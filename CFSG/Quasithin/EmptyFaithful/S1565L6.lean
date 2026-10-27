module

public import CFSG.Quasithin.Background.E2Two
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LieType.Simplicity.Suzuki

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section Lift

variable {G : Type} [Group G]

private noncomputable def starMap (M' H K : Subgroup G) (hKH : K ≤ H) :
    ↥K →* ↥(E2.star M' H K) :=
  (((QuotientGroup.mk' ((kerIn M' H).subgroupOf H)).comp (Subgroup.inclusion hKH)).codRestrict
    (E2.star M' H K) fun k => ⟨Subgroup.inclusion hKH k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩)

private theorem starMap_surjective (M' H K : Subgroup G) (hKH : K ≤ H) :
    Function.Surjective (starMap M' H K hKH) := by
  rintro ⟨y, x, hx, rfl⟩
  refine ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, ?_⟩
  apply Subtype.ext
  rfl

private theorem starMap_eq_one_iff (M' H K : Subgroup G) (hKH : K ≤ H) (k : ↥K) :
    starMap M' H K hKH k = 1 ↔ Subgroup.inclusion hKH k ∈ (kerIn M' H).subgroupOf H := by
  constructor
  · intro h
    have := congrArg Subtype.val h
    exact (QuotientGroup.eq_one_iff _).mp this
  · intro h
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).mpr h

theorem exists_sylow_borel_lift {M' H K : Subgroup G} (hKH : K ≤ H) {L : Type} [Group L]
    [Nontrivial L] (ρ : ↥K →* L) (hρ : Function.Surjective ρ)
    (hker : ∀ k : ↥K, Subgroup.inclusion hKH k ∈ (kerIn M' H).subgroupOf H → ρ k = 1)
    (hsimple : IsSimpleGroup ↥(E2.star M' H K))
    (hB : E2.IsBorelIn (E2.star M' H K) (E2.star M' H (M' ⊓ K))) :
    ∃ S : Sylow 2 L, ∀ b ∈ Subgroup.normalizer ((S : Subgroup L) : Set L),
      ∃ k : ↥K, (k : G) ∈ M' ∧ ρ k = b := by
  have hq := starMap_surjective M' H K hKH
  have hkq : (starMap M' H K hKH).ker ≤ ρ.ker := by
    intro k hk
    rw [MonoidHom.mem_ker, starMap_eq_one_iff] at hk
    exact hker k hk
  let ρ' : ↥(E2.star M' H K) →* L :=
    (starMap M' H K hKH).liftOfRightInverse (Function.surjInv hq)
      (Function.rightInverse_surjInv hq) ⟨ρ, hkq⟩
  have hρ'q : ∀ k, ρ' (starMap M' H K hKH k) = ρ k := fun k =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨ρ, hkq⟩ k
  have hρ's : Function.Surjective ρ' := by
    intro l
    obtain ⟨k, rfl⟩ := hρ l
    exact ⟨starMap M' H K hKH k, hρ'q k⟩
  have hρ'i : Function.Injective ρ' := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases hsimple.eq_bot_or_eq_top_of_normal ρ'.ker with h | h
    · exact h
    · exfalso
      obtain ⟨l₁, hl₁⟩ := exists_ne (1 : L)
      obtain ⟨y, rfl⟩ := hρ's l₁
      have : y ∈ ρ'.ker := by rw [h]; trivial
      exact hl₁ (by simpa using this)
  let e : ↥(E2.star M' H K) ≃* L := MulEquiv.ofBijective ρ' ⟨hρ'i, hρ's⟩
  obtain ⟨S₀, hS₀, hMKs⟩ := hB
  obtain ⟨hS₀K, hS₀2, hS₀i⟩ := hS₀
  have hS' : IsPGroup 2 (S₀.subgroupOf (E2.star M' H K)) :=
    hS₀2.of_equiv (Subgroup.subgroupOfEquivOfLe hS₀K).symm
  let S₁ : Sylow 2 ↥(E2.star M' H K) := hS'.toSylow hS₀i
  let S : Sylow 2 L :=
    S₁.comapOfInjective e.symm.toMonoidHom e.symm.injective
      (by rw [MonoidHom.range_eq_top.mpr e.symm.surjective]; exact le_top)
  have hSmem : ∀ h : L, h ∈ (S : Subgroup L) ↔ e.symm h ∈ (S₁ : Subgroup ↥(E2.star M' H K)) :=
    fun h => Iff.rfl
  have hS₁mem : ∀ h : ↥(E2.star M' H K), h ∈ (S₁ : Subgroup ↥(E2.star M' H K)) ↔ (h : E2.StarQuot M' H) ∈ S₀ :=
    fun h => Iff.rfl
  refine ⟨S, fun b hb => ?_⟩
  set y : ↥(E2.star M' H K) := e.symm b with hy
  have hyN : y ∈ Subgroup.normalizer ((S₁ : Subgroup ↥(E2.star M' H K)) : Set ↥(E2.star M' H K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have h1 := Subgroup.mem_normalizer_iff.mp hb (e h)
    rw [hSmem, hSmem, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply] at h1
    exact h1
  have hyY : (y : E2.StarQuot M' H) ∈ Subgroup.normalizer (S₀ : Set (E2.StarQuot M' H)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hhS
      have hhK : h ∈ E2.star M' H K := hS₀K hhS
      have := (Subgroup.mem_normalizer_iff.mp hyN ⟨h, hhK⟩).mp ((hS₁mem _).mpr hhS)
      exact (hS₁mem _).mp this
    · intro hS2'
      have hhK : h ∈ E2.star M' H K := by
        have h1 : (y : E2.StarQuot M' H)⁻¹ * ((y : E2.StarQuot M' H) * h * (y : E2.StarQuot M' H)⁻¹) *
            (y : E2.StarQuot M' H) = h := by group
        rw [← h1]
        exact (E2.star M' H K).mul_mem ((E2.star M' H K).mul_mem ((E2.star M' H K).inv_mem y.2)
          (hS₀K hS2')) y.2
      have := (Subgroup.mem_normalizer_iff.mp hyN ⟨h, hhK⟩).mpr ((hS₁mem _).mpr hS2')
      exact (hS₁mem _).mp this
  have hmem : (y : E2.StarQuot M' H) ∈ E2.star M' H (M' ⊓ K) := by
    rw [hMKs]
    exact ⟨y.2, hyY⟩
  obtain ⟨x, hx, hxy⟩ := hmem
  have hxM : (x : G) ∈ M' ⊓ K := Subgroup.mem_subgroupOf.mp hx
  refine ⟨⟨(x : G), hxM.2⟩, hxM.1, ?_⟩
  have hk : starMap M' H K hKH ⟨(x : G), hxM.2⟩ = y := by
    apply Subtype.ext
    exact hxy
  rw [← hρ'q, hk]
  exact e.apply_symm_apply b

end Lift


theorem isSimpleGroup_of_psl2_or_sz {X : Type} [Group X] {n : ℕ} (h : IsPSL 2 2 n X ∨ IsSz n X) :
    IsSimpleGroup X := by
  rcases h with h | h
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 2 n h).2
  · exact (CFSG.LieType.Simplicity.fam_2b2_simplicity X 2 n h).2

end CFSG.Quasithin
