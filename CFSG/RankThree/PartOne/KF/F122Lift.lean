module

public import CFSG.RankThree.PartOne.S11c.Sec66Glue
public import CFSG.RankThree.PartTwo.Census.Criteria

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.PartOne.Sec66T

variable {G : Type} [Group G] [Finite G]

theorem three_le_localRank_of_fixed_plane {p : ℕ} (hp : p.Prime) {L : Subgroup G}
    (hZ : ¬ p ∣ Nat.card (Subgroup.center L)) {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) (hxp : x ^ p = 1) (hxL : x ∉ L)
    (R : Subgroup (↥L ⧸ Subgroup.center ↥L)) (hRe : IsElementaryAbelian p ↥R)
    (hRc : Nat.card R = p ^ 2) (hRfix : ∀ r ∈ R, centerQuotientConj L ⟨x, hx⟩ r = r)
    (U : Subgroup (↥L ⧸ Subgroup.center ↥L)) (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 ↥U)
    (hUinv : ∀ u ∈ U, centerQuotientConj L ⟨x, hx⟩ u ∈ U)
    (hRU : R ≤ Subgroup.normalizer (U : Set (↥L ⧸ Subgroup.center ↥L))) :
    3 ≤ localRank p ↥(L ⊔ Subgroup.zpowers x) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set α := centerQuotientConj L ⟨x, hx⟩ with hα
  set G₁ : Subgroup G := L ⊓ Subgroup.centralizer ({x} : Set G) with hG₁
  obtain ⟨θ, hθsurj, -, hθval⟩ := exists_fixed_hom hp hZ hx hxp
  let π : L →* L ⧸ Subgroup.center L := QuotientGroup.mk' (Subgroup.center L)
  have hkerdvd : Nat.card θ.ker ∣ Nat.card (Subgroup.center L) := by
    let ιJ : ↥G₁ →* ↥L := Subgroup.inclusion inf_le_left
    have hker : θ.ker.map ιJ ≤ Subgroup.center L := by
      rintro _ ⟨y, hy, rfl⟩
      have h1 := hθval y
      rw [MonoidHom.mem_ker.mp hy] at h1
      exact (QuotientGroup.eq_one_iff (ιJ y)).mp h1.symm
    have h2 : Nat.card (θ.ker.map ιJ) = Nat.card θ.ker :=
      Subgroup.card_map_of_injective (Subgroup.inclusion_injective _)
    rw [← h2]
    exact Subgroup.card_dvd_of_le hker
  have hcop : Nat.Coprime (Nat.card θ.ker) (p ^ 2) :=
    (Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr
      (fun h => hZ (h.trans hkerdvd)))).symm
  have hRle : R ≤ fixSub α := fun r hr => hRfix r hr
  let R₀ : Subgroup ↥(fixSub α) := R.subgroupOf (fixSub α)
  have hR₀card : Nat.card R₀ = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRle).toEquiv, hRc]
  obtain ⟨R', hR'map, hR'card, hR'inj⟩ :=
    exists_lift_of_surjective_coprime θ hθsurj hcop R₀ hR₀card
  have hπR : ∀ y ∈ R', π ⟨(y : G), y.2.1⟩ ∈ R := by
    intro y hy
    have h1 : θ y ∈ R₀ := by rw [← hR'map]; exact ⟨y, hy, rfl⟩
    have h2 : ((θ y : ↥(fixSub α)) : L ⧸ Subgroup.center L) ∈ R := h1
    rw [hθval y] at h2
    exact h2
  let A₂ : Subgroup G := R'.map G₁.subtype
  have hA₂L : ∀ y ∈ A₂, y ∈ L := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2.1
  have hA₂x : ∀ y ∈ A₂, y * x = x * y := by
    rintro _ ⟨y, -, rfl⟩
    exact (Subgroup.mem_centralizer_singleton_iff.mp y.2.2)
  have hA₂p : ∀ y ∈ A₂, y ^ p = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : (θ (y ^ p) : ↥(fixSub α)) = θ 1 := by
      apply Subtype.ext
      rw [map_pow, map_one]
      have hr := hπR y hy
      have := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := R)
        (π ⟨(y : G), y.2.1⟩) hr
      have h3 : ((θ y : ↥(fixSub α)) : L ⧸ Subgroup.center L) = π ⟨(y : G), y.2.1⟩ := hθval y
      show ((θ y : ↥(fixSub α)) : L ⧸ Subgroup.center L) ^ p = 1
      rw [h3]
      exact this
    have h2 := hR'inj _ (R'.pow_mem hy p) 1 R'.one_mem h1
    show ((y ^ p : ↥G₁) : G) = 1
    rw [h2]
    rfl
  have hA₂c' : ∀ y ∈ A₂, ∀ z ∈ A₂, y * z = z * y := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    have h1 : θ (y * z) = θ (z * y) := by
      apply Subtype.ext
      rw [map_mul, map_mul]
      have hyr := hπR y hy
      have hzr := hπR z hz
      have h4 := hRe.is_comm.comm (⟨π ⟨(y : G), y.2.1⟩, hyr⟩ : R) ⟨π ⟨(z : G), z.2.1⟩, hzr⟩
      have h5 := congrArg Subtype.val h4
      simp only [Subgroup.coe_mul] at h5
      simp only [Subgroup.coe_mul]
      rw [hθval y, hθval z]
      exact h5
    have h2 := hR'inj _ (R'.mul_mem hy hz) _ (R'.mul_mem hz hy) h1
    exact congrArg (fun w : ↥G₁ => (w : G)) h2
  have hA₂card : Nat.card A₂ = p ^ 2 := by
    rw [Subgroup.card_map_of_injective G₁.subtype_injective, hR'card]
  obtain ⟨S, hS2, hS1, hSφ⟩ := exists_aut_invariant_two_subgroup (Subgroup.center L)
    (fun z hz => hz) U hU2 hU1
  let S' : Subgroup G := S.map L.subtype
  have hSL : S' ≤ L := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hS'1 : S' ≠ ⊥ := by
    intro h
    apply hS1
    have := (Subgroup.map_eq_bot_iff _).mp h
    rw [Subgroup.ker_subtype] at this
    exact eq_bot_iff.mpr this
  have hS'2 : IsPGroup 2 S' := hS2.map L.subtype
  have hconj : ∀ y ∈ R', ∀ s ∈ S, (⟨(y : G), y.2.1⟩ : L) * s * (⟨(y : G), y.2.1⟩ : L)⁻¹ ∈ S := by
    intro y hy s hs
    refine hSφ (MulAut.conj (⟨(y : G), y.2.1⟩ : L)) (fun w => ?_) s hs
    have h1 := (Subgroup.mem_normalizer_iff.mp (hRU (hπR y hy))) (π w)
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
    exact h1
  have hA₂S : A₂ ≤ Subgroup.normalizer (S' : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨_, hconj y hy s hs, rfl⟩
    · rintro ⟨s, hs, hsh⟩
      refine ⟨_, hconj (y⁻¹) (R'.inv_mem hy) s hs, ?_⟩
      have hs' : (s : G) = (y : G) * h * (y : G)⁻¹ := hsh
      show ((y⁻¹ : ↥G₁) : G) * (s : G) * ((y⁻¹ : ↥G₁) : G)⁻¹ = h
      rw [Subgroup.coe_inv, hs']
      group
  have hUα : ∀ w : L, π w ∈ U ↔ α (π w) ∈ U := by
    intro w
    refine ⟨hUinv _, fun h => ?_⟩
    have hle : Subgroup.map α.toMonoidHom U ≤ U := by
      rintro _ ⟨u, hu, rfl⟩
      exact hUinv u hu
    have hfin : Finite U := inferInstance
    have heq : Subgroup.map α.toMonoidHom U = U :=
      Subgroup.eq_of_le_of_card_ge hle
        (Subgroup.card_map_of_injective (f := α.toMonoidHom) α.injective).ge
    rw [← heq] at h
    obtain ⟨u, hu, hux⟩ := h
    have : u = π w := α.injective hux
    rw [← this]
    exact hu
  let φa : MulAut L := L.normalizerMonoidHom ⟨x, hx⟩
  have hφa : ∀ w : L, π (φa w) = α (π w) := fun w => rfl
  have hφacoe : ∀ w : L, ((φa w : L) : G) = x * (w : G) * x⁻¹ := fun w =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨x, hx⟩ w
  have hSa : ∀ s ∈ S, φa s ∈ S := fun s hs =>
    hSφ φa (fun w => by rw [hφa]; exact hUα w) s hs
  have hSa' : ∀ s ∈ S, φa⁻¹ s ∈ S := fun s hs =>
    hSφ φa⁻¹ (fun w => by
      have h1 := hUα (φa⁻¹ w)
      rw [← hφa, MulAut.apply_inv_self] at h1
      exact h1.symm) s hs
  have hxS' : x ∈ Subgroup.normalizer (S' : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨φa s, hSa s hs, (hφacoe s).symm⟩
    · rintro ⟨s, hs, hsh⟩
      refine ⟨φa⁻¹ s, hSa' s hs, ?_⟩
      have h1 := hφacoe (φa⁻¹ s)
      rw [MulAut.apply_inv_self] at h1
      have hsh' : (s : G) = x * h * x⁻¹ := hsh
      show ((φa⁻¹ s : L) : G) = h
      have h2 : ((φa⁻¹ s : L) : G) = x⁻¹ * (s : G) * x := by
        rw [h1]
        group
      rw [h2, hsh']
      group
  have hxA₂ : x ∉ A₂ := fun h => hxL (hA₂L x h)
  obtain ⟨A₃, -, hA₃le, hA₃card, hA₃c, hA₃p⟩ :=
    exists_elementary_ext hp hA₂c' hA₂p hA₂card hxA₂ hxp (fun y hy => hA₂x y hy)
  have hA₃S : A₃ ≤ Subgroup.normalizer (S' : Set G) :=
    hA₃le.trans (sup_le hA₂S ((Subgroup.zpowers_le).mpr hxS'))
  set M : Subgroup G := L ⊔ Subgroup.zpowers x with hM
  have hLM : L ≤ M := le_sup_left
  have hxM : x ∈ M := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hA₃M : A₃ ≤ M :=
    hA₃le.trans (sup_le (fun y hy => hLM (hA₂L y hy)) ((Subgroup.zpowers_le).mpr hxM))
  have hS'M : S' ≤ M := hSL.trans hLM
  have hS''1 : S'.subgroupOf M ≠ ⊥ := by
    intro h
    apply hS'1
    rw [← Subgroup.map_subgroupOf_eq_of_le hS'M, h, Subgroup.map_bot]
  have hS''2 : IsPGroup 2 (S'.subgroupOf M) := hS'2.comap_subtype
  have hE : CFSG.Assembly.IsElemAbelian p (A₃.subgroupOf M) := by
    refine ⟨⟨⟨fun y z => ?_⟩⟩, fun y hy => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      exact hA₃c _ y.2 _ z.2
    · apply Subtype.ext
      rw [Subgroup.coe_pow, OneMemClass.coe_one]
      exact hA₃p _ hy
  have hc : Nat.card (A₃.subgroupOf M) = p ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₃M).toEquiv, hA₃card]
  have hEP : A₃.subgroupOf M ≤ Subgroup.normalizer ((S'.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hyA : (y : G) ∈ A₃ := hy
    have h5 := Subgroup.mem_normalizer_iff.mp (hA₃S hyA) (z : G)
    change (z : G) ∈ S' ↔ (y : G) * z * (y : G)⁻¹ ∈ S' at h5
    exact h5
  exact CFSG.RankThree.PartTwo.Census.le_localRank_of_le_normalizer hp hS''1 hS''2 hE hc hEP

end CFSG.RankThree.PartOne
