module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Vol2.Ch4Sec3C135Kern

public section

namespace CFSG.Quasithin.H13.Ch4.C135

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.Ch4 Matrix
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem msPair_facts {G₀ R₀ : Subgroup G} (hMS : IsMSPair G₀ R₀) :
    R₀ ≤ G₀ ∧ pCoreOf 2 G₀ ≤ R₀ ∧ IsPGroup 2 R₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hMS.2.1 with ⟨H', hH'lt, hodd, rfl⟩ | ⟨hRG, hOR, -, -, -, -, -, hE⟩
  · refine ⟨(pCoreOf_le 2 H').trans hH'lt.le, ?_, pCoreOf_isPGroup 2 H'⟩
    obtain ⟨P, hP⟩ := exists_isSylowTwoOf H'
    have hPG : IsSylowTwoOf P G₀ := by
      refine ⟨hP.1.trans hH'lt.le, hP.2.1, fun h2 => ?_⟩
      have h1 := Subgroup.relIndex_mul_relIndex P H' G₀ hP.1 hH'lt.le
      have h3 : 2 ∣ P.relIndex H' * H'.relIndex G₀ := h1 ▸ h2
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h3 with h | h
      · exact hP.2.2 h
      · exact hodd h
    exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_two_le_of_isSylowTwoOf hPG).trans hP.1)
      (hH'lt.le.trans (le_normalizer_pCoreOf 2 G₀)) (pCoreOf_isPGroup 2 G₀)
  · refine ⟨hRG, hOR, fun r => ?_⟩
    obtain ⟨e⟩ := hE
    set π := QuotientGroup.mk' (CFSG.pCore 2 ↥G₀) with hπ
    set Rb := (R₀.subgroupOf G₀).map π with hRb
    have hr : (⟨r, hRG r.2⟩ : ↥G₀) ∈ R₀.subgroupOf G₀ := r.2
    have hsq : π ⟨r, hRG r.2⟩ ^ 2 = 1 := by
      have h1 : (⟨π ⟨r, hRG r.2⟩, ⟨_, hr, rfl⟩⟩ : ↥Rb) ^ 2 = 1 := by
        apply e.injective
        rw [map_pow, map_one]
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow, toAdd_one, two_nsmul]
        funext i
        show (_ : ZMod 2) + _ = 0
        generalize (Multiplicative.toAdd (e ⟨π ⟨r, hRG r.2⟩, ⟨_, hr, rfl⟩⟩)) i = z
        fin_cases z <;> rfl
      exact congrArg Subtype.val h1
    rw [← map_pow, ← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hsq
    obtain ⟨m, hm⟩ := CFSG.pCore_isPGroup ⟨_, hsq⟩
    refine ⟨m + 1, Subtype.ext ?_⟩
    have h2 := congrArg (fun x : ↥(CFSG.pCore 2 ↥G₀) => ((x : ↥G₀) : G)) hm
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h2
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [pow_succ', pow_mul]
    exact h2

namespace Hyp135

variable {F : Type} [Field F] {G₀ L : Subgroup G} {α : ↥L →* ↥(StatedSL 3 F)}
  (H : Hyp135 G₀ L α)
include H

theorem centralizer_U_le {R₀ : Subgroup G} (hMS : IsMSPair G₀ R₀)
    (hG₀ : (G₀ : Set G) = (L : Set G) * (R₀ : Set G)) :
    G₀ ⊓ Subgroup.centralizer (centerOf (c134Q G₀ L) : Set G) ≤ pCoreOf 2 G₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hRG, -, hR2⟩ := msPair_facts hMS
  set Y := G₀ ⊓ Subgroup.centralizer (centerOf (c134Q G₀ L) : Set G) with hY
  have hGY : G₀ ≤ Subgroup.normalizer (Y : Set G) := fun g hg =>
    mem_normalizer_inf (Subgroup.le_normalizer hg)
      (mem_normalizer_centralizer_of_mem (H.le_normalizer_U hg))
  have hLN : (L.subgroupOf G₀).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer H.le]
    exact H.norm
  set φ := QuotientGroup.mk' (L.subgroupOf G₀) with hφ
  have hsurj : Function.Surjective (φ.comp (Subgroup.inclusion hRG)) := by
    intro z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (L.subgroupOf G₀) z
    have hg : (g : G) ∈ (L : Set G) * (R₀ : Set G) := by rw [← hG₀]; exact g.2
    obtain ⟨l, hl, r, hr, hlr⟩ := Set.mem_mul.mp hg
    refine ⟨⟨r, hr⟩, ?_⟩
    rw [MonoidHom.comp_apply]
    apply QuotientGroup.eq.mpr
    rw [Subgroup.mem_subgroupOf]
    show ((Subgroup.inclusion hRG ⟨r, hr⟩)⁻¹ * g : ↥G₀).1 ∈ L
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
    rw [← hlr]
    have h1 := (Subgroup.mem_normalizer_iff.mp (H.norm (hRG (R₀.inv_mem hr))) l).mp hl
    simpa [mul_assoc] using h1
  have hQ2 : IsPGroup 2 (↥G₀ ⧸ L.subgroupOf G₀) := hR2.of_surjective _ hsurj
  have hY2 : IsPGroup 2 Y := by
    rintro ⟨y, hyG, hyC⟩
    obtain ⟨k, hk⟩ := hQ2 (φ ⟨y, hyG⟩)
    rw [← map_pow, ← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] at hk
    have hyk : y ^ 2 ^ k ∈ L := hk
    have hyC' : y ^ 2 ^ k ∈ Subgroup.centralizer (centerOf (c134Q G₀ L) : Set G) :=
      Subgroup.pow_mem _ hyC _
    have h1 : α ⟨_, hyk⟩ = 1 := map_eq_one_of_mem_centralizer H.nat one_ne_zero hyC'
    have h2 : (⟨_, hyk⟩ : ↥L) ∈ α.ker := h1
    rw [H.surj.2] at h2
    obtain ⟨m, hm⟩ := CFSG.pCore_isPGroup ⟨_, h2⟩
    refine ⟨k + m, Subtype.ext ?_⟩
    have h3 := congrArg (fun x : ↥(CFSG.pCore 2 ↥L) => ((x : ↥L) : G)) hm
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h3 ⊢
    rw [pow_add, pow_mul]
    exact h3
  exact le_pCoreOf_of_le_normalizer 2 inf_le_left hGY hY2

omit [Finite G] in
theorem isElemAbelian_U [CharP F 2] : IsElemAbelian 2 (centerOf (c134Q G₀ L)) := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · exact Subgroup.mem_centralizer_iff.mp y.2.2 x x.2.1
  · have h1 : crd H.nat (⟨x, hx⟩ ^ 2) = 0 := by
      rw [sq, crd_mul]
      funext i j
      exact CharTwo.add_self_eq_zero _
    have h2 := crd_injective H.nat (h1.trans (crd_one H.nat).symm)
    simpa using congrArg Subtype.val h2

omit [Finite G] in
theorem U_ne_bot : centerOf (c134Q G₀ L) ≠ ⊥ := by
  intro h
  obtain ⟨u, hu⟩ := crd_surjective H.nat (fun _ => Pi.single 0 1)
  have hu1 : (u : G) = 1 := Subgroup.mem_bot.mp (h.le u.2)
  have h1 : u = 1 := Subtype.ext hu1
  rw [h1, crd_one] at hu
  have := congrFun (congrFun hu 0) 0
  simp at this

theorem exists_maxElemAbelian_not_le [CharP F 2] {R₀ : Subgroup G} (hMS : IsMSPair G₀ R₀) :
    ∃ A, IsMaxElemAbelian R₀ A ∧ ¬ A ≤ pCoreOf 2 G₀ := by
  obtain ⟨-, hTR, -⟩ := msPair_facts hMS
  by_contra hcon
  push Not at hcon
  have hJT : thompsonJ R₀ ≤ pCoreOf 2 G₀ := iSup₂_le fun A hA => hcon A hA
  have hJeq : thompsonJ R₀ = thompsonJ (pCoreOf 2 G₀) := thompsonJ_eq_of_le hJT hTR
  have hUR : centerOf (c134Q G₀ L) ≤ R₀ :=
    (centerOf_le'.trans H.c134Q_le_pCoreOf).trans hTR
  obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian R₀
  have hA₀ne : A₀ ≠ ⊥ := by
    intro h
    have h1 := hA₀.2.2 _ hUR H.isElemAbelian_U
    rw [h, Subgroup.card_bot] at h1
    exact H.U_ne_bot (Subgroup.eq_bot_of_card_le _ h1)
  have hJne : thompsonJ R₀ ≠ ⊥ := fun h =>
    hA₀ne (le_bot_iff.mp (h ▸ (le_iSup₂ (f := fun A (_ : IsMaxElemAbelian R₀ A) => A) A₀ hA₀)))
  refine hMS.2.2 (thompsonJ R₀) (thompsonJ_le_self R₀) hJne
    (CFSG.QuasithinUnique.Setup.characteristic_thompsonJ R₀) ?_
  rw [hJeq]
  intro g hg
  have hgT : g ∈ Subgroup.normalizer (pCoreOf 2 G₀ : Set G) := le_normalizer_pCoreOf 2 G₀ hg
  have h1 := cjSub_thompsonJ hgT
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h1]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h1, mem_cjSub] at hx
    simpa [mul_assoc] using hx

end Hyp135

end CFSG.Quasithin.H13.Ch4.C135

end
