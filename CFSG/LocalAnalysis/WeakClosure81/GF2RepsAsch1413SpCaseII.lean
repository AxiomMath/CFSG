module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413SpData
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413Normalizes
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413Adapt

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch1413

open CFSG.Quasithin CFSG.Open CFSG.ComponentClassification.CatFactsSp4 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial SymplecticHigher SymplecticFlag Subgroup

private theorem a1413SpCaseII_spIota_injective {Q : Type} [Group Q] {L : Subgroup Q}
    {K : Type} [Field K] (e : ↥L ≃* StatedProj (StatedSp 2 K)) :
    Function.Injective (spIota e) := by
  intro x y h
  exact e.symm.injective (Subtype.ext h)

private theorem a1413SpCaseII_eq_one_or_u1_of_central_E1 {K : Type} [Field K]
    (h2 : (2 : K) ≠ 0) {x : StatedProj (StatedSp 2 K)} (hx : x ∈ E1 K)
    (hc : ∀ y ∈ E1 K, x * y = y * x) : x = 1 ∨ x = u1 K := by
  obtain ⟨g, rfl⟩ := mem_E1.mp hx
  have hg : g ∈ center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [Subgroup.mem_center_iff]
    intro h
    apply injective_E1 h2
    have h1 := hc (proj 2 K (blkSL K (h, 1))) (mem_E1.mpr ⟨h, rfl⟩)
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk,
      mul_one] at h1
    simp only [MonoidHom.comp_apply, MonoidHom.inl_apply]
    exact h1.symm
  rcases eq_one_or_neg_of_mem_center hg with h | h
  · left
    have hg1 : g = 1 := Subtype.ext h
    rw [hg1, show ((1 : Matrix.SpecialLinearGroup (Fin 2) K),
      (1 : Matrix.SpecialLinearGroup (Fin 2) K)) = 1 from rfl, map_one, map_one]
  · right
    rw [show g = negOneSL from Subtype.ext h, u1_eq_proj_blkSL']

private theorem a1413SpCaseII_u1_mul_self {K : Type} [Field K] : u1 K * u1 K = 1 := by
  have hT1 : T1 K * T1 K = 1 := by
    apply sp_ext
    rw [Subgroup.coe_mul, Units.val_mul, coe_T1, blk_mul]
    simp [blk_one_one]
  rw [u1, ← map_mul, hT1, map_one]

private theorem a1413SpCaseII_center_map_E1 {Q : Type} [Group Q] {L : Subgroup Q}
    {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0)
    (e : ↥L ≃* StatedProj (StatedSp 2 K)) :
    ∀ x ∈ (E1 K).map (spIota e),
      (∀ y ∈ (E1 K).map (spIota e), x * y = y * x) ↔
        x ∈ zpowers (spIota e (u1 K)) := by
  intro x hx
  constructor
  · intro hc
    obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp hx
    have hc₀ : ∀ y ∈ E1 K, x₀ * y = y * x₀ := by
      intro y hy
      have h := hc (spIota e y) (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
      rw [← map_mul, ← map_mul] at h
      exact a1413SpCaseII_spIota_injective e h
    rcases a1413SpCaseII_eq_one_or_u1_of_central_E1 h2 hx₀ hc₀ with h1 | h1
    · rw [h1, map_one]
      exact Subgroup.one_mem _
    · rw [h1]
      exact Subgroup.mem_zpowers _
  · intro hxzp y hy
    obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.mp hy
    have hzcent : spIota e (u1 K) ∈
        Subgroup.centralizer (((E1 K).map (spIota e) : Subgroup Q) : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.mp hw
      show spIota e w₀ * spIota e (u1 K) = spIota e (u1 K) * spIota e w₀
      rw [← map_mul, ← map_mul]
      congr 1
      exact commute_E1_E2 hw₀ u1_mem_E2
    have hxcent : x ∈ Subgroup.centralizer
        (((E1 K).map (spIota e) : Subgroup Q) : Set Q) :=
      (Subgroup.zpowers_le.mpr hzcent) hxzp
    exact ((Subgroup.mem_centralizer_iff.mp hxcent) (spIota e y₀)
      (Subgroup.mem_map.mpr ⟨y₀, hy₀, rfl⟩)).symm

theorem asch1413_sp4_caseII_le (h64o : Asch6_4Odd) (h64s : Asch6_4Seven)
    {Q : Type} [Group Q] [Finite Q] {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {ρ : Q →* MulAut V} (hρ : Function.Injective ρ)
    {L A : Subgroup Q} (hLn : L.Normal) (hc : centralizer (L : Set Q) ≤ L)
    (hZ : Subgroup.center ↥L = ⊥) {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p) (h7 : 7 ≤ p) (e : ↥L ≃* StatedProj (StatedSp 2 K))
    (hA : Nat.card A = 4) (hAe : IsElemAbelian 2 A) (hq : IsQuadraticOn ρ A)
    (hAz : ∀ a ∈ A, a * spIota e (u1 K) = spIota e (u1 K) * a) (hzA : spIota e (u1 K) ∉ A) :
    p = 7 ∧ A ≤ (X0 K).map (spIota e) := by
  classical
  let ι : StatedProj (StatedSp 2 K) →* Q := spIota e
  let z : Q := ι (u1 K)
  let X₁ : Subgroup Q := (E1 K).map ι
  let X₂ : Subgroup Q := (E2 K).map ι
  let X : Subgroup Q := (X0 K).map ι
  let G₀ : Subgroup Q := X ⊔ A
  have hι : Function.Injective ι := a1413SpCaseII_spIota_injective e
  have hpne2 : p ≠ 2 := by omega
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact hp.odd_of_ne_two hpne2
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  have h4 : 4 ≤ Nat.card K := by rw [hK]; omega
  have h5 : 5 ≤ Nat.card K := by rw [hK]; omega
  have hp5 : 5 < p := by omega
  obtain ⟨hN, hAC₁, hCQ⟩ := asch1413_sp4_data hLn hc hodd h5 hZ e hA hAe hAz hzA
  have hz_mem : z ∈ X₁ := Subgroup.mem_map.mpr ⟨u1 K, u1_mem_E1, rfl⟩
  have hz_order : orderOf z = 2 := by
    show orderOf (ι (u1 K)) = 2
    rw [orderOf_injective ι hι (u1 K)]
    exact orderOf_eq_prime (by rw [pow_two]; exact a1413SpCaseII_u1_mul_self) (u1_ne_one h2)
  have hZX : ∀ x ∈ X₁, (∀ y ∈ X₁, x * y = y * x) ↔ x ∈ zpowers z := by
    intro x hx
    exact a1413SpCaseII_center_map_E1 h2 e x hx
  have hperf : ⁅X₁, X₁⁆ = X₁ := by
    have hperfE : Group.IsPerfect ↥(E1 K) := (isQuasisimple_E1 h2 h4).1
    show ⁅(E1 K).map ι, (E1 K).map ι⁆ = (E1 K).map ι
    rw [← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hperfE]
  have hmod : F6.IsL2 p 1 (↥X₁ ⧸ Subgroup.center ↥X₁) := by
    have hg : ↥X₁ ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
      (Subgroup.equivMapOfInjective (E1 K) ι hι).symm.trans (E1Equiv h2).symm
    refine ⟨⟨hp, le_rfl, le_rfl, ?_, ?_⟩, K, inferInstance, inferInstance, ?_, ?_⟩
    · intro h
      have hp2 : p = 2 := by
        have h' := (Prod.ext_iff.mp h).2
        rwa [pow_one] at h'
      omega
    · intro h
      have hp3 : p = 3 := by
        have h' := (Prod.ext_iff.mp h).2
        rwa [pow_one] at h'
      omega
    · rw [pow_one]
      exact hK
    · exact ⟨(QuotientGroup.congr (Subgroup.center ↥X₁)
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) hg
        (Subgroup.map_center_eq hg)).trans (projectiveSpecialLinearGroupEquivStatedProj 2 K)⟩
  have hquasi : CFSG.Open.IsQuasisimple ↥X₁ :=
    CFSG.Open.IsQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective (E1 K) ι hι).symm
      (A3.isQuasisimple_iff_open.mp (isQuasisimple_E1 h2 h4))
  have hnorm₁ : (X₁.subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono (E1_le_X0 h2))]
    intro h k hh hk
    obtain ⟨h₀, hh₀, rfl⟩ := Subgroup.mem_map.mp hh
    obtain ⟨k₀, hk₀, rfl⟩ := Subgroup.mem_map.mp hk
    refine Subgroup.mem_map.mpr ⟨k₀ * h₀ * k₀⁻¹, conj_mem_E1 h2 hk₀ hh₀, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hnorm₂ : (X.subgroupOf G₀).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    refine sup_le Subgroup.le_normalizer ?_
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hN a ha x hx
    · intro hx
      have h1 : a⁻¹ * (a * x * a⁻¹) * (a⁻¹)⁻¹ ∈ X := hN a⁻¹ (A.inv_mem ha) _ hx
      convert h1 using 1
      group
  have hXcomp : IsComponentOf X₁ G₀ :=
    ⟨(Subgroup.map_mono (E1_le_X0 h2)).trans le_sup_left,
      IsSubnormal.step (Subgroup.map_mono (E1_le_X0 h2)) hnorm₁
        (IsSubnormal.step le_sup_left hnorm₂ (IsSubnormal.refl G₀)),
      hquasi⟩
  have hAN₁ : A ≤ Subgroup.normalizer (X₁ : Set Q) :=
    asch1413_normalizes hV hρ hXcomp hz_order hz_mem hZX le_sup_right hA hAe hq hAC₁ hp
      hp5 hmod
  have hAN : ∀ a ∈ A, ∀ x ∈ X₁, a * x * a⁻¹ ∈ X₁ := by
    intro a ha x hx
    exact (Subgroup.mem_normalizer_iff.mp (hAN₁ ha) x).mp hx
  have hzA' : ∀ a ∈ A, a * z = z * a := fun a ha => hAz a ha
  have hAC' : ∀ a ∈ A, (∀ x ∈ X₁, a * x = x * a) → a = 1 := by
    intro a ha hcent
    have hmem : a ∈ A ⊓ Subgroup.centralizer (X₁ : Set Q) := by
      refine Subgroup.mem_inf.mpr ⟨ha, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (hcent x hx).symm
    have hbot : a ∈ (⊥ : Subgroup Q) := by
      rw [← hAC₁]
      exact hmem
    exact Subgroup.mem_bot.mp hbot
  obtain ⟨hp7, hdecomp⟩ :=
    asch1413_adapt64 h64o h64s hV hρ hz_order hz_mem hperf hZX hzA' hAN hA hAe hq hAC' hp
      hp5 hmod
  refine ⟨hp7, ?_⟩
  intro a ha
  obtain ⟨x, hx, c, hc, hax⟩ := hdecomp a ha
  rw [hax]
  exact Subgroup.mul_mem _
    (Subgroup.map_mono (E1_le_X0 h2) hx)
    (Subgroup.map_mono (E2_le_X0 h2) (hCQ hc))

end CFSG.LocalAnalysis.WeakClosure81.Asch1413

end
