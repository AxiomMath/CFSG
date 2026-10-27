module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223Y1Canon
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223Y1Klein
public import CFSG.Quasithin.EmptyFaithful.S152UStruct
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223Stmt22

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace S15223

theorem autOn_inf_centralizer_eq_bot {G : Type} [Group G] {M V : Subgroup G} :
    autOn (M ⊓ Subgroup.centralizer (V : Set G)) V = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  obtain ⟨x, hx, hxX, rfl⟩ := mem_autOn_iff_exists.mp ha
  exact Subgroup.mem_bot.mpr (A4.conjAct_eq_one_iff.mpr hxX.2)

theorem autOn_not_le_conjSub {G : Type} [Group G] [Finite G] {T Mc M H : Subgroup G}
    {B₀ : Subgroup (MulAut (V154 T Mc M))} {I Z₁ : Subgroup G} {t : G} (hs : Setting152 T Mc M)
    (hD : Inputs152 T Mc M H B₀ I) (hNI : M ⊓ I = M ⊓ Subgroup.centralizer (Z₁ : Set G))
    (hZle : quasithinOmegaOneCenter T ≤ Z₁ ⊔ conjSub t Z₁)
    (hZtle : conjSub t Z₁ ≤ zSOf T Mc M B₀)
    (hD0 : autOn (oPrimeResidualOf 3 (M ⊓ I)) (V154 T Mc M) ≠ ⊥)
    (hE9 : Nat.card (oTwoUpper (autOn M (V154 T Mc M))) = 9) :
    ¬ autOn (oPrimeResidualOf 3 (M ⊓ I)) (V154 T Mc M) ≤
      autOn (conjSub t (oPrimeResidualOf 3 (M ⊓ I))) (V154 T Mc M) := by
  intro hle
  apply hD0
  have hMV : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hTV : T ≤ Subgroup.normalizer (V154 T Mc M : Set G) := (T_le_M152 hs).trans hMV
  have hDE : autOn (oPrimeResidualOf 3 (M ⊓ I)) (V154 T Mc M) ≤ oTwoUpper (autOn M (V154 T Mc M)) :=
    autOn_oPrimeResidual_le hMV inf_le_left
  rw [eq_bot_iff]
  intro a ha
  obtain ⟨y, hyV, hyY, rfl⟩ := mem_autOn_iff_exists.mp ha
  have hyI : y ∈ M ⊓ I := oPrimeResidual_le hyY
  have hyC1 : y ∈ Subgroup.centralizer (Z₁ : Set G) := by
    rw [hNI] at hyI
    exact hyI.2
  obtain ⟨y', hy'V, hy'Y, hyy'⟩ := mem_autOn_iff_exists.mp (hle ha)
  have hy'C1 : t⁻¹ * y' * t ∈ Subgroup.centralizer (Z₁ : Set G) := by
    have h := oPrimeResidual_le (mem_conjSub.mp hy'Y)
    rw [hNI] at h
    exact h.2
  have hyZt : ∀ z' ∈ conjSub t Z₁, z' * y = y * z' := by
    intro z' hz'
    have hz'V : z' ∈ V154 T Mc M := zS_le_V152 hs B₀ (hZtle hz')
    have h1 : y' * z' = z' * y' := by
      have hc := Subgroup.mem_centralizer_iff.mp hy'C1 _ (mem_conjSub.mp hz')
      calc y' * z' = t * ((t⁻¹ * y' * t) * (t⁻¹ * z' * t)) * t⁻¹ := by group
        _ = t * ((t⁻¹ * z' * t) * (t⁻¹ * y' * t)) * t⁻¹ := by rw [hc]
        _ = z' * y' := by group
    have e1 : ((conjAct (V154 T Mc M) ⟨y, hyV⟩ ⟨z', hz'V⟩ : V154 T Mc M) : G) = y * z' * y⁻¹ :=
      conj_coe_apply (V154 T Mc M) ⟨y, hyV⟩ ⟨z', hz'V⟩
    have e2 : ((conjAct (V154 T Mc M) ⟨y', hy'V⟩ ⟨z', hz'V⟩ : V154 T Mc M) : G) =
        y' * z' * y'⁻¹ := conj_coe_apply (V154 T Mc M) ⟨y', hy'V⟩ ⟨z', hz'V⟩
    rw [hyy'] at e2
    have h3 : y' * z' * y'⁻¹ = z' := by rw [h1]; group
    have h4 : y * z' * y⁻¹ = z' := by rw [← e1, e2, h3]
    calc z' * y = (y * z' * y⁻¹) * y := by rw [h4]
      _ = y * z' := by group
  have hcen : Z₁ ⊔ conjSub t Z₁ ≤ Subgroup.centralizer ({y} : Set G) := by
    refine sup_le (fun z hz => ?_) (fun z hz => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hyC1 z hz)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hyZt z hz)
  have hyZ : y ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcen (hZle hz))
  have hyU : y ∈ (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) ⊔ T := by
    rw [← hD.h14.inf_eq.2]
    exact ⟨(oPrimeResidual_le.trans inf_le_left) hyY, hyZ⟩
  have haT : conjAct (V154 T Mc M) ⟨y, hyV⟩ ∈ autOn T (V154 T Mc M) := by
    have h := mem_autOn_of_mem hyV hyU
    rw [autOn_sup (inf_le_left.trans hMV) hTV, autOn_inf_centralizer_eq_bot, bot_sup_eq] at h
    exact h
  have hE3 : IsPGroup 3 (oTwoUpper (autOn M (V154 T Mc M))) :=
    IsPGroup.of_card (p := 3) (n := 2) (by rw [hE9]; norm_num)
  have hT2 : IsPGroup 2 (autOn T (V154 T Mc M)) := isPGroup_autOn hs.qtfe.sylow.1 hTV
  have hdisj : Disjoint (autOn T (V154 T Mc M)) (oTwoUpper (autOn M (V154 T Mc M))) :=
    IsPGroup.disjoint_of_ne 2 3 (by norm_num) _ _ hT2 hE3
  exact Subgroup.mem_bot.mpr (Subgroup.disjoint_def.mp hdisj haT (hDE ha))

theorem input15222ThreeCanon_of (h5 : StageLemma15205) (h159 : StageLemma1519)
    (h11 : StageLemma15211) (h13 : StageLemma15213) (h14 : StageLemma15214)
    (hN : StageNotation15209) (h16 : StageLemma15216) (h17 : StageLemma15217) :
    Input15222ThreeCanon := by
  intro G _ _ T Mc M hs H hH H₁ H₂ hP B₀ hB₀ I hI hii hCh h3p hnirr Y₁ hcanon hY₁eq hY₁N hSY hq
  have hD : Inputs152 T Mc M H B₀ I :=
    ⟨h5 G T Mc M hs, h159 G T Mc M hs.qtfe hs.mf hs.ce, h13 G T Mc M hs H hH,
      h14 G T Mc M hs B₀ hB₀, h11 G T Mc M hs H hH, hN G T Mc M hs H hH,
      h16 G T Mc M hs H hH B₀ hB₀ I hI, h17 G T Mc M hs B₀ hB₀ I hI⟩
  obtain ⟨B, hB⟩ := (hN G T Mc M hs H hH).sigmaPrime_nonempty
  have hMV : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hTM : T ≤ M := T_le_M152 hs
  have hC : M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤ M ⊓ I :=
    le_inf inf_le_left ((cv_le_inf152 hs hD).trans inf_le_right)
  have hOmS : Om4FactsStatement := fun _ _ _ _ hX => S152O4.om4_facts hX
  have hE9 : Nat.card (oTwoUpper (autOn M (V154 T Mc M))) = 9 :=
    (om4_card152 hOmS hii.2.2.1).2
  have hEc := (oTwoUpper_Mb_odd_comm hD hOmS).2
  have hnTS : ¬ T ≤ sOf152 T Mc M B₀ := fun h => by
    have h1 := Subgroup.relIndex_eq_one.mpr h
    rw [hD.h17.2.2] at h1
    omega
  obtain ⟨t, htT, htS⟩ := IsConcreteLE.not_le_iff_exists.mp hnTS
  obtain ⟨Z₁, hZ₁sup, hZ₁inf, hNI, -⟩ := hii.2.2.2
  obtain ⟨hZs4, hZse⟩ := card_zS152 hB₀ hD
  have hZc : ∀ a ∈ zSOf T Mc M B₀, ∀ b ∈ zSOf T Mc M B₀, a * b = b * a := by
    intro a ha b hb
    have := hZse.1
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : zSOf T Mc M B₀) ⟨b, hb⟩)
  have htZs : t ∈ Subgroup.normalizer (zSOf T Mc M B₀ : Set G) := by
    rw [← commutator_eq_zSOf hD.h13 hB₀ hB]
    exact (hD.h11 B hB).normal htT
  have htZ : t ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp (quasithinOmegaOneCenter_le_center T hz).2 t htT).symm
  have htn : t ∉ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) := fun hc => htS ⟨htT, hc⟩
  obtain ⟨hZle, hZtle⟩ := le_sup_conjSub_of_klein hZs4 hZc hD.h17.2.1 hZ₁sup hZ₁inf htZs htZ htn
  have hS2 : IsPGroup 2 (sOf152 T Mc M B₀) := hs.qtfe.sylow.1.to_le S_le_T152
  have hY₁ne : oPrimeResidualOf 3 (M ⊓ I) ≠ ⊥ := by
    rw [← hcanon]
    exact ne_bot_of_quot_perm hS2 hq
  have hD0 := autOn_oPrimeResidual_ne_bot hMV inf_le_left h3p hY₁ne
  have hnle := autOn_not_le_conjSub hs hD hNI hZle hZtle hD0 hE9
  have hres := abstract_step hMV inf_le_left hC hEc hE9 (hTM htT) hD0 hnle
  refine ⟨t, htT, htS, ?_, ?_⟩
  · rw [hcanon]
    exact hres.1
  · rw [hcanon, hres.2, hii.2.1.1.2.1]

end S15223

end CFSG.Quasithin
