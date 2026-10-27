module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223Y1Main

public section

namespace CFSG.Quasithin.S15221

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.S15223

variable {G : Type} [Group G] [Finite G]

section Setting

variable {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I : Subgroup G}

theorem autOn_Y1_facts (hs : Setting152 T Mc M) (hD : Inputs152 T Mc M H B₀ I)
    (hodd : Odd (Nat.card (oTwoUpper (autOn M (V154 T Mc M))))) {Y₁ : Subgroup G}
    (hY₁M : Y₁ ≤ M) (hY₁eq : Y₁ = oTwoUpper Y₁) (h3 : (pCoreOf 2 Y₁).relIndex Y₁ = 3)
    (hnot : ¬ Y₁ ≤ Mc ⊓ I) :
    autOn Y₁ (V154 T Mc M) ≤ oTwoUpper (autOn M (V154 T Mc M)) ∧
      Nat.card (autOn Y₁ (V154 T Mc M)) = 3 ∧
      Y₁ ⊓ Subgroup.centralizer (V154 T Mc M : Set G) = pCoreOf 2 Y₁ := by
  have hMV : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hY₁V : Y₁ ≤ Subgroup.normalizer (V154 T Mc M : Set G) := hY₁M.trans hMV
  have hE : autOn Y₁ (V154 T Mc M) ≤ oTwoUpper (autOn M (V154 T Mc M)) := by
    have h1 : autOn Y₁ (V154 T Mc M) = autOn (oTwoUpper Y₁) (V154 T Mc M) :=
      congrArg (fun X => autOn X (V154 T Mc M)) hY₁eq
    rw [h1, ← A4.oTwoUpper_autOn hY₁V]
    exact oTwoUpper_mono (A4.autOn_mono hY₁M)
  have hO2C : pCoreOf 2 Y₁ ≤ Subgroup.centralizer (V154 T Mc M : Set G) := by
    intro x hx
    have hxN : x ∈ Subgroup.normalizer (V154 T Mc M : Set G) := hY₁V (pCoreOf_le 2 Y₁ hx)
    have hxa : conjAct (V154 T Mc M) ⟨x, hxN⟩ ∈ autOn (pCoreOf 2 Y₁) (V154 T Mc M) :=
      mem_autOn_of_mem hxN hx
    have h2 : IsPGroup 2 (autOn (pCoreOf 2 Y₁) (V154 T Mc M)) :=
      isPGroup_autOn (pCoreOf_isPGroup 2 Y₁) ((pCoreOf_le 2 Y₁).trans hY₁V)
    have h3' : conjAct (V154 T Mc M) ⟨x, hxN⟩ ∈ oTwoUpper (autOn M (V154 T Mc M)) :=
      hE (A4.autOn_mono (pCoreOf_le 2 Y₁) hxa)
    exact A4.conjAct_eq_one_iff.mp (eq_one_of_mem_of_odd_of_isPGroup hodd h2 h3' hxa)
  have hcard := card_autOn_eq_relIndex (A := Y₁) hY₁V
  have hle1 : pCoreOf 2 Y₁ ≤ Y₁ ⊓ Subgroup.centralizer (V154 T Mc M : Set G) :=
    le_inf (pCoreOf_le 2 Y₁) hO2C
  have hmul := Subgroup.relIndex_mul_relIndex (pCoreOf 2 Y₁)
    (Y₁ ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) Y₁ hle1 inf_le_left
  rw [h3] at hmul
  have hne1 : (Y₁ ⊓ Subgroup.centralizer (V154 T Mc M : Set G)).relIndex Y₁ ≠ 1 := by
    intro h1
    have h2 := Subgroup.relIndex_eq_one.mp h1
    exact hnot fun y hy => cv_le_inf152 hs hD ⟨hY₁M hy, (h2 hy).2⟩
  have hd : (Y₁ ⊓ Subgroup.centralizer (V154 T Mc M : Set G)).relIndex Y₁ ∣ 3 :=
    Dvd.intro_left _ hmul
  have h33 : (Y₁ ⊓ Subgroup.centralizer (V154 T Mc M : Set G)).relIndex Y₁ = 3 :=
    ((Nat.dvd_prime Nat.prime_three).mp hd).resolve_left hne1
  rw [h33] at hmul
  have hone : (pCoreOf 2 Y₁).relIndex (Y₁ ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) = 1 := by
    omega
  exact ⟨hE, by rw [hcard, h33],
    le_antisymm (Subgroup.relIndex_eq_one.mp hone) hle1⟩

theorem autOn_not_le_conjSub_gen {Z₁ : Subgroup G} {t : G} (hs : Setting152 T Mc M)
    (hD : Inputs152 T Mc M H B₀ I) {Y₁ : Subgroup G} (hY₁N : Y₁ ≤ M ⊓ I)
    (hNI : M ⊓ I = M ⊓ Subgroup.centralizer (Z₁ : Set G))
    (hZle : quasithinOmegaOneCenter T ≤ Z₁ ⊔ conjSub t Z₁)
    (hZtle : conjSub t Z₁ ≤ zSOf T Mc M B₀)
    (hD0 : autOn Y₁ (V154 T Mc M) ≠ ⊥)
    (hDE : autOn Y₁ (V154 T Mc M) ≤ oTwoUpper (autOn M (V154 T Mc M)))
    (hE9 : Nat.card (oTwoUpper (autOn M (V154 T Mc M))) = 9) :
    ¬ autOn Y₁ (V154 T Mc M) ≤ autOn (conjSub t Y₁) (V154 T Mc M) := by
  intro hle
  apply hD0
  have hMV : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hTV : T ≤ Subgroup.normalizer (V154 T Mc M : Set G) := (T_le_M152 hs).trans hMV
  rw [eq_bot_iff]
  intro a ha
  obtain ⟨y, hyV, hyY, rfl⟩ := mem_autOn_iff_exists.mp ha
  have hyI : y ∈ M ⊓ I := hY₁N hyY
  have hyC1 : y ∈ Subgroup.centralizer (Z₁ : Set G) := by
    rw [hNI] at hyI
    exact hyI.2
  obtain ⟨y', hy'V, hy'Y, hyy'⟩ := mem_autOn_iff_exists.mp (hle ha)
  have hy'C1 : t⁻¹ * y' * t ∈ Subgroup.centralizer (Z₁ : Set G) := by
    have h := hY₁N (mem_conjSub.mp hy'Y)
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
    exact ⟨(hY₁N.trans inf_le_left) hyY, hyZ⟩
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

theorem autOn_ne_of_normal (hs : Setting152 T Mc M) (hB₀ : IsB0 T Mc M B₀)
    (hD : Inputs152 T Mc M H B₀ I) (hii : Concl15218ii T Mc M H B₀ I) {Y₁ : Subgroup G}
    (hY₁N : Y₁ ≤ M ⊓ I) (hDE : autOn Y₁ (V154 T Mc M) ≤ oTwoUpper (autOn M (V154 T Mc M)))
    (hD0 : autOn Y₁ (V154 T Mc M) ≠ ⊥) {Y : Subgroup G} (hYM : Y ≤ M)
    (hYn : M ≤ Subgroup.normalizer (Y : Set G)) :
    autOn Y (V154 T Mc M) ≠ autOn Y₁ (V154 T Mc M) := by
  intro heq
  have hOmS : Om4FactsStatement := fun _ _ _ _ hX => S152O4.om4_facts hX
  have hMV : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hTM : T ≤ M := T_le_M152 hs
  obtain ⟨B, hB⟩ := hD.hN.sigmaPrime_nonempty
  have hE9 : Nat.card (oTwoUpper (autOn M (V154 T Mc M))) = 9 :=
    (om4_card152 hOmS hii.2.2.1).2
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
  have hnle := autOn_not_le_conjSub_gen hs hD hY₁N hNI hZle hZtle hD0 hDE hE9
  apply hnle
  have h1 : autOn (conjSub t Y₁) (V154 T Mc M) = autOn Y (V154 T Mc M) := by
    rw [autOn_conjSub_eq hMV (hTM htT) (hY₁N.trans inf_le_left), ← heq,
      ← autOn_conjSub_eq hMV (hTM htT) hYM, conjSub_eq_self152 (hYn (hTM htT))]
  rw [h1, heq]

end Setting

end CFSG.Quasithin.S15221
