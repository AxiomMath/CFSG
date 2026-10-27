module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie2ProofOuter
import CFSG.Quasithin.Background.FFC2G2
import CFSG.Quasithin.Background.SmithB42G2Id
import CFSG.LieType.Chevalley.NoncentralNormalSolvable
import CFSG.RankThree.PartTwo.KFacts.K71G2
import CFSG.RankThree.PartTwo.Sec11.SetUp1118ProofCarrier
import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.Quasithin.Background.B4ModelsWitness

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open scoped commutatorElement

namespace KS11Lie3Proof

theorem hasType424_of_commutator_le {Γ : Type} [Group Γ] [Finite Γ] (N : Subgroup Γ)
    (hcomm : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ N) (h : KS11Lie2Proof.HasType424 Γ) :
    KS11Lie2Proof.HasType424 N := by
  obtain ⟨L, ⟨hLp, hLsn, hLq⟩, hT⟩ := h
  have hLN : L ≤ N := by
    have h1 : ⁅L, L⁆ = L := Subgroup.commutator_eq_self
    rw [← h1, Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def]
    exact hcomm a b
  set e : L.subgroupOf N ≃* L := Subgroup.subgroupOfEquivOfLe hLN with he
  set eq := QuotientGroup.congr _ _ e (aschbacherSolvableCore_map_mulEquiv Nat.prime_three e)
  refine ⟨L.subgroupOf N, ⟨?_, hLsn.subgroupOf, ?_⟩, isType424_of_mulEquiv eq hT⟩
  · have := hLp
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv eq.symm hLq

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem sl2Three_eq_commutator {k : Type} [Field k] [CharP k 2] :
    KS11Lie2Proof.sl2Three k = vSL 1 * uSL 1 * (vSL 1)⁻¹ * (uSL 1)⁻¹ := by
  have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
  apply Subtype.ext
  simp only [KS11Lie2Proof.sl2Three, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, coe_vSL, coe_uSL, Matrix.adjugate_fin_two,
    Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  linear_combination (-2) * h2

section G2Two


open CFSG.LieType.HighestRoot in
theorem g2_exists_e9_commutator (k : Type) [Field k] [CharP k 2] :
    ∃ u v : adjointGroup .G2 k, u ∈ _root_.commutator (adjointGroup .G2 k) ∧
      v ∈ _root_.commutator (adjointGroup .G2 k) ∧ u ≠ 1 ∧ u ^ 3 = 1 ∧ v ^ 3 = 1 ∧
      u * v = v * u ∧ v ∉ Subgroup.zpowers u := by
  set n := canonicalRep (coxeterSystem .G2) k (simple .G2 g2s * simple .G2 g2l) with hn
  set ρ₁ := simpleRootSL2 .G2 k g2l with hρ₁
  set ρ₂ := simpleRootSL2 .G2 k g2s with hρ₂
  set M := KS11Lie2Proof.sl2Three k with hM
  have hu₀Q : ρ₁ M ∈ rootSubgroup .G2 k g2e0 ⊔ rootSubgroup .G2 k (-g2e0) := by
    rw [← closure_xUnit_yUnit_eq_rootSubgroup_sup, ← range_simpleRootSL2]
    exact ⟨M, rfl⟩
  have hQ₂ : ∀ A, MulAut.conj n (ρ₂ A) ∈ rootSubgroup .G2 k g2δ ⊔ rootSubgroup .G2 k (-g2δ) := by
    intro A
    rw [← map_conj_canonicalRep_closure_xUnit_yUnit g2_w_smul, ← range_simpleRootSL2]
    exact ⟨ρ₂ A, ⟨A, rfl⟩, rfl⟩
  have hnA : n ∈ adjointGroup .G2 k := canonicalRep_mem_adjointGroup _ k _
  have hu₀A : ρ₁ M ∈ adjointGroup .G2 k := simpleRootSL2_mem_adjointGroup _ M
  have hv₀A : MulAut.conj n (ρ₂ M) ∈ adjointGroup .G2 k :=
    mul_mem (mul_mem hnA (simpleRootSL2_mem_adjointGroup _ M)) (inv_mem hnA)
  have hcomm : ∀ (i : Fin (Tag.rank .G2)),
      (⟨simpleRootSL2 .G2 k i M, simpleRootSL2_mem_adjointGroup _ M⟩ : adjointGroup .G2 k) ∈
        _root_.commutator (adjointGroup .G2 k) := by
    intro i
    have hc : (⟨simpleRootSL2 .G2 k i M, simpleRootSL2_mem_adjointGroup _ M⟩ :
        adjointGroup .G2 k) =
        ⁅(⟨simpleRootSL2 .G2 k i (vSL 1), simpleRootSL2_mem_adjointGroup _ _⟩ :
          adjointGroup .G2 k),
          ⟨simpleRootSL2 .G2 k i (uSL 1), simpleRootSL2_mem_adjointGroup _ _⟩⁆ := by
      apply Subtype.ext
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hM, sl2Three_eq_commutator, map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [hc, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  refine ⟨⟨ρ₁ M, hu₀A⟩, ⟨MulAut.conj n (ρ₂ M), hv₀A⟩, hcomm g2l, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : (⟨MulAut.conj n (ρ₂ M), hv₀A⟩ : adjointGroup .G2 k) =
        ⟨n, hnA⟩ * ⟨ρ₂ M, simpleRootSL2_mem_adjointGroup _ M⟩ * (⟨n, hnA⟩)⁻¹ := rfl
    rw [e]
    exact (inferInstance : (_root_.commutator (adjointGroup .G2 k)).Normal).conj_mem _
      (hcomm g2s) _
  · intro h
    have h1 : ρ₁ M = 1 := congrArg Subtype.val h
    obtain ⟨l, -, hl⟩ := KS11Lie2Proof.simpleRootSL2_eq_one g2l h1
    exact KS11Lie2Proof.sl2Three_ne_smul (l : k) hl
  · apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, hM, KS11Lie2Proof.sl2Three_pow_three, map_one]
  · apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, ← map_pow, hM, KS11Lie2Proof.sl2Three_pow_three, map_one, map_one]
  · exact Subtype.ext (KS11Lie2Proof.g2_commute' hu₀Q (hQ₂ M)).eq
  · intro hmem
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hv₀ : MulAut.conj n (ρ₂ M) = ρ₁ M ^ i := by
      have h1 := congrArg Subtype.val hi
      simp only [Subgroup.coe_zpow] at h1
      exact h1.symm
    have hvQ₁ : MulAut.conj n (ρ₂ M) ∈ rootSubgroup .G2 k g2e0 ⊔ rootSubgroup .G2 k (-g2e0) := by
      rw [hv₀]
      exact zpow_mem hu₀Q i
    have hc := (KS11Lie2Proof.g2_commute' hvQ₁ (hQ₂ (uSL 1))).eq
    have hc' : ρ₂ M * ρ₂ (uSL 1) = ρ₂ (uSL 1) * ρ₂ M :=
      (MulAut.conj n).injective (by rw [map_mul, map_mul]; exact hc)
    have h1 : ρ₂ (M * uSL 1 * (uSL 1 * M)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, hc', mul_inv_cancel]
    obtain ⟨l, hl2, hl⟩ := KS11Lie2Proof.simpleRootSL2_eq_one g2s h1
    apply KS11Lie2Proof.sl2Three_mul_uSL_ne hl2
    have h2 : M * uSL 1 = (M * uSL 1 * (uSL 1 * M)⁻¹) * (uSL 1 * M) := by group
    rw [hM] at h2 hl
    rw [h2, Matrix.SpecialLinearGroup.coe_mul, hl, Matrix.smul_mul, Matrix.one_mul]

theorem nonempty_adjointGroup_g2_mulEquiv_quasithinG2 {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2) :
    Nonempty (adjointGroup .G2 k ≃* CFSG.Open.quasithinG2 k) := by
  have : CharP k 2 := CFSG.Quasithin.B42G2Id.charP_two_of_card (f := 1) (by rw [hk, pow_one])
  have hQC := CFSG.Quasithin.G11.P3G2.quasithinG2_eq_cayleyGroup (K := k)
  obtain ⟨ψ, -, hsurj⟩ := CFSG.Quasithin.B42G2Id.exists_surjective_adjointGroup_hom_cayleyGroup
    (F := k)
  obtain ⟨hs, ⟨a, b, hab⟩, -⟩ := CFSG.Quasithin.FFC.commutator_data_g2 hk
    (MulEquiv.refl ↥(CFSG.Open.quasithinG2 k))
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    by_contra hne
    have hnc : ¬ ψ.ker ≤ Subgroup.center (adjointGroup .G2 k) := by
      rw [center_adjointGroup_eq_bot_field, le_bot_iff]
      exact hne
    have hsol := (noncentral_normal_solvable_quotient .G2 k ψ.ker hnc).2.1
    have hC : Group.IsSolvable ↥(CFSG.Quasithin.Explicit.cayleyGroup k) :=
      Group.isSolvable_of_surjective
        (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj).surjective
    have hC' : Group.IsSolvable ↥(CFSG.Open.quasithinG2 k) := by
      rw [hQC]
      exact hC
    have hle : ⁅CFSG.Open.quasithinG2 k, CFSG.Open.quasithinG2 k⁆ ≤
        CFSG.Open.quasithinG2 k := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
        (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
    have hD : Group.IsSolvable ↥⁅CFSG.Open.quasithinG2 k, CFSG.Open.quasithinG2 k⁆ :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hD) a b)
  exact ⟨(MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩).trans (MulEquiv.subgroupCongr hQC.symm)⟩

theorem isSimpleGroup_commutator_g2_two {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2) : IsSimpleGroup (_root_.commutator (adjointGroup .G2 k)) := by
  obtain ⟨E⟩ := nonempty_adjointGroup_g2_mulEquiv_quasithinG2 hk
  obtain ⟨hs, -, -⟩ := CFSG.Quasithin.FFC.commutator_data_g2 hk (Subgroup.topEquiv.trans E)
  rw [commutator_def]
  exact hs

theorem not_hasType424_g2_two {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2) :
    ¬ KS11Lie2Proof.HasType424 (adjointGroup .G2 k) := by
  have : CharP k 2 := CFSG.Quasithin.B42G2Id.charP_two_of_card (f := 1) (by rw [hk, pow_one])
  have : Finite (ModGL Tag.G2 k) := finite_modGL
  have : IsSimpleGroup (_root_.commutator (adjointGroup .G2 k)) :=
    isSimpleGroup_commutator_g2_two hk
  obtain ⟨u, v, huC, hvC, hu1, hu3, hv3, huv, hvu⟩ := g2_exists_e9_commutator k
  have hc : ⁅u, v⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr huv
  refine KS11Lie2Proof.not_hasType424_of_simple (_root_.commutator (adjointGroup .G2 k)) ?_ huC
    hvC hu1 hu3 hv3 (by rw [hc]; exact Commute.one_left _) (by rw [hc]; exact Commute.one_left _)
    hvu
  intro a b
  rw [← commutatorElement_def, commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)

theorem not_hasType424_fixSub_two {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hk : Nat.card (fixSubfield σ) = 2) :
    ¬ KS11Lie2Proof.HasType424 (Item426.fixSub (KFacts.g2FieldHom K σ)) := by
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  intro h
  have h1 := hasType424_of_commutator_le (KS11Lie2Proof.fixN σ)
    (KS11Lie2Proof.commutator_mem_fixN σ) h
  exact not_hasType424_g2_two hk (h1.of_mulEquiv (KS11Lie2Proof.fixNEquiv σ))

theorem not_hasType424_outer_g2_eight {K : Type} [Field K] [Finite K] (hK8 : Nat.card K = 8)
    {α : MulAut (adjointGroup Tag.G2 K)} (hα3 : α ^ 3 = 1) (hout : ¬ KFacts.IsInnerAut α) :
    ¬ KS11Lie2Proof.HasType424 (Item426.fixSub α) := by
  have : CharP K 2 := CFSG.Quasithin.B42G2Id.charP_two_of_card (f := 3) (by rw [hK8]; norm_num)
  have hK3 : ringChar K ≠ 3 := by
    rw [ringChar.eq K 2]
    norm_num
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK8]
    norm_num
  obtain ⟨σ, hσ3, k, rfl⟩ := KFacts.g2_order_three_field_descent hK3 hK4 hα3 hout
  have hcard : Nat.card (fixSubfield σ) ^ 3 = 2 ^ 3 := by
    have h := KFacts.card_fixSubfield_pow σ
    rw [hσ3, hK8] at h
    rw [h]
    norm_num
  have hk2 : Nat.card (fixSubfield σ) = 2 := Nat.pow_left_injective (by norm_num) hcard
  intro h
  rw [KS11Lie2Proof.conj_mul_mul_inv_eq_congr] at h
  exact not_hasType424_fixSub_two σ hk2
    (h.of_mulEquiv (KS11Lie2Proof.fixSubCongr (MulAut.conj k) _).symm)

end G2Two

end KS11Lie3Proof

section Assembly

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem noOuterType424G2Eight_holds : NoOuterType424G2Eight := by
  intro Z _ _ hZ α J hα3 hin hJ hJT
  obtain ⟨X, _, ⟨q, hq, hq8, ⟨f⟩⟩, ⟨e⟩⟩ := hZ
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set K := GaloisField q.p q.exponent
  have hK : Nat.card K = q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact GaloisField.card _ _ q.exponent_pos.ne'
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).g2 q hq K hK
  have hXp : Group.IsPerfect X := by
    have := SetUp1118Proof.isPerfect_lie_G2 q hq
    exact Group.IsPerfect.ofSurjective (f := f.symm.toMonoidHom) f.symm.surjective
  let E : Z ≃* adjointGroup Tag.G2 K :=
    ((e.trans ((MulEquiv.subgroupCongr hXp.commutator_eq_top).trans Subgroup.topEquiv)).trans
      (f.trans b.symm)).trans
      ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
        QuotientGroup.quotientBot)
  have hT := (KS11Lie2Proof.hasType424_of_mem hJ hJT).of_mulEquiv
    (KS11Lie2Proof.fixSubCongr E α)
  have hα3' : MulAut.congr E α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hout : ¬ KFacts.IsInnerAut (MulAut.congr E α) := by
    rintro ⟨c, hc⟩
    apply hin
    refine ⟨E.symm c, ?_⟩
    have h1 := congrArg (MulAut.congr E.symm) hc
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj] at h1
    rw [h1]
    ext z
    simp
  exact KS11Lie3Proof.not_hasType424_outer_g2_eight (hK.trans hq8) hα3' hout hT

theorem noOuterType424G2_holds : NoOuterType424G2 :=
  noOuterType424G2_of_eight noOuterType424G2Eight_holds

end Assembly

end CFSG.RankThree.PartTwo.Sec11
