module

public import CFSG.RankThree.GF2n.Smith81.Sec2Stmt
public import CFSG.RankThree.GF2n.Smith81.TiRecognition
public import CFSG.RankThree.GF2n.Stroth80.ClassicalQuasisimple
public import CFSG.Holt.Bender
public import CFSG.Timmesfeld.Bridge.StrongEmbedding
public import CFSG.GroupTheory.QuasiDihedralFusion.Basic
public import CFSG.Models.PGLSimple

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

private theorem isSolvable_of_le_isSolvable {X : Type} [Group X] {S R : Subgroup X}
    (hS : Group.IsSolvable ↥S) (hR : R ≤ S) : Group.IsSolvable ↥R := by
  haveI := hS
  exact solvable_of_solvable_injective (f := Subgroup.inclusion hR)
    (Subgroup.inclusion_injective hR)

private theorem not_quotSat_of_isSolvable {G : Type} [Group G] {S N : Subgroup G}
    {P : ∀ (X : Type) [Group X], Prop}
    (hS : Group.IsSolvable ↥S) (hP : ∀ (X : Type) [Group X], P X → ¬ Group.IsSolvable X) :
    ¬ QuotSat S N P := by
  rintro ⟨hN, hPX⟩
  haveI := hS
  haveI : Group.IsSolvable (↥S ⧸ N.subgroupOf S) :=
    solvable_of_surjective (QuotientGroup.mk'_surjective (N.subgroupOf S))
  exact hP _ hPX this

private theorem not_isSolvable_of_isOmegaPlus (hCL : ClassicalNonsolvableStatement) {m q : ℕ}
    (hm : 2 ≤ m) (hq4 : 4 ≤ q) (hq2 : ∃ j : ℕ, q = 2 ^ j) :
    ∀ (X : Type) [Group X], IsOmegaPlus m q X → ¬ Group.IsSolvable X := by
  rintro X _ ⟨K, hF, hFin, hKq, ⟨e⟩⟩ hX
  obtain ⟨j, hj⟩ := hq2
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hKq.trans hj)
  haveI : Group.IsSolvable X := hX
  have h4K : 4 ≤ Nat.card K := by rw [hKq]; exact hq4
  exact (hCL K h4K).2.2.1 m hm (solvable_of_surjective (f := e.toMonoidHom) e.surjective)

private theorem not_isSolvable_of_isOmegaMinus (hCL : ClassicalNonsolvableStatement) {m q : ℕ}
    (hm : 2 ≤ m) (hq4 : 4 ≤ q) (hq2 : ∃ j : ℕ, q = 2 ^ j) :
    ∀ (X : Type) [Group X], IsOmegaMinus m q X → ¬ Group.IsSolvable X := by
  rintro X _ ⟨K, hF, hFin, hKq, b, c, hirr, ⟨e⟩⟩ hX
  obtain ⟨j, hj⟩ := hq2
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hKq.trans hj)
  haveI : Group.IsSolvable X := hX
  have h4K : 4 ≤ Nat.card K := by rw [hKq]; exact hq4
  exact (hCL K h4K).2.2.2 m b c hm hirr (solvable_of_surjective (f := e.toMonoidHom) e.surjective)

private theorem not_isSolvable_of_isPSUModel {j q : ℕ} (hq : q = 2 ^ j) :
    ∀ (X : Type) [Group X], IsPSUModel 6 q X → ¬ Group.IsSolvable X := by
  subst hq
  rintro X _ ⟨K, hF, hFin, hKq, ⟨e⟩⟩ hX
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsSolvable X := hX
  have hnq : ((6 : ℕ), (2 : ℕ) ^ j) ≠ (3, 2) := by
    intro h
    exact absurd (congrArg Prod.fst h) (by norm_num)
  haveI := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 j hKq 6
    (by norm_num) hnq
  haveI : Nontrivial (StatedProj (StatedSU 6 (2 ^ j) K)) := IsSimpleGroup.toNontrivial
  haveI := CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (K := K) (p := 2) (f := j) hKq
    (n := 6) (by norm_num) hnq
  haveI : Group.IsPerfect (StatedProj (StatedSU 6 (2 ^ j) K)) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  exact Group.IsPerfect.not_isSolvable (StatedProj (StatedSU 6 (2 ^ j) K))
    (solvable_of_surjective (f := e.toMonoidHom) e.surjective)

private theorem not_isSolvable_of_isPSLModel {q : ℕ} (hq4 : 4 ≤ q) :
    ∀ (X : Type) [Group X], IsPSLModel 6 q X → ¬ Group.IsSolvable X := by
  rintro X _ ⟨K, hF, hFin, hKq, ⟨e⟩⟩ hX
  haveI : Group.IsSolvable X := hX
  have h4K : 4 ≤ Nat.card K := by rw [hKq]; exact hq4
  haveI : IsSimpleGroup (StatedProj (StatedSL 6 K)) :=
    CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL K (by norm_num)
      (Or.inl (by norm_num)) (Or.inl (by norm_num))
  haveI : Nontrivial (StatedProj (StatedSL 6 K)) := IsSimpleGroup.toNontrivial
  haveI : Group.IsPerfect (StatedSL 6 K) :=
    (statedSL_quasisimple_of_card 6 K (by norm_num) h4K).1
  haveI : Group.IsPerfect (StatedProj (StatedSL 6 K)) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  exact Group.IsPerfect.not_isSolvable (StatedProj (StatedSL 6 K))
    (solvable_of_surjective (f := e.toMonoidHom) e.surjective)

private theorem eq_one_of_mem_statedSL {K : Type} [Field K] {n : ℕ} (hn : n ≤ 1)
    {g : Matrix.GeneralLinearGroup (Fin n) K} (hg : g ∈ StatedSL n K) : g = 1 := by
  rw [CFSG.Open.StatedAPI.mem_statedSL_iff] at hg
  interval_cases n
  · exact Subsingleton.elim _ _
  · refine Units.ext (Matrix.ext fun a b => ?_)
    rw [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]
    simpa [Matrix.det_fin_one, Matrix.one_apply] using hg

private theorem not_isSolvable_lgen {G : Type} [Group G] [Finite G]
    (hCL : ClassicalNonsolvableStatement) {M Q Z B : Subgroup G}
    (hc : RemCfg M Q Z B) : ¬ Group.IsSolvable ↥(Lgen M (LB M Q B)) := by
  intro hS
  have hyp := hc.ctx.hyp
  obtain ⟨j, -, hj, -⟩ := hyp.cp
  have hq4 : 4 ≤ Nat.card Z := hyp.q4
  have hq2 : ∃ i : ℕ, Nat.card Z = 2 ^ i := ⟨j, hj⟩
  have hRt : ∀ t : G, Rt M (LB M Q B) t ≤ Lgen M (LB M Q B) := by
    intro t
    unfold Rt Lgen
    refine iSup_le fun m => iSup_le fun hm => iSup_le fun _ => ?_
    exact le_iSup₂_of_le m hm le_rfl
  obtain hO | hE | ⟨n, hT⟩ := hc.remaining
  ·
    obtain ⟨t, -, hcase⟩ := hO
    have hRs : Group.IsSolvable ↥(Rt M (LB M Q B) t) := isSolvable_of_le_isSolvable hS (hRt t)
    rcases hcase with hE1 | ⟨m, hm2, -, -, hq⟩
    · obtain ⟨-, -, hq⟩ := hE1
      rcases hq with hq | hq
      · exact not_quotSat_of_isSolvable (P := IsOmegaPlus 2 (Nat.card Z)) hRs
          (not_isSolvable_of_isOmegaPlus hCL (le_refl 2) hq4 hq2) hq
      · exact not_quotSat_of_isSolvable (P := IsOmegaMinus 2 (Nat.card Z)) hRs
          (not_isSolvable_of_isOmegaMinus hCL (le_refl 2) hq4 hq2) hq
    · rcases hq with ⟨hq, -⟩ | ⟨hq, -⟩
      · exact not_quotSat_of_isSolvable (P := IsOmegaPlus m (Nat.card Z)) hRs
          (not_isSolvable_of_isOmegaPlus hCL hm2 hq4 hq2) hq
      · exact not_quotSat_of_isSolvable (P := IsOmegaMinus m (Nat.card Z)) hRs
          (not_isSolvable_of_isOmegaMinus hCL hm2 hq4 hq2) hq
  ·
    obtain ⟨t, -, hcase⟩ := hE
    have hRs : Group.IsSolvable ↥(Rt M (LB M Q B) t) := isSolvable_of_le_isSolvable hS (hRt t)
    rcases hcase with hE3 | hE4 | hE5
    · obtain ⟨-, -, hq⟩ := hE3
      rcases hq with hq | hq
      · exact not_quotSat_of_isSolvable (P := IsPSUModel 6 (Nat.card Z)) hS
          (not_isSolvable_of_isPSUModel hj) hq
      · exact not_quotSat_of_isSolvable (P := IsPSLModel 6 (Nat.card Z)) hS
          (not_isSolvable_of_isPSLModel hq4) hq
    · obtain ⟨-, -, hq, -⟩ := hE4
      exact not_quotSat_of_isSolvable (P := IsOmegaPlus 4 (Nat.card Z)) hRs
        (not_isSolvable_of_isOmegaPlus hCL (by norm_num) hq4 hq2) hq
    · obtain ⟨-, -, hq, -⟩ := hE5
      exact not_quotSat_of_isSolvable (P := IsOmegaPlus 6 (Nat.card Z)) hRs
        (not_isSolvable_of_isOmegaPlus hCL (by norm_num) hq4 hq2) hq
  ·
    rcases hT with ⟨hnTIM, K, hKF, hKfin, hKq, φ, hφ, hker, -⟩ | ⟨-, hD2, -⟩
    · rcases Nat.lt_or_ge n 2 with hn | hn
      ·
        have hSQ : Lgen M (LB M Q B) ≤ Q := by
          intro x hx
          have hmem : φ ⟨x, hx⟩ ∈ φ.range := MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩
          rw [hφ] at hmem
          have h1 : φ ⟨x, hx⟩ = 1 := eq_one_of_mem_statedSL (by omega) hmem
          have h2 : (⟨x, hx⟩ : ↥(Lgen M (LB M Q B))) ∈ φ.ker := MonoidHom.mem_ker.mpr h1
          rw [hker, Subgroup.mem_subgroupOf] at h2
          exact h2
        have hLQ : LB M Q B = Q :=
          le_antisymm (fun x hx => hSQ (mem_Lgen_of_mem hx)) le_sup_left
        apply hnTIM
        intro m hm
        left
        rw [hLQ, conjSubgroup_eq_self_iff.mpr (hyp.Q_normal.2 hm), inf_idem]
      ·
        have hSL : Group.IsSolvable ↥(StatedSL n K) := by
          haveI := hS
          rw [← hφ]
          exact solvable_of_surjective φ.rangeRestrict_surjective
        haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hKq.trans hj)
        have h4K : 4 ≤ Nat.card K := by rw [hKq]; exact hq4
        exact (hCL K h4K).1 n hn hSL
    · exact not_quotSat_isSLModel_of_solvable hCL hq4 hq2 (le_refl 2) hS hD2.2

theorem not_stronglyEmbedded_fstar {G : Type} [Group G] [Finite G]
    (M Q Z B : Subgroup G) (hc : RemCfg M Q Z B) :
    ¬ ∃ M' : Subgroup (FStar G), CFSG.IsStronglyEmbedded M' := by
  rintro ⟨H, hH⟩
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfus : CFSG.Open.fusionStronglyEmbedded H := hH
  have hCL : ClassicalNonsolvableStatement :=
    classicalNonsolvable_of_quasisimple classicalQuasisimpleStatement_holds
  have hyp := hc.ctx.hyp
  have hF : fittingSubgroup G = ⊥ := hyp.toTim81Hyp.fittingSubgroup_eq_bot hyp.q4
  obtain ⟨K, hK, hFK, hZK⟩ := exists_component_eq_generalizedFitting hyp
  obtain ⟨hsimple, -⟩ := Tim81.component_isSimple hF hK
  subst hFK
  haveI : IsSimpleGroup ↥(generalizedFitting G) := hsimple
  have hXn : (generalizedFitting G).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic).2
  have hQX : Q ≤ generalizedFitting G := Q_le_generalizedFitting hyp
  have hZX : Z ≤ generalizedFitting G := hZK
  obtain ⟨j, k, hj, hcp⟩ := hyp.cp
  have hq4 : 4 ≤ Nat.card Z := hyp.q4
  have hZne : Z ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hq4
    omega
  have hj2 : 2 ≤ j := by
    rcases Nat.lt_or_ge j 2 with h | h
    · interval_cases j <;> norm_num [hj] at hq4
    · exact h
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  have hzsq : (z : G) ^ 2 = 1 := sq_eq_one_of_cp hcp z z.2
  have hzne : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzX2 : (⟨(z : G), hZX z.2⟩ : FStar G) ^ 2 = 1 :=
    Subtype.ext (by simpa using hzsq)
  have hzX1 : (⟨(z : G), hZX z.2⟩ : FStar G) ≠ 1 := fun h => hzne (congrArg Subtype.val h)
  have hX2 : 2 ∣ Nat.card (FStar G) := by
    have := orderOf_dvd_natCard (⟨(z : G), hZX z.2⟩ : FStar G)
    rwa [orderOf_eq_prime hzX2 hzX1] at this
  have hO : ∀ R : Subgroup (FStar G), R.Normal → Odd (Nat.card R) → R = ⊥ := by
    intro R hRn hRodd
    haveI := hRn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R with h | h
    · exact h
    · exfalso
      rw [h, Subgroup.card_top] at hRodd
      exact (Nat.not_even_iff_odd.mpr hRodd) (even_iff_two_dvd.mpr hX2)
  have hZxcard : Nat.card (Z.subgroupOf (generalizedFitting G)) = 2 ^ j :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZX).toEquiv).trans hj
  obtain ⟨V, hVcard, -, hVZ⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (H := (⊥ : Subgroup (FStar G))) (L := Z.subgroupOf (generalizedFitting G)) (n := 2)
    (by rw [Subgroup.card_bot]; exact one_dvd _)
    (by rw [hZxcard]; exact pow_dvd_pow 2 hj2) bot_le
  have hV4 : Nat.card V = 4 := by rw [hVcard]; norm_num
  have hV2 : ∀ v ∈ V, v ^ 2 = 1 := by
    intro v hv
    have hvZ : ((v : FStar G) : G) ∈ Z := Subgroup.mem_subgroupOf.mp (hVZ hv)
    apply Subtype.ext
    simpa using sq_eq_one_of_cp hcp _ hvZ
  haveI hHs : Group.IsSolvable ↥H :=
    CFSG.Holt.isSolvable_of_fusionStronglyEmbedded hfus hO hV4 hV2
  obtain ⟨P, hPH⟩ := CFSG.Timmesfeld.Bridge.exists_sylow_le hfus
  have hZx2 : IsPGroup 2 (Z.subgroupOf (generalizedFitting G)) := IsPGroup.of_card hZxcard
  obtain ⟨c, -, hcZ⟩ := CFSG.QuasiDihedralFusion.exists_conj_le_sylow ⊤ P le_top
    (Z.subgroupOf (generalizedFitting G)) le_top hZx2
  have hWH : (Z.subgroupOf (generalizedFitting G)).map (MulAut.conj c).toMonoidHom ≤ H :=
    hcZ.trans hPH
  have hW2 : 2 ∣ Nat.card ((Z.subgroupOf (generalizedFitting G)).map
      (MulAut.conj c).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hZxcard]
    exact dvd_pow_self 2 (by omega)
  have hA : ∀ W' : Subgroup (FStar G), W' ≤ H → 2 ∣ Nat.card W' →
      ∀ w : FStar G, (∀ x ∈ W', w * x * w⁻¹ ∈ W') → w ∈ H := by
    intro W' hW'H h2 w hw
    by_contra hwH
    have hodd := hfus.2.2 w hwH
    have hle : W' ≤ H ⊓ conjugate H w := by
      intro x hx
      exact Subgroup.mem_inf.mpr
        ⟨hW'H hx, CFSG.Timmesfeld.Bridge.mem_map_conj_inv_iff.mpr (hW'H (hw x hx))⟩
    exact (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hle)))
      (even_iff_two_dvd.mpr h2)
  have hLM : LB M Q B ≤ M := sup_le hyp.Q_normal.1 inf_le_right
  have hLX : Lgen M (LB M Q B) ≤ generalizedFitting G := by
    have hL : LB M Q B ≤ generalizedFitting G := by
      refine sup_le hQX (inf_le_left.trans ?_)
      obtain ⟨g, -, hQg, -⟩ := IsZConjugate.QB_eq hyp hc.ctx.conj
      rw [hQg]
      intro y hy
      rw [mem_conjSubgroup] at hy
      have h := hXn.conj_mem _ (hQX hy) g
      rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at h
    unfold Lgen
    refine iSup₂_le fun m _ => ?_
    intro y hy
    rw [mem_conjSubgroup] at hy
    have h := hXn.conj_mem _ (hL hy) m
    rwa [show m * (m⁻¹ * y * m) * m⁻¹ = y by group] at h
  have hSH : ∀ s : FStar G, (s : G) ∈ Lgen M (LB M Q B) →
      c * s * c⁻¹ ∈ H := by
    intro s hs
    have hsM : (s : G) ∈ M := by
      unfold Lgen at hs
      exact (Lgen_le hLM : Lgen M (LB M Q B) ≤ M) hs
    have hsZ : ∀ z' ∈ Z.subgroupOf (generalizedFitting G),
        s * z' * s⁻¹ ∈ Z.subgroupOf (generalizedFitting G) := by
      intro z' hz'
      rw [Subgroup.mem_subgroupOf] at hz' ⊢
      exact (Subgroup.mem_normalizer_iff.mp (hyp.Z_normal.2 hsM) (z' : G)).mp hz'
    apply hA _ hWH hW2 (c * s * c⁻¹)
    rintro _ ⟨z', hz', rfl⟩
    have e : c * s * c⁻¹ * (MulAut.conj c).toMonoidHom z' * (c * s * c⁻¹)⁻¹ =
        (MulAut.conj c).toMonoidHom (s * z' * s⁻¹) := by
      show c * s * c⁻¹ * (c * z' * c⁻¹) * (c * s * c⁻¹)⁻¹ = c * (s * z' * s⁻¹) * c⁻¹
      group
    rw [e]
    exact Subgroup.mem_map_of_mem _ (hsZ z' hz')
  let Sx : Subgroup (FStar G) := (Lgen M (LB M Q B)).subgroupOf (generalizedFitting G)
  let f : ↥Sx →* ↥H := MonoidHom.codRestrict ((MulAut.conj c).toMonoidHom.comp Sx.subtype) H
    (fun s => hSH s.1 (Subgroup.mem_subgroupOf.mp s.2))
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : c * (x.1 : FStar G) * c⁻¹ = c * (y.1 : FStar G) * c⁻¹ := congrArg Subtype.val hxy
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  haveI hSxs : Group.IsSolvable ↥Sx := solvable_of_solvable_injective hf
  haveI hLs : Group.IsSolvable ↥(Lgen M (LB M Q B)) :=
    solvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hLX).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hLX).surjective
  exact not_isSolvable_lgen hCL hc hLs

end CFSG.RankThree.GF2n.Smith81
