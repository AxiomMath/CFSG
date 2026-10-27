module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDSixPlaneSU
public import CFSG.LocalAnalysis.StandardType.GGQTwoDGNOrthRefl
public import CFSG.LocalAnalysis.StandardType.GGQTwoSU34
public import CFSG.LocalAnalysis.StandardType.GGUnitaryTwoResidual
public import CFSG.ClassicalGroups.Unitary.Transitivity
import CFSG.ClassicalInvolution.Phan.PhanDn.PanelStab
import CFSG.ClassicalGroups.Orthogonal.SixPlane.Restrict
import CFSG.RankThree.Literature.FSmithOrthogonal
import CFSG.ClassicalGroups.Orthogonal.SixPlane.FrameGeometry
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltPlusD.NMPoly
import CFSG.LocalAnalysis.StandardType.PhanEBridgeGeom

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalGroups.Orthogonal.SixPlane (V Q Om rot crefl planeOf planeSpan mem_planeSpan
  single_mem_planeSpan supp mem_supp supp_mono supp_le_Om rot_mem_supp rot_pow_three commute_rot
  Q_single polar_single_inl_apply polar_single_inr_apply polar_single_single_of_planeOf_ne)
open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn CFSG.LieType.BorelTits
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary (coordBlockSU mem_coordBlockSU_iff
  blockSUOn coe_coe_blockSUOn)
open CFSG.ClassicalInvolution.Balance.StrongBalance.Linear (blockOn_apply_mem blockOn_apply_not_mem)
open CFSG.ClassicalInvolution.Models.OrthogonalPairs (QuadExt)
open CFSG.ClassicalGroups.Unitary (herm smul_def exists_mem_T_smul_eq_of_norm_one
  isUnitaryInvolution_unitaryInvolution)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local instance] ZMod.algebra

noncomputable section

section Gen

variable {n : ℕ}

variable (n) in
@[expose] def signedTripleJoin (S : Finset (Fin n)) : Subgroup (V n ≃ₗ[ZMod 2] V n) :=
  ⨆ (a : Fin n) (b : Fin n) (d : Fin n) (_ : a ∈ S ∧ b ∈ S ∧ d ∈ S ∧ a ≠ b ∧ a ≠ d ∧ b ≠ d)
    (u : ℕ) (w : ℕ) (_ : (u = 1 ∨ u = 2) ∧ (w = 1 ∨ w = 2)),
    Subgroup.closure {z | z ∈ supp n {a, b, d} ∧ (∃ k : ℕ, z ^ 2 ^ k = 1) ∧
      Commute z (rot n a ^ u * rot n b * rot n d ^ w)}

theorem signedTripleJoin_le_supp (S : Finset (Fin n)) : signedTripleJoin n S ≤ supp n S :=
  iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun h => iSup_le fun _ =>
    iSup_le fun _ => iSup_le fun _ => (Subgroup.closure_le _).mpr fun _ hz =>
      supp_mono (Finset.insert_subset h.1 (Finset.insert_subset h.2.1
        (Finset.singleton_subset_iff.mpr h.2.2.1))) hz.1

private lemma coordBlockSU_smul_eq_self_of_eq_zero {K : Type} [Field K] [Finite K] {p f : ℕ}
    [Fact p.Prime] [CharP K p] {T : Finset (Fin n)} {s : Su K p f n}
    (hs : s ∈ coordBlockSU K p f T) {x : Fin n → K} (hx : ∀ i ∈ T, x i = 0) : s • x = x := by
  have hmat := mem_coordBlockSU_iff.mp hs
  funext i
  rw [smul_def, Matrix.mulVec_apply_eq_sum]
  by_cases hi : i ∈ T
  · rw [hx i hi]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j ∈ T
    · rw [hx j hj, mul_zero]
    · have hij : i ≠ j := fun h => hj (h ▸ hi)
      rw [hmat i j (Or.inr hj), if_neg hij, zero_mul]
  · rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · rw [hmat i i (Or.inl hi), if_pos rfl, one_mul]
    · intro j _ hji
      rw [hmat i j (Or.inl hi), if_neg hji.symm, zero_mul]

private lemma blockSUOn_smul_apply_mem {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] {J : Finset (Fin n)} (t : Su K p f J.card) {x : Fin n → K} {i : Fin n}
    (hi : i ∈ J) :
    (blockSUOn K p f J t • x) i = (t • fun k => x (J.equivFin.symm k)) (J.equivFin ⟨i, hi⟩) := by
  rw [smul_def, coe_coe_blockSUOn, smul_def]
  simp only [Matrix.mulVec, dotProduct]
  rw [← Finset.sum_subset (Finset.subset_univ J)]
  · rw [← Finset.sum_coe_sort J, ← Equiv.sum_comp J.equivFin]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [blockOn_apply_mem J _ hi j.2]
    simp [Subtype.coe_eta, Equiv.symm_apply_apply]
  · intro j _ hj
    rw [blockOn_apply_not_mem J _ (Or.inr hj), if_neg fun h : i = j => hj (h ▸ hi), zero_mul]

private lemma blockSUOn_smul_apply_not_mem {K : Type} [Field K] [Finite K] {p f : ℕ}
    [Fact p.Prime] [CharP K p] {J : Finset (Fin n)} (t : Su K p f J.card) {x : Fin n → K}
    {i : Fin n} (hi : i ∉ J) : (blockSUOn K p f J t • x) i = x i := by
  rw [smul_def, coe_coe_blockSUOn]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · rw [blockOn_apply_not_mem J _ (Or.inl hi), if_pos rfl, one_mul]
  · intro j _ hji
    by_cases hj : j ∈ J
    · rw [blockOn_apply_not_mem J _ (Or.inl hi), if_neg (Ne.symm hji), zero_mul]
    · rw [blockOn_apply_not_mem J _ (Or.inr hj), if_neg (Ne.symm hji), zero_mul]
  · intro hi'
    exact absurd (Finset.mem_univ i) hi'

private lemma herm_comp_equivFin_of_vanishes {K : Type} [Field K] [Finite K] {p f : ℕ}
    [Fact p.Prime] [CharP K p] {J : Finset (Fin n)} {x : Fin n → K} (hx : ∀ i ∉ J, x i = 0) :
    herm (unitaryInvolution K p f) (fun k => x (J.equivFin.symm k))
      (fun k => x (J.equivFin.symm k)) = herm (unitaryInvolution K p f) x x := by
  simp only [herm]
  conv_rhs =>
    rw [← Finset.sum_subset (Finset.subset_univ J)
      fun i _ hi => by rw [hx i hi, map_zero, zero_mul]]
    rw [← Finset.sum_coe_sort J]
    rw [← Equiv.sum_comp J.equivFin.symm]

theorem exists_mem_coordBlockSU_smul_eq {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) {J : Finset (Fin n)} (hJ : 4 ≤ J.card)
    {x y : Fin n → K} (hx : ∀ i ∉ J, x i = 0) (hy : ∀ i ∉ J, y i = 0)
    (hxx : herm (unitaryInvolution K p f) x x = 1)
    (hyy : herm (unitaryInvolution K p f) y y = 1) :
    ∃ s ∈ coordBlockSU K p f J, s • x = y := by
  obtain ⟨t, _, ht⟩ := exists_mem_T_smul_eq_of_norm_one
    (isUnitaryInvolution_unitaryInvolution hK) (Or.inl hJ)
    ((herm_comp_equivFin_of_vanishes hx).trans hxx) ((herm_comp_equivFin_of_vanishes hy).trans hyy)
  refine ⟨blockSUOn K p f J t, ⟨t, rfl⟩, funext fun i => ?_⟩
  by_cases hi : i ∈ J
  · rw [blockSUOn_smul_apply_mem t hi, ht]
    simp only [Equiv.symm_apply_apply]
  · rw [blockSUOn_smul_apply_not_mem t hi, hx i hi, hy i hi]

section Unitary

variable {K : Type} [Field K] [Finite K] [CharP K 2] {ω : K} {c : Fin n → ZMod 3}

omit [Finite K] in
private lemma sixPlaneK_apply_eq_zero {T : Finset (Fin n)} {v : V n} (hv : v ∈ planeSpan n T)
    {i : Fin n} (hi : i ∉ T) : sixPlaneK ω c v i = 0 := by
  rw [sixPlaneK_apply, mem_planeSpan.mp hv (Sum.inl i) hi, mem_planeSpan.mp hv (Sum.inr i) hi,
    map_zero, zero_add, zero_mul]

private lemma sixConj_symm_apply (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)
    (hc : ∀ i, c i = 1 ∨ c i = -1) (g : (Fin n → K) ≃ₗ[ZMod 2] (Fin n → K)) (v : V n) :
    (sixConj ω c hK hω hc).symm g v =
      (sixPlaneEquiv ω c hK hω hc).symm (g (sixPlaneEquiv ω c hK hω hc v)) :=
  rfl

private lemma sixPlaneK_sixSU_apply (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)
    (hc : ∀ i, c i = 1 ∨ c i = -1) (s : Su K 2 1 n) (v : V n) :
    sixPlaneK ω c (sixSU ω c hK hω hc s v) = s • sixPlaneK ω c v := by
  rw [sixSU_apply, sixConj_symm_apply, ← sixPlaneEquiv_apply hK hω hc,
    LinearEquiv.apply_symm_apply, suEndN_apply, sixPlaneEquiv_apply]

theorem sixSU_mem_Om (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)
    (hc : ∀ i, c i = 1 ∨ c i = -1) (hn : 4 ≤ n) (s : Su K 2 1 n) :
    sixSU ω c hK hω hc s ∈ Om n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have E : QuadExt (ZMod 2) K (unitaryInvolution K 2 1) :=
    quadExt_of_card_of_char_two 1 (by rw [Nat.card_zmod, pow_one]) (by rw [hK]; norm_num)
  have h6 : 6 ≤ Module.finrank (ZMod 2) (V (m + 1)) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  have hmap : (TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))).map
      (sixConj ω c hK hω hc).symm.toMonoidHom ≤
        TauCeti.QuadraticMap.orthogonalGroup (Q (m + 1)) := by
    rintro _ ⟨g, hg, rfl⟩
    change g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)) at hg
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff] at hg ⊢
    intro v
    change Q (m + 1) ((sixConj ω c hK hω hc).symm g v) = Q (m + 1) v
    rw [sixConj_symm_apply, ← Qn_sixPlaneK E hω hc, ← Qn_sixPlaneK E hω hc,
      ← sixPlaneEquiv_apply hK hω hc, LinearEquiv.apply_symm_apply]
    exact hg (sixPlaneEquiv ω c hK hω hc v)
  have h1 : (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))).map
      (sixConj ω c hK hω hc).symm.toMonoidHom ≤ Om (m + 1) := by
    change Subgroup.map _ ⁅TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)),
      TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))⁆ ≤ Om (m + 1)
    rw [Subgroup.map_commutator]
    refine (Subgroup.commutator_mono hmap hmap).trans ?_
    rw [CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_omegaGroup
      (CFSG.ClassicalGroups.Orthogonal.SixPlane.nondegenerate_Q (m + 1)) h6]
  rw [sixSU_apply]
  exact h1 ⟨_, suEndN_mem_orthDerived (F := ZMod 2) (K := K) (f := 1) (E := E) (m := m) hn s, rfl⟩

theorem sixSU_mem_supp (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)
    (hc : ∀ i, c i = 1 ∨ c i = -1) (hn : 4 ≤ n) {T : Finset (Fin n)} {s : Su K 2 1 n}
    (hs : s ∈ coordBlockSU K 2 1 T) : sixSU ω c hK hω hc s ∈ supp n T := by
  refine mem_supp.mpr ⟨sixSU_mem_Om hK hω hc hn s, fun v hv => sixPlaneK_injective hω hc ?_⟩
  rw [sixPlaneK_sixSU_apply]
  exact coordBlockSU_smul_eq_self_of_eq_zero hs fun i hi =>
    sixPlaneK_apply_eq_zero hv (Finset.notMem_compl.mpr hi)

open scoped Matrix in
private lemma commute_suEndN_diagHom {J : Finset (Fin n)} {s : Su K 2 1 n}
    (hs : s ∈ coordBlockSU K 2 1 J)
    {t : Fin n → CFSG.LieType.Steinberg.normOne (unitaryInvolution K 2 1)}
    (ht : ∀ i ∈ J, ∀ j ∈ J, ((t i : Kˣ) : K) = ((t j : Kˣ) : K)) :
    Commute (suEndN (F := ZMod 2) (unitaryInvolution K 2 1) n s)
      (diagHom (ZMod 2) (unitaryInvolution K 2 1) n t) := by
  classical
  set v : Fin n → K := fun i => ((t i : Kˣ) : K) with hv
  have hvc : ∀ i ∈ J, ∀ j ∈ J, v i = v j := fun i hi j hj => by
    simpa only [hv] using ht i hi j hj
  have hmat :=
    CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary.diagonal_mul_comm_of_mem_coordBlockSU
      (p := 2) (f := 1) (v := v) hs hvc
  have hD : ∀ w : Fin n → K,
      diagHom (ZMod 2) (unitaryInvolution K 2 1) n t w = fun j => v j * w j := by
    intro w
    funext j
    rw [diagHom_apply, hv]
  have key : ∀ w : Fin n → K,
      (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (fun j => v j * w j)) =
        fun i => v i * ((((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) i) := by
    intro w
    have h1 : (fun j => v j * w j) = Matrix.diagonal v *ᵥ w := by
      funext j
      rw [Matrix.mulVec_diagonal]
    have h2 : (fun i => v i *
        ((((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) i)) =
        Matrix.diagonal v *ᵥ ((((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *ᵥ w) := by
      funext j
      rw [Matrix.mulVec_diagonal]
    rw [h1, h2]
    simp only [Matrix.mulVec_mulVec]
    rw [hmat]
  refine LinearEquiv.ext fun u => ?_
  simp only [LinearEquiv.mul_apply, suEndN_apply, CFSG.ClassicalGroups.Unitary.smul_def, hD]
  exact key u

theorem commute_sixSU_rot_triple (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)
    (hc : ∀ i, c i = 1 ∨ c i = -1) {a b d : Fin n} (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    {s : Su K 2 1 n} (hs : s ∈ coordBlockSU K 2 1 {a, b, d}) :
    Commute (sixSU ω c hK hω hc s)
      (rot n a ^ (c a).val * rot n b ^ (c b).val * rot n d ^ (c d).val) := by
  classical
  set t : Fin n → CFSG.LieType.Steinberg.normOne (unitaryInvolution K 2 1) :=
    Pi.mulSingle a (sixZeta hω) * Pi.mulSingle b (sixZeta hω) *
      Pi.mulSingle d (sixZeta hω) with ht
  have hP : sixConj ω c hK hω hc
      (rot n a ^ (c a).val * rot n b ^ (c b).val * rot n d ^ (c d).val) =
      diagHom (ZMod 2) (unitaryInvolution K 2 1) n t := by
    rw [ht]
    simp only [map_mul]
    rw [sixConj_rot_pow hK hω hc a, sixConj_rot_pow hK hω hc b, sixConj_rot_pow hK hω hc d]
  have ht_eq : ∀ i ∈ ({a, b, d} : Finset (Fin n)), t i = sixZeta hω := by
    intro i hi
    rw [ht]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [Pi.mul_apply, Pi.mulSingle_apply]
    rcases hi with rfl | rfl | rfl
    · rw [if_pos rfl, if_neg hab, if_neg had]
      simp
    · rw [if_neg (Ne.symm hab), if_pos rfl, if_neg hbd]
      simp
    · rw [if_neg (Ne.symm had), if_neg (Ne.symm hbd), if_pos rfl]
      simp
  have hconst : ∀ i ∈ ({a, b, d} : Finset (Fin n)), ∀ j ∈ ({a, b, d} : Finset (Fin n)),
      ((t i : Kˣ) : K) = ((t j : Kˣ) : K) := by
    intro i hi j hj
    rw [ht_eq i hi, ht_eq j hj]
  have h := (commute_suEndN_diagHom hs hconst).map (sixConj ω c hK hω hc).symm
  rw [← hP, MulEquiv.symm_apply_apply, ← sixSU_apply] at h
  exact h

theorem map_coordBlockSU_le_closure (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)
    (hc : ∀ i, c i = 1 ∨ c i = -1) (hn : 4 ≤ n) {a b d : Fin n} (hab : a ≠ b) (had : a ≠ d)
    (hbd : b ≠ d) :
    (coordBlockSU K 2 1 {a, b, d}).map (sixSU ω c hK hω hc) ≤
      Subgroup.closure {z | z ∈ supp n {a, b, d} ∧ (∃ k : ℕ, z ^ 2 ^ k = 1) ∧
        Commute z (rot n a ^ (c a).val * rot n b ^ (c b).val * rot n d ^ (c d).val)} := by
  classical
  set t : V n ≃ₗ[ZMod 2] V n :=
    rot n a ^ (c a).val * rot n b ^ (c b).val * rot n d ^ (c d).val
  set C : Subgroup (V n ≃ₗ[ZMod 2] V n) :=
    supp n {a, b, d} ⊓ Subgroup.centralizer {t} with hC
  let θ : Su K 2 1 ({a, b, d} : Finset (Fin n)).card →* (V n ≃ₗ[ZMod 2] V n) :=
    (sixSU ω c hK hω hc).comp (blockSUOn K 2 1 {a, b, d})
  have hθrange : θ.range = (coordBlockSU K 2 1 {a, b, d}).map (sixSU ω c hK hω hc) :=
    MonoidHom.range_comp (sixSU ω c hK hω hc) (blockSUOn K 2 1 {a, b, d})
  have hTcard : ({a, b, d} : Finset (Fin n)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, had]),
      Finset.card_insert_of_notMem (by simp [hbd]), Finset.card_singleton]
  have hθC : θ.range ≤ C := by
    rintro _ ⟨x, rfl⟩
    show (sixSU ω c hK hω hc) (blockSUOn K 2 1 {a, b, d} x) ∈ C
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact sixSU_mem_supp hK hω hc hn ⟨x, rfl⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (commute_sixSU_rot_triple hK hω hc hab had hbd ⟨x, rfl⟩).eq
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hgg : θ.range ≤ ggOTwoPrime C :=
    ggSu_range_le_ggOTwoPrime (f := 1) hK' (by rw [hTcard]; norm_num) θ hθC
  rw [hθrange] at hgg
  refine hgg.trans ?_
  rw [hC]
  unfold ggOTwoPrime
  refine Subgroup.closure_mono ?_
  rintro y ⟨hy, hy2⟩
  exact ⟨hy.1, hy2, Subgroup.mem_centralizer_singleton_iff.mp hy.2⟩

private lemma map_coordBlockSU_le_signedTripleJoin_of_card_three
    (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0) {A S : Finset (Fin n)} (hAS : A ⊆ S)
    (hA : A.card = 3) (hn : 4 ≤ n) :
    (coordBlockSU K 2 1 A).map (sixSU ω (fun _ => 1) hK hω fun _ => Or.inl rfl) ≤
      signedTripleJoin n S := by
  obtain ⟨a, b, d, hab, had, hbd, rfl⟩ := Finset.card_eq_three.mp hA
  have ha : a ∈ S := hAS (by simp)
  have hb : b ∈ S := hAS (by simp)
  have hd : d ∈ S := hAS (by simp)
  have hcl : (coordBlockSU K 2 1 {a, b, d}).map
      (sixSU ω (fun _ => 1) hK hω fun _ => Or.inl rfl) ≤
      Subgroup.closure {z | z ∈ supp n {a, b, d} ∧ (∃ k : ℕ, z ^ 2 ^ k = 1) ∧
        Commute z (rot n a ^ (1 : ZMod 3).val * rot n b ^ (1 : ZMod 3).val *
          rot n d ^ (1 : ZMod 3).val)} :=
    map_coordBlockSU_le_closure (c := fun _ => 1) hK hω (fun _ => Or.inl rfl) hn hab had hbd
  rw [show (1 : ZMod 3).val = 1 from rfl, pow_one, pow_one, pow_one] at hcl
  refine hcl.trans (le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le d (le_iSup_of_le
    ⟨ha, hb, hd, hab, had, hbd⟩ (le_iSup_of_le 1 (le_iSup_of_le 1 (le_iSup_of_le
      ⟨Or.inl rfl, Or.inl rfl⟩ le_rfl)))))))

theorem map_coordBlockSU_le_signedTripleJoin (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)
    {S : Finset (Fin n)} (hS : S.card = 4) :
    (coordBlockSU K 2 1 S).map (sixSU ω (fun _ => 1) hK hω fun _ => Or.inl rfl) ≤
      signedTripleJoin n S := by
  classical
  have hn : 4 ≤ n := by
    have h := Finset.card_le_univ S
    rw [Fintype.card_fin] at h
    omega
  obtain ⟨s₁, hs₁⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  have hA : (S.erase s₁).card = 3 := by rw [Finset.card_erase_of_mem hs₁, hS]
  obtain ⟨s₄, hs₄⟩ := Finset.card_pos.mp (by rw [hA]; norm_num : 0 < (S.erase s₁).card)
  have hs₄S : s₄ ∈ S := Finset.mem_of_mem_erase hs₄
  have hs₄₁ : s₄ ≠ s₁ := Finset.ne_of_mem_erase hs₄
  have hB : (S.erase s₄).card = 3 := by rw [Finset.card_erase_of_mem hs₄S, hS]
  have hAsub : S.erase s₁ ⊆ S := Finset.erase_subset s₁ S
  have hBsub : S.erase s₄ ⊆ S := Finset.erase_subset s₄ S
  have hAB : S.erase s₁ ∪ S.erase s₄ = S := by
    refine Finset.Subset.antisymm (Finset.union_subset hAsub hBsub) ?_
    intro x hx
    by_cases hx1 : x = s₁
    · subst hx1
      exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨Ne.symm hs₄₁, hs₁⟩)
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hx1, hx⟩)
  have hsup : coordBlockSU K 2 1 S =
      coordBlockSU K 2 1 (S.erase s₁) ⊔ coordBlockSU K 2 1 (S.erase s₄) := by
    have h := coordBlockSU_sup_three (K := K) hK hA hB (by rw [hAB, hS])
    rw [hAB] at h
    exact h.symm
  rw [hsup, Subgroup.map_sup]
  exact sup_le (map_coordBlockSU_le_signedTripleJoin_of_card_three hK hω hAsub hA hn)
    (map_coordBlockSU_le_signedTripleJoin_of_card_three hK hω hBsub hB hn)

private lemma herm_sixPlaneK (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)
    (hc : ∀ i, c i = 1 ∨ c i = -1) (v : V n) :
    herm (unitaryInvolution K 2 1) (sixPlaneK ω c v) (sixPlaneK ω c v) =
      algebraMap (ZMod 2) K (Q n v) := by
  have E : QuadExt (ZMod 2) K (unitaryInvolution K 2 1) :=
    quadExt_of_card_of_char_two 1 (by rw [Nat.card_zmod, pow_one]) (by rw [hK]; norm_num)
  rw [← Qn_sixPlaneK E hω hc, algebraMap_Qn, herm]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem exists_mem_coordBlockSU_sixSU_apply_eq (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)
    (hc : ∀ i, c i = 1 ∨ c i = -1) {S : Finset (Fin n)} (hS : 4 ≤ S.card) {v w : V n}
    (hv : v ∈ planeSpan n S) (hw : w ∈ planeSpan n S) (hQv : Q n v = 1) (hQw : Q n w = 1) :
    ∃ s ∈ coordBlockSU K 2 1 S, sixSU ω c hK hω hc s v = w := by
  have hK2 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  obtain ⟨s, hs, hsvw⟩ := exists_mem_coordBlockSU_smul_eq hK2 hS (x := sixPlaneK ω c v)
    (y := sixPlaneK ω c w) (fun _ hi => sixPlaneK_apply_eq_zero hv hi)
    (fun _ hi => sixPlaneK_apply_eq_zero hw hi) (by rw [herm_sixPlaneK hK hω hc, hQv, map_one])
    (by rw [herm_sixPlaneK hK hω hc, hQw, map_one])
  exact ⟨s, hs, sixPlaneK_injective hω hc (by rw [sixPlaneK_sixSU_apply, hsvw])⟩

end Unitary

private lemma crefl_mul_self (k : Fin n ⊕ Fin n) : crefl n k * crefl n k = 1 :=
  TauCeti.QuadraticMap.reflection_mul_self (Q n) (Pi.single k 1)

private lemma crefl_inv (k : Fin n ⊕ Fin n) : (crefl n k)⁻¹ = crefl n k :=
  inv_eq_of_mul_eq_one_right (crefl_mul_self k)

private lemma rot_pow_two_eq_inv (i : Fin n) : rot n i ^ 2 = (rot n i)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by simpa [pow_succ] using rot_pow_three i)

private lemma rot_pow_four (i : Fin n) : rot n i ^ 4 = rot n i := by
  rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, rot_pow_three, one_mul]

theorem crefl_mul_rot_mul_crefl (k : Fin n ⊕ Fin n) :
    crefl n k * rot n (planeOf k) * crefl n k = rot n (planeOf k) ^ 2 := by
  rw [rot_pow_two_eq_inv]
  rcases k with i | i
  · show crefl n (.inl i) * rot n i * crefl n (.inl i) = (rot n i)⁻¹
    rw [rot, ← mul_assoc, crefl_mul_self, one_mul, mul_inv_rev, crefl_inv, crefl_inv]
  · show crefl n (.inr i) * rot n i * crefl n (.inr i) = (rot n i)⁻¹
    rw [rot, mul_assoc, mul_assoc, crefl_mul_self, mul_one, mul_inv_rev, crefl_inv, crefl_inv]

private lemma commute_crefl_of_polar_eq_zero {k l : Fin n ⊕ Fin n}
    (h : QuadraticMap.polar (Q n) (Pi.single k 1) (Pi.single l 1) = 0) :
    Commute (crefl n k) (crefl n l) := by
  have h' : Commute (CFSG.ClassicalGroups.Orthogonal.reflect (Q n) (Pi.single k 1))
      (CFSG.ClassicalGroups.Orthogonal.reflect (Q n) (Pi.single l 1)) :=
    (CFSG.ClassicalGroups.Orthogonal.commute_reflect_iff (Q := Q n)
      (v := Pi.single k 1) (w := Pi.single l 1)
      (by rw [Q_single]) (by rw [Q_single])).mpr h
  rwa [CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflection,
    CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflection] at h'

theorem crefl_mul_rot_mul_crefl_of_ne {k : Fin n ⊕ Fin n} {j : Fin n} (h : planeOf k ≠ j) :
    crefl n k * rot n j * crefl n k = rot n j := by
  have hc : ∀ l, planeOf l = j → Commute (crefl n k) (crefl n l) := fun l hl =>
    commute_crefl_of_polar_eq_zero (polar_single_single_of_planeOf_ne (by rwa [hl]))
  have hr : Commute (crefl n k) (rot n j) := (hc (.inl j) rfl).mul_right (hc (.inr j) rfl)
  rw [hr.eq, mul_assoc, crefl_mul_self, mul_one]

private lemma crefl_apply (k : Fin n ⊕ Fin n) (v : V n) :
    crefl n k v = v + QuadraticMap.polar (Q n) (Pi.single k 1) v • Pi.single k 1 := by
  rw [crefl, TauCeti.QuadraticMap.reflection_apply, invOf_eq_inv, Q_single, inv_one, one_mul,
    sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq]

theorem crefl_mul_mul_crefl_mem_supp (k : Fin n ⊕ Fin n) {T : Finset (Fin n)}
    {g : V n ≃ₗ[ZMod 2] V n} (hg : g ∈ supp n T) : crefl n k * g * crefl n k ∈ supp n T := by
  obtain ⟨hgOm, hgfix⟩ := mem_supp.mp hg
  have hmem : ∀ v ∈ planeSpan n Tᶜ, crefl n k v ∈ planeSpan n Tᶜ := by
    intro v hv
    rw [crefl_apply]
    by_cases hkT : planeOf k ∈ T
    · have hpol : QuadraticMap.polar (Q n) (Pi.single k 1) v = 0 := by
        rcases k with i | i
        · rw [polar_single_inl_apply]
          exact mem_planeSpan.mp hv (Sum.inr i) (by simpa [planeOf] using hkT)
        · rw [polar_single_inr_apply]
          exact mem_planeSpan.mp hv (Sum.inl i) (by simpa [planeOf] using hkT)
      rwa [hpol, zero_smul, add_zero]
    · refine add_mem hv (Submodule.smul_mem _ _ (mem_planeSpan.mpr fun l hl => ?_))
      rw [Pi.single_apply, if_neg]
      rintro rfl
      exact hl (Finset.mem_compl.mpr hkT)
  refine mem_supp.mpr ⟨?_, fun v hv => ?_⟩
  · have hkO : crefl n k ∈ TauCeti.QuadraticMap.orthogonalGroup (Q n) :=
      TauCeti.QuadraticMap.reflection_mem_orthogonalGroup (Q n) (Pi.single k 1)
    rw [CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup]
    refine ⟨mul_mem (mul_mem hkO hgOm.1) hkO, ?_⟩
    have hconj : crefl n k * g * crefl n k = crefl n k * g * (crefl n k)⁻¹ := by
      rw [crefl_inv]
    rw [hconj, CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_conj]
    exact hgOm.2
  · have h2 : crefl n k (crefl n k v) = v := by
      simpa [LinearEquiv.mul_apply] using congrArg (fun e => e v) (crefl_mul_self k)
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hgfix _ (hmem v hv), h2]

private lemma rot_pow_two_mul (i : Fin n) {m : ℕ} (hm : m = 1 ∨ m = 2) :
    rot n i ^ (2 * m) = rot n i ^ (3 - m) := by
  rcases hm with rfl | rfl <;> simp [rot_pow_four]

private lemma rot_triple_sq {a b d : Fin n} {u w : ℕ} (hu : u = 1 ∨ u = 2)
    (hw : w = 1 ∨ w = 2) :
    (rot n a ^ u * rot n b ^ 2 * rot n d ^ w) ^ 2 =
      rot n a ^ (3 - u) * rot n b * rot n d ^ (3 - w) := by
  have hab : Commute (rot n a ^ u) (rot n b ^ 2) := (commute_rot a b).pow_pow u 2
  have habd : Commute (rot n a ^ u * rot n b ^ 2) (rot n d ^ w) :=
    ((commute_rot a d).pow_pow u w).mul_left ((commute_rot b d).pow_pow 2 w)
  rw [habd.mul_pow, hab.mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm u, mul_comm w,
    rot_pow_two_mul a hu, rot_pow_two_mul d hw, show 2 * 2 = 4 from rfl, rot_pow_four]

private lemma exists_pow_conj_crefl_rot_triple {s₀ a b d : Fin n} (hab : a ≠ b) (had : a ≠ d)
    (hbd : b ≠ d) {u w : ℕ} (huw : (u = 1 ∨ u = 2) ∧ (w = 1 ∨ w = 2)) :
    ∃ u' w' m : ℕ, ((u' = 1 ∨ u' = 2) ∧ (w' = 1 ∨ w' = 2)) ∧
      MulAut.conj (crefl n (Sum.inl s₀)) (rot n a ^ u * rot n b * rot n d ^ w) ^ m =
        rot n a ^ u' * rot n b * rot n d ^ w' := by
  have hs : MulAut.conj (crefl n (Sum.inl s₀)) (rot n s₀) = rot n s₀ ^ 2 := by
    rw [MulAut.conj_apply, crefl_inv]
    exact crefl_mul_rot_mul_crefl (.inl s₀)
  have hne : ∀ {i}, s₀ ≠ i → MulAut.conj (crefl n (Sum.inl s₀)) (rot n i) = rot n i := by
    intro i hi
    rw [MulAut.conj_apply, crefl_inv]
    exact crefl_mul_rot_mul_crefl_of_ne hi
  have h3 : ∀ m : ℕ, m = 1 ∨ m = 2 → 3 - m = 1 ∨ 3 - m = 2 := fun m hm => by omega
  simp only [map_mul, map_pow]
  by_cases hsa : s₀ = a
  · subst hsa
    exact ⟨3 - u, w, 1, ⟨h3 u huw.1, huw.2⟩, by
      rw [pow_one, hs, hne hab, hne had, ← pow_mul, rot_pow_two_mul _ huw.1]⟩
  by_cases hsb : s₀ = b
  · subst hsb
    refine ⟨3 - u, 3 - w, 2, ⟨h3 u huw.1, h3 w huw.2⟩, ?_⟩
    rw [hne (Ne.symm hab), hs, hne hbd]
    exact rot_triple_sq huw.1 huw.2
  by_cases hsd : s₀ = d
  · subst hsd
    exact ⟨u, 3 - w, 1, ⟨huw.1, h3 w huw.2⟩, by
      rw [pow_one, hne (Ne.symm had), hne (Ne.symm hbd), hs, ← pow_mul, rot_pow_two_mul _ huw.2]⟩
  exact ⟨u, w, 1, huw, by rw [pow_one, hne hsa, hne hsb, hne hsd]⟩

private lemma mem_signedTripleJoin_of_generator {S : Finset (Fin n)} {a b d : Fin n}
    (habd : a ∈ S ∧ b ∈ S ∧ d ∈ S ∧ a ≠ b ∧ a ≠ d ∧ b ≠ d)
    {u w : ℕ} (huw : (u = 1 ∨ u = 2) ∧ (w = 1 ∨ w = 2))
    {z : V n ≃ₗ[ZMod 2] V n}
    (hz : z ∈ supp n {a, b, d} ∧ (∃ k : ℕ, z ^ 2 ^ k = 1) ∧
      Commute z (rot n a ^ u * rot n b * rot n d ^ w)) :
    z ∈ signedTripleJoin n S := by
  have hle : Subgroup.closure {z | z ∈ supp n {a, b, d} ∧
      (∃ k : ℕ, z ^ 2 ^ k = 1) ∧
      Commute z (rot n a ^ u * rot n b * rot n d ^ w)} ≤ signedTripleJoin n S :=
    le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le d (le_iSup_of_le habd
      (le_iSup_of_le u (le_iSup_of_le w (le_iSup_of_le huw le_rfl))))))
  exact hle (Subgroup.subset_closure hz)

private lemma conj_crefl_mem_signedTripleJoin {S : Finset (Fin n)} (s₀ : Fin n) {a b d : Fin n}
    (habd : a ∈ S ∧ b ∈ S ∧ d ∈ S ∧ a ≠ b ∧ a ≠ d ∧ b ≠ d) {u w : ℕ}
    (huw : (u = 1 ∨ u = 2) ∧ (w = 1 ∨ w = 2)) {z : V n ≃ₗ[ZMod 2] V n}
    (hz : z ∈ supp n {a, b, d} ∧ (∃ k : ℕ, z ^ 2 ^ k = 1) ∧
      Commute z (rot n a ^ u * rot n b * rot n d ^ w)) :
    MulAut.conj (crefl n (Sum.inl s₀)) z ∈ signedTripleJoin n S := by
  obtain ⟨u', w', m, huw', ht⟩ := exists_pow_conj_crefl_rot_triple (s₀ := s₀) habd.2.2.2.1
    habd.2.2.2.2.1 habd.2.2.2.2.2 huw
  obtain ⟨hzs, ⟨k, hk⟩, hzc⟩ := hz
  refine mem_signedTripleJoin_of_generator habd huw' ⟨?_, ⟨k, ?_⟩, ?_⟩
  · rw [MulAut.conj_apply, crefl_inv]
    exact crefl_mul_mul_crefl_mem_supp _ hzs
  · rw [← map_pow, hk, map_one]
  · rw [← ht]
    exact (hzc.map (MulAut.conj (crefl n (Sum.inl s₀)))).pow_right m

theorem crefl_mul_mul_crefl_mem_signedTripleJoin {S : Finset (Fin n)} (s₀ : Fin n)
    {g : V n ≃ₗ[ZMod 2] V n} (hg : g ∈ signedTripleJoin n S) :
    crefl n (Sum.inl s₀) * g * crefl n (Sum.inl s₀) ∈ signedTripleJoin n S := by
  suffices h : signedTripleJoin n S ≤
      (signedTripleJoin n S).comap (MulAut.conj (crefl n (Sum.inl s₀))).toMonoidHom by
    have h' := h hg
    rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, crefl_inv] at h'
  refine iSup_le fun a => iSup_le fun b => iSup_le fun d => iSup_le fun habd => ?_
  refine iSup_le fun u => iSup_le fun w => iSup_le fun huw => ?_
  rw [Subgroup.closure_le]
  exact fun z hz => conj_crefl_mem_signedTripleJoin s₀ habd huw hz

theorem supp_le_of_crefl {S : Finset (Fin n)} (hS : 3 ≤ S.card)
    {H : Subgroup (V n ≃ₗ[ZMod 2] V n)} (hH : H ≤ supp n S) {s₀ : Fin n} (hs₀ : s₀ ∈ S)
    (hrH : ∀ h ∈ H, crefl n (Sum.inl s₀) * h * crefl n (Sum.inl s₀) ∈ H)
    (htr : ∀ w ∈ planeSpan n S, Q n w = 1 → ∃ h ∈ H, h (Pi.single (Sum.inl s₀) 1) = w) :
    supp n S ≤ H := by
  have hcrefl : crefl n (Sum.inl s₀) =
      CFSG.ClassicalGroups.Orthogonal.reflect (Q n) (Pi.single (Sum.inl s₀) 1) :=
    (CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflection (Q := Q n)
      (v := Pi.single (Sum.inl s₀) (1 : ZMod 2))).symm
  rw [hcrefl] at hrH
  exact CFSG.ClassicalGroups.Orthogonal.SixPlane.supp_le_of_reflect hS hH
    (single_mem_planeSpan (k := Sum.inl s₀) hs₀) (Q_single n (Sum.inl s₀)) hrH htr

theorem supp_le_signedTripleJoin {S : Finset (Fin n)} (hS : S.card = 4) :
    supp n S ≤ signedTripleJoin n S := by
  classical
  have hK4 : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨ω, hω⟩ :=
    CFSG.HardMathSupport.Curtis.NaturalModuleCensus.NM_exists_root (K := GaloisField 2 2) hK4
  obtain ⟨s₀, hs₀⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  refine supp_le_of_crefl (H := signedTripleJoin n S) (by omega : 3 ≤ S.card)
    (signedTripleJoin_le_supp S) hs₀ ?_ ?_
  · intro h hh
    exact crefl_mul_mul_crefl_mem_signedTripleJoin s₀ hh
  · intro w hw hQw
    obtain ⟨s, hs, hsv⟩ :=
      exists_mem_coordBlockSU_sixSU_apply_eq (K := GaloisField 2 2) (ω := ω)
        (c := fun _ => 1) hK4 hω (fun _ => Or.inl rfl) (S := S) (by omega : 4 ≤ S.card)
        (single_mem_planeSpan (k := Sum.inl s₀) hs₀) hw (Q_single n (Sum.inl s₀)) hQw
    refine ⟨sixSU ω (fun _ => 1) hK4 hω (fun _ => Or.inl rfl) s, ?_, hsv⟩
    exact map_coordBlockSU_le_signedTripleJoin (K := GaloisField 2 2) (ω := ω) hK4 hω hS
      (Subgroup.mem_map_of_mem _ hs)

end Gen

theorem supp_le_iSup_signedTriple {n : ℕ} {S : Finset (Fin n)} (hS : S.card = 4) :
    supp n S ≤ ⨆ (a : Fin n) (b : Fin n) (d : Fin n)
      (_ : a ∈ S ∧ b ∈ S ∧ d ∈ S ∧ a ≠ b ∧ a ≠ d ∧ b ≠ d) (u : ℕ) (w : ℕ)
      (_ : (u = 1 ∨ u = 2) ∧ (w = 1 ∨ w = 2)),
      Subgroup.closure {z | z ∈ supp n {a, b, d} ∧ (∃ k : ℕ, z ^ 2 ^ k = 1) ∧
        Commute z (rot n a ^ u * rot n b * rot n d ^ w)} :=
  supp_le_signedTripleJoin hS

end

end CFSG.StandardType.QTwo

end
