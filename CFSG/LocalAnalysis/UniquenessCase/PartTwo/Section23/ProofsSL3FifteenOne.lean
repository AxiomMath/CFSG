module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsSL3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsFourN
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsSL3Fifteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SL3GeomParabolic
public import CFSG.GroupTheory.Commutator.JoinNormalizer
public import CFSG.GroupTheory.Frattini.MapSubtypeLe

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem s23fifteen_centralizerMod_isPGroup {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h4 : S23_4 D Ch) (h1930 : H1930 D) :
    IsPGroup 2 ↥(centralizerMod D.Z D.M (CFSG.Open.pCoreOf 2 D.M) ⊓
      Subgroup.centralizer (D.Z : Set G) : Subgroup G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUZ : D.U = D.Z := (h4 h1930 c.toCtx23L).1
  have hZM : D.M ≤ Subgroup.normalizer (D.Z : Set G) :=
    hUZ ▸ (h4 h1930 c.toCtx23L).2.2
  have hZ2 : IsPGroup 2 D.Z :=
    CFSG.Open.IsElemAbelian.isPGroup (c.isElemAbelian_Z h4 h1930)
  have hchar : CFSG.QuasithinUnique.CharTwo D.M :=
    D.standing.charTwo D.M D.maxLocal.1
  rintro ⟨d, hd⟩
  obtain ⟨n, hn⟩ := exists_pow_two_pow_eq_one_of_stability hZM hZ2 hchar
    hd.1.1 hd.2 hd.1.2.2
  exact ⟨n, Subtype.ext (by simpa using hn)⟩

private theorem s23fifteen_centralizerMod_le_pCoreOf {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hA2 : IsPGroup 2 ↥(centralizerMod D.Z D.M (CFSG.Open.pCoreOf 2 D.M) ⊓
      Subgroup.centralizer (D.Z : Set G) : Subgroup G)) :
    centralizerMod D.Z D.M (CFSG.Open.pCoreOf 2 D.M) ⊓
      Subgroup.centralizer (D.Z : Set G) ≤ CFSG.Open.pCoreOf 2 D.M := by
  classical
  let Q : Subgroup G := CFSG.Open.pCoreOf 2 D.M
  let A : Subgroup G := centralizerMod D.Z D.M Q ⊓ Subgroup.centralizer (D.Z : Set G)
  have hUZ : D.U = D.Z := (h4 h1930 c.toCtx23L).1
  have hZM : D.M ≤ Subgroup.normalizer (D.Z : Set G) :=
    hUZ ▸ (h4 h1930 c.toCtx23L).2.2
  have hQnorm : D.M ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) D.M
  have hA2' : IsPGroup 2 A := by simpa [A, Q] using hA2
  have hA_le_M : A ≤ D.M := inf_le_left.trans (centralizerMod_le_left D.Z D.M Q)
  have hA_norm : D.M ≤ Subgroup.normalizer (A : Set G) := by
    refine le_normalizer_inf ?_ ?_
    · exact le_normalizer_centralizerMod hZM Subgroup.le_normalizer hQnorm
    · exact hZM.trans (normalizer_le_normalizer_centralizer D.Z)
  have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2)
    hA_le_M hA_norm hA2'
  simpa [A, Q] using hle

private theorem s23fifteen_W_le_centralizerMod {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hWT : ⁅c.W, D.T⁆ ≤ D.Z) :
    c.W ≤ centralizerMod D.Z D.M (CFSG.Open.pCoreOf 2 D.M) ⊓
      Subgroup.centralizer (D.Z : Set G) := by
  classical
  let Q : Subgroup G := CFSG.Open.pCoreOf 2 D.M
  have hQ_le_T : Q ≤ D.T :=
    CFSG.Quasithin.E1.pCoreOf_two_le_of_isSylowIn
      (CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM)
  have hT_cent : D.T ≤ Subgroup.centralizer (D.Z : Set G) :=
    uc22main1_T_le_centralizer D
  have hW_le_T : c.W ≤ D.T := c.W_le_V.trans (c.V_le_T h4 h1930)
  have hW_le_M : c.W ≤ D.M := hW_le_T.trans D.sylowM.le
  have hW_cent : c.W ≤ Subgroup.centralizer (D.Z : Set G) := hW_le_T.trans hT_cent
  have hW_norm : c.W ≤ Subgroup.normalizer (D.Z : Set G) :=
    hW_cent.trans (Subgroup.centralizer_le_normalizer (D.Z : Set G))
  intro w hw
  refine ⟨?_, hW_cent hw⟩
  change w ∈ centralizerMod D.Z D.M Q
  rw [mem_centralizerMod]
  refine ⟨hW_le_M hw, hW_norm hw, ?_⟩
  intro q hq
  simpa [commutatorElement_def] using
    Subgroup.commutator_le.mp hWT w hw q (hQ_le_T hq)

private theorem s23fifteen_W_le_pCoreOf_M {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hWT : ⁅c.W, D.T⁆ ≤ D.Z) :
    c.W ≤ CFSG.Open.pCoreOf 2 D.M := by
  classical
  let Q : Subgroup G := CFSG.Open.pCoreOf 2 D.M
  let A : Subgroup G := centralizerMod D.Z D.M Q ⊓ Subgroup.centralizer (D.Z : Set G)
  have hW_le_A : c.W ≤ A := by
    simpa [A, Q] using s23fifteen_W_le_centralizerMod c h4 h1930 hWT
  have hA2 : IsPGroup 2 A := by
    simpa [A, Q] using s23fifteen_centralizerMod_isPGroup c h4 h1930
  have hA_le_Q : A ≤ Q := by
    simpa [A, Q] using s23fifteen_centralizerMod_le_pCoreOf c h4 h1930 hA2
  simpa [Q] using hW_le_A.trans hA_le_Q

private theorem s23fifteen_Wm_le_pCoreOf {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hWT : ⁅c.W, D.T⁆ ≤ D.Z) (m : ↥D.M) :
    c.W.map (MulAut.conj (m : G)).toMonoidHom ≤ CFSG.Open.pCoreOf 2 D.M := by
  let Q : Subgroup G := CFSG.Open.pCoreOf 2 D.M
  have hQnorm : D.M ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) D.M
  have hWQ : c.W ≤ Q := s23fifteen_W_le_pCoreOf_M c h4 h1930 hWT
  have h1 : c.W.map (MulAut.conj (m : G)).toMonoidHom ≤
      Q.map (MulAut.conj (m : G)).toMonoidHom := Subgroup.map_mono hWQ
  have h2 : Q.map (MulAut.conj (m : G)).toMonoidHom = Q :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQnorm m.2)
  rw [h2] at h1
  simpa [Q] using h1

private theorem s23fifteen_E_eq_iSup {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (hKW : conjClosure c.K c.W = c.V) :
    c.E = ⨆ m : ↥D.M, c.W.map (MulAut.conj (m : G)).toMonoidHom := by
  have hKM : c.K ≤ D.M := (uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_left
  rw [Ctx23L.E, ← hKW]
  exact (conjClosure_conjClosure_of_le hKM).trans (uc22br4_conjClosure_eq D.M c.W)

theorem Ctx2311.E_le_pCoreOf_M_of {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (h4 : S23_4 D Ch) (h1930 : H1930 D) (hWT : ⁅c.W, D.T⁆ ≤ D.Z)
    (hKW : conjClosure c.K c.W = c.V) :
    c.E ≤ CFSG.Open.pCoreOf 2 D.M := by
  rw [s23fifteen_E_eq_iSup c hKW]
  exact iSup_le fun m => s23fifteen_Wm_le_pCoreOf c h4 h1930 hWT m

private theorem s23fifteen_commutator_Wm_Wn_le_Z {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hWT : ⁅c.W, D.T⁆ ≤ D.Z) (m n : ↥D.M) :
    ⁅c.W.map (MulAut.conj (m : G)).toMonoidHom,
      c.W.map (MulAut.conj (n : G)).toMonoidHom⁆ ≤ D.Z := by
  classical
  let Q : Subgroup G := CFSG.Open.pCoreOf 2 D.M
  have hUZ : D.U = D.Z := (h4 h1930 c.toCtx23L).1
  have hZM : D.M ≤ Subgroup.normalizer (D.Z : Set G) :=
    hUZ ▸ (h4 h1930 c.toCtx23L).2.2
  have hQnorm : D.M ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) D.M
  have hQ_le_T : Q ≤ D.T :=
    CFSG.Quasithin.E1.pCoreOf_two_le_of_isSylowIn
      (CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM)
  have hQ_eq : Q.map (MulAut.conj (m : G)).toMonoidHom = Q :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQnorm m.2)
  have hWn_le_Tm : c.W.map (MulAut.conj (n : G)).toMonoidHom ≤
      D.T.map (MulAut.conj (m : G)).toMonoidHom := by
    calc c.W.map (MulAut.conj (n : G)).toMonoidHom ≤ Q :=
          s23fifteen_Wm_le_pCoreOf c h4 h1930 hWT n
      _ = Q.map (MulAut.conj (m : G)).toMonoidHom := hQ_eq.symm
      _ ≤ D.T.map (MulAut.conj (m : G)).toMonoidHom := Subgroup.map_mono hQ_le_T
  have hZm : D.Z.map (MulAut.conj (m : G)).toMonoidHom = D.Z :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hZM m.2)
  calc ⁅c.W.map (MulAut.conj (m : G)).toMonoidHom,
        c.W.map (MulAut.conj (n : G)).toMonoidHom⁆
      ≤ ⁅c.W.map (MulAut.conj (m : G)).toMonoidHom,
          D.T.map (MulAut.conj (m : G)).toMonoidHom⁆ :=
        Subgroup.commutator_mono le_rfl hWn_le_Tm
    _ = (⁅c.W, D.T⁆).map (MulAut.conj (m : G)).toMonoidHom :=
        (Subgroup.map_commutator c.W D.T
          (MulAut.conj (m : G)).toMonoidHom).symm
    _ ≤ D.Z := by
        have h := Subgroup.map_mono
          (f := (MulAut.conj (m : G)).toMonoidHom) hWT
        rwa [hZm] at h

theorem s23fifteen_commutator_E_E_le_Z {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hWT : ⁅c.W, D.T⁆ ≤ D.Z) (hKW : conjClosure c.K c.W = c.V) :
    ⁅c.E, c.E⁆ ≤ D.Z := by
  classical
  let Q : Subgroup G := CFSG.Open.pCoreOf 2 D.M
  have hQnorm : D.M ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) D.M
  have hQ_le_T : Q ≤ D.T :=
    CFSG.Quasithin.E1.pCoreOf_two_le_of_isSylowIn
      (CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM)
  have hT_cent : D.T ≤ Subgroup.centralizer (D.Z : Set G) :=
    uc22main1_T_le_centralizer D
  have hEeq := s23fifteen_E_eq_iSup c hKW
  have hWm_le_Q : ∀ m : ↥D.M,
      c.W.map (MulAut.conj (m : G)).toMonoidHom ≤ Q :=
    fun m => s23fifteen_Wm_le_pCoreOf c h4 h1930 hWT m
  have hWm_norm : ∀ m : ↥D.M,
      c.W.map (MulAut.conj (m : G)).toMonoidHom ≤
        Subgroup.normalizer (D.Z : Set G) := by
    intro m
    exact ((hWm_le_Q m).trans hQ_le_T).trans
      (hT_cent.trans (Subgroup.centralizer_le_normalizer (D.Z : Set G)))
  have hcomm_pair : ∀ m n : ↥D.M,
      ⁅c.W.map (MulAut.conj (m : G)).toMonoidHom,
        c.W.map (MulAut.conj (n : G)).toMonoidHom⁆ ≤ D.Z :=
    fun m n => s23fifteen_commutator_Wm_Wn_le_Z c h4 h1930 hWT m n
  have hcomm_left : ∀ m : ↥D.M,
      ⁅c.W.map (MulAut.conj (m : G)).toMonoidHom,
        (⨆ n : ↥D.M, c.W.map (MulAut.conj (n : G)).toMonoidHom)⁆ ≤ D.Z :=
    fun m => CFSG.GroupTheory.commutator_iSup_right_le_of_le_normalizer
      hWm_norm (hcomm_pair m)
  have hcomm_sup := CFSG.GroupTheory.commutator_iSup_left_le_of_le_normalizer
    hWm_norm hcomm_left
  rw [hEeq]
  exact hcomm_sup

private theorem s23fifteen_sq_mul_mem_Z {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) {a b : G} (haE : a ∈ c.E) (hbE : b ∈ c.E)
    (hT_cent : D.T ≤ Subgroup.centralizer (D.Z : Set G))
    (hE_le_T : c.E ≤ D.T) (hcommEE : ⁅c.E, c.E⁆ ≤ D.Z)
    (ha2 : a ^ 2 ∈ D.Z) (hb2 : b ^ 2 ∈ D.Z) :
    (a * b) ^ 2 ∈ D.Z := by
  have hc : ⁅b, a⁆ ∈ D.Z := Subgroup.commutator_le.mp hcommEE b hbE a haE
  have hca : a * ⁅b, a⁆ = ⁅b, a⁆ * a :=
    (Subgroup.mem_centralizer_iff.mp (hT_cent (hE_le_T haE)) _ hc).symm
  have hba : b * a = ⁅b, a⁆ * a * b := by
    rw [commutatorElement_def]
    group
  have hsq_ab : (a * b) ^ 2 = ⁅b, a⁆ * (a ^ 2) * (b ^ 2) := by
    rw [pow_two]
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (⁅b, a⁆ * a * b) * b := by rw [hba]
      _ = (a * ⁅b, a⁆) * a * b * b := by group
      _ = ⁅b, a⁆ * a * a * b * b := by rw [hca]
      _ = ⁅b, a⁆ * (a ^ 2) * (b ^ 2) := by
          rw [pow_two, pow_two]
          group
  rw [hsq_ab]
  exact D.Z.mul_mem (D.Z.mul_mem hc ha2) hb2

private theorem s23fifteen_sq_mem_closure {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (hWea : IsElemAbelian 2 c.W)
    (hT_cent : D.T ≤ Subgroup.centralizer (D.Z : Set G))
    (hE_le_T : c.E ≤ D.T) (hcommEE : ⁅c.E, c.E⁆ ≤ D.Z)
    (hEcl : c.E = Subgroup.closure (⋃ m : ↥D.M,
      (c.W.map (MulAut.conj (m : G)).toMonoidHom : Set G))) :
    ∀ x ∈ Subgroup.closure (⋃ m : ↥D.M,
      (c.W.map (MulAut.conj (m : G)).toMonoidHom : Set G)), x ^ 2 ∈ D.Z := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hy
      have h2 : y ^ 2 = 1 := (hWea.map (MulAut.conj (m : G)).toMonoidHom).2 y hm
      rw [h2]
      exact D.Z.one_mem
  | one => simp
  | mul a b ha hb iha ihb =>
      exact s23fifteen_sq_mul_mem_Z c (hEcl.symm ▸ ha) (hEcl.symm ▸ hb)
        hT_cent hE_le_T hcommEE iha ihb
  | inv a ha iha =>
      have h2 : (a⁻¹) ^ 2 = (a ^ 2)⁻¹ := by
        simp [pow_two, mul_inv_rev]
      rw [h2]
      exact D.Z.inv_mem iha

theorem s23fifteen_sq_mem_Z {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hWT : ⁅c.W, D.T⁆ ≤ D.Z) (hKW : conjClosure c.K c.W = c.V) :
    ∀ x ∈ c.E, x ^ 2 ∈ D.Z := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Subgroup G := CFSG.Open.pCoreOf 2 D.M
  have hEeq := s23fifteen_E_eq_iSup c hKW
  have hQ_le_T : Q ≤ D.T :=
    CFSG.Quasithin.E1.pCoreOf_two_le_of_isSylowIn
      (CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM)
  have hE_le_T : c.E ≤ D.T := by
    rw [hEeq]
    exact iSup_le fun m =>
      (s23fifteen_Wm_le_pCoreOf c h4 h1930 hWT m).trans hQ_le_T
  have hT_cent : D.T ≤ Subgroup.centralizer (D.Z : Set G) :=
    uc22main1_T_le_centralizer D
  have hWea : IsElemAbelian 2 c.W :=
    (c.isElemAbelian_V h4 h1930).mono c.W_le_V
  have hcommEE : ⁅c.E, c.E⁆ ≤ D.Z :=
    s23fifteen_commutator_E_E_le_Z c h4 h1930 hWT hKW
  have hEcl : c.E = Subgroup.closure (⋃ m : ↥D.M,
      (c.W.map (MulAut.conj (m : G)).toMonoidHom : Set G)) := by
    rw [hEeq, Subgroup.iSup_eq_closure]
  intro x hx
  rw [hEcl] at hx
  exact s23fifteen_sq_mem_closure c hWea hT_cent hE_le_T hcommEE hEcl x hx

private theorem s23fifteen_frattini_le_Z {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hWT : ⁅c.W, D.T⁆ ≤ D.Z) (hKW : conjClosure c.K c.W = c.V) :
    (frattini ↥c.E).map c.E.subtype ≤ D.Z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE2 : IsPGroup 2 ↥c.E :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M).to_le
      (Ctx2311.E_le_pCoreOf_M_of c h4 h1930 hWT hKW)
  exact CFSG.GroupTheory.frattini_map_subtype_le_of_commutator_le_of_pow_mem
    (p := 2) hE2 (s23fifteen_commutator_E_E_le_Z c h4 h1930 hWT hKW)
    (s23fifteen_sq_mem_Z c h4 h1930 hWT hKW)

private theorem s23fifteen_frattini_eq_Z {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h4 : S23_4 D Ch) (h4i : S23_4_inputN D Ch)
    (h14 : S23_14 D Ch) (h1930 : H1930 D)
    (hWT : ⁅c.W, D.T⁆ ≤ D.Z) (hKW : conjClosure c.K c.W = c.V) :
    (frattini ↥c.E).map c.E.subtype = D.Z := by
  have hphi_le_Z : (frattini ↥c.E).map c.E.subtype ≤ D.Z :=
    s23fifteen_frattini_le_Z c h4 h1930 hWT hKW
  have hUZ : D.U = D.Z := (h4 h1930 c.toCtx23L).1
  haveI : (frattini ↥c.E).Characteristic := frattini_characteristic (G := ↥c.E)
  have hMnormE : D.M ≤ Subgroup.normalizer (c.E : Set G) :=
    uc22p22v_le_normalizer_conjClosure D.M c.V
  have hMnormPhi : D.M ≤ Subgroup.normalizer
      ((frattini ↥c.E).map c.E.subtype : Set G) :=
    hMnormE.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (frattini ↥c.E))
  have hPhi_norm : X23_4 D c.N ⊓ D.M ≤ Subgroup.normalizer
      ((frattini ↥c.E).map c.E.subtype : Set G) :=
    inf_le_right.trans hMnormPhi
  have hIrr : IrrOn (X23_4 D c.N ⊓ D.M) D.U :=
    (h4i h1930 c.toCtx23L).2
  have hPhi_le_U : (frattini ↥c.E).map c.E.subtype ≤ D.U := by
    rw [hUZ]
    exact hphi_le_Z
  have hPhi_ne_bot : (frattini ↥c.E).map c.E.subtype ≠ ⊥ := by
    intro hbot
    exact h14 h1930 c
      ((Subgroup.map_eq_bot_iff_of_injective (frattini ↥c.E) (f := c.E.subtype)
        c.E.subtype_injective).mp hbot)
  rcases hIrr _ hPhi_le_U hPhi_norm with hbot | htop
  · exact absurd hbot hPhi_ne_bot
  · simpa [hUZ] using htop

theorem s23_15_1_of (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h4i : S23_4_inputN D Ch) (h14 : S23_14 D Ch)
    (hWT : H1930 D → ∀ c : Ctx2311 D Ch, ⁅c.W, D.T⁆ ≤ D.Z)
    (hKW : H1930 D → ∀ c : Ctx2311 D Ch, conjClosure c.K c.W = c.V) :
    S23_15_1 D Ch :=
  fun h1930 c => s23fifteen_frattini_eq_Z c h4 h4i h14 h1930 (hWT h1930 c) (hKW h1930 c)

theorem s23_19_of_sl3 (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h4i : S23_4_inputN D Ch) (h14 : S23_14 D Ch)
    (hE : UC22P20gExcFacts) (h207 : S20_7 D)
    (h2 : S23_2_natural D Ch) (h3 : S23_3 D Ch)
    (hline : S23_5_line D Ch) (hKN : KNshape) (hK : KOrdNatural) (hS : KSchurL2)
    (hS3 : KSchurSL3) (hN1 : S23_9_NotSp4SU4O6m D Ch) (hN2 : S23_9_NotO6p D Ch)
    (hN3 : S23_9_NotLarge D Ch) (hKS : KSL3Span) (hKL : KSL3Line) :
    S23_19 D Ch := by
  obtain ⟨hKW, -, -, -, hWT⟩ :=
    Ctx2311.geom2311_of D Ch hE h207 h2 h3 h4 hline hKN hK hS hS3 hN1 hN2 hN3 hKS hKL
  refine s23_19_of_isPGroup D Ch (s23_15_1_of D Ch h4 h4i h14 hWT hKW) ?_
  intro h1930 c
  exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M).to_le
    (Ctx2311.E_le_pCoreOf_M_of c h4 h1930 (hWT h1930 c) (hKW h1930 c))

end CFSG.LocalAnalysis.UniquenessCase.UC22
