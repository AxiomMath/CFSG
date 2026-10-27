module

public import CFSG.Quasithin.Recognition.Stroth.Str86FieldAutVertex
public import CFSG.Quasithin.Recognition.Stroth.BenderAut
public import CFSG.Quasithin.Recognition.Stroth.BenderFrame

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

abbrev str86S' (L1 L2 S : Subgroup G) : Subgroup G :=
  (S ⊓ L1) ⊔ (S ⊓ L2)

abbrev Str86AutFact (L : Subgroup G) : Prop :=
  ∀ (T : Sylow 2 (oTwoQuot ↥L)) (H : Subgroup (oTwoQuot ↥L)),
    H ≤ Subgroup.normalizer ((T : Subgroup (oTwoQuot ↥L)) : Set _) →
    Odd (Nat.card H) →
    (T : Subgroup (oTwoQuot ↥L)) ⊔ H =
      Subgroup.normalizer ((T : Subgroup (oTwoQuot ↥L)) : Set _) →
    ∀ σ : MulAut (oTwoQuot ↥L), (∃ k : ℕ, σ ^ (2 ^ k) = 1) →
      (∀ x ∈ (T : Subgroup _), σ x ∈ (T : Subgroup _)) →
      (∀ h ∈ H, σ h = h) → σ = 1

theorem str86S'_le (L1 L2 S : Subgroup G) : str86S' L1 L2 S ≤ S :=
  sup_le inf_le_left inf_le_left

theorem str86S'_comm (L1 L2 S : Subgroup G) :
    str86S' L2 L1 S = str86S' L1 L2 S := by
  rw [str86S', str86S', sup_comm]

theorem sup_inf_str86S' (L1 L2 S : Subgroup G) :
    (str86S' L1 L2 S ⊓ L1) ⊔ (str86S' L1 L2 S ⊓ L2) = str86S' L1 L2 S := by
  rw [str86S', sup_inf_inf_left, sup_inf_inf_right]

theorem borelOf_str86S'_left (L1 L2 S : Subgroup G) :
    borelOf L1 (str86S' L1 L2 S) = borelOf L1 S := by
  rw [borelOf, borelOf, str86S', sup_inf_inf_left]

theorem borelOf_str86S'_right (L1 L2 S : Subgroup G) :
    borelOf L2 (str86S' L1 L2 S) = borelOf L2 S := by
  rw [borelOf, borelOf, str86S', sup_inf_inf_right]

theorem bigB_eq_bigB_str86S'_sup (L1 L2 S : Subgroup G) :
    bigB L1 L2 S = bigB L1 L2 (str86S' L1 L2 S) ⊔ S := by
  rw [bigB, bigB, borelOf_str86S'_left, borelOf_str86S'_right]
  rw [show (borelOf L1 S ⊔ borelOf L2 S) ⊔ str86S' L1 L2 S ⊔ S =
      (borelOf L1 S ⊔ borelOf L2 S) ⊔ S by
    rw [sup_assoc, sup_eq_right.mpr (str86S'_le L1 L2 S)]]

theorem str86S'_le_bigB (L1 L2 S : Subgroup G) :
    str86S' L1 L2 S ≤ bigB L1 L2 (str86S' L1 L2 S) :=
  show str86S' L1 L2 S ≤
    (borelOf L1 (str86S' L1 L2 S) ⊔ borelOf L2 (str86S' L1 L2 S)) ⊔
      str86S' L1 L2 S from le_sup_right

theorem str86S'_le_P1_str86S' (L1 L2 S : Subgroup G) :
    str86S' L1 L2 S ≤ P1 L1 L2 (str86S' L1 L2 S) :=
  (str86S'_le_bigB L1 L2 S).trans
    (show bigB L1 L2 (str86S' L1 L2 S) ≤ P1 L1 L2 (str86S' L1 L2 S)
      from le_sup_right)

theorem le_normalizer_pCoreOf_P1 (L1 L2 S : Subgroup G) :
    P1 L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
  le_normalizer_pCoreOf 2 (P1 L1 L2 S)

theorem le_normalizer_bigB_str86S' {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) :
    S ≤ Subgroup.normalizer (bigB L1 L2 (str86S' L1 L2 S) : Set G) := by
  have hSnS' : S ≤ Subgroup.normalizer (str86S' L1 L2 S : Set G) := by
    rw [str86S']
    exact F1.le_normalizer_sup (F1.le_normalizer_inf_of_le hF.1.h1.normalizes)
      (F1.le_normalizer_inf_of_le hF.1.h2.normalizes)
  have hSnB1 : S ≤ Subgroup.normalizer (borelOf L1 (str86S' L1 L2 S) : Set G) := by
    rw [borelOf_str86S'_left]
    exact F1.le_normalizer_borelOf hF.1.h1.normalizes
  have hSnB2 : S ≤ Subgroup.normalizer (borelOf L2 (str86S' L1 L2 S) : Set G) := by
    rw [borelOf_str86S'_right]
    exact F1.le_normalizer_borelOf hF.1.h2.normalizes
  show S ≤ Subgroup.normalizer
    (((borelOf L1 (str86S' L1 L2 S) ⊔ borelOf L2 (str86S' L1 L2 S)) ⊔
      str86S' L1 L2 S : Subgroup G) : Set G)
  exact F1.le_normalizer_sup (F1.le_normalizer_sup hSnB1 hSnB2) hSnS'

theorem le_normalizer_P1_str86S' {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) :
    S ≤ Subgroup.normalizer (P1 L1 L2 (str86S' L1 L2 S) : Set G) := by
  show S ≤ Subgroup.normalizer
    ((L1 ⊔ bigB L1 L2 (str86S' L1 L2 S) : Subgroup G) : Set G)
  exact F1.le_normalizer_sup hF.1.h1.normalizes (le_normalizer_bigB_str86S' hF)

theorem le_pCoreOf_of_vertex_cartan
    {L1 L2 S D : Subgroup G} (hF : F112Hyp L1 L2 S) (hAut : Str86AutFact L1)
    (hNF : Str86NF L1 (Q1 L1 L2 (str86S' L1 L2 S)) (Z1 L1 L2 (str86S' L1 L2 S)))
    (hDborel : D ≤ borelOf L1 S) (hDodd : Odd (Nat.card D))
    (hDsup : (S ⊓ L1) ⊔ D = borelOf L1 S) :
    S ⊓ Subgroup.centralizer (D : Set G) ≤ Q1 L1 L2 S := by
  classical
  have hF' : F112Hyp L1 L2 (str86S' L1 L2 S) := f112Hyp_sup_inf hF
  have hSB' : bigB L1 L2 (str86S' L1 L2 S) ≤
      Subgroup.normalizer (str86S' L1 L2 S : Set G) :=
    bigB_le_normalizer_of_sup_inf_eq hF'.1 (sup_inf_str86S' L1 L2 S)
  have hB_eq : bigB L1 L2 S = bigB L1 L2 (str86S' L1 L2 S) ⊔ S :=
    bigB_eq_bigB_str86S'_sup L1 L2 S
  have hP_eq : P1 L1 L2 S = P1 L1 L2 (str86S' L1 L2 S) ⊔ S := by
    rw [P1, P1, hB_eq, sup_assoc]
  have hSP' : S ≤ Subgroup.normalizer (P1 L1 L2 (str86S' L1 L2 S) : Set G) :=
    le_normalizer_P1_str86S' hF
  have hSyl' : IsSylowTwoOf (str86S' L1 L2 S) (P1 L1 L2 (str86S' L1 L2 S)) :=
    f112_isSylowTwoOf_P1 hF'.toW
  have hS'odd : Odd ((str86S' L1 L2 S).relIndex (P1 L1 L2 (str86S' L1 L2 S))) := by
    simpa only [Subgroup.relIndex] using
      (Nat.not_even_iff_odd.mp fun he => hSyl'.2.2 (even_iff_two_dvd.mp he))
  have hS'P' : str86S' L1 L2 S ≤ P1 L1 L2 (str86S' L1 L2 S) :=
    str86S'_le_P1_str86S' L1 L2 S
  have hLP' : L1 ≤ P1 L1 L2 (str86S' L1 L2 S) := le_sup_left
  have hP'Q' : P1 L1 L2 (str86S' L1 L2 S) ≤
      Subgroup.normalizer (Q1 L1 L2 (str86S' L1 L2 S) : Set G) :=
    le_normalizer_pCoreOf_P1 L1 L2 (str86S' L1 L2 S)
  have hSnQ' : S ≤ Subgroup.normalizer (Q1 L1 L2 (str86S' L1 L2 S) : Set G) :=
    hSP'.trans (normalizer_le_normalizer_pCoreOf 2 (P1 L1 L2 (str86S' L1 L2 S)))
  have hPQ' : P1 L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 (str86S' L1 L2 S) : Set G) := by
    rw [hP_eq]
    exact sup_le hP'Q' hSnQ'
  have hPZ' : P1 L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 (str86S' L1 L2 S) : Set G) :=
    hPQ'.trans (CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneCenterOf _)
  have hPL : P1 L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    sup_le Subgroup.le_normalizer (bigB_le_normalizer_of_hyp111 hF.1)
  have hTL : ∀ t ∈ S ⊓ Subgroup.centralizer (D : Set G), ∀ l ∈ L1,
      t * l * t⁻¹ * l⁻¹ ∈ Q1 L1 L2 (str86S' L1 L2 S) := by
    intro t ht l hl
    have htS : t ∈ S := ht.1
    have htC : t ∈ Subgroup.centralizer (D : Set G) := ht.2
    have hσ1 : oTwoQuotConj L1 ⟨t, hF.1.h1.normalizes htS⟩ = 1 :=
      oTwoQuotConj_eq_one_of_autFact hF.1 hAut hDborel hDsup hDodd htS htC
    have hker := (oTwoQuotConj_eq_one_iff L1 ⟨t, hF.1.h1.normalizes htS⟩).mp hσ1 l hl
    have hcomm : t * l * t⁻¹ * l⁻¹ ∈ pCoreOf 2 L1 :=
      commutator_of_inv_right_mem (le_normalizer_pCoreOf 2 L1 hl) hker
    exact (Hyp111.pCoreOf_le_pCoreOf_vertex hF'.1) hcomm
  have hE2 : ∀ s ∈ str86S' L1 L2 S,
      (∀ l ∈ L1, s * l * s⁻¹ * l⁻¹ ∈ Q1 L1 L2 (str86S' L1 L2 S)) →
      s ∈ Q1 L1 L2 (str86S' L1 L2 S) := by
    intro s hs hcomm
    refine mem_pCoreOf_of_commutator_mem hF'.1 hSB' hs (fun l hl => ?_)
    exact commutator_inv_inv_mem (hP'Q' (hS'P' hs)) (hP'Q' (hLP' hl)) (hcomm l hl)
  have hC7 : P1 L1 L2 (str86S' L1 L2 S) ⊓
      Subgroup.centralizer (Q1 L1 L2 (str86S' L1 L2 S) : Set G) ≤
      Q1 L1 L2 (str86S' L1 L2 S) :=
    F1.parabolic_charTwo (Hyp111R.of_hyp111 rankOneListedFacts hF'.1)
  exact le_pCoreOf_of_fieldAut (P := P1 L1 L2 S) (P' := P1 L1 L2 (str86S' L1 L2 S))
    (L := L1) (S := S) (S' := str86S' L1 L2 S)
    (T := S ⊓ Subgroup.centralizer (D : Set G))
    (Q' := Q1 L1 L2 (str86S' L1 L2 S)) (Z' := Z1 L1 L2 (str86S' L1 L2 S))
    hP_eq hSP' hF.1.h1.pgroup (str86S'_le L1 L2 S) hS'P' hS'odd rfl
    (CFSG.Quasithin.A4.omegaOneCenterOf_le _) hPQ' hPZ' hLP' hPL inf_le_left hTL hE2 hC7 hNF

theorem eq_sup_str86S'_pCoreOf_of_cartan {L1 L2 S D : Subgroup G}
    (hSdec : S = (S ⊓ L1) ⊔ (S ⊓ Subgroup.centralizer (D : Set G)))
    (hTQ : S ⊓ Subgroup.centralizer (D : Set G) ≤ Q1 L1 L2 S)
    (hQ1S : Q1 L1 L2 S ≤ S) :
    S = str86S' L1 L2 S ⊔ Q1 L1 L2 S := by
  have hS1 : S ⊓ L1 ≤ str86S' L1 L2 S := by
    rw [str86S']
    exact le_sup_left
  refine le_antisymm ?_ (sup_le (str86S'_le L1 L2 S) hQ1S)
  calc S = (S ⊓ L1) ⊔ (S ⊓ Subgroup.centralizer (D : Set G)) := hSdec
    _ ≤ str86S' L1 L2 S ⊔ Q1 L1 L2 S :=
      sup_le (hS1.trans le_sup_left) (hTQ.trans le_sup_right)

theorem eq_sup_str86S'_pCoreOf_of_vertex
    {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S)
    (hAut : Str86AutFact L1)
    (hNF : Str86NF L1 (Q1 L1 L2 (str86S' L1 L2 S)) (Z1 L1 L2 (str86S' L1 L2 S)))
    (h1n : (S.subgroupOf (S ⊔ borelOf L1 S)).Normal) :
    S = str86S' L1 L2 S ⊔ Q1 L1 L2 S := by
  classical
  have hF' : F112Hyp L1 L2 (str86S' L1 L2 S) := f112Hyp_sup_inf hF
  have hSB' : bigB L1 L2 (str86S' L1 L2 S) ≤
      Subgroup.normalizer (str86S' L1 L2 S : Set G) :=
    bigB_le_normalizer_of_sup_inf_eq hF'.1 (sup_inf_str86S' L1 L2 S)
  obtain ⟨D, hDborel, hDodd, hDsup, -⟩ :=
    exists_complement_eq_sup_centralizer hF'.1 hSB'
  have hDborel' : D ≤ borelOf L1 S := by
    rw [← borelOf_str86S'_left L1 L2 S]
    exact hDborel
  have hDn : D ≤ Subgroup.normalizer (S : Set G) :=
    hDborel'.trans ((le_sup_right : borelOf L1 S ≤ S ⊔ borelOf L1 S).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (le_sup_left : S ≤ S ⊔ borelOf L1 S)).mp h1n))
  have hDL : D ≤ L1 := hDborel'.trans (F1.borelOf_le L1 S)
  have hSdec : S = (S ⊓ L1) ⊔ (S ⊓ Subgroup.centralizer (D : Set G)) :=
    eq_sup_inf_centralizer_of_odd hF.1.h1.pgroup hF.1.h1.normalizes hDn hDL hDodd
  have hDsupS : (S ⊓ L1) ⊔ D = borelOf L1 S := by
    rw [← borelOf_str86S'_left L1 L2 S, ← hDsup, str86S', sup_inf_inf_left]
  exact eq_sup_str86S'_pCoreOf_of_cartan hSdec
    (le_pCoreOf_of_vertex_cartan hF hAut hNF hDborel' hDodd hDsupS)
    (F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW))

theorem bigB_le_normalizer_of_eq_sup_pCoreOf
    {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S)
    (hS : S = str86S' L1 L2 S ⊔ Q1 L1 L2 S) :
    bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) := by
  have hF' : F112Hyp L1 L2 (str86S' L1 L2 S) := f112Hyp_sup_inf hF
  have hSB' : bigB L1 L2 (str86S' L1 L2 S) ≤
      Subgroup.normalizer (str86S' L1 L2 S : Set G) :=
    bigB_le_normalizer_of_sup_inf_eq hF'.1 (sup_inf_str86S' L1 L2 S)
  have hB1S' : borelOf L1 S ≤ Subgroup.normalizer (str86S' L1 L2 S : Set G) := by
    rw [← borelOf_str86S'_left L1 L2 S]
    exact (le_sup_left.trans le_sup_left : borelOf L1 (str86S' L1 L2 S) ≤
      bigB L1 L2 (str86S' L1 L2 S)).trans hSB'
  have hB2S' : borelOf L2 S ≤ Subgroup.normalizer (str86S' L1 L2 S : Set G) := by
    rw [← borelOf_str86S'_right L1 L2 S]
    exact (le_sup_right.trans le_sup_left : borelOf L2 (str86S' L1 L2 S) ≤
      bigB L1 L2 (str86S' L1 L2 S)).trans hSB'
  have hB1Q : borelOf L1 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    ((le_sup_left.trans le_sup_left).trans le_sup_right).trans
      (le_normalizer_pCoreOf_P1 L1 L2 S)
  have hB2Q : borelOf L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    ((le_sup_right.trans le_sup_left).trans le_sup_right).trans
      (le_normalizer_pCoreOf_P1 L1 L2 S)
  have hSS' : S ≤ Subgroup.normalizer (str86S' L1 L2 S : Set G) := by
    rw [str86S']
    exact F1.le_normalizer_sup (F1.le_normalizer_inf_of_le hF.1.h1.normalizes)
      (F1.le_normalizer_inf_of_le hF.1.h2.normalizes)
  have hSQ : S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    (le_sup_right.trans le_sup_right).trans (le_normalizer_pCoreOf_P1 L1 L2 S)
  have hbigS' : bigB L1 L2 S ≤ Subgroup.normalizer (str86S' L1 L2 S : Set G) :=
    sup_le (sup_le hB1S' hB2S') hSS'
  have hbigQ : bigB L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    sup_le (sup_le hB1Q hB2Q) hSQ
  have hbig : bigB L1 L2 S ≤
      Subgroup.normalizer ((str86S' L1 L2 S ⊔ Q1 L1 L2 S : Subgroup G) : Set G) :=
    F1.le_normalizer_sup (X := bigB L1 L2 S) (H := str86S' L1 L2 S)
      (K := Q1 L1 L2 S) hbigS' hbigQ
  rw [← hS] at hbig
  exact hbig

theorem Q1_comm (L1 L2 S : Subgroup G) : Q1 L2 L1 S = Q2 L1 L2 S := by
  rw [Q1, Q2, P1, P2, bigB_comm]

theorem Z1_comm (L1 L2 S : Subgroup G) : Z1 L2 L1 S = Z2 L1 L2 S := by
  rw [Z1, Z2, Q1_comm]

theorem str86_bigB_le_normalizer_of_nf {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (h1 : VU3Big L1)
    (h2 : ∃ n : ℕ, 2 ≤ n ∧ IsL2Quot n (oTwoQuot ↥L2))
    (hNF1 : Str86NF L1 (Q1 L1 L2 ((S ⊓ L1) ⊔ (S ⊓ L2)))
      (Z1 L1 L2 ((S ⊓ L1) ⊔ (S ⊓ L2))))
    (hNF2 : Str86NF L2 (Q2 L1 L2 ((S ⊓ L1) ⊔ (S ⊓ L2)))
      (Z2 L1 L2 ((S ⊓ L1) ⊔ (S ⊓ L2)))) :
    bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) := by
  classical
  rcases hF.2.2 with h1n | h2n
  · have hAut1 : Str86AutFact L1 := fun T H hH hHodd hTH σ hσ hσT hσH =>
      mulAut_eq_one_of_fixes_borel_complement (H := H) (Or.inr (Or.inl h1)) T hH hHodd hTH σ
        hσ hσT hσH
    have hNF1' : Str86NF L1 (Q1 L1 L2 (str86S' L1 L2 S)) (Z1 L1 L2 (str86S' L1 L2 S)) := by
      simpa only [str86S'] using hNF1
    exact bigB_le_normalizer_of_eq_sup_pCoreOf hF
      (eq_sup_str86S'_pCoreOf_of_vertex hF hAut1 hNF1' h1n)
  · obtain ⟨n, hn, hL2⟩ := h2
    have hFsym : F112Hyp L2 L1 S := F112Hyp.symm hF
    have hAut2 : Str86AutFact L2 := fun T H hH hHodd hTH σ hσ hσT hσH =>
      mulAut_eq_one_of_fixes_borel_complement (H := H) (Or.inr (Or.inr ⟨n, hn, hL2⟩)) T hH
        hHodd hTH σ hσ hσT hσH
    have hNF2' : Str86NF L2 (Q1 L2 L1 (str86S' L2 L1 S)) (Z1 L2 L1 (str86S' L2 L1 S)) := by
      simpa only [str86S'_comm, Q1_comm, Z1_comm] using hNF2
    have hbig2 : bigB L2 L1 S ≤ Subgroup.normalizer (S : Set G) :=
      bigB_le_normalizer_of_eq_sup_pCoreOf hFsym
        (eq_sup_str86S'_pCoreOf_of_vertex hFsym hAut2 hNF2' h2n)
    rwa [bigB_comm] at hbig2

end CFSG.Quasithin.Stroth
