module

public import CFSG.LocalAnalysis.StandardType.GGFrameTBBody
public import CFSG.LocalAnalysis.StandardType.GGTwAutBasic
import CFSG.LocalAnalysis.StandardType.GGFrameClassicalNum
import CFSG.LocalAnalysis.StandardType.GGFrameClassicalAut
import CFSG.LocalAnalysis.StandardType.GGStdPosC24Signed
import CFSG.LocalAnalysis.StandardType.GGRootGenAvoidReflModel
import CFSG.LocalAnalysis.StandardType.GGTableB
import CFSG.LocalAnalysis.StandardType.GGTwAutHolds
import CFSG.LocalAnalysis.StandardType.GGTwOmPlusHolds
import CFSG.LocalAnalysis.StandardType.GGKGForkLinNsB
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviTransfer
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwo

public section

namespace CFSG.StandardType.FrameRoute

open CFSG CFSG.Assembly SpCoord Multiplicative

@[expose] def FrameTBRow (N : ℕ) (d : Option ℕ) (R : Type) [Group R] (I : Set (MulAut R)) :
    Prop :=
  ∀ r : ℕ, GGTorusReflGenW 3 r R I ∧
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
      GGTorusTBGroup 3 r R I L' ψ A →
        (FrameNumIs (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) N d ∧
          FrameConn (ggAutomizer (MulAut.conj : L' →* MulAut L').range A)) ∧
        ∃ S : Subgroup L', IsPGroup 3 S ∧ ¬ IsCyclic S

theorem frameTBBody_of_row {lab : LargeEvenLabel} {N : ℕ} {d : Option ℕ}
    (hnum : frameLabNum lab = (N, d))
    (h : LargeEvenLabelAll lab fun R _ I _ => FrameTBRow N d R I) :
    LargeEvenLabelAll lab (frameTBBody lab) :=
  h.mono fun R _ I _ hR r _ _ => by
    rw [hnum]
    exact hR r

theorem exists_noncyclic_three_of_forall_conj {L' : Type} [Group L'] [Finite L']
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian 3 A) (h9 : 3 ^ 2 ≤ Nat.card A)
    (hinn : ∀ a ∈ A, ∃ l : L', a = MulAut.conj l) :
    ∃ S : Subgroup L', IsPGroup 3 S ∧ ¬ IsCyclic S := by
  set C : Subgroup L' := A.comap (MulAut.conj : L' →* MulAut L')
  let ρ : ↥C →* ↥A :=
    ((MulAut.conj : L' →* MulAut L').comp C.subtype).codRestrict A fun x => x.2
  have hρ : Function.Surjective ρ := by
    rintro ⟨a, ha⟩
    obtain ⟨l, rfl⟩ := hinn a ha
    exact ⟨⟨l, ha⟩, rfl⟩
  have hpA : IsPGroup 3 ↥A := fun x => ⟨1, Subtype.ext (by simpa using hA.2 x.1 x.2)⟩
  obtain ⟨U, -, hU, hUmap⟩ :=
    AGLEmbedding.exists_isPGroup_three_map_eq hρ (hpA.to_subgroup ⊤)
  refine ⟨U.map C.subtype, hU.map C.subtype, fun hcyc => ?_⟩
  have e := U.equivMapOfInjective C.subtype C.subtype_injective
  haveI : IsCyclic ↥U := isCyclic_of_injective e.toMonoidHom e.injective
  have hsurj : Function.Surjective (ρ.comp U.subtype) := by
    intro a
    have ha : a ∈ U.map ρ := by
      rw [hUmap]
      exact Subgroup.mem_top a
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp ha
    exact ⟨⟨u, hu⟩, rfl⟩
  haveI : IsCyclic ↥A := isCyclic_of_surjective _ hsurj
  haveI : Finite ↥A := Finite.of_surjective ρ hρ
  exact TableB.not_isCyclic_of_card (by norm_num) hA.2 h9 ‹_›

theorem frameTB_of_twPieces {ℓ : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hZ : Subgroup.center R = ⊥) (hI : GGOutdiagPrime 3 R I) (hcp : GGCenterPrime 3 R)
    (hS : GGTorusSignedEltSC 3 R) (hU : GGElemAbelianRankLE R 3 ℓ)
    (hL : GGSelfCentRankGE 3 ℓ R) : FrameTBRow (ℓ ^ 2) none R I := by
  intro r
  refine ⟨ggTorusReflGenW_of_signedEltSC Nat.prime_three (by decide) hZ hI hcp hS,
    fun L' _ _ ψ A hA => ?_⟩
  obtain ⟨hψ, hker, hperf, hAe, hAI, -, h3, hsc⟩ := hA
  have hup : Nat.card A ≤ 3 ^ ℓ :=
    ggTorusRankLE_of_elemAbelian hZ hI hU L' ψ hψ hker hperf A hAe hAI
  have hlow : 3 ^ ℓ ≤ Nat.card A :=
    ggTorusSCRank_of_selfCentRankGE Nat.prime_three hZ hI hcp hL L' ψ hψ hker hperf A hAe hAI hsc
  have hAI' : ∀ a ∈ A, ∃ φ ∈ {φ ∈ I | φ ^ 3 = 1}, ∀ l : L', φ (ψ l) = ψ (a l) := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    exact ⟨φ, ⟨hφI, ggTw_pow_eq_one_of_lift hψ hφ (hAe.2 a ha)⟩, hφ⟩
  obtain ⟨k, Θ, hk, -, hsgn, hperm, hsp⟩ := exists_signedModelSC (I := {φ ∈ I | φ ^ 3 = 1})
    Nat.prime_three (by decide) (fun φ hφ => hI φ hφ.1 hφ.2) hZ hcp hS hψ hker hperf hAe hAI'
    h3 hsc
  have hkℓ : k = ℓ := KGA.kga_k_eq Nat.prime_three Θ hlow hup
  subst hkℓ
  exact ⟨frameNumIs_frameConn_of_signedPerm hk Θ
      (mem_ggAutomizer_iff_isSignedPerm Θ hsgn hperm hsp),
    exists_noncyclic_three_of_forall_conj hAe (le_trans (by norm_num) h3)
      (exists_mulAut_conj_of_mem hψ hker hperf hI hAe hAI)⟩


theorem frameTBBody_omPlusHalf {r : ℕ} (hr : 3 ≤ r) (hev : Even r) :
    LargeEvenLabelAll ⟨.D, r + 1, 1⟩ (frameTBBody ⟨.D, r + 1, 1⟩) := by
  have h1 : ¬ (r + 1) % 2 = 0 := by
    obtain ⟨k, hk⟩ := hev
    omega
  refine frameTBBody_of_row (N := r ^ 2) (d := none)
    (by simp only [frameLabNum, frameTagNum, h1, ↓reduceIte, Nat.add_sub_cancel]) ?_
  exact ggTwOmPlus_label_of_rec (f := 1) (P := FrameTBRow (r ^ 2) none) hr fun K _ _ _ hK =>
    frameTB_of_twPieces (ggTwOmPlus_facts_rec (m := r + 1) hr rfl).1
      (ggTwOmPlus_facts_rec (m := r + 1) hr rfl).2.1
      (ggTwOmPlus_facts_rec (m := r + 1) hr rfl).2.2
      (ggTwOmPlus_signed_rec hK hr hev rfl (by norm_num))
      (ggTwOmPlus_rankLE_rec hK hr hev rfl (by norm_num))
      (ggTwOmPlus_scRank_rec hK hr hev rfl (by norm_num))

theorem frameTBBody_omMinusHalf {r : ℕ} (hr : 3 ≤ r) (hodd : Odd r) :
    LargeEvenLabelAll ⟨.twD, r + 1, 1⟩ (frameTBBody ⟨.twD, r + 1, 1⟩) := by
  have h1 : ¬ (r + 1) % 2 = 1 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have h3 : 3 ∣ 2 ^ 1 - 1 ∨ (Odd r ∧ 3 ∣ 2 ^ 1 + 1) := Or.inr ⟨hodd, by norm_num⟩
  refine frameTBBody_of_row (N := r ^ 2) (d := none)
    (by simp only [frameLabNum, frameTagNum, h1, ↓reduceIte, Nat.add_sub_cancel]) ?_
  exact ggTwOm_label_of_rec (f := 1) (P := FrameTBRow (r ^ 2) none) hr fun K _ _ _ hK b c hbc =>
    frameTB_of_twPieces (ggTwOm_facts_rec (m := r + 1 - 1) hK hbc hr rfl h3).1
      (ggTwOm_facts_rec (m := r + 1 - 1) hK hbc hr rfl h3).2.1
      (ggTwOm_facts_rec (m := r + 1 - 1) hK hbc hr rfl h3).2.2
      (ggOrthSignedTorusInput_holds.2 K (r + 1 - 1) 3 b c (by omega) hbc Nat.prime_three
        (by rw [hK]; simpa using h3))
      (ggTwOm_rankLE_rec hK hbc hr rfl h3)
      (ggTwOm_scRank_rec hK hbc hr rfl h3)

theorem frameTBBody_slHalf {r ε : ℕ} (hr : 3 ≤ r) (hε : ε ≤ 1) :
    LargeEvenLabelAll ⟨.A, 2 * r - 1 + ε, 1⟩ (frameTBBody ⟨.A, 2 * r - 1 + ε, 1⟩) := by
  have hdiv : (2 * r - 1 + ε + 1) / 2 = r := by omega
  refine frameTBBody_of_row (N := r ^ 2) (d := none)
    (by simp only [frameLabNum, frameTagNum, hdiv]) ?_
  exact ggTwSL_label_of_rec (f := 1) (ε := ε) (P := FrameTBRow (r ^ 2) none) (by omega) hε
    fun K _ _ _ hK =>
    frameTB_of_twPieces
      (ggTwSL_facts_rec (d := 2 * r - 1 + ε + 1) hr (by omega) (by rw [hK]; norm_num)).1
      (ggTwSL_facts_rec (d := 2 * r - 1 + ε + 1) hr (by omega) (by rw [hK]; norm_num)).2.1
      (ggTwSL_facts_rec (d := 2 * r - 1 + ε + 1) hr (by omega) (by rw [hK]; norm_num)).2.2
      (ggKGLn_signedEltSC_linearNonsplit Nat.prime_three (by norm_num) ggTw_cast_three_ne_zero
        (by rw [hK]; norm_num) (by omega))
      (ggTwSL_rankLE_rec (d := 2 * r - 1 + ε + 1) hr (by omega) (by rw [hK]; norm_num))
      (ggTwSL_scRank_rec (d := 2 * r - 1 + ε + 1) hr (by omega) (by rw [hK]; norm_num))

end CFSG.StandardType.FrameRoute

end
