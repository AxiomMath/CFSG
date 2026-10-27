module

public import CFSG.RankThree.PartOne.U5K.KernelTwo
public import CFSG.RankThree.PartOne.S12.Sec1515U5
import CFSG.RankThree.PartOne.S12.Sec12FusSyl
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public section

namespace CFSG.RankThree.PartOne.U5K

open CFSG CFSG.Assembly CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.RankThreeEven (projSU)

@[expose] def U5EInndiag : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E →
    Outcome152Five p E A (lieGenerated p E) →
    ∀ (f : ℕ), 1 ≤ f →
      ∀ (e : ↥(lieGenerated p E) ⧸ Subgroup.center ↥(lieGenerated p E) ≃* projSU 5 2 f)
        (x : G) (hx : x ∈ lieNormalizer p E), x ∈ E →
          U5Act (lieGenerated p E) e ⟨x, hx⟩ ∈ U5Inndiag f ∧
            (U5Act (lieGenerated p E) e ⟨x, hx⟩ = 1 → x = 1)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem E_le_lieNormalizer (h15 : Sec15Hyp G p A c L E) : E ≤ lieNormalizer p E := fun _ hx =>
  torusNormalizer_le_lieNormalizer h15.h12.prime E (Subgroup.le_normalizer hx)

theorem u5_kernel_facts (h15 : Sec15Hyp G p A c L E) (hF12 : Sec12Facts G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E)) (h1511 : Node1511) (hEin : U5EInndiag)
    {f : ℕ} (hf : 1 ≤ f)
    (e : ↥(lieGenerated p E) ⧸ Subgroup.center ↥(lieGenerated p E) ≃* projSU 5 2 f) :
    ¬ 2 ∣ Nat.card (U5Act (lieGenerated p E) e).ker ∧
      ¬ p ∣ Nat.card (U5Act (lieGenerated p E) e).ker := by
  have hp := h15.h12.prime
  have hodp : ¬ p ∣ Nat.card (U5Act (lieGenerated p E) e).ker :=
    ker_not_dvd_p_of_max hp e h15.h12.E_elem (E_le_lieNormalizer h15) h15.h12.A_le_E h15.h12.E_le
      h15.h12.E_max (fun x hx hxE h => (hEin G p A c L E h15 hF12 hout f hf e x hx hxE).2 h)
  refine ⟨ker_not_dvd_two_of_max hp hf e h15.h12.E_elem (E_le_lieNormalizer h15) h15.h12.A_le_E
    hodp h15.h12.setup.2.2.2.1 ?_, hodp⟩
  intro M hM
  exact h1511 G p A c L E h15 hF12 (Or.inr (Or.inr (Or.inr (Or.inr hout)))) A le_rfl
    (Or.inr ⟨hout, rfl⟩) M hM

theorem kf1515U5Faithful_of (h1511 : Node1511) (hEin : U5EInndiag) (hM : U5Model) :
    KF1515U5Faithful := by
  intro G _ _ p A c L E T B h15 hF12 hout hcfg
  obtain ⟨f, hf, hpf, ⟨e⟩, -⟩ := id hout
  have hp := h15.h12.prime
  have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three (by have := h15.h12.three_lt; omega)
    (by have := h15.h12.three_lt; omega)
  have hker := u5_kernel_facts h15 hF12 hout h1511 hEin hf e
  exact faithful_pure hM hf hp hp5 hpf e hcfg.sylow hker.1 hker.2 (E_le_lieNormalizer h15)
    (fun x hx hxE => (hEin G p A c L E h15 hF12 hout f hf e x hx hxE).1) hcfg.B_le_E hcfg.B_le_X
    hcfg.B_elem hcfg.B_card

theorem kf1515U5Syl_of (h1511 : Node1511) (hEin : U5EInndiag) (hM : U5Model) : KF1515U5Syl := by
  intro G _ _ p A c L E T B h15 hF12 hout hcfg P hP
  obtain ⟨f, hf, hpf, ⟨e⟩, -⟩ := id hout
  have hp := h15.h12.prime
  have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three (by have := h15.h12.three_lt; omega)
    (by have := h15.h12.three_lt; omega)
  have hker := u5_kernel_facts h15 hF12 hout h1511 hEin hf e
  exact syl_pure hM hf hp hp5 hpf e hcfg.sylow hker.1 hker.2 (hP.1.trans inf_le_left) hP.2.1
    (hP.1.trans inf_le_right)

theorem kf1515U5Core_of (h1510 : Node1510) (h1511 : Node1511) (hEin : U5EInndiag)
    (hM : U5Model) : KF1515U5Core := by
  intro G _ _ p A c L E T B h15 hF12 hout hcfg M hMloc
  obtain ⟨f, hf, hpf, ⟨e⟩, -⟩ := id hout
  have hp := h15.h12.prime
  have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three (by have := h15.h12.three_lt; omega)
    (by have := h15.h12.three_lt; omega)
  have hker := u5_kernel_facts h15 hF12 hout h1511 hEin hf e
  have hout' : Outcome152 p E A (lieGenerated p E) :=
    Or.inr (Or.inr (Or.inr (Or.inr hout)))
  set R : Subgroup G := inSubgroup (CFSG.pCore 2) M with hR
  have hR2 : IsPGroup 2 R := (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).map M.subtype
  have hMR : M ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.le_normalizer.trans
      (Sec15Final.normalizer_le_normalizer_map_subtype_of_characteristic inferInstance)
  have hBM : B ≤ M := fun b hb => hMloc.2 (hcfg.B_le_X hb)
  have hBnorm : B ≤ Subgroup.normalizer (R : Set G) := fun b hb => hMR (hBM hb)
  have hpow : ∀ member : B, member ^ p = 1 := fun member => by
    have := hcfg.B_elem
    have h := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := B) (member : G) member.2
    exact Subtype.ext (by simpa using h)
  have hcomp : ¬ p ∣ Nat.card R := by
    obtain ⟨n, hn⟩ := hR2.exists_card_eq
    rw [hn]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    omega
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
    p hp B R hpow hcfg.B_card hcomp hBnorm
  have hRN : R ≤ lieNormalizer p E := by
    refine hgen.le.trans (iSup_le fun member => iSup_le fun hne => ?_)
    intro x hx
    have hmemE : (member : G) ∈ E := hcfg.B_le_E member.2
    have hU1 : Subgroup.zpowers (member : G) ≠ ⊥ := fun h =>
      hne (Subtype.ext (Subgroup.zpowers_eq_bot.1 h))
    have hnorm := h1510 G p A c L E h15 hF12 hout' (Subgroup.zpowers (member : G))
      (Subgroup.zpowers_le.2 hmemE) hU1
    refine hnorm (Sec12Fus.mem_normalizer_zpowers_of_conj ?_)
    have hxc : x ∈ Subgroup.centralizer ({(member : G)} : Set G) := hx.2
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 hxc
    rw [h1, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers _
  exact core_pure hM hf hp hp5 hpf e hcfg.sylow hker.1 hR2 hRN fun x hx => hMR (hMloc.2 hx)

end CFSG.RankThree.PartOne.U5K
