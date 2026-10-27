module

public import CFSG.Quasithin.MS93.M15L3
public import CFSG.Quasithin.MS93.M15G2
public import CFSG.Quasithin.MS93.M15Sp4
public import CFSG.Quasithin.MS93.FFMain
public import CFSG.Quasithin.H13.VolIAltCoverSix

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section Aux

variable {V : Type} [CommGroup V] [Finite V] {X K : Subgroup (MulAut V)}

omit [Finite V] in
theorem xmodFixed_top_eq (K : Subgroup (MulAut V)) : XMod.fixed ↥K (⊤ : Subgroup V) = fixV K := by
  ext v
  simp only [XMod.mem_fixed, Subgroup.mem_top, true_and, mem_fixV]
  exact ⟨fun hv x hx => hv ⟨x, hx⟩, fun hv a => hv a a.2⟩

theorem MS15Hyp.irrPlus (h : MS15Hyp X K) : commV K ∈ IrrPlus K ⊤ := by
  refine ⟨le_top, ?_⟩
  rw [h.comm]
  exact ⟨XMod.isInv_top, (xmodCommOf_top_eq K).trans h.comm,
    (xmodFixed_top_eq K).symm ▸ h.irr⟩

theorem ne_bot_of_realizesVia_nat {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {I : Subgroup W} {F : Type} [Field F] {π : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) →* ↥L}
    (hR : (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 F)).RealizesVia L I ⊥ π) : I ≠ ⊥ := by
  intro hI
  subst hI
  obtain ⟨-, -, -, -, -, -, -, β, hβs, -, -⟩ := hR
  set e : Multiplicative (Fin 3 → F) := Multiplicative.ofAdd (Pi.single 0 1)
  obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨e, Subgroup.mem_top _⟩)
  have hu1 : u = 1 := Subtype.ext (Subgroup.mem_bot.1 u.2)
  rw [hu1, map_one] at hu
  have h1 := (QuotientGroup.eq_one_iff _).1 hu.symm
  have h2 : e = 1 := Subgroup.mem_bot.1 (Subgroup.mem_subgroupOf.1 h1)
  have h3 := congrArg (fun x : Multiplicative (Fin 3 → F) => Multiplicative.toAdd x 0) h2
  simp [e] at h3

theorem false_of_directSum_two {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {F : Type}
    [Field F] (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup W) ⊤)
    (hD : DirectSumOfCopies L ⊤ ⊥ (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 F)) 2) : False := by
  obtain ⟨I, π, -, hind, -, hreal⟩ := hD
  have h0 := ne_bot_of_realizesVia_nat (hreal 0)
  have h1 := ne_bot_of_realizesVia_nat (hreal 1)
  have hinv : XMod.IsInv ↥L (I 0) := fun a l hl => (hreal 0).2.2.2.1 a l hl
  rcases hirr.2 (I 0) hinv bot_le le_top with hb | ht
  · exact h0 hb
  · apply h1
    have hle : I 1 ≤ ⊥ ⊔ ⨆ (j : Fin 2) (_ : j ≠ 0), I j :=
      le_sup_of_le_right (le_iSup₂_of_le (f := fun (j : Fin 2) (_ : j ≠ 0) => I j) 1
        (by decide) le_rfl)
    have := hind 0
    rw [ht, top_inf_eq] at this
    exact le_bot_iff.1 (this ▸ hle)

end Aux

section Main

variable {V : Type} [CommGroup V] [Finite V] {X K : Subgroup (MulAut V)}

theorem ms15AS_of
    (h14 : MS14AS) : MS15AS := by
  intro V _ _ hV X K h
  obtain ⟨-, -, hcases, -⟩ :=
    h14 (Sec (⊤ : Subgroup V) (fixV K)) (MS15Hyp.sec_sq hV) _ _ (h.ffHyp hV)
  have hI := h.irrPlus
  rcases hcases with ⟨n, F, iF, fF, hn, hF, -, -, hnat | hdir⟩ | ⟨hhat, -⟩ | hsp | hg2
  ·
    have hK : BinaryNaturalSL K ⊤ (fixV K) 3 n :=
      h.binaryNaturalSL_of_quot hV h.le
        (⟨F, iF, fF, hF, hnat⟩ : BinaryNaturalSL (autSec K ⊤ (fixV K)) ⊤ ⊥ 3 n)
    rcases (show n = 1 ∨ 1 < n by omega) with rfl | hn1
    · exact Or.inl (caseL3 hV h hK)
    · exfalso
      have hK' : BinaryNaturalSL K (commV K) (fixV K ⊓ commV K) 3 n := by
        rw [h.comm, inf_top_eq]
        exact hK
      have := H13.VolI.binaryNaturalSL_three_eq_bot hV hI hn1 hK'
      rw [h.comm, inf_top_eq] at this
      exact h.fix_ne this
  ·
    exact (false_of_directSum_two h.isIrrSec_quot hdir).elim
  ·
    exfalso
    have hK : TripleA6Six K (commV K) (fixV K ⊓ commV K) := by
      rw [h.comm, inf_top_eq]
      exact h.tripleA6Six_of_quot hV h.le hhat
    have := H13.VolI.tripleA6Six_eq_bot hV hI hK
    rw [h.comm, inf_top_eq] at this
    exact h.fix_ne this
  ·
    rcases hsp with ⟨n, hn, hS⟩ | hA
    · have hK := h.binaryNaturalSp4_of_quot hV h.le hS
      obtain ⟨hb, F, iF, fF, hF, Z, hZ, hR⟩ := sp4_case_large hV h hn hK
      exact Or.inr (Or.inl (Or.inl ⟨n, hn, hK, hb, F, iF, fF, hF, Z, hZ, hR⟩))
    · have hK := h.alternatingNatural_of_quot hV h.le hA
      rcases H13.VolI.altNaturalCoverSix_holds V hV K (fixV K) le_rfl h.comm hK with h0 | h2
      · exact (h.fix_ne h0).elim
      · exact Or.inr (Or.inl (Or.inr ⟨hK, h2⟩))
  ·
    rcases hg2 with ⟨n, hn, hG⟩ | ⟨hGd, hXK, hGX⟩
    · have hK := h.g2Natural_of_quot hV h.le hG
      obtain ⟨hb, F, iF, fF, hF, Z, hZ, hR⟩ := g2_case_large hV h hn hK
      exact Or.inr (Or.inr (Or.inl ⟨n, hn, hK, hb, F, iF, fF, hF, Z, hZ, hR⟩))
    · have hK := h.g2NaturalDerived_of_quot hV h.le hGd
      have hX := h.g2Natural_of_quot hV le_rfl hGX
      exact Or.inr (Or.inr (Or.inr ⟨hK, MS15Hyp.ne_of_quot_ne hXK, hX, g2_case_two hV h hK⟩))

end Main

theorem ms15AS_holds :
    MS15AS :=
  ms15AS_of ms14AS_holds

end CFSG.Quasithin.MS93
