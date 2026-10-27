module

public import CFSG.RankThree.GF2n.Tim81.Cited.UnitaryTIModuleTI
import CFSG.RankThree.GF2n.Tim79aSUModelGen

public section

namespace CFSG.RankThree.GF2n.Tim81.TIModule

open Matrix CFSG.RankThree.FFModules CFSG.Timmesfeld.ARS CFSG.Timmesfeld.LieEmbed
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f m : ℕ}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

private theorem single_ne_smul_single {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    ∀ c : F, (Pi.single j 1 : Fin n → F) ≠ c • Pi.single i 1 := by
  intro c h
  have := congrFun h j
  rw [Pi.single_eq_same, Pi.smul_apply, Pi.single_eq_of_ne hij.symm, smul_zero] at this
  exact one_ne_zero this

private def frameIdx (k : ℕ) (j : Fin (k + 1)) : Fin (k + k + 2) := ⟨j.val, by omega⟩

private theorem frameIdx_ne_rev {k : ℕ} (j j' : Fin (k + 1)) :
    frameIdx k j ≠ Fin.rev (frameIdx k j') := by
  intro h
  have := congrArg Fin.val h
  simp only [frameIdx, Fin.val_rev] at this
  omega

private theorem frameIdx_ne {k : ℕ} {j j' : Fin (k + 1)} (h : j ≠ j') :
    frameIdx k j ≠ frameIdx k j' := fun h' =>
  h (Fin.ext (by have := congrArg Fin.val h'; simpa [frameIdx] using this))

private theorem frameIdx_rev_ne {k : ℕ} {j j' : Fin (k + 1)} (h : j ≠ j') :
    Fin.rev (frameIdx k j) ≠ Fin.rev (frameIdx k j') := fun h' =>
  frameIdx_ne h (Fin.rev_injective h')

private theorem frame_perp {k : ℕ} {σ' : F ≃+* F} {j j' : Fin (k + 1)} (h : j ≠ j')
    {u v : Fin (k + k + 2) → F}
    (hu : u = Pi.single (frameIdx k j) 1 ∨ u = Pi.single (Fin.rev (frameIdx k j)) 1)
    (hv : v = Pi.single (frameIdx k j') 1 ∨ v = Pi.single (Fin.rev (frameIdx k j')) 1) :
    uForm σ' u v = 0 ∧ ∀ c : F, v ≠ c • u := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact ⟨by rw [uForm_single_left, Pi.single_eq_of_ne (frameIdx_ne_rev j' j).symm],
      single_ne_smul_single (frameIdx_ne h)⟩
  · exact ⟨by rw [uForm_single_left, Pi.single_eq_of_ne (frameIdx_rev_ne h)],
      single_ne_smul_single (frameIdx_ne_rev j j')⟩
  · exact ⟨by rw [uForm_single_left, Fin.rev_rev, Pi.single_eq_of_ne (frameIdx_ne h)],
      single_ne_smul_single (frameIdx_ne_rev j' j).symm⟩
  · exact ⟨by rw [uForm_single_left, Fin.rev_rev, Pi.single_eq_of_ne (frameIdx_ne_rev j j')],
      single_ne_smul_single (frameIdx_rev_ne h)⟩

section

variable (hF : Nat.card F = (2 ^ f) ^ 2)
  (σ : Representation (ZMod 2) (SU (unitaryInvolution F 2 f) (m + 2)) W)

include hF in
theorem natCard_commSpan_top_le (hm : 2 ≤ m) :
    Nat.card (commSpan σ ⊤) ≤
      Nat.card (transvComm σ (Pi.single 0 1)) ^ (2 * (m + 2) - 3) := by
  classical
  have hσF := unitaryInvolution_involutive hF
  have h0r : (0 : Fin (m + 2)) ≠ Fin.rev 0 := by
    rw [Fin.rev_zero]
    intro h
    have := congrArg Fin.val h
    simp at this
  have he₀ : uForm (unitaryInvolution F 2 f) (Pi.single (0 : Fin (m + 2)) 1 : Fin (m + 2) → F)
      (Pi.single 0 1) = 0 := uForm_single_self h0r
  obtain ⟨U, hUlen, hUiso, hUgen⟩ := Tim79a.suFrameGenAll_holds F f hF (m + 2) (by omega)
  have hL : (⨆ u ∈ (U.toFinset : Set (Fin (m + 2) → F)),
      transvGroup (unitaryInvolution F 2 f) (m + 2) u) = ⊤ := by
    refine hUgen _ fun u hu => ?_
    rw [uTransLe_iff (isUTransGroup_transvGroup hσF (hUiso u hu).2)]
    exact le_iSup₂_of_le (f := fun u (_ : u ∈ (U.toFinset : Set (Fin (m + 2) → F))) =>
      transvGroup (unitaryInvolution F 2 f) (m + 2) u) u (by simpa using hu) le_rfl
  have hle := commSpan_le_biSup_of_le (σ := σ) (U.toFinset : Set (Fin (m + 2) → F))
    (fun u => transvGroup (unitaryInvolution F 2 f) (m + 2) u) (H := ⊤) hL.ge
  have hcard : ∀ u ∈ U.toFinset, Nat.card (transvComm σ u) =
      Nat.card (transvComm σ (Pi.single 0 1)) := fun u hu =>
    natCard_transvComm hF σ (by omega) (hUiso u (List.mem_toFinset.1 hu)).1
      (hUiso u (List.mem_toFinset.1 hu)).2 (single_one_ne_zero 0) he₀
  calc Nat.card (commSpan σ ⊤)
      ≤ Nat.card ↥(⨆ u ∈ U.toFinset, transvComm σ u) := by
        refine natCard_mono (hle.trans ?_)
        simp only [Finset.mem_coe]
        exact le_rfl
    _ ≤ ∏ u ∈ U.toFinset, Nat.card (transvComm σ u) := natCard_biSup_le _ _
    _ = Nat.card (transvComm σ (Pi.single 0 1)) ^ U.toFinset.card := by
        rw [Finset.prod_congr rfl hcard, Finset.prod_const]
    _ ≤ Nat.card (transvComm σ (Pi.single 0 1)) ^ (2 * (m + 2) - 3) :=
        Nat.pow_le_pow_right Nat.card_pos ((List.toFinset_card_le U).trans hUlen)

include hF in
theorem sq_le_natCard_transvComm (hf : 2 ≤ f) (hm : 2 ≤ m) (hσ : ∃ x w, σ x w ≠ w)
    (hW : Nat.card W ≤ (2 ^ f) ^ (2 * (m + 2)))
    (hpow : ∃ k : ℕ, Nat.card (transvComm σ (Pi.single 0 1)) = (2 ^ f) ^ k) :
    (2 ^ f) ^ 2 ≤ Nat.card (transvComm σ (Pi.single 0 1)) := by
  obtain ⟨k, hk⟩ := hpow
  have h1 := natCard_commSpan_top_le hF σ hm
  have h2 : (2 ^ f) ^ (2 * (m + 2 - 1)) ≤ Nat.card (commSpan σ ⊤) :=
    (fix_or_sub_mem_SU hF hf (by omega) σ hW).2 hσ
      (fun x u hu => apply_mem_commSpan (fun _ _ => Subgroup.mem_top _) hu)
      (fun x w => sub_mem_commSpan (Subgroup.mem_top x) w)
  rw [hk, ← pow_mul] at h1
  have hq : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
  have h4 := (Nat.pow_le_pow_iff_right hq).1 (h2.trans h1)
  have hk2 : 2 ≤ k := by
    by_contra h
    push Not at h
    interval_cases k <;> omega
  rw [hk]
  exact Nat.pow_le_pow_right (by positivity) hk2

variable {σ}

include hF in
theorem fixSub_top_eq_bot_and_commSpan_top_eq_top (hf : 2 ≤ f) (hm : 2 ≤ m) (heven : Even m)
    (hσ : ∃ x w, σ x w ≠ w) (hTI : IsTIRep σ) (hW : Nat.card W = (2 ^ f) ^ (2 * (m + 2)))
    (hpow : ∃ k : ℕ, Nat.card (transvComm σ (Pi.single 0 1)) = (2 ^ f) ^ k) :
    fixSub σ ⊤ = ⊥ ∧ commSpan σ ⊤ = ⊤ := by
  classical
  obtain ⟨k, rfl⟩ := heven
  have hs₀ := sq_le_natCard_transvComm hF σ hf hm hσ hW.le hpow
  set s₀ := Nat.card (transvComm σ (Pi.single 0 1)) with hs₀def
  have h0r : (0 : Fin (k + k + 2)) ≠ Fin.rev 0 := by
    rw [Fin.rev_zero]
    intro h
    have := congrArg Fin.val h
    simp at this
  have he₀ : uForm (unitaryInvolution F 2 f) (Pi.single (0 : Fin (k + k + 2)) 1 :
      Fin (k + k + 2) → F) (Pi.single 0 1) = 0 := uForm_single_self h0r
  have hpair : ∀ j : Fin (k + 1), ∀ u : Fin (k + k + 2) → F,
      (u = Pi.single (frameIdx k j) 1 ∨ u = Pi.single (Fin.rev (frameIdx k j)) 1) →
        u ≠ 0 ∧ uForm (unitaryInvolution F 2 f) u u = 0 := by
    rintro j u (rfl | rfl)
    · exact ⟨single_one_ne_zero _, uForm_single_self (frameIdx_ne_rev j j)⟩
    · exact ⟨single_one_ne_zero _,
        uForm_single_self (by rw [Fin.rev_rev]; exact (frameIdx_ne_rev j j).symm)⟩
  have had : ∀ j : Fin (k + 1), uForm (unitaryInvolution F 2 f)
      (Pi.single (frameIdx k j) 1) (Pi.single (Fin.rev (frameIdx k j)) 1) = 1 := fun j => by
    rw [uForm_single_left, Pi.single_eq_same]
  let X : Fin (k + 1) → Submodule (ZMod 2) W := fun j =>
    commSpan σ (transvGroup (unitaryInvolution F 2 f) (k + k + 2) (Pi.single (frameIdx k j) 1) ⊔
      transvGroup (unitaryInvolution F 2 f) (k + k + 2) (Pi.single (Fin.rev (frameIdx k j)) 1))
  let Fx : Fin (k + 1) → Submodule (ZMod 2) W := fun j =>
    fixSub σ (transvGroup (unitaryInvolution F 2 f) (k + k + 2) (Pi.single (frameIdx k j) 1) ⊔
      transvGroup (unitaryInvolution F 2 f) (k + k + 2) (Pi.single (Fin.rev (frameIdx k j)) 1))
  have hXF : ∀ j ∈ (Finset.univ : Finset (Fin (k + 1))), X j ⊓ Fx j = ⊥ := fun j _ =>
    commSpan_sup_inf_fixSub_eq_bot hF hf hm hσ hTI (hpair j _ (Or.inl rfl)).2
      (hpair j _ (Or.inr rfl)).2 (had j)
  have hkey : ∀ j j' : Fin (k + 1), j ≠ j' → ∀ u v : Fin (k + k + 2) → F,
      (u = Pi.single (frameIdx k j) 1 ∨ u = Pi.single (Fin.rev (frameIdx k j)) 1) →
      (v = Pi.single (frameIdx k j') 1 ∨ v = Pi.single (Fin.rev (frameIdx k j')) 1) →
        transvComm σ u ≤ fixSub σ (transvGroup (unitaryInvolution F 2 f) (k + k + 2) v) := by
    intro j j' hjj' u v hu hv
    exact transvComm_le_fixSub hF hf hm hσ hTI (hpair j u hu).1 (hpair j u hu).2
      (hpair j' v hv).1 (hpair j' v hv).2 (frame_perp hjj' hu hv).1
      (frame_perp (σ' := unitaryInvolution F 2 f) hjj' hu hv).2
  have hle : ∀ j ∈ (Finset.univ : Finset (Fin (k + 1))), ∀ j' ∈ Finset.univ, j ≠ j' →
      X j ≤ Fx j' := by
    intro j _ j' _ hjj'
    change commSpan σ _ ≤ fixSub σ _
    rw [commSpan_sup, fixSub_sup]
    exact sup_le
      (le_inf (hkey j j' hjj' _ _ (Or.inl rfl) (Or.inl rfl))
        (hkey j j' hjj' _ _ (Or.inl rfl) (Or.inr rfl)))
      (le_inf (hkey j j' hjj' _ _ (Or.inr rfl) (Or.inl rfl))
        (hkey j j' hjj' _ _ (Or.inr rfl) (Or.inr rfl)))
  obtain ⟨hcardX, hinfX⟩ := natCard_biSup_eq_prod Finset.univ X Fx hXF hle
  have hXj : ∀ j, Nat.card (X j) = s₀ * s₀ := by
    intro j
    have hnp : ∀ c : F, (Pi.single (Fin.rev (frameIdx k j)) 1 : Fin (k + k + 2) → F) ≠
        c • Pi.single (frameIdx k j) 1 := single_ne_smul_single (frameIdx_ne_rev j j)
    change Nat.card ↥(commSpan σ _) = _
    rw [commSpan_sup, natCard_sup_of_inf_eq_bot (transvComm_inf_eq_bot hF hf hm hσ hTI
        (hpair j _ (Or.inl rfl)).1 (hpair j _ (Or.inl rfl)).2 (hpair j _ (Or.inr rfl)).1
        (hpair j _ (Or.inr rfl)).2 hnp),
      natCard_transvComm hF σ (by omega) (hpair j _ (Or.inl rfl)).1 (hpair j _ (Or.inl rfl)).2
        (single_one_ne_zero 0) he₀,
      natCard_transvComm hF σ (by omega) (hpair j _ (Or.inr rfl)).1 (hpair j _ (Or.inr rfl)).2
        (single_one_ne_zero 0) he₀]
  have hbig : Nat.card W ≤ Nat.card ↥(⨆ j ∈ (Finset.univ : Finset (Fin (k + 1))), X j) := by
    rw [hcardX, Finset.prod_congr rfl fun j _ => hXj j, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, hW]
    calc (2 ^ f) ^ (2 * (k + k + 2)) = ((2 ^ f) ^ 2 * (2 ^ f) ^ 2) ^ (k + 1) := by ring
      _ ≤ (s₀ * s₀) ^ (k + 1) := Nat.pow_le_pow_left (Nat.mul_le_mul hs₀ hs₀) _
  have htop : (⨆ j ∈ (Finset.univ : Finset (Fin (k + 1))), X j) = ⊤ := by
    refine eq_of_le_of_natCard_le le_top ?_
    rwa [Nat.card_congr (Submodule.topEquiv (R := ZMod 2) (M := W)).toEquiv]
  refine ⟨?_, ?_⟩
  · rw [htop, top_inf_eq] at hinfX
    rw [eq_bot_iff, ← hinfX]
    exact le_iInf₂ fun j _ => fixSub_antitone le_top
  · rw [eq_top_iff, ← htop]
    exact iSup₂_le fun j _ => commSpan_mono le_top

include hF in
theorem eq_bot_or_eq_top_SU_of_even (hf : 2 ≤ f) (hm : 2 ≤ m) (heven : Even m)
    (hσ : ∃ x w, σ x w ≠ w) (hTI : IsTIRep σ) (hW : Nat.card W = (2 ^ f) ^ (2 * (m + 2)))
    (hpow : ∃ k : ℕ, Nat.card (transvComm σ (Pi.single 0 1)) = (2 ^ f) ^ k)
    {U : Submodule (ZMod 2) W} (hU : ∀ x, ∀ u ∈ U, σ x u ∈ U) : U = ⊥ ∨ U = ⊤ := by
  obtain ⟨hfix, hcomm⟩ :=
    fixSub_top_eq_bot_and_commSpan_top_eq_top hF hf hm heven hσ hTI hW hpow
  rcases (fix_or_sub_mem_SU hF hf (by omega) σ hW.le).1 hU with h | h
  · left
    rw [eq_bot_iff]
    intro u hu
    have hmem : u ∈ fixSub σ ⊤ := fun x _ => h x u hu
    rwa [hfix] at hmem
  · right
    rw [eq_top_iff, ← hcomm]
    exact commSpan_le_iff.2 fun x _ w => h x w

end

end CFSG.RankThree.GF2n.Tim81.TIModule
