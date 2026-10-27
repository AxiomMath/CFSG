module

public import Certificates.Kernel.Co1Sub.BindChecks
public import Certificates.Kernel.Co1Sub.Checks
public import CFSG.Certificates.Kernel.Co1Sub.SlpMem
public import CFSG.Certificates.Kernel.Co1Sub.TxtSound
public import CFSG.Certificates.Kernel.SporCov.F2Kit
public import CFSG.Sporadic.Fi23.SlpSpec

public section

namespace CFSG.KD.Co1Sub

open CFSG.KC.Co1Sub CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KC.G13 CFSG.KLie.CT CFSG.KC.TabMatGrp
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.Fi23 CFSG.Sporadic.Th CFSG.Sporadic.Co1Sub.Native
open CFSG.Sporadic.Co1.Native (co1Data)
open CFSG.Sporadic.SmallF2.Native (VecData)

private theorem andB_eq (a b : Bool) : andB a b = (a && b) := by
  cases a <;> rfl

noncomputable abbrev φJ : J (co1Data ()) →* GL (Fin 24) (ZMod 2) := (J (co1Data ())).subtype

noncomputable abbrev auxG (i : ℕ) : J (co1Data ()) := slpG (genG (co1Data ())) (aux ()) i

theorem txt_parts : AuxT.chars = wordsC aW ∧ nonemptyK aW = true ∧ aM.length = 301 := by
  have h := ch120801_txt
  rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, lenL_eq_length] at h
  exact ⟨charsEq_sound h.1, h.2.1, h.2.2⟩

theorem aW_length : aW.length = 301 := by
  rw [← (slpK_spec ch120801_aux).1, txt_parts.2.2]

theorem aux_eq : aux () = (aW.map (·.map decZ)).toArray := by
  have hW : aW ≠ [] := fun h => by simpa [h] using aW_length
  unfold aux parseWords
  rw [AuxT.eq, txt_parts.1, splitOn_wordsC hW txt_parts.2.1]

theorem aux_get {t : ℕ} (ht : t < aW.length) : (aux ())[t]! = (aW.getD t []).map decZ := by
  rw [aux_eq, getElem!_pos _ t (by simpa using ht)]
  simp [List.getD_eq_getElem _ _ ht, List.getElem?_eq_getElem ht]

theorem det_ne_of_mul {X Y : Matrix (Fin 24) (Fin 24) (ZMod 2)} (h : X * Y = 1) : X.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem seed_parts : G.length = 2 ∧ MatP 24 (G.getD 0 0) = mA (co1Data ()) ∧
    MatP 24 (G.getD 1 0) = mB (co1Data ()) := by
  have h := ch120801_seed
  rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, lenL_eq_length,
    getL_zero_eq, getL_zero_eq] at h
  exact ⟨h.1, CFSG.KD.SporCov.MatP_seedA (D := co1Data ()) SeedA.eq h.2.1,
    CFSG.KD.SporCov.MatP_seedB (D := co1Data ()) SeedB.eq h.2.2⟩

theorem gen_parts : Gi.length = 2 ∧ MatP 24 (G.getD 0 0) * MatP 24 (Gi.getD 0 0) = 1 ∧
    MatP 24 (G.getD 1 0) * MatP 24 (Gi.getD 1 0) = 1 := by
  obtain ⟨hl, hs⟩ := invsK_spec ch120801_gen
  have e : ∀ i < 2, MatP 24 (G.getD i 0) * MatP 24 (Gi.getD i 0) = 1 := fun i hi => by
    rw [← MatP_mul, ← mulS_eq, hs i (by rw [seed_parts.1]; exact hi), MatP_oneS]
  exact ⟨by rw [hl, seed_parts.1], e 0 (by omega), e 1 (by omega)⟩

theorem val_a (D : VecData) (h : (mA D).det ≠ 0) : matOf (J D).subtype (a D) = mA D := by
  rw [matOf, Subgroup.subtype_apply, a, Subtype.coe_mk, gA, dif_pos h,
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero]

theorem val_b (D : VecData) (h : (mB D).det ≠ 0) : matOf (J D).subtype (b D) = mB D := by
  rw [matOf, Subgroup.subtype_apply, b, Subtype.coe_mk, gB, dif_pos h,
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero]

theorem MatP_a : MatP 24 (G.getD 0 0) = matOf φJ (a (co1Data ())) := by
  have hdet : (mA (co1Data ())).det ≠ 0 := by
    rw [← seed_parts.2.1]
    exact det_ne_of_mul gen_parts.2.1
  rw [seed_parts.2.1]
  exact (val_a _ hdet).symm

theorem MatP_b : MatP 24 (G.getD 1 0) = matOf φJ (b (co1Data ())) := by
  have hdet : (mB (co1Data ())).det ≠ 0 := by
    rw [← seed_parts.2.2]
    exact det_ne_of_mul gen_parts.2.2
  rw [seed_parts.2.2]
  exact (val_b _ hdet).symm

noncomputable abbrev eA (k : ℕ) : J (co1Data ()) :=
  if k = 0 then a (co1Data ()) else if k = 1 then b (co1Data ()) else auxG (k - 2)

theorem letter_eq {t c : ℕ} (hc : c / 2 < 2 + t) :
    (if (decZ c).natAbs ≤ 2 then genG (co1Data ()) (decZ c)
      else if (decZ c).natAbs - 3 < t then
        (if 0 < decZ c then auxG ((decZ c).natAbs - 3) else (auxG ((decZ c).natAbs - 3))⁻¹)
      else 1) = letG eA c := by
  have hn : (decZ c).natAbs = c / 2 + 1 := by
    rw [decZ_eq]
    split_ifs <;> omega
  have hp : (0 < decZ c) ↔ ¬ c % 2 = 1 := by
    rw [decZ_eq]
    split_ifs <;> simp_all <;> omega
  rw [hn]
  unfold letG
  rcases (by omega : c / 2 = 0 ∨ c / 2 = 1 ∨ 2 ≤ c / 2) with h | h | h
  · rw [if_pos (by omega), h]
    by_cases hc2 : c % 2 = 1
    · rw [if_pos hc2, decZ_eq, if_pos hc2, h]
      simp [genG, eA]
    · rw [if_neg hc2, decZ_eq, if_neg hc2, h]
      simp [genG, eA]
  · rw [if_pos (by omega), h]
    by_cases hc2 : c % 2 = 1
    · rw [if_pos hc2, decZ_eq, if_pos hc2, h]
      simp [genG, eA]
    · rw [if_neg hc2, decZ_eq, if_neg hc2, h]
      simp [genG, eA]
  · rw [if_neg (by omega), if_pos (by omega)]
    have he : eA (c / 2) = auxG (c / 2 + 1 - 3) := by
      have e3 : c / 2 - 2 = c / 2 + 1 - 3 := by omega
      rw [eA, if_neg (by omega), if_neg (by omega), e3]
    by_cases hc2 : c % 2 = 1
    · rw [if_neg (by rw [hp]; exact not_not.2 hc2), if_pos hc2, he]
    · rw [if_pos (hp.2 hc2), if_neg hc2, he]

theorem auxG_eq {t : ℕ} (ht : t < aW.length) :
    eA (2 + t) = ((aW.getD t []).map (letG eA)).prod := by
  have hr := (slpK_spec ch120801_aux).2.2
  rw [seed_parts.1] at hr
  have e2 : eA (2 + t) = auxG t := by
    rw [eA, if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel_left]
  rw [e2, auxG, slpG_eq, aux_get ht, wordG, List.map_map]
  congr 1
  exact List.map_congr_left fun c hc => letter_eq (hr t ht c hc)

theorem MatP_aM {t : ℕ} (ht : t < aW.length) :
    MatP 24 (aM.getD t 0) = matOf φJ (auxG t) ∧ MatP 24 (aMi.getD t 0) = matOf φJ (auxG t)⁻¹ := by
  have hB : ∀ i < G.length, MatP 24 (G.getD i 0) = matOf φJ (eA i) ∧
      MatP 24 (Gi.getD i 0) = matOf φJ (eA i)⁻¹ := by
    intro i hi
    rw [seed_parts.1] at hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact ⟨MatP_a, MatP_inv_of MatP_a gen_parts.2.1⟩
    · exact ⟨MatP_b, MatP_inv_of MatP_b gen_parts.2.2⟩
  have hs := slpK_sound ch120801_aux hB fun t ht => by rw [seed_parts.1]; exact auxG_eq ht
  obtain ⟨-, h1, h2⟩ := hs t ht
  have e2 : eA (G.length + t) = auxG t := by
    rw [seed_parts.1, eA, if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel_left]
  rw [e2] at h1 h2
  exact ⟨h1, h2⟩

theorem getD_pick (L : List ℕ) {idx : List ℕ} {i : ℕ} (hi : i < idx.length) :
    (pickL L idx).getD i 0 = L.getD (idx.getD i 0) 0 := by
  rw [pickL_eq, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
    List.getD_eq_getElem _ _ hi]

theorem pick_parts {idx : List ℕ} (hidx : ∀ i ∈ idx, i < 301) (K : Subgroup (J (co1Data ())))
    (hK : ∀ i ∈ idx, auxG i ∈ K) :
    (pickL aM idx).length = idx.length ∧
    (∀ i < (pickL aM idx).length, MatP 24 ((pickL aM idx).getD i 0) =
        matOf φJ (auxG (idx.getD i 0)) ∧
      MatP 24 ((pickL aMi idx).getD i 0) = matOf φJ (auxG (idx.getD i 0))⁻¹) ∧
    ∀ i < (pickL aM idx).length, auxG (idx.getD i 0) ∈ K := by
  have hl : (pickL aM idx).length = idx.length := by rw [pickL_eq, List.length_map]
  have hm : ∀ i < idx.length, idx.getD i 0 ∈ idx := fun i hi => by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  refine ⟨hl, fun i hi => ?_, fun i hi => hK _ (hm i (by omega))⟩
  rw [hl] at hi
  have hlt : idx.getD i 0 < aW.length := by
    rw [aW_length]
    exact hidx _ (hm i hi)
  rw [getD_pick aM hi, getD_pick aMi hi]
  exact MatP_aM hlt

theorem MatP_tM (K : Subgroup (J (co1Data ()))) (hK : ∀ i ∈ tI, auxG i ∈ K) :
    ∀ t < tW.length, ∃ g ∈ K, MatP 24 (tM.getD t 0) = matOf φJ g ∧
      MatP 24 (tMi.getD t 0) = matOf φJ g⁻¹ := by
  obtain ⟨-, hB, hK'⟩ := pick_parts (by decide) K hK
  exact slpK_mem K ch120801_chain hB hK'

theorem MatP_gM (K : Subgroup (J (co1Data ()))) (hK : ∀ i ∈ hI, auxG i ∈ K) :
    ∀ t < gW.length, ∃ g ∈ K, MatP 24 (gM.getD t 0) = matOf φJ g ∧
      MatP 24 (gMi.getD t 0) = matOf φJ g⁻¹ := by
  obtain ⟨-, hB, hK'⟩ := pick_parts (by decide) K hK
  exact slpK_mem K ch120801_gw hB hK'

theorem eq_of_MatP {g h : J (co1Data ())} {M : ℕ} (hg : MatP 24 M = matOf φJ g)
    (hh : MatP 24 M = matOf φJ h) : g = h :=
  Subtype.val_injective (Units.ext (hg.symm.trans hh))

theorem eq_top_of_hI (K : Subgroup (J (co1Data ()))) (hK : ∀ i ∈ hI, auxG i ∈ K) : K = ⊤ := by
  have h := ch120801_gAB
  rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq, Nat.beq_eq,
    lenL_eq_length, getL_zero_eq, getL_zero_eq, getL_zero_eq, getL_zero_eq] at h
  obtain ⟨hl, h36, h37⟩ := h
  have hgl : gW.length = 38 := by rw [← (slpK_spec ch120801_gw).1, hl]
  obtain ⟨ga, hga, ea, -⟩ := MatP_gM K hK 36 (by omega)
  obtain ⟨gb, hgb, eb, -⟩ := MatP_gM K hK 37 (by omega)
  rw [h36] at ea
  rw [h37] at eb
  have e1 := eq_of_MatP ea MatP_a
  have e2 := eq_of_MatP eb MatP_b
  rw [eq_top_iff, ← closure_ab (co1Data ()), Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · rw [← e1]
    exact hga
  · rw [← e2]
    exact hgb

end CFSG.KD.Co1Sub

end
