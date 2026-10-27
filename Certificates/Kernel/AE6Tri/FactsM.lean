module

public import Certificates.Kernel.AE6Tri.MChain
public import Certificates.Kernel.AE6Tri.ChecksB
public import Certificates.Kernel.AE6Tri.Facts
public import CFSG.Certificates.Kernel.AE6TriSound
public import Certificates.Kernel.AE6F.Final

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAE6Tri

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.AE6Tri CFSG.KD.AE6Tri
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.EvenSmallLie.OmegaEight (omegaT)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

@[expose] noncomputable def gP (c : Nat) : Equiv.Perm (Fin 360) :=
  if c < 8 then CFSG.EvenSmallLie.OmegaEight.gen c else 1

theorem prep_gen {l : Nat} (hl : l < 8) :
    Orb.PRep 360 9 (CertificateChecks.KernelO8.AP.S l) (CFSG.EvenSmallLie.OmegaEight.gen l) := by
  have hp := allN_spec (CertificateChecks.KernelAE6F.perm_head CertificateChecks.KernelO8.AP.head)
    l (lt_of_lt_of_le hl (by norm_num))
  have hr := rep_permOfArr (Orb.isInvA_unpack hp)
  unfold CFSG.EvenSmallLie.OmegaEight.gen
  rw [CertificateChecks.KernelO8.genAP.2 l (by omega)]
  exact Orb.prep_of_rep hr.1

theorem gRep : GRep RG gP := by
  intro c
  by_cases hc : c < 8
  · have e : gl RG c = CertificateChecks.KernelO8.AP.S c := by
      unfold gl RG
      interval_cases c <;> rfl
    rw [e, gP, if_pos hc]
    exact prep_gen hc
  · have e : gl RG c = pidn 360 9 := by
      unfold gl
      rw [List.getD_eq_default]
      simp only [RG, List.length_cons, List.length_nil]
      omega
    rw [e, gP, if_neg hc]
    exact Orb.prep_pidn (by norm_num) (by norm_num)

theorem coe_curtisGen (i : Fin 8) : (A6.curtisGen i : Equiv.Perm (Fin 360)) = gP i.val := by
  rw [gP, if_pos i.isLt]
  rfl

@[expose] noncomputable def SM : Array (Array Nat) :=
  ((List.range 8).map fun j => unpack 360 9 (MQ.S j)).toArray

@[expose] def baseML : List (Fin 360) := [0, 2, 1, 4, 24, 8]

@[expose] def baseMA : Array Nat := (baseML.map Fin.val).toArray

theorem SM_get {j : Nat} (hj : j < 8) : SM[j]! = unpack 360 9 (MQ.S j) := by
  interval_cases j <;> rfl

theorem bindsM : Binds 360 9 MQ.S 8 6 MQ.BP SM baseMA := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [SM], fun j hj => SM_get hj, rfl,
    fun t ht => ?_⟩
  interval_cases t <;> decide

theorem rawOKM : rawChainOK 360 (SM.extract 0 5) SM baseMA
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 5 8 mDerive) 1 = true :=
  rawChainK_sound (NS := 15) (CH := 24) bindsM MQ.head MQ.hl (by norm_num) MQ.hs

theorem extract_sizeM : (SM.extract 0 5).size = 5 := by simp [SM]

theorem extract_getM {i : Nat} (hi : i < 5) : (SM.extract 0 5)[i]! = SM[i]! := by
  interval_cases i <;> rfl

theorem permsM : allN 8 (fun j => permOK 360 9 (mask 9) (360 * 9) (MQ.S j) (MQ.SI j)) = true :=
  CertificateChecks.KernelAE6F.perm_head MQ.head

theorem genM : ∀ k < 5, permOfArr 360 SM[k]! = gP (ml.getD k 0) := by
  have hl : ml.length = 5 := shapes.2.2.2.2.1
  refine fun k hk => mgOK_sound gRep (s := fun j => permOfArr 360 SM[j]!)
    (fun j hj => (Orb.prep_PS bindsM permsM (j := j) (by omega)).1) kGensMQ k (by omega)

theorem ml_bits : ∀ k < 5, ml.getD k 0 < 8 ∧ bit 93 (ml.getD k 0) = true := by decide

theorem ml_of_bit : ∀ c < 8, bit 93 c = true → ∃ k < 5, ml.getD k 0 = c := by decide

theorem gens_eq : {g | ∃ k < (SM.extract 0 5).size, permOfArr 360 (SM.extract 0 5)[k]! = g} =
    {x | ∃ c < 8, bit 93 c = true ∧ gP c = x} := by
  ext x
  rw [extract_sizeM]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [extract_getM hk, genM k hk]
    exact ⟨_, (ml_bits k hk).1, (ml_bits k hk).2, rfl⟩
  · rintro ⟨c, hc, hb, rfl⟩
    obtain ⟨k, hk, rfl⟩ := ml_of_bit c hc hb
    exact ⟨k, hk, by rw [extract_getM hk, genM k hk]⟩

theorem prodM : (rawOrbitSizes 360 SM baseMA).prod = 12288 := by
  rw [rawOrbitSizesK_sound bindsM permsM MQ.hl, ← Nat.eq_of_beq_eq_true kOrdMQ]
  simp [List.range_succ]
  ring

theorem cardM : Nat.card (lsub gP 93) = 12288 := by
  have h := CFSG.Quasithin.card_closure_permOfArr_of_rawChainOK (n := 360) (O := SM.extract 0 5)
    (S := SM) (base := baseML) (W := CFSG.Sporadic.Schreier.Co3.Native.wordsArr 5 8 mDerive)
    (chunks := 1) (by norm_num) (by decide) (by norm_num) (by rw [extract_sizeM]; simp [SM])
    (fun i hi => (extract_getM (extract_sizeM ▸ hi)).symm) (by rw [extract_sizeM]; exact rawOKM)
  rw [gens_eq] at h
  rw [← prodM]
  exact h

theorem allIx_get {α : Type} : ∀ {L : List α} {f : Nat → α → Bool} {i₀ : Nat},
    allIx L f i₀ = true → ∀ i (hi : i < L.length), f (i + i₀) L[i] = true
  | [], _, _, _, i, hi => absurd hi (by simp)
  | a :: t, f, i₀, h, i, hi => by
    have h' := (bAnd_iff _ _).1 h
    cases i with
    | zero => simpa using h'.1
    | succ i =>
      have := allIx_get h'.2 i (by simpa using hi)
      rw [show i + 1 + i₀ = i + Nat.succ i₀ by omega]
      simpa using this

theorem tzB_eq : tzB = [0, 172, 36] := kLevLen.2

theorem words_ok : (∀ l < 3, ∀ c ∈ tzH.getD l [], c < 8 ∧ bit 93 c = true) ∧
    ∀ l < 3, ∀ w ∈ tzW.getD l [], ∀ c ∈ w, c < 8 ∧ bit 93 c = true := by decide

theorem lev_len : ∀ l < 3, (tzW.getD l []).length = [64, 32, 6].getD l 0 := by decide

theorem fix_base {z : Equiv.Perm (Fin 360)} (hz : z ∈ lsub gP 93)
    (hc : ∀ x ∈ lsub gP 93, z * x = x * z) {l : Nat} (hl : l < 3) (hb : tzB.getD l 0 < 360) :
    z ⟨tzB.getD l 0, hb⟩ = ⟨tzB.getD l 0, hb⟩ := by
  have hk := allIx_get kSep l (by rw [tzB_eq]; simpa using hl)
  rw [Nat.add_zero, ← List.getD_eq_getElem _ 0] at hk
  obtain ⟨hp, hb', hinv, hpO, hsep, -, hw⟩ := sepOK_sound gRep hk
  let O : Finset (Fin 360) := Finset.univ.filter fun q => q.val ∈ tzO.getD l []
  have hO : ∀ x ∈ lsub gP 93, ∀ q ∈ O, x q ∈ O := maps_of_closure (by
    rintro x ⟨c, hc8, hbc, rfl⟩ q hq
    simp only [O, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    exact hinv c hc8 hbc q hq)
  have hfix := fix_of_sep hc hz hO (p := ⟨tzP.getD l 0, hp⟩)
    (by simp only [O, Finset.mem_filter, Finset.mem_univ, true_and]; exact hpO)
    (fun q hq hne => by
      simp only [O, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      obtain ⟨c, hc8, hbc, hcp, hcq⟩ := hsep q hq (fun e => hne (Fin.ext e))
      exact ⟨gP c, Subgroup.subset_closure ⟨c, hc8, hbc, rfl⟩, hcp, hcq⟩)
    (h := wv gP (tzH.getD l [])) (wv_mem _ (words_ok.1 l hl))
  rw [hw] at hfix
  exact hfix

theorem lev_images {l : Nat} (hl : l < 3) (hb : tzB.getD l 0 < 360) :
    ∃ S : Finset (Fin 360), S.card = [64, 32, 6].getD l 0 ∧ ∀ p ∈ S, ∃ x ∈ lsub gP 93,
      (∀ c : Fin 360, c.val ∈ tzB.take l → x c = c) ∧ x ⟨tzB.getD l 0, hb⟩ = p := by
  classical
  have hk := allIx_get kLev l (by rw [tzB_eq]; simpa using hl)
  rw [Nat.add_zero, ← List.getD_eq_getElem _ 0] at hk
  obtain ⟨hw, hd⟩ := levOK_sound gRep hb hk
  refine ⟨((tzW.getD l []).map fun w => wv gP w ⟨tzB.getD l 0, hb⟩).toFinset, ?_, ?_⟩
  · rw [List.toFinset_card_of_nodup (List.pairwise_map.2 hd), List.length_map, lev_len l hl]
  · intro p hp
    obtain ⟨w, hwm, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hp)
    exact ⟨wv gP w, wv_mem _ (words_ok.2 l hl w hwm), (hw w hwm).2, rfl⟩

theorem tz_perm {z : Equiv.Perm (Fin 360)} (hz : z ∈ lsub gP 93)
    (hc : ∀ c < 8, bit 93 c = true → z * gP c = gP c * z) : z = 1 := by
  have hcK : ∀ x ∈ lsub gP 93, z * x = x * z := comm_of_closure (by
    rintro x ⟨c, hc8, hb, rfl⟩
    exact hc c hc8 hb)
  have f0 := fix_base hz hcK (l := 0) (by norm_num) (by rw [tzB_eq]; decide)
  have f1 := fix_base hz hcK (l := 1) (by norm_num) (by rw [tzB_eq]; decide)
  have f2 := fix_base hz hcK (l := 2) (by norm_num) (by rw [tzB_eq]; decide)
  obtain ⟨S0, c0, h0⟩ := lev_images (l := 0) (by norm_num) (by rw [tzB_eq]; decide)
  obtain ⟨S1, c1, h1⟩ := lev_images (l := 1) (by norm_num) (by rw [tzB_eq]; decide)
  obtain ⟨S2, c2, h2⟩ := lev_images (l := 2) (by norm_num) (by rw [tzB_eq]; decide)
  simp only [tzB_eq] at f0 f1 f2 h0 h1 h2
  simp only [List.getD_cons_zero, List.getD_cons_succ] at c0 c1 c2
  refine eq_one_of_base (K := lsub gP 93) _ _ _ S0 S1 S2
    (fun p hp => by
      obtain ⟨x, hx, -, e⟩ := h0 p hp
      exact ⟨x, hx, e⟩)
    (fun p hp => by
      obtain ⟨x, hx, hf, e⟩ := h1 p hp
      exact ⟨x, hx, hf _ (by simp), e⟩)
    (fun p hp => by
      obtain ⟨x, hx, hf, e⟩ := h2 p hp
      exact ⟨x, hx, hf _ (by simp), hf _ (by simp), e⟩)
    (by rw [cardM, c0, c1, c2]) (by rw [c0, c1, c2]; norm_num) hz f0 f1 f2

theorem ae6M_le : ae6LetterSub ↑ae6MLetters ≤ (lsub gP 93).comap omegaT.subtype := by
  rw [ae6LetterSub, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  have hb := (mask_iff i).1.2 hi
  exact Subgroup.subset_closure ⟨i.val, i.isLt, hb, (coe_curtisGen i).symm⟩

theorem map_ae6M : (ae6LetterSub ↑ae6MLetters).map omegaT.subtype = lsub gP 93 := by
  rw [ae6LetterSub, MonoidHom.map_closure, lsub]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i.val, i.isLt, (mask_iff i).1.2 hi, (coe_curtisGen i).symm⟩
  · rintro ⟨c, hc, hb, rfl⟩
    exact ⟨_, ⟨⟨c, hc⟩, (mask_iff ⟨c, hc⟩).1.1 hb, rfl⟩, coe_curtisGen ⟨c, hc⟩⟩

theorem card_ae6M : Nat.card (ae6LetterSub ↑ae6MLetters) = 12288 := by
  rw [← cardM, ← map_ae6M, Subgroup.card_map_of_injective omegaT.subtype_injective]

theorem tz : ∀ m ∈ ae6LetterSub ↑ae6MLetters,
    (∀ i ∈ ae6MLetters, m * A6.curtisGen i = A6.curtisGen i * m) → m = 1 := by
  intro m hm hc
  apply Subtype.ext
  refine tz_perm (ae6M_le hm) fun c hc8 hb => ?_
  have e := congrArg Subtype.val (hc ⟨c, hc8⟩ ((mask_iff ⟨c, hc8⟩).1.1 hb))
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_curtisGen] at e
  exact e

end CertificateChecks.KernelAE6Tri

end
