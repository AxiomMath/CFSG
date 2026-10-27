module

public import CFSG.Quasithin.Background.HParabCode22Gen
public import CFSG.Quasithin.Background.HB82Code22
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23L34Gen

public section

namespace CFSG.Quasithin.H.Code22

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Mathieu.H16Pf CFSG.Quasithin.H.Coc
  CFSG.Quasithin.H.Parab CFSG.Quasithin.H.FixSyl
open scoped commutatorElement

@[expose] def q16P (t : Fin 16) : Equiv.Perm (Fin 24) :=
  permOfArr 24 (q16Arr t) (q16Arr t) (q16_inv t t.2)

theorem hasArr_q16P (t : Fin 16) : HasArr (q16P t) (q16Arr t) := hasArr_permOfArr _

theorem hasArr_q16P_inv (t : Fin 16) : HasArr (q16P t)⁻¹ (q16Arr t) := hasArr_permOfArr_inv _

theorem eq_of_hasArr_q16 {σ : Equiv.Perm (Fin 24)} {s t : ℕ} (hs : s < 16) (ht : t < 16)
    (h1 : HasArr σ (q16Arr s)) (h2 : HasArr σ (q16Arr t)) : s = t := by
  by_contra hne
  obtain ⟨k, hk, hne'⟩ := q16_sep s hs t ht hne
  exact hne' ((h1 ⟨k, hk⟩).symm.trans (h2 ⟨k, hk⟩))

theorem q16P_mul (s t : Fin 16) :
    q16P s * q16P t = q16P ⟨s ^^^ t, Nat.xor_lt_two_pow (n := 4) s.2 t.2⟩ := by
  refine perm_eq_of_hasArr (hasArr_mul (hasArr_q16P s) (hasArr_q16P t)) ?_
  rw [q16_mul s s.2 t t.2]
  exact hasArr_q16P _

theorem q16P_zero : q16P 0 = 1 := by
  refine perm_eq_of_hasArr (hasArr_q16P 0) ?_
  rw [show q16Arr ((0 : Fin 16) : ℕ) = idArr by decide]
  exact hasArr_one

theorem q16P_mul_self (t : Fin 16) : q16P t * q16P t = 1 := by
  rw [q16P_mul, ← q16P_zero]
  exact congrArg q16P (Fin.ext (Nat.xor_self _))

@[expose] def Q16P : Subgroup (Equiv.Perm (Fin 24)) where
  carrier := Set.range q16P
  mul_mem' := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨_, (q16P_mul s t).symm⟩
  one_mem' := ⟨0, q16P_zero⟩
  inv_mem' := by
    rintro _ ⟨t, rfl⟩
    exact ⟨t, (inv_eq_of_mul_eq_one_right (q16P_mul_self t)).symm⟩

theorem mem_Q16P {σ : Equiv.Perm (Fin 24)} : σ ∈ Q16P ↔ ∃ t, q16P t = σ := Iff.rfl

theorem card_Q16P : Nat.card Q16P = 16 := by
  have hf : Function.Injective fun t : Fin 16 => (⟨q16P t, t, rfl⟩ : Q16P) := by
    intro s t h
    have h' : q16P s = q16P t := congrArg Subtype.val h
    exact Fin.ext (eq_of_hasArr_q16 s.2 t.2 (hasArr_q16P s) (by rw [h']; exact hasArr_q16P t))
  have hs : Function.Surjective fun t : Fin 16 => (⟨q16P t, t, rfl⟩ : Q16P) := by
    rintro ⟨_, t, rfl⟩
    exact ⟨t, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ ⟨hf, hs⟩), Nat.card_eq_fintype_card, Fintype.card_fin]

theorem hbQ_mem_of_word {σ : Equiv.Perm (Fin 24)} {w : List ℕ}
    (h : HasArr σ (wArr [hbAArr, hbBArr] w)) : σ ∈ hbQ := by
  rw [perm_eq_of_hasArr h (hasArr_wPerm (Coc24.hasArr_getD₂ hasArr_hbA hasArr_hbB) w)]
  refine wPerm_mem (fun p hp => ?_) w
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact hbA_mem_Q
  · exact hbB_mem_Q

theorem Q16P_le_hbQ : Q16P ≤ hbQ := by
  rintro _ ⟨t, rfl⟩
  exact hbQ_mem_of_word ((q16_words t t.2).symm ▸ hasArr_q16P t)

@[expose] def q16B (j : ℕ) : Fin 16 := ⟨2 ^ j % 16, Nat.mod_lt _ (by norm_num)⟩

theorem hasArr_q16B {j : ℕ} (hj : j < 4) : HasArr (q16P (q16B j)) (q16Basis.getD j idArr) := by
  rw [← q16_basis j hj]
  have h := hasArr_q16P (q16B j)
  rwa [show ((q16B j : Fin 16) : ℕ) = 2 ^ j from Nat.mod_eq_of_lt
    (lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) hj) (by norm_num))] at h

@[expose] def q16BPs : List (Equiv.Perm (Fin 24)) := (List.range 4).map fun j => q16P (q16B j)

theorem hasArr_q16BPs : ∀ i, HasArr (q16BPs.getD i 1) (q16Basis.getD i idArr) := by
  intro i
  by_cases hi : i < 4
  · rw [q16BPs, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
      List.getElem_range]
    exact hasArr_q16B hi
  · rw [List.getD_eq_default _ _ (by simp [q16BPs]; omega),
      List.getD_eq_default _ _ (by simp [q16Basis]; omega)]
    exact hasArr_one

theorem q16P_mem {K : Subgroup (Equiv.Perm (Fin 24))} (h : ∀ j < 4, q16P (q16B j) ∈ K)
    (t : Fin 16) : q16P t ∈ K := by
  have hw := hasArr_wPerm hasArr_q16BPs ((List.range 4).filter fun i => (t : ℕ).testBit i)
  rw [q16_bits t t.2] at hw
  rw [perm_eq_of_hasArr (hasArr_q16P t) hw]
  refine wPerm_mem (fun p hp => ?_) _
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hp
  exact h j (List.mem_range.1 hj)

@[expose] def q16KcP (i : ℕ) : Equiv.Perm (Fin 24) :=
  if i < 4 then ⁅q16P (q16B i), hbA⁆ else ⁅q16P (q16B (i - 4)), hbB⁆

theorem hasArr_q16KcP {i : ℕ} (hi : i < 8) : HasArr (q16KcP i) (q16KcArr i) := by
  unfold q16KcP q16KcArr
  split_ifs with h4
  · rw [commutatorElement_def, mul_assoc (q16P (q16B i) * hbA)]
    have hq : HasArr (q16P (q16B i))⁻¹ (q16Basis.getD i idArr) := by
      rw [← q16_basis i h4]
      have h := hasArr_q16P_inv (q16B i)
      rwa [show ((q16B i : Fin 16) : ℕ) = 2 ^ i from Nat.mod_eq_of_lt
        (lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) h4) (by norm_num))] at h
    exact hasArr_mul (hasArr_mul (hasArr_q16B h4) hasArr_hbA) (hasArr_mul hq hasArr_hbAinv)
  · have h4' : i - 4 < 4 := by omega
    rw [commutatorElement_def, mul_assoc (q16P (q16B (i - 4)) * hbB)]
    have hq : HasArr (q16P (q16B (i - 4)))⁻¹ (q16Basis.getD (i - 4) idArr) := by
      rw [← q16_basis (i - 4) h4']
      have h := hasArr_q16P_inv (q16B (i - 4))
      rwa [show ((q16B (i - 4) : Fin 16) : ℕ) = 2 ^ (i - 4) from Nat.mod_eq_of_lt
        (lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) h4') (by norm_num))] at h
    exact hasArr_mul (hasArr_mul (hasArr_q16B h4') hasArr_hbB) (hasArr_mul hq hasArr_hbBinv)

theorem hasArr_q16KcPs :
    ∀ i, HasArr (((List.range 8).map q16KcP).getD i 1) (q16Kc.getD i idArr) := by
  intro i
  by_cases hi : i < 8
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range,
      q16Kc, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
    exact hasArr_q16KcP hi
  · rw [List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp [q16Kc]; omega)]
    exact hasArr_one

theorem q16_le_comm : Q16P ≤ ⁅Q16P, hbQ⁆ := by
  have hB : ∀ j < 4, q16P (q16B j) ∈ Q16P := fun j _ => ⟨_, rfl⟩
  have hkc : ∀ p ∈ (List.range 8).map q16KcP, p ∈ ⁅Q16P, hbQ⁆ := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
    have hi8 := List.mem_range.1 hi
    unfold q16KcP
    split_ifs with h4
    · exact Subgroup.commutator_mem_commutator (hB i h4) hbA_mem_Q
    · exact Subgroup.commutator_mem_commutator (hB (i - 4) (by omega)) hbB_mem_Q
  refine fun σ hσ => ?_
  obtain ⟨t, rfl⟩ := hσ
  refine q16P_mem (fun j hj => ?_) t
  have hw := hasArr_wPerm hasArr_q16KcPs (q16CommWords.getD j [])
  rw [q16_comm j hj] at hw
  rw [perm_eq_of_hasArr (hasArr_q16B hj) hw]
  exact wPerm_mem hkc _

@[expose] def s1GP (g : ℕ) : Equiv.Perm (Fin 24) :=
  if h : g < 6 then permOfArr 24 (s1Gens.getD g idArr) (s1Gens.getD g idArr) (s1Gens_inv g h)
  else 1

@[expose] def s1GPs : List (Equiv.Perm (Fin 24)) := (List.range 6).map s1GP

theorem hasArr_s1GP {g : ℕ} (hg : g < 6) : HasArr (s1GP g) (s1Gens.getD g idArr) := by
  rw [s1GP, dite_eq_left hg]
  exact hasArr_permOfArr _

theorem s1GP_mul_self (g : ℕ) : s1GP g * s1GP g = 1 := by
  unfold s1GP
  split_ifs
  · exact permOfArr_mul_self _
  · exact one_mul 1

theorem hasArr_s1GPs : ∀ i, HasArr (s1GPs.getD i 1) (s1Gens.getD i idArr) := by
  intro i
  by_cases hi : i < 6
  · rw [s1GPs, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
      List.getElem_range]
    exact hasArr_s1GP hi
  · rw [List.getD_eq_default _ _ (by simp [s1GPs]; omega),
      List.getD_eq_default _ _ (by simp [s1Gens, q16Basis]; omega)]
    exact hasArr_one

@[expose] def S1P : Subgroup (Equiv.Perm (Fin 24)) :=
  Subgroup.closure (Set.range fun g : Fin 6 => s1GP g)

theorem s1GP_mem_S1P (g : ℕ) : s1GP g ∈ S1P := by
  by_cases hg : g < 6
  · exact Subgroup.subset_closure ⟨⟨g, hg⟩, rfl⟩
  · rw [s1GP, dite_eq_right hg]
    exact S1P.one_mem

@[expose] def s1Q (i : ℕ) : Equiv.Perm (Fin 24) := wPerm s1GPs (s1Words.getD i [])

theorem hasArr_s1Q {i : ℕ} (hi : i < 64) : HasArr (s1Q i) (s1Arr i) := by
  have hw := hasArr_wPerm hasArr_s1GPs (s1Words.getD i [])
  rwa [s1_words i hi] at hw

theorem s1Q_mem (i : ℕ) : s1Q i ∈ S1P := by
  refine wPerm_mem (fun p hp => ?_) _
  obtain ⟨g, -, rfl⟩ := List.mem_map.1 hp
  exact s1GP_mem_S1P g

theorem eq_of_hasArr_s1 {σ : Equiv.Perm (Fin 24)} {i j : ℕ} (hi : i < 64) (hj : j < 64)
    (h1 : HasArr σ (s1Arr i)) (h2 : HasArr σ (s1Arr j)) : i = j := by
  by_contra hne
  obtain ⟨k, hk, hne'⟩ := s1_sep i hi j hj hne
  exact hne' ((h1 ⟨k, hk⟩).symm.trans (h2 ⟨k, hk⟩))

theorem mem_S1P {σ : Equiv.Perm (Fin 24)} : σ ∈ S1P ↔ ∃ i < 64, HasArr σ (s1Arr i) := by
  constructor
  · intro h
    induction h using Subgroup.closure_induction_right with
    | one => exact ⟨0, by norm_num, s1_one ▸ hasArr_one⟩
    | mul_right x _ y hy ih =>
      obtain ⟨g, rfl⟩ := hy
      obtain ⟨i, hi, hx⟩ := ih
      obtain ⟨hlt, heq⟩ := s1_mulR i hi g g.2
      refine ⟨_, hlt, ?_⟩
      rw [← heq]
      exact hasArr_mul hx (hasArr_s1GP g.2)
    | mul_inv_cancel x _ y hy ih =>
      obtain ⟨g, rfl⟩ := hy
      obtain ⟨i, hi, hx⟩ := ih
      obtain ⟨hlt, heq⟩ := s1_mulR i hi g g.2
      refine ⟨_, hlt, ?_⟩
      rw [inv_eq_of_mul_eq_one_right (s1GP_mul_self g), ← heq]
      exact hasArr_mul hx (hasArr_s1GP g.2)
  · rintro ⟨i, hi, hσ⟩
    rw [perm_eq_of_hasArr hσ (hasArr_s1Q hi)]
    exact s1Q_mem i

theorem card_S1P : Nat.card S1P = 64 := by
  have hf : Function.Injective fun i : Fin 64 => (⟨s1Q i, s1Q_mem i⟩ : S1P) := by
    intro i j h
    have h' : s1Q i = s1Q j := congrArg Subtype.val h
    exact Fin.ext (eq_of_hasArr_s1 i.2 j.2 (hasArr_s1Q i.2) (by rw [h']; exact hasArr_s1Q j.2))
  have hs : Function.Surjective fun i : Fin 64 => (⟨s1Q i, s1Q_mem i⟩ : S1P) := by
    rintro ⟨σ, hσ⟩
    obtain ⟨i, hi, hσi⟩ := mem_S1P.1 hσ
    exact ⟨⟨i, hi⟩, Subtype.ext (perm_eq_of_hasArr (hasArr_s1Q hi) hσi)⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ ⟨hf, hs⟩), Nat.card_eq_fintype_card, Fintype.card_fin]

theorem S1P_le_hbQ : S1P ≤ hbQ := by
  rw [S1P, Subgroup.closure_le]
  rintro _ ⟨⟨g, hg⟩, rfl⟩
  show s1GP g ∈ hbQ
  have hgen : HasArr (s1GP g) (s1Gens.getD g idArr) := hasArr_s1GP hg
  rcases (by omega : g < 4 ∨ g = 4 ∨ g = 5) with h4 | rfl | rfl
  · have h : s1Gens.getD g idArr = q16Basis.getD g idArr := by
      rw [s1Gens, List.getD_append _ _ _ _ (by simp [q16Basis]; omega)]
    rw [h] at hgen
    rw [perm_eq_of_hasArr hgen (hasArr_q16B h4)]
    exact Q16P_le_hbQ ⟨_, rfl⟩
  · exact hbQ_mem_of_word (by rw [v_words.1]; exact hgen)
  · exact hbQ_mem_of_word (by rw [v_words.2]; exact hgen)

@[expose] def tripKey (σ : Equiv.Perm (Fin 24)) : ℕ :=
  (σ 2 : ℕ) + 24 * (σ 3 : ℕ) + 576 * (σ 4 : ℕ)

theorem tripKey_mul {σ τ : Equiv.Perm (Fin 24)} {a : Array ℕ} (hσ : HasArr σ a) :
    tripKey (σ * τ) = tripAct a (tripKey τ) := by
  have h2 := (τ 2).2
  have h3 := (τ 3).2
  have h4 := (τ 4).2
  have e1 : tripKey τ % 24 = τ 2 := by unfold tripKey; omega
  have e2 : tripKey τ / 24 % 24 = τ 3 := by unfold tripKey; omega
  have e3 : tripKey τ / 576 = τ 4 := by unfold tripKey; omega
  unfold tripAct
  rw [e1, e2, e3, ← hσ, ← hσ, ← hσ]
  rfl

theorem le_card_hbQ : 960 ≤ Nat.card hbQ := by
  have h := le_card_of_tree (K := hbQ) tripKey hbQTripAct (fun gi m => by
      rintro ⟨σ, hσ, rfl⟩
      by_cases hg : gi = 0
      · refine ⟨hbA * σ, hbQ.mul_mem hbA_mem_Q hσ, ?_⟩
        rw [tripKey_mul hasArr_hbA, hbQTripAct, ite_eq_left hg]
      · refine ⟨hbB * σ, hbQ.mul_mem hbB_mem_Q hσ, ?_⟩
        rw [tripKey_mul hasArr_hbB, hbQTripAct, ite_eq_right hg])
    (start := 2378) ⟨1, hbQ.one_mem, rfl⟩ hbQTree_ok
  rwa [hbQTree_length] at h

theorem card_stab_UC_le :
    Nat.card ↥(imgC mog22 ⊓ stabSub UC) ≤ 1920 := by
  have hmem : ∀ i < [cRhoA, cRhoB].length, [cRhoA, cRhoB].getD i 1 ∈ imgC mog22 := by
    intro i hi
    rcases i with _ | _ | i
    · exact rhoC10_mem_imgC _
    · exact rhoC10_mem_imgC _
    · simp at hi
  have hact : ∀ i < [cRhoA, cRhoB].length,
      ActsBy ([cRhoA, cRhoB].getD i 1) ([c22A, c22B].getD i []) := by
    intro i hi
    rcases i with _ | _ | i
    · exact actsBy_cRhoA
    · exact actsBy_cRhoB
    · simp at hi
  have h := card_stab_le_of_orb hmem hact (d := hbU0Basis) (st := ucSteps)
    (fun e he => by simpa using ucSteps_lt e he) uc_orb_lt uc_orb_nodup
  rw [uc_orb_length, card_imgC_mog22] at h
  have h' : 231 * Nat.card ↥(imgC mog22 ⊓ stabSub UC) ≤ 443520 := h
  omega

@[expose] def tP : Equiv.Perm (Fin 24) := permOfArr 24 tArr tInv t_ok.1

theorem hasArr_tP : HasArr tP tArr := hasArr_permOfArr _

theorem hasArr_tPinv : HasArr tP⁻¹ tInv := hasArr_permOfArr_inv _

theorem tP_mem : tP ∈ mog22 :=
  mem_mog22_of_arr (mem_AutPerm_of_arr _ t_ok.2.1) hasArr_tP t_ok.2.2.1 t_ok.2.2.2.1

theorem rho_tP_mem : rhoC10 mog22 mog22_le_mog22plus ⟨tP, tP_mem⟩ ∈ imgC mog22 ⊓ stabSub UC := by
  refine ⟨rhoC10_mem_imgC _, ?_⟩
  have hinv : ∀ m < 2 ^ 10, (rhoC10 mog22 mog22_le_mog22plus ⟨tP, tP_mem⟩)⁻¹ (toW 10 m) =
      toW 10 (actC10 tInv m) := fun m _ => by
    rw [← map_inv]
    exact rhoC10_toW mog22 mog22_le_mog22plus (⟨tP, tP_mem⟩⁻¹ : ↥mog22) hasArr_tPinv m
  exact mem_stabSub_of_maps (maps_UC (f := actC10 tArr)
    (fun m _ => rhoC10_toW mog22 mog22_le_mog22plus _ hasArr_tP m) (fun m _ => actC10_lt _ _)
    (fun m hm => (t_pres m hm).1)) (maps_UC hinv (fun m _ => actC10_lt _ _)
    (fun m hm => (t_pres m hm).2))

theorem hbQ_fix13 : ∀ σ ∈ hbQ, σ 13 = 13 := by
  have h : hbQ ≤ MulAction.stabilizer (Equiv.Perm (Fin 24)) (13 : Fin 24) := by
    rw [hbQ, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hasArr_hbA.apply_eq 13 hb_fix13.1
    · exact hasArr_hbB.apply_eq 13 hb_fix13.2
  exact fun σ hσ => h hσ

theorem rho_tP_not_mem :
    rhoC10 mog22 mog22_le_mog22plus ⟨tP, tP_mem⟩ ∉ imgC hbQ := by
  rintro ⟨σ, hσ, he⟩
  have h1 : σ = ⟨tP, tP_mem⟩ := ModelType.rhoC10_mog22_injective he
  have h2 := hbQ_fix13 _ (Subgroup.mem_subgroupOf.1 hσ)
  rw [h1] at h2
  have h3 : tP 13 = 19 := hasArr_tP.apply_eq 13 t_ok.2.2.2.2
  rw [h2] at h3
  exact absurd h3 (by decide)

theorem card_imgC_hbQ_eq :
    Nat.card ↥(imgC hbQ) = Nat.card hbQ := by
  rw [imgC, Subgroup.card_map_of_injective ModelType.rhoC10_mog22_injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hbQ_le).toEquiv]

theorem card_stab_UC :
    Nat.card ↥(imgC hbQ) = 960 ∧ Nat.card ↥(imgC mog22 ⊓ stabSub UC) = 2 * 960 := by
  have : Finite (MulAut W10) := finite_mulAut_z (V := W10)
  have hc := Subgroup.card_mul_index ((imgC hbQ).subgroupOf (imgC mog22 ⊓ stabSub UC))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe imgC_hbQ_le).toEquiv,
    card_imgC_hbQ_eq] at hc
  have hi1 : ((imgC hbQ).subgroupOf (imgC mog22 ⊓ stabSub UC)).index ≠ 1 := by
    intro h1
    rw [Subgroup.index_eq_one] at h1
    have hmem : (⟨_, rho_tP_mem⟩ : ↥(imgC mog22 ⊓ stabSub UC)) ∈
        (imgC hbQ).subgroupOf (imgC mog22 ⊓ stabSub UC) := by
      rw [h1]
      trivial
    exact rho_tP_not_mem (Subgroup.mem_subgroupOf.1 hmem)
  have hi0 : ((imgC hbQ).subgroupOf (imgC mog22 ⊓ stabSub UC)).index ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have hle := card_stab_UC_le
  have hge := le_card_hbQ
  have hi2 : ((imgC hbQ).subgroupOf (imgC mog22 ⊓ stabSub UC)).index = 2 := by
    rcases Nat.lt_or_ge ((imgC hbQ).subgroupOf (imgC mog22 ⊓ stabSub UC)).index 3 with h | h
    · omega
    · nlinarith
  rw [hi2] at hc
  refine ⟨?_, ?_⟩
  · rw [card_imgC_hbQ_eq]
    omega
  · rw [← hc]
    omega

theorem card_imgC_hbQ :
    Nat.card ↥(imgC hbQ) = 960 :=
  card_stab_UC.1

theorem card_hbQ :
    Nat.card hbQ = 960 := by
  rw [← card_imgC_hbQ_eq]
  exact card_imgC_hbQ

theorem perfectCore_stab_UC :
    perfectCore (imgC mog22 ⊓ stabSub UC) = imgC hbQ := by
  have : Finite (MulAut W10) := finite_mulAut_z (V := W10)
  refine le_antisymm ?_ (le_perfectCore_of_perfect imgC_hbQ_le commutator_imgC_hbQ)
  refine (perfectCore_le_derivedSeriesOf _ 1).trans ?_
  rw [derivedSeriesOf_succ, derivedSeriesOf_zero]
  refine Coc24.commutator_le_of_card_two_mul imgC_hbQ_le ?_
  rw [card_stab_UC.2, card_imgC_hbQ]

theorem factorization_960' : (960 : ℕ).factorization 2 = 6 := by
  rw [show (960 : ℕ) = 2 ^ 6 * 15 by norm_num, Nat.factorization_mul (by positivity) (by norm_num),
    Finsupp.add_apply, Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem pCoreOf_hbQ_le :
    pCoreOf 2 hbQ ≤ Q16P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.Open.pCore 2 ↥hbQ with hN
  have hNn : N.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hNp : IsPGroup 2 N := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hT : Nat.card (S1P.subgroupOf hbQ) = 2 ^ (Nat.card ↥hbQ).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S1P_le_hbQ).toEquiv, card_S1P, card_hbQ,
      factorization_960']
    norm_num
  let T : Sylow 2 ↥hbQ := Sylow.ofCard (S1P.subgroupOf hbQ) hT
  have hNT : N ≤ (T : Subgroup ↥hbQ) := hNp.le_sylow_of_normal T
  have hS1 : ∀ n ∈ N, (n : Equiv.Perm (Fin 24)) ∈ S1P := fun n hn =>
    Subgroup.mem_subgroupOf.1 (hNT hn)
  rintro _ ⟨n, hn, rfl⟩
  obtain ⟨i, hi, hni⟩ := mem_S1P.1 (hS1 n hn)
  by_cases h16 : i < 16
  · exact ⟨⟨i, h16⟩, perm_eq_of_hasArr (hasArr_q16P _) (by rw [← s1_q16 i h16]; exact hni)⟩
  · exfalso
    set bQ : ↥hbQ := ⟨hbB, hbB_mem_Q⟩
    have hy : bQ⁻¹ * n * bQ⁻¹⁻¹ ∈ N := hNn.conj_mem n hn bQ⁻¹
    obtain ⟨j, hj, hnj⟩ := mem_S1P.1 (hS1 _ hy)
    have hc : HasArr ((bQ⁻¹ * n * bQ⁻¹⁻¹ : ↥hbQ) : Equiv.Perm (Fin 24))
        (cArr hbBInv (cArr (s1Arr i) hbBArr)) := by
      show HasArr (hbB⁻¹ * (n : Equiv.Perm (Fin 24)) * hbB⁻¹⁻¹) _
      rw [inv_inv, mul_assoc]
      exact hasArr_mul hasArr_hbBinv (hasArr_mul hni hasArr_hbB)
    obtain ⟨k, hk, hne⟩ := s1_conj i hi (by omega) j hj
    exact hne ((hc ⟨k, hk⟩).symm.trans (hnj ⟨k, hk⟩))

theorem pCoreOf_imgC_hbQ_le :
    pCoreOf 2 (imgC hbQ) ≤ imgC Q16P := by
  rw [imgC, pCoreOf_map_of_injective 2 _ ModelType.rhoC10_mog22_injective,
    Coc24.pCoreOf_subgroupOf hbQ_le]
  exact Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.2 (pCoreOf_hbQ_le (Subgroup.mem_subgroupOf.1 hx))

theorem imgC_q16_le_comm : imgC Q16P ≤ ⁅imgC Q16P, imgC hbQ⁆ := by
  have hQ : Q16P ≤ mog22 := Q16P_le_hbQ.trans hbQ_le
  have hC : ⁅Q16P, hbQ⁆ ≤ mog22 :=
    (Subgroup.commutator_mono Q16P_le_hbQ le_rfl).trans (commutator_hbQ.le.trans hbQ_le)
  have h : ⁅Q16P.subgroupOf mog22, hbQ.subgroupOf mog22⁆ = (⁅Q16P, hbQ⁆).subgroupOf mog22 := by
    apply Subgroup.map_injective mog22.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hQ,
      Subgroup.map_subgroupOf_eq_of_le hbQ_le, Subgroup.map_subgroupOf_eq_of_le hC]
  rw [imgC, imgC, ← Subgroup.map_commutator, h]
  exact Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.2 (q16_le_comm (Subgroup.mem_subgroupOf.1 hx))

@[expose] def tauP : Equiv.Perm (Fin 24) := permOfArr 24 tauArr tauInv tau_ok.1

theorem hasArr_tauP : HasArr tauP tauArr := hasArr_permOfArr _

theorem hasArr_tauPinv : HasArr tauP⁻¹ tauInv := hasArr_permOfArr_inv _

theorem tauP_mem : tauP ∈ mog22 :=
  mem_mog22_of_arr (mem_AutPerm_of_arr _ tau_ok.2.1) hasArr_tauP tau_ok.2.2.1 tau_ok.2.2.2.1

@[expose] def K22 : Subgroup (Equiv.Perm (Fin 24)) := mog21.map (MulAut.conj tauP).toMonoidHom

theorem K22_le : K22 ≤ mog22 := by
  rintro _ ⟨x, hx, rfl⟩
  show tauP * x * tauP⁻¹ ∈ mog22
  exact mog22.mul_mem (mog22.mul_mem tauP_mem (mog21_le_mog22 hx)) (mog22.inv_mem tauP_mem)

theorem conj_mem_mog21 {σ : Equiv.Perm (Fin 24)} {a : Array ℕ} (hσ : σ ∈ AutPerm)
    (ha : HasArr σ a) (h0 : (cArr tauInv (cArr a tauArr))[0]! = 0)
    (h1 : (cArr tauInv (cArr a tauArr))[1]! = 1) (h2 : (cArr tauInv (cArr a tauArr))[2]! = 2) :
    tauP⁻¹ * σ * tauP ∈ mog21 := by
  have hc : HasArr (tauP⁻¹ * σ * tauP) (cArr tauInv (cArr a tauArr)) := by
    rw [mul_assoc]
    exact hasArr_mul hasArr_tauPinv (hasArr_mul ha hasArr_tauP)
  have hA : tauP⁻¹ * σ * tauP ∈ AutPerm :=
    AutPerm.mul_mem (AutPerm.mul_mem (AutPerm.inv_mem tauP_mem.1.1) hσ) tauP_mem.1.1
  exact ⟨mem_mog22_of_arr hA hc h0 h1, (mem_stab_iff 2 _).2 (hc.apply_eq 2 h2)⟩

theorem hbQ_le_K22 : hbQ ≤ K22 := by
  rw [hbQ, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · refine ⟨tauP⁻¹ * hbA * tauP, conj_mem_mog21 hbA_mem.1.1 hasArr_hbA tau_ok.2.2.2.2.1
      tau_ok.2.2.2.2.2.1 tau_ok.2.2.2.2.2.2.1, ?_⟩
    show tauP * (tauP⁻¹ * hbA * tauP) * tauP⁻¹ = hbA
    group
  · refine ⟨tauP⁻¹ * hbB * tauP, conj_mem_mog21 hbB_mem.1.1 hasArr_hbB
      tau_ok.2.2.2.2.2.2.2.1 tau_ok.2.2.2.2.2.2.2.2.1 tau_ok.2.2.2.2.2.2.2.2.2, ?_⟩
    show tauP * (tauP⁻¹ * hbB * tauP) * tauP⁻¹ = hbB
    group

theorem card_K22 :
    Nat.card K22 = 20160 := by
  rw [K22, Subgroup.card_map_of_injective (MulAut.conj tauP).injective, card_mog21]

@[expose] def k22u : Equiv.Perm (Fin 24) := tauP * psi21 m21gA * tauP⁻¹

@[expose] def k22v : Equiv.Perm (Fin 24) := tauP * psi21 m21gB * tauP⁻¹

theorem K22_eq_closure :
    K22 = Subgroup.closure {k22u, k22v} := by
  rw [K22, ← map_psi21_M21nat, M21nat, MonoidHom.map_closure, MonoidHom.map_closure,
    Set.image_pair, Set.image_pair]
  rfl

theorem m21_rels : ∀ w ∈ CFSG.LieType.Multipliers.L34.rels.map (List.map fun l => (l.1.val, l.2)),
    CFSG.Sporadic.Bridge.wordProd (CFSG.Sporadic.Bridge.TwoGen.img2 m21gA m21gB) w = 1 := by
  decide +kernel

theorem k22u_mem :
    k22u ∈ mog22 :=
  K22_le (K22_eq_closure ▸ Subgroup.subset_closure (Set.mem_insert _ _))

theorem k22v_mem :
    k22v ∈ mog22 :=
  K22_le (K22_eq_closure ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

theorem wordProd_k22 :
    ∀ w ∈ CFSG.LieType.Multipliers.L34.rels.map (List.map fun l => (l.1.val, l.2)),
      CFSG.Sporadic.Bridge.wordProd (CFSG.Sporadic.Bridge.TwoGen.img2 k22u k22v) w = 1 := by
  intro w hw
  have h := CFSG.Sporadic.Bridge.map_wordProd ((MulAut.conj tauP).toMonoidHom.comp psi21)
    (CFSG.Sporadic.Bridge.TwoGen.img2 m21gA m21gB) w
  rw [m21_rels w hw, map_one] at h
  have he : (fun i => ((MulAut.conj tauP).toMonoidHom.comp psi21)
      (CFSG.Sporadic.Bridge.TwoGen.img2 m21gA m21gB i)) =
      CFSG.Sporadic.Bridge.TwoGen.img2 k22u k22v := by
    funext i
    unfold CFSG.Sporadic.Bridge.TwoGen.img2
    split_ifs <;> rfl
  rw [he] at h
  exact h.symm

@[expose] noncomputable def KC22 :
    Subgroup (MulAut W10) :=
  Subgroup.closure {rhoC10 mog22 mog22_le_mog22plus ⟨k22u, k22u_mem⟩,
    rhoC10 mog22 mog22_le_mog22plus ⟨k22v, k22v_mem⟩}

theorem KC22_eq_map :
    KC22 = (Subgroup.closure ({⟨k22u, k22u_mem⟩, ⟨k22v, k22v_mem⟩} : Set ↥mog22)).map
      (rhoC10 mog22 mog22_le_mog22plus) := by
  rw [KC22, MonoidHom.map_closure, Set.image_pair]

theorem map_subtype_K22 :
    (Subgroup.closure ({⟨k22u, k22u_mem⟩, ⟨k22v, k22v_mem⟩} : Set ↥mog22)).map mog22.subtype =
      K22 := by
  rw [MonoidHom.map_closure, Set.image_pair, K22_eq_closure]
  rfl

theorem imgC_hbQ_le_KC22 :
    imgC hbQ ≤ KC22 := by
  rw [KC22_eq_map]
  rintro _ ⟨σ, hσ, rfl⟩
  refine ⟨σ, ?_, rfl⟩
  have hσK : (σ : Equiv.Perm (Fin 24)) ∈ K22 := hbQ_le_K22 (Subgroup.mem_subgroupOf.1 hσ)
  rw [← map_subtype_K22] at hσK
  obtain ⟨τ, hτ, hτσ⟩ := hσK
  rwa [show σ = τ from Subtype.ext hτσ.symm]

theorem KC22_le :
    KC22 ≤ imgC mog22 := by
  rw [KC22, Subgroup.closure_le]
  rintro _ (rfl | rfl) <;> exact rhoC10_mem_imgC _

theorem isPSL_KC22 :
    IsPSL 3 2 2 ↥KC22 := by
  set ρ := rhoC10 mog22 mog22_le_mog22plus
  have hrel : ∀ w ∈ CFSG.LieType.Multipliers.L34.rels.map (List.map fun l => (l.1.val, l.2)),
      CFSG.Sporadic.Bridge.wordProd (CFSG.Sporadic.Bridge.TwoGen.img2 (ρ ⟨k22u, k22u_mem⟩)
        (ρ ⟨k22v, k22v_mem⟩)) w = 1 := by
    intro w hw
    have h1 := CFSG.Sporadic.Bridge.map_wordProd ρ
      (CFSG.Sporadic.Bridge.TwoGen.img2 (⟨k22u, k22u_mem⟩ : ↥mog22) ⟨k22v, k22v_mem⟩) w
    have h2 : CFSG.Sporadic.Bridge.wordProd
        (CFSG.Sporadic.Bridge.TwoGen.img2 (⟨k22u, k22u_mem⟩ : ↥mog22) ⟨k22v, k22v_mem⟩) w = 1 := by
      apply Subtype.ext
      rw [CFSG.Sporadic.Bridge.coe_wordProd]
      have he : (fun i => ((CFSG.Sporadic.Bridge.TwoGen.img2
          (⟨k22u, k22u_mem⟩ : ↥mog22) ⟨k22v, k22v_mem⟩ i : ↥mog22) : Equiv.Perm (Fin 24))) =
          CFSG.Sporadic.Bridge.TwoGen.img2 k22u k22v := by
        funext i
        unfold CFSG.Sporadic.Bridge.TwoGen.img2
        split_ifs <;> rfl
      rw [he]
      exact wordProd_k22 w hw
    rw [h2, map_one] at h1
    have he : (fun i => ρ (CFSG.Sporadic.Bridge.TwoGen.img2
        (⟨k22u, k22u_mem⟩ : ↥mog22) ⟨k22v, k22v_mem⟩ i)) =
        CFSG.Sporadic.Bridge.TwoGen.img2 (ρ ⟨k22u, k22u_mem⟩) (ρ ⟨k22v, k22v_mem⟩) := by
      funext i
      unfold CFSG.Sporadic.Bridge.TwoGen.img2
      split_ifs <;> rfl
    rw [he] at h1
    exact h1.symm
  have hcard : 20160 ≤ Nat.card ↥KC22 := by
    rw [KC22_eq_map, Subgroup.card_map_of_injective ModelType.rhoC10_mog22_injective,
      ← Subgroup.card_map_of_injective mog22.subtype_injective, map_subtype_K22, card_K22]
  exact CFSG.Quasithin.A312M23.isPSL_three_four_of_gens
    (Subgroup.subset_closure (Set.mem_insert _ _))
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)) rfl hrel hcard

theorem imgC_mono {A B : Subgroup (Equiv.Perm (Fin 24))} (h : A ≤ B) : imgC A ≤ imgC B :=
  Subgroup.map_mono fun _ hx => Subgroup.mem_subgroupOf.2 (h (Subgroup.mem_subgroupOf.1 hx))

theorem hbU0Masks_lt : ∀ m ∈ hbU0Masks, m < 2 ^ 10 := by
  decide

theorem maskOf_mem_UC {φ : MulAut W10} (hφ : φ ∈ stabSub UC) {u : ℕ} (hu : u ∈ hbU0Masks) :
    maskOf 10 (φ (toW 10 u)) ∈ hbU0Masks := by
  have h1 : φ (toW 10 u) ∈ UC := (hφ _).2 ((toW_mem_UC_iff (hbU0Masks_lt u hu)).2 hu)
  rw [← (maskOf_spec (φ (toW 10 u))).2] at h1
  exact (toW_mem_UC_iff (maskOf_spec _).1).1 h1

theorem actsBy_rho_arr {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ mog22) {a : Array ℕ}
    (ha : HasArr σ a) {c : List ℕ} (hc : matOf 10 (actC10 a) = c) :
    ActsBy (rhoC10 mog22 mog22_le_mog22plus ⟨σ, hσ⟩) c := by
  rw [← hc]
  exact actsBy_of_xorLin (xorLin_actC10 a) (rhoC10_toW mog22 mog22_le_mog22plus _ ha)

theorem card_cent_UC_le :
    Nat.card ↥((imgC mog22 ⊓ stabSub UC) ⊓ centSub UC) ≤ 16 := by
  have : Finite (MulAut W10) := finite_mulAut_z (V := W10)
  have hgen : ∀ gi : ℕ, ∃ g ∈ imgC mog22 ⊓ stabSub UC, ActsBy g (cucCols gi) := by
    intro gi
    unfold cucCols
    split_ifs
    · exact ⟨_, ⟨rhoC10_mem_imgC _, rho_hbA_mem_stabSub⟩,
        actsBy_rho_arr hbA_mem hasArr_hbA hbCols_eq.1⟩
    · exact ⟨_, ⟨rhoC10_mem_imgC _, rho_hbB_mem_stabSub⟩,
        actsBy_rho_arr hbB_mem hasArr_hbB hbCols_eq.2.1⟩
    · exact ⟨_, rho_tP_mem, actsBy_rho_arr tP_mem hasArr_tP hbCols_eq.2.2⟩
  have hlt : ∀ gi, ∀ x ∈ cucCols gi, x < 2 ^ 10 := by
    intro gi x hx
    unfold cucCols at hx
    split_ifs at hx <;> exact cuc_cols_lt x (by simp [hx])
  have hM : ∀ m, m ∈ hbU0Masks → actM hbU0Basis (actM ucD m) = m ∧ actM ucD m < 2 ^ 4 :=
    fun m hm => ucD_ok m hm
  have h := card_mul_le_of_tree (K := imgC mog22 ⊓ stabSub UC)
    (C := (imgC mog22 ⊓ stabSub UC) ⊓ centSub UC) inf_le_left
    (tupKey 10 4 ucD ucUs) (fun φ _ ψ hψ => tupKey_mul_fix ucUs fun u hu =>
      hψ.2 _ ((toW_mem_UC_iff (hbU0Masks_lt u (ucUs_mem u hu))).2 (ucUs_mem u hu)))
    cucAct (fun gi m => by
      rintro ⟨φ, hφ, rfl⟩
      obtain ⟨g, hg, hga⟩ := hgen gi
      exact ⟨g * φ, Subgroup.mul_mem _ hg hφ, tupKey_mul hga (hlt gi) hM ucUs
        fun u hu => maskOf_mem_UC hφ.2 (ucUs_mem u hu)⟩)
    ⟨1, Subgroup.one_mem _, by
      rw [tupKey_one ucUs fun u hu => hbU0Masks_lt u (ucUs_mem u hu), ucUs_start]⟩ cucTree_ok
  rw [cucTree_length, card_stab_UC.2] at h
  omega

theorem imgC_Q16P_le_cent : imgC Q16P ≤ (imgC mog22 ⊓ stabSub UC) ⊓ centSub UC := by
  have hfix : ∀ φ ∈ imgC Q16P, φ ∈ centSub UC := by
    rintro _ ⟨σ, hσ, rfl⟩ _ ⟨m, hm, rfl⟩
    obtain ⟨t, ht⟩ := mem_Q16P.1 (Subgroup.mem_subgroupOf.1 hσ)
    have hm' : m ∈ hbU0Masks := (hb_combos m (combos_lt hbU0Basis_lt m hm)).1 hm
    exact (rhoC10_toW mog22 mog22_le_mog22plus σ (ht ▸ hasArr_q16P t) m).trans
      (congrArg (toW 10) (q16_fix t t.2 m hm'))
  refine fun φ hφ => ⟨⟨imgC_mono (Q16P_le_hbQ.trans hbQ_le) hφ, ?_⟩, hfix φ hφ⟩
  exact centSub_le_stabSub UC (hfix φ hφ)

theorem card_imgC_Q16P :
    Nat.card ↥(imgC Q16P) = 16 := by
  rw [imgC, Subgroup.card_map_of_injective ModelType.rhoC10_mog22_injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Q16P_le_hbQ.trans hbQ_le)).toEquiv, card_Q16P]

theorem cent_UC_eq :
    (imgC mog22 ⊓ stabSub UC) ⊓ centSub UC = imgC Q16P := by
  have : Finite (MulAut W10) := finite_mulAut_z (V := W10)
  exact (Subgroup.eq_of_le_of_card_ge imgC_Q16P_le_cent
    (by rw [card_imgC_Q16P]; exact card_cent_UC_le)).symm

theorem card_mul_relIndex {G : Type*} [Group G] (H K : Subgroup G) :
    Nat.card ↥(H ⊓ K) * H.relIndex K = Nat.card K := by
  rw [Subgroup.relIndex, ← Subgroup.inf_subgroupOf_right,
    ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : H ⊓ K ≤ K)).toEquiv,
    Subgroup.card_mul_index]

theorem card_normalizer_imgC :
    Nat.card ↥(Subgroup.normalizer ((imgC mog22 : Subgroup (MulAut W10)) : Set (MulAut W10))) =
      887040 := by
  have hN : Subgroup.normalizer ((imgC mog22 : Subgroup (MulAut W10)) : Set (MulAut W10)) =
      (rhoC10 mog22plus le_rfl).range := by
    rw [← range_rhoC10_eq_imgC]
    exact normalizer_rhoC10_mog22
  rw [hN, ← Nat.card_congr (MonoidHom.ofInjective rhoC10_mog22plus_injective).toEquiv,
    card_mog22plus]

theorem imgC_Q16P_le
    {X : Subgroup (MulAut W10)}
    (hX : fixV X = UC) (hXN : X ≤ Subgroup.normalizer ((imgC mog22 : Subgroup (MulAut W10)) :
      Set (MulAut W10))) (hXc : Nat.card ↥X = 2 ^ 5) : imgC Q16P ≤ X := by
  have : Finite (MulAut W10) := finite_mulAut_z (V := W10)
  have hHN : imgC mog22 ≤ Subgroup.normalizer ((imgC mog22 : Subgroup (MulAut W10)) :
      Set (MulAut W10)) := Subgroup.le_normalizer
  have hrN : (imgC mog22).relIndex
      (Subgroup.normalizer ((imgC mog22 : Subgroup (MulAut W10)) : Set (MulAut W10))) = 2 := by
    have h := card_mul_relIndex (imgC mog22)
      (Subgroup.normalizer ((imgC mog22 : Subgroup (MulAut W10)) : Set (MulAut W10)))
    rw [inf_of_le_left hHN, card_imgC_mog22, card_normalizer_imgC] at h
    omega
  have hrX : (imgC mog22).relIndex X ≤ 2 := by
    have h := Subgroup.relIndex_le_of_le_right (H := imgC mog22) hXN (by rw [hrN]; norm_num)
    rwa [hrN] at h
  have hc := card_mul_relIndex (imgC mog22) X
  rw [hXc] at hc
  have hge : 16 ≤ Nat.card ↥(imgC mog22 ⊓ X) := by
    rcases Nat.lt_or_ge ((imgC mog22).relIndex X) 1 with h0 | h1
    · have h0' : (imgC mog22).relIndex X = 0 := by omega
      rw [h0'] at hc
      omega
    · nlinarith
  have hle : imgC mog22 ⊓ X ≤ imgC Q16P := by
    rw [← cent_UC_eq]
    intro φ hφ
    have hc' : φ ∈ centSub UC := by
      intro u hu
      rw [← hX] at hu
      exact hu φ hφ.2
    exact ⟨⟨hφ.1, centSub_le_stabSub UC hc'⟩, hc'⟩
  have heq : imgC mog22 ⊓ X = imgC Q16P :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_imgC_Q16P]; exact hge)
  rw [← heq]
  exact inf_le_right

theorem parab_std_of_le
    {X₀ : Subgroup (MulAut W10)} (hX : fixV X₀ = UC)
    (hQ : imgC Q16P ≤ X₀) :
    Nat.card ↥(perfectCore (imgC mog22 ⊓ stabSub (fixV X₀))) = 960 ∧
      pCoreOf 2 (perfectCore (imgC mog22 ⊓ stabSub (fixV X₀))) ≤
        ⁅X₀, perfectCore (imgC mog22 ⊓ stabSub (fixV X₀))⁆ ∧
      ∃ K : Subgroup (MulAut W10), perfectCore (imgC mog22 ⊓ stabSub (fixV X₀)) ≤ K ∧
        K ≤ imgC mog22 ∧ IsPSL 3 2 2 ↥K := by
  rw [hX, perfectCore_stab_UC]
  exact ⟨card_imgC_hbQ, pCoreOf_imgC_hbQ_le.trans
    (imgC_q16_le_comm.trans (Subgroup.commutator_mono hQ le_rfl)),
    KC22, imgC_hbQ_le_KC22, KC22_le, isPSL_KC22⟩

theorem parab_std
    {X₀ : Subgroup (MulAut W10)} (hX : fixV X₀ = UC)
    (hXN : X₀ ≤ Subgroup.normalizer ((imgC mog22 : Subgroup (MulAut W10)) : Set (MulAut W10)))
    (hXc : Nat.card ↥X₀ = 2 ^ 5) :
    Nat.card ↥(perfectCore (imgC mog22 ⊓ stabSub (fixV X₀))) = 960 ∧
      pCoreOf 2 (perfectCore (imgC mog22 ⊓ stabSub (fixV X₀))) ≤
        ⁅X₀, perfectCore (imgC mog22 ⊓ stabSub (fixV X₀))⁆ ∧
      ∃ K : Subgroup (MulAut W10), perfectCore (imgC mog22 ⊓ stabSub (fixV X₀)) ≤ K ∧
        K ≤ imgC mog22 ∧ IsPSL 3 2 2 ↥K :=
  parab_std_of_le hX (imgC_Q16P_le hX hXN hXc)

end CFSG.Quasithin.H.Code22
