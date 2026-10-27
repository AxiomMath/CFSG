module

public import CFSG.Sporadic.Schreier.J4SCommGenBase1
public import CFSG.Sporadic.Schreier.J4SOdd276Base1
public import CFSG.Sporadic.Schreier.J4SOddLocal

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

theorem rowsMatrix_xorRows (X Y : Array ℕ) :
    rowsMatrix 112 (xorRows X Y) = rowsMatrix 112 X + rowsMatrix 112 Y := by
  ext i j
  rw [Matrix.add_apply, SmallF2.rowsMatrix_apply, SmallF2.rowsMatrix_apply,
    SmallF2.rowsMatrix_apply]
  unfold xorRows
  simp only [Array.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
  rw [toVecD_xor, Pi.add_apply]

theorem add_self_vec (w : Fin 112 → ZMod 2) : w + w = 0 := by
  funext i
  rw [Pi.add_apply, Pi.zero_apply]
  generalize w i = c
  revert c
  decide

theorem vecMul_certSum {x : Fin 112 → ZMod 2} :
    ∀ L : List (Array ℕ × Array ℕ), (∀ MU ∈ L, x ᵥ* rowsMatrix 112 MU.1 = x) →
      x ᵥ* rowsMatrix 112 (certSum L) = x ᵥ* rowsMatrix 112 eRows
  | [], _ => rfl
  | (M, U) :: L, h => by
    rw [certSum, rowsMatrix_xorRows, rowsMatrix_xorRows, SmallF2.rowsMatrix_mulRows,
      Matrix.vecMul_add,
      Matrix.vecMul_add, ← Matrix.vecMul_vecMul, h (M, U) List.mem_cons_self,
      vecMul_certSum L fun MU hMU => h MU (List.mem_cons_of_mem _ hMU), add_self_vec, zero_add]

theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

theorem fixed_cert
    {x : Fin 112 → ZMod 2} (hx : ∀ MU ∈ certList, x ᵥ* rowsMatrix 112 MU.1 = x) :
    x = 0 ∨ x = toVecD 112 (tInvRows[110]?.getD 0) ∨ x = toVecD 112 (tInvRows[111]?.getD 0) ∨
      x = toVecD 112 (tInvRows[110]?.getD 0) + toVecD 112 (tInvRows[111]?.getD 0) := by
  have h1 := vecMul_certSum certList hx
  set c := x ᵥ* rowsMatrix 112 eRows with hcdef
  have hc : ∀ j : Fin 112, j.val < 110 → c j = 0 := by
    intro j hj
    rw [hcdef, Matrix.vecMul, dotProduct]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [SmallF2.rowsMatrix_apply, toVecD_apply, cert_check.2.1 r r.isLt j hj]
    simp
  have hx' : x = c ᵥ* rowsMatrix 112 tInvRows := by
    rw [← h1, Matrix.vecMul_vecMul, ← SmallF2.rowsMatrix_mulRows, cert_check.1,
      SmallF2.rowsMatrix_idRows, Matrix.vecMul_one]
  have hcs : c = Pi.single (110 : Fin 112) (c 110) + Pi.single (111 : Fin 112) (c 111) := by
    funext j
    rw [Pi.add_apply]
    by_cases hj : j.val < 110
    · have h110 : j ≠ 110 := by intro h; subst h; simp at hj
      have h111 : j ≠ 111 := by intro h; subst h; simp at hj
      rw [hc j hj, Pi.single_eq_of_ne h110, Pi.single_eq_of_ne h111, add_zero]
    · have hj' : j = 110 ∨ j = 111 := by
        have := j.isLt
        rcases Nat.lt_or_ge j.val 111 with h | h
        · left; exact Fin.ext (by simp; omega)
        · right; exact Fin.ext (by simp; omega)
      rcases hj' with rfl | rfl
      · rw [Pi.single_eq_same, Pi.single_eq_of_ne (by decide), add_zero]
      · rw [Pi.single_eq_same, Pi.single_eq_of_ne (by decide), zero_add]
  rw [hcs, Matrix.add_vecMul, Matrix.single_vecMul, Matrix.single_vecMul] at hx'
  have e110 : (rowsMatrix 112 tInvRows).row 110 = toVecD 112 (tInvRows[110]?.getD 0) := rfl
  have e111 : (rowsMatrix 112 tInvRows).row 111 = toVecD 112 (tInvRows[111]?.getD 0) := rfl
  rw [e110, e111] at hx'
  rcases zmod2_cases (c 110) with h0 | h0 <;> rcases zmod2_cases (c 111) with h1' | h1' <;>
    rw [h0, h1'] at hx' <;> simp only [zero_smul, one_smul, zero_add, add_zero] at hx'
  · exact Or.inl hx'
  · exact Or.inr (Or.inr (Or.inl hx'))
  · exact Or.inr (Or.inl hx')
  · exact Or.inr (Or.inr (Or.inr hx'))

@[expose] def commEl (l : ℕ) : J := η (commM commPairs[l]!)

theorem mem_certList {MU : Array ℕ × Array ℕ} (h : MU ∈ certList) :
    ∃ l < 10, MU.1 = (etaP (commM commPairs[l]!)).2 := by
  unfold certList at h
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 h
  exact ⟨l, List.mem_range.1 hl, rfl⟩

theorem fixed_of_commEl
    {x : Row} (hx : ∀ l < 10, commEl l • x = x) :
    ofRow x = 0 ∨ ofRow x = toVecD 112 (tInvRows[110]?.getD 0) ∨
      ofRow x = toVecD 112 (tInvRows[111]?.getD 0) ∨
      ofRow x = toVecD 112 (tInvRows[110]?.getD 0) + toVecD 112 (tInvRows[111]?.getD 0) := by
  refine fixed_cert fun MU hMU => ?_
  obtain ⟨l, hl, hMU1⟩ := mem_certList hMU
  have h1 := congrArg ofRow (hx l hl)
  rw [smul_row] at h1
  rw [hMU1]
  have hrep := (rep_etaP j4Facts.mat (commM commPairs[l]!)).2.2.2
  have e : rowsMatrix 112 (etaP (commM commPairs[l]!)).2 =
      (((commEl l)⁻¹ : J) : GL (Fin 112) (ZMod 2)) := by
    rw [← φ_apply]
    exact hrep
  rw [e]
  exact h1

theorem smul_row_eq_zero_iff (g : J) (x : Row) : ofRow (g • x) = 0 ↔ ofRow x = 0 := by
  constructor
  · intro h
    have e : x = g⁻¹ • (g • x) := by rw [inv_smul_smul]
    rw [e, smul_row, h, Matrix.zero_vecMul]
  · intro h
    rw [smul_row, h, Matrix.zero_vecMul]

theorem mem_H_of_commute_commEl
    {r : J} {q : ℕ} [Fact q.Prime] (hq : 3 < q) (hr : r ^ q = 1)
    (hc : ∀ l < 10, r * commEl l = commEl l * r) : r ∈ H := by
  classical
  set w1 : Row := toRow (toVecD 112 (tInvRows[110]?.getD 0))
  set w2 : Row := toRow (toVecD 112 (tInvRows[111]?.getD 0))
  set w3 : Row := toRow (toVecD 112 (tInvRows[110]?.getD 0) + toVecD 112 (tInvRows[111]?.getD 0))
  set T : Set Row := {x | ofRow x ≠ 0 ∧ ∀ l < 10, commEl l • x = x} with hT
  have hTsub : T ⊆ {w1, w2, w3} := by
    rintro x ⟨hx0, hx⟩
    rcases fixed_of_commEl hx with h | h | h | h
    · exact absurd h hx0
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hTf : T.Finite := (Set.toFinite {w1, w2, w3}).subset hTsub
  have hT3 : T.ncard ≤ 3 := by
    refine (Set.ncard_le_ncard hTsub (Set.toFinite _)).trans ?_
    refine (Set.ncard_insert_le _ _).trans ?_
    have := Set.ncard_insert_le w2 ({w3} : Set Row)
    rw [Set.ncard_singleton] at this
    omega
  have hrT : ∀ x ∈ T, r • x ∈ T := by
    rintro x ⟨hx0, hx⟩
    refine ⟨fun h => hx0 ((smul_row_eq_zero_iff r x).1 h), fun l hl => ?_⟩
    rw [← mul_smul, ← hc l hl, mul_smul, hx l hl]
  have hvT : v ∈ T := by
    refine ⟨fun h => ?_, fun l hl => ?_⟩
    · have h0 : toVecD 112 rootBits = toVecD 112 0 := by
        rw [toVecD_zero]
        exact h
      exact cert_check.2.2.2.2.1 (toVecD_injective cert_check.2.2.2.2.2.1 (by norm_num) h0)
    · exact H_le_stabilizer_v (N_le_H (η_mem_N _))
  have h := smul_eq_of_ncard_le_three hq hr hTf hT3 hrT hvT
  have hs : r ∈ MulAction.stabilizer J v := MulAction.mem_stabilizer_iff.2 h
  rw [stabilizer_v_eq_Hj, ← H_eq_Hj] at hs
  exact hs

theorem kgen_mem_centralizer_one
    {i : ℕ} (hi : i < 4) : kgen i ∈ Subgroup.centralizer {η 1} := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h : kgen i * η 1 * (kgen i)⁻¹ = η 1 := by rw [kgen_acts hi, gen_fix_one i hi]
  calc kgen i * η 1 = kgen i * η 1 * (kgen i)⁻¹ * kgen i := by group
    _ = η 1 * kgen i := by rw [h]

theorem S0_le_centralizer_one :
    S0 ≤ Subgroup.centralizer {η 1} := by
  rw [S0, Subgroup.closure_le]
  rintro _ (rfl | ⟨i, rfl⟩)
  · exact N_le_centralizer (η_mem_N 1) (η_mem_N 4)
  · exact kgen_mem_centralizer_one i.isLt

theorem sgen_mem_centralizer_one
    {m : ℕ} (h1 : 1 ≤ m) (h9 : m < 9) :
    sgen m ∈ Subgroup.centralizer {η 1} := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h : sgen m * η 1 * (sgen m)⁻¹ = η 1 := by rw [sgen_conj, (wPaths_check.1 m h9 h1).2]
  calc sgen m * η 1 = sgen m * η 1 * (sgen m)⁻¹ * sgen m := by group
    _ = η 1 * sgen m := by rw [h]

theorem pathApp_mem {B : Subgroup J}
    (hB : ∀ m, 1 ≤ m → m < 9 → ∀ b ∈ B, sgen m * b * (sgen m)⁻¹ ∈ B) :
    ∀ w : List ℕ, (∀ m ∈ w, 1 ≤ m ∧ m < 9) → ∀ a, η a ∈ B → η (pathApp w a) ∈ B
  | [], _, _, ha => ha
  | m :: w, hw, a, ha => by
    have hm := hw m List.mem_cons_self
    have h1 : η (app11 (sCols m) a) ∈ B := by
      rw [← sgen_conj]
      exact hB m hm.1 hm.2 _ ha
    exact pathApp_mem hB w (fun m' hm' => hw m' (List.mem_cons_of_mem _ hm')) _ h1

theorem spanOK_spec {vs : List ℕ} (h : spanOK vs = true) :
    ∀ c < 2048, ∃ m < 2048, xorSub vs m = c := by
  intro c hc
  unfold spanOK at h
  have h1 := List.all_eq_true.1 h c (List.mem_range.2 hc)
  rw [List.contains_iff_mem] at h1
  obtain ⟨m, hm, e⟩ := List.mem_map.1 h1
  exact ⟨m, List.mem_range.1 hm, e⟩

@[expose] def Wsub : Subgroup J where
  carrier := {g | ∃ a ∈ wSet, η a = g}
  one_mem' := ⟨0, List.mem_cons_self, η_zero⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a ^^^ b, wSet_check.2.2.2 a ha b hb, η_xor a b⟩
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, ha, (η_inv a).symm⟩

theorem Wsub_le_N : Wsub ≤ N := by
  rintro _ ⟨a, -, rfl⟩
  exact η_mem_N a

theorem card_le_of_list
    {B : Subgroup J} (L : List ℕ) (hL : L.Nodup) (hlt : ∀ a ∈ L, a < 2 ^ 11)
    (hB : ∀ a ∈ L, η a ∈ B) : L.length ≤ Nat.card B := by
  have hf : Function.Injective fun i : Fin L.length =>
      (⟨η (L[i.val]), hB _ (List.getElem_mem _)⟩ : B) := by
    intro i j h
    have h1 := Subtype.ext_iff.1 h
    dsimp only at h1
    have h2 := η_injOn (hlt _ (List.getElem_mem _)) (hlt _ (List.getElem_mem _)) h1
    exact Fin.ext ((List.Nodup.getElem_inj_iff hL).1 h2)
  have h := Nat.card_le_card_of_injective _ hf
  rwa [Nat.card_fin] at h

theorem card_Wsub :
    16 ≤ Nat.card Wsub := by
  have h := card_le_of_list (B := Wsub) wSet wSet_check.2.1 wSet_check.2.2.1
    fun a ha => ⟨a, ha, rfl⟩
  rwa [wSet_check.1] at h

theorem oddCore_centralizer_η1 :
    CFSG.oddCore (Subgroup.centralizer ({η 1} : Set J)) = ⊥ := by
  have ht : η 1 ∈ N := η_mem_N 1
  set C := Subgroup.centralizer ({η 1} : Set J) with hC
  set R := oddCoreImage C with hR
  apply oddCore_eq_bot_of_oddCoreImage
  have hRodd : Odd (Nat.card R) := odd_card_oddCoreImage C
  have hHt : Nat.card (H ⊓ C : Subgroup J) * 1771 = Nat.card H :=
    card_H_inf_centralizer ht QT_unique_J4_local_normal_module_irreducible.2.2.2.1
  have hdvd := card_oddCoreImage_mul_dvd ht
  have hHt' : Nat.card (H ⊓ C : Subgroup J) = 283115520 := by rw [card_H] at hHt; omega
  rw [hHt', card_J j4Facts, mul_comm] at hdvd
  have hRM : Nat.card R ∣ [7, 11, 11, 11, 23, 29, 31, 37, 43].prod := by
    have h5 := Nat.dvd_div_of_mul_dvd hdvd
    have e : 86775571046077562880 / 283115520 = [7, 11, 11, 11, 23, 29, 31, 37, 43].prod := by
      norm_num
    rwa [e] at h5
  have hN2 : ∀ a ∈ N, a * a = 1 := fun a ha => by
    obtain ⟨i, -, rfl⟩ := exists_η_eq ha
    exact η_mul_self i
  have hS0R : ∀ s ∈ S0, ∀ r ∈ R, s * r * s⁻¹ ∈ R := fun s hs r hr =>
    oddCoreImage_conj C (S0_le_centralizer_one hs) hr
  have hS02 : IsPGroup 2 S0 := IsPGroup.of_card card_S0
  have hexcl : ∀ q ∈ [7, 23, 29, 31, 37, 43], ¬ q ∣ Nat.card R := by
    intro q hq hdq
    have hq' : q = 7 ∨ q = 23 ∨ q = 29 ∨ q = 31 ∨ q = 37 ∨ q = 43 := by simpa using hq
    have hqp : q.Prime := by rcases hq' with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
    have : Fact q.Prime := ⟨hqp⟩
    have hq3 : 3 < q := by omega
    have hR0 : Nat.card R ≠ 0 := Nat.card_pos.ne'
    obtain ⟨P, hPR, hPp, hPc, hPS⟩ := exists_invariant_sylow hS02 hRodd hS0R q
    have hv1 : (Nat.card R).factorization q = 1 := by
      have hpos := hqp.factorization_pos_of_dvd hR0 hdq
      by_contra hne
      have h2 : q ^ 2 ∣ Nat.card R := (hqp.pow_dvd_iff_le_factorization hR0).2 (by omega)
      have h3 := h2.trans hRM
      revert h3
      rcases hq' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hPq : Nat.card P = q := by rw [hPc, hv1, pow_one]
    have hE := card_le_two_pow_mul_card_centralizer N_comm hN2 (by omega : q ≠ 2) hPp
      (fun n hn x hx => hPS n (N_le_S0 hn) x hx) (m := 1) (by rw [hPq, pow_one])
    rw [pow_one] at hE
    set E := N ⊓ Subgroup.centralizer (P : Set J) with hEdef
    have hEN : E ≤ N := inf_le_left
    have hES : ∀ s ∈ S0, ∀ b ∈ E, s * b * s⁻¹ ∈ E := fun s hs b hb =>
      conj_mem_inf_centralizer (fun n hn => conj_mem_N_of_mem_H s (S0_le_H hs) n hn)
        (fun x hx => by
          have := hPS s⁻¹ (S0.inv_mem hs) x hx
          rwa [inv_inv] at this) hb
    have hmE : ∀ l < 10, commEl l ∈ E := by
      intro l hl
      have hlt : l < commPairs.length := by rw [cert_check.2.2.2.2.2.2.2]; exact hl
      have hp := cert_check.2.2.2.1 commPairs[l]! (by
        rw [getElem!_pos commPairs l hlt]
        exact List.getElem_mem _)
      have e : commEl l = η (commPairs[l]!).1 *
          (kgen (commPairs[l]!).2 * η (commPairs[l]!).1 * (kgen (commPairs[l]!).2)⁻¹) := by
        rw [commEl, commM, η_xor, kgen_acts hp.2]
      rw [e]
      have hk : kgen (commPairs[l]!).2 ∈ S0 := kgen_mem_S0 ⟨_, hp.2⟩
      by_cases h1 : η (commPairs[l]!).1 ∈ E
      · exact E.mul_mem h1 (hES _ hk _ h1)
      · refine mul_mem_of_index_le_two hEN hE (η_mem_N _)
          (conj_mem_N_of_mem_H _ (S0_le_H hk) _ (η_mem_N _)) h1 fun h2 => h1 ?_
        have h3 := hES _ (S0.inv_mem hk) _ h2
        rwa [show (kgen (commPairs[l]!).2)⁻¹ * (kgen (commPairs[l]!).2 * η (commPairs[l]!).1 *
          (kgen (commPairs[l]!).2)⁻¹) * (kgen (commPairs[l]!).2)⁻¹⁻¹ = η (commPairs[l]!).1 by
          group] at h3
    have hPne : P ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hPq
      exact hqp.one_lt.ne hPq
    obtain ⟨⟨r, hrP⟩, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hPne
    have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
    have hrq : r ^ q = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, ← hPq]
      exact Subgroup.orderOf_dvd_natCard P hrP
    have hrH := mem_H_of_commute_commEl hq3 hrq fun l hl =>
      Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 (hmE l hl)).2 r hrP
    have hrRH : r ∈ R ⊓ H := Subgroup.mem_inf.2 ⟨hPR hrP, hrH⟩
    rw [oddCoreImage_inf_H ht] at hrRH
    exact hr1' hrRH
  have hR11 : Nat.card R ∣ [11, 11, 11].prod := by
    have hc : ∀ q ∈ [7, 23, 29, 31, 37, 43], Nat.Coprime (Nat.card R) q := by
      intro q hq
      have hq' : q = 7 ∨ q = 23 ∨ q = 29 ∨ q = 31 ∨ q = 37 ∨ q = 43 := by simpa using hq
      have hqp : q.Prime := by rcases hq' with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
      exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hqp).2 (hexcl q hq))
    have hcop : Nat.Coprime (Nat.card R) (7 * 23 * 29 * 31 * 37 * 43) := by
      refine Nat.Coprime.mul_right (Nat.Coprime.mul_right (Nat.Coprime.mul_right
        (Nat.Coprime.mul_right (Nat.Coprime.mul_right ?_ ?_) ?_) ?_) ?_) ?_ <;>
        exact hc _ (by simp)
    have e : [7, 11, 11, 11, 23, 29, 31, 37, 43].prod =
        [11, 11, 11].prod * (7 * 23 * 29 * 31 * 37 * 43) := by norm_num
    rw [e] at hRM
    exact hcop.dvd_of_dvd_mul_right hRM
  have hcN := card_le_two_pow_length_mul_card_centralizer N_comm hN2 hRodd
    (N_conj_oddCoreImage ht) (L := [11, 11, 11]) (by decide) hR11
  set B := N ⊓ Subgroup.centralizer (R : Set J) with hBdef
  rw [card_N] at hcN
  have hB8 : 256 ≤ Nat.card B := by
    norm_num at hcN
    omega
  have hW := card_Wsub
  obtain ⟨w, hwW, hwB, hw1⟩ := exists_mem_inf_ne_one (inf_le_left : B ≤ N) Wsub_le_N N_comm
    (by rw [card_N]; nlinarith)
  obtain ⟨a, ha, rfl⟩ := hwW
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hw1 η_zero
  have hap : a ∈ wPaths.map Prod.fst := by
    rcases List.mem_cons.1 ha with h | h
    · exact absurd h ha0
    · exact h
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hap
  have hpc := wPaths_check.2 p hp
  have hBs : ∀ m, 1 ≤ m → m < 9 → ∀ b ∈ B, sgen m * b * (sgen m)⁻¹ ∈ B := fun m h1 h9 b hb =>
    conj_mem_centralizer_oddCoreImage
      (fun n hn => conj_mem_N_of_mem_H _ (K_le_H (sgen_mem_K m)) n hn)
      (sgen_mem_centralizer_one h1 h9) hb
  have hvecs : ∀ v ∈ pathVecs p, η v ∈ B := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
    exact pathApp_mem hBs w (hpc.1 w hw) _ hwB
  have hall : ∀ c < 2048, η c ∈ B := fun c hc => by
    obtain ⟨m, -, e⟩ := spanOK_spec hpc.2 c hc
    rw [← e]
    exact η_xorSub_mem _ hvecs m
  have hNB : N ≤ B := fun n hn => by
    obtain ⟨c, hc, rfl⟩ := exists_η_eq hn
    exact hall c hc
  exact oddCoreImage_eq_bot_of_le ht (hNB.trans inf_le_right)

theorem CTU_J4_local_1771_orbit_involution_centralizer_odd_core :
    ∀ t : J, (∃ g : J, ∃ k ∈ K, t = g⁻¹ * (k⁻¹ * η 1 * k) * g) →
      orderOf t = 2 ∧ CFSG.oddCore (Subgroup.centralizer ({t} : Set J)) = ⊥ := by
  intro t ht
  have hc := isConj_of_orbit ht
  exact ⟨(orderOf_of_isConj hc).trans (orderOf_η (by norm_num) (by norm_num)),
    FischerOddCore.oddCore_centralizer_eq_bot_of_isConj hc oddCore_centralizer_η1⟩

theorem CTU_J4_full_group_local_1771_orbit_involution_odd_core
    {X : Type*} [Group X] [Finite X]
    (hF : IsSimpleGroup (CFSG.generalizedFitting X))
    (hnab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a)
    (ψ : CFSG.generalizedFitting X ≃* J) (t : CFSG.generalizedFitting X)
    (ht : ∃ g : J, ∃ k ∈ K, ψ t = g⁻¹ * (k⁻¹ * η 1 * k) * g) :
    orderOf (t : X) = 2 ∧ CFSG.oddCore (Subgroup.centralizer ({(t : X)} : Set X)) = ⊥ := by
  have h := @full_group_of_local_conj X J _ _ (Subgroup.toGroup J) hF hnab ψ N
    CTU_J4_pointwise_local_binary_subgroup_automorphism_kernel_is_two_group.1 N_comm K (η 1)
    (fun k hk => conj_inv_mem_N hk (η_mem_N 1))
    CTU_J4_local_1771_orbit_involution_centralizer_odd_core t ht
  exact h

end CFSG.Sporadic.J4Schreier
