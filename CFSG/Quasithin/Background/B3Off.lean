module

public import CFSG.Quasithin.Background.B3Vec
public import CFSG.Quasithin.Background.B3Cert
public import CFSG.Quasithin.Background.B1Basic

public section

namespace CFSG.Quasithin.B3

variable {n : ℕ}

theorem act_mk (k : Mod) (g : Gp n) (w : ↥(k.W n)) :
    Mod.act n k g (QuotientGroup.mk w) =
      QuotientGroup.mk ⟨permAct n g w, k.isInv_W n g w w.2⟩ := rfl

theorem act_trivial_imp (k : Mod) (g : Gp n) (h : Mod.act n k g = 1) (w : U n) (hw : w ∈ k.W n) :
    permAct n g w * w⁻¹ ∈ k.N n := by
  have h1 := congrArg (fun f : MulAut (k.V n) => f (QuotientGroup.mk ⟨w, hw⟩)) h
  simp only [MulAut.one_apply] at h1
  rw [act_mk] at h1
  have h2 := QuotientGroup.eq.1 h1
  have h3 : (⟨permAct n g w, k.isInv_W n g w hw⟩ : ↥(k.W n))⁻¹ * ⟨w, hw⟩ ∈
      (k.N n).subgroupOf (k.W n) := h2
  rw [Subgroup.mem_subgroupOf] at h3
  simpa [mul_comm] using (k.N n).inv_mem h3

@[expose] def pair (i j : Fin n) : U n := ⟨fun x => if x = i ∨ x = j then 1 else 0⟩

theorem pair_mem_U0 {i j : Fin n} (hij : i ≠ j) : pair i j ∈ U0 n := by
  show wt n (pair i j) = 1
  have h2 : wt n (pair i j) = Multiplicative.ofAdd (∑ x, (pair i j).val x) := rfl
  rw [h2]
  have h3 : ∑ x, (pair i j).val x = 0 := by
    simp only [pair]
    rw [Finset.sum_boole]
    have : (Finset.univ.filter (fun x : Fin n => x = i ∨ x = j)) = {i, j} := by
      ext x; simp
    rw [this, Finset.card_pair hij]
    decide
  rw [h3]
  rfl

theorem pair_mem_W (k : Mod) {i j : Fin n} (hij : i ≠ j) : pair i j ∈ k.W n := by
  cases k
  · exact Subgroup.mem_top _
  · exact pair_mem_U0 hij
  · exact Subgroup.mem_top _
  · exact pair_mem_U0 hij

theorem permAct_pair (σ : Gp n) (i j : Fin n) : permAct n σ (pair i j) = pair (σ i) (σ j) := by
  ext x
  rw [permAct_val]
  simp only [pair]
  simp only [Equiv.symm_apply_eq]

theorem pair_inv (i j : Fin n) : (pair i j)⁻¹ = pair i j := by
  ext x
  simp only [U.val_inv, pair]
  split_ifs <;> decide

theorem exists_fresh (hn : 5 ≤ n) (a b c d : Fin n) :
    ∃ x : Fin n, x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ x ≠ d := by
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {a, b, c, d} := by
    intro x _
    by_cases h1 : x = a
    · simp [h1]
    by_cases h2 : x = b
    · simp [h2]
    by_cases h3 : x = c
    · simp [h3]
    simp [hcon x h1 h2 h3]
  have h4 := Finset.card_le_card hsub
  have h5 : ({a, b, c, d} : Finset (Fin n)).card ≤ 4 := Finset.card_le_four
  simp only [Finset.card_univ, Fintype.card_fin] at h4
  omega

theorem act_moves (hn : 5 ≤ n) (k : Mod) (g : Gp n) (hg : Mod.act n k g = 1) (i j : Fin n)
    (hij : i ≠ j) : g i = i ∨ g i = j := by
  have h := act_trivial_imp k g hg (pair i j) (pair_mem_W k hij)
  rw [permAct_pair, pair_inv] at h
  have h1 : pair (g i) (g j) * pair i j = 1 := by
    cases k
    · exact Subgroup.mem_bot.1 h
    · exact Subgroup.mem_bot.1 h
    · rcases (mem_Esub_iff _).1 h with h | h
      · exact h
      · exfalso
        obtain ⟨x, hx1, hx2, hx3, hx4⟩ := exists_fresh hn (g i) (g j) i j
        have := congrArg (fun w : U n => w.val x) h
        simp [pair, eVec, hx1, hx2, hx3, hx4] at this
    · rcases (mem_Esub_iff _).1 h with h | h
      · exact h
      · exfalso
        obtain ⟨x, hx1, hx2, hx3, hx4⟩ := exists_fresh hn (g i) (g j) i j
        have := congrArg (fun w : U n => w.val x) h
        simp [pair, eVec, hx1, hx2, hx3, hx4] at this
  have h2 := congrArg (fun w : U n => w.val (g i)) h1
  by_contra hc
  push Not at hc
  simp [pair, hc.1, hc.2] at h2

theorem act_injective (hn : 5 ≤ n) (k : Mod) : Function.Injective (Mod.act n k) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  ext i
  obtain ⟨j, hj, -, -, -⟩ := exists_fresh hn i i i i
  obtain ⟨j', hj', hjj'⟩ : ∃ j' : Fin n, j' ≠ i ∧ j' ≠ j := by
    obtain ⟨x, hx1, hx2, -, -⟩ := exists_fresh hn i j i j
    exact ⟨x, hx1, hx2⟩
  have h1 := act_moves hn k g hg i j hj.symm
  have h2 := act_moves hn k g hg i j' hj'.symm
  simp only [Equiv.Perm.coe_one, id_eq]
  rcases h1 with h1 | h1
  · rw [h1]
  · rcases h2 with h2 | h2
    · rw [h2]
    · exact absurd (h1.symm.trans h2) hjj'.symm

@[expose] def IsOffG (n : ℕ) (k : Mod) (A : Subgroup (Gp n)) : Prop :=
  IsFFStarOffender ((⊤ : Subgroup (Gp n)).map (Mod.act n k)) (A.map (Mod.act n k))

theorem map_cj (k : Mod) (g : Gp n) (A : Subgroup (Gp n)) :
    (cj g A).map (Mod.act n k) = B1.conjAut (Mod.act n k g) (A.map (Mod.act n k)) := by
  ext y
  rw [B1.mem_conjAut]
  simp only [Subgroup.mem_map, mem_cj]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨g⁻¹ * x * g, hx, by simp [map_mul]⟩
  · rintro ⟨a, ha, h⟩
    refine ⟨g * a * g⁻¹, ?_, ?_⟩
    · simpa [mul_assoc] using ha
    · have h' : Mod.act n k a = (Mod.act n k g)⁻¹ * y * Mod.act n k g := h
      simp only [map_mul, map_inv, h']
      simp [mul_assoc]

theorem IsOffG.cj {k : Mod} {A : Subgroup (Gp n)} (h : IsOffG n k A) (g : Gp n) :
    IsOffG n k (cj g A) := by
  unfold IsOffG at *
  rw [map_cj]
  exact B1.isFFStarOffender_conjAut h (Subgroup.mem_map_of_mem _ (Subgroup.mem_top g))

theorem cj_cj_inv (g : Gp n) (A : Subgroup (Gp n)) : cj g (cj g⁻¹ A) = A := by
  ext x
  simp only [mem_cj]
  simp [mul_assoc]

theorem isOffG_cj_iff {k : Mod} {A : Subgroup (Gp n)} (g : Gp n) :
    IsOffG n k (cj g A) ↔ IsOffG n k A := by
  refine ⟨fun h => ?_, fun h => h.cj g⟩
  have := h.cj g⁻¹
  have e : cj g⁻¹ (cj g A) = A := by
    have := cj_cj_inv g⁻¹ A
    simpa using this
  rwa [e] at this

@[expose] noncomputable def cN (n : ℕ) (k : Mod) : ℕ := Nat.card ↥(k.N n ⊓ k.W n)

theorem cN_pos (k : Mod) : 0 < cN n k := Nat.card_pos

@[expose] def Fval (n : ℕ) (k : Mod) (A : List Tab) : ℕ := A.length * cntF n k A

@[expose] def offOK (n : ℕ) (k : Mod) (D : List (List Tab)) (A : List Tab) : Bool :=
  !(A.length == 1) && D.all (fun B =>
    !(B.all (fun t => A.contains t)) || decide (Fval n k B ≤ Fval n k A))

theorem subOf_eq {X : List Tab} (hX : subOK n X = true) {K : Subgroup (Gp n)}
    (hK : ∀ x : Gp n, x ∈ K ↔ tab x ∈ X) : K = subOf n X := by
  ext x
  rw [hK, mem_subOf hX]

theorem fval_eq (hn : 5 ≤ n) (k : Mod) {X : List Tab} (hX : subOK n X = true)
    {K : Subgroup (Gp n)} (hK : ∀ x : Gp n, x ∈ K ↔ tab x ∈ X) :
    Nat.card (K.map (Mod.act n k)) * Nat.card (fixV (K.map (Mod.act n k))) * cN n k =
      Fval n k X := by
  have h1 : Nat.card (K.map (Mod.act n k)) = X.length := by
    rw [Subgroup.card_map_of_injective (act_injective hn k), subOf_eq hX hK, card_subOf hX]
  have h2 := card_fix_cnt k K X (subOK_spec hX).1 hK
  rw [h1, mul_assoc]
  unfold Fval cN
  rw [h2]

theorem subOf_comm {A : List Tab} (hA : subOK n A = true)
    (hc : ∀ a ∈ A, ∀ b ∈ A, mulT a b = mulT b a) :
    ∀ x ∈ subOf n A, ∀ y ∈ subOf n A, x * y = y * x := by
  intro x hx y hy
  rw [mem_subOf hA] at hx hy
  apply tab_injective
  rw [tab_mul, tab_mul]
  exact hc _ hx _ hy

theorem subOf_sq {A : List Tab} (hA : subOK n A = true) (hs : ∀ a ∈ A, mulT a a = idT n) :
    ∀ x ∈ subOf n A, x * x = 1 := by
  intro x hx
  rw [mem_subOf hA] at hx
  apply tab_injective
  rw [tab_mul, tab_one]
  exact hs _ hx

theorem isOffG_iff_offOK (hn : 5 ≤ n) (k : Mod) {T : List Tab} {D : List (List Tab)}
    (hT : subOK n T = true) (hD : chkEA n T D = true) {A : List Tab} (hA : A ∈ D) :
    IsOffG n k (subOf n A) ↔ offOK n k D A = true := by
  obtain ⟨-, hmem, -⟩ := chkEA_spec hD
  obtain ⟨hAok, hAT, hAcomm, hAsq⟩ := hmem A hA
  have hAv := (subOK_spec hAok).1
  have hid : idT n ∈ A := (subOK_spec hAok).2.1
  constructor
  · intro h
    simp only [offOK, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, List.all_eq_true,
      Bool.or_eq_true, decide_eq_true_eq]
    refine ⟨?_, fun B hB => ?_⟩
    · intro hlen
      apply h.2.1
      have hall : ∀ t ∈ A, t = idT n := by
        intro t ht
        obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 hlen
        rw [ha] at ht hid
        simp only [List.mem_singleton] at ht hid
        rw [ht, hid]
      have : subOf n A = ⊥ := by
        ext x
        rw [mem_subOf hAok, Subgroup.mem_bot]
        constructor
        · intro hx
          apply tab_injective
          rw [hall _ hx, tab_one]
        · intro hx
          rw [hx, tab_one]
          exact hid
      rw [this, Subgroup.map_bot]
    · by_cases hsub : B.all (fun t => A.contains t) = true
      · right
        obtain ⟨hBok, -, -, -⟩ := hmem B hB
        have hle : subOf n B ≤ subOf n A := by
          intro x hx
          rw [mem_subOf hBok] at hx
          rw [mem_subOf hAok]
          exact List.contains_iff_mem.1 (List.all_eq_true.1 hsub _ hx)
        have h1 := h.2.2.2 ((subOf n B).map (Mod.act n k)) (Subgroup.map_mono hle)
        have e1 := fval_eq hn k hBok (K := subOf n B) (fun x => mem_subOf hBok)
        have e2 := fval_eq hn k hAok (K := subOf n A) (fun x => mem_subOf hAok)
        rw [← e1, ← e2]
        exact Nat.mul_le_mul_right _ h1
      · left
        simpa using hsub
  · intro h
    simp only [offOK, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, List.all_eq_true,
      Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨hlen, hall⟩ := h
    refine ⟨Subgroup.map_mono le_top, ?_, ⟨?_, ?_⟩, ?_⟩
    · obtain ⟨t, htA, htne⟩ : ∃ t ∈ A, t ≠ idT n := by
        by_contra hcon
        push Not at hcon
        have hnd := (subOK_spec hAok).2.2.2.2
        have hsub : A ⊆ [idT n] := fun t ht => by simp [hcon t ht]
        have h1 := (hnd.subperm hsub).length_le
        have h2 : 0 < A.length := List.length_pos_of_mem hid
        simp only [List.length_singleton] at h1
        omega
      obtain ⟨x, rfl⟩ := exists_tab_eq (hAv t htA)
      have hx : x ∈ subOf n A := (mem_subOf hAok).2 htA
      have hx1 : x ≠ 1 := fun h => htne (by rw [h, tab_one])
      have hx2 : Mod.act n k x ≠ 1 := fun h' =>
        hx1 (act_injective hn k (h'.trans (map_one _).symm))
      intro hbot
      have h3 : Mod.act n k x ∈ (subOf n A).map (Mod.act n k) := Subgroup.mem_map_of_mem _ hx
      rw [hbot, Subgroup.mem_bot] at h3
      exact hx2 h3
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, subOf_comm hAok hAcomm x hx y hy]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, pow_two, subOf_sq hAok hAsq x hx, map_one]
    · intro B' hB'
      let B : Subgroup (Gp n) := subOf n A ⊓ B'.comap (Mod.act n k)
      have hBmap : B.map (Mod.act n k) = B' := by
        ext y
        constructor
        · rintro ⟨x, ⟨_, hx2⟩, rfl⟩
          exact hx2
        · intro hy
          obtain ⟨x, hx, hxy⟩ := hB' hy
          exact ⟨x, ⟨hx, by show Mod.act n k x ∈ B'; rw [hxy]; exact hy⟩, hxy⟩
      obtain ⟨C, hC, hCok, hBC⟩ := exists_mem_D hT hD B
        (fun x hx => hAT _ ((mem_subOf hAok).1 hx.1))
        (fun a ha b hb => subOf_comm hAok hAcomm a ha.1 b hb.1)
        (fun a ha => subOf_sq hAok hAsq a ha.1)
      have hCsub : C.all (fun t => A.contains t) = true := by
        simp only [List.all_eq_true, List.contains_iff_mem]
        intro t ht
        obtain ⟨σ, rfl⟩ := exists_tab_eq ((subOK_spec hCok).1 t ht)
        exact (mem_subOf hAok).1 ((hBC σ).2 ht).1
      have hFle : Fval n k C ≤ Fval n k A := by
        rcases hall C hC with h | h
        · rw [hCsub] at h
          exact absurd h (by simp)
        · exact h
      have e1 := fval_eq hn k hCok (K := B) hBC
      have e2 := fval_eq hn k hAok (K := subOf n A) (fun x => mem_subOf hAok)
      rw [hBmap] at e1
      refine Nat.le_of_mul_le_mul_right ?_ (cN_pos (n := n) k)
      calc _ = Fval n k C := e1
        _ ≤ Fval n k A := hFle
        _ = _ := e2.symm

end CFSG.Quasithin.B3
