module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNPGL27Facts

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NFF7.C914

open CFSG.QuasithinUnique.A6Facts CFSG.Quasithin CFSG.Open Subgroup

structure RowOK (r : Row) : Prop where
  K_sub : ∀ k ∈ r.K, k ∈ gLit
  K_one : cid ∈ r.K
  Y_one : cid ∈ r.Y
  U_one : cid ∈ r.U
  M_one : cid ∈ r.M
  K_mul : ∀ c ∈ r.K, ∀ d ∈ r.K, Core.cmul c d ∈ r.K
  Y_mul : ∀ c ∈ r.Y, ∀ d ∈ r.Y, Core.cmul c d ∈ r.Y
  U_mul : ∀ c ∈ r.U, ∀ d ∈ r.U, Core.cmul c d ∈ r.U
  M_mul : ∀ c ∈ r.M, ∀ d ∈ r.M, Core.cmul c d ∈ r.M
  Y_sub : ∀ y ∈ r.Y, y ∈ r.K
  U_sub : ∀ u ∈ r.U, u ∈ r.K
  M_sub : ∀ m ∈ r.M, m ∈ r.K
  U_norm : ∀ k ∈ r.K, ∀ u ∈ r.U, ∃ u' ∈ r.U, Core.cmul k u = Core.cmul u' k
  M_norm : ∀ k ∈ r.K, ∀ m ∈ r.M, ∃ m' ∈ r.M, Core.cmul k m = Core.cmul m' k
  U_sq : ∀ u ∈ r.U, Core.cmul u u = cid
  M_cube : ∀ m ∈ r.M, Core.cmul (Core.cmul m m) m ∈ r.U
  K_sq : ∀ k ∈ r.K, Core.cmul k k ∈ r.M
  Y_cube : ∀ y ∈ r.Y, Core.cmul (Core.cmul y y) y = cid
  Y_length : r.Y.length = 3
  Y_nodup : r.Y.Nodup
  K_nodup : r.K.Nodup
  KT_length : (r.K.filter fun k => decide (k ∈ tLit)).length * 3 = r.K.length
  K_nine : ¬ 9 ∣ r.K.length

variable {X : Type} [Group X] [Finite X] {φ : X →* Equiv.Perm (Fin 8)} {Tb : Subgroup X}

@[expose] def kSub (φ : X →* Equiv.Perm (Fin 8)) {r : Row} (h : RowOK r) : Subgroup X :=
  subL φ r.K h.K_one h.K_mul

@[expose] def ySub (φ : X →* Equiv.Perm (Fin 8)) {r : Row} (h : RowOK r) : Subgroup X :=
  subL φ r.Y h.Y_one h.Y_mul

@[expose] def uSub (φ : X →* Equiv.Perm (Fin 8)) {r : Row} (h : RowOK r) : Subgroup X :=
  subL φ r.U h.U_one h.U_mul

@[expose] def mSub (φ : X →* Equiv.Perm (Fin 8)) {r : Row} (h : RowOK r) : Subgroup X :=
  subL φ r.M h.M_one h.M_mul

theorem mem_kSub {r : Row} {h : RowOK r} {x : X} : x ∈ kSub φ h ↔ codeN 8 (φ x) ∈ r.K :=
  Iff.rfl

theorem oTwoPTwo_kSub (hφ : IsF7Emb φ) {r : Row} (h : RowOK r) :
    E1.oTwoPTwo ↥(kSub φ h) 3 = ⊤ := by
  refine oTwoPTwo_eq_top_of (U := uSub φ h) (M := mSub φ h) (fun k hk u hu => ?_)
    (fun k hk m hm => ?_) (fun u hu => hφ.sq_of_code (h.U_sq _ hu)) (fun m hm => ?_)
    (fun k hk => ?_)
  · obtain ⟨u', hu', he⟩ := h.U_norm _ hk _ hu
    obtain ⟨u'', rfl⟩ := hφ.surj u' (h.K_sub _ (h.U_sub _ hu'))
    rw [hφ.mul_eq_mul (b := u) (c := u'') (d := k) he, mul_inv_cancel_right]
    exact hu'
  · obtain ⟨m', hm', he⟩ := h.M_norm _ hk _ hm
    obtain ⟨m'', rfl⟩ := hφ.surj m' (h.K_sub _ (h.M_sub _ hm'))
    rw [hφ.mul_eq_mul (b := m) (c := m'') (d := k) he, mul_inv_cancel_right]
    exact hm'
  · change codeN 8 (φ (m ^ 3)) ∈ r.U
    rw [pow_succ, pow_two, code_mul, code_mul]
    exact h.M_cube _ hm
  · change codeN 8 (φ (k ^ 2)) ∈ r.M
    rw [pow_two, code_mul]
    exact h.K_sq _ hk

theorem card_kSub (hφ : IsF7Emb φ) {r : Row} (h : RowOK r) :
    Nat.card (kSub φ h) = r.K.length :=
  hφ.card_eq (fun _ => Iff.rfl) h.K_sub h.K_nodup

theorem card_ySub (hφ : IsF7Emb φ) {r : Row} (h : RowOK r) : Nat.card (ySub φ h) = 3 := by
  rw [hφ.card_eq (fun _ => Iff.rfl) (fun y hy => h.K_sub _ (h.Y_sub y hy)) h.Y_nodup, h.Y_length]

theorem card_kSub_inf (hφ : IsF7Model φ Tb) {r : Row} (h : RowOK r) :
    Nat.card (kSub φ h ⊓ Tb : Subgroup X) = (r.K.filter fun k => decide (k ∈ tLit)).length := by
  refine hφ.card_eq (fun x => ?_) (fun c hc => h.K_sub _ (List.mem_filter.1 hc).1)
    (h.K_nodup.filter _)
  rw [mem_inf, mem_kSub, hφ.memT, List.mem_filter, decide_eq_true_iff]

theorem twoPTwoIrred_kSub (hφ : IsF7Model φ Tb) (hTb : IsSylowIn 2 Tb ⊤) {r : Row}
    (h : RowOK r) : TwoPTwoIrred (kSub φ h) (kSub φ h ⊓ Tb) (ySub φ h) 3 := by
  have hK := card_kSub hφ.toIsF7Emb h
  have hKT := card_kSub_inf hφ h
  have hY := card_ySub hφ.toIsF7Emb h
  have hKT3 := h.KT_length
  have hK9 := h.K_nine
  refine ⟨⟨Nat.prime_three, by decide, oTwoPTwo_kSub hφ.toIsF7Emb h, ⟨inf_le_left,
    hTb.isPGroup.to_le inf_le_right, ?_⟩, ⟨fun y hy => h.Y_sub _ hy,
    fun y => ⟨1, Subtype.ext ?_⟩, ?_⟩⟩, irredOnFrattiniQuot_of_card_prime Nat.prime_three hY⟩
  · have hr := relIndex_mul_card (kSub φ h ⊓ Tb) (kSub φ h)
    rw [inf_right_comm, inf_idem, hKT, hK, ← hKT3] at hr
    have hpos : 0 < (r.K.filter fun k => decide (k ∈ tLit)).length := by
      have := List.length_pos_of_mem h.K_one
      omega
    have h3 : (kSub φ h ⊓ Tb).relIndex (kSub φ h) = 3 :=
      Nat.eq_of_mul_eq_mul_right hpos (hr.trans (mul_comm _ _))
    rw [h3]
    decide
  · simpa using hφ.cube_of_code (h.Y_cube _ y.2)
  · have hr := relIndex_mul_card (ySub φ h) (kSub φ h)
    have hYK : ySub φ h ⊓ kSub φ h = ySub φ h := inf_eq_left.2 fun y hy => h.Y_sub _ hy
    rw [hYK, hY, hK] at hr
    intro h3
    apply hK9
    rw [← hr]
    exact Nat.mul_dvd_mul_right h3 3

omit [Finite X] in
theorem mem_normalizer_of_code (hφ : IsF7Emb φ) {H : Subgroup X} {l : List (List ℕ)}
    (hH : ∀ x, x ∈ H ↔ codeN 8 (φ x) ∈ l) (hl : ∀ c ∈ l, c ∈ gLit) {v : X}
    (h1 : ∀ c ∈ l, ∃ c' ∈ l, Core.cmul (codeN 8 (φ v)) c = Core.cmul c' (codeN 8 (φ v)))
    (h2 : ∀ c ∈ l, ∃ c' ∈ l, Core.cmul c (codeN 8 (φ v)) = Core.cmul (codeN 8 (φ v)) c') :
    v ∈ normalizer (H : Set X) := by
  rw [mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    obtain ⟨c', hc', he⟩ := h1 _ ((hH g).1 hg)
    obtain ⟨g', rfl⟩ := hφ.surj c' (hl c' hc')
    rw [hφ.mul_eq_mul (b := g) (c := g') (d := v) he, mul_inv_cancel_right]
    exact (hH g').2 hc'
  · intro hg
    obtain ⟨c', hc', he⟩ := h2 _ ((hH _).1 hg)
    obtain ⟨g', rfl⟩ := hφ.surj c' (hl c' hc')
    have e : v * g * v⁻¹ * v = v * g' := hφ.mul_eq_mul he
    rw [inv_mul_cancel_right] at e
    rw [mul_left_cancel e]
    exact (hH g').2 hc'

theorem not_mem_pCoreOf_two {K : Subgroup X} {v k u : X} (hk : k ∈ K) (hu : k * v = u * k)
    (h3 : (v * u) ^ 3 = 1) (h1 : v * u ≠ 1) : v ∉ pCoreOf 2 K := by
  intro hv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu' : u = k * v * k⁻¹ := by rw [hu, mul_inv_cancel_right]
  have huO : u ∈ pCoreOf 2 K := by
    rw [hu']
    exact (mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hk) v).mp hv
  obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨v * u, mul_mem hv huO⟩
  have h2 : (v * u) ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
  have hg : (v * u) ^ (Nat.gcd 3 (2 ^ n)) = 1 := pow_gcd_eq_one.mpr ⟨h3, h2⟩
  have hcop : Nat.gcd 3 (2 ^ n) = 1 := Nat.Coprime.pow_right n (by norm_num)
  rw [hcop, pow_one] at hg
  exact h1 hg

omit [Finite X] in
theorem mem_of_sq_code (hφ : IsF7Emb φ) {L : Subgroup X} (hsq : ∀ x : X, x ^ 2 ∈ L) {x : X}
    (hx : ∃ d ∈ gLit, Core.cmul d d = codeN 8 (φ x)) : x ∈ L := by
  obtain ⟨d, hd, he⟩ := hx
  obtain ⟨y, rfl⟩ := hφ.surj d hd
  rw [hφ.code_inj (x := x) (y := y ^ 2) (by rw [pow_two, code_mul, he])]
  exact hsq y

theorem eq_Vsub_of_two (hφ : IsF7Model φ Tb) {E : Subgroup X} (hE : E ≤ Tb)
    (hEe : IsElemAbelian 2 E) {a b : X} (ha : a ∈ E) (hb : b ∈ E) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab : a ≠ b) : ∃ i : Fin 4, E = Vsub φ i := by
  obtain ⟨hcomm, hsq⟩ := hEe
  have hAc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨i, -, -, -, hV, hC⟩ := ident_check _ ((hφ.memT a).1 (hE ha)) _
    ((hφ.memT b).1 (hE hb)) (code_sq_of_sq (hsq a ha)) (code_sq_of_sq (hsq b hb))
    (fun h => ha1 (hφ.eq_one h)) (fun h => hb1 (hφ.eq_one h))
    (fun h => hab (hφ.code_inj h)) (by rw [← code_mul, ← code_mul, hAc a ha b hb])
  refine ⟨i, le_antisymm (fun x hx => ?_) (fun x hx => ?_)⟩
  · refine mem_Vsub.2 (hC _ ((hφ.memT x).1 (hE hx)) ?_ ?_)
    · rw [← code_mul, ← code_mul, hAc x hx a ha]
    · rw [← code_mul, ← code_mul, hAc x hx b hb]
  · rcases hV _ (mem_Vsub.1 hx) with h | h | h | h
    · rw [hφ.eq_one h]
      exact one_mem E
    · rw [hφ.code_inj h]
      exact ha
    · rw [hφ.code_inj h]
      exact hb
    · rw [hφ.code_inj (h.trans (code_mul a b).symm)]
      exact mul_mem ha hb

theorem elem_cases (hφ : IsF7Model φ Tb) {E : Subgroup X} (hE : E ≤ Tb)
    (hEe : IsElemAbelian 2 E) (hne : E ≠ ⊥) :
    (∃ i : Fin 4, E = Vsub φ i) ∨ ∃ a ∈ E, a ≠ 1 ∧ ∀ x ∈ E, x = 1 ∨ x = a := by
  obtain ⟨⟨a, ha⟩, ha1⟩ := ne_bot_iff_exists_ne_one.mp hne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  by_cases h : ∃ b ∈ E, b ≠ 1 ∧ b ≠ a
  · obtain ⟨b, hb, hb1, hba⟩ := h
    exact Or.inl (eq_Vsub_of_two hφ hE hEe ha hb ha1' hb1 hba.symm)
  · refine Or.inr ⟨a, ha, ha1', fun x hx => ?_⟩
    by_contra hx'
    rw [not_or] at hx'
    exact h ⟨x, hx, hx'⟩

end CFSG.LocalAnalysis.WeakClosure81.NFF7.C914
