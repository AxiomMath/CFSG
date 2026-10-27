module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5bE16G
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6Good
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7NOrbL
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7Sub

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

@[expose] def yl : PL := Thl.getD 9 []

@[expose] def Ttl : List PL := Thl.filter fun l => comp l (Tl.getD 20 []) == comp (Tl.getD 20 []) l

theorem yl_check : yl ∈ Thl ∧ comp yl yl = idL := by decide +kernel

theorem union_check : ∀ l ∈ Thl, comp l fhatL = comp fhatL l → comp l l = idL →
    l ∈ Al1 ∨ l ∈ Al2 := by
  decide +kernel

theorem coset_check : ∀ l ∈ Thl, l ∈ Ttl ∨ comp yl l ∈ Ttl := by decide +kernel

theorem Ttl_norm : ∀ l ∈ Ttl, NormL l (gi2.map fun i => Al2.getD i []) Al2 := by
  decide +kernel

theorem A1_gens_norm : (∀ k < 5, NormL (gTL k) (gi1.map fun i => Al1.getD i []) Al1) ∧
    NormL fhatL (gi1.map fun i => Al1.getD i []) Al1 := by
  decide +kernel

theorem gens_mem {Kl : List PL} {gi : List ℕ} (h : ∀ i ∈ gi, i < Kl.length) :
    ∀ g ∈ gi.map (fun i => Kl.getD i []), g ∈ Kl := by
  intro g hg
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
  rw [List.getD_eq_getElem _ _ (h i hi)]
  exact List.getElem_mem _


noncomputable def yA : Ah := Classical.choose (exists_That_of_mem_Thl yl_check.1)

theorem yA_mem : yA ∈ That := (Classical.choose_spec (exists_That_of_mem_Thl yl_check.1)).1

theorem repL_yA : RepL yl (yA : P45) :=
  (Classical.choose_spec (exists_That_of_mem_Thl yl_check.1)).2

theorem yA_sq : yA * yA = 1 := by
  apply Subtype.ext
  apply eq_of_repL (l := comp yl yl) (repL_mul repL_yA repL_yA)
  rw [yl_check.2]
  exact repL_one 45

theorem That_le_normalizer_A1h : That ≤ Subgroup.normalizer (A1h : Set Ah) := by
  rw [That, Subgroup.closure_le]
  rintro g (⟨k, rfl⟩ | rfl)
  · exact mem_normalizer_of_normL (h1 := A1_check.1) (hmul := A1_check.2.1) A1_check.2.2.2.1
      (gens_mem gens_check.1) gens_check.2.1 (repL_gTA k) (A1_gens_norm.1 k k.2)
  · exact mem_normalizer_of_normL (h1 := A1_check.1) (hmul := A1_check.2.1) A1_check.2.2.2.1
      (gens_mem gens_check.1) gens_check.2.1 repL_fhat A1_gens_norm.2

theorem That_le_normalizer_VA :
    That ≤ Subgroup.normalizer (VA : Set Ah) := by
  rw [normalizer_VA]
  exact That_le_Bh.trans Bh_le_P2h

theorem mem_normalizer_A2h_of_Ttl {m : Ah} {l : PL} (hl : l ∈ Ttl) (hrep : RepL l (m : P45)) :
    m ∈ Subgroup.normalizer (A2h : Set Ah) :=
  mem_normalizer_of_normL (h1 := A2_check.1) (hmul := A2_check.2.1) A2_check.2.2.2.1
    (gens_mem gens_check.2.2.1) gens_check.2.2.2 hrep (Ttl_norm l hl)

theorem conjSub_That_A2h {m : Ah} (hm : m ∈ That) :
    B6.conjSub m A2h = A2h ∨ B6.conjSub m A2h = B6.conjSub yA A2h := by
  obtain ⟨l, hl, hrep⟩ := (mem_That_iff m).1 hm
  rcases coset_check l hl with h | h
  · exact Or.inl (B6.conjSub_eq_self (mem_normalizer_A2h_of_Ttl h hrep))
  · right
    have hn : yA * m ∈ Subgroup.normalizer (A2h : Set Ah) :=
      mem_normalizer_A2h_of_Ttl h (repL_mul repL_yA hrep)
    have h1 : B6.conjSub yA (B6.conjSub m A2h) = A2h := by
      rw [← B6.conjSub_mul]
      exact B6.conjSub_eq_self hn
    have h2 : yA⁻¹ = yA := by
      have := yA_sq
      exact inv_eq_of_mul_eq_one_right this
    calc B6.conjSub m A2h = B6.conjSub yA⁻¹ (B6.conjSub yA (B6.conjSub m A2h)) := by
          rw [← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one]
      _ = B6.conjSub yA A2h := by rw [h1, h2]

section Classify


theorem card_VA_eq : Nat.card ↥VA = 16 := by
  have h1 := card_VA_ge
  have h2 := card_le_length_of_reps VA (F := Vl) fun s hs => (mem_VA_iff s).1 hs
  rw [Vl_length] at h2
  omega

theorem e16_classify {K : Subgroup Ah} (hKT : K ≤ That) (hcard : Nat.card ↥K = 16)
    (hab : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) (hsq : ∀ a ∈ K, a * a = 1) :
    K = A1h ∨ K = A2h ∨ K = B6.conjSub yA A2h ∨ K = VA := by
  by_cases hKV : K ≤ VA
  · exact Or.inr (Or.inr (Or.inr
      (Subgroup.eq_of_le_of_card_ge hKV (by rw [card_VA_eq, hcard]))))
  obtain ⟨r, hrK, hr⟩ := e16_good hKT (by omega) hab hsq hKV
  obtain ⟨m, hm, hrm⟩ := good_conj_That (hKT hrK) hr
  set K' := B6.conjSub m⁻¹ K with hK'
  have hmem : ∀ x, x ∈ K' ↔ m * x * m⁻¹ ∈ K := by
    intro x
    rw [hK', B6.mem_conjSub]
    simp
  have hK'T : K' ≤ That := by
    intro x hx
    have h1 : m * x * m⁻¹ ∈ That := hKT ((hmem x).1 hx)
    have := That.mul_mem (That.mul_mem (That.inv_mem hm) h1) hm
    simpa [mul_assoc] using this
  have hK'ab : ∀ a ∈ K', ∀ b ∈ K', a * b = b * a := by
    intro a ha b hb
    have := hab _ ((hmem a).1 ha) _ ((hmem b).1 hb)
    have e1 : m * a * m⁻¹ * (m * b * m⁻¹) = m * (a * b) * m⁻¹ := by group
    have e2 : m * b * m⁻¹ * (m * a * m⁻¹) = m * (b * a) * m⁻¹ := by group
    rw [e1, e2] at this
    have := mul_left_cancel (mul_right_cancel this)
    exact this
  have hK'sq : ∀ a ∈ K', a * a = 1 := by
    intro a ha
    have := hsq _ ((hmem a).1 ha)
    have e1 : m * a * m⁻¹ * (m * a * m⁻¹) = m * (a * a) * m⁻¹ := by group
    rw [e1] at this
    have h2 : m * (a * a) * m⁻¹ = m * 1 * m⁻¹ := by rw [this]; group
    exact mul_left_cancel (mul_right_cancel h2)
  have hfK' : fhatA ∈ K' := by
    rw [hmem]
    rw [← hrm]
    exact hrK
  have hcard' : Nat.card ↥K' = 16 := by rw [hK', conjSub_card, hcard]
  have hunion : ∀ x ∈ K', x ∈ A1h ∨ x ∈ A2h := by
    intro x hx
    obtain ⟨l, hl, hrep⟩ := (mem_That_iff x).1 (hK'T hx)
    have hcomm : comp l fhatL = comp fhatL l :=
      comp_comm_of_comm (v := fhatA) (g := x) repL_fhat hrep (hK'ab x hx fhatA hfK')
    have hl2 : comp l l = idL := repL_unique (repL_mul hrep hrep) (by
      have : (x : P45) * (x : P45) = 1 := congrArg Subtype.val (hK'sq x hx)
      rw [this]
      exact repL_one 45)
    rcases union_check l hl hcomm hl2 with h | h
    · exact Or.inl ⟨l, h, hrep⟩
    · exact Or.inr ⟨l, h, hrep⟩
  have hKm : K = B6.conjSub m K' := by
    rw [hK', ← B6.conjSub_mul, mul_inv_cancel, B6.conjSub_one]
  rcases le_or_le_of_forall_mem hunion with h | h
  · have hK1 : K' = A1h := Subgroup.eq_of_le_of_card_ge h (by rw [card_A1h, hcard'])
    left
    rw [hKm, hK1]
    exact B6.conjSub_eq_self (That_le_normalizer_A1h hm)
  · have hK2 : K' = A2h := Subgroup.eq_of_le_of_card_ge h (by rw [card_A2h, hcard'])
    rw [hKm, hK2]
    rcases conjSub_That_A2h hm with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inl h'))

end Classify

end CFSG.Quasithin.H13.F431.U42Aut
