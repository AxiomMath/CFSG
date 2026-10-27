module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Geom
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin U42F431

@[expose] def gTY (k : ℕ) : Y := ⟨wordP (TgW.getD k []), wordP_mem _⟩

@[expose] def T : Subgroup Y := Subgroup.closure (Set.range fun k : Fin 5 => gTY k)

@[expose] def c3Y : Y := ⟨wordP c3W, wordP_mem _⟩

theorem repL_gTY (k : ℕ) : RepL (gTL k) ((gTY k : Y) : P45) := by
  rw [gTL_eq]
  exact repL_wordP _

theorem repL_c3 : RepL c3L ((c3Y : Y) : P45) := by
  rw [c3L_eq]
  exact repL_wordP _

theorem chkT_spec :
    Tl.length = 64 ∧ Tpar.length = 64 ∧
    (∀ i < 64, i = 0 ∨ ((Tpar.getD i (0, 0)).1 < i ∧ (Tpar.getD i (0, 0)).2 < 5 ∧
      Tl.getD i [] = comp (Tl.getD (Tpar.getD i (0, 0)).1 []) (gTL (Tpar.getD i (0, 0)).2))) ∧
    Tl.getD 0 [] = idL ∧
    (∀ i < 64, ∀ k < 5, comp (Tl.getD i []) (gTL k) ∈ Tl) ∧
    (∀ i < 64, ∀ j < 64, i = j ∨ Tl.getD i [] ≠ Tl.getD j []) ∧
    (∀ k < 5, (gTL k).getD 0 0 = 0 ∧ sameSet (imgSet (gTL k) L0) L0 = true) ∧
    comp c3L (comp c3L c3L) = idL ∧ c3L ≠ idL ∧ c3L.getD 0 0 = 0 ∧
    sameSet (imgSet c3L L0) L0 = true ∧
    (∀ k < 5, comp (comp c3L (gTL k)) (comp c3L c3L) ∈ Tl) ∧
    (∀ i < 64, ((List.range 5).all fun k =>
        comp (Tl.getD i []) (gTL k) == comp (gTL k) (Tl.getD i [])) = false ∨
      Tl.getD i [] = idL ∨ Tl.getD i [] = xL) ∧
    xL ∈ Tl ∧ comp t0L t0L = idL ∧ t0L ≠ idL ∧ (fixPts xL).length = 13 ∧ fixPts t0L = L0 := by
  have h := Certificates.certificate4161.2.2.2.1
  simp only [chkT, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq, bne_iff_ne,
    ne_eq, List.contains_iff_mem, decide_eq_true_eq, and_assoc, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  exact h

theorem exists_Tel {i : ℕ} (hi : i < 64) :
    ∃ g : Y, g ∈ T ∧ RepL (Tl.getD i []) (g : P45) := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases (chkT_spec.2.2.1 i hi) with h0 | ⟨hj, hk, heq⟩
    · subst h0
      refine ⟨1, T.one_mem, ?_⟩
      rw [chkT_spec.2.2.2.1]
      exact repL_one 45
    · obtain ⟨g, hgT, hg⟩ := ih _ hj (by omega)
      refine ⟨g * gTY (Tpar.getD i (0, 0)).2, T.mul_mem hgT ?_, ?_⟩
      · exact Subgroup.subset_closure ⟨⟨(Tpar.getD i (0, 0)).2, hk⟩, rfl⟩
      · rw [heq]
        exact repL_mul hg (repL_gTY _)

theorem mem_T_iff (g : Y) :
    g ∈ T ↔ ∃ i < 64, RepL (Tl.getD i []) (g : P45) := by
  constructor
  · intro hg
    have key : ((T : Subgroup Y) : Set Y) ⊆ {g : Y | ∃ i < 64, RepL (Tl.getD i []) (g : P45)} := by
      refine closure_subset_of_right_closed (S := Set.range fun k : Fin 5 => gTY k) ?_ ?_ ?_
      · intro s _
        obtain ⟨n, hn, h⟩ := (isOfFinOrder_of_finite s).exists_pow_eq_one
        exact ⟨n, hn, h⟩
      · exact ⟨0, by norm_num, by rw [chkT_spec.2.2.2.1]; exact repL_one 45⟩
      · rintro p ⟨i, hi, hp⟩ s ⟨k, rfl⟩
        have hmem := chkT_spec.2.2.2.2.1 i hi k k.2
        obtain ⟨i', hi', hi'e⟩ := List.mem_iff_getElem.1 hmem
        have hi64 : i' < 64 := by have := chkT_spec.1; omega
        refine ⟨i', hi64, ?_⟩
        rw [List.getD_eq_getElem _ _ hi', hi'e]
        exact repL_mul hp (repL_gTY k)
    exact key hg
  · rintro ⟨i, hi, hg⟩
    obtain ⟨g', hg'T, hg'⟩ := exists_Tel hi
    have : g = g' := Subtype.ext (eq_of_repL hg hg')
    rwa [this]

theorem card_T : Nat.card T = 64 := by
  choose! Tel hTel using fun (i : ℕ) (hi : i < 64) => exists_Tel (i := i) hi
  have hbij : Function.Bijective fun i : Fin 64 => (⟨Tel i, (hTel i i.2).1⟩ : T) := by
    constructor
    · intro i j hij
      have h1 := hTel i i.2
      have h2 := hTel j j.2
      have hij' : Tel i = Tel j := congrArg Subtype.val hij
      have hl : Tl.getD i [] = Tl.getD j [] := repL_unique h1.2 (hij' ▸ h2.2)
      rcases chkT_spec.2.2.2.2.2.1 i i.2 j j.2 with h | h
      · exact Fin.ext h
      · exact absurd hl h
    · rintro ⟨g, hg⟩
      obtain ⟨i, hi, hgi⟩ := (mem_T_iff g).1 hg
      refine ⟨⟨i, hi⟩, Subtype.ext (Subtype.ext ?_)⟩
      have h := hTel i hi
      exact eq_of_repL h.2 hgi
  rw [← Nat.card_eq_of_bijective _ hbij]
  simp

theorem gTY_mem_B0 (k : ℕ) (hk : k < 5) : gTY k ∈ B0 := by
  have h := chkT_spec.2.2.2.2.2.2.1 k hk
  refine ⟨(mem_P1_iff _).2 ?_, (mem_P2_iff _).2 ?_⟩
  · apply Fin.ext
    rw [← (repL_gTY k).2 0]
    exact h.1
  · rw [L0S, image_lineSet (repL_gTY k) L0_lt, lineSet_eq_of_sameSet h.2]

theorem T_le_B0 : T ≤ B0 := by
  rw [T, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  exact gTY_mem_B0 k k.2

theorem c3_mem_B0 : c3Y ∈ B0 := by
  have h1 := chkT_spec.2.2.2.2.2.2.2.2.2.2.1
  have h2 := chkT_spec.2.2.2.2.2.2.2.2.2.1
  refine ⟨(mem_P1_iff _).2 ?_, (mem_P2_iff _).2 ?_⟩
  · apply Fin.ext
    rw [← repL_c3.2 0]
    exact h2
  · rw [L0S, image_lineSet repL_c3 L0_lt, lineSet_eq_of_sameSet h1]

theorem c3_pow_three : c3Y ^ 3 = 1 := by
  apply Subtype.ext
  have h := chkT_spec.2.2.2.2.2.2.2.1
  have e : ((c3Y : Y) : P45) * (((c3Y : Y) : P45) * ((c3Y : Y) : P45)) = 1 := by
    refine eq_of_repL (l := comp c3L (comp c3L c3L))
      (repL_mul repL_c3 (repL_mul repL_c3 repL_c3)) ?_
    rw [h]
    exact repL_one 45
  simpa [pow_succ, mul_assoc] using e

theorem c3_ne_one : c3Y ≠ 1 := by
  intro h
  have hl : c3L = idL := repL_unique repL_c3 (by
    rw [show ((c3Y : Y) : P45) = 1 by rw [h]; rfl]
    exact repL_one 45)
  exact chkT_spec.2.2.2.2.2.2.2.2.1 hl

theorem orderOf_c3 : orderOf c3Y = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime c3_pow_three c3_ne_one

theorem repL_c3_inv : RepL (comp c3L c3L) (((c3Y : Y) : P45)⁻¹) := by
  have e : ((c3Y : Y) : P45)⁻¹ = ((c3Y : Y) : P45) * ((c3Y : Y) : P45) := by
    have h := c3_pow_three
    have h' : ((c3Y : Y) : P45) ^ 3 = 1 := by simpa using congrArg Subtype.val h
    rw [inv_eq_iff_mul_eq_one]
    calc ((c3Y : Y) : P45) * (((c3Y : Y) : P45) * ((c3Y : Y) : P45))
        = ((c3Y : Y) : P45) ^ 3 := by simp [pow_succ, mul_assoc]
      _ = 1 := h'
  rw [e]
  exact repL_mul repL_c3 repL_c3

theorem c3_conj_mem_T (k : ℕ) (hk : k < 5) :
    c3Y * gTY k * c3Y⁻¹ ∈ T := by
  rw [mem_T_iff]
  have hmem := chkT_spec.2.2.2.2.2.2.2.2.2.2.2.1 k hk
  obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.1 hmem
  have hi64 : i < 64 := by have := chkT_spec.1; omega
  refine ⟨i, hi64, ?_⟩
  rw [List.getD_eq_getElem _ _ hi, hie]
  exact repL_mul (repL_mul repL_c3 (repL_gTY k)) repL_c3_inv

theorem c3_conj_mem {h : Y} (hh : h ∈ T) :
    c3Y * h * c3Y⁻¹ ∈ T := by
  refine Subgroup.closure_induction (p := fun x _ => c3Y * x * c3Y⁻¹ ∈ T) ?_ ?_ ?_ ?_ hh
  · rintro _ ⟨k, rfl⟩
    exact c3_conj_mem_T k k.2
  · simp only [mul_one, mul_inv_cancel]
    exact T.one_mem
  · intro x y _ _ hx hy
    have : c3Y * (x * y) * c3Y⁻¹ = (c3Y * x * c3Y⁻¹) * (c3Y * y * c3Y⁻¹) := by
      simp only [mul_assoc, inv_mul_cancel_left]
    rw [this]
    exact T.mul_mem hx hy
  · intro x _ hx
    have : c3Y * x⁻¹ * c3Y⁻¹ = (c3Y * x * c3Y⁻¹)⁻¹ := by
      simp only [mul_inv_rev, inv_inv, mul_assoc]
    rw [this]
    exact T.inv_mem hx

theorem c3_mem_normalizer :
    c3Y ∈ Subgroup.normalizer (T : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨c3_conj_mem, fun hu => ?_⟩
  have h3' : c3Y * (c3Y * c3Y) = 1 := by
    have := c3_pow_three
    rwa [pow_three] at this
  have h3 : c3Y * c3Y * c3Y = 1 := by rw [mul_assoc]; exact h3'
  have hinv : c3Y⁻¹ = c3Y * c3Y := by
    rw [inv_eq_iff_mul_eq_one]; exact h3'
  have e : h = c3Y * (c3Y * (c3Y * h * c3Y⁻¹) * c3Y⁻¹) * c3Y⁻¹ := by
    have e1 : (c3Y * c3Y * c3Y) * h * (c3Y * c3Y * c3Y)⁻¹ = h := by
      rw [h3]; simp
    refine e1.symm.trans ?_
    simp only [mul_inv_rev, mul_assoc]
  rw [e]
  exact c3_conj_mem (c3_conj_mem hu)

theorem isSylow_T :
    CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ := by
  refine ⟨le_top, ?_, ?_⟩
  · exact IsPGroup.of_card (n := 6) (by rw [card_T]; norm_num)
  · show ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    have h := Subgroup.index_mul_card (H := T)
    rw [card_T, show Nat.card Y = 25920 from card_Xs] at h
    omega

end CFSG.Quasithin.H13.F431.U42
