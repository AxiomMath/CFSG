module

public import CFSG.Quasithin.H13.VolII16SLNat
public import CFSG.Quasithin.H13.VolII16Central

public section

noncomputable section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Quasithin CFSG.Assembly.LowTwoRank Matrix Subgroup
open scoped commutatorElement

section Diag

variable {K : Type*} [Field K]

@[expose] def diagSL (d : Fin 3 → K) (hd : d 0 * d 1 * d 2 = 1) : SpecialLinearGroup (Fin 3) K :=
  ⟨diagonal d, by rw [det_diagonal, Fin.prod_univ_three, hd]⟩

theorem diagSL_coe (d : Fin 3 → K) (hd : d 0 * d 1 * d 2 = 1) :
    ((diagSL d hd : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal d :=
  rfl

theorem diagSL_mul_comm {d e : Fin 3 → K} (hd : d 0 * d 1 * d 2 = 1) (he : e 0 * e 1 * e 2 = 1) :
    diagSL d hd * diagSL e he = diagSL e he * diagSL d hd := by
  apply Subtype.ext
  show (diagSL d hd : Matrix (Fin 3) (Fin 3) K) * diagSL e he =
    (diagSL e he : Matrix (Fin 3) (Fin 3) K) * diagSL d hd
  rw [diagSL_coe, diagSL_coe, diagonal_mul_diagonal, diagonal_mul_diagonal,
    show (fun i => d i * e i) = fun i => e i * d i from funext fun i => mul_comm _ _]

theorem transvection_comm_diagSL {i j : Fin 3} (hij : i ≠ j) (c : K) {d : Fin 3 → K}
    (hd : d 0 * d 1 * d 2 = 1) (hdij : d i = d j) :
    SpecialLinearGroup.transvection hij c * diagSL d hd =
      diagSL d hd * SpecialLinearGroup.transvection hij c := by
  apply Subtype.ext
  show (SpecialLinearGroup.transvection hij c : Matrix (Fin 3) (Fin 3) K) * diagSL d hd =
    (diagSL d hd : Matrix (Fin 3) (Fin 3) K) * SpecialLinearGroup.transvection hij c
  rw [diagSL_coe, SpecialLinearGroup.transvection_coe]
  ext a b
  rw [mul_diagonal, diagonal_mul]
  by_cases hab : a = b
  · subst hab
    exact mul_comm _ _
  · rw [Matrix.add_apply, one_apply_ne hab, zero_add, single_apply]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      rw [hdij, mul_comm]
    · simp

theorem closure_centralizers_eq_top {d e : Fin 3 → K} (hd : d 0 * d 1 * d 2 = 1)
    (he : e 0 * e 1 * e 2 = 1) (hd01 : d 0 = d 1) (he12 : e 1 = e 2) :
    closure {g | g * diagSL d hd = diagSL d hd * g ∨ g * diagSL e he = diagSL e he * g} = ⊤ := by
  set S := {g | g * diagSL d hd = diagSL d hd * g ∨ g * diagSL e he = diagSL e he * g}
  have h01 : ∀ c : K, SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 1) c ∈
      closure S := fun c => Subgroup.subset_closure (Or.inl (transvection_comm_diagSL _ c hd hd01))
  have h10 : ∀ c : K, SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 0) c ∈
      closure S := fun c =>
    Subgroup.subset_closure (Or.inl (transvection_comm_diagSL _ c hd hd01.symm))
  have h12 : ∀ c : K, SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 2) c ∈
      closure S := fun c => Subgroup.subset_closure (Or.inr (transvection_comm_diagSL _ c he he12))
  have h21 : ∀ c : K, SpecialLinearGroup.transvection (by decide : (2 : Fin 3) ≠ 1) c ∈
      closure S := fun c =>
    Subgroup.subset_closure (Or.inr (transvection_comm_diagSL _ c he he12.symm))
  have hcomm : ∀ {x y : SpecialLinearGroup (Fin 3) K}, x ∈ closure S → y ∈ closure S →
      ⁅x, y⁆ ∈ closure S := fun hx hy => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  have h02 : ∀ c : K, SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) c ∈
      closure S := fun c => by
    have h := SpecialLinearGroup.commutatorElement_transvection (by decide : (0 : Fin 3) ≠ 1)
      (by decide : (1 : Fin 3) ≠ 2) (by decide : (0 : Fin 3) ≠ 2) c 1
    rw [mul_one] at h
    rw [← h]
    exact hcomm (h01 c) (h12 1)
  have h20 : ∀ c : K, SpecialLinearGroup.transvection (by decide : (2 : Fin 3) ≠ 0) c ∈
      closure S := fun c => by
    have h := SpecialLinearGroup.commutatorElement_transvection (by decide : (2 : Fin 3) ≠ 1)
      (by decide : (1 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 0) c 1
    rw [mul_one] at h
    rw [← h]
    exact hcomm (h21 c) (h10 1)
  rw [eq_top_iff, ← SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field,
    closure_le]
  rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
  rw [TransvectionStruct.toSpecialLinearGroup_mk]
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | exact h01 c
    | exact h10 c
    | exact h12 c
    | exact h21 c
    | exact h02 c
    | exact h20 c

end Diag

theorem sl3_cover {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 < n) (hK : Nat.card K = 2 ^ n)
    {W : Type} [CommGroup W] [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1) {H : Subgroup (MulAut W)}
    {Z : Subgroup W} (hZ : Z ≤ fixV H) (hcomm : commV H = ⊤)
    (h : (FFModel.nat (StatedSL 3 K)).Realizes H ⊤ Z) : Z = ⊥ := by
  classical
  obtain ⟨π₀, b₀, hπs, -, hbk, hbe⟩ := topBot_data (D := FFModel.nat (StatedSL 3 K)) rfl rfl h
  let π : ↥(StatedSL 3 K) →* ↥H := π₀
  let b : W →* Multiplicative (Fin 3 → K) := b₀
  set ψ := specialLinearGroupEquivStatedSL 3 K
  let ρ : SpecialLinearGroup (Fin 3) K →* MulAut W := H.subtype.comp (π.comp ψ.toMonoidHom)
  have hbk' : ∀ w, b w = 1 ↔ w ∈ Z := hbk
  have hρ : ∀ (g : SpecialLinearGroup (Fin 3) K) (w : W), Multiplicative.toAdd (b (ρ g w)) =
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ Multiplicative.toAdd (b w) := fun g w =>
    congrArg Multiplicative.toAdd (hbe (ψ g) w)
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨l, hl0, hl1⟩ : ∃ l : K, l ≠ 0 ∧ l ≠ 1 := by
    by_contra hc
    push Not at hc
    have hs : Function.Surjective (![0, 1] : Fin 2 → K) := fun x => by
      by_cases hx : x = 0
      · exact ⟨0, by simp [hx]⟩
      · exact ⟨1, by simp [hc x hx]⟩
    have h1 := Nat.card_le_card_of_surjective _ hs
    rw [hK, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    have h2 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  set q := Fintype.card K with hqdef
  have hq : q = 2 ^ n := by rw [hqdef, ← Nat.card_eq_fintype_card, hK]
  have hodd : Odd (q - 1) := by
    rw [hq]
    exact Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' (by omega)).2 even_two) odd_one
  have hlq : l ^ (q - 1) = 1 := FiniteField.pow_card_sub_one_eq_one l hl0
  have hm1 : l⁻¹ * l⁻¹ ≠ 1 := by
    intro h2
    rw [← mul_inv] at h2
    have h3 : l ^ 2 = 1 := by rw [sq]; exact inv_eq_one.1 h2
    have h4 := pow_gcd_eq_one.2 ⟨h3, hlq⟩
    rw [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.2 hodd), pow_one] at h4
    exact hl1 h4
  have hm0 : l⁻¹ * l⁻¹ ≠ 0 := mul_ne_zero (inv_ne_zero hl0) (inv_ne_zero hl0)
  have hmq : (l⁻¹ * l⁻¹) ^ (q - 1) = 1 := FiniteField.pow_card_sub_one_eq_one _ hm0
  let d : Fin 3 → K := ![l, l, l⁻¹ * l⁻¹]
  let e : Fin 3 → K := ![l⁻¹ * l⁻¹, l, l]
  have hd : d 0 * d 1 * d 2 = 1 := by
    show l * l * (l⁻¹ * l⁻¹) = 1
    rw [mul_mul_mul_comm, mul_inv_cancel₀ hl0, one_mul]
  have he : e 0 * e 1 * e 2 = 1 := by
    show l⁻¹ * l⁻¹ * l * l = 1
    rw [mul_assoc, mul_assoc, inv_mul_cancel_left₀ hl0, inv_mul_cancel₀ hl0]
  have hdv : ∀ i, d i ≠ 1 ∧ d i ^ (q - 1) = 1 := fun i => by
    fin_cases i
    exacts [⟨hl1, hlq⟩, ⟨hl1, hlq⟩, ⟨hm1, hmq⟩]
  have hev : ∀ i, e i ≠ 1 ∧ e i ^ (q - 1) = 1 := fun i => by
    fin_cases i
    exacts [⟨hm1, hmq⟩, ⟨hl1, hlq⟩, ⟨hl1, hlq⟩]
  have hpow : ∀ (v : Fin 3 → K) (hv : v 0 * v 1 * v 2 = 1), (∀ i, v i ^ (q - 1) = 1) →
      ρ (diagSL v hv) ^ (q - 1) = 1 := fun v hv hvq => by
    rw [← map_pow]
    have h1 : diagSL v hv ^ (q - 1) = 1 := by
      apply Subtype.ext
      show (diagSL v hv : Matrix (Fin 3) (Fin 3) K) ^ (q - 1) = 1
      rw [diagSL_coe, diagonal_pow,
        show v ^ (q - 1) = 1 from funext fun i => by rw [Pi.pow_apply, Pi.one_apply, hvq i]]
      exact diagonal_one
    rw [h1, map_one]
  have hfpf : ∀ (v : Fin 3 → K) (hv : v 0 * v 1 * v 2 = 1), (∀ i, v i ≠ 1) →
      ∀ w, ρ (diagSL v hv) w = w → w ∈ Z := fun v hv hv1 w hw => by
    have h1 := hρ (diagSL v hv) w
    rw [hw, diagSL_coe] at h1
    have h2 : Multiplicative.toAdd (b w) = 0 := funext fun i => by
      have h3 := congrFun h1 i
      rw [mulVec_diagonal] at h3
      have h4 : (v i - 1) * Multiplicative.toAdd (b w) i = 0 := by
        rw [sub_mul, one_mul, ← h3, sub_self]
      exact (mul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 (hv1 i))
    exact (hbk' w).1 (Multiplicative.toAdd.injective (by rw [h2, toAdd_one]))
  have hgen : H ≤ closure {x | x * ρ (diagSL d hd) = ρ (diagSL d hd) * x ∨
      x * ρ (diagSL e he) = ρ (diagSL e he) * x} := by
    intro x hx
    obtain ⟨γ, hγ⟩ := hπs ⟨x, hx⟩
    obtain ⟨g, rfl⟩ := ψ.surjective γ
    have hx' : ρ g = x := congrArg Subtype.val hγ
    rw [← hx']
    have hle : closure {g | g * diagSL d hd = diagSL d hd * g ∨
        g * diagSL e he = diagSL e he * g} ≤ (closure {x | x * ρ (diagSL d hd) =
          ρ (diagSL d hd) * x ∨ x * ρ (diagSL e he) = ρ (diagSL e he) * x}).comap ρ := by
      rw [closure_le]
      intro g hg
      rw [SetLike.mem_coe, mem_comap]
      apply Subgroup.subset_closure
      rcases hg with hg | hg
      · left
        rw [← map_mul, hg, map_mul]
      · right
        rw [← map_mul, hg, map_mul]
    exact hle (by rw [closure_centralizers_eq_top hd he rfl rfl]; exact mem_top g)
  exact eq_bot_of_two_fpf (t₁ := ρ (diagSL d hd)) (t₂ := ρ (diagSL e he)) hW2 hZ hcomm
    (π (ψ (diagSL d hd))).2 (π (ψ (diagSL e he))).2
    (by rw [← map_mul, ← map_mul, diagSL_mul_comm]) hodd hodd
    (hpow d hd fun i => (hdv i).2) (hpow e he fun i => (hev i).2)
    (hfpf d hd fun i => (hdv i).1) (hfpf e he fun i => (hev i).1) hgen

theorem binaryNaturalSL_three_eq_bot {V : Type} [CommGroup V] [Finite V]
    (hV2 : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)} (hI : commV L ∈ IrrPlus L ⊤) {n : ℕ}
    (hn : 1 < n) (h : BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 3 n) :
    fixV L ⊓ commV L = ⊥ := by
  obtain ⟨K, _, _, hK, hR⟩ := h
  exact eq_bot_of_restrict _ (fun _ _ _ hW2 _ _ hZ hcomm hRW =>
    sl3_cover hn hK hW2 hZ hcomm hRW) hV2 hI hR

end CFSG.Quasithin.H13.VolI
