module

public import CFSG.LocalAnalysis.StandardType.GGPGLToralityBasic
import CFSG.LocalAnalysis.StandardType.GGPGLToralityCaseB

public section

namespace CFSG.StandardType

open Matrix

private lemma kgLangS1ALinWeightAux_exists_weight {d p : ℕ} (hd : 2 ≤ d)
    (h2 : ¬ (p : ℤ) ∣ 2) :
    ∃ a : Fin d → ℤ, (∑ i, a i = 0) ∧ ∃ i j, ¬ (p : ℤ) ∣ a i - a j := by
  let i0 : Fin d := ⟨0, by omega⟩
  let i1 : Fin d := ⟨1, by omega⟩
  have hne : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i1] at this
  refine ⟨fun i => if i = i0 then 1 else if i = i1 then -1 else 0, ?_, ?_⟩
  · have hpt : ∀ i, (if i = i0 then (1:ℤ) else if i = i1 then -1 else 0)
        = (if i = i0 then (1:ℤ) else 0) + (if i = i1 then (-1:ℤ) else 0) := by
      intro i
      by_cases h0 : i = i0
      · subst h0
        simp [hne]
      · by_cases h1 : i = i1
        · subst h1
          simp [h0, hne]
        · simp [h0, h1]
    rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq' Finset.univ i0 (fun _ => (1:ℤ)),
      Finset.sum_ite_eq' Finset.univ i1 (fun _ => (-1:ℤ))]
    simp
  · refine ⟨i0, i1, ?_⟩
    have hval : (if i0 = i0 then (1:ℤ) else if i0 = i1 then -1 else 0) -
        (if i1 = i0 then (1:ℤ) else if i1 = i1 then -1 else 0) = 2 := by
      rw [if_pos rfl, if_neg (Ne.symm hne), if_pos rfl]
      norm_num
    change ¬ (p : ℤ) ∣ (if i0 = i0 then (1:ℤ) else if i0 = i1 then -1 else 0) -
        (if i1 = i0 then (1:ℤ) else if i1 = i1 then -1 else 0)
    rw [hval]
    exact h2

private lemma kgLangS1ALinWeightAux_weight_two_classes {d p : ℕ} {β : Type} [DecidableEq β]
    (w : Fin d → β) {b₁ b₂ : β} (hb : b₁ ≠ b₂)
    (himg : Finset.univ.image w = {b₁, b₂})
    (hK1 : (Finset.univ.filter (fun i => w i = b₁)).card = p)
    (hK2 : (Finset.univ.filter (fun i => w i = b₂)).card = p)
    (hp : 0 < p) (h2 : ¬ (p : ℤ) ∣ 2) :
    ∃ a : Fin d → ℤ, (∑ i, a i = 0) ∧ (∃ i j, ¬ (p : ℤ) ∣ a i - a j) ∧
      ∀ i j, a i ≠ a j → w i ≠ w j := by
  have hfilt : (Finset.univ.filter (fun i => ¬ w i = b₁)) =
      Finset.univ.filter (fun i => w i = b₂) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi
      have : w i ∈ Finset.univ.image w := Finset.mem_image_of_mem w (Finset.mem_univ i)
      rw [himg] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h
      · exact absurd h hi
      · exact h
    · intro hi h
      rw [h] at hi
      exact hb hi
  refine ⟨fun i => if w i = b₁ then (1:ℤ) else -1, ?_, ?_, ?_⟩
  · rw [Finset.sum_ite (fun _ => (1:ℤ)) (fun _ => (-1:ℤ)) (s := Finset.univ)
      (p := fun i => w i = b₁)]
    rw [hfilt, Finset.sum_const, Finset.sum_const, hK1, hK2]
    simp only [nsmul_eq_mul]
    ring
  · have hK1pos : 0 < (Finset.univ.filter (fun i => w i = b₁)).card := by rw [hK1]; exact hp
    have hK2pos : 0 < (Finset.univ.filter (fun i => w i = b₂)).card := by rw [hK2]; exact hp
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hK1pos
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hK2pos
    refine ⟨i, j, ?_⟩
    have hi' : w i = b₁ := (Finset.mem_filter.mp hi).2
    have hj' : w j = b₂ := (Finset.mem_filter.mp hj).2
    have hval : (if w i = b₁ then (1:ℤ) else -1) -
        (if w j = b₁ then (1:ℤ) else -1) = 2 := by
      rw [if_pos hi', if_neg (fun h => hb (h.symm.trans hj'))]
      norm_num
    rw [hval]
    exact h2
  · intro i j hij hwij
    apply hij
    change (if w i = b₁ then (1:ℤ) else -1) = (if w j = b₁ then (1:ℤ) else -1)
    rw [hwij]

private lemma kgLangS1ALinWeightAux_isBlockDiag_comp {ι β γ : Type*} {K : Type*} [Field K]
    {w : ι → β} {a : ι → γ} {M : Matrix ι ι K} (h : TypeA.PGLTor.IsBlockDiag w M)
    (hwa : ∀ i j, a i ≠ a j → w i ≠ w j) : TypeA.PGLTor.IsBlockDiag a M :=
  fun i j hij => h i j (hwa i j hij)

theorem kgLangS1A_weight_of_diag {d p : ℕ} {K : Type} [Field K] [Finite K] (hp : p.Prime)
    (hp2 : p ≠ 2) (hd : d = p ∨ d = 2 * p)
    {G : Subgroup (GL (Fin d) K)} (hG : TypeA.PGLTor.IsProjElem p G)
    (hab : ∀ g ∈ G, ∀ h ∈ G, g * h = h * g) (hcard : p ^ 2 * (Nat.card K - 1) ≤ Nat.card G)
    (A : GL (Fin d) K)
    (hA : ∀ y ∈ G, y ^ p = 1 → ∀ i j, i ≠ j →
      ((A : Matrix (Fin d) (Fin d) K) * (y : Matrix (Fin d) (Fin d) K) *
        ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) i j = 0) :
    ∃ a : Fin d → ℤ,
      (∀ g ∈ G, ∀ i j, a i ≠ a j →
        ((A : Matrix (Fin d) (Fin d) K) * (g : Matrix (Fin d) (Fin d) K) *
          ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) i j = 0) ∧
      ∑ i, a i = 0 ∧ ∃ i j, ¬ (p : ℤ) ∣ a i - a j := by
  classical
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hd3 : 3 ≤ d := by rcases hd with h | h <;> omega
  let i₀ : Fin d := ⟨0, by omega⟩
  haveI : Nonempty (Fin d) := ⟨i₀⟩
  have hKpos : 0 < Nat.card K - 1 := by
    have := Finite.one_lt_card (α := K); omega
  have hp_dvd_two : ¬ (p : ℤ) ∣ 2 := by
    rintro ⟨k, hk⟩
    have hpz : (0 : ℤ) < p := by exact_mod_cast hp.pos
    have hp3z : (3 : ℤ) ≤ p := by exact_mod_cast hp3
    by_cases hk0 : k ≤ 0
    · have : (p : ℤ) * k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hpz) hk0
      omega
    · push Not at hk0
      have hk1 : (1 : ℤ) ≤ k := by omega
      have : (p : ℤ) * 1 ≤ (p : ℤ) * k := mul_le_mul_of_nonneg_left hk1 (le_of_lt hpz)
      omega
  let Y : Set (GL (Fin d) K) := {y | y ∈ G ∧ y ^ p = 1}
  have : NeZero p := ⟨hp.ne_zero⟩
  let w : Fin d → (Y → K) := fun i y => TypeA.PGLTor.conjMatrix A (y : GL (Fin d) K) i i
  have hYdiag : ∀ y ∈ Y, TypeA.PGLTor.conjMatrix A y =
      diagonal (fun i => TypeA.PGLTor.conjMatrix A y i i) :=
    fun y hy => TypeA.PGLTor.eq_diagonal_of_offDiag_eq_zero (hA y hy.1 hy.2)
  have hdecomp : ∀ x ∈ G, ∀ c : Kˣ,
      (x : GL (Fin d) K) ^ p = GeneralLinearGroup.scalar (Fin d) (c ^ p) →
      ∃ y ∈ Y, x = GeneralLinearGroup.scalar (Fin d) c * y := fun x hx c hc =>
    ⟨GeneralLinearGroup.scalar (Fin d) c⁻¹ * x,
      ⟨G.mul_mem (hG.scalar_mem _) hx, TypeA.PGLTor.pow_eq_one_of_pow_eq_scalar_pow hc⟩, by
        rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]⟩
  have hwp : ∀ (y : Y) i, w i y ^ p = 1 := by
    intro y i
    have h1 := TypeA.PGLTor.conjMatrix_pow A (y : GL (Fin d) K) p
    rw [y.2.2, TypeA.PGLTor.conjMatrix_one, hYdiag (y : GL (Fin d) K) y.2, diagonal_pow] at h1
    have h2 := congrFun (congrFun h1 i) i
    simpa [one_apply_eq] using h2.symm
  have hblock : ∀ g ∈ G, TypeA.PGLTor.IsBlockDiag w (TypeA.PGLTor.conjMatrix A g) := by
    intro g hg i j hij
    have hy : ∃ y : Y, w i y ≠ w j y := by
      by_contra hcon
      push Not at hcon
      exact hij (funext hcon)
    obtain ⟨y, hy⟩ := hy
    have hcomm : TypeA.PGLTor.conjMatrix A g * diagonal (fun k => w k y) =
        diagonal (fun k => w k y) * TypeA.PGLTor.conjMatrix A g := by
      rw [show diagonal (fun k => w k y) = TypeA.PGLTor.conjMatrix A (y : GL (Fin d) K) from
          (hYdiag (y : GL (Fin d) K) y.2).symm,
        ← TypeA.PGLTor.conjMatrix_mul, ← TypeA.PGLTor.conjMatrix_mul,
        hab (y : GL (Fin d) K) y.2.1 g hg]
    exact TypeA.PGLTor.isBlockDiag_of_commute_diagonal hcomm i j hy
  by_cases hgood : ∀ x : G, ∃ c : Kˣ, TypeA.PGLTor.lam hp hp2 hG x = c ^ p
  · obtain ⟨a, ha_sum, ha_neq⟩ :=
      kgLangS1ALinWeightAux_exists_weight (d := d) (p := p) (by omega) hp_dvd_two
    refine ⟨a, ?_, ha_sum, ha_neq⟩
    intro g hg i j hij
    change TypeA.PGLTor.conjMatrix A g i j = 0
    obtain ⟨c, hc⟩ := hgood ⟨g, hg⟩
    have hxp : (g : GL (Fin d) K) ^ p = GeneralLinearGroup.scalar (Fin d) (c ^ p) := by
      rw [TypeA.PGLTor.lam_spec hp hp2 hG ⟨g, hg⟩, hc]
    obtain ⟨y, hy, hxy⟩ := hdecomp g hg c hxp
    rw [hxy, TypeA.PGLTor.conjMatrix_scalar_mul, Matrix.smul_apply]
    have hij' : i ≠ j := fun h => hij (by rw [h])
    rw [hYdiag y hy, diagonal_apply_ne _ hij']
    simp
  · push Not at hgood
    obtain ⟨g, hgnot⟩ := hgood
    have hdvd : ∀ b : Y → K, p ∣ Fintype.card {i : Fin d // w i = b} := by
      intro b
      by_contra hnd
      have hgp : (TypeA.PGLTor.conjMatrix A (g : GL (Fin d) K)) ^ p =
          scalar (Fin d) ((TypeA.PGLTor.lam hp hp2 hG g : Kˣ) : K) := by
        rw [← TypeA.PGLTor.conjMatrix_pow, TypeA.PGLTor.lam_spec hp hp2 hG g,
          TypeA.PGLTor.conjMatrix_scalar]
      have hM : ((TypeA.PGLTor.conjMatrix A (g : GL (Fin d) K)).toSquareBlock w b) ^ p =
          scalar {i : Fin d // w i = b} ((TypeA.PGLTor.lam hp hp2 hG g : Kˣ) : K) := by
        rw [← TypeA.PGLTor.toSquareBlock_pow_of_isBlockDiag
            (hblock (g : GL (Fin d) K) g.2) b p, hgp, TypeA.PGLTor.toSquareBlock_scalar]
      obtain ⟨c, hc⟩ := TypeA.PGLTor.exists_pow_eq_of_pow_eq_scalar hp hM hnd
      exact hgnot c hc.symm
    have hs : (Finset.univ.image w).card * p ≤ d := by
      have h1 : d = ∑ b ∈ Finset.univ.image w,
          (Finset.univ.filter (fun i => w i = b)).card := by
        have h := Finset.card_eq_sum_card_fiberwise (f := w) (s := Finset.univ)
          (t := Finset.univ.image w)
          (fun i _ => Finset.mem_image_of_mem w (Finset.mem_univ i))
        rwa [Finset.card_univ, Fintype.card_fin] at h
      calc (Finset.univ.image w).card * p
          = (Finset.univ.image w).card • p := by rw [smul_eq_mul]
        _ ≤ ∑ b ∈ Finset.univ.image w,
              (Finset.univ.filter (fun i => w i = b)).card := by
            refine Finset.card_nsmul_le_sum _ _ _ fun b hb => ?_
            obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hb
            have h2 := hdvd (w i)
            rw [Fintype.card_subtype] at h2
            exact Nat.le_of_dvd (Finset.card_pos.mpr ⟨i, by simp⟩) h2
        _ = d := h1.symm
    have hsle2 : (Finset.univ.image w).card ≤ 2 := by
      rcases hd with hd | hd
      · have hs' : (Finset.univ.image w).card * p ≤ 1 * p := by
          calc (Finset.univ.image w).card * p ≤ d := hs
            _ = 1 * p := by rw [hd, one_mul]
        have := Nat.le_of_mul_le_mul_right hs' hp.pos
        omega
      · have hs' : (Finset.univ.image w).card * p ≤ 2 * p := by
          calc (Finset.univ.image w).card * p ≤ d := hs
            _ = 2 * p := hd
        exact Nat.le_of_mul_le_mul_right hs' hp.pos
    have hspos : 1 ≤ (Finset.univ.image w).card :=
      Finset.card_pos.mpr ⟨w i₀, Finset.mem_image_of_mem w (Finset.mem_univ i₀)⟩
    by_cases hs1 : (Finset.univ.image w).card = 1
    · exfalso
      set lm := TypeA.PGLTor.lam hp hp2 hG with hlm
      set ψ : G →* TypeA.PGLTor.PowQuot K p := (QuotientGroup.mk' _).comp lm with hψ
      have hψker : ∀ x : G, x ∈ ψ.ker ↔ ∃ c : Kˣ, c ^ p = lm x := fun x => by
        rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
          TypeA.PGLTor.powQuot_mk_eq_one_iff]
      set G₀ := ψ.ker.map G.subtype with hG₀
      have hGcard : Nat.card G ≤ Nat.card G₀ * p := by
        rw [hG₀, Subgroup.card_map_of_injective (Subgroup.subtype_injective G),
          ← Subgroup.card_ker_mul_card_range ψ]
        exact Nat.mul_le_mul_left _ ((Subgroup.card_le_card_group _).trans
          TypeA.PGLTor.card_powQuot_le)
      have hG₀diag : ∀ x ∈ G₀, ∃ δ : Fin d → K,
          TypeA.PGLTor.conjMatrix A (x : GL (Fin d) K) = diagonal δ ∧
          (∀ i j, w i = w j → δ i = δ j) ∧ ∀ i, δ i ^ p = δ i₀ ^ p := by
        rintro _ ⟨x, hx, rfl⟩
        obtain ⟨c, hc⟩ := (hψker x).mp hx
        have hxp : (x : GL (Fin d) K) ^ p = GeneralLinearGroup.scalar (Fin d) (c ^ p) := by
          rw [TypeA.PGLTor.lam_spec hp hp2 hG x, ← hlm, hc]
        obtain ⟨y, hy, hxy⟩ := hdecomp x x.2 c hxp
        refine ⟨fun i => (c : K) * w i ⟨y, hy⟩, ?_, ?_, ?_⟩
        · change TypeA.PGLTor.conjMatrix A x = _
          rw [hxy, TypeA.PGLTor.conjMatrix_scalar_mul, hYdiag y hy, smul_eq_diagonal_mul,
            diagonal_mul_diagonal]
        · intro i j hij
          simp only [hij]
        · intro i
          rw [mul_pow, mul_pow, hwp, hwp]
      have hcount := TypeA.PGLTor.card_le_of_diag (p := p) A w i₀ hG₀diag
      rw [hs1] at hcount
      simp at hcount
      have hb : Nat.card G ≤ (Nat.card K - 1) * p :=
        hGcard.trans (Nat.mul_le_mul_right p hcount)
      have hp_lt_sq : p < p ^ 2 := by
        rw [pow_two]
        nlinarith [hp.one_lt]
      have hlt : (Nat.card K - 1) * p < p ^ 2 * (Nat.card K - 1) := by
        rw [mul_comm (p ^ 2) (Nat.card K - 1)]
        exact Nat.mul_lt_mul_of_pos_left hp_lt_sq hKpos
      omega
    · have hs2 : (Finset.univ.image w).card = 2 := by omega
      obtain ⟨b₁, b₂, hb, himg⟩ := Finset.card_eq_two.mp hs2
      have hd_eq : d = 2 * p := by
        have h2p : 2 * p ≤ d := by
          calc 2 * p = (Finset.univ.image w).card * p := by rw [hs2]
            _ ≤ d := hs
        rcases hd with hd | hd <;> omega
      have hsum2 : (Finset.univ.filter (fun i => w i = b₁)).card +
          (Finset.univ.filter (fun i => w i = b₂)).card = d := by
        have h1 := Finset.card_eq_sum_card_fiberwise (f := w) (s := Finset.univ)
          (t := Finset.univ.image w)
          (fun i _ => Finset.mem_image_of_mem w (Finset.mem_univ i))
        rw [Finset.card_univ, Fintype.card_fin, himg, Finset.sum_pair hb] at h1
        exact h1.symm
      have hdvd1 : p ∣ (Finset.univ.filter (fun i => w i = b₁)).card := by
        have := hdvd b₁
        rwa [Fintype.card_subtype] at this
      have hdvd2 : p ∣ (Finset.univ.filter (fun i => w i = b₂)).card := by
        have := hdvd b₂
        rwa [Fintype.card_subtype] at this
      obtain ⟨k1, hk1⟩ := hdvd1
      obtain ⟨k2, hk2⟩ := hdvd2
      have hpos1 : 0 < (Finset.univ.filter (fun i => w i = b₁)).card := by
        have hmem : b₁ ∈ Finset.univ.image w := by rw [himg]; simp
        obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
        exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
      have hpos2 : 0 < (Finset.univ.filter (fun i => w i = b₂)).card := by
        have hmem : b₂ ∈ Finset.univ.image w := by rw [himg]; simp
        obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
        exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
      have hk1pos : 0 < k1 := by
        rcases Nat.eq_zero_or_pos k1 with h | h
        · rw [h, mul_zero] at hk1
          rw [hk1] at hpos1
          exact absurd hpos1 (lt_irrefl 0)
        · exact h
      have hk2pos : 0 < k2 := by
        rcases Nat.eq_zero_or_pos k2 with h | h
        · rw [h, mul_zero] at hk2
          rw [hk2] at hpos2
          exact absurd hpos2 (lt_irrefl 0)
        · exact h
      have hsumk : p * k1 + p * k2 = 2 * p := by
        calc p * k1 + p * k2 = (Finset.univ.filter (fun i => w i = b₁)).card +
              (Finset.univ.filter (fun i => w i = b₂)).card := by rw [← hk1, ← hk2]
          _ = d := hsum2
          _ = 2 * p := hd_eq
      have hk : k1 + k2 = 2 := by
        have h2' : p * (k1 + k2) = p * 2 := by rw [mul_add, hsumk]; ring
        exact Nat.eq_of_mul_eq_mul_left hp.pos h2'
      have hk1eq : k1 = 1 := by omega
      have hk2eq : k2 = 1 := by omega
      have hK1 : (Finset.univ.filter (fun i => w i = b₁)).card = p := by
        rw [hk1, hk1eq, mul_one]
      have hK2 : (Finset.univ.filter (fun i => w i = b₂)).card = p := by
        rw [hk2, hk2eq, mul_one]
      obtain ⟨a, ha_sum, ha_neq, ha_const⟩ :=
        kgLangS1ALinWeightAux_weight_two_classes w hb himg hK1 hK2 hp.pos hp_dvd_two
      refine ⟨a, ?_, ha_sum, ha_neq⟩
      intro g hg i j hij
      change TypeA.PGLTor.conjMatrix A g i j = 0
      exact kgLangS1ALinWeightAux_isBlockDiag_comp (hblock g hg) ha_const i j hij

theorem kgLangS1A_lin_weight {d p : ℕ} {K : Type} [Field K] [Finite K] (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) (hd : d = p ∨ d = 2 * p)
    {G : Subgroup (GL (Fin d) K)} (hG : TypeA.PGLTor.IsProjElem p G)
    (hab : ∀ g ∈ G, ∀ h ∈ G, g * h = h * g) (hcard : p ^ 2 * (Nat.card K - 1) ≤ Nat.card G) :
    ∃ (A : GL (Fin d) K) (a : Fin d → ℤ),
      (∀ g ∈ G, ∀ i j, a i ≠ a j →
        ((A : Matrix (Fin d) (Fin d) K) * (g : Matrix (Fin d) (Fin d) K) *
          ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) i j = 0) ∧
      ∑ i, a i = 0 ∧ ∃ i j, ¬ (p : ℤ) ∣ a i - a j := by
  classical
  obtain ⟨ζ, hζ⟩ := TypeA.PGLTor.exists_isPrimitiveRoot_of_dvd hp hpK
  let Y : Set (GL (Fin d) K) := {y | y ∈ G ∧ y ^ p = 1}
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨A, hA⟩ := TypeA.PGLTor.exists_conj_diagonal hζ Y
    (fun x hx y hy => hab x hx.1 y hy.1) (fun x hx => hx.2)
  obtain ⟨a, ha, hsum, hneq⟩ :=
    kgLangS1A_weight_of_diag hp hp2 hd hG hab hcard A (fun y hy hyp => hA y ⟨hy, hyp⟩)
  exact ⟨A, a, ha, hsum, hneq⟩

end CFSG.StandardType
