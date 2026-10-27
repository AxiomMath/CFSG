module

public import CFSG.RankThree.PartTwo.Sec21.FF79KTypeLnGen
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3E9Z
public import CFSG.GroupTheory.BaerSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.PartTwo.Sec11.Theorem1134
public import CFSG.RankThree.PartTwo.Sec21.Item21Early3ProofExists
public import CFSG.RankThree.PartTwo.Sec4.LThreePiSLOn
public import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import Certificates.Certificate3084
public import Certificates.Certificate3139
public import Certificates.Certificate3168
public import Certificates.Certificate3169

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.S3

open CFSG CFSG.RankThree.PartTwo.Sec21 TLn
local notation "Z3" => ZMod 3 × ZMod 3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] {u v r₁ r₂ w : G}

@[expose] def ψ (u v : G) (p : Z3) : G := u ^ p.1.val * v ^ p.2.val

@[expose] def lin (e₁ e₂ : Z3) (p : Z3) : Z3 := p.1.val • e₁ + p.2.val • e₂

@[expose] def IsMono (e : Z3) : Prop := e = (1, 0) ∨ e = (2, 0) ∨ e = (0, 1) ∨ e = (0, 2)

instance : DecidablePred IsMono := fun e => by unfold IsMono; infer_instance

theorem pow_val_add (hu : u ^ 3 = 1) (a c : ZMod 3) : u ^ (a + c).val = u ^ a.val * u ^ c.val := by
  rw [← pow_add, ZMod.val_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + c.val) 3, pow_add, pow_mul, hu, one_pow, mul_one]

theorem ψ_add (h : E9Data u v) (p q : Z3) : ψ u v (p + q) = ψ u v p * ψ u v q := by
  unfold ψ
  rw [Prod.fst_add, Prod.snd_add, pow_val_add h.a3, pow_val_add h.b3]
  have hc : Commute (v ^ p.2.val) (u ^ q.1.val) := (Commute.pow_pow h.comm.symm _ _)
  calc u ^ p.1.val * u ^ q.1.val * (v ^ p.2.val * v ^ q.2.val)
      = u ^ p.1.val * (u ^ q.1.val * v ^ p.2.val) * v ^ q.2.val := by group
    _ = u ^ p.1.val * (v ^ p.2.val * u ^ q.1.val) * v ^ q.2.val := by rw [hc.eq]
    _ = u ^ p.1.val * v ^ p.2.val * (u ^ q.1.val * v ^ q.2.val) := by group

theorem ψ_zero : ψ u v 0 = 1 := by simp [ψ]

theorem ψ_nsmul (h : E9Data u v) (n : ℕ) (p : Z3) : ψ u v (n • p) = ψ u v p ^ n := by
  induction n with
  | zero => simp [ψ_zero]
  | succ n ih => rw [succ_nsmul, ψ_add h, ih, pow_succ]

theorem ψ_inj (h : E9Data u v) {p q : Z3} (hpq : ψ u v p = ψ u v q) : p = q := by
  have := h.dist p.1 p.2 q.1 q.2 hpq
  exact Prod.ext this.1 this.2

theorem ψ_neg (h : E9Data u v) (p : Z3) : ψ u v (-p) = (ψ u v p)⁻¹ := by
  have := ψ_add h p (-p)
  have h0 : p + -p = 0 := by ext <;> simp
  rw [h0, ψ_zero] at this
  exact eq_inv_of_mul_eq_one_right this.symm

theorem ψ_mem (h : E9Data u v) (p : Z3) : ψ u v p ∈ R u v :=
  h.mem_R_iff.mpr ⟨p.1, p.2, rfl⟩

theorem exists_ψ (h : E9Data u v) {x : G} (hx : x ∈ R u v) : ∃ p, x = ψ u v p := by
  obtain ⟨i, j, rfl⟩ := h.mem_R_iff.mp hx
  exact ⟨(i, j), rfl⟩

theorem ψ_eq_one (h : E9Data u v) {p : Z3} (hp : ψ u v p = 1) : p = 0 :=
  ψ_inj h (hp.trans ψ_zero.symm)

@[simp] theorem ψ_10 : ψ u v (1, 0) = u := by show u ^ 1 * v ^ 0 = u; simp
@[simp] theorem ψ_20 : ψ u v (2, 0) = u ^ 2 := by show u ^ 2 * v ^ 0 = u ^ 2; simp
@[simp] theorem ψ_01 : ψ u v (0, 1) = v := by show u ^ 0 * v ^ 1 = v; simp
@[simp] theorem ψ_02 : ψ u v (0, 2) = v ^ 2 := by show u ^ 0 * v ^ 2 = v ^ 2; simp

theorem conj_ψ (h : E9Data u v) {d : G} {e₁ e₂ : Z3} (h1 : d * u * d⁻¹ = ψ u v e₁)
    (h2 : d * v * d⁻¹ = ψ u v e₂) (p : Z3) : d * ψ u v p * d⁻¹ = ψ u v (lin e₁ e₂ p) := by
  unfold lin
  rw [ψ_add h, ψ_nsmul h, ψ_nsmul h, ← h1, ← h2]
  unfold ψ
  simp only [conj_pow]
  group

theorem isMono_of_inBlocks {x : G} (hx : InBlocks u v x) : ∃ e, IsMono e ∧ x = ψ u v e := by
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨(1, 0), Or.inl rfl, ψ_10.symm⟩
  · exact ⟨(2, 0), Or.inr (Or.inl rfl), ψ_20.symm⟩
  · exact ⟨(0, 1), Or.inr (Or.inr (Or.inl rfl)), ψ_01.symm⟩
  · exact ⟨(0, 2), Or.inr (Or.inr (Or.inr rfl)), ψ_02.symm⟩

set_option maxRecDepth 4000 in
theorem lin_four : ∀ e₁ e₂ : Z3, IsMono e₁ → IsMono e₂ → (∀ p, lin e₁ e₂ p = 0 → p = 0) →
    ∀ p, lin e₁ e₂ (lin e₁ e₂ (lin e₁ e₂ (lin e₁ e₂ p))) = p := by
  decide +kernel

theorem mem_of_coprime {x : G} {H : Subgroup G} {m n : ℕ} (hmn : Nat.Coprime m n)
    (hm : x ^ m ∈ H) (hn : x ^ n ∈ H) : x ∈ H := by
  have h := Nat.gcd_eq_gcd_ab m n
  rw [hmn] at h
  have e : x = (x ^ (m : ℤ)) ^ (Nat.gcdA m n) * (x ^ (n : ℤ)) ^ (Nat.gcdB m n) := by
    rw [← zpow_mul, ← zpow_mul, ← zpow_add, ← h]; simp
  rw [e]
  exact H.mul_mem (H.zpow_mem (by simpa using hm) _) (H.zpow_mem (by simpa using hn) _)

theorem cen_of_mono (h : E9Data u v) {d : G} (hu : InBlocks u v (d * u * d⁻¹))
    (hv : InBlocks u v (d * v * d⁻¹)) {k : ℕ} (hd : d ^ (3 ^ k) = 1) :
    ∀ x ∈ R u v, d * x * d⁻¹ = x := by
  obtain ⟨e₁, he₁, h1⟩ := isMono_of_inBlocks hu
  obtain ⟨e₂, he₂, h2⟩ := isMono_of_inBlocks hv
  have hc := conj_ψ h h1 h2
  have hinj : ∀ p, lin e₁ e₂ p = 0 → p = 0 := fun p hp => by
    have := hc p
    rw [hp, ψ_zero] at this
    exact ψ_eq_one h (by rw [show ψ u v p = d⁻¹ * (d * ψ u v p * d⁻¹) * d by group, this]; group)
  have h4 := lin_four e₁ e₂ he₁ he₂ hinj
  set C : Subgroup G := Subgroup.centralizer (R u v : Set G)
  have hd4 : d ^ 4 ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨p, rfl⟩ := exists_ψ h hx
    have : d ^ 4 * ψ u v p * (d ^ 4)⁻¹ = ψ u v p := by
      have e : d ^ 4 * ψ u v p * (d ^ 4)⁻¹ = d * (d * (d * (d * ψ u v p * d⁻¹) * d⁻¹) * d⁻¹) *
          d⁻¹ := by rw [show d ^ 4 = d * (d * (d * d)) by simp [pow_succ, mul_assoc]]; group
      rw [e, hc, hc, hc, hc, h4]
    calc ψ u v p * d ^ 4 = (d ^ 4 * ψ u v p * (d ^ 4)⁻¹) * d ^ 4 := by rw [this]
      _ = d ^ 4 * ψ u v p := by group
  have hd3 : d ^ (3 ^ k) ∈ C := by rw [hd]; exact C.one_mem
  have hdC := mem_of_coprime (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 4 3)) hd4 hd3
  intro x hx
  have := Subgroup.mem_centralizer_iff.mp hdC x hx
  rw [← this]; group

set_option maxRecDepth 4000 in
theorem irred_check : ∀ p : Z3, p ≠ 0 → (∃ k l m n : Fin 3,
    (k : ℕ) • p + (l : ℕ) • lin (2, 0) (0, 1) p + (m : ℕ) • lin (0, 1) (1, 0) p +
      (n : ℕ) • lin (0, 1) (1, 0) (lin (2, 0) (0, 1) p) = (1, 0)) ∧
    (∃ k l m n : Fin 3,
    (k : ℕ) • p + (l : ℕ) • lin (2, 0) (0, 1) p + (m : ℕ) • lin (0, 1) (1, 0) p +
      (n : ℕ) • lin (0, 1) (1, 0) (lin (2, 0) (0, 1) p) = (0, 1)) := by
  decide +kernel

theorem lin_z : ∀ p : Z3, lin (2, 0) (0, 1) (lin (1, 0) (0, 2) p) = -p := by decide

theorem nd_r₁_conj (D : NormData u v r₁ r₂ w) (p : Z3) :
    r₁ * ψ u v p * r₁⁻¹ = ψ u v (lin (2, 0) (0, 1) p) :=
  conj_ψ D.toE9Data (by rw [ψ_20, D.r₁a]; group) (by rw [ψ_01, D.r₁b]; group) p

theorem nd_r₂_conj (D : NormData u v r₁ r₂ w) (p : Z3) :
    r₂ * ψ u v p * r₂⁻¹ = ψ u v (lin (1, 0) (0, 2) p) :=
  conj_ψ D.toE9Data (by rw [ψ_10, D.r₂a]; group) (by rw [ψ_02, D.r₂b]; group) p

theorem nd_w_conj (D : NormData u v r₁ r₂ w) (p : Z3) :
    w * ψ u v p * w⁻¹ = ψ u v (lin (0, 1) (1, 0) p) :=
  conj_ψ D.toE9Data (by rw [ψ_01, D.wa]; group) (by rw [ψ_10, D.wb]; group) p

theorem nd_irred (D : NormData u v r₁ r₂ w) {L : Subgroup G} (hL : L ≤ R u v)
    (h1 : ∀ x ∈ L, r₁ * x * r₁⁻¹ ∈ L) (hw : ∀ x ∈ L, w * x * w⁻¹ ∈ L) : L = ⊥ ∨ L = R u v := by
  have h := D.toE9Data
  by_cases hb : L = ⊥
  · exact Or.inl hb
  right
  obtain ⟨⟨x, hxL⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hb
  obtain ⟨p, rfl⟩ := exists_ψ h (hL hxL)
  have hp : p ≠ 0 := fun h0 => hx1 (Subtype.ext (by show ψ u v p = 1; rw [h0, ψ_zero]))
  have hmem : ∀ k l m n : Fin 3, ψ u v ((k : ℕ) • p + (l : ℕ) • lin (2, 0) (0, 1) p +
      (m : ℕ) • lin (0, 1) (1, 0) p + (n : ℕ) • lin (0, 1) (1, 0) (lin (2, 0) (0, 1) p)) ∈ L := by
    intro k l m n
    have a1 : ψ u v (lin (2, 0) (0, 1) p) ∈ L := by rw [← nd_r₁_conj D]; exact h1 _ hxL
    have a2 : ψ u v (lin (0, 1) (1, 0) p) ∈ L := by rw [← nd_w_conj D]; exact hw _ hxL
    have a3 : ψ u v (lin (0, 1) (1, 0) (lin (2, 0) (0, 1) p)) ∈ L := by
      rw [← nd_w_conj D]; exact hw _ a1
    simp only [ψ_add h, ψ_nsmul h]
    exact L.mul_mem (L.mul_mem (L.mul_mem (L.pow_mem hxL _) (L.pow_mem a1 _))
      (L.pow_mem a2 _)) (L.pow_mem a3 _)
  obtain ⟨⟨k, l, m, n, e1⟩, ⟨k', l', m', n', e2⟩⟩ := irred_check p hp
  have hu : u ∈ L := by have := hmem k l m n; rwa [e1, ψ_10] at this
  have hv : v ∈ L := by have := hmem k' l' m' n'; rwa [e2, ψ_01] at this
  refine le_antisymm hL ?_
  rw [Subgroup.closure_le]
  intro y hy
  rcases hy with rfl | rfl
  · exact hu
  · exact hv

end CFSG.RankThree.PartTwo.Sec21.FF79.S3
