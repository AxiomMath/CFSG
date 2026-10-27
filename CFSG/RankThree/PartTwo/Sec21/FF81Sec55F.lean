module

public import CFSG.RankThree.PartTwo.Sec21.FF81Sec55C
import CFSG.Quasithin.H13.AS91Sec8Prod
import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Grow
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41
import CFSG.RankThree.PartTwo.Sec21.FF81Sec36Z
import CFSG.RankThree.PartTwo.Sec21.FF81Sec43T
import CFSG.LinearAlgebra.LinearGroups.LinearTwo
import CFSG.LocalAnalysis.ComponentClassification.CatFC.L44CoverTrivial
import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
import CFSG.LocalAnalysis.ComponentClassification.GSLitType
import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Basic
import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8L4
import CFSG.Sporadic.Th.F2Spec

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open P51 (V e)
open S36 (hypF hypU hypA dot)

variable {G : Type} [Group G] [Finite G]

namespace S55

open scoped Pointwise

theorem le_of_norm {W M : Subgroup G} {z : G} (hz : z ^ 3 = 1)
    (hW : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    (hzW : ∀ x ∈ W, z * x * z⁻¹ ∈ W) (hzM : ∀ x ∈ M, z * x * z⁻¹ ∈ M)
    (hfix : ∀ x ∈ W, z * x * z⁻¹ = x → x ∈ M)
    (hidx : ∀ x ∈ W, ∀ y ∈ W, x ∉ M → y ∉ M → x * y ∈ M) : W ≤ M := by
  intro w hw
  by_contra hwM
  have hw₁ : z * w * z⁻¹ ∈ W := hzW w hw
  have hw₂ : z * (z * w * z⁻¹) * z⁻¹ ∈ W := hzW _ hw₁
  have h3 : z * (z * (z * w * z⁻¹) * z⁻¹) * z⁻¹ = w := by
    have hz' : z * z * z = 1 := by rw [← pow_three', hz]
    have : z * (z * (z * w * z⁻¹) * z⁻¹) * z⁻¹ = (z * z * z) * w * (z * z * z)⁻¹ := by group
    rw [this, hz']; group
  have hw₂M : z * (z * w * z⁻¹) * z⁻¹ ∉ M := fun h => hwM (by have := hzM _ h; rwa [h3] at this)
  have hw₁M : z * w * z⁻¹ ∉ M := fun h => hw₂M (hzM _ h)
  have hn : w * (z * w * z⁻¹) * (z * (z * w * z⁻¹) * z⁻¹) ∈ M := by
    refine hfix _ (W.mul_mem (W.mul_mem hw hw₁) hw₂) ?_
    calc z * (w * (z * w * z⁻¹) * (z * (z * w * z⁻¹) * z⁻¹)) * z⁻¹
        = (z * w * z⁻¹) * (z * (z * w * z⁻¹) * z⁻¹) *
            (z * (z * (z * w * z⁻¹) * z⁻¹) * z⁻¹) := by group
      _ = (z * w * z⁻¹) * (z * (z * w * z⁻¹) * z⁻¹) * w := by rw [h3]
      _ = w * (z * w * z⁻¹) * (z * (z * w * z⁻¹) * z⁻¹) := by
        exact (hW _ (W.mul_mem hw₁ hw₂) w hw).trans (mul_assoc _ _ _).symm
  have h12 := hidx w hw _ hw₁ hwM hw₁M
  have := M.mul_mem (M.inv_mem h12) hn
  rw [inv_mul_cancel_left] at this
  exact hw₂M this

theorem mul_mem_of_card {W M : Subgroup G} (hMW : M ≤ W) (hW : Nat.card W = 8)
    (hM : 2 < Nat.card M) {x y : G} (hx : x ∈ W) (hy : y ∈ W) (hxM : x ∉ M) (hyM : y ∉ M) :
    x * y ∈ M := by
  have hdvd : Nat.card M ∣ 2 ^ 3 := by have := Subgroup.card_dvd_of_le hMW; rwa [hW] at this
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  interval_cases k
  · omega
  · omega
  · have hrel := Subgroup.relIndex_mul_card (H := M) (K := W)
    rw [inf_of_le_left hMW, hk', hW] at hrel
    have hidx : (M.subgroupOf W).index = 2 := by
      change M.relIndex W = 2; omega
    have := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)).2
      (iff_of_false (by rwa [Subgroup.mem_subgroupOf]) (by rwa [Subgroup.mem_subgroupOf]))
    rwa [Subgroup.mem_subgroupOf] at this
  · exact absurd ((Subgroup.eq_of_le_of_card_ge hMW (by rw [hk', hW]; norm_num)) ▸ hx) hxM

theorem exists_mul_of_card {D P Q : Subgroup G} (hP : P ≤ D) (hQ : Q ≤ D)
    (h : Nat.card P * Nat.card Q = Nat.card D * Nat.card ↥(P ⊓ Q)) :
    ∀ d ∈ D, ∃ p ∈ P, ∃ q ∈ Q, d = p * q := by
  have hc := CFSG.Quasithin.H13.AS91.card_mul_set_mul_card_inf P Q
  rw [h] at hc
  have hcard : Nat.card ((P : Set G) * (Q : Set G)) = Nat.card D :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos hc
  have hsub : (P : Set G) * (Q : Set G) ⊆ (D : Set G) := by
    rintro _ ⟨p, hp, q, hq, rfl⟩
    exact D.mul_mem (hP hp) (hQ hq)
  have heq : (P : Set G) * (Q : Set G) = (D : Set G) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hcard]
    rfl
  intro d hd
  have hd' : d ∈ (P : Set G) * (Q : Set G) := heq ▸ hd
  obtain ⟨p, hp, q, hq, rfl⟩ := hd'
  exact ⟨p, hp, q, hq, rfl⟩

theorem le_nor_of_norm {D P Q : Subgroup G} {z : G} (hD : IsPGroup 2 D) (hPD : P ≤ D)
    (hPQ : ∀ d ∈ D, ∃ p ∈ P, ∃ q ∈ Q, d = p * q) (hPne : P ≠ D) (hQ : Nat.card Q = 8)
    (hQP : Nat.card ↥(Q ⊓ P) = 2) (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) (hz : z ^ 3 = 1)
    (hzP : z ∈ Nor P) (hzQ : z ∈ Nor Q) (hfix : ∀ x ∈ Q, z * x * z⁻¹ = x → x ∈ P) :
    Q ≤ Nor P := by
  obtain ⟨g, hgD, hgP, hgN⟩ :=
    CFSG.GH74.GLS.Stage1.Thm6.Sec13.exists_mem_normalizer_not_mem hD (lt_of_le_of_ne hPD hPne)
  obtain ⟨p, hp, q, hq, rfl⟩ := hPQ g hgD
  have hqN : q ∈ Nor P := by
    have := (Nor P).mul_mem ((Nor P).inv_mem (Subgroup.le_normalizer hp)) hgN
    rwa [inv_mul_cancel_left] at this
  have hqP : q ∉ P := fun h => hgP (P.mul_mem hp h)
  have hlt : Q ⊓ P < Q ⊓ Nor P :=
    lt_of_le_of_ne (inf_le_inf_left _ Subgroup.le_normalizer) fun h =>
      hqP (h ▸ (Subgroup.mem_inf.mpr ⟨hq, hqN⟩ : q ∈ Q ⊓ Nor P)).2
  have hM : 2 < Nat.card ↥(Q ⊓ Nor P) := hQP ▸ Subgroup.card_lt_of_lt hlt
  have key : Q ≤ Q ⊓ Nor P := by
    refine le_of_norm hz hQab (fun x hx => (Subgroup.mem_normalizer_iff.mp hzQ x).mp hx)
      (fun x hx => ?_) (fun x hx hfx => ⟨hx, Subgroup.le_normalizer (hfix x hx hfx)⟩)
      (fun x hx y hy hxM hyM => mul_mem_of_card inf_le_left hQ hM hx hy hxM hyM)
    have hx' : x ∈ Q ⊓ Nor P := hx
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hzQ x).mp hx'.1,
      (Nor P).mul_mem ((Nor P).mul_mem hzP hx'.2) ((Nor P).inv_mem hzP)⟩
  exact fun x hx => (key hx).2

theorem le_cenS_of_norm {P Q : Subgroup G} {s z : G} (hPQ : P ≤ Nor Q) (hQP : Q ≤ Nor P)
    (hint : ∀ y ∈ Q ⊓ P, y = 1 ∨ y = s) (hs2 : s * s = 1) (hsQ : ∀ x ∈ Q, x * s = s * x)
    (hsP : ∀ a ∈ P, a * s = s * a) (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) (hz : z ^ 3 = 1)
    (hzP : ∀ a ∈ P, z * a = a * z) (hzQ : z ∈ Nor Q)
    (hfix : ∀ x ∈ Q, z * x * z⁻¹ = x → x ∈ P) : P ≤ CenS Q := by
  intro a ha
  have hcomm : ∀ x ∈ Q, x * a ≠ a * x → a * x * a⁻¹ = s * x := by
    intro x hx hxa
    have h1 : a * x * a⁻¹ * x⁻¹ ∈ Q :=
      Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hPQ ha) x).mp hx) (Q.inv_mem hx)
    have h2 : a * x * a⁻¹ * x⁻¹ ∈ P := by
      have := P.mul_mem ha ((Subgroup.mem_normalizer_iff.mp (hQP hx) a⁻¹).mp (P.inv_mem ha))
      rwa [← mul_assoc, ← mul_assoc] at this
    rcases hint _ (Subgroup.mem_inf.mpr ⟨h1, h2⟩) with h | h
    · rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h; exact absurd h.symm hxa
    · rw [mul_inv_eq_iff_eq_mul] at h; exact h
  have key : Q ≤ Q ⊓ Cen a := by
    refine le_of_norm hz hQab (fun x hx => (Subgroup.mem_normalizer_iff.mp hzQ x).mp hx)
      (fun x hx => ?_) (fun x hx hfx => ?_) (fun x hx y hy hxM hyM => ?_)
    · have hx' : x ∈ Q ⊓ Cen a := hx
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hzQ x).mp hx'.1, ?_⟩
      have hxa : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.mp hx'.2
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hza := hzP a ha
      calc z * x * z⁻¹ * a = z * x * (z⁻¹ * a * z) * z⁻¹ := by group
        _ = z * (x * a) * z⁻¹ := by rw [show z⁻¹ * a * z = a by rw [mul_assoc, ← hza]; group]; group
        _ = z * (a * x) * z⁻¹ := by rw [hxa]
        _ = a * (z * x * z⁻¹) := by rw [← mul_assoc, hza]; group
    · refine Subgroup.mem_inf.mpr ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      rcases hint x (Subgroup.mem_inf.mpr ⟨hx, hfix x hx hfx⟩) with rfl | rfl
      · rw [one_mul, mul_one]
      · exact (hsP a ha).symm
    · have hxa : x * a ≠ a * x := fun h => hxM (Subgroup.mem_inf.mpr ⟨hx,
        Subgroup.mem_centralizer_singleton_iff.mpr h⟩)
      have hya : y * a ≠ a * y := fun h => hyM (Subgroup.mem_inf.mpr ⟨hy,
        Subgroup.mem_centralizer_singleton_iff.mpr h⟩)
      have ex := hcomm x hx hxa
      have ey := hcomm y hy hya
      refine Subgroup.mem_inf.mpr ⟨Q.mul_mem hx hy, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have : a * (x * y) * a⁻¹ = x * y := by
        calc a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) := by group
          _ = s * x * (s * y) := by rw [ex, ey]
          _ = s * (x * s) * y := by group
          _ = s * s * x * y := by rw [hsQ x hx]; group
          _ = x * y := by rw [hs2, one_mul]
      calc x * y * a = a * (x * y) * a⁻¹ * a := by rw [this]
        _ = a * (x * y) := by group
  exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (key hx).2

end S55

namespace S55

theorem Coord.mem_cenS {ε : (Fin 3 → ZMod 3) → G} {A : Subgroup G} (h : Coord ε A) {y : G}
    (h0 : y * ε ![1, 0, 0] = ε ![1, 0, 0] * y) (h1 : y * ε ![0, 1, 0] = ε ![0, 1, 0] * y)
    (h2 : y * ε ![0, 0, 1] = ε ![0, 0, 1] * y) : y ∈ CenS A := by
  refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
  obtain ⟨x, rfl⟩ := h.surj a ha
  have hx : x = (x 0 • ![1, 0, 0] + x 1 • ![0, 1, 0]) + x 2 • ![0, 0, 1] := by
    ext j; fin_cases j <;> simp
  rw [hx, h.add, h.add, h.smul, h.smul, h.smul]
  exact (((Commute.pow_left h0.symm _).mul_left (Commute.pow_left h1.symm _)).mul_left
    (Commute.pow_left h2.symm _)).eq

set_option maxRecDepth 100000 in
theorem span_three :
    ∀ z, dot (hypF 3) z = 0 → ∃ c d : ZMod 3, z = c • ![0, 0, 1] + d • ![1, 2, 0] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem filter_u₂ :
    Finset.univ.filter (fun i : Fin 13 => dot (hypF i) ![1, 2, 0] = 0) = {2, 3, 9, 10} := by
  decide

end S55

variable {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ s₀ : G}

section Frattini

variable (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀)
include h5

theorem FF81Sec5.A₁_comm {x y : G} (hx : x ∈ A₁sub b b₁ b₂ b₃) (hy : y ∈ A₁sub b b₁ b₂ b₃) :
    x * y = y * x := by
  obtain ⟨p, rfl⟩ := h5.coordA.surj x hx
  obtain ⟨q, rfl⟩ := h5.coordA.surj y hy
  rw [← h5.coordA.add, ← h5.coordA.add, add_comm]

theorem FF81Sec5.A₁_le_nor_W (i : Fin 13) : A₁sub b b₁ b₂ b₃ ≤ Nor (h5.W i) := fun a ha =>
  Subgroup.mem_normalizer_fintype fun y hy => by
    have hy' : y ∈ Op 2 (Cen s₀) ⊓ CenS (S55.hyp h5.εA i) := hy
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (h5.A₁_le_nor_S ha) y).mp hy'.1,
      Subgroup.mem_centralizer_iff.mpr fun c hc => ?_⟩
    have hcA := S55.hyp_le h5.coordA i hc
    have hyc := Subgroup.mem_centralizer_iff.mp hy'.2 c hc
    have hac := h5.A₁_comm ha hcA
    calc c * (a * y * a⁻¹) = (c * a) * y * a⁻¹ := by group
      _ = a * (c * y) * a⁻¹ := by rw [← hac]; group
      _ = a * (y * c) * a⁻¹ := by rw [hyc]
      _ = a * y * a⁻¹ * (a * c) * a⁻¹ := by group
      _ = a * y * a⁻¹ * (c * a) * a⁻¹ := by rw [hac]
      _ = a * y * a⁻¹ * c := by group

theorem FF81Sec5.εA_u₂ : h5.εA ![1, 2, 0] = b * b₁⁻¹ := by
  rw [show (![1, 2, 0] : Fin 3 → ZMod 3) = ![1, 0, 0] + -![0, 1, 0] by decide, h5.coordA.add,
    h5.coordA.neg, h5.εA_b, h5.εA_b₁]

theorem FF81Sec5.mem_cenS_hyp₃ {y : G} :
    y ∈ CenS (S55.hyp h5.εA 3) ↔
      y * (b₂ * b₃) = b₂ * b₃ * y ∧ y * (b * b₁⁻¹) = b * b₁⁻¹ * y := by
  rw [h5.coordA.cenS_hyp (by decide) (by decide) S55.span_three, h5.εA_u₃, h5.εA_u₂]

theorem FF81Sec5.mem_W₂_inf_W₃ (hKF : KF_Sp6Levi) {y : G} (hy : y ∈ h5.W 2 ⊓ h5.W 3) :
    y = 1 ∨ y = s₀ := by
  have hy' : y ∈ (Op 2 (Cen s₀) ⊓ CenS (S55.hyp h5.εA 2)) ⊓
      (Op 2 (Cen s₀) ⊓ CenS (S55.hyp h5.εA 3)) := hy
  obtain ⟨hyb, hyb₁⟩ := h5.mem_cenS_hyp₂.mp hy'.1.2
  obtain ⟨hyu, -⟩ := h5.mem_cenS_hyp₃.mp hy'.2.2
  refine h5.mem_S_cenS_A₁ hKF (Subgroup.mem_inf.mpr ⟨hy'.1.1, h5.coordA.mem_cenS ?_ ?_ ?_⟩)
  · rw [h5.εA_b]; exact hyb
  · rw [h5.εA_b₁]; exact hyb₁
  · rw [h5.εA_u₃]; exact hyu

end Frattini

section C23

variable (hKF : KF_Sp6Levi) (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀)
include hKF h5

theorem FF81Sec5.W₂_le_cenS_W₃ (hW2 : IsElemAb 2 3 (h5.W 2)) (hW1 : Nat.card (h5.W 1) = 2) :
    h5.W 2 ≤ CenS (h5.W 3) := by
  obtain ⟨g, hgH, hg⟩ := h5.gens hKF
  obtain ⟨hc, hs⟩ := S36.coprime_solvable_of_two (op_two_isPGroup s₀)
  have hbA : b ∈ A₁sub b b₁ b₂ b₃ := Subgroup.subset_closure (by simp)
  have huA : b₂ * b₃ ∈ A₁sub b b₁ b₂ b₃ := h5.εA_u₃ ▸ h5.coordA.mem _
  have hb3 : b ^ 3 = 1 := h5.εA_b ▸ h5.coordA.cube _
  have hu3 : (b₂ * b₃) ^ 3 = 1 := h5.εA_u₃ ▸ h5.coordA.cube _
  have hc2 : Nat.card (h5.W 2) = 8 := hW2.2
  have hc3 : Nat.card (h5.W 3) = 8 := by rw [h5.card_W hgH hg (r := 2) (w := [2]) (by decide), hc2]
  have hc9 : Nat.card (h5.W 9) = 2 := by rw [h5.card_W hgH hg (r := 1) (w := [0, 2]) (by decide), hW1]
  have hc10 : Nat.card (h5.W 10) = 2 := by
    rw [h5.card_W hgH hg (r := 1) (w := [0, 2, 1]) (by decide), hW1]
  have hint : ∀ y ∈ h5.W 2 ⊓ h5.W 3, y = 1 ∨ y = s₀ := fun y hy => h5.mem_W₂_inf_W₃ hKF hy
  have hs₀23 : s₀ ∈ h5.W 2 ⊓ h5.W 3 := Subgroup.mem_inf.mpr ⟨h5.s₀_mem_W 2, h5.s₀_mem_W 3⟩
  have hc23 : Nat.card ↥(h5.W 2 ⊓ h5.W 3) = 2 := card_eq_two_of_le h5.hs₀ hs₀23 hint
  have hc32 : Nat.card ↥(h5.W 3 ⊓ h5.W 2) = 2 := by rw [inf_comm]; exact hc23
  set D := Op 2 (Cen s₀) ⊓ Cen (b * b₁⁻¹) with hD
  have hcD : Nat.card D = 32 := by
    have hw := S55.card_cen_mul_pow_three h5.coordA h5.A₁_le_nor_S hc hs (x := ![1, 2, 0])
      (by decide)
    rw [S55.filter_u₂, h5.εA_u₂, h5.card_S_cenS_A₁ hKF] at hw
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true,
      Finset.prod_insert, Finset.prod_singleton] at hw
    change Nat.card D * 2 ^ 3 = Nat.card (h5.W 2) * (Nat.card (h5.W 3) *
      (Nat.card (h5.W 9) * Nat.card (h5.W 10))) at hw
    rw [hc2, hc3, hc9, hc10] at hw
    omega
  have hWD : ∀ i : Fin 13, dot (hypF i) ![1, 2, 0] = 0 → h5.W i ≤ D := fun i hi y hy => by
    have hy' : y ∈ Op 2 (Cen s₀) ⊓ CenS (S55.hyp h5.εA i) := hy
    refine Subgroup.mem_inf.mpr ⟨hy'.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← h5.εA_u₂]
    exact (Subgroup.mem_centralizer_iff.mp hy'.2 _ ((h5.coordA.mem_hyp i _).2 hi)).symm
  have h2D := hWD 2 (by decide)
  have h3D := hWD 3 (by decide)
  have hDp : IsPGroup 2 D := (op_two_isPGroup s₀).to_le inf_le_left
  have hab2 : ∀ x ∈ h5.W 2, ∀ y ∈ h5.W 2, x * y = y * x := by
    haveI := hW2.1
    intro x hx y hy
    exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥(h5.W 2))).comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hab3 : ∀ x ∈ h5.W 3, ∀ y ∈ h5.W 3, x * y = y * x := by
    rw [← h5.conjBy_W hgH hg (r := 2) (w := [2]) (by decide)]
    intro x hx y hy
    have := hab2 _ (mem_conjBy_iff.mp hx) _ (mem_conjBy_iff.mp hy)
    exact comm_of_conj_comm _ _ _ this
  have hbN2 := h5.A₁_le_nor_W 2 hbA
  have hbN3 := h5.A₁_le_nor_W 3 hbA
  have huN2 := h5.A₁_le_nor_W 2 huA
  have huN3 := h5.A₁_le_nor_W 3 huA
  have hfix3 : ∀ x ∈ h5.W 3, b * x * b⁻¹ = x → x ∈ h5.W 2 := by
    intro x hx hfx
    have hx' : x ∈ Op 2 (Cen s₀) ⊓ CenS (S55.hyp h5.εA 3) := hx
    obtain ⟨-, hxu₂⟩ := h5.mem_cenS_hyp₃.mp hx'.2
    have hxb : x * b = b * x := by
      calc x * b = b * x * b⁻¹ * b := by rw [hfx]
        _ = b * x := by group
    refine Subgroup.mem_inf.mpr ⟨hx'.1, h5.mem_cenS_hyp₂.mpr ⟨hxb, ?_⟩⟩
    have h1 : x * b₁⁻¹ = b₁⁻¹ * x := by
      calc x * b₁⁻¹ = b⁻¹ * (b * x) * b₁⁻¹ := by group
        _ = b⁻¹ * (x * b) * b₁⁻¹ := by rw [hxb]
        _ = b⁻¹ * (x * (b * b₁⁻¹)) := by group
        _ = b⁻¹ * (b * b₁⁻¹ * x) := by rw [hxu₂]
        _ = b₁⁻¹ * x := by group
    calc x * b₁ = b₁ * (b₁⁻¹ * x) * b₁ := by group
      _ = b₁ * (x * b₁⁻¹) * b₁ := by rw [h1]
      _ = b₁ * x := by group
  have hfix2 : ∀ x ∈ h5.W 2, (b₂ * b₃) * x * (b₂ * b₃)⁻¹ = x → x ∈ h5.W 3 := by
    intro x hx hfx
    have hx' : x ∈ Op 2 (Cen s₀) ⊓ CenS (S55.hyp h5.εA 2) := hx
    obtain ⟨hxb, hxb₁⟩ := h5.mem_cenS_hyp₂.mp hx'.2
    have hxu : x * (b₂ * b₃) = b₂ * b₃ * x := by
      calc x * (b₂ * b₃) = (b₂ * b₃) * x * (b₂ * b₃)⁻¹ * (b₂ * b₃) := by rw [hfx]
        _ = b₂ * b₃ * x := by group
    have hxb₁' : x * b₁⁻¹ = b₁⁻¹ * x := by
      calc x * b₁⁻¹ = b₁⁻¹ * (b₁ * x) * b₁⁻¹ := by group
        _ = b₁⁻¹ * (x * b₁) * b₁⁻¹ := by rw [hxb₁]
        _ = b₁⁻¹ * x := by group
    refine Subgroup.mem_inf.mpr ⟨hx'.1, h5.mem_cenS_hyp₃.mpr ⟨hxu, ?_⟩⟩
    calc x * (b * b₁⁻¹) = b * (x * b₁⁻¹) := by rw [← mul_assoc, hxb, mul_assoc]
      _ = b * b₁⁻¹ * x := by rw [hxb₁', ← mul_assoc]
  have hne2 : h5.W 2 ≠ D := fun h => by rw [← h, hc2] at hcD; omega
  have hne3 : h5.W 3 ≠ D := fun h => by rw [← h, hc3] at hcD; omega
  have hN32 : h5.W 3 ≤ Nor (h5.W 2) :=
    S55.le_nor_of_norm hDp h2D
      (S55.exists_mul_of_card h2D h3D (by rw [hc2, hc3, hcD, hc23])) hne2 hc3 hc32 hab3
      hb3 hbN2 hbN3 hfix3
  have hN23 : h5.W 2 ≤ Nor (h5.W 3) :=
    S55.le_nor_of_norm hDp h3D
      (S55.exists_mul_of_card h3D h2D (by rw [hc2, hc3, hcD, hc32])) hne3 hc2 hc23 hab2
      hu3 huN3 huN2 hfix2
  have hsc : ∀ i : Fin 13, ∀ x ∈ h5.W i, x * s₀ = s₀ * x := fun i x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (op_two_le s₀ (Subgroup.mem_inf.mp hx).1)
  have hint32 : ∀ y ∈ h5.W 3 ⊓ h5.W 2, y = 1 ∨ y = s₀ := fun y hy => hint y (by
    rw [inf_comm]; exact hy)
  have hs2 : s₀ * s₀ = 1 := by rw [← sq, ← h5.hs₀, pow_orderOf_eq_one]
  refine S55.le_cenS_of_norm hN23 hN32 hint32 hs2 (hsc 3) (hsc 2) hab3 hb3 (fun a ha => ?_)
    hbN3 hfix3
  have ha' : a ∈ Op 2 (Cen s₀) ⊓ CenS (S55.hyp h5.εA 2) := ha
  exact (h5.mem_cenS_hyp₂.mp ha'.2).1.symm

end C23

end CFSG.RankThree.PartTwo.Sec21.FF81
