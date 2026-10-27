module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P55Shift
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P58Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5StmtA

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P58

theorem adj' (ℓ : Line Γ) {i j : ℤ} (h : j = i + 1) : Γ.Adj (ℓ.vert i) (ℓ.vert j) := by
  subst h
  exact ℓ.adj i

theorem nb' (ℓ : Line Γ) {i j : ℤ} (h : j = i + 2) : ℓ.vert i ≠ ℓ.vert j := by
  subst h
  exact ℓ.nb i

section LineFacts

variable {ℓ : Line Γ} {z : G} {a b tL tR : ℤ}

theorem central_last (hd : ℓ.IsCoreFix z a b tL tR) {i j : ℤ} (hi : i = b - 1) (hj : j = b) :
    ∀ h : G, h • ℓ.vert i = ℓ.vert i → h • ℓ.vert j = ℓ.vert j → h * z = z * h := by
  intro h h1 h2
  rw [hi] at h1
  rw [hj] at h2
  have hc := hd.core.2.2.1 (b - 1) (by have := P55.fix_a_lt hd; omega) (by omega)
  refine hc.2 h ⟨MulAction.mem_stabilizer_iff.2 h1, MulAction.mem_stabilizer_iff.2 ?_⟩
  rw [sub_add_cancel]
  exact h2

theorem central_first (hd : ℓ.IsCoreFix z a b tL tR) {i j : ℤ} (hi : i = a) (hj : j = a + 1) :
    ∀ h : G, h • ℓ.vert i = ℓ.vert i → h • ℓ.vert j = ℓ.vert j → h * z = z * h := by
  intro h h1 h2
  rw [hi] at h1
  rw [hj] at h2
  have hc := hd.core.2.2.1 a le_rfl (P55.fix_a_lt hd)
  exact hc.2 h ⟨MulAction.mem_stabilizer_iff.2 h1, MulAction.mem_stabilizer_iff.2 h2⟩

theorem f54_right {F : FanTree Γ G} (h54 : Fan54 F) (h40 : Fan40 F) (hZ : z ∈ ℓ.Zc)
    (hc : ℓ.IsCoreC z a b) {i j : ℤ} (hi : i = b) (hj : j = b - 1) :
    ∀ x : G, x • ℓ.vert i = ℓ.vert i → x • ℓ.vert j ≠ ℓ.vert j → x * z ≠ z * x := by
  intro x h1 h2
  rw [hi] at h1
  rw [hj] at h2
  exact h54 h40 ℓ z a b hZ hc b (b - 1) (Or.inl ⟨rfl, rfl⟩) x
    (MulAction.mem_stabilizer_iff.2 h1) (fun h => h2 (MulAction.mem_stabilizer_iff.1 h))

theorem f54_left {F : FanTree Γ G} (h54 : Fan54 F) (h40 : Fan40 F) (hZ : z ∈ ℓ.Zc)
    (hc : ℓ.IsCoreC z a b) {i j : ℤ} (hi : i = a) (hj : j = a + 1) :
    ∀ x : G, x • ℓ.vert i = ℓ.vert i → x • ℓ.vert j ≠ ℓ.vert j → x * z ≠ z * x := by
  intro x h1 h2
  rw [hi] at h1
  rw [hj] at h2
  exact h54 h40 ℓ z a b hZ hc a (a + 1) (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) x
    (MulAction.mem_stabilizer_iff.2 h1) (fun h => h2 (MulAction.mem_stabilizer_iff.1 h))

theorem edgeCirc_fix' {i j : ℤ} {g : G} (hg : g ∈ ℓ.edgeCirc (G := G) i) (hj : j = i + 1) :
    g • ℓ.vert i = ℓ.vert i ∧ g • ℓ.vert j = ℓ.vert j := by
  subst hj
  exact ℓ.edgeCirc_fix hg

end LineFacts

theorem final3 (F : FanTree Γ G) (h40 : Fan40 F) (h51a : Fan51a F) (ℓ : Line Γ) (α : ℤ) {u : G}
    (hu1 : u ≠ 1) (hc₀ : ∀ g ∈ ℓ.edgeCirc (G := G) α, g * u = u * g)
    (hc₂ : ∀ g ∈ ℓ.edgeCirc (G := G) (α + 2), g * u = u * g)
    (hv : u • ℓ.vert (α + 1) = ℓ.vert (α + 1)) (hq : u • ℓ.vert (α + 2) = ℓ.vert (α + 2)) :
    False := by
  have hn : ¬ LineSingLe Γ G ℓ (3 - 1) := P58.not_lineSingLe h40 ℓ (by norm_num)
  have e : ((3 - 1 : ℕ) : ℤ) = 2 := by norm_num
  obtain ⟨x₁, hx₁, hx₁o⟩ := h51a h40 ℓ α 3 (by norm_num) hn 1 le_rfl (by norm_num)
  obtain ⟨x₂, hx₂, hx₂o⟩ := h51a h40 ℓ α 3 (by norm_num) hn 2 (by norm_num) (by norm_num)
  rw [e] at hx₁ hx₂
  have hMc : ∀ h ∈ Subgroup.closure (ℓ.edgeCirc (G := G) α ∪ ℓ.edgeCirc (G := G) (α + 2)),
      h * u = u * h := by
    intro h hh
    have hle : Subgroup.closure (ℓ.edgeCirc (G := G) α ∪ ℓ.edgeCirc (G := G) (α + 2)) ≤
        Subgroup.centralizer ({u} : Set G) := by
      rw [Subgroup.closure_le]
      intro g hg
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases hg with hg | hg
      · exact hc₀ g hg
      · exact hc₂ g hg
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hh)
  have h1 : (α + ((1 : ℕ) : ℤ)) = α + 1 := by norm_num
  have h2 : (α + ((2 : ℕ) : ℤ)) = α + 2 := by norm_num
  try rw [h1] at hx₁
  rw [h1] at hx₁o
  try rw [h2] at hx₂
  rw [h2] at hx₂o
  have hu_loc := P58.locTr_of_pow F hx₁.1 hx₁.2 hx₁o
  have hw_loc := P58.locTr_of_pow F hx₂.1 hx₂.2 hx₂o
  have hadj : Γ.Adj (ℓ.vert (α + 1)) (ℓ.vert (α + 2)) := P58.adj' ℓ (by ring)
  exact hu1 (P58.eq_one_of_locTr F hadj hMc hv hq hu_loc hw_loc)

end P58

end CFSG.Quasithin.Fan86
