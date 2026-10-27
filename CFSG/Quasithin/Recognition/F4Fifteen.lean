module

public import CFSG.Quasithin.Recognition.F4Apart

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Quasithin.F7 CFSG.Quasithin.RankTwoAmalgam.Completion

universe u w w'

namespace GPath

variable {V : Type u} {Γ : SimpleGraph V}

theorem exists_opposite_of_polygon {c : V → Bool} (hΓ : Γ.Connected)
    (hc : ∀ a b, Γ.Adj a b → c a ≠ c b) {m : ℕ} (hU : UniqueGeod Γ m) (hm : 2 ≤ m) {S : Set V}
    (hS : IsPolygon Γ S (2 * m)) {a : V} (ha : a ∈ S) :
    (∃ b ∈ S, Γ.dist a b = m) ∧ ∃ w ∈ S, Γ.Adj a w := by
  obtain ⟨φ⟩ := hS
  have hM : 0 < 2 * m := by omega
  have hM3 : 3 ≤ 2 * m := by omega
  obtain ⟨i₀, hi₀⟩ := φ.surjective ⟨a, ha⟩
  have hz0 : polyWalk hM φ i₀.val 0 = a := by
    rw [polyWalk_zero hM φ i₀, hi₀]
  have hadj := polyWalk_adj hM φ i₀.val hM3
  have hnb := polyWalk_nb hM φ i₀.val hM3
  refine ⟨⟨polyWalk hM φ i₀.val m, polyWalk_mem hM φ i₀.val m, ?_⟩,
    ⟨polyWalk hM φ i₀.val 1, polyWalk_mem hM φ i₀.val 1, ?_⟩⟩
  · have := window_dist hΓ hc hU (polyWalk hM φ i₀.val) hadj hnb 0 (le_refl m)
    rwa [hz0, Nat.zero_add] at this
  · have := hadj 0
    rwa [hz0, Nat.zero_add] at this

end GPath

namespace RankTwoAmalgam.Completion

variable {α : RankTwoAmalgam.{u}} {Y : Type w'} [Group Y] {c : α.Completion Y}

theorem exists_smul_of_vtype_eq (u v : c.Γ) (h : CosetGeom.vtype u = CosetGeom.vtype v) :
    ∃ g : c.G0, g • u = v := by
  obtain ⟨g₁, hg₁⟩ := exists_smul_eq_baseVert c u
  obtain ⟨g₂, hg₂⟩ := exists_smul_eq_baseVert c v
  rw [h] at hg₁
  refine ⟨g₂ * g₁⁻¹, ?_⟩
  have h1 : g₁⁻¹ • u = c.baseVert (CosetGeom.vtype v) := inv_smul_eq_iff.mpr hg₁.symm
  rw [mul_smul, h1]
  exact hg₂

end RankTwoAmalgam.Completion

namespace GPath

variable {V : Type u} {Γ : SimpleGraph V} {H : Type*} [Group H] [MulAction H V] [GraphAction H Γ]

theorem image_smul_verts {n : ℕ} (g : H) (p : GPath Γ n) :
    (fun v => g • v) '' p.verts = (g • p).verts := by
  ext v
  constructor
  · rintro ⟨x, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨p i, ⟨i, hi, rfl⟩, rfl⟩

end GPath

namespace RankTwoAmalgam.Completion

variable {α : RankTwoAmalgam.{u}} {Y : Type w'} [Group Y] {c : α.Completion Y} {m : ℕ}

theorem smul_mem_geods (g : c.G0) {a b : c.Γ} {p : GPath c.graph m} (hp : p ∈ c.geods m a b) :
    g • p ∈ c.geods m (g • a) (g • b) := by
  obtain ⟨h0, hm, hg⟩ := hp
  refine ⟨by rw [GPath.smul_apply, h0], by rw [GPath.smul_apply, hm], ?_⟩
  show c.graph.dist ((g • p) 0) ((g • p) m) = m
  rw [GPath.smul_apply, GPath.smul_apply, GPath.dist_smul (connected_graph c)]
  exact hg

end RankTwoAmalgam.Completion

end CFSG.Quasithin
