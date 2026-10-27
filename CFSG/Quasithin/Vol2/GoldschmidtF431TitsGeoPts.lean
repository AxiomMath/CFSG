module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoDefs
public import CFSG.Quasithin.Recognition.F4Small

public section

namespace CFSG.Quasithin.TitsGeo

open CFSG.Open CFSG.Quasithin.F7 CFSG.Quasithin.RankTwoAmalgam.Completion

universe u w

variable {α : RankTwoAmalgam.{u}} {Y : Type w} [Group Y]

section Paths

variable {c : α.Completion Y} {n : ℕ}

theorem vtype_path_succ (p : GPath c.graph n) {i : ℕ} (hi : i < n) :
    CosetGeom.vtype (p (i + 1)) = !CosetGeom.vtype (p i) := by
  have := CosetGeom.vtype_ne_of_adj (p.adj i hi)
  cases h1 : CosetGeom.vtype (p i) <;> cases h2 : CosetGeom.vtype (p (i + 1)) <;>
    simp_all

theorem vtype_path_even (p : GPath c.graph n) : ∀ {i : ℕ}, i ≤ n → Even i →
    CosetGeom.vtype (p i) = CosetGeom.vtype (p 0)
  | 0, _, _ => rfl
  | 1, _, he => absurd he (by decide)
  | i + 2, hi, he => by
    have h1 := vtype_path_succ p (show i + 1 < n by omega)
    have h2 := vtype_path_succ p (show i < n by omega)
    have h3 := vtype_path_even p (show i ≤ n by omega) (by
      rcases he with ⟨r, hr⟩
      exact ⟨r - 1, by omega⟩)
    rw [h1, h2, h3]
    simp

theorem vtype_path_odd (p : GPath c.graph n) {i : ℕ} (hi : i ≤ n) (ho : Odd i) :
    CosetGeom.vtype (p i) = !CosetGeom.vtype (p 0) := by
  obtain ⟨j, rfl⟩ := ho
  have h1 := vtype_path_succ p (show 2 * j < n by omega)
  rw [h1, vtype_path_even p (show 2 * j ≤ n by omega) ⟨j, by omega⟩]

theorem rev_mem_nbPaths {a : c.Γ} {p : GPath c.graph n} (hp : p ∈ GPath.nbPaths c.graph a n) :
    p.rev ∈ GPath.nbPaths c.graph (p n) n := by
  refine ⟨?_, hp.2.rev⟩
  rw [GPath.rev_apply _ (Nat.zero_le n), Nat.sub_zero]

theorem rev_apply_last (p : GPath c.graph n) : p.rev n = p 0 := by
  rw [GPath.rev_apply _ le_rfl, Nat.sub_self]

theorem hbip (c : α.Completion Y) :
    ∀ a b : c.Γ, c.graph.Adj a b → CosetGeom.vtype a ≠ CosetGeom.vtype b :=
  fun _ _ h => CosetGeom.vtype_ne_of_adj h

end Paths

namespace TitsHyp

variable {c : α.Completion Y} [Finite Y] {k : ℕ} (T : TitsHyp c k)

include T

theorem hval : ∀ v a b : c.Γ, ∃ w, c.graph.Adj v w ∧ w ≠ a ∧ w ≠ b :=
  exists_nbr_ne T.faithful T.thick1 T.thick2

theorem pt_F35 {a : c.Γ} (ha : CosetGeom.vtype a = false) {p : GPath c.graph (k + 2)}
    (hp : p ∈ GPath.nbPaths c.graph a (k + 2)) :
    GPath.F35Conclusion c.graph c.G0 a (k + 1) p :=
  GPath.lemma_F35 (T.hval) (T.transPt a ha) (connected_graph c) (hbip c) (by have := T.hk; omega) hp

theorem ln_F35 {a : c.Γ} (ha : CosetGeom.vtype a = true) {p : GPath c.graph (k + 1)}
    (hp : p ∈ GPath.nbPaths c.graph a (k + 1)) :
    GPath.F35Conclusion c.graph c.G0 a k p :=
  GPath.lemma_F35 (T.hval) (T.transLn a ha) (connected_graph c) (hbip c) T.hk hp

theorem pt_dist {a : c.Γ} (ha : CosetGeom.vtype a = false) {i : ℕ} (hi : i ≤ k + 1)
    {q : GPath c.graph i} (hq : q ∈ GPath.nbPaths c.graph a i) : c.graph.dist a (q i) = i := by
  obtain ⟨p, hp⟩ := GPath.exists_nbPaths T.hval a (k + 2)
  exact (T.pt_F35 ha hp).2.1 i hi q hq

theorem pt_end {a : c.Γ} (ha : CosetGeom.vtype a = false) {p : GPath c.graph (k + 2)}
    (hp : p ∈ GPath.nbPaths c.graph a (k + 2)) : c.graph.dist a (p (k + 2)) = k + 2 :=
  (T.pt_F35 ha hp).2.2.2.2.2.2 (fun y hy hne => T.noFix a ha p hp y hy hne)

theorem pt_uniq {a : c.Γ} (ha : CosetGeom.vtype a = false) {n : ℕ} (hn : n < k + 2)
    {r : GPath c.graph n} (hr : r ∈ GPath.nbPaths c.graph a n) {t : GPath c.graph n}
    (ht0 : t 0 = a) (htn : t n = r n) (htg : t.IsGeodesic) : t = r := by
  obtain ⟨p, hp, hpr⟩ := GPath.exists_extend_to T.hval (show n ≤ k + 2 by omega) hr
  have hF := T.pt_F35 ha hp
  rcases Nat.lt_or_ge n (k + 1) with h1 | h1
  · have := hF.2.2.2.1 n h1 t ht0 (by rw [htn, ← hpr, GPath.take_apply_of_le _ _ _ le_rfl]) htg
    rw [this, hpr]
  · have hn1 : n = k + 1 := by omega
    subst hn1
    rcases hF.2.2.2.2.2.1 with h3 | ⟨hd, -⟩
    · have := (h3 p hp).2 t ht0 htg (by rw [htn, ← hpr, GPath.take_apply_of_le _ _ _ le_rfl])
      rw [this, hpr]
    · exfalso
      have := T.pt_end ha hp
      have := hd (p (k + 2))
      omega

end TitsHyp

end CFSG.Quasithin.TitsGeo
