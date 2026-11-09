module

public import CFSG.GH74.GLS.C3.Layer2.FinModelTabInputs
public import Certificates.Kernel.Direct.C5041Gen

public section

namespace CertificateChecks.KernelDirect.C5041

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.C3 CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.Model
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2

variable {n : ℕ} [NeZero n]

def c1 (t : Tab n) : Bool := (List.finRange 64).all (fun i => decide (t.el.get i ∈ Tl n))
def c2 (t : Tab n) : Bool := (Tl n).all (fun g => (List.finRange 64).any fun i => decide (t.el.get i = g))
def c3 (t : Tab n) : Bool := (List.finRange 64).all (fun i => (List.finRange 64).all fun j =>
    imp (decide (t.el.get i = t.el.get j)) (i == j))
def c4 (t : Tab n) : Bool := (List.finRange 64).all (fun i => (List.finRange 64).all fun j =>
    decide (t.el.get (t.mulT i j) = t.el.get i * t.el.get j))
def c5 (t : Tab n) : Bool := decide (t.el.get t.one = 1)
def c6 (t : Tab n) : Bool :=
  (List.finRange 64).all (fun i => decide (t.el.get (t.inv.get i) = (t.el.get i)⁻¹))
def c7 (t : Tab n) : Bool := decide (t.el.get t.x0i = x0 n)
def c8 (t : Tab n) : Bool :=
  (List.finRange 64).all (fun i => evalW t.mulT t.one t.gens.get (t.words.get i) == i)
def c9 (t : Tab n) : Bool := (List.finRange 64).all (fun i => (List.finRange 64).all fun j =>
    imp (t.isInv i && t.isInv j && t.cls.get i == t.cls.get j) (t.rep.get i == t.rep.get j))
def c10 (t : Tab n) : Bool := (List.finRange 64).all (fun j => imp (t.isInv j)
    (decide (∃ σ : Perm (Fin n), σ * (t.el.get (t.rep.get j)).1 * σ⁻¹ = (t.el.get j).1 ∧
      ∃ d ∈ Dl, d * (t.el.get (t.rep.get j)).2 * d⁻¹ = (t.el.get j).2 ∧ sign σ = sign d)))
def c11 (t : Tab n) : Bool :=
  (List.finRange 64).all (fun i => (t.isQ.get i == true) == decide ((t.el.get i).1 = 1))
def c12 (t : Tab n) : Bool :=
  (List.finRange 64).all (fun i => t.nm.get i == numMoved (emb n (t.el.get i)))
def c13 (t : Tab n) : Bool := (List.finRange 64).all (fun i => decide (a0perm n * emb n (t.el.get i) *
    (a0perm n)⁻¹ = emb n (t.el.get (t.astar.get i))))
def c14 (t : Tab n) : Bool := decide (∀ σ : Perm (Fin n), σ ≠ 1 → σ * σ * σ = 1 → σ ∈ t.o3)
def c15 (t : Tab n) : Bool := t.o3.all (fun σ => decide (σ ≠ 1 ∧ σ * σ * σ = 1))
def c16 (t : Tab n) : Bool := t.useW == decide (n = 7)

def swapsP (l : List (Fin n × Fin n)) : Perm (Fin n) := (l.map fun p => swap p.1 p.2).prod

def c10w (t : Tab n) (W : List (List (Fin n × Fin n))) : Bool :=
  (List.finRange 64).all (fun j => imp (t.isInv j)
    (decide (swapsP (W.getD j.1 []) * (t.el.get (t.rep.get j)).1 * (swapsP (W.getD j.1 []))⁻¹ =
        (t.el.get j).1) &&
      Dl.any fun d => decide (d * (t.el.get (t.rep.get j)).2 * d⁻¹ = (t.el.get j).2) &&
        decide (sign (swapsP (W.getD j.1 [])) = sign d)))

theorem imp_mono {p q r : Bool} (h : q = true → r = true) : imp p q = true → imp p r = true := by
  cases p
  · exact fun _ => rfl
  · exact h

theorem c10_of (t : Tab n) (W : List (List (Fin n × Fin n))) (h : c10w t W = true) :
    c10 t = true := by
  simp only [c10, c10w, List.all_eq_true] at h ⊢
  intro j hj
  refine imp_mono (fun hq => ?_) (h j hj)
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at hq ⊢
  obtain ⟨h1, d, hd, h2, h3⟩ := hq
  exact ⟨_, h1, d, hd, h2, h3⟩

def w6 : List (List (Fin 6 × Fin 6)) :=
  [[], [(4, 5)], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
    [(0, 2), (1, 3)], [(0, 2), (1, 3)], [], [], [(2, 3), (4, 5)], [(2, 3)], [(2, 3)], [(2, 3)],
    [(0, 4), (4, 2), (1, 5), (5, 3)], [(0, 4), (4, 2), (1, 5), (5, 3)], [], [],
    [(1, 3), (3, 2)], [(1, 3), (3, 2)], [], [], [(1, 2), (2, 3)], [(1, 2), (2, 3), (4, 5)],
    [(1, 2), (2, 3)], [(1, 2), (2, 3)], [], [], [], [], [], [], [], [],
    [(1, 4), (4, 2), (2, 5), (5, 3)], [(1, 4), (4, 3), (2, 5)], [(1, 4), (4, 2), (2, 5), (5, 3)],
    [(1, 4), (4, 2), (2, 5), (5, 3)], [(0, 2), (2, 5), (5, 1), (1, 4)], [(0, 2), (2, 5), (1, 4)],
    [(0, 2), (2, 5), (5, 1), (1, 4)], [(0, 2), (2, 5), (5, 1), (1, 4)], [(1, 2)], [(1, 2)],
    [], [], [], [(4, 5)], [], []]

def w7 : List (List (Fin 7 × Fin 7)) :=
  [[], [(5, 6)], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
    [(0, 2), (1, 3)], [(0, 2), (1, 3)], [], [], [(2, 3), (5, 6)], [(2, 3)], [(2, 3)], [(2, 3)],
    [(0, 4), (4, 2), (1, 5), (5, 3)], [(0, 4), (4, 2), (1, 5), (5, 3)], [], [],
    [(1, 3), (3, 2)], [(1, 3), (3, 2)], [], [], [(1, 2), (2, 3)], [(1, 2), (2, 3), (5, 6)],
    [(1, 2), (2, 3)], [(1, 2), (2, 3)], [], [], [], [], [], [], [], [],
    [(1, 4), (4, 2), (2, 5), (5, 3)], [(1, 4), (4, 2), (2, 5), (5, 6), (6, 3)],
    [(1, 4), (4, 2), (2, 5), (5, 3)], [(1, 4), (4, 2), (2, 5), (5, 3)],
    [(0, 2), (2, 5), (5, 1), (1, 4)], [(0, 2), (2, 5), (5, 6), (6, 1), (1, 4)],
    [(0, 2), (2, 5), (5, 1), (1, 4)], [(0, 2), (2, 5), (5, 1), (1, 4)], [(1, 2)], [(1, 2)],
    [], [], [], [(5, 6)], [], []]

theorem c4_of (hn : n = 6 ∨ n = 7) (h1 : c1 (mkTab n) = true) (h2 : c2 (mkTab n) = true) :
    c4 (mkTab n) = true := by
  simp only [c1, c2, c4, List.all_eq_true, List.any_eq_true, decide_eq_true_eq,
    List.mem_finRange, true_and, forall_const] at h1 h2 ⊢
  exact fun i j => mulT_mkTab_spec hn h1 h2 i j

theorem c14_of (hn : n ≤ 8) : c14 (mkTab n) = true :=
  decide_eq_true fun σ h1 h3 => mem_o3List hn σ h1 h3

theorem validB_of (t : Tab n) (h1 : c1 t = true) (h2 : c2 t = true) (h3 : c3 t = true)
    (h4 : c4 t = true) (h5 : c5 t = true) (h6 : c6 t = true) (h7 : c7 t = true)
    (h8 : c8 t = true) (h9 : c9 t = true) (h10 : c10 t = true) (h11 : c11 t = true)
    (h12 : c12 t = true) (h13 : c13 t = true) (h14 : c14 t = true) (h15 : c15 t = true)
    (h16 : c16 t = true) : t.validB = true := by
  unfold Tab.validB Tab.checks
  simp only [List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_eq_true]
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem v6_1 : c1 (mkTab 6) = true := by decide +kernel
theorem v6_2 : c2 (mkTab 6) = true := by decide +kernel
theorem v6_3 : c3 (mkTab 6) = true := by decide +kernel
theorem v6_4 : c4 (mkTab 6) = true := c4_of (Or.inl rfl) v6_1 v6_2
theorem v6_5 : c5 (mkTab 6) = true := by decide +kernel
theorem v6_6 : c6 (mkTab 6) = true := by decide +kernel
theorem v6_7 : c7 (mkTab 6) = true := by decide +kernel
theorem v6_8 : c8 (mkTab 6) = true := by decide +kernel
theorem v6_9 : c9 (mkTab 6) = true := by decide +kernel
theorem v6_10w : c10w (mkTab 6) w6 = true := by decide +kernel
theorem v6_10 : c10 (mkTab 6) = true := c10_of _ _ v6_10w
theorem v6_11 : c11 (mkTab 6) = true := by decide +kernel
theorem v6_12 : c12 (mkTab 6) = true := by decide +kernel
theorem v6_13 : c13 (mkTab 6) = true := by decide +kernel
theorem v6_14 : c14 (mkTab 6) = true := c14_of (by decide)
theorem v6_15 : c15 (mkTab 6) = true := by decide +kernel
theorem v6_16 : c16 (mkTab 6) = true := by decide +kernel

theorem v7_1 : c1 (mkTab 7) = true := by decide +kernel
theorem v7_2 : c2 (mkTab 7) = true := by decide +kernel
theorem v7_3 : c3 (mkTab 7) = true := by decide +kernel
theorem v7_4 : c4 (mkTab 7) = true := c4_of (Or.inr rfl) v7_1 v7_2
theorem v7_5 : c5 (mkTab 7) = true := by decide +kernel
theorem v7_6 : c6 (mkTab 7) = true := by decide +kernel
theorem v7_7 : c7 (mkTab 7) = true := by decide +kernel
theorem v7_8 : c8 (mkTab 7) = true := by decide +kernel
theorem v7_9 : c9 (mkTab 7) = true := by decide +kernel
theorem v7_10w : c10w (mkTab 7) w7 = true := by decide +kernel
theorem v7_10 : c10 (mkTab 7) = true := c10_of _ _ v7_10w
theorem v7_11 : c11 (mkTab 7) = true := by decide +kernel
theorem v7_12 : c12 (mkTab 7) = true := by decide +kernel
theorem v7_13 : c13 (mkTab 7) = true := by decide +kernel
theorem v7_14 : c14 (mkTab 7) = true := c14_of (by decide)
theorem v7_15 : c15 (mkTab 7) = true := by decide +kernel
theorem v7_16 : c16 (mkTab 7) = true := by decide +kernel

theorem validB6_0 : (mkTab 6).validB = true :=
  validB_of _ v6_1 v6_2 v6_3 v6_4 v6_5 v6_6 v6_7 v6_8 v6_9 v6_10 v6_11 v6_12 v6_13 v6_14 v6_15
    v6_16

theorem validB7_1 : (mkTab 7).validB = true :=
  validB_of _ v7_1 v7_2 v7_3 v7_4 v7_5 v7_6 v7_7 v7_8 v7_9 v7_10 v7_11 v7_12 v7_13 v7_14 v7_15
    v7_16

end CertificateChecks.KernelDirect.C5041
