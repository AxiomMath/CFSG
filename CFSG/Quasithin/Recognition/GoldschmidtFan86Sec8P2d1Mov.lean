module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2d1Comm

public section

namespace CFSG.Quasithin.Fan86.P2d1

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem comm_moves_abstract (F : FanTree Γ G) {Y Y' : G} {a b δ t o : V}
    (hY'sq : Y' * Y' = 1)
    (hYfix : ∀ v, Γ.dist o v ≤ 4 → (Y • v = v ↔ (Γ.dist a v ≤ 2 ∨ Γ.dist b v ≤ 2)))
    (hYo : Y • o = o) (hY'o : Y' • o = o) (hY'b : Y' • b = b) (hY'a : Y' • a = t)
    (hYt : Y • t = t) (hd1 : Γ.dist t δ = 4) (hd2 : Γ.dist o δ = 4) (hd3 : Γ.dist a δ = 2)
    (hd4 : Γ.dist b δ = 3) : (Y * Y' * Y * Y') • δ ≠ δ := by
  intro hfix
  have hY'sq' : ∀ v : V, Y' • (Y' • v) = v := fun v => by rw [← mul_smul, hY'sq, one_smul]
  have hY't : Y' • t = a := by rw [← hY'a, hY'sq']
  have hu1o : Γ.dist o (Y' • δ) = 4 := by
    have := dist_smul F Y' o δ
    rwa [hY'o, hd2] at this
  have hu1b : Γ.dist b (Y' • δ) = 3 := by
    have := dist_smul F Y' b δ
    rwa [hY'b, hd4] at this
  have hu1a : Γ.dist a (Y' • δ) = 4 := by
    have := dist_smul F Y' t δ
    rwa [hY't, hd1] at this
  have hmoved : Y • (Y' • δ) ≠ Y' • δ := fun h => by
    have := (hYfix _ (by omega)).1 h
    omega
  have e1 : Γ.dist t (Y • (Y' • δ)) = Γ.dist t (Y' • δ) := by
    have := dist_smul F Y t (Y' • δ)
    rwa [hYt] at this
  have e2 : Γ.dist t (Y' • δ) = 2 := by
    have := dist_smul F Y' a δ
    rwa [hY'a, hd3] at this
  have e3 : Γ.dist a (Y' • (Y • (Y' • δ))) = Γ.dist t (Y • (Y' • δ)) := by
    have := dist_smul F Y' t (Y • (Y' • δ))
    rwa [hY't] at this
  have e4 : Γ.dist o (Y' • (Y • (Y' • δ))) = Γ.dist o (Y • (Y' • δ)) := by
    have := dist_smul F Y' o (Y • (Y' • δ))
    rwa [hY'o] at this
  have e5 : Γ.dist o (Y • (Y' • δ)) = Γ.dist o (Y' • δ) := by
    have := dist_smul F Y o (Y' • δ)
    rwa [hYo] at this
  have hfix3 : Y • (Y' • (Y • (Y' • δ))) = Y' • (Y • (Y' • δ)) :=
    (hYfix _ (by omega)).2 (Or.inl (by omega))
  have hv : (Y * Y' * Y * Y') • δ = Y' • (Y • (Y' • δ)) := by
    simp only [mul_smul]
    exact hfix3
  rw [hv] at hfix
  apply hmoved
  have := congrArg (fun x => Y' • x) hfix
  simp only [hY'sq'] at this
  exact this

theorem comm_moves_delta (h71c : Fan71c F L) (h81 : Fan81 F L) {i j : Fin 5} {l₁ l₂ m₁ m₂ : V}
    (hZ : IsZ2Pair Γ G α (D.alpha i) (D.beta i) l₁ l₂ 2)
    (hZ' : IsZ2Pair Γ G α (D.alpha j) (D.beta j) m₁ m₂ 2) (hij : i ≠ j) :
    fcomm (L.z l₁ * L.z l₂) (L.z m₁ * L.z m₂) • D.delta i ≠ D.delta i := by
  have hYsq := P2c.pair_sq D h71c hZ
  have hY'sq := P2c.pair_sq D h71c hZ'
  obtain ⟨t, hts, -, hit, hYt⟩ := P2c.pair_alpha_third D h71c h81 hZ' hij
  have hβt : Γ.Adj (D.beta i) t := by
    have : t ∈ Γ.neighborSet (D.beta i) := by rw [hts]; simp
    exact this
  have hdt : Γ.dist (D.delta i) t = 4 := by
    have h1 := D.dist_alpha_delta F i
    have h2 := D.dist_beta_delta F i
    rw [SimpleGraph.dist_comm] at h1 h2
    have := IsTree.dist_succ_of_ne F.isTree (D.adj_beta_alpha i) hβt hit (w := D.delta i)
      (by omega)
    omega
  rw [fcomm_invol hYsq hY'sq]
  refine comm_moves_abstract F (a := D.alpha i) (b := D.beta i) (t := t) (o := α) hY'sq
    (fun v hv => P2c.pair_fixed_iff D h81 hZ hv) (pair_fix_alpha D h81 hZ)
    (pair_fix_alpha D h81 hZ') (P2c.pair_fix_beta D h81 hZ' i) hYt
    (pair_fix_ball D h81 hZ (by rw [SimpleGraph.dist_eq_one_iff_adj.2 hβt]; norm_num)) ?_
    (D.dist_delta F i) (D.dist_alpha_delta F i) (D.dist_beta_delta F i)
  rw [SimpleGraph.dist_comm]
  exact hdt

theorem comm_moves_delta' (h71c : Fan71c F L) (h81 : Fan81 F L) {i j : Fin 5} {l₁ l₂ m₁ m₂ : V}
    (hZ : IsZ2Pair Γ G α (D.alpha i) (D.beta i) l₁ l₂ 2)
    (hZ' : IsZ2Pair Γ G α (D.alpha j) (D.beta j) m₁ m₂ 2) (hij : i ≠ j) :
    fcomm (L.z l₁ * L.z l₂) (L.z m₁ * L.z m₂) • D.delta j ≠ D.delta j := by
  intro h
  apply comm_moves_delta D h71c h81 hZ' hZ hij.symm
  rw [← F87.fcomm_inv_eq] at h
  exact (inv_smul_eq_iff.1 h).symm

end CFSG.Quasithin.Fan86.P2d1
