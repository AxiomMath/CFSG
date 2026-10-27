module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5Defs

public section

namespace CFSG.Quasithin.Fan86

namespace P514

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

open scoped Classical in
@[expose] noncomputable def Lb (z : G) (α u : V) : G :=
  if h : ∃ g : G, g • α = u then h.choose * z * h.choose⁻¹ else 1

theorem Lb_eq {z : G} {α u : V} (hz : z ∈ Cinv G α) {g : G} (hg : g • α = u) :
    Lb z α u = g * z * g⁻¹ := by
  have h : ∃ g : G, g • α = u := ⟨g, hg⟩
  have hc : h.choose • α = u := h.choose_spec
  have e : Lb z α u = h.choose * z * h.choose⁻¹ := by simp only [Lb, h, dite_true]
  rw [e]
  generalize h.choose = c at hc ⊢
  have hk : c⁻¹ * g ∈ MulAction.stabilizer G α := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, hg, ← hc, inv_smul_smul]
  have hcom : (c⁻¹ * g) * z = z * (c⁻¹ * g) := hz.2.2.2 _ hk
  calc c * z * c⁻¹ = c * (z * (c⁻¹ * g)) * g⁻¹ := by group
    _ = c * ((c⁻¹ * g) * z) * g⁻¹ := by rw [hcom]
    _ = g * z * g⁻¹ := by group

theorem Lb_self {z : G} {α : V} (hz : z ∈ Cinv G α) : Lb z α α = z := by
  rw [Lb_eq hz (g := 1) (one_smul G α)]
  simp

theorem exists_conj_of_adj (F : FanTree Γ G) {α o u : V} (h1 : Γ.Adj α o) (h2 : Γ.Adj o u) :
    ∃ g : G, g • α = u :=
  F.exists_smul_of_walk_even 1 (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2
    SimpleGraph.Walk.nil)) rfl

theorem Lb_conj {z : G} {α u : V} (hz : z ∈ Cinv G α) (hu : ∃ g : G, g • α = u) (k : G) :
    k * Lb z α u * k⁻¹ = Lb z α (k • u) := by
  obtain ⟨g, hg⟩ := hu
  rw [Lb_eq hz hg, Lb_eq hz (g := k * g) (by rw [mul_smul, hg])]
  group

theorem Lb_cinv {z : G} {α u : V} (hz : z ∈ Cinv G α) (hu : ∃ g : G, g • α = u) :
    Lb z α u ∈ Cinv G u := by
  obtain ⟨g, hg⟩ := hu
  rw [Lb_eq hz hg]
  obtain ⟨h1, h2, h3, h4⟩ := hz
  refine ⟨fun h => h1 ?_, ?_, ?_, ?_⟩
  · calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [h2]; group
  · rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, mul_smul, mul_smul, ← hg, inv_smul_smul,
      MulAction.mem_stabilizer_iff.1 h3]
  · intro h hh
    have hmem : g⁻¹ * h * g ∈ MulAction.stabilizer G α := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hg,
        MulAction.mem_stabilizer_iff.1 hh, ← hg, inv_smul_smul]
    have hc := h4 _ hmem
    calc h * (g * z * g⁻¹) = g * (g⁻¹ * h * g * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * h * g)) * g⁻¹ := by rw [hc]
      _ = g * z * g⁻¹ * h := by group

theorem Lb_mul_self {z : G} {α u : V} (hz : z ∈ Cinv G α) (hu : ∃ g : G, g • α = u) :
    Lb z α u * Lb z α u = 1 := (Lb_cinv hz hu).2.1

theorem Lb_ne_one {z : G} {α u : V} (hz : z ∈ Cinv G α) (hu : ∃ g : G, g • α = u) :
    Lb z α u ≠ 1 := (Lb_cinv hz hu).1

theorem Lb_mem_nbrStab (F : FanTree Γ G) {z : G} {α o u : V} (hz : z ∈ Cinv G α)
    (hb : z ∈ ballStab Γ G 2 α) (h1 : Γ.Adj α o) (h2 : Γ.Adj o u) :
    Lb z α u ∈ nbrStab Γ G o := by
  obtain ⟨g, hg⟩ := exists_conj_of_adj F h1 h2
  rw [Lb_eq hz hg]
  refine mem_nbrStab.2 fun w hw => ?_
  have e1 : Γ.Adj α (g⁻¹ • o) := by
    have := (F.adj_smul g⁻¹ u o).2 h2.symm
    rwa [← hg, inv_smul_smul] at this
  have e2 : Γ.Adj (g⁻¹ • o) (g⁻¹ • w) := (F.adj_smul g⁻¹ o w).2 hw
  have hd : Γ.dist α (g⁻¹ • w) ≤ 2 :=
    (SimpleGraph.dist_le (SimpleGraph.Walk.cons e1 (SimpleGraph.Walk.cons e2
      SimpleGraph.Walk.nil))).trans (by simp)
  have := mem_ballStab.1 hb _ hd
  simp only [mul_smul, this, smul_inv_smul]

theorem Lb_commute (F : FanTree Γ G) {z : G} {α o u u' : V} (hz : z ∈ Cinv G α)
    (hb : z ∈ ballStab Γ G 2 α) (h1 : Γ.Adj α o) (h2 : Γ.Adj o u) (h3 : Γ.Adj o u') :
    Lb z α u * Lb z α u' = Lb z α u' * Lb z α u := by
  have hK := Lb_mem_nbrStab F hz hb h1 h2
  have hst : Lb z α u ∈ MulAction.stabilizer G u' :=
    MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 hK u' h3)
  exact (Lb_cinv hz (exists_conj_of_adj F h1 h3)).2.2.2 _ hst

end P514

end CFSG.Quasithin.Fan86
