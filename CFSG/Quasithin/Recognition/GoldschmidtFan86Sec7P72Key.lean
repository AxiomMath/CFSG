module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P72Loc

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

namespace P72

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

structure Arc4 (Γ : SimpleGraph V) (x0 x1 x2 x3 x4 : V) : Prop where
  a01 : Γ.Adj x0 x1
  a12 : Γ.Adj x1 x2
  a23 : Γ.Adj x2 x3
  a34 : Γ.Adj x3 x4
  n02 : x0 ≠ x2
  n13 : x1 ≠ x3
  n24 : x2 ≠ x4

structure Br (Γ : SimpleGraph V) (α ν l : V) : Prop where
  a1 : Γ.Adj α ν
  a2 : Γ.Adj ν l
  ne : l ≠ α

variable {F : FanTree Γ G} {L : ZLab Γ G}

theorem Br.valence (F : FanTree Γ G) {α ν l : V} (b : Br Γ α ν l) (hα : valence Γ α = 5) :
    valence Γ ν = 3 ∧ valence Γ l = 5 :=
  ⟨valence_adj_three F hα b.a1, valence_adj_five F (valence_adj_three F hα b.a1) b.a2⟩

theorem Br.dist_alpha (hT : Γ.IsTree) {α ν l : V} (b : Br Γ α ν l) : Γ.dist l α = 2 := by
  rw [SimpleGraph.dist_comm]
  exact dist_two hT b.a1 b.a2 b.ne

theorem Br.dist_arc (hT : Γ.IsTree) {α ν l x1 x2 x3 x4 : V} (b : Br Γ α ν l)
    (A : Arc4 Γ α x1 x2 x3 x4) (hν : ν ≠ x1) :
    Γ.dist l x1 = 3 ∧ Γ.dist l x2 = 4 ∧ Γ.dist l x3 = 5 := by
  obtain ⟨d3, d4⟩ := dist_branch hT b.a1 b.a2 b.ne A.a01 A.a12 A.n02.symm hν
  have := IsTree.dist_succ_of_ne hT (w := l) A.a12.symm A.a23 A.n13 (by omega)
  exact ⟨d3, d4, by omega⟩

theorem x3_eq (h : Fan71c F L) {α ν₁ ν₂ l₁ l₂ x1 x2 x3 x4 : V} (hα : valence Γ α = 5)
    (b₁ : Br Γ α ν₁ l₁) (b₂ : Br Γ α ν₂ l₂) (A : Arc4 Γ α x1 x2 x3 x4) (h1 : ν₁ ≠ x1)
    (h2 : ν₂ ≠ x1) :
    L.z l₂ • x3 = L.z l₁ • x3 ∧ L.z l₁ • x3 ≠ x3 ∧ Γ.Adj x2 (L.z l₁ • x3) := by
  have hv1 := (b₁.valence F hα).2
  have hv2 := (b₂.valence F hα).2
  obtain ⟨c11, c12, c13⟩ := b₁.dist_arc F.isTree A h1
  obtain ⟨c21, c22, c23⟩ := b₂.dist_arc F.isTree A h2
  have hmem : L.z l₁ * L.z l₂ ∈ nbrStab Γ G x2 :=
    mul_mem_nbrStab h A.a12.symm hv1 hv2 (by omega) (by omega) (by omega) (by omega) A.a23
      (by omega) A.a23 (by omega)
  refine ⟨smul_eq_of_mul_mem (L.z_mul_self hv1) hmem A.a23, z_move h hv1 (by omega), ?_⟩
  have hx2 : L.z l₁ • x2 = x2 := z_fix h hv1 (by omega)
  have := (F.adj_smul (L.z l₁) x2 x3).2 A.a23
  rwa [hx2] at this

theorem mu_facts (h : Fan71c F L) {α ν l x1 x2 x3 x4 x3' : V} (hα : valence Γ α = 5)
    (b : Br Γ α ν l) (A : Arc4 Γ α x1 x2 x3 x4) (hν : ν ≠ x1) (hx3 : L.z l • x3 = x3')
    (hne : x3' ≠ x3) (hadj : Γ.Adj x2 x3') :
    Γ.Adj x3' (L.z l • x4) ∧ L.z l • x4 ≠ x2 ∧ valence Γ (L.z l • x4) = 5 ∧
      Γ.dist x4 (L.z l • x4) = 4 := by
  have hv := (b.valence F hα).2
  obtain ⟨c1, c2, c3⟩ := b.dist_arc F.isTree A hν
  have hx2 : L.z l • x2 = x2 := z_fix h hv (by omega)
  have hadj' : Γ.Adj x3' (L.z l • x4) := by
    have := (F.adj_smul (L.z l) x3 x4).2 A.a34
    rwa [hx3] at this
  have hne2 : L.z l • x4 ≠ x2 := fun hh => A.n24 (by
    have : L.z l • x4 = L.z l • x2 := by rw [hx2]; exact hh
    exact (MulAction.injective (L.z l) this).symm)
  have hv4 := (val_arc4 F A.a01 A.a12 A.a23 A.a34 hα).2.2.2
  obtain ⟨e1, e2, -, -⟩ := dist_arc4 F.isTree A.a01 A.a12 A.a23 A.a34 A.n02 A.n13 A.n24
  have e3 : Γ.dist x4 x3' = 3 := by
    have := IsTree.dist_succ_of_ne F.isTree (w := x4) A.a23 hadj hne.symm (by omega)
    omega
  have e4 : Γ.dist x4 (L.z l • x4) = 4 := by
    have := IsTree.dist_succ_of_ne F.isTree (w := x4) hadj.symm hadj' hne2.symm (by omega)
    omega
  exact ⟨hadj', hne2, by rw [valence_smul F]; exact hv4, e4⟩

end P72

end CFSG.Quasithin.Fan86
