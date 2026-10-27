module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86LocalChar
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4Cfg

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem exists_edge_char_of_valence (F : FanTree Γ G) {v a : V} {p : ℕ} (hp : valence Γ v = p)
    (hva : Γ.Adj v a) :
    ∃ φ : ↥(MulAction.stabilizer G v ⊓ MulAction.stabilizer G a) →* (ZMod p)ˣ,
      ∀ e : ↥(MulAction.stabilizer G v ⊓ MulAction.stabilizer G a),
        (e : G) ∈ nbrStab Γ G v ↔ φ e = 1 := by
  subst hp
  obtain ⟨φ, h, -⟩ := F.exists_edge_char hva
  exact ⟨φ, h⟩

theorem units_zmod_five_eq_neg_one (x : (ZMod 5)ˣ) (h : x * x = 1) (h1 : x ≠ 1) : x = -1 := by
  revert x
  decide

theorem edge_char_eq_neg_one {v a : V}
    {φ : ↥(MulAction.stabilizer G v ⊓ MulAction.stabilizer G a) →* (ZMod 5)ˣ}
    (hφ : ∀ e : ↥(MulAction.stabilizer G v ⊓ MulAction.stabilizer G a),
      (e : G) ∈ nbrStab Γ G v ↔ φ e = 1)
    {e : ↥(MulAction.stabilizer G v ⊓ MulAction.stabilizer G a)}
    (h2 : (e : G) * e ∈ nbrStab Γ G v) (h1 : (e : G) ∉ nbrStab Γ G v) : φ e = -1 := by
  refine units_zmod_five_eq_neg_one _ ?_ (fun h => h1 ((hφ e).2 h))
  rw [← map_mul]
  exact (hφ (e * e)).1 h2

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L)

@[expose] def alphaV (i : Fin 3) : V := S.D.bv S.xβ i 1

@[expose] def xiV (i : Fin 3) : V := S.D.bv S.xβ i 2

@[expose] def muV (i : Fin 3) : V := S.D.bv S.xβ i 3

theorem alphaV_eq (i : Fin 3) : S.alphaV i = (S.xβ ^ (i : ℕ))⁻¹ • S.α := by
  simp [alphaV, D10Set.bv, S.D.start 0]

theorem xiV_eq (i : Fin 3) : S.xiV i = (S.xβ ^ (i : ℕ))⁻¹ • S.D.beta 0 := by
  simp [xiV, D10Set.bv, D10Set.beta]

theorem muV_eq (i : Fin 3) : S.muV i = (S.xβ ^ (i : ℕ))⁻¹ • S.D.alpha 0 := by
  simp [muV, D10Set.bv, D10Set.alpha]

theorem xβ_pow_inv_smul_beta (n : ℕ) : (S.xβ ^ n)⁻¹ • S.beta = S.beta := by
  rw [inv_smul_eq_iff]
  exact (MulAction.mem_stabilizer_iff.1
    (pow_mem (MulAction.mem_stabilizer_iff.2 S.xβ_smul_beta) n)).symm

theorem alphaV_zero : S.alphaV 0 = S.α := by simp [alphaV_eq]

theorem alphaV_one : S.alphaV 1 = S.xβ⁻¹ • S.α := by simp [alphaV_eq]

theorem alphaV_two : S.alphaV 2 = S.D.alpha 2 := by
  rw [alphaV_eq]
  exact S.collar_one

theorem adj_beta_alphaV (F : FanTree Γ G) (i : Fin 3) : Γ.Adj S.beta (S.alphaV i) := by
  have h := (F.adj_smul (S.xβ ^ (i : ℕ))⁻¹ S.beta S.α).2 (S.D.adj_start_beta 2).symm
  rwa [S.xβ_pow_inv_smul_beta, ← S.alphaV_eq] at h

theorem adj_alphaV_xiV (F : FanTree Γ G) (i : Fin 3) : Γ.Adj (S.alphaV i) (S.xiV i) := by
  have h := (F.adj_smul (S.xβ ^ (i : ℕ))⁻¹ S.α (S.D.beta 0)).2 (S.D.adj_start_beta 0)
  rwa [← S.alphaV_eq, ← S.xiV_eq] at h

theorem adj_xiV_muV (F : FanTree Γ G) (i : Fin 3) : Γ.Adj (S.xiV i) (S.muV i) := by
  have h := (F.adj_smul (S.xβ ^ (i : ℕ))⁻¹ (S.D.beta 0) (S.D.alpha 0)).2 (S.D.adj_beta_alpha 0)
  rwa [← S.xiV_eq, ← S.muV_eq] at h

theorem valence_alphaV (F : FanTree Γ G) (i : Fin 3) : valence Γ (S.alphaV i) = 5 := by
  rw [alphaV_eq, valence_smul F]
  exact S.D.val

theorem valence_xiV (F : FanTree Γ G) (i : Fin 3) : valence Γ (S.xiV i) = 3 := by
  rw [xiV_eq, valence_smul F]
  exact S.D.valence_beta F 0

theorem valence_muV (F : FanTree Γ G) (i : Fin 3) : valence Γ (S.muV i) = 5 := by
  rw [muV_eq, valence_smul F]
  exact S.D.valence_alpha F 0

theorem mem_neighborSet_beta_iff (F : FanTree Γ G) {w : V} :
    Γ.Adj S.beta w ↔ ∃ i : Fin 3, S.alphaV i = w := by
  have h := S.neighborSet_beta F
  have hw : Γ.Adj S.beta w ↔ w ∈ ({S.α, S.xβ⁻¹ • S.α, S.D.alpha 2} : Set V) := by
    rw [← h]
    rfl
  rw [hw]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, S.alphaV_zero⟩
    · exact ⟨1, S.alphaV_one⟩
    · exact ⟨2, S.alphaV_two⟩
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl S.alphaV_zero
    · exact Or.inr (Or.inl S.alphaV_one)
    · exact Or.inr (Or.inr S.alphaV_two)

theorem alphaV_injective : Function.Injective S.alphaV := by
  have h01 : S.alphaV 0 ≠ S.alphaV 1 := by
    rw [alphaV_zero, alphaV_one]
    exact fun e => S.alpha_ne_xβ_inv e.symm
  have h02 : S.alphaV 0 ≠ S.alphaV 2 := by
    rw [alphaV_zero, alphaV_two]
    exact fun e => S.D.alpha_ne_start 2 e.symm
  have h12 : S.alphaV 1 ≠ S.alphaV 2 := by
    rw [alphaV_one, alphaV_two]
    exact S.xβ_inv_alpha_ne_alpha2
  intro i j h
  fin_cases i <;> fin_cases j <;>
    first
    | rfl
    | exact absurd h h01
    | exact absurd h h01.symm
    | exact absurd h h02
    | exact absurd h h02.symm
    | exact absurd h h12
    | exact absurd h h12.symm

theorem dist_smul_beta (F : FanTree Γ G) (n : ℕ) (v : V) :
    Γ.dist S.beta ((S.xβ ^ n)⁻¹ • v) = Γ.dist S.beta v := by
  have := dist_smul F (S.xβ ^ n)⁻¹ S.beta v
  rwa [S.xβ_pow_inv_smul_beta] at this

theorem dist_beta_alphaV (F : FanTree Γ G) (i : Fin 3) : Γ.dist S.beta (S.alphaV i) = 1 :=
  dist_eq_one_iff_adj.2 (S.adj_beta_alphaV F i)

theorem dist_beta_xiV (F : FanTree Γ G) (h : Fan71c F L) (i : Fin 3) :
    Γ.dist S.beta (S.xiV i) = 2 := by
  rw [xiV_eq, S.dist_smul_beta F]
  exact S.D.dist_vert_ne F h (i := 2) (j := 0) (by decide) (m := 1) (m' := 1) (by norm_num)
    (by norm_num)

theorem dist_beta_muV (F : FanTree Γ G) (h : Fan71c F L) (i : Fin 3) :
    Γ.dist S.beta (S.muV i) = 3 := by
  rw [muV_eq, S.dist_smul_beta F]
  exact S.D.dist_vert_ne F h (i := 2) (j := 0) (by decide) (m := 1) (m' := 2) (by norm_num)
    (by norm_num)

theorem dist_alphaV_muV (F : FanTree Γ G) (i : Fin 3) :
    Γ.dist (S.alphaV i) (S.muV i) = 2 := by
  rw [alphaV_eq, muV_eq, dist_smul F]
  exact S.D.dist_start_alpha F 0

theorem dist_muV_alphaV_ne (F : FanTree Γ G) (h : Fan71c F L) {i j : Fin 3} (hij : j ≠ i) :
    Γ.dist (S.muV j) (S.alphaV i) = 4 := by
  have h1 : Γ.dist (S.muV j) (S.alphaV j) + 1 = Γ.dist (S.muV j) S.beta := by
    rw [SimpleGraph.dist_comm, S.dist_alphaV_muV F, SimpleGraph.dist_comm, S.dist_beta_muV F h]
  have := IsTree.dist_succ_of_ne F.isTree (S.adj_beta_alphaV F j) (S.adj_beta_alphaV F i)
    (fun e => hij (S.alphaV_injective e)) h1
  rw [this, SimpleGraph.dist_comm, S.dist_beta_muV F h]

theorem dist_muV_xiV_ne (F : FanTree Γ G) (h : Fan71c F L) {i j : Fin 3} (hij : j ≠ i) :
    Γ.dist (S.muV j) (S.xiV i) = 5 := by
  have h1 : Γ.dist (S.muV j) S.beta + 1 = Γ.dist (S.muV j) (S.alphaV i) := by
    rw [S.dist_muV_alphaV_ne F h hij, SimpleGraph.dist_comm, S.dist_beta_muV F h]
  have hne : S.beta ≠ S.xiV i := fun e => by
    have := S.dist_beta_xiV F h i
    rw [← e, SimpleGraph.dist_self] at this
    omega
  have := IsTree.dist_succ_of_ne F.isTree (S.adj_beta_alphaV F i).symm
    (S.adj_alphaV_xiV F i) hne h1
  rw [this, S.dist_muV_alphaV_ne F h hij]

theorem exists_arm_char (F : FanTree Γ G) (i : Fin 3) :
    ∃ φ : ↥(MulAction.stabilizer G (S.alphaV i) ⊓ MulAction.stabilizer G S.beta) →* (ZMod 5)ˣ,
      ∀ e : ↥(MulAction.stabilizer G (S.alphaV i) ⊓ MulAction.stabilizer G S.beta),
        (e : G) ∈ nbrStab Γ G (S.alphaV i) ↔ φ e = 1 :=
  exists_edge_char_of_valence F (S.valence_alphaV F i) (S.adj_beta_alphaV F i).symm

theorem exists_xi_char (F : FanTree Γ G) (i : Fin 3) :
    ∃ φ : ↥(MulAction.stabilizer G (S.xiV i) ⊓ MulAction.stabilizer G (S.alphaV i)) →*
        (ZMod 3)ˣ,
      ∀ e : ↥(MulAction.stabilizer G (S.xiV i) ⊓ MulAction.stabilizer G (S.alphaV i)),
        (e : G) ∈ nbrStab Γ G (S.xiV i) ↔ φ e = 1 :=
  exists_edge_char_of_valence F (S.valence_xiV F i) (S.adj_alphaV_xiV F i).symm

theorem mem_ballStab_two_beta_iff (F : FanTree Γ G) {g : G} :
    g ∈ ballStab Γ G 2 S.beta ↔ ∀ i : Fin 3, g ∈ nbrStab Γ G (S.alphaV i) := by
  constructor
  · intro hg i
    refine mem_nbrStab.2 fun w hw => mem_ballStab.1 hg w ?_
    calc Γ.dist S.beta w ≤ Γ.dist S.beta (S.alphaV i) + Γ.dist (S.alphaV i) w :=
          F.isTree.connected.dist_triangle
      _ ≤ 1 + 1 := by
          rw [S.dist_beta_alphaV F, dist_eq_one_iff_adj.2 hw]
      _ = 2 := rfl
  · intro hg
    refine mem_ballStab.2 fun w hw => ?_
    have hb : g • S.beta = S.beta := mem_nbrStab.1 (hg 0) S.beta (S.adj_beta_alphaV F 0).symm
    have hd : Γ.dist S.beta w = 0 ∨ Γ.dist S.beta w = 1 ∨ Γ.dist S.beta w = 2 := by omega
    rcases hd with hd | hd | hd
    · have : S.beta = w := by
        by_contra hne
        exact absurd hd (F.isTree.connected.pos_dist_of_ne hne).ne'
      rw [← this]
      exact hb
    · obtain ⟨i, rfl⟩ := (S.mem_neighborSet_beta_iff F).1 (dist_eq_one_iff_adj.1 hd)
      exact MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer _ (hg i))
    · obtain ⟨u, hu, hu1⟩ := IsTree.exists_adj_dist_succ F.isTree (u := S.beta) (v := w) (n := 1)
        hd
      obtain ⟨i, rfl⟩ := (S.mem_neighborSet_beta_iff F).1 (dist_eq_one_iff_adj.1 hu1)
      exact mem_nbrStab.1 (hg i) w hu

end Sec9Cfg

end CFSG.Quasithin.Fan86
