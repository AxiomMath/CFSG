module

public import CFSG.Quasithin.H13.AS91Sec5CountA
public import CFSG.Quasithin.H13.AS91Sec5PlaneCount

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94
open scoped Pointwise

theorem ncard_doubleCount_le {α β : Type*} [Finite α] [Finite β] (r : α → β → Prop) (P : α → Prop)
    (Q : β → Prop) {m n : ℕ} (hP : ∀ a, P a → {b | Q b ∧ r a b}.ncard = m)
    (hQ : ∀ b, Q b → {a | P a ∧ r a b}.ncard ≤ n) :
    {a | P a}.ncard * m ≤ {b | Q b}.ncard * n := by
  classical
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  have h1 : ∀ a ∈ Finset.univ.filter P,
      m ≤ ((Finset.univ.filter Q).bipartiteAbove r a).card := fun a ha => by
    rw [← hP a (Finset.mem_filter.1 ha).2, ← Set.ncard_coe_finset]
    refine le_of_eq (congrArg Set.ncard ?_)
    ext b
    simp [Finset.bipartiteAbove]
  have h2 : ∀ b ∈ Finset.univ.filter Q,
      ((Finset.univ.filter P).bipartiteBelow r b).card ≤ n := fun b hb => by
    refine le_trans (le_of_eq ?_) (hQ b (Finset.mem_filter.1 hb).2)
    rw [← Set.ncard_coe_finset]
    congr 1
    ext a
    simp [Finset.bipartiteBelow]
  have key := Finset.card_mul_le_card_mul r h1 h2
  have hPc : {a | P a}.ncard = (Finset.univ.filter P).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext a
    simp
  have hQc : {b | Q b}.ncard = (Finset.univ.filter Q).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext b
    simp
  rw [hPc, hQc]
  exact key

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

@[expose] def Pcl (i : Fin 5) : Set (G ⧸ c.G2) :=
  {n | n ∈ c.deltaAt i c.x0 c.l0 ∧ c.LnP n c.pi0}

@[expose] def Lam (w : G ⧸ c.G1) : Set (G ⧸ c.G1) :=
  {b | c.OnP b c.pi0 ∧ c.Delta.Adj c.x0 b ∧ c.Delta.Adj w b}

@[expose] def FarNb (w : G ⧸ c.G1) : Set (G ⧸ c.G1) :=
  {v | v ∈ c.farP ∧ c.Delta.Adj w v}

@[expose] def Ucl (y : G ⧸ c.G1) (i : Fin 5) : Set (G ⧸ c.G1) :=
  {b | ∃ m ∈ c.Pcl i, b ∈ c.Aset y m}

theorem smul_mem_Lam {g : G} (hg : g ∈ c.G1 ⊓ c.G3) {w b : G ⧸ c.G1} :
    g • b ∈ c.Lam (g • w) ↔ b ∈ c.Lam w := by
  have hx : g • c.x0 = c.x0 := c.smul_x0_of_mem hg.1
  have hp : g • c.pi0 = c.pi0 := c.G3_smul_pi0 hg.2
  have h1 : c.OnP (g • b) c.pi0 ↔ c.OnP b c.pi0 := by
    have := c.onP_smul_iff g (a := b) (σ := c.pi0)
    rwa [hp] at this
  have h2 : c.Delta.Adj c.x0 (g • b) ↔ c.Delta.Adj c.x0 b := by
    have := c.adj_smul_iff g (a := c.x0) (b := b)
    rwa [hx] at this
  have h3 : c.Delta.Adj (g • w) (g • b) ↔ c.Delta.Adj w b := c.adj_smul_iff g
  simp only [Lam, Set.mem_setOf_eq, h1, h2, h3]

theorem ncard_Lam_smul {g : G} (hg : g ∈ c.G1 ⊓ c.G3) (w : G ⧸ c.G1) :
    (c.Lam (g • w)).ncard = (c.Lam w).ncard := by
  have hset : c.Lam (g • w) = (g • ·) '' c.Lam w := by
    ext b
    constructor
    · intro hb
      refine ⟨g⁻¹ • b, ?_, smul_inv_smul g b⟩
      rw [← c.smul_mem_Lam hg, smul_inv_smul]
      exact hb
    · rintro ⟨b', hb', rfl⟩
      exact (c.smul_mem_Lam hg).2 hb'
  rw [hset, Set.ncard_image_of_injective _ (MulAction.injective g)]

theorem ncard_biUnion_Aset (hLU : Stmt5_LineU) (hJ : HypJ4 G z) (y : G ⧸ c.G1)
    {P : Set (G ⧸ c.G2)} (hP : ∀ m ∈ P, c.OnL c.x0 m) {a : ℕ}
    (hA : ∀ m ∈ P, (c.Aset y m).ncard = a) :
    {b | ∃ m ∈ P, b ∈ c.Aset y m}.ncard = P.ncard * a := by
  have h := ncard_doubleCount (fun (m : G ⧸ c.G2) (b : G ⧸ c.G1) => c.OnL b m) (fun m => m ∈ P)
    (fun b => ∃ m ∈ P, b ∈ c.Aset y m) (m := a) (n := 1) ?_ ?_
  · rw [Set.setOf_mem_eq, mul_one] at h
    exact h.symm
  · intro m hm
    have hset : {b | (∃ m' ∈ P, b ∈ c.Aset y m') ∧ c.OnL b m} = c.Aset y m := by
      ext b
      constructor
      · rintro ⟨⟨m', hm', hb⟩, hbm⟩
        have e := c.eq_of_onL hLU hJ (Ne.symm hb.2.1) (hP m' hm') hb.1 (hP m hm) hbm
        rw [← e]
        exact hb
      · intro hb
        exact ⟨⟨m, hm, hb⟩, hb.1⟩
    rw [hset]
    exact hA m hm
  · rintro b ⟨m₀, hm₀, hb⟩
    have hset : {m | m ∈ P ∧ c.OnL b m} = {m₀} := by
      ext m
      constructor
      · rintro ⟨hm, hbm⟩
        exact c.eq_of_onL hLU hJ (Ne.symm hb.2.1) (hP m hm) hbm (hP m₀ hm₀) hb.1
      · rintro rfl
        exact ⟨hm₀, hb.1⟩
    rw [hset]
    exact Set.ncard_singleton m₀

theorem ncard_Aset_l0 {y : G ⧸ c.G1} (hy : y ∈ c.ptsL) (hyx : y ≠ c.x0) :
    (c.Aset y c.l0).ncard = 3 := by
  have hl0 : c.OnL c.x0 c.l0 := cInc_mk c.G1 c.G2 1
  have hset : c.Aset y c.l0 = {a | c.OnL a c.l0} \ {c.x0, y} := by
    ext a
    simp only [mem_Aset, Set.mem_diff, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or]
    constructor
    · rintro ⟨ha, hax, hya⟩
      exact ⟨ha, hax, fun h => hya.ne h.symm⟩
    · rintro ⟨ha, hax, hay⟩
      exact ⟨ha, hax, c.adj_of_onL (Ne.symm hay) hy ha⟩
  have hsub : ({c.x0, y} : Set (G ⧸ c.G1)) ⊆ {a | c.OnL a c.l0} := by
    intro a ha
    rcases ha with rfl | rfl
    · exact hl0
    · exact hy
  rw [hset, Set.ncard_diff hsub, Set.ncard_pair (Ne.symm hyx), c.ncard_onL c.l0]

end Loc49

namespace ResM24

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z} (ρ : ResM24 c)

include ρ in
theorem Lam_eq (hG2 : Stmt5_Gamma2) (hJ : HypJ4 G z) (y : G ⧸ c.G1) :
    c.Lam y = c.Ucl y 0 ∪ c.Ucl y 1 ∪ c.Ucl y 2 := by
  have hl0 : c.OnL c.x0 c.l0 := cInc_mk c.G1 c.G2 1
  have hl0P : c.LnP c.l0 c.pi0 := cInc_mk c.G2 c.G3 1
  ext b
  constructor
  · rintro ⟨hbP, hxb, hyb⟩
    obtain ⟨hne, m, hxm, hbm⟩ := id hxb
    have hmP : c.LnP m c.pi0 := c.lnP_of_adj hG2 hJ c.x0_mem_ptsP hbP hxb hxm hbm
    have hba : b ∈ c.Aset y m := ⟨hbm, Ne.symm hne, hyb⟩
    by_cases hml : m = c.l0
    · subst hml
      exact Or.inl (Or.inl ⟨c.l0, ⟨(ρ.mem_deltaAt_zero_iff hl0 hl0).2 rfl, hmP⟩, hba⟩)
    · rcases ρ.mem_deltaAt_one_or_two hl0 hxm hl0P hmP hml with h1 | h2
      · exact Or.inl (Or.inr ⟨m, ⟨h1, hmP⟩, hba⟩)
      · exact Or.inr ⟨m, ⟨h2, hmP⟩, hba⟩
  · rintro ((⟨m, ⟨hmδ, hmP⟩, hba⟩ | ⟨m, ⟨hmδ, hmP⟩, hba⟩) | ⟨m, ⟨hmδ, hmP⟩, hba⟩) <;>
    exact ⟨c.inc_pt_plane hba.1 hmP,
      c.adj_of_onL (Ne.symm hba.2.1) (c.onL_of_mem_deltaAt hmδ) hba.1, hba.2.2⟩

include ρ in
theorem disjoint_Ucl (hLU : Stmt5_LineU) (hJ : HypJ4 G z) (y : G ⧸ c.G1) {i j : Fin 5}
    (hij : i ≠ j) : Disjoint (c.Ucl y i) (c.Ucl y j) := by
  rw [Set.disjoint_left]
  rintro b ⟨m, ⟨hmi, -⟩, hbm⟩ ⟨m', ⟨hmj, -⟩, hbm'⟩
  have hxm := c.onL_of_mem_deltaAt hmi
  have hxm' := c.onL_of_mem_deltaAt hmj
  have e := c.eq_of_onL hLU hJ (Ne.symm hbm.2.1) hxm hbm.1 hxm' hbm'.1
  subst e
  obtain ⟨k, -, hk⟩ := ρ.deltaAt_existsUnique (cInc_mk c.G1 c.G2 1) hxm
  exact hij ((hk i hmi).trans (hk j hmj).symm)

include ρ in
theorem ncard_Lam (hLU : Stmt5_LineU) (hG2 : Stmt5_Gamma2) (hJ : HypJ4 G z) {y : G ⧸ c.G1}
    (hy : y ∈ c.ptsL) (hyx : y ≠ c.x0) {a₁ a₂ : ℕ}
    (h1 : ∀ k ∈ c.Pcl 1, (c.Aset y k).ncard = a₁) (h2 : ∀ k ∈ c.Pcl 2, (c.Aset y k).ncard = a₂) :
    (c.Lam y).ncard = 3 + 6 * a₁ + 8 * a₂ := by
  have hl0 : c.OnL c.x0 c.l0 := cInc_mk c.G1 c.G2 1
  have hl0P : c.LnP c.l0 c.pi0 := cInc_mk c.G2 c.G3 1
  have hP0 : c.Pcl 0 = {c.l0} := by
    ext n
    constructor
    · rintro ⟨hn, -⟩
      exact (ρ.mem_deltaAt_zero_iff hl0 (c.onL_of_mem_deltaAt hn)).1 hn
    · rintro rfl
      exact ⟨(ρ.mem_deltaAt_zero_iff hl0 hl0).2 rfl, hl0P⟩
  have hU0 : (c.Ucl y 0).ncard = 3 := by
    have h := c.ncard_biUnion_Aset hLU hJ y (P := c.Pcl 0) (a := 3)
      (fun m hm => c.onL_of_mem_deltaAt hm.1) (fun m hm => by
        rw [hP0] at hm
        rw [Set.mem_singleton_iff.1 hm]
        exact c.ncard_Aset_l0 hy hyx)
    have h1 : (c.Pcl 0).ncard = 1 := by rw [hP0]; exact Set.ncard_singleton _
    rw [h1, one_mul] at h
    exact h
  have hU1 : (c.Ucl y 1).ncard = 6 * a₁ := by
    have h := c.ncard_biUnion_Aset hLU hJ y (P := c.Pcl 1) (a := a₁)
      (fun m hm => c.onL_of_mem_deltaAt hm.1) h1
    have h6 : (c.Pcl 1).ncard = 6 := ρ.ncard_deltaAt_one_lnP hl0 hl0P
    rw [h6] at h
    exact h
  have hU2 : (c.Ucl y 2).ncard = 8 * a₂ := by
    have h := c.ncard_biUnion_Aset hLU hJ y (P := c.Pcl 2) (a := a₂)
      (fun m hm => c.onL_of_mem_deltaAt hm.1) h2
    have h8 : (c.Pcl 2).ncard = 8 := ρ.ncard_deltaAt_two_lnP hl0 hl0P
    rw [h8] at h
    exact h
  have d01 := ρ.disjoint_Ucl hLU hJ y (i := 0) (j := 1) (by decide)
  have d02 := ρ.disjoint_Ucl hLU hJ y (i := 0) (j := 2) (by decide)
  have d12 := ρ.disjoint_Ucl hLU hJ y (i := 1) (j := 2) (by decide)
  rw [ρ.Lam_eq hG2 hJ y, Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨d02, d12⟩),
    Set.ncard_union_eq d01, hU0, hU1, hU2]

include ρ in
theorem ncard_Lam_add_FarNb (hLU : Stmt5_LineU) (hG2 : Stmt5_Gamma2) (hJ : HypJ4 G z)
    {w : G ⧸ c.G1} (hw : w ∈ c.nbrP) : (c.Lam w).ncard + (c.FarNb w).ncard + 1 = 60 := by
  have h60 := ρ.ncard_adj_onP hLU hG2 hJ (a := w) (σ := c.pi0) hw.1
  have hx0 : c.x0 ∉ c.Lam w ∪ c.FarNb w := by
    rintro (h | h)
    · exact h.2.1.ne rfl
    · exact h.1.2.1 rfl
  have hdisj : Disjoint (c.Lam w) (c.FarNb w) := by
    rw [Set.disjoint_left]
    rintro u ⟨-, hxu, -⟩ ⟨⟨-, -, hnxu⟩, -⟩
    exact hnxu hxu
  have hset : {b | c.OnP b c.pi0 ∧ c.Delta.Adj w b} = insert c.x0 (c.Lam w ∪ c.FarNb w) := by
    ext u
    constructor
    · rintro ⟨hu, hwu⟩
      by_cases hux : u = c.x0
      · exact Or.inl hux
      · by_cases hxu : c.Delta.Adj c.x0 u
        · exact Or.inr (Or.inl ⟨hu, hxu, hwu⟩)
        · exact Or.inr (Or.inr ⟨⟨hu, hux, hxu⟩, hwu⟩)
    · rintro (rfl | ⟨hu, -, hwu⟩ | ⟨⟨hu, -, -⟩, hwu⟩)
      · exact ⟨c.x0_mem_ptsP, hw.2.symm⟩
      · exact ⟨hu, hwu⟩
      · exact ⟨hu, hwu⟩
  rw [hset, Set.ncard_insert_of_notMem hx0, Set.ncard_union_eq hdisj] at h60
  omega

include ρ in
theorem Lam_bounds (hLU : Stmt5_LineU) (hG2 : Stmt5_Gamma2) (hJ : HypJ4 G z) {y : G ⧸ c.G1}
    (hy : y ∈ c.nbrP) (hlam : ∀ w ∈ c.nbrP, (c.Lam w).ncard = (c.Lam y).ncard) :
    43 ≤ (c.Lam y).ncard ∧ (c.Lam y).ncard ≤ 58 := by
  have hfar : ∀ w ∈ c.nbrP, (c.FarNb w).ncard = 59 - (c.Lam y).ncard := by
    intro w hw
    have h := ρ.ncard_Lam_add_FarNb hLU hG2 hJ hw
    rw [hlam w hw] at h
    omega
  have hle59 : (c.Lam y).ncard ≤ 59 := by
    have := ρ.ncard_Lam_add_FarNb hLU hG2 hJ hy
    omega
  have h60 : c.nbrP.ncard = 60 := ρ.ncard_adj_onP hLU hG2 hJ c.x0_mem_ptsP
  have h16 : c.farP.ncard = 16 := ρ.ncard_far_onP hLU hG2 hJ c.x0_mem_ptsP
  have hge : 43 ≤ (c.Lam y).ncard := by
    have h := ncard_doubleCount_le (fun (w v : G ⧸ c.G1) => c.Delta.Adj w v)
      (fun w => w ∈ c.nbrP) (fun v => v ∈ c.farP) (m := 59 - (c.Lam y).ncard) (n := 60)
      (fun w hw => hfar w hw) (fun v hv => ?_)
    · rw [Set.setOf_mem_eq, Set.setOf_mem_eq, h60, h16] at h
      omega
    · have hsub : {w | w ∈ c.nbrP ∧ c.Delta.Adj w v} ⊆ {u | c.OnP u c.pi0 ∧ c.Delta.Adj v u} :=
        fun w hw => ⟨hw.1.1, hw.2.symm⟩
      exact (Set.ncard_le_ncard hsub).trans (ρ.ncard_adj_onP hLU hG2 hJ hv.1).le
  refine ⟨hge, ?_⟩
  by_contra hcon
  have h59 : (c.Lam y).ncard = 59 := by omega
  have hempty : ∀ w ∈ c.nbrP, ∀ v ∈ c.farP, ¬ c.Delta.Adj w v := by
    intro w hw v hv hwv
    have h0 : (c.FarNb w).ncard = 0 := by rw [hfar w hw, h59]
    have hfin : c.FarNb w = ∅ := (Set.ncard_eq_zero (Set.toFinite _)).1 h0
    have hv' : v ∈ c.FarNb w := ⟨hv, hwv⟩
    rw [hfin] at hv'
    exact hv'
  obtain ⟨v, hv⟩ : c.farP.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  have hsub : {u | c.OnP u c.pi0 ∧ c.Delta.Adj v u} ⊆ c.farP \ {v} := by
    rintro u ⟨hu, hvu⟩
    refine ⟨⟨hu, ?_, ?_⟩, hvu.ne.symm⟩
    · rintro rfl
      exact hv.2.2 hvu.symm
    · intro hxu
      exact hempty u ⟨hu, hxu⟩ v hv hvu.symm
  have h1 := Set.ncard_le_ncard hsub
  rw [ρ.ncard_adj_onP hLU hG2 hJ hv.1, Set.ncard_diff_singleton_of_mem hv, h16] at h1
  omega

include ρ in
theorem ncard_Aset_values (hK : c.KerFacts) (hLU : Stmt5_LineU) (hG2 : Stmt5_Gamma2)
    (hJ : HypJ4 G z) {y : G ⧸ c.G1} (hy : y ∈ c.ptsL) (hyx : y ≠ c.x0) :
    (∀ k ∈ c.delta 1, (c.Aset y k).ncard = 2) ∧ (∀ k ∈ c.delta 2, (c.Aset y k).ncard = 4) := by
  have hl0 : c.OnL c.x0 c.l0 := cInc_mk c.G1 c.G2 1
  have hl0P : c.LnP c.l0 c.pi0 := cInc_mk c.G2 c.G3 1
  obtain ⟨k₁, hk₁⟩ : (c.Pcl 1).Nonempty := Set.nonempty_of_ncard_ne_zero (by
    have h6 : (c.Pcl 1).ncard = 6 := ρ.ncard_deltaAt_one_lnP hl0 hl0P
    omega)
  obtain ⟨k₂, hk₂⟩ : (c.Pcl 2).Nonempty := Set.nonempty_of_ncard_ne_zero (by
    have h8 : (c.Pcl 2).ncard = 8 := ρ.ncard_deltaAt_two_lnP hl0 hl0P
    omega)
  have hd1 : ∀ k ∈ c.Pcl 1, k ∈ c.delta 1 := fun k hk =>
    (c.mem_delta_iff_mem_deltaAt 1).2 hk.1
  have hd2 : ∀ k ∈ c.Pcl 2, k ∈ c.delta 2 := fun k hk =>
    (c.mem_delta_iff_mem_deltaAt 2).2 hk.1
  have e1 : ∀ k ∈ c.Pcl 1, (c.Aset y k).ncard = (c.Aset y k₁).ncard := fun k hk =>
    ρ.ncard_Aset_delta 1 hy hyx (hd1 k hk) (hd1 k₁ hk₁)
  have e2 : ∀ k ∈ c.Pcl 2, (c.Aset y k).ncard = (c.Aset y k₂).ncard := fun k hk =>
    ρ.ncard_Aset_delta 2 hy hyx (hd2 k hk) (hd2 k₂ hk₂)
  have hyP : y ∈ c.nbrP := ⟨c.inc_pt_plane hy hl0P, c.adj_of_onL (Ne.symm hyx) hl0 hy⟩
  have hlam : ∀ w ∈ c.nbrP, (c.Lam w).ncard = (c.Lam y).ncard := by
    intro w hw
    obtain ⟨g, hg, rfl⟩ := c.nbrP_transitive (hG2 G z hJ c) y hyP w hw
    exact c.ncard_Lam_smul hg y
  have hcount := ρ.ncard_Lam hLU hG2 hJ hy hyx e1 e2
  obtain ⟨hlo, hhi⟩ := ρ.Lam_bounds hLU hG2 hJ hyP hlam
  have ha1 := Loc49.ncard_Aset_delta_one hK hy hk₁.1
  have ha2 := Loc49.ncard_Aset_delta_two hK hy hk₂.1
  have a1 : (c.Aset y k₁).ncard = 2 := by omega
  have a2 : (c.Aset y k₂).ncard = 4 := by omega
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · rw [ρ.ncard_Aset_delta 1 hy hyx hk (hd1 k₁ hk₁)]
    exact a1
  · rw [ρ.ncard_Aset_delta 2 hy hyx hk (hd2 k₂ hk₂)]
    exact a2

end ResM24


theorem stmt5_4_34_of
    (hres : ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
      Nonempty (ResM24 c))
    (hker : ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
      c.KerFacts)
    (hLU : Stmt5_LineU) (hG2 : Stmt5_Gamma2) : Stmt5_4_34 := by
  intro G _ _ z hJ c y hy hyx
  obtain ⟨ρ⟩ := hres G z hJ c
  obtain ⟨h1, h2⟩ := ρ.ncard_Aset_values (hker G z hJ c) hLU hG2 hJ hy hyx
  have hl0 : c.OnL c.x0 c.l0 := cInc_mk c.G1 c.G2 1
  have hyadj : c.Delta.Adj y c.x0 := c.adj_of_onL hyx hy hl0
  refine ⟨fun k hk => ?_, fun k hk a ha => ?_⟩
  · have hkx : c.OnL c.x0 k := hk.1.symm'
    have hset : {a | a ∈ objOf c.G1 c.G2 k ∧ c.Delta.Adj y a} = insert c.x0 (c.Aset y k) := by
      ext a
      constructor
      · rintro ⟨ha, hya⟩
        by_cases hax : a = c.x0
        · exact Or.inl hax
        · exact Or.inr ⟨ha, hax, hya⟩
      · rintro (rfl | ⟨ha, -, hya⟩)
        · exact ⟨hkx, hyadj⟩
        · exact ⟨ha, hya⟩
    rw [hset, Set.ncard_insert_of_notMem (fun h => h.2.1 rfl), h1 k hk]
  · by_cases hax : a = c.x0
    · rw [hax]
      exact hyadj
    · have hkx : c.OnL c.x0 k := hk.1.symm'
      have hsub : c.Aset y k ⊆ {a | c.OnL a k} \ {c.x0} := fun a ha => ⟨ha.1, ha.2.1⟩
      have heq := Set.eq_of_subset_of_ncard_le hsub
        (le_of_eq (by rw [c.ncard_onL_ne hkx, h2 k hk]))
      have hmem : a ∈ c.Aset y k := by
        rw [heq]
        exact ⟨ha, hax⟩
      exact hmem.2.2

end CFSG.Quasithin.H13.AS91
