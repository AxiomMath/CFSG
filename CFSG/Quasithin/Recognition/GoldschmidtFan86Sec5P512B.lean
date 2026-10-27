module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P512A

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P512

theorem ballStab_two_of (F : FanTree Γ G) {v : V} {y : G} (hK : y ∈ nbrStab Γ G v)
    (hN : ∀ ν, Γ.Adj v ν → y ∈ nbrStab Γ G ν) : y ∈ ballStab Γ G 2 v := by
  rw [mem_ballStab]
  intro w hw
  have hcases : Γ.dist v w = 0 ∨ Γ.dist v w = 1 ∨ Γ.dist v w = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · obtain rfl : v = w := F.isTree.connected.dist_eq_zero_iff.1 h0
    exact MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer _ hK)
  · exact mem_nbrStab.1 hK w (dist_eq_one_iff_adj.1 h1)
  · obtain ⟨ν, hν⟩ := P62.exists_br F h2
    exact mem_nbrStab.1 (hN ν hν.1) w hν.2.1

theorem nbrStab_of_ballStab_two {v : V} {y : G} (hb : y ∈ ballStab Γ G 2 v) :
    y ∈ nbrStab Γ G v ∧ ∀ ν, Γ.Adj v ν → y ∈ nbrStab Γ G ν := by
  have h1 : y ∈ nbrStab Γ G v := mem_nbrStab.2 fun w hw =>
    mem_ballStab.1 hb w (by rw [dist_eq_one_iff_adj.2 hw]; omega)
  refine ⟨h1, fun ν hν => mem_nbrStab.2 fun u hu => mem_ballStab.1 hb u ?_⟩
  exact (dist_le (Walk.cons hν (Walk.cons hu Walk.nil))).trans (by simp)

theorem ball2_track (F : FanTree Γ G) (h510 : Fan510 F) (h511 : Fan511 F)
    (h53a : Fan53a F) (h40 : Fan40 F) {T : Track Γ G} (hT : InXi T) {z : G} {a : ℤ}
    (hz : z ∈ T.line.ZZ) (hz1 : z ≠ 1) (hcore : T.line.IsCore z a (a + 2)) :
    z ∈ ballStab Γ G 2 (T.line.vert (a + 1)) := by
  set ℓ := T.line with hℓ
  have hzα : z ∈ Cinv G (ℓ.vert (a + 1)) := fan512cen F h40 T z a hT hz hz1 hcore
  obtain ⟨⟨a', b', tL, tR, hf⟩, -⟩ := coreSat2 h510 h511 h40 hT hz hz1
  have hfix : ℓ.IsCoreFix z a (a + 2) tL tR := ⟨hf.fix, hcore⟩
  have hl1 : 1 ≤ a - tL := (h53a h40 ℓ z a (a + 2) tL tR hz hfix).2.1
  have htR : a + 2 ≤ tR := ((hf.fix (a + 2)).1 (hcore.2.1 (a + 2) (by omega) le_rfl)).2
  have hzm : z • ℓ.vert (a - 1) = ℓ.vert (a - 1) := (hf.fix (a - 1)).2 ⟨by omega, by omega⟩
  have hne : ℓ.vert (a + 1) ≠ ℓ.vert (a - 1) := by
    have := ℓ.nb (a - 1)
    rw [show a - 1 + 2 = a + 1 by ring] at this
    exact this.symm
  have hKa : z ∈ nbrStab Γ G (ℓ.vert a) :=
    F.fix_two_nbrs (ℓ.adj a) (ℓ.adj_pred a) hne (hcore.2.1 (a + 1) (by omega) (by omega)) hzm
  refine ballStab_two_of F (P62.cinv_mem_nbrStab F hzα) fun ν hν => ?_
  obtain ⟨g, hg, hgx⟩ := F.loc_trans _ _ _ (ℓ.adj a).symm hν
  have := F.conj_mem_nbrStab_smul g hKa
  rw [hgx] at this
  have hgz : g * z * g⁻¹ = z := by
    rw [hzα.2.2.2 g hg]
    group
  rwa [hgz] at this

theorem list_prod_mul_self {L : List G} (hc : L.Pairwise Commute) (h2 : ∀ x ∈ L, x * x = 1) :
    L.prod * L.prod = 1 := by
  induction L with
  | nil => simp
  | cons x t ih =>
    have hxt : Commute x t.prod :=
      Commute.list_prod_right t x fun y hy => List.rel_of_pairwise_cons hc hy
    have ht := ih (List.Pairwise.of_cons hc) fun y hy => h2 y (List.mem_cons_of_mem _ hy)
    rw [List.prod_cons]
    calc x * t.prod * (x * t.prod) = x * (t.prod * x) * t.prod := by group
      _ = x * (x * t.prod) * t.prod := by rw [← hxt.eq]
      _ = (x * x) * (t.prod * t.prod) := by group
      _ = 1 := by rw [h2 x List.mem_cons_self, ht, mul_one]

section Prod

variable (F : FanTree Γ G) {α : V} {z : G} (hz : z ∈ Cinv G α)
include F hz

omit hz in
theorem lab_mem_nbrStab_adj (hb : z ∈ ballStab Γ G 2 α) {β u : V} (hβu : Γ.Adj β u) (g : G)
    (hg : g • α = u) : g * z * g⁻¹ ∈ nbrStab Γ G β := by
  have hadj : Γ.Adj (g⁻¹ • β) α := by
    have := (F.adj_smul g⁻¹ β u).2 hβu
    rwa [← hg, inv_smul_smul] at this
  have := F.conj_mem_nbrStab_smul g ((nbrStab_of_ballStab_two hb).2 _ hadj.symm)
  rwa [smul_inv_smul] at this

theorem prod_eq_one (hb : z ∈ ballStab Γ G 2 α)
    (hF1 : ∀ β, ¬ Equiv3 G α β → Cinv G β = ∅) {β : V} (hβ : ¬ Equiv3 G α β) (l : List V)
    (h : V → G) (hl : l.Nodup) (hmem : ∀ u, u ∈ l ↔ Γ.Adj β u)
    (hh : ∀ u, Γ.Adj β u → h u • α = u) :
    (l.map fun u => h u * z * (h u)⁻¹).Pairwise Commute ∧
      (l.map fun u => h u * z * (h u)⁻¹).prod = 1 := by
  set f : V → G := fun u => h u * z * (h u)⁻¹ with hf
  have hfL : ∀ u, Γ.Adj β u → f u = P514.Lb z α u := fun u hu => (P514.Lb_eq hz (hh u hu)).symm
  have hfK : ∀ u, Γ.Adj β u → f u ∈ nbrStab Γ G β := fun u hu =>
    lab_mem_nbrStab_adj F hb hu (h u) (hh u hu)
  have hfC : ∀ u, Γ.Adj β u → f u ∈ Cinv G u := fun u hu => by
    rw [hfL u hu]
    exact P514.Lb_cinv hz ⟨h u, hh u hu⟩
  have hcomm : ∀ u u', Γ.Adj β u → Γ.Adj β u' → Commute (f u) (f u') := by
    intro u u' hu hu'
    have hst : f u ∈ MulAction.stabilizer G u' :=
      MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 (hfK u hu) u' hu')
    exact (hfC u' hu').2.2.2 (f u) hst
  have hpair : (l.map f).Pairwise Commute := by
    rw [List.pairwise_map]
    exact hl.imp_of_mem fun ha hb _ => hcomm _ _ ((hmem _).1 ha) ((hmem _).1 hb)
  refine ⟨hpair, ?_⟩
  by_contra hv1
  have hv2 : (l.map f).prod * (l.map f).prod = 1 := by
    refine list_prod_mul_self hpair fun x hx => ?_
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
    exact (hfC u ((hmem u).1 hu)).2.1
  have hvK : (l.map f).prod ∈ nbrStab Γ G β := by
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
    exact hfK u ((hmem u).1 hu)
  have hvcen : ∀ k ∈ MulAction.stabilizer G β, k * (l.map f).prod = (l.map f).prod * k := by
    intro k hk
    have hkβ : k • β = β := MulAction.mem_stabilizer_iff.1 hk
    have hadj : ∀ u, Γ.Adj β u → Γ.Adj β (k • u) := fun u hu => by
      have := (F.adj_smul k β u).2 hu
      rwa [hkβ] at this
    have hconj : k * (l.map f).prod * k⁻¹ = ((l.map fun u => k • u).map f).prod := by
      have := map_list_prod (MulAut.conj k) (l.map f)
      rw [MulAut.conj_apply] at this
      rw [this, List.map_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hu' := (hmem u).1 hu
      show k * f u * k⁻¹ = f (k • u)
      rw [hfL u hu', hfL _ (hadj u hu'), P514.Lb_conj hz ⟨h u, hh u hu'⟩ k]
    have hperm : (l.map fun u => k • u).Perm l := by
      rw [List.perm_ext_iff_of_nodup (hl.map (MulAction.injective k)) hl]
      intro w
      simp only [List.mem_map]
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact (hmem _).2 (hadj u ((hmem u).1 hu))
      · intro hw
        refine ⟨k⁻¹ • w, (hmem _).2 ?_, smul_inv_smul k w⟩
        have := (F.adj_smul k⁻¹ β w).2 ((hmem w).1 hw)
        rwa [inv_smul_eq_iff.2 hkβ.symm] at this
    have hP := ((hperm.map f).symm).prod_eq' hpair
    rw [hP.symm] at hconj
    exact mul_inv_eq_iff_eq_mul.1 hconj
  exact (Set.eq_empty_iff_forall_notMem.1 (hF1 β hβ)) _ ⟨hv1, hv2, hvK |> F.nbrStab_le_stabilizer β,
    hvcen⟩

end Prod

end P512

theorem fan512b (F : FanTree Γ G) (h510 : Fan510 F) (h511 : Fan511 F) (h53a : Fan53a F) :
    Fan512b F := by
  intro h40 T z a hT hz hz1 hcore
  have hzα := fan512cen F h40 T z a hT hz hz1 hcore
  have hb := P512.ball2_track F h510 h511 h53a h40 hT hz hz1 hcore
  exact ⟨hb, fun β l h hβ hl hmem hh => P512.prod_eq_one F hzα hb
    (fun β' hβ' => fan512a F h510 h511 h40 T z a hT hz hz1 hcore β' hβ') hβ l h hl hmem hh⟩

end CFSG.Quasithin.Fan86
