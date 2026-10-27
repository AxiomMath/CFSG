module

public import CFSG.RankThree.GF2n.Tim81.Sec4.NAbGamma
public import CFSG.RankThree.GF2n.Tim81.Sec4.OrthExt

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open CFSG.RankThree.GF2n.Tim81.Sec2
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G}

namespace RootHyp

theorem inf_conj_Pc_le_W0
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN)) :
    Pc M V ⊓ conjSubgroup h₀ (Pc M V) ≤ W₀ := by
  set D : Subgroup G := Pc M V ⊓ conjSubgroup h₀ (Pc M V) with hD
  have hcomm₁ : ⁅D, Pc M V⁆ ≤ V ⊓ W₀ :=
    commutator_inf_conj_Pc_le h hPH hVH hH hnM hK hnab hL hW₀ hN hW₀ne
  have hcomm₂ : ⁅D, conjSubgroup h₀ (Pc M V)⁆ ≤ conjSubgroup h₀ V ⊓ W₀ :=
    commutator_inf_conj_Pc_conj_le h hPH hVH hH hnM hK hnab hL hW₀ hN hW₀ne
  intro d hd
  have hdD : d ∈ D := by simpa [hD] using hd
  have hdC : d ∈ Subgroup.centralizer (kOf V H : Set G) :=
    inf_conj_Pc_le_centralizer_kOf h hPH hH hnM hK hdD
  refine mem_of_isOrthModule_of_forall_commutator_mem h hPH hVH hH hnM ψ hl hW₀ hN horth
    (fun k hk => Subgroup.mem_centralizer_iff.mp hdC k hk) ?_ ?_
  · intro p hp
    have hmem : ⁅p, d⁆ ∈ ⁅Pc M V, D⁆ := Subgroup.commutator_mem_commutator hp hdD
    rw [Subgroup.commutator_comm] at hmem
    exact (inf_le_right : V ⊓ W₀ ≤ W₀) (hcomm₁ hmem)
  · intro p hp
    have hmem : ⁅p, d⁆ ∈ ⁅conjSubgroup h₀ (Pc M V), D⁆ :=
      Subgroup.commutator_mem_commutator hp hdD
    rw [Subgroup.commutator_comm] at hmem
    exact (inf_le_right : conjSubgroup h₀ V ⊓ W₀ ≤ W₀) (hcomm₂ hmem)

private theorem mem_W0_of_mem_inf_xOf_of_commutator_mem_aux
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN))
    (hcomm : ⁅Pc M V ⊓ Tim79a.xOf V H, Pc M V⁆ ≤ V ⊓ W₀)
    {v : G} (hv : v ∈ Pc M V ⊓ Tim79a.xOf V H)
    {y : G} (hy : y ∈ conjSubgroup h₀ (Pc M V)) (hyK : y ∉ kOf V H)
    (hvy : ⁅y, v⁆ ∈ W₀) :
    v ∈ W₀ := by
  refine mem_of_isOrthModule_of_commutator_mem_beta h hPH hVH hH hnM ψ hl hW₀ hN horth
    (fun k hk => (Subgroup.mem_centralizer_iff.mp ((mem_kOf_iff.mp hk).2) v hv.2).symm) ?_
    hy hyK hvy
  intro p hp
  have hmem : ⁅p, v⁆ ∈ ⁅Pc M V, Pc M V ⊓ Tim79a.xOf V H⁆ :=
    Subgroup.commutator_mem_commutator hp hv
  rw [Subgroup.commutator_comm] at hmem
  exact (inf_le_right : V ⊓ W₀ ≤ W₀) (hcomm hmem)

theorem mem_W0_of_mem_inf_xOf_of_commutator_mem
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN))
    {v : G} (hv : v ∈ Pc M V ⊓ Tim79a.xOf V H)
    {y : G} (hy : y ∈ conjSubgroup h₀ (Pc M V)) (hyK : y ∉ kOf V H)
    (hvy : ⁅y, v⁆ ∈ W₀) :
    v ∈ W₀ :=
  mem_W0_of_mem_inf_xOf_of_commutator_mem_aux h hPH hVH hH hnM hW₀ hN ψ hl horth
    (commutator_inf_xOf_le h hPH hVH hH hnM hK hnab hL hW₀ hN hW₀ne) hv hy hyK hvy

theorem mem_W0_of_mem_conj_inf_xOf_of_commutator_mem
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN))
    {v : G} (hv : v ∈ conjSubgroup h₀ (Pc M V) ⊓ Tim79a.xOf V H)
    {x : G} (hx : x ∈ Pc M V) (hxK : x ∉ kOf V H) (hxv : ⁅x, v⁆ ∈ W₀) :
    v ∈ W₀ := by
  obtain ⟨y, hyH, hPy, -, hHy⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  have hHinv : H = Pc M V ⊔ conjSubgroup y⁻¹ (Pc M V) := by
    have h := congrArg (conjSubgroup y⁻¹) hHy
    rw [conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer (H.inv_mem hyH)),
      conjSubgroup_sup_eq_sup, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h
    exact h.trans (sup_comm _ _)
  have hv'P : y⁻¹ * v * y ∈ Pc M V := by
    have h : v ∈ conjSubgroup y (Pc M V) := by rw [← hPy]; exact hv.1
    exact mem_conjSubgroup.mp h
  have hv'W : y⁻¹ * v * y ∈ Tim79a.xOf V H := by
    simpa using
      (Subgroup.mem_normalizer_iff.mp (Tim79a.H_le_normalizer_xOf V H (H.inv_mem hyH)) v).mp hv.2
  have hx'Py : y⁻¹ * x * y ∈ conjSubgroup y⁻¹ (Pc M V) := by
    refine mem_conjSubgroup.mpr ?_
    have heq : (y⁻¹)⁻¹ * (y⁻¹ * x * y) * y⁻¹ = x := by group
    rw [heq]
    exact hx
  have hx'K : y⁻¹ * x * y ∉ kOf V H := by
    intro hmem
    have h : x ∈ conjSubgroup y (kOf V H) := mem_conjSubgroup.mpr hmem
    rw [conjSubgroup_kOf_eq_self_of_mem (V := V) (H := H) hyH] at h
    exact hxK h
  have hxv' : ⁅y⁻¹ * x * y, y⁻¹ * v * y⁆ ∈ W₀ := by
    have heq : ⁅y⁻¹ * x * y, y⁻¹ * v * y⁆ = y⁻¹ * ⁅x, v⁆ * y := by
      rw [commutatorElement_def, commutatorElement_def]
      group
    rw [heq]
    simpa using (Subgroup.mem_normalizer_iff.mp (hN (H.inv_mem hyH)) ⁅x, v⁆).mp hxv
  have hcomm : ⁅Pc M V ⊓ Tim79a.xOf V H, Pc M V⁆ ≤ V ⊓ W₀ :=
    commutator_inf_xOf_le h hPH hVH hH hnM hK hnab hL hW₀ hN hW₀ne
  have hmain := mem_W0_of_mem_inf_xOf_of_commutator_mem_aux (h₀ := y⁻¹) h hPH hVH hHinv
    hnM hW₀ hN ψ hl horth hcomm (v := y⁻¹ * v * y)
    (Subgroup.mem_inf.mpr ⟨hv'P, hv'W⟩) hx'Py hx'K hxv'
  have heq : y * (y⁻¹ * v * y) * y⁻¹ = v := by group
  rw [← heq]
  exact (Subgroup.mem_normalizer_iff.mp (hN hyH) (y⁻¹ * v * y)).mp hmain

end RootHyp

end CFSG.RankThree.GF2n.Tim81
