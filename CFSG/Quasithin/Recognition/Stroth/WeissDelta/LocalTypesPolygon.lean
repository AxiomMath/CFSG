module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.VertexFacts
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.Valency

public section

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {X : Type} [Group X] {P1 P2 : Subgroup X} {Y : Type} [Group Y] [Finite Y]

private theorem localGroup_eq_rangeGroup_of
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) [Fintype c.Γ]
    [DecidableRel c.graph.Adj] {P : Subgroup X} {ψ : ↥P →* c.G0} {u : c.Γ}
    (hψu : ψ.range ≤ MulAction.stabilizer c.G0 u)
    (hψ : ψ.range = MulAction.stabilizer c.G0 u) :
    localGroup c.G0 c.graph u =
      rangeGroup (Γ := c.graph) (P1 := P) (ψ1 := ψ) (u := u) hψu := by
  ext σ
  constructor
  · rintro ⟨g, rfl⟩
    rw [mem_rangeGroup_iff (P1 := P) (ψ1 := ψ) (u := u) hψu]
    have hg : (g : c.G0) ∈ ψ.range := by
      rw [hψ]
      exact g.2
    obtain ⟨a, ha⟩ := hg
    refine ⟨a, fun w => ?_⟩
    show (g : c.G0) • w.1 = _
    rw [← ha]
  · intro hσ
    obtain ⟨a, ha⟩ := (mem_rangeGroup_iff (P1 := P) (ψ1 := ψ) (u := u) hψu σ).mp hσ
    refine ⟨⟨ψ a, hψu ⟨a, rfl⟩⟩, ?_⟩
    ext w
    show (ψ a : c.G0) • w.1 = (σ w).1
    rw [ha w]

private theorem isMultiplyPretransitive_rangeGroup_of
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) [Fintype c.Γ]
    [DecidableRel c.graph.Adj] {P : Subgroup X} {ψ : ↥P →* c.G0} {u : c.Γ}
    (hψu : ψ.range ≤ MulAction.stabilizer c.G0 u)
    (h2t : @MulAction.IsMultiplyPretransitive
      ↥(rangeGroup (Γ := c.graph) (P1 := P) (ψ1 := ψ) (u := u) hψu)
      (nbrs (Γ := c.graph) u)
      _ (rangeAction (Γ := c.graph) (P1 := P) (ψ1 := ψ) (u := u) hψu) 2) :
    MulAction.IsMultiplyPretransitive
      ↥(rangeGroup (Γ := c.graph) (P1 := P) (ψ1 := ψ) (u := u) hψu)
      (nbrs (Γ := c.graph) u) 2 := by
  rw [MulAction.is_two_pretransitive_iff]
  rw [@MulAction.is_two_pretransitive_iff _ _ _
    (rangeAction (Γ := c.graph) (P1 := P) (ψ1 := ψ) (u := u) hψu)] at h2t
  intro a b d e hab hde
  obtain ⟨g, hg1, hg2⟩ := h2t hab hde
  refine ⟨g, ?_, ?_⟩
  · rw [Subgroup.smul_def, Equiv.Perm.smul_def]
    exact (rangeAction_smul_eq hψu g a).symm.trans hg1
  · rw [Subgroup.smul_def, Equiv.Perm.smul_def]
    exact (rangeAction_smul_eq hψu g b).symm.trans hg2

private theorem card_nbrs_xv_of_sz {n a : ℕ} (hn : 3 ≤ n)
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) (hc : c.IsFaithful)
    (hM : MoufangCondition c.G0 c.graph n) (hW : WeissFree c.G0 c.graph n) (ha : 1 ≤ a)
    (hSz : HasNormalCopy (Subconst P1 P2) ↥(Sz a))
    (hV1 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P1 = 2 ^ e + 1)
    (hV2 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P2 = 2 ^ e + 1) :
    Nat.card {w : c.Γ // c.graph.Adj c.xv w} = 2 ^ (2 * (2 * a + 1)) + 1 := by
  have h1 : Nat.card (c.graph.neighborSet c.xv) = (P1 ⊓ P2).relIndex P1 :=
    card_neighborSet_xv c hc
  have h2 : (P1 ⊓ P2).relIndex P1 = 2 ^ (2 * (2 * a + 1)) + 1 :=
    relIndex_eq_of_sz hn c hc hM hW ha hSz hV1 hV2
  rw [show Nat.card {w : c.Γ // c.graph.Adj c.xv w} =
    Nat.card (c.graph.neighborSet c.xv) from rfl, h1, h2]

private theorem card_nbrs_xv_of_u3 {n k : ℕ} (hn : 3 ≤ n)
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) (hc : c.IsFaithful)
    (hM : MoufangCondition c.G0 c.graph n) (hW : WeissFree c.G0 c.graph n) (hk : 2 ≤ k)
    (F : Type) [Field F] [Finite F] (hF : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : HasNormalCopy (Subconst P1 P2) (StatedProj (StatedSU 3 (2 ^ k) F)))
    (hV1 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P1 = 2 ^ e + 1)
    (hV2 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P2 = 2 ^ e + 1) :
    Nat.card {w : c.Γ // c.graph.Adj c.xv w} = 2 ^ (3 * k) + 1 := by
  have h1 : Nat.card (c.graph.neighborSet c.xv) = (P1 ⊓ P2).relIndex P1 :=
    card_neighborSet_xv c hc
  have h2 : (P1 ⊓ P2).relIndex P1 = 2 ^ (3 * k) + 1 :=
    relIndex_eq_of_u3 hn c hc hM hW hk F hF hU3 hV1 hV2
  rw [show Nat.card {w : c.Γ // c.graph.Adj c.xv w} =
    Nat.card (c.graph.neighborSet c.xv) from rfl, h1, h2]

private theorem card_nbrs_lv_of_l2 {n m : ℕ} (hn : 3 ≤ n)
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) (hc : c.IsFaithful)
    (hM : MoufangCondition c.G0 c.graph n) (hW : WeissFree c.G0 c.graph n) (hm : 2 ≤ m)
    (hL2 : HasNormalCopy (Subconst P2 P1)
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m)))
    (hV1 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P1 = 2 ^ e + 1)
    (hV2 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P2 = 2 ^ e + 1) :
    Nat.card {w : c.Γ // c.graph.Adj c.lv w} = 2 ^ m + 1 := by
  have h1 : Nat.card (c.graph.neighborSet c.lv) = (P1 ⊓ P2).relIndex P2 :=
    card_neighborSet_lv c hc
  have h2 : (P1 ⊓ P2).relIndex P2 = 2 ^ m + 1 :=
    relIndex_eq_of_l2 hn c hc hM hW hm hL2 hV1 hV2
  rw [show Nat.card {w : c.Γ // c.graph.Adj c.lv w} =
    Nat.card (c.graph.neighborSet c.lv) from rfl, h1, h2]

private theorem isLocalSz_xv_of_completion {n : ℕ} (hn : 3 ≤ n)
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) (hc : c.IsFaithful)
    (hM : MoufangCondition c.G0 c.graph n) (hW : WeissFree c.G0 c.graph n)
    {a : ℕ} (ha : 1 ≤ a) (hSz : HasNormalCopy (Subconst P1 P2) ↥(Sz a))
    (hV1 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P1 = 2 ^ e + 1)
    (hV2 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P2 = 2 ^ e + 1) :
    IsLocalSz c.G0 c.graph c.xv a := by
  classical
  haveI : Fintype c.Γ := Fintype.ofFinite c.Γ
  haveI : DecidableRel c.graph.Adj := fun v w => Classical.dec _
  let ψ1 : ↥P1 →* c.G0 := RankTwoAmalgam.Completion.f1 (c := c)
  let hψ1u : ψ1.range ≤ MulAction.stabilizer c.G0 c.xv := f1_range_le_stabilizer_xv c
  have hv1 : 2 ≤ (P1 ⊓ P2).relIndex P1 := by
    obtain ⟨e, he, hrel⟩ := hV1
    rw [hrel]
    have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    omega
  have hv2 : 2 ≤ (P1 ⊓ P2).relIndex P2 := by
    obtain ⟨e, he, hrel⟩ := hV2
    rw [hrel]
    have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    omega
  obtain ⟨R, hRle, hRreg⟩ := exists_regular_root_xv hn c hc hM hW hv1 hv2
  obtain ⟨hN, -, h2t⟩ := subconstNatural_data (Γ := c.graph) (D := c.G0)
    (X := X) (P1 := P1) (P2 := P2) (ψ1 := ψ1) (u := c.xv) (v := c.lv)
    (RankTwoAmalgam.Completion.f1_injective c hc) hψ1u (f1_range_inf_stabilizer_lv c hc)
    (fun w hw => exists_f1_smul_lv c hw) R hRle hRreg CosetGeom.adj_γ₀_γ₁ hSz
  have hcard := card_nbrs_xv_of_sz hn c hc hM hW ha hSz hV1 hV2
  have h2nat := isMultiplyPretransitive_rangeGroup_of (c := c) (P := P1) (ψ := ψ1)
    (u := c.xv) hψ1u h2t
  have hgrp := localGroup_eq_rangeGroup_of (c := c) (P := P1) (ψ := ψ1) (u := c.xv)
    hψ1u (f1_range_eq_stabilizer_xv c)
  refine ⟨hcard, ?_, ?_⟩
  · exact hgrp.symm ▸ h2nat
  · exact hgrp.symm ▸ hN

private theorem isLocalU3_xv_of_completion {n : ℕ} (hn : 3 ≤ n)
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) (hc : c.IsFaithful)
    (hM : MoufangCondition c.G0 c.graph n) (hW : WeissFree c.G0 c.graph n)
    {k : ℕ} (hk : 2 ≤ k) (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : HasNormalCopy (Subconst P1 P2) (StatedProj (StatedSU 3 (2 ^ k) F)))
    (hV1 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P1 = 2 ^ e + 1)
    (hV2 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P2 = 2 ^ e + 1) :
    IsLocalU3 c.G0 c.graph c.xv k F := by
  classical
  haveI : Fintype c.Γ := Fintype.ofFinite c.Γ
  haveI : DecidableRel c.graph.Adj := fun v w => Classical.dec _
  let ψ1 : ↥P1 →* c.G0 := RankTwoAmalgam.Completion.f1 (c := c)
  let hψ1u : ψ1.range ≤ MulAction.stabilizer c.G0 c.xv := f1_range_le_stabilizer_xv c
  have hv1 : 2 ≤ (P1 ⊓ P2).relIndex P1 := by
    obtain ⟨e, he, hrel⟩ := hV1
    rw [hrel]
    have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    omega
  have hv2 : 2 ≤ (P1 ⊓ P2).relIndex P2 := by
    obtain ⟨e, he, hrel⟩ := hV2
    rw [hrel]
    have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    omega
  obtain ⟨R, hRle, hRreg⟩ := exists_regular_root_xv hn c hc hM hW hv1 hv2
  obtain ⟨hN, -, h2t⟩ := subconstNatural_data (Γ := c.graph) (D := c.G0)
    (X := X) (P1 := P1) (P2 := P2) (ψ1 := ψ1) (u := c.xv) (v := c.lv)
    (RankTwoAmalgam.Completion.f1_injective c hc) hψ1u (f1_range_inf_stabilizer_lv c hc)
    (fun w hw => exists_f1_smul_lv c hw) R hRle hRreg CosetGeom.adj_γ₀_γ₁ hU3
  have hcard := card_nbrs_xv_of_u3 hn c hc hM hW hk F hF hU3 hV1 hV2
  have h2nat := isMultiplyPretransitive_rangeGroup_of (c := c) (P := P1) (ψ := ψ1)
    (u := c.xv) hψ1u h2t
  have hgrp := localGroup_eq_rangeGroup_of (c := c) (P := P1) (ψ := ψ1) (u := c.xv)
    hψ1u (f1_range_eq_stabilizer_xv c)
  refine ⟨hcard, ?_, ?_⟩
  · exact hgrp.symm ▸ h2nat
  · exact hgrp.symm ▸ hN

private theorem isLocalL2_lv_of_completion {n : ℕ} (hn : 3 ≤ n)
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) (hc : c.IsFaithful)
    (hM : MoufangCondition c.G0 c.graph n) (hW : WeissFree c.G0 c.graph n)
    {m : ℕ} (hm : 2 ≤ m)
    (hL2 : HasNormalCopy (Subconst P2 P1)
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m)))
    (hV1 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P1 = 2 ^ e + 1)
    (hV2 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P2 = 2 ^ e + 1) :
    IsLocalL2 c.G0 c.graph c.lv m := by
  classical
  haveI : Fintype c.Γ := Fintype.ofFinite c.Γ
  haveI : DecidableRel c.graph.Adj := fun v w => Classical.dec _
  let ψ2 : ↥P2 →* c.G0 := RankTwoAmalgam.Completion.f2 (c := c)
  let hψ2v : ψ2.range ≤ MulAction.stabilizer c.G0 c.lv := f2_range_le_stabilizer_lv c
  have hv1 : 2 ≤ (P1 ⊓ P2).relIndex P1 := by
    obtain ⟨e, he, hrel⟩ := hV1
    rw [hrel]
    have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    omega
  have hv2 : 2 ≤ (P1 ⊓ P2).relIndex P2 := by
    obtain ⟨e, he, hrel⟩ := hV2
    rw [hrel]
    have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    omega
  obtain ⟨R, hRle, hRreg⟩ := exists_regular_root_lv hn c hc hM hW hv1 hv2
  obtain ⟨hN, -, h2t⟩ := subconstNatural_data (Γ := c.graph) (D := c.G0)
    (X := X) (P1 := P2) (P2 := P1) (ψ1 := ψ2) (u := c.lv) (v := c.xv)
    (RankTwoAmalgam.Completion.f2_injective c hc) hψ2v (f2_range_inf_stabilizer_xv c hc)
    (fun w hw => exists_f2_smul_xv c hw) R hRle hRreg CosetGeom.adj_γ₀_γ₁.symm hL2
  have hcard := card_nbrs_lv_of_l2 hn c hc hM hW hm hL2 hV1 hV2
  have h2nat := isMultiplyPretransitive_rangeGroup_of (c := c) (P := P2) (ψ := ψ2)
    (u := c.lv) hψ2v h2t
  have hgrp := localGroup_eq_rangeGroup_of (c := c) (P := P2) (ψ := ψ2) (u := c.lv)
    hψ2v (f2_range_eq_stabilizer_lv c)
  refine ⟨hcard, ?_, ?_⟩
  · exact hgrp.symm ▸ h2nat
  · exact hgrp.symm ▸ hN

theorem isLocal_of_polygon8
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) (hc : c.IsFaithful)
    (hM : MoufangCondition c.G0 c.graph 8) (hW : WeissFree c.G0 c.graph 8)
    {a m : ℕ} (ha : 1 ≤ a) (hm : 2 ≤ m)
    (hSz : HasNormalCopy (Subconst P1 P2) ↥(Sz a))
    (hL2 : HasNormalCopy (Subconst P2 P1)
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m)))
    (hV1 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P1 = 2 ^ e + 1)
    (hV2 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P2 = 2 ^ e + 1) (g : c.G0) :
    IsLocalSz c.G0 c.graph (g • c.xv) a ∧ IsLocalL2 c.G0 c.graph (g • c.lv) m :=
  ⟨isLocalSz_smul (isLocalSz_xv_of_completion (n := 8) (by norm_num) c hc hM hW
      ha hSz hV1 hV2) g,
    isLocalL2_smul (isLocalL2_lv_of_completion (n := 8) (by norm_num) c hc hM hW
      hm hL2 hV1 hV2) g⟩

theorem isLocal_of_polygon4
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) (hc : c.IsFaithful)
    (hM : MoufangCondition c.G0 c.graph 4) (hW : WeissFree c.G0 c.graph 4)
    {k m : ℕ} (F : Type) [Field F] [Finite F] (hk : 2 ≤ k) (hm : 3 ≤ m)
    (hF : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : HasNormalCopy (Subconst P1 P2) (StatedProj (StatedSU 3 (2 ^ k) F)))
    (hL2 : HasNormalCopy (Subconst P2 P1)
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m)))
    (hV1 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P1 = 2 ^ e + 1)
    (hV2 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P2 = 2 ^ e + 1) (g : c.G0) :
    IsLocalU3 c.G0 c.graph (g • c.xv) k F ∧ IsLocalL2 c.G0 c.graph (g • c.lv) m :=
  ⟨isLocalU3_smul (isLocalU3_xv_of_completion (n := 4) (by norm_num) c hc hM hW
      hk F hF hU3 hV1 hV2) g,
    isLocalL2_smul (isLocalL2_lv_of_completion (n := 4) (by norm_num) c hc hM hW
      (by omega) hL2 hV1 hV2) g⟩

private theorem exists_two_adj (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    (hc : c.IsFaithful) (hv1 : 2 ≤ (P1 ⊓ P2).relIndex P1)
    (hv2 : 2 ≤ (P1 ⊓ P2).relIndex P2) (v : c.Γ) :
    ∃ w w' : c.Γ, c.graph.Adj v w ∧ c.graph.Adj v w' ∧ w ≠ w' := by
  have hval : 2 ≤ Nat.card (c.graph.neighborSet v) := by
    rcases card_neighborSet_eq c hc v with ⟨-, hv⟩ | ⟨-, hv⟩
    · rw [hv]; exact hv1
    · rw [hv]; exact hv2
  have h1 : 1 < (c.graph.neighborSet v).ncard := by
    rw [← Nat.card_coe_set_eq]
    omega
  have hpos : 0 < (c.graph.neighborSet v).ncard := by omega
  obtain ⟨w, hw⟩ := (Set.ncard_pos (Set.toFinite _)).mp hpos
  obtain ⟨w', hw', hne⟩ := Set.exists_ne_of_one_lt_ncard h1 w
  exact ⟨w, w', by simpa using hw, by simpa using hw', hne.symm⟩

theorem localFacts_of_polygon8
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) (hc : c.IsFaithful)
    (hM : MoufangCondition c.G0 c.graph 8) (hW : WeissFree c.G0 c.graph 8)
    (hg : ((2 * 8 + 2 : ℕ) : ℕ∞) < c.graph.egirth) {a m : ℕ} (ha : 1 ≤ a) (hm : 2 ≤ m)
    (hSz : HasNormalCopy (Subconst P1 P2) ↥(Sz a))
    (hL2 : HasNormalCopy (Subconst P2 P1)
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m)))
    (hV1 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P1 = 2 ^ e + 1)
    (hV2 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P2 = 2 ^ e + 1) :
    ∀ z : c.Γ, LocalFacts c.G0 c.graph z ∧ ZassenhausFacts c.G0 c.graph z := by
  have hv1 : 2 ≤ (P1 ⊓ P2).relIndex P1 := by
    obtain ⟨e, he, hrel⟩ := hV1
    rw [hrel]
    have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    omega
  have hv2 : 2 ≤ (P1 ⊓ P2).relIndex P2 := by
    obtain ⟨e, he, hrel⟩ := hV2
    rw [hrel]
    have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    omega
  have hg4 : (4 : ℕ∞) < c.graph.egirth := by
    refine lt_trans ?_ hg
    norm_num
  have htwin := twinFree_of_egirth (Γ := c.graph) hg4
    (fun v => exists_two_adj c hc hv1 hv2 v)
  have hK : ∀ z : c.Γ, FixingNeighbourhoodFixesVertex (H := c.G0) (Γ := c.graph) z :=
    fun z => fixingSubgroup_le_stabilizer_of_twinFree (H := c.G0) (Γ := c.graph) htwin z
  intro z
  obtain (⟨g, hg⟩ | ⟨g, hg⟩) := exists_smul_eq_xv_or_lv (c := c) z
  · rw [← hg]
    obtain ⟨hSzg, -⟩ := isLocal_of_polygon8 c hc hM hW ha hm hSz hL2 hV1 hV2 g
    obtain ⟨hL, hZ, -⟩ := vertexFacts_of_isLocalSz (H := c.G0) (Γ := c.graph) (a := a)
      ha (hK (g • c.xv)) hSzg
    exact ⟨hL, hZ⟩
  · rw [← hg]
    obtain ⟨-, hL2g⟩ := isLocal_of_polygon8 c hc hM hW ha hm hSz hL2 hV1 hV2 g
    obtain ⟨hL, hZ, -, -⟩ := vertexFacts_of_isLocalL2 (H := c.G0) (Γ := c.graph) (m := m)
      hm (hK (g • c.lv)) hL2g
    exact ⟨hL, hZ⟩

theorem localFacts_of_polygon4
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) (hc : c.IsFaithful)
    (hM : MoufangCondition c.G0 c.graph 4) (hW : WeissFree c.G0 c.graph 4)
    (hg : ((2 * 4 + 2 : ℕ) : ℕ∞) < c.graph.egirth) {k m : ℕ} (F : Type) [Field F] [Finite F]
    (hk : 2 ≤ k) (hm : 3 ≤ m) (hF : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : HasNormalCopy (Subconst P1 P2) (StatedProj (StatedSU 3 (2 ^ k) F)))
    (hL2 : HasNormalCopy (Subconst P2 P1)
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m)))
    (hV1 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P1 = 2 ^ e + 1)
    (hV2 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P2 = 2 ^ e + 1) :
    ∀ z : c.Γ, LocalFacts c.G0 c.graph z := by
  have hv1 : 2 ≤ (P1 ⊓ P2).relIndex P1 := by
    obtain ⟨e, he, hrel⟩ := hV1
    rw [hrel]
    have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    omega
  have hv2 : 2 ≤ (P1 ⊓ P2).relIndex P2 := by
    obtain ⟨e, he, hrel⟩ := hV2
    rw [hrel]
    have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    omega
  have hg4 : (4 : ℕ∞) < c.graph.egirth := by
    refine lt_trans ?_ hg
    norm_num
  have htwin := twinFree_of_egirth (Γ := c.graph) hg4
    (fun v => exists_two_adj c hc hv1 hv2 v)
  have hK : ∀ z : c.Γ, FixingNeighbourhoodFixesVertex (H := c.G0) (Γ := c.graph) z :=
    fun z => fixingSubgroup_le_stabilizer_of_twinFree (H := c.G0) (Γ := c.graph) htwin z
  intro z
  obtain (⟨g, hg⟩ | ⟨g, hg⟩) := exists_smul_eq_xv_or_lv (c := c) z
  · rw [← hg]
    obtain ⟨hU3g, -⟩ := isLocal_of_polygon4 c hc hM hW F hk hm hF hU3 hL2 hV1 hV2 g
    obtain ⟨hL, -, -⟩ := vertexFacts_of_isLocalU3 (H := c.G0) (Γ := c.graph) (k := k)
      hk F hF (hK (g • c.xv)) hU3g
    exact hL
  · rw [← hg]
    obtain ⟨-, hL2g⟩ := isLocal_of_polygon4 c hc hM hW F hk hm hF hU3 hL2 hV1 hV2 g
    obtain ⟨hL, -, -, -⟩ := vertexFacts_of_isLocalL2 (H := c.G0) (Γ := c.graph) (m := m)
      (by omega) (hK (g • c.lv)) hL2g
    exact hL

end CFSG.Quasithin.Stroth.WeissDelta

end
