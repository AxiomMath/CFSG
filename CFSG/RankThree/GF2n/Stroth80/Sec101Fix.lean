module

public import CFSG.RankThree.GF2n.Stroth80.Sec101Clique
public import CFSG.RankThree.GF2n.Stroth80.Sec101Orbit
public import CFSG.RankThree.GF2n.Stroth80.Sec101Roots

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem IsRootB.exists_mem_not_mem_Z (hc : Ctx M Q Z B) {E : Subgroup G}
    (hE : IsRootB M B E) : ∃ x ∈ E, x ∉ Z := by
  have hcard : Nat.card E = Nat.card Z := by
    obtain ⟨m, hm, rfl⟩ := hE
    rw [card_conjSubgroup]
    obtain ⟨g, hg⟩ := hc.conj
    rw [hg, card_conjSubgroup]
  have hne : E ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    have := hc.hyp.q4
    omega
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  refine ⟨(x : G), x.2, ?_⟩
  intro hxZ
  have hmem : (x : G) ∈ E ⊓ Z := ⟨x.2, hxZ⟩
  rw [inf_comm, (hE.ctx hc).inf_eq_bot, Subgroup.mem_bot] at hmem
  exact hx1 (Subtype.ext hmem)

theorem IsSaturated101.conj (hc : Ctx M Q Z B) {X : Subgroup G}
    (hsat : IsSaturated101 M Q Z B X) {g : G} (hg : g ∈ M) :
    IsSaturated101 M Q Z B (conjSubgroup g X) := by
  intro C hC hCX D hD hDle
  have hginv : g⁻¹ ∈ M := M.inv_mem hg
  have hC0 : IsRootB M B (conjSubgroup g⁻¹ C) := hC.conj hginv
  have hC0X : conjSubgroup g⁻¹ C ≤ X := by
    calc conjSubgroup g⁻¹ C ≤ conjSubgroup g⁻¹ (conjSubgroup g X) := Subgroup.map_mono hCX
      _ = X := by rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  have hD0 : IsRootB M B (conjSubgroup g⁻¹ D) := hD.conj hginv
  have hD0le : conjSubgroup g⁻¹ D ≤ Q ⊓ QB (conjSubgroup g⁻¹ C) := by
    calc conjSubgroup g⁻¹ D ≤ conjSubgroup g⁻¹ (Q ⊓ QB C) := Subgroup.map_mono hDle
      _ = conjSubgroup g⁻¹ Q ⊓ conjSubgroup g⁻¹ (QB C) := conjSubgroup_inf g⁻¹ Q (QB C)
      _ = Q ⊓ QB (conjSubgroup g⁻¹ C) := by rw [hc.conj_Q_eq hginv, QB_conj]
  have hD0X : conjSubgroup g⁻¹ D ≤ X := hsat (conjSubgroup g⁻¹ C) hC0 hC0X
    (conjSubgroup g⁻¹ D) hD0 hD0le
  calc D = conjSubgroup g (conjSubgroup g⁻¹ D) := by
        rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
    _ ≤ conjSubgroup g X := Subgroup.map_mono hD0X

theorem IsSaturated101.inf_eq (hc : Ctx M Q Z B) {X : Subgroup G} (hX : IsClique101 M Q Z B X)
    (hsat : IsSaturated101 M Q Z B X) {g : G} (hg : g ∈ M) :
    X ⊓ conjSubgroup g X = Z ∨ conjSubgroup g X = X := by
  by_cases hZ : X ⊓ conjSubgroup g X = Z
  · exact Or.inl hZ
  · refine Or.inr ?_
    have hXg : IsClique101 M Q Z B (conjSubgroup g X) := hX.conj hc hg
    have hZle : Z ≤ X ⊓ conjSubgroup g X := by
      refine le_inf hX.Z_le ?_
      rw [← hc.conj_Z_eq hg]
      exact Subgroup.map_mono hX.Z_le
    have hnot : ¬ X ⊓ conjSubgroup g X ≤ Z := fun hle => hZ (le_antisymm hle hZle)
    obtain ⟨x, hx, hxZ⟩ := Set.not_subset.mp hnot
    have hx1 : x ≠ 1 := fun h => hxZ (h ▸ Z.one_mem)
    obtain ⟨C, hC, hxC, hCX⟩ := hX.cover x hx.1 hxZ
    obtain ⟨C', hC', hxC', hC'Xg⟩ := hXg.cover x hx.2 hxZ
    have hCC' : C = C' :=
      Smith81.IsZConjugate.eq_of_mem hc.hyp (hC.isZConjugate hc) (hC'.isZConjugate hc)
        hx1 hxC hxC'
    have hC''Xg : C ≤ conjSubgroup g X := by rwa [← hCC'] at hC'Xg
    have hXgQB : conjSubgroup g X ≤ QB C := hXg.le_QB C hC hC''Xg
    have hle : conjSubgroup g X ≤ X := by
      refine hXg.le_of_roots hX.Z_le ?_
      intro D hD hDXg
      exact hsat C hC hCX D hD
        (le_inf (hDXg.trans hXg.le_Q) (hDXg.trans hXgQB))
    have hcard : Nat.card (conjSubgroup g X) = Nat.card X := card_conjSubgroup g X
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])

private theorem IsSaturated101.conj_eq_of_LB_eq (hc : Ctx M Q Z B) {n : ℕ}
    (H : Sec10Hyp hc n) {X : Subgroup G} (hX : IsClique101 M Q Z B X)
    (hsat : IsSaturated101 M Q Z B X) {C : Subgroup G} (hC : IsRootB M B C) (hCX : C ≤ X)
    {g : G} (hg : g ∈ M) (hLCeq : LB M Q (conjSubgroup g C) = LB M Q C) :
    conjSubgroup g X = X := by
  have hC' : IsRootB M B (conjSubgroup g C) := hC.conj hg
  have hsup : conjSubgroup g C ⊔ Z = C ⊔ Z := (IsRootB.LB_eq_iff H hC' hC).mp hLCeq
  have hC'X : conjSubgroup g C ≤ X := by
    calc conjSubgroup g C ≤ conjSubgroup g C ⊔ Z := le_sup_left
      _ = C ⊔ Z := hsup
      _ ≤ X := sup_le hCX hX.Z_le
  obtain ⟨x, hxC', hxZ⟩ := hC'.exists_mem_not_mem_Z hc
  have hxX : x ∈ X := hC'X hxC'
  have hxXg : x ∈ conjSubgroup g X := (Subgroup.map_mono hCX) hxC'
  rcases IsSaturated101.inf_eq hc hX hsat hg with h | h
  · exfalso
    exact hxZ (h ▸ (show x ∈ X ⊓ conjSubgroup g X from ⟨hxX, hxXg⟩))
  · exact h

private theorem IsSaturated101.le_inf_QB_of_LB_ne (h34 : Stroth34Statement)
    {hc : Ctx M Q Z B} {n : ℕ} {c : G} (hcM : c ∈ M)
    (H : Sec10Hyp (hc.conj_of_mem hcM) n) {g : G} (hg : g ∈ M)
    (hLCne : LB M Q (conjSubgroup g (conjSubgroup c B)) ≠ LB M Q (conjSubgroup c B))
    {t : G} (ht : t ∈ LB M Q (conjSubgroup c B) ⊓
      conjSubgroup g (LB M Q (conjSubgroup c B))) (htQ : t ∉ Q) :
    conjSubgroup g (conjSubgroup c B) ≤ Q ⊓ QB (conjSubgroup c B) := by
  have hcC : Ctx M Q Z (conjSubgroup c B) := hc.conj_of_mem hcM
  have hRtne : Rt M (LB M Q (conjSubgroup c B)) t ≠ LB M Q (conjSubgroup c B) := by
    intro hRt
    apply hLCne
    have hle : LB M Q (conjSubgroup g (conjSubgroup c B)) ≤
        LB M Q (conjSubgroup c B) := by
      calc LB M Q (conjSubgroup g (conjSubgroup c B))
          ≤ Rt M (LB M Q (conjSubgroup c B)) t := hcC.LB_conj_le_Rt hg ht.2
        _ = LB M Q (conjSubgroup c B) := hRt
    have hcard : Nat.card (LB M Q (conjSubgroup g (conjSubgroup c B))) =
        Nat.card (LB M Q (conjSubgroup c B)) := by
      rw [hcC.LB_conj hg, card_conjSubgroup]
    exact Subgroup.eq_of_le_of_card_ge hle hcard.ge
  have hsl : SLlike hcC t := (H.alt t ht.1 htQ).resolve_left hRtne
  obtain ⟨m, hm2, hslm⟩ := hsl.exists_SLMNat
  have hslC : SLNat hcC t := hslm.toSLNat hm2
  have hs : Sec5Hyp hcC n t := H.toSec5 ht.1 htQ
  have h35 : CQt Q Z (LB M Q (conjSubgroup c B)) =
      (((conjSubgroup c B) ⊔ Z : Subgroup G) : Set G) :=
    (stroth_3_5 h34 hcC H.width H.n_gt H.noA2 H.gen).2.1
  exact (sec39_conjB_le_Vt hg ht.2).trans (hcC.Vt_le_inf_QB_of_SLNat hs h35 hslC)

private theorem IsSaturated101.conj_eq_of_LB_ne (hc : Ctx M Q Z B) {X : Subgroup G}
    (hX : IsClique101 M Q Z B X) (hsat : IsSaturated101 M Q Z B X) {C : Subgroup G}
    (hC : IsRootB M B C) (hCX : C ≤ X) {g : G} (hg : g ∈ M)
    (hC'le : conjSubgroup g C ≤ Q ⊓ QB C) (hCne : C ≠ conjSubgroup g C) :
    conjSubgroup g X = X := by
  have hC' : IsRootB M B (conjSubgroup g C) := hC.conj hg
  have hC_le_QB : C ≤ QB (conjSubgroup g C) :=
    (StrothHyp.le_QB_iff_le_QB hc.hyp (hC.isZConjugate hc) (hC'.isZConjugate hc)
      hCne).mpr (hC'le.trans inf_le_right)
  have hsatg : IsSaturated101 M Q Z B (conjSubgroup g X) := hsat.conj hc hg
  have hC_Xg : C ≤ conjSubgroup g X :=
    hsatg (conjSubgroup g C) hC' (Subgroup.map_mono hCX) C hC
      (le_inf (hCX.trans hX.le_Q) hC_le_QB)
  obtain ⟨x, hxC, hxZ⟩ := hC.exists_mem_not_mem_Z hc
  have hxX : x ∈ X := hCX hxC
  have hxXg : x ∈ conjSubgroup g X := hC_Xg hxC
  rcases IsSaturated101.inf_eq hc hX hsat hg with h | h
  · exfalso
    exact hxZ (h ▸ (show x ∈ X ⊓ conjSubgroup g X from ⟨hxX, hxXg⟩))
  · exact h

theorem IsSaturated101.conj_eq_of_LB (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) {X : Subgroup G} (hX : IsClique101 M Q Z B X)
    (hsat : IsSaturated101 M Q Z B X) {C : Subgroup G} (hC : IsRootB M B C) (hCX : C ≤ X)
    {g : G} (hg : g ∈ M) (hne : LB M Q C ⊓ conjSubgroup g (LB M Q C) ≠ Q) :
    conjSubgroup g X = X := by
  obtain ⟨c, hcM, rfl⟩ := hC
  have HC : Sec10Hyp (hc.conj_of_mem hcM) n := H.conj_of_mem hcM
  have hQle : Q ≤ LB M Q (conjSubgroup c B) ⊓
      conjSubgroup g (LB M Q (conjSubgroup c B)) := by
    refine le_inf sec39_Q_le_LB ?_
    calc Q = conjSubgroup g Q := (hc.conj_Q_eq hg).symm
      _ ≤ conjSubgroup g (LB M Q (conjSubgroup c B)) := Subgroup.map_mono sec39_Q_le_LB
  obtain ⟨t, ht, htQ⟩ := Set.not_subset.mp (fun hle => hne (le_antisymm hle hQle))
  by_cases hLCeq : LB M Q (conjSubgroup g (conjSubgroup c B)) =
      LB M Q (conjSubgroup c B)
  · exact IsSaturated101.conj_eq_of_LB_eq hc H hX hsat ⟨c, hcM, rfl⟩ hCX hg hLCeq
  · have hC'le : conjSubgroup g (conjSubgroup c B) ≤ Q ⊓ QB (conjSubgroup c B) :=
      IsSaturated101.le_inf_QB_of_LB_ne (hc := hc) h34 hcM HC hg hLCeq ht htQ
    exact IsSaturated101.conj_eq_of_LB_ne hc hX hsat ⟨c, hcM, rfl⟩ hCX hg hC'le
      (fun hEq => hLCeq (congrArg (LB M Q) hEq).symm)

end CFSG.RankThree.GF2n.Stroth80
