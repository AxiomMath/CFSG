module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12InvTools

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def M12InvHyp {G : Type} [Group G] [Finite G] (Y : Subgroup G) : Prop :=
  haveI : (solvableRadical Y).Normal := Subgroup.normal_sSup _ fun _ hN => hN.1
  Nonempty (Y ⧸ solvableRadical Y ≃* CFSG.Blueprint.NativeSporadic.M12)

@[expose] def InvPartA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (F : Subgroup G) (b : G) (Y : Subgroup G),
    Sec13Data G F b Y → M12InvHyp Y →
      Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* CFSG.Blueprint.NativeSporadic.M12) ∧
        b ∉ Y ∧ Nat.card (F ⊓ Y : Subgroup G) = 9

@[expose] def InvPartB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E F : Subgroup G) (a b : G)
    (R Y : Subgroup G), YCfg G A c L E F a b R Y →
      Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* CFSG.Blueprint.NativeSporadic.M12) → b ∉ Y →
      Nat.card (F ⊓ Y : Subgroup G) = 9 → E ⊔ F ≤ Subgroup.zpowers b ⊔ Y

@[expose] def InvPartC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E F : Subgroup G) (a b : G)
    (R Y : Subgroup G), YCfg G A c L E F a b R Y → b ∉ Y →
      E ⊔ F ≤ Subgroup.zpowers b ⊔ Y →
      E = Subgroup.zpowers b ⊔ (E ⊓ Y) ∧ Nat.card (E ⊓ Y : Subgroup G) = 9 ∧ c ∈ Y

@[expose] def InvPartD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (E Y : Subgroup G) (b : G),
    CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
    E ≤ Subgroup.normalizer (Y : Set G) → (∀ y ∈ Y, y * b = b * y) → b ∈ E →
    E = Subgroup.zpowers b ⊔ (E ⊓ Y) →
    ∀ V : Subgroup (Y ⧸ aschbacherSolvableCore 3 Y), V ≠ ⊥ → IsPGroup 2 V →
      ((E ⊓ Y).subgroupOf Y).map (QuotientGroup.mk' (aschbacherSolvableCore 3 Y)) ≤
        Subgroup.normalizer (V : Set (Y ⧸ aschbacherSolvableCore 3 Y)) →
      E ∈ partTwoE G

@[expose] def InvPartE : Prop :=
  ∀ (X : Type) [Group X], Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M12) →
    ∀ B : Subgroup X, Nat.card B = 9 →
      (∃ t ∈ Subgroup.normalizer (B : Set X), ∀ x ∈ B, t * x * t⁻¹ = x⁻¹) ∨
        ∃ V : Subgroup X, V ≠ ⊥ ∧ IsPGroup 2 V ∧ B ≤ Subgroup.normalizer (V : Set X)

@[expose] def InvPartF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y X : Subgroup G), X ≤ Y → (∀ x ∈ X, x ^ 3 = 1) →
    ∀ tb ∈ Subgroup.normalizer
        (((X.subgroupOf Y).map (QuotientGroup.mk' (aschbacherSolvableCore 3 Y)) :
          Subgroup (Y ⧸ aschbacherSolvableCore 3 Y)) : Set (Y ⧸ aschbacherSolvableCore 3 Y)),
      (∀ x ∈ (X.subgroupOf Y).map (QuotientGroup.mk' (aschbacherSolvableCore 3 Y)),
        tb * x * tb⁻¹ = x⁻¹) →
      ∃ t ∈ Y, ∀ x ∈ X, t * x * t⁻¹ = x⁻¹

open M12Inv in
theorem m12Inverting_of_parts (hA : InvPartA) (hB : InvPartB) (hC : InvPartC) (hD : InvPartD)
    (hE : InvPartE) (hF : InvPartF) : M12Inverting := by
  intro G _ _ A c L E F a b R Y hY hM
  have hDb : Sec13Data G F b Y := hY.hD
  obtain ⟨hMθ, hbY, hF9⟩ := hA G F b Y hDb hM
  have hEF := hB G A c L E F a b R Y hY hMθ hbY hF9
  obtain ⟨hdec, hE9, hcY⟩ := hC G A c L E F a b R Y hY hbY hEF
  have hEe := hY.hCfg.hEe
  have hbc : ∀ y ∈ Y, y * b = b * y := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mp (hDb.le_centralizer hy)
  have hXexp : ∀ x ∈ (E ⊓ Y : Subgroup G), x ^ 3 = 1 := fun x hx => hEe.2 x hx.1
  have hX3 : IsPGroup 3 ((E ⊓ Y).subgroupOf Y) := by
    intro x
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    have := hXexp _ (Subgroup.mem_subgroupOf.mp x.2)
    simpa using this
  have hXcard : Nat.card ((E ⊓ Y).subgroupOf Y) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : E ⊓ Y ≤ Y)).toEquiv]
    exact hE9
  have hB9 : Nat.card (((E ⊓ Y).subgroupOf Y).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 Y))) = 9 := by
    rw [card_map_eq_of_injOn _ (injOn_mk_of_isPGroup Nat.prime_three hX3), hXcard]
  rcases hE _ hMθ _ hB9 with ⟨tb, htbN, htbinv⟩ | ⟨V, hV1, hV2, hBV⟩
  · obtain ⟨t, htY, htinv⟩ := hF G Y (E ⊓ Y) inf_le_right hXexp tb htbN htbinv
    have htb : t * b = b * t := hbc t htY
    refine ⟨t, E ⊓ Y, ⟨htY, htb, ?_, inf_le_left, hE9, ⟨hY.hcE, hcY⟩, fun hb => hbY hb.2,
      htinv⟩⟩
    have hKe : (E ⊓ Y : Subgroup G) ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hbc x hx.2)
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    rw [hdec] at hn
    obtain ⟨i, k, hk, rfl⟩ := exists_zpow_mul_of_mem_zpowers_sup' hKe hn
    have htbi : t * b ^ i * t⁻¹ = b ^ i := by
      have : Commute t b := htb
      rw [(this.zpow_right i).eq]
      group
    have h1 : t * (b ^ i * k) * t⁻¹ = b ^ i * (t * k * t⁻¹) := by
      calc t * (b ^ i * k) * t⁻¹ = (t * b ^ i * t⁻¹) * (t * k * t⁻¹) := by group
        _ = b ^ i * (t * k * t⁻¹) := by rw [htbi]
    rw [h1, htinv k hk]
    exact mul_mem (E.zpow_mem hY.hbE i) (E.inv_mem hk.1)
  · exact absurd (hD G E Y b hEe hY.hCfg.hE27 hY.hEY hbc hY.hbE hdec V hV1 hV2 hBV) hY.hE

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
