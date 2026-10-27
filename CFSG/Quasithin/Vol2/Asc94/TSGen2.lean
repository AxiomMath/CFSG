module

public import CFSG.Quasithin.Vol2.Asc94.TSGen
public import CFSG.CGT.Timmesfeld75.Fusion

public section

namespace CFSG.Quasithin.A94.Gen

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G]

theorem isElemAbelian_map {G' : Type} [Group G'] (f : G →* G') {X : Subgroup G}
    (hX : IsElemAbelian 2 X) : IsElemAbelian 2 (X.map f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a', ha', ha⟩ := a.2
    obtain ⟨b', hb', hb⟩ := b.2
    apply Subtype.ext
    show (a : G') * b = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul]
    exact congrArg f (congrArg Subtype.val (hX.1.is_comm.comm (⟨a', ha'⟩ : X) ⟨b', hb'⟩))
  · obtain ⟨x', hx', rfl⟩ := hx
    rw [← map_pow, hX.2 x' hx', map_one]

theorem isElemAbelian_conjSubgroup (g : G) {X : Subgroup G} (hX : IsElemAbelian 2 X) :
    IsElemAbelian 2 (conjSubgroup g X) :=
  isElemAbelian_map _ hX

theorem card_conjSubgroup (g : G) (X : Subgroup G) :
    Nat.card (conjSubgroup g X) = Nat.card X :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

private lemma mem_sylow_smul_iff' {p : ℕ} {P : Sylow p G} {g y : G} :
    y ∈ ((g • P : Sylow p G) : Subgroup G) ↔ g⁻¹ * y * g ∈ (P : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, rfl⟩
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hs
  · intro hs
    exact ⟨g⁻¹ * y * g, hs, by simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]⟩

theorem weaklyClosedIn_of_sylow [Finite G] (T : Sylow 2 G) {R : Subgroup G}
    (hR : WeaklyClosedIn R (T : Subgroup G)) :
    ∀ U : Subgroup G, IsPGroup 2 U → R ≤ U → WeaklyClosedIn R U := by
  intro U hU hRU
  obtain ⟨P, hUP⟩ := hU.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq G T P
  have hmem : ∀ x : G, x ∈ (P : Subgroup G) ↔ k⁻¹ * x * k ∈ (T : Subgroup G) := by
    intro x
    rw [← hk]
    exact mem_sylow_smul_iff'
  have h1 : conjSubgroup k⁻¹ R = R := by
    refine hR.2 k⁻¹ ?_
    intro y hy
    rw [mem_conjSubgroup, inv_inv] at hy
    have h := (hmem (k * y * k⁻¹)).1 (hUP (hRU hy))
    rwa [show k⁻¹ * (k * y * k⁻¹) * k = y by group] at h
  refine ⟨hRU, fun g hg => ?_⟩
  have h2 : conjSubgroup (k⁻¹ * g) R = R := by
    refine hR.2 _ ?_
    intro y hy
    rw [mem_conjSubgroup] at hy
    have hy' : (k⁻¹ * g)⁻¹ * y * (k⁻¹ * g) ∈ R := hy
    have h3 : g * ((k⁻¹ * g)⁻¹ * y * (k⁻¹ * g)) * g⁻¹ ∈ U := by
      have := mem_conjSubgroup.2 (show g⁻¹ * (g * ((k⁻¹ * g)⁻¹ * y * (k⁻¹ * g)) * g⁻¹) * g ∈ R by
        rw [show g⁻¹ * (g * ((k⁻¹ * g)⁻¹ * y * (k⁻¹ * g)) * g⁻¹) * g =
          (k⁻¹ * g)⁻¹ * y * (k⁻¹ * g) by group]
        exact hy')
      exact hg this
    have h4 := (hmem _).1 (hUP h3)
    rwa [show k⁻¹ * (g * ((k⁻¹ * g)⁻¹ * y * (k⁻¹ * g)) * g⁻¹) * k = y by group] at h4
  calc conjSubgroup g R = conjSubgroup k (conjSubgroup (k⁻¹ * g) R) := by
        rw [conjSubgroup_conjSubgroup]
        congr 1
        group
    _ = conjSubgroup k R := by rw [h2]
    _ = conjSubgroup k (conjSubgroup k⁻¹ R) := by rw [h1]
    _ = R := by rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]

theorem normal_subgroupOf_of_conj {T A : Subgroup G} (h : ∀ t ∈ T, ∀ a ∈ A, t⁻¹ * a * t ∈ A) :
    (A.subgroupOf T).Normal :=
  ⟨fun n hn g => by
    have hn' : (n : G) ∈ A := Subgroup.mem_subgroupOf.1 hn
    exact Subgroup.mem_subgroupOf.2 (by
      have := h (g : G)⁻¹ (T.inv_mem g.2) _ hn'
      simpa using this)⟩

theorem mem_cj {g x : G} {T : Subgroup G} : x ∈ conjSubgroup g T ↔ g⁻¹ * x * g ∈ T :=
  mem_conjSubgroup

theorem mem_normalizer_iff_cj {T : Subgroup G} {g : G} :
    g ∈ Subgroup.normalizer (T : Set G) ↔ conjSubgroup g T = T :=
  mem_normalizer_iff_conjSubgroup_eq

theorem cj_inv_cj (n : G) (X : Subgroup G) : conjSubgroup n⁻¹ (conjSubgroup n X) = X := by
  rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]

theorem cj_inf (n : G) (X Y : Subgroup G) :
    conjSubgroup n (X ⊓ Y) = conjSubgroup n X ⊓ conjSubgroup n Y :=
  Subgroup.map_inf_eq X Y _ (MulAut.conj n).injective

end CFSG.Quasithin.A94.Gen

namespace CFSG.Quasithin.A94

scoped notation "cjS" => CFSG.CGT.Timmesfeld75.conjSubgroup

end CFSG.Quasithin.A94
