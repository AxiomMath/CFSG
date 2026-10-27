module

public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.Quasithin.A38c17

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator_le_commutator_of_le_sup_central {Z : Subgroup G}
    (hZ : Z ≤ Subgroup.center G) {X Y : Subgroup G} (hXY : X ≤ Y ⊔ Z) : ⁅X, X⁆ ≤ ⁅Y, Y⁆ := by
  have : Z.Normal := Subgroup.normal_of_le_center hZ
  refine Subgroup.commutator_le.mpr fun x hx x' hx' => ?_
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hXY hx)
  obtain ⟨y', hy', z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hXY hx')
  have ez := Subgroup.mem_center_iff.mp (hZ hz)
  have ez' := Subgroup.mem_center_iff.mp (hZ hz')
  have hl : ∀ w : G, ⁅y * z, w⁆ = ⁅y, w⁆ := fun w => by
    simp only [commutatorElement_def, mul_inv_rev]
    calc y * z * w * (z⁻¹ * y⁻¹) * w⁻¹ = y * (z * w) * z⁻¹ * y⁻¹ * w⁻¹ := by group
      _ = y * (w * z) * z⁻¹ * y⁻¹ * w⁻¹ := by rw [← ez w]
      _ = y * w * y⁻¹ * w⁻¹ := by group
  have hr : ⁅y, y' * z'⁆ = ⁅y, y'⁆ := by
    simp only [commutatorElement_def, mul_inv_rev]
    calc y * (y' * z') * y⁻¹ * (z'⁻¹ * y'⁻¹) = y * y' * (z' * y⁻¹) * z'⁻¹ * y'⁻¹ := by group
      _ = y * y' * (y⁻¹ * z') * z'⁻¹ * y'⁻¹ := by rw [← ez' y⁻¹]
      _ = y * y' * y⁻¹ * y'⁻¹ := by group
  rw [hl, hr]
  exact Subgroup.commutator_mem_commutator hy hy'

theorem derivedSeriesOf_succ_le_of_le_sup_central {Z : Subgroup G}
    (hZ : Z ≤ Subgroup.center G) {X Y : Subgroup G} (hXY : X ≤ Y ⊔ Z) (n : ℕ) :
    derivedSeriesOf X (n + 1) ≤ derivedSeriesOf Y (n + 1) := by
  induction n with
  | zero => exact commutator_le_commutator_of_le_sup_central hZ hXY
  | succ n ih => exact Subgroup.commutator_mono ih ih

theorem relIndex_sup_eq_of_normal_le {Z H : Subgroup G} [Z.Normal] (hZH : Z ≤ H)
    (B : Subgroup G) : H.relIndex (B ⊔ Z) = H.relIndex B := by
  let f : G →* G ⧸ Z := QuotientGroup.mk' Z
  have hker : f.ker = Z := QuotientGroup.ker_mk' Z
  have key : ∀ C : Subgroup G, H.relIndex C = (H.map f).relIndex (C.map f) := fun C => by
    rw [← Subgroup.relIndex_comap, Subgroup.comap_map_eq, hker, sup_eq_left.mpr hZH]
  rw [key, key, Subgroup.map_sup, (Subgroup.map_eq_bot_iff Z).mpr hker.ge, sup_bot_eq]

theorem sup_central_relIndex_odd {Z 𝒢 A : Subgroup G} (hZ : Z ≤ Subgroup.center G)
    (h1 : 𝒢 ≤ A ⊔ Z) (h2 : A ≤ 𝒢 ⊔ Z) {M : Subgroup G} (hM : M ≤ 𝒢)
    (hodd : Odd (M.relIndex 𝒢)) : Odd ((M ⊔ Z).relIndex A) := by
  have : Z.Normal := Subgroup.normal_of_le_center hZ
  have hsup : A ⊔ Z = 𝒢 ⊔ Z := le_antisymm (sup_le h2 le_sup_right) (sup_le h1 le_sup_right)
  have e : (M ⊔ Z).relIndex A = (M ⊔ Z).relIndex 𝒢 := by
    rw [← relIndex_sup_eq_of_normal_le (le_sup_right : Z ≤ M ⊔ Z) A, hsup,
      relIndex_sup_eq_of_normal_le (le_sup_right : Z ≤ M ⊔ Z) 𝒢]
  have hMK : M ≤ (M ⊔ Z) ⊓ 𝒢 := le_inf le_sup_left hM
  have hmul := Subgroup.relIndex_mul_relIndex M ((M ⊔ Z) ⊓ 𝒢) 𝒢 hMK inf_le_right
  rw [Subgroup.inf_relIndex_right] at hmul
  rw [e]
  exact hodd.of_dvd_nat (Dvd.intro_left _ hmul)

theorem sup_central_isSolvable {Z 𝒢 A : Subgroup G} (hZ : Z ≤ Subgroup.center G)
    (h1 : 𝒢 ≤ A ⊔ Z) {M : Subgroup G} (hM : M ≤ 𝒢)
    (h : Group.IsSolvable ↥((M ⊔ Z).subgroupOf A)) : Group.IsSolvable ↥M := by
  have hP : M ⊔ Z ≤ Z ⊔ A := sup_le (hM.trans (h1.trans (sup_comm A Z).le)) le_sup_left
  have hdec : M ⊔ Z = Z ⊔ ((M ⊔ Z) ⊓ A) :=
    A3.eq_sup_inf_of_le_sup (hZ.trans (Subgroup.center_le_normalizer _)) le_sup_right hP
  have hMS : M ≤ ((M ⊔ Z) ⊓ A) ⊔ Z := le_sup_left.trans (hdec.le.trans (sup_comm _ _).le)
  obtain ⟨n, hn⟩ := (isSolvable_iff_exists_derivedSeriesOf_eq_bot _).mp h
  have hS : derivedSeriesOf ((M ⊔ Z) ⊓ A) n = ⊥ := by
    rw [← Subgroup.subgroupOf_map_subtype, ← map_derivedSeriesOf, hn, Subgroup.map_bot]
  refine (isSolvable_iff_exists_derivedSeriesOf_eq_bot M).mpr ⟨n + 1, le_bot_iff.mp ?_⟩
  calc derivedSeriesOf M (n + 1) ≤ derivedSeriesOf ((M ⊔ Z) ⊓ A) (n + 1) :=
        derivedSeriesOf_succ_le_of_le_sup_central hZ hMS n
    _ ≤ derivedSeriesOf ((M ⊔ Z) ⊓ A) n := derivedSeriesOf_antitone _ (Nat.le_succ n)
    _ = ⊥ := hS

theorem le_perfectCore_of_le_sup_central {Z : Subgroup G} (hZ : Z ≤ Subgroup.center G)
    {M X : Subgroup G} (hX : ⁅X, X⁆ = X) (hXM : X ≤ M ⊔ Z) : X ≤ perfectCore M := by
  have hXM' : X ≤ M :=
    calc X = ⁅X, X⁆ := hX.symm
      _ ≤ ⁅M, M⁆ := commutator_le_commutator_of_le_sup_central hZ hXM
      _ ≤ M := A3.commutator_self_le M
  exact le_perfectCore_of_perfect hXM' hX

end CFSG.Quasithin.A38c17
