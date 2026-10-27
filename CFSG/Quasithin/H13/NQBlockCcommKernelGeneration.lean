module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup
open scoped commutatorElement

theorem central_of_central_modulo_central {E : Type*} [Group E] [Group.IsPerfect E] (k : E)
    (hk : ∀ h : E, ⁅k, h⁆ ∈ center E) : k ∈ center E := by
  have hcomm : ∀ x y : E, ⁅k, x⁆ * y = y * ⁅k, x⁆ := fun x y =>
    ((mem_center_iff.mp (hk x)) y).symm
  let φ : E →* center E :=
    { toFun := fun h => ⟨⁅k, h⁆, hk h⟩
      map_one' := Subtype.ext (by simp [commutatorElement_def])
      map_mul' := fun x y => Subtype.ext (by
        change ⁅k, x * y⁆ = ⁅k, x⁆ * ⁅k, y⁆
        have h1 : ⁅k, x⁆ * ⁅k, y⁆ = ⁅k, x⁆ * (x * ⁅k, y⁆ * x⁻¹) := by
          rw [← hcomm y x, mul_inv_cancel_right]
        rw [h1]
        simp only [commutatorElement_def]
        group) }
  have hker : φ.ker = ⊤ := by
    rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := E)]
    exact Abelianization.commutator_subset_ker φ
  rw [mem_center_iff]
  intro h
  have h1 : φ h = 1 := by
    have : h ∈ φ.ker := by rw [hker]; exact mem_top h
    exact this
  have h2 : ⁅k, h⁆ = 1 := congrArg Subtype.val h1
  rw [commutatorElement_eq_one_iff_mul_comm] at h2
  exact h2.symm

theorem perfect_odd_kernel_generation {H : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    (A : Subgroup H) [A.Normal] (_hA : Odd (Nat.card A)) (_hJ : CFSG.IsQuasisimple (H ⧸ A))
    (hZ : Nat.card (center (H ⧸ A)) = 2) {s : ℕ} [Fact s.Prime] (hs5 : 5 ≤ s)
    (ψ : (H ⧸ A) ⧸ center (H ⧸ A) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod s)) :
    ⁅A, (⊤ : Subgroup H)⁆ = A := by
  classical
  set C := ⁅A, (⊤ : Subgroup H)⁆ with hCdef
  have hCA : C ≤ A := commutator_le_left A ⊤
  have : C.Normal := commutator_normal A ⊤
  set π : H ⧸ C →* H ⧸ A := QuotientGroup.map C A (MonoidHom.id H) hCA with hπ
  have hπmk : ∀ x : H, π (x : H ⧸ C) = (x : H ⧸ A) := fun _ => rfl
  have hπs : Function.Surjective π := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨x, rfl⟩
  have hkerπ : ∀ y : H ⧸ C, π y = 1 → y ∈ center (H ⧸ C) := by
    intro y hy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hπmk, QuotientGroup.eq_one_iff] at hy
    rw [mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    have h1 : ⁅a, g⁆ ∈ C := commutator_mem_commutator hy (mem_top g)
    rw [commutatorElement_def] at h1
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h3 : (g * a)⁻¹ * (a * g) =
        (g * a)⁻¹ * (a * g * a⁻¹ * g⁻¹) * ((g * a)⁻¹)⁻¹ := by group
    rw [h3]
    exact (inferInstance : C.Normal).conj_mem _ h1 _
  set f : H ⧸ C →* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 2 (ZMod s) :=
    ((CFSG.QuasithinUnique.Setup.Family.p2Equiv (ZMod s)).symm.toMonoidHom.comp
      ψ.toMonoidHom).comp ((QuotientGroup.mk' (center (H ⧸ A))).comp π) with hf
  have hfs : Function.Surjective f := by
    refine (CFSG.QuasithinUnique.Setup.Family.p2Equiv (ZMod s)).symm.surjective.comp
      (ψ.surjective.comp ((QuotientGroup.mk'_surjective _).comp hπs))
  have hmemker : ∀ y : H ⧸ C, y ∈ f.ker ↔ π y ∈ center (H ⧸ A) := by
    intro y
    rw [MonoidHom.mem_ker, hf]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]
    rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hkercen : f.ker ≤ center (H ⧸ C) := by
    intro k hk
    rw [hmemker] at hk
    refine central_of_central_modulo_central k fun h => hkerπ _ ?_
    rw [map_commutatorElement]
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact ((mem_center_iff.mp hk) (π h)).symm
  have hbound := CFSG.QuasithinUnique.Setup.Family.p2_central_kernel_bound hs5 f hfs hkercen
  set Abar := A.map (QuotientGroup.mk' C) with hAbar
  have hAbarle : Abar ≤ f.ker := by
    rintro _ ⟨a, ha, rfl⟩
    rw [hmemker, QuotientGroup.mk'_apply, hπmk, (QuotientGroup.eq_one_iff _).mpr ha]
    exact one_mem _
  have hAbarne : Abar ≠ f.ker := by
    obtain ⟨z, hz⟩ : ∃ z ∈ center (H ⧸ A), z ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have h1 : center (H ⧸ A) = ⊥ := eq_bot_iff.mpr fun z hz => (mem_bot).mpr (hcon z hz)
      rw [h1, card_bot] at hZ
      exact absurd hZ (by norm_num)
    obtain ⟨y, rfl⟩ := hπs z
    intro heq
    have hy : y ∈ f.ker := (hmemker y).mpr hz.1
    rw [← heq] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    apply hz.2
    rw [QuotientGroup.mk'_apply, hπmk]
    exact (QuotientGroup.eq_one_iff _).mpr ha
  have hdvd : Nat.card Abar ∣ Nat.card f.ker := card_dvd_of_le hAbarle
  have hlt : Nat.card Abar ≠ Nat.card f.ker := fun h =>
    hAbarne (eq_of_le_of_card_ge hAbarle h.symm.le)
  have hAbar1 : Nat.card Abar = 1 := by
    obtain ⟨m, hm⟩ := hdvd
    have hpos : 0 < Nat.card Abar := Nat.card_pos
    have hkpos : 0 < Nat.card f.ker := Nat.card_pos
    have hm1 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hm
      omega
    have hm2 : m ≠ 1 := by
      rintro rfl
      rw [mul_one] at hm
      exact hlt hm.symm
    have h2m : 2 ≤ m := by omega
    have : Nat.card Abar * 2 ≤ 2 := (Nat.mul_le_mul_left _ h2m).trans (hm ▸ hbound)
    omega
  have hAbarbot : Abar = ⊥ := card_eq_one.mp hAbar1
  refine le_antisymm hCA fun a ha => ?_
  have h1 : (QuotientGroup.mk' C a) ∈ Abar := ⟨a, ha, rfl⟩
  rw [hAbarbot, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

end CFSG.Quasithin.H13.NQBlock
