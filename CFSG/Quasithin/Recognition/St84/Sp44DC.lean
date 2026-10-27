module

public import CFSG.Quasithin.Recognition.St84.Sp44Borel

public section

namespace CFSG.Quasithin.F112R.St84.Sp44

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.QuasithinUnique.Setup.X7b (radA1 radA2 uElt_inj uElt_mul_self uElt_zero_eq_one
  card_radicals radA1_inf_radA2 mem_antiUnipotentCenter_iff_central radA1_le_antiUnipotent
  radA2_le_antiUnipotent antiUnipotentCenter_le_radA1 antiUnipotentCenter_le_radA2
  mul_self_of_mem_radA1 mul_self_of_mem_radA2 elementary_le_radA1_or_radA2)
open CFSG.RankThree.PartOne.KCRootAxis
open CFSG.QuasithinUnique.Fin257.Sp4
open Matrix
open scoped Pointwise

variable {F : Type} [Field F] [Finite F] [CharP F 2]

abbrev T0B (F : Type) [Field F] [CharP F 2] : Subgroup ↥(B0 F) :=
  (antiUnipotent F).subgroupOf (B0 F)

abbrev A1B (F : Type) [Field F] [CharP F 2] : Subgroup ↥(B0 F) :=
  (radA1 F).subgroupOf (B0 F)

abbrev A2B (F : Type) [Field F] [CharP F 2] : Subgroup ↥(B0 F) :=
  (radA2 F).subgroupOf (B0 F)

abbrev Z0B (F : Type) [Field F] [CharP F 2] : Subgroup ↥(B0 F) :=
  (antiUnipotentCenter F).subgroupOf (B0 F)

abbrev U1B (F : Type) [Field F] [CharP F 2] : Subgroup ↥(B0 F) :=
  (rootU₁ F).subgroupOf (B0 F)

abbrev U2B (F : Type) [Field F] [CharP F 2] : Subgroup ↥(B0 F) :=
  (rootU₂ F).subgroupOf (B0 F)

abbrev HB (F : Type) [Field F] [CharP F 2] : Subgroup ↥(B0 F) :=
  (dTor F).subgroupOf (B0 F)

abbrev XaB (F : Type) [Field F] [CharP F 2] : Subgroup ↥(B0 F) :=
  (rootXa F).subgroupOf (B0 F)

abbrev XbB (F : Type) [Field F] [CharP F 2] : Subgroup ↥(B0 F) :=
  (rootXb F).subgroupOf (B0 F)

theorem A1_le_B0 : radA1 F ≤ B0 F :=
  (radA1_le_antiUnipotent (K := F)).trans Subgroup.le_normalizer

theorem A2_le_B0 : radA2 F ≤ B0 F :=
  (radA2_le_antiUnipotent (K := F)).trans Subgroup.le_normalizer

theorem Z0_le_B0 : antiUnipotentCenter F ≤ B0 F :=
  antiUnipotentCenter_le.trans Subgroup.le_normalizer

theorem U1_le_B0 : rootU₁ F ≤ B0 F :=
  rootU₁_le_antiUnipotentCenter.trans Z0_le_B0

theorem U2_le_B0 : rootU₂ F ≤ B0 F :=
  rootU₂_le_antiUnipotentCenter.trans Z0_le_B0

theorem Xa_le_B0 : rootXa F ≤ B0 F :=
  rootXa_le_antiUnipotent.trans Subgroup.le_normalizer

theorem Xb_le_B0 : rootXb F ≤ B0 F :=
  rootXb_le_antiUnipotent.trans Subgroup.le_normalizer

theorem A1B_le_T0B : A1B F ≤ T0B F :=
  Subgroup.subgroupOf_mono _ (radA1_le_antiUnipotent (K := F))

theorem A2B_le_T0B : A2B F ≤ T0B F :=
  Subgroup.subgroupOf_mono _ (radA2_le_antiUnipotent (K := F))

theorem Z0B_le_A1B : Z0B F ≤ A1B F :=
  Subgroup.subgroupOf_mono _ (antiUnipotentCenter_le_radA1 (K := F))

theorem Z0B_le_A2B : Z0B F ≤ A2B F :=
  Subgroup.subgroupOf_mono _ (antiUnipotentCenter_le_radA2 (K := F))

theorem U1B_le_Z0B : U1B F ≤ Z0B F :=
  Subgroup.subgroupOf_mono _ rootU₁_le_antiUnipotentCenter

theorem U2B_le_Z0B : U2B F ≤ Z0B F :=
  Subgroup.subgroupOf_mono _ rootU₂_le_antiUnipotentCenter

theorem XaB_le_T0B : XaB F ≤ T0B F :=
  Subgroup.subgroupOf_mono _ rootXa_le_antiUnipotent

theorem XbB_le_T0B : XbB F ≤ T0B F :=
  Subgroup.subgroupOf_mono _ rootXb_le_antiUnipotent


theorem U1B_ne_U2B : U1B F ≠ U2B F := by
  intro h
  let x : ↥(B0 F) := ⟨uElt 0 1 0 0, U1_le_B0 ⟨1, rfl⟩⟩
  have hx1 : x ∈ U1B F := ⟨1, rfl⟩
  have hx2 : x ∈ U2B F := by rw [← h]; exact hx1
  obtain ⟨c, hc⟩ := hx2
  exact one_ne_zero (uElt_inj hc).2.1

theorem map_U1B (hF : Nat.card F = 2 ^ 2) (σ : MulAut ↥(B0 F))
    (hZ : (Z0B F).map σ.toMonoidHom = Z0B F)
    (hU : ∃ b : ↥(B0 F), b ∈ U1B F ∧ σ b ∉ U2B F) :
    (U1B F).map σ.toMonoidHom = U1B F := by
  classical
  let W : Subgroup (antiSp F) := ((U1B F).map σ.toMonoidHom).map (B0 F).subtype
  have hWZ : W ≤ antiUnipotentCenter F := by
    rintro y ⟨b, hb, rfl⟩
    have hbZ : b ∈ Z0B F := by
      have hle : (U1B F).map σ.toMonoidHom ≤ (Z0B F).map σ.toMonoidHom :=
        Subgroup.map_mono U1B_le_Z0B
      rw [hZ] at hle
      exact hle hb
    exact hbZ
  have hWc : Nat.card W = 4 := by
    rw [show Nat.card W = Nat.card ((U1B F).map σ.toMonoidHom) from
      Subgroup.card_map_of_injective (B0 F).subtype_injective,
      Subgroup.card_map_of_injective σ.injective, card_rootU₁_subgroupOf hF]
  have hact : ∀ h ∈ dTor F, ∀ y : antiSp F, y ∈ W → h * y * h⁻¹ ∈ W := by
    intro h hh y hy
    let hB : ↥(B0 F) := ⟨h, dTor_le hh⟩
    obtain ⟨w, hw, rfl⟩ := hy
    have hN : ((U1B F).map σ.toMonoidHom).Normal :=
      rootU₁_normal.map σ.toMonoidHom σ.surjective
    have hconj : hB * w * hB⁻¹ ∈ (U1B F).map σ.toMonoidHom := hN.conj_mem w hw hB
    exact ⟨hB * w * hB⁻¹, hconj, by simp [hB]⟩
  have hWn : dTor F ≤ Subgroup.normalizer (W : Set (antiSp F)) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hact h hh y
    · intro hy
      have hh' : h⁻¹ ∈ dTor F := (dTor F).inv_mem hh
      have hmem := hact h⁻¹ hh' (h * y * h⁻¹) hy
      have heq : h⁻¹ * (h * y * h⁻¹) * (h⁻¹)⁻¹ = y := by group
      rwa [heq] at hmem
  rcases eq_rootU_of_dTor_normal hF hWZ hWc hWn with hW | hW
  · apply Subgroup.map_injective (B0 F).subtype_injective
    calc ((U1B F).map σ.toMonoidHom).map (B0 F).subtype = W := rfl
      _ = rootU₁ F := hW
      _ = (U1B F).map (B0 F).subtype := (Subgroup.map_subgroupOf_eq_of_le U1_le_B0).symm
  · exfalso
    obtain ⟨b, hbU1, hbnotU2⟩ := hU
    have hbmap : σ b ∈ (U1B F).map σ.toMonoidHom := ⟨b, hbU1, rfl⟩
    have hmemW : (σ b : antiSp F) ∈ W := ⟨σ b, hbmap, rfl⟩
    rw [hW] at hmemW
    exact hbnotU2 hmemW

theorem map_U2B (hF : Nat.card F = 2 ^ 2) (σ : MulAut ↥(B0 F))
    (hZ : (Z0B F).map σ.toMonoidHom = Z0B F)
    (hU1 : (U1B F).map σ.toMonoidHom = U1B F) :
    (U2B F).map σ.toMonoidHom = U2B F := by
  classical
  let W : Subgroup (antiSp F) := ((U2B F).map σ.toMonoidHom).map (B0 F).subtype
  have hWZ : W ≤ antiUnipotentCenter F := by
    rintro y ⟨b, hb, rfl⟩
    have hbZ : b ∈ Z0B F := by
      have hle : (U2B F).map σ.toMonoidHom ≤ (Z0B F).map σ.toMonoidHom :=
        Subgroup.map_mono U2B_le_Z0B
      rw [hZ] at hle
      exact hle hb
    exact hbZ
  have hWc : Nat.card W = 4 := by
    rw [show Nat.card W = Nat.card ((U2B F).map σ.toMonoidHom) from
      Subgroup.card_map_of_injective (B0 F).subtype_injective,
      Subgroup.card_map_of_injective σ.injective, card_rootU₂_subgroupOf hF]
  have hact : ∀ h ∈ dTor F, ∀ y : antiSp F, y ∈ W → h * y * h⁻¹ ∈ W := by
    intro h hh y hy
    let hB : ↥(B0 F) := ⟨h, dTor_le hh⟩
    obtain ⟨w, hw, rfl⟩ := hy
    have hN : ((U2B F).map σ.toMonoidHom).Normal :=
      rootU₂_normal.map σ.toMonoidHom σ.surjective
    have hconj : hB * w * hB⁻¹ ∈ (U2B F).map σ.toMonoidHom := hN.conj_mem w hw hB
    exact ⟨hB * w * hB⁻¹, hconj, by simp [hB]⟩
  have hWn : dTor F ≤ Subgroup.normalizer (W : Set (antiSp F)) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hact h hh y
    · intro hy
      have hh' : h⁻¹ ∈ dTor F := (dTor F).inv_mem hh
      have hmem := hact h⁻¹ hh' (h * y * h⁻¹) hy
      have heq : h⁻¹ * (h * y * h⁻¹) * (h⁻¹)⁻¹ = y := by group
      rwa [heq] at hmem
  rcases eq_rootU_of_dTor_normal hF hWZ hWc hWn with hW | hW
  · exfalso
    have hsub : (U2B F).map σ.toMonoidHom = U1B F := by
      apply Subgroup.map_injective (B0 F).subtype_injective
      calc ((U2B F).map σ.toMonoidHom).map (B0 F).subtype = W := rfl
        _ = rootU₁ F := hW
        _ = (U1B F).map (B0 F).subtype := (Subgroup.map_subgroupOf_eq_of_le U1_le_B0).symm
    have hEq : (U1B F).map σ.toMonoidHom = (U2B F).map σ.toMonoidHom :=
      (hsub.trans hU1.symm).symm
    exact U1B_ne_U2B (Subgroup.map_injective σ.injective hEq)
  · apply Subgroup.map_injective (B0 F).subtype_injective
    calc ((U2B F).map σ.toMonoidHom).map (B0 F).subtype = W := rfl
      _ = rootU₂ F := hW
      _ = (U2B F).map (B0 F).subtype := (Subgroup.map_subgroupOf_eq_of_le U2_le_B0).symm

theorem subgroup_map_eq_pointwise_smul {Y : Type} [Group Y] (a : MulAut Y) (H : Subgroup Y) :
    H.map a.toMonoidHom = a • H := by
  rw [Subgroup.pointwise_smul_def]
  congr 1

theorem map_conj_inv_comp {Y : Type} [Group Y] (σ : MulAut Y) {g : Y} {H : Subgroup Y}
    (h : H.map σ.toMonoidHom = H.map (MulAut.conj g).toMonoidHom) :
    H.map (((MulAut.conj g)⁻¹ * σ).toMonoidHom) = H := by
  change H.map (((MulAut.conj g)⁻¹).toMonoidHom.comp σ.toMonoidHom) = H
  rw [← Subgroup.map_map, h, Subgroup.map_map]
  have hcomp : ((MulAut.conj g)⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      (1 : MulAut Y).toMonoidHom := by
    ext y
    change (MulAut.conj g)⁻¹ ((MulAut.conj g) y) = y
    exact MulAut.inv_apply_self Y (MulAut.conj g) y
  rw [hcomp, MulAut.one_def]
  exact Subgroup.map_id H

theorem exists_conj_torusB (hF : Nat.card F = 2 ^ 2) (σ : MulAut ↥(B0 F)) :
    ∃ g₁ : ↥(B0 F), (HB F).map σ.toMonoidHom =
      (HB F).map (MulAut.conj g₁).toMonoidHom := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hHp : IsPGroup 3 ↥(HB F) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [card_dTor_subgroupOf hF]
    norm_num
  have hHidx : ¬ 3 ∣ (HB F).index := by
    have hcard := Subgroup.card_mul_index (HB F)
    rw [card_dTor_subgroupOf hF, card_B0 hF] at hcard
    have hidx : (HB F).index = 2 ^ 8 := by
      norm_num at hcard ⊢
      omega
    rw [hidx]
    norm_num
  let SH : Sylow 3 ↥(B0 F) := hHp.toSylow hHidx
  have hSH : (SH : Subgroup ↥(B0 F)) = HB F := rfl
  haveI : Finite (Sylow 3 ↥(B0 F)) := Sylow.finite_of_finiteIndex SH
  obtain ⟨g₁, hg₁⟩ := MulAction.exists_smul_eq ↥(B0 F) SH (σ • SH)
  refine ⟨g₁, ?_⟩
  have h := congrArg (fun S : Sylow 3 ↥(B0 F) => (S : Subgroup ↥(B0 F))) hg₁
  rw [Sylow.coe_subgroup_smul, Sylow.pointwise_smul_def, hSH] at h
  have hmap : (HB F).map (MulAut.conj g₁).toMonoidHom = (HB F).map σ.toMonoidHom := by
    rw [subgroup_map_eq_pointwise_smul (Y := ↥(B0 F)) (MulAut.conj g₁),
      subgroup_map_eq_pointwise_smul (Y := ↥(B0 F)) σ]
    exact h
  exact hmap.symm

theorem frobAutB0_pow_apply (k : ℕ) (g : ↥(B0 F)) :
    (((frobAutB0 (F := F)) ^ k) g : antiSp F) = (frobAut F ^ k) (g : antiSp F) := by
  induction k generalizing g with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, MulAut.mul_apply, pow_succ, MulAut.mul_apply]
      calc ((((frobAutB0 (F := F)) ^ k) (frobAutB0 g) : ↥(B0 F)) : antiSp F)
          = (frobAut F ^ k) ((frobAutB0 g : ↥(B0 F)) : antiSp F) := ih _
        _ = (frobAut F ^ k) (frobAut F (g : antiSp F)) := by rw [frobAutB0_apply]
        _ = (frobAut F ^ k * frobAut F) (g : antiSp F) := rfl


theorem units_eq_one_or_eq_or_sq (hF : Nat.card F = 2 ^ 2) {ω : Fˣ} (hω : ω ≠ 1)
    (s : Fˣ) : s = 1 ∨ s = ω ∨ s = ω ^ 2 := by
  classical
  haveI : Fintype Fˣ := Fintype.ofFinite Fˣ
  have hcu : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]; norm_num
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h
    apply hω
    apply Units.ext
    have h' : ((ω : F) ^ 2) = 1 := by simpa using congrArg (fun u : Fˣ => (u : F)) h
    rcases sq_eq_one_iff.mp h' with h1 | h1
    · exact h1
    · rwa [CharTwo.neg_eq] at h1
  have hωω2 : ω ≠ ω ^ 2 := by
    intro h
    have h1 : (1 : Fˣ) = ω := by
      calc (1 : Fˣ) = ω * ω⁻¹ := by group
        _ = ω ^ 2 * ω⁻¹ := by rw [← h]
        _ = ω := by group
    exact hω h1.symm
  have hcard : ({1, ω, ω ^ 2} : Finset Fˣ).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hω.symm, hω2.symm]),
      Finset.card_insert_of_notMem (by simp [hωω2]), Finset.card_singleton]
  have huniv : ({1, ω, ω ^ 2} : Finset Fˣ) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hcard, ← Nat.card_eq_fintype_card, hcu]
  have hs : s ∈ ({1, ω, ω ^ 2} : Finset Fˣ) := by
    rw [huniv]
    exact Finset.mem_univ s
  simpa using hs

theorem units_ne_sq (hF : Nat.card F = 2 ^ 2) {ω : Fˣ} (hω : ω ≠ 1) : ω ≠ ω ^ 2 := by
  intro h
  have h1 : (1 : Fˣ) = ω := by
    calc (1 : Fˣ) = ω * ω⁻¹ := by group
      _ = ω ^ 2 * ω⁻¹ := by rw [← h]
      _ = ω := by group
  exact hω h1.symm

theorem units_pow_one_ne_pow_two (hF : Nat.card F = 2 ^ 2) {ω : Fˣ} (hω : ω ≠ 1) :
    ω ^ 1 ≠ ω ^ 2 := by
  simpa using units_ne_sq (F := F) hF hω

theorem units_sq_eq_inv (hF : Nat.card F = 2 ^ 2) (u : Fˣ) : u ^ 2 = u⁻¹ := by
  have hcu : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]; norm_num
  have h3 : u ^ 3 = 1 := by
    simpa [hcu] using pow_card_eq_one' (x := u)
  have hm : u * u ^ 2 = 1 := by
    rw [← pow_succ', show 1 + 2 = 3 by norm_num, h3]
  exact eq_inv_of_mul_eq_one_right hm


theorem T0B_normal : (T0B F).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.le_normalizer)).mpr le_rfl

theorem map_A1B (σ : MulAut ↥(B0 F))
    (hA : ∀ b : ↥(B0 F), (b : antiSp F) ∈ radA1 F ↔ (σ b : antiSp F) ∈ radA1 F) :
    (A1B F).map σ.toMonoidHom = A1B F := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact (hA x).mp hx
  · intro x hx
    refine ⟨σ⁻¹ x, ?_, by simp⟩
    have hx' : (x : antiSp F) ∈ radA1 F := hx
    exact (hA (σ⁻¹ x)).mpr (by simpa using hx')

theorem map_Z0B (σ : MulAut ↥(B0 F))
    (hA1 : (A1B F).map σ.toMonoidHom = A1B F)
    (hA2 : (A2B F).map σ.toMonoidHom = A2B F) :
    (Z0B F).map σ.toMonoidHom = Z0B F := by
  have hcenter : Z0B F = A1B F ⊓ A2B F := by
    ext x
    rw [Subgroup.mem_inf]
    constructor
    · intro hx
      have hx' : (x : antiSp F) ∈ radA1 F ⊓ radA2 F := by
        rw [radA1_inf_radA2]
        exact hx
      exact ⟨hx'.1, hx'.2⟩
    · rintro ⟨h1, h2⟩
      have hx' : (x : antiSp F) ∈ antiUnipotentCenter F := by
        rw [← radA1_inf_radA2]
        exact ⟨h1, h2⟩
      exact hx'
  rw [hcenter, Subgroup.map_inf _ _ σ.toMonoidHom σ.injective, hA1, hA2]

theorem map_conj_inv_comp_of_map {H : Subgroup ↥(B0 F)} [H.Normal]
    (σ : MulAut ↥(B0 F)) (g : ↥(B0 F)) (h : H.map σ.toMonoidHom = H) :
    H.map (((MulAut.conj g)⁻¹ * σ).toMonoidHom) = H := by
  refine map_conj_inv_comp σ ?_
  rw [h]
  exact (Subgroup.Normal.map_conj_eq (H := H) g).symm

theorem frobAutB0_sq (hF : Nat.card F = 2 ^ 2) :
    (frobAutB0 (F := F)) ^ 2 = 1 := by
  apply MulEquiv.ext
  intro b
  apply Subtype.ext
  rw [frobAutB0_pow_apply, frobAut_sq hF]
  simp

theorem map_T0B (hF : Nat.card F = 2 ^ 2) (σ : MulAut ↥(B0 F)) :
    (T0B F).map σ.toMonoidHom = T0B F := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTnorm : (T0B F).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.le_normalizer)).mpr le_rfl
  have hTp : IsPGroup 2 ↥(T0B F) :=
    (isSylowTwoOf_antiUnipotent_B0 hF).2.1.of_equiv
      (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := antiUnipotent F))).symm
  have hTpc : T0B F = CFSG.pCore 2 ↥(B0 F) := by
    refine le_antisymm ?_ ?_
    · exact le_sSup ⟨hTnorm, hTp⟩
    · obtain ⟨S, hS⟩ :=
        CFSG.Quasithin.F7.isSylowTwoOf_exists_sylow (isSylowTwoOf_antiUnipotent_B0 hF)
      refine sSup_le ?_
      rintro K ⟨hKn, hKp⟩
      letI : K.Normal := hKn
      have hle := IsPGroup.le_sylow_of_normal (p := 2) hKp S
      rwa [hS] at hle
  rw [hTpc, CFSG.pCore_map_iso]

theorem map_A2B (hF : Nat.card F = 2 ^ 2) (σ : MulAut ↥(B0 F))
    (hA1 : (A1B F).map σ.toMonoidHom = A1B F)
    (hT : (T0B F).map σ.toMonoidHom = T0B F) :
    (A2B F).map σ.toMonoidHom = A2B F := by
  classical
  have hA1ne : A1B F ≠ A2B F := by
    intro h
    apply radA1_ne_radA2 (K := F)
    have hmap := congrArg (fun H : Subgroup ↥(B0 F) => H.map (B0 F).subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le A1_le_B0,
      Subgroup.map_subgroupOf_eq_of_le A2_le_B0] at hmap
  have hcardA2 : Nat.card ((A2B F).map σ.toMonoidHom) = 2 ^ 6 := by
    rw [Subgroup.card_map_of_injective σ.injective, card_radA2_subgroupOf hF]
  let E : Subgroup (antiSp F) := ((A2B F).map σ.toMonoidHom).map (B0 F).subtype
  have hEU : E ≤ antiUnipotent F := by
    rintro y ⟨b, hb, rfl⟩
    have hbT : b ∈ T0B F := by
      rw [← hT]
      exact Subgroup.map_mono A2B_le_T0B hb
    exact hbT
  have hE2 : ∀ y ∈ E, y * y = 1 := by
    rintro y ⟨b, hb, rfl⟩
    obtain ⟨a, ha, rfl⟩ := hb
    have ha2 : a * a = 1 := by
      apply Subtype.ext
      simpa using mul_self_of_mem_radA2 (K := F) ha
    have h : σ a * σ a = 1 := by simpa using congrArg σ ha2
    simpa using congrArg (fun z : ↥(B0 F) => (z : antiSp F)) h
  rcases elementary_le_radA1_or_radA2 hEU hE2 with hE1 | hE2'
  · have hle1 : (A2B F).map σ.toMonoidHom ≤ A1B F := by
      have h : E ≤ (A1B F).map (B0 F).subtype := by
        rwa [Subgroup.map_subgroupOf_eq_of_le A1_le_B0]
      exact Subgroup.map_subtype_le_map_subtype.mp h
    have heq1 : (A2B F).map σ.toMonoidHom = A1B F :=
      Subgroup.eq_of_le_of_card_ge hle1 (by
        rw [card_radA1_subgroupOf hF, hcardA2])
    have hmap : (A2B F).map σ.toMonoidHom = (A1B F).map σ.toMonoidHom := by
      rw [heq1, hA1]
    exact absurd (Subgroup.map_injective σ.injective hmap.symm) hA1ne
  · have hle2 : (A2B F).map σ.toMonoidHom ≤ A2B F := by
      have h : E ≤ (A2B F).map (B0 F).subtype := by
        rwa [Subgroup.map_subgroupOf_eq_of_le A2_le_B0]
      exact Subgroup.map_subtype_le_map_subtype.mp h
    exact Subgroup.eq_of_le_of_card_ge hle2 (by
      rw [card_radA2_subgroupOf hF, hcardA2])



theorem exists_frobAutB0_pow_fixes_torus (hF : Nat.card F = 2 ^ 2) (σ₁ : MulAut ↥(B0 F)) (ε : ℕ)
    (hε : ε = 1 ∨ ε = 2)
    (hact : ∀ s t : Fˣ, σ₁ ⟨dSp s t, dTor_le (dSp_mem_dTor s t)⟩ =
      ⟨dSp (s ^ ε) (t ^ ε), dTor_le (dSp_mem_dTor (s ^ ε) (t ^ ε))⟩) :
    ∃ k : ℕ, (k = 0 ∨ k = 1) ∧ ∀ h ∈ HB F,
      ((frobAutB0 (F := F) ^ k) * σ₁) h = h := by
  rcases hε with rfl | rfl
  · refine ⟨0, Or.inl rfl, ?_⟩
    intro h hh
    obtain ⟨s, t, hst⟩ := mem_dTor.mp (Subgroup.mem_subgroupOf.mp hh)
    have hh' : h = ⟨dSp s t, dTor_le (dSp_mem_dTor s t)⟩ := Subtype.ext hst
    rw [hh']
    have h0 : ((frobAutB0 (F := F) ^ 0) * σ₁) ⟨dSp s t, dTor_le (dSp_mem_dTor s t)⟩ =
        σ₁ ⟨dSp s t, dTor_le (dSp_mem_dTor s t)⟩ := by simp
    rw [h0, hact s t]
    simp
  · refine ⟨1, Or.inr rfl, ?_⟩
    intro h hh
    obtain ⟨s, t, hst⟩ := mem_dTor.mp (Subgroup.mem_subgroupOf.mp hh)
    let h' : ↥(B0 F) := ⟨dSp s t, dTor_le (dSp_mem_dTor s t)⟩
    have hhh : h = h' := Subtype.ext hst
    rw [hhh]
    have h1 : ((frobAutB0 (F := F) ^ 1) * σ₁) h' = frobAutB0 (F := F) (σ₁ h') := by simp
    rw [h1]
    apply Subtype.ext
    rw [frobAutB0_apply]
    change (frobAut F) ((σ₁ h' : ↥(B0 F)) : antiSp F) = (h' : antiSp F)
    have hh2 : σ₁ h' =
        (⟨dSp (s ^ 2) (t ^ 2), dTor_le (dSp_mem_dTor (s ^ 2) (t ^ 2))⟩ : ↥(B0 F)) := hact s t
    rw [hh2]
    change (frobAut F) (dSp (s ^ 2) (t ^ 2)) = (dSp s t : antiSp F)
    rw [frobAut_dSp hF (s ^ 2) (t ^ 2), units_sq_eq_inv hF s, units_sq_eq_inv hF t,
      inv_inv, inv_inv]

theorem maps_to_XaB (hF : Nat.card F = 2 ^ 2) (σ : MulAut ↥(B0 F))
    (hT : (T0B F).map σ.toMonoidHom = T0B F)
    (hfix : ∀ h ∈ HB F, σ h = h) :
    (XaB F).map σ.toMonoidHom ≤ XaB F := by
  classical
  haveI : Fintype Fˣ := Fintype.ofFinite Fˣ
  have hcu : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]; norm_num
  have h1lt : 1 < Fintype.card Fˣ := by
    rw [← Nat.card_eq_fintype_card, hcu]
    norm_num
  obtain ⟨s0, hs0⟩ := Fintype.exists_ne_of_one_lt_card h1lt (1 : Fˣ)
  rintro _ ⟨x, hx, rfl⟩
  have hxT : x ∈ T0B F := XaB_le_T0B hx
  have hxXa : (x : antiSp F) ∈ rootXa F := hx
  let h0B : ↥(B0 F) := ⟨dSp s0 s0, dTor_le (dSp_mem_dTor s0 s0)⟩
  have h0H : h0B ∈ HB F := Subgroup.mem_subgroupOf.mpr (dSp_mem_dTor s0 s0)
  have hfix0 : σ h0B = h0B := hfix h0B h0H
  have hcommB : h0B * x = x * h0B := Subtype.ext (rootXa_comm_dSp s0 hxXa)
  have hcommσB : h0B * σ x = σ x * h0B := by
    have := congrArg σ hcommB
    simpa [map_mul, hfix0] using this
  have hσT : σ x ∈ T0B F := by
    rw [← hT]
    exact ⟨x, hxT, rfl⟩
  have hσU : ((σ x : ↥(B0 F)) : antiSp F) ∈ antiUnipotent F := hσT
  have hcommσ : dSp s0 s0 * ((σ x : ↥(B0 F)) : antiSp F) =
      ((σ x : ↥(B0 F)) : antiSp F) * dSp s0 s0 := by
    simpa [h0B] using congrArg (fun z : ↥(B0 F) => (z : antiSp F)) hcommσB
  exact centralizer_dSp_diag hF hs0 hσU hcommσ

theorem maps_to_XbB (hF : Nat.card F = 2 ^ 2) (σ : MulAut ↥(B0 F))
    (hT : (T0B F).map σ.toMonoidHom = T0B F)
    (hfix : ∀ h ∈ HB F, σ h = h) :
    (XbB F).map σ.toMonoidHom ≤ XbB F := by
  classical
  haveI : Fintype Fˣ := Fintype.ofFinite Fˣ
  have hcu : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]; norm_num
  have h1lt : 1 < Fintype.card Fˣ := by
    rw [← Nat.card_eq_fintype_card, hcu]
    norm_num
  obtain ⟨s0, hs0⟩ := Fintype.exists_ne_of_one_lt_card h1lt (1 : Fˣ)
  rintro _ ⟨x, hx, rfl⟩
  have hxT : x ∈ T0B F := XbB_le_T0B hx
  have hxXb : (x : antiSp F) ∈ rootXb F := hx
  let h0B : ↥(B0 F) := ⟨dSp s0 1, dTor_le (dSp_mem_dTor s0 1)⟩
  have h0H : h0B ∈ HB F := Subgroup.mem_subgroupOf.mpr (dSp_mem_dTor s0 1)
  have hfix0 : σ h0B = h0B := hfix h0B h0H
  have hcommB : h0B * x = x * h0B := Subtype.ext (rootXb_comm_dSp_left s0 hxXb)
  have hcommσB : h0B * σ x = σ x * h0B := by
    have := congrArg σ hcommB
    simpa [map_mul, hfix0] using this
  have hσT : σ x ∈ T0B F := by
    rw [← hT]
    exact ⟨x, hxT, rfl⟩
  have hσU : ((σ x : ↥(B0 F)) : antiSp F) ∈ antiUnipotent F := hσT
  have hcommσ : dSp s0 1 * ((σ x : ↥(B0 F)) : antiSp F) =
      ((σ x : ↥(B0 F)) : antiSp F) * dSp s0 1 := by
    simpa [h0B] using congrArg (fun z : ↥(B0 F) => (z : antiSp F)) hcommσB
  exact centralizer_dSp_left hF hs0 hσU hcommσ

theorem map_XaB (hF : Nat.card F = 2 ^ 2) (σ : MulAut ↥(B0 F))
    (hT : (T0B F).map σ.toMonoidHom = T0B F)
    (hfix : ∀ h ∈ HB F, σ h = h) :
    (XaB F).map σ.toMonoidHom = XaB F := by
  have hfwd := maps_to_XaB hF σ hT hfix
  have hTinv : (T0B F).map σ⁻¹.toMonoidHom = T0B F := by
    have h := congrArg (fun K : Subgroup ↥(B0 F) => K.map σ⁻¹.toMonoidHom) hT
    rw [Subgroup.map_map] at h
    have hcomp : (MulEquiv.toMonoidHom σ⁻¹).comp (MulEquiv.toMonoidHom σ) =
        MonoidHom.id ↥(B0 F) := by
      ext y
      simp
    rw [hcomp, Subgroup.map_id] at h
    exact h.symm
  have hfixinv : ∀ h ∈ HB F, σ⁻¹ h = h := by
    intro h hh
    have hh' := hfix h hh
    calc σ⁻¹ h = σ⁻¹ (σ h) := by rw [hh']
      _ = h := by simp
  have hbwd := maps_to_XaB hF σ⁻¹ hTinv hfixinv
  refine le_antisymm hfwd ?_
  intro x hx
  have hx' : σ⁻¹ x ∈ XaB F := hbwd ⟨x, hx, rfl⟩
  exact ⟨σ⁻¹ x, hx', by simp⟩

theorem map_XbB (hF : Nat.card F = 2 ^ 2) (σ : MulAut ↥(B0 F))
    (hT : (T0B F).map σ.toMonoidHom = T0B F)
    (hfix : ∀ h ∈ HB F, σ h = h) :
    (XbB F).map σ.toMonoidHom = XbB F := by
  have hfwd := maps_to_XbB hF σ hT hfix
  have hTinv : (T0B F).map σ⁻¹.toMonoidHom = T0B F := by
    have h := congrArg (fun K : Subgroup ↥(B0 F) => K.map σ⁻¹.toMonoidHom) hT
    rw [Subgroup.map_map] at h
    have hcomp : (MulEquiv.toMonoidHom σ⁻¹).comp (MulEquiv.toMonoidHom σ) =
        MonoidHom.id ↥(B0 F) := by
      ext y
      simp
    rw [hcomp, Subgroup.map_id] at h
    exact h.symm
  have hfixinv : ∀ h ∈ HB F, σ⁻¹ h = h := by
    intro h hh
    have hh' := hfix h hh
    calc σ⁻¹ h = σ⁻¹ (σ h) := by rw [hh']
      _ = h := by simp
  have hbwd := maps_to_XbB hF σ⁻¹ hTinv hfixinv
  refine le_antisymm hfwd ?_
  intro x hx
  have hx' : σ⁻¹ x ∈ XbB F := hbwd ⟨x, hx, rfl⟩
  exact ⟨σ⁻¹ x, hx', by simp⟩


theorem exists_scalar_Xa (hF : Nat.card F = 2 ^ 2) (σ : MulAut ↥(B0 F))
    (hT : (T0B F).map σ.toMonoidHom = T0B F)
    (hfix : ∀ h ∈ HB F, σ h = h) :
    ∃ lam : Fˣ, ∀ a : F,
      σ ⟨uElt a 0 0 0, Xa_le_B0 ⟨a, rfl⟩⟩ =
        ⟨uElt ((lam : F) * a) 0 0 0, Xa_le_B0 ⟨(lam : F) * a, rfl⟩⟩ := by
  classical
  have hXa := map_XaB hF σ hT hfix
  let ua : F → ↥(B0 F) := fun a => ⟨uElt a 0 0 0, Xa_le_B0 ⟨a, rfl⟩⟩
  have hua_mem (a : F) : ua a ∈ XaB F := ⟨a, rfl⟩
  have hex : ∀ a : F, ∃ b : F, σ (ua a) =
      (⟨uElt b 0 0 0, Xa_le_B0 ⟨b, rfl⟩⟩ : ↥(B0 F)) := by
    intro a
    have hmem : σ (ua a) ∈ XaB F := by
      rw [← hXa]
      exact ⟨ua a, hua_mem a, rfl⟩
    obtain ⟨b, hb⟩ := hmem
    exact ⟨b, Subtype.ext hb⟩
  let fa : F → F := fun a => Classical.choose (hex a)
  have hfa (a : F) : σ (ua a) =
      (⟨uElt (fa a) 0 0 0, Xa_le_B0 ⟨fa a, rfl⟩⟩ : ↥(B0 F)) :=
    Classical.choose_spec (hex a)
  have hfa0 : fa 0 = 0 := by
    have h := hfa 0
    have h1 : (⟨uElt (fa 0) 0 0 0, Xa_le_B0 ⟨fa 0, rfl⟩⟩ : ↥(B0 F)) = 1 := by
      rw [← h]
      simp [ua, uElt_zero_eq_one]
    have h2 : (uElt (fa 0) 0 0 0 : antiSp F) = 1 := Subtype.ext_iff.mp h1
    have h3 : (uElt (fa 0) 0 0 0 : antiSp F) = uElt 0 0 0 0 := by
      simpa [uElt_zero_eq_one] using h2
    exact (uElt_inj h3).1
  have hfa_add : ∀ a b : F, fa (a + b) = fa a + fa b := by
    intro a b
    have hmul : σ (ua (a + b)) = σ (ua a) * σ (ua b) := by
      rw [show ua (a + b) = ua a * ua b by
        apply Subtype.ext
        change uElt (a + b) 0 0 0 = uElt a 0 0 0 * uElt b 0 0 0
        rw [uElt_mul]
        congr 1 <;> ring]
      rw [map_mul]
    rw [hfa (a + b), hfa a, hfa b] at hmul
    have hv : (uElt (fa (a + b)) 0 0 0 : antiSp F) = uElt (fa a + fa b) 0 0 0 := by
      have := congrArg (fun z : ↥(B0 F) => (z : antiSp F)) hmul
      simpa [uElt_mul] using this
    exact (uElt_inj hv).1
  have hfa1 : fa 1 ≠ 0 := by
    intro h0
    have h : σ (ua 1) = 1 := by
      rw [hfa 1, h0]
      simp [ua, uElt_zero_eq_one]
    have hua1 : ua 1 = 1 := σ.injective (by simpa using h)
    have hv : (uElt 1 0 0 0 : antiSp F) = 1 := Subtype.ext_iff.mp hua1
    have hv' : (uElt 1 0 0 0 : antiSp F) = uElt 0 0 0 0 := by
      simpa [uElt_zero_eq_one] using hv
    have h10 : (1 : F) = 0 := (uElt_inj hv').1
    exact one_ne_zero h10
  have hscale : ∀ (μ : Fˣ) (a : F), fa ((μ : F) * a) = (μ : F) * fa a := by
    intro μ a
    let hμ : ↥(B0 F) := ⟨dSp μ 1, dTor_le (dSp_mem_dTor μ 1)⟩
    have hμH : hμ ∈ HB F := Subgroup.mem_subgroupOf.mpr (dSp_mem_dTor μ 1)
    have hfixμ : σ hμ = hμ := hfix hμ hμH
    have hconj : σ (hμ * ua a * hμ⁻¹) = σ (ua ((μ : F) * a)) := by
      congr 1
      apply Subtype.ext
      change dSp μ 1 * uElt a 0 0 0 * (dSp μ 1)⁻¹ = uElt ((μ : F) * a) 0 0 0
      rw [dSp_conj_uElt]
      simp
    rw [map_mul, map_mul, map_inv, hfixμ, hfa a] at hconj
    have hEq : hμ * ua (fa a) * hμ⁻¹ = ua (fa ((μ : F) * a)) := by
      have h := hconj
      rw [hfa ((μ : F) * a)] at h
      exact h
    have hleft : ((hμ * ua (fa a) * hμ⁻¹ : ↥(B0 F)) : antiSp F) =
        uElt ((μ : F) * fa a) 0 0 0 := by
      change (dSp μ 1 : antiSp F) * uElt (fa a) 0 0 0 * (dSp μ 1)⁻¹ =
        uElt ((μ : F) * fa a) 0 0 0
      rw [dSp_conj_uElt]
      simp
    have hv := congrArg (fun z : ↥(B0 F) => (z : antiSp F)) hEq
    rw [hleft] at hv
    exact (uElt_inj hv).1.symm
  let lam : Fˣ := Units.mk0 (fa 1) hfa1
  refine ⟨lam, ?_⟩
  have hscaled : ∀ a : F, fa a = (lam : F) * a := by
    intro a
    by_cases ha : a = 0
    · subst ha
      rw [hfa0]
      simp
    · let μ : Fˣ := Units.mk0 a ha
      have hμa : (μ : F) = a := rfl
      calc fa a = fa ((μ : F) * 1) := by rw [hμa, mul_one]
        _ = (μ : F) * fa 1 := hscale μ 1
        _ = a * fa 1 := by rw [hμa]
        _ = (lam : F) * a := by
          change a * fa 1 = fa 1 * a
          exact mul_comm _ _
  intro a
  rw [hfa a, hscaled a]

theorem exists_scalar_Xb (hF : Nat.card F = 2 ^ 2) (σ : MulAut ↥(B0 F))
    (hT : (T0B F).map σ.toMonoidHom = T0B F)
    (hfix : ∀ h ∈ HB F, σ h = h) :
    ∃ lam : Fˣ, ∀ d : F,
      σ ⟨uElt 0 0 0 d, Xb_le_B0 ⟨d, rfl⟩⟩ =
        ⟨uElt 0 0 0 ((lam : F) * d), Xb_le_B0 ⟨(lam : F) * d, rfl⟩⟩ := by
  classical
  have hXb := map_XbB hF σ hT hfix
  let ub : F → ↥(B0 F) := fun d => ⟨uElt 0 0 0 d, Xb_le_B0 ⟨d, rfl⟩⟩
  have hub_mem (d : F) : ub d ∈ XbB F := ⟨d, rfl⟩
  have hex : ∀ d : F, ∃ e : F, σ (ub d) =
      (⟨uElt 0 0 0 e, Xb_le_B0 ⟨e, rfl⟩⟩ : ↥(B0 F)) := by
    intro d
    have hmem : σ (ub d) ∈ XbB F := by
      rw [← hXb]
      exact ⟨ub d, hub_mem d, rfl⟩
    obtain ⟨e, he⟩ := hmem
    exact ⟨e, Subtype.ext he⟩
  let fb : F → F := fun d => Classical.choose (hex d)
  have hfb (d : F) : σ (ub d) =
      (⟨uElt 0 0 0 (fb d), Xb_le_B0 ⟨fb d, rfl⟩⟩ : ↥(B0 F)) :=
    Classical.choose_spec (hex d)
  have hfb0 : fb 0 = 0 := by
    have h := hfb 0
    have h1 : (⟨uElt 0 0 0 (fb 0), Xb_le_B0 ⟨fb 0, rfl⟩⟩ : ↥(B0 F)) = 1 := by
      rw [← h]
      simp [ub, uElt_zero_eq_one]
    have h2 : (uElt 0 0 0 (fb 0) : antiSp F) = 1 := Subtype.ext_iff.mp h1
    have h3 : (uElt 0 0 0 (fb 0) : antiSp F) = uElt 0 0 0 0 := by
      simpa [uElt_zero_eq_one] using h2
    exact (uElt_inj h3).2.2.2
  have hfb_add : ∀ a b : F, fb (a + b) = fb a + fb b := by
    intro a b
    have hmul : σ (ub (a + b)) = σ (ub a) * σ (ub b) := by
      rw [show ub (a + b) = ub a * ub b by
        apply Subtype.ext
        change uElt 0 0 0 (a + b) = uElt 0 0 0 a * uElt 0 0 0 b
        rw [uElt_mul]
        congr 1 <;> ring]
      rw [map_mul]
    rw [hfb (a + b), hfb a, hfb b] at hmul
    have hv : (uElt 0 0 0 (fb (a + b)) : antiSp F) = uElt 0 0 0 (fb a + fb b) := by
      have := congrArg (fun z : ↥(B0 F) => (z : antiSp F)) hmul
      simpa [uElt_mul] using this
    exact (uElt_inj hv).2.2.2
  have hfb1 : fb 1 ≠ 0 := by
    intro h0
    have h : σ (ub 1) = 1 := by
      rw [hfb 1, h0]
      simp [ub, uElt_zero_eq_one]
    have hub1 : ub 1 = 1 := σ.injective (by simpa using h)
    have hv : (uElt 0 0 0 1 : antiSp F) = 1 := Subtype.ext_iff.mp hub1
    have hv' : (uElt 0 0 0 1 : antiSp F) = uElt 0 0 0 0 := by
      simpa [uElt_zero_eq_one] using hv
    have h10 : (1 : F) = 0 := (uElt_inj hv').2.2.2
    exact one_ne_zero h10
  have hsq_surj : ∀ μ : Fˣ, ∃ τ : Fˣ, τ ^ 2 = μ := by
    intro μ
    refine ⟨μ ^ 2, ?_⟩
    have hcu : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]; norm_num
    have h3 : μ ^ 3 = 1 := by
      simpa [hcu] using pow_card_eq_one' (x := μ)
    calc (μ ^ 2) ^ 2 = μ ^ 4 := by rw [← pow_mul]
      _ = μ ^ 3 * μ := by
        rw [show 4 = 3 + 1 by norm_num, pow_add]
        simp
      _ = μ := by simp [h3]
  have hscale : ∀ (τ : Fˣ) (d : F), fb (((τ : F) ^ 2) * d) = ((τ : F) ^ 2) * fb d := by
    intro τ d
    let hτ : ↥(B0 F) := ⟨dSp 1 τ, dTor_le (dSp_mem_dTor 1 τ)⟩
    have hτH : hτ ∈ HB F := Subgroup.mem_subgroupOf.mpr (dSp_mem_dTor 1 τ)
    have hfixτ : σ hτ = hτ := hfix hτ hτH
    have hconj : σ (hτ * ub d * hτ⁻¹) = σ (ub (((τ : F) ^ 2) * d)) := by
      congr 1
      apply Subtype.ext
      change dSp 1 τ * uElt 0 0 0 d * (dSp 1 τ)⁻¹ = uElt 0 0 0 (((τ : F) ^ 2) * d)
      rw [dSp_conj_uElt]
      simp
    rw [map_mul, map_mul, map_inv, hfixτ, hfb d] at hconj
    have hEq : hτ * ub (fb d) * hτ⁻¹ = ub (fb (((τ : F) ^ 2) * d)) := by
      have h := hconj
      rw [hfb (((τ : F) ^ 2) * d)] at h
      exact h
    have hleft : ((hτ * ub (fb d) * hτ⁻¹ : ↥(B0 F)) : antiSp F) =
        uElt 0 0 0 (((τ : F) ^ 2) * fb d) := by
      change (dSp 1 τ : antiSp F) * uElt 0 0 0 (fb d) * (dSp 1 τ)⁻¹ =
        uElt 0 0 0 (((τ : F) ^ 2) * fb d)
      rw [dSp_conj_uElt]
      simp
    have hv := congrArg (fun z : ↥(B0 F) => (z : antiSp F)) hEq
    rw [hleft] at hv
    exact (uElt_inj hv).2.2.2.symm
  let lam : Fˣ := Units.mk0 (fb 1) hfb1
  refine ⟨lam, ?_⟩
  have hscaled : ∀ d : F, fb d = (lam : F) * d := by
    intro d
    by_cases hd : d = 0
    · subst hd
      rw [hfb0]
      simp
    · let μ : Fˣ := Units.mk0 d hd
      obtain ⟨τ, hτ⟩ := hsq_surj μ
      have hτd : ((τ : F) ^ 2) * 1 = d := by
        have hμd : (μ : F) = d := rfl
        rw [← hμd, ← hτ]
        norm_num
      calc fb d = fb (((τ : F) ^ 2) * 1) := by rw [hτd]
        _ = ((τ : F) ^ 2) * fb 1 := hscale τ 1
        _ = (μ : F) * fb 1 := by
          rw [show ((τ : F) ^ 2) = (μ : F) by
            simpa using congrArg (fun u : Fˣ => (u : F)) hτ]
        _ = d * fb 1 := by rw [show (μ : F) = d from rfl]
        _ = (lam : F) * d := by
          change d * fb 1 = fb 1 * d
          exact mul_comm _ _
  intro d
  rw [hfb d, hscaled d]


theorem map_closure_generators_B0 :
    (Subgroup.closure ((XaB F : Set ↥(B0 F)) ∪ XbB F ∪ HB F)).map (B0 F).subtype =
      Subgroup.closure ((rootXa F : Set (antiSp F)) ∪ rootXb F ∪ dTor F) := by
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases hz with (hz | hz) | hz
    · exact Or.inl (Or.inl hz)
    · exact Or.inl (Or.inr hz)
    · exact Or.inr hz
  · intro hy
    rcases hy with (hy | hy) | hy
    · exact ⟨⟨y, Xa_le_B0 hy⟩, Or.inl (Or.inl hy), rfl⟩
    · exact ⟨⟨y, Xb_le_B0 hy⟩, Or.inl (Or.inr hy), rfl⟩
    · exact ⟨⟨y, dTor_le hy⟩, Or.inr hy, rfl⟩

theorem closure_generators_top (hF : Nat.card F = 2 ^ 2) :
    Subgroup.closure ((XaB F : Set ↥(B0 F)) ∪ XbB F ∪ HB F) = ⊤ := by
  rw [eq_top_iff]
  intro b _
  have hb' : (b : antiSp F) ∈
      (Subgroup.closure ((XaB F : Set ↥(B0 F)) ∪ XbB F ∪ HB F)).map (B0 F).subtype := by
    rw [map_closure_generators_B0]
    exact B0_le_closure hF b.2
  obtain ⟨c, hc, hcb⟩ := hb'
  have hcbeq : c = b := Subtype.ext hcb
  rwa [hcbeq] at hc

theorem exists_conj_of_fixes_H (hF : Nat.card F = 2 ^ 2) (σ : MulAut ↥(B0 F))
    (hT : (T0B F).map σ.toMonoidHom = T0B F)
    (hfix : ∀ h ∈ HB F, σ h = h) :
    ∃ h₀ : ↥(B0 F), ∀ b : ↥(B0 F), σ b = h₀ * b * h₀⁻¹ := by
  classical
  obtain ⟨lamA, hA⟩ := exists_scalar_Xa hF σ hT hfix
  obtain ⟨lamB, hB⟩ := exists_scalar_Xb hF σ hT hfix
  let t0 : Fˣ := lamB ^ 2
  have ht0 : t0 ^ 2 = lamB := by
    have hcu : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]; norm_num
    have h3 : lamB ^ 3 = 1 := by
      simpa [hcu] using pow_card_eq_one' (x := lamB)
    calc t0 ^ 2 = lamB ^ 4 := by
          rw [show t0 = lamB ^ 2 from rfl, ← pow_mul]
      _ = lamB ^ 3 * lamB := by
          rw [show 4 = 3 + 1 by norm_num, pow_add]
          simp
      _ = lamB := by simp [h3]
  let h0 : ↥(B0 F) :=
    ⟨dSp (lamA * t0) t0, dTor_le (dSp_mem_dTor (lamA * t0) t0)⟩
  have h0H : h0 ∈ HB F :=
    Subgroup.mem_subgroupOf.mpr (dSp_mem_dTor (lamA * t0) t0)
  have hEq : ∀ x ∈ Subgroup.closure ((XaB F : Set ↥(B0 F)) ∪ XbB F ∪ HB F),
      σ x = h0 * x * h0⁻¹ := by
    intro x hx
    refine Subgroup.closure_induction (p := fun y _ => σ y = h0 * y * h0⁻¹)
      ?mem ?one ?mul ?inv hx
    · intro y hy
      rcases hy with (hy | hy) | hy
      · obtain ⟨a, ha⟩ := hy
        have hy' : y = (⟨uElt a 0 0 0, Xa_le_B0 ⟨a, rfl⟩⟩ : ↥(B0 F)) := Subtype.ext ha
        rw [hy', hA a]
        apply Subtype.ext
        dsimp only [h0]
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
        simp only [Subgroup.coe_mk]
        change uElt ((lamA : F) * a) 0 0 0 =
          (dSp (lamA * t0) t0 : antiSp F) * uElt a 0 0 0 * (dSp (lamA * t0) t0)⁻¹
        rw [dSp_conj_uElt]
        congr 1
        · rw [Units.val_mul]
          symm
          calc (↑lamA * ↑t0) * ↑t0⁻¹ * a
              = ↑lamA * (↑t0 * ↑t0⁻¹) * a := by ring
            _ = ↑lamA * 1 * a := by rw [Units.mul_inv]
            _ = ↑lamA * a := by ring
        · simp
        · simp
        · simp
      · obtain ⟨d, hd⟩ := hy
        have hy' : y = (⟨uElt 0 0 0 d, Xb_le_B0 ⟨d, rfl⟩⟩ : ↥(B0 F)) := Subtype.ext hd
        rw [hy', hB d]
        apply Subtype.ext
        dsimp only [h0]
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
        simp only [Subgroup.coe_mk]
        change uElt 0 0 0 ((lamB : F) * d) =
          (dSp (lamA * t0) t0 : antiSp F) * uElt 0 0 0 d * (dSp (lamA * t0) t0)⁻¹
        rw [dSp_conj_uElt]
        congr 1
        · simp
        · simp
        · simp
        · rw [show ((lamB : F) * d) = ((t0 : F) ^ 2) * d by
              rw [show ((t0 : F) ^ 2) = (lamB : F) by
                simpa using congrArg (fun u : Fˣ => (u : F)) ht0]]
      · have hcomm : h0 * y = y * h0 := Subtype.ext (dTor_comm h0H hy)
        rw [hfix y hy, hcomm, mul_assoc, mul_inv_cancel, mul_one]
    · simp
    · intro x y hx hy ihx ihy
      rw [map_mul, ihx, ihy]
      group
    · intro x hx ih
      rw [map_inv, ih]
      group
  refine ⟨h0, ?_⟩
  intro b
  exact hEq b (by
    rw [closure_generators_top hF]
    exact Subgroup.mem_top b)

theorem preserves_Kb {σ : MulAut ↥(B0 F)}
    (hA1 : (A1B F).map σ.toMonoidHom = A1B F)
    (hZ : (Z0B F).map σ.toMonoidHom = Z0B F)
    {h : ↥(B0 F)}
    (hh : ∀ x : antiSp F, x ∈ radA1 F →
      (h : antiSp F) * x * (h : antiSp F)⁻¹ * x⁻¹ ∈ antiUnipotentCenter F) :
    ∀ x : antiSp F, x ∈ radA1 F →
      (σ h : antiSp F) * x * (σ h : antiSp F)⁻¹ * x⁻¹ ∈ antiUnipotentCenter F := by
  intro x hx
  let xB : ↥(B0 F) := ⟨x, A1_le_B0 hx⟩
  have hx1 : xB ∈ A1B F := Subgroup.mem_subgroupOf.mpr hx
  have hxmap : xB ∈ (A1B F).map σ.toMonoidHom := by
    rw [hA1]
    exact hx1
  obtain ⟨y, hy1, hyx⟩ := hxmap
  have hcond : h * y * h⁻¹ * y⁻¹ ∈ Z0B F := by
    have := hh (y : antiSp F) hy1
    simpa [Subgroup.mem_subgroupOf] using this
  have hcondmap : σ (h * y * h⁻¹ * y⁻¹) ∈ Z0B F := by
    have : σ (h * y * h⁻¹ * y⁻¹) ∈ (Z0B F).map σ.toMonoidHom := ⟨_, hcond, rfl⟩
    rwa [hZ] at this
  have hxy : (σ y : antiSp F) = x := by
    change ((MulEquiv.toMonoidHom σ) y : antiSp F) = x
    rw [hyx]
  have hval : (σ (h * y * h⁻¹ * y⁻¹) : antiSp F) =
      (σ h : antiSp F) * x * (σ h : antiSp F)⁻¹ * x⁻¹ := by
    rw [map_mul, map_mul, map_inv, map_inv]
    simp [hxy]
  rw [← hval]
  exact hcondmap

theorem preserves_Ka {σ : MulAut ↥(B0 F)}
    (hA2 : (A2B F).map σ.toMonoidHom = A2B F)
    (hZ : (Z0B F).map σ.toMonoidHom = Z0B F)
    {h : ↥(B0 F)}
    (hh : ∀ x : antiSp F, x ∈ radA2 F →
      (h : antiSp F) * x * (h : antiSp F)⁻¹ * x⁻¹ ∈ antiUnipotentCenter F) :
    ∀ x : antiSp F, x ∈ radA2 F →
      (σ h : antiSp F) * x * (σ h : antiSp F)⁻¹ * x⁻¹ ∈ antiUnipotentCenter F := by
  intro x hx
  let xB : ↥(B0 F) := ⟨x, A2_le_B0 hx⟩
  have hx1 : xB ∈ A2B F := Subgroup.mem_subgroupOf.mpr hx
  have hxmap : xB ∈ (A2B F).map σ.toMonoidHom := by
    rw [hA2]
    exact hx1
  obtain ⟨y, hy1, hyx⟩ := hxmap
  have hcond : h * y * h⁻¹ * y⁻¹ ∈ Z0B F := by
    have := hh (y : antiSp F) hy1
    simpa [Subgroup.mem_subgroupOf] using this
  have hcondmap : σ (h * y * h⁻¹ * y⁻¹) ∈ Z0B F := by
    have : σ (h * y * h⁻¹ * y⁻¹) ∈ (Z0B F).map σ.toMonoidHom := ⟨_, hcond, rfl⟩
    rwa [hZ] at this
  have hxy : (σ y : antiSp F) = x := by
    change ((MulEquiv.toMonoidHom σ) y : antiSp F) = x
    rw [hyx]
  have hval : (σ (h * y * h⁻¹ * y⁻¹) : antiSp F) =
      (σ h : antiSp F) * x * (σ h : antiSp F)⁻¹ * x⁻¹ := by
    rw [map_mul, map_mul, map_inv, map_inv]
    simp [hxy]
  rw [← hval]
  exact hcondmap

theorem preserves_K2 {σ : MulAut ↥(B0 F)}
    (hU2 : (U2B F).map σ.toMonoidHom = U2B F) {h : ↥(B0 F)}
    (hh : ∀ x : antiSp F, x ∈ rootU₂ F →
      (h : antiSp F) * x * (h : antiSp F)⁻¹ = x) :
    ∀ x : antiSp F, x ∈ rootU₂ F →
      (σ h : antiSp F) * x * (σ h : antiSp F)⁻¹ = x := by
  intro x hx
  let xB : ↥(B0 F) := ⟨x, U2_le_B0 hx⟩
  have hx1 : xB ∈ U2B F := Subgroup.mem_subgroupOf.mpr hx
  have hxmap : xB ∈ (U2B F).map σ.toMonoidHom := by
    rw [hU2]
    exact hx1
  obtain ⟨y, hy1, hyx⟩ := hxmap
  have hcond : h * y * h⁻¹ = y := by
    apply Subtype.ext
    simpa using hh (y : antiSp F) hy1
  have hgoal : σ h * xB * (σ h)⁻¹ = xB := by
    rw [← hyx]
    calc σ h * σ y * (σ h)⁻¹ = σ (h * y * h⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = σ y := by rw [hcond]
  have := congrArg (fun z : ↥(B0 F) => (z : antiSp F)) hgoal
  simpa using this

theorem torus_action_eq_pow (hF : Nat.card F = 2 ^ 2) (σ₁ : MulAut ↥(B0 F))
    (hH : (HB F).map σ₁.toMonoidHom = HB F)
    (hA1 : (A1B F).map σ₁.toMonoidHom = A1B F)
    (hA2 : (A2B F).map σ₁.toMonoidHom = A2B F)
    (hZ : (Z0B F).map σ₁.toMonoidHom = Z0B F)
    (hU2 : (U2B F).map σ₁.toMonoidHom = U2B F) :
    ∃ ε : ℕ, (ε = 1 ∨ ε = 2) ∧
      ∀ s t : Fˣ, σ₁ ⟨dSp s t, dTor_le (dSp_mem_dTor s t)⟩ =
        ⟨dSp (s ^ ε) (t ^ ε), dTor_le (dSp_mem_dTor (s ^ ε) (t ^ ε))⟩ := by
  classical
  haveI : Fintype Fˣ := Fintype.ofFinite Fˣ
  have hcu : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]; norm_num
  have h1lt : 1 < Fintype.card Fˣ := by
    rw [← Nat.card_eq_fintype_card, hcu]
    norm_num
  obtain ⟨ω, hω⟩ := Fintype.exists_ne_of_one_lt_card h1lt (1 : Fˣ)
  have hcover : ∀ x : Fˣ, x = 1 ∨ x = ω ∨ x = ω ^ 2 :=
    fun x => units_eq_one_or_eq_or_sq (F := F) hF hω x
  have hωω2 : ω ^ 1 ≠ ω ^ 2 := units_pow_one_ne_pow_two (F := F) hF hω
  let t : ↥(B0 F) := ⟨dSp ω 1, dTor_le (dSp_mem_dTor ω 1)⟩
  have htH : t ∈ HB F := Subgroup.mem_subgroupOf.mpr (dSp_mem_dTor ω 1)
  have hσtH : σ₁ t ∈ HB F := by
    rw [← hH]
    exact ⟨t, htH, rfl⟩
  have hKb_t : ∀ x : antiSp F, x ∈ radA1 F →
      (t : antiSp F) * x * (t : antiSp F)⁻¹ * x⁻¹ ∈ antiUnipotentCenter F := by
    intro x hx
    exact (dSp_mem_Kb_iff hF ω 1).mpr rfl x hx
  have hKb_img := preserves_Kb (F := F) hA1 hZ hKb_t
  obtain ⟨s, u, hsu⟩ := mem_dTor.mp (Subgroup.mem_subgroupOf.mp hσtH)
  have hKb' : ∀ x ∈ radA1 F,
      dSp s u * x * (dSp s u)⁻¹ * x⁻¹ ∈ antiUnipotentCenter F := by
    simpa [hsu] using hKb_img
  have hu : u = 1 := (dSp_mem_Kb_iff hF s u).mp hKb'
  have hsut : (σ₁ t : antiSp F) = dSp s 1 := by
    rw [hsu, hu]
  have hsne : s ≠ 1 := by
    intro hs1
    have hσt1 : σ₁ t = 1 := by
      apply Subtype.ext
      rw [hsut, hs1]
      simp [dSp_one]
    have ht1 : t = 1 := σ₁.injective (by simpa using hσt1)
    have hd : dSp ω 1 = (1 : antiSp F) := Subtype.ext_iff.mp ht1
    exact hω (dSp_inj (hd.trans dSp_one.symm)).1
  have hsa : s = ω ∨ s = ω ^ 2 := by
    rcases hcover s with h | h | h
    · exact absurd h hsne
    · exact Or.inl h
    · exact Or.inr h
  let εa : ℕ := if s = ω then 1 else 2
  have hεa : εa = 1 ∨ εa = 2 := by
    by_cases hsω : s = ω <;> simp [εa, hsω]
  have hspow : s = ω ^ εa := by
    rcases hsa with h | h
    · subst h
      simp [εa]
    · subst h
      have hne : ¬ (ω ^ 2 = ω) := fun hh => units_ne_sq (F := F) hF hω hh.symm
      simp [εa, hne]
  let t2 : ↥(B0 F) := ⟨dSp 1 ω, dTor_le (dSp_mem_dTor 1 ω)⟩
  have ht2H : t2 ∈ HB F := Subgroup.mem_subgroupOf.mpr (dSp_mem_dTor 1 ω)
  have hσt2H : σ₁ t2 ∈ HB F := by
    rw [← hH]
    exact ⟨t2, ht2H, rfl⟩
  have hK2_t : ∀ x : antiSp F, x ∈ rootU₂ F →
      (t2 : antiSp F) * x * (t2 : antiSp F)⁻¹ = x := by
    intro x hx
    exact (dSp_mem_K2ab_iff hF 1 ω).mpr rfl x hx
  have hK2_img := preserves_K2 (F := F) hU2 hK2_t
  obtain ⟨s2, u2, hsu2⟩ := mem_dTor.mp (Subgroup.mem_subgroupOf.mp hσt2H)
  have hK2' : ∀ x ∈ rootU₂ F, dSp s2 u2 * x * (dSp s2 u2)⁻¹ = x := by
    simpa [hsu2] using hK2_img
  have hs2 : s2 = 1 := (dSp_mem_K2ab_iff hF s2 u2).mp hK2'
  have hsut2 : (σ₁ t2 : antiSp F) = dSp 1 u2 := by
    rw [hsu2, hs2]
  have hu2ne : u2 ≠ 1 := by
    intro hu2
    have hσt21 : σ₁ t2 = 1 := by
      apply Subtype.ext
      rw [hsut2, hu2]
      simp [dSp_one]
    have ht21 : t2 = 1 := σ₁.injective (by simpa using hσt21)
    have hd : dSp 1 ω = (1 : antiSp F) := Subtype.ext_iff.mp ht21
    exact hω (dSp_inj (hd.trans dSp_one.symm)).2
  have hu2a : u2 = ω ∨ u2 = ω ^ 2 := by
    rcases hcover u2 with h | h | h
    · exact absurd h hu2ne
    · exact Or.inl h
    · exact Or.inr h
  let εb : ℕ := if u2 = ω then 1 else 2
  have hεb : εb = 1 ∨ εb = 2 := by
    by_cases huω : u2 = ω <;> simp [εb, huω]
  have hu2pow : u2 = ω ^ εb := by
    rcases hu2a with h | h
    · subst h
      simp [εb]
    · subst h
      have hne : ¬ (ω ^ 2 = ω) := fun hh => units_ne_sq (F := F) hF hω hh.symm
      simp [εb, hne]
  let t3 : ↥(B0 F) := t * t2
  have ht3H : t3 ∈ HB F := (HB F).mul_mem htH ht2H
  have hKa_t3 : ∀ x : antiSp F, x ∈ radA2 F →
      (t3 : antiSp F) * x * (t3 : antiSp F)⁻¹ * x⁻¹ ∈ antiUnipotentCenter F := by
    intro x hx
    have h3 : (t3 : antiSp F) = dSp ω ω := by
      change (dSp ω 1 : antiSp F) * dSp 1 ω = dSp ω ω
      rw [dSp_mul]
      simp
    rw [h3]
    exact (dSp_mem_Ka_iff hF ω ω).mpr rfl x hx
  have hKa_img := preserves_Ka (F := F) hA2 hZ hKa_t3
  have hσt3 : (σ₁ t3 : antiSp F) = dSp s u2 := by
    change (σ₁ (t * t2) : antiSp F) = dSp s u2
    rw [map_mul]
    change (σ₁ t : antiSp F) * (σ₁ t2 : antiSp F) = dSp s u2
    rw [hsut, hsut2, dSp_mul]
    simp
  have hKa' : ∀ x ∈ radA2 F,
      dSp s u2 * x * (dSp s u2)⁻¹ * x⁻¹ ∈ antiUnipotentCenter F := by
    simpa only [hσt3] using hKa_img
  have hst : s = u2 := (dSp_mem_Ka_iff hF s u2).mp hKa'
  have hεeq : εa = εb := by
    have hpow : ω ^ εa = ω ^ εb := by
      rw [← hspow, ← hu2pow, hst]
    rcases hεa with ha | ha <;> rcases hεb with hb | hb
    · rw [ha, hb]
    · rw [ha, hb] at hpow
      exact absurd hpow hωω2
    · rw [ha, hb] at hpow
      exact absurd hpow.symm hωω2
    · rw [ha, hb]
  refine ⟨εa, hεa, ?_⟩
  have hleft : ∀ x : Fˣ,
      σ₁ ⟨dSp x 1, dTor_le (dSp_mem_dTor x 1)⟩ =
        ⟨dSp (x ^ εa) 1, dTor_le (dSp_mem_dTor (x ^ εa) 1)⟩ := by
    intro x
    have hgen : σ₁ ⟨dSp ω 1, dTor_le (dSp_mem_dTor ω 1)⟩ =
        ⟨dSp (ω ^ εa) 1, dTor_le (dSp_mem_dTor (ω ^ εa) 1)⟩ := by
      apply Subtype.ext
      rw [hsut, ← hspow]
    rcases hcover x with hx | hx | hx
    · subst hx
      apply Subtype.ext
      simp [dSp_one]
    · subst hx
      exact hgen
    · subst hx
      have hpow2 : (⟨dSp (ω ^ 2) 1, dTor_le (dSp_mem_dTor (ω ^ 2) 1)⟩ : ↥(B0 F)) =
          (⟨dSp ω 1, dTor_le (dSp_mem_dTor ω 1)⟩ : ↥(B0 F)) ^ 2 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, dSp_pow]
        simp
      rw [hpow2, map_pow, hgen]
      apply Subtype.ext
      rw [Subgroup.coe_pow, dSp_pow]
      simp only [one_pow]
      congr 1
      rw [← pow_mul, ← pow_mul, mul_comm]
  have hright : ∀ x : Fˣ,
      σ₁ ⟨dSp 1 x, dTor_le (dSp_mem_dTor 1 x)⟩ =
        ⟨dSp 1 (x ^ εa), dTor_le (dSp_mem_dTor 1 (x ^ εa))⟩ := by
    intro x
    have hgen : σ₁ ⟨dSp 1 ω, dTor_le (dSp_mem_dTor 1 ω)⟩ =
        ⟨dSp 1 (ω ^ εa), dTor_le (dSp_mem_dTor 1 (ω ^ εa))⟩ := by
      apply Subtype.ext
      rw [hsut2, hu2pow, ← hεeq]
    rcases hcover x with hx | hx | hx
    · subst hx
      apply Subtype.ext
      simp [dSp_one]
    · subst hx
      exact hgen
    · subst hx
      have hpow2 : (⟨dSp 1 (ω ^ 2), dTor_le (dSp_mem_dTor 1 (ω ^ 2))⟩ : ↥(B0 F)) =
          (⟨dSp 1 ω, dTor_le (dSp_mem_dTor 1 ω)⟩ : ↥(B0 F)) ^ 2 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, dSp_pow]
        simp
      rw [hpow2, map_pow, hgen]
      apply Subtype.ext
      rw [Subgroup.coe_pow, dSp_pow]
      simp only [one_pow]
      congr 1
      rw [← pow_mul, ← pow_mul, mul_comm]
  intro s0 t0
  have hdecomp : (⟨dSp s0 t0, dTor_le (dSp_mem_dTor s0 t0)⟩ : ↥(B0 F)) =
      (⟨dSp s0 1, dTor_le (dSp_mem_dTor s0 1)⟩ : ↥(B0 F)) *
        (⟨dSp 1 t0, dTor_le (dSp_mem_dTor 1 t0)⟩ : ↥(B0 F)) := by
    apply Subtype.ext
    change dSp s0 t0 = (dSp s0 1 : antiSp F) * dSp 1 t0
    rw [dSp_mul]
    simp
  rw [hdecomp, map_mul, hleft s0, hright t0]
  apply Subtype.ext
  change (dSp (s0 ^ εa) 1 : antiSp F) * dSp 1 (t0 ^ εa) = dSp (s0 ^ εa) (t0 ^ εa)
  rw [dSp_mul]
  simp


theorem sp44_dc (hF : Nat.card F = 2 ^ 2) (σ : ↥(B0 F) ≃* ↥(B0 F))
    (hA : ∀ b : ↥(B0 F), (b : antiSp F) ∈ radA1 F ↔ (σ b : antiSp F) ∈ radA1 F)
    (hU : ∃ b : ↥(B0 F), (b : antiSp F) ∈ rootU₁ F ∧ (σ b : antiSp F) ∉ rootU₂ F) :
    ∃ g ∈ B0 F, ∃ k : ℕ, ∀ b : ↥(B0 F),
      (σ b : antiSp F) = g * (frobAut F ^ k) (b : antiSp F) * g⁻¹ := by
  classical
  have hT : (T0B F).map σ.toMonoidHom = T0B F := map_T0B hF σ
  have hA1 : (A1B F).map σ.toMonoidHom = A1B F := map_A1B σ hA
  have hA2 : (A2B F).map σ.toMonoidHom = A2B F := map_A2B hF σ hA1 hT
  have hZ : (Z0B F).map σ.toMonoidHom = Z0B F := map_Z0B σ hA1 hA2
  have hU1 : (U1B F).map σ.toMonoidHom = U1B F := map_U1B hF σ hZ hU
  have hU2 : (U2B F).map σ.toMonoidHom = U2B F := map_U2B hF σ hZ hU1
  obtain ⟨g₁, hg₁⟩ := exists_conj_torusB hF σ
  let σ₁ : MulAut ↥(B0 F) := (MulAut.conj g₁)⁻¹ * σ
  have hH : (HB F).map σ₁.toMonoidHom = HB F := map_conj_inv_comp σ hg₁
  have hT₁ : (T0B F).map σ₁.toMonoidHom = T0B F := by
    letI : (T0B F).Normal := T0B_normal
    exact map_conj_inv_comp_of_map σ g₁ hT
  have hA1₁ : (A1B F).map σ₁.toMonoidHom = A1B F := by
    letI : (A1B F).Normal := radA1_normal
    exact map_conj_inv_comp_of_map σ g₁ hA1
  have hA2₁ : (A2B F).map σ₁.toMonoidHom = A2B F := by
    letI : (A2B F).Normal := radA2_normal
    exact map_conj_inv_comp_of_map σ g₁ hA2
  have hZ₁ : (Z0B F).map σ₁.toMonoidHom = Z0B F := by
    letI : (Z0B F).Normal := antiUnipotentCenter_normal
    exact map_conj_inv_comp_of_map σ g₁ hZ
  have hU1₁ : (U1B F).map σ₁.toMonoidHom = U1B F := by
    letI : (U1B F).Normal := rootU₁_normal
    exact map_conj_inv_comp_of_map σ g₁ hU1
  have hU2₁ : (U2B F).map σ₁.toMonoidHom = U2B F := by
    letI : (U2B F).Normal := rootU₂_normal
    exact map_conj_inv_comp_of_map σ g₁ hU2
  obtain ⟨ε, hε, hact⟩ := torus_action_eq_pow hF σ₁ hH hA1₁ hA2₁ hZ₁ hU2₁
  obtain ⟨k, hk, hfix⟩ := exists_frobAutB0_pow_fixes_torus hF σ₁ ε hε hact
  let σ₂ : MulAut ↥(B0 F) := (frobAutB0 (F := F) ^ k) * σ₁
  have hfix₂ : ∀ h ∈ HB F, σ₂ h = h := hfix
  have hT₂ : (T0B F).map σ₂.toMonoidHom = T0B F := by
    have hcomp : σ₂.toMonoidHom =
        ((frobAutB0 (F := F) ^ k).toMonoidHom.comp σ₁.toMonoidHom) := rfl
    rw [hcomp, ← Subgroup.map_map, hT₁, map_T0B hF (frobAutB0 (F := F) ^ k)]
  obtain ⟨h₀, hconj⟩ := exists_conj_of_fixes_H hF σ₂ hT₂ hfix₂
  have hσeq : σ = MulAut.conj g₁ * σ₁ := by
    rw [show σ₁ = (MulAut.conj g₁)⁻¹ * σ from rfl]
    group
  have hfrob2 : (frobAutB0 (F := F)) ^ 2 = 1 := frobAutB0_sq hF
  have hfinv : ((frobAutB0 (F := F)) ^ k)⁻¹ = frobAutB0 (F := F) ^ k := by
    rcases hk with rfl | rfl
    · simp
    · rw [pow_one]
      exact (eq_inv_of_mul_eq_one_right (by simpa [pow_two] using hfrob2)).symm
  have hσ₁b : ∀ b : ↥(B0 F), σ₁ b = (frobAutB0 (F := F) ^ k) (σ₂ b) := by
    intro b
    have h : σ₂ b = (frobAutB0 (F := F) ^ k) (σ₁ b) := by
      rw [show σ₂ = (frobAutB0 (F := F) ^ k) * σ₁ from rfl, MulAut.mul_apply]
    calc σ₁ b = ((frobAutB0 (F := F) ^ k)⁻¹) ((frobAutB0 (F := F) ^ k) (σ₁ b)) :=
          (MulAut.inv_apply_self ↥(B0 F) (frobAutB0 (F := F) ^ k) (σ₁ b)).symm
      _ = ((frobAutB0 (F := F) ^ k)⁻¹) (σ₂ b) := by rw [← h]
      _ = (frobAutB0 (F := F) ^ k) (σ₂ b) := by rw [hfinv]
  let gB : ↥(B0 F) := g₁ * (frobAutB0 (F := F) ^ k) h₀
  refine ⟨(gB : antiSp F), gB.2, k, ?_⟩
  intro b
  have hbB : σ b = gB * ((frobAutB0 (F := F) ^ k) b) * gB⁻¹ := by
    calc σ b = (MulAut.conj g₁ * σ₁) b := by rw [hσeq]
      _ = g₁ * σ₁ b * g₁⁻¹ := by rw [MulAut.mul_apply, MulAut.conj_apply]
      _ = g₁ * ((frobAutB0 (F := F) ^ k) (σ₂ b)) * g₁⁻¹ := by rw [hσ₁b b]
      _ = g₁ * ((frobAutB0 (F := F) ^ k) (h₀ * b * h₀⁻¹)) * g₁⁻¹ := by rw [hconj b]
      _ = g₁ * ((frobAutB0 (F := F) ^ k) h₀ *
            ((frobAutB0 (F := F) ^ k) b) * ((frobAutB0 (F := F) ^ k) h₀)⁻¹) * g₁⁻¹ := by
            rw [map_mul, map_mul, map_inv]
      _ = gB * ((frobAutB0 (F := F) ^ k) b) * gB⁻¹ := by
            simp only [gB]
            group
  have hv := congrArg (fun z : ↥(B0 F) => (z : antiSp F)) hbB
  simpa [gB, frobAutB0_pow_apply] using hv

end CFSG.Quasithin.F112R.St84.Sp44
