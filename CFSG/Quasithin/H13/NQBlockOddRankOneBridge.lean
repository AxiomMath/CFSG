module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2Cover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySuzukiNormalizer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.H13.U3SimpleRoot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesCollapse

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup
open scoped MatrixGroups LinearAlgebra.Projectivization Pointwise
open CFSG.Quasithin (fixV IsElemAbelian2)
open CFSG.QuasithinUnique.Setup.Family (CQ)
open CFSG.QuasithinUnique.Setup.SL2Modules (repOfSubgroup)

section Binary

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem add_self_eq_zero_of_zmod_two (w : W) : w + w = 0 := by
  rw [← two_smul (ZMod 2) w, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem multiplicative_mul_self (w : Multiplicative W) : w * w = 1 :=
  add_self_eq_zero_of_zmod_two (Multiplicative.toAdd w)

@[expose] def unitsToMulAut : (Module.End (ZMod 2) W)ˣ →* MulAut (Multiplicative W) :=
  MonoidHom.mk' (fun u =>
    { toFun := fun x => Multiplicative.ofAdd (u.val (Multiplicative.toAdd x))
      invFun := fun x => Multiplicative.ofAdd (u.inv (Multiplicative.toAdd x))
      left_inv := fun x => by
        change Multiplicative.ofAdd ((u.inv * u.val) (Multiplicative.toAdd x)) = x
        rw [u.inv_val]
        rfl
      right_inv := fun x => by
        change Multiplicative.ofAdd ((u.val * u.inv) (Multiplicative.toAdd x)) = x
        rw [u.val_inv]
        rfl
      map_mul' := fun x y => by
        change Multiplicative.ofAdd (u.val (Multiplicative.toAdd x + Multiplicative.toAdd y)) = _
        rw [map_add]
        rfl })
    fun _ _ => MulEquiv.ext fun _ => rfl

theorem unitsToMulAut_apply (u : (Module.End (ZMod 2) W)ˣ) (x : Multiplicative W) :
    unitsToMulAut u x = Multiplicative.ofAdd (u.val (Multiplicative.toAdd x)) := rfl

theorem unitsToMulAut_injective : Function.Injective (unitsToMulAut (W := W)) := by
  intro u v h
  refine Units.ext (LinearMap.ext fun w => ?_)
  have h1 := DFunLike.congr_fun h (Multiplicative.ofAdd w)
  rw [unitsToMulAut_apply, unitsToMulAut_apply] at h1
  exact Multiplicative.ofAdd.injective h1

theorem isPerfect_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : Group.IsPerfect A) : Group.IsPerfect B := by
  rw [Group.isPerfect_def, _root_.commutator_def] at h ⊢
  rw [← map_top_of_surjective (e : A →* B) e.surjective, ← map_commutator, h]

theorem offender_lt_of_mulAut_exclusion (L B : Subgroup (Module.End (ZMod 2) W)ˣ)
    (hirr : (repOfSubgroup L).IsIrreducible) (hperf : Group.IsPerfect L)
    (hBe : CFSG.IsElementaryAbelian 2 B) (hB1 : B ≠ ⊥)
    (hBN : B ≤ normalizer (L : Set (Module.End (ZMod 2) W)ˣ))
    (hex : ∀ L' : Subgroup (MulAut (Multiplicative W)), Group.IsPerfect L' →
      (∀ U : Subgroup (Multiplicative W), (∀ g ∈ L', ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) →
      Nonempty (CQ L' ≃* CQ L) →
      ∀ A : Subgroup (MulAut (Multiplicative W)),
        A ≤ normalizer (L' : Set (MulAut (Multiplicative W))) → A ≠ ⊥ → IsElemAbelian2 A →
          Nat.card A * Nat.card (fixV A) < Nat.card (Multiplicative W)) :
    Nat.card B * Nat.card {w : W // ∀ b ∈ B, b.val w = w} < Nat.card W := by
  classical
  have hφ := unitsToMulAut_injective (W := W)
  let eL : L ≃* L.map unitsToMulAut := L.equivMapOfInjective unitsToMulAut hφ
  have hperf' : Group.IsPerfect (L.map unitsToMulAut) := isPerfect_of_mulEquiv eL hperf
  have hirr' : ∀ U : Subgroup (Multiplicative W),
      (∀ g ∈ L.map unitsToMulAut, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    obtain ⟨-, hirrW⟩ := (CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff _).mp hirr
    let N : Submodule (ZMod 2) W := AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup' U)
    have hN : ∀ g : L, ∀ u ∈ N, repOfSubgroup L g u ∈ N := fun g u hu =>
      hU (unitsToMulAut g.1) ⟨g.1, g.2, rfl⟩ (Multiplicative.ofAdd u) hu
    rcases hirrW N hN with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      have hxN : Multiplicative.toAdd x ∈ N := hx
      rw [h, Submodule.mem_bot] at hxN
      exact hxN
    · right
      rw [eq_top_iff]
      intro x _
      have hxN : Multiplicative.toAdd x ∈ N := by
        rw [h]
        exact Submodule.mem_top
      exact hxN
  have hCQ : Nonempty (CQ (L.map unitsToMulAut) ≃* CQ L) :=
    ⟨(QuotientGroup.congr _ _ eL (map_center_eq eL)).symm⟩
  have hBN' : B.map unitsToMulAut ≤
      normalizer ((L.map unitsToMulAut : Subgroup _) : Set (MulAut (Multiplicative W))) :=
    (map_mono hBN).trans (le_normalizer_map _)
  have hB1' : B.map unitsToMulAut ≠ ⊥ := fun h =>
    hB1 ((map_eq_bot_iff_of_injective _ hφ).mp h)
  have hBe' : IsElemAbelian2 (B.map unitsToMulAut) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul,
        show a * b = b * a from congrArg Subtype.val (hBe.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := B) a ha, map_one]
  have h := hex _ hperf' hirr' hCQ _ hBN' hB1' hBe'
  have hfix : Nat.card (fixV (B.map unitsToMulAut)) =
      Nat.card {w : W // ∀ b ∈ B, b.val w = w} := by
    refine Nat.card_congr
      { toFun := fun x => ⟨Multiplicative.toAdd x.1, fun b hb => ?_⟩
        invFun := fun w => ⟨Multiplicative.ofAdd w.1, fun g hg => ?_⟩
        left_inv := fun x => rfl
        right_inv := fun w => rfl }
    · exact congrArg Multiplicative.toAdd (x.2 (unitsToMulAut b) ⟨b, hb, rfl⟩)
    · obtain ⟨b, hb, rfl⟩ := hg
      exact congrArg Multiplicative.ofAdd (w.2 b hb)
  rwa [card_map_of_injective hφ, hfix, Nat.card_congr Multiplicative.toAdd] at h

variable [Finite W] [Nontrivial W]

open CFSG.QuasithinUnique.Setup.Family (primeLinearTwoCover) in
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL) in
theorem offender_lt_of_projectiveSL
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : 11 ≤ ℓ)
    (L B : Subgroup (Module.End (ZMod 2) W)ˣ) (hirr : (repOfSubgroup L).IsIrreducible)
    (hperf : Group.IsPerfect L) (α : CQ L ≃* projectiveSL 2 (ZMod ℓ))
    (hBe : CFSG.IsElementaryAbelian 2 B) (hB1 : B ≠ ⊥)
    (hBN : B ≤ normalizer (L : Set (Module.End (ZMod 2) W)ˣ)) :
    Nat.card B * Nat.card {w : W // ∀ b ∈ B, b.val w = w} < Nat.card W :=
  offender_lt_of_mulAut_exclusion L B hirr hperf hBe hB1 hBN
    fun _ hperf' hirr' ⟨e⟩ A hA hA1 hAe =>
      (primeLinearTwoCover hℓ multiplicative_mul_self hperf' hirr' (e.trans α)).2 A hA hA1 hAe

open CFSG.QuasithinUnique.Setup.Family (suzuki_irreducible_normalizer_excludes) in
theorem offender_lt_of_suzuki
    (a : ℕ) (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (L B : Subgroup (Module.End (ZMod 2) W)ˣ)
    (hirr : (repOfSubgroup L).IsIrreducible) (hperf : Group.IsPerfect L)
    (α : CQ L ≃* CFSG.Blueprint.suzukiGroup a K) (hBe : CFSG.IsElementaryAbelian 2 B)
    (hB1 : B ≠ ⊥) (hBN : B ≤ normalizer (L : Set (Module.End (ZMod 2) W)ˣ)) :
    Nat.card B * Nat.card {w : W // ∀ b ∈ B, b.val w = w} < Nat.card W :=
  offender_lt_of_mulAut_exclusion L B hirr hperf hBe hB1 hBN
    fun L' hperf' hirr' ⟨e⟩ A hA hA1 hAe =>
      (suzuki_irreducible_normalizer_excludes a ha hK (Multiplicative W) multiplicative_mul_self
        L' hperf' hirr' (e.trans α)).2.2.2.2 A hA1 hAe hA

theorem offender_lt_of_J1 (L B : Subgroup (Module.End (ZMod 2) W)ˣ)
    (hirr : (repOfSubgroup L).IsIrreducible) (hperf : Group.IsPerfect L)
    (α : CQ L ≃* CFSG.Blueprint.NativeSporadic.J1) (hBe : CFSG.IsElementaryAbelian 2 B)
    (hB1 : B ≠ ⊥) (hBN : B ≤ normalizer (L : Set (Module.End (ZMod 2) W)ˣ)) :
    Nat.card B * Nat.card {w : W // ∀ b ∈ B, b.val w = w} < Nat.card W :=
  offender_lt_of_mulAut_exclusion L B hirr hperf hBe hB1 hBN
    fun L' hperf' hirr' ⟨e⟩ A hA hA1 hAe =>
      CFSG.QuasithinUnique.Setup.X1.j1ExclusionProp (Multiplicative W) multiplicative_mul_self
        L' A hperf' ⟨inferInstance, hirr'⟩ ⟨e.trans α⟩ hA hA1 hAe

end Binary

section SL2

open CFSG.QuasithinUnique.Setup.SL2Modules (upperRootGroup borelSubgroup uElt
  mem_upperRootGroup_iff sl2_defining_characteristic_Sylow_normalizer_maximal_Borel
  natCard_upperRootGroup)
open CFSG.GorensteinWalter (psl2ProjectiveInfinity psl2AffinePoint
  existsUnique_psl2AffinePoint_eq)

open Matrix

variable {F : Type} [Field F]

theorem uElt_smul_affinePoint (t x : F) :
    uElt t • psl2AffinePoint F x = psl2AffinePoint F (x + t) := by
  rw [psl2AffinePoint, Projectivization.smul_mk]
  change Projectivization.mk F ((uElt t).val *ᵥ ![x, 1]) _ =
    Projectivization.mk F ![x + t, 1] _
  rw [Projectivization.mk_eq_mk_iff']
  refine ⟨1, ?_⟩
  change (1 : F) • (![x + t, 1] : Fin 2 → F) = (uElt t).val *ᵥ ![x, 1]
  ext i
  fin_cases i <;> simp [uElt, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail, add_comm]

theorem exists_upperRootGroup_smul_eq {β γ : ℙ F (Fin 2 → F)}
    (hβ : β ≠ psl2ProjectiveInfinity F) (hγ : γ ≠ psl2ProjectiveInfinity F) :
    ∃ u ∈ upperRootGroup F, u • β = γ := by
  obtain ⟨x, rfl, -⟩ := existsUnique_psl2AffinePoint_eq β hβ
  obtain ⟨y, rfl, -⟩ := existsUnique_psl2AffinePoint_eq γ hγ
  refine ⟨uElt (y - x), (mem_upperRootGroup_iff _).mpr ⟨_, rfl⟩, ?_⟩
  rw [uElt_smul_affinePoint, add_sub_cancel]

@[expose] def mulCommSubgroup {G : Type*} [Group G] (A T : Subgroup G)
    (h : (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G)) : Subgroup G where
  carrier := (A : Set G) * (T : Set G)
  mul_mem' := by
    rintro _ _ ⟨x, hx, s, hs, rfl⟩ ⟨x', hx', s', hs', rfl⟩
    have hsx : s * x' ∈ (T : Set G) * (A : Set G) := ⟨s, hs, x', hx', rfl⟩
    rw [← h] at hsx
    obtain ⟨x'', hx'', s'', hs'', he⟩ := hsx
    have he : x'' * s'' = s * x' := he
    refine ⟨x * x'', A.mul_mem hx hx'', s'' * s', T.mul_mem hs'' hs', ?_⟩
    calc x * x'' * (s'' * s') = x * (x'' * s'') * s' := by group
      _ = x * s * (x' * s') := by rw [he]; group
  one_mem' := ⟨1, A.one_mem, 1, T.one_mem, one_mul 1⟩
  inv_mem' := by
    rintro _ ⟨x, hx, s, hs, rfl⟩
    have h' : s⁻¹ * x⁻¹ ∈ (T : Set G) * (A : Set G) :=
      ⟨s⁻¹, T.inv_mem hs, x⁻¹, A.inv_mem hx, rfl⟩
    rw [← h] at h'
    simpa [_root_.mul_inv_rev] using h'

theorem lt_sq_sub_one_of_prime_dvd {p q : ℕ} (hp : p.Prime) (hq : 3 ≤ q)
    (hdvd : p ∣ q ^ 2 - 1) : p < q ^ 2 - 1 := by
  have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  have hpos : 0 < q ^ 2 - 1 := by
    have : 9 ≤ q ^ 2 := by nlinarith
    omega
  rcases (Nat.le_of_dvd hpos hdvd).lt_or_eq with h | h
  · exact h
  · exfalso
    rw [h, hfac] at hp
    exact Nat.not_prime_mul (by omega) (by omega) hp

theorem sl2_le_normalizer_of_mul_comm [Fintype F] [IsSimpleGroup SL(2, F)] {f : ℕ} (hf : 3 ≤ f)
    (hF : Fintype.card F = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (D : Subgroup SL(2, F))
    (hD : Nat.card D = p) (T : Sylow 2 SL(2, F))
    (hDT : (D : Set SL(2, F)) * (T : Set SL(2, F)) = (T : Set SL(2, F)) * (D : Set SL(2, F))) :
    D ≤ normalizer ((T : Subgroup SL(2, F)) : Set SL(2, F)) ∧ p ∣ 2 ^ f - 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    (k := f) Nat.prime_two (by omega) (by rw [Nat.card_eq_fintype_card, hF])
  obtain ⟨hcard, ⟨U0, hU0⟩, -, hcardB, -, -, -, hsyl⟩ :=
    sl2_defining_characteristic_Sylow_normalizer_maximal_Borel (F := F) (p := 2)
  obtain ⟨g, hgT, hgN, -⟩ := hsyl T
  have hq8 : 8 ≤ Fintype.card F := by
    rw [hF]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hstab : MulAction.stabilizer SL(2, F) (g • psl2ProjectiveInfinity F) =
      normalizer ((T : Subgroup SL(2, F)) : Set SL(2, F)) := by
    ext x
    rw [hgN x, borelSubgroup, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
      mul_smul, mul_smul, inv_smul_eq_iff]
  have hTα : (T : Subgroup SL(2, F)) ≤ MulAction.stabilizer SL(2, F)
      (g • psl2ProjectiveInfinity F) := hstab ▸ le_normalizer
  have hTn : ((T : Subgroup SL(2, F)).subgroupOf
      (MulAction.stabilizer SL(2, F) (g • psl2ProjectiveInfinity F))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hTα).mpr hstab.le
  have hTcard : Nat.card (T : Subgroup SL(2, F)) = Fintype.card F := by
    rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity U0, hU0, natCard_upperRootGroup]
  have hT1 : (T : Subgroup SL(2, F)) ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hTcard
    omega
  have htr : ∀ β γ : ℙ F (Fin 2 → F), β ≠ g • psl2ProjectiveInfinity F →
      γ ≠ g • psl2ProjectiveInfinity F → ∃ u ∈ (T : Subgroup SL(2, F)), u • β = γ := by
    intro β γ hβ hγ
    have hβ' : g⁻¹ • β ≠ psl2ProjectiveInfinity F := fun h => hβ (by rw [← h, smul_inv_smul])
    have hγ' : g⁻¹ • γ ≠ psl2ProjectiveInfinity F := fun h => hγ (by rw [← h, smul_inv_smul])
    obtain ⟨u, hu, huβ⟩ := exists_upperRootGroup_smul_eq hβ' hγ'
    refine ⟨g * u * g⁻¹, (hgT _).mpr ?_, ?_⟩
    · rw [show g⁻¹ * (g * u * g⁻¹) * g = u by group]
      exact hu
    · rw [mul_smul, mul_smul, huβ, smul_inv_smul]
  set q := Fintype.card F with hq
  have hpq : ¬ p ∣ q := by
    rw [hF]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have hpSL : p ∣ q ^ 2 - 1 := by
    have h := card_subgroup_dvd_card D
    rw [hD, hcard] at h
    exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpq).dvd_of_dvd_mul_left h
  have hplt := lt_sq_sub_one_of_prime_dvd hp (by omega) hpSL
  let M := mulCommSubgroup D T hDT
  have hTM : (T : Subgroup SL(2, F)) ≤ M := fun s hs => ⟨1, D.one_mem, s, hs, one_mul s⟩
  have hDM : D ≤ M := fun x hx => ⟨x, hx, 1, (T : Subgroup SL(2, F)).one_mem, mul_one x⟩
  have hMlt : M < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun hM => ?_
    have h1 : Nat.card M ≤ Nat.card D * Nat.card (T : Subgroup SL(2, F)) :=
      Set.natCard_mul_le (s := (D : Set SL(2, F))) (t := (T : Set SL(2, F)))
    rw [hM, card_top, hcard, hD, hTcard] at h1
    have h2 : q * (q ^ 2 - 1) ≤ q * p := by rw [mul_comm q p]; exact h1
    have h3 := Nat.le_of_mul_le_mul_left h2 (by omega)
    omega
  have hMN := CFSG.Quasithin.H13.U3.simple_transitive_root_proper_overgroups
    (g • psl2ProjectiveInfinity F) hT1 hTα hTn htr hMlt hTM
  have hDN : D ≤ normalizer ((T : Subgroup SL(2, F)) : Set SL(2, F)) :=
    hstab ▸ hDM.trans hMN
  refine ⟨hDN, ?_⟩
  have hNcard : Nat.card (normalizer ((T : Subgroup SL(2, F)) : Set SL(2, F))) = q * (q - 1) := by
    rw [← hcardB]
    refine Nat.card_congr
      { toFun := fun x => ⟨g⁻¹ * x * g, (hgN x).mp x.2⟩
        invFun := fun b => ⟨g * b * g⁻¹, (hgN _).mpr ?_⟩
        left_inv := fun x => Subtype.ext ?_
        right_inv := fun b => Subtype.ext ?_ }
    · rw [show g⁻¹ * (g * (b : SL(2, F)) * g⁻¹) * g = b by group]
      exact b.2
    · change g * (g⁻¹ * (x : SL(2, F)) * g) * g⁻¹ = x
      group
    · change g⁻¹ * (g * (b : SL(2, F)) * g⁻¹) * g = b
      group
  have h := card_dvd_of_le hDN
  rw [hD, hNcard] at h
  rw [← hF]
  exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpq).dvd_of_dvd_mul_left h

end SL2

end CFSG.Quasithin.H13.NQBlock
