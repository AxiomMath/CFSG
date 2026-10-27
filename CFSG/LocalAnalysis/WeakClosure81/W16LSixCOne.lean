module

public import CFSG.LocalAnalysis.WeakClosure81.W16LSixCDefs
public import CFSG.LocalAnalysis.WeakClosure81.W16LCGrp
public import CFSG.LocalAnalysis.WeakClosure81.W162TenTwoBGroup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.SignalizerFunctorTheorem.Quadratic
open CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

private theorem w16l_eq_of_mem_zpowers_card_two {Y : Type} [Group Y] {t x : Y}
    (hcard : Nat.card (Subgroup.zpowers t) = 2) (hx : x ∈ Subgroup.zpowers t) (hx1 : x ≠ 1) :
    x = t := by
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hcard
    omega
  obtain ⟨z, -, hzuniq⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.zpowers t)).mp hcard
  have hx_eq : (⟨x, hx⟩ : Subgroup.zpowers t) = z :=
    hzuniq ⟨x, hx⟩ (fun h => hx1 (congrArg Subtype.val h))
  have ht_eq : (⟨t, Subgroup.mem_zpowers t⟩ : Subgroup.zpowers t) = z :=
    hzuniq ⟨t, Subgroup.mem_zpowers t⟩ (fun h => ht1 (congrArg Subtype.val h))
  exact congrArg Subtype.val (hx_eq.trans ht_eq.symm)

theorem IsMinFam16.barSub_ne_top (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    {X : Type} [Group X] {φ : ↥(CFSG.Quasithin.conjClosure V H) →* X}
    (hφ : SevenK.IsBarMap (CFSG.Quasithin.conjClosure V H) (iSub16 V H) φ) :
    SevenK.barSub (CFSG.Quasithin.conjClosure V H) φ V ≠ ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro htop
  have hI2 : IsPGroup 2 (iSub16 V H) :=
    CFSG.Open.IsElemAbelian.isPGroup (Cex16.isElemAbelian_iSub16 h1 hS h hH.1)
  have hK2 : IsPGroup 2 ↥(CFSG.Quasithin.conjClosure V H) := by
    intro k
    have hk : φ k ∈ SevenK.barSub (CFSG.Quasithin.conjClosure V H) φ V := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨v, hv, hφv⟩ := SevenK.mem_barSub.mp hk
    have hv2 : (v : ↥(CFSG.Quasithin.conjClosure V H)) ^ 2 = 1 := by
      apply Subtype.ext
      simpa using h.hyp.h6.elemAbelian.2 (v : G) hv
    have hφk2 : (φ k) ^ 2 = 1 := by
      rw [← hφv, ← map_pow, hv2, map_one]
    have hk2I : ((k ^ 2 : ↥(CFSG.Quasithin.conjClosure V H)) : G) ∈ iSub16 V H :=
      (hφ.ker_iff (k ^ 2)).mp (by rw [map_pow, hφk2])
    obtain ⟨m, hm⟩ := hI2 ⟨((k ^ 2 : ↥(CFSG.Quasithin.conjClosure V H)) : G), hk2I⟩
    have h2 : ((k ^ 2 : ↥(CFSG.Quasithin.conjClosure V H)) ^ 2 ^ m) = 1 := by
      apply Subtype.ext
      simpa using congrArg Subtype.val hm
    refine ⟨m + 1, ?_⟩
    rw [show (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m by rw [pow_succ, mul_comm]]
    rw [pow_mul]
    exact h2
  have hKH : CFSG.Quasithin.conjClosure V H ≤ H := IsMinFam16.conjClosure_le_H h hH
  have hnorm : H ≤ Subgroup.normalizer (CFSG.Quasithin.conjClosure V H : Set G) :=
    CFSG.Quasithin.le_normalizer_conjClosure V H
  exact hV ((CFSG.Quasithin.le_conjClosure V H).trans
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hKH hnorm hK2))

theorem w16l_traceSpace_ti {X W : Type} [Group X] [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] {ρ : X →* LGL 2 W} {A : Subgroup X} {Z : Submodule (ZMod 2) W}
    (hA : LiftHyp ρ A Z) {t : X} (hAt : A = Subgroup.zpowers t) (hA2 : Nat.card A = 2) :
    traceSpace (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ) t ≠ ⊥ ∧
      ∀ y : X, traceSpace (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ) t ⊓
          (traceSpace (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ) t).map
            ((LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ) y) ≠ ⊥ →
        y * t = t * y := by
  let ρ' : X →* (W →ₗ[ZMod 2] W) := LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ
  change traceSpace ρ' t ≠ ⊥ ∧
    ∀ y : X, traceSpace ρ' t ⊓ (traceSpace ρ' t).map (ρ' y) ≠ ⊥ → y * t = t * y
  have hρ'apply : ∀ y : X, ρ' y = ((ρ y : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) := fun _ => rfl
  have htA : t ∈ A := by rw [hAt]; exact Subgroup.mem_zpowers t
  have ht1 : t ≠ 1 := by
    intro ht
    have h1 : Nat.card A = 1 := by
      rw [hAt, ht, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot]
    omega
  have hTZ : traceSpace ρ' t ≤ Z := by
    intro w hw
    rw [traceSpace, LinearMap.mem_range] at hw
    obtain ⟨v, hv⟩ := hw
    rw [← hv, hρ'apply t]
    exact hA.comm_le t htA v
  have hTne : traceSpace ρ' t ≠ ⊥ := by
    intro hbot
    have hz : ρ' t - 1 = 0 := by
      rw [traceSpace] at hbot
      exact LinearMap.range_eq_bot.mp hbot
    have h1 : ρ' t = 1 := sub_eq_zero.mp hz
    have hfix : ∀ w : W, ρ t w = w := by
      intro w
      have h2 := congrArg (fun f : W →ₗ[ZMod 2] W => f w) h1
      rw [hρ'apply t] at h2
      simpa using h2
    exact ht1 (hA.faithful t htA hfix)
  refine ⟨hTne, ?_⟩
  intro y hy
  have hZne : Z ⊓ Z.map (ρ' y) ≠ ⊥ := by
    intro hbot
    exact hy (le_bot_iff.mp ((inf_le_inf hTZ (Submodule.map_mono hTZ)).trans (le_of_eq hbot)))
  have hZmap : Z.map (ρ' y) = Z := by
    rw [hρ'apply y] at hZne ⊢
    exact hA.ti y hZne
  have hnorm : y ∈ Subgroup.normalizer (A : Set X) := hA.norm y hZmap
  have hconjA : y * t * y⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hnorm t).mp htA
  have hconj_ne : y * t * y⁻¹ ≠ 1 := by
    intro h
    apply ht1
    have h2 := congrArg (fun z => y⁻¹ * z * y) h
    simpa [mul_assoc] using h2
  have hconj_eq : y * t * y⁻¹ = t := by
    refine w16l_eq_of_mem_zpowers_card_two (t := t) ?_ ?_ hconj_ne
    · rw [← hAt]; exact hA2
    · rw [← hAt]; exact hconjA
  have h3 := congrArg (fun z => z * y) hconj_eq
  simpa [mul_assoc] using h3

private theorem w16l_le_fusionOddCore {Y : Type*} [Group Y] {N : Subgroup Y} [N.Normal]
    (hN : Odd (Nat.card N)) : N ≤ fusionOddCore Y :=
  le_sSup ⟨inferInstance, hN⟩

private theorem w16l_odd_fusionOddCore (Y : Type*) [Group Y] [Finite Y] :
    Odd (Nat.card (fusionOddCore Y)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : fusionOddCore Y = CFSG.pPrimeCore 2 Y := by
    unfold fusionOddCore CFSG.pPrimeCore
    congr 1
    ext K
    simp [Nat.coprime_two_left]
  rw [h]
  exact Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := Y))

private theorem w16l_map_conj_normal_subgroupOf {Γ : Type} [Group Γ] {L N : Subgroup Γ}
    (hL : L.Normal) (hNL : N ≤ L) (hN : (N.subgroupOf L).Normal) (γ : Γ) :
    ((N.map (MulAut.conj γ).toMonoidHom).subgroupOf L).Normal := by
  haveI : L.Normal := hL
  have hNnorm : L ≤ Subgroup.normalizer (N : Set Γ) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mp hN
  have hMle : N.map (MulAut.conj γ).toMonoidHom ≤ L := by
    calc N.map (MulAut.conj γ).toMonoidHom ≤ L.map (MulAut.conj γ).toMonoidHom :=
          Subgroup.map_mono hNL
      _ = L := Subgroup.Normal.map_conj_eq L γ
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hMle]
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.mp hx
    have hγ : γ⁻¹ * l * γ ∈ L := by simpa using hL.conj_mem l hl γ⁻¹
    refine Subgroup.mem_map.mpr ⟨(γ⁻¹ * l * γ) * n * (γ⁻¹ * l * γ)⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hNnorm hγ) n).mp hn
    · rw [← hnx]
      change γ * ((γ⁻¹ * l * γ) * n * (γ⁻¹ * l * γ)⁻¹) * γ⁻¹ =
        l * (γ * n * γ⁻¹) * l⁻¹
      group
  · intro hx
    obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.mp hx
    have hγ : γ⁻¹ * l⁻¹ * γ ∈ L := by simpa using hL.conj_mem l⁻¹ (L.inv_mem hl) γ⁻¹
    refine Subgroup.mem_map.mpr ⟨(γ⁻¹ * l⁻¹ * γ) * n * (γ⁻¹ * l⁻¹ * γ)⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hNnorm hγ) n).mp hn
    · have hxx : x = l⁻¹ * (MulAut.conj γ) n * l := by
        have h : (MulAut.conj γ) n = l * x * l⁻¹ := hnx
        rw [h]
        group
      rw [hxx]
      change γ * ((γ⁻¹ * l⁻¹ * γ) * n * (γ⁻¹ * l⁻¹ * γ)⁻¹) * γ⁻¹ =
        l⁻¹ * (γ * n * γ⁻¹) * l
      group

theorem IsMinFam16.exp_class_oddCore (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    {X : Type} [Group X] {φ : ↥(CFSG.Quasithin.conjClosure V H) →* X}
    (hφ : SevenK.IsBarMap (CFSG.Quasithin.conjClosure V H) (iSub16 V H) φ)
    {t : X} (ht2 : t * t = 1)
    (hAt : SevenK.barSub (CFSG.Quasithin.conjClosure V H) φ V = Subgroup.zpowers t)
    (hA2 : Nat.card (SevenK.barSub (CFSG.Quasithin.conjClosure V H) φ V) = 2)
    (hE : Subgroup.zpowers t ⊔ fusionOddCore X = ⊤) (hne : fusionOddCore X ≠ ⊥)
    (hgen : fusionOddCore X ≤ ⁅fusionOddCore X, Subgroup.zpowers t⁆) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ (∀ x ∈ fusionOddCore X, x ^ p = 1) ∧
      ∀ x ∈ fusionOddCore X, ∀ y ∈ fusionOddCore X, ∀ z ∈ fusionOddCore X,
        ⁅⁅x, y⁆, z⁆ = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥(CFSG.Quasithin.conjClosure V H) :=
    Finite.of_injective (Subtype.val : ↥(CFSG.Quasithin.conjClosure V H) → G) Subtype.val_injective
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  have hS_le_H : S ≤ H := hH.1.1
  have hI_le_H : iSub16 V H ≤ H :=
    (Cex16.iSub16_le_pCoreOf h hH.1).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  haveI : ((iSub16 V H).subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hI_le_H]
    exact CFSG.Quasithin.le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H
  let Γ : Type := ↥H ⧸ ((iSub16 V H).subgroupOf H)
  let ψ : ↥H →* Γ := QuotientGroup.mk' ((iSub16 V H).subgroupOf H)
  have hψ_surj : Function.Surjective ψ := QuotientGroup.mk'_surjective _
  have hψker : ∀ j : ↥H, ψ j = 1 ↔ (j : G) ∈ iSub16 V H := by
    intro j
    change (j : Γ) = 1 ↔ (j : G) ∈ iSub16 V H
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  let inclK : ↥(CFSG.Quasithin.conjClosure V H) →* ↥H := IsMinFam16.inclK h hH
  have hcoe : ∀ k : ↥(CFSG.Quasithin.conjClosure V H), ((inclK k : ↥H) : G) = (k : G) :=
    fun k => rfl
  have hker_le : φ.ker ≤ (ψ.comp inclK).ker := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    rw [MonoidHom.comp_apply]
    exact (hψker (inclK k)).mpr (by
      show (k : G) ∈ iSub16 V H
      simpa only [hcoe k] using (hφ.ker_iff k).mp hk)
  let ι : X →* Γ := (φ.liftOfSurjective hφ.surjective) ⟨ψ.comp inclK, hker_le⟩
  have hι : ∀ k : ↥(CFSG.Quasithin.conjClosure V H), ι (φ k) = ψ (inclK k) := fun k =>
    φ.liftOfRightInverse_comp_apply (Function.surjInv hφ.surjective)
      (Function.rightInverse_surjInv hφ.surjective) ⟨ψ.comp inclK, hker_le⟩ k
  have hιinj : Function.Injective ι := by
    intro x1 x2 h
    obtain ⟨k1, rfl⟩ := hφ.surjective x1
    obtain ⟨k2, rfl⟩ := hφ.surjective x2
    have h1 : ψ (inclK k1) = ψ (inclK k2) := by rw [← hι k1, ← hι k2]; exact h
    have h2 : ψ (inclK k1 * (inclK k2)⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    have hmem : ((inclK k1 * (inclK k2)⁻¹ : ↥H) : G) ∈ iSub16 V H := (hψker _).mp h2
    have h3 : φ (k1 * k2⁻¹) = 1 := by
      apply (hφ.ker_iff (k1 * k2⁻¹)).mpr
      show (k1 : G) * (k2 : G)⁻¹ ∈ iSub16 V H
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hcoe k1, hcoe k2] using hmem
    rw [map_mul, map_inv] at h3
    exact eq_of_mul_inv_eq_one h3
  let EΓ : Subgroup Γ := (fusionOddCore X).map ι
  let P : Subgroup Γ := (S.subgroupOf H).map ψ
  have hEΓle : EΓ ≤ ι.range := by
    change (fusionOddCore X).map ι ≤ ι.range
    exact (Subgroup.map_mono le_top).trans (le_of_eq (MonoidHom.range_eq_map ι).symm)
  have hrange_eq : ι.range = ((CFSG.Quasithin.conjClosure V H).subgroupOf H).map ψ := by
    ext γ
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨k, rfl⟩ := hφ.surjective x
      refine Subgroup.mem_map.mpr ⟨inclK k, ?_, (hι k).symm⟩
      rw [Subgroup.mem_subgroupOf]
      exact k.2
    · intro hγ
      obtain ⟨j, hj, hjγ⟩ := Subgroup.mem_map.mp hγ
      rw [Subgroup.mem_subgroupOf] at hj
      refine ⟨φ ⟨(j : G), hj⟩, ?_⟩
      rw [hι]
      rw [show inclK ⟨(j : G), hj⟩ = j from Subtype.ext rfl]
      exact hjγ
  have hKsub_normal : ((CFSG.Quasithin.conjClosure V H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (IsMinFam16.conjClosure_le_H h hH)).mpr
      (CFSG.Quasithin.le_normalizer_conjClosure V H)
  have hLnorm : (ι.range).Normal := by
    rw [hrange_eq]
    exact hKsub_normal.map ψ hψ_surj
  haveI hLnormI : (ι.range).Normal := hLnorm
  have hcardEΓ : Nat.card EΓ = Nat.card (fusionOddCore X) := by
    change Nat.card ((fusionOddCore X).map ι) = Nat.card (fusionOddCore X)
    exact Subgroup.card_map_of_injective hιinj
  have hodd_EΓ : Odd (Nat.card EΓ) := by
    rw [hcardEΓ]
    exact w16l_odd_fusionOddCore X
  have hSsub2 : IsPGroup 2 (S.subgroupOf H) :=
    (h.sylow.isPGroup).of_equiv (Subgroup.subgroupOfEquivOfLe hS_le_H).symm
  have hP2 : IsPGroup 2 P := by
    change IsPGroup 2 ((S.subgroupOf H).map ψ)
    exact IsPGroup.map hSsub2 ψ
  have hEΓL : (EΓ.subgroupOf (ι.range)).Normal := by
    have hmap : (fusionOddCore X).map (MonoidHom.rangeRestrict ι) =
        EΓ.subgroupOf (ι.range) := by
      change (fusionOddCore X).map (MonoidHom.rangeRestrict ι) =
        ((fusionOddCore X).map ι).subgroupOf (ι.range)
      ext γ
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      · intro h1
        rw [Subgroup.mem_subgroupOf] at h1
        obtain ⟨x, hx, hxγ⟩ := Subgroup.mem_map.mp h1
        exact ⟨x, hx, Subtype.ext hxγ⟩
    rw [← hmap]
    exact (inferInstance : (fusionOddCore X).Normal).map (MonoidHom.rangeRestrict ι)
      (MonoidHom.rangeRestrict_surjective ι)
  have hconj_le : ∀ δ : Γ, EΓ.map (MulAut.conj δ).toMonoidHom ≤ EΓ := by
    intro γ
    let M : Subgroup Γ := EΓ.map (MulAut.conj γ).toMonoidHom
    let E' : Subgroup X := M.comap ι
    have hMle : M ≤ ι.range := by
      calc M ≤ (ι.range).map (MulAut.conj γ).toMonoidHom := Subgroup.map_mono hEΓle
        _ = ι.range := Subgroup.Normal.map_conj_eq (ι.range) γ
    have hE'map : E'.map ι = M := Subgroup.map_comap_eq_self hMle
    have hE'norm : E'.Normal := by
      have hsub : (M.subgroupOf (ι.range)).Normal :=
        w16l_map_conj_normal_subgroupOf hLnorm hEΓle hEΓL γ
      have hcomap : (M.subgroupOf (ι.range)).comap (MonoidHom.rangeRestrict ι) = E' := by
        ext x; rfl
      rw [← hcomap]
      exact hsub.comap _
    haveI : E'.Normal := hE'norm
    have hE'odd : Odd (Nat.card E') := by
      have hc1 : Nat.card E' = Nat.card M := by
        rw [← Subgroup.card_map_of_injective (K := E') (f := ι) hιinj, hE'map]
      have hc2 : Nat.card M = Nat.card EΓ :=
        Subgroup.card_map_of_injective (MulAut.conj γ).injective
      have hc3 : Nat.card EΓ = Nat.card (fusionOddCore X) := by
        change Nat.card ((fusionOddCore X).map ι) = Nat.card (fusionOddCore X)
        exact Subgroup.card_map_of_injective hιinj
      rw [hc1, hc2, hc3]
      exact w16l_odd_fusionOddCore X
    have hE'le : E' ≤ fusionOddCore X := w16l_le_fusionOddCore hE'odd
    calc M = E'.map ι := hE'map.symm
      _ ≤ (fusionOddCore X).map ι := Subgroup.map_mono hE'le
      _ = EΓ := rfl
  have hEΓnorm : EΓ.Normal := by
    rw [Subgroup.normal_iff_map_conj_eq]
    intro γ
    refine le_antisymm (hconj_le γ) ?_
    intro x hx
    have hx' : (MulAut.conj γ)⁻¹ x ∈ EΓ := by
      have hγinv : (MulAut.conj γ)⁻¹ = MulAut.conj γ⁻¹ := (map_inv (MulAut.conj) γ).symm
      rw [hγinv]
      exact hconj_le γ⁻¹ (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    exact Subgroup.mem_map.mpr ⟨(MulAut.conj γ)⁻¹ x, hx',
      MulAut.apply_inv_self Γ (MulAut.conj γ) x⟩
  have hEΓP : EΓ ⊓ P = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hdvd : orderOf x ∣ Nat.card EΓ := Subgroup.orderOf_dvd_natCard EΓ hx.1
    have hodd_ord : Odd (orderOf x) := hodd_EΓ.of_dvd_nat hdvd
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hP2) ⟨x, hx.2⟩
    have hm' : orderOf x = 2 ^ m := (orderOf_mk x hx.2).symm.trans hm
    have hodd2 : Odd (2 ^ m) := by rw [← hm']; exact hodd_ord
    have hm0 : m = 0 := by
      by_contra h0
      exact (Nat.not_even_iff_odd.mpr hodd2)
        (Even.pow_of_ne_zero (show Even (2 : ℕ) by norm_num) h0)
    rw [hm0, pow_zero] at hm'
    exact orderOf_eq_one_iff.mp hm'
  have hEΓne : EΓ ≠ ⊥ := by
    intro hbot
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have hxΓ : ι x ∈ EΓ := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hbot] at hxΓ
    exact hιinj (by rw [Subgroup.mem_bot.mp hxΓ, map_one])
  have hEΓgen : EΓ ≤ ⁅EΓ, Subgroup.zpowers (ι t)⁆ := by
    have h2 : (fusionOddCore X).map ι ≤
        (⁅fusionOddCore X, Subgroup.zpowers t⁆).map ι := Subgroup.map_mono hgen
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers] at h2
    exact h2
  have hEY_repr : ∀ y ∈ EΓ, ∃ k : ↥(CFSG.Quasithin.conjClosure V H), ψ (inclK k) = y := by
    intro y hy
    obtain ⟨e, -, heq⟩ :=
      Subgroup.mem_map.mp (show y ∈ (fusionOddCore X).map ι from hy)
    obtain ⟨k, hk⟩ := hφ.surjective e
    exact ⟨k, by rw [← hι k, hk, heq]⟩
  have ht1 : t ≠ 1 := by
    intro ht
    have h1 : Nat.card (SevenK.barSub (CFSG.Quasithin.conjClosure V H) φ V) = 1 := by
      rw [hAt, ht, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot]
    omega
  have hmin : ∀ Y : Subgroup Γ, Y ≤ EΓ → Y ≠ EΓ →
      P ≤ Subgroup.normalizer (Y : Set Γ) → ∀ y ∈ Y, ι t * y = y * ι t := by
    intro Y hYle hYne hPnorm y hyY
    have hHY_le_H : ((P ⊔ Y).comap ψ).map H.subtype ≤ H :=
      Subgroup.map_subtype_le ((P ⊔ Y).comap ψ)
    have hS_le_HY : S ≤ ((P ⊔ Y).comap ψ).map H.subtype := by
      intro s hs
      refine Subgroup.mem_map.mpr ⟨⟨s, hS_le_H hs⟩, ?_, rfl⟩
      rw [Subgroup.mem_comap]
      exact Subgroup.mem_sup_left (Subgroup.mem_map.mpr ⟨⟨s, hS_le_H hs⟩, hs, rfl⟩)
    have hHY_le_CU : ((P ⊔ Y).comap ψ).map H.subtype ≤ centralizer (U : Set G) :=
      fun x hx => hH.1.2.1 (hHY_le_H hx)
    by_cases hHYM : ((P ⊔ Y).comap ψ).map H.subtype ≤ M
    · obtain ⟨k, hk⟩ := hEY_repr y (hYle hyY)
      have htA : t ∈ SevenK.barSub (CFSG.Quasithin.conjClosure V H) φ V := by
        rw [hAt]; exact Subgroup.mem_zpowers t
      obtain ⟨v, hvV, hφv⟩ := SevenK.mem_barSub.mp htA
      have hjHY : ((inclK k : ↥H) : G) ∈ ((P ⊔ Y).comap ψ).map H.subtype := by
        refine Subgroup.mem_map.mpr ⟨inclK k, ?_, rfl⟩
        rw [Subgroup.mem_comap]
        show ψ (inclK k) ∈ P ⊔ Y
        rw [hk]
        exact Subgroup.mem_sup_right hyY
      have hjM : ((inclK k : ↥H) : G) ∈ M := hHYM hjHY
      have hjNorm : ((inclK k : ↥H) : G) ∈ Subgroup.normalizer (V : Set G) := by
        rw [h.hyp.h6.normalizer_eq]
        exact hjM
      have hv_conj : ((inclK k : ↥H) : G) * (v : G) * ((inclK k : ↥H) : G)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp hjNorm (v : G)).mp hvV
      have hv_conj' : (k : G) * (v : G) * (k : G)⁻¹ ∈ V := by
        rw [hcoe k] at hv_conj
        exact hv_conj
      have hφx'A : φ (k * v * k⁻¹) ∈
          SevenK.barSub (CFSG.Quasithin.conjClosure V H) φ V := by
        refine SevenK.mem_barSub.mpr ⟨k * v * k⁻¹, ?_, rfl⟩
        simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hv_conj'
      have hconj_eq : y * ι t * y⁻¹ = ι (φ (k * v * k⁻¹)) := by
        have hkey : (inclK k) * (inclK v) * (inclK k)⁻¹ = inclK (k * v * k⁻¹) := by
          rw [map_mul, map_mul, map_inv]
        calc y * ι t * y⁻¹
            = ψ (inclK k) * ψ (inclK v) * (ψ (inclK k))⁻¹ := by
              rw [← hk, ← hφv, hι v]
          _ = ψ ((inclK k) * (inclK v) * (inclK k)⁻¹) := by rw [map_mul, map_mul, map_inv]
          _ = ψ (inclK (k * v * k⁻¹)) := by rw [hkey]
          _ = ι (φ (k * v * k⁻¹)) := (hι (k * v * k⁻¹)).symm
      have hAΓ : (SevenK.barSub (CFSG.Quasithin.conjClosure V H) φ V).map ι =
          Subgroup.zpowers (ι t) := by
        rw [hAt, MonoidHom.map_zpowers]
      have hmem : y * ι t * y⁻¹ ∈ Subgroup.zpowers (ι t) := by
        rw [hconj_eq]
        exact hAΓ ▸ Subgroup.mem_map.mpr ⟨φ (k * v * k⁻¹), hφx'A, rfl⟩
      have hcardz : Nat.card (Subgroup.zpowers (ι t)) = 2 := by
        rw [← hAΓ, Subgroup.card_map_of_injective hιinj, hA2]
      have htΓ_ne : ι t ≠ 1 := fun h1 => ht1 (hιinj (by rw [h1, map_one]))
      have hconj_ne : y * ι t * y⁻¹ ≠ 1 := by
        intro h1
        apply htΓ_ne
        have h2 := congrArg (fun z => y⁻¹ * z * y) h1
        simpa [mul_assoc] using h2
      have hconj_eq_t : y * ι t * y⁻¹ = ι t :=
        w16l_eq_of_mem_zpowers_card_two hcardz hmem hconj_ne
      calc ι t * y = (y * ι t * y⁻¹) * y := by rw [hconj_eq_t]
        _ = y * ι t := by group
    · exfalso
      have hHY : ((P ⊔ Y).comap ψ).map H.subtype = H :=
        hH.2 _ hHY_le_H ⟨hS_le_HY, hHY_le_CU, hHYM⟩
      have hcomap : (P ⊔ Y).comap ψ = ⊤ := by
        rw [eq_top_iff]
        intro j _
        have hj : (j : G) ∈ ((P ⊔ Y).comap ψ).map H.subtype := by
          rw [hHY]
          exact j.2
        obtain ⟨j', hj', hj'eq⟩ := Subgroup.mem_map.mp hj
        have hjj : j' = j := Subtype.ext hj'eq
        rwa [hjj] at hj'
      have hsup : P ⊔ Y = ⊤ := by
        have h1 : ((P ⊔ Y).comap ψ).map ψ = ⊤ := by
          rw [hcomap, Subgroup.map_top_of_surjective ψ hψ_surj]
        rwa [Subgroup.map_comap_eq_self_of_surjective hψ_surj] at h1
      have hEY : EΓ ≤ Y := by
        intro e he
        have hePY : e ∈ (P ⊔ Y : Subgroup Γ) := by rw [hsup]; exact Subgroup.mem_top e
        rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right P Y hPnorm] at hePY
        obtain ⟨p, hpP, y', hy'Y, hpy⟩ := hePY
        have hp_eq : p = e * y'⁻¹ := by rw [← hpy]; group
        have hpE : p ∈ EΓ := by
          rw [hp_eq]
          exact EΓ.mul_mem he (EΓ.inv_mem (hYle hy'Y))
        have hpbot : p ∈ EΓ ⊓ P := ⟨hpE, hpP⟩
        rw [hEΓP] at hpbot
        have hp1 : p = 1 := Subgroup.mem_bot.mp hpbot
        have heY : e ∈ Y := by
          rw [← hpy, hp1]
          change (1 : Γ) * y' ∈ Y
          rw [one_mul]
          exact hy'Y
        exact heY
      exact hYne (le_antisymm hYle hEY)
  haveI : Finite Γ := Finite.of_surjective ψ hψ_surj
  haveI : EΓ.Normal := hEΓnorm
  have htΓ2 : ι t * ι t = 1 := by rw [← map_mul, ht2, map_one]
  obtain ⟨p, hpp, hp2, -, hexp, hclass⟩ :=
    w162_exp_class_of_min (Γ := Γ) (N := EΓ) (P := P) hodd_EΓ hP2 htΓ2 hEΓne hEΓgen hmin
  refine ⟨p, hpp, hp2, ?_, ?_⟩
  · intro x hx
    have hxΓ : ι x ∈ EΓ := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have h1 : (ι x) ^ p = 1 := hexp (ι x) hxΓ
    have h2 : ι (x ^ p) = 1 := by rw [map_pow]; exact h1
    exact hιinj (by rw [h2, map_one])
  · intro x hx y hy z hz
    have hxΓ : ι x ∈ EΓ := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have hyΓ : ι y ∈ EΓ := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    have hzΓ : ι z ∈ EΓ := Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
    have h1 := hclass (ι x) hxΓ (ι y) hyΓ (ι z) hzΓ
    have h2 : ι ⁅⁅x, y⁆, z⁆ = 1 := by
      rw [map_commutatorElement, map_commutatorElement]
      exact h1
    exact hιinj (by rw [h2, map_one])

end CFSG.LocalAnalysis.WeakClosure81

end
