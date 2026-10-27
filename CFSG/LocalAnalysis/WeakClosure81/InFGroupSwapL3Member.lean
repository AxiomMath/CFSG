module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
import CFSG.LocalAnalysis.WeakClosure81.InFGroupNormalPerfect
import CFSG.LocalAnalysis.WeakClosure81.InFGroupNormalPSLRank
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Bridge
import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Iso
import CFSG.Quasithin.Background.C126NatSL2
public import CFSG.Quasithin.Vol2.Ch11SecOE8P
public import CFSG.Quasithin.Vol2.Ch11SecOE8Q
public import CFSG.Quasithin.Vol2.Ch11SecOE8S

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SwapL3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.QuasithinUnique.Fin257.L3 CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.Vol2.Ch11 CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
  CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.L3T
open CFSG.Quasithin.Vol2.Ch11.SecE3 (AlmostSimple)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (InCalEi ECaseII tA)
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem isPSL_two_of_mulEquiv_sl2 {X : Type} [Group X] {F : Type} [Field F] [Finite F]
    [CharP F 2] {n : ℕ} (e : X ≃* SL(2, F)) (hF : Nat.card F = 2 ^ n) (hF4 : 4 ≤ Nat.card F) :
    IsPSL 2 2 n X := by
  have hs : ∃ s : Finset F, s.card = 4 := exists_finset_card_four hF4
  have : IsSimpleGroup SL(2, F) := E1.RootLift.isSimpleGroup_SL2 hF4
  have : Group.IsPerfect SL(2, F) := CFSG.LinearGroups.special_linear_dimension_two_perfect hs
  have : Group.IsPerfect X :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have : Nontrivial X := e.toEquiv.nontrivial
  exact CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0)
    (CFSG.Quasithin.H13.lieModel_psl_two_of_mulEquiv inferInstance hF
      (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F)))

theorem inCalEi_sup_tA_of_quot_sl2 {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {T A X : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hAT : A ≤ T) (hA : IsElemAbelian 2 A)
    (φ : ↥X →* SL(2, F)) (hφ : Function.Surjective φ) (hker : IsPGroup 2 φ.ker)
    (hF : Nat.card F = 2 ^ n) (hF4 : 4 ≤ Nat.card F) (hXperf : ⁅X, X⁆ = X)
    (hτN : tA T A ≤ Subgroup.normalizer (X : Set G)) (hL : IsSylowIn 2 (T ⊓ X) X)
    (hAC : ¬ ∀ a ∈ A, ∀ x ∈ X, ⁅a, x⁆ ∈ φ.ker.map X.subtype) :
    InCalEi n T A (X ⊔ tA T A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup SL(2, F) := E1.RootLift.isSimpleGroup_SL2 hF4
  set τ := tA T A with hτdef
  have hτT : τ ≤ T := E1.tauOf_le _ _ _
  set K := X ⊔ τ with hKdef
  have hXK : X ≤ K := le_sup_left
  have hτK : τ ≤ K := le_sup_right
  have hKN : K ≤ Subgroup.normalizer (X : Set G) := sup_le Subgroup.le_normalizer hτN
  have hJn : (X.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXK).mpr hKN
  have hAK : A ≤ K := (le_tA_of_isElemAbelian hAT hA).trans hτK
  have hkerO : φ.ker = CFSG.pCore 2 ↥X := ker_eq_pCore φ hφ hker hF4
  let e : ModO2 X ≃* SL(2, F) :=
    (QuotientGroup.quotientMulEquivOfEq hkerO.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  have hJs : IsSimpleGroup (ModO2 X) := e.isSimpleGroup
  have hJnab : ∃ a b : ModO2 X, a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := SecE3.sl2_nonabelian (K := F)
    exact ⟨e.symm x, e.symm y, fun h => hxy (e.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have hJpsl : IsPSL 2 2 n (ModO2 X) := isPSL_two_of_mulEquiv_sl2 e hF hF4
  have hK2 : ∀ x ∈ K, ∃ k : ℕ, x ^ 2 ^ k ∈ X := by
    have : (X.subgroupOf K).Normal := hJn
    have hτ' : IsPGroup 2 ↥(τ.subgroupOf K) :=
      (hT.2.1.to_le hτT).comap_of_injective K.subtype K.subtype_injective
    have hsup : X.subgroupOf K ⊔ τ.subgroupOf K = ⊤ :=
      (Subgroup.codisjoint_subgroupOf_sup X τ).eq_top
    have htwo : ∀ q : ↥K, ∃ k : ℕ, q ^ 2 ^ k ∈ X.subgroupOf K := fun q => by
      have hq : q ∈ X.subgroupOf K ⊔ τ.subgroupOf K := hsup ▸ Subgroup.mem_top q
      obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hq
      obtain ⟨k, hk⟩ := hτ' ⟨z, hz⟩
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
        (QuotientGroup.eq_one_iff y).mpr hy, one_mul, ← QuotientGroup.mk_pow,
        show z ^ 2 ^ k = 1 by simpa using congrArg Subtype.val hk, QuotientGroup.mk_one]
    intro x hx
    obtain ⟨k, hk⟩ := htwo ⟨x, hx⟩
    exact ⟨k, by simpa [Subgroup.mem_subgroupOf] using hk⟩
  have hpX : φ.ker.map X.subtype = pCoreOf 2 X := by rw [hkerO]; rfl
  have hAJ : ∃ a ∈ A, ∃ x ∈ X, ⁅a, x⁆ ∉ pCoreOf 2 X := by
    by_contra hc
    push Not at hc
    exact hAC fun a ha x hx => hpX ▸ hc a ha x hx
  have hEII : ECaseII T A K := eCaseII_of_normal_perfect hXK hJn hXperf hJs hK2 hAK hAJ
  have hm : E3.mQuot A (pCoreOf 2 K) ≤ n :=
    mQuot_pCoreOf_le_of_normal_psl hXK hJn hJs hJnab hJpsl hK2 hAK hA
  have hSyl : IsSylowIn 2 (T ⊓ K) K := SecU1.Comp.isSylowIn_sup hT.2.1 hτT hτN hL
  have hnot : ¬ A ≤ pCoreOf 2 K := by
    intro hAO
    obtain ⟨a, ha, x, hx, hne⟩ := hAJ
    apply hne
    have haK : a ∈ K := hAK ha
    have hxK : x ∈ K := hXK hx
    have hKO : K ≤ Subgroup.normalizer ((pCoreOf 2 K : Subgroup G) : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
    have h1 : ⁅a, x⁆ ∈ pCoreOf 2 K := by
      rw [commutatorElement_def, mul_assoc, mul_assoc]
      refine (pCoreOf 2 K).mul_mem (hAO ha) ?_
      have hconj := (Subgroup.mem_normalizer_iff.mp (hKO hxK) a⁻¹).mp
        ((pCoreOf 2 K).inv_mem (hAO ha))
      simpa [mul_assoc] using hconj
    have h2 : ⁅a, x⁆ ∈ X := by
      rw [commutatorElement_def]
      exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKN haK) x).mp hx) (X.inv_mem hx)
    have hle : pCoreOf 2 K ⊓ X ≤ pCoreOf 2 X :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
        ((le_inf (hXK.trans hKO) Subgroup.le_normalizer).trans
          Subgroup.inf_normalizer_le_normalizer_inf)
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le inf_le_left)
    exact hle ⟨h1, h2⟩
  exact ⟨⟨le_inf hτT hτK, CFSG.ABGLocalTools.isSylowOf_iff.mpr hSyl, hnot, Or.inr hEII⟩, hm⟩

theorem inCalEi_of_twisted {L T A : Subgroup G} [hLn : L.Normal] (h : AlmostSimple L)
    (hT : IsSylowIn 2 T ⊤) {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) (e : ↥L ≃* projectiveSL 3 K)
    (he : ((T ⊓ L).subgroupOf L).map e.toMonoidHom = projUnitriangular 3 K)
    (hAT : A ≤ T) (hA : IsElemAbelian 2 A) (hcard : 2 ^ n < Nat.card A) {t : G} (htT : t ∈ T)
    (htA : ∀ a ∈ A, t * a = a * t) (htE : actHom e t ∉ semilinearAutGroup 3 K) :
    ∃ L₀ : Subgroup G, L₀ ≤ L ∧ ¬ Group.IsSolvable ↥L₀ ∧ InCalEi n T A (L₀ ⊔ tA T A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hK4' : ∃ s : Finset K, s.card = 4 := exists_finset_card_four hK4
  set ψ := actHom e with hψdef
  have hψ : Function.Injective ψ := actHom_injective e h.centralizer_eq
  set ι : projectiveSL 3 K →* G := L.subtype.comp e.symm.toMonoidHom with hιdef
  have hι : Function.Injective ι := L.subtype_injective.comp e.symm.injective
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set E := A.map ψ with hEdef
  have h2 : ∀ α ∈ E, α * α = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← pow_two, hA.2 a ha, map_one]
  have hc : ∀ α ∈ E, ∀ β ∈ E, α * β = β * α := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hAc a ha b hb]
  have hU : ∀ α ∈ E, ∀ u ∈ projUnitriangular 3 K, α u ∈ projUnitriangular 3 K := by
    rintro _ ⟨a, ha, rfl⟩ u hu
    exact actHom_mem_U e he (hAT ha) u hu
  have hcardE : Nat.card K < Nat.card E := by
    rw [hEdef, Subgroup.card_map_of_injective hψ, hK]
    exact hcard
  have hθc : ∀ α ∈ E, ψ t * α = α * ψ t := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, htA a ha]
  obtain ⟨hBW, hB1, a', ha'E, ha'Es, ha'fix⟩ :=
    twisted_case hn hK E h2 hc hU htE (actHom_mem_U e he htT) hθc hcardE
  obtain ⟨a₁, ha₁A, rfl⟩ := ha'E
  obtain ⟨j, hj, hjr⟩ := exists_SL_two_fixed_of_twisted (by omega : 1 ≤ n) hK
    (h2 _ ⟨a₁, ha₁A, rfl⟩) ha'Es ha'fix
  set F₀ := fixedSubgroup (ψ a₁) with hF₀
  set L₀ := F₀.map ι with hL₀
  have hL₀r : L₀ = (ι.comp j).range := by rw [hL₀, ← hjr, MonoidHom.range_comp]
  have eL : ↥L₀ ≃* SL(2, K) :=
    ((MonoidHom.ofInjective (f := ι.comp j) (hι.comp hj)).trans
      (MulEquiv.subgroupCongr hL₀r.symm)).symm
  have hL₀L : L₀ ≤ L := by
    rintro _ ⟨p, -, rfl⟩
    exact (e.symm p).2
  have hL₀s : ¬ Group.IsSolvable ↥L₀ := fun hs => SzN2.not_isSolvable_sl2 hK4'
    (Group.isSolvable_of_isSolvable_injective (f := eL.symm.toMonoidHom) eL.symm.injective)
  have hτN : E1.tauOf ⊤ T A ≤ Subgroup.normalizer (L₀ : Set G) := by
    intro τ hτm
    have hτa : τ * a₁ = a₁ * τ :=
      Subgroup.mem_centralizer_singleton_iff.mp (tauOf_le_centralizer h ha₁A hτm)
    have hcomm : ψ τ * ψ a₁ = ψ a₁ * ψ τ := by rw [← map_mul, ← map_mul, hτa]
    apply mem_normalizer_map_iota e
    refine Subgroup.eq_of_le_of_card_ge ?_ (Subgroup.card_map_of_injective (ψ τ).injective).ge
    rintro _ ⟨x, hx, rfl⟩
    have hx' : ψ a₁ x = x := hx
    change ψ a₁ (ψ τ x) = ψ τ x
    rw [← MulAut.mul_apply, ← hcomm, MulAut.mul_apply, hx']
  have hTL : (projUnitriangular 3 K).map ι = T ⊓ L := by
    rw [← he, Subgroup.map_map]
    have hcomp : ι.comp e.toMonoidHom = L.subtype := by
      ext x
      simp [hιdef]
    rw [hcomp, Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem]
  have hWF : (Wg : Subgroup (projectiveSL 3 K)) ≤ F₀ := fun g hg => ha'fix g hg
  have hZT : (Wg : Subgroup (projectiveSL 3 K)).map ι ≤ T ⊓ L₀ := by
    refine le_inf ?_ (Subgroup.map_mono hWF)
    have : (Wg : Subgroup (projectiveSL 3 K)).map ι ≤ T ⊓ L := by
      rw [← hTL]
      exact Subgroup.map_mono (Wg_le_V1.trans V1_le_U)
    exact this.trans inf_le_left
  have hL : IsSylowIn 2 (T ⊓ L₀) L₀ := by
    refine ⟨inf_le_right, hT.2.1.to_le inf_le_left, fun h2r => ?_⟩
    have hmul := Subgroup.relIndex_mul_card (H := T ⊓ L₀) (K := L₀)
    rw [inf_of_le_left inf_le_right] at hmul
    obtain ⟨s, hs⟩ := Subgroup.card_dvd_of_le hZT
    rw [Subgroup.card_map_of_injective hι, card_Wg] at hs
    have hL₀c : Nat.card L₀ = Nat.card K * (Nat.card K ^ 2 - 1) := by
      rw [Nat.card_congr eL.toEquiv, card_SL_two]
    rw [hs, hL₀c] at hmul
    have hKpos : 0 < Nat.card K := Nat.card_pos
    have hrs : (T ⊓ L₀).relIndex L₀ * s = Nat.card K ^ 2 - 1 := by
      apply Nat.eq_of_mul_eq_mul_left hKpos
      rw [← hmul]
      ring
    have hev : Even (Nat.card K ^ 2) := by
      rw [hK, ← pow_mul]
      exact (Nat.even_pow' (by omega)).mpr even_two
    have hodd : Odd (Nat.card K ^ 2 - 1) :=
      Nat.Even.sub_odd (Nat.one_le_iff_ne_zero.mpr (by positivity)) hev odd_one
    rw [← hrs] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2r.mul_right s))
  have hAC : ¬ A ≤ Subgroup.centralizer (L₀ : Set G) := by
    intro hAC'
    obtain ⟨⟨u, huB⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp hB1)
    have hu1' : u ≠ 1 := fun h1 => hu1 (Subtype.ext h1)
    have huA : ι u ∈ A := by
      obtain ⟨a, ha, hau⟩ := huB
      rw [eq_iota_of_actHom_eq e h.centralizer_eq hau] at ha
      exact ha
    have huL₀ : ι u ∈ L₀ := ⟨u, hWF (hBW huB), rfl⟩
    have : IsSimpleGroup SL(2, K) := E1.RootLift.isSimpleGroup_SL2 hK4
    have hZ := SecE3.center_eq_bot_of_simple (SecE3.sl2_nonabelian (K := K))
    have hcen : eL ⟨ι u, huL₀⟩ ∈ Subgroup.center SL(2, K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y, rfl⟩ := eL.surjective y
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp (hAC' huA) y y.2)
    rw [hZ, Subgroup.mem_bot, map_eq_one_iff _ eL.injective] at hcen
    apply hu1'
    apply hι
    rw [map_one]
    exact congrArg Subtype.val hcen
  have hkerL : IsPGroup 2 eL.toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr eL.injective]
    exact IsPGroup.of_bot
  have hperf : ⁅L₀, L₀⁆ = L₀ := CFSG.Quasithin.C126.Nat.commutator_eq_of_equiv_sl2 hK4 eL
  refine ⟨L₀, hL₀L, hL₀s, inCalEi_sup_tA_of_quot_sl2 hT hAT hA eL.toMonoidHom eL.surjective
    hkerL hK hK4 hperf hτN hL fun hall => hAC fun a ha => ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h1 := hall a ha x hx
  rw [(MonoidHom.ker_eq_bot_iff _).mpr eL.injective, Subgroup.map_bot, Subgroup.mem_bot,
    commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

theorem inCalEi_of_semilinear {L T A : Subgroup G} [hLn : L.Normal] (h : AlmostSimple L)
    (hT : IsSylowIn 2 T ⊤) {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) (e : ↥L ≃* projectiveSL 3 K)
    (he : ((T ⊓ L).subgroupOf L).map e.toMonoidHom = projUnitriangular 3 K)
    (hAT : A ≤ T) (hA : IsElemAbelian 2 A) (hcard : 2 ^ n < Nat.card A)
    (hsemi : ∀ t ∈ T, (∀ a ∈ A, t * a = a * t) → actHom e t ∈ semilinearAutGroup 3 K) :
    ∃ X : Subgroup G, X ≤ L ∧ ¬ Group.IsSolvable ↥X ∧ InCalEi n T A (X ⊔ tA T A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hK4' : ∃ s : Finset K, s.card = 4 := exists_finset_card_four hK4
  set ψ := actHom e with hψdef
  have hψ : Function.Injective ψ := actHom_injective e h.centralizer_eq
  set ι : projectiveSL 3 K →* G := L.subtype.comp e.symm.toMonoidHom with hιdef
  have hι : Function.Injective ι := L.subtype_injective.comp e.symm.injective
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set E := A.map ψ with hEdef
  have h2 : ∀ α ∈ E, α * α = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← pow_two, hA.2 a ha, map_one]
  have hc : ∀ α ∈ E, ∀ β ∈ E, α * β = β * α := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hAc a ha b hb]
  have hU : ∀ α ∈ E, ∀ u ∈ projUnitriangular 3 K, α u ∈ projUnitriangular 3 K := by
    rintro _ ⟨a, ha, rfl⟩ u hu
    exact actHom_mem_U e he (hAT ha) u hu
  have hEs : E ≤ semilinearAutGroup 3 K := by
    rintro _ ⟨a, ha, rfl⟩
    exact hsemi a (hAT ha) fun b hb => hAc a ha b hb
  have hcardE : Nat.card K < Nat.card E := by
    rw [hEdef, Subgroup.card_map_of_injective hψ, hK]
    exact hcard
  obtain ⟨u, hu, huW, hV⟩ := exists_inner_V_of_le_semilinear hn hK E h2 hc hU hEs hcardE
  have huA : ι u ∈ A := by
    obtain ⟨a, ha, hau⟩ := hu
    rw [eq_iota_of_actHom_eq e h.centralizer_eq hau] at ha
    exact ha
  have hτ : ∀ τ ∈ E1.tauOf ⊤ T A, τ ∈ T ∧ ψ τ ∈ semilinearAutGroup 3 K := by
    intro τ hτm
    have hτT := E1.tauOf_le _ _ _ hτm
    refine ⟨hτT, hsemi τ hτT fun a ha => ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (tauOf_le_centralizer h ha hτm)
  have hTL : (projUnitriangular 3 K).map ι = T ⊓ L := by
    rw [← he, Subgroup.map_map]
    have hcomp : ι.comp e.toMonoidHom = L.subtype := by
      ext x
      simp [hιdef]
    rw [hcomp, Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem]
  have hTLs : IsSylowTwoOf (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal (⟨hT.1, hT.2.1, hT.2.2⟩ : IsSylowTwoOf T ⊤) le_top
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hLn])
  have pkg₀ := Rk2.rank2Pkg_proj3 hK hn
  have key : ∀ (j : Fin 2) (x₀ : SL(3, K)) (hx₀ : x₀ ∈ perfectCore (Q3 K j)),
      ι (proj 3 K x₀) ∈ A → blk3 j ⟨x₀, hx₀⟩ ≠ 1 →
        ∃ X : Subgroup G, X ≤ L ∧ ¬ Group.IsSolvable ↥X ∧
          InCalEi n T A (X ⊔ tA T A) := by
    intro j x₀ hx₀ hA₀ hb
    set X := (perfectCore ((Q3 K j).map (proj 3 K))).map ι with hX
    obtain ⟨φ, hφs, hφk, hφv⟩ := exists_levi_iota hK hn ι hι j
    have hx₀X : ι (proj 3 K x₀) ∈ X :=
      ⟨proj 3 K x₀, by rw [← map_perfectCore]; exact ⟨x₀, hx₀, rfl⟩, rfl⟩
    have hXL : X ≤ L := by
      rintro _ ⟨p, -, rfl⟩
      exact (e.symm p).2
    have hXs : ¬ Group.IsSolvable ↥X := fun hs =>
      SzN2.not_isSolvable_sl2 hK4' (Group.isSolvable_of_surjective hφs)
    have hτN : E1.tauOf ⊤ T A ≤ Subgroup.normalizer (X : Set G) := by
      intro τ hτm
      obtain ⟨hτT, hτs⟩ := hτ τ hτm
      apply mem_normalizer_map_iota e
      rw [map_perfectCore, map_Q3_of_mem_semilinear hτs (actHom_mem_U e he hτT) j]
    have hL : IsSylowIn 2 (T ⊓ X) X := by
      set Pj := ((Q3 K j).map (proj 3 K)).map ι with hPj
      have hUP : T ⊓ L ≤ Pj := by
        rw [← hTL]
        exact Subgroup.map_mono (pkg₀.res.2.1 j)
      have hPL : Pj ≤ L := by
        rintro _ ⟨p, -, rfl⟩
        exact (e.symm p).2
      have h1 := B6.isSylowTwoOf_mono hTLs hUP hPL
      have hXP : X ≤ Pj := Subgroup.map_mono (perfectCore_le _)
      have hPN : Pj ≤ Subgroup.normalizer (X : Set G) := by
        rintro _ ⟨p, hp, rfl⟩
        have hpn : p ∈ Subgroup.normalizer
            ((perfectCore ((Q3 K j).map (proj 3 K)) : Subgroup (projectiveSL 3 K)) :
              Set (projectiveSL 3 K)) :=
          normalizer_le_normalizer_perfectCore _ (Subgroup.le_normalizer hp)
        apply mem_normalizer_map_iota e
        rw [show ι p = ((e.symm p : ↥L) : G) from rfl, actHom_of_mem e (e.symm p).2]
        simp only [Subtype.coe_eta, MulEquiv.apply_symm_apply]
        exact A1b.conjSub_eq_iff_mem_normalizer.mpr hpn
      have h2 := B6.isSylowTwoOf_inf_normal h1 hXP hPN
      rw [inf_assoc, inf_eq_right.mpr hXL] at h2
      exact ⟨h2.1, h2.2.1, h2.2.2⟩
    have hAC := not_forall_commutator_mem_ker hK4 φ hφs hA₀ hx₀X
      (by rw [hφv x₀ hx₀ hx₀X]; exact hb)
    have hperf : ⁅X, X⁆ = X := by
      rw [hX, ← Subgroup.map_commutator, perfectCore_perfect]
    exact ⟨X, hXL, hXs, inCalEi_sup_tA_of_quot_sl2 hT hAT hA φ hφs hφk hK hK4 hperf hτN hL hAC⟩
  rcases hV with hV1 | hV2
  · obtain ⟨a₀, c, rfl⟩ := mem_V1.mp hV1
    have ha₀ : a₀ ≠ 0 := fun h0 => huW ⟨c, by rw [h0, xP_zero, one_mul]⟩
    refine key 1 (xMat a₀ * wMat c) (xMat_mul_wMat_mem hK4' a₀ c) (by rw [map_mul]; exact huA)
      fun h1 => ha₀ ?_
    have := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 1) h1
    simp only [blk3_xMat_mul_wMat] at this
    simpa using this
  · obtain ⟨b₀, c, rfl⟩ := mem_V2.mp hV2
    have hb₀ : b₀ ≠ 0 := fun h0 => huW ⟨c, by rw [h0, yP_zero, one_mul]⟩
    refine key 0 (yMat b₀ * wMat c) (yMat_mul_wMat_mem hK4' b₀ c) (by rw [map_mul]; exact huA)
      fun h1 => hb₀ ?_
    have := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 1) h1
    simp only [blk3_yMat_mul_wMat] at this
    simpa using this

end CFSG.LocalAnalysis.WeakClosure81.SwapL3
