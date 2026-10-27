module

public import CFSG.Quasithin.H13.L32A726Q
public import CFSG.Quasithin.H13.KG14726CPar
public import CFSG.Quasithin.H13.KG14726CU33
public import CFSG.Quasithin.Background.SmithC27Setup
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm
public import CFSG.Quasithin.H13.KG14726Elim

public noncomputable section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Subgroup KG14726

namespace KG14726

section AutOn

variable {G : Type} [Group G] {K V : Subgroup G}

theorem conjAct_mem_autOn {H : Subgroup G} (hHN : H ≤ normalizer (V : Set G)) {h : G}
    (hh : h ∈ H) : conjAct V ⟨h, hHN hh⟩ ∈ autOn H V :=
  ⟨⟨h, hHN hh⟩, mem_subgroupOf.mpr hh, rfl⟩

@[expose] def autOnHom (hKN : K ≤ normalizer (V : Set G)) : ↥K →* ↥(autOn K V) :=
  ((conjAct V).comp (inclusion hKN)).codRestrict (autOn K V) fun k =>
    conjAct_mem_autOn hKN k.2

theorem autOnHom_apply (hKN : K ≤ normalizer (V : Set G)) (k : ↥K) :
    ((autOnHom hKN k : ↥(autOn K V)) : MulAut ↥V) = conjAct V ⟨k, hKN k.2⟩ := rfl

theorem autOnHom_surjective (hKN : K ≤ normalizer (V : Set G)) :
    Function.Surjective (autOnHom hKN) := by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, mem_subgroupOf.mp hx⟩, Subtype.ext rfl⟩

@[expose] def quotAutOn (hKN : K ≤ normalizer (V : Set G))
    (hO : pCoreOf 2 K ≤ centralizer (V : Set G)) :
    (↥K ⧸ CFSG.pCore 2 ↥K) →* ↥(autOn K V) :=
  QuotientGroup.lift _ (autOnHom hKN) fun x hx => by
    have hxG : (x : G) ∈ pCoreOf 2 K := ⟨x, by exact hx, rfl⟩
    have hxC := hO hxG
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    rw [autOnHom_apply]
    have hmem : (⟨x, hKN x.2⟩ : ↥(normalizer (V : Set G))) ∈ (V.normalizerMonoidHom).ker := by
      rw [normalizerMonoidHom_ker, mem_subgroupOf]
      exact hxC
    exact hmem

theorem quotAutOn_surjective (hKN : K ≤ normalizer (V : Set G))
    (hO : pCoreOf 2 K ≤ centralizer (V : Set G)) : Function.Surjective (quotAutOn hKN hO) := by
  intro y
  obtain ⟨k, rfl⟩ := autOnHom_surjective hKN y
  exact ⟨k, rfl⟩

theorem nontrivial_autOn (hKN : K ≤ normalizer (V : Set G))
    (hKV : ¬ K ≤ centralizer (V : Set G)) : Nontrivial ↥(autOn K V) := by
  rw [IsConcreteLE.not_le_iff_exists] at hKV
  obtain ⟨k, hkK, hkV⟩ := hKV
  rw [mem_centralizer_iff] at hkV
  push Not at hkV
  obtain ⟨v, hv, hne⟩ := hkV
  refine ⟨⟨autOnHom hKN ⟨k, hkK⟩, 1, fun h => hne ?_⟩⟩
  have h1 := congrArg (fun φ : ↥(autOn K V) => ((φ : MulAut ↥V) ⟨v, hv⟩ : G)) h
  simp only [autOnHom_apply, coe_one, MulAut.one_apply] at h1
  have h2 : ((conjAct V ⟨k, hKN hkK⟩) ⟨v, hv⟩ : G) = k * v * k⁻¹ := rfl
  rw [h2] at h1
  calc v * k = k * v * k⁻¹ * k := by rw [h1]
    _ = k * v := by group

end AutOn

theorem exists_sylow_map_of_isBorelIn {G H : Type} [Group G] [Group H] {W Bor : Subgroup G}
    (hBor : CFSG.Quasithin.IsBorelIn W Bor) (e : ↥W ≃* H) :
    ∃ S' : Subgroup H, IsSylowTwoOf S' ⊤ ∧
      (Bor.subgroupOf W).map e.toMonoidHom = normalizer (S' : Set H) := by
  obtain ⟨S, hS, rfl⟩ := hBor
  have hSW : S ≤ W := hS.1
  refine ⟨(S.subgroupOf W).map e.toMonoidHom,
    ⟨le_top, (hS.2.1.comap_of_injective W.subtype W.subtype_injective).map _, ?_⟩, ?_⟩
  · rw [← Subgroup.relIndex, Subgroup.relIndex_top_right, MulEquiv.toMonoidHom_eq_coe,
      index_map_equiv]
    exact hS.2.2
  · rw [← map_equiv_normalizer_eq]
    congr 1
    ext x
    rw [mem_subgroupOf, mem_inf, mem_normalizer_iff, mem_normalizer_iff]
    constructor
    · rintro ⟨-, hx⟩ s
      rw [mem_subgroupOf, mem_subgroupOf, coe_mul, coe_mul, coe_inv]
      exact hx s
    · intro hx
      refine ⟨x.2, fun g => ?_⟩
      constructor
      · intro hg
        have h := (hx ⟨g, hSW hg⟩).mp (by rw [mem_subgroupOf]; exact hg)
        rwa [mem_subgroupOf, coe_mul, coe_mul, coe_inv] at h
      · intro hg
        have hgW : g ∈ W := by
          have h1 : (x : G) * g * (x : G)⁻¹ ∈ W := hSW hg
          have h2 : (x : G)⁻¹ * ((x : G) * g * (x : G)⁻¹) * (x : G) ∈ W :=
            W.mul_mem (W.mul_mem (W.inv_mem x.2) h1) x.2
          rwa [show (x : G)⁻¹ * ((x : G) * g * (x : G)⁻¹) * (x : G) = g by group] at h2
        have h := (hx ⟨g, hgW⟩).mpr (by rw [mem_subgroupOf, coe_mul, coe_mul, coe_inv]; exact hg)
        rwa [mem_subgroupOf] at h

section PrimeTest

variable {G : Type} [Group G] {M K V : Subgroup G}
  {B : Subgroup (MulAut (↥K ⧸ CFSG.pCore 2 ↥K))}

theorem false_of_autOn_prime (hKN : K ≤ normalizer (V : Set G))
    (hO : pCoreOf 2 K ≤ centralizer (V : Set G)) (hB : ∃ a : ℕ, Nat.card B = 2 ^ a * 27)
    (hF4 : ∀ k : ↥K, (k : G) ∈ M →
      MulAut.conj (QuotientGroup.mk k : ↥K ⧸ CFSG.pCore 2 ↥K) ∈ B)
    (hZ : ∀ w ∈ center ↥(autOn K V), w ^ 3 = 1) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {y : MulAut ↥V} (hy : y ∈ autOn (M ⊓ K) V) (hyp : orderOf y = p) : False := by
  obtain ⟨x, hx, rfl⟩ := hy
  have hx : (x : G) ∈ M ∧ (x : G) ∈ K := mem_inf.mp (mem_subgroupOf.mp hx)
  set k : ↥K := ⟨x, hx.2⟩ with hk
  have hψ : ((quotAutOn hKN hO (k : ↥K ⧸ CFSG.pCore 2 ↥K) : ↥(autOn K V)) : MulAut ↥V) =
      conjAct V x := rfl
  refine false_of_surjective_prime hB (quotAutOn hKN hO) (quotAutOn_surjective hKN hO) hZ hp
    hp5 (hF4 k hx.1) ?_
  rw [← Subgroup.orderOf_coe, hψ, hyp]

end PrimeTest

theorem center_specialLinear_two_eq_bot {F : Type} [Field F] [CharP F 2] :
    center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center, scalars_two_eq_bot]

theorem pow_three_of_mem_center_specialLinear_three {F : Type} [Field F]
    {A : Matrix.SpecialLinearGroup (Fin 3) F}
    (hA : A ∈ center (Matrix.SpecialLinearGroup (Fin 3) F)) :
    A ^ 3 = 1 := by
  rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_scalars] at hA
  obtain ⟨c, hc, hAc⟩ := hA
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, hAc, Matrix.SpecialLinearGroup.coe_one, ← map_pow,
    ← Units.val_pow_eq_pow_val, hc, Units.val_one, map_one]

theorem pow_three_of_mem_center_of_mulEquiv {W W' : Type*} [Group W] [Group W'] (e : W ≃* W')
    (h : ∀ w ∈ center W', w ^ 3 = 1) : ∀ w ∈ center W, w ^ 3 = 1 := by
  intro w hw
  have hw' : e w ∈ center W' := by
    rw [mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, (mem_center_iff.mp hw) z]
  apply e.injective
  rw [map_pow, h _ hw', map_one]

theorem card_mulAut_dvd_factorial_of_mulEquiv {X : Type*} [Group X] {n : ℕ} (hn : 5 ≤ n)
    (hn6 : n ≠ 6) (e : X ≃* alternatingGroup (Fin n)) : Nat.card (MulAut X) ∣ n.factorial := by
  rw [card_mulAut_congr e, card_mulAut_alternatingGroup hn hn6]

theorem card_mulAut_dvd_of_mulEquiv_alternatingGroup_six
    {X : Type*} [Group X] (e : X ≃* alternatingGroup (Fin 6)) : Nat.card (MulAut X) ∣ 1440 := by
  rw [card_mulAut_congr e]
  exact card_mulAut_alternatingGroup_six_dvd

end KG14726

open KG14726

theorem kg14726C27C_of (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G) :
    KG14726C27C := by
  intro G _ _ H R M K hC23 hK hqs hchar hKM hRN A hA B hBA hBi hB _ hF4 _
  obtain ⟨⟨h1, -, -⟩, -, h3⟩ := hC27 G H R M K _ hC23 hK hqs hchar hKM hRN rfl
  set V := omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) with hV
  set X := ↥K ⧸ CFSG.pCore 2 ↥K with hXdef
  have : Group.IsPerfect X := hqs.1
  have hKN : K ≤ normalizer (V : Set G) :=
    le_sup_left.trans ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ R)).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf _))
  have hKn : (K.subgroupOf (K ⊔ R)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le le_normalizer hRN)
  have hO : pCoreOf 2 K ≤ centralizer (V : Set G) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hsub : CFSG.Open.IsSubnormal K (K ⊔ R) := .step le_sup_left hKn (.refl _)
    exact (A4.pCoreOf_le_of_subnormal 2 hsub).trans (h1.trans inf_le_right)
  have hKV : ¬ K ≤ centralizer (V : Set G) :=
    SmithC27.Hyp27.not_le_centralizer ⟨hC23, hK, hqs, hchar, hKM, hRN⟩
  have : Nontrivial ↥(autOn K V) := nontrivial_autOn hKN hKV
  set ψ := quotAutOn hKN hO with hψdef
  have hψ : Function.Surjective ψ := quotAutOn_surjective hKN hO
  have hord : ∀ n : ℕ, Nat.card (MulAut X) ∣ n → ¬ 27 ∣ n → False := fun n hn h27 =>
    false_of_card_mulAut_dvd hn h27 hB
  have hinj : center X = ⊥ → Function.Injective ψ := fun hc => by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hc]
    exact ker_le_center_of_surjective hqs ψ hψ
  rcases h3 with ⟨-, h⟩ | h | h | h | h | h | h | h
  ·
    rcases h with ⟨⟨n, hn, F, _, _, hF, α, hα, hker, -⟩, -, hBor⟩ | ⟨⟨α, hα, hker, -⟩, -⟩ |
      ⟨⟨α, hα, hker, -⟩, -⟩ | ⟨⟨α, hα, hker, -⟩, -⟩
    ·
      have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
      have : CharP F 2 :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_two (by omega) hF'
      set eX := quotientPCoreEquiv α hα hker with heX
      have hcX : center X = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have hex : eX x ∈ center (Matrix.SpecialLinearGroup (Fin 2) F) := by
          rw [mem_center_iff]
          intro y
          obtain ⟨z, rfl⟩ := eX.surjective y
          rw [← map_mul, ← map_mul, (mem_center_iff.mp hx) z]
        rw [center_specialLinear_two_eq_bot, mem_bot] at hex
        rw [mem_bot]
        exact eX.injective (by rw [hex, map_one])
      rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | hn3
      · exact hord 120 (card_mulAut_dvd_of_mulEquiv_sl2_four hqs (by rw [hF']; norm_num) eX)
          (by decide)
      · let eψ : X ≃* ↥(autOn K V) := MulEquiv.ofBijective ψ ⟨hinj hcX, hψ⟩
        let eW : ↥(autOn K V) ≃* Matrix.SpecialLinearGroup (Fin 2) F := eψ.symm.trans eX
        obtain ⟨S', hS', hmap⟩ := exists_sylow_map_of_isBorelIn hBor eW
        obtain ⟨p, hp, hp5, y', hy', hy'p⟩ := exists_prime_orderOf_mem_normalizer_sl2 hF' hn3 hS'
        rw [← hmap] at hy'
        obtain ⟨y, hy, hyp⟩ := exists_orderOf_mem_of_mem_map eW hy'
        have hZ : ∀ w ∈ center ↥(autOn K V), w ^ 3 = 1 :=
          pow_three_of_mem_center_of_mulEquiv eW fun w hw => by
            rw [center_specialLinear_two_eq_bot, mem_bot] at hw
            rw [hw, one_pow]
        exact false_of_autOn_prime hKN hO hB hF4 hZ hp hp5 hy (hyp.trans hy'p)
    · exact hord _ (card_mulAut_dvd_factorial_of_mulEquiv (by norm_num) (by norm_num)
        (quotientPCoreEquiv α hα hker)) (by decide)
    · exact hord _ (card_mulAut_dvd_factorial_of_mulEquiv (by norm_num) (by norm_num)
        (quotientPCoreEquiv α hα hker)) (by decide)
    · exact hord _ (card_mulAut_dvd_factorial_of_mulEquiv (by norm_num) (by norm_num)
        (quotientPCoreEquiv α hα hker)) (by decide)
  ·
    obtain ⟨⟨n, α, h5, h8, -, ⟨hα, hker, -⟩, -⟩, -⟩ := h
    rcases (by omega : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) with rfl | rfl | rfl | rfl
    · exact hord _ (card_mulAut_dvd_factorial_of_mulEquiv (by norm_num) (by norm_num)
        (quotientPCoreEquiv α hα hker)) (by decide)
    · exact hord 1440 (card_mulAut_dvd_of_mulEquiv_alternatingGroup_six
        (quotientPCoreEquiv α hα hker)) (by decide)
    · exact hord _ (card_mulAut_dvd_factorial_of_mulEquiv (by norm_num) (by norm_num)
        (quotientPCoreEquiv α hα hker)) (by decide)
    · exact hord _ (card_mulAut_dvd_factorial_of_mulEquiv (by norm_num) (by norm_num)
        (quotientPCoreEquiv α hα hker)) (by decide)
  ·
    obtain ⟨⟨-, ⟨-, -, ⟨e⟩⟩, -⟩, -⟩ := h
    exact hord 1440 (card_mulAut_dvd_of_quotientCenter_alternatingGroup_six e) (by decide)
  ·
    obtain ⟨⟨-, ⟨α, hα, hker⟩, -⟩, -⟩ := h
    exact hord _ (card_mulAut_dvd_factorial_of_mulEquiv (by norm_num) (by norm_num)
      (quotientPCoreEquiv α hα hker)) (by decide)
  ·
    obtain ⟨⟨-, α, hα, hker, -⟩ | ⟨-, F, _, _, hF, α, hα, hker, -⟩, hPar⟩ := h
    · exact hord 1440 (card_mulAut_dvd_of_mulEquiv_alternatingGroup_six
        (quotientPCoreEquiv α hα hker)) (by decide)
    ·
      have hF' : Nat.card F = 4 := by rw [Nat.card_eq_fintype_card, hF]
      have : CharP F 2 :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_two (by norm_num) (show Nat.card F = 2 ^ 2 by rw [hF']; norm_num)
      set eX := quotientPCoreEquiv α hα hker with heX
      have hbij := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
        (r := 2) (K := F)
      let e₂ : X ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 F) :=
        eX.trans (MulEquiv.ofBijective _ hbij)
      have : IsSimpleGroup
          (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 F)) :=
        CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by norm_num)
          (Or.inl (Or.inr (by rw [hF'])))
      have hcX : center X = ⊥ := center_eq_bot_of_mulEquiv_simple hqs e₂
      let eψ : X ≃* ↥(autOn K V) := MulEquiv.ofBijective ψ ⟨hinj hcX, hψ⟩
      let eW : ↥(autOn K V) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) := eψ.symm.trans eX
      obtain ⟨y', hy', hy'5⟩ := exists_orderOf_five_mem_of_isMaxParabolic2_sp4 hF'
        (CFSG.Quasithin.QP.isMaxParabolic2_top_of_mulEquiv hPar eW)
      obtain ⟨y, hy, hyp⟩ := exists_orderOf_mem_of_mem_map eW hy'
      have hZ : ∀ w ∈ center ↥(autOn K V), w ^ 3 = 1 := by
        intro w hw
        have hw' : eψ.symm w ∈ center X := by
          rw [mem_center_iff]
          intro y
          obtain ⟨z, rfl⟩ := eψ.symm.surjective y
          rw [← map_mul, ← map_mul, (mem_center_iff.mp hw) z]
        rw [hcX, mem_bot] at hw'
        rw [show w = 1 from eψ.symm.injective (by rw [hw', map_one]), one_pow]
      exact false_of_autOn_prime hKN hO hB hF4 hZ Nat.prime_five le_rfl hy (hyp.trans hy'5)
  ·
    obtain ⟨⟨-, hU, -⟩, -⟩ := h
    exact false_of_isPSU_three_three hqs hU hA hBA hBi hB
  ·
    obtain ⟨⟨m, F, _, _, hm, hF, ⟨e⟩⟩, hPar, -⟩ := h
    have hF' : Nat.card F = 2 ^ m := by rw [Nat.card_eq_fintype_card, hF]
    have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hF'
    let eW : ↥(autOn K V) ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
      e.trans (specialLinearGroupEquivStatedSL 3 F).symm
    rcases (by omega : m = 1 ∨ 2 ≤ m) with rfl | hm2
    · have := nontrivial_specialLinearGroup (n := 3) (by norm_num) F
      have eQ : X ⧸ center X ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F :=
        ((quotientCenterEquivOfSurjective hqs ψ hψ).trans (quotientCenterCongr eW)).trans
          (quotientCenterSpecialLinearEquiv 3 F)
      exact hord _ (card_mulAut_dvd_of_quotientCenter_projectiveSL_card_two (Or.inl rfl)
        (by rw [hF']; norm_num) eQ) (by decide)
    · obtain ⟨p, hp, hp5, y', hy', hy'p⟩ := exists_prime_orderOf_mem_of_isMaxParabolic2_sl3 hF' hm2
        (CFSG.Quasithin.QP.isMaxParabolic2_top_of_mulEquiv hPar eW)
      obtain ⟨y, hy, hyp⟩ := exists_orderOf_mem_of_mem_map eW hy'
      exact false_of_autOn_prime hKN hO hB hF4
        (pow_three_of_mem_center_of_mulEquiv eW fun _ hw =>
          pow_three_of_mem_center_specialLinear_three hw) hp hp5 hy (hyp.trans hy'p)
  ·
    obtain ⟨he, -⟩ := h
    rcases he with he | he
    · obtain ⟨e⟩ := he
      have := nontrivial_specialLinearGroup (n := 4) (by norm_num) (ZMod 2)
      have eQ : X ⧸ center X ≃*
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 4 (ZMod 2) :=
        ((quotientCenterEquivOfSurjective hqs ψ hψ).trans
          (quotientCenterCongr (e.trans (specialLinearGroupEquivStatedSL 4 (ZMod 2)).symm))).trans
          (quotientCenterSpecialLinearEquiv 4 (ZMod 2))
      exact hord _ (card_mulAut_dvd_of_quotientCenter_projectiveSL_card_two (Or.inr (Or.inl rfl))
        (by rw [Nat.card_zmod]) eQ) (by decide)
    · obtain ⟨e⟩ := he
      have := nontrivial_specialLinearGroup (n := 5) (by norm_num) (ZMod 2)
      have eQ : X ⧸ center X ≃*
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 5 (ZMod 2) :=
        ((quotientCenterEquivOfSurjective hqs ψ hψ).trans
          (quotientCenterCongr (e.trans (specialLinearGroupEquivStatedSL 5 (ZMod 2)).symm))).trans
          (quotientCenterSpecialLinearEquiv 5 (ZMod 2))
      exact hord _ (card_mulAut_dvd_of_quotientCenter_projectiveSL_card_two (Or.inr (Or.inr rfl))
        (by rw [Nat.card_zmod]) eQ) (by decide)

end CFSG.Quasithin.H13

end
