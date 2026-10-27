module

public import CFSG.Quasithin.H13.A7Nat1236InspBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL4L5
public import CFSG.Quasithin.H13.A7Nat1238Ke

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Subgroup CFSG.Open CFSG.Quasithin Matrix
open CFSG.QuasithinUnique.Vol2Native.A312L (rank2_eq_perfectCore sl2_isSimple sl2_nonabelian
  exists_conj_of_isSylowTwoOf map_map_symm mapEquiv)

theorem not_isSolvable_of_isQuasisimple' {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q) :
    ¬ Group.IsSolvable Q := by
  obtain ⟨hperf, -, a, b, hab⟩ := hQ
  have : Nontrivial Q := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have : Subsingleton (Q ⧸ center Q) := (QuotientGroup.mk'_surjective (center Q)).subsingleton
    exact hab (Subsingleton.elim _ _)
  exact Group.IsPerfect.not_isSolvable Q

theorem isQuasisimple_pCore_quotient_of_twoKer {W Q : Type*} [Group W] [Finite W] [Group Q]
    (hQ : CFSG.IsQuasisimple Q) (ρ : W →* Q) (hρ : Function.Surjective ρ)
    (hker : IsPGroup 2 ρ.ker) : CFSG.IsQuasisimple (W ⧸ CFSG.pCore 2 W) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Q := Finite.of_surjective ρ hρ
  have hOn : (CFSG.pCore 2 W).Normal := CFSG.pCore_normal
  have hOp : IsPGroup 2 (CFSG.pCore 2 W) := CFSG.pCore_isPGroup
  have hkerO : ρ.ker ≤ CFSG.pCore 2 W := le_sSup ⟨inferInstance, hker⟩
  have hO'n : ((CFSG.pCore 2 W).map ρ).Normal := hOn.map _ hρ
  have hO'p : IsPGroup 2 ((CFSG.pCore 2 W).map ρ) := hOp.map _
  have hO'c : (CFSG.pCore 2 W).map ρ ≤ center Q := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hO'n with htop | hc
    · exfalso
      apply not_isSolvable_of_isQuasisimple' hQ
      have h2 : IsPGroup 2 (⊤ : Subgroup Q) := htop ▸ hO'p
      have h3 : IsPGroup 2 Q := h2.of_equiv Subgroup.topEquiv
      have := h3.isNilpotent
      infer_instance
    · exact hc
  have hquot := (CFSG.LocalCores.quasisimple_central_quotient hQ _ hO'c).1
  let φ : W →* Q ⧸ (CFSG.pCore 2 W).map ρ := (QuotientGroup.mk' _).comp ρ
  have hφs : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hρ
  have hφker : φ.ker = CFSG.pCore 2 W := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have h1 : y⁻¹ * x ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
      have h2 := mul_mem hy (hkerO h1)
      rwa [mul_inv_cancel_left] at h2
    · intro hx
      exact ⟨x, hx, rfl⟩
  have e : W ⧸ CFSG.pCore 2 W ≃* Q ⧸ (CFSG.pCore 2 W).map ρ :=
    (QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hquot

theorem isQuasisimple_pCore_quotient_of_surjective {W B : Type*} [Group W] [Finite W] [Group B]
    (hW : CFSG.IsQuasisimple (W ⧸ CFSG.pCore 2 W)) (ρ : W →* B) (hρ : Function.Surjective ρ)
    (hB : ¬ IsPGroup 2 B) : CFSG.IsQuasisimple (B ⧸ CFSG.pCore 2 B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite B := Finite.of_surjective ρ hρ
  have hBn : (CFSG.pCore 2 B).Normal := CFSG.pCore_normal
  have hWn : (CFSG.pCore 2 W).Normal := CFSG.pCore_normal
  have hle : CFSG.pCore 2 W ≤ (CFSG.pCore 2 B).comap ρ := by
    intro w hw
    have h1 : (CFSG.pCore 2 W).map ρ ≤ CFSG.pCore 2 B :=
      le_sSup ⟨hWn.map ρ hρ, CFSG.pCore_isPGroup.map ρ⟩
    exact h1 ⟨w, hw, rfl⟩
  let ρ' : W ⧸ CFSG.pCore 2 W →* B ⧸ CFSG.pCore 2 B := QuotientGroup.map _ _ ρ hle
  have hρ' : Function.Surjective ρ' := by
    intro q
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨w, rfl⟩ := hρ b
    exact ⟨QuotientGroup.mk w, rfl⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hW ρ'.normal_ker with htop | hc
  · exfalso
    apply hB
    intro b
    have hb : (QuotientGroup.mk b : B ⧸ CFSG.pCore 2 B) = 1 := by
      obtain ⟨w, rfl⟩ := hρ b
      have h1 : (QuotientGroup.mk w : W ⧸ CFSG.pCore 2 W) ∈ ρ'.ker := htop ▸ mem_top _
      rw [MonoidHom.mem_ker] at h1
      exact h1
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := B)) ⟨b, (QuotientGroup.eq_one_iff b).1 hb⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  · exact CFSG.LocalCores.isQuasisimple_of_surjective hW ρ' hρ' hc

theorem surjective_comp_inclusion_perfectCore {S Q : Type*} [Group S] [Finite S] [Group Q]
    [Finite Q] (hQ : commutator Q = ⊤) {H : Subgroup S} {f : ↥H →* Q}
    (hf : Function.Surjective f) :
    Function.Surjective (f.comp (Subgroup.inclusion (perfectCore_le H))) := by
  have h1 : (perfectCore H).subgroupOf H = perfectCore (⊤ : Subgroup ↥H) := by
    have h2 := map_perfectCore H.subtype (⊤ : Subgroup ↥H)
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
    rw [← h2]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have h3 : ((perfectCore H).subgroupOf H).map f = ⊤ := by
    rw [h1, map_perfectCore, Subgroup.map_top_of_surjective f hf]
    exact perfectCore_eq_self_of_perfect (by rw [← _root_.commutator_def]; exact hQ)
  intro q
  have hq : q ∈ ((perfectCore H).subgroupOf H).map f := by
    rw [h3]
    exact Subgroup.mem_top q
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hq
  exact ⟨⟨y, hy⟩, rfl⟩

theorem isQuasisimple_pCore_quotient_perfectCore {S : Type} [Group S] [Finite S]
    {H : Subgroup S} (hH : CFSG.IsQuasisimple (↥H ⧸ CFSG.pCore 2 ↥H)) :
    CFSG.IsQuasisimple (↥(perfectCore H) ⧸ CFSG.pCore 2 ↥(perfectCore H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  have hperf : commutator (↥H ⧸ CFSG.pCore 2 ↥H) = ⊤ := hH.1.commutator_eq_top
  let ρ : ↥(perfectCore H) →* ↥H ⧸ CFSG.pCore 2 ↥H :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion (perfectCore_le H))
  have hρ : Function.Surjective ρ :=
    surjective_comp_inclusion_perfectCore hperf (QuotientGroup.mk'_surjective _)
  refine isQuasisimple_pCore_quotient_of_twoKer hH ρ hρ ?_
  rintro ⟨x, hx⟩
  have hx' : Subgroup.inclusion (perfectCore_le H) x ∈ CFSG.pCore 2 ↥H := by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    exact hx
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨_, hx'⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have h1 := congrArg (fun y : ↥(CFSG.pCore 2 ↥H) => ((y : ↥H) : S)) hk
  simpa using h1

theorem mem_lFamily_perfectCore {S : Type} [Group S] [Finite S] {Y U : Subgroup S}
    (hq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y)) (hU : U ≤ normalizer (Y : Set S)) :
    perfectCore Y ∈ lFamily U := by
  have hperf := perfectCore_perfect Y
  show perfectCore Y ∈ cComp (perfectCore Y ⊔ U)
  refine mem_cComp_of_quasisimple_quotient
    (fun N _ hN => eq_top_of_perfect_of_isPGroup hperf N hN)
    (isQuasisimple_pCore_quotient_perfectCore hq) ?_
  exact A3.subnormal_of_normal le_sup_left
    ((normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (sup_le le_normalizer (hU.trans (normalizer_le_normalizer_perfectCore Y))))

theorem exists_lFamily_of_hom {G : Type} [Group G] [Finite G] {K X T₀ : Subgroup G}
    (hXK : X ≤ K) (hT₀X : T₀ ≤ normalizer (X : Set G)) (hT₀ : QuasithinUnique.IsSylowTwoOf T₀ K)
    (hXq : CFSG.IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X)) {θ : ↥X →* alternatingGroup (Fin 6)}
    (hθ : Function.Surjective θ) {S : Type} [Group S] [Finite S] (κ : ↥K →* S)
    (hκ : Function.Surjective κ) (hker : ∀ x : ↥X, κ (Subgroup.inclusion hXK x) = 1 → θ x = 1) :
    ∃ U B : Subgroup S, QuasithinUnique.IsSylowTwoOf U ⊤ ∧ B ∈ lFamily U ∧
      B ≤ (κ.comp (Subgroup.inclusion hXK)).range ∧
      ∃ f : ↥B →* alternatingGroup (Fin 6), Function.Surjective f := by
  set ρ := κ.comp (Subgroup.inclusion hXK) with hρ
  obtain ⟨fx, hfx⟩ := exists_surj_of_ker_le ρ hθ hker
  have hq : CFSG.IsQuasisimple (↥ρ.range ⧸ CFSG.pCore 2 ↥ρ.range) :=
    isQuasisimple_pCore_quotient_of_surjective hXq ρ.rangeRestrict ρ.rangeRestrict_surjective
      (not_isPGroup_of_surj_alt_six hfx)
  exact ⟨(T₀.subgroupOf K).map κ, perfectCore ρ.range, isSylowTwoOf_map_subgroupOf hT₀ κ hκ,
    mem_lFamily_perfectCore hq (map_le_normalizer_range hXK hT₀X κ), perfectCore_le _,
    fx.comp (Subgroup.inclusion (perfectCore_le _)),
    surjective_comp_inclusion_perfectCore commutator_alt_six hfx⟩

theorem false_of_lFamily_conj {S : Type} [Group S] [Finite S] {U₀ : Subgroup S}
    (hU₀ : QuasithinUnique.IsSylowTwoOf U₀ ⊤)
    (h : ∀ B ∈ lFamily U₀, B ≠ ⊤ → ∀ f : ↥B →* alternatingGroup (Fin 6),
      Function.Surjective f → False)
    {U : Subgroup S} (hU : QuasithinUnique.IsSylowTwoOf U ⊤) {B : Subgroup S}
    (hB : B ∈ lFamily U) (hBtop : B ≠ ⊤) {f : ↥B →* alternatingGroup (Fin 6)}
    (hf : Function.Surjective f) : False := by
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf hU₀ hU
  let e : S ≃* S := (MulAut.conj g).symm
  have hT' : U.map e.toMonoidHom = U₀ := by
    rw [← hg]
    exact map_map_symm (MulAut.conj g) U₀
  have hB' : B.map e.toMonoidHom ∈ lFamily U₀ := by
    have h1 := cComp_map_mulEquiv e (show B ∈ cComp (B ⊔ U) from hB)
    rw [Subgroup.map_sup, hT'] at h1
    exact h1
  have hne : B.map e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hBtop
    have := congrArg (Subgroup.map e.symm.toMonoidHom) htop
    rw [map_map_symm, Subgroup.map_top_of_surjective _ e.symm.surjective] at this
    exact this
  exact h _ hB' hne (f.comp (mapEquiv e B).toMonoidHom) (hf.comp (mapEquiv e B).surjective)

theorem mul_sq_sub_one_ne (q : ℕ) : q * (q ^ 2 - 1) ≠ 360 := by
  intro h
  rcases Nat.lt_or_ge q 8 with hq | hq
  · interval_cases q <;> norm_num at h
  · have h64 : 64 ≤ q ^ 2 := by nlinarith
    have h1 : 8 * 63 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul hq (by omega)
    rw [h] at h1
    norm_num at h1

theorem card_SL_of_card_two {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2) (n : ℕ)
    [NeZero n] : Nat.card (SpecialLinearGroup (Fin n) F) = ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
  rw [Matrix.card_SL_field, hF]
  simp

theorem charP_two_of_card {F : Type} [Field F] {k : ℕ} (hk : 1 ≤ k) (hF : Nat.card F = 2 ^ k) :
    CharP F 2 :=
  CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hk hF

theorem finite_SL {F : Type} [Field F] [Finite F] (n : ℕ) :
    Finite (SpecialLinearGroup (Fin n) F) :=
  Finite.of_injective (fun A : SpecialLinearGroup (Fin n) F => (A : Matrix (Fin n) (Fin n) F))
    Subtype.val_injective

section RankTwo

open CFSG.QuasithinUnique.Setup.X6

theorem false_of_rank2_levi {S : Type} [Group S] [Finite S] (hq : CFSG.IsQuasisimple S)
    {U : Subgroup S} {P : Fin 2 → Subgroup S} (hP : ResidualOvergroupsAt S U P)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF4 : ∃ s : Finset F, s.card = 4)
    (g : ∀ j, ↥(perfectCore (P j)) →* SpecialLinearGroup (Fin 2) F)
    (hg : ∀ j, Function.Surjective (g j)) (hker : ∀ j, IsPGroup 2 (g j).ker)
    {B : Subgroup S} (hB : B ∈ lFamily U) (hBtop : B ≠ ⊤)
    {f : ↥B →* alternatingGroup (Fin 6)} (hf : Function.Surjective f) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (SpecialLinearGroup (Fin 2) F) := finite_SL 2
  have hs := sl2_isSimple hF4
  have hnab := sl2_nonabelian hF4
  have hsolv : ∀ j, Group.IsSolvable (g j).ker := fun j => by
    have := (hker j).isNilpotent
    infer_instance
  obtain ⟨j, hBj⟩ := rank2_eq_perfectCore hq hP
    (fun j => ⟨SpecialLinearGroup (Fin 2) F, inferInstance, hs, hnab, g j, hg j, hsolv j⟩) hB
    hBtop
  let gB : ↥B →* SpecialLinearGroup (Fin 2) F :=
    (g j).comp (MulEquiv.subgroupCongr hBj).toMonoidHom
  have hgB : Function.Surjective gB := (hg j).comp (MulEquiv.subgroupCongr hBj).surjective
  have hkerB : IsPGroup 2 gB.ker := by
    intro x
    obtain ⟨k, hk⟩ := hker j ⟨MulEquiv.subgroupCongr hBj x.1, x.2⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : (MulEquiv.subgroupCongr hBj x.1) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [← map_pow, map_eq_one_iff _ (MulEquiv.subgroupCongr hBj).injective] at h1
    exact h1
  have hcard : Nat.card (SpecialLinearGroup (Fin 2) F) ≠ 360 := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
    exact mul_sq_sub_one_ne _
  exact false_of_surj_alt_six_of_twoKer hcard hgB hkerB hf

end RankTwo

section LinearThree

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Setup.X6
open CFSG.QuasithinUnique.Vol2Native.A312L (linear_three_residual_of_cover perfectCoreMapEquiv
  blk3 blk3_surjective blk3_ker_isPGroup)

theorem false_of_sl3 {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Fintype.card F = 2 ^ n) {U : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hU : QuasithinUnique.IsSylowTwoOf U ⊤) {B : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hB : B ∈ lFamily U) (hBtop : B ≠ ⊤) {f : ↥B →* alternatingGroup (Fin 6)}
    (hf : Function.Surjective f) : False := by
  classical
  have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have : CharP F 2 := charP_two_of_card hn hF'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  ·
    have hn1 : n = 1 := by omega
    subst hn1
    have h168 : Nat.card (SpecialLinearGroup (Fin 3) F) = 168 := by
      rw [card_SL_of_card_two (by rw [hF]; norm_num) 3]
      simp [Fin.prod_univ_succ]
    have h1 := (card_alt_six_dvd hf).trans (Subgroup.card_subgroup_dvd_card B)
    rw [h168] at h1
    norm_num at h1
  · have hK : ∃ k : ℕ, Nat.card F = 2 ^ k := ⟨n, hF'⟩
    have hK4 : ∃ s : Finset F, s.card = 4 := by
      refine CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four ?_
      rw [hF']
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    have hq : CFSG.IsQuasisimple (SpecialLinearGroup (Fin 3) F) :=
      CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 F le_rfl
    have hres := linear_three_residual_of_cover hK (MonoidHom.id (SpecialLinearGroup (Fin 3) F))
      Function.surjective_id (by rw [MonoidHom.ker_id]; exact bot_le)
    obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
    have hU₀ : QuasithinUnique.IsSylowTwoOf
        ((unitriangular 3 F).map (MonoidHom.id (SpecialLinearGroup (Fin 3) F))) ⊤ := by
      rw [Subgroup.map_id]
      exact hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
    refine false_of_lFamily_conj hU₀ (fun B hB hBtop f hf => ?_) hU hB hBtop hf
    have hinj : ∀ j : Fin 2, ∀ x ∈ perfectCore (Q3 F j), ∀ y ∈ perfectCore (Q3 F j),
        (MonoidHom.id (SpecialLinearGroup (Fin 3) F)) x =
          (MonoidHom.id (SpecialLinearGroup (Fin 3) F)) y → x = y :=
      fun j x _ y _ h => h
    let eN : ∀ j : Fin 2, ↥(perfectCore (Q3 F j)) ≃*
        ↥(perfectCore ((Q3 F j).map (MonoidHom.id (SpecialLinearGroup (Fin 3) F)))) :=
      fun j => perfectCoreMapEquiv (MonoidHom.id _) (Q3 F j) (hinj j)
    refine false_of_rank2_levi hq hres hK4 (fun j => (blk3 j).comp (eN j).symm.toMonoidHom)
      (fun j => (blk3_surjective hK4 j).comp (eN j).symm.surjective) (fun j z => ?_) hB hBtop hf
    obtain ⟨k, hk⟩ := blk3_ker_isPGroup hK j ⟨(eN j).symm z.1, z.2⟩
    have h1 : ((eN j).symm z.1) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    refine ⟨k, Subtype.ext ?_⟩
    show z.1 ^ 2 ^ k = 1
    have : (eN j).symm (z.1 ^ 2 ^ k) = 1 := by rw [map_pow]; exact h1
    exact (map_eq_one_iff _ (eN j).symm.injective).mp this

end LinearThree

section SymplecticFour

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Setup.X6
open CFSG.QuasithinUnique.Vol2Native.A312L (perfectCoreMapEquiv proj_injective_charTwo blkN
  blkN_surjective blkN_ker_isPGroup)

theorem false_of_sp4 {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4)
    {U : Subgroup (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 F))}
    (hU : QuasithinUnique.IsSylowTwoOf U ⊤)
    {B : Subgroup (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 F))}
    (hB : B ∈ lFamily U) (hBtop : B ≠ ⊤)
    {f : ↥B →* alternatingGroup (Fin 6)} (hf : Function.Surjective f) : False := by
  classical
  have hF' : Nat.card F = 2 ^ 2 := by rw [Nat.card_eq_fintype_card, hF]; norm_num
  have : CharP F 2 := charP_two_of_card (by norm_num) hF'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : ∃ k : ℕ, Nat.card F = 2 ^ k := ⟨2, hF'⟩
  have hK4 : ∃ s : Finset F, s.card = 4 := ⟨Finset.univ, by rw [Finset.card_univ, hF]⟩
  have hq : CFSG.IsQuasisimple
      (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 F)) := by
    have h1 := CFSG.LieType.Universal.Symplectic.isQuasisimple 2 F (by norm_num)
      (Or.inl (Or.inr (by rw [hF']; norm_num)))
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (MulEquiv.ofBijective (proj 2 F) ⟨proj_injective_charTwo, proj_surjective⟩) h1
  have hres : ResidualOvergroupsAt
      (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 F))
      (projUnipotent 2 F)
      (fun j : Fin 2 => (Q2 F j).map (proj 2 F)) := symplectic_two_residualOvergroupsAt hK
  obtain ⟨P, hP⟩ := exists_sylow_projUnipotent (K := F) 2 (r := 2) (by norm_num)
  have hU₀ : QuasithinUnique.IsSylowTwoOf (projUnipotent 2 F) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  refine false_of_lFamily_conj hU₀ (fun B hB hBtop f hf => ?_) hU hB hBtop hf
  have hinj : ∀ j : Fin 2, ∀ x ∈ perfectCore (Q2 F j), ∀ y ∈ perfectCore (Q2 F j),
      proj 2 F x = proj 2 F y → x = y := fun j x _ y _ h => proj_injective_charTwo h
  let eN : ∀ j : Fin 2, ↥(perfectCore (Q2 F j)) ≃* ↥(perfectCore ((Q2 F j).map (proj 2 F))) :=
    fun j => perfectCoreMapEquiv (proj 2 F) (Q2 F j) (hinj j)
  refine false_of_rank2_levi hq hres hK4 (fun j => (blkN j).comp (eN j).symm.toMonoidHom)
    (fun j => (blkN_surjective hK4 j).comp (eN j).symm.surjective) (fun j z => ?_) hB hBtop hf
  obtain ⟨k, hk⟩ := blkN_ker_isPGroup hK j ⟨(eN j).symm z.1, z.2⟩
  have h1 : ((eN j).symm z.1) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  refine ⟨k, Subtype.ext ?_⟩
  show z.1 ^ 2 ^ k = 1
  have : (eN j).symm (z.1 ^ 2 ^ k) = 1 := by rw [map_pow]; exact h1
  exact (map_eq_one_iff _ (eN j).symm.injective).mp this

end SymplecticFour

section LinearFourFive

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.QuasithinUnique.Vol2Native.A312L (exists_big_or_small bigBlock_conclusion
  sl_isSimple_of_card_two upperTriangular_le_unitriangular isPGroup_ker_of_unitriangular
  unitriangular_of_bigBlockHom perfectCore_eq_bot_of_small bigBlockHom bigBlockHom_surjective)

theorem card_SL_ne_of_card_two {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)
    {m : ℕ} (hm3 : 3 ≤ m) (hm5 : m ≤ 5) : Nat.card (SpecialLinearGroup (Fin m) F) ≠ 360 := by
  have : NeZero m := ⟨by omega⟩
  rw [card_SL_of_card_two hF m]
  interval_cases m <;> simp [Fin.prod_univ_succ]

theorem false_of_sl_two_of_ne_top {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)
    {n : ℕ} (hn4 : 4 ≤ n) (hn5 : n ≤ 5) {B : Subgroup (SpecialLinearGroup (Fin n) F)}
    (hB : B ∈ lFamily (unitriangular n F)) (hBtop : B ≠ ⊤)
    {f : ↥B →* alternatingGroup (Fin 6)} (hf : Function.Surjective f) : False := by
  classical
  have hF' : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hF]
  have hcardK : Nat.card F = 2 ^ 1 := by rw [hF']; norm_num
  have : CharP F 2 := charP_two_of_card le_rfl hcardK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : CFSG.IsQuasisimple (SpecialLinearGroup (Fin n) F) := by
    obtain rfl | rfl : n = 4 ∨ n = 5 := by omega
    · exact CFSG.LieType.Universal.SpecialLinear.isQuasisimple 3 F (by norm_num)
    · exact CFSG.LieType.Universal.SpecialLinear.isQuasisimple 4 F (by norm_num)
  have hB' : B ∈ cComp (B ⊔ unitriangular n F) := hB
  have hMne : B ⊔ unitriangular n F ≠ ⊤ := by
    intro htop
    rw [htop] at hB'
    exact hBtop (A321.cComp_eq_top_of_quasisimple hq hB')
  have hMns : ¬ Group.IsSolvable ↥(B ⊔ unitriangular n F) := fun hs =>
    not_isSolvable_of_mem_cComp hB'
      (Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (le_of_mem_cComp hB' : B ≤ B ⊔ unitriangular n F))
        (Subgroup.inclusion_injective _))
  have hUB : upperTriangular n F ≤ B ⊔ unitriangular n F :=
    (upperTriangular_le_unitriangular hF').trans le_sup_right
  obtain ⟨hMQ, -⟩ := borel_overgroups (B ⊔ unitriangular n F) hUB
  have hIcuts : ∀ c ∈ borelOvergroupCuts (B ⊔ unitriangular n F), 1 ≤ c ∧ c < n := fun c hc => by
    obtain ⟨h1, h2, -⟩ := hc
    exact ⟨h1, h2⟩
  rcases exists_big_or_small (n := n) (I := borelOvergroupCuts (B ⊔ unitriangular n F)) with
    hsmall | ⟨a, m, h, hm3, ha, hb, hno⟩
  · apply hMns
    rw [isSolvable_iff_perfectCore_eq_bot, hMQ]
    exact perfectCore_eq_bot_of_small hF' (by omega) hsmall
  · have hmn : m < n := by
      by_contra hmn
      have hmn' : m = n ∧ a = 0 := by omega
      have hIempty : borelOvergroupCuts (B ⊔ unitriangular n F) = ∅ := by
        ext c
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hc
        obtain ⟨h1, h2⟩ := hIcuts c hc
        exact hno c hc ⟨by omega, by omega⟩
      apply hMne
      rw [hMQ, hIempty, flagStabilizer_empty]
    obtain ⟨hBeq, -⟩ := bigBlock_conclusion hF' (by omega) hn5 h hm3 ha hb hno hB hMQ
    have hperfEq : perfectCore (B ⊔ unitriangular n F) =
        perfectCore (flagStabilizer n F (borelOvergroupCuts (B ⊔ unitriangular n F))) :=
      congrArg perfectCore hMQ
    let e1 : ↥B ≃* ↥(perfectCore (flagStabilizer n F
        (borelOvergroupCuts (B ⊔ unitriangular n F)))) :=
      (MulEquiv.subgroupCongr hBeq).trans (MulEquiv.subgroupCongr hperfEq)
    let gB : ↥B →* SpecialLinearGroup (Fin m) F := (bigBlockHom _ a m h ha hb).comp e1.toMonoidHom
    have hgB : Function.Surjective gB :=
      (bigBlockHom_surjective hF' h hm3 ha hb hno).comp e1.surjective
    have hkerB : IsPGroup 2 gB.ker := by
      refine isPGroup_ker_of_unitriangular (by omega) gB fun x hx => ?_
      have h1 := unitriangular_of_bigBlockHom hF' hn5 h hm3 ha hb hno (e1 x) hx
      exact h1
    have : Finite (SpecialLinearGroup (Fin m) F) := finite_SL m
    have := sl_isSimple_of_card_two hF' hm3
    exact false_of_surj_alt_six_of_twoKer (card_SL_ne_of_card_two hF hm3 (by omega)) hgB hkerB hf

theorem false_of_sl_two {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2) {n : ℕ}
    (hn4 : 4 ≤ n) (hn5 : n ≤ 5) {U : Subgroup (SpecialLinearGroup (Fin n) F)}
    (hU : QuasithinUnique.IsSylowTwoOf U ⊤) {B : Subgroup (SpecialLinearGroup (Fin n) F)}
    (hB : B ∈ lFamily U) {f : ↥B →* alternatingGroup (Fin 6)} (hf : Function.Surjective f) :
    False := by
  classical
  have hF' : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hF]
  have hcardK : Nat.card F = 2 ^ 1 := by rw [hF']; norm_num
  have : CharP F 2 := charP_two_of_card le_rfl hcardK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hBtop : B = ⊤
  · subst hBtop
    have : Finite (SpecialLinearGroup (Fin n) F) := finite_SL n
    have := sl_isSimple_of_card_two hF' (by omega : 3 ≤ n)
    let g : SpecialLinearGroup (Fin n) F →* alternatingGroup (Fin 6) :=
      f.comp (Subgroup.topEquiv (G := SpecialLinearGroup (Fin n) F)).symm.toMonoidHom
    have hg : Function.Surjective g := by
      intro a
      obtain ⟨x, rfl⟩ := hf a
      refine ⟨Subgroup.topEquiv x, ?_⟩
      show f (Subgroup.topEquiv.symm (Subgroup.topEquiv x)) = f x
      rw [MulEquiv.symm_apply_apply]
    exact false_of_surj_alt_six_of_simple (card_SL_ne_of_card_two hF (by omega) hn5) hg
  · obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := F) 2 (n := n) (by omega)
    have hU₀ : QuasithinUnique.IsSylowTwoOf (unitriangular n F) ⊤ :=
      hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
    exact false_of_lFamily_conj hU₀ (fun B hB hBtop f hf =>
      false_of_sl_two_of_ne_top hF hn4 hn5 hB hBtop hf) hU hB hBtop hf

end LinearFourFive

end CFSG.Quasithin.H13.A7
