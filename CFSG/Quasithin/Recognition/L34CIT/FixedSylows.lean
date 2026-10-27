module

public import CFSG.Quasithin.Recognition.L34CIT.Opposite

public section

namespace CFSG.Quasithin.L34CIT

open Subgroup CFSG.Open
open scoped Pointwise
open CFSG.GroupTheory.WielandtProduct (mem_conj_smul_iff)

variable {A : Type} [Group A]

namespace Config

theorem line_smul_sylow (C : Config A) [Finite A] (a : A) (P : Sylow 2 A) :
    C.line (a • P) = MulAut.conj a • C.line P := by
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq A C.T P
  rw [← hb, smul_smul, C.line_smul (a * b), C.line_smul b, map_mul, mul_smul]

private theorem finite_sylowTwo (C : Config A) [Finite A] : Finite (Sylow 2 A) :=
  Finite.of_surjective (fun a : A => a • C.T) fun P => MulAction.exists_smul_eq A C.T P

private theorem finite_sylowTwo_A5 : Finite (Sylow 2 (alternatingGroup (Fin 5))) :=
  Nat.finite_of_card_ne_zero (by
    rw [CFSG.GroupTheory.AlternatingFive.card_sylowTwo]
    norm_num)

private noncomputable def sylowToA5 (C : Config A) [Finite A] :
    {P : Sylow 2 A // C.L ≤ (P : Subgroup A)} → Sylow 2 (alternatingGroup (Fin 5)) :=
  fun P => Classical.choose (C.comap_image_point P.2)

private theorem sylowToA5_comap (C : Config A) [Finite A]
    (P : {P : Sylow 2 A // C.L ≤ (P : Subgroup A)}) :
    (((C.sylowToA5 P : Sylow 2 (alternatingGroup (Fin 5))) : Subgroup _).comap C.quotL) =
      (P.1 : Subgroup A).subgroupOf C.K₁ :=
  Classical.choose_spec (C.comap_image_point P.2)

private theorem sylowToA5_injective (C : Config A) [Finite A] :
    Function.Injective C.sylowToA5 := by
  intro P P' h
  apply Subtype.ext
  apply Sylow.ext
  have hcomap : ((C.sylowToA5 P : Sylow 2 (alternatingGroup (Fin 5))) : Subgroup _).comap C.quotL =
      ((C.sylowToA5 P' : Sylow 2 (alternatingGroup (Fin 5))) : Subgroup _).comap C.quotL := by
    rw [h]
  rw [C.sylowToA5_comap P, C.sylowToA5_comap P'] at hcomap
  have hinf := Subgroup.subgroupOf_inj.mp hcomap
  rw [inf_eq_left.mpr (C.le_normalizer_L_of_le_sylow P.2),
    inf_eq_left.mpr (C.le_normalizer_L_of_le_sylow P'.2)] at hinf
  exact hinf

private theorem sylowToA5_bijective (C : Config A) [Finite A] :
    Function.Bijective C.sylowToA5 := by
  classical
  haveI : Finite (Sylow 2 A) := C.finite_sylowTwo
  haveI : Finite (Sylow 2 (alternatingGroup (Fin 5))) := finite_sylowTwo_A5
  haveI : Fintype {P : Sylow 2 A // C.L ≤ (P : Subgroup A)} := Fintype.ofFinite _
  haveI : Fintype (Sylow 2 (alternatingGroup (Fin 5))) := Fintype.ofFinite _
  refine (Fintype.bijective_iff_injective_and_card C.sylowToA5).mpr
    ⟨C.sylowToA5_injective, ?_⟩
  have h1 : Fintype.card {P : Sylow 2 A // C.L ≤ (P : Subgroup A)} = 5 := by
    rw [← Nat.card_eq_fintype_card,
      show Nat.card {P : Sylow 2 A // C.L ≤ (P : Subgroup A)} =
        ({P : Sylow 2 A | C.L ≤ (P : Subgroup A)} : Set (Sylow 2 A)).ncard from
        Nat.card_coe_set_eq _]
    exact C.ncard_sylow_ge_L
  have h2 : Fintype.card (Sylow 2 (alternatingGroup (Fin 5))) = 5 := by
    rw [← Nat.card_eq_fintype_card]
    exact CFSG.GroupTheory.AlternatingFive.card_sylowTwo
  omega

theorem ncard_fixed_sylow_ge_L (C : Config A) [Finite A] {k : A} (hk : k ∈ C.K₁)
    (hk3 : orderOf k = 3) :
    {P : Sylow 2 A | C.L ≤ (P : Subgroup A) ∧ k • P = P}.ncard = 2 := by
  classical
  haveI : Finite (Sylow 2 A) := C.finite_sylowTwo
  haveI : Finite (Sylow 2 (alternatingGroup (Fin 5))) := finite_sylowTwo_A5
  let e : {P : Sylow 2 A // C.L ≤ (P : Subgroup A)} ≃
      Sylow 2 (alternatingGroup (Fin 5)) :=
    Equiv.ofBijective C.sylowToA5 C.sylowToA5_bijective
  let y : alternatingGroup (Fin 5) := C.quotL ⟨k, hk⟩
  have hy3 : orderOf y = 3 := by
    apply orderOf_eq_prime
    · have hkord : orderOf (⟨k, hk⟩ : C.K₁) = 3 := by
        rw [Subgroup.orderOf_mk, hk3]
      have hkpow : (⟨k, hk⟩ : C.K₁) ^ 3 = 1 := by
        rw [← hkord]
        exact pow_orderOf_eq_one _
      dsimp [y]
      rw [← map_pow, hkpow, map_one]
    · intro hy1
      have hker : (⟨k, hk⟩ : C.K₁) ∈ C.quotL.ker := by
        rw [MonoidHom.mem_ker]
        exact hy1
      rw [C.ker_quotL] at hker
      have hkL : k ∈ C.L := hker
      have hL2 : IsPGroup 2 C.L := C.isElemAbelian_L.isPGroup
      obtain ⟨m, hm⟩ := hL2.exists_orderOf_eq_pow (⟨k, hkL⟩ : C.L)
      have hkord : orderOf (⟨k, hkL⟩ : C.L) = 3 := by
        rw [Subgroup.orderOf_mk, hk3]
      rw [hkord] at hm
      have h3dvd : 3 ∣ 2 ^ m := by rw [← hm]
      have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h3dvd
      norm_num at h32
  have hiff : ∀ P : {P : Sylow 2 A // C.L ≤ (P : Subgroup A)},
      k • (P : Sylow 2 A) = (P : Sylow 2 A) ↔ y • (e P) = e P := by
    intro P
    have hPK : (P : Subgroup A) ≤ C.K₁ := C.le_normalizer_L_of_le_sylow P.2
    have hcomap : ((e P : Sylow 2 (alternatingGroup (Fin 5))) : Subgroup _).comap C.quotL =
        (P : Subgroup A).subgroupOf C.K₁ := by
      simpa [e] using C.sylowToA5_comap P
    have h1 : k • (P : Sylow 2 A) = (P : Sylow 2 A) ↔
        k ∈ normalizer ((P : Subgroup A) : Set A) :=
      Sylow.smul_eq_iff_mem_normalizer
    have h2 : k ∈ normalizer ((P : Subgroup A) : Set A) ↔
        (⟨k, hk⟩ : C.K₁) ∈ normalizer ((P : Subgroup A).subgroupOf C.K₁) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hPK]
      rfl
    have h3 : (⟨k, hk⟩ : C.K₁) ∈ normalizer ((P : Subgroup A).subgroupOf C.K₁) ↔
        y ∈ normalizer ((e P : Sylow 2 (alternatingGroup (Fin 5))) : Set _) := by
      rw [← hcomap]
      rw [← Subgroup.comap_normalizer_eq_of_surjective
        ((e P : Sylow 2 (alternatingGroup (Fin 5))) : Subgroup _) C.quotL_surjective]
      rfl
    have h4 : y ∈ normalizer ((e P : Sylow 2 (alternatingGroup (Fin 5))) : Set _) ↔
        y • (e P) = e P := (Sylow.smul_eq_iff_mem_normalizer).symm
    exact h1.trans (h2.trans (h3.trans h4))
  let e0 : {P : Sylow 2 A // C.L ≤ (P : Subgroup A) ∧ k • P = P} ≃
      {P : {P : Sylow 2 A // C.L ≤ (P : Subgroup A)} //
        k • (P : Sylow 2 A) = (P : Sylow 2 A)} :=
    { toFun := fun P => ⟨⟨P.1, P.2.1⟩, P.2.2⟩
      invFun := fun P => ⟨P.1.1, P.1.2, P.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e2 : {P : {P : Sylow 2 A // C.L ≤ (P : Subgroup A)} //
        k • (P : Sylow 2 A) = (P : Sylow 2 A)} ≃
      {Q : Sylow 2 (alternatingGroup (Fin 5)) // y • Q = Q} :=
    Equiv.subtypeEquiv e hiff
  rw [← Nat.card_coe_set_eq]
  calc Nat.card {P : Sylow 2 A // C.L ≤ (P : Subgroup A) ∧ k • P = P}
      = Nat.card {P : {P : Sylow 2 A // C.L ≤ (P : Subgroup A)} //
          k • (P : Sylow 2 A) = (P : Sylow 2 A)} := Nat.card_congr e0
    _ = Nat.card {Q : Sylow 2 (alternatingGroup (Fin 5)) // y • Q = Q} := Nat.card_congr e2
    _ = 2 := CFSG.GroupTheory.AlternatingFive.card_fixed_sylow_two_of_orderOf_eq_three hy3

theorem ncard_fixed_sylow_ge_M (C : Config A) [Finite A] {k : A} (hk : k ∈ C.K₂)
    (hk3 : orderOf k = 3) :
    {P : Sylow 2 A | C.M ≤ (P : Subgroup A) ∧ k • P = P}.ncard = 2 := by
  simpa using C.swap.ncard_fixed_sylow_ge_L hk hk3

private theorem ncard_fixed_sylow_ge_conj_L (C : Config A) [Finite A] (a : A) {k : A}
    (hk : k ∈ normalizer ((MulAut.conj a • C.L : Subgroup A) : Set A))
    (hk3 : orderOf k = 3) :
    {P : Sylow 2 A | (MulAut.conj a • C.L : Subgroup A) ≤ (P : Subgroup A) ∧
      k • P = P}.ncard = 2 := by
  classical
  let k' : A := a⁻¹ * k * a
  have hnorm : normalizer ((MulAut.conj a • C.L : Subgroup A) : Set A) =
      MulAut.conj a • normalizer (C.L : Set A) :=
    (Subgroup.map_equiv_normalizer_eq C.L (MulAut.conj a)).symm
  have hk'B : k' ∈ C.K₁ := by
    have hk' : k ∈ MulAut.conj a • C.K₁ := by
      rw [hnorm] at hk
      exact hk
    simpa [k'] using mem_conj_smul_iff.mp hk'
  have hk'3 : orderOf k' = 3 := by
    have hk1 : k ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hk3
      norm_num at hk3
    have hk'pow : k' ^ 3 = 1 := by
      have hk3pow : k ^ 3 = 1 := by
        rw [← hk3]
        exact pow_orderOf_eq_one k
      have hk'eq : k' = MulAut.conj a⁻¹ k := by
        simp [k', MulAut.conj_apply]
      rw [hk'eq, ← map_pow, hk3pow, map_one]
    have hk'1 : k' ≠ 1 := by
      intro h
      apply hk1
      have : k = a * k' * a⁻¹ := by dsimp [k']; group
      rw [this, h]
      group
    exact orderOf_eq_prime hk'pow hk'1
  have hiff_le : ∀ P : Sylow 2 A,
      (MulAut.conj a • C.L : Subgroup A) ≤ ((a • P : Sylow 2 A) : Subgroup A) ↔
        C.L ≤ (P : Subgroup A) := by
    intro P
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff
  have hiff_smul : ∀ P : Sylow 2 A, k • (a • P) = a • P ↔ k' • P = P := by
    intro P
    have hsmul : k • (a • P) = a • (k' • P) := by
      rw [smul_smul, smul_smul]
      congr 1
      dsimp [k']
      group
    rw [hsmul]
    constructor
    · intro h
      have := congrArg (fun Q : Sylow 2 A => a⁻¹ • Q) h
      simpa [smul_smul] using this
    · intro h
      rw [h]
  have hset : {P : Sylow 2 A | (MulAut.conj a • C.L : Subgroup A) ≤ (P : Subgroup A) ∧
        k • P = P} =
      (fun P : Sylow 2 A => a • P) ''
        {P : Sylow 2 A | C.L ≤ (P : Subgroup A) ∧ k' • P = P} := by
    ext P
    constructor
    · rintro ⟨hle, hfix⟩
      refine ⟨a⁻¹ • P, ⟨?_, ?_⟩, by simp⟩
      · have hle' : (MulAut.conj a • C.L : Subgroup A) ≤
            ((a • (a⁻¹ • P) : Sylow 2 A) : Subgroup A) := by simpa using hle
        exact (hiff_le (a⁻¹ • P)).mp hle'
      · have hfix' : k • (a • (a⁻¹ • P)) = a • (a⁻¹ • P) := by simpa using hfix
        exact (hiff_smul (a⁻¹ • P)).mp hfix'
    · rintro ⟨Q, ⟨hle, hfix⟩, rfl⟩
      exact ⟨(hiff_le Q).mpr hle, (hiff_smul Q).mpr hfix⟩
  rw [hset]
  have hinj : Function.Injective (fun P : Sylow 2 A => a • P) := by
    intro P Q h
    have := congrArg (fun R : Sylow 2 A => a⁻¹ • R) h
    simpa [smul_smul] using this
  rw [Set.ncard_image_of_injective _ hinj, C.ncard_fixed_sylow_ge_L hk'B hk'3]

private theorem ncard_fixed_sylow_ge_conj_M (C : Config A) [Finite A] (a : A) {k : A}
    (hk : k ∈ normalizer ((MulAut.conj a • C.M : Subgroup A) : Set A))
    (hk3 : orderOf k = 3) :
    {P : Sylow 2 A | (MulAut.conj a • C.M : Subgroup A) ≤ (P : Subgroup A) ∧
      k • P = P}.ncard = 2 := by
  simpa using C.swap.ncard_fixed_sylow_ge_conj_L a hk hk3

theorem ncard_fixed_sylow_ge_line (C : Config A) [Finite A] (P₀ : Sylow 2 A) {k : A}
    (hk : k ∈ normalizer (C.line P₀ : Set A)) (hk3 : orderOf k = 3) :
    {P : Sylow 2 A | C.line P₀ ≤ (P : Subgroup A) ∧ k • P = P}.ncard = 2 := by
  obtain ⟨a, -, hpa⟩ := C.line_spec P₀
  rw [hpa] at hk ⊢
  exact C.ncard_fixed_sylow_ge_conj_M a hk hk3

private theorem zcaseL_inter_fixed_ncard_le (C : Config A) [Finite A] {k : A}
    (hk : k ∈ normalizer (C.T : Set A)) (hk3 : orderOf k = 3) :
    (C.zcaseL ∩ {P : Sylow 2 A | k • P = P}).ncard ≤ 1 := by
  classical
  haveI : Finite (Sylow 2 A) := C.finite_sylowTwo
  have hkK1 : k ∈ C.K₁ := (C.normalizer_T_le hk).1
  have hkT : k • C.T = C.T := (Sylow.smul_eq_iff_mem_normalizer).mpr hk
  have hLset : {P : Sylow 2 A | C.L ≤ (P : Subgroup A) ∧ k • P = P}.ncard = 2 :=
    C.ncard_fixed_sylow_ge_L hkK1 hk3
  have hTmem : C.T ∈ {P : Sylow 2 A | C.L ≤ (P : Subgroup A) ∧ k • P = P} :=
    ⟨C.L_le, hkT⟩
  have hdiffcard : ({P : Sylow 2 A | C.L ≤ (P : Subgroup A) ∧ k • P = P} \
      {C.T}).ncard = 1 := by
    rw [Set.ncard_diff_singleton_of_mem hTmem, hLset]
  obtain ⟨S₁, hS₁⟩ := Set.ncard_eq_one.mp hdiffcard
  have hS₁mem : S₁ ∈ {P : Sylow 2 A | C.L ≤ (P : Subgroup A) ∧ k • P = P} \ {C.T} := by
    rw [hS₁]
    exact Set.mem_singleton _
  obtain ⟨⟨hLS₁, hkS₁⟩, hS₁neT⟩ := hS₁mem
  have hS₁ne : S₁ ≠ C.T := by simpa using hS₁neT
  have hkline : k ∈ normalizer (C.line S₁ : Set A) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h := C.line_smul_sylow k S₁
    rw [hkS₁] at h
    exact h.symm
  have hlineSet : {P : Sylow 2 A | C.line S₁ ≤ (P : Subgroup A) ∧ k • P = P}.ncard = 2 :=
    C.ncard_fixed_sylow_ge_line S₁ hkline hk3
  have hS₁line : S₁ ∈ {P : Sylow 2 A | C.line S₁ ≤ (P : Subgroup A) ∧ k • P = P} :=
    ⟨C.line_le S₁, hkS₁⟩
  have hlineDiff : ({P : Sylow 2 A | C.line S₁ ≤ (P : Subgroup A) ∧ k • P = P} \
      {S₁}).ncard = 1 := by
    rw [Set.ncard_diff_singleton_of_mem hS₁line, hlineSet]
  have hsub : C.zcaseL ∩ {P : Sylow 2 A | k • P = P} ⊆
      ({P : Sylow 2 A | C.line S₁ ≤ (P : Subgroup A) ∧ k • P = P} \ {S₁}) := by
    intro P hP
    obtain ⟨hPL, hPfix⟩ := hP
    obtain ⟨hDleL, hDcard⟩ := hPL
    have hPneT : P ≠ C.T := by
      intro hPT
      rw [hPT, inf_idem, C.card_T] at hDcard
      norm_num at hDcard
    set S : Sylow 2 A := C.centreSylowOf P hDleL hDcard with hSdef
    obtain ⟨hLS, hSneT, hDeq⟩ := C.centreSylowOf_spec P hDleL hDcard
    have hSne : S ≠ C.T := hSneT
    have hptS : C.point S = C.L := C.point_eq_L_of_le hLS
    have hDne : ((C.T : Subgroup A) ⊓ (P : Subgroup A)) ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hDcard
      norm_num at hDcard
    obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDne
    set v : A := (u : A) with hvdef
    have hvD : v ∈ (C.T : Subgroup A) ⊓ (P : Subgroup A) := u.2
    have hv1 : v ≠ 1 := fun h => hu1 (Subtype.ext (by simpa [hvdef] using h))
    have hvT : v ∈ (C.T : Subgroup A) := hvD.1
    have hvP : v ∈ (P : Subgroup A) := hvD.2
    have hvL : v ∈ C.L := hDleL hvD
    have hvLineS : v ∈ C.line S := by
      have hmem : v ∈ C.L ⊓ C.line S := by
        rw [← hDeq]
        exact hvD
      exact hmem.2
    have hzS : v ∈ C.point S ⊓ C.line S := by
      rw [hptS]
      exact ⟨hvL, hvLineS⟩
    have hcentv : centralizer ({v} : Set A) = (S : Subgroup A) :=
      C.centralizer_Z_sylow hzS hv1
    have hfixT : MulAut.conj k • (C.T : Subgroup A) = (C.T : Subgroup A) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hk
    have hfixL : MulAut.conj k • (C.L : Subgroup A) = C.L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hkK1
    have hfixP : MulAut.conj k • (P : Subgroup A) = (P : Subgroup A) := by
      have := congrArg (fun Q : Sylow 2 A => (Q : Subgroup A)) hPfix
      exact this
    have hkvT : k * v * k⁻¹ ∈ (C.T : Subgroup A) := by
      rw [← hfixT, mem_conj_smul_iff]
      have h : k⁻¹ * (k * v * k⁻¹) * k = v := by group
      rwa [h]
    have hkvP : k * v * k⁻¹ ∈ (P : Subgroup A) := by
      rw [← hfixP, mem_conj_smul_iff]
      have h : k⁻¹ * (k * v * k⁻¹) * k = v := by group
      rwa [h]
    have hkvL : k * v * k⁻¹ ∈ C.L := by
      rw [← hfixL, mem_conj_smul_iff]
      have h : k⁻¹ * (k * v * k⁻¹) * k = v := by group
      rwa [h]
    have hkvline : k * v * k⁻¹ ∈ C.line S := by
      have hmem : k * v * k⁻¹ ∈ C.L ⊓ C.line S := by
        rw [← hDeq]
        exact ⟨hkvT, hkvP⟩
      exact hmem.2
    have hkv1 : k * v * k⁻¹ ≠ 1 := by
      intro h
      apply hv1
      have : v = k⁻¹ * (k * v * k⁻¹) * k := by group
      rw [this, h]
      group
    have hzS' : k * v * k⁻¹ ∈ C.point S ⊓ C.line S := by
      rw [hptS]
      exact ⟨hkvL, hkvline⟩
    have hcentkv : centralizer ({k * v * k⁻¹} : Set A) = (S : Subgroup A) :=
      C.centralizer_Z_sylow hzS' hkv1
    have hkS : MulAut.conj k • (S : Subgroup A) = (S : Subgroup A) := by
      have hconj : centralizer ({k * v * k⁻¹} : Set A) =
          MulAut.conj k • centralizer ({v} : Set A) := by
        rw [CFSG.GroupTheory.GL52.centralizer_conj]
        rfl
      rw [hcentkv, hcentv] at hconj
      exact hconj.symm
    have hkS_sylow : k • S = S := Sylow.ext hkS
    have hS_in : S ∈ {P : Sylow 2 A | C.L ≤ (P : Subgroup A) ∧ k • P = P} \ {C.T} :=
      ⟨⟨hLS, hkS_sylow⟩, hSne⟩
    have hSeq : S = S₁ := by
      have : S ∈ ({S₁} : Set (Sylow 2 A)) := by
        rw [← hS₁]
        exact hS_in
      simpa using this
    have hlineS : C.line S₁ ≤ (P : Subgroup A) := by
      rw [← hSeq]
      exact C.line_le_of_inf_eq hLS hSne hDeq
    have hPneS₁ : P ≠ S₁ := by
      intro hPS
      have hDsup : C.L ≤ (C.T : Subgroup A) ⊓ (P : Subgroup A) := by
        rw [hPS]
        exact le_inf C.L_le hLS₁
      have h16 : 16 ≤ Nat.card ↥((C.T : Subgroup A) ⊓ (P : Subgroup A)) := by
        calc 16 = Nat.card ↥C.L := C.card_L.symm
          _ ≤ _ := Subgroup.card_le_of_le hDsup
      omega
    exact ⟨⟨hlineS, hPfix⟩, by simpa using hPneS₁⟩
  calc (C.zcaseL ∩ {P : Sylow 2 A | k • P = P}).ncard
      ≤ ({P : Sylow 2 A | C.line S₁ ≤ (P : Subgroup A) ∧ k • P = P} \ {S₁}).ncard :=
        Set.ncard_le_ncard hsub
    _ = 1 := hlineDiff

theorem ncard_nonopposite_fixed_le (C : Config A) [Finite A] {k : A}
    (hk : k ∈ normalizer (C.T : Set A)) (hk3 : orderOf k = 3) :
    {P : Sylow 2 A | (C.T : Subgroup A) ⊓ (P : Subgroup A) ≠ ⊥ ∧ k • P = P}.ncard ≤ 5 := by
  classical
  haveI : Finite (Sylow 2 A) := C.finite_sylowTwo
  have hkK1 : k ∈ C.K₁ := (C.normalizer_T_le hk).1
  have hkK2 : k ∈ C.K₂ := (C.normalizer_T_le hk).2
  have hkT : k • C.T = C.T := (Sylow.smul_eq_iff_mem_normalizer).mpr hk
  let B : Set (Sylow 2 A) := {P : Sylow 2 A | C.L ≤ (P : Subgroup A) ∧ k • P = P} \ {C.T}
  let C' : Set (Sylow 2 A) := {P : Sylow 2 A | C.M ≤ (P : Subgroup A) ∧ k • P = P} \ {C.T}
  let D : Set (Sylow 2 A) := C.zcaseL ∩ {P : Sylow 2 A | k • P = P}
  let E : Set (Sylow 2 A) := C.zcaseM ∩ {P : Sylow 2 A | k • P = P}
  have h1 : ({C.T} : Set (Sylow 2 A)).ncard = 1 := Set.ncard_singleton _
  have h2 : B.ncard = 1 := by
    show ({P : Sylow 2 A | C.L ≤ (P : Subgroup A) ∧ k • P = P} \ {C.T}).ncard = 1
    rw [Set.ncard_diff_singleton_of_mem
        (show C.T ∈ {P : Sylow 2 A | C.L ≤ (P : Subgroup A) ∧ k • P = P} from
          ⟨C.L_le, hkT⟩),
      C.ncard_fixed_sylow_ge_L hkK1 hk3]
  have h3 : C'.ncard = 1 := by
    show ({P : Sylow 2 A | C.M ≤ (P : Subgroup A) ∧ k • P = P} \ {C.T}).ncard = 1
    rw [Set.ncard_diff_singleton_of_mem
        (show C.T ∈ {P : Sylow 2 A | C.M ≤ (P : Subgroup A) ∧ k • P = P} from
          ⟨C.M_le, hkT⟩),
      C.ncard_fixed_sylow_ge_M hkK2 hk3]
  have h4 : D.ncard ≤ 1 := C.zcaseL_inter_fixed_ncard_le hk hk3
  have h5 : E.ncard ≤ 1 := by
    have h := C.swap.zcaseL_inter_fixed_ncard_le hk hk3
    simpa [E, D, zcaseL, zcaseM] using h
  have hsub : {P : Sylow 2 A | (C.T : Subgroup A) ⊓ (P : Subgroup A) ≠ ⊥ ∧ k • P = P} ⊆
      ((({C.T} : Set (Sylow 2 A)) ∪ B) ∪ C') ∪ D ∪ E := by
    intro P hP
    obtain ⟨hD, hfix⟩ := hP
    by_cases hPT : P = C.T
    · exact Or.inl (Or.inl (Or.inl (Or.inl (by rw [hPT]; exact Set.mem_singleton _))))
    · rcases C.inf_eq_bot_or_L_or_M_or_four hPT with hbot | hL | hM | hfour
      · exact absurd hbot hD
      · have hLP : C.L ≤ (P : Subgroup A) := by
          rw [← hL]
          exact inf_le_right
        exact Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨hLP, hfix⟩, hPT⟩)))
      · have hMP : C.M ≤ (P : Subgroup A) := by
          rw [← hM]
          exact inf_le_right
        exact Or.inl (Or.inl (Or.inr ⟨⟨hMP, hfix⟩, hPT⟩))
      · rcases hfour.1 with hleL | hleM
        · exact Or.inl (Or.inr ⟨⟨hleL, hfour.2⟩, hfix⟩)
        · exact Or.inr ⟨⟨hleM, hfour.2⟩, hfix⟩
  have hU : (((({C.T} : Set (Sylow 2 A)) ∪ B) ∪ C') ∪ D ∪ E).ncard ≤ 5 := by
    have hAB : (({C.T} : Set (Sylow 2 A)) ∪ B).ncard ≤ 2 := by
      have := Set.ncard_union_le ({C.T} : Set (Sylow 2 A)) B
      omega
    have hABC : ((({C.T} : Set (Sylow 2 A)) ∪ B) ∪ C').ncard ≤ 3 := by
      have := Set.ncard_union_le (({C.T} : Set (Sylow 2 A)) ∪ B) C'
      omega
    have hABCD : (((({C.T} : Set (Sylow 2 A)) ∪ B) ∪ C') ∪ D).ncard ≤ 4 := by
      have := Set.ncard_union_le ((({C.T} : Set (Sylow 2 A)) ∪ B) ∪ C') D
      omega
    have := Set.ncard_union_le (((({C.T} : Set (Sylow 2 A)) ∪ B) ∪ C') ∪ D) E
    omega
  calc {P : Sylow 2 A | (C.T : Subgroup A) ⊓ (P : Subgroup A) ≠ ⊥ ∧ k • P = P}.ncard
      ≤ (((({C.T} : Set (Sylow 2 A)) ∪ B) ∪ C') ∪ D ∪ E).ncard := Set.ncard_le_ncard hsub
    _ ≤ 5 := hU

end Config

end CFSG.Quasithin.L34CIT
