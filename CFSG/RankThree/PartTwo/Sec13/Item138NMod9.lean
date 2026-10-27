module

public import CFSG.RankThree.PartTwo.Sec13.Item138N
public import CFSG.RankThree.PartTwo.Sec13.Item13Theta
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec13.Item13K410
import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi zPi PiField ModThree ModNine IsTypeC Type123
  diagE)
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open Matrix

theorem dvd_sl3Order_iff {q : ℕ} (hq : q % 3 = 1) :
    243 ∣ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) ↔ q % 9 = 1 := by
  obtain ⟨b, rfl⟩ : ∃ b, q = 3 * b + 1 := ⟨q / 3, by omega⟩
  have h2 : (3 * b + 1) ^ 2 - 1 = 3 * b * (3 * b + 2) := Nat.sub_eq_of_eq_add (by ring)
  have h3 : (3 * b + 1) ^ 3 - 1 = 9 * b * (3 * b ^ 2 + 3 * b + 1) :=
    Nat.sub_eq_of_eq_add (by ring)
  have e : (3 * b + 1) ^ 3 * (3 * b * (3 * b + 2)) * (9 * b * (3 * b ^ 2 + 3 * b + 1)) =
      27 * (b ^ 2 * ((3 * b + 1) ^ 3 * (3 * b + 2) * (3 * b ^ 2 + 3 * b + 1))) := by ring
  rw [h2, h3, e, show (243 : ℕ) = 27 * 9 by norm_num, Nat.mul_dvd_mul_iff_left (by norm_num)]
  have hU : ¬ 3 ∣ (3 * b + 1) ^ 3 * (3 * b + 2) * (3 * b ^ 2 + 3 * b + 1) := by
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
    · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
      · have := Nat.prime_three.dvd_of_dvd_pow h
        omega
      · omega
    · omega
  have hcop : Nat.Coprime 9 ((3 * b + 1) ^ 3 * (3 * b + 2) * (3 * b ^ 2 + 3 * b + 1)) :=
    Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hU)
  rw [hcop.dvd_mul_right]
  constructor
  · intro h
    have : 3 ∣ b := Nat.prime_three.dvd_of_dvd_pow (dvd_trans (by norm_num) h)
    omega
  · intro h
    obtain ⟨k, rfl⟩ : 3 ∣ b := by omega
    exact ⟨k ^ 2, by ring⟩

theorem dvd_su3Order_iff {q : ℕ} (hq : q % 3 = 2) :
    243 ∣ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) ↔ q % 9 = 8 := by
  obtain ⟨b, rfl⟩ : ∃ b, q = 3 * b + 2 := ⟨q / 3, by omega⟩
  have h2 : (3 * b + 2) ^ 2 - 1 = 3 * (3 * b + 1) * (b + 1) := Nat.sub_eq_of_eq_add (by ring)
  have e : (3 * b + 2) ^ 3 * (3 * (3 * b + 1) * (b + 1)) * ((3 * b + 2) ^ 3 + 1) =
      27 * ((b + 1) ^ 2 * ((3 * b + 2) ^ 3 * (3 * b + 1) * (3 * b ^ 2 + 3 * b + 1))) := by ring
  rw [h2, e, show (243 : ℕ) = 27 * 9 by norm_num, Nat.mul_dvd_mul_iff_left (by norm_num)]
  have hU : ¬ 3 ∣ (3 * b + 2) ^ 3 * (3 * b + 1) * (3 * b ^ 2 + 3 * b + 1) := by
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
    · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
      · have := Nat.prime_three.dvd_of_dvd_pow h
        omega
      · omega
    · omega
  have hcop : Nat.Coprime 9 ((3 * b + 2) ^ 3 * (3 * b + 1) * (3 * b ^ 2 + 3 * b + 1)) :=
    Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hU)
  rw [hcop.dvd_mul_right]
  constructor
  · intro h
    have : 3 ∣ b + 1 := Nat.prime_three.dvd_of_dvd_pow (dvd_trans (by norm_num) h)
    omega
  · intro h
    obtain ⟨k, hk⟩ : 3 ∣ b + 1 := by omega
    exact ⟨k ^ 2, by rw [hk]; ring⟩

theorem modNine_iff_dvd {π : Bool} {q : ℕ} (hq : ModThree π q) :
    ModNine π q ↔ 243 ∣ q ^ 3 * (q ^ 2 - 1) * cond π (q ^ 3 - 1) (q ^ 3 + 1) := by
  cases π
  · exact (dvd_su3Order_iff hq).symm
  · exact (dvd_sl3Order_iff hq).symm

theorem modNine_of_mod_nine {π : Bool} {q : ℕ} (hq : ModThree π q)
    (h9 : q % 9 = 1 ∨ q % 9 = 8) : ModNine π q := by
  cases π
  · change q % 3 = 2 at hq
    change q % 9 = 8
    omega
  · change q % 3 = 1 at hq
    change q % 9 = 1
    omega

section Orders

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem card_slPi_three (hK : PiField π p f K) :
    Nat.card (slPi π 3 (p ^ f) K) =
      (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * cond π ((p ^ f) ^ 3 - 1) ((p ^ f) ^ 3 + 1) := by
  have := hK.finite
  cases π
  · rw [Nat.card_congr (Sec4.slPiFalseEquiv p f K).toEquiv,
      KFacts.card_unitarySU_three hK.unitary]
    rfl
  · let _ := Fintype.ofFinite K
    have hc : Fintype.card K = p ^ f := by
      rw [Fintype.card_eq_nat_card, hK.card]
      rfl
    rw [Nat.card_congr (Sec4.slPiTrueEquiv (p ^ f) K).toEquiv, KFacts.card_SL_three, hc]
    rfl

theorem card_projImage_slPi_mul_three (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    Nat.card (projImage (slPi π 3 (p ^ f) K)) * 3 =
      (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * cond π ((p ^ f) ^ 3 - 1) ((p ^ f) ^ 3 + 1) := by
  set S := slPi π 3 (p ^ f) K
  have h1 : (ProjGenLinGroup.mk.comp S.subtype).range = projImage S := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hS : Nat.card S = Nat.card (ProjGenLinGroup.mk.comp S.subtype).ker *
      Nat.card (projImage S) := by
    rw [← h1, ← Subgroup.index_ker, Subgroup.card_mul_index]
  have hker : (ProjGenLinGroup.mk.comp S.subtype).ker =
      (Subgroup.center (GL (Fin 3) K)).subgroupOf S := by
    ext s
    simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ProjGenLinGroup.mk_eq_one]
  have hk : Nat.card (ProjGenLinGroup.mk.comp S.subtype).ker = 3 := by
    rw [hker, ← Subgroup.card_subtype, Subgroup.subgroupOf_map_subtype, inf_comm,
      card_slPi_inf_center hK hq]
  rw [← card_slPi_three hK, hS, hk, mul_comm]

theorem modNine_iff_dvd_card (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    ModNine π (p ^ f) ↔ 81 ∣ Nat.card (projImage (slPi π 3 (p ^ f) K)) := by
  rw [modNine_iff_dvd hq, ← card_projImage_slPi_mul_three hK hq,
    show (243 : ℕ) = 81 * 3 by norm_num, Nat.mul_dvd_mul_iff_right (by norm_num)]

theorem modNine_of_mulEquiv {X : Type*} [Group X] {K' : Type} [Field K'] {p' f' : ℕ}
    {π' : Bool} (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hK' : PiField π' p' f' K')
    (hq' : ModThree π' (p' ^ f')) (e : X ≃* projImage (slPi π 3 (p ^ f) K))
    (e' : X ≃* projImage (slPi π' 3 (p' ^ f') K')) (h9 : ModNine π (p ^ f)) :
    ModNine π' (p' ^ f') := by
  rw [modNine_iff_dvd_card hK' hq', ← Nat.card_congr (e.symm.trans e').toEquiv]
  exact (modNine_iff_dvd_card hK hq).mp h9

theorem exists_projImage_model {X : Type} [Group X] {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (h : Sec4.IsoLThreePi X p e) :
    ∃ (π : Bool) (K : Type) (_ : Field K), PiField π p e K ∧ ModThree π (p ^ e) ∧
      Nonempty (X ≃* projImage (slPi π 3 (p ^ e) K)) := by
  have hp : p.Prime := Fact.out
  rcases h with ⟨hq3, ⟨φ⟩⟩ | ⟨hq3, ⟨φ⟩⟩
  · refine ⟨true, GaloisField p e, inferInstance, ⟨hp, he, ?_⟩, hq3,
      ⟨φ.trans (MulEquiv.subgroupCongr (Sec4.projSL_eq_projImage _ _))⟩⟩
    rw [GaloisField.card p e (by omega)]
    rfl
  · refine ⟨false, GaloisField p (2 * e), inferInstance, ⟨hp, he, ?_⟩, hq3,
      ⟨φ.trans (MulEquiv.subgroupCongr (Sec4.projSU_eq_projImage _ _))⟩⟩
    rw [GaloisField.card p (2 * e) (by omega)]
    change p ^ (2 * e) = (p ^ e) ^ 2
    rw [← pow_mul, mul_comm]

end Orders

section TypeC

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_inner_of_mem_isTypeC (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h9 : ModNine π (p ^ f)) {D : Subgroup (GL (Fin 3) K)} (hD : IsTypeC π (p ^ f) K D)
    {y : GL (Fin 3) K} (hy : y ∈ D) :
    ∃ l ∈ slPi π 3 (p ^ f) K, ∀ m ∈ slPi π 3 (p ^ f) K, y * m * y⁻¹ = l * m * l⁻¹ := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau hK hq
  have hyH : y ∈ glPi π 3 (p ^ f) K := hD.1 hy
  by_cases hys : y ∈ StatedScalars (Fin 3) K
  · refine ⟨1, one_mem _, fun m _ => ?_⟩
    rw [← Sec4.commute_of_mem_statedScalars hys m]
    group
  · obtain ⟨a₁, -, -, htypes⟩ := Sec4.isTypeC_types hK hq hD
    have h2 := (htypes y hy hys).2
    have hyZ : y ∉ zPi π 3 (p ^ f) K := fun h => hys (by
      rw [Sec4.zPi_eq hπ hq' hτ hτ1] at h
      exact h.2)
    have hy3 : y ^ 3 ∈ zPi π 3 (p ^ f) K := by
      rw [Sec4.zPi_eq hπ hq' hτ hτ1]
      exact ⟨pow_mem hyH 3, hD.2.1 y hy⟩
    by_cases h1 : Type123 π (p ^ f) K y 1
    · obtain ⟨τ', hτ', hτ'1, z, hz, g, hg, hD'⟩ := h1
      exact (Sec4.rank3II_4_10_two hK hq hτ' hτ'1 hyH hyZ hy3).mpr
        (Or.inl ⟨y * z, ⟨z, hz, rfl⟩, g, hg, hD'⟩)
    · obtain ⟨e, he3, he1, z, hz, g, hg, hD'⟩ := h2 h1
      have he1' : (e : K) ≠ 1 := fun h => he1 (Units.ext h)
      exact (Sec4.rank3II_4_10_two hK hq he3 he1' hyH hyZ hy3).mpr
        (Or.inr ⟨⟨y * z, ⟨z, hz, rfl⟩, g, hg, e, Or.inl rfl, hD'⟩, h9⟩)

theorem exists_conj_eq_of_isTypeC {X : Type*} [Group X] (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) (h9 : ModNine π (p ^ f))
    (e : X ≃* projImage (slPi π 3 (p ^ f) K)) {D : Subgroup (GL (Fin 3) K)}
    (hD : IsTypeC π (p ^ f) K D) {τ : MulAut X} {y : GL (Fin 3) K} (hy : y ∈ D)
    (hτ : ∀ z : X, ((e (τ z) : ProjGenLinGroup (Fin 3) K)) =
      ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹) :
    ∃ w : X, ∀ z : X, τ z = w * z * w⁻¹ := by
  obtain ⟨l, hl, hlm⟩ := exists_inner_of_mem_isTypeC hK hq h9 hD hy
  refine ⟨e.symm ⟨ProjGenLinGroup.mk l, Subgroup.mem_map_of_mem _ hl⟩, fun z => ?_⟩
  apply e.injective
  apply Subtype.ext
  obtain ⟨m, hm, hmz⟩ := (e z).2
  rw [hτ z, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [← hmz, ← map_mul, ← map_inv, ← map_mul, hlm m hm, map_mul, map_mul, map_inv]

theorem exists_mk_not_mem_projImage_slPi (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    ∃ g ∈ glPi π 3 (p ^ f) K, ProjGenLinGroup.mk g ∉ projImage (slPi π 3 (p ^ f) K) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have := hK.finite
  set T := rootsOfUnity (Sec4.qSubPi π (p ^ f)) K with hT
  obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set τu : Kˣ := Units.mk0 τ hτ0 with hτu
  have hτu3 : τu ∈ rootsOfUnity 3 K :=
    (mem_rootsOfUnity _ _).mpr (Units.ext (by simp [hτu, hτ]))
  have hτT : τu ∈ T := Sec4.cube_root_mem_qSubPi hq hτu3
  have hns : ¬ Function.Surjective (powMonoidHom 3 : T →* T) := by
    intro hs
    have hinj := Finite.injective_iff_surjective.mpr hs
    have h1 : (powMonoidHom 3 : T →* T) ⟨τu, hτT⟩ = (powMonoidHom 3 : T →* T) 1 := by
      apply Subtype.ext
      simp only [powMonoidHom_apply, SubmonoidClass.mk_pow, one_pow, OneMemClass.coe_one]
      exact (mem_rootsOfUnity _ _).mp hτu3
    have h2 := congrArg (fun t : T => ((t : Kˣ) : K)) (hinj h1)
    exact hτ1 (by simpa [hτu] using h2)
  obtain ⟨μ, hμ⟩ := not_forall.mp hns
  push Not at hμ
  refine ⟨diagE (μ : Kˣ), Sec4.diagUnits_mem_glPi hK μ.2 (one_mem _) (one_mem _), ?_⟩
  rintro ⟨s, hs, hsg⟩
  have hc : s⁻¹ * diagE (μ : Kˣ) ∈ Subgroup.center (GL (Fin 3) K) := by
    rw [← ProjGenLinGroup.mk_eq_one, map_mul, map_inv, hsg, inv_mul_cancel]
  rw [GeneralLinearGroup.center_eq_range_scalar] at hc
  obtain ⟨ℓ, hℓ⟩ := hc
  have hℓH : GeneralLinearGroup.scalar (Fin 3) ℓ ∈ glPi π 3 (p ^ f) K := by
    rw [hℓ]
    exact mul_mem (inv_mem (Sec4.slPi_le_glPi hπ hs))
      (Sec4.diagUnits_mem_glPi hK μ.2 (one_mem _) (one_mem _))
  have hℓT : ℓ ∈ T := (Sec4.scalar_mem_glPi_iff hK ℓ).mp hℓH
  apply hμ ⟨ℓ, hℓT⟩
  apply Subtype.ext
  have hdets : GeneralLinearGroup.det s = 1 :=
    Units.ext (by rw [GeneralLinearGroup.val_det_apply]; exact ((Sec4.mem_slPi_iff hπ).mp hs).2)
  have hdet := congrArg GeneralLinearGroup.det hℓ
  rw [map_mul, map_inv, hdets, inv_one, one_mul, Sec4.det_diagE] at hdet
  have hdsc : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) ℓ) = ℓ ^ 3 :=
    Units.ext (by rw [GeneralLinearGroup.val_det_apply, Sec4.det_scalar, Units.val_pow_eq_pow_val])
  rw [hdsc] at hdet
  simpa using hdet

end TypeC

section Bar

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E : Subgroup G}

omit [Finite G] in
theorem exists_mk_mul_of_mem_lBarA (hL : L ∈ thetaComponentsAt 3 c)
    (hEN : E ≤ Subgroup.normalizer (L : Set G))
    (hEH : E ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    {x : Subgroup.normalizer (Subgroup.zpowers c : Set G) ⧸
      aschbacherSolvableCore 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G))}
    (hx : x ∈ lBarA c L E) :
    ∃ (l : G) (hl : l ∈ L) (e : G) (he : e ∈ E),
      x = QuotientGroup.mk' _ ⟨l, le_normalizer_zpowers_of_mem hL hl⟩ *
        QuotientGroup.mk' _ ⟨e, hEH he⟩ := by
  obtain ⟨n, hn, rfl⟩ := hx
  have hn' : (n : G) ∈ ((L ⊔ E : Subgroup G) : Set G) := Subgroup.mem_subgroupOf.mp hn
  rw [Subgroup.coe_mul_of_right_le_normalizer_left L E hEN] at hn'
  obtain ⟨l, hl, e, he, hle⟩ := Set.mem_mul.mp hn'
  refine ⟨l, hl, e, he, ?_⟩
  rw [← map_mul]
  congr 1
  exact Subtype.ext hle.symm

theorem exists_lBar_conj_eq_of_inner (hL : L ∈ thetaComponentsAt 3 c)
    (hEN : E ≤ Subgroup.normalizer (L : Set G))
    (hEH : E ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hinn : ∀ e ∈ E, ∀ hN : e ∈ Subgroup.normalizer (L : Set G),
      ∃ w : L ⧸ aschbacherSolvableCore 3 L, ∀ z,
        Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨e, hN⟩) z = w * z * w⁻¹)
    {x : Subgroup.normalizer (Subgroup.zpowers c : Set G) ⧸
      aschbacherSolvableCore 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G))}
    (hx : x ∈ lBarA c L E) :
    ∃ w ∈ Sec12.lBar c L, ∀ m ∈ Sec12.lBar c L, x * m * x⁻¹ = w * m * w⁻¹ := by
  obtain ⟨l, hl, e, he, rfl⟩ := exists_mk_mul_of_mem_lBarA hL hEN hEH hx
  obtain ⟨w, hw⟩ := hinn e he (hEN he)
  obtain ⟨η, hη⟩ := exists_lBarEquiv hL
  set q := QuotientGroup.mk' (aschbacherSolvableCore 3
    (Subgroup.normalizer (Subgroup.zpowers c : Set G))) with hq
  set wb : Subgroup.normalizer (Subgroup.zpowers c : Set G) ⧸
      aschbacherSolvableCore 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) :=
    (η w).1 with hwb
  set eb := q ⟨e, hEH he⟩ with heb
  set lb := q ⟨l, le_normalizer_zpowers_of_mem hL hl⟩ with hlb
  have key : ∀ n : Subgroup.normalizer (Subgroup.zpowers c : Set G), (n : G) ∈ L →
      eb * q n * eb⁻¹ = wb * q n * wb⁻¹ := by
    intro n hn
    have h1 := congrArg (fun z => ((η z : Sec12.lBar c L) :
        Subgroup.normalizer (Subgroup.zpowers c : Set G) ⧸
          aschbacherSolvableCore 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G))))
      (hw ((⟨(n : G), hn⟩ : L) : L ⧸ aschbacherSolvableCore 3 L))
    simp only [Sec4.thetaQuotMulAut_mk, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
      hη] at h1
    rw [heb, ← map_mul, ← map_inv, ← map_mul]
    exact h1
  refine ⟨lb * wb, mul_mem ⟨_, Subgroup.mem_subgroupOf.mpr hl, rfl⟩ (η w).2, ?_⟩
  rintro _ ⟨n, hn, rfl⟩
  have hk := key n (Subgroup.mem_subgroupOf.mp hn)
  calc lb * eb * q n * (lb * eb)⁻¹ = lb * (eb * q n * eb⁻¹) * lb⁻¹ := by group
    _ = lb * (wb * q n * wb⁻¹) * lb⁻¹ := by rw [hk]
    _ = lb * wb * q n * (lb * wb)⁻¹ := by group

theorem commutator_lBarA_eq (h : Sec13Data G A c L) (hEN : E ≤ Subgroup.normalizer (L : Set G))
    (hEH : E ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    commutator (lBarA c L E) = (Sec12.lBar c L).subgroupOf (lBarA c L E) := by
  have hL := h.mem_thetaComponentsAt
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L E) with hΛ
  have hΛn : Λ.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨_, ⟨z, hz, rfl⟩⟩ := g
    obtain ⟨l, hl, hlx⟩ := hx
    have hzN : (z : G) ∈ Subgroup.normalizer (L : Set G) :=
      sup_le Subgroup.le_normalizer hEN (Subgroup.mem_subgroupOf.mp hz)
    refine ⟨z * l * z⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hzN _).mp (Subgroup.mem_subgroupOf.mp hl)
    · simp only [map_mul, map_inv, hlx, Subgroup.coe_mul, Subgroup.coe_inv]
  set Eb := ((E.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G))).map
    (QuotientGroup.mk' (aschbacherSolvableCore 3
      (Subgroup.normalizer (Subgroup.zpowers c : Set G))))).subgroupOf (lBarA c L E) with hEb
  have hsup : Λ ⊔ Eb = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    obtain ⟨l, hl, e, he, hxe⟩ := exists_mk_mul_of_mem_lBarA hL hEN hEH hx
    have hlA : QuotientGroup.mk' (aschbacherSolvableCore 3
        (Subgroup.normalizer (Subgroup.zpowers c : Set G)))
          ⟨l, le_normalizer_zpowers_of_mem hL hl⟩ ∈ lBarA c L E :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hl))
    have heA : QuotientGroup.mk' (aschbacherSolvableCore 3
        (Subgroup.normalizer (Subgroup.zpowers c : Set G))) ⟨e, hEH he⟩ ∈ lBarA c L E :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right he))
    have e1 : (⟨x, hx⟩ : lBarA c L E) = ⟨_, hlA⟩ * ⟨_, heA⟩ := Subtype.ext hxe
    rw [e1]
    refine Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mpr ⟨_, ?_, rfl⟩)
      (Subgroup.mem_subgroupOf.mpr ⟨_, ?_, rfl⟩)
    · exact Subgroup.mem_subgroupOf.mpr hl
    · exact Subgroup.mem_subgroupOf.mpr he
  have hEcomm : IsMulCommutative Eb := by
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨n₁, hn₁, h₁⟩ := Subgroup.mem_subgroupOf.mp a.2
    obtain ⟨n₂, hn₂, h₂⟩ := Subgroup.mem_subgroupOf.mp b.2
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← h₁, ← h₂, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hEc _ (Subgroup.mem_subgroupOf.mp hn₁) _ (Subgroup.mem_subgroupOf.mp hn₂))
  refine le_antisymm (Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup hEcomm) ?_
  have hΛp : Group.IsPerfect Λ := by
    have := isPerfect_lBar h
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe lBar_le_lBarA).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe lBar_le_lBarA).symm.surjective
  have h1 : (⊤ : Subgroup Λ).map Λ.subtype = Λ := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  calc Λ = (commutator Λ).map Λ.subtype := by rw [hΛp.commutator_eq_top, h1]
    _ = ⁅Λ, Λ⁆ := by rw [commutator_def, Subgroup.map_commutator, h1]
    _ ≤ commutator (lBarA c L E) := Subgroup.commutator_mono le_top le_top

theorem false_of_inner_of_isZ3PGLThreePi (h : Sec13Data G A c L)
    (hEN : E ≤ Subgroup.normalizer (L : Set G))
    (hEH : E ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hinn : ∀ x ∈ lBarA c L E, ∃ w ∈ Sec12.lBar c L, ∀ m ∈ Sec12.lBar c L,
      x * m * x⁻¹ = w * m * w⁻¹)
    (hPGL : Sec8.IsZ3PGLThreePi (lBarA c L E)) : False := by
  obtain ⟨π, p, f, K, _, hK, hq, ⟨φ⟩⟩ := hPGL
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L E) with hΛ
  have hcomm := commutator_lBarA_eq h hEN hEH hEc
  have hq2 : 2 < p ^ f := by
    by_contra hle
    have h2 : p ^ f = 2 := by
      have : 2 ≤ p ^ f := le_trans hK.prime.two_le (Nat.le_self_pow (by have := hK.one_le; omega) _)
      omega
    cases π
    · have hs := isSolvable_projImage_glPi_two hK h2
      have : Group.IsSolvable (lBarA c L E) :=
        Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
      have hΛs : Group.IsSolvable Λ := inferInstance
      have hΛp : Group.IsPerfect Λ := by
        have := isPerfect_lBar h
        exact Group.IsPerfect.ofSurjective
          (f := (Subgroup.subgroupOfEquivOfLe lBar_le_lBarA).symm.toMonoidHom)
          (Subgroup.subgroupOfEquivOfLe lBar_le_lBarA).symm.surjective
      have : Nontrivial (Sec12.lBar c L) :=
        (Subgroup.nontrivial_iff_ne_bot _).mpr (lBar_ne_bot h)
      have : Nontrivial Λ :=
        (Subgroup.subgroupOfEquivOfLe
          (lBar_le_lBarA (c := c) (L := L) (A := E))).surjective.nontrivial
      exact Group.IsPerfect.not_isSolvable Λ hΛs
    · change p ^ f % 3 = 1 at hq
      omega
  have hmap : Λ.map φ.toMonoidHom = (⊥ : Subgroup (Multiplicative (ZMod 3))).prod
      ((projImage (slPi π 3 (p ^ f) K)).subgroupOf (projImage (glPi π 3 (p ^ f) K))) := by
    rw [hΛ, ← hcomm, ← commutator_projImage_glPi hK hq2, ← commutator_zthree_prod, commutator_def,
      Subgroup.map_commutator, Subgroup.map_top_of_surjective _ φ.surjective, commutator_def]
  obtain ⟨g, hg, hgS⟩ := exists_mk_not_mem_projImage_slPi hK hq
  set gb : projImage (glPi π 3 (p ^ f) K) :=
    ⟨ProjGenLinGroup.mk g, Subgroup.mem_map_of_mem _ hg⟩ with hgb
  set x : lBarA c L E := φ.symm (1, gb) with hx
  obtain ⟨w, hw, hwx⟩ := hinn x x.2
  set w' : lBarA c L E := ⟨w, lBar_le_lBarA hw⟩ with hw'
  have hφw : φ w' ∈ Λ.map φ.toMonoidHom :=
    Subgroup.mem_map_of_mem φ.toMonoidHom (Subgroup.mem_subgroupOf.mpr hw)
  rw [hmap] at hφw
  obtain ⟨h₀, hh₀, hh₀w⟩ := Subgroup.mem_subgroupOf.mp hφw.2
  have hcomm' : ∀ s ∈ slPi π 3 (p ^ f) K,
      ProjGenLinGroup.mk (h₀⁻¹ * g) * ProjGenLinGroup.mk s =
        ProjGenLinGroup.mk s * ProjGenLinGroup.mk (h₀⁻¹ * g) := by
    intro s hs
    set sb : projImage (glPi π 3 (p ^ f) K) :=
      ⟨ProjGenLinGroup.mk s, Subgroup.mem_map_of_mem _ (Sec4.slPi_le_glPi hπ hs)⟩ with hsb
    have hsΛ : ((1 : Multiplicative (ZMod 3)), sb) ∈ Λ.map φ.toMonoidHom := by
      rw [hmap]
      exact ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_map_of_mem _ hs)⟩
    obtain ⟨m, hm, hφm⟩ := hsΛ
    have h2 : x * m * x⁻¹ = w' * m * w'⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hwx _ (Subgroup.mem_subgroupOf.mp hm)
    have hφx : φ x = (1, gb) := by
      rw [hx]
      exact φ.apply_symm_apply _
    have hφm' : φ m = (1, sb) := hφm
    have h3 := congrArg φ h2
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hφx, hφm'] at h3
    have h4 := congrArg (fun y => ((y.2 : projImage (glPi π 3 (p ^ f) K)) :
      ProjGenLinGroup (Fin 3) K)) h3
    simp only [Prod.snd_mul, Prod.snd_inv, Subgroup.coe_mul, Subgroup.coe_inv] at h4
    rw [← hh₀w] at h4
    have h5 : ProjGenLinGroup.mk g * ProjGenLinGroup.mk s * (ProjGenLinGroup.mk g)⁻¹ =
        ProjGenLinGroup.mk h₀ * ProjGenLinGroup.mk s * (ProjGenLinGroup.mk h₀)⁻¹ := h4
    rw [map_mul, map_inv]
    calc (ProjGenLinGroup.mk h₀)⁻¹ * ProjGenLinGroup.mk g * ProjGenLinGroup.mk s =
        (ProjGenLinGroup.mk h₀)⁻¹ * (ProjGenLinGroup.mk g * ProjGenLinGroup.mk s *
          (ProjGenLinGroup.mk g)⁻¹) * ProjGenLinGroup.mk g := by group
      _ = (ProjGenLinGroup.mk h₀)⁻¹ * (ProjGenLinGroup.mk h₀ * ProjGenLinGroup.mk s *
          (ProjGenLinGroup.mk h₀)⁻¹) * ProjGenLinGroup.mk g := by rw [h5]
      _ = ProjGenLinGroup.mk s * ((ProjGenLinGroup.mk h₀)⁻¹ * ProjGenLinGroup.mk g) := by group
  have hsc := mem_statedScalars_of_commute_mk hK hq hq2 hcomm'
  have h1 : ProjGenLinGroup.mk (h₀⁻¹ * g) = 1 := Sec4.mk_eq_one_iff_mem_statedScalars.mpr hsc
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact hgS ⟨h₀, hh₀, h1⟩

end Bar

section Main

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem not_modNine_of_isTypeCOn (h : Sec13Data G A c L) (hcE : c ∈ E)
    (hE3 : CFSG.Assembly.IsElemAbelian 3 E) (hEN : E ≤ Subgroup.normalizer (L : Set G))
    (hC : Sec4.IsTypeCOn E L) (hPGL : Sec8.IsZ3PGLThreePi (lBarA c L E)) {p e : ℕ}
    [Fact p.Prime] (he : 1 ≤ e) (hiso : Sec4.IsoLThreePi (L ⧸ aschbacherSolvableCore 3 L) p e) :
    ¬ (p ^ e % 9 = 1 ∨ p ^ e % 9 = 8) := by
  intro h9
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE3.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hEH : E ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun x hx =>
    centralizer_le_normalizer_zpowers c
      (Subgroup.mem_centralizer_singleton_iff.mpr (hEc x hx c hcE))
  obtain ⟨π, p', f, K, _, hK, hq, φ, D, hD, hτD, -⟩ := hC
  obtain ⟨π₀, K₀, _, hK₀, hq₀, ⟨φ₀⟩⟩ := exists_projImage_model he hiso
  have h9' : ModNine π (p' ^ f) :=
    modNine_of_mulEquiv hK₀ hq₀ hK hq φ₀ φ (modNine_of_mod_nine hq₀ h9)
  have hinn : ∀ e' ∈ E, ∀ hN : e' ∈ Subgroup.normalizer (L : Set G),
      ∃ w : L ⧸ aschbacherSolvableCore 3 L, ∀ z,
        Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨e', hN⟩) z = w * z * w⁻¹ := by
    intro e' he' hN
    obtain ⟨y, hy, hyz⟩ := hτD _ (Sec4.mem_autThetaQuot_iff.mpr ⟨e', hN, he', rfl⟩)
    exact exists_conj_eq_of_isTypeC hK hq h9' φ hD hy hyz
  exact false_of_inner_of_isZ3PGLThreePi h hEN hEH hEc
    (fun x hx => exists_lBar_conj_eq_of_inner h.mem_thetaComponentsAt hEN hEH hinn hx) hPGL

theorem item138Mod9N : Item138Mod9N := by
  intro G _ _ A c L E hH hPGL _ p e _ he hiso
  obtain ⟨h, -, hcE, hE3, -, hEN, -, -, hC⟩ := hH
  exact not_modNine_of_isTypeCOn h hcE hE3 hEN hC hPGL he hiso

theorem rank3II_13_8N_of_three_steps (hEx : Item138ExistsN) (hMain : Item138MainN)
    (hΩ : Item138OmegaN) : Item138N :=
  rank3II_13_8N_of_steps hEx hMain item138Mod9N hΩ

end Main

end CFSG.RankThree.PartTwo.Sec13
