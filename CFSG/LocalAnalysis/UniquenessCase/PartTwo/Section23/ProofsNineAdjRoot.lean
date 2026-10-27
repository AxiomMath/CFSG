module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Bar2TransferSL3
public import CFSG.Adapters.StatedSLPerfect
public import CFSG.Models.PGLSimple
public import CFSG.GroupTheory.FixedPointQuotientCard
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveLine
public import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
public import CFSG.SignalizerFunctorTheorem.Quadratic.ThompsonJ

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.Assembly.LowTwoRank
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

theorem isPerfect_of_isSLn_two {m : ℕ} (hm : 2 ≤ m)
    (h : CFSG.LocalAnalysis.UniquenessCase.PartTwo.IsSLn X 2 m) :
    Group.IsPerfect X := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  letI := hKf
  letI := hKfin
  letI : Fintype K := Fintype.ofFinite K
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  haveI : Group.IsPerfect ↥(StatedSL 2 K) :=
    CFSG.Open.StatedAPI.isPerfect_statedSL_two_of_four_le_card hK4
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem isSimpleGroup_of_isSLn_two {m : ℕ} (hm : 2 ≤ m)
    (h : CFSG.LocalAnalysis.UniquenessCase.PartTwo.IsSLn X 2 m) :
    IsSimpleGroup X := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  letI := hKf
  letI := hKfin
  letI : Fintype K := Fintype.ofFinite K
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hK2 : Nat.card K ≠ 2 := by omega
  have hK3 : Nat.card K ≠ 3 := by omega
  have hKeven : Fintype.card K % 2 = 0 := by
    rw [Fintype.card_eq_nat_card, hKcard]
    exact Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 2 (by omega))
  have hchar : ringChar K = 2 :=
    (FiniteField.even_card_iff_char_two (F := K)).mpr hKeven
  haveI : CharP K 2 := hchar ▸ ringChar.charP K
  have hbot : (StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K) = ⊥ :=
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot
  let q : StatedProj (StatedSL 2 K) ≃* ↥(StatedSL 2 K) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  haveI : IsSimpleGroup (StatedProj (StatedSL 2 K)) :=
    CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL K (d := 2) (by norm_num)
      (Or.inr hK2) (Or.inr hK3)
  haveI : IsSimpleGroup ↥(StatedSL 2 K) := q.symm.isSimpleGroup
  exact e.isSimpleGroup

theorem isL2_of_isSLn_two {m : ℕ} (hm : 2 ≤ m)
    (h : CFSG.LocalAnalysis.UniquenessCase.PartTwo.IsSLn X 2 m) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.IsL2 X m := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  letI := hKf
  letI := hKfin
  letI : Fintype K := Fintype.ofFinite K
  have hKeven : Fintype.card K % 2 = 0 := by
    rw [Fintype.card_eq_nat_card, hKcard]
    exact Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 2 (by omega))
  have hchar : ringChar K = 2 :=
    (FiniteField.even_card_iff_char_two (F := K)).mpr hKeven
  haveI : CharP K 2 := hchar ▸ ringChar.charP K
  have hbot : (StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K) = ⊥ :=
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot
  let q : StatedProj (StatedSL 2 K) ≃* ↥(StatedSL 2 K) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  have h4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hadm : StatedLieAdmissible .PSL 2 2 m := by
    refine ⟨Nat.prime_two, by omega, by omega, ?_, ?_⟩
    · intro h
      have h2 : 2 ^ m = 2 := congrArg Prod.snd h
      rw [h2] at h4
      omega
    · intro h
      have h3 : 2 ^ m = 3 := congrArg Prod.snd h
      rw [h3] at h4
      omega
  exact Or.inl ⟨by decide, ⟨hadm, K, hKf, hKfin, hKcard, ⟨e.trans q.symm⟩⟩⟩

theorem pCore_eq_bot_of_isSLn_two {m : ℕ} (hm : 2 ≤ m)
    (h : CFSG.LocalAnalysis.UniquenessCase.PartTwo.IsSLn X 2 m) :
    CFSG.pCore 2 X = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup X := isSimpleGroup_of_isSLn_two hm h
  have hp : ¬ IsPGroup 2 X := by
    intro hP
    obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
    letI := hKf
    letI := hKfin
    letI : Fintype K := Fintype.ofFinite K
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    have hcard : Nat.card X = Nat.card K * (Nat.card K ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two K]
    have h3 : 3 ∣ Nat.card K ^ 2 - 1 := by
      rw [hKcard, ← pow_mul, show (2 : ℕ) ^ (m * 2) = 4 ^ m by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, Nat.mul_comm]]
      simpa using Nat.sub_one_dvd_pow_sub_one 4 m
    have h3X : 3 ∣ Nat.card X := by
      rw [hcard]
      simpa [Nat.mul_comm] using Dvd.dvd.mul_right h3 (Nat.card K)
    have h3pow : 3 ∣ 2 ^ n := by
      rw [← hn]
      exact h3X
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3pow
    omega
  haveI : (CFSG.pCore 2 X).Normal := CFSG.pCore_normal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 X) with hbot | htop
  · exact hbot
  · have hpc : IsPGroup 2 ↥(CFSG.pCore 2 X) := CFSG.pCore_isPGroup (p := 2) (G := X)
    rw [htop] at hpc
    exact absurd (hpc.of_equiv Subgroup.topEquiv) hp

theorem not_dvd_orderOf_div_of_ker {X Y : Type} [Group X] [Finite X] [Group Y]
    {f : X →* Y} {H : Subgroup X} (hker : f.ker = H) (hH : IsPGroup 2 H)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {u : Y} (hu : orderOf u = r)
    {d : X} (hdu : f d = u) : ¬ r ∣ orderOf d / r := by
  intro hdvd
  have hdiv : r ∣ orderOf d := by
    rw [← hu, ← hdu]
    exact orderOf_map_dvd f d
  have hdsord : orderOf (d ^ (orderOf d / r)) = r :=
    orderOf_pow_orderOf_div (by exact (orderOf_pos d).ne') hdiv
  have hpow : u ^ (orderOf d / r) = 1 :=
    (orderOf_dvd_iff_pow_eq_one (x := u) (n := orderOf d / r)).mp (by
      rw [hu]
      exact hdvd)
  have hdsH : d ^ (orderOf d / r) ∈ H := by
    rw [← hker, MonoidHom.mem_ker, map_pow, hdu, hpow]
  obtain ⟨k, hk⟩ := IsPGroup.exists_orderOf_dvd_pow (p := 2) hH
    (⟨d ^ (orderOf d / r), hdsH⟩ : ↥H)
  have hrk : r ∣ 2 ^ k := by
    rw [← hdsord]
    simpa [Subgroup.orderOf_mk] using hk
  have hr2' : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
    (hr.dvd_of_dvd_pow hrk)
  exact hr2 hr2'

private theorem exists_coprime_mul_modEq_one {m r : ℕ} (hr : r.Prime)
    (hcop : Nat.Coprime m r) :
    ∃ q : ℕ, 0 < q ∧ q < r ∧ Nat.Coprime q r ∧ m * q ≡ 1 [MOD r] := by
  obtain ⟨q, hq_lt, hq⟩ :=
    Nat.exists_mul_mod_eq_one_of_coprime (n := m) (k := r) hcop hr.one_lt
  have hqpos : 0 < q := by
    by_contra h
    rw [Nat.not_lt] at h
    have hq0 : q = 0 := Nat.eq_zero_of_le_zero h
    rw [hq0, Nat.mul_zero, Nat.zero_mod] at hq
    omega
  have hqr : Nat.Coprime q r := by
    rw [Nat.coprime_comm, hr.coprime_iff_not_dvd]
    intro hdvd
    have hq0 : q = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hq_lt
    omega
  refine ⟨q, hqpos, hq_lt, hqr, ?_⟩
  rw [Nat.ModEq, Nat.mod_eq_of_lt hr.one_lt]
  exact hq

theorem exists_pow_orderOf_eq_prime_of_ker {X Y : Type} [Group X] [Finite X] [Group Y]
    {f : X →* Y} {H : Subgroup X} (hker : f.ker = H) (hH : IsPGroup 2 H)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {u : Y} (hu : orderOf u = r)
    {d : X} (hdu : f d = u) :
    ∃ e : ℕ, e ≡ 0 [MOD (orderOf d / r)] ∧ e ≡ 1 [MOD r] ∧
      orderOf (d ^ e) = r ∧ f (d ^ e) = u := by
  have hdiv : r ∣ orderOf d := by
    rw [← hu, ← hdu]
    exact orderOf_map_dvd f d
  have hnot : ¬ r ∣ orderOf d / r :=
    not_dvd_orderOf_div_of_ker hker hH hr hr2 hu hdu
  have hcop : Nat.Coprime (orderOf d / r) r := by
    rw [Nat.coprime_comm]
    exact (hr.coprime_iff_not_dvd).mpr hnot
  obtain ⟨q, hqpos, hq_lt, hqr, he1⟩ := exists_coprime_mul_modEq_one hr hcop
  have he0 : orderOf d / r * q ≡ 0 [MOD (orderOf d / r)] :=
    (Nat.modEq_zero_iff_dvd).mpr ⟨q, rfl⟩
  have hdsord : orderOf (d ^ (orderOf d / r)) = r :=
    orderOf_pow_orderOf_div (by exact (orderOf_pos d).ne') hdiv
  have hord : orderOf (d ^ (orderOf d / r * q)) = r := by
    rw [pow_mul]
    have hcop' : Nat.Coprime (orderOf (d ^ (orderOf d / r))) q := by
      rw [hdsord]
      exact hqr.symm
    rw [hcop'.orderOf_pow, hdsord]
  have hue : u ^ (orderOf d / r * q) = u := by
    have hmod : orderOf d / r * q ≡ 1 [MOD orderOf u] := by
      rw [hu]
      exact he1
    simpa using (pow_eq_pow_iff_modEq (x := u)).mpr hmod
  refine ⟨orderOf d / r * q, he0, he1, hord, ?_⟩
  rw [map_pow, hdu, hue]

end CFSG.GroupTheory

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC PartTwo Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G}

structure S23_9_AdjRootData (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (Xstar : Subgroup ↥(c.H hV)) (b : G) (r m : ℕ) where
  X : Subgroup G
  hXK : X ≤ Hinf (D.M ⊓ c.L)
  hXperf : ⁅X, X⁆ = X
  hXsl : IsSLn (Bar2 X) 2 m
  hbX : b ∈ Subgroup.normalizer (X : Set G)
  dRoot : G
  hdX : dRoot ∈ X
  hdorder : orderOf dRoot = r
  hdb : dRoot * b = b * dRoot
  hinner : ∀ x ∈ X,
    b * x * b⁻¹ * (dRoot * x * dRoot⁻¹)⁻¹ ∈ (CFSG.pCore 2 ↥X).map X.subtype
  hmap : (X.subgroupOf c.L).map (c.phiL hV) = Xstar

@[expose] noncomputable def rootLift (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (Xstar : Subgroup ↥(c.H hV)) : Subgroup G :=
  Hinf (Hinf (D.M ⊓ c.L) ⊓ (Xstar.comap (c.phiL hV)).map c.L.subtype)

theorem rootLift_le_K (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (Xstar : Subgroup ↥(c.H hV)) : rootLift c hV Xstar ≤ Hinf (D.M ⊓ c.L) :=
  (uc22p21c_Hinf_le _).trans inf_le_left

theorem rootLift_le_L (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (Xstar : Subgroup ↥(c.H hV)) : rootLift c hV Xstar ≤ c.L :=
  (rootLift_le_K c hV Xstar).trans ((uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_right)

theorem rootLift_perfect (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (Xstar : Subgroup ↥(c.H hV)) :
    ⁅rootLift c hV Xstar, rootLift c hV Xstar⁆ = rootLift c hV Xstar :=
  uc22p21c_Hinf_perfect _

theorem map_rootLift_subgroupOf (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {Xstar : Subgroup ↥(c.H hV)}
    (hXle : Xstar ≤ ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV))
    (hXperf : ⁅Xstar, Xstar⁆ = Xstar) :
    ((rootLift c hV Xstar).subgroupOf c.L).map (c.phiL hV) = Xstar := by
  let K' : Subgroup ↥c.L := (Hinf (D.M ⊓ c.L)).subgroupOf c.L
  let Y : Subgroup ↥c.L := Xstar.comap (c.phiL hV)
  let A : Subgroup G := Hinf (D.M ⊓ c.L) ⊓ Y.map c.L.subtype
  have hAcL : A ≤ c.L :=
    inf_le_left.trans ((uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_right)
  have hAeq : A.subgroupOf c.L = K' ⊓ Y := by
    apply Subgroup.map_subtype_inj.mp
    rw [Subgroup.map_subgroupOf_eq_of_le hAcL,
      Subgroup.map_inf _ _ _ (Subgroup.subtype_injective _),
      Subgroup.map_subgroupOf_eq_of_le
        ((uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_right)]
  have hsub : (rootLift c hV Xstar).subgroupOf c.L = Hinf (K' ⊓ Y) := by
    rw [rootLift]
    change (CFSG.inSubgroup CFSG.perfectResidual A).subgroupOf c.L = Hinf (K' ⊓ Y)
    rw [CFSG.RankThree.PartTwo.KFacts.subgroupOf_inSubgroup_perfectResidual hAcL]
    simpa only [Hinf] using congrArg Hinf hAeq
  have hmap : (K' ⊓ Y).map (c.phiL hV) = Xstar := by
    have hle : Xstar ≤ K'.map (c.phiL hV) := by
      simpa only [K'] using hXle
    simpa only [Y] using
      CFSG.SignalizerFunctorTheorem.Quadratic.ThompsonJAux.map_inf_comap_of_le
        (T := K') (E := Xstar) (f := c.phiL hV) hle
  have hHinf : Hinf Xstar = Xstar :=
    CFSG.RankThree.inSubgroup_perfectResidual_of_isPerfect
      (Subgroup.isPerfect_iff.mpr hXperf)
  rw [hsub, CFSG.LocalAnalysis.UniquenessCase.UC22.Hinf_map, hmap, hHinf]

private theorem mem_normalizer_comap_of_mem_normalizer
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {Xstar : Subgroup ↥(c.H hV)} {b : G} (hbL : b ∈ c.L)
    (ht : c.phiL hV ⟨b, hbL⟩ ∈ Subgroup.normalizer (Xstar : Set ↥(c.H hV))) :
    (⟨b, hbL⟩ : ↥c.L) ∈
      Subgroup.normalizer ((Xstar.comap (c.phiL hV) : Subgroup ↥c.L) : Set ↥c.L) := by
  let bL : ↥c.L := ⟨b, hbL⟩
  let t : ↥(c.H hV) := c.phiL hV bL
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [Subgroup.mem_comap] at hy ⊢
    have h := (Subgroup.mem_normalizer_iff.mp ht (c.phiL hV y)).mp hy
    simpa [t, map_mul, map_inv] using h
  · intro hy
    rw [Subgroup.mem_comap] at hy ⊢
    have hy' : t * c.phiL hV y * t⁻¹ ∈ Xstar := by
      simpa [t, map_mul, map_inv] using hy
    exact (Subgroup.mem_normalizer_iff.mp ht (c.phiL hV y)).mpr hy'

private theorem map_conj_comap_subtype_eq
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {Xstar : Subgroup ↥(c.H hV)} {b : G} (hbL : b ∈ c.L)
    (hYnorm : (⟨b, hbL⟩ : ↥c.L) ∈
      Subgroup.normalizer ((Xstar.comap (c.phiL hV) : Subgroup ↥c.L) : Set ↥c.L)) :
    b ∈ Subgroup.normalizer
      (((Xstar.comap (c.phiL hV)).map c.L.subtype : Subgroup G) : Set G) := by
  let bL : ↥c.L := ⟨b, hbL⟩
  let Y : Subgroup ↥c.L := Xstar.comap (c.phiL hV)
  let Z : Subgroup G := Y.map c.L.subtype
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change Z.map (MulAut.conj b).toMonoidHom = Z
  calc Z.map (MulAut.conj b).toMonoidHom
      = (Y.map c.L.subtype).map (MulAut.conj b).toMonoidHom := rfl
    _ = Y.map ((MulAut.conj b).toMonoidHom.comp c.L.subtype) :=
        Subgroup.map_map Y (MulAut.conj b).toMonoidHom c.L.subtype
    _ = Y.map (c.L.subtype.comp (MulAut.conj bL).toMonoidHom) := by
        congr 1
    _ = (Y.map (MulAut.conj bL).toMonoidHom).map c.L.subtype :=
        (Subgroup.map_map Y c.L.subtype (MulAut.conj bL).toMonoidHom).symm
    _ = Z := by
        have hYeq : Y.map (MulAut.conj bL).toMonoidHom = Y :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mp hYnorm
        simpa only [Z] using congrArg (Subgroup.map c.L.subtype) hYeq

theorem mem_normalizer_rootLift (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {Xstar : Subgroup ↥(c.H hV)} {b : G} (hbL : b ∈ c.L) (hbM : b ∈ D.M)
    (ht : c.phiL hV ⟨b, hbL⟩ ∈ Subgroup.normalizer (Xstar : Set ↥(c.H hV))) :
    b ∈ Subgroup.normalizer (rootLift c hV Xstar : Set G) := by
  let bL : ↥c.L := ⟨b, hbL⟩
  let K0 : Subgroup G := Hinf (D.M ⊓ c.L)
  let Y : Subgroup ↥c.L := Xstar.comap (c.phiL hV)
  let Z : Subgroup G := Y.map c.L.subtype
  let A : Subgroup G := K0 ⊓ Z
  have hbML : b ∈ D.M ⊓ c.L := ⟨hbM, hbL⟩
  have hKnorm : b ∈ Subgroup.normalizer (K0 : Set G) := by
    simpa only [K0, Hinf] using
      (CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
        (D.M ⊓ c.L)) (Subgroup.le_normalizer (H := D.M ⊓ c.L) hbML)
  have hYnorm : bL ∈ Subgroup.normalizer (Y : Set ↥c.L) :=
    mem_normalizer_comap_of_mem_normalizer c hV hbL ht
  have hZnorm : b ∈ Subgroup.normalizer (Z : Set G) :=
    map_conj_comap_subtype_eq c hV hbL hYnorm
  have hAnorm : b ∈ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hKnorm hZnorm ⊢
    rw [Subgroup.map_inf _ _ _ (MulAut.conj b).injective, hKnorm, hZnorm]
  have hA' : b ∈ Subgroup.normalizer (Hinf (K0 ⊓ Z) : Set G) := by
    simpa only [Hinf] using
      (CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
        (K0 ⊓ Z)) hAnorm
  simpa only [rootLift, A, K0, Z, Y] using hA'

@[expose] noncomputable def rootLiftHom (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {m : ℕ} {Xstar : Subgroup ↥(c.H hV)}
    (hXle : Xstar ≤ ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV))
    (hm2 : 2 ≤ m) (hXsl : IsSLn Xstar 2 m) :
    ↥(rootLift c hV Xstar) →* ↥Xstar := by
  have hXperf : ⁅Xstar, Xstar⁆ = Xstar :=
    Subgroup.isPerfect_iff.mp (CFSG.GroupTheory.isPerfect_of_isSLn_two hm2 hXsl)
  let g : ↥(rootLift c hV Xstar) →* ↥(c.H hV) :=
    (c.phiL hV).comp (Subgroup.inclusion (rootLift_le_L c hV Xstar))
  exact g.codRestrict Xstar fun x => by
    have hx : g x ∈ ((rootLift c hV Xstar).subgroupOf c.L).map (c.phiL hV) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr x.2)
    rwa [map_rootLift_subgroupOf c hV hXle hXperf] at hx

theorem rootLiftHom_apply (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {m : ℕ} {Xstar : Subgroup ↥(c.H hV)}
    (hXle : Xstar ≤ ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV))
    (hm2 : 2 ≤ m) (hXsl : IsSLn Xstar 2 m) (x : ↥(rootLift c hV Xstar)) :
    (rootLiftHom c hV hXle hm2 hXsl x : ↥(c.H hV)) =
      c.phiL hV ⟨(x : G), rootLift_le_L c hV Xstar x.2⟩ := rfl

theorem rootLiftHom_surjective (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {m : ℕ} {Xstar : Subgroup ↥(c.H hV)}
    (hXle : Xstar ≤ ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV))
    (hm2 : 2 ≤ m) (hXsl : IsSLn Xstar 2 m) :
    Function.Surjective (rootLiftHom c hV hXle hm2 hXsl) := by
  have hXperf : ⁅Xstar, Xstar⁆ = Xstar :=
    Subgroup.isPerfect_iff.mp (CFSG.GroupTheory.isPerfect_of_isSLn_two hm2 hXsl)
  intro y
  have hy : (y : ↥(c.H hV)) ∈ ((rootLift c hV Xstar).subgroupOf c.L).map (c.phiL hV) := by
    rw [map_rootLift_subgroupOf c hV hXle hXperf]
    exact y.2
  obtain ⟨x, hx, hxφ⟩ := Subgroup.mem_map.mp hy
  refine ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, ?_⟩
  exact Subtype.ext hxφ

theorem rootLiftHom_conj_normalizer (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {m : ℕ} {Xstar : Subgroup ↥(c.H hV)}
    (hXle : Xstar ≤ ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV))
    (hm2 : 2 ≤ m) (hXsl : IsSLn Xstar 2 m) {g : G} (hgL : g ∈ c.L)
    (hgN : g ∈ Subgroup.normalizer (rootLift c hV Xstar : Set G))
    (y : ↥(rootLift c hV Xstar)) :
    (rootLiftHom c hV hXle hm2 hXsl
        ((Subgroup.normalizerMonoidHom (rootLift c hV Xstar)) ⟨g, hgN⟩ y) :
      ↥(c.H hV)) =
      c.phiL hV ⟨g, hgL⟩ * (rootLiftHom c hV hXle hm2 hXsl y : ↥(c.H hV)) *
        (c.phiL hV ⟨g, hgL⟩)⁻¹ := by
  rw [rootLiftHom_apply]
  have hval : ((Subgroup.normalizerMonoidHom (rootLift c hV Xstar)) ⟨g, hgN⟩ y : G) =
      g * (y : G) * g⁻¹ :=
    Subgroup.normalizerMonoidHom_apply_apply_coe _ ⟨g, hgN⟩ y
  have hcle : (⟨((Subgroup.normalizerMonoidHom (rootLift c hV Xstar)) ⟨g, hgN⟩ y : G),
      rootLift_le_L c hV Xstar
        ((Subgroup.normalizerMonoidHom (rootLift c hV Xstar)) ⟨g, hgN⟩ y).2⟩ : ↥c.L) =
      ⟨g, hgL⟩ * ⟨(y : G), rootLift_le_L c hV Xstar y.2⟩ * ⟨g, hgL⟩⁻¹ := by
    apply Subtype.ext
    simpa using hval
  rw [hcle, map_mul, map_mul, map_inv]
  rfl

theorem rootLiftHom_mul_conj (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {m : ℕ} {Xstar : Subgroup ↥(c.H hV)}
    (hXle : Xstar ≤ ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV))
    (hm2 : 2 ≤ m) (hXsl : IsSLn Xstar 2 m) {dRoot : G}
    (hdX : dRoot ∈ rootLift c hV Xstar) {u : ↥(c.H hV)}
    (hdφ : c.phiL hV ⟨dRoot, rootLift_le_L c hV Xstar hdX⟩ = u)
    (y : ↥(rootLift c hV Xstar)) :
    (rootLiftHom c hV hXle hm2 hXsl
        (⟨dRoot, hdX⟩ * y * ⟨dRoot, hdX⟩⁻¹) : ↥(c.H hV)) =
      u * (rootLiftHom c hV hXle hm2 hXsl y : ↥(c.H hV)) * u⁻¹ := by
  rw [map_mul, map_mul, map_inv]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hd : (rootLiftHom c hV hXle hm2 hXsl ⟨dRoot, hdX⟩ : ↥(c.H hV)) = u := by
    rw [rootLiftHom_apply]
    exact hdφ
  rw [hd]

private theorem rootLift_ker_commutator_mem_pCore
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n)
    {m : ℕ} {Xstar : Subgroup ↥(c.H hV)}
    (hXle : Xstar ≤ ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV))
    (hm2 : 2 ≤ m) (hXsl : IsSLn Xstar 2 m) :
    ∀ x ∈ (rootLiftHom c hV hXle hm2 hXsl).ker,
      ∀ y : ↥(rootLift c hV Xstar),
        x * y * x⁻¹ * y⁻¹ ∈ CFSG.pCore 2 ↥(rootLift c hV Xstar) := by
  intro x hx y
  have hx1 : rootLiftHom c hV hXle hm2 hXsl x = 1 := hx
  have hx2 := congrArg Subtype.val hx1
  rw [rootLiftHom_apply] at hx2
  have hxker : (⟨(x : G), rootLift_le_L c hV Xstar x.2⟩ : ↥c.L) ∈ (c.phiL hV).ker := hx2
  have hcomm := c.phiL_ker_commutator_mem_pCore hV hK hnat
    ⟨(x : G), rootLift_le_L c hV Xstar x.2⟩ hxker
    ⟨(y : G), rootLift_le_L c hV Xstar y.2⟩
  have hzL : ((x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹) ∈
      CFSG.Open.pCoreOf 2 c.L := by
    rw [CFSG.Open.pCoreOf]
    exact Subgroup.mem_map.mpr ⟨_, hcomm, rfl⟩
  have hzX : (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ ∈ rootLift c hV Xstar :=
    (rootLift c hV Xstar).mul_mem
      ((rootLift c hV Xstar).mul_mem
        ((rootLift c hV Xstar).mul_mem x.2 y.2) ((rootLift c hV Xstar).inv_mem x.2))
      ((rootLift c hV Xstar).inv_mem y.2)
  have hz := CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 (rootLift_le_L c hV Xstar)
    (Subgroup.mem_inf.mpr ⟨hzX, hzL⟩)
  rw [CFSG.Open.pCoreOf] at hz
  obtain ⟨a, ha, hav⟩ := hz
  rw [show x * y * x⁻¹ * y⁻¹ = a from Subtype.ext (by simpa using hav.symm)]
  exact ha

private theorem rootLift_comap_pCore_eq_and_quotient
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n)
    (hS : KSchurL2) {m : ℕ} {Xstar : Subgroup ↥(c.H hV)}
    (hXle : Xstar ≤ ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV))
    (hm2 : 2 ≤ m) (hXsl : IsSLn Xstar 2 m) :
    (rootLiftHom c hV hXle hm2 hXsl).ker =
        CFSG.pCore 2 ↥(rootLift c hV Xstar) ∧
      Nonempty ((rootLift c hV Xstar) ⧸ CFSG.pCore 2 ↥(rootLift c hV Xstar) ≃*
        ↥Xstar) := by
  have hperfect : ⁅(⊤ : Subgroup ↥(rootLift c hV Xstar)),
      (⊤ : Subgroup ↥(rootLift c hV Xstar))⁆ = ⊤ := by
    haveI : Group.IsPerfect ↥(rootLift c hV Xstar) :=
      Subgroup.isPerfect_iff.mpr (rootLift_perfect c hV Xstar)
    rw [← commutator_def]
    exact Group.IsPerfect.commutator_eq_top
  have hker := rootLift_ker_commutator_mem_pCore c hV hK hnat hXle hm2 hXsl
  have hbot : CFSG.pCore 2 ↥Xstar = ⊥ :=
    CFSG.GroupTheory.pCore_eq_bot_of_isSLn_two hm2 hXsl
  have hIsL2 : IsL2 ↥Xstar m := CFSG.GroupTheory.isL2_of_isSLn_two hm2 hXsl
  have hshape : IsL2 (↥Xstar ⧸ CFSG.pCore 2 ↥Xstar) m ∨
      IsL2Square (↥Xstar ⧸ CFSG.pCore 2 ↥Xstar) m := by
    left
    let e : (↥Xstar ⧸ CFSG.pCore 2 ↥Xstar) ≃* ↥Xstar :=
      (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
    have hLie : CFSG.Blueprint.LieModel ↥Xstar .PSL 2 2 m := hIsL2
    exact CFSG.Blueprint.LieModel.of_mulEquiv e.symm hLie
  exact comap_pCore_eq_of_pCore_eq_bot (rootLiftHom c hV hXle hm2 hXsl)
    (rootLiftHom_surjective c hV hXle hm2 hXsl) hperfect hker hS hshape hbot

theorem ker_rootLiftHom_eq_pCore (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n)
    (hS : KSchurL2) {m : ℕ} {Xstar : Subgroup ↥(c.H hV)}
    (hXle : Xstar ≤ ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV))
    (hm2 : 2 ≤ m) (hXsl : IsSLn Xstar 2 m) :
    (rootLiftHom c hV hXle hm2 hXsl).ker =
      CFSG.pCore 2 ↥(rootLift c hV Xstar) :=
  (rootLift_comap_pCore_eq_and_quotient c hV hK hnat hS hXle hm2 hXsl).1

theorem rootLift_quotient_equiv (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n)
    (hS : KSchurL2) {m : ℕ} {Xstar : Subgroup ↥(c.H hV)}
    (hXle : Xstar ≤ ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV))
    (hm2 : 2 ≤ m) (hXsl : IsSLn Xstar 2 m) :
    Nonempty ((rootLift c hV Xstar) ⧸ CFSG.pCore 2 ↥(rootLift c hV Xstar) ≃* ↥Xstar) :=
  (rootLift_comap_pCore_eq_and_quotient c hV hK hnat hS hXle hm2 hXsl).2

theorem isSLn_bar2_rootLift (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n)
    (hS : KSchurL2) {m : ℕ} {Xstar : Subgroup ↥(c.H hV)}
    (hXle : Xstar ≤ ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV))
    (hm2 : 2 ≤ m) (hXsl : IsSLn Xstar 2 m) :
    IsSLn (Bar2 (rootLift c hV Xstar)) 2 m := by
  obtain ⟨e⟩ := rootLift_quotient_equiv c hV hK hnat hS hXle hm2 hXsl
  exact IsSLn.of_mulEquiv e.symm hXsl

private noncomputable def rootLiftCoset (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {m : ℕ} {Xstar : Subgroup ↥(c.H hV)}
    (hXle : Xstar ≤ ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV))
    (hm2 : 2 ≤ m) (hXsl : IsSLn Xstar 2 m) (u : ↥(c.H hV)) (hu : u ∈ Xstar) :
    Set ↥(rootLift c hV Xstar) :=
  {y | rootLiftHom c hV hXle hm2 hXsl y = ⟨u, hu⟩}

private noncomputable def rootLiftAction (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {m : ℕ} {Xstar : Subgroup ↥(c.H hV)}
    (hXle : Xstar ≤ ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV))
    (hm2 : 2 ≤ m) (hXsl : IsSLn Xstar 2 m) {b : G}
    (hbX : b ∈ Subgroup.normalizer (rootLift c hV Xstar : Set G)) :
    Subgroup.zpowers b →* MulAut ↥(rootLift c hV Xstar) :=
  (Subgroup.normalizerMonoidHom (rootLift c hV Xstar)).comp
    (Subgroup.inclusion (Subgroup.zpowers_le_of_mem hbX))

private theorem rootLiftHom_conj_coset_iff
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {m : ℕ} {Xstar : Subgroup ↥(c.H hV)}
    (hXle : Xstar ≤ ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV))
    (hm2 : 2 ≤ m) (hXsl : IsSLn Xstar 2 m) {b : G} {u : ↥(c.H hV)} {hu : u ∈ Xstar}
    (hb : b ∈ c.B0)
    (hbX : b ∈ Subgroup.normalizer (rootLift c hV Xstar : Set G))
    (hact : ∀ x ∈ Xstar, c.phiL hV ⟨b, c.hL0L (c.hB0.1 hb)⟩ * x *
      (c.phiL hV ⟨b, c.hL0L (c.hB0.1 hb)⟩)⁻¹ = u * x * u⁻¹)
    (y : ↥(rootLift c hV Xstar)) :
    (rootLiftHom c hV hXle hm2 hXsl
        ((Subgroup.normalizerMonoidHom (rootLift c hV Xstar)) ⟨b, hbX⟩ y) :
        ↥(c.H hV)) = u ↔
      (rootLiftHom c hV hXle hm2 hXsl y : ↥(c.H hV)) = u := by
  let bL : ↥c.L := ⟨b, c.hL0L (c.hB0.1 hb)⟩
  let t : ↥(c.H hV) := c.phiL hV bL
  have htut : t * u * t⁻¹ = u := by
    have := hact u hu
    simpa [t, bL] using this
  have htu : u * t = t * u := (mul_inv_eq_iff_eq_mul.mp htut).symm
  have hconj : ∀ z : ↥(c.H hV), t * z * t⁻¹ = u ↔ z = u := by
    intro z
    constructor
    · intro h
      calc z = t⁻¹ * (t * z * t⁻¹) * t := by group
        _ = t⁻¹ * (u * t) := by rw [h]; group
        _ = t⁻¹ * (t * u) := by rw [htu]
        _ = u := by group
    · intro h
      rw [h, htut]
  rw [rootLiftHom_conj_normalizer c hV hXle hm2 hXsl bL.2 hbX y]
  exact hconj _

private theorem rootLift_fixed_point_hfix
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {m : ℕ} {Xstar : Subgroup ↥(c.H hV)}
    (hXle : Xstar ≤ ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV))
    (hm2 : 2 ≤ m) (hXsl : IsSLn Xstar 2 m) {b : G} {u : ↥(c.H hV)} {hu : u ∈ Xstar}
    (hb : b ∈ c.B0)
    (hbX : b ∈ Subgroup.normalizer (rootLift c hV Xstar : Set G))
    (hact : ∀ x ∈ Xstar, c.phiL hV ⟨b, c.hL0L (c.hB0.1 hb)⟩ * x *
      (c.phiL hV ⟨b, c.hL0L (c.hB0.1 hb)⟩)⁻¹ = u * x * u⁻¹) :
    ∀ a : Subgroup.zpowers b, ∀ y : ↥(rootLift c hV Xstar),
      rootLiftHom c hV hXle hm2 hXsl
          (rootLiftAction c hV hXle hm2 hXsl hbX a y) = ⟨u, hu⟩ ↔
        rootLiftHom c hV hXle hm2 hXsl y = ⟨u, hu⟩ := by
  let A : Subgroup G := Subgroup.zpowers b
  let bA : A := ⟨b, Subgroup.mem_zpowers b⟩
  have hbA : b ∈ Subgroup.normalizer (rootLift c hV Xstar : Set G) :=
    (Subgroup.zpowers_le_of_mem hbX) bA.2
  let α : A →* MulAut ↥(rootLift c hV Xstar) := rootLiftAction c hV hXle hm2 hXsl hbX
  letI : MulAction A ↥(rootLift c hV Xstar) := MulAction.compHom _ α
  let T : Set ↥(rootLift c hV Xstar) := rootLiftCoset c hV hXle hm2 hXsl u hu
  have hcoe : ∀ w : ↥Xstar, (w = ⟨u, hu⟩) ↔ ((w : ↥(c.H hV)) = u) := by
    intro w
    rw [Subtype.ext_iff]
  have hgen : bA ∈ MulAction.stabilizer A T := by
    rw [MulAction.mem_stabilizer_set]
    intro y
    change α bA y ∈ T ↔ y ∈ T
    change rootLiftHom c hV hXle hm2 hXsl (α bA y) = ⟨u, hu⟩ ↔
      rootLiftHom c hV hXle hm2 hXsl y = ⟨u, hu⟩
    rw [hcoe (rootLiftHom c hV hXle hm2 hXsl (α bA y)),
      hcoe (rootLiftHom c hV hXle hm2 hXsl y)]
    exact rootLiftHom_conj_coset_iff (hu := hu) c hV hXle hm2 hXsl hb hbA hact y
  have htop : MulAction.stabilizer A T = ⊤ := by
    have hz : Subgroup.zpowers bA = ⊤ := CFSG.zpowers_self_eq_top b
    exact top_le_iff.mp (hz ▸ Subgroup.zpowers_le.mpr hgen)
  intro a y
  have ha : a ∈ MulAction.stabilizer A T := by
    rw [htop]
    exact Subgroup.mem_top a
  have hmem := MulAction.mem_stabilizer_set.mp ha y
  change α a y ∈ T ↔ y ∈ T at hmem
  change rootLiftHom c hV hXle hm2 hXsl (α a y) = ⟨u, hu⟩ ↔
    rootLiftHom c hV hXle hm2 hXsl y = ⟨u, hu⟩ at hmem
  exact hmem

private theorem rootLift_invariant_coset
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {m : ℕ} {Xstar : Subgroup ↥(c.H hV)}
    (hXle : Xstar ≤ ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV))
    (hm2 : 2 ≤ m) (hXsl : IsSLn Xstar 2 m) {u : ↥(c.H hV)} {hu : u ∈ Xstar}
    {A : Subgroup G} (α : A →* MulAut ↥(rootLift c hV Xstar))
    (d0 : ↥(rootLift c hV Xstar))
    (hd0 : rootLiftHom c hV hXle hm2 hXsl d0 = ⟨u, hu⟩)
    (hker : (rootLiftHom c hV hXle hm2 hXsl).ker =
      CFSG.pCore 2 ↥(rootLift c hV Xstar))
    (hfix : ∀ a : A, ∀ y : ↥(rootLift c hV Xstar),
      rootLiftHom c hV hXle hm2 hXsl (α a y) = ⟨u, hu⟩ ↔
        rootLiftHom c hV hXle hm2 hXsl y = ⟨u, hu⟩) :
    ∀ a : A, ∀ y : ↥(rootLift c hV Xstar),
      d0⁻¹ * y ∈ CFSG.pCore 2 ↥(rootLift c hV Xstar) →
      d0⁻¹ * α a y ∈ CFSG.pCore 2 ↥(rootLift c hV Xstar) := by
  intro a y hy
  have hyT : rootLiftHom c hV hXle hm2 hXsl y = ⟨u, hu⟩ := by
    have h1 : rootLiftHom c hV hXle hm2 hXsl (d0⁻¹ * y) = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact hy
    have h2 : rootLiftHom c hV hXle hm2 hXsl y =
        rootLiftHom c hV hXle hm2 hXsl d0 *
          rootLiftHom c hV hXle hm2 hXsl (d0⁻¹ * y) := by
      rw [← map_mul]
      congr 1
      group
    rw [h2, hd0, h1, mul_one]
  have hstep : rootLiftHom c hV hXle hm2 hXsl (α a y) = ⟨u, hu⟩ :=
    (hfix a y).mpr hyT
  have h1 : rootLiftHom c hV hXle hm2 hXsl (d0⁻¹ * α a y) = 1 := by
    have h2 : rootLiftHom c hV hXle hm2 hXsl (d0⁻¹ * α a y) =
        (rootLiftHom c hV hXle hm2 hXsl d0)⁻¹ *
          rootLiftHom c hV hXle hm2 hXsl (α a y) := by
      rw [map_mul, map_inv]
    rw [h2, hd0, hstep]
    simp
  rw [← hker, MonoidHom.mem_ker]
  exact h1

private theorem exists_fixed_lift_of_coprime
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {m : ℕ} {Xstar : Subgroup ↥(c.H hV)}
    (hXle : Xstar ≤ ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV))
    (hm2 : 2 ≤ m) (hXsl : IsSLn Xstar 2 m) {b : G} {u : ↥(c.H hV)} {hu : u ∈ Xstar}
    {r : ℕ}
    {A : Subgroup G} [Finite A] (α : A →* MulAut ↥(rootLift c hV Xstar))
    {bA : A}
    (hαb : ∀ d : ↥(rootLift c hV Xstar),
      (α bA d : G) = b * (d : G) * b⁻¹)
    (hr : r.Prime) (hr2 : r ≠ 2) (hA : IsPGroup r A)
    (d0 : ↥(rootLift c hV Xstar))
    (hd0 : rootLiftHom c hV hXle hm2 hXsl d0 = ⟨u, hu⟩)
    (hker : (rootLiftHom c hV hXle hm2 hXsl).ker =
      CFSG.pCore 2 ↥(rootLift c hV Xstar))
    (hinv : ∀ a : A, ∀ y : ↥(rootLift c hV Xstar),
      d0⁻¹ * y ∈ CFSG.pCore 2 ↥(rootLift c hV Xstar) →
      d0⁻¹ * α a y ∈ CFSG.pCore 2 ↥(rootLift c hV Xstar)) :
    ∃ d : ↥(rootLift c hV Xstar),
      rootLiftHom c hV hXle hm2 hXsl d = ⟨u, hu⟩ ∧ (d : G) * b = b * (d : G) := by
  letI : Fact r.Prime := ⟨hr⟩
  let X : Subgroup G := rootLift c hV Xstar
  let f : ↥X →* ↥Xstar := rootLiftHom c hV hXle hm2 hXsl
  let H : Subgroup ↥X := CFSG.pCore 2 ↥X
  have hcop : ¬ r ∣ Nat.card H := by
    have hHp : IsPGroup 2 H := CFSG.pCore_isPGroup (p := 2) (G := ↥X)
    obtain ⟨k, hk⟩ := hHp.exists_card_eq
    rw [hk]
    intro hdvd
    have hr2' : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
      (hr.dvd_of_dvd_pow hdvd)
    exact hr2 hr2'
  obtain ⟨d, hdH, hdfix⟩ :=
    (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed r hA α H hcop d0).2 hinv
  have hdφ : f d = ⟨u, hu⟩ := by
    have h1 : f (d0⁻¹ * d) = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact hdH
    have h2 : f d = f d0 * f (d0⁻¹ * d) := by
      rw [← map_mul]
      congr 1
      group
    rw [h2, hd0, h1, mul_one]
  have hdb : (d : G) * b = b * (d : G) := by
    have hfix := hdfix bA
    have h := congrArg Subtype.val hfix
    rw [hαb d] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  exact ⟨d, hdφ, hdb⟩

theorem exists_fixed_lift_rootLift (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n)
    (hS : KSchurL2) {m : ℕ} {Xstar : Subgroup ↥(c.H hV)} {b : G} {u : ↥(c.H hV)} {r : ℕ}
    (hb : b ∈ c.B0) {hu : u ∈ Xstar} (hr : r.Prime) (hr2 : r ≠ 2)
    (hborder : orderOf b = r)
    (ht : c.phiL hV ⟨b, c.hL0L (c.hB0.1 hb)⟩ ∈
      Subgroup.normalizer (Xstar : Set ↥(c.H hV)))
    (hXle : Xstar ≤ ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV))
    (hm2 : 2 ≤ m) (hXsl : IsSLn Xstar 2 m)
    (huord : orderOf u = r)
    (hact : ∀ x ∈ Xstar, c.phiL hV ⟨b, c.hL0L (c.hB0.1 hb)⟩ * x *
      (c.phiL hV ⟨b, c.hL0L (c.hB0.1 hb)⟩)⁻¹ = u * x * u⁻¹) :
    ∃ d : ↥(rootLift c hV Xstar),
      rootLiftHom c hV hXle hm2 hXsl d = ⟨u, hu⟩ ∧
      (d : G) * b = b * (d : G) := by
  have hbL : b ∈ c.L := c.hL0L (c.hB0.1 hb)
  let X : Subgroup G := rootLift c hV Xstar
  let f : ↥X →* ↥Xstar := rootLiftHom c hV hXle hm2 hXsl
  have hker : f.ker = CFSG.pCore 2 ↥X :=
    ker_rootLiftHom_eq_pCore c hV hK hnat hS hXle hm2 hXsl
  obtain ⟨d0, hd0⟩ := rootLiftHom_surjective c hV hXle hm2 hXsl ⟨u, hu⟩
  have htb : b ∈ Subgroup.normalizer (X : Set G) :=
    mem_normalizer_rootLift c hV hbL (c.hBM hb) ht
  let A : Subgroup G := Subgroup.zpowers b
  let bA : A := ⟨b, Subgroup.mem_zpowers b⟩
  have hbA : b ∈ Subgroup.normalizer (X : Set G) :=
    (Subgroup.zpowers_le_of_mem htb) bA.2
  have hfix := rootLift_fixed_point_hfix (hu := hu) c hV hXle hm2 hXsl hb htb hact
  have hinv := rootLift_invariant_coset (hu := hu) c hV hXle hm2 hXsl
    (rootLiftAction c hV hXle hm2 hXsl htb) d0 hd0 hker hfix
  have hA : IsPGroup r A := by
    apply IsPGroup.of_card
    change Nat.card (Subgroup.zpowers b) = r ^ 1
    rw [Nat.card_zpowers, hborder, pow_one]
  have hαb : ∀ d : ↥X,
      (rootLiftAction c hV hXle hm2 hXsl htb bA d : G) = b * (d : G) * b⁻¹ :=
    fun d => Subgroup.normalizerMonoidHom_apply_apply_coe X ⟨b, hbA⟩ d
  exact exists_fixed_lift_of_coprime c hV hXle hm2 hXsl
    (rootLiftAction c hV hXle hm2 hXsl htb) (hu := hu) hαb hr hr2 hA d0 hd0 hker hinv

private theorem exists_rootLift_pow
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {m : ℕ} {Xstar : Subgroup ↥(c.H hV)}
    (hXle : Xstar ≤ ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV))
    (hm2 : 2 ≤ m) (hXsl : IsSLn Xstar 2 m) {b : G} {u : ↥(c.H hV)} {hu : u ∈ Xstar}
    {r : ℕ} (d : ↥(rootLift c hV Xstar))
    (hdφ : rootLiftHom c hV hXle hm2 hXsl d = ⟨u, hu⟩)
    (hdb : (d : G) * b = b * (d : G))
    (hker : (rootLiftHom c hV hXle hm2 hXsl).ker =
      CFSG.pCore 2 ↥(rootLift c hV Xstar))
    (hH : IsPGroup 2 (CFSG.pCore 2 ↥(rootLift c hV Xstar)))
    (hr : r.Prime) (hr2 : r ≠ 2) (huord : orderOf u = r) :
    ∃ dRoot : ↥(rootLift c hV Xstar),
      orderOf (dRoot : G) = r ∧ ((dRoot : G) * b = b * (dRoot : G)) ∧
        c.phiL hV ⟨(dRoot : G), rootLift_le_L c hV Xstar dRoot.2⟩ = u := by
  let f : ↥(rootLift c hV Xstar) →* ↥Xstar := rootLiftHom c hV hXle hm2 hXsl
  obtain ⟨e, -, -, hdord, hdeφ⟩ :=
    CFSG.GroupTheory.exists_pow_orderOf_eq_prime_of_ker (f := f)
      (H := CFSG.pCore 2 ↥(rootLift c hV Xstar)) hker hH hr hr2
      (u := (⟨u, hu⟩ : ↥Xstar)) (by simpa [Subgroup.orderOf_mk] using huord) hdφ
  refine ⟨d ^ e, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact hdord
  · have hcomm : Commute (d : G) b := hdb
    simpa [Subgroup.coe_pow] using (hcomm.pow_left e).eq
  · have h := congrArg Subtype.val hdeφ
    rw [rootLiftHom_apply] at h
    simpa using h

private theorem rootLift_inner_condition
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {m : ℕ} {Xstar : Subgroup ↥(c.H hV)}
    (hXle : Xstar ≤ ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV))
    (hm2 : 2 ≤ m) (hXsl : IsSLn Xstar 2 m) {b : G} {u : ↥(c.H hV)}
    (hb : b ∈ c.B0)
    (hbX : b ∈ Subgroup.normalizer (rootLift c hV Xstar : Set G))
    {dRoot : G} (hdX : dRoot ∈ rootLift c hV Xstar)
    (hdRootφ : c.phiL hV ⟨dRoot, rootLift_le_L c hV Xstar hdX⟩ = u)
    (hker : (rootLiftHom c hV hXle hm2 hXsl).ker =
      CFSG.pCore 2 ↥(rootLift c hV Xstar))
    (hact : ∀ x ∈ Xstar, c.phiL hV ⟨b, c.hL0L (c.hB0.1 hb)⟩ * x *
      (c.phiL hV ⟨b, c.hL0L (c.hB0.1 hb)⟩)⁻¹ = u * x * u⁻¹) :
    ∀ x ∈ rootLift c hV Xstar,
      b * x * b⁻¹ * (dRoot * x * dRoot⁻¹)⁻¹ ∈
        (CFSG.pCore 2 ↥(rootLift c hV Xstar)).map (rootLift c hV Xstar).subtype := by
  let X : Subgroup G := rootLift c hV Xstar
  let f : ↥X →* ↥Xstar := rootLiftHom c hV hXle hm2 hXsl
  let H : Subgroup ↥X := CFSG.pCore 2 ↥X
  let bL : ↥c.L := ⟨b, c.hL0L (c.hB0.1 hb)⟩
  let t : ↥(c.H hV) := c.phiL hV bL
  intro x hx
  let xX : ↥X := ⟨x, hx⟩
  let bAct : ↥X := (Subgroup.normalizerMonoidHom X) ⟨b, hbX⟩ xX
  let dAct : ↥X := ⟨dRoot, hdX⟩ * xX * ⟨dRoot, hdX⟩⁻¹
  let zX : ↥X := bAct * dAct⁻¹
  have hzval : (zX : G) = b * x * b⁻¹ * (dRoot * x * dRoot⁻¹)⁻¹ := by
    simp [zX, bAct, dAct, xX, Subgroup.normalizerMonoidHom_apply_apply_coe,
      Subgroup.coe_mul, Subgroup.coe_inv]
  have hfb : (f bAct : ↥(c.H hV)) = t * (f xX) * t⁻¹ := by
    simpa [f, bAct, xX, t, bL] using
      rootLiftHom_conj_normalizer c hV hXle hm2 hXsl bL.2 hbX xX
  have hfd : (f dAct : ↥(c.H hV)) = u * (f xX) * u⁻¹ := by
    simpa [f, dAct, xX] using
      rootLiftHom_mul_conj c hV hXle hm2 hXsl hdX hdRootφ xX
  have hfz : f zX = 1 := by
    apply Subtype.ext
    rw [map_mul, map_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hfb, hfd]
    rw [← hact (f xX) (f xX).2]
    simp [t, bL]
  have hzpc : zX ∈ CFSG.pCore 2 ↥X := by
    rw [← hker, MonoidHom.mem_ker]
    exact hfz
  rw [← hzval]
  exact Subgroup.mem_map.mpr ⟨zX, hzpc, rfl⟩

theorem exists_rootLift_data (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n)
    (hS : KSchurL2) {m : ℕ} {Xstar : Subgroup ↥(c.H hV)} {b : G} {u : ↥(c.H hV)} {r : ℕ}
    (hb : b ∈ c.B0) (hr : r.Prime) (hr2 : r ≠ 2) (hborder : orderOf b = r)
    (ht : c.phiL hV ⟨b, c.hL0L (c.hB0.1 hb)⟩ ∈
      Subgroup.normalizer (Xstar : Set ↥(c.H hV)))
    (hXle : Xstar ≤ ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV))
    (hm2 : 2 ≤ m) (hXsl : IsSLn Xstar 2 m) (hu : u ∈ Xstar) (huord : orderOf u = r)
    (hact : ∀ x ∈ Xstar, c.phiL hV ⟨b, c.hL0L (c.hB0.1 hb)⟩ * x *
      (c.phiL hV ⟨b, c.hL0L (c.hB0.1 hb)⟩)⁻¹ = u * x * u⁻¹) :
    Nonempty (S23_9_AdjRootData D Ch c hV Xstar b r m) := by
  have hbL : b ∈ c.L := c.hL0L (c.hB0.1 hb)
  let X : Subgroup G := rootLift c hV Xstar
  let f : ↥X →* ↥Xstar := rootLiftHom c hV hXle hm2 hXsl
  let H : Subgroup ↥X := CFSG.pCore 2 ↥X
  have hker : f.ker = H := ker_rootLiftHom_eq_pCore c hV hK hnat hS hXle hm2 hXsl
  obtain ⟨d, hdφ, hdb⟩ :=
    exists_fixed_lift_rootLift c hV hK hnat hS hb (hu := hu) hr hr2 hborder ht hXle hm2 hXsl
      huord hact
  have hH : IsPGroup 2 H := CFSG.pCore_isPGroup (p := 2) (G := ↥X)
  obtain ⟨dRootX, hdorderX, hdbX, hdRootφX⟩ :=
    exists_rootLift_pow c hV hXle hm2 hXsl d hdφ hdb hker hH hr hr2 huord
  let dRoot : G := dRootX
  have hdX : dRoot ∈ X := dRootX.2
  have hdorder : orderOf dRoot = r := hdorderX
  have hdbRoot : dRoot * b = b * dRoot := hdbX
  have hdRootφ : c.phiL hV ⟨dRoot, rootLift_le_L c hV Xstar hdX⟩ = u := hdRootφX
  have hbX : b ∈ Subgroup.normalizer (X : Set G) :=
    mem_normalizer_rootLift c hV hbL (c.hBM hb) ht
  have hinner := rootLift_inner_condition c hV hXle hm2 hXsl hb hbX hdX hdRootφ hker hact
  have hXperf : ⁅Xstar, Xstar⁆ = Xstar :=
    Subgroup.isPerfect_iff.mp (CFSG.GroupTheory.isPerfect_of_isSLn_two hm2 hXsl)
  exact ⟨{
    X := X
    hXK := rootLift_le_K c hV Xstar
    hXperf := rootLift_perfect c hV Xstar
    hXsl := isSLn_bar2_rootLift c hV hK hnat hS hXle hm2 hXsl
    hbX := hbX
    dRoot := dRoot
    hdX := hdX
    hdorder := hdorder
    hdb := hdbRoot
    hinner := hinner
    hmap := map_rootLift_subgroupOf c hV hXle hXperf }⟩

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
