module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiAct
public import CFSG.RankThree.PartTwo.Sec4.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open Matrix

section Perfect

variable {K : Type} [Field K]

@[expose] noncomputable def projOf (H : Subgroup (GL (Fin 3) K)) : H →* projImage H :=
  (ProjGenLinGroup.mk : GL (Fin 3) K →* ProjGenLinGroup (Fin 3) K).subgroupMap H

theorem projOf_surjective (H : Subgroup (GL (Fin 3) K)) : Function.Surjective (projOf H) :=
  MonoidHom.subgroupMap_surjective _ _

theorem coe_projOf (H : Subgroup (GL (Fin 3) K)) (s : H) :
    ((projOf H s : projImage H) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (s : GL (Fin 3) K) :=
  rfl

theorem mem_ker_projOf {H : Subgroup (GL (Fin 3) K)} (s : H) :
    s ∈ (projOf H).ker ↔ (s : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := by
  rw [MonoidHom.mem_ker, ← Subtype.coe_inj, coe_projOf, Subgroup.coe_one,
    ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
  rfl

theorem eq_one_of_isPerfect_projImage {H : Subgroup (GL (Fin 3) K)}
    [Group.IsPerfect (projImage H)] {C : Type*} [CommGroup C] (φ : H →* C)
    (hφ : ∀ s : H, (s : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K → φ s = 1) (s : H) :
    φ s = 1 := by
  have hle : (projOf H).ker ≤ φ.ker := fun t ht =>
    (MonoidHom.mem_ker).mpr (hφ t ((mem_ker_projOf t).mp ht))
  let φ₁ : H ⧸ (projOf H).ker →* C := QuotientGroup.lift _ φ hle
  let φ' : projImage H →* C :=
    φ₁.comp (QuotientGroup.quotientKerEquivOfSurjective _ (projOf_surjective H)).symm.toMonoidHom
  have hker : φ'.ker = ⊤ := by
    rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := projImage H)]
    exact Abelianization.commutator_subset_ker φ'
  have h1 : φ' (projOf H s) = 1 := (MonoidHom.mem_ker).mp (hker ▸ Subgroup.mem_top _)
  have h2 : φ' (projOf H s) = φ s := by
    change φ₁ ((QuotientGroup.quotientKerEquivOfSurjective _ (projOf_surjective H)).symm
      (projOf H s)) = φ s
    have : (QuotientGroup.quotientKerEquivOfSurjective _ (projOf_surjective H)).symm
        (projOf H s) = (s : H ⧸ (projOf H).ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [this]
    rfl
  rw [← h2, h1]

theorem commute_of_comm_mod_scalars {H : Subgroup (GL (Fin 3) K)}
    [Group.IsPerfect (projImage H)] {y : GL (Fin 3) K}
    (hy : ∀ s ∈ H, y * s * y⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) K) :
    ∀ s ∈ H, y * s = s * y := by
  have hc : ∀ s ∈ H, ∃ c : Kˣ, GeneralLinearGroup.scalar (Fin 3) c = y * s * y⁻¹ * s⁻¹ :=
    fun s hs => hy s hs
  choose c hc' using hc
  have hcomm : ∀ (z : GL (Fin 3) K) (u : Kˣ), z * GeneralLinearGroup.scalar (Fin 3) u =
      GeneralLinearGroup.scalar (Fin 3) u * z := fun z u =>
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u z).eq
  have hmul : ∀ s (hs : s ∈ H) t (ht : t ∈ H),
      c (s * t) (mul_mem hs ht) = c s hs * c t ht := by
    intro s hs t ht
    have h1 : GeneralLinearGroup.scalar (Fin 3) (c (s * t) (mul_mem hs ht)) =
        GeneralLinearGroup.scalar (Fin 3) (c s hs * c t ht) := by
      rw [hc', map_mul, hc', hc']
      have e1 : y * t * y⁻¹ * t⁻¹ * s⁻¹ = s⁻¹ * (y * t * y⁻¹ * t⁻¹) := by
        rw [← hc' t ht, ← hcomm]
      calc y * (s * t) * y⁻¹ * (s * t)⁻¹ = (y * s * y⁻¹) * (y * t * y⁻¹ * t⁻¹ * s⁻¹) := by
            group
        _ = (y * s * y⁻¹) * (s⁻¹ * (y * t * y⁻¹ * t⁻¹)) := by rw [e1]
        _ = _ := by group
    have h2 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 0 0) h1
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq] at h2
    exact Units.ext h2
  let φ : H →* Kˣ :=
    { toFun := fun s => c s s.2
      map_one' := by
        have h1 : GeneralLinearGroup.scalar (Fin 3) (c 1 H.one_mem) =
            GeneralLinearGroup.scalar (Fin 3) 1 := by
          rw [hc', map_one]
          group
        have h2 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 0 0) h1
        simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
          Matrix.diagonal_apply_eq] at h2
        exact Units.ext h2
      map_mul' := fun s t => hmul s s.2 t t.2 }
  have hφ := eq_one_of_isPerfect_projImage φ (fun s hs => by
    obtain ⟨u, hu⟩ := hs
    have h1 : GeneralLinearGroup.scalar (Fin 3) (c s s.2) =
        GeneralLinearGroup.scalar (Fin 3) 1 := by
      rw [hc', ← hu, hcomm y u, map_one]
      group
    have h2 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 0 0) h1
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq] at h2
    exact Units.ext h2)
  intro s hs
  have h1 : c s hs = 1 := hφ ⟨s, hs⟩
  have h2 := hc' s hs
  rw [h1, map_one] at h2
  calc y * s = y * s * y⁻¹ * s⁻¹ * (s * y) := by group
    _ = s * y := by rw [← h2, one_mul]

end Perfect

section Model

theorem statedSL_eq_ker_det (K : Type) [Field K] :
    StatedSL 3 K = (GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).ker :=
  CFSG.Open.StatedAPI.statedSL_eq_ker_det 3 K

theorem projSL_eq_projImage (q : ℕ) (K : Type) [Field K] :
    projSL 3 K = projImage (slPi true 3 q K) := by
  rw [projSL]
  exact congrArg projImage (statedSL_eq_ker_det K).symm

theorem projSU_eq_projImage (p f : ℕ) [Fact p.Prime] :
    projSU 3 p f = projImage (slPi false 3 (p ^ f) (GaloisField p (2 * f))) := by
  rw [projSU]
  congr 1
  change _ = StatedSU 3 (p ^ f) _
  rw [StatedSU]
  congr 1
  ext A
  simp [Units.ext_iff]

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem exists_pslPi_model {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e) (hL : IsoLThreePi L p e)
    (hLq : CFSG.IsQuasisimple L) :
    ∃ (π : Bool) (K : Type) (_ : Field K), PiField π p e K ∧ ModThree π (p ^ e) ∧
      2 < p ^ e ∧ Nonempty (L ≃* projImage (slPi π 3 (p ^ e) K)) := by
  have hp : p.Prime := Fact.out
  have hpe2 : 2 ≤ p ^ e := le_trans hp.two_le (Nat.le_self_pow (by omega) _)
  rcases hL with ⟨hq3, ⟨φ⟩⟩ | ⟨hq3, ⟨φ⟩⟩
  · refine ⟨true, GaloisField p e, inferInstance, ⟨hp, he, ?_⟩, hq3, ?_,
      ⟨φ.trans (MulEquiv.subgroupCongr (projSL_eq_projImage _ _))⟩⟩
    · rw [GaloisField.card p e (by omega)]
      rfl
    · by_contra h2
      have : p ^ e = 2 := by omega
      rw [this] at hq3
      norm_num at hq3
  · have hK : PiField false p e (GaloisField p (2 * e)) := ⟨hp, he, by
      rw [GaloisField.card p (2 * e) (by omega)]
      change p ^ (2 * e) = (p ^ e) ^ 2
      rw [← pow_mul, mul_comm]⟩
    refine ⟨false, GaloisField p (2 * e), inferInstance, hK, hq3, ?_,
      ⟨φ.trans (MulEquiv.subgroupCongr (projSU_eq_projImage _ _))⟩⟩
    by_contra h2
    have hpe : p ^ e = 2 := by omega
    have hp2 : p = 2 := by
      have := (Nat.prime_two.eq_one_or_self_of_dvd p ⟨p ^ (e - 1), by
        rw [← pow_succ', Nat.sub_add_cancel he, hpe]⟩)
      rcases this with h | h
      · exact absurd h hp.one_lt.ne'
      · exact h
    have he1 : e = 1 := by
      rw [hp2] at hpe
      exact Nat.pow_right_injective le_rfl (show 2 ^ e = 2 ^ 1 by rw [hpe, pow_one])
    subst hp2
    subst he1
    have hU : UnitaryFieldData 2 1 (GaloisField 2 (2 * 1)) := hK.unitary
    have hcard := CFSG.RankThree.CentralLiftU.card_statedSU_three_two hU rfl
    have := Fintype.ofFinite (StatedSU 3 (2 ^ 1) (GaloisField 2 (2 * 1)))
    have hsolv : Group.IsSolvable (StatedSU 3 (2 ^ 1) (GaloisField 2 (2 * 1))) :=
      CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3) (b := 3)
        Nat.prime_two Nat.prime_three (by norm_num)
        (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
    have hsolv' : Group.IsSolvable (slPi false 3 (2 ^ 1) (GaloisField 2 (2 * 1))) := hsolv
    have h1 : Group.IsSolvable (projImage (slPi false 3 (2 ^ 1) (GaloisField 2 (2 * 1)))) :=
      Group.isSolvable_of_surjective (projOf_surjective (slPi false 3 (2 ^ 1) _))
    have hsolvL : Group.IsSolvable L :=
      Group.isSolvable_of_surjective (f := (φ.trans (MulEquiv.subgroupCongr
        (projSU_eq_projImage _ _))).symm.toMonoidHom) (MulEquiv.surjective _)
    have : Group.IsPerfect L := hLq.1
    have := CFSG.LocalCores.isQuasisimple_nontrivial hLq
    exact Group.IsPerfect.not_isSolvable L hsolvL

end Model

section LiftsP

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem mem_statedScalars_of_comm_mod (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))] {w : GL (Fin 3) K}
    (hw : ∀ s ∈ slPi π 3 (p ^ f) K, w * s * w⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) K) :
    w ∈ StatedScalars (Fin 3) K := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  exact mem_statedScalars_of_commute hπ hq' hτ hτ1 fun s hs =>
    commute_of_comm_mod_scalars hw s hs

theorem mk_eq_one_iff_mem_statedScalars {w : GL (Fin 3) K} :
    ProjGenLinGroup.mk w = 1 ↔ w ∈ StatedScalars (Fin 3) K := by
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
  rfl

theorem center_projImage_eq_bot (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))] :
    Subgroup.center (projImage (slPi π 3 (p ^ f) K)) = ⊥ := by
  rw [eq_bot_iff]
  intro m hm
  obtain ⟨s, rfl⟩ := projOf_surjective _ m
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [coe_projOf, Subgroup.coe_one, mk_eq_one_iff_mem_statedScalars]
  refine mem_statedScalars_of_comm_mod hK hq fun t ht => ?_
  rw [← mk_eq_one_iff_mem_statedScalars]
  have h1 := Subgroup.mem_center_iff.mp hm (projOf _ ⟨t, ht⟩)
  have h2 := congrArg (fun x : projImage (slPi π 3 (p ^ f) K) =>
    (x : ProjGenLinGroup (Fin 3) K)) h1
  simp only [Subgroup.coe_mul, coe_projOf] at h2
  simp only [map_mul, map_inv]
  rw [← h2]
  group

variable {G : Type} [Group G] {L : Subgroup G} [hLn : L.Normal]

@[expose] def IsPGLAtP (e : L ≃* projImage (slPi π 3 (p ^ f) K)) (g : G)
    (y : GL (Fin 3) K) : Prop :=
  y ∈ glPi π 3 (p ^ f) K ∧ ∀ m : projImage (slPi π 3 (p ^ f) K),
    ((slAct e ⟨g, mem_normalizer_of_normal g⟩ m : projImage (slPi π 3 (p ^ f) K)) :
      ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk y * m * (ProjGenLinGroup.mk y)⁻¹

variable (e : L ≃* projImage (slPi π 3 (p ^ f) K))

theorem coe_slAct_eqP (g : G) (m : projImage (slPi π 3 (p ^ f) K)) :
    ((slAct e ⟨g, mem_normalizer_of_normal g⟩ m : projImage (slPi π 3 (p ^ f) K)) :
      ProjGenLinGroup (Fin 3) K) =
      (e ⟨g * (e.symm m : G) * g⁻¹, hLn.conj_mem _ (e.symm m).2 g⟩ :
        ProjGenLinGroup (Fin 3) K) :=
  rfl

theorem slAct_mul_applyP (g h : G) (m : projImage (slPi π 3 (p ^ f) K)) :
    slAct e ⟨g * h, mem_normalizer_of_normal _⟩ m =
      slAct e ⟨g, mem_normalizer_of_normal g⟩ (slAct e ⟨h, mem_normalizer_of_normal h⟩ m) := by
  have : (⟨g * h, mem_normalizer_of_normal _⟩ : Subgroup.normalizer (L : Set G)) =
      ⟨g, mem_normalizer_of_normal g⟩ * ⟨h, mem_normalizer_of_normal h⟩ := rfl
  rw [this, map_mul, MulAut.mul_apply]

theorem isPGLAtP_mul {g h : G} {y z : GL (Fin 3) K} (hg : IsPGLAtP e g y)
    (hh : IsPGLAtP e h z) : IsPGLAtP e (g * h) (y * z) := by
  refine ⟨mul_mem hg.1 hh.1, fun m => ?_⟩
  rw [slAct_mul_applyP, hg.2, hh.2, map_mul]
  group

theorem isPGLAtP_of_mem (hπ : π = false → UnitaryFieldData p f K) {l : G} (hl : l ∈ L)
    {s : GL (Fin 3) K} (hs : s ∈ slPi π 3 (p ^ f) K)
    (hes : ((e ⟨l, hl⟩ : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk s) :
    IsPGLAtP e l s := by
  refine ⟨slPi_le_glPi hπ hs, fun m => ?_⟩
  rw [coe_slAct_eqP]
  have : (⟨l * (e.symm m : G) * l⁻¹, hLn.conj_mem _ (e.symm m).2 l⟩ : L) =
      ⟨l, hl⟩ * e.symm m * (⟨l, hl⟩ : L)⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
    Subgroup.coe_mul, Subgroup.coe_inv, hes]

theorem isPGLAtP_of_mem_centralizer {g : G} (hg : g ∈ Subgroup.centralizer (L : Set G)) :
    IsPGLAtP e g 1 := by
  refine ⟨one_mem _, fun m => ?_⟩
  rw [coe_slAct_eqP, map_one, one_mul, inv_one, mul_one]
  have : (⟨g * (e.symm m : G) * g⁻¹, hLn.conj_mem _ (e.symm m).2 g⟩ : L) = e.symm m := by
    apply Subtype.ext
    change g * (e.symm m : G) * g⁻¹ = e.symm m
    rw [(Subgroup.mem_centralizer_iff.mp hg _ (e.symm m).2).symm, mul_inv_cancel_right]
  rw [this, MulEquiv.apply_symm_apply]

variable {e}

theorem isPGLAtP_inv_mul_mem (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))] {g : G} {y z : GL (Fin 3) K}
    (hy : IsPGLAtP e g y) (hz : IsPGLAtP e g z) : y⁻¹ * z ∈ StatedScalars (Fin 3) K := by
  refine mem_statedScalars_of_comm_mod hK hq fun s hs => ?_
  rw [← mk_eq_one_iff_mem_statedScalars]
  have h1 := hy.2 (projOf _ ⟨s, hs⟩)
  have h2 := hz.2 (projOf _ ⟨s, hs⟩)
  rw [h1, coe_projOf] at h2
  rw [show ProjGenLinGroup.mk (y⁻¹ * z * s * (y⁻¹ * z)⁻¹ * s⁻¹) =
      (ProjGenLinGroup.mk y)⁻¹ * ProjGenLinGroup.mk z * ProjGenLinGroup.mk s *
        ((ProjGenLinGroup.mk y)⁻¹ * ProjGenLinGroup.mk z)⁻¹ * (ProjGenLinGroup.mk s)⁻¹ by
    simp only [map_mul, map_inv]]
  calc (ProjGenLinGroup.mk y)⁻¹ * ProjGenLinGroup.mk z * ProjGenLinGroup.mk s *
        ((ProjGenLinGroup.mk y)⁻¹ * ProjGenLinGroup.mk z)⁻¹ * (ProjGenLinGroup.mk s)⁻¹ =
      (ProjGenLinGroup.mk y)⁻¹ * (ProjGenLinGroup.mk z * ProjGenLinGroup.mk s *
        (ProjGenLinGroup.mk z)⁻¹) * ProjGenLinGroup.mk y * (ProjGenLinGroup.mk s)⁻¹ := by group
    _ = (ProjGenLinGroup.mk y)⁻¹ * (ProjGenLinGroup.mk y * ProjGenLinGroup.mk s *
        (ProjGenLinGroup.mk y)⁻¹) * ProjGenLinGroup.mk y * (ProjGenLinGroup.mk s)⁻¹ := by
          rw [h2]
    _ = 1 := by group

theorem mem_centralizer_of_isPGLAtP_scalar {g : G} {y : GL (Fin 3) K} (hy : IsPGLAtP e g y)
    (hys : y ∈ StatedScalars (Fin 3) K) : g ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h1 := hy.2 (e ⟨l, hl⟩)
  rw [coe_slAct_eqP] at h1
  simp only [MulEquiv.symm_apply_apply] at h1
  have hmk : ProjGenLinGroup.mk y = 1 := mk_eq_one_iff_mem_statedScalars.mpr hys
  rw [hmk, one_mul, inv_one, mul_one] at h1
  have h2 := e.injective (Subtype.ext h1)
  have h3 : g * l * g⁻¹ = l := congrArg Subtype.val h2
  calc l * g = g * l * g⁻¹ * g := by rw [h3]
    _ = g * l := by group

theorem isPGLAtP_mul_scalar {g : G} {y : GL (Fin 3) K} (hy : IsPGLAtP e g y) {μ : Kˣ}
    (hμ : GeneralLinearGroup.scalar (Fin 3) μ ∈ glPi π 3 (p ^ f) K) :
    IsPGLAtP e g (y * GeneralLinearGroup.scalar (Fin 3) μ) := by
  refine ⟨mul_mem hy.1 hμ, fun m => ?_⟩
  have hmk : ProjGenLinGroup.mk (GeneralLinearGroup.scalar (Fin 3) μ) = 1 :=
    mk_eq_one_iff_mem_statedScalars.mpr ⟨μ, rfl⟩
  rw [hy.2 m, map_mul, hmk, mul_one]

theorem isPGLAtP_pow {g : G} {y : GL (Fin 3) K} (hy : IsPGLAtP e g y) (n : ℕ) :
    IsPGLAtP e (g ^ n) (y ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact isPGLAtP_of_mem_centralizer e (Subgroup.one_mem _)
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact isPGLAtP_mul e ih hy

end LiftsP

section PglHomP

variable {G : Type} [Group G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool} {e : L ≃* projImage (slPi π 3 (p ^ f) K)}

@[expose] noncomputable def pglHomP (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))]
    (A' : Subgroup G) (hA' : ∀ a ∈ A', ∃ y, IsPGLAtP e a y) :
    A' →* GL (Fin 3) K ⧸ StatedScalars (Fin 3) K where
  toFun a :=
    ((Classical.choose (hA' a a.2) : GL (Fin 3) K) : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K)
  map_one' := by
    have h1 := Classical.choose_spec (hA' 1 A'.one_mem)
    have h2 : IsPGLAtP e (1 : G) 1 := isPGLAtP_of_mem_centralizer e (Subgroup.one_mem _)
    have h3 := isPGLAtP_inv_mul_mem hK hq h2 h1
    rw [inv_one, one_mul] at h3
    exact (QuotientGroup.eq_one_iff _).mpr h3
  map_mul' a b := by
    have ha := Classical.choose_spec (hA' a a.2)
    have hb := Classical.choose_spec (hA' b b.2)
    have hab := Classical.choose_spec (hA' (a * b) (a * b).2)
    have h := isPGLAtP_mul e ha hb
    have h3 := isPGLAtP_inv_mul_mem hK hq h hab
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq]
    have := inv_mem h3
    rwa [_root_.mul_inv_rev, inv_inv] at this

variable {hK : PiField π p f K} {hq : ModThree π (p ^ f)}
  [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))] {A' : Subgroup G}
  {hA' : ∀ a ∈ A', ∃ y, IsPGLAtP e a y}

theorem pglHomP_apply (a : A') {y : GL (Fin 3) K} (hy : IsPGLAtP e a y) :
    pglHomP hK hq A' hA' a = (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) := by
  change ((Classical.choose (hA' a a.2) : GL (Fin 3) K) :
    GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) = y
  rw [QuotientGroup.eq]
  exact isPGLAtP_inv_mul_mem hK hq (Classical.choose_spec (hA' a a.2)) hy

theorem pglHomP_eq_one_iff (a : A') :
    pglHomP hK hq A' hA' a = 1 ↔ (a : G) ∈ Subgroup.centralizer (L : Set G) := by
  obtain ⟨y, hy⟩ := hA' a a.2
  rw [pglHomP_apply a hy, QuotientGroup.eq_one_iff]
  constructor
  · exact mem_centralizer_of_isPGLAtP_scalar hy
  · intro hc
    have h1 := isPGLAtP_inv_mul_mem hK hq (isPGLAtP_of_mem_centralizer e hc) hy
    rwa [inv_one, one_mul] at h1

theorem ker_pglHomP :
    (pglHomP hK hq A' hA').ker = (Subgroup.centralizer (L : Set G)).subgroupOf A' := by
  ext a
  rw [MonoidHom.mem_ker, pglHomP_eq_one_iff, Subgroup.mem_subgroupOf]

theorem card_eq_card_inf_mul_card_rangeP :
    Nat.card A' = Nat.card (A' ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) *
      Nat.card (pglHomP hK hq A' hA').range := by
  rw [← Subgroup.index_ker (pglHomP hK hq A' hA'),
    ← Subgroup.card_mul_index (pglHomP hK hq A' hA').ker,
    ker_pglHomP, ← Subgroup.inf_subgroupOf_left]
  congr 1
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

theorem range_pglHomP_comm (hcomm : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a) :
    ∀ x ∈ (pglHomP hK hq A' hA').range, ∀ y ∈ (pglHomP hK hq A' hA').range, x * y = y * x := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hcomm a a.2 b b.2)

theorem range_pglHomP_pow (h3 : ∀ a ∈ A', a ^ 3 = 1) :
    ∀ x ∈ (pglHomP hK hq A' hA').range, x ^ 3 = 1 := by
  rintro _ ⟨a, rfl⟩
  rw [← map_pow]
  have : a ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, h3 a a.2, Subgroup.coe_one])
  rw [this, map_one]

theorem mk_mem_range_pglHomP {a : G} (ha : a ∈ A') {y : GL (Fin 3) K} (hy : IsPGLAtP e a y) :
    (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ (pglHomP hK hq A' hA').range :=
  ⟨⟨a, ha⟩, pglHomP_apply ⟨a, ha⟩ hy⟩

theorem exists_isPGLAtP_of_mk_mem {y : GL (Fin 3) K} (hy : y ∈ glPi π 3 (p ^ f) K)
    (hmem : (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ (pglHomP hK hq A' hA').range) :
    ∃ a ∈ A', IsPGLAtP e a y := by
  obtain ⟨a, ha⟩ := hmem
  obtain ⟨z, hz⟩ := hA' a a.2
  rw [pglHomP_apply a hz, QuotientGroup.eq] at ha
  obtain ⟨c, hc⟩ := ha
  refine ⟨a, a.2, hy, fun m => ?_⟩
  have hyz : y = z * GeneralLinearGroup.scalar (Fin 3) c := by rw [hc]; group
  have hmk : ProjGenLinGroup.mk (GeneralLinearGroup.scalar (Fin 3) c) = 1 :=
    mk_eq_one_iff_mem_statedScalars.mpr ⟨c, rfl⟩
  rw [hz.2, hyz, map_mul, hmk, mul_one]

end PglHomP

section DichotomyLinear

variable {K : Type} [Field K] {p f : ℕ}

open CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartTwo.KFacts

@[expose] noncomputable def slToPsl (q : ℕ) (K : Type) [Field K] :
    SpecialLinearGroup (Fin 3) K →* projImage (slPi true 3 q K) :=
  (projOf (slPi true 3 q K)).comp (slPiTrueEquiv q K).symm.toMonoidHom

theorem coe_slToPsl {q : ℕ} (s : SpecialLinearGroup (Fin 3) K) :
    ((slToPsl q K s : projImage (slPi true 3 q K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL s) := by
  change ProjGenLinGroup.mk (((slPiTrueEquiv q K).symm s : slPi true 3 q K) : GL (Fin 3) K) = _
  rw [show (((slPiTrueEquiv q K).symm s : slPi true 3 q K) : GL (Fin 3) K) =
    Matrix.SpecialLinearGroup.toGL s from coe_statedSLEquiv_symm_eq_toGL s]

theorem toGL_map_eq_frobGL (σ : K ≃+* K) (t : SpecialLinearGroup (Fin 3) K) :
    Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map σ.toRingHom t) =
      frobGL σ (Matrix.SpecialLinearGroup.toGL t) := by
  apply Units.ext
  ext i j
  rfl

theorem slToPsl_surjective (q : ℕ) : Function.Surjective (slToPsl q K) :=
  (projOf_surjective _).comp (MulEquiv.surjective _)

theorem ker_slToPsl (q : ℕ) : (slToPsl q K).ker = scalars 3 K := by
  ext s
  have h0 : ((Matrix.SpecialLinearGroup.toGL s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (s : Matrix (Fin 3) (Fin 3) K) := rfl
  rw [MonoidHom.mem_ker, ← Subtype.coe_inj, coe_slToPsl, Subgroup.coe_one,
    mk_eq_one_iff_mem_statedScalars, mem_scalars]
  constructor
  · rintro ⟨c, hc⟩
    have h := congrArg Units.val hc
    rw [GeneralLinearGroup.coe_scalar, h0] at h
    have hdet : (c : K) ^ 3 = 1 := by
      have h1 := congrArg Matrix.det h
      rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, s.2] at h1
      exact h1
    exact ⟨c, Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one]), h.symm⟩
  · rintro ⟨c, -, hc⟩
    refine ⟨c, Units.ext ?_⟩
    rw [GeneralLinearGroup.coe_scalar, h0, hc]

@[expose] noncomputable def pslEquivProjective (q : ℕ) (K : Type) [Field K] :
    projImage (slPi true 3 q K) ≃* projectiveSL 3 K :=
  (QuotientGroup.quotientKerEquivOfSurjective _ (slToPsl_surjective (K := K) q)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (ker_slToPsl q))

theorem pslEquivProjective_slToPsl {q : ℕ} (s : SpecialLinearGroup (Fin 3) K) :
    pslEquivProjective q K (slToPsl q K s) = proj 3 K s := by
  rw [pslEquivProjective, MulEquiv.trans_apply]
  have : (QuotientGroup.quotientKerEquivOfSurjective _ (slToPsl_surjective (K := K) q)).symm
      (slToPsl q K s) = (s : SpecialLinearGroup (Fin 3) K ⧸ (slToPsl q K).ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [this]
  rfl

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem pslAct_pgl_or_field_linear (hK : PiField true p f K)
    (hθ : aschbacherSolvableCore 3 L = ⊥) (e : L ≃* projImage (slPi true 3 (p ^ f) K))
    (x : Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1) :
    (∃ y ∈ glPi true 3 (p ^ f) K, ∀ m : projImage (slPi true 3 (p ^ f) K),
        (slAct e x m : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk y * m * (ProjGenLinGroup.mk y)⁻¹) ∨
    (InducesStdKind L x .field ∧ ∃ f₀ : ℕ, f = 3 * f₀ ∧ ∃ σ : K ≃+* K,
      ((∀ c, σ c = c ^ piCard true (p ^ f₀)) ∨ ∀ c, σ c = c ^ (piCard true (p ^ f₀) ^ 2)) ∧
      ∃ g ∈ glPi true 3 (p ^ f) K, ∀ s (hs : s ∈ slPi true 3 (p ^ f) K),
        (slAct e x (projOf _ ⟨s, hs⟩) : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk (g * frobGL σ s * g⁻¹)) := by
  have := hK.finite
  set ψ := pslEquivProjective (p ^ f) K with hψ
  set e' := (thetaBotEquiv hθ).trans (e.trans ψ) with he'
  have hind := inducedAutHom_thetaBot hθ e ψ x
  set α := MulAut.congr ψ (slAct e x) with hα
  have hα3 : α ^ 3 = 1 := by
    rw [hα, ← map_pow, ← map_pow, hx3, map_one, map_one]
  have hcoe : ∀ s : SpecialLinearGroup (Fin 3) K,
      slAct e x (slToPsl (p ^ f) K s) = ψ.symm (α (proj 3 K s)) := by
    intro s
    rw [hα, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, ← pslEquivProjective_slToPsl (q := p ^ f),
      MulEquiv.symm_apply_apply]
  have hproj : ∀ t : SpecialLinearGroup (Fin 3) K,
      ψ.symm (proj 3 K t) = slToPsl (p ^ f) K t := by
    intro t
    rw [MulEquiv.symm_apply_eq, pslEquivProjective_slToPsl]
  have hslPi : ∀ s (hs : s ∈ slPi true 3 (p ^ f) K),
      projOf _ ⟨s, hs⟩ = slToPsl (p ^ f) K (slPiTrueEquiv (p ^ f) K ⟨s, hs⟩) := by
    intro s hs
    change projOf _ ⟨s, hs⟩ = projOf _ ((slPiTrueEquiv (p ^ f) K).symm
      (slPiTrueEquiv (p ^ f) K ⟨s, hs⟩))
    rw [MulEquiv.symm_apply_apply]
  by_cases hD : α ∈ linearAutGroup 3 K
  · left
    obtain ⟨A, hA⟩ := (mem_linearAutGroup_iff (n := 3) (K := K)).mp hD
    refine ⟨A, mem_glPi_true _ _, fun m => ?_⟩
    obtain ⟨s, rfl⟩ := slToPsl_surjective (K := K) (p ^ f) m
    rw [hcoe, ← hA, conjAut_proj, hproj, coe_slToPsl, coe_slToPsl, toGL_slConjugation, map_mul,
      map_mul, map_inv]
  · right
    refine ⟨InducesStdKind.psl 3 K (le_refl 3) ⟨e', x.2, ?_⟩, ?_⟩
    · change (stdPinnedPSL 3 K).HasKind (inducedAutHom L e' x) .field
      rw [hind]
      exact isField_of_pow_three_eq_one le_rfl hα3 hD
    · obtain ⟨σ, hσ3, H, hαH⟩ := linear_order_three_field_descent le_rfl α hα3 hD
      obtain ⟨h3f, hσc⟩ := eq_frobenius_pow_of_orderOf_eq_three hK.prime hK.one_le
        (hK.card : Nat.card K = p ^ f) hσ3
      obtain ⟨f₀, rfl⟩ := h3f
      have hf₀ : 3 * f₀ / 3 = f₀ := by omega
      have hf₀' : 2 * (3 * f₀) / 3 = 2 * f₀ := by omega
      refine ⟨f₀, rfl, σ, ?_, H * frobGL σ H⁻¹, mem_glPi_true _ _, fun s hs => ?_⟩
      · rcases hσc with h | h
        · exact Or.inl fun c => by rw [h, hf₀]; rfl
        · exact Or.inr fun c => by
            rw [h, hf₀']
            change c ^ p ^ (2 * f₀) = c ^ (p ^ f₀) ^ 2
            rw [← pow_mul, mul_comm]
      · rw [hslPi s hs, hcoe, hαH, MulAut.mul_apply, MulAut.mul_apply, ← map_inv, conjAut_proj,
          fieldAut_proj, conjAut_proj, hproj, coe_slToPsl, toGL_slConjugation, toGL_map_eq_frobGL,
          toGL_slConjugation, toGL_slPiTrueEquiv, inv_inv, conj_frobGL_conj]

end DichotomyLinear

section DichotomyUnitary

variable {K : Type} [Field K] {p f : ℕ}

open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

@[expose] noncomputable def suToPsu (p f : ℕ) (K : Type) [Field K] :
    unitarySU p f K 3 →* projImage (slPi false 3 (p ^ f) K) :=
  (projOf (slPi false 3 (p ^ f) K)).comp (slPiFalseEquiv p f K).symm.toMonoidHom

theorem coe_suToPsu (s : unitarySU p f K 3) :
    ((suToPsu p f K s : projImage (slPi false 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (s : GL (Fin 3) K) :=
  rfl

theorem suToPsu_surjective : Function.Surjective (suToPsu p f K) := by
  intro m
  obtain ⟨s, rfl⟩ := projOf_surjective _ m
  exact ⟨slPiFalseEquiv p f K s, by simp [suToPsu]⟩

theorem ker_suToPsu (h : UnitaryFieldData p f K) : (suToPsu p f K).ker = unitaryScalars h 3 := by
  rw [unitaryScalars_eq h (by norm_num)]
  ext s
  rw [MonoidHom.mem_ker, ← Subtype.coe_inj, coe_suToPsu, Subgroup.coe_one,
    mk_eq_one_iff_mem_statedScalars, Subgroup.mem_subgroupOf]

@[expose] noncomputable def psuEquivUnitary (h : UnitaryFieldData p f K) :
    projImage (slPi false 3 (p ^ f) K) ≃* unitaryPSU h 3 :=
  (QuotientGroup.quotientKerEquivOfSurjective _ (suToPsu_surjective (p := p) (f := f)
    (K := K))).symm.trans (QuotientGroup.quotientMulEquivOfEq (ker_suToPsu h))

theorem psuEquivUnitary_suToPsu (h : UnitaryFieldData p f K) (s : unitarySU p f K 3) :
    psuEquivUnitary h (suToPsu p f K s) = unitaryProj h 3 s := by
  rw [psuEquivUnitary, MulEquiv.trans_apply]
  have : (QuotientGroup.quotientKerEquivOfSurjective _ (suToPsu_surjective (p := p) (f := f)
      (K := K))).symm (suToPsu p f K s) = (s : unitarySU p f K 3 ⧸ (suToPsu p f K).ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [this]
  rfl

theorem psuConj_unitaryProj (h : UnitaryFieldData p f K) (A : unitaryIsom3 h)
    (s : unitarySU p f K 3) :
    psuConj h A (unitaryProj h 3 s) = unitaryProj h 3 (suConj h A s) :=
  rfl

theorem psuField_unitaryProj (h : UnitaryFieldData p f K) (σ : K ≃+* K)
    (s : unitarySU p f K 3) :
    psuField h σ (unitaryProj h 3 s) = unitaryProj h 3 (suField h σ s) :=
  rfl

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem pslAct_pgl_or_field_unitary (hK : PiField false p f K) (hq2 : 2 < p ^ f)
    (hθ : aschbacherSolvableCore 3 L = ⊥) (e : L ≃* projImage (slPi false 3 (p ^ f) K))
    (x : Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1) :
    (∃ y ∈ glPi false 3 (p ^ f) K, ∀ m : projImage (slPi false 3 (p ^ f) K),
        (slAct e x m : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk y * m * (ProjGenLinGroup.mk y)⁻¹) ∨
    (InducesStdKind L x .field ∧ ∃ f₀ : ℕ, f = 3 * f₀ ∧ ∃ σ : K ≃+* K,
      ((∀ c, σ c = c ^ piCard false (p ^ f₀)) ∨ ∀ c, σ c = c ^ (piCard false (p ^ f₀) ^ 2)) ∧
      ∃ g ∈ glPi false 3 (p ^ f) K, ∀ s (hs : s ∈ slPi false 3 (p ^ f) K),
        (slAct e x (projOf _ ⟨s, hs⟩) : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk (g * frobGL σ s * g⁻¹)) := by
  have h := hK.unitary
  have := hK.finite
  set ψ := psuEquivUnitary h with hψ
  set e' := (thetaBotEquiv hθ).trans (e.trans ψ) with he'
  have hind := inducedAutHom_thetaBot hθ e ψ x
  set α := MulAut.congr ψ (slAct e x) with hα
  have hα3 : α ^ 3 = 1 := by
    rw [hα, ← map_pow, ← map_pow, hx3, map_one, map_one]
  have hcoe : ∀ s : unitarySU p f K 3,
      slAct e x (suToPsu p f K s) = ψ.symm (α (unitaryProj h 3 s)) := by
    intro s
    rw [hα, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, ← psuEquivUnitary_suToPsu h, MulEquiv.symm_apply_apply]
  have hproj : ∀ t : unitarySU p f K 3, ψ.symm (unitaryProj h 3 t) = suToPsu p f K t := by
    intro t
    rw [MulEquiv.symm_apply_eq, psuEquivUnitary_suToPsu]
  have hslPi : ∀ s (hs : s ∈ slPi false 3 (p ^ f) K),
      projOf _ ⟨s, hs⟩ = suToPsu p f K ⟨s, hs⟩ := fun s hs => rfl
  by_cases hD : α ∈ (psuConj h).range
  · left
    obtain ⟨A, hA⟩ := hD
    refine ⟨A, (mem_glPi_false h).mpr A.2, fun m => ?_⟩
    obtain ⟨s, rfl⟩ := suToPsu_surjective (p := p) (f := f) (K := K) m
    rw [hcoe, ← hA, psuConj_unitaryProj, hproj, coe_suToPsu, coe_suToPsu, coe_suConj, map_mul,
      map_mul, Subgroup.coe_inv, map_inv]
  · right
    refine ⟨InducesStdKind.psu3 h hq2 ⟨e', x.2, ?_⟩, ?_⟩
    · change (stdPinnedPSU3 h).HasKind (inducedAutHom L e' x) .field
      rw [hind]
      exact isField_psu3_of_pow_three_eq_one hq2 hα3 hD
    · obtain ⟨σ, hσ3, H, hαH⟩ := unitary_order_three_field_descent hq2 α hα3 hD
      have hcard : Nat.card K = p ^ (2 * f) := by
        rw [hK.card]
        change (p ^ f) ^ 2 = p ^ (2 * f)
        rw [← pow_mul, mul_comm]
      obtain ⟨h3f, hσc⟩ := eq_frobenius_pow_of_orderOf_eq_three hK.prime (by
        have := hK.one_le; omega) hcard hσ3
      obtain ⟨f₀, rfl⟩ : 3 ∣ f := by
        have hc : Nat.Coprime 3 2 := by norm_num
        exact hc.dvd_of_dvd_mul_left h3f
      have hf₀ : 2 * (3 * f₀) / 3 = 2 * f₀ := by omega
      have hf₀' : 2 * (2 * (3 * f₀)) / 3 = 4 * f₀ := by omega
      have hH : (H : GL (Fin 3) K) * frobGL σ (H : GL (Fin 3) K)⁻¹ ∈
          glPi false 3 (p ^ (3 * f₀)) K := by
        refine (mem_glPi_false h).mpr ?_
        rw [← mem_unitaryIsom3]
        exact mul_mem H.2 (glAut_mem_unitaryIsom3 σ (inv_mem H.2))
      refine ⟨f₀, rfl, σ, ?_, _, hH, fun s hs => ?_⟩
      · rcases hσc with hc | hc
        · exact Or.inl fun c => by
            rw [hc, hf₀]
            change c ^ p ^ (2 * f₀) = c ^ (p ^ f₀) ^ 2
            rw [← pow_mul, mul_comm]
        · exact Or.inr fun c => by
            rw [hc, hf₀']
            change c ^ p ^ (4 * f₀) = c ^ ((p ^ f₀) ^ 2) ^ 2
            rw [← pow_mul, ← pow_mul]
            ring_nf
      · rw [hslPi s hs, hcoe, hαH, MulAut.mul_apply, MulAut.mul_apply, ← map_inv,
          psuConj_unitaryProj, psuField_unitaryProj, psuConj_unitaryProj, hproj, coe_suToPsu,
          coe_suConj, coe_suField, coe_suConj, glAut_eq_frobGL, ← conj_frobGL_conj]
        simp only [Subgroup.coe_inv, inv_inv]

end DichotomyUnitary

section Dichotomy

open CFSG.RankThree.PartTwo.KFacts

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {p f : ℕ}
  {π : Bool}

theorem pslAct_pgl_or_field (hK : PiField π p f K) (hq2 : 2 < p ^ f)
    (hθ : aschbacherSolvableCore 3 L = ⊥) (e : L ≃* projImage (slPi π 3 (p ^ f) K))
    (x : Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1) :
    (∃ y ∈ glPi π 3 (p ^ f) K, ∀ m : projImage (slPi π 3 (p ^ f) K),
        (slAct e x m : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk y * m * (ProjGenLinGroup.mk y)⁻¹) ∨
    (InducesStdKind L x .field ∧ ∃ f₀ : ℕ, f = 3 * f₀ ∧ ∃ σ : K ≃+* K,
      ((∀ c, σ c = c ^ piCard π (p ^ f₀)) ∨ ∀ c, σ c = c ^ (piCard π (p ^ f₀) ^ 2)) ∧
      ∃ g ∈ glPi π 3 (p ^ f) K, ∀ s (hs : s ∈ slPi π 3 (p ^ f) K),
        (slAct e x (projOf _ ⟨s, hs⟩) : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk (g * frobGL σ s * g⁻¹)) := by
  cases π
  · exact pslAct_pgl_or_field_unitary hK hq2 hθ e x hx3
  · exact pslAct_pgl_or_field_linear hK hθ e x hx3

end Dichotomy

end CFSG.RankThree.PartTwo.Sec4
