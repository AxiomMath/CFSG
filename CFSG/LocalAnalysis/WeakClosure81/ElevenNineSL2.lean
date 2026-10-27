module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellSL2
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.TotallySplit

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix Module
open CFSG.QuasithinUnique.Setup.Campbell
open scoped LinearAlgebra.Projectivization Pointwise

variable {F : Type*} [Field F]

theorem eleven_nine_sl2_submodule_eq_of_ne_bot_of_smul
    {p : Projectivization F (Fin 2 → F)} {S : Submodule F (Fin 2 → F)}
    (hSp : S ≤ p.submodule) (hS : S ≠ ⊥)
    (hsmul : ∀ a : F, a ≠ 0 → ∀ w ∈ S, a • w ∈ S) : S = p.submodule := by
  obtain ⟨w₀, hw₀S, hw₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  have hw₀p : w₀ ∈ p.submodule := hSp hw₀S
  have hp : p = Projectivization.mk F w₀ hw₀ := eq_mk_of_mem_submodule hw₀ hw₀p
  refine le_antisymm hSp ?_
  intro w hw
  have hw' : w ∈ (Projectivization.mk F w₀ hw₀).submodule := by rwa [← hp]
  rw [Projectivization.submodule_mk, Submodule.mem_span_singleton] at hw'
  obtain ⟨c, rfl⟩ := hw'
  rcases eq_or_ne c 0 with rfl | hc
  · simpa using S.zero_mem
  · exact hsmul c hc w₀ hw₀S

theorem eleven_nine_sl2_addSubgroup_eq_of_ne_bot_of_smul
    {p : Projectivization F (Fin 2 → F)} {S : AddSubgroup (Fin 2 → F)}
    (hSp : (S : Set (Fin 2 → F)) ⊆ p.submodule) (hS : S ≠ ⊥)
    (hsmul : ∀ a : F, a ≠ 0 → ∀ w ∈ S, a • w ∈ S) :
    (S : Set (Fin 2 → F)) = p.submodule := by
  have hne : ∃ w ∈ S, w ≠ 0 := by
    by_contra h
    apply hS
    refine le_antisymm (fun w hw => ?_) bot_le
    rw [AddSubgroup.mem_bot]
    by_contra hw0
    exact h ⟨w, hw, hw0⟩
  obtain ⟨w₀, hw₀S, hw₀⟩ := hne
  have hw₀p : w₀ ∈ p.submodule := hSp hw₀S
  have hp : p = Projectivization.mk F w₀ hw₀ := eq_mk_of_mem_submodule hw₀ hw₀p
  refine Set.eq_of_subset_of_subset hSp ?_
  intro w hw
  have hw' : w ∈ (Projectivization.mk F w₀ hw₀).submodule := by rwa [← hp]
  rw [Projectivization.submodule_mk, Submodule.mem_span_singleton] at hw'
  obtain ⟨c, rfl⟩ := hw'
  rcases eq_or_ne c 0 with rfl | hc
  · simpa using S.zero_mem
  · exact hsmul c hc w₀ hw₀S

variable [Finite F]

theorem eleven_nine_sl2_fixes_eq_zero_of_mem_normalizer_of_not_mem_rootGrp
    {p : Projectivization F (Fin 2 → F)} {g : SpecialLinearGroup (Fin 2) F}
    (hgN : g ∈ Subgroup.normalizer (rootGrp p : Set (SpecialLinearGroup (Fin 2) F)))
    (hg : g ∉ rootGrp p) {w : Fin 2 → F} (hw : g • w = w) : w = 0 := by
  by_contra hw0
  have hgp : g • p = p := mem_normalizer_rootGrp_iff.mp hgN
  have hg1 : g ≠ 1 := fun h => hg (h ▸ Subgroup.one_mem (rootGrp p))
  have hm : g ∈ rootGrp (Projectivization.mk F w hw0) := mem_rootGrp_mk_of_smul_eq hw0 hw
  have hpm : p = Projectivization.mk F w hw0 := eq_of_smul_eq_of_mem_rootGrp hm hg1 hgp
  rw [← hpm] at hm
  exact hg hm

theorem eleven_nine_sl2_exists_scalar {p : Projectivization F (Fin 2 → F)}
    (g : SpecialLinearGroup (Fin 2) F)
    (hg : g ∈ Subgroup.normalizer (rootGrp p : Set (SpecialLinearGroup (Fin 2) F))) :
    ∃ a : F, ∀ w ∈ p.submodule, g • w = a • w := by
  obtain ⟨v, hv, hpv⟩ : ∃ v : Fin 2 → F, ∃ hv : v ≠ 0,
      p = Projectivization.mk F v hv :=
    ⟨p.rep, p.rep_nonzero, (Projectivization.mk_rep _).symm⟩
  subst hpv
  have hgp : g • Projectivization.mk F v hv = Projectivization.mk F v hv :=
    mem_normalizer_rootGrp_iff.mp hg
  have hmem : v ∈ (Projectivization.mk F v hv).submodule := by
    rw [Projectivization.submodule_mk]; exact Submodule.mem_span_singleton_self v
  have hgv : g • v ∈ (Projectivization.mk F v hv).submodule := by
    have h1 : g • v ∈ g • (Projectivization.mk F v hv).submodule :=
      Submodule.smul_mem_pointwise_smul v g _ hmem
    rwa [← PSL.smul_submodule, hgp] at h1
  rw [Projectivization.submodule_mk, Submodule.mem_span_singleton] at hgv
  obtain ⟨a, ha⟩ := hgv
  refine ⟨a, fun w hw => ?_⟩
  rw [Projectivization.submodule_mk, Submodule.mem_span_singleton] at hw
  obtain ⟨c, rfl⟩ := hw
  rw [smul_comm, ← ha, smul_smul, smul_smul, mul_comm]

@[expose] noncomputable def eleven_nine_sl2_scalar {p : Projectivization F (Fin 2 → F)}
    (g : SpecialLinearGroup (Fin 2) F)
    (hg : g ∈ Subgroup.normalizer (rootGrp p : Set (SpecialLinearGroup (Fin 2) F))) : F :=
  Classical.choose (eleven_nine_sl2_exists_scalar g hg)

theorem eleven_nine_sl2_scalar_smul {p : Projectivization F (Fin 2 → F)}
    (g : SpecialLinearGroup (Fin 2) F)
    (hg : g ∈ Subgroup.normalizer (rootGrp p : Set (SpecialLinearGroup (Fin 2) F)))
    {w : Fin 2 → F} (hw : w ∈ p.submodule) :
    g • w = eleven_nine_sl2_scalar g hg • w :=
  Classical.choose_spec (eleven_nine_sl2_exists_scalar g hg) w hw

theorem eleven_nine_sl2_scalar_ne_zero {p : Projectivization F (Fin 2 → F)}
    (g : SpecialLinearGroup (Fin 2) F)
    (hg : g ∈ Subgroup.normalizer (rootGrp p : Set (SpecialLinearGroup (Fin 2) F))) :
    eleven_nine_sl2_scalar g hg ≠ 0 := by
  obtain ⟨v, hv, hpv⟩ : ∃ v : Fin 2 → F, ∃ hv : v ≠ 0,
      p = Projectivization.mk F v hv :=
    ⟨p.rep, p.rep_nonzero, (Projectivization.mk_rep _).symm⟩
  subst hpv
  intro h0
  have hmem : v ∈ (Projectivization.mk F v hv).submodule := by
    rw [Projectivization.submodule_mk]; exact Submodule.mem_span_singleton_self v
  have h1 := eleven_nine_sl2_scalar_smul g hg hmem
  rw [h0, zero_smul] at h1
  have h3 : v = 0 := by
    have := congrArg (fun x => g⁻¹ • x) h1
    simpa using this
  exact hv h3

theorem eleven_nine_sl2_scalar_eq_one_iff {p : Projectivization F (Fin 2 → F)}
    (g : SpecialLinearGroup (Fin 2) F)
    (hg : g ∈ Subgroup.normalizer (rootGrp p : Set (SpecialLinearGroup (Fin 2) F))) :
    eleven_nine_sl2_scalar g hg = 1 ↔ g ∈ rootGrp p := by
  obtain ⟨v, hv, hpv⟩ : ∃ v : Fin 2 → F, ∃ hv : v ≠ 0,
      p = Projectivization.mk F v hv :=
    ⟨p.rep, p.rep_nonzero, (Projectivization.mk_rep _).symm⟩
  subst hpv
  have hmem : v ∈ (Projectivization.mk F v hv).submodule := by
    rw [Projectivization.submodule_mk]; exact Submodule.mem_span_singleton_self v
  constructor
  · intro h1
    have h2 := eleven_nine_sl2_scalar_smul g hg hmem
    rw [h1, one_smul] at h2
    exact mem_rootGrp_mk_of_smul_eq hv h2
  · intro hgroot
    have hsc := eleven_nine_sl2_scalar_smul g hg hmem
    have hfix : g • v = v := by
      refine Matrix.SpecialLinearGroup.lineStab_fix_of_span v hv g ?_
      unfold rootGrp at hgroot
      rwa [Projectivization.submodule_mk] at hgroot
    have hsub : (eleven_nine_sl2_scalar g hg - 1) • v = 0 := by
      rw [sub_smul, one_smul, ← hsc, hfix, sub_self]
    rcases smul_eq_zero.mp hsub with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv

theorem eleven_nine_sl2_scalar_mul {p : Projectivization F (Fin 2 → F)}
    (g h : SpecialLinearGroup (Fin 2) F)
    (hg : g ∈ Subgroup.normalizer (rootGrp p : Set (SpecialLinearGroup (Fin 2) F)))
    (hh : h ∈ Subgroup.normalizer (rootGrp p : Set (SpecialLinearGroup (Fin 2) F)))
    (hgh : g * h ∈ Subgroup.normalizer (rootGrp p : Set (SpecialLinearGroup (Fin 2) F))) :
    eleven_nine_sl2_scalar (g * h) hgh =
      eleven_nine_sl2_scalar g hg * eleven_nine_sl2_scalar h hh := by
  obtain ⟨v, hv, hpv⟩ : ∃ v : Fin 2 → F, ∃ hv : v ≠ 0,
      p = Projectivization.mk F v hv :=
    ⟨p.rep, p.rep_nonzero, (Projectivization.mk_rep _).symm⟩
  subst hpv
  have hmem : v ∈ (Projectivization.mk F v hv).submodule := by
    rw [Projectivization.submodule_mk]; exact Submodule.mem_span_singleton_self v
  have e1 := eleven_nine_sl2_scalar_smul (g * h) hgh hmem
  have e2 := eleven_nine_sl2_scalar_smul h hh hmem
  have e3 := eleven_nine_sl2_scalar_smul g hg hmem
  rw [mul_smul, e2, smul_comm, e3, smul_smul, mul_comm] at e1
  have hsub : (eleven_nine_sl2_scalar (g * h) hgh -
      eleven_nine_sl2_scalar g hg * eleven_nine_sl2_scalar h hh) • v = 0 := by
    rw [sub_smul, ← e1, sub_self]
  rcases smul_eq_zero.mp hsub with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hv

@[expose] noncomputable def eleven_nine_sl2_scalarHom {p : Projectivization F (Fin 2 → F)}
    {D' : Subgroup (SpecialLinearGroup (Fin 2) F)}
    (hD : D' ≤ Subgroup.normalizer (rootGrp p : Set (SpecialLinearGroup (Fin 2) F))) :
    D' →* Fˣ where
  toFun d := Units.mk0 (eleven_nine_sl2_scalar (d : SpecialLinearGroup (Fin 2) F) (hD d.2))
    (eleven_nine_sl2_scalar_ne_zero _ _)
  map_one' := by
    apply Units.ext
    have h1 : eleven_nine_sl2_scalar (1 : SpecialLinearGroup (Fin 2) F)
        (hD (Subgroup.one_mem D')) = 1 :=
      (eleven_nine_sl2_scalar_eq_one_iff 1 _).mpr (Subgroup.one_mem _)
    simpa using h1
  map_mul' g h := by
    apply Units.ext
    have hm := eleven_nine_sl2_scalar_mul (g : SpecialLinearGroup (Fin 2) F)
      (h : SpecialLinearGroup (Fin 2) F) (hD g.2) (hD h.2)
      (hD (D'.mul_mem g.2 h.2))
    simpa using hm

theorem eleven_nine_sl2_scalarHom_apply {p : Projectivization F (Fin 2 → F)}
    {D' : Subgroup (SpecialLinearGroup (Fin 2) F)}
    (hD : D' ≤ Subgroup.normalizer (rootGrp p : Set (SpecialLinearGroup (Fin 2) F))) (d : D') :
    ((eleven_nine_sl2_scalarHom hD d : Fˣ) : F) =
      eleven_nine_sl2_scalar (d : SpecialLinearGroup (Fin 2) F) (hD d.2) := rfl

theorem eleven_nine_sl2_scalarHom_injective {p : Projectivization F (Fin 2 → F)}
    {D' : Subgroup (SpecialLinearGroup (Fin 2) F)}
    (hD : D' ≤ Subgroup.normalizer (rootGrp p : Set (SpecialLinearGroup (Fin 2) F)))
    {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hodd : Odd (Nat.card D')) :
    Function.Injective (eleven_nine_sl2_scalarHom hD) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : IsPGroup 2 (rootGrp p) := by
    refine IsPGroup.of_card (n := n) ?_
    rw [card_rootGrp, hcard]
  have hnot2 : ¬ 2 ∣ Nat.card D' :=
    fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  intro g h hgh
  have hsc : eleven_nine_sl2_scalar (g : SpecialLinearGroup (Fin 2) F) (hD g.2) =
      eleven_nine_sl2_scalar (h : SpecialLinearGroup (Fin 2) F) (hD h.2) :=
    congrArg (fun u : Fˣ => (u : F)) hgh
  have h1g : eleven_nine_sl2_scalar (1 : SpecialLinearGroup (Fin 2) F)
      (hD (Subgroup.one_mem D')) = 1 :=
    (eleven_nine_sl2_scalar_eq_one_iff 1 _).mpr (Subgroup.one_mem _)
  have hinv : eleven_nine_sl2_scalar ((g : SpecialLinearGroup (Fin 2) F)⁻¹)
      (hD (D'.inv_mem g.2)) *
      eleven_nine_sl2_scalar (g : SpecialLinearGroup (Fin 2) F) (hD g.2) = 1 := by
    have hmul := eleven_nine_sl2_scalar_mul ((g : SpecialLinearGroup (Fin 2) F)⁻¹)
      (g : SpecialLinearGroup (Fin 2) F) (hD (D'.inv_mem g.2)) (hD g.2)
      (hD (D'.mul_mem (D'.inv_mem g.2) g.2))
    have h1 : eleven_nine_sl2_scalar
        ((g : SpecialLinearGroup (Fin 2) F)⁻¹ * (g : SpecialLinearGroup (Fin 2) F))
        (hD (D'.mul_mem (D'.inv_mem g.2) g.2)) = 1 := by
      simpa using h1g
    exact hmul.symm.trans h1
  have hone : eleven_nine_sl2_scalar
      ((g : SpecialLinearGroup (Fin 2) F)⁻¹ * (h : SpecialLinearGroup (Fin 2) F))
      (hD (D'.mul_mem (D'.inv_mem g.2) h.2)) = 1 := by
    have hmul := eleven_nine_sl2_scalar_mul ((g : SpecialLinearGroup (Fin 2) F)⁻¹)
      (h : SpecialLinearGroup (Fin 2) F) (hD (D'.inv_mem g.2)) (hD h.2)
      (hD (D'.mul_mem (D'.inv_mem g.2) h.2))
    exact hmul.trans (by rw [← hsc]; exact hinv)
  have hroot : ((g⁻¹ * h : D') : SpecialLinearGroup (Fin 2) F) ∈ rootGrp p :=
    (eleven_nine_sl2_scalar_eq_one_iff _ (hD (g⁻¹ * h).2)).mp (by simpa using hone)
  have hpow : ∃ k : ℕ, ((g⁻¹ * h : D') : SpecialLinearGroup (Fin 2) F) ^ 2 ^ k = 1 := by
    simpa using hpg ⟨_, hroot⟩
  obtain ⟨k, hk⟩ := hpow
  have hk' : (g⁻¹ * h : D') ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
  have hdvd : orderOf (g⁻¹ * h : D') ∣ Nat.card D' := orderOf_dvd_natCard _
  have hdvd2 : orderOf (g⁻¹ * h : D') ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hk'
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
  have hj0 : j = 0 := by
    by_contra hjn
    have h2j : 2 ∣ 2 ^ j := dvd_pow_self 2 hjn
    exact hnot2 ((hj ▸ h2j).trans hdvd)
  have hone' : (g⁻¹ * h : D') = 1 := by
    rw [← orderOf_eq_one_iff, hj, hj0, pow_zero]
  exact inv_mul_eq_one.mp hone'

theorem eleven_nine_sl2_isCyclic_of_le_normalizer {p : Projectivization F (Fin 2 → F)}
    {D' : Subgroup (SpecialLinearGroup (Fin 2) F)}
    (hD : D' ≤ Subgroup.normalizer (rootGrp p : Set (SpecialLinearGroup (Fin 2) F)))
    {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hodd : Odd (Nat.card D')) : IsCyclic D' := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Finite D' := Subtype.finite
  refine isCyclic_of_injective_ringHom
    ((Units.coeHom F).comp (eleven_nine_sl2_scalarHom hD)) ?_
  intro g h hgh
  exact eleven_nine_sl2_scalarHom_injective hD hcard hodd
    (Units.ext (show (((eleven_nine_sl2_scalarHom hD) g : Fˣ) : F) =
      (((eleven_nine_sl2_scalarHom hD) h : Fˣ) : F) from hgh))

end CFSG.LocalAnalysis.WeakClosure81
