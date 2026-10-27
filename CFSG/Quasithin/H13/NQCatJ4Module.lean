module

public import CFSG.Quasithin.H13.NQCatJ4Sylow
public import CFSG.LinearAlgebra.ExtraspecialCyclotomicModule
public import CFSG.LieType.BorelTits.Flag
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.RankThree.GroupTheory.SteinbergBKFrattiniOuterPrimeBound
public import Certificates.Certificate7020
public import Certificates.Certificate3084
public import Certificates.Certificate8024
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupActions.SelfCentralizingCoreOuterPrimeBound
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.Sporadic.Schreier.J4SSylow

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.NQCat

open Subgroup CFSG.LinearAlgebra
open scoped commutatorElement Matrix

noncomputable def jrep : Sporadic.J4.J →* Module.End (ZMod 2) (Fin 112 → ZMod 2) where
  toFun g := Matrix.mulVecLin (jmat g)
  map_one' := by rw [map_one, Matrix.mulVecLin_one, Module.End.one_eq_id]
  map_mul' a b := by rw [map_mul, Matrix.mulVecLin_mul, Module.End.mul_eq_comp]

theorem jrep_apply (g : Sporadic.J4.J) (v : Fin 112 → ZMod 2) : jrep g v = jmat g *ᵥ v := by
  simp only [jrep, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.mulVecLin_apply]

theorem jrep_sub_one (g : Sporadic.J4.J) : jrep g - 1 = Matrix.mulVecLin (jmat g - 1) := by
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.sub_apply, Module.End.one_apply, jrep_apply, Matrix.mulVecLin_apply,
    Matrix.sub_mulVec, Matrix.one_mulVec]

theorem jmat_eq_one_of_jrep {g : Sporadic.J4.J} (h : ∀ v, jrep g v = v) : g = 1 := by
  apply jmat_injective
  rw [map_one]
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_one, LinearMap.id_apply, ← jrep_apply, h v]

noncomputable abbrev qrep
    : Representation (ZMod 2) j4Q (Fin 112 → ZMod 2) :=
  jrep.comp j4Q.subtype

noncomputable abbrev zQ :
    j4Q := ⟨j4z, ElevenData.z_mem⟩

theorem finrank_centralFixed
    : Module.finrank (ZMod 2) (centralFixed qrep zQ) = 2 := by
  have h := fixDim_z_pow (k := 1) (by norm_num) (by norm_num)
  rw [pow_one, fixDim] at h
  rw [centralFixed, MonoidHom.comp_apply, Subgroup.coe_subtype, jrep_sub_one]
  exact h

theorem orderOf_two_zmod_eleven : orderOf (2 : ZMod 11) = 11 - 1 :=
  (orderOf_eq_iff (by norm_num)).2 ⟨by decide, by decide⟩

theorem closure_xy_j4Q :
    Subgroup.closure ({⟨j4x, mem_closure_pair_left _ _⟩, ⟨j4y, mem_closure_pair_right _ _⟩} :
      Set j4Q) = ⊤ := by
  rw [← closure_closure_coe_preimage (k := ({j4x, j4y} : Set Sporadic.J4.J))]
  congr 1
  ext g
  simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h) <;> simp [h]
  · rintro (h | h)
    · left
      exact Subtype.ext h
    · right
      exact Subtype.ext h

theorem zQ_eq :
    zQ = ⁅(⟨j4x, mem_closure_pair_left _ _⟩ : j4Q), ⟨j4y, mem_closure_pair_right _ _⟩⁆ :=
  Subtype.ext (by simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv])

theorem j4Q_module :
    IsCompl (centralFixed qrep zQ) (centralImage qrep zQ) ∧
      (∀ g : j4Q, ∀ u ∈ centralFixed qrep zQ, qrep g u = u) ∧
      centralImage qrep zQ ≠ ⊥ ∧
      ∀ S : Submodule (ZMod 2) (Fin 112 → ZMod 2), S ≤ centralImage qrep zQ →
        (∀ g : j4Q, ∀ s ∈ S, qrep g s ∈ S) → S = ⊥ ∨ S = centralImage qrep zQ := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨h1, h2, -, -, -, ⟨h3, h4⟩, -⟩ := extraspecial_prime_cyclotomic_minimal_module
    (p := 11) (by norm_num) orderOf_two_zmod_eleven j4Data.isExtraspecial j4Data.card_closure
    j4Data.exponent_eq closure_xy_j4Q zQ_eq qrep (r := 2) (by norm_num)
    (by rw [Module.finrank_fin_fun]) finrank_centralFixed
  exact ⟨h1, h2, h3, h4⟩

theorem not_dvd_card_GL_two {d : ℕ} (hd : d ≤ 21) :
    ¬ 11 ^ 3 ∣ Nat.card (GL (Fin d) (ZMod 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.SectionRank.Ccomm.card_GL_zmod]
  interval_cases d <;> simp only [Fin.prod_univ_succ, Fin.prod_univ_zero] <;> norm_num

theorem zQ_mem_center :
    zQ ∈ center j4Q := by
  have h : j4z ∈ (center j4Q).map j4Q.subtype := by
    rw [j4Data.center_eq]
    exact mem_zpowers _
  obtain ⟨c, hc, hce⟩ := h
  have : c = zQ := Subtype.ext hce
  exact this ▸ hc

theorem commute_z_of_normalized
    {D : Subgroup Sporadic.J4.J} (hD : IsPGroup 2 D)
    (hcard : Nat.card D ≤ 2 ^ 21) (hQD : j4Q ≤ normalizer (D : Set Sporadic.J4.J)) :
    ∀ d ∈ D, j4z * d = d * j4z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hDN : D ≤ normalizer (D : Set Sporadic.J4.J) := le_normalizer
  let D' := D.subgroupOf (normalizer (D : Set Sporadic.J4.J))
  let φ : j4Q →* MulAut D' := (MulAut.conjNormal (H := D')).comp (Subgroup.inclusion hQD)
  by_cases hz : zQ ∈ φ.ker
  · intro d hd
    have h2 := congrArg (fun α : MulAut D' =>
      (((α ⟨⟨d, hDN hd⟩, hd⟩ : D') : normalizer (D : Set Sporadic.J4.J)) : Sporadic.J4.J))
      (MonoidHom.mem_ker.1 hz)
    simp only [φ, MonoidHom.comp_apply, MulAut.conjNormal_apply, MulAut.one_apply,
      Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion] at h2
    calc j4z * d = j4z * d * j4z⁻¹ * j4z := by group
      _ = d * j4z := by rw [h2]
  · exfalso
    have hker : φ.ker = ⊥ := by
      by_contra hne
      have : Group.IsNilpotent j4Q := j4Data.isPGroup.isNilpotent
      have h := Group.IsNilpotent.inf_center_ne_bot_of_normal (H := φ.ker) hne
      have hZ : Nat.card (center j4Q) = 11 := j4Data.isExtraspecial.2.2.2
      have hdvd : Nat.card ↥(φ.ker ⊓ center j4Q) ∣ 11 := hZ ▸ card_dvd_of_le inf_le_right
      rcases (Nat.dvd_prime (by norm_num)).1 hdvd with h1 | h11
      · exact h (eq_bot_of_card_eq _ h1)
      · have heq : φ.ker ⊓ center j4Q = center j4Q :=
          eq_of_le_of_card_ge inf_le_right (by rw [h11, hZ])
        have hzk : zQ ∈ φ.ker ⊓ center j4Q := by
          rw [heq]
          exact zQ_mem_center
        exact hz hzk.1
    have hφ : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hker
    have : Finite (MulAut D') :=
      Finite.of_injective _ (DFunLike.coe_injective (F := MulAut D'))
    have h113 : 11 ^ 3 ∣ Nat.card (MulAut D') := by
      rw [← j4Data.card_closure, Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]
      exact card_subgroup_dvd_card _
    have hD' : IsPGroup 2 D' := hD.of_equiv (subgroupOfEquivOfLe hDN).symm
    obtain ⟨-, -, -, -, d, hdcard, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hD'
    have hd : d ≤ 21 := by
      have h1 : Nat.card (D' ⧸ frattini D') ≤ Nat.card D' :=
        Nat.le_of_dvd Nat.card_pos (card_quotient_dvd_card _)
      have h2 : Nat.card D' = Nat.card D := Nat.card_congr (subgroupOfEquivOfLe hDN).toEquiv
      rw [hdcard, h2] at h1
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 (h1.trans hcard)
    have hbound := CFSG.RankThree.GroupTheory.SteinbergBK.pow_factorization_card_mulAut_dvd
      (p := 11) (q := 2) (by norm_num) hD' hdcard
    have h3 : 3 ≤ (Nat.card (MulAut D')).factorization 11 :=
      ((Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) Nat.card_pos.ne').1 h113)
    apply not_dvd_card_GL_two hd
    exact ((pow_dvd_pow 11 h3).trans hbound).trans (Nat.ordProj_dvd _ _)

@[expose] noncomputable def restrictRep {H : Type*} [Group H] (ρ : H →* Module.End (ZMod 2)
    (Fin 112 → ZMod 2)) (S : Submodule (ZMod 2) (Fin 112 → ZMod 2))
    (hS : ∀ g, ∀ s ∈ S, ρ g s ∈ S) : H →* Module.End (ZMod 2) S where
  toFun g := (ρ g).restrict (hS g)
  map_one' := by
    refine LinearMap.ext fun s => Subtype.ext ?_
    show ρ 1 s = s
    rw [map_one, Module.End.one_apply]
  map_mul' a b := by
    refine LinearMap.ext fun s => Subtype.ext ?_
    show ρ (a * b) s = ρ a (ρ b s)
    rw [map_mul, Module.End.mul_apply]

theorem restrictRep_apply {H : Type*} [Group H] (ρ : H →* Module.End (ZMod 2)
    (Fin 112 → ZMod 2)) (S : Submodule (ZMod 2) (Fin 112 → ZMod 2))
    (hS : ∀ g, ∀ s ∈ S, ρ g s ∈ S) (g : H) (s : S) :
    ((restrictRep ρ S hS g s : S) : Fin 112 → ZMod 2) = ρ g s := rfl

theorem card_units_end_of_finrank_two {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    (hU : Module.finrank (ZMod 2) U = 2) : Nat.card (Module.End (ZMod 2) U)ˣ = 6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Module.Finite (ZMod 2) U := Module.finite_of_finrank_eq_succ hU
  let b := Module.finBasisOfFinrankEq (ZMod 2) U hU
  rw [Nat.card_congr (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv).toEquiv]
  change Nat.card (GL (Fin 2) (ZMod 2)) = 6
  rw [CFSG.SectionRank.Ccomm.card_GL_zmod]
  simp only [Fin.prod_univ_two]
  norm_num

theorem card_le_two_of_normalized
    {D : Subgroup Sporadic.J4.J} (hD : IsPGroup 2 D)
    (hQD : j4Q ≤ normalizer (D : Set Sporadic.J4.J)) (hzD : ∀ d ∈ D, j4z * d = d * j4z) :
    Nat.card D ≤ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hUW, -, hW0, hirr⟩ := j4Q_module
  set U := centralFixed qrep zQ
  set W := centralImage qrep zQ
  have hqz : qrep zQ = jrep j4z := rfl
  have hcz : ∀ d : D, Commute (jrep d) (qrep zQ) := fun d => by
    rw [hqz]
    show jrep d * jrep j4z = jrep j4z * jrep d
    rw [← map_mul, ← map_mul, hzD d d.2]
  have hDW : ∀ d : D, ∀ w ∈ W, (jrep.comp D.subtype) d w ∈ W := fun d =>
    mapsTo_centralImage (hcz d)
  have hDU : ∀ d : D, ∀ u ∈ U, (jrep.comp D.subtype) d u ∈ U := fun d =>
    mapsTo_centralFixed (hcz d)
  let S : Submodule (ZMod 2) (Fin 112 → ZMod 2) := W ⊓ ⨅ d : D, LinearMap.ker (jrep d - 1)
  have hmemS : ∀ v, v ∈ S ↔ v ∈ W ∧ ∀ d : D, jrep d v = v := by
    intro v
    simp only [S, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      Module.End.one_apply, sub_eq_zero]
  have hSQ : ∀ g : j4Q, ∀ s ∈ S, qrep g s ∈ S := by
    intro g s hs
    rw [hmemS] at hs ⊢
    have hgz : Commute (qrep g) (qrep zQ) := by
      show qrep g * qrep zQ = qrep zQ * qrep g
      rw [← map_mul, ← map_mul, (mem_center_iff.1 zQ_mem_center g)]
    refine ⟨mapsTo_centralImage hgz s hs.1, fun d => ?_⟩
    have hgD : ((g : Sporadic.J4.J))⁻¹ ∈ normalizer (D : Set Sporadic.J4.J) :=
      inv_mem (hQD g.2)
    have hd' : (g : Sporadic.J4.J)⁻¹ * d * ((g : Sporadic.J4.J)⁻¹)⁻¹ ∈ D :=
      (mem_normalizer_iff.1 hgD d).1 d.2
    rw [inv_inv] at hd'
    have e : (d : Sporadic.J4.J) * g = g * ((g : Sporadic.J4.J)⁻¹ * d * g) := by group
    have hfix := hs.2 ⟨_, hd'⟩
    have hq : ∀ v, qrep g v = jrep g v := fun _ => rfl
    calc jrep d (qrep g s) = jrep ((d : Sporadic.J4.J) * g) s := by
          rw [map_mul, Module.End.mul_apply, hq]
      _ = jrep (g * ((g : Sporadic.J4.J)⁻¹ * d * g)) s := by rw [e]
      _ = qrep g (jrep ((g : Sporadic.J4.J)⁻¹ * d * g) s) := by
          rw [map_mul, Module.End.mul_apply, hq]
      _ = qrep g s := by rw [hfix]
  have hS0 : S ≠ ⊥ := by
    have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hW0
    obtain ⟨w, hw0, hwfix⟩ := CFSG.LieType.BorelTits.exists_fixed_ne_zero
      (restrictRep (jrep.comp D.subtype) W hDW) 2 ⊤ (hD.to_subgroup ⊤)
    intro hbot
    apply hw0
    have hwS : (w : Fin 112 → ZMod 2) ∈ S := by
      rw [hmemS]
      refine ⟨w.2, fun d => ?_⟩
      have h1 := congrArg Subtype.val (hwfix d (mem_top d))
      rw [restrictRep_apply] at h1
      exact h1
    rw [hbot, Submodule.mem_bot] at hwS
    exact Subtype.ext hwS
  have hSW : S = W := (hirr S inf_le_left hSQ).resolve_left hS0
  have hDWfix : ∀ d : D, ∀ w ∈ W, jrep d w = w := fun d w hw =>
    ((hmemS w).1 (by rw [hSW]; exact hw)).2 d
  let ψ := (restrictRep (jrep.comp D.subtype) U hDU).toHomUnits
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have hU1 : ∀ u ∈ U, jrep d u = u := fun u hu => by
      have h1 := congrArg (fun A : (Module.End (ZMod 2) U)ˣ =>
        (((A : Module.End (ZMod 2) U) ⟨u, hu⟩ : U) : Fin 112 → ZMod 2)) hd
      simp only [ψ, MonoidHom.coe_toHomUnits, Units.val_one, Module.End.one_apply] at h1
      rw [restrictRep_apply] at h1
      exact h1
    have hall : ∀ v, jrep d v = v := by
      intro v
      have hv : v ∈ U ⊔ W := by rw [hUW.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
      rw [map_add, hU1 u hu, hDWfix d w hw]
    exact Subtype.ext (jmat_eq_one_of_jrep hall)
  have hdvd : Nat.card D ∣ 6 := by
    rw [← card_units_end_of_finrank_two finrank_centralFixed,
      Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv]
    exact card_subgroup_dvd_card _
  obtain ⟨k, hk⟩ := hD.exists_card_eq
  rw [hk] at hdvd ⊢
  rcases (show k = 0 ∨ k = 1 ∨ 2 ≤ k by omega) with rfl | rfl | h2
  · norm_num
  · norm_num
  · exfalso
    have h4 : 2 ^ 2 ∣ 6 := (pow_dvd_pow 2 h2).trans hdvd
    norm_num at h4

end CFSG.Quasithin.H13.NQCat
