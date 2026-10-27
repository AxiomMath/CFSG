module

public import CFSG.Sporadic.HNOddCore.FusB
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalInvolutionOddCore
public import Certificates.Certificate2084
public import Certificates.Certificate2087
public import Certificates.Certificate2091
public import Certificates.Certificate2094
public import Certificates.Certificate2096
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.Sporadic.HN.Local
open Equiv Equiv.Perm

theorem oddCore_bot_of_mulEquiv {G K : Type*} [Group G] [Group K] (e : G ≃* K)
    (h : CFSG.oddCore K = ⊥) : CFSG.oddCore G = ⊥ := by
  refine sSup_eq_bot.2 fun M hM => ?_
  have hn : (M.map e.toMonoidHom).Normal := hM.1.map _ e.surjective
  have hodd : Odd (Nat.card (M.map e.toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact hM.2
  have hle : M.map e.toMonoidHom ≤ CFSG.oddCore K := le_sSup ⟨hn, hodd⟩
  rw [h, le_bot_iff] at hle
  rw [← Subgroup.map_eq_bot_iff_of_injective (f := e.toMonoidHom) M e.injective]
  exact hle

theorem card_fixed_of_type {σ : Perm (Fin 12)} {k : ℕ} (h : σ.cycleType = Multiset.replicate k 2) :
    Nat.card {ω // σ ω = ω} + 2 * k = 12 := by
  have hs : σ.support.card = 2 * k := by
    rw [← Equiv.Perm.sum_cycleType, h, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have e : Nat.card {ω // σ ω = ω} = (Finset.univ.filter fun ω => σ ω = ω).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 12)))
    (fun ω => σ ω = ω)
  rw [Finset.card_univ, Fintype.card_fin] at hsum
  rw [e, ← hs]
  exact hsum

theorem oddCore_altCentralizer {σ : Perm (Fin 12)}
    (hk : σ.cycleType = Multiset.replicate 2 2 ∨ σ.cycleType = Multiset.replicate 6 2) :
    CFSG.oddCore ↥(alternatingGroup (Fin 12) ⊓ Subgroup.centralizer ({σ} : Set (Perm (Fin 12)))) =
      ⊥ := by
  have h2 : σ ^ 2 = 1 := by
    rcases hk with h | h
    · exact sq_eq_one_of_cycleType_replicate h
    · exact sq_eq_one_of_cycleType_replicate h
  have h1 : σ ≠ 1 := by
    rintro rfl
    rw [Equiv.Perm.cycleType_one] at hk
    rcases hk with h | h
    · exact absurd (congrArg Multiset.card h) (by simp)
    · exact absurd (congrArg Multiset.card h) (by simp)
  have hfix : Nat.card {ω // σ ω = ω} ≠ 3 := by
    rcases hk with h | h
    · have := card_fixed_of_type h
      omega
    · have := card_fixed_of_type h
      omega
  exact (ComponentClassification.SymmetricLocal.involution_permutation_centralizer_odd_core
    le_rfl (orderOf_eq_prime h2 h1)).1 hfix

theorem sub_mem_centralizer_iff {G : Type*} [Group G] {H : Subgroup G} {a b : H} :
    a ∈ Subgroup.centralizer {b} ↔ a * b = b * a :=
  Subgroup.mem_centralizer_singleton_iff

theorem conj_mem_HJ_of_fix
    {g c : JH} (hc : c • (g • x0) = g • x0) : g⁻¹ * c * g ∈ HJ := by
  rw [mem_HJ_iff_fix, mul_smul, mul_smul, hc, inv_smul_smul]

theorem conj_comm {a b g : JH} (h : a * b = b * a) :
    (g⁻¹ * a * g) * (g⁻¹ * b * g) = (g⁻¹ * b * g) * (g⁻¹ * a * g) := by
  calc (g⁻¹ * a * g) * (g⁻¹ * b * g) = g⁻¹ * (a * b) * g := by group
    _ = g⁻¹ * (b * a) * g := by rw [h]
    _ = (g⁻¹ * b * g) * (g⁻¹ * a * g) := by group

@[expose] def stabToH
    {t g : JH} :
    MulAction.stabilizer (Subgroup.centralizer {t}) (g • x0) →* HJ :=
  MonoidHom.codRestrict ((MulAut.conj g⁻¹).toMonoidHom.comp ((Subgroup.centralizer {t}).subtype.comp
    (MulAction.stabilizer (Subgroup.centralizer {t}) (g • x0)).subtype)) HJ fun c => by
      have hc : (c : Subgroup.centralizer {t}) • (g • x0) = g • x0 :=
        MulAction.mem_stabilizer_iff.1 c.2
      have e : ((MulAut.conj g⁻¹).toMonoidHom.comp ((Subgroup.centralizer {t}).subtype.comp
          (MulAction.stabilizer (Subgroup.centralizer {t}) (g • x0)).subtype)) c =
          g⁻¹ * c.1.1 * g := by
        simp
      rw [e]
      exact conj_mem_HJ_of_fix hc

theorem stabToH_val
    {t g : JH} (c : MulAction.stabilizer (Subgroup.centralizer {t}) (g • x0)) :
    ((stabToH c : HJ) : JH) = g⁻¹ * c.1.1 * g := by
  simp [stabToH]

@[expose] def stabHom
    {t g : JH} (hx : g⁻¹ * t * g ∈ HJ) :
    MulAction.stabilizer (Subgroup.centralizer {t}) (g • x0) →*
      ↥(alternatingGroup (Fin 12) ⊓
        Subgroup.centralizer
          ({(thetaJ ⟨g⁻¹ * t * g, hx⟩ : Perm (Fin 12))} : Set (Perm (Fin 12)))) :=
  MonoidHom.codRestrict (thetaHom.comp (stabToH (t := t) (g := g))) _ fun c => by
      rw [MonoidHom.comp_apply, thetaHom_apply]
      refine Subgroup.mem_inf.2 ⟨(thetaJ (stabToH c)).2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hct : c.1.1 * t = t * c.1.1 := sub_mem_centralizer_iff.1 c.1.2
      have e : stabToH c * ⟨g⁻¹ * t * g, hx⟩ = ⟨g⁻¹ * t * g, hx⟩ * stabToH c := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, stabToH_val]
        exact conj_comm hct
      have e2 := congrArg (fun h => (thetaJ h : Perm (Fin 12))) e
      simp only [map_mul, Subgroup.coe_mul] at e2
      exact e2

theorem stabHom_val
    {t g : JH} (hx : g⁻¹ * t * g ∈ HJ)
    (c : MulAction.stabilizer (Subgroup.centralizer {t}) (g • x0)) :
    ((stabHom hx c : Perm (Fin 12))) = (thetaJ (stabToH c) : Perm (Fin 12)) := rfl

theorem stabHom_bijective
    {t g : JH} (hx : g⁻¹ * t * g ∈ HJ) :
    Function.Bijective (stabHom hx) := by
  constructor
  · intro a b hab
    have e1 : (thetaJ (stabToH a) : Perm (Fin 12)) = thetaJ (stabToH b) := by
      rw [← stabHom_val hx, ← stabHom_val hx, hab]
    have e2 := thetaJ.injective (Subtype.ext e1)
    have e3 : g⁻¹ * a.1.1 * g = g⁻¹ * b.1.1 * g := by
      rw [← stabToH_val, ← stabToH_val, e2]
    apply Subtype.ext
    apply Subtype.ext
    simpa using e3
  · rintro ⟨σ, hσ⟩
    obtain ⟨hσA, hσC⟩ := Subgroup.mem_inf.1 hσ
    obtain ⟨h, hθ⟩ : ∃ h : HJ, (thetaJ h : Perm (Fin 12)) = σ :=
      ⟨thetaJ.symm ⟨σ, hσA⟩, by rw [MulEquiv.apply_symm_apply]⟩
    have hcx : h * ⟨g⁻¹ * t * g, hx⟩ = ⟨g⁻¹ * t * g, hx⟩ * h := by
      apply thetaJ.injective
      apply Subtype.ext
      rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hθ]
      exact Subgroup.mem_centralizer_singleton_iff.1 hσC
    have hcx' := congrArg Subtype.val hcx
    simp only [Subgroup.coe_mul] at hcx'
    have hct : g * h * g⁻¹ ∈ Subgroup.centralizer {t} := by
      refine sub_mem_centralizer_iff.2 ?_
      calc g * h * g⁻¹ * t = g * ((h : JH) * (g⁻¹ * t * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * t * g) * h) * g⁻¹ := by rw [hcx']
        _ = t * (g * h * g⁻¹) := by group
    have hfix : (⟨g * h * g⁻¹, hct⟩ : Subgroup.centralizer {t}) • (g • x0) = g • x0 := by
      rw [Subgroup.smul_def]
      show (g * h * g⁻¹) • (g • x0) = g • x0
      rw [mul_smul, mul_smul, inv_smul_smul, (mem_HJ_iff_fix _).1 h.2]
    refine ⟨⟨⟨g * h * g⁻¹, hct⟩, hfix⟩, ?_⟩
    apply Subtype.ext
    rw [stabHom_val]
    have e : stabToH (t := t) (g := g) ⟨⟨g * h * g⁻¹, hct⟩, hfix⟩ = h := by
      apply Subtype.ext
      rw [stabToH_val]
      show g⁻¹ * (g * h * g⁻¹) * g = h
      group
    rw [e, hθ]

theorem t2_sqR :
    (jR t2J) ^ 2 = 1 := by
  have h : (t2V : RH) ^ 2 = 1 := sq_of_thetaR thetaR_t2V
  exact h

theorem t2_ne_oneR :
    jR t2J ≠ 1 := by
  have h : (t2V : RH) ≠ 1 := ne_one_of_thetaR (by norm_num) thetaR_t2V
  exact h

theorem isConj_conj_inv {G : Type*} [Group G] (a g : G) : IsConj a (g⁻¹ * a * g) :=
  isConj_iff.2 ⟨g⁻¹, by rw [inv_inv]⟩

theorem stabilizer_t2
    {p : X} (hp : t2J • p = p) :
    ∃ (g : JH) (hx : g⁻¹ * t2J * g ∈ HJ), g • x0 = p ∧
      ((thetaJ ⟨g⁻¹ * t2J * g, hx⟩ : Perm (Fin 12)).cycleType = Multiset.replicate 2 2 ∨
        (thetaJ ⟨g⁻¹ * t2J * g, hx⟩ : Perm (Fin 12)).cycleType = Multiset.replicate 6 2) ∧
      (∀ c : JH, (c ∈ Subgroup.centralizer {t2J} ∧ c • p = p) ↔
        (g⁻¹ * c * g ∈ Subgroup.centralizer {g⁻¹ * t2J * g} ∧ g⁻¹ * c * g ∈ HJ)) ∧
      CFSG.oddCore (MulAction.stabilizer (Subgroup.centralizer {t2J}) p) = ⊥ := by
  obtain ⟨g, hg⟩ := exists_smul_zero p.val p.isLt
  have hgp : g • x0 = p := Fin.ext hg
  subst hgp
  have hx : g⁻¹ * t2J * g ∈ HJ := conj_mem_HJ_of_fix hp
  have hxV : jR (g⁻¹ * t2J * g) ∈ RV := (jR_mem_RV_iff _).2 hx
  have hconj : IsConj (jR t2J) (jR (g⁻¹ * t2J * g)) := isConj_jR (isConj_conj_inv t2J g)
  have htype := (conj_t2_iff (r := ⟨_, hxV⟩) (sq_of_isConj hconj t2_sqR)
    (ne_one_of_isConj hconj t2_ne_oneR)).1 hconj
  rw [thetaR_jR hx] at htype
  refine ⟨g, hx, rfl, htype, fun c => ?_, ?_⟩
  · have hfix : c • (g • x0) = g • x0 ↔ g⁻¹ * c * g ∈ HJ := by
      rw [mem_HJ_iff_fix, mul_smul, mul_smul, inv_smul_eq_iff]
    rw [hfix, sub_mem_centralizer_iff, sub_mem_centralizer_iff]
    refine and_congr_left fun _ => ⟨fun h => conj_comm h, fun h => ?_⟩
    calc c * t2J = g * ((g⁻¹ * c * g) * (g⁻¹ * t2J * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t2J * g) * (g⁻¹ * c * g)) * g⁻¹ := by rw [h]
      _ = t2J * c := by group
  · exact oddCore_bot_of_mulEquiv (MulEquiv.ofBijective _ (stabHom_bijective hx))
      (oddCore_altCentralizer htype)

end CFSG.Sporadic.HNOddCore
