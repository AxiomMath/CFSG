module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res3ProofL325Image
import CFSG.RankThree.PartTwo.Sec15.KL3FactsProofTools
import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
import CFSG.RankThree.PartTwo.Sec16.Item169StepsProofHess
import CFSG.RankThree.PartTwo.KFacts.KP4

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix

namespace KL3FactsProof

variable {K : Type} [Field K]

@[expose] noncomputable def toM {L : Subgroup (GL (Fin 3) K)} : L →* projImage L :=
  (ProjGenLinGroup.mk.comp L.subtype).codRestrict _ fun l => ⟨l, l.2, rfl⟩

theorem le_theta_of_normal' {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {J V₀ : Subgroup G} (hVJ : V₀ ≤ J) (hVn : ∀ x ∈ J, ∀ v ∈ V₀, x * v * x⁻¹ ∈ V₀)
    (hVs : Group.IsSolvable ↥V₀) (hVp : ¬ p ∣ Nat.card ↥V₀) :
    V₀ ≤ inSubgroup (aschbacherSolvableCore p) J := by
  have hn : (V₀.subgroupOf J).Normal := ⟨fun x hx g => by
    have hxV : (x : G) ∈ V₀ := Subgroup.mem_subgroupOf.mp hx
    exact Subgroup.mem_subgroupOf.mpr (hVn g g.2 x hxV)⟩
  have hsol : Group.IsSolvable ↥(V₀.subgroupOf J) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hVJ).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hVJ).injective
  have hcard : Nat.card ↥(V₀.subgroupOf J) = Nat.card ↥V₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVJ).toEquiv
  have hle := (solvable_prime_complement_core_characterization (H := ↥J) hp).2.2.2.1 _ hn hsol
    (by rw [hcard]; exact hVp)
  intro v hv
  exact ⟨⟨v, hVJ hv⟩, hle (Subgroup.mem_subgroupOf.mpr hv), rfl⟩

theorem not_dvd_card_theta {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (J : Subgroup G) : ¬ p ∣ Nat.card (inSubgroup (aschbacherSolvableCore p) J) := by
  rw [inSubgroup, Subgroup.card_map_of_injective J.subtype_injective]
  exact (solvable_prime_complement_core_characterization (H := ↥J) hp).2.2.1

theorem theta_le {G : Type} [Group G] {p : ℕ} (J : Subgroup G) :
    inSubgroup (aschbacherSolvableCore p) J ≤ J :=
  Subgroup.map_subtype_le _

section Core

variable {p f : ℕ}

theorem pow_conj_eq_scalar_pow {l d : GL (Fin 3) K} {μ : Kˣ}
    (h : l * d * l⁻¹ = GeneralLinearGroup.scalar (Fin 3) μ * d) (n : ℕ) :
    l ^ n * d * (l ^ n)⁻¹ = GeneralLinearGroup.scalar (Fin 3) (μ ^ n) * d := by
  have hc : ∀ x : GL (Fin 3) K, ∀ ν : Kˣ,
      x * GeneralLinearGroup.scalar (Fin 3) ν = GeneralLinearGroup.scalar (Fin 3) ν * x :=
    fun x ν => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ν x).eq
  induction n with
  | zero => simp
  | succ n ih =>
    calc l ^ (n + 1) * d * (l ^ (n + 1))⁻¹ = l * (l ^ n * d * (l ^ n)⁻¹) * l⁻¹ := by
          rw [pow_succ']; group
      _ = l * (GeneralLinearGroup.scalar (Fin 3) (μ ^ n) * d) * l⁻¹ := by rw [ih]
      _ = GeneralLinearGroup.scalar (Fin 3) (μ ^ n) * (l * d * l⁻¹) := by
          rw [← mul_assoc, hc l]; group
      _ = GeneralLinearGroup.scalar (Fin 3) (μ ^ (n + 1)) * d := by
          rw [h, ← mul_assoc, ← map_mul, ← pow_succ]

theorem commute_of_mk_commute_of_coprime {τ : K} (hτ : τ ^ 3 = 1) {l : GL (Fin 3) K}
    (h : ProjGenLinGroup.mk l * ProjGenLinGroup.mk (diagTau hτ) =
      ProjGenLinGroup.mk (diagTau hτ) * ProjGenLinGroup.mk l)
    (hn : Nat.Coprime 3 (orderOf (ProjGenLinGroup.mk l))) :
    l * diagTau hτ = diagTau hτ * l := by
  obtain ⟨μ, hμ⟩ := exists_scalar_of_mk_commute h
  have hdet1 : ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [coe_diagTau, det_fin_three]
    simp
    linear_combination hτ
  have hc : ∀ x : GL (Fin 3) K, ∀ ν : Kˣ,
      x * GeneralLinearGroup.scalar (Fin 3) ν = GeneralLinearGroup.scalar (Fin 3) ν * x :=
    fun x ν => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ν x).eq
  have hμ3 : μ ^ 3 = 1 := by
    have e := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K).det) hμ
    simp only [Units.val_mul, det_mul] at e
    rw [det_scalar, hdet1, mul_one] at e
    have hgi : (l : Matrix (Fin 3) (Fin 3) K).det * ((l⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).det = 1 := by
      rw [← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    rw [mul_one] at e
    rw [← e, hgi]
  set n := orderOf (ProjGenLinGroup.mk l) with hn_def
  have hln : ProjGenLinGroup.mk (l ^ n) = 1 := by rw [map_pow]; exact pow_orderOf_eq_one _
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hln
  obtain ⟨s, hs⟩ := hln
  have e2 := pow_conj_eq_scalar_pow hμ n
  have e3 : l ^ n * diagTau hτ * (l ^ n)⁻¹ = diagTau hτ := by
    rw [← hs, ← hc]
    group
  rw [e3] at e2
  have hμn : μ ^ n = 1 := by
    have e4 : GeneralLinearGroup.scalar (Fin 3) (μ ^ n) = 1 := by
      have := congrArg (fun x => x * (diagTau hτ)⁻¹) e2
      simpa using this.symm
    apply Units.ext
    have := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K) 0 0) e4
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq,
      Units.val_one, Matrix.one_apply_eq] at this
    rw [Units.val_one]
    exact this
  have hμ1 : μ = 1 := by
    have h1 : orderOf μ ∣ 3 := orderOf_dvd_of_pow_eq_one hμ3
    have h2 : orderOf μ ∣ n := orderOf_dvd_of_pow_eq_one hμn
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hn h1 h2)
  rw [hμ1, map_one, one_mul] at hμ
  calc l * diagTau hτ = l * diagTau hτ * l⁻¹ * l := by group
    _ = diagTau hτ * l := by rw [hμ]

theorem theta_centralizer_diagTau (hK : PiField true 5 2 K) {τ : K} (hτ : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) (dM : projImage (slPi true 3 (5 ^ 2) K))
    (hdM : (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ)) :
    IsPGroup 2 (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {dM})) ∧
      Nat.card (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {dM})) = 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  have hq : ModThree true (5 ^ 2) := by
    change 5 ^ 2 % 3 = 1
    norm_num
  have hq24 : qSubPi true (5 ^ 2) = 24 := rfl
  set C := Subgroup.centralizer ({dM} : Set (projImage (slPi true 3 (5 ^ 2) K))) with hC
  set θ := inSubgroup (aschbacherSolvableCore 3) C with hθ
  have hθ3 : ¬ 3 ∣ Nat.card θ := not_dvd_card_theta Nat.prime_three C
  set T := (toM.comp (Subgroup.inclusion (inf_le_left :
    slPi true 3 (5 ^ 2) K ⊓ Subgroup.centralizer {diagTau hτ} ≤ slPi true 3 (5 ^ 2) K))).range
    with hT
  have hTcard : Nat.card T ∣ 24 * 24 := by
    obtain ⟨e⟩ := centralizer_diagTau_mulEquiv hK hq hτ hτ1
    have h1 := Subgroup.card_range_dvd (toM.comp (Subgroup.inclusion (inf_le_left :
      slPi true 3 (5 ^ 2) K ⊓ Subgroup.centralizer {diagTau hτ} ≤ slPi true 3 (5 ^ 2) K)))
    have h24 : Nat.card (Multiplicative (ZMod (qSubPi true (5 ^ 2)))) = 24 := by
      rw [hq24, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, h24] at h1
    exact h1
  have hθT : θ ≤ T := by
    intro m hm
    have hmC : m ∈ C := theta_le C hm
    obtain ⟨l, hlL, hlm⟩ := m.2
    have hcomm : ProjGenLinGroup.mk l * ProjGenLinGroup.mk (diagTau hτ) =
        ProjGenLinGroup.mk (diagTau hτ) * ProjGenLinGroup.mk l := by
      rw [hlm, ← hdM]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hmC)
    have hord : Nat.Coprime 3 (orderOf (ProjGenLinGroup.mk l)) := by
      rw [hlm, Subgroup.orderOf_coe]
      have h1 : orderOf m ∣ Nat.card θ := by
        have := orderOf_dvd_natCard (⟨m, hm⟩ : θ)
        rwa [Subgroup.orderOf_mk] at this
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h => hθ3 (h.trans h1)
    have hld := commute_of_mk_commute_of_coprime hτ hcomm hord
    refine ⟨⟨l, hlL, Subgroup.mem_centralizer_singleton_iff.mpr hld⟩, ?_⟩
    exact Subtype.ext hlm
  have hθ64 : Nat.card θ ∣ 64 := by
    have h1 : Nat.card θ ∣ 64 * 9 := by
      have := (Subgroup.card_dvd_of_le hθT).trans hTcard
      norm_num at this ⊢
      exact this
    have hc3 : Nat.Coprime (Nat.card θ) 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3).symm
    have hc9 : Nat.Coprime (Nat.card θ) 9 := by simpa using Nat.Coprime.pow_right 2 hc3
    exact hc9.dvd_of_dvd_mul_right h1
  have h8 : ∀ a : Kˣ, a ∈ rootsOfUnity 8 K → a ∈ rootsOfUnity (qSubPi true (5 ^ 2)) K := by
    intro a ha
    rw [mem_rootsOfUnity] at ha ⊢
    rw [hq24, show (24 : ℕ) = 8 * 3 by norm_num, pow_mul, ha, one_pow]
  have hd8 : ∀ a : Kˣ, a ∈ rootsOfUnity 8 K ↔ a ^ 8 = 1 := fun a => mem_rootsOfUnity 8 a
  let ω : ↥(rootsOfUnity 8 K) × ↥(rootsOfUnity 8 K) →* projImage (slPi true 3 (5 ^ 2) K) :=
    toM.comp ((torusHom.comp ((rootsOfUnity 8 K).subtype.prodMap
      (rootsOfUnity 8 K).subtype)).codRestrict _ fun ab =>
        torusHom_mem_slPi hK (h8 _ ab.1.2) (h8 _ ab.2.2))
  have hω : ∀ ab, ((ω ab : projImage (slPi true 3 (5 ^ 2) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (torusHom ((ab.1 : Kˣ), (ab.2 : Kˣ))) := fun ab => rfl
  have hdet : ∀ ab : Kˣ × Kˣ,
      ((torusHom ab : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    intro ab
    rw [coe_torusHom, det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [← Units.val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hωinj : Function.Injective ω := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    have h1 : ProjGenLinGroup.mk (torusHom ((a : Kˣ), (b : Kˣ))) = 1 :=
      congrArg Subtype.val hab
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h1
    obtain ⟨c, hc⟩ := h1
    have hc3 : c ^ 3 = 1 := by
      have e := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K).det) hc
      simp only [det_scalar, hdet] at e
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, e, Units.val_one])
    have hc8 : c ^ 8 = 1 := by
      have e : torusHom ((a : Kˣ), (b : Kˣ)) ^ 8 = 1 := by
        rw [← map_pow, Prod.pow_mk, (hd8 _).mp a.2, (hd8 _).mp b.2]
        exact map_one _
      rw [← hc, ← map_pow] at e
      apply Units.ext
      have := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K) 0 0) e
      simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq,
        Units.val_one, Matrix.one_apply_eq] at this
      rw [Units.val_one]
      exact this
    have hc1 : c = 1 := by
      have h1 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
      have h2 : orderOf c ∣ 8 := orderOf_dvd_of_pow_eq_one hc8
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (by norm_num) h1 h2)
    rw [hc1, map_one] at hc
    have := torusHom_injective (hc.symm.trans (map_one torusHom).symm)
    rw [Prod.mk_eq_one] at this
    exact Prod.ext (Subtype.ext this.1) (Subtype.ext this.2)
  set W := ω.range with hW
  have h8K : Nat.card (rootsOfUnity 8 K) = 8 := by
    have : NeZero (8 : ℕ) := ⟨by norm_num⟩
    refine CFSG.LinearGroups.card_rootsOfUnity_of_dvd ?_
    rw [hK.card]
    change 8 ∣ 5 ^ 2 - 1
    norm_num
  have hW64 : Nat.card W = 64 := by
    rw [hW, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hωinj, Subgroup.card_top,
      Nat.card_prod, h8K]
  have hcommd : ∀ ab : Kˣ × Kˣ, torusHom ab * diagTau hτ = diagTau hτ * torusHom ab := by
    intro ab
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_torusHom, coe_diagTau_eq_diagonal,
      diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hWC : W ≤ C := by
    rintro _ ⟨ab, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hω, hdM, ← map_mul, ← map_mul, hcommd]
  have hWn : ∀ x ∈ C, ∀ w ∈ W, x * w * x⁻¹ ∈ W := by
    rintro x hx _ ⟨⟨a, b⟩, rfl⟩
    obtain ⟨l, hlL, hlx⟩ := x.2
    have hcomm : ProjGenLinGroup.mk l * ProjGenLinGroup.mk (diagTau hτ) =
        ProjGenLinGroup.mk (diagTau hτ) * ProjGenLinGroup.mk l := by
      rw [hlx, ← hdM]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hx)
    have hdM' : ProjGenLinGroup.mk (diagTau hτ) * ProjGenLinGroup.mk (torusHom (a.1, b.1)) =
        ProjGenLinGroup.mk (torusHom (a.1, b.1)) * ProjGenLinGroup.mk (diagTau hτ) := by
      rw [← map_mul, ← map_mul, hcommd]
    set t' := l * torusHom (a.1, b.1) * l⁻¹ with ht'
    have ht'S : t' ∈ slPi true 3 (5 ^ 2) K := by
      rw [mem_slPi_true]
      simp only [ht', Units.val_mul, det_mul, hdet, mul_one]
      rw [← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]
    have ht'8 : t' ^ 8 = 1 := by
      rw [ht', conj_pow, ← map_pow, Prod.pow_mk, (hd8 _).mp a.2, (hd8 _).mp b.2,
        show ((1 : Kˣ), (1 : Kˣ)) = 1 from rfl, map_one, mul_one, mul_inv_cancel]
    have hmk : ProjGenLinGroup.mk t' * ProjGenLinGroup.mk (diagTau hτ) =
        ProjGenLinGroup.mk (diagTau hτ) * ProjGenLinGroup.mk t' := by
      have hLD : Commute (ProjGenLinGroup.mk l) (ProjGenLinGroup.mk (diagTau hτ)) := hcomm
      have hTD : Commute (ProjGenLinGroup.mk (torusHom (a.1, b.1)))
          (ProjGenLinGroup.mk (diagTau hτ)) := hdM'.symm
      have := (hLD.mul_left hTD).mul_left hLD.inv_left
      rw [ht', map_mul, map_mul, map_inv]
      exact this.eq
    have hord : Nat.Coprime 3 (orderOf (ProjGenLinGroup.mk t')) := by
      have h8' : ProjGenLinGroup.mk t' ^ 8 = 1 := by rw [← map_pow, ht'8, map_one]
      exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one h8') (by norm_num)
    have ht'd := commute_of_mk_commute_of_coprime hτ hmk hord
    have ht'C : t' ∈ slPi true 3 (5 ^ 2) K ⊓ Subgroup.centralizer {diagTau hτ} :=
      ⟨ht'S, Subgroup.mem_centralizer_singleton_iff.mpr ht'd⟩
    rw [centralizer_diagTau_eq hK hq hτ hτ1] at ht'C
    obtain ⟨⟨a', b'⟩, hab'⟩ := ht'C
    have hab'' : torusHom ((a' : Kˣ), (b' : Kˣ)) = t' := hab'
    have h8a : (a' : Kˣ) ^ 8 = 1 ∧ (b' : Kˣ) ^ 8 = 1 := by
      have e : torusHom ((a' : Kˣ) ^ 8, (b' : Kˣ) ^ 8) = 1 := by
        rw [← Prod.pow_mk, map_pow, hab'', ht'8]
      have := torusHom_injective (e.trans (map_one torusHom).symm)
      exact Prod.mk_eq_one.mp this
    refine ⟨(⟨a', (hd8 _).mpr h8a.1⟩, ⟨b', (hd8 _).mpr h8a.2⟩), ?_⟩
    apply Subtype.ext
    rw [hω]
    change ProjGenLinGroup.mk (torusHom ((a' : Kˣ), (b' : Kˣ))) =
      (x : ProjGenLinGroup (Fin 3) K) * ProjGenLinGroup.mk (torusHom (a.1, b.1)) *
        (x : ProjGenLinGroup (Fin 3) K)⁻¹
    rw [hab'', ← hlx, ht', map_mul, map_mul, map_inv]
  have hWs : Group.IsSolvable W := by
    have : IsMulCommutative W := ⟨⟨fun x y => by
      obtain ⟨u, hu⟩ := x.2
      obtain ⟨v, hv⟩ := y.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hu, ← hv, ← map_mul, ← map_mul, mul_comm]⟩⟩
    infer_instance
  have hW3 : ¬ 3 ∣ Nat.card W := by rw [hW64]; norm_num
  have hWθ := le_theta_of_normal' Nat.prime_three hWC hWn hWs hW3
  have hge : 64 ≤ Nat.card θ := hW64 ▸ Subgroup.card_le_of_le hWθ
  have h64 : Nat.card θ = 64 := le_antisymm (Nat.le_of_dvd (by norm_num) hθ64) hge
  exact ⟨IsPGroup.of_card (n := 6) (by rw [h64]; norm_num), h64⟩

end Core

section Model

variable {p f : ℕ} {π : Bool}
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

theorem conj_mem_projImage (hπ : π = false → UnitaryFieldData p f K)
    {g : GL (Fin 3) K} (hg : g ∈ glPi π 3 (p ^ f) K) (m : projImage (slPi π 3 (p ^ f) K)) :
    ProjGenLinGroup.mk g * (m : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk g)⁻¹ ∈
      projImage (slPi π 3 (p ^ f) K) := by
  obtain ⟨l, hl, hlm⟩ := m.2
  refine ⟨g * l * g⁻¹, conj_mem_slPi hπ hg hl, ?_⟩
  rw [map_mul, map_mul, map_inv, hlm]

@[expose] noncomputable def conjM (hπ : π = false → UnitaryFieldData p f K)
    {g : GL (Fin 3) K} (hg : g ∈ glPi π 3 (p ^ f) K) :
    MulAut (projImage (slPi π 3 (p ^ f) K)) where
  toFun m := ⟨ProjGenLinGroup.mk g * (m : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk g)⁻¹,
    conj_mem_projImage hπ hg m⟩
  invFun m := ⟨(ProjGenLinGroup.mk g)⁻¹ * (m : ProjGenLinGroup (Fin 3) K) * ProjGenLinGroup.mk g,
    by simpa using conj_mem_projImage hπ (inv_mem hg) m⟩
  left_inv m := Subtype.ext (by simp [mul_assoc])
  right_inv m := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem coe_conjM (hπ : π = false → UnitaryFieldData p f K)
    {g : GL (Fin 3) K} (hg : g ∈ glPi π 3 (p ^ f) K) (m : projImage (slPi π 3 (p ^ f) K)) :
    ((conjM hπ hg m : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk g * (m : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk g)⁻¹ :=
  rfl

end Model

end KL3FactsProof

open KL3FactsProof

theorem kl325ThetaCent : KL325ThetaCent := by
  intro X _ _ _ hX x hx
  obtain ⟨φ⟩ := hX
  set K := GaloisField 5 2 with hKdef
  have hK : PiField true 5 2 K := ⟨Nat.prime_five, by norm_num, by
    rw [GaloisField.card 5 2 (by norm_num)]; rfl⟩
  have hq : ModThree true (5 ^ 2) := by
    change 5 ^ 2 % 3 = 1
    norm_num
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  have ψ : X ≃* projImage (slPi true 3 (5 ^ 2) K) :=
    φ.trans (MulEquiv.subgroupCongr (projSL_eq_projImage (5 ^ 2) K))
  have key : ∀ y : projImage (slPi true 3 (5 ^ 2) K), orderOf y = 3 →
      IsPGroup 2 (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {y})) ∧
        Nat.card (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {y})) = 64 := by
    intro y hy
    have hπ : true = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 5 2 K :=
      fun h => absurd h (by decide)
    have hq' : true = false → ModThree false (5 ^ 2) := fun h => absurd h (by decide)
    obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
    have h9 : ¬ 9 ∣ Nat.card K - 1 := by
      rw [hK.card]
      change ¬ 9 ∣ 5 ^ 2 - 1
      norm_num
    obtain ⟨w, hw, hwy⟩ := y.2
    have hy3 : y ^ 3 = 1 := by
      have := pow_orderOf_eq_one y
      rwa [hy] at this
    have hw3' : ProjGenLinGroup.mk w ^ 3 = 1 := by
      rw [hwy]
      exact congrArg Subtype.val hy3
    have hw3 : w ^ 3 = 1 := Sec16.ProofHess.pow_three_eq_one_of_lift hK h9 hw hw3'
    have hy1 : y ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hy
      norm_num at hy
    have hwZ : w ∉ zPi true 3 (5 ^ 2) K := by
      intro hz
      apply hy1
      apply Subtype.ext
      rw [← hwy, Subgroup.coe_one, ProjGenLinGroup.mk_eq_one,
        GeneralLinearGroup.center_eq_range_scalar]
      exact (Subgroup.mem_inf.mp ((zPi_eq hπ hq' hτ hτ1) ▸ hz)).2
    have hwo : orderOf w = 3 := by
      refine orderOf_eq_prime hw3 fun h1 => hwZ ?_
      rw [h1]
      exact one_mem _
    obtain ⟨g, hg, hgw⟩ := rank3II_4_10_three hK hq hτ hτ1 hw hwZ hwo
    set dM : projImage (slPi true 3 (5 ^ 2) K) :=
      ⟨ProjGenLinGroup.mk (diagTau hτ), ⟨_, diagTau_mem_slPi hπ hq' hτ, rfl⟩⟩ with hdM
    have hγ : conjM hπ hg dM = y := by
      apply Subtype.ext
      rw [coe_conjM, ← hwy]
      change ProjGenLinGroup.mk g * ProjGenLinGroup.mk (diagTau hτ) *
        (ProjGenLinGroup.mk g)⁻¹ = _
      rw [← hgw, map_mul, map_mul, map_inv]
      group
    obtain ⟨h1, h2⟩ := theta_centralizer_diagTau hK hτ hτ1 dM rfl
    have e : (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {dM})).map
        (conjM hπ hg).toMonoidHom =
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {y}) := by
      rw [CFSG.RankThree.PartTwo.KFacts.KP4.map_theta,
        CFSG.RankThree.PartTwo.KFacts.KP4.map_centralizer_singleton, hγ]
    rw [← e]
    exact ⟨h1.map _, by rw [Subgroup.card_map_of_injective (conjM hπ hg).injective, h2]⟩
  obtain ⟨h1, h2⟩ := key (ψ x) (by rw [MulEquiv.orderOf_eq]; exact hx)
  have e : (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {x})).map ψ.toMonoidHom =
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {ψ x}) := by
    rw [CFSG.RankThree.PartTwo.KFacts.KP4.map_theta,
      CFSG.RankThree.PartTwo.KFacts.KP4.map_centralizer_singleton]
  rw [← e] at h1 h2
  refine ⟨?_, by rwa [Subgroup.card_map_of_injective ψ.injective] at h2⟩
  have := h1.comap_of_injective ψ.toMonoidHom ψ.injective
  rwa [Subgroup.comap_map_eq_self_of_injective ψ.injective] at this

theorem step1515LA7L325Gen_of_kfacts'
    (h135 : Item135)
    (h142 : Item142R) (h1511 : Item1511R) (hloc : Claim1411LocalR) (hK : KL325SubgroupOrder) :
    Step1515LA7L325Gen :=
  step1515LA7L325Gen_of_kfacts h135 h142 h1511 hloc kl325ThetaCent hK

end CFSG.RankThree.PartTwo.Sec15
