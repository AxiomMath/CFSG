module

public import CFSG.RankThree.PartOne.KF.F128Act
public import CFSG.RankThree.PartOne.KF.F128Count
public import CFSG.RankThree.PartOne.KF.F128Syl
public import CFSG.RankThree.PartOne.K128.LangStep
public import CFSG.RankThree.PartOne.K1214.Omega
public import CFSG.RankThree.PartOne.S9.Sylow.ResidualBridge
public import CFSG.RankThree.PartOne.KF.F128Cyclic

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix
  CFSG.Blueprint
open CFSG.Assembly (evenRank)
open CFSG.RankThree.PartOne.K1214 (SylowShape)

@[expose] def KF128Rk2c : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (J E : Subgroup G) (a c d : G),
    p.Prime → 5 ≤ p → CFSG.IsQuasisimple J → evenRank G ≤ 3 → 2 ≤ CFSG.pRank p ↥J →
    ¬ p ∣ Nat.card (Subgroup.center J) → IsElementaryAbelian p E →
    E ≤ Subgroup.normalizer (J : Set G) → a ∈ E → d ∈ E → c ∈ E → d ∈ J → d ≠ 1 → c ≠ 1 →
    c ∈ Subgroup.centralizer (J : Set G) → InducesFieldAut p a J →
    ∃ y ∈ J, (∃ k : ℕ, orderOf y = p ^ k) ∧ y * d * y⁻¹ = d ∧ y * a * y⁻¹ ≠ a ∧
      ∀ e ∈ E, y * e * y⁻¹ * e⁻¹ ∈ Subgroup.zpowers d

theorem kf128Rk2c_of_syl (hT : ∀ t, TagFixedFacts t) (hK2 : ∀ t, Sec66T_K2 t) (hS : KF128Syl) :
    KF128Rk2c := by
  intro G _ _ p J E a c d hp hp5 hq he hrk hZ hEel hEN haE hdE hcE hdJ hd1 hc1 hcC hfa
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hEpow : ∀ x ∈ E, x ^ p = 1 := fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian x hx
  have hap : a ^ p = 1 := hEpow a haE
  have hcp : c ^ p = 1 := hEpow c hcE
  have hdp : d ^ p = 1 := hEpow d hdE
  have hac : a * c = c * a := Torsion37.mul_comm_of_isElementaryAbelian hEel haE hcE
  have hu : a ∈ Subgroup.normalizer (J : Set G) := hfa.1
  have huJ : a ∉ J ⊔ Subgroup.centralizer (J : Set G) := hfa.2.1
  have hs1 : ¬ (p : ℤ) ∣ 1 := by
    intro h
    have : p ∣ 1 := by exact_mod_cast h
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  set α : MulAut (↥J ⧸ Subgroup.center ↥J) := centerQuotientConj J ⟨a, hu⟩ with hα
  have hαp : α ^ p = 1 := centerQuotientConj_pow hu hap
  have hinn : α ∉ innerAut (↥J ⧸ Subgroup.center ↥J) := by
    rintro ⟨q, hq'⟩
    exact huJ (mem_sup_of_inner hq.1 hu hq'.symm)
  have hF : FixedFacts p α :=
    fixedFacts_of_setting hT hp hp5 hq hZ he hfa hap hu hap huJ hcC hc1 hcp hac hac
      ⟨1, 1, hs1, J.one_mem, by simp, by simp⟩
  have hLR2 := localRankLeTwo_of_evenRank he hp hp2 hZ hcC hc1 hcp
  have hLRA : LocalRankAut p (↥J ⧸ Subgroup.center ↥J) α :=
    localRankAut_of_evenRank he hp hp2 hZ hu hap huJ hcC hc1 hcp hac
  have hrkT : 2 ≤ CFSG.pRank p (↥J ⧸ Subgroup.center ↥J) := by
    rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp _ hZ]
    exact hrk
  obtain ⟨e', he2, hshT, hshN⟩ := hS ↥J hq ((Sec9A.evenRank_subgroup_le J).trans he) _
    (QuotientGroup.mk' (Subgroup.center ↥J)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) p hp hp5 (by rw [QuotientGroup.ker_mk']; exact hZ) hLR2 α hαp
    hinn hLRA hF hrkT
  have hEp : IsPGroup p E := fun g => ⟨1, Subtype.ext (by simpa using hEpow g.1 g.2)⟩
  obtain ⟨P, hP, hEP⟩ := exists_invariant_sylowOf hEN hEp
  have hPJ : P ≤ J := hP.le
  have hdord : orderOf d = p := orderOf_eq_prime hdp hd1
  have hdP : d ∈ P :=
    mem_of_pElement_mem_normalizer hP hdJ (hEP hdE) ⟨1, by rw [hdord, pow_one]⟩
  have hSyl := (CFSG.ABGLocalTools.isSylowOf_iff.1 hP)
  obtain ⟨φ₀⟩ := K1214.SylowShape.exists_equiv hp (Subgroup.center ↥J) hZ hshT
    (S := P.subgroupOf J) (hSyl.2.1.comap_subtype) hSyl.2.2
  let φ : ↥P ≃* (Fin 2 → Multiplicative (ZMod (p ^ e'))) :=
    (Subgroup.subgroupOfEquivOfLe hPJ).symm.trans φ₀
  have hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (K128.comm_of_equiv φ ⟨x, hx⟩ ⟨y, hy⟩)
  have haNP : a ∈ Subgroup.normalizer (P : Set G) := hEP haE
  set σ : MulAut ↥P := P.normalizerMonoidHom ⟨a, haNP⟩ with hσ
  have hσp : σ ^ p = 1 := by
    rw [hσ, ← map_pow]
    have : (⟨a, haNP⟩ : Subgroup.normalizer (P : Set G)) ^ p = 1 :=
      Subtype.ext (by simpa using hap)
    rw [this, map_one]
  have hσx : ∀ x : ↥P, ((σ x : ↥P) : G) = a * x * a⁻¹ := fun x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe P ⟨a, haNP⟩ x
  have hσk : ∀ (k : ℕ) (x : ↥P), (((σ ^ k) x : ↥P) : G) = a ^ k * x * (a ^ k)⁻¹ := by
    intro k x
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, hσx, ih]
      group
  have hCP : Nat.card ↥(P ⊓ Subgroup.centralizer ({a} : Set G)) ≤ p ^ (2 * (e' - 1)) :=
    card_le_of_fixedFacts hp hZ hu hF hshN (S := P ⊓ Subgroup.centralizer ({a} : Set G))
      (hSyl.2.1.to_le inf_le_left) (inf_le_left.trans hPJ) (fun s hs => by
        have := Subgroup.mem_centralizer_singleton_iff.1 hs.2
        calc a * s * a⁻¹ = (s * a) * a⁻¹ := by rw [this]
          _ = s := by group)
  have hcount : Nat.card (MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id ↥P)) ≤
      p ^ (2 * (e' - 1)) := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun x : MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id ↥P) =>
        (⟨(x.1 : G), x.1.2, ?_⟩ : ↥(P ⊓ Subgroup.centralizer ({a} : Set G)))) ?_) hCP
    · have hx : σ x.1 = x.1 := x.2
      have h1 : a * (x.1 : G) * a⁻¹ = x.1 := by
        rw [← hσx]
        exact congrArg Subtype.val hx
      show (x.1 : G) ∈ Subgroup.centralizer ({a} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (x.1 : G) * a = (a * x.1 * a⁻¹) * a := by rw [h1]
        _ = a * x.1 := by group
    · intro x y hxy
      have h := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext (by simpa using h))
  have hd'p : ((⟨d, hdP⟩ : ↥P)⁻¹) ^ p = 1 := by
    apply Subtype.ext
    simp [inv_pow, hdp]
  obtain ⟨y₀, hy₀⟩ := K128.exists_apply_mul_inv_eq hp5 he2 φ σ hσp hcount hd'p
  obtain ⟨-, hA2⟩ := K1214.act_lemma_mul hp5 (Or.inr rfl) (by omega) (Or.inr he2) φ σ hσp
  have hσd : σ (⟨d, hdP⟩ : ↥P)⁻¹ = (⟨d, hdP⟩ : ↥P)⁻¹ := hA2 _ hd'p
  let _ : CommGroup ↥P := { (inferInstance : Group ↥P) with mul_comm := K128.comm_of_equiv φ }
  have hpow := K128.pow_apply_eq_mul σ hσd hy₀
  obtain ⟨t, n, f₀, hf₀, hM, hX⟩ := hF.fieldAutT
  have hK2T := hK2 t (↥J ⧸ Subgroup.center ↥J) p hp hp5
    ⟨n, p * f₀, statedLieAdmissible_of_lieModel hM, hM⟩ hLR2
  have hLRA' : ∀ (v : G) (hv : v ∈ E),
      LocalRankAut p (↥J ⧸ Subgroup.center ↥J) (centerQuotientConj J ⟨v, hEN hv⟩) := by
    intro v hv
    by_cases hvin : centerQuotientConj J ⟨v, hEN hv⟩ ∈ innerAut (↥J ⧸ Subgroup.center ↥J)
    · intro _ h
      exact absurd hvin h
    · have hvJ : v ∉ J ⊔ Subgroup.centralizer (J : Set G) := fun h =>
        hvin ((centerQuotientConj_mem_innerAut_iff hq.1 (hEN hv)).2 h)
      exact localRankAut_of_evenRank he hp hp2 hZ (hEN hv) (hEpow v hv) hvJ hcC hc1 hcp
        (Torsion37.mul_comm_of_isElementaryAbelian hEel hv hcE)
  have hay : a * (y₀ : G) * a⁻¹ * (y₀ : G)⁻¹ = d⁻¹ := by
    have := congrArg Subtype.val hy₀
    rw [Subgroup.coe_mul, hσx, Subgroup.coe_inv, Subgroup.coe_inv] at this
    exact this
  have h1 : a * (y₀ : G) * a⁻¹ = d⁻¹ * y₀ := by
    calc a * (y₀ : G) * a⁻¹ = (a * (y₀ : G) * a⁻¹ * (y₀ : G)⁻¹) * y₀ := by group
      _ = d⁻¹ * y₀ := by rw [hay]
  have h2 : (y₀ : G) * a * (y₀ : G)⁻¹ * a⁻¹ = d := by
    calc (y₀ : G) * a * (y₀ : G)⁻¹ * a⁻¹ = (y₀ : G) * (a * (y₀ : G) * a⁻¹)⁻¹ := by group
      _ = (y₀ : G) * (d⁻¹ * y₀)⁻¹ := by rw [h1]
      _ = d := by group
  refine ⟨(y₀ : G), hPJ y₀.2, ?_, ?_, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hSyl.2.1 y₀
    have hk' : (y₀ : G) ^ (p ^ k) = 1 := congrArg Subtype.val hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hk')
    exact ⟨j, hj⟩
  · have := hPab _ y₀.2 d hdP
    calc (y₀ : G) * d * (y₀ : G)⁻¹ = (d * y₀) * (y₀ : G)⁻¹ := by rw [this]
      _ = d := by group
  · intro h
    have : (y₀ : G) * a * (y₀ : G)⁻¹ * a⁻¹ = 1 := by rw [h]; group
    rw [h2] at this
    exact hd1 this
  · intro e he
    obtain ⟨k, hk⟩ := exists_act_pow hp hq.1 hP hPab hEP hEel hEN hZ haE huJ hK2T hLRA' he
    have hek := hk (y₀ : G) y₀.2
    have hσky : a ^ k * (y₀ : G) * (a ^ k)⁻¹ = (d⁻¹) ^ k * y₀ := by
      rw [← hσk k y₀, hpow k]
      simp
    have h3 : (y₀ : G) * e * (y₀ : G)⁻¹ * e⁻¹ = d ^ k := by
      calc (y₀ : G) * e * (y₀ : G)⁻¹ * e⁻¹ = (y₀ : G) * (e * (y₀ : G) * e⁻¹)⁻¹ := by group
        _ = (y₀ : G) * ((d⁻¹) ^ k * y₀)⁻¹ := by rw [hek, hσky]
        _ = d ^ k := by group
    rw [h3]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers d) k

end CFSG.RankThree.PartOne
