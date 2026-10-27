module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.QuasisimpleCore
public import CFSG.Assembly.Defs
public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup
open scoped commutatorElement

lemma lf_comm_central {H : Type*} [Group H] (x y a b : H) (hxa : Commute x a) (hxb : Commute x b)
    (hxy : Commute x y) (hya : Commute y a) (hyb : Commute y b) :
    ⁅x * a, y * b⁆ = ⁅a, b⁆ := by
  have hxw : Commute x (a * y * b * a⁻¹) :=
    ((hxa.mul_right hxy).mul_right hxb).mul_right hxa.inv_right
  have hyz : Commute y (a * b * a⁻¹ * b⁻¹) :=
    ((hya.mul_right hyb).mul_right hya.inv_right).mul_right hyb.inv_right
  have e1 : x * (a * y * b * a⁻¹) * x⁻¹ = a * y * b * a⁻¹ := by
    rw [hxw.eq, mul_inv_cancel_right]
  have e2 : y * (a * b * a⁻¹ * b⁻¹) * y⁻¹ = a * b * a⁻¹ * b⁻¹ := by
    rw [hyz.eq, mul_inv_cancel_right]
  calc ⁅x * a, y * b⁆ = x * (a * y * b * a⁻¹) * x⁻¹ * b⁻¹ * y⁻¹ := by
        rw [commutatorElement_def]; group
    _ = a * y * b * a⁻¹ * b⁻¹ * y⁻¹ := by rw [e1]
    _ = y * (a * b * a⁻¹ * b⁻¹) * y⁻¹ := by rw [← hya.eq]; group
    _ = ⁅a, b⁆ := by rw [commutatorElement_def]; exact e2

lemma lf_comm_mem_of_normalizer {H : Type*} [Group H] (J : Subgroup H) (g : H)
    (hg : g ∈ normalizer (J : Set H)) (b : H) (hb : b ∈ J) : ⁅g, b⁆ ∈ J := by
  rw [commutatorElement_def]
  exact J.mul_mem ((Subgroup.mem_normalizer_iff.mp hg b).mp hb) (J.inv_mem hb)

theorem commute_of_trivial_mod_center {H : Type*} [Group H] (J : Subgroup H)
    (hJ : ⁅J, J⁆ = J) (g : H) (hg : g ∈ normalizer (J : Set H))
    (hgZ : ∀ j ∈ J, ∀ k ∈ J, ⁅⁅j, g⁆, k⁆ = 1) : ∀ j ∈ J, ⁅j, g⁆ = 1 := by
  have hcen : ∀ a ∈ J, ∀ k ∈ J, Commute ⁅g, a⁆ k := by
    intro a ha k hk
    have h1 : Commute ⁅a, g⁆ k := commutatorElement_eq_one_iff_mul_comm.mp (hgZ a ha k hk)
    rw [← commutatorElement_inv]
    exact h1.inv_left
  have hconj : ∀ a ∈ J, ∀ b ∈ J, g * ⁅a, b⁆ = ⁅a, b⁆ * g := by
    intro a ha b hb
    have h2 : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
      rw [commutatorElement_def, commutatorElement_def]; group
    have h3 : g * a * g⁻¹ = ⁅g, a⁆ * a := by
      rw [commutatorElement_def]; group
    have h4 : g * b * g⁻¹ = ⁅g, b⁆ * b := by
      rw [commutatorElement_def]; group
    rw [h3, h4] at h2
    have h5 : g * ⁅a, b⁆ * g⁻¹ = ⁅a, b⁆ :=
      h2.trans (lf_comm_central _ _ a b (hcen a ha a ha) (hcen a ha b hb)
        (hcen a ha _ (lf_comm_mem_of_normalizer J g hg b hb)) (hcen b hb a ha) (hcen b hb b hb))
    exact mul_inv_eq_iff_eq_mul.mp h5
  have hle : ⁅J, J⁆ ≤ Subgroup.centralizer {g} := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hconj a ha b hb).symm
  rw [hJ] at hle
  intro j hj
  exact commutatorElement_eq_one_iff_mul_comm.mpr
    (Subgroup.mem_centralizer_singleton_iff.mp (hle hj))

theorem lemmaF_core {H : Type*} [Group H] [Finite H] {p : ℕ} (hp : p.Prime) (J Ebar : Subgroup H)
    (hJ : CFSG.IsQuasisimple J)
    (hX : ∃ X : Subgroup H, X ≤ J ∧ (X.subgroupOf J).Normal ∧ IsPGroup p X ∧
      ∀ j ∈ J, ∀ e ∈ Ebar, ⁅j, e⁆ ∈ X) :
    ∀ j ∈ J, ∀ e ∈ Ebar, ⁅j, e⁆ = 1 := by
  obtain ⟨X, hXJ, hXn, hXp, hXe⟩ := hX
  have hJopen : CFSG.Open.IsQuasisimple J := ⟨Group.isPerfect_def.mp hJ.1, hJ.2.1⟩
  have hXc : X.subgroupOf J ≤ Subgroup.center J :=
    CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_center_of_quasisimple
      hJopen p hp (X.subgroupOf J) hXn hXp.comap_subtype
  have hcenZ : ∀ j ∈ J, ∀ e ∈ Ebar, ∀ k ∈ J, ⁅⁅j, e⁆, k⁆ = 1 := by
    intro j hj e he k hk
    have hzJ : ⁅j, e⁆ ∈ J := hXJ (hXe j hj e he)
    have hmem : (⟨⁅j, e⁆, hzJ⟩ : J) ∈ X.subgroupOf J :=
      Subgroup.mem_subgroupOf.mpr (hXe j hj e he)
    have hc := Subgroup.mem_center_iff.mp (hXc hmem) ⟨k, hk⟩
    have hkz : k * ⁅j, e⁆ = ⁅j, e⁆ * k := congrArg Subtype.val hc
    exact commutatorElement_eq_one_iff_mul_comm.mpr hkz.symm
  have hfwd : ∀ e ∈ Ebar, ∀ j ∈ J, e * j * e⁻¹ ∈ J := by
    intro e he j hj
    have h1 : ⁅e, j⁆ ∈ J := by
      rw [← commutatorElement_inv]
      exact J.inv_mem (hXJ (hXe j hj e he))
    have h2 : e * j * e⁻¹ = ⁅e, j⁆ * j := by
      rw [commutatorElement_def]; group
    rw [h2]
    exact J.mul_mem h1 hj
  have hnorm : ∀ e ∈ Ebar, e ∈ normalizer (J : Set H) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hfwd e he h hh
    · intro hh
      have h3 := hfwd e⁻¹ (Ebar.inv_mem he) (e * h * e⁻¹) hh
      have heq : e⁻¹ * (e * h * e⁻¹) * e⁻¹⁻¹ = h := by group
      rw [heq] at h3
      exact h3
  intro j hj e he
  exact commute_of_trivial_mod_center J (Subgroup.isPerfect_iff.mp hJ.1) e (hnorm e he)
    (fun j' hj' k hk => hcenZ j' hj' e he k hk) j hj

lemma lf_comm_mem_inf {M : Type*} [Group M] (K E P₀ : Subgroup M)
    (hEK : ∀ e ∈ E, e ∈ normalizer (K : Set M))
    (hEP₀ : E ≤ P₀) (hKP₀ : ∀ k ∈ K, k ∈ normalizer (P₀ : Set M))
    (k : M) (hk : k ∈ K) (e : M) (he : e ∈ E) : ⁅k, e⁆ ∈ K ⊓ P₀ := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have h1 : e * k⁻¹ * e⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hEK e he) k⁻¹).mp (K.inv_mem hk)
    have h2 : ⁅k, e⁆ = k * (e * k⁻¹ * e⁻¹) := by
      rw [commutatorElement_def]; group
    rw [h2]
    exact K.mul_mem hk h1
  · rw [commutatorElement_def]
    exact P₀.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKP₀ k hk) e).mp (hEP₀ he))
      (P₀.inv_mem (hEP₀ he))

lemma lf_conj_inf {M : Type*} [Group M] (K P₀ : Subgroup M)
    (hKP₀ : ∀ k ∈ K, k ∈ normalizer (P₀ : Set M)) (k : M) (hk : k ∈ K) (a : M)
    (ha : a ∈ K ⊓ P₀) : k * a * k⁻¹ ∈ K ⊓ P₀ := by
  obtain ⟨ha1, ha2⟩ := Subgroup.mem_inf.mp ha
  exact Subgroup.mem_inf.mpr ⟨K.mul_mem (K.mul_mem hk ha1) (K.inv_mem hk),
    (Subgroup.mem_normalizer_iff.mp (hKP₀ k hk) a).mp ha2⟩

lemma lf_map_normal {M : Type*} [Group M] (R : Subgroup M) [R.Normal] (K P₀ : Subgroup M)
    (hKP₀ : ∀ k ∈ K, k ∈ normalizer (P₀ : Set M)) :
    (((K ⊓ P₀).map (QuotientGroup.mk' R)).subgroupOf (K.map (QuotientGroup.mk' R))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨a, ha, han⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hn)
  obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp g.2
  rw [Subgroup.mem_subgroupOf]
  refine Subgroup.mem_map.mpr ⟨k * a * k⁻¹, lf_conj_inf K P₀ hKP₀ k hk a ha, ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hkg, ← han, map_mul, map_mul,
    map_inv]

theorem lemmaF {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime) (R : Subgroup M) [R.Normal]
    (K E P₀ : Subgroup M) (hKperf : ⁅K, K⁆ = K) (hEK : ∀ e ∈ E, e ∈ normalizer (K : Set M))
    (hP₀ : IsPGroup p P₀) (hEP₀ : E ≤ P₀) (hKP₀ : ∀ k ∈ K, k ∈ normalizer (P₀ : Set M))
    (hq : CFSG.IsQuasisimple (K.map (QuotientGroup.mk' R))) :
    ∀ e ∈ E, ∀ k ∈ K, ⁅(e : M ⧸ R), (k : M ⧸ R)⁆ = 1 := by
  have hKP : IsPGroup p (K ⊓ P₀ : Subgroup M) := hP₀.to_inf_right
  have hmem : ∀ j ∈ K.map (QuotientGroup.mk' R), ∀ e' ∈ E.map (QuotientGroup.mk' R),
      ⁅j, e'⁆ ∈ (K ⊓ P₀).map (QuotientGroup.mk' R) := by
    intro j hj e' he'
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hj
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp he'
    rw [← map_commutatorElement]
    exact Subgroup.mem_map_of_mem _ (lf_comm_mem_inf K E P₀ hEK hEP₀ hKP₀ k hk e he)
  have hcore := lemmaF_core hp (K.map (QuotientGroup.mk' R)) (E.map (QuotientGroup.mk' R)) hq
    ⟨(K ⊓ P₀).map (QuotientGroup.mk' R), Subgroup.map_mono inf_le_left,
      lf_map_normal R K P₀ hKP₀, hKP.map (QuotientGroup.mk' R), hmem⟩
  intro e he k hk
  have h1 : ⁅(k : M ⧸ R), (e : M ⧸ R)⁆ = 1 :=
    hcore (QuotientGroup.mk' R k) (Subgroup.mem_map_of_mem _ hk)
      (QuotientGroup.mk' R e) (Subgroup.mem_map_of_mem _ he)
  rw [← commutatorElement_inv, h1, inv_one]

end CFSG.RankThree.PartTwo.Sec13.F135Last
