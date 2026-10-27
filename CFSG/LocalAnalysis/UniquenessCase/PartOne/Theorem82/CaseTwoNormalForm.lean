module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoTransitive
public import CFSG.GroupTheory.WreathThree
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs812
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSplit
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKernel
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CComponents

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace SylowThreeData

variable (d : SylowThreeData G)

theorem map_conj_H_of_normalizes {g : G} (hgS : g ∈ Subgroup.normalizer (d.S : Set G))
    (hgL : ∀ i, (d.Lf i).map (MulAut.conj g).toMonoidHom = d.Lf (i + 1)) (i : Fin 3) :
    (d.H i).map (MulAut.conj g).toMonoidHom = d.H (i + 1) := by
  have hS : d.S.map (MulAut.conj g).toMonoidHom = d.S :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hgS
  rw [d.H_def i, d.H_def (i + 1), Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective, hS,
    hgL i]

theorem base_eq_of_maps {g : G} (hgS : g ∈ Subgroup.normalizer (d.S : Set G))
    (hgL : ∀ i, (d.Lf i).map (MulAut.conj g).toMonoidHom = d.Lf (i + 1)) :
    CFSG.GroupTheory.WreathThree.base (d.H 0) g = d.S := by
  have hH (i : Fin 3) : (d.H i).map (MulAut.conj g).toMonoidHom = d.H (i + 1) :=
    d.map_conj_H_of_normalizes hgS hgL i
  have hcomp : (MulAut.conj (g ^ 2)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show g ^ 2 * x * (g ^ 2)⁻¹ = g * (g * x * g⁻¹) * g⁻¹ by rw [pow_two]; group]
  have hH0 : (d.H 0).map (MulAut.conj g).toMonoidHom = d.H 1 := by
    simpa using hH 0
  have hH1 : (d.H 1).map (MulAut.conj g).toMonoidHom = d.H 2 := by
    simpa using hH 1
  have h2 : (d.H 0).map (MulAut.conj (g ^ 2)).toMonoidHom = d.H 2 := by
    rw [hcomp, ← Subgroup.map_map, hH0, hH1]
  change d.H 0 ⊔ (d.H 0).map (MulAut.conj g).toMonoidHom ⊔
    (d.H 0).map (MulAut.conj (g ^ 2)).toMonoidHom = d.S
  rw [hH0, h2, d.S_eq_sup]

theorem card_S_eq_card_H_pow_three {g : G} (hgS : g ∈ Subgroup.normalizer (d.S : Set G))
    (hgL : ∀ i, (d.Lf i).map (MulAut.conj g).toMonoidHom = d.Lf (i + 1)) :
    Nat.card d.S = Nat.card (d.H 0) ^ 3 := by
  have hH (i : Fin 3) : (d.H i).map (MulAut.conj g).toMonoidHom = d.H (i + 1) :=
    d.map_conj_H_of_normalizes hgS hgL i
  have hH0 : (d.H 0).map (MulAut.conj g).toMonoidHom = d.H 1 := by
    simpa using hH 0
  have hH1 : (d.H 1).map (MulAut.conj g).toMonoidHom = d.H 2 := by
    simpa using hH 1
  have hcard1 : Nat.card ↥(d.H 1) = Nat.card ↥(d.H 0) := by
    rw [← hH0, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hcard2 : Nat.card ↥(d.H 2) = Nat.card ↥(d.H 0) := by
    rw [← hH1, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hcard1
  have hH01 : d.H 0 ⊔ d.H 1 ≤ d.Lf 0 ⊔ d.Lf 1 :=
    sup_le ((d.H_le_Lf 0).trans le_sup_left) ((d.H_le_Lf 1).trans le_sup_right)
  have hdisj01 : Disjoint (d.H 0) (d.H 1) := by
    rw [Subgroup.disjoint_def]
    intro x hx0 hx1
    exact d.eq_one_of_mem_Lf_of_mem_sup (i := 0) (j := 1) (k := 2) (by decide) (by decide)
      (by decide) (d.H_le_S 0 hx0) (d.H_le_Lf 0 hx0) (Subgroup.mem_sup_left (d.H_le_Lf 1 hx1))
  have hdisj012 : Disjoint (d.H 0 ⊔ d.H 1) (d.H 2) := by
    rw [Subgroup.disjoint_def]
    intro x hx01 hx2
    exact d.eq_one_of_mem_Lf_of_mem_sup (i := 2) (j := 0) (k := 1) (by decide) (by decide)
      (by decide) (d.H_le_S 2 hx2) (d.H_le_Lf 2 hx2)
      (hH01 hx01)
  have hnorm01 : d.H 1 ≤ Subgroup.normalizer (d.H 0 : Set G) := by
    refine (show d.H 1 ≤ Subgroup.centralizer (d.H 0 : Set G) from ?_).trans
      (Subgroup.centralizer_le_normalizer _)
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact d.S_commute a b (d.H_le_S 0 ha) (d.H_le_S 1 hb)
  have hnorm012 : d.H 2 ≤ Subgroup.normalizer ((d.H 0 ⊔ d.H 1 : Subgroup G) : Set G) := by
    have hcent0 : d.H 2 ≤ Subgroup.centralizer (d.H 0 : Set G) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact d.S_commute a b (d.H_le_S 0 ha) (d.H_le_S 2 hb)
    have hcent1 : d.H 2 ≤ Subgroup.centralizer (d.H 1 : Set G) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact d.S_commute a b (d.H_le_S 1 ha) (d.H_le_S 2 hb)
    exact (le_inf (hcent0.trans (Subgroup.centralizer_le_normalizer _))
      (hcent1.trans (Subgroup.centralizer_le_normalizer _))).trans
      (Subgroup.inf_normalizer_le_normalizer_sup (d.H 0) (d.H 1))
  have hcard01 : Nat.card ↥(d.H 0 ⊔ d.H 1) = Nat.card ↥(d.H 0) * Nat.card ↥(d.H 1) :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer (d.H 0) (d.H 1)
      hnorm01 hdisj01
  have hcard012 : Nat.card ↥((d.H 0 ⊔ d.H 1) ⊔ d.H 2) =
      Nat.card ↥(d.H 0 ⊔ d.H 1) * Nat.card ↥(d.H 2) :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer (d.H 0 ⊔ d.H 1) (d.H 2)
      hnorm012 hdisj012
  rw [d.S_eq_sup, hcard012, hcard01, hcard1, hcard2]
  ring

theorem isWreathThree_of_maps {g : G} (hg3S : g ^ 3 ∈ d.S)
    (hgS : g ∈ Subgroup.normalizer (d.S : Set G))
    (hgL : ∀ i, (d.Lf i).map (MulAut.conj g).toMonoidHom = d.Lf (i + 1)) :
    CFSG.GroupTheory.WreathThree.IsWreathThree (d.H 0) g := by
  have hbase : CFSG.GroupTheory.WreathThree.base (d.H 0) g = d.S :=
    d.base_eq_of_maps hgS hgL
  refine ⟨?_, d.isCyclic_H 0, d.H_ne_bot 0, ?_, ?_, ?_⟩
  · exact IsPGroup.to_le d.hS.isPGroup (d.H_le_S 0)
  · intro a ha b hb
    rw [hbase] at ha hb
    exact d.S_commute a b ha hb
  · rw [hbase, d.card_S_eq_card_H_pow_three hgS hgL]
  · rw [hbase]
    exact hg3S

theorem permHom_pow_three_eq_one (hinj : Function.Injective d.Lf)
    (hperm : ∀ m ∈ d.M, ∀ i, ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j)
    {g : G} (hg : g ∈ d.M) (hg3 : IsPGroup 3 (Subgroup.zpowers g)) :
    d.permHom hinj hperm ⟨g, hg⟩ ^ 3 = 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hg3.exists_card_eq
  have hord : orderOf g = 3 ^ k := by
    rw [← Nat.card_zpowers, hk]
  have hgk : (⟨g, hg⟩ : ↥d.M) ^ (3 ^ k) = 1 := by
    apply Subtype.ext
    show g ^ (3 ^ k) = 1
    rw [← hord, pow_orderOf_eq_one]
  have hσpow : (d.permHom hinj hperm ⟨g, hg⟩) ^ (3 ^ k) = 1 := by
    rw [← map_pow, hgk, map_one]
  have hdvd1 : orderOf (d.permHom hinj hperm ⟨g, hg⟩) ∣ 3 ^ k :=
    orderOf_dvd_of_pow_eq_one hσpow
  have hdvd2 : orderOf (d.permHom hinj hperm ⟨g, hg⟩) ∣ 6 := by
    have h := orderOf_dvd_natCard (d.permHom hinj hperm ⟨g, hg⟩)
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h
    norm_num at h
    exact h
  obtain ⟨j, -, hdj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd1
  rw [hdj] at hdvd2
  have hj1 : j ≤ 1 := by
    by_contra hcon
    have h2 : 2 ≤ j := by omega
    have h9 : 9 ≤ 3 ^ j := by
      calc (9 : ℕ) = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) h2
    have hle : 3 ^ j ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd2
    omega
  rw [← orderOf_dvd_iff_pow_eq_one, hdj]
  interval_cases j <;> simp

end SylowThreeData

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

theorem map_conj_H (i : Fin 3) : (t.d.H i).map (MulAut.conj t.y).toMonoidHom = t.d.H (i + 1) := by
  refine t.d.map_conj_H_of_normalizes ?_ t.hyL i
  rw [t.hdS]
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer t.hyP, c.le_normalizer_L (t.hP.le t.hyP)⟩

theorem map_conj_A (i : Fin 3) : (t.d.A i).map (MulAut.conj t.y).toMonoidHom = t.d.A (i + 1) := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [t.d.mem_A_iff] at ha ⊢
    refine ⟨?_, ?_⟩
    · have hmem : MulAut.conj t.y a ∈ (t.d.H i).map (MulAut.conj t.y).toMonoidHom :=
        Subgroup.mem_map_of_mem _ ha.1
      rwa [t.map_conj_H i] at hmem
    · calc (t.y * a * t.y⁻¹) ^ 3 = (MulAut.conj t.y) (a ^ 3) := by
            rw [map_pow]
            rfl
        _ = 1 := by rw [ha.2, map_one]
  · intro hx
    rw [t.d.mem_A_iff] at hx
    obtain ⟨hxH, hx3⟩ := hx
    refine ⟨MulAut.conj t.y⁻¹ x, ?_, ?_⟩
    · rw [t.d.mem_A_iff]
      have hxH' : x ∈ (t.d.H i).map (MulAut.conj t.y).toMonoidHom := by
        rwa [t.map_conj_H i]
      obtain ⟨b, hb, hbx⟩ := Subgroup.mem_map.mp hxH'
      refine ⟨?_, ?_⟩
      · rw [← hbx]
        have hconj : (MulAut.conj t.y⁻¹) ((MulAut.conj t.y).toMonoidHom b) = b := by
          simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom, inv_inv]
          group
        rw [hconj]
        exact hb
      · calc (MulAut.conj t.y⁻¹ x) ^ 3 = MulAut.conj t.y⁻¹ (x ^ 3) :=
            (map_pow (MulAut.conj t.y⁻¹) x 3).symm
          _ = 1 := by rw [hx3, map_one]
    · have hconj : (MulAut.conj t.y).toMonoidHom ((MulAut.conj t.y⁻¹) x) = x := by
        simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom, inv_inv]
        group
      rw [hconj]

theorem isWreathThree : CFSG.GroupTheory.WreathThree.IsWreathThree (t.d.H 0) t.y := by
  refine t.d.isWreathThree_of_maps ?_ ?_ t.hyL
  · rw [t.hy3]
    exact t.d.S.one_mem
  rw [t.hdS]
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer t.hyP, c.le_normalizer_L (t.hP.le t.hyP)⟩

theorem base_eq : CFSG.GroupTheory.WreathThree.base (t.d.H 0) t.y = t.d.S := by
  refine t.d.base_eq_of_maps ?_ t.hyL
  rw [t.hdS]
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer t.hyP, c.le_normalizer_L (t.hP.le t.hyP)⟩

theorem orderOf_y : orderOf t.y = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime t.hy3 ?_
  intro h1
  have h0 := t.hyL 0
  rw [h1] at h0
  have hfix : (t.d.Lf 0).map (MulAut.conj (1 : G)).toMonoidHom = t.d.Lf 0 := by
    rw [show MulAut.conj (1 : G) = 1 from map_one (MulAut.conj : G →* MulAut G)]
    exact Subgroup.map_id _
  have h01 : (0 : Fin 3) = 1 := t.hinj (by rw [← hfix]; simpa using h0)
  exact (by decide : (0 : Fin 3) ≠ 1) h01

theorem eq_AA_of_isElemAbelian {E : Subgroup G} (hEP : E ≤ t.P)
    (hE : CFSG.Open.IsElemAbelian 3 E) (hEcard : Nat.card E = 27) : E = t.d.AA := by
  obtain ⟨A, -, hA_elem, hA_card, -, hA_unique⟩ :=
    CFSG.GroupTheory.WreathThree.exists_unique_elemAbelian t.isWreathThree t.hy3
  have hE_le : E ≤ CFSG.GroupTheory.WreathThree.base (t.d.H 0) t.y ⊔
      Subgroup.zpowers t.y := by
    rw [t.base_eq, t.hPy]
    exact hEP
  have hEeq : E = A := hA_unique E hE_le hE hEcard
  have hAA_le : t.d.AA ≤ CFSG.GroupTheory.WreathThree.base (t.d.H 0) t.y ⊔
      Subgroup.zpowers t.y := by
    rw [t.base_eq]
    exact t.d.AA_le_S.trans le_sup_left
  have hAAeq : t.d.AA = A := hA_unique t.d.AA hAA_le t.d.isElemAbelian_AA t.d.card_AA
  exact hEeq.trans hAAeq.symm

theorem mem_AA_or_exists_conj_eq {x : G} (hxP : x ∈ t.P) (hx3 : x ^ 3 = 1) :
    x ∈ t.d.AA ∨ ∃ s ∈ t.d.S, s * x * s⁻¹ = t.y ∨ s * x * s⁻¹ = t.y⁻¹ := by
  by_cases hxS : x ∈ t.d.S
  · exact Or.inl (t.d.mem_AA_of_pow_eq_one hxS hx3)
  · right
    have hx : x ∈ CFSG.GroupTheory.WreathThree.base (t.d.H 0) t.y ⊔
        Subgroup.zpowers t.y := by
      rw [t.base_eq, t.hPy]
      exact hxP
    obtain ⟨s, hs, hconj⟩ :=
      CFSG.GroupTheory.WreathThree.exists_conj_eq_of_pow_three t.isWreathThree t.hy3 hx
        (by rwa [t.base_eq]) hx3
    exact ⟨s, by rwa [t.base_eq] at hs, hconj⟩

theorem y_not_mem_L : t.y ∉ c.L := by
  intro hyL
  have hyL' : t.y ∈ t.d.L := by rwa [← t.hdL] at hyL
  have hLnorm (i : Fin 3) : t.d.L ≤ Subgroup.normalizer (t.d.Lf i : Set G) := by
    rw [t.d.hL]
    exact sup_le (sup_le (t.d.hLnorm i 0) (t.d.hLnorm i 1)) (t.d.hLnorm i 2)
  have hnorm : t.y ∈ Subgroup.normalizer (t.d.Lf 0 : Set G) := hLnorm 0 hyL'
  have hfix : (t.d.Lf 0).map (MulAut.conj t.y).toMonoidHom = t.d.Lf 0 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hnorm
  have h01 : (0 : Fin 3) = 1 := t.hinj (by rw [← hfix]; simpa using t.hyL 0)
  exact (by decide : (0 : Fin 3) ≠ 1) h01

end CaseTwoTransitive

namespace Ctx812E

theorem exists_caseTwoTransitive (c : Ctx812E G) (hK8 : OuterThreeSplit)
    (d : SylowThreeData G) (hdM : d.M = c.S.M) (hdL : d.L = c.L)
    (hinj : Function.Injective d.Lf)
    (hcomp : ∀ i, CFSG.Yardstones.Mf4cdcdf2e013.Asc83CComponent c.S.M (d.Lf i))
    (hperm : ∀ m ∈ c.S.M, ∀ i, ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P c.S.M) (hdS : d.S = P ⊓ c.L)
    (hII : ¬ ∀ i, P ≤ Subgroup.normalizer (d.Lf i : Set G)) :
    ∃ t : CaseTwoTransitive c, t.d = d ∧ t.P = P := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPM : P ≤ d.M := by rw [hdM]; exact hP.le
  have hperm' : ∀ m ∈ d.M, ∀ i, ∃ j,
      (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j := by
    intro m hm i
    exact hperm m (hdM ▸ hm) i
  have hSP : d.S ≤ P := by rw [hdS]; exact inf_le_left
  have hP0 : P ⊓ ⨅ i, Subgroup.normalizer (d.Lf i : Set G) = d.S :=
    (Ctx812E.inf_iInf_normalizer_Lf_eq c hK8 d hdM hdL hcomp hP hdS).trans hdS.symm
  rcases d.forall_le_normalizer_or_exists_forall_map_ne hinj hperm' hPM hP.isPGroup with
    hnorm | ⟨y₀, hy₀P, hy₀move⟩
  · exact absurd hnorm hII
  have hM : y₀ ∈ d.M := hPM hy₀P
  have normS {g : G} (hgP : g ∈ P) : g ∈ Subgroup.normalizer (d.S : Set G) := by
    rw [hdS]
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hgP, c.le_normalizer_L (hdM ▸ hPM hgP)⟩
  have pow3_mem_S {g : G} (hgP : g ∈ P) (hgm : g ∈ d.M)
      (hgσ : d.permHom hinj hperm' ⟨g, hgm⟩ ^ 3 = 1) : g ^ 3 ∈ d.S := by
    have hg3M : g ^ 3 ∈ d.M := d.M.pow_mem hgm 3
    have hperm3 : d.permHom hinj hperm' ⟨g ^ 3, hg3M⟩ = 1 := by
      rw [show (⟨g ^ 3, hg3M⟩ : ↥d.M) = ⟨g, hgm⟩ ^ 3 from Subtype.ext rfl, map_pow, hgσ]
    have hnorm (i : Fin 3) : g ^ 3 ∈ Subgroup.normalizer (d.Lf i : Set G) :=
      (d.mem_normalizer_Lf_iff hinj hperm' ⟨g ^ 3, hg3M⟩ i).mpr (by rw [hperm3]; rfl)
    have hmem : g ^ 3 ∈ P ⊓ ⨅ i, Subgroup.normalizer (d.Lf i : Set G) :=
      ⟨P.pow_mem hgP 3, Subgroup.mem_iInf.mpr hnorm⟩
    rwa [hP0] at hmem
  let σ : Equiv.Perm (Fin 3) := d.permHom hinj hperm' ⟨y₀, hM⟩
  have hσ3 : σ ^ 3 = 1 :=
    d.permHom_pow_three_eq_one hinj hperm' hM
      (hP.isPGroup.to_le (Subgroup.zpowers_le.mpr hy₀P))
  have hσfix : ∀ i, σ i ≠ i := by
    intro i hi
    exact hy₀move i ((d.map_conj_Lf_eq hinj hperm' ⟨y₀, hM⟩ i).trans (by rw [hi]))
  have hσ0 : σ 0 = 1 ∨ σ 0 = 2 := by
    have hlt : (σ 0).val < 3 := (σ 0).isLt
    have hne : (σ 0).val ≠ 0 := by
      intro h
      exact hσfix 0 (Fin.ext (by simpa using h))
    have hcases : (σ 0).val = 1 ∨ (σ 0).val = 2 := by omega
    rcases hcases with h | h
    · exact Or.inl (Fin.ext (by simpa using h))
    · exact Or.inr (Fin.ext (by simpa using h))
  have hshift : ∀ τ : Equiv.Perm (Fin 3), τ ^ 3 = 1 → (∀ i, τ i ≠ i) → τ 0 = 1 →
      τ = finRotate 3 := by decide
  have hshiftInv : ∀ τ : Equiv.Perm (Fin 3), τ ^ 3 = 1 → (∀ i, τ i ≠ i) → τ 0 = 2 →
      τ = (finRotate 3)⁻¹ := by decide
  obtain ⟨y₁, hy₁P, hy₁3S, hy₁L⟩ : ∃ y₁ ∈ P, y₁ ^ 3 ∈ d.S ∧
      ∀ i, (d.Lf i).map (MulAut.conj y₁).toMonoidHom = d.Lf (i + 1) := by
    rcases hσ0 with h0 | h0
    · have hσeq : σ = finRotate 3 := hshift σ hσ3 hσfix h0
      have hσeq3 : d.permHom hinj hperm' ⟨y₀, hM⟩ ^ 3 = 1 := by simpa [σ] using hσ3
      refine ⟨y₀, hy₀P, pow3_mem_S hy₀P hM hσeq3, ?_⟩
      intro i
      rw [d.map_conj_Lf_eq hinj hperm' ⟨y₀, hM⟩ i]
      change d.Lf (σ i) = d.Lf (i + 1)
      rw [hσeq, finRotate_apply]
    · have hσeq : σ = (finRotate 3)⁻¹ := hshiftInv σ hσ3 hσfix h0
      have hy₁M : y₀⁻¹ ∈ d.M := d.M.inv_mem hM
      have hσinv : d.permHom hinj hperm' ⟨y₀⁻¹, hy₁M⟩ = σ⁻¹ := by
        rw [show (⟨y₀⁻¹, hy₁M⟩ : ↥d.M) = ⟨y₀, hM⟩⁻¹ from Subtype.ext rfl, map_inv]
      have hσinv3 : d.permHom hinj hperm' ⟨y₀⁻¹, hy₁M⟩ ^ 3 = 1 := by
        rw [hσinv, show (σ⁻¹) ^ 3 = (σ ^ 3)⁻¹ by group, hσ3, inv_one]
      refine ⟨y₀⁻¹, P.inv_mem hy₀P, pow3_mem_S (P.inv_mem hy₀P) hy₁M hσinv3, ?_⟩
      intro i
      rw [d.map_conj_Lf_eq hinj hperm' ⟨y₀⁻¹, hy₁M⟩ i, hσinv]
      change d.Lf (σ⁻¹ i) = d.Lf (i + 1)
      rw [show σ⁻¹ = finRotate 3 by rw [hσeq, inv_inv], finRotate_apply]
  have hy₁M : y₁ ∈ d.M := hPM hy₁P
  have hbase₁ : CFSG.GroupTheory.WreathThree.base (d.H 0) y₁ = d.S :=
    d.base_eq_of_maps (normS hy₁P) hy₁L
  have hw : CFSG.GroupTheory.WreathThree.IsWreathThree (d.H 0) y₁ :=
    d.isWreathThree_of_maps hy₁3S (normS hy₁P) hy₁L
  obtain ⟨s, hs, hs3⟩ := CFSG.GroupTheory.WreathThree.exists_mul_pow_three_eq_one hw
  have hsS : s ∈ d.S := by rwa [hbase₁] at hs
  have hsL : s ∈ d.L := d.hS.le hsS
  have hLnorm (i : Fin 3) : d.L ≤ Subgroup.normalizer (d.Lf i : Set G) := by
    rw [d.hL]
    exact sup_le (sup_le (d.hLnorm i 0) (d.hLnorm i 1)) (d.hLnorm i 2)
  have hsFix (i : Fin 3) : (d.Lf i).map (MulAut.conj s).toMonoidHom = d.Lf i :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hLnorm i hsL)
  let y : G := y₁ * s
  have hyP : y ∈ P := P.mul_mem hy₁P (hSP hsS)
  have hy3 : y ^ 3 = 1 := hs3
  have hcomp_conj : (MulAut.conj (y₁ * s)).toMonoidHom =
      (MulAut.conj y₁).toMonoidHom.comp (MulAut.conj s).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hyL (i : Fin 3) : (d.Lf i).map (MulAut.conj y).toMonoidHom = d.Lf (i + 1) := by
    show (d.Lf i).map (MulAut.conj (y₁ * s)).toMonoidHom = d.Lf (i + 1)
    rw [hcomp_conj, ← Subgroup.map_map, hsFix i, hy₁L i]
  have hyMove (i : Fin 3) : (d.Lf i).map (MulAut.conj y).toMonoidHom ≠ d.Lf i := by
    rw [hyL i]
    intro h
    exact (by fin_cases i <;> decide : ∀ j : Fin 3, j + 1 ≠ j) i (hinj h)
  have hsup := (d.kernel_sup_zpowers_eq hinj hperm' hPM hP.isPGroup hyP hyMove).2
  have hPy : d.S ⊔ Subgroup.zpowers y = P := by
    rw [← hP0]
    exact hsup
  exact ⟨⟨d, hdM, hdL, hinj, hcomp, hperm, P, hP, hdS, y, hyP, hy3, hyL, hPy⟩, rfl, rfl⟩

end Ctx812E

namespace Ctx812

theorem exists_caseTwoTransitive (c : Ctx812 G) (hK8 : OuterThreeSplit)
    (d : SylowThreeData G) (hdM : d.M = c.S.M) (hdL : d.L = c.L)
    (hinj : Function.Injective d.Lf)
    (hcomp : ∀ i, CFSG.Yardstones.Mf4cdcdf2e013.Asc83CComponent c.S.M (d.Lf i))
    (hperm : ∀ m ∈ c.S.M, ∀ i, ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P c.S.M) (hdS : d.S = P ⊓ c.L)
    (hII : ¬ ∀ i, P ≤ Subgroup.normalizer (d.Lf i : Set G)) :
    ∃ t : CaseTwoTransitive c.toCtx812E, t.d = d ∧ t.P = P :=
  Ctx812E.exists_caseTwoTransitive c.toCtx812E hK8 d hdM hdL hinj hcomp hperm hP hdS hII

end Ctx812

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
