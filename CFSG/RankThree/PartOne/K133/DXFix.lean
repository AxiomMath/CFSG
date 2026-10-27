module

public import CFSG.RankThree.PartOne.K133.ParA
public import CFSG.RankThree.PartOne.K133.Count
import CFSG.RankThree.PartOne.S9.Vanishing.Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne
open scoped commutatorElement

variable {G : Type} [Group G]

theorem thetaQuotientCentralizer_le_autFixedInG_of_quasisimple [Finite G] {p : ℕ} (hp : p.Prime)
    {E : Subgroup G} {t : MulAut E} {K X : Subgroup G} (hE : IsElementaryAbelian p E)
    (hcard : Nat.card E = p ^ 4) (hcardC : Nat.card ↥(autFixedInG E t) = p ^ 3) (ht1 : t ≠ 1)
    (hKq : CFSG.IsQuasisimple ↥K) (hEK : E ≤ Subgroup.normalizer (K : Set G))
    (hCK : autFixedInG E t ≤ Subgroup.centralizer (K : Set G))
    (hlift : ∃ (k : G) (hk : k ∈ Subgroup.normalizer (E : Set G)), k ∈ K ∧
      E.normalizerMonoidHom ⟨k, hk⟩ = t)
    (hKX : K ≤ X) :
    thetaQuotientCentralizer p E X ≤ autFixedInG E t := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hKperf : Group.IsPerfect ↥K := hKq.1
  obtain ⟨hNX, hNn⟩ := theta_le_and_normal p X
  obtain ⟨hNs, -⟩ := theta_solvable_and_not_dvd hp X
  intro y hy
  by_contra hyC
  obtain ⟨hyE, -, -⟩ := mem_thetaQuotientCentralizer_iff.1 hy
  have hKy : ⁅K, Subgroup.zpowers y⁆ = ⊥ := by
    have hz : ⁅K, Subgroup.zpowers y⁆ ≤ inSubgroup (aschbacherSolvableCore p) X :=
      (Subgroup.commutator_mono hKX le_rfl).trans (commutator_zpowers_le_theta hy)
    have hzK : ⁅K, Subgroup.zpowers y⁆ ≤ K := by
      rw [Subgroup.commutator_le]
      intro k hk z hz'
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz'
      have hyz : y ^ n ∈ Subgroup.normalizer (K : Set G) :=
        Subgroup.zpow_mem _ (hEK hyE) n
      have h1 : ⁅k, y ^ n⁆ = k * (y ^ n * k⁻¹ * (y ^ n)⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [h1]
      exact K.mul_mem hk ((Subgroup.mem_normalizer_iff.mp hyz _).mp (K.inv_mem hk))
    let N₁ : Subgroup ↥K := (inSubgroup (aschbacherSolvableCore p) X).subgroupOf K
    have hN₁n : N₁.Normal := by
      refine ⟨fun n hn k => ?_⟩
      show ((k * n * k⁻¹ : ↥K) : G) ∈ inSubgroup (aschbacherSolvableCore p) X
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.mp
        (Vanish.le_normalizer_inSubgroup_aschbacherSolvableCore p X (hKX k.2)) _).mp hn
    rcases LocalCores.quasisimple_normal_subgroups hKq hN₁n with htop | hcen
    · exfalso
      have hKθ' : K ≤ inSubgroup (aschbacherSolvableCore p) X := fun k hk => by
        have : (⟨k, hk⟩ : ↥K) ∈ N₁ := htop ▸ Subgroup.mem_top _
        exact this
      have : Group.IsSolvable ↥K :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKθ')
          (Subgroup.inclusion_injective _)
      have : Nontrivial ↥K := LocalCores.isQuasisimple_nontrivial hKq
      exact Group.IsPerfect.not_isSolvable ↥K inferInstance
    · have h1 : ⁅⁅K, Subgroup.zpowers y⁆, K⁆ = ⊥ := by
        rw [eq_bot_iff, Subgroup.commutator_le]
        intro z hz' k hk
        have hzN : (⟨z, hzK hz'⟩ : ↥K) ∈ N₁ := hz hz'
        have hcz := Subgroup.mem_center_iff.mp (hcen hzN) ⟨k, hk⟩
        have hcz' : k * z = z * k := congrArg Subtype.val hcz
        rw [commutatorElement_def, ← hcz', Subgroup.mem_bot]
        group
      have h2 : ⁅⁅Subgroup.zpowers y, K⁆, K⁆ = ⊥ := by
        rw [Subgroup.commutator_comm (Subgroup.zpowers y) K]
        exact h1
      have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
      rwa [Subgroup.isPerfect_iff.1 hKperf] at h3
  have hKcent : K ≤ Subgroup.centralizer (Subgroup.zpowers y : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hKy
  have hy1 : y ≠ 1 := fun h1 => hyC (h1 ▸ Subgroup.one_mem _)
  have hyp : y ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) y hyE
  have hyord : orderOf y = p := orderOf_eq_prime hyp hy1
  have hCE : autFixedInG E t ≤ E := Subgroup.map_subtype_le _
  have hcommE : ∀ x ∈ E, ∀ z ∈ E, x * z = z * x := fun x hx z hz =>
    congrArg Subtype.val (hE.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
  have hcard' := card_sup_zpowers hp hyord (fun x hx => hcommE x (hCE hx) y hyE) hyC
  have hEsup : autFixedInG E t ⊔ Subgroup.zpowers y = E := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hCE (Subgroup.zpowers_le.2 hyE)) ?_
    rw [hcard, hcard', hcardC]
    exact (by ring : p ^ 4 = p ^ 3 * p).le
  have hKE : ∀ k ∈ K, ∀ x ∈ E, x * k = k * x := by
    intro k hk x hx
    have hCc : autFixedInG E t ≤ Subgroup.centralizer ({k} : Set G) := fun u hu =>
      Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 (hCK hu) k hk).symm
    have hyc : Subgroup.zpowers y ≤ Subgroup.centralizer ({k} : Set G) :=
      Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 (hKcent hk) y (Subgroup.mem_zpowers y)))
    have hEc : E ≤ Subgroup.centralizer ({k} : Set G) := hEsup ▸ sup_le hCc hyc
    exact Subgroup.mem_centralizer_singleton_iff.1 (hEc hx)
  obtain ⟨k, hk, hkK, hkt⟩ := hlift
  apply ht1
  rw [← hkt]
  refine MulEquiv.ext fun a => Subtype.ext ?_
  simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply]
  have hak := hKE k hkK a a.2
  rw [← hak, mul_assoc, mul_inv_cancel, mul_one]

end CFSG.RankThree.PartOne.K133
