module

public import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores
public import CFSG.RankThree.GroupTheory.SteinbergCEQuotientKernelMonotonicity
public import CFSG.RankThree.LocalRank.ThetaPlaneAlpha
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBY

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.LocalRank
open scoped Pointwise

variable {H : Type*} [Group H]

theorem normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore (p : ℕ) (L : Subgroup H) :
    Subgroup.normalizer (L : Set H) ≤
      Subgroup.normalizer (inSubgroup (aschbacherSolvableCore p) L : Set H) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact conj_mem_inSubgroup_aschbacherSolvableCore hg
  · intro hx
    have := conj_mem_inSubgroup_aschbacherSolvableCore (inv_mem hg) hx
    simpa [mul_assoc] using this

theorem mem_normalizer_commutator {U V : Subgroup H} {g : H}
    (hU : g ∈ Subgroup.normalizer (U : Set H)) (hV : g ∈ Subgroup.normalizer (V : Set H)) :
    g ∈ Subgroup.normalizer ((⁅U, V⁆ : Subgroup H) : Set H) :=
  mem_normalizer_of_map_conj_eq (by
    rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer hU,
      map_conj_eq_of_mem_normalizer hV])

theorem thetaT_le_centralizer (p : ℕ) (B : Subgroup H) :
    thetaT p B ≤ Subgroup.centralizer (B : Set H) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  by_cases hb1 : b = 1
  · rw [hb1, one_mul, mul_one]
  · have hxθ := Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hx b) hb) hb1
    exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.map_subtype_le _ hxθ)).symm

theorem le_of_isPGroup_two_of_odd_relIndex [Finite H] {X W N : Subgroup H} (hX : IsPGroup 2 X)
    (hXW : X ≤ W) (hNW : N ≤ W) (hWN : W ≤ Subgroup.normalizer (N : Set H))
    (hodd : ¬ 2 ∣ N.relIndex W) : X ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (N.subgroupOf W).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNW).mpr hWN
  set f := QuotientGroup.mk' (N.subgroupOf W)
  have hX' : IsPGroup 2 (X.subgroupOf W) := hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXW).symm
  obtain ⟨m, hm⟩ := (hX'.map f).exists_card_eq
  have hdvd : Nat.card ((X.subgroupOf W).map f) ∣ N.relIndex W :=
    Subgroup.card_subgroup_dvd_card _
  rw [hm] at hdvd
  have hm0 : m = 0 := by
    rcases m with _ | m
    · rfl
    · exact absurd ((dvd_pow_self 2 (Nat.succ_ne_zero m)).trans hdvd) hodd
  rw [hm0, pow_zero] at hm
  have hbot : (X.subgroupOf W).map f = ⊥ := Subgroup.eq_bot_of_card_eq _ hm
  intro x hx
  have hmem : f ⟨x, hXW hx⟩ ∈ (X.subgroupOf W).map f :=
    Subgroup.mem_map_of_mem f (show (⟨x, hXW hx⟩ : W) ∈ X.subgroupOf W from hx)
  rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
  exact hmem

theorem section_nine_residual_to_intersection [Finite H] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (B : Subgroup H) :
    (∀ t ∈ B, t ≠ 1 →
      ((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set H)), B⁆ ⊔
          thetaT p B : Subgroup H) : Set H) =
        ((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set H)), B⁆ :
          Subgroup H) : Set H) * (thetaT p B : Set H)) ∧
      ((∃ t ∈ B, t ≠ 1 ∧ CFSG.Quasithin.twoPrimeResidual
          (⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set H)), B⁆ ⊔
            thetaT p B) ≤ aschbacherSolvableCore p H) →
        twoCoreX B ≤ aschbacherSolvableCore p H) := by
  have hO2θ : ∀ a : H, inSubgroup (pCore 2) (Subgroup.centralizer ({a} : Set H)) ≤
      inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({a} : Set H)) := fun _ =>
    Subgroup.map_mono ((solvable_prime_complement_core_characterization hp).2.2.2.2.2.2 2
      Nat.prime_two (Ne.symm hp2))
  have hXI : twoCoreX B ≤ thetaT p B := by
    intro x hx
    simp only [thetaT, Subgroup.mem_iInf]
    intro a ha ha1
    exact hO2θ a ((mem_twoCoreX_iff.mp hx) a ha ha1)
  refine ⟨fun t ht ht1 => ?_, fun ⟨t, ht, ht1, hres⟩ => ?_⟩
  · apply Subgroup.coe_mul_of_right_le_normalizer_left
    intro g hg
    have hgθ := Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hg t) ht) ht1
    have hgC : g ∈ Subgroup.centralizer ({t} : Set H) := Subgroup.map_subtype_le _ hgθ
    exact mem_normalizer_commutator
      (normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore p _ (Subgroup.le_normalizer hgC))
      (Subgroup.centralizer_le_normalizer _ (thetaT_le_centralizer p B hg))
  · have hXW := hXI.trans (le_sup_right (a :=
      ⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set H)), B⁆))
    have hX2 : IsPGroup 2 (twoCoreX B) :=
      (isPGroup_inSubgroup_pCore 2 _).to_le fun x hx => (mem_twoCoreX_iff.mp hx) t ht ht1
    refine le_trans ?_ hres
    unfold CFSG.Quasithin.twoPrimeResidual
    exact le_iInf₂ fun N hN => le_of_isPGroup_two_of_odd_relIndex hX2 hXW hN.1 hN.2.1 hN.2.2

end CFSG.RankThree.GroupTheory.SteinbergBY
