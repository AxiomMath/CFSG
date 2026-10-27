module

public import CFSG.RankThree.PartTwo.Sec11.Item112
import CFSG.RankThree.PartTwo.KFacts.K71L28Cent

public section

namespace CFSG.RankThree.PartTwo.Sec9

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement


section General

variable {G : Type} [Group G] [Finite G]

theorem commutator_le_thetaQuotCentralizer_of_fixedCore {A : Subgroup G} {c : G}
    {L : Subgroup G} {a : G} {R : Subgroup G} (h : Hyp91 G A c L a R)
    (hNL : Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hK : ∀ e ∈ A, e ∉ Subgroup.zpowers c → ∀ (he : e ∈ Subgroup.normalizer (L : Set G))
      (N : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L))),
      (∀ ν ∈ N, ν * Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨e, he⟩) =
        Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨e, he⟩) * ν) →
      ¬ 3 ∣ Nat.card N →
      (∀ ℓ : L ⧸ aschbacherSolvableCore 3 L,
        Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨e, he⟩) ℓ = ℓ →
          ∀ ν ∈ N, MulAut.conj ℓ * ν * (MulAut.conj ℓ)⁻¹ ∈ N) →
      N = ⊥)
    {A' : Subgroup G} (hA'A : A' ≤ A) (hcard : Nat.card A = 3 * Nat.card A') (hcA' : c ∈ A') :
    ⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (A' : Set G)), A⁆ ≤
      Sec4.thetaQuotCentralizer L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hA3 : IsPGroup 3 A := fun u => ⟨1, Subtype.ext (by simpa using hexp u u.2)⟩
  have hcA := h.mem_A
  have hco : orderOf c = 3 := orderOf_eq_prime (hexp c hcA) h.ne_one
  have hCN : ∀ z : G, z * c = c * z → z ∈ Subgroup.normalizer (L : Set G) := fun z hz =>
    hNL (Sec10.mem_normalizer_zpowers_of_conj_mem (by
      rw [hz, mul_inv_cancel_right]
      exact Subgroup.mem_zpowers c))
  have hA'9 : Nat.card A' = 9 := by
    have h27 := h.card_eq
    omega
  obtain ⟨e, heA', hec⟩ : ∃ e ∈ A', e ∉ Subgroup.zpowers c := by
    by_contra hcon
    push Not at hcon
    have hle : A' ≤ Subgroup.zpowers c := hcon
    have := Subgroup.card_le_of_le hle
    rw [hA'9, Nat.card_zpowers, hco] at this
    norm_num at this
  have heA := hA'A heA'
  have hA'eq : Subgroup.closure ({c, e} : Set G) = A' := by
    have hle : Subgroup.closure ({c, e} : Set G) ≤ A' := by
      rw [Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy <;> rw [hy]
      · exact hcA'
      · exact heA'
    have h1 : Subgroup.zpowers c ≤ Subgroup.closure ({c, e} : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    have h9 := three_mul_card_le_of_le_of_ne hA3 (hle.trans hA'A) h1 (fun hEq => hec (by
      rw [hEq]
      exact Subgroup.subset_closure (by simp)))
    rw [Nat.card_zpowers, hco] at h9
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hA'9]; omega)
  set C := Subgroup.centralizer (A' : Set G) with hC
  set X := inSubgroup (aschbacherSolvableCore 3) C
  have hcen : ∀ z : G, z * c = c * z → z * e = e * z → z ∈ C := by
    intro z hzc hze
    rw [hC, ← hA'eq, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hzc.symm
    · exact hze.symm
  have hXC : X ≤ C := Subgroup.map_subtype_le _
  have hCc : C ≤ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.centralizer_le (by simpa using hcA')
  have hCe : C ≤ Subgroup.centralizer ({e} : Set G) :=
    Subgroup.centralizer_le (by simpa using heA')
  have hXN : X ≤ Subgroup.normalizer (L : Set G) := fun x hx =>
    hCN x (Subgroup.mem_centralizer_singleton_iff.mp (hCc (hXC hx)))
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := by
    intro y hy
    apply Sec6.normalizer_le_normalizer_theta C
    apply Subgroup.le_normalizer
    rw [hC, Subgroup.mem_centralizer_iff]
    intro z hz
    exact hcomm z (hA'A hz) y hy
  set ρ := (Sec4.thetaQuotMulAut L).comp (Sec4.compAction L)
  have heN : e ∈ Subgroup.normalizer (L : Set G) := hCN e (hcomm e heA c hcA)
  set N : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)) :=
    (X.subgroupOf (Subgroup.normalizer (L : Set G))).map ρ
  have hNbot : N = ⊥ := by
    refine hK e heA hec heN N ?_ ?_ ?_
    · rintro _ ⟨⟨x, hxN⟩, hx, rfl⟩
      have hxX : x ∈ X := Subgroup.mem_subgroupOf.mp hx
      have hxe : x * e = e * x := Subgroup.mem_centralizer_singleton_iff.mp (hCe (hXC hxX))
      have h1 : (⟨x, hxN⟩ : Subgroup.normalizer (L : Set G)) * ⟨e, heN⟩ =
          ⟨e, heN⟩ * ⟨x, hxN⟩ := Subtype.ext hxe
      have h2 := congrArg ρ h1
      rw [map_mul, map_mul] at h2
      exact h2
    · intro h3
      have h1 : Nat.card N ∣ Nat.card X := by
        refine (Subgroup.card_map_dvd _ ρ).trans ?_
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXN).toEquiv]
      exact Sec11.not_three_dvd_card_inSubgroup_theta C (h3.trans h1)
    · intro ℓ hℓ ν hν
      obtain ⟨⟨x, hxN⟩, hx, rfl⟩ := hν
      induction ℓ using QuotientGroup.induction_on with
      | H y =>
        obtain ⟨z, hz, hze⟩ := Sec11.exists_lift_of_fixed heN (hexp e heA) y hℓ
        have hzC : (z : G) ∈ C := by
          refine hcen z ?_ hze.symm
          exact (Subgroup.mem_centralizer_singleton_iff.mp
            (Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt z.2))
        have hzX : (z : G) ∈ Subgroup.normalizer (X : Set G) :=
          Sec6.normalizer_le_normalizer_theta C (Subgroup.le_normalizer hzC)
        have hzxN : (z : G) * x * (z : G)⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.le_normalizer z.2) hxN)
            (Subgroup.inv_mem _ (Subgroup.le_normalizer z.2))
        refine ⟨⟨(z : G) * x * (z : G)⁻¹, hzxN⟩, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.mp hzX x).mp (Subgroup.mem_subgroupOf.mp hx)
        · rw [← hz, ← Sec11.thetaQuotMulAut_compAction_of_mem L z.2]
          have e1 : (⟨(z : G) * x * (z : G)⁻¹, hzxN⟩ : Subgroup.normalizer (L : Set G)) =
              ⟨z, Subgroup.le_normalizer z.2⟩ * ⟨x, hxN⟩ * (⟨z, Subgroup.le_normalizer z.2⟩)⁻¹ :=
            rfl
          rw [e1, map_mul, map_mul, map_inv]
          rfl
  have hXCL : X ≤ Sec4.thetaQuotCentralizer L := by
    intro x hx
    have h1 : ρ ⟨x, hXN hx⟩ ∈ N := ⟨⟨x, hXN hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [hNbot, Subgroup.mem_bot] at h1
    exact ⟨⟨x, hXN hx⟩, h1, rfl⟩
  refine le_trans ?_ hXCL
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  have h1 : y * x⁻¹ * y⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hAX hy) x⁻¹).mp (X.inv_mem hx)
  rw [show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
  exact X.mul_mem hx h1

theorem normalizer_le_normalizer_L_of_psl28 (h45 : Sec4.Item4_5) {A : Subgroup G} {c : G}
    {L : Subgroup G} {a : G} {R : Subgroup G} (h : Hyp91 G A c L a R)
    (hL : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 3))) :
    Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp h.mem_partTwoF.1 h.mem_A
      h.ne_one L h.mem_thetaComponentsAt
  obtain ⟨e, σ, x, b, hbA, -, hx3, hx1, -⟩ := KFacts.exists_l28_model_of_hyp91 h hL hAL
  have h3L : 3 ∣ Nat.card L := by
    have h1 : 3 ∣ Nat.card (L ⧸ aschbacherSolvableCore 3 L) := by
      rw [Nat.card_congr e.toEquiv]
      exact (dvd_of_eq (orderOf_eq_prime hx3 hx1).symm).trans (orderOf_dvd_natCard x)
    exact h1.trans (Subgroup.card_quotient_dvd_card _)
  intro n hn
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  set Ln := L.map (MulAut.conj n).toMonoidHom with hLn
  have hcn : Subgroup.centralizer ({(MulAut.conj n) c} : Set G) =
      Subgroup.centralizer ({c} : Set G) := by
    have hz : Subgroup.zpowers ((MulAut.conj n) c) = Subgroup.zpowers c := by
      have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
      rw [MonoidHom.map_zpowers] at h1
      exact h1
    rw [GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers,
      GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers, hz]
  have hLnc : Ln ∈ thetaComponentsAt 3 c := by
    have h1 := map_mem_thetaComponentsAt (MulAut.conj n) h.mem_thetaComponentsAt
    rw [thetaComponentsAt_eq_thetaComponentsIn, hcn] at h1
    exact h1
  have hZ : Subgroup.center (Ln ⧸ aschbacherSolvableCore 3 Ln) = ⊥ :=
    KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot
      ((Sec13.thetaQuotEquiv (MulAut.conj n) L).symm.trans e)
      (GorensteinWalter.psl2_center_eq_bot _)
  have h3 : 3 ∣ Nat.card Ln := by
    rw [hLn, Subgroup.card_map_of_injective (MulAut.conj n).injective]
    exact h3L
  exact Sec11.not_three_dvd_of_mem_thetaComponentsAt_ne h45 h hLnc hne hZ h3

end General

theorem notLTwoEight_of (h45 : Sec4.Item4_5) : NotLTwoEight := by
  intro G _ _ A c L a R h hL
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp h.mem_partTwoF.1 h.mem_A
      h.ne_one L h.mem_thetaComponentsAt
  rcases h.invTwo_or_commutator with (hi | ⟨A', hA'A, hcard, hcA', hnot⟩) | ⟨hL8, -⟩
  · exact KFacts.not_invTwoBarNontrivial_of_hyp91_psl28 h hL hAL hi
  · exact hnot (commutator_le_thetaQuotCentralizer_of_fixedCore h
      (normalizer_le_normalizer_L_of_psl28 h45 h hL)
      (fun e heA hec he N => KFacts.eq_bot_of_hyp91_psl28 h hL hAL heA hec he N)
      hA'A hcard hcA')
  · exact hL8 hL

end CFSG.RankThree.PartTwo.Sec9
