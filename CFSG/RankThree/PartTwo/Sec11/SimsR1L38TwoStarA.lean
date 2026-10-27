module

public import CFSG.RankThree.PartTwo.Sec11.TwoStarProof
public import CFSG.RankThree.PartTwo.Sec11.Item116R1Defs
public import CFSG.RankThree.PartTwo.Sec11.SimsR1Defs

public section

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1.L38TwoStar

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.GroupTheory
open scoped commutatorElement

theorem mem_centralizer_of_pow_three_of_isCyclic {M : Type*} [Group M] {Q : Subgroup M}
    [Finite Q] (hcyc : IsCyclic Q) (hQ : IsPGroup 2 Q) {g : M}
    (hg : g ∈ Subgroup.normalizer (Q : Set M)) (hg3 : g ^ 3 = 1) :
    g ∈ Subgroup.centralizer (Q : Set M) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hcyc
  set φ := Q.normalizerMonoidHom ⟨g, hg⟩ with hφ
  have hφ3 : φ ^ 3 = 1 := by
    rw [hφ, ← map_pow]
    have : (⟨g, hg⟩ : Subgroup.normalizer (Q : Set M)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hg3)
    rw [this, map_one]
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hcard : ∃ j : ℕ, Nat.card (MulAut Q) = 2 ^ j := by
    rw [IsCyclic.card_mulAut, hk]
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exact ⟨0, by rw [h0]; simp⟩
    · exact ⟨k - 1, by rw [Nat.totient_prime_pow Nat.prime_two h0]; simp⟩
  obtain ⟨j, hj⟩ := hcard
  have h1 : orderOf φ ∣ 3 := orderOf_dvd_of_pow_eq_one hφ3
  have h2 : orderOf φ ∣ 2 ^ j := hj ▸ orderOf_dvd_natCard φ
  have h3 : orderOf φ = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left j (by norm_num)) h2 h1
  have hker : (⟨g, hg⟩ : Subgroup.normalizer (Q : Set M)) ∈ Q.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker]
    exact orderOf_eq_one_iff.mp h3
  rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hker
  exact hker

section Theta

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem mem_thetaQuotCentralizer_of_autHom_eq_one {q : G}
    (hqN : q ∈ Subgroup.normalizer (L : Set G)) (hq : TwoStarProof.autHom L ⟨q, hqN⟩ = 1) :
    q ∈ Sec4.thetaQuotCentralizer L :=
  ⟨⟨q, hqN⟩, hq, rfl⟩

theorem autHom_eq_one_of_mem_thetaQuotCentralizer {q : G}
    (hqN : q ∈ Subgroup.normalizer (L : Set G)) (hq : q ∈ Sec4.thetaQuotCentralizer L) :
    TwoStarProof.autHom L ⟨q, hqN⟩ = 1 := by
  obtain ⟨y, hy, hyq⟩ := hq
  have : (⟨q, hqN⟩ : Subgroup.normalizer (L : Set G)) = y := Subtype.ext hyq.symm
  rw [this]
  exact hy

theorem mem_normalizer_thetaQuotCentralizer {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G)) :
    x ∈ Subgroup.normalizer ((Sec4.thetaQuotCentralizer L : Subgroup G) : Set G) := by
  let f : Subgroup.normalizer (L : Set G) →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
    (Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom
  have hnorm : f.ker.Normal := MonoidHom.normal_ker f
  have hconj : ∀ n ∈ Sec4.thetaQuotCentralizer L, x * n * x⁻¹ ∈ Sec4.thetaQuotCentralizer L := by
    intro n hn
    obtain ⟨n', hn', hn'e⟩ := Subgroup.mem_map.mp hn
    have h1 : (⟨x, hx⟩ * n' * ⟨x, hx⟩⁻¹ : Subgroup.normalizer (L : Set G)) ∈ f.ker :=
      hnorm.conj_mem n' hn' _
    exact ⟨_, h1, by rw [← hn'e]; rfl⟩
  exact Subgroup.mem_normalizer_fintype hconj

end Theta

section Certified


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d : G}

theorem comm_of_mem_A (h : ResidueConfig G A c L a R Y d) : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u :=
  fun u hu v hv => congrArg Subtype.val (h.mem_partTwoF.1.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)

theorem mem_theta_of_mem_pCore_inf (hAut : SimsR1L38AutFacts) (h45 : Sec4.Item4_5)
    (h : ResidueConfig G A c L a R Y d) (hT : A ∉ partTwoT G) (hL : IsL3Eight L) {y : G}
    (hyA : y ∈ A) (hyB : y ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d) {r : G}
    (hr : r ∈ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set G) ⊓
      Subgroup.centralizer ({y} : Set G))) (hrL : r ∈ L) :
    r ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  have hAe := h.mem_partTwoF.1
  have hAc := comm_of_mem_A h
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set N := Subgroup.normalizer (L : Set G) with hN
  set P := inSubgroup (CFSG.pCore 2) (C ⊓ Subgroup.centralizer ({y} : Set G)) with hP
  have hCL : C ≤ N := TwoStarProof.centralizer_le_normalizer_of_config h45 h hT
  have hLC : L ≤ C := TwoStarProof.le_centralizer_of_config h
  have hAC : A ≤ C := fun u hu => Subgroup.mem_centralizer_singleton_iff.mpr (hAc u hu c h.mem_A)
  have hyN : y ∈ N := hCL (hAC hyA)
  have hy3 : y ^ 3 = 1 := hAe.2 y hyA
  have hP2 : IsPGroup 2 P := SteinbergBY.isPGroup_inSubgroup_pCore 2 _
  have hPC : P ≤ C ⊓ Subgroup.centralizer ({y} : Set G) := SteinbergBY.inSubgroup_pCore_le 2 _
  set σ := TwoStarProof.autHom L ⟨y, hyN⟩ with hσ
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσ, ← map_pow]
    have : (⟨y, hyN⟩ : N) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    rw [this, map_one]
  have hnot : σ ∉ (MulAut.conj : (L ⧸ aschbacherSolvableCore 3 L) →*
      MulAut (L ⧸ aschbacherSolvableCore 3 L)).range :=
    TwoStarProof.autHom_not_inner_of_not_mem h45 h hT hyA hyB hyN
  have hne : σ ≠ 1 := fun h1 => hnot (by rw [h1]; exact Subgroup.one_mem _)
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hne
  have hbot := (hAut (L ⧸ aschbacherSolvableCore 3 L) hL).2.1 σ hord hnot
  set q := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hq
  set R' : Subgroup (L ⧸ aschbacherSolvableCore 3 L) := (P.subgroupOf L).map q with hR'
  have hR2 : IsPGroup 2 R' := (hP2.comap_subtype (K := L)).map q
  have hRF : R' ≤ Sec11.fixedSub σ := by
    rintro _ ⟨l, hl, rfl⟩
    have hly : (l : G) ∈ Subgroup.centralizer ({y} : Set G) :=
      (hPC (Subgroup.mem_subgroupOf.mp hl)).2
    have hcomm : (l : G) * y = y * l := Subgroup.mem_centralizer_singleton_iff.mp hly
    have h1 : (Sec4.compAction L ⟨y, hyN⟩ l : L) = l := by
      apply Subtype.ext
      change y * (l : G) * y⁻¹ = l
      rw [← hcomm]
      group
    show Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨y, hyN⟩)
      (l : L ⧸ aschbacherSolvableCore 3 L) = (l : L ⧸ aschbacherSolvableCore 3 L)
    rw [Sec4.thetaQuotMulAut_mk, h1]
  have hFN : Sec11.fixedSub σ ≤
      Subgroup.normalizer (R' : Set (L ⧸ aschbacherSolvableCore 3 L)) := by
    intro k hk
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨l, hl, rfl⟩ := hn
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective k
    obtain ⟨z, hzw, hzy⟩ := exists_lift_of_fixed hyN hy3 w hk
    have hzC : (z : G) ∈ C ⊓ Subgroup.centralizer ({y} : Set G) :=
      ⟨hLC z.2, Subgroup.mem_centralizer_singleton_iff.mpr hzy.symm⟩
    have hlP : (l : G) ∈ P := Subgroup.mem_subgroupOf.mp hl
    have hzlP : (z : G) * l * (z : G)⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (SteinbergBY.le_normalizer_inSubgroup_pCore 2 _ hzC)
        l).mp hlP
    refine ⟨z * l * z⁻¹, Subgroup.mem_subgroupOf.mpr (by simpa using hzlP), ?_⟩
    have hqz : q z = (w : L ⧸ aschbacherSolvableCore 3 L) := hzw
    rw [map_mul, map_mul, map_inv, hqz]
  have hle : R' ≤ inSubgroup (CFSG.pCore 2) (Sec11.fixedSub σ) :=
    SteinbergBY.le_inSubgroup_pCore hR2 hRF hFN
  have hbot' : inSubgroup (CFSG.pCore 2) (Sec11.fixedSub σ) = ⊥ := by
    rw [inSubgroup, hbot]
    exact Subgroup.map_bot _
  have hmem : q ⟨r, hrL⟩ ∈ R' := ⟨⟨r, hrL⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
  have h1 := hle hmem
  rw [hbot', Subgroup.mem_bot] at h1
  have h2 : (⟨r, hrL⟩ : L) ∈ aschbacherSolvableCore 3 L :=
    (QuotientGroup.eq_one_iff (N := aschbacherSolvableCore 3 L) ⟨r, hrL⟩).mp h1
  exact ⟨_, h2, rfl⟩

theorem commutator_le_theta_of_commutator_mem (h45 : Sec4.Item4_5)
    (h : ResidueConfig G A c L a R Y d) (hT : A ∉ partTwoT G) {y : G} (hyA : y ∈ A)
    (hyB : y ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d)
    (hd : ∀ q ∈ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set G) ⊓
        Subgroup.centralizer ({y} : Set G)),
      q * d * q⁻¹ * d⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L) :
    ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set G) ⊓
        Subgroup.centralizer ({y} : Set G)), A⁆ ≤
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)) := by
  have hAe := h.mem_partTwoF.1
  have : IsElementaryAbelian 3 A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 A).2 hAe
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set N := Subgroup.normalizer (L : Set G) with hN
  set P := inSubgroup (CFSG.pCore 2) (C ⊓ Subgroup.centralizer ({y} : Set G)) with hP
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθL
  have hCL := TwoStarProof.centralizer_le_normalizer_of_config h45 h hT
  have hAc := comm_of_mem_A h
  have hAC : A ≤ C := fun u hu => Subgroup.mem_centralizer_singleton_iff.mpr (hAc u hu c h.mem_A)
  have hPC : P ≤ C ⊓ Subgroup.centralizer ({y} : Set G) := SteinbergBY.inSubgroup_pCore_le 2 _
  have hyN : y ∈ N := hCL (hAC hyA)
  have hyc : y ∉ Subgroup.zpowers c := fun hyc => hyB (Subgroup.mem_sup_left hyc)
  have hdE : d ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers y := by
    intro hd'
    have hplane := TwoStarProof.zpowers_sup_eq_of_mem h.card_eq h.mem_A h.ne_one hyA hyc h.d_mem
      h.not_mem_zpowers hd'
    exact hyB (hplane ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  have hA' := TwoStarProof.zpowers_sup_sup_eq h.card_eq h.mem_A h.ne_one hyA hyc h.d_mem hdE
  have hNθ : N ≤ Subgroup.normalizer (θL : Set G) := Sec6.normalizer_le_normalizer_theta L
  rw [Subgroup.commutator_le]
  intro q hq x hx
  let T : Subgroup G :=
    { carrier := {x | x ∈ N ∧ q * x * q⁻¹ * x⁻¹ ∈ θL}
      mul_mem' := by
        rintro x₁ x₂ ⟨h₁N, h₁⟩ ⟨h₂N, h₂⟩
        refine ⟨N.mul_mem h₁N h₂N, ?_⟩
        have e₁ : q * (x₁ * x₂) * q⁻¹ * (x₁ * x₂)⁻¹ =
            (q * x₁ * q⁻¹ * x₁⁻¹) * (x₁ * (q * x₂ * q⁻¹ * x₂⁻¹) * x₁⁻¹) := by group
        rw [e₁]
        exact θL.mul_mem h₁ ((Subgroup.mem_normalizer_iff.mp (hNθ h₁N) _).mp h₂)
      one_mem' := ⟨N.one_mem, by simp⟩
      inv_mem' := by
        rintro x₁ ⟨h₁N, h₁⟩
        refine ⟨N.inv_mem h₁N, ?_⟩
        have e₁ : q * x₁⁻¹ * q⁻¹ * x₁⁻¹⁻¹ = x₁⁻¹ * (q * x₁ * q⁻¹ * x₁⁻¹)⁻¹ * x₁⁻¹⁻¹ := by group
        rw [e₁]
        exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hNθ h₁N)) _).mp
          (θL.inv_mem h₁) }
  have hqC : q ∈ C := (hPC hq).1
  have hqy : q * y = y * q := Subgroup.mem_centralizer_singleton_iff.mp (hPC hq).2
  have hcT : c ∈ T := by
    refine ⟨hCL (hAC h.mem_A), ?_⟩
    have hqc : q * c = c * q := Subgroup.mem_centralizer_singleton_iff.mp hqC
    rw [hqc, mul_inv_cancel_right, mul_inv_cancel]
    exact θL.one_mem
  have hyT : y ∈ T := by
    refine ⟨hyN, ?_⟩
    rw [hqy, mul_inv_cancel_right, mul_inv_cancel]
    exact θL.one_mem
  have hdT : d ∈ T := ⟨hCL (hAC h.d_mem), hd q hq⟩
  have hAT : A ≤ T := by
    rw [← hA']
    exact sup_le (sup_le (Subgroup.zpowers_le.mpr hcT) (Subgroup.zpowers_le.mpr hyT))
      (Subgroup.zpowers_le.mpr hdT)
  rw [commutatorElement_def]
  exact TwoStarProof.theta_L_le h45 h hT (hAT hx).2

theorem commutator_pCore_le_theta_of_outer (hAut : SimsR1L38AutFacts) (h45 : Sec4.Item4_5)
    (h : ResidueConfig G A c L a R Y d) (hT : A ∉ partTwoT G) (hL : IsL3Eight L) {y : G}
    (hyA : y ∈ A) (hyB : y ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d) :
    ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set G) ⊓
        Subgroup.centralizer ({y} : Set G)), A⁆ ≤
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)) := by
  refine commutator_le_theta_of_commutator_mem h45 h hT hyA hyB fun q hq => ?_
  have hAc := comm_of_mem_A h
  have hCL := TwoStarProof.centralizer_le_normalizer_of_config h45 h hT
  have hdL := TwoStarProof.d_mem_L h
  have hAC : ∀ x ∈ A, x ∈ Subgroup.centralizer ({c} : Set G) := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc u hu c h.mem_A)
  have hPC := SteinbergBY.inSubgroup_pCore_le 2
    (Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer ({y} : Set G)) hq
  have hdC : d ∈ Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) :=
    ⟨hAC d h.d_mem, Subgroup.mem_centralizer_singleton_iff.mpr (hAc d h.d_mem y hyA)⟩
  have hqN : q ∈ Subgroup.normalizer (L : Set G) := hCL hPC.1
  have hdq : d * q⁻¹ * d⁻¹ ∈ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set G) ⊓
      Subgroup.centralizer ({y} : Set G)) :=
    (Subgroup.mem_normalizer_iff.mp (SteinbergBY.le_normalizer_inSubgroup_pCore 2 _ hdC) q⁻¹).mp
      (Subgroup.inv_mem _ hq)
  refine mem_theta_of_mem_pCore_inf hAut h45 h hT hL hyA hyB ?_ ?_
  · have e : q * d * q⁻¹ * d⁻¹ = q * (d * q⁻¹ * d⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hq hdq
  · have h1 : q * d * q⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hqN d).mp hdL
    exact L.mul_mem h1 (L.inv_mem hdL)

end Certified

end CFSG.RankThree.PartTwo.Sec11.SimsR1.L38TwoStar
