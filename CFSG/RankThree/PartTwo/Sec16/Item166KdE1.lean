module

public import CFSG.RankThree.PartTwo.Sec16.Item166CtrLB
import CFSG.RankThree.PartTwo.Sec16.Item166KdSupp
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.GroupTheory.CoprimeSectionStability
import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.RankThree.GroupTheory.SteinbergCEMutualSupplementResidual
public import CFSG.RankThree.PartTwo.Sec16.Item166ThetaCompY

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kd166

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.PartTwo.Sec16 CFSG.GH74.GLS
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

private def centModE (Q K : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (Q : Set G) ∧ ∀ k ∈ K, ⁅g, k⁆ ∈ Q}
  one_mem' := ⟨one_mem _, fun k _ => by simp [commutatorElement_def]⟩
  mul_mem' := by
    rintro g h ⟨hgN, hg⟩ ⟨hhN, hh⟩
    refine ⟨mul_mem hgN hhN, fun k hk => ?_⟩
    rw [commutatorElement_mul_left_eq_conj_mul]
    exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp hgN _).mp (hh k hk)) (hg k hk)
  inv_mem' := by
    rintro g ⟨hgN, hg⟩
    refine ⟨inv_mem hgN, fun k hk => ?_⟩
    have hgi : g⁻¹ ∈ Subgroup.normalizer (Q : Set G) := inv_mem hgN
    have h1 : g⁻¹ * ⁅g, k⁆⁻¹ * g⁻¹⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp hgi _).mp (Q.inv_mem (hg k hk))
    have h2 : ⁅g⁻¹, k⁆ = g⁻¹ * ⁅g, k⁆⁻¹ * g⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h2]
    exact h1

private theorem commutator_mem_of_mem_normalizer {Q : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) (hx : x ∈ Q) : ⁅g, x⁆ ∈ Q := by
  have h1 : g * x * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have h2 : ⁅g, x⁆ = (g * x * g⁻¹) * x⁻¹ := by rw [commutatorElement_def]
  rw [h2]
  exact Q.mul_mem h1 (Q.inv_mem hx)

private theorem commutator_mem_of_mem_normalizer' {Q : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) (hx : x ∈ Q) : ⁅x, g⁆ ∈ Q := by
  have h1 : ⁅x, g⁆ = ⁅g, x⁆⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [h1]
  exact Q.inv_mem (commutator_mem_of_mem_normalizer hg hx)

private theorem mem_normalizer_inSubgroup_perfectResidual' {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer (inSubgroup perfectResidual K : Set G) :=
  CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (perfectResidual ↥K) hg

private theorem theta_lB_eq_pCore_two' (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d) :
    aschbacherSolvableCore 3 ↥(lB A (Subgroup.closure {c, d})) =
      CFSG.pCore 2 ↥(lB A (Subgroup.closure {c, d})) := by
  set J := lB A (Subgroup.closure {c, d}) with hJdef
  haveI : Group.IsPerfect ↥J := by
    rw [hJdef, Ctr166.lB_closure_eq_residual h hJ hdA hd1 hdc]
    exact Item148HJ.residual_isPerfect L d
  have htc : Sec4.IsTripleCover (↥J ⧸ CFSG.pCore 2 ↥J) (alternatingGroup (Fin 6)) :=
    Ctr166.isTripleCover_lB h.toSec14Std (Ctr166.isHyperplane_closure_cd h hJ hdA hd1 hdc)
      (Ctr166.isLBConfig_closure_cd_of_threeCentral h hJ hdc)
  obtain ⟨-, -, hθ3, -, -, -, hθO⟩ :=
    solvable_prime_complement_core_characterization (H := ↥J) Nat.prime_three
  set Q := CFSG.pCore 2 ↥J
  haveI : Q.Normal := CFSG.pCore_normal
  have hO2θ : Q ≤ aschbacherSolvableCore 3 ↥J := hθO 2 Nat.prime_two (by norm_num)
  have hθn : (aschbacherSolvableCore 3 ↥J).Normal := aschbacherSolvableCore_normal 3 ↥J
  let f := QuotientGroup.mk' Q
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective Q
  haveI hZn : ((aschbacherSolvableCore 3 ↥J).map f).Normal := hθn.map f hf
  have hZ3 : ¬ 3 ∣ Nat.card ((aschbacherSolvableCore 3 ↥J).map f) := fun h3 =>
    hθ3 (h3.trans (Subgroup.card_map_dvd _ f))
  have hZbot : (aschbacherSolvableCore 3 ↥J).map f = ⊥ :=
    ThetaCompY.eq_bot_of_normal_of_not_three_dvd (T := ↥J ⧸ Q)
      (N := (aschbacherSolvableCore 3 ↥J).map f) htc hZ3
  have hθle : aschbacherSolvableCore 3 ↥J ≤ Q := by
    rw [← QuotientGroup.ker_mk' Q]
    exact (Subgroup.map_eq_bot_iff (f := f) _).mp hZbot
  exact le_antisymm hθle hO2θ

theorem le_normalizer_of_mem_centralizer_theta (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d)
    {K : Subgroup G} (hKeq : K = lB A (Subgroup.closure {c, d}) ⊔
      inSubgroup (aschbacherSolvableCore 3) K) :
    inSubgroup (aschbacherSolvableCore 3) K ⊓ Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
  classical
  have hD13 : Sec13Data G A c L := h.toSec13Data
  have hL : L ∈ thetaComponentsAt 3 c := hD13.mem_thetaComponentsAt
  set J := lB A (Subgroup.closure {c, d}) with hJdef
  set θK := inSubgroup (aschbacherSolvableCore 3) K
  set T := θK ⊓ Subgroup.centralizer ({c} : Set G) with hTdef
  set Θc := inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G))
  have hJK : J ≤ K := by
    rw [hKeq]
    exact le_sup_left
  have hJL : J ≤ L := by
    rw [hJdef, Ctr166.lB_closure_eq_residual h hJ hdA hd1 hdc]
    exact Item148HJ.residual_le L d
  have hJc : J ≤ Subgroup.centralizer ({c} : Set G) := hJL.trans hD13.le_centralizer
  have hJperf : Group.IsPerfect ↥J := by
    rw [hJdef, Ctr166.lB_closure_eq_residual h hJ hdA hd1 hdc]
    exact Item148HJ.residual_isPerfect L d
  have hJne : J ≠ ⊥ := by
    intro hbot
    have hdJ : d ∈ J := Ctr166.mem_lB_closure h hJ hdA hd1 hdc
    exact hd1 (Subgroup.mem_bot.mp (hbot ▸ hdJ))
  have hJT : J ≤ Subgroup.normalizer (T : Set G) := by
    intro l hl
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Sec6.le_normalizer_theta K (hJK hl), Subgroup.le_normalizer (hJc hl)⟩
  have hTs : Group.IsSolvable ↥T := by
    haveI := (Sec6.theta_solvable_and_not_dvd K).1
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective _)
  have hΘs : Group.IsSolvable ↥Θc :=
    (Sec6.theta_solvable_and_not_dvd (Subgroup.centralizer ({c} : Set G))).1
  have hTΘ : T ≤ Subgroup.normalizer (Θc : Set G) :=
    inf_le_right.trans (Sec6.le_normalizer_theta _)
  have hVs : Group.IsSolvable ↥(Θc ⊔ T) :=
    CFSG.RankThree.GroupTheory.isSolvable_sup_of_le_normalizer hTΘ hΘs hTs
  have hθL : inSubgroup (aschbacherSolvableCore 3) L ≤ Θc := Sec21.theta_le_theta_centralizer hL
  intro t ht
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  set L' := L.map (MulAut.conj t).toMonoidHom
  have hL' : L' ∈ thetaComponentsAt 3 c := Sec6.map_conj_mem_thetaComponentsAt ht.2 hL
  have hc : ⁅L, L'⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L :=
    (le_normalizer_and_commutator_le_of_ne hL hL' (Ne.symm hne)).2
  have hJV : J ≤ Θc ⊔ T := by
    have hJJ : ⁅J, J⁆ = J := Subgroup.commutator_eq_self
    rw [← hJJ, Subgroup.commutator_le]
    intro l₁ hl₁ l₂ hl₂
    have hs : ⁅l₂, t⁆ ∈ T := commutator_mem_of_mem_normalizer (hJT hl₂) ht
    have hu : t * l₂ * t⁻¹ ∈ L' := ⟨l₂, hJL hl₂, by simp [MulAut.conj_apply]⟩
    have hl₂e : l₂ = ⁅l₂, t⁆ * (t * l₂ * t⁻¹) := by
      rw [commutatorElement_def]
      group
    have hcomm : ⁅l₁, l₂⁆ = ⁅l₁, ⁅l₂, t⁆⁆ * (⁅l₂, t⁆ * ⁅l₁, t * l₂ * t⁻¹⁆ * ⁅l₂, t⁆⁻¹) := by
      conv_lhs => rw [hl₂e]
      simp only [commutatorElement_def]
      group
    rw [hcomm]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_right
      (commutator_mem_of_mem_normalizer (hJT hl₁) hs)) (Subgroup.mem_sup_left ?_)
    have hm : ⁅l₁, t * l₂ * t⁻¹⁆ ∈ Θc :=
      hθL (hc (Subgroup.commutator_mem_commutator (hJL hl₁) hu))
    exact (Subgroup.mem_normalizer_iff.mp (hTΘ hs) _).mp hm
  have hJs : Group.IsSolvable ↥J := by
    haveI := hVs
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hJV)
      (Subgroup.inclusion_injective _)
  haveI : Nontrivial ↥J := (Subgroup.nontrivial_iff_ne_bot J).mpr hJne
  exact Group.IsPerfect.not_isSolvable ↥J hJs

theorem commutator_lB_le_of_forall_commutator_mem (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d)
    {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 d)
    (hKeq : K = lB A (Subgroup.closure {c, d}) ⊔ inSubgroup (aschbacherSolvableCore 3) K)
    {M N : Subgroup G} (hMθ : M ≤ inSubgroup (aschbacherSolvableCore 3) K)
    (hModd : Odd (Nat.card ↥M)) (hNM : N ≤ M) (hMN : M ≤ Subgroup.normalizer (N : Set G))
    (hcM : c ∈ Subgroup.normalizer (M : Set G)) (hcN : c ∈ Subgroup.normalizer (N : Set G))
    (hJM : lB A (Subgroup.closure {c, d}) ≤ Subgroup.normalizer (M : Set G))
    (hJN : lB A (Subgroup.closure {c, d}) ≤ Subgroup.normalizer (N : Set G))
    (hct : ∀ m ∈ M, c * m * c⁻¹ * m⁻¹ ∈ N) :
    ⁅M, lB A (Subgroup.closure {c, d})⁆ ≤ N := by
  classical
  have hD13 : Sec13Data G A c L := h.toSec13Data
  set J := lB A (Subgroup.closure {c, d}) with hJdef
  set θK := inSubgroup (aschbacherSolvableCore 3) K
  have hJK : J ≤ K := by
    rw [hKeq]
    exact le_sup_left
  have hKd : K ≤ Subgroup.centralizer ({d} : Set G) :=
    Sec14.le_centralizer_of_mem_thetaComponentsAt hK
  have hTL := le_normalizer_of_mem_centralizer_theta h hJ hdA hd1 hdc hKeq
  have hJθ : J ⊓ θK = inSubgroup (aschbacherSolvableCore 3) J :=
    inf_theta_eq_of_eq_sup hJK hKeq
  have hθJ2 : IsPGroup 2 ↥(inSubgroup (aschbacherSolvableCore 3) J) := by
    unfold inSubgroup
    rw [theta_lB_eq_pCore_two' h hJ hdA hd1 hdc]
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥J)).map J.subtype
  have hxJ : ∀ x ∈ M, x ∈ Subgroup.centralizer ({c} : Set G) → ∀ l ∈ J, ⁅x, l⁆ = 1 := by
    intro x hxM hxc l hl
    have hxT : x ∈ θK ⊓ Subgroup.centralizer ({c} : Set G) := ⟨hMθ hxM, hxc⟩
    have hxJN : x ∈ Subgroup.normalizer (J : Set G) := by
      rw [hJdef, Ctr166.lB_closure_eq_residual h hJ hdA hd1 hdc]
      refine mem_normalizer_inSubgroup_perfectResidual'
        (Subgroup.inf_normalizer_le_normalizer_inf ⟨hTL hxT, ?_⟩)
      exact Subgroup.le_normalizer (hKd (Sec6.theta_le K (hMθ hxM)))
    have h1 : ⁅x, l⁆ ∈ J := commutator_mem_of_mem_normalizer hxJN hl
    have h2 : ⁅x, l⁆ ∈ M := commutator_mem_of_mem_normalizer' (hJM hl) hxM
    have h3 : ⁅x, l⁆ ∈ inSubgroup (aschbacherSolvableCore 3) J := by
      rw [← hJθ]
      exact ⟨h1, hMθ h2⟩
    obtain ⟨k, hk⟩ := (hθJ2.to_le le_rfl) ⟨_, h3⟩
    have hord2 : orderOf ⁅x, l⁆ ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      have := congrArg Subtype.val hk
      simpa using this
    have hordM : orderOf ⁅x, l⁆ ∣ Nat.card ↥M := by
      have := Subgroup.orderOf_dvd_natCard M h2
      simpa using this
    have hcop : Nat.Coprime (2 ^ k) (Nat.card ↥M) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hModd)
    have hone : orderOf ⁅x, l⁆ = 1 := by
      have hg := Nat.dvd_gcd hord2 hordM
      rw [Nat.Coprime.gcd_eq_one hcop] at hg
      exact Nat.dvd_one.mp hg
    exact orderOf_eq_one_iff.mp hone
  have hcA : c ∈ A := (Sec13.zpowers_mem_omegaA_iff.mp h.zpowers_mem_omegaA).1
  have hc3 : c ^ 3 = 1 := h.toSec14Std.isE27.1.2 c hcA
  have hDc : Subgroup.zpowers c ≤ centModE N M := by
    rw [Subgroup.zpowers_le]
    exact ⟨hcN, fun m hm => by rw [commutatorElement_def]; exact hct m hm⟩
  have hDM : Subgroup.zpowers c ≤ Subgroup.normalizer (M : Set G) :=
    Subgroup.zpowers_le.mpr hcM
  have hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers c)) (Nat.card ↥M) := by
    rw [Nat.card_zpowers]
    have hord : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
    have h3M : ¬ 3 ∣ Nat.card ↥M := fun h3 =>
      (Sec6.theta_solvable_and_not_dvd K).2 (h3.trans (Subgroup.card_dvd_of_le hMθ))
    exact Nat.Coprime.coprime_dvd_left hord
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3M)
  have hMs : Group.IsSolvable ↥M := by
    haveI := (Sec6.theta_solvable_and_not_dvd K).1
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hMθ)
      (Subgroup.inclusion_injective _)
  rw [Subgroup.commutator_le]
  intro m hm l hl
  have hmD : ∀ g ∈ Subgroup.zpowers c, g * m * g⁻¹ * m⁻¹ ∈ N := by
    intro g hg
    have := (hDc hg).2 m hm
    rwa [commutatorElement_def] at this
  have hmem := (CFSG.GroupTheory.CoprimeSection.mem_centralizer_sup_iff hNM hMN
    (Subgroup.zpowers_le.mpr hcM) (Subgroup.zpowers_le.mpr hcN) hcop hMs hm).mp hmD
  have hCN : M ⊓ Subgroup.centralizer (Subgroup.zpowers c : Set G) ≤
      Subgroup.normalizer (N : Set G) := inf_le_left.trans hMN
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ N hCN] at hmem
  obtain ⟨x, hx, n, hn, rfl⟩ := Set.mem_mul.mp hmem
  have hxc : x ∈ Subgroup.centralizer ({c} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_iff.mp hx.2 c (Subgroup.mem_zpowers c)
    exact this.symm
  have hxl : ⁅x, l⁆ = 1 := hxJ x hx.1 hxc l hl
  rw [commutatorElement_mul_left_eq_conj_mul, hxl, mul_one]
  exact (Subgroup.mem_normalizer_iff.mp (hMN hx.1) _).mp
    (commutator_mem_of_mem_normalizer' (hJN hl) hn)

end CFSG.RankThree.PartTwo.Sec16.Kd166
