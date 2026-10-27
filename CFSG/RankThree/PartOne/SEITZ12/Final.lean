module

public import CFSG.RankThree.PartOne.SEITZ12.CaseB3
public import CFSG.RankThree.PartOne.SEITZ12.CaseB5
public import CFSG.RankThree.PartOne.SEITZ12.Generate
public import CFSG.RankThree.PartOne.SEITZ12.Module
public import CFSG.RankThree.PartOne.SEITZ12.Dichotomy

public section

namespace CFSG.RankThree.PartOne.SEITZ12

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution CFSG.LieType.Ree.LargeReeCover
  CFSG.RankThree.PartOne.SEITZ7

set_option linter.unusedSectionVars false

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem phi4_sylowH_mem_V₂ (hK : Nat.card K = 2 ^ (2 * m + 1)) (h i : K) :
    sylowH m K h i ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ := by
  have hv : sylowV m K 0 0 0 0 0 0 0 h i 0 0 0 = sylowH m K h i := by
    simp [sylowV, sylowA, sylowB, sylowD, sylowF, sylowJ, sylowK, sylowL, sylowX,
      largeReeSigma_zero, pinnedX_zero]
  rw [← hv]
  exact Subgroup.mem_inf.2 ⟨sylowV_rest_mem_rootSpan_one _ _ _ _ _ _ _ _ _,
    (Subgroup.mem_inf.1 (sylowV_mem hK _ _ _ _ _ _ _ _ _ _ _ _)).2⟩

theorem phi4_S₁_le_V₂ (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    conjSub (F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩) (szNw K) ≤
      F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  obtain ⟨b, c, h⟩ := exists_largeReeCoord_eq hK hy
  have hyB : y = sylowB m K b c := by rw [sylowB_eq_largeReeCoord, h]
  show szNw K * y * (szNw K)⁻¹ ∈ _
  rw [hyB, szNw_conj_sylowB]
  exact phi4_sylowH_mem_V₂ hK b c

theorem phi4_caseA_le (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) {a₀ : ModGL F4.tag K}
    (ha₀ : a₀ ∈ rankOneGroupTwo K m) (ha₀1 : a₀ ≠ 1)
    (hA : ¬ ∀ x ∈ phi4D m K a₀, x * centralZ K m 1 = centralZ K m 1 * x →
      x ∈ conjSub (F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩) (szNw K) ⊔
        rankOneGroupTwo K m) :
    F4.reeGamma K m ≤ phi4D m K a₀ := by
  have hX₂D : rankOneGroupTwo K m ≤ phi4D m K a₀ := phi4_X₂_le_D hK ha₀ ha₀1
  have hX₁D : conjSub (rankOneGroupTwo K m) (szNw K) ≤ phi4D m K a₀ := phi4_X₁_le_D hK ha₀ ha₀1
  have hS₁ : conjSub (F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩) (szNw K) ≤
      phi4D m K a₀ ⊓ F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ :=
    le_inf ((Subgroup.map_mono (f := (MulAut.conj (szNw K)).toMonoidHom)
      U₂_le_rankOneGroupTwo).trans hX₁D) (phi4_S₁_le_V₂ hK)
  have hX₂ : ∀ x ∈ rankOneGroupTwo K m,
      ∀ w ∈ phi4D m K a₀ ⊓ F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩,
      x * w * x⁻¹ ∈ phi4D m K a₀ ⊓ F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ := by
    intro x hx w hw
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (hX₂D hx) hw.1) (inv_mem (hX₂D hx)), ?_⟩
    exact (Subgroup.mem_normalizer_iff.1 (rankOneGroupTwo_le_normalizer_complement hK hx) w).1 hw.2
  have hne : ¬ phi4D m K a₀ ⊓ F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ ≤
      conjSub (F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩) (szNw K) := by
    intro hle
    refine hA fun x hxD hxz => ?_
    obtain ⟨v, hv, r, hr, rfl⟩ := phi4_decomp_centralizer hm hK (phi4_D_le hxD) hxz
    have hvD : v ∈ phi4D m K a₀ := by
      simpa using mul_mem hxD (inv_mem (hX₂D hr))
    exact Subgroup.mul_mem_sup (hle (Subgroup.mem_inf.2 ⟨hvD, hv⟩)) hr
  have hKk := module_lemma hm hK
    (phi4D m K a₀ ⊓ F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩) inf_le_right hS₁
    hX₂ hne
  exact reeGamma_le_of_K hm hK (phi4D m K a₀) hX₂D (phi4_t_mem_D hm hK ha₀ ha₀1)
    fun k => (hKk k).1

theorem phi4_caseB_contra (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {a₀ : ModGL F4.tag K} (ha₀ : a₀ ∈ rankOneGroupTwo K m)
    (hord : orderOf a₀ = p) (ha₀1 : a₀ ≠ 1)
    (hB' : ∀ x ∈ phi4D m K a₀, x * centralZ K m 1 = centralZ K m 1 * x →
      x ∈ conjSub (F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩) (szNw K) ⊔
        rankOneGroupTwo K m) :
    False := by
  have : Finite (phi4D m K a₀) := phi4_finite_D
  have hq : 8 ≤ 2 ^ (2 * m + 1) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcomm : ∀ x ∈ rankOneGroupTwo K m, ∀ y ∈ conjSub (rankOneGroupTwo K m) (szNw K),
      x * y = y * x := fun x hx y hy => commute_rankOneGroupTwo_szSubB x hx y hy
  have hinf : rankOneGroupTwo K m ⊓ conjSub (rankOneGroupTwo K m) (szNw K) = ⊥ :=
    rankOneGroupTwo_inf_szSubB hm hK
  have hS₂syl : ∀ P : Subgroup (ModGL F4.tag K), P ≤ rankOneGroupTwo K m → IsPGroup 2 P →
      F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩ ≤ P →
        P = F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩ :=
    fun P hP hP2 hU => phi4_U₂_max hm hK P hP hP2 hU
  have hcls : ∀ g ∈ phi4D m K a₀, ∀ x, inTwoA m K x → inTwoA m K (g * x * g⁻¹) :=
    fun g hg x hx => inTwoA_conj hx (phi4_D_le hg)
  have hcls₂ : ∀ z ∈ zTwo m K, z ≠ 1 → inTwoA m K z := by
    intro z hz hz1
    obtain ⟨c, rfl⟩ := (mem_zTwo_iff z).1 hz
    refine inTwoA_sylowB_zero hK ?_
    rintro rfl
    exact hz1 phi4_sylowB_zero_zero
  have hcls₃ : ∀ z₁ ∈ conjSub (zTwo m K) (szNw K), ∀ z₂ ∈ zTwo m K, z₁ ≠ 1 → z₂ ≠ 1 →
      ¬ inTwoA m K (z₁ * z₂) := by
    intro z₁ hz₁ z₂ hz₂ h₁ h₂
    obtain ⟨c, rfl⟩ := phi4_mem_Z₁_iff.1 hz₁
    obtain ⟨c', rfl⟩ := (mem_zTwo_iff z₂).1 hz₂
    refine not_inTwoA_mixed hm hK ?_ ?_
    · rintro rfl
      exact h₁ phi4_centralZ_zero
    · rintro rfl
      exact h₂ phi4_sylowB_zero_zero
  have hcls₄ : ∀ x ∈ rankOneGroupTwo K m, x * x = 1 → x ≠ 1 → inTwoA m K x :=
    fun x hx hx2 hx1 => inTwoA_of_involution_rankOneGroupTwo hm hK hx hx2 hx1
  have hB : ∀ z ∈ conjSub (zTwo m K) (szNw K), z ≠ 1 → ∀ x ∈ phi4D m K a₀, x * z = z * x →
      x ∈ conjSub (F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩) (szNw K) ⊔
        rankOneGroupTwo K m := by
    intro z hz hz1 x hxD hxz
    obtain ⟨c, rfl⟩ := phi4_mem_Z₁_iff.1 hz
    have hc : c ≠ 0 := by
      rintro rfl
      exact hz1 phi4_centralZ_zero
    refine hB' x hxD ?_
    have hx' : x ∈ F4.reeGamma K m ⊓ Subgroup.centralizer {centralZ K m c} :=
      Subgroup.mem_inf.2 ⟨phi4_D_le hxD, Subgroup.mem_centralizer_singleton_iff.2 hxz⟩
    rw [phi4_inf_centralizer_centralZ hm hK hc] at hx'
    exact Subgroup.mem_centralizer_singleton_iff.1 hx'.2
  have hN : ∀ n ∈ phi4D m K a₀, (∃ k : ℕ, orderOf n = 2 ^ k) →
      (∀ z ∈ conjSub (zTwo m K) (szNw K), n * z * n⁻¹ ∈ conjSub (zTwo m K) (szNw K)) →
        ∀ z ∈ conjSub (zTwo m K) (szNw K), n * z = z * n := by
    intro n hn ⟨k, hk⟩ hnorm
    refine phi4_two_element_centralizes hm hK (phi4_D_le hn) (k := k) ?_ hnorm
    rw [← hk]
    exact pow_orderOf_eq_one n
  exact phi4_caseB_false (phi4D m K a₀) (rankOneGroupTwo K m)
    (F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩) (zTwo m K) (szNw K) (2 ^ (2 * m + 1))
    (inTwoA m K) hq szNw_mul_self (phi4_t_mem_D hm hK ha₀ ha₀1) (phi4_X₂_le_D hK ha₀ ha₀1)
    (phi4_X₁_le_D hK ha₀ ha₀1) hcomm hinf (rankOneGroupTwo_perfect hm hK)
    U₂_le_rankOneGroupTwo hS₂syl (suzukiTwo_U₂ hm hK) hcls (inTwoA_szNw hm hK) hcls₂ hcls₃
    hcls₄ hB hN (phi4_t_square hm hK hp hp2 ha₀ hord)

theorem phi4_ambient_holds (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    Phi4Ambient m K := by
  intro p hp hp5 _ a₀ ha₀ hord
  have hp2 : p ≠ 2 := by omega
  have ha₀1 : a₀ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hord
    exact hp.one_lt.ne hord
  refine le_antisymm phi4_D_le ?_
  by_cases hB' : ∀ x ∈ phi4D m K a₀, x * centralZ K m 1 = centralZ K m 1 * x →
      x ∈ conjSub (F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩) (szNw K) ⊔ rankOneGroupTwo K m
  · exact (phi4_caseB_contra hm hK hp hp2 ha₀ hord ha₀1 hB').elim
  · exact phi4_caseA_le hm hK ha₀ ha₀1 hB'

end CFSG.RankThree.PartOne.SEITZ12
