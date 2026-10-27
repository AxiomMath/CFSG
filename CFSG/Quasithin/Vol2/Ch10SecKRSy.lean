module

public import CFSG.Quasithin.Vol2.Ch10SecKRSu
public import CFSG.Quasithin.Vol2.Ch10SecKRSv
public import CFSG.Quasithin.Vol2.Ch10SecKRSw

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open CFSG.Open C10P4F

variable {G : Type} [Group G]

theorem conj_mem_theta_of {X : Subgroup G} {g : G} (hX : ∀ x ∈ X, x ^ 3 = 1 → g * x * g⁻¹ ∈ X)
    {x : G} (hx : x ∈ theta X) : g * x * g⁻¹ ∈ theta X := by
  induction hx using Subgroup.closure_induction with
  | mem z hz =>
    refine mem_theta (hX z hz.1 hz.2) ?_
    rw [conj_pow, hz.2, mul_one, mul_inv_cancel]
  | one => simp
  | mul a b _ _ ha hb =>
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ha

variable [Finite G] {J : Subgroup G} (ρ : ↥J →* SL5) (hρ : Function.Surjective ρ)
  (hker : ∀ j : ↥J, ρ j = 1 → ∃ k : ℕ, j ^ 2 ^ k = 1) {P : Subgroup G} (hPJ : P ≤ J)
  (hlift : ∀ j : ↥J, (j : G) ^ 3 = 1 → ρ j ∈ Q1 → (j : G) ∈ P)

omit [Finite G] in
include hρ hker hlift in
theorem img_eq_Q1 (hPQ : img ρ P ≤ Q1) : img ρ P = Q1 := by
  refine le_antisymm hPQ ?_
  rw [← theta_Q1]
  refine (Subgroup.closure_le _).mpr ?_
  rintro g ⟨hg, hg3⟩
  obtain ⟨j, hj3, rfl⟩ := exists_three_lift ρ hker (MonoidHom.mem_range.mpr (hρ g)) hg3
  have hj3' : (j : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hj3
  exact ⟨j, Subgroup.mem_subgroupOf.mpr (hlift j hj3' hg), rfl⟩

omit [Finite G] in
include hρ hker hPJ hlift in
theorem exists_mem_theta {g : SL5} (hg : g ∈ M 3) (hg3 : g ^ 3 = 1) :
    ∃ j : ↥J, (j : G) ∈ theta (pre ρ P (M 3)) ∧ (j : G) ^ 3 = 1 ∧ ρ j = g := by
  obtain ⟨j, hj3, rfl⟩ := exists_three_lift ρ hker (MonoidHom.mem_range.mpr (hρ g)) hg3
  have hj3' : (j : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hj3
  exact ⟨j, mem_theta ((mem_pre hPJ).mpr ⟨hlift j hj3' (M_le_Q1 (by norm_num) hg), hg⟩) hj3',
    hj3', rfl⟩

omit [Finite G] in
include hρ hker hPJ hlift in
theorem three_dvd_card_theta : 3 ∣ Nat.card (theta (pre ρ P (M 3))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, hj, hj3, hjg⟩ := exists_mem_theta ρ hρ hker hPJ hlift
    (by rw [← P2_eq]; exact tP2_mem) (by decide)
  have hj1 : (j : G) ≠ 1 := fun h => by
    have : j = 1 := Subtype.ext h
    rw [this, map_one] at hjg
    exact (by decide : tP2 ≠ 1) hjg.symm
  have h3 : orderOf (⟨(j : G), hj⟩ : ↥(theta (pre ρ P (M 3)))) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hj3 hj1
  exact (dvd_of_eq h3.symm).trans (orderOf_dvd_natCard _)

include hker hPJ in
theorem not_nine_dvd_card_theta : ¬ 9 ∣ Nat.card (theta (pre ρ P (M 3))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h9
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 2)
    (G := ↥(theta (pre ρ P (M 3)))) (by simpa using h9)
  have hTJ : theta (pre ρ P (M 3)) ≤ J := ((theta_le _).trans inf_le_left).trans hPJ
  let f : ↥Q →* SL5 := (ρ.comp (Subgroup.inclusion hTJ)).comp Q.subtype
  have hQ3 : IsPGroup 3 Q := IsPGroup.of_card hQ
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨k, hk⟩ := hker _ hq
    obtain ⟨m, hm⟩ := hQ3 q
    have h1 : (((q : ↥(theta (pre ρ P (M 3)))) : G)) = 1 := eq_one_of_two_three (m := k) (n := m)
      (by simpa using congrArg Subtype.val hk)
      (by simpa using congrArg (fun x : ↥Q => ((x : ↥(theta (pre ρ P (M 3)))) : G)) hm)
    exact Subtype.ext (Subtype.ext h1)
  have hle : f.range ≤ P2 := by
    rintro _ ⟨q, rfl⟩
    have hq : ((q : ↥(theta (pre ρ P (M 3)))) : G) ∈ pre ρ P (M 3) :=
      theta_le _ (q : ↥(theta (pre ρ P (M 3)))).2
    rw [P2_eq]
    exact ((mem_pre hPJ).mp hq).2
  have hR3 : IsPGroup 3 f.range := fun y => by
    obtain ⟨q, hq⟩ := y.2
    obtain ⟨m, hm⟩ := hQ3 q
    refine ⟨m, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow, ← hq, ← map_pow, hm, map_one]
    rfl
  have hcard := card_le_three_of_le_P2 hle hR3
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hQ] at hcard
  norm_num at hcard

omit [Finite G] in
include hρ hker hPJ hlift in
theorem pCoreOf_theta_ne_bot : pCoreOf 2 (theta (pre ρ P (M 3))) ≠ ⊥ := by
  have hTJ : theta (pre ρ P (M 3)) ≤ J := ((theta_le _).trans inf_le_left).trans hPJ
  have hTM : ∀ x (hx : x ∈ theta (pre ρ P (M 3))), ρ ⟨x, hTJ hx⟩ ∈ P2 := fun x hx => by
    rw [P2_eq]
    exact ((mem_pre hPJ).mp (theta_le _ hx)).2
  have hNT : pre ρ (theta (pre ρ P (M 3))) radP2 ≤ theta (pre ρ P (M 3)) := inf_le_left
  have hNn : ((pre ρ (theta (pre ρ P (M 3))) radP2).subgroupOf
      (theta (pre ρ P (M 3)))).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    obtain ⟨hnT, hnr⟩ := (mem_pre hTJ).mp hn
    refine (mem_pre hTJ).mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2 hnT)
      (Subgroup.inv_mem _ g.2), ?_⟩
    have h1 : (⟨(g : G) * n * (g : G)⁻¹, hTJ (Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2 hnT)
        (Subgroup.inv_mem _ g.2))⟩ : ↥J) = ⟨g, hTJ g.2⟩ * ⟨n, hTJ hnT⟩ * (⟨g, hTJ g.2⟩)⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv]
    exact conj_mem_radP2 (hTM g g.2) hnr⟩
  have hN2 : IsPGroup 2 (pre ρ (theta (pre ρ P (M 3))) radP2) := fun n => by
    obtain ⟨hnT, hnr⟩ := (mem_pre hTJ).mp n.2
    obtain ⟨k, hk⟩ := isPGroup_uniSL_five ⟨_, radP2_le_uniSL hnr⟩
    have hk' : ρ (⟨n, hTJ hnT⟩ ^ 2 ^ k) = 1 := by
      rw [map_pow]
      simpa using congrArg Subtype.val hk
    obtain ⟨m, hm⟩ := hker _ hk'
    refine ⟨k + m, Subtype.ext ?_⟩
    have h1 : ((n : G) ^ 2 ^ k) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    simpa [pow_add, pow_mul] using h1
  obtain ⟨j₁, hj₁, -, hρ₁⟩ := exists_mem_theta ρ hρ hker hPJ hlift
    (by rw [← P2_eq]; exact tP2_mem) (by decide)
  obtain ⟨j₂, hj₂, -, hρ₂⟩ := exists_mem_theta ρ hρ hker hPJ hlift
    (by rw [← P2_eq]; exact wP2_mem) (by decide)
  have hmem : (j₁ : G) * j₂ ∈ pre ρ (theta (pre ρ P (M 3))) radP2 :=
    (mem_pre hTJ).mpr ⟨Subgroup.mul_mem _ hj₁ hj₂, by
      show ρ (j₁ * j₂) ∈ radP2
      rw [map_mul, hρ₁, hρ₂, ← trvE03_eq]
      exact trvE03_mem_radP2⟩
  have hne : (j₁ : G) * j₂ ≠ 1 := fun h => by
    have h1 : j₁ * j₂ = 1 := Subtype.ext h
    have h2 := congrArg ρ h1
    rw [map_mul, hρ₁, hρ₂, map_one, ← trvE03_eq] at h2
    exact (by decide : (trvE (0 : Fin 5) 3 (by decide) : SL5) ≠ 1) h2
  have hle := CFSG.LieType.BorelTits.le_pCoreOf 2 hNT hNn hN2
  intro hbot
  rw [hbot] at hle
  exact hne ((Subgroup.mem_bot).mp (hle hmem))

include hPJ hlift in
theorem mem_normalizer_theta {d : ↥J} (hd : ρ d ∈ P0) :
    (d : G) ∈ Subgroup.normalizer (theta (pre ρ P (M 3)) : Set G) := by
  refine mem_normalizer_of_conj_mem fun z hz => conj_mem_theta_of (fun x hx hx3 => ?_) hz
  obtain ⟨hxP, hxM⟩ := (mem_pre hPJ).mp hx
  have hx3' : (⟨x, hPJ hxP⟩ : ↥J) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  have hy3 : ((d * ⟨x, hPJ hxP⟩ * d⁻¹ : ↥J) : G) ^ 3 = 1 := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [conj_pow, hx3, mul_one, mul_inv_cancel]
  have hρy : ρ (d * ⟨x, hPJ hxP⟩ * d⁻¹) ∈ P2 := by
    rw [map_mul, map_mul, map_inv]
    refine conj_mem_P2_of_mem_P0 hd (by rw [P2_eq]; exact hxM) ?_
    rw [← map_pow, hx3', map_one]
  have hyP := hlift _ hy3 (by rw [P2_eq] at hρy; exact M_le_Q1 (by norm_num) hρy)
  have hmem : ((d * ⟨x, hPJ hxP⟩ * d⁻¹ : ↥J) : G) ∈ pre ρ P (M 3) :=
    (mem_pre hPJ).mpr ⟨hyP, by rw [P2_eq] at hρy; exact hρy⟩
  simpa using hmem

theorem false_of_E27 (hK : CFSG.QuasithinUnique.quasithinIsQTKECat G) {R K : Subgroup G}
    {d d' u w : G} (hR2 : pCoreOf 2 R ≠ ⊥) (h3 : 3 ∣ Nat.card R) (h9 : ¬ 9 ∣ Nat.card R)
    (hRE : ∀ x ∈ R, x ∈ Subgroup.centralizer ({u} : Set G) ∧
      x ∈ Subgroup.centralizer ({w} : Set G))
    (hdR : d ∈ Subgroup.normalizer (R : Set G)) (hd'R : d' ∈ Subgroup.normalizer (R : Set G))
    (hK2 : IsPGroup 2 K) (hd3 : d ^ 3 = 1) (hd'3 : d' ^ 3 = 1)
    (hdK : d ∈ Subgroup.normalizer (K : Set G)) (hd'K : d' ∈ Subgroup.normalizer (K : Set G))
    (hcomm : d * d' * d⁻¹ * d'⁻¹ ∈ K) (hKu : K ≤ Subgroup.centralizer ({u} : Set G))
    (hKw : K ≤ Subgroup.centralizer ({w} : Set G)) (hdw : d ∈ Subgroup.centralizer ({w} : Set G))
    (hd'u : d' ∈ Subgroup.centralizer ({u} : Set G))
    (hdu : d ∉ Subgroup.centralizer ({u} : Set G))
    (hd'w : d' ∉ Subgroup.centralizer ({w} : Set G)) : False := by
  obtain ⟨E, hEH, hEc, hE3, hE9, hEE⟩ := exists_E9 hK2 hdR hd'R hd3 hd'3 hdK hd'K hcomm hKu hKw
    hdw hd'u hdu hd'w
  have hNH : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (pCoreOf 2 R : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 R
  have hER : E ⊓ R = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxE, hxR⟩
    exact hEE x hxE (hRE x hxR).1 (hRE x hxR).2
  have h3H := three_le_pRank (hEH.trans hNH) (Subgroup.le_normalizer.trans hNH) hEH hEc hE3 hE9
    hER h3 h9
  have hH2 : pCoreOf 2 (Subgroup.normalizer (pCoreOf 2 R : Set G)) ≠ ⊥ := by
    intro hbot
    apply hR2
    have hle : pCoreOf 2 R ≤ pCoreOf 2 (Subgroup.normalizer (pCoreOf 2 R : Set G)) :=
      CFSG.LieType.BorelTits.le_pCoreOf 2 Subgroup.le_normalizer Subgroup.normal_in_normalizer
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 R)
    rw [hbot] at hle
    exact eq_bot_iff.mpr hle
  have := pRank_le_two_of_pCoreOf_ne_bot hK hH2 Nat.prime_three (by norm_num)
  omega

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS
