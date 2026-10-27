module

public import CFSG.RankThree.GF2n.Parrott.Section5KLTransport
public import CFSG.RankThree.GF2n.Parrott.Section5KLUV
public import CFSG.RankThree.GF2n.Parrott.Section5KLTUV
public import CFSG.RankThree.GF2n.Parrott.ActionQAIdentificationOutsideEquality

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : A45)

omit [Finite G]
  in
private theorem orderOf_eq_two_of_mul_self {a : G} (ha : a * a = 1) (ha1 : a ≠ 1) :
    orderOf a = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact ha) ha1

theorem lemma54_kl (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z)) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ) :
    ∀ x ∈ H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G),
      orderOf x = 2 →
      (∀ c ∈ H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G),
        c * x * c⁻¹ ∉ lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)) →
      ∀ K : Subgroup G,
        IsSylowOf 2 K
          (H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
            centralizer ({x} : Set G)) →
        Nat.card K < 2 ^ 8 ∧
        ((∃ a ∈ centerIn K, a ≠ 1 ∧ a ≠ z ∧
            (∃ c ∈ H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G),
              c * a * c⁻¹ ∈ lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)) ∧
            (∃ c ∈ H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G),
              c * (a * z) * c⁻¹ ∈
                lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)) ∧
            ∀ e ∈ centerIn K, e = 1 ∨ e = z ∨ e = a ∨ e = a * z ∨ ∃ c ∈ H z, c * x * c⁻¹ = e) ∨
          (z ∈ Subgroup.closure ((fun k => k * k) '' (K : Set G)) ∧
            Subgroup.closure ((fun k => k * k) '' (K : Set G)) ≤ J z)) := by
  classical
  obtain ⟨z₁, hz₁sup, hz₁z, hord⟩ := exists_z1 (z := z) h
  have hz₁ : z₁ ∈ centerIn (J z) := by
    rw [hz₁sup]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z₁)
  intro x hx hx2 hxW K hK
  have hzW : z ∈ lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) :=
    z_mem_lemma54W h (σ := sigma1Nine (z := z) D * σ₂⁻¹) (τ := τ)
  have hxz : x ≠ z := by
    rintro rfl
    exact hxW 1 (Subgroup.one_mem _) (by simpa using hzW)
  refine ⟨card_lt_of_isSylowOf_centralizer_sigma1Nine_mul_inv D h hZ P hP hσ₂ hq₂ hc₂ hx hx2 hxz
    hK, ?_⟩
  change lemma54KLBranches z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) x
    (lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)) K
  have hxx : x * x = 1 := by
    have h2 := pow_orderOf_eq_one x
    rwa [hx2, pow_two] at h2
  let x' : ↥(H z) := ⟨x, hx.1⟩
  have hx'σ : (x' : G) ∈
      centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) := hx.2
  have hx'2 : x' * x' = 1 := Subtype.ext hxx
  obtain ⟨c, hcσ, hcases⟩ :=
    exists_conj_qH_eq_of_mem_centralizer_sigma1Nine_mul_inv D h hσ₂ hq₂ hc₂ hx'σ hx'2
  have hcY : (c : G) ∈
      H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) :=
    ⟨c.2, hcσ⟩
  have hyG : ((c * x' * c⁻¹ : ↥(H z)) : G) = (c : G) * x * (c : G)⁻¹ := rfl
  have hyσ : ((c * x' * c⁻¹ : ↥(H z)) : G) ∈
      centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) := by
    rw [hyG]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcσ hx.2) (Subgroup.inv_mem _ hcσ)
  have hy2 : (c * x' * c⁻¹) * (c * x' * c⁻¹) = 1 := by
    calc (c * x' * c⁻¹) * (c * x' * c⁻¹) = c * (x' * x') * c⁻¹ := by group
      _ = 1 := by rw [hx'2, mul_one, mul_inv_cancel]
  have hyy : ((c * x' * c⁻¹ : ↥(H z)) : G) * ((c * x' * c⁻¹ : ↥(H z)) : G) = 1 := by
    simpa using congrArg Subtype.val hy2
  refine forall_isSylowOf_lemma54KLBranches_of_conj h hcY ?_ K hK
  rw [← hyG]
  rcases hcases with h1 | ht | huv | htuv
  · exfalso
    have hyJ : ((c * x' * c⁻¹ : ↥(H z)) : G) ∈ J z :=
      Subgroup.mem_subgroupOf.mp ((J_mem_iff D _).mpr h1)
    have hy1 : ((c * x' * c⁻¹ : ↥(H z)) : G) ≠ 1 := by
      rw [hyG]
      intro h1'
      have hx1 : x = 1 := by
        have h3 := congrArg (fun g => (c : G)⁻¹ * g * (c : G)) h1'
        simpa [mul_assoc] using h3
      rw [hx1, orderOf_one] at hx2
      exact absurd hx2 (by norm_num)
    obtain ⟨d, hdY, hdW⟩ := exists_conj_mem_lemma54W D h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂ _
      (Subgroup.mem_inf.mpr ⟨hyJ, hyσ⟩) (orderOf_eq_two_of_mul_self hyy hy1)
    apply hxW (d * (c : G)) (Subgroup.mul_mem _ hdY hcY)
    have heq : d * (c : G) * x * (d * (c : G))⁻¹ =
        d * ((c * x' * c⁻¹ : ↥(H z)) : G) * d⁻¹ := by
      rw [hyG]
      group
    rw [heq]
    exact hdW
  · exfalso
    have hyW := mem_lemma54W_of_qH_eq_tA D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ (c * x' * c⁻¹) hyσ
      hyy ht
    exact hxW c hcY (by rw [← hyG]; exact hyW)
  · intro K' hK'
    obtain ⟨a, haZ, ha1, haz, haQ, ha2, hcenter⟩ :=
      exists_mem_centerIn_lemma54T₂_inf_centralizer_of_qH_eq_uv D h hZ hz₁ hz₁z hord P hP hσ₂ hq₂
        hc₂ hyσ hy2 huv
    have hK₀ := isSylowOf_lemma54T₂_inf_centralizer_of_qH_eq_uv D h hZ hz₁ hz₁z hord P hP hσ₂
      hq₂ hc₂ hyσ hy2 huv
    refine forall_isSylowOf_lemma54KLBranches h hK₀ ?_ K' hK'
    left
    have hzsq : z * z = 1 := by
      have h2 := pow_orderOf_eq_one z
      rwa [h.1, pow_two] at h2
    have hzJσ : z ∈
        J z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) :=
      Subgroup.mem_inf.mpr ⟨z_mem_J h, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp (z_centralizes_H h) _
          (sigma1Nine (z := z) D * σ₂⁻¹).2).symm⟩
    have hazQ : a * z ∈
        J z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) :=
      Subgroup.mul_mem _ haQ hzJσ
    have hazc : a * z = z * a :=
      Subgroup.mem_centralizer_iff.mp (z_centralizes_H h) a (J_le_H (Subgroup.mem_inf.mp haQ).1)
    have haz2 : (a * z) * (a * z) = 1 := by
      calc (a * z) * (a * z) = a * (z * a) * z := by group
        _ = a * (a * z) * z := by rw [← hazc]
        _ = (a * a) * (z * z) := by group
        _ = 1 := by rw [ha2, hzsq, one_mul]
    have haz1 : a * z ≠ 1 := by
      intro h1'
      apply haz
      calc a = (a * z) * z := by rw [mul_assoc, hzsq, mul_one]
        _ = z := by rw [h1', one_mul]
    refine ⟨a, haZ, ha1, haz, ?_, ?_, hcenter⟩
    · exact exists_conj_mem_lemma54W D h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂ a haQ
        (orderOf_eq_two_of_mul_self ha2 ha1)
    · exact exists_conj_mem_lemma54W D h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂ (a * z) hazQ
        (orderOf_eq_two_of_mul_self haz2 haz1)
  · intro K' hK'
    right
    exact closure_mul_self_of_qH_eq_t_uv D h hZ hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hyσ hy2 htuv K' hK'

theorem lemma54_kl_of_not_equalityBranch (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z))
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ) :
    ∀ x ∈ H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G),
      orderOf x = 2 →
      (∀ c ∈ H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G),
        c * x * c⁻¹ ∉ lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)) →
      ∀ K : Subgroup G,
        IsSylowOf 2 K
          (H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
            centralizer ({x} : Set G)) →
        Nat.card K < 2 ^ 8 ∧
        ((∃ a ∈ centerIn K, a ≠ 1 ∧ a ≠ z ∧
            (∃ c ∈ H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G),
              c * a * c⁻¹ ∈ lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)) ∧
            (∃ c ∈ H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G),
              c * (a * z) * c⁻¹ ∈
                lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)) ∧
            ∀ e ∈ centerIn K, e = 1 ∨ e = z ∨ e = a ∨ e = a * z ∨ ∃ c ∈ H z, c * x * c⁻¹ = e) ∨
          (z ∈ Subgroup.closure ((fun k => k * k) '' (K : Set G)) ∧
            Subgroup.closure ((fun k => k * k) '' (K : Set G)) ≤ J z)) := by
  obtain ⟨P, -, hP⟩ := (generatorConjugacy_iff_actionQA45_eq_conj_rhoAct h D).mp
    (generatorConjugacy_of_not_equalityBranch h D hIII)
  exact lemma54_kl D h hZ P (fun a => by simpa [rhoA, toQAct] using hP a) hσ₂ hq₂ hc₂ hqτ hτ hτ₁
    hτ₂

end CFSG.RankThree.GF2n.Parrott
