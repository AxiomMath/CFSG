module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9RW
public import CFSG.RankThree.GF2n.Stroth80.HeringSec96Flag

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.G11.P3Ortho.Om4
open CFSG.Open.StatedAPI
open scoped commutatorElement Matrix

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem exists_centralizer_mul_of_caseA (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) (hA : CaseA Q Z t) {r : G} (hr : r ∈ Rt M (LB M Q B) t) :
    ∃ c ∈ Rt M (LB M Q B) t, c * t = t * c ∧ r * c⁻¹ ∈ hc.CN t := by
  classical
  have h := hs.toSec5
  have ht : t ∈ LB M Q B := h.mem
  obtain ⟨K, fK, finK, hK, φ, hφ, hker, -, hn, -, -⟩ := hs.plus4
  haveI := hn
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  have hq4 : 4 ≤ Nat.card K := hK ▸ hc.hyp.q4
  let φ'' : ↥(Rt M (LB M Q B) t) →*
      (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) := (Ψ K).toMonoidHom.comp φ
  have hφ''1 : ∀ s : ↥(Rt M (LB M Q B) t), φ'' s = 1 ↔ (s : G) ∈ hc.CN t := by
    intro s
    show Ψ K (φ s) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hrange : φ''.range = (rho' K).range := by
    have h1 : φ''.range = φ.range.map (Ψ K).toMonoidHom := MonoidHom.range_comp _ _
    rw [h1, hφ, map_statedOmega, commutator_eq_range hq4]
  have hperf : ⁅φ''.range, φ''.range⁆ = φ''.range := by
    rw [hrange]
    have hSL := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hq4
    have hP : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K ×
        Matrix.SpecialLinearGroup (Fin 2) K) := isPerfect_prod hSL hSL
    have hPR : Group.IsPerfect (rho' K).range := Group.IsPerfect.range (rho' K)
    exact Subgroup.commutator_eq_self
  have hcen : ∀ x ∈ Q, ∀ z ∈ Z, x * z = z * x :=
    fun x hx z hz => (hc.hyp.toHyp79.V_central hz hx).symm
  have commZ : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x :=
    fun x hx y hy => hcen x (hc.Z_le_Q hx) y hy
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt ht
  have hQk : ∀ y ∈ Q, ∀ hy : y ∈ Rt M (LB M Q B) t, φ'' ⟨y, hy⟩ = 1 :=
    fun y hyQ hyR => (hφ''1 _).mpr (hc.Q_le_CN ht hyQ)
  have hcR : ∀ c : ↥(Rt M (LB M Q B) t), ∀ z ∈ Z, (c : G) * z * (c : G)⁻¹ = z :=
    fun c z hz => caseA_conj_of_mem_H0 (hc.Rt_le_H0 t c.2) hz
  have hred : ∀ s : ↥(Rt M (LB M Q B) t), ∃ c : ↥(Rt M (LB M Q B) t),
      (∃ w ∈ Z, (c : G) * t * (c : G)⁻¹ = t * w) ∧ φ'' c = φ'' s := by
    intro s
    obtain ⟨y, hyQ, w, hwZ, hsy⟩ := caseA_conj hc h hA (s : G) s.2
    have hyR : y⁻¹ ∈ Rt M (LB M Q B) t := (Rt M (LB M Q B) t).inv_mem (hQR hyQ)
    have hyw : y⁻¹ * w * y = w := by
      rw [hcen y⁻¹ (Q.inv_mem hyQ) w hwZ]
      group
    refine ⟨⟨y⁻¹, hyR⟩ * s, ⟨w, hwZ, ?_⟩, ?_⟩
    · show (y⁻¹ * (s : G)) * t * (y⁻¹ * (s : G))⁻¹ = t * w
      calc (y⁻¹ * (s : G)) * t * (y⁻¹ * (s : G))⁻¹ = y⁻¹ * ((s : G) * t * (s : G)⁻¹) * y := by
            group
        _ = y⁻¹ * (y * t * y⁻¹ * w) * y := by rw [hsy]
        _ = t * (y⁻¹ * w * y) := by group
        _ = t * w := by rw [hyw]
    · rw [MonoidHom.map_mul, hQk y⁻¹ (Q.inv_mem hyQ) hyR, one_mul]
  have hcomm : ∀ g₁ ∈ φ''.range, ∀ g₂ ∈ φ''.range,
      ⁅g₁, g₂⁆ ∈ ((Subgroup.centralizer {t}).subgroupOf (Rt M (LB M Q B) t)).map φ'' := by
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨r₁, rfl⟩ := MonoidHom.mem_range.mp hg₁
    obtain ⟨r₂, rfl⟩ := MonoidHom.mem_range.mp hg₂
    obtain ⟨c₁, ⟨w₁, hw₁Z, e₁⟩, hφ₁⟩ := hred r₁
    obtain ⟨c₂, ⟨w₂, hw₂Z, e₂⟩, hφ₂⟩ := hred r₂
    rw [← hφ₁, ← hφ₂]
    refine Subgroup.mem_map.mpr ⟨⁅c₁, c₂⁆, ?_, map_commutatorElement φ'' c₁ c₂⟩
    rw [Subgroup.mem_subgroupOf]
    have hk := caseA_comm_centralizes (t := t) (c₁ := (c₁ : G)) (c₂ := (c₂ : G))
      (hcR c₁) (hcR c₂) hw₁Z hw₂Z commZ e₁ e₂
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hk.symm
  have hcov : φ''.range ≤
      ((Subgroup.centralizer {t}).subgroupOf (Rt M (LB M Q B) t)).map φ'' :=
    calc φ''.range = ⁅φ''.range, φ''.range⁆ := hperf.symm
      _ ≤ _ := Subgroup.commutator_le.mpr hcomm
  obtain ⟨c, hcC, hcφ⟩ := Subgroup.mem_map.mp (hcov ⟨⟨r, hr⟩, rfl⟩)
  have hct : (c : G) * t = t * (c : G) :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hcC) t
      (Set.mem_singleton t)).symm
  have h1 : φ'' (⟨r, hr⟩ * c⁻¹) = 1 := by
    rw [map_mul, map_inv, hcφ, mul_inv_cancel]
  exact ⟨c, c.2, hct, (hφ''1 _).mp h1⟩

theorem wpoint96_caseA (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (hA : CaseA Q Z t) : WPointConcl M Q Z B t := by
  intro _ hBt
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hYR : Y ≤ Rt M (LB M Q B) t := hsplit.1.2.2.2.1
  obtain ⟨y, hyY, hyB⟩ : ∃ y ∈ Y, ¬ conjSubgroup y B ≤ (B ⊔ Z : Subgroup G) := by
    by_contra hno
    push Not at hno
    have hle : Uline Z B Y ≤ B ⊔ Z := sup_le le_sup_right (iSup₂_le hno)
    have hcard := Subgroup.card_le_of_le hle
    have hBcard : Nat.card B = Nat.card Z := by
      obtain ⟨g, hg⟩ := hc.conj
      rw [hg, card_conjSubgroup]
    rw [(sec97LineNat_of h34 h311a G M Q Z B hc n t hs X Y hsplit).1, hc.card_sup_Z,
      hBcard] at hcard
    have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
    have h3 : Nat.card Z * Nat.card Z * Nat.card Z ≤ Nat.card Z * Nat.card Z * 1 :=
      calc Nat.card Z * Nat.card Z * Nat.card Z = Nat.card Z ^ 3 := by ring
        _ ≤ Nat.card Z * Nat.card Z := hcard
        _ = Nat.card Z * Nat.card Z * 1 := by ring
    have h1 := Nat.le_of_mul_le_mul_left h3 (by positivity)
    omega
  obtain ⟨c, hcR, hct, hnN⟩ := exists_centralizer_mul_of_caseA hc hs hA (hYR hyY)
  have hcM : c ∈ M := hc.Rt_le_M t hcR
  have hcomm : ∀ b ∈ B, ⁅y * c⁻¹, c * b * c⁻¹⁆ ∈ Z := fun b hb =>
    hnN.2 _ (hc.conj_Rt_le_Vt ht hcR (Subgroup.mem_sup_left ⟨b, hb, rfl⟩))
  have hyb : ∀ b ∈ B, y * b * y⁻¹ ∈ conjSubgroup y B := fun b hb => by
    rw [mem_conjSubgroup, show y⁻¹ * (y * b * y⁻¹) * y = b by group]
    exact hb
  have hZB : Z ≤ QB B := hc.Z_le_QB.1
  have hflag := sec96Flag_of h34 h311a G M Q Z B hc n t hs X Y hsplit
  refine ⟨conjSubgroup c B, ⟨c, hcM, rfl⟩, ?_, ?_⟩
  ·
    intro hCB
    apply hyB
    intro x hx
    have hb : y⁻¹ * x * y ∈ B := mem_conjSubgroup.mp hx
    have hcb : c * (y⁻¹ * x * y) * c⁻¹ ∈ B := by
      rw [← hCB]
      exact ⟨_, hb, rfl⟩
    have hx' : x = ⁅y * c⁻¹, c * (y⁻¹ * x * y) * c⁻¹⁆ * (c * (y⁻¹ * x * y) * c⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [hx']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hcomm _ hb)) (Subgroup.mem_sup_left hcb)
  · intro x hx
    have hb : c⁻¹ * x * c ∈ B := mem_conjSubgroup.mp hx
    have e : c * (c⁻¹ * x * c) * c⁻¹ = x := by group
    have hxP : x ∈ Q ⊓ QB (Subgroup.zpowers t) := by
      have h1 := caseA_conj_P hc hcM hct
        (show c⁻¹ * x * c ∈ Q ⊓ QB (Subgroup.zpowers t) from ⟨hc.le hb, hBt hb⟩)
      rwa [e] at h1
    have hyl : y * (c⁻¹ * x * c) * y⁻¹ ∈ QB B := by
      have h1 := hflag (conjSubgroup_le_Uline (Z := Z) hyY (hyb _ hb))
      exact (sup_le inf_le_right hZB) h1
    have hcz : ⁅y * c⁻¹, x⁆ ∈ Z := by
      have h1 := hcomm _ hb
      rwa [e] at h1
    have hx' : x = ⁅y * c⁻¹, x⁆⁻¹ * (y * (c⁻¹ * x * c) * y⁻¹) := by
      rw [commutatorElement_def]
      group
    refine ⟨hxP, ?_⟩
    rw [hx']
    exact (QB B).mul_mem ((QB B).inv_mem (hZB hcz)) hyl

end HS9


@[expose] def Sec96WCaseAStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ X Y : Subgroup G, HS9.Split95 M Q Z B t X Y → HS9.Sec4Concl M Q Z B X Y →
      HS9.OneConcl hc X Y → CaseA Q Z t → HS9.WPointConcl M Q Z B t

@[expose] def Sec96WCaseBStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ X Y : Subgroup G, HS9.Split95 M Q Z B t X Y → HS9.Sec4Concl M Q Z B X Y →
      HS9.OneConcl hc X Y → ¬ CaseA Q Z t → HS9.WPointConcl M Q Z B t

theorem sec96WCaseA_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement) :
    Sec96WCaseAStatement := by
  intro G _ _ M Q Z B hc n t hs X Y hsplit _ _ hA
  exact HS9.wpoint96_caseA h34 h311a hc hs hsplit hA

theorem sec96W_of_cases (hA : Sec96WCaseAStatement) (hB : Sec96WCaseBStatement) :
    Sec96WStatement := by
  intro G _ _ M Q Z B hc n t hs X Y hsplit h4 h1
  by_cases hCA : CaseA Q Z t
  · exact hA G M Q Z B hc n t hs X Y hsplit h4 h1 hCA
  · exact hB G M Q Z B hc n t hs X Y hsplit h4 h1 hCA

theorem sec96W_of_caseB (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hB : Sec96WCaseBStatement) : Sec96WStatement :=
  sec96W_of_cases (sec96WCaseA_of h34 h311a) hB

end CFSG.RankThree.GF2n.Stroth80
