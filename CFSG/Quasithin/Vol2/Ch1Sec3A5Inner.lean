module

public import CFSG.Quasithin.Vol2.Ch1Sec3A5J1
public import CFSG.Quasithin.Vol2.Ch1Sec3A5PSL
public import CFSG.Quasithin.Vol2.Ch1Sec3Lem139Cases

public section

namespace CFSG.Quasithin.L139A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.GorensteinWalter

variable {G : Type} [Group G]

@[expose] def conjSub {Y : Subgroup G} {t : G} (htY : t ∈ Subgroup.normalizer (Y : Set G)) :
    ↥Y ≃* ↥Y where
  toFun y := ⟨t * y * t⁻¹, (Subgroup.mem_normalizer_iff.mp htY y).mp y.2⟩
  invFun y := ⟨t⁻¹ * y * t, by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem htY) y).mp y.2
    simpa using this⟩
  left_inv y := by ext; simp [mul_assoc]
  right_inv y := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]

@[simp]
theorem conjSub_apply {Y : Subgroup G} {t : G} (htY : t ∈ Subgroup.normalizer (Y : Set G))
    (y : ↥Y) : ((conjSub htY y : ↥Y) : G) = t * y * t⁻¹ := rfl

@[expose] noncomputable def conjBar {Y : Subgroup G} {t : G}
    (htY : t ∈ Subgroup.normalizer (Y : Set G)) : MulAut (ModO2 Y) :=
  QuotientGroup.congr _ _ (conjSub htY) (CFSG.pCore_map_iso 2 (conjSub htY))

theorem conjBar_mk {Y : Subgroup G} {t : G} (htY : t ∈ Subgroup.normalizer (Y : Set G))
    (y : ↥Y) : conjBar htY (y : ModO2 Y) = ((conjSub htY y : ↥Y) : ModO2 Y) :=
  QuotientGroup.congr_mk _ _ _ _ y

theorem equiv_psl2_zmod {X : Type} [Group X] {p : ℕ} [Fact p.Prime] (h : IsPSL 2 p 1 X) :
    Nonempty (X ≃* PSL2 (ZMod p)) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card (ZMod p) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hK, pow_one]
  let φ : K ≃+* ZMod p := FiniteField.ringEquivOfCardEq hcard
  exact ⟨e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
    K).symm.trans (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ (Fin 2)))⟩

theorem five_lt_of_sq_mod_five {p : ℕ} (hp : p.Prime) (h : p ^ 2 % 5 = 1) : 5 < p := by
  by_contra hle
  replace hle : p ≤ 5 := by omega
  interval_cases p <;> first | exact absurd hp (by decide) | exact absurd h (by norm_num)

theorem mem_pCoreOf_of_mem_pCore {L Y : Subgroup G} (hLY : L ≤ Y) {y : ↥Y}
    (hyL : (y : G) ∈ L) (hy : y ∈ CFSG.pCore 2 ↥Y) : (y : G) ∈ pCoreOf 2 L := by
  set D : Subgroup G := (CFSG.pCore 2 ↥Y).map Y.subtype ⊓ L with hD
  have hDL : D ≤ L := inf_le_right
  have h2 : IsPGroup 2 D :=
    ((CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).map Y.subtype).to_le inf_le_left
  have hn : (D.subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨⟨q, hq, hqn⟩, -⟩ := hn
    refine ⟨⟨⟨g, hLY g.2⟩ * q * ⟨g, hLY g.2⟩⁻¹, CFSG.pCore_normal.conj_mem q hq _, ?_⟩,
      (g * n * g⁻¹ : ↥L).2⟩
    simp only [Subgroup.coe_subtype] at hqn
    simp [hqn]
  exact CFSG.LieType.BorelTits.le_pCoreOf 2 hDL hn h2 ⟨⟨y, hy, rfl⟩, hyL⟩

theorem mk_mem_modO2Image_pCoreOf_iff {L Y : Subgroup G} (hLY : L ≤ Y) {y : ↥Y}
    (hyL : (y : G) ∈ L) :
    (y : ModO2 Y) ∈ modO2Image Y (pCoreOf 2 L) ↔ (y : G) ∈ pCoreOf 2 L := by
  constructor
  · rintro ⟨z, hz, hzy⟩
    replace hz := Subgroup.mem_subgroupOf.mp hz
    have hzy' : (z : ModO2 Y) = (y : ModO2 Y) := hzy
    rw [QuotientGroup.eq] at hzy'
    have hzL : (z : G) ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L hz
    have hw := mem_pCoreOf_of_mem_pCore hLY (y := z⁻¹ * y) (by
      simpa using mul_mem (inv_mem hzL) hyL) hzy'
    have e1 : (y : G) = z * ((z⁻¹ * y : ↥Y) : G) := by simp
    rw [e1]
    exact mul_mem hz hw
  · intro hy
    exact ⟨y, Subgroup.mem_subgroupOf.mpr hy, rfl⟩

section Fin

variable [Finite G]

theorem inner_of_a5SecInner {L Y : Subgroup G} (hLY : L ≤ Y) {t : G}
    (htL : t ∈ Subgroup.normalizer (L : Set G)) (htY : t ∈ Subgroup.normalizer (Y : Set G))
    (hL5 : Nonempty (ModO2 L ≃* alternatingGroup (Fin 5))) (hsec : A5SecInner (ModO2 Y)) :
    ∃ ℓ ∈ L, ∀ x ∈ L, (t * x * t⁻¹)⁻¹ * (ℓ * x * ℓ⁻¹) ∈ pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eL⟩ := hL5
  set A := modO2Image Y L with hA
  set N := modO2Image Y (pCoreOf 2 L) with hN
  have hNL : pCoreOf 2 L ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hmemA : ∀ a ∈ A, ∃ y : ↥Y, (y : G) ∈ L ∧ (y : ModO2 Y) = a := by
    rintro a ⟨y, hy, rfl⟩
    exact ⟨y, Subgroup.mem_subgroupOf.mp hy, rfl⟩
  have hmkA : ∀ y : ↥Y, (y : G) ∈ L → (y : ModO2 Y) ∈ A := fun y hy =>
    ⟨y, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  have hNA : N ≤ A := by
    rintro _ ⟨y, hy, rfl⟩
    exact hmkA y (hNL (Subgroup.mem_subgroupOf.mp hy))
  have hNn : (N.subgroupOf A).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨y₁, hy₁L, hy₁⟩ := hmemA g g.2
    obtain ⟨y₂, hy₂, hy₂n⟩ := hn
    replace hy₂ := Subgroup.mem_subgroupOf.mp hy₂
    refine ⟨y₁ * y₂ * y₁⁻¹, ?_, ?_⟩
    · apply Subgroup.mem_subgroupOf.mpr
      have := (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hy₁L) _).mp hy₂
      simpa using this
    · rw [map_mul, map_mul, map_inv, hy₂n, QuotientGroup.mk'_apply, hy₁]
      simp
  have hN2 : IsPGroup 2 ↥N :=
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).comap_of_injective Y.subtype
      Y.subtype_injective).map _
  let ρ : ↥L →* ↥A :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp (Subgroup.inclusion hLY)).codRestrict A
      (fun x => hmkA _ x.2)
  have hρ : Function.Surjective ρ := by
    rintro ⟨a, ha⟩
    obtain ⟨y, hyL, rfl⟩ := hmemA a ha
    exact ⟨⟨y, hyL⟩, rfl⟩
  let ψ : ↥L →* ↥A ⧸ N.subgroupOf A := (QuotientGroup.mk' (N.subgroupOf A)).comp ρ
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hρ
  have hker : ψ.ker = CFSG.pCore 2 ↥L := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rw [show ((ρ x : ↥A) : ModO2 Y) = ((⟨x, hLY x.2⟩ : ↥Y) : ModO2 Y) from rfl,
      mk_mem_modO2Image_pCoreOf_iff hLY x.2]
    exact Subgroup.mem_map_iff_mem L.subtype_injective
  let eQ : ModO2 L ≃* (↥A ⧸ N.subgroupOf A) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  have hβA : ∀ x ∈ A, conjBar htY x ∈ A := by
    intro x hx
    obtain ⟨y, hyL, rfl⟩ := hmemA x hx
    rw [conjBar_mk]
    exact hmkA _ ((Subgroup.mem_normalizer_iff.mp htL y).mp hyL)
  have hβN : ∀ x ∈ N, conjBar htY x ∈ N := by
    rintro _ ⟨y, hy, rfl⟩
    replace hy := Subgroup.mem_subgroupOf.mp hy
    refine ⟨conjSub htY y, ?_, (conjBar_mk htY y).symm⟩
    apply Subgroup.mem_subgroupOf.mpr
    rw [conjSub_apply]
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L htL) y).mp hy
  obtain ⟨a, haA, ha⟩ := hsec A N hNA hN2 ⟨eQ.symm.trans eL⟩ (conjBar htY) hβA hβN
  obtain ⟨ℓ₀, hℓL, rfl⟩ := hmemA a haA
  refine ⟨ℓ₀, hℓL, fun x hx => ?_⟩
  have h1 := ha _ (hmkA ⟨x, hLY hx⟩ hx)
  rw [conjBar_mk] at h1
  set w : ↥Y := (conjSub htY ⟨x, hLY hx⟩)⁻¹ * (ℓ₀ * ⟨x, hLY hx⟩ * ℓ₀⁻¹) with hw
  have hwmk : (w : ModO2 Y) = ((conjSub htY ⟨x, hLY hx⟩ : ↥Y) : ModO2 Y)⁻¹ *
      ((ℓ₀ : ModO2 Y) * ((⟨x, hLY hx⟩ : ↥Y) : ModO2 Y) * (ℓ₀ : ModO2 Y)⁻¹) := by
    rw [hw]
    simp
  have hwG : (w : G) = (t * x * t⁻¹)⁻¹ * (ℓ₀ * x * (ℓ₀ : G)⁻¹) := by
    rw [hw]
    simp
  have hwL : (w : G) ∈ L := by
    rw [hwG]
    exact mul_mem (inv_mem ((Subgroup.mem_normalizer_iff.mp htL x).mp hx))
      (mul_mem (mul_mem hℓL hx) (inv_mem hℓL))
  rw [← hwmk] at h1
  have h2 := (mk_mem_modO2Image_pCoreOf_iff hLY hwL).mp h1
  rwa [hwG] at h2

end Fin

theorem lemma139A5Inner_of (h37 : A37ForSQTK) :
    H13.Lemma139A5Inner := by
  intro G _ _ hQ hs hnab T L Y _ hL hY hLY _ _ hL5 hYc t htT htL
  have htY : t ∈ Subgroup.normalizer (Y : Set G) :=
    (lemma_1_2_8_one_le hQ hs hnab h37 hL hY hLY ⟨htT, htL⟩).2
  refine inner_of_a5SecInner hLY htL htY hL5 ?_
  rcases hYc with hJ | ⟨p, hp, hp5, hP⟩
  · exact a5SecInner_j1 hJ
  · have : Fact p.Prime := ⟨hp⟩
    obtain ⟨ι⟩ := equiv_psl2_zmod hP
    exact a5SecInner_of_equiv_psl2 (five_lt_of_sq_mod_five hp hp5) ι

end CFSG.Quasithin.L139A5
