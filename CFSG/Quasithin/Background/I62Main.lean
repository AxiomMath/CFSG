module

public import CFSG.Quasithin.Background.I62Conj
public import CFSG.CGT.Timmesfeld75.Core214Proof
public import CFSG.CGT.Timmesfeld75.Lemma214Transfer
public import CFSG.CGT.Timmesfeld75.AschbacherNoPolarDischarge
public import CFSG.CGT.T75N.BenderCenter
public import CFSG.CGT.T75N.UnitaryTwoGen
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneModels

public section

namespace CFSG.CGT.Timmesfeld75

theorem lemma214_proved :
    Lemma214 :=
  lemma214_of_core
      (core214_of_inputs aschbacherNoPolarInput_of_repo T75N.benderCenterInput
          T75N.unitaryTwoGenerationInput)

end CFSG.CGT.Timmesfeld75

namespace CFSG.Quasithin.ASInputs

open CFSG.Open

@[expose] def AS_I_6_2_twoCases : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V A : Subgroup G), IsElemAbelian 2 V → IsElemAbelian 2 A →
    Nat.card V = Nat.card A → IsTISetIn V ⊤ → IsTISetIn A ⊤ →
    (∀ g : G, V ≠ conjSubgroup A g → conjSubgroup A g ⊓ V = ⊥) →
    tiU V A ≠ ⊥ → tiU V A < V →
      (tiU V A ⊓ tiB V A = ⊥ ∧ ⁅tiU V A, tiB V A⁆ = ⊥ ∧
        tiX V A ≤ Subgroup.normalizer (tiY V A : Set G) ∧
        ∀ v ∈ V, v ∉ tiU V A →
          tiU V A = tiY V A ⊓ Subgroup.centralizer ({v} : Set G) ∧
            tiU V A = ⁅tiY V A, Subgroup.zpowers v⁆) ∧
      ∃ _ : ((tiY V A).subgroupOf (tiX V A)).Normal,
        (∃ m : ℕ, Odd m ∧
            Nonempty (↥(tiX V A) ⧸ (tiY V A).subgroupOf (tiX V A) ≃* DihedralGroup m)) ∨
          (∃ n : ℕ, IsPSL 2 2 n (↥(tiX V A) ⧸ (tiY V A).subgroupOf (tiX V A))) ∨
          ∃ n : ℕ, IsSz n (↥(tiX V A) ⧸ (tiY V A).subgroupOf (tiX V A))

end CFSG.Quasithin.ASInputs

namespace CFSG.Quasithin.I62

open CFSG.Open CFSG.Quasithin.ASInputs CFSG.QuasithinUnique
open scoped Pointwise MatrixGroups commutatorElement

section Transport

variable {G : Type} [Group G] {X : Subgroup G}

theorem tconj_subgroupOf (K : Subgroup G) (g : ↥X) :
    CFSG.CGT.Timmesfeld75.conjSubgroup g (K.subgroupOf X) =
      (conjSubgroup K (g : G)⁻¹).subgroupOf X := by
  ext x
  rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    mem_conjSubgroup_iff, inv_inv]
  simp

theorem mem_normalizer_subgroupOf_iff {K : Subgroup G} (hK : K ≤ X) (x : ↥X) :
    x ∈ Subgroup.normalizer ((K.subgroupOf X : Subgroup ↥X) : Set ↥X) ↔
      (x : G) ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    by_cases hy : y ∈ X
    · have := h ⟨y, hy⟩
      simpa [Subgroup.mem_subgroupOf] using this
    · constructor
      · intro hyK
        exact absurd (hK hyK) hy
      · intro hyK
        exfalso
        apply hy
        have h1 : (x : G) * y * (x : G)⁻¹ ∈ X := hK hyK
        rw [show y = (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹) * x by group]
        exact X.mul_mem (X.mul_mem (X.inv_mem x.2) h1) x.2
  · intro h y
    have := h (y : G)
    simpa [Subgroup.mem_subgroupOf] using this

theorem normIn_subgroupOf (K : Subgroup G) {L : Subgroup G} (hL : L ≤ X) :
    CFSG.CGT.Timmesfeld75.normIn (K.subgroupOf X) (L.subgroupOf X) =
      (K ⊓ Subgroup.normalizer (L : Set G)).subgroupOf X := by
  ext x
  rw [CFSG.CGT.Timmesfeld75.normIn, Subgroup.mem_inf, mem_normalizer_subgroupOf_iff hL,
    Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]

end Transport

variable {G : Type} [Group G] [Finite G]

theorem isPSL_two_two_of_mulEquiv {Q : Type} [Group Q] {f : ℕ} (hf : 2 ≤ f)
    (e : Q ≃* PSL(2, GaloisField 2 f)) : IsPSL 2 2 f Q := by
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, fun h => ?_, fun h => ?_⟩, GaloisField 2 f,
    inferInstance, inferInstance, hcard,
    ⟨e.trans (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL (GaloisField 2 f) 2 2 f
      (by omega) hcard).symm⟩⟩
  · have := congrArg Prod.snd h
    simp only at this
    omega
  · have := congrArg Prod.snd h
    simp only at this
    omega

theorem isSz_of_mulEquiv {Q : Type} [Group Q] {a : ℕ} (ha : 1 ≤ a) (e : Q ≃* Sz a) :
    IsSz (2 * a + 1) Q := by
  have hcard : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1) :=
    GaloisField.card 2 (2 * a + 1) (by omega)
  exact ⟨rfl, a, ha, GaloisField 2 (2 * a + 1), inferInstance, inferInstance, rfl, hcard,
    ⟨e.trans (szEquivSuzukiGroup a)⟩⟩

namespace Hyp

variable {V A : Subgroup G} (h : Hyp V A)
include h

theorem cases :
    ∃ _ : ((tiY V A).subgroupOf (tiX V A)).Normal,
      (∃ m : ℕ, Odd m ∧
          Nonempty (↥(tiX V A) ⧸ (tiY V A).subgroupOf (tiX V A) ≃* DihedralGroup m)) ∨
        (∃ n : ℕ, IsPSL 2 2 n (↥(tiX V A) ⧸ (tiY V A).subgroupOf (tiX V A))) ∨
        ∃ n : ℕ, IsSz n (↥(tiX V A) ⧸ (tiY V A).subgroupOf (tiX V A)) := by
  have hb := h.toBase
  set X := tiX V A with hXdef
  have hVX : V ≤ X := le_sup_left
  have hAX : A ≤ X := le_sup_right
  have hUX : tiU V A ≤ X := inf_le_left.trans hVX
  have hBX : tiB V A ≤ X := inf_le_left.trans hAX
  have hYX : tiY V A ≤ X := sup_le hUX hBX
  have hYn : ((tiY V A).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYX).mpr hb.tiX_le_normalizer_tiY
  refine ⟨hYn, ?_⟩
  obtain ⟨x, hxX, hxA⟩ := h.exists_conjSubgroup_eq
  have hAV : conjSubgroup V x = A := by
    rw [← hxA, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  set T : Subgroup ↥X := V.subgroupOf X with hT
  set g : ↥X := ⟨x⁻¹, X.inv_mem hxX⟩ with hg
  have hTg : CFSG.CGT.Timmesfeld75.conjSubgroup g T = A.subgroupOf X := by
    rw [hT, tconj_subgroupOf, hg]
    simp only [inv_inv]
    rw [hAV]
  have hWC : CFSG.CGT.Timmesfeld75.IsWC T := by
    refine ⟨⟨⟨⟨fun a b => Subtype.ext (Subtype.ext (hb.comm_V a.2 b.2))⟩⟩, fun y hy =>
      Subtype.ext (by simpa using hb.hV.2 _ hy)⟩, fun t ht ht1 => ⟨fun y hy => ?_,
        fun g' hg' => ?_⟩⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (hb.comm_V hy ht)
    · rw [hT, tconj_subgroupOf] at hg' ⊢
      have ht1' : (t : G) ≠ 1 := fun h1 => ht1 (Subtype.ext h1)
      have hle : conjSubgroup V (g' : G)⁻¹ ≤ Subgroup.centralizer ({(t : G)} : Set G) := by
        intro y hy
        have hyX : y ∈ X := by
          have h1 : (g' : G)⁻¹ * y * ((g' : G)⁻¹)⁻¹ ∈ V := mem_conjSubgroup_iff.mp hy
          rw [inv_inv] at h1
          rw [show y = (g' : G) * ((g' : G)⁻¹ * y * (g' : G)) * (g' : G)⁻¹ by group]
          exact X.mul_mem (X.mul_mem g'.2 (hVX h1)) (X.inv_mem g'.2)
        have := hg' (show (⟨y, hyX⟩ : ↥X) ∈ (conjSubgroup V (g' : G)⁻¹).subgroupOf X from hy)
        rw [Subgroup.mem_centralizer_singleton_iff] at this ⊢
        exact congrArg Subtype.val this
      rw [h.conjSubgroup_eq_of_le_centralizer (X.inv_mem g'.2) ht ht1' hle]
  have hne : CFSG.CGT.Timmesfeld75.conjSubgroup g T ≠ T := by
    rw [hTg, hT]
    intro heq
    rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hAX, inf_eq_left.mpr hVX] at heq
    apply h.ne
    rw [eq_bot_iff]
    intro u hu
    have : u ∈ V ⊓ A := ⟨hu.1, heq ▸ hu.1⟩
    rw [hb.inf] at this
    exact this
  have hnorm : CFSG.CGT.Timmesfeld75.normIn T (CFSG.CGT.Timmesfeld75.conjSubgroup g T) ≠ ⊥ := by
    rw [hTg, hT, normIn_subgroupOf V hAX]
    intro hbot
    rw [Subgroup.subgroupOf_eq_bot] at hbot
    exact h.ne (le_bot_iff.mp (hbot le_rfl hUX))
  obtain ⟨-, hN, hcases⟩ := CFSG.CGT.Timmesfeld75.lemma214_proved ↥X T hWC g hne hnorm
  set Tg := CFSG.CGT.Timmesfeld75.conjSubgroup g T with hTgdef
  have hsup : T ⊔ Tg = ⊤ := by
    rw [hTg, hT, ← Subgroup.subgroupOf_sup hVX hAX]
    exact Subgroup.subgroupOf_self X
  have hcfg : CFSG.CGT.Timmesfeld75.cfgM T Tg = (tiY V A).subgroupOf X := by
    rw [hTg, CFSG.CGT.Timmesfeld75.cfgM, hT, normIn_subgroupOf V hAX,
      normIn_subgroupOf A hVX, ← Subgroup.subgroupOf_sup hUX hBX]
  set e₀ : ↥(T ⊔ Tg) ≃* ↥X := (MulEquiv.subgroupCongr hsup).trans Subgroup.topEquiv with he₀
  have he₀v : ∀ w : ↥(T ⊔ Tg), e₀ w = (w : ↥X) := fun _ => rfl
  have he : ((CFSG.CGT.Timmesfeld75.cfgM T Tg).subgroupOf (T ⊔ Tg)).map e₀.toMonoidHom =
      (tiY V A).subgroupOf X := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [← hcfg]
      exact hw
    · intro hz
      refine ⟨⟨z, by rw [hsup]; exact Subgroup.mem_top z⟩, ?_, rfl⟩
      show z ∈ CFSG.CGT.Timmesfeld75.cfgM T Tg
      rw [hcfg]
      exact hz
  have E := (@QuotientGroup.congr _ _ _ _ _ _ hN hYn e₀ he).symm
  rcases hcases with ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩ | ⟨n, hn, -, ⟨e⟩⟩
  · exact Or.inr (Or.inl ⟨f, isPSL_two_two_of_mulEquiv hf (E.trans e)⟩)
  · exact Or.inr (Or.inr ⟨2 * a + 1, isSz_of_mulEquiv ha (E.trans e)⟩)
  · exact Or.inl ⟨n, hn, ⟨E.trans e⟩⟩

end Hyp

theorem as_I_6_2_twoCases_holds :
    AS_I_6_2_twoCases := by
  intro G _ _ V A hVe hAe hcard hTIV hTIA hcross hU hUlt
  have h := Hyp.mk' hVe hAe hcard hTIV hTIA hcross hU hUlt
  have hb := h.toBase
  refine ⟨⟨hb.tiU_inf_tiB, hb.commutator_tiU_tiB, hb.tiX_le_normalizer_tiY, fun v hv hvU =>
    ⟨(hb.inf_centralizer_tiY hv hvU).symm, h.tiU_eq_commutator hv hvU⟩⟩, h.cases⟩

end CFSG.Quasithin.I62

end
