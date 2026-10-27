module

public import CFSG.Quasithin.Background.AutOnPerfect
public import CFSG.Quasithin.Vol2.Ch11SecB23
public import CFSG.Quasithin.Background.B2FactorizationResidual

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA
open scoped IsMulCommutative Pointwise

section General

variable {G : Type} [Group G] [Finite G]

theorem autOn_perfectCore {A V : Subgroup G} (hA : A ≤ Subgroup.normalizer (V : Set G)) :
    autOn (perfectCore A) V = perfectCore (autOn A V) :=
  CFSG.Quasithin.AutOn.autOn_perfectCore_eq hA

theorem autOn_pCoreOf_le (A V : Subgroup G) :
    autOn (pCoreOf 2 A) V ≤ pCoreOf 2 (autOn A V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (A4.autOn_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 A)) ?_
    (B6.isPGroup_autOn (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 A) V)
  refine le_normalizer_of_forall fun a ha x hx => ?_
  obtain ⟨y, hy, hyV, rfl⟩ := mem_autOn_iff.mp ha
  obtain ⟨z, hz, hzV, rfl⟩ := mem_autOn_iff.mp hx
  rw [conjV_conj]
  exact conjV_mem_autOn ((Subgroup.mem_normalizer_iff.mp
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 A hy) z).mp hz) _

omit [Finite G] in
theorem fixV_autOn_eq {L V : Subgroup G} [IsMulCommutative ↥V]
    (hL : L ≤ Subgroup.normalizer (V : Set G)) :
    fixV (autOn L V) = (Subgroup.centralizer (L : Set G)).subgroupOf V :=
  CFSG.Quasithin.AutOn.fixV_autOn_eq hL

omit [Finite G] in
theorem commV_autOn_eq_top {L V : Subgroup G} [IsMulCommutative ↥V]
    (hL : L ≤ Subgroup.normalizer (V : Set G)) (hVL : ⁅V, L⁆ = V) :
    commV (autOn L V) = ⊤ :=
  CFSG.Quasithin.AutOn.commV_autOn_eq_top hL hVL

theorem center_SL2_eq_bot {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hn : 1 ≤ n) : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  have : Fintype K := Fintype.ofFinite K
  have h2 : (2 : K) = 0 := by
    have h0 : ((Fintype.card K : ℕ) : K) = 0 := FiniteField.cast_card_eq_zero K
    rw [Fintype.card_eq_nat_card, hK, Nat.cast_pow] at h0
    exact pow_eq_zero_iff (by omega) |>.mp h0
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hr1 : r = 1 := by
    have hr2 : r ^ 2 = 1 := by simpa using hr
    have : (r - 1) ^ 2 = 0 := by
      calc (r - 1) ^ 2 = 2 * (1 - r) + (r ^ 2 - 1) := by ring
        _ = 0 := by rw [h2, hr2]; ring
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this)
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hrA, hr1]
  simp

omit [Finite G] in
theorem inf_sectionCentralizer_le {X : Subgroup G} {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n)
    (e : ↥X ⧸ CFSG.pCore 2 ↥X ≃* Matrix.SpecialLinearGroup (Fin 2) K) :
    X ⊓ sectionCentralizer X (pCoreOf 2 X) ≤ pCoreOf 2 X := by
  intro x hx
  obtain ⟨hxX, -, -, hxc⟩ := hx
  have hN : (CFSG.pCore 2 ↥X).Normal := CFSG.pCore_normal
  have hcen : ∀ y : ↥X ⧸ CFSG.pCore 2 ↥X,
      (QuotientGroup.mk (⟨x, hxX⟩ : ↥X) : ↥X ⧸ CFSG.pCore 2 ↥X) * y =
        y * QuotientGroup.mk (⟨x, hxX⟩ : ↥X) := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H y =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      obtain ⟨z, hz, hze⟩ := hxc y y.2
      have hzmem : (⟨x, hxX⟩ * y * (⟨x, hxX⟩ : ↥X)⁻¹ * y⁻¹ : ↥X) ∈ CFSG.pCore 2 ↥X := by
        have : z = ⟨x, hxX⟩ * y * (⟨x, hxX⟩ : ↥X)⁻¹ * y⁻¹ := Subtype.ext (by simpa using hze)
        rw [← this]
        exact hz
      have h3 := hN.conj_mem _ (inv_mem hzmem) (⟨x, hxX⟩ * y)⁻¹
      have e1 : (⟨x, hxX⟩ * y)⁻¹ * (y * ⟨x, hxX⟩) =
          (⟨x, hxX⟩ * y)⁻¹ * (⟨x, hxX⟩ * y * (⟨x, hxX⟩ : ↥X)⁻¹ * y⁻¹)⁻¹ *
            (⟨x, hxX⟩ * y)⁻¹⁻¹ := by group
      rw [e1]
      exact h3
  have h1 : e (QuotientGroup.mk (⟨x, hxX⟩ : ↥X)) = 1 := by
    have hc : e (QuotientGroup.mk (⟨x, hxX⟩ : ↥X)) ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
      rw [Subgroup.mem_center_iff]
      intro B
      have := hcen (e.symm B)
      calc B * e (QuotientGroup.mk (⟨x, hxX⟩ : ↥X)) =
          e (e.symm B * QuotientGroup.mk (⟨x, hxX⟩ : ↥X)) := by simp
        _ = e (QuotientGroup.mk (⟨x, hxX⟩ : ↥X) * e.symm B) := by rw [this]
        _ = e (QuotientGroup.mk (⟨x, hxX⟩ : ↥X)) * B := by simp
    rw [center_SL2_eq_bot hK hn, Subgroup.mem_bot] at hc
    exact hc
  have h2 : (⟨x, hxX⟩ : ↥X) ∈ CFSG.pCore 2 ↥X := by
    rw [← QuotientGroup.eq_one_iff]
    exact e.injective (h1.trans (map_one e).symm)
  exact ⟨⟨x, hxX⟩, h2, rfl⟩

end General

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem par_point (hF : PointFacts) (h1102 : Stmt11_0_2) (hyp : Hyp11 G T L I n)
    {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) [IsMulCommutative ↥(fsuV T I)] :
    ParConcl (autOn L (fsuV T I)) (autOn T (fsuV T I)) (V₁.subgroupOf (fsuV T I)) := by
  obtain ⟨_, hirr, -, -, hk⟩ := h1102 G T L I n hyp
  have hsq : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (isElemAbelian_fsuV hyp).2 w w.2)
  have hn : 2 ≤ n := hyp.one_lt
  have hLV := L_le_normalizer_fsuV hyp
  have hfix := fixV_autOn_eq hLV
  have hcomm := commV_autOn_eq_top hLV hirr.2.2.2.1
  have hflag := isFlagW_of_isVi hyp hV₁
  obtain ⟨hS2, hSH, hSU⟩ := autOn_T_props hyp (IsVi.le_fsuV hV₁) (IsVi.le_normalizer hV₁)
  rcases hk with ⟨K, _, _, hK, -, π, hπ, hng⟩ | ⟨K, _, _, hK, -, π, hπ, hng⟩ |
      ⟨-, -, -, -, -, hG2⟩
  · exact hF.parSL3 K n hn hK _ hsq _ _ π hπ hfix hcomm _ (isSylowTwoOf_P hyp) _ hflag _ hS2
      hSH hSU hng
  · exact hF.parSp4 K n hn hK _ hsq _ _ π hπ hfix hcomm _ (isSylowTwoOf_P hyp) _ hflag _ hS2
      hSH hSU hng
  · obtain ⟨K, _, _, hK, π, hπ⟩ := hG2
    exact hF.parG2 K n hn hK _ hsq _ _ π hπ hfix hcomm _ (isSylowTwoOf_P hyp) _ hflag _ hS2
      hSH hSU

theorem T_le_normalizer_lOf (hyp : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) : T ≤ Subgroup.normalizer (LOf L V₁ : Set G) :=
  (B2F.le_normalizer_inf hyp.normal ((IsVi.le_normalizer hV₁).trans Subgroup.le_normalizer)).trans
    (normalizer_le_normalizer_perfectCore _)

theorem lOf_le_centralizer (hF : PointFacts) (h1102 : Stmt11_0_2) (hyp : Hyp11 G T L I n)
    {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) :
    LOf L V₁ ≤ Subgroup.centralizer (V₁ : Set G) := by
  have := (isElemAbelian_fsuV hyp).1
  have hpar := (par_point hF h1102 hyp hV₁).1
  have hle := IsVi.le_fsuV hV₁
  have hA : L ⊓ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    inf_le_left.trans (L_le_normalizer_fsuV hyp)
  rw [autOn_inf_stabW hle, ← autOn_perfectCore hA] at hpar
  intro l hl
  have hlV : l ∈ Subgroup.normalizer (fsuV T I : Set G) := hA (perfectCore_le _ hl)
  have h1 := hpar _ (conjV_mem_autOn hl hlV)
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h3 := congrArg Subtype.val (h1 ⟨v, hle hv⟩ (Subgroup.mem_subgroupOf.mpr hv))
  rw [conjV_apply_coe] at h3
  calc v * l = l * v * l⁻¹ * l := by rw [h3]
    _ = l * v := by group

theorem commutator_rOf_mem (hyp : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) {r l : G} (hr : r ∈ ROf T L V₁) (hl : l ∈ LOf L V₁) :
    r * l * r⁻¹ * l⁻¹ ∈ pCoreOf 2 (LOf L V₁) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTL := T_le_normalizer_lOf hyp hV₁
  have hLTN : LOf L V₁ ⊔ T ≤ Subgroup.normalizer (LOf L V₁ : Set G) :=
    sup_le Subgroup.le_normalizer hTL
  have hRT : ROf T L V₁ ≤ T :=
    B6.pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow
      le_sup_right)
  have hRN : LOf L V₁ ⊔ T ≤ Subgroup.normalizer (ROf T L V₁ : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hRL : ROf T L V₁ ⊓ LOf L V₁ ≤ pCoreOf 2 (LOf L V₁) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
      (B2F.le_normalizer_inf (le_sup_left.trans hRN) Subgroup.le_normalizer)
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)
  refine hRL ⟨?_, ?_⟩
  · have h1 : l * r⁻¹ * l⁻¹ ∈ ROf T L V₁ :=
      (Subgroup.mem_normalizer_iff.mp (hRN (Subgroup.mem_sup_left hl)) _).mp (inv_mem hr)
    have e : r * l * r⁻¹ * l⁻¹ = r * (l * r⁻¹ * l⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hr h1
  · have h1 : r * l * r⁻¹ ∈ LOf L V₁ :=
      (Subgroup.mem_normalizer_iff.mp (hLTN (Subgroup.mem_sup_right (hRT hr))) _).mp hl
    exact Subgroup.mul_mem _ h1 (inv_mem hl)

theorem rOf_le_centralizer (hF : PointFacts) (h1102 : Stmt11_0_2) (hyp : Hyp11 G T L I n)
    {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) :
    ROf T L V₁ ≤ Subgroup.centralizer (V₁ : Set G) := by
  have := (isElemAbelian_fsuV hyp).1
  have hpar := (par_point hF h1102 hyp hV₁).2
  have hle := IsVi.le_fsuV hV₁
  have hA : L ⊓ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    inf_le_left.trans (L_le_normalizer_fsuV hyp)
  rw [autOn_inf_stabW hle, ← autOn_perfectCore hA] at hpar
  have hRT : ROf T L V₁ ≤ T :=
    B6.pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow
      le_sup_right)
  have hLVN : LOf L V₁ ≤ Subgroup.normalizer (fsuV T I : Set G) := (perfectCore_le _).trans hA
  intro r hr
  have hrV : r ∈ Subgroup.normalizer (fsuV T I : Set G) := T_le_normalizer_fsuV T I (hRT hr)
  have h1 := hpar _ (conjV_mem_autOn (hRT hr) hrV) fun k hk => by
    obtain ⟨l, hl, hlV, rfl⟩ := mem_autOn_iff.mp hk
    rw [← conjV_inv, ← conjV_inv, ← conjV_mul, ← conjV_mul, ← conjV_mul]
    exact autOn_pCoreOf_le _ _ (conjV_mem_autOn (commutator_rOf_mem hyp hV₁ hr hl) _)
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h3 := congrArg Subtype.val (h1 ⟨v, hle hv⟩ (Subgroup.mem_subgroupOf.mpr hv))
  rw [conjV_apply_coe] at h3
  calc v * r = r * v * r⁻¹ * r := by rw [h3]
    _ = r * v := by group

end CFSG.Quasithin.Vol2.Ch11.SecB
