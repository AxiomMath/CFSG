module

public import CFSG.Quasithin.Background.E6EightMarkedRoots
public import CFSG.Quasithin.Background.E6TwentyFiveStmt
public import CFSG.Milestones.ASVolI.E2
public import CFSG.Quasithin.Background.VolIE54
public import CFSG.Quasithin.Background.E6Fourteen
public import CFSG.Quasithin.Background.E6ThreeOpenHeX
public import CFSG.Quasithin.Background.E6TwentyThreePG
public import CFSG.Quasithin.Background.E6ParabolicTorus
public import CFSG.Quasithin.Background.RonanE628RTorus
import CFSG.Quasithin.Background.RonanE628RMain
import CFSG.Quasithin.Background.RonanE628RBorel
public import CFSG.Quasithin.Background.Asc81cPfMain
public import CFSG.Quasithin.Vol2.Ch3Sec3Frontier
public import CFSG.Quasithin.Background.E6TwelveProved
public import CFSG.Quasithin.H13.NQCatKG68All
public import CFSG.LocalAnalysis.SectionRank.QTK.Basic
public import CFSG.Quasithin.Background.E6Ten
import CFSG.Quasithin.Background.RonanE611Main
import CFSG.Quasithin.Background.RonanE68Main

public section

open scoped Pointwise commutatorElement

namespace CFSG.ASVolI

namespace ChE

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Lemma68

variable {G : Type} [Group G]

@[expose] def autSubInduced (L X : Subgroup G) : Subgroup (MulAut ↥L) where
  carrier := {α | ∃ g ∈ X ⊓ Subgroup.normalizer (L : Set G),
    ∀ x : ↥L, ((α x : ↥L) : G) = g * (x : G) * g⁻¹}
  one_mem' := ⟨1, Subgroup.one_mem _, fun x => by simp⟩
  mul_mem' := by
    rintro α β ⟨g, hg, hα⟩ ⟨h, hh, hβ⟩
    refine ⟨g * h, Subgroup.mul_mem _ hg hh, fun x => ?_⟩
    rw [MulAut.mul_apply, hα, hβ]
    group
  inv_mem' := by
    rintro α ⟨g, hg, hα⟩
    refine ⟨g⁻¹, Subgroup.inv_mem _ hg, fun x => ?_⟩
    have h1 : ((α (α⁻¹ x) : ↥L) : G) = (x : G) := by simp
    rw [hα] at h1
    have h2 : (((α⁻¹ x : ↥L)) : G) = g⁻¹ * (x : G) * g := by
      calc (((α⁻¹ x : ↥L)) : G) = g⁻¹ * (g * ((α⁻¹ x : ↥L) : G) * g⁻¹) * g := by group
        _ = g⁻¹ * (x : G) * g := by rw [h1]
    rw [h2]
    simp

@[expose] def E68Case1P {V : Subgroup G} (hV : CFSG.Open.IsElemAbelian 2 V) (T M U L : Subgroup G) :
    Prop :=
  ∃ n : ℕ,
    ((2 ≤ n ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSL 2 2 n) ∨
      (Odd n ∧ 3 ≤ n ∧ CFSG.Blueprint.SuzukiModel ↥L 2 n) ∨
      (1 ≤ n ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSL 3 2 n) ∨
      (2 ≤ n ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSU 3 2 n) ∨
      (n = 2 ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 2 ∧
        IsPGroup 2 (Subgroup.center ↥L))) ∧
    L ⊓ M = L ⊓ Subgroup.normalizer (((T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L : Subgroup G) :
      Set G) ∧
    IsCyclic (autI hV (L ⊓ M)) ∧ Nat.card (autI hV (L ⊓ M)) = 2 ^ n - 1 ∧
    E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = n ∧
    E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) ≤ E3.mQuot V U ∧
    (1 < n → ⁅V, L ⊓ M⁆ ⊓ (V ⊓ Subgroup.centralizer (L : Set G)) = ⊥ ∧
      ⁅V, L ⊓ M⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)) = V ∧ E3.mQuot ⁅V, L ⊓ M⁆ ⊥ = n)

@[expose] def E68Case2P (T M V U L : Subgroup G) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧
    ((2 ≤ n ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSp 2 2 n) ∨
      (n = 1 ∧ Nonempty (↥L ≃* alternatingGroup (Fin 6)))) ∧
    E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) ≤ E3.mQuot V U ∧
    (1 < n → ⁅V, L ⊓ M⁆ ⊓ (V ⊓ Subgroup.centralizer (L : Set G)) = ⊥ ∧
      ⁅V, L ⊓ M⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)) = V) ∧
    ((L ⊓ M = L ⊓ Subgroup.normalizer (((T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L : Subgroup G) :
        Set G) ∧
      ((E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = 2 * n ∧
          ∃ A : Subgroup G, U < A ∧ A < V ∧ E3.mQuot V A = n ∧
            ¬ L ⊓ Subgroup.centralizer (A : Set G) ≤ M) ∨
        (n = 1 ∧ E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = 1))) ∨
     (L ⊓ Subgroup.normalizer (((T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L : Subgroup G) :
        Set G) ≤ L ⊓ M ∧ L ⊓ M < L ∧
      (∀ K : Subgroup G, L ⊓ M ≤ K → K ≤ L → K = L ⊓ M ∨ K = L) ∧
      E6.IsMarkedSp4Root n (autSubInduced L (L ⊔ V)) (autSubInduced L V) ∧
      E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = n))

@[expose] def E68EqualityScope (M V U : Subgroup G) : Prop :=
  E3.mQuot V U = 1 ∨
    ∀ W : Subgroup G, W ∈ E6.gammaE64 V M → U ≤ W → W = U

@[expose] def E68Case3P (T M V U L : Subgroup G) : Prop :=
  CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSL 4 2 1 ∧
    Nonempty ((↥(L ⊔ (T ⊓ Subgroup.centralizer (V : Set G))) ⧸
      CFSG.pCore 2 ↥(L ⊔ (T ⊓ Subgroup.centralizer (V : Set G)))) ≃* Equiv.Perm (Fin 8)) ∧
    U ≤ V ⊓ Subgroup.centralizer (L : Set G) ∧
    (E68EqualityScope M V U → U = V ⊓ Subgroup.centralizer (L : Set G)) ∧
    E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = 1 ∧ E3.rParam V = 1

@[expose] def E68Case5P (M V U L : Subgroup G) : Prop :=
  ((∃ p : ℕ, CFSG.QuasithinUnique.Ch1.IsFermatOrMersennePrime p ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSL 2 p 1) ∨
    CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSL 3 3 1 ∨
      Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)) ∧
    U ≤ V ⊓ Subgroup.centralizer (L : Set G) ∧
    (E68EqualityScope M V U → U = V ⊓ Subgroup.centralizer (L : Set G)) ∧
    E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = 1 ∧ E3.rParam V = 1

end Lemma68

end ChE

open ChE CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.E1 CFSG.QuasithinUnique

@[expose] def E_6_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V : Subgroup G), E6.HypE61 T M V →
    ∀ L : Subgroup G, ¬ L ≤ M → ⁅V, L⁆ ≠ ⊥

set_option linter.unusedVariables false in
theorem as_E_6_2 : E_6_2 := fun G _ _ T M V h L hL => E6.e6_2 h hL

@[expose] def E_6_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V : Subgroup G) (h : E6.HypE61 T M V),
    2 < mParam (autI h.isElemAbelian M) →
      (mParam (autI h.isElemAbelian M) : ℕ∞) ≤ rParam V ∧
        sParam h.isElemAbelian = mParam (autI h.isElemAbelian M) ∧ 2 < sParam h.isElemAbelian

section

theorem as_E_6_3
    : E_6_3 := by
  intro G _ _ T M V h h2
  have hA := CFSG.Quasithin.E6.as_E_6_3_of_thm104_insp CFSG.Quasithin.Asc81c.Pf.thm104
    CFSG.Quasithin.E6.e623A6Insp_holds G T M V h.isElemAbelian h h2
  exact ⟨hA.1, hA.2, by rw [hA.2]; exact h2⟩

end

@[expose] def E_6_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V : Subgroup G) (h : E6.HypE61 T M V),
    (∀ U : Subgroup G, U ≤ V → U ≠ ⊥ →
      M ⊓ Subgroup.centralizer (U : Set G) ≤ M ⊓ Subgroup.normalizer (V : Set G)) ∧
    (∀ U : Subgroup G, U ≤ V → U ≠ ⊥ →
      (twoPrimeResidual (M ⊓ Subgroup.centralizer (U : Set G)) ≤
          M ⊓ Subgroup.centralizer (V : Set G) ↔
        Odd (Nat.card (autI h.isElemAbelian (M ⊓ Subgroup.centralizer (U : Set G)))))) ∧
    (∃ U : Subgroup G, U ≤ V ∧ (mQuot V U : ℕ∞) = rParam V ∧
        ¬ Subgroup.centralizer (U : Set G) ≤ M) ∧
    (∀ U : Subgroup G, U ≤ V → (mQuot V U : ℕ∞) = rParam V →
      ¬ Subgroup.centralizer (U : Set G) ≤ M →
      rParam V < (mParam (autI h.isElemAbelian M) : ℕ∞) → U ∈ E6.gammaE64 V M)

theorem as_E_6_4 : E_6_4 := by
  intro G _ _ T M V h
  have hNV : Subgroup.normalizer (V : Set G) ≠ ⊤ := by
    intro htop
    haveI : V.Normal := Subgroup.normalizer_eq_top_iff.1 htop
    rcases h.simple.eq_bot_or_eq_top_of_normal V with hb | ht
    · exact h.ne_bot hb
    · obtain ⟨a, b, hab⟩ := h.nonabelian
      apply hab
      have ha : a ∈ V := by rw [ht]; exact Subgroup.mem_top a
      have hb : b ∈ V := by rw [ht]; exact Subgroup.mem_top b
      exact congrArg Subtype.val (h.isElemAbelian.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hCbot : (⊤ : Subgroup G) ≤ Subgroup.centralizer ((⊥ : Subgroup G) : Set G) := fun g _ =>
    Subgroup.mem_centralizer_iff.2 fun x hx => by
      rw [Subgroup.mem_bot.1 (SetLike.mem_coe.1 hx), one_mul, mul_one]
  have hCbotN : ¬ Subgroup.centralizer ((⊥ : Subgroup G) : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    fun hle => hNV (top_le_iff.1 (hCbot.trans hle))
  have hMtop : M ≠ ⊤ := by
    intro htop
    obtain ⟨P, hP1, hP2, hPM⟩ := h.inM.1.1
    haveI : P.Normal := Subgroup.normalizer_eq_top_iff.1 (hPM.symm.trans htop)
    rcases h.simple.eq_bot_or_eq_top_of_normal P with hb | ht
    · exact hP1 hb
    · have hG2 : IsPGroup 2 (⊤ : Subgroup G) := ht ▸ hP2
      obtain ⟨n, hn⟩ := B6.exists_relIndex_eq_two_pow_of_isPGroup hG2 T
      have hT1 : T.relIndex ⊤ = 1 := by
        rcases Nat.eq_zero_or_pos n with hn0 | hnpos
        · rw [hn, hn0, pow_zero]
        · have h2 : 2 ∣ T.relIndex ⊤ := by
            rw [hn]
            exact dvd_pow_self 2 hnpos.ne'
          exact absurd h2 h.isSylowIn_top.2.2
      exact hNV (top_le_iff.1 ((Subgroup.relIndex_eq_one.1 hT1).trans h.normal))
  refine ⟨fun U hUV hU1 => le_inf inf_le_left (E6.inf_centralizer_le_normalizer h hUV hU1),
    fun U hUV hU1 => ?_, ?_, fun U hUV hr hC hlt => ?_⟩
  ·
    have hXN := E6.inf_centralizer_le_normalizer h hUV hU1
    constructor
    · intro hres
      exact E6.E68Proof.odd_card_autI h.isElemAbelian hXN (hres.trans inf_le_right)
    · intro hodd
      rw [CFSG.Quasithin.card_autI_eq h.isElemAbelian hXN] at hodd
      have hnd : ¬ 2 ∣ ((M ⊓ Subgroup.centralizer (U : Set G)) ⊓
          Subgroup.centralizer (V : Set G)).relIndex (M ⊓ Subgroup.centralizer (U : Set G)) := by
        rintro ⟨c, hc⟩
        obtain ⟨m, hm⟩ := hodd
        omega
      have hNorm : M ⊓ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer
          (((M ⊓ Subgroup.centralizer (U : Set G)) ⊓ Subgroup.centralizer (V : Set G) :
            Subgroup G) : Set G) :=
        B2F.le_normalizer_inf Subgroup.le_normalizer (B2F.le_normalizer_centralizer hXN)
      exact (iInf₂_le ((M ⊓ Subgroup.centralizer (U : Set G)) ⊓
        Subgroup.centralizer (V : Set G)) ⟨inf_le_left, hNorm, hnd⟩).trans
        (inf_le_inf_right _ inf_le_left)
  ·
    have hrne : E3.rParam V ≠ ⊤ := by
      intro htop
      have hle := E6.rParam_le_mQuot (bot_le : (⊥ : Subgroup G) ≤ V) hCbotN
      rw [htop] at hle
      exact ENat.natCast_ne_top _ (top_le_iff.1 hle)
    obtain ⟨U, hUV, hCN, hUr⟩ := E6.exists_eq_rParam' hrne
    by_cases hU1 : U = ⊥
    · subst hU1
      exact ⟨⊥, bot_le, hUr, fun hle => hMtop (top_le_iff.1 (hCbot.trans hle))⟩
    · exact ⟨U, hUV, hUr, fun hCM =>
        hCN fun g hg => E6.inf_centralizer_le_normalizer h hUV hU1 ⟨hCM hg, hg⟩⟩
  ·
    have hU1 : U ≠ ⊥ := by
      rintro rfl
      have h1 := E6.mQuot_bot_eq_rk h.isElemAbelian
      have h2 := E3.mParam_le_rk (autI h.isElemAbelian M)
      have h3 : E3.mQuot V ⊥ < E3.mParam (autI h.isElemAbelian M) := by
        have h4 : (E3.mQuot V ⊥ : ℕ∞) < (E3.mParam (autI h.isElemAbelian M) : ℕ∞) := by
          rw [hr]
          exact hlt
        exact_mod_cast h4
      omega
    have hlt' : E3.mQuot V U < E3.mParam (autI h.isElemAbelian M) := by
      have h4 : (E3.mQuot V U : ℕ∞) < (E3.mParam (autI h.isElemAbelian M) : ℕ∞) := by
        rw [hr]
        exact hlt
      exact_mod_cast h4
    exact E6.mem_gammaE64_of_mQuot_lt h.isElemAbelian h hUV hU1 hC hlt'

@[expose] def E_6_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V : Subgroup G), E6.HypE61 T M V →
    ∀ U ∈ E6.gammaE64 V M,
      IsSylowIn 2 (T ⊓ Subgroup.centralizer (V : Set G)) (Subgroup.centralizer (U : Set G)) ∧
      (cgsIn (Subgroup.centralizer (U : Set G)) (T ⊓ Subgroup.centralizer (V : Set G)) ≤
          Subgroup.centralizer (U : Set G) ⊓ M ∧
        Subgroup.centralizer (U : Set G) ⊓ M < Subgroup.centralizer (U : Set G)) ∧
      (V ≤ Subgroup.centralizer (U : Set G) ⊓ M ∧
        Subgroup.centralizer (U : Set G) ⊓ M ≤ Subgroup.normalizer (V : Set G))

set_option linter.unusedVariables false in
theorem as_E_6_5 : E_6_5 := fun G _ _ T M V h U hU =>
  ⟨E6.e6_5_one h hU, E6.e6_5_two h hU, E6.e6_5_three h hU⟩

@[expose] def E_6_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V : Subgroup G), E6.HypE61 T M V →
    (∀ U ∈ E6.gammaE64 V M, CharTwo (Subgroup.centralizer (U : Set G) ⊓ M)) ∧
    (∀ A : Subgroup G, A ≤ M → IsPGroup 2 A → A ≠ ⊥ →
      CharTwo (M ⊓ Subgroup.centralizer (A : Set G))) ∧
    (∀ U ∈ E6.gammaE64 V M, ∀ z : G, z ∈ V ⊓ Subgroup.centralizer (T : Set G) → z ≠ 1 →
      CharTwo (Subgroup.centralizer (U : Set G) ⊓ Subgroup.centralizer ({z} : Set G)) ∧
        pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ⊓
            Subgroup.centralizer (pCoreOf 2 (Subgroup.centralizer (U : Set G) ⊓
              Subgroup.centralizer ({z} : Set G)) : Set G) ≤
          pCoreOf 2 (Subgroup.centralizer (U : Set G) ⊓ Subgroup.centralizer ({z} : Set G))) ∧
    (∀ U ∈ E6.gammaE64 V M, U ⊓ (V ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥ →
      CharTwo (Subgroup.centralizer (U : Set G)))

private theorem shultE6_centralizer_singleton {G : Type} [Group G] (z : G) :
    Subgroup.centralizer ({z} : Set G) =
      Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
  ext g
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hg x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 (SetLike.mem_coe.1 hx)
    exact (show Commute z g from hg z (Set.mem_singleton z)).zpow_left n
  · intro hg x hx
    rw [Set.mem_singleton_iff.1 hx]
    exact hg z (SetLike.mem_coe.2 (Subgroup.mem_zpowers z))

theorem as_E_6_6 : E_6_6 := by
  intro G _ _ T M V h
  refine ⟨fun U hU => ?_, fun A hAM hA _ => E6.e6_6_two h hAM hA, fun U hU z hz hz1 => ?_,
    fun U hU hUZ => ?_⟩
  · rw [inf_comm]
    exact E6.e6_6_one h hU.1
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hzV : z ∈ V := hz.1
    have hzC : z ∈ Subgroup.centralizer (T : Set G) := hz.2
    have hUV : U ≤ V := hU.1
    have hU2 : IsPGroup 2 U := h.isPGroup_V.to_le hUV
    have hzpV : Subgroup.zpowers z ≤ V := Subgroup.zpowers_le.2 hzV
    have hzp2 : IsPGroup 2 (Subgroup.zpowers z) := h.isPGroup_V.to_le hzpV
    rw [shultE6_centralizer_singleton z]
    set Z := Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) with hZdef
    have hT2 : IsSylowTwoOf T ⊤ :=
      ⟨le_top, h.sylow.1, by rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]; exact h.sylow.2⟩
    have hZ' : Subgroup.zpowers z ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥ := by
      intro h0
      have hm : z ∈ Subgroup.zpowers z ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) :=
        ⟨Subgroup.mem_zpowers z, h.le hzV, hzC⟩
      rw [h0, Subgroup.mem_bot] at hm
      exact hz1 hm
    have hN := CT.charTwo_normalizer_of_inf_center h.qtke.2.1 hT2 hzp2 hZ'
    have hZch : CharTwo Z := by
      have hc := CT.CharTwo.inf_centralizer hN Subgroup.le_normalizer hzp2
      rwa [inf_eq_right.2 (Subgroup.centralizer_le_normalizer _)] at hc
    have hUZ : U ≤ Z := fun u hu => Subgroup.mem_centralizer_iff.2 fun x hx =>
      B2F.isElemAbelian_comm h.isElemAbelian (hzpV (SetLike.mem_coe.1 hx)) (hUV hu)
    have hUC : U ≤ Subgroup.centralizer (U : Set G) := fun u hu =>
      Subgroup.mem_centralizer_iff.2 fun x hx =>
        B2F.isElemAbelian_comm h.isElemAbelian (hUV hx) (hUV hu)
    have hKch : CharTwo (Subgroup.centralizer (U : Set G) ⊓ Z) := by
      have hc := CT.CharTwo.inf_centralizer hZch hUZ hU2
      rw [inf_comm]
      exact hc
    refine ⟨hKch, ?_⟩
    set K := Subgroup.centralizer (U : Set G) ⊓ Z with hKdef
    have hKZ : K ≤ Z := inf_le_right
    have hKN : K ≤ Subgroup.normalizer (U : Set G) :=
      inf_le_left.trans (Subgroup.centralizer_le_normalizer _)
    have hUK : U ≤ K := le_inf hUC hUZ
    have hUR : U ≤ pCoreOf 2 K :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hUK hKN hU2
    have hXZ : Z ≤ Subgroup.normalizer ((pCoreOf 2 Z : Subgroup G) : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Z
    have hRK : K ≤ Subgroup.normalizer ((pCoreOf 2 K : Subgroup G) : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
    have hWC : pCoreOf 2 Z ⊓ Subgroup.centralizer ((pCoreOf 2 K : Subgroup G) : Set G) ≤
        Subgroup.centralizer (U : Set G) := by
      intro w hw
      exact Subgroup.mem_centralizer_iff.2 fun u hu =>
        Subgroup.mem_centralizer_iff.1 hw.2 u (hUR hu)
    have hWZ : pCoreOf 2 Z ⊓ Subgroup.centralizer ((pCoreOf 2 K : Subgroup G) : Set G) ≤ Z :=
      inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 Z)
    have hWK : pCoreOf 2 Z ⊓ Subgroup.centralizer ((pCoreOf 2 K : Subgroup G) : Set G) ≤ K :=
      le_inf hWC hWZ
    have hWn : ((pCoreOf 2 Z ⊓ Subgroup.centralizer ((pCoreOf 2 K : Subgroup G) : Set G) :
        Subgroup G).subgroupOf K).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have hk : (g : G) ∈ K := g.2
      have hkN : (g : G) ∈ Subgroup.normalizer ((pCoreOf 2 Z : Subgroup G) : Set G) :=
        hXZ (hKZ hk)
      have hkR : (g : G) ∈ Subgroup.normalizer ((pCoreOf 2 K : Subgroup G) : Set G) :=
        hRK hk
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.1 hkN _).1 hn.1
      · refine Subgroup.mem_centralizer_iff.2 fun r hr => ?_
        have hr' : (g : G)⁻¹ * r * (g : G) ∈ pCoreOf 2 K := by
          refine (Subgroup.mem_normalizer_iff.1 hkR _).2 ?_
          have e : (g : G) * ((g : G)⁻¹ * r * (g : G)) * (g : G)⁻¹ = r := by group
          rw [e]
          exact hr
        have hw := Subgroup.mem_centralizer_iff.1 hn.2 _ hr'
        calc r * ((g : G) * (n : G) * (g : G)⁻¹)
            = (g : G) * (((g : G)⁻¹ * r * (g : G)) * (n : G)) * (g : G)⁻¹ := by group
          _ = (g : G) * ((n : G) * ((g : G)⁻¹ * r * (g : G))) * (g : G)⁻¹ := by rw [hw]
          _ = ((g : G) * (n : G) * (g : G)⁻¹) * r := by group
    have hW2 : IsPGroup 2 ↥(pCoreOf 2 Z ⊓
        Subgroup.centralizer ((pCoreOf 2 K : Subgroup G) : Set G)) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Z).to_le inf_le_left
    exact CFSG.LieType.BorelTits.le_pCoreOf 2 hWK hWn hW2
  · exact E6.as_E_6_6_four_proved G T M V U h ⟨hU.2.1, hU.1, hU.2.2.1, hU.2.2.2⟩ hUZ

@[expose] def E_6_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V : Subgroup G), E6.HypE61 T M V →
    ∀ U ∈ E6.gammaE64 V M, ∀ K : Subgroup G, T ⊓ Subgroup.centralizer (V : Set G) ≤ K →
      K ≤ Subgroup.centralizer (U : Set G) → CharTwo K →
      ∃ (s : ℕ) (Ls : Fin s → Subgroup G), s ≤ 2 ∧
        (∀ i, IsChi0Block K (Ls i)) ∧ (∀ i j, i ≠ j → ⁅Ls i, Ls j⁆ = ⊥) ∧
        (∀ i, Ls i = ⁅Ls i, thompsonJ (T ⊓ Subgroup.centralizer (V : Set G))⁆) ∧
        ((K ⊓ M : Subgroup G) : Set G) * ((⨆ i, Ls i : Subgroup G) : Set G) = (K : Set G) ∧
        (∀ i, (IsAltType (Ls i) 3 → E3.mQuot V (V ⊓ Subgroup.centralizer (Ls i : Set G)) = 1 ∧
            M.relIndex (Ls i) = 3 ∧ rParam V = 1) ∧
          (IsAltType (Ls i) 5 → E3.mQuot V (V ⊓ Subgroup.centralizer (Ls i : Set G)) = 1 ∧
            M.relIndex (Ls i) = 5 ∧ rParam V = 1)) ∧
        (∀ i (n : ℕ), 1 < n → IsLin2Type (Ls i) n →
          ∃ X : Subgroup G, X ≤ Ls i ⊓ M ∧ IsCyclic X ∧ Nat.card X = 2 ^ n - 1 ∧
            (V ⊓ Subgroup.centralizer (Ls i : Set G)) ⊓ ⁅V, X⁆ = ⊥ ∧
            (V ⊓ Subgroup.centralizer (Ls i : Set G)) ⊔ ⁅V, X⁆ = V ∧
            E3.mQuot ⁅V, X⁆ ⊥ = n ∧
            Ls i ⊓ M = (((Ls i ⊓ (T ⊓ Subgroup.centralizer (V : Set G)) : Subgroup G) : Set G) *
              (X : Set G) : Set G) ∧
            E2.IsBorelIn (⊤ : Subgroup (↥(Ls i) ⧸ CFSG.pCore 2 ↥(Ls i)))
              (((M ⊓ Ls i).subgroupOf (Ls i)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(Ls i)))) ∧
            n ≤ E3.mQuot V U)

section ShultE67

private theorem shultE67_mem_sup {G : Type} [Group G] {H K : Subgroup G}
    (hHK : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {z : G} (hz : z ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, z = h * k := by
  let P : Subgroup G :=
    { carrier := {z | ∃ h ∈ H, ∃ k ∈ K, z = h * k}
      mul_mem' := by
        rintro _ _ ⟨h₁, h₁H, k₁, k₁K, rfl⟩ ⟨h₂, h₂H, k₂, k₂K, rfl⟩
        refine ⟨h₁ * h₂, H.mul_mem h₁H h₂H, k₁ * k₂, K.mul_mem k₁K k₂K, ?_⟩
        calc h₁ * k₁ * (h₂ * k₂) = h₁ * (k₁ * h₂) * k₂ := by group
          _ = h₁ * (h₂ * k₁) * k₂ := by rw [← hHK h₂ h₂H k₁ k₁K]
          _ = h₁ * h₂ * (k₁ * k₂) := by group
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨h, hh, k, hk, rfl⟩
        refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
        rw [mul_inv_rev]
        exact (hHK h⁻¹ (H.inv_mem hh) k⁻¹ (K.inv_mem hk)).symm }
  have hHP : H ≤ P := fun h hh => ⟨h, hh, 1, K.one_mem, (mul_one h).symm⟩
  have hKP : K ≤ P := fun k hk => ⟨1, H.one_mem, k, hk, (one_mul k).symm⟩
  have hzP : z ∈ P := sup_le hHP hKP hz
  obtain ⟨h, hh, k, hk, hzk⟩ := hzP
  exact ⟨h, hh, k, hk, hzk⟩

private theorem shultE67_absorb {G : Type} [Group G] {A H K : Subgroup G} (hHA : H ≤ A)
    (hHK : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) :
    (A : Set G) * ((H ⊔ K : Subgroup G) : Set G) = (A : Set G) * (K : Set G) := by
  ext z
  constructor
  · rintro ⟨a, ha, w, hw, rfl⟩
    obtain ⟨h, hh, k, hk, rfl⟩ := shultE67_mem_sup hHK hw
    exact ⟨a * h, A.mul_mem ha (hHA hh), k, hk, mul_assoc a h k⟩
  · rintro ⟨a, ha, k, hk, rfl⟩
    exact ⟨a, ha, k, Subgroup.mem_sup_right hk, rfl⟩

private theorem shultE67_mul_of_le {G : Type} [Group G] {A B : Subgroup G} (hBA : B ≤ A) :
    (A : Set G) * (B : Set G) = (A : Set G) := by
  ext z
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact A.mul_mem ha (hBA hb)
  · intro hz
    exact ⟨z, hz, 1, B.one_mem, mul_one z⟩

private theorem shultE67_mul_bot {G : Type} [Group G] (A : Subgroup G) :
    (A : Set G) * ((⊥ : Subgroup G) : Set G) = (A : Set G) := by
  ext z
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hb
    rw [hb]
    simpa using ha
  · intro hz
    exact ⟨z, hz, 1, Subgroup.one_mem (⊥ : Subgroup G), mul_one z⟩

private theorem shultE67_iSup_fin_two {G : Type} [Group G] (L : Fin 2 → Subgroup G) :
    (⨆ i, L i) = L 0 ⊔ L 1 := by
  refine le_antisymm (iSup_le fun i => ?_) (sup_le (le_iSup L 0) (le_iSup L 1))
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

private theorem shultE67_comm_of_bot {G : Type} [Group G] {A B : Subgroup G}
    (h : ⁅A, B⁆ = ⊥) : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  intro a ha b hb
  have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h ha
  exact (Subgroup.mem_centralizer_iff.1 hc b hb).symm

private theorem shultE67_prune {G : Type} [Group G] {K M : Subgroup G} {r : ℕ} (hr : r ≤ 2)
    {Lb : Fin r → Subgroup G} (hLK : ∀ i, Lb i ≤ K)
    (hcomm : ∀ i j, i ≠ j → Lb i ≠ Lb j → ⁅Lb i, Lb j⁆ = ⊥)
    (hset : (K : Set G) = ((K ⊓ M : Subgroup G) : Set G) * ((⨆ i, Lb i : Subgroup G) : Set G)) :
    ∃ (s : ℕ) (Ls : Fin s → Subgroup G), s ≤ 2 ∧
      (∀ i, ¬ Ls i ≤ M ∧ ∃ j, Ls i = Lb j) ∧
      (∀ i j, i ≠ j → ⁅Ls i, Ls j⁆ = ⊥) ∧
      (K : Set G) = ((K ⊓ M : Subgroup G) : Set G) * ((⨆ i, Ls i : Subgroup G) : Set G) := by
  interval_cases r
  · exact ⟨0, Lb, by norm_num, fun i => i.elim0, fun i => i.elim0, hset⟩
  · by_cases h0 : Lb 0 ≤ M
    · refine ⟨0, fun i => i.elim0, by norm_num, fun i => i.elim0, fun i => i.elim0, ?_⟩
      have hA : Lb 0 ≤ K ⊓ M := le_inf (hLK 0) h0
      have h1 : (⨆ i, Lb i : Subgroup G) = Lb 0 :=
        le_antisymm (iSup_le fun i => le_of_eq (congrArg Lb (Subsingleton.elim i 0)))
          (le_iSup Lb 0)
      rw [h1, shultE67_mul_of_le hA] at hset
      rw [iSup_of_empty, shultE67_mul_bot]
      exact hset
    · refine ⟨1, Lb, by norm_num, fun i => ⟨?_, i, rfl⟩,
        fun i j hij => absurd (Subsingleton.elim i j) hij, hset⟩
      have hi : i = 0 := Subsingleton.elim i 0
      rw [hi]
      exact h0
  · by_cases e : Lb 0 = Lb 1
    · have h1 : (⨆ i, Lb i : Subgroup G) = Lb 0 := by
        rw [shultE67_iSup_fin_two, e, sup_idem]
      by_cases h0 : Lb 0 ≤ M
      · refine ⟨0, fun i => i.elim0, by norm_num, fun i => i.elim0, fun i => i.elim0, ?_⟩
        have hA : Lb 0 ≤ K ⊓ M := le_inf (hLK 0) h0
        rw [h1, shultE67_mul_of_le hA] at hset
        rw [iSup_of_empty, shultE67_mul_bot]
        exact hset
      · refine ⟨1, fun _ => Lb 0, by norm_num, fun _ => ⟨h0, 0, rfl⟩,
          fun i j hij => absurd (Subsingleton.elim i j) hij, ?_⟩
        rw [iSup_const]
        rw [h1] at hset
        exact hset
    · rcases em (Lb 0 ≤ M) with h0 | h0 <;> rcases em (Lb 1 ≤ M) with h1 | h1
      · refine ⟨0, fun i => i.elim0, by norm_num, fun i => i.elim0, fun i => i.elim0, ?_⟩
        have hA : Lb 0 ⊔ Lb 1 ≤ K ⊓ M := sup_le (le_inf (hLK 0) h0) (le_inf (hLK 1) h1)
        rw [shultE67_iSup_fin_two, shultE67_mul_of_le hA] at hset
        rw [iSup_of_empty, shultE67_mul_bot]
        exact hset
      · refine ⟨1, fun _ => Lb 1, by norm_num, fun _ => ⟨h1, 1, rfl⟩,
          fun i j hij => absurd (Subsingleton.elim i j) hij, ?_⟩
        have hA0 : Lb 0 ≤ K ⊓ M := le_inf (hLK 0) h0
        have hc01 : ∀ a ∈ Lb 0, ∀ b ∈ Lb 1, a * b = b * a :=
          shultE67_comm_of_bot (hcomm 0 1 (by decide) e)
        rw [shultE67_iSup_fin_two, shultE67_absorb hA0 hc01] at hset
        rw [iSup_const]
        exact hset
      · refine ⟨1, fun _ => Lb 0, by norm_num, fun _ => ⟨h0, 0, rfl⟩,
          fun i j hij => absurd (Subsingleton.elim i j) hij, ?_⟩
        have hA1 : Lb 1 ≤ K ⊓ M := le_inf (hLK 1) h1
        have hc10 : ∀ a ∈ Lb 1, ∀ b ∈ Lb 0, a * b = b * a :=
          shultE67_comm_of_bot (hcomm 1 0 (by decide) (Ne.symm e))
        rw [shultE67_iSup_fin_two, sup_comm, shultE67_absorb hA1 hc10] at hset
        rw [iSup_const]
        exact hset
      · refine ⟨2, Lb, le_refl 2, fun i => ⟨by fin_cases i <;> assumption, i, rfl⟩, ?_, hset⟩
        intro i j hij
        fin_cases i <;> fin_cases j
        · exact absurd rfl hij
        · exact hcomm 0 1 (by decide) e
        · exact hcomm 1 0 (by decide) (Ne.symm e)
        · exact absurd rfl hij

private theorem shultE67_mQuot_one {G : Type} [Group G] [Finite G] {V U' : Subgroup G}
    (hV : IsPGroup 2 V) (hU'V : U' ≤ V) (hne : U' ≠ V) (hle : U'.relIndex V ≤ 2) :
    E3.mQuot V U' = 1 := by
  have hpow := E3.relIndex_eq_two_pow hV U'
  have hm0 : E3.mQuot V U' ≠ 0 := fun h0 => hne ((E3.mQuot_eq_zero_iff hV hU'V).1 h0)
  rw [hpow] at hle
  have hm1 : E3.mQuot V U' < 2 := by
    by_contra hc
    push Not at hc
    have h4 : 4 ≤ 2 ^ E3.mQuot V U' := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ E3.mQuot V U' := Nat.pow_le_pow_right (by norm_num) hc
    omega
  omega

private theorem shultE67_rParam_one {G : Type} [Group G] [Finite G] {T M V L W : Subgroup G}
    (h : E6.HypE61 T M V) (hLM : ¬ L ≤ M) (hWV : W ≤ V)
    (hLW : L ≤ Subgroup.centralizer (W : Set G)) (hm : E3.mQuot V W = 1) :
    E3.rParam V = 1 := by
  have hC : ¬ Subgroup.centralizer (W : Set G) ≤ Subgroup.normalizer (V : Set G) := fun hc =>
    hLM (hLW.trans (hc.trans h.normalizer_le))
  have h1 := E6.rParam_le_mQuot hWV hC
  rw [hm, Nat.cast_one] at h1
  exact le_antisymm h1 (E6.one_le_rParam h)

private theorem shultE67_altcard {G : Type} [Group G] {L : Subgroup G} {m : ℕ}
    (h : IsAltType L m) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = Nat.card (alternatingGroup (Fin m)) := by
  obtain ⟨α, hα, hker, -⟩ := h
  rw [← hker]
  exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv

private theorem shultE67_card_alt3 : Nat.card (alternatingGroup (Fin 3)) = 3 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.factorial]

private theorem shultE67_card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.factorial]

private theorem shultE67_normalizer_map {X Y : Type} [Group X] [Group Y] {f : X →* Y}
    (hf : Function.Surjective f) {S : Subgroup X} (hk : f.ker ≤ S) (g : X) :
    f g ∈ Subgroup.normalizer ((S.map f : Subgroup Y) : Set Y) ↔
      g ∈ Subgroup.normalizer (S : Set X) := by
  have hmem : ∀ x : X, f x ∈ S.map f ↔ x ∈ S := by
    intro x
    constructor
    · rintro ⟨t, ht, hte⟩
      have hker : t⁻¹ * x ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hte, inv_mul_cancel]
      have := S.mul_mem ht (hk hker)
      simpa using this
    · intro hx
      exact Subgroup.mem_map_of_mem f hx
  have fwd : ∀ g' : X, f g' ∈ Subgroup.normalizer ((S.map f : Subgroup Y) : Set Y) →
      ∀ s ∈ S, g' * s * g'⁻¹ ∈ S := by
    intro g' hg' s hs
    have h1 := (Subgroup.mem_normalizer_iff.1 hg' (f s)).1 (Subgroup.mem_map_of_mem f hs)
    have h2 : f (g' * s * g'⁻¹) = f g' * f s * (f g')⁻¹ := by simp [map_mul, map_inv]
    rw [← hmem, h2]
    exact h1
  constructor
  · intro hg
    rw [Subgroup.mem_normalizer_iff]
    intro s
    refine ⟨fwd g hg s, fun hs => ?_⟩
    have hg' : f g⁻¹ ∈ Subgroup.normalizer ((S.map f : Subgroup Y) : Set Y) := by
      rw [map_inv]
      exact Subgroup.inv_mem _ hg
    have e : g⁻¹ * (g * s * g⁻¹) * g⁻¹⁻¹ = s := by group
    have := fwd g⁻¹ hg' _ hs
    rw [e] at this
    exact this
  · intro hg
    rw [Subgroup.mem_normalizer_iff] at hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    obtain ⟨x, rfl⟩ := hf y
    have hR : f g * f x * (f g)⁻¹ = f (g * x * g⁻¹) := by simp [map_mul, map_inv]
    rw [hR, hmem, hmem]
    exact hg x

private theorem shultE67_map_normalizer {X Y : Type} [Group X] [Group Y] {f : X →* Y}
    (hf : Function.Surjective f) {S : Subgroup X} (hk : f.ker ≤ S) :
    (Subgroup.normalizer (S : Set X)).map f =
      Subgroup.normalizer ((S.map f : Subgroup Y) : Set Y) := by
  ext q
  obtain ⟨g, rfl⟩ := hf q
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxg⟩
    rw [← hxg]
    exact (shultE67_normalizer_map hf hk x).2 hx
  · intro hg
    exact ⟨g, (shultE67_normalizer_map hf hk g).1 hg, rfl⟩

private def shultE67A5a : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

private def shultE67A5b : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

private def shultE67A5V : Subgroup (alternatingGroup (Fin 5)) where
  carrier := {x | x = 1 ∨ x = shultE67A5a ∨ x = shultE67A5b ∨ x = shultE67A5a * shultE67A5b}
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      decide +kernel
  one_mem' := Or.inl rfl
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel

private theorem shultE67A5V_mem (x : alternatingGroup (Fin 5)) :
    x ∈ shultE67A5V ↔ (x = 1 ∨ x = shultE67A5a ∨ x = shultE67A5b ∨ x = shultE67A5a * shultE67A5b) :=
  Iff.rfl

private theorem shultE67A5V_card : Nat.card shultE67A5V = 4 := by
  have hset : (shultE67A5V : Set (alternatingGroup (Fin 5))) =
      ↑({1, shultE67A5a, shultE67A5b, shultE67A5a * shultE67A5b} :
        Finset (alternatingGroup (Fin 5))) := by
    ext x
    simp [shultE67A5V_mem]
  have h4 : ({1, shultE67A5a, shultE67A5b, shultE67A5a * shultE67A5b} :
      Finset (alternatingGroup (Fin 5))).card = 4 := by
    decide +kernel
  show Nat.card (shultE67A5V : Set (alternatingGroup (Fin 5))) = 4
  rw [Nat.card_coe_set_eq, hset, Set.ncard_coe_finset, h4]

private theorem shultE67A5V_mem_normalizer (σ : alternatingGroup (Fin 5)) :
    σ ∈ Subgroup.normalizer (shultE67A5V : Set (alternatingGroup (Fin 5))) ↔
      (σ : Equiv.Perm (Fin 5)) 4 = 4 := by
  rw [Subgroup.mem_normalizer_iff]
  simp only [shultE67A5V_mem]
  revert σ
  decide +kernel

private theorem shultE67A5V_card_normalizer :
    Nat.card (Subgroup.normalizer (shultE67A5V : Set (alternatingGroup (Fin 5)))) = 12 := by
  have e : Nat.card (Subgroup.normalizer (shultE67A5V : Set (alternatingGroup (Fin 5)))) =
      Nat.card {σ : alternatingGroup (Fin 5) // (σ : Equiv.Perm (Fin 5)) 4 = 4} :=
    Nat.card_congr (Equiv.subtypeEquivRight shultE67A5V_mem_normalizer)
  rw [e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

private theorem shultE67_index_odd (W : Subgroup (alternatingGroup (Fin 5)))
    (hW : Nat.card W = 4) : ¬ 2 ∣ W.index := by
  have h := Subgroup.card_mul_index W
  rw [hW, shultE67_card_alt5] at h
  omega

private def shultE67_sylow (W : Subgroup (alternatingGroup (Fin 5))) (hW : Nat.card W = 4) :
    Sylow 2 (alternatingGroup (Fin 5)) :=
  (IsPGroup.of_card (n := 2) (by rw [hW]; norm_num)).toSylow (shultE67_index_odd W hW)

private theorem shultE67_sylow_coe (W : Subgroup (alternatingGroup (Fin 5)))
    (hW : Nat.card W = 4) :
    (shultE67_sylow W hW : Subgroup (alternatingGroup (Fin 5))) = W :=
  IsPGroup.toSylow_coe _ _

private theorem shultE67_a5_normalizer_card (K : Subgroup (alternatingGroup (Fin 5)))
    (hK : Nat.card K = 4) :
    Nat.card (Subgroup.normalizer (K : Set (alternatingGroup (Fin 5)))) = 12 := by
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 5))
    (shultE67_sylow shultE67A5V shultE67A5V_card) (shultE67_sylow K hK)
  have hcoe : shultE67A5V.map (MulAut.conj c).toMonoidHom = K := by
    have h := congrArg
      (fun P : Sylow 2 (alternatingGroup (Fin 5)) => (P : Subgroup (alternatingGroup (Fin 5)))) hc
    simp only [Sylow.coe_subgroup_smul, shultE67_sylow_coe shultE67A5V shultE67A5V_card,
      shultE67_sylow_coe K hK] at h
    rw [← h]
    ext x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply, MulAut.conj_symm_apply]
  rw [← hcoe, ← Subgroup.map_equiv_normalizer_eq,
    Subgroup.card_map_of_injective (MulAut.conj c).injective]
  exact shultE67A5V_card_normalizer

private theorem shultE67_alt5_index {X : Type} [Group X] [Finite X]
    (α : X →* alternatingGroup (Fin 5)) (hα : Function.Surjective α) {S : Subgroup X}
    (hk : α.ker ≤ S) (hS2 : IsPGroup 2 S) (hSodd : ¬ 2 ∣ S.index) :
    (Subgroup.normalizer (S : Set X)).index = 5 := by
  have hP2 : IsPGroup 2 (S.map α) := hS2.map α
  have hPidx : (S.map α).index = S.index := Subgroup.index_map_eq S hα hk
  have h60 : Nat.card (S.map α) * (S.map α).index = 60 := by
    rw [Subgroup.card_mul_index, shultE67_card_alt5]
  have hPodd : ¬ 2 ∣ (S.map α).index := by
    rw [hPidx]
    exact hSodd
  obtain ⟨k, hk'⟩ := (IsPGroup.iff_card).1 hP2
  rw [hk'] at h60
  have hPcard : Nat.card (S.map α) = 4 := by
    rcases Nat.lt_or_ge k 3 with hk3 | hk3
    · interval_cases k
      · norm_num at h60
        omega
      · norm_num at h60
        omega
      · rw [hk']
        norm_num
    · have h8 : 2 ^ 3 ∣ 60 := by
        rw [← h60]
        exact Dvd.dvd.mul_right (pow_dvd_pow 2 hk3) _
      norm_num at h8
  have hH12 : Nat.card (Subgroup.normalizer ((S.map α : Subgroup (alternatingGroup (Fin 5))) :
      Set (alternatingGroup (Fin 5)))) = 12 := shultE67_a5_normalizer_card (S.map α) hPcard
  have hEq : Subgroup.normalizer (S : Set X) =
      (Subgroup.normalizer ((S.map α : Subgroup (alternatingGroup (Fin 5))) :
        Set (alternatingGroup (Fin 5)))).comap α := by
    ext g
    rw [Subgroup.mem_comap]
    exact (shultE67_normalizer_map hα hk g).symm
  rw [hEq, Subgroup.index_comap_of_surjective _ hα]
  have hHm := Subgroup.card_mul_index (Subgroup.normalizer ((S.map α : Subgroup
    (alternatingGroup (Fin 5))) : Set (alternatingGroup (Fin 5))))
  rw [hH12, shultE67_card_alt5] at hHm
  omega

private theorem shultE67_autI_isCyclic {G : Type} [Group G] {V X : Subgroup G}
    (hV : CFSG.Open.IsElemAbelian 2 V) (hX : X ≤ Subgroup.normalizer (V : Set G))
    [IsCyclic X] : IsCyclic (autI hV X) := by
  rw [← CFSG.Quasithin.range_convHom hV X hX]
  exact isCyclic_of_surjective (convHom hV X hX).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)

private theorem shultE67_coprime (n k : ℕ) (hn : 1 ≤ n) :
    Nat.Coprime (2 ^ n - 1) (2 ^ k) := by
  refine Nat.Coprime.pow_right k ?_
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  omega

private theorem shultE67_isPGroup_zpowers {X : Type} [Group X] [Finite X] {g : X} {k : ℕ}
    (hg : g ^ 2 ^ k = 1) : IsPGroup 2 (Subgroup.zpowers g) := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hg)
  exact (IsPGroup.iff_card).2 ⟨j, by rw [Nat.card_zpowers, hj]⟩

private theorem shultE67_le_of_odd_index {X : Type} [Group X] [Finite X] {P S : Subgroup X}
    (hPodd : ¬ 2 ∣ P.index) (hS : IsPGroup 2 S) (hPS : P ≤ S) : S ≤ P := by
  have hmul : P.relIndex S * S.index = P.index := Subgroup.relIndex_mul_index hPS
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hS
  have hdvd : (P.subgroupOf S).index ∣ 2 ^ a := by
    rw [← ha]
    exact Subgroup.index_dvd_card _
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hb0 : b = 0 := by
    by_contra hb0
    apply hPodd
    rw [← hmul]
    apply Dvd.dvd.mul_right
    show 2 ∣ (P.subgroupOf S).index
    rw [hb]
    exact dvd_pow_self 2 hb0
  have h1 : P.relIndex S = 1 := by
    show (P.subgroupOf S).index = 1
    rw [hb, hb0, pow_zero]
  exact Subgroup.relIndex_eq_one.1 h1

private theorem shultE67_mem_of_normalizes {X : Type} [Group X] [Finite X] {S R : Subgroup X}
    (hS2 : IsPGroup 2 S) (hSodd : ¬ 2 ∣ S.index) (hR2 : IsPGroup 2 R)
    (hRN : R ≤ Subgroup.normalizer (S : Set X)) : R ≤ S := by
  have hSR : IsPGroup 2 (S ⊔ R : Subgroup X) := IsPGroup.to_sup_of_normal_left' hS2 hR2 hRN
  have hle : S ⊔ R ≤ S := shultE67_le_of_odd_index hSodd hSR le_sup_left
  exact le_sup_right.trans hle

private theorem shultE67_mem_normalizer_subgroupOf {G : Type} [Group G] {L S : Subgroup G}
    (hSL : S ≤ L) (g : ↥L) :
    g ∈ Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L) ↔
      (g : G) ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hg s
    by_cases hs : s ∈ L
    · have := hg ⟨s, hs⟩
      simpa [Subgroup.mem_subgroupOf] using this
    · constructor
      · intro hsS
        exact absurd (hSL hsS) hs
      · intro hgs
        exfalso
        apply hs
        have hgL : (g : G) * s * (g : G)⁻¹ ∈ L := hSL hgs
        have h2 : s = (g : G)⁻¹ * ((g : G) * s * (g : G)⁻¹) * (g : G) := by group
        rw [h2]
        exact L.mul_mem (L.mul_mem (L.inv_mem g.2) hgL) g.2
  · intro hg s
    simpa [Subgroup.mem_subgroupOf] using hg (s : G)

private theorem shultE67_subgroupOf_normalizer {G : Type} [Group G] {L M S : Subgroup G}
    (hSL : S ≤ L) (hEq : L ⊓ M = L ⊓ Subgroup.normalizer (S : Set G)) :
    M.subgroupOf L = Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
  ext g
  rw [Subgroup.mem_subgroupOf, shultE67_mem_normalizer_subgroupOf hSL]
  have h1 : (g : G) ∈ L ⊓ M ↔ (g : G) ∈ L ⊓ Subgroup.normalizer (S : Set G) := by
    rw [hEq]
  rw [Subgroup.mem_inf, Subgroup.mem_inf] at h1
  exact ⟨fun hm => (h1.1 ⟨g.2, hm⟩).2, fun hn => (h1.2 ⟨g.2, hn⟩).2⟩

private theorem shultE67_subgroupOf_eq_pCore {G : Type} [Group G] {L M : Subgroup G}
    (hLM : L ⊓ M = pCoreOf 2 L) : M.subgroupOf L = CFSG.pCore 2 ↥L := by
  ext x
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    have hx' : (x : G) ∈ L ⊓ M := ⟨x.2, hx⟩
    rw [hLM] at hx'
    unfold pCoreOf at hx'
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx'
    have hxy : y = x := Subtype.ext hyx
    rw [← hxy]
    exact hy
  · intro hx
    have hx' : (x : G) ∈ pCoreOf 2 L := Subgroup.mem_map_of_mem L.subtype hx
    rw [← hLM] at hx'
    exact hx'.2

private theorem shultE67_pCore_le {G : Type} [Group G] {L S : Subgroup G}
    (hpc : pCoreOf 2 L ≤ S) : CFSG.pCore 2 ↥L ≤ S.subgroupOf L := by
  intro x hx
  rw [Subgroup.mem_subgroupOf]
  exact hpc (Subgroup.mem_map_of_mem L.subtype hx)

private theorem shultE67_borel_sylow {G : Type} [Group G] {L B : Subgroup G}
    (hBor : IsBorelOfBlock L B) (hne : ¬ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3) :
    ∃ S : Subgroup G, IsSylowTwoOf S L ∧
      B ⊔ pCoreOf 2 L = L ⊓ Subgroup.normalizer (S : Set G) := by
  unfold IsBorelOfBlock at hBor
  rw [if_neg hne] at hBor
  exact hBor

private theorem shultE67_card_eq {G : Type} [Group G] {V U W : Subgroup G}
    (hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hUV : U ≤ V) (hWV : W ≤ V)
    (hinf : U ⊓ W = ⊥) (hsup : U ⊔ W = V) :
    Nat.card W = U.relIndex V := by
  haveI hnorm : (U.subgroupOf V).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hc : (g : G) * (n : G) = (n : G) * (g : G) := hcomm g.1 g.2 n.1 n.2
    have e : (g : G) * (n : G) * (g : G)⁻¹ = (n : G) := by
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    show ((g : G) * (n : G) * (g : G)⁻¹) ∈ U
    rw [e]
    exact hn⟩
  let f : ↥(W.subgroupOf V) →* ↥V ⧸ U.subgroupOf V :=
    (QuotientGroup.mk' (U.subgroupOf V)).comp (W.subgroupOf V).subtype
  have hf : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · rw [injective_iff_map_eq_one]
      intro a ha
      have ha' : ((a : ↥V) : G) ∈ U := by
        have h1 := (QuotientGroup.eq_one_iff ((a : ↥V))).1 ha
        exact Subgroup.mem_subgroupOf.1 h1
      have ha'' : ((a : ↥V) : G) ∈ W := Subgroup.mem_subgroupOf.1 a.2
      have hbot : ((a : ↥V) : G) ∈ U ⊓ W := ⟨ha', ha''⟩
      rw [hinf, Subgroup.mem_bot] at hbot
      apply Subtype.ext
      apply Subtype.ext
      simpa using hbot
    · intro q
      obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf V) q
      have hv : (v : G) ∈ U ⊔ W := by
        rw [hsup]
        exact v.2
      obtain ⟨u, hu, w, hw, hvw⟩ := shultE67_mem_sup
        (fun a ha b hb => hcomm a (hUV ha) b (hWV hb)) hv
      refine ⟨⟨⟨w, hWV hw⟩, Subgroup.mem_subgroupOf.2 hw⟩, ?_⟩
      show QuotientGroup.mk' (U.subgroupOf V) (⟨w, hWV hw⟩ : ↥V) =
        QuotientGroup.mk' (U.subgroupOf V) v
      apply QuotientGroup.eq.2
      rw [Subgroup.mem_subgroupOf]
      show (w : G)⁻¹ * (v : G) ∈ U
      rw [hvw, hcomm u (hUV hu) w (hWV hw), inv_mul_cancel_left]
      exact hu
  have e1 : Nat.card W = Nat.card (W.subgroupOf V) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWV).symm.toEquiv
  have e2 : Nat.card (W.subgroupOf V) = Nat.card (↥V ⧸ U.subgroupOf V) :=
    Nat.card_congr (Equiv.ofBijective f hf)
  rw [e1, e2]
  rfl

end ShultE67

section E6_7


private theorem shultE67_block
    {G : Type} [Group G] [Finite G] {T M V U K L : Subgroup G}
    (h : E6.HypE61 T M V) (hU : U ∈ E6.gammaE64 V M)
    (hKU : K ≤ Subgroup.centralizer (U : Set G)) (hK : CharTwo K)
    (hQK : IsSylowTwoOf (T ⊓ Subgroup.centralizer (V : Set G)) K)
    (hL : IsChi0Block K L) (hJ : L = ⁅L, thompsonJ (T ⊓ Subgroup.centralizer (V : Set G))⁆)
    (hBor : IsBorelOfBlock L (L ⊓ (K ⊓ M))) (hLM : ¬ L ≤ M) :
    (IsAltType L 3 → E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = 1 ∧
        M.relIndex L = 3 ∧ E3.rParam V = 1) ∧
    (IsAltType L 5 → E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = 1 ∧
        M.relIndex L = 5 ∧ E3.rParam V = 1) ∧
    (∀ n : ℕ, 1 < n → IsLin2Type L n → ∃ X : Subgroup G, X ≤ L ⊓ M ∧ IsCyclic X ∧
        Nat.card X = 2 ^ n - 1 ∧ (V ⊓ Subgroup.centralizer (L : Set G)) ⊓ ⁅V, X⁆ = ⊥ ∧
        (V ⊓ Subgroup.centralizer (L : Set G)) ⊔ ⁅V, X⁆ = V ∧
        E3.mQuot ⁅V, X⁆ ⊥ = n ∧
        L ⊓ M = (((L ⊓ (T ⊓ Subgroup.centralizer (V : Set G)) : Subgroup G) : Set G) *
          (X : Set G) : Set G) ∧
        E2.IsBorelIn (⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L))
          (((M ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) ∧
        n ≤ E3.mQuot V U) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  have hB2 : IsBlock2 K L := hL.1
  have hLK : L ≤ K := hB2.2.1
  have hV2 : IsPGroup 2 V := h.isPGroup_V
  have hUV : U ≤ V := hU.1
  have hVQ : V ≤ Q := h.le_inf_centralizer
  have hQV : Q ≤ Subgroup.centralizer (V : Set G) := inf_le_right
  have hQM : Q ≤ M := hQV.trans h.centralizer_le
  have hKM : K ⊓ M ≤ Subgroup.normalizer (V : Set G) :=
    (inf_le_inf_right M hKU).trans (E6.e6_5_three h hU).2
  have hLV : ⁅V, L⁆ ≠ ⊥ := E6.e6_2 h hLM
  have hVL : ¬ V ≤ Subgroup.centralizer (L : Set G) := fun hc =>
    hLV (Subgroup.commutator_eq_bot_iff_le_centralizer.2 hc)
  have hUC : U ≤ V ⊓ Subgroup.centralizer (L : Set G) := le_inf hUV fun u hu =>
    Subgroup.mem_centralizer_iff.2 fun l hl =>
      (Subgroup.mem_centralizer_iff.1 (hKU (hLK hl)) u hu).symm
  have hsylQ : IsSylowTwoOf (Q ⊓ L) L := E6.isSylowTwoOf_inf_of_isBlock2 hQK hB2
  have hpcV : pCoreOf 2 L ≤ Q ⊓ L := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hsylQ
  have hpcLM : pCoreOf 2 L ≤ L ⊓ M :=
    le_inf (hpcV.trans inf_le_right) ((hpcV.trans inf_le_left).trans hQM)
  have hne_V : V ⊓ Subgroup.centralizer (L : Set G) ≠ V := fun heq =>
    hVL (by rw [← heq]; exact inf_le_right)
  refine ⟨fun h3 => ?_, fun h5 => ?_, fun n hn hlin => ?_⟩
  ·
    have hc3 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3 := by
      rw [shultE67_altcard h3, shultE67_card_alt3]
    have hBor3 : L ⊓ (K ⊓ M) ≤ pCoreOf 2 L := by
      unfold IsBorelOfBlock at hBor
      rwa [if_pos hc3] at hBor
    have hLMeq : L ⊓ M = pCoreOf 2 L :=
      le_antisymm (fun x hx => hBor3 ⟨hx.1, hLK hx.1, hx.2⟩) hpcLM
    have hrel : M.relIndex L = 3 := by
      show (M.subgroupOf L).index = 3
      rw [shultE67_subgroupOf_eq_pCore hLMeq]
      exact hc3
    have hm1 : E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = 1 :=
      shultE67_mQuot_one hV2 inf_le_left hne_V
        (E6.relIndex_le_two_of_alt3 hK hB2 h3 hQK hJ hVQ hQV)
    exact ⟨hm1, hrel, shultE67_rParam_one h hLM inf_le_left
      (fun l hl => Subgroup.mem_centralizer_iff.2 fun w hw =>
        (Subgroup.mem_centralizer_iff.1 hw.2 l hl).symm) hm1⟩
  ·
    obtain ⟨α5, hα5, hker5, -⟩ := id h5
    have hc5 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 60 := by
      rw [shultE67_altcard h5, shultE67_card_alt5]
    have hne3 : ¬ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3 := by
      rw [hc5]
      norm_num
    obtain ⟨S, hS, hEq'⟩ := shultE67_borel_sylow hBor hne3
    have hA : L ⊓ (K ⊓ M) = L ⊓ M :=
      le_antisymm (inf_le_inf_left _ inf_le_right) (fun x hx => ⟨hx.1, hLK hx.1, hx.2⟩)
    rw [hA, sup_eq_left.2 hpcLM] at hEq'
    have hEq : L ⊓ M = L ⊓ Subgroup.normalizer (S : Set G) := hEq'
    have hSL : S ≤ L := hS.1
    have hS2 : IsPGroup 2 (S.subgroupOf L) :=
      hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSL).symm
    have hSodd : ¬ 2 ∣ (S.subgroupOf L).index := hS.2.2
    have hkS : α5.ker ≤ S.subgroupOf L := by
      rw [hker5]
      exact shultE67_pCore_le (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS)
    have hrel : M.relIndex L = 5 := by
      show (M.subgroupOf L).index = 5
      rw [shultE67_subgroupOf_normalizer hSL hEq]
      exact shultE67_alt5_index α5 hα5 hkS hS2 hSodd
    have hm1 : E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = 1 :=
      shultE67_mQuot_one hV2 inf_le_left hne_V
        (E6.relIndex_le_two_of_alt5 hK hB2 h5 hQK hVQ hQV)
    exact ⟨hm1, hrel, shultE67_rParam_one h hLM inf_le_left
      (fun l hl => Subgroup.mem_centralizer_iff.2 fun w hw =>
        (Subgroup.mem_centralizer_iff.1 hw.2 l hl).symm) hm1⟩
  ·
    obtain ⟨-, hidx, x, hx, hxj, hall, hsub2, -⟩ :=
      E6.lin2_block_torus'' h.isElemAbelian h.le hQK hQM hKM hK hB2 hn hlin hBor hVL
    have hxLM : x ∈ L ⊓ M := ⟨hx.1, hx.2.2⟩
    have hne3 : ¬ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3 := by
      intro hc3
      have hBor3 : L ⊓ (K ⊓ M) ≤ pCoreOf 2 L := by
        unfold IsBorelOfBlock at hBor
        rwa [if_pos hc3] at hBor
      have hxp : x ∈ (CFSG.pCore 2 ↥L).map L.subtype := hBor3 hx
      obtain ⟨y0, hy0, hy0x⟩ := Subgroup.mem_map.1 hxp
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨y0, hy0⟩
      have hy1 : y0 ^ 2 ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      have hx1 : x ^ 2 ^ k = 1 := by
        rw [← hy0x]
        have := congrArg Subtype.val hy1
        simpa using this
      have hdvd : (2 ^ n - 1) ∣ 2 ^ k :=
        (hxj (2 ^ k)).1 (by rw [hx1]; exact Subgroup.one_mem _)
      have h1 : 2 ^ n - 1 = 1 := Nat.Coprime.eq_one_of_dvd (shultE67_coprime n k (by omega)) hdvd
      have h4 : 4 ≤ 2 ^ n := by
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    obtain ⟨S, hS, hEq'⟩ := shultE67_borel_sylow hBor hne3
    have hA : L ⊓ (K ⊓ M) = L ⊓ M :=
      le_antisymm (inf_le_inf_left _ inf_le_right) (fun x hx => ⟨hx.1, hLK hx.1, hx.2⟩)
    rw [hA, sup_eq_left.2 hpcLM] at hEq'
    have hEq : L ⊓ M = L ⊓ Subgroup.normalizer (S : Set G) := hEq'
    have hSL : S ≤ L := hS.1
    have hS2 : IsPGroup 2 (S.subgroupOf L) :=
      hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSL).symm
    have hSodd : ¬ 2 ∣ (S.subgroupOf L).index := hS.2.2
    have hpcS : pCoreOf 2 L ≤ S := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS
    have hR2 : IsPGroup 2 ((Q ⊓ L).subgroupOf L) :=
      hsylQ.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
    have hRN : (Q ⊓ L).subgroupOf L ≤
        Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
      intro r hr
      rw [shultE67_mem_normalizer_subgroupOf hSL]
      have hr' : (r : G) ∈ Q ⊓ L := Subgroup.mem_subgroupOf.1 hr
      have hrLM : (r : G) ∈ L ⊓ M := ⟨hr'.2, hQM hr'.1⟩
      rw [hEq] at hrLM
      exact hrLM.2
    have hR_le_S : (Q ⊓ L).subgroupOf L ≤ S.subgroupOf L :=
      shultE67_mem_of_normalizes hS2 hSodd hR2 hRN
    have hS_le_R : S.subgroupOf L ≤ (Q ⊓ L).subgroupOf L :=
      shultE67_le_of_odd_index hsylQ.2.2 hS2 hR_le_S
    have hSQ : ∀ g ∈ S, g ∈ Q ⊓ L := by
      intro g hg
      have hgL : (⟨g, hSL hg⟩ : ↥L) ∈ S.subgroupOf L := Subgroup.mem_subgroupOf.2 hg
      exact Subgroup.mem_subgroupOf.1 (hS_le_R hgL)
    have hcS : ∀ c : G, c ∈ L → c ∈ M → (∃ k : ℕ, c ^ 2 ^ k = 1) → c ∈ S := by
      intro c hcL hcM hck
      obtain ⟨k', hk'⟩ := hck
      have hcLM : c ∈ L ⊓ M := ⟨hcL, hcM⟩
      have hcN : (⟨c, hcL⟩ : ↥L) ∈
          Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
        rw [shultE67_mem_normalizer_subgroupOf hSL]
        rw [hEq] at hcLM
        exact hcLM.2
      have hzp : Subgroup.zpowers (⟨c, hcL⟩ : ↥L) ≤
          Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L) :=
        Subgroup.zpowers_le.2 hcN
      have hcpow : (⟨c, hcL⟩ : ↥L) ^ 2 ^ k' = 1 := Subtype.ext (by simpa using hk')
      have hle := shultE67_mem_of_normalizes hS2 hSodd (shultE67_isPGroup_zpowers hcpow) hzp
      exact Subgroup.mem_subgroupOf.1 (hle (Subgroup.mem_zpowers _))
    obtain ⟨k, hk⟩ := hsub2 (x ^ (2 ^ n - 1)) (pow_mem hx _) ((hxj (2 ^ n - 1)).2 dvd_rfl)
    have hcop : Nat.Coprime (2 ^ n - 1) (2 ^ k) := shultE67_coprime n k (by omega)
    have hy_mod : ∀ j : ℕ, (x ^ 2 ^ k) ^ j ∈ Subgroup.centralizer (V : Set G) ↔
        (2 ^ n - 1) ∣ j := by
      intro j
      rw [← pow_mul, hxj, hcop.dvd_mul_left]
    have hy_pow : (x ^ 2 ^ k) ^ (2 ^ n - 1) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hk]
    have hy_ord : orderOf (x ^ 2 ^ k) = 2 ^ n - 1 :=
      Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hy_pow)
        ((hy_mod (orderOf (x ^ 2 ^ k))).1 (by rw [pow_orderOf_eq_one]; exact Subgroup.one_mem _))
    have hyLM : x ^ 2 ^ k ∈ L ⊓ M := pow_mem hxLM _
    have hXLM : Subgroup.zpowers (x ^ 2 ^ k) ≤ L ⊓ M := Subgroup.zpowers_le.2 hyLM
    have hXcard : Nat.card (Subgroup.zpowers (x ^ 2 ^ k)) = 2 ^ n - 1 := by
      rw [Nat.card_zpowers, hy_ord]
    have hXC : Subgroup.zpowers (x ^ 2 ^ k) ⊓ Subgroup.centralizer (V : Set G) = ⊥ := by
      refine eq_bot_iff.2 fun g hg => ?_
      obtain ⟨hgX, hgC⟩ := hg
      obtain ⟨j, hj, hjg⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1 hgX)
      rw [← hjg] at hgC ⊢
      rw [hy_ord] at hj
      have hj0 : j = 0 := Nat.eq_zero_of_dvd_of_lt ((hy_mod j).1 hgC) (Finset.mem_range.1 hj)
      rw [hj0, pow_zero]
      exact Subgroup.one_mem _
    have hmV : E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = n := by
      have h1 := E3.relIndex_eq_two_pow hV2 (V ⊓ Subgroup.centralizer (L : Set G))
      rw [hidx] at h1
      exact (Nat.pow_right_injective (le_refl 2) h1).symm
    have hXN : Subgroup.zpowers (x ^ 2 ^ k) ≤ Subgroup.normalizer (V : Set G) :=
      hXLM.trans ((inf_le_inf_right M hLK).trans hKM)
    have hXU : Subgroup.zpowers (x ^ 2 ^ k) ≤
        Subgroup.centralizer ((V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
      intro g hg
      have hgL : g ∈ L := (hXLM hg).1
      exact Subgroup.mem_centralizer_iff.2 fun w hw =>
        (Subgroup.mem_centralizer_iff.1 hw.2 g hgL).symm
    have hXc : IsCyclic (autI h.isElemAbelian (Subgroup.zpowers (x ^ 2 ^ k))) :=
      shultE67_autI_isCyclic h.isElemAbelian hXN
    have hXcard' : Nat.card (autI h.isElemAbelian (Subgroup.zpowers (x ^ 2 ^ k))) =
        2 ^ E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) - 1 := by
      rw [hmV, CFSG.Quasithin.card_autI_eq h.isElemAbelian hXN, hXC, Subgroup.relIndex_bot_left,
        hXcard]
    obtain ⟨hdec1, hdec2, -⟩ := E6.singer_autI h.isElemAbelian inf_le_left
      (by rw [hmV]; exact hn) hXU hXN hXc hXcard'
    have hWV : ⁅V, Subgroup.zpowers (x ^ 2 ^ k)⁆ ≤ V := by
      rw [Subgroup.commutator_le]
      intro v hv g hg
      rw [commutatorElement_def]
      have h1 : g * v⁻¹ * g⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.1 (hXN hg) v⁻¹).1 (V.inv_mem hv)
      have h2 : v * g * v⁻¹ * g⁻¹ = v * (g * v⁻¹ * g⁻¹) := by group
      rw [h2]
      exact V.mul_mem hv h1
    have hcardW : Nat.card (⁅V, Subgroup.zpowers (x ^ 2 ^ k)⁆ : Subgroup G) =
        (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V :=
      shultE67_card_eq (fun a ha b hb => B2F.isElemAbelian_comm h.isElemAbelian ha hb)
        inf_le_left hWV hdec1 hdec2
    have hmW : E3.mQuot (⁅V, Subgroup.zpowers (x ^ 2 ^ k)⁆ : Subgroup G) ⊥ = n := by
      have h1 : E3.mQuot (⁅V, Subgroup.zpowers (x ^ 2 ^ k)⁆ : Subgroup G) ⊥ =
          E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) := by
        unfold E3.mQuot
        rw [Subgroup.relIndex_bot_left, hcardW]
      rw [h1, hmV]
    have hset : L ⊓ M = (((L ⊓ (Q) : Subgroup G) : Set G) *
        (Subgroup.zpowers (x ^ 2 ^ k) : Set G) : Set G) := by
      ext m
      constructor
      · intro hm
        have hmLM : m ∈ L ⊓ M := hm
        obtain ⟨j, hj⟩ := hall m ⟨hmLM.1, hLK hmLM.1, hmLM.2⟩
        have hxjLM : x ^ j ∈ L ⊓ M := pow_mem hxLM j
        have hcLM : m * (x ^ j)⁻¹ ∈ L ⊓ M := (L ⊓ M).mul_mem hmLM ((L ⊓ M).inv_mem hxjLM)
        have hcS_mem : m * (x ^ j)⁻¹ ∈ S :=
          hcS _ hcLM.1 hcLM.2 (hsub2 _ ⟨hcLM.1, hLK hcLM.1, hcLM.2⟩ hj)
        have hzLM : x ^ (2 ^ n - 1) ∈ L ⊓ M := pow_mem hxLM _
        have hz_mem : x ^ (2 ^ n - 1) ∈ S := hcS _ hzLM.1 hzLM.2 ⟨k, hk⟩
        obtain ⟨u, w, huw⟩ : IsCoprime (((2 ^ n - 1 : ℕ)) : ℤ) ((2 ^ k : ℕ) : ℤ) :=
          Nat.isCoprime_iff_coprime.2 hcop
        have hsplit : (j : ℤ) = ((2 ^ k : ℕ) : ℤ) * ((j : ℤ) * w) +
            ((2 ^ n - 1 : ℕ) : ℤ) * ((j : ℤ) * u) := by
          linear_combination (-(j : ℤ)) * huw
        have hdecomp : x ^ (j : ℤ) =
            (x ^ 2 ^ k) ^ ((j : ℤ) * w) * (x ^ (2 ^ n - 1)) ^ ((j : ℤ) * u) := by
          calc x ^ (j : ℤ)
              = x ^ (((2 ^ k : ℕ) : ℤ) * ((j : ℤ) * w) +
                  ((2 ^ n - 1 : ℕ) : ℤ) * ((j : ℤ) * u)) := by rw [← hsplit]
            _ = x ^ (((2 ^ k : ℕ) : ℤ) * ((j : ℤ) * w)) *
                  x ^ (((2 ^ n - 1 : ℕ) : ℤ) * ((j : ℤ) * u)) := zpow_add _ _ _
            _ = (x ^ ((2 ^ k : ℕ) : ℤ)) ^ ((j : ℤ) * w) *
                  (x ^ ((2 ^ n - 1 : ℕ) : ℤ)) ^ ((j : ℤ) * u) := by
              rw [zpow_mul x (((2 ^ k : ℕ)) : ℤ), zpow_mul x (((2 ^ n - 1 : ℕ)) : ℤ)]
            _ = (x ^ 2 ^ k) ^ ((j : ℤ) * w) * (x ^ (2 ^ n - 1)) ^ ((j : ℤ) * u) := by
              rw [zpow_natCast, zpow_natCast]
        have hyz : Commute (x ^ 2 ^ k) (x ^ (2 ^ n - 1)) := (Commute.refl x).pow_pow _ _
        have hcomm' := hyz.zpow_zpow ((j : ℤ) * w) ((j : ℤ) * u)
        have e1 : (x ^ 2 ^ k) ^ ((j : ℤ) * w) * (x ^ (2 ^ n - 1)) ^ ((j : ℤ) * u) = x ^ j := by
          rw [← hdecomp, zpow_natCast]
        have haQ : m * (x ^ j)⁻¹ * (x ^ (2 ^ n - 1)) ^ ((j : ℤ) * u) ∈ Q ⊓ L :=
          (Q ⊓ L).mul_mem (hSQ _ hcS_mem) (hSQ _ (Subgroup.zpow_mem S hz_mem _))
        refine ⟨m * (x ^ j)⁻¹ * (x ^ (2 ^ n - 1)) ^ ((j : ℤ) * u), ?_,
          (x ^ 2 ^ k) ^ ((j : ℤ) * w), ?_, ?_⟩
        · show _ ∈ L ⊓ Q
          rw [inf_comm]
          exact haQ
        · exact SetLike.mem_coe.2 (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _)
        · calc m * (x ^ j)⁻¹ * (x ^ (2 ^ n - 1)) ^ ((j : ℤ) * u) * (x ^ 2 ^ k) ^ ((j : ℤ) * w)
              = m * (x ^ j)⁻¹ * ((x ^ (2 ^ n - 1)) ^ ((j : ℤ) * u) *
                  (x ^ 2 ^ k) ^ ((j : ℤ) * w)) := mul_assoc _ _ _
            _ = m * (x ^ j)⁻¹ * ((x ^ 2 ^ k) ^ ((j : ℤ) * w) *
                  (x ^ (2 ^ n - 1)) ^ ((j : ℤ) * u)) := by rw [hcomm'.eq]
            _ = m := by rw [e1, inv_mul_cancel_right]
      · rintro ⟨a, ha, b, hb, rfl⟩
        have ha' : a ∈ L ⊓ Q := ha
        exact (L ⊓ M).mul_mem ⟨ha'.1, hQM ha'.2⟩ (hXLM hb)
    have hMsub : (M ⊓ L).subgroupOf L = M.subgroupOf L := by
      ext g
      simp [Subgroup.mem_subgroupOf]
    have hMSL := shultE67_subgroupOf_normalizer hSL hEq
    have hkerP : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker ≤ S.subgroupOf L := by
      rw [QuotientGroup.ker_mk']
      exact shultE67_pCore_le hpcS
    have hsurj := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L)
    have hmapEq : ((M ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) =
        (⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) ⊓ Subgroup.normalizer
          ((((S.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) :
            Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) : Set (↥L ⧸ CFSG.pCore 2 ↥L)) := by
      rw [hMsub, hMSL, top_inf_eq, shultE67_map_normalizer hsurj hkerP]
    have hborel : E2.IsBorelIn (⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L))
        (((M ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) := by
      unfold E2.IsBorelIn
      refine ⟨(S.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)),
        ⟨le_top, hS2.map _, ?_⟩, hmapEq⟩
      show ¬ 2 ∣ (((S.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).relIndex ⊤)
      rw [Subgroup.relIndex_top_right, Subgroup.index_map_eq _ hsurj hkerP]
      exact hSodd
    have hn2 : n ≤ E3.mQuot V U := by
      have := E3.mQuot_mono (V := V) hUC
      rw [hmV] at this
      exact this
    exact ⟨Subgroup.zpowers (x ^ 2 ^ k), hXLM, inferInstance, hXcard, hdec1, hdec2, hmW,
      hset, hborel, hn2⟩

theorem as_E_6_7
    : E_6_7 := by
  intro G _ _ T M V h U hU K hTK hKU hK
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQsyl : IsSylowTwoOf (T ⊓ Subgroup.centralizer (V : Set G)) K :=
    A4.isSylowTwoOf_mono (E6.e6_5_one h hU) hTK hKU
  have hcgs : cgsIn K (T ⊓ Subgroup.centralizer (V : Set G)) ≤ K ⊓ M := by
    refine le_inf (iSup_le fun C => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ =>
      inf_le_left) ?_
    exact (E6.cgsIn_mono hKU).trans ((E6.e6_5_two h hU).1.trans inf_le_right)
  have hO2 : pCoreOf 2 K ≠ ⊥ := by
    intro h0
    apply h.Q_ne_bot
    have h1 := hK
    unfold CharTwo at h1
    rw [h0, Subgroup.coe_bot, Subgroup.centralizer_eq_top_iff_subset.2 (by simp),
      inf_top_eq] at h1
    exact le_bot_iff.1 (hTK.trans h1)
  have hsq : IsSQTKIn K :=
    ⟨stronglyQuasithin_of_pCoreOf_ne_bot h.qtke hO2,
      kGroup_of_pCoreOf_ne_bot h.qtke h.simple h.nonabelian hO2⟩
  obtain ⟨r, Lb, hr, hLb, hprod⟩ := H13.VolI.asc129Statement_holds G K
    (T ⊓ Subgroup.centralizer (V : Set G)) (K ⊓ M) hsq hK hQsyl hcgs inf_le_left
  have hLK : ∀ i, Lb i ≤ K := fun i => (hLb i).1.1.2.1
  have hset := E6.coe_eq_mul_iSup hLK hprod
  have hcommd : ∀ i j, i ≠ j → Lb i ≠ Lb j → ⁅Lb i, Lb j⁆ = ⊥ := fun i j _ hne =>
    distinctBlocksCommuteStatement K (Lb i) (Lb j) hK (hLb i).1.1 (hLb j).1.1 hne
  obtain ⟨s, Ls, hs, hLs, hcommLs, hsetLs⟩ := shultE67_prune hr hLK hcommd hset
  have hblk : ∀ i, IsChi0Block K (Ls i) ∧
      ⁅Ls i, thompsonJ (T ⊓ Subgroup.centralizer (V : Set G))⁆ = Ls i ∧
      IsBorelOfBlock (Ls i) (Ls i ⊓ (K ⊓ M)) ∧ ¬ Ls i ≤ M := by
    intro i
    obtain ⟨hnot, j, hj⟩ := hLs i
    refine ⟨?_, ?_, ?_, hnot⟩
    · rw [hj]
      exact (hLb j).1
    · rw [hj]
      exact (hLb j).2.2
    · rw [hj]
      exact (hLb j).2.1
  have hB := fun i => shultE67_block h hU hKU hK hQsyl (hblk i).1 (hblk i).2.1.symm
    (hblk i).2.2.1 (hblk i).2.2.2
  exact ⟨s, Ls, hs, fun i => (hblk i).1, hcommLs, fun i => (hblk i).2.1.symm, hsetLs.symm,
    fun i => ⟨(hB i).1, (hB i).2.1⟩, fun i n hn hlin => (hB i).2.2 n hn hlin⟩

end E6_7

@[expose] def E_6_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U L : Subgroup G) (h : E6.HypE61 T M V),
    U ∈ E6.gammaE64 V M → IsComponentIn L (Subgroup.centralizer (U : Set G)) →
      ¬ L ≤ M ∧
        (E68Case1P h.isElemAbelian T M U L ∨ E68Case2P T M V U L ∨ E68Case3P T M V U L ∨
          E6.E68Case4 M V U L ∨ E68Case5P M V U L)

section

theorem as_E_6_8
    : E_6_8 := by
  have hInn : CFSG.QuasithinUnique.Ch1.EvenLieAutInner :=
    CFSG.Quasithin.H13.KG68.evenLieAutInner_holds
  have h121 : CFSG.QuasithinUnique.Id2519.Prop121Three :=
    CFSG.QuasithinUnique.DoubleA3.in2436_p121_3
  have hnot : CFSG.QuasithinUnique.Vol2Native.L239.L239NotRankOne :=
    CFSG.QuasithinUnique.Vol2Native.L239.l239NotRankOne
  have hC129 : ∀ (G : Type) [Group G] [Finite G], CFSG.Quasithin.ASC129Statement G :=
    CFSG.Quasithin.H13.VolI.asc129Statement_holds
  have hSpor : CFSG.QuasithinUnique.Ch1.SporadicAutInner :=
    CFSG.QuasithinUnique.Ch1.sporadicAutInner_of_residual
      (CFSG.QuasithinUnique.Ch1.sporadicResidualAutInner_of_rest
        (CFSG.QuasithinUnique.Ch1.sporadicRestAutInner_of_J4OutOdd
          CFSG.QuasithinUnique.Setup.X1.j4OuterOdd))
  exact CFSG.Quasithin.RonanE68.e68P_of_inputs CFSG.QuasithinUnique.Ch1.lemma115_3_List_proved
    hC129 CFSG.QuasithinUnique.parabolicPairs_proved hnot h121
    CFSG.Quasithin.E6.e68AltRank hInn hSpor
    CFSG.Quasithin.H13.KG68.sporadicSylowCenterCyclic_holds
    CFSG.QuasithinUnique.Vol2Native.L239.l239Covers
    CFSG.Quasithin.E6.E68Proof.smallCatL33_holds CFSG.Quasithin.E6.E68Proof.smallCatL2p_holds
    CFSG.Quasithin.E6.E68Proof.e68A6Case
    (CFSG.Quasithin.E6.E68Proof.e68M22Excl hC129 hSpor
      CFSG.QuasithinUnique.Vol2Native.L239.l239M22Parabolic
      CFSG.QuasithinUnique.Vol2Native.L239.l239M23Parabolic hnot h121)
    (CFSG.Quasithin.E6.E68Proof.e68LieRankTwo_of_facts
      CFSG.Quasithin.E6.E68Proof.e68LieFacts_holds hInn h121)
    CFSG.Quasithin.E6.E68Proof.e68LieFacts_holds

end

@[expose] def E_6_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V : Subgroup G), E6.HypE61 T M V →
    ∀ U ∈ E6.gammaE64 V M,
      oddCoreIn (Subgroup.centralizer (U : Set G)) ⊓ M = ⊥ ∧
      (oddCoreIn (Subgroup.centralizer (U : Set G)) ≠ ⊥ →
        (∃ A : Subgroup G, U ≤ A ∧ A ≤ V ∧ E3.mQuot V A = 1 ∧
          ¬ oddCoreIn (Subgroup.centralizer (U : Set G)) ⊓ Subgroup.centralizer (A : Set G) ≤ M) ∧
        rParam V = 1)

set_option linter.unusedVariables false in
theorem as_E_6_9 : E_6_9 := fun G _ _ T M V h U hU =>
  ⟨E6.e6_9_one h hU, fun hO => by
    obtain ⟨A, hUA, hAV, hA1, hAM⟩ := E6.e6_9_two h hU hO
    refine ⟨⟨A, hUA, hAV, hA1, hAM⟩, ?_⟩
    have hCN : ¬ Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (V : Set G) := fun hle =>
      hAM (inf_le_right.trans (hle.trans h.normalizer_le))
    have h1 := E6.rParam_le_mQuot hAV hCN
    rw [hA1] at h1
    exact le_antisymm (by exact_mod_cast h1) (E6.one_le_rParam h)⟩

@[expose] def E_6_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V : Subgroup G), E6.HypE61 T M V →
    ∀ U ∈ E6.gammaE64 V M, E3.mQuot V U = 1 →
      (U ⊓ (V ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥ ∨ CharTwo (Subgroup.centralizer (U : Set G))) →
      CharTwo (Subgroup.centralizer (U : Set G)) ∧
      (∃ (s : ℕ) (Ls : Fin s → Subgroup G) (ns : Fin s → ℕ), s ≤ 2 ∧
        (∀ i, IsBlock2 (Subgroup.centralizer (U : Set G)) (Ls i) ∧ (ns i = 3 ∨ ns i = 5) ∧
          IsAltType (Ls i) (ns i) ∧ M.relIndex (Ls i) = ns i) ∧
        (∀ i j, i ≠ j → ⁅Ls i, Ls j⁆ = ⊥) ∧
        ((Subgroup.centralizer (U : Set G) ⊓ M : Subgroup G) : Set G) *
            ((⨆ i, Ls i : Subgroup G) : Set G) = (Subgroup.centralizer (U : Set G) : Set G)) ∧
      (∀ W : Subgroup G, W ≤ U → ¬ ∃ E : Subgroup G, IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
        E ≤ Subgroup.normalizer (W : Set G) ∧ E ⊓ Subgroup.centralizer (W : Set G) = ⊥) ∧
      ¬ omegaOneCenterOf (T ⊓ Subgroup.normalizer (U : Set G)) ≤ U

section ShultE610

private theorem shultE610_mem_sup_normal {G : Type} [Group G] {H K : Subgroup G}
    (hHK : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) {z : G} (hz : z ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, z = h * k := by
  let P : Subgroup G :=
    { carrier := {z | ∃ h ∈ H, ∃ k ∈ K, z = h * k}
      mul_mem' := by
        rintro _ _ ⟨h₁, h₁H, k₁, k₁K, rfl⟩ ⟨h₂, h₂H, k₂, k₂K, rfl⟩
        refine ⟨h₁ * h₂, H.mul_mem h₁H h₂H, (h₂⁻¹ * k₁ * h₂⁻¹⁻¹) * k₂,
          K.mul_mem (hHK h₂⁻¹ (H.inv_mem h₂H) k₁ k₁K) k₂K, ?_⟩
        group
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨h, hh, k, hk, rfl⟩
        refine ⟨h⁻¹, H.inv_mem hh, h * k⁻¹ * h⁻¹, hHK h hh k⁻¹ (K.inv_mem hk), ?_⟩
        group }
  have hHP : H ≤ P := fun h hh => ⟨h, hh, 1, K.one_mem, (mul_one h).symm⟩
  have hKP : K ≤ P := fun k hk => ⟨1, H.one_mem, k, hk, (one_mul k).symm⟩
  have hzP : z ∈ P := sup_le hHP hKP hz
  obtain ⟨h, hh, k, hk, hzk⟩ := hzP
  exact ⟨h, hh, k, hk, hzk⟩

private theorem shultE610_three_dvd_alt {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : IsAltType L 3 ∨ IsAltType L 5) : 3 ∣ Nat.card L := by
  have hcard := Subgroup.card_mul_index (CFSG.pCore 2 ↥L)
  rcases h with h3 | h5
  · have hidx : (CFSG.pCore 2 ↥L).index = Nat.card (alternatingGroup (Fin 3)) :=
      shultE67_altcard h3
    rw [hidx, shultE67_card_alt3] at hcard
    exact Dvd.intro_left _ hcard
  · have hidx : (CFSG.pCore 2 ↥L).index = Nat.card (alternatingGroup (Fin 5)) :=
      shultE67_altcard h5
    rw [hidx, shultE67_card_alt5] at hcard
    rw [← hcard]
    exact dvd_mul_of_dvd_right (by norm_num) _

private theorem shultE610_pRank_le_two {G : Type} [Group G] [Finite G]
    (hq : CFSG.Open.evenRank G ≤ 2) {W : Subgroup G} (hWne : W ≠ ⊥) (hW2 : IsPGroup 2 W) :
    CFSG.Open.pRank 3 (Subgroup.normalizer (W : Set G)) ≤ 2 := by
  have hloc : CFSG.Open.pRank 3 (Subgroup.normalizer (W : Set G)) ≤
      CFSG.Assembly.RankThreeEven.localRank 3 G :=
    CFSG.RankThree.Classical.pRank_le_localRank (by norm_num) ⟨W, hWne, hW2, rfl⟩
  exact hloc.trans ((CFSG.SectionRank.QTK.localRank_le_evenRank Nat.prime_three (by norm_num)).trans
    hq)

private theorem shultE610_central_elt {Y : Type} [Group Y] [Finite Y] {Q N : Subgroup Y}
    (hQ : IsPGroup 3 Q) (hNQ : Q ≤ Subgroup.normalizer (N : Set Y)) (hN : N ⊓ Q ≠ ⊥) :
    ∃ y : Y, y ∈ N ∧ y ∈ Q ∧ (∀ q ∈ Q, q * y = y * q) ∧ y ≠ 1 ∧ y ^ 3 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQN : Q ≤ Subgroup.normalizer ((N ⊓ Q : Subgroup Y) : Set Y) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact ⟨(Subgroup.mem_normalizer_iff.1 (hNQ hg) x).1 hx.1,
        Q.mul_mem (Q.mul_mem hg hx.2) (Q.inv_mem hg)⟩
    · intro hx
      have h2 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      have h1 := (Subgroup.mem_normalizer_iff.1 (hNQ (Q.inv_mem hg)) (g * x * g⁻¹)).1 hx.1
      have h3 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ ∈ Q :=
        Q.mul_mem (Q.mul_mem (Q.inv_mem hg) hx.2) (Q.inv_mem (Q.inv_mem hg))
      rw [h2] at h1 h3
      exact ⟨h1, h3⟩
  have hne : (N ⊓ Q).subgroupOf Q ≠ ⊥ := by
    intro h0
    apply hN
    have hd := Subgroup.subgroupOf_eq_bot.1 h0
    rw [disjoint_iff, inf_eq_left.2 (inf_le_right : N ⊓ Q ≤ Q)] at hd
    exact hd
  haveI hnorm : ((N ⊓ Q).subgroupOf Q).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hQN
  haveI : Group.IsNilpotent Q := hQ.isNilpotent
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hzQ : ∀ q : ↥Q, q * z = z * q := fun q => Subgroup.mem_center_iff.1 hz.2 q
  have hzN : (z : Y) ∈ N := (Subgroup.mem_subgroupOf.1 hz.1).1
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext (by simpa using h))
  obtain ⟨f, hf⟩ := IsPGroup.iff_card.1 hQ
  have hdvd : orderOf z ∣ 3 ^ f := by
    rw [← hf]
    exact orderOf_dvd_natCard z
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hm
    exact hz1' hm
  have h3dvd : 3 ∣ orderOf z := by
    rw [hm]
    exact dvd_pow_self 3 hm0
  have hyord : orderOf (z ^ (orderOf z / 3)) = 3 :=
    orderOf_pow_orderOf_div (orderOf_pos z).ne' h3dvd
  have hw1 : z ^ (orderOf z / 3) ≠ 1 := fun h => by
    rw [h, orderOf_one] at hyord
    norm_num at hyord
  refine ⟨((z ^ (orderOf z / 3) : ↥Q) : Y), ?_, (z ^ (orderOf z / 3) : ↥Q).2, ?_, ?_, ?_⟩
  · rw [Subgroup.coe_pow]
    exact N.pow_mem hzN _
  · intro q hq
    have hc : Commute (⟨q, hq⟩ : ↥Q) z := hzQ ⟨q, hq⟩
    have := congrArg Subtype.val (hc.pow_right (orderOf z / 3)).eq
    simpa using this
  · exact fun h => hw1 (Subtype.ext h)
  · have h3Q : (z ^ (orderOf z / 3) : ↥Q) ^ 3 = 1 := by
      have hpow := pow_orderOf_eq_one (z ^ (orderOf z / 3) : ↥Q)
      rwa [hyord] at hpow
    rw [← Subgroup.coe_pow, h3Q, Subgroup.coe_one]

private theorem shultE610_rank_of_central {G : Type} [Group G] [Finite G] {W E : Subgroup G}
    (hE3 : CFSG.Open.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hEN : E ≤ Subgroup.normalizer (W : Set G)) (hEC : E ⊓ Subgroup.centralizer (W : Set G) = ⊥)
    {y : G} (hyC : y ∈ Subgroup.centralizer (W : Set G)) (hyE : ∀ e ∈ E, e * y = y * e)
    (hy1 : y ≠ 1) (hy3 : y ^ 3 = 1) :
    3 ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (W : Set G)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm' : ∀ h ∈ E, ∀ k ∈ Subgroup.zpowers y, h * k = k * h := by
    intro h hh k hk
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    have hc : Commute h y := hyE h hh
    exact (hc.zpow_right j).eq
  have hk3 : ∀ k ∈ Subgroup.zpowers y, k ^ 3 = 1 := by
    intro k hk
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
  have hAG : ∀ x ∈ E ⊔ Subgroup.zpowers y, ∀ z ∈ E ⊔ Subgroup.zpowers y, x * z = z * x := by
    intro x hx z hz
    obtain ⟨h1, hh1, k1, hk1, rfl⟩ := shultE67_mem_sup hcomm' hx
    obtain ⟨h2, hh2, k2, hk2, rfl⟩ := shultE67_mem_sup hcomm' hz
    have c12 : Commute h1 h2 :=
      congrArg Subtype.val (hE3.1.is_comm.comm (⟨h1, hh1⟩ : ↥E) ⟨h2, hh2⟩)
    have hk12 : Commute k1 k2 := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk1
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk2
      exact (Commute.refl y).zpow_zpow i j
    have hk_h : Commute k1 h2 := (hcomm' h2 hh2 k1 hk1).symm
    have hh_k : Commute h1 k2 := hcomm' h1 hh1 k2 hk2
    exact (Commute.mul_left (Commute.mul_right c12 hh_k) (Commute.mul_right hk_h hk12)).eq
  have hA3 : ∀ x ∈ E ⊔ Subgroup.zpowers y, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨h1, hh1, k1, hk1, rfl⟩ := shultE67_mem_sup hcomm' hx
    have hc : Commute h1 k1 := hcomm' h1 hh1 k1 hk1
    rw [hc.mul_pow, hE3.2 h1 hh1, hk3 k1 hk1, one_mul]
  set A : Subgroup G := E ⊔ Subgroup.zpowers y with hAdef
  have hAel : CFSG.Open.IsElemAbelian 3 A :=
    ⟨⟨⟨fun a b => Subtype.ext (hAG a a.2 b b.2)⟩⟩, fun x hx => hA3 x hx⟩
  have hAp : IsPGroup 3 ↥A := fun g => ⟨1, Subtype.ext (by simpa using hA3 g.1 g.2)⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hAp
  have hyA : y ∈ A :=
    (le_sup_right : Subgroup.zpowers y ≤ E ⊔ Subgroup.zpowers y) (Subgroup.mem_zpowers y)
  have hEA : E < A := by
    refine lt_of_le_of_ne le_sup_left (fun hEA' => ?_)
    have hyE' : y ∈ E := by
      rw [hEA']
      exact hyA
    have : y ∈ E ⊓ Subgroup.centralizer (W : Set G) := ⟨hyE', hyC⟩
    rw [hEC, Subgroup.mem_bot] at this
    exact hy1 this
  have hlt : Nat.card E < Nat.card A := Subgroup.card_lt_of_lt hEA
  rw [hE9, hm] at hlt
  have hm3 : 3 ≤ m := by
    by_contra hc
    push Not at hc
    interval_cases m <;> norm_num at hlt
  have hrange : (A.subtype : ↥A →* G).range ≤ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.range_subtype]
    exact sup_le hEN (Subgroup.zpowers_le.2 (Subgroup.centralizer_le_normalizer (W : Set G) hyC))
  have hle := CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num) (fun a b => by
      exact Subtype.ext (hAG a a.2 b b.2)) (fun a => by
      have := hA3 a.1 a.2
      exact Subtype.ext (by simpa using this)) hm A.subtype Subtype.val_injective hrange
  omega

private theorem shultE610_three_le_pRank {G : Type} [Group G] [Finite G] {W E : Subgroup G}
    (hE3 : CFSG.Open.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hEN : E ≤ Subgroup.normalizer (W : Set G)) (hEC : E ⊓ Subgroup.centralizer (W : Set G) = ⊥)
    (hC3 : 3 ∣ Nat.card (Subgroup.centralizer (W : Set G))) :
    3 ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (W : Set G)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup G := Subgroup.centralizer (W : Set G) with hCdef
  have hEC_n : ∀ e ∈ E, ∀ c ∈ C, e * c * e⁻¹ ∈ C := by
    intro e he c hc
    rw [hCdef, Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : e⁻¹ * w * e ∈ W := by
      have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ (hEN he)) w).1 hw
      simpa using h1
    have hcw := Subgroup.mem_centralizer_iff.1 (show c ∈ Subgroup.centralizer (W : Set G) from hc)
      _ hw'
    calc w * (e * c * e⁻¹) = e * ((e⁻¹ * w * e) * c) * e⁻¹ := by group
      _ = e * (c * (e⁻¹ * w * e)) * e⁻¹ := by rw [hcw]
      _ = (e * c * e⁻¹) * w := by group
  set X : Subgroup G := E ⊔ C with hXdef
  have hEX : ∀ e ∈ E, e ∈ X := fun e he => (le_sup_left : E ≤ X) he
  have hX_norm : X ≤ Subgroup.normalizer (C : Set G) := by
    rw [hXdef]
    refine sup_le (fun e he => ?_) (fun c hc => Subgroup.le_normalizer hc)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hEC_n e he x hx
    · intro hx
      have h1 := hEC_n e⁻¹ (Subgroup.inv_mem _ he) _ hx
      have h2 : e⁻¹ * (e * x * e⁻¹) * e⁻¹⁻¹ = x := by group
      rw [h2] at h1
      exact h1
  haveI hCn : (C.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hX_norm
  have hdecomp : ∀ x ∈ X, ∃ e ∈ E, ∃ c ∈ C, x = e * c := fun x hx =>
    shultE610_mem_sup_normal hEC_n hx
  have hEs : Nat.card (E.subgroupOf X) = 9 := by
    rw [← hE9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : E ≤ X)).toEquiv
  have hquot : Nat.card (↥X ⧸ C.subgroupOf X) = 9 := by
    have hbij : Function.Bijective
        ((QuotientGroup.mk' (C.subgroupOf X)).comp (E.subgroupOf X).subtype) := by
      refine ⟨?_, ?_⟩
      · rw [injective_iff_map_eq_one]
        intro a ha
        have haC : ((a : ↥X) : G) ∈ C :=
          Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 ha)
        have haE : ((a : ↥X) : G) ∈ E := Subgroup.mem_subgroupOf.1 a.2
        have hbot : ((a : ↥X) : G) ∈ E ⊓ C := ⟨haE, haC⟩
        rw [hEC, Subgroup.mem_bot] at hbot
        apply Subtype.ext
        apply Subtype.ext
        simpa using hbot
      · intro q
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf X) q
        obtain ⟨e, he, c, hc, hxec⟩ := hdecomp x.1 x.2
        refine ⟨⟨⟨e, hEX e he⟩, Subgroup.mem_subgroupOf.2 he⟩, ?_⟩
        show QuotientGroup.mk' (C.subgroupOf X) (⟨e, hEX e he⟩ : ↥X) =
          QuotientGroup.mk' (C.subgroupOf X) x
        apply QuotientGroup.eq.2
        rw [Subgroup.mem_subgroupOf]
        show ((⟨e, hEX e he⟩ : ↥X)⁻¹ * x : ↥X).1 ∈ C
        have hx' : ((⟨e, hEX e he⟩ : ↥X)⁻¹ * x : ↥X).1 = e⁻¹ * x.1 := by
          simp
        rw [hx', hxec, inv_mul_cancel_left]
        exact hc
    rw [← hEs]
    exact (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
  have hEs3 : IsPGroup 3 (E.subgroupOf X) := by
    intro g
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    have hgE : ((g : ↥X) : G) ∈ E := Subgroup.mem_subgroupOf.1 g.2
    have hg3 : ((g : ↥X) : G) ^ 3 = 1 := hE3.2 _ hgE
    simpa using hg3
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hEs3
  have hCs : Nat.card (C.subgroupOf X) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : C ≤ X)).toEquiv
  have hXcard : Nat.card ↥X = 9 * Nat.card (C.subgroupOf X) := by
    have h := Subgroup.card_mul_index (C.subgroupOf X)
    have hidx : (C.subgroupOf X).index = 9 := hquot
    rw [hidx] at h
    rw [← h, mul_comm]
  have h3C' : 3 ∣ Nat.card (C.subgroupOf X) := by
    rw [hCs]
    exact hC3
  have h27 : 3 ^ 3 ∣ Nat.card ↥X := by
    rw [hXcard]
    have h9 : (3 : ℕ) ^ 3 = 9 * 3 := by norm_num
    rw [h9]
    exact mul_dvd_mul_left 9 h3C'
  have hQcard : 27 ≤ Nat.card (Q : Subgroup ↥X) := by
    have hne : Nat.card ↥X ≠ 0 := Nat.card_pos.ne'
    rw [Sylow.card_eq_multiplicity Q]
    have h3f := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).1 h27
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ Nat.factorization (Nat.card ↥X) 3 := Nat.pow_le_pow_right (by norm_num) h3f
  have hP0 : (Q : Subgroup ↥X) ⊓ C.subgroupOf X ≠ ⊥ := by
    intro h0
    have hinj : Function.Injective
        ((QuotientGroup.mk' (C.subgroupOf X)).comp (Q : Subgroup ↥X).subtype) := by
      rw [injective_iff_map_eq_one]
      intro a ha
      have hmem : (a : ↥X) ∈ (Q : Subgroup ↥X) ⊓ C.subgroupOf X :=
        ⟨a.2, (QuotientGroup.eq_one_iff _).1 ha⟩
      rw [h0, Subgroup.mem_bot] at hmem
      apply Subtype.ext
      simpa using hmem
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [hquot] at hle
    omega
  have hNQ : (Q : Subgroup ↥X) ≤ Subgroup.normalizer ((C.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hCn.conj_mem x hx q
    · intro hx
      have h1 := hCn.conj_mem _ hx q⁻¹
      have h2 : q⁻¹ * (q * x * q⁻¹) * q⁻¹⁻¹ = x := by group
      rw [h2] at h1
      exact h1
  obtain ⟨yX, hyN, hyQ, hycen, hy1X, hy3X⟩ :=
    shultE610_central_elt Q.isPGroup' hNQ (by rw [inf_comm]; exact hP0)
  have hyC : (yX : G) ∈ C := Subgroup.mem_subgroupOf.1 hyN
  have hyE : ∀ e ∈ E, e * (yX : G) = (yX : G) * e := by
    intro e he
    have heX : (⟨e, hEX e he⟩ : ↥X) ∈ (Q : Subgroup ↥X) :=
      hQ (Subgroup.mem_subgroupOf.2 he)
    have := congrArg Subtype.val (hycen _ heX)
    simpa using this
  have hy1 : (yX : G) ≠ 1 := fun h => hy1X (Subtype.ext h)
  have hy3 : (yX : G) ^ 3 = 1 := by
    have := congrArg Subtype.val hy3X
    simpa using this
  exact shultE610_rank_of_central hE3 hE9 hEN hEC hyC hyE hy1 hy3

end ShultE610

section E6_10


theorem as_E_6_10
    : E_6_10 := by
  intro G _ _ T M V h U hU hm hcase
  classical
  have hUG : ASInputs.GammaE64 M V U := ⟨hU.2.1, hU.1, hU.2.2.1, hU.2.2.2⟩
  have hCU : CharTwo (Subgroup.centralizer (U : Set G)) := by
    rcases hcase with hZ | hch
    · exact E6.as_E_6_6_four_proved G T M V U h hUG hZ
    · exact hch
  have hTK : T ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.centralizer (U : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le hU.1)
  obtain ⟨s, Ls, hs, hchi, hcomm, -, hprod, h2, h3⟩ :=
    as_E_6_7 G T M V h U hU (Subgroup.centralizer (U : Set G)) hTK le_rfl hCU
  have halt : ∀ i, IsAltType (Ls i) 3 ∨ IsAltType (Ls i) 5 := by
    intro i
    rcases (hchi i).2 with ⟨n, hn, hlin⟩ | h3' | h5'
    · obtain ⟨_X, -, -, -, -, -, -, -, -, hle⟩ := h3 i n hn hlin
      rw [hm] at hle
      omega
    · exact Or.inl h3'
    · exact Or.inr h5'
  let ns : Fin s → ℕ := fun i => if IsAltType (Ls i) 3 then 3 else 5
  have hns : ∀ i, IsAltType (Ls i) (ns i) ∧ (ns i = 3 ∨ ns i = 5) := by
    intro i
    by_cases h3i : IsAltType (Ls i) 3
    · have hn3 : ns i = 3 := if_pos h3i
      exact ⟨by rw [hn3]; exact h3i, Or.inl hn3⟩
    · have h5i : IsAltType (Ls i) 5 := (halt i).resolve_left h3i
      have hn5 : ns i = 5 := if_neg h3i
      exact ⟨by rw [hn5]; exact h5i, Or.inr hn5⟩
  have hrel : ∀ i, M.relIndex (Ls i) = ns i := by
    intro i
    by_cases h3i : IsAltType (Ls i) 3
    · have hn3 : ns i = 3 := if_pos h3i
      rw [hn3]
      exact ((h2 i).1 h3i).2.1
    · have h5i : IsAltType (Ls i) 5 := (halt i).resolve_left h3i
      have hn5 : ns i = 5 := if_neg h3i
      rw [hn5]
      exact ((h2 i).2 h5i).2.1
  have hblock : ∀ i, IsBlock2 (Subgroup.centralizer (U : Set G)) (Ls i) ∧
      (ns i = 3 ∨ ns i = 5) ∧ IsAltType (Ls i) (ns i) ∧ M.relIndex (Ls i) = ns i :=
    fun i => ⟨(hchi i).1, (hns i).2, (hns i).1, hrel i⟩
  have hs1 : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · exfalso
      subst h0
      rw [iSup_of_empty, shultE67_mul_bot] at hprod
      refine hU.2.2.1 (fun x hx => ?_)
      have hx' : x ∈ ((Subgroup.centralizer (U : Set G) ⊓ M : Subgroup G) : Set G) := by
        rw [hprod]
        exact hx
      exact (Subgroup.mem_inf.1 hx').2
    · exact h0
  have h3U : 3 ∣ Nat.card (Subgroup.centralizer (U : Set G)) := by
    have hle := (hchi ⟨0, hs1⟩).1.2.1
    exact (shultE610_three_dvd_alt (halt ⟨0, hs1⟩)).trans (Subgroup.card_dvd_of_le hle)
  refine ⟨hCU, ⟨s, Ls, ns, hs, hblock, hcomm, hprod⟩, ?_, ?_⟩
  ·
    intro W hWU hEx
    obtain ⟨E, hE3, hE9, hEN, hEC⟩ := hEx
    by_cases hW0 : W = ⊥
    · have hEcen : E ≤ Subgroup.centralizer (W : Set G) := by
        intro e _
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [hW0, Subgroup.coe_bot, Set.mem_singleton_iff] at hw
        rw [hw, one_mul, mul_one]
      have hEbot : E = ⊥ := by
        rw [← inf_eq_left.2 hEcen, hEC]
      rw [hEbot, Subgroup.card_bot] at hE9
      norm_num at hE9
    · have hC3W : 3 ∣ Nat.card (Subgroup.centralizer (W : Set G)) :=
        h3U.trans (Subgroup.card_dvd_of_le (Subgroup.centralizer_le hWU))
      have hpW2 : IsPGroup 2 W := h.isPGroup_V.to_le (hWU.trans hU.1)
      have hlow := shultE610_three_le_pRank hE3 hE9 hEN hEC hC3W
      have hup := shultE610_pRank_le_two h.qtke.2.2 hW0 hpW2
      omega
  ·
    have hch4 : (V ⊓ Subgroup.centralizer (T : Set G)) ⊓ U ≠ ⊥ ∨
        CharTwo (Subgroup.centralizer (U : Set G)) := by
      rcases hcase with hZ | hch
      · left
        rwa [inf_comm]
      · right
        exact hch
    exact H13.ch6InE610Four_proved G T M V U h hU hm hch4

end E6_10

@[expose] def E_6_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U : Subgroup G) (h : E6.HypE61 T M V),
    U ∈ E6.gammaE64 V M →
    (∀ W : Subgroup G, W ≤ V → U < W → Subgroup.centralizer (W : Set G) ≤ M) →
    1 < E3.mQuot V U →
    ∃ L X : Subgroup G,
      (L ≤ Subgroup.centralizer (U : Set G) ∧
        (L.subgroupOf (Subgroup.centralizer (U : Set G))).Normal ∧
        ((Subgroup.centralizer (U : Set G) ⊓ M : Subgroup G) : Set G) * (L : Set G) =
          (Subgroup.centralizer (U : Set G) : Set G)) ∧
      (U ⊓ ⁅V, X⁆ = ⊥ ∧ U ⊔ ⁅V, X⁆ = V ∧ X ≤ L ⊓ M ∧ IsCyclic X ∧
        Nat.card X = 2 ^ E3.mQuot V U - 1 ∧ autI h.isElemAbelian X ≠ ⊥ ∧
        (∀ v ∈ ⁅V, X⁆, v ≠ 1 → ∀ x ∈ X, x * v * x⁻¹ = v → x ∈ Subgroup.centralizer (V : Set G)) ∧
        (∀ v ∈ ⁅V, X⁆, v ≠ 1 → ∀ w ∈ ⁅V, X⁆, w ≠ 1 → ∃ x ∈ X, x * v * x⁻¹ = w) ∧
        autI h.isElemAbelian (M ⊓ Subgroup.normalizer (U : Set G)) ≤
          Subgroup.normalizer (autI h.isElemAbelian X : Set (MulAut (IntMod V h.isElemAbelian))) ∧
        autI h.isElemAbelian X ≤ autI h.isElemAbelian (M ⊓ Subgroup.normalizer (U : Set G))) ∧
      ((CharTwo (Subgroup.centralizer (U : Set G)) ∧
          IsBlock2 (Subgroup.centralizer (U : Set G)) L ∧ IsLin2Type L (E3.mQuot V U) ∧
          M.relIndex L = 2 ^ E3.mQuot V U + 1) ∨
        ((CFSG.generalizedFitting ↥(Subgroup.centralizer (U : Set G))).map
              (Subgroup.centralizer (U : Set G)).subtype = pCoreOf 2 (Subgroup.centralizer (U : Set G)) ⊔ L ∧
          (CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 2
              (E3.mQuot V U) ∨
            CFSG.Blueprint.SuzukiModel (↥L ⧸ Subgroup.center ↥L) 2 (E3.mQuot V U) ∨
            CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2
              (E3.mQuot V U) ∨
            CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 2
              (E3.mQuot V U)) ∧
          E2.IsBorelIn L (M ⊓ L) ∧
          pCoreOf 2 L ⊔ ⁅V, X⁆ = centerOf (L ⊓ (T ⊓ Subgroup.centralizer (V : Set G)))) ∨
        ((CFSG.generalizedFitting ↥(Subgroup.centralizer (U : Set G))).map
              (Subgroup.centralizer (U : Set G)).subtype = pCoreOf 2 (Subgroup.centralizer (U : Set G)) ⊔ L ∧
          CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSp 2 2 (E3.mQuot V U) ∧
          IsMaxParabolic2 L (L ⊓ M) ∧ perfectCore (L ⊓ M) = L ⊓ Subgroup.centralizer (V : Set G) ∧
          ⁅V, X⁆ = rootGroupOfParabolic (L ⊓ M))) ∧
      Subgroup.centralizer (U : Set G) ⊓ Subgroup.centralizer (L : Set G) ≤
        M ⊓ Subgroup.centralizer (V : Set G)

section

theorem as_E_6_11
    : E_6_11 := by
  exact CFSG.Quasithin.RonanE611.e611_holds CFSG.Quasithin.E6.E68Proof.e68Stmt_holds
    CFSG.Quasithin.H13.VolI.asc129Statement_holds CFSG.Quasithin.H13.NQCat.e68BorelKernel_holds

end

@[expose] def E_6_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U : Subgroup G), E6.HypE61 T M V →
    U ≠ ⊥ → U ≤ V →
    M ⊓ Subgroup.centralizer (U : Set G) = M ⊓ Subgroup.centralizer (V : Set G) →
    ¬ Subgroup.centralizer (U : Set G) ≤ M →
      (∃ U₁ : Subgroup G, U ≤ U₁ ∧ U₁ ≤ V ∧ E3.mQuot V U₁ = 1 ∧
        ¬ Subgroup.centralizer (U₁ : Set G) ≤ M) ∧ rParam V = 1

section E6_12


theorem as_E_6_12
    : E_6_12 :=
  CFSG.Quasithin.E6.as_E_6_12_proved CFSG.Quasithin.H13.KG68.e68ComponentFacts_holds

end E6_12

@[expose] def E_6_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V W : Subgroup G), E6.HypE61 T M V →
    W ≠ ⊥ → W ≤ V →
    twoPrimeResidual (M ⊓ Subgroup.centralizer (W : Set G)) ≤ M ⊓ Subgroup.centralizer (V : Set G) →
    T ≤ Subgroup.normalizer (W : Set G) →
      Subgroup.centralizer (W : Set G) ≤ M ∧ W ∉ E6.gammaE64 V M

section

theorem as_E_6_13
    : E_6_13 := by
  intro G _ _ T M V W h hW1 hWV hres hWT
  have hC : Subgroup.centralizer (W : Set G) ≤ M :=
    CFSG.Quasithin.E6.e6_13 CFSG.Quasithin.H13.Frontier331.theorem311 h hWV hW1 hres hWT
  exact ⟨hC, fun hmem => hmem.2.2.1 hC⟩

end

@[expose] def E_6_14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V W M₀ : Subgroup G), E6.HypE61 T M V →
    W ≠ ⊥ → W ≤ V →
    twoPrimeResidual (M ⊓ Subgroup.centralizer (W : Set G)) ≤ M ⊓ Subgroup.centralizer (V : Set G) →
    (CharTwo (Subgroup.centralizer (W : Set G)) ∧
      (CFSG.Open.pRank 3 (Subgroup.centralizer (W : Set G)) ≤ 1 ∨
        ∃ R : Subgroup G, R ≤ Subgroup.normalizer (W : Set G) ∧ Nat.card R = 3 ∧
          R ⊓ Subgroup.centralizer (W : Set G) = ⊥)) →
    (T ≤ M₀ ∧ M₀ ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) ∧
      IsUniqueM M₀ M ∧ IsMaxSubgroupIn M₀ (M₀ ⊓ Subgroup.normalizer (W : Set G)) ∧
      (M₀ ⊓ Subgroup.normalizer (W : Set G)).relIndex M₀ ≠ 2) →
      Subgroup.centralizer (W : Set G) ≤ M ∧ W ∉ E6.gammaE64 V M

section

theorem as_E_6_14
    : E_6_14 := by
  intro G _ _ T M V W M₀ h hW1 hWV hres hii hiii
  have hii2 : CFSG.pRank 3 ↥(Subgroup.centralizer (W : Set G)) ≤ 1 ∨
      ∃ Y : Subgroup G, Y ≤ Subgroup.normalizer (W : Set G) ∧ Nat.card Y = 3 ∧
        Y ⊓ Subgroup.centralizer (W : Set G) = ⊥ := by
    rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_three]
    exact hii.2
  have hC : Subgroup.centralizer (W : Set G) ≤ M :=
    CFSG.Quasithin.E6.as_E_6_14_of CFSG.Quasithin.H13.VolI.asc129Statement_holds G T M V W M₀ h
      hW1 hWV hres hii.1 hii2 hiii.1 hiii.2.1 hiii.2.2.1 hiii.2.2.2.1 hiii.2.2.2.2
  exact ⟨hC, fun hmem => hmem.2.2.1 hC⟩

end

@[expose] def E_6_16 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V : Subgroup G) (h : E6.HypE61 T M V),
    E6.HypE615 h.isElemAbelian M → ∀ W : Subgroup G, W ≤ V → E3.mQuot V W = 1 →
      (¬ Subgroup.centralizer (W : Set G) ≤ M →
        rParam V = 1 ∧ 2 < mParam (autI h.isElemAbelian M) ∧ W ∈ E6.gammaE64 V M) ∧
      (oTwoUpper ((CFSG.generalizedFitting ↥(Subgroup.centralizer (W : Set G))).map
          (Subgroup.centralizer (W : Set G)).subtype) ≠ ⊥ →
        ¬ Subgroup.centralizer (W : Set G) ≤ M)

private theorem shultE6_gfEqPCore {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (h : CharTwo X) : CFSG.generalizedFitting ↥X = CFSG.pCore 2 ↥X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore ↥X 2).mp ?_
  intro x hx
  have hx' : (x : G) ∈ X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨x.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx r hr)
  obtain ⟨y, hy, hyx⟩ := h hx'
  rwa [← Subtype.ext hyx]

private theorem shultE6_oTwoUpperGfBot {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : CharTwo H) : oTwoUpper ((CFSG.generalizedFitting ↥H).map H.subtype) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [shultE6_gfEqPCore hH]
  refine le_antisymm (oTwoUpper_le_of_pow_mem fun x hx => ?_) bot_le
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H ⟨x, hx⟩
  exact ⟨k, Subgroup.mem_bot.2 (by simpa using congrArg Subtype.val hk)⟩

theorem as_E_6_16 : E_6_16 := by
  intro G _ _ T M V h h15 W hWV hW
  exact ⟨fun hC => E6.e6_16_one h.isElemAbelian h h15 hWV hW hC,
    fun hO => E6.e6_16_two h hWV fun hCH => hO (shultE6_oTwoUpperGfBot hCH)⟩

@[expose] def E_6_17 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V : Subgroup G) (h : E6.HypE61 T M V),
    E6.HypE615 h.isElemAbelian M → rParam V = 1 →
      2 < mParam (autI h.isElemAbelian M) ∧ 6 ≤ rk ↥V

section

theorem as_E_6_17
    : E_6_17 := by
  intro G _ _ T M V h h15 hr
  obtain ⟨h1, h2⟩ := CFSG.Quasithin.E6.e6_17 CFSG.Quasithin.H13.Frontier331.theorem311
    h.isElemAbelian h h15 hr
  refine ⟨h1, ?_⟩
  rw [CFSG.Quasithin.E6.mQuot_bot_eq_rk h.isElemAbelian] at h2
  exact h2

end

@[expose] def E_6_18 : Prop := E6.E618Stmt

section

theorem as_E_6_18
    : E_6_18 := by
  exact CFSG.Quasithin.E6.e618Stmt_holds

end

@[expose] def E_6_19 : Prop := E6.E619Stmt

section

theorem as_E_6_19
    : E_6_19 := by
  exact CFSG.Quasithin.E6.e619_of CFSG.Quasithin.H13.Frontier331.theorem311
    CFSG.QuasithinUnique.Ch1.lemma115_3_List_proved as_E_6_18 CFSG.Quasithin.E6.e619Insp_holds

end

@[expose] def E_6_20 : Prop := E6.E620Stmt

section

theorem as_E_6_20
    : E_6_20 := by
  exact CFSG.Quasithin.E6.e620_of CFSG.Quasithin.H13.Frontier331.theorem311 as_E_6_19

end

@[expose] def E_6_21 : Prop := E6.E621Stmt

section

theorem as_E_6_21
    : E_6_21 := by
  exact CFSG.Quasithin.E6.e621_of as_E_6_20

end

@[expose] def E_6_22 : Prop := E6.E622Stmt

section

theorem as_E_6_22
    : E_6_22 := by
  exact CFSG.Quasithin.E6.e622_of CFSG.Quasithin.H13.Frontier331.theorem311
    CFSG.QuasithinUnique.Ch1.lemma115_3_List_proved as_E_6_18 as_E_6_21
    CFSG.Quasithin.E6.Spor.e68CentComp_holds

end

@[expose] def E_6_23 : Prop := E6.E623Stmt

section

theorem as_E_6_23
    : E_6_23 := by
  have h311 := CFSG.Quasithin.H13.Frontier331.theorem311
  have hlist := CFSG.QuasithinUnique.Ch1.lemma115_3_List_proved
  have hI31 := CFSG.Quasithin.VolI.as_I_3_1_three_of CFSG.QuasithinUnique.Vol2Native.a36CoreForSQTKCat_proved
    CFSG.Quasithin.H13.A5.a38ForSQTKCat_holds
  have hC129 := CFSG.Quasithin.H13.VolI.asc129Statement_holds
  have h618 := CFSG.Quasithin.E6.e618Stmt_holds
  have h619 := CFSG.Quasithin.E6.e619_of h311 hlist h618 CFSG.Quasithin.E6.e619Insp_holds
  have h620 := CFSG.Quasithin.E6.e620_of h311 h619
  have h621 := CFSG.Quasithin.E6.e621_of h620
  have h622 := CFSG.Quasithin.E6.e622_of h311 hlist h618 h621 CFSG.Quasithin.E6.Spor.e68CentComp_holds
  have hOver := CFSG.Quasithin.E6.e623A6Over_of h311 hlist CFSG.Quasithin.E6.e623A6Insp_holds
  have hD := CFSG.Quasithin.E6.e623A6Detour_of_over h311 hI31 hOver
  have hA6 := CFSG.Quasithin.E6.e623A6Config_of_detour h311 hD
  have hLay := CFSG.Quasithin.E6.e623A3Layer_of h311 h618 h621 h622 CFSG.Quasithin.E6.E68Proof.e68Stmt_holds
    CFSG.Quasithin.H13.KGE623A3.e623CentA3Comp_holds hA6
  have hA3 := CFSG.Quasithin.E6.e623A3Dichotomy_of_layer h311 hC129 h621 hLay
  exact CFSG.Quasithin.E6.e623_of_kg h311 h622 CFSG.Quasithin.H13.VolI.a36ForSQTK_holds
    CFSG.QuasithinUnique.Vol2Native.a37ForSQTKCat_proved CFSG.Quasithin.H13.A5.a38ForSQTKCat_holds
    CFSG.QuasithinUnique.Vol2Native.a39ForSQTKCat_proved h621 CFSG.Quasithin.E6.E68Proof.e68Stmt_holds
    (CFSG.Quasithin.H13.KGE623.e623CentA5Block_of CFSG.Quasithin.H13.KGE623.sp44OrderThreeCent_holds)
    hC129 hA3

end

@[expose] def E_6_24 : Prop := E6.E624Stmt

section

theorem as_E_6_24 : E_6_24 := by
  exact CFSG.Quasithin.E6.e624_of CFSG.Quasithin.Asc81c.Pf.thm104

end

@[expose] def E_6_25 : Prop := E6.E625FullStmt

section

theorem as_E_6_25
    : E_6_25 := by
  intro G _ _ T M V U hV h hm _ hr _ hlt
  have hle := (as_E_6_3 G T M V h hm).1
  rw [← hr] at hle
  exact absurd (by exact_mod_cast hle) (not_le.2 hlt)

end

@[expose] def E_6_26 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V M H S : Subgroup G) (j : ℕ), IsSylowIn 2 T ⊤ →
    V ≠ ⊥ → IsElemAbelian 2 V → V ≤ T → T ≤ Subgroup.normalizer (V : Set G) →
    Subgroup.normalizer (V : Set G) ≤ M →
    IsUniqueM (Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) M →
    0 < j → nParam H ≤ (j : ℕ∞) → IsSylowIn 2 S H →
    T ⊓ Subgroup.centralizer (V : Set G) ≤ S → S ≤ T →
    (j : ℕ∞) < rParam V → thompsonJi S j ≤ S ⊓ Subgroup.centralizer (V : Set G) →
      H ≤ M ∧ Subgroup.normalizer (S : Set G) ≤ M

theorem as_E_6_26 : E_6_26 := by
  intro G _ _ T V M H S j hT hV1 hV hVT _ hNM hM hj hn hS hQS hST hr hJ
  by_cases hpS : j < CFSG.Open.pRank 2 S
  · have hJ' := hJ
    rw [CFSG.Quasithin.VolI.E54.thompsonJi_eq_thompsonJk hpS] at hJ'
    exact E6.e6_26 hT.2.1 hV1 hV hVT hNM hM hj hn hS hQS hST hr hJ'
  · push Not at hpS
    by_cases hNVt : Subgroup.normalizer (V : Set G) = ⊤
    · have hMt : M = ⊤ := eq_top_iff.2 (hNVt ▸ hNM)
      rw [hMt]
      exact ⟨le_top, le_top⟩
    · exfalso
      have hVQ : V ≤ T ⊓ Subgroup.centralizer (V : Set G) :=
        le_inf hVT fun v hv => Subgroup.mem_centralizer_iff.2 fun w hw =>
          B2F.isElemAbelian_comm hV hw hv
      have hVS : V ≤ S := hVQ.trans hQS
      have hC : ¬ Subgroup.centralizer ((⊥ : Subgroup G) : Set G) ≤
          Subgroup.normalizer (V : Set G) := fun hle =>
        hNVt (top_le_iff.1 fun g _ => hle (Subgroup.mem_centralizer_iff.2 fun x hx => by
          rw [Subgroup.mem_bot.1 (SetLike.mem_coe.1 hx), one_mul, mul_one]))
      have h1 := E6.rParam_le_mQuot (bot_le : (⊥ : Subgroup G) ≤ V) hC
      rw [E6.mQuot_bot_eq_rk hV] at h1
      have hcard := CFSG.Quasithin.VolI.E54.card_le_two_pow_pRank_of_le hVS hV
      have h2 : rk (IntMod V hV) ≤ CFSG.Open.pRank 2 S := by
        show padicValNat 2 (Nat.card V) ≤ _
        calc padicValNat 2 (Nat.card V) ≤ Nat.log 2 (Nat.card V) := padicValNat_le_nat_log _
          _ ≤ Nat.log 2 (2 ^ CFSG.Open.pRank 2 S) := Nat.log_mono_right hcard
          _ = CFSG.Open.pRank 2 S := Nat.log_pow (by norm_num) _
      have h3 : rParam V ≤ (j : ℕ∞) := h1.trans (by exact_mod_cast h2.trans hpS)
      exact absurd hr (not_lt.2 h3)

@[expose] def E_6_27 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U : Subgroup G) (h : E6.HypE61 T M V) (j : ℕ),
    U ≠ ⊥ → U ≤ V → 1 ≤ j → (j : ℕ∞) < rParam V →
    thompsonJi (M ⊓ Subgroup.centralizer (U : Set G)) j ≤ M ⊓ Subgroup.centralizer (V : Set G) →
    nPrime (autI h.isElemAbelian (M ⊓ Subgroup.centralizer (U : Set G))) ≤ j →
    (∀ X : Subgroup G, X ≤ M ⊓ Subgroup.centralizer (V : Set G) → X ≠ ⊥ → Odd (Nat.card X) →
      Subgroup.normalizer (X : Set G) ≤ M) →
      Subgroup.centralizer (U : Set G) ≤ M

section

theorem as_E_6_27
    : E_6_27 := by
  intro G _ _ T M V U h j hU1 hUV hj1 hr h2 h3 h4
  have hNV : Subgroup.normalizer (V : Set G) ≠ ⊤ := by
    intro htop
    haveI : V.Normal := Subgroup.normalizer_eq_top_iff.1 htop
    rcases h.simple.eq_bot_or_eq_top_of_normal V with hb | ht
    · exact h.ne_bot hb
    · obtain ⟨a, b, hab⟩ := h.nonabelian
      apply hab
      have ha : a ∈ V := by rw [ht]; exact Subgroup.mem_top a
      have hb : b ∈ V := by rw [ht]; exact Subgroup.mem_top b
      exact congrArg Subtype.val (h.isElemAbelian.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hCbot : (⊤ : Subgroup G) ≤ Subgroup.centralizer ((⊥ : Subgroup G) : Set G) := fun g _ =>
    Subgroup.mem_centralizer_iff.2 fun x hx => by
      rw [Subgroup.mem_bot.1 (SetLike.mem_coe.1 hx), one_mul, mul_one]
  have hCbotN : ¬ Subgroup.centralizer ((⊥ : Subgroup G) : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    fun hle => hNV (top_le_iff.1 (hCbot.trans hle))
  have h1 := CFSG.Quasithin.E6.rParam_le_mQuot (bot_le : (⊥ : Subgroup G) ≤ V) hCbotN
  rw [CFSG.Quasithin.E6.mQuot_bot_eq_rk h.isElemAbelian] at h1
  have hVMU : V ≤ M ⊓ Subgroup.centralizer (U : Set G) :=
    le_inf (h.le.trans h.inM.2) fun v hv => Subgroup.mem_centralizer_iff.2 fun u hu =>
      B2F.isElemAbelian_comm h.isElemAbelian (hUV hu) hv
  have hcard := CFSG.Quasithin.VolI.E54.card_le_two_pow_pRank_of_le hVMU h.isElemAbelian
  have hrk : rk (IntMod V h.isElemAbelian) ≤
      CFSG.Open.pRank 2 (M ⊓ Subgroup.centralizer (U : Set G)) := by
    show padicValNat 2 (Nat.card V) ≤ _
    calc padicValNat 2 (Nat.card V) ≤ Nat.log 2 (Nat.card V) := padicValNat_le_nat_log _
      _ ≤ Nat.log 2 (2 ^ CFSG.Open.pRank 2 (M ⊓ Subgroup.centralizer (U : Set G))) :=
          Nat.log_mono_right hcard
      _ = CFSG.Open.pRank 2 (M ⊓ Subgroup.centralizer (U : Set G)) := Nat.log_pow (by norm_num) _
  have hlt : j < CFSG.Open.pRank 2 (M ⊓ Subgroup.centralizer (U : Set G)) := by
    have hjr : (j : ℕ∞) < ((rk (IntMod V h.isElemAbelian) : ℕ) : ℕ∞) := lt_of_lt_of_le hr h1
    exact lt_of_lt_of_le (by exact_mod_cast hjr) hrk
  rw [CFSG.Quasithin.VolI.E54.thompsonJi_eq_thompsonJk hlt] at h2
  exact CFSG.Quasithin.E6.e6_27
    (CFSG.Quasithin.E6.parabolicTorusFact_of_e22C CFSG.Quasithin.H13.e22StatementC_holds
      CFSG.Quasithin.H13.e22TorusFacts_holds)
    h hU1 hUV (by omega) hr h2 h3 (fun X hX hX1 _ hodd => h4 X hX hX1 hodd)

end

@[expose] def E_6_28_image : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V : Subgroup G) (h : E6.HypE61 T M V),
    1 < rParam V → thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G) →
    (∀ X : Subgroup G, X ≤ M ⊓ Subgroup.centralizer (V : Set G) → X ≠ ⊥ → Odd (Nat.card X) →
      Subgroup.normalizer (X : Set G) ≤ M) →
    ∀ α β : ℕ∞,
      α = ⨅ U ∈ {U : Subgroup G | U ≤ V ∧ ¬ thompsonJi (M ⊓ Subgroup.normalizer (V : Set G) ⊓
          Subgroup.centralizer (U : Set G)) 1 ≤ M ⊓ Subgroup.centralizer (V : Set G)},
        (E3.mQuot V U : ℕ∞) →
      β = ⨅ U ∈ {U : Subgroup G | U ≤ V ∧
          1 < nPrime (autI h.isElemAbelian (M ⊓ Subgroup.centralizer (U : Set G)))},
        (E3.mQuot V U : ℕ∞) →
      min α β ≤ rParam V

@[expose] def E_6_28 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V : Subgroup G) (h : E6.HypE61 T M V),
    1 < rParam V → thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G) →
    (∀ X : Subgroup G, X ≤ M ⊓ Subgroup.centralizer (V : Set G) → X ≠ ⊥ → Odd (Nat.card X) →
      Subgroup.normalizer (X : Set G) ≤ M) →
    ∀ α β : ℕ∞,
      α = ⨅ U ∈ {U : Subgroup G | U ≤ V ∧ ¬ thompsonJi (M ⊓ Subgroup.normalizer (V : Set G) ⊓
          Subgroup.centralizer (U : Set G)) 1 ≤ M ⊓ Subgroup.centralizer (V : Set G)},
        (E3.mQuot V U : ℕ∞) →
      β = ⨅ U ∈ {U : Subgroup G | U ≤ V ∧
          1 < nPrime (M ⊓ Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer (U : Set G))},
        (E3.mQuot V U : ℕ∞) →
      min α β ≤ rParam V

section

theorem as_E_6_28_of_uniqueMBorelTorusR
    (hBT : CFSG.Quasithin.RonanE628.UniqueMBorelTorusR) :
    E_6_28 := by
  intro G _ _ T M V h hr hJ _ α β hα hβ
  exact CFSG.Quasithin.RonanE628.min_le_rParam
    (CFSG.Quasithin.E6.parabolicTorusFact_of_e22C CFSG.Quasithin.H13.e22StatementC_holds
      CFSG.Quasithin.H13.e22TorusFacts_holds)
    h hr (fun hC _ => CFSG.Quasithin.RonanE628.hres_of_holds_R hBT h hr hJ hC) hα hβ

theorem as_E_6_28_of_uniqueMBorelTorus
    (hBT : CFSG.Quasithin.RonanE628.UniqueMBorelTorus) :
    E_6_28 :=
  as_E_6_28_of_uniqueMBorelTorusR (CFSG.Quasithin.RonanE628.uniqueMBorelTorusR_of hBT)

end

section


theorem as_E_6_28
    : E_6_28 :=
  as_E_6_28_of_uniqueMBorelTorusR CFSG.Quasithin.RonanE628.MathAS4.uniqueMBorelTorusR_holds

end

end CFSG.ASVolI
