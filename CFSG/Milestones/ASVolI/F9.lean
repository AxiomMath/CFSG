module

public import CFSG.Milestones.ASVolI.F8
public import CFSG.Quasithin.Background.F9Six
public import CFSG.Quasithin.Background.F9Dual
public import CFSG.Quasithin.Background.RonanF9TAction
public import CFSG.Quasithin.Background.RonanF918FiveK
public import CFSG.Quasithin.Vol2.Ch3D310Holds
public import CFSG.Quasithin.Background.GoldschmidtD391
public import CFSG.Quasithin.Background.SmithB42G2IdFact
public import CFSG.Quasithin.Background.F918Fine4Pf
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.Quasithin.Background.F918D36Holds
public import CFSG.Quasithin.Background.SmithD321Holds
public import CFSG.Quasithin.Background.F918J6
public import CFSG.Quasithin.Vol2.Ch3T326PL
public import CFSG.Quasithin.Vol2.Ch1A3Proved
import CFSG.Quasithin.Background.RonanF914
import CFSG.Quasithin.Background.RonanF95Six
import CFSG.Quasithin.Background.RonanF918Normal
import CFSG.Quasithin.Background.RonanF918Clauses
import CFSG.Quasithin.Background.RonanF918Three
import CFSG.Quasithin.Background.RonanF918FiveNoFix
import CFSG.Quasithin.Background.RonanF918FiveDM

public section

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.CosetGeom CFSG.Quasithin.F7

abbrev HypF_9_1 {G : Type} [Group G] (T V L V₁ Vp H : Subgroup G) : Prop := HypF91 T V L V₁ Vp H

abbrev HypF_9_8 {G : Type} [Group G] (T V L V₁ Vp H : Subgroup G) : Prop := HypF98 T V L V₁ Vp H

@[expose] def IsQ8CentralPow (k : ℕ) (P : Type*) [Group P] : Prop :=
  Nat.card P = 2 ^ (2 * k + 1) ∧ ∃ Q : Fin k → Subgroup P,
    (∀ i j, i ≠ j → Q i ≤ Subgroup.centralizer (Q j : Set P)) ∧ (⨆ i, Q i) = ⊤ ∧
    ∀ i, Nonempty (↥(Q i) ≃* QuaternionGroup 2)

end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.CosetGeom CFSG.Quasithin.F7
open CFSG.ASVolI.ChF
open scoped Pointwise

private theorem exists_mem_pow_mul_eq {G : Type} [Group G] {A : Subgroup G} {a q : G}
    (ha : a ∈ A) (hq : q ∈ Subgroup.normalizer (A : Set G)) (m : ℕ) :
    ∃ a' ∈ A, (a * q) ^ m = a' * q ^ m := by
  induction m with
  | zero => exact ⟨1, A.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨a', ha', he⟩ := ih
    refine ⟨a' * (q ^ n * a * (q ^ n)⁻¹), A.mul_mem ha' ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (A : Set G)).pow_mem hq n) a).mp ha
    · rw [pow_succ (a * q) n, he, pow_succ q n]
      group

private theorem oTwoRes_sup_le_of_normalizes {G : Type} [Group G] {A Q : Subgroup G}
    (hQ : IsPGroup 2 Q) (hQA : Q ≤ Subgroup.normalizer (A : Set G)) :
    oTwoRes (A ⊔ Q) ≤ A := by
  have hmul : ((A ⊔ Q : Subgroup G) : Set G) = (A : Set G) * (Q : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left A Q hQA
  rw [oTwoRes, Subgroup.closure_le]
  rintro y ⟨hy, m, hm, hym⟩
  obtain ⟨a, ha, q, hq, rfl⟩ : y ∈ (A : Set G) * (Q : Set G) := by rw [← hmul]; exact hy
  obtain ⟨a', ha', he⟩ := exists_mem_pow_mul_eq ha (hQA hq) m
  have hqm : q ^ m ∈ A := by
    have h1 : a' * q ^ m = 1 := by rw [← he, hym]
    rw [eq_inv_of_mul_eq_one_right h1]
    exact A.inv_mem ha'
  obtain ⟨k, hk⟩ := hQ ⟨q, hq⟩
  have hqk : q ^ 2 ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  have hcop : m.Coprime (orderOf q) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hqk)
      (Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hm))
  obtain ⟨c, hc⟩ := exists_pow_eq_self_of_coprime hcop
  have hqA : q ∈ A := by
    rw [← hc]
    exact A.pow_mem hqm c
  exact A.mul_mem ha hqA

private theorem oTwoRes_oTwoRes_sup_eq {G : Type} [Group G] (X Q : Subgroup G)
    (hQ : IsPGroup 2 Q) (hQN : Q ≤ Subgroup.normalizer ((oTwoRes X : Subgroup G) : Set G)) :
    oTwoRes (oTwoRes X ⊔ Q) = oTwoRes X := by
  refine le_antisymm (oTwoRes_sup_le_of_normalizes hQ hQN) ?_
  show Subgroup.closure _ ≤ oTwoRes (oTwoRes X ⊔ Q)
  rw [Subgroup.closure_le]
  rintro x ⟨hxX, m, hm, hxm⟩
  exact Subgroup.subset_closure ⟨(le_sup_left : oTwoRes X ≤ oTwoRes X ⊔ Q)
    (Subgroup.subset_closure ⟨hxX, m, hm, hxm⟩), m, hm, hxm⟩

private theorem le_normalizer_inf_normalizer {G : Type} [Group G] {T L V₁ : Subgroup G}
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hTV : T ≤ Subgroup.normalizer (V₁ : Set G)) :
    T ≤ Subgroup.normalizer ((L ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hN : x ∈ Subgroup.normalizer (V₁ : Set G) ↔
      t * x * t⁻¹ ∈ Subgroup.normalizer (V₁ : Set G) := by
    constructor
    · intro hx
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hTV ht) hx) (Subgroup.inv_mem _ (hTV ht))
    · intro hx
      have h1 := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hTV ht)) hx) (hTV ht)
      have e : t⁻¹ * (t * x * t⁻¹) * t = x := by group
      rwa [e] at h1
  have hL := Subgroup.mem_normalizer_iff.mp (hTL ht) x
  simp only [SetLike.mem_coe, Subgroup.mem_inf]
  exact and_congr hL hN

private theorem le_normalizer_oTwoRes_of_le_normalizer {G : Type} [Group G] {X T : Subgroup G}
    (hTX : T ≤ Subgroup.normalizer (X : Set G)) :
    T ≤ Subgroup.normalizer ((oTwoRes X : Subgroup G) : Set G) := by
  intro t ht
  have hK : conjSub t X = X := F7.conjSub_eq_of_mem_normalizer (hTX ht)
  have hK' : conjSub t (oTwoRes X) = oTwoRes X := by rw [conjSub_oTwoRes, hK]
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h1 := mem_conjSub (g := t) (x := t * y * t⁻¹) (H := oTwoRes X)
  rw [hK', show t⁻¹ * (t * y * t⁻¹) * t = y by group] at h1
  exact h1.symm

private theorem oTwoRes_L₁Of_sup_T {G : Type} [Group G] {T L V₁ : Subgroup G}
    (hT : IsPGroup 2 T) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hTV : T ≤ Subgroup.normalizer (V₁ : Set G)) :
    oTwoRes (L₁Of L V₁ ⊔ T) = L₁Of L V₁ :=
  oTwoRes_oTwoRes_sup_eq (L ⊓ Subgroup.normalizer (V₁ : Set G)) T hT
    (le_normalizer_oTwoRes_of_le_normalizer (le_normalizer_inf_normalizer hTL hTV))

private theorem lt_of_mIdx_pos {G : Type} [Group G] {X Y : Subgroup G} (hYX : Y ≤ X)
    (h : 0 < CFSG.Quasithin.mIdx X Y) : Y < X := by
  refine lt_of_le_of_ne hYX fun e => ?_
  subst e
  simp [CFSG.Quasithin.mIdx] at h

private theorem mIdx_le_mIdx_bot {G : Type} [Group G] [Finite G] {X Y : Subgroup G}
    (hYX : Y ≤ X) : CFSG.Quasithin.mIdx X Y ≤ CFSG.Quasithin.mIdx X ⊥ := by
  unfold CFSG.Quasithin.mIdx
  have hd : Y.relIndex X ∣ (⊥ : Subgroup G).relIndex X :=
    Subgroup.relIndex_dvd_of_le_left X bot_le
  have hb : (⊥ : Subgroup G).relIndex X ≠ 0 := by
    show ((⊥ : Subgroup G).subgroupOf X).index ≠ 0
    exact Subgroup.index_ne_zero_of_finite
  exact (padicValNat_dvd_iff_le hb).mp (dvd_trans pow_padicValNat_dvd hd)

@[expose] def F_9_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ Vp H : Subgroup G), HypF_9_1 T V L V₁ Vp H →
    AlmostSpecialHyp Vp V₁ L T H ∧
    ((conjClosure Vp H ≤ pCoreOf 2 H ∧
        (∀ u ∈ conjClosure Vp H, ∀ q ∈ pCoreOf 2 H, u * q * u⁻¹ * q⁻¹ ∈ V₁) ∧
        ∀ u ∈ conjClosure Vp H, u ^ 2 ∈ V₁) ∧
      (∀ D : Subgroup G, D ≤ H → H ≤ Subgroup.normalizer (D : Set G) →
        (∀ d ∈ D, ∃ k : ℕ, d ^ 2 ^ k ∈ centralizerMod V₁ H (conjClosure Vp H)) →
          D ≤ centralizerMod V₁ H (conjClosure Vp H))) ∧
    frattiniOf (conjClosure Vp H) ≤ V₁ ∧
    (pCoreOf 2 H = centralizerMod V₁ H (conjClosure Vp H) ∧
      centralizerMod V₁ H (conjClosure Vp H) ≤ centralizerMod V₁ H Vp ∧
      centralizerMod V₁ H Vp ≤ H ⊓ Subgroup.normalizer (V : Set G)) ∧
    (HypF_7_6 ((L ⊔ T) ⊔ H) (L ⊔ T) H T V ∧ (L ⊔ T) ⊓ H = L₁Of L V₁ ⊔ T)

theorem as_F_9_2 : F_9_2 := by
  intro G _ _ T V L V₁ Vp H h
  have hA := h.amalgamHypV
  refine ⟨h.almostSpecialHyp, ⟨h.F92_1, fun D hDH hHD hD => h.F92_1_reduced hDH hHD hD⟩,
    h.F92_2, h.F92_3, ?_, h.LT_inf_H⟩
  exact ⟨⟨inferInstance, inferInstance, h.charTwo_LT, hA.sylow_inf, h.sylow_LT, h.sylow_H, rfl,
    h.o2_trivial⟩, h.reduced, h.cT.trans h.pCoreOf_LT_eq⟩

@[expose] def F_9_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ Vp H : Subgroup G), HypF_9_1 T V L V₁ Vp H →
    List.TFAE [V ≤ pCoreOf 2 H, V ≤ H ⊓ Subgroup.centralizer (conjClosure Vp H : Set G),
      V ≤ centralizerMod V₁ H (conjClosure Vp H)]

theorem as_F_9_3 : F_9_3 := by
  intro G _ _ T V L V₁ Vp H h
  exact HypF91.F93 h

@[expose] def F_9_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ Vp H : Subgroup G), HypF_9_1 T V L V₁ Vp H →
    (V ≤ pCoreOf 2 H → IsElemAbelian 2 (conjClosure Vp H)) ∧
    (⁅V, (H ⊓ Subgroup.centralizer (Vp : Set G)) ⊓ (H ⊓ Subgroup.normalizer (V : Set G))⁆ ≤ V₁ →
      (∀ x ∈ conjClosure Vp H, ∀ y ∈ conjClosure Vp H, x * y = y * x) → V ≤ pCoreOf 2 H) ∧
    ((H ⊓ Subgroup.centralizer (Vp : Set G)) ⊓ (H ⊓ Subgroup.normalizer (V : Set G)) =
        H ⊓ Subgroup.centralizer (V : Set G) →
      List.TFAE [V ≤ pCoreOf 2 H, IsElemAbelian 2 (conjClosure Vp H),
        IsElemAbelian 2 (conjClosure V H)])

theorem as_F_9_4 : F_9_4 := by
  intro G _ _ T V L V₁ Vp H h
  exact ⟨HypF91.F94_1 h, fun hcomm hab => HypF91.F94_2 h hcomm hab,
    fun hC => HypF91.F94_3 h hC⟩

@[expose] def F_9_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ Vp H : Subgroup G), HypF_9_1 T V L V₁ Vp H →
    Vp.relIndex V = 2 → ¬ V ≤ centralizerMod V₁ H (conjClosure Vp H) →
    (V ⊓ centralizerMod V₁ H (conjClosure Vp H)).relIndex V = 2 ∧
    (tildeOf V₁ ⁅pCoreOf 2 H, V⁆ = tildeOf V₁ Vp ∧
      tildeOf V₁ ⁅conjClosure Vp H, V⁆ = tildeOf V₁ Vp) ∧
    (centralizerMod (pCoreOf 2 H) H V = H ⊓ Subgroup.normalizer (Vp : Set G) ∧
      H ⊓ Subgroup.normalizer (Vp : Set G) = H ⊓ Subgroup.normalizer (V : Set G)) ∧
    (∀ k ∈ H, conjSub k⁻¹ V ≤ centralizerMod V₁ H (conjClosure Vp H) ⊔ V → conjSub k⁻¹ V = V) ∧
    ((∀ g ∈ H, V₁ < V ⊓ conjSub g⁻¹ V → IsPGroup 2 ↥(V ⊔ conjSub g⁻¹ V)) →
      ∀ h ∈ H,
        ¬ (∀ x ∈ V ⊔ conjSub h⁻¹ V,
            ∃ n : ℕ, x ^ 2 ^ n ∈ centralizerMod V₁ H (conjClosure Vp H)) →
        F95FiveConclusion V₁ Vp V H h ∧
        (⁅V, H ⊓ Subgroup.centralizer (Vp : Set G)⁆ ≤ V₁ →
          (Nat.card V = 2 ^ 4 →
            IsQ8CentralPow 2 ↥(Vp ⊔ conjSub h⁻¹ Vp) ∧
            Nonempty (↥(autOn (tildeOf V₁ (V ⊔ conjSub h⁻¹ V)) (tildeOf V₁ (conjClosure Vp H))) ≃*
              DihedralGroup 3)) ∧
          (Nat.card V = 2 ^ 6 →
            H ⊓ Subgroup.centralizer (Vp : Set G) = H ⊓ Subgroup.centralizer (V : Set G) →
            IsQ8CentralPow 4 ↥(Vp ⊔ conjSub h⁻¹ Vp) ∧
            (Nonempty (↥(autOn (tildeOf V₁ (V ⊔ conjSub h⁻¹ V)) (tildeOf V₁ (conjClosure Vp H))) ≃*
                DihedralGroup 3) ∨
              Nonempty (↥(autOn (tildeOf V₁ (V ⊔ conjSub h⁻¹ V)) (tildeOf V₁ (conjClosure Vp H))) ≃*
                DihedralGroup 5) ∨
              Nonempty (↥(autOn (tildeOf V₁ (V ⊔ conjSub h⁻¹ V)) (tildeOf V₁ (conjClosure Vp H))) ≃*
                DihedralGroup 6)))))

theorem as_F_9_5 : F_9_5 := by
  intro G _ _ T V L V₁ Vp H h hidx hVc
  have hQ := h.pCoreOf_eq_centralizerMod
  rw [← hQ] at hVc ⊢
  obtain ⟨hVp, -⟩ := h.F95_1 hidx hVc
  refine ⟨?_, h.F95_2 hidx hVc, h.F95_3 hidx hVc,
    fun k hk hVk => h.F95_4 hidx hVc hk hVk, fun hyp5 g hg hI => ⟨h.F95_5 hidx hVc hyp5 hg hI, ?_⟩⟩
  · rw [← hVp]
    exact hidx
  · exact fun hc => h.F95_six hidx hVc hyp5 hg hI hc

@[expose] def F_9_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ Vp H : Subgroup G), HypF_9_1 T V L V₁ Vp H →
    ∀ g ∈ L, conjSub g⁻¹ V₁ ≠ V₁ →
      (∀ y ∈ L ⊔ T, conjSub g⁻¹ V₁ = conjSub y⁻¹ V₁ →
        conjSub g⁻¹ H = conjSub y⁻¹ H ∧ conjSub g⁻¹ (pCoreOf 2 H) = conjSub y⁻¹ (pCoreOf 2 H) ∧
        conjSub g⁻¹ (conjClosure Vp H) = conjSub y⁻¹ (conjClosure Vp H) ∧
        conjSub g⁻¹ (conjClosure V H) = conjSub y⁻¹ (conjClosure V H)) ∧
      (∀ g₀ ∈ L, conjSub g₀⁻¹ V₁ = conjSub g⁻¹ V₁ → g₀ * g₀ ∈ L₁Of L V₁ ⊔ T →
        conjSub g₀⁻¹ (conjClosure Vp H ⊓ conjSub g⁻¹ (pCoreOf 2 H)) =
          conjSub g⁻¹ (conjClosure Vp H) ⊓ pCoreOf 2 H ∧
        conjSub g₀⁻¹ (conjClosure V H ⊓ conjSub g⁻¹ (pCoreOf 2 H)) =
          conjSub g⁻¹ (conjClosure V H) ⊓ pCoreOf 2 H) ∧
      (⁅conjClosure V H ⊓ conjSub g⁻¹ (pCoreOf 2 H), conjSub g⁻¹ (conjClosure Vp H)⁆ ≤
          conjSub g⁻¹ V₁ ∧
        ⁅conjClosure Vp H ⊓ conjSub g⁻¹ (pCoreOf 2 H),
          conjSub g⁻¹ (conjClosure Vp H) ⊓ pCoreOf 2 H⁆ = ⊥)

theorem as_F_9_6 : F_9_6 := by
  intro G _ _ T V L V₁ Vp H h g hg hne
  exact ⟨fun y hy hV => HypF91.F96_1 h hg hy hV,
    fun g₀ hg₀ hV hsq => HypF91.F96_2 h hg hg₀ hV.symm hsq, HypF91.F96_3 h hne⟩

@[expose] def F_9_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ Vp H : Subgroup G), HypF_9_1 T V L V₁ Vp H →
    IsElemAbelian 2 (conjClosure Vp H) →
    ((∀ x ∈ pCoreOf 2 H, ∀ u ∈ conjClosure Vp H, x * u * x⁻¹ * u⁻¹ ∈ V₁) ∧
      (∀ x ∈ pCoreOf 2 H, ∀ u ∈ conjClosure Vp H, ∀ u' ∈ conjClosure Vp H,
        x * (u * u') * x⁻¹ * (u * u')⁻¹ = (x * u * x⁻¹ * u⁻¹) * (x * u' * x⁻¹ * u'⁻¹)) ∧
      (∀ x ∈ pCoreOf 2 H, ∀ z ∈ conjClosure Vp H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G),
        x * z * x⁻¹ * z⁻¹ = 1) ∧
      (∀ x ∈ pCoreOf 2 H, ∀ y ∈ pCoreOf 2 H, ∀ u ∈ conjClosure Vp H,
        (x * y) * u * (x * y)⁻¹ * u⁻¹ = (x * u * x⁻¹ * u⁻¹) * (y * u * y⁻¹ * u⁻¹))) ∧
    (∀ x ∈ pCoreOf 2 H, (∀ u ∈ conjClosure Vp H, x * u * x⁻¹ * u⁻¹ = 1) ↔
      x ∈ pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure Vp H : Set G)) ∧
    (∀ f : ↥(conjClosure Vp H) →* ↥V₁,
      (∀ z : ↥(conjClosure Vp H), (z : G) ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) → f z = 1) →
      ∃ x ∈ pCoreOf 2 H, ∀ u : ↥(conjClosure Vp H), (f u : G) = x * u * x⁻¹ * u⁻¹) ∧
    (∀ h ∈ H, ∀ x ∈ pCoreOf 2 H, ∀ u ∈ conjClosure Vp H,
      (h * x * h⁻¹) * u * (h * x * h⁻¹)⁻¹ * u⁻¹ = x * (h⁻¹ * u * h) * x⁻¹ * (h⁻¹ * u * h)⁻¹)

theorem as_F_9_7 : F_9_7 := by
  intro G _ _ T V L V₁ Vp H hyp hU
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro x hx u hu
    exact hyp.commutator_mem_V₁ hx hu
  · intro x hx u hu u' hu'
    exact hyp.commutator_mul_right hx hu hu'
  · intro x hx z hz
    have hc : x * z = z * x := Subgroup.mem_centralizer_iff.mp hz.2 x hx
    rw [hc]
    group
  · intro x hx y hy u hu
    exact hyp.commutator_mul_left hx hy hu
  · intro x hx
    constructor
    · intro h1
      refine ⟨hx, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
      have e : x * u * x⁻¹ = u := mul_inv_eq_one.mp (h1 u hu)
      have h2 : x * u = (x * u * x⁻¹) * x := by group
      rw [e] at h2
      exact h2.symm
    · intro h1 u hu
      have hc : u * x = x * u := Subgroup.mem_centralizer_iff.mp h1.2 u hu
      have hc' : x * u = u * x := hc.symm
      rw [hc']
      group
  · intro f hf
    exact hyp.F97_surj hU f fun u hu =>
      hf u (Subgroup.mem_centralizer_iff.mpr fun x hx => hu x hx)
  · intro k hk x hx u hu
    have hu' : k⁻¹ * u * k ∈ conjClosure Vp H := by
      have h1 := (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_conjClosure Vp H (H.inv_mem hk)) u).mp hu
      simpa using h1
    have key := hyp.commutator_conj hk hx hu'
    rw [show k * (k⁻¹ * u * k) * k⁻¹ = u by group] at key
    exact key

@[expose] def F_9_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ H : Subgroup G),
    (HypF_8_1 T V L V₁ H ∧ Nat.card V₁ = 2) ↔ HypF_9_8 T V L V₁ V H

theorem as_F_9_9 : F_9_9 := by
  intro G _ _ T V L V₁ H
  exact ⟨fun h => HypF81.toHypF98 h.1 h.2, fun h => ⟨HypF98.toHypF81 h, h.toHypF91.card_V₁⟩⟩

@[expose] def F_9_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ Vp H : Subgroup G), HypF_9_8 T V L V₁ Vp H →
    conjClosure V H = Vv V (F8.γ₁ T L H) ∧
    ∃ γ : F8.Geom T L H, IsCriticalVertex ((L ⊔ T) ⊔ H) (L ⊔ T) H V γ

theorem as_F_9_10 : F_9_10 := by
  intro G _ _ T V L V₁ Vp H h
  obtain ⟨γ, hγ⟩ := exists_isCriticalVertex h.amalgamHypV h.V_ne_bot
  exact ⟨h.toHypF91.conjClosure_eq_Vv_γ₁, γ, hγ⟩

@[expose] def F_9_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ Vp H : Subgroup G), HypF_9_8 T V L V₁ Vp H →
    (3 ≤ F8.b T V L H ∧ Odd (F8.b T V L H)) ∧
    (∀ x ∈ conjClosure V H, ∀ y ∈ conjClosure V H, x * y = y * x) ∧
    (∀ x ∈ conjClosure Vp H, ∀ y ∈ conjClosure Vp H, x * y = y * x)

theorem as_F_9_11 : F_9_11 := by
  intro G _ _ T V L V₁ Vp H h
  exact ⟨h.three_le_b_and_odd, fun x hx y hy => isElemAbelian_comm h.F911_2 hx hy,
    fun x hx y hy => isElemAbelian_comm h.F911_3 hx hy⟩

@[expose] def F_9_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ Vp H : Subgroup G) (γ γ' : F8.Geom T L H)
    (g : ↥((L ⊔ T) ⊔ H)), HypF_9_8 T V L V₁ Vp H → F8Setup T V L H γ γ' g →
      conjSub (g : G) (L₁Of L V₁) = oTwoRes (stab γ' ⊓ stab γ)

theorem as_F_9_12 : F_9_12 := by
  intro G _ _ T V L V₁ Vp H γ γ' g hyp s
  have hstab : stab γ' ⊓ stab γ = conjSub (g : G) (L₁Of L V₁ ⊔ T) := by
    rw [← s.edge₁, ← s.edge₀, stab_smul, stab_smul, ← conjSub_inf, hyp.F913_1]
  rw [hstab, ← conjSub_oTwoRes,
    oTwoRes_L₁Of_sup_T hyp.sylow.2.1 hyp.normalizes_L hyp.T_normalizes_V₁]

@[expose] def F_9_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ Vp H : Subgroup G) (γ γ' : F8.Geom T L H)
    (g : ↥((L ⊔ T) ⊔ H)), HypF_9_8 T V L V₁ Vp H → F8Setup T V L H γ γ' g →
      stab (F8.γ₀ T L H) ⊓ stab (F8.γ₁ T L H) = L₁Of L V₁ ⊔ T ∧
      (conjClosure V H ≤ pCoreOf 2 (stab γ' ⊓ stab γ) ∧
        ∀ γ₂ ∈ nbrs (F8.γ₁ T L H), CosetGeom.dist γ γ₂ + 2 = F8.b T V L H →
          F8.Uγ V H (g : G) ≤ pCoreOf 2 (stab (F8.γ₁ T L H) ⊓ stab γ₂)) ∧
      (∀ X Y : Subgroup G, (X = Vp ∨ X = V) → (Y = Vp ∨ Y = V) →
        ⁅conjClosure X H, F8.Uγ Y H (g : G)⁆ ≤ conjClosure X H ⊓ F8.Uγ Y H (g : G)) ∧
      (F8.Uγ V H (g : G) ≤ Subgroup.normalizer (conjClosure V H : Set G) ∧
        F8.Uγ V H (g : G) ≤ Subgroup.normalizer (conjClosure Vp H : Set G)) ∧
      (¬ ⁅F8.Uγ Vp H (g : G), V⁆ ≤ F8.A₁ V₁ (g : G) ∧ V₁ ⊓ F8.A₁ V₁ (g : G) = ⊥) ∧
      (⁅F8.Uγ Vp H (g : G), F9.EH V Vp V₁ H (g : G)⁆ ≤ F8.A₁ V₁ (g : G) ∧
        ⁅conjClosure Vp H, F9.Eγ V Vp V₁ H (g : G)⁆ ≤ V₁) ∧
      ⁅F8.DH Vp V₁ H (g : G), F8.Dγ Vp V₁ H (g : G)⁆ = ⊥

theorem as_F_9_13 : F_9_13 := by
  intro G _ _ T V L V₁ Vp H γ γ' g hyp s
  exact ⟨hyp.F913_1, hyp.F913_2 s, fun X Y hX hY => hyp.F913_3 s hX hY, hyp.F913_4 s,
    ⟨hyp.F913_5a s, hyp.F913_5b s⟩, HypF98.F913_6 V Vp V₁ H (g : G), hyp.F913_7 s⟩

@[expose] def F_9_14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ Vp H : Subgroup G), HypF_9_8 T V L V₁ Vp H →
    (3 < F8.b T V L H →
      ∀ x ∈ conjClosure (conjClosure Vp H) L, ∀ y ∈ conjClosure (conjClosure Vp H) L,
        x * y = y * x) ∧
    (F8.b T V L H = 3 →
      ∃ l ∈ L, ∃ v ∈ conjClosure V H, ∃ u ∈ conjSub l (conjClosure Vp H), v * u ≠ u * v) ∧
    ((V ≤ conjClosure Vp H ∨
        H ⊓ Subgroup.centralizer (Vp : Set G) ≤ Subgroup.centralizer (V : Set G) ∨
        (∀ x ∈ H ⊓ Subgroup.centralizer (Vp : Set G), ⁅V, Subgroup.zpowers x⁆ ≠ ⊥ →
          ∀ g : G, conjSub g⁻¹ V ≤ Subgroup.normalizer ((⁅V, Subgroup.zpowers x⁆ : Subgroup G) : Set G) →
            conjSub g⁻¹ V ≤ Subgroup.centralizer (V : Set G))) →
      ((∀ x ∈ conjClosure (conjClosure Vp H) L, ∀ y ∈ conjClosure (conjClosure Vp H) L,
          x * y = y * x) ↔ 3 < F8.b T V L H)) ∧
    ∀ (γ γ' : F8.Geom T L H) (g : ↥((L ⊔ T) ⊔ H)), F8Setup T V L H γ γ' g →
      (F8.b T V L H = 3 → ∃ k ∈ H, F8.A₁ V₁ (g : G) ≤ conjSub k⁻¹ V) ∧
      ((∀ v ∈ V, ∀ w ∈ V, v ≠ 1 → w ≠ 1 → ∃ l ∈ L, l * v * l⁻¹ = w) →
        H = Subgroup.centralizer (V₁ : Set G) →
        ∀ k ∈ H, conjSub k⁻¹ (F8.A₁ V₁ (g : G)) ≤ V →
          F8.b T V L H = 3 ∧
          ∃ l ∈ L, conjSub k⁻¹ (F8.Uγ Vp H (g : G)) = conjSub l (conjClosure Vp H))

theorem as_F_9_14 : F_9_14 := by
  intro G _ _ T V L V₁ Vp H hyp
  refine ⟨fun hb x hx y hy => isElemAbelian_comm (hyp.F914_1_of_lt hb) hx hy,
    hyp.exists_noncomm_of_b_eq_three, RonanF914.F914_1' hyp, ?_⟩
  intro γ γ' g s
  exact ⟨hyp.F914_2 s, fun htrans hH k hk hA => hyp.F914_3 s htrans hH hk hA⟩

@[expose] def F_9_15 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ Vp H : Subgroup G) (γ γ' : F8.Geom T L H)
    (g : ↥((L ⊔ T) ⊔ H)), HypF_9_8 T V L V₁ Vp H → F8Setup T V L H γ γ' g →
      conjClosure V H ⊓ ballStab 1 γ = F9.EH V Vp V₁ H (g : G) ∧
      F8.Uγ V H (g : G) ⊓ ballStab 1 (F8.γ₁ T L H) = F9.Eγ V Vp V₁ H (g : G)

theorem as_F_9_15 : F_9_15 := by
  intro G _ _ T V L V₁ Vp H γ γ' g hyp s
  exact ⟨hyp.F915_1 s, hyp.F915_2 s⟩

@[expose] def F_9_16 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ Vp H : Subgroup G) (hyp : HypF_9_8 T V L V₁ Vp H),
    (∀ (γ γ' : F8.Geom T L H) (g : ↥((L ⊔ T) ⊔ H)), F8Setup T V L H γ γ' g →
      F8.Uγ Vp H (g : G) = F8.Dγ Vp V₁ H (g : G) →
        (F8.DH Vp V₁ H (g : G) < conjClosure Vp H ∧
          IsTransvectionGroupOn (conjClosure Vp H) (F8.Uγ Vp H (g : G)) V₁) ∨
        (F8.DH Vp V₁ H (g : G) = conjClosure Vp H ∧
          ⁅conjClosure Vp H, F8.Uγ Vp H (g : G)⁆ = ⊥ ∧
          IsTransvectionGroupOn V (F8.Uγ Vp H (g : G)) V₁)) ∧
    (∀ (γ γ' : F8.Geom T L H) (g : ↥((L ⊔ T) ⊔ H)), F8Setup T V L H γ γ' g →
      0 < mIdx (F8.Uγ Vp H (g : G)) (F8.Dγ Vp V₁ H (g : G)) →
      mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (g : G)) ≤
        mIdx (F8.Uγ Vp H (g : G)) (F8.Dγ Vp V₁ H (g : G)) →
        autOn (tildeOf V₁ (F8.Uγ Vp H (g : G))) (tildeOf V₁ (conjClosure Vp H)) ∈
          @Qset ↥(tildeOf V₁ (conjClosure Vp H))
            (commGroupOfElemAbelian hyp.toHypF91.isElemAbelian_tilde)
            (autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H))) ∧
        (2 * mIdx (F8.Uγ Vp H (g : G)) (F8.Dγ Vp V₁ H (g : G)) =
            mIdx (conjClosure Vp H) (centralizerMod V₁ (conjClosure Vp H) (F8.Uγ Vp H (g : G))) →
          mIdx (F8.Uγ Vp H (g : G)) (F8.Dγ Vp V₁ H (g : G)) =
              mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (g : G)) ∧
            centralizerMod V₁ (F8.Uγ Vp H (g : G)) (F8.DH Vp V₁ H (g : G)) =
              F8.Dγ Vp V₁ H (g : G) ∧
            ⁅F8.Uγ Vp H (g : G), F8.DH Vp V₁ H (g : G)⁆ ≤ F8.A₁ V₁ (g : G) ∧
            Nat.card (F8.A₁ V₁ (g : G)) = 2 ∧ F8.A₁ V₁ (g : G) ⊓ V₁ = ⊥ ∧
            F8.Dγ Vp V₁ H (g : G) < F8.Uγ Vp H (g : G))) ∧
    (qInt (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H)) hyp.toHypF91.isElemAbelian_tilde ≤ 2 ∧
      ∃ B : Subgroup G, B ≤ pCoreOf 2 (L₁Of L V₁ ⊔ T) ∧
        autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure Vp H)) ∈
          @Qset ↥(tildeOf V₁ (conjClosure Vp H))
            (commGroupOfElemAbelian hyp.toHypF91.isElemAbelian_tilde)
            (autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H)))) ∧
    (∀ (γ γ' : F8.Geom T L H) (g : ↥((L ⊔ T) ⊔ H)), F8Setup T V L H γ γ' g →
      F8.Dγ Vp V₁ H (g : G) < F8.Uγ Vp H (g : G) →
        ∃ (δ δ' : F8.Geom T L H) (k : ↥((L ⊔ T) ⊔ H)), F8Setup T V L H δ δ' k ∧
          0 < mIdx (F8.Uγ Vp H (k : G)) (F8.Dγ Vp V₁ H (k : G)) ∧
          mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (k : G)) ≤
            mIdx (F8.Uγ Vp H (k : G)) (F8.Dγ Vp V₁ H (k : G)) ∧
          autOn (tildeOf V₁ (F8.Uγ Vp H (k : G))) (tildeOf V₁ (conjClosure Vp H)) ∈
            @Qset ↥(tildeOf V₁ (conjClosure Vp H))
              (commGroupOfElemAbelian hyp.toHypF91.isElemAbelian_tilde)
              (autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H))))

theorem as_F_9_16 : F_9_16 := by
  intro G _ _ T V L V₁ Vp H hyp
  exact ⟨fun γ γ' g s hD => hyp.F916_1 s hD, fun γ γ' g s hpos hle => hyp.F916_2 s hpos hle,
    hyp.F916_3, fun γ γ' g s hlt => hyp.F916_4 s hlt⟩

@[expose] def F_9_17 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ Vp H : Subgroup G) (γ γ' : F8.Geom T L H)
    (g : ↥((L ⊔ T) ⊔ H)), HypF_9_8 T V L V₁ Vp H → F8Setup T V L H γ γ' g →
      0 < mIdx (F8.Uγ Vp H (g : G)) (F8.Dγ Vp V₁ H (g : G)) →
        (¬ F8.Uγ V H (g : G) ≤ ballStab 1 (F8.γ₁ T L H) ∧
          ∃ β ∈ nbrs γ, ¬ Vv V β ≤ ballStab 1 (F8.γ₁ T L H) ∧
            CosetGeom.dist β (F8.γ₁ T L H) = F8.b T V L H) ∧
        ∃ (β δ δ' : F8.Geom T L H) (k y : ↥((L ⊔ T) ⊔ H)),
          β ∈ nbrs γ ∧ β ≠ γ' ∧
          ¬ Vv V β ≤ ballStab 1 (F8.γ₁ T L H) ∧
          CosetGeom.dist β (F8.γ₁ T L H) = F8.b T V L H ∧
          F8Setup T V L H δ δ' k ∧
          y • β = F8.γ₀ T L H ∧ y • γ = F8.γ₁ T L H ∧
          y • F8.γ₁ T L H = δ ∧
          conjSub (y : G) (conjClosure Vp H) = F8.Uγ Vp H (k : G) ∧
          conjSub (y : G) (F8.Uγ Vp H (g : G)) = conjClosure Vp H ∧
          conjSub (y : G) (conjClosure V H) = F8.Uγ V H (k : G) ∧
          conjSub (y : G) (F8.Uγ V H (g : G)) = conjClosure V H ∧
          conjSub (y : G) V₁ = F8.A₁ V₁ (k : G) ∧
          conjSub (y : G) (F8.A₁ V₁ (g : G)) = V₁ ∧
          conjSub (y : G) (F8.Dγ Vp V₁ H (g : G)) = F8.DH Vp V₁ H (k : G) ∧
          conjSub (y : G) (F8.DH Vp V₁ H (g : G)) = F8.Dγ Vp V₁ H (k : G) ∧
          mIdx (F8.Uγ Vp H (k : G)) (F8.Dγ Vp V₁ H (k : G)) =
            mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (g : G)) ∧
          mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (k : G)) =
            mIdx (F8.Uγ Vp H (g : G)) (F8.Dγ Vp V₁ H (g : G)) ∧
          (∃ (ε ε' : F8.Geom T L H) (a : ↥((L ⊔ T) ⊔ H)),
            ((ε = γ ∧ ε' = γ' ∧ a = g) ∨ (ε = δ ∧ ε' = δ' ∧ a = k)) ∧
            F8Setup T V L H ε ε' a ∧
            0 < mIdx (F8.Uγ Vp H (a : G)) (F8.Dγ Vp V₁ H (a : G)) ∧
            mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (a : G)) ≤
              mIdx (F8.Uγ Vp H (a : G)) (F8.Dγ Vp V₁ H (a : G))) ∧
          (mIdx (F8.Uγ Vp H (g : G)) ⊥ =
              mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (g : G)) →
            mIdx (F8.Uγ Vp H (g : G)) (F8.Dγ Vp V₁ H (g : G)) ≤
              mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (g : G))) ∧
          ((mIdx (F8.Uγ Vp H (g : G)) (F8.Dγ Vp V₁ H (g : G)) =
              mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (g : G)) ∨
            mIdx (F8.Uγ Vp H (g : G)) ⊥ =
              mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (g : G))) →
            (∀ S : F8.Geom T L H → F8.Geom T L H → Prop,
              (∀ (x : ↥((L ⊔ T) ⊔ H)) (α ζ : F8.Geom T L H),
                S (x • α) (x • ζ) ↔ S α ζ) →
              (∀ (ζ ζ' : F8.Geom T L H) (a : ↥((L ⊔ T) ⊔ H)),
                F8Setup T V L H ζ ζ' a →
                0 < mIdx (F8.Uγ Vp H (a : G)) (F8.Dγ Vp V₁ H (a : G)) →
                mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (a : G)) ≤
                  mIdx (F8.Uγ Vp H (a : G)) (F8.Dγ Vp V₁ H (a : G)) →
                S (F8.γ₁ T L H) ζ) → S γ (F8.γ₁ T L H)) ∧
            (∀ S : F8.Geom T L H → F8.Geom T L H → F8.Geom T L H → Prop,
              (∀ (x : ↥((L ⊔ T) ⊔ H)) (α ζ η : F8.Geom T L H),
                S (x • α) (x • ζ) (x • η) ↔ S α ζ η) →
              (∀ (ζ ζ' : F8.Geom T L H) (a : ↥((L ⊔ T) ⊔ H)),
                F8Setup T V L H ζ ζ' a →
                0 < mIdx (F8.Uγ Vp H (a : G)) (F8.Dγ Vp V₁ H (a : G)) →
                mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (a : G)) ≤
                  mIdx (F8.Uγ Vp H (a : G)) (F8.Dγ Vp V₁ H (a : G)) →
                S (F8.γ₀ T L H) (F8.γ₁ T L H) ζ) →
              S β γ (F8.γ₁ T L H)))

theorem as_F_9_17 : F_9_17 := by
  intro G _ _ T V L V₁ Vp H γ γ' g hyp s hpos
  have hA := hyp.amalgamHypV
  have hlt : F8.Dγ Vp V₁ H (g : G) < F8.Uγ Vp H (g : G) :=
    lt_of_mIdx_pos (centralizerMod_le_left _ _ _) hpos
  have hn := hyp.not_Vγ_le_ballStab_of_lt s hlt
  obtain ⟨β, hβ, hnl⟩ := hyp.exists_nbr_not_le_ballStab s hn
  have hdβ : CosetGeom.dist β (F8.γ₁ T L H) = F8.b T V L H :=
    hyp.dist_eq_of_not_le_ballStab s hβ hnl
  have hβne : β ≠ γ' := by
    intro e
    rw [e] at hdβ
    have h2 := s.geodesic
    rw [CosetGeom.dist_comm] at hdβ
    omega
  have hadj : (graph ((L ⊔ T) ⊔ H) (L ⊔ T) H).Adj β γ := SimpleGraph.Adj.symm hβ
  have hvtγ : vtype γ = true := by rw [← s.edge₁, vtype_smul, vtype_γ₁]
  obtain ⟨x, ⟨hx0, hx1⟩ | ⟨hx0, hx1⟩⟩ := exists_smul_edge hadj
  swap
  · exfalso
    have := congrArg vtype hx0
    rw [vtype_smul, vtype_γ₀, hvtγ] at this
    exact absurd this (by decide)
  have hyγ : x⁻¹ • γ = F8.γ₁ T L H := by rw [← hx1, inv_smul_smul]
  have hxβ : x⁻¹ • β = F8.γ₀ T L H := by rw [← hx0, inv_smul_smul]
  have hcrit : IsCriticalVertex ((L ⊔ T) ⊔ H) (L ⊔ T) H V (x⁻¹ • F8.γ₁ T L H) := by
    refine ⟨?_, ?_, ?_⟩
    · have hd := dist_smul x (F8.γ₀ T L H) (x⁻¹ • F8.γ₁ T L H)
      rw [hx0, smul_inv_smul] at hd
      exact hd.symm.trans hdβ
    · intro hle
      apply hnl
      rw [← hx0, Vv_smul_γ₀ hA.normalizes]
      have := conjSub_mono (x : G) hle
      rwa [← ballStab_smul, smul_inv_smul] at this
    · have hd := dist_smul x (F8.γ₁ T L H) (x⁻¹ • F8.γ₁ T L H)
      rw [hx1, smul_inv_smul] at hd
      have := s.critical.geodesic
      rw [CosetGeom.dist_comm] at hd
      rw [← hd]; exact this
  obtain ⟨δ', k, sk⟩ := hyp.exists_F8Setup_of_critical hcrit
  have hk₁ : (((x⁻¹ * g : ↥((L ⊔ T) ⊔ H)) : ↥((L ⊔ T) ⊔ H)) : G) ∈ H := by
    have h1 : (x⁻¹ * g) • F8.γ₁ T L H = F8.γ₁ T L H := by
      rw [mul_smul, s.edge₁, hyγ]
    have := mem_stab_of_smul_eq h1
    rwa [stab_γ₁ hA.le₂] at this
  have hk₂ : (((k⁻¹ * x⁻¹ : ↥((L ⊔ T) ⊔ H)) : ↥((L ⊔ T) ⊔ H)) : G) ∈ H := by
    have h1 : (k⁻¹ * x⁻¹) • F8.γ₁ T L H = F8.γ₁ T L H := by
      rw [mul_smul, ← sk.edge₁, inv_smul_smul]
    have := mem_stab_of_smul_eq h1
    rwa [stab_γ₁ hA.le₂] at this
  have hk₁' : ((x : G))⁻¹ * (g : G) ∈ H := by simpa using hk₁
  have hk₂' : ((k : G))⁻¹ * ((x : G))⁻¹ ∈ H := by simpa using hk₂
  have eU : conjSub (x : G)⁻¹ (conjClosure Vp H) = F8.Uγ Vp H (k : G) := by
    have e : (x : G)⁻¹ = (k : G) * ((k : G)⁻¹ * (x : G)⁻¹) := by group
    rw [F8.Uγ, e, conjSub_mul, F7.conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure Vp H hk₂')]
  have eUV : conjSub (x : G)⁻¹ (conjClosure V H) = F8.Uγ V H (k : G) := by
    have e : (x : G)⁻¹ = (k : G) * ((k : G)⁻¹ * (x : G)⁻¹) := by group
    rw [F8.Uγ, e, conjSub_mul, F7.conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure V H hk₂')]
  have eV : conjSub (x : G)⁻¹ V₁ = conjSub (k : G) V₁ := by
    have e : (x : G)⁻¹ = (k : G) * ((k : G)⁻¹ * (x : G)⁻¹) := by group
    rw [e, conjSub_mul, F7.conjSub_eq_of_mem_normalizer (hyp.H_normalizes_V₁ hk₂')]
  have eB : conjSub (x : G)⁻¹ (F8.Uγ Vp H (g : G)) = conjClosure Vp H := by
    rw [F8.Uγ, ← conjSub_mul, F7.conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure Vp H hk₁')]
  have eBV : conjSub (x : G)⁻¹ (F8.Uγ V H (g : G)) = conjClosure V H := by
    rw [F8.Uγ, ← conjSub_mul, F7.conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure V H hk₁')]
  have eA : conjSub (x : G)⁻¹ (F8.A₁ V₁ (g : G)) = V₁ := by
    rw [F8.A₁, ← conjSub_mul, F7.conjSub_eq_of_mem_normalizer (hyp.H_normalizes_V₁ hk₁')]
  have eDk : F8.DH Vp V₁ H (k : G) = conjSub (x : G)⁻¹ (F8.Dγ Vp V₁ H (g : G)) := by
    rw [F8.DH, F8.Dγ, conjSub_centralizerMod, eB, ← eU, eV]
    rfl
  have eDγ : F8.Dγ Vp V₁ H (k : G) = conjSub (x : G)⁻¹ (F8.DH Vp V₁ H (g : G)) := by
    rw [F8.Dγ, F8.DH, conjSub_centralizerMod, eA, eB, ← eU]
  have hm1 : mIdx (F8.Uγ Vp H (k : G)) (F8.Dγ Vp V₁ H (k : G)) =
      mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (g : G)) := by
    rw [← eU, eDγ, F9.mIdx_conjSub]
  have hm2 : mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (k : G)) =
      mIdx (F8.Uγ Vp H (g : G)) (F8.Dγ Vp V₁ H (g : G)) := by
    rw [eDk, ← eB, F9.mIdx_conjSub]
  have hbot : mIdx (F8.Uγ Vp H (g : G)) (F8.Dγ Vp V₁ H (g : G)) ≤
      mIdx (F8.Uγ Vp H (g : G)) ⊥ :=
    mIdx_le_mIdx_bot (centralizerMod_le_left _ _ _)
  have hbotB : mIdx (F8.Uγ Vp H (g : G)) ⊥ =
      mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (g : G)) →
      mIdx (F8.Uγ Vp H (g : G)) (F8.Dγ Vp V₁ H (g : G)) ≤
        mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (g : G)) :=
    fun hB => hbot.trans hB.le
  have hpd : (mIdx (F8.Uγ Vp H (g : G)) (F8.Dγ Vp V₁ H (g : G)) =
        mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (g : G)) ∨
      mIdx (F8.Uγ Vp H (g : G)) ⊥ = mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (g : G))) →
      0 < mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (g : G)) ∧
        mIdx (F8.Uγ Vp H (g : G)) (F8.Dγ Vp V₁ H (g : G)) ≤
          mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (g : G)) := by
    rintro (h | h)
    · exact ⟨by rw [← h]; exact hpos, h.le⟩
    · exact ⟨lt_of_lt_of_le hpos (hbot.trans h.le), hbot.trans h.le⟩
  have hex : ∃ (ε ε' : F8.Geom T L H) (a : ↥((L ⊔ T) ⊔ H)),
      ((ε = γ ∧ ε' = γ' ∧ a = g) ∨ (ε = x⁻¹ • F8.γ₁ T L H ∧ ε' = δ' ∧ a = k)) ∧
      F8Setup T V L H ε ε' a ∧
      0 < mIdx (F8.Uγ Vp H (a : G)) (F8.Dγ Vp V₁ H (a : G)) ∧
      mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (a : G)) ≤
        mIdx (F8.Uγ Vp H (a : G)) (F8.Dγ Vp V₁ H (a : G)) := by
    by_cases hc : mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (g : G)) ≤
        mIdx (F8.Uγ Vp H (g : G)) (F8.Dγ Vp V₁ H (g : G))
    · exact ⟨γ, γ', g, Or.inl ⟨rfl, rfl, rfl⟩, s, hpos, hc⟩
    · have hlt' := not_le.mp hc
      refine ⟨x⁻¹ • F8.γ₁ T L H, δ', k, Or.inr ⟨rfl, rfl, rfl⟩, sk, ?_, ?_⟩
      · rw [hm1]; exact lt_trans hpos hlt'
      · rw [hm2, hm1]; exact hlt'.le
  have hS : (mIdx (F8.Uγ Vp H (g : G)) (F8.Dγ Vp V₁ H (g : G)) =
        mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (g : G)) ∨
      mIdx (F8.Uγ Vp H (g : G)) ⊥ = mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (g : G))) →
      (∀ S : F8.Geom T L H → F8.Geom T L H → Prop,
        (∀ (x' : ↥((L ⊔ T) ⊔ H)) (α ζ : F8.Geom T L H), S (x' • α) (x' • ζ) ↔ S α ζ) →
        (∀ (ζ ζ' : F8.Geom T L H) (a : ↥((L ⊔ T) ⊔ H)),
          F8Setup T V L H ζ ζ' a →
          0 < mIdx (F8.Uγ Vp H (a : G)) (F8.Dγ Vp V₁ H (a : G)) →
          mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (a : G)) ≤
            mIdx (F8.Uγ Vp H (a : G)) (F8.Dγ Vp V₁ H (a : G)) →
          S (F8.γ₁ T L H) ζ) → S γ (F8.γ₁ T L H)) ∧
      (∀ S : F8.Geom T L H → F8.Geom T L H → F8.Geom T L H → Prop,
        (∀ (x' : ↥((L ⊔ T) ⊔ H)) (α ζ η : F8.Geom T L H),
          S (x' • α) (x' • ζ) (x' • η) ↔ S α ζ η) →
        (∀ (ζ ζ' : F8.Geom T L H) (a : ↥((L ⊔ T) ⊔ H)),
          F8Setup T V L H ζ ζ' a →
          0 < mIdx (F8.Uγ Vp H (a : G)) (F8.Dγ Vp V₁ H (a : G)) →
          mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (a : G)) ≤
            mIdx (F8.Uγ Vp H (a : G)) (F8.Dγ Vp V₁ H (a : G)) →
          S (F8.γ₀ T L H) (F8.γ₁ T L H) ζ) →
        S β γ (F8.γ₁ T L H)) := by
    intro hdisj
    obtain ⟨hB0, hBA⟩ := hpd hdisj
    have pos_k : 0 < mIdx (F8.Uγ Vp H (k : G)) (F8.Dγ Vp V₁ H (k : G)) := by
      rw [hm1]; exact hB0
    have dom_k : mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (k : G)) ≤
        mIdx (F8.Uγ Vp H (k : G)) (F8.Dγ Vp V₁ H (k : G)) := by
      rw [hm2, hm1]; exact hBA
    refine ⟨fun S hS' hP => ?_, fun S3 hS3 hP3 => ?_⟩
    · have h1 := hP (x⁻¹ • F8.γ₁ T L H) δ' k sk pos_k dom_k
      exact (hS' x⁻¹ γ (F8.γ₁ T L H)).mp (by rw [hyγ]; exact h1)
    · have h1 := hP3 (x⁻¹ • F8.γ₁ T L H) δ' k sk pos_k dom_k
      exact (hS3 x⁻¹ β γ (F8.γ₁ T L H)).mp (by rw [hxβ, hyγ]; exact h1)
  refine ⟨⟨hn, β, hβ, hnl, hdβ⟩, β, x⁻¹ • F8.γ₁ T L H, δ', k, x⁻¹, hβ, hβne, hnl, hdβ, sk, hxβ,
    hyγ, rfl, eU, eB, eUV, eBV, eV, eA, eDk.symm, eDγ.symm, hm1, hm2, hex, hbotB, hS⟩

end CFSG.ASVolI

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.CosetGeom CFSG.Quasithin.F7
open CFSG.Assembly.LowTwoRank
open scoped Matrix

section F918

variable {G : Type} [Group G]

abbrev GtOf (V₁ : Subgroup G) : Type := SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁

noncomputable def CcOf (V₁ Ug K₀ : Subgroup G) : Subgroup (GtOf V₁) :=
  tildeOf V₁ Ug ⊓ Subgroup.centralizer (tildeOf V₁ K₀ : Set (GtOf V₁))

abbrev GhOf (V₁ Ug K₀ : Subgroup G) : Type :=
  SecQuot (Subgroup.normalizer (CcOf V₁ Ug K₀ : Set (GtOf V₁))) (CcOf V₁ Ug K₀)

noncomputable def hatOf (V₁ Ug K₀ X : Subgroup G) : Subgroup (GhOf V₁ Ug K₀) :=
  secImg (Subgroup.normalizer (CcOf V₁ Ug K₀ : Set (GtOf V₁))) (CcOf V₁ Ug K₀) (tildeOf V₁ X)

def ModIso {X : Type} [Group X] (K A₁ A₂ : Subgroup X) : Prop :=
  K ≤ Subgroup.normalizer (A₁ : Set X) ∧ K ≤ Subgroup.normalizer (A₂ : Set X) ∧
    ∃ φ : ↥A₁ ≃* ↥A₂, ∀ k ∈ K, ∀ a a' : ↥A₁, (a' : X) = k * a * k⁻¹ →
      (φ a' : X) = k * (φ a : X) * k⁻¹

def ModelOn {X : Type} [Group X] (D : FFModel) (Y A : Subgroup X) : Prop :=
  Y ≤ Subgroup.normalizer (A : Set X) ∧
    ∃ hA : IsElemAbelian 2 A, @FFModel.Realizes ↥A (commGroupOfElemAbelian hA) D (autOn Y A) ⊤ ⊥

noncomputable def tensorModel (n : ℕ) (F : Type) [Field F] : FFModel where
  Gam := ↥(StatedSL n F) × ↥(StatedSL n F)
  Amb := Multiplicative (Matrix (Fin n) (Fin n) F)
  act g X := Multiplicative.ofAdd
    (((g.1 : Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) * Multiplicative.toAdd X *
      ((g.2 : Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ)
  sec := ⊤
  ker := ⊥

noncomputable def multiNatModel (n m : ℕ) (F : Type) [Field F] : FFModel where
  Gam := ↥(StatedSL n F)
  Amb := Multiplicative (Matrix (Fin n) (Fin m) F)
  act g X := Multiplicative.ofAdd
    (((g : Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) * Multiplicative.toAdd X)
  sec := ⊤
  ker := ⊥

noncomputable def orthModel (F : Type) [Field F] (σ : F →+* F) : FFModel where
  Gam := ↥(StatedSL 2 F)
  Amb := Multiplicative (Matrix (Fin 2) (Fin 2) F)
  act g X := Multiplicative.ofAdd
    (((g : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * Multiplicative.toAdd X *
      (((g : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).map σ)ᵀ)
  sec := AddSubgroup.toSubgroup (AddMonoidHom.eqLocus (AddMonoidHom.id (Matrix (Fin 2) (Fin 2) F))
    ((AddMonoidHom.mapMatrix σ.toAddMonoidHom).comp
      (Matrix.transposeAddEquiv (Fin 2) (Fin 2) F).toAddMonoidHom))
  ker := ⊥

end F918

end CFSG.ASVolI.ChF

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.CosetGeom CFSG.Quasithin.F7
open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped Matrix commutatorElement

section F918b

variable {G : Type} [Group G]

noncomputable def KstOf (V₁ Ug K : Subgroup G) : Subgroup (MulAut ↥(tildeOf V₁ Ug)) :=
  autOn (tildeOf V₁ K) (tildeOf V₁ Ug)

def IsBenderGroup (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, LieModel X .PSL 2 2 n) ∨ (∃ n : ℕ, LieModel X .PSU 3 2 n) ∨
    ∃ n : ℕ, LieModel X .twistedB2 0 2 n

def IsF918FourList (Ks : Type) [Group Ks] : Prop :=
  IsBenderGroup (Ks ⧸ Subgroup.center Ks) ∨ (∃ n : ℕ, LieModel (Ks ⧸ Subgroup.center Ks) .PSL 3 2 n) ∨
    (Nonempty ((Ks ⧸ Subgroup.center Ks) ≃* alternatingGroup (Fin 6))) ∨
    (∃ n : ℕ, 2 ≤ n ∧ LieModel (Ks ⧸ Subgroup.center Ks) .PSp 2 2 n) ∨
    LieModel (Ks ⧸ Subgroup.center Ks) .PSU 3 3 1 ∨
    (∃ n : ℕ, 2 ≤ n ∧ LieModel (Ks ⧸ Subgroup.center Ks) .G2 0 2 n) ∨
    LieModel (Ks ⧸ Subgroup.center Ks) .PSL 4 2 1 ∨ LieModel (Ks ⧸ Subgroup.center Ks) .PSL 5 2 1 ∨
    (Nonempty ((Ks ⧸ Subgroup.center Ks) ≃* alternatingGroup (Fin 7)) ∧ Nat.card (Subgroup.center Ks) ≠ 3) ∨
    Nonempty (Ks ≃* ↥CFSG.Blueprint.NativeSporadic.M22) ∨
    (Group.IsPerfect Ks ∧ Nat.card (Subgroup.center Ks) = 3 ∧
      Nonempty ((Ks ⧸ Subgroup.center Ks) ≃* ↥CFSG.Blueprint.NativeSporadic.M22))

def IsF918FiveList (Ks : Type) [Group Ks] : Prop :=
  (∃ n : ℕ, LieModel Ks .PSL 2 2 n) ∨ (∃ n : ℕ, LieModel Ks .twistedB2 0 2 n) ∨
    Nonempty (Ks ≃* alternatingGroup (Fin 5)) ∨ LieModel Ks .PSL 3 2 1

def NatSL (d n : ℕ) (Ks : Type) [Group Ks] {X : Type} [Group X] (Y A : Subgroup X) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧ Nonempty (Ks ≃* ↥(StatedSL d F)) ∧
    ModelOn (FFModel.nat (StatedSL d F)) Y A

def NatSp4 (n : ℕ) (Ks : Type) [Group Ks] {X : Type} [Group X] (Y A : Subgroup X) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧ Nonempty (Ks ≃* ↥(StatedSp 2 F)) ∧
    ModelOn (FFModel.nat (StatedSp 2 F)) Y A

def NatSz (Ks : Type) [Group Ks] {X : Type} [Group X] (Y A : Subgroup X) : Prop :=
  ∃ (a : ℕ) (F : Type) (_ : Field F) (_ : Finite F), 1 ≤ a ∧ Nat.card F = 2 ^ (2 * a + 1) ∧
    Nonempty (Ks ≃* ↥(CFSG.Blueprint.suzukiGroup a F)) ∧ ModelOn (FFModel.nat (CFSG.Blueprint.suzukiGroup a F)) Y A

def NatA6 (Ks : Type) [Group Ks] {X : Type} [Group X] (Y A : Subgroup X) : Prop :=
  Nonempty (Ks ≃* alternatingGroup (Fin 6)) ∧ ModelOn (FFModel.altDn 6) Y A

end F918b

end CFSG.ASVolI.ChF

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.CosetGeom CFSG.Quasithin.F7
open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped Matrix commutatorElement

section F918c

variable {G : Type} [Group G]

noncomputable def hat' (V₁ Vp H K T X : Subgroup G) : Subgroup (GhOf V₁ (conjClosure Vp H) (conjClosure K T)) :=
  hatOf V₁ (conjClosure Vp H) (conjClosure K T) X

def IsIrrPlusT (V₁ Vp H K T I : Subgroup G) : Prop :=
  V₁ ≤ I ∧ I ≤ conjClosure Vp H ∧ IsIrrPlusTilde V₁ (conjClosure K T) I ∧
    ∀ S : Subgroup (GhOf V₁ (conjClosure Vp H) (conjClosure K T)),
      S ≤ hat' V₁ Vp H K T (conjClosure I T) → hat' V₁ Vp H K T (conjClosure K T) ≤ Subgroup.normalizer (S : Set _) →
      ModIso (hat' V₁ Vp H K T (conjClosure K T)) S (hat' V₁ Vp H K T I) → S ≤ hat' V₁ Vp H K T I

def HatDSum (V₁ Vp H K T J I' : Subgroup G) (t : G) : Prop :=
  hat' V₁ Vp H K T J = hat' V₁ Vp H K T I' ⊔ hat' V₁ Vp H K T (conjSub t⁻¹ I') ∧
    hat' V₁ Vp H K T I' ⊓ hat' V₁ Vp H K T (conjSub t⁻¹ I') = ⊥

def F918NatChoice4 (V₁ Vp H K T I : Subgroup G) : Prop :=
  (∃ n : ℕ, NatSL 3 n ↥(KstOf V₁ (conjClosure Vp H) K)
    (hat' V₁ Vp H K T K) (hat' V₁ Vp H K T I)) ∨
    (∃ n : ℕ, NatSp4 n ↥(KstOf V₁ (conjClosure Vp H) K)
      (hat' V₁ Vp H K T K) (hat' V₁ Vp H K T I)) ∨
    NatA6 ↥(KstOf V₁ (conjClosure Vp H) K)
      (hat' V₁ Vp H K T K) (hat' V₁ Vp H K T I) ∨
    NatSL 4 1 ↥(KstOf V₁ (conjClosure Vp H) K)
      (hat' V₁ Vp H K T K) (hat' V₁ Vp H K T I) ∨
    NatSL 5 1 ↥(KstOf V₁ (conjClosure Vp H) K)
      (hat' V₁ Vp H K T K) (hat' V₁ Vp H K T I) ∨
    (Nonempty (↥(KstOf V₁ (conjClosure Vp H) K) ≃* alternatingGroup (Fin 7)) ∧
      Nat.card ↥(tildeOf V₁ I) = 2 ^ 4)

def F918NatChoice5 (V₁ Vp H K T I : Subgroup G) : Prop :=
  (∃ n : ℕ, NatSL 2 n ↥(KstOf V₁ (conjClosure Vp H) K) (hat' V₁ Vp H K T K) (hat' V₁ Vp H K T I)) ∨
    NatSz ↥(KstOf V₁ (conjClosure Vp H) K) (hat' V₁ Vp H K T K) (hat' V₁ Vp H K T I) ∨
    (Nonempty (↥(KstOf V₁ (conjClosure Vp H) K) ≃* alternatingGroup (Fin 5)) ∧
      ModelOn (FFModel.altDn 5) (hat' V₁ Vp H K T K) (hat' V₁ Vp H K T I)) ∨
    NatSL 3 1 ↥(KstOf V₁ (conjClosure Vp H) K) (hat' V₁ Vp H K T K) (hat' V₁ Vp H K T I)

end F918c

end CFSG.ASVolI.ChF

namespace CFSG.ASVolI.ChF

open CFSG.Quasithin CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint

abbrev HypF_9_18Conditional {G : Type} [Group G] (T V L V₁ Vp H K : Subgroup G) : Prop :=
  HypF918 T V L V₁ Vp H K

structure HypF_9_18 {G : Type} [Group G] (T V L V₁ Vp H K : Subgroup G) : Prop
    extends HypF98 T V L V₁ Vp H where
  K_cComp : K ∈ cComp H
  K_quasisimple : CFSG.IsQuasisimple (↥K ⧸ (pCoreOf 2 K).subgroupOf K)
  H_product : ∀ element : G, element ∈ H ↔
    ∃ component factor : G, component ∈ conjClosure K T ∧ factor ∈ ((L ⊔ T) ⊓ H) ∧
      element = component * factor

def HasExactSectionActionKernel {G : Type} [Group G] (X U N C : Subgroup G) : Prop :=
  X ≤ Subgroup.normalizer (U : Set G) ∧ X ≤ Subgroup.normalizer (N : Set G) ∧ N ≤ U ∧
    ∀ element ∈ X, (∀ vector ∈ U, element * vector * element⁻¹ * vector⁻¹ ∈ N) ↔ element ∈ C

noncomputable def F918MultiplicityOperator (F : Type) [Field F]
    (matrix : Matrix.GeneralLinearGroup (Fin 2) F)
    (vector : Multiplicative (Matrix (Fin 2) (Fin 2) F)) :
    Multiplicative (Matrix (Fin 2) (Fin 2) F) :=
  Multiplicative.ofAdd (Multiplicative.toAdd vector *
    (Matrix.transpose (matrix : Matrix (Fin 2) (Fin 2) F)))

def F918MultiplicityLineFixed (F : Type) [Field F]
    (image : Subgroup (Matrix.GeneralLinearGroup (Fin 2) F))
    (line : Submodule F (Fin 2 → F)) : Prop :=
  Module.finrank F line = 1 ∧
    ∀ matrix ∈ image, ∀ vector ∈ line,
      (matrix : Matrix (Fin 2) (Fin 2) F).mulVec vector ∈ line

noncomputable def F918MultiplicityLineModule (F : Type) [Field F]
    (line : Submodule F (Fin 2 → F)) : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F)) :=
  { carrier := {matrix | ∀ row, (fun column => Multiplicative.toAdd matrix row column) ∈ line}
    one_mem' := by
      intro row
      change (0 : Fin 2 → F) ∈ line
      exact line.zero_mem
    mul_mem' := by
      intro first second first_mem second_mem row
      exact line.add_mem (first_mem row) (second_mem row)
    inv_mem' := by
      intro matrix matrix_mem row
      exact line.neg_mem (matrix_mem row) }

structure F918MultiplicityData {G : Type} [Group G]
    (V₁ Vp H K T I : Subgroup G) (F : Type) [Field F] where
  coordinates : ↥(V₁ ⊔ ⁅conjClosure I H, K⁆) →*
    Multiplicative (Matrix (Fin 2) (Fin 2) F)
  coordinates_surjective : Function.Surjective coordinates
  coordinates_kernel : ∀ vector, coordinates vector = 1 ↔
    (vector : G) ∈ centralizerMod V₁ (V₁ ⊔ ⁅conjClosure I H, K⁆) (conjClosure K T)
  markedComponent : ↥K →* ↥(StatedSL 2 F)
  markedComponent_surjective : Function.Surjective markedComponent
  markedComponent_kernel : ∀ element, markedComponent element = 1 ↔
    (element : G) ∈ pCoreOf 2 H
  component_equivariance : ∀ element : ↥K, ∀ vector transported : ↥(V₁ ⊔ ⁅conjClosure I H, K⁆),
    (transported : G) = element * vector * element⁻¹ →
    coordinates transported = Multiplicative.ofAdd
      (((markedComponent element : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        Multiplicative.toAdd (coordinates vector))
  centralizer_normalizes : centralizerMod (pCoreOf 2 H) H (conjClosure K T) ≤
    Subgroup.normalizer ((V₁ ⊔ ⁅conjClosure I H, K⁆ : Subgroup G) : Set G)
  normalizer_normalizes : H ⊓ Subgroup.normalizer (K : Set G) ≤
    Subgroup.normalizer ((V₁ ⊔ ⁅conjClosure I H, K⁆ : Subgroup G) : Set G)
  multiplicity : ↥(centralizerMod (pCoreOf 2 H) H (conjClosure K T)) →*
    Matrix.GeneralLinearGroup (Fin 2) F
  multiplicity_equivariance :
    ∀ element : ↥(centralizerMod (pCoreOf 2 H) H (conjClosure K T)),
      ∀ vector transported : ↥(V₁ ⊔ ⁅conjClosure I H, K⁆),
        (transported : G) = element * vector * element⁻¹ →
        coordinates transported = F918MultiplicityOperator F (multiplicity element) (coordinates vector)
  multiplicity_kernel :
    ∀ element : ↥(centralizerMod (pCoreOf 2 H) H (conjClosure K T)),
      multiplicity element = 1 ↔
        ∀ vector transported : ↥(V₁ ⊔ ⁅conjClosure I H, K⁆),
          (transported : G) = element * vector * element⁻¹ →
            coordinates transported = coordinates vector
  normalizerAction : ↥(H ⊓ Subgroup.normalizer (K : Set G)) →*
    MulAut (Multiplicative (Matrix (Fin 2) (Fin 2) F))
  normalizer_equivariance : ∀ element : ↥(H ⊓ Subgroup.normalizer (K : Set G)),
    ∀ vector transported : ↥(V₁ ⊔ ⁅conjClosure I H, K⁆),
      (transported : G) = element * vector * element⁻¹ →
        coordinates transported = normalizerAction element (coordinates vector)
  fieldAction : ↥(H ⊓ Subgroup.normalizer (K : Set G)) →* (F ≃+* F)
  semilinear : ∀ element scalar matrix,
    normalizerAction element (Multiplicative.ofAdd (scalar • matrix)) =
      Multiplicative.ofAdd (fieldAction element scalar •
        Multiplicative.toAdd (normalizerAction element (Multiplicative.ofAdd matrix)))
  commutant_transport : ∀ element : ↥(H ⊓ Subgroup.normalizer (K : Set G)),
    ∀ matrix : Matrix.GeneralLinearGroup (Fin 2) F,
      ∃ transported : Matrix.GeneralLinearGroup (Fin 2) F,
        ∀ vector, normalizerAction element (F918MultiplicityOperator F matrix vector) =
          F918MultiplicityOperator F transported (normalizerAction element vector)
  actual_image_transport : ∀ element : ↥(H ⊓ Subgroup.normalizer (K : Set G)),
    ∀ matrix ∈ multiplicity.range,
      ∃ transported ∈ multiplicity.range,
        ∀ vector, normalizerAction element (F918MultiplicityOperator F matrix vector) =
          F918MultiplicityOperator F transported (normalizerAction element vector)
  full_commutant : ∀ operator : MulAut (Multiplicative (Matrix (Fin 2) (Fin 2) F)),
    (∀ (scalar : F) (matrix : Matrix (Fin 2) (Fin 2) F),
      operator (Multiplicative.ofAdd (scalar • matrix)) =
      Multiplicative.ofAdd (scalar • Multiplicative.toAdd (operator (Multiplicative.ofAdd matrix)))) →
    (∀ element : ↥(StatedSL 2 F), ∀ matrix,
      operator (Multiplicative.ofAdd
        (((element : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * matrix)) =
      Multiplicative.ofAdd
        (((element : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          Multiplicative.toAdd (operator (Multiplicative.ofAdd matrix)))) →
    ∃ uniqueMatrix : Matrix.GeneralLinearGroup (Fin 2) F,
      (∀ vector, operator vector = F918MultiplicityOperator F uniqueMatrix vector) ∧
      ∀ otherMatrix, (∀ vector, operator vector = F918MultiplicityOperator F otherMatrix vector) →
        otherMatrix = uniqueMatrix

def F918MultiplicityCases {G : Type} [Group G]
    {V₁ Vp H K T I : Subgroup G} {F : Type} [Field F]
    (data : F918MultiplicityData V₁ Vp H K T I F) : Prop :=
  (∃ line : Submodule F (Fin 2 → F), F918MultiplicityLineFixed F data.multiplicity.range line ∧
    ∃ J : Subgroup G, V₁ ≤ J ∧ J ≤ V₁ ⊔ ⁅conjClosure I H, K⁆ ∧ IsIrrPlusTilde V₁ K J ∧
      J = V₁ ⊔ ⁅((F918MultiplicityLineModule F line).comap data.coordinates).map
        (V₁ ⊔ ⁅conjClosure I H, K⁆).subtype, K⁆ ∧
      centralizerMod (pCoreOf 2 H) H (conjClosure K T) ≤ Subgroup.normalizer (J : Set G) ∧
      ∀ element : ↥(H ⊓ Subgroup.normalizer (K : Set G)),
        (∀ vector ∈ F918MultiplicityLineModule F line,
          data.normalizerAction element vector ∈ F918MultiplicityLineModule F line) →
        (element : G) ∈ Subgroup.normalizer (J : Set G)) ∨
  (∀ line : Submodule F (Fin 2 → F), Module.finrank F line = 1 →
    ¬ F918MultiplicityLineFixed F data.multiplicity.range line)

def F918ResidualMultiplicity {G : Type} [Group G]
    (V₁ Vp H K T I : Subgroup G) : Prop :=
  ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F), 2 ≤ n ∧ Nat.card F = 2 ^ n ∧
    ∃ data : F918MultiplicityData V₁ Vp H K T I F, F918MultiplicityCases data

@[expose] def HasNoFaithfulFFModulesMod {G : Type} [Group G] (X C : Subgroup G) : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) → ∀ ρ : ↥X →* MulAut W,
    (∀ x : ↥X, ρ x = 1 ↔ (x : G) ∈ C) → ¬ IsFFModule ρ.range

theorem noFaithfulFF_tilde_transport {G : Type} [Group G] [Finite G]
    (X U N C : Subgroup G) (hU : IsElemAbelian 2 (tildeOf N U))
    (hnumerator : U ≤ Subgroup.normalizer (N : Set G))
    (hkernel : HasExactSectionActionKernel X U N C)
    (hno : HasNoFaithfulFFModulesMod X C) :
    ¬ IsFFInt (tildeOf N X) (tildeOf N U) hU := by
  intro hFF
  obtain ⟨hXU, hXN, -, hker⟩ := hkernel
  obtain ⟨ρ, hrange, hkerρ⟩ :=
    CFSG.Quasithin.RonanF9T.exists_hom_range_autOn X U N hXU hXN hnumerator
  letI : CommGroup ↥(tildeOf N U) := commGroupOfElemAbelian hU
  refine hno ↥(tildeOf N U) (fun w => Subtype.ext (by simpa using hU.2 w w.2)) ρ
    (fun x => (hkerρ x).trans (hker x x.2)) ?_
  rw [hrange]
  exact hFF

theorem noFaithfulFF_quotient_transport {G : Type} [Group G] [Finite G]
    (X U N C : Subgroup G)
    (hU : IsElemAbelian 2 (secImg (Subgroup.normalizer (N : Set G)) N U))
    (hnumerator : U ≤ Subgroup.normalizer (N : Set G))
    (hkernel : HasExactSectionActionKernel X U N C)
    (hno : HasNoFaithfulFFModulesMod X C) :
    ¬ IsFFInt (secImg (Subgroup.normalizer (N : Set G)) N X)
      (secImg (Subgroup.normalizer (N : Set G)) N U) hU :=
  noFaithfulFF_tilde_transport X U N C hU hnumerator hkernel hno

theorem hypF918Conditional_of_literal {G : Type} [Group G]
    {T V L V₁ Vp H K : Subgroup G} (hyp : HypF_9_18 T V L V₁ Vp H K)
    (hnormal : H ≤ Subgroup.normalizer (conjClosure K T : Set G)) :
    HypF_9_18Conditional T V L V₁ Vp H K := by
  have hK₀ : conjClosure K T ≤ H :=
    conjClosure_le fun _ ht _ hz =>
      H.mul_mem (H.mul_mem (hyp.T_le_H ht) (le_of_mem_cComp hyp.K_cComp hz))
        (H.inv_mem (hyp.T_le_H ht))
  refine ⟨hyp.toHypF98, hyp.K_cComp, hyp.K_quasisimple, le_antisymm ?_ (sup_le hK₀ inf_le_right),
    hnormal⟩
  intro element helement
  obtain ⟨component, factor, hc, hf, rfl⟩ := (hyp.H_product element).mp helement
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hf)

end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.CosetGeom CFSG.Quasithin.F7
open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.ASVolI.ChF
open scoped Matrix commutatorElement

@[expose] def F_9_18 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ Vp H K : Subgroup G) (hyp : HypF_9_18 T V L V₁ Vp H K),
    CFSG.SectionRank.IsSQTKCat ↥H →
    (∃ I : Subgroup G, IsIrrPlusT V₁ Vp H K T I) ∧
    (∃ B : Subgroup G, B ≤ pCoreOf 2 (L₁Of L V₁ ⊔ T) ∧
      (∀ b ∈ B, (∀ k ∈ conjClosure K T, b * k * b⁻¹ * k⁻¹ ∈ pCoreOf 2 H) → b ∈ pCoreOf 2 H) ∧
      autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure Vp H)) ∈
        @Qset ↥(tildeOf V₁ (conjClosure Vp H))
          (commGroupOfElemAbelian hyp.toHypF98.toHypF91.isElemAbelian_tilde)
          (autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H)))) ∧
    (∀ W : Subgroup G, V₁ ≤ W → W ≤ conjClosure Vp H →
      conjClosure K T ⊔ T ≤ Subgroup.normalizer (W : Set G) → tildeOf V₁ W ≠ ⊥ →
      tildeOf V₁ ⁅W, conjClosure K T⁆ = tildeOf V₁ W →
        tildeOf V₁ W = tildeOf V₁ ⁅conjClosure Vp H, conjClosure K T⁆ ∨
        ((∃ hW : IsElemAbelian 2 (tildeOf V₁ W),
            IsFFInt (tildeOf V₁ (conjClosure K T ⊔ T)) (tildeOf V₁ W) hW) ∧
          ∃ hQ : IsElemAbelian 2 (secImg (Subgroup.normalizer (W : Set G)) W (conjClosure Vp H)),
            IsFFInt (secImg (Subgroup.normalizer (W : Set G)) W (conjClosure K T ⊔ T))
              (secImg (Subgroup.normalizer (W : Set G)) W (conjClosure Vp H)) hQ) ∨
        ((∃ hW : IsElemAbelian 2 (tildeOf V₁ W),
            F9.IsStrongFFInt (tildeOf V₁ (conjClosure K T ⊔ T)) (tildeOf V₁ W) hW) ∨
          ∃ hQ : IsElemAbelian 2 (secImg (Subgroup.normalizer (W : Set G)) W (conjClosure Vp H)),
            F9.IsStrongFFInt (secImg (Subgroup.normalizer (W : Set G)) W (conjClosure K T ⊔ T))
              (secImg (Subgroup.normalizer (W : Set G)) W (conjClosure Vp H)) hQ)) ∧
    ∀ I : Subgroup G, IsIrrPlusT V₁ Vp H K T I →
      (CFSG.SectionRank.IsSQTKCat ↥H ∧ IsSylowTwoOf T H ∧ oTwoRes (conjClosure K T) = conjClosure K T ∧
        H ≤ Subgroup.normalizer (conjClosure K T : Set G) ∧ K ∈ cComp H ∧
        CFSG.IsQuasisimple (↥K ⧸ (pCoreOf 2 K).subgroupOf K) ∧
        V₁ ≤ conjClosure Vp H ∧ conjClosure Vp H ≤ pCoreOf 2 H ∧
        H ≤ Subgroup.normalizer (V₁ : Set G) ∧ H ≤ Subgroup.normalizer (conjClosure Vp H : Set G) ∧
        IsElemAbelian 2 (tildeOf V₁ (conjClosure Vp H)) ∧
        (∀ E : Subgroup G, E ≤ conjClosure K T → conjClosure K T ≤ Subgroup.normalizer (E : Set G) →
          (∀ e ∈ E, ∃ k : ℕ, e ^ 2 ^ k ∈ pCoreOf 2 H) → E ≤ pCoreOf 2 H) ∧
        pCoreOf 2 (conjClosure K T ⊔ T) ≤ Subgroup.normalizer (I : Set G) ∧
        IsIrrPlusTilde V₁ (conjClosure K T) I) ∧
      (∀ B : Subgroup G, B ≤ pCoreOf 2 (L₁Of L V₁ ⊔ T) →
        (∀ b ∈ B, (∀ k ∈ conjClosure K T, b * k * b⁻¹ * k⁻¹ ∈ pCoreOf 2 H) → b ∈ pCoreOf 2 H) →
        autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure Vp H)) ∈
          @Qset ↥(tildeOf V₁ (conjClosure Vp H))
            (commGroupOfElemAbelian hyp.toHypF98.toHypF91.isElemAbelian_tilde)
            (autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H))) →
        ∀ X : Subgroup G, (X = T ∨ X = H) →
          (∀ k ∈ conjClosure K T, (∀ i ∈ conjClosure I X, k * i * k⁻¹ * i⁻¹ ∈ V₁) →
            ∀ k' ∈ conjClosure K T, k * k' * k⁻¹ * k'⁻¹ ∈ pCoreOf 2 H) ∧
          (∀ b ∈ B, (∀ i ∈ conjClosure I X, b * i * b⁻¹ * i⁻¹ ∈ V₁) → b ∈ pCoreOf 2 H) ∧
          ∃ hX : IsElemAbelian 2 (tildeOf V₁ (conjClosure I X)),
            autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure I X)) ∈
              @Qset ↥(tildeOf V₁ (conjClosure I X)) (commGroupOfElemAbelian hX)
                (autOn (tildeOf V₁ (conjClosure K T ⊔ T)) (tildeOf V₁ (conjClosure I X))) ∧
            qInt (tildeOf V₁ (K ⊔ T)) (tildeOf V₁ (conjClosure I X)) hX ≤ 2) ∧
      (K = conjClosure K T →
        IsF918FourList ↥(KstOf V₁ (conjClosure Vp H) K) ∧
        (H ≤ Subgroup.normalizer (I : Set G) ∨
          (tildeOf V₁ (conjClosure I T) = tildeOf V₁ I ∧
            ∃ hV : IsElemAbelian 2 (hat' V₁ Vp H K T I),
              IsFFInt (hat' V₁ Vp H K T (K ⊔ T)) (hat' V₁ Vp H K T I) hV) ∨
          (F918NatChoice4 V₁ Vp H K T I ∧
            (∃ t : G, t ∈ T ∧ t ∉ Subgroup.normalizer (I : Set G)) ∧
            ∀ t : G, t ∈ T → t ∉ Subgroup.normalizer (I : Set G) →
              HatDSum V₁ Vp H K T (conjClosure I H) I t ∧
              ¬ ModIso (hat' V₁ Vp H K T K) (hat' V₁ Vp H K T I)
                  (hat' V₁ Vp H K T (conjSub t⁻¹ I))))) ∧
      (conjClosure K T ≠ K ∧ K ≤ conjClosure K T →
        IsF918FiveList ↥(KstOf V₁ (conjClosure Vp H) K) ∧
        ((H ≤ Subgroup.normalizer (I : Set G) ∧
            ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
              Nonempty (↥(KstOf V₁ (conjClosure Vp H) K) ≃* ↥(StatedSL 2 F)) ∧
              ModelOn (tensorModel 2 F) (tildeOf V₁ (conjClosure K T)) (tildeOf V₁ I)) ∨
          (H ≤ Subgroup.normalizer (I : Set G) ∧
            ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
              Nonempty (↥(KstOf V₁ (conjClosure Vp H) K) ≃* ↥(StatedSL 3 F)) ∧
              ModelOn (tensorModel 3 F) (tildeOf V₁ (conjClosure K T)) (tildeOf V₁ I)) ∨
          ((∃ t : G, t ∈ T ∧ t ∉ Subgroup.normalizer (K : Set G)) ∧
            ∀ t : G, t ∈ T → t ∉ Subgroup.normalizer (K : Set G) →
              ∃ K' : Subgroup G, (K' = K ∨ K' = conjSub t⁻¹ K) ∧
              HatDSum V₁ Vp H K' T (conjClosure I H) ⁅conjClosure I H, K'⁆ t ∧
              tildeOf V₁ ⁅conjClosure I H, K'⁆ ≤
                tildeOf V₁ (conjClosure I H) ⊓
                  Subgroup.centralizer (tildeOf V₁ (conjSub t⁻¹ K') : Set (GtOf V₁)) ∧
              ((
              ((hat' V₁ Vp H K' T ⁅conjClosure I H, K'⁆ =
                  hat' V₁ Vp H K' T (conjClosure I H) ⊓
                    Subgroup.centralizer (hat' V₁ Vp H K' T (conjSub t⁻¹ K') : Set _)) ∧
              (hat' V₁ Vp H K' T ⁅conjClosure I H, K'⁆ = hat' V₁ Vp H K' T I ∧
                  (F918NatChoice5 V₁ Vp H K' T I ∨
                    ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F) (σ : F →+* F),
                      Even n ∧ Nat.card F = 2 ^ n ∧ σ ≠ RingHom.id F ∧ (∀ x, σ (σ x) = x) ∧
                      Nonempty (↥(KstOf V₁ (conjClosure Vp H) K') ≃* ↥(StatedSL 2 F)) ∧
                      ModelOn (orthModel F σ) (hat' V₁ Vp H K' T K') (hat' V₁ Vp H K' T I)))) ∨
                ((tildeOf V₁ ⁅conjClosure I H, K'⁆ =
                  tildeOf V₁ (conjClosure I H) ⊓
                    Subgroup.centralizer (tildeOf V₁ (conjSub t⁻¹ K') : Set (GtOf V₁))) ∧
                (LieModel ↥(KstOf V₁ (conjClosure Vp H) K') .PSL 3 2 1 ∧
                  (∃ s : G, s ∈ T ∧ s ∈ Subgroup.normalizer (K' : Set G) ∧
                    s ∉ Subgroup.normalizer (I : Set G)) ∧
                  ∀ s : G, s ∈ T → s ∈ Subgroup.normalizer (K' : Set G) →
                    s ∉ Subgroup.normalizer (I : Set G) →
                    (tildeOf V₁ ⁅conjClosure I H, K'⁆ =
                      tildeOf V₁ I ⊔ tildeOf V₁ (conjSub s⁻¹ I) ∧
                      tildeOf V₁ I ⊓ tildeOf V₁ (conjSub s⁻¹ I) = ⊥) ∧
                    Nat.card ↥(tildeOf V₁ I) = 2 ^ 3)) ∨
                ((tildeOf V₁ ⁅conjClosure I H, K'⁆ =
                  tildeOf V₁ (conjClosure I H) ⊓
                    Subgroup.centralizer (tildeOf V₁ (conjSub t⁻¹ K') : Set (GtOf V₁))) ∧
                (LieModel ↥(KstOf V₁ (conjClosure Vp H) K') .PSL 3 2 1 ∧
                  (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
                    ModelOn (multiNatModel 3 4 F) (tildeOf V₁ K') (tildeOf V₁ ⁅conjClosure I H, K'⁆)) ∧
                  (Nonempty (↥(oTwoRes
                      (autOn (tildeOf V₁ (centralizerMod (pCoreOf 2 H) H (conjClosure K' T)))
                        (tildeOf V₁ (conjClosure I H)))) ≃* Multiplicative (ZMod 5)) ∨
                    Nonempty (↥(oTwoRes
                      (autOn (tildeOf V₁ (centralizerMod (pCoreOf 2 H) H (conjClosure K' T)))
                        (tildeOf V₁ (conjClosure I H)))) ≃*
                          (Multiplicative (ZMod 5) × Multiplicative (ZMod 5))))))) ∨
                F918ResidualMultiplicity V₁ Vp H K' T I)))) ∧
      ((∀ N : Subgroup G, N ≤ conjClosure K T ⊔ T →
          conjClosure K T ⊔ T ≤ Subgroup.normalizer (N : Set G) →
          (conjClosure K T ⊔ T) ⊓ pCoreOf 2 H ≤ N → ⁅N, conjClosure K T⁆ ≤ pCoreOf 2 H →
          ChF.HasNoFaithfulFFModulesMod (conjClosure K T ⊔ T) N) →
        tildeOf V₁ (conjClosure I H) = tildeOf V₁ ⁅conjClosure Vp H, conjClosure K T⁆)

private theorem f918_clause_six {G : Type} [Group G] [Finite G]
    {T V L V₁ Vp H K : Subgroup G} (h : HypF918 T V L V₁ Vp H K) {W : Subgroup G}
    (hV₁W : V₁ ≤ W) (hWU : W ≤ conjClosure Vp H)
    (hWN : conjClosure K T ⊔ T ≤ Subgroup.normalizer (W : Set G)) (hW0 : tildeOf V₁ W ≠ ⊥)
    (hWK : tildeOf V₁ ⁅W, conjClosure K T⁆ = tildeOf V₁ W) :
    tildeOf V₁ W = tildeOf V₁ ⁅conjClosure Vp H, conjClosure K T⁆ ∨
      ((∃ hW : IsElemAbelian 2 (tildeOf V₁ W),
          IsFFInt (tildeOf V₁ (conjClosure K T ⊔ T)) (tildeOf V₁ W) hW) ∧
        ∃ hQ : IsElemAbelian 2 (secImg (Subgroup.normalizer (W : Set G)) W (conjClosure Vp H)),
          IsFFInt (secImg (Subgroup.normalizer (W : Set G)) W (conjClosure K T ⊔ T))
            (secImg (Subgroup.normalizer (W : Set G)) W (conjClosure Vp H)) hQ) ∨
      ((∃ hW : IsElemAbelian 2 (tildeOf V₁ W),
          F9.IsStrongFFInt (tildeOf V₁ (conjClosure K T ⊔ T)) (tildeOf V₁ W) hW) ∨
        ∃ hQ : IsElemAbelian 2 (secImg (Subgroup.normalizer (W : Set G)) W (conjClosure Vp H)),
          F9.IsStrongFFInt (secImg (Subgroup.normalizer (W : Set G)) W (conjClosure K T ⊔ T))
            (secImg (Subgroup.normalizer (W : Set G)) W (conjClosure Vp H)) hQ) := by
  rcases h.F918_6 hV₁W hWU hWN hW0 hWK with ha | ⟨hb1, hb2⟩ | hc
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨⟨_, hb1⟩, _, hb2⟩)
  · rcases hc with hc | hc
    · exact Or.inr (Or.inr (Or.inl ⟨_, hc⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨_, hc⟩))

private theorem f918_clause_seven {G : Type} [Group G] [Finite G]
    {T V L V₁ Vp H K I : Subgroup G} (h : HypF918 T V L V₁ Vp H K)
    (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H) (hI : IsIrrPlusTilde V₁ (conjClosure K T) I)
    (h7 : ∀ N : Subgroup G, N ≤ conjClosure K T ⊔ T →
      conjClosure K T ⊔ T ≤ Subgroup.normalizer (N : Set G) →
      (conjClosure K T ⊔ T) ⊓ pCoreOf 2 H ≤ N → ⁅N, conjClosure K T⁆ ≤ pCoreOf 2 H →
      ChF.HasNoFaithfulFFModulesMod (conjClosure K T ⊔ T) N) :
    tildeOf V₁ (conjClosure I H) = tildeOf V₁ ⁅conjClosure Vp H, conjClosure K T⁆ := by
  have h1 := h.toHypF98.toHypF91
  have hUH : conjClosure Vp H ≤ H :=
    h1.conjClosure_Vp_le_pCoreOf.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hUN : conjClosure Vp H ≤ Subgroup.normalizer (V₁ : Set G) :=
    hUH.trans h1.H_normalizes_V₁
  have hIHU : conjClosure I H ≤ conjClosure Vp H := conjClosure_le_conjClosure_U hIU le_rfl
  have hIHN : conjClosure K T ⊔ T ≤ Subgroup.normalizer (conjClosure I H : Set G) :=
    h.K₀T_le_H.trans (le_normalizer_conjClosure I H)
  have hUW : conjClosure Vp H ≤ Subgroup.normalizer (conjClosure I H : Set G) :=
    HypF91.le_normalizer_of_isElemAbelian_le h.toHypF98.F911_3 hIHU
  have hQV₁ : ∀ x ∈ pCoreOf 2 H, ∀ e ∈ conjClosure Vp H, x * e * x⁻¹ * e⁻¹ ∈ V₁ := by
    intro x hx e he
    have := V₁.inv_mem (h1.commutator_conjClosure_le e he x hx)
    have e' : (e * x * e⁻¹ * x⁻¹)⁻¹ = x * e * x⁻¹ * e⁻¹ := by group
    rwa [e'] at this
  have hWK := h.tilde_commutator_conjClosure hIU hI
  have hW0 : tildeOf V₁ (conjClosure I H) ≠ ⊥ := by
    intro hbot
    have hIV₁ : I ≤ V₁ := by
      intro i hi
      have hiN : i ∈ Subgroup.normalizer (V₁ : Set G) := hUN (hIU hi)
      have : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨i, hiN⟩ ∈
          tildeOf V₁ (conjClosure I H) :=
        secMk_mem_secImg (x := ⟨i, hiN⟩) (le_conjClosure I H hi)
      rw [hbot] at this
      have h2 : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨i, hiN⟩ = 1 := this
      exact secMk_eq_one_iff.mp h2
    have hIC : I ≤ centralizerMod V₁ I (conjClosure K T) := by
      intro i hi
      refine ⟨hi, hUN (hIU hi), fun k hk => ?_⟩
      have h3 : k * i⁻¹ * k⁻¹ ∈ V₁ :=
        (Subgroup.mem_normalizer_iff.mp (h1.H_normalizes_V₁ (h.K₀_le_H hk)) i⁻¹).mp
          (V₁.inv_mem (hIV₁ hi))
      have e : i * k * i⁻¹ * k⁻¹ = i * (k * i⁻¹ * k⁻¹) := by group
      rw [e]
      exact V₁.mul_mem (hIV₁ hi) h3
    exact (not_le_of_gt hI.2.2.1) hIC
  by_cases ha : tildeOf V₁ (conjClosure I H) = tildeOf V₁ ⁅conjClosure Vp H, conjClosure K T⁆
  · exact ha
  exfalso
  have hnt1 : ¬ ∀ k ∈ conjClosure K T, ∀ w ∈ conjClosure I H, k * w * k⁻¹ * w⁻¹ ∈ V₁ := by
    intro hall
    have hle : ⁅conjClosure I H, conjClosure K T⁆ ≤ V₁ := by
      refine Subgroup.commutator_le.mpr fun w hw k hk => ?_
      have := V₁.inv_mem (hall k hk w hw)
      have e : (k * w * k⁻¹ * w⁻¹)⁻¹ = w * k * w⁻¹ * k⁻¹ := by group
      rwa [e] at this
    apply hW0
    rw [← hWK]
    exact tildeOf_eq_bot_of_le hle
  have hnt2 : ¬ ∀ k ∈ conjClosure K T, ∀ u ∈ conjClosure Vp H,
      k * u * k⁻¹ * u⁻¹ ∈ conjClosure I H := by
    intro hall
    have hle : ⁅conjClosure Vp H, conjClosure K T⁆ ≤ conjClosure I H := by
      refine Subgroup.commutator_le.mpr fun u hu k hk => ?_
      have := (conjClosure I H).inv_mem (hall k hk u hu)
      have e : (k * u * k⁻¹ * u⁻¹)⁻¹ = u * k * u⁻¹ * k⁻¹ := by group
      rwa [e] at this
    apply ha
    refine le_antisymm ?_ (secImg_mono hle)
    rw [← hWK]
    exact secImg_mono (Subgroup.commutator_mono hIHU le_rfl)
  have hIHel : IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)) := h.isElemAbelian_tilde_of_le hIHU
  have hIHq : IsElemAbelian 2 (secImg (Subgroup.normalizer (conjClosure I H : Set G))
      (conjClosure I H) (conjClosure Vp H)) := h.isElemAbelian_quotient (conjClosure I H)
  have hN₁Q : (conjClosure K T ⊔ T) ⊓ pCoreOf 2 H ≤
      centralizerMod V₁ (conjClosure K T ⊔ T) (conjClosure I H) := fun x hx =>
    ⟨hx.1, h.K₀T_le_normalizer_V₁ hx.1, fun e he => hQV₁ x hx.2 e (hIHU he)⟩
  have hNo₁ := h7 (centralizerMod V₁ (conjClosure K T ⊔ T) (conjClosure I H))
    (centralizerMod_le_left _ _ _)
    (le_normalizer_centralizerMod h.K₀T_le_normalizer_V₁ Subgroup.le_normalizer hIHN) hN₁Q
    (CFSG.Quasithin.RonanF918.commutator_kernel_le_pCoreOf h h.K₀T_le_normalizer_V₁ hIHN hnt1)
  have hker₁ : HasExactSectionActionKernel (conjClosure K T ⊔ T) (conjClosure I H) V₁
      (centralizerMod V₁ (conjClosure K T ⊔ T) (conjClosure I H)) :=
    ⟨hIHN, h.K₀T_le_normalizer_V₁, le_trans hV₁I (le_conjClosure I H), fun x hx =>
      ⟨fun hall => ⟨hx, h.K₀T_le_normalizer_V₁ hx, hall⟩, fun hxN e he => hxN.2.2 e he⟩⟩
  have hN₂Q : (conjClosure K T ⊔ T) ⊓ pCoreOf 2 H ≤
      centralizerMod (conjClosure I H) (conjClosure K T ⊔ T) (conjClosure Vp H) := fun x hx =>
    ⟨hx.1, hIHN hx.1, fun e he => le_conjClosure I H (hV₁I (hQV₁ x hx.2 e he))⟩
  have hNo₂ := h7 (centralizerMod (conjClosure I H) (conjClosure K T ⊔ T) (conjClosure Vp H))
    (centralizerMod_le_left _ _ _)
    (le_normalizer_centralizerMod hIHN Subgroup.le_normalizer h.K₀T_le_normalizer_U) hN₂Q
    (CFSG.Quasithin.RonanF918.commutator_kernel_le_pCoreOf h hIHN h.K₀T_le_normalizer_U hnt2)
  have hker₂ : HasExactSectionActionKernel (conjClosure K T ⊔ T) (conjClosure Vp H)
      (conjClosure I H)
      (centralizerMod (conjClosure I H) (conjClosure K T ⊔ T) (conjClosure Vp H)) :=
    ⟨h.K₀T_le_normalizer_U, hIHN, hIHU, fun x hx =>
      ⟨fun hall => ⟨hx, hIHN hx, hall⟩, fun hxN e he => hxN.2.2 e he⟩⟩
  rcases h.F918_6 (le_trans hV₁I (le_conjClosure I H)) hIHU hIHN hW0 hWK with ha' | ⟨hb1, -⟩ | hc
  · exact ha ha'
  · exact noFaithfulFF_tilde_transport _ _ _ _ hIHel (hIHU.trans hUN) hker₁ hNo₁ hb1
  · rcases hc with hc | hc
    · exact noFaithfulFF_tilde_transport _ _ _ _ hIHel (hIHU.trans hUN) hker₁ hNo₁
        (F9.IsStrongFFInt.isFFInt hc)
    · exact noFaithfulFF_quotient_transport _ _ _ _ hIHq hUW hker₂ hNo₂
        (F9.IsStrongFFInt.isFFInt hc)

private theorem f918_o2inv_of_isIrrPlusT {G : Type} [Group G] [Finite G]
    {T V L V₁ Vp H K I : Subgroup G} (h : HypF918 T V L V₁ Vp H K)
    (hI : IsIrrPlusT V₁ Vp H K T I) :
    pCoreOf 2 (conjClosure K T ⊔ T) ≤ Subgroup.normalizer (I : Set G) :=
  CFSG.Quasithin.RonanF918.o2inv_of_homHat h hI.1 hI.2.1 hI.2.2.1 hI.2.2.2

private theorem f918_exists_isIrrPlusT {G : Type} [Group G] [Finite G]
    {T V L V₁ Vp H K : Subgroup G} (h : HypF918 T V L V₁ Vp H K) :
    ∃ I : Subgroup G, IsIrrPlusT V₁ Vp H K T I := by
  obtain ⟨I, hV₁I, hIU, W, hWinv, hirrU⟩ := exists_isIrrPlusTildeU h
  have hirrT : IsIrrPlusTildeT h hIU := isIrrPlusTildeT_of_ambient h hIU W hWinv hirrU
  exact ⟨I, hV₁I, hIU, isIrrPlusTilde_of_module h hV₁I hIU hirrT,
    CFSG.Quasithin.RonanF918.hom_of_isIrrPlusTildeT h hV₁I hIU hirrT⟩

private structure F918Inputs : Prop where
  d310 : CFSG.Quasithin.D310
  d391 : CFSG.Quasithin.D391
  insp4 : CFSG.Quasithin.Insp4
  fine4 : CFSG.Quasithin.F918Fine4
  hat6 : CFSG.Quasithin.F918Fine4Hat6
  griess : CFSG.Open.GriessAllModelsStatement
  d36 : CFSG.Quasithin.D36
  d37 : CFSG.Quasithin.D37
  d321 : CFSG.Quasithin.D321
  insp5a : CFSG.Quasithin.Insp5a
  d321O2 : CFSG.Quasithin.H13.T326.D321O2

private theorem f918_four {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}
    (inp : F918Inputs)
    (h : HypF918 T V L V₁ Vp H K) (hSQ : CFSG.SectionRank.IsSQTKCat ↥H) {I : Subgroup G}
    (hI : IsIrrPlusT V₁ Vp H K T I) (hK : K = conjClosure K T) :
    IsF918FourList ↥(KstOf V₁ (conjClosure Vp H) K) ∧
      (H ≤ Subgroup.normalizer (I : Set G) ∨
        (tildeOf V₁ (conjClosure I T) = tildeOf V₁ I ∧
          ∃ hV : IsElemAbelian 2 (hat' V₁ Vp H K T I),
            IsFFInt (hat' V₁ Vp H K T (K ⊔ T)) (hat' V₁ Vp H K T I) hV) ∨
        (F918NatChoice4 V₁ Vp H K T I ∧
          (∃ t : G, t ∈ T ∧ t ∉ Subgroup.normalizer (I : Set G)) ∧
          ∀ t : G, t ∈ T → t ∉ Subgroup.normalizer (I : Set G) →
            HatDSum V₁ Vp H K T (conjClosure I H) I t ∧
            ¬ ModIso (hat' V₁ Vp H K T K) (hat' V₁ Vp H K T I)
                (hat' V₁ Vp H K T (conjSub t⁻¹ I)))) := by
  obtain ⟨hV₁I, hIU, hIrr, hhom⟩ := hI
  have hirr : IsIrrPlusTildeT h hIU :=
    CFSG.Quasithin.RonanF918.isIrrPlusTildeT_of_homHat h hV₁I hIU hIrr hhom
  have hH := CFSG.Quasithin.G64.sqtkGroup_of_isSQTKCat hSQ
  have hK' : conjClosure K T = K := hK.symm
  obtain ⟨hfine, hfour⟩ := F918_4_fine h hH hK' hV₁I hIU hirr inp.d310 inp.d391 inp.insp4 inp.fine4
  haveI := factElem h hIU
  exact ⟨CFSG.Quasithin.RonanF918.isF918FourListU_of_fourListFine
    (CFSG.Quasithin.RonanF918.isQuasisimple_autIH h) hfine,
    CFSG.Quasithin.RonanF918.four_cases_of_inputs inp.griess h hK' hV₁I hIU hirr hfour
      (inp.fine4 G T V L V₁ Vp H K h hH hK').1 hH inp.hat6⟩

private theorem f918_five {G : Type} [Group G] [Finite G]
    {T V L V₁ Vp H K : Subgroup G} (inp : F918Inputs) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK)
    (h : HypF918 T V L V₁ Vp H K) (hSQ : CFSG.SectionRank.IsSQTKCat ↥H) {I : Subgroup G}
    (hI : IsIrrPlusT V₁ Vp H K T I) (hK : conjClosure K T ≠ K) :
    IsF918FiveList ↥(KstOf V₁ (conjClosure Vp H) K) ∧
      ((H ≤ Subgroup.normalizer (I : Set G) ∧
          ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
            Nonempty (↥(KstOf V₁ (conjClosure Vp H) K) ≃* ↥(StatedSL 2 F)) ∧
            ModelOn (tensorModel 2 F) (tildeOf V₁ (conjClosure K T)) (tildeOf V₁ I)) ∨
        (H ≤ Subgroup.normalizer (I : Set G) ∧
          ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
            Nonempty (↥(KstOf V₁ (conjClosure Vp H) K) ≃* ↥(StatedSL 3 F)) ∧
            ModelOn (tensorModel 3 F) (tildeOf V₁ (conjClosure K T)) (tildeOf V₁ I)) ∨
        ∀ (t : G) (ht : t ∈ T), t ∉ Subgroup.normalizer (K : Set G) →
          CFSG.Quasithin.RonanF918.F918FiveIiiS h hI.2.1 ht) := by
  obtain ⟨hV₁I, hIU, hIrr, hhom⟩ := hI
  have hirr : IsIrrPlusTildeT h hIU :=
    CFSG.Quasithin.RonanF918.isIrrPlusTildeT_of_homHat h hV₁I hIU hIrr hhom
  have hH := CFSG.Quasithin.G64.sqtkGroup_of_isSQTKCat hSQ
  exact CFSG.Quasithin.RonanF918.five_alternatives inp.d36 inp.d37 inp.d321 inp.insp5a hA37 hA38 h hH
    hK hV₁I hIU hirr

private theorem f918_mult_d {G : Type} [Group G] [Finite G]
    {T V L V₁ Vp H K : Subgroup G} (hA37 : A37ForSQTK) (hA38 : A38ForSQTK)
    (h : HypF918 T V L V₁ Vp H K) (hSQ : CFSG.SectionRank.IsSQTKCat ↥H) {I : Subgroup G}
    (hI : IsIrrPlusT V₁ Vp H K T I) (hK : conjClosure K T ≠ K)
    (hD : CFSG.Quasithin.RonanF918.F918IiiD h hI.2.1) :
    F918ResidualMultiplicity V₁ Vp H K T I := by
  have hI' := hI
  obtain ⟨hV₁I, hIU, hIrr, hhom⟩ := hI'
  have hirr : IsIrrPlusTildeT h hIU :=
    CFSG.Quasithin.RonanF918.isIrrPlusTildeT_of_homHat h hV₁I hIU hIrr hhom
  have hH := CFSG.Quasithin.G64.sqtkGroup_of_isSQTKCat hSQ
  obtain ⟨n, F, hF, hFin, hn, hcard, data, hcases⟩ :=
    CFSG.Quasithin.RonanF918.multData_of_iiiD h hH hA37 hA38 hK hV₁I hIU hirr hD
  let data' : F918MultiplicityData V₁ Vp H K T I F :=
    { coordinates := data.coordinates
      coordinates_surjective := data.coordinates_surjective
      coordinates_kernel := data.coordinates_kernel
      markedComponent := data.markedComponent
      markedComponent_surjective := data.markedComponent_surjective
      markedComponent_kernel := data.markedComponent_kernel
      component_equivariance := data.component_equivariance
      centralizer_normalizes := data.centralizer_normalizes
      normalizer_normalizes := data.normalizer_normalizes
      multiplicity := data.multiplicity
      multiplicity_equivariance := data.multiplicity_equivariance
      multiplicity_kernel := data.multiplicity_kernel
      normalizerAction := data.normalizerAction
      normalizer_equivariance := data.normalizer_equivariance
      fieldAction := data.fieldAction
      semilinear := data.semilinear
      commutant_transport := data.commutant_transport
      actual_image_transport := data.actual_image_transport
      full_commutant := data.full_commutant }
  exact ⟨n, F, hF, hFin, hn, hcard, data', hcases⟩

private theorem f918_iii_body {G : Type} [Group G] [Finite G]
    {T V L V₁ Vp H K : Subgroup G} (inp : F918Inputs) (hA37 : A37ForSQTK)
    (hA38 : A38ForSQTK) (h : HypF918 T V L V₁ Vp H K) (hSQ : CFSG.SectionRank.IsSQTKCat ↥H) {I : Subgroup G}
    (hI : IsIrrPlusT V₁ Vp H K T I) (hK : conjClosure K T ≠ K) {t : G} (ht : t ∈ T)
    (htK : t ∉ Subgroup.normalizer (K : Set G)) (hsq : t * t ∈ Subgroup.normalizer (K : Set G))
    (hG : CFSG.Quasithin.RonanF918.F918Good h hI.2.1 ht) :
    HatDSum V₁ Vp H K T (conjClosure I H) ⁅conjClosure I H, K⁆ t ∧
    tildeOf V₁ ⁅conjClosure I H, K⁆ ≤
      tildeOf V₁ (conjClosure I H) ⊓
        Subgroup.centralizer (tildeOf V₁ (conjSub t⁻¹ K) : Set (GtOf V₁)) ∧
    ((
              ((hat' V₁ Vp H K T ⁅conjClosure I H, K⁆ =
                  hat' V₁ Vp H K T (conjClosure I H) ⊓
                    Subgroup.centralizer (hat' V₁ Vp H K T (conjSub t⁻¹ K) : Set _)) ∧
              (hat' V₁ Vp H K T ⁅conjClosure I H, K⁆ = hat' V₁ Vp H K T I ∧
                  (F918NatChoice5 V₁ Vp H K T I ∨
                    ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F) (σ : F →+* F),
                      Even n ∧ Nat.card F = 2 ^ n ∧ σ ≠ RingHom.id F ∧ (∀ x, σ (σ x) = x) ∧
                      Nonempty (↥(KstOf V₁ (conjClosure Vp H) K) ≃* ↥(StatedSL 2 F)) ∧
                      ModelOn (orthModel F σ) (hat' V₁ Vp H K T K) (hat' V₁ Vp H K T I)))) ∨
                ((tildeOf V₁ ⁅conjClosure I H, K⁆ =
                  tildeOf V₁ (conjClosure I H) ⊓
                    Subgroup.centralizer (tildeOf V₁ (conjSub t⁻¹ K) : Set (GtOf V₁))) ∧
                (LieModel ↥(KstOf V₁ (conjClosure Vp H) K) .PSL 3 2 1 ∧
                  (∃ s : G, s ∈ T ∧ s ∈ Subgroup.normalizer (K : Set G) ∧
                    s ∉ Subgroup.normalizer (I : Set G)) ∧
                  ∀ s : G, s ∈ T → s ∈ Subgroup.normalizer (K : Set G) →
                    s ∉ Subgroup.normalizer (I : Set G) →
                    (tildeOf V₁ ⁅conjClosure I H, K⁆ =
                      tildeOf V₁ I ⊔ tildeOf V₁ (conjSub s⁻¹ I) ∧
                      tildeOf V₁ I ⊓ tildeOf V₁ (conjSub s⁻¹ I) = ⊥) ∧
                    Nat.card ↥(tildeOf V₁ I) = 2 ^ 3)) ∨
                ((tildeOf V₁ ⁅conjClosure I H, K⁆ =
                  tildeOf V₁ (conjClosure I H) ⊓
                    Subgroup.centralizer (tildeOf V₁ (conjSub t⁻¹ K) : Set (GtOf V₁))) ∧
                (LieModel ↥(KstOf V₁ (conjClosure Vp H) K) .PSL 3 2 1 ∧
                  (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
                    ModelOn (multiNatModel 3 4 F) (tildeOf V₁ K) (tildeOf V₁ ⁅conjClosure I H, K⁆)) ∧
                  (Nonempty (↥(oTwoRes
                      (autOn (tildeOf V₁ (centralizerMod (pCoreOf 2 H) H (conjClosure K T)))
                        (tildeOf V₁ (conjClosure I H)))) ≃* Multiplicative (ZMod 5)) ∨
                    Nonempty (↥(oTwoRes
                      (autOn (tildeOf V₁ (centralizerMod (pCoreOf 2 H) H (conjClosure K T)))
                        (tildeOf V₁ (conjClosure I H)))) ≃*
                          (Multiplicative (ZMod 5) × Multiplicative (ZMod 5))))))) ∨
                F918ResidualMultiplicity V₁ Vp H K T I) := by
  have hI' := hI
  obtain ⟨hV₁I, hIU, hIrr, hhom⟩ := hI'
  have hirr : IsIrrPlusTildeT h hIU :=
    CFSG.Quasithin.RonanF918.isIrrPlusTildeT_of_homHat h hV₁I hIU hIrr hhom
  have hH := CFSG.Quasithin.G64.sqtkGroup_of_isSQTKCat hSQ
  obtain ⟨hdsum, hincl, hrest⟩ := CFSG.Quasithin.RonanF918.five_iii_cases_nofix inp.d321O2 h hH hA37 hA38
    hK hV₁I hIU hIrr hirr ht htK hsq hG
  refine ⟨hdsum, hincl, ?_⟩
  rcases hrest with ha | hb | hc | hd
  · exact Or.inl (Or.inl ha)
  · exact Or.inl (Or.inr (Or.inl hb))
  · exact Or.inl (Or.inr (Or.inr hc))
  · exact Or.inr (f918_mult_d hA37 hA38 h hSQ hI hK hd)

private theorem isIrrPlusT_congr {G : Type} [Group G] {T V₁ Vp H K K' I : Subgroup G}
    (hcc : conjClosure K' T = conjClosure K T) (hI : IsIrrPlusT V₁ Vp H K T I) :
    IsIrrPlusT V₁ Vp H K' T I := by
  let P : Subgroup G → Prop := fun K₀ =>
    V₁ ≤ I ∧ I ≤ conjClosure Vp H ∧ IsIrrPlusTilde V₁ K₀ I ∧
      ∀ S : Subgroup (GhOf V₁ (conjClosure Vp H) K₀),
        S ≤ hatOf V₁ (conjClosure Vp H) K₀ (conjClosure I T) →
        hatOf V₁ (conjClosure Vp H) K₀ K₀ ≤ Subgroup.normalizer (S : Set _) →
        ModIso (hatOf V₁ (conjClosure Vp H) K₀ K₀) S (hatOf V₁ (conjClosure Vp H) K₀ I) →
        S ≤ hatOf V₁ (conjClosure Vp H) K₀ I
  have key : P (conjClosure K T) → P (conjClosure K' T) := fun hP => Eq.mpr (congrArg P hcc) hP
  exact key hI

private theorem f918_iii {G : Type} [Group G] [Finite G]
    {T V L V₁ Vp H K : Subgroup G} (inp : F918Inputs) (hA37 : A37ForSQTK)
    (hA38 : A38ForSQTK) (h : HypF918 T V L V₁ Vp H K) (hSQ : CFSG.SectionRank.IsSQTKCat ↥H) {I : Subgroup G}
    (hI : IsIrrPlusT V₁ Vp H K T I) (hK : conjClosure K T ≠ K)
    (hiii : ∀ (t : G) (ht : t ∈ T), t ∉ Subgroup.normalizer (K : Set G) →
      CFSG.Quasithin.RonanF918.F918FiveIiiS h hI.2.1 ht) :
    ∀ t : G, t ∈ T → t ∉ Subgroup.normalizer (K : Set G) →
      ∃ K' : Subgroup G, (K' = K ∨ K' = conjSub t⁻¹ K) ∧
        HatDSum V₁ Vp H K' T (conjClosure I H) ⁅conjClosure I H, K'⁆ t ∧
        tildeOf V₁ ⁅conjClosure I H, K'⁆ ≤
          tildeOf V₁ (conjClosure I H) ⊓
            Subgroup.centralizer (tildeOf V₁ (conjSub t⁻¹ K') : Set (GtOf V₁)) ∧
        ((
              ((hat' V₁ Vp H K' T ⁅conjClosure I H, K'⁆ =
                  hat' V₁ Vp H K' T (conjClosure I H) ⊓
                    Subgroup.centralizer (hat' V₁ Vp H K' T (conjSub t⁻¹ K') : Set _)) ∧
              (hat' V₁ Vp H K' T ⁅conjClosure I H, K'⁆ = hat' V₁ Vp H K' T I ∧
                  (F918NatChoice5 V₁ Vp H K' T I ∨
                    ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F) (σ : F →+* F),
                      Even n ∧ Nat.card F = 2 ^ n ∧ σ ≠ RingHom.id F ∧ (∀ x, σ (σ x) = x) ∧
                      Nonempty (↥(KstOf V₁ (conjClosure Vp H) K') ≃* ↥(StatedSL 2 F)) ∧
                      ModelOn (orthModel F σ) (hat' V₁ Vp H K' T K') (hat' V₁ Vp H K' T I)))) ∨
                ((tildeOf V₁ ⁅conjClosure I H, K'⁆ =
                  tildeOf V₁ (conjClosure I H) ⊓
                    Subgroup.centralizer (tildeOf V₁ (conjSub t⁻¹ K') : Set (GtOf V₁))) ∧
                (LieModel ↥(KstOf V₁ (conjClosure Vp H) K') .PSL 3 2 1 ∧
                  (∃ s : G, s ∈ T ∧ s ∈ Subgroup.normalizer (K' : Set G) ∧
                    s ∉ Subgroup.normalizer (I : Set G)) ∧
                  ∀ s : G, s ∈ T → s ∈ Subgroup.normalizer (K' : Set G) →
                    s ∉ Subgroup.normalizer (I : Set G) →
                    (tildeOf V₁ ⁅conjClosure I H, K'⁆ =
                      tildeOf V₁ I ⊔ tildeOf V₁ (conjSub s⁻¹ I) ∧
                      tildeOf V₁ I ⊓ tildeOf V₁ (conjSub s⁻¹ I) = ⊥) ∧
                    Nat.card ↥(tildeOf V₁ I) = 2 ^ 3)) ∨
                ((tildeOf V₁ ⁅conjClosure I H, K'⁆ =
                  tildeOf V₁ (conjClosure I H) ⊓
                    Subgroup.centralizer (tildeOf V₁ (conjSub t⁻¹ K') : Set (GtOf V₁))) ∧
                (LieModel ↥(KstOf V₁ (conjClosure Vp H) K') .PSL 3 2 1 ∧
                  (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
                    ModelOn (multiNatModel 3 4 F) (tildeOf V₁ K') (tildeOf V₁ ⁅conjClosure I H, K'⁆)) ∧
                  (Nonempty (↥(oTwoRes
                      (autOn (tildeOf V₁ (centralizerMod (pCoreOf 2 H) H (conjClosure K' T)))
                        (tildeOf V₁ (conjClosure I H)))) ≃* Multiplicative (ZMod 5)) ∨
                    Nonempty (↥(oTwoRes
                      (autOn (tildeOf V₁ (centralizerMod (pCoreOf 2 H) H (conjClosure K' T)))
                        (tildeOf V₁ (conjClosure I H)))) ≃*
                          (Multiplicative (ZMod 5) × Multiplicative (ZMod 5))))))) ∨
                F918ResidualMultiplicity V₁ Vp H K' T I) := by
  intro t ht htK
  have hinvT : t⁻¹ ∈ T := T.inv_mem ht
  have hH := CFSG.Quasithin.G64.sqtkGroup_of_isSQTKCat hSQ
  have hsq : t * t ∈ Subgroup.normalizer (K : Set G) :=
    CFSG.Quasithin.RonanF918.sq_mem_normalizer_of_not_mem h hH hA37 hA38 hK ht htK
  have hinvK : t⁻¹ ∉ Subgroup.normalizer (K : Set G) := fun hh => htK ((Subgroup.inv_mem_iff _).mp hh)
  rcases CFSG.Quasithin.RonanF918.iii_dichotomy h hI.2.1 ht hsq (hiii t⁻¹ hinvT hinvK) with hg | hg
  · exact ⟨K, Or.inl rfl, f918_iii_body inp hA37 hA38 h hSQ hI hK ht htK hsq hg⟩
  · have hcc : conjClosure (conjSub t⁻¹ K) T = conjClosure K T :=
      CFSG.Quasithin.RonanF918.conjClosure_conjSub_eq hinvT
    have hI'' : IsIrrPlusT V₁ Vp H (conjSub t⁻¹ K) T I := isIrrPlusT_congr hcc hI
    exact ⟨conjSub t⁻¹ K, Or.inr rfl,
      f918_iii_body inp hA37 hA38 (CFSG.Quasithin.RonanF918.hypF918_conj h hinvT) hSQ hI''
        (CFSG.Quasithin.RonanF918.conjClosure_conjSub_ne ht hK) ht
        (CFSG.Quasithin.RonanF918.not_mem_normalizer_conjSub htK)
        (CFSG.Quasithin.RonanF918.sq_mem_normalizer_conjSub hsq) hg⟩

private theorem f_9_18_of_inputs
    (inp : F918Inputs) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) : F_9_18 := by
  intro G _ _ T V L V₁ Vp H K hyp hSQ
  have hnormal : H ≤ Subgroup.normalizer (conjClosure K T : Set G) :=
    CFSG.Quasithin.RonanF918.H_le_normalizer_K₀ (CFSG.Quasithin.G64.sqtkGroup_of_isSQTKCat hSQ)
      hA37 hA38 hyp.K_cComp hyp.toHypF98.toHypF91.sylow_H
  have h : HypF918 T V L V₁ Vp H K := hypF918Conditional_of_literal hyp hnormal
  refine ⟨f918_exists_isIrrPlusT h, CFSG.Quasithin.RonanF918.clause_two h, ?_, ?_⟩
  · intro W hV₁W hWU hWN hW0 hWK
    exact f918_clause_six h hV₁W hWU hWN hW0 hWK
  · intro I hI
    have hI' := hI
    obtain ⟨hV₁I, hIU, hIrr, -⟩ := hI'
    obtain ⟨hsyl, hoT, hnorm, hV₁U, hUQ, hHN, hHU, hel, hE⟩ :=
      CFSG.Quasithin.RonanF918.clause_one_core h
    refine ⟨⟨hSQ, hsyl, hoT, hnorm, hyp.K_cComp, hyp.K_quasisimple, hV₁U, hUQ, hHN, hHU, hel, hE,
      f918_o2inv_of_isIrrPlusT h hI, hIrr⟩, ?_,
      fun hK => f918_four inp h hSQ hI hK,
      fun hK => ?_, ?_⟩
    · intro B hBL hfaith hQ X hX
      exact CFSG.Quasithin.RonanF918.F918_3_general h hIU hIrr hBL hfaith hQ hX
    · obtain ⟨hlist, hcases⟩ := f918_five inp hA37 hA38 h hSQ hI hK.1
      refine ⟨hlist, ?_⟩
      rcases hcases with hi | hii | hiii
      · exact Or.inl hi
      · exact Or.inr (Or.inl hii)
      · refine Or.inr (Or.inr ⟨?_, f918_iii inp hA37 hA38 h hSQ hI hK.1 hiii⟩)
        by_contra hcon
        push Not at hcon
        apply hK.1
        apply le_antisymm
        · refine conjClosure_le fun t ht z hz => ?_
          exact (Subgroup.mem_normalizer_iff.mp (hcon t ht) z).mp hz
        · exact le_conjClosure K T
    · intro h7
      exact f918_clause_seven h hV₁I hIU hIrr h7

section F918AsProof

theorem as_F_9_18
    : F_9_18 := by
  have hA37 : A37ForSQTK := CFSG.Quasithin.a37ForSQTK_proved
  have hA38 : A38ForSQTK := CFSG.Quasithin.a38ForSQTK_proved
  have h310 : CFSG.Quasithin.D310 := CFSG.Quasithin.H13.d310_holds
  have h391 : CFSG.Quasithin.D391 := CFSG.Quasithin.d391_holds
  have hA21 : CFSG.Quasithin.AsA21SQTKSection := CFSG.Quasithin.asA21SQTKSection
  have hG2 : CFSG.Quasithin.FactG2Cayley := CFSG.Quasithin.factG2Cayley_holds
  have h42 : CFSG.Quasithin.AsB42 := CFSG.Quasithin.asB42_holds
  have h45 : CFSG.Quasithin.AsB45 := CFSG.Quasithin.asB45_holds
  have hB56 : CFSG.Quasithin.AsB56 := CFSG.Quasithin.asB56_holds
  have hF : CFSG.Quasithin.Vol2.Ch10.SecA.Facts10_1 :=
    CFSG.Quasithin.Vol2.Ch10.SecA.facts10_1_holds
  have hNS : CFSG.Quasithin.Insp5aNonShape := CFSG.Quasithin.insp5aNonShape_holds
  have hL38 : CFSG.Quasithin.D3L38 := CFSG.Quasithin.d3L38_of_a38 CFSG.Quasithin.d3A38_holds
  have h9 := CFSG.Quasithin.SmithD321.a38B42_of hF hNS
  have h36 := CFSG.Quasithin.SmithD39Two.d36c_holds
  have h37 : CFSG.Quasithin.D37 := CFSG.Quasithin.d37_holds
  have h38 := CFSG.Quasithin.SmithD39Two.d38Top_holds
  have h321 : CFSG.Quasithin.D321 := by
    intro W _ _ M Mp T L V hD t htT htn hMp hq _ _ _ _ _ _ _ _
    exact CFSG.Quasithin.d321_holds W M Mp T L V hD t htT htn hMp hq
  have hA23 := CFSG.Quasithin.a23SQTKListFact
  have hSz := CFSG.Quasithin.H13.simpleThreePrimeSuzukiFact
  exact f_9_18_of_inputs
    ⟨h310, h391, CFSG.Quasithin.insp4_of_inputs hA21 hG2 h42 h45 h310,
      CFSG.Quasithin.F918Fine4Pf.f918Fine4_of h310 h391,
      CFSG.Quasithin.F918Fine4Pf.f918Fine4Hat6_of h310 h391 hA21,
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement,
      CFSG.Quasithin.d36_holds, h37, h321,
      CFSG.Quasithin.insp5a_of_inputs hA21 h45 hF hNS,
      CFSG.Quasithin.H13.T326.d321O2_of hA21 h42 h9 h36 h37 hB56 h38 hA23 hSz hL38⟩
    hA37 hA38

end F918AsProof

end CFSG.ASVolI
