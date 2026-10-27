module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqSzModule
import CFSG.RankThree.GF2n.Tim81.Sec2.SzThreeGen
import CFSG.ClassicalInvolution.AschTight.Sec7L98A
public import CFSG.Assembly.OrderReductions.ReplacementGeometry
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic
public import CFSG.Quasithin.Background.SmithC27Setup
public import CFSG.Quasithin.EmptyFaithful.S151bRank

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.GH74.QTGen4.DSGen4 (IsElemSec)
open scoped commutatorElement

public section

namespace CFSG.Quasithin.Stroth

variable {G : Type} [Group G] [Finite G]
private theorem exists_closure_three_conj_eq_top_of_sz {X : Type}
    [Group X] {a : ℕ} (ha : 1 ≤ a) (e : X ≃* Sz a) {x : X} (hx : x * x = 1) (hx1 : x ≠ 1) :
    ∃ g₁ g₂ : X, Subgroup.closure ({x, g₁ * x * g₁⁻¹, g₂ * x * g₂⁻¹} : Set X) = ⊤ := by
  have hK : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1) :=
    GaloisField.card 2 (2 * a + 1) (by omega)
  let f : X ≃* CFSG.Blueprint.suzukiGroup a (GaloisField 2 (2 * a + 1)) :=
    e.trans (suzukiGroupEquivSz a _ hK).symm
  obtain ⟨h₁, h₂, hgen⟩ := CFSG.RankThree.GF2n.Tim81.Sec2.exists_closure_three_conj_eq_top hK ha
    (f x) (by rw [← map_mul, hx, map_one]) (fun h => hx1 (f.injective (by rw [h, map_one])))
  refine ⟨f.symm h₁, f.symm h₂, ?_⟩
  have h := congrArg (Subgroup.map f.symm.toMonoidHom) hgen
  rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _ f.symm.surjective] at h
  rw [← h]
  congr 1
  simp [Set.image_insert_eq, Set.image_singleton]

private theorem card_le_of_isElemAbelian_of_sz {X : Type} [Group X]
    [Finite X] {a : ℕ} (ha : 1 ≤ a) (e : X ≃* Sz a) {A : Subgroup X}
    (hA : IsElemAbelian 2 A) : Nat.card A ≤ 2 ^ (2 * a + 1) := by
  have hBt : CFSG.GH74.Uniqueness.Bender.BenderType X (2 * a + 1) 2 1 :=
    CFSG.GH74.Uniqueness.Bender.BenderType.suzuki a ha
      (e.trans (MulEquiv.subgroupCongr (CFSG.GH74.Uniqueness.Bender.szModel_eq_open_sz a).symm))
  have hAp : IsPGroup 2 A := fun y => ⟨1, Subtype.ext (by simpa using hA.2 y y.2)⟩
  obtain ⟨Q, hAQ⟩ := hAp.exists_le_sylow
  obtain ⟨t, hc⟩ := hBt.exists_benderCore Q
  have hAZ := hc.elemAbelian_le_rootCenter hAQ fun y hy => by
    have := hA.2 y hy
    rwa [sq] at this
  calc Nat.card A ≤ Nat.card (CFSG.GH74.Uniqueness.Bender.rootCenter (Q : Subgroup X)) :=
        Subgroup.card_le_of_le hAZ
    _ = 2 ^ (2 * a + 1) := hc.card_center

private theorem relIndex_inf_pCoreOf_le_of_sz {L A : Subgroup G}
    {a : ℕ} (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L ≃* Sz a)) (hAL : A ≤ L)
    (hA : IsElemAbelian 2 A) : (A ⊓ pCoreOf 2 L).relIndex A ≤ 2 ^ (2 * a + 1) := by
  obtain ⟨e⟩ := hSz
  let φ : ↥A →* oTwoQuot ↥L :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hAL)
  have hker : (A ⊓ pCoreOf 2 L).subgroupOf A = φ.ker := by
    ext ⟨y, hy⟩
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, Subgroup.mem_inf]
    simp only [φ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨-, z, hz, hzy⟩
      rwa [show Subgroup.inclusion hAL ⟨y, hy⟩ = z from Subtype.ext hzy.symm]
    · intro h
      exact ⟨hy, _, h, rfl⟩
  have hrange : IsElemAbelian 2 φ.range := by
    refine ⟨⟨⟨fun u v => ?_⟩⟩, fun z hz => ?_⟩
    · obtain ⟨_, u', rfl⟩ := u
      obtain ⟨_, v', rfl⟩ := v
      exact Subtype.ext (by
        simp only [Subgroup.coe_mul]
        rw [← map_mul, ← map_mul, hA.1.is_comm.comm u' v'])
    · obtain ⟨z', rfl⟩ := hz
      rw [← map_pow, show z' ^ 2 = 1 from Subtype.ext (by simpa using hA.2 z' z'.2), map_one]
  calc (A ⊓ pCoreOf 2 L).relIndex A = Nat.card φ.range := by
        rw [Subgroup.relIndex, hker, Subgroup.index_ker]
    _ ≤ 2 ^ (2 * a + 1) := card_le_of_isElemAbelian_of_sz ha e hrange

private theorem relIndex_inf_centralizer_le_of_isMaxElemAbelian {T A V D : Subgroup G}
    (hA : IsMaxElemAbelian T A) (hV : IsElemAbelian 2 V) (hVT : V ≤ T) (hDA : D ≤ A)
    (hDV : D ≤ Subgroup.centralizer (V : Set G)) :
    (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V ≤ D.relIndex A := by
  set C := A ⊓ Subgroup.centralizer (V : Set G) with hC
  have hCel : IsElemAbelian 2 C := by
    refine ⟨⟨⟨fun u v => Subtype.ext ?_⟩⟩, fun y hy => hA.2.1.2 y hy.1⟩
    have h := congrArg Subtype.val (hA.2.1.1.is_comm.comm (⟨u, u.2.1⟩ : ↥A) ⟨v, v.2.1⟩)
    simpa using h
  have hcomm : ∀ c ∈ C, ∀ v ∈ V, c * v = v * c := fun c hc v hv =>
    (Subgroup.mem_centralizer_iff.mp hc.2 v hv).symm
  have hCV : IsElemAbelian 2 (C ⊔ V) := isElemAbelian_sup_of_commute151b hCel hV hcomm
  have h4 : Nat.card ↥(C ⊔ V) ≤ Nat.card A :=
    hA.2.2 _ (sup_le (inf_le_left.trans hA.1) hVT) hCV
  have hCN : C ≤ Subgroup.normalizer (V : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  have e3 := CFSG.OrderReductions.ReplacementGeometry.card_product_mul_card_intersection C V hCN
  have e1 : (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V *
      Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) = Nat.card V := by
    have := Subgroup.relIndex_mul_card (V ⊓ Subgroup.centralizer (A : Set G)) V
    rwa [inf_eq_left.mpr (inf_le_left : V ⊓ Subgroup.centralizer (A : Set G) ≤ V)] at this
  have e2 : D.relIndex A * Nat.card D = Nat.card A := by
    have := Subgroup.relIndex_mul_card D A
    rwa [inf_eq_left.mpr hDA] at this
  have h5 : Nat.card ↥(C ⊓ V) ≤ Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := by
    refine Subgroup.card_le_of_le fun y hy => Subgroup.mem_inf.mpr ⟨hy.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h' := congrArg Subtype.val (hA.2.1.1.is_comm.comm (⟨h, hh⟩ : ↥A) ⟨y, hy.1.1⟩)
    simpa using h'
  have h6 : Nat.card D ≤ Nat.card C := Subgroup.card_le_of_le fun y hy => ⟨hDA hy, hDV hy⟩
  have hw : 0 < Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := Nat.card_pos
  have hc : 0 < Nat.card C := Nat.card_pos
  generalize (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V = r₁ at e1 ⊢
  generalize D.relIndex A = r₂ at e2 ⊢
  generalize Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) = w at e1 h5 hw
  generalize Nat.card ↥(C ⊔ V) = s at h4 e3
  generalize Nat.card ↥(C ⊓ V) = i at e3 h5
  generalize Nat.card C = c at e3 h6 hc
  generalize Nat.card D = d at e2 h6
  generalize Nat.card V = v at e1 e3
  generalize Nat.card A = n at h4 e2
  refine Nat.le_of_mul_le_mul_right (c := w * c) ?_ (Nat.mul_pos hw hc)
  calc r₁ * (w * c) = (r₁ * w) * c := by ring
    _ = s * i := by rw [e1, e3]; ring
    _ ≤ n * i := Nat.mul_le_mul_right _ h4
    _ = r₂ * d * i := by rw [e2]
    _ ≤ r₂ * c * w := Nat.mul_le_mul (Nat.mul_le_mul_left _ h6) h5
    _ = r₂ * (w * c) := by ring

private theorem relIndex_ne_zero_of_finite (H K : Subgroup G) : H.relIndex K ≠ 0 := by
  intro h
  have := Subgroup.relIndex_mul_card H K
  rw [h, zero_mul] at this
  exact (Nat.card_pos (α := K)).ne' this.symm

private theorem le_normalizer_of_forall_conj_mem {L K : Subgroup G}
    (h : ∀ l ∈ L, ∀ k ∈ K, l * k * l⁻¹ ∈ K) : L ≤ Subgroup.normalizer (K : Set G) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨h l hl k, fun hk => ?_⟩
  have := h l⁻¹ (L.inv_mem hl) _ hk
  simpa [mul_assoc] using this

private theorem le_normalizer_thompsonJ_of_le_pCoreOf {L P : Subgroup G} (hP : IsSylowTwoOf P L)
    (hJ : thompsonJ P ≤ pCoreOf 2 L) : L ≤ Subgroup.normalizer (thompsonJ P : Set G) := by
  rw [← GammaExtra.thompsonJ_eq_of_le hJ (pCoreOf_le_of_isSylowTwoOf hP)]
  exact (le_normalizer_pCoreOf 2 L).trans (GammaExtra.normalizer_le_normalizer_thompsonJ _)

private theorem commutator_eq_one_of_not_thompsonJ_le
    {L P : Subgroup G} {a : ℕ} (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L ≃* Sz a))
    (hP : IsSylowTwoOf P L) (hJ : ¬ thompsonJ P ≤ pCoreOf 2 L) :
    ∀ l ∈ L, ∀ v ∈ omegaOneCenterOf (pCoreOf 2 L), ⁅l, v⁆ = 1 := by
  classical
  set E := pCoreOf 2 L with hE
  set V := omegaOneCenterOf E with hVdef
  have hEP : E ≤ P := pCoreOf_le_of_isSylowTwoOf hP
  have hEV : ∀ e ∈ E, ∀ v ∈ V, e * v = v * e := fun e he v hv =>
    Subgroup.mem_centralizer_iff.mp (A4.omegaOneCenterOf_le_centerOf E hv).2 e he
  have hVE : V ≤ E := fun v hv => (A4.omegaOneCenterOf_le_centerOf E hv).1
  have hVel : IsElemAbelian 2 V := SmithC27.isElemAbelian_omegaOneCenterOf E
  have hLV : L ≤ Subgroup.normalizer (V : Set G) :=
    (le_normalizer_pCoreOf 2 L).trans (A4.normalizer_le_normalizer_omegaOneCenterOf E)
  have hVP : V ≤ P := hVE.trans hEP
  obtain ⟨A, hA, hAE⟩ : ∃ A, IsMaxElemAbelian P A ∧ ¬ A ≤ E := by
    by_contra h
    push Not at h
    exact hJ (GammaExtra.thompsonJ_le h)
  obtain ⟨x, hxA, hxE⟩ := SetLike.not_le_iff_exists.mp hAE
  have hxL : x ∈ L := hP.1 (hA.1 hxA)
  obtain ⟨e⟩ := hSz
  set N₀ := CFSG.pCore 2 ↥L with hN₀
  have hq1 : (QuotientGroup.mk' N₀ ⟨x, hxL⟩ : oTwoQuot ↥L) ≠ 1 := by
    intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    exact hxE ⟨_, h, rfl⟩
  have hq2 : QuotientGroup.mk' N₀ ⟨x, hxL⟩ * QuotientGroup.mk' N₀ ⟨x, hxL⟩ =
      (1 : oTwoQuot ↥L) := by
    rw [← map_mul, show (⟨x, hxL⟩ : ↥L) * ⟨x, hxL⟩ = 1 from
      Subtype.ext (by simpa [sq] using hA.2.1.2 x hxA), map_one]
  obtain ⟨gb₁, gb₂, hgen⟩ := exists_closure_three_conj_eq_top_of_sz ha e hq2 hq1
  obtain ⟨g₁, rfl⟩ := QuotientGroup.mk'_surjective N₀ gb₁
  obtain ⟨g₂, rfl⟩ := QuotientGroup.mk'_surjective N₀ gb₂
  set A₁ := B6.conjSub (g₁ : G) A with hA₁
  set A₂ := B6.conjSub (g₂ : G) A with hA₂
  set W := (V ⊓ Subgroup.centralizer (A : Set G)) ⊓ (V ⊓ Subgroup.centralizer (A₁ : Set G)) ⊓
    (V ⊓ Subgroup.centralizer (A₂ : Set G)) with hWdef
  have hWL : ∀ l ∈ L, ∀ w ∈ W, w * l = l * w := by
    let N : Subgroup ↥L := (Subgroup.centralizer (W : Set G)).subgroupOf L
    have hmemN : ∀ y : ↥L, (∀ w ∈ W, w * (y : G) = y * w) → y ∈ N := fun y hy =>
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_centralizer_iff.mpr hy)
    have hpN : N₀ ≤ N := fun y hy => hmemN y fun w hw =>
      (hEV y ⟨y, hy, rfl⟩ w hw.1.1.1).symm
    have hxN : (⟨x, hxL⟩ : ↥L) ∈ N := hmemN _ fun w hw =>
      (Subgroup.mem_centralizer_iff.mp hw.1.1.2 x hxA).symm
    have hconj : ∀ (g : ↥L) (B : Subgroup G), B = B6.conjSub (g : G) A →
        W ≤ Subgroup.centralizer (B : Set G) → g * ⟨x, hxL⟩ * g⁻¹ ∈ N := by
      intro g B hB hWB
      refine hmemN _ fun w hw => ?_
      have hmem : (g : G) * x * (g : G)⁻¹ ∈ B := by
        rw [hB, B6.mem_conjSub]
        simpa [mul_assoc] using hxA
      exact (Subgroup.mem_centralizer_iff.mp (hWB hw) _ hmem).symm
    have hx₁N := hconj g₁ A₁ rfl fun w hw => hw.1.2.2
    have hx₂N := hconj g₂ A₂ rfl fun w hw => hw.2.2
    have hmap : N.map (QuotientGroup.mk' N₀) = ⊤ := by
      rw [eq_top_iff, ← hgen, Subgroup.closure_le]
      rintro _ (rfl | rfl | rfl)
      · exact ⟨_, hxN, rfl⟩
      · exact ⟨_, hx₁N, by simp⟩
      · exact ⟨_, hx₂N, by simp⟩
    have hNtop : N = ⊤ := by
      have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' N₀) N
      rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk', sup_eq_left.mpr hpN] at h1
      exact h1.symm
    intro l hl w hw
    have hlN : (⟨l, hl⟩ : ↥L) ∈ N := hNtop ▸ Subgroup.mem_top _
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hlN) w hw
  have hrel : ∀ B T : Subgroup G, IsMaxElemAbelian T B → V ≤ T → B ≤ L →
      (V ⊓ Subgroup.centralizer (B : Set G)).relIndex V ≤ 2 ^ (2 * a + 1) := by
    intro B T hB hVT hBL
    calc (V ⊓ Subgroup.centralizer (B : Set G)).relIndex V ≤ (B ⊓ E).relIndex B :=
          relIndex_inf_centralizer_le_of_isMaxElemAbelian hB hVel hVT inf_le_left
            (fun y hy => Subgroup.mem_centralizer_iff.mpr fun v hv => (hEV y hy.2 v hv).symm)
      _ ≤ 2 ^ (2 * a + 1) := relIndex_inf_pCoreOf_le_of_sz ha ⟨e⟩ hBL hB.2.1
  have hconjV : ∀ g : ↥L, V ≤ B6.conjSub (g : G) P := fun g => by
    calc V = B6.conjSub (g : G) V := (B6.conjSub_eq_self (hLV g.2)).symm
      _ ≤ B6.conjSub (g : G) P := (B6.conjSub (g : G)).monotone hVP
  have hconjL : ∀ g : ↥L, B6.conjSub (g : G) A ≤ L := fun g => by
    calc B6.conjSub (g : G) A ≤ B6.conjSub (g : G) L :=
          (B6.conjSub (g : G)).monotone (hA.1.trans hP.1)
      _ = L := B6.conjSub_eq_self (Subgroup.le_normalizer g.2)
  have hb₀ := hrel A P hA hVP (hA.1.trans hP.1)
  have hb₁ := hrel A₁ _ (B6.isMaxElemAbelian_conjSub hA g₁) (hconjV g₁) (hconjL g₁)
  have hb₂ := hrel A₂ _ (B6.isMaxElemAbelian_conjSub hA g₂) (hconjV g₂) (hconjL g₂)
  have hbound : (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V < 2 ^ (4 * (2 * a + 1)) := by
    have hWle : W ≤ V ⊓ Subgroup.centralizer (L : Set G) := fun w hw =>
      Subgroup.mem_inf.mpr
        ⟨hw.1.1.1, Subgroup.mem_centralizer_iff.mpr fun l hl => (hWL l hl w hw).symm⟩
    calc (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V ≤ W.relIndex V :=
          Subgroup.relIndex_le_of_le_left hWle (relIndex_ne_zero_of_finite W V)
      _ ≤ ((V ⊓ Subgroup.centralizer (A : Set G)) ⊓
            (V ⊓ Subgroup.centralizer (A₁ : Set G))).relIndex V *
          (V ⊓ Subgroup.centralizer (A₂ : Set G)).relIndex V := Subgroup.relIndex_inf_le
      _ ≤ (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V *
          (V ⊓ Subgroup.centralizer (A₁ : Set G)).relIndex V *
          (V ⊓ Subgroup.centralizer (A₂ : Set G)).relIndex V :=
          Nat.mul_le_mul_right _ Subgroup.relIndex_inf_le
      _ ≤ 2 ^ (2 * a + 1) * 2 ^ (2 * a + 1) * 2 ^ (2 * a + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul hb₀ hb₁) hb₂
      _ < 2 ^ (4 * (2 * a + 1)) := by
          rw [← pow_add, ← pow_add]
          exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hVcomm : ⁅V, V⁆ ≤ (⊥ : Subgroup G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun v hv =>
      Subgroup.mem_centralizer_iff.mpr fun w hw => A4.mul_comm_of_mem_omegaOneCenterOf hw hv).le
  have hsecZ : IsElemSec (V ⊓ Subgroup.centralizer (L : Set G)) V := by
    refine ⟨inf_le_left, hVcomm.trans bot_le, fun v hv => ?_⟩
    rw [A4.sq_eq_one_of_mem_omegaOneCenterOf hv]
    exact one_mem _
  have hLZ : L ≤ Subgroup.normalizer (V : Set G) ⊓
      Subgroup.normalizer ((V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
    refine le_inf hLV (le_normalizer_of_forall_conj_mem fun l hl k hk => ?_)
    have hlk : l * k = k * l := Subgroup.mem_centralizer_iff.mp hk.2 l hl
    rwa [hlk, mul_inv_cancel_right]
  have hQZ : ∀ p ∈ pCoreOf 2 L, ∀ v ∈ V, ⁅p, v⁆ ∈ V ⊓ Subgroup.centralizer (L : Set G) :=
    fun p hp v hv => by
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hEV p hp v hv)]
      exact one_mem _
  have hstep : ∀ l ∈ L, ∀ v ∈ V, ⁅l, v⁆ ∈ V ⊓ Subgroup.centralizer (L : Set G) := by
    by_contra hnt
    push Not at hnt
    exact absurd hbound (not_lt.mpr
      (two_pow_le_relIndex_of_nontrivial_of_sz ha ⟨e⟩ hsecZ hLZ hQZ hnt))
  have hsec0 : IsElemSec (⊥ : Subgroup G) V := by
    refine ⟨bot_le, hVcomm, fun v hv => ?_⟩
    rw [A4.sq_eq_one_of_mem_omegaOneCenterOf hv]
    exact one_mem _
  have hL0 : L ≤ Subgroup.normalizer (V : Set G) ⊓
      Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    refine le_inf hLV (le_normalizer_of_forall_conj_mem fun l _ k hk => ?_)
    rw [Subgroup.mem_bot] at hk ⊢
    rw [hk, mul_one, mul_inv_cancel]
  have hQ0 : ∀ p ∈ pCoreOf 2 L, ∀ v ∈ V, ⁅p, v⁆ ∈ (⊥ : Subgroup G) := fun p hp v hv =>
    Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr (hEV p hp v hv))
  have hquad : ∀ t ∈ P, ∀ v ∈ V, ⁅t, ⁅t, v⁆⁆ ∈ (⊥ : Subgroup G) := fun t ht v hv => by
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.mp (hstep t (hP.1 ht) v hv).2 t (hP.1 ht)
  intro l hl v hv
  exact Subgroup.mem_bot.mp
    (commutator_mem_of_quadratic_of_sz ha ⟨e⟩ hP hsec0 hL0 hQ0 hquad
      l hl v hv)

theorem le_normalizer_centerOf_or_le_normalizer_thompsonJ
    {L P : Subgroup G} {a : ℕ} (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L ≃* Sz a))
    (hC : L ⊓ Subgroup.centralizer (pCoreOf 2 L : Set G) ≤ pCoreOf 2 L)
    (hP : IsSylowTwoOf P L) :
    L ≤ Subgroup.normalizer (centerOf P : Set G) ∨
      L ≤ Subgroup.normalizer (thompsonJ P : Set G) := by
  classical
  by_cases hJ : thompsonJ P ≤ pCoreOf 2 L
  · exact Or.inr (le_normalizer_thompsonJ_of_le_pCoreOf hP hJ)
  left
  have hV := commutator_eq_one_of_not_thompsonJ_le ha hSz hP hJ
  set E := pCoreOf 2 L with hE
  set Z := centerOf E with hZ
  have hEP : E ≤ P := pCoreOf_le_of_isSylowTwoOf hP
  have hLZ : L ≤ Subgroup.normalizer (Z : Set G) :=
    (le_normalizer_pCoreOf 2 L).trans (A4.normalizer_le_normalizer_centerOf E)
  have hZab : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2 x (Subgroup.mem_inf.mp hx).1
  have hZ2 : IsPGroup 2 Z := (pCoreOf_isPGroup 2 L).to_le inf_le_left
  have hodd : ∀ y ∈ L, Odd (orderOf y) → ∀ z ∈ Z, y * z * y⁻¹ = z := fun y hy hyo =>
    CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7.conj_eq_of_odd hZab hZ2
      (fun z hz => (Subgroup.mem_normalizer_iff.mp (hLZ hy) z).mp hz) hyo
      (fun z hz hz2 => by
        have hzV : z ∈ omegaOneCenterOf E := by
          unfold omegaOneCenterOf omegaOneOf
          exact Subgroup.subset_closure ⟨hz, by rw [sq]; exact hz2⟩
        have h := hV y hy z hzV
        rw [commutatorElement_eq_one_iff_mul_comm] at h
        rw [h, mul_inv_cancel_right])
  obtain ⟨e⟩ := hSz
  set N₀ := CFSG.pCore 2 ↥L with hN₀
  let N' : Subgroup ↥L := (Subgroup.centralizer (Z : Set G)).subgroupOf L
  have hmemN' : ∀ y : ↥L, (∀ z ∈ Z, z * (y : G) = y * z) → y ∈ N' := fun y hy =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_centralizer_iff.mpr hy)
  have hN'norm : N'.Normal := by
    refine ⟨fun n hn l => hmemN' _ fun z hz => ?_⟩
    have hn' := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hn)
    have hz' : (l : G)⁻¹ * z * l ∈ Z := by
      have := (Subgroup.mem_normalizer_iff.mp (hLZ (L.inv_mem l.2)) z).mp hz
      simpa using this
    have hc := hn' _ hz'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc z * ((l : G) * n * (l : G)⁻¹)
        = (l : G) * (((l : G)⁻¹ * z * l) * n) * (l : G)⁻¹ := by group
      _ = (l : G) * (n * ((l : G)⁻¹ * z * l)) * (l : G)⁻¹ := by rw [hc]
      _ = (l : G) * n * (l : G)⁻¹ * z := by group
  have hpN' : N₀ ≤ N' := fun y hy => hmemN' y fun z hz =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 y ⟨y, hy, rfl⟩ |>.symm
  have hoddN' : ∀ y : ↥L, Odd (orderOf y) → y ∈ N' := fun y hy => hmemN' y fun z hz => by
    have h := hodd y y.2 (by rwa [Subgroup.orderOf_coe]) z hz
    calc z * (y : G) = (y : G) * z * (y : G)⁻¹ * y := by rw [h]
      _ = (y : G) * z := by group
  have hBt : CFSG.GH74.Uniqueness.Bender.BenderType (oTwoQuot ↥L) (2 * a + 1) 2 1 :=
    CFSG.GH74.Uniqueness.Bender.BenderType.suzuki a ha
      (e.trans (MulEquiv.subgroupCongr (CFSG.GH74.Uniqueness.Bender.szModel_eq_open_sz a).symm))
  haveI hsimple : IsSimpleGroup (oTwoQuot ↥L) := hBt.isSimple
  have hmap : N'.map (QuotientGroup.mk' N₀) = ⊤ := by
    haveI : (N'.map (QuotientGroup.mk' N₀)).Normal :=
      hN'norm.map (QuotientGroup.mk' N₀) (QuotientGroup.mk'_surjective N₀)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N'.map (QuotientGroup.mk' N₀)) with
      hbot | htop
    · exfalso
      have h2 : IsPGroup 2 (oTwoQuot ↥L) := by
        intro xb
        obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N₀ xb
        obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
        refine ⟨k, ?_⟩
        have hyk : Odd (orderOf (y ^ 2 ^ k)) := by
          rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨m, hkm⟩, hkm,
            Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
          exact hm
        have hmem : QuotientGroup.mk' N₀ (y ^ 2 ^ k) ∈ N'.map (QuotientGroup.mk' N₀) :=
          ⟨_, hoddN' _ hyk, rfl⟩
        rw [hbot, Subgroup.mem_bot, map_pow] at hmem
        exact hmem
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
      have hcard := hBt.card_eq
      rw [hn] at hcard
      have hdvd : ((2 ^ (2 * a + 1)) ^ 2 + 1) ∣ 2 ^ n := Dvd.intro _ hcard.symm
      have hodd' : Odd ((2 ^ (2 * a + 1)) ^ 2 + 1) :=
        (Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, by norm_num⟩).add_one
      have h1 := Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hodd')) hdvd
      have : 0 < (2 ^ (2 * a + 1)) ^ 2 := by positivity
      omega
    · exact htop
  have hN'top : N' = ⊤ := by
    have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' N₀) N'
    rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk', sup_eq_left.mpr hpN'] at h1
    exact h1.symm
  have hZP : centerOf P ≤ Z := by
    intro z hz
    have hz' := Subgroup.mem_inf.mp hz
    have hzE : z ∈ Subgroup.centralizer (E : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun h hh => Subgroup.mem_centralizer_iff.mp hz'.2 h (hEP hh)
    exact Subgroup.mem_inf.mpr ⟨hC (Subgroup.mem_inf.mpr ⟨hP.1 hz'.1, hzE⟩), hzE⟩
  refine le_normalizer_of_forall_conj_mem fun l hl z hz => ?_
  have hlN : (⟨l, hl⟩ : ↥L) ∈ N' := hN'top ▸ Subgroup.mem_top _
  have hcomm : z * l = l * z :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hlN) z (hZP hz)
  rw [← hcomm, mul_inv_cancel_right]
  exact hz

end CFSG.Quasithin.Stroth
