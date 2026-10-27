module

public import CFSG.Quasithin.Vol2.Ch4Sec3C135Pi
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.Vol2.Ch4Sec3C135Cnt
public import CFSG.Quasithin.Vol2.Ch4Sec3C135MS

public section

namespace CFSG.Quasithin.H13.Ch4.C135

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.Ch4 Matrix
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F]

omit [Finite G] in
theorem mul_comm_of_isElemAbelian {A : Subgroup G} (hA : IsElemAbelian 2 A) {x y : G}
    (hx : x ∈ A) (hy : y ∈ A) : x * y = y * x := CFSG.Open.IsElemAbelian.comm hA hx hy

theorem card_le_mul_card_inf {K V W : Subgroup G} (hKV : K ≤ V) (hWV : W ≤ V) {N : ℕ}
    (hV : Nat.card V ≤ N * Nat.card K) : Nat.card W ≤ N * Nat.card ↥(K ⊓ W) := by
  have e1 := Subgroup.relIndex_mul_card K V
  have e2 := Subgroup.relIndex_mul_card K W
  rw [inf_eq_left.mpr hKV] at e1
  have hne : K.relIndex V ≠ 0 := by
    intro h
    rw [h, zero_mul] at e1
    exact Nat.card_pos.ne e1
  have h3 : K.relIndex V ≤ N := by
    have h4 : K.relIndex V * Nat.card K ≤ N * Nat.card K := e1 ▸ hV
    exact Nat.le_of_mul_le_mul_right h4 Nat.card_pos
  rw [← e2]
  exact Nat.mul_le_mul_right _ ((Subgroup.relIndex_le_of_le_right hWV hne).trans h3)

namespace QC

variable {X K : Subgroup G}

@[expose] def hom (Qc : QC X K F) : ↥X →* Multiplicative (Fin 3 → F) where
  toFun x := Multiplicative.ofAdd (Qc.κ x)
  map_one' := by rw [Qc.κ_one]; rfl
  map_mul' x y := by rw [Qc.mul]; rfl

omit [Finite G] in
theorem card_eq [Finite F] (Qc : QC X K F) (hKX : K ≤ X) :
    Nat.card X = Nat.card K * Nat.card F ^ 3 := by
  rw [← Subgroup.card_ker_mul_card_range Qc.hom, ← card_fun3']
  congr 1
  · exact Nat.card_congr
      { toFun := fun x => ⟨x.1.1, (Qc.ker x.1).mp
          (congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp x.2))⟩
        invFun := fun k => ⟨⟨k.1, hKX k.2⟩, MonoidHom.mem_ker.mpr (by
          show Multiplicative.ofAdd (Qc.κ ⟨k.1, hKX k.2⟩) = 1
          rw [(Qc.ker _).mpr k.2]
          rfl)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  · have hs : Function.Surjective Qc.hom := fun v => by
      obtain ⟨x, hx⟩ := Qc.surj (Multiplicative.toAdd v)
      exact ⟨x, by show Multiplicative.ofAdd (Qc.κ x) = v; rw [hx]; rfl⟩
    rw [MonoidHom.range_eq_top.mpr hs, Subgroup.card_top]
    exact Nat.card_congr Multiplicative.toAdd

omit [Finite G] in
theorem rep_κ_of_commute (Qc : QC X K F) {A : Subgroup G}
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (a : ↥A) (x : ↥X) (h : (a : G) * x = x * a) :
    Qc.rep hAX hAK a (Qc.κ x) = Qc.κ x := by
  rw [Qc.rep_κ]
  congr 1
  apply Subtype.ext
  show (a : G) * x * (a : G)⁻¹ = x
  rw [h, mul_inv_cancel_right]

end QC

namespace Hyp135

variable {G₀ L : Subgroup G} {α : ↥L →* ↥(StatedSL 3 F)} (H : Hyp135 G₀ L α)

omit [Finite G] in
include H in
theorem card_U [Finite F] : Nat.card (centerOf (c134Q G₀ L)) = Nat.card F ^ 3 := by
  rw [H.qU.card_eq bot_le, Subgroup.card_bot, one_mul]

omit [Finite G] in
theorem mem_centralizer_of_rep {A : Subgroup G} (hAG : A ≤ G₀) {x : ↥A}
    (hx : H.qU.rep (hAG.trans H.le_normalizer_U) (le_normalizer_bot A) x = 1) :
    (x : G) ∈ Subgroup.centralizer (centerOf (c134Q G₀ L) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have h1 := H.qU.rep_κ (hAG.trans H.le_normalizer_U) (le_normalizer_bot A) x ⟨u, hu⟩
  rw [hx, Equiv.Perm.one_apply] at h1
  have h2 := congrArg Subtype.val (H.qU_injective h1)
  rw [coe_cnj] at h2
  calc u * x = x * u * (x : G)⁻¹ * x := by rw [← h2]
    _ = x * u := by group

theorem card_le_range_mul {A : Subgroup G} (hAG : A ≤ G₀)
    (hCU : G₀ ⊓ Subgroup.centralizer (centerOf (c134Q G₀ L) : Set G) ≤ pCoreOf 2 G₀) :
    Nat.card A ≤ Nat.card (H.qU.rep (hAG.trans H.le_normalizer_U) (le_normalizer_bot A)).range *
      Nat.card ↥(A ⊓ pCoreOf 2 G₀) := by
  rw [← Subgroup.card_ker_mul_card_range (H.qU.rep (hAG.trans H.le_normalizer_U)
    (le_normalizer_bot A)), mul_comm]
  refine Nat.mul_le_mul_left _ (Nat.card_le_card_of_injective (fun x => ⟨x.1.1, x.1.2,
    hCU ⟨hAG x.1.2, H.mem_centralizer_of_rep hAG (MonoidHom.mem_ker.mp x.2)⟩⟩) ?_)
  intro x y hxy
  have h := Subtype.ext_iff.mp hxy
  exact Subtype.ext (Subtype.ext h)

omit [Finite G] in
theorem range_ne_bot {A : Subgroup G} (hAG : A ≤ G₀)
    (hCU : G₀ ⊓ Subgroup.centralizer (centerOf (c134Q G₀ L) : Set G) ≤ pCoreOf 2 G₀)
    (hAT : ¬ A ≤ pCoreOf 2 G₀) :
    (H.qU.rep (hAG.trans H.le_normalizer_U) (le_normalizer_bot A)).range ≠ ⊥ := by
  intro h
  apply hAT
  intro a ha
  have h1 : H.qU.rep (hAG.trans H.le_normalizer_U) (le_normalizer_bot A) ⟨a, ha⟩ = 1 := by
    rw [← Subgroup.mem_bot, ← h]
    exact ⟨⟨a, ha⟩, rfl⟩
  exact hCU ⟨hAG ha, H.mem_centralizer_of_rep hAG h1⟩

omit [Finite G] in
theorem card_inf_U_le [Finite F] {A : Subgroup G} (hAG : A ≤ G₀) (hA : IsElemAbelian 2 A) :
    Nat.card ↥(A ⊓ centerOf (c134Q G₀ L)) ≤
      Nat.card (fixAll (H.qU.rep (hAG.trans H.le_normalizer_U) (le_normalizer_bot A))) := by
  refine Nat.card_le_card_of_injective (fun x => ⟨H.qU.κ ⟨x, x.2.2⟩, fun a =>
    H.qU.rep_κ_of_commute _ _ a _ (mul_comm_of_isElemAbelian hA a.2 x.2.1)⟩) ?_
  intro x y hxy
  have h := Subtype.ext_iff.mp hxy
  have h' := Subtype.ext_iff.mp (H.qU_injective h)
  exact Subtype.ext h'

end Hyp135

namespace Hyp135.Adapted

variable {G₀ L : Subgroup G} {α : ↥L →* ↥(StatedSL 3 F)} {H : Hyp135 G₀ L α} (C : H.Adapted)

omit [Finite G] in
theorem card_W [Finite F] : Nat.card C.W = Nat.card F ^ 6 := by
  rw [C.qW.card_eq (C.centerOf_le_Wμ _), H.card_U]
  ring

theorem card_inf_W_le [Finite F] [CharP F 2] (hTQ : ¬ pCoreOf 2 G₀ ≤ c134Q G₀ L)
    {A : Subgroup G} (hAG : A ≤ G₀) (hA : IsElemAbelian 2 A) :
    Nat.card ↥(A ⊓ C.W) ≤
      Nat.card (fixAll (H.qU.rep (hAG.trans H.le_normalizer_U) (le_normalizer_bot A))) *
        Nat.card (fixAll (C.qW.rep (hAG.trans (C.le_normalizer_W_of_ne hTQ))
          (hAG.trans H.le_normalizer_U))) := by
  have hle : A ⊓ C.W ≤ C.W := inf_le_right
  rw [← Subgroup.card_ker_mul_card_range (C.qW.hom.comp (Subgroup.inclusion hle))]
  refine Nat.mul_le_mul ((Nat.card_le_card_of_injective (fun x =>
    (⟨x.1.1, x.1.2.1, (C.qW.ker (Subgroup.inclusion hle x.1)).mp
      (congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp x.2))⟩ :
        ↥(A ⊓ centerOf (c134Q G₀ L)))) ?_).trans (H.card_inf_U_le hAG hA)) ?_
  · intro x y h
    have h' := Subtype.ext_iff.mp h
    exact Subtype.ext (Subtype.ext h')
  · refine Nat.card_le_card_of_injective (fun y => ⟨Multiplicative.toAdd y.1, ?_⟩) ?_
    · obtain ⟨x, hx⟩ := y.2
      intro a
      rw [← hx]
      exact C.qW.rep_κ_of_commute _ _ a (Subgroup.inclusion hle x)
        (mul_comm_of_isElemAbelian hA a.2 x.2.1)
    · intro x y h
      have h' := Subtype.ext_iff.mp h
      exact Subtype.ext (Multiplicative.toAdd.injective h')

variable [CharP F 2]

theorem isElemAbelian_V : IsElemAbelian 2 C.V :=
  ⟨⟨⟨fun x y => Subtype.ext (C.V_comm x.2 y.2)⟩⟩, fun _ hx => C.V_sq hx⟩

theorem two_mul_card_W_le (hTQ : ¬ pCoreOf 2 G₀ ≤ c134Q G₀ L) :
    2 * Nat.card C.W ≤ Nat.card C.V := by
  obtain ⟨t, ht, htQ⟩ : ∃ t ∈ pCoreOf 2 G₀, t ∉ c134Q G₀ L := by
    by_contra h
    push Not at h
    exact hTQ h
  obtain ⟨q₀, hq₀⟩ := C.exists_mul_mem_V ht
  have hVW : ¬ C.V ≤ C.W := fun h => htQ (by
    have := (c134Q G₀ L).mul_mem (C.W_le_Q (h hq₀)) q₀.2
    simpa using this)
  have e := Subgroup.relIndex_mul_card C.W C.V
  rw [inf_eq_left.mpr C.W_le_V] at e
  have h1 : C.W.relIndex C.V ≠ 1 := fun h => hVW (Subgroup.relIndex_eq_one.mp h)
  have h0 : C.W.relIndex C.V ≠ 0 := by
    intro h
    rw [h, zero_mul] at e
    exact Nat.card_pos.ne e
  rw [← e]
  exact Nat.mul_le_mul_right _ (by omega)

theorem πf_congr {t t' : G} (ht : t ∈ pCoreOf 2 G₀) (ht' : t' ∈ pCoreOf 2 G₀) (h : t = t') :
    C.πf ht = C.πf ht' := by
  subst h
  rfl

theorem card_inf_T_le [Finite F] {A : Subgroup G} (P : (Fin 3 → F) → Prop)
    (hP : ∀ t (ht : t ∈ pCoreOf 2 G₀), t ∈ A → P (C.πf ht)) :
    Nat.card ↥(A ⊓ pCoreOf 2 G₀) ≤ Nat.card ↥(A ⊓ C.V) * Nat.card {v // P v} := by
  let π : ↥(A ⊓ pCoreOf 2 G₀) →* Multiplicative (Fin 3 → F) :=
    { toFun := fun t => Multiplicative.ofAdd (C.πf t.2.2)
      map_one' := by
        show Multiplicative.ofAdd (C.πf (pCoreOf 2 G₀).one_mem) = 1
        rw [C.πf_of_mem_V _ C.V.one_mem]
        rfl
      map_mul' := fun t t' => by
        show Multiplicative.ofAdd (C.πf ((pCoreOf 2 G₀).mul_mem t.2.2 t'.2.2)) = _
        rw [C.πf_mul]
        rfl }
  rw [← Subgroup.card_ker_mul_card_range π]
  refine Nat.mul_le_mul (Nat.card_le_card_of_injective (fun t => ⟨t.1.1, t.1.2.1,
    C.mem_V_of_πf t.1.2.2 (congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp t.2))⟩) ?_)
    (Nat.card_le_card_of_injective (fun y => ⟨Multiplicative.toAdd y.1, ?_⟩) ?_)
  · intro x y h
    have h' := Subtype.ext_iff.mp h
    exact Subtype.ext (Subtype.ext h')
  · obtain ⟨t, ht⟩ := y.2
    rw [← ht]
    exact hP t t.2.2 t.2.1
  · intro x y h
    have h' := Subtype.ext_iff.mp h
    exact Subtype.ext (Multiplicative.toAdd.injective h')

theorem πf_fixed (hTQ : ¬ pCoreOf 2 G₀ ≤ c134Q G₀ L) {A : Subgroup G} (hAG : A ≤ G₀)
    (hA : IsElemAbelian 2 A) {t : G} (ht : t ∈ pCoreOf 2 G₀) (htA : t ∈ A) (a : ↥A) :
    C.q2.rep (hAG.trans H.le_normalizer_Q) (hAG.trans (C.le_normalizer_W_of_ne hTQ)) a
      (C.πf ht) = C.πf ht := by
  have hat : (a : G) * t * (a : G)⁻¹ = t := by
    rw [mul_comm_of_isElemAbelian hA a.2 htA, mul_inv_cancel_right]
  have hmem : (a : G) * t * (a : G)⁻¹ ∈ pCoreOf 2 G₀ := by rw [hat]; exact ht
  have h1 := C.πf_conj (hAG a.2) (C.le_normalizer_V_of_ne hTQ (hAG a.2)) ht hmem
  calc C.q2.rep (hAG.trans H.le_normalizer_Q) (hAG.trans (C.le_normalizer_W_of_ne hTQ)) a
        (C.q2.κ (C.qPart ht)) = C.q2.κ (cnj (H.le_normalizer_Q (hAG a.2)) (C.qPart ht)) :=
          QC.rep_κ _ _ _ a _
    _ = C.πf hmem := h1.symm
    _ = C.πf ht := C.πf_congr hmem ht hat

theorem πf_mem_span {A : Subgroup G} (hA : IsElemAbelian 2 A) {w : G} (hwA : w ∈ A)
    (hwW : w ∈ C.W) (hwU : w ∉ centerOf (c134Q G₀ L)) {t : G} (ht : t ∈ pCoreOf 2 G₀)
    (htA : t ∈ A) : ∃ c : F, C.πf ht = c • C.eW ⟨w, hwW⟩ := by
  set q := C.qPart ht with hq
  have hv := C.qPart_spec ht
  have htw : t * w = w * t := mul_comm_of_isElemAbelian hA htA hwA
  have hvw : t * (q : G)⁻¹ * w = w * (t * (q : G)⁻¹) :=
    (Subgroup.mem_centralizer_iff.mp hv.2 w hwW).symm
  have h1 : (q : G)⁻¹ * w = w * (q : G)⁻¹ := by
    calc (q : G)⁻¹ * w = t⁻¹ * (t * (q : G)⁻¹ * w) := by group
      _ = t⁻¹ * (w * t) * (q : G)⁻¹ := by rw [hvw]; group
      _ = w * (q : G)⁻¹ := by rw [← htw]; group
  have hqw : (q : G) * w = w * q := by
    calc (q : G) * w = q * (w * (q : G)⁻¹) * q := by group
      _ = w * q := by rw [← h1]; group
  have hw1 : C.e (C.wQ ⟨w, hwW⟩) 1 = 0 := (C.mem_W_iff _).mp hwW
  have hw0 : C.e (C.wQ ⟨w, hwW⟩) 0 ≠ 0 := by
    intro h0
    apply hwU
    have h2 : C.e (C.wQ ⟨w, hwW⟩) = 0 := by
      funext i
      fin_cases i
      · exact h0
      · exact hw1
    exact (C.ker _).mp h2
  exact C.mem_span_of_commute hw1 hw0 (q := q) hqw

omit [Finite G] [CharP F 2] in
theorem card_span_le [Finite F] (y : Fin 3 → F) :
    Nat.card {v : Fin 3 → F // ∃ c : F, v = c • y} ≤ Nat.card F :=
  Nat.card_le_card_of_surjective (fun c => ⟨c • y, c, rfl⟩) fun v => by
    obtain ⟨c, hc⟩ := v.2
    exact ⟨c, Subtype.ext hc.symm⟩

include C in
theorem false_of_ne [Finite F] (hq : 2 ≤ Nat.card F) {R₀ : Subgroup G} (hMS : IsMSPair G₀ R₀)
    (hG₀ : (G₀ : Set G) = (L : Set G) * (R₀ : Set G)) (hTQ : ¬ pCoreOf 2 G₀ ≤ c134Q G₀ L) :
    False := by
  obtain ⟨hRG, hTR, -⟩ := msPair_facts hMS
  have hCU := H.centralizer_U_le hMS hG₀
  obtain ⟨A, hAmax, hAT⟩ := H.exists_maxElemAbelian_not_le hMS
  have hAG : A ≤ G₀ := hAmax.1.trans hRG
  have hA : IsElemAbelian 2 A := hAmax.2.1
  obtain ⟨h1, h2⟩ := C.offender hTQ hAG hA (H.range_ne_bot hAG hCU hAT)
  have hVA : Nat.card C.V ≤ Nat.card A := hAmax.2.2 _ (inf_le_left.trans hTR) C.isElemAbelian_V
  have hWV := C.two_mul_card_W_le hTQ
  have hAB := H.card_le_range_mul hAG hCU
  have hAU := H.card_inf_U_le hAG hA
  have hAW := C.card_inf_W_le hTQ hAG hA
  have hW := C.card_W
  by_cases hI : ∃ v ∈ A ⊓ C.V, v ∉ C.W
  · obtain ⟨v, hv, hvW⟩ := hI
    have hBV : A ⊓ pCoreOf 2 G₀ ≤ C.V := fun b hb =>
      C.mem_V_of_commute hv.2 hvW hb.2 (mul_comm_of_isElemAbelian hA hb.1 hv.1)
    have hle := card_le_mul_card_inf hBV C.W_le_V (hVA.trans hAB)
    have hle2 : Nat.card ↥(A ⊓ pCoreOf 2 G₀ ⊓ C.W) ≤ Nat.card ↥(A ⊓ C.W) :=
      Subgroup.card_le_of_le (inf_le_inf_right _ inf_le_left)
    have h3 : Nat.card F ^ 6 * Nat.card F < Nat.card F ^ 6 * 2 := by
      calc Nat.card F ^ 6 * Nat.card F
          ≤ Nat.card (H.qU.rep (hAG.trans H.le_normalizer_U) (le_normalizer_bot A)).range *
            (Nat.card (fixAll (H.qU.rep (hAG.trans H.le_normalizer_U) (le_normalizer_bot A))) *
              Nat.card (fixAll (C.qW.rep (hAG.trans (C.le_normalizer_W_of_ne hTQ))
                (hAG.trans H.le_normalizer_U)))) * Nat.card F := by
            rw [← hW]
            exact Nat.mul_le_mul_right _ (hle.trans (Nat.mul_le_mul_left _ (hle2.trans hAW)))
        _ = _ := by ring
        _ < 2 * Nat.card F ^ 6 := h1
        _ = Nat.card F ^ 6 * 2 := by ring
    have := Nat.lt_of_mul_lt_mul_left h3
    omega
  · push Not at hI
    have hVW : A ⊓ C.V ≤ A ⊓ C.W := fun v hv => ⟨hv.1, hI v hv⟩
    by_cases hII : ∃ w ∈ A ⊓ C.W, w ∉ centerOf (c134Q G₀ L)
    · obtain ⟨w, hw, hwU⟩ := hII
      have hB := C.card_inf_T_le (A := A) (fun v => ∃ c : F, v = c • C.eW ⟨w, hw.2⟩)
        fun t ht htA => C.πf_mem_span hA hw.1 hw.2 hwU ht htA
      have hS := card_span_le (C.eW ⟨w, hw.2⟩)
      have : Nat.card A < Nat.card A := by
        calc Nat.card A
            ≤ Nat.card (H.qU.rep (hAG.trans H.le_normalizer_U) (le_normalizer_bot A)).range *
              Nat.card ↥(A ⊓ pCoreOf 2 G₀) := hAB
          _ ≤ Nat.card (H.qU.rep (hAG.trans H.le_normalizer_U) (le_normalizer_bot A)).range *
              ((Nat.card (fixAll (H.qU.rep (hAG.trans H.le_normalizer_U)
                (le_normalizer_bot A))) *
                Nat.card (fixAll (C.qW.rep (hAG.trans (C.le_normalizer_W_of_ne hTQ))
                  (hAG.trans H.le_normalizer_U)))) * Nat.card F) :=
            Nat.mul_le_mul_left _ (hB.trans (Nat.mul_le_mul
              ((Subgroup.card_le_of_le hVW).trans hAW) hS))
          _ = _ := by ring
          _ < 2 * Nat.card F ^ 6 := h1
          _ = 2 * Nat.card C.W := by rw [hW]
          _ ≤ Nat.card A := hWV.trans hVA
      exact lt_irrefl _ this
    · push Not at hII
      have hWU : A ⊓ C.V ≤ A ⊓ centerOf (c134Q G₀ L) := fun v hv => ⟨hv.1, hII v (hVW hv)⟩
      have hB := C.card_inf_T_le (A := A) (fun v => ∀ a,
        C.q2.rep (hAG.trans H.le_normalizer_Q) (hAG.trans (C.le_normalizer_W_of_ne hTQ)) a v = v)
        fun t ht htA => C.πf_fixed hTQ hAG hA ht htA
      have : Nat.card A < Nat.card A := by
        calc Nat.card A
            ≤ Nat.card (H.qU.rep (hAG.trans H.le_normalizer_U) (le_normalizer_bot A)).range *
              Nat.card ↥(A ⊓ pCoreOf 2 G₀) := hAB
          _ ≤ Nat.card (H.qU.rep (hAG.trans H.le_normalizer_U) (le_normalizer_bot A)).range *
              (Nat.card (fixAll (H.qU.rep (hAG.trans H.le_normalizer_U)
                (le_normalizer_bot A))) *
                Nat.card (fixAll (C.q2.rep (hAG.trans H.le_normalizer_Q)
                  (hAG.trans (C.le_normalizer_W_of_ne hTQ))))) :=
            Nat.mul_le_mul_left _ (hB.trans (Nat.mul_le_mul_right _
              ((Subgroup.card_le_of_le hWU).trans hAU)))
          _ = _ := by ring
          _ < 2 * Nat.card F ^ 6 := h2
          _ = 2 * Nat.card C.W := by rw [hW]
          _ ≤ Nat.card A := hWV.trans hVA
      exact lt_irrefl _ this

end Hyp135.Adapted

end CFSG.Quasithin.H13.Ch4.C135

end
