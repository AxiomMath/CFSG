module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenResults
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGlue
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGlue2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenFiveTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs15

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def s15SixAdm (D : Data G) (V : Subgroup G) (g : G) : Prop :=
  V ≤ conjSubgroup D.M g ∧ conjSubgroup V g ≤ D.M

theorem s15_Six_adm_inv {D : Data G} {V : Subgroup G} {g : G} (h : s15SixAdm D V g) :
    s15SixAdm D V g⁻¹ := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [mem_conjSubgroup_iff, inv_inv]
    refine h.2 (mem_conjSubgroup_iff.2 ?_)
    have : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [this]
    exact hx
  · have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ V := mem_conjSubgroup_iff.1 hx
    rw [inv_inv] at hx'
    have h1 := mem_conjSubgroup_iff.1 (h.1 hx')
    have : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [this] at h1

theorem s15_Six_adm_mul {D : Data G} {V : Subgroup G} (hN : D.M ≤ normalizer (V : Set G))
    {g x y : G} (h : s15SixAdm D V g) (hx : x ∈ D.M) (hy : y ∈ D.M) :
    s15SixAdm D V (x * g * y) := by
  refine ⟨fun v hv => ?_, fun a ha => ?_⟩
  · rw [mem_conjSubgroup_iff]
    have hyv : y * v * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hN hy) v).1 hv
    have h1 : g * (y * v * y⁻¹) * g⁻¹ ∈ D.M := mem_conjSubgroup_iff.1 (h.1 hyv)
    have h2 : x * (g * (y * v * y⁻¹) * g⁻¹) * x⁻¹ ∈ D.M :=
      D.M.mul_mem (D.M.mul_mem hx h1) (D.M.inv_mem hx)
    have : x * g * y * v * (x * g * y)⁻¹ = x * (g * (y * v * y⁻¹) * g⁻¹) * x⁻¹ := by group
    rw [this]
    exact h2
  · have ha' : x * g * y * a * (x * g * y)⁻¹ ∈ V := mem_conjSubgroup_iff.1 ha
    have h1 : g * (y * a * y⁻¹) * g⁻¹ ∈ V := by
      have h3 := (Subgroup.mem_normalizer_iff.1 (hN (D.M.inv_mem hx))
        (x * g * y * a * (x * g * y)⁻¹)).1 ha'
      have : x⁻¹ * (x * g * y * a * (x * g * y)⁻¹) * x⁻¹⁻¹ = g * (y * a * y⁻¹) * g⁻¹ := by group
      rwa [this] at h3
    have h4 : y * a * y⁻¹ ∈ D.M := h.2 (mem_conjSubgroup_iff.2 h1)
    have h5 : a = y⁻¹ * (y * a * y⁻¹) * y := by group
    rw [h5]
    exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hy) h4) hy

theorem s15_Six_comm_mem_inf {M V : Subgroup G} (hM : M ≤ normalizer (V : Set G)) {g : G}
    (hg : V ≤ conjSubgroup M g) (hA : conjSubgroup V g ≤ M) {w b : G} (hw : w ∈ V)
    (hb : b ∈ conjSubgroup V g) : b * w * b⁻¹ * w⁻¹ ∈ V ⊓ conjSubgroup V g := by
  have hbM : b ∈ M := hA hb
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · have h1 : b * w * b⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hM hbM) w).1 hw
    exact V.mul_mem h1 (V.inv_mem hw)
  · have hwg : g * w * g⁻¹ ∈ M := mem_conjSubgroup_iff.1 (hg hw)
    have hbg : g * b * g⁻¹ ∈ V := mem_conjSubgroup_iff.1 hb
    have h2 : g * (w * b⁻¹ * w⁻¹) * g⁻¹ ∈ V := by
      have : g * (w * b⁻¹ * w⁻¹) * g⁻¹ =
          (g * w * g⁻¹) * (g * b * g⁻¹)⁻¹ * (g * w * g⁻¹)⁻¹ := by group
      rw [this]
      exact (Subgroup.mem_normalizer_iff.1 (hM hwg) ((g * b * g⁻¹)⁻¹)).1 (V.inv_mem hbg)
    have h4 : w * b⁻¹ * w⁻¹ ∈ conjSubgroup V g := mem_conjSubgroup_iff.2 h2
    have : b * w * b⁻¹ * w⁻¹ = b * (w * b⁻¹ * w⁻¹) := by group
    rw [this]
    exact (conjSubgroup V g).mul_mem hb h4

theorem s15_Six_reduce (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    (H : ∀ g' : G, s15SixAdm D V g' →
      ⁅wSub V₀ V hV L, conjSubgroup (wSub V₀ V hV L) g'⁆ = ⊥)
    {g : G} (hg : s15SixAdm D V g) : ⁅V, conjSubgroup V g⁆ = ⊥ := by
  have hN : D.M ≤ normalizer (V : Set G) := h.hyp125.pairFacts.le_normalizer
  have hVeq := iSup_wConj_eq D h1217 h hV hL
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  calc V = ⨆ X ∈ wConj D.M V₀ V hV L, X := hVeq.symm
    _ ≤ centralizer (conjSubgroup V g : Set G) := by
      refine iSup₂_le fun X hX => ?_
      obtain ⟨y, hy, rfl⟩ := hX
      rw [Subgroup.le_centralizer_iff]
      have h1 : conjSubgroup V g ≤ centralizer (conjSubgroup (wSub V₀ V hV L) y : Set G) := by
        rw [← E3.conjSubgroup_le_conjSubgroup_iff g⁻¹, E3.conjSubgroup_conj_inv,
          E3.conjSubgroup_centralizer]
        calc V = ⨆ X ∈ wConj D.M V₀ V hV L, X := hVeq.symm
          _ ≤ _ := by
            refine iSup₂_le fun X' hX' => ?_
            obtain ⟨x, hx, rfl⟩ := hX'
            rw [← E3.conjSubgroup_le_conjSubgroup_iff x⁻¹, E3.conjSubgroup_conj_inv,
              E3.conjSubgroup_centralizer, conjSubgroup_conjSubgroup,
              conjSubgroup_conjSubgroup]
            have hadm : s15SixAdm D V (y * (g⁻¹ * x⁻¹)) := by
              rw [← mul_assoc]
              exact s15_Six_adm_mul hN (s15_Six_adm_inv hg) hy (D.M.inv_mem hx)
            have h2 := H _ hadm
            rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h2
            exact h2
      exact h1

theorem s15_Six_inf_conj_eq_bot (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) {g : G} (hg : g ∉ D.M) :
    (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) ⊓
      conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g = ⊥ := by
  have hWV : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤ V :=
    sup_le (preTil_le V₀ V hV _) (s15_Infra_v1Sub_le h.hyp151.hyp125 hV)
  have h2 : IsPGroup 2 ↥(wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L : Subgroup G) :=
    hV.isPGroup.to_le hWV
  exact inf_conjSubgroup_eq_bot_of_uniqueMax D.maxLocal h2 h2
    (fun w hw hw1 => h.unique₁ w hw hw1) (fun w hw hw1 => h.unique₁ w hw hw1) hg

theorem s15_Six_mem_sup_of_commute {S T : Subgroup G} (h : ∀ x ∈ S, ∀ y ∈ T, x * y = y * x)
    {u : G} (hu : u ∈ S ⊔ T) : ∃ x ∈ S, ∃ y ∈ T, u = x * y := by
  let P : Subgroup G :=
    { carrier := {u | ∃ x ∈ S, ∃ y ∈ T, u = x * y}
      mul_mem' := by
        rintro _ _ ⟨x, hx, y, hy, rfl⟩ ⟨x', hx', y', hy', rfl⟩
        refine ⟨x * x', S.mul_mem hx hx', y * y', T.mul_mem hy hy', ?_⟩
        have : y * x' = x' * y := (h x' hx' y hy).symm
        calc x * y * (x' * y') = x * (y * x') * y' := by group
          _ = x * (x' * y) * y' := by rw [this]
          _ = x * x' * (y * y') := by group
      one_mem' := ⟨1, S.one_mem, 1, T.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨x, hx, y, hy, rfl⟩
        refine ⟨x⁻¹, S.inv_mem hx, y⁻¹, T.inv_mem hy, ?_⟩
        calc (x * y)⁻¹ = (y * x)⁻¹ := by rw [h x hx y hy]
          _ = x⁻¹ * y⁻¹ := by rw [mul_inv_rev] }
  have hST : S ⊔ T ≤ P :=
    sup_le (fun x hx => ⟨x, hx, 1, T.one_mem, by simp⟩) (fun y hy => ⟨1, S.one_mem, y, hy, by simp⟩)
  exact hST hu

@[expose] def s15SixKer (F : Subgroup G) (U : Set G) (Q : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ F ∧ x ∈ normalizer (Q : Set G) ∧ ∀ d ∈ U, x * d * x⁻¹ * d⁻¹ ∈ Q}
  mul_mem' := by
    rintro x y ⟨hxF, hxN, hx⟩ ⟨hyF, hyN, hy⟩
    refine ⟨F.mul_mem hxF hyF, (normalizer (Q : Set G)).mul_mem hxN hyN, fun d hd => ?_⟩
    have h1 : x * (y * d * y⁻¹ * d⁻¹) * x⁻¹ ∈ Q :=
      ((Subgroup.mem_normalizer_iff.1 hxN) _).1 (hy d hd)
    have : x * y * d * (x * y)⁻¹ * d⁻¹ =
        x * (y * d * y⁻¹ * d⁻¹) * x⁻¹ * (x * d * x⁻¹ * d⁻¹) := by group
    rw [this]
    exact Q.mul_mem h1 (hx d hd)
  one_mem' := ⟨F.one_mem, (normalizer (Q : Set G)).one_mem, fun d _ => by simp⟩
  inv_mem' := by
    rintro x ⟨hxF, hxN, hx⟩
    refine ⟨F.inv_mem hxF, (normalizer (Q : Set G)).inv_mem hxN, fun d hd => ?_⟩
    have h1 : x⁻¹ * (x * d * x⁻¹ * d⁻¹)⁻¹ * x⁻¹⁻¹ ∈ Q :=
      ((Subgroup.mem_normalizer_iff.1 ((normalizer (Q : Set G)).inv_mem hxN)) _).1
        (Q.inv_mem (hx d hd))
    have : x⁻¹ * d * x⁻¹⁻¹ * d⁻¹ = x⁻¹ * (x * d * x⁻¹ * d⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [this]
    exact h1

theorem s15_Six_comm_of_normalizers {E F : Subgroup G} (h : E ⊓ F = ⊥) {b w : G}
    (hb : b ∈ F ⊓ normalizer (E : Set G)) (hw : w ∈ E ⊓ normalizer (F : Set G)) :
    b * w * b⁻¹ * w⁻¹ = 1 := by
  obtain ⟨hbF, hbN⟩ := Subgroup.mem_inf.1 hb
  obtain ⟨hwE, hwN⟩ := Subgroup.mem_inf.1 hw
  have h1 : b * w * b⁻¹ * w⁻¹ ∈ E :=
    E.mul_mem (((Subgroup.mem_normalizer_iff.1 hbN) w).1 hwE) (E.inv_mem hwE)
  have h2 : b * w * b⁻¹ * w⁻¹ ∈ F := by
    have h3 : w * b⁻¹ * w⁻¹ ∈ F := ((Subgroup.mem_normalizer_iff.1 hwN) _).1 (F.inv_mem hbF)
    have : b * w * b⁻¹ * w⁻¹ = b * (w * b⁻¹ * w⁻¹) := by group
    rw [this]
    exact F.mul_mem hbF h3
  have h4 : b * w * b⁻¹ * w⁻¹ ∈ E ⊓ F := Subgroup.mem_inf.2 ⟨h1, h2⟩
  rw [h] at h4
  exact Subgroup.mem_bot.1 h4

theorem s15_Six_normalizes_of_comm {E F : Subgroup G} {c : ℕ}
    (h1 : ∀ b ∈ F ⊓ normalizer (E : Set G), ∀ w ∈ E, b * w * b⁻¹ * w⁻¹ = 1)
    (h2 : E3.mQuot F (F ⊓ normalizer (E : Set G)) ≤ 1) (h4 : 1 < c)
    (h3 : ∀ w ∈ E, w ∉ normalizer (F : Set G) →
      c ≤ E3.mQuot F (F ⊓ centralizer ({w} : Set G))) :
    E ≤ normalizer (F : Set G) := by
  intro w hw
  by_contra hwn
  have h5 := h3 w hw hwn
  have hle : F ⊓ normalizer (E : Set G) ≤ F ⊓ centralizer ({w} : Set G) := by
    intro b hb
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hb).1, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h6 : b * w * b⁻¹ = w := mul_inv_eq_one.1 (h1 b hb w hw)
    calc b * w = (b * w * b⁻¹) * b := by group
      _ = w * b := by rw [h6]
  have h7 := E3.mQuot_mono (V := F) hle
  omega

theorem s15_Six_exists_not_mem {W H₁ H₂ : Subgroup G} (h1 : ¬ W ≤ H₁) (h2 : ¬ W ≤ H₂) :
    ∃ w ∈ W, w ∉ H₁ ∧ w ∉ H₂ := by
  obtain ⟨a, haW, haH₁⟩ := SetLike.not_le_iff_exists.1 h1
  obtain ⟨b, hbW, hbH₂⟩ := SetLike.not_le_iff_exists.1 h2
  by_cases ha₂ : a ∈ H₂
  · by_cases hb₁ : b ∈ H₁
    · refine ⟨a * b, W.mul_mem haW hbW, fun hab => haH₁ ?_, fun hab => hbH₂ ?_⟩
      · have := H₁.mul_mem hab (H₁.inv_mem hb₁)
        simpa using this
      · have := H₂.mul_mem (H₂.inv_mem ha₂) hab
        simpa using this
    · exact ⟨b, hbW, hb₁, hbH₂⟩
  · exact ⟨a, haW, haH₁, ha₂⟩

theorem s15_Six_conj_le_normalizer_iff (A X : Subgroup G) (g : G) :
    conjSubgroup A g ≤ normalizer (X : Set G) ↔ A ≤ normalizer (conjSubgroup X g⁻¹ : Set G) := by
  rw [← E3.conjSubgroup_normalizer, ← E3.conjSubgroup_le_conjSubgroup_iff g⁻¹,
    E3.conjSubgroup_conj_inv]

theorem s15_Six_mQuot_sup_le {W Q K : Subgroup G} (hQK : Q ≤ K)
    (hV2 : IsPGroup 2 ↥(W ⊔ Q : Subgroup G)) (hcomm : ∀ x ∈ W, ∀ y ∈ Q, x * y = y * x) :
    E3.mQuot (W ⊔ Q) K ≤ E3.mQuot W K := by
  have hW2 : IsPGroup 2 W := hV2.to_le (le_sup_left : W ≤ W ⊔ Q)
  have hWV : W ≤ W ⊔ Q := le_sup_left
  let ι : ↥W → ↥(W ⊔ Q : Subgroup G) := fun w => ⟨w, hWV w.2⟩
  let f : ↥W ⧸ K.subgroupOf W → ↥(W ⊔ Q : Subgroup G) ⧸ K.subgroupOf (W ⊔ Q) :=
    Quotient.map' ι (fun a b hab => by
      rw [QuotientGroup.leftRel_apply] at hab ⊢
      exact hab)
  have hsurj : Function.Surjective f := by
    intro q
    induction q using QuotientGroup.induction_on with | _ v => ?_
    obtain ⟨x, hx, y, hy, hv⟩ := s15_Six_mem_sup_of_commute hcomm v.2
    refine ⟨QuotientGroup.mk ⟨x, hx⟩, ?_⟩
    show (QuotientGroup.mk (ι ⟨x, hx⟩) : ↥(W ⊔ Q : Subgroup G) ⧸ _) = QuotientGroup.mk v
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have : x⁻¹ * (v : G) = y := by rw [hv]; group
    show x⁻¹ * (v : G) ∈ K
    rw [this]
    exact hQK hy
  have h1 : (K.relIndex (W ⊔ Q)) ≤ K.relIndex W := by
    unfold Subgroup.relIndex
    rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
    exact Nat.card_le_card_of_surjective f hsurj
  rw [E3.relIndex_eq_two_pow hV2, E3.relIndex_eq_two_pow hW2] at h1
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 h1

theorem s15_Six_mQuot_wSub_inf_v1Sub (D : Data G) {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hV : IsElemAbelian 2 V) :
    E3.mQuot (wSub V₀ V hV L) (wSub V₀ V hV L ⊓ v1Sub D.M V₀ V hV L) =
      gamma15 D.M V₀ V hV L := by
  have h1 := mSub_wSub D h hV (L := L)
  have h2 := E3.mQuot_add (V := wSub V₀ V hV L) (U := ⊥)
    (U' := wSub V₀ V hV L ⊓ v1Sub D.M V₀ V hV L) bot_le inf_le_left
  rw [s15_FiveTen_mQuot_bot_eq_rk, s15_FiveTen_mQuot_bot_eq_rk] at h2
  have h3 : mSub (wSub V₀ V hV L) = rk ↥(wSub V₀ V hV L) := rfl
  have h4 : delta15 D.M V₀ V hV L = rk ↥(wSub V₀ V hV L ⊓ v1Sub D.M V₀ V hV L) := by
    rw [inf_comm]
    rfl
  omega

theorem s15_Six_mQuot_conj_wSub_inf_v1Sub (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp125 D V₀ V) (hV : IsElemAbelian 2 V) (g : G) :
    E3.mQuot (conjSubgroup (wSub V₀ V hV L) g)
      (conjSubgroup (wSub V₀ V hV L) g ⊓ conjSubgroup (v1Sub D.M V₀ V hV L) g) =
      gamma15 D.M V₀ V hV L := by
  rw [← E3.conjSubgroup_inf, E3.mQuot_conjSubgroup]
  exact s15_Six_mQuot_wSub_inf_v1Sub D h hV

theorem s15_Six_not_wSub_le_v1Sub (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) :
    ¬ wSub V₀ V hV L ≤ v1Sub D.M V₀ V hV L := by
  intro hle
  have h1 := s15_Six_mQuot_wSub_inf_v1Sub D h.hyp125 hV (L := L)
  rw [inf_eq_left.2 hle, E3.mQuot_self] at h1
  have h2 := two_le_gamma15 D h hV hL
  omega

theorem s15_Six_mQuot_inf_normalizer_le_one (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) {E : Subgroup G} (hE : E ≤ D.M)
    (hE2 : IsPGroup 2 E) (hs : s15 D.M V₀ V hV L ≤ 3) :
    E3.mQuot E (E ⊓ normalizer (wSub V₀ V hV L : Set G)) ≤ 1 := by
  have h1 := s15_Glue_relIndex_inf_normalizer_le D h hV hE
  rw [E3.relIndex_eq_two_pow hE2] at h1
  by_contra hm
  have hm2 : 2 ≤ E3.mQuot E (E ⊓ normalizer (wSub V₀ V hV L : Set G)) := by omega
  have : 2 ^ 2 ≤ 2 ^ E3.mQuot E (E ⊓ normalizer (wSub V₀ V hV L : Set G)) :=
    Nat.pow_le_pow_right (by norm_num) hm2
  omega

theorem s15_Six_mQuot_inf_normalizer_conj_le_one (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) {g : G} {E : Subgroup G}
    (hE : E ≤ conjSubgroup D.M g) (hE2 : IsPGroup 2 E) (hs : s15 D.M V₀ V hV L ≤ 3) :
    E3.mQuot E (E ⊓ normalizer (conjSubgroup (wSub V₀ V hV L) g : Set G)) ≤ 1 := by
  have hE'M : conjSubgroup E g⁻¹ ≤ D.M := by
    have := E3.conjSubgroup_mono_left g⁻¹ hE
    rwa [E3.conjSubgroup_conj_inv] at this
  have hE'2 : IsPGroup 2 (conjSubgroup E g⁻¹) := E3.isPGroup_conjSubgroup hE2 g⁻¹
  have h1 := s15_Six_mQuot_inf_normalizer_le_one D h hV hE'M hE'2 hs
  have h2 : E3.mQuot E (E ⊓ normalizer (conjSubgroup (wSub V₀ V hV L) g : Set G)) =
      E3.mQuot (conjSubgroup E g⁻¹)
        (conjSubgroup E g⁻¹ ⊓ normalizer (wSub V₀ V hV L : Set G)) := by
    rw [← E3.mQuot_conjSubgroup (conjSubgroup E g⁻¹) _ g, E3.conjSubgroup_inf,
      E3.conjSubgroup_inv_conj, E3.conjSubgroup_normalizer]
  rw [h2]
  exact h1

theorem s15_Six_mem_conj_v1Sub_of_commutator_mem (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) {g x w : G} (hx : x ∈ conjSubgroup D.M g)
    (hxn : x ∉ normalizer (conjSubgroup (wSub V₀ V hV L) g : Set G))
    (hw : w ∈ conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g)
    (hxw : x * w * x⁻¹ * w⁻¹ ∈ conjSubgroup (v1Sub D.M V₀ V hV L) g) :
    w ∈ conjSubgroup (v1Sub D.M V₀ V hV L) g := by
  have hx' : g * x * g⁻¹ ∈ D.M := mem_conjSubgroup_iff.1 hx
  have hxn' : g * x * g⁻¹ ∉ nBar D.M V₀ V hV L := by
    intro hmem
    rw [← inf_normalizer_wSub_eq_nBar D h hV] at hmem
    apply hxn
    rw [← E3.conjSubgroup_normalizer]
    exact mem_conjSubgroup_iff.2 (Subgroup.mem_inf.1 hmem).2
  have hw' : g * w * g⁻¹ ∈ wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L := mem_conjSubgroup_iff.1 hw
  have hxw' : (g * x * g⁻¹) * (g * w * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * w * g⁻¹)⁻¹ ∈
      v1Sub D.M V₀ V hV L := by
    have h1 := mem_conjSubgroup_iff.1 hxw
    have e : (g * x * g⁻¹) * (g * w * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * w * g⁻¹)⁻¹ =
        g * (x * w * x⁻¹ * w⁻¹) * g⁻¹ := by group
    rwa [e]
  exact mem_conjSubgroup_iff.2 (mem_v1Sub_of_commutator_mem D h hV hx' hxn' hw' hxw')

theorem s15_Six_le_mQuot_conj (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) {g x : G} (hx : x ∈ conjSubgroup D.M g)
    (hxn : x ∉ normalizer (conjSubgroup (wSub V₀ V hV L) g : Set G)) :
    gamma15 D.M V₀ V hV L ≤ E3.mQuot (conjSubgroup (wSub V₀ V hV L) g)
      (conjSubgroup (wSub V₀ V hV L) g ⊓ centralizer ({x} : Set G)) := by
  have hle : conjSubgroup (wSub V₀ V hV L) g ⊓ centralizer ({x} : Set G) ≤
      conjSubgroup (wSub V₀ V hV L) g ⊓ conjSubgroup (v1Sub D.M V₀ V hV L) g := by
    intro w hw
    obtain ⟨hwB, hwC⟩ := Subgroup.mem_inf.1 hw
    refine Subgroup.mem_inf.2 ⟨hwB, ?_⟩
    have hwD : w ∈ conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g :=
      E3.conjSubgroup_mono_left g le_sup_left hwB
    refine s15_Six_mem_conj_v1Sub_of_commutator_mem D h hV hx hxn hwD ?_
    have hc : w * x = x * w := Subgroup.mem_centralizer_singleton_iff.1 hwC
    have : x * w * x⁻¹ * w⁻¹ = 1 := by rw [← hc]; group
    rw [this]
    exact Subgroup.one_mem _
  have h1 := s15_Six_mQuot_conj_wSub_inf_v1Sub D h.hyp125 hV g (L := L)
  have h2 := E3.mQuot_mono (V := conjSubgroup (wSub V₀ V hV L) g) hle
  omega

theorem s15_Six_comm_eq_one (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) {g : G} {B : Subgroup G}
    (hB : B = conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g) (hg : g ∉ D.M)
    (hs : ¬ (s15 D.M V₀ V hV L = 2 ∧
      delta15 D.M V₀ V hV L < gamma15 D.M V₀ V hV L - 1))
    {a y : G} (ha : a ∈ B) (hy : y ∈ conjSubgroup D.M g)
    (hc : a * y * a⁻¹ * y⁻¹ ∈ wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) :
    a * y * a⁻¹ * y⁻¹ = 1 := by
  by_contra hne1
  have h151 := h.hyp151
  have h125 := h151.hyp125
  have hBV0 : B ⊓ (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) = ⊥ := by
    rw [hB, inf_comm]
    exact s15_Six_inf_conj_eq_bot D h hV hg
  have hym : g * y * g⁻¹ ∈ D.M := mem_conjSubgroup_iff.1 hy
  have haA : g * a * g⁻¹ ∈ wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L := by
    rw [hB] at ha
    exact mem_conjSubgroup_iff.1 ha
  have hyy : g * y * g⁻¹ * (g * a * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹ ∈
      conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) (g * y * g⁻¹)⁻¹ := by
    rw [mem_conjSubgroup_iff]
    have : (g * y * g⁻¹)⁻¹ * (g * y * g⁻¹ * (g * a * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹) *
        ((g * y * g⁻¹)⁻¹)⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ haA
  have hV1m : conjSubgroup (v1Sub D.M V₀ V hV L) (g * y * g⁻¹)⁻¹ = v1Sub D.M V₀ V hV L :=
    conjSubgroup_eq_iff_mem_normalizer.mpr
      (Subgroup.inv_mem _ (s15_Infra_le_normalizer_v1Sub h125 hV hym))
  have hsup : conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) (g * y * g⁻¹)⁻¹ =
      conjSubgroup (wSub V₀ V hV L) (g * y * g⁻¹)⁻¹ ⊔ v1Sub D.M V₀ V hV L := by
    have h1 : conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) (g * y * g⁻¹)⁻¹ =
        conjSubgroup (wSub V₀ V hV L) (g * y * g⁻¹)⁻¹ ⊔
          conjSubgroup (v1Sub D.M V₀ V hV L) (g * y * g⁻¹)⁻¹ := by
      simp only [conjSubgroup]
      exact Subgroup.map_sup _ _ _
    rw [h1, hV1m]
  have hyW : g * y * g⁻¹ * (g * a * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹ ∈
      conjSubgroup (wSub V₀ V hV L) (g * y * g⁻¹)⁻¹ ⊔ v1Sub D.M V₀ V hV L := hsup ▸ hyy
  have hgc : g * (a * y * a⁻¹ * y⁻¹) * g⁻¹ = (g * a * g⁻¹) *
      (g * y * g⁻¹ * (g * a * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹) := by group
  by_cases hWm : conjSubgroup (wSub V₀ V hV L) (g * y * g⁻¹)⁻¹ = wSub V₀ V hV L
  · have hc1 : g * (a * y * a⁻¹ * y⁻¹) * g⁻¹ ∈ wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L := by
      rw [hgc]
      refine Subgroup.mul_mem _ haA ?_
      rwa [hWm] at hyW
    have hcB : a * y * a⁻¹ * y⁻¹ ∈ B := by
      rw [hB]
      exact mem_conjSubgroup_iff.2 hc1
    have h2 : a * y * a⁻¹ * y⁻¹ ∈ B ⊓ (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) :=
      Subgroup.mem_inf.2 ⟨hcB, hc⟩
    rw [hBV0] at h2
    exact hne1 (Subgroup.mem_bot.1 h2)
  · have hginv : g⁻¹ ∉ D.M := by
      intro hginv
      exact hg (by simpa using D.M.inv_mem hginv)
    have hthird := h.third g⁻¹ hginv (wSub V₀ V hV L)
      ⟨1, D.M.one_mem, (conjSubgroup_one _).symm⟩
      (conjSubgroup (wSub V₀ V hV L) (g * y * g⁻¹)⁻¹)
      ⟨(g * y * g⁻¹)⁻¹, D.M.inv_mem hym, rfl⟩ (fun heq => hWm heq.symm) ?_
    · exact hs hthird
    · intro hbot
      have hmem : g * (a * y * a⁻¹ * y⁻¹) * g⁻¹ ∈
          (wSub V₀ V hV L ⊔ conjSubgroup (wSub V₀ V hV L) (g * y * g⁻¹)⁻¹ ⊔
            v1Sub D.M V₀ V hV L) ⊓
            conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g⁻¹ := by
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · rw [hgc]
          refine Subgroup.mul_mem _ ?_ ?_
          · have hle : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤
                wSub V₀ V hV L ⊔ conjSubgroup (wSub V₀ V hV L) (g * y * g⁻¹)⁻¹ ⊔
                  v1Sub D.M V₀ V hV L :=
              sup_le (le_sup_left.trans le_sup_left) le_sup_right
            exact hle haA
          · have hle : conjSubgroup (wSub V₀ V hV L) (g * y * g⁻¹)⁻¹ ⊔
                  v1Sub D.M V₀ V hV L ≤
                wSub V₀ V hV L ⊔ conjSubgroup (wSub V₀ V hV L) (g * y * g⁻¹)⁻¹ ⊔
                  v1Sub D.M V₀ V hV L :=
              sup_le (le_sup_right.trans le_sup_left) le_sup_right
            exact hle hyW
        · rw [mem_conjSubgroup_iff]
          have : g⁻¹ * (g * (a * y * a⁻¹ * y⁻¹) * g⁻¹) * (g⁻¹)⁻¹ = a * y * a⁻¹ * y⁻¹ := by
            group
          rw [this]
          exact hc
      rw [hbot] at hmem
      have h3 := Subgroup.mem_bot.1 hmem
      apply hne1
      have h4 : a * y * a⁻¹ * y⁻¹ = g⁻¹ * (g * (a * y * a⁻¹ * y⁻¹) * g⁻¹) * g := by group
      rw [h4, h3]
      group

@[expose] def s15SixStar (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  ∀ h : G, h ∉ D.M →
    (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) ⊓ conjSubgroup V h = ⊥

theorem s15_Six_delta_lt_of_not_star (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    (hs : s15 D.M V₀ V hV L = 2) (hStar : ¬ s15SixStar D V₀ V L hV) :
    delta15 D.M V₀ V hV L < gamma15 D.M V₀ V hV L - 1 := by
  obtain ⟨h', hh', hne⟩ : ∃ h' : G, h' ∉ D.M ∧
      (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) ⊓ conjSubgroup V h' ≠ ⊥ := by
    by_contra hcon
    exact hStar fun h' hh' => by_contra fun hne => hcon ⟨h', hh', hne⟩
  have hcard := ncard_wConj D h.hyp151 hV
  rw [hs] at hcard
  obtain ⟨X, Y, hXY, hXYeq⟩ := Set.ncard_eq_two.1 hcard
  have hX : X ∈ wConj D.M V₀ V hV L := by rw [hXYeq]; exact Or.inl rfl
  have hY : Y ∈ wConj D.M V₀ V hV L := by rw [hXYeq]; exact Or.inr rfl
  have hVeq : X ⊔ Y ⊔ v1Sub D.M V₀ V hV L = V := by
    have h1 := iSup_wConj_eq D h1217 h.hyp151 hV hL
    rw [hXYeq, iSup_insert, iSup_singleton] at h1
    rw [h1]
    exact sup_eq_left.2 (s15_Infra_v1Sub_le h.hyp151.hyp125 hV)
  have hinv : h'⁻¹ ∉ D.M := fun hm => hh' (by simpa using D.M.inv_mem hm)
  refine (h.third h'⁻¹ hinv X hX Y hY hXY ?_).2
  rw [hVeq]
  intro hbot
  apply hne
  have h2 := congrArg (fun Z => conjSubgroup Z h') hbot
  simp only [E3.conjSubgroup_inf, E3.conjSubgroup_inv_conj, E3.conjSubgroup_bot] at h2
  rw [inf_comm]
  exact h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
