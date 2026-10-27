module

public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaEquality2

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem relIndex_centralizerMod_zpowers_le_of_commutator_mem {Z Q D : Subgroup G} {x : G}
    (hQZ : Q ≤ Subgroup.normalizer (Z : Set G)) (hxZ : x ∈ Subgroup.normalizer (Z : Set G))
    (hD : ∀ v ∈ Q, v * x * v⁻¹ * x⁻¹ ∈ D) :
    (centralizerMod Z Q (Subgroup.zpowers x)).relIndex Q ≤ Z.relIndex D := by
  classical
  set C := centralizerMod Z Q (Subgroup.zpowers x) with hC
  have hconj : ∀ v : G, v ∈ Q → x * v * x⁻¹ ∈ Subgroup.normalizer (Z : Set G) :=
    fun v hv => Subgroup.mul_mem _ (Subgroup.mul_mem _ hxZ (hQZ hv)) (Subgroup.inv_mem _ hxZ)
  let Φ : ↥Q → ↥D := fun v => ⟨(v : G) * x * (v : G)⁻¹ * x⁻¹, hD v v.2⟩
  have hkey : ∀ v w : ↥Q,
      (v⁻¹ * w ∈ C.subgroupOf Q) ↔ ((Φ v)⁻¹ * Φ w ∈ Z.subgroupOf D) := by
    intro v w
    have hu : ((v⁻¹ * w : ↥Q) : G) ∈ Q := (v⁻¹ * w).2
    have hcz : x * (v : G) * x⁻¹ ∈ Subgroup.normalizer (Z : Set G) := hconj v v.2
    have htw : (((Φ v)⁻¹ * Φ w : ↥D) : G) =
        (x * (v : G) * x⁻¹) *
          (((v⁻¹ * w : ↥Q) : G) * x * (((v⁻¹ * w : ↥Q) : G))⁻¹ * x⁻¹) *
          (x * (v : G) * x⁻¹)⁻¹ := by
      show ((v : G) * x * (v : G)⁻¹ * x⁻¹)⁻¹ * ((w : G) * x * (w : G)⁻¹ * x⁻¹) = _
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, htw,
      ← Subgroup.mem_normalizer_iff.mp hcz _]
    exact mem_centralizerMod_zpowers_iff_of_normalizer hQZ hxZ hu
  have hwell : ∀ a b : ↥Q, QuotientGroup.leftRel (C.subgroupOf Q) a b →
      QuotientGroup.leftRel (Z.subgroupOf D) (Φ a) (Φ b) := by
    intro a b hab
    exact QuotientGroup.leftRel_apply.mpr
      ((hkey a b).mp (QuotientGroup.leftRel_apply.mp hab))
  let F : ↥Q ⧸ C.subgroupOf Q → ↥D ⧸ Z.subgroupOf D := Quotient.map' Φ hwell
  have hF : ∀ v : ↥Q, F (QuotientGroup.mk v) = QuotientGroup.mk (Φ v) := fun v => rfl
  have hinj : Function.Injective F := by
    intro a b hab
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective b
    rw [hF, hF, QuotientGroup.eq] at hab
    rw [QuotientGroup.eq]
    exact (hkey v w).mpr hab
  calc C.relIndex Q = Nat.card (↥Q ⧸ C.subgroupOf Q) := rfl
    _ ≤ Nat.card (↥D ⧸ Z.subgroupOf D) := Nat.card_le_card_of_injective F hinj
    _ = Z.relIndex D := rfl

theorem pow_le_relIndex_centralizerMod_between {H U W A : Subgroup G} (hUH : U ≤ H)
    (hAH : A ≤ H) {k : ℕ}
    (hk : ∀ L' N' : Subgroup G, W ≤ L' → IsChiefStep H U L' N' → ¬ IsCentralStep H L' N' →
      k ≤ (centralizerMod L' N' A).relIndex N')
    {N : Subgroup G} {n : ℕ} (h : F112W.IsChiefSeriesBetween H U W N n) :
    k ^ n ≤ (centralizerMod W N A).relIndex N := by
  induction h with
  | refl =>
    rw [pow_zero]
    exact Nat.one_le_iff_ne_zero.mpr (D15Proof.relIndex_ne_zero _ _)
  | @central N L n hstep _ hser ih =>
    have hLN : L ≤ N := hstep.2.2.1.le
    have hCL : centralizerMod W N A ⊓ L = centralizerMod W L A := by
      refine le_antisymm ?_ ?_
      · rintro x ⟨⟨-, hxNW, hx⟩, hxL⟩
        exact ⟨hxL, hxNW, hx⟩
      · intro x hx
        exact ⟨centralizerMod_mono_left A hLN hx, hx.1⟩
    calc k ^ n ≤ (centralizerMod W L A).relIndex L := ih
      _ = (centralizerMod W N A).relIndex L := by rw [← hCL, Subgroup.inf_relIndex_right]
      _ ≤ (centralizerMod W N A).relIndex N :=
          Subgroup.relIndex_le_of_le_right hLN (D15Proof.relIndex_ne_zero _ _)
  | @noncentral N L n hstep hnc hser ih =>
    have hLN : L ≤ N := hstep.2.2.1.le
    have hWL : W ≤ L := hser.le
    have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
    have hCD : centralizerMod W N A ≤ centralizerMod L N A := by
      rintro x ⟨hxN, hxNW, hx⟩
      exact ⟨hxN, (hstep.1.1.trans (hUH.trans hHL)) hxN, fun a ha => hWL (hx a ha)⟩
    have hLD : L ≤ centralizerMod L N A := by
      intro x hxL
      refine ⟨hLN hxL, Subgroup.le_normalizer hxL, fun a ha => ?_⟩
      have h1 : a * x⁻¹ * a⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hHL (hAH ha)) x⁻¹).mp (L.inv_mem hxL)
      have e : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
      rw [e]
      exact L.mul_mem hxL h1
    have hCL : centralizerMod W N A ⊓ L = centralizerMod W L A := by
      refine le_antisymm ?_ ?_
      · rintro x ⟨⟨-, hxNW, hx⟩, hxL⟩
        exact ⟨hxL, hxNW, hx⟩
      · intro x hx
        exact ⟨centralizerMod_mono_left A hLN hx, hx.1⟩
    have hmul : (centralizerMod W N A).relIndex (centralizerMod L N A) *
        (centralizerMod L N A).relIndex N = (centralizerMod W N A).relIndex N :=
      Subgroup.relIndex_mul_relIndex _ _ _ hCD (centralizerMod_le_left L N A)
    have h1 : k ^ n ≤ (centralizerMod W N A).relIndex (centralizerMod L N A) :=
      calc k ^ n ≤ (centralizerMod W L A).relIndex L := ih
        _ = (centralizerMod W N A).relIndex L := by rw [← hCL, Subgroup.inf_relIndex_right]
        _ ≤ (centralizerMod W N A).relIndex (centralizerMod L N A) :=
            Subgroup.relIndex_le_of_le_right hLD (D15Proof.relIndex_ne_zero _ _)
    have h2 : k ≤ (centralizerMod L N A).relIndex N := hk L N hWL hstep hnc
    calc k ^ (n + 1) = k ^ n * k := pow_succ _ _
      _ ≤ (centralizerMod W N A).relIndex (centralizerMod L N A) *
            (centralizerMod L N A).relIndex N := Nat.mul_le_mul h1 h2
      _ = (centralizerMod W N A).relIndex N := hmul

theorem l2_chiefFactor_card_of_quadratic {H Q S X Lo Hi : Subgroup G} {m : ℕ} {x : G}
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥H)) (hQ : IsPGroup 2 Q) (hQH : Q ≤ H)
    (hHQ : H ≤ Subgroup.normalizer (Q : Set G))
    (hstep : IsChiefStep H Q Lo Hi) (hnc : ¬ IsCentralStep H Lo Hi)
    (hSH : S ≤ H) (hSX : S ≤ Subgroup.normalizer (X : Set G)) (hXQ : X ⊔ Q = S)
    (hXX : ⁅X, X⁆ ≤ Lo) (hxX : x ∈ X) (hxsq : x * x ∈ pCoreOf 2 H) (hxO : x ∉ pCoreOf 2 H)
    (hdisp : (centralizerMod Lo Hi (Subgroup.zpowers x)).relIndex Hi ≤ 2 ^ m) :
    Lo.relIndex Hi = (2 ^ m) ^ 2 ∧ Lo.relIndex (centralizerMod Lo Hi S) = 2 ^ m := by
  classical
  have hXleS : X ≤ S := by rw [← hXQ]; exact le_sup_left
  have hQleS : Q ≤ S := by rw [← hXQ]; exact le_sup_right
  have hxS : x ∈ S := hXleS hxX
  have hxH : x ∈ H := hSH hxS
  have hHiQ : Hi ≤ Q := hstep.1.1
  have hLoHi : Lo ≤ Hi := hstep.2.2.1.le
  have hHL : H ≤ Subgroup.normalizer (Lo : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHHi : H ≤ Subgroup.normalizer (Hi : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hsq : (centralizerMod Lo Hi (Subgroup.zpowers x)).relIndex Hi ^ 2 = Lo.relIndex Hi :=
    str86_chiefSection_sq_relIndex hm hL2 hQ hQH hstep hnc hxH hxsq hxO
  have hlow : 2 ^ m ≤ (centralizerMod Lo Hi (Subgroup.zpowers x)).relIndex Hi :=
    l2ChiefSectionRep_pow_le_relIndex_centralizerMod hm hL2 hQ hQH hstep hnc hxH hxsq hxO
  have hCx : (centralizerMod Lo Hi (Subgroup.zpowers x)).relIndex Hi = 2 ^ m :=
    le_antisymm hdisp hlow
  have hfact : Lo.relIndex Hi = (2 ^ m) ^ 2 := by
    rw [← hsq, hCx]
  have hpowpos : 0 < 2 ^ m := by positivity
  have hLCx : Lo ≤ centralizerMod Lo Hi (Subgroup.zpowers x) := by
    intro l hl
    refine ⟨hLoHi hl, Subgroup.le_normalizer hl, fun u hu => ?_⟩
    have huH : u ∈ H := Subgroup.zpowers_le.mpr hxH hu
    have h1 : u * l⁻¹ * u⁻¹ ∈ Lo :=
      (Subgroup.mem_normalizer_iff.mp (hHL huH) l⁻¹).mp (Lo.inv_mem hl)
    have e : l * u * l⁻¹ * u⁻¹ = l * (u * l⁻¹ * u⁻¹) := by group
    rw [e]
    exact Lo.mul_mem hl h1
  have hCSle : centralizerMod Lo Hi S ≤ centralizerMod Lo Hi (Subgroup.zpowers x) :=
    centralizerMod_anti_right Hi (Subgroup.zpowers_le.mpr hxS)
  have hupper : Lo.relIndex (centralizerMod Lo Hi S) ≤ 2 ^ m := by
    have hmul := Subgroup.relIndex_mul_relIndex Lo (centralizerMod Lo Hi (Subgroup.zpowers x)) Hi
      hLCx (centralizerMod_le_left Lo Hi _)
    have hcx : Lo.relIndex (centralizerMod Lo Hi (Subgroup.zpowers x)) = 2 ^ m := by
      rw [hCx, hfact, pow_two] at hmul
      exact Nat.eq_of_mul_eq_mul_right hpowpos (by rw [hmul])
    rw [← hcx]
    exact Subgroup.relIndex_le_of_le_right hCSle (D15Proof.relIndex_ne_zero _ _)
  have hD : ∀ v ∈ Hi, v * x * v⁻¹ * x⁻¹ ∈ centralizerMod Lo Hi S := by
    intro v hv
    have hvQ : v ∈ Q := hHiQ hv
    have hvH : v ∈ H := hQH hvQ
    have hvS : v ∈ S := hQleS hvQ
    set y := v * x * v⁻¹ * x⁻¹ with hydef
    have hyHi : y ∈ Hi := by
      have hxv : x * v⁻¹ * x⁻¹ ∈ Hi :=
        (Subgroup.mem_normalizer_iff.mp (hHHi hxH) v⁻¹).mp (Hi.inv_mem hv)
      rw [hydef]
      have e : v * x * v⁻¹ * x⁻¹ = v * (x * v⁻¹ * x⁻¹) := by group
      rw [e]
      exact Hi.mul_mem hv hxv
    have hyH : y ∈ H := by
      rw [hydef]
      exact H.mul_mem (H.mul_mem (H.mul_mem hvH hxH) (H.inv_mem hvH)) (H.inv_mem hxH)
    have hyX : y ∈ X := by
      have hvx : v * x * v⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp (hSX hvS) x).mp hxX
      rw [hydef]
      have e : v * x * v⁻¹ * x⁻¹ = (v * x * v⁻¹) * x⁻¹ := by group
      rw [e]
      exact X.mul_mem hvx (X.inv_mem hxX)
    refine ⟨hyHi, hHL hyH, fun s hs => ?_⟩
    have hXE : X ≤ centralizerMod Lo (Subgroup.normalizer (Lo : Set G)) (Subgroup.zpowers y) := by
      intro a ha
      refine (mem_centralizerMod_zpowers_iff_of_normalizer (N := Subgroup.normalizer (Lo : Set G))
        (L := Lo) (t := y) (x := a) le_rfl (hHL hyH)
        (hHL (hSH (hXleS ha)))).mpr ?_
      have hcomm : ⁅a, y⁆ ∈ Lo := hXX (Subgroup.commutator_mem_commutator ha hyX)
      rwa [commutatorElement_def] at hcomm
    have hQE : Q ≤ centralizerMod Lo (Subgroup.normalizer (Lo : Set G)) (Subgroup.zpowers y) := by
      intro a ha
      refine (mem_centralizerMod_zpowers_iff_of_normalizer (N := Subgroup.normalizer (Lo : Set G))
        (L := Lo) (t := y) (x := a) le_rfl (hHL hyH) (hHL (hQH ha))).mpr ?_
      have hcomm : ⁅y, a⁆ ∈ Lo :=
        F112W.commutator_le_of_isChiefStep hQ hQH hHQ hstep hHiQ
          (Subgroup.commutator_mem_commutator hyHi ha)
      have e : a * y * a⁻¹ * y⁻¹ = ⁅y, a⁆⁻¹ := by rw [commutatorElement_def]; group
      rw [e]
      exact Lo.inv_mem hcomm
    have hSE : S ≤ centralizerMod Lo (Subgroup.normalizer (Lo : Set G)) (Subgroup.zpowers y) := by
      rw [← hXQ]
      exact sup_le hXE hQE
    have hmem : s * y * s⁻¹ * y⁻¹ ∈ Lo :=
      (mem_centralizerMod_zpowers_iff_of_normalizer (N := Subgroup.normalizer (Lo : Set G))
        (L := Lo) (t := y) (x := s) le_rfl (hHL hyH) (hHL (hSH hs))).mp (hSE hs)
    have e : y * s * y⁻¹ * s⁻¹ = (s * y * s⁻¹ * y⁻¹)⁻¹ := by group
    rw [e]
    exact Lo.inv_mem hmem
  have hlower : 2 ^ m ≤ Lo.relIndex (centralizerMod Lo Hi S) := by
    rw [← hCx]
    exact relIndex_centralizerMod_zpowers_le_of_commutator_mem (Z := Lo) (Q := Hi)
      (D := centralizerMod Lo Hi S) (x := x) (hHiQ.trans (hQH.trans hHL)) (hHL hxH) hD
  exact ⟨hfact, le_antisymm hupper hlower⟩

theorem relIndex_centralizerMod_le_of_section {Z Q Lo Hi A : Subgroup G} (hZLo : Z ≤ Lo)
    (hHiQ : Hi ≤ Q) (hHiLo : Hi ≤ Subgroup.normalizer (Lo : Set G)) :
    (centralizerMod Lo Hi A).relIndex Hi ≤ (centralizerMod Z Q A).relIndex Q := by
  have hle : centralizerMod Z Q A ⊓ Hi ≤ centralizerMod Lo Hi A := by
    rintro y ⟨⟨-, -, hy⟩, hyHi⟩
    exact ⟨hyHi, hHiLo hyHi, fun a ha => hZLo (hy a ha)⟩
  calc (centralizerMod Lo Hi A).relIndex Hi
      ≤ (centralizerMod Z Q A ⊓ Hi).relIndex Hi :=
        Subgroup.relIndex_le_of_le_left hle (D15Proof.relIndex_ne_zero _ _)
    _ = (centralizerMod Z Q A).relIndex Hi := Subgroup.inf_relIndex_right _ _
    _ ≤ (centralizerMod Z Q A).relIndex Q :=
        Subgroup.relIndex_le_of_le_right hHiQ (D15Proof.relIndex_ne_zero _ _)

theorem chiefSeriesBetween_count_le_one_of_displacement {H Q W : Subgroup G} {m c : ℕ} {x : G}
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥H)) (hQ : IsPGroup 2 Q) (hQH : Q ≤ H)
    (hxH : x ∈ H) (hxsq : x * x ∈ pCoreOf 2 H) (hxO : x ∉ pCoreOf 2 H)
    (hdisp : (centralizerMod W Q (Subgroup.zpowers x)).relIndex Q ≤ 2 ^ m)
    (hser : F112W.IsChiefSeriesBetween H Q W Q c) : c ≤ 1 := by
  have hpow : (2 ^ m) ^ c ≤ (centralizerMod W Q (Subgroup.zpowers x)).relIndex Q :=
    pow_le_relIndex_centralizerMod_between hQH (Subgroup.zpowers_le.mpr hxH)
      (fun _ _ _ hstep hnc =>
        l2ChiefSectionRep_pow_le_relIndex_centralizerMod hm hL2 hQ hQH hstep hnc hxH hxsq hxO)
      hser
  have hr : 2 ≤ 2 ^ m :=
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  by_contra hc
  have h2 : (2 ^ m) ^ 2 ≤ 2 ^ m :=
    (Nat.pow_le_pow_right (by omega) (by omega)).trans (hpow.trans hdisp)
  have h3 : 2 * 2 ^ m ≤ 2 ^ m * 2 ^ m := Nat.mul_le_mul_right _ hr
  rw [pow_two] at h2
  omega

end CFSG.Quasithin.Stroth
