module

public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepairCent

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix
open CFSG.SectionRank.OddCover (diagHom coe_diagHom)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

namespace SURepair

section Linear

variable {K : Type} [Field K] {f n : ℕ}

theorem vecMul_bar_of_mulVec_eq (h : UnitaryFieldData 2 f K) {w : Matrix (Fin n) (Fin n) K}
    (hw : (w.map h.bar)ᵀ * w = 1) {r : Fin n → K} (hr : w *ᵥ r = r) :
    vecMul (h.bar ∘ r) w = h.bar ∘ r := by
  have h1 : (w.map h.bar) *ᵥ (h.bar ∘ r) = h.bar ∘ r := by
    funext i
    have e := RingHom.map_mulVec h.bar w r i
    rw [hr] at e
    exact e.symm
  calc vecMul (h.bar ∘ r) w = vecMul ((w.map h.bar) *ᵥ (h.bar ∘ r)) w := by rw [h1]
    _ = vecMul (vecMul (h.bar ∘ r) (w.map h.bar)ᵀ) w := by rw [vecMul_transpose]
    _ = vecMul (h.bar ∘ r) ((w.map h.bar)ᵀ * w) := vecMul_vecMul _ _ _
    _ = h.bar ∘ r := by rw [hw, vecMul_one]

theorem mulVec_conj_sub (D w : GL (Fin n) K) (u : Fin n → K) :
    (D : Matrix (Fin n) (Fin n) K) *ᵥ ((w : Matrix (Fin n) (Fin n) K) *ᵥ u - u) =
      ((D * w * D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        ((D : Matrix (Fin n) (Fin n) K) *ᵥ u) - (D : Matrix (Fin n) (Fin n) K) *ᵥ u := by
  rw [mulVec_sub, mulVec_mulVec, mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
    show D * w * D⁻¹ * D = D * w by group]

noncomputable abbrev vSupp (v : Fin n → K) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => v i ≠ 0

theorem mem_vSupp {v : Fin n → K} {i : Fin n} : i ∈ vSupp v ↔ v i ≠ 0 := by
  classical
  unfold vSupp
  simp

theorem exists_pair_of_isPGroup_two (h : UnitaryFieldData 2 f K) {W : Subgroup (GL (Fin n) K)}
    (hW2 : IsPGroup 2 W) (hW1 : W ≠ ⊥)
    (hWu : ∀ w ∈ W, (((w : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
      ((w : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1)
    {S : Set (Fin n → Kˣ)}
    (hSW : ∀ d ∈ S, ∀ w ∈ W, diagHom n d * w * (diagHom n d)⁻¹ ∈ W ∧
      (diagHom n d)⁻¹ * w * diagHom n d ∈ W) :
    ∃ s t : Fin n, s ≠ t ∧ ∀ d ∈ S, d s = d t := by
  classical
  have : Finite K := h.finite
  have : CharP K 2 := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X : Submodule K (Fin n → K) := Submodule.span K
    {v | ∃ w ∈ W, ∃ u : Fin n → K, v = ((w : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u - u}
    with hX
  have hgen : ∀ w ∈ W, ∀ u : Fin n → K,
      ((w : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u - u ∈ X :=
    fun w hw u => Submodule.subset_span ⟨w, hw, u, rfl⟩
  have hWX : ∀ w ∈ W, ∀ x ∈ X, ((w : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ X := by
    intro w hw x hx
    induction hx using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨w', hw', u, rfl⟩ := hv
      have e : ((w : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
          (((w' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u - u) =
          (((w * w' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u - u) -
            (((w : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u - u) := by
        rw [Units.val_mul, ← mulVec_mulVec, mulVec_sub]
        abel
      rw [e]
      exact X.sub_mem (hgen _ (W.mul_mem hw hw') u) (hgen w hw u)
    | zero => rw [mulVec_zero]; exact X.zero_mem
    | add x y _ _ hx hy => rw [mulVec_add]; exact X.add_mem hx hy
    | smul c x _ hx => rw [mulVec_smul]; exact X.smul_mem c hx
  let _ : MulAction ↥W ↥X :=
    { smul := fun w x => ⟨((w : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (x : Fin n → K),
        hWX w w.2 x x.2⟩
      one_smul := fun x => Subtype.ext (by
        change (((1 : W) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (x : Fin n → K) = x
        rw [Subgroup.coe_one, Units.val_one, one_mulVec])
      mul_smul := fun w w' x => Subtype.ext (by
        change (((w * w' : W) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (x : Fin n → K) =
          ((w : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
            (((w' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (x : Fin n → K))
        rw [Subgroup.coe_mul, Units.val_mul, mulVec_mulVec]) }
  obtain ⟨⟨w₀, hw₀⟩, hw₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hW1
  have hw₀1' : w₀ ≠ 1 := fun h' => hw₀1 (Subtype.ext h')
  obtain ⟨u₀, hu₀⟩ : ∃ u : Fin n → K,
      ((w₀ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u ≠ u := by
    by_contra hall
    push Not at hall
    apply hw₀1'
    apply Units.ext
    rw [Units.val_one]
    exact ext_of_mulVec_single fun i => by rw [hall, one_mulVec]
  have hx₀ : (⟨_, hgen w₀ hw₀ u₀⟩ : ↥X) ≠ 0 := fun h' => hu₀ (sub_eq_zero.mp (congrArg Subtype.val h'))
  have hdvd : 2 ∣ Nat.card ↥X := by
    have h2 : (2 : ℕ) • (⟨_, hgen w₀ hw₀ u₀⟩ : ↥X) = 0 := by
      apply Subtype.ext
      funext i
      change (2 : ℕ) • ((((w₀ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u₀ - u₀) i) = 0
      rw [two_nsmul, CharTwo.add_self_eq_zero]
    rw [← addOrderOf_eq_prime h2 hx₀]
    exact addOrderOf_dvd_natCard _
  have h0 : (0 : ↥X) ∈ MulAction.fixedPoints ↥W ↥X := fun w => Subtype.ext (by
    change ((w : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (0 : Fin n → K) = 0
    rw [mulVec_zero])
  obtain ⟨r, hrfix, hr0⟩ := hW2.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥X hdvd h0
  let R : Submodule K (Fin n → K) :=
    { carrier := {v | v ∈ X ∧ ∀ w ∈ W, ((w : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = v}
      add_mem' := fun {a b} ha hb => ⟨X.add_mem ha.1 hb.1, fun w hw => by
        rw [mulVec_add, ha.2 w hw, hb.2 w hw]⟩
      zero_mem' := ⟨X.zero_mem, fun w _ => mulVec_zero _⟩
      smul_mem' := fun c v hv => ⟨X.smul_mem c hv.1, fun w hw => by
        rw [mulVec_smul, hv.2 w hw]⟩ }
  have hrR : (r : Fin n → K) ∈ R :=
    ⟨r.2, fun w hw => congrArg Subtype.val (hrfix ⟨w, hw⟩)⟩
  have hr0' : (r : Fin n → K) ≠ 0 := fun h' => hr0 (Subtype.ext h'.symm)
  have hDX : ∀ d ∈ S, ∀ x ∈ X, ((diagHom n d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ X := by
    intro d hd x hx
    induction hx using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨w, hw, u, rfl⟩ := hv
      rw [mulVec_conj_sub]
      exact hgen _ (hSW d hd w hw).1 _
    | zero => rw [mulVec_zero]; exact X.zero_mem
    | add x y _ _ hx hy => rw [mulVec_add]; exact X.add_mem hx hy
    | smul c x _ hx => rw [mulVec_smul]; exact X.smul_mem c hx
  have hDR : ∀ d ∈ S, ∀ v ∈ R, ((diagHom n d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ R := by
    intro d hd v hv
    refine ⟨hDX d hd v hv.1, fun w hw => ?_⟩
    have h1 := hv.2 _ (hSW d hd w hw).2
    rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec] at h1
    calc ((w : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
          (((diagHom n d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) =
        ((diagHom n d * ((diagHom n d)⁻¹ * w * diagHom n d) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) *ᵥ v := by
          rw [show diagHom n d * ((diagHom n d)⁻¹ * w * diagHom n d) = w * diagHom n d by group,
            Units.val_mul, mulVec_mulVec]
      _ = ((diagHom n d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v := by
          rw [Units.val_mul, ← mulVec_mulVec, Units.val_mul, Units.val_mul, ← mulVec_mulVec,
            ← mulVec_mulVec, h1]
  have hiso : ∀ v ∈ R, ∀ x ∈ X, (h.bar ∘ v) ⬝ᵥ x = 0 := by
    intro v hv x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hw, u, rfl⟩ := hy
      rw [dotProduct_sub, dotProduct_mulVec,
        vecMul_bar_of_mulVec_eq h (hWu w hw) (hv.2 w hw), sub_self]
    | zero => exact dotProduct_zero _
    | add x y _ _ hx hy => rw [dotProduct_add, hx, hy, add_zero]
    | smul c x _ hx => rw [dotProduct_smul, hx, smul_zero]
  obtain ⟨v, ⟨hvR, hv0⟩, hmin⟩ := WellFounded.has_min
    (InvImage.wf (fun v : Fin n → K => (vSupp v).card) wellFounded_lt)
    {v | v ∈ R ∧ v ≠ 0} ⟨_, hrR, hr0'⟩
  have heig : ∀ d ∈ S, ∀ i j, v i ≠ 0 → v j ≠ 0 → d i = d j := by
    intro d hd i j hi hj
    set v' := ((diagHom n d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v - ((d i : Kˣ) : K) • v
      with hv'
    have hv'R : v' ∈ R := R.sub_mem (hDR d hd v hvR) (R.smul_mem _ hvR)
    have hv'k : ∀ k, v' k = (((d k : Kˣ) : K) - (d i : K)) * v k := by
      intro k
      rw [hv', Pi.sub_apply, coe_diagHom, mulVec_diagonal, Pi.smul_apply, smul_eq_mul, sub_mul]
    have hsub : vSupp v' ⊆ (vSupp v).erase i := by
      intro k hk
      rw [mem_vSupp, hv'k] at hk
      refine Finset.mem_erase.mpr ⟨fun hki => ?_, mem_vSupp.mpr fun h0 => hk (by rw [h0, mul_zero])⟩
      rw [hki, sub_self, zero_mul] at hk
      exact hk rfl
    have hlt : (vSupp v').card < (vSupp v).card :=
      (Finset.card_le_card hsub).trans_lt (Finset.card_erase_lt_of_mem (mem_vSupp.mpr hi))
    have hv'0 : v' = 0 := by
      by_contra hne
      exact hmin v' ⟨hv'R, hne⟩ hlt
    have hj' := hv'k j
    rw [hv'0, Pi.zero_apply] at hj'
    have h1 := (mul_eq_zero.mp hj'.symm).resolve_right hj
    exact (Units.ext (sub_eq_zero.mp h1)).symm
  obtain ⟨s, hs⟩ : ∃ s, v s ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hv0 (funext hall)
  obtain ⟨t, hts, ht⟩ : ∃ t, t ≠ s ∧ v t ≠ 0 := by
    by_contra hall
    push Not at hall
    have hvv := hiso v hvR v hvR.1
    rw [dotProduct, Finset.sum_eq_single s (fun b _ hbs => by rw [hall b hbs, mul_zero])
      (fun h' => absurd (Finset.mem_univ s) h'), Function.comp_apply,
      UnitaryFieldData.bar_apply, ← pow_succ] at hvv
    exact hs ((pow_eq_zero_iff (Nat.succ_ne_zero _)).mp hvv)
  exact ⟨s, t, Ne.symm hts, fun d hd => heig d hd s t hs ht⟩

end Linear

section Lift

variable {G : Type} [Group G] {K : Type} [Field K] {f n : ℕ}

theorem conj_mem_sylow_of_mem_suPairs {φ : ↥(unitarySU 2 f K n) →* G} {V : Subgroup G}
    {P : Sylow 2 ↥(V.comap φ)} [Unique (Sylow 2 ↥(V.comap φ))] {b : G} {D : GL (Fin n) K}
    (hD : (b, D) ∈ SUTorus.suPairs φ) (hbV : b ∈ Subgroup.normalizer (V : Set G))
    {w : ↥(V.comap φ)} (hw : w ∈ (P : Subgroup ↥(V.comap φ))) :
    ∃ w' : ↥(V.comap φ), w' ∈ (P : Subgroup ↥(V.comap φ)) ∧
      (((w' : ↥(unitarySU 2 f K n)) : GL (Fin n) K)) =
        D * (((w : ↥(unitarySU 2 f K n)) : GL (Fin n) K)) * D⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmem : D * (((w : ↥(unitarySU 2 f K n)) : GL (Fin n) K)) * D⁻¹ ∈ unitarySU 2 f K n :=
    (Subgroup.mem_normalizer_iff.mp hD.1 _).mp (w : ↥(unitarySU 2 f K n)).2
  set u : ↥(unitarySU 2 f K n) := ⟨_, hmem⟩ with hu
  have hφu : φ u = b * φ (w : ↥(unitarySU 2 f K n)) * b⁻¹ := (hD.2 _ u rfl).symm
  have huV : u ∈ V.comap φ := by
    show φ u ∈ V
    rw [hφu]
    exact (Subgroup.mem_normalizer_iff.mp hbV _).mp w.2
  set w' : ↥(V.comap φ) := ⟨u, huV⟩ with hw'
  refine ⟨w', ?_, rfl⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp P.isPGroup' ⟨w, hw⟩
  have hwk : w ^ 2 ^ k = 1 := by
    have h1 := pow_orderOf_eq_one (⟨w, hw⟩ : (P : Subgroup ↥(V.comap φ)))
    rw [hk] at h1
    have h3 := congrArg Subtype.val h1
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h3
  have hw'k : w' ^ 2 ^ k = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_one]
    change (D * (((w : ↥(unitarySU 2 f K n)) : GL (Fin n) K)) * D⁻¹) ^ 2 ^ k = 1
    rw [conj_pow, ← Subgroup.coe_pow, ← Subgroup.coe_pow, hwk, Subgroup.coe_one, Subgroup.coe_one,
      mul_one, mul_inv_cancel]
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow (isPGroup_zpowers_of_pow Nat.prime_two hw'k)
  rw [Subsingleton.elim Q P] at hQ
  exact hQ (Subgroup.mem_zpowers _)

theorem exists_framePair_of_twoSubgroup (h : UnitaryFieldData 2 f K)
    {φ : ↥(unitarySU 2 f K n) →* G} (hker : φ.ker ≤ Subgroup.center ↥(unitarySU 2 f K n))
    {B V : Subgroup G} (hV1 : V ≠ ⊥) (hV2 : IsPGroup 2 V) (hVφ : V ≤ φ.range)
    (hBV : B ≤ Subgroup.normalizer (V : Set G)) :
    ∃ s t : Fin n, s ≠ t ∧ GGFramePair φ B s t := by
  classical
  have : Finite K := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Vt : Subgroup ↥(unitarySU 2 f K n) := V.comap φ with hVt
  set f' : ↥Vt →* G := φ.comp Vt.subtype with hf'
  have hfr : f'.range ≤ V := by
    rintro _ ⟨w, rfl⟩
    exact w.2
  have hker' : f'.ker ≤ Subgroup.center ↥Vt := by
    intro w hw
    have hz : (w : ↥(unitarySU 2 f K n)) ∈ Subgroup.center _ := hker hw
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro v
    exact Subtype.ext (hz v)
  have hrange2 : IsPGroup 2 f'.range := hV2.to_le hfr
  have : Finite f'.range := Finite.of_surjective _ f'.rangeRestrict_surjective
  have : Group.IsNilpotent f'.range := hrange2.isNilpotent
  have : Group.IsNilpotent ↥Vt :=
    Subgroup.isNilpotent_of_ker_le_center f'.rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict]; exact hker')
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥Vt))
  have hPn : (P : Subgroup ↥Vt).Normal := inferInstance
  have := Sylow.unique_of_normal P hPn
  have hP1 : (P : Subgroup ↥Vt) ≠ ⊥ := by
    obtain ⟨⟨v, hvV⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hV1
    have hv1' : v ≠ 1 := fun h' => hv1 (Subtype.ext h')
    obtain ⟨u, hu⟩ := hVφ hvV
    have huV : u ∈ Vt := by
      show φ u ∈ V
      rw [hu]
      exact hvV
    obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp hV2 ⟨v, hvV⟩
    rw [Subgroup.orderOf_mk] at hj
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hj
      exact hv1' hj
    have hdvd : 2 ∣ Nat.card ↥Vt := by
      have h1 : orderOf v ∣ orderOf (⟨u, huV⟩ : ↥Vt) := by
        have h2 : f' ⟨u, huV⟩ = v := hu
        rw [← h2]
        exact orderOf_map_dvd f' _
      rw [hj] at h1
      exact (dvd_pow_self 2 hj0).trans (h1.trans (orderOf_dvd_natCard _))
    exact P.ne_bot_of_dvd_card hdvd
  set W : Subgroup (GL (Fin n) K) :=
    ((P : Subgroup ↥Vt).map Vt.subtype).map (unitarySU 2 f K n).subtype with hW
  have hW2 : IsPGroup 2 W := (P.isPGroup'.map _).map _
  have hW1 : W ≠ ⊥ := by
    rw [hW, Ne, Subgroup.map_eq_bot_iff_of_injective _ (unitarySU 2 f K n).subtype_injective,
      Subgroup.map_eq_bot_iff_of_injective _ Vt.subtype_injective]
    exact hP1
  have hWu : ∀ w ∈ W, (((w : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
      ((w : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
    exact ((mem_unitarySU_iff h).mp (w : ↥(unitarySU 2 f K n)).2).2
  set S : Set (Fin n → Kˣ) := {d | ∃ b ∈ B, SURep.GGFrameActs φ b d} with hS
  have hconj : ∀ b : G, ∀ D : GL (Fin n) K, (b, D) ∈ SUTorus.suPairs φ →
      b ∈ Subgroup.normalizer (V : Set G) → ∀ w ∈ W, D * w * D⁻¹ ∈ W := by
    rintro b D hD hbV _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    obtain ⟨w', hw', he⟩ := conj_mem_sylow_of_mem_suPairs (P := P) hD hbV hw
    exact ⟨_, ⟨w', hw', rfl⟩, he⟩
  have hSW : ∀ d ∈ S, ∀ w ∈ W, diagHom n d * w * (diagHom n d)⁻¹ ∈ W ∧
      (diagHom n d)⁻¹ * w * diagHom n d ∈ W := by
    rintro d ⟨b, hb, hbd⟩ w hw
    have hD := mem_suPairs_of_frameActs h hbd
    refine ⟨hconj b _ hD (hBV hb) w hw, ?_⟩
    have hD' := (SUTorus.suPairs φ).inv_mem hD
    rw [Prod.inv_mk] at hD'
    have h1 := hconj b⁻¹ _ hD' (Subgroup.inv_mem _ (hBV hb)) w hw
    rwa [inv_inv] at h1
  obtain ⟨s, t, hst, hd⟩ := exists_pair_of_isPGroup_two h hW2 hW1 hWu hSW
  exact ⟨s, t, hst, fun b hb τ hτ => hd τ ⟨b, hb, hτ⟩⟩

end Lift

end SURepair

section Inputs

open CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution)

@[expose] def GGUnitaryBTwoLocalInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU .PSU n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU .PSU n f).D .PSU n f ψ → GGSixStepOne p B Bs x L D J →
      p ∣ 2 ^ f + 1 →
        ∃ V : Subgroup G, V ≤ ggG0 p B x L D J ∧ V ≠ ⊥ ∧ IsPGroup 2 V ∧
          B ≤ Subgroup.normalizer (V : Set G)

theorem ggUnitaryBFramePairInput_of_twoLocal (h2 : GGUnitaryBTwoLocalInput) :
    GGUnitaryBFramePairInput := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 hp P hP _
  right
  obtain ⟨V, hVG, hV1, hV2, hBV⟩ := h2 G p B Bs x L D J n (f + 1) ψ hctx s1 hp
  have hF : Nat.card (GaloisField 2 (2 * (f + 1))) = (2 ^ (f + 1)) ^ 2 :=
    card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)
  have h : UnitaryFieldData 2 (f + 1) (GaloisField 2 (2 * (f + 1))) :=
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hrφ : (SURep.ggFrameU hF ψ P hP).range = ggG0 p B x L D J :=
    (SURep.range_ggFrameU hF ψ P hP).trans hrange
  exact SURepair.exists_framePair_of_twoSubgroup h (SURep.ker_ggFrameU_le hF ψ P hP hker) hV1 hV2
    (by rw [hrφ]; exact hVG) hBV

theorem ggUnitaryBstarCentralizerInput_of_twoLocal (h2 : GGUnitaryBTwoLocalInput) :
    GGUnitaryBstarCentralizerInput :=
  ggUnitaryBstarCentralizerInput_of_pair (ggUnitaryBFramePairInput_of_twoLocal h2)

theorem ggStepTwoUnitaryFusionLargeInput_of_twoLocal (h2 : GGUnitaryBTwoLocalInput) :
    GGStepTwoUnitaryFusionLargeInput :=
  ggStepTwoUnitaryFusionLargeInput_of_pair (ggUnitaryBFramePairInput_of_twoLocal h2)

end Inputs

end CFSG.StandardType
