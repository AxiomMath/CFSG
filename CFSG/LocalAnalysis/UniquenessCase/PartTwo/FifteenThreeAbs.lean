module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeJ2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

@[expose] def RJPrime153 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (J : Subgroup (MulAut W)) (R : Subgroup W), s15JNat J R →
      (∀ j ∈ J, (∀ r ∈ R, j r = r) → j = 1) →
      (⁅J, J⁆.subgroupOf J).index ≤ 2 ∧ s15KNat ↥⁅J, J⁆ ⁅J, J⁆ R

section Abstract

variable {W : Type} [CommGroup W] [Finite W]

private theorem s15_Three_derived_le {J B : Subgroup (MulAut W)} (hBJ : B ≤ J)
    (hB : (B.subgroupOf J).Normal) (hidx : (B.subgroupOf J).index ≤ 2) : ⁅J, J⁆ ≤ B := by
  haveI : (B.subgroupOf J).Normal := hB
  have hdvd : Nat.card (↥J ⧸ B.subgroupOf J) ∣ 2 := by
    have hle : Nat.card (↥J ⧸ B.subgroupOf J) ≤ 2 := by
      rw [← Subgroup.index_eq_card]
      exact hidx
    have hge : 1 ≤ Nat.card (↥J ⧸ B.subgroupOf J) := Nat.card_pos
    have hcases : Nat.card (↥J ⧸ B.subgroupOf J) = 1 ∨
        Nat.card (↥J ⧸ B.subgroupOf J) = 2 := by omega
    rcases hcases with h | h <;> rw [h] <;> norm_num
  haveI : IsMulCommutative (↥J ⧸ B.subgroupOf J) :=
    (isCyclic_of_card_dvd_prime (p := 2) hdvd).isMulCommutative
  have hmap : (_root_.commutator ↥J).map (QuotientGroup.mk' (B.subgroupOf J)) = ⊥ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      QuotientGroup.range_mk', ← _root_.commutator_def, commutator_eq_bot]
  have hcomm : _root_.commutator ↥J ≤ B.subgroupOf J := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmap
    exact hmap
  calc ⁅J, J⁆ = (_root_.commutator ↥J).map J.subtype :=
        (Subgroup.map_subtype_commutator J).symm
    _ ≤ (B.subgroupOf J).map J.subtype := Subgroup.map_mono hcomm
    _ = B := Subgroup.map_subgroupOf_eq_of_le hBJ

private theorem s15_Three_eq_derived {J B : Subgroup (MulAut W)} (hBJ : B ≤ J)
    (hB : (B.subgroupOf J).Normal) (hidx : (B.subgroupOf J).index ≤ 2)
    (hDer : (⁅J, J⁆.subgroupOf J).index ≤ 2)
    (hno2 : ∀ N : Subgroup ↥B, N.Normal → (∃ n : ℕ, N.index = 2 ^ n) → N = ⊤) :
    B = ⁅J, J⁆ := by
  set J' : Subgroup (MulAut W) := ⁅J, J⁆ with hJ'def
  have hJ'J : J' ≤ J := hJ'def.symm ▸ Subgroup.commutator_le_self J
  have hJ'B : J' ≤ B := hJ'def.symm ▸ s15_Three_derived_le hBJ hB hidx
  have hJ'eq : J'.subgroupOf J = _root_.commutator ↥J := by
    apply Subgroup.map_injective (f := J.subtype) J.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hJ'J, Subgroup.map_subtype_commutator]
  have hJ'n : (J'.subgroupOf J).Normal := hJ'eq ▸ inferInstance
  have hN : (J'.subgroupOf B).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hJ'B]
    intro h k hh hk
    exact (Subgroup.normal_subgroupOf_iff hJ'J).mp hJ'n h k hh (hBJ hk)
  have hdvd : (J'.subgroupOf B).index ∣ (J'.subgroupOf J).index :=
    ⟨B.relIndex J, (Subgroup.relIndex_mul_relIndex J' B J hJ'B hBJ).symm⟩
  have hNle : (J'.subgroupOf B).index ≤ 2 := by
    have hpos : 0 < (J'.subgroupOf J).index := by
      rw [Subgroup.index_eq_card]; exact Nat.card_pos
    exact (Nat.le_of_dvd hpos hdvd).trans hDer
  have hge : 1 ≤ (J'.subgroupOf B).index := by
    rw [Subgroup.index_eq_card]; exact Nat.card_pos
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (J'.subgroupOf B).index = 2 ^ n := by
    have hcases : (J'.subgroupOf B).index = 1 ∨ (J'.subgroupOf B).index = 2 := by omega
    rcases hcases with h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
  have htop : J'.subgroupOf B = ⊤ := hno2 (J'.subgroupOf B) hN ⟨n, hn⟩
  exact le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hJ'B

private theorem s15_Three_conj_mem_tgroup {A : Subgroup (MulAut W)} {t a : MulAut W}
    (ha : a ∈ A) {j : MulAut W} (hj : j ∈ s15TGroup A t) :
    a * j * a⁻¹ ∈ s15TGroup A t := by
  rw [s15TGroup] at hj ⊢
  induction hj using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    refine Subgroup.subset_closure ⟨b * a⁻¹, A.mul_mem hb (A.inv_mem ha), ?_⟩
    group
  | one => simp
  | mul x y _ _ hx hy =>
    rw [show a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) by group]
    exact mul_mem hx hy
  | inv x _ hx =>
    rw [show a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ by group]
    exact inv_mem hx

private theorem s15_Three_normalizes_tgroup {A : Subgroup (MulAut W)} {t a : MulAut W}
    (ha : a ∈ A) : ∀ j : MulAut W, j ∈ s15TGroup A t ↔ a * j * a⁻¹ ∈ s15TGroup A t := by
  intro j
  refine ⟨s15_Three_conj_mem_tgroup ha, fun hj => ?_⟩
  have h := s15_Three_conj_mem_tgroup (A.inv_mem ha) hj
  have h' : a⁻¹ * (a * j * a⁻¹) * (a⁻¹)⁻¹ = j := by group
  rwa [h'] at h

private theorem s15_Three_mem_stabSub {A : Subgroup (MulAut W)} {R : Subgroup W}
    (hR : StableUnder A R) {a : MulAut W} (ha : a ∈ A) : a ∈ stabSub R := by
  intro u
  refine ⟨fun hu => ?_, fun hu => hR a ha u hu⟩
  have h := hR a⁻¹ (A.inv_mem ha) (a u) hu
  simpa [MulAut.inv_apply] using h

private theorem s15_Three_mem_stabSub_zpowers {t : MulAut W} {R : Subgroup W}
    (hRt : StableUnder (Subgroup.zpowers t) R) {x : MulAut W}
    (hx : x ∈ Subgroup.zpowers t) : x ∈ stabSub R := by
  intro u
  refine ⟨fun hu => ?_, fun hu => hRt x hx u hu⟩
  have h := hRt x⁻¹ (Subgroup.inv_mem _ hx) (x u) hu
  simpa [MulAut.inv_apply] using h

private theorem s15_Three_tgroup_stable_R {A : Subgroup (MulAut W)} {t : MulAut W}
    {R : Subgroup W} (hR : StableUnder A R) (hRt : StableUnder (Subgroup.zpowers t) R) :
    StableUnder (s15TGroup A t) R := by
  have hle : s15TGroup A t ≤ stabSub R := by
    rw [s15TGroup, Subgroup.closure_le]
    rintro x ⟨a, ha, rfl⟩
    exact (stabSub R).mul_mem
      ((stabSub R).mul_mem ((stabSub R).inv_mem (s15_Three_mem_stabSub hR ha))
        (s15_Three_mem_stabSub_zpowers hRt (Subgroup.mem_zpowers t)))
      (s15_Three_mem_stabSub hR ha)
  intro x hx r hr
  exact (mem_stabSub.mp (hle hx) r).2 hr

private theorem s15_Three_act_trivial {A J B : Subgroup (MulAut W)} {R : Subgroup W}
    (hR : StableUnder A R) (hBJ : B ≤ J) (hB : (B.subgroupOf J).Normal)
    (hidx : (B.subgroupOf J).index ≤ 2)
    (hno2A : ∀ N : Subgroup ↥A, N.Normal → (∃ n : ℕ, N.index = 2 ^ n) → N = ⊤)
    (hfaith : ∀ j ∈ J, (∀ r ∈ R, j r = r) → j = 1)
    (hact : ∀ a ∈ A, ∃ j ∈ J, ∀ r ∈ R, a r = j r) :
    ∀ a ∈ A, ∃ b ∈ B, ∀ r ∈ R, a r = b r := by
  classical
  let jOf : ↥A → MulAut W := fun a => Classical.choose (hact a a.2)
  have hjOf_mem : ∀ a : ↥A, jOf a ∈ J := fun a => (Classical.choose_spec (hact a a.2)).1
  have hjOf_act : ∀ a : ↥A, ∀ r ∈ R, (a : MulAut W) r = jOf a r :=
    fun a => (Classical.choose_spec (hact a a.2)).2
  have hmul : ∀ a b : ↥A, jOf (a * b) = jOf a * jOf b := by
    intro a b
    have hker : (jOf (a * b))⁻¹ * (jOf a * jOf b) = 1 := by
      refine hfaith ((jOf (a * b))⁻¹ * (jOf a * jOf b))
        (J.mul_mem (J.inv_mem (hjOf_mem (a * b)))
          (J.mul_mem (hjOf_mem a) (hjOf_mem b))) ?_
      intro r hr
      have h1 : (jOf a) ((jOf b) r) = jOf (a * b) r := by
        rw [← hjOf_act b r hr, ← hjOf_act a ((b : MulAut W) r) (hR b b.2 r hr),
          ← hjOf_act (a * b) r hr]
        rfl
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, h1]
      simp
    exact inv_mul_eq_one.mp hker
  let f : ↥A →* ↥J :=
    { toFun := fun a => ⟨jOf a, hjOf_mem a⟩
      map_one' := by
        apply Subtype.ext
        exact hfaith (jOf 1) (hjOf_mem 1)
          (fun r hr => by simpa using (hjOf_act 1 r hr).symm)
      map_mul' := fun a b => by
        apply Subtype.ext
        exact hmul a b }
  haveI : (B.subgroupOf J).Normal := hB
  let θ : ↥A →* ↥J ⧸ (B.subgroupOf J) := (QuotientGroup.mk' (B.subgroupOf J)).comp f
  have hker_le : θ.ker.index ≤ 2 := by
    rw [Subgroup.index_ker]
    calc Nat.card θ.range ≤ Nat.card (↥J ⧸ (B.subgroupOf J)) := by
          simpa using Subgroup.card_le_of_le (show θ.range ≤ ⊤ from le_top)
      _ = (B.subgroupOf J).index := (Subgroup.index_eq_card (B.subgroupOf J)).symm
      _ ≤ 2 := hidx
  have hker_ge : 1 ≤ θ.ker.index := by
    rw [Subgroup.index_ker]; exact Nat.card_pos
  obtain ⟨n, hn⟩ : ∃ n : ℕ, θ.ker.index = 2 ^ n := by
    have hcases : θ.ker.index = 1 ∨ θ.ker.index = 2 := by omega
    rcases hcases with h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
  have hker_top : θ.ker = ⊤ := hno2A θ.ker inferInstance ⟨n, hn⟩
  intro a ha
  have hmem : (⟨a, ha⟩ : ↥A) ∈ θ.ker := by rw [hker_top]; trivial
  rw [MonoidHom.mem_ker] at hmem
  change QuotientGroup.mk' (B.subgroupOf J) (f ⟨a, ha⟩) = 1 at hmem
  have hmemN : f ⟨a, ha⟩ ∈ B.subgroupOf J := (QuotientGroup.eq_one_iff _).mp hmem
  exact ⟨jOf ⟨a, ha⟩, Subgroup.mem_subgroupOf.mp hmemN, fun r hr =>
    hjOf_act ⟨a, ha⟩ r hr⟩

private theorem s15_Three_commSub_sup (B : Subgroup (MulAut W)) (X Y : Subgroup W) :
    commSub (X ⊔ Y) B = commSub X B ⊔ commSub Y B := by
  refine le_antisymm ?_ ?_
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨b, hb, w, hw, rfl⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.1 hw
    have h1 : b (x * y) * (x * y)⁻¹ = (b x * x⁻¹) * (b y * y⁻¹) := by
      rw [map_mul, mul_inv_rev]
      calc b x * b y * (y⁻¹ * x⁻¹)
          = b x * b y * (x⁻¹ * y⁻¹) := by rw [mul_comm (y⁻¹) (x⁻¹)]
        _ = b x * (b y * (x⁻¹ * y⁻¹)) := by rw [mul_assoc]
        _ = b x * (x⁻¹ * (b y * y⁻¹)) := by
              rw [← mul_assoc (b y) (x⁻¹) (y⁻¹), mul_comm (b y) (x⁻¹), mul_assoc]
        _ = (b x * x⁻¹) * (b y * y⁻¹) := by rw [← mul_assoc]
    rw [h1]
    exact (commSub X B ⊔ commSub Y B).mul_mem
      (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨b, hb, x, hx, rfl⟩))
      (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨b, hb, y, hy, rfl⟩))
  · exact sup_le (commSub_mono le_sup_left le_rfl) (commSub_mono le_sup_right le_rfl)

private theorem s15_Three_commSub_stable {A B : Subgroup (MulAut W)} {R : Subgroup W}
    (hR : StableUnder A R) (hBA : ∀ a ∈ A, ∀ b ∈ B, a⁻¹ * b * a ∈ B) :
    StableUnder A (commSub R B) := by
  intro a ha c hc
  rw [commSub] at hc ⊢
  induction hc using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, r, hr, rfl⟩ := hz
    refine Subgroup.subset_closure ⟨a * b * a⁻¹, ?_, a r, hR a ha r hr, ?_⟩
    · have := hBA a⁻¹ (A.inv_mem ha) b hb
      simpa using this
    · have h2 : (a * b * a⁻¹) (a r) = a (b r) := by simp [MulAut.mul_apply]
      rw [map_mul, map_inv, h2]
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

private theorem s15_Three_commSub_eq_bot_or_top {A B : Subgroup (MulAut W)} {R : Subgroup W}
    (hR : IsIrrOn A R ⊥) (hBA : ∀ a ∈ A, ∀ b ∈ B, a⁻¹ * b * a ∈ B)
    (hBR : StableUnder B R) : commSub R B = ⊥ ∨ commSub R B = R := by
  have hle : commSub R B ≤ R := commSub_le_of_invariant hBR
  have hstab : StableUnder A (commSub R B) :=
    s15_Three_commSub_stable hR.2.1 hBA
  rcases hR.2.2.2 (commSub R B) hstab bot_le hle with h | h
  · exact Or.inl h
  · exact Or.inr h

private theorem s15_Three_card_comm_two (hW : ∀ w : W, w ^ 2 = 1) {t : MulAut W}
    (ht : InducesTransvection t ⊤) :
    Nat.card ↥(commSub ⊤ (Subgroup.zpowers t)) = 2 := by
  rw [card_eq_two_pow hW, ht.2, pow_one]

private theorem s15_Three_card_le_two_of_comm (hW : ∀ w : W, w ^ 2 = 1) {t : MulAut W}
    (ht : InducesTransvection t ⊤) {R : Subgroup W}
    (hR : commSub R (Subgroup.zpowers t) = R) : Nat.card ↥R ≤ 2 := by
  rw [← hR]
  exact (Subgroup.card_le_of_le (commSub_mono le_top le_rfl)).trans
    (le_of_eq (s15_Three_card_comm_two hW ht))

private theorem s15_Three_comm_eq_bot_of_card_two {A : Subgroup (MulAut W)} {R : Subgroup W}
    (hR : StableUnder A R) (hcard : Nat.card ↥R ≤ 2) : commSub R A = ⊥ := by
  rw [commSub_eq_bot_iff]
  intro r hr a ha
  by_cases h1 : Nat.card ↥R = 1
  · have hRbot : R = ⊥ := Subgroup.card_eq_one.mp h1
    have hr1 : r = 1 := Subgroup.mem_bot.mp (hRbot ▸ hr)
    rw [hr1, map_one]
  · have h2 : Nat.card ↥R = 2 := by
      have hge : 1 ≤ Nat.card ↥R := Nat.card_pos
      omega
    obtain ⟨c, hc1, hcu⟩ := (Nat.card_eq_two_iff' (1 : ↥R)).1 h2
    have hcne : (c : W) ≠ 1 := fun h => hc1 (Subtype.ext h)
    have hmemc : (c : W) ∈ R := c.2
    have hchar : ∀ x ∈ R, x = 1 ∨ x = (c : W) := by
      intro x hx
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · right
        have := hcu ⟨x, hx⟩ (fun h => hx1 (congrArg Subtype.val h))
        exact congrArg Subtype.val this
    rcases hchar r hr with hr1 | hrc
    · rw [hr1, map_one]
    · rw [hrc]
      have hac : a (c : W) ∈ R := hR a ha (c : W) hmemc
      rcases hchar (a (c : W)) hac with h1' | h2'
      · exfalso
        have ha1 : a (c : W) = 1 := h1'
        have hc1' : (c : W) = 1 := by
          have := congrArg (fun x => a.symm x) ha1
          simpa [MulAut.inv_apply] using this
        exact hcne hc1'
      · exact h2'

private theorem s15_Three_commSub_zpowers_stable {A : Subgroup (MulAut W)} {t : MulAut W}
    {R : Subgroup W} (hR : StableUnder A R) (hRt : StableUnder (Subgroup.zpowers t) R)
    (hcomm : ∀ a ∈ A, ∀ u ∈ R, t (a u) = a (t u)) :
    StableUnder A (commSub R (Subgroup.zpowers t)) := by
  intro a ha c hc
  rw [commSub] at hc ⊢
  induction hc using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨x, hx, u, hu, rfl⟩ := hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    refine Subgroup.subset_closure ⟨t ^ k, Subgroup.zpow_mem_zpowers t k,
      a u, hR a ha u hu, ?_⟩
    have hk : (t ^ k) (a u) = a ((t ^ k) u) :=
      (zpow_induction_left (g := t)
        (P := fun x : MulAut W => (∀ v ∈ R, x v ∈ R) ∧ ∀ v ∈ R, x (a v) = a (x v))
        ⟨by intro v hv; simpa using hv, by intro v hv; simp⟩
        (fun x hx => ⟨by
            intro v hv
            exact hRt t (Subgroup.mem_zpowers t) (x v) (hx.1 v hv),
          by
            intro v hv
            rw [MulAut.mul_apply, MulAut.mul_apply, hx.2 v hv]
            exact hcomm a ha (x v) (hx.1 v hv)⟩)
        (fun x hx => ⟨by
            intro v hv
            exact hRt t⁻¹ (Subgroup.inv_mem _ (Subgroup.mem_zpowers t)) (x v) (hx.1 v hv),
          by
            intro v hv
            rw [MulAut.mul_apply, MulAut.mul_apply, hx.2 v hv]
            have hw := hcomm a ha (t⁻¹ (x v))
              (hRt t⁻¹ (Subgroup.inv_mem _ (Subgroup.mem_zpowers t)) (x v) (hx.1 v hv))
            have hw' : t (a (t⁻¹ (x v))) = a (x v) := by
              simpa [MulAut.mul_apply, MulAut.inv_apply] using hw
            have hw2 : a (t⁻¹ (x v)) = t⁻¹ (a (x v)) := by
              rw [← hw']
              simp [MulAut.mul_apply, MulAut.inv_apply]
            exact hw2.symm⟩)
        k).2 u hu
    rw [map_mul, map_inv, ← hk]
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

theorem s15_Three_knat_of_jnat (hDer : RJPrime153) (hW : ∀ w : W, w ^ 2 = 1)
    {J B : Subgroup (MulAut W)} {R : Subgroup W} (hJ : s15JNat J R)
    (hfaith : ∀ j ∈ J, (∀ r ∈ R, j r = r) → j = 1) (hBJ : B ≤ J) (hB : (B.subgroupOf J).Normal)
    (hidx : (B.subgroupOf J).index ≤ 2)
    (hno2 : ∀ N : Subgroup ↥B, N.Normal → (∃ n : ℕ, N.index = 2 ^ n) → N = ⊤) :
    s15KNat ↥B B R := by
  obtain ⟨hidx', hK⟩ := hDer W hW J R hJ hfaith
  have heq : B = ⁅J, J⁆ := s15_Three_eq_derived hBJ hB hidx hidx' hno2
  rw [heq]
  exact hK

theorem s15_Three_act_in_B (hNorm : RNormNat153) (hW : ∀ w : W, w ^ 2 = 1)
    {A : Subgroup (MulAut W)} {t : MulAut W} (ht : InducesTransvection t ⊤)
    (htA : s15Normalizes t A) (hF : Fstar A = A) (hO : s15TwoCoreTrivial A) {R S : Subgroup W}
    (hR : IsIrrOn A R ⊥) (hRt : StableUnder (Subgroup.zpowers t) R) (hS : StableUnder A S)
    (hRS' : R ⊔ S = ⊤) (htS : S ≤ fixV (Subgroup.zpowers t))
    (hJ : s15JNat (s15TGroup A t) R) :
    ∀ a ∈ A, ∃ b ∈ ⁅A, Subgroup.zpowers t⁆, ∀ r ∈ R, a r = b r := by
  obtain ⟨hBA, hBJ, hBn, hidx, hno2⟩ := s15_Three_B_facts hW ht htA hF hO
  have hSfix : S ≤ fixV (s15TGroup A t) := s15_Three_tgroup_fix_S hS htS
  have hfaithJ : ∀ j ∈ s15TGroup A t, (∀ r ∈ R, j r = r) → j = 1 :=
    s15_Three_tgroup_faithful hRS' hSfix
  have hJstab : StableUnder (s15TGroup A t) R := s15_Three_tgroup_stable_R hR.2.1 hRt
  have hact : ∀ a ∈ A, ∃ j ∈ s15TGroup A t, ∀ r ∈ R, a r = j r := by
    intro a ha
    exact hNorm W hW (s15TGroup A t) R hJ hJstab hfaithJ a
      (s15_Three_mem_stabSub hR.2.1 ha) (s15_Three_normalizes_tgroup ha)
  exact s15_Three_act_trivial hR.2.1 hBJ hBn hidx (s15_Three_no_two_quotient hF hO) hfaithJ hact

theorem s15_Three_comm_B (hW : ∀ w : W, w ^ 2 = 1) {A : Subgroup (MulAut W)} {t : MulAut W}
    (ht : InducesTransvection t ⊤) (htA : s15Normalizes t A) (hF : Fstar A = A)
    (hO : s15TwoCoreTrivial A) {R S : Subgroup W} (hR : IsIrrOn A R ⊥) (hRc : commSub R A = R)
    (hRt : StableUnder (Subgroup.zpowers t) R) (hS : StableUnder A S) (hRS' : R ⊔ S = ⊤)
    (htS : S ≤ fixV (Subgroup.zpowers t)) (htR : commSub R (Subgroup.zpowers t) ≠ ⊥) :
    commSub ⊤ ⁅A, Subgroup.zpowers t⁆ = R := by
  obtain ⟨hBA, hBJ, hBn, hidx, hno2⟩ := s15_Three_B_facts hW ht htA hF hO
  set B : Subgroup (MulAut W) := ⁅A, Subgroup.zpowers t⁆ with hBdef
  have hJirr : IsIrrOn (s15TGroup A t) R ⊥ :=
    s15_Three_irr_J hW ht htA hF hO hR hRt hS hRS' htS htR
  have hJstabR : StableUnder (s15TGroup A t) R := hJirr.2.1
  have hSfixJ : S ≤ fixV (s15TGroup A t) := s15_Three_tgroup_fix_S hS htS
  have hBS : ∀ s ∈ S, ∀ b ∈ B, b s = s := fun s hs b hb => hSfixJ hs b (hBJ hb)
  have hBR : StableUnder B R := fun b hb r hr => hJstabR b (hBJ hb) r hr
  have hJB : ∀ j ∈ s15TGroup A t, ∀ b ∈ B, j⁻¹ * b * j ∈ B := by
    intro j hj b hb
    have := (Subgroup.normal_subgroupOf_iff hBJ).mp hBn b j⁻¹ hb (inv_mem hj)
    simpa using this
  have hsup : commSub ⊤ B = commSub R B := by
    rw [← hRS', s15_Three_commSub_sup]
    have hSbot : commSub S B = ⊥ := commSub_eq_bot_iff.mpr hBS
    rw [hSbot, sup_bot_eq]
  rw [hsup]
  rcases s15_Three_commSub_eq_bot_or_top hJirr hJB hBR with hbot | htop
  · exfalso
    have hfixB : R ≤ fixV B := commSub_eq_bot_iff.mp hbot
    have htc : ∀ a ∈ A, ∀ u ∈ R, t (a u) = a (t u) := by
      intro a ha u hu
      have hb : ⁅a⁻¹, t⁆ ∈ B := by
        have := Subgroup.commutator_mem_commutator (A.inv_mem ha) (Subgroup.mem_zpowers t)
        simpa [commutatorElement_def] using this
      have htu : t u ∈ R := hRt t (Subgroup.mem_zpowers t) u hu
      have hfix := (mem_fixV.1 (hfixB htu)) ⁅a⁻¹, t⁆ hb
      rw [commutatorElement_def] at hfix
      have h2 := congrArg (fun x => a x) hfix
      simpa [MulAut.mul_apply, MulAut.inv_apply] using h2
    have hstab : StableUnder A (commSub R (Subgroup.zpowers t)) :=
      s15_Three_commSub_zpowers_stable hR.2.1 hRt htc
    have hcommt_eq : commSub R (Subgroup.zpowers t) = R := by
      rcases hR.2.2.2 (commSub R (Subgroup.zpowers t)) hstab bot_le
        (commSub_le_of_invariant hRt) with h | h
      · exact absurd h htR
      · exact h
    have hcard : Nat.card ↥R ≤ 2 := s15_Three_card_le_two_of_comm hW ht hcommt_eq
    have hcommA : commSub R A = ⊥ := s15_Three_comm_eq_bot_of_card_two hR.2.1 hcard
    rw [hRc] at hcommA
    exact hR.1.ne' hcommA
  · exact htop

theorem s15_Three_core (hDer : RJPrime153) (hNorm : RNormNat153) (hW : ∀ w : W, w ^ 2 = 1)
    {A : Subgroup (MulAut W)} {t : MulAut W} (ht : InducesTransvection t ⊤)
    (htA : s15Normalizes t A) (hF : Fstar A = A) (hO : s15TwoCoreTrivial A) {R S : Subgroup W}
    (hR : IsIrrOn A R ⊥) (hRc : commSub R A = R)
    (hRt : StableUnder (Subgroup.zpowers t) R) (hS : StableUnder A S)
    (hRS' : R ⊔ S = ⊤) (htS : S ≤ fixV (Subgroup.zpowers t))
    (htR : commSub R (Subgroup.zpowers t) ≠ ⊥) (hJ : s15JNat (s15TGroup A t) R) :
    ⁅A, Subgroup.zpowers t⁆ ≤ A ∧ (∀ s ∈ S, ∀ b ∈ ⁅A, Subgroup.zpowers t⁆, b s = s) ∧
      (∀ a ∈ A, ∃ b ∈ ⁅A, Subgroup.zpowers t⁆, ∀ r ∈ R, a r = b r) ∧
      commSub ⊤ ⁅A, Subgroup.zpowers t⁆ = R ∧
      s15KNat ↥⁅A, Subgroup.zpowers t⁆ ⁅A, Subgroup.zpowers t⁆ R := by
  obtain ⟨hBA, hBJ, hBn, hidx, hno2⟩ := s15_Three_B_facts hW ht htA hF hO
  have hSfix := s15_Three_tgroup_fix_S hS htS
  refine ⟨hBA, fun s hs b hb => hSfix hs b (hBJ hb), ?_, ?_, ?_⟩
  · exact s15_Three_act_in_B hNorm hW ht htA hF hO hR hRt hS hRS' htS hJ
  · exact s15_Three_comm_B hW ht htA hF hO hR hRc hRt hS hRS' htS htR
  · exact s15_Three_knat_of_jnat hDer hW hJ (s15_Three_tgroup_faithful hRS' hSfix) hBJ hBn hidx hno2

theorem s15_Three_abstract (hMcL : RMcLaughlin) (hDer : RJPrime153) (hNorm : RNormNat153)
    (hW : ∀ w : W, w ^ 2 = 1)
    {A N : Subgroup (MulAut W)} {t : MulAut W} (hAN : A ≤ N)
    (hNA : ∀ n ∈ N, ∀ a : MulAut W, a ∈ A ↔ n * a * n⁻¹ ∈ A) (htN : t ∈ N)
    (ht : InducesTransvection t ⊤) (hF : Fstar A = A) (hO : s15TwoCoreTrivial A)
    (hcomm : commSub ⊤ A = ⊤) (hsemi : s15Semisimple A)
    (htrans : ∀ I I' : Subgroup W, IsIrrOn A I ⊥ → IsIrrOn A I' ⊥ →
      ∃ n ∈ N, s15SecIso A (I.map (n : MulAut W).toMonoidHom) ⊥ I' ⊥) :
    ∃ B : Subgroup (MulAut W), B = ⁅A, Subgroup.zpowers t⁆ ∧ B ≤ A ∧
      IsDirectProdOfConj A B N ∧ s15KNat ↥B B (commSub ⊤ B) ∧
      sSupIndep {Z : Subgroup W | ∃ n ∈ N,
        Z = commSub ⊤ (B.map (MulAut.conj n).toMonoidHom)} ∧
      sSup {Z : Subgroup W | ∃ n ∈ N,
        Z = commSub ⊤ (B.map (MulAut.conj n).toMonoidHom)} = ⊤ := by
  have htA : s15Normalizes t A := fun a => hNA t htN a
  obtain ⟨R, S, hR, hRc, hRt, hS, hRS, hRS', htS, htR, hmult⟩ :=
    s15_Three_split hW ht htA hsemi hcomm
  have hJ := s15_Three_jnat hMcL hW ht htA hF hO hR hRt hS hRS hRS' htS htR
  obtain ⟨hBA, hBS, hAB, hBR, hK⟩ :=
    s15_Three_core hDer hNorm hW ht htA hF hO hR hRc hRt hS hRS' htS htR hJ
  obtain ⟨h1, h2, h3⟩ := s15_Three_assemble hW hNA hsemi htrans hR hS hRS hRS' hmult hBA hBS hAB hBR
  refine ⟨⁅A, Subgroup.zpowers t⁆, rfl, hBA, h1, ?_, h2, h3⟩
  rw [hBR]
  exact hK


end Abstract

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
