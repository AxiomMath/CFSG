module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeF
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeE

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

section Abstract

variable {W : Type} [CommGroup W] [Finite W]

private lemma s15_Three_conj_commut (g a k : MulAut W) :
    g * ⁅a, k⁆ * g⁻¹ = ⁅g * a, k⁆ * ⁅g, k⁆⁻¹ := by
  simp only [commutatorElement_def]
  group

private lemma s15_Three_conj_commut' (g a k : MulAut W) :
    g * ⁅a, k⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * k * g⁻¹⁆ := by
  simp only [commutatorElement_def]
  group

theorem s15_Three_comm_le {A : Subgroup (MulAut W)} {t : MulAut W} (htA : s15Normalizes t A) :
    ⁅A, Subgroup.zpowers t⁆ ≤ A := by
  refine Subgroup.commutator_le.mpr ?_
  intro a ha k hk
  have htn : t ∈ Subgroup.normalizer A := Subgroup.mem_normalizer_iff.mpr htA
  have hkn : k ∈ Subgroup.normalizer A := (Subgroup.zpowers_le.mpr htn) hk
  have hka : k * a⁻¹ * k⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.mp hkn a⁻¹).mp (A.inv_mem ha)
  have heq : ⁅a, k⁆ = a * (k * a⁻¹ * k⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [heq]
  exact A.mul_mem ha hka

theorem s15_Three_comm_normalized {A : Subgroup (MulAut W)} {t : MulAut W}
    (htA : s15Normalizes t A) {x : MulAut W} (hx : x ∈ ⁅A, Subgroup.zpowers t⁆) :
    (∀ a ∈ A, a⁻¹ * x * a ∈ ⁅A, Subgroup.zpowers t⁆) ∧
      t⁻¹ * x * t ∈ ⁅A, Subgroup.zpowers t⁆ := by
  have htn : t ∈ Subgroup.normalizer A := Subgroup.mem_normalizer_iff.mpr htA
  have hta : ∀ a ∈ A, t⁻¹ * a * t ∈ A := fun a ha =>
    (Subgroup.mem_normalizer_iff''.mp htn a).mp ha
  refine Subgroup.closure_induction
    (p := fun x _ => (∀ a ∈ A, a⁻¹ * x * a ∈ ⁅A, Subgroup.zpowers t⁆) ∧
      t⁻¹ * x * t ∈ ⁅A, Subgroup.zpowers t⁆) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨a', ha', k, hk, rfl⟩
    constructor
    · intro a ha
      have heq : a⁻¹ * ⁅a', k⁆ * a = ⁅a⁻¹ * a', k⁆ * ⁅a⁻¹, k⁆⁻¹ :=
        s15_Three_conj_commut a⁻¹ a' k
      rw [heq]
      exact (⁅A, Subgroup.zpowers t⁆).mul_mem
        (Subgroup.commutator_mem_commutator (A.mul_mem (A.inv_mem ha) ha') hk)
        ((⁅A, Subgroup.zpowers t⁆).inv_mem
          (Subgroup.commutator_mem_commutator (A.inv_mem ha) hk))
    · have hk_comm : t⁻¹ * k * t = k := by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
        have := conj_zpow (a := t⁻¹) (b := t) (i := i)
        simpa using this.symm
      have heq : t⁻¹ * ⁅a', k⁆ * t = ⁅t⁻¹ * a' * t, k⁆ := by
        have h := s15_Three_conj_commut' (g := t⁻¹) a' k
        simp only [inv_inv] at h
        rw [h, hk_comm]
      rw [heq]
      exact Subgroup.commutator_mem_commutator (hta a' ha') hk
  · refine ⟨fun a _ => ?_, ?_⟩
    · simpa using (⁅A, Subgroup.zpowers t⁆).one_mem
    · simpa using (⁅A, Subgroup.zpowers t⁆).one_mem
  · intro x y _ _ hx' hy'
    refine ⟨fun a ha => ?_, ?_⟩
    · have heq : a⁻¹ * (x * y) * a = (a⁻¹ * x * a) * (a⁻¹ * y * a) := by group
      rw [heq]
      exact (⁅A, Subgroup.zpowers t⁆).mul_mem (hx'.1 a ha) (hy'.1 a ha)
    · have heq : t⁻¹ * (x * y) * t = (t⁻¹ * x * t) * (t⁻¹ * y * t) := by group
      rw [heq]
      exact (⁅A, Subgroup.zpowers t⁆).mul_mem hx'.2 hy'.2
  · intro x _ hx'
    refine ⟨fun a ha => ?_, ?_⟩
    · have heq : a⁻¹ * x⁻¹ * a = (a⁻¹ * x * a)⁻¹ := by group
      rw [heq]
      exact (⁅A, Subgroup.zpowers t⁆).inv_mem (hx'.1 a ha)
    · have heq : t⁻¹ * x⁻¹ * t = (t⁻¹ * x * t)⁻¹ := by group
      rw [heq]
      exact (⁅A, Subgroup.zpowers t⁆).inv_mem hx'.2

theorem s15_Three_comm_le_tgroup {A : Subgroup (MulAut W)} {t : MulAut W} :
    ⁅A, Subgroup.zpowers t⁆ ≤ s15TGroup A t := by
  refine Subgroup.commutator_le.mpr ?_
  intro a ha k hk
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  have hgen : a * t * a⁻¹ ∈ s15TGroup A t :=
    Subgroup.subset_closure ⟨a⁻¹, A.inv_mem ha, by group⟩
  have htmem : t ∈ s15TGroup A t :=
    Subgroup.subset_closure ⟨1, A.one_mem, by simp⟩
  have heq : ⁅a, t ^ i⁆ = (a * t * a⁻¹) ^ i * (t ^ i)⁻¹ := by
    rw [commutatorElement_def, conj_zpow]
  rw [heq]
  exact (s15TGroup A t).mul_mem (Subgroup.zpow_mem _ hgen i)
    ((s15TGroup A t).inv_mem (Subgroup.zpow_mem _ htmem i))

theorem s15_Three_sq_eq_one (hW : ∀ w : W, w ^ 2 = 1) {t : MulAut W}
    (ht : InducesTransvection t ⊤) : t * t = 1 := by
  let C : Subgroup W := commSub ⊤ (Subgroup.zpowers t)
  have hcard : Nat.card C = 2 := by
    rw [card_eq_two_pow hW C, show rk C = 1 from ht.2]
    norm_num
  obtain ⟨c, hc1, hcu⟩ := (Nat.card_eq_two_iff' (1 : C)).1 hcard
  have hcne : (c : W) ≠ 1 := fun h => hc1 (Subtype.ext h)
  have hmemc : (c : W) ∈ C := c.2
  have hchar : ∀ x ∈ C, x = 1 ∨ x = (c : W) := by
    intro x hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · right
      have := hcu ⟨x, hx⟩ (fun h => hx1 (congrArg Subtype.val h))
      exact congrArg Subtype.val this
  have hstab : ∀ x ∈ C, t x ∈ C := by
    intro x hx
    refine Subgroup.closure_induction (p := fun y _ => t y ∈ C) ?_ ?_ ?_ ?_ hx
    · rintro y ⟨χ, hχ, w, -, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hχ
      refine Subgroup.subset_closure ⟨t ^ k, Subgroup.zpow_mem_zpowers t k, t w,
        Subgroup.mem_top _, ?_⟩
      rw [map_mul, map_inv]
      congr 1
      have hcomm : t ^ k * t = t * t ^ k := by group
      exact congrArg (fun φ : MulAut W => φ w) hcomm
    · simp
    · intro y z _ _ hy hz
      rw [map_mul]
      exact C.mul_mem hy hz
    · intro y _ hy
      rw [map_inv]
      exact C.inv_mem hy
  have htc : t (c : W) = (c : W) := by
    rcases hchar (t (c : W)) (hstab _ hmemc) with h | h
    · exact absurd (t.injective (h.trans (map_one t).symm)) hcne
    · exact h
  have hact : ∀ u : W, t u = u ∨ t u = u * c := by
    intro u
    have hmem : t u * u⁻¹ ∈ C :=
      Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, u, Subgroup.mem_top u, rfl⟩
    rcases hchar _ hmem with h | h
    · left
      exact mul_inv_eq_one.1 h
    · right
      have h' : t u * u⁻¹ = (c : W) := h
      calc t u = t u * u⁻¹ * u := by group
        _ = (c : W) * u := by rw [h']
        _ = u * c := mul_comm _ _
  ext u
  rcases hact u with h | h
  · simp [MulAut.mul_apply, h]
  · calc (t * t) u = t (t u) := rfl
      _ = t (u * c) := by rw [h]
      _ = t u * t c := by rw [map_mul]
      _ = (u * c) * c := by rw [h, htc]
      _ = u := by rw [mul_assoc, ← sq, hW c, mul_one]

theorem s15_Three_tgroup_le_sup (hW : ∀ w : W, w ^ 2 = 1) {A : Subgroup (MulAut W)}
    {t : MulAut W} (ht : InducesTransvection t ⊤) (htA : s15Normalizes t A) :
    s15TGroup A t ≤ ⁅A, Subgroup.zpowers t⁆ ⊔ Subgroup.zpowers t := by
  have ht2 : t * t = 1 := s15_Three_sq_eq_one hW ht
  refine (Subgroup.closure_le (K := ⁅A, Subgroup.zpowers t⁆ ⊔ Subgroup.zpowers t)).mpr ?_
  rintro x ⟨a, ha, rfl⟩
  have hcomm : ⁅a⁻¹, t⁆ ∈ ⁅A, Subgroup.zpowers t⁆ :=
    Subgroup.commutator_mem_commutator (A.inv_mem ha) (Subgroup.mem_zpowers t)
  have heq : a⁻¹ * t * a = ⁅a⁻¹, t⁆ * t := by
    rw [commutatorElement_def]
    group
  rw [heq]
  exact Subgroup.mul_mem_sup hcomm (Subgroup.mem_zpowers t)

theorem s15_Three_B_facts_basic {A : Subgroup (MulAut W)} {t : MulAut W}
    (htA : s15Normalizes t A) (hF : Fstar A = A) (hO : s15TwoCoreTrivial A) :
    ⁅A, Subgroup.zpowers t⁆ ≤ A ∧ ((⁅A, Subgroup.zpowers t⁆).subgroupOf A).Normal ∧
      Fstar ⁅A, Subgroup.zpowers t⁆ = ⁅A, Subgroup.zpowers t⁆ ∧
      s15TwoCoreTrivial ⁅A, Subgroup.zpowers t⁆ := by
  have hBA : ⁅A, Subgroup.zpowers t⁆ ≤ A := s15_Three_comm_le htA
  have hnorm : ((⁅A, Subgroup.zpowers t⁆).subgroupOf A).Normal := by
    refine (Subgroup.normal_subgroupOf_iff hBA).mpr ?_
    intro h k hh hk
    have := (s15_Three_comm_normalized htA hh).1 k⁻¹ (A.inv_mem hk)
    simpa using this
  exact ⟨hBA, hnorm, s15_Three_fstar_of_normal hBA hnorm hF,
    s15_Three_twoCore_of_normal hBA hnorm hO⟩

theorem s15_Three_B_facts (hW : ∀ w : W, w ^ 2 = 1) {A : Subgroup (MulAut W)} {t : MulAut W}
    (ht : InducesTransvection t ⊤) (htA : s15Normalizes t A) (hF : Fstar A = A)
    (hO : s15TwoCoreTrivial A) :
    ⁅A, Subgroup.zpowers t⁆ ≤ A ∧ ⁅A, Subgroup.zpowers t⁆ ≤ s15TGroup A t ∧
      ((⁅A, Subgroup.zpowers t⁆).subgroupOf (s15TGroup A t)).Normal ∧
      ((⁅A, Subgroup.zpowers t⁆).subgroupOf (s15TGroup A t)).index ≤ 2 ∧
      ∀ N : Subgroup ↥(⁅A, Subgroup.zpowers t⁆), N.Normal → (∃ n : ℕ, N.index = 2 ^ n) →
        N = ⊤ := by
  obtain ⟨hBA, hBnA, hFB, hOB⟩ := s15_Three_B_facts_basic htA hF hO
  have ht2 : t * t = 1 := s15_Three_sq_eq_one hW ht
  have htinv : t⁻¹ = t := by
    have h : t⁻¹ * (t * t) = t := by group
    rwa [ht2, mul_one] at h
  have hBJ : ⁅A, Subgroup.zpowers t⁆ ≤ s15TGroup A t := s15_Three_comm_le_tgroup
  have hJt : t ∈ s15TGroup A t :=
    Subgroup.subset_closure ⟨1, A.one_mem, by simp⟩
  have hJeq : s15TGroup A t = ⁅A, Subgroup.zpowers t⁆ ⊔ Subgroup.zpowers t := by
    refine le_antisymm (s15_Three_tgroup_le_sup hW ht htA) ?_
    exact sup_le hBJ (Subgroup.zpowers_le.mpr hJt)
  have hBnJ : ((⁅A, Subgroup.zpowers t⁆).subgroupOf (s15TGroup A t)).Normal := by
    have key : ∀ k ∈ s15TGroup A t,
        (∀ h ∈ ⁅A, Subgroup.zpowers t⁆, k * h * k⁻¹ ∈ ⁅A, Subgroup.zpowers t⁆) ∧
        (∀ h ∈ ⁅A, Subgroup.zpowers t⁆, k⁻¹ * h * k ∈ ⁅A, Subgroup.zpowers t⁆) := by
      intro k hk
      refine Subgroup.closure_induction
        (p := fun k _ => (∀ h ∈ ⁅A, Subgroup.zpowers t⁆,
            k * h * k⁻¹ ∈ ⁅A, Subgroup.zpowers t⁆) ∧
          (∀ h ∈ ⁅A, Subgroup.zpowers t⁆,
            k⁻¹ * h * k ∈ ⁅A, Subgroup.zpowers t⁆)) ?_ ?_ ?_ ?_ hk
      · rintro y ⟨a, ha, rfl⟩
        constructor
        · intro h hh
          have hab : a * h * a⁻¹ ∈ ⁅A, Subgroup.zpowers t⁆ :=
            (s15_Three_comm_normalized htA hh).1 a⁻¹ (A.inv_mem ha)
          have htab : t⁻¹ * (a * h * a⁻¹) * t ∈ ⁅A, Subgroup.zpowers t⁆ :=
            (s15_Three_comm_normalized htA hab).2
          have hfin : a⁻¹ * (t⁻¹ * (a * h * a⁻¹) * t) * a ∈
              ⁅A, Subgroup.zpowers t⁆ :=
            (s15_Three_comm_normalized htA htab).1 a ha
          have heq : (a⁻¹ * t * a) * h * (a⁻¹ * t * a)⁻¹ =
              a⁻¹ * (t * (a * h * a⁻¹) * t⁻¹) * a := by group
          rw [heq]
          simpa only [htinv] using hfin
        · intro h hh
          have hab : a * h * a⁻¹ ∈ ⁅A, Subgroup.zpowers t⁆ :=
            (s15_Three_comm_normalized htA hh).1 a⁻¹ (A.inv_mem ha)
          have htab : t⁻¹ * (a * h * a⁻¹) * t ∈ ⁅A, Subgroup.zpowers t⁆ :=
            (s15_Three_comm_normalized htA hab).2
          have hfin : a⁻¹ * (t⁻¹ * (a * h * a⁻¹) * t) * a ∈
              ⁅A, Subgroup.zpowers t⁆ :=
            (s15_Three_comm_normalized htA htab).1 a ha
          have heq : (a⁻¹ * t * a)⁻¹ * h * (a⁻¹ * t * a) =
              a⁻¹ * (t⁻¹ * (a * h * a⁻¹) * t) * a := by group
          rw [heq]
          exact hfin
      · refine ⟨fun h hh => ?_, fun h hh => ?_⟩ <;> simpa using hh
      · intro x y _ _ hx' hy'
        refine ⟨fun h hh => ?_, fun h hh => ?_⟩
        · have heq : (x * y) * h * (x * y)⁻¹ = x * (y * h * y⁻¹) * x⁻¹ := by group
          rw [heq]
          exact hx'.1 _ (hy'.1 h hh)
        · have heq : (x * y)⁻¹ * h * (x * y) = y⁻¹ * (x⁻¹ * h * x) * y := by group
          rw [heq]
          exact hy'.2 _ (hx'.2 h hh)
      · intro x _ hx'
        exact ⟨fun h hh => hx'.2 h hh, fun h hh => hx'.1 h hh⟩
    refine (Subgroup.normal_subgroupOf_iff hBJ).mpr ?_
    intro h k hh hk
    exact (key k hk).1 h hh
  have hidx : ((⁅A, Subgroup.zpowers t⁆).subgroupOf (s15TGroup A t)).index ≤ 2 := by
    let J := s15TGroup A t
    let NB : Subgroup ↥J := (⁅A, Subgroup.zpowers t⁆).subgroupOf J
    let NT : Subgroup ↥J := (Subgroup.zpowers t).subgroupOf J
    haveI : NB.Normal := hBnJ
    have hztJ : Subgroup.zpowers t ≤ J := Subgroup.zpowers_le.mpr hJt
    have htop : NT ⊔ NB = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hztJ hBJ, sup_comm, ← hJeq, Subgroup.subgroupOf_self]
    have hrel : NB.index = NB.relIndex NT := by
      have h := Subgroup.relIndex_sup_right (H := NT) (K := NB)
      rw [htop, Subgroup.relIndex_top_right] at h
      exact h
    have hmul : NB.relIndex NT * Nat.card (NB ⊓ NT : Subgroup ↥J) = Nat.card NT :=
      Subgroup.relIndex_mul_card NB NT
    have hcardNT : Nat.card NT = orderOf t := by
      rw [show Nat.card NT = Nat.card (Subgroup.zpowers t) from
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hztJ).toEquiv, Nat.card_zpowers]
    have horder : orderOf t ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      simpa [pow_two] using ht2
    change NB.index ≤ 2
    rw [hrel]
    haveI : Nonempty ↥NT := ⟨⟨1, NT.one_mem⟩⟩
    calc NB.relIndex NT ≤ orderOf t := by
          rw [← hcardNT]
          exact Nat.le_of_dvd Nat.card_pos (Dvd.intro _ hmul)
      _ ≤ 2 := Nat.le_of_dvd (by norm_num) horder
  exact ⟨hBA, hBJ, hBnJ, hidx, fun N hN hidxN => s15_Three_no_two_quotient hFB hOB N hN hidxN⟩

theorem s15_Three_conj_in_J (hW : ∀ w : W, w ^ 2 = 1) {A : Subgroup (MulAut W)} {t : MulAut W}
    (ht : InducesTransvection t ⊤) (htA : s15Normalizes t A) (hF : Fstar A = A)
    (hO : s15TwoCoreTrivial A) (htB : t ∈ ⁅A, Subgroup.zpowers t⁆) :
    ∀ a ∈ A, ∃ e ∈ ⁅A, Subgroup.zpowers t⁆, a⁻¹ * t * a = e⁻¹ * t * e := by
  obtain ⟨hBA, hBnA, hFB, hOB⟩ := s15_Three_B_facts_basic htA hF hO
  have ht2 : t * t = 1 := s15_Three_sq_eq_one hW ht
  have htlayer : (⟨t, htB⟩ : ↥(⁅A, Subgroup.zpowers t⁆)) ∈
      CFSG.layer ↥(⁅A, Subgroup.zpowers t⁆) :=
    s15_Three_involution_mem_layer hFB hOB htB ht2
  have htmap : t ∈ (CFSG.layer ↥(⁅A, Subgroup.zpowers t⁆)).map
      (⁅A, Subgroup.zpowers t⁆).subtype :=
    Subgroup.mem_map.mpr ⟨⟨t, htB⟩, htlayer, rfl⟩
  intro a ha
  obtain ⟨c, hcA, e, heLayer, hcent, haeq⟩ :=
    s15_Three_eq_cent_mul_layer hBA hBnA hF a ha
  have heB : e ∈ ⁅A, Subgroup.zpowers t⁆ :=
    Subgroup.map_subtype_le (CFSG.layer ↥(⁅A, Subgroup.zpowers t⁆)) heLayer
  have hct : c * t = t * c := hcent t htmap
  have hct' : c⁻¹ * t * c = t := by
    calc c⁻¹ * t * c = c⁻¹ * (t * c) := by rw [mul_assoc]
      _ = c⁻¹ * (c * t) := by rw [hct.symm]
      _ = t := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  refine ⟨e, heB, ?_⟩
  rw [haeq]
  calc (c * e)⁻¹ * t * (c * e) = e⁻¹ * (c⁻¹ * t * c) * e := by group
    _ = e⁻¹ * t * e := by rw [hct']

end Abstract

section Splitting

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem s15_Three_proj_exists {J K J₁ : Subgroup Γ} (hKJ : K ≤ J)
    (hKn : (K.subgroupOf J).Normal) (hJ₁ : J₁ ≤ J) (hdisj : J₁ ⊓ K = ⊥) (hsup : J₁ ⊔ K = J) :
    ∃ p : ↥J →* ↥J₁, (∀ x : ↥J₁, p ⟨x, hJ₁ x.2⟩ = x) ∧
      ∀ y : ↥J, (y : Γ) ∈ K → p y = 1 := by
  let N : Subgroup ↥J := K.subgroupOf J
  haveI : N.Normal := hKn
  let H : Subgroup ↥J := J₁.subgroupOf J
  let f : H →* ↥J ⧸ N := (QuotientGroup.mk' N).comp H.subtype
  have hHN : H ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : (z : Γ) ∈ J₁ ⊓ K := ⟨hz.1, hz.2⟩
    rw [hdisj] at h1
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp h1))
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have hxy' : f (x⁻¹ * y) = 1 := by
      rw [map_mul, map_inv, hxy, inv_mul_cancel]
    have hmemN : ((x⁻¹ * y : H) : ↥J) ∈ N := by
      have h := hxy'
      change QuotientGroup.mk' N ((x⁻¹ * y : H) : ↥J) = 1 at h
      exact (QuotientGroup.eq_one_iff _).mp h
    have hmemH : ((x⁻¹ * y : H) : ↥J) ∈ H := H.mul_mem (H.inv_mem x.2) y.2
    have hbot : ((x⁻¹ * y : H) : ↥J) ∈ H ⊓ N := ⟨hmemH, hmemN⟩
    rw [hHN, Subgroup.mem_bot] at hbot
    have hbotH : x⁻¹ * y = 1 := Subtype.val_injective hbot
    exact inv_mul_eq_one.mp hbotH
  have hf_surj : Function.Surjective f := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N q
    have htop : H ⊔ N = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hJ₁ hKJ, hsup, Subgroup.subgroupOf_self]
    have hymul : y ∈ (H : Set ↥J) * (N : Set ↥J) := by
      rw [← Subgroup.mul_normal H N, htop]
      trivial
    obtain ⟨h, hh, n, hn, hhn⟩ := Set.mem_mul.mp hymul
    refine ⟨⟨h, hh⟩, ?_⟩
    change QuotientGroup.mk' N h = QuotientGroup.mk' N y
    rw [QuotientGroup.mk'_eq_mk']
    exact ⟨n, hn, hhn⟩
  let e : H ≃* (↥J ⧸ N) := MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  let e₁ : H ≃* ↥J₁ := Subgroup.subgroupOfEquivOfLe hJ₁
  refine ⟨e₁.toMonoidHom.comp (e.symm.toMonoidHom.comp (QuotientGroup.mk' N)), ?_, ?_⟩
  · intro x
    change e₁ (e.symm (QuotientGroup.mk' N ⟨x, hJ₁ x.2⟩)) = x
    have hx1 : QuotientGroup.mk' N ⟨x, hJ₁ x.2⟩ = f (e₁.symm x) := by
      change QuotientGroup.mk' N ⟨x, hJ₁ x.2⟩ =
        QuotientGroup.mk' N ((e₁.symm x : H) : ↥J)
      rw [show ((e₁.symm x : H) : ↥J) = ⟨x, hJ₁ x.2⟩ from rfl]
    have hx : e.symm (QuotientGroup.mk' N ⟨x, hJ₁ x.2⟩) = e₁.symm x := by
      rw [hx1]
      exact e.symm_apply_apply (e₁.symm x)
    rw [hx, e₁.apply_symm_apply]
  · intro y hy
    change e₁ (e.symm (QuotientGroup.mk' N y)) = 1
    have hyN : y ∈ N := hy
    have h1 : QuotientGroup.mk' N y = 1 := (QuotientGroup.eq_one_iff _).mpr hyN
    rw [h1, map_one, map_one]

theorem s15_Three_quot_group {J B K J₁ : Subgroup Γ} (hBJ : B ≤ J)
    (hBn : (B.subgroupOf J).Normal) (hidx : (B.subgroupOf J).index ≤ 2) (hKJ : K ≤ J)
    (hKn : (K.subgroupOf J).Normal) (hJ₁ : J₁ ≤ J) (hdisj : J₁ ⊓ K = ⊥) (hsup : J₁ ⊔ K = J)
    {τ b : Γ} (hτ : τ ∈ J₁) (hτB : τ ∉ B) (hb : b ∈ B) (hbτ : ∃ k ∈ K, b = k * τ)
    (hno2 : ∀ N : Subgroup ↥B, N.Normal → (∃ n : ℕ, N.index = 2 ^ n) → N = ⊤) : False := by
  obtain ⟨p, hp₁, hpK⟩ := s15_Three_proj_exists hKJ hKn hJ₁ hdisj hsup
  let N : Subgroup ↥J := B.subgroupOf J
  haveI : N.Normal := hBn
  let Q := ↥J ⧸ N
  let φ : ↥B →* Q :=
    (QuotientGroup.mk' N).comp ((Subgroup.inclusion hJ₁).comp (p.comp (Subgroup.inclusion hBJ)))
  have hNφn : φ.ker.Normal := inferInstance
  have hQcard : Nat.card Q ≤ 2 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  have hQpos : 0 < Nat.card Q := by
    rw [← Subgroup.index_eq_card]
    exact Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have hle : φ.ker.index ≤ 2 := by
    rw [Subgroup.index_ker]
    exact (Nat.le_of_dvd hQpos (Subgroup.card_subgroup_dvd_card φ.range)).trans hQcard
  have hex : ∃ n : ℕ, φ.ker.index = 2 ^ n := by
    have hpos : 0 < φ.ker.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    have : φ.ker.index = 1 ∨ φ.ker.index = 2 := by omega
    rcases this with h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
  obtain ⟨k, hkK, hbk⟩ := hbτ
  have hkJ : k ∈ J := hKJ hkK
  have hτJ : τ ∈ J := hJ₁ hτ
  have hbJ : (⟨b, hBJ hb⟩ : ↥J) = (⟨k, hkJ⟩ : ↥J) * (⟨τ, hτJ⟩ : ↥J) := by
    apply Subtype.ext
    exact hbk
  have hp : p ⟨b, hBJ hb⟩ = (⟨τ, hτ⟩ : ↥J₁) := by
    rw [hbJ, map_mul, hpK ⟨k, hkJ⟩ hkK, one_mul]
    exact hp₁ ⟨τ, hτ⟩
  have hφb : φ ⟨b, hb⟩ = QuotientGroup.mk' N ⟨τ, hτJ⟩ := by
    change QuotientGroup.mk' N (Subgroup.inclusion hJ₁
      (p (Subgroup.inclusion hBJ ⟨b, hb⟩))) = QuotientGroup.mk' N ⟨τ, hτJ⟩
    rw [show (Subgroup.inclusion hBJ ⟨b, hb⟩ : ↥J) = ⟨b, hBJ hb⟩ from rfl, hp]
    rfl
  have hker : (⟨b, hb⟩ : ↥B) ∈ φ.ker := by
    rw [hno2 φ.ker hNφn hex]
    exact Subgroup.mem_top _
  have hτN : (⟨τ, hτJ⟩ : ↥J) ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    exact hφb.symm.trans (MonoidHom.mem_ker.mp hker)
  exact hτB hτN

end Splitting

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
