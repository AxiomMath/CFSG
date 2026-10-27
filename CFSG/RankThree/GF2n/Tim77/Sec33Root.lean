module

public import CFSG.RankThree.GF2n.Tim77.Sec33Pair
public import CFSG.RankThree.GF2n.Tim77.Sec33Quot

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld.RootInvolutions Subgroup
open CFSG.GH74.Uniqueness.Bender CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

section Certified3


theorem sec33_root_types [Finite G] {A Abar S₀ B : Subgroup G} {s : G}
    (hC : Sec3Ctx A Abar S₀ B) (hs : Section3.IsSChoice A Abar S₀ B s)
    (hq : 2 < Section3.q A Abar)
    [hNn : ((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)).Normal] {n i : ℕ}
    (hi : i = 1 ∨ i = 2)
    (hK : BenderType ((↥(Section3.Y A Abar s) ⧸
        (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) ⧸
        Subgroup.center (↥(Section3.Y A Abar s) ⧸
          (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s))) n i 1)
    {y : G} (hy : y ∈ Section3.Y A Abar s)
    (hcomm : ∀ x ∈ A, ∀ w ∈ conjSubgroup y A, x * w = w * x) :
    ∀ b ∈ conjSubgroup y A, ∃ a ∈ A, ∀ z ∈ Section3.Y A Abar s,
      (b * a⁻¹) * z * (b * a⁻¹)⁻¹ * z⁻¹ ∈ Section3.N A Abar s := by
  classical
  obtain ⟨hNY, hYN, hNab⟩ := tim77Sec32a_holds G A Abar S₀ B s hC hs
  have hNc : ∀ x ∈ Section3.N A Abar s, ∀ w ∈ Section3.N A Abar s, x * w = w * x :=
    fun x hx w hw => congrArg Subtype.val (hNab.1.is_comm.comm ⟨x, hx⟩ ⟨w, hw⟩)
  have hAY : A ≤ Section3.Y A Abar s := sec32d_A_le_Y
  have hAbY : Abar ≤ Section3.Y A Abar s := sec32d_Abar_le_Y
  have hq' : 2 < (Section3.A0 A Abar).relIndex A := by
    have h1 := hC.setup.relIndex_Lb
    unfold Section3.q at hq
    rw [h1] at hq
    exact hq
  set Y := Section3.Y A Abar s with hYdef
  set N := Section3.N A Abar s with hNdef
  set Q := ↥Y ⧸ N.subgroupOf Y with hQdef
  let π : ↥Y →* Q ⧸ Subgroup.center Q :=
    (QuotientGroup.mk' (Subgroup.center Q)).comp (QuotientGroup.mk' (N.subgroupOf Y))
  have hπ1 : ∀ z : ↥Y, π z = 1 ↔ (QuotientGroup.mk z : Q) ∈ Subgroup.center Q :=
    fun z => QuotientGroup.eq_one_iff _
  have hπN : ∀ (m : G) (hm : m ∈ Y), m ∈ N → π ⟨m, hm⟩ = 1 := by
    intro m hm hmN
    have h1 : (QuotientGroup.mk ⟨m, hm⟩ : Q) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hmN)
    rw [hπ1, h1]
    exact Subgroup.one_mem _
  have hcen := sec33_mem_center_iff (Y := Y) (N := N) hYN
  have hnotc : ∀ (a : G) (ha : a ∈ A), a ∉ Section3.A0 A Abar → π ⟨a, hAY ha⟩ ≠ 1 :=
    fun a ha haL h1 => sec33_not_central hC hs ha haL ((hπ1 _).mp h1)
  obtain ⟨x₁, hx₁X, hx₁⟩ := hC.setup.exists_conj_eq
  have hx₁Y : x₁ ∈ Y := (sup_le hAY hAbY) hx₁X
  have hconjY : ∀ g ∈ Y, conjSubgroup g A ≤ Y := by
    intro g hg w hw
    obtain ⟨a, ha, rfl⟩ := (mem_conjSubgroup_exists_t77 g A w).1 hw
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (hAY ha)) (Subgroup.inv_mem _ hg)
  have hAyY : conjSubgroup y A ≤ Y := hconjY y hy
  have hAx₁Y : conjSubgroup x₁ A ≤ Y := hconjY x₁ hx₁Y
  have hsqA : ∀ a ∈ A, a * a = 1 := fun a ha => hC.setup.sq_A ha
  have hsqconj : ∀ g : G, ∀ w ∈ conjSubgroup g A, w * w = 1 := by
    intro g w hw
    obtain ⟨a, ha, rfl⟩ := (mem_conjSubgroup_exists_t77 g A w).1 hw
    rw [show g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ by group, hsqA a ha]
    group
  have hπsq : ∀ (g : G) (hg : g ∈ Y), g * g = 1 → π ⟨g, hg⟩ * π ⟨g, hg⟩ = 1 := by
    intro g hg h1
    rw [← map_mul]
    have : (⟨g, hg⟩ : ↥Y) * ⟨g, hg⟩ = 1 := Subtype.ext (by simpa using h1)
    rw [this, map_one]
  have mem_img : ∀ {H : Subgroup G} (hH : H ≤ Y) {k : Q ⧸ Subgroup.center Q},
      k ∈ (H.subgroupOf Y).map π ↔ ∃ (g : G) (hg : g ∈ H), π ⟨g, hH hg⟩ = k := by
    intro H hH k
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hH hg⟩, hg, rfl⟩
  have hmain : (((conjSubgroup y A).subgroupOf Y).map π) ≤ (A.subgroupOf Y).map π := by
    set T := (A.subgroupOf Y).map π with hT
    set Tbar := (Abar.subgroupOf Y).map π with hTbar
    set T₁ := ((conjSubgroup y A).subgroupOf Y).map π with hT₁
    have hTsq : ∀ t ∈ T, t * t = 1 := by
      intro t ht
      obtain ⟨a, ha, rfl⟩ := (mem_img hAY).mp ht
      exact hπsq a (hAY ha) (hsqA a ha)
    have hTbarsq : ∀ x ∈ Tbar, x * x = 1 := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := (mem_img hAbY).mp hx
      exact hπsq a (hAbY ha) (hC.setup.sq_Ab ha)
    have hT₁sq : ∀ x ∈ T₁, x * x = 1 := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := (mem_img hAyY).mp hx
      exact hπsq a (hAyY ha) (hsqconj y a ha)
    obtain ⟨a₀, ha₀A, ha₀L⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hC.setup.L_le hC.a0_ne)
    have hψA : ∃ (a₀ : G) (h : a₀ ∈ A), π ⟨a₀, hAY h⟩ ≠ 1 :=
      ⟨a₀, ha₀A, hnotc a₀ ha₀A ha₀L⟩
    have hTne : T ≠ ⊥ := by
      intro hbot
      apply hnotc a₀ ha₀A ha₀L
      have : π ⟨a₀, hAY ha₀A⟩ ∈ T := (mem_img hAY).mpr ⟨a₀, ha₀A, rfl⟩
      rw [hbot] at this
      exact Subgroup.mem_bot.mp this
    have hconjne : ∀ g : G, ∀ hg : g ∈ Y, π ⟨g * a₀ * g⁻¹, Subgroup.mul_mem _
        (Subgroup.mul_mem _ hg (hAY ha₀A)) (Subgroup.inv_mem _ hg)⟩ ≠ 1 := by
      intro g hg h1
      apply hnotc a₀ ha₀A ha₀L
      have e : (⟨g * a₀ * g⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (hAY ha₀A))
          (Subgroup.inv_mem _ hg)⟩ : ↥Y) = ⟨g, hg⟩ * ⟨a₀, hAY ha₀A⟩ * ⟨g, hg⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv] at h1
      have h2 : π ⟨a₀, hAY ha₀A⟩ = (π ⟨g, hg⟩)⁻¹ * 1 * π ⟨g, hg⟩ := by
        rw [← h1]; group
      rw [h2]
      group
    have hAbar_a₀ : x₁ * a₀ * x₁⁻¹ ∈ Abar := by
      rw [hx₁]
      exact (mem_conjSubgroup_conj_t77 x₁ a₀ A).2 ha₀A
    have hTbne : Tbar ≠ ⊥ := by
      intro hbot
      apply hconjne x₁ hx₁Y
      have : π ⟨x₁ * a₀ * x₁⁻¹, hAbY hAbar_a₀⟩ ∈ Tbar := (mem_img hAbY).mpr ⟨_, hAbar_a₀, rfl⟩
      rw [hbot] at this
      exact Subgroup.mem_bot.mp this
    have hMN : Section3.M A Abar ≤ N := by
      rw [hC.m_eq]
      exact sup_le sec33_A0_le_N sec33_Abar0_le_N
    have hψM : ∀ (m : G) (hm : m ∈ Section3.M A Abar),
        π ⟨m, (hC.setup.M_le_X.trans (sup_le hAY hAbY)) hm⟩ = 1 :=
      fun m hm => hπN m _ (hMN hm)
    have h4 : ∀ x ∈ Tbar, x ≠ 1 → ∃ a ∈ T, a ≠ 1 ∧ a ≠ x ∧ (a * x) ^ (2 * i + 1) = 1 := by
      intro x hx hx1
      obtain ⟨g, hg, rfl⟩ := (mem_img hAbY).mp hx
      obtain ⟨a, ha, h1, h2, h3⟩ :=
        sec33_pair_partner hC.setup hq' hAY hAbY hK hi π hψM hψA g hg hx1
      exact ⟨π ⟨a, hAY ha⟩, (mem_img hAY).mpr ⟨a, ha, rfl⟩, h1, h2, h3⟩
    have hnc_TT : ∃ t ∈ T, ∃ x ∈ Tbar, t * x ≠ x * t := by
      obtain ⟨⟨x, hx⟩, hx1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hTbne
      have hx1 : x ≠ 1 := fun h' => hx1' (Subtype.ext h')
      obtain ⟨a, haT, ha1, hax, hapow⟩ := h4 x hx hx1
      refine ⟨a, haT, x, hx, fun hcomm => hax ?_⟩
      have hsq : (a * x) * (a * x) = 1 :=
        sec33_mul_sq_of_comm_invol (hTsq a haT) (hTbarsq x hx) hcomm
      have h1 := sec33_eq_one_of_sq_of_pow hsq (odd_two_mul_add_one i) hapow
      have : a = x⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact inv_eq_of_mul_eq_one_right (hTbarsq x hx)
    have hcomm' : ∀ b ∈ T₁, ∀ t ∈ T, b * t = t * b := by
      intro b hb t ht
      obtain ⟨w, hw, rfl⟩ := (mem_img hAyY).mp hb
      obtain ⟨a, ha, rfl⟩ := (mem_img hAY).mp ht
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcomm a ha w hw).symm
    by_cases hnc : ∀ x ∈ conjSubgroup y A, ∀ w ∈ Abar, x * w = w * x
    · intro b hb
      have : b = 1 := by
        obtain ⟨w, hw, rfl⟩ := (mem_img hAyY).mp hb
        refine sec33_bender_centralizer_bot hK hTsq hTbarsq hTne hTbne hnc_TT (hT₁sq _ hb) ?_ ?_
        · exact fun t ht => hcomm' _ hb t ht
        · intro x hx
          obtain ⟨a, ha, rfl⟩ := (mem_img hAbY).mp hx
          rw [← map_mul, ← map_mul]
          congr 1
          exact Subtype.ext (hnc w hw a ha)
      rw [this]
      exact T.one_mem
    · have hnc' : ¬ ∀ x ∈ conjSubgroup y A, ∀ w ∈ conjSubgroup x₁ A, x * w = w * x := by
        rw [← hx₁]; exact hnc
      have S₂ := sec41_prop24 hC hYN hNc hy hx₁Y hnc'
      have hq₂ : 2 < (conjSubgroup x₁ (Section3.A0 A Abar)).relIndex (conjSubgroup x₁ A) := by
        unfold conjSubgroup
        rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj x₁).injective]
        exact hq'
      have hconjN : ∀ g ∈ Y, conjSubgroup g (Section3.A0 A Abar) ≤ N := by
        intro g hg w hw
        obtain ⟨a, ha, rfl⟩ := (mem_conjSubgroup_exists_t77 g _ w).1 hw
        exact (Subgroup.mem_normalizer_iff.mp (hYN g hg) a).mp (sec33_A0_le_N ha)
      have hψM₂ : ∀ (m : G) (hm : m ∈ conjSubgroup y (Section3.A0 A Abar) ⊔
          conjSubgroup x₁ (Section3.A0 A Abar)),
          π ⟨m, (S₂.symm.M_le_X.trans (sup_le hAx₁Y hAyY)) hm⟩ = 1 := fun m hm =>
        hπN m _ ((sup_le (hconjN y hy) (hconjN x₁ hx₁Y)) hm)
      have hψA₂ : ∃ (c : G) (h : c ∈ conjSubgroup x₁ A), π ⟨c, hAx₁Y h⟩ ≠ 1 :=
        ⟨x₁ * a₀ * x₁⁻¹, (mem_conjSubgroup_conj_t77 x₁ a₀ A).2 ha₀A, hconjne x₁ hx₁Y⟩
      have h5 : ∀ b ∈ T₁, b ≠ 1 → ∃ x ∈ Tbar, x ≠ 1 ∧ x ≠ b ∧ (x * b) ^ (2 * i + 1) = 1 := by
        intro b hb hb1
        obtain ⟨w, hw, rfl⟩ := (mem_img hAyY).mp hb
        obtain ⟨a, ha, h1, h2, h3⟩ :=
          sec33_pair_partner S₂.symm hq₂ hAx₁Y hAyY hK hi π hψM₂ hψA₂ w hw hb1
        have haAbar : a ∈ Abar := by rw [hx₁]; exact ha
        exact ⟨π ⟨a, hAx₁Y ha⟩, (mem_img hAbY).mpr ⟨a, haAbar, rfl⟩, h1, h2, h3⟩
      exact sec33_bender_root_le hK hi hTsq hTbarsq hT₁sq hTne hcomm' h4 h5
  intro b hb
  have hbY : b ∈ Y := hAyY hb
  obtain ⟨a, ha, hab⟩ := (mem_img hAY).mp (hmain ((mem_img hAyY).mpr ⟨b, hb, rfl⟩))
  refine ⟨a, ha, ?_⟩
  have h1 : π ⟨b * a⁻¹, Subgroup.mul_mem _ hbY (Subgroup.inv_mem _ (hAY ha))⟩ = 1 := by
    have : (⟨b * a⁻¹, Subgroup.mul_mem _ hbY (Subgroup.inv_mem _ (hAY ha))⟩ : ↥Y) =
        ⟨b, hbY⟩ * ⟨a, hAY ha⟩⁻¹ := rfl
    rw [this, map_mul, map_inv, hab, mul_inv_cancel]
  exact (hcen _).mp ((hπ1 _).mp h1)

theorem sec33_type3_false [Finite G] {A Abar S₀ B : Subgroup G} {s : G}
    (hC : Sec3Ctx A Abar S₀ B) (hs : Section3.IsSChoice A Abar S₀ B s)
    [hNn : ((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)).Normal] {n e : ℕ}
    (hK : BenderType ((↥(Section3.Y A Abar s) ⧸
        (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) ⧸
        Subgroup.center (↥(Section3.Y A Abar s) ⧸
          (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s))) n 3 e)
    (hsY : s ∈ normalizer (Section3.Y A Abar s : Set G))
    (hsN : s ∈ normalizer (Section3.N A Abar s : Set G)) {g : G}
    (hgY : g ∈ Section3.Y A Abar s)
    (h1 : ∀ a ∈ A, g * a * g⁻¹ * a⁻¹ ∈ Section3.N A Abar s)
    (h2 : ∀ y ∈ Section3.Y A Abar s, (g * g) * y * (g * g)⁻¹ * y⁻¹ ∈ Section3.N A Abar s)
    (hg : ∀ x : ↥(Section3.Y A Abar s) ⧸
        (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s),
      sec33Tau hsY hsN x = QuotientGroup.mk ⟨g, hgY⟩ * x * (QuotientGroup.mk ⟨g, hgY⟩)⁻¹) :
    False := by
  classical
  obtain ⟨hNY, hYN, hNab⟩ := tim77Sec32a_holds G A Abar S₀ B s hC hs
  have hAY : A ≤ Section3.Y A Abar s := sec32d_A_le_Y
  have hAbY : Abar ≤ Section3.Y A Abar s := sec32d_Abar_le_Y
  have hconjsY : conjSubgroup s Abar ≤ Section3.Y A Abar s := sec32d_conj_le_Y
  set Y := Section3.Y A Abar s with hYdef
  set N := Section3.N A Abar s with hNdef
  set Q := ↥Y ⧸ N.subgroupOf Y with hQdef
  let π : ↥Y →* Q ⧸ Subgroup.center Q :=
    (QuotientGroup.mk' (Subgroup.center Q)).comp (QuotientGroup.mk' (N.subgroupOf Y))
  have hπ1 : ∀ z : ↥Y, π z = 1 ↔ (QuotientGroup.mk z : Q) ∈ Subgroup.center Q :=
    fun z => QuotientGroup.eq_one_iff _
  have hcen := sec33_mem_center_iff (Y := Y) (N := N) hYN
  have hnotc : ∀ (a : G) (ha : a ∈ A), a ∉ Section3.A0 A Abar → π ⟨a, hAY ha⟩ ≠ 1 :=
    fun a ha haL h1 => sec33_not_central hC hs ha haL ((hπ1 _).mp h1)
  have hπsq : ∀ (g : G) (hg : g ∈ Y), g * g = 1 → π ⟨g, hg⟩ * π ⟨g, hg⟩ = 1 := by
    intro g hg h1
    rw [← map_mul]
    have : (⟨g, hg⟩ : ↥Y) * ⟨g, hg⟩ = 1 := Subtype.ext (by simpa using h1)
    rw [this, map_one]
  have mem_img : ∀ {H : Subgroup G} (hH : H ≤ Y) {k : Q ⧸ Subgroup.center Q},
      k ∈ (H.subgroupOf Y).map π ↔ ∃ (g : G) (hg : g ∈ H), π ⟨g, hH hg⟩ = k := by
    intro H hH k
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hH hg⟩, hg, rfl⟩
  set T := (A.subgroupOf Y).map π with hT
  set Tbar := (Abar.subgroupOf Y).map π with hTbar
  have hTsq : ∀ t ∈ T, t * t = 1 := by
    intro t ht
    obtain ⟨a, ha, rfl⟩ := (mem_img hAY).mp ht
    exact hπsq a (hAY ha) (hC.setup.sq_A ha)
  have hTbarsq : ∀ x ∈ Tbar, x * x = 1 := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := (mem_img hAbY).mp hx
    exact hπsq a (hAbY ha) (hC.setup.sq_Ab ha)
  obtain ⟨a₀, ha₀A, ha₀L⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hC.setup.L_le hC.a0_ne)
  have hTne : T ≠ ⊥ := by
    intro hbot
    apply hnotc a₀ ha₀A ha₀L
    have : π ⟨a₀, hAY ha₀A⟩ ∈ T := (mem_img hAY).mpr ⟨a₀, ha₀A, rfl⟩
    rw [hbot] at this
    exact Subgroup.mem_bot.mp this
  have hπN : ∀ (m : G) (hm : m ∈ Y), m ∈ N → π ⟨m, hm⟩ = 1 := by
    intro m hm hmN
    have h1 : (QuotientGroup.mk ⟨m, hm⟩ : Q) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hmN)
    rw [hπ1, h1]
    exact Subgroup.one_mem _
  set gb : Q ⧸ Subgroup.center Q := π ⟨g, hgY⟩ with hgb
  have hgcomm : ∀ t ∈ T, gb * t = t * gb := by
    intro t ht
    obtain ⟨a, ha, rfl⟩ := (mem_img hAY).mp ht
    have hmem : g * a * g⁻¹ * a⁻¹ ∈ Y := Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ hgY (hAY ha)) (Subgroup.inv_mem _ hgY)) (Subgroup.inv_mem _ (hAY ha))
    have h3 := hπN _ hmem (h1 a ha)
    have e : (⟨g * a * g⁻¹ * a⁻¹, hmem⟩ : ↥Y) =
        ⟨g, hgY⟩ * ⟨a, hAY ha⟩ * ⟨g, hgY⟩⁻¹ * ⟨a, hAY ha⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h3
    calc gb * π ⟨a, hAY ha⟩
        = (gb * π ⟨a, hAY ha⟩ * gb⁻¹ * (π ⟨a, hAY ha⟩)⁻¹) * (π ⟨a, hAY ha⟩ * gb) := by group
      _ = π ⟨a, hAY ha⟩ * gb := by rw [hgb, h3, one_mul]
  have hgg : gb * gb = 1 := by
    have hmem : g * g ∈ Y := Subgroup.mul_mem _ hgY hgY
    have h3 := (hπ1 ⟨g * g, hmem⟩).mpr ((hcen ⟨g * g, hmem⟩).mpr h2)
    have e : (⟨g * g, hmem⟩ : ↥Y) = ⟨g, hgY⟩ * ⟨g, hgY⟩ := rfl
    rw [e, map_mul] at h3
    exact h3
  have hπs : ∀ (u : G) (hu : u ∈ Abar),
      π ⟨s * u * s⁻¹, hconjsY ((mem_conjSubgroup_conj_t77 s u Abar).2 hu)⟩ =
        gb * π ⟨u, hAbY hu⟩ * gb⁻¹ := by
    intro u hu
    have h3 := hg (QuotientGroup.mk ⟨u, hAbY hu⟩)
    rw [sec33Tau_mk] at h3
    have h4 := congrArg (QuotientGroup.mk' (Subgroup.center Q)) h3
    simp only [map_mul, map_inv] at h4
    exact h4
  obtain ⟨S, hTS, hgS⟩ := sec33_exists_sylow_centralizes hK hTsq hTne hgg hgcomm
  obtain ⟨S', hTbS'⟩ := (isPGroup_two_of_sq_eq_one hTbarsq).exists_le_sylow
  obtain ⟨tS', hcS'⟩ := hK.exists_benderCore S'
  have hTbR : Tbar ≤ rootCenter (S' : Subgroup (Q ⧸ Subgroup.center Q)) := fun t ht =>
    hcS'.mem_rootCenter_of_mul_self (hTbS' ht) (hTbarsq t ht)
  have hπsurj : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have htop : (⊤ : Subgroup (Q ⧸ Subgroup.center Q)) ≤ T ⊔ Tbar ⊔ conjSubgroup gb Tbar := by
    have hY' : (A ⊔ Abar) ⊔ conjSubgroup s Abar = Y := rfl
    have h1 : ((A ⊔ Abar) ⊔ conjSubgroup s Abar).subgroupOf Y = ⊤ := by
      rw [hY']; exact Subgroup.subgroupOf_self Y
    rw [Subgroup.subgroupOf_sup (sup_le hAY hAbY) hconjsY,
      Subgroup.subgroupOf_sup hAY hAbY] at h1
    have h2 := congrArg (Subgroup.map π) h1
    rw [Subgroup.map_top_of_surjective _ hπsurj, Subgroup.map_sup, Subgroup.map_sup] at h2
    rw [← h2]
    refine sup_le_sup_left ?_ _
    rintro k ⟨z, hz, rfl⟩
    have hz' : (z : G) ∈ conjSubgroup s Abar := hz
    obtain ⟨u, hu, hzu⟩ := (mem_conjSubgroup_exists_t77 s Abar (z : G)).1 hz'
    have hzeq : z = ⟨s * u * s⁻¹, hconjsY ((mem_conjSubgroup_conj_t77 s u Abar).2 hu)⟩ :=
      Subtype.ext hzu.symm
    rw [hzeq, hπs u hu]
    rw [mem_conjSubgroup]
    have : gb⁻¹ * (gb * π ⟨u, hAbY hu⟩ * gb⁻¹) * gb = π ⟨u, hAbY hu⟩ := by group
    rw [this]
    exact (mem_img hAbY).mpr ⟨u, hu, rfl⟩
  by_cases hSS : S = S'
  · subst hSS
    apply hK.isSimpleBenderGroup.not_commutative
    intro x y
    have hconjR : conjSubgroup gb Tbar ≤ rootCenter (S : Subgroup (Q ⧸ Subgroup.center Q)) := by
      intro z hz
      rw [mem_conjSubgroup] at hz
      have h5 := conj_mem_rootCenter (le_borel _ (rootCenter_le _ hgS)) (hTbR hz)
      have e : gb * (gb⁻¹ * z * gb) * gb⁻¹ = z := by group
      rw [e] at h5
      exact h5
    have hall : (⊤ : Subgroup (Q ⧸ Subgroup.center Q)) ≤
        rootCenter (S : Subgroup (Q ⧸ Subgroup.center Q)) :=
      htop.trans (sup_le (sup_le hTS hTbR) hconjR)
    have hx : x ∈ rootCenter (S : Subgroup (Q ⧸ Subgroup.center Q)) := hall trivial
    have hy : y ∈ rootCenter (S : Subgroup (Q ⧸ Subgroup.center Q)) := hall trivial
    exact ((mem_rootCenter_iff.mp hx).2 y (rootCenter_le _ hy)).symm
  · exact sec33_bender_type3_ne_top hK hSS hTS hTbR hTne hgS (top_le_iff.mp htop)

end Certified3

end CFSG.RankThree.GF2n.Tim77
