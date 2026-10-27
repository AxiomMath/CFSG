module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenUniqueMax

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s15_FiveTen_isTI_of_uniqueMax (D : Data G) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : D.M ≤ normalizer (V : Set G))
    (hU : ∀ w ∈ V, w ≠ 1 → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))) :
    CFSG.CGT.Timmesfeld75.IsTI V := by
  intro g
  by_cases hg : g⁻¹ ∈ D.M
  · right
    have hgn : g⁻¹ ∈ normalizer (V : Set G) := hM hg
    have : CFSG.CGT.Timmesfeld75.conjSubgroup g V = V := by
      ext x
      rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
      have h1 := Subgroup.mem_normalizer_iff.1 hgn x
      simpa [inv_inv] using h1.symm
    rw [this, inf_idem]
  · left
    have hbot := inf_conjSubgroup_eq_bot_of_uniqueMax D.maxLocal hV.isPGroup hV.isPGroup hU hU hg
    have : CFSG.CGT.Timmesfeld75.conjSubgroup g V = conjSubgroup V g⁻¹ := by
      ext x
      rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup, mem_conjSubgroup_iff, inv_inv]
    rw [this]
    exact hbot

theorem fifteen_five (D : Data G) (h129 : R129_1 D) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) :
    1 < s15 D.M V₀ V hV L := by
  have h151 := h.hyp151
  have hWmem : wSub V₀ V hV L ∈ wConj D.M V₀ V hV L :=
    ⟨1, D.M.one_mem, by simp [conjSubgroup_one]⟩
  have hcard := ncard_wConj D h151 hV
  have hpos : 0 < s15 D.M V₀ V hV L := by
    rw [← hcard]
    exact (Set.ncard_pos (Set.toFinite _)).2 ⟨_, hWmem⟩
  by_contra hs
  have hs1 : s15 D.M V₀ V hV L = 1 := by omega
  obtain ⟨X, hX⟩ := Set.ncard_eq_one.1 (hcard.trans hs1)
  have hXW : X = wSub V₀ V hV L := by
    rw [hX] at hWmem
    exact (Set.mem_singleton_iff.1 hWmem).symm
  have hVW : wSub V₀ V hV L = V := by
    have := iSup_wConj_eq D h1217 h151 hV hL
    rw [hX, hXW] at this
    simpa using this
  have hU : ∀ w ∈ V, w ≠ 1 → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
    intro w hw hw1
    have hwW : w ∈ wSub V₀ V hV L := hVW.symm ▸ hw
    exact h.unique₁ w (Subgroup.mem_sup_left hwW) hw1
  exact h129 V₀ V h151.hyp125
    (s15_FiveTen_isTI_of_uniqueMax D hV h151.hyp125.pairFacts.le_normalizer hU)

theorem s15_FiveTen_mQuot_bot_eq_rk (X : Subgroup G) : E3.mQuot X ⊥ = rk ↥X := by
  unfold E3.mQuot rk
  rw [Subgroup.relIndex_bot_left]

theorem s15_FiveTen_mQuot_wSub_sup_v1Sub (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp125 D V₀ V) (hV : IsElemAbelian 2 V) :
    E3.mQuot (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) (v1Sub D.M V₀ V hV L) =
      gamma15 D.M V₀ V hV L := by
  have h1 := mSub_wSub_sup_v1Sub D h hV (L := L)
  have h2 := E3.mQuot_add (V := wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L)
    (bot_le : (⊥ : Subgroup G) ≤ v1Sub D.M V₀ V hV L) le_sup_right
  rw [s15_FiveTen_mQuot_bot_eq_rk, s15_FiveTen_mQuot_bot_eq_rk] at h2
  have h3 : mSub (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) =
      rk ↥(wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) := rfl
  have h4 : mSub (v1Sub D.M V₀ V hV L) = rk ↥(v1Sub D.M V₀ V hV L) := rfl
  omega

theorem s15_FiveTen_mQuot_conj_v1Sub (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp125 D V₀ V) (hV : IsElemAbelian 2 V) (g : G) :
    E3.mQuot (conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g)
      (conjSubgroup (v1Sub D.M V₀ V hV L) g) = gamma15 D.M V₀ V hV L := by
  rw [E3.mQuot_conjSubgroup]
  exact s15_FiveTen_mQuot_wSub_sup_v1Sub D h hV

theorem s15_FiveTen_mQuot_conj_bot (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp125 D V₀ V) (hV : IsElemAbelian 2 V) (g : G) :
    E3.mQuot (conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g) ⊥ =
      E3.mQuot (v1Sub D.M V₀ V hV L) ⊥ + gamma15 D.M V₀ V hV L := by
  have h1 := E3.mQuot_add (V := conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g)
    (bot_le : (⊥ : Subgroup G) ≤ conjSubgroup (v1Sub D.M V₀ V hV L) g)
    (E3.conjSubgroup_mono_left g (le_sup_right : v1Sub D.M V₀ V hV L ≤
      wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L))
  have h2 := E3.mQuot_conjSubgroup (v1Sub D.M V₀ V hV L) ⊥ g
  rw [E3.conjSubgroup_bot] at h2
  rw [h1, s15_FiveTen_mQuot_conj_v1Sub D h hV g, h2]

theorem centralizer_le_normalizer_of_mQuot_lt (D : Data G)
    {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) {g : G}
    {A R : Subgroup G} (hA : A = conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g)
    (hRA : R ≤ A) (hR : E3.mQuot A R < gamma15 D.M V₀ V hV L) :
    R ≠ ⊥ ∧ centralizer (R : Set G) ≤ conjSubgroup D.M g ⊓ normalizer (A : Set G) := by
  have h151 := h.hyp151
  have hγ := s15_FiveTen_mQuot_conj_v1Sub D h151.hyp125 hV (L := L) g
  rw [← hA] at hγ
  have hRbot : R ≠ ⊥ := by
    intro hbot
    subst hbot
    have := E3.mQuot_mono (V := A) (U := ⊥)
      (U' := conjSubgroup (v1Sub D.M V₀ V hV L) g) bot_le
    omega
  refine ⟨hRbot, fun x hx => ?_⟩
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hRbot
  have haA : (a : G) ∈ conjSubgroup
      (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g := hA ▸ hRA a.2
  have ha1' : (a : G) ≠ 1 := fun h1 => ha1 (Subtype.ext h1)
  have hWV : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤ V :=
    sup_le (preTil_le V₀ V hV _) (s15_Infra_v1Sub_le h151.hyp125 hV)
  have ha2 : ∃ n : ℕ, (a : G) ^ (2 ^ n) = 1 := by
    refine ⟨1, ?_⟩
    have := (E3.isElemAbelian_conjSubgroup hV g).2 (a : G)
      (E3.conjSubgroup_mono_left g hWV haA)
    simpa using this
  have hu := uniqueMax_conjSubgroup_of_mem (g := g) h.unique₁ haA ha1'
  have hK : rankThreeIsMaxTwoLocal (conjSubgroup D.M g) :=
    UC6.isMaxTwoLocal_conj (show IsMaxTwoLocalSubgroup D.M from D.maxLocal) g
  have hxa : (x : G) ∈ centralizer ({(a : G)} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.1 hx a a.2).symm
  have hxM : x ∈ conjSubgroup D.M g := (centralizer_le_of_uniqueMax hK ha1' ha2 hu).1 hxa
  refine Subgroup.mem_inf.2 ⟨hxM, ?_⟩
  by_contra hxN
  have hy : g * x * g⁻¹ ∈ D.M := mem_conjSubgroup_iff.1 hxM
  have hyn : g * x * g⁻¹ ∉ nBar D.M V₀ V hV L := by
    intro hyn
    apply hxN
    have hyN : g * x * g⁻¹ ∈ normalizer
        ((wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L : Subgroup G) : Set G) := by
      rw [← inf_normalizer_wSub_sup_v1Sub_eq_nBar D h151 hV] at hyn
      exact (Subgroup.mem_inf.1 hyn).2
    rw [hA, ← E3.conjSubgroup_normalizer]
    exact mem_conjSubgroup_iff.2 hyN
  have hRV1 : R ≤ conjSubgroup (v1Sub D.M V₀ V hV L) g := by
    intro r hr
    rw [mem_conjSubgroup_iff]
    have hrA : r ∈ conjSubgroup
        (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g := hA ▸ hRA hr
    have hw : g * r * g⁻¹ ∈ wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L :=
      mem_conjSubgroup_iff.1 hrA
    refine mem_v1Sub_of_commutator_mem D h151 hV hy hyn hw ?_
    have hcomm : r * x = x * r := Subgroup.mem_centralizer_iff.1 hx r hr
    have h1 : g * x * g⁻¹ * (g * r * g⁻¹) * (g * x * g⁻¹)⁻¹ *
        (g * r * g⁻¹)⁻¹ = 1 := by
      calc _ = g * (x * r * x⁻¹ * r⁻¹) * g⁻¹ := by group
        _ = 1 := by rw [← hcomm]; group
    rw [h1]
    exact one_mem _
  have := E3.mQuot_mono (V := A) hRV1
  omega

theorem s15_FiveTen_mQuot_inf_centralizer_le {E V₁ : Subgroup G} {v : G} (hE : IsPGroup 2 E)
    (hV₁ : IsPGroup 2 V₁) (h : ∀ e ∈ E, v⁻¹ * (e⁻¹ * v * e) ∈ V₁) :
    E3.mQuot E (E ⊓ centralizer ({v} : Set G)) ≤ E3.mQuot V₁ ⊥ := by
  have hrel := s15_Lin_relIndex_centralizer_le h
  have h1 : (E ⊓ centralizer ({v} : Set G)).relIndex E =
      (centralizer ({v} : Set G)).relIndex E := by
    rw [inf_comm]
    exact Subgroup.inf_relIndex_right _ _
  have h2 := E3.relIndex_eq_two_pow hE (E ⊓ centralizer ({v} : Set G))
  have h3 := E3.card_eq_two_pow_mul hV₁ (bot_le : (⊥ : Subgroup G) ≤ V₁)
  rw [Subgroup.card_bot, mul_one] at h3
  rw [← h1, h2, h3] at hrel
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 hrel

theorem fifteen_ten (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) {g : G} {A B E : Subgroup G}
    (hA : A = conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g) (hB : B = A ⊓ D.M)
    (hEB : E ≤ B) (hE : E3.mQuot A E < gamma15 D.M V₀ V hV L)
    (hVg : ¬ V ≤ conjSubgroup D.M g) (hgV : ¬ conjSubgroup V g ≤ D.M) :
    wStar D.M V₀ V hV L ⊓ fixV (barSub (v1Sub D.M V₀ V hV L) V hV E) =
        imgTil (v1Sub D.M V₀ V hV L) V hV (wSub V₀ V hV L ⊓ centralizer (E : Set G)) ∧
      ⁅wSub V₀ V hV L ⊓ centralizer (E : Set G), B⁆ = ⊥ := by
  have h151 := h.hyp151
  have hM : D.M ≤ normalizer (V : Set G) := h151.hyp125.pairFacts.le_normalizer
  have hBA : B ≤ A := hB ▸ inf_le_left
  have hBM : B ≤ D.M := hB ▸ inf_le_right
  have hEA : E ≤ A := hEB.trans hBA
  have hEM : E ≤ D.M := hEB.trans hBM
  have hEs : E ≤ stabTil (v1Sub D.M V₀ V hV L) V :=
    hEM.trans (le_stabTil hM (s15_Infra_le_normalizer_v1Sub h151.hyp125 hV))
  have hcen := (centralizer_le_normalizer_of_mQuot_lt D h hV hA hEA hE).2
  have hWV : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤ V :=
    sup_le (preTil_le V₀ V hV _) (s15_Infra_v1Sub_le h151.hyp125 hV)
  have hAV : A ≤ conjSubgroup V g := hA ▸ E3.conjSubgroup_mono_left g hWV
  have hVabel : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x :=
    fun x hx y hy => B2F.isElemAbelian_comm hV hx hy
  have hVgabel : ∀ x ∈ conjSubgroup V g, ∀ y ∈ conjSubgroup V g, x * y = y * x :=
    fun x hx y hy => B2F.isElemAbelian_comm (E3.isElemAbelian_conjSubgroup hV g) hx hy
  have hA2 : IsPGroup 2 A := (E3.isElemAbelian_conjSubgroup hV g).isPGroup.to_le hAV
  have hE2 : IsPGroup 2 E := hA2.to_le hEA
  have hV12 : IsPGroup 2 (v1Sub D.M V₀ V hV L) :=
    hV.isPGroup.to_le (s15_Infra_v1Sub_le h151.hyp125 hV)
  have hKMg : rankThreeIsMaxTwoLocal (conjSubgroup D.M g) :=
    UC6.isMaxTwoLocal_conj (show IsMaxTwoLocalSubgroup D.M from D.maxLocal) g
  have hU1 : ∀ w ∈ v1Sub D.M V₀ V hV L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) :=
    fun w hw hw1 => h.unique₁ w (Subgroup.mem_sup_right hw) hw1
  have hV1g : v1Sub D.M V₀ V hV L ⊓ conjSubgroup V g = ⊥ :=
    inf_eq_bot_of_not_le_of_uniqueMax D.maxLocal hV12 hU1 hVgabel hgV
  have hAUm : ∀ w ∈ A, w ≠ 1 →
      UniqueMax (conjSubgroup D.M g) (conjSubgroup D.M g ⊓ centralizer ({w} : Set G)) :=
    fun w hw hw1 => uniqueMax_conjSubgroup_of_mem (g := g) h.unique₁ (hA ▸ hw) hw1
  have hAV0 : A ⊓ V = ⊥ := inf_eq_bot_of_not_le_of_uniqueMax hKMg hA2 hAUm hVabel hVg
  refine ⟨?_, ?_⟩
  · ext u
    constructor
    · intro hu
      obtain ⟨hu_W, hu_fix⟩ := Subgroup.mem_inf.1 hu
      obtain ⟨x, hxW, rfl⟩ :=
        (mem_imgTil (v1Sub D.M V₀ V hV L) V hV (wSub V₀ V hV L) u).1 hu_W
      have hvV : x.val ∈ V := x.val_mem
      have hcomm1 : ∀ e ∈ E, e * x.val * e⁻¹ * (x.val)⁻¹ ∈ v1Sub D.M V₀ V hV L := by
        intro e he
        have := (mem_fixV.1 hu_fix) (actTil (v1Sub D.M V₀ V hV L) V hV ⟨e, hEs he⟩)
          (actTil_mem_barSub _ V hV he (hEs he))
        rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at this
        exact this
      have horbit : ∀ e ∈ E, (x.val)⁻¹ * (e⁻¹ * x.val * e) ∈ v1Sub D.M V₀ V hV L := by
        intro e he
        have hc := hcomm1 e⁻¹ (E.inv_mem he)
        rw [inv_inv] at hc
        have hcV : e⁻¹ * x.val * e * (x.val)⁻¹ ∈ V :=
          s15_Infra_v1Sub_le h151.hyp125 hV hc
        have hcomm := B2F.isElemAbelian_comm hV hcV hvV
        have key : (x.val)⁻¹ * (e⁻¹ * x.val * e) =
            e⁻¹ * x.val * e * (x.val)⁻¹ := by
          calc (x.val)⁻¹ * (e⁻¹ * x.val * e)
              = (x.val)⁻¹ * ((e⁻¹ * x.val * e * (x.val)⁻¹) * x.val) := by group
            _ = (x.val)⁻¹ * (x.val * (e⁻¹ * x.val * e * (x.val)⁻¹)) := by rw [hcomm]
            _ = e⁻¹ * x.val * e * (x.val)⁻¹ := by group
        rw [key]
        exact hc
      have hmq := s15_FiveTen_mQuot_inf_centralizer_le hE2 hV12 horbit
      have hCbot : E ⊓ centralizer ({x.val} : Set G) ≠ ⊥ := by
        intro hbot
        have h1 := E3.mQuot_add (V := A) (U := E ⊓ centralizer ({x.val} : Set G)) (U' := E)
          inf_le_left hEA
        have h2 := s15_FiveTen_mQuot_conj_bot D h151.hyp125 hV (L := L) g
        rw [← hA] at h2
        rw [hbot] at h1 hmq
        omega
      obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hCbot
      have haE : (a : G) ∈ E := (Subgroup.mem_inf.1 a.2).1
      have hav : (a : G) ∈ centralizer ({x.val} : Set G) := (Subgroup.mem_inf.1 a.2).2
      have ha1' : (a : G) ≠ 1 := fun h1 => ha1 (Subtype.ext h1)
      have hu' := hAUm (a : G) (hEA haE) ha1'
      have ha2 : ∃ n : ℕ, (a : G) ^ (2 ^ n) = 1 := by
        refine ⟨1, ?_⟩
        have := (E3.isElemAbelian_conjSubgroup hV g).2 (a : G) (hAV (hEA haE))
        simpa using this
      have hvM : x.val ∈ conjSubgroup D.M g := by
        refine (centralizer_le_of_uniqueMax hKMg ha1' ha2 hu').1 ?_
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.1 hav).symm
      have hvNVg : x.val ∈ normalizer (conjSubgroup V g : Set G) := by
        have h1 : conjSubgroup D.M g ≤ conjSubgroup (normalizer (V : Set G)) g :=
          E3.conjSubgroup_mono_left g hM
        rw [E3.conjSubgroup_normalizer] at h1
        exact h1 hvM
      have hvcent : ∀ e ∈ E, e * x.val = x.val * e := by
        intro e he
        have hc1 := hcomm1 e he
        have hcVg : e * x.val * e⁻¹ * (x.val)⁻¹ ∈ conjSubgroup V g := by
          have h1 : e⁻¹ ∈ conjSubgroup V g := (conjSubgroup V g).inv_mem (hAV (hEA he))
          have h2 := (Subgroup.mem_normalizer_iff.1 hvNVg e⁻¹).1 h1
          have h3 : e * (x.val * e⁻¹ * (x.val)⁻¹) ∈ conjSubgroup V g :=
            (conjSubgroup V g).mul_mem (hAV (hEA he)) h2
          simpa [mul_assoc] using h3
        have h4 : e * x.val * e⁻¹ * (x.val)⁻¹ ∈
            v1Sub D.M V₀ V hV L ⊓ conjSubgroup V g := Subgroup.mem_inf.2 ⟨hc1, hcVg⟩
        rw [hV1g] at h4
        have h5 : e * x.val * e⁻¹ * (x.val)⁻¹ = 1 := Subgroup.mem_bot.1 h4
        calc e * x.val = (e * x.val * e⁻¹ * (x.val)⁻¹) * (x.val * e) := by group
          _ = x.val * e := by rw [h5, one_mul]
      exact (mem_imgTil _ V hV _ _).2
        ⟨x, Subgroup.mem_inf.2 ⟨hxW, Subgroup.mem_centralizer_iff.2 hvcent⟩, rfl⟩
    · intro hu
      obtain ⟨x, hx, rfl⟩ := (mem_imgTil (v1Sub D.M V₀ V hV L) V hV _ u).1 hu
      obtain ⟨hxW, hxC⟩ := Subgroup.mem_inf.1 hx
      refine Subgroup.mem_inf.2 ⟨(mem_imgTil _ V hV _ _).2 ⟨x, hxW, rfl⟩, ?_⟩
      rw [mem_fixV]
      intro φ hφ
      obtain ⟨e, heE, rfl⟩ := (mem_barSub _ V hV E φ).1 hφ
      rw [actTil_mk]
      congr 1
      apply IntMod.val_injective
      rw [actStab_apply_val]
      have := Subgroup.mem_centralizer_iff.1 hxC (e : G) heE
      calc (e : G) * x.val * (e : G)⁻¹ = x.val * (e : G) * (e : G)⁻¹ := by rw [this]
        _ = x.val := by group
  · refine le_bot_iff.1 (Subgroup.commutator_le.2 fun v hv b hb => ?_)
    obtain ⟨hvW, hvC⟩ := Subgroup.mem_inf.1 hv
    have hvN : v ∈ normalizer (A : Set G) := (Subgroup.mem_inf.1 (hcen hvC)).2
    have hbA : b ∈ A := hBA hb
    have hbV : b ∈ normalizer (V : Set G) := hM (hBM hb)
    have hvV : v ∈ V := preTil_le V₀ V hV _ hvW
    have h1 : ⁅v, b⁆ ∈ A ⊓ V := by
      rw [commutatorElement_def]
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · exact A.mul_mem ((Subgroup.mem_normalizer_iff.1 hvN b).1 hbA) (A.inv_mem hbA)
      · have h2 := (Subgroup.mem_normalizer_iff.1 hbV v⁻¹).1 (V.inv_mem hvV)
        have h3 : v * (b * v⁻¹ * b⁻¹) ∈ V := V.mul_mem hvV h2
        simpa [mul_assoc] using h3
    rw [hAV0] at h1
    exact h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
