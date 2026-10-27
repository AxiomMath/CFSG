module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res2ProofLBalComp
public import CFSG.RankThree.PartTwo.Sec14.Notation
public import CFSG.RankThree.PartTwo.Sec6.Item612Core

public section

namespace CFSG.RankThree.PartTwo.Sec14

namespace Item148Res5

open CFSG CFSG.RankThree.PartTwo.Sec14.Res2LBal
open CFSG.GH74.GLS (pPrimeCoreOf)

variable {X : Type} [Group X] [Finite X]

section Conj

omit [Finite X] in
theorem map_conj_eq_iff {J : Subgroup X} {y : X} :
    J.map (MulAut.conj y).toMonoidHom = J ↔ y ∈ Subgroup.normalizer (J : Set X) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rfl

omit [Finite X] in
theorem map_conj_eq_map_conj_iff {J : Subgroup X} {y y' : X} :
    J.map (MulAut.conj y).toMonoidHom = J.map (MulAut.conj y').toMonoidHom ↔
      y⁻¹ * y' ∈ Subgroup.normalizer (J : Set X) := by
  rw [← map_conj_eq_iff]
  constructor
  · intro h
    rw [← map_conj_map_conj, ← h, map_conj_map_conj, inv_mul_cancel, map_conj_one]
  · intro h
    conv_rhs => rw [show y' = y * (y⁻¹ * y') by group]
    rw [← map_conj_map_conj, h]

omit [Finite X] in
theorem mem_normalizer_map_conj_iff {J : Subgroup X} {x g : X} :
    g ∈ Subgroup.normalizer (J.map (MulAut.conj x).toMonoidHom : Set X) ↔
      x⁻¹ * g * x ∈ Subgroup.normalizer (J : Set X) := by
  rw [← map_conj_eq_iff, map_conj_map_conj, eq_comm, map_conj_eq_map_conj_iff, mul_assoc]

omit [Finite X] in
theorem card_map_conj (J : Subgroup X) (x : X) :
    Nat.card (J.map (MulAut.conj x).toMonoidHom) = Nat.card J :=
  Subgroup.card_map_of_injective (MulAut.conj x).injective

end Conj

section Normalize

variable {J A B₀ : Subgroup X} {e : X}

theorem conj_mem_normalizer_of_component_e (hJ : IsComponent J) (h3 : 3 ∣ Nat.card J)
    (he3 : e ^ 3 = 1) (heJ : e ∈ Subgroup.centralizer (J : Set X)) (hB₀J : B₀ ≤ J)
    (hA : A = Subgroup.zpowers e ⊔ B₀)
    (hF3 : ∀ w : X, w ∈ Subgroup.centralizer (A : Set X) → w ^ 3 = 1 → w ∈ A)
    (hAJ : A ⊓ Subgroup.centralizer (J : Set X) ≤ Subgroup.zpowers e) (x : X) :
    x⁻¹ * e * x ∈ Subgroup.normalizer (J : Set X) := by
  by_contra hn
  have heN : e ∈ Subgroup.normalizer (J : Set X) :=
    Subgroup.centralizer_le_normalizer (J : Set X) heJ
  set J₁ := J.map (MulAut.conj x).toMonoidHom with hJ₁
  have hmove : e ∉ Subgroup.normalizer (J₁ : Set X) := fun h =>
    hn (mem_normalizer_map_conj_iff.mp h)
  obtain ⟨h01, h02, h12⟩ := orbit_ne he3 hmove
  set J₂ := J₁.map (MulAut.conj (e ^ 1)).toMonoidHom with hJ₂
  set J₃ := J₁.map (MulAut.conj (e ^ 2)).toMonoidHom with hJ₃
  have hc₁ : IsComponent J₁ := isComponent_conj hJ x
  have hc₂ : IsComponent J₂ := isComponent_conj hc₁ _
  have hc₃ : IsComponent J₃ := isComponent_conj hc₁ _
  have hxN : x ∉ Subgroup.normalizer (J : Set X) := by
    intro hx
    apply hn
    exact mul_mem (mul_mem (inv_mem hx) heN) hx
  have hne : ∀ y : X, y ∈ Subgroup.normalizer (J : Set X) →
      J.map (MulAut.conj (y * x)).toMonoidHom ≠ J := by
    intro y hy h
    apply hxN
    have h1 := map_conj_eq_iff.mp h
    have : x = y⁻¹ * (y * x) := by group
    rw [this]
    exact mul_mem (inv_mem hy) h1
  have hJ₁J : J₁ ≠ J := by
    have := hne 1 (one_mem _)
    rwa [one_mul] at this
  have hJ₂J : J₂ ≠ J := by
    rw [hJ₂, hJ₁, map_conj_map_conj]
    exact hne _ (pow_mem heN 1)
  have hJ₃J : J₃ ≠ J := by
    rw [hJ₃, hJ₁, map_conj_map_conj]
    exact hne _ (pow_mem heN 2)
  set D := J₁ ⊔ J₂ ⊔ J₃ with hD
  have hDC : D ≤ Subgroup.centralizer (J : Set X) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact fun y hy => mem_centralizer_of_mem_of_ne hJ hc₁ hJ₁J.symm hy
    · exact fun y hy => mem_centralizer_of_mem_of_ne hJ hc₂ hJ₂J.symm hy
    · exact fun y hy => mem_centralizer_of_mem_of_ne hJ hc₃ hJ₃J.symm hy
  have hDN : D ≤ Subgroup.normalizer (J₁ : Set X) := by
    refine sup_le (sup_le Subgroup.le_normalizer ?_) ?_
    · exact fun y hy => Subgroup.centralizer_le_normalizer (J₁ : Set X)
        (mem_centralizer_of_mem_of_ne hc₁ hc₂ h01 hy)
    · exact fun y hy => Subgroup.centralizer_le_normalizer (J₁ : Set X)
        (mem_centralizer_of_mem_of_ne hc₁ hc₃ h02 hy)
  have heD : e ∈ Subgroup.normalizer (D : Set X) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change D.map (MulAut.conj e).toMonoidHom = D
    have e1 : J₁.map (MulAut.conj e).toMonoidHom = J₂ := by rw [hJ₂, pow_one]
    have e2 : J₂.map (MulAut.conj e).toMonoidHom = J₃ := by
      rw [hJ₂, hJ₃, map_conj_map_conj, pow_one, ← pow_two]
    have e3 : J₃.map (MulAut.conj e).toMonoidHom = J₁ := by
      rw [hJ₃, map_conj_map_conj, ← pow_succ', he3, map_conj_one]
    rw [hD, Subgroup.map_sup, Subgroup.map_sup, e1, e2, e3]
    exact (sup_comm _ _).trans (sup_assoc _ _ _).symm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 (Subgroup.zpowers e) := isPGroup_zpowers he3
  have hPD : Subgroup.zpowers e ≤ Subgroup.normalizer (D : Set X) :=
    (Subgroup.zpowers_le).mpr heD
  have hmod := Sec6.card_inf_centralizer_modEq hP hPD
  have h3D : 3 ∣ Nat.card D := by
    have h1 : 3 ∣ Nat.card J₁ := by rw [card_map_conj]; exact h3
    exact h1.trans (Subgroup.card_dvd_of_le (le_sup_left.trans le_sup_left))
  have h3C : 3 ∣ Nat.card
      ↥(D ⊓ Subgroup.centralizer (Subgroup.zpowers e : Set X)) :=
    Nat.modEq_zero_iff_dvd.mp (hmod.trans (Nat.modEq_zero_iff_dvd.mpr h3D))
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 3 h3C
  have hw' : orderOf (w : X) = 3 := by rw [Subgroup.orderOf_coe]; exact hw
  have hw3 : (w : X) ^ 3 = 1 := by rw [← hw']; exact pow_orderOf_eq_one _
  have hwD : (w : X) ∈ D := w.2.1
  have hwA : (w : X) ∈ Subgroup.centralizer (A : Set X) := by
    rw [hA, Subgroup.mem_centralizer_iff]
    intro a ha
    have hcl : Subgroup.zpowers e ⊔ B₀ ≤ Subgroup.centralizer {(w : X)} := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact ((Subgroup.mem_centralizer_iff.mp w.2.2) e (Subgroup.mem_zpowers e))
      · intro b hb
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp (hDC hwD) b (hB₀J hb)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcl ha)
  have hwAA : (w : X) ∈ A := hF3 _ hwA hw3
  have hwe : (w : X) ∈ Subgroup.zpowers e := hAJ ⟨hwAA, hDC hwD⟩
  have hle : Subgroup.zpowers (w : X) ≤ Subgroup.zpowers e := Subgroup.zpowers_le.mpr hwe
  have hcard : Nat.card (Subgroup.zpowers e) ≤ Nat.card (Subgroup.zpowers (w : X)) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hw']
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one he3)
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  have heW : e ∈ Subgroup.zpowers (w : X) := by
    rw [heq]
    exact Subgroup.mem_zpowers e
  have heDD : e ∈ D := (Subgroup.zpowers_le.mpr hwD) heW
  exact hmove (hDN heDD)

theorem conj_mem_normalizer_of_component (hJ : IsComponent J) (h3 : 3 ∣ Nat.card J)
    (he3 : e ^ 3 = 1) (heJ : e ∈ Subgroup.centralizer (J : Set X)) (hB₀J : B₀ ≤ J)
    (hA : A = Subgroup.zpowers e ⊔ B₀)
    (hF3 : ∀ w : X, w ∈ Subgroup.centralizer (A : Set X) → w ^ 3 = 1 → w ∈ A)
    (hAJ : A ⊓ Subgroup.centralizer (J : Set X) ≤ Subgroup.zpowers e) (x : X) {a : X}
    (ha : a ∈ A) : x⁻¹ * a * x ∈ Subgroup.normalizer (J : Set X) := by
  have hsub : A ≤ Subgroup.normalizer (J.map (MulAut.conj x).toMonoidHom : Set X) := by
    rw [hA]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, mem_normalizer_map_conj_iff]
      exact conj_mem_normalizer_of_component_e hJ h3 he3 heJ hB₀J hA hF3 hAJ x
    · intro b hb
      by_cases hx : J.map (MulAut.conj x).toMonoidHom = J
      · rw [hx]
        exact Subgroup.le_normalizer (hB₀J hb)
      · exact Subgroup.centralizer_le_normalizer _
          (mem_centralizer_of_mem_of_ne (isComponent_conj hJ x) hJ hx (hB₀J hb))
  exact mem_normalizer_map_conj_iff.mp (hsub ha)

theorem commutator_le_normalizer_of_component (hJ : IsComponent J) (h3 : 3 ∣ Nat.card J)
    (he3 : e ^ 3 = 1) (heJ : e ∈ Subgroup.centralizer (J : Set X)) (hB₀J : B₀ ≤ J)
    (hA : A = Subgroup.zpowers e ⊔ B₀)
    (hF3 : ∀ w : X, w ∈ Subgroup.centralizer (A : Set X) → w ^ 3 = 1 → w ∈ A)
    (hAJ : A ⊓ Subgroup.centralizer (J : Set X) ≤ Subgroup.zpowers e) (H : Subgroup X) :
    ⁅H, A⁆ ≤ Subgroup.normalizer (J : Set X) := by
  have hAN : A ≤ Subgroup.normalizer (J : Set X) := by
    rw [hA]
    refine sup_le ?_ (hB₀J.trans Subgroup.le_normalizer)
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer (J : Set X) heJ
  rw [Subgroup.commutator_le]
  intro x _ a ha
  have h1 := conj_mem_normalizer_of_component hJ h3 he3 heJ hB₀J hA hF3 hAJ x⁻¹ ha
  rw [inv_inv] at h1
  rw [commutatorElement_def]
  exact mul_mem h1 (inv_mem (hAN ha))

theorem le_normalizer_of_component (hJ : IsComponent J) (h3 : 3 ∣ Nat.card J)
    (he3 : e ^ 3 = 1) (heJ : e ∈ Subgroup.centralizer (J : Set X)) (hB₀J : B₀ ≤ J)
    (hA : A = Subgroup.zpowers e ⊔ B₀)
    (hF3 : ∀ w : X, w ∈ Subgroup.centralizer (A : Set X) → w ^ 3 = 1 → w ∈ A)
    (hAJ : A ⊓ Subgroup.centralizer (J : Set X) ≤ Subgroup.zpowers e) {H : Subgroup X}
    (hH : H ≤ ⁅H, A⁆) : H ≤ Subgroup.normalizer (J : Set X) :=
  hH.trans (commutator_le_normalizer_of_component hJ h3 he3 heJ hB₀J hA hF3 hAJ H)

end Normalize

section Inner

variable {J : Subgroup X}

omit [Finite X] in
theorem mem_sup_centralizer_iff {g : X} :
    g ∈ J ⊔ Subgroup.centralizer (J : Set X) ↔
      ∃ j ∈ J, ∃ c ∈ Subgroup.centralizer (J : Set X), j * c = g := by
  have hle : J ≤ Subgroup.normalizer (Subgroup.centralizer (J : Set X) : Set X) :=
    fun j hj => Subgroup.mem_normalizer_iff.mpr fun c => by
      constructor
      · intro hc
        rw [Subgroup.mem_centralizer_iff] at hc ⊢
        intro y hy
        have h1 := hc y hy
        have h2 := hc (j⁻¹ * y * j) (by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (inv_mem hj)) y).mp hy
          simpa using this)
        calc y * (j * c * j⁻¹) = j * ((j⁻¹ * y * j) * c) * j⁻¹ := by group
          _ = j * (c * (j⁻¹ * y * j)) * j⁻¹ := by rw [h2]
          _ = j * c * j⁻¹ * y := by group
      · intro hc
        rw [Subgroup.mem_centralizer_iff] at hc ⊢
        intro y hy
        have h2 := hc (j * y * j⁻¹) (by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hj) y).mp hy
          exact this)
        calc y * c = j⁻¹ * ((j * y * j⁻¹) * (j * c * j⁻¹)) * j := by group
          _ = j⁻¹ * ((j * c * j⁻¹) * (j * y * j⁻¹)) * j := by rw [h2]
          _ = c * y := by group
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right J _ hle]
  constructor
  · rintro ⟨j, hj, c, hc, rfl⟩
    exact ⟨j, hj, c, hc, rfl⟩
  · rintro ⟨j, hj, c, hc, rfl⟩
    exact ⟨j, hj, c, hc, rfl⟩

omit [Finite X] in
theorem normalizer_le_normalizer_sup_centralizer :
    Subgroup.normalizer (J : Set X) ≤
      Subgroup.normalizer ((J ⊔ Subgroup.centralizer (J : Set X) : Subgroup X) : Set X) := by
  have key : ∀ n ∈ Subgroup.normalizer (J : Set X), ∀ g,
      g ∈ J ⊔ Subgroup.centralizer (J : Set X) →
        n * g * n⁻¹ ∈ J ⊔ Subgroup.centralizer (J : Set X) := by
    intro n hn g hg
    obtain ⟨j, hj, c, hc, rfl⟩ := mem_sup_centralizer_iff.mp hg
    refine mem_sup_centralizer_iff.mpr ⟨n * j * n⁻¹, (Subgroup.mem_normalizer_iff.mp hn j).mp hj,
      n * c * n⁻¹, ?_, by group⟩
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro y hy
    have hy' : n⁻¹ * y * n ∈ J := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) y).mp hy
      simpa using this
    have h1 := hc _ hy'
    calc y * (n * c * n⁻¹) = n * ((n⁻¹ * y * n) * c) * n⁻¹ := by group
      _ = n * (c * (n⁻¹ * y * n)) * n⁻¹ := by rw [h1]
      _ = n * c * n⁻¹ * y := by group
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨key n hn g, fun h => ?_⟩
  have := key n⁻¹ (inv_mem hn) _ h
  rwa [show n⁻¹ * (n * g * n⁻¹) * n⁻¹⁻¹ = g by group] at this

omit [Finite X] in
theorem le_sup_centralizer_of_le_commutator {A H : Subgroup X}
    (hAJ : A ≤ J ⊔ Subgroup.centralizer (J : Set X))
    (hHN : H ≤ Subgroup.normalizer (J : Set X)) (hH : H ≤ ⁅H, A⁆) :
    H ≤ J ⊔ Subgroup.centralizer (J : Set X) := by
  refine hH.trans ?_
  rw [Subgroup.commutator_le]
  intro x hx a ha
  have h1 : x * a * x⁻¹ ∈ J ⊔ Subgroup.centralizer (J : Set X) :=
    (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_sup_centralizer (hHN hx)) a).mp
      (hAJ ha)
  rw [commutatorElement_def]
  exact mul_mem h1 (inv_mem (hAJ ha))

end Inner

section Core

variable {Y J : Subgroup X}

theorem le_centralizer_conj_of_normal (hJ : IsComponent J) (h3 : 3 ∣ Nat.card J) (hJY : J ≤ Y)
    {F : Subgroup X} (hFC : F ≤ Y ⊓ Subgroup.centralizer (J : Set X))
    (hFn : Y ⊓ Subgroup.centralizer (J : Set X) ≤ Subgroup.normalizer (F : Set X))
    (hF3 : ¬ 3 ∣ Nat.card F) {g : X} (hg : g ∈ Y) :
    F ≤ Subgroup.centralizer ((J.map (MulAut.conj g).toMonoidHom : Subgroup X) : Set X) := by
  by_cases hgJ : J.map (MulAut.conj g).toMonoidHom = J
  · rw [hgJ]
    exact hFC.trans inf_le_right
  set C := Y ⊓ Subgroup.centralizer (J : Set X) with hC
  set L := J.map (MulAut.conj g).toMonoidHom with hLdef
  have hL : IsComponent L := isComponent_conj hJ g
  have hLY : L ≤ Y := by
    rintro _ ⟨j, hj, rfl⟩
    exact Y.mul_mem (Y.mul_mem hg (hJY hj)) (Y.inv_mem hg)
  have hLC : L ≤ C := le_inf hLY fun y hy => mem_centralizer_of_mem_of_ne hJ hL (Ne.symm hgJ) hy
  set L' : Subgroup ↥C := L.subgroupOf C with hL'
  set F' : Subgroup ↥C := F.subgroupOf C with hF'
  have hL'c : IsComponent L' :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLC).symm hL.1,
      hL.2.subgroupOf⟩
  have hF'n : F'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hFC).mpr hFn
  rcases CFSG.LocalCores.component_normal_subgroup hL'c hF'n with h | h
  · exfalso
    have hLF : L ≤ F := by
      intro y hy
      have : (⟨y, hLC hy⟩ : ↥C) ∈ F' := h (Subgroup.mem_subgroupOf.mpr hy)
      exact Subgroup.mem_subgroupOf.mp this
    apply hF3
    have h1 : 3 ∣ Nat.card L := by rw [hLdef, card_map_conj]; exact h3
    exact h1.trans (Subgroup.card_dvd_of_le hLF)
  · intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      (Subgroup.mem_subgroupOf.mpr hl : (⟨l, hLC hl⟩ : ↥C) ∈ L')
    have h2 := Subgroup.mem_centralizer_iff.mp h1 ⟨f, hFC hf⟩ (Subgroup.mem_subgroupOf.mpr hf)
    exact (congrArg Subtype.val h2).symm

theorem eq_bot_of_normal_centralizer_component (hJ : IsComponent J) (h3 : 3 ∣ Nat.card J)
    (hJY : J ≤ Y)
    (hY : ∀ P : Subgroup X, P ≤ Y → Y ≤ Subgroup.normalizer (P : Set X) →
      ¬ 3 ∣ Nat.card P → P = ⊥)
    {F : Subgroup X} (hFC : F ≤ Y ⊓ Subgroup.centralizer (J : Set X))
    (hFn : Y ⊓ Subgroup.centralizer (J : Set X) ≤ Subgroup.normalizer (F : Set X))
    (hF3 : ¬ 3 ∣ Nat.card F) : F = ⊥ := by
  set S : Set X := {x | ∃ g ∈ Y, ∃ j ∈ J, g * j * g⁻¹ = x} with hS
  set Ch : Subgroup X := Y ⊓ Subgroup.centralizer S with hCh
  have hFCh : F ≤ Ch := by
    refine le_inf (hFC.trans inf_le_left) ?_
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨g, hg, j, hj, rfl⟩
    have h1 := le_centralizer_conj_of_normal hJ h3 hJY hFC hFn hF3 hg hf
    exact Subgroup.mem_centralizer_iff.mp h1 _ (conj_mem_map hj g)
  have hChC : Ch ≤ Y ⊓ Subgroup.centralizer (J : Set X) := by
    refine le_inf inf_le_left ?_
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact Subgroup.mem_centralizer_iff.mp hc.2 j ⟨1, one_mem _, j, hj, by group⟩
  have hYCh : Y ≤ Subgroup.normalizer (Ch : Set X) := by
    have key : ∀ h ∈ Y, ∀ c ∈ Ch, h * c * h⁻¹ ∈ Ch := by
      intro h hh c hc
      refine ⟨Y.mul_mem (Y.mul_mem hh hc.1) (Y.inv_mem hh), Subgroup.mem_centralizer_iff.mpr ?_⟩
      rintro _ ⟨g, hg, j, hj, rfl⟩
      have h1 := Subgroup.mem_centralizer_iff.mp hc.2 ((h⁻¹ * g) * j * (h⁻¹ * g)⁻¹)
        ⟨h⁻¹ * g, Y.mul_mem (Y.inv_mem hh) hg, j, hj, rfl⟩
      calc g * j * g⁻¹ * (h * c * h⁻¹) =
          h * ((h⁻¹ * g) * j * (h⁻¹ * g)⁻¹ * c) * h⁻¹ := by group
        _ = h * (c * ((h⁻¹ * g) * j * (h⁻¹ * g)⁻¹)) * h⁻¹ := by rw [h1]
        _ = h * c * h⁻¹ * (g * j * g⁻¹) := by group
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨key h hh c, fun hc => ?_⟩
    have := key h⁻¹ (Y.inv_mem hh) _ hc
    rwa [show h⁻¹ * (h * c * h⁻¹) * h⁻¹⁻¹ = c by group] at this
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime 3 (Nat.card F) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hF3
  have hFW : F ≤ pPrimeCoreOf 3 Ch := le_pPrimeCoreOf hFCh (hChC.trans hFn) hcop
  have hW := hY (pPrimeCoreOf 3 Ch) ((pPrimeCoreOf_le 3 Ch).trans inf_le_left)
    (hYCh.trans (normalizer_le_normalizer_pPrimeCoreOf 3 Ch))
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Ch))
  rw [hW] at hFW
  exact le_bot_iff.mp hFW

theorem mem_of_mem_sup_centralizer (hJ : IsComponent J) (h3 : 3 ∣ Nat.card J) (hJY : J ≤ Y)
    (hY : ∀ P : Subgroup X, P ≤ Y → Y ≤ Subgroup.normalizer (P : Set X) →
      ¬ 3 ∣ Nat.card P → P = ⊥)
    (hZ : J ⊓ Subgroup.centralizer (J : Set X) = ⊥) {O : Subgroup X} (hO3 : ¬ 3 ∣ Nat.card O)
    (hON : Y ⊓ Subgroup.centralizer (J : Set X) ≤ Subgroup.normalizer (O : Set X)) {z : X}
    (hzO : z ∈ O) (hzY : z ∈ Y) (hzJ : z ∈ J ⊔ Subgroup.centralizer (J : Set X)) : z ∈ J := by
  set C := Y ⊓ Subgroup.centralizer (J : Set X) with hC
  have hcommJ : ∀ c ∈ C, ∀ j ∈ J, j * c = c * j := fun c hc j hj =>
    Subgroup.mem_centralizer_iff.mp hc.2 j hj
  let S' : Subgroup X :=
    { carrier := {c | c ∈ C ∧ ∃ j ∈ J, j * c ∈ O}
      mul_mem' := by
        rintro c₁ c₂ ⟨hc₁, j₁, hj₁, h₁⟩ ⟨hc₂, j₂, hj₂, h₂⟩
        refine ⟨C.mul_mem hc₁ hc₂, j₁ * j₂, J.mul_mem hj₁ hj₂, ?_⟩
        have e : j₁ * j₂ * (c₁ * c₂) = j₁ * c₁ * (j₂ * c₂) := by
          rw [mul_assoc j₁ j₂, ← mul_assoc j₂, hcommJ c₁ hc₁ j₂ hj₂]
          group
        rw [e]
        exact O.mul_mem h₁ h₂
      one_mem' := ⟨C.one_mem, 1, J.one_mem, by rw [one_mul]; exact O.one_mem⟩
      inv_mem' := by
        rintro c ⟨hc, j, hj, h⟩
        refine ⟨C.inv_mem hc, j⁻¹, J.inv_mem hj, ?_⟩
        have e : j⁻¹ * c⁻¹ = (j * c)⁻¹ := by
          rw [_root_.mul_inv_rev, ← hcommJ c⁻¹ (C.inv_mem hc) j⁻¹ (J.inv_mem hj)]
        rw [e]
        exact O.inv_mem h }
  have hS'C : S' ≤ C := fun c hc => hc.1
  have hS'N : C ≤ Subgroup.normalizer (S' : Set X) := by
    have key : ∀ d ∈ C, ∀ c ∈ S', d * c * d⁻¹ ∈ S' := by
      rintro d hd c ⟨hc, j, hj, h⟩
      refine ⟨C.mul_mem (C.mul_mem hd hc) (C.inv_mem hd), j, hj, ?_⟩
      have e : j * (d * c * d⁻¹) = d * (j * c) * d⁻¹ := by
        have h1 := hcommJ d hd j hj
        calc j * (d * c * d⁻¹) = (j * d) * c * d⁻¹ := by group
          _ = (d * j) * c * d⁻¹ := by rw [h1]
          _ = d * (j * c) * d⁻¹ := by group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hON hd) _).mp h
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨key d hd c, fun h => ?_⟩
    have := key d⁻¹ (C.inv_mem hd) _ h
    rwa [show d⁻¹ * (d * c * d⁻¹) * d⁻¹⁻¹ = c by group] at this
  have hS'3 : ¬ 3 ∣ Nat.card S' := by
    intro h3S
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 3 h3S
    obtain ⟨hsC, j, hj, hjs⟩ := s.2
    set m := orderOf (j * (s : X)) with hm
    have hm3 : ¬ 3 ∣ m := fun h => hO3 (h.trans (Subgroup.orderOf_dvd_natCard O hjs))
    have hjc : Commute j (s : X) := hcommJ _ hsC j hj
    have h1 : j ^ m * (s : X) ^ m = 1 := by rw [← hjc.mul_pow, hm, pow_orderOf_eq_one]
    have h2 : (s : X) ^ m ∈ J ⊓ Subgroup.centralizer (J : Set X) := by
      refine ⟨?_, Subgroup.pow_mem _ hsC.2 m⟩
      have : (s : X) ^ m = (j ^ m)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [this]
      exact J.inv_mem (J.pow_mem hj m)
    rw [hZ, Subgroup.mem_bot] at h2
    have h3m : orderOf (s : X) ∣ m := orderOf_dvd_of_pow_eq_one h2
    rw [Subgroup.orderOf_coe, hs] at h3m
    exact hm3 h3m
  have hS'bot : S' = ⊥ :=
    eq_bot_of_normal_centralizer_component hJ h3 hJY hY hS'C hS'N hS'3
  obtain ⟨j, hj, c, hc, rfl⟩ := mem_sup_centralizer_iff.mp hzJ
  have hcY : c ∈ Y := by
    have : c = j⁻¹ * (j * c) := by group
    rw [this]
    exact Y.mul_mem (Y.inv_mem (hJY hj)) hzY
  have hcS : c ∈ S' := ⟨⟨hcY, hc⟩, j, hj, hzO⟩
  rw [hS'bot, Subgroup.mem_bot] at hcS
  rw [hcS, mul_one]
  exact hj

end Core

end Item148Res5

end CFSG.RankThree.PartTwo.Sec14
