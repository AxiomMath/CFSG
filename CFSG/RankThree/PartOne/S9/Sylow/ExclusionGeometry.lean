module

public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionSetup
public import CFSG.RankThree.PartOne.S9.StatementsTwoAction
public import CFSG.RankThree.GroupTheory.SteinbergBMActivePrimeLine
public import CFSG.RankThree.GroupTheory.SteinbergBYQD32Extraspecial

public section

namespace CFSG.RankThree.PartOne.Sec9Excl

open Subgroup CFSG CFSG.RankThree.GroupTheory

section Involution

variable {G : Type*} [Group G]

theorem normalizer_zpowers_eq_centralizer {r : G} (hr : orderOf r = 2) :
    normalizer ((zpowers r : Subgroup G) : Set G) = centralizer ({r} : Set G) := by
  have hr1 : r ≠ 1 := fun h => by simp [h] at hr
  ext g
  constructor
  · intro hg
    have h1 : g * r * g⁻¹ ∈ zpowers r := (Subgroup.mem_normalizer_iff.mp hg r).mp
      (Subgroup.mem_zpowers r)
    rw [CFSG.RankThree.GroupTheory.SteinbergBY.mem_zpowers_of_orderOf_eq_two hr] at h1
    rcases h1 with h1 | h1
    · exact absurd (by simpa using h1) hr1
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * r = (g * r * g⁻¹) * g := by group
        _ = r * g := by rw [h1]
  · intro hg
    have hg' : g ∈ centralizer ((zpowers r : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have : Commute g r := Subgroup.mem_centralizer_singleton_iff.mp hg
      exact ((this.symm.zpow_left k).eq)
    exact centralizer_le_normalizer _ hg'

theorem isTwoLocal_centralizer {r : G} (hr : orderOf r = 2) :
    CFSG.Assembly.IsTwoLocal (centralizer ({r} : Set G)) := by
  have hr1 : r ≠ 1 := fun h => by simp [h] at hr
  refine ⟨zpowers r, ?_, ?_, (normalizer_zpowers_eq_centralizer hr).symm⟩
  · rwa [Ne, Subgroup.zpowers_eq_bot]
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hr, pow_one])

end Involution

section Core

variable {G : Type*} [Group G]

theorem centralizer_inf_centralizer_pCore_le (hchar : CFSG.Assembly.IsCharTwoType G) {r : G}
    (hr : orderOf r = 2) :
    centralizer ({r} : Set G) ⊓
        centralizer ((inSubgroup (pCore 2) (centralizer ({r} : Set G)) : Subgroup G) : Set G) ≤
      inSubgroup (pCore 2) (centralizer ({r} : Set G)) := by
  have h := hchar _ (isTwoLocal_centralizer hr)
  have e : CFSG.Assembly.pCoreOf 2 (centralizer ({r} : Set G)) =
      inSubgroup (pCore 2) (centralizer ({r} : Set G)) := by
    simp only [CFSG.Assembly.pCoreOf, inSubgroup]
  rwa [e] at h

theorem inf_centralizer_pCore_eq_bot (hchar : CFSG.Assembly.IsCharTwoType G) {r : G}
    (hr : orderOf r = 2) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {F : Subgroup G} (hFq : IsPGroup q F)
    (hFr : F ≤ centralizer ({r} : Set G)) :
    F ⊓ centralizer ((inSubgroup (pCore 2) (centralizer ({r} : Set G)) : Subgroup G) : Set G) =
      ⊥ := by
  have h1 : F ⊓ centralizer ((inSubgroup (pCore 2) (centralizer ({r} : Set G)) : Subgroup G) :
      Set G) ≤ inSubgroup (pCore 2) (centralizer ({r} : Set G)) := fun x hx =>
    centralizer_inf_centralizer_pCore_le hchar hr ⟨hFr hx.1, hx.2⟩
  have h2 : F ⊓ inSubgroup (pCore 2) (centralizer ({r} : Set G)) = ⊥ :=
    inf_eq_bot_of_isPGroup hq Nat.prime_two hq2 hFq (isPGroup_inSubgroup_pCore 2 _)
  refine eq_bot_iff.mpr fun x hx => ?_
  have hx' : x ∈ F ⊓ inSubgroup (pCore 2) (centralizer ({r} : Set G)) := ⟨hx.1, h1 hx⟩
  rwa [h2] at hx'

theorem le_normalizer_inSubgroup_frattini (D : Subgroup G) :
    D ≤ normalizer ((inSubgroup frattini D : Subgroup G) : Set G) :=
  le_normalizer_map_subtype D (frattini D)

theorem map_subtype_center (F : Subgroup G) :
    (Subgroup.center F).map F.subtype = F ⊓ centralizer (F : Set G) := by
  ext x
  rw [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, fun h hh => ?_⟩
    have := Subgroup.mem_center_iff.mp hy ⟨h, hh⟩
    exact congrArg Subtype.val this
  · rintro ⟨hx, hc⟩
    refine ⟨⟨x, hx⟩, Subgroup.mem_center_iff.mpr fun g => ?_, rfl⟩
    exact Subtype.ext (hc g g.2)

theorem shape_of_geometry {q : ℕ} (hq : q.Prime) {D F : Subgroup G}
    (h1 : (IsElementaryAbelian q D ∧ Nat.card D = q ^ 4) →
      IsElementaryAbelian q F ∧ Nat.card F = q ^ 2)
    (h2 : ¬ (IsElementaryAbelian q D ∧ Nat.card D = q ^ 4) →
      (∀ x ∈ F, x ^ q = 1) ∧ Nat.card F = q ^ 3 ∧ F ⊓ centralizer (F : Set G) = ⁅F, F⁆ ∧
        ⁅F, F⁆ = inSubgroup frattini F ∧ inSubgroup frattini F = inSubgroup frattini D ∧
        Nat.card (inSubgroup frattini D) = q) :
    (IsElementaryAbelian q F ∧ Nat.card F = q ^ 2) ∨
      (Monoid.exponent F = q ∧ Nat.card F = q ^ 3 ∧ Subgroup.center F = commutator F ∧
        commutator F = frattini F ∧ Nat.card (Subgroup.center F) = q) := by
  by_cases hel : IsElementaryAbelian q D ∧ Nat.card D = q ^ 4
  · exact Or.inl (h1 hel)
  right
  obtain ⟨hpow, hcard, hcent, hcomm, hfrat, hfD⟩ := h2 hel
  have hinj := Subgroup.map_injective (G := F) F.subtype_injective
  have hZ : (Subgroup.center F).map F.subtype = (commutator F).map F.subtype := by
    rw [map_subtype_center, Subgroup.map_subtype_commutator, hcent]
  have hC : (commutator F).map F.subtype = (frattini F).map F.subtype := by
    rw [Subgroup.map_subtype_commutator]
    exact hcomm
  refine ⟨?_, hcard, hinj hZ, hinj hC, ?_⟩
  · have hdvd : Monoid.exponent F ∣ q := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
      Subtype.ext (by simpa using hpow x x.2)
    rcases (Nat.dvd_prime hq).mp hdvd with h | h
    · exfalso
      have hsub : Subsingleton F := ⟨fun a b => by
        have ha := Monoid.pow_exponent_eq_one a
        have hb := Monoid.pow_exponent_eq_one b
        rw [h, pow_one] at ha hb
        rw [ha, hb]⟩
      have : Nat.card F = 1 := Nat.card_unique
      rw [hcard] at this
      have h3 : 1 < q ^ 3 := Nat.one_lt_pow (by norm_num) hq.one_lt
      omega
    · exact h
  · have h1 : Nat.card (Subgroup.center F) = Nat.card ((Subgroup.center F).map F.subtype) :=
      (Subgroup.card_map_of_injective F.subtype_injective).symm
    rw [h1, map_subtype_center, hcent, hcomm, hfrat, hfD]

end Core

section GoodLine

variable {G : Type} [Group G] [Finite G]

theorem exists_good_line (hQDG : QuaternionDihedralOddCentralizerGeometry)
    (hchar : CFSG.Assembly.IsCharTwoType G)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {R D B : Subgroup G}
    (hRqd : Nonempty (R ≃* QD32)) (hRD : R ≤ normalizer (D : Set G))
    (hBD : B ≤ normalizer (D : Set G)) (hBR : B ≤ centralizer (R : Set G))
    (hRDc : R ⊓ centralizer (D : Set G) = ⊥) (hfrat : ⁅R, inSubgroup frattini D⁆ = ⊥)
    (hQD : IsQDShape q D) (hDq : IsPGroup q D)
    {z r : G} (hzR : z ∈ R) (hz1 : z ≠ 1) (hzc : z ∈ inSubgroup Subgroup.center R)
    (hrR : r ∈ R) (hr2 : orderOf r = 2) (hrc : r ∉ inSubgroup Subgroup.center R) :
    ∃ Y : Subgroup G, Y ≤ D ⊓ centralizer ({r} : Set G) ∧ Nat.card Y = q ∧
      B ≤ normalizer (Y : Set G) ∧ z ∈ normalizer (Y : Set G) ∧
      3 ≤ CFSG.pRank q ↥(D ⊓ centralizer (Y : Set G)) ∧
      D ⊓ centralizer (Y : Set G) = ⁅D ⊓ centralizer (Y : Set G), zpowers z⁆ ∧
      ⁅inSubgroup (pCore 2) (centralizer ({r} : Set G)) ⊓ centralizer (Y : Set G),
        D ⊓ centralizer ({r} : Set G) ⊓ centralizer (Y : Set G)⁆ ≠ ⊥ := by
  obtain ⟨h1, h2, h3⟩ := hQDG G q hq hq2 R D B hRqd hRD hBD hBR hRDc hfrat hQD z hzR hz1 hzc r hrR
    hr2 hrc (D ⊓ centralizer ({r} : Set G)) rfl
  set F := D ⊓ centralizer ({r} : Set G) with hFdef
  set K := inSubgroup (pCore 2) (centralizer ({r} : Set G)) with hKdef
  have hFq : IsPGroup q F := hDq.to_le inf_le_left
  have hFr : F ≤ centralizer ({r} : Set G) := inf_le_right
  have hKp : IsPGroup 2 K := isPGroup_inSubgroup_pCore 2 _
  have hFK : F ≤ normalizer (K : Set G) := hFr.trans (le_normalizer_inSubgroup_pCore 2 _)
  have hCF : F ⊓ centralizer (K : Set G) = ⊥ :=
    inf_centralizer_pCore_eq_bot hchar hr2 hq hq2 hFq hFr
  obtain ⟨Y₀, hY₀F, hY₀c, hY₀Φ', hY₀nt⟩ :=
    CFSG.RankThree.GroupTheory.SteinbergBM.small_odd_group_active_prime_line hq hq2 hKp hFK hCF
      (shape_of_geometry hq h1 h2)
  have hY₀Φ : ¬ Y₀ ≤ inSubgroup frattini D := by
    by_cases hel : IsElementaryAbelian q D ∧ Nat.card D = q ^ 4
    · intro hle
      have : Fact q.Prime := ⟨hq⟩
      have hDel := hel.1
      have hpg : Fact (IsPGroup q D) := ⟨IsElementaryAbelian.isPGroup q D⟩
      have hbot : inSubgroup frattini D = ⊥ := by
        rw [inSubgroup, frattini_eq_bot_of_isElementaryAbelian (p := q), Subgroup.map_bot]
      rw [hbot, le_bot_iff] at hle
      rw [hle, Subgroup.card_bot] at hY₀c
      exact hq.one_lt.ne hY₀c
    · rwa [← (h2 hel).2.2.2.2.1]
  obtain ⟨-, -, f, hfF, hBf, hzf⟩ := h3 Y₀ hY₀F hY₀c hY₀Φ
  have hfD : f ∈ D := hfF.1
  have hYF : conjugate Y₀ f ≤ F := by
    intro x hx
    rw [mem_conjugate_iff] at hx
    have := F.mul_mem (F.mul_mem (F.inv_mem hfF) (hY₀F hx)) hfF
    simpa [mul_assoc] using this
  have hYc : Nat.card (conjugate Y₀ f) = q := (card_conjugate Y₀ f).trans hY₀c
  have hYΦ : ¬ conjugate Y₀ f ≤ inSubgroup frattini D := by
    intro hle
    apply hY₀Φ
    intro y₀ hy₀
    have hy : f⁻¹ * y₀ * f ∈ conjugate Y₀ f := by
      rw [mem_conjugate_iff]
      simpa [mul_assoc] using hy₀
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_inSubgroup_frattini D hfD)
      (f⁻¹ * y₀ * f)).mp (hle hy)
    simpa [mul_assoc] using this
  obtain ⟨hrank, hP, -⟩ := h3 (conjugate Y₀ f) hYF hYc hYΦ
  refine ⟨conjugate Y₀ f, hYF, hYc, hBf, hzf, hrank, hP hzf, ?_⟩
  intro hbot
  apply hY₀nt
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro k₀ hk₀
  rw [Subgroup.mem_centralizer_iff]
  intro e₀ he₀
  have hconj : ∀ x₀ : G, (∀ y₀ ∈ Y₀, y₀ * x₀ = x₀ * y₀) →
      ∀ y ∈ conjugate Y₀ f, y * (f⁻¹ * x₀ * f) = (f⁻¹ * x₀ * f) * y := by
    intro x₀ hx₀ y hy
    rw [mem_conjugate_iff] at hy
    have h := hx₀ _ hy
    calc y * (f⁻¹ * x₀ * f) = f⁻¹ * ((f * y * f⁻¹) * x₀) * f := by group
      _ = f⁻¹ * (x₀ * (f * y * f⁻¹)) * f := by rw [h]
      _ = (f⁻¹ * x₀ * f) * y := by group
  have hk : f⁻¹ * k₀ * f ∈ K ⊓ centralizer ((conjugate Y₀ f : Subgroup G) : Set G) := by
    refine ⟨?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hFK hfF)) k₀).mp hk₀.1
      simpa using this
    · exact Subgroup.mem_centralizer_iff.mpr
        (hconj k₀ (Subgroup.mem_centralizer_iff.mp hk₀.2))
  have he : f⁻¹ * e₀ * f ∈ F ⊓ centralizer ((conjugate Y₀ f : Subgroup G) : Set G) := by
    refine ⟨F.mul_mem (F.mul_mem (F.inv_mem hfF) he₀.1) hfF, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr (hconj e₀ (Subgroup.mem_centralizer_iff.mp he₀.2))
  have hcomm := Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot hk) _ he
  have := congrArg (fun x => f * x * f⁻¹) hcomm
  simpa [mul_assoc] using this

end GoodLine

end CFSG.RankThree.PartOne.Sec9Excl
