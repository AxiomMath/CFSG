module

public import CFSG.RankThree.PartOne.S12.Sec138Local
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.LocalAnalysis.GorensteinLyons (IsThreeTranspositions)

namespace Sec138Trans

section FiniteGroups

open Equiv

theorem odd_involution_exists : ∀ σ : Perm (Fin 4), σ * σ = 1 → Perm.sign σ = -1 →
    ∃ x y : Fin 4, x ≠ y ∧ σ = swap x y := by
  decide +kernel

theorem exists_swap_pow_ne : ∀ σ : Perm (Fin 4), σ * σ = 1 → σ ≠ 1 →
    (∀ x y : Fin 4, x ≠ y → σ ≠ swap x y) → ∃ x y : Fin 4, x ≠ y ∧ (σ * swap x y) ^ 6 ≠ 1 := by
  decide +kernel

theorem one_class {Γ : Type*} [Group Γ] (ψ : Γ ≃* Perm (Fin 4)) {S : Set Γ}
    (hconj : ∀ g : Γ, ∀ x ∈ S, g * x * g⁻¹ ∈ S) (hinv : ∀ x ∈ S, x * x = 1 ∧ x ≠ 1)
    (hgen : Subgroup.closure S = ⊤) (h6 : ∀ x ∈ S, ∀ y ∈ S, (x * y) ^ 6 = 1) :
    ∀ x ∈ S, ∀ y ∈ S, ∃ g : Γ, g * x * g⁻¹ = y := by
  have hodd : ∃ x ∈ S, Perm.sign (ψ x) = -1 := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ x ∈ S, Perm.sign (ψ x) = 1 := fun x hx =>
      (Int.units_eq_one_or _).resolve_right (hcon x hx)
    have htop : ∀ y : Γ, Perm.sign (ψ y) = 1 := by
      intro y
      have hy : y ∈ Subgroup.closure S := by
        rw [hgen]
        trivial
      induction hy using Subgroup.closure_induction with
      | mem x hx => exact hall x hx
      | one => simp
      | mul x y _ _ hx hy => simp [map_mul, hx, hy]
      | inv x _ hx => simp [hx]
    have h := htop (ψ.symm (swap 0 1))
    rw [MulEquiv.apply_symm_apply, Perm.sign_swap (by decide)] at h
    exact absurd h (by decide)
  obtain ⟨x0, hx0, hsgn⟩ := hodd
  have hx02 : ψ x0 * ψ x0 = 1 := by rw [← map_mul, (hinv x0 hx0).1, map_one]
  obtain ⟨a0, b0, hab0, hψx0⟩ := odd_involution_exists (ψ x0) hx02 hsgn
  have hswaps : ∀ a b : Fin 4, a ≠ b → ∃ y ∈ S, ψ y = swap a b := by
    intro a b hab
    obtain ⟨h, hh⟩ := isConj_iff.mp (Perm.isConj_swap hab0 hab)
    refine ⟨ψ.symm h * x0 * (ψ.symm h)⁻¹, hconj _ x0 hx0, ?_⟩
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hψx0]
    exact hh
  have hall_swap : ∀ y ∈ S, ∃ a b : Fin 4, a ≠ b ∧ ψ y = swap a b := by
    intro y hy
    by_contra hcon
    push Not at hcon
    have hy2 : ψ y * ψ y = 1 := by rw [← map_mul, (hinv y hy).1, map_one]
    have hy1 : ψ y ≠ 1 := fun h => (hinv y hy).2 ((MulEquiv.map_eq_one_iff ψ).1 h)
    obtain ⟨a, b, hab, hne⟩ := exists_swap_pow_ne (ψ y) hy2 hy1 hcon
    obtain ⟨z, hz, hψz⟩ := hswaps a b hab
    apply hne
    rw [← hψz, ← map_mul, ← map_pow, h6 y hy z hz, map_one]
  intro x hx y hy
  obtain ⟨a, b, hab, hψx⟩ := hall_swap x hx
  obtain ⟨c, d, hcd, hψy⟩ := hall_swap y hy
  obtain ⟨h, hh⟩ := isConj_iff.mp (Perm.isConj_swap hab hcd)
  refine ⟨ψ.symm h, ψ.injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hψx, hψy]
  exact hh

theorem not_S4_and_S5 {Γ : Type*} [Group Γ] (h4 : Nonempty (Γ ≃* Perm (Fin 4)))
    (h5 : Nonempty (Γ ≃* Perm (Fin 5))) : False := by
  obtain ⟨e4⟩ := h4
  obtain ⟨e5⟩ := h5
  have h := Nat.card_congr (e4.symm.trans e5).toEquiv
  rw [Nat.card_perm, Nat.card_perm, Nat.card_fin, Nat.card_fin] at h
  revert h
  decide

end FiniteGroups

theorem commute_of_closure {M : Type*} [Group M] {S T : Set M}
    (h : ∀ a ∈ S, ∀ b ∈ T, a * b = b * a) :
    ∀ y ∈ Subgroup.closure S, ∀ z ∈ Subgroup.closure T, y * z = z * y := by
  have h1 : ∀ b ∈ T, ∀ y ∈ Subgroup.closure S, Commute y b := by
    intro b hb y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx => exact h x hx b hb
    | one => exact Commute.one_left b
    | mul x y _ _ hx hy => exact hx.mul_left hy
    | inv x _ hx => exact hx.inv_left
  intro y hy z hz
  have : Commute y z := by
    induction hz using Subgroup.closure_induction with
    | mem x hx => exact h1 x hx y hy
    | one => exact Commute.one_right y
    | mul x z _ _ hx hz => exact hx.mul_right hz
    | inv x _ hx => exact hx.inv_right
  exact this.eq

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem torusImage_le_torusWeyl (E Y : Subgroup G) : torusImage E Y ≤ torusWeyl E :=
  Subgroup.map_le_range _ _

theorem reflections_one_class {p : ℕ} (hp : p.Prime) {E Y : Subgroup G} (h3 : ThreeTranspD p E)
    (hclosure : torusImage E Y =
      Subgroup.closure (reflectionSet p E ∩ (torusImage E Y : Set (MulAut E))))
    (hweyl : Nonempty (torusImage E Y ≃* Equiv.Perm (Fin 4))) :
    ∀ s ∈ reflectionSet p E, s ∈ torusImage E Y → ∀ t ∈ reflectionSet p E, t ∈ torusImage E Y →
      ∃ g ∈ torusImage E Y, g * s * g⁻¹ = t := by
  obtain ⟨ψ⟩ := hweyl
  let Γ : Subgroup (MulAut E) := torusImage E Y
  let S : Set ↥Γ := {x | (x : MulAut E) ∈ reflectionSet p E}
  have hconj : ∀ g : ↥Γ, ∀ x ∈ S, g * x * g⁻¹ ∈ S := fun g x hx =>
    WeylIso.conj_mem_reflectionSet_of_weyl hp (torusImage_le_torusWeyl E Y g.2) hx
  have hinv : ∀ x ∈ S, x * x = 1 ∧ x ≠ 1 := by
    intro x hx
    refine ⟨Subtype.ext (RefFacts.mul_self_eq_one hx.1), fun h1 => ?_⟩
    have h2 : (x : MulAut E) = 1 := congrArg Subtype.val h1
    have := hx.1.1
    rw [h2, orderOf_one] at this
    omega
  have hgen : Subgroup.closure S = ⊤ := by
    apply Subgroup.map_injective Γ.subtype_injective
    rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype]
    have himage : Γ.subtype '' S = reflectionSet p E ∩ (Γ : Set (MulAut E)) := by
      ext s
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hx, x.2⟩
      · rintro ⟨hs, hsΓ⟩
        exact ⟨⟨s, hsΓ⟩, hs, rfl⟩
    rw [himage]
    exact hclosure.symm
  have h6 : ∀ x ∈ S, ∀ y ∈ S, (x * y) ^ 6 = 1 := by
    intro x hx y hy
    have hle := h3 _ hx _ hy
    have hpos : 0 < orderOf ((x : MulAut E) * y) := orderOf_pos _
    have hdvd : orderOf ((x : MulAut E) * y) ∣ 6 := by
      have h123 : orderOf ((x : MulAut E) * y) = 1 ∨ orderOf ((x : MulAut E) * y) = 2 ∨
          orderOf ((x : MulAut E) * y) = 3 := by omega
      rcases h123 with h | h | h <;> rw [h] <;> norm_num
    exact Subtype.ext (orderOf_dvd_iff_pow_eq_one.1 hdvd)
  intro s hs hsΓ t ht htΓ
  obtain ⟨g, hg⟩ := one_class ψ hconj hinv hgen h6 ⟨s, hsΓ⟩ hs ⟨t, htΓ⟩ ht
  exact ⟨g.1, g.2, congrArg Subtype.val hg⟩

omit [Finite G] in
theorem torusImage_le_reflectionGroup {p : ℕ} {E Y : Subgroup G}
    (hclosure : torusImage E Y =
      Subgroup.closure (reflectionSet p E ∩ (torusImage E Y : Set (MulAut E)))) :
    torusImage E Y ≤ reflectionGroup p E :=
  hclosure.le.trans (Subgroup.closure_mono Set.inter_subset_left)

theorem isThreeTranspositions_D {p : ℕ} (hp : p.Prime) {E : Subgroup G} (h3 : ThreeTranspD p E) :
    IsThreeTranspositions {x : ↥(reflectionGroup p E) | (x : MulAut E) ∈ reflectionSet p E} := by
  let D' : Set ↥(reflectionGroup p E) := {x | (x : MulAut E) ∈ reflectionSet p E}
  have hD'mem : ∀ t (ht : t ∈ reflectionSet p E),
      (⟨t, Subgroup.subset_closure ht⟩ : ↥(reflectionGroup p E)) ∈ D' := fun t ht => ht
  have hconj : ∀ g : ↥(reflectionGroup p E), ∀ x ∈ D', g * x * g⁻¹ ∈ D' := fun g x hx =>
    WeylIso.conj_mem_reflectionSet_of_weyl hp (WeylIso.closure_le_weyl g.2) hx
  have hord : ∀ x ∈ D', orderOf x = 2 := fun x hx => by
    rw [← Subgroup.orderOf_coe]
    exact hx.1.1
  have hle3 : ∀ x ∈ D', ∀ y ∈ D', orderOf (x * y) ≤ 3 := fun x hx y hy => by
    rw [← Subgroup.orderOf_coe]
    exact h3 _ hx _ hy
  have hgen : Subgroup.closure D' = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    change x ∈ Subgroup.closure (reflectionSet p E) at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (hD'mem x hx)
    | one => exact Subgroup.one_mem _
    | mul x y hx hy ihx ihy => exact Subgroup.mul_mem _ ihx ihy
    | inv x hx ih => exact Subgroup.inv_mem _ ih
  exact ⟨⟨hconj, hord, hgen, fun x hx y hy => (hle3 x hx y hy).trans (by norm_num),
    fun x hx y hy h4 => absurd h4 (by have := hle3 x hx y hy; omega)⟩, hle3⟩

theorem fischer_commute {p : ℕ} (hp : p.Prime) {E : Subgroup G} (h3 : ThreeTranspD p E)
    {t0 : MulAut E} (ht0 : t0 ∈ reflectionSet p E) :
    ∀ a ∈ reflectionSet p E, (∃ g ∈ reflectionGroup p E, g * t0 * g⁻¹ = a) →
      ∀ b ∈ reflectionSet p E, (¬ ∃ g ∈ reflectionGroup p E, g * t0 * g⁻¹ = b) →
        a * b = b * a := by
  let D' : Set ↥(reflectionGroup p E) := {x | (x : MulAut E) ∈ reflectionSet p E}
  let t0' : ↥(reflectionGroup p E) := ⟨t0, Subgroup.subset_closure ht0⟩
  let A0 : Set ↥(reflectionGroup p E) := {x | ∃ g : ↥(reflectionGroup p E), g * t0' * g⁻¹ = x}
  let B0 : Set ↥(reflectionGroup p E) := D' \ A0
  have hD'conj : ∀ g : ↥(reflectionGroup p E), ∀ x ∈ D', g * x * g⁻¹ ∈ D' := fun g x hx =>
    WeylIso.conj_mem_reflectionSet_of_weyl hp (WeylIso.closure_le_weyl g.2) hx
  have ht0' : t0' ∈ D' := ht0
  have hA0D : A0 ⊆ D' := by
    rintro _ ⟨g, rfl⟩
    exact hD'conj g t0' ht0'
  have hAB : D' = A0 ∪ B0 := (Set.union_sdiff_cancel hA0D).symm
  have hdisj : Disjoint A0 B0 := Set.disjoint_sdiff_right
  have hA : ∀ g : ↥(reflectionGroup p E), ∀ x ∈ A0, g * x * g⁻¹ ∈ A0 := by
    rintro g _ ⟨k, rfl⟩
    exact ⟨g * k, by group⟩
  have hcomm := CFSG.RankThree.PartTwo.Sec7.rank3II_7_1 (isThreeTranspositions_D hp h3) hAB
    hdisj hA
  intro a ha ⟨g, hg, hga⟩ b hb hnb
  have hA0a : (⟨a, Subgroup.subset_closure ha⟩ : ↥(reflectionGroup p E)) ∈ A0 :=
    ⟨⟨g, hg⟩, Subtype.ext hga⟩
  have hB0b : (⟨b, Subgroup.subset_closure hb⟩ : ↥(reflectionGroup p E)) ∈ B0 :=
    ⟨hb, fun ⟨k, hk⟩ => hnb ⟨k, k.2, congrArg Subtype.val hk⟩⟩
  exact congrArg Subtype.val (hcomm _ hA0a _ hB0b)

theorem rowNine_data (h136 : Node136) (h138I : Node138I) (h124b : Node124b) {p : ℕ}
    {B : Subgroup G} {c : G} {X E : Subgroup G} (h : Sec12Hyp G p B c X E)
    (hF12 : Sec12Facts G p B c X E) (hF13 : Sec13Facts G p B c X E)
    (hT : ¬ Outcome152Five p E B (lieGenerated p E)) (hEB : E ≠ B) :
    torusImage E X = Subgroup.closure (reflectionSet p E ∩ (torusImage E X : Set (MulAut E))) ∧
      Nonempty (torusImage E X ≃* Equiv.Perm (Fin 4)) ∧ Nat.card E = p ^ 4 ∧
      ¬ (RowModel p X 11 ∧ RowWeylIso E (torusImage E X) 11) ∧ Sec12TwoGeneric p c X E := by
  obtain ⟨hclosure, r, hr1, hr12, hmodel, hweyl, hr8, hr9⟩ := hF12.three
  have hr9' : 9 ≤ r := by
    by_contra hlt
    exact hEB (hr8 (by omega))
  have hcard : Nat.card E = p ^ 4 := hr9 hr9'
  have hnot10 := h136 G p B c X E h hF12 hF13 hT hEB
  obtain ⟨hnot11, hnot12⟩ := h138I G p B c X E h hF12 hF13 hT hEB
  have hr : r = 9 := by
    by_contra hne9
    have h10 : r = 10 ∨ r = 11 ∨ r = 12 := by omega
    rcases h10 with rfl | rfl | rfl
    · exact hnot10 hmodel
    · exact hnot11 ⟨hmodel, hweyl⟩
    · exact hnot12 ⟨hmodel, hweyl⟩
  subst hr
  have hweyl' : Nonempty (torusImage E X ≃* Equiv.Perm (Fin 4)) := hweyl
  have hno11 : ¬ (RowModel p X 11 ∧ RowWeylIso E (torusImage E X) 11) := fun h11 =>
    not_S4_and_S5 hweyl' h11.2
  have hZ : ¬ p ∣ Nat.card (Subgroup.center X) := by
    intro hZ
    have hME := h124b G p B c X E h hZ
    rcases hF12.four.2 with ⟨-, hinf⟩ | ⟨h11, -⟩
    · rw [hME] at hinf
      apply h.c_ne_one
      have : c ∈ Subgroup.zpowers c ⊓ E := ⟨Subgroup.mem_zpowers c, h.A_le_E h.c_mem⟩
      rw [hinf, Subgroup.mem_bot] at this
      exact this
    · exact hno11 h11
  have hG : Sec12TwoGeneric p c X E := hF12.two.resolve_right fun hS =>
    hZ (by rw [hS.center_card, hS.p_eq])
  exact ⟨hclosure, hweyl', hcard, hno11, hG⟩

@[expose] def fixedByImage (E Y : Subgroup G) : Subgroup G where
  carrier := {e | ∃ he : e ∈ E, ∀ y ∈ torusImage E Y, y ⟨e, he⟩ = ⟨e, he⟩}
  one_mem' := ⟨one_mem _, fun y _ => map_one y⟩
  mul_mem' := by
    rintro a b ⟨ha, hfa⟩ ⟨hb, hfb⟩
    refine ⟨mul_mem ha hb, fun y hy => ?_⟩
    have : (⟨a * b, mul_mem ha hb⟩ : E) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [this, map_mul, hfa y hy, hfb y hy]
  inv_mem' := by
    rintro a ⟨ha, hfa⟩
    refine ⟨inv_mem ha, fun y hy => ?_⟩
    have : (⟨a⁻¹, inv_mem ha⟩ : E) = ⟨a, ha⟩⁻¹ := rfl
    rw [this, map_inv, hfa y hy]

omit [Finite G] in
theorem fixedByImage_le (E Y : Subgroup G) : fixedByImage E Y ≤ E := fun _ he => he.1

omit [Finite G] in
theorem conjAut_mem_torusImage {E Y : Subgroup G} {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G))
    (hwY : w ∈ Y) : conjAut E w hw ∈ torusImage E Y :=
  ⟨⟨w, hw⟩, Subgroup.mem_subgroupOf.2 hwY, rfl⟩

theorem fixedByImage_eq_zpowers {p : ℕ} {B : Subgroup G} {c : G} {X E : Subgroup G}
    (h : Sec12Hyp G p B c X E) (hF12 : Sec12Facts G p B c X E)
    {b : MulAut E} (hb : IsAutReflection p E b) (hbX : b ∈ torusImage E X) :
    fixedByImage E X = Subgroup.zpowers c := by
  have hcE : c ∈ E := h.A_le_E h.c_mem
  have hCinv : torusInvariant E X (fixedByImage E X) := by
    rintro w ⟨hwX, hwN⟩ e ⟨heE, hfe⟩
    have h1 := hfe _ (conjAut_mem_torusImage hwN hwX)
    have h2 : w * e * w⁻¹ = e := by
      have := congrArg Subtype.val h1
      rw [Equivariance.coe_conjAut hwN] at this
      exact this
    rw [h2]
    exact ⟨heE, hfe⟩
  have hcC : c ∈ fixedByImage E X := by
    refine ⟨hcE, fun y hy => ?_⟩
    obtain ⟨⟨w, hwN⟩, hwX, rfl⟩ := Subgroup.mem_map.1 hy
    have hwX' : w ∈ X := Subgroup.mem_subgroupOf.1 hwX
    apply Subtype.ext
    show ((conjAut E w hwN ⟨c, hcE⟩ : E) : G) = c
    rw [Equivariance.coe_conjAut hwN, mul_inv_eq_iff_eq_mul]
    exact (Sec12Three.comm_c_L h w hwX').symm
  have hC1 : fixedByImage E X ≠ ⊥ := by
    intro hbot
    have : c ∈ (⊥ : Subgroup G) := hbot ▸ hcC
    exact h.c_ne_one (Subgroup.mem_bot.1 this)
  have hCE : fixedByImage E X ≠ E := by
    intro hCE
    have hb1 : b = 1 := by
      apply MulEquiv.ext
      intro e
      have he : (e : G) ∈ fixedByImage E X := by
        rw [hCE]
        exact e.2
      obtain ⟨heE, hfe⟩ := he
      exact hfe b hbX
    have := hb.1
    rw [hb1, orderOf_one] at this
    omega
  rcases hF12.four.1 _ (fixedByImage_le E X) hCinv hC1 hCE with hC | hC
  · exact hC
  · exfalso
    rcases hF12.four.2 with ⟨-, hinf⟩ | ⟨-, hE⟩
    · have : c ∈ Subgroup.zpowers c ⊓ ⁅E, X ⊓ torusNormalizer E⁆ :=
        ⟨Subgroup.mem_zpowers c, hC ▸ hcC⟩
      rw [hinf, Subgroup.mem_bot] at this
      exact h.c_ne_one this
    · exact hCE (hC.trans hE)

omit [Finite G] in
theorem fixedByImage_invariant {E L X : Subgroup G}
    (hcomm : ∀ y ∈ torusImage E L, ∀ z ∈ torusImage E X, y * z = z * y) :
    torusInvariant E L (fixedByImage E X) := by
  rintro w ⟨hwL, hwN⟩ e ⟨heE, hfe⟩
  have hy := conjAut_mem_torusImage hwN hwL
  have hmemE : w * e * w⁻¹ ∈ E := by
    have := ((conjAut E w hwN) ⟨e, heE⟩).2
    rwa [Equivariance.coe_conjAut hwN] at this
  refine ⟨hmemE, fun z hz => ?_⟩
  apply Subtype.ext
  have h1 : (⟨w * e * w⁻¹, hmemE⟩ : E) = conjAut E w hwN ⟨e, heE⟩ :=
    Subtype.ext (Equivariance.coe_conjAut hwN ⟨e, heE⟩).symm
  rw [h1]
  have h2 : z ((conjAut E w hwN) ⟨e, heE⟩) = (conjAut E w hwN) (z ⟨e, heE⟩) := by
    have := congrArg (fun m : MulAut E => m ⟨e, heE⟩) (hcomm _ hy z hz).symm
    simpa [MulAut.mul_apply] using this
  rw [h2, hfe z hz]

omit [Finite G] in
theorem zpowers_comm_of_comm {c : G} {J : Subgroup G} (hc : ∀ j ∈ J, c * j = j * c) :
    ∀ k ∈ Subgroup.zpowers c, ∀ j ∈ J, k * j = j * k := by
  intro k hk j hj
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
  exact (Commute.zpow_left (hc j hj : Commute c j) i).eq

theorem zpowers_eq {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} (h : Sec12Hyp G p A c L E)
    (hF12 : Sec12Facts G p A c L E) (h11 : ¬ (RowModel p L 11 ∧ RowWeylIso E (torusImage E L) 11))
    (hcard : Nat.card E = p ^ 4)
    {c' : G} (hc'E : c' ∈ E) (hc'1 : c' ≠ 1) (hinv : torusInvariant E L (Subgroup.zpowers c')) :
    Subgroup.zpowers c' = Subgroup.zpowers c := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hc'ord : orderOf c' = p := orderOf_eq_prime (Sec12Three.pow_eq_one_of_mem_E h hc'E) hc'1
  have hcard' : Nat.card (Subgroup.zpowers c') = p := by rw [Nat.card_zpowers, hc'ord]
  have hle : Subgroup.zpowers c' ≤ E := Subgroup.zpowers_le.2 hc'E
  have hne0 : Subgroup.zpowers c' ≠ ⊥ := by
    intro hbot
    exact hc'1 (Subgroup.mem_bot.1 (hbot ▸ Subgroup.mem_zpowers c'))
  have hlt : p ^ 2 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  have hneE : Subgroup.zpowers c' ≠ E := by
    intro hEq
    rw [hEq, hcard] at hcard'
    have : p < p ^ 4 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  rcases hF12.four.1 _ hle hinv hne0 hneE with hc | hM
  · exact hc
  · exfalso
    rcases hF12.four.2 with ⟨hsup, hinf⟩ | ⟨h11', -⟩
    · have hM_le : ⁅E, L ⊓ torusNormalizer E⁆ ≤ E := hM ▸ hle
      have hcomm : ∀ k ∈ Subgroup.zpowers c, ∀ l ∈ ⁅E, L ⊓ torusNormalizer E⁆, k * l = l * k :=
        fun k hk l hl => by
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
          have hc : c * l = l * c :=
            congrArg Subtype.val (h.E_elem.is_comm.comm ⟨c, h.A_le_E h.c_mem⟩ ⟨l, hM_le hl⟩)
          exact (Commute.zpow_left (hc : Commute c l) i).eq
      have hcc := Torsion37.card_sup_of_commute_disjoint hcomm (disjoint_iff.2 hinf)
      rw [← hsup, Nat.card_zpowers, Sec12Three.orderOf_c h, hcard, ← hM, hcard'] at hcc
      have h22 : p * p = p ^ 2 := by ring
      omega
    · exact h11 h11'

omit [Finite G] in
theorem le_of_perfect_le_sup {P J : Subgroup G} {c : G} (hP : Group.IsPerfect P)
    (hc : ∀ j ∈ J, c * j = j * c) (hle : P ≤ Subgroup.zpowers c ⊔ J) : P ≤ J := by
  have hZc : ∀ z ∈ Subgroup.zpowers c, ∀ w ∈ J ⊔ Subgroup.zpowers c, z * w = w * z := by
    intro z hz w hw
    obtain ⟨l, hl, z', hz', rfl⟩ := Torsion37.exists_mul_of_mem_sup_of_commute
      (fun l hl z hz => (zpowers_comm_of_comm hc z hz l hl).symm) hw
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz'
    rw [← mul_assoc,
      (zpowers_comm_of_comm hc _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) i) l hl),
      mul_assoc, mul_assoc, (Commute.zpow_zpow_self c i j).eq]
  have hJJ : ⁅J, J⁆ ≤ J := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  calc P = ⁅P, P⁆ := (Subgroup.isPerfect_iff.1 hP).symm
    _ ≤ ⁅J ⊔ Subgroup.zpowers c, J ⊔ Subgroup.zpowers c⁆ :=
        Subgroup.commutator_mono (hle.trans_eq (sup_comm _ _)) (hle.trans_eq (sup_comm _ _))
    _ ≤ ⁅J, J⁆ := Sec13Base.commutator_sup_le_of_central hZc
    _ ≤ J := hJJ

theorem p_dvd_card_of_generic {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hG : Sec12TwoGeneric p c L E) : p ∣ Nat.card L := by
  have hp := h.prime
  have hcL : c ∉ L := h.c_not_mem_of_generic hG
  have R := h.restr_of_generic hG
  have hEcard := R.card_E hp (Sec12Three.orderOf_c h) hcL
  have h3 := h.pow_three_dvd_card_E
  rw [hEcard] at h3
  have h4 : p ^ 2 ∣ Nat.card ↥(E ⊓ L) := by
    have : p * p ^ 2 ∣ p * Nat.card ↥(E ⊓ L) := by
      rw [← pow_succ', mul_comm]
      exact h3
    exact Nat.dvd_of_mul_dvd_mul_left hp.pos this
  exact ((dvd_pow_self p (by norm_num)).trans h4).trans (Subgroup.card_dvd_of_le inf_le_right)

omit [Finite G] in
theorem sectionTenRel_of_le {p : ℕ} {L K : Subgroup G} (h : L ≤ K) : sectionTenRel p L K := by
  rw [sectionTenRel, inf_eq_left.2 h]
  exact (sup_eq_left.mpr (Subgroup.map_subtype_le _)).symm

theorem eq_of_zpowers_eq {p : ℕ} {A B' : Subgroup G} {c c' : G} {L X' E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hG : Sec12TwoGeneric p c L E) (hL : L ∈ thetaCompZeroStarE p E)
    (h' : Sec12Hyp G p B' c' X' E) (hG' : Sec12TwoGeneric p c' X' E)
    (hX : X' ∈ thetaCompZeroStarE p E) (hzp : Subgroup.zpowers c' = Subgroup.zpowers c) :
    X' = L := by
  have hp := h.prime
  have hcomm : ∀ x ∈ X', c * x = x * c := fun x hx => by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hzp ▸ Subgroup.mem_zpowers c : c ∈
      Subgroup.zpowers c')
    rw [← hk]
    exact (Commute.zpow_left (Sec12Three.comm_c_L h' x hx : Commute c' x) k).eq
  have hxN : ∀ x ∈ X', x ∈ cNormalizer c := fun x hx => by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (hcomm x hx : Commute c x) j).eq
  have hXgen := Sec13Base.le_closure_pElements hp hG'.quasisimple hG'.center_pPrime
    (p_dvd_card_of_generic h' hG')
  have hPM : X' ≤ Subgroup.zpowers c ⊔ L := by
    refine hXgen.trans ((Subgroup.closure_le _).2 ?_)
    rintro x ⟨hxX, hxp⟩
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    · have : Fact p.Prime := ⟨hp⟩
      exact hG.pElements x (hxN x hxX) (orderOf_eq_prime hxp hx1)
  have hXL : X' ≤ L := le_of_perfect_le_sup hG'.quasisimple.1 (Sec12Three.comm_c_L h) hPM
  have hrel : sectionTenRel p L X' := hX.2.2 L hL.2.1 (sectionTenRel_of_le hXL)
  exact le_antisymm hXL (le_of_sectionTenRel_of_isQuasisimple hp hG.quasisimple hrel)

end Sec138Trans

theorem node138Trans_of_nodes (h136 : Node136) (h138I : Node138I)
    (hSchreier : SchreierFor InCatalog) (hTwoAction : TwoActionInputs)
    (h106 : SectionTenMaximalMovingThetaComponentsQuasisimple) (h11 : Sec11One)
    (h122 : Node122) (h122b : Node122b) (h123 : Node123) (h124 : Node124) (h124b : Node124b)
    (h125 : Node125) (h126 : Node126) (h127 : Node127) (h128 : Node128) (h129 : Node129) :
    Node138Trans := by
  rintro G _ _ p A c L E h hF12 hF13 hT hEA - h3
  have hp : p.Prime := h.prime
  obtain ⟨hclL, hweylL, hcard, h11L, hGL⟩ :=
    Sec138Trans.rowNine_data h136 h138I h124b h hF12 hF13 hT hEA
  have hL24 : Nat.card (torusImage E L) = 24 := by
    obtain ⟨e⟩ := hweylL
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  obtain ⟨t0, ht0D, ht0L⟩ : ∃ t ∈ reflectionSet p E, t ∈ torusImage E L := by
    by_contra hcon
    push Not at hcon
    have hempty : reflectionSet p E ∩ (torusImage E L : Set (MulAut E)) = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun t ht => hcon t ht.1 ht.2
    have h0 := hclL
    rw [hempty, Subgroup.closure_empty] at h0
    rw [h0, Subgroup.card_bot] at hL24
    omega
  have hLX := Sec138Trans.torusImage_le_reflectionGroup hclL
  have hLone := Sec138Trans.reflections_one_class hp h3 hclL hweylL
  have hclass : ∀ b ∈ reflectionSet p E, ∃ g ∈ reflectionGroup p E, g * t0 * g⁻¹ = b := by
    intro b hb
    by_contra hnb
    obtain ⟨hbrefl, X', hX', hbX'⟩ := hb
    have hbD : b ∈ reflectionSet p E := ⟨hbrefl, X', hX', hbX'⟩
    obtain ⟨B', c', hB'adm, hc'B', hc'1, hH', hF12'⟩ := hF13.reinstantiate X' hX'
    have hT' : ¬ Outcome152Five p E B' (lieGenerated p E) := by
      rintro ⟨f, hf1, hpf, hmod, hweyl5, hc5, -, hev⟩
      exact hT ⟨f, hf1, hpf, hmod, hweyl5, hc5, hEA, hev⟩
    have hEB' : E ≠ B' := by
      intro hEB
      have h1 : Nat.card B' = p ^ 3 := hB'adm.2.2.1
      rw [← hEB, hcard] at h1
      have : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
      omega
    have hF13' := Sec13Facts.of_nodes hSchreier hTwoAction h106 h11 h122 h122b h123 h124 h125
      h126 h127 h128 h129 hH' hT'
    obtain ⟨hclX, hweylX, -, -, hGX⟩ :=
      Sec138Trans.rowNine_data h136 h138I h124b hH' hF12' hF13' hT' hEB'
    have hXX := Sec138Trans.torusImage_le_reflectionGroup hclX
    have hXone := Sec138Trans.reflections_one_class hp h3 hclX hweylX
    have hAcl : ∀ a ∈ reflectionSet p E, a ∈ torusImage E L →
        ∃ g ∈ reflectionGroup p E, g * t0 * g⁻¹ = a := by
      intro a ha haL
      obtain ⟨g, hg, hga⟩ := hLone t0 ht0D ht0L a ha haL
      exact ⟨g, hLX hg, hga⟩
    have hBcl : ∀ b' ∈ reflectionSet p E, b' ∈ torusImage E X' →
        ¬ ∃ g ∈ reflectionGroup p E, g * t0 * g⁻¹ = b' := by
      rintro b' hb' hb'X ⟨g, hg, hgb'⟩
      obtain ⟨g', hg', hg'b⟩ := hXone b hbD hbX' b' hb' hb'X
      apply hnb
      refine ⟨g'⁻¹ * g, mul_mem (inv_mem (hXX hg')) hg, ?_⟩
      rw [← hg'b] at hgb'
      calc (g'⁻¹ * g) * t0 * (g'⁻¹ * g)⁻¹ = g'⁻¹ * (g * t0 * g⁻¹) * g' := by group
        _ = g'⁻¹ * (g' * b * g'⁻¹) * g' := by rw [hgb']
        _ = b := by group
    have hcomm : ∀ y ∈ torusImage E L, ∀ z ∈ torusImage E X', y * z = z * y := fun y hy z hz =>
      Sec138Trans.commute_of_closure (S := reflectionSet p E ∩ (torusImage E L : Set (MulAut E)))
        (T := reflectionSet p E ∩ (torusImage E X' : Set (MulAut E)))
        (fun a ha b' hb' => Sec138Trans.fischer_commute hp h3 ht0D a ha.1 (hAcl a ha.1 ha.2) b'
          hb'.1 (hBcl b' hb'.1 hb'.2)) y (hclL.le hy) z (hclX.le hz)
    have hc'E : c' ∈ E := hB'adm.1 hc'B'
    have hfix := Sec138Trans.fixedByImage_eq_zpowers hH' hF12' hbrefl hbX'
    have hinv : torusInvariant E L (Subgroup.zpowers c') := by
      rw [← hfix]
      exact Sec138Trans.fixedByImage_invariant hcomm
    have hzp := Sec138Trans.zpowers_eq h hF12 h11L hcard hc'E hc'1 hinv
    have hXL := Sec138Trans.eq_of_zpowers_eq h hGL hF13.inZeroStar hH' hGX hX' hzp
    rw [hXL] at hbX'
    obtain ⟨g, hg, hgb⟩ := hLone t0 ht0D ht0L b hbD hbX'
    exact hnb ⟨g, hLX hg, hgb⟩
  intro s hs t ht
  obtain ⟨x, hx, hxs⟩ := hclass s hs
  obtain ⟨y, hy, hyt⟩ := hclass t ht
  refine ⟨y * x⁻¹, mul_mem hy (inv_mem hx), ?_⟩
  rw [← hxs, ← hyt]
  group

end CFSG.RankThree.PartOne
