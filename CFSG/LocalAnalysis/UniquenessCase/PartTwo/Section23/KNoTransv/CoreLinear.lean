module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.Defs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs28
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.SectionIrr
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv

open CFSG.HardMathSupport.Solomon CFSG.ComponentClassification.OutcomeLocal

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M]

local notation "𝔾" => LinearMap.GeneralLinearGroup (ZMod 2) M

section Helpers

variable {G : Type*} [Group G]

private theorem finite_generalLinearGroup {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] : Finite (LinearMap.GeneralLinearGroup (ZMod 2) V) :=
  Finite.of_injective (fun f : LinearMap.GeneralLinearGroup (ZMod 2) V => (f : V → V))
    fun f g h => Units.ext (LinearMap.ext fun x => congrFun h x)

private theorem mem_conjClosure_self (H : Subgroup G) (s : G) : s ∈ conjClosure H s :=
  Subgroup.subset_closure ⟨1, H.one_mem, by simp⟩

private theorem conjClosure_le_conjClosure {H D : Subgroup G} (hHD : H ≤ D) (s : G) :
    conjClosure H s ≤ conjClosure D s := by
  apply Subgroup.closure_mono
  rintro x ⟨h, hh, rfl⟩
  exact ⟨h, hHD hh, rfl⟩

private theorem conjClosure_le_normalizer {H : Subgroup G} {s : G}
    (hs : s ∈ Subgroup.normalizer (H : Set G)) :
    conjClosure H s ≤ Subgroup.normalizer (H : Set G) := by
  unfold conjClosure
  rw [Subgroup.closure_le]
  rintro x ⟨g, hg, rfl⟩
  have hgN : g ∈ Subgroup.normalizer (H : Set G) := Subgroup.le_normalizer hg
  have h1 : g⁻¹ * s ∈ Subgroup.normalizer (H : Set G) :=
    Subgroup.mul_mem (H := Subgroup.normalizer (H : Set G)) (Subgroup.inv_mem _ hgN) hs
  exact Subgroup.mul_mem (H := Subgroup.normalizer (H : Set G)) h1 hgN

private def cosetUnion (H : Subgroup G) (s : G) (hs : s ∈ Subgroup.normalizer (H : Set G))
    (hs2 : s * s = 1) : Subgroup G where
  carrier := {x | x ∈ H ∨ ∃ h ∈ H, x = h * s}
  one_mem' := Or.inl H.one_mem
  mul_mem' := by
    have hnorm : ∀ y ∈ H, s * y * s⁻¹ ∈ H := fun y hy =>
      (Subgroup.mem_normalizer_iff.mp hs y).mp hy
    rintro x y (hx | ⟨a, ha, rfl⟩) (hy | ⟨b, hb, rfl⟩)
    · exact Or.inl (H.mul_mem hx hy)
    · exact Or.inr ⟨x * b, H.mul_mem hx hb, by group⟩
    · refine Or.inr ⟨a * (s * y * s⁻¹), H.mul_mem ha (hnorm y hy), ?_⟩
      group
    · refine Or.inl ?_
      have hb' : s * b * s⁻¹ ∈ H := hnorm b hb
      have h : a * s * (b * s) = a * (s * b * s⁻¹) * (s * s) := by group
      rw [h, hs2, mul_one]
      exact H.mul_mem ha hb'
  inv_mem' := by
    have hnorm : ∀ y ∈ H, s * y * s⁻¹ ∈ H := fun y hy =>
      (Subgroup.mem_normalizer_iff.mp hs y).mp hy
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
    rintro x (hx | ⟨a, ha, rfl⟩)
    · exact Or.inl (H.inv_mem hx)
    · refine Or.inr ⟨s * a⁻¹ * s⁻¹, hnorm a⁻¹ (H.inv_mem ha), ?_⟩
      rw [mul_inv_rev, hsinv, mul_assoc (s * a⁻¹) s s, hs2, mul_one]

private theorem conjClosure_le_cosetUnion {H : Subgroup G} {s : G}
    (hs : s ∈ Subgroup.normalizer (H : Set G)) (hs2 : s * s = 1) :
    conjClosure H s ≤ cosetUnion H s hs hs2 := by
  unfold conjClosure
  rw [Subgroup.closure_le]
  rintro x ⟨g, hg, rfl⟩
  have hmem : g⁻¹ * (s * g * s⁻¹) ∈ H :=
    H.mul_mem (H.inv_mem hg) ((Subgroup.mem_normalizer_iff.mp hs g).mp hg)
  refine Or.inr ⟨g⁻¹ * (s * g * s⁻¹), hmem, ?_⟩
  group

end Helpers

private theorem exists_pow_four_ne_one [Finite M] {H : Subgroup 𝔾} (hH : ⁅H, H⁆ = H)
    (hH1 : H ≠ ⊥) : ∃ x ∈ H, x ^ 4 ≠ 1 := by
  by_contra h
  push Not at h
  haveI : Finite 𝔾 := finite_generalLinearGroup
  haveI : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hH1
  have hP : IsPGroup 2 ↥H := by
    rw [isPGroup_iff_exists_orderOf_dvd_pow]
    refine ⟨2, fun g => ?_⟩
    have hg4 : g ^ 4 = 1 := by
      apply Subtype.ext
      simpa using h (g : 𝔾) g.2
    rw [show 2 ^ 2 = 4 by norm_num]
    exact orderOf_dvd_iff_pow_eq_one.mpr hg4
  have hperf : Group.IsPerfect ↥H := Subgroup.isPerfect_iff.mpr hH
  exact Group.IsPerfect.not_isNilpotent ↥H (IsPGroup.isNilpotent hP)

theorem exists_mcLaughlin_quotient_linear [Finite M] {H : Subgroup 𝔾} (hH : ⁅H, H⁆ = H)
    (hH1 : H ≠ ⊥) {τ : 𝔾} (hτ : IsF2Transvection τ) (hτN : τ ∈ Subgroup.normalizer (H : Set 𝔾))
    (hgen : H ≤ conjClosure H τ) :
    ∃ (T : Type) (_ : Group T) (_ : IsSimpleGroup T) (ψ : ↥H →* T),
      Function.Surjective ψ ∧ (∀ h ∈ ψ.ker, h ^ 4 = 1) ∧ (∃ a b : T, a * b ≠ b * a) ∧
      ∃ (W : Type) (_ : Group W) (_ : Finite W) (c : ℕ),
        UniquenessMaximal.IsMcLaughlinGroup W ∧ (c = 1 ∨ c = 2) ∧ Nat.card T * c = Nat.card W ∧
        ∀ n : ℕ, Nonempty (W ≃* Equiv.Perm (Fin n)) → c = 2 := by
  classical
  haveI : Finite 𝔾 := finite_generalLinearGroup
  have hτ2 : τ * τ = 1 := by
    obtain ⟨φ, a, h, -, -, rfl⟩ := (isF2Transvection_iff τ).mp hτ
    exact tv_mul_self φ a h
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ2
  let D : Subgroup 𝔾 := conjClosure H τ
  have hHD : H ≤ D := hgen
  have hτD : τ ∈ D := mem_conjClosure_self H τ
  have hDgen : D ≤ conjClosure D τ := conjClosure_le_conjClosure hHD τ
  have hDN : D ≤ Subgroup.normalizer (H : Set 𝔾) := conjClosure_le_normalizer hτN
  have hHnD : (H.subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHD).mpr hDN
  obtain ⟨x, hxH, hx4⟩ := exists_pow_four_ne_one hH hH1
  have hD4 : ∃ y ∈ D, y ^ 4 ≠ 1 := ⟨x, hHD hxH, hx4⟩
  obtain ⟨V, hVadd, hVmod, hVfin, ρ, hMcL, hker4⟩ :=
    exists_section hτ hτD hDgen hD4
  letI := hVadd
  letI := hVmod
  letI := hVfin
  let W := ↥ρ.range
  letI : Group W := inferInstance
  haveI : Finite (LinearMap.GeneralLinearGroup (ZMod 2) V) := finite_generalLinearGroup
  letI : Finite W := inferInstance
  let T₀ : Subgroup W := (H.subgroupOf D).map ρ.rangeRestrict
  have hT₀n : T₀.Normal := hHnD.map ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hsub : ⁅H.subgroupOf D, H.subgroupOf D⁆ = H.subgroupOf D := by
    refine (Subgroup.map_injective D.subtype_injective).eq_iff.mp ?_
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hHD, hH]
  have hT₀comm : ⁅T₀, T₀⁆ = T₀ := by
    change ⁅(H.subgroupOf D).map ρ.rangeRestrict, (H.subgroupOf D).map ρ.rangeRestrict⁆ =
      (H.subgroupOf D).map ρ.rangeRestrict
    rw [← Subgroup.map_commutator, hsub]
  have hT₀1 : T₀ ≠ ⊥ := by
    intro hbot
    have hbot' : Subgroup.map ρ.rangeRestrict (H.subgroupOf D) = ⊥ := hbot
    have hle' : H.subgroupOf D ≤ ρ.rangeRestrict.ker :=
      (Subgroup.map_eq_bot_iff (f := ρ.rangeRestrict) (H.subgroupOf D)).mp hbot'
    have hle : H.subgroupOf D ≤ ρ.ker := by
      intro d hd
      rw [MonoidHom.mem_ker]
      have h1 : ρ.rangeRestrict d = 1 := by
        simpa using MonoidHom.mem_ker.mp (hle' hd)
      have := congrArg (fun w : W => (w : LinearMap.GeneralLinearGroup (ZMod 2) V)) h1
      simpa using this
    have hxker : (⟨x, hHD hxH⟩ : ↥D) ∈ ρ.ker :=
      hle (show (⟨x, hHD hxH⟩ : ↥D) ∈ H.subgroupOf D from hxH)
    have hx4' : x ^ 4 = 1 := by
      have := congrArg (fun d : ↥D => (d : 𝔾)) (hker4 _ hxker)
      simpa using this
    exact hx4 hx4'
  obtain ⟨hT₀simple, hT₀nonab, hT₀neTop⟩ :=
    isSimpleGroup_of_isMcLaughlinGroup hMcL hT₀n hT₀comm hT₀1
  let f : ↥H →* W := ρ.rangeRestrict.comp (Subgroup.inclusion hHD)
  have hfmem : ∀ h : ↥H, f h ∈ T₀ := fun h =>
    Subgroup.mem_map_of_mem ρ.rangeRestrict
      (show Subgroup.inclusion hHD h ∈ H.subgroupOf D from h.2)
  let ψ : ↥H →* ↥T₀ := f.codRestrict T₀ hfmem
  have hψsurj : Function.Surjective ψ := by
    intro t
    obtain ⟨d, hd, hdt⟩ := Subgroup.mem_map.mp t.2
    refine ⟨⟨(d : ↥D).1, hd⟩, ?_⟩
    apply Subtype.ext
    change ρ.rangeRestrict (Subgroup.inclusion hHD ⟨(d : ↥D).1, hd⟩) = (t : W)
    have hincl : Subgroup.inclusion hHD ⟨(d : ↥D).1, hd⟩ = d := Subtype.ext rfl
    rw [hincl]
    exact hdt
  have hψker : ∀ h ∈ ψ.ker, h ^ 4 = 1 := by
    intro h hh
    have h1 : f h = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hh)
      simpa [ψ] using this
    have hincl : Subgroup.inclusion hHD h ∈ ρ.ker := by
      rw [MonoidHom.mem_ker]
      have := congrArg (fun w : W => (w : LinearMap.GeneralLinearGroup (ZMod 2) V)) h1
      simpa [f] using this
    apply Subtype.ext
    have h4 := congrArg (fun d : ↥D => (d : 𝔾)) (hker4 _ hincl)
    simpa using h4
  have hcvd : T₀.index ∣ 2 := by
    rw [Subgroup.index_dvd_two_iff']
    refine ⟨ρ.rangeRestrict ⟨τ, hτD⟩, fun b => ?_⟩
    obtain ⟨d, rfl⟩ := ρ.rangeRestrict_surjective b
    rcases conjClosure_le_cosetUnion hτN hτ2 d.2 with hd | ⟨h, hh, hdh⟩
    · right
      exact Subgroup.mem_map_of_mem ρ.rangeRestrict
        (show d ∈ H.subgroupOf D from hd)
    · left
      have hmem : (⟨τ, hτD⟩ * d : ↥D) ∈ H.subgroupOf D := by
        show (τ * (d : 𝔾)) ∈ H
        rw [hdh, show τ * (h * τ) = τ * h * τ⁻¹ by rw [hτinv]; group]
        exact (Subgroup.mem_normalizer_iff.mp hτN h).mp hh
      have := Subgroup.mem_map_of_mem ρ.rangeRestrict hmem
      simpa only [map_mul] using this
  have hc12 : T₀.index = 1 ∨ T₀.index = 2 :=
    (Nat.dvd_prime Nat.prime_two).mp hcvd
  refine ⟨↥T₀, inferInstance, hT₀simple, ψ, hψsurj, hψker, hT₀nonab,
    W, inferInstance, inferInstance, T₀.index, hMcL, hc12, T₀.card_mul_index, ?_⟩
  intro n hn
  rcases hc12 with h | h
  · exact absurd (Subgroup.index_eq_one.mp h) (hT₀neTop n hn)
  · exact h

end CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv
