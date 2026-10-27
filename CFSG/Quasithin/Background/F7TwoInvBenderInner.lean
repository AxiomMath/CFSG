module

public import CFSG.Quasithin.Background.F7TwoInvAutWrap
public import CFSG.GH74.Uniqueness.Bender.Commuting
public import CFSG.GH74.Uniqueness.Section4Bender

public section

namespace CFSG.Quasithin.F7Two

open CFSG.GH74.Uniqueness.Bender
open CFSG.GH74.Uniqueness (isSimpleGroup_of_isBenderGroup exists_not_commute_of_isBenderGroup)
open CFSG.BenderSuzuki (IsBenderGroup)

theorem exists_central_involution_of_isPGroup {D : Type*} [Group D] [Finite D] [Nontrivial D]
    (hD : IsPGroup 2 D) : ∃ z ∈ Subgroup.center D, z * z = 1 ∧ z ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hD.center_nontrivial
  have hdvd : 2 ∣ Nat.card (Subgroup.center D) := by
    rcases (hD.to_subgroup (Subgroup.center D)).card_eq_or_dvd with h | h
    · exact absurd h (Finite.one_lt_card.ne')
    · exact h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hz2 : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hz, sq] at h
  refine ⟨z, z.2, congrArg Subtype.val hz2, fun h1 => ?_⟩
  have : z = 1 := Subtype.ext h1
  rw [this, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem commute_of_isPGroup_closure_involutions {K : Type*}
    [Group K] [Finite K] {n i e : ℕ} (h : BenderType K n i e) {a b : K} (ha : a * a = 1)
    (hb : b * b = 1) (hP : IsPGroup 2 ↥(Subgroup.closure ({a, b} : Set K))) :
    a * b = b * a := by
  by_cases ha1 : a = 1
  · rw [ha1, one_mul, mul_one]
  set D : Subgroup K := Subgroup.closure ({a, b} : Set K) with hD
  have haD : a ∈ D := Subgroup.subset_closure (Set.mem_insert _ _)
  have hbD : b ∈ D := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have : Nontrivial D := ⟨⟨⟨a, haD⟩, 1, fun h1 => ha1 (congrArg Subtype.val h1)⟩⟩
  obtain ⟨z, hzc, hz2, hz1⟩ := exists_central_involution_of_isPGroup hP
  have hzD := Subgroup.mem_center_iff.mp hzc
  refine h.commute_of_commute_involutions (z := (z : K)) ha (congrArg Subtype.val hz2) hb
    (fun h1 => hz1 (Subtype.ext h1)) ?_ ?_
  · exact congrArg Subtype.val (hzD ⟨a, haD⟩)
  · exact congrArg Subtype.val (hzD ⟨b, hbD⟩)

variable {L : Type*} [Group L]

theorem invAutGen_conj_of_two_adjacent_commute [Finite L] (hs : IsSimpleGroup L)
    (hnonab : ∃ x y : L, x * y ≠ y * x) {g : L} (hg2 : g * g = 1) (hg1 : g ≠ 1)
    (hdih : ∀ x : L, IsPGroup 2 ↥(Subgroup.closure ({g, x * g * x⁻¹} : Set L)) →
      g * (x * g * x⁻¹) = (x * g * x⁻¹) * g) : InvAutGen L (MulAut.conj g) := by
  have := hs
  have hZ := center_eq_bot_of_isSimpleGroup hs hnonab
  rw [invAutGen_iff_invGen_range (f := MonoidHom.id L) Function.injective_id (a := g)
    (φ := MulAut.conj g) (fun x => by simp [MulAut.conj_apply]),
    MonoidHom.range_eq_top.mpr Function.surjective_id]
  have hac : ∃ x ∈ (⊤ : Subgroup L), g * x ≠ x * g := by
    by_contra hcon
    push Not at hcon
    apply hg1
    have : g ∈ Subgroup.center L :=
      Subgroup.mem_center_iff.mpr fun x => (hcon x (Subgroup.mem_top x)).symm
    rwa [hZ, Subgroup.mem_bot] at this
  have hnonab' : ∃ x y : ↥(⊤ : Subgroup L), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnonab
    exact ⟨⟨x, Subgroup.mem_top x⟩, ⟨y, Subgroup.mem_top y⟩,
      fun h => hxy (congrArg Subtype.val h)⟩
  exact invGen_of_two_adjacent_commute Subgroup.topEquiv.isSimpleGroup hnonab' hg2
    (fun x _ => Subgroup.mem_top _) hac fun x _ hP => hdih x hP

theorem invAutGen_conj_of_benderType {K : Type*} [Group K]
    [Finite K] {n i e : ℕ} (h : BenderType K n i e) {g : K} (hg2 : g * g = 1) (hg1 : g ≠ 1) :
    InvAutGen K (MulAut.conj g) := by
  have hB : IsBenderGroup K := isBenderGroup_iff_exists_benderType.mpr ⟨n, i, e, h⟩
  refine invAutGen_conj_of_two_adjacent_commute (isSimpleGroup_of_isBenderGroup hB)
    (exists_not_commute_of_isBenderGroup hB) hg2 hg1 fun x hP => ?_
  refine commute_of_isPGroup_closure_involutions h hg2 ?_ hP
  calc x * g * x⁻¹ * (x * g * x⁻¹) = x * (g * g) * x⁻¹ := by group
    _ = 1 := by rw [hg2]; group

end CFSG.Quasithin.F7Two
