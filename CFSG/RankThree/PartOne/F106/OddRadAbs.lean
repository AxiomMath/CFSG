module

import CFSG.LieType.SteinbergBRMulEquivCores
import CFSG.GroupTheory.ABGLocalTools.Constraint
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG CFSG.SignalizerFunctorTheorem.Nonsolvable
open scoped commutatorElement

section Abstract

theorem map_perfectResidual_eq_of_commutator_le {G : Type*} [Group G] [Finite G]
    {C N : Subgroup G} (hNC : N ≤ C) (hC : ⁅C, C⁆ ≤ N) :
    (perfectResidual ↥C).map C.subtype = (perfectResidual ↥N).map N.subtype := by
  apply le_antisymm
  · have key : ∀ k : ℕ, (derivedSeries ↥C (k + 1)).map C.subtype ≤
        (derivedSeries ↥N k).map N.subtype := by
      intro k
      induction k with
      | zero =>
        rw [derivedSeries_one, derivedSeries_zero, Subgroup.map_top, Subgroup.range_subtype,
          commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
        exact hC
      | succ k ih =>
        rw [derivedSeries_succ, Subgroup.map_commutator, derivedSeries_succ (G := ↥N) k,
          Subgroup.map_commutator]
        exact Subgroup.commutator_mono ih ih
    have hN : (perfectResidual ↥N).map N.subtype =
        ⨅ k, (derivedSeries ↥N k).map N.subtype := by
      rw [perfectResidual, Subgroup.map_iInf _ N.subtype_injective]
    rw [hN]
    refine le_iInf fun k => ?_
    have h1 : (perfectResidual ↥C).map C.subtype ≤
        (derivedSeries ↥C (k + 1)).map C.subtype :=
      Subgroup.map_mono (iInf_le _ (k + 1))
    exact h1.trans (key k)
  · exact le_perfectResidual_map_of_isPerfect (isPerfect_perfectResidual_map N)
      ((Subgroup.map_subtype_le _).trans hNC)

theorem card_rad_perfectResidual_eq_of_commutator_le {G : Type*} [Group G] [Finite G]
    {C N : Subgroup G} (hNC : N ≤ C) (hC : ⁅C, C⁆ ≤ N) :
    Nat.card ↥(solvableRadical ↥(perfectResidual ↥C)) =
      Nat.card ↥(solvableRadical ↥(perfectResidual ↥N)) := by
  have h := map_perfectResidual_eq_of_commutator_le hNC hC
  let ε : ↥(perfectResidual ↥C) ≃* ↥(perfectResidual ↥N) :=
    ((perfectResidual ↥C).equivMapOfInjective C.subtype C.subtype_injective).trans
      ((MulEquiv.subgroupCongr h).trans
        ((perfectResidual ↥N).equivMapOfInjective N.subtype N.subtype_injective).symm)
  rw [← CFSG.LieType.SteinbergBR.solvableRadical_map_equiv ε,
    Subgroup.card_map_of_injective ε.injective]

theorem card_rad_perfectResidual_dvd_of_surjective {G H : Type*} [Group G] [Group H] [Finite G]
    (f : G →* H) (hf : Function.Surjective f) (hk : Group.IsSolvable f.ker) :
    Nat.card ↥(solvableRadical ↥(perfectResidual H)) ∣
      Nat.card ↥(solvableRadical ↥(perfectResidual G)) := by
  classical
  have : Finite H := Finite.of_surjective f hf
  have hmap : (perfectResidual G).map f = perfectResidual H :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq f hf
  let g : ↥(perfectResidual G) →* ↥(perfectResidual H) :=
    (f.comp (perfectResidual G).subtype).codRestrict (perfectResidual H) (fun x => by
      rw [← hmap]; exact ⟨x, x.2, rfl⟩)
  have hg : Function.Surjective g := by
    intro y
    have h1 : (y : H) ∈ (perfectResidual G).map f := by rw [hmap]; exact y.2
    obtain ⟨x, hx, hxy⟩ := h1
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  set R : Subgroup ↥(perfectResidual H) := solvableRadical ↥(perfectResidual H) with hR
  have hRn : R.Normal := inferInstance
  have hRs : Group.IsSolvable R := CFSG.ABGLocalTools.solvableRadical_isSolvable
  set S : Subgroup ↥(perfectResidual G) := R.comap g with hS
  have hSn : S.Normal := hRn.comap g
  let gS : ↥S →* ↥R := (g.comp S.subtype).codRestrict R (fun x => x.2)
  have hgS : Function.Surjective gS := by
    intro r
    obtain ⟨x, hx⟩ := hg r.1
    exact ⟨⟨x, show g x ∈ R from hx ▸ r.2⟩, Subtype.ext hx⟩
  have hSs : Group.IsSolvable S := by
    have hker : Group.IsSolvable ↥gS.ker := by
      let φ : ↥gS.ker →* ↥f.ker :=
        ((perfectResidual G).subtype.comp (S.subtype.comp gS.ker.subtype)).codRestrict f.ker
          (fun x => by
            have h1 : gS x.1 = 1 := x.2
            have h3 : g (S.subtype x.1) = 1 := congrArg Subtype.val h1
            exact congrArg Subtype.val h3)
      have hinj : Function.Injective φ := by
        intro a b hab
        have h4 : ((perfectResidual G).subtype.comp (S.subtype.comp gS.ker.subtype)) a =
            ((perfectResidual G).subtype.comp (S.subtype.comp gS.ker.subtype)) b :=
          congrArg (fun z : ↥f.ker => (z : G)) hab
        exact ((perfectResidual G).subtype_injective.comp
          (S.subtype_injective.comp gS.ker.subtype_injective)) h4
      exact Group.isSolvable_of_isSolvable_injective (f := φ) hinj
    exact Group.isSolvable_of_ker_le_range gS.ker.subtype gS (by
      intro w hw
      exact ⟨⟨w, hw⟩, rfl⟩)
  have hSle : S ≤ solvableRadical ↥(perfectResidual G) := le_solvableRadical hSn hSs
  exact (Subgroup.card_dvd_of_surjective hgS).trans (Subgroup.card_dvd_of_le hSle)

theorem commutatorElement_mul_central_left {G : Type*} [Group G] (s y z : G)
    (hz : z ∈ Subgroup.center G) : ⁅s * z, y⁆ = ⁅s, y⁆ := by
  have h : z * y * z⁻¹ = y := by
    rw [← Subgroup.mem_center_iff.mp hz y]; group
  calc ⁅s * z, y⁆ = s * (z * y * z⁻¹) * s⁻¹ * y⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = ⁅s, y⁆ := by rw [h]; simp only [commutatorElement_def]

theorem commutatorElement_mul_central_right {G : Type*} [Group G] (s t w : G)
    (hw : w ∈ Subgroup.center G) : ⁅s, t * w⁆ = ⁅s, t⁆ := by
  calc ⁅s, t * w⁆ = s * t * (w * s⁻¹ * w⁻¹) * t⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = ⁅s, t⁆ := by
      have h' : w * s⁻¹ * w⁻¹ = s⁻¹ := by
        rw [← Subgroup.mem_center_iff.mp hw s⁻¹]; group
      rw [h']; simp only [commutatorElement_def]

theorem isPerfect_of_isSimpleGroup_nonabelian {G : Type*} [Group G] [IsSimpleGroup G]
    (h : ∃ a b : G, a * b ≠ b * a) : Group.IsPerfect G := by
  refine ⟨?_⟩
  rcases (inferInstance : (commutator G).Normal).eq_bot_or_eq_top with hb | ht
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    apply hab
    have hmem : ⁅a, b⁆ ∈ commutator G :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [hb, Subgroup.mem_bot, commutatorElement_def] at hmem
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [hmem, one_mul]
  · exact ht

end Abstract

theorem eq_one_of_sq_eq_one_of_odd_card {Y : Type*} [Group Y] (hY : Odd (Nat.card Y)) {y : Y}
    (hy : y ^ 2 = 1) : y = 1 := by
  have h1 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hy
  have h2 : orderOf y ∣ Nat.card Y := orderOf_dvd_natCard y
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exfalso
    rw [h] at h2
    exact (Nat.not_even_iff_odd.mpr hY) (even_iff_two_dvd.mpr h2)

theorem odd_card_rad_perfectResidual_pi {ι : Type*} [Finite ι] {G : ι → Type*}
    [∀ i, Group (G i)] [∀ i, Finite (G i)]
    (h : ∀ i, Odd (Nat.card ↥(solvableRadical ↥(perfectResidual (G i))))) :
    Odd (Nat.card ↥(solvableRadical ↥(perfectResidual (∀ i, G i)))) := by
  classical
  have : Finite (∀ i, G i) := inferInstance
  set P : Subgroup (∀ i, G i) := perfectResidual (∀ i, G i) with hPdef
  have hmap : ∀ i, P.map (Pi.evalMonoidHom G i) = perfectResidual (G i) := fun i =>
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq (Pi.evalMonoidHom G i)
      (Function.surjective_eval i)
  let g : ∀ i, ↥P →* ↥(perfectResidual (G i)) := fun i =>
    ((Pi.evalMonoidHom G i).comp P.subtype).codRestrict (perfectResidual (G i)) (fun x => by
      rw [← hmap i]; exact ⟨x, x.2, rfl⟩)
  have hg : ∀ i, Function.Surjective (g i) := by
    intro i y
    have h1 : (y : G i) ∈ P.map (Pi.evalMonoidHom G i) := by rw [hmap i]; exact y.2
    obtain ⟨x, hx, hxy⟩ := h1
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  set R : Subgroup ↥P := solvableRadical ↥P with hR
  by_contra hodd
  have heven : 2 ∣ Nat.card R := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' (G := ↥R) 2 heven
  have hr2 : r ^ 2 = 1 := by rw [← hr]; exact pow_orderOf_eq_one r
  have hr1 : r ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hr
    exact absurd hr (by norm_num)
  apply hr1
  have hRs : Group.IsSolvable R := CFSG.ABGLocalTools.solvableRadical_isSolvable
  have hall : ∀ i, g i (r : ↥P) = 1 := by
    intro i
    have hn : (R.map (g i)).Normal := (inferInstance : R.Normal).map (g i) (hg i)
    have hs : Group.IsSolvable ↥(R.map (g i)) := Group.isSolvable_of_surjective
      ((g i).subgroupMap_surjective R)
    have hle : R.map (g i) ≤ solvableRadical ↥(perfectResidual (G i)) :=
      le_solvableRadical hn hs
    have hmem : g i (r : ↥P) ∈ solvableRadical ↥(perfectResidual (G i)) :=
      hle ⟨r, r.2, rfl⟩
    have hy2 : (⟨g i (r : ↥P), hmem⟩ :
        ↥(solvableRadical ↥(perfectResidual (G i)))) ^ 2 = 1 := by
      apply Subtype.ext
      show g i (r : ↥P) ^ 2 = 1
      rw [← map_pow]
      have : (r : ↥P) ^ 2 = 1 := congrArg Subtype.val hr2
      rw [this, map_one]
    have := eq_one_of_sq_eq_one_of_odd_card (h i) hy2
    exact congrArg Subtype.val this
  apply Subtype.ext
  apply Subtype.ext
  funext i
  have := congrArg Subtype.val (hall i)
  exact this

end CFSG.RankThree.PartOne.F106
