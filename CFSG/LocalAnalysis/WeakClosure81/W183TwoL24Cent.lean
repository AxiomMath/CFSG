module

public import CFSG.LocalAnalysis.WeakClosure81.W183Mem
public import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

namespace Ctx188

variable {D : Data G} {V₀ V H : Subgroup G} {i j : ℕ}

theorem w183tp_centralizes (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T))
    (hN : calNIn H D.T = {H ⊓ D.M}) {g : G} (hgM : g ∈ D.M) {a : LGL 2 M.W}
    (hA : M.img (vInH V H g) = Subgroup.zpowers a) (hord : orderOf a = 2) :
    ∀ X : Subgroup (LGL 2 M.W), X ≤ M.img H → M.img D.T ≤ X → X ≠ M.img H →
      ∀ y ∈ X, y * a = a * y := by
  classical
  intro X hXle hTX hXne y hy
  have hDTleH : D.T ≤ H := x.hyp.hyp171.2.1
  let Xt : Subgroup G := (X.comap M.ρ).map H.subtype
  have hXtleH : Xt ≤ H := by
    intro z hz
    obtain ⟨w, -, hwz⟩ := Subgroup.mem_map.1 hz
    rw [← hwz]
    exact w.2
  have hDTleXt : D.T ≤ Xt := by
    intro t ht
    have htH : t ∈ H := hDTleH ht
    have hρ : M.ρ ⟨t, htH⟩ ∈ X :=
      hTX (M.mem_img.2 ⟨⟨t, htH⟩, ht, rfl⟩)
    exact Subgroup.mem_map.2 ⟨⟨t, htH⟩, Subgroup.mem_comap.2 hρ, rfl⟩
  have hXtneH : Xt ≠ H := by
    intro hXtH
    apply hXne
    refine le_antisymm hXle fun r hr => ?_
    obtain ⟨j, hjH, hjr⟩ := M.mem_img.1 hr
    have hjXt : (j : G) ∈ Xt := by rw [hXtH]; exact hjH
    obtain ⟨w, hw, hwj⟩ := Subgroup.mem_map.1 hjXt
    have hwj' : w = j := Subtype.ext hwj
    rw [hwj'] at hw
    rw [← hjr]
    exact Subgroup.mem_comap.1 hw
  have hXtltH : Xt < H := lt_of_le_of_ne hXtleH hXtneH
  obtain ⟨X₀, hX₀, hXle₀⟩ := exists_mem_calNIn_of_lt hDTleXt hXtltH
  rw [hN] at hX₀
  have hX₀eq : X₀ = H ⊓ D.M := by simpa using hX₀
  have hXtleM : Xt ≤ D.M := hXle₀.trans (hX₀eq.le.trans inf_le_right)
  have hyH : y ∈ M.img H := hXle hy
  obtain ⟨j, hjH, hjy⟩ := M.mem_img.1 hyH
  have hjXt : (j : G) ∈ Xt := by
    have hj : j ∈ X.comap M.ρ := by
      rw [Subgroup.mem_comap, hjy]
      exact hy
    exact Subgroup.mem_map.2 ⟨j, hj, rfl⟩
  have hjM : (j : G) ∈ D.M := hXtleM hjXt
  have hconjD : conjSubgroup D.M g = D.M :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (D.M.le_normalizer hgM)
  have hjconj : (j : G) ∈ conjSubgroup D.M g := by rw [hconjD]; exact hjM
  have hnorm := Hyp183.img_normalizer_of_mem_conj (g := g) x.hyp M j.2 hjconj
  have hnorm' : y ∈ Subgroup.normalizer (Subgroup.zpowers a : Set (LGL 2 M.W)) := by
    rw [← hjy]
    rw [hA] at hnorm
    exact hnorm
  have hconjmem : y * a * y⁻¹ ∈ Subgroup.zpowers a :=
    ((Subgroup.mem_normalizer_iff.mp hnorm') a).mp (Subgroup.mem_zpowers a)
  have hane : a ≠ 1 := by
    intro hone
    rw [hone, orderOf_one] at hord
    norm_num at hord
  have hconjne : y * a * y⁻¹ ≠ 1 := by
    intro hone
    apply hane
    calc a = y⁻¹ * (y * a * y⁻¹) * y := by group
      _ = y⁻¹ * 1 * y := by rw [hone]
      _ = 1 := by group
  rw [mem_zpowers_iff_mem_range_orderOf] at hconjmem
  obtain ⟨i, hi_mem, hi_eq⟩ := Finset.mem_image.mp hconjmem
  rw [hord, Finset.mem_range] at hi_mem
  interval_cases i
  · rw [pow_zero] at hi_eq
    exact (hconjne hi_eq.symm).elim
  · rw [pow_one] at hi_eq
    have key : a * y = y * a := by
      calc a * y = (y * a * y⁻¹) * y := by
            simpa using congrArg (fun z => z * y) hi_eq
        _ = y * a := by group
    exact key.symm

end Ctx188

theorem w183tp_asch210_split {T L : Subgroup G}
    (h : Set.ncard {X : Subgroup G | ∃ t ∈ T, X = conjSubgroup L t} ≤ 2) :
    (∀ t ∈ T, conjSubgroup L t = L) ∨
      ∃ t ∈ T, conjSubgroup L t ≠ L ∧
        ∀ s ∈ T, conjSubgroup L s = L ∨ conjSubgroup L s = conjSubgroup L t := by
  classical
  by_cases hall : ∀ t ∈ T, conjSubgroup L t = L
  · exact Or.inl hall
  · obtain ⟨t, htT, htne⟩ : ∃ t ∈ T, conjSubgroup L t ≠ L := by
      push Not at hall
      exact hall
    refine Or.inr ⟨t, htT, htne, ?_⟩
    let S : Set (Subgroup G) := {X | ∃ t ∈ T, X = conjSubgroup L t}
    have hLmem : L ∈ S := ⟨1, T.one_mem, (conjSubgroup_one L).symm⟩
    have htmem : conjSubgroup L t ∈ S := ⟨t, htT, rfl⟩
    have hsub : ({L, conjSubgroup L t} : Set (Subgroup G)) ⊆ S := by
      intro X hX
      rcases hX with hX | hX
      · rw [hX]; exact hLmem
      · rw [hX]; exact htmem
    have hpair : ({L, conjSubgroup L t} : Set (Subgroup G)).ncard = 2 :=
      Set.ncard_pair fun heq => htne heq.symm
    have heq : ({L, conjSubgroup L t} : Set (Subgroup G)) = S :=
      Set.eq_of_subset_of_ncard_le hsub (by rw [hpair]; exact h)
    intro s hsT
    have hs : conjSubgroup L s ∈ S := ⟨s, hsT, rfl⟩
    rw [← heq] at hs
    rcases hs with hs | hs
    · exact Or.inl hs
    · exact Or.inr hs

private theorem w183_card_isL2_two {X : Type} [Group X] (h : IsL2 X 2) : Nat.card X = 60 := by
  have hs := CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel
    (G := X) (t := .PSL) (n := 2) (p := 2) (f := 2) (by decide) h
  have h1 := (CFSG.Timmesfeld.card_statedClassicalModel_two
    (G := X) (t := .PSL) (n := 2) (f := 2) hs).1 rfl
  rw [h1]
  norm_num [CFSG.Open.ordA]

private theorem w183_card_isU3_two {X : Type} [Group X] (h : IsU3 X 2) : Nat.card X = 62400 := by
  have hs := CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel
    (G := X) (t := .PSU) (n := 3) (p := 2) (f := 2) (by decide) h
  have h1 := (CFSG.Timmesfeld.card_statedClassicalModel_two
    (G := X) (t := .PSU) (n := 3) (f := 2) hs).2.1 rfl
  rw [h1]
  decide

theorem w183tp_shape_base {X : Type} [Group X] (h : IsL2 X 2 ∨ IsU3 X 2) :
    IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  have hsimple : IsSimpleGroup X := by
    rcases h with hL2 | hU3
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU3
  refine ⟨hsimple, ?_⟩
  by_contra hcon
  have hcomm : IsMulCommutative X := ⟨⟨fun a b => by
    by_contra hab
    exact hcon ⟨a, b, hab⟩⟩⟩
  have hprime : (Nat.card X).Prime := Group.is_simple_iff_prime_card.mp hsimple
  rcases h with hL2 | hU3
  · have hc := w183_card_isL2_two hL2
    have h3 : 3 ∣ Nat.card X := by rw [hc]; norm_num
    have h31 : 3 = Nat.card X := (hprime.eq_one_or_self_of_dvd 3 h3).resolve_left (by norm_num)
    omega
  · have hc := w183_card_isU3_two hU3
    have h3 : 3 ∣ Nat.card X := by rw [hc]; norm_num
    have h31 : 3 = Nat.card X := (hprime.eq_one_or_self_of_dvd 3 h3).resolve_left (by norm_num)
    omega

theorem w183tp_shape_dvd {K L : Subgroup G}
    (h : HasQuotShape L (K : Set G) (fun X _ => IsL2 X 2 ∨ IsU3 X 2)) :
    3 ∣ K.relIndex L := by
  obtain ⟨X, _, φ, hφs, hφk, hP⟩ := h
  have hker : φ.ker = K.subgroupOf L := by
    ext k
    rw [MonoidHom.mem_ker, hφk k, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  have hcard : K.relIndex L = Nat.card X := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv
  rw [hcard]
  rcases hP with hL2 | hU3
  · rw [w183_card_isL2_two hL2]; norm_num
  · rw [w183_card_isU3_two hU3]; norm_num

theorem w183tp_shape_cj {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {A : Subgroup (LGL 2 V)} (y : LGL 2 V) (h : IsL2 ↥A 2 ∨ IsU3 ↥A 2) :
    IsL2 ↥(cj y A) 2 ∨ IsU3 ↥(cj y A) 2 := by
  rcases h with hL2 | hU3
  · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv
      (Subgroup.equivMapOfInjective A (MulAut.conj y).toMonoidHom
        (MulAut.conj y).injective) hL2)
  · exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv
      (Subgroup.equivMapOfInjective A (MulAut.conj y).toMonoidHom
        (MulAut.conj y).injective) hU3)

end CFSG.LocalAnalysis.WeakClosure81

end
