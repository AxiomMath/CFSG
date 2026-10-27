module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RankOneTorusPart1

@[expose] public section

public section

namespace CFSG.StandardType.F4ExplicitPos.RankOneTorus
open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.CurtisTits CFSG.LieType.Universal
variable {K : Type} [Field K] [CharP K 2]

theorem eq_one_of_prod_zpow_cartan' {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    {B : Matrix (Fin n) (Fin n) ℤ} (hB : A * B = 1) {u : Fin n → Kˣ}
    (hu : ∀ m, ∏ j, u j ^ A j m = 1) (l : Fin n) : u l = 1 := by
  have key : ∏ m, (∏ j, u j ^ A j m) ^ B m l = u l := by
    simp only [← Finset.prod_zpow, ← zpow_mul]
    rw [Finset.prod_comm]
    simp only [← zpow_finset_sum']
    have h : ∀ j, ∑ m, A j m * B m l = if j = l then 1 else 0 := fun j => by
      have := congrFun (congrFun hB j) l
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      exact this
    simp only [h]
    rw [Finset.prod_eq_single l]
    · simp
    · intro j _ hj
      simp [hj]
    · intro h
      exact absurd (Finset.mem_univ l) h
  rw [← key]
  simp [hu]

theorem wtChar_mulSingle' (j : Fin Tag.F4.rank) (s : Kˣ) (μ : Fin Tag.F4.rank → ℤ) :
    wtChar (Pi.mulSingle j s) μ = s ^ (∑ l, Tag.cartan Tag.F4 j l * μ l) := by
  rw [wtChar, Finset.prod_eq_single j]
  · rw [Pi.mulSingle_eq_same]
  · intro b _ hb
    rw [Pi.mulSingle_eq_of_ne hb, one_zpow]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem torus_le_charSub'
    {i j : Fin Tag.F4.rank} (hij : j ≠ i) :
    torus (τ := Tag.F4) K j ≤ charSub (τ := Tag.F4) K i := by
  rintro _ ⟨s, rfl⟩
  refine ⟨Pi.mulSingle j s, by simp [hij.symm], fun b => ?_⟩
  rw [wtChar_mulSingle']
  change (torusElt Tag.F4 K j s : Module.End K (RootModule Tag.F4 K)) (Finsupp.single b 1) =
    ((s ^ (∑ l, Tag.cartan Tag.F4 j l * labelWt Tag.F4 b l) : Kˣ) : K) •
      Finsupp.single b 1
  exact torusElt_single j s b

theorem cartan_mul_cartanInvF4_check :
    Tag.cartan .F4 * CFSG.LieType.Chevalley.cartanInvF4 = 1 := by
  decide +kernel

theorem torus_iSupIndep :
    iSupIndep (torus (τ := Tag.F4) K) := by
  have hB : Tag.cartan .F4 * CFSG.LieType.Chevalley.cartanInvF4 = 1 :=
    cartan_mul_cartanInvF4_check
  intro i
  rw [disjoint_iff]
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨hgi, hgj⟩ := Subgroup.mem_inf.1 hg
  have hle : (⨆ (j) (_ : j ≠ i), torus (τ := Tag.F4) K j) ≤
      charSub (τ := Tag.F4) K i :=
    iSup₂_le fun j hj => torus_le_charSub' hj
  obtain ⟨t, ht, hchar⟩ := hle hgj
  obtain ⟨s, rfl⟩ := MonoidHom.mem_range.1 hgi
  have hm : ∀ m, s ^ Tag.cartan Tag.F4 i m = ∏ j, t j ^ Tag.cartan Tag.F4 j m := by
    intro m
    have h1 := torusElt_single i s (Sum.inr ⟨Pi.single m 1, isRoot_single Tag.F4 m⟩)
    have h2 := hchar (Sum.inr ⟨Pi.single m 1, isRoot_single Tag.F4 m⟩)
    have hsum : ∀ j, ∑ l, Tag.cartan Tag.F4 j l * labelWt Tag.F4
        (Sum.inr ⟨Pi.single m 1, isRoot_single Tag.F4 m⟩ : Label Tag.F4) l =
        Tag.cartan Tag.F4 j m := by
      intro j
      simp [labelWt, Pi.single_apply]
    simp only [hsum] at h1
    rw [wtChar] at h2
    simp only [hsum] at h2
    have h3 : (torusHom K i s : ↥(adjointGroup Tag.F4 K)) = torusElement Tag.F4 K i s := rfl
    rw [endHom_apply, h3] at h2
    change (torusElt Tag.F4 K i s : Module.End K (RootModule Tag.F4 K)) _ = _ at h2
    rw [h1] at h2
    have h4 := congrArg (fun x : RootModule Tag.F4 K =>
      x (Sum.inr ⟨Pi.single m 1, isRoot_single Tag.F4 m⟩)) h2
    simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h4
    exact Units.ext h4
  set u : Fin Tag.F4.rank → Kˣ := Function.update t i s⁻¹ with hu_def
  have hu : ∀ m, ∏ j, u j ^ Tag.cartan Tag.F4 j m = 1 := by
    intro m
    have e : ∏ j, u j ^ Tag.cartan Tag.F4 j m =
        (s⁻¹) ^ Tag.cartan Tag.F4 i m * ∏ j, t j ^ Tag.cartan Tag.F4 j m := by
      rw [← Finset.mul_prod_erase Finset.univ (fun j => u j ^ Tag.cartan Tag.F4 j m)
          (Finset.mem_univ i),
        ← Finset.mul_prod_erase Finset.univ (fun j => t j ^ Tag.cartan Tag.F4 j m)
          (Finset.mem_univ i),
        ht, one_zpow, one_mul, hu_def, Function.update_self]
      congr 1
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [e, ← hm, inv_zpow, inv_mul_cancel]
  have hs : s⁻¹ = 1 := by
    have := eq_one_of_prod_zpow_cartan' hB hu i
    rwa [hu_def, Function.update_self] at this
  rw [inv_eq_one.1 hs]
  exact map_one (torusHom K i)

section ActualF4

theorem rankOne_bruhat_f4Datum
    (i : Fin Tag.F4.rank) {g : ↥(adjointGroup Tag.F4 K)}
    (hg : g ∈ rankOne ((f4Datum K).rootGroup) i) :
    (∃ h ∈ torus (τ := Tag.F4) K i, ∃ u ∈ (f4Datum K).rootGroup (Pi.single i 1), g = h * u) ∨
      ∃ u ∈ (f4Datum K).rootGroup (Pi.single i 1), ∃ h ∈ torus (τ := Tag.F4) K i,
        ∃ v ∈ (f4Datum K).rootGroup (Pi.single i 1),
          g = u * weylElement Tag.F4 K i * h * v :=
  rankOne_bruhat (rootOperatorFamily Tag.F4) i hg

theorem eq_one_of_mem_normalizer_f4Datum
    (i : Fin Tag.F4.rank)
    {u : ↥(adjointGroup Tag.F4 K)} (hu : u ∈ (f4Datum K).rootGroup (Pi.single i 1))
    (hn : u ∈ Subgroup.normalizer ((f4Datum K).rootGroup (-Pi.single i 1) :
      Set ↥(adjointGroup Tag.F4 K))) :
    u = 1 :=
  eq_one_of_mem_normalizer (rootOperatorFamily Tag.F4) i hu hn

theorem torus_commute_f4Datum
    {i j : Fin Tag.F4.rank} {g h : ↥(adjointGroup Tag.F4 K)}
    (hg : g ∈ torus (τ := Tag.F4) K i) (hh : h ∈ torus (τ := Tag.F4) K j) : Commute g h :=
  torus_commute hg hh

theorem torus_iSupIndep_f4Datum
    : iSupIndep (torus (τ := Tag.F4) K) :=
  torus_iSupIndep

end ActualF4

end CFSG.StandardType.F4ExplicitPos.RankOneTorus

end

end
