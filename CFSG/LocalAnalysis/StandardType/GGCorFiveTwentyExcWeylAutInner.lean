module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcDiagramAutomorphisms
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcRootFamilyConjugacy
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcRootReflectionRelations
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylOuterTransport
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylReflectionOfFixedPoints
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylNormDefs

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley.SimplyLacedCover

variable {τ : Tag} {p : ℕ}

theorem exists_rootFamily_of_fixCount [Fact p.Prime] (hp2 : p ≠ 2)
    (hτ : ∀ i, τ.symmetrizer i i = 1) (hr : 0 < τ.rank) (α : MulAut (WeylGroup τ))
    (hfix : ∀ i, Nat.card {f : Multiplicative (Fin τ.rank → ZMod p) //
      ExcWeylOuter.torusMulAut τ p (α (simple τ i)) f = f} = p ^ (τ.rank - 1)) :
    ∃ β : Fin τ.rank → Fin τ.rank → ℤ, (∀ i, IsRoot τ (β i)) ∧
      ∀ i, α (simple τ i) = rootReflection (β i) := by
  have hw : ∀ i, α (simple τ i) * α (simple τ i) = 1 := fun i => by
    rw [← map_mul, (coxeterSystem τ).simple_mul_simple_self, map_one]
  have hw1 : ∀ i, α (simple τ i) ≠ 1 := fun i h =>
    (coxeterSystem τ).simple_ne_one i (α.injective (h.trans (map_one α).symm))
  choose β hβ hβα using fun i =>
    exists_rootReflection_of_natCard_fix_torusMulAut hp2 hτ hr (hw i) (hw1 i) (hfix i)
  exact ⟨β, hβ, hβα⟩

theorem rootFamily_ne_and_ne_neg {α : MulAut (WeylGroup τ)} {β : Fin τ.rank → Fin τ.rank → ℤ}
    (hβ : ∀ i, IsRoot τ (β i)) (hα : ∀ i, α (simple τ i) = rootReflection (β i))
    {i j : Fin τ.rank} (hij : i ≠ j) : β j ≠ β i ∧ β j ≠ -β i := by
  refine ⟨fun h => hij ?_, fun h => hij ?_⟩
  · refine (coxeterSystem τ).simple_injective (α.injective ?_)
    rw [hα, hα, h]
  · refine (coxeterSystem τ).simple_injective (α.injective ?_)
    rw [hα, hα, h, rootReflection_neg (hβ i)]

theorem iform_eq_zero_of_cartan_eq_zero (hτ : ∀ i, τ.symmetrizer i i = 1)
    {α : MulAut (WeylGroup τ)} {β : Fin τ.rank → Fin τ.rank → ℤ} (hβ : ∀ i, IsRoot τ (β i))
    (hα : ∀ i, α (simple τ i) = rootReflection (β i)) {i j : Fin τ.rank} (hij : i ≠ j)
    (h0 : τ.cartan i j = 0) : iform (β i) (β j) = 0 := by
  obtain ⟨hne, hne'⟩ := rootFamily_ne_and_ne_neg hβ hα hij
  have hcomm : Commute (simple τ i) (simple τ j) := (commute_simple_iff hτ hij).2 h0
  have h := hcomm.map α
  rw [hα, hα] at h
  exact iform_eq_zero_of_commute_rootReflection hτ (hβ i) (hβ j) hne hne' h

theorem iform_eq_pm_one_of_cartan_eq_neg_one (hτ : ∀ i, τ.symmetrizer i i = 1)
    {α : MulAut (WeylGroup τ)} {β : Fin τ.rank → Fin τ.rank → ℤ} (hβ : ∀ i, IsRoot τ (β i))
    (hα : ∀ i, α (simple τ i) = rootReflection (β i)) {i j : Fin τ.rank} (hij : i ≠ j)
    (h1 : τ.cartan i j = -1) : iform (β i) (β j) = 1 ∨ iform (β i) (β j) = -1 := by
  obtain ⟨hne, hne'⟩ := rootFamily_ne_and_ne_neg hβ hα hij.symm
  rcases iform_mem hτ (hβ i) (hβ j) hne hne' with h | h | h
  · exact Or.inr h
  · exfalso
    have hc : Commute (rootReflection (β i)) (rootReflection (β j)) :=
      rootReflection_commute_of_iform_eq_zero (hβ i) (hβ j) h
    rw [← hα, ← hα] at hc
    have hc' : Commute (simple τ i) (simple τ j) := by
      have := hc.map α.symm
      simpa using this
    have := (commute_simple_iff hτ hij).1 hc'
    omega
  · exact Or.inl h

theorem weylAut_inner_of_fixCount [Fact p.Prime] (hp2 : p ≠ 2)
    (hτ : ∀ i, τ.symmetrizer i i = 1) (hr : 0 < τ.rank)
    (hgauge : ∀ c : Fin τ.rank → Fin τ.rank → ℤ, (∀ i j, c i j = c j i) → (∀ i, c i i = 2) →
      (∀ i j, i ≠ j → τ.cartan i j = 0 → c i j = 0) →
      (∀ i j, τ.cartan i j = -1 → c i j = 1 ∨ c i j = -1) →
      ∃ ε : Fin τ.rank → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ∀ i j, ε i * ε j * c i j = τ.cartan i j)
    (hperm : ∀ π : Equiv.Perm (Fin τ.rank), (∀ i j, τ.cartan (π i) (π j) = τ.cartan i j) →
      ∃ g : WeylGroup τ, ∀ i, g * simple τ i * g⁻¹ = simple τ (π i))
    (α : MulAut (WeylGroup τ))
    (hfix : ∀ i, Nat.card {f : Multiplicative (Fin τ.rank → ZMod p) //
      ExcWeylOuter.torusMulAut τ p (α (simple τ i)) f = f} = p ^ (τ.rank - 1)) :
    ∃ w : WeylGroup τ, ∀ v, α v = w * v * w⁻¹ := by
  obtain ⟨β, hβ, hα⟩ := exists_rootFamily_of_fixCount hp2 hτ hr α hfix
  obtain ⟨ε, hε, hεc⟩ := hgauge (fun i j => iform (β i) (β j)) (fun i j => iform_comm _ _)
    (fun i => iform_self_eq_two hτ (hβ i))
    (fun i j hij h0 => iform_eq_zero_of_cartan_eq_zero hτ hβ hα hij h0)
    (fun i j h1 => iform_eq_pm_one_of_cartan_eq_neg_one hτ hβ hα
      (fun h => by subst h; rw [Tag.cartan_self] at h1; omega) h1)
  set γ : Fin τ.rank → Fin τ.rank → ℤ := fun i => ε i • β i with hγdef
  have hγ_pos : ∀ i, ε i = 1 → γ i = β i := fun i h => by simp [γ, h]
  have hγ_neg : ∀ i, ε i = -1 → γ i = -β i := fun i h => by simp [γ, h]
  have hγroot : ∀ i, IsRoot τ (γ i) := by
    intro i
    rcases hε i with h | h
    · rw [hγ_pos i h]
      exact hβ i
    · rw [hγ_neg i h]
      exact IsRoot.neg (hβ i)
  have hγgram : ∀ i j, iform (γ i) (γ j) = τ.cartan i j := by
    intro i j
    have h := hεc i j
    simp only [γ, iform_smul_left, iform_smul_right]
    rw [← h]
    ring
  have hγrefl : ∀ i, α (simple τ i) = rootReflection (γ i) := by
    intro i
    rcases hε i with h | h
    · rw [hγ_pos i h, hα i]
    · rw [hγ_neg i h, rootReflection_neg (hβ i), hα i]
  obtain ⟨u, hu⟩ := exists_weyl_smul_rootFamily_eq_single hτ hγgram hγroot α.toMonoidHom
    (fun i => hγrefl i)
  choose π hπ using hu
  have hsimple : ∀ i, simple τ (π i) = u * α (simple τ i) * u⁻¹ := by
    intro i
    have h1 : rootReflection (u • γ i) = u * rootReflection (γ i) * u⁻¹ :=
      rootReflection_smul_root u (hγroot i)
    rw [hπ i] at h1
    have h2 : rootReflection (Pi.single (π i) 1 : Fin τ.rank → ℤ) = simple τ (π i) := by
      rw [rootReflection_eq_conj (w := 1) (j := π i) (one_smul _ _), one_mul, inv_one, mul_one]
    rw [← h2, h1, hγrefl i]
  have hπinj : Function.Injective π := by
    intro i j hij
    have h := hsimple i
    rw [hij, hsimple j] at h
    have h' : α (simple τ j) = α (simple τ i) := mul_left_cancel (mul_right_cancel h)
    exact ((coxeterSystem τ).simple_injective (α.injective h')).symm
  have hgram : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j := by
    intro i j
    by_cases hij : π i = π j
    · obtain rfl := hπinj hij
      rw [Tag.cartan_self, Tag.cartan_self]
    · have h := iform_smul u (γ i) (γ j)
      rw [hπ i, hπ j, hγgram, iform_single_single_of_ne hτ hij] at h
      exact h
  obtain ⟨g, hg⟩ := hperm (Equiv.ofBijective π (Finite.injective_iff_bijective.mp hπinj)) hgram
  refine ⟨u⁻¹ * g, fun v => ?_⟩
  have hgen : α.toMonoidHom = (MulAut.conj (u⁻¹ * g)).toMonoidHom := by
    refine (coxeterSystem τ).ext_simple fun i => ?_
    have h1 : α (simple τ i) = u⁻¹ * simple τ (π i) * u := by
      rw [hsimple i]
      group
    have h2 : simple τ (π i) = g * simple τ i * g⁻¹ := (hg i).symm
    change α (simple τ i) = (u⁻¹ * g) * simple τ i * (u⁻¹ * g)⁻¹
    rw [h1, h2]
    group
  exact (DFunLike.congr_fun hgen v).trans (MulAut.conj_apply _ _)

theorem natCard_fix_torusMulAut_simple [Fact p.Prime] (hp2 : p ≠ 2)
    (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i) (i : Fin τ.rank) :
    Nat.card {f : Multiplicative (Fin τ.rank → ZMod p) //
      ExcWeylOuter.torusMulAut τ p (simple τ i) f = f} = p ^ (τ.rank - 1) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hr : 0 < τ.rank := Fin.pos i
  rw [ExcWeylOuter.torusMulAut_simple hsymm i]
  have h := card_fix_torusReflAut hp hp2 (CFSG.RankThree.CentralCover.cartanFunctional τ p i)
    (Pi.single i 1) (CFSG.RankThree.CentralCover.cartanFunctional_single i)
  rw [natCard_multiplicative_fin_zmod] at h
  have hpr : p ^ τ.rank = p ^ (τ.rank - 1) * p := by
    rw [← pow_succ]
    congr 1
    omega
  exact Nat.eq_of_mul_eq_mul_right hp.pos (h.trans hpr)

theorem normInducesInner_range_torusMulAut_of_diagram [Fact p.Prime] (hp2 : p ≠ 2)
    (hτ : ∀ i, τ.symmetrizer i i = 1) (hr : 0 < τ.rank)
    (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i)
    (hgauge : ∀ c : Fin τ.rank → Fin τ.rank → ℤ, (∀ i j, c i j = c j i) → (∀ i, c i i = 2) →
      (∀ i j, i ≠ j → τ.cartan i j = 0 → c i j = 0) →
      (∀ i j, τ.cartan i j = -1 → c i j = 1 ∨ c i j = -1) →
      ∃ ε : Fin τ.rank → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ∀ i j, ε i * ε j * c i j = τ.cartan i j)
    (hperm : ∀ π : Equiv.Perm (Fin τ.rank), (∀ i j, τ.cartan (π i) (π j) = τ.cartan i j) →
      ∃ g : WeylGroup τ, ∀ i, g * simple τ i * g⁻¹ = simple τ (π i)) :
    NormInducesInner (ExcWeylOuter.torusMulAut τ p).range := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro φ hφ
  have hρ : Function.Injective (ExcWeylOuter.torusMulAut τ p) :=
    ExcWeylOuter.torusMulAut_injective hp2
  obtain ⟨α, hα⟩ := exists_mulAut_conj_of_mem_normalizer_range hρ hφ
  have hfix : ∀ i, Nat.card {f : Multiplicative (Fin τ.rank → ZMod p) //
      ExcWeylOuter.torusMulAut τ p (α (simple τ i)) f = f} = p ^ (τ.rank - 1) := by
    intro i
    rw [hα (simple τ i), natCard_fix_conj_mulAut]
    exact natCard_fix_torusMulAut_simple hp2 hsymm i
  obtain ⟨w, hw⟩ := weylAut_inner_of_fixCount hp2 hτ hr hgauge hperm α hfix
  refine ⟨ExcWeylOuter.torusMulAut τ p w, MonoidHom.mem_range.mpr ⟨w, rfl⟩, ?_⟩
  intro v hv
  obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hv
  rw [← hα u, hw u]
  simp

theorem normInducesInner_range_torusMulAut_E6 [Fact p.Prime] (hp2 : p ≠ 2) :
    NormInducesInner (ExcWeylOuter.torusMulAut Tag.E6 p).range :=
  normInducesInner_range_torusMulAut_of_diagram hp2 (by decide) (by decide)
    NoOffExc.cartan_symm_E6 exists_sign_gauge_E6 exists_conj_simple_of_cartan_perm_E6

theorem normInducesInner_range_torusMulAut_E7 [Fact p.Prime] (hp2 : p ≠ 2) :
    NormInducesInner (ExcWeylOuter.torusMulAut Tag.E7 p).range :=
  normInducesInner_range_torusMulAut_of_diagram hp2 (by decide) (by decide)
    TableBExc.Three.cartan_symm_E7 exists_sign_gauge_E7 exists_conj_simple_of_cartan_perm_E7

theorem normInducesInner_range_torusMulAut_E8 [Fact p.Prime] (hp2 : p ≠ 2) :
    NormInducesInner (ExcWeylOuter.torusMulAut Tag.E8 p).range :=
  normInducesInner_range_torusMulAut_of_diagram hp2 (by decide) (by decide)
    TableBExc.Three.cartan_symm_E8 exists_sign_gauge_E8 exists_conj_simple_of_cartan_perm_E8

end CFSG.StandardType

end
