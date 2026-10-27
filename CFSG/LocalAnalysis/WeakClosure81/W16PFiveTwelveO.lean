module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.SignalizerFunctorTheorem.Quadratic.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Open Subgroup

theorem sum_eq_zero_of_free_orbits {X V : Type*} [DecidableEq X] [AddCommMonoid V]
    {A : Type*} [Group A] [Fintype A] [MulAction A X] (S : Finset X)
    (hS : ∀ a : A, ∀ x ∈ S, a • x ∈ S) (hfree : ∀ a : A, ∀ x ∈ S, a • x = x → a = 1)
    (f : X → V) (hf : ∀ x ∈ S, ∑ a : A, f (a • x) = 0) :
    ∑ x ∈ S, f x = 0 := by
  classical
  have main : ∀ T : Finset X, (∀ a : A, ∀ x ∈ T, a • x ∈ T) →
      (∀ a : A, ∀ x ∈ T, a • x = x → a = 1) →
      (∀ x ∈ T, ∑ a : A, f (a • x) = 0) → ∑ x ∈ T, f x = 0 := by
    intro T
    induction T using Finset.strongInductionOn with
    | _ T ih =>
      intro hT hfreeT hfT
      rcases T.eq_empty_or_nonempty with hT0 | ⟨x, hx⟩
      · rw [hT0, Finset.sum_empty]
      · set O : Finset X := Finset.univ.image (fun a : A => a • x) with hO
        have hxO : x ∈ O := by
          rw [hO, Finset.mem_image]
          exact ⟨1, Finset.mem_univ 1, one_smul A x⟩
        have hOT : O ⊆ T := by
          intro y hy
          rw [hO, Finset.mem_image] at hy
          obtain ⟨a, -, rfl⟩ := hy
          exact hT a x hx
        have hinj : Set.InjOn (fun a : A => a • x) (Finset.univ : Finset A) := by
          intro a _ b _ hab
          have hab' : a • x = b • x := hab
          have h1 : (b⁻¹ * a) • x = x := by
            rw [mul_smul, hab', inv_smul_smul]
          exact (inv_mul_eq_one.mp (hfreeT (b⁻¹ * a) x hx h1)).symm
        have hsumO : ∑ y ∈ O, f y = 0 := by
          rw [hO, Finset.sum_image hinj]
          exact hfT x hx
        have hT' : ∀ a : A, ∀ y ∈ T \ O, a • y ∈ T \ O := by
          intro a y hy
          rw [Finset.mem_sdiff] at hy ⊢
          refine ⟨hT a y hy.1, fun hc => hy.2 ?_⟩
          rw [hO, Finset.mem_image] at hc
          obtain ⟨b, -, hb⟩ := hc
          rw [hO, Finset.mem_image]
          exact ⟨a⁻¹ * b, Finset.mem_univ _, by rw [mul_smul, hb, inv_smul_smul]⟩
        have hfree' : ∀ a : A, ∀ y ∈ T \ O, a • y = y → a = 1 :=
          fun a y hy => hfreeT a y (Finset.mem_sdiff.mp hy).1
        have hf' : ∀ y ∈ T \ O, ∑ a : A, f (a • y) = 0 :=
          fun y hy => hfT y (Finset.mem_sdiff.mp hy).1
        have hrest : ∑ y ∈ T \ O, f y = 0 :=
          ih (T \ O) (Finset.sdiff_ssubset hOT ⟨x, hxO⟩) hT' hfree' hf'
        have hsd := Finset.sum_sdiff (f := f) hOT
        rw [hrest, hsumO, zero_add] at hsd
        exact hsd.symm
  exact main S hS hfree hf

theorem permMod_fixed_of_index_two {G : Type} [Group G] [Finite G] {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (ρ : G →* LGL 2 V) {B A D : Subgroup G} (hAB : A ≤ B)
    (hA : IsElemAbelian 2 A) (hDA : D ≤ A) (hD2 : D.relIndex A = 2)
    (hD : ∀ w : V, (∀ d ∈ D, ρ d w = w) → ∀ a ∈ A, ρ a w = w)
    (hfree : ∀ g : G, g ∉ B → ∀ a ∈ A, g⁻¹ * a * g ∈ B → a = 1) {z : V}
    (hz : ∀ b ∈ B, ρ b z = z) : ∀ g : G, ρ g z = z := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype (G ⧸ B) := Fintype.ofFinite (G ⧸ B)
  haveI : Fintype ↥A := Fintype.ofFinite ↥A
  haveI : Fintype ↥D := Fintype.ofFinite ↥D
  let f : G ⧸ B → V := fun ω =>
    Quotient.liftOn' ω (fun g : G => ρ g z) (fun g₁ g₂ h => by
      have hmem : g₁⁻¹ * g₂ ∈ B := QuotientGroup.leftRel_apply.mp h
      have h2 : ρ g₂ z = ρ g₁ z := by
        conv_lhs => rw [show g₂ = g₁ * (g₁⁻¹ * g₂) from by group]
        rw [map_mul]
        change ρ g₁ (ρ (g₁⁻¹ * g₂) z) = ρ g₁ z
        rw [hz (g₁⁻¹ * g₂) hmem]
      exact h2.symm)
  have hf_mk : ∀ g : G, f ((g : G) : G ⧸ B) = ρ g z := fun g => rfl
  have hf_smul : ∀ (h : G) (ω : G ⧸ B), f (h • ω) = ρ h (f ω) := by
    intro h ω
    refine QuotientGroup.induction_on ω ?_
    intro g
    rw [show h • (g : G ⧸ B) = ((h * g : G) : G ⧸ B) from rfl, hf_mk, hf_mk]
    change ρ (h * g) z = ρ h (ρ g z)
    rw [map_mul]
    rfl
  have h2 : ∀ v : V, v + v = 0 := fun v => by
    rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from by decide, zero_smul]
  let ω₀ : G ⧸ B := ((1 : G) : G ⧸ B)
  let S : Finset (G ⧸ B) := Finset.univ.erase ω₀
  have hsmul_B : ∀ c ∈ B, c • ω₀ = ω₀ := by
    intro c hc
    change c • ((1 : G) : G ⧸ B) = ((1 : G) : G ⧸ B)
    rw [show c • ((1 : G) : G ⧸ B) = ((c * 1 : G) : G ⧸ B) from rfl, mul_one]
    exact QuotientGroup.eq.mpr (by simpa using B.inv_mem hc)
  have hS : ∀ a : ↥A, ∀ x ∈ S, a • x ∈ S := by
    intro a x hx
    rw [Finset.mem_erase] at hx ⊢
    refine ⟨?_, Finset.mem_univ _⟩
    intro hcon
    apply hx.1
    have h := congrArg (fun y : G ⧸ B => (a : ↥A)⁻¹ • y) hcon
    rw [inv_smul_smul] at h
    rw [show (a : ↥A)⁻¹ • ω₀ = ω₀ from
      hsmul_B ((a : ↥A)⁻¹ : G) (hAB (A.inv_mem a.2))] at h
    exact h
  have hfreeA : ∀ a : ↥A, ∀ x ∈ S, a • x = x → a = 1 := by
    intro a x hx hfix
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have hgB : g ∉ B := by
      intro hg
      exact (Finset.mem_erase.mp hx).1 (by
        show (g : G ⧸ B) = ((1 : G) : G ⧸ B)
        rw [QuotientGroup.eq]
        simpa using B.inv_mem hg)
    have h1 : (g : G ⧸ B) = (((a : G) * g : G) : G ⧸ B) := by
      have h2' : (a : ↥A) • (g : G ⧸ B) = (((a : G) * g : G) : G ⧸ B) := rfl
      rw [h2'] at hfix
      exact hfix.symm
    have hmem : g⁻¹ * (a : G) * g ∈ B := by
      have := QuotientGroup.eq.mp h1
      simpa [mul_assoc] using this
    exact Subtype.ext (by simpa using hfree g hgB (a : G) a.2 hmem)
  have hsumA : ∀ ω : G ⧸ B, (∑ x : ↥A, f (x • ω)) = 0 := by
    intro ω
    let sig : V := ∑ d : ↥D, f ((d : G) • ω)
    have hfixD : ∀ d' : ↥D, ρ (d' : G) sig = sig := by
      intro d'
      have h1 : ρ (d' : G) sig = ∑ d : ↥D, f (((d' : G) * (d : G)) • ω) := by
        dsimp only [sig]
        rw [map_sum]
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [← hf_smul, mul_smul]
      rw [h1]
      have hp : ∀ d : ↥D, f (((d' : G) * (d : G)) • ω)
          = f (((d' * d : ↥D) : G) • ω) := by
        intro d
        simp only [Subgroup.coe_mul]
      have hre : (∑ d : ↥D, f (((d' * d : ↥D) : G) • ω)) = sig := by
        have := Equiv.sum_comp (Equiv.mulLeft d')
          (fun e : ↥D => f ((e : G) • ω))
        simpa only [Equiv.coe_mulLeft] using this
      rw [Finset.sum_congr rfl (fun d _ => hp d)]
      exact hre
    have hfixA : ∀ a ∈ A, ρ a sig = sig := hD sig (fun d hd => hfixD ⟨d, hd⟩)
    obtain ⟨a, haA, haD, hpart⟩ :=
      (Subgroup.relIndex_eq_two_iff_exists_notMem_and' (H := D) (K := A)).mp hD2
    let c : G := a⁻¹
    have hcA : c ∈ A := by simpa [c] using A.inv_mem haA
    have hcD : c ∉ D := by
      intro h
      exact haD (by simpa [c] using D.inv_mem h)
    set Dset : Finset ↥A :=
      Finset.univ.image (fun d : ↥D => (⟨(d : G), hDA d.2⟩ : ↥A)) with hDset
    set Cset : Finset ↥A := Finset.univ.image
      (fun d : ↥D => (⟨c * (d : G), A.mul_mem hcA (hDA d.2)⟩ : ↥A)) with hCset
    have hdisj : Disjoint Dset Cset := by
      rw [Finset.disjoint_left]
      intro y hy hyC
      rw [hDset, Finset.mem_image] at hy
      obtain ⟨d1, -, rfl⟩ := hy
      rw [hCset, Finset.mem_image] at hyC
      obtain ⟨d2, -, hEq⟩ := hyC
      have hval : c * (d2 : G) = (d1 : G) := congrArg Subtype.val hEq
      have hc : c ∈ D := by
        have hc_eq : c = (d1 : G) * (d2 : G)⁻¹ := by
          rw [← hval, mul_assoc, mul_inv_cancel, mul_one]
        rw [hc_eq]
        exact D.mul_mem d1.2 (D.inv_mem d2.2)
      exact hcD hc
    have hcover : (Finset.univ : Finset ↥A) = Dset ∪ Cset := by
      apply Finset.Subset.antisymm
      · intro x _
        rw [Finset.mem_union]
        rcases hpart (x : G) x.2 with haxD | hxD
        · right
          rw [hCset, Finset.mem_image]
          refine ⟨⟨a * (x : G), haxD⟩, Finset.mem_univ _, Subtype.ext ?_⟩
          show c * (a * (x : G)) = (x : G)
          rw [show c = a⁻¹ from rfl, inv_mul_cancel_left]
        · left
          rw [hDset, Finset.mem_image]
          exact ⟨⟨(x : G), hxD⟩, Finset.mem_univ _, Subtype.ext rfl⟩
      · intro x _
        exact Finset.mem_univ x
    have hsumD : ∑ y ∈ Dset, f (y • ω) = sig := by
      rw [hDset]
      rw [Finset.sum_image (s := (Finset.univ : Finset ↥D))
        (g := fun d : ↥D => (⟨(d : G), hDA d.2⟩ : ↥A))
        (fun d1 _ d2 _ hEq =>
          Subtype.ext (congrArg (fun x : ↥A => (x : G)) hEq))]
      exact Finset.sum_congr rfl (fun d _ => rfl)
    have hsumC : ∑ y ∈ Cset, f (y • ω) = ρ c sig := by
      rw [hCset]
      rw [Finset.sum_image (s := (Finset.univ : Finset ↥D))
        (g := fun d : ↥D => (⟨c * (d : G), A.mul_mem hcA (hDA d.2)⟩ : ↥A))
        (fun d1 _ d2 _ hEq =>
          Subtype.ext
            (mul_left_cancel (congrArg (fun x : ↥A => (x : G)) hEq)))]
      dsimp only [sig]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      show f ((c * (d : G)) • ω) = ρ c (f ((d : G) • ω))
      rw [mul_smul, hf_smul]
    have hsplit : ∑ x : ↥A, f (x • ω) = sig + ρ c sig := by
      rw [hcover, Finset.sum_union hdisj, hsumD, hsumC]
    rw [hsplit, hfixA c hcA]
    exact h2 sig
  have hzero : ∑ x ∈ S, f x = 0 :=
    sum_eq_zero_of_free_orbits (A := ↥A) S hS hfreeA f (fun x _ => hsumA x)
  have hsum : ∑ ω : G ⧸ B, f ω = z := by
    have h2' : f ω₀ + ∑ ω ∈ S, f ω = ∑ ω : G ⧸ B, f ω := by
      dsimp only [S]
      exact Finset.add_sum_erase Finset.univ f (Finset.mem_univ ω₀)
    rw [hzero, add_zero] at h2'
    rw [← h2']
    rw [show ω₀ = ((1 : G) : G ⧸ B) from rfl, hf_mk, map_one]
    rfl
  have hfixed : ∀ h : G, ρ h (∑ ω : G ⧸ B, f ω) = ∑ ω : G ⧸ B, f ω := by
    intro h
    calc ρ h (∑ ω : G ⧸ B, f ω) = ∑ ω : G ⧸ B, ρ h (f ω) :=
          map_sum (ρ h) f Finset.univ
      _ = ∑ ω : G ⧸ B, f (h • ω) := by
          refine Finset.sum_congr rfl (fun ω _ => ?_)
          exact (hf_smul h ω).symm
      _ = ∑ ω : G ⧸ B, f ω := by
          simpa only [MulAction.toPerm_apply] using Equiv.sum_comp (MulAction.toPerm h) f
  intro g
  calc ρ g z = ρ g (∑ ω : G ⧸ B, f ω) := by rw [hsum]
    _ = ∑ ω : G ⧸ B, f ω := hfixed g
    _ = z := hsum

end CFSG.LocalAnalysis.WeakClosure81

end
