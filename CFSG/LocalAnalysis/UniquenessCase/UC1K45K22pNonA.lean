module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45K22pDefs
public import CFSG.GroupTheory.LocalCores.MinimalNormal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup

def invariantAuts {G : Type*} [Group G] [Finite G] (N : Subgroup G) : Subgroup (MulAut G) where
  carrier := {τ | ∀ x ∈ N, τ x ∈ N}
  one_mem' := by intro x hx; simpa using hx
  mul_mem' := by
    intro τ₁ τ₂ h₁ h₂ x hx
    exact h₁ _ (h₂ x hx)
  inv_mem' := by
    intro τ hτ x hx
    have hle : N.map τ.toMonoidHom ≤ N := by
      rintro _ ⟨y, hy, rfl⟩
      exact hτ y hy
    have hcard : Nat.card N = Nat.card (N.map τ.toMonoidHom) :=
      Nat.card_congr (Subgroup.equivMapOfInjective N τ.toMonoidHom τ.injective)
    have heq : N.map τ.toMonoidHom = N :=
      Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)
    have hx' : x ∈ N.map τ.toMonoidHom := heq.symm ▸ hx
    obtain ⟨y, hy, hyx⟩ := hx'
    show τ⁻¹ x ∈ N
    rw [← hyx]
    simpa using hy

theorem zpow_mem_of_mem_of_invariant {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    {σ : MulAut G} (hσ : ∀ x ∈ N, σ x ∈ N) {τ : MulAut G} (hτ : τ ∈ Subgroup.zpowers σ)
    {x : G} (hx : x ∈ N) : τ x ∈ N := by
  have hsub : Subgroup.zpowers σ ≤ invariantAuts N := by
    rw [Subgroup.zpowers_le]
    exact hσ
  exact hsub hτ x hx

theorem normal_map_inl_semidirectProduct {M G : Type*} [Group M] [Group G] (φ : G →* MulAut M)
    {N : Subgroup M} (hN : N.Normal) (hφ : ∀ g : G, ∀ x ∈ N, φ g x ∈ N) :
    (N.map (SemidirectProduct.inl : M →* M ⋊[φ] G)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨n₀, hn₀, rfl⟩ := Subgroup.mem_map.mp hn
  have hmem : g.left * φ g.right n₀ * g.left⁻¹ ∈ N :=
    hN.conj_mem _ (hφ g.right n₀ hn₀) g.left
  have heq : g * (SemidirectProduct.inl n₀) * g⁻¹ =
      SemidirectProduct.inl (g.left * φ g.right n₀ * g.left⁻¹) := by
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right g]
    rw [map_mul, map_mul, map_inv, SemidirectProduct.inl_aut, map_inv]
    group
  rw [heq]
  exact Subgroup.mem_map_of_mem _ hmem

theorem exists_factors_of_minInv {M : Type} [Group M] [Finite M] (σ : MulAut M) (hσ : σ ^ 3 = 1)
    {N : Subgroup M} (hN : K22p.IsMinInv σ N) (hna : ¬ IsMulCommutative ↥N) :
    ∃ (r : ℕ) (S : Fin r → Subgroup M), 1 ≤ r ∧ (∀ i, S i ≤ N) ∧
      (∀ i, ((S i).subgroupOf N).Normal) ∧ (∀ i, IsSimpleGroup ↥(S i)) ∧
      (∀ i, ¬ IsMulCommutative ↥(S i)) ∧
      (∀ i j, i ≠ j → ∀ x ∈ S i, ∀ y ∈ S j, x * y = y * x) ∧ (⨆ i, S i) = N := by
  classical
  let G : Type := ↥(Subgroup.zpowers σ)
  let ψ : G →* MulAut M := (Subgroup.zpowers σ).subtype
  let Γ : Type := M ⋊[ψ] G
  let ι : M →* Γ := SemidirectProduct.inl
  have hιinj : Function.Injective ι := SemidirectProduct.inl_injective
  haveI hGfin : Finite G := IsOfFinOrder.finite_zpowers ⟨3, by norm_num, hσ⟩
  haveI hΓfin : Finite Γ := Finite.of_equiv (M × G) SemidirectProduct.equivProd.symm
  have hInv : ∀ g : G, ∀ x ∈ N, ψ g x ∈ N := fun g x hx =>
    zpow_mem_of_mem_of_invariant hN.invariant g.2 hx
  let N' : Subgroup Γ := N.map ι
  have hN'normal : N'.Normal := normal_map_inl_semidirectProduct (φ := ψ) hN.normal hInv
  have hN'ne : N' ≠ ⊥ := fun h =>
    hN.ne_bot ((Subgroup.map_eq_bot_iff_of_injective N hιinj).mp h)
  have hN'min : ∀ L : Subgroup Γ, L.Normal → L ≤ N' → L = ⊥ ∨ L = N' := by
    intro L hL hLN'
    let L' : Subgroup M := L.comap ι
    have hL'le : L' ≤ N := by
      rw [← Subgroup.comap_map_eq_self_of_injective hιinj N]
      exact Subgroup.comap_mono hLN'
    have hL'normal : L'.Normal := hL.comap ι
    have hL'inv : ∀ x ∈ L', σ x ∈ L' := by
      intro x hx
      have hxL : ι x ∈ L := hx
      have hconj : SemidirectProduct.inr ⟨σ, Subgroup.mem_zpowers σ⟩ * ι x *
          (SemidirectProduct.inr ⟨σ, Subgroup.mem_zpowers σ⟩)⁻¹ ∈ L :=
        hL.conj_mem (ι x) hxL (SemidirectProduct.inr ⟨σ, Subgroup.mem_zpowers σ⟩)
      have heq : ι (σ x) = SemidirectProduct.inr ⟨σ, Subgroup.mem_zpowers σ⟩ * ι x *
          (SemidirectProduct.inr ⟨σ, Subgroup.mem_zpowers σ⟩)⁻¹ := by
        have h := SemidirectProduct.inl_aut (φ := ψ) (g := ⟨σ, Subgroup.mem_zpowers σ⟩) x
        rw [show ψ ⟨σ, Subgroup.mem_zpowers σ⟩ = σ from rfl] at h
        simpa [ι, map_inv] using h
      show ι (σ x) ∈ L
      rw [heq]
      exact hconj
    have hLmap : L = L'.map ι :=
      (Subgroup.map_comap_eq_self (f := ι) (H := L)
        (hLN'.trans (Subgroup.map_le_range (f := ι) N))).symm
    rcases hN.minimal L' hL'normal hL'inv hL'le with h | h
    · left
      rw [hLmap, h, Subgroup.map_bot]
    · right
      rw [hLmap, h]
  obtain ⟨r, S', hr, hS'le, hS'simple, hS'conj, hS'norm, e, he⟩ :=
    CFSG.LocalCores.minimal_normal_simple_factors hN'normal hN'ne hN'min
  haveI hS'simpleI : ∀ i, IsSimpleGroup ↥(S' i) := hS'simple
  let S : Fin r → Subgroup M := fun i => (S' i).comap ι
  have hSmap : ∀ i, (S i).map ι = S' i := fun i =>
    Subgroup.map_comap_eq_self (f := ι) (H := S' i)
      ((hS'le i).trans (Subgroup.map_le_range (f := ι) N))
  have hSleN : ∀ i, S i ≤ N := by
    intro i
    rw [show S i = (S' i).comap ι from rfl,
      ← Subgroup.comap_map_eq_self_of_injective hιinj N]
    exact Subgroup.comap_mono (hS'le i)
  refine ⟨r, S, hr, hSleN, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨fun n hn g => ?_⟩
    have hn' : ι (n : M) ∈ S' i := hn
    have hnN' : ι (n : M) ∈ N' := Subgroup.mem_map_of_mem ι n.2
    have hgN' : ι (g : M) ∈ N' := Subgroup.mem_map_of_mem ι g.2
    have hconj := (hS'norm i).conj_mem (⟨ι (n : M), hnN'⟩ : N') hn' (⟨ι (g : M), hgN'⟩ : N')
    show ι ((g : M) * (n : M) * (g : M)⁻¹) ∈ S' i
    rw [map_mul, map_mul, map_inv]
    exact hconj
  · intro i
    have hiso : ↥(S i) ≃* ↥(S' i) :=
      (Subgroup.equivMapOfInjective (S i) ι hιinj).trans (MulEquiv.subgroupCongr (hSmap i))
    exact MulEquiv.isSimpleGroup hiso
  · intro i hi
    haveI : IsMulCommutative ↥(S i) := hi
    haveI hS'i : IsMulCommutative ↥(S' i) := hSmap i ▸ inferInstance
    have hcomm_all : ∀ j, IsMulCommutative ↥(S' j) := fun j => by
      obtain ⟨g, hg⟩ := hS'conj i j
      rw [hg]
      exact Subgroup.map_isMulCommutative (H := S' i) (MulAut.conj g⁻¹).toMonoidHom
    haveI : ∀ j, IsMulCommutative ↥(S' j) := hcomm_all
    haveI hN'comm : IsMulCommutative ↥N' := IsMulCommutative.of_comm (fun a b => by
      obtain ⟨x, rfl⟩ := e.surjective a
      obtain ⟨y, rfl⟩ := e.surjective b
      rw [← map_mul, ← map_mul, mul_comm'])
    let eN : ↥N ≃* ↥N' := Subgroup.equivMapOfInjective N ι hιinj
    haveI : IsMulCommutative ↥N := IsMulCommutative.of_comm (fun a b => by
      apply eN.injective
      rw [map_mul, map_mul, mul_comm'])
    exact hna inferInstance
  · intro i j hij x hx y hy
    have hx' : ι x ∈ S' i := hx
    have hy' : ι y ∈ S' j := hy
    let a : (k : Fin r) → S' k := Pi.mulSingle i ⟨ι x, hx'⟩
    let b : (k : Fin r) → S' k := Pi.mulSingle j ⟨ι y, hy'⟩
    have ha : (e a : Γ) = ι x := by
      simpa [a] using he i a (by intro k hk; exact Pi.mulSingle_eq_of_ne hk _)
    have hb : (e b : Γ) = ι y := by
      simpa [b] using he j b (by intro k hk; exact Pi.mulSingle_eq_of_ne hk _)
    have hcomm : (e a : Γ) * (e b : Γ) = (e b : Γ) * (e a : Γ) := by
      have h := congrArg e (Pi.mulSingle_commute hij (⟨ι x, hx'⟩ : S' i) (⟨ι y, hy'⟩ : S' j))
      have h' := congrArg (fun w : ↥N' => (w : Γ)) h
      simpa [map_mul] using h'
    have hxy : ι x * ι y = ι y * ι x := by
      rw [← ha, ← hb]
      exact hcomm
    apply hιinj
    rw [map_mul, map_mul]
    exact hxy
  · apply le_antisymm
    · exact iSup_le hSleN
    · have hN'eq : N' = ⨆ i, S' i := by
        refine le_antisymm ?_ (iSup_le hS'le)
        intro x hx
        obtain ⟨z, hz⟩ := e.surjective ⟨x, hx⟩
        have hx' : (e z : Γ) = x := congrArg Subtype.val hz
        rw [← hx']
        have hcommz : (↑(Finset.univ : Finset (Fin r)) : Set (Fin r)).Pairwise
            (fun i j => Commute (Pi.mulSingle (M := fun k => ↥(S' k)) i (z i))
              (Pi.mulSingle (M := fun k => ↥(S' k)) j (z j))) := by
          intro i _ j _ hij
          exact Pi.mulSingle_commute (f := fun k => ↥(S' k)) hij (z i) (z j)
        have hzprod : Finset.univ.noncommProd
            (fun i => Pi.mulSingle (M := fun k => ↥(S' k)) i (z i)) hcommz = z :=
          Finset.noncommProd_mulSingle z
        rw [← hzprod]
        change ((N'.subtype.comp e.toMonoidHom)
            (Finset.univ.noncommProd
              (fun i => Pi.mulSingle (M := fun k => ↥(S' k)) i (z i)) hcommz)) ∈ ⨆ i, S' i
        have hmapΓ := Finset.map_noncommProd Finset.univ
            (fun i => Pi.mulSingle (M := fun k => ↥(S' k)) i (z i)) hcommz
            (N'.subtype.comp e.toMonoidHom)
        rw [hmapΓ]
        refine Subgroup.noncommProd_mem (⨆ i, S' i) _ (fun i _ => ?_)
        have hzi : (e (Pi.mulSingle (M := fun k => ↥(S' k)) i (z i)) : Γ) = (z i : Γ) := by
          simpa using he i (Pi.mulSingle (M := fun k => ↥(S' k)) i (z i))
            (by intro j hj; exact Pi.mulSingle_eq_of_ne hj _)
        change (e (Pi.mulSingle (M := fun k => ↥(S' k)) i (z i)) : Γ) ∈ ⨆ i, S' i
        rw [hzi]
        exact Subgroup.mem_iSup_of_mem i (z i).2
      have hmap_iSup : (⨆ i, S i).map ι = ⨆ i, S' i := by
        rw [Subgroup.map_iSup]
        exact iSup_congr fun i => hSmap i
      have hcomap : ((⨆ i, S i).map ι).comap ι = ⨆ i, S i :=
        Subgroup.comap_map_eq_self_of_injective hιinj (⨆ i, S i)
      have hNcomap : N'.comap ι = N :=
        Subgroup.comap_map_eq_self_of_injective hιinj N
      rw [← hNcomap, hN'eq, ← hmap_iSup, hcomap]

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46
