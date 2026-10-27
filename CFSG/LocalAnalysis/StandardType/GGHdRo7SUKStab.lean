module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUDefs

import CFSG.LocalAnalysis.StandardType.GGHdRo7KNC
import CFSG.LocalAnalysis.StandardType.GGSCNoTVCyclic
import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel
import CFSG.GroupTheory.GL52.SylowTools

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem hdRo7SUKStabAux_coord_equiv {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V)
    (σ : Equiv.Perm (Fin m)) (w : V) (j : Fin m) :
    b.coord j ((b.equiv b σ) w) = b.coord (σ.symm j) w := by
  have h : (b.coord j).comp ((b.equiv b σ).toLinearMap) = b.coord (σ.symm j) := by
    refine b.ext (fun i => ?_)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equiv_apply,
      Module.Basis.coord_apply, Module.Basis.repr_self_apply]
    by_cases hij : σ i = j
    · have hji : i = σ.symm j := by rw [← hij, Equiv.symm_apply_apply]
      simp [hij, hji]
    · have hji : i ≠ σ.symm j := by
        intro h'
        exact hij (by rw [h', Equiv.apply_symm_apply])
      simp [hij, hji]
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe] using
    congrArg (fun φ : V →ₗ[ZMod p] (ZMod p) => φ w) h

private theorem hdRo7SUKStabAux_coord_ones {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V) (k : Fin m) :
    b.coord k (SUOnes p b) = 1 := by
  unfold SUOnes
  rw [map_sum]
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self_apply]
  simp

private theorem hdRo7SUKStabAux_fixed_span {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V) (hm : 2 ≤ m) {w : V}
    (hw : ∀ a : V ≃ₗ[ZMod p] V, SUPerm p b a → a w = w) :
    w ∈ Submodule.span (ZMod p) ({SUOnes p b} : Set V) := by
  have hcoord : ∀ i j : Fin m, b.coord i w = b.coord j w := by
    intro i j
    by_cases hij : i = j
    · subst hij; rfl
    · have hsup : SUPerm p b (b.equiv b (Equiv.swap i j)) :=
        ⟨Equiv.swap i j, fun k => by rw [Module.Basis.equiv_apply]⟩
      have hfix := hw _ hsup
      have hsj : Equiv.symm (Equiv.swap i j) i = j := by
        rw [Equiv.symm_apply_eq, Equiv.swap_apply_right]
      have h1 := congrArg (b.coord i) hfix
      rw [hdRo7SUKStabAux_coord_equiv b (Equiv.swap i j) w i, hsj] at h1
      exact h1.symm
  rw [Submodule.mem_span_singleton]
  refine ⟨b.coord ⟨0, by omega⟩ w, ?_⟩
  apply b.repr.injective
  ext i
  have hones : b.repr (SUOnes p b) i = 1 := by
    rw [← Module.Basis.coord_apply]; exact hdRo7SUKStabAux_coord_ones b i
  have hwi : b.repr w i = b.coord i w := by rw [← Module.Basis.coord_apply]
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, hones, mul_one, hwi]
  exact (hcoord i ⟨0, by omega⟩).symm

private theorem hdRo7SUKStabAux_card_le_of_mem_span {α : Type*} {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {x : V} (f : α → V) (hinj : Function.Injective f)
    (hspan : ∀ a, f a ∈ Submodule.span (ZMod p) ({x} : Set V)) : Nat.card α ≤ p := by
  let g : α → ZMod p := fun a => Classical.choose (Submodule.mem_span_singleton.mp (hspan a))
  have hg : Function.Injective g := by
    intro a b hab
    apply hinj
    have ha := Classical.choose_spec (Submodule.mem_span_singleton.mp (hspan a))
    have hb := Classical.choose_spec (Submodule.mem_span_singleton.mp (hspan b))
    calc f a = g a • x := ha.symm
      _ = g b • x := by rw [hab]
      _ = f b := hb
  have h := Nat.card_le_card_of_injective g hg
  rwa [Nat.card_zmod] at h

private theorem hdRo7SUKStabAux_aut_normalizer {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {y : G} {K : Subgroup G}
    (hS : CFSG.Assembly.LargeEvenSStar p B y K)
    (hnc : ∃ S : Subgroup G, S ≤ K ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hy : y ∈ Bs) (φ : MulAut ↥Bs) (hφ : φ ∈ ggAutomizer ⊤ Bs)
    (hfix : φ ⟨y, hy⟩ ∈ Subgroup.zpowers (⟨y, hy⟩ : ↥Bs)) :
    φ ∈ Subgroup.normalizer (ggAutomizer K Bs : Set (MulAut ↥Bs)) := by
  obtain ⟨g, -, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hφ
  have hgy : g * y * g⁻¹ ∈ Subgroup.zpowers y := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hfix
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h1 := congrArg Subtype.val hk
    rw [hφg] at h1
    simpa using h1
  have hgK : g ∈ Subgroup.normalizer (K : Set G) :=
    mem_normalizer_of_sstar' hS hnc
      (CFSG.GroupTheory.GL52.mem_normalizer_zpowers_of_conj_mem hgy)
  have hφi := inv_apply_of_forall hφg
  rw [Subgroup.mem_normalizer_iff]
  intro ψ
  constructor
  · intro hψ
    obtain ⟨l, hl, hlN, hψl⟩ := mem_ggAutomizer_iff.mp hψ
    refine mem_ggAutomizer_iff.mpr ⟨g * l * g⁻¹,
      (Subgroup.mem_normalizer_iff.mp hgK l).mp hl,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hlN) (Subgroup.inv_mem _ hgN),
      fun b => ?_⟩
    rw [MulAut.mul_apply, MulAut.mul_apply, hφg, hψl, hφi]
    group
  · intro hψ
    obtain ⟨l, hl, hlN, hψl⟩ := mem_ggAutomizer_iff.mp hψ
    have hgK' := Subgroup.inv_mem _ hgK
    have hgN' := Subgroup.inv_mem _ hgN
    refine mem_ggAutomizer_iff.mpr ⟨g⁻¹ * l * g, ?_, ?_, fun b => ?_⟩
    · simpa using (Subgroup.mem_normalizer_iff.mp hgK' l).mp hl
    · simpa using Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN' hlN) hgN
    · have hψeq : ψ = φ⁻¹ * (φ * ψ * φ⁻¹) * φ := by group
      rw [hψeq, MulAut.mul_apply, MulAut.mul_apply, hφi, hψl, hφg]
      group

private theorem hdRo7SUKStabAux_of_noncyclic {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hnc : ∃ S : Subgroup G, S ≤ K ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    {m : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (b : Module.Basis (Fin m) (ZMod p) V) (hy : y ∈ Bs) (hp3 : p = 3) (hm : 7 ≤ m)
    (h3 : ¬ 3 ∣ m) (hiy : ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) = SUOnes p b)
    (hAK : ∀ g, g ∈ (ggAutomizer K Bs).map (ggLin (p := p) ι) ↔ SUPerm p b g) :
    ∀ a ∈ (ggAutomizer ⊤ Bs).map (ggLin (p := p) ι), a (SUOnes p b) = SUOnes p b →
      ∀ s, SUPerm p b s → SUPerm p b (a * s * a⁻¹) := by
  intro a ha hafix s hs
  obtain ⟨ψ, hψ, hψa⟩ := Subgroup.mem_map.mp ha
  have hψy : ψ ⟨y, hy⟩ = ⟨y, hy⟩ := by
    apply ι.injective
    apply Additive.ofMul.injective
    have h1 : ι (Additive.ofMul (ψ ⟨y, hy⟩)) = ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) := by
      calc ι (Additive.ofMul (ψ ⟨y, hy⟩))
          = ggLin (p := p) ι ψ (ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) := by
              rw [ggLin_apply_ofMul]
        _ = a (SUOnes p b) := by rw [hψa, hiy]
        _ = SUOnes p b := hafix
        _ = ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) := by rw [hiy]
    exact h1
  have hfix : ψ ⟨y, hy⟩ ∈ Subgroup.zpowers (⟨y, hy⟩ : ↥Bs) := by
    rw [hψy]
    exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
  have hSHat : CFSG.Assembly.LargeEvenSHat p B y K := hH.2.2.2.2.1.1
  have hneighbor : CFSG.Assembly.LargeEvenIsNeighborOf p B x L y K :=
    isNeighborOf_of_ggNbr hH.1.2.2 hH.2.2.2.2.1
  have hcomp : CFSG.Assembly.IsComponentOf K (Subgroup.centralizer ({y} : Set G)) :=
    (isComponentOf_of_isNeighborOf hH.1.1.2.2.2.2.2.2.2 hneighbor).1
  have hBsK : Bs ≤ Subgroup.normalizer (K : Set G) :=
    CFSG.StandardType.GGInnerDiagOn.le_normalizer (hH.2.2.1.2 y K hH.2.2.2.2.1)
  have hEC : Bs ≤ Subgroup.normalizer
      ((Subgroup.centralizer (K : Set G) : Subgroup G) : Set G) :=
    hBsK.trans (normalizer_le_normalizer_centralizer K)
  have hcard : Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤ p := by
    let f : ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) → V :=
      fun u => ι (Additive.ofMul (⟨(u : G), (Subgroup.mem_inf.mp u.2).1⟩ : ↥Bs))
    have hinj : Function.Injective f := by
      intro u v huv
      have h : (⟨(u : G), (Subgroup.mem_inf.mp u.2).1⟩ : ↥Bs) =
          ⟨(v : G), (Subgroup.mem_inf.mp v.2).1⟩ :=
        Additive.ofMul.injective (ι.injective huv)
      exact Subtype.ext (congrArg (fun z : ↥Bs => (z : G)) h)
    have hspan : ∀ u, f u ∈ Submodule.span (ZMod p) ({SUOnes p b} : Set V) := by
      intro u
      apply hdRo7SUKStabAux_fixed_span b (by omega)
      intro s hs
      obtain ⟨ν, hν, hνs⟩ := Subgroup.mem_map.mp ((hAK s).mpr hs)
      obtain ⟨k, hkK, hkN, hνk⟩ := mem_ggAutomizer_iff.mp hν
      have hku : k * (u : G) = (u : G) * k :=
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp u.2).2) k hkK
      have hνu : ν (⟨(u : G), (Subgroup.mem_inf.mp u.2).1⟩ : ↥Bs) =
          ⟨(u : G), (Subgroup.mem_inf.mp u.2).1⟩ := by
        apply Subtype.ext
        rw [hνk, hku]
        group
      rw [← hνs]
      dsimp only [f]
      rw [ggLin_apply_ofMul, hνu]
    exact hdRo7SUKStabAux_card_le_of_mem_span f hinj hspan
  have hp2 : p ≠ 2 := by omega
  have hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (K : Set G) → IsPGroup p S → IsCyclic S :=
    fun S hSK hSp =>
      ggSCNoTV_isCyclic (p := p) hp2 (E := Bs) (C := Subgroup.centralizer (K : Set G))
        hH.1.2.1.2.1 hH.1.2.1.2.2.2 hH.2.2.2.1 hEC hcard hSK hSp
  have hS : CFSG.Assembly.LargeEvenSStar p B y K :=
    ⟨hSHat.1, hSHat.2.1, hSHat.2.2.1, hcomp, hcyc⟩
  have hψN : ψ ∈ Subgroup.normalizer (ggAutomizer K Bs : Set (MulAut ↥Bs)) :=
    hdRo7SUKStabAux_aut_normalizer hS hnc hy ψ hψ hfix
  obtain ⟨σ, hσ, hσs⟩ := Subgroup.mem_map.mp ((hAK s).mpr hs)
  have hconj : ψ * σ * ψ⁻¹ ∈ ggAutomizer K Bs :=
    (Subgroup.mem_normalizer_iff.mp hψN σ).mp hσ
  refine (hAK (a * s * a⁻¹)).mp ?_
  refine Subgroup.mem_map.mpr ⟨ψ * σ * ψ⁻¹, hconj, ?_⟩
  rw [map_mul, map_mul, map_inv, hψa, hσs]

theorem su_kstab_holds : SUKStabLeaf := by
  intro G _ _ p B Bs x L D J y K hH hp hrow m V _ _ ι b hy hp3 hm h3 hiy hAK a ha hafix s hs
  haveI : Fact p.Prime := hp
  exact hdRo7SUKStabAux_of_noncyclic hH
    (CFSG.StandardType.HdRo7KNC.knc_holds G p B Bs x L D J y K hH (Or.inr hrow))
    ι b hy hp3 hm h3 hiy hAK a ha hafix s hs

end CFSG.StandardType.HdRo7SU
