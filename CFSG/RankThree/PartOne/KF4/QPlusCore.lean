module

public import CFSG.RankThree.PartOne.KF4.EvenCore

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.LieType.Chevalley
open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.LocalRank CFSG.RankThree.PartOne.KE
open scoped Pointwise commutatorElement


theorem layer_commutator_of_embedding {C G : Type*} [Group C] [Finite C] [Group G]
    {D : Subgroup C} (ψ : D →* G) (hψ : Function.Injective ψ) {P : Subgroup G}
    (h : ⁅ψ.range, ψ.range⁆ = P) (hL : CFSG.layer ↥P = ⊤) :
    CFSG.layer (⁅D, D⁆ : Subgroup C) = ⊤ ∧
      (⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆).map ψ = P ∧
      (⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆).map D.subtype = ⁅D, D⁆ := by
  have h1 : (⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆).map D.subtype = ⁅D, D⁆ := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h2 : (⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆).map ψ = P := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, h]
  refine ⟨?_, h2, h1⟩
  set T' : Subgroup D := ⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆ with hT'
  have e1 : T' ≃* (T'.map ψ) := Subgroup.equivMapOfInjective _ ψ hψ
  have e2 : T' ≃* (⁅D, D⁆ : Subgroup C) :=
    (Subgroup.equivMapOfInjective _ D.subtype D.subtype_injective).trans
      (MulEquiv.subgroupCongr h1)
  have e3 : T' ≃* P := e1.trans (MulEquiv.subgroupCongr h2)
  have hfin : Finite ↥P := by
    have : Finite D := inferInstance
    exact Finite.of_equiv T' e3.toEquiv
  exact CFSG.LocalCores.layer_eq_top_of_surjective hL (e3.symm.trans e2).toMonoidHom
    (e3.symm.trans e2).surjective

theorem f4_even_core_odd_of_embedding_layer (K : Type) [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (L : Type) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    {p : ℕ} (hp : p.Prime) {B : Subgroup (MulAut (adjointGroup .F4 K))}
    (hB : (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range ≤ B)
    {x : adjointGroup .F4 K} (c : adjointGroup .F4 K) (g0 : ModGL .F4 L)
    (hg0C : g0 ∈ adjointGroup .F4 L)
    (ψ : Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)) →* ModGL .F4 L)
    (hψinj : Function.Injective ψ)
    (hψ : ∀ y, ψ y = g0⁻¹ * adjEmb .F4 K L (c * (y : adjointGroup .F4 K) * c⁻¹) * g0)
    {Pt : Subgroup (ModGL .F4 L)} (hPtL : CFSG.layer ↥Pt = ⊤)
    (hcomm : ⁅ψ.range, ψ.range⁆ = Pt) (i : Fin Tag.F4.rank) (h₀ : ModGL .F4 L)
    (hh₀C : h₀ ∈ adjointGroup .F4 L)
    (hroot : ∀ Y : SL2 K, h₀ * simpleRootSL2 .F4 L i
        (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h₀⁻¹ ∈ Pt)
    (hsolv : ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))),
      V.Normal → Group.IsSolvable V → Odd (Nat.card V)) :
    Odd (Nat.card ↥(inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut (adjointGroup .F4 K))} :
        Set (MulAut (adjointGroup .F4 K)))))) := by
  classical
  have : Finite (adjointGroup .F4 K) := by
    have : Finite (ModGL .F4 K) := finite_modGL
    infer_instance
  obtain ⟨hRL, h2, h1⟩ := layer_commutator_of_embedding ψ hψinj hcomm hPtL
  have hodd : Odd (Nat.card ↥(Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)) ⊓
      Subgroup.centralizer ((⁅Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)),
        Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))⁆ :
          Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K)))) :=
    odd_card_inf_centralizer_derived hsolv
  obtain ⟨h'', hh''⟩ : ∃ h'' : ModGL .F4 L, h'' = (adjEmb .F4 K L c)⁻¹ * g0 * h₀ := ⟨_, rfl⟩
  have hh''C : h'' ∈ adjointGroup .F4 L := by
    rw [hh'']
    exact mul_mem (mul_mem (inv_mem (adjEmb_mem c)) hg0C) hh₀C
  have hmapB := map_subtype_theta_centralizer hp B (⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B)
  have hle : Pt ≤ ψ.range := by
    rw [← hcomm, Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hKey : ∀ Y : SL2 K, ∃ y ∈ (⁅Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)),
      Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K)),
      adjEmb .F4 K L y = h'' * simpleRootSL2 .F4 L i
      (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h''⁻¹ := by
    intro Y
    obtain ⟨y', hy'ψ⟩ := hle (hroot Y)
    have h3 := hψ y'
    rw [hy'ψ] at h3
    have h4 : adjEmb .F4 K L (c * (y' : adjointGroup .F4 K) * c⁻¹) =
        g0 * (h₀ * simpleRootSL2 .F4 L i (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) *
          h₀⁻¹) * g0⁻¹ := by
      rw [h3]
      group
    rw [map_mul, map_mul, map_inv] at h4
    have hmem := hroot Y
    rw [← h2] at hmem
    obtain ⟨y'', hy'', hy''ψ⟩ := hmem
    have hyy : y'' = y' := hψinj (hy''ψ.trans hy'ψ.symm)
    refine ⟨(y' : adjointGroup .F4 K), ?_, ?_⟩
    · rw [← h1]
      exact ⟨y', hyy ▸ hy'', rfl⟩
    · rw [hh'']
      calc adjEmb .F4 K L (y' : adjointGroup .F4 K)
          = (adjEmb .F4 K L c)⁻¹ * (adjEmb .F4 K L c * adjEmb .F4 K L (y' : adjointGroup .F4 K) *
              (adjEmb .F4 K L c)⁻¹) * adjEmb .F4 K L c := by group
        _ = _ := by rw [h4]; group
  obtain ⟨M, _, _, ι, g', hg'C, R₀, hR₀R, hRg⟩ :=
    exists_even_descended_root K L i h'' hh''C
      (⁅Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)),
        Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K))
      hKey
  have hS := even_F4_descended_root_layer_centralizer_local_core_odd hf K hK hp B hB x hRL hodd
    R₀ hR₀R M ι hg'C (IsRoot.basis i) 1 hRg
  rw [← hmapB, Subgroup.card_map_of_injective B.subtype_injective]
  exact hS

end CFSG.RankThree.PartOne.KF4
