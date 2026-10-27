module

public import CFSG.RankThree.PartOne.FOCD.CompSimple
import CFSG.RankThree.Chevalley.SteinbergCEG2EvenQPlusTorus
import CFSG.RankThree.PartOne.KF.QuadExt
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.RankThree.Classical.SL2SemilinearRoots
public import CFSG.LieType.Chevalley.LangRootRankOne
public import CFSG.LieType.Chevalley.ToralCentralizerBruhat

public section

namespace CFSG.RankThree.PartOne.FOCD

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne


section Data

variable {K : Type} [Field K] [Finite K] [CharP K 2] {K₂ : Type} [Field K₂] [Finite K₂]
  [Algebra K K₂] {p : ℕ}

omit [CharP K 2] in
theorem compGoodAt_of_qplus_data (hp : p.Prime) (hpq : p ∣ Nat.card K + 1)
    (Γ : Subgroup (ModGL .G2 K₂)) (S : Sylow p ↥Γ)
    (hS : (S : Subgroup ↥Γ) ≤ (torusGroup .G2 K₂ ⊓ Γ).subgroupOf Γ)
    (hrank1 : ∀ α : Fin Tag.G2.rank → ℤ, IsRoot .G2 α → ∃ P : GL (Fin 2) K₂,
      (rootRankOneGroup .G2 K₂ α ⊓ Γ).comap (rootSL2 .G2 K₂ α) =
        (Matrix.SpecialLinearGroup.map (algebraMap K K₂)).range.map
          (CFSG.RankThree.Classical.conjSL P) ∧
      IsSimpleGroup ↥(rootRankOneGroup .G2 K₂ α ⊓ Γ) ∧
      ∃ x y : ↥(rootRankOneGroup .G2 K₂ α ⊓ Γ), x * y ≠ y * x)
    (hunique : ∀ x ∈ torusGroup .G2 K₂ ⊓ Γ, ∃! a : Fin Tag.G2.rank → K₂ˣ,
      rootDiagUnit .G2 a = x)
    (hab : ∀ x ∈ torusGroup .G2 K₂, ∀ y ∈ torusGroup .G2 K₂, x * y = y * x)
    (hcent : ∀ a : Fin Tag.G2.rank → K₂ˣ, rootDiagUnit .G2 a ∈ torusGroup .G2 K₂ ⊓ Γ →
      orderOf (rootDiagUnit .G2 a) = p →
      (rootCharKernel a = ∅ →
        Γ ⊓ Subgroup.centralizer ({rootDiagUnit .G2 a} : Set (ModGL .G2 K₂)) =
          torusGroup .G2 K₂ ⊓ Γ) ∧
      (rootCharKernel a ≠ ∅ → ∃ α : Fin Tag.G2.rank → ℤ, IsRoot .G2 α ∧
        ⁅Γ ⊓ Subgroup.centralizer ({rootDiagUnit .G2 a} : Set (ModGL .G2 K₂)),
          Γ ⊓ Subgroup.centralizer ({rootDiagUnit .G2 a} : Set (ModGL .G2 K₂))⁆ =
          rootRankOneGroup .G2 K₂ α ⊓ Γ))
    (c : ↥Γ) (hcord : orderOf c = p) : CompGoodAt p c := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL .G2 K₂) := finite_modGL
  have hcP : IsPGroup p (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hcord, pow_one])
  obtain ⟨S', hS'⟩ := hcP.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq ↥Γ S S'
  have hcmem : c ∈ (S' : Subgroup ↥Γ) := hS' (Subgroup.mem_zpowers c)
  rw [← hh, Sylow.coe_subgroup_smul] at hcmem
  have hcS : (MulAut.conj h)⁻¹ • c ∈ (S : Subgroup ↥Γ) :=
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem.1 hcmem
  have hscdef : (MulAut.conj h)⁻¹ • c = h⁻¹ * c * h := by
    rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply]
    simp
  rw [hscdef] at hcS
  have hsT := hS hcS
  refine compGoodAt_conj h⁻¹ ?_
  have hconj : h⁻¹ * c * h⁻¹⁻¹ = h⁻¹ * c * h := by simp
  rw [hconj]
  have hsord : orderOf (h⁻¹ * c * h) = p := by
    rw [← hconj, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hcord
  have hsmem : (((h⁻¹ * c * h : ↥Γ)) : ModGL .G2 K₂) ∈ torusGroup .G2 K₂ ⊓ Γ :=
    ⟨(Subgroup.mem_subgroupOf.1 hsT).1, (h⁻¹ * c * h : ↥Γ).2⟩
  obtain ⟨a, ha, -⟩ := hunique _ hsmem
  have hdord : orderOf (rootDiagUnit .G2 a) = p := by
    rw [ha, Subgroup.orderOf_coe]
    exact hsord
  have hdmem : rootDiagUnit .G2 a ∈ torusGroup .G2 K₂ ⊓ Γ := ha ▸ hsmem
  have hdΓ : rootDiagUnit .G2 a ∈ Γ := hdmem.2
  have hseq : h⁻¹ * c * h = (⟨rootDiagUnit .G2 a, hdΓ⟩ : ↥Γ) := Subtype.ext ha.symm
  rw [hseq]
  by_cases hker : rootCharKernel a = ∅
  ·
    have hD := (hcent a hdmem hdord).1 hker
    refine compGoodAt_of_comm fun x hx y hy => ?_
    have hx' : (x : ModGL .G2 K₂) ∈ Γ ⊓ Subgroup.centralizer
        ({rootDiagUnit .G2 a} : Set (ModGL .G2 K₂)) :=
      ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hx))⟩
    have hy' : (y : ModGL .G2 K₂) ∈ Γ ⊓ Subgroup.centralizer
        ({rootDiagUnit .G2 a} : Set (ModGL .G2 K₂)) :=
      ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hy))⟩
    rw [hD] at hx' hy'
    exact Subtype.ext (hab _ hx'.1 _ hy'.1)
  · obtain ⟨α, hα, hcomm⟩ := (hcent a hdmem hdord).2 hker
    obtain ⟨P, hcomap, hsimple, hnc⟩ := hrank1 α hα
    set D : Subgroup (ModGL .G2 K₂) :=
      Γ ⊓ Subgroup.centralizer ({rootDiagUnit .G2 a} : Set (ModGL .G2 K₂)) with hD
    set Q' : Subgroup (ModGL .G2 K₂) := rootRankOneGroup .G2 K₂ α ⊓ Γ with hQ'
    have hQD : Q' ≤ D := by
      rw [← hcomm]
      exact Subgroup.commutator_le.2 fun x hx y hy => by
        rw [commutatorElement_def]
        exact D.mul_mem (D.mul_mem (D.mul_mem hx hy) (D.inv_mem hx)) (D.inv_mem hy)
    have hDQ : ⁅D, D⁆ ≤ Q' := le_of_eq hcomm
    have hSLinj : Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2)
        (algebraMap K K₂)) := by
      intro A B hAB
      ext i j
      have h1 := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) K₂ =>
        (X : Matrix (Fin 2) (Fin 2) K₂) i j) hAB
      simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Matrix.map_apply] at h1
      exact (algebraMap K K₂).injective h1
    have hPinj : Function.Injective (CFSG.RankThree.Classical.conjSL P) := fun A B hAB => by
      have h1 := congrArg (CFSG.RankThree.Classical.conjSL P⁻¹) hAB
      rwa [← CFSG.RankThree.Classical.conjSL_mul, ← CFSG.RankThree.Classical.conjSL_mul,
        inv_mul_cancel, CFSG.RankThree.Classical.conjSL_one,
        CFSG.RankThree.Classical.conjSL_one] at h1
    have hinj : Function.Injective (rootSL2 .G2 K₂ α) := rootSL2_injective_of_field α
    have hQle : Q' ≤ rootRankOneGroup .G2 K₂ α := inf_le_left
    have hmap : (Q'.comap (rootSL2 .G2 K₂ α)).map (rootSL2 .G2 K₂ α) = Q' := by
      rw [Subgroup.map_comap_eq]
      exact inf_of_le_right hQle
    have hcardQ : Nat.card Q' = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
      calc Nat.card Q' = Nat.card ((Q'.comap (rootSL2 .G2 K₂ α)).map (rootSL2 .G2 K₂ α)) := by
            rw [hmap]
        _ = Nat.card (Q'.comap (rootSL2 .G2 K₂ α)) := Subgroup.card_map_of_injective hinj
        _ = Nat.card (((Matrix.SpecialLinearGroup.map (algebraMap K K₂)).range).map
              (CFSG.RankThree.Classical.conjSL P)) := by rw [hcomap]
        _ = Nat.card (Matrix.SpecialLinearGroup.map (algebraMap K K₂)).range :=
            Subgroup.card_map_of_injective hPinj
        _ = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) :=
            (Nat.card_congr (MonoidHom.ofInjective hSLinj).toEquiv).symm
    have hpQ : p ∣ Nat.card Q' := by
      rw [hcardQ, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
      refine Dvd.dvd.mul_left (hpq.trans ?_) _
      have hq1 : 1 ≤ Nat.card K := Nat.card_pos
      rw [show Nat.card K ^ 2 - 1 = (Nat.card K - 1) * (Nat.card K + 1) by
        obtain ⟨w, hw⟩ : ∃ w, Nat.card K = w + 1 := ⟨Nat.card K - 1, by omega⟩
        rw [hw]; simp only [Nat.add_sub_cancel]; ring_nf; omega]
      exact Dvd.intro_left _ rfl
    exact compGoodAt_of_simple_layer hdΓ hsimple hnc hQD hDQ hpQ

end Data

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

theorem compGoodAt_G2_qplus (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ Nat.card K + 1)
    (b : adjointGroup .G2 K) (hb1 : b ≠ 1) (hbp : b ^ p = 1) : CompGoodAt p b := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, z, hg, hzC, hzdef, hz, hΓ, hF2, ⟨φ⟩, hodd, ⟨S, hS⟩, hE, hrank1, hunique, hcent⟩ :=
    even_G2_qplus_torus_and_fixed_root_centralizers K hp hp3 hpq (KFQ.Qext K) KFQ.finrank_qext
      (KFQ.frobQ K).toRingEquiv fun c => KFQ.frobQ_apply c
  have : Finite (KFQ.Qext K) := inferInstance
  let ψ : ModGL .G2 K →* ModGL .G2 (KFQ.Qext K) :=
    (MulAut.conj g).toMonoidHom.comp (baseChangeGL (algebraMap K (KFQ.Qext K)))
  have hψ : Function.Injective ψ :=
    (MulAut.conj g).injective.comp (baseChangeGL_injective (τ := .G2) (algebraMap K (KFQ.Qext K)))
  let ε : adjointGroup .G2 K ≃* conjEntrywiseImage K g :=
    Subgroup.equivMapOfInjective (adjointGroup .G2 K) ψ hψ
  refine compGoodAt_of_mulEquiv ε ?_
  have hcord : orderOf (ε b) = p := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hbp hb1
  obtain ⟨e₂, -⟩ := G2_F4_torus_coordinates .G2 (Or.inl rfl) (KFQ.Qext K)
  have hHcomm : ∀ x ∈ torusGroup .G2 (KFQ.Qext K), ∀ y ∈ torusGroup .G2 (KFQ.Qext K),
      x * y = y * x := by
    intro x hx y hy
    obtain ⟨u, hu⟩ : ∃ u, e₂ u = ⟨x, hx⟩ := ⟨e₂.symm ⟨x, hx⟩, by simp⟩
    obtain ⟨v, hv⟩ : ∃ v, e₂ v = ⟨y, hy⟩ := ⟨e₂.symm ⟨y, hy⟩, by simp⟩
    have := congrArg Subtype.val
      (show e₂ u * e₂ v = e₂ v * e₂ u by rw [← map_mul, ← map_mul, mul_comm])
    rw [hu, hv] at this
    exact this
  refine compGoodAt_of_qplus_data hp hpq (conjEntrywiseImage K g) S hS ?_ hunique hHcomm ?_ (ε b)
    hcord
  · intro α hα
    obtain ⟨P, h1, h2, -, h3⟩ := hrank1 α hα
    exact ⟨P, h1, h2, h3⟩
  · intro a h1 h2
    obtain ⟨hA, hB, -⟩ := hcent a h1 h2
    refine ⟨hA, fun hne => ?_⟩
    obtain ⟨α, hα, -, hc, -⟩ := hB hne
    exact ⟨α, hα, hc⟩

end CFSG.RankThree.PartOne.FOCD
