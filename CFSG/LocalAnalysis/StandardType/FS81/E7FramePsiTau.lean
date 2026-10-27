module

public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameGraph

public section

namespace CFSG.StandardType.FrameRoute.FS81.E7Frame

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution.WeakCT
open CFSG.Timmesfeld CFSG.SeitzReduction.E7Pilot CFSG.SeitzReduction.EPilot
open CFSG.ClassicalInvolution.ModelFacts
open CFSG.RankThree.GF2n.Smith81.D6Spin (swap45 swap45_mem_roots)
open CFSG.LieType.Universal.Spin (isFiniteType_cartanD)
open CFSG.LieType.RootSystem (roots)

attribute [-instance] CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

@[expose] def perpHigh : Fin (Tag.rank .E7) → ℤ := ![0, 1, 1, 2, 2, 2, 1]

@[expose] def tauFrameWord : List (Fin (Tag.rank .E7)) :=
  [5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1]

@[expose] def psiFrameWord : List (Fin (Tag.rank .E7)) :=
  [2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]

@[expose] def psiFrameWordX : List (Fin (Tag.rank .E7)) :=
  [1, 3, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 1]

theorem tauFrameWord_smul :
    (coxeterSystem .E7).wordProd tauFrameWord • theta = Pi.single 6 1 ∧
      (coxeterSystem .E7).wordProd tauFrameWord • (Pi.single 6 1 : Fin (Tag.rank .E7) → ℤ) =
        Pi.single 0 1 ∧
      (coxeterSystem .E7).wordProd tauFrameWord • rootA234 = Pi.single 1 1 ∧
      (coxeterSystem .E7).wordProd tauFrameWord • (Pi.single 5 1 : Fin (Tag.rank .E7) → ℤ) =
        Pi.single 2 1 ∧
      (coxeterSystem .E7).wordProd tauFrameWord • (Pi.single 4 1 : Fin (Tag.rank .E7) → ℤ) =
        Pi.single 3 1 ∧
      (coxeterSystem .E7).wordProd tauFrameWord • perpHigh = lam := by
  simp only [tauFrameWord, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one,
    mul_smul, simple_smul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact List.ofFn_injective (by decide +kernel)

theorem psiFrameWord_smul :
    (coxeterSystem .E7).wordProd psiFrameWord • theta = Pi.single 0 1 ∧
      (coxeterSystem .E7).wordProd psiFrameWord • (Pi.single 6 1 : Fin (Tag.rank .E7) → ℤ) =
        Pi.single 1 1 ∧
      (coxeterSystem .E7).wordProd psiFrameWord • (Pi.single 5 1 : Fin (Tag.rank .E7) → ℤ) =
        Pi.single 3 1 ∧
      (coxeterSystem .E7).wordProd psiFrameWord • (Pi.single 4 1 : Fin (Tag.rank .E7) → ℤ) =
        Pi.single 4 1 ∧
      (coxeterSystem .E7).wordProd psiFrameWord • (Pi.single 3 1 : Fin (Tag.rank .E7) → ℤ) =
        Pi.single 5 1 ∧
      (coxeterSystem .E7).wordProd psiFrameWord • (Pi.single 1 1 : Fin (Tag.rank .E7) → ℤ) =
        Pi.single 6 1 ∧
      (coxeterSystem .E7).wordProd psiFrameWord • perpHigh = mu ∧
      (coxeterSystem .E7).wordProd psiFrameWord • (Pi.single 2 1 : Fin (Tag.rank .E7) → ℤ) =
        lam := by
  simp only [psiFrameWord, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one,
    mul_smul, simple_smul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact List.ofFn_injective (by decide +kernel)

theorem psiFrameWordX_smul :
    (coxeterSystem .E7).wordProd psiFrameWordX • (Pi.single 6 1 : Fin (Tag.rank .E7) → ℤ) =
        Pi.single 2 1 ∧
      (coxeterSystem .E7).wordProd psiFrameWordX • (Pi.single 5 1 : Fin (Tag.rank .E7) → ℤ) =
        Pi.single 3 1 ∧
      (coxeterSystem .E7).wordProd psiFrameWordX • (Pi.single 4 1 : Fin (Tag.rank .E7) → ℤ) =
        Pi.single 4 1 ∧
      (coxeterSystem .E7).wordProd psiFrameWordX • (Pi.single 3 1 : Fin (Tag.rank .E7) → ℤ) =
        Pi.single 5 1 ∧
      (coxeterSystem .E7).wordProd psiFrameWordX • (Pi.single 1 1 : Fin (Tag.rank .E7) → ℤ) =
        -perpHigh ∧
      (coxeterSystem .E7).wordProd psiFrameWordX • perpHigh = -Pi.single 1 1 ∧
      (coxeterSystem .E7).wordProd psiFrameWordX • (Pi.single 2 1 : Fin (Tag.rank .E7) → ℤ) =
        Pi.single 6 1 := by
  simp only [psiFrameWordX, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one,
    mul_smul, simple_smul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact List.ofFn_injective (by decide +kernel)

theorem single_mem_perpRoots_E7 {i : Fin (Tag.rank .E7)} (hi : i ≠ 0) :
    (Pi.single i 1 : Fin (Tag.rank .E7) → ℤ) ∈ perpRoots .E7 :=
  single_mem_perpRoots hi

section Roots


theorem perpHigh_mem_perpRoots : perpHigh ∈ perpRoots .E7 :=
  ⟨mem_rootFinset.1 (by decide +kernel), rfl⟩

end Roots

section Core


theorem isInnerAut_of_congr_eq_conj {M : Subgroup (ModGL .E7 (ZMod 2))} (e : ↥Dperp ≃* ↥M)
    {φ : MulAut ↥Dperp} {y : M} (hy : MulAut.congr e φ = MulAut.conj y) :
    φ = MulAut.conj (e.symm y) := by
  refine MulEquiv.ext fun z => ?_
  have h := congrArg (fun χ : MulAut M => χ (e z)) hy
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.conj_apply] at h
  rw [MulAut.conj_apply, ← e.symm_apply_apply (φ z), h, map_mul, map_mul, map_inv,
    e.symm_apply_apply]

end Core

section Native


theorem map_conj_Dperp_tau :
    Dperp.map (MulAut.conj (wordRepE7 (ZMod 2) tauFrameWord : ModGL .E7 (ZMod 2))).toMonoidHom =
      M6 := by
  rw [map_conj_Dperp, tauFrameWord_smul.1]
  rfl

@[expose] noncomputable def tauEquiv : ↥Dperp ≃* ↥M6 :=
  conjDperp _ map_conj_Dperp_tau

@[expose] noncomputable def e7Tau : MulAut ↥M6 := MulAut.congr tauEquiv perpGraph

theorem e7Tau_fix {v : Fin 6 → ℤ} (hv : v ∈ roots (isFiniteType_cartanD 6) ∅)
    (hsv : swap45 v = v) {x : M6}
    (hx : (x : ModGL .E7 (ZMod 2)) ∈ J ((coxeterSystem .E7).wordProd tauFrameWord • d6Embed v)) :
    e7Tau x = x := by
  rw [← map_conj_wordRepE7_J tauFrameWord (isRoot_d6Embed hv)] at hx
  have h2 : ((tauEquiv.symm x : Dperp) : ModGL .E7 (ZMod 2)) ∈ J (d6Embed v) := by
    rw [tauEquiv, coe_conjDperp_symm]
    exact conj_inv_mem_of_mem_map hx
  have h3 : perpGraph (tauEquiv.symm x) = tauEquiv.symm x :=
    perpGraph_fix hv hsv h2 (tauEquiv.symm x).2
  show tauEquiv (perpGraph (tauEquiv.symm x)) = x
  rw [h3, MulEquiv.apply_symm_apply]

theorem e7NatTau_holds : E7NatTau := by
  obtain ⟨-, hw0, hw1, hw2, hw3, hwl⟩ := tauFrameWord_smul
  refine ⟨e7Tau, fun ⟨y, hy⟩ => not_isInnerAut_perpGraph ⟨_, isInnerAut_of_congr_eq_conj _ hy⟩,
    fun x hx => ?_⟩
  rcases hx with h | h | h | h | h
  · refine e7Tau_fix (v := Pi.single 0 1)
      (mem_rootsD6_of_isRoot (γ := Pi.single 6 1) (by decide) (isRoot_single .E7 _)) (by decide)
      ?_
    rw [show d6Embed (Pi.single 0 1) = (Pi.single 6 1 : Fin (Tag.rank .E7) → ℤ) by decide, hw0]
    exact h
  · refine e7Tau_fix (v := ![0, 0, 0, 1, 1, 1])
      (mem_rootsD6_of_isRoot (γ := rootA234) (by decide) (mem_rootFinset.1 (by decide +kernel)))
      (by decide) ?_
    rw [show d6Embed ![0, 0, 0, 1, 1, 1] = rootA234 by decide, hw1]
    exact h
  · refine e7Tau_fix (v := Pi.single 1 1)
      (mem_rootsD6_of_isRoot (γ := Pi.single 5 1) (by decide) (isRoot_single .E7 _)) (by decide)
      ?_
    rw [show d6Embed (Pi.single 1 1) = (Pi.single 5 1 : Fin (Tag.rank .E7) → ℤ) by decide, hw2]
    exact h
  · refine e7Tau_fix (v := Pi.single 2 1)
      (mem_rootsD6_of_isRoot (γ := Pi.single 4 1) (by decide) (isRoot_single .E7 _)) (by decide)
      ?_
    rw [show d6Embed (Pi.single 2 1) = (Pi.single 4 1 : Fin (Tag.rank .E7) → ℤ) by decide, hw3]
    exact h
  · refine e7Tau_fix (v := ![1, 2, 2, 2, 1, 1])
      (mem_rootsD6_of_isRoot (γ := perpHigh) (by decide) perpHigh_mem_perpRoots.1) (by decide)
      ?_
    rw [show d6Embed ![1, 2, 2, 2, 1, 1] = perpHigh by decide, hwl]
    exact h

theorem map_conj_Dperp_psi :
    Dperp.map (MulAut.conj (wordRepE7 (ZMod 2) psiFrameWord : ModGL .E7 (ZMod 2))).toMonoidHom =
      M0 := by
  rw [map_conj_Dperp, psiFrameWord_smul.1]
  rfl

@[expose] noncomputable def psiEquiv : ↥Dperp ≃* ↥M0 :=
  conjDperp _ map_conj_Dperp_psi

theorem wordRepE7_psiFrameWordX_mem :
    (wordRepE7 (ZMod 2) psiFrameWordX : ModGL .E7 (ZMod 2)) ∈ Dperp := by
  have hall : ∀ i ∈ psiFrameWordX, i ≠ 0 := by decide
  rw [coe_wordRepE7]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  have hi0 : i ≠ 0 := hall i hi
  refine J_le_Dperp (single_mem_perpRoots_E7 hi0) ?_
  show _ ∈ rootRankOneGroup .E7 (ZMod 2) (Pi.single i 1)
  rw [rootRankOneGroup_eq_sup (K := ZMod 2) (isRoot_single .E7 i)]
  exact weylElt_mem_rootPair i 1

@[expose] noncomputable def psiX : ↥Dperp :=
  ⟨wordRepE7 (ZMod 2) psiFrameWordX, wordRepE7_psiFrameWordX_mem⟩

@[expose] noncomputable def e7Psi : MulAut ↥M0 :=
  MulAut.congr psiEquiv (perpGraph * MulAut.conj psiX)

theorem not_isInnerAut_e7Psi : ¬ IsInnerAut e7Psi := by
  rintro ⟨y, hy⟩
  have h := isInnerAut_of_congr_eq_conj psiEquiv hy
  apply not_isInnerAut_perpGraph
  refine ⟨psiEquiv.symm y * psiX⁻¹, ?_⟩
  rw [map_mul, ← h, map_inv, mul_inv_cancel_right]

theorem e7Psi_map_J {γ' : Fin (Tag.rank .E7) → ℤ} {v : Fin 6 → ℤ} (hγ' : γ' ∈ perpRoots .E7)
    (hv : v ∈ roots (isFiniteType_cartanD 6) ∅)
    (h2 : J ((coxeterSystem .E7).wordProd psiFrameWordX • γ') = J (d6Embed v)) :
    ((J ((coxeterSystem .E7).wordProd psiFrameWord • γ')).subgroupOf M0).map
        e7Psi.toMonoidHom =
      (J ((coxeterSystem .E7).wordProd psiFrameWord • d6Embed (swap45 v))).subgroupOf M0 := by
  have hv' := swap45_mem_roots hv
  have he := coe_conjDperp _ map_conj_Dperp_psi
  have hsrc : (J ((coxeterSystem .E7).wordProd psiFrameWord • γ')).subgroupOf M0 =
      ((J γ').subgroupOf Dperp).map psiEquiv.toMonoidHom := by
    rw [psiEquiv, map_subgroupOf_of_coe _ _ he (J_le_Dperp hγ'),
      map_conj_wordRepE7_J psiFrameWord hγ'.1]
  have hcomp : e7Psi.toMonoidHom.comp psiEquiv.toMonoidHom =
      psiEquiv.toMonoidHom.comp ((perpGraph.toMonoidHom).comp (MulAut.conj psiX).toMonoidHom) := by
    ext z
    simp [e7Psi, MulAut.congr_apply]
  have hx : ((J γ').subgroupOf Dperp).map (MulAut.conj psiX).toMonoidHom =
      (J (d6Embed v)).subgroupOf Dperp := by
    rw [map_subgroupOf_of_coe (MulAut.conj psiX) (wordRepE7 (ZMod 2) psiFrameWordX : ModGL .E7 (ZMod 2))
      (fun a => rfl) (J_le_Dperp hγ'), map_conj_wordRepE7_J psiFrameWordX hγ'.1, h2]
  rw [hsrc, Subgroup.map_map, hcomp, ← Subgroup.map_map, ← Subgroup.map_map, hx,
    map_perpGraph_J hv, psiEquiv, map_subgroupOf_of_coe _ _ he
      (J_le_Dperp (d6Embed_mem_perpRoots hv')),
    map_conj_wordRepE7_J psiFrameWord (isRoot_d6Embed hv')]

theorem e7NatPsi_holds : E7NatPsi := by
  obtain ⟨-, h6, h5, h4, h3, h1, hh, h2⟩ := psiFrameWord_smul
  obtain ⟨x6, x5, x4, x3, x1, xh, x2⟩ := psiFrameWordX_smul
  have p6 := single_mem_perpRoots_E7 (i := 6) (by decide)
  have p5 := single_mem_perpRoots_E7 (i := 5) (by decide)
  have p4 := single_mem_perpRoots_E7 (i := 4) (by decide)
  have p3 := single_mem_perpRoots_E7 (i := 3) (by decide)
  have p2 := single_mem_perpRoots_E7 (i := 2) (by decide)
  have p1 := single_mem_perpRoots_E7 (i := 1) (by decide)
  have ph := perpHigh_mem_perpRoots
  have hd0 : d6Embed (Pi.single 0 1) = (Pi.single 6 1 : Fin (Tag.rank .E7) → ℤ) := by decide
  have hd1 : d6Embed (Pi.single 1 1) = (Pi.single 5 1 : Fin (Tag.rank .E7) → ℤ) := by decide
  have hd2 : d6Embed (Pi.single 2 1) = (Pi.single 4 1 : Fin (Tag.rank .E7) → ℤ) := by decide
  have hd3 : d6Embed (Pi.single 3 1) = (Pi.single 3 1 : Fin (Tag.rank .E7) → ℤ) := by decide
  have hd4 : d6Embed (Pi.single 4 1) = (Pi.single 2 1 : Fin (Tag.rank .E7) → ℤ) := by decide
  have hd5 : d6Embed (Pi.single 5 1) = (Pi.single 1 1 : Fin (Tag.rank .E7) → ℤ) := by decide
  have hdh : d6Embed ![1, 2, 2, 2, 1, 1] = perpHigh := by decide
  have r0 := mem_rootsD6_of_isRoot hd0 (isRoot_single .E7 _)
  have r1 := mem_rootsD6_of_isRoot hd1 (isRoot_single .E7 _)
  have r2 := mem_rootsD6_of_isRoot hd2 (isRoot_single .E7 _)
  have r3 := mem_rootsD6_of_isRoot hd3 (isRoot_single .E7 _)
  have r4 := mem_rootsD6_of_isRoot hd4 (isRoot_single .E7 _)
  have r5 := mem_rootsD6_of_isRoot hd5 (isRoot_single .E7 _)
  have rh := mem_rootsD6_of_isRoot hdh ph.1
  refine ⟨e7Psi, not_isInnerAut_e7Psi, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have h := e7Psi_map_J p6 r4 (by rw [x6, hd4])
    rwa [h6, show swap45 (Pi.single 4 1) = Pi.single 5 1 by decide, hd5, h1] at h
  ·
    have h := e7Psi_map_J p5 r3 (by rw [x5, hd3])
    rwa [h5, show swap45 (Pi.single 3 1) = Pi.single 3 1 by decide, hd3, h3] at h
  ·
    have h := e7Psi_map_J p4 r2 (by rw [x4, hd2])
    rwa [h4, show swap45 (Pi.single 2 1) = Pi.single 2 1 by decide, hd2, h4] at h
  ·
    have h := e7Psi_map_J p3 r1 (by rw [x3, hd1])
    rwa [h3, show swap45 (Pi.single 1 1) = Pi.single 1 1 by decide, hd1, h5] at h
  ·
    have h := e7Psi_map_J p1 rh (by rw [x1, hdh, J_neg ph.1])
    rwa [h1, show swap45 ![1, 2, 2, 2, 1, 1] = ![1, 2, 2, 2, 1, 1] by decide, hdh, hh] at h
  ·
    have h := e7Psi_map_J ph r5 (by rw [xh, hd5, J_neg (isRoot_single .E7 _)])
    rwa [hh, show swap45 (Pi.single 5 1) = Pi.single 4 1 by decide, hd4, h2] at h
  ·
    have h := e7Psi_map_J p2 r0 (by rw [x2, hd0])
    rwa [h2, show swap45 (Pi.single 0 1) = Pi.single 0 1 by decide, hd0, h6] at h

end Native

end CFSG.StandardType.FrameRoute.FS81.E7Frame
