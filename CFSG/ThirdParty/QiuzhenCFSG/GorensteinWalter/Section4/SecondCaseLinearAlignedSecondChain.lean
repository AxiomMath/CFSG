module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearAlignedChain
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The second aligned equation-(11) identity chain

Applying the exact first chain to the inverse representative `g⁻¹` and then
conjugating by `g` gives the source region identity
`M ∩ (X ⊔ E^g) = X ⊔ C_E(P₀)^g`.  Stabilization `A^g=A` transports the
centralizer endpoint at the same time.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private lemma conjugate_conjugate_sasc
    {G : Type u} [Group G] {H : Subgroup G} (a b : G) :
    conjugateSubgroup (conjugateSubgroup H a) b =
      conjugateSubgroup H (b * a) := by
  change (H.map (MulAut.conj a).toMonoidHom).map
      (MulAut.conj b).toMonoidHom =
    H.map (MulAut.conj (b * a)).toMonoidHom
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

private lemma conjugate_one_sasc
    {G : Type u} [Group G] {H : Subgroup G} :
    conjugateSubgroup H (1 : G) = H := by
  change H.map (MulAut.conj (1 : G)).toMonoidHom = H
  have hcid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [hcid, Subgroup.map_id]

private lemma conjugate_inf_sasc
    {G : Type u} [Group G] (H L : Subgroup G) (g : G) :
    conjugateSubgroup (H ⊓ L) g =
      conjugateSubgroup H g ⊓ conjugateSubgroup L g := by
  change (H ⊓ L).map (MulAut.conj g).toMonoidHom =
    H.map (MulAut.conj g).toMonoidHom ⊓
      L.map (MulAut.conj g).toMonoidHom
  exact Subgroup.map_inf H L (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective

private lemma conjugate_sup_sasc
    {G : Type u} [Group G] (H L : Subgroup G) (g : G) :
    conjugateSubgroup (H ⊔ L) g =
      conjugateSubgroup H g ⊔ conjugateSubgroup L g := by
  exact Subgroup.map_sup H L (MulAut.conj g).toMonoidHom

private lemma conjugate_centralizer_eq_sasc
    {G : Type u} [Group G] (A : Subgroup G) (g : G)
    (hAg : conjugateSubgroup A g = A) :
    conjugateSubgroup (Subgroup.centralizer (A : Set G)) g =
      Subgroup.centralizer (A : Set G) := by
  apply le_antisymm
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have haAg : g⁻¹ * a * g ∈ A := by
      have haMap : a ∈ conjugateSubgroup A g := by rwa [hAg]
      rcases Subgroup.mem_map.mp haMap with ⟨a0, ha0, ha0a⟩
      have ha0eq : a0 = g⁻¹ * a * g := by
        apply (MulAut.conj g).injective
        simpa [MulAut.conj_apply, mul_assoc] using ha0a
      rwa [← ha0eq]
    have hcomm : (g⁻¹ * a * g) * y = y * (g⁻¹ * a * g) :=
      (Subgroup.mem_centralizer_iff.mp hy) (g⁻¹ * a * g) haAg
    have hxval : x = g * y * g⁻¹ := by
      simpa [MulAut.conj_apply] using hyx.symm
    rw [hxval]
    calc
      a * (g * y * g⁻¹) = g * ((g⁻¹ * a * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * a * g)) * g⁻¹ := by rw [hcomm]
      _ = (g * y * g⁻¹) * a := by group
  · intro x hx
    have hAgInv : conjugateSubgroup A g⁻¹ = A := by
      have h := congrArg (fun H : Subgroup G => conjugateSubgroup H g⁻¹) hAg
      simp [conjugate_conjugate_sasc, conjugate_one_sasc] at h
      exact h.symm
    have hxBack : g⁻¹ * x * g ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have haAg : g * a * g⁻¹ ∈ A := by
        have haMap : g * a * g⁻¹ ∈ conjugateSubgroup A g :=
          Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
        rwa [hAg] at haMap
      have hcomm : (g * a * g⁻¹) * x = x * (g * a * g⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp hx) (g * a * g⁻¹) haAg
      calc
        a * (g⁻¹ * x * g) = g⁻¹ * ((g * a * g⁻¹) * x) * g := by group
        _ = g⁻¹ * (x * (g * a * g⁻¹)) * g := by rw [hcomm]
        _ = (g⁻¹ * x * g) * a := by group
    exact Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, hxBack, by
      simp [MulAut.conj_apply, mul_assoc]⟩

/-- The second aligned chain:
`M ∩ (X ⊔ E^g) = X ⊔ C_E(P₀)^g = C_{X⊔E^g}(A)`. -/
public theorem secondCase_linear_aligned_second_chain
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (post : SecondCaseLinearPostNineData c w d K)
    (X : Subgroup G)
    (hXleA : X ≤ post.od.A) (hXneP : X ≠ post.od.P)
    (hXconj : ∃ g : G, X = conjugateSubgroup post.od.P g) :
    ∃ g : G,
      X = conjugateSubgroup post.od.P g ∧
      g * c.t * g⁻¹ = c.t ∧
      conjugateSubgroup post.od.A g = post.od.A ∧
      (conjugateSubgroup w.M g ⊓ (post.od.P ⊔ d.E) =
          (post.od.P ⊔ d.E) ⊓ Subgroup.normalizer (X : Set G)) ∧
      ((post.od.P ⊔ d.E) ⊓ Subgroup.normalizer (X : Set G) =
          post.od.P ⊔ (Subgroup.centralizer (post.od.P0 : Set G) ⊓ d.E)) ∧
      (post.od.P ⊔ (Subgroup.centralizer (post.od.P0 : Set G) ⊓ d.E) =
          (post.od.P ⊔ d.E) ⊓ Subgroup.centralizer (post.od.A : Set G)) ∧
      (d.E ⊓ Subgroup.normalizer (X : Set G) =
          Subgroup.centralizer (post.od.P0 : Set G) ⊓ d.E) ∧
      (w.M ⊓ (X ⊔ conjugateSubgroup d.E g) =
        X ⊔ conjugateSubgroup
          (Subgroup.centralizer (post.od.P0 : Set G) ⊓ d.E) g) ∧
      (X ⊔ conjugateSubgroup
          (Subgroup.centralizer (post.od.P0 : Set G) ⊓ d.E) g =
        (X ⊔ conjugateSubgroup d.E g) ⊓
          Subgroup.centralizer (post.od.A : Set G)) := by
  classical
  obtain ⟨g, hX, hfix, hAg, hfirst⟩ :=
    secondCase_linear_aligned_chain hmin c w d K hK e post X
      hXleA hXneP hXconj
  have hPnot : ¬ ∃ z : G,
      conjugateSubgroup post.od.P z = post.od.P0 :=
    secondCase_linear_P_not_conjugate_P0 c w d K post
  have hZ : Subgroup.center d.E = ⊥ :=
    secondCase_linear_center_eq_bot hmin c w d K hK e post
  have hAgInv : conjugateSubgroup post.od.A g⁻¹ = post.od.A := by
    have h := congrArg (fun H : Subgroup G => conjugateSubgroup H g⁻¹) hAg
    simp [conjugate_conjugate_sasc, conjugate_one_sasc] at h
    exact h.symm
  let Xinv : Subgroup G := conjugateSubgroup post.od.P g⁻¹
  have hXinvleA : Xinv ≤ post.od.A := by
    calc
      Xinv ≤ conjugateSubgroup post.od.A g⁻¹ := by
        intro x hx
        rcases Subgroup.mem_map.mp hx with ⟨p, hp, rfl⟩
        exact Subgroup.mem_map.mpr ⟨p, by
          rw [post.od.A_eq]
          exact (le_sup_left : post.od.P ≤ post.od.P ⊔ post.od.P0) hp, rfl⟩
      _ = post.od.A := hAgInv
  have hXinvneP : Xinv ≠ post.od.P := by
    intro hEq
    apply hXneP
    calc
      X = conjugateSubgroup post.od.P g := hX
      _ = conjugateSubgroup Xinv g := by rw [hEq]
      _ = post.od.P := by
        dsimp [Xinv]
        simp [conjugate_conjugate_sasc, conjugate_one_sasc]
  have hfixInv : g⁻¹ * c.t * (g⁻¹)⁻¹ = c.t := by
    have hcomm : g * c.t = c.t * g := mul_inv_eq_iff_eq_mul.mp hfix
    calc
      g⁻¹ * c.t * (g⁻¹)⁻¹ = g⁻¹ * c.t * g := by simp
      _ = g⁻¹ * (c.t * g) := by group
      _ = g⁻¹ * (g * c.t) := by rw [hcomm]
      _ = c.t := by simp
  have hchainInv :=
    secondCase_linearEquation11_first_identity_chain_of_P0_centralizer
      hmin c w d K hK e post hZ g⁻¹ rfl hXinvleA hXinvneP
        hAgInv hPnot
  let C : Subgroup G :=
    Subgroup.centralizer (post.od.P0 : Set G) ⊓ d.E
  have hMC : conjugateSubgroup w.M g⁻¹ ⊓ (post.od.P ⊔ d.E) =
      post.od.P ⊔ C := by
    exact hchainInv.1.trans hchainInv.2.1
  have hCA : post.od.P ⊔ C =
      (post.od.P ⊔ d.E) ⊓
        Subgroup.centralizer (post.od.A : Set G) :=
    hchainInv.2.2.1
  have hmapMC := congrArg (fun H : Subgroup G => conjugateSubgroup H g) hMC
  have hmapCA := congrArg (fun H : Subgroup G => conjugateSubgroup H g) hCA
  have hMsecond : w.M ⊓ (X ⊔ conjugateSubgroup d.E g) =
      X ⊔ conjugateSubgroup C g := by
    simpa [conjugate_inf_sasc, conjugate_sup_sasc,
      conjugate_conjugate_sasc, conjugate_one_sasc, hX] using hmapMC
  have hCent : conjugateSubgroup
      (Subgroup.centralizer (post.od.A : Set G)) g =
        Subgroup.centralizer (post.od.A : Set G) :=
    conjugate_centralizer_eq_sasc post.od.A g hAg
  have hCsecond : X ⊔ conjugateSubgroup C g =
      (X ⊔ conjugateSubgroup d.E g) ⊓
        Subgroup.centralizer (post.od.A : Set G) := by
    simpa [conjugate_inf_sasc, conjugate_sup_sasc, hCent, hX] using hmapCA
  exact ⟨g, hX, hfix, hAg, hfirst.1, hfirst.2.1, hfirst.2.2.1,
    hfirst.2.2.2, hMsecond, hCsecond⟩

end CFSG.GorensteinWalter
