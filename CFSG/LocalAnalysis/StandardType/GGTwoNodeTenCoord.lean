module

public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepLE3E6
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGResKnownGroup
public import CFSG.LocalAnalysis.StandardType.GGRCTransfer
import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Nodes
import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepFrame
import CFSG.LocalAnalysis.StandardType.GGTWHLNormalizer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma tenCoordAux_nine_tag {p : ℕ} {labJ labX : LargeEvenLabel}
    (hr : ggRowTwoNode p labJ labX) (h8 : labX.rank = 8) :
    labX.tag = .A ∨ labX.tag = .twA := by
  rcases hr with ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩
  · exact Or.inl (by rw [hX])
  · exact Or.inr (by rw [hX])
  · exfalso
    have : labX.rank = 0 := by rw [hX]
    omega
  · exfalso
    have : labX.rank = 0 := by rw [hX]
    omega

private theorem tenCoordAux_xdatum_of_A {G : Type} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} (h : GGResXDatumA p Bs X n) : GGResXDatum p Bs X := by
  obtain ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h, α, e, hM, hW, hC, hlin, hrefl, hpair, hf, hcl⟩ := h
  exact ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h, α, hW, hC, hlin, hrefl, hpair, hf, hcl⟩

private theorem tenCoordAux_xdatumA {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hD : GGTwoNodeIndepDatum) (hH : GGResHyp p B Bs x L D J y K)
    (X : Subgroup G) (z : G) (hXz : (X = L ∧ z = x) ∨ (X = K ∧ z = y)) (hz : z ∈ X)
    {labJ labX : LargeEvenLabel} (hJΛ : LargeEvenInLambda2 labJ) (hXΛ : LargeEvenInLambda2 labX)
    (hJl : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hXl : GGHasLabel labX (↥X ⧸ Subgroup.center ↥X))
    (hr : ggRowTwoNode p labJ labX) (htag : labX.tag = .A ∨ labX.tag = .twA) :
    GGResXDatumA p Bs X labX.rank := by
  rcases (hD G p B Bs x L D J y K hH X z hXz labJ labX hJΛ hXΛ hJl hXl hr hz)
    with ⟨-, hA⟩ | ⟨hE, -⟩
  · rcases hA with hAx | ⟨-, hXA⟩
    · obtain ⟨Λ, iF, iD, M, C, V, iAC, iM, ι, φ, h, α, e, hMeq, hW, hC, hφ, hrefl, hpair,
        hf, hAL, -⟩ := hAx
      exact ⟨Λ, iF, iD, M, C, V, iAC, iM, ι, φ, h, α, e, hMeq, hW, hC, hφ, hrefl, hpair,
        hf, hAL⟩
    · exact hXA
  · exfalso
    rcases hE with h | h <;> rcases htag with h' | h' <;>
      exact absurd (h.symm.trans h') (by decide)

private theorem tenCoordAux_coxeterA_entry (m : ℕ) (i j : Fin m) :
    (CoxeterMatrix.A m) i j =
      if i = j then 1 else if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then 3 else 2 :=
  rfl

private theorem tenCoordAux_three_nodes {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {Bs X J Y : Subgroup G} (hBs : IsElemAbelian p Bs) {N : ℕ} (hN5 : 5 ≤ N)
    (hXd : GGResXDatumA p Bs X (N - 1)) (hXs : GGResTwoNodeSideDatum p Bs X J)
    (hYd : GGResLeviSideDatumLE3 p Bs Y J) (hY2 : ¬ GGResTwoNodeSideDatum p Bs Y J) :
    ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
      (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
      (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V),
      Fintype.card Λ = N ∧ GGIsWeylMatrix M ∧ GGIntCartan M C ∧
        (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧
        (∀ i, GGIsReflection p (φ i)) ∧
        (∀ i j, α i (h j) = (C i j : ZMod p)) ∧
        (∃ f : M.Group ≃* ↥(ggAutomizer Y Bs), ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i) ∧
        ggAutomizer Y Bs = Subgroup.closure (Set.range φ) ∧
        ggAutomizer J Bs ≤ ggAutomizer Y Bs ∧
        ggAutomizer J Bs ≤ ggAutomizer X Bs ∧
        (∃ a ∈ ggAutomizer J Bs, ∃ b ∈ ggAutomizer J Bs, a * b ≠ b * a) := by
  classical
  obtain ⟨Λ₀, i1₀, i2₀, M₀, C₀, V₀, i3₀, i4₀, ι₀, φ₀, h₀, α₀, e₀, hM₀, hW₀, hC₀,
    hlin₀, hrefl₀, hpair₀, hf₀ex, hclos₀⟩ := hXd
  letI := i1₀
  letI := i2₀
  letI := i3₀
  letI := i4₀
  obtain ⟨f₀, hf₀⟩ := hf₀ex
  obtain ⟨Λ, i1, i2, b₁, b₂, M, C, MJ, V, i3, i4, ι, φ, h, α, hb, hWM, hC, hWMJ, hMJ,
    hlin, hrefl, hpair, hfex, hclos, hfJex, hclosJ, hconj⟩ := hXs
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  obtain ⟨f, hf⟩ := hfex
  obtain ⟨fJ, hfJ⟩ := hfJex
  obtain ⟨e, hM⟩ :=
    ggTW_typeA_of_datum (p := p) (n := N - 1) hp2 (by omega) hBs (ggAutomizer X Bs)
      e₀ hM₀ hW₀ f₀ φ₀ hf₀ hrefl₀ hWM f φ hf hrefl
  obtain ⟨eJ, hMJ'⟩ := ggTW_twoNode_J_typeA hN5 e hM hb hWMJ hMJ
  obtain ⟨ΛY, i1Y, i2Y, S, MY, CY, MJY, VY, i3Y, i4Y, ιY, φY, hYc, αY, hS1, hS2, hWMY,
    hCY, hWMJY, hMJY, hlinY, hreflY, hpairY, hfYex, hclosY, hfJYex, hclosJY, hconjY⟩ := hYd
  letI := i1Y
  letI := i2Y
  letI := i3Y
  letI := i4Y
  obtain ⟨fY, hfY⟩ := hfYex
  obtain ⟨fJY, hfJY⟩ := hfJYex
  have hS3 : S.card = 3 := by
    rcases (by omega : S.card = 2 ∨ S.card = 3) with h2 | h3
    · exact absurd (ggResTwoNodeSideDatum_of_leviLE3_card_two (p := p) h2 ιY φY hYc αY hWMY hCY
        hWMJY hMJY hlinY hreflY hpairY ⟨fY, hfY⟩ hclosY ⟨fJY, hfJY⟩ hclosJY hconjY) hY2
    · exact h3
  obtain ⟨eY, hMJY'⟩ :=
    ggTW_typeA_of_datum (p := p) (n := N - 3) hp2 (by omega) hBs (ggAutomizer J Bs)
      eJ hMJ' hWMJ fJ (fun j => φ j) hfJ (fun j => hrefl j) hWMJY fJY
      (fun j => φY j) hfJY (fun j => hreflY j)
  have hcardJ : Fintype.card {j : ΛY // j ∉ S} = N - 3 := by
    have h := (Fintype.card_congr eY).symm
    simpa using h
  have hcardS : Fintype.card {j : ΛY // j ∈ S} = S.card := by
    simpa using Fintype.card_coe S
  have hcard : Fintype.card ΛY = N := by
    have h := Fintype.card_subtype_compl (fun j : ΛY => j ∈ S)
    rw [hcardJ, hcardS, hS3] at h
    omega
  have hleY : ggAutomizer J Bs ≤ ggAutomizer Y Bs := by
    rw [hclosJY, hclosY]
    exact Subgroup.closure_mono (by
      rintro _ ⟨j, rfl⟩
      exact ⟨(j : ΛY), rfl⟩)
  have hleX : ggAutomizer J Bs ≤ ggAutomizer X Bs := by
    rw [hclosJ, hclos]
    exact Subgroup.closure_mono (by
      rintro _ ⟨j, rfl⟩
      exact ⟨(j : Λ), rfl⟩)
  have hnonab : ∃ a ∈ ggAutomizer J Bs, ∃ b ∈ ggAutomizer J Bs, a * b ≠ b * a := by
    let i0 : Fin (N - 3) := ⟨0, by omega⟩
    let i1 : Fin (N - 3) := ⟨1, by omega⟩
    have hM3 : MJY.M (eY i0) (eY i1) = 3 := by
      rw [hMJY', CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      rw [tenCoordAux_coxeterA_entry]
      simp [i0, i1]
    have horder : orderOf (MJY.simple (eY i0) * MJY.simple (eY i1)) = 3 := by
      have h1 : orderOf (MJY.simple (eY i0) * MJY.simple (eY i1)) =
          MJY.M (eY i0) (eY i1) := by
        rw [← CoxeterMatrix.toCoxeterSystem_simple]
        exact CoxeterSystem.orderOf_simple_mul_simple MJY.toCoxeterSystem (eY i0) (eY i1)
      rw [h1, hM3]
    have hx2 : MJY.simple (eY i0) * MJY.simple (eY i0) = 1 := by
      rw [← CoxeterMatrix.toCoxeterSystem_simple]
      exact CoxeterSystem.simple_mul_simple_self MJY.toCoxeterSystem (eY i0)
    have hy2 : MJY.simple (eY i1) * MJY.simple (eY i1) = 1 := by
      rw [← CoxeterMatrix.toCoxeterSystem_simple]
      exact CoxeterSystem.simple_mul_simple_self MJY.toCoxeterSystem (eY i1)
    have hne : MJY.simple (eY i0) * MJY.simple (eY i1) ≠
        MJY.simple (eY i1) * MJY.simple (eY i0) := by
      intro hcomm
      have hsq : (MJY.simple (eY i0) * MJY.simple (eY i1)) ^ 2 = 1 := by
        calc (MJY.simple (eY i0) * MJY.simple (eY i1)) ^ 2
            = (MJY.simple (eY i0) * MJY.simple (eY i1)) *
                (MJY.simple (eY i0) * MJY.simple (eY i1)) := pow_two _
          _ = MJY.simple (eY i0) * (MJY.simple (eY i1) * MJY.simple (eY i0)) *
                MJY.simple (eY i1) := by group
          _ = MJY.simple (eY i0) * (MJY.simple (eY i0) * MJY.simple (eY i1)) *
                MJY.simple (eY i1) := by rw [hcomm]
          _ = (MJY.simple (eY i0) * MJY.simple (eY i0)) *
                (MJY.simple (eY i1) * MJY.simple (eY i1)) := by group
          _ = 1 := by rw [hx2, hy2, one_mul]
      have hdvd : orderOf (MJY.simple (eY i0) * MJY.simple (eY i1)) ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr hsq
      rw [horder] at hdvd
      exact absurd hdvd (by norm_num : ¬ (3 ∣ 2))
    refine ⟨(fJY (MJY.simple (eY i0)) : MulAut ↥Bs), (fJY (MJY.simple (eY i0))).2,
      (fJY (MJY.simple (eY i1)) : MulAut ↥Bs), (fJY (MJY.simple (eY i1))).2, ?_⟩
    intro heq
    have heq' : fJY (MJY.simple (eY i0)) * fJY (MJY.simple (eY i1)) =
        fJY (MJY.simple (eY i1)) * fJY (MJY.simple (eY i0)) := Subtype.ext heq
    have hxy : MJY.simple (eY i0) * MJY.simple (eY i1) =
        MJY.simple (eY i1) * MJY.simple (eY i0) := by
      apply fJY.injective
      simpa [map_mul] using heq'
    exact hne hxy
  exact ⟨ΛY, i1Y, i2Y, MY, CY, VY, i3Y, i4Y, ιY, φY, hYc, αY, hcard, hWMY, hCY, hlinY,
    hreflY, hpairY, ⟨fY, hfY⟩, hclosY, hleY, hleX, hnonab⟩

@[expose] def GGTenCoord {G : Type} [Group G] [Finite G] (Bs L K : Subgroup G) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (_ : Finite V)
    (ι : Additive ↥Bs ≃+ V) (ΛL : Type) (_ : Fintype ΛL) (_ : DecidableEq ΛL)
    (ML : CoxeterMatrix ΛL) (CL : Matrix ΛL ΛL ℤ) (φL : ΛL → MulAut ↥Bs) (hL : ΛL → V)
    (aL : ΛL → Module.Dual (ZMod 3) V) (φK : Fin 8 → MulAut ↥Bs) (hK : Fin 8 → V)
    (aK : Fin 8 → Module.Dual (ZMod 3) V),
    Module.finrank (ZMod 3) V = 10 ∧ Fintype.card ΛL = 9 ∧ GGIsWeylMatrix ML ∧ GGIntCartan ML CL ∧
      (∀ i w, ggLin (p := 3) ι (φL i) w = w - aL i w • hL i) ∧ (∀ i, GGIsReflection 3 (φL i)) ∧
      (∀ i j, aL i (hL j) = (CL i j : ZMod 3)) ∧
      (∃ fL : ML.Group ≃* ↥(ggAutomizer L Bs), ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φL i) ∧
      ggAutomizer L Bs = Subgroup.closure (Set.range φL) ∧
      (∀ i w, ggLin (p := 3) ι (φK i) w = w - aK i w • hK i) ∧ (∀ i, GGIsReflection 3 (φK i)) ∧
      (∀ i j, aK i (hK j) = (CartanMatrix.A 8 i j : ZMod 3)) ∧
      ggAutomizer K Bs = Subgroup.closure (Set.range φK) ∧
      (∃ a ∈ ggAutomizer L Bs ⊓ ggAutomizer K Bs, ∃ b ∈ ggAutomizer L Bs ⊓ ggAutomizer K Bs,
        a * b ≠ b * a)

theorem ggTen_coord (hD : GGTwoNodeIndepDatum) (hJ2 : GGTBJTwoNodeInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p = 3) {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hrow : GGResRowAt ggRowTwoNodeNine p J K) (hyK : y ∈ K) (hcard : Nat.card ↥Bs = 3 ^ 10)
    (hLY : GGResLeviSideDatumLE3 p Bs L J) (hLn : ¬ GGResTwoNodeSideDatum p Bs L J) :
    GGTenCoord Bs L K := by
  classical
  subst hp3
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, hrNN, -, hrank8⟩ := hrow
  have hBs : IsElemAbelian 3 Bs := hH.1.tableB_facts.2.1
  have htag : labX.tag = .A ∨ labX.tag = .twA := tenCoordAux_nine_tag hrNN hrank8
  have hXdK : GGResXDatumA 3 Bs K 8 := by
    have h := tenCoordAux_xdatumA hD hH K y (Or.inr ⟨rfl, rfl⟩) hyK hJΛ hXΛ hJlab hXlab hrNN htag
    simpa [hrank8] using h
  have hrow2 : GGResRowAt ggRowTwoNode 3 J K :=
    ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, hrNN⟩
  have hXs : GGResTwoNodeSideDatum 3 Bs K J :=
    (hJ2 G 3 B Bs x L D J y K hH).2 (tenCoordAux_xdatum_of_A hXdK) hrow2
  obtain ⟨ΛL, iFL, iDL, ML, CL, VL, iAL, iML, ιL, φL, hL, aL, hcardL, hWM, hC, hlinL,
    hreflL, hpairL, hfLex, hclosL, hleL, hleK, hnonab⟩ :=
    tenCoordAux_three_nodes (p := 3) (by norm_num) (X := K) (Y := L) (J := J) hBs
      (N := 9) (by norm_num) hXdK hXs hLY hLn
  obtain ⟨fL, hfL⟩ := hfLex
  obtain ⟨Λ₀, iF0, iD0, M0, C0, V0, iA0, iM0, ι0, φ0, h0, α0, e0, hM0, hW0, hC0, hlin0,
    hrefl0, hpair0, hf0ex, hclos0⟩ := hXdK
  letI := iF0
  letI := iD0
  letI := iA0
  letI := iM0
  obtain ⟨f0, hf0⟩ := hf0ex
  haveI : Finite VL :=
    Finite.of_injective (fun v : VL => (ιL.symm v : Additive ↥Bs))
      (fun a b h => ιL.symm.injective h)
  have hfin : Module.finrank (ZMod 3) VL = 10 := by
    have h1 : Nat.card ↥Bs = 3 ^ Module.finrank (ZMod 3) VL := by
      calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := Nat.card_congr Additive.ofMul
        _ = Nat.card VL := Nat.card_congr ιL.toEquiv
        _ = 3 ^ Module.finrank (ZMod 3) VL := (FiniteField.pow_finrank_eq_natCard 3 VL).symm
    have h2 : 3 ^ Module.finrank (ZMod 3) VL = 3 ^ 10 := by rw [← h1, hcard]
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h2
  let T : V0 ≃+ VL := ι0.symm.trans ιL
  let eLin : V0 ≃ₗ[ZMod 3] VL :=
    LinearEquiv.ofBijective (T.toAddMonoidHom.toZModLinearMap 3) T.bijective
  let φK : Fin 8 → MulAut ↥Bs := fun i => φ0 (e0 i)
  let hK : Fin 8 → VL := fun i => eLin (h0 (e0 i))
  let aK : Fin 8 → Module.Dual (ZMod 3) VL := fun i => (α0 (e0 i)).comp eLin.symm.toLinearMap
  have hlinK : ∀ i w, ggLin (p := 3) ιL (φK i) w = w - aK i w • hK i := by
    intro i w
    have htrans := ggLin_transport (p := 3) ι0 ιL (φ0 (e0 i)) (eLin.symm w)
    rw [hlin0] at htrans
    have h1 : ιL (ι0.symm (eLin.symm w)) = w := by
      change T (eLin.symm w) = w
      rw [show T (eLin.symm w) = eLin (eLin.symm w) from rfl, LinearEquiv.apply_symm_apply]
    have h2 : ιL (ι0.symm (eLin.symm w - α0 (e0 i) (eLin.symm w) • h0 (e0 i))) =
        w - aK i w • hK i := by
      change T (eLin.symm w - α0 (e0 i) (eLin.symm w) • h0 (e0 i)) = w - aK i w • hK i
      rw [show T (eLin.symm w - α0 (e0 i) (eLin.symm w) • h0 (e0 i)) =
          eLin (eLin.symm w - α0 (e0 i) (eLin.symm w) • h0 (e0 i)) from rfl]
      simp only [map_sub, map_smul, LinearEquiv.apply_symm_apply, aK, hK, LinearMap.comp_apply]
      rfl
    rw [h1] at htrans
    rw [← htrans, h2]
  have hreflK : ∀ i, GGIsReflection 3 (φK i) := fun i => hrefl0 (e0 i)
  have hpairK : ∀ i j, aK i (hK j) = (CartanMatrix.A 8 i j : ZMod 3) := by
    intro i j
    have h1 : eLin.symm (hK j) = h0 (e0 j) := by
      change eLin.symm (eLin (h0 (e0 j))) = h0 (e0 j)
      rw [LinearEquiv.symm_apply_apply]
    have h2 : aK i (hK j) = (C0 (e0 i) (e0 j) : ZMod 3) := by
      change (α0 (e0 i)) (eLin.symm (hK j)) = (C0 (e0 i) (e0 j) : ZMod 3)
      rw [h1]
      exact hpair0 (e0 i) (e0 j)
    rw [h2]
    have h3 := ggIndep_cartan_of_reindex e0 hC0 hM0 i j
    rw [h3]
  have hclosK : ggAutomizer K Bs = Subgroup.closure (Set.range φK) := by
    rw [hclos0]
    congr 1
    exact (e0.surjective.range_comp φ0).symm
  refine ⟨VL, iAL, iML, inferInstance, ιL, ΛL, iFL, iDL, ML, CL, φL, hL, aL, φK, hK, aK,
    hfin, hcardL, hWM, hC, hlinL, hreflL, hpairL, ⟨fL, hfL⟩, hclosL, hlinK, hreflK, hpairK,
    hclosK, ?_⟩
  obtain ⟨a, ha, b, hb, hnab⟩ := hnonab
  exact ⟨a, Subgroup.mem_inf.mpr ⟨hleL ha, hleK ha⟩, b,
    Subgroup.mem_inf.mpr ⟨hleL hb, hleK hb⟩, hnab⟩

end CFSG.StandardType

end
