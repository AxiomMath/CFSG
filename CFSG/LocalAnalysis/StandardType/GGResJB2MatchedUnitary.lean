module

public import CFSG.LocalAnalysis.StandardType.GGResJA2UnitaryRecognition
public import CFSG.LocalAnalysis.StandardType.GGResJUnitaryCubicBlock
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeThree
public import CFSG.RankThree.CentralExtension.ThreeCoverCubeLifting
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TRank
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.CentralExtension
open scoped commutatorElement

theorem B2_coroot_span_of_lineJDatum
    {G : Type} [Group G] [Finite G]
    {B Bs L D J Kc : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y Kc)
    (hD : GGResLineJDatum 3 Bs J .B2) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V)
      (ι : Additive ↥Bs ≃+ V) (r : Fin 2 → MulAut ↥Bs) (hvec : Fin 2 → V)
      (α : Fin 2 → Module.Dual (ZMod 3) V) (E : Subgroup G) (eG : Fin 2 → G),
      (∀ j w, ggLin (p := 3) ι (r j) w = w -
        α j w • hvec j) ∧
      (∀ j, α j (hvec j) = 2) ∧
      LinearIndependent (ZMod 3) hvec ∧
      E = ggSpanSub ι (Submodule.span (ZMod 3) (Set.range hvec)) ∧
      E = Subgroup.closure (Set.range eG) ∧
      E ≤ Bs ⊓ J ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      E ⊓ Subgroup.centralizer (J : Set G) = ⊥ ∧
      (∀ i, eG i ∈ Bs ⊓ J) ∧
      (∀ hb1 : eG 1 ∈ Bs, r 1 ⟨eG 1, hb1⟩ = ⟨eG 1, hb1⟩⁻¹) ∧
      (∀ (hb0 : eG 0 ∈ Bs) (hb1 : eG 1 ∈ Bs),
        r 1 ⟨eG 0, hb0⟩ = ⟨eG 1, hb1⟩ * ⟨eG 0, hb0⟩) ∧
      (∀ hb0 : eG 0 ∈ Bs, r 0 ⟨eG 0, hb0⟩ = ⟨eG 0, hb0⟩⁻¹) ∧
      (∀ (hb1 : eG 1 ∈ Bs) (hb0 : eG 0 ∈ Bs),
        r 0 ⟨eG 1, hb1⟩ = ⟨eG 0, hb0⟩⁻¹ * ⟨eG 1, hb1⟩) ∧
      ggAutomizer J Bs = Subgroup.closure (Set.range r) := by
  classical
  obtain ⟨V, instA, instM, ι, r, hvec, α, hform, _hrefl, hpair, hind, hgen⟩ := hD
  letI : AddCommGroup V := instA
  letI : Module (ZMod 3) V := instM
  have hN : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  have hdet : (CartanMatrix.B 2).det = 2 := by
    simpa using CartanMatrix.B_det (by norm_num : 0 < 2)
  have hC : ∀ c : Fin 2 → ZMod 3,
      (∀ j, ∑ l, (CartanMatrix.B 2 j l : ZMod 3) * c l = 0) → c = 0 :=
    ker_zero_of_det_two hdet
  have hα2 : ∀ j : Fin 2, α j (hvec j) = 2 := by
    intro j
    rw [hpair j j]
    fin_cases j <;> rfl
  let W : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range hvec)
  let E : Subgroup G := ggSpanSub ι W
  have hEprops := GGResLineJDatum.coroot_span_subgroup_properties_of_cartan
    (G := G) (Bs := Bs) (J := J) (k := 2) (V := V) hN ι r hvec α
    (CartanMatrix.B 2) hform hα2 hpair hind hC hgen W rfl
  let eG : Fin 2 → G := fun i => (Additive.toMul (ι.symm (hvec i)) : ↥Bs)
  have heE : ∀ i, eG i ∈ E := by
    intro i
    rw [show E = ggSpanSub ι W from rfl]
    exact mem_ggSpanSub.mpr ⟨hvec i, Submodule.subset_span (Set.mem_range_self i), by
      simp [eG]⟩
  have hEgen : E = Subgroup.closure (Set.range eG) := by
    dsimp [E, W, eG]
    exact corootSpan_eq_closure (Bs := Bs) ι hvec
  have hα2' : ∀ j : Fin 2, α j (hvec j) = 2 := hα2
  have hform' : ∀ j w, ggLin (p := 3) ι (r j) w =
      w - α j w • hvec j := hform
  let j0 : Fin GGResLineJType.B2.rank := ⟨0, by decide⟩
  let j1 : Fin GGResLineJType.B2.rank := ⟨1, by decide⟩
  have hr1e1 : ∀ hb1 : eG 1 ∈ Bs,
      r j1 ⟨eG 1, hb1⟩ = ⟨eG 1, hb1⟩⁻¹ := by
    intro hb1
    rw [ggLin_inv_iff (p := 3) (ι := ι) (φ := r j1) (b := ⟨eG 1, hb1⟩)]
    rw [show ι (Additive.ofMul ⟨eG 1, hb1⟩) = hvec j1 by
      rw [show (⟨eG 1, hb1⟩ : ↥Bs) = Additive.toMul (ι.symm (hvec j1)) by
        apply Subtype.ext
        simp [eG]; rfl]
      simp]
    rw [hform j1, hα2 j1]
    module
  have hr1e0 : ∀ (hb0 : eG 0 ∈ Bs) (hb1 : eG 1 ∈ Bs),
      r j1 ⟨eG 0, hb0⟩ = ⟨eG 1, hb1⟩ * ⟨eG 0, hb0⟩ := by
    intro hb0 hb1
    apply Additive.ofMul.injective
    apply ι.injective
    rw [← ggLin_apply_ofMul (p := 3) (ι := ι) (φ := r j1) (b := ⟨eG 0, hb0⟩)]
    rw [show ι (Additive.ofMul ⟨eG 0, hb0⟩) = hvec j0 by
      rw [show (⟨eG 0, hb0⟩ : ↥Bs) = Additive.toMul (ι.symm (hvec j0)) by
        apply Subtype.ext
        simp [eG]; rfl]
      simp]
    rw [hform j1, hpair j1 j0]
    have hC : (GGResLineJType.B2.cartan j1 j0 : ZMod 3) = -1 := rfl
    rw [hC]
    change hvec j0 - -(1 : ZMod 3) • hvec j1 =
      ι (Additive.ofMul ⟨eG 1, hb1⟩ + Additive.ofMul ⟨eG 0, hb0⟩)
    rw [map_add]
    rw [show ι (Additive.ofMul ⟨eG 1, hb1⟩) = hvec j1 by
      rw [show (⟨eG 1, hb1⟩ : ↥Bs) = Additive.toMul (ι.symm (hvec j1)) by
        apply Subtype.ext
        simp [eG]; rfl]
      simp]
    rw [show ι (Additive.ofMul ⟨eG 0, hb0⟩) = hvec j0 by
      rw [show (⟨eG 0, hb0⟩ : ↥Bs) = Additive.toMul (ι.symm (hvec j0)) by
        apply Subtype.ext
        simp [eG]; rfl]
      simp]
    module
  have hr0e0 : ∀ hb0 : eG 0 ∈ Bs,
      r j0 ⟨eG 0, hb0⟩ = ⟨eG 0, hb0⟩⁻¹ := by
    intro hb0
    rw [ggLin_inv_iff (p := 3) (ι := ι) (φ := r j0) (b := ⟨eG 0, hb0⟩)]
    rw [show ι (Additive.ofMul ⟨eG 0, hb0⟩) = hvec j0 by
      rw [show (⟨eG 0, hb0⟩ : ↥Bs) = Additive.toMul (ι.symm (hvec j0)) by
        apply Subtype.ext
        simp [eG]; rfl]
      simp]
    rw [hform j0, hα2 j0]
    module
  have hr0e1 : ∀ (hb1 : eG 1 ∈ Bs) (hb0 : eG 0 ∈ Bs),
      r j0 ⟨eG 1, hb1⟩ = ⟨eG 0, hb0⟩⁻¹ * ⟨eG 1, hb1⟩ := by
    intro hb1 hb0
    apply Additive.ofMul.injective
    apply ι.injective
    rw [← ggLin_apply_ofMul (p := 3) (ι := ι) (φ := r j0) (b := ⟨eG 1, hb1⟩)]
    rw [show ι (Additive.ofMul ⟨eG 1, hb1⟩) = hvec j1 by
      rw [show (⟨eG 1, hb1⟩ : ↥Bs) = Additive.toMul (ι.symm (hvec j1)) by
        apply Subtype.ext
        simp [eG]; rfl]
      simp]
    rw [hform j0, hpair j0 j1]
    have hC : (GGResLineJType.B2.cartan j0 j1 : ZMod 3) = 1 := by
      show (CartanMatrix.B 2 0 1 : ZMod 3) = 1
      decide
    rw [hC]
    change hvec j1 - (1 : ZMod 3) • hvec j0 =
      ι (Additive.ofMul ((⟨eG 0, hb0⟩ : ↥Bs)⁻¹ * ⟨eG 1, hb1⟩))
    change hvec j1 - (1 : ZMod 3) • hvec j0 =
      ι (Additive.ofMul ((⟨eG 0, hb0⟩ : ↥Bs)⁻¹) + Additive.ofMul ⟨eG 1, hb1⟩)
    rw [map_add]
    rw [show ι (Additive.ofMul ((⟨eG 0, hb0⟩ : ↥Bs)⁻¹)) = -hvec j0 by
      rw [show (Additive.ofMul ((⟨eG 0, hb0⟩ : ↥Bs)⁻¹)) =
          Additive.ofMul (Additive.toMul (ι.symm (-hvec j0))) by
        congr 1
        apply Subtype.ext
        simp [eG]; rfl]
      simp]
    rw [show ι (Additive.ofMul ⟨eG 1, hb1⟩) = hvec j1 by
      rw [show (⟨eG 1, hb1⟩ : ↥Bs) = Additive.toMul (ι.symm (hvec j1)) by
        apply Subtype.ext
        simp [eG]; rfl]
      simp]
    module
  exact ⟨V, instA, instM, ι, r, hvec, α, E, eG, hform', hα2, hind, rfl, hEgen,
    hEprops.1, hEprops.2.1, by simpa using hEprops.2.2.1,
    hEprops.2.2.2, fun i => ⟨(hEprops.1 (heE i)).1, (hEprops.1 (heE i)).2⟩,
    hr1e1, hr1e0, hr0e0, hr0e1, hgen⟩






private theorem closure_map_eq_of_generators
    {X : Type} [Group X] [Finite X] {E : Subgroup X} {a b : X} {r s : MulAut X}
    (hE : E = Subgroup.closure ({a, b} : Set X))
    (ha : a ∈ E) (hb : b ∈ E)
    (hr_a : r a = a⁻¹) (hr_b : r b = a⁻¹ * b)
    (hs_a : s a = b * a) (hs_b : s b = b⁻¹) :
    ∀ φ ∈ Subgroup.closure ({r, s} : Set (MulAut X)), E.map φ.toMonoidHom = E := by
  classical
  haveI : Finite ↥E := Subtype.finite
  have hr_le : E.map r.toMonoidHom ≤ E := by
    rw [hE, MonoidHom.map_closure]
    apply (Subgroup.closure_le (Subgroup.closure ({a, b} : Set X))).2
    rintro _ ⟨x, hx, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · subst x
      simpa [hr_a] using (Subgroup.closure ({a, b} : Set X)).inv_mem
        (Subgroup.subset_closure (by simp : a ∈ ({a, b} : Set X)))
    · subst x
      simpa [hr_b] using (Subgroup.closure ({a, b} : Set X)).mul_mem
        ((Subgroup.closure ({a, b} : Set X)).inv_mem
          (Subgroup.subset_closure (by simp : a ∈ ({a, b} : Set X))))
        (Subgroup.subset_closure (by simp : b ∈ ({a, b} : Set X)))
  have hs_le : E.map s.toMonoidHom ≤ E := by
    rw [hE, MonoidHom.map_closure]
    apply (Subgroup.closure_le (Subgroup.closure ({a, b} : Set X))).2
    rintro _ ⟨x, hx, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · subst x
      simpa [hs_a] using (Subgroup.closure ({a, b} : Set X)).mul_mem
        (Subgroup.subset_closure (by simp : b ∈ ({a, b} : Set X)))
        (Subgroup.subset_closure (by simp : a ∈ ({a, b} : Set X)))
    · subst x
      simpa [hs_b] using (Subgroup.closure ({a, b} : Set X)).inv_mem
        (Subgroup.subset_closure (by simp : b ∈ ({a, b} : Set X)))
  have hr_eq : E.map r.toMonoidHom = E := by
    apply Subgroup.eq_of_le_of_card_ge hr_le
    rw [Subgroup.card_map_of_injective (MulEquiv.injective r)]
  have hs_eq : E.map s.toMonoidHom = E := by
    apply Subgroup.eq_of_le_of_card_ge hs_le
    rw [Subgroup.card_map_of_injective (MulEquiv.injective s)]
  intro φ hφ
  refine Subgroup.closure_induction (p := fun φ _ => E.map φ.toMonoidHom = E) ?_ ?_ ?_ ?_ hφ
  · intro x hx
    rcases hx with rfl | rfl
    · exact hr_eq
    · exact hs_eq
  · change E.map (MonoidHom.id X) = E
    exact Subgroup.map_id E
  · intro p q _ _ hp hq
    rw [show (p * q).toMonoidHom = p.toMonoidHom.comp q.toMonoidHom from rfl]
    rw [← Subgroup.map_map, hq, hp]
  · intro p _ hp
    have h1 : p⁻¹ * p = 1 := inv_mul_cancel p
    have h := congrArg (fun q : MulAut X => E.map q.toMonoidHom) h1
    rw [show (p⁻¹ * p).toMonoidHom = p⁻¹.toMonoidHom.comp p.toMonoidHom from rfl] at h
    rw [← Subgroup.map_map] at h
    rw [hp] at h
    simpa only [show (1 : MulAut X).toMonoidHom = MonoidHom.id X from rfl,
      Subgroup.map_id] using h


private theorem B2_rank2_preimage_commutative
    {G : Type} [Group G] [Finite G]
    {B Bs L D J Kc : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y Kc)
    (hD : GGResLineJDatum 3 Bs J .B2)
    {F : Type} [Field F] [Finite F] {n : ℕ}
    (hU : UnitaryFieldData 2 n F)
    (hFcard : Nat.card F = (2 ^ n) ^ 2) (hn2 : 2 ≤ n) (hpq : 3 ∣ 2 ^ n + 1)
    (θ : ↥J ⧸ Subgroup.center ↥J ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin 3) F (2 ^ n)))
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (Aact : ↥Bs → GL (Fin 3) F)
    (hAGU : ∀ b, Aact b ∈ LargeEvenGUSet (Fin 3) F (2 ^ n))
    (hAproj : ∀ b, TableB.projConj (LargeEvenSUGroup (Fin 3) F (2 ^ n))
      ⟨Aact b, TableBUE.gu_subset_normalizer hU (hAGU b)⟩ = ggBeta J θ hN b)
    (hperfJ : commutator ↥J = ⊤) :
    ∃ Ebar : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin 3) F (2 ^ n))),
      Nat.card Ebar = 9 ∧ IsElemAbelian 3 Ebar ∧
      (∀ x y : LargeEvenSUGroup (Fin 3) F (2 ^ n),
        x ∈ Ebar.comap (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) F (2 ^ n))) →
        y ∈ Ebar.comap (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) F (2 ^ n))) →
        x * y = y * x) ∧
      (∀ x (hx : x ∈ Ebar),
        cubeClass (π := LargeEvenProjMk (LargeEvenSUGroup (Fin 3) F (2 ^ n)))
          (hπ := QuotientGroup.mk'_surjective _)
          (hZ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.ker_projMk_uni_le_center
            (LargeEvenSUGroup (Fin 3) F (2 ^ n))) x = 1) ∧
      (∀ z ∈ (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) F (2 ^ n))).ker, z ^ 3 = 1) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let L : Subgroup (GL (Fin 3) F) := LargeEvenSUGroup (Fin 3) F (2 ^ n)
  let R : Type := LargeEvenProj L
  let ψ : ↥J →* R := ggQuotHom θ
  obtain ⟨V, instA, instM, ι, r, hvec, α, E, eG, hform, hα2, hind,
    hEspan, hEgen, hEsub, hEelem, hEcard, hEbot, hmem,
    hr1e1, hr1e0, hr0e0, hr0e1, hgen⟩ := B2_coroot_span_of_lineJDatum hH hD
  have hEsubBs : E ≤ Bs := fun x hx => (hEsub hx).1
  have hEsubJ : E ≤ J := fun x hx => (hEsub hx).2
  haveI : Finite ↥Bs := Subtype.finite
  let A : Subgroup (MulAut ↥J) := (ggGamma J hN).range
  let I : Set (MulAut R) :=
    LargeEvenMatConjImage (LargeEvenProjMk L) (LargeEvenGUSet (Fin 3) F (2 ^ n))
  have hψs : Function.Surjective ψ := ggQuotHom_surjective θ
  have hkerψ : ψ.ker ≤ Subgroup.center ↥J := by
    rw [show ψ.ker = (ggQuotHom θ).ker from rfl, ker_ggQuotHom θ]
  have hBsElem : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hAe : IsElemAbelian 3 A := by
    dsimp [A]
    exact isElemAbelian_range
      (fun a b : ↥Bs => hBsElem.1.is_comm.comm a b)
      (fun b : ↥Bs => Subtype.ext (by simpa using hBsElem.2 b b.2))
      (ggGamma J hN)
  have hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : ↥J, φ (ψ l) = ψ (a l) := by
    rintro a ⟨b, rfl⟩
    let hANb : Aact b ∈ Subgroup.normalizer (L : Set (GL (Fin 3) F)) :=
      TableBUE.gu_subset_normalizer hU (hAGU b)
    refine ⟨TableB.projConj L ⟨Aact b, hANb⟩, ?_, ?_⟩
    · exact ggUSixSh_projConj_mem_matConjImage (H := L) (S := LargeEvenGUSet (Fin 3) F (2 ^ n))
        (hA := hAGU b) (hAN := hANb)
    · intro l
      calc
        TableB.projConj L ⟨Aact b, hANb⟩ (ψ l) = ggBeta J θ hN b (ψ l) := by
          rw [hAproj b]
        _ = ψ (((ggGamma J hN) b) l) :=
          ggBeta_ggQuotHom J hN θ b l
        _ = ψ (((ggGamma J hN) b) l) := rfl
  have hgamma : ggGamma J hN = ggGamma J (GGResHyp.Bs_le_normalizer_J hH) := by
    ext b
    rfl
  have h9 : 9 ≤ Nat.card A := by
    dsimp [A]
    rw [hgamma]
    simpa using GGResHyp.sq_le_card_gamma_J (p := 3) hH
  have h2n : 2 < 2 ^ n := by
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  have hlt : Nat.card A < 27 := by
    have h := TableBUE.card_lt_unitary_three (h := hU) (p := 3) (n := n)
      hFcard h2n (by norm_num) hpq (L' := ↥J) (ψ := ψ)
      hψs hkerψ hperfJ hAe hAI
    simpa using h
  have hApg : IsPGroup 3 A := hAe.isPGroup
  obtain ⟨k, hk⟩ := hApg.exists_card_eq
  rw [hk] at h9 hlt
  have hk2 : k = 2 := by
    have hk2le : 2 ≤ k := by
      by_contra h
      have hk1 : k ≤ 1 := by omega
      have hle : 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      norm_num at h9 hle
      omega
    have hk2ge : k ≤ 2 := by
      by_contra h
      have hk3 : 3 ≤ k := by omega
      have hge : 27 ≤ 3 ^ k := by
        calc 27 = 3 ^ 3 := by norm_num
          _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
      omega
    omega
  have hAcard : Nat.card A = 9 := by
    rw [hk, hk2]
    norm_num
  have he0E : eG 0 ∈ E := by
    rw [hEgen]
    exact Subgroup.subset_closure ⟨0, rfl⟩
  have he1E : eG 1 ∈ E := by
    rw [hEgen]
    exact Subgroup.subset_closure ⟨1, rfl⟩
  let eB : Fin 2 → ↥Bs := fun i => ⟨eG i, (hmem i).1⟩
  let EB : Subgroup ↥Bs := E.subgroupOf Bs
  have he0B : eB 0 ∈ EB := Subgroup.mem_subgroupOf.mpr (by simpa [eB] using he0E)
  have he1B : eB 1 ∈ EB := Subgroup.mem_subgroupOf.mpr (by simpa [eB] using he1E)
  have hEBgen : EB = Subgroup.closure ({eB 0, eB 1} : Set ↥Bs) := by
    apply Subgroup.map_injective (Subgroup.subtype_injective Bs)
    rw [Subgroup.map_subgroupOf_eq_of_le hEsubBs, hEgen, MonoidHom.map_closure]
    congr 1
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact ⟨eB 0, by simp, rfl⟩
      · exact ⟨eB 1, by simp, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      rcases hw with hw | hw
      · subst w
        exact ⟨0, rfl⟩
      · subst w
        exact ⟨1, rfl⟩
  have hgen' : ggAutomizer J Bs =
      Subgroup.closure ({r 0, r 1} : Set (MulAut ↥Bs)) := by
    rw [hgen]
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hmap_phi : ∀ φ ∈ ggAutomizer J Bs, EB.map φ.toMonoidHom = EB := by
    intro φ hφ
    rw [hgen'] at hφ
    refine (closure_map_eq_of_generators (X := ↥Bs) (E := EB) (a := eB 0) (b := eB 1)
      (r := r 0) (s := r 1) hEBgen he0B he1B ?_ ?_ ?_ ?_) φ hφ
    · exact Subtype.ext (congrArg Subtype.val (hr0e0 (hmem 0).1))
    · exact Subtype.ext (congrArg Subtype.val (hr0e1 (hmem 1).1 (hmem 0).1))
    · exact Subtype.ext (congrArg Subtype.val (hr1e0 (hmem 0).1 (hmem 1).1))
    · exact Subtype.ext (congrArg Subtype.val (hr1e1 (hmem 1).1))
  have hφE_inj : Function.Injective (ψ.comp (Subgroup.inclusion hEsubJ)) := by
    intro a b hab
    have h1 : (ψ.comp (Subgroup.inclusion hEsubJ)) (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h1' : ψ (Subgroup.inclusion hEsubJ (a * b⁻¹)) = 1 := h1
    have hker : Subgroup.inclusion hEsubJ (a * b⁻¹) ∈ ψ.ker := MonoidHom.mem_ker.mpr h1'
    rw [show ψ.ker = (ggQuotHom θ).ker from rfl, ker_ggQuotHom θ] at hker
    have hcent : ((a : G) * (b : G)⁻¹) ∈ Subgroup.centralizer (J : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hcomm := Subgroup.mem_center_iff.mp hker ⟨l, hl⟩
      exact congrArg Subtype.val hcomm
    have hmem : (a : G) * (b : G)⁻¹ ∈ E := E.mul_mem a.2 (E.inv_mem b.2)
    have hbot : (a : G) * (b : G)⁻¹ = 1 :=
      Subgroup.mem_bot.mp (by rw [← hEbot]; exact ⟨hmem, hcent⟩)
    apply Subtype.ext
    calc (a : G) = (a : G) * (b : G)⁻¹ * b := by group
      _ = b := by rw [hbot]; simp
  let φE : ↥E →* R := ψ.comp (Subgroup.inclusion hEsubJ)
  let Ebar : Subgroup R := φE.range
  have hEbar_card : Nat.card Ebar = 9 := by
    dsimp [Ebar]
    rw [← Nat.card_congr (MonoidHom.ofInjective hφE_inj).toEquiv]
    exact hEcard
  have hEbar_elem : IsElemAbelian 3 Ebar := by
    dsimp [Ebar]
    exact isElemAbelian_range
      (fun a b : ↥E => hEelem.1.is_comm.comm a b)
      (fun a : ↥E => Subtype.ext (hEelem.2 a a.2)) φE
  let γE : ↥E →* A := (ggGamma J hN).rangeRestrict.comp (Subgroup.inclusion hEsubBs)
  have hγE_inj : Function.Injective γE := by
    intro a b hab
    have h1 : γE (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h1' : ggGamma J hN (Subgroup.inclusion hEsubBs (a * b⁻¹)) = 1 := by
      simpa [γE] using congrArg Subtype.val h1
    have hcent : ((a : G) * (b : G)⁻¹) ∈ Subgroup.centralizer (J : Set G) := by
      exact (ggGamma_eq_one_iff (L := J) (B := Bs) (G := G) hN
        (Subgroup.inclusion hEsubBs (a * b⁻¹))).mp h1'
    have hmem : (a : G) * (b : G)⁻¹ ∈ E := E.mul_mem a.2 (E.inv_mem b.2)
    have hbot : (a : G) * (b : G)⁻¹ = 1 :=
      Subgroup.mem_bot.mp (by rw [← hEbot]; exact ⟨hmem, hcent⟩)
    apply Subtype.ext
    calc (a : G) = (a : G) * (b : G)⁻¹ * b := by group
      _ = b := by rw [hbot]; simp
  have hγE_card : Nat.card γE.range = Nat.card E :=
    (Nat.card_congr (MonoidHom.ofInjective hγE_inj).toEquiv).symm
  have hγE_range : γE.range = ⊤ := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact le_top
    · rw [Subgroup.card_top, hAcard, hγE_card, hEcard]
  have hγE_surj : Function.Surjective γE := by
    intro a
    have : a ∈ γE.range := by rw [hγE_range]; exact Subgroup.mem_top a
    exact this
  let γEe : ↥E ≃* A := MulEquiv.ofBijective γE ⟨hγE_inj, hγE_surj⟩
  let ρ : ↥Bs →* R := φE.comp (γEe.symm.toMonoidHom.comp ((ggGamma J hN).rangeRestrict))
  have hρrange : ρ.range = Ebar := by
    ext z
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨γEe.symm ((ggGamma J hN).rangeRestrict b), rfl⟩
    · rintro ⟨e, rfl⟩
      obtain ⟨b, hb⟩ := MonoidHom.rangeRestrict_surjective (ggGamma J hN) (γEe e)
      refine ⟨b, ?_⟩
      change φE (γEe.symm ((ggGamma J hN).rangeRestrict b)) = φE e
      rw [hb]
      exact congrArg φE (γEe.symm_apply_apply e)
  have hρker : ∀ b : ↥Bs, ρ b = 1 ↔ ggGamma J hN b = 1 := by
    intro b
    constructor
    · intro hb
      have h1 : γEe.symm ((ggGamma J hN).rangeRestrict b) = 1 := by
        apply hφE_inj
        change φE (γEe.symm ((ggGamma J hN).rangeRestrict b)) = φE 1
        rw [show φE (γEe.symm ((ggGamma J hN).rangeRestrict b)) = 1 from hb]
        simp
      have h2 : (ggGamma J hN).rangeRestrict b = 1 := by
        calc
          (ggGamma J hN).rangeRestrict b =
              γE (γEe.symm ((ggGamma J hN).rangeRestrict b)) :=
            (γEe.apply_symm_apply _).symm
          _ = 1 := by simpa [γEe, γE] using congrArg γE h1
      exact congrArg Subtype.val h2
    · intro hb
      have h1 : (ggGamma J hN).rangeRestrict b = 1 := Subtype.ext hb
      change φE (γEe.symm ((ggGamma J hN).rangeRestrict b)) = 1
      rw [h1]
      simp
  have hconj : ∀ φ ∈ ggAutomizer J Bs, ∃ t : R, ∀ b : ↥Bs,
      ρ (φ b) = t * ρ b * t⁻¹ := by
    intro φ hφ
    obtain ⟨n, hnJ, hnN, hnact⟩ := mem_ggAutomizer_iff.mp hφ
    refine ⟨ψ ⟨n, hnJ⟩, ?_⟩
    intro b
    let e : ↥E := γEe.symm ((ggGamma J hN).rangeRestrict b)
    let eφ : ↥E := γEe.symm ((ggGamma J hN).rangeRestrict (φ b))
    let eJ : ↥J := Subgroup.inclusion hEsubJ e
    let q : ↥J := (⟨n, hnJ⟩ : ↥J) * eJ * (⟨n, hnJ⟩ : ↥J)⁻¹
    have hφeB_mem : φ (⟨e.1, hEsubBs e.2⟩ : ↥Bs) ∈ EB := by
      have hmemmap : φ (⟨e.1, hEsubBs e.2⟩ : ↥Bs) ∈ EB.map φ.toMonoidHom :=
        Subgroup.mem_map.mpr ⟨⟨e.1, hEsubBs e.2⟩,
          Subgroup.mem_subgroupOf.mpr e.2, rfl⟩
      rwa [hmap_phi φ hφ] at hmemmap
    have hqE : (q : G) ∈ E := by
      have hmemE : (⟨φ (⟨e.1, hEsubBs e.2⟩ : ↥Bs),
          (φ (⟨e.1, hEsubBs e.2⟩ : ↥Bs)).2⟩ : ↥Bs) ∈ EB := hφeB_mem
      rw [Subgroup.mem_subgroupOf] at hmemE
      have hEq : q = (⟨((φ (⟨e.1, hEsubBs e.2⟩ : ↥Bs) : ↥Bs) : G), hEsubJ hmemE⟩ : ↥J) := by
        apply Subtype.ext
        change (n : G) * (e : G) * (n : G)⁻¹ =
          ((φ (⟨e.1, hEsubBs e.2⟩ : ↥Bs) : ↥Bs) : G)
        exact (hnact ⟨e.1, hEsubBs e.2⟩).symm
      rw [hEq]
      exact hmemE
    have hγe : ggGamma J hN (⟨e.1, hEsubBs e.2⟩ : ↥Bs) = ggGamma J hN b := by
      have hval : (γEe e : MulAut ↥J) =
          ((ggGamma J hN).rangeRestrict b : MulAut ↥J) :=
        congrArg (fun a : A => (a : MulAut ↥J)) (γEe.apply_symm_apply _)
      change (γE e : MulAut ↥J) = ((ggGamma J hN).rangeRestrict b : MulAut ↥J)
      exact hval
    have hγn : ggGamma J hN (φ b) =
        MulAut.conj ⟨n, hnJ⟩ * ggGamma J hN b * (MulAut.conj ⟨n, hnJ⟩)⁻¹ := by
      rw [show φ b = ⟨(n : G) * (b : G) * (n : G)⁻¹, _⟩ by
        apply Subtype.ext
        exact hnact b]
      exact ggGamma_conj J hN ⟨n, hnJ⟩ b (by
        rw [← hnact b]
        exact (φ b).2)
    have hqBs : (⟨(q : G), hEsubBs hqE⟩ : ↥Bs) =
        ⟨(n : G) * (e : G) * (n : G)⁻¹, hEsubBs hqE⟩ := by
      apply Subtype.ext
      rfl
    have hγeφ : ggGamma J hN ((Subgroup.inclusion hEsubBs) eφ) = ggGamma J hN (φ b) := by
      have hval : ((γEe eφ : A) : MulAut ↥J) =
          ((ggGamma J hN).rangeRestrict (φ b) : MulAut ↥J) :=
        congrArg (fun a : A => (a : MulAut ↥J)) (γEe.apply_symm_apply _)
      change (ggGamma J hN) ((Subgroup.inclusion hEsubBs) eφ) = ggGamma J hN (φ b)
      exact hval
    have hγE_ne : γE ⟨q, hqE⟩ = γE eφ := by
      apply Subtype.ext
      dsimp [γE]
      change ggGamma J hN (⟨(q : G), hEsubBs hqE⟩ : ↥Bs) =
        ggGamma J hN ((Subgroup.inclusion hEsubBs) eφ)
      rw [hqBs]
      rw [ggGamma_conj J hN ⟨n, hnJ⟩ ⟨e.1, hEsubBs e.2⟩ (by
        rw [show (n : G) * (e : G) * (n : G)⁻¹ =
          ((φ (⟨e.1, hEsubBs e.2⟩ : ↥Bs) : ↥Bs) : G) from (hnact ⟨e.1, hEsubBs e.2⟩).symm]
        exact (φ ⟨e.1, hEsubBs e.2⟩).2)]
      rw [hγe, hγeφ, hγn]
    have hEeq : eφ = ⟨q, hqE⟩ := by
      apply γEe.injective
      exact hγE_ne.symm
    calc
      ρ (φ b) = φE eφ := rfl
      _ = φE ⟨q, hqE⟩ := by rw [hEeq]
      _ = ψ ⟨n, hnJ⟩ * φE e * (ψ ⟨n, hnJ⟩)⁻¹ := by
        change ψ (Subgroup.inclusion hEsubJ ⟨q, hqE⟩) =
          ψ ⟨n, hnJ⟩ * ψ (Subgroup.inclusion hEsubJ e) * (ψ ⟨n, hnJ⟩)⁻¹
        rw [show Subgroup.inclusion hEsubJ ⟨q, hqE⟩ =
          (⟨n, hnJ⟩ : ↥J) * Subgroup.inclusion hEsubJ e * (⟨n, hnJ⟩ : ↥J)⁻¹ from by
            apply Subtype.ext
            rfl]
        rw [map_mul, map_mul, map_inv]
      _ = ψ ⟨n, hnJ⟩ * ρ b * (ψ ⟨n, hnJ⟩)⁻¹ := rfl

  have hmap_top : (⊤ : Subgroup ↥E).map (Subgroup.subtype E) = E := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  have hEgenE : (⊤ : Subgroup ↥E) =
      Subgroup.closure ({⟨eG 0, he0E⟩, ⟨eG 1, he1E⟩} : Set ↥E) := by
    apply Subgroup.map_injective (Subgroup.subtype_injective E)
    rw [hmap_top, MonoidHom.map_closure]
    conv_lhs => rw [hEgen]
    have hset : Set.range eG =
        (Subgroup.subtype E) '' ({⟨eG 0, he0E⟩, ⟨eG 1, he1E⟩} : Set ↥E) := by
      ext z
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i
        · exact ⟨⟨eG 0, he0E⟩, by simp, rfl⟩
        · exact ⟨⟨eG 1, he1E⟩, by simp, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        rcases hy with rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    rw [hset]
  let t0 : R := φE ⟨eG 0, he0E⟩
  let t1 : R := φE ⟨eG 1, he1E⟩
  have ht0Ebar : t0 ∈ Ebar := by
    dsimp [Ebar, t0]
    exact ⟨_, rfl⟩
  have ht1Ebar : t1 ∈ Ebar := by
    dsimp [Ebar, t1]
    exact ⟨_, rfl⟩
  have hEbar_gen : Ebar = Subgroup.closure ({t0, t1} : Set R) := by
    dsimp [Ebar]
    rw [MonoidHom.range_eq_map, hEgenE, MonoidHom.map_closure]
    congr 1
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨⟨eG 0, he0E⟩, by simp, rfl⟩
      · exact ⟨⟨eG 1, he1E⟩, by simp, rfl⟩


  have hr0mem : r 0 ∈ ggAutomizer J Bs := by
    rw [hgen']
    exact Subgroup.subset_closure (by simp)
  obtain ⟨n0, hn0J, hn0N, hn0act⟩ := mem_ggAutomizer_iff.mp hr0mem
  have hr1mem : r 1 ∈ ggAutomizer J Bs := by
    rw [hgen']
    exact Subgroup.subset_closure (by simp)
  obtain ⟨n1, hn1J, hn1N, hn1act⟩ := mem_ggAutomizer_iff.mp hr1mem
  have ht0pow : t0 ^ 3 = 1 := by
    have h : (⟨eG 0, he0E⟩ : ↥E) ^ 3 = 1 :=
      Subtype.ext (hEelem.2 (eG 0) he0E)
    have h2 := congrArg φE h
    rw [map_pow] at h2
    simpa [t0] using h2
  have ht1pow : t1 ^ 3 = 1 := by
    have h : (⟨eG 1, he1E⟩ : ↥E) ^ 3 = 1 :=
      Subtype.ext (hEelem.2 (eG 1) he1E)
    have h2 := congrArg φE h
    rw [map_pow] at h2
    simpa [t1] using h2
  have hconj0 : IsConj t0 t0⁻¹ := by
    refine isConj_iff.mpr ⟨ψ ⟨n0, hn0J⟩, ?_⟩
    let e0J : ↥J := Subgroup.inclusion hEsubJ ⟨eG 0, he0E⟩
    have hEq : (⟨n0, hn0J⟩ : ↥J) * e0J * (⟨n0, hn0J⟩ : ↥J)⁻¹ = e0J⁻¹ := by
      apply Subtype.ext
      change (n0 : G) * (eG 0 : G) * (n0 : G)⁻¹ = (eG 0 : G)⁻¹
      rw [← hn0act (eB 0)]
      exact congrArg Subtype.val (hr0e0 (hmem 0).1)
    calc
      ψ ⟨n0, hn0J⟩ * t0 * (ψ ⟨n0, hn0J⟩)⁻¹ =
          ψ ((⟨n0, hn0J⟩ : ↥J) * e0J * (⟨n0, hn0J⟩ : ↥J)⁻¹) := by
        simp [t0, e0J, φE, map_mul, map_inv]
      _ = ψ e0J⁻¹ := by rw [hEq]
      _ = t0⁻¹ := by simp [t0, e0J, φE, map_inv]
  have hconj1 : IsConj t1 t1⁻¹ := by
    refine isConj_iff.mpr ⟨ψ ⟨n1, hn1J⟩, ?_⟩
    let e1J : ↥J := Subgroup.inclusion hEsubJ ⟨eG 1, he1E⟩
    have hEq : (⟨n1, hn1J⟩ : ↥J) * e1J * (⟨n1, hn1J⟩ : ↥J)⁻¹ = e1J⁻¹ := by
      apply Subtype.ext
      change (n1 : G) * (eG 1 : G) * (n1 : G)⁻¹ = (eG 1 : G)⁻¹
      rw [← hn1act (eB 1)]
      exact congrArg Subtype.val (hr1e1 (hmem 1).1)
    calc
      ψ ⟨n1, hn1J⟩ * t1 * (ψ ⟨n1, hn1J⟩)⁻¹ =
          ψ ((⟨n1, hn1J⟩ : ↥J) * e1J * (⟨n1, hn1J⟩ : ↥J)⁻¹) := by
        simp [t1, e1J, φE, map_mul, map_inv]
      _ = ψ e1J⁻¹ := by rw [hEq]
      _ = t1⁻¹ := by simp [t1, e1J, φE, map_inv]
  haveI : IsElementaryAbelian 3 Ebar := hEbar_elem.isElementaryAbelian
  have hclass : cubeClassHom (π := LargeEvenProjMk L)
      (hπ := QuotientGroup.mk'_surjective _)
      (hZ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.ker_projMk_uni_le_center L) Ebar = 1 := by
    apply MonoidHom.ext
    intro x
    have hxclos : (x : R) ∈ Subgroup.closure ({t0, t1} : Set R) := by
      rw [← hEbar_gen]
      exact x.2
    have hP : ∀ y (hy : y ∈ Subgroup.closure ({t0, t1} : Set R)),
        ∀ hyE : y ∈ Ebar, cubeClassHom (π := LargeEvenProjMk L)
          (hπ := QuotientGroup.mk'_surjective _)
          (hZ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.ker_projMk_uni_le_center L)
          Ebar ⟨y, hyE⟩ = 1 := by
      intro y hy
      refine Subgroup.closure_induction (p := fun y _ => ∀ hyE : y ∈ Ebar,
        cubeClassHom (π := LargeEvenProjMk L)
          (hπ := QuotientGroup.mk'_surjective _)
          (hZ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.ker_projMk_uni_le_center L)
          Ebar ⟨y, hyE⟩ = 1) ?_ ?_ ?_ ?_ hy
      · intro y hygen
        rcases hygen with rfl | rfl
        · intro hyE
          rw [cubeClassHom_apply]
          exact cubeClass_eq_one_of_isConj_inv
            (QuotientGroup.mk'_surjective _)
            (CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.ker_projMk_uni_le_center L)
            t0 ht0pow hconj0
        · intro hyE
          rw [cubeClassHom_apply]
          exact cubeClass_eq_one_of_isConj_inv
            (QuotientGroup.mk'_surjective _)
            (CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.ker_projMk_uni_le_center L)
            t1 ht1pow hconj1
      · intro hyE
        have h1 : (⟨1, hyE⟩ : Ebar) = 1 := Subtype.ext rfl
        rw [h1, map_one]
      · intro a b hxa hxb ha hb hyE
        have haE : a ∈ Ebar := by rw [hEbar_gen]; exact hxa
        have hbE : b ∈ Ebar := by rw [hEbar_gen]; exact hxb
        have h1 : (⟨a * b, hyE⟩ : Ebar) = (⟨a, haE⟩ : Ebar) * ⟨b, hbE⟩ :=
          Subtype.ext rfl
        rw [h1, map_mul, ha haE, hb hbE, mul_one]
      · intro a hxa ha hyE
        have haE : a ∈ Ebar := by rw [hEbar_gen]; exact hxa
        have h1 : (⟨a⁻¹, hyE⟩ : Ebar) = (⟨a, haE⟩ : Ebar)⁻¹ := Subtype.ext rfl
        rw [h1, map_inv, ha haE, inv_one]
    exact hP x hxclos x.2


  have hker_eq : (LargeEvenProjMk L).ker = unitaryScalars hU 3 := by
    rw [show LargeEvenProjMk L =
        QuotientGroup.mk' ((LargeEvenScalars (Fin 3) F).subgroupOf L) from rfl,
      QuotientGroup.ker_mk']
    rw [unitaryScalars_eq hU (by norm_num)]
    change (LargeEvenScalars (Fin 3) F).subgroupOf L =
      (CFSG.Open.StatedScalars (Fin 3) F).subgroupOf (unitarySU 2 n F 3)
    rfl
  have hkerexp : ∀ z ∈ (LargeEvenProjMk L).ker, z ^ 3 = 1 := by
    intro z hz
    rw [hker_eq] at hz
    obtain ⟨c, hnorm, hc3, hzscalar⟩ := (mem_unitaryScalars).mp hz
    apply Subtype.ext
    change ((z : GL (Fin 3) F)) ^ 3 = 1
    calc
      ((z : GL (Fin 3) F)) ^ 3 =
          (Matrix.GeneralLinearGroup.scalar (Fin 3) c) ^ 3 := by rw [hzscalar]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) (c ^ 3) := by rw [map_pow]
      _ = 1 := by rw [hc3, map_one]

  refine ⟨Ebar, hEbar_card, hEbar_elem, ?_, ?_, hkerexp⟩
  intro a b ha hb
  have hcomm := CFSG.StandardType.pair_zero_on_coroot_span hN ι r hvec α hform hα2 hind hgen
    (π := LargeEvenProjMk L) (hπ := QuotientGroup.mk'_surjective _)
    (hker := CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.ker_projMk_uni_le_center L)
    (ρ := ρ) hρker hconj (W := Submodule.span (ZMod 3) (Set.range hvec)) rfl ?_
  · exact hcomm a b (by simpa [hρrange] using ha) (by simpa [hρrange] using hb)
  · intro z hz
    rw [hρrange] at hz
    rcases hz with ⟨e, rfl⟩
    obtain ⟨b0, hb0⟩ := MonoidHom.rangeRestrict_surjective (ggGamma J hN) (γEe e)
    have heb : γEe.symm ((ggGamma J hN).rangeRestrict b0) = e := by
      rw [hb0]
      exact γEe.symm_apply_apply e
    have he : (e : G) ∈ ggSpanSub ι (Submodule.span (ZMod 3) (Set.range hvec)) := by
      rw [← hEspan]
      exact e.2
    obtain ⟨v, hv, hve⟩ := mem_ggSpanSub.mp he
    refine ⟨⟨v, hv⟩, ?_⟩
    change φE (γEe.symm ((ggGamma J hN).rangeRestrict
      (Additive.toMul (ι.symm v)))) = φE e
    rw [← heb]
    congr 1
    rw [show (Additive.toMul (ι.symm v) : ↥Bs) = ⟨e.1, hEsubBs e.2⟩ from Subtype.ext hve]
    have hb' : (ggGamma J hN).rangeRestrict b0 =
        (ggGamma J hN).rangeRestrict ⟨e.1, hEsubBs e.2⟩ := by
      rw [hb0]
      rfl
    exact congrArg γEe.symm hb'.symm
  · intro x hx
    have h := congrArg (fun f => f ⟨x, hx⟩) hclass
    simpa [cubeClassHom_apply] using h


private theorem B2_rank2_false
    {G : Type} [Group G] [Finite G]
    {B Bs L D J Kc : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y Kc)
    (hD : GGResLineJDatum 3 Bs J .B2)
    {F : Type} [Field F] [Finite F] {n : ℕ}
    (hU : UnitaryFieldData 2 n F)
    (hFcard : Nat.card F = (2 ^ n) ^ 2) (hn2 : 2 ≤ n) (hpq : 3 ∣ 2 ^ n + 1)
    (θ : ↥J ⧸ Subgroup.center ↥J ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin 3) F (2 ^ n)))
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (Aact : ↥Bs → GL (Fin 3) F)
    (hAGU : ∀ b, Aact b ∈ LargeEvenGUSet (Fin 3) F (2 ^ n))
    (hAproj : ∀ b, TableB.projConj (LargeEvenSUGroup (Fin 3) F (2 ^ n))
      ⟨Aact b, TableBUE.gu_subset_normalizer hU (hAGU b)⟩ = ggBeta J θ hN b)
    (hperfJ : commutator ↥J = ⊤) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let L : Subgroup (GL (Fin 3) F) := LargeEvenSUGroup (Fin 3) F (2 ^ n)
  let π : ↥L →* LargeEvenProj L := LargeEvenProjMk L
  obtain ⟨Ebar, hEbar_card, hEbar_elem, hcomm, hclassPt, hkerexp⟩ :=
    B2_rank2_preimage_commutative hH hD hU hFcard hn2 hpq θ hN Aact hAGU hAproj hperfJ
  haveI : IsElementaryAbelian 3 Ebar := hEbar_elem.isElementaryAbelian
  have hclass : cubeClassHom (π := π)
      (hπ := QuotientGroup.mk'_surjective _)
      (hZ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.ker_projMk_uni_le_center L) Ebar = 1 := by
    apply MonoidHom.ext
    intro e
    exact hclassPt e.1 e.2
  obtain ⟨U, hUelem, hUmap, hkerU, hUcard⟩ :=
    exists_isElementaryAbelian_lift_of_cubeClassHom_eq_one
      (QuotientGroup.mk'_surjective _)
      (CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.ker_projMk_uni_le_center L)
      hcomm hclass hkerexp
  have hker_eq : π.ker = unitaryScalars hU 3 := by
    dsimp [π, L]
    rw [show LargeEvenProjMk (LargeEvenSUGroup (Fin 3) F (2 ^ n)) =
        QuotientGroup.mk' ((LargeEvenScalars (Fin 3) F).subgroupOf
          (LargeEvenSUGroup (Fin 3) F (2 ^ n))) from rfl,
      QuotientGroup.ker_mk']
    rw [unitaryScalars_eq hU (by norm_num)]
    change (LargeEvenScalars (Fin 3) F).subgroupOf (LargeEvenSUGroup (Fin 3) F (2 ^ n)) =
      (CFSG.Open.StatedScalars (Fin 3) F).subgroupOf (unitarySU 2 n F 3)
    rfl
  have hker3 : Nat.card π.ker = 3 := by
    rw [hker_eq]
    exact (card_unitaryScalars hU (n := 3) (by norm_num)).trans (Nat.gcd_eq_left hpq)
  have hUcard27 : Nat.card U = 27 := by
    rw [hUcard, hker3, hEbar_card]
  let A9 : Subgroup (GL (Fin 3) F) := U.map (Subgroup.subtype L)
  have hA9card : Nat.card A9 = 27 := by
    dsimp [A9]
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective L), hUcard27]
  have hdet : ∀ g ∈ A9, (g : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rintro _ ⟨u, hu, rfl⟩
    have huSU : (u : GL (Fin 3) F) ∈ unitarySU 2 n F 3 := by
      change (u : GL (Fin 3) F) ∈ unitarySU 2 n F 3
      exact u.2
    exact ((mem_unitarySU_iff hU).mp huSU).1
  have hcommA9 : ∀ x ∈ A9, ∀ y ∈ A9, x * y = y * x := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    have h := hUelem.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩
    have hL : (u : ↥L) * (v : ↥L) = (v : ↥L) * (u : ↥L) :=
      congrArg (fun z : U => (z : ↥L)) h
    exact congrArg (fun z : ↥L => (z : GL (Fin 3) F)) hL
  have hpowA9 : ∀ x ∈ A9, x ^ 3 = 1 := by
    rintro _ ⟨u, hu, rfl⟩
    have hu3 : u ^ 3 = 1 := elemPow_eq_one_of_isElementaryAbelian (A := U) u hu
    simpa using congrArg (fun z : ↥L => (z : GL (Fin 3) F)) hu3
  have h3F : (3 : F) ≠ 0 := by
    haveI : CharP F 2 := hU.charP
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    have h3eq : (3 : F) = 1 := by
      calc (3 : F) = 2 + 1 := by norm_num
        _ = 1 := by rw [h2]; simp
    intro h
    rw [h3eq] at h
    norm_num at h
  have hle : Nat.card A9 ≤ 9 :=
    CFSG.HardMathSupport.Solomon.Coordinator.card_le_nine
      (F := F) h3F hdet hcommA9 hpowA9
  have : 27 ≤ 9 := by simpa [hA9card] using hle
  omega


theorem GGResHyp.actual_J_not_matched_unitary_for_B2
    {G : Type} [Group G] [Finite G]
    {B Bs L D J Kc : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y Kc)
    (hD : GGResLineJDatum 3 Bs J .B2)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs J) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hperfJ, lab, hΛ, hraw⟩ := hMark
  obtain ⟨tag, r, n⟩ := lab
  obtain ⟨R0, _, I0, F0, hQ0⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_, _, θ0, hP0⟩ := hQ0
  obtain ⟨hS0, _, _⟩ := hP0
  have htag : tag = .twA := hS0.1
  have hpq : 3 ∣ 2 ^ n + 1 := hS0.2
  have hΛtw : LargeEvenInLambda2 ⟨.twA, r, n⟩ := by simpa [htag] using hΛ
  have hr2 : 2 ≤ r := hΛtw.2.1
  by_cases hr3 : 3 ≤ r
  · have hMarkStrong : GGInnerDiagOnLabel
        (fun _ lab => lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n + 1 ∧ 3 ≤ lab.rank) 3 Bs J := by
      refine ⟨hperfJ, ⟨tag, r, n⟩, hΛ,
        largeEvenRawDatum_mono (lab := ⟨tag, r, n⟩) ?_ hraw⟩
      rintro R _ I F ⟨hs, hna, θ, hP⟩
      obtain ⟨hS, hN', hBsI⟩ := hP
      exact ⟨hs, hna, θ, ⟨⟨hS.1, hS.2, hr3⟩, hN', hBsI⟩⟩
    have hsmall : Nat.card (ggAutomizer J Bs) ≤ 8 := by
      rw [ggAutomizer_card_of_lineJDatum_B2 (p := 3) (by norm_num) hD]
    exact GGResHyp.false_of_compatible_unitary_marking_rank_ge_three_of_card_le_eight
      hH hD hMarkStrong hsmall
  · have hr2eq : r = 2 := by omega
    subst r
    subst tag
    have hn2 : 2 ≤ n := hΛ.2.2 rfl
    let S : ℕ → LargeEvenLabel → Prop := fun _ lab => lab = ⟨.twA, 2, n⟩
    have hSmark : GGInnerDiagOnLabel S 3 Bs J := by
      refine ⟨hperfJ, ⟨.twA, 2, n⟩, hΛ,
        largeEvenRawDatum_mono (lab := ⟨.twA, 2, n⟩) ?_ hraw⟩
      rintro R _ I F ⟨hs, hna, θ, hP⟩
      obtain ⟨hS, hN', hBsI⟩ := hP
      exact ⟨hs, hna, θ, ⟨rfl, hN', hBsI⟩⟩
    have hSspec : ∀ lab : LargeEvenLabel, S 3 lab →
        lab.tag = .twA ∧ 3 ≤ lab.rank + 1 ∧ lab.n ≠ 1 := by
      intro lab hlab
      subst hlab
      exact ⟨rfl, by norm_num, Nat.ne_of_gt (by omega : 1 < n)⟩
    have hgen := GGInnerDiagOnLabel.exists_general_unitary_cover_actors
      (S := S) hSmark hSspec
    unfold CFSG.StandardType.ResJUnitaryActor.GeneralUnitaryActorsConclusion at hgen
    obtain ⟨F, hFfield, hFfinite, d, f, lab2, hSlab2, _htag2, hd_eq, hf_eq, _hlab_eq,
      hf2, _hd3, hFcard, θ, φ, hU, Aact, ρ0, hN, hAGU, hAiso,
      hφs, hφker, hφcomp, hAprime, hAproj, hYact, hρ⟩ := hgen
    have hlab2 : lab2 = ⟨.twA, 2, n⟩ := hSlab2
    subst lab2
    have hd3 : d = 3 := by omega
    have hfn : f = n := hf_eq
    subst d
    subst f
    have hFcard' : Nat.card F = (2 ^ n) ^ 2 := hFcard
    have hU' : UnitaryFieldData 2 n F := hU
    exact B2_rank2_false hH hD hU' hFcard' hn2 hpq θ hN Aact hAGU hAproj hperfJ

end CFSG.StandardType

end
