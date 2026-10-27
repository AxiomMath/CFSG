module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcCent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley.EvenF4QPlus

private theorem ggKGEn_family_data
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    (hp : p.Prime) (hp3 : 3 ≤ p) (hτ6 : τ = .E6 → 5 ≤ p) (F : ExcFrame τ K p E)
    (hw : (p ∣ Nat.card K - 1 ∧ F.w = 1) ∨ (p ∣ Nat.card K + 1 ∧ ExcIsLongest τ F.w)) :
    ∃ (ι : Type) (a : ι → Fin τ.rank → (AlgebraicClosure K)ˣ),
      familyStabilizer a = {1} ∧ familyKernel a = ∅ ∧
        ∀ i, ∃ e ∈ E, rootDiagUnit τ (a i) =
          F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) * F.D.g0 := by
  obtain ⟨Fr, hFr, hΦ⟩ := F.frob
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_ringHom (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨ζu, hζu⟩ :=
    CFSG.LieType.SeitzGeneration.exists_primitiveRoot_units (L := AlgebraicClosure K) (ℓ := 2)
      (by norm_num) hp (by omega)
  let ζ : AlgebraicClosure K := ζu
  have hζ : IsPrimitiveRoot ζ p := IsPrimitiveRoot.coe_units_iff.2 hζu
  rcases hw with ⟨hpq, hwn⟩ | ⟨hpq, hlong⟩
  · let ι := {b : Fin τ.rank → (AlgebraicClosure K)ˣ // ∀ j, b j ^ p = 1}
    let a : ι → Fin τ.rank → (AlgebraicClosure K)ˣ := Subtype.val
    refine ⟨ι, a, ?_, ?_, ?_⟩
    · exact ggKGExc_familyStabilizer_allPTorsion (ζ := ζ) hτ hp hp3 hζ a
        fun b hb => ⟨⟨b, hb⟩, rfl⟩
    · exact ggKGExc_familyKernel_allPTorsion (ζ := ζ) hp hp3 hζ a
        fun b hb => ⟨⟨b, hb⟩, rfl⟩
    · intro i
      exact ggKGEx_exists_conj_of_hact hp hp3 hτ6 hτ F hΦ i.property
        (ggKGEx_hact_w_one F hFr hwn hpq i.property)
  · by_cases hE6 : τ = .E6
    · subst hE6
      let ι := {b : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ //
        (∀ j, b j ^ p = 1) ∧ ∀ i, b (ggKGEx_phi i) = b i}
      let a : ι → Fin Tag.E6.rank → (AlgebraicClosure K)ˣ := Subtype.val
      refine ⟨ι, a, ?_, ?_, ?_⟩
      · refine ggKGExc_familyStabilizer_phi (ζ := ζ) hp (hτ6 rfl) hζ a ?_
        intro b hb h05 h24
        exact ⟨⟨b, hb, ggKGEx_phi_fix h05 h24⟩, rfl⟩
      · refine ggKGExc_familyKernel_phi (ζ := ζ) hp (hτ6 rfl) hζ a ?_
        intro b hb h05 h24
        exact ⟨⟨b, hb, ggKGEx_phi_fix h05 h24⟩, rfl⟩
      · intro i
        exact ggKGEx_exists_conj_of_hact hp hp3 hτ6 hτ F hΦ i.property.1
          (ggKGEx_hact_w_phi F hFr hlong hpq i.property.1 i.property.2)
    · have hτ' : τ = .E7 ∨ τ = .E8 ∨ τ = .F4 := by
        rcases hτ with h | h | h | h
        · exact absurd h hE6
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      let ι := {b : Fin τ.rank → (AlgebraicClosure K)ˣ // ∀ j, b j ^ p = 1}
      let a : ι → Fin τ.rank → (AlgebraicClosure K)ˣ := Subtype.val
      refine ⟨ι, a, ?_, ?_, ?_⟩
      · exact ggKGExc_familyStabilizer_allPTorsion (ζ := ζ) hτ hp hp3 hζ a
          fun b hb => ⟨⟨b, hb⟩, rfl⟩
      · exact ggKGExc_familyKernel_allPTorsion (ζ := ζ) hp hp3 hζ a
          fun b hb => ⟨⟨b, hb⟩, rfl⟩
      · intro i
        exact ggKGEx_exists_conj_of_hact hp hp3 hτ6 hτ F hΦ i.property
          (ggKGEx_hact_w_neg F hFr hτ' hlong hpq i.property)

private theorem ggKGEn_conj_y_apply
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (F : ExcFrame τ K p E)
    (a e : adjointGroup τ K) :
    (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (a : ModGL τ K) * F.D.g0) *
      (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) * F.D.g0) *
      (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (a : ModGL τ K) * F.D.g0)⁻¹ =
    F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((a * e * a⁻¹ : adjointGroup τ K) : ModGL τ K) * F.D.g0 := by
  have hcoe : ((a * e * a⁻¹ : adjointGroup τ K) : ModGL τ K) =
      (a : ModGL τ K) * (e : ModGL τ K) * (a : ModGL τ K)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hcoe, map_mul, map_mul, map_inv]
  group

private theorem ggKGEn_conj_y_inv_apply
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (F : ExcFrame τ K p E)
    (a e : adjointGroup τ K) :
    (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (a : ModGL τ K) * F.D.g0)⁻¹ *
      (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) * F.D.g0) *
      (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (a : ModGL τ K) * F.D.g0) =
    F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((a⁻¹ * e * a : adjointGroup τ K) : ModGL τ K) * F.D.g0 := by
  have hcoe : ((a⁻¹ * e * a : adjointGroup τ K) : ModGL τ K) =
      (a : ModGL τ K)⁻¹ * (e : ModGL τ K) * (a : ModGL τ K) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hcoe, map_mul, map_mul, map_inv]
  group

private theorem ggKGEn_step_mem_torusGroup
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ} {E : Subgroup (adjointGroup τ K)}
    (F : ExcFrame τ K p E) {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    {h : ModGL τ (AlgebraicClosure K)} (hh : h ∈ torusGroup τ (AlgebraicClosure K)) :
    F.D.n * Units.map (entrywiseHom Fr) h * F.D.n⁻¹ ∈ torusGroup τ (AlgebraicClosure K) := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  have h1 : Units.map (entrywiseHom Fr) (rootDiagUnit τ b) =
      rootDiagUnit τ (fun i => Units.map Fr.toMonoidHom (b i)) :=
    Units.ext (entrywise_rootDiag Fr b)
  rw [h1]
  have h2 : rootDiagUnit τ (fun i => Units.map Fr.toMonoidHom (b i)) ∈
      torusGroup τ (AlgebraicClosure K) := rootDiagUnit_mem_torusGroup _
  rw [F.n_eq]
  exact (Subgroup.mem_normalizer_iff.1
    (canonicalRep_mem_normalizer (R := AlgebraicClosure K) F.w) _).1 h2

private theorem ggKGEn_eq_one_of_canonicalRep_mem_torusGroup
    {τ : Tag} {L : Type} [Field L] {v : WeylGroup τ}
    (h : canonicalRep (coxeterSystem τ) L v ∈ torusGroup τ L) : v = 1 :=
  ((mapsRootLines_of_mem_torusGroup h).unique (mapsRootLines_canonicalRep v)).symm

theorem ggKGExc_normalizer_weyl
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    (hp : p.Prime) (hp3 : 3 ≤ p) (hτ6 : τ = .E6 → 5 ≤ p) (F : ExcFrame τ K p E)
    (hw : (p ∣ Nat.card K - 1 ∧ F.w = 1) ∨ (p ∣ Nat.card K + 1 ∧ ExcIsLongest τ F.w))
    {x : adjointGroup τ K} (hx : x ∈ Subgroup.normalizer (E : Set (adjointGroup τ K))) :
    ∃ v : WeylGroup τ, v ∈ Subgroup.centralizer ({F.w} : Set (WeylGroup τ)) ∧
      ∀ e ∈ E,
        F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((x * e * x⁻¹ : adjointGroup τ K) : ModGL τ K) * F.D.g0 =
          canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v *
            (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) * F.D.g0) *
            (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v)⁻¹ := by
  classical
  obtain ⟨Fr, hFr, hΦ⟩ := F.frob
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_ringHom (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨ι, a, hstab, hker, hroot⟩ := ggKGEn_family_data hτ hp hp3 hτ6 F hw
  let L := AlgebraicClosure K
  let y : ModGL τ L :=
    F.D.g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL τ K) * F.D.g0
  let V : Set (ModGL τ L) :=
    {z | ∃ e ∈ E, z = F.D.g0⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL τ K) * F.D.g0}
  have hVH : V ⊆ torusGroup τ L := by
    rintro z ⟨e, he, rfl⟩
    exact (mem_twistedTorusOf.1 ((F.mem_iff e).1 he).2).1
  have hCV : adjointGroup τ L ⊓ Subgroup.centralizer V = torusGroup τ L := by
    refine le_antisymm ?_ ?_
    · intro g hg
      obtain ⟨hgG, hgC⟩ := Subgroup.mem_inf.1 hg
      have hfam : g ∈ familyCentralizer τ L a := by
        rw [mem_familyCentralizer]
        refine ⟨hgG, fun i => ?_⟩
        obtain ⟨e, he, heq⟩ := hroot i
        have hmem : rootDiagUnit τ (a i) ∈ V := ⟨e, he, heq⟩
        have hc : rootDiagUnit τ (a i) * g = g * rootDiagUnit τ (a i) := hgC _ hmem
        calc rootDiagUnit τ (a i) * g * (rootDiagUnit τ (a i))⁻¹
            = g * rootDiagUnit τ (a i) * (rootDiagUnit τ (a i))⁻¹ := by rw [hc]
          _ = g := by group
      exact ggKGEx_familyCentralizer_le_torus a hker hstab hfam
    · intro g hg
      refine Subgroup.mem_inf.2 ⟨torusGroup_le_adjointGroup' hg, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨e, he, rfl⟩ := hz
      have hzH : F.D.g0⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL τ K) * F.D.g0 ∈
          torusGroup τ L := hVH ⟨e, he, rfl⟩
      exact (mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hg)
        (torusGroup_le_diagonalGroup hzH)).symm
  have hg_mem : y ∈ adjointGroup τ L ⊓ Subgroup.normalizer V := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact mul_mem (mul_mem (inv_mem F.D.g0_mem)
        (CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup (algebraMap K L) x.property)) F.D.g0_mem
    · rw [Subgroup.mem_set_normalizer_iff]
      intro z
      constructor
      · intro hz
        obtain ⟨e, he, rfl⟩ := hz
        refine ⟨x * e * x⁻¹, (Subgroup.mem_normalizer_iff.1 hx e).1 he, ?_⟩
        exact ggKGEn_conj_y_apply F x e
      · intro hz
        obtain ⟨e, he, heq⟩ := hz
        have hxinv : x⁻¹ ∈ Subgroup.normalizer (E : Set (adjointGroup τ K)) :=
          Subgroup.inv_mem _ hx
        refine ⟨x⁻¹ * e * x, (Subgroup.mem_normalizer_iff.1 hxinv e).1 he, ?_⟩
        have hz_eq : z = y⁻¹ *
            (F.D.g0⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL τ K) * F.D.g0) * y := by
          calc z = y⁻¹ * (y * z * y⁻¹) * y := by group
            _ = y⁻¹ *
                (F.D.g0⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL τ K) * F.D.g0) * y := by
                  rw [heq]
        rw [hz_eq]
        change (F.D.g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL τ K) * F.D.g0)⁻¹ *
            (F.D.g0⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL τ K) * F.D.g0) *
            (F.D.g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL τ K) * F.D.g0) =
          F.D.g0⁻¹ * baseChangeGL (algebraMap K L)
            ((x⁻¹ * e * x : adjointGroup τ K) : ModGL τ K) * F.D.g0
        exact ggKGEn_conj_y_inv_apply F x e
  obtain ⟨h, hhT, v, hyv⟩ :=
    CFSG.RankThree.Chevalley.exists_eq_mul_canonicalRep_of_mem_normalizer hVH hCV hg_mem
  have hΦy : F.D.Φ y = F.D.n⁻¹ * y * F.D.n := by
    have hBx : Units.map (entrywiseHom Fr) (baseChangeGL (algebraMap K L) (x : ModGL τ K)) =
        baseChangeGL (algebraMap K L) (x : ModGL τ K) :=
      units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr (x : ModGL τ K)
    have hΦg : F.D.Φ F.D.g0 = F.D.g0 * F.D.n := F.D.lang
    change F.D.Φ (F.D.g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL τ K) * F.D.g0) =
      F.D.n⁻¹ * (F.D.g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL τ K) * F.D.g0) * F.D.n
    rw [map_mul, map_mul, map_inv, hΦg, hΦ, hBx]
    group
  have hstep : F.D.n * F.D.Φ y * F.D.n⁻¹ = y := by
    rw [hΦy]
    group
  have hstepH : F.D.n * F.D.Φ h * F.D.n⁻¹ ∈ torusGroup τ L := by
    rw [hΦ]
    exact ggKGEn_step_mem_torusGroup F hhT
  have hΦnv : F.D.Φ (canonicalRep (coxeterSystem τ) L v) =
      canonicalRep (coxeterSystem τ) L v := by
    rw [hΦ]
    exact frobenius_canonicalRep Fr v
  have hconj : F.D.n * F.D.Φ (canonicalRep (coxeterSystem τ) L v) * F.D.n⁻¹ =
      canonicalRep (coxeterSystem τ) L (F.w * v * F.w⁻¹) := by
    rw [hΦnv, F.n_eq]
    rw [canonicalRep_inv_of_charTwo (M := L) F.w,
      ← canonicalRep_mul_of_charTwo (M := L) F.w v,
      ← canonicalRep_mul_of_charTwo (M := L) (F.w * v) F.w⁻¹]
  have hstep_h : y = (F.D.n * F.D.Φ h * F.D.n⁻¹) *
      canonicalRep (coxeterSystem τ) L (F.w * v * F.w⁻¹) := by
    calc y = F.D.n * F.D.Φ y * F.D.n⁻¹ := hstep.symm
      _ = F.D.n * F.D.Φ (h * canonicalRep (coxeterSystem τ) L v) * F.D.n⁻¹ := by rw [hyv]
      _ = F.D.n * (F.D.Φ h * F.D.Φ (canonicalRep (coxeterSystem τ) L v)) * F.D.n⁻¹ := by
        rw [map_mul]
      _ = (F.D.n * F.D.Φ h * F.D.n⁻¹) *
          (F.D.n * F.D.Φ (canonicalRep (coxeterSystem τ) L v) * F.D.n⁻¹) := by group
      _ = (F.D.n * F.D.Φ h * F.D.n⁻¹) *
          canonicalRep (coxeterSystem τ) L (F.w * v * F.w⁻¹) := by rw [hconj]
  have hHcanon : canonicalRep (coxeterSystem τ) L ((F.w * v * F.w⁻¹) * v⁻¹) ∈
      torusGroup τ L := by
    have hh_eq : h * canonicalRep (coxeterSystem τ) L v =
        (F.D.n * F.D.Φ h * F.D.n⁻¹) *
          canonicalRep (coxeterSystem τ) L (F.w * v * F.w⁻¹) :=
      hyv.symm.trans hstep_h
    have hHn' : canonicalRep (coxeterSystem τ) L (F.w * v * F.w⁻¹) *
        (canonicalRep (coxeterSystem τ) L v)⁻¹ ∈ torusGroup τ L := by
      have hcalc : (F.D.n * F.D.Φ h * F.D.n⁻¹)⁻¹ * h =
          canonicalRep (coxeterSystem τ) L (F.w * v * F.w⁻¹) *
            (canonicalRep (coxeterSystem τ) L v)⁻¹ := by
        calc (F.D.n * F.D.Φ h * F.D.n⁻¹)⁻¹ * h
            = (F.D.n * F.D.Φ h * F.D.n⁻¹)⁻¹ * h *
                (canonicalRep (coxeterSystem τ) L v *
                  (canonicalRep (coxeterSystem τ) L v)⁻¹) := by group
          _ = (F.D.n * F.D.Φ h * F.D.n⁻¹)⁻¹ *
                (h * canonicalRep (coxeterSystem τ) L v) *
                (canonicalRep (coxeterSystem τ) L v)⁻¹ := by group
          _ = (F.D.n * F.D.Φ h * F.D.n⁻¹)⁻¹ *
                ((F.D.n * F.D.Φ h * F.D.n⁻¹) *
                  canonicalRep (coxeterSystem τ) L (F.w * v * F.w⁻¹)) *
                (canonicalRep (coxeterSystem τ) L v)⁻¹ := by rw [hh_eq]
          _ = canonicalRep (coxeterSystem τ) L (F.w * v * F.w⁻¹) *
                (canonicalRep (coxeterSystem τ) L v)⁻¹ := by group
      have hmem : (F.D.n * F.D.Φ h * F.D.n⁻¹)⁻¹ * h ∈ torusGroup τ L :=
        mul_mem (inv_mem hstepH) hhT
      rw [hcalc] at hmem
      exact hmem
    have hrew : canonicalRep (coxeterSystem τ) L ((F.w * v * F.w⁻¹) * v⁻¹) =
        canonicalRep (coxeterSystem τ) L (F.w * v * F.w⁻¹) *
          (canonicalRep (coxeterSystem τ) L v)⁻¹ := by
      rw [canonicalRep_mul_of_charTwo (M := L) (F.w * v * F.w⁻¹) v⁻¹,
        canonicalRep_inv_of_charTwo (M := L) v]
    rw [hrew]
    exact hHn'
  have hwu : (F.w * v * F.w⁻¹) * v⁻¹ = 1 :=
    ggKGEn_eq_one_of_canonicalRep_mem_torusGroup hHcanon
  have hcomm : F.w * v = v * F.w := by
    have h1 : F.w * v * F.w⁻¹ = v := by
      have := congrArg (fun z => z * v) hwu
      simpa [mul_assoc] using this
    calc F.w * v = (F.w * v * F.w⁻¹) * F.w := by group
      _ = v * F.w := by rw [h1]
  refine ⟨v, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact hcomm
  · intro e he
    have hconj_e : y *
        (F.D.g0⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL τ K) * F.D.g0) * y⁻¹ =
        F.D.g0⁻¹ * baseChangeGL (algebraMap K L)
          ((x * e * x⁻¹ : adjointGroup τ K) : ModGL τ K) * F.D.g0 :=
      ggKGEn_conj_y_apply F x e
    have hyeH : F.D.g0⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL τ K) * F.D.g0 ∈
        torusGroup τ L := (mem_twistedTorusOf.1 ((F.mem_iff e).1 he).2).1
    have hnvH : canonicalRep (coxeterSystem τ) L v *
        (F.D.g0⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL τ K) * F.D.g0) *
        (canonicalRep (coxeterSystem τ) L v)⁻¹ ∈ torusGroup τ L :=
      (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer (R := L) v) _).1 hyeH
    have hcentral : y *
        (F.D.g0⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL τ K) * F.D.g0) * y⁻¹ =
        canonicalRep (coxeterSystem τ) L v *
          (F.D.g0⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL τ K) * F.D.g0) *
          (canonicalRep (coxeterSystem τ) L v)⁻¹ := by
      calc y * (F.D.g0⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL τ K) * F.D.g0) * y⁻¹
          = (h * canonicalRep (coxeterSystem τ) L v) *
              (F.D.g0⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL τ K) * F.D.g0) *
              (h * canonicalRep (coxeterSystem τ) L v)⁻¹ := by rw [hyv]
        _ = h * (canonicalRep (coxeterSystem τ) L v *
              (F.D.g0⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL τ K) * F.D.g0) *
              (canonicalRep (coxeterSystem τ) L v)⁻¹) * h⁻¹ := by group
        _ = (canonicalRep (coxeterSystem τ) L v *
              (F.D.g0⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL τ K) * F.D.g0) *
              (canonicalRep (coxeterSystem τ) L v)⁻¹) * h * h⁻¹ := by
            rw [mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hhT)
              (torusGroup_le_diagonalGroup hnvH)]
        _ = canonicalRep (coxeterSystem τ) L v *
              (F.D.g0⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL τ K) * F.D.g0) *
              (canonicalRep (coxeterSystem τ) L v)⁻¹ := by group
    exact hconj_e.symm.trans hcentral

theorem ggKGExc_normalizer_faithful
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    (hp : p.Prime) (hp3 : 3 ≤ p) (hτ6 : τ = .E6 → 5 ≤ p) (F : ExcFrame τ K p E)
    (hw : (p ∣ Nat.card K - 1 ∧ F.w = 1) ∨ (p ∣ Nat.card K + 1 ∧ ExcIsLongest τ F.w))
    {v : WeylGroup τ}
    (hv : ∀ e ∈ E,
      canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v *
          (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) * F.D.g0) *
          (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v)⁻¹ =
        F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) * F.D.g0) :
    v = 1 := by
  classical
  let L := AlgebraicClosure K
  obtain ⟨ι, a, hstab, hker, hroot⟩ := ggKGEn_family_data hτ hp hp3 hτ6 F hw
  have hv_stab : v ∈ familyStabilizer a := by
    refine fun i => ?_
    show ∀ u : Fin τ.rank → ℤ, rootChar (a i) (v • u) = rootChar (a i) u
    intro u
    obtain ⟨e, he, heq⟩ := hroot i
    have hfix : canonicalRep (coxeterSystem τ) L v * rootDiagUnit τ (a i) *
        (canonicalRep (coxeterSystem τ) L v)⁻¹ = rootDiagUnit τ (a i) := by
      rw [heq]
      exact hv e he
    have htuple : weylTuple v (a i) = a i := by
      apply rootDiagUnit_injective
      rw [← canonicalRep_conj_rootDiagUnit]
      exact hfix
    have h := congrArg (fun t => rootChar t (v • u)) htuple
    rw [rootChar_weylTuple, inv_smul_smul] at h
    exact h.symm
  have : v ∈ ({1} : Set (WeylGroup τ)) := hstab ▸ hv_stab
  simpa using this

end CFSG.StandardType

end
