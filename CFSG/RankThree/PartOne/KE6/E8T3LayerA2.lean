module

public import CFSG.RankThree.PartOne.KE6.E8T3Conj
public import CFSG.RankThree.PartOne.KE.SigmaFactorTransport
public import CFSG.RankThree.PartOne.KE6.E8T3A2
public import CFSG.RankThree.PartOne.KE6.E8T3Act

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
open scoped MatrixGroups

variable {L : Type} [Field L]

theorem sigmaSetE8_isRoot (v : WeylGroup Tag.E8) : ∀ r ∈ sigmaSetE8 v, IsRoot Tag.E8 r :=
  fun r hr => by
    rw [sigmaSetE8_eq] at hr
    obtain ⟨i, j, hij, rfl⟩ := hr
    exact isRoot_sigmaRootE8 v hij

theorem sigmaSetE8_transport (v : WeylGroup Tag.E8) :
    (fun γ => v • γ) '' sigmaSetE8 1 = sigmaSetE8 v := by
  simp only [sigmaSetE8, Set.image_image, one_smul]

theorem edge_02_mem : ((0 : Fin Tag.E8.rank), (2 : Fin Tag.E8.rank)) ∈ e8Edges := by decide

theorem layer_A2_with_model [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f)
    {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L] (hk : Nat.card k = ℓ ^ f) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hq2 : ε = -1 → 2 < ℓ ^ f) (v : WeylGroup Tag.E8)
    (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L) (hnC : n ∈ adjointGroup Tag.E8 L)
    (hnW : ∀ x : V8, weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • x = e8T3We ε • x)
    (hSv : ∀ α ∈ sigmaSetE8 v, e8T3We ε • α ∈ sigmaSetE8 v)
    (hSneg : ∀ α ∈ sigmaSetE8 v, -α ∈ sigmaSetE8 v) :
    ∃ P : Subgroup (ModGL Tag.E8 L),
      P = rootSpan Tag.E8 L (sigmaSetE8 v) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) ∧
      SigmaFactor n (iterateFrobenius L ℓ f) (sigmaSetE8 v) (fun _ : Unit => P)
        (Subgroup.normalizer (rootSpan Tag.E8 L (sigmaSetE8 v) : Set (ModGL Tag.E8 L))) ∧
      (ε = 1 → Nonempty (P ≃* SL(3, k))) ∧
      ∃ h₀ : ModGL Tag.E8 L, ∀ Y : SL(2, k),
        h₀ * simpleRootSL2 Tag.E8 L (e8Index 0)
          (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈ P := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (show 0 < ℓ ^ f from pow_pos hℓ.pos f)
    exact ⟨x, by rw [hFr, hx]⟩⟩
  set Φ : ModGL Tag.E8 L →* ModGL Tag.E8 L := Units.map (entrywiseHom Fr) with hΦ
  set V : ModGL Tag.E8 L := canonicalRep (coxeterSystem Tag.E8) L v with hV
  have hVm : V ∈ monomialSubgroup Tag.E8 L := canonicalRep_mem_monomialSubgroup L v
  have hVadj : V ∈ adjointGroup Tag.E8 L := canonicalRep_mem_adjointGroup _ L v
  have hΦV : Φ V = V := by
    have h1 := entrywise_canonicalRep (RingEquiv.ofBijective Fr hFrbij) v
    have h2 : (RingEquiv.ofBijective Fr hFrbij).toRingHom = Fr := RingHom.ext fun _ => rfl
    rw [h2] at h1
    exact h1
  set n' : ModGL Tag.E8 L := V⁻¹ * n * V with hn'
  have hn'm : n' ∈ monomialSubgroup Tag.E8 L := mul_mem (mul_mem (inv_mem hVm) hnm) hVm
  have hn'adj : n' ∈ adjointGroup Tag.E8 L := mul_mem (mul_mem (inv_mem hVadj) hnC) hVadj
  have hπV : weylQuotientHom Tag.E8 L ⟨V, hVm⟩ = v :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep v)
  have hπn' : weylQuotientHom Tag.E8 L ⟨n', hn'm⟩ =
      v⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hnm⟩ * v := by
    have : (⟨n', hn'm⟩ : monomialSubgroup Tag.E8 L) = ⟨V, hVm⟩⁻¹ * ⟨n, hnm⟩ * ⟨V, hVm⟩ :=
      Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv, hπV]
  have hT''rel : ∀ x : V8, (v⁻¹ * e8T3W * v) • (v⁻¹ * e8T3W * v) • x + (v⁻¹ * e8T3W * v) • x + x
      = 0 := by
    intro x
    have := rel_conj e8T3W_rel v⁻¹ x
    simpa using this
  have hW'' : ∀ x : V8, (v⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hnm⟩ * v) • x =
      ε • ((v⁻¹ * e8T3W * v) • x) := conj_smul_eq hε hnW v
  have hcoe : (↑({0, 2} : Finset (Fin Tag.E8.rank)) : Set (Fin Tag.E8.rank)) = e8support13 := by
    ext i
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, e8support13]
    rfl
  have hmaps : ∀ β ∈ parabolicRoots Tag.E8 (↑({0, 2} : Finset (Fin Tag.E8.rank)) :
      Set (Fin Tag.E8.rank)), (v⁻¹ * e8T3W * v) • β ∈ parabolicRoots Tag.E8
        (↑({0, 2} : Finset (Fin Tag.E8.rank)) : Set (Fin Tag.E8.rank)) := by
    intro β hβ
    rw [hcoe] at hβ ⊢
    have h1 : v • β ∈ sigmaSetE8 v := ⟨β, hβ, rfl⟩
    have h2 := stab_of_We hε hSneg hSv _ h1
    obtain ⟨γ, hγ, hγv⟩ := h2
    rw [mul_smul, mul_smul]
    have : v⁻¹ • e8T3W • v • β = γ := by
      rw [← hγv]
      simp only [inv_smul_smul]
    rw [this]
    exact hγ
  have hcols := e8T3_cols_A2 hT''rel edge_02_mem hmaps
  obtain ⟨π, hπ⟩ := e8T3_shape_std hε hW'' hcols
  have hπ' : ∀ i j : Fin 3, i ≠ j → weylQuotientHom Tag.E8 L ⟨n', hn'm⟩ • sigmaRootE8 1 i j =
      if ε = 1 then sigmaRootE8 1 (π i) (π j) else sigmaRootE8 1 (π j) (π i) := by
    rw [hπn']
    exact hπ
  obtain ⟨P', hP'1, hfac, hmodel, h₀', hh₀'⟩ := e8_a2_factor_with_model hℓ hf hk hε hq2 Fr hFr 1 n' hn'm π hπ'
  have hroots := sigmaSetE8_isRoot 1
  have htr := SigmaFactor.transport Fr hFrbij v n hroots hfac
  rw [sigmaSetE8_transport v] at htr
  set c₀ : ModGL Tag.E8 L →* ModGL Tag.E8 L := (MulAut.conj V).toMonoidHom with hc₀
  have hcapp : ∀ x, c₀ x = V * x * V⁻¹ := fun x => by simp [hc₀, MulAut.conj_apply]
  have hPeq : P'.map c₀ = rootSpan Tag.E8 L (sigmaSetE8 v) ⊓ twistedFixedPoints n Φ := by
    have hQ : (rootSpan Tag.E8 L (sigmaSetE8 1)).map c₀ = rootSpan Tag.E8 L (sigmaSetE8 v) := by
      rw [map_conj_rootSpan v hroots, sigmaSetE8_transport v]
    have hR : (twistedFixedPoints n' Φ).map c₀ = twistedFixedPoints n Φ := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [hcapp]
        exact (mem_twistedFixedPoints_conj hΦV).1 hx
      · intro hy
        refine ⟨V⁻¹ * y * V, (mem_twistedFixedPoints_conj hΦV).2 ?_, ?_⟩
        · have e : V * (V⁻¹ * y * V) * V⁻¹ = y := by group
          rw [e]
          exact hy
        · rw [hcapp]
          group
    rw [hP'1, Subgroup.map_inf _ _ c₀ (MulAut.conj V).injective, hQ, hR]
  refine ⟨P'.map c₀, hPeq, ⟨htr.finite, htr.quasi, htr.le_root, htr.le_fix, htr.le_adj,
    fun _ y hy hyR u hu => ?_, htr.thetaFree⟩, ?_, ?_⟩
  · rw [hPeq] at hu ⊢
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hy u).1 hu.1,
      mul_mem (mul_mem hyR hu.2) (inv_mem hyR)⟩
  · intro hε1
    obtain ⟨eP⟩ := hmodel hε1
    exact ⟨(Subgroup.equivMapOfInjective P' c₀ (MulAut.conj V).injective).symm.trans eP⟩
  · refine ⟨V * h₀', fun Y => ?_⟩
    refine ⟨h₀' * simpleRootSL2 Tag.E8 L (e8Index 0)
      (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀'⁻¹, hh₀' Y, ?_⟩
    rw [hcapp]
    group

theorem layer_A2 [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f)
    {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L] (hk : Nat.card k = ℓ ^ f) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hq2 : ε = -1 → 2 < ℓ ^ f) (v : WeylGroup Tag.E8)
    (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L) (hnC : n ∈ adjointGroup Tag.E8 L)
    (hnW : ∀ x : V8, weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • x = e8T3We ε • x)
    (hSv : ∀ α ∈ sigmaSetE8 v, e8T3We ε • α ∈ sigmaSetE8 v)
    (hSneg : ∀ α ∈ sigmaSetE8 v, -α ∈ sigmaSetE8 v) :
    ∃ P : Subgroup (ModGL Tag.E8 L),
      P = rootSpan Tag.E8 L (sigmaSetE8 v) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) ∧
      SigmaFactor n (iterateFrobenius L ℓ f) (sigmaSetE8 v) (fun _ : Unit => P)
        (Subgroup.normalizer (rootSpan Tag.E8 L (sigmaSetE8 v) : Set (ModGL Tag.E8 L))) ∧
      ∃ h₀ : ModGL Tag.E8 L, ∀ Y : SL(2, k),
        h₀ * simpleRootSL2 Tag.E8 L (e8Index 0)
          (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈ P := by
  obtain ⟨P, hP, hfac, _, hroot⟩ :=
    layer_A2_with_model hf hk hε hq2 v n hnm hnC hnW hSv hSneg
  exact ⟨P, hP, hfac, hroot⟩

end CFSG.RankThree.PartOne.KE6
