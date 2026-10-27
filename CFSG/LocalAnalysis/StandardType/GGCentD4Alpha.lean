module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneInput
public import CFSG.LocalAnalysis.StandardType.GGCentD4Diagram
public import CFSG.LocalAnalysis.StandardType.GGCentD4HomExt
public import CFSG.LocalAnalysis.StandardType.GGCentD4Theta
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentPerm
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCentralizer
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4Basic
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeSylow

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KD4T
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6 CFSG.RankThree.Chevalley

section Certs


variable {L : Type} [Field L]

private def Acts (a : Fin Tag.E6.rank → Lˣ)
    (Θ : ↥(rootSpan Tag.E6 L (rootCharKernel a)) ≃* ↥(adjointGroup Tag.D4 L))
    (x : ModGL Tag.E6 L) (ε : ℕ) : Prop :=
  x ∈ Subgroup.normalizer
      (rootSpan Tag.E6 L (rootCharKernel a) : Set (ModGL Tag.E6 L)) ∧
    ∃ g : ↥(adjointGroup Tag.D4 L),
      ∀ (y : ModGL Tag.E6 L) (hy : y ∈ rootSpan Tag.E6 L (rootCharKernel a))
        (hy' : x * y * x⁻¹ ∈ rootSpan Tag.E6 L (rootCharKernel a)),
        Θ ⟨x * y * x⁻¹, hy'⟩ = g * d4Graph L ε (Θ ⟨y, hy⟩) * g⁻¹

private theorem mem_rootSpan_of_mem_normalizer {a : Fin Tag.E6.rank → Lˣ}
    {x y : ModGL Tag.E6 L}
    (hx : x ∈ Subgroup.normalizer
      (rootSpan Tag.E6 L (rootCharKernel a) : Set (ModGL Tag.E6 L)))
    (hy : y ∈ rootSpan Tag.E6 L (rootCharKernel a)) :
    x * y * x⁻¹ ∈ rootSpan Tag.E6 L (rootCharKernel a) :=
  (Subgroup.mem_normalizer_iff.1 hx y).1 hy

private theorem acts_one {a : Fin Tag.E6.rank → Lˣ}
    {Θ : ↥(rootSpan Tag.E6 L (rootCharKernel a)) ≃* ↥(adjointGroup Tag.D4 L)} :
    Acts a Θ 1 0 := by
  refine ⟨Subgroup.one_mem _, ⟨1, ?_⟩⟩
  intro y hy hy'
  rw [d4Graph_zero]
  have h : (⟨1 * y * 1⁻¹, hy'⟩ : ↥(rootSpan Tag.E6 L (rootCharKernel a))) = ⟨y, hy⟩ :=
    Subtype.ext (by group)
  rw [h]
  simp

private theorem acts_zero_mul {a : Fin Tag.E6.rank → Lˣ}
    {Θ : ↥(rootSpan Tag.E6 L (rootCharKernel a)) ≃* ↥(adjointGroup Tag.D4 L)}
    {x z : ModGL Tag.E6 L} {ε : ℕ} (hx : Acts a Θ x 0) (hz : Acts a Θ z ε) :
    Acts a Θ (x * z) ε := by
  refine ⟨Subgroup.mul_mem _ hx.1 hz.1, ?_⟩
  obtain ⟨g, hg⟩ := hx.2
  obtain ⟨h, hh⟩ := hz.2
  refine ⟨g * h, ?_⟩
  intro y hy hy'
  have hzy : z * y * z⁻¹ ∈ rootSpan Tag.E6 L (rootCharKernel a) :=
    mem_rootSpan_of_mem_normalizer hz.1 hy
  have hxzy : x * (z * y * z⁻¹) * x⁻¹ ∈ rootSpan Tag.E6 L (rootCharKernel a) :=
    mem_rootSpan_of_mem_normalizer hx.1 hzy
  have h1 : Θ ⟨x * z * y * (x * z)⁻¹, hy'⟩ =
      Θ ⟨x * (z * y * z⁻¹) * x⁻¹, hxzy⟩ := by
    congr 1
  rw [h1, hg (z * y * z⁻¹) hzy hxzy, d4Graph_zero, MulAut.one_apply,
    hh y hy hzy]
  group

private theorem acts_inv_zero {a : Fin Tag.E6.rank → Lˣ}
    {Θ : ↥(rootSpan Tag.E6 L (rootCharKernel a)) ≃* ↥(adjointGroup Tag.D4 L)}
    {x : ModGL Tag.E6 L} (hx : Acts a Θ x 0) : Acts a Θ x⁻¹ 0 := by
  refine ⟨Subgroup.inv_mem _ hx.1, ?_⟩
  obtain ⟨g, hg⟩ := hx.2
  refine ⟨g⁻¹, ?_⟩
  intro y hy hy'
  simp only [inv_inv] at hy' ⊢
  have hz : x⁻¹ * y * x ∈ rootSpan Tag.E6 L (rootCharKernel a) :=
    mem_rootSpan_of_mem_normalizer (Subgroup.inv_mem _ hx.1) hy
  have hxzy : x * (x⁻¹ * y * x) * x⁻¹ ∈ rootSpan Tag.E6 L (rootCharKernel a) :=
    mem_rootSpan_of_mem_normalizer hx.1 hz
  have hmain := hg (x⁻¹ * y * x) hz hxzy
  have hconj : Θ ⟨x * (x⁻¹ * y * x) * x⁻¹, hxzy⟩ = Θ ⟨y, hy⟩ := by
    congr 1
    exact Subtype.ext (by group)
  rw [hconj, d4Graph_zero, MulAut.one_apply] at hmain
  rw [d4Graph_zero, MulAut.one_apply]
  have hz_eq : Θ ⟨x⁻¹ * y * x, hz⟩ = g⁻¹ * Θ ⟨y, hy⟩ * g := by
    rw [hmain]
    group
  have hsub : (⟨x⁻¹ * y * x, hy'⟩ : ↥(rootSpan Tag.E6 L (rootCharKernel a))) =
      ⟨x⁻¹ * y * x, hz⟩ := Subtype.ext rfl
  rw [hsub]
  exact hz_eq

private def actsSet (a : Fin Tag.E6.rank → Lˣ)
    (Θ : ↥(rootSpan Tag.E6 L (rootCharKernel a)) ≃* ↥(adjointGroup Tag.D4 L)) :
    Subgroup (ModGL Tag.E6 L) where
  carrier := {x | Acts a Θ x 0}
  one_mem' := acts_one
  mul_mem' hx hz := acts_zero_mul hx hz
  inv_mem' hx := acts_inv_zero hx

private theorem acts_zero_of_mem_rootSpan {a : Fin Tag.E6.rank → Lˣ}
    {Θ : ↥(rootSpan Tag.E6 L (rootCharKernel a)) ≃* ↥(adjointGroup Tag.D4 L)}
    {x : ModGL Tag.E6 L} (hx : x ∈ rootSpan Tag.E6 L (rootCharKernel a)) :
    Acts a Θ x 0 := by
  refine ⟨Subgroup.le_normalizer hx, ⟨Θ ⟨x, hx⟩, ?_⟩⟩
  intro y hy hy'
  rw [d4Graph_zero, MulAut.one_apply]
  have h : (⟨x * y * x⁻¹, hy'⟩ : ↥(rootSpan Tag.E6 L (rootCharKernel a))) =
      ⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ := Subtype.ext rfl
  rw [h]
  simp only [map_mul, map_inv]

private theorem acts_zero_of_mem_torus {a : Fin Tag.E6.rank → Lˣ}
    {Θ : ↥(rootSpan Tag.E6 L (rootCharKernel a)) ≃* ↥(adjointGroup Tag.D4 L)}
    (htorus : ∀ τ ∈ torusGroup Tag.E6 L,
      ∃ τ' : ↥(adjointGroup Tag.D4 L), ∀ (y : ModGL Tag.E6 L)
        (hy : y ∈ rootSpan Tag.E6 L (rootCharKernel a))
        (hy' : τ * y * τ⁻¹ ∈ rootSpan Tag.E6 L (rootCharKernel a)),
        Θ ⟨τ * y * τ⁻¹, hy'⟩ = τ' * Θ ⟨y, hy⟩ * τ'⁻¹)
    {τ : ModGL Tag.E6 L} (hτ : τ ∈ torusGroup Tag.E6 L) : Acts a Θ τ 0 := by
  refine ⟨(toralCentralizer_le_normalizer_rootSpan a)
    (torusGroup_le_toralCentralizer a hτ), ?_⟩
  obtain ⟨τ', hτ'⟩ := htorus τ hτ
  exact ⟨τ', fun y hy hy' => by rw [d4Graph_zero]; exact hτ' y hy hy'⟩

private theorem acts_zero_of_mem_toralRootGroup {a : Fin Tag.E6.rank → Lˣ}
    {Θ : ↥(rootSpan Tag.E6 L (rootCharKernel a)) ≃* ↥(adjointGroup Tag.D4 L)}
    (htorus : ∀ τ ∈ torusGroup Tag.E6 L,
      ∃ τ' : ↥(adjointGroup Tag.D4 L), ∀ (y : ModGL Tag.E6 L)
        (hy : y ∈ rootSpan Tag.E6 L (rootCharKernel a))
        (hy' : τ * y * τ⁻¹ ∈ rootSpan Tag.E6 L (rootCharKernel a)),
        Θ ⟨τ * y * τ⁻¹, hy'⟩ = τ' * Θ ⟨y, hy⟩ * τ'⁻¹)
    {x : ModGL Tag.E6 L} (hx : x ∈ toralRootGroup Tag.E6 L a) : Acts a Θ x 0 := by
  rw [toralRootGroup] at hx
  exact (sup_le (fun τ hτ => acts_zero_of_mem_torus htorus hτ)
    (fun x hx => acts_zero_of_mem_rootSpan hx) :
      torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (rootCharKernel a) ≤ actsSet a Θ) hx

private theorem acts_canonicalRep_of_not_mem {a : Fin Tag.E6.rank → Lˣ}
    {Θ : ↥(rootSpan Tag.E6 L (rootCharKernel a)) ≃* ↥(adjointGroup Tag.D4 L)}
    (ha3 : ∀ i, a i ^ 3 = 1) (v : WeylGroup Tag.E6)
    (hv : rootCharKernel a =
      (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    (hgraph : ∀ (z : WeylGroup Tag.E6) (ε : ℕ),
      (∀ k : Fin Tag.D4.rank,
        z • (v • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ)) =
          v • (Pi.single (d4Idx ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k)) 1 : Fin Tag.E6.rank → ℤ)) →
      ∀ (y : ModGL Tag.E6 L) (hy : y ∈ rootSpan Tag.E6 L (rootCharKernel a))
        (hy' : canonicalRep (coxeterSystem Tag.E6) L z * y *
          (canonicalRep (coxeterSystem Tag.E6) L z)⁻¹ ∈
            rootSpan Tag.E6 L (rootCharKernel a)),
        Θ ⟨canonicalRep (coxeterSystem Tag.E6) L z * y *
          (canonicalRep (coxeterSystem Tag.E6) L z)⁻¹, hy'⟩ =
            d4Graph L ε (Θ ⟨y, hy⟩))
    (htorus : ∀ τ ∈ torusGroup Tag.E6 L,
      ∃ τ' : ↥(adjointGroup Tag.D4 L), ∀ (y : ModGL Tag.E6 L)
        (hy : y ∈ rootSpan Tag.E6 L (rootCharKernel a))
        (hy' : τ * y * τ⁻¹ ∈ rootSpan Tag.E6 L (rootCharKernel a)),
        Θ ⟨τ * y * τ⁻¹, hy'⟩ = τ' * Θ ⟨y, hy⟩ * τ'⁻¹)
    {w : WeylGroup Tag.E6} (hw : w ∈ rootCharStabilizerSubgroup a)
    (hw' : w ∉ kernelReflectionGroup a) :
    ∃ ε : ℕ, (ε = 1 ∨ ε = 2) ∧
      Acts a Θ (canonicalRep (coxeterSystem Tag.E6) L w) ε := by
  classical
  obtain ⟨u, ε, hu, hε3, hε0, hact⟩ := ntpD4_diagram a ha3 v hv w hw
  have hε : ε = 1 ∨ ε = 2 := by
    have hne := hε0 hw'
    omega
  have huW : u ∈ rootCharStabilizerSubgroup a := kernelReflectionGroup_le a hu
  have huwW : u * w ∈ rootCharStabilizerSubgroup a := mul_mem huW hw
  have huwN : canonicalRep (coxeterSystem Tag.E6) L (u * w) ∈
      Subgroup.normalizer
        (rootSpan Tag.E6 L (rootCharKernel a) : Set (ModGL Tag.E6 L)) :=
    canonicalRep_mem_normalizer_rootSpan_rootCharKernel
      (mem_rootCharStabilizerSubgroup.1 huwW)
  have hgraphActs : Acts a Θ (canonicalRep (coxeterSystem Tag.E6) L (u * w)) ε := by
    refine ⟨huwN, ⟨1, ?_⟩⟩
    intro y hy hy'
    simpa using hgraph (u * w) ε hact y hy hy'
  have huM : canonicalRep (coxeterSystem Tag.E6) L u ∈ toralRootGroup Tag.E6 L a := by
    have hmem : (⟨u, huW⟩ : rootCharStabilizerSubgroup a) ∈
        (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a) :=
      Subgroup.mem_subgroupOf.2 hu
    have h1 := kernelReflectionGroup_le_ker (K := L) a hmem
    rw [MonoidHom.mem_ker, weylToralQuotientHom_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at h1
    exact h1
  obtain ⟨k, hk, hk_eq⟩ := canonicalRep_mul_mem (R := L) u w
  have huInvZ : Acts a Θ ((canonicalRep (coxeterSystem Tag.E6) L u)⁻¹) 0 :=
    acts_inv_zero (acts_zero_of_mem_toralRootGroup htorus huM)
  have hkZ : Acts a Θ k 0 := acts_zero_of_mem_toralRootGroup htorus (Subgroup.mem_sup_left hk)
  have hprod : Acts a Θ ((canonicalRep (coxeterSystem Tag.E6) L u)⁻¹ * k) 0 :=
    acts_zero_mul huInvZ hkZ
  have hcw : Acts a Θ (canonicalRep (coxeterSystem Tag.E6) L w) ε := by
    have heq : canonicalRep (coxeterSystem Tag.E6) L w =
        (canonicalRep (coxeterSystem Tag.E6) L u)⁻¹ * k *
          canonicalRep (coxeterSystem Tag.E6) L (u * w) := by
      calc canonicalRep (coxeterSystem Tag.E6) L w
          = (canonicalRep (coxeterSystem Tag.E6) L u)⁻¹ *
              (canonicalRep (coxeterSystem Tag.E6) L u *
                canonicalRep (coxeterSystem Tag.E6) L w) := by group
        _ = (canonicalRep (coxeterSystem Tag.E6) L u)⁻¹ *
              (k * canonicalRep (coxeterSystem Tag.E6) L (u * w)) := by rw [hk_eq]
        _ = (canonicalRep (coxeterSystem Tag.E6) L u)⁻¹ * k *
              canonicalRep (coxeterSystem Tag.E6) L (u * w) := by group
    rw [heq]
    exact acts_zero_mul hprod hgraphActs
  exact ⟨ε, hε, hcw⟩

end Certs

theorem ntpD4_torus_conj
    {L : Type} [Field L] [IsAlgClosed L] (v : WeylGroup Tag.E6)
    (Y : Subgroup (ModGL Tag.E6 L))
    (hY : Y = rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)))
    (Θ : ↥Y ≃* ↥(adjointGroup Tag.D4 L))
    (hΘ : ∀ (y : ↥Y) (k : Fin Tag.D4.rank) (c : L),
      ((y : ModGL Tag.E6 L) = canonicalRep (coxeterSystem Tag.E6) L v *
          xUnit Tag.E6 L (d4Idx k) c * (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ →
        (Θ y : ModGL Tag.D4 L) = xUnit Tag.D4 L k c) ∧
      ((y : ModGL Tag.E6 L) = canonicalRep (coxeterSystem Tag.E6) L v *
          yUnit Tag.E6 L (d4Idx k) c * (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ →
        (Θ y : ModGL Tag.D4 L) = yUnit Tag.D4 L k c))
    (τ : ModGL Tag.E6 L) (hτ : τ ∈ torusGroup Tag.E6 L) :
    (∀ y ∈ Y, τ * y * τ⁻¹ ∈ Y) ∧
      ∃ τ' : ↥(adjointGroup Tag.D4 L),
        ∀ (y : ModGL Tag.E6 L) (hy : y ∈ Y) (hy' : τ * y * τ⁻¹ ∈ Y),
          Θ ⟨τ * y * τ⁻¹, hy'⟩ = τ' * Θ ⟨y, hy⟩ * τ'⁻¹ := by
  classical
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hτ
  let nv : ModGL Tag.E6 L := canonicalRep (coxeterSystem Tag.E6) L v
  have hS : ∀ α ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      IsRoot Tag.E6 α := by
    rintro α ⟨β, hβ, rfl⟩
    exact IsRoot.smul hβ.1 v
  have hroot (k : Fin Tag.D4.rank) :
      IsRoot Tag.E6 (v • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ)) :=
    IsRoot.smul (isRoot_single Tag.E6 (d4Idx k)) v
  let b : Fin Tag.D4.rank → Lˣ := fun k =>
    CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar l
      (v • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ))
  have hchar (k : Fin Tag.D4.rank) :
      torusRootChar (rootDiagUnit Tag.E6 l)
        (v • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ)) = ((b k : Lˣ) : L) :=
    CFSG.RankThree.Chevalley.EvenF4QPlus.torusRootChar_rootDiagUnit l (hroot k)
  have hchar_neg (k : Fin Tag.D4.rank) :
      torusRootChar (rootDiagUnit Tag.E6 l)
        (-(v • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ))) = (((b k)⁻¹ : Lˣ) : L) := by
    rw [CFSG.RankThree.Chevalley.EvenF4QPlus.torusRootChar_rootDiagUnit l (IsRoot.neg (hroot k))]
    have hneg : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar l
        (-(v • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ))) =
        (CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar l
          (v • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ)))⁻¹ := by
      have h := CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar_sub l 0
        (v • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ))
      rw [zero_sub, CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar_zero,
        one_mul] at h
      exact h
    rw [hneg]
  have hNA : rootDiagUnit Tag.E6 l ∈ Subgroup.normalizer
      (rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)) :
        Set (ModGL Tag.E6 L)) :=
    CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan hS hτ
  have hNmemA : ∀ y : ModGL Tag.E6 L,
      y ∈ rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)) →
        rootDiagUnit Tag.E6 l * y * (rootDiagUnit Tag.E6 l)⁻¹ ∈
          rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)) :=
    fun y hy => (Subgroup.mem_normalizer_iff.1 hNA y).1 hy
  have hNmem : ∀ y : ModGL Tag.E6 L, y ∈ Y →
      rootDiagUnit Tag.E6 l * y * (rootDiagUnit Tag.E6 l)⁻¹ ∈ Y := by
    intro y hy
    rw [hY] at hy ⊢
    exact hNmemA y hy
  let cY : ↥Y →* ↥Y :=
    { toFun := fun y =>
        ⟨rootDiagUnit Tag.E6 l * (y : ModGL Tag.E6 L) * (rootDiagUnit Tag.E6 l)⁻¹,
          hNmem (y : ModGL Tag.E6 L) y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y =>
        Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_one]; group) }
  have hmem : rootDiagUnit Tag.D4 b ∈ adjointGroup Tag.D4 L :=
    CFSG.LieType.AlgebraicGroups.torusGroup_le_adjointGroup
      (rootDiagUnit_mem_torusGroup b)
  let τ' : ↥(adjointGroup Tag.D4 L) := ⟨rootDiagUnit Tag.D4 b, hmem⟩
  let φ : ↥Y →* ↥(adjointGroup Tag.D4 L) := Θ.toMonoidHom.comp cY
  let ψ : ↥Y →* ↥(adjointGroup Tag.D4 L) :=
    (MulAut.conj τ').toMonoidHom.comp Θ.toMonoidHom
  have hxgen : ∀ (y : ↥Y) (k : Fin Tag.D4.rank) (c : L),
      (y : ModGL Tag.E6 L) = nv * xUnit Tag.E6 L (d4Idx k) c * nv⁻¹ → φ y = ψ y := by
    intro y k c hgen
    obtain ⟨εx, -, hεx⟩ :=
      exists_canonicalRep_mul_pinnedX_mul_inv (R := L) v (isRoot_single Tag.E6 (d4Idx k))
    have hconj : rootDiagUnit Tag.E6 l * (y : ModGL Tag.E6 L) * (rootDiagUnit Tag.E6 l)⁻¹ =
        nv * xUnit Tag.E6 L (d4Idx k) ((b k : L) * c) * nv⁻¹ := by
      rw [hgen, ← pinnedX_single Tag.E6 L (d4Idx k) c, hεx c,
        conj_pinnedX_of_mem_torusGroup hτ (hroot k) (εx * c), hchar k]
      rw [← pinnedX_single Tag.E6 L (d4Idx k) ((b k : L) * c), hεx ((b k : L) * c)]
      congr 1
      ring
    have hφ : (φ y : ModGL Tag.D4 L) = xUnit Tag.D4 L k ((b k : L) * c) := by
      change (Θ ⟨rootDiagUnit Tag.E6 l * (y : ModGL Tag.E6 L) * (rootDiagUnit Tag.E6 l)⁻¹,
          hNmem (y : ModGL Tag.E6 L) y.2⟩ : ModGL Tag.D4 L) = xUnit Tag.D4 L k ((b k : L) * c)
      exact (hΘ ⟨rootDiagUnit Tag.E6 l * (y : ModGL Tag.E6 L) * (rootDiagUnit Tag.E6 l)⁻¹,
        hNmem (y : ModGL Tag.E6 L) y.2⟩ k ((b k : L) * c)).1 hconj
    have hψ : (ψ y : ModGL Tag.D4 L) = xUnit Tag.D4 L k ((b k : L) * c) := by
      have hΘy : (Θ y : ModGL Tag.D4 L) = xUnit Tag.D4 L k c := (hΘ y k c).1 hgen
      change rootDiagUnit Tag.D4 b * (Θ y : ModGL Tag.D4 L) * (rootDiagUnit Tag.D4 b)⁻¹ =
        xUnit Tag.D4 L k ((b k : L) * c)
      rw [hΘy, (root_diagonal_conjugation Tag.D4 L b).1 k c]
    exact Subtype.ext (hφ.trans hψ.symm)
  have hygen : ∀ (y : ↥Y) (k : Fin Tag.D4.rank) (c : L),
      (y : ModGL Tag.E6 L) = nv * yUnit Tag.E6 L (d4Idx k) c * nv⁻¹ → φ y = ψ y := by
    intro y k c hgen
    obtain ⟨εy, -, hεy⟩ :=
      exists_canonicalRep_mul_pinnedX_mul_inv (R := L) v (isRoot_neg_single Tag.E6 (d4Idx k))
    have hεy' : ∀ d : L, nv * pinnedX Tag.E6 L
        (-(Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ)) d * nv⁻¹ =
        pinnedX Tag.E6 L (-(v • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ)))
          (εy * d) := by
      intro d
      simpa only [smul_neg] using hεy d
    have hconj : rootDiagUnit Tag.E6 l * (y : ModGL Tag.E6 L) * (rootDiagUnit Tag.E6 l)⁻¹ =
        nv * yUnit Tag.E6 L (d4Idx k) (((b k)⁻¹ : Lˣ) * c) * nv⁻¹ := by
      rw [hgen, ← pinnedX_neg_single Tag.E6 L (d4Idx k) c, hεy' c,
        conj_pinnedX_of_mem_torusGroup hτ (IsRoot.neg (hroot k)) (εy * c), hchar_neg k]
      rw [← pinnedX_neg_single Tag.E6 L (d4Idx k) (((b k)⁻¹ : Lˣ) * c),
        hεy' (((b k)⁻¹ : Lˣ) * c)]
      congr 1
      ring
    have hφ : (φ y : ModGL Tag.D4 L) = yUnit Tag.D4 L k (((b k)⁻¹ : Lˣ) * c) := by
      change (Θ ⟨rootDiagUnit Tag.E6 l * (y : ModGL Tag.E6 L) * (rootDiagUnit Tag.E6 l)⁻¹,
          hNmem (y : ModGL Tag.E6 L) y.2⟩ : ModGL Tag.D4 L) =
        yUnit Tag.D4 L k (((b k)⁻¹ : Lˣ) * c)
      exact (hΘ ⟨rootDiagUnit Tag.E6 l * (y : ModGL Tag.E6 L) * (rootDiagUnit Tag.E6 l)⁻¹,
        hNmem (y : ModGL Tag.E6 L) y.2⟩ k (((b k)⁻¹ : Lˣ) * c)).2 hconj
    have hψ : (ψ y : ModGL Tag.D4 L) = yUnit Tag.D4 L k (((b k)⁻¹ : Lˣ) * c) := by
      have hΘy : (Θ y : ModGL Tag.D4 L) = yUnit Tag.D4 L k c := (hΘ y k c).2 hgen
      change rootDiagUnit Tag.D4 b * (Θ y : ModGL Tag.D4 L) * (rootDiagUnit Tag.D4 b)⁻¹ =
        yUnit Tag.D4 L k (((b k)⁻¹ : Lˣ) * c)
      rw [hΘy, (root_diagonal_conjugation Tag.D4 L b).2.1 k c]
    exact Subtype.ext (hφ.trans hψ.symm)
  have hφψ : φ = ψ := ntpD4_hom_ext (L := L) v Y hY Θ hΘ hxgen hygen
  refine ⟨hNmem, τ', ?_⟩
  intro y hy hy'
  have h := DFunLike.congr_fun hφψ ⟨y, hy⟩
  have harg : (⟨rootDiagUnit Tag.E6 l * y * (rootDiagUnit Tag.E6 l)⁻¹, hy'⟩ : ↥Y) =
      ⟨rootDiagUnit Tag.E6 l * y * (rootDiagUnit Tag.E6 l)⁻¹, hNmem y hy⟩ := Subtype.ext rfl
  rw [harg]
  exact h


theorem ntpD4_alpha
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀) (a : Fin Tag.E6.rank → Lˣ) (n : ModGL .E6 L)
    (hpair : OrderThreeOutsideConnected S a n) (v : WeylGroup Tag.E6)
    (hv : rootCharKernel a =
      (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    (Y : Subgroup (ModGL Tag.E6 L)) (hY : Y = rootSpan Tag.E6 L (rootCharKernel a))
    (Θ : ↥Y ≃* ↥(adjointGroup Tag.D4 L))
    (hgraph : ∀ (z : WeylGroup Tag.E6) (ε : ℕ),
      (∀ k : Fin Tag.D4.rank,
        z • (v • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ)) =
          v • (Pi.single (d4Idx ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k)) 1 : Fin Tag.E6.rank → ℤ)) →
      ∀ (y : ModGL Tag.E6 L) (hy : y ∈ Y)
        (hy' : canonicalRep (coxeterSystem Tag.E6) L z * y *
          (canonicalRep (coxeterSystem Tag.E6) L z)⁻¹ ∈ Y),
        Θ ⟨canonicalRep (coxeterSystem Tag.E6) L z * y *
          (canonicalRep (coxeterSystem Tag.E6) L z)⁻¹, hy'⟩ =
            d4Graph L ε (Θ ⟨y, hy⟩))
    (_htorus : ∀ τ ∈ torusGroup Tag.E6 L, ∀ (y : ModGL Tag.E6 L) (hy : y ∈ Y)
      (hy' : τ * y * τ⁻¹ ∈ Y),
      ∃ τ' : ↥(adjointGroup Tag.D4 L), Θ ⟨τ * y * τ⁻¹, hy'⟩ = τ' * Θ ⟨y, hy⟩ * τ'⁻¹) :
    ∃ (g : ↥(adjointGroup Tag.D4 L)) (ε : ℕ), (ε = 1 ∨ ε = 2) ∧
      ∀ (y : ModGL .E6 L) (hy : y ∈ Y) (hy' : n * y * n⁻¹ ∈ Y),
        Θ ⟨n * y * n⁻¹, hy'⟩ = g * d4Graph L ε (Θ ⟨y, hy⟩) * g⁻¹ := by
  classical
  subst hY
  have hYv : rootSpan Tag.E6 L (rootCharKernel a) =
      rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)) := by
    rw [hv]
  obtain ⟨Θ₀, hΘ₀⟩ := ntpD4_theta (L := L) v
  let Θ₀' : ↥(rootSpan Tag.E6 L (rootCharKernel a)) ≃* ↥(adjointGroup Tag.D4 L) :=
    (MulEquiv.subgroupCongr hYv).trans Θ₀
  have hΘ₀' : ∀ (y : ↥(rootSpan Tag.E6 L (rootCharKernel a))) (k : Fin Tag.D4.rank) (c : L),
      ((y : ModGL Tag.E6 L) = canonicalRep (coxeterSystem Tag.E6) L v *
          xUnit Tag.E6 L (d4Idx k) c * (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ →
        (Θ₀' y : ModGL Tag.D4 L) = xUnit Tag.D4 L k c) ∧
      ((y : ModGL Tag.E6 L) = canonicalRep (coxeterSystem Tag.E6) L v *
          yUnit Tag.E6 L (d4Idx k) c * (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ →
        (Θ₀' y : ModGL Tag.D4 L) = yUnit Tag.D4 L k c) := by
    intro y k c
    let z : ↥(d4KernelGroup L v) :=
      ⟨y, by
        change (y : ModGL Tag.E6 L) ∈
          rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
        rw [← hYv]
        exact y.2⟩
    have hcoe : (Θ₀' y : ModGL Tag.D4 L) = (Θ₀ z : ModGL Tag.D4 L) := by
      change (Θ₀ ((MulEquiv.subgroupCongr hYv) y) : ModGL Tag.D4 L) = (Θ₀ z : ModGL Tag.D4 L)
      rw [show ((MulEquiv.subgroupCongr hYv) y : ↥(d4KernelGroup L v)) = z from Subtype.ext rfl]
    have h := hΘ₀ z k c
    constructor
    · intro hgen
      rw [hcoe]
      exact h.1 (by simpa [z] using hgen)
    · intro hgen
      rw [hcoe]
      exact h.2 (by simpa [z] using hgen)
  have hinner₀ := ntpD4_torus_conj (L := L) v
    (rootSpan Tag.E6 L (rootCharKernel a)) hYv Θ₀' hΘ₀'
  let β : ↥(adjointGroup Tag.D4 L) ≃* ↥(adjointGroup Tag.D4 L) := Θ₀'.symm.trans Θ
  have hβ : ∀ z : ↥(rootSpan Tag.E6 L (rootCharKernel a)), β (Θ₀' z) = Θ z := by
    intro z
    simp [β]
  have htorus : ∀ τ ∈ torusGroup Tag.E6 L,
      ∃ τ' : ↥(adjointGroup Tag.D4 L), ∀ (y : ModGL Tag.E6 L)
        (hy : y ∈ rootSpan Tag.E6 L (rootCharKernel a))
        (hy' : τ * y * τ⁻¹ ∈ rootSpan Tag.E6 L (rootCharKernel a)),
        Θ ⟨τ * y * τ⁻¹, hy'⟩ = τ' * Θ ⟨y, hy⟩ * τ'⁻¹ := by
    intro τ hτ
    obtain ⟨τ₀, hτ₀⟩ := (hinner₀ τ hτ).2
    refine ⟨β τ₀, ?_⟩
    intro y hy hy'
    rw [← hβ ⟨τ * y * τ⁻¹, hy'⟩, hτ₀ y hy hy']
    simp only [map_mul, map_inv]
    rw [hβ ⟨y, hy⟩]
  obtain ⟨ha3, -, -, hnMM, -, hcomm, C, m, hm, hC, hCn, hCd, -, hW2⟩ := hpair
  have hnC : n ∈ toralCentralizer .E6 L a := by
    refine mem_toralCentralizer.2 ⟨(S.D.mem_model.1 hnMM).1, ?_⟩
    calc rootDiagUnit .E6 a * n * (rootDiagUnit .E6 a)⁻¹
        = n * rootDiagUnit .E6 a * (rootDiagUnit .E6 a)⁻¹ := by rw [hcomm]
      _ = n := by group
  have hnM' : n ∉ toralRootGroup .E6 L a := by
    intro hnM
    have hcommC : C * rootDiagUnit .E6 a = rootDiagUnit .E6 a * C := by
      calc C * rootDiagUnit .E6 a
          = (C * rootDiagUnit .E6 a * C⁻¹) * C := by group
        _ = rootDiagUnit .E6 a * C := by rw [hCd]
    have hCd' : rootDiagUnit .E6 a * C * (rootDiagUnit .E6 a)⁻¹ = C := by
      rw [← hcommC]
      group
    have hCtp : C ∈ toralCentralizer .E6 L a := mem_toralCentralizer.2 ⟨hC, hCd'⟩
    have hCm : m ∈ toralRootGroup .E6 L a := by
      have hnN := (Subgroup.mem_normalizer_iff.1
        (toralCentralizer_le_normalizer a hCtp) n).1 hnM
      rwa [hCn] at hnN
    obtain ⟨w₁, k₁, hk₁, hkw⟩ := monomialSubgroup_le_torusWeylCosets hm
    have hmaps : MapsRootLines m w₁ := by
      rw [hkw]
      simpa using (mapsRootLines_of_mem_torusGroup hk₁).mul (mapsRootLines_canonicalRep w₁)
    have hwq : weylQuotientHom .E6 L ⟨m, hm⟩ = w₁ := weylQuotientHom_eq hmaps
    have hwK : w₁ ∈ kernelReflectionGroup a := by
      refine mem_kernelReflectionGroup_of_canonicalRep_mem_gen ?_
      have h1 : k₁⁻¹ * m ∈ toralRootGroup .E6 L a :=
        mul_mem (inv_mem (Subgroup.mem_sup_left hk₁)) hCm
      have e : canonicalRep (coxeterSystem Tag.E6) L w₁ = k₁⁻¹ * m := by
        rw [hkw]
        group
      rwa [e]
    rw [hwq] at hW2
    exact hW2 hwK
  obtain ⟨w, hw, μ, hμ, hn_eq⟩ :=
    exists_mul_canonicalRep_of_mem_toralCentralizer (K := L) a hnC
  have hwsub : w ∈ rootCharStabilizerSubgroup a := mem_rootCharStabilizerSubgroup.2 hw
  have hwker : w ∉ kernelReflectionGroup a := by
    intro hwK
    apply hnM'
    have hcM : canonicalRep (coxeterSystem Tag.E6) L w ∈ toralRootGroup .E6 L a := by
      have hmem : (⟨w, hwsub⟩ : rootCharStabilizerSubgroup a) ∈
          (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a) :=
        Subgroup.mem_subgroupOf.2 hwK
      have h1 := kernelReflectionGroup_le_ker (K := L) a hmem
      rw [MonoidHom.mem_ker, weylToralQuotientHom_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf] at h1
      exact h1
    rw [hn_eq]
    exact mul_mem hμ hcM
  obtain ⟨ε, hε, hcw⟩ :=
    acts_canonicalRep_of_not_mem ha3 v hv hgraph htorus hwsub hwker
  have hnActs : Acts a Θ n ε := by
    rw [hn_eq]
    exact acts_zero_mul (acts_zero_of_mem_toralRootGroup htorus hμ) hcw
  obtain ⟨g, hg⟩ := hnActs.2
  exact ⟨g, ε, hε, hg⟩

end CFSG.StandardType.NTPlane

end
