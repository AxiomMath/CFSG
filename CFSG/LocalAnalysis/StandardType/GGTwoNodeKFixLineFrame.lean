module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeKFixLineDefs
public import CFSG.LocalAnalysis.StandardType.GGHLAutomizer
public import CFSG.LocalAnalysis.StandardType.GGRowKFrame

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTwoNodeKFixLineFrameInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G) (N : ℕ), GGResHyp p B Bs x L D J y K →
    ¬ GGCoxeterForkDatum p Bs L K → ¬ GGCoxeterStdDatum p Bs L K → ¬ GGE6DepPerpCfg p Bs L K →
    GGResRowAt (fun p labJ labK => ggRowTwoNode p labJ labK ∧ labK.rank + 1 = N) p J K →
    p ≠ 2 → 5 ≤ N → N ≤ 10 → p ∣ N → GGResXDatumAIndep p Bs K (N - 1) → ∀ hx : x ∈ Bs,
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
      (h : Fin (N - 1) → V) (α : Fin (N - 1) → Module.Dual (ZMod p) V)
      (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (T : Type) (_ : Finite T) (s : T → (V ≃ₗ[ZMod p] V)),
      Module.finrank (ZMod p) V ≤ N ∧ LinearIndependent (ZMod p) h ∧
      (∀ i j, α i (h j) = (CartanMatrix.A (N - 1) i j : ZMod p)) ∧
      (∀ i v, r i v = v - α i v • h i) ∧
      Subgroup.closure (Set.range r) = (ggAutomizer K Bs).map (ggLin (p := p) ι) ∧
      (∀ k, GGLinRefl (s k)) ∧
      (SimpleGraph.fromRel fun i j => s i * s j ≠ s j * s i).Connected ∧
      ggLinFix (Set.range s) = Submodule.span (ZMod p) {ι (Additive.ofMul ⟨x, hx⟩)} ∧
      ι (Additive.ofMul ⟨x, hx⟩) ≠ 0 ∧ ι (Additive.ofMul ⟨x, hx⟩) ∉ ggLinFix (Set.range r) ∧
      (∀ g ∈ Subgroup.closure (Set.range r ∪ Set.range s),
        ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))

theorem ggTwoNodeKFixLine_of_lin (hLin : GGIndepFixLineLin) (hFrame : GGTwoNodeKFixLineFrameInput) :
    GGTwoNodeKFixLineInput := by
  intro G _ _ p _ B Bs x L D J y K N hH hF hS hE hrow hp2 hN5 hN10 hpN hyK hXI b
  classical
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hyD : y ∈ D := by
    rw [hH.2.2.2.2.1.2.1]
    exact Subgroup.subset_closure (by simp)
  have hy : y ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hyD)
  have hy1 : y ≠ 1 := ggRC_y_ne_one hH
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hH.2.2.2.2.1.1.2.2.2.1
  have hfixy : ∀ φ ∈ ggAutomizer K Bs, φ (⟨y, hy⟩ : ↥Bs) = ⟨y, hy⟩ :=
    ggHLA_fixes_x hKy hy
  obtain ⟨V, iVadd, iVmod, ι, h, α, r, T, iT, s,
      hdim, hind, hpair, hr, hclosure, hs, hconn, hfixs, hx0, hxnot, hnt⟩ :=
    hFrame G p B Bs x L D J y K N hH hF hS hE hrow hp2 hN5 hN10 hpN hXI hx
  letI := iVadd
  letI := iVmod
  letI := iT
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let F : Submodule (ZMod p) V := ggLinFix (Set.range r)
  let xV : V := ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))
  let vy : V := ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))
  have hFfin : Module.finrank (ZMod p) F = 1 :=
    hLin p N hp2 hN5 hpN V hdim h α r hind hpair hr T s hs hconn xV hx0 hfixs hxnot hnt
  have hvy_mem : vy ∈ F := by
    intro a ha
    rcases ha with ⟨i, rfl⟩
    have hri : r i ∈ Subgroup.closure (Set.range r) := Subgroup.subset_closure ⟨i, rfl⟩
    rw [hclosure] at hri
    rcases Subgroup.mem_map.mp hri with ⟨φ, hφA, hφi⟩
    calc (r i) vy = ggLin (p := p) ι φ vy := by rw [hφi]
      _ = ggLin (p := p) ι φ (ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) := rfl
      _ = ι (Additive.ofMul (φ (⟨y, hy⟩ : ↥Bs))) := by rw [ggLin_apply_ofMul]
      _ = ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) := by rw [hfixy φ hφA]
      _ = vy := rfl
  have hvy0 : vy ≠ 0 := by
    intro h0
    have h1 : Additive.ofMul (⟨y, hy⟩ : ↥Bs) = 0 := by
      apply ι.injective
      simpa [vy] using h0
    have h2 : (⟨y, hy⟩ : ↥Bs) = 1 := by
      have := congrArg Additive.toMul h1
      simpa using this
    exact hy1 (by simpa using congrArg Subtype.val h2)
  have hspan_le : Submodule.span (ZMod p) ({vy} : Set V) ≤ F := by
    rw [Submodule.span_le]
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    rw [hv]
    exact hvy_mem
  have hFeq : F = Submodule.span (ZMod p) ({vy} : Set V) :=
    (Submodule.eq_of_le_of_finrank_eq hspan_le
      (by rw [finrank_span_singleton hvy0, hFfin])).symm
  constructor
  ·
    intro hb
    have hbF : ι (Additive.ofMul b) ∈ F := by
      intro a ha
      rcases ha with ⟨i, rfl⟩
      have hri : r i ∈ Subgroup.closure (Set.range r) := Subgroup.subset_closure ⟨i, rfl⟩
      rw [hclosure] at hri
      rcases Subgroup.mem_map.mp hri with ⟨φ, hφA, hφi⟩
      calc (r i) (ι (Additive.ofMul b))
          = ggLin (p := p) ι φ (ι (Additive.ofMul b)) := by rw [hφi]
        _ = ι (Additive.ofMul (φ b)) := by rw [ggLin_apply_ofMul]
        _ = ι (Additive.ofMul b) := by rw [hb φ hφA]
    rw [hFeq] at hbF
    rcases Submodule.mem_span_singleton.mp hbF with ⟨c, hc⟩
    have hc' : (c.val : ℤ) • vy = ι (Additive.ofMul b) := by
      rw [← Int.cast_smul_eq_zsmul (R := ZMod p)]
      simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
      exact hc
    have hpow : Additive.ofMul ((⟨y, hy⟩ : ↥Bs) ^ (c.val : ℤ)) = Additive.ofMul b := by
      apply ι.injective
      calc ι (Additive.ofMul ((⟨y, hy⟩ : ↥Bs) ^ (c.val : ℤ)))
          = ι ((c.val : ℤ) • Additive.ofMul (⟨y, hy⟩ : ↥Bs)) := by rw [ofMul_zpow]
        _ = (c.val : ℤ) • ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) := by rw [map_zsmul]
        _ = (c.val : ℤ) • vy := rfl
        _ = ι (Additive.ofMul b) := hc'
    refine Subgroup.mem_zpowers_iff.mpr ⟨(c.val : ℤ), ?_⟩
    have hc2 := congrArg (fun z : ↥Bs => (z : G)) (congrArg Additive.toMul hpow)
    simpa using hc2
  ·
    intro hb φ hφA
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hbk : b = (⟨y, hy⟩ : ↥Bs) ^ k := Subtype.ext (by simpa using hk.symm)
    rw [hbk, map_zpow, hfixy φ hφA]

end CFSG.StandardType

end
