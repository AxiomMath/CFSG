module

public import CFSG.LocalAnalysis.StandardType.GGIndepFixLineAssembly
public import CFSG.LocalAnalysis.StandardType.GGIndepFixLineWeyl
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeKFixLineFrame

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggIndepFixLineLin_of_zs (hZS : ZS.UseInput) : GGIndepFixLineLin :=
  ggIndepFixLineLin_of_families hZS ggFixLineNotWeyl_holds

theorem ggTwoNodeKFixLineInput_of_zs_frame (hZS : ZS.UseInput)
    (hFrame : GGTwoNodeKFixLineFrameInput) : GGTwoNodeKFixLineInput :=
  ggTwoNodeKFixLine_of_lin (ggIndepFixLineLin_of_zs hZS) hFrame

theorem ggTwoNodeKIndep_false_of_not_mem (hLin : GGIndepFixLineLin)
    (hFrame : GGTwoNodeKFixLineFrameInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G} {N : ℕ}
    (hH : GGResHyp p B Bs x L D J y K) (hF : ¬ GGCoxeterForkDatum p Bs L K)
    (hS : ¬ GGCoxeterStdDatum p Bs L K) (hE : ¬ GGE6DepPerpCfg p Bs L K)
    (hrow : GGResRowAt (fun p labJ labK => ggRowTwoNode p labJ labK ∧ labK.rank + 1 = N) p J K)
    (hp2 : p ≠ 2) (hN5 : 5 ≤ N) (hN10 : N ≤ 10) (hpN : p ∣ N) (hyK : y ∉ K)
    (hXI : GGResXDatumAIndep p Bs K (N - 1)) : False := by
  classical
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hyD : y ∈ D := by
    rw [hH.2.2.2.2.1.2.1]
    exact Subgroup.subset_closure (by simp)
  have hy : y ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hyD)
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hH.2.2.2.2.1.1.2.2.2.1
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
  have hy1 : y ≠ 1 := ggRC_y_ne_one hH
  have hfixy : ∀ φ ∈ ggAutomizer K Bs, φ (⟨y, hy⟩ : ↥Bs) = ⟨y, hy⟩ :=
    ggHLA_fixes_x hKy hy
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
  have hfixK : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer K Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers y := by
    intro b hb
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
  obtain ⟨Λ, iΛ, iΛdec, MK, CK, VK, iVKadd, iVKmod, ιK, φK, hK, αK, e,
      hMK, hweyl, hCK, hφK, hrefl, hpairK, hAut, hAK, hLI⟩ := hXI
  letI := iVKadd
  letI := iVKmod
  exact ggXDatumA_dep_K hp2 hH hy hyK hfixK hN5 hpN e hMK hCK hφK hpairK hAK hLI

end CFSG.StandardType

end
