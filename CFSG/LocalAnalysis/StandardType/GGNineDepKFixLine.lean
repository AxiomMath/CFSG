module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeNineDepTwoRestDefs
public import CFSG.LocalAnalysis.StandardType.GGNineDepLin
public import CFSG.LocalAnalysis.StandardType.GGNineDepEightNodes
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeFrameShared
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeKFixLineDefs
public import CFSG.LocalAnalysis.StandardType.GGResCentBound
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepLarge
public import CFSG.LocalAnalysis.StandardType.GGHLAutomizer
public import CFSG.LocalAnalysis.StandardType.GGRowKFrame
public import CFSG.LocalAnalysis.StandardType.GGSmallDepDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggSmallDepFixLineAt_three_nine (hD : GGNineDepFixLineLin) :
    @GGSmallDepFixLineAt 3 9 ⟨by norm_num⟩ := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  intro V _ _ h α r T s x hlin hdep hstab hweyl
  refine hD V h α r T s x
    ⟨hlin.p_ne_two, by norm_num, hlin.p_dvd, hlin.dim_le, hlin.pair, hlin.refl_form, hlin.finT,
      hlin.s_refl, hlin.conn, hlin.x_ne, hlin.fix_s, hlin.x_not_fix, hlin.no_transv⟩
    hdep ?_ hweyl
  have h612 : 6 * (3 - 1) = (12 : ℕ) := by norm_num
  simpa only [h612] using hstab

theorem ggTwoNodeDepKFixLine_of_lin (hI : GGIndepFixLineLin) (hFix : GGTBFixInput)
    (hWA : GGTBFixNbrXInput) (hDim : GGTwoNodeRowDimKnown) (hLNC : GGLNoncyclicInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} {N : ℕ} (hD : GGSmallDepFixLineAt p N)
    (hH : GGResHyp p B Bs x L D J y K)
    (hrow : GGResRowAt (fun p labJ labK => ggRowTwoNode p labJ labK ∧ labK.rank + 1 = N) p J K)
    (hp2 : p ≠ 2) (hN5 : 5 ≤ N) (hpN : p ∣ N)
    (hKs : GGResTwoNodeSideDatum p Bs K J) (hLs : GGResTwoNodeSideDatum p Bs L J)
    (hXd : GGResXDatumA p Bs K (N - 1)) (b : ↥Bs) (hb : ∀ φ ∈ ggAutomizer K Bs, φ b = b) :
    (b : G) ∈ Subgroup.zpowers y := by
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
  have hLd : GGResXDatum p Bs L := ggNine_xdatum_of_side hLs
  have hL8 := ggTwoNode_L_weyl hp2 hH.1.2.1.2.1 hN5 hXd hKs hLs
  obtain ⟨V, iVadd, iVmod, ι, h, α, r, T, iT, s, hdim, hpair, hr, hclosK, hs, hconn, hsclos,
      hfixs, hx0, hxnot, hnt, -⟩ :=
    ggTwoNodeFrame_of_datums hFix hWA hDim hH hrow hp2 hN5 hpN hXd hLd hx
  letI := iVadd
  letI := iVmod
  letI := iT
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let F : Submodule (ZMod p) V := ggLinFix (Set.range r)
  let xV : V := ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))
  let vy : V := ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))
  have hstab : Nat.card ↥(ggLargeGrp r s ⊓ MulAction.stabilizer (V ≃ₗ[ZMod p] V) xV) ≤
      6 * (p - 1) * Nat.card ↥(Subgroup.closure (Set.range s)) := by
    have hjoin : ggLargeGrp r s =
        (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := p) ι) := by
      show Subgroup.closure (Set.range r ∪ Set.range s) = _
      rw [Subgroup.closure_union, hclosK, hsclos, ← Subgroup.map_sup, sup_comm]
    have hmapStab : ((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
        MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs)).map (ggLin (p := p) ι) =
        ggLargeGrp r s ⊓ MulAction.stabilizer (V ≃ₗ[ZMod p] V) xV := by
      rw [hjoin]
      ext g
      simp only [Subgroup.mem_map, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
      constructor
      · rintro ⟨ψ, ⟨hψA, hψs⟩, rfl⟩
        exact ⟨⟨ψ, hψA, rfl⟩, (ggLin_fix_iff (p := p) ι ψ ⟨x, hx⟩).mp hψs⟩
      · rintro ⟨⟨ψ, hψA, rfl⟩, hs'⟩
        exact ⟨ψ, ⟨hψA, (ggLin_fix_iff (p := p) ι ψ ⟨x, hx⟩).mpr hs'⟩, rfl⟩
    have hbound := ggResCentBound_of_xDatum hLNC hFix hH hx hLd
    have hcardL : Nat.card ↥(Subgroup.closure (Set.range s)) =
        Nat.card ↥(ggAutomizer L Bs) := by
      rw [hsclos]
      exact (Nat.card_congr (Subgroup.equivMapOfInjective _ (ggLin (p := p) ι)
        (ggLin_injective ι)).toEquiv).symm
    rw [← hmapStab, hcardL]
    calc Nat.card ↥(((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
          MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs)).map (ggLin (p := p) ι))
        = Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
            MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs)) :=
          (Nat.card_congr (Subgroup.equivMapOfInjective _ (ggLin (p := p) ι)
            (ggLin_injective ι)).toEquiv).symm
      _ ≤ (p - 1) * 6 * Nat.card ↥(ggAutomizer L Bs) := hbound
      _ = 6 * (p - 1) * Nat.card ↥(ggAutomizer L Bs) := by
          rw [Nat.mul_comm (p - 1) 6]
  have hweylL : ∃ M : CoxeterMatrix (Fin (N - 1)), GGIsWeylMatrix M ∧
      Nonempty (M.Group ≃* ↥(Subgroup.closure (Set.range s))) := by
    obtain ⟨M8, hW8, ⟨f8⟩⟩ := hL8
    exact ⟨M8, hW8, ⟨f8.trans ((Subgroup.equivMapOfInjective _ (ggLin (p := p) ι)
      (ggLin_injective ι)).trans (MulEquiv.subgroupCongr hsclos.symm))⟩⟩
  have hFle : Module.finrank (ZMod p) F ≤ 1 := by
    by_cases hind : LinearIndependent (ZMod p) h
    · exact (hI p N hp2 hN5 hpN V hdim h α r hind hpair hr T s hs hconn
        xV hx0 hfixs hxnot hnt).le
    · exact hD V h α r T s xV ⟨hp2, hpN, hdim, hpair, hr, iT, hs, hconn,
        hx0, hfixs, hxnot, hnt⟩ hind hstab hweylL
  have hvy_mem : vy ∈ F := by
    intro a ha
    rcases ha with ⟨i, rfl⟩
    have hri : r i ∈ Subgroup.closure (Set.range r) := Subgroup.subset_closure ⟨i, rfl⟩
    rw [hclosK] at hri
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
  have hFfin : Module.finrank (ZMod p) F = 1 :=
    le_antisymm hFle (by
      simpa [finrank_span_singleton hvy0] using Submodule.finrank_mono hspan_le)
  have hFeq : F = Submodule.span (ZMod p) ({vy} : Set V) :=
    (Submodule.eq_of_le_of_finrank_eq hspan_le
      (by rw [finrank_span_singleton hvy0, hFfin])).symm
  have hbF : ι (Additive.ofMul b) ∈ F := by
    intro a ha
    rcases ha with ⟨i, rfl⟩
    have hri : r i ∈ Subgroup.closure (Set.range r) := Subgroup.subset_closure ⟨i, rfl⟩
    rw [hclosK] at hri
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

theorem ggNineDepKFixLine_of_lin (hI : GGIndepFixLineLin) (hD : GGNineDepFixLineLin)
    (hFix : GGTBFixInput) (hWA : GGTBFixNbrXInput) (hDim : GGTwoNodeRowDimKnown)
    (hLNC : GGLNoncyclicInput) (hJ2 : GGTBJTwoNodeInput) : GGNineDepKFixLine := by
  intro G _ _ p _ B Bs x L D J y K hH _ _ _ hrow _ hLs hXd b hb
  classical
  have hp3 : p = 3 := by
    rcases hrow with ⟨-, -, -, -, -, -, -, hp3, -⟩
    exact hp3
  subst hp3
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hrow2 : GGResRowAt ggRowTwoNode 3 J K := by
    obtain ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hr⟩ := hrow
    exact ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hr.1⟩
  have hrow9 : GGResRowAt
      (fun p labJ labK => ggRowTwoNode p labJ labK ∧ labK.rank + 1 = 9) 3 J K := by
    obtain ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hr⟩ := hrow
    have h8 : labX.rank = 8 := hr.2.2
    exact ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hr.1, by omega⟩
  have hKs : GGResTwoNodeSideDatum 3 Bs K J :=
    (hJ2 G 3 B Bs x L D J y K hH).2 (l6a_xdatum_of_A hXd) hrow2
  exact ggTwoNodeDepKFixLine_of_lin hI hFix hWA hDim hLNC (ggSmallDepFixLineAt_three_nine hD)
    hH hrow9 hp2 (by norm_num) (by norm_num) hKs hLs hXd b hb

theorem ggNineDepKFixLine_of_omega (hK : GGReflClassOmegaInput) (hI : GGIndepFixLineLin)
    (hFix : GGTBFixInput) (hWA : GGTBFixNbrXInput) (hDim : GGTwoNodeRowDimKnown)
    (hLNC : GGLNoncyclicInput) (hJ2 : GGTBJTwoNodeInput) (hK2 : GGNineDepRowLinInput)
    (hK3 : GGNineDepRowImprimInput) (hK4a : GGNineDepRowSymSuccInput)
    (hK4b : GGNineDepRowSymSuccTwoInput) (hK5a : GGNineDepRowE7Input)
    (hK5b : GGNineDepRowE8Input) (hK6 : GGNineDepRowOrthInput) : GGNineDepKFixLine :=
  ggNineDepKFixLine_of_lin hI
    (ggNineDepFixLineLin_of_omega hK hK2 hK3 hK4a hK4b hK5a hK5b hK6) hFix hWA hDim hLNC hJ2

end CFSG.StandardType

end
