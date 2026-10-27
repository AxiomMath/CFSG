module

public import CFSG.LocalAnalysis.StandardType.GGResIFixJ
public import CFSG.LocalAnalysis.StandardType.GGResILineInputs
public import CFSG.LocalAnalysis.StandardType.GGResIQEight

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ComponentClassification Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggDichotomy_step (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hInn : GGInnerDiagAll p B Bs x L D J) {t : MulAut ↥Bs}
    {Jt : Subgroup G} (hind : t ∈ ggInduced Jt Bs)
    (hJC : Jt ≤ Subgroup.centralizer (ggFixG Bs t : Set G))
    (hpc : IsPComponent p (Jt.subgroupOf (Subgroup.centralizer (ggFixG Bs t : Set G))))
    {d : G} {X : Subgroup G} (hd1 : d ≠ 1) (hdE : d ∈ ggFixG Bs t)
    (hX : LargeEvenPComponent p (Subgroup.centralizer ({d} : Set G)) X) (hJX : J ≤ X) :
    Jt ≤ X ∨ ∀ a ∈ ggInduced J Bs, t * a = a * t := by
  obtain ⟨hI, hBsB, hDJ⟩ := hcfg
  have hsimple : IsSimpleGroup G := hI.1
  have hnab : ∃ a b : G, a * b ≠ b * a := hI.2.1
  have hKP : KProper InCatalog G := hI.2.2.1
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hBsabel : IsElemAbelian p Bs := hBsB.2.1
  have hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBsabel.1.is_comm.comm (⟨a, ha⟩ : ↥Bs) ⟨b, hb⟩)
  have hexp : ∀ b ∈ Bs, b ^ p = 1 := hBsabel.2
  have hpJ : p ∣ Nat.card J := hP G p B x L D J hI hDJ
  have hJJ : ⁅J, J⁆ = J :=
    commutator_self_eq_of_isQuasisimple hDJ.1.2.2.2.2.2.1.2.2
  have hBsL : Bs ≤ normalizer (L : Set G) := GGDichotomy.le_normalizer_of_innerDiagOn hInn.1
  have hBsJ : Bs ≤ normalizer (J : Set G) :=
    GGDichotomy.le_normalizer_stdSub hcomm hBsB.1 hDJ.1 hBsL
  have hEBs : ggFixG Bs t ≤ Bs := Subgroup.map_subtype_le _
  have hT : CFSG.Open.lBalanceIsPComponent p (centralizer (ggFixG Bs t : Set G)) Jt :=
    (CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance p _ Jt hJC).mp hpc
  have hKGroup : CFSG.Open.lBalanceIsKGroup ↥(centralizer ({d} : Set G)) :=
    lBalanceIsKGroup_of_kProper hKP (centralizer_singleton_ne_top_of_isSimpleGroup hnab hd1)
  have hBsd : Bs ≤ centralizer ({d} : Set G) := fun b hb =>
    mem_centralizer_singleton_iff.mpr (hcomm b hb d (hEBs hdE))
  have hBsX := GGDichotomy.le_normalizer_of_pComponent hBsd hX hJX hJJ hpJ hBsJ
  rcases GGDichotomy.dichotomy_core hL hp hcomm hexp hEBs hdE hKGroup hBsX
      ((largeEvenPComponent_iff_lBalance p _ X).1 hX).2 hT with h | h
  · exact Or.inl h
  · exact Or.inr (GGDichotomy.aut_commute_of_commutator_le hBsd hexp hind hJX h)

theorem ggResI_alpha_eq_zero_of_refl {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    {φ : MulAut ↥Bs} {hv : V} {αv : Module.Dual (ZMod p) V}
    (hφ : ∀ w, ggLin (p := p) ι φ w = w - αv w • hv) (hr : GGIsReflection p φ) {w : V}
    (hfix : ggLin (p := p) ι φ w = w) : αv w = 0 := by
  have hh0 : hv ≠ 0 := by
    intro h0
    have hid : φ = 1 := by
      apply ggLin_injective (p := p) ι
      ext w'
      rw [hφ, h0, smul_zero, sub_zero, map_one]
      rfl
    obtain ⟨-, hc⟩ := hr
    rw [hid] at hc
    simp only [MulAut.one_apply] at hc
    have hpos : 0 < Nat.card ↥Bs := Nat.card_pos
    have hc' : Nat.card {b : ↥Bs // True} * p = Nat.card ↥Bs := by simpa using hc
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)] at hc'
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    nlinarith
  rw [hφ, sub_eq_self] at hfix
  exact (smul_eq_zero.mp hfix).resolve_right hh0

theorem ggResI_vert_fix {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {x d : G} {X : Subgroup G} (hxBs : x ∈ Bs) (hexp : ∀ c ∈ Bs, c ^ p = 1)
    (hXpc : LargeEvenPComponent p (Subgroup.centralizer ({d} : Set G)) X)
    (hV : (⁅X, Subgroup.zpowers x⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p X)
    {t : MulAut ↥Bs} {Jt : Subgroup G} (hind : t ∈ ggInduced Jt Bs) (hJtX : Jt ≤ X) :
    x ∈ ggFixG Bs t := by
  obtain ⟨n, hnJt, hnN, hn⟩ := hind
  have hsub : IsSubnormal X (Subgroup.centralizer ({d} : Set G)) :=
    (AssemblyBPredicates.isSubnormal_iff_open _ _).2
      ((largeEvenPComponent_iff_lBalance p _ _).1 hXpc).2.1
  have hO : n * x * n⁻¹ * x⁻¹ ∈
      CFSG.Open.lBalancePrimeCore p (Subgroup.centralizer ({d} : Set G)) :=
    largeEvenPPrimeCoreOf_le_of_isSubnormal hsub
      (hV (Subgroup.commutator_mem_commutator (hJtX hnJt) (Subgroup.mem_zpowers x)))
  have hBs' : n * x * n⁻¹ * x⁻¹ ∈ Bs := by
    have h1 : n * x * n⁻¹ ∈ Bs := (mem_normalizer_iff.mp hnN x).mp hxBs
    exact Bs.mul_mem h1 (Bs.inv_mem hxBs)
  have hnx : n * x * n⁻¹ * x⁻¹ = 1 :=
    GGDichotomy.eq_one_of_mem_of_coprime (LBalance.primeCore_coprime p _) hO (hexp _ hBs')
  exact GGDichotomy.mem_ggFixG_of_induced hxBs hn (mul_inv_eq_one.mp hnx)

theorem ggResI_line_exit (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput)
    (hReal : GGReflRealizedQFourInputThree) (hPL : GGPumpLineThreeInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hp3 : p = 3)
    (hq : ¬ GGInnerDiagOnLabel GGLabQTwo p Bs L)
    (hLD : GGResLeviDatum p Bs L J K ggSelI (ggTypRankLt 8))
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ} {CL : Matrix Λ Λ ℤ} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] [Finite V] (ι : Additive ↥Bs ≃+ V)
    {φ : Option Λ → MulAut ↥Bs} {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hr : ∀ o, GGIsReflection p (φ o))
    (hL : ∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod p))
    (hspan : Submodule.span (ZMod p) (Set.range h) = ⊤) (hind : LinearIndependent (ZMod p) h)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none}))
    (hJ : ggAutomizer J Bs = Subgroup.closure (Set.range fun j : {j : Λ // j ≠ b} => φ (some j)))
    (allA : Prop) (hallA : allA → GGInnerDiagOnLabel GGLabQFour p Bs K)
    (hcert : GGResILineCert p b CL (fun o => ggLin (p := p) ι (φ o)) α allA) : False := by
  classical
  obtain ⟨T, e, hcart, hindJ, z, w, F, S, hzJ, hwJ, hzL, hF, hFmem, hSle, hbad⟩ := hcert
  have hp : p.Prime := Fact.out
  obtain ⟨-, hBsE, hxBs, hLx, -⟩ := hH.1.tableB_facts
  have hexp : ∀ c ∈ Bs, c ^ p = 1 := hBsE.2
  have hdim := ggResI_finrank hspan hind
  obtain ⟨hDfix, hI1⟩ := ggResI_fixJ_le_D hH ι hφ (fun j _ => hr (some j)) hdim hJ hindJ
  have hαx : ∀ i : Λ, α (some i) (ι (Additive.ofMul ⟨x, hxBs⟩)) = 0 := fun i =>
    ggResI_alpha_eq_zero_of_refl ι (hφ (some i)) (hr (some i))
      ((ggLin_fix_iff (p := p) ι _ _).mp (ggResI_automizer_fix hxBs hLx (φ (some i))
        (hAL ▸ Subgroup.subset_closure ⟨i, rfl⟩)))
  set dB : ↥Bs := Additive.toMul (ι.symm z) with hdB
  have hιd : ι (Additive.ofMul dB) = z := by simp [hdB]
  set wB : ↥Bs := Additive.toMul (ι.symm w) with hwB
  have hιw : ι (Additive.ofMul wB) = w := by simp [hwB]
  have hdD : (dB : G) ∈ D := hDfix dB fun j hj => by rw [hιd]; exact hzJ j hj
  have hwD : (wB : G) ∈ D := hDfix wB fun j hj => by rw [hιw]; exact hwJ j hj
  have hdx : (dB : G) ∉ Subgroup.zpowers x := by
    intro hdx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hdx
    have hbk : dB = (⟨x, hxBs⟩ : ↥Bs) ^ k := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
    obtain ⟨i, hi⟩ := hzL
    apply hi
    rw [← hιd, hbk, ofMul_zpow, map_zsmul, map_zsmul, hαx i, smul_zero]
  have hd1 : (dB : G) ≠ 1 := fun h1 => hdx (h1 ▸ Subgroup.one_mem _)
  have hD : D = Subgroup.closure {x, (dB : G)} := eq_closure_pair_of_mem hH.1.1 hH.1.2.2 hdD hdx
  have hpJ : p ∣ Nat.card J := hSP G p B x L D J hH.1.1 hH.1.2.2
  obtain ⟨hXpc, hJX, -, hNV⟩ :=
    pumpup_of_stdSub (ggPumpupInput_of_lBalance hLB) hH.1.1 hH.1.2.2 hpJ hD
  set X := ggLayerClosure p (Subgroup.centralizer ({(dB : G)} : Set G)) J with hX
  have hmemb : ∀ ψo ∈ F, ∃ t : MulAut ↥Bs,
      ggLin (p := p) ι t = ψo.1 * ggLin (p := p) ι (φ ψo.2) * ψo.1⁻¹ ∧
      ∃ Jt : Subgroup G, t ∈ ggInduced Jt Bs ∧ Jt ≤ X ∧ x ∉ ggFixG Bs t := by
    intro ψo hψo
    obtain ⟨hA, hψ, hz0, hw0, j, hjb, hjc⟩ := hFmem ψo hψo
    rw [← ggResI_map_sup ι (ggResI_sup_eq_closure hAL hAK)] at hψ
    obtain ⟨ψ₀, hψ₀, hψ₀e⟩ := Subgroup.mem_map.mp hψ
    have hψ₀top : ψ₀ ∈ ggAutomizer ⊤ Bs := Subgroup.subset_closure (ggResI_mem_ggInduced_top hψ₀)
    obtain ⟨n₀, -, hn₀, hψ₀n⟩ := eq_ggConjAut_of_mem_ggAutomizer hψ₀top
    have hR : GGRealized p Bs (φ ψo.2) := by
      rcases ho : ψo.2 with _ | i
      · have hAa : allA := hA.resolve_right fun hne => hne ho
        have hRK : GGReflRealizedIn p Bs K := hReal G p B Bs x L D J hH.1 hH.2.2.1 hH.2.2.2.1 hp3 K
          (Or.inr ⟨y, hH.2.2.2.2.1⟩) (hallA hAa)
        exact ggRealized_of_reflRealizedIn hp (hH.1.2.1.1 hH.2.2.2.2.1.1.2.1)
          ((CFSG.Assembly.LargeEven.largeEvenPComponent_iff_glaPComponent p _ K).mp
            hH.2.2.2.2.1.1.2.2.2.2.1) hRK (hAK ▸ Subgroup.subset_closure (Or.inr rfl)) (hr none)
      · have hRL : GGReflRealizedIn p Bs L := hReal G p B Bs x L D J hH.1 hH.2.2.1 hH.2.2.2.1 hp3 L
          (Or.inl rfl) (ggResI_qFour_L hH.2.2.1.1 hq)
        exact ggRealized_of_reflRealizedIn_L hSP hH.1 hRL
          (hAL ▸ Subgroup.subset_closure ⟨i, rfl⟩) (hr (some i))
    set t : MulAut ↥Bs := ψ₀ * φ ψo.2 * ψ₀⁻¹ with ht
    have htR : GGRealized p Bs t := by
      rw [ht, hψ₀n]
      exact hR.conj hp hn₀
    have htlin : ggLin (p := p) ι t = ψo.1 * ggLin (p := p) ι (φ ψo.2) * ψo.1⁻¹ := by
      rw [ht, map_mul, map_mul, map_inv, hψ₀e]
    have hdE : (dB : G) ∈ ggFixG Bs t := by
      refine ⟨dB, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_ggFix, ggLin_fix_iff (p := p) ι, hιd, htlin,
        LinearEquiv.mul_apply, LinearEquiv.mul_apply, hφ, hz0, zero_smul, sub_zero,
        LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
    have hxE : x ∉ ggFixG Bs t := by
      intro hxE
      have hDE : D ≤ ggFixG Bs t := by
        rw [hD, Subgroup.closure_le]
        rintro c (rfl | rfl)
        · exact hxE
        · exact hdE
      obtain ⟨c, hc, hcw⟩ := Subgroup.mem_map.mp (hDE hwD)
      have hcw' : c = wB := Subtype.ext hcw
      rw [hcw', mem_ggFix, ggLin_fix_iff (p := p) ι, hιw, htlin,
        LinearEquiv.mul_apply, LinearEquiv.mul_apply] at hc
      have hfixu : ggLin (p := p) ι (φ ψo.2) (ψo.1⁻¹ w) = ψo.1⁻¹ w :=
        ψo.1.injective (by rw [hc, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply])
      exact hw0 (ggResI_alpha_eq_zero_of_refl ι (hφ ψo.2) (hr ψo.2) hfixu)
    obtain ⟨Jt, hindt, hJC, hpc⟩ := htR
    rcases ggDichotomy_step hLB hSP hH.1 hH.2.2.1 hindt hJC hpc hd1 hdE hXpc hJX with hJtX | hcomm
    · exact ⟨t, htlin, Jt, hindt, hJtX, hxE⟩
    · exfalso
      apply hjc
      have hjJ : φ (some j) ∈ ggInduced J Bs :=
        mem_ggAutomizer_iff.mp (hJ ▸ Subgroup.subset_closure ⟨⟨j, hjb⟩, rfl⟩)
      have hc : ggLin (p := p) ι t * ggLin (p := p) ι (φ (some j)) =
          ggLin (p := p) ι (φ (some j)) * ggLin (p := p) ι t := by
        rw [← map_mul, ← map_mul, hcomm _ hjJ]
      rw [htlin] at hc
      exact hc
  obtain ⟨ψo₀, hψo₀⟩ := List.exists_mem_of_ne_nil F hF
  rcases hNV with hN | hV
  ·
    have hAJX : ggAutomizer J Bs ≤ ggAutomizer X Bs :=
      Subgroup.closure_mono fun φ' ⟨g, hgJ, hgN, hg⟩ => ⟨g, hJX hgJ, hgN, hg⟩
    have hSX : S ≤ (ggAutomizer X Bs).map (ggLin (p := p) ι) := by
      refine hSle.trans ((Subgroup.closure_le _).mpr ?_)
      rintro u (⟨ψo, hψo, rfl⟩ | ⟨j, hjb, rfl⟩)
      · obtain ⟨t, htlin, Jt, ⟨g, hgJt, hgN, hg⟩, hJtX, -⟩ := hmemb ψo hψo
        exact ⟨t, Subgroup.subset_closure ⟨g, hJtX hgJt, hgN, hg⟩, htlin⟩
      · exact ⟨φ (some j), hAJX (hJ ▸ Subgroup.subset_closure ⟨⟨j, hjb⟩, rfl⟩), rfl⟩
    have hdvd : T.bad ∣ Nat.card (ggAutomizer X Bs) := by
      refine hbad.trans ?_
      rw [← Subgroup.card_map_of_injective (ggLin_injective (p := p) ι)]
      exact Subgroup.card_dvd_of_le hSX
    have hJD : GGResLineJDatum p Bs J T := by
      refine ⟨V, inferInstance, inferInstance, ι, fun k => φ (some (e k).1),
        fun k => h (some (e k).1), fun k => α (some (e k).1), fun k w => hφ _ w, fun k => hr _,
        fun i j => by rw [hL, hcart],
        hind.comp _ fun a c hac => e.injective (Subtype.ext (Option.some_injective _ hac)), ?_⟩
      rw [hJ]
      congr 1
      ext u
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨e.symm j, by simp⟩
      · rintro ⟨k, rfl⟩
        exact ⟨e k, rfl⟩
    have hcardBs : Nat.card ↥Bs = p ^ (T.rank + 2) := by
      have hcard : Nat.card ↥Bs = Nat.card V := Nat.card_congr (Additive.ofMul.trans ι.toEquiv)
      have hV := FiniteField.pow_finrank_eq_natCard p V
      have hcardΛ : Fintype.card Λ = T.rank + 1 := by
        rw [← Fintype.card_congr (Equiv.optionSubtypeNe b), Fintype.card_option,
          ← Fintype.card_congr e, Fintype.card_fin]
      rw [hcard, ← hV, hdim, hcardΛ]
    exact hPL G p B Bs x L D J y K hH hp3 hLD T hJD hcardBs hI1 (dB : G) X hN hJX hdvd
  ·
    obtain ⟨t, -, Jt, hindt, hJtX, hxE⟩ := hmemb ψo₀ hψo₀
    exact hxE (ggResI_vert_fix hxBs hexp hXpc hV hindt hJtX)

end CFSG.StandardType
