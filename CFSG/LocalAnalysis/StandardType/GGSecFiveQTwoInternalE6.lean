module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveQTwoInternal
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSix
public import CFSG.LocalAnalysis.StandardType.GGTBRowUCartan
public import CFSG.LocalAnalysis.StandardType.GGTBRowDCartan
public import CFSG.LocalAnalysis.StandardType.GGPZCartanRank
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBWeylInfType
public import CFSG.LocalAnalysis.StandardType.GGRCWeylCard
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthWeylOrdD
public import CFSG.LocalAnalysis.StandardType.GGSpJoinCoxeterCard
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoEnd
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoEndExc
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaMinusEnd
public import CFSG.LocalAnalysis.StandardType.GGAutomizerJoinInduced

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open Module

variable {G : Type} [Group G] [Finite G]

theorem GGSecFiveRestHyp.mem_sup_of_twA5_of_card_six
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hR : GGSecFiveRestHyp 3 B Bs x L D J)
    {y : G} {K : Subgroup G} (hN : GGNbr 3 B x D J y K)
    (hWeyl : GGWeylOfType 3 CoxeterMatrix.E₆ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hlab : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) 3 Bs L)
    (hcard : Nat.card Bs = 3 ^ 6) : x ∈ L ⊔ K := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcfg : GGConfig 3 B Bs x L D J := hR.1
  have hNT : GGNoTransvection 3 Bs := hR.2.2.2.1
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  obtain ⟨-, hBs, hxB, hLx, -⟩ := hcfg.tableB_facts
  have hx1 : x ≠ 1 := hS.2.2.1
  have hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hcyc : ∀ S : Subgroup G, IsPGroup 3 S → S ≤ Subgroup.centralizer (L : Set G) →
      IsCyclic S := fun S hSp hSL => hcfg.1.2.2.2.2.2.2.1.2.2.2.2 S hSL hSp
  have hKn : Bs ≤ Subgroup.normalizer (K : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn (hR.2.2.1.2 y K hN)
  obtain ⟨hperf, F, _, _, θ, hF4, hBsN, hI⟩ := exists_unitaryDatum_of_innerDiagOnLabel_twA5 hlab
  have hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    inf_centralizer_eq_zpowers_of_elemAbelian Nat.prime_three hBs hxB hx1 hLx
      (fun S hSL hSp => hcyc S hSp hSL)
  let M : Subgroup G := L ⊔ Subgroup.centralizer (L : Set G)
  have hLM : L ≤ M := le_sup_left
  have hcardBin : Nat.card ↥(Bs ⊓ M) = 3 ^ 5 :=
    E6QTwo.card_inf_sup_centralizer_of_card_six hF4 θ hperf hBs hcard hxB hBL hBsN hI
  have hxM : x ∈ M := by
    refine Subgroup.mem_sup_right (Subgroup.mem_centralizer_iff.mpr fun l hl => ?_)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
  obtain ⟨V, hVadd, hVmod, ⟨ι⟩⟩ := exists_ggLinData (p := 3) hBs
  let : AddCommGroup V := hVadd
  let : Module (ZMod 3) V := hVmod
  have hVcard : Nat.card V = 3 ^ 6 := by
    rw [← card_eq_of_ggLin ι]
    exact hcard
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [hVcard]; norm_num)
  let A₀ : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs ⊔ ggAutomizer K Bs
  have hA : ∀ ψ ∈ A₀, ψ ∈ ggInduced ⊤ Bs := fun ψ hψ =>
    mem_ggInduced_top_of_mem_ggAutomizer
      (sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hψ)
  obtain ⟨e, cr, α, hα, he, hP⟩ := E6QTwo.exists_cartan_pairing_E6 hNT hWeyl hA ι
  have hmapA : A₀.map (ggLin (p := 3) ι) = E6QTwo.e6Weyl hα :=
    E6QTwo.map_ggLin_eq_e6Weyl ι e hα he
  have hWcard : Nat.card (E6QTwo.e6Weyl hα) = 51840 := by
    rw [E6QTwo.card_e6Weyl_eq ι e hα he]
    rw [show Nat.card A₀ = Nat.card (CoxeterMatrix.E₆).Group from
      (Nat.card_congr e.toEquiv).symm, card_coxeterE6_group]
  let vx : V := ι (Additive.ofMul (⟨x, hxB⟩ : ↥Bs))
  have hvx : vx ≠ 0 := by
    intro h0
    have h1 : Additive.ofMul (⟨x, hxB⟩ : ↥Bs) = 0 := ι.injective (by rw [map_zero]; exact h0)
    have h2 : (⟨x, hxB⟩ : ↥Bs) = 1 := by
      simpa using congrArg Additive.toMul h1
    exact hx1 (by simpa using congrArg Subtype.val h2)
  have hspanx : (ZMod 3) ∙ vx = ggLinImage ι (Subgroup.zpowers x) :=
    span_singleton_eq_ggLinImage ι hxB
  have hHcard : Nat.card (ggLinImage (p := 3) ι M) = 3 ^ 5 := by
    rw [card_ggLinImage]
    exact hcardBin
  have hxH : vx ∈ ggLinImage (p := 3) ι M := (ofMul_mem_ggLinImage ι M _).mpr hxM
  have hAle : (ggAutomizer L Bs).map (ggLin (p := 3) ι) ≤ E6QTwo.e6Weyl hα := by
    rw [← hmapA]
    exact Subgroup.map_mono le_sup_left
  have hcardA : 720 ≤ Nat.card ((ggAutomizer L Bs).map (ggLin (p := 3) ι)) := by
    rw [Subgroup.card_map_of_injective (ggLin_injective ι)]
    exact E6QTwo.le_card_ggAutomizer_of_card_six hF4 θ hperf hBs hcard hxB hx1 hBL hstar hBsN hI
      hLx
  have hfixAL : ∀ ψ ∈ ggAutomizer L Bs, ψ ⟨x, hxB⟩ = ⟨x, hxB⟩ := fun ψ hψ =>
    ggAutomizer_apply_eq_of_le_centralizer hLx hψ
  have hAx : ∀ g ∈ (ggAutomizer L Bs).map (ggLin (p := 3) ι), g vx = vx := by
    rintro _ ⟨ψ, hψ, rfl⟩
    show ggLin (p := 3) ι ψ (ι (Additive.ofMul (⟨x, hxB⟩ : ↥Bs))) = _
    rw [ggLin_apply_ofMul, hfixAL ψ hψ]
  have hAH : ∀ g ∈ (ggAutomizer L Bs).map (ggLin (p := 3) ι), ∀ v,
      g v - v ∈ ggLinImage (p := 3) ι M := by
    rintro _ ⟨ψ, hψ, rfl⟩ v
    obtain ⟨l, hlL, -, hlψ⟩ := mem_ggAutomizer_iff.mp hψ
    obtain ⟨b, rfl⟩ : ∃ b : ↥Bs, ι (Additive.ofMul b) = v :=
      ⟨Additive.toMul (ι.symm v), by simp⟩
    rw [ggLin_apply_ofMul_sub, ofMul_mem_ggLinImage]
    have hbl : (b : G) * l⁻¹ * (b : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hBsN b.2) l⁻¹).mp (L.inv_mem hlL)
    have heq : ((ψ b * b⁻¹ : ↥Bs) : G) = l * ((b : G) * l⁻¹ * (b : G)⁻¹) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hlψ b]
      group
    rw [heq]
    exact hLM (L.mul_mem hlL hbl)
  have hfix : ∀ v, (∀ g ∈ (ggAutomizer L Bs).map (ggLin (p := 3) ι),
      g v - v ∈ (ZMod 3) ∙ vx) → v ∈ (ZMod 3) ∙ vx := by
    intro v hv
    obtain ⟨b, rfl⟩ : ∃ b : ↥Bs, ι (Additive.ofMul b) = v :=
      ⟨Additive.toMul (ι.symm v), by simp⟩
    rw [hspanx, ofMul_mem_ggLinImage]
    refine E6QTwo.mem_zpowers_of_forall_conj_of_card_six hF4 θ hperf hBs hcard hxB hx1 hBL hstar
      hBsN hI hLx b.2 ?_
    intro l hlL hlN
    have h1 := hv _ (Subgroup.mem_map_of_mem _ (ggConjAut_mem_ggAutomizer hlL hlN))
    rw [ggLin_apply_ofMul_sub, hspanx, ofMul_mem_ggLinImage] at h1
    exact h1
  have hspan : Submodule.span (ZMod 3) (Set.range cr) = ggLinImage (p := 3) ι M :=
    E6QTwo.span_range_eq_of_card_six hP hα hVcard hWcard hAle hcardA hvx hAx hHcard hxH hAH hfix
  have hcr : ∀ i, cr i ∈ ggLinImage (p := 3) ι (L ⊔ K) := fun i =>
    (mem_ggLinImage ι (L ⊔ K) (cr i)).mpr (coroot_mem_of_reflection (by norm_num) ι
      (fun b => mul_inv_mem_sup_of_mem_sup_ggAutomizer hBsN hKn (e (CoxeterMatrix.E₆.simple i)).2 b)
      (hα i) (he i))
  have hle : Submodule.span (ZMod 3) (Set.range cr) ≤ ggLinImage (p := 3) ι (L ⊔ K) := by
    rw [Submodule.span_le]
    rintro v ⟨i, rfl⟩
    exact hcr i
  have hvxLK : vx ∈ ggLinImage (p := 3) ι (L ⊔ K) := by
    apply hle
    rw [hspan]
    exact hxH
  exact (ofMul_mem_ggLinImage ι (L ⊔ K) _).mp hvxLK

theorem GGSecFiveRouteCfg.le_card_ggAutomizerJoin_of_weylOfType_E6
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {y : G} {K : Subgroup G}
    (hN : GGNbr p B x D J y K)
    (hW : GGWeylOfType p CoxeterMatrix.E₆ (ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
    51840 ≤ Nat.card (ggAutomizerJoin L Bs 𝒦) := by
  have hjoin : ggAutomizerJoin L Bs {K} = ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    simp [ggAutomizerJoin]
  have hmax := hcfg.2.2.2.2.2 {K} (ggNbrSet_singleton hN)
    (by rw [hjoin]; exact hW.weylReflectionGroup ggIsWeylMatrix_E6)
  rw [hjoin] at hmax
  obtain ⟨e, -⟩ := hW
  rw [← Nat.card_congr e.toEquiv, card_coxeterE6_group] at hmax
  exact hmax

theorem weylOfType_E6_of_pow_five_lt_card {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)}
    (hBs : IsElemAbelian 3 Bs) (hNT : GGNoTransvection 3 Bs) (hA : GGWeylReflectionGroup 3 A)
    (hind : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs) (hfix : ∀ b : ↥Bs, (∀ ψ ∈ A, ψ b = b) → b = 1)
    (h5 : 3 ^ 5 < Nat.card Bs) (h6 : Nat.card Bs ≤ 3 ^ 6)
    (hord : 51840 ≤ Nat.card A ∨ Nat.card A ∣ 51840) :
    GGWeylOfType 3 CoxeterMatrix.E₆ A := by
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have h4 : (4 : ZMod 3) ≠ 0 := by decide
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hlow : ∀ {ι : Type} [Fintype ι] {M : CoxeterMatrix ι}, GGWeylOfType 3 M A →
      6 ≤ Fintype.card ι := by
    intro ι _ M hW
    have h := h5.trans_le (SpJoinRefl.card_le_pow_of_weylOfType hW hfix)
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp h
  have hup : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M : CoxeterMatrix ι} {C : Matrix ι ι ℤ},
      GGIntCartan M C → (∀ i j, M i j ≠ 6) → ∀ (par : ι → ι) (root : ι) (depth : ι → ℕ),
      (∀ i j, i ≠ j → (C i j ≠ 0 ↔ ((i ≠ root ∧ par i = j) ∨ (j ≠ root ∧ par j = i)))) →
      (∀ i, i ≠ root → depth (par i) < depth i) → GGWeylOfType 3 M A →
      (C.map (Int.castRingHom (ZMod 3))).rank ≤ 6 := by
    intro ι _ _ M C hC hno6 par root depth hpar hdepth hW
    have h := pow_rank_le_card_of_cartan_pairing hBs (C := C) fun ιV => by
      obtain ⟨-, h, α, -, -, hP⟩ := SecFiveRootRefl.exists_cartan_pairing_of_weylOfType' hp2 hNT
        hC hno6 par root depth hpar hdepth hW hind ιV
      exact ⟨h, α, hP⟩
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (h.trans h6)
  have hcardW : ∀ {ι : Type} {M : CoxeterMatrix ι}, GGWeylOfType 3 M A →
      Nat.card A = Nat.card M.Group := by
    intro ι M hW
    obtain ⟨e, -⟩ := hW
    exact (Nat.card_congr e.toEquiv).symm
  rcases ggWeylReflectionGroup_cases hA with ⟨n, hn, hW⟩ | ⟨n, hn, hW⟩ |
    ⟨n, hn, hW⟩ | hW | hW | hW | hW | hW
  ·
    exfalso
    have h6 := hlow hW
    rw [Fintype.card_fin] at h6
    obtain ⟨hno6, hpar, hdepth⟩ := ggCartanA_pathTree (k := n) ⟨0, hn⟩ rfl
    have hr := hup (ggIntCartan_A n) hno6 (ggPathPar n) ⟨0, hn⟩ (fun i => i.1) hpar hdepth hW
    have hweyl : GGIsWeylMatrix (CoxeterMatrix.A n) := by
      refine Or.inl ⟨n, Equiv.refl _, hn, Or.inl ?_⟩
      apply CoxeterMatrix.ext
      funext i j
      rw [CoxeterMatrix.reindex_apply]
      rfl
    have hrk := ggIntCartan_card_le_rank_add_one hweyl (ggIntCartan_A n) 3 hp2
    rw [Fintype.card_fin] at hrk
    have h7 : n ≤ 7 := by omega
    rw [hcardW hW, l05nK3a_card_coxeterA n] at hord
    interval_cases n <;> norm_num [Nat.factorial] at hord
  ·
    exfalso
    have h6 := hlow hW
    rw [Fintype.card_fin] at h6
    obtain ⟨hno6, hpar, hdepth⟩ := ggCartanC_pathTree (k := n) ⟨0, by omega⟩ rfl
    have hr := hup (ggIntCartan_C n) hno6 (ggPathPar n) ⟨0, by omega⟩ (fun i => i.1) hpar hdepth
      hW
    rw [rank_eq_card_of_isUnit_det (by
      rw [CartanMatrix.C_det (by omega), Int.cast_ofNat]
      exact isUnit_iff_ne_zero.mpr h2), Fintype.card_fin] at hr
    obtain rfl : n = 6 := by omega
    rw [hcardW hW, ggCoxeterB_card 6 (by norm_num)] at hord
    norm_num [Nat.factorial] at hord
  ·
    exfalso
    have h6 := hlow hW
    rw [Fintype.card_fin] at h6
    obtain ⟨hno6, hpar, hdepth⟩ := ggCartanD_forkTree (k := n) hn ⟨0, by omega⟩ rfl
    have hr := hup (ggIntCartan_D n) hno6 (ggDForkPar n) ⟨0, by omega⟩ (fun i => i.1) hpar hdepth
      hW
    rw [rank_eq_card_of_isUnit_det (by
      rw [CartanMatrix.D_det (by omega), Int.cast_ofNat]
      exact isUnit_iff_ne_zero.mpr h4), Fintype.card_fin] at hr
    obtain rfl : n = 6 := by omega
    rw [hcardW hW, OrthF3.card_coxeterD_eq 6 (by norm_num)] at hord
    norm_num [Nat.factorial] at hord
  · exact hW
  ·
    exfalso
    have hr := hup ggIntCartan_E₇ (by intro i j; fin_cases i <;> fin_cases j <;> decide)
      ![0, 3, 0, 2, 3, 4, 5] 0 ![0, 3, 1, 2, 3, 4, 5]
      (by intro i j hij; fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide)
      (by decide) hW
    rw [rank_eq_card_of_isUnit_det (by
      rw [CartanMatrix.E₇_det, Int.cast_ofNat]
      exact isUnit_iff_ne_zero.mpr h2), Fintype.card_fin] at hr
    omega
  ·
    exfalso
    have hr := hup ggIntCartan_E₈ (by intro i j; fin_cases i <;> fin_cases j <;> decide)
      ![0, 3, 0, 2, 3, 4, 5, 6] 0 ![0, 3, 1, 2, 3, 4, 5, 6]
      (by intro i j hij; fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide)
      (by decide) hW
    rw [rank_eq_card_of_isUnit_det (by
      rw [CartanMatrix.E₈_det, Int.cast_one]
      exact isUnit_one), Fintype.card_fin] at hr
    omega
  · exfalso
    have h6 := hlow hW
    rw [Fintype.card_fin] at h6
    omega
  · exfalso
    have h6 := hlow hW
    rw [Fintype.card_fin] at h6
    omega

theorem GGSecFiveRouteCfg.weylOfType_E6_of_card_six
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hbig : 51840 ≤ Nat.card (ggAutomizerJoin L Bs 𝒦)) (hcard : Nat.card Bs = 3 ^ 6) :
    GGWeylOfType 3 CoxeterMatrix.E₆ (ggAutomizerJoin L Bs 𝒦) :=
  weylOfType_E6_of_pow_five_lt_card hcfg.1.1.2.1.2.1 hcfg.1.2.2.2.1 hcfg.2.2.2.2.1
    (fun φ hφ => ggAutomizerJoin_le_ggInduced_top L 𝒦 hφ)
    (fun b hb => hcfg.eq_one_of_forall_join_fix hTBF hWI b hb) (by rw [hcard]; norm_num) hcard.le
    (Or.inl hbig)

theorem GGSecFiveRouteCfg.weylAt_E6_of_weylOfType_E6
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hW : GGWeylOfType 3 CoxeterMatrix.E₆ (ggAutomizerJoin L Bs 𝒦)) (h5 : 3 ^ 5 < Nat.card Bs) :
    GGSecFiveWeylAt 3 B Bs x L D J CoxeterMatrix.E₆ := by
  have h6 : Nat.card Bs ≤ 3 ^ 6 := by
    simpa using hcfg.card_le_pow_of_weylOfType hTBF hWI le_rfl hW
  obtain ⟨y, K, hN, hsup⟩ := hcfg.exists_nbr_sup_le
  have hdvd : Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) ∣ 51840 := by
    obtain ⟨e, -⟩ := hW
    rw [← card_coxeterE6_group, Nat.card_congr e.toEquiv]
    exact Subgroup.card_dvd_of_le hsup
  exact ⟨y, K, hN, weylOfType_E6_of_pow_five_lt_card hcfg.1.1.2.1.2.1 hcfg.1.2.2.2.1
    (hcfg.1.2.2.2.2.1 y K hN (hcfg.2.1 y K hN) (Or.inr hcfg.2.1))
    (fun φ hφ => ggAutomizerJoin_le_ggInduced_top L 𝒦 (hsup hφ))
    (fun b hb => GGSecFiveRestHyp.eq_one_of_fix_pair hTBF hWI hcfg.1 hcfg.2.1 hN b hb)
    h5 h6 (Or.inr hdvd)⟩

theorem GGSecFiveRouteCfg.card_le_pow_succ_of_weylOfType_L (hTBF : GGTBFixInput)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {ι : Type} [Fintype ι] {M : CoxeterMatrix ι}
    (hWL : GGWeylOfType 3 M (ggAutomizer L Bs)) : Nat.card Bs ≤ 3 ^ (Fintype.card ι + 1) := by
  have hR := hcfg.1
  have hconf : GGConfig 3 B Bs x L D J := hR.1
  have hS : LargeEvenSStar 3 B x L := hconf.1.2.2.2.2.2.2.1
  obtain ⟨-, hBs, hxB, -, -⟩ := hconf.tableB_facts
  have horderx : orderOf x = 3 := orderOf_eq_prime (hBs.2 x hxB) hS.2.2.1
  obtain ⟨y, K, hnbr⟩ := exists_ggNbr hconf.1.2.2.2.2.2.2.2 hconf.2.2
  have hFix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer L Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers x :=
    hTBF G 3 B Bs x L D J hconf hR.2.1 hR.2.2.1 hR.2.2.2.1 y K hnbr (hcfg.2.1 y K hnbr)
      (Or.inr hcfg.2.1)
  let F₀ : Subgroup ↥Bs := (Subgroup.zpowers x).subgroupOf Bs
  have hle := card_le_pow_mul_card_of_weylOfType hWL F₀ fun b hb =>
    Subgroup.mem_subgroupOf.mpr (hFix b hb)
  have hF : Nat.card F₀ ≤ 3 := by
    rw [← horderx, ← Nat.card_zpowers]
    exact Nat.card_le_card_of_injective
      (fun b => (⟨((b : ↥Bs) : G), Subgroup.mem_subgroupOf.mp b.2⟩ : Subgroup.zpowers x))
      fun a b h => by
        have h' := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext h')
  calc Nat.card Bs ≤ 3 ^ Fintype.card ι * Nat.card F₀ := hle
    _ ≤ 3 ^ Fintype.card ι * 3 := Nat.mul_le_mul_left _ hF
    _ = 3 ^ (Fintype.card ι + 1) := by ring

theorem GGSecFiveRouteCfg.exists_weylOfType_of_tbTorRow
    (hW : GGTBTorWRows) (hLift : GGTBTorLiftRows) (hTBF : GGTBFixInput)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    (P : ∀ (_r _m N : ℕ), Matrix (Fin N) (Fin N) ℤ → CoxeterMatrix (Fin N) → Prop)
    (hL : GGInnerDiagOnLabel (fun p lab => ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ)
      (M : CoxeterMatrix (Fin N)), GGTBTorRowAt p lab r m N C M ∧ P r m N C M) 3 Bs L) :
    ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ) (M : CoxeterMatrix (Fin N)), P r m N C M ∧
      GGWeylOfType 3 M (ggAutomizer L Bs) ∧ Nat.card Bs ≤ 3 ^ (N + 1) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR := hcfg.1
  have hconf : GGConfig 3 B Bs x L D J := hR.1
  obtain ⟨-, hBs, -, -, -⟩ := hconf.tableB_facts
  have hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hconf.2.1.2.2.2
  obtain ⟨lab, r, m, N, C, M, R, _instR, θ, I, hN, hperf, hlab, hrow, hP, hBsI, hlift, hT, -⟩ :=
    l05nPlQ_marking_with hW hLift (by norm_num : (3 : ℕ) ≠ 2) P hL
  obtain ⟨hom, hpm, -, hMC⟩ := l05nPlP1_row_facts (p := 3) Nat.prime_three (by norm_num) hlab hrow
  have hTor : GGTorusTorData m N C M ↥L (ggGamma L hN).range :=
    hT ↥L (ggQuotHom θ) (ggGamma L hN).range (ggTorusTBGroup_of_L hconf hperf θ hN hBsI hlift)
  have hWeyl : GGWeylOfType 3 M (ggAutomizer L Bs) :=
    NSJoin.weylOfType_of_torData (by norm_num : (3 : ℕ) ≠ 2) hom hpm hMC hBs hstar hN hTor
  refine ⟨r, m, N, C, M, hP, hWeyl, ?_⟩
  simpa using hcfg.card_le_pow_succ_of_weylOfType_L hTBF hWeyl

theorem ggSecFiveQTwoInternalE6Input_of_inputs
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hW : GGTBTorWRows)
    (hLift : GGTBTorLiftRows) (hFSE : GGSecFiveE6QTwoFS81Input) :
    GGSecFiveQTwoInternalE6Input := by
  intro G _ _ B Bs x L D J 𝒦 hcfg hT1 _ hq y K hN hWp hcard
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR := hcfg.1
  have hconf : GGConfig 3 B Bs x L D J := hR.1
  have hS : LargeEvenSStar 3 B x L := hconf.1.2.2.2.2.2.2.1
  obtain ⟨-, hBs, hxB, hLx, -⟩ := hconf.tableB_facts
  have hx1 : x ≠ 1 := hS.2.2.1
  have hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup 3 S →
      IsCyclic S := fun S hSL hSp => hS.2.2.2.2 S hSL hSp
  have hcardA₀ : Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) = 51840 := by
    obtain ⟨e₀, -⟩ := hWp
    exact (Nat.card_congr e₀.toEquiv).symm.trans card_coxeterE6_group
  have hbig := hcfg.le_card_ggAutomizerJoin_of_weylOfType_E6 hN hWp
  obtain ⟨e, hrefl⟩ := hcfg.weylOfType_E6_of_card_six hTBF hWI hbig hcard
  have hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) CoxeterMatrix.E₆ e :=
    ⟨ggIsWeylMatrix_E6, hrefl⟩
  have hle3 : ∀ i j : Fin 6, i ≠ j → CoxeterMatrix.E₆.M i j ≤ 3 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide
  have hE : GGIsWeylMatrixE CoxeterMatrix.E₆ := by
    refine Or.inl ⟨Equiv.refl _, ?_⟩
    apply CoxeterMatrix.ext
    funext i j
    rw [CoxeterMatrix.reindex_apply]
    rfl
  have hns : ¬ GGSplitLie 3 L := ggSecFive_not_split_of_not_tier1 hcfg hT1 hpres (Or.inr hE)
  obtain ⟨lab₀, hΛ₀, hhas₀, R₀, _, I₀, F₀, θ₀, hP₀⟩ := largeEvenMarking_exists_hasLabel hq
  have hn₀ : lab₀.n = 1 := by
    have h1 : 1 ≤ lab₀.n := hΛ₀.1
    have h2 : lab₀.n < 2 := hP₀.1
    omega
  have hlab : GGInnerDiagOnLabel (fun p lab => lab.n = 1 ∧ (ggRowP_ESU p lab ∨ ggRowP_EOmM p lab ∨
      ggRowP_ETwE6 p lab ∨ (p = 3 ∧ (ggRowP_EOmP p lab ∨ ggRowP_EE7 p lab ∨ ggRowP_EE8 p lab ∨
        ggRowP_NF4 p lab)))) 3 Bs L := by
    refine GGInnerDiagOnLabel.mono_label_of_hasLabel ?_ (ggL_baseLabel_of_nonSplit hcfg hpres hle3 hns)
    intro lab hΛ hhas hrow
    have htag : lab.tag ≠ .A ∧ (lab.tag = .twD → lab.rank ≠ 2) := by
      obtain ⟨t, r, n⟩ := lab
      simp only [ggRowP_ESU, ggRowP_EOmM, ggRowP_ETwE6, ggRowP_EOmP, ggRowP_EE7, ggRowP_EE8,
        ggRowP_NF4] at hrow
      dsimp only at hrow ⊢
      rcases hrow with ⟨⟨rfl, -⟩ | ⟨rfl, rfl⟩, -⟩ | ⟨rfl, h5, -, -⟩ | ⟨rfl, -⟩ |
        ⟨-, -, ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
      all_goals refine ⟨by decide, fun h => ?_⟩
      all_goals first | exact absurd h (by decide) | omega
    have hiso : GGLabelIso lab lab₀ := ggLabelRigidInput_holds lab lab₀ _ hΛ hΛ₀ hhas hhas₀
    have hn : lab.n = 1 := (NSJoin.ggLabelIso_n_eq hiso htag.1 htag.2).trans hn₀
    rcases hrow with h1 | h2 | h3 | ⟨hn', hp3, h4⟩
    · exact ⟨hn, Or.inl h1⟩
    · exact ⟨hn, Or.inr (Or.inl h2)⟩
    · exact ⟨hn, Or.inr (Or.inr (Or.inl h3))⟩
    · exact ⟨hn', Or.inr (Or.inr (Or.inr ⟨hp3, h4⟩))⟩
  have hU : GGInnerDiagOnLabel (fun p lab =>
      (((lab.tag = .twA ∧ lab.rank = 5) ∨ (lab.tag = .D ∧ lab.rank = 4) ∨
          (lab.tag = .twD ∧ lab.rank = 5)) ∧ lab.n = 1) ∨
        (∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ) (M : CoxeterMatrix (Fin N)),
          GGTBTorRowAt p lab r m N C M ∧ (N ≤ 3 ∨ ¬ Nat.card M.Group ∣ 51840)) ∨
        (lab.tag = .twA ∧ lab.rank = 4 ∧ lab.n = 1) ∨ GGF4ThreeLabel p lab ∨
        GGTwE6BadLabel p lab) 3 Bs L := by
    refine GGInnerDiagOnLabel.mono' ?_ hlab
    intro lab hS
    obtain ⟨hn, hrows⟩ := hS
    rcases hrows with h1 | h2 | h3 | ⟨_, h4⟩
    · exact E6QTwo.endLabel_cases hn (Or.inl h1)
    · exact E6QTwo.endLabel_cases hn (Or.inr (Or.inl h2))
    · exact E6QTwo.endLabel_cases hn (Or.inr (Or.inr (Or.inl h3)))
    · exact E6QTwo.endLabel_cases hn (Or.inr (Or.inr (Or.inr h4)))
  have hsmall : ∀ (P : ∀ (_r _m N : ℕ), Matrix (Fin N) (Fin N) ℤ → CoxeterMatrix (Fin N) → Prop),
      (∀ r m N C M, P r m N C M → N ≤ 4) →
      GGInnerDiagOnLabel (fun p lab => ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ)
        (M : CoxeterMatrix (Fin N)), GGTBTorRowAt p lab r m N C M ∧ P r m N C M) 3 Bs L → False := by
    intro P hP hL
    obtain ⟨r, m, N, C, M, hPN, -, hle⟩ := hcfg.exists_weylOfType_of_tbTorRow hW hLift hTBF P hL
    have hN4 := hP r m N C M hPN
    rw [hcard] at hle
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle
    omega
  rcases GGInnerDiagOnLabel.elim_or hU with hA | hBCDE
  ·
    have hA' : GGInnerDiagOnLabel (fun _ lab => (lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) ∨
        (lab.tag = .D ∧ lab.rank = 4 ∧ lab.n = 1) ∨ (lab.tag = .twD ∧ lab.rank = 5 ∧ lab.n = 1))
        3 Bs L := by
      refine GGInnerDiagOnLabel.mono' ?_ hA
      rintro lab ⟨⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩, hn⟩
      · exact Or.inl ⟨h1, h2, hn⟩
      · exact Or.inr (Or.inl ⟨h1, h2, hn⟩)
      · exact Or.inr (Or.inr ⟨h1, h2, hn⟩)
    rcases GGInnerDiagOnLabel.elim_or hA' with h5 | hDE
    · exact hR.mem_sup_of_twA5_of_card_six hN hWp h5 hcard
    rcases GGInnerDiagOnLabel.elim_or hDE with hD4 | hD5
    ·
      refine (hsmall (fun _ _ N _ _ => N = 4) (fun _ _ _ _ _ h => h.le) ?_).elim
      refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) hD4
      obtain ⟨⟨ht, hr, hn⟩, hnorm, hinds⟩ := hP
      obtain ⟨t, r, n⟩ := lab
      simp only at ht hr hn
      subst ht hr hn
      exact ⟨⟨4 - ggTorEnn 3 ⟨.D, 4, 1⟩, ggTorMpm 3 ⟨.D, 4, 1⟩, 4, CartanMatrix.D 4,
        ggCoxeterMatrixD 4, GGTBTorRowAt.d (Or.inl ⟨rfl, Or.inr ⟨by decide, by decide⟩⟩), rfl⟩,
        hnorm, hinds⟩
    ·
      refine (hR.omegaMinusEnd_false' hFSE
        ⟨ggAutomizer L Bs ⊔ ggAutomizer K Bs,
          sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top), hcardA₀⟩
        (GGInnerDiagOnLabel.toMarking hD5)).elim
  rcases GGInnerDiagOnLabel.elim_or hBCDE with hB | hCDE
  ·
    exfalso
    obtain ⟨r, m, N, C, M, hPN, hWL, hle⟩ := hcfg.exists_weylOfType_of_tbTorRow hW hLift hTBF
      (fun _ _ N _ M => N ≤ 3 ∨ ¬ Nat.card M.Group ∣ 51840) hB
    rcases hPN with hN3 | hndvd
    · rw [hcard] at hle
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle
      omega
    · obtain ⟨f, -⟩ := hWL
      refine hndvd ?_
      rw [Nat.card_congr f.toEquiv, ← hcardA₀]
      exact Subgroup.card_dvd_of_le le_sup_left
  rcases GGInnerDiagOnLabel.elim_or hCDE with hC4 | hDE
  ·
    refine (hsmall (fun _ _ N _ _ => N = 4) (fun _ _ _ _ _ h => h.le) ?_).elim
    refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) hC4
    obtain ⟨⟨ht, hr, hn⟩, hnorm, hinds⟩ := hP
    obtain ⟨t, r, n⟩ := lab
    simp only at ht hr hn
    subst ht hr hn
    exact ⟨⟨4 - ggTorEnn 3 ⟨.twA, 4, 1⟩, ggTorM ⟨.twA, 4, 1⟩, 4, CartanMatrix.A 4,
      CoxeterMatrix.A 4, GGTBTorRowAt.aInd (p := 3) (lab := ⟨.twA, 4, 1⟩) (Or.inr rfl)
        (by decide) (by decide), rfl⟩, hnorm, hinds⟩
  rcases GGInnerDiagOnLabel.elim_or hDE with hF4 | hE6b
  ·
    have hM4 : GGF4ThreeMarking Bs L := largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP) hF4
    have hrank : ∀ hN' : Bs ≤ Subgroup.normalizer (L : Set G),
        3 ^ 4 ≤ Nat.card (ggGamma L hN').range := by
      intro hN'
      have hmul := card_range_ggGamma_mul_of Nat.prime_three hBs hxB hx1 hLx hcyc hN'
      rw [hcard] at hmul
      omega
    exact (ggRow_absurd_of_framePair hcfg hpres hle3 le_sup_left
      (ggF4Three_framePair_of_rank hconf hM4 hrank)).elim
  ·
    have hWL : GGWeylOfType 3 CoxeterMatrix.E₆ (ggAutomizer L Bs) :=
      ggTwE6Bad_weylOfType hR hE6b
    obtain ⟨f, -⟩ := hWL
    have hcardL : Nat.card ↥(ggAutomizer L Bs) = 51840 :=
      (Nat.card_congr f.toEquiv).symm.trans card_coxeterE6_group
    have hEq : ggAutomizer L Bs = ggAutomizer L Bs ⊔ ggAutomizer K Bs :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hcardL, hcardA₀])
    have hb : ∀ φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, φ ⟨x, hxB⟩ = ⟨x, hxB⟩ := by
      intro φ hφ
      rw [← hEq] at hφ
      exact ggAutomizer_apply_eq_of_le_centralizer (x := ⟨x, hxB⟩) hLx hφ
    have hb1 := hR.eq_one_of_fix_pair hTBF hWI hcfg.2.1 hN ⟨x, hxB⟩ hb
    exact (hx1 (by simpa using congrArg Subtype.val hb1)).elim

theorem ggSecFiveQTwoInternalInput_of_tbTor
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hW : GGTBTorWRows)
    (hLift : GGTBTorLiftRows) (hFSE : GGSecFiveE6QTwoFS81Input) : GGSecFiveQTwoInternalInput :=
  ggSecFiveQTwoInternalInput_of_e6 hTBF hWI
    (ggSecFiveQTwoInternalE6Input_of_inputs hTBF hWI hW hLift hFSE)

end CFSG.StandardType

end
