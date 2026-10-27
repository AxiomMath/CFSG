module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoUnitaryAux
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoPairing
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoTransfer
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixInner
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixPerm
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixCenter
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixModule
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoOuter
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixAux
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoLocal
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoCoverTwo
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoJoinPreimage
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoNotU12

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem GGSecFiveE6QTwoCfg.card_bstar_eq_or_of_twA5
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGSecFiveE6QTwoCfg 3 B Bs x L D J)
    (hlab : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) 3 Bs L) :
    Nat.card Bs = 3 ^ 5 ∨ Nat.card Bs = 3 ^ 6 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, -, hBs, hxB, hx1, -, hLx, -, hcyc, hNT⟩ := e6QTwo_config_facts hC
  obtain ⟨K', hWeyl⟩ := hC.exists_weylOfType_E6_sup
  obtain ⟨hperf, K, hfieldK, hfiniteK, θ, hK4, hBsN, hI⟩ :=
    exists_unitaryDatum_of_innerDiagOnLabel_twA5 hlab
  have hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    inf_centralizer_eq_zpowers_of_elemAbelian Nat.prime_three hBs hxB hx1 hLx
      (fun S hSL hSp => hcyc S hSp hSL)
  have hA : ∀ ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer K' Bs, ψ ∈ ggInduced ⊤ Bs := by
    intro ψ hψ
    exact mem_ggInduced_top_of_mem_ggAutomizer
      (sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hψ)
  have hge : 3 ^ 5 ≤ Nat.card Bs := E6QTwo.three_pow_five_le_card hBs hNT hA hWeyl
  have hle : Nat.card Bs ≤ 3 ^ 6 :=
    E6QTwo.card_le_three_pow_six_of_twA5 hK4 θ hperf hBs hxB hBL hBsN hI
  obtain ⟨k, hk⟩ := hBs.isPGroup.exists_card_eq
  rw [hk] at hge hle ⊢
  have hk5 : 5 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).mp hge
  have hk6 : k ≤ 6 := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
  interval_cases k
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem GGSecFiveE6QTwoCfg.false_of_card_bstar_eq_three_pow_six
    (hT : CFSG.LargeExtraspecial.Bridge.OrderMainFor G)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGSecFiveE6QTwoCfg 3 B Bs x L D J)
    (hlab : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) 3 Bs L)
    (hcard : Nat.card Bs = 3 ^ 6) :
    False := by
  classical
  have hU12 : ¬ Nonempty (G ≃* timmesfeldPSU 12) :=
    hC.not_nonempty_mulEquiv_psu12 (by rw [hcard]; norm_num)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hRest, hG, hS, hBs, hxB, hx1, horderx, hLx, hstar, hcyc, hNT⟩ :=
    e6QTwo_config_facts hC
  have : IsSimpleGroup G := hRest.1.1.1
  obtain ⟨K', hWeyl⟩ := hC.exists_weylOfType_E6_sup
  obtain ⟨hperf, K, hfieldK, hfiniteK, θ, hK4, hBsN, hI⟩ :=
    exists_unitaryDatum_of_innerDiagOnLabel_twA5 hlab
  obtain ⟨ω, hω⟩ := USixTwo.exists_root_omega (K := K) hK4
  have hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    inf_centralizer_eq_zpowers_of_elemAbelian Nat.prime_three hBs hxB hx1 hLx
      (fun S hSL hSp => hcyc S hSp hSL)
  have hN : (L.subgroupOf (Subgroup.centralizer {x})).Normal :=
    E6QTwo.normal_of_sStar_of_marking_twA5 hS
      (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.1) hlab)
  obtain ⟨M, hM⟩ : ∃ M : Subgroup G, M = L ⊔ Subgroup.centralizer (L : Set G) := ⟨_, rfl⟩
  obtain ⟨Bin, hBin⟩ : ∃ Bin : Subgroup G, Bin = Bs ⊓ M := ⟨_, rfl⟩
  have hLM : L ≤ M := by
    rw [hM]
    exact le_sup_left
  have hcardBin : Nat.card Bin = 3 ^ 5 := by
    rw [hBin, hM]
    exact E6QTwo.card_inf_sup_centralizer_of_card_six hK4 θ hperf hBs hcard hxB hBL hBsN hI
  have hxC : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
  have hxM : x ∈ M := by
    rw [hM]
    exact Subgroup.mem_sup_right hxC
  have hxBin : x ∈ Bin := by
    rw [hBin]
    exact Subgroup.mem_inf.mpr ⟨hxB, hxM⟩
  obtain ⟨V, hVadd, hVmod, ⟨ι⟩⟩ := exists_ggLinData (p := 3) hBs
  have hVcard : Nat.card V = 3 ^ 6 := by
    rw [← card_eq_of_ggLin ι]
    exact hcard
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [hVcard]; norm_num)
  let A₀ : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs ⊔ ggAutomizer K' Bs
  have hWeylA : GGWeylOfType 3 CoxeterMatrix.E₆ A₀ := hWeyl
  have hA : ∀ ψ ∈ A₀, ψ ∈ ggInduced ⊤ Bs := by
    intro ψ hψ
    exact mem_ggInduced_top_of_mem_ggAutomizer
      (sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hψ)
  obtain ⟨e, cr, α, hα, he, hP⟩ := E6QTwo.exists_cartan_pairing_E6 hNT hWeylA hA ι
  have hmapA : A₀.map (ggLin (p := 3) ι) = E6QTwo.e6Weyl hα :=
    E6QTwo.map_ggLin_eq_e6Weyl ι e hα he
  have hWcard : Nat.card (E6QTwo.e6Weyl hα) = 51840 := by
    rw [E6QTwo.card_e6Weyl_eq ι e hα he]
    rw [show Nat.card A₀ = Nat.card (CoxeterMatrix.E₆).Group from
      (Nat.card_congr e.toEquiv).symm, card_coxeterE6_group]
  have hmem_e6 : ∀ ψ ∈ A₀, ggLin (p := 3) ι ψ ∈ E6QTwo.e6Weyl hα := by
    intro ψ hψ
    rw [← hmapA]
    exact Subgroup.mem_map_of_mem _ hψ
  let vx : V := ι (Additive.ofMul (⟨x, hxB⟩ : ↥Bs))
  have hvxdef : vx = ι (Additive.ofMul (⟨x, hxB⟩ : ↥Bs)) := rfl
  have hvx : vx ≠ 0 := by
    intro h0
    rw [hvxdef] at h0
    have h1 : Additive.ofMul (⟨x, hxB⟩ : ↥Bs) = 0 := ι.injective (by rw [h0, map_zero])
    have h2 : (⟨x, hxB⟩ : ↥Bs) = 1 := by
      simpa using congrArg Additive.toMul h1
    exact hx1 (by simpa using congrArg Subtype.val h2)
  have hspanx : (ZMod 3) ∙ vx = ggLinImage ι (Subgroup.zpowers x) :=
    span_singleton_eq_ggLinImage ι hxB
  have hHcard : Nat.card (ggLinImage (p := 3) ι M) = 3 ^ 5 := by
    rw [card_ggLinImage, ← hBin]
    exact hcardBin
  have hxH : vx ∈ ggLinImage (p := 3) ι M := (ofMul_mem_ggLinImage ι M _).mpr hxM
  have hAle : (ggAutomizer L Bs).map (ggLin (p := 3) ι) ≤ E6QTwo.e6Weyl hα := by
    rw [← hmapA]
    exact Subgroup.map_mono le_sup_left
  have hcardA : 720 ≤ Nat.card ((ggAutomizer L Bs).map (ggLin (p := 3) ι)) := by
    rw [Subgroup.card_map_of_injective (ggLin_injective ι)]
    exact E6QTwo.le_card_ggAutomizer_of_card_six hK4 θ hperf hBs hcard hxB hx1 hBL hstar hBsN hI
      hLx
  have hfixAL : ∀ ψ ∈ ggAutomizer L Bs, ψ ⟨x, hxB⟩ = ⟨x, hxB⟩ := fun ψ hψ =>
    ggAutomizer_apply_eq_of_le_centralizer hLx hψ
  have hAx : ∀ g ∈ (ggAutomizer L Bs).map (ggLin (p := 3) ι), g vx = vx := by
    rintro _ ⟨ψ, hψ, rfl⟩
    rw [hvxdef, ggLin_apply_ofMul, hfixAL ψ hψ]
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
    refine E6QTwo.mem_zpowers_of_forall_conj_of_card_six hK4 θ hperf hBs hcard hxB hx1 hBL hstar
      hBsN hI hLx b.2 ?_
    intro l hlL hlN
    have h1 := hv _ (Subgroup.mem_map_of_mem _ (ggConjAut_mem_ggAutomizer hlL hlN))
    rw [ggLin_apply_ofMul_sub, hspanx, ofMul_mem_ggLinImage] at h1
    exact h1
  have hspan : Submodule.span (ZMod 3) (Set.range cr) = ggLinImage (p := 3) ι M :=
    E6QTwo.span_range_eq_of_card_six hP hα hVcard hWcard hAle hcardA hvx hAx hHcard hxH hAH hfix
  obtain ⟨r, hre6, hrx, hrmod, hrE, v₀, hv₀H, hrv₀⟩ :=
    E6QTwo.exists_reflection_of_card_six hP hα hVcard hWcard hAle hcardA hvx hAx hHcard hxH hAH
      hfix
  let W : Subgroup G := ggConjPreimage Bs A₀
  have hWN : W ≤ Subgroup.normalizer (Bs : Set G) := ggConjPreimage_le_normalizer Bs A₀
  have hex : ∀ ψ ∈ A₀, ∃ g ∈ W, ∀ b : ↥Bs, ((ψ b : ↥Bs) : G) = g * b * g⁻¹ := by
    intro ψ hψ
    obtain ⟨g, -, hgN, hg⟩ := hA ψ hψ
    refine ⟨g, ?_, hg⟩
    rw [mem_ggConjPreimage_iff ⟨g, hgN⟩]
    have hEq : Bs.normalizerMonoidHom ⟨g, hgN⟩ = ψ := by
      ext b
      exact (hg b).symm
    rw [hEq]
    exact hψ
  obtain ⟨ψg, hψgA, hψgr⟩ := Subgroup.mem_map.mp (show r ∈ A₀.map (ggLin (p := 3) ι) by
    rw [hmapA]; exact hre6)
  obtain ⟨g, hgW, hgψ⟩ := hex ψg hψgA
  have hgx : g * x * g⁻¹ = x⁻¹ := by
    have h2 : ψg ⟨x, hxB⟩ = (⟨x, hxB⟩ : ↥Bs)⁻¹ := by
      rw [← ggLin_apply_ofMul_eq_iff (p := 3) ι, hψgr, ofMul_inv, map_neg]
      exact hrx
    rw [← hgψ ⟨x, hxB⟩]
    exact congrArg Subtype.val h2
  have hgB : ∀ z ∈ Bs, g * z * g⁻¹ * z⁻¹ ∈ Subgroup.zpowers x := by
    intro z hz
    have h1 := hrmod (ι (Additive.ofMul (⟨z, hz⟩ : ↥Bs)))
    rw [← hψgr, ggLin_apply_ofMul_sub, hspanx, ofMul_mem_ggLinImage] at h1
    have h2 : ((ψg ⟨z, hz⟩ * (⟨z, hz⟩ : ↥Bs)⁻¹ : ↥Bs) : G) = g * z * g⁻¹ * z⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hgψ]
    rwa [h2] at h1
  have hxL : x ∉ L := E6QTwo.not_mem_of_conj_eq_inv_of_card_six hK4 θ hperf hBs hcard hxB hx1
    hBL hBsN hI hLx hN hcyc hgx hgB
  have hZ2 : IsPGroup 2 (Subgroup.center L) :=
    E6QTwo.isPGroup_two_center_of_not_mem hK4 θ hperf hBs hxB hBL hstar hBsN hxL
  obtain ⟨hcardBL, θ', hmap', hI'⟩ :=
    E6QTwo.card_inf_eq_and_exists_map_eq_torU_of_card_six hK4 θ hperf hZ2 hBs hcard hxB hx1 hBL
      hstar hBsN hI
  obtain ⟨a, haL, hθa, ha1, ψa, hψaAL, -, hψaa, hψamod⟩ :=
    E6QTwo.exists_reflection_threeA_of_card_six hK4 hω θ' hZ2 hmap' hBs hcard hBsN hI'
  let va : V := ι (Additive.ofMul a)
  have hvadef : va = ι (Additive.ofMul a) := rfl
  have hva : va ≠ 0 := by
    intro h0
    rw [hvadef] at h0
    have h1 : Additive.ofMul a = 0 := ι.injective (by rw [h0, map_zero])
    have h2 : a = 1 := by simpa using congrArg Additive.toMul h1
    exact ha1 h2
  have haH : va ∈ ggLinImage (p := 3) ι M := (ofMul_mem_ggLinImage ι M a).mpr (hLM haL)
  have hgv : ggLin (p := 3) ι ψa va = -va := by
    rw [hvadef, ggLin_apply_ofMul, hψaa, ofMul_inv, map_neg]
  have hgu : ∀ u, ∃ c : ZMod 3, ggLin (p := 3) ι ψa u - u = c • va := by
    intro u
    have h := exists_smul_ggLin_sub_eq_of_forall_mem_zpowers (p := 3) ι
      (fun x y => hBs.1.is_comm.comm x y) hψamod u
    rwa [hvadef]
  obtain ⟨s, hse6, hsvx⟩ := E6QTwo.exists_mem_e6Weyl_apply_eq_of_card_six hP hα hVcard hWcard hAle
    hcardA hvx hAx hHcard hxH hAH hfix hva haH (Subgroup.mem_map_of_mem _ hψaAL) hgv hgu
  obtain ⟨ψs, hψsA, hψsr⟩ := Subgroup.mem_map.mp (show s ∈ A₀.map (ggLin (p := 3) ι) by
    rw [hmapA]; exact hse6)
  obtain ⟨n, hnW, hnψ⟩ := hex ψs hψsA
  have hnx : n * x * n⁻¹ = a := by
    have h2 : ψs ⟨x, hxB⟩ = a := by
      rw [← ggLin_apply_ofMul_eq_iff (p := 3) ι, hψsr]
      exact hsvx
    rw [← hnψ ⟨x, hxB⟩]
    exact congrArg Subtype.val h2
  have hnL : n * x * n⁻¹ ∈ L := hnx ▸ haL
  have hθn : θ' (QuotientGroup.mk (⟨n * x * n⁻¹, hnL⟩ : L)) = USixTwo.threeA hω := by
    have hsub : (⟨n * x * n⁻¹, hnL⟩ : L) = ⟨a, haL⟩ := Subtype.ext hnx
    rw [hsub]
    exact hθa
  have hWBin : ∀ w ∈ W, ∀ b ∈ Bin, w * b * w⁻¹ ∈ Bin := by
    intro w hw b hb
    rw [hBin] at hb ⊢
    obtain ⟨hbBs, hbM⟩ := Subgroup.mem_inf.mp hb
    have hwN : w ∈ Subgroup.normalizer (Bs : Set G) := hWN hw
    have hψA : Bs.normalizerMonoidHom ⟨w, hwN⟩ ∈ A₀ := (mem_ggConjPreimage_iff ⟨w, hwN⟩).mp hw
    have h1 : ggLin (p := 3) ι (Bs.normalizerMonoidHom ⟨w, hwN⟩)
        (ι (Additive.ofMul (⟨b, hbBs⟩ : ↥Bs))) ∈ ggLinImage (p := 3) ι M := by
      rw [← hspan]
      refine E6QTwo.apply_mem_span_range_of_mem_e6Weyl hα (hmem_e6 _ hψA) ?_
      rw [hspan]
      exact (ofMul_mem_ggLinImage ι M _).mpr hbM
    rw [ggLin_apply_ofMul, ofMul_mem_ggLinImage] at h1
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hwN b).mp hbBs, h1⟩
  have hWN' : W ≤ Subgroup.normalizer (Bin : Set G) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro b
    refine ⟨hWBin w hw b, fun hb => ?_⟩
    have h1 := hWBin w⁻¹ (W.inv_mem hw) _ hb
    rwa [show w⁻¹ * (w * b * w⁻¹) * w⁻¹⁻¹ = b by group] at h1
  have hBinE : IsElemAbelian 3 Bin := by
    rw [hBin]
    refine ⟨⟨⟨fun c d => Subtype.ext ?_⟩⟩, fun z hz => hBs.2 z hz.1⟩
    have hcd := congrArg Subtype.val (hBs.1.is_comm.comm (⟨c, c.2.1⟩ : ↥Bs) ⟨d, d.2.1⟩)
    exact hcd
  have hBinL : Bin ⊓ L = Bs ⊓ L := by
    rw [hBin, inf_assoc, inf_eq_right.mpr hLM]
  have hmapBin : ((Bin ⊓ L).subgroupOf L).map
      (θ'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) = USixTwo.torU K := by
    rw [hBinL]
    exact hmap'
  have hZ : Subgroup.center L = ⊥ :=
    E6QTwo.center_eq_bot_of_isPGroup_two hG hK4 hω θ' hperf hZ2 horderx hLx hN hcyc hBinE hxBin
      hcardBin hmapBin ⟨n, hWN' hnW, hnL, hθn⟩
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_eq_mk_of_center_eq_bot hZ θ'
  have hφmap : ((Bin ⊓ L).subgroupOf L).map φ.toMonoidHom = USixTwo.torU K := by
    have hcomp : φ.toMonoidHom = θ'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)) :=
      MonoidHom.ext fun l => hφ l
    rw [hcomp]
    exact hmapBin
  have hφn : φ ⟨n * x * n⁻¹, hnL⟩ = USixTwo.threeA hω := by
    rw [hφ]
    exact hθn
  have hS' : USixTwo.LocalSetting hω x L φ Bin :=
    ⟨hK4, horderx, hLx, hN, hcyc, hBinE, hxBin, hcardBin, hφmap, ⟨n, hWN' hnW, hnL, hφn⟩⟩
  have hWb : W ⊓ Subgroup.centralizer {x} ≤
      (L ⊓ Subgroup.normalizer (Bin : Set G)) ⊔ Subgroup.centralizer (Bin : Set G) := by
    intro w hw
    obtain ⟨hwW, hwC⟩ := Subgroup.mem_inf.mp hw
    have hwN : w ∈ Subgroup.normalizer (Bs : Set G) := hWN hwW
    have hψA : Bs.normalizerMonoidHom ⟨w, hwN⟩ ∈ A₀ := (mem_ggConjPreimage_iff ⟨w, hwN⟩).mp hwW
    have hfixw : Bs.normalizerMonoidHom ⟨w, hwN⟩ ⟨x, hxB⟩ = ⟨x, hxB⟩ := by
      apply Subtype.ext
      show w * x * w⁻¹ = x
      rw [Subgroup.mem_centralizer_singleton_iff.mp hwC]
      group
    have hmemA := E6QTwo.mem_of_mem_e6Weyl_of_apply_eq_of_card_six hP hα hVcard hWcard hAle
      hcardA hvx hAx hHcard hxH hAH hfix (hmem_e6 _ hψA)
      (by rw [hvxdef, ggLin_apply_ofMul, hfixw])
    obtain ⟨ψ', hψ', hψ'eq⟩ := Subgroup.mem_map.mp hmemA
    have hψAL : Bs.normalizerMonoidHom ⟨w, hwN⟩ ∈ ggAutomizer L Bs :=
      (ggLin_injective ι hψ'eq) ▸ hψ'
    obtain ⟨l, hlL, hlN, hlψ⟩ := mem_ggAutomizer_iff.mp hψAL
    have hCb : l⁻¹ * w ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have h1 : w * b * w⁻¹ = ((Bs.normalizerMonoidHom ⟨w, hwN⟩ ⟨b, hb⟩ : ↥Bs) : G) := rfl
      have hcomm' : (l⁻¹ * w) * b = b * (l⁻¹ * w) := by
        calc (l⁻¹ * w) * b = l⁻¹ * (w * b * w⁻¹) * w := by group
          _ = l⁻¹ * (l * b * l⁻¹) * w := by rw [h1, hlψ ⟨b, hb⟩]
          _ = b * (l⁻¹ * w) := by group
      exact hcomm'.symm
    have hlBin : l ∈ Subgroup.normalizer (Bin : Set G) := by
      rw [hBin]
      exact Subgroup.inf_normalizer_le_normalizer_inf
        (Subgroup.mem_inf.mpr ⟨hlN, Subgroup.le_normalizer (hLM hlL)⟩)
    have hCBin : Subgroup.centralizer (Bs : Set G) ≤ Subgroup.centralizer (Bin : Set G) :=
      Subgroup.centralizer_le (by rw [hBin]; exact SetLike.coe_subset_coe.mpr inf_le_left)
    have h3 : l * (l⁻¹ * w) ∈ (L ⊓ Subgroup.normalizer (Bin : Set G)) ⊔
        Subgroup.centralizer (Bin : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hlL, hlBin⟩))
        (Subgroup.mem_sup_right (hCBin hCb))
    rwa [mul_inv_cancel_left] at h3
  have hEH : ggLinImage (p := 3) ι L ≤ ggLinImage ι M := ggLinImage_mono ι hLM
  have hEcard : Nat.card (ggLinImage (p := 3) ι L) = 3 ^ 4 := (card_ggLinImage ι L).trans hcardBL
  have hxE : vx ∉ ggLinImage (p := 3) ι L := fun h =>
    hxL ((ofMul_mem_ggLinImage ι L ⟨x, hxB⟩).mp h)
  have hAE : ∀ g ∈ (ggAutomizer L Bs).map (ggLin (p := 3) ι), ∀ v ∈ ggLinImage (p := 3) ι L,
      g v ∈ ggLinImage (p := 3) ι L := by
    rintro _ ⟨ψ, hψ, rfl⟩ v hv
    obtain ⟨l, hlL, -, hlψ⟩ := mem_ggAutomizer_iff.mp hψ
    obtain ⟨b, rfl⟩ : ∃ b : ↥Bs, ι (Additive.ofMul b) = v :=
      ⟨Additive.toMul (ι.symm v), by simp⟩
    rw [ofMul_mem_ggLinImage] at hv
    rw [ggLin_apply_ofMul, ofMul_mem_ggLinImage, hlψ]
    exact L.mul_mem (L.mul_mem hlL hv) (L.inv_mem hlL)
  have hgBL : ∀ z ∈ Bin ⊓ L, g * z * g⁻¹ = z := by
    intro z hz
    rw [hBinL] at hz
    obtain ⟨hzBs, hzL⟩ := Subgroup.mem_inf.mp hz
    have hrz := hrE _ hEH hEcard hxE hAE _ ((ofMul_mem_ggLinImage ι L ⟨z, hzBs⟩).mpr hzL)
    rw [← hψgr, ggLin_apply_ofMul_eq_iff] at hrz
    rw [← hgψ ⟨z, hzBs⟩, hrz]
  obtain ⟨b₀, rfl⟩ : ∃ b : ↥Bs, ι (Additive.ofMul b) = v₀ :=
    ⟨Additive.toMul (ι.symm v₀), by simp⟩
  have hb₀M : (b₀ : G) ∉ L ⊔ Subgroup.centralizer (L : Set G) := by
    rw [← hM]
    exact fun h => hv₀H ((ofMul_mem_ggLinImage ι M b₀).mpr h)
  rw [← hψgr, ggLin_apply_ofMul_eq_iff] at hrv₀
  have hgb₀ : g * b₀ = b₀ * g := by
    have h1 : g * b₀ * g⁻¹ = b₀ := by rw [← hgψ b₀, hrv₀]
    calc g * (b₀ : G) = g * b₀ * g⁻¹ * g := by group
      _ = b₀ * g := by rw [h1]
  exact USixTwo.LocalSetting.false_of_commute_outer hG hS' hWN' hWb ⟨n, hnW, hnL, hφn⟩
    ⟨g, hgW, hgBL, hgx, b₀, hBsN b₀.2, hgb₀, hBs.2 _ b₀.2, hb₀M⟩ hT hU12

end CFSG.StandardType

end
