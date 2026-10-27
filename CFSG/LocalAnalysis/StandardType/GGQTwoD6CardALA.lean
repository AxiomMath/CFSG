module

public import CFSG.LocalAnalysis.StandardType.GGQTwoD6CardALDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

theorem ggQ2d6l_not_AL_le_AJ {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} [Fact (Nat.Prime 3)] (hS : GGQTwoSetting 3 B Bs x L D J) {y' : G}
    {K' : Subgroup G} (M' : GGQTwoModel 3 Bs x y' D L J K') :
    ¬ ggAutomizer L Bs ≤ ggAutomizer J Bs := by
  intro hle
  have hConfig := hS.1.1
  have hStd := hConfig.2.2
  have hStdPre : LargeEvenStdSubPre 3 B x L D J := hStd.1
  have hDleB : D ≤ B := hStdPre.1
  have hcardD : Nat.card D = 3 ^ 2 := hStdPre.2.2.1
  have hDcent : D = B ⊓ Subgroup.centralizer (J : Set G) := hStdPre.2.2.2.2.2.2
  have hBs : GGBstar 3 B Bs := hConfig.2.1
  have hBBs : B ≤ Bs := hBs.1
  have hDleBs : D ≤ Bs := hDleB.trans hBBs
  have hDleCJ : D ≤ Subgroup.centralizer (J : Set G) := by
    rw [hDcent]
    exact inf_le_right
  have hJleCD : J ≤ Subgroup.centralizer (D : Set G) :=
    Subgroup.le_centralizer_iff.mp hDleCJ
  obtain ⟨-, -, -, -, -, -, hSStar, -⟩ := hConfig.1
  have hxne : x ≠ 1 := hSStar.2.2.1
  have : Finite M'.V := Finite.of_equiv (Additive ↥Bs) M'.model.toEquiv
  let v : M'.V := M'.model (Additive.ofMul ⟨x, M'.hx⟩)
  have hvne : v ≠ 0 := by
    intro h0
    have hm0 : M'.model (Additive.ofMul (⟨x, M'.hx⟩ : ↥Bs)) = 0 := by
      simpa [v] using h0
    have h1 : Additive.ofMul (⟨x, M'.hx⟩ : ↥Bs) = 0 := by
      have hm0' : M'.model (Additive.ofMul (⟨x, M'.hx⟩ : ↥Bs)) = M'.model 0 := by
        simpa using hm0
      simpa using M'.model.injective hm0'
    have h2 : (⟨x, M'.hx⟩ : ↥Bs) = 1 := Additive.ofMul.injective (by simpa using h1)
    exact hxne (by simpa using congrArg (fun b : ↥Bs => (b : G)) h2)
  have hspan : Nat.card (Submodule.span (ZMod 3) ({v} : Set M'.V)) = 3 := by
    let f : ZMod 3 → ↥(Submodule.span (ZMod 3) ({v} : Set M'.V)) :=
      fun c => ⟨c • v, Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton v))⟩
    have hf_inj : Function.Injective f := by
      intro a b hab
      have h : a • v = b • v := congrArg Subtype.val hab
      have hzero : (a - b) • v = 0 := by
        rw [sub_smul, h, sub_self]
      have hab0 : a - b = 0 := by
        rcases (smul_eq_zero.mp hzero) with h' | h'
        · exact h'
        · exact absurd h' hvne
      exact sub_eq_zero.mp hab0
    have hf_surj : Function.Surjective f := by
      intro w
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp w.2
      exact ⟨c, Subtype.ext hc⟩
    have e : ZMod 3 ≃ ↥(Submodule.span (ZMod 3) ({v} : Set M'.V)) :=
      Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
    rw [← Nat.card_congr e]
    exact Nat.card_zmod 3
  let F : ↥D → ↥(ggFixedSubmodule (p := 3) M'.model (ggAutomizer L Bs)) := fun d =>
    ⟨M'.model (Additive.ofMul ⟨(d : G), hDleBs d.2⟩), by
      rw [mem_ggFixedSubmodule_iff]
      intro φ hφL
      have hφJ : φ ∈ ggAutomizer J Bs := hle hφL
      obtain ⟨g, hgJ, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hφJ
      have hgD : g ∈ Subgroup.centralizer (D : Set G) := hJleCD hgJ
      have hcomm : (d : G) * g = g * (d : G) :=
        Subgroup.mem_centralizer_iff.mp hgD (d : G) d.2
      have hge : g * (d : G) * g⁻¹ = (d : G) := by
        rw [← hcomm]
        group
      have hφd : (φ ⟨(d : G), hDleBs d.2⟩ : G) = (d : G) := by
        rw [hφg]
        exact hge
      have hb : φ ⟨(d : G), hDleBs d.2⟩ = ⟨(d : G), hDleBs d.2⟩ := Subtype.ext hφd
      rw [ggLin_apply_ofMul, hb]⟩
  have hF : Function.Injective F := by
    intro d1 d2 h
    have h' : M'.model (Additive.ofMul ⟨(d1 : G), hDleBs d1.2⟩) =
        M'.model (Additive.ofMul ⟨(d2 : G), hDleBs d2.2⟩) :=
      congrArg Subtype.val h
    have h'' : Additive.ofMul (⟨(d1 : G), hDleBs d1.2⟩ : ↥Bs) =
        Additive.ofMul (⟨(d2 : G), hDleBs d2.2⟩ : ↥Bs) := M'.model.injective h'
    have hb : (⟨(d1 : G), hDleBs d1.2⟩ : ↥Bs) = ⟨(d2 : G), hDleBs d2.2⟩ :=
      Additive.ofMul.injective h''
    exact Subtype.ext (congrArg (fun b : ↥Bs => (b : G)) hb)
  have hlecard := Nat.card_le_card_of_injective F hF
  have hcardD9 : Nat.card ↥D = 9 := by
    rw [hcardD]
    norm_num
  have hcardfix : Nat.card ↥(ggFixedSubmodule (p := 3) M'.model (ggAutomizer L Bs)) = 3 := by
    rw [M'.fixed_x]
    exact hspan
  rw [hcardD9, hcardfix] at hlecard
  omega

end CFSG.StandardType

end
