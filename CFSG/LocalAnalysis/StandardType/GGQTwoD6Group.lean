module

public import CFSG.LocalAnalysis.StandardType.GGQTwoD6Frame
public import CFSG.LocalAnalysis.StandardType.GGQTwoFinishGen

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace QTwoD6

open CFSG.StandardType.QTwoLin

theorem isReflLin_iff_std (g : V7 ≃ₗ[ZMod 3] V7) :
    IsReflLin g ↔ CFSG.StandardType.IsReflLin g :=
  Iff.rfl

@[expose] noncomputable def linA {G : Type} [Group G] [Finite G] {Bs K : Subgroup G}
    (N : GGQ2NbrDatum 3 Bs K) (F : N.V ≃ₗ[ZMod 3] V7) : Subgroup (V7 ≃ₗ[ZMod 3] V7) :=
  (ggAutomizer ⊤ Bs).map (ggCoord N F)

@[expose] noncomputable def linAL {G : Type} [Group G] [Finite G] {Bs K : Subgroup G}
    (L : Subgroup G) (N : GGQ2NbrDatum 3 Bs K) (F : N.V ≃ₗ[ZMod 3] V7) :
    Subgroup (V7 ≃ₗ[ZMod 3] V7) :=
  (ggAutomizer L Bs).map (ggCoord N F)

theorem ggQ2d6_linAL_le_linA {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {L : Subgroup G}
    {N : GGQ2NbrDatum 3 Bs K} {b : N.Λ} {y : G} {hy : y ∈ Bs} (Fr : GGQ2D6Frame N b hy) :
    linAL L N Fr.F ≤ linA N Fr.F := by
  exact Subgroup.map_mono (f := ggCoord N Fr.F) (ggAutomizer_mono Bs le_top)

theorem ggQ2d6_transvectionFree {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) {K : Subgroup G}
    {N : GGQ2NbrDatum 3 Bs K} {b : N.Λ} {y : G} {hy : y ∈ Bs} (Fr : GGQ2D6Frame N b hy) :
    TransvectionFree (linA N Fr.F) := by
  have hNT : GGNoTransvection 3 Bs := hS.1.2.2.2.1
  have hA : TransvectionFree ((ggAutomizer ⊤ Bs).map (ggLin (p := 3) N.model)) := by
    intro g hg hgT
    obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨u, ψ, hu, hψ, hψu, hgv⟩ := hgT
    have hφ' : φ ∈ ggInduced ⊤ Bs := by
      rw [ggAutomizer_eq] at hφ
      exact hφ
    exact hNT φ hφ' (ggIsTransvection_of_apply N.model hu hψ hψu hgv)
  rw [linA]
  show TransvectionFree ((ggAutomizer ⊤ Bs).map
    ((ggLinConj Fr.F).toMonoidHom.comp (ggLin (p := 3) N.model)))
  rw [← Subgroup.map_map]
  exact (ggLinConj_transvectionFree Fr.F
    ((ggAutomizer ⊤ Bs).map (ggLin (p := 3) N.model))).mpr hA

theorem ggQ2d6_W6_le {G : Type} [Group G] [Finite G] {Bs K : Subgroup G}
    {N : GGQ2NbrDatum 3 Bs K} {b : N.Λ} {y : G} {hy : y ∈ Bs} (Fr : GGQ2D6Frame N b hy) :
    W6 ≤ linA N Fr.F := by
  rw [W6, linA]
  refine (Subgroup.closure_le _).mpr ?_
  rintro g ⟨i, rfl⟩
  refine Subgroup.mem_map.mpr ⟨N.simple (Fr.e i), ?_, ?_⟩
  · exact ggAutomizer_mono Bs (le_top : K ≤ ⊤)
      (by rw [N.automizer_K]; exact Subgroup.subset_closure ⟨Fr.e i, rfl⟩)
  · exact ggQ2_d6_coord_simple Fr i

private lemma ggQ2d6l_layer_le {G : Type} [Group G] (H : Subgroup G) :
    LargeEvenLayer H ≤ H := by
  change sSup {K : Subgroup G | IsComponentOf K H} ≤ H
  exact sSup_le fun K hK => hK.1

theorem ggQ2d6_J6_le_linAL {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) {K : Subgroup G}
    {N : GGQ2NbrDatum 3 Bs K} {b : N.Λ} {y : G} {hy : y ∈ Bs}
    (hJ : ggAutomizer J Bs = Subgroup.closure (N.simple '' {k | k ≠ b}))
    (Fr : GGQ2D6Frame N b hy) : J6 ≤ linAL L N Fr.F := by
  have hJL : J ≤ L := by
    obtain ⟨-, -, hStd⟩ := hS.1.1
    have hPre : LargeEvenStdSubPre 3 B x L D J := hStd.1
    have hJeq : J = LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G)) := hPre.2.2.2.2.1
    rw [hJeq]
    exact (ggQ2d6l_layer_le _).trans inf_le_left
  rw [J6, linAL]
  refine (Subgroup.closure_le _).mpr ?_
  rintro g ⟨j, hj, rfl⟩
  refine Subgroup.mem_map.mpr ⟨N.simple (Fr.e j), ?_, ?_⟩
  · exact ggAutomizer_mono Bs hJL
      (by rw [hJ]; exact
        Subgroup.subset_closure ⟨Fr.e j, fun h => hj (Fr.e.injective (h.trans Fr.b_eq)), rfl⟩)
  · exact ggQ2_d6_coord_simple Fr j

theorem ggQ2d6_AL_fix {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) {y' : G} {K' : Subgroup G}
    (M' : GGQTwoModel 3 Bs x y' D L J K') {K : Subgroup G} {N : GGQ2NbrDatum 3 Bs K}
    {b : N.Λ} {y : G} {hy : y ∈ Bs} (Fr : GGQ2D6Frame N b hy) (hx : x ∈ Bs) :
    ∀ φ ∈ linAL L N Fr.F, φ (ggEll N Fr.F hx) = ggEll N Fr.F hx := by
  have _ := hS
  intro φ hφ
  rw [linAL] at hφ
  obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp hφ
  have hfixM : ∀ ψ ∈ ggAutomizer L Bs,
      ggLin (p := 3) M'.model ψ (M'.model (Additive.ofMul ⟨x, M'.hx⟩)) =
        M'.model (Additive.ofMul ⟨x, M'.hx⟩) := by
    intro ψ hψ
    have hmem : M'.model (Additive.ofMul ⟨x, M'.hx⟩) ∈
        ggFixedSubmodule (p := 3) M'.model (ggAutomizer L Bs) := by
      rw [M'.fixed_x]
      exact Submodule.subset_span (Set.mem_singleton _)
    exact (mem_ggFixedSubmodule_iff (p := 3) (ι := M'.model)
      (N := ggAutomizer L Bs) (v := M'.model (Additive.ofMul ⟨x, M'.hx⟩))).mp hmem ψ hψ
  have hfixψ : ψ (⟨x, hx⟩ : ↥Bs) = ⟨x, hx⟩ := by
    have h1 := hfixM ψ hψ
    rw [ggLin_apply_ofMul (p := 3) M'.model ψ (⟨x, M'.hx⟩)] at h1
    have h2 : ψ (⟨x, M'.hx⟩ : ↥Bs) = ⟨x, M'.hx⟩ :=
      Additive.ofMul.injective (M'.model.injective h1)
    have h3 : (⟨x, M'.hx⟩ : ↥Bs) = ⟨x, hx⟩ := Subtype.ext rfl
    rw [← h3]
    exact h2
  rw [ggEll]
  rw [ggQ2_d6_coord_apply, LinearEquiv.symm_apply_apply,
    ggLin_apply_ofMul (p := 3) N.model ψ (⟨x, hx⟩), hfixψ]

theorem ggQ2d6_AL_moves {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr 3 B x D J y K) {y' : G} {K' : Subgroup G}
    (M' : GGQTwoModel 3 Bs x y' D L J K') {N : GGQ2NbrDatum 3 Bs K} {b : N.Λ} {hy : y ∈ Bs}
    (Fr : GGQ2D6Frame N b hy) :
    ∃ φ ∈ linAL L N Fr.F, φ e0 ≠ e0 := by
  by_contra hcon
  have hcon' : ∀ φ ∈ linAL L N Fr.F, φ e0 = e0 := by
    intro φ hφ
    by_contra hne
    exact hcon ⟨φ, hφ, hne⟩
  have hconfig : GGConfig 3 B Bs x L D J := hS.1.1
  have hStd : LargeEvenStdSub 3 B x L D J := hconfig.2.2
  have hStdPre : LargeEvenStdSubPre 3 B x L D J := hStd.1
  have hDleB : D ≤ B := hStdPre.1
  have hBBs : B ≤ Bs := hconfig.2.1.1
  have hDBs : D ≤ Bs := hDleB.trans hBBs
  have hxmem : x ∈ D := by
    rw [hnb.2.1]
    exact Subgroup.subset_closure (Set.mem_insert x {y})
  have hxBs : x ∈ Bs := hDBs hxmem
  have hx3 : x ^ 3 = 1 := hconfig.2.1.2.1.2 x hxBs
  have hfixy : ∀ ψ ∈ ggAutomizer L Bs, ψ (⟨y, hy⟩ : ↥Bs) = ⟨y, hy⟩ := by
    intro ψ hψ
    have h1 : ggCoord N Fr.F ψ e0 = e0 :=
      hcon' (ggCoord N Fr.F ψ) (Subgroup.mem_map.mpr ⟨ψ, hψ, rfl⟩)
    rw [← Fr.F_y] at h1
    rw [ggQ2_d6_coord_apply, LinearEquiv.symm_apply_apply] at h1
    have h3 : ggLin (p := 3) N.model ψ (N.model (Additive.ofMul ⟨y, hy⟩)) =
        N.model (Additive.ofMul ⟨y, hy⟩) := Fr.F.injective h1
    rw [ggLin_apply_ofMul (p := 3) N.model ψ (⟨y, hy⟩)] at h3
    exact Additive.ofMul.injective (N.model.injective h3)
  have hmemM : M'.model (Additive.ofMul ⟨y, hy⟩) ∈
      ggFixedSubmodule (p := 3) M'.model (ggAutomizer L Bs) := by
    rw [mem_ggFixedSubmodule_iff]
    intro ψ hψ
    rw [ggLin_apply_ofMul (p := 3) M'.model ψ (⟨y, hy⟩), hfixy ψ hψ]
  have hspan : M'.model (Additive.ofMul ⟨y, hy⟩) ∈
      Submodule.span (ZMod 3) {M'.model (Additive.ofMul ⟨x, M'.hx⟩)} := by
    rw [← M'.fixed_x]
    exact hmemM
  have hzyx : (⟨y, hy⟩ : ↥Bs) ∈ Subgroup.zpowers (⟨x, M'.hx⟩ : ↥Bs) :=
    (ggQ2d6_model_span_iff (p := 3) M'.model (y := x) M'.hx ⟨y, hy⟩).mp hspan
  have hyzx : y ∈ Subgroup.zpowers x := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzyx
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨k, by simpa [Subgroup.coe_zpow] using congrArg Subtype.val hk⟩
  have hDle : D ≤ Subgroup.zpowers x := by
    rw [hnb.2.1]
    refine (Subgroup.closure_le _).mpr ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hzx | hzy
    · rw [hzx]; exact Subgroup.mem_zpowers x
    · rw [hzy]; exact hyzx
  have hxord : orderOf x ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hx3
  have hzcard : Nat.card (Subgroup.zpowers x) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) hxord
  have hcardD : Nat.card D = 9 := by
    have h9 := hStdPre.2.2.1
    norm_num at h9
    exact h9
  have hle : Nat.card D ≤ Nat.card (Subgroup.zpowers x) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hDle)
      (Subgroup.inclusion_injective hDle)
  omega

end QTwoD6

end CFSG.StandardType

end
