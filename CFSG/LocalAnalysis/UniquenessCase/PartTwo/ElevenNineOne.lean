module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22uf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace ElevenNine

theorem exists_Y (D : Data G) {V₀ V : Subgroup G} (hV : F11.Hyp11 D V₀ V) (h118 : C118 D V₀ V)
    [hNorm : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] {X : Subgroup G}
    (hX₀X : F11.CTilde D.M V₀ V ≤ X) (hXM : X ≤ D.M)
    (hlayer : rankThreeLayer (F11.barImage11 D.M V₀ V X) = F11.barImage11 D.M V₀ V X) :
    ∃ Y : Subgroup G, F11.IsY119 D.M V₀ V X Y ∧
      (D.M ≤ normalizer (X : Set G) → D.M ≤ normalizer (Y : Set G)) := by
  obtain ⟨hn, hO, -⟩ := hyp11_ctilde D hV
  haveI hNn : (barImage D.M (F11.CTilde D.M V₀ V)).Normal := uc22p22u_barImage_normal hn
  obtain ⟨φ, hφs, hφk, hφπ⟩ := uc22p22u_exists_phi (M := D.M) (X := F11.CTilde D.M V₀ V) hO
  have h118V := h118
  set X₀ : Subgroup G := F11.CTilde D.M V₀ V with hX₀
  set N : Subgroup (Bar2 D.M) := barImage D.M X₀ with hN
  set Fs : Subgroup (Bar2 D.M) :=
    (CFSG.fittingSubgroup ↥N).map N.subtype ⊔ (CFSG.layer ↥N).map N.subtype with hFs
  set C : Subgroup (Bar2 D.M) := centralizer (Fs : Set (Bar2 D.M)) with hC
  haveI : (CFSG.layer ↥N).Characteristic := CFSG.LocalCores.layer_characteristic
  haveI hFn : ((CFSG.fittingSubgroup ↥N).map N.subtype).Normal := inferInstance
  haveI hEn : ((CFSG.layer ↥N).map N.subtype).Normal := inferInstance
  haveI hFsn : Fs.Normal := Subgroup.sup_normal _ _
  haveI hCn : C.Normal := uc22p21c_normal_centralizer Fs
  set Xb : Subgroup (F11.MBar11 D.M V₀ V) := F11.barImage11 D.M V₀ V X with hXb
  have hXbperf : ⁅Xb, Xb⁆ = Xb := uc22p22u_isPerfect_of_rankThreeLayer hlayer
  have hXblayer : CFSG.layer ↥Xb = ⊤ := uc22p22u_layer_eq_top_of_rankThreeLayer hlayer
  have hUφ : (barImage D.M X).map φ = Xb := by
    ext q
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hu
      rw [hφπ]
      exact uc22p22u_mem_barImage11.2 ⟨m, hm, rfl⟩
    · intro hq
      obtain ⟨m, hm, rfl⟩ := uc22p22u_mem_barImage11.1 hq
      exact ⟨uc22p21cPi D.M m, uc22p21c_mem_barImage.2 ⟨m, hm, rfl⟩, hφπ m⟩
  have hNU : N ≤ barImage D.M X := by
    intro q hq
    obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hq
    exact uc22p21c_mem_barImage.2 ⟨m, hX₀X hm, rfl⟩
  have hsplit : barImage D.M X ≤ (barImage D.M X ⊓ C) ⊔ N :=
    uc22p22u_split_of_perfect φ N hφk h118V (barImage D.M X) hNU (by rw [hUφ]; exact hXbperf)
  set C1 : Subgroup G := barPreimage D.M C with hC1
  set W : Subgroup G := X ⊓ C1 with hWdef
  have hC1n : D.M ≤ normalizer (C1 : Set G) := uc22p22u_barPreimage_normalizes (D := C)
  have hWM : W ≤ D.M := inf_le_left.trans hXM
  have hWX : W ≤ X := inf_le_left
  have hWC : ∀ w : ↥D.M, (w : G) ∈ W → uc22p21cPi D.M w ∈ C := fun w hw =>
    (uc22p21c_mem_barPreimage.1 hw.2).choose_spec
  have hWonto : ∀ q ∈ Xb, ∃ w : ↥D.M, (w : G) ∈ W ∧
      (QuotientGroup.mk w : F11.MBar11 D.M V₀ V) = q := by
    intro q hq
    obtain ⟨m, hm, rfl⟩ := uc22p22u_mem_barImage11.1 hq
    obtain ⟨c, hc, k', hk', hck⟩ := Subgroup.mem_sup_of_normal_right.1
      (hsplit (uc22p21c_mem_barImage.2 ⟨m, hm, rfl⟩))
    obtain ⟨⟨m₁, hm₁, rfl⟩, hcC⟩ := hc
    obtain ⟨k, hk, rfl⟩ := uc22p21c_mem_barImage.1 hk'
    refine ⟨m₁, ⟨hm₁, uc22p21c_mem_barPreimage.2 ⟨m₁.2, hcC⟩⟩, ?_⟩
    have h1 : (m₁ * k)⁻¹ * m ∈ CFSG.pCore 2 ↥D.M := by
      refine (QuotientGroup.eq_one_iff _).1 ?_
      change uc22p21cPi D.M _ = 1
      rw [map_mul, map_inv, map_mul, hck, inv_mul_cancel]
    have h2 : (((m₁ * k)⁻¹ * m : ↥D.M) : G) ∈ X₀ := hO ⟨_, h1, rfl⟩
    apply uc22p22u_mk_eq_iff.2
    have h3 : ((m₁⁻¹ * m : ↥D.M) : G) = (k : G) * (((m₁ * k)⁻¹ * m : ↥D.M) : G) := by
      simp [mul_assoc]
    rw [h3]
    exact X₀.mul_mem hk h2
  let f : ↥W →* ↥Xb :=
    ((QuotientGroup.mk' ((F11.CTilde D.M V₀ V).subgroupOf D.M)).comp
      (Subgroup.inclusion hWM)).codRestrict Xb fun w =>
      uc22p22u_mem_barImage11.2 ⟨Subgroup.inclusion hWM w, hWX w.2, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨q, hq⟩
    obtain ⟨w, hw, hwq⟩ := hWonto q hq
    exact ⟨⟨(w : G), hw⟩, Subtype.ext hwq⟩
  set Y : Subgroup G := Hinf W with hY
  have hYW : Y ≤ W := uc22p21c_Hinf_le W
  have hYperf : ⁅Y, Y⁆ = Y := uc22p21c_Hinf_perfect W
  have hYM : Y ≤ D.M := hYW.trans hWM
  have hYX : Y ≤ X := hYW.trans hWX
  have hYC : ∀ y : ↥D.M, (y : G) ∈ Y → uc22p21cPi D.M y ∈ C := fun y hy => hWC y (hYW hy)
  have hXbres : (CFSG.perfectResidual ↥Xb) = ⊤ := by
    refine eq_top_iff.2 (uc22p21c_le_perfectResidual ⊤ ?_)
    have h2 : ⁅(⊤ : Subgroup ↥Xb), (⊤ : Subgroup ↥Xb)⁆ = ⊤ := by
      have h1 := uc22p22u_layer_eq_top_of_rankThreeLayer hlayer
      have := CFSG.LocalCores.layer_perfect (G := ↥Xb)
      rwa [h1] at this
    exact h2
  have hres : (CFSG.perfectResidual ↥W).map f = ⊤ := by
    rw [uc22p21c_map_perfectResidual f hf, hXbres]
  have hYbar : F11.barImage11 D.M V₀ V Y = Xb := by
    apply le_antisymm
    · intro q hq
      obtain ⟨m, hm, rfl⟩ := uc22p22u_mem_barImage11.1 hq
      exact uc22p22u_mem_barImage11.2 ⟨m, hYX hm, rfl⟩
    · intro q hq
      have h1 : (⟨q, hq⟩ : ↥Xb) ∈ (CFSG.perfectResidual ↥W).map f := by
        rw [hres]
        trivial
      obtain ⟨w, hw, hwq⟩ := h1
      exact uc22p22u_mem_barImage11.2 ⟨Subgroup.inclusion hWM w, uc22p21c_mem_Hinf.2 ⟨w, hw, rfl⟩,
        congrArg Subtype.val hwq⟩
  have hnormW : ∀ g ∈ D.M, g ∈ normalizer (X : Set G) → g ∈ normalizer (W : Set G) := by
    intro g hgM hgX
    rw [mem_normalizer_iff]
    intro x
    have h1 := mem_normalizer_iff.1 (hC1n hgM) x
    have h2 := mem_normalizer_iff.1 hgX x
    constructor
    · rintro ⟨hxX, hxC⟩
      exact ⟨h2.1 hxX, h1.1 hxC⟩
    · rintro ⟨hxX, hxC⟩
      exact ⟨h2.2 hxX, h1.2 hxC⟩
  have hXW : X ≤ normalizer (W : Set G) := fun g hg =>
    hnormW g (hXM hg) (Subgroup.le_normalizer hg)
  have hXY : X ≤ normalizer (Y : Set G) := fun g hg =>
    CFSG.SignalizerFunctorTheorem.Nonsolvable.normalizer_le_normalizer_perfectResidual_map W
      (hXW hg)
  have hπcomm : ∀ a b : ↥D.M, (a : G) ∈ Y ⊓ X₀ → (b : G) ∈ Y ⊓ X₀ →
      uc22p21cPi D.M a * uc22p21cPi D.M b = uc22p21cPi D.M b * uc22p21cPi D.M a := by
    intro a b ha hb
    have haN : uc22p21cPi D.M a ∈ N := uc22p21c_mem_barImage.2 ⟨a, ha.2, rfl⟩
    have haF : uc22p21cPi D.M a ∈ Fs := uc22p22u_inf_centralizer_fstar_le N ⟨haN, hYC a ha.1⟩
    exact Subgroup.mem_centralizer_iff.1 (hYC b hb.1) _ haF
  have hS : Group.IsSolvable ↥(Y ⊓ X₀) :=
    uc22p22u_isSolvable_of_pi_comm (inf_le_left.trans hYM) hπcomm
  have hYX₀ : Y ⊓ X₀ ≤ OInf Y := by
    have hnorm : ((Y ⊓ X₀).subgroupOf Y).Normal := by
      rw [Subgroup.inf_subgroupOf_left]
      refine ⟨fun a ha g => ?_⟩
      have ha' : (a : G) ∈ X₀ := ha
      exact (mem_normalizer_iff.1 (hn (hYM g.2)) (a : G)).1 ha'
    have hsolv : Group.IsSolvable ↥((Y ⊓ X₀).subgroupOf Y) := by
      haveI := hS
      exact Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe (inf_le_left : Y ⊓ X₀ ≤ Y)).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe (inf_le_left : Y ⊓ X₀ ≤ Y)).injective
    have hle : (Y ⊓ X₀).subgroupOf Y ≤ CFSG.solvableRadical ↥Y := le_sSup ⟨hnorm, hsolv⟩
    intro x hx
    exact ⟨⟨x, hx.1⟩, hle (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  let ψ : ↥Y →* ↥Xb := f.comp (Subgroup.inclusion hYW)
  have hψ : Function.Surjective ψ := by
    intro q
    have h1 : q ∈ (CFSG.perfectResidual ↥W).map f := by
      rw [hres]
      trivial
    obtain ⟨w, hw, hwq⟩ := h1
    exact ⟨⟨(w : G), uc22p21c_mem_Hinf.2 ⟨w, hw, rfl⟩⟩, hwq⟩
  have hker : ∀ k : ↥Y, k ∈ ψ.ker → ((k : ↥Y) : G) ∈ X₀ := by
    intro k hk
    have h1 : (QuotientGroup.mk (Subgroup.inclusion hYM k) : F11.MBar11 D.M V₀ V) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.1 hk)
    exact Subgroup.mem_subgroupOf.1
      ((QuotientGroup.eq_one_iff (N := (F11.CTilde D.M V₀ V).subgroupOf D.M)
        (Subgroup.inclusion hYM k)).1 h1)
  have hle2 : (pCoreOf 2 D.M).subgroupOf Y ≤ CFSG.pCore 2 ↥Y := by
    haveI : ((pCoreOf 2 D.M).subgroupOf Y).Normal := by
      refine ⟨fun a ha g => ?_⟩
      have ha' : (a : G) ∈ pCoreOf 2 D.M := ha
      exact uc22p21c_conj_mem_pCoreOf_self (hYM g.2) ha'
    exact le_sSup ⟨inferInstance, (uc22p21c_isPGroup_pCoreOf D.M).comap_subtype⟩
  have hKY : ⁅(⊤ : Subgroup ↥Y), ψ.ker⁆ ≤ CFSG.pCore 2 ↥Y := by
    refine Subgroup.commutator_le.2 fun y _ k hk => ?_
    have hkX : ((k : ↥Y) : G) ∈ X₀ := hker k hk
    have h1 : ⁅(Subgroup.inclusion hYM y), Subgroup.inclusion hYM k⁆ ∈ CFSG.pCore 2 ↥D.M := by
      refine (QuotientGroup.eq_one_iff _).1 ?_
      change uc22p21cPi D.M _ = 1
      rw [map_commutatorElement]
      refine commutatorElement_eq_one_iff_commute.2 ?_
      have hkN : uc22p21cPi D.M (Subgroup.inclusion hYM k) ∈ N :=
        uc22p21c_mem_barImage.2 ⟨_, hkX, rfl⟩
      have hkF : uc22p21cPi D.M (Subgroup.inclusion hYM k) ∈ Fs :=
        uc22p22u_inf_centralizer_fstar_le N ⟨hkN, hYC _ k.2⟩
      exact (Subgroup.mem_centralizer_iff.1 (hYC _ y.2) _ hkF).symm
    exact hle2 (Subgroup.mem_subgroupOf.2 ⟨_, h1, rfl⟩)
  have hYperf' : ⁅(⊤ : Subgroup ↥Y), (⊤ : Subgroup ↥Y)⁆ = ⊤ := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype, hYperf]
  let e : ↥Y ⧸ ψ.ker ≃* ↥Xb := QuotientGroup.quotientKerEquivOfSurjective ψ hψ
  have hlayerQ : CFSG.layer (↥Y ⧸ ψ.ker) = ⊤ := by
    have h1 := CFSG.WholeGroup.layer_map_mulEquiv e.symm
    rw [hXblayer, Subgroup.map_top_of_surjective _ e.symm.surjective] at h1
    exact h1.symm
  have hlayerBar : CFSG.layer (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊤ :=
    uc22p22u_layer_bar_eq_top ψ.ker hYperf' hKY hlayerQ
  have hO2E : F11.O2E Y = Y := by
    unfold F11.O2E
    rw [← uc22p22u_layer_eq_rankThreeLayer_top (↥Y ⧸ CFSG.pCore 2 ↥Y), hlayerBar,
      Subgroup.comap_top, Subgroup.map_top, Subgroup.range_subtype]
  exact ⟨Y, ⟨hYX, hYperf, hO2E, hXY, hYX₀, hYbar⟩, fun hMX g hg =>
    CFSG.SignalizerFunctorTheorem.Nonsolvable.normalizer_le_normalizer_perfectResidual_map W
      (hnormW g hg (hMX hg))⟩

end ElevenNine

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
