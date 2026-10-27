module

public import CFSG.Quasithin.Vol2.Ch3Sec1Inputs
public import CFSG.Quasithin.Vol2.Ch3Sec1D12
public import CFSG.Quasithin.Background.B4Dual

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

section PCore

variable {G : Type} [Group G] [Finite G]

theorem le_pCoreOf_inf_of_le_pCoreOf {M K V : Subgroup G} (hVK : V ≤ K)
    (hVM : V ≤ pCoreOf 2 M) : V ≤ pCoreOf 2 (K ⊓ M) := by
  have hX : V ≤ pCoreOf 2 M ⊓ (K ⊓ M) :=
    le_inf hVM (le_inf hVK (hVM.trans (pCoreOf_le 2 M)))
  refine hX.trans (le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
    ((pCoreOf_isPGroup 2 M).to_le inf_le_left))
  exact A1a.le_normalizer_inf (fun g hg => le_normalizer_pCoreOf 2 M hg.2) Subgroup.le_normalizer

variable {T M M₀ H V : Subgroup G}

theorem Hyp315Base.le_pCoreOf_M (hK : quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T)
    (hM : InM T M) (h : Hyp315Base T M M₀ H V) : V ≤ pCoreOf 2 M := by
  have h1 : pCoreOf 2 M ≤ pCoreOf 2 M₀ :=
    pCoreOf_le_pCoreOf_of_sylow h.le_M hT.1 h.T_le
      (isSylowTwoOf_of_isSylowTwo hT h.T_le_M).2.2
  have h2 : pCoreOf 2 M₀ ≤ Subgroup.centralizer (V : Set G) :=
    A4.pCoreOf_le_centralizer_of_isTwoReducedIn h.reduced
  have hCT : CharTwo M := charTwo_of_inH' hK hT (inH_of_inM hM)
  intro v hv
  exact hCT ⟨h.le_M (h.reduced.1 hv), Subgroup.mem_centralizer_iff.mpr fun g hg =>
    (Subgroup.mem_centralizer_iff.mp (h2 (h1 hg)) v hv).symm⟩

theorem hypE28_of_hyp315 (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hK : quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T) (hM : InM T M)
    (h : Hyp315Base T M M₀ H V) (hD : D11Hyp M₀ H T V (H ⊓ M))
    (hnff : ¬ IsFFInt M₀ V h.reduced.2.2.1) (hVH : ¬ V ≤ pCoreOf 2 H) :
    HypE28 H T (H ⊓ M) V := by
  have hMin := hD.minParabolic hnff
  refine ⟨hMin, isSQTKSub_of_inH hK hs hnab h.inH_H, h.reduced.2.2.1, hD.V_le_T,
    h.T_le.trans h.reduced.2.1, ?_, ?_⟩
  · exact le_pCoreOf_inf_of_le_pCoreOf (hD.V_le_T.trans h.hStar.1.1) (h.le_pCoreOf_M hK hT hM)
  · intro hker
    exact hVH (hMin.le_pCoreOf_of_isPGroup_of_le_kerIn
      (B6.isPGroup_of_isElemAbelian h.reduced.2.2.1) hker)

theorem case_i (hE213 : E213Three) (hE215 : E215) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hK : quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T)
    (hM : InM T M) (h : Hyp315Base T M M₀ H V) (hD : D11Hyp M₀ H T V (H ⊓ M))
    (hnff : ¬ IsFFInt M₀ V h.reduced.2.2.1) (hVH : ¬ V ≤ pCoreOf 2 H) :
    qhatInt M₀ V h.reduced.2.2.1 ≤ 2 ∧
      (IsTISetIn V M → qhatInt M₀ V h.reduced.2.2.1 < 2) := by
  have hE := hypE28_of_hyp315 hs hnab hK hT hM h hD hnff hVH
  have hCT : CharTwo H := charTwo_of_inH' hK hT h.inH_H
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := h.T_le.trans h.reduced.2.1
  have hle : qhatInt M₀ V h.reduced.2.2.1 ≤ qhatInt H V h.reduced.2.2.1 :=
    qhatInt_le_of_isSylowTwoOf h.reduced.2.2.1 hD.sylow₂ hTV h.T_le
  refine ⟨hle.trans (hE213 G H T (H ⊓ M) V hE hCT), fun hTI => ?_⟩
  have hTI' : IsTISetIn V (H ⊓ M) :=
    ⟨le_inf (hD.V_le_T.trans h.hStar.1.1) (hD.V_le_T.trans h.T_le_M),
      fun g hg hgN => hTI.2 g hg.2 hgN⟩
  exact lt_of_le_of_lt hle (hE215 G H T (H ⊓ M) V hE hCT hTI')

end PCore

section DualGeneral

variable {W : Type} [CommGroup W] {Γ : Type*} [Group Γ]

theorem pCoreOf_le_pCoreOf_of_normal {N X : Subgroup Γ} [Finite Γ] (hNX : N ≤ X)
    (hXN : X ≤ Subgroup.normalizer (N : Set Γ)) : pCoreOf 2 N ≤ pCoreOf 2 X :=
  le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 N).trans hNX)
    (hXN.trans (normalizer_le_normalizer_pCoreOf 2 N)) (pCoreOf_isPGroup 2 N)

theorem pCoreOf_map_dualAct_eq_bot [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {A : Subgroup (MulAut W)} (hA : pCoreOf 2 A = ⊥) : pCoreOf 2 (A.map (dualAct W)) = ⊥ := by
  have hinj := dualAct_injective hW
  set Q := pCoreOf 2 (A.map (dualAct W)) with hQ
  set N : Subgroup (MulAut W) := A ⊓ Q.comap (dualAct W) with hN
  have hQn : A.map (dualAct W) ≤ Subgroup.normalizer (Q : Set _) :=
    le_normalizer_pCoreOf 2 _
  have hNn : A ≤ Subgroup.normalizer (N : Set (MulAut W)) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ b ∈ A, ∀ n ∈ N, b * n * b⁻¹ ∈ N := by
      intro b hb n hn
      refine ⟨A.mul_mem (A.mul_mem hb hn.1) (A.inv_mem hb), ?_⟩
      have h1 : dualAct W n ∈ Q := hn.2
      have h2 := (Subgroup.mem_normalizer_iff.mp (hQn ⟨b, hb, rfl⟩) (dualAct W n)).mp h1
      simpa [map_mul, map_inv] using h2
    intro x
    refine ⟨fun hx => key a ha x hx, fun hx => ?_⟩
    simpa [mul_assoc] using key a⁻¹ (A.inv_mem ha) _ hx
  have hN2 : IsPGroup 2 N := by
    intro x
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (A.map (dualAct W)) (⟨dualAct W x, x.2.2⟩ : Q)
    refine ⟨k, Subtype.ext (hinj ?_)⟩
    have := congrArg (fun y : Q => (y : MulAut (W →* Multiplicative (ZMod 2)))) hk
    simpa [map_pow] using this
  have hNle : N ≤ pCoreOf 2 A := le_pCoreOf_of_le_normalizer 2 inf_le_left hNn hN2
  rw [hA, le_bot_iff] at hNle
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨a, haA, rfl⟩ := (pCoreOf_le 2 _) hq
  have : a ∈ N := ⟨haA, hq⟩
  rw [hNle, Subgroup.mem_bot] at this
  rw [this, map_one]
  exact Subgroup.one_mem _

end DualGeneral

section FFJ

variable {W : Type*} [CommGroup W]

theorem isFFStarOffender_of_le {X Y A : Subgroup (MulAut W)} (hAY : A ≤ Y)
    (hA : IsFFStarOffender X A) : IsFFStarOffender Y A :=
  ⟨hAY, hA.2⟩

theorem ffJ_ffJ (X : Subgroup (MulAut W)) : ffJ (ffJ X) = ffJ X :=
  le_antisymm (B6.ffJ_le _)
    (iSup₂_le fun _ hA => B6.le_ffJ (isFFStarOffender_of_le (B6.le_ffJ hA) hA))

end FFJ

section DualFF

variable {G : Type} [Group G] [Finite G]

theorem qInt_le_two_of_dualFF (hB : B513) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hK : quasithinIsQTKECat G) {M₀ V : Subgroup G}
    (hred : IsTwoReducedIn M₀ V) (hV0 : V ≠ ⊥) (hdual : IsDualFFInt M₀ V hred.2.2.1) :
    qInt M₀ V hred.2.2.1 ≤ 2 := by
  have hV := hred.2.2.1
  let _ : CommGroup ↥V := commGroupOfElemAbelian hV
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa [pow_two] using hV.2 v v.2)
  have hinj : Function.Injective (dualAct ↥V) := dualAct_injective hV2
  set A : Subgroup (MulAut ↥V) := autOn M₀ V with hA
  set Xd : Subgroup (MulAut (↥V →* Multiplicative (ZMod 2))) := A.map (dualAct ↥V) with hXd
  set Jd : Subgroup (MulAut (↥V →* Multiplicative (ZMod 2))) :=
    @ffJ (↥V →* Multiplicative (ZMod 2)) MonoidHom.instCommGroup Xd with hJd
  have hJle : Jd ≤ Xd := B6.ffJ_le Xd
  have hXN : Xd ≤ Subgroup.normalizer (Jd : Set _) := B6.le_normalizer_ffJ Xd
  have hO2A : pCoreOf 2 A = ⊥ := pCoreOf_autOn_eq_bot_of_isTwoReducedIn hred
  have hO2X : pCoreOf 2 Xd = ⊥ := pCoreOf_map_dualAct_eq_bot hV2 hO2A
  have hO2J : pCoreOf 2 Jd = ⊥ :=
    le_bot_iff.mp (hO2X ▸ pCoreOf_le_pCoreOf_of_normal hJle hXN)
  have hJJ : @ffJ (↥V →* Multiplicative (ZMod 2)) MonoidHom.instCommGroup Jd = Jd :=
    ffJ_ffJ Xd
  set X : Subgroup (MulAut ↥V) := A ⊓ Jd.comap (dualAct ↥V) with hX
  have hXmap : X.map (dualAct ↥V) = Jd := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro j hj
      obtain ⟨a, haA, rfl⟩ := hJle hj
      exact ⟨a, ⟨haA, hj⟩, rfl⟩
  have hXA : X ≤ A := inf_le_left
  let φ : ↥(Subgroup.normalizer (V : Set G)) →* MulAut (↥V →* Multiplicative (ZMod 2)) :=
    (dualAct ↥V).comp (conjAct V)
  set Y : Subgroup G := ((Jd.comap φ).map (Subgroup.normalizer (V : Set G)).subtype) ⊓ M₀ with hY
  have hYN : Y ≤ Subgroup.normalizer (V : Set G) := by
    rintro y ⟨⟨z, -, rfl⟩, -⟩
    exact z.2
  have hYM : Y ≤ M₀ := inf_le_right
  have hmemY : ∀ z : ↥(Subgroup.normalizer (V : Set G)), (z : G) ∈ M₀ → φ z ∈ Jd → (z : G) ∈ Y :=
    fun z hzM hz => ⟨⟨z, hz, rfl⟩, hzM⟩
  have hR : pCoreOf 2 M₀ ≤ Y := by
    intro x hx
    have hxC : x ∈ Subgroup.centralizer (V : Set G) :=
      A4.pCoreOf_le_centralizer_of_isTwoReducedIn hred hx
    have hxN : x ∈ Subgroup.normalizer (V : Set G) := Subgroup.centralizer_le_normalizer _ hxC
    refine hmemY ⟨x, hxN⟩ (pCoreOf_le 2 M₀ hx) ?_
    have h1 : conjAct V ⟨x, hxN⟩ = 1 := A4.conjAct_eq_one_iff.mpr hxC
    show (dualAct ↥V) (conjAct V ⟨x, hxN⟩) ∈ Jd
    rw [h1, map_one]
    exact Jd.one_mem
  have hYO : pCoreOf 2 Y ≠ ⊥ := by
    intro hbot
    have h1 : pCoreOf 2 M₀ ≤ pCoreOf 2 Y :=
      le_pCoreOf_of_le_normalizer 2 hR (hYM.trans (le_normalizer_pCoreOf 2 M₀))
        (pCoreOf_isPGroup 2 M₀)
    rw [hbot, le_bot_iff] at h1
    exact hV0 (le_bot_iff.mp ((A4.le_pCoreOf_of_isTwoReducedIn hred).trans h1.le))
  have hsq : IsSQTKSub Y :=
    ⟨kGroup_of_pCoreOf_ne_bot hK hs hnab hYO, stronglyQuasithin_of_pCoreOf_ne_bot hK hYO⟩
  have hmem : ∀ y : ↥Y, φ (Subgroup.inclusion hYN y) ∈ X.map (dualAct ↥V) := by
    intro y
    obtain ⟨⟨z, hzJ, hzy⟩, hyM⟩ := y.2
    have hz : z = Subgroup.inclusion hYN y := Subtype.ext hzy
    subst hz
    have haA : conjAct V (Subgroup.inclusion hYN y) ∈ A :=
      ⟨Subgroup.inclusion hYN y, hyM, rfl⟩
    exact ⟨conjAct V (Subgroup.inclusion hYN y), ⟨haA, hzJ⟩, rfl⟩
  let f : ↥Y →* ↥(X.map (dualAct ↥V)) :=
    (φ.comp (Subgroup.inclusion hYN)).codRestrict (X.map (dualAct ↥V)) hmem
  have hf : Function.Surjective f := by
    rintro ⟨w, a, ⟨haA, haJ⟩, rfl⟩
    obtain ⟨z, hzM, rfl⟩ := haA
    have hzY : (z : G) ∈ Y := hmemY z hzM haJ
    exact ⟨⟨z, hzY⟩, Subtype.ext rfl⟩
  have hW'2 : ∀ f : ↥V →* Multiplicative (ZMod 2), f ^ 2 = 1 := by
    intro f
    refine DFunLike.ext _ _ fun v => ?_
    show (f v) ^ 2 = 1
    generalize f v = x
    revert x
    decide
  have hne : Jd ≠ ⊥ := by
    obtain ⟨A₀, hA₀⟩ := ((B1_4_5 hW'2 Xd).out 1 2).mp hdual
    intro hbot
    exact hA₀.2.1 (le_bot_iff.mp (hbot ▸ B6.le_ffJ hA₀))
  have hXne : X ≠ ⊥ := by
    intro hbot
    apply hne
    rw [← hXmap, hbot, Subgroup.map_bot]
  have hfix : X.map (dualAct ↥V) =
      @ffJ (↥V →* Multiplicative (ZMod 2)) MonoidHom.instCommGroup (X.map (dualAct ↥V)) :=
    hXmap.trans (hJJ.symm.trans (congrArg
      (@ffJ (↥V →* Multiplicative (ZMod 2)) MonoidHom.instCommGroup) hXmap).symm)
  have hq := hB ↥V hV2 X hXne (hXmap ▸ hO2J) hfix
    ⟨↥Y, inferInstance, inferInstance, hsq.2, hsq.1, f, hf⟩
  exact (kq_anti_group hXA 2).trans hq

end DualFF

end CFSG.Quasithin
