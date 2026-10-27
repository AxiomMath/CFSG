module

public import CFSG.Quasithin.EmptyFaithful.SzC4Close
public import CFSG.Quasithin.EmptyFaithful.S153D52

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Quasithin.SBd7
  CFSG.Quasithin.S153D
open scoped commutatorElement Pointwise

namespace Stellmacher.PU.L3YC

section Conj

variable {G : Type} [Group G]

theorem comm_conjSub (g : G) (A B : Subgroup G) :
    ⁅B6.conjSub g A, B6.conjSub g B⁆ = B6.conjSub g ⁅A, B⁆ := by
  show ⁅A.map (MulAut.conj g).toMonoidHom, B.map (MulAut.conj g).toMonoidHom⁆ =
    ⁅A, B⁆.map (MulAut.conj g).toMonoidHom
  exact (Subgroup.map_commutator _ _ _).symm

theorem comm_eq_conjSub {A B : Subgroup G} (g : G) (h : ⁅A, B⁆ = A) :
    ⁅B6.conjSub g A, B6.conjSub g B⁆ = B6.conjSub g A := by
  rw [comm_conjSub, h]

theorem comm_eq_of_conjSub {A B : Subgroup G} (g : G)
    (h : ⁅B6.conjSub g A, B6.conjSub g B⁆ = B6.conjSub g A) : ⁅A, B⁆ = A := by
  rw [comm_conjSub] at h
  exact (B6.conjSub g).injective h

end Conj

theorem pu_f1_f2 (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hq : IsLnTwoQuot L 3) (c12 : Concl15312Two Yp L)
    (hV : ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥) (hYY : Yp = Y153 Mc M)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    {t' : G} (ht'T : t' ∈ T) (ht'S : t' ∉ Sgp153 T V₁)
    (hswap : B6.conjSub t' (YL153 Yp L) = YC153 Yp L)
    (h4 : MS93.IsC134Case4Corr (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) L) :
    ∃ Vc Vn : Subgroup G, ((Vc = V₁ ∧ Vn = V₂) ∨ (Vc = V₂ ∧ Vn = V₁)) ∧
      ⁅VZ T M, YC153 Yp L⁆ = Vc ∧ Vc = c134CQ (L ⊔ Sgp153 T V₁) L ∧
      ⁅VZ T M, YL153 Yp L⁆ = Vn ∧
      Vn ≤ ⁅centerOf (c134Q (L ⊔ Sgp153 T V₁) L), L⁆ := by
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hyp : Hyp153 G T Mc M := hh.hyp
  obtain ⟨hLc, hLn, -, -, -, hLq⟩ := c.conc
  have hLI : L ∈ cComp I := mem_cComp_of_mem_cComp_thompsonJ hLc
  have hLle : L ≤ I := le_of_mem_cComp hLI
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hLI
  have hYpL : Yp ≤ Subgroup.normalizer (L : Set G) := Yp_le_normalizer h37 h38 hh c.ctx.inH hLI
  have hRN : R153 T V₁ Yp ≤ Subgroup.normalizer (L : Set G) := c.c16.R_norm
  have hO : pCoreOf 2 (L ⊔ R153 T V₁ Yp) ≤ R153 T V₁ Yp :=
    pCoreOf_sup_R153_le c.facts hLI hLq hRN
  have hlab := SBd5.l3YLLabel_of_l3 h113 h37 h38 SBd3.l3SolvableOverSylow_holds G T Mc M V₁ V₂ Yp
    I L t c hq c12 hV hYY
  have hTS : T ≤ Subgroup.normalizer (Sgp153 T V₁ : Set G) :=
    Hyp153.T_le_normalizer_Sgp153 hyp hh.decomp
  have hSV₁ : Sgp153 T V₁ ≤ Subgroup.normalizer (V₁ : Set G) := inf_le_right
  have hTRn : Yp ⊔ T ≤ Subgroup.normalizer (R153 T V₁ Yp : Set G) :=
    (Hyp15310.lemma_15_3_11_five_case_one h113 hh hYY).2.2.1
  have hRS : R153 T V₁ Yp ≤ Sgp153 T V₁ := by
    intro r hr
    have hr' := c.facts.R_eq ▸ hr
    refine ⟨hr'.1, ?_⟩
    have h1 : r ∈ Subgroup.centralizer (V₁ : Set G) :=
      Subgroup.centralizer_le hh.decomp.le₁ hr'.2
    exact Subgroup.centralizer_le_normalizer (V₁ : Set G) h1
  have hS2 : IsPGroup 2 ↥(Sgp153 T V₁) := hyp.qtfe.sylow.1.to_le inf_le_left
  have hSTle : Sgp153 T V₁ ≤ T := inf_le_left
  set R : Subgroup G := R153 T V₁ Yp with hR
  set O : Subgroup G := pCoreOf 2 (L ⊔ R) with hOdef
  set Q : Subgroup G := ⁅O, L⁆ with hQ
  set W : Subgroup G := WL153 T M L with hW
  have hOL : L ≤ Subgroup.normalizer (O : Set G) := fun l hl =>
    le_normalizer_pCoreOf 2 (L ⊔ R) (Subgroup.mem_sup_left hl)
  have hYpR : Yp ≤ Subgroup.normalizer (R : Set G) := le_sup_left.trans hTRn
  have hTR : T ≤ Subgroup.normalizer (R : Set G) := le_sup_right.trans hTRn
  have hNO : ∀ g : G, g ∈ Subgroup.normalizer (L : Set G) → g ∈ Subgroup.normalizer (R : Set G) →
      g ∈ Subgroup.normalizer (O : Set G) := fun g h1 h2 =>
    normalizer_le_normalizer_pCoreOf 2 (L ⊔ R)
      (Subgroup.inf_normalizer_le_normalizer_sup L R ⟨h1, h2⟩)
  have hQO : Q ≤ O := by
    refine Subgroup.commutator_le.mpr fun x hx l hl => ?_
    have h1 : l * x⁻¹ * l⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp (hOL hl) _).mp (O.inv_mem hx)
    have e : x * l * x⁻¹ * l⁻¹ = x * (l * x⁻¹ * l⁻¹) := by group
    rw [commutatorElement_def, e]
    exact O.mul_mem hx h1
  have hQR : Q ≤ R := hQO.trans hO
  have hQS : Q ≤ Sgp153 T V₁ := hQR.trans hRS
  have hSQ : Sgp153 T V₁ ≤ Subgroup.normalizer (Q : Set G) := fun s hs =>
    SBd5.mem_normalizer_commutator_of (hNO s (hSL hs) (hTR (hSTle hs))) (hSL hs)
  have hLQ : L ≤ Subgroup.normalizer (Q : Set G) := fun l hl =>
    SBd5.mem_normalizer_commutator_of (hOL hl) (Subgroup.le_normalizer hl)
  have hWc : W ≤ centerOf O := WL_le_centerOf hh c.ctx c.facts hLI hO
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := fun l hl =>
    le_normalizer_conjClosure (VZ T M) L hl
  have hWab : IsElemAbelian 2 W := c.c16.reduced_LR.2.2.1
  have hWcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := fun x hx y hy => by
    have := hWab.1
    exact setLike_mul_comm hx hy
  have hUQ : ⁅W, L⁆ ≤ Q := Subgroup.commutator_mono (fun x hx => (hWc hx).1) le_rfl
  have hUW : ⁅W, L⁆ ≤ W := Subgroup.le_normalizer_iff_commutator_le_left.mp hLW
  have hUc : ∀ u ∈ ⁅W, L⁆, ∀ q ∈ Q, u * q = q * u := fun u hu q hq' =>
    (Subgroup.mem_centralizer_iff.mp (hWc (hUW hu)).2 q (hQO hq')).symm
  have hVab : ∀ a ∈ VZ T M, ∀ b ∈ VZ T M, a * b = b * a := fun a ha b hb => by
    have := hyp.elemAbelian.1
    exact setLike_mul_comm ha hb
  have hYLle : YL153 Yp L ≤ Yp ⊓ L := oTwoUpper_le _
  have hYL153 : YL153 Yp L ≤ Y153 Mc M := (hYLle.trans inf_le_left).trans (le_of_eq hYY)
  have hyfacts : ∀ y ∈ centralizerSection Yp L (pCoreOf 2 L), y ∈ Subgroup.normalizer (L : Set G) ∧
      y ∈ Subgroup.normalizer (Q : Set G) ∧ (∀ x ∈ L, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 L) := by
    intro y hy
    obtain ⟨hyYp, hyL, -, hyc⟩ := hy
    exact ⟨hyL, SBd5.mem_normalizer_commutator_of (hNO y hyL (hYpR hyYp)) hyL, hyc⟩
  have hΩ : ∀ n' ∈ Sgp153 T V₁, (∀ s ∈ Sgp153 T V₁, s * n' * s⁻¹ = n') → n' * n' = 1 →
      n' ∈ VZ T M := by
    intro n' hn' hnc hn2
    have h8 := (hyp.lemma_15_3_8 hh.decomp).1
    have hmem : n' ∈ omegaOneCenterOf (T ⊓ Subgroup.normalizer (V₁ : Set G)) :=
      Subgroup.subset_closure ⟨⟨hn', Subgroup.mem_centralizer_iff.mpr fun s hs => by
        have := hnc s hs
        exact mul_inv_eq_iff_eq_mul.mp this⟩, by rw [pow_two]; exact hn2⟩
    rw [h8] at hmem
    exact hmem.1
  have hCnt : ⁅VZ T M, YC153 Yp L⁆ ≠ ⊥ := by
    intro hb
    apply hV
    rw [eq_bot_iff]
    refine Subgroup.commutator_le.mpr fun v hv y hy => ?_
    have hMN := hyp.le_normalizer (hyp.T_le ht'T)
    have hv' : t' * v * t'⁻¹ ∈ VZ T M := (Subgroup.mem_normalizer_iff.mp hMN v).mp hv
    have hy' : t' * y * t'⁻¹ ∈ YC153 Yp L := by
      rw [← hswap, B6.mem_conjSub]
      have e : t'⁻¹ * (t' * y * t'⁻¹) * t' = y := by group
      rw [e]
      exact hy
    have h1 : ⁅t' * v * t'⁻¹, t' * y * t'⁻¹⁆ ∈ (⊥ : Subgroup G) :=
      hb ▸ Subgroup.commutator_mem_commutator hv' hy'
    rw [Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    have e : ⁅v, y⁆ = t'⁻¹ * ⁅t' * v * t'⁻¹, t' * y * t'⁻¹⁆ * t' := by
      simp only [commutatorElement_def]
      group
    rw [e, h1]
    group
  have hYLgen : ∀ K : Subgroup G, (∀ y ∈ YL153 Yp L, Odd (orderOf y) → y ∈ K) →
      YL153 Yp L ≤ K := by
    intro K hK
    refine (Subgroup.closure_le K).mpr ?_
    rintro y ⟨hyX, hyodd⟩
    exact hK y (mem_oTwoUpper_of_odd hyX hyodd) hyodd
  have hYCgen : ∀ K : Subgroup G, (∀ y ∈ YC153 Yp L, Odd (orderOf y) → y ∈ K) →
      YC153 Yp L ≤ K := by
    intro K hK
    refine (Subgroup.closure_le K).mpr ?_
    rintro y ⟨hyX, hyodd⟩
    exact hK y (mem_oTwoUpper_of_odd hyX hyodd) hyodd
  have hsqV : ∀ a ∈ VZ T M, a * a = 1 := fun a ha => by
    have := hyp.elemAbelian.2 a ha
    rw [pow_two] at this
    exact this
  have hQeq : c134Q (L ⊔ Sgp153 T V₁) L = Q := by
    rw [c134Q_sup_eq hperf hSL hRN]
    rfl
  obtain ⟨⟨n, F, _, _, α, hFc, hα, hE2, -, -, -, -, -, -⟩, -⟩ := h4
  unfold c134CQ at hE2
  rw [hQeq] at hE2
  have hF : Fintype.card F = 2 := SBd5.card_eq_two_of_modO2Surj hq hFc hα
  have hn1 : n = 1 := by
    have h2 : 2 ^ n = 2 ^ 1 := by rw [← hFc, hF]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h2
  subst hn1
  obtain ⟨hC4', hCsq'⟩ := isE2_card_sq hE2
  have hC4 : Nat.card ↥(Q ⊓ Subgroup.centralizer (L : Set G)) = 4 := by
    rw [hC4']
    norm_num
  have hCsq : ∀ c ∈ Q ⊓ Subgroup.centralizer (L : Set G), c * c = 1 := fun c hc =>
    congrArg Subtype.val (hCsq' ⟨c, hc⟩)
  have hC1 : Q ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hC4
    omega
  have hSC : Sgp153 T V₁ ≤
      Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
    fun s hs => Subgroup.inf_normalizer_le_normalizer_inf ⟨hSQ hs,
      S153F.mem_normalizer_centralizer_of_mem_normalizer (hSL hs)⟩
  obtain ⟨c₀, hc₀C, hc₀1, hc₀sq, hc₀S⟩ :=
    SzC4.exists_fixed_involution hS2 (inf_le_left.trans hQS) hSC hC1 hCsq
  have hc₀V : c₀ ∈ VZ T M :=
    hΩ c₀ (inf_le_left.trans hQS hc₀C) (fun s hs => mul_inv_eq_iff_eq_mul.mpr (hc₀S s hs)) hc₀sq
  have hYLL : YL153 Yp L ≤ L := fun y hy => (hYLle hy).2
  have hc₀YL : ∀ y ∈ YL153 Yp L, y * c₀ * y⁻¹ = c₀ := fun y hy =>
    mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_iff.mp hc₀C.2 y (hYLL hy))
  have hYLN := Hyp153.Y153_le_normalizer_V h113 hyp hh.decomp
  obtain ⟨hswV₁, hswV₂⟩ := szN3_conj_V_swap hyp hh.decomp ht'T ht'S
  obtain ⟨Vc, Vn, hlabel, hsup, hc4, hn4, hYLc, hYLn, hYCn, hYCc, hcommVn, hcommVc⟩ :
      ∃ Vc Vn : Subgroup G, ((Vc = V₁ ∧ Vn = V₂) ∨ (Vc = V₂ ∧ Vn = V₁)) ∧
        Vc ⊔ Vn = VZ T M ∧ Nat.card Vc = 4 ∧ Nat.card Vn = 4 ∧
        YL153 Yp L ≤ Subgroup.centralizer (Vc : Set G) ∧
        YL153 Yp L ≤ Subgroup.normalizer (Vn : Set G) ∧
        YC153 Yp L ≤ Subgroup.centralizer (Vn : Set G) ∧
        YC153 Yp L ≤ Subgroup.normalizer (Vc : Set G) ∧
        ⁅Vn, YL153 Yp L⁆ = Vn ∧ ⁅Vc, YC153 Yp L⁆ = Vc := by
    rcases hlab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hn : ⁅V₂, YL153 Yp L⁆ = V₂ := by
        rw [h1]
        exact hyp.commutator_V₂_Yplus h113 hh.decomp
      have hc : ⁅V₁, YC153 Yp L⁆ = V₁ := by
        have := comm_eq_conjSub t' hn
        rwa [hswV₂, hswap] at this
      refine ⟨V₁, V₂, Or.inl ⟨rfl, rfl⟩, hh.decomp.sup, hh.decomp.card₁, hh.decomp.card₂, ?_,
        fun y hy => hYLN.2 (hYL153 hy), ?_, ?_, hn, hc⟩
      · rw [h1]; exact (oTwoUpper_le _).trans inf_le_right
      · rw [h2]; exact (oTwoUpper_le _).trans inf_le_right
      · intro y hy
        apply hYLN.1
        rw [h2] at hy
        exact ((oTwoUpper_le _).trans inf_le_left) hy
    · have hc : ⁅V₂, YC153 Yp L⁆ = V₂ := by
        rw [h2]
        exact hyp.commutator_V₂_Yplus h113 hh.decomp
      have hn : ⁅V₁, YL153 Yp L⁆ = V₁ :=
        comm_eq_of_conjSub t' (by rw [hswV₁, hswap]; exact hc)
      refine ⟨V₂, V₁, Or.inr ⟨rfl, rfl⟩, by rw [sup_comm]; exact hh.decomp.sup,
        hh.decomp.card₂, hh.decomp.card₁, ?_, fun y hy => hYLN.1 (hYL153 hy), ?_, ?_, hn, hc⟩
      · rw [h1]; exact (oTwoUpper_le _).trans inf_le_right
      · rw [h2]; exact (oTwoUpper_le _).trans inf_le_right
      · intro y hy
        apply hYLN.2
        rw [h2] at hy
        exact ((oTwoUpper_le _).trans inf_le_left) hy
  have hVcV : Vc ≤ VZ T M := hsup ▸ le_sup_left
  have hVnV : Vn ≤ VZ T M := hsup ▸ le_sup_right
  have hc₀Vc : c₀ ∈ Vc :=
    SzC4.fixed_mem_Vc hsup hVab hn4 hsqV hYLc hYLn hYLgen hV hc₀V hc₀YL
  have hYCC : ∀ y ∈ YC153 Yp L, ∀ x ∈ Q ⊓ Subgroup.centralizer (L : Set G),
      y * x * y⁻¹ ∈ Q ⊓ Subgroup.centralizer (L : Set G) := by
    have hle : YC153 Yp L ≤
        Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro y ⟨hyX, -⟩
      obtain ⟨hyL, hyQ, -⟩ := hyfacts y hyX
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hyQ,
        S153F.mem_normalizer_centralizer_of_mem_normalizer hyL⟩
    intro y hy x hx
    exact (Subgroup.mem_normalizer_iff.mp (hle hy) x).mp hx
  have hVcC : Vc ≤ Q ⊓ Subgroup.centralizer (L : Set G) :=
    SzC4.Vc_le_of_moved hsup hVab hc4 hsqV hYCn hYCc hYCgen hCnt hYCC hc₀C hc₀Vc hc₀1
  have hF1le : ⁅VZ T M, YC153 Yp L⁆ ≤ Vc :=
    SBd6.comm_le_of_decomp hVab (by rw [sup_comm]; exact hsup) hYCn hYCc
  have hF1 : ⁅VZ T M, YC153 Yp L⁆ = Vc :=
    le_antisymm hF1le (hcommVc ▸ Subgroup.commutator_mono hVcV le_rfl)
  have hVcCQ : Vc = c134CQ (L ⊔ Sgp153 T V₁) L := by
    rw [c134CQ, hQeq]
    exact Subgroup.eq_of_le_of_card_ge hVcC (by rw [hC4, hc4])
  have hF2le : ⁅VZ T M, YL153 Yp L⁆ ≤ Vn :=
    SBd6.comm_le_of_decomp hVab hsup hYLc hYLn
  have hF2 : ⁅VZ T M, YL153 Yp L⁆ = Vn :=
    le_antisymm hF2le (hcommVn ▸ Subgroup.commutator_mono hVnV le_rfl)
  have hVLU : ⁅VZ T M, YL153 Yp L⁆ ≤ ⁅W, L⁆ :=
    Subgroup.commutator_mono (le_conjClosure (VZ T M) L) (hYLle.trans inf_le_right)
  have hVnQ : Vn ≤ Q := hF2 ▸ hVLU.trans hUQ
  have hQC : ∀ q ∈ Q, ∀ v ∈ VZ T M, v * q = q * v := by
    intro q hq v hv
    have hqR : q ∈ R153 T V₁ Yp := hQR hq
    have hr' : q ∈ T ⊓ Subgroup.centralizer (VZ T M : Set G) := by
      rw [← c.facts.R_eq]
      exact hqR
    exact Subgroup.mem_centralizer_iff.mp hr'.2 v hv
  have hVnZ : Vn ≤ centerOf Q := fun x hx =>
    ⟨hVnQ hx, Subgroup.mem_centralizer_iff.mpr fun q hq => (hQC q hq x (hVnV hx)).symm⟩
  have hF2U : Vn ≤ ⁅centerOf (c134Q (L ⊔ Sgp153 T V₁) L), L⁆ := by
    rw [hQeq]
    calc Vn = ⁅Vn, YL153 Yp L⁆ := hcommVn.symm
      _ ≤ ⁅centerOf Q, L⁆ := Subgroup.commutator_mono hVnZ hYLL
  exact ⟨Vc, Vn, hlabel, hF1, hVcCQ, hF2, hF2U⟩
end Stellmacher.PU.L3YC

end CFSG.Quasithin
