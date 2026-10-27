module

public import CFSG.LocalAnalysis.WeakClosure81.EightTwentyP
public import CFSG.LocalAnalysis.WeakClosure81.EightTwentyPQ
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPSit
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPSetupB
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPPull

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsU3 IsL3 IsSp4 IsSL3)

variable {G : Type} [Group G] [Finite G]

private theorem wc820pp_elemAbOrderEight {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hrk : rk ↥V = 3) : ElemAbOrderEight ↥V := by
  have h2 : IsPGroup 2 ↥V := CFSG.Quasithin.isPGroup_two_of_sq_eq_one fun x =>
    Subtype.ext (by
      have hx := hV.2 (x : G) x.2
      simpa [pow_two] using hx)
  have hcard : Nat.card ↥V = 8 := by
    rw [CFSG.Quasithin.card_eq_two_pow_of_isPGroup h2, hrk]
    norm_num
  refine ⟨hcard, ?_, ?_⟩
  · haveI : IsMulCommutative ↥V := hV.1
    intro x y
    exact mul_comm' x y
  · intro x
    have hx := hV.2 (x : G) x.2
    exact Subtype.ext (by simpa [pow_two] using hx)

private theorem wc820pp_le_normalizer_cGrp {H T : Subgroup G} :
    H ≤ Subgroup.normalizer (cGrp H T : Set G) := by
  have h1 : H ≤ Subgroup.normalizer (H : Set G) := Subgroup.le_normalizer
  have h2 : H ≤ Subgroup.normalizer (eGrp H T : Set G) :=
    le_normalizer_conjClosure (omegaOneCenterOf T) H
  have h3 : H ≤ Subgroup.normalizer
      ((Subgroup.centralizer (eGrp H T : Set G) : Subgroup G) : Set G) :=
    CFSG.Quasithin.A1b.le_normalizer_centralizer h2
  have h4 : H ≤ Subgroup.normalizer
      ((H ⊓ Subgroup.centralizer (eGrp H T : Set G) : Subgroup G) : Set G) :=
    (le_inf h1 h3).trans Subgroup.inf_normalizer_le_normalizer_inf
  simpa [cGrp] using h4

private theorem wc820pp_of_hasQuotShape_bot {Q : Type} [Group Q] {K : Subgroup Q}
    {P : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → P X → P Y)
    (h : HasQuotShape K ((⊥ : Subgroup Q) : Set Q) P) : P ↥K := by
  obtain ⟨X, hX, ψ, hψsurj, hψker, hPX⟩ := h
  letI : Group X := hX
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx1 : (x : Q) = 1 := by
      have h := (hψker x).mp hx
      simpa using h
    exact Subtype.ext hx1
  exact hP (MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩).symm hPX

private theorem wc820pp_isU3_of_hasQuotShape_bot {Q : Type} [Group Q] {K : Subgroup Q}
    (h : HasQuotShape K ((⊥ : Subgroup Q) : Set Q) (fun X _ => IsU3 X 2)) : IsU3 ↥K 2 :=
  wc820pp_of_hasQuotShape_bot (P := fun X _ => IsU3 X 2) (fun e hh => hh.of_mulEquiv e) h

private theorem wc820pp_isL3_of_hasQuotShape_bot {Q : Type} [Group Q] {K : Subgroup Q}
    (h : HasQuotShape K ((⊥ : Subgroup Q) : Set Q) (fun X _ => IsL3 X 2)) : IsL3 ↥K 2 :=
  wc820pp_of_hasQuotShape_bot (P := fun X _ => IsL3 X 2) (fun e hh => hh.of_mulEquiv e) h

private theorem wc820pp_isSp4_of_hasQuotShape_bot {Q : Type} [Group Q] {K : Subgroup Q}
    (h : HasQuotShape K ((⊥ : Subgroup Q) : Set Q) (fun X _ => IsSp4 X 2)) : IsSp4 ↥K 2 :=
  wc820pp_of_hasQuotShape_bot (P := fun X _ => IsSp4 X 2) (fun e hh => hh.of_mulEquiv e) h

private theorem wc820pp_isSL3_of_hasQuotShape_bot {Q : Type} [Group Q] {K : Subgroup Q}
    (h : HasQuotShape K ((⊥ : Subgroup Q) : Set Q) (fun X _ => IsSL3 X 2)) : IsSL3 ↥K 2 :=
  wc820pp_of_hasQuotShape_bot (P := fun X _ => IsSL3 X 2)
    (fun e hh => ⟨(CFSG.Open.IsQuasisimple.congr e).mp hh.1,
      hh.2.quotient_center_of_mulEquiv e⟩) h

private theorem wc820pp_rankTwoShape_of_shapeRankTwo {Q : Type} [Group Q] {K : Subgroup Q}
    (h : ShapeRankTwoMod (⊥ : Subgroup Q) K) : RankTwoShape K := by
  rcases h with hL3 | hSL3 | hSp4
  · exact Or.inl (wc820pp_isL3_of_hasQuotShape_bot hL3)
  · exact Or.inr (Or.inr (wc820pp_isSL3_of_hasQuotShape_bot hSL3))
  · exact Or.inr (Or.inl (wc820pp_isSp4_of_hasQuotShape_bot hSp4))

theorem exists_section_GL32 (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS) {V H T A : Subgroup G}
    {i : ℕ} (h : Pre813 V H T i A) {Q : Type} [Group Q] {φ : ↥H →* Q}
    (hφ : IsBarMap H (cGrp H T) φ) :
    ∃ (E : Type) (_ : Group E) (W : Subgroup (MulAut E)) (X : Type) (_ : Group X)
      (ψ : ↥W →* X) (Φ : ↥(barSub H φ (H ⊓ normalizer (V : Set G))) →* X),
      ElemAbOrderEight E ∧ Function.Surjective ψ ∧
        ∀ x : ↥(barSub H φ (H ⊓ normalizer (V : Set G))), Φ x = 1 →
          (x : Q) ∈ barSub H φ (H ⊓ normalizer (V : Set G) ⊓ centralizer (V : Set G)) := by
  have hVab : IsElemAbelian 2 V := h.minCex.hyp.hyp7.1
  have hrk : rk ↥V = 3 := h.concl812.1
  set M₁ : Subgroup G := H ⊓ normalizer (V : Set G) with hM₁
  have hCM₁ : cGrp H T ≤ M₁ := by
    refine le_inf inf_le_left ?_
    exact (cGrp_le_kerMV h5_11 h5_13 h).trans (kerMV_le_normalizer V H)
  have hCmnorm : ((cGrp H T).subgroupOf M₁).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCM₁).mpr
      ((inf_le_left : M₁ ≤ H).trans (wc820pp_le_normalizer_cGrp (H := H) (T := T)))
  let ρ : ↥M₁ →* MulAut ↥V :=
    (Subgroup.normalizerMonoidHom (H := V)).comp
      (Subgroup.inclusion (inf_le_right : M₁ ≤ Subgroup.normalizer (V : Set G)))
  have hρapply : ∀ (m : ↥M₁) (y : ↥V),
      ((ρ m y : ↥V) : G) = (m : G) * (y : G) * (m : G)⁻¹ := fun m y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe V
      (Subgroup.inclusion (inf_le_right : M₁ ≤ Subgroup.normalizer (V : Set G)) m) y
  have hρker : ∀ m : ↥M₁, ρ m = 1 ↔ (m : G) ∈ M₁ ⊓ centralizer (V : Set G) := by
    intro m
    constructor
    · intro hm
      refine Subgroup.mem_inf.mpr ⟨m.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : ((ρ m) ⟨y, hy⟩ : G) = y := by rw [hm]; rfl
      rw [hρapply m ⟨y, hy⟩] at hy'
      have : (m : G) * y = y * (m : G) := by
        calc (m : G) * y = ((m : G) * y * (m : G)⁻¹) * (m : G) := by group
          _ = y * (m : G) := by rw [hy']
      exact this.symm
    · intro hm
      refine MulEquiv.ext fun y => ?_
      apply Subtype.ext
      rw [hρapply m y, MulAut.one_apply]
      have hcomm := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hm).2 (y : G) y.2
      rw [hcomm.symm]
      group
  let W : Subgroup (MulAut ↥V) := ρ.range
  let ρW : ↥M₁ →* ↥W :=
    ρ.codRestrict W (fun m => MonoidHom.mem_range.mpr ⟨m, rfl⟩)
  have hρWsurj : Function.Surjective ρW := by
    intro w
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp w.2
    exact ⟨m, Subtype.ext hm⟩
  let Cm : Subgroup ↥M₁ := (cGrp H T).subgroupOf M₁
  let W₀ : Subgroup ↥W := Cm.map ρW
  have hW₀ : W₀.Normal := hCmnorm.map ρW hρWsurj
  letI : W₀.Normal := hW₀
  let X : Type := ↥W ⧸ W₀
  let ψ : ↥W →* X := QuotientGroup.mk' W₀
  let π : ↥M₁ →* ↥(barSub H φ M₁) :=
    (φ.comp (Subgroup.inclusion (inf_le_left : M₁ ≤ H))).codRestrict (barSub H φ M₁)
      (fun m => mem_barSub.mpr ⟨Subgroup.inclusion inf_le_left m, m.2, rfl⟩)
  have hπsurj : Function.Surjective π := by
    intro y
    obtain ⟨k, hk, hkφ⟩ := mem_barSub.mp y.2
    refine ⟨⟨(k : G), hk⟩, ?_⟩
    apply Subtype.ext
    change φ (Subgroup.inclusion inf_le_left ⟨(k : G), hk⟩) = (y : Q)
    rw [show Subgroup.inclusion inf_le_left ⟨(k : G), hk⟩ = k from Subtype.ext rfl]
    exact hkφ
  have hπker : π.ker = Cm := by
    ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hm
      have h1 : φ (Subgroup.inclusion inf_le_left m) = 1 := by
        have h2 := congrArg Subtype.val hm
        simpa [π] using h2
      exact (hφ.ker_iff (Subgroup.inclusion inf_le_left m)).mp h1
    · intro hm
      apply Subtype.ext
      change φ (Subgroup.inclusion inf_le_left m) = 1
      exact (hφ.ker_iff (Subgroup.inclusion inf_le_left m)).mpr hm
  have hCm_le : Cm ≤ (ψ.comp ρW).ker := by
    intro c hc
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_map_of_mem ρW hc
  have hg_le : π.ker ≤ (ψ.comp ρW).ker := by
    rw [hπker]
    exact hCm_le
  let Φ : ↥(barSub H φ M₁) →* X :=
    (MonoidHom.liftOfSurjective π hπsurj) ⟨ψ.comp ρW, hg_le⟩
  have hΦπ : ∀ m : ↥M₁, Φ (π m) = ψ (ρW m) := fun m =>
    MonoidHom.liftOfRightInverse_comp_apply π (Function.surjInv hπsurj)
      (Function.rightInverse_surjInv hπsurj) ⟨ψ.comp ρW, hg_le⟩ m
  refine ⟨↥V, inferInstance, W, X, inferInstance, ψ, Φ, wc820pp_elemAbOrderEight hVab hrk,
    QuotientGroup.mk'_surjective W₀, ?_⟩
  intro x hx
  obtain ⟨m, rfl⟩ := hπsurj x
  have hx1 : ψ (ρW m) = 1 := by rw [← hΦπ m]; exact hx
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
  obtain ⟨c, hc, hcρ⟩ := Subgroup.mem_map.mp hx1
  have hρ1 : ρ (m * c⁻¹) = 1 := by
    have h1 : ρW (m * c⁻¹) = 1 := by
      rw [map_mul, map_inv, hcρ]
      group
    exact congrArg Subtype.val h1
  have hkerρ : ((m * c⁻¹ : ↥M₁) : G) ∈ M₁ ⊓ centralizer (V : Set G) :=
    (hρker (m * c⁻¹)).mp hρ1
  refine mem_barSub.mpr ⟨Subgroup.inclusion inf_le_left (m * c⁻¹), hkerρ, ?_⟩
  have hcC : (c : G) ∈ cGrp H T := hc
  have hφc : φ (Subgroup.inclusion inf_le_left c) = 1 :=
    (hφ.ker_iff (Subgroup.inclusion inf_le_left c)).mpr hcC
  show φ (Subgroup.inclusion inf_le_left (m * c⁻¹)) = (π m : Q)
  have hπm : (π m : Q) = φ (Subgroup.inclusion inf_le_left m) := rfl
  rw [hπm]
  have hsplit : Subgroup.inclusion inf_le_left (m * c⁻¹) =
      Subgroup.inclusion inf_le_left m * (Subgroup.inclusion inf_le_left c)⁻¹ := by
    rw [map_mul, map_inv]
  rw [hsplit, map_mul, map_inv, hφc, inv_one, mul_one]

theorem w3Claim820'_holds (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS)
    (hF0 : OddSchurMultiplierFact) (hF1 : InvolutionCentralizerFact)
    (hF2 : FourGroupInnerFact) (hF3 : BorelOvergroupFact) (hF6 : BorelGL32Fact) :
    W3Claim820' G := by
  intro V H T A L K i hS hUC
  have h : Pre813 V H T i A := hS.toPre
  obtain ⟨hK, L₀, hL₀⟩ := Pre813.exists_data810 h5_11 h5_13 h
  have hCnorm : ((cGrp H T).subgroupOf H).Normal := hS.concl813.comp.1
  obtain ⟨Q, hQgrp, hQfin, φ, hφ⟩ := exists_isBarMap hCnorm
  letI : Group Q := hQgrp
  letI : Finite Q := hQfin
  have hcfg : Cfg813 (barSub H φ T) (barSub H φ A) (barSub H φ (H ⊓ normalizer (V : Set G)))
      (barSub H φ (kerMV V H)) (barSub H φ L₀) :=
    Pre813.cfg h5_11 h5_13 h hK hL₀ hφ
  have hcaseQ : Case813UC (⊥ : Subgroup Q) ⊤ (barSub H φ T) (barSub H φ A) (barSub H φ L) :=
    Sit813.caseUC_barSub hS hφ hUC
  have hJ₀ : IsComponentOf (barSub H φ L) ⊤ := Sit813.isComponentOf_barSub hS hφ
  obtain ⟨E, hEgrp, W, X, hXgrp, ψ, Φ, hE8, hψsurj, hker⟩ :=
    exists_section_GL32 h5_11 h5_13 h hφ
  let N : Subgroup Q := barSub H φ (H ⊓ normalizer (V : Set G) ⊓ centralizer (V : Set G))
  have hsec : ∃ (E' : Type) (_ : Group E') (W' : Subgroup (MulAut E')) (X' : Type)
      (_ : Group X') (ψ' : ↥W' →* X')
      (Φ' : ↥(barSub H φ (H ⊓ normalizer (V : Set G))) →* X'),
      ElemAbOrderEight E' ∧ Function.Surjective ψ' ∧
        ∀ x : ↥(barSub H φ (H ⊓ normalizer (V : Set G))), Φ' x = 1 → (x : Q) ∈ N :=
    ⟨E, hEgrp, W, X, hXgrp, ψ, Φ, hE8, hψsurj, hker⟩
  have hcase : IsU3 ↥(barSub H φ L) 2 ∨ (RankTwoShape (barSub H φ L) ∧
      ∀ a ∈ barSub H φ A, ∀ t ∈ barSub H φ T ⊓ conjClosure (barSub H φ L) ⊤,
        a * t * a⁻¹ * t⁻¹ ∈ (⊥ : Subgroup Q)) := by
    rcases hcaseQ with hU3 | ⟨hrank, hcent⟩
    · exact Or.inl (wc820pp_isU3_of_hasQuotShape_bot hU3)
    · exact Or.inr ⟨wc820pp_rankTwoShape_of_shapeRankTwo hrank, hcent⟩
  have hAleN : barSub H φ A ≤ N :=
    Cfg813.A_le_of_section hF0 hF1 hF2 hF3 hF6 hcfg N hsec hJ₀ hcase
  obtain ⟨hAT, -⟩ := h.mem
  have hTH : T ≤ H := h.minCex.hyp.sylow.le.trans inf_le_left
  have hAH : A ≤ H := hAT.trans hTH
  have hHC : H ≤ Subgroup.normalizer (cGrp H T : Set G) := Sit813.le_normalizer_cGrp hS
  intro a ha
  have hbar : φ ⟨a, hAH ha⟩ ∈ barSub H φ A := mem_barSub.mpr ⟨⟨a, hAH ha⟩, ha, rfl⟩
  have hmemN : φ ⟨a, hAH ha⟩ ∈ N := hAleN hbar
  obtain ⟨q, hq, hqφ⟩ := mem_barSub.mp hmemN
  have hker : ((⟨a, hAH ha⟩ : ↥H) * q⁻¹) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hqφ]
    group
  have hC : a * (q : G)⁻¹ ∈ cGrp H T := by
    have h' := (hφ.ker_iff ((⟨a, hAH ha⟩ : ↥H) * q⁻¹)).mp hker
    simpa using h'
  have hqH : (q : G) ∈ H := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hq).1).1
  have hqnorm : (q : G) ∈ Subgroup.normalizer (cGrp H T : Set G) := hHC hqH
  have hqinvnorm : (q : G)⁻¹ ∈ Subgroup.normalizer (cGrp H T : Set G) :=
    (Subgroup.normalizer (cGrp H T : Set G)).inv_mem hqnorm
  have hqinv : (q : G)⁻¹ * a ∈ cGrp H T := by
    have hconj := (Subgroup.mem_normalizer_iff.mp hqinvnorm (a * (q : G)⁻¹)).mp hC
    have heq : (q : G)⁻¹ * a =
        (q : G)⁻¹ * (a * (q : G)⁻¹) * ((q : G)⁻¹)⁻¹ := by group
    rw [heq]
    exact hconj
  have haeq : a = (q : G) * ((q : G)⁻¹ * a) := by group
  rw [haeq]
  exact Subgroup.mul_mem_sup hq hqinv

end CFSG.LocalAnalysis.WeakClosure81

end
