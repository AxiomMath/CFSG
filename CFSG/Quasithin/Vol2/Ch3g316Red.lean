module

public import CFSG.Quasithin.Vol2.Ch3zCmp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellElem

public section

namespace CFSG.Quasithin.Ch3g316

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
  CFSG.Quasithin.D15Proof
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commutator_twoResidual_pCoreOf_le {H T M₂ R : Subgroup G} (hmp : MinParabolic H T M₂)
    (hRT : R ≤ T) (hTR : T ≤ Subgroup.normalizer (R : Set G)) (hJR : thompsonJ T ≤ R)
    (hJH : ¬ thompsonJ T ≤ pCoreOf 2 H)
    (hQn : H ≤ Subgroup.normalizer ((R ⊓ pCoreOf 2 H : Subgroup G) : Set G)) :
    ⁅twoResidual H, pCoreOf 2 H⁆ ≤ R ⊓ pCoreOf 2 H := by
  have hTH : T ≤ H := hmp.isSylow.1
  have hYn : H ≤ Subgroup.normalizer
      ((centralizerMod (R ⊓ pCoreOf 2 H) H (pCoreOf 2 H) : Subgroup G) : Set G) :=
    le_normalizer_centralizerMod hQn Subgroup.le_normalizer (le_normalizer_pCoreOf 2 H)
  have hJY : thompsonJ T ≤ centralizerMod (R ⊓ pCoreOf 2 H) H (pCoreOf 2 H) := by
    intro j hj
    have hjR : j ∈ R := hJR hj
    have hjT : j ∈ T := hRT hjR
    refine ⟨hTH hjT, hQn (hTH hjT), fun q hq => ⟨?_, ?_⟩⟩
    · have hqT : q ∈ T := B6.pCoreOf_two_le_of_isSylowTwoOf hmp.isSylow hq
      have h1 : q * j⁻¹ * q⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hTR hqT) _).mp (R.inv_mem hjR)
      have e : j * q * j⁻¹ * q⁻¹ = j * (q * j⁻¹ * q⁻¹) := by group
      rw [e]
      exact R.mul_mem hjR h1
    · have h1 : j * q * j⁻¹ ∈ pCoreOf 2 H :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (hTH hjT)) q).mp hq
      exact (pCoreOf 2 H).mul_mem h1 ((pCoreOf 2 H).inv_mem hq)
  rcases hmp.le_kerIn_or_twoResidual_le (centralizerMod_le_left _ _ _) hYn with h | h
  · exact absurd (hmp.le_pCoreOf_of_isPGroup_of_le_kerIn
      (hmp.isSylow.2.1.to_le (hJR.trans hRT)) (hJY.trans h)) hJH
  · rw [Subgroup.commutator_le]
    intro k hk q hq
    exact (h hk).2.2 q hq

theorem d125_noquad (hB : B69One) {H T M₂ U L N A : Subgroup G} (hmp : MinParabolic H T M₂)
    (hsqtk : IsSQTKSub H) (hUT : U ≤ T) (hUe : IsElemAbelian 2 U) (hstep : IsChiefStep H U L N)
    (hnc : ¬ IsCentralStep H L N) (hAT : A ≤ T) (hAe : IsElemAbelian 2 A) :
    (centralizerMod L A N).relIndex A ≤ (centralizerMod L N A).relIndex N := by
  have hTH : T ≤ H := hmp.isSylow.1
  have hUH : U ≤ H := hUT.trans hTH
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hNU : N ≤ U := hstep.1.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hNU.trans hUH).trans hHL
  have hAH : A ≤ H := hAT.trans hTH
  have hE := isElemAbelian_secImg_of_le (L := L) hUe hNU
  by_contra hlt
  push Not at hlt
  have hnt : ¬ ∀ b ∈ A, ∀ e ∈ N, b * e * b⁻¹ * e⁻¹ ∈ L := by
    intro hall
    have hCA : centralizerMod L A N = A := le_antisymm (centralizerMod_le_left _ _ _)
      fun b hb => ⟨hb, hHL (hAH hb), hall b hb⟩
    rw [hCA, Subgroup.relIndex_self] at hlt
    exact absurd hlt (not_lt.mpr (Nat.one_le_iff_ne_zero.mpr (relIndex_ne_zero _ _)))
  have hStrong := isStrongFFModule_autOn_secImg hE hNL hHL hHN hAH hAe hnt hlt
  set A_ := Subgroup.normalizer (L : Set G) with hAdef
  set E := secImg A_ L N with hEdef
  set X := autOn (secImg A_ L H) E with hXdef
  let _ : CommGroup ↥E := commGroupOfElemAbelian hE
  have hsq' : ∀ v : ↥E, v ^ 2 = 1 := fun v => Subtype.ext (hE.2 v v.2)
  have hmemE : ∀ g : ↥H, secMk A_ L (Subgroup.inclusion hHL g) ∈
      Subgroup.normalizer (E : Set (SecQuot A_ L)) := fun g =>
    secMk_mem_normalizer_secImg (hHN g.2)
  let β : ↥H →* ↥(Subgroup.normalizer (E : Set (SecQuot A_ L))) :=
    ((secMk A_ L).comp (Subgroup.inclusion hHL)).codRestrict _ hmemE
  let ψ : ↥H →* MulAut ↥E := (conjAct E).comp β
  have hψX : ∀ g : ↥H, ψ g ∈ X := fun g =>
    Subgroup.mem_map.mpr ⟨β g, Subgroup.mem_subgroupOf.mpr
      (secMk_mem_secImg (A := A_) (B := L) (X := H) (x := Subgroup.inclusion hHL g) g.2), rfl⟩
  let φ : ↥H →* ↥X := ψ.codRestrict X hψX
  have hφsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨a, haG, hay⟩ := mem_secImg.mp (Subgroup.mem_subgroupOf.mp hy)
    refine ⟨⟨a, haG⟩, Subtype.ext ?_⟩
    show conjAct E (β ⟨a, haG⟩) = conjAct E y
    congr 1
    exact Subtype.ext hay
  have hker : φ.ker ≤ M₂.subgroupOf H := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have hψ1 : ψ g = 1 := congrArg Subtype.val hg
    have hcent : ((β g : ↥(Subgroup.normalizer (E : Set (SecQuot A_ L)))) : SecQuot A_ L) ∈
        Subgroup.centralizer (E : Set (SecQuot A_ L)) := A4.conjAct_eq_one_iff.mp hψ1
    have hgC : (g : G) ∈ centralizerMod L H N := by
      refine ⟨g.2, hHL g.2, fun n hn => ?_⟩
      have hnE : secMk A_ L ⟨n, hNL hn⟩ ∈ E := secMk_mem_secImg (A := A_) (B := L) (X := N) hn
      have hcomm := Subgroup.mem_centralizer_iff.mp hcent _ hnE
      have h1 : secMk A_ L (⟨g, hHL g.2⟩ * ⟨n, hNL hn⟩ * ⟨g, hHL g.2⟩⁻¹ * ⟨n, hNL hn⟩⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        have hc : secMk A_ L ⟨n, hNL hn⟩ * secMk A_ L ⟨g, hHL g.2⟩ =
            secMk A_ L ⟨g, hHL g.2⟩ * secMk A_ L ⟨n, hNL hn⟩ := hcomm
        rw [← hc]
        group
      exact secMk_eq_one_iff.mp h1
    have hk := centralizerMod_le_kerIn hmp hUT hstep hnc hgC
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hk 1 H.one_mem)
  have hmpX := MinParabolic.map_of_surjective hmp.subgroupOf hφsurj hker
  have hO2 : pCoreOf 2 (⊤ : Subgroup ↥X) = ⊥ := by
    set Q : Subgroup ↥X := pCoreOf 2 (⊤ : Subgroup ↥X) with hQdef
    have hQn : Q.Normal :=
      Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_pCoreOf 2 (⊤ : Subgroup ↥X)))
    have hQ := normal_two_eq_bot hUH hstep hE (Q.map X.subtype) (Subgroup.map_subtype_le Q)
      (by
        have e : (Q.map X.subtype).subgroupOf X = Q :=
          Subgroup.comap_map_eq_self_of_injective X.subtype_injective Q
        rw [e]
        exact hQn)
      ((pCoreOf_isPGroup 2 (⊤ : Subgroup ↥X)).map X.subtype)
    exact (Subgroup.map_eq_bot_iff_of_injective Q X.subtype_injective).mp hQ
  exact hB E hsq' X _ _ ⟨↥H, inferInstance, inferInstance, hsqtk.2, hsqtk.1, φ, hφsurj⟩ hmpX hO2
    hStrong

omit [Finite G] in
theorem le_normalizer_centralizer {H V : Subgroup G}
    (hHV : H ≤ Subgroup.normalizer (V : Set G)) :
    H ≤ Subgroup.normalizer ((Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (V : Set G), ∀ c ∈ Subgroup.centralizer (V : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro v hv
    have hv' : g⁻¹ * v * g ∈ V := (Subgroup.mem_normalizer_iff''.mp hg v).mp hv
    have h1 := hc _ hv'
    calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * v := by group
  intro g hg
  refine B6.mem_normalizer_of_forall_mem (fun c hc => key g (hHV hg) c hc) fun c hc => ?_
  simpa using key g⁻¹ (Subgroup.inv_mem _ (hHV hg)) c hc

theorem le_pCoreOf_of_le_centralizer {H T M₂ V X : Subgroup G} (hmp : MinParabolic H T M₂)
    (hHV : H ≤ Subgroup.normalizer (V : Set G))
    (hK : ¬ twoResidual H ≤ Subgroup.centralizer (V : Set G)) (hXH : X ≤ H) (hX : IsPGroup 2 X)
    (hXV : X ≤ Subgroup.centralizer (V : Set G)) : X ≤ pCoreOf 2 H := by
  have hCn : H ≤ Subgroup.normalizer ((H ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) :
      Set G) := fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hg, le_normalizer_centralizer hHV hg⟩
  have hCJ := hmp.le_kerIn_of_not_twoResidual_le inf_le_left hCn
    (fun hle => hK (hle.trans inf_le_right))
  exact hmp.le_pCoreOf_of_isPGroup_of_le_kerIn hX (le_inf hXH hXV |>.trans hCJ)

omit [Finite G] in
theorem exists_isMaxElemAbelian_not_le_pCoreOf {T Q : Subgroup G} (hJ : ¬ thompsonJ T ≤ Q) :
    ∃ A : Subgroup G, IsMaxElemAbelian T A ∧ ¬ A ≤ Q := by
  by_contra hall
  push Not at hall
  exact hJ (iSup₂_le fun A hA => hall A hA)

theorem relIndex_centralizer_le {T A U : Subgroup G} (hA : IsMaxElemAbelian T A) (hUT : U ≤ T)
    (hUe : IsElemAbelian 2 U) :
    (Subgroup.centralizer (A : Set G)).relIndex U ≤
      (Subgroup.centralizer (U : Set G)).relIndex A := by
  have hcard : ∀ X Y : Subgroup G, Nat.card ((Subgroup.centralizer (X : Set G)).subgroupOf Y) =
      Nat.card ↥(Y ⊓ Subgroup.centralizer (X : Set G)) := fun X Y => by
    rw [← Subgroup.inf_subgroupOf_right (Subgroup.centralizer (X : Set G)) Y, inf_comm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  obtain ⟨-, h⟩ := Setup.Campbell.action_inequality hA hUT hUe
  have h1 := ((Subgroup.centralizer (A : Set G)).subgroupOf U).card_mul_index
  have h2 := ((Subgroup.centralizer (U : Set G)).subgroupOf A).card_mul_index
  rw [hcard] at h1 h2
  rw [← h1, ← h2, ← Subgroup.relIndex, ← Subgroup.relIndex] at h
  have hpos : 0 < Nat.card ↥(U ⊓ Subgroup.centralizer (A : Set G)) *
      Nat.card ↥(A ⊓ Subgroup.centralizer (U : Set G)) := Nat.mul_pos Nat.card_pos Nat.card_pos
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc Nat.card ↥(U ⊓ Subgroup.centralizer (A : Set G)) *
        Nat.card ↥(A ⊓ Subgroup.centralizer (U : Set G)) *
        (Subgroup.centralizer (A : Set G)).relIndex U =
      Nat.card ↥(U ⊓ Subgroup.centralizer (A : Set G)) *
        (Subgroup.centralizer (A : Set G)).relIndex U *
        Nat.card ↥(A ⊓ Subgroup.centralizer (U : Set G)) := by ring
    _ ≤ Nat.card ↥(A ⊓ Subgroup.centralizer (U : Set G)) *
        (Subgroup.centralizer (U : Set G)).relIndex A *
        Nat.card ↥(U ⊓ Subgroup.centralizer (A : Set G)) := h
    _ = Nat.card ↥(U ⊓ Subgroup.centralizer (A : Set G)) *
        Nat.card ↥(A ⊓ Subgroup.centralizer (U : Set G)) *
        (Subgroup.centralizer (U : Set G)).relIndex A := by ring

omit [Finite G] in
theorem commutator_commutator_swap {U : Subgroup G} (hUa : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x)
    {q k : G} (hq : ∀ u ∈ U, q * u * q⁻¹ ∈ U) (hk : ∀ u ∈ U, k * u * k⁻¹ ∈ U)
    (hc : ∀ u ∈ U, ⁅q, k⁆ * u = u * ⁅q, k⁆) {x : G} (hx : x ∈ U) :
    ⁅⁅x, k⁆, q⁆ = ⁅⁅x, q⁆, k⁆ := by
  have hy : k * x * k⁻¹ ∈ U := hk x hx
  have hz : q * x * q⁻¹ ∈ U := hq x hx
  have hw' : k * (q * x * q⁻¹) * k⁻¹ ∈ U := hk _ hz
  have hww : q * (k * x * k⁻¹) * q⁻¹ = k * (q * x * q⁻¹) * k⁻¹ := by
    have h := hc _ hw'
    calc q * (k * x * k⁻¹) * q⁻¹
        = ⁅q, k⁆ * (k * (q * x * q⁻¹) * k⁻¹) * ⁅q, k⁆⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = k * (q * x * q⁻¹) * k⁻¹ := by rw [h]; group
  have e1 : ⁅⁅x, k⁆, q⁆ = x * (k * x * k⁻¹)⁻¹ * (q * (k * x * k⁻¹) * q⁻¹) * (q * x * q⁻¹)⁻¹ := by
    simp only [commutatorElement_def]; group
  have e2 : ⁅⁅x, q⁆, k⁆ = x * (q * x * q⁻¹)⁻¹ * (k * (q * x * q⁻¹) * k⁻¹) * (k * x * k⁻¹)⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e1, e2, hww]
  have ha : (k * x * k⁻¹)⁻¹ ∈ U := U.inv_mem hy
  have hc' : (q * x * q⁻¹)⁻¹ ∈ U := U.inv_mem hz
  have key : (k * x * k⁻¹)⁻¹ * (k * (q * x * q⁻¹) * k⁻¹) * (q * x * q⁻¹)⁻¹ =
      (q * x * q⁻¹)⁻¹ * (k * (q * x * q⁻¹) * k⁻¹) * (k * x * k⁻¹)⁻¹ := by
    set a := (k * x * k⁻¹)⁻¹
    set b := k * (q * x * q⁻¹) * k⁻¹
    set c := (q * x * q⁻¹)⁻¹
    calc a * b * c = a * (b * c) := mul_assoc _ _ _
      _ = a * (c * b) := by rw [hUa b hw' c hc']
      _ = (a * c) * b := (mul_assoc _ _ _).symm
      _ = (c * a) * b := by rw [hUa a ha c hc']
      _ = c * (a * b) := mul_assoc _ _ _
      _ = c * (b * a) := by rw [hUa a ha b hw']
      _ = c * b * a := (mul_assoc _ _ _).symm
  calc x * (k * x * k⁻¹)⁻¹ * (k * (q * x * q⁻¹) * k⁻¹) * (q * x * q⁻¹)⁻¹
      = x * ((k * x * k⁻¹)⁻¹ * (k * (q * x * q⁻¹) * k⁻¹) * (q * x * q⁻¹)⁻¹) := by
        simp only [mul_assoc]
    _ = x * ((q * x * q⁻¹)⁻¹ * (k * (q * x * q⁻¹) * k⁻¹) * (k * x * k⁻¹)⁻¹) := by rw [key]
    _ = x * (q * x * q⁻¹)⁻¹ * (k * (q * x * q⁻¹) * k⁻¹) * (k * x * k⁻¹)⁻¹ := by
        simp only [mul_assoc]

theorem isChiefSeriesFrom_one (hB1 : B69One) {H T M₂ U A : Subgroup G}
    (hmp : MinParabolic H T M₂) (hsq : IsSQTKSub H) (hUT : U ≤ T) (hUe : IsElemAbelian 2 U)
    (hUn : H ≤ Subgroup.normalizer (U : Set G)) (hA : IsMaxElemAbelian T A)
    (hAQ : ¬ A ≤ pCoreOf 2 H) (hBC : A ⊓ pCoreOf 2 H ≤ Subgroup.centralizer (U : Set G))
    (hK : ¬ twoResidual H ≤ Subgroup.centralizer (U : Set G)) :
    IsChiefSeriesFrom H U U 1 := by
  have hTH : T ≤ H := hmp.isSylow.1
  have hUH : U ≤ H := hUT.trans hTH
  have hUp : IsPGroup 2 U := hmp.isSylow.2.1.to_le hUT
  have hAT : A ≤ T := hA.1
  have hAe : IsElemAbelian 2 A := hA.2.1
  have hAH : A ≤ H := hAT.trans hTH
  set B := A ⊓ pCoreOf 2 H with hB
  have hBA : B ≤ A := inf_le_left
  have hCA : A ⊓ Subgroup.centralizer (U : Set G) = B := by
    refine le_antisymm (le_inf inf_le_left ?_) (le_inf hBA hBC)
    exact le_pCoreOf_of_le_centralizer hmp hUn hK (inf_le_left.trans hAH)
      (hmp.isSylow.2.1.to_le (inf_le_left.trans hAT)) inf_le_right
  have hCAidx : (Subgroup.centralizer (U : Set G)).relIndex A = B.relIndex A := by
    rw [← Subgroup.inf_relIndex_left, ← hCA, inf_comm]
  have hk2 : 2 ≤ B.relIndex A := by
    have hne : B.relIndex A ≠ 1 := fun h => hAQ ((Subgroup.relIndex_eq_one.mp h).trans inf_le_right)
    have hpos := Nat.pos_of_ne_zero (relIndex_ne_zero B A)
    omega
  have hk : ∀ L N : Subgroup G, IsChiefStep H U L N → ¬ IsCentralStep H L N →
      B.relIndex A ≤ (centralizerMod L N A).relIndex N := by
    intro L N hstep hnc
    have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
    have hcm : centralizerMod L A N = B := by
      refine le_antisymm (le_inf (centralizerMod_le_left _ _ _) ?_) ?_
      · refine hmp.le_pCoreOf_of_isPGroup_of_le_kerIn
          (hmp.isSylow.2.1.to_le ((centralizerMod_le_left _ _ _).trans hAT)) ?_
        exact fun x hx => centralizerMod_le_kerIn hmp hUT hstep hnc
          (centralizerMod_mono_left N hAH hx)
      · intro x hx
        refine ⟨hBA hx, hHL (hAH (hBA hx)), fun n hn => ?_⟩
        have h1 : x * n = n * x := (Subgroup.mem_centralizer_iff.mp (hBC hx) n (hstep.1.1 hn)).symm
        rw [h1, mul_inv_cancel_right, mul_inv_cancel]
        exact L.one_mem
    rw [← hcm]
    exact d125_noquad hB1 hmp hsq hUT hUe hstep hnc hAT hAe
  obtain ⟨n, hn⟩ := exists_isChiefSeriesFrom U
    (⟨le_rfl, fun g hg x hx => (Subgroup.mem_normalizer_iff.mp (hUn hg) x).mp hx⟩ :
      IsNormalIn H U U)
  have hpow := pow_le_relIndex hUH hAH hk hn
  have hineq := relIndex_centralizer_le hA hUT hUe
  have hn1 : n ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have h1 : B.relIndex A ^ 2 ≤ B.relIndex A ^ n := Nat.pow_le_pow_right (by omega) hlt
    have h2 : B.relIndex A ^ 2 ≤ B.relIndex A := h1.trans (hpow.trans (hineq.trans hCAidx.le))
    nlinarith
  have hn0 : n ≠ 0 := by
    intro h0
    apply hK
    have h := D14.commutator_eq_bot_of_zero hUp hn h0
    rw [F6.twoResidual_eq_oTwoUpper, ← Subgroup.commutator_eq_bot_iff_le_centralizer,
      Subgroup.commutator_comm]
    exact h
  have : n = 1 := by omega
  exact this ▸ hn

theorem exists_reducedModule (hB1 : B69One) {H T M₂ R U : Subgroup G}
    (hmp : MinParabolic H T M₂) (hsq : IsSQTKSub H)
    (hRT : R ≤ T) (hTR : T ≤ Subgroup.normalizer (R : Set G)) (hJR : thompsonJ T ≤ R)
    (hJH : ¬ thompsonJ T ≤ pCoreOf 2 H)
    (hQn : H ≤ Subgroup.normalizer ((R ⊓ pCoreOf 2 H : Subgroup G) : Set G))
    (hUe : IsElemAbelian 2 U) (hUn : H ≤ Subgroup.normalizer (U : Set G))
    (hUQ : U ≤ R ⊓ pCoreOf 2 H)
    (hUC : U ≤ Subgroup.centralizer ((R ⊓ pCoreOf 2 H : Subgroup G) : Set G))
    (hK : ¬ twoResidual H ≤ Subgroup.centralizer (U : Set G)) :
    IsTwoReducedIn H ⁅U, twoResidual H⁆ ∧
      ¬ thompsonJ T ≤ Subgroup.centralizer ((⁅U, twoResidual H⁆ : Subgroup G) : Set G) := by
  have hTH : T ≤ H := hmp.isSylow.1
  have hQHT : pCoreOf 2 H ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hmp.isSylow
  have hUT : U ≤ T := (hUQ.trans inf_le_right).trans hQHT
  have hUH : U ≤ H := hUT.trans hTH
  have hUp : IsPGroup 2 U := hmp.isSylow.2.1.to_le hUT
  have hKH : twoResidual H ≤ H := twoResidual_le H
  have hKo : twoResidual H = oTwoUpper H := F6.twoResidual_eq_oTwoUpper H
  have hUa : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := (B6.isElemAbelian_iff.mp hUe).1
  have hKQ := commutator_twoResidual_pCoreOf_le hmp hRT hTR hJR hJH hQn
  obtain ⟨A, hA, hAQ⟩ := exists_isMaxElemAbelian_not_le_pCoreOf hJH
  have hBC : A ⊓ pCoreOf 2 H ≤ Subgroup.centralizer (U : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun u hu =>
      (Subgroup.mem_centralizer_iff.mp (hUC hu) x ⟨hJR (B6.le_thompsonJ hA hx.1), hx.2⟩).symm
  have hone := isChiefSeriesFrom_one hB1 hmp hsq hUT hUe hUn hA hAQ hBC hK
  obtain ⟨K₁, L₁, hstep, hL₁, hUK₁⟩ := D14.exists_chiefStep_of_one hUp hUH hone rfl
  rw [← hKo] at hL₁ hUK₁
  have hE : IsElemAbelian 2 (Ch3z.chiefMod L₁ K₁) :=
    isElemAbelian_secImg_of_le (L := L₁) hUe hstep.1.1
  have hQcm : pCoreOf 2 H ≤ centralizerMod L₁ H K₁ := Ch3z.pCoreOf_le_centralizerMod hUH hstep hE
  have hK1K : ⁅K₁, twoResidual H⁆ ≤ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
    rw [Subgroup.commutator_le]
    intro n hn k hk q hq
    have hqH : q ∈ H := pCoreOf_le 2 H hq
    have hkH : k ∈ H := hKH hk
    have hcQ : ⁅q, k⁆ ∈ R ⊓ pCoreOf 2 H := by
      rw [← commutatorElement_inv]
      exact (R ⊓ pCoreOf 2 H).inv_mem (hKQ (Subgroup.commutator_mem_commutator hk hq))
    have hswap := commutator_commutator_swap hUa
      (fun u hu => (Subgroup.mem_normalizer_iff.mp (hUn hqH) u).mp hu)
      (fun u hu => (Subgroup.mem_normalizer_iff.mp (hUn hkH) u).mp hu)
      (fun u hu => Subgroup.mem_centralizer_iff.mp (hUC hu) _ hcQ) (hstep.1.1 hn)
    have h1 : ⁅n, q⁆ ∈ L₁ := by
      rw [← commutatorElement_inv]
      exact L₁.inv_mem ((hQcm hq).2.2 n hn)
    have h2 : ⁅⁅n, q⁆, k⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator h1 hk
      rw [hL₁] at this
      exact Subgroup.mem_bot.mp this
    rw [← hswap] at h2
    exact (commutatorElement_eq_one_iff_mul_comm.mp h2).symm
  have hVV : ⁅U, twoResidual H⁆ ≤ ⁅⁅U, twoResidual H⁆, twoResidual H⁆ := by
    rw [hKo]
    exact D14.commutator_le_commutator_commutator hUp hUH hUn
  have hVK₁ : ⁅U, twoResidual H⁆ ≤ ⁅K₁, twoResidual H⁆ :=
    hVV.trans (Subgroup.commutator_mono hUK₁ le_rfl)
  have hVU : ⁅U, twoResidual H⁆ ≤ U :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hKH.trans hUn)
  have hHV : H ≤ Subgroup.normalizer ((⁅U, twoResidual H⁆ : Subgroup G) : Set G) :=
    D14.le_normalizer_commutator hUn (le_normalizer_twoResidual H)
  have hVH : ⁅U, twoResidual H⁆ ≤ H := hVU.trans hUH
  have hVe : IsElemAbelian 2 ⁅U, twoResidual H⁆ := Setup.Campbell.isElemAbelian_mono hUe hVU
  have hKV : ¬ twoResidual H ≤
      Subgroup.centralizer ((⁅U, twoResidual H⁆ : Subgroup G) : Set G) := by
    intro hle
    apply hK
    have h1 : ⁅⁅U, twoResidual H⁆, twoResidual H⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hle)
    have h2 : ⁅U, twoResidual H⁆ = ⊥ := le_bot_iff.mp (hVV.trans h1.le)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact h2)
  have hQcV : pCoreOf 2 H ≤ Subgroup.centralizer ((⁅U, twoResidual H⁆ : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mp (hVK₁.trans hK1K)
  refine ⟨⟨hVH, hHV, hVe, ?_⟩, fun hJV => hJH ?_⟩
  · intro D hDH hDn hD2
    set C₀ : Subgroup G := H ⊓ Subgroup.centralizer ((⁅U, twoResidual H⁆ : Subgroup G) : Set G)
      with hC₀
    have hC₀n : H ≤ Subgroup.normalizer (C₀ : Set G) := fun g hg =>
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hg, le_normalizer_centralizer hHV hg⟩
    have hC₀J : C₀ ≤ kerIn M₂ H := hmp.le_kerIn_of_not_twoResidual_le inf_le_left hC₀n
      (fun hle => hKV (hle.trans inf_le_right))
    have hDC₀ : ∀ d ∈ D, ∃ k : ℕ, d ^ 2 ^ k ∈ C₀ := fun d hd => by
      obtain ⟨k, hk⟩ := hD2 d hd
      exact ⟨k, H.pow_mem (hDH hd) _, hk⟩
    obtain ⟨n, hn⟩ := B6.exists_relIndex_eq_two_pow (hDH.trans hC₀n) hDC₀
    have hD'n : H ≤ Subgroup.normalizer ((D ⊔ C₀ : Subgroup G) : Set G) :=
      D14.le_normalizer_sup hDn hC₀n
    have hD'2 : ∀ d ∈ D ⊔ C₀, ∃ k : ℕ, d ^ 2 ^ k ∈ C₀ := fun d hd =>
      ⟨n, B6.pow_mem_of_relIndex_eq_two_pow (sup_le (hDH.trans hC₀n) Subgroup.le_normalizer)
        ((B6.relIndex_sup_eq_of_le_normalizer (hDH.trans hC₀n)).trans hn) d hd⟩
    have hD'C₀ := hmp.le_of_isTwoQuotient_of_pCoreOf_le hC₀n (le_inf (pCoreOf_le 2 H) hQcV)
      (hC₀J.trans kerIn_le) le_sup_right (sup_le hDH inf_le_left) hD'n hD'2
    exact (le_sup_left.trans hD'C₀).trans inf_le_right
  · exact le_pCoreOf_of_le_centralizer hmp hHV hKV ((hJR.trans hRT).trans hTH)
      (hmp.isSylow.2.1.to_le (hJR.trans hRT)) hJV

end CFSG.Quasithin.Ch3g316
