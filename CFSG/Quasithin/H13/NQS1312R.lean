module

public import CFSG.Quasithin.H13.NQS1312F
public import CFSG.Quasithin.H13.NQS1312D
public import CFSG.Quasithin.Background.C2Bridge
public import CFSG.Quasithin.Background.A4Four
public import CFSG.Quasithin.EmptyFaithful.T1515Der4

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3.NLine

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.SteinbergCB
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pCoreOf_le_oTwoFIn (H : Subgroup G) : pCoreOf 2 H ≤ oTwoFIn H := by
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨y, ?_, rfl⟩
  show QuotientGroup.mk' (CFSG.pCore 2 ↥H) y ∈ CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H)
  have : QuotientGroup.mk' (CFSG.pCore 2 ↥H) y = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hy
  rw [this]
  exact Subgroup.one_mem _

theorem centralizer_line_le
    (h1332 : Stmt13_3_2) (h311 : Theorem311Stmt) {T L V : Subgroup G} {z : G}
    [IsElementaryAbelian 2 V] (hH : QTH13 G T L)
    (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) (hF : QTU3InternalFrame T L V z)
    {Φ : Additive V ≃ₗ[ZMod 2] W6}
    (hΦLs : ∀ j ∈ J6, ∃ (l : G) (hl : l ∈ L), linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hF.2.2.2.2.2.2.1 hl⟩) = glLin j)
    (hΦN : ∀ n : normalizer (V : Set G), ∃ k ∈ N6,
      linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl n) = glLin k)
    (hcomp : ∀ K ∈ cComp (centralizer ({ptOf Φ (vecOf 15), ptOf Φ (vecOf 52)} : Set G)),
      CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) → K ≤ normalizer (L : Set G)) :
    centralizer ({ptOf Φ (vecOf 15), ptOf Φ (vecOf 52)} : Set G) ≤ normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTL, hVT, hVe, hV64, hVQ, -, hLV, hTV, -, -, hTC, -, -⟩ := id hF
  obtain ⟨-, hVM, -, -, hTI⟩ := u3_selected_local_normalizer_and_TI_of_1332 h1332 hH hF
  set u₁ := ptOf Φ (vecOf 15) with hu₁
  set v₁ := ptOf Φ (vecOf 52) with hv₁
  set H := centralizer ({u₁, v₁} : Set G) with hHdef
  set M := normalizer (L : Set G) with hM
  set Q := pCoreOf 2 (L ⊔ T) with hQ
  have hu₁V : u₁ ∈ V := ptOf_mem _
  have hv₁V : v₁ ∈ V := ptOf_mem _
  have hu₁1 : u₁ ≠ 1 := by
    intro h
    have h0 : vecOf 15 = (0 : W6) := ptOf_injective (h.trans ptOf_zero.symm)
    have := vecOf_injective (by norm_num : 15 < 64) (by norm_num : 0 < 64)
      (h0.trans vecOf_zero.symm)
    norm_num at this
  have hset : ({u₁, v₁} : Set G) ⊆ V := by
    rintro _ (rfl | rfl)
    exacts [hu₁V, hv₁V]
  have hCVH : centralizer (V : Set G) ≤ H := Subgroup.centralizer_le hset
  have hHu : H ≤ centralizer ({u₁} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 (Set.mem_insert _ _))
  have hHM : H ⊓ M ≤ normalizer (V : Set G) := fun x hx =>
    hTI u₁ hu₁V hu₁1 ⟨hx.2, hHu hx.1⟩
  have hcen : ∀ x ∈ H, x * u₁ * x⁻¹ = u₁ ∧ x * v₁ * x⁻¹ = v₁ := by
    intro x hx
    rw [hHdef, mem_centralizer_iff] at hx
    refine ⟨?_, ?_⟩
    · rw [← hx u₁ (Set.mem_insert _ _)]; group
    · rw [← hx v₁ (Set.mem_insert_of_mem _ rfl)]; group
  have hF2 : oTwoFIn H ≤ M := oTwoFIn_le_line h1332 h311 hH hU3 hF hΦLs hΦN
  have hO2 : pCoreOf 2 H ≤ H ⊓ M :=
    le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 H) ((pCoreOf_le_oTwoFIn H).trans hF2)
  have hFstar : oTwoFstarIn H ≤ H ⊓ M :=
    oTwoFstarIn_le_of_components1516 hO2 (le_inf C2Six.oTwoFIn_le hF2)
      (fun K hK hq => le_inf (le_of_mem_cComp hK) (hcomp K hK hq))
  set X : Subgroup G := (O2Fstar ↥H).map H.subtype with hX
  have hXeq : X = oTwoFstarIn H := (oTwoFstarIn_eq_map_O2Fstar H).symm
  have hOX : pCoreOf 2 H ≤ X := by
    rintro _ ⟨n, hn, rfl⟩
    refine ⟨n, ?_, rfl⟩
    show QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) n ∈ CFSG.generalizedFitting (OTwoQuot H)
    have : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) n = 1 :=
      (QuotientGroup.eq_one_iff n).mpr hn
    rw [this]
    exact Subgroup.one_mem _
  have hA44 : A44Hyp H X := by
    right
    rw [imageOTwoQuot_O2Fstar]
    exact ⟨IsSubnormal.refl _, fun x hx _ => hx.2⟩
  have hO2eq : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H := a4_4_1 hOX (hXeq ▸ hFstar) hA44
  obtain ⟨k₁, hk₁L, hk₁τ, hk₁15, hk₁52⟩ := exists_k_mem_L hLV hΦLs
  have hk₁H : k₁ ∈ H := by
    rw [hHdef, mem_centralizer_iff]
    rintro _ (rfl | rfl)
    · calc u₁ * k₁ = k₁ * u₁ * k₁⁻¹ * k₁ := by rw [hk₁15]
        _ = k₁ * u₁ := by group
    · calc v₁ * k₁ = k₁ * v₁ * k₁⁻¹ * k₁ := by rw [hk₁52]
        _ = k₁ * v₁ := by group
  have hk₁M : k₁ ∈ M := Subgroup.le_normalizer hk₁L
  set R := pCoreOf 2 (H ⊓ M) with hR
  have hRp : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hRle : R ≤ H ⊓ M := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hRCV : R ≤ centralizer (V : Set G) :=
    le_centralizer_of_isPGroup hΦN (hLV hk₁L) (tau_eq_iff.2 hk₁τ) hRp (hRle.trans hHM)
      (fun r hr => hcen r (hRle hr).1)
      (fun r hr => (mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
        (Subgroup.mem_inf.2 ⟨hk₁H, hk₁M⟩)) r).1 hr)
  set Y := M ⊓ centralizer (V : Set G) with hY
  set R₀ := pCoreOf 2 Y with hR₀
  have hYHM : Y ≤ H ⊓ M := le_inf (inf_le_right.trans hCVH) inf_le_left
  have hYN : H ⊓ M ≤ normalizer (Y : Set G) := fun x hx =>
    inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx.2,
      normalizer_le_normalizer_centralizer V (hHM hx)⟩
  have hRR₀ : R = R₀ := by
    apply le_antisymm
    · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (le_inf (hRle.trans inf_le_right) hRCV)
        (hYHM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)) hRp
    · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans hYHM)
        (hYN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hR₀p : IsPGroup 2 R₀ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hQp : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hQsyl := isSylowTwoOf_Q hH hF
  have hR₀Q : R₀ ≤ Q := by
    have h1 := eq_of_isSylowTwoOf_le hQsyl le_sup_right
      (sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 Y) hQsyl.1)
      (IsPGroup.to_sup_of_normal_left' hR₀p hQp
        (hQsyl.1.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)))
    exact le_sup_left.trans h1.le
  have hVR₀ : V ≤ R₀ := by
    have hVcomm : V ≤ centralizer (V : Set G) := fun x hx => mem_centralizer_iff.2 fun y hy => by
      have := hVe.toIsMulCommutative
      exact congrArg Subtype.val (mul_comm (⟨y, hy⟩ : V) ⟨x, hx⟩)
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (le_inf (hVT.trans hTL) hVcomm) (inf_le_right.trans (centralizer_le_normalizer_self V))
      (IsPGroup.of_card (n := 6) (by rw [hV64]; norm_num))
  have hV1 : V ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hV64
    norm_num at hV64
  have hR₀1 : R₀ ≠ ⊥ := fun h => hV1 (le_bot_iff.1 (h ▸ hVR₀))
  have hLT : L ⊔ T ≤ normalizer (R₀ : Set G) := by
    refine le_trans ?_ (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
    refine sup_le (fun l hl => ?_) (fun t ht => ?_)
    · exact inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (Subgroup.le_normalizer hl),
        normalizer_le_normalizer_centralizer V (hLV hl)⟩
    · exact inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hTL ht),
        normalizer_le_normalizer_centralizer V (hTV ht)⟩
  have hNR₀ : normalizer (R₀ : Set G) ≤ M :=
    normalizer_le_of_le_Q h1332 hH hR₀1 hR₀p hR₀Q hLT
  have hHN : H ≤ normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  rw [← hO2eq, hRR₀] at hHN
  exact hHN.trans hNR₀

@[expose] noncomputable def b0V {V : Subgroup G} [IsElementaryAbelian 2 V]
    (Φ : Additive V ≃ₗ[ZMod 2] W6) : LinearMap.BilinForm (ZMod 2) (Additive V) :=
  b0.compl₁₂ (Φ : Additive V →ₗ[ZMod 2] W6) (Φ : Additive V →ₗ[ZMod 2] W6)

omit [Finite G] in
theorem b0V_apply {V : Subgroup G} [IsElementaryAbelian 2 V] (Φ : Additive V ≃ₗ[ZMod 2] W6)
    (x y : Additive V) : b0V Φ x y = b0 (Φ x) (Φ y) := rfl

omit [Finite G] in
theorem b0V_nondegenerate {V : Subgroup G} [IsElementaryAbelian 2 V]
    (Φ : Additive V ≃ₗ[ZMod 2] W6) : (b0V Φ).Nondegenerate := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · have h0 : Φ x = 0 := b0_nondegenerate.1 _ fun w => by
      have := hx (Φ.symm w)
      rwa [b0V_apply, LinearEquiv.apply_symm_apply] at this
    simpa using h0
  · have h0 : Φ y = 0 := b0_nondegenerate.2 _ fun w => by
      have := hy (Φ.symm w)
      rwa [b0V_apply, LinearEquiv.apply_symm_apply] at this
    simpa using h0

omit [Finite G] in
theorem b0V_isAlt {V : Subgroup G} [IsElementaryAbelian 2 V] (Φ : Additive V ≃ₗ[ZMod 2] W6) :
    (b0V Φ).IsAlt := fun x => b0_isAlt (Φ x)

omit [Finite G] in
theorem b0V_invariant
    {V : Subgroup G}
    [IsElementaryAbelian 2 V] {Φ : Additive V ≃ₗ[ZMod 2] W6}
    (hΦN : ∀ n : normalizer (V : Set G), ∃ k ∈ N6,
      linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl n) = glLin k)
    (n : normalizer (V : Set G)) (x y : Additive V) :
    b0V Φ (u3ConjLin V _ le_rfl n x) (u3ConjLin V _ le_rfl n y) = b0V Φ x y := by
  obtain ⟨k, hk, hkn⟩ := hΦN n
  have hΦ : ∀ w, Φ (u3ConjLin V _ le_rfl n w) = glLin k (Φ w) := fun w => by
    rw [← hkn, linConj_apply, LinearEquiv.symm_apply_apply]
  rw [b0V_apply, b0V_apply, hΦ, hΦ, glLin_apply, glLin_apply,
    b0_mulVec_of_mem_b0Stab (N6_le_b0Stab hk)]

end CFSG.Quasithin.H13.U3.NLine

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.SteinbergCB NLine
open scoped IsMulCommutative

theorem u3NondegLineCentralizer_of_comp
    (h1332 : Stmt13_3_2) (h311 : Theorem311Stmt) (hK : U3LineComponentExclusion) :
    U3NondegLineCentralizer := by
  intro G _ _ T L V z _ hH hU3 hF b hbn hba hbi u v hu hv huv
  have hLV : L ≤ normalizer (V : Set G) := hF.2.2.2.2.2.2.1
  have hV64 : Nat.card V = 64 := hF.2.2.2.1
  have hV1 : V ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hV64
    norm_num at hV64
  obtain ⟨Φ, -, hΦLs, hΦN, -⟩ := u3_six_module_transport_adapted h1332 hH hU3 hF
  have huv0 : b0 (Φ (Additive.ofMul ⟨u, hu⟩)) (Φ (Additive.ofMul ⟨v, hv⟩)) ≠ 0 := by
    rwa [← form_eq_b0 hLV hΦLs hV1 hbn hbi]
  obtain ⟨l, hl, hlu, hlv⟩ := exists_conj_line hLV hΦLs hu hv huv0
  have h1552 : b0V Φ (Additive.ofMul ⟨ptOf Φ (vecOf 15), ptOf_mem _⟩)
      (Additive.ofMul ⟨ptOf Φ (vecOf 52), ptOf_mem _⟩) ≠ 0 := by
    rw [b0V_apply, phi_ptOf, phi_ptOf, b0_vecOf, dotB_15_52]
    decide
  have hcomp := hK G T L V z hH hU3 hF (b0V Φ) (b0V_nondegenerate Φ) (b0V_isAlt Φ)
    (b0V_invariant hΦN) _ _ (ptOf_mem _) (ptOf_mem _) h1552
  have hmain := centralizer_line_le h1332 h311 hH hU3 hF hΦLs hΦN hcomp
  intro c hc
  have hlM : l ∈ normalizer (L : Set G) := Subgroup.le_normalizer hl
  have hc' : l⁻¹ * c * l ∈ centralizer ({ptOf Φ (vecOf 15), ptOf Φ (vecOf 52)} : Set G) := by
    have hcu : u * c = c * u := (mem_centralizer_iff.1 hc) u (Set.mem_insert _ _)
    have hcv : v * c = c * v := (mem_centralizer_iff.1 hc) v (Set.mem_insert_of_mem _ rfl)
    rw [mem_centralizer_iff]
    rintro _ (rfl | rfl)
    · have h1 : ptOf Φ (vecOf 15) = l⁻¹ * u * l := by rw [← hlu]; group
      rw [h1]
      calc l⁻¹ * u * l * (l⁻¹ * c * l) = l⁻¹ * (u * c) * l := by group
        _ = l⁻¹ * (c * u) * l := by rw [hcu]
        _ = l⁻¹ * c * l * (l⁻¹ * u * l) := by group
    · rcases hlv with h | h
      · have h1 : ptOf Φ (vecOf 52) = l⁻¹ * v * l := by rw [← h]; group
        rw [h1]
        calc l⁻¹ * v * l * (l⁻¹ * c * l) = l⁻¹ * (v * c) * l := by group
          _ = l⁻¹ * (c * v) * l := by rw [hcv]
          _ = l⁻¹ * c * l * (l⁻¹ * v * l) := by group
      · have h1 : ptOf Φ (vecOf 52) = l⁻¹ * (v * u) * l := by rw [← h]; group
        rw [h1]
        calc l⁻¹ * (v * u) * l * (l⁻¹ * c * l) = l⁻¹ * (v * (u * c)) * l := by group
          _ = l⁻¹ * (v * (c * u)) * l := by rw [hcu]
          _ = l⁻¹ * ((v * c) * u) * l := by group
          _ = l⁻¹ * ((c * v) * u) * l := by rw [hcv]
          _ = l⁻¹ * c * l * (l⁻¹ * (v * u) * l) := by group
  have h2 := hmain hc'
  have h3 : l * (l⁻¹ * c * l) * l⁻¹ ∈ normalizer (L : Set G) :=
    mul_mem (mul_mem hlM h2) (inv_mem hlM)
  rwa [show l * (l⁻¹ * c * l) * l⁻¹ = c by group] at h3

end CFSG.Quasithin.H13.U3
