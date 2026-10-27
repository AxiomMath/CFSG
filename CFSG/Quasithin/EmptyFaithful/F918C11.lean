module

public import CFSG.Quasithin.EmptyFaithful.F918C10
public import CFSG.Quasithin.Background.F918C3
public import CFSG.Quasithin.EmptyFaithful.F918C1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

section Center

variable {G : Type} [Group G]

theorem center_eq_bot_of_simple_perfect {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hperf : Group.IsPerfect Q) : Subgroup.center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · exfalso
    have h1 : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊤ := by
      have := hperf.commutator_eq_top
      rwa [_root_.commutator_def] at this
    have hc : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      exact Subgroup.mem_centralizer_iff.2 fun y _ =>
        Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top x) y
    rw [h1] at hc
    obtain ⟨x, hx⟩ := exists_ne (1 : Q)
    exact hx (Subgroup.mem_bot.1 (hc ▸ Subgroup.mem_top x))

variable [Finite G]

theorem hZ_comp {H K : Subgroup G} (hK : K ∈ cComp H) (hS' : IsSimpleGroup (KBar K)) :
    ∀ x ∈ K, (∀ k' ∈ K, x * k' * x⁻¹ * k'⁻¹ ∈ pCoreOf 2 H) → x ∈ pCoreOf 2 H := by
  intro x hx hcomm
  have hKH : K ≤ H := le_of_mem_cComp hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperfK : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hK)
  have hperfQ : Group.IsPerfect (KBar K) :=
    Group.IsPerfect.ofSurjective (G := K) (G' := KBar K)
      (f := QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K)) (QuotientGroup.mk'_surjective _)
  have hZ := center_eq_bot_of_simple_perfect hperfQ
  have hKO : K ⊓ pCoreOf 2 H ≤ pCoreOf 2 K := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ?_
    · intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro n
      constructor
      · rintro ⟨hnK, hnQ⟩
        exact ⟨K.mul_mem (K.mul_mem hg hnK) (K.inv_mem hg),
          (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (hKH hg)) n).mp hnQ⟩
      · rintro ⟨hnK, hnQ⟩
        refine ⟨?_, ?_⟩
        · have := K.mul_mem (K.mul_mem (K.inv_mem hg) hnK) hg
          simpa [mul_assoc] using this
        · exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (hKH hg)) n).mpr hnQ
    · exact (pCoreOf_isPGroup 2 H).to_le inf_le_right
  have hP : ∀ k' ∈ K, x * k' * x⁻¹ * k'⁻¹ ∈ pCoreOf 2 K := fun k' hk' =>
    hKO ⟨K.mul_mem (K.mul_mem (K.mul_mem hx hk') (K.inv_mem hx)) (K.inv_mem hk'), hcomm k' hk'⟩
  have hcent : (QuotientGroup.mk (⟨x, hx⟩ : ↥K) : KBar K) ∈ Subgroup.center (KBar K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    induction g using QuotientGroup.induction_on with
    | H b =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have hq := hP ((b : G)⁻¹) (K.inv_mem b.2)
      have e : x⁻¹ * (b : G)⁻¹ * x * (b : G) = x⁻¹ * (x * (b : G)⁻¹ * x⁻¹ * (b : G))⁻¹ * x := by
        group
      have h2 := (Subgroup.mem_normalizer_iff''.mp (le_normalizer_pCoreOf 2 K hx) _).mp
        ((pCoreOf 2 K).inv_mem (by simpa using hq))
      simpa [e, mul_assoc] using h2
  rw [hZ] at hcent
  have h1 : (⟨x, hx⟩ : ↥K) ∈ (pCoreOf 2 K).subgroupOf K :=
    (QuotientGroup.eq_one_iff _).1 (Subgroup.mem_bot.1 hcent)
  exact A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK) (Subgroup.mem_subgroupOf.1 h1)

end Center

@[expose] def N4Stmt : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L A : Subgroup (MulAut W)) (V : Subgroup W)
    (σ : MulAut W), D3Std M Mp T L V → Mp = L → QOff Mp T A (orbSup T V) → σ ∈ T → σ ∈ M →
      σ ∈ Subgroup.normalizer (L : Set (MulAut W)) → ModDynkin L σ → σ ∉ stabSub V →
      IsSumMod (fixV L) V (V.map σ.toMonoidHom) ⊤ → IsPSL 3 2 1 ↥L →
      BinaryNaturalSL L V (V ⊓ fixV L) 3 1 → V ⊓ fixV L = ⊥

section Case1

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

theorem case1_aux (h : HypF918 T V L V₁ Vp H K) (hH : SQTKGroup ↥H) (hHeq : H = conjClosure K T ⊔ T)
    (hK₀ : conjClosure K T = K) (hS' : IsSimpleGroup (KBar K)) (hL : KbarIsL3Two K ∨ KbarIsA6 K)
    {s : G} (hsT : s ∈ T) (hsK : s ∈ Subgroup.normalizer (K : Set G))
    (hdyn : KbarNontrivialOnDynkin K s) (h310 : D310) (h391 : D391) (hNat : Insp14622Nat)
    (hI161 : AsI161A6) (hN4 : N4Stmt)
    (hNo : HasNoFaithfulFFModulesMod (conjClosure K T ⊔ T) (pCoreOf 2 H)) :
    ∃ I : Subgroup G, V₁ ≤ I ∧ ⁅conjClosure Vp H, K⁆ ⊔ V₁ = I ⊔ conjSub s I ∧
      IsNaturalLike K V₁ I := by
  obtain ⟨I, hV₁I, hIU, W, hW, hirrU⟩ := exists_isIrrPlusTildeU h
  have hirrT := isIrrPlusTildeT_of_ambient h hIU W hW hirrU
  have hF := factElem h hIU
  have hout := case1_group h hH hK₀ hV₁I hIU hirrT h310 h391 hNat hS' hsT hsK hdyn
  refine ⟨I, hV₁I, ?_, ?_⟩
  swap
  · refine isNaturalLike_of_naturalType h hV₁I hIU hirrT hK₀ hS' hout.ne hL hout.nat hI161 ?_
    intro hPSL
    obtain ⟨B, hA⟩ := hout.off
    have hsH : s ∈ H := h.T_le_H hsT
    have hns : actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨s, hsH⟩ ∉
        stabSub (subM V₁ (conjClosure I H) I) := fun hst =>
      hout.notNorm ((actH_mem_stabSub_subM_iff h.H_le_normalizer_V₁
        (h.conjClosure_le_normalizer_V₁ hIU) (le_normalizer_conjClosure I H) hV₁I
        (le_conjClosure I H) ⟨s, hsH⟩).mp hst)
    exact hN4 _ _ _ _ _ _ _ _ hout.std (by rw [hK₀]) hA
      (actH_mem_autIH_of_mem (I := I) h h.T_le_H hsT)
      (actH_mem_autIH_of_mem (I := I) h (le_refl H) hsH)
      (actH_mem_normalizer_autIH (I := I) h hsH hsK) hout.dynkin hns hout.sum hPSL (hout.nat.1 hPSL)
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hsH : s ∈ H := h.T_le_H hsT
  have hIHN := h.conjClosure_le_normalizer_V₁ hIU
  have hIH := le_normalizer_conjClosure I H
  have hirr' : subM V₁ (conjClosure I H) I ∈ IrrPlusOn (autIH V₁ I H (conjClosure K T))
      (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I)) (autIH V₁ I H T) := hirrT
  have hKnorm : ∀ y ∈ H, y ∈ Subgroup.normalizer (K : Set G) := fun y hy => hK₀ ▸ h.K₀_normal hy
  have hcomm : XMod.commOf ↥(autIH V₁ I H K) (subM V₁ (conjClosure I H) I) =
      subM V₁ (conjClosure I H) I := by
    have := hirr'.1.2.2.1
    rwa [hK₀] at this
  have hVinv : ∀ x ∈ autIH V₁ I H K, ∀ v ∈ subM V₁ (conjClosure I H) I,
      x v ∈ subM V₁ (conjClosure I H) I := fun x hx v hv => by
    have := hirr'.1.2.1
    rw [hK₀] at this
    exact this ⟨x, hx⟩ v hv
  have hgen := iSup_actH_subM_eq_top h.H_le_normalizer_V₁ hIHN hIH hV₁I
  have hMnorm : ∀ m ∈ (H.subgroupOf H).map (actH h.H_le_normalizer_V₁ hIH),
      m ∈ Subgroup.normalizer ((autIH V₁ I H K : Subgroup _) : Set _) := by
    rintro _ ⟨y, -, rfl⟩
    exact actH_mem_normalizer_autIH h y.2 (hKnorm y y.2)
  have hperf := commV_eq_top_of_generated hgen hMnorm hcomm
  have hσN := actH_mem_normalizer_autIH (I := I) h hsH hsK
  have hinv := inv_sup hVinv (inv_map_of_normalizes hσN hVinv)
  have hsup := eq_sup_of_sum hout.sum hinv hperf
  have hIs := map_actH_subM h.H_le_normalizer_V₁ hIHN hIH hV₁I (le_conjClosure I H) ⟨s, hsH⟩
  have hIsI : conjSub s I ≤ conjClosure I H := by
    intro x hx
    rw [mem_conjSub] at hx
    have := (Subgroup.mem_normalizer_iff.mp (hIH hsH) (s⁻¹ * x * s)).mp (le_conjClosure I H hx)
    simpa [mul_assoc] using this
  have hV₁Is : V₁ ≤ conjSub s I := by
    intro v hv
    rw [mem_conjSub]
    exact hV₁I ((Subgroup.mem_normalizer_iff''.mp (h.H_le_normalizer_V₁ hsH) v).mp hv)
  rw [hIs] at hsup
  have hIHeq : conjClosure I H = I ⊔ conjSub s I :=
    eq_sup_of_subM_sup_eq_top hIHN hV₁I (le_conjClosure I H) hIsI hsup
  have hZ : ∀ x ∈ conjClosure K T,
      (∀ k' ∈ conjClosure K T, x * k' * x⁻¹ * k'⁻¹ ∈ pCoreOf 2 H) → x ∈ pCoreOf 2 H := by
    rw [hK₀]
    exact hZ_comp h.K_cComp hS'
  have hI := isIrrPlusTilde_of_module h hV₁I hIU hirrT
  have h7 := h.F918_7' hHeq hZ hV₁I hIU hI hNo
  rw [hK₀] at h7
  have hUN : conjClosure Vp H ≤ Subgroup.normalizer (V₁ : Set G) :=
    h.conjClosure_le_normalizer_V₁ (le_conjClosure Vp H)
  have hcU : ⁅conjClosure Vp H, K⁆ ≤ conjClosure Vp H := by
    refine Subgroup.commutator_le.mpr fun u hu k hk => ?_
    have h1 : k * u⁻¹ * k⁻¹ ∈ conjClosure Vp H :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure Vp H (hKH hk)) u⁻¹).mp
        ((conjClosure Vp H).inv_mem hu)
    have e : u * k * u⁻¹ * k⁻¹ = u * (k * u⁻¹ * k⁻¹) := by group
    rw [commutatorElement_def, e]
    exact (conjClosure Vp H).mul_mem hu h1
  have hXN : ⁅conjClosure Vp H, K⁆ ⊔ V₁ ≤ Subgroup.normalizer (V₁ : Set G) :=
    sup_le (hcU.trans hUN) Subgroup.le_normalizer
  have hYN : I ⊔ conjSub s I ≤ Subgroup.normalizer (V₁ : Set G) := hIHeq ▸ hIHN
  refine eq_of_secImg_eq (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁) le_sup_right
    (hV₁I.trans le_sup_left) hXN hYN ?_
  show tildeOf V₁ (⁅conjClosure Vp H, K⁆ ⊔ V₁) = tildeOf V₁ (I ⊔ conjSub s I)
  rw [tildeOf_sup' (hcU.trans hUN) Subgroup.le_normalizer, tildeOf_eq_bot_of_le le_rfl, sup_bot_eq,
    ← h7, hIHeq]

end Case1

section Case1S

variable {G : Type} [Group G] [Finite G] {T M K : Subgroup G}

theorem isDecompUK_case1 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (S : Setting146 G T M)
    (hK : K ∈ cComp (mcOf T)) (hS' : IsSimpleGroup (KBar K))
    (hHeq : mcOf T = conjClosure K T ⊔ T) (hK₀ : conjClosure K T = K)
    (hL : KbarIsL3Two K ∨ KbarIsA6 K) {s : G} (hsT : s ∈ T)
    (hsK : s ∈ Subgroup.normalizer (K : Set G)) (hdyn : KbarNontrivialOnDynkin K s)
    (h310 : D310) (h391 : D391) (hNat : Insp14622Nat) (hI161 : AsI161A6) (hN4 : N4Stmt)
    (hNo : HasNoFaithfulFFModulesMod (conjClosure K T ⊔ T) (pCoreOf 2 (mcOf T))) :
    ∃ I : Subgroup G, IsDecompUK T M K I (conjSub s I) s := by
  have h : HypF918 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) (mcOf T) K := by
    rw [hHeq]
    exact hypF918_of_setting146 h37 h38 S hK hS'
  have hH : SQTKGroup ↥(mcOf T) := S.sqtkGroup_of_isHTM S.isHTM_mcOf
  obtain ⟨I, hV₁I, hsup, hnat⟩ :=
    case1_aux h hH hHeq hK₀ hS' hL hsT hsK hdyn h310 h391 hNat hI161 hN4 hNo
  have hsH : s ∈ mcOf T := h.T_le_H hsT
  refine ⟨I, ⟨⟨hsT, hsK⟩, hdyn, hV₁I, ?_, rfl, hsup, hnat⟩⟩
  intro v hv
  rw [mem_conjSub]
  exact hV₁I ((Subgroup.mem_normalizer_iff''.mp (h.H_le_normalizer_V₁ hsH) v).mp hv)

end Case1S

end CFSG.Quasithin
