module

public import CFSG.Quasithin.EmptyFaithful.S146zUD3Mod
public import CFSG.Quasithin.EmptyFaithful.S146zUD3Rot
public import CFSG.Quasithin.EmptyFaithful.S146zUD3Inf
public import CFSG.Quasithin.EmptyFaithful.S146zUBSetup

public section

namespace CFSG.Quasithin.S146zU.UD3

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
  CFSG.Quasithin.S146zU.UA
open scoped Pointwise commutatorElement

section CaseOne

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def CaseOne {T V L V₁ Vp H K : Subgroup G}
    (h : HypF918 T V L V₁ Vp H K) {I : Subgroup G} (hIU : I ≤ conjClosure Vp H) : Prop :=
  haveI := factElem h hIU
  subM V₁ (conjClosure I H) I = ⊤ ∧
    ∃ n, IsPSL 2 2 n ↥(autSub (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)) ∧
      Omega4PlusModule (autSub (autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I)) n

end CaseOne

section Main

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T M H PQ H₀ H₁ H₂ : Subgroup G} {t : G}

theorem caseI_false (h36 : A36ForSQTK) (hlist : SQTKList3Dvd)
    (iS : Input14614NoSz) (S : Setting146 G T M) (hred : IsRedCE T M H PQ 5)
    (hmax : PMaximal T M 5) (hdec : IsDecP T M H 5 H₀ H₁ H₂ t) {K₁ : Subgroup G} {s : G}
    (hK₁ : K₁ ∈ cComp (mcOf T)) (hsT : s ∈ T) (hsN : s ∉ Subgroup.normalizer (K₁ : Set G))
    (hKz : conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ conjSub s K₁)
    (e : Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)))
    (hF : HypF918 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) (mcOf T) K₁)
    {I : Subgroup G} (hIU : I ≤ conjClosure (VZ T M) (mcOf T))
    (hclaim : tildeOf (quasithinOmegaOneCenter T) (conjClosure I (mcOf T)) =
      tildeOf (quasithinOmegaOneCenter T)
        ⁅conjClosure (VZ T M) (mcOf T), conjClosure K₁ T⁆)
    (hcase : CaseOne hF hIU) : False := by
  classical
  have := factElem hF hIU
  have hHG : H ≤ mcOf T := S.le_mcOf hred.isHTM
  have hTG : T ≤ mcOf T := hred.isHTM.1.1.trans hHG
  have hsG : s ∈ mcOf T := hTG hsT
  have hK₂ : conjSub s K₁ ∈ cComp (mcOf T) := conjSub_mem_cComp_of_mem hK₁ hsG
  have hK₁G : K₁ ≤ mcOf T := le_of_mem_cComp hK₁
  have hK₂G : conjSub s K₁ ≤ mcOf T := le_of_mem_cComp hK₂
  have hKzn : mcOf T ≤ Subgroup.normalizer
      ((conjClosure (oTwoUpper H) (mcOf T) : Subgroup G) : Set G) :=
    le_normalizer_conjClosure _ _
  have hK₀ : conjClosure K₁ T = K₁ ⊔ conjSub s K₁ :=
    UB.conjClosure_eq_sup_conjSub hsT hKz (hTG.trans hKzn)
  have hKzK₀ : conjClosure (oTwoUpper H) (mcOf T) = conjClosure K₁ T := hKz.trans hK₀.symm
  have hK₁Kz : K₁ ≤ conjClosure (oTwoUpper H) (mcOf T) := hKz ▸ le_sup_left
  have hK₂Kz : conjSub s K₁ ≤ conjClosure (oTwoUpper H) (mcOf T) := hKz ▸ le_sup_right
  have hinf := inf_le_pCoreOf h36 hlist iS S hred hmax hK₁ hsT hsN hKz e
  have hcommK := commutator_mem_pCoreOf h36 hlist iS S hred hmax hK₁ hsT hsN hKz e
  obtain ⟨hV, n, hL, hΩ⟩ := hcase
  have hLn : IsPSL 2 2 n ↥(autIH (quasithinOmegaOneCenter T) I (mcOf T) K₁) :=
    isPSL_of_autSub_top hV hL
  obtain ⟨hn1, hLcard⟩ := S153H.card_psl_two_two hLn
  have hLne : autIH (quasithinOmegaOneCenter T) I (mcOf T) K₁ ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hLcard
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
    have h4 : 4 ≤ (2 ^ n) ^ 2 := by nlinarith
    have h3 : 3 ≤ (2 ^ n) ^ 2 - 1 := by omega
    have := Nat.mul_le_mul h2 h3
    omega
  have eL := UB.nonempty_autIH_equiv_L216 hF hIU hLne e
  have hY : 2 ∣ Nat.card ↥(autIH (quasithinOmegaOneCenter T) I (mcOf T) K₁) := by
    obtain ⟨eL'⟩ := eL
    rw [Nat.card_congr eL'.toEquiv, SBc16.card_L216]
    norm_num
  have hsyl := isSylowTwoOf_inf_K₁ S hred hK₁ hK₂ hKz
  have hA2 : ∀ a ∈ (T ⊓ K₁).subgroupOf K₁, ∃ k : ℕ, a ^ 2 ^ k = 1 := by
    intro a ha
    have haT : (a : G) ∈ T := (Subgroup.mem_subgroupOf.mp ha).1
    obtain ⟨k, hk⟩ := S.hyp.sylow.1 ⟨a, haT⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
  obtain ⟨a₀, ha₀, hfa₀, hfa₀2⟩ := exists_involution_of_surjective (toAutI hF I)
    (toAutI_surjective hF I) hY hsyl.2.2 hA2
  have hx₀T : (a₀ : G) ∈ T := (Subgroup.mem_subgroupOf.mp ha₀).1
  have hx₀K : (a₀ : G) ∈ K₁ := a₀.2
  have hx₀G : (a₀ : G) ∈ mcOf T := hK₁G hx₀K
  set ρ := actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I (mcOf T)) with hρ
  have hae : ((toAutI hF I a₀ : ↥(autIH (quasithinOmegaOneCenter T) I (mcOf T) K₁)) :
      MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (conjClosure I (mcOf T)))) =
      ρ ⟨(a₀ : G), hx₀G⟩ := rfl
  have ha : ρ ⟨(a₀ : G), hx₀G⟩ ∈ autIH (quasithinOmegaOneCenter T) I (mcOf T) K₁ := by
    rw [← hae]
    exact (toAutI hF I a₀).2
  have ha1 : ρ ⟨(a₀ : G), hx₀G⟩ ≠ 1 := by
    intro h
    exact hfa₀ (Subtype.ext (hae.trans h))
  have ha2 : ρ ⟨(a₀ : G), hx₀G⟩ ^ 2 = 1 := by
    have := congrArg Subtype.val hfa₀2
    rw [← hae]
    simpa using this
  have hb₀K : s * (a₀ : G) * s⁻¹ ∈ conjSub s K₁ := mul_mem_conjSub hx₀K
  have hb₀T : s * (a₀ : G) * s⁻¹ ∈ T := T.mul_mem (T.mul_mem hsT hx₀T) (T.inv_mem hsT)
  have hb₀G : s * (a₀ : G) * s⁻¹ ∈ mcOf T := hK₂G hb₀K
  have hb₀eq : (⟨s * (a₀ : G) * s⁻¹, hb₀G⟩ : ↥(mcOf T)) =
      ⟨s, hsG⟩ * ⟨(a₀ : G), hx₀G⟩ * (⟨s, hsG⟩ : ↥(mcOf T))⁻¹ := Subtype.ext rfl
  have hbe : ρ ⟨s * (a₀ : G) * s⁻¹, hb₀G⟩ =
      ρ ⟨s, hsG⟩ * ρ ⟨(a₀ : G), hx₀G⟩ * (ρ ⟨s, hsG⟩)⁻¹ := by
    rw [hb₀eq, map_mul, map_mul, map_inv]
  have hb : ρ ⟨s * (a₀ : G) * s⁻¹, hb₀G⟩ ∈
      autIH (quasithinOmegaOneCenter T) I (mcOf T) (conjSub s K₁) := by
    rw [autIH_eq_map hF hK₂G]
    exact ⟨⟨s * (a₀ : G) * s⁻¹, hb₀G⟩, Subgroup.mem_subgroupOf.mpr hb₀K, rfl⟩
  have hb1 : ρ ⟨s * (a₀ : G) * s⁻¹, hb₀G⟩ ≠ 1 := by
    intro h
    apply ha1
    have h1 : ρ ⟨(a₀ : G), hx₀G⟩ = (ρ ⟨s, hsG⟩)⁻¹ * ρ ⟨s * (a₀ : G) * s⁻¹, hb₀G⟩ * ρ ⟨s, hsG⟩ := by
      rw [hbe]; group
    rw [h1, h]
    group
  have hb2 : ρ ⟨s * (a₀ : G) * s⁻¹, hb₀G⟩ ^ 2 = 1 := by
    have h1 : ρ ⟨s * (a₀ : G) * s⁻¹, hb₀G⟩ ^ 2 =
        ρ ⟨s, hsG⟩ * ρ ⟨(a₀ : G), hx₀G⟩ ^ 2 * (ρ ⟨s, hsG⟩)⁻¹ := by
      rw [hbe, pow_two, pow_two]; group
    rw [h1, ha2]
    group
  have hMp : autIH (quasithinOmegaOneCenter T) I (mcOf T) (conjClosure K₁ T) =
      autIH (quasithinOmegaOneCenter T) I (mcOf T) K₁ ⊔
        autIH (quasithinOmegaOneCenter T) I (mcOf T) (conjSub s K₁) :=
    UB.autIH_conjClosure_eq hF hsG hK₀
  have hcomm : ∀ x ∈ autIH (quasithinOmegaOneCenter T) I (mcOf T) K₁,
      ∀ y ∈ autIH (quasithinOmegaOneCenter T) I (mcOf T) (conjSub s K₁), x * y = y * x := by
    intro x hx y hy
    rw [autIH_eq_map hF hK₁G] at hx
    rw [autIH_eq_map hF hK₂G] at hy
    obtain ⟨k₁, hk₁, rfl⟩ := hx
    obtain ⟨k₂, hk₂, rfl⟩ := hy
    have hc := hcommK (k₁ : G) (Subgroup.mem_subgroupOf.mp hk₁) (k₂ : G)
      (Subgroup.mem_subgroupOf.mp hk₂)
    have h1 : ρ (k₁ * k₂ * k₁⁻¹ * k₂⁻¹) = 1 := hF.actH_eq_one_of_mem_pCoreOf hIU hc
    have h2 : ρ k₁ * ρ k₂ * (ρ k₁)⁻¹ * (ρ k₂)⁻¹ = 1 := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact h1
    calc ρ k₁ * ρ k₂ = (ρ k₁ * ρ k₂ * (ρ k₁)⁻¹ * (ρ k₂)⁻¹) * (ρ k₂ * ρ k₁) := by group
      _ = ρ k₂ * ρ k₁ := by rw [h2, one_mul]
  obtain ⟨φ₁, hs₁, hker₁⟩ := hdec.exists_phi_gen
  obtain ⟨φ₂, hs₂, hker₂⟩ := hdec.swap.exists_phi_gen
  obtain ⟨x, y, hxH₁, hyH₂, hφx, hφy, hx5, hy5, -, -⟩ :=
    exists_commuting_pair (by norm_num : Nat.Prime 5) (by norm_num : (5 : ℕ) ≠ 2) hdec φ₁ hs₁
      hker₁ φ₂ hs₂ hker₂
  have hH₁H : H₁ ≤ H := hdec.le₁.trans hdec.le
  have hH₂H : H₂ ≤ H := hdec.le₂.trans hdec.le
  have hxH : x ∈ H := hH₁H hxH₁
  have hyH : y ∈ H := hH₂H hyH₂
  have hxG : x ∈ mcOf T := hHG hxH
  have hyG : y ∈ mcOf T := hHG hyH
  have hxodd : Odd (orderOf x) := Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hx5)
  have hyodd : Odd (orderOf y) := Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hy5)
  have hxK₀ : x ∈ conjClosure K₁ T :=
    hKzK₀ ▸ le_conjClosure _ _ (mem_oTwoUpper_of_odd hxH hxodd)
  have hyK₀ : y ∈ conjClosure K₁ T :=
    hKzK₀ ▸ le_conjClosure _ _ (mem_oTwoUpper_of_odd hyH hyodd)
  have hsub₁ : tildeOf (quasithinOmegaOneCenter T) (uHi T M H H₁) ≤
      tildeOf (quasithinOmegaOneCenter T) (conjClosure I (mcOf T)) :=
    (tildeOf_uHi_le S hred hdec φ₁ hker₁ hφx hxG hxK₀).trans hclaim.ge
  have hsub₂ : tildeOf (quasithinOmegaOneCenter T) (uHi T M H H₂) ≤
      tildeOf (quasithinOmegaOneCenter T) (conjClosure I (mcOf T)) :=
    (tildeOf_uHi_le S hred hdec.swap φ₂ hker₂ hφy hyG hyK₀).trans hclaim.ge
  have hc₁ : Nat.card ↥(subM (quasithinOmegaOneCenter T) (conjClosure I (mcOf T))
      (uHi T M H H₁)) = 2 ^ 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsub₁).toEquiv).trans
      (card_tildeOf_uHi S hred hH₁H (hdec.rank₁.1 rfl))
  have hc₂ : Nat.card ↥(subM (quasithinOmegaOneCenter T) (conjClosure I (mcOf T))
      (uHi T M H H₂)) = 2 ^ 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsub₂).toEquiv).trans
      (card_tildeOf_uHi S hred hH₂H (hdec.rank₂.1 rfl))
  have hinf12 : subM (quasithinOmegaOneCenter T) (conjClosure I (mcOf T)) (uHi T M H H₁) ⊓
      subM (quasithinOmegaOneCenter T) (conjClosure I (mcOf T)) (uHi T M H H₂) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have h1 : (w : SecQuot (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
        (quasithinOmegaOneCenter T)) ∈ tildeOf (quasithinOmegaOneCenter T) (uHi T M H H₁) ⊓
          tildeOf (quasithinOmegaOneCenter T) (uHi T M H H₂) := ⟨hw.1, hw.2⟩
    rw [tildeOf_uHi_inf_eq_bot hdec, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  have hfixX : ∀ {Hi : Subgroup G}, Hi ≤ H → ∀ {z : G} (hz : z ∈ pCoreOf 2 H) (hzG : z ∈ mcOf T),
      ∀ w ∈ subM (quasithinOmegaOneCenter T) (conjClosure I (mcOf T)) (uHi T M H Hi),
        ρ ⟨z, hzG⟩ w = w := by
    intro Hi hHi z hz hzG w hw
    obtain ⟨⟨u, huN⟩, huJ, hu⟩ := mem_secImg.mp hw
    exact actH_fix_of_comm _ _ ⟨z, hzG⟩ huN (comm_mem_of_mem_pCoreOf S hred hHi hz huJ) w hu.symm
  have hx₀P : (a₀ : G) ∈ pCoreOf 2 H := hinf _ hx₀T (hK₁Kz hx₀K)
  have hb₀P : s * (a₀ : G) * s⁻¹ ∈ pCoreOf 2 H := hinf _ hb₀T (hK₂Kz hb₀K)
  exact false_of_two_fixed hV eL ⟨n, hL, hΩ⟩ hMp hcomm ha hb ha1 hb1 ha2 hb2 hinf12 hc₁ hc₂
    (fun w hw => hfixX hH₁H hx₀P hx₀G w hw) (fun w hw => hfixX hH₁H hb₀P hb₀G w hw)
    (fun w hw => hfixX hH₂H hx₀P hx₀G w hw) (fun w hw => hfixX hH₂H hb₀P hb₀G w hw)

end Main

end CFSG.Quasithin.S146zU.UD3
