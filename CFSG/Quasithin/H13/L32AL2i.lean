module

public import CFSG.Quasithin.H13.L32AL2h
public import CFSG.Quasithin.Background.F918Z4c2Real
public import CFSG.Quasithin.H13.L32AM50h

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.H13.L32A.C
open scoped IsMulCommutative

section General

variable {W' : Type} [CommGroup W'] [Finite W']

omit [Finite W'] in
theorem false_of_sum (hV : ∀ w : W', w ^ 2 = 1) {L₁ L₂ : Subgroup (MulAut W')}
    {t : MulAut W'} (hs1 : ∀ g ∈ L₁, t⁻¹ * g * t ∈ L₂) (hs2 : ∀ g ∈ L₂, t⁻¹ * g * t ∈ L₁)
    (hA : ∀ a ∈ commSub ⊤ L₁, ∀ g ∈ L₂, g a = a)
    (hsum : (⊤ : Subgroup W') ≤ commSub ⊤ L₁ ⊔ (commSub ⊤ L₁).map t.toMonoidHom)
    {y₁ y₂ : MulAut W'} (hy₁ : y₁ ∈ L₁) (hy₂ : y₂ ∈ L₂) (hy3 : y₁ ^ 3 = 1) {P : Subgroup W'}
    (hP : P ≠ ⊥) (hsame : ∀ v ∈ P, y₁ v = y₂ v) (hfpf : ∀ v ∈ P, y₁ v = v → v = 1) :
    False := by
  have hAinv : ∀ g ∈ L₁, ∀ a ∈ commSub ⊤ L₁, g a ∈ commSub ⊤ L₁ := fun g hg a ha =>
    B1.commSub_smul_mem (M := ⊤) (M' := ⊤) (Y := L₁) (Y' := L₁) g
      (fun y hy => mul_mem (mul_mem hg hy) (inv_mem hg)) (fun _ _ => Subgroup.mem_top _) a ha
  refine hP (eq_bot_of_same_action hV (A := commSub ⊤ L₁)
    (B := (commSub ⊤ L₁).map t.toMonoidHom) (y₁ := y₁) (y₂ := y₂) hy3 ?_ ?_
    (fun a ha => hA a ha y₂ hy₂) (le_top.trans hsum) hsame hfpf)
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨(t⁻¹ * y₂ * t) a, hAinv _ (hs2 y₂ hy₂) a ha, ?_⟩
    show t ((t⁻¹ * y₂ * t) a) = y₂ (t a)
    simp [MulAut.mul_apply]
  · rintro _ ⟨a, ha, rfl⟩
    show y₁ (t a) = t a
    have h2 := congrArg t (hA a ha _ (hs1 y₁ hy₁))
    simpa [MulAut.mul_apply] using h2

end General

variable {G : Type} [Group G] [Finite G] {T L V K W : Subgroup G} {t₀ : G}

namespace TopCtx

variable (X : TopCtx T L V K W t₀) [IsMulCommutative ↥(conjClosure V (A6.g1 T V))]

theorem act_mem_normalizer {n : ↥(A6.g1 T V)} (hn : (n : G) ∈ Subgroup.normalizer (K : Set G)) :
    X.top.act n ∈ Subgroup.normalizer (X.img K : Set (MulAut (Hat V (A6.g1 T V) W))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨κ, hκ, rfl⟩
    refine ⟨n * κ * n⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    show ((n * κ * n⁻¹ : ↥(A6.g1 T V)) : G) ∈ K
    simpa using (Subgroup.mem_normalizer_iff.mp hn _).mp hκ
  · rintro ⟨κ, hκ, hκe⟩
    refine ⟨n⁻¹ * κ * n, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) _).mp hκ
      show ((n⁻¹ * κ * n : ↥(A6.g1 T V)) : G) ∈ K
      simpa using this
    · rw [map_mul, map_mul, map_inv, hκe]
      group

theorem img_Kt_eq : X.img (K.map (MulAut.conj t₀ : G →* G)) =
    conjAutSub (X.top.act ⟨t₀, X.C.ht₀H⟩) (X.img K) := by
  rw [img_eq_map, img_eq_map, ← X.C.kb'_eq, conjAutSub, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext c w
  simp [MulAut.conj_apply, map_mul, map_inv]
  rfl

theorem img_K₀_eq :
    X.img (conjClosure K T) = X.img K ⊔ X.img (K.map (MulAut.conj t₀ : G →* G)) := by
  have C := X.C
  have hTH : T ≤ A6.g1 T V := by rw [X.R.hG1]; exact le_sup_right
  have hKH : K ≤ A6.g1 T V := le_of_mem_cComp X.R.hK
  have hKt : K.map (MulAut.conj t₀ : G →* G) ≤ conjClosure K T := by
    rintro _ ⟨k, hk, rfl⟩
    simpa using mem_conjClosure C.ht₀ hk
  have hK₀le : conjClosure K T ≤ K ⊔ K.map (MulAut.conj t₀ : G →* G) := by
    refine conjClosure_le fun s hs k hk => ?_
    rcases C.two s (hTH hs) with h | h
    · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp h k).mp hk)
    · refine Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨(t₀⁻¹ * s) * k * (t₀⁻¹ * s)⁻¹,
        (Subgroup.mem_normalizer_iff.mp h k).mp hk, ?_⟩)
      simp only [MonoidHom.coe_ofClass, MulAut.conj_apply]
      group
  have heq : conjClosure K T = K ⊔ K.map (MulAut.conj t₀ : G →* G) :=
    le_antisymm hK₀le (sup_le (le_conjClosure K T) hKt)
  rw [img, img, img, heq, Subgroup.subgroupOf_sup hKH C.hKtH, Subgroup.map_sup]

theorem exists_pair (hA37 : A37ForSQTK) (h29 : Thm14_7_29) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    ∃ y₁ ∈ X.img K, ∃ y₂ ∈ X.img (K.map (MulAut.conj t₀ : G →* G)), y₁ ^ 3 = 1 ∧
      y₂ ^ 3 = 1 ∧ vHat V (A6.g1 T V) W ≠ ⊥ ∧ (∀ v ∈ vHat V (A6.g1 T V) W, y₁ v = y₂ v) ∧
      ∀ v ∈ vHat V (A6.g1 T V) W, y₁ v = v → v = 1 := by
  have C := X.C
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V C.S.hyp.hyp C.S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 C.S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  have S14 := Hyp147.set14 C.S.hyp h1222 h1332 h1334 hV2
  obtain ⟨y, hyL, hy3, hfpfy⟩ := exists_l1_fpf C.S.hyp hMod h1222 h1332 h1334
  have hl1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hy : y ∈ l1 T L V := by rw [← hl1]; exact hyL
  have hyH : y ∈ A6.g1 T V := Setting147.l1H' C.S hy
  obtain ⟨k₁, hk₁K, k₂, hk₂K, he, hk₁3, hk₂3, hk₁, hk₂⟩ := C.decomp hA37 hy hy3
  obtain ⟨β₁, β₂, rfl, rfl, hβ₁X, -, hβ12, hyβ⟩ :=
    CtxL2Same.exists_same_action C hA37 h29 h1222 h1332 h1334 S14 hy hy3 hfpfy hk₁K hk₂K he hk₁
      hk₂
  have hVW := Setting147.inf_V_eq X.top.S h1222 h1332 h1334 X.top.hV₁W X.top.hWU X.top.hHW
  have hF := X.top.hF
  have hcentral : ∀ z ∈ fsuV1 T V, ∀ b ∈ A6.g1 T V, z * b = b * z := fun z hz b hb =>
    (Subgroup.mem_centralizer_iff.mp (hF.H_le_centralizer hb)) z hz
  refine ⟨X.top.act β₁, ?_, X.top.act β₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [img_eq_map]
    exact ⟨_, hk₁K, rfl⟩
  · rw [img_eq_map]
    exact ⟨_, hk₂K, rfl⟩
  · rw [← X.actDot_mk β₁, ← map_pow, hk₁3, map_one]
  · rw [← X.actDot_mk β₂, ← map_pow, hk₂3, map_one]
  ·
    obtain ⟨v, hv, hv1⟩ : ∃ v ∈ V, v ∉ fsuV1 T V := by
      by_contra hno
      push Not at hno
      have := Subgroup.card_le_of_le (show V ≤ fsuV1 T V from hno)
      rw [S14.card_V, S14.card_V1] at this
      omega
    intro hbot
    have hmem : InternalSec.secMk (W.subgroupOf (conjClosure V (A6.g1 T V)))
        ⟨v, le_conjClosure V _ hv⟩ ∈ vHat V (A6.g1 T V) W := ⟨⟨v, le_conjClosure V _ hv⟩, hv, rfl⟩
    rw [hbot, Subgroup.mem_bot, A6.A6Mod.secMk_eq_one_iff] at hmem
    apply hv1
    have : v ∈ V ⊓ W := Subgroup.mem_inf.mpr ⟨hv, hmem⟩
    rwa [hVW] at this
  ·
    rintro _ ⟨u, hu, rfl⟩
    have hu' : (u : G) ∈ V := hu
    rw [X.top.act_secMk, X.top.act_secMk, ← mul_inv_eq_one, ← map_inv, ← map_mul,
      A6.A6Mod.secMk_eq_one_iff]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Setup.rho_apply_coe]
    obtain ⟨-, -, hβv⟩ := L32NSet14.mem_trivSub.mp hβ12
    have h1 := (Subgroup.mem_normalizer_iff.mp hβ₁X.2 _).mp (hβv (u : G) hu')
    apply X.top.hV₁W
    have e : (β₁ : G) * u * (β₁ : G)⁻¹ * ((β₂ : G) * u * (β₂ : G)⁻¹)⁻¹ =
        ((β₁ : G) * (((β₁ : G)⁻¹ * β₂) * u * ((β₁ : G)⁻¹ * β₂)⁻¹ * (u : G)⁻¹) * (β₁ : G)⁻¹)⁻¹ := by
      group
    rw [e]
    exact inv_mem h1
  ·
    rintro _ ⟨u, hu, rfl⟩ hfix
    have hu' : (u : G) ∈ V := hu
    rw [X.top.act_secMk, ← mul_inv_eq_one, ← map_inv, ← map_mul,
      A6.A6Mod.secMk_eq_one_iff] at hfix
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Setup.rho_apply_coe] at hfix
    have hβV : (β₁ : G) * u * (β₁ : G)⁻¹ * (u : G)⁻¹ ∈ V :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp hβ₁X.1 _).mp hu') (inv_mem hu')
    have h1 : (β₁ : G) * u * (β₁ : G)⁻¹ * (u : G)⁻¹ ∈ fsuV1 T V := by
      have : (β₁ : G) * u * (β₁ : G)⁻¹ * (u : G)⁻¹ ∈ V ⊓ W := Subgroup.mem_inf.mpr ⟨hβV, hfix⟩
      rwa [hVW] at this
    obtain ⟨-, -, hxv⟩ := L32NSet14.mem_trivSub.mp hyβ
    have h2 := hxv (u : G) hu'
    have hy2H : y ^ 2 ∈ A6.g1 T V := pow_mem hyH 2
    set c := ((y ^ 2)⁻¹ * β₁) * (u : G) * ((y ^ 2)⁻¹ * β₁)⁻¹ * (u : G)⁻¹ with hc
    have hcy : c * y ^ 2 = y ^ 2 * c := hcentral c h2 _ hy2H
    have h3 : y ^ 2 * (u : G) * (y ^ 2)⁻¹ * (u : G)⁻¹ =
        c⁻¹ * ((β₁ : G) * u * (β₁ : G)⁻¹ * (u : G)⁻¹) := by
      calc y ^ 2 * (u : G) * (y ^ 2)⁻¹ * (u : G)⁻¹
          = c⁻¹ * (y ^ 2 * c * (y ^ 2)⁻¹) * (y ^ 2 * (u : G) * (y ^ 2)⁻¹ * (u : G)⁻¹) := by
            rw [← hcy]
            group
        _ = c⁻¹ * ((β₁ : G) * u * (β₁ : G)⁻¹ * (u : G)⁻¹) := by
            rw [hc]
            group
    have h4 : y ^ 2 * (u : G) * (y ^ 2)⁻¹ * (u : G)⁻¹ ∈ fsuV1 T V := by
      rw [h3]
      exact mul_mem (inv_mem h2) h1
    have hy2 : y ^ 2 = y⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ]
      exact hy3
    have h6 := (Subgroup.mem_normalizer_iff.mp (hF.toHypF91.H_normalizes_V₁ hyH) _).mp h4
    have e : y * (u : G) * y⁻¹ * (u : G)⁻¹ =
        (y * (y ^ 2 * (u : G) * (y ^ 2)⁻¹ * (u : G)⁻¹) * y⁻¹)⁻¹ := by
      rw [hy2]
      group
    have hu1 := hfpfy (u : G) hu' (by rw [e]; exact inv_mem h6)
    rw [A6.A6Mod.secMk_eq_one_iff]
    exact X.top.hV₁W hu1

theorem t_mem_img : X.top.act ⟨t₀, X.C.ht₀H⟩ ∈ X.img T :=
  ⟨⟨t₀, X.C.ht₀H⟩, Subgroup.mem_subgroupOf.mpr X.C.ht₀, rfl⟩

theorem t_sq_mem_normalizer : X.top.act ⟨t₀, X.C.ht₀H⟩ * X.top.act ⟨t₀, X.C.ht₀H⟩ ∈
    Subgroup.normalizer (X.img K : Set (MulAut (Hat V (A6.g1 T V) W))) := by
  rw [← map_mul]
  exact X.act_mem_normalizer X.C.sq_mem

theorem t_not_mem_normalizer (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6)
    (h33 : Lemma14_7_33) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    X.top.act ⟨t₀, X.C.ht₀H⟩ ∉
      Subgroup.normalizer (X.img K : Set (MulAut (Hat V (A6.g1 T V) W))) := by
  intro hn
  have C := X.C
  have hinj := X.actDot_injective hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
  have hK1 : ∀ k ∈ modO2Image (A6.g1 T V) K, k = 1 := by
    intro k hk
    apply C.eq_one_of_mem_kb_kt hA37 hk
    have h1 : X.actDot k ∈ X.img K := by rw [img_eq_map]; exact ⟨k, hk, rfl⟩
    have h2 : X.actDot k ∈ X.img (K.map (MulAut.conj t₀ : G →* G)) := by
      rw [img_Kt_eq]
      refine ⟨(X.top.act ⟨t₀, C.ht₀H⟩)⁻¹ * X.actDot k * X.top.act ⟨t₀, C.ht₀H⟩, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) _).mp h1
        simpa using this
      · simp [MulAut.conj_apply, mul_assoc]
    rw [img_eq_map] at h2
    obtain ⟨k', hk', hkk'⟩ := h2
    rw [hinj hkk'] at hk'
    exact hk'
  have : IsSimpleGroup ↥(modO2Image (A6.g1 T V) K) := C.isSimpleGroup_kb
  obtain ⟨⟨a, ha⟩, ha1⟩ := exists_ne (1 : ↥(modO2Image (A6.g1 T V) K))
  exact ha1 (Subtype.ext (hK1 a ha))

theorem omega4 (hD36 : D36) (hD37 : D37) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK)
    (h76 : Lemma14_7_6) (h33 : Lemma14_7_33) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd)
    (h29 : Thm14_7_29) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    Omega4PlusModule (autSub (X.img (conjClosure K T)) ⊤) 2 := by
  have hV : ∀ w : Hat V (A6.g1 T V) W, w ^ 2 = 1 := fun w => by
    rw [pow_two]; exact X.top.sec_sq w
  set t := X.top.act ⟨t₀, X.C.ht₀H⟩ with ht
  obtain ⟨V', hV'⟩ := X.exists_irrPlusOn hA37 h1222 h1332 h1334
  have hD := X.d31 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334 hV'.1
  have hne : V' ≠ ⊥ := (bot_le.trans_lt hV'.1.2.2.2.1).ne'
  have hVT : orbSup (X.img T) V' = ⊤ := X.orbSup_eq_top hne hV'.1.2.1
  obtain ⟨B, hBL, hB⟩ := X.top.hF.F916_3_aux
  have hBT : B ≤ T := hBL.trans (L32A.pCoreOf_le_of_le X.R.S.hyp le_sup_right)
  have hA := X.qOff_img hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334 hB hBT
  rw [← hVT] at hA
  have hstd : D3Std (X.img (A6.g1 T V)) (X.img (conjClosure K T)) (X.img T) (X.img K) V' :=
    ⟨hD, hA.qhat_VT hD.exp, by rw [hVT]; exact hV'⟩
  have htL := X.t_not_mem_normalizer hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
  have hMp : X.img (conjClosure K T) = X.img K ⊔ conjAutSub t (X.img K) := by
    rw [img_K₀_eq, img_Kt_eq]
  have hsq := X.t_sq_mem_normalizer
  have hs1 : ∀ g ∈ X.img K, t⁻¹ * g * t ∈ conjAutSub t (X.img K) := by
    intro g hg
    refine ⟨(t * t)⁻¹ * g * (t * t), ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (inv_mem hsq) g).mp hg
      simpa using this
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hs2 : ∀ g ∈ conjAutSub t (X.img K), t⁻¹ * g * t ∈ X.img K := by
    rintro _ ⟨ℓ, hℓ, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hℓ
  have hs1' : ∀ g ∈ conjAutSub t (X.img K), t⁻¹⁻¹ * g * t⁻¹ ∈ X.img K := by
    rintro _ ⟨ℓ, hℓ, rfl⟩
    have := (Subgroup.mem_normalizer_iff.mp hsq ℓ).mp hℓ
    simpa [MulAut.conj_apply, mul_assoc] using this
  have hs2' : ∀ g ∈ X.img K, t⁻¹⁻¹ * g * t⁻¹ ∈ conjAutSub t (X.img K) := fun g hg =>
    ⟨g, hg, by simp [MulAut.conj_apply]⟩
  obtain ⟨y₁, hy₁, y₂, hy₂, hy3, hy3', hP, hsame, hfpf⟩ :=
    X.exists_pair hA37 h29 h1222 h1332 h1334
  rw [img_Kt_eq] at hy₂
  have hfix : fixV (X.img (conjClosure K T)) = ⊥ := X.fixV_img_K₀ hA37 h1222 h1332 h1334
  by_cases hVeq : V' = orbSup (X.img T) V'
  · have hVtop : V' = ⊤ := hVeq.trans hVT
    rcases hD37 _ _ _ _ _ _ hstd hVeq t X.t_mem_img htL hMp with ⟨n, hn1, hn2⟩ | ⟨hn1, -⟩
    · rw [hVtop] at hn1 hn2
      obtain ⟨φ⟩ := X.nonempty_equiv_img_K hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
      have h60 : Nat.card ↥(autSub (X.img K) ⊤) = 60 := by
        rw [Nat.card_congr (autSubTopEquiv _).toEquiv, Nat.card_congr φ.toEquiv,
          nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        rfl
      have hc := Z4c2.card_of_isPSL_two_two hn1
      rw [h60] at hc
      have hn : n = 2 := by
        rcases Nat.lt_or_ge n 3 with h | h
        · interval_cases n
          · norm_num at hc
          · norm_num at hc
          · rfl
        · exfalso
          have h8 : 8 ≤ 2 ^ n := by
            calc 8 = 2 ^ 3 := by norm_num
              _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
          have h64 : 64 ≤ (2 ^ n) ^ 2 := by
            calc 64 = 8 ^ 2 := by norm_num
              _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h8 2
          have h504 : 8 * 63 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h8 (by omega)
          omega
      rw [hn] at hn2
      exact hn2
    · exfalso
      rw [hVtop] at hn1
      obtain ⟨φ⟩ := X.nonempty_equiv_img_K hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
      have h1 := SBc11.card_of_isPSL_three_two hn1
      rw [Nat.card_congr (autSubTopEquiv _).toEquiv, Nat.card_congr φ.toEquiv,
        nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
      exact absurd h1 (by decide)
  · exfalso
    have hlt : V' < orbSup (X.img T) V' := lt_of_le_of_ne (le_orbSup _ _) hVeq
    rcases hD36.1 _ _ _ _ _ _ hstd hlt t X.t_mem_img htL hMp with hc | hc
    · obtain ⟨-, ⟨hsum, hA'⟩, -⟩ := hc
      rw [hVT, hfix, inf_bot_eq] at hsum
      rw [hVT] at hA'
      exact false_of_sum hV hs1 hs2 hA' (hsum.1.trans (sup_bot_eq _)).le hy₁ hy₂ hy3 hP hsame
        hfpf
    · obtain ⟨-, ⟨hsum, hA'⟩, -⟩ := hc
      rw [hVT, hfix, inf_bot_eq] at hsum
      rw [hVT, conjAutSub_inv_conjAutSub] at hA'
      exact false_of_sum hV hs1' hs2' hA' (hsum.1.trans (sup_bot_eq _)).le hy₂ hy₁ hy3' hP
        (fun v hv => (hsame v hv).symm) (fun v hv h => hfpf v hv ((hsame v hv).trans h))

end TopCtx

end CFSG.Quasithin.H13.L32A.L2
