module

public import CFSG.Quasithin.H13.L32AL2c
public import CFSG.Quasithin.H13.L32AL2d
public import CFSG.Quasithin.H13.L32A715i
public import CFSG.Quasithin.Background.C126RFCases
public import CFSG.Quasithin.H13.L32AC35a
public import CFSG.Quasithin.H13.L32ACSk8

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.H13.L32A.C CFSG.Quasithin.C1Pack

variable {G : Type} [Group G] [Finite G] {T L V K : Subgroup G}

theorem exists_ctxL2_of_red (hA37 : A37ForSQTK) (hA38 : A38ForSQTK)
    (R : L2Red G T L V K) :
    ∃ t₀ : G, CtxL2 T L V (A6.g1 T V) K t₀ 2 := by
  have hKH := le_of_mem_cComp R.hK
  have h121 := lemma_1_2_1_three R.S.hyp.fsu.qtke R.S.hyp.fsu.simple R.S.hyp.fsu.nonabelian
    hA37 hA38 R.S.hz.1.2 R.hK
  have hyN : ∀ y ∈ l1 T L V, y ^ 3 = 1 → y ∈ Subgroup.normalizer (K : Set G) :=
    fun y hy hy3 =>
      mem_normalizer_of_cube hKH (h121.imp_right fun h => h.1) (Setting147.l1H' R.S hy) hy3
  obtain ⟨t₀, ht₀T, ht₀N⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) := by
    by_contra h
    push Not at h
    exact R.hT h
  have ht₀H := Setting147.TH' R.S ht₀T
  have h2 : (conjSubgroupsBy (A6.g1 T V) K).ncard = 2 := by
    rcases h121 with hn | ⟨h2, -⟩
    · exact absurd ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hn ht₀H) ht₀N
    · exact h2
  exact ⟨t₀, ⟨⟨R.S, R.hK, ht₀T, ht₀N, mem_normalizer_or_of_ncard h2 ht₀H ht₀N, hyN⟩, le_rfl,
    C126.isPSL_two_two_two_of_alternating_five _ R.hA5⟩⟩

theorem eq_one_of_centralizes (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6)
    (h33 : Lemma14_7_33) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (R : L2Red G T L V K)
    {t₀ : G} (C : CtxL2 T L V (A6.g1 T V) K t₀ 2)
    {c : ↥(A6.g1 T V) ⧸ CFSG.pCore 2 ↥(A6.g1 T V)}
    (h1 : ∀ a ∈ modO2Image (A6.g1 T V) K, c * a = a * c)
    (h2 : ∀ b ∈ modO2Image (A6.g1 T V) (K.map (MulAut.conj t₀ : G →* G)), c * b = b * c) :
    c = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have S := R.S
  have hKH := le_of_mem_cComp R.hK
  have hTH := Setting147.TH' S
  have hSH := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hTH
  have hmono : ∀ {A B : Subgroup G}, A ≤ B → modO2Image (A6.g1 T V) A ≤ modO2Image (A6.g1 T V) B :=
    fun h => Subgroup.map_mono fun _ hz => h hz
  have hK₀H : conjClosure K T ≤ A6.g1 T V := conjClosure_le fun s hs k hk =>
    mul_mem (mul_mem (hTH hs) (hKH hk)) (inv_mem (hTH hs))
  have hK₀n : A6.g1 T V ≤ Subgroup.normalizer (conjClosure K T : Set G) :=
    normal_conjClosure_of_pCoreOf_ne_bot S.hyp.fsu.qtke S.hyp.fsu.simple S.hyp.fsu.nonabelian
      hA37 hA38 S.hz.1.2 hSH R.hK
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
  have hsup : modO2Image (A6.g1 T V) (conjClosure K T) ≤
      modO2Image (A6.g1 T V) K ⊔ modO2Image (A6.g1 T V) (K.map (MulAut.conj t₀ : G →* G)) := by
    refine (hmono hK₀le).trans ?_
    show ((K ⊔ K.map (MulAut.conj t₀ : G →* G)).subgroupOf (A6.g1 T V)).map _ ≤ _
    rw [Subgroup.subgroupOf_sup hKH C.hKtH, Subgroup.map_sup]
    exact le_rfl
  have hK₀bn : (modO2Image (A6.g1 T V) (conjClosure K T)).Normal := by
    have h1 : ((conjClosure K T).subgroupOf (A6.g1 T V)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hK₀H).mpr hK₀n
    exact h1.map _ (QuotientGroup.mk'_surjective _)
  have hCbot : Subgroup.centralizer (modO2Image (A6.g1 T V) (conjClosure K T) :
      Set (↥(A6.g1 T V) ⧸ CFSG.pCore 2 ↥(A6.g1 T V))) = ⊥ := by
    have hC3 : Nat.Coprime 3 (Nat.card ↥(Subgroup.centralizer
        (modO2Image (A6.g1 T V) (conjClosure K T) :
          Set (↥(A6.g1 T V) ⧸ CFSG.pCore 2 ↥(A6.g1 T V))))) := by
      refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 => ?_
      obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' 3 h3
      have hd3 : (d : ↥(A6.g1 T V) ⧸ CFSG.pCore 2 ↥(A6.g1 T V)) ^ 3 = 1 := by
        rw [← hd, ← Subgroup.orderOf_coe]
        exact pow_orderOf_eq_one _
      have hd1 : (d : ↥(A6.g1 T V) ⧸ CFSG.pCore 2 ↥(A6.g1 T V)) ≠ 1 := fun h => by
        have : d = 1 := Subtype.ext h
        rw [this, orderOf_one] at hd
        omega
      have hdK : ∀ m ∈ modO2Image (A6.g1 T V) K,
          (d : ↥(A6.g1 T V) ⧸ CFSG.pCore 2 ↥(A6.g1 T V)) * m = m * d := fun m hm =>
        ((Subgroup.mem_centralizer_iff.mp d.2) m (hmono (le_conjClosure K T) hm)).symm
      have hdK' : ∀ m ∈ modO2Image (A6.g1 T V) (K.map (MulAut.conj t₀ : G →* G)),
          (d : ↥(A6.g1 T V) ⧸ CFSG.pCore 2 ↥(A6.g1 T V)) * m = m * d := fun m hm =>
        ((Subgroup.mem_centralizer_iff.mp d.2) m (hmono hKt hm)).symm
      exact hd1 (CFSG.Quasithin.H13.L32A.C.eq_one_of_centralizes_two (pRank_three_star_le_two S)
        (fun a ha b hb => C.commute_kb hA37 ha hb) C.center_kb C.center_kt C.three_dvd_kb
        C.three_dvd_kt hdK hdK' hd3)
    have hle : Subgroup.centralizer (modO2Image (A6.g1 T V) (conjClosure K T) :
        Set (↥(A6.g1 T V) ⧸ CFSG.pCore 2 ↥(A6.g1 T V))) ≤
          CFSG.pPrimeCore 3 (↥(A6.g1 T V) ⧸ CFSG.pCore 2 ↥(A6.g1 T V)) :=
      le_sSup (s := {N : Subgroup (↥(A6.g1 T V) ⧸ CFSG.pCore 2 ↥(A6.g1 T V)) |
        N.Normal ∧ Nat.Coprime 3 (Nat.card N)}) ⟨Subgroup.normal_centralizer, hC3⟩
    rw [pPrimeCore_star_eq_bot h76 h33 h36 hlist S] at hle
    exact eq_bot_iff.mpr hle
  have hcen : modO2Image (A6.g1 T V) K ⊔ modO2Image (A6.g1 T V) (K.map (MulAut.conj t₀ : G →* G)) ≤
      Subgroup.centralizer ({c} : Set (↥(A6.g1 T V) ⧸ CFSG.pCore 2 ↥(A6.g1 T V))) := by
    refine sup_le (fun m hm => ?_) (fun m hm => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (h1 m hm).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (h2 m hm).symm
  have hc : c ∈ Subgroup.centralizer (modO2Image (A6.g1 T V) (conjClosure K T) :
      Set (↥(A6.g1 T V) ⧸ CFSG.pCore 2 ↥(A6.g1 T V))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have := hcen (hsup hm)
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  rw [hCbot] at hc
  exact Subgroup.mem_bot.mp hc

theorem not_isTransvection_red (hA37 : A37ForSQTK) (hA38 : A38ForSQTK)
    (h29 : Thm14_7_29) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h76 : Lemma14_7_6) (h33 : Lemma14_7_33) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd)
    (R : L2Red G T L V K)
    (hF : HypF98 T V L (fsuV1 T V) V (A6.g1 T V))
    (τ : ↥(A6.g1 T V) ⧸ CFSG.pCore 2 ↥(A6.g1 T V)) :
    ¬ IsTransvection (rhoDot hF.toHypF91 τ) := by
  obtain ⟨t₀, C⟩ := exists_ctxL2_of_red hA37 hA38 R
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
  have hV : ∀ w : UMod hF.toHypF91, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hcentral : ∀ z ∈ fsuV1 T V, ∀ b ∈ A6.g1 T V, z * b = b * z := fun z hz b hb =>
    (Subgroup.mem_centralizer_iff.mp (hF.H_le_centralizer hb)) z hz
  have hρβ : ∀ (β : ↥(A6.g1 T V)) {v : G} (hv : v ∈ V),
      rhoDot hF.toHypF91 (QuotientGroup.mk' (CFSG.pCore 2 ↥(A6.g1 T V)) β)
          (clsU hF.toHypF91 (le_conjClosure V (A6.g1 T V) hv)) =
        clsU hF.toHypF91 (conj_mem_UH β.2 (le_conjClosure V (A6.g1 T V) hv)) :=
    fun β _ hv => rhoH_clsU hF.toHypF91 β (le_conjClosure V (A6.g1 T V) hv)
  let P : Subgroup (UMod hF.toHypF91) :=
    { carrier := {w | ∃ v : G, ∃ hv : v ∈ V, clsU hF.toHypF91 (le_conjClosure V _ hv) = w}
      mul_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a * b, V.mul_mem ha hb, by rw [clsU_mul]⟩
      one_mem' := ⟨1, V.one_mem, clsU_one _⟩
      inv_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨a⁻¹, V.inv_mem ha, by rw [clsU_inv]⟩ }
  have hP : P ≠ ⊥ := by
    obtain ⟨v, hv, hv1⟩ : ∃ v ∈ V, v ∉ fsuV1 T V := by
      by_contra hno
      push Not at hno
      have := Subgroup.card_le_of_le (show V ≤ fsuV1 T V from hno)
      rw [S14.card_V, S14.card_V1] at this
      omega
    intro hPb
    have hmem : clsU hF.toHypF91 (le_conjClosure V _ hv) ∈ P := ⟨v, hv, rfl⟩
    rw [hPb, Subgroup.mem_bot, clsU_eq_one_iff] at hmem
    exact hv1 hmem
  have hsame : ∀ w ∈ P,
      rhoDot hF.toHypF91 (QuotientGroup.mk' (CFSG.pCore 2 ↥(A6.g1 T V)) β₁) w =
        rhoDot hF.toHypF91 (QuotientGroup.mk' (CFSG.pCore 2 ↥(A6.g1 T V)) β₂) w := by
    rintro _ ⟨v, hv, rfl⟩
    rw [hρβ β₁ hv, hρβ β₂ hv, clsU_eq_iff]
    obtain ⟨-, -, hβv⟩ := L32NSet14.mem_trivSub.mp hβ12
    have h1 := (Subgroup.mem_normalizer_iff.mp hβ₁X.2 _).mp (hβv v hv)
    have h3 : ((β₂ : G) * v * (β₂ : G)⁻¹) * ((β₁ : G) * v * (β₁ : G)⁻¹)⁻¹ ∈ fsuV1 T V := by
      have e : ((β₂ : G) * v * (β₂ : G)⁻¹) * ((β₁ : G) * v * (β₁ : G)⁻¹)⁻¹ =
          (β₁ : G) * (((β₁ : G)⁻¹ * β₂) * v * ((β₁ : G)⁻¹ * β₂)⁻¹ * v⁻¹) * (β₁ : G)⁻¹ := by
        group
      rw [e]
      exact h1
    have hbH : (β₁ : G) * v * (β₁ : G)⁻¹ ∈ A6.g1 T V :=
      mul_mem (mul_mem β₁.2 (hF.toHypF91.V_le_H hv)) (inv_mem β₁.2)
    have hc := hcentral _ h3 _ hbH
    have e : ((β₁ : G) * v * (β₁ : G)⁻¹)⁻¹ * ((β₂ : G) * v * (β₂ : G)⁻¹) =
        ((β₁ : G) * v * (β₁ : G)⁻¹)⁻¹ * ((((β₂ : G) * v * (β₂ : G)⁻¹) *
          ((β₁ : G) * v * (β₁ : G)⁻¹)⁻¹) * ((β₁ : G) * v * (β₁ : G)⁻¹)) := by
      group
    rw [e, hc, ← mul_assoc, inv_mul_cancel, one_mul]
    exact h3
  have hfpf : ∀ w ∈ P,
      rhoDot hF.toHypF91 (QuotientGroup.mk' (CFSG.pCore 2 ↥(A6.g1 T V)) β₁) w = w → w = 1 := by
    rintro _ ⟨v, hv, rfl⟩ hfix
    rw [clsU_eq_one_iff]
    have h1 := (rhoH_clsU_eq_iff hF.toHypF91 β₁ (le_conjClosure V _ hv)).mp hfix
    obtain ⟨-, -, hxv⟩ := L32NSet14.mem_trivSub.mp hyβ
    have h2 := hxv v hv
    have hy2H : y ^ 2 ∈ A6.g1 T V := pow_mem hyH 2
    set c := ((y ^ 2)⁻¹ * β₁) * v * ((y ^ 2)⁻¹ * β₁)⁻¹ * v⁻¹ with hc
    have hcy : c * y ^ 2 = y ^ 2 * c := hcentral c h2 _ hy2H
    have h3 : y ^ 2 * v * (y ^ 2)⁻¹ * v⁻¹ = c⁻¹ * ((β₁ : G) * v * (β₁ : G)⁻¹ * v⁻¹) := by
      calc y ^ 2 * v * (y ^ 2)⁻¹ * v⁻¹
          = c⁻¹ * (y ^ 2 * c * (y ^ 2)⁻¹) * (y ^ 2 * v * (y ^ 2)⁻¹ * v⁻¹) := by
            rw [← hcy]
            group
        _ = c⁻¹ * ((β₁ : G) * v * (β₁ : G)⁻¹ * v⁻¹) := by
            rw [hc]
            group
    have h4 : y ^ 2 * v * (y ^ 2)⁻¹ * v⁻¹ ∈ fsuV1 T V := by
      rw [h3]
      exact mul_mem (inv_mem h2) h1
    have hy2 : y ^ 2 = y⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ]
      exact hy3
    have h6 := (Subgroup.mem_normalizer_iff.mp (hF.toHypF91.H_normalizes_V₁ hyH) _).mp h4
    have e : y * v * y⁻¹ * v⁻¹ = (y * (y ^ 2 * v * (y ^ 2)⁻¹ * v⁻¹) * y⁻¹)⁻¹ := by
      rw [hy2]
      group
    exact hfpfy v hv (by rw [e]; exact inv_mem h6)
  obtain ⟨e₁⟩ := R.hA5
  obtain ⟨e₂⟩ := C.nonempty_equiv
  have hnorm : ∀ c : ↥(A6.g1 T V) ⧸ CFSG.pCore 2 ↥(A6.g1 T V),
      ((∀ a ∈ modO2Image (A6.g1 T V) K, c * a * c⁻¹ ∈ modO2Image (A6.g1 T V) K) ∧
        ∀ b ∈ modO2Image (A6.g1 T V) (K.map (MulAut.conj t₀ : G →* G)),
          c * b * c⁻¹ ∈ modO2Image (A6.g1 T V) (K.map (MulAut.conj t₀ : G →* G))) ∨
      ∀ a ∈ modO2Image (A6.g1 T V) K,
        c * a * c⁻¹ ∈ modO2Image (A6.g1 T V) (K.map (MulAut.conj t₀ : G →* G)) := by
    intro c
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(A6.g1 T V)) c
    have hconj : ∀ (A : Subgroup G) (κ : ↥(A6.g1 T V)),
        (h : G) * κ * (h : G)⁻¹ ∈ A →
        QuotientGroup.mk' (CFSG.pCore 2 ↥(A6.g1 T V)) h *
            QuotientGroup.mk' (CFSG.pCore 2 ↥(A6.g1 T V)) κ *
            (QuotientGroup.mk' (CFSG.pCore 2 ↥(A6.g1 T V)) h)⁻¹ ∈ modO2Image (A6.g1 T V) A :=
      fun A κ hm => mem_modO2Image'.mpr ⟨h * κ * h⁻¹, hm, by rw [map_mul, map_mul, map_inv]⟩
    rcases C.two h h.2 with hN | hN
    · left
      refine ⟨fun a ha => ?_, fun b hb => ?_⟩
      · obtain ⟨κ, hκ, rfl⟩ := mem_modO2Image'.mp ha
        exact hconj _ κ ((Subgroup.mem_normalizer_iff.mp hN _).mp hκ)
      · obtain ⟨κ, hκ, rfl⟩ := mem_modO2Image'.mp hb
        exact hconj _ κ ((Subgroup.mem_normalizer_iff.mp (C.mem_normalizer_kt h.2 hN) _).mp hκ)
    · right
      intro a ha
      obtain ⟨κ, hκ, rfl⟩ := mem_modO2Image'.mp ha
      refine hconj _ κ ⟨(t₀⁻¹ * h) * κ * (t₀⁻¹ * h)⁻¹,
        (Subgroup.mem_normalizer_iff.mp hN _).mp hκ, ?_⟩
      simp only [MonoidHom.coe_ofClass, MulAut.conj_apply]
      group
  exact not_isTransvection hV (rhoDot hF.toHypF91) (rhoDot_injective _) (e₂.symm.trans e₁)
    (C.equivKt.symm.trans (e₂.symm.trans e₁)) (fun a ha b hb => C.commute_kb hA37 ha hb)
    (fun z h1 h2 => C.eq_one_of_mem_kb_kt hA37 h1 h2)
    (fun c _ h1 h2 => eq_one_of_centralizes hA37 hA38 h76 h33 h36 hlist R C h1 h2) hnorm
    hk₁K hk₂K hk₁3 hk₂3 hP hsame hfpf τ

theorem dγ_lt_uγ_of_red (hA37 : A37ForSQTK) (hA38 : A38ForSQTK)
    (h29 : Thm14_7_29) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h76 : Lemma14_7_6) (h33 : Lemma14_7_33) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd)
    (R : L2Red G T L V K)
    (hF : HypF98 T V L (fsuV1 T V) V (A6.g1 T V)) :
    ∀ (γ γ' : F8.Geom T L (A6.g1 T V)) (g : ↥((L ⊔ T) ⊔ A6.g1 T V)),
      F8Setup T V L (A6.g1 T V) γ γ' g →
        F8.Dγ V (fsuV1 T V) (A6.g1 T V) (g : G) < F8.Uγ V (A6.g1 T V) (g : G) := by
  intro γ γ' g s
  refine lt_of_le_of_ne (centralizerMod_le_left _ _ _) fun hD => ?_
  obtain ⟨y, hy⟩ := exists_transvection_of_eq hF s hD.symm
  exact not_isTransvection_red hA37 hA38 h29 h1222 h1332 h1334 h76 h33 h36 hlist R hF
    (QuotientGroup.mk y) hy

end CFSG.Quasithin.H13.L32A.L2
