module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIStep11C
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIStep4
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIDefs
public import CFSG.Quasithin.Vol2.GoldschmidtL128Wire
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIY0
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4RepStmt

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Quasithin.H13

open scoped IsMulCommutative

section Aux

variable {G : Type} [Group G] [Finite G]

theorem T_le_p128 (T L V : Subgroup G) : T ≤ p128 T L V := by
  refine le_inf le_sup_right ?_
  refine le_iInf fun Y => le_iInf fun hY => ?_
  obtain ⟨i, -, hi⟩ := hY
  exact hi.2.2

theorem T_le_normalizer_i128 (T L V V₁ : Subgroup G) :
    T ≤ Subgroup.normalizer (i128 T L V V₁ : Set G) := fun t ht =>
  le_normalizer_conjClosure (u128 V V₁) (p128 T L V) (T_le_p128 T L V ht)

theorem T_normalizes_DI {T L V V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V 4 V₁ V₂)
    {I : Subgroup G} (hTI : T ≤ Subgroup.normalizer (I : Set G)) :
    T ≤ Subgroup.normalizer ((I ⊓ wcSub T L V V₁ : Subgroup G) : Set G) := by
  have hfwd : ∀ y : G, y ∈ Subgroup.normalizer (I : Set G) →
      y ∈ Subgroup.normalizer (i128 T L V V₁ : Set G) → y ∈ Subgroup.normalizer (V₁ : Set G) →
      ∀ x ∈ I ⊓ wcSub T L V V₁, y * x * y⁻¹ ∈ I ⊓ wcSub T L V V₁ := by
    intro y h1 h2 h3 x hx
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 h1 x).1 (Subgroup.mem_inf.1 hx).1,
      wc_normalized (V₂ := V₂) h2 h3 x (Subgroup.mem_inf.1 hx).2⟩
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hfwd t (hTI ht) (T_le_normalizer_i128 T L V V₁ ht) (T_le_normalizer_V₁ hs ht) x
  · intro hx
    have h := hfwd t⁻¹ (Subgroup.inv_mem _ (hTI ht))
      (Subgroup.inv_mem _ (T_le_normalizer_i128 T L V V₁ ht))
      (Subgroup.inv_mem _ (T_le_normalizer_V₁ hs ht)) _ hx
    have e : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := by group
    rw [e] at h
    exact h

end Aux

theorem case1294FiveDI_ofW_five (F0 : FactF0) (F1 : FactF1) (F2 : FactF2) (F3 : FactF3)
    (F4 : FactF4) (F5 : FactF5) :
    Stmt12_2_2 → Stmt12_2_13 → Lemma12_8_10 → Lemma12_8_13 → Lemma12_8_13_five →
      Case1294FiveID → Case1294FiveDI := by
  intro h1222 h12213 h12810 h12813 h12813f hID
  have h1289 : Lemma12_8_9W := lemma12_8_9W_holds h1222 h12213
  intro G _ _ T L V hcx V₁ V₂ K₁ hs hLK hK hK4 D h5 himg
  have h12812 : Lemma12_8_12_two := lemma12_8_12_two_of h1222 h12213
  have hO2 : oTwoUpper (p128 T L V) ≤ p128 T L V := by
    unfold oTwoUpper
    exact (Subgroup.closure_le _).2 fun x hx => hx.1
  obtain ⟨g, hgmem, hgN⟩ := L128P.exists_not_mem_normalizer h1222 hs
  have hgP : g ∈ p128 T L V := hO2 hgmem
  have hK₁H : K₁ ≤ Subgroup.normalizer (V₁ : Set G) := K₁_le_normalizer hK
  have hK₁U : K₁ ≤ Subgroup.normalizer (u128 V V₁ : Set G) := K₁_le_normalizer_u128 hK
  have hnormH : ∀ h ∈ Subgroup.normalizer (V₁ : Set G), ∀ k ∈ K₁, h * k * h⁻¹ ∈ K₁ := by
    intro h hh k hk
    exact (Subgroup.mem_normalizer_iff.1
      ((h12813f G T L V V₁ V₂ K₁ hs hLK hK hK4 g hgP hgN D h5 himg).1 hh) k).1 hk
  obtain ⟨hdim, q, hq, -, hS, hΓO, hidx⟩ := id h5
  have hF4 := F4 D.V q D.B hdim hq (L128A.HatU.B_nondegenerate D) hS
  obtain ⟨rel2, hKΓ, hcardΩ, hker⟩ := step2_q hK hK4 D hF4.1 hF4.2.1 hΓO hidx himg
  have hΩF4 : F4Out q D.B (D.img K₁) := hF4.2.2 (D.img K₁) hKΓ rel2
  obtain ⟨hTΩ, S, hS3, hSq, hSV, hSπ, hTS⟩ :=
    step3_main h1222 h12213 F5 hcx hs D hq hΓO hΩF4
  obtain ⟨I, hIZ, hKI, hTI, hel, hI16, hkerI⟩ :=
    hID G T L V hcx V₁ V₂ K₁ hs hLK hK hK4 D h5 himg
  haveI hcomm : IsMulCommutative ↥I := hel.1
  letI hmod : Module (ZMod 2) (Additive ↥I) := zmodModuleOf hel.2
  have hcardI2 : Nat.card (Additive ↥I) = 2 ^ 4 := by
    show Nat.card ↥I = 2 ^ 4
    norm_num [hI16]
  have hM : Module.finrank (ZMod 2) (Additive ↥I) = 4 := finrank_of_natCard hcardI2
  have hcardGL : Nat.card (Additive ↥I ≃ₗ[ZMod 2] Additive ↥I) = 20160 := card_GL_four hM
  obtain ⟨κ, hκ⟩ := exists_kappa D hK₁U hKI hker hkerI
  have hκbij : Function.Bijective κ := kappa_bijective D hK₁U hKI hker hkerI hκ hcardΩ hcardGL
  obtain ⟨kap, hkap⟩ : ∃ kap : ↥(D.img K₁) ≃* (Additive ↥I ≃ₗ[ZMod 2] Additive ↥I),
      ∀ x, kap x = κ x := ⟨MulEquiv.ofBijective κ hκbij, fun _ => rfl⟩
  have hact : ∀ x : G, ∀ (hxU : x ∈ Subgroup.normalizer (u128 V V₁ : Set G))
      (hxI : x ∈ Subgroup.normalizer (I : Set G)) (hxH : x ∈ Subgroup.normalizer (V₁ : Set G))
      (hxΩ : D.ρ ⟨x, hxU⟩ ∈ D.img K₁),
      linAct (V := I) ⟨x, hxI⟩ = kap ⟨D.ρ ⟨x, hxU⟩, hxΩ⟩ := by
    intro x hxU hxI hxH hxΩ
    rw [hkap]
    exact linAct_eq_kappa F0 hI16 D hK₁U hK₁H hKI hker hkerI hnormH hκ hκbij x hxU hxI hxH hxΩ
  have hlt : V₁ < zU128 V V₁ := by
    refine lt_of_le_of_ne (V₁_le_zU h1222 h12213 hs) fun h => ?_
    have h1 : I ≤ V₁ := fun x hx => by
      have hx' := hIZ hx
      rw [← h] at hx'
      exact hx'
    have h2 := Subgroup.card_le_of_le h1
    rw [hI16, card_V₁ hs] at h2
    norm_num at h2
  have hEnv : ∀ a : G, a ∈ V₂ → a ∉ V₁ →
      ∃ E : DIEnv T L V V₁ V₂ K₁ g D, E.I = I ∧ E.a = a := by
    intro a haV₂ haV₁
    obtain ⟨p, ℓ, Pl, hp, hℓ, hPl, hpℓ, hℓPl, -, hY₁, hY₂⟩ :=
      step5_main F1 h1222 h12213 hcx hs hK₁H hM D hΩF4 himg hTΩ S hS3 hSq hSV hTS haV₂ haV₁ kap
    obtain ⟨y₀, hy₀, hy₀3⟩ := exists_y0 h1222 hcx hs
    obtain ⟨hD0, hDg4⟩ := step6_main h1222 h12213 h1289 h12810 h12812 h12813 F2 F3 hcx hs hLK
      hK₁H hK₁U hgP hgN hlt D hΩF4 S hS3 hSq hSV hSπ hTS hTΩ haV₂ haV₁ hker hM kap p ℓ Pl hp hℓ
      hPl hpℓ hℓPl hY₁ hY₂ hy₀ hy₀3
    let E : DIEnv T L V V₁ V₂ K₁ g D :=
      { hcx := hcx
        hs := hs
        hLK := hLK
        hgP := hgP
        hgN := hgN
        hK₁H := hK₁H
        hK₁U := hK₁U
        hker := hker
        himg := himg
        hTΩ := hTΩ
        I := I
        hIZ := hIZ
        hTI := hTI
        hKI := hKI
        hI16 := hI16
        kap := kap
        hact := hact
        S := S
        hS3 := hS3
        hSV := hSV
        hSπ := hSπ
        fp := p
        fl := ℓ
        fPl := Pl
        hM := hM
        hp := hp
        hℓ := hℓ
        hPl := hPl
        hpℓ := hpℓ
        hℓPl := hℓPl
        a := a
        haV₂ := haV₂
        haV₁ := haV₁
        hY₁ := hY₁
        hY₂ := hY₂
        hD0 := hD0
        hDg4 := hDg4
        y₀ := y₀
        hy₀ := hy₀
        hy₀3 := hy₀3 }
    exact ⟨E, rfl, rfl⟩
  have hptOf : ∀ E : DIEnv T L V V₁ V₂ K₁ g D,
      kmapOf (D.img K₁) E.kap (stabS E.S) = stabS E.fp := fun E =>
    E.hY₂.resolve_right fun hpl =>
      (DIEnv.plane_false E h1222 h12213 h1289 h12810 h12813 F2 F3 hpl).elim
  obtain ⟨a₀, ha₀V₂, ha₀V₁⟩ := exists_a_mem hs
  obtain ⟨E₀, hEI₀, -⟩ := hEnv a₀ ha₀V₂ ha₀V₁
  have hcard : Nat.card ↥(I ⊓ wcSub T L V V₁) = 4 := by
    have h := DIEnv.card_DI E₀ h1222 h12213 h1289 h12810 h12813 F2 F3 (hptOf E₀)
    rw [hEI₀] at h
    exact h
  have hinf : I ⊓ wcSub T L V V₁ ⊓ V₁ = ⊥ := by
    have h := DIEnv.DI_inf_V1 E₀
    rw [hEI₀] at h
    exact h
  have hTDI := T_normalizes_DI hs hTI
  refine ⟨I ⊓ wcSub T L V V₁, fun x hx => hIZ (Subgroup.mem_inf.1 hx).1,
    fun x hx => (Subgroup.mem_inf.1 hx).2, hcard, hinf,
    fun d hd => hel.2 d (Subgroup.mem_inf.1 hd).1, hTDI, ?_⟩
  intro a ha haV₁ h hK₁h hord hρ
  obtain ⟨k, hk⟩ := hord
  obtain ⟨E, hEI, hEa⟩ := hEnv a ha haV₁
  have hh : (h : G) ∈ k0Sub K₁ D (D.π E.a) :=
    mem_k0Sub.2 ⟨hK₁h, h.2, by rw [hEa]; exact hρ⟩
  obtain ⟨h1, h2⟩ := DIEnv.leaf_norm E h1222 h12213 h1289 h12810 h12813 h12813f F2 F3 (hptOf E)
    hK hK4 h5 hnormH hh k hk
  rw [hEI] at h1 h2
  exact ⟨h1, h2⟩

end CFSG.Quasithin.H13.C1294
