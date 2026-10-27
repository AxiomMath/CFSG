module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qk

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def R613AutAt (D : Data G) (p : ℕ) (P P₀ : Subgroup G) : Prop :=
  ((∀ m ∈ D.M, (∀ x ∈ P ⊓ inftyOf (centralizer (P₀ : Set G)),
      m * x * m⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M) →
    m ∈ centralizer (inftyOf (centralizer (P₀ : Set G)) : Set G) ⊔
      (P ⊓ inftyOf (centralizer (P₀ : Set G))) ⊔ CFSG.Open.pCoreOf 2 D.M) ∧
    D.M ≤ normalizer ((P ⊓ inftyOf (centralizer (P₀ : Set G)) ⊔
      CFSG.Open.pCoreOf 2 D.M : Subgroup G) : Set G) ∧
    ∀ t ∈ D.T, (∀ x ∈ P ⊓ inftyOf (centralizer (P₀ : Set G)),
      t * x * t⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M) → t ∈ CFSG.Open.pCoreOf 2 D.M)

theorem r613Aut_iff (D : Data G) :
    R613Aut D ↔ ∀ (p : ℕ) (P P₀ : Subgroup G), Hyp612 D p P P₀ → R613AutAt D p P P₀ := Iff.rfl

end CFSG.LocalAnalysis.UniquenessCase.UC6

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem uc22p22ql_false_of_T_top (D : Data G) {p : ℕ} (hpP : p.Prime) (hp2 : p ≠ 2) {V₀ V P₁ Dd : Subgroup G}
    (hH : F11.Hyp11 D V₀ V) (hDM : Dd ≤ D.M)
    (hfpf : ∀ d ∈ Dd, d ≠ 1 → ∀ r ∈ pCoreOf 2 D.M, d * r * d⁻¹ = r → r = 1) (hP₁M : P₁ ≤ D.M)
    (hel : IsElemAbelian p P₁) (hcard : p ^ 2 ≤ Nat.card P₁) (hDP : ∀ d ∈ Dd, ∀ a ∈ P₁, d * a = a * d)
    (hP₁C : P₁ ⊓ F11.CTilde D.M V₀ V = ⊥) (hDC : Dd ⊓ F11.CTilde D.M V₀ V = ⊥)
    (hT : P₁ ≤ Dd ⊔ F11.CTilde D.M V₀ V) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hV, hV₀V, hMV₀, -⟩ := uc22p22q_hyp11_unpack D hH
  have hMV : D.M ≤ normalizer (V : Set G) := hV.2.2.1
  have hVR : V ≤ pCoreOf 2 D.M :=
    uc22p22qh_le_pCoreOf hV.2.1 (uc22p22e_isPGroup_of_elem hV.2.2.2)
      (fun k hk x hx => (mem_normalizer_iff.1 (hMV hk) x).1 hx)
  set C : Subgroup G := F11.CTilde D.M V₀ V with hCdef
  have hCn : ∀ m ∈ D.M, ∀ c ∈ C, m * c * m⁻¹ ∈ C := fun m hm c hc =>
    uc22p22q_ctilde_conj_mem hMV hMV₀ hm hc
  have hDN : Dd ≤ normalizer (C : Set G) := fun d hd =>
    uc22p22qk_mem_normalizer fun c hc => hCn d (hDM hd) c hc
  have hPN : P₁ ≤ normalizer (C : Set G) := fun a ha =>
    uc22p22qk_mem_normalizer fun c hc => hCn a (hP₁M ha) c hc
  set E : Subgroup G := Dd ⊓ (P₁ ⊔ C) with hE
  have hmemE : ∀ e ∈ E, e ∈ Dd ∧ ∃ a ∈ P₁, a * e ∈ C := fun e he =>
    ⟨he.1, (uc22p22qk_mem_sup_iff hPN).1 he.2⟩
  have hsurj : ∀ a ∈ P₁, ∃ e ∈ E, ∃ c' ∈ C, a = e * c' := by
    intro a ha
    obtain ⟨d, hd, hdc⟩ := (uc22p22qk_mem_sup_iff hDN).1 (hT ha)
    refine ⟨d⁻¹, ⟨Dd.inv_mem hd, ?_⟩, d * a, hdc, by group⟩
    have e1 : d⁻¹ = a * (d * a)⁻¹ := by group
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right (C.inv_mem hdc))
  have hEexp : ∀ e ∈ E, e ^ p = 1 := by
    intro e he
    obtain ⟨heD, a, haP, haeC⟩ := hmemE e he
    have hcomm : Commute a e := (hDP e heD a haP).symm
    have h1 : e ^ p ∈ C := by
      have := C.pow_mem haeC p
      rwa [hcomm.mul_pow, hel.2 a haP, one_mul] at this
    have h2 : e ^ p ∈ Dd ⊓ C := ⟨Dd.pow_mem heD p, h1⟩
    rw [hDC] at h2
    exact Subgroup.mem_bot.1 h2
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    obtain ⟨hxD, a₁, ha₁, ha₁x⟩ := hmemE x hx
    obtain ⟨hyD, a₂, ha₂, ha₂y⟩ := hmemE y hy
    have hxa₂ : a₂ * x = x * a₂ := (hDP x hxD a₂ ha₂).symm
    have hya₁ : a₁ * y = y * a₁ := (hDP y hyD a₁ ha₁).symm
    have hcc : a₁ * a₂ = a₂ * a₁ := hel.comm ha₁ ha₂
    have z1 : (a₁ * x) * (a₂ * y) = (a₁ * a₂) * (x * y) := by
      calc (a₁ * x) * (a₂ * y) = a₁ * (x * a₂) * y := by group
        _ = a₁ * (a₂ * x) * y := by rw [hxa₂]
        _ = (a₁ * a₂) * (x * y) := by group
    have z2 : (a₂ * y) * (a₁ * x) = (a₁ * a₂) * (y * x) := by
      calc (a₂ * y) * (a₁ * x) = a₂ * (y * a₁) * x := by group
        _ = a₂ * (a₁ * y) * x := by rw [hya₁]
        _ = (a₂ * a₁) * (y * x) := by group
        _ = (a₁ * a₂) * (y * x) := by rw [hcc]
    have hC1 : (a₁ * a₂) * (x * y) ∈ C := by rw [← z1]; exact C.mul_mem ha₁x ha₂y
    have hC2 : (a₁ * a₂) * (y * x) ∈ C := by rw [← z2]; exact C.mul_mem ha₂y ha₁x
    have hq : (x * y)⁻¹ * (y * x) ∈ C := by
      have := C.mul_mem (C.inv_mem hC1) hC2
      have e : ((a₁ * a₂) * (x * y))⁻¹ * ((a₁ * a₂) * (y * x)) = (x * y)⁻¹ * (y * x) := by group
      rwa [e] at this
    have hqD : (x * y)⁻¹ * (y * x) ∈ Dd :=
      Dd.mul_mem (Dd.inv_mem (Dd.mul_mem hxD hyD)) (Dd.mul_mem hyD hxD)
    have h3 : (x * y)⁻¹ * (y * x) ∈ Dd ⊓ C := ⟨hqD, hq⟩
    rw [hDC] at h3
    exact inv_mul_eq_one.1 (Subgroup.mem_bot.1 h3)
  have hEV : ∀ e ∈ E, ∀ w ∈ V, e * w * e⁻¹ ∈ V := fun e he w hw =>
    (mem_normalizer_iff.1 (hMV (hDM he.1)) w).1 hw
  have hcyc : IsCyclic ↥E := uc22p22q_isCyclic_of_fpf hpP hp2
    (fun a ha b hb => hV.2.2.2.comm ha hb) hV.2.2.2.2 hV.1 hEcomm hEexp hEV
    (fun e he he1 w hw hew => hfpf e he.1 he1 w (hVR hw) hew)
  have hElem : IsElemAbelian p E := ⟨⟨⟨fun a b => Subtype.ext (hEcomm a a.2 b b.2)⟩⟩, hEexp⟩
  choose! f hf using hsurj
  let g : ↥P₁ → ↥E := fun a => ⟨f a, (hf a a.2).1⟩
  have hginj : Function.Injective g := by
    intro a b hab
    have hfab : f a = f b := congrArg Subtype.val hab
    obtain ⟨-, c₁, hc₁, ha⟩ := hf a a.2
    obtain ⟨-, c₂, hc₂, hb⟩ := hf b b.2
    have key : (a : G)⁻¹ * b = c₁⁻¹ * c₂ := by
      calc (a : G)⁻¹ * b = (f a * c₁)⁻¹ * (f b * c₂) := by rw [← ha, ← hb]
        _ = c₁⁻¹ * c₂ := by rw [hfab]; group
    have hmem : (a : G)⁻¹ * b ∈ P₁ ⊓ C :=
      ⟨P₁.mul_mem (P₁.inv_mem a.2) b.2, by rw [key]; exact C.mul_mem (C.inv_mem hc₁) hc₂⟩
    rw [hP₁C] at hmem
    exact Subtype.ext (inv_mul_eq_one.1 (Subgroup.mem_bot.1 hmem))
  have hle : Nat.card P₁ ≤ Nat.card E := Nat.card_le_card_of_injective g hginj
  exact uc22p22n_not_isCyclic_of_card hpP hElem (hcard.trans hle) hcyc

theorem uc22p22ql_decomp {Dd P₁ R : Subgroup G} (hDR : Dd ≤ normalizer (R : Set G))
    (hPR : P₁ ≤ normalizer (R : Set G)) (hDPn : Dd ≤ normalizer (P₁ : Set G))
    (hDP : ∀ d ∈ Dd, ∀ a ∈ P₁, d * a = a * d) {c : G} (hc : c ∈ Dd ⊔ P₁ ⊔ R) :
    ∃ d ∈ Dd, ∃ a ∈ P₁, ∃ r ∈ R, c = d * a * r := by
  obtain ⟨y, hy, hyc⟩ := (uc22p22qk_mem_sup_iff (sup_le hDR hPR)).1 hc
  obtain ⟨d, hd, hdy⟩ := (uc22p22qk_mem_sup_iff hDPn).1 hy
  have hcomm : d * (d * y)⁻¹ = (d * y)⁻¹ * d := hDP d hd _ (P₁.inv_mem hdy)
  refine ⟨d, hd, (d * y)⁻¹, P₁.inv_mem hdy, y * c, hyc, ?_⟩
  calc c = (d * y)⁻¹ * d * (y * c) := by group
    _ = d * (d * y)⁻¹ * (y * c) := by rw [hcomm]

theorem uc22p22ql_ctilde_le (D : Data G) (h61 : UC6.R6_1 D) {p : ℕ} (hpσ : p ∈ D.sig) (hp5 : 5 ≤ p)
    {V₀ V P₁ Dd : Subgroup G} (hH : F11.Hyp11 D V₀ V) (hP₁M : P₁ ≤ D.M) (hel : IsElemAbelian p P₁)
    (hcard : p ^ 2 ≤ Nat.card P₁) (hirr : IrrOn (D.M ⊓ normalizer (P₁ : Set G)) P₁) (hDM : Dd ≤ D.M)
    (hfpf : ∀ d ∈ Dd, d ≠ 1 → ∀ r ∈ pCoreOf 2 D.M, d * r * d⁻¹ = r → r = 1)
    (hDP : ∀ d ∈ Dd, ∀ a ∈ P₁, d * a = a * d)
    (hnorm : ∀ n ∈ D.M ⊓ normalizer (P₁ : Set G), ∃ k ∈ D.M ⊓ centralizer (P₁ : Set G),
      k⁻¹ * n ∈ normalizer (Dd : Set G))
    (h4a : ∀ m ∈ D.M, (∀ x ∈ P₁, m * x * m⁻¹ * x⁻¹ ∈ pCoreOf 2 D.M) → m ∈ Dd ⊔ P₁ ⊔ pCoreOf 2 D.M)
    (h4b : D.M ≤ normalizer ((P₁ ⊔ pCoreOf 2 D.M : Subgroup G) : Set G)) :
    F11.CTilde D.M V₀ V ≤ pCoreOf 2 D.M := by
  have hpP : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  have hnc : ¬ IsCyclic P₁ := uc22p22n_not_isCyclic_of_card hpP hel hcard
  have h0 := uc22p22qk_P1_centralizes_V0 D h61 hpσ hp5 hP₁M hel hnc hirr hH
  have hPC := uc22p22qk_P1_inf_ctilde D h61 hpσ hP₁M hel hnc hirr hH h0
  have hDC := uc22p22qk_D_inf_ctilde D hH hDM hfpf
  obtain ⟨hV, hV₀V, hMV₀, -⟩ := uc22p22q_hyp11_unpack D hH
  have hMV : D.M ≤ normalizer (V : Set G) := hV.2.2.1
  have hRC := uc22p22qh_pCore_le_ctilde D hH
  set C : Subgroup G := F11.CTilde D.M V₀ V with hCdef
  have hCn : ∀ m ∈ D.M, ∀ c ∈ C, m * c * m⁻¹ ∈ C := fun m hm c hc =>
    uc22p22q_ctilde_conj_mem hMV hMV₀ hm hc
  have hMN : D.M ≤ normalizer (pCoreOf 2 D.M : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 D.M
  have hDN : Dd ≤ normalizer (C : Set G) := fun d hd =>
    uc22p22qk_mem_normalizer fun c hc => hCn d (hDM hd) c hc
  have hDPn : Dd ≤ normalizer (P₁ : Set G) := fun d hd =>
    uc22p22qk_mem_normalizer fun a ha => by
      have : d * a * d⁻¹ = a := by rw [hDP d hd a ha]; group
      rw [this]
      exact ha
  intro c hc
  have hcomm : ∀ x ∈ P₁, c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 D.M := fun x hx =>
    uc22p22qk_comm_mem_pCore D hH hP₁M hPC h4b hc hx
  obtain ⟨d, hdD, a, haP, r, hrR, rfl⟩ := uc22p22ql_decomp (fun d hd => hMN (hDM hd))
    (fun a ha => hMN (hP₁M ha)) hDPn hDP (h4a c (uc22p22q_mem_ctilde.1 hc).1 hcomm)
  have hdaC : d * a ∈ C := by
    have e : d * a = (d * a * r) * r⁻¹ := by group
    rw [e]
    exact C.mul_mem hc (C.inv_mem (hRC hrR))
  have haT : a ∈ P₁ ⊓ (Dd ⊔ C) := ⟨haP, (uc22p22qk_mem_sup_iff hDN).2 ⟨d, hdD, hdaC⟩⟩
  have hTnorm : D.M ⊓ normalizer (P₁ : Set G) ≤
      normalizer ((P₁ ⊓ (Dd ⊔ C) : Subgroup G) : Set G) := by
    rintro n ⟨hnM, hnP⟩
    obtain ⟨k, hk, hkn⟩ := hnorm n ⟨hnM, hnP⟩
    have hkP : k ∈ normalizer (P₁ : Set G) := Subgroup.centralizer_le_normalizer _ hk.2
    have hn₀P : k⁻¹ * n ∈ normalizer (P₁ : Set G) :=
      (normalizer (P₁ : Set G)).mul_mem ((normalizer (P₁ : Set G)).inv_mem hkP) hnP
    have hn₀C : k⁻¹ * n ∈ normalizer (C : Set G) :=
      uc22p22qk_mem_normalizer fun c hc => hCn _ (D.M.mul_mem (D.M.inv_mem hk.1) hnM) c hc
    have hn₀ : k⁻¹ * n ∈ normalizer ((P₁ ⊓ (Dd ⊔ C) : Subgroup G) : Set G) :=
      inf_normalizer_le_normalizer_inf ⟨hn₀P, inf_normalizer_le_normalizer_sup Dd C ⟨hkn, hn₀C⟩⟩
    have hk' : k ∈ normalizer ((P₁ ⊓ (Dd ⊔ C) : Subgroup G) : Set G) :=
      uc22p22qk_mem_normalizer fun w hw => by
        have h1 := Subgroup.mem_centralizer_iff.1 hk.2 w hw.1
        have e : k * w * k⁻¹ = w := by rw [mul_inv_eq_iff_eq_mul]; exact h1.symm
        rw [e]
        exact hw
    have e : n = k * (k⁻¹ * n) := by group
    rw [e]
    exact (normalizer ((P₁ ⊓ (Dd ⊔ C) : Subgroup G) : Set G)).mul_mem hk' hn₀
  rcases hirr _ inf_le_left hTnorm with hT | hT
  · have ha1 : a = 1 := by
      rw [hT] at haT
      exact Subgroup.mem_bot.1 haT
    subst ha1
    have hd : d ∈ Dd ⊓ C := ⟨hdD, by simpa using hdaC⟩
    rw [hDC] at hd
    have hd1 : d = 1 := Subgroup.mem_bot.1 hd
    subst hd1
    simpa using hrR
  · exfalso
    refine uc22p22ql_false_of_T_top D hpP hp2 hH hDM hfpf hP₁M hel hcard hDP hPC hDC fun a' ha' => ?_
    have : a' ∈ P₁ ⊓ (Dd ⊔ C) := by rw [hT]; exact ha'
    exact this.2

theorem uc22p22q_r112_pair (D : Data G) (hstd : Sigma23Std D) (h61 : UC6.R6_1 D) {p : ℕ} {P P₀ : Subgroup G}
    (hH : UC6.Hyp612 D p P P₀) (hd : UC6.R613DefAt D p P P₀) (h4 : UC6.R613AutAt D p P P₀)
    {V₀ V : Subgroup G} (hH11 : F11.Hyp11 D V₀ V) : F11.CTilde D.M V₀ V = pCoreOf 2 D.M := by
  obtain ⟨⟨hp3, -, hwc, hΓ, hL, hfrob⟩, hcent⟩ := hd
  obtain ⟨h4a, h4b, -⟩ := h4
  have hpσ : p ∈ D.sig := by
    rw [D.sig_sub]
    exact Or.inl (Or.inr hH.mem_sig2)
  have hpP : p.Prime := (D.sig_prime p hpσ).1
  haveI : Fact p.Prime := ⟨hpP⟩
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  have hp5 : 5 ≤ p := by
    rcases (by omega : p = 4 ∨ 5 ≤ p) with rfl | h
    · exact absurd hpP (by decide)
    · exact h
  obtain ⟨n, hn, hel, hcard⟩ := uc22p22q_P1_elem D hstd hH hwc hL hp2
  have hirr := uc22p22q_irr_P1 D hstd hH hwc hL hp2 hΓ
  obtain ⟨hDM, hfpf⟩ := uc22p22qk_frob_unpack D hfrob
  refine le_antisymm (uc22p22ql_ctilde_le D h61 hpσ hp5 hH11 (inf_le_left.trans hH.sylow.le) hel
    (by rw [hcard]; exact Nat.pow_le_pow_right hpP.pos hn) hirr hDM hfpf
    (fun d hd a ha => (Subgroup.mem_centralizer_iff.1 hd a ha.2).symm) ?_ h4a h4b)
    (uc22p22qh_pCore_le_ctilde D hH11)
  intro m hm
  obtain ⟨k, hk, hkn⟩ := uc22p22qh_normalizer_decomp hH.sylow hcent hH.le (uc22p22q_weak_elem hwc) hm.1 hm.2
  refine ⟨k, hk, ?_⟩
  have hC := uc22p22q_mem_normalizer_centralizer hkn
  exact uc22p22q_mem_normalizer_centralizer
    (uc22p22qk_mem_normalizer fun x hx => uc22p22q_inftyOf_conj hC hx)

theorem uc22p22q_r112_of (D : Data G) (hstd : Sigma23Std D) (h61 : UC6.R6_1 D) (hsp : Sigma2Print D)
    (hid : UC6.R613Ident D) (hcent : UC6.R613Cent D) (h4 : UC6.R613Aut D) : F11.R112 D := by
  rintro V₀ V hH11 ⟨p, hp⟩
  obtain ⟨P, P₀, hH, hc2⟩ := hsp p hp
  exact uc22p22q_r112_pair D hstd h61 hH
    (uc22p22q_r613defAt_of D hstd h61 hH hc2 (hid p P P₀ hH) (hcent p P P₀ hH)) (h4 p P P₀ hH) hH11

end CFSG.LocalAnalysis.UniquenessCase.UC22
