module

public import CFSG.Quasithin.MS93.S4AFMod

public section

namespace CFSG.Quasithin.MS93.S4A.F

open CFSG.Quasithin CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S46
open scoped Matrix

section Lift

variable {H : Type*} [Group H] {F : Type} [Field F] {Y : Type} [CommGroup Y]

@[expose] noncomputable def liftRho (ψ : H →* SL3 F) (hψ : Function.Surjective ψ)
    (σ : H →* MulAut Y) (hker : ψ.ker ≤ σ.ker) : SL3 F →* MulAut Y :=
  (QuotientGroup.lift ψ.ker σ hker).comp
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.toMonoidHom

variable {ψ : H →* SL3 F} (hψ : Function.Surjective ψ) {σ : H →* MulAut Y}
  (hker : ψ.ker ≤ σ.ker)

theorem liftRho_apply (h : H) : liftRho ψ hψ σ hker (ψ h) = σ h := by
  have e : (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm (ψ h) = (h : H ⧸ ψ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [liftRho, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e, QuotientGroup.lift_mk]

theorem map_liftRho (A : Subgroup H) : (A.map ψ).map (liftRho ψ hψ σ hker) = A.map σ := by
  ext y
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, (liftRho_apply hψ hker a).symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ψ a, ⟨a, ha, rfl⟩, liftRho_apply hψ hker a⟩

theorem range_liftRho : (liftRho ψ hψ σ hker).range = σ.range := by
  ext y
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨h, rfl⟩ := hψ g
    exact ⟨h, (liftRho_apply hψ hker h).symm⟩
  · rintro ⟨h, rfl⟩
    exact ⟨ψ h, liftRho_apply hψ hker h⟩

theorem liftRho_nt (hnt : ∃ h y, σ h y ≠ y) : ∃ g y, liftRho ψ hψ σ hker g y ≠ y := by
  obtain ⟨h, y, hy⟩ := hnt
  exact ⟨ψ h, y, by rwa [liftRho_apply]⟩

end Lift

section SecPre

variable {X : Type} [CommGroup X]

theorem secPre_inf (W U : Subgroup X) (Q₁ Q₂ : Subgroup (Sec W U)) :
    secPre W U (Q₁ ⊓ Q₂) = secPre W U Q₁ ⊓ secPre W U Q₂ := by
  ext v
  simp only [Subgroup.mem_inf, mem_secPre]
  constructor
  · rintro ⟨hv, h1, h2⟩
    exact ⟨⟨hv, h1⟩, ⟨hv, h2⟩⟩
  · rintro ⟨⟨hv, h1⟩, ⟨_, h2⟩⟩
    exact ⟨hv, h1, h2⟩

theorem secPre_sup (W U : Subgroup X) (Q₁ Q₂ : Subgroup (Sec W U)) :
    secPre W U (Q₁ ⊔ Q₂) = secPre W U Q₁ ⊔ secPre W U Q₂ := by
  apply le_antisymm
  · intro v hv
    obtain ⟨hvW, hvQ⟩ := mem_secPre.mp hv
    obtain ⟨s₁, hs₁, s₂, hs₂, hs⟩ := Subgroup.mem_sup.mp hvQ
    obtain ⟨w₁, rfl⟩ := QuotientGroup.mk_surjective s₁
    have h1 : (w₁ : X) ∈ secPre W U Q₁ := mem_secPre.mpr ⟨w₁.2, hs₁⟩
    have h2 : (w₁ : X)⁻¹ * v ∈ secPre W U Q₂ := by
      refine mem_secPre.mpr ⟨W.mul_mem (W.inv_mem w₁.2) hvW, ?_⟩
      have e : (QuotientGroup.mk ⟨(w₁ : X)⁻¹ * v, W.mul_mem (W.inv_mem w₁.2) hvW⟩ : Sec W U) =
          (QuotientGroup.mk w₁)⁻¹ * QuotientGroup.mk ⟨v, hvW⟩ := rfl
      rw [e, ← hs, inv_mul_cancel_left]
      exact hs₂
    have e : v = (w₁ : X) * ((w₁ : X)⁻¹ * v) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)
  · exact sup_le (fun v hv => by
      obtain ⟨hvW, hvQ⟩ := mem_secPre.mp hv
      exact mem_secPre.mpr ⟨hvW, Subgroup.mem_sup_left hvQ⟩) (fun v hv => by
      obtain ⟨hvW, hvQ⟩ := mem_secPre.mp hv
      exact mem_secPre.mpr ⟨hvW, Subgroup.mem_sup_right hvQ⟩)

theorem secPre_bot {W U : Subgroup X} (hUW : U ≤ W) : secPre W U ⊥ = U := by
  ext v
  rw [mem_secPre]
  constructor
  · rintro ⟨hv, h1⟩
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact h1
  · intro hv
    refine ⟨hUW hv, ?_⟩
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hv

theorem secPre_top (W U : Subgroup X) : secPre W U ⊤ = W := by
  ext v
  rw [mem_secPre]
  exact ⟨fun ⟨hv, _⟩ => hv, fun hv => ⟨hv, Subgroup.mem_top _⟩⟩

end SecPre

section Coinv

variable {X : Type} [CommGroup X] [Finite X]

theorem commOn_ne_of_isPGroup (hX2 : ∀ x : X, x ^ 2 = 1) {Q₀ : Subgroup (MulAut X)}
    (hQ₀ : IsPGroup 2 Q₀) {N : Subgroup X} (hN : ∀ a ∈ Q₀, ∀ n ∈ N, a n ∈ N) (hN1 : N ≠ ⊥) :
    G6.commOn Q₀ N ≠ N := by
  intro heq
  have hN' : ∀ a : ↥Q₀, ∀ n ∈ N, Q₀.subtype a n ∈ N := fun a n hn => hN a a.2 n hn
  set ρN := resRho Q₀.subtype N hN' with hρN
  have hN2 : ∀ v : ↥N, v ^ 2 = 1 := fun v => Subtype.ext (by
    rw [Subgroup.coe_pow, hX2, Subgroup.coe_one])
  have hbot : commV (⊥ : Subgroup (MulAut ↥N)) ≠ ⊤ := by
    intro htop
    obtain ⟨⟨n, hn⟩, hn1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hN1
    have h1 : (⟨n, hn⟩ : ↥N) ∈ commV (⊥ : Subgroup (MulAut ↥N)) := by rw [htop]; trivial
    have h2 : commV (⊥ : Subgroup (MulAut ↥N)) ≤ ⊥ := by
      rw [G6.commV_le_iff]
      intro x hx v
      rw [Subgroup.mem_bot] at hx
      rw [hx, MulAut.one_apply, mul_inv_cancel]
      exact Subgroup.one_mem _
    have h3 := h2 h1
    rw [Subgroup.mem_bot] at h3
    exact hn1 (Subtype.ext (congrArg Subtype.val h3))
  have hne := G6.commV_ne_top_of_two_power hN2 (K := ρN.range) (N := ⊥)
    (fun k _ n hn => by rw [Subgroup.mem_bot] at hn ⊢; rw [hn, mul_one, mul_inv_cancel])
    (fun k hk => by
      obtain ⟨a, rfl⟩ := hk
      obtain ⟨m, hm⟩ := hQ₀ a
      exact ⟨m, by rw [← map_pow, hm, map_one]; exact Subgroup.one_mem _⟩) hbot
  apply hne
  rw [eq_top_iff]
  intro v _
  have hv : (v : X) ∈ G6.commOn Q₀ N := by rw [heq]; exact v.2
  have hle : G6.commOn Q₀ N ≤ (commV ρN.range).map N.subtype := by
    rw [G6.commOn, Subgroup.closure_le]
    rintro _ ⟨a, ha, u, hu, rfl⟩
    refine ⟨ρN ⟨a, ha⟩ ⟨u, hu⟩ * (⟨u, hu⟩ : ↥N)⁻¹,
      G6.mem_commV_of_mem (X := ρN.range) (x := ρN ⟨a, ha⟩)
        (MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩) ⟨u, hu⟩, ?_⟩
    rfl
  obtain ⟨v', hv', he⟩ := hle hv
  rwa [← Subtype.ext he]

omit [Finite X] in
theorem dualCoann_bot : dualCoann (⊥ : Subgroup (DualGrp X)) = ⊤ := by
  rw [eq_top_iff]
  intro v _ f hf
  rw [Subgroup.mem_bot.mp hf]
  rfl

theorem eq_top_of_commV_sup (hX2 : ∀ x : X, x ^ 2 = 1) {Q₀ : Subgroup (MulAut X)}
    (hQ₀ : IsPGroup 2 Q₀) {N : Subgroup X} (hN : ∀ a ∈ Q₀, ∀ n ∈ N, a n ∈ N)
    (h : commV Q₀ ⊔ N = ⊤) : N = ⊤ := by
  by_contra hne
  have hD : dualAnn N ≠ ⊥ := by
    intro hbot
    apply hne
    rw [← dualCoann_dualAnn hX2 N, hbot, dualCoann_bot]
  have hB : IsPGroup 2 (dualSub Q₀) := hQ₀.map (dualAct X)
  have hM : ∀ b ∈ dualSub Q₀, ∀ m ∈ dualAnn N, b m ∈ dualAnn N := by
    rintro _ ⟨a, ha, rfl⟩ m hm n hn
    rw [dualAct_apply]
    exact hm _ (hN _ (Q₀.inv_mem ha) n hn)
  obtain ⟨m, hmD, hm1, hmfix⟩ := B1.exists_fixed_ne_one dualGrp_sq hB hM hD
  have hmC : m ∈ fixV (dualSub Q₀) := fun b hb => hmfix b hb
  rw [fixV_dualSub] at hmC
  apply hm1
  refine DualGrp.ext fun v => ?_
  have hv : v ∈ commV Q₀ ⊔ N := by rw [h]; trivial
  obtain ⟨c, hc, n, hn, rfl⟩ := Subgroup.mem_sup.mp hv
  change m (c * n) = 1
  rw [map_mul, hmC c hc, hmD n hn, mul_one]

end Coinv

section Fix

variable {F : Type} [Field F] [Finite F] {n : ℕ} {H : Type} [Group H]
  {X : Type} [CommGroup X] [Finite X]

omit [Finite F] [Finite X] in
theorem commV_map_inv {Q : Subgroup H} [Q.Normal] (ρ : H →* MulAut X) (h : H) {x : X}
    (hx : x ∈ commV (Q.map ρ)) : ρ h x ∈ commV (Q.map ρ) := by
  refine G6.apply_mem_commV (fun y hy => ?_) hx
  obtain ⟨q, hq, rfl⟩ := hy
  exact ⟨h * q * h⁻¹, Subgroup.Normal.conj_mem inferInstance q hq h, by
    rw [map_mul, map_mul, map_inv]⟩

omit [Finite F] [Finite X] in
theorem commOn_map_inv {Q : Subgroup H} [Q.Normal] (ρ : H →* MulAut X) {N : Subgroup X}
    (hN : ∀ h, ∀ x ∈ N, ρ h x ∈ N) (h : H) {x : X} (hx : x ∈ G6.commOn (Q.map ρ) N) :
    ρ h x ∈ G6.commOn (Q.map ρ) N := by
  have hle : G6.commOn (Q.map ρ) N ≤ (G6.commOn (Q.map ρ) N).comap (ρ h).toMonoidHom := by
    rw [G6.commOn, Subgroup.closure_le]
    rintro _ ⟨_, ⟨q, hq, rfl⟩, u, hu, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    refine Subgroup.subset_closure ⟨ρ (h * q * h⁻¹),
      ⟨h * q * h⁻¹, Subgroup.Normal.conj_mem inferInstance q hq h, rfl⟩, ρ h u, hN h u hu, ?_⟩
    simp [map_mul, map_inv]
  exact hle hx

omit [Finite F] [Finite X] in
theorem ker_le_ker_secRho {ψ : H →* SL3 F} {Q : Subgroup H} (hQ : ψ.ker = Q)
    (ρ : H →* MulAut X) {W U : Subgroup X} (hW : ∀ h, ∀ w ∈ W, ρ h w ∈ W)
    (hU : ∀ h, ∀ u ∈ U, ρ h u ∈ U) (hQU : ∀ q ∈ Q, ∀ w ∈ W, ρ q w * w⁻¹ ∈ U) :
    ψ.ker ≤ (secRho ρ hW hU).ker := by
  intro q hq
  rw [hQ] at hq
  rw [MonoidHom.mem_ker, secRho_eq_one_iff]
  exact ⟨range_le_stabSub ρ hW ⟨q, rfl⟩, fun w hw => hQU q hq w hw⟩

omit [Finite X] in
theorem secRho_nt_of_not_le {Q : Subgroup H} [Q.Normal] (ρ : H →* MulAut X) {L : Subgroup H}
    (hN : ¬ commV (L.map ρ) ≤ commV (Q.map ρ)) :
    ∃ h y, secRho ρ (fun _ _ _ => Subgroup.mem_top _)
      (fun h _ hx => commV_map_inv (Q := Q) ρ h hx) h y ≠ y := by
  by_contra hcon
  push Not at hcon
  apply hN
  rw [G6.commV_le_iff]
  rintro _ ⟨l, -, rfl⟩ v
  have h1 := hcon l (QuotientGroup.mk ⟨v, Subgroup.mem_top v⟩)
  rw [secRho_mk, mk_eq_mk_iff, Subgroup.mem_subgroupOf] at h1
  simpa using h1

theorem fix_commV_ker (h14 : MS14AS) (hSQ : SQTKQuot) (hsq : SQTKGroup (SL3 F))
    (hF : Nat.card F = 2 ^ n) (hX2 : ∀ x : X, x ^ 2 = 1) (ψ : H →* SL3 F)
    (hψ : Function.Surjective ψ) {Q : Subgroup H} (hQ : ψ.ker = Q) (hQ2 : IsPGroup 2 Q)
    (ρ : H →* MulAut X) {L : Subgroup H} (hL : ⁅L, L⁆ = L) {A : Subgroup H}
    (hA2 : ∀ a ∈ A, ψ a ^ 2 = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, ψ a * ψ b = ψ b * ψ a)
    (hqA : Nat.card F ≤ Nat.card (A.map ψ)) (hcomm : Nat.card (commV (A.map ρ)) ≤ Nat.card F)
    (hN : ¬ commV (L.map ρ) ≤ commV (Q.map ρ)) :
    ∀ l ∈ L, ∀ x ∈ commV (Q.map ρ), ρ l x = x := by
  have : Q.Normal := hQ ▸ MonoidHom.normal_ker ψ
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  set K := commV (Q.map ρ) with hKdef
  have hKinv : ∀ h, ∀ x ∈ K, ρ h x ∈ K := fun h x hx => commV_map_inv ρ h hx
  have htop : ∀ h, ∀ x ∈ (⊤ : Subgroup X), ρ h x ∈ (⊤ : Subgroup X) :=
    fun _ _ _ => Subgroup.mem_top _
  set B : Subgroup (SL3 F) := A.map ψ with hBdef
  have hB2 : ∀ b ∈ B, b ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    exact hA2 a ha
  have hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
    exact hAc a ha a' ha'
  have hB : B ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hqA
    omega
  set σ₀ := secRho ρ htop hKinv with hσ₀
  have hker₀ : ψ.ker ≤ σ₀.ker := by
    intro q hq
    rw [hQ] at hq
    rw [MonoidHom.mem_ker, secRho_eq_one_iff]
    refine ⟨range_le_stabSub ρ htop ⟨q, rfl⟩, fun w _ => ?_⟩
    exact G6.mem_commV_of_mem (Subgroup.mem_map.mpr ⟨q, hq, rfl⟩) w
  have hnt₀ : ∃ h y, σ₀ h y ≠ y := by
    by_contra hcon
    push Not at hcon
    apply hN
    rw [G6.commV_le_iff]
    rintro _ ⟨l, -, rfl⟩ v
    have h1 := hcon l (QuotientGroup.mk ⟨v, Subgroup.mem_top v⟩)
    rw [hσ₀, secRho_mk, mk_eq_mk_iff, Subgroup.mem_subgroupOf] at h1
    simpa using h1
  have hlow₀ := le_card_commV h14 hSQ hsq hF (sec_sq hX2) (liftRho ψ hψ σ₀ hker₀)
    (liftRho_nt hψ hker₀ hnt₀) hB hB2 hBc (by
      rw [map_liftRho]
      exact (card_commV_sec_le ρ htop hKinv le_top A).trans (hcomm.trans hqA))
  rw [map_liftRho] at hlow₀
  have hmul₀ := card_commV_sec_mul_le ρ htop hKinv le_top A
  have hle₀ := Subgroup.card_le_of_le (commOn_le_commV (A.map ρ) ⊤)
  have key : ∀ m : ℕ, ∀ N : Subgroup X, Nat.card N ≤ m → (∀ h, ∀ x ∈ N, ρ h x ∈ N) →
      N ≤ K → ∀ l ∈ L, ∀ x ∈ N, ρ l x = x := by
    intro m
    induction m with
    | zero =>
      intro N hNc
      have : 0 < Nat.card N := Nat.card_pos
      omega
    | succ m ih =>
      intro N hNc hNinv hNK
      by_cases hN1 : N = ⊥
      · intro l _ x hx
        rw [hN1, Subgroup.mem_bot] at hx
        rw [hx, map_one]
      set N₁ := G6.commOn (Q.map ρ) N with hN₁def
      have hN₁N : N₁ ≤ N := by
        rw [hN₁def, G6.commOn, Subgroup.closure_le]
        rintro _ ⟨_, ⟨q, -, rfl⟩, u, hu, rfl⟩
        exact N.mul_mem (hNinv q u hu) (N.inv_mem hu)
      have hQ₀ : IsPGroup 2 (Q.map ρ) := hQ2.map ρ
      have hN₁ne : N₁ ≠ N := commOn_ne_of_isPGroup hX2 hQ₀
        (fun a ha n hn => by obtain ⟨q, -, rfl⟩ := ha; exact hNinv q n hn) hN1
      have hN₁inv : ∀ h, ∀ x ∈ N₁, ρ h x ∈ N₁ := fun h x hx => commOn_map_inv ρ hNinv h hx
      have hN₁c : Nat.card N₁ ≤ m := by
        have h1 : Nat.card N₁ < Nat.card N := by
          refine lt_of_le_of_ne (Subgroup.card_le_of_le hN₁N) fun h => hN₁ne ?_
          exact Subgroup.eq_of_le_of_card_ge hN₁N h.ge
        omega
      have hfix₁ := ih N₁ hN₁c hN₁inv (hN₁N.trans hNK)
      by_cases hstep : ∀ l ∈ L, ∀ x ∈ N, ρ l x * x⁻¹ ∈ N₁
      · exact fix_of_two_step ρ hL hfix₁ hstep
      exfalso
      push Not at hstep
      obtain ⟨l, hl, x, hx, hlx⟩ := hstep
      set σ₁ := secRho ρ hNinv hN₁inv with hσ₁
      have hker₁ : ψ.ker ≤ σ₁.ker := by
        intro q hq
        rw [hQ] at hq
        rw [MonoidHom.mem_ker, secRho_eq_one_iff]
        refine ⟨range_le_stabSub ρ hNinv ⟨q, rfl⟩, fun w hw => ?_⟩
        exact Subgroup.subset_closure ⟨ρ q, ⟨q, hq, rfl⟩, w, hw, rfl⟩
      have hnt₁ : ∃ h y, σ₁ h y ≠ y := sec_nt ρ hNinv hN₁inv hx hlx
      have hlow₁ := le_card_commV h14 hSQ hsq hF (sec_sq hX2) (liftRho ψ hψ σ₁ hker₁)
        (liftRho_nt hψ hker₁ hnt₁) hB hB2 hBc (by
          rw [map_liftRho]
          exact (card_commV_sec_le ρ hNinv hN₁inv hN₁N A).trans (hcomm.trans hqA))
      rw [map_liftRho] at hlow₁
      have hmul₁ := card_commV_sec_mul_le ρ hNinv hN₁inv hN₁N A
      have hNA : G6.commOn (A.map ρ) N ≤ G6.commOn (A.map ρ) ⊤ ⊓ K := by
        refine le_inf (Subgroup.closure_mono fun _ ⟨a, ha, u, _, hu⟩ =>
          ⟨a, ha, u, Subgroup.mem_top u, hu⟩) ?_
        rw [G6.commOn, Subgroup.closure_le]
        rintro _ ⟨_, ⟨a, -, rfl⟩, u, hu, rfl⟩
        exact hNK (N.mul_mem (hNinv a u hu) (N.inv_mem hu))
      have h1 : Nat.card F ≤ Nat.card (G6.commOn (A.map ρ) N) := by
        have h2 : 0 < Nat.card ↥(G6.commOn (A.map ρ) N ⊓ N₁) := Nat.card_pos
        calc Nat.card F ≤ Nat.card (commV (A.map σ₁)) := hlow₁
          _ ≤ Nat.card (commV (A.map σ₁)) * Nat.card ↥(G6.commOn (A.map ρ) N ⊓ N₁) :=
            Nat.le_mul_of_pos_right _ h2
          _ ≤ Nat.card (G6.commOn (A.map ρ) N) := hmul₁
      have h3 : Nat.card F * Nat.card F ≤ Nat.card F :=
        calc Nat.card F * Nat.card F
            ≤ Nat.card (commV (A.map σ₀)) * Nat.card ↥(G6.commOn (A.map ρ) ⊤ ⊓ K) :=
              Nat.mul_le_mul hlow₀ (h1.trans (Subgroup.card_le_of_le hNA))
          _ ≤ Nat.card (G6.commOn (A.map ρ) ⊤) := hmul₀
          _ ≤ Nat.card F := hle₀.trans hcomm
      have : Nat.card F * 2 ≤ Nat.card F * Nat.card F := Nat.mul_le_mul_left _ hq2
      omega
  exact key (Nat.card K) K le_rfl hKinv le_rfl

end Fix

section Split

variable {F : Type} [Field F] [Finite F] {n : ℕ} {H : Type} [Group H]
  {X : Type} [CommGroup X] [Finite X]

omit [Finite F] [Finite X] in
theorem natSplit_core (ψ : H →* SL3 F) (hψ : Function.Surjective ψ) {Q : Subgroup H}
    [Q.Normal] (ρ : H →* MulAut X)
    (htop : ∀ h, ∀ x ∈ (⊤ : Subgroup X), ρ h x ∈ (⊤ : Subgroup X))
    (hKinv : ∀ h, ∀ x ∈ commV (Q.map ρ), ρ h x ∈ commV (Q.map ρ))
    (hker₀ : ψ.ker ≤ (secRho ρ htop hKinv).ker)
    (hdec : IsNatDecomp (liftRho ψ hψ (secRho ρ htop hKinv) hker₀)) :
    ∃ C : Subgroup X, commV (Q.map ρ) ≤ C ∧
      (∀ h, ∀ c ∈ C, ρ h c * c⁻¹ ∈ commV (Q.map ρ)) ∧
      commV ρ.range ⊔ C = ⊤ ∧ commV ρ.range ⊓ C = commV (Q.map ρ) ∧
      ∃ (F' : Type) (_ : Field F') (_ : Finite F'), Nat.card F' = Nat.card F ∧
        ∃ (τ : H →* SL3 F') (β : ↥(commV ρ.range) →* Multiplicative (Fin 3 → F')),
          Function.Surjective τ ∧ Function.Surjective β ∧
          (∀ p : ↥(commV ρ.range), β p = 1 ↔ (p : X) ∈ commV (Q.map ρ)) ∧
          ∀ h (p : ↥(commV ρ.range)),
            β (resRho ρ (commV ρ.range) (fun g _ hx => commV_inv ρ g hx) h p) =
              Multiplicative.ofAdd ((τ h : Matrix (Fin 3) (Fin 3) F') *ᵥ
                Multiplicative.toAdd (β p)) := by
  set K := commV (Q.map ρ) with hKdef
  have hKP : K ≤ commV ρ.range := G6.commV_mono (Subgroup.map_le_range ρ Q)
  set σ₀ := secRho ρ htop hKinv with hσ₀
  set ρ₀ := liftRho ψ hψ σ₀ hker₀ with hρ₀
  obtain ⟨hPC, hPC', F', iF', fF', hFF', τ₀, θ, hτ₀s, hτ₀e⟩ := hdec
  have hP₀ : commV ρ₀.range = commV σ₀.range := by rw [hρ₀, range_liftRho]
  have hsecP : secPre ⊤ K (commV ρ₀.range) = commV ρ.range := by
    apply le_antisymm
    · rw [hP₀, hσ₀, range_secRho]
      exact secPre_commV_le hKP fun a ha w _ => G6.mem_commV_of_mem ha w
    · rw [G6.commV_le_iff]
      rintro _ ⟨h, rfl⟩ v
      refine (mem_secPre (W := ⊤) (U := K)).mpr ⟨Subgroup.mem_top _, ?_⟩
      rw [hP₀]
      have e : (QuotientGroup.mk ⟨ρ h v * v⁻¹, Subgroup.mem_top _⟩ : Sec ⊤ K) =
          σ₀ h (QuotientGroup.mk ⟨v, Subgroup.mem_top v⟩) *
            (QuotientGroup.mk ⟨v, Subgroup.mem_top v⟩)⁻¹ := rfl
      rw [e]
      exact G6.mem_commV_of_mem (MonoidHom.mem_range.mpr ⟨h, rfl⟩) _
  set C := secPre ⊤ K (fixV ρ₀.range) with hCdef
  refine ⟨C, le_secPre le_top _, ?_, ?_, ?_, F', iF', fF', hFF', τ₀.comp ψ, ?_⟩
  · intro h c hc
    obtain ⟨_, hc'⟩ := mem_secPre.mp hc
    have h1 := hc' (ρ₀ (ψ h)) ⟨ψ h, rfl⟩
    rw [hρ₀, liftRho_apply, hσ₀, secRho_mk, mk_eq_mk_iff, Subgroup.mem_subgroupOf] at h1
    simpa using h1
  · rw [← hsecP, ← secPre_sup, hPC', secPre_top]
  · rw [← hsecP, ← secPre_inf, hPC, secPre_bot le_top]
  have hmem : ∀ p : ↥(commV ρ.range),
      (QuotientGroup.mk ⟨(p : X), Subgroup.mem_top _⟩ : Sec ⊤ K) ∈ commV ρ₀.range := by
    intro p
    have hp : (p : X) ∈ secPre ⊤ K (commV ρ₀.range) := by rw [hsecP]; exact p.2
    obtain ⟨_, hp'⟩ := mem_secPre.mp hp
    exact hp'
  let j : ↥(commV ρ.range) →* ↥(commV ρ₀.range) :=
    { toFun := fun p => ⟨QuotientGroup.mk ⟨(p : X), Subgroup.mem_top _⟩, hmem p⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun p p' => Subtype.ext rfl }
  have hj : ∀ p, ((j p : ↥(commV ρ₀.range)) : Sec ⊤ K) =
      QuotientGroup.mk ⟨(p : X), Subgroup.mem_top _⟩ := fun _ => rfl
  refine ⟨θ.toMonoidHom.comp j, hτ₀s.comp hψ, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨⟨s, hs⟩, hsy⟩ := θ.surjective y
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective s
    have hw : (w : X) ∈ commV ρ.range := by
      rw [← hsecP]
      exact mem_secPre.mpr ⟨w.2, hs⟩
    refine ⟨⟨w, hw⟩, ?_⟩
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← hsy]
    congr 1
  · intro p
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    constructor
    · intro h1
      have h2 := congrArg Subtype.val h1
      rw [hj, Subgroup.coe_one, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
      exact h2
    · intro h1
      apply Subtype.ext
      rw [hj, Subgroup.coe_one, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact h1
  · intro h p
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply,
      MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    have e : j (resRho ρ (commV ρ.range) (fun g _ hx => commV_inv ρ g hx) h p) =
        resRho ρ₀ (commV ρ₀.range) (fun g _ hx => commV_inv ρ₀ g hx) (ψ h) (j p) := by
      apply Subtype.ext
      change (QuotientGroup.mk ⟨ρ h p, Subgroup.mem_top _⟩ : Sec ⊤ K) =
        liftRho ψ hψ σ₀ hker₀ (ψ h) (QuotientGroup.mk ⟨(p : X), Subgroup.mem_top _⟩)
      rw [liftRho_apply]
      rfl
    rw [e, hτ₀e]

theorem natSplit_quot (h14 : MS14AS) (hSQ : SQTKQuot) (hsq : SQTKGroup (SL3 F))
    (hF : Nat.card F = 2 ^ n) (hX2 : ∀ x : X, x ^ 2 = 1) (ψ : H →* SL3 F)
    (hψ : Function.Surjective ψ) {Q : Subgroup H} (hQ : ψ.ker = Q) (ρ : H →* MulAut X)
    {A : Subgroup H} (hA2 : ∀ a ∈ A, ψ a ^ 2 = 1)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, ψ a * ψ b = ψ b * ψ a)
    (hqA : Nat.card F ≤ Nat.card (A.map ψ)) (hcomm : Nat.card (commV (A.map ρ)) ≤ Nat.card F)
    (hnt : ¬ commV ρ.range ≤ commV (Q.map ρ)) :
    ∃ C : Subgroup X, commV (Q.map ρ) ≤ C ∧
      (∀ h, ∀ c ∈ C, ρ h c * c⁻¹ ∈ commV (Q.map ρ)) ∧
      commV ρ.range ⊔ C = ⊤ ∧ commV ρ.range ⊓ C = commV (Q.map ρ) ∧
      ∃ (F' : Type) (_ : Field F') (_ : Finite F'), Nat.card F' = Nat.card F ∧
        ∃ (τ : H →* SL3 F') (β : ↥(commV ρ.range) →* Multiplicative (Fin 3 → F')),
          Function.Surjective τ ∧ Function.Surjective β ∧
          (∀ p : ↥(commV ρ.range), β p = 1 ↔ (p : X) ∈ commV (Q.map ρ)) ∧
          ∀ h (p : ↥(commV ρ.range)),
            β (resRho ρ (commV ρ.range) (fun g _ hx => commV_inv ρ g hx) h p) =
              Multiplicative.ofAdd ((τ h : Matrix (Fin 3) (Fin 3) F') *ᵥ
                Multiplicative.toAdd (β p)) := by
  have : Q.Normal := hQ ▸ MonoidHom.normal_ker ψ
  have hKinv : ∀ h, ∀ x ∈ commV (Q.map ρ), ρ h x ∈ commV (Q.map ρ) :=
    fun h x hx => commV_map_inv ρ h hx
  have htop : ∀ h, ∀ x ∈ (⊤ : Subgroup X), ρ h x ∈ (⊤ : Subgroup X) :=
    fun _ _ _ => Subgroup.mem_top _
  set B : Subgroup (SL3 F) := A.map ψ with hBdef
  have hB2 : ∀ b ∈ B, b ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    exact hA2 a ha
  have hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
    exact hAc a ha a' ha'
  have hB : B ≠ ⊥ := by
    intro hbot
    have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
    rw [hbot, Subgroup.card_bot] at hqA
    omega
  have hker₀ := ker_le_ker_secRho hQ ρ htop hKinv fun q hq w _ =>
    G6.mem_commV_of_mem (Subgroup.mem_map.mpr ⟨q, hq, rfl⟩) w
  have hnt₀ : ∃ h y, secRho ρ htop hKinv h y ≠ y :=
    secRho_nt_of_not_le (L := ⊤) ρ (by rw [← MonoidHom.range_eq_map]; exact hnt)
  have hcomm' : Nat.card (commV (B.map (liftRho ψ hψ _ hker₀))) ≤ Nat.card F := by
    rw [map_liftRho]
    exact (card_commV_sec_le ρ htop hKinv le_top A).trans hcomm
  exact natSplit_core ψ hψ ρ htop hKinv hker₀ (dualOff_decomp h14 hSQ hsq hF (sec_sq hX2) _
    (liftRho_nt hψ hker₀ hnt₀) hB hB2 hBc hqA hcomm')

end Split

end CFSG.Quasithin.MS93.S4A.F
