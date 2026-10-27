module

public import CFSG.RankThree.GF2n.Stroth80.Sec83Card
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {G : Type} [Group G]

structure Om4Frame (Q Z V W R N L L' A A' : Subgroup G) (q : ℕ) : Prop where
  ZV : Z ≤ V
  VW : V ≤ W
  WQ : W ≤ Q
  Qcomm : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ Z
  Qsq : ∀ x ∈ Q, x ^ 2 ∈ Z
  Zcen : ∀ z ∈ Z, ∀ x ∈ Q, z * x = x * z
  Vsq : ∀ v ∈ V, v ^ 2 = 1
  Vcen : ∀ v ∈ V, ∀ x ∈ W, v * x = x * v
  RV : ∀ s ∈ R, ∀ x ∈ V, s * x * s⁻¹ ∈ V
  RW : ∀ s ∈ R, ∀ x ∈ W, s * x * s⁻¹ ∈ W
  NR : N ≤ R
  LR : L ≤ R
  L'R : L' ≤ R
  N3 : ∀ s ∈ N, ∀ x ∈ W, ⁅s, x⁆ ∈ V
  opp : IsOppDecomp W V L L' A A'
  Lsq : ∀ y ∈ L, y ^ 2 ∈ Q
  L'sq : ∀ y ∈ L', y ^ 2 ∈ Q
  LZ : ∀ y ∈ L, ∀ z ∈ Z, y * z = z * y
  L'Z : ∀ y ∈ L', ∀ z ∈ Z, y * z = z * y
  gen : ∀ y ∈ L', y ∉ N → R ≤ N ⊔ (L ⊔ conjSubgroup y L)
  gen' : ∀ y ∈ L, y ∉ N → R ≤ N ⊔ (L' ⊔ conjSubgroup y L')
  cardL : Nat.card L = Nat.card ↥(L ⊓ N) * q ^ 2
  cardL' : Nat.card L' = Nat.card ↥(L' ⊓ N) * q ^ 2
  Aab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a
  A'ab : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a
  CQW : ∀ x ∈ Q, (∀ w ∈ W, ⁅x, w⁆ = 1) → x ∈ V
  q2 : 2 ≤ q
  WV : Nat.card W = Nat.card V * q ^ 4

theorem isOppDecomp_swap {P I L₁ L₂ A₁ A₂ : Subgroup G} (h : IsOppDecomp P I L₁ L₂ A₁ A₂) :
    IsOppDecomp P I L₂ L₁ A₂ A₁ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h3, h4, h1, h2, by rw [sup_comm]; exact h5, by rw [inf_comm]; exact h6, h7, h8, h10, h9⟩

theorem Om4Frame.swap {Q Z V W R N L L' A A' : Subgroup G} {q : ℕ}
    (F : Om4Frame Q Z V W R N L L' A A' q) : Om4Frame Q Z V W R N L' L A' A q where
  ZV := F.ZV
  VW := F.VW
  WQ := F.WQ
  Qcomm := F.Qcomm
  Qsq := F.Qsq
  Zcen := F.Zcen
  Vsq := F.Vsq
  Vcen := F.Vcen
  RV := F.RV
  RW := F.RW
  NR := F.NR
  LR := F.L'R
  L'R := F.LR
  N3 := F.N3
  opp := isOppDecomp_swap F.opp
  Lsq := F.L'sq
  L'sq := F.Lsq
  LZ := F.L'Z
  L'Z := F.LZ
  gen := F.gen'
  gen' := F.gen
  cardL := F.cardL'
  cardL' := F.cardL
  Aab := F.A'ab
  A'ab := F.Aab
  CQW := F.CQW
  q2 := F.q2
  WV := F.WV

variable {Q Z V W R N L L' A A' : Subgroup G} {q : ℕ}

theorem sec7om4_decomp {P I L₁ L₂ A₁ A₂ : Subgroup G} (h : IsOppDecomp P I L₁ L₂ A₁ A₂) :
    ∀ c ∈ P, ∃ a ∈ A₁, ∃ b ∈ A₂, c = a * b := by
  obtain ⟨hI1, hA1P, hI2, hA2P, hsup, hinf, hcomm, hsq, h9, h10⟩ := h
  have hnorm : A₂ ≤ Subgroup.normalizer (A₁ : Set G) := by
    refine Subgroup.le_normalizer_iff.mpr fun y hy a ha => ?_
    have hc : ⁅y, a⁆ ∈ A₁ := hI1 (hcomm y (hA2P hy) a (hA1P ha))
    have key : y * a * y⁻¹ = ⁅y, a⁆ * a := by
      rw [commutatorElement_def]
      group
    rw [key]
    exact A₁.mul_mem hc ha
  intro c hc
  have h1 : c ∈ ((A₁ ⊔ A₂ : Subgroup G) : Set G) := by
    rw [hsup]
    exact hc
  rw [Subgroup.coe_mul_of_right_le_normalizer_left A₁ A₂ hnorm] at h1
  obtain ⟨a, ha, b, hb, rfl⟩ := h1
  exact ⟨a, ha, b, hb, rfl⟩

theorem sec7om4_G_aux {V R N L L' : Subgroup G} (hRV : ∀ s ∈ R, ∀ x ∈ V, s * x * s⁻¹ ∈ V)
    (hLR : L ≤ R) (hL'R : L' ≤ R) (hNR : N ≤ R) {w y : G}
    (hN : ∀ s ∈ N, ⁅s, w⁆ ∈ V) (hL : ∀ l ∈ L, ⁅l, w⁆ ∈ V) (hy : y ∈ L') (hyw : ⁅y, w⁆ ∈ V)
    (hgen : R ≤ N ⊔ (L ⊔ conjSubgroup y L)) : ∀ l ∈ L', ⁅l, w⁆ ∈ V := by
  let S : Subgroup G :=
    { carrier := {s | s ∈ R ∧ ⁅s, w⁆ ∈ V}
      mul_mem' := by
        rintro a b ⟨haR, ha⟩ ⟨hbR, hb⟩
        refine ⟨R.mul_mem haR hbR, ?_⟩
        have e : ⁅a * b, w⁆ = a * ⁅b, w⁆ * a⁻¹ * ⁅a, w⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact V.mul_mem (hRV a haR _ hb) ha
      one_mem' := ⟨R.one_mem, by simp [commutatorElement_def]⟩
      inv_mem' := by
        rintro a ⟨haR, ha⟩
        refine ⟨R.inv_mem haR, ?_⟩
        have e : ⁅a⁻¹, w⁆ = (a⁻¹ * ⁅a, w⁆ * a)⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have := hRV a⁻¹ (R.inv_mem haR) _ ha
        simpa [mul_assoc] using V.inv_mem this }
  have hNS : N ≤ S := fun s hs => ⟨hNR hs, hN s hs⟩
  have hLS : L ≤ S := fun s hs => ⟨hLR hs, hL s hs⟩
  have hyS : y ∈ S := ⟨hL'R hy, hyw⟩
  have hLyS : conjSubgroup y L ≤ S := by
    intro x hx
    rw [mem_conjSubgroup] at hx
    have h1 : y * (y⁻¹ * x * y) * y⁻¹ ∈ S :=
      S.mul_mem (S.mul_mem hyS (hLS hx)) (S.inv_mem hyS)
    simpa [mul_assoc] using h1
  have hRS : R ≤ S := hgen.trans (sup_le hNS (sup_le hLS hLyS))
  intro l hl
  exact (hRS (hL'R hl)).2

theorem Om4Frame.fixed (F : Om4Frame Q Z V W R N L L' A A' q) {w y : G} (hw : w ∈ A) (hy : y ∈ L')
    (hyN : y ∉ N) (hyw : ⁅y, w⁆ ∈ V) : w ∈ V := by
  obtain ⟨hVA, hAW, hVA', hA'W, hsup, hinf, hcomm, hsq, hiffA, hiffA'⟩ := F.opp
  have hwW : w ∈ W := hAW hw
  have hLw : ∀ l ∈ L, ⁅l, w⁆ ∈ V := (hiffA w hwW).mp hw
  have hall := sec7om4_G_aux F.RV F.LR F.L'R F.NR (fun s hs => F.N3 s hs w hwW) hLw hy hyw
    (F.gen y hy hyN)
  have hA' : w ∈ A' := (hiffA' w hwW).mpr hall
  have : w ∈ A ⊓ A' := ⟨hw, hA'⟩
  rwa [hinf] at this

theorem Om4Frame.Ha (F : Om4Frame Q Z V W R N L L' A A' q) {y w : G} (hy : y ∈ L')
    (hw : w ∈ A) : ⁅y, w⁆ ∈ A' := by
  have hopp := F.opp
  obtain ⟨hVA, hAW, hVA', hA'W, hsup, hinf, hcomm, hsq, hiffA, hiffA'⟩ := hopp
  have hwW : w ∈ W := hAW hw
  by_cases hyN : y ∈ N
  · exact hVA' (F.N3 y hyN w hwW)
  obtain ⟨c, hc⟩ : ∃ c, c = ⁅y, w⁆ := ⟨_, rfl⟩
  rw [← hc]
  have hyR : y ∈ R := F.L'R hy
  have hcW : c ∈ W := by
    have h1 := F.RW y hyR w hwW
    rw [hc, commutatorElement_def]
    exact W.mul_mem h1 (W.inv_mem hwW)
  have hy2Q := F.L'sq y hy
  have hwQ := F.WQ hwW
  have h2 : ⁅y ^ 2, w⁆ ∈ V := F.ZV (F.Qcomm _ hy2Q w hwQ)
  have h3 : y * c * y⁻¹ * c = ⁅y ^ 2, w⁆ := by
    rw [hc]
    simp only [commutatorElement_def, pow_two]
    group
  have h4 : y * c * y⁻¹ * c ∈ V := by
    rw [h3]
    exact h2
  have hc2 : c ^ 2 ∈ V := hsq c hcW
  have h5 : ⁅y, c⁆ ∈ V := by
    have e : ⁅y, c⁆ = (y * c * y⁻¹ * c) * (c ^ 2)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact V.mul_mem h4 (V.inv_mem hc2)
  obtain ⟨a₁, ha₁, a₂, ha₂, hca⟩ := sec7om4_decomp F.opp c hcW
  have ha₁W : a₁ ∈ W := hAW ha₁
  have hv2 : ⁅y, a₂⁆ ∈ V := (hiffA' a₂ (hA'W ha₂)).mp ha₂ y hy
  have e2 : ⁅y, a₁ * a₂⁆ = ⁅y, a₁⁆ * ⁅y, a₂⁆ := by
    have e3 : ⁅y, a₁ * a₂⁆ = ⁅y, a₁⁆ * (a₁ * ⁅y, a₂⁆ * a₁⁻¹) := by
      simp only [commutatorElement_def]
      group
    have e4 : a₁ * ⁅y, a₂⁆ * a₁⁻¹ = ⁅y, a₂⁆ := by
      rw [mul_inv_eq_iff_eq_mul]
      exact (F.Vcen _ hv2 a₁ ha₁W).symm
    rw [e3, e4]
  have h6 : ⁅y, a₁⁆ ∈ V := by
    have e : ⁅y, a₁⁆ = ⁅y, c⁆ * ⁅y, a₂⁆⁻¹ := by
      rw [hca, e2]
      group
    rw [e]
    exact V.mul_mem h5 (V.inv_mem hv2)
  have ha₁V : a₁ ∈ V := F.fixed ha₁ hy hyN h6
  rw [hca]
  exact A'.mul_mem (hVA' ha₁V) ha₂

theorem Om4Frame.Hc [Finite G] (F : Om4Frame Q Z V W R N L L' A A' q) {w : G} (hw : w ∈ A)
    (hwV : w ∉ V) :
    q ^ 2 * Nat.card V ≤ Nat.card A' ∧
      (Nat.card A' = q ^ 2 * Nat.card V → ∀ c ∈ A', ∃ y ∈ L', ∃ v ∈ V, c = ⁅y, w⁆ * v) := by
  have hopp := F.opp
  obtain ⟨hVA, hAW, hVA', hA'W, hsup, hinf, hcomm, hsq, hiffA, hiffA'⟩ := hopp
  have hwW : w ∈ W := hAW hw
  have hmem : ∀ y : ↥L', ⁅(y : G), w⁆ ∈ A' := fun y => F.Ha y.2 hw
  have hAN : A' ≤ Subgroup.normalizer (V : Set G) := by
    refine Subgroup.le_normalizer_iff.mpr fun x hx v hv => ?_
    have hc : ⁅x, v⁆ ∈ V := hcomm x (hA'W hx) v (F.VW hv)
    have key : x * v * x⁻¹ = ⁅x, v⁆ * v := by
      rw [commutatorElement_def]
      group
    rw [key]
    exact V.mul_mem hc hv
  haveI : (V.subgroupOf A').Normal := Subgroup.normal_subgroupOf_of_le_normalizer hAN
  obtain ⟨f, hf⟩ : ∃ f : ↥L' →* ↥A' ⧸ V.subgroupOf A',
      ∀ y : ↥L', f y = QuotientGroup.mk (⟨⁅(y : G), w⁆, hmem y⟩ : ↥A') := by
    refine ⟨MonoidHom.mk' (fun y : ↥L' => QuotientGroup.mk (⟨⁅(y : G), w⁆, hmem y⟩ : ↥A')) ?_,
      fun y => rfl⟩
    intro y₁ y₂
    show QuotientGroup.mk (⟨⁅((y₁ * y₂ : ↥L') : G), w⁆, hmem (y₁ * y₂)⟩ : ↥A') =
      QuotientGroup.mk (⟨⁅(y₁ : G), w⁆, hmem y₁⟩ : ↥A') *
        QuotientGroup.mk (⟨⁅(y₂ : G), w⁆, hmem y₂⟩ : ↥A')
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    set X₁ := ⁅(y₁ : G), w⁆ with hX₁
    set X₂ := ⁅(y₂ : G), w⁆ with hX₂
    have hX₁W : X₁ ∈ W := hA'W (hmem y₁)
    have hX₂W : X₂ ∈ W := hA'W (hmem y₂)
    have hv₁ : ⁅(y₁ : G), X₂⁆ ∈ V := (hiffA' X₂ hX₂W).mp (hmem y₂) y₁ y₁.2
    have hP : ⁅(y₁ : G) * (y₂ : G), w⁆ = ⁅(y₁ : G), X₂⁆ * (X₂ * X₁) := by
      rw [hX₁, hX₂]
      simp only [commutatorElement_def]
      group
    rw [hP]
    set v₁ := ⁅(y₁ : G), X₂⁆ with hv₁def
    have c1 : X₂⁻¹ * v₁⁻¹ = v₁⁻¹ * X₂⁻¹ := (F.Vcen _ (V.inv_mem hv₁) _ (W.inv_mem hX₂W)).symm
    have c2 : X₁⁻¹ * v₁⁻¹ = v₁⁻¹ * X₁⁻¹ := (F.Vcen _ (V.inv_mem hv₁) _ (W.inv_mem hX₁W)).symm
    have e : (v₁ * (X₂ * X₁))⁻¹ * (X₁ * X₂) = v₁⁻¹ * (X₁⁻¹ * X₂⁻¹ * X₁ * X₂) := by
      calc (v₁ * (X₂ * X₁))⁻¹ * (X₁ * X₂) = X₁⁻¹ * X₂⁻¹ * v₁⁻¹ * X₁ * X₂ := by group
        _ = X₁⁻¹ * (X₂⁻¹ * v₁⁻¹) * X₁ * X₂ := by simp only [mul_assoc]
        _ = X₁⁻¹ * (v₁⁻¹ * X₂⁻¹) * X₁ * X₂ := by rw [c1]
        _ = (X₁⁻¹ * v₁⁻¹) * X₂⁻¹ * X₁ * X₂ := by simp only [mul_assoc]
        _ = (v₁⁻¹ * X₁⁻¹) * X₂⁻¹ * X₁ * X₂ := by rw [c2]
        _ = v₁⁻¹ * (X₁⁻¹ * X₂⁻¹ * X₁ * X₂) := by simp only [mul_assoc]
    rw [e]
    have hcc : X₁⁻¹ * X₂⁻¹ * X₁ * X₂ = ⁅X₁⁻¹, X₂⁻¹⁆ := by
      simp only [commutatorElement_def, inv_inv]
    rw [hcc]
    exact V.mul_mem (V.inv_mem hv₁) (hcomm _ (W.inv_mem hX₁W) _ (W.inv_mem hX₂W))
  have hker : f.ker = N.subgroupOf L' := by
    ext y
    rw [MonoidHom.mem_ker, hf, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf]
    constructor
    · intro h
      by_contra hyN
      exact hwV (F.fixed hw y.2 hyN h)
    · intro hyN
      exact F.N3 y hyN w hwW
  have hLmap : Nat.card ↥((L'.subgroupOf L').map f) = q ^ 2 := by
    have h1 := card_inf_mul_card_map (le_refl L') f hker
    have h2 := F.cardL'
    have hpos : 0 < Nat.card ↥(L' ⊓ N) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2)
  have hQcard : Nat.card (↥A' ⧸ V.subgroupOf A') * Nat.card V = Nat.card A' := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (V.subgroupOf A')
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVA').toEquiv] at h1
    exact h1.symm
  have hle : q ^ 2 ≤ Nat.card (↥A' ⧸ V.subgroupOf A') := by
    rw [← hLmap]
    exact Subgroup.card_le_card_group _
  refine ⟨?_, fun hAeq c hc => ?_⟩
  · calc q ^ 2 * Nat.card V ≤ Nat.card (↥A' ⧸ V.subgroupOf A') * Nat.card V :=
          Nat.mul_le_mul_right _ hle
      _ = Nat.card A' := hQcard
  · have hVpos : 0 < Nat.card V := Nat.card_pos
    have hq : Nat.card (↥A' ⧸ V.subgroupOf A') = q ^ 2 :=
      Nat.eq_of_mul_eq_mul_right hVpos (hQcard.trans hAeq)
    have htop : (L'.subgroupOf L').map f = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [hLmap, hq])
    have hmk : (QuotientGroup.mk (⟨c, hc⟩ : ↥A') : ↥A' ⧸ V.subgroupOf A') ∈
        (L'.subgroupOf L').map f := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨y, -, hy⟩ := hmk
    rw [hf, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hy
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hy
    refine ⟨y, y.2, _, hy, ?_⟩
    group

theorem comm_sq_eq_comm_comm {y w : G} (hy : y * w ^ 2 = w ^ 2 * y)
    (hk : ⁅w, ⁅y, w⁆⁆ * ⁅y, w⁆ = ⁅y, w⁆ * ⁅w, ⁅y, w⁆⁆) : ⁅y, w⁆ ^ 2 = ⁅⁅y, w⁆, w⁆ := by
  set c := ⁅y, w⁆ with hc
  set k := ⁅w, c⁆ with hk'
  clear_value k c
  have h1 : y * w * y⁻¹ = c * w := by rw [hc, commutatorElement_def]; group
  have h2 : (y * w * y⁻¹) ^ 2 = w ^ 2 := by
    have : (y * w * y⁻¹) ^ 2 = y * w ^ 2 * y⁻¹ := by rw [pow_two, pow_two]; group
    rw [this, hy]; group
  have h3 : w * c = k * c * w := by rw [hk', commutatorElement_def]; group
  have h4 : (c * w) ^ 2 = k * c ^ 2 * w ^ 2 := by
    calc (c * w) ^ 2 = c * (w * c) * w := by simp only [pow_two, mul_assoc]
      _ = c * (k * c * w) * w := by rw [h3]
      _ = (c * k) * c * w * w := by simp only [mul_assoc]
      _ = (k * c) * c * w * w := by rw [hk]
      _ = k * c ^ 2 * w ^ 2 := by simp only [pow_two, mul_assoc]
  rw [h1, h4] at h2
  have h5 : k * c ^ 2 = 1 := by
    have := congrArg (· * (w ^ 2)⁻¹) h2
    simpa [mul_assoc] using this
  have h6 : c ^ 2 = k⁻¹ := eq_inv_of_mul_eq_one_right h5
  rw [h6, hk', commutatorElement_inv]

theorem Om4Frame.sq_comm (F : Om4Frame Q Z V W R N L L' A A' q) {w : G} (hw : w ∈ A)
    (hsurj : ∀ c ∈ A', ∃ y ∈ L', ∃ v ∈ V, c = ⁅y, w⁆ * v) : ∀ c ∈ A', c ^ 2 = ⁅c, w⁆ := by
  intro c hc
  obtain ⟨y, hy, v, hv, rfl⟩ := hsurj c hc
  obtain ⟨hVA, hAW, hVA', hA'W, hsup, hinf, hcomm, hsq, hiffA, hiffA'⟩ := F.opp
  have hwW : w ∈ W := hAW hw
  have hwQ : w ∈ Q := F.WQ hwW
  have heW : ⁅y, w⁆ ∈ W := hA'W (F.Ha hy hw)
  have heQ : ⁅y, w⁆ ∈ Q := F.WQ heW
  have hS : ⁅y, w⁆ ^ 2 = ⁅⁅y, w⁆, w⁆ :=
    comm_sq_eq_comm_comm (F.L'Z y hy (w ^ 2) (F.Qsq w hwQ))
      (F.Zcen _ (F.Qcomm w hwQ _ heQ) _ heQ)
  have hve : v * ⁅y, w⁆ = ⁅y, w⁆ * v := F.Vcen v hv _ heW
  have hvw : v * w * v⁻¹ = w := by
    rw [mul_inv_eq_iff_eq_mul]
    exact F.Vcen v hv w hwW
  have e1 : (⁅y, w⁆ * v) ^ 2 = ⁅y, w⁆ ^ 2 := by
    calc (⁅y, w⁆ * v) ^ 2 = ⁅y, w⁆ * v * (⁅y, w⁆ * v) := pow_two _
      _ = ⁅y, w⁆ * (v * ⁅y, w⁆) * v := by simp only [mul_assoc]
      _ = ⁅y, w⁆ * (⁅y, w⁆ * v) * v := by rw [hve]
      _ = ⁅y, w⁆ ^ 2 * v ^ 2 := by simp only [pow_two, mul_assoc]
      _ = ⁅y, w⁆ ^ 2 := by rw [F.Vsq v hv, mul_one]
  have e2 : ⁅⁅y, w⁆ * v, w⁆ = ⁅⁅y, w⁆, w⁆ := by
    have : ⁅⁅y, w⁆ * v, w⁆ = ⁅y, w⁆ * (v * w * v⁻¹) * ⁅y, w⁆⁻¹ * w⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [this, hvw, commutatorElement_def ⁅y, w⁆ w]
  rw [e1, e2, hS]

theorem Om4Frame.false_of_surj [Finite G] (F : Om4Frame Q Z V W R N L L' A A' q)
    (hAV : A ≠ V) (hA : Nat.card A = q ^ 2 * Nat.card V)
    (hsurj : ∀ w ∈ A, w ∉ V → ∀ c ∈ A', ∃ y ∈ L', ∃ v ∈ V, c = ⁅y, w⁆ * v) : False := by
  obtain ⟨hVA, hAW, hVA', hA'W, hsup, hinf, hcomm, hsq, hiffA, hiffA'⟩ := F.opp
  obtain ⟨w, hwA, hwV⟩ : ∃ w ∈ A, w ∉ V := by
    by_contra h
    push Not at h
    exact hAV (le_antisymm h hVA)
  have hVpos : 0 < Nat.card V := Nat.card_pos
  have hq4 : 4 ≤ q ^ 2 := by nlinarith [F.q2]
  obtain ⟨w', hw'A, hw'V, hww'⟩ : ∃ w' ∈ A, w' ∉ V ∧ w⁻¹ * w' ∉ V := by
    by_contra h
    push Not at h
    have hsub : (A : Set G) ⊆ (V : Set G) ∪ (fun v => w * v) '' (V : Set G) := by
      intro a ha
      by_cases haV : a ∈ V
      · exact Or.inl haV
      · right
        refine ⟨w⁻¹ * a, h a ha haV, ?_⟩
        simp
    have hcard : (A : Set G).ncard ≤ 2 * (V : Set G).ncard := by
      calc (A : Set G).ncard
          ≤ ((V : Set G) ∪ (fun v => w * v) '' (V : Set G)).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ (V : Set G).ncard + ((fun v => w * v) '' (V : Set G)).ncard :=
            Set.ncard_union_le _ _
        _ ≤ (V : Set G).ncard + (V : Set G).ncard := by
            have := Set.ncard_image_le (f := fun v => w * v) (s := (V : Set G)) (Set.toFinite _)
            omega
        _ = 2 * (V : Set G).ncard := by ring
    have e1 : Nat.card A = (A : Set G).ncard := Nat.card_coe_set_eq _
    have e2 : Nat.card V = (V : Set G).ncard := Nat.card_coe_set_eq _
    rw [e1, e2] at hA
    rw [e2] at hVpos
    nlinarith
  have hsq' : ∀ x ∈ A, x ∉ V → ∀ c ∈ A', c ^ 2 = ⁅c, x⁆ := fun x hx hxV =>
    F.sq_comm hx (hsurj x hx hxV)
  have hdA : w⁻¹ * w' ∈ A := A.mul_mem (A.inv_mem hwA) hw'A
  have hdA' : ∀ c ∈ A', c * (w⁻¹ * w') = (w⁻¹ * w') * c := by
    intro c hc
    have h1 : c * w * c⁻¹ = c ^ 2 * w := by
      have := hsq' w hwA hwV c hc
      rw [commutatorElement_def] at this
      calc c * w * c⁻¹ = (c * w * c⁻¹ * w⁻¹) * w := by group
        _ = c ^ 2 * w := by rw [← this]
    have h2 : c * w' * c⁻¹ = c ^ 2 * w' := by
      have := hsq' w' hw'A hw'V c hc
      rw [commutatorElement_def] at this
      calc c * w' * c⁻¹ = (c * w' * c⁻¹ * w'⁻¹) * w' := by group
        _ = c ^ 2 * w' := by rw [← this]
    have h3 : c * (w⁻¹ * w') * c⁻¹ = w⁻¹ * w' := by
      calc c * (w⁻¹ * w') * c⁻¹ = (c * w * c⁻¹)⁻¹ * (c * w' * c⁻¹) := by group
        _ = (c ^ 2 * w)⁻¹ * (c ^ 2 * w') := by rw [h1, h2]
        _ = w⁻¹ * w' := by group
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3
  have hdW : ∀ x ∈ W, ⁅w⁻¹ * w', x⁆ = 1 := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := sec7om4_decomp F.opp x hx
    have h2 : (w⁻¹ * w') * b = b * (w⁻¹ * w') := (hdA' b hb).symm
    refine commutatorElement_eq_one_iff_mul_comm.mpr ?_
    calc w⁻¹ * w' * (a * b) = (w⁻¹ * w' * a) * b := by simp only [mul_assoc]
      _ = (a * (w⁻¹ * w')) * b := by rw [F.Aab _ hdA a ha]
      _ = a * ((w⁻¹ * w') * b) := by simp only [mul_assoc]
      _ = a * (b * (w⁻¹ * w')) := by rw [h2]
      _ = a * b * (w⁻¹ * w') := by simp only [mul_assoc]
  have hdV : w⁻¹ * w' ∈ V := F.CQW _ (F.WQ (hAW hdA)) hdW
  exact hww' hdV

theorem Om4Frame.main_aux [Finite G] (F : Om4Frame Q Z V W R N L L' A A' q) (hAV : A ≠ V) :
    False := by
  obtain ⟨hVA, hAW, hVA', hA'W, hsup, hinf, hcomm, hsq, hiffA, hiffA'⟩ := F.opp
  have hcard := card_mul_card_isOppDecomp F.opp
  have hVpos : 0 < Nat.card V := Nat.card_pos
  have hq4 : 4 ≤ q ^ 2 := by nlinarith [F.q2]
  obtain ⟨w, hwA, hwV⟩ : ∃ w ∈ A, w ∉ V := by
    by_contra h
    push Not at h
    exact hAV (le_antisymm h hVA)
  obtain ⟨h1, -⟩ := F.Hc hwA hwV
  have hA'V : A' ≠ V := by
    intro h
    rw [h] at h1
    nlinarith
  obtain ⟨w', hw'A', hw'V⟩ : ∃ w' ∈ A', w' ∉ V := by
    by_contra h
    push Not at h
    exact hA'V (le_antisymm h hVA')
  obtain ⟨h2, -⟩ := F.swap.Hc hw'A' hw'V
  have hWV := F.WV
  rw [hWV] at hcard
  have hq0 : 0 < q := by
    have := F.q2
    omega
  have hkpos : 0 < q ^ 2 * Nat.card V := Nat.mul_pos (pow_pos hq0 2) hVpos
  have hprod : (q ^ 2 * Nat.card V) * (q ^ 2 * Nat.card V) = Nat.card A * Nat.card A' := by
    rw [← hcard]
    ring
  have hA : Nat.card A = q ^ 2 * Nat.card V := by
    by_contra hne
    have hlt : q ^ 2 * Nat.card V < Nat.card A := lt_of_le_of_ne h2 (Ne.symm hne)
    have hle : (q ^ 2 * Nat.card V + 1) * (q ^ 2 * Nat.card V) ≤ Nat.card A * Nat.card A' :=
      Nat.mul_le_mul (Nat.succ_le_of_lt hlt) h1
    rw [← hprod] at hle
    nlinarith
  have hA' : Nat.card A' = q ^ 2 * Nat.card V := by
    rw [hA] at hprod
    exact (Nat.eq_of_mul_eq_mul_left hkpos hprod).symm
  exact F.false_of_surj hAV hA (fun w hw hwV => (F.Hc hw hwV).2 hA')

theorem Om4Frame.contradiction [Finite G] (F : Om4Frame Q Z V W R N L L' A A' q) : False := by
  by_cases hAV : A = V
  · by_cases hA'V : A' = V
    · have hW : W = V := by
        rw [← F.opp.2.2.2.2.1, hAV, hA'V, sup_idem]
      have hc := F.WV
      rw [hW] at hc
      have hVpos : 0 < Nat.card V := Nat.card_pos
      have h16 : 2 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left F.q2 4
      have : Nat.card V * 16 ≤ Nat.card V * q ^ 4 := Nat.mul_le_mul_left _ (by simpa using h16)
      omega
    · exact F.swap.main_aux hA'V
  · exact F.main_aux hAV

end CFSG.RankThree.GF2n.Stroth80
