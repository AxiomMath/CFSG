module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4HexBase

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin

section CosetAct

@[expose, reducible] def burnsideF45_cosetAct {A : Type} [Group A] (G₀ G₁ G₂ : Subgroup A) :
    MulAction ↥G₀ (CosetGeom G₀ G₁ G₂) := inferInstance

@[expose, reducible] def burnsideF45_cosetSMul {A : Type} [Group A] (G₀ G₁ G₂ : Subgroup A) :
    SMul ↥G₀ (CosetGeom G₀ G₁ G₂) := inferInstance

end CosetAct

section Pred

variable {W : Type} (Γ : SimpleGraph W) (X : Type) [Group X] [MulAction X W]

@[expose] def burnsideF45_FaithfulAt (u : W) : Prop :=
  ∀ w, Γ.dist u w = 6 → ∀ t : X, t • u = u → t • w = w → (∀ a, Γ.Adj u a → t • a = a) → t = 1

@[expose] def burnsideF45_TwoAt (u : W) : Prop :=
  ∀ w, Γ.dist u w = 6 → ∀ a c a' c', Γ.Adj u a → Γ.Adj u c → a ≠ c → Γ.Adj u a' →
    Γ.Adj u c' → a' ≠ c' → ∃ t : X, t • u = u ∧ t • w = w ∧ t • a = a' ∧ t • c = c'

@[expose] def burnsideF45_TransAt (u : W) : Prop :=
  ∀ w w', Γ.dist u w = 6 → Γ.dist u w' = 6 → ∃ t : X, t • u = u ∧ t • w = w'

@[expose] def burnsideF45_OutAt (R : Subgroup X) (u : W) : Prop :=
  ∀ w, Γ.dist u w = 6 → ∃ t : X, t • u = u ∧ t • w = w ∧ t ∉ R

@[expose] def burnsideF45_InAt (R : Subgroup X) (u : W) : Prop :=
  ∀ w, Γ.dist u w = 6 → ∀ t : X, t • u = u → t • w = w → t ∈ R

end Pred

structure burnsideF45_HexModel {W : Type} (Γ : SimpleGraph W) (X : Type) [Group X] [MulAction X W]
    (R : Subgroup X) (x₀ l₀ : W) : Prop where
  edge : IsPGroup 2 ↥(MulAction.stabilizer X x₀ ⊓ MulAction.stabilizer X l₀)
  faithx : burnsideF45_FaithfulAt Γ X x₀
  faithl : burnsideF45_FaithfulAt Γ X l₀
  twox : burnsideF45_TwoAt Γ X x₀
  twol : burnsideF45_TwoAt Γ X l₀
  transx : burnsideF45_TransAt Γ X x₀
  transl : burnsideF45_TransAt Γ X l₀
  signx : ∃ w, Γ.dist x₀ w = 6 ∧ ∃ y : X, y • x₀ = x₀ ∧ y • w = w ∧ y ∉ R
  signl : ∃ w, Γ.dist l₀ w = 6 ∧ ∃ y : X, y • l₀ = l₀ ∧ y • w = w ∧ y ≠ 1 ∧ y * y = 1 ∧ y ∈ R
  outer : ∃ y : X, y • x₀ = x₀ ∧ y • l₀ = l₀ ∧ y ∉ R

section Conj

variable {W : Type} {Γ : SimpleGraph W} {X : Type} [Group X] [MulAction X W] [GraphAction X Γ]

theorem burnsideF45_dist_smul_left (hΓ : Γ.Connected) (y : X) (u w : W) :
    Γ.dist (y • u) w = Γ.dist u (y⁻¹ • w) := by
  rw [← GPath.dist_smul hΓ y u (y⁻¹ • w), smul_inv_smul]

theorem burnsideF45_faithfulAt_smul (hΓ : Γ.Connected) {u : W}
    (h : burnsideF45_FaithfulAt Γ X u) (y : X) : burnsideF45_FaithfulAt Γ X (y • u) := by
  intro w hw t htu htw hta
  have h1 : (y⁻¹ * t * y) • u = u := by
    rw [mul_smul, mul_smul, htu, inv_smul_smul]
  have hw' : Γ.dist u (y⁻¹ • w) = 6 := by
    rw [← burnsideF45_dist_smul_left hΓ]; exact hw
  have h2 : (y⁻¹ * t * y) • (y⁻¹ • w) = y⁻¹ • w := by
    rw [mul_smul, mul_smul, smul_inv_smul, htw]
  have h3 : ∀ a, Γ.Adj u a → (y⁻¹ * t * y) • a = a := by
    intro a ha
    have hya : Γ.Adj (y • u) (y • a) := (GraphAction.adj_smul y u a).mpr ha
    rw [mul_smul, mul_smul, hta _ hya, inv_smul_smul]
  have h4 := h _ hw' _ h1 h2 h3
  calc t = y * (y⁻¹ * t * y) * y⁻¹ := by group
    _ = 1 := by rw [h4]; group

theorem burnsideF45_twoAt_smul (hΓ : Γ.Connected) {u : W} (h : burnsideF45_TwoAt Γ X u) (y : X) :
    burnsideF45_TwoAt Γ X (y • u) := by
  intro w hw a c a' c' ha hc hac ha' hc' hac'
  have hw' : Γ.dist u (y⁻¹ • w) = 6 := by
    rw [← burnsideF45_dist_smul_left hΓ]; exact hw
  have hadj : ∀ z, Γ.Adj (y • u) z → Γ.Adj u (y⁻¹ • z) := fun z hz => by
    have := (GraphAction.adj_smul y⁻¹ (y • u) z).mpr hz
    rwa [inv_smul_smul] at this
  have hne : ∀ {z z' : W}, z ≠ z' → y⁻¹ • z ≠ y⁻¹ • z' := fun hzz e =>
    hzz (smul_left_cancel y⁻¹ e)
  obtain ⟨t, htu, htw, hta, htc⟩ := h _ hw' _ _ _ _ (hadj a ha) (hadj c hc) (hne hac)
    (hadj a' ha') (hadj c' hc') (hne hac')
  refine ⟨y * t * y⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [mul_smul, mul_smul, inv_smul_smul, htu]
  · rw [mul_smul, mul_smul, htw, smul_inv_smul]
  · rw [mul_smul, mul_smul, hta, smul_inv_smul]
  · rw [mul_smul, mul_smul, htc, smul_inv_smul]

theorem burnsideF45_outAt_smul (hΓ : Γ.Connected) {R : Subgroup X} (hR : R.Normal) {u : W}
    (h : burnsideF45_OutAt Γ X R u) (y : X) : burnsideF45_OutAt Γ X R (y • u) := by
  intro w hw
  have h1 : Γ.dist u (y⁻¹ • w) = 6 := by rw [← burnsideF45_dist_smul_left hΓ]; exact hw
  obtain ⟨t, htu, htw, htR⟩ := h _ h1
  refine ⟨y * t * y⁻¹, ?_, ?_, fun hmem => htR ?_⟩
  · rw [mul_smul, mul_smul, inv_smul_smul, htu]
  · rw [mul_smul, mul_smul, htw, smul_inv_smul]
  · have := hR.conj_mem _ hmem y⁻¹
    simpa [mul_assoc] using this

theorem burnsideF45_inAt_smul (hΓ : Γ.Connected) {R : Subgroup X} (hR : R.Normal) {u : W}
    (h : burnsideF45_InAt Γ X R u) (y : X) : burnsideF45_InAt Γ X R (y • u) := by
  intro w hw t htu htw
  have h1 : Γ.dist u (y⁻¹ • w) = 6 := by rw [← burnsideF45_dist_smul_left hΓ]; exact hw
  have h2 : (y⁻¹ * t * y) • u = u := by rw [mul_smul, mul_smul, htu, inv_smul_smul]
  have h3 : (y⁻¹ * t * y) • (y⁻¹ • w) = y⁻¹ • w := by
    rw [mul_smul, mul_smul, smul_inv_smul, htw]
  have h4 := h _ h1 _ h2 h3
  have := hR.conj_mem _ h4 y
  simpa [mul_assoc] using this

end Conj

section Three

variable {W : Type}

theorem burnsideF45_mem_three {N : Set W} (hN : N.ncard = 3) {p q r : W} (hp : p ∈ N) (hq : q ∈ N)
    (hr : r ∈ N) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) {z : W} (hz : z ∈ N) :
    z = p ∨ z = q ∨ z = r := by
  have hfin : N.Finite := Set.finite_of_ncard_ne_zero (by rw [hN]; norm_num)
  have hsub : ({p, q, r} : Set W) ⊆ N := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact hp
    · exact hq
    · exact hr
  have hcard : ({p, q, r} : Set W).ncard = 3 := Set.ncard_eq_three.2 ⟨p, q, r, hpq, hpr, hqr, rfl⟩
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hN, hcard]) hfin
  rw [← heq] at hz
  simpa using hz

theorem burnsideF45_eq_of_agree_two {N : Set W} (hN : N.ncard = 3) {f₁ f₂ : W → W}
    (hf₁ : Function.Injective f₁) (hf₂ : Function.Injective f₂) (h₁ : ∀ z ∈ N, f₁ z ∈ N)
    (h₂ : ∀ z ∈ N, f₂ z ∈ N) {a c : W} (ha : a ∈ N) (hc : c ∈ N) (hac : a ≠ c)
    (hfa : f₁ a = f₂ a) (hfc : f₁ c = f₂ c) {z : W} (hz : z ∈ N) : f₁ z = f₂ z := by
  obtain ⟨d, hd, hda, hdc⟩ := CFSG.Quasithin.D4Hex.exists_third (by rw [hN]) a c
  rcases burnsideF45_mem_three hN ha hc hd hac (Ne.symm hda) (Ne.symm hdc) hz with rfl | rfl | rfl
  · exact hfa
  · exact hfc
  · rcases burnsideF45_mem_three hN (h₁ a ha) (h₁ c hc) (h₁ z hd) (hf₁.ne hac)
      (hf₁.ne (Ne.symm hda)) (hf₁.ne (Ne.symm hdc)) (h₂ z hd) with e | e | e
    · exact absurd (hf₂ (e.trans hfa)) hda
    · exact absurd (hf₂ (e.trans hfc)) hdc
    · exact e.symm

end Three

section Card

variable {W : Type} {Γ : SimpleGraph W} {X : Type} [Group X] [MulAction X W] [GraphAction X Γ]

theorem burnsideF45_card_stab_opp {u w : W} (hF : burnsideF45_FaithfulAt Γ X u)
    (hT : burnsideF45_TwoAt Γ X u) (h3 : (Γ.neighborSet u).ncard = 3) (huw : Γ.dist u w = 6) :
    Nat.card ↥(MulAction.stabilizer X u ⊓ MulAction.stabilizer X w) = 6 := by
  set S := MulAction.stabilizer X u ⊓ MulAction.stabilizer X w with hS
  set N := Γ.neighborSet u with hNdef
  have hfin : N.Finite := Set.finite_of_ncard_ne_zero (by rw [h3]; norm_num)
  haveI : Finite ↥N := hfin.to_subtype
  have hsu : ∀ s : S, (s : X) • u = u := fun s => MulAction.mem_stabilizer_iff.mp s.2.1
  have hsw : ∀ s : S, (s : X) • w = w := fun s => MulAction.mem_stabilizer_iff.mp s.2.2
  have hmapsto : ∀ s : S, ∀ a ∈ N, (s : X) • a ∈ N := by
    intro s a ha
    have := (GraphAction.adj_smul (s : X) u a).mpr ha
    rwa [hsu s] at this
  let ρ : S → Equiv.Perm N := fun s =>
    { toFun := fun a => ⟨(s : X) • (a : W), hmapsto s a a.2⟩
      invFun := fun a => ⟨((s⁻¹ : S) : X) • (a : W), hmapsto s⁻¹ a a.2⟩
      left_inv := fun a => Subtype.ext (by
        show ((s⁻¹ : S) : X) • (s : X) • (a : W) = a
        rw [Subgroup.coe_inv, inv_smul_smul])
      right_inv := fun a => Subtype.ext (by
        show (s : X) • ((s⁻¹ : S) : X) • (a : W) = a
        rw [Subgroup.coe_inv, smul_inv_smul]) }
  have hρ : ∀ s : S, ∀ a : N, ((ρ s a : N) : W) = (s : X) • (a : W) := fun _ _ => rfl
  have hinj : Function.Injective ρ := by
    intro s s' hss
    have hfix : ∀ a, Γ.Adj u a → ((s : X)⁻¹ * s') • a = a := by
      intro a ha
      have := congrArg Subtype.val (Equiv.congr_fun hss ⟨a, ha⟩)
      rw [hρ, hρ] at this
      rw [mul_smul, ← this, inv_smul_smul]
    have h1 := hF w huw ((s : X)⁻¹ * s') (by rw [mul_smul, hsu, inv_smul_eq_iff, hsu])
      (by rw [mul_smul, hsw, inv_smul_eq_iff, hsw]) hfix
    apply Subtype.ext
    have : (s : X)⁻¹ * s' = 1 := h1
    rw [inv_mul_eq_one] at this
    exact this
  have hsurj : Function.Surjective ρ := by
    classical
    intro σ
    obtain ⟨a, c, d, hac, had, hcd, hNeq⟩ := Set.ncard_eq_three.1 h3
    have ha : a ∈ N := by rw [hNeq]; simp
    have hc : c ∈ N := by rw [hNeq]; simp
    have hσac : ((σ ⟨a, ha⟩ : N) : W) ≠ ((σ ⟨c, hc⟩ : N) : W) := fun e =>
      hac (congrArg Subtype.val (σ.injective (Subtype.ext e)))
    obtain ⟨t, htu, htw, hta, htc⟩ := hT w huw a c (σ ⟨a, ha⟩) (σ ⟨c, hc⟩) ha hc hac
      (σ ⟨a, ha⟩).2 (σ ⟨c, hc⟩).2 hσac
    let s : S := ⟨t, MulAction.mem_stabilizer_iff.mpr htu, MulAction.mem_stabilizer_iff.mpr htw⟩
    refine ⟨s, Equiv.ext fun z => Subtype.ext ?_⟩
    rw [hρ]
    let f₂ : W → W := fun y => if hy : y ∈ N then ((σ ⟨y, hy⟩ : N) : W) else y
    have hf₂ : ∀ y (hy : y ∈ N), f₂ y = ((σ ⟨y, hy⟩ : N) : W) := fun y hy => dif_pos hy
    have hf₂inj : Function.Injective f₂ := by
      intro y y' hyy
      by_cases hy : y ∈ N <;> by_cases hy' : y' ∈ N
      · rw [hf₂ y hy, hf₂ y' hy'] at hyy
        exact congrArg Subtype.val (σ.injective (Subtype.ext hyy))
      · exfalso
        have h1 : f₂ y ∈ N := by rw [hf₂ y hy]; exact (σ _).2
        have h2 : f₂ y' = y' := dif_neg hy'
        rw [hyy, h2] at h1
        exact hy' h1
      · exfalso
        have h1 : f₂ y' ∈ N := by rw [hf₂ y' hy']; exact (σ _).2
        have h2 : f₂ y = y := dif_neg hy
        rw [← hyy, h2] at h1
        exact hy h1
      · have h1 : f₂ y = y := dif_neg hy
        have h2 : f₂ y' = y' := dif_neg hy'
        rw [h1, h2] at hyy
        exact hyy
    have e := burnsideF45_eq_of_agree_two h3 (f₁ := fun y => t • y) (f₂ := f₂)
      (MulAction.injective t) hf₂inj (fun y hy => hmapsto s y hy)
      (fun y hy => by rw [hf₂ y hy]; exact (σ _).2) ha hc hac (by rw [hf₂ a ha]; exact hta)
      (by rw [hf₂ c hc]; exact htc) z.2
    show t • (z : W) = _
    rw [e, hf₂ z z.2]
  rw [Nat.card_congr (Equiv.ofBijective ρ ⟨hinj, hsurj⟩), Nat.card_perm, Nat.card_coe_set_eq, h3]
  rfl

theorem burnsideF45_card_inf_index_two {R H : Subgroup X} (hR : R.index = 2) (hH : ¬ H ≤ R) :
    2 * Nat.card ↥(R ⊓ H) = Nat.card ↥H := by
  haveI := Subgroup.normal_of_index_eq_two hR
  have hdvd : R.relIndex H ∣ 2 := hR ▸ Subgroup.relIndex_dvd_index_of_normal R H
  have h1 : R.relIndex H ≠ 1 := fun h => hH (Subgroup.relIndex_eq_one.1 h)
  have h2 : R.relIndex H = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd h h1
    · exact h
  have := Subgroup.relIndex_mul_card R H
  rwa [h2] at this

end Card

section Kernel

variable {W : Type} {Γ : SimpleGraph W} {G : Type} [Group G] [MulAction G W] [GraphAction G Γ]

variable (G Γ) in
@[expose] def burnsideF45_g2dKer (u : W) : Subgroup G where
  carrier := {g | g • u = u ∧ ∀ a, Γ.Adj u a → g • a = a}
  one_mem' := ⟨one_smul _ _, fun _ _ => one_smul _ _⟩
  mul_mem' := fun {a b} ha hb =>
    ⟨by rw [mul_smul, hb.1, ha.1], fun w hw => by rw [mul_smul, hb.2 w hw, ha.2 w hw]⟩
  inv_mem' := fun {a} ha =>
    ⟨by rw [inv_smul_eq_iff, ha.1], fun w hw => by rw [inv_smul_eq_iff, ha.2 w hw]⟩

theorem burnsideF45_g2dKer_normalizer (u : W) :
    MulAction.stabilizer G u ≤ Subgroup.normalizer (burnsideF45_g2dKer Γ G u : Set G) := by
  intro h hh
  have hhu : h • u = u := MulAction.mem_stabilizer_iff.mp hh
  have hhu' : h⁻¹ • u = u := by rw [inv_smul_eq_iff, hhu]
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    refine ⟨by rw [mul_smul, mul_smul, hhu', hk.1, hhu], fun a ha => ?_⟩
    have ha' : Γ.Adj u (h⁻¹ • a) := by
      have := (GraphAction.adj_smul h⁻¹ u a).mpr ha
      rwa [hhu'] at this
    rw [mul_smul, mul_smul, hk.2 _ ha', smul_inv_smul]
  · intro hk
    refine ⟨?_, fun a ha => ?_⟩
    · have h1 := hk.1
      rw [mul_smul, mul_smul, hhu'] at h1
      have h2 := congrArg (fun z => h⁻¹ • z) h1
      simp only [inv_smul_smul] at h2
      rw [h2, hhu']
    · have ha' : Γ.Adj u (h • a) := by
        have := (GraphAction.adj_smul h u a).mpr ha
        rwa [hhu] at this
      have h1 := hk.2 _ ha'
      rw [mul_smul, mul_smul, inv_smul_smul] at h1
      have h2 := congrArg (fun z => h⁻¹ • z) h1
      simpa using h2

theorem burnsideF45_g2dKer_le_pCoreOf {p : ℕ} {u a₀ : W} (ha₀ : Γ.Adj u a₀)
    (hp : IsPGroup p ↥(MulAction.stabilizer G u ⊓ MulAction.stabilizer G a₀)) :
    burnsideF45_g2dKer Γ G u ≤ pCoreOf p (MulAction.stabilizer G u) := by
  have hle : burnsideF45_g2dKer Γ G u ≤ MulAction.stabilizer G u := fun g hg =>
    MulAction.mem_stabilizer_iff.mpr hg.1
  have hle' : burnsideF45_g2dKer Γ G u ≤ MulAction.stabilizer G u ⊓ MulAction.stabilizer G a₀ :=
    fun g hg => ⟨MulAction.mem_stabilizer_iff.mpr hg.1, MulAction.mem_stabilizer_iff.mpr (hg.2 a₀ ha₀)⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p hle
    (burnsideF45_g2dKer_normalizer u) (hp.to_le hle')

end Kernel

section HexGeom

variable {W : Type} {Γ : SimpleGraph W}

theorem burnsideF45_exists_opp_nbr (hP : IsGenPolygon Γ 6)
    (h3 : ∀ w, (Γ.neighborSet w).ncard = 3) {l y : W} (hy : Γ.dist l y = 5) :
    ∃ w, Γ.Adj y w ∧ Γ.dist l w = 6 := by
  obtain ⟨c, hc⟩ := hP.bipartite
  obtain ⟨r, hr0, hr5, -⟩ := GPath.exists_geodesic' hP.connected l y hy
  obtain ⟨w, hw, hwne⟩ := CFSG.Quasithin.D4Hex.exists_other (N := Γ.neighborSet y)
    (by rw [h3 y]; norm_num) (r 4)
  have hadj : Γ.Adj y w := hw
  refine ⟨w, hadj, ?_⟩
  rcases GPath.dist_adj_succ_or hP.connected hc l hadj with h | h
  · omega
  · exfalso
    have hd4 : Γ.dist l w = 4 := by omega
    obtain ⟨r', hr'0, hr'4, -⟩ := GPath.exists_geodesic' hP.connected l w hd4
    let s : GPath Γ 5 := r'.snoc y (by rw [hr'4]; exact hadj.symm)
    have hs0 : s 0 = l := by
      show r'.snoc y _ 0 = l
      rw [GPath.snoc_of_le _ _ _ (Nat.zero_le 4), hr'0]
    have hs5 : s 5 = y := GPath.snoc_last _ _ _
    have hs4 : s 4 = w := by
      show r'.snoc y _ 4 = w
      rw [GPath.snoc_of_le _ _ _ le_rfl, hr'4]
    have hsg : s.IsGeodesic := by
      show Γ.dist (s 0) (s 5) = 5
      rw [hs0, hs5]; exact hy
    have hrg : r.IsGeodesic := by
      show Γ.dist (r 0) (r 5) = 5
      rw [hr0, hr5]; exact hy
    have e := hP.uniqueGeod 5 s r hsg hrg (hs0.trans hr0.symm) (hs5.trans hr5.symm) (by norm_num)
    apply hwne
    rw [← hs4, e]

theorem burnsideF45_exists_opp_adj (hP : IsGenPolygon Γ 6)
    (h3 : ∀ w, (Γ.neighborSet w).ncard = 3) {l y : W} (hy : Γ.dist l y = 5) :
    ∃ x, Γ.Adj l x ∧ Γ.dist x y = 6 := by
  obtain ⟨x, hx, hdx⟩ := burnsideF45_exists_opp_nbr hP h3 (l := y) (y := l)
    (by rw [SimpleGraph.dist_comm]; exact hy)
  exact ⟨x, hx, by rw [SimpleGraph.dist_comm]; exact hdx⟩

end HexGeom

section Main

variable {W : Type} {Γ : SimpleGraph W} {G X : Type} [Group G] [Group X] [MulAction G W]
  [MulAction X W] [GraphAction G Γ] [GraphAction X Γ]

structure burnsideF45_G2dHex (Γ : SimpleGraph W) (J : G →* X) (x₀ l₀ : W) : Prop where
  compat : ∀ (g : G) (w : W), J g • w = g • w
  inj : Function.Injective J
  index : J.range.index = 2
  poly : IsGenPolygon Γ 6
  three : ∀ w : W, (Γ.neighborSet w).ncard = 3
  col : ∃ c : W → Bool, (∀ a b, Γ.Adj a b → c a ≠ c b) ∧ (∀ g : G, c (g • x₀) = false) ∧
    ∀ g : G, c (g • l₀) = true
  vert : ∀ w, ∃ g : G, g • x₀ = w ∨ g • l₀ = w
  flag : ∀ u w, Γ.Adj u w → ∃ g : G, (g • x₀ = u ∧ g • l₀ = w) ∨ (g • x₀ = w ∧ g • l₀ = u)
  qfix : ∀ u, ∀ h ∈ pCoreOf 2 (MulAction.stabilizer G u), ∀ a, Γ.Adj u a → h • a = a
  model : burnsideF45_HexModel Γ X J.range x₀ l₀

namespace burnsideF45_G2dHex

variable {J : G →* X} {x₀ l₀ : W} (H : burnsideF45_G2dHex Γ J x₀ l₀)
include H

theorem normal : J.range.Normal := Subgroup.normal_of_index_eq_two H.index

theorem smul_path (g : G) {n : ℕ} (q : GPath Γ n) : J g • q = g • q :=
  GPath.ext' fun i _ => by rw [GPath.smul_apply, GPath.smul_apply, H.compat]

theorem mem_stab_iff (g : G) (u : W) : g ∈ MulAction.stabilizer G u ↔ J g • u = u := by
  rw [MulAction.mem_stabilizer_iff, H.compat]

theorem exists_point {w : W} {c : W → Bool} (hcl : ∀ g : G, c (g • l₀) = true) (hw : c w = false) :
    ∃ g : G, g • x₀ = w := by
  obtain ⟨g, hg | hg⟩ := H.vert w
  · exact ⟨g, hg⟩
  · rw [← hg, hcl] at hw
    exact absurd hw (by decide)

theorem exists_line {w : W} {c : W → Bool} (hcx : ∀ g : G, c (g • x₀) = false) (hw : c w = true) :
    ∃ g : G, g • l₀ = w := by
  obtain ⟨g, hg | hg⟩ := H.vert w
  · rw [← hg, hcx] at hw
    exact absurd hw (by decide)
  · exact ⟨g, hg⟩

theorem point_of_adj_line {u w : W} (hu : ∃ g : G, g • l₀ = u) (hw : Γ.Adj u w) :
    ∃ g' : G, g' • x₀ = w := by
  obtain ⟨c, hc, hcx, hcl⟩ := H.col
  obtain ⟨g, rfl⟩ := hu
  refine H.exists_point hcl ?_
  have h1 := hc _ _ hw
  rw [hcl g] at h1
  cases hcw : c w
  · rfl
  · rw [hcw] at h1
    exact absurd rfl h1

theorem line_of_even {u w : W} (hu : ∃ g : G, g • l₀ = u) (hw : Even (Γ.dist u w)) :
    ∃ g' : G, g' • l₀ = w := by
  obtain ⟨c, hc, hcx, hcl⟩ := H.col
  obtain ⟨g, rfl⟩ := hu
  refine H.exists_line hcx ?_
  have := (GPath.dist_even_iff H.poly.connected hc (g • l₀) w).2 hw
  rw [← this, hcl]

theorem faith_pt {u : W} (hu : ∃ g : G, g • x₀ = u) : burnsideF45_FaithfulAt Γ X u := by
  obtain ⟨g, rfl⟩ := hu
  rw [← H.compat]
  exact burnsideF45_faithfulAt_smul H.poly.connected H.model.faithx (J g)

theorem faith_ln {u : W} (hu : ∃ g : G, g • l₀ = u) : burnsideF45_FaithfulAt Γ X u := by
  obtain ⟨g, rfl⟩ := hu
  rw [← H.compat]
  exact burnsideF45_faithfulAt_smul H.poly.connected H.model.faithl (J g)

theorem two_pt {u : W} (hu : ∃ g : G, g • x₀ = u) : burnsideF45_TwoAt Γ X u := by
  obtain ⟨g, rfl⟩ := hu
  rw [← H.compat]
  exact burnsideF45_twoAt_smul H.poly.connected H.model.twox (J g)

theorem two_ln {u : W} (hu : ∃ g : G, g • l₀ = u) : burnsideF45_TwoAt Γ X u := by
  obtain ⟨g, rfl⟩ := hu
  rw [← H.compat]
  exact burnsideF45_twoAt_smul H.poly.connected H.model.twol (J g)

theorem outAt_x₀ : burnsideF45_OutAt Γ X J.range x₀ := by
  obtain ⟨w₀, hw₀, y₀, hy₀x, hy₀w, hy₀R⟩ := H.model.signx
  intro v hv
  obtain ⟨t, htx, htv⟩ := H.model.transx w₀ v hw₀ hv
  refine ⟨t * y₀ * t⁻¹, ?_, ?_, fun hmem => hy₀R ?_⟩
  · rw [mul_smul, mul_smul, inv_smul_eq_iff.mpr htx.symm, hy₀x, htx]
  · rw [mul_smul, mul_smul, inv_smul_eq_iff.mpr htv.symm, hy₀w, htv]
  · have := H.normal.conj_mem _ hmem t⁻¹
    simpa [mul_assoc] using this

theorem inAt_l₀ : burnsideF45_InAt Γ X J.range l₀ := by
  obtain ⟨w₀, hw₀, z, hzl, hzw, hz1, hzz, hzR⟩ := H.model.signl
  have hS : MulAction.stabilizer X l₀ ⊓ MulAction.stabilizer X w₀ ≤ J.range := by
    by_contra hnot
    have hcard := burnsideF45_card_stab_opp H.model.faithl H.model.twol (H.three l₀) hw₀
    have h2 := burnsideF45_card_inf_index_two H.index hnot
    rw [hcard] at h2
    have hzmem : z ∈ J.range ⊓ (MulAction.stabilizer X l₀ ⊓ MulAction.stabilizer X w₀) :=
      ⟨hzR, MulAction.mem_stabilizer_iff.mpr hzl, MulAction.mem_stabilizer_iff.mpr hzw⟩
    have hord : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hzz) hz1
    have hdvd := orderOf_dvd_natCard (⟨z, hzmem⟩ :
      ↥(J.range ⊓ (MulAction.stabilizer X l₀ ⊓ MulAction.stabilizer X w₀)))
    have e : orderOf (⟨z, hzmem⟩ :
        ↥(J.range ⊓ (MulAction.stabilizer X l₀ ⊓ MulAction.stabilizer X w₀))) = orderOf z :=
      (Subgroup.orderOf_coe _).symm
    rw [e, hord] at hdvd
    omega
  intro v hv t htl htv
  obtain ⟨s, hsl, hsv⟩ := H.model.transl v w₀ hv hw₀
  have hmem : s * t * s⁻¹ ∈ J.range := hS ⟨MulAction.mem_stabilizer_iff.mpr (by
      rw [mul_smul, mul_smul, inv_smul_eq_iff.mpr hsl.symm, htl, hsl]),
    MulAction.mem_stabilizer_iff.mpr (by
      rw [mul_smul, mul_smul, inv_smul_eq_iff.mpr hsv.symm, htv, hsv])⟩
  have := H.normal.conj_mem _ hmem s⁻¹
  simpa [mul_assoc] using this

theorem out_pt {u : W} (hu : ∃ g : G, g • x₀ = u) : burnsideF45_OutAt Γ X J.range u := by
  obtain ⟨g, rfl⟩ := hu
  rw [← H.compat]
  exact burnsideF45_outAt_smul H.poly.connected H.normal H.outAt_x₀ (J g)

theorem in_ln {u : W} (hu : ∃ g : G, g • l₀ = u) : burnsideF45_InAt Γ X J.range u := by
  obtain ⟨g, rfl⟩ := hu
  rw [← H.compat]
  exact burnsideF45_inAt_smul H.poly.connected H.normal H.inAt_l₀ (J g)

theorem card_X_pt {u v : W} (hu : ∃ g : G, g • x₀ = u) (hv : Γ.dist u v = 6) :
    Nat.card ↥(MulAction.stabilizer X u ⊓ MulAction.stabilizer X v) = 6 :=
  burnsideF45_card_stab_opp (H.faith_pt hu) (H.two_pt hu) (H.three u) hv

theorem card_RX_pt {u v : W} (hu : ∃ g : G, g • x₀ = u) (hv : Γ.dist u v = 6) :
    Nat.card ↥(J.range ⊓ (MulAction.stabilizer X u ⊓ MulAction.stabilizer X v)) = 3 := by
  have hnot : ¬ (MulAction.stabilizer X u ⊓ MulAction.stabilizer X v ≤ J.range) := by
    obtain ⟨t, htu, htv, htR⟩ := H.out_pt hu v hv
    exact fun h => htR (h ⟨MulAction.mem_stabilizer_iff.mpr htu, MulAction.mem_stabilizer_iff.mpr htv⟩)
  have := burnsideF45_card_inf_index_two H.index hnot
  rw [H.card_X_pt hu hv] at this
  omega

theorem map_stab_inf (u v : W) :
    (MulAction.stabilizer G u ⊓ MulAction.stabilizer G v).map J =
      J.range ⊓ (MulAction.stabilizer X u ⊓ MulAction.stabilizer X v) := by
  ext y
  constructor
  · rintro ⟨g, ⟨hgu, hgv⟩, rfl⟩
    exact ⟨⟨g, rfl⟩, MulAction.mem_stabilizer_iff.mpr ((H.mem_stab_iff g u).1 hgu),
      MulAction.mem_stabilizer_iff.mpr ((H.mem_stab_iff g v).1 hgv)⟩
  · rintro ⟨⟨g, rfl⟩, hu, hv⟩
    exact ⟨g, ⟨(H.mem_stab_iff g u).2 (MulAction.mem_stabilizer_iff.mp hu),
      (H.mem_stab_iff g v).2 (MulAction.mem_stabilizer_iff.mp hv)⟩, rfl⟩

theorem card_pt {u v : W} (hu : ∃ g : G, g • x₀ = u) (hv : Γ.dist u v = 6) :
    Nat.card ↥(MulAction.stabilizer G u ⊓ MulAction.stabilizer G v) = 3 := by
  rw [← Subgroup.card_map_of_injective H.inj, H.map_stab_inf]
  exact H.card_RX_pt hu hv

theorem point_iso {u v : W} (hu : ∃ g : G, g • x₀ = u) (hv : Γ.dist u v = 6) :
    Nonempty (↥(MulAction.stabilizer G u ⊓ MulAction.stabilizer G v) ≃* Multiplicative (ZMod 3)) := by
  have hc := H.card_pt hu hv
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic ↥(MulAction.stabilizer G u ⊓ MulAction.stabilizer G v) := isCyclic_of_prime_card hc
  exact ⟨mulEquivOfCyclicCardEq (by rw [hc]; simp)⟩

theorem point_trans {u v : W} (hu : ∃ g : G, g • x₀ = u) (hv : Γ.dist u v = 6) {a a' : W}
    (ha : Γ.Adj u a) (ha' : Γ.Adj u a') : ∃ h : G, h • u = u ∧ h • v = v ∧ h • a = a' := by
  by_cases haa : a = a'
  · exact ⟨1, one_smul _ _, one_smul _ _, by rw [one_smul, haa]⟩
  have h3 := H.three u
  obtain ⟨c, hc, hca, hca'⟩ := CFSG.Quasithin.D4Hex.exists_third (N := Γ.neighborSet u)
    (by rw [h3]) a a'
  have hcN : Γ.Adj u c := hc
  obtain ⟨t, htu, htv, hta, htc⟩ := H.two_pt hu v hv a a' a' c ha ha' haa ha' hcN (Ne.symm hca')
  have hmap : ∀ z, Γ.Adj u z → Γ.Adj u (t • z) := fun z hz => by
    have := (GraphAction.adj_smul t u z).mpr hz
    rwa [htu] at this
  have htc' : t • c = a := by
    rcases burnsideF45_mem_three h3 ha ha' hcN haa (Ne.symm hca) (Ne.symm hca') (hmap c hcN) with
      e | e | e
    · exact e
    · exact absurd (MulAction.injective t (e.trans hta.symm)) hca
    · exact absurd (MulAction.injective t (e.trans htc.symm)) hca'
  have hfix : ∀ z, Γ.Adj u z → (t * (t * t)) • z = z := by
    intro z hz
    rcases burnsideF45_mem_three h3 ha ha' hcN haa (Ne.symm hca) (Ne.symm hca') hz with
      rfl | rfl | rfl
    · rw [mul_smul, mul_smul, hta, htc, htc']
    · rw [mul_smul, mul_smul, htc, htc', hta]
    · rw [mul_smul, mul_smul, htc', hta, htc]
  have ht3 : t * (t * t) = 1 :=
    H.faith_pt hu v hv _ (by rw [mul_smul, mul_smul, htu, htu, htu])
      (by rw [mul_smul, mul_smul, htv, htv, htv]) hfix
  have htR : t ∈ J.range := by
    have h4 : t = (t ^ 2) ^ 2 := by
      calc t = t * (t * t) * t := by rw [ht3, one_mul]
        _ = (t ^ 2) ^ 2 := by simp only [sq, mul_assoc]
    rw [h4]
    exact Subgroup.sq_mem_of_index_two H.index _
  obtain ⟨h, rfl⟩ := htR
  exact ⟨h, (H.compat h u).symm.trans htu, (H.compat h v).symm.trans htv,
    (H.compat h a).symm.trans hta⟩

theorem point_invol {u v : W} (hu : ∃ g : G, g • x₀ = u) (hv : Γ.dist u v = 6) {a : W}
    (ha : Γ.Adj u a) : ∃ τ : X, τ • u = u ∧ τ • v = v ∧ τ • a = a ∧ τ ∉ J.range := by
  have h3 := H.three u
  obtain ⟨c, hc, hca, -⟩ := CFSG.Quasithin.D4Hex.exists_third (N := Γ.neighborSet u)
    (by rw [h3]) a a
  obtain ⟨d, hd, hda, hdc⟩ := CFSG.Quasithin.D4Hex.exists_third (N := Γ.neighborSet u)
    (by rw [h3]) a c
  have hcN : Γ.Adj u c := hc
  have hdN : Γ.Adj u d := hd
  obtain ⟨τ, hτu, hτv, hτa, hτc⟩ := H.two_pt hu v hv a c a d ha hcN (Ne.symm hca) ha hdN
    (Ne.symm hda)
  have hmap : ∀ z, Γ.Adj u z → Γ.Adj u (τ • z) := fun z hz => by
    have := (GraphAction.adj_smul τ u z).mpr hz
    rwa [hτu] at this
  have hτd : τ • d = c := by
    rcases burnsideF45_mem_three h3 ha hcN hdN (Ne.symm hca) (Ne.symm hda) (Ne.symm hdc)
      (hmap d hdN) with e | e | e
    · exact absurd (MulAction.injective τ (e.trans hτa.symm)) hda
    · exact e
    · exact absurd (MulAction.injective τ (e.trans hτc.symm)) hdc
  have hfix : ∀ z, Γ.Adj u z → (τ * τ) • z = z := by
    intro z hz
    rcases burnsideF45_mem_three h3 ha hcN hdN (Ne.symm hca) (Ne.symm hda) (Ne.symm hdc) hz with
      rfl | rfl | rfl
    · rw [mul_smul, hτa, hτa]
    · rw [mul_smul, hτc, hτd]
    · rw [mul_smul, hτd, hτc]
  have hτ2 : τ * τ = 1 :=
    H.faith_pt hu v hv _ (by rw [mul_smul, hτu, hτu]) (by rw [mul_smul, hτv, hτv]) hfix
  have hτ1 : τ ≠ 1 := fun h => by
    rw [h, one_smul] at hτc
    exact hdc hτc.symm
  refine ⟨τ, hτu, hτv, hτa, fun hR => ?_⟩
  have hmem : τ ∈ J.range ⊓ (MulAction.stabilizer X u ⊓ MulAction.stabilizer X v) :=
    ⟨hR, MulAction.mem_stabilizer_iff.mpr hτu, MulAction.mem_stabilizer_iff.mpr hτv⟩
  have hord : orderOf τ = 2 := orderOf_eq_prime (by rw [sq]; exact hτ2) hτ1
  have hdvd := orderOf_dvd_natCard (⟨τ, hmem⟩ :
    ↥(J.range ⊓ (MulAction.stabilizer X u ⊓ MulAction.stabilizer X v)))
  have e : orderOf (⟨τ, hmem⟩ :
      ↥(J.range ⊓ (MulAction.stabilizer X u ⊓ MulAction.stabilizer X v))) = orderOf τ :=
    (Subgroup.orderOf_coe _).symm
  rw [e, hord, H.card_RX_pt hu hv] at hdvd
  omega

theorem edge_G {u a : W} (hua : Γ.Adj u a) :
    IsPGroup 2 ↥(MulAction.stabilizer G u ⊓ MulAction.stabilizer G a) := by
  obtain ⟨g, hg⟩ := H.flag u a hua
  rintro ⟨h, hh⟩
  have hhu : J h • u = u := (H.mem_stab_iff h u).1 hh.1
  have hha : J h • a = a := (H.mem_stab_iff h a).1 hh.2
  have hfix : J h • (J g • x₀) = J g • x₀ ∧ J h • (J g • l₀) = J g • l₀ := by
    rw [H.compat g x₀, H.compat g l₀]
    rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact ⟨hhu, hha⟩
    · rw [h1, h2]; exact ⟨hha, hhu⟩
  have hy : (J g)⁻¹ * J h * J g ∈ MulAction.stabilizer X x₀ ⊓ MulAction.stabilizer X l₀ := by
    refine ⟨MulAction.mem_stabilizer_iff.mpr ?_, MulAction.mem_stabilizer_iff.mpr ?_⟩
    · rw [mul_smul, mul_smul, hfix.1, inv_smul_smul]
    · rw [mul_smul, mul_smul, hfix.2, inv_smul_smul]
  obtain ⟨k, hk⟩ := H.model.edge ⟨_, hy⟩
  refine ⟨k, Subtype.ext ?_⟩
  have hk' : ((J g)⁻¹ * J h * J g) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have e : ((J g)⁻¹ * J h * J g) ^ 2 ^ k = (J g)⁻¹ * (J h) ^ 2 ^ k * J g := by
    have := conj_pow (a := (J g)⁻¹) (b := J h) (i := 2 ^ k)
    simpa using this
  rw [e] at hk'
  have h1 : J (h ^ 2 ^ k) = 1 := by
    rw [map_pow]
    have := congrArg (fun z => J g * z * (J g)⁻¹) hk'
    simpa [mul_assoc] using this
  have h2 := H.inj (h1.trans (map_one J).symm)
  simpa using h2

theorem ker_le {u a₀ : W} (ha₀ : Γ.Adj u a₀) :
    burnsideF45_g2dKer Γ G u ≤ pCoreOf 2 (MulAction.stabilizer G u) :=
  burnsideF45_g2dKer_le_pCoreOf ha₀ (H.edge_G ha₀)

theorem complement_line {u v : W} (hu : ∃ g : G, g • l₀ = u) (hv : Γ.dist u v = 6) :
    IsComplementIn (MulAction.stabilizer G u ⊓ MulAction.stabilizer G v)
      (pCoreOf 2 (MulAction.stabilizer G u)) (MulAction.stabilizer G u) := by
  have h3 := H.three u
  obtain ⟨a, ha, -⟩ := CFSG.Quasithin.D4Hex.exists_other (N := Γ.neighborSet u)
    (by rw [h3]; norm_num) u
  obtain ⟨c, hc, hca⟩ := CFSG.Quasithin.D4Hex.exists_other (N := Γ.neighborSet u)
    (by rw [h3]; norm_num) a
  have haN : Γ.Adj u a := ha
  have hcN : Γ.Adj u c := hc
  refine ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 _, inf_le_left, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro h hh
    obtain ⟨hq, hhu, hhv⟩ := hh
    have h1 : J h = 1 := H.faith_ln hu v hv (J h) ((H.mem_stab_iff h u).1 hhu)
      ((H.mem_stab_iff h v).1 hhv) (fun z hz => by rw [H.compat]; exact H.qfix u h hq z hz)
    rw [Subgroup.mem_bot]
    exact H.inj (h1.trans (map_one J).symm)
  · intro g' hg'
    have hg'u : g' • u = u := MulAction.mem_stabilizer_iff.mp hg'
    have hmapg : ∀ z, Γ.Adj u z → Γ.Adj u (g' • z) := fun z hz => by
      have := (GraphAction.adj_smul g' u z).mpr hz
      rwa [hg'u] at this
    obtain ⟨t, htu, htv, hta, htc⟩ := H.two_ln hu v hv a c (g' • a) (g' • c) haN hcN (Ne.symm hca)
      (hmapg a haN) (hmapg c hcN) (fun e => hca (smul_left_cancel g' e).symm)
    obtain ⟨k, rfl⟩ : t ∈ J.range := H.in_ln hu v hv t htu htv
    have hku : k • u = u := (H.compat k u).symm.trans htu
    have hk : k ∈ MulAction.stabilizer G u ⊓ MulAction.stabilizer G v :=
      ⟨(H.mem_stab_iff k u).2 htu, (H.mem_stab_iff k v).2 htv⟩
    have hmapk : ∀ z, Γ.Adj u z → Γ.Adj u (k • z) := fun z hz => by
      have := (GraphAction.adj_smul k u z).mpr hz
      rwa [hku] at this
    have hagree : ∀ z, Γ.Adj u z → g' • z = k • z := fun z hz =>
      burnsideF45_eq_of_agree_two h3 (f₁ := fun y => g' • y) (f₂ := fun y => k • y)
        (MulAction.injective g') (MulAction.injective k) hmapg hmapk haN hcN (Ne.symm hca)
        ((H.compat k a).symm.trans hta).symm ((H.compat k c).symm.trans htc).symm hz
    refine ⟨g' * k⁻¹, ?_, k, hk, by group⟩
    apply H.ker_le haN
    have hku' : k⁻¹ • u = u := by rw [inv_smul_eq_iff, hku]
    refine ⟨by rw [mul_smul, hku', hg'u], fun z hz => ?_⟩
    have hz' : Γ.Adj u (k⁻¹ • z) := by
      have := (GraphAction.adj_smul k⁻¹ u z).mpr hz
      rwa [hku'] at this
    rw [mul_smul, hagree _ hz', smul_inv_smul]

theorem adj_first {a : W} {n : ℕ} (hn : 1 ≤ n) {r : GPath Γ n} (hr : r ∈ GPath.nbPaths Γ a n) :
    Γ.Adj a (r 1) := by
  have := r.adj 0 hn
  rwa [hr.1] at this

theorem pathTrans_x (q q' : GPath Γ 6) (hq : q ∈ GPath.nbPaths Γ x₀ 6)
    (hq' : q' ∈ GPath.nbPaths Γ x₀ 6) : ∃ g : G, g • x₀ = x₀ ∧ g • q = q' := by
  have hx : ∃ g : G, g • x₀ = x₀ := ⟨1, one_smul _ _⟩
  have hv := CFSG.Quasithin.D4Hex.end_dist H.poly le_rfl hq
  have hv' := CFSG.Quasithin.D4Hex.end_dist H.poly le_rfl hq'
  obtain ⟨t, htx, htv⟩ := H.model.transx _ _ hv hv'
  obtain ⟨t', ht'x, ht'v, ht'R⟩ : ∃ t' : X, t' • x₀ = x₀ ∧ t' • q 6 = q' 6 ∧ t' ∈ J.range := by
    by_cases htR : t ∈ J.range
    · exact ⟨t, htx, htv, htR⟩
    · obtain ⟨s, hsx, hsv, hsR⟩ := H.outAt_x₀ (q 6) hv
      refine ⟨t * s, by rw [mul_smul, hsx, htx], by rw [mul_smul, hsv, htv], ?_⟩
      exact (Subgroup.mul_mem_iff_of_index_two H.index).2 (iff_of_false htR hsR)
  obtain ⟨g₁, rfl⟩ := ht'R
  have hg₁x : g₁ • x₀ = x₀ := (H.compat g₁ x₀).symm.trans ht'x
  have hq₁ : g₁ • q ∈ GPath.nbPaths Γ x₀ 6 := CFSG.Quasithin.TitsGeo.smul_mem_nbPaths hq hg₁x
  have hq₁6 : (g₁ • q) 6 = q' 6 := by
    rw [GPath.smul_apply]
    exact (H.compat g₁ _).symm.trans ht'v
  obtain ⟨g₂, hg₂x, hg₂v, hg₂1⟩ := H.point_trans hx hv' (H.adj_first (by norm_num) hq₁)
    (H.adj_first (by norm_num) hq')
  refine ⟨g₂ * g₁, by rw [mul_smul, hg₁x, hg₂x], ?_⟩
  rw [GPath.mul_smul']
  refine CFSG.Quasithin.D4Hex.eq_of_first_last H.poly
    (CFSG.Quasithin.TitsGeo.smul_mem_nbPaths hq₁ hg₂x) hq' ?_ ?_
  · rw [GPath.smul_apply]
    exact hg₂1
  · rw [GPath.smul_apply, hq₁6]
    exact hg₂v

theorem pathTrans_l (q q' : GPath Γ 5) (hq : q ∈ GPath.nbPaths Γ l₀ 5)
    (hq' : q' ∈ GPath.nbPaths Γ l₀ 5) : ∃ g : G, g • l₀ = l₀ ∧ g • q = q' := by
  have hl : ∃ g : G, g • l₀ = l₀ := ⟨1, one_smul _ _⟩
  have hy := CFSG.Quasithin.D4Hex.end_dist H.poly (by norm_num) hq
  have hy' := CFSG.Quasithin.D4Hex.end_dist H.poly (by norm_num) hq'
  obtain ⟨t, htl, hty, htR⟩ : ∃ t : X, t • l₀ = l₀ ∧ t • q 5 = q' 5 ∧ t ∈ J.range := by
    obtain ⟨w, hw, hdw⟩ := burnsideF45_exists_opp_nbr H.poly H.three hy
    obtain ⟨w', hw', hdw'⟩ := burnsideF45_exists_opp_nbr H.poly H.three hy'
    obtain ⟨t₁, ht₁l, ht₁w⟩ := H.model.transl w w' hdw hdw'
    have hw'l : ∃ g : G, g • l₀ = w' := H.line_of_even hl (by rw [hdw']; decide)
    have hdl : Γ.dist w' l₀ = 6 := by rw [SimpleGraph.dist_comm]; exact hdw'
    have hadj1 : Γ.Adj w' (t₁ • q 5) := by
      have := (GraphAction.adj_smul t₁ (q 5) w).mpr hw
      rw [ht₁w] at this
      exact this.symm
    obtain ⟨t₂, ht₂w, ht₂l, ht₂y⟩ := CFSG.Quasithin.D4Hex.trans_of_two
      (by rw [H.three w']; norm_num) (H.two_ln hw'l l₀ hdl) hadj1 hw'.symm
    have h3l : (t₂ * t₁) • l₀ = l₀ := by rw [mul_smul, ht₁l, ht₂l]
    have h3y : (t₂ * t₁) • q 5 = q' 5 := by rw [mul_smul, ht₂y]
    by_cases h3R : t₂ * t₁ ∈ J.range
    · exact ⟨t₂ * t₁, h3l, h3y, h3R⟩
    · obtain ⟨x', hx', hdx'⟩ := burnsideF45_exists_opp_adj H.poly H.three hy'
      have hx'pt := H.point_of_adj_line hl hx'
      obtain ⟨τ, hτx, hτy, hτl, hτR⟩ := H.point_invol hx'pt hdx' hx'.symm
      refine ⟨τ * (t₂ * t₁), by rw [mul_smul, h3l, hτl], by rw [mul_smul, h3y, hτy], ?_⟩
      exact (Subgroup.mul_mem_iff_of_index_two H.index).2 (iff_of_false hτR h3R)
  obtain ⟨g, rfl⟩ := htR
  have hgl : g • l₀ = l₀ := (H.compat g l₀).symm.trans htl
  refine ⟨g, hgl, ?_⟩
  have hgq : g • q ∈ GPath.nbPaths Γ l₀ 5 := CFSG.Quasithin.TitsGeo.smul_mem_nbPaths hq hgl
  obtain ⟨c, hc⟩ := H.poly.bipartite
  have g1 : (g • q).IsGeodesic :=
    GPath.isGeodesic_of_noBack H.poly.connected hc H.poly.uniqueGeod 5 (by norm_num) _ hgq.2
  have g2 : q'.IsGeodesic :=
    GPath.isGeodesic_of_noBack H.poly.connected hc H.poly.uniqueGeod 5 (by norm_num) _ hq'.2
  exact H.poly.uniqueGeod 5 _ _ g1 g2 (hgq.1.trans hq'.1.symm)
    (by rw [GPath.smul_apply]; exact (H.compat g _).symm.trans hty) (by norm_num)

theorem trans_paths_l {q r : GPath Γ 6} (hq : q ∈ GPath.nbPaths Γ l₀ 6)
    (hr : r ∈ GPath.nbPaths Γ l₀ 6) : ∃ y : X, y • l₀ = l₀ ∧ y • q = r := by
  obtain ⟨t₁, ht₁l, ht₁6⟩ := H.model.transl (q 6) (r 6)
    (CFSG.Quasithin.D4Hex.end_dist H.poly le_rfl hq) (CFSG.Quasithin.D4Hex.end_dist H.poly le_rfl hr)
  have hq₁ : t₁ • q ∈ GPath.nbPaths Γ l₀ 6 := CFSG.Quasithin.TitsGeo.smul_mem_nbPaths hq ht₁l
  obtain ⟨t₂, ht₂l, ht₂6, ht₂1⟩ := CFSG.Quasithin.D4Hex.trans_of_two
    (by rw [H.three l₀]; norm_num) (H.model.twol (r 6) (CFSG.Quasithin.D4Hex.end_dist H.poly le_rfl hr))
    (H.adj_first (by norm_num) hq₁) (H.adj_first (by norm_num) hr)
  refine ⟨t₂ * t₁, by rw [mul_smul, ht₁l, ht₂l], ?_⟩
  rw [GPath.mul_smul']
  refine CFSG.Quasithin.D4Hex.eq_of_first_last H.poly
    (CFSG.Quasithin.TitsGeo.smul_mem_nbPaths hq₁ ht₂l) hr ?_ ?_
  · rw [GPath.smul_apply]
    exact ht₂1
  · rw [GPath.smul_apply, GPath.smul_apply, ht₁6]
    exact ht₂6

theorem orbits_l : ∃ q₁ ∈ GPath.nbPaths Γ l₀ 6, ∃ q₂ ∈ GPath.nbPaths Γ l₀ 6,
    GPath.nbPaths Γ l₀ 6 = {r | ∃ g ∈ MulAction.stabilizer G l₀, g • q₁ = r} ∪
      {r | ∃ g ∈ MulAction.stabilizer G l₀, g • q₂ = r} ∧
    Disjoint {r | ∃ g ∈ MulAction.stabilizer G l₀, g • q₁ = r}
      {r | ∃ g ∈ MulAction.stabilizer G l₀, g • q₂ = r} ∧
    Nat.card ↥{r | ∃ g ∈ MulAction.stabilizer G l₀, g • q₁ = r} =
      Nat.card ↥{r | ∃ g ∈ MulAction.stabilizer G l₀, g • q₂ = r} := by
  have hval : ∀ v a b : W, ∃ w, Γ.Adj v w ∧ w ≠ a ∧ w ≠ b := fun v a b => by
    obtain ⟨w, hw, h1, h2⟩ := CFSG.Quasithin.D4Hex.exists_third (N := Γ.neighborSet v)
      (by rw [H.three v]) a b
    exact ⟨w, hw, h1, h2⟩
  obtain ⟨q₁, hq₁⟩ := GPath.exists_nbPaths hval l₀ 6
  obtain ⟨b, -, hbl, hbR⟩ := H.model.outer
  have hq₂ : b • q₁ ∈ GPath.nbPaths Γ l₀ 6 := CFSG.Quasithin.TitsGeo.smul_mem_nbPaths hq₁ hbl
  have hbinv : b⁻¹ ∉ J.range := fun h => hbR (by simpa using J.range.inv_mem h)
  have hconj : ∀ g : G, g • l₀ = l₀ → ∀ s : X, s • l₀ = l₀ →
      ∃ g' : G, g' • l₀ = l₀ ∧ J g' = s * J g * s⁻¹ := by
    intro g hg s hs
    obtain ⟨g', hg'⟩ : s * J g * s⁻¹ ∈ J.range := H.normal.conj_mem _ ⟨g, rfl⟩ s
    refine ⟨g', ?_, hg'⟩
    rw [← H.compat, hg', mul_smul, mul_smul, inv_smul_eq_iff.mpr hs.symm, H.compat, hg, hs]
  refine ⟨q₁, hq₁, b • q₁, hq₂, ?_, ?_, ?_⟩
  · ext r
    constructor
    · intro hr
      obtain ⟨y, hyl, hyr⟩ := H.trans_paths_l hq₁ hr
      by_cases hyR : y ∈ J.range
      · obtain ⟨g, rfl⟩ := hyR
        exact Or.inl ⟨g, (H.mem_stab_iff g l₀).2 hyl, by rw [← H.smul_path]; exact hyr⟩
      · obtain ⟨g, hg⟩ : y * b⁻¹ ∈ J.range :=
          (Subgroup.mul_mem_iff_of_index_two H.index).2 (iff_of_false hyR hbinv)
        refine Or.inr ⟨g, (H.mem_stab_iff g l₀).2 ?_, ?_⟩
        · rw [hg, mul_smul, inv_smul_eq_iff.mpr hbl.symm, hyl]
        · rw [← hyr, ← H.smul_path, hg, ← GPath.mul_smul', inv_mul_cancel_right]
    · rintro (⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩)
      · exact CFSG.Quasithin.TitsGeo.smul_mem_nbPaths hq₁ (MulAction.mem_stabilizer_iff.mp hg)
      · exact CFSG.Quasithin.TitsGeo.smul_mem_nbPaths hq₂ (MulAction.mem_stabilizer_iff.mp hg)
  · rw [Set.disjoint_left]
    rintro r ⟨g₁, hg₁, rfl⟩ ⟨g₂, hg₂, h₂⟩
    have hpt : ∀ i, ((J g₂ * b)⁻¹ * J g₁) • q₁ i = q₁ i := by
      intro i
      have := congrArg (fun r : GPath Γ 6 => r i) h₂
      simp only [GPath.smul_apply] at this
      rw [mul_smul, H.compat g₁, ← this, ← H.compat g₂, inv_smul_eq_iff, mul_smul]
    have hsR : (J g₂ * b)⁻¹ * J g₁ ∈ J.range := H.inAt_l₀ (q₁ 6)
      (CFSG.Quasithin.D4Hex.end_dist H.poly le_rfl hq₁) _ (by have := hpt 0; rwa [hq₁.1] at this)
      (hpt 6)
    apply hbinv
    have e : b⁻¹ = ((J g₂ * b)⁻¹ * J g₁) * (J g₁)⁻¹ * J g₂ := by group
    rw [e]
    exact J.range.mul_mem (J.range.mul_mem hsR (J.range.inv_mem ⟨g₁, rfl⟩)) ⟨g₂, rfl⟩
  · have f : ∀ r ∈ {r | ∃ g ∈ MulAction.stabilizer G l₀, g • q₁ = r},
        b • r ∈ {r | ∃ g ∈ MulAction.stabilizer G l₀, g • (b • q₁) = r} := by
      rintro r ⟨g, hg, rfl⟩
      obtain ⟨g', hg'l, hg'⟩ := hconj g (MulAction.mem_stabilizer_iff.mp hg) b hbl
      refine ⟨g', MulAction.mem_stabilizer_iff.mpr hg'l, GPath.ext' fun i _ => ?_⟩
      simp only [GPath.smul_apply]
      rw [← H.compat g', hg', mul_smul, mul_smul, inv_smul_smul, H.compat]
    have f' : ∀ r ∈ {r | ∃ g ∈ MulAction.stabilizer G l₀, g • (b • q₁) = r},
        b⁻¹ • r ∈ {r | ∃ g ∈ MulAction.stabilizer G l₀, g • q₁ = r} := by
      rintro r ⟨g, hg, rfl⟩
      obtain ⟨g', hg'l, hg'⟩ := hconj g (MulAction.mem_stabilizer_iff.mp hg) b⁻¹
        (inv_smul_eq_iff.mpr hbl.symm)
      refine ⟨g', MulAction.mem_stabilizer_iff.mpr hg'l, GPath.ext' fun i _ => ?_⟩
      simp only [GPath.smul_apply]
      rw [← H.compat g', hg', mul_smul, mul_smul, inv_inv, ← H.compat g]
    exact Nat.card_congr
      { toFun := fun r => ⟨b • r.1, f r.1 r.2⟩
        invFun := fun r => ⟨b⁻¹ • r.1, f' r.1 r.2⟩
        left_inv := fun r => Subtype.ext (by
          show b⁻¹ • b • r.1 = r.1
          rw [← GPath.mul_smul', inv_mul_cancel, GPath.one_smul'])
        right_inv := fun r => Subtype.ext (by
          show b • b⁻¹ • r.1 = r.1
          rw [← GPath.mul_smul', mul_inv_cancel, GPath.one_smul']) }

theorem twoTrans_l {v : W} (hv : Γ.dist l₀ v = 6) {q₁ q₂ r₁ r₂ : GPath Γ 6}
    (hq₁ : q₁ ∈ GPath.nbPaths Γ l₀ 6) (hq₁v : q₁ 6 = v) (hq₂ : q₂ ∈ GPath.nbPaths Γ l₀ 6)
    (hq₂v : q₂ 6 = v) (hq : q₁ ≠ q₂) (hr₁ : r₁ ∈ GPath.nbPaths Γ l₀ 6) (hr₁v : r₁ 6 = v)
    (hr₂ : r₂ ∈ GPath.nbPaths Γ l₀ 6) (hr₂v : r₂ 6 = v) (hr : r₁ ≠ r₂) :
    ∃ g ∈ MulAction.stabilizer G l₀ ⊓ MulAction.stabilizer G v, g • q₁ = r₁ ∧ g • q₂ = r₂ := by
  have hq1 : q₁ 1 ≠ q₂ 1 := fun h =>
    hq (CFSG.Quasithin.D4Hex.eq_of_first_last H.poly hq₁ hq₂ h (hq₁v.trans hq₂v.symm))
  have hr1 : r₁ 1 ≠ r₂ 1 := fun h =>
    hr (CFSG.Quasithin.D4Hex.eq_of_first_last H.poly hr₁ hr₂ h (hr₁v.trans hr₂v.symm))
  obtain ⟨t, htl, htv, ht1, ht2⟩ := H.model.twol v hv _ _ _ _ (H.adj_first (by norm_num) hq₁)
    (H.adj_first (by norm_num) hq₂) hq1 (H.adj_first (by norm_num) hr₁)
    (H.adj_first (by norm_num) hr₂) hr1
  obtain ⟨g, rfl⟩ := H.inAt_l₀ v hv t htl htv
  have hgl : g • l₀ = l₀ := (H.compat g l₀).symm.trans htl
  have hgv : g • v = v := (H.compat g v).symm.trans htv
  refine ⟨g, ⟨MulAction.mem_stabilizer_iff.mpr hgl, MulAction.mem_stabilizer_iff.mpr hgv⟩, ?_, ?_⟩
  · refine CFSG.Quasithin.D4Hex.eq_of_first_last H.poly
      (CFSG.Quasithin.TitsGeo.smul_mem_nbPaths hq₁ hgl) hr₁ ?_ ?_
    · rw [GPath.smul_apply]
      exact (H.compat g _).symm.trans ht1
    · rw [GPath.smul_apply, hq₁v, hgv, hr₁v]
  · refine CFSG.Quasithin.D4Hex.eq_of_first_last H.poly
      (CFSG.Quasithin.TitsGeo.smul_mem_nbPaths hq₂ hgl) hr₂ ?_ ?_
    · rw [GPath.smul_apply]
      exact (H.compat g _).symm.trans ht2
    · rw [GPath.smul_apply, hq₂v, hgv, hr₂v]

end burnsideF45_G2dHex

end Main

end CFSG.ASVolI
