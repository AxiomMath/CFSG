module

public import CFSG.Timmesfeld.Bridge.RootSetsConn17

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G]

theorem exists_index_sq_le [Finite G] {A M : Subgroup G}
    (hAc : ∀ p ∈ A, ∀ q ∈ A, Commute p q) (hA2 : ∀ p ∈ A, p * p = 1) {f : G}
    (hf2 : f * f = 1) (hfA : ∀ p ∈ A, f * p * f⁻¹ ∈ A)
    (hfM : ∀ p ∈ A, p ∈ M → f * p * f⁻¹ ∈ M) :
    ∃ U : Subgroup A, M.subgroupOf A ≤ U ∧
      (∀ p : A, p ∈ U → f * (p : G) * f⁻¹ * (p : G)⁻¹ ∈ M) ∧
        U.index ^ 2 ≤ (M.subgroupOf A).index := by
  have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_right hf2
  let δ : A →* A := MonoidHom.mk'
    (fun p => ⟨f * p * f⁻¹ * (p : G)⁻¹, A.mul_mem (hfA p p.2) (A.inv_mem p.2)⟩) fun p q => by
      apply Subtype.ext
      show f * ((p : G) * q) * f⁻¹ * ((p : G) * q)⁻¹ =
        f * p * f⁻¹ * (p : G)⁻¹ * (f * q * f⁻¹ * (q : G)⁻¹)
      have hc : Commute ((p : G)⁻¹) (f * q * f⁻¹ * (q : G)⁻¹) :=
        hAc _ (A.inv_mem p.2) _ (A.mul_mem (hfA q q.2) (A.inv_mem q.2))
      calc f * ((p : G) * q) * f⁻¹ * ((p : G) * q)⁻¹ =
          f * p * f⁻¹ * ((f * q * f⁻¹ * (q : G)⁻¹) * (p : G)⁻¹) := by group
        _ = f * p * f⁻¹ * ((p : G)⁻¹ * (f * q * f⁻¹ * (q : G)⁻¹)) := by rw [hc.eq]
        _ = _ := by group
  have hδ : ∀ p : A, (δ p : G) = f * p * f⁻¹ * (p : G)⁻¹ := fun p => rfl
  have hMU : M.subgroupOf A ≤ (M.subgroupOf A).comap δ := by
    intro p hp
    rw [Subgroup.mem_subgroupOf] at hp
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hδ]
    exact M.mul_mem (hfM p p.2 hp) (M.inv_mem hp)
  have hrange : δ.range ≤ (M.subgroupOf A).comap δ := by
    rintro _ ⟨p, rfl⟩
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hδ, hδ]
    set r := f * (p : G) * f⁻¹ * (p : G)⁻¹ with hr
    have hr2 : r * r = 1 := hA2 r (A.mul_mem (hfA p p.2) (A.inv_mem p.2))
    have hfr : f * r * f⁻¹ = r⁻¹ := by
      calc f * r * f⁻¹ = f * f * ((p : G) * f⁻¹ * (p : G)⁻¹ * f⁻¹) := by rw [hr]; group
        _ = (p : G) * f * (p : G)⁻¹ * f⁻¹ := by rw [hf2, one_mul, hfi]
        _ = r⁻¹ := by rw [hr]; group
    rw [hfr, ← mul_inv_rev, hr2, inv_one]
    exact M.one_mem
  refine ⟨(M.subgroupOf A).comap δ, hMU, fun p hp => ?_, ?_⟩
  · rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hδ] at hp
    exact hp
  · have h1 : ((M.subgroupOf A).comap δ).index ≤
        (M.subgroupOf A).relIndex ((M.subgroupOf A).comap δ) := by
      rw [Subgroup.index_comap]
      exact Subgroup.relIndex_le_of_le_right hrange
        (by rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
    rw [sq, ← Subgroup.relIndex_mul_index hMU]
    exact Nat.mul_le_mul_right _ h1

theorem exists_mem_not_mem_of_odd [Finite G] {A M : Subgroup G}
    (hAc : ∀ p ∈ A, ∀ q ∈ A, Commute p q) (hA2 : ∀ p ∈ A, p * p = 1) {k : ℕ} (hk : Odd k)
    (hind : (M.subgroupOf A).index = 2 ^ k) {f₁ f₂ : G} (hf₁ : f₁ * f₁ = 1) (hf₂ : f₂ * f₂ = 1)
    (hf₁A : ∀ p ∈ A, f₁ * p * f₁⁻¹ ∈ A) (hf₂A : ∀ p ∈ A, f₂ * p * f₂⁻¹ ∈ A)
    (hf₁M : ∀ p ∈ A, p ∈ M → f₁ * p * f₁⁻¹ ∈ M) (hf₂M : ∀ p ∈ A, p ∈ M → f₂ * p * f₂⁻¹ ∈ M) :
    ∃ p ∈ A, p ∉ M ∧ f₁ * p * f₁⁻¹ * p⁻¹ ∈ M ∧ f₂ * p * f₂⁻¹ * p⁻¹ ∈ M := by
  obtain ⟨U₁, hMU₁, hU₁, hi₁⟩ := exists_index_sq_le hAc hA2 hf₁ hf₁A hf₁M
  obtain ⟨U₂, hMU₂, hU₂, hi₂⟩ := exists_index_sq_le hAc hA2 hf₂ hf₂A hf₂M
  have hpow : ∀ U : Subgroup A, M.subgroupOf A ≤ U → U.index ^ 2 ≤ 2 ^ k →
      U.index ≤ 2 ^ (k / 2) := by
    intro U hMU hi
    obtain ⟨j, -, hj⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two).1 (hind ▸ Subgroup.index_dvd_of_le hMU)
    rw [hj, ← pow_mul] at hi
    rw [hj]
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hi
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlt : (U₁ ⊓ U₂).index < (M.subgroupOf A).index := by
    obtain ⟨r, rfl⟩ := hk
    calc (U₁ ⊓ U₂).index ≤ U₁.index * U₂.index := Subgroup.index_inf_le
      _ ≤ 2 ^ ((2 * r + 1) / 2) * 2 ^ ((2 * r + 1) / 2) :=
        Nat.mul_le_mul (hpow U₁ hMU₁ (hind ▸ hi₁)) (hpow U₂ hMU₂ (hind ▸ hi₂))
      _ < 2 ^ (2 * r + 1) := by
        rw [← pow_add]
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)
      _ = (M.subgroupOf A).index := hind.symm
  by_contra hall
  push Not at hall
  have hle : U₁ ⊓ U₂ ≤ M.subgroupOf A := by
    intro p hp
    rw [Subgroup.mem_subgroupOf]
    by_contra hpM
    exact hall p p.2 hpM (hU₁ p hp.1) (hU₂ p hp.2)
  rw [le_antisymm hle (le_inf hMU₁ hMU₂)] at hlt
  exact lt_irrefl _ hlt

variable {D : Set G}

namespace Step6

variable {a b c x z : G} {P : Subgroup G}

theorem mem_mcore_of_mem_qcore (hB : OddTranspBender) (h3 : Step6ThreeProductHyp)
    (hC : ConnCex D) (h : Step6 D a b c x z P) {p : G} (hp : p ∈ P) (hpQ : p ∈ qcore D x P) :
    p ∈ mcore D x P := by
  have hD := hC.setting.root
  have key : ∀ p ∈ P, p ∈ mcore D x P ∨ ∃ d ∈ D, d ∈ P ∧ d * p ∈ mcore D x P := by
    intro p hp
    rw [h.hPL] at hp
    induction hp using Subgroup.closure_induction with
    | mem y hy =>
      exact Or.inr ⟨y, hy.1, hy.2, by rw [hD.mul_self_eq_one hy.1]; exact one_mem _⟩
    | one => exact Or.inl (one_mem _)
    | mul y w hy hw ihy ihw =>
      rw [← h.hPL] at hy hw
      rcases ihy with hy0 | ⟨d₁, hd₁, hd₁P, h1⟩ <;> rcases ihw with hw0 | ⟨d₂, hd₂, hd₂P, h2⟩
      · exact Or.inl (Subgroup.mul_mem _ hy0 hw0)
      · refine Or.inr ⟨d₂, hd₂, hd₂P, ?_⟩
        rw [show d₂ * (y * w) = y * (d₂ * w) by
          rw [← mul_assoc, (h.commute_of_mem_P hC hd₂P hy).eq, mul_assoc]]
        exact Subgroup.mul_mem _ hy0 h2
      · refine Or.inr ⟨d₁, hd₁, hd₁P, ?_⟩
        rw [← mul_assoc]
        exact Subgroup.mul_mem _ h1 hw0
      · have h12 : d₁ * y * (d₂ * w) ∈ mcore D x P := Subgroup.mul_mem _ h1 h2
        have hc2 : Commute d₂ y := h.commute_of_mem_P hC hd₂P hy
        by_cases hq : d₁ * d₂ ∈ qcore D x P
        · refine Or.inl ?_
          have hdd : d₁ * d₂ ∈ mcore D x P :=
            Subgroup.subset_closure ⟨d₁, hd₁, hd₁P, d₂, hd₂, hd₂P, hq, rfl⟩
          rw [show y * w = (d₁ * d₂)⁻¹ * (d₁ * y * (d₂ * w)) by
            rw [show d₁ * y * (d₂ * w) = d₁ * (y * d₂) * w by group, ← hc2.eq]; group]
          exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hdd) h12
        · obtain ⟨d, hd, hdP, w', hw', hdw⟩ :=
            h.exists_eq_mul_of_mem hB h3 hC (P.mul_mem hd₁P hd₂P) hq
          have hw'M := h.zcore_le_mcore hB hC hw'
          have hw'P : w' ∈ P := by
            have : w' = d⁻¹ * (d₁ * d₂) := by rw [hdw]; group
            rw [this]
            exact P.mul_mem (P.inv_mem hdP) (P.mul_mem hd₁P hd₂P)
          refine Or.inr ⟨d, hd, hdP, ?_⟩
          have e1 : d = d₁ * d₂ * w'⁻¹ := by rw [hdw]; group
          have hc : Commute (d₁ * d₂) w'⁻¹ :=
            h.commute_of_mem_P hC (P.mul_mem hd₁P hd₂P) (P.inv_mem hw'P)
          rw [show d * (y * w) = w'⁻¹ * (d₁ * y * (d₂ * w)) by
            rw [e1, hc.eq, show w'⁻¹ * (d₁ * d₂) * (y * w) = w'⁻¹ * (d₁ * (d₂ * y) * w) by group,
              hc2.eq]
            group]
          exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hw'M) h12
    | inv y hy ihy =>
      rw [← h.hPL] at hy
      rw [inv_eq_of_mul_eq_one_right (h.mul_self_of_mem_P hC hy)]
      exact ihy
  rcases key p hp with hp0 | ⟨d, hd, hdP, hdp⟩
  · exact hp0
  · exfalso
    apply h.not_mem_qcore hC hd
    have := (qcore D x P).mul_mem (mcore_le_qcore hdp) ((qcore D x P).inv_mem hpQ)
    rwa [mul_inv_cancel_right] at this

theorem index_eq_of_sz (hB : OddTranspBender) (hC : ConnCex D) (h : Step6 D a b c x z P)
    {m : ℕ} (hm : 1 ≤ m)
    (e : lsub D x P ⧸ CFSG.solvableRadical (lsub D x P) ≃* CFSG.Theory.Comparator.SzModel m) :
    ((qcore D x P).subgroupOf P).index = 2 ^ (2 * m + 1) := by
  classical
  have := hC.setting.finite
  have hN := hC.setting.normal
  have hD := hC.setting.root
  set X := lsub D x P with hX
  set Q := CFSG.pCore 2 X with hQ
  set π := QuotientGroup.mk' Q with hπ
  have hBX := h.isBenderGroup_pCore hB hC
  obtain ⟨Sb, hSb⟩ := h.exists_sylow_ge hC
  have hmodel : CFSG.Theory.Comparator.SzModel m = CFSG.Open.Sz m := CFSG.Models.benderSzModel_eq_sz m
  let e' : X ⧸ Q ≃* CFSG.Open.Sz m :=
    ((QuotientGroup.quotientMulEquivOfEq (h.solvableRadical_eq_pCore hB hC)).symm.trans e).trans
      (MulEquiv.subgroupCongr hmodel)
  have : Finite (CFSG.Open.Sz m) := Finite.of_surjective e' e'.surjective
  have hFB := (CFSG.Open.bender_suzuki_borel_full m hm).map_mulEquiv e'.symm
  have hZ : Nat.card (Subgroup.center (Sb : Subgroup (X ⧸ Q))) = 2 ^ (2 * m + 1) :=
    (hFB Sb).2.2.2.1
  let ρ : P →* X ⧸ Q := π.comp (Subgroup.inclusion h.le_lsub)
  have hρ : ∀ p : P, ρ p = π ⟨p, h.le_lsub p.2⟩ := fun p => rfl
  have hker : ρ.ker = (qcore D x P).subgroupOf P := by
    ext p
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hρ]
    constructor
    · intro h1
      exact ⟨_, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
    · rintro ⟨q, hq, hqp⟩
      have : (⟨p, h.le_lsub p.2⟩ : X) = q := Subtype.ext hqp.symm
      rw [this]
      exact (QuotientGroup.eq_one_iff _).2 hq
  have hmemS : ∀ y : X, (y : G) ∈ P → π y ∈ Sb := fun y hy => hSb ⟨y, hy, rfl⟩
  have hinv : ∀ y : X, (y : G) ∈ D → π y * π y = 1 := fun y hy => by
    rw [← map_mul, show y * y = 1 from Subtype.ext (hD.mul_self_eq_one hy), map_one]
  have hcen : ∀ w : X ⧸ Q, w ∈ Sb → w * w = 1 → ∀ q ∈ Sb, Commute q w := fun w hw hw2 q hq =>
    (Asc72.IsBenderGroup.commute_of_mul_self_eq_one hBX Sb hw hw2 q hq).symm
  have hrange : ρ.range =
      (Subgroup.center (Sb : Subgroup (X ⧸ Q))).map (Sb : Subgroup (X ⧸ Q)).subtype := by
    apply le_antisymm
    ·
      set C := (Subgroup.center (Sb : Subgroup (X ⧸ Q))).map (Sb : Subgroup (X ⧸ Q)).subtype
      have hPT : P ≤ (C.comap π).map X.subtype := by
        rw [h.hPL, Subgroup.closure_le]
        intro l hl
        set lX : X := ⟨l, mem_lsub_of_mem hl.1 hl.2⟩
        have hlS := hmemS lX hl.2
        refine ⟨lX, ⟨⟨π lX, hlS⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_, rfl⟩, rfl⟩
        exact (hcen _ hlS (hinv lX hl.1) g g.2).eq
      rintro _ ⟨p, rfl⟩
      obtain ⟨y, hy, hyp⟩ := hPT p.2
      have : (⟨p, h.le_lsub p.2⟩ : X) = y := Subtype.ext hyp.symm
      rw [hρ, this]
      exact hy
    ·
      rintro _ ⟨c, hc, rfl⟩
      by_cases hc1 : ((c : X ⧸ Q)) = 1
      · rw [Subgroup.coe_subtype, hc1]
        exact one_mem _
      have hcS : (c : X ⧸ Q) ∈ Sb ∧ ∀ q ∈ Sb, Commute q (c : X ⧸ Q) :=
        ⟨c.2, fun q hq => Subtype.ext_iff.1 (Subgroup.mem_center_iff.1 hc ⟨q, hq⟩)⟩
      set aX : X := ⟨a, mem_lsub_of_mem h.ha h.haP⟩
      have haS : π aX ∈ Sb ∧ ∀ q ∈ Sb, Commute q (π aX) :=
        ⟨hmemS aX h.haP, hcen _ (hmemS aX h.haP) (hinv aX h.ha)⟩
      have ha1 : π aX ≠ 1 := fun h1 =>
        h.not_mem_qcore hC h.ha ⟨aX, (QuotientGroup.eq_one_iff aX).1 h1, rfl⟩
      obtain ⟨gb, -, hgb⟩ := Asc72.IsBenderGroup.exists_normalizer_conj hBX Sb hcS hc1 haS ha1
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Q gb
      set y : X := g⁻¹ * aX * g with hy
      have hyD : (y : G) ∈ D := by
        have := hN (g⁻¹ : X) a h.ha
        simpa [hy] using this
      have hgb' : π g * c * (π g)⁻¹ = π aX := hgb
      have hπy : π y = c := by
        rw [hy, map_mul, map_mul, map_inv, ← hgb']
        group
      have hyP : (y : G) ∈ P := h.mem_of_mem_sylow hC hSb hyD (hπy ▸ c.2)
      refine ⟨⟨y, hyP⟩, ?_⟩
      rw [hρ, Subgroup.coe_subtype]
      exact hπy
  rw [← hker, Subgroup.index_ker, hrange,
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hZ]

theorem exists_mul_eq_of_commute (hB : OddTranspBender) (h3 : Step6ThreeProductHyp)
    (hC : ConnCex D) (h : Step6 D a b c x z P) {f : G} (hf : f ∈ D)
    (hfN : f ∈ Subgroup.normalizer (P : Set G)) (hfP : f ∉ P) {ℓ ℓ' : G} (hℓ : ℓ ∈ D)
    (hℓ' : ℓ' ∈ D) (hℓP : ℓ ∈ P) (hℓ'P : ℓ' ∈ P) (hfℓ : Commute f ℓ) (hfℓ' : Commute f ℓ')
    {α : G} (hα : α ∈ D) (hαP : α ∈ P) (hq : ℓ * α ∈ qcore D x P) :
    ∃ u ∈ D, u ∈ P ∧ ℓ' * u ∈ qcore D x P ∧ ℓ * α = ℓ' * u := by
  have hD := hC.setting.root
  obtain ⟨u, hu, huP, w, hw, heq⟩ := h3 G D a b c x z P hC h ℓ hℓ hℓP ℓ' hℓ' hℓ'P α hα hαP hq
  obtain ⟨w', hw', hw'w⟩ := hw
  have hwQ : w ∈ qcore D x P := ⟨w', hw'.2, hw'w⟩
  have hu_eq : u = ℓ * ℓ' * α * w⁻¹ := by rw [heq]; group
  have hℓ'u : ℓ' * u = ℓ * α * w⁻¹ := by
    rw [hu_eq, show ℓ' * (ℓ * ℓ' * α * w⁻¹) = ℓ' * (ℓ * ℓ') * α * w⁻¹ by group,
      (h.commute_of_mem_P hC hℓP hℓ'P).eq,
      show ℓ' * (ℓ' * ℓ) * α * w⁻¹ = ℓ' * ℓ' * ℓ * α * w⁻¹ by group, hD.mul_self_eq_one hℓ',
      one_mul]
  have hℓ'uQ : ℓ' * u ∈ qcore D x P := by
    rw [hℓ'u]
    exact (qcore D x P).mul_mem hq ((qcore D x P).inv_mem hwQ)
  have hfα := h.commute_of_mul_mem_qcore hB h3 hC hf hfN hℓ hℓP hfℓ hα hαP
    (mul_mem_qcore_comm hC hℓ hα hq)
  have hfu := h.commute_of_mul_mem_qcore hB h3 hC hf hfN hℓ' hℓ'P hfℓ' hu huP
    (mul_mem_qcore_comm hC hℓ' hu hℓ'uQ)
  have hfw : Commute f w := by
    rw [show w = u⁻¹ * (ℓ * ℓ' * α) by rw [heq]; group]
    exact hfu.inv_right.mul_right ((hfℓ.mul_right hfℓ').mul_right hfα)
  rw [← hw'w] at hfw
  have hw1 := h.eq_one_of_commute_center hC hf hfN hfP hw'.1 hfw
  refine ⟨u, hu, huP, hℓ'uQ, ?_⟩
  rw [hℓ'u, ← hw'w, hw1, map_one, inv_one, mul_one]

theorem exists_commute_commute (hB : OddTranspBender) (h3 : Step6ThreeProductHyp)
    (hC : ConnCex D) (h : Step6 D a b c x z P) {k : ℕ} (hk : Odd k)
    (hind : ((qcore D x P).subgroupOf P).index = 2 ^ k) {f₁ f₂ : G} (hf₁ : f₁ ∈ D)
    (hf₁N : f₁ ∈ Subgroup.normalizer (P : Set G)) (hf₂ : f₂ ∈ D)
    (hf₂N : f₂ ∈ Subgroup.normalizer (P : Set G)) :
    ∃ γ ∈ D, γ ∈ P ∧ Commute f₁ γ ∧ Commute f₂ γ := by
  have := hC.setting.finite
  have hD := hC.setting.root
  have hN := hC.setting.normal
  have hfM : ∀ {f : G}, f ∈ Subgroup.normalizer (P : Set G) → ∀ p ∈ P, p ∈ qcore D x P →
      f * p * f⁻¹ ∈ qcore D x P := fun hfN p hp hpQ =>
    mcore_le_qcore (h.conj_mem_mcore hB h3 hC hfN (h.mem_mcore_of_mem_qcore hB h3 hC hp hpQ))
  have hfP : ∀ {f : G}, f ∈ Subgroup.normalizer (P : Set G) → ∀ p ∈ P, f * p * f⁻¹ ∈ P :=
    fun hfN p hp => (Subgroup.mem_normalizer_iff.1 hfN p).1 hp
  obtain ⟨p, hp, hpQ, hp₁, hp₂⟩ := exists_mem_not_mem_of_odd (A := P) (M := qcore D x P)
    (fun p hp q hq => h.commute_of_mem_P hC hp hq) (fun p hp => h.mul_self_of_mem_P hC hp) hk
    hind (hD.mul_self_eq_one hf₁) (hD.mul_self_eq_one hf₂) (hfP hf₁N) (hfP hf₂N) (hfM hf₁N)
    (hfM hf₂N)
  obtain ⟨γ, hγ, hγP, w, hw, hpγ⟩ := h.exists_eq_mul_of_mem hB h3 hC hp hpQ
  have hwP : w ∈ P := by
    rw [show w = γ⁻¹ * p by rw [hpγ]; group]
    exact P.mul_mem (P.inv_mem hγP) hp
  have hwQ := zcore_le_qcore hw
  have hcomm : ∀ {f : G}, f ∈ D → f ∈ Subgroup.normalizer (P : Set G) →
      f * p * f⁻¹ * p⁻¹ ∈ qcore D x P → Commute f γ := by
    intro f hf hfN hfp
    have h1 : f * w⁻¹ * f⁻¹ ∈ qcore D x P :=
      hfM hfN _ (P.inv_mem hwP) ((qcore D x P).inv_mem hwQ)
    have hc : Commute p⁻¹ (f * w⁻¹ * f⁻¹ * w) :=
      h.commute_of_mem_P hC (P.inv_mem hp) (P.mul_mem (hfP hfN _ (P.inv_mem hwP)) hwP)
    have hmem : f * γ * f⁻¹ * γ⁻¹ ∈ qcore D x P := by
      rw [show γ = p * w⁻¹ by rw [hpγ]; group,
        show f * (p * w⁻¹) * f⁻¹ * (p * w⁻¹)⁻¹ = f * p * f⁻¹ * ((f * w⁻¹ * f⁻¹ * w) * p⁻¹) by
          group, ← hc.eq, ← mul_assoc]
      exact (qcore D x P).mul_mem hfp ((qcore D x P).mul_mem h1 hwQ)
    rw [hD.inv_eq hγ] at hmem
    exact h.commute_of_mul_conj_mem_qcore hC hf hfN hγ hγP
      (mul_mem_qcore_comm hC (hN f γ hγ) hγ hmem)
  exact ⟨γ, hγ, hγP, hcomm hf₁ hf₁N hp₁, hcomm hf₂ hf₂N hp₂⟩

theorem false_of_sz (hB : OddTranspBender) (hC : ConnCex D) (h : Step6 D a b c x z P) {m : ℕ}
    (hm : 1 ≤ m)
    (e : lsub D x P ⧸ CFSG.solvableRadical (lsub D x P) ≃* CFSG.Theory.Comparator.SzModel m) :
    False := by
  have h3 := step6ThreeProductHyp hB OddTransp.oddTranspThirdKind
  have hind := h.index_eq_of_sz hB hC hm e
  have hk : Odd (2 * m + 1) := odd_two_mul_add_one m
  obtain ⟨fa, hfa, hfaN, hfaP, hfaa⟩ := h.exists_mem_normalizer_commute hB h3 hC h.ha h.haP
  have hgen : mcore D x P ≤ Subgroup.centralizer {fa} := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨d, hd, hdP, e', he', he'P, hq, rfl⟩
    obtain ⟨fd, hfd, hfdN, hfdP, hfdd⟩ := h.exists_mem_normalizer_commute hB h3 hC hd hdP
    obtain ⟨γ, hγ, hγP, hfdγ, hfaγ⟩ :=
      h.exists_commute_commute hB h3 hC hk hind hfd hfdN hfa hfaN
    obtain ⟨u, hu, huP, hγu, hdu⟩ :=
      h.exists_mul_eq_of_commute hB h3 hC hfd hfdN hfdP hd hγ hdP hγP hfdd hfdγ he' he'P hq
    obtain ⟨u', hu', hu'P, hau', hγu'⟩ :=
      h.exists_mul_eq_of_commute hB h3 hC hfa hfaN hfaP hγ h.ha hγP h.haP hfaγ hfaa hu huP hγu
    have hfau' := h.commute_of_mul_mem_qcore hB h3 hC hfa hfaN h.ha h.haP hfaa hu' hu'P
      (mul_mem_qcore_comm hC h.ha hu' hau')
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, hdu, hγu']
    exact (hfaa.mul_right hfau').eq.symm
  have hz := hgen (h.zcore_le_mcore hB hC
    ⟨⟨z, h.z_mem_lsub⟩, ⟨h.z_mem_center, h.z_mem_pCore hC⟩, rfl⟩)
  rw [Subgroup.mem_centralizer_singleton_iff] at hz
  exact h.hz1 (congrArg Subtype.val
    (h.eq_one_of_commute_center hC hfa hfaN hfaP h.z_mem_center hz.symm))

end Step6

end CFSG.Timmesfeld.Bridge
