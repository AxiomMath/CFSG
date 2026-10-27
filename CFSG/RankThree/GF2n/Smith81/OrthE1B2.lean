module

public import CFSG.RankThree.GF2n.Smith81.OrthE1Small
public import CFSG.RankThree.GF2n.Smith81.OrthE1B7a
public import CFSG.RankThree.GF2n.Smith81.Sec220Conj

public section

open scoped commutatorElement

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

section B2Generic

theorem b2_charP_two {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) : CharP K 2 := by
  haveI := Fintype.ofFinite K
  obtain ⟨m, hm, hKm⟩ := FiniteField.card K (ringChar K)
  have hdvd : ringChar K ∣ 2 ^ n := by
    rw [← hK, Nat.card_eq_fintype_card, hKm]
    exact dvd_pow_self _ (by have := m.pos; omega)
  have hp2 : ringChar K = 2 :=
    (Nat.prime_dvd_prime_iff_eq hm Nat.prime_two).mp (hm.dvd_of_dvd_pow hdvd)
  have : CharP K (ringChar K) := ringChar.charP K
  rw [hp2] at this
  exact this

theorem b2_sl_facts {X : Type} [Group X] {q n : ℕ} (hX : IsSLModel 2 q X) (hq : q = 2 ^ n)
    (h4 : 4 ≤ q) :
    Nat.card X = q * (q ^ 2 - 1) ∧ IsSimpleGroup X ∧
      ∀ x : X, (∀ y : X, Commute x y) → x = 1 := by
  obtain ⟨K, hKf, hfin, hcard, ⟨e⟩⟩ := hX
  have hchar : CharP K 2 := b2_charP_two (hcard.trans hq)
  have h4K : 4 ≤ Nat.card K := hcard ▸ h4
  have hquasi := statedSL_quasisimple_of_card 2 K le_rfl h4K
  have hsimp : IsSimpleGroup (StatedSL 2 K) := isSimpleGroup_statedSL_two hquasi
  refine ⟨?_, e.isSimpleGroup, ?_⟩
  · rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two, hcard]
  · intro x hx
    have hz : e x ∈ Subgroup.center (StatedSL 2 K) := by
      refine Subgroup.mem_center_iff.mpr fun g => ?_
      have hc := hx (e.symm g)
      have := congrArg e hc
      simpa using this.symm
    rw [center_statedSL_two_eq_bot, Subgroup.mem_bot] at hz
    exact e.injective (by rw [hz, map_one])

theorem b2_sl_card {G : Type} [Group G] {S Q : Subgroup G} {q n : ℕ}
    (hQS : Q ≤ S) (hS : QuotSat S Q (IsSLModel 2 q)) (hq : q = 2 ^ n) (h4 : 4 ≤ q) :
    Nat.card S = Nat.card Q * (q * (q ^ 2 - 1)) := by
  obtain ⟨hN, hX⟩ := hS
  haveI := hN
  have h := (b2_sl_facts hX hq h4).1
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Q.subgroupOf S)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQS).toEquiv] at h1
  rw [h1, h, mul_comm]

theorem b2_sl_center_elem {G : Type} [Group G] {S Q : Subgroup G} {q n : ℕ}
    (hS : QuotSat S Q (IsSLModel 2 q)) (hq : q = 2 ^ n) (h4 : 4 ≤ q)
    {x : G} (hx : x ∈ S) (hc : ∀ y ∈ S, ⁅x, y⁆ ∈ Q) : x ∈ Q := by
  obtain ⟨hN, hX⟩ := hS
  haveI := hN
  have hcen := (b2_sl_facts hX hq h4).2.2
  have key := hcen (QuotientGroup.mk' (Q.subgroupOf S) ⟨x, hx⟩) (fun w => by
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf S) w
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
    refine (QuotientGroup.eq_one_iff _).mpr ?_
    rw [Subgroup.mem_subgroupOf]
    simpa [commutatorElement_def] using hc y hy)
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp key)

theorem b2_sl_dich {G : Type} [Group G] {F Q H : Subgroup G} (hQF : Q ≤ F)
    (hN : (Q.subgroupOf F).Normal) (hS : IsSimpleGroup (↥F ⧸ Q.subgroupOf F))
    (hQH : Q ≤ H) (hHF : H ≤ F) (hH : ∀ f ∈ F, ∀ h ∈ H, f * h * f⁻¹ ∈ H) : H = Q ∨ H = F := by
  haveI := hN
  haveI := hS
  have hHn : (H.subgroupOf F).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hHF]
    intro h k hh hk
    exact hH k hk h hh
  haveI := hHn.map (QuotientGroup.mk' (Q.subgroupOf F)) (QuotientGroup.mk'_surjective _)
  rcases Subgroup.Normal.eq_bot_or_eq_top
      ((H.subgroupOf F).map (QuotientGroup.mk' (Q.subgroupOf F))) with hb | ht
  · left
    refine le_antisymm (fun h hh => ?_) hQH
    have hF : h ∈ F := hHF hh
    have hmem := Subgroup.mem_map_of_mem (QuotientGroup.mk' (Q.subgroupOf F))
      (Subgroup.mem_subgroupOf.mpr hh : (⟨h, hF⟩ : ↥F) ∈ H.subgroupOf F)
    rw [hb, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hmem)
  · right
    refine le_antisymm hHF (fun f hf => ?_)
    have hmem : QuotientGroup.mk' (Q.subgroupOf F) (⟨f, hf⟩ : ↥F) ∈
        (H.subgroupOf F).map (QuotientGroup.mk' (Q.subgroupOf F)) := by
      rw [ht]
      exact Subgroup.mem_top _
    obtain ⟨h', hh', he⟩ := Subgroup.mem_map.mp hmem
    have hrel : h'⁻¹ * (⟨f, hf⟩ : ↥F) ∈ Q.subgroupOf F := (QuotientGroup.eq).mp he
    have hfQ : (h' : G)⁻¹ * f ∈ Q := Subgroup.mem_subgroupOf.mp hrel
    have key : (h' : G) * ((h' : G)⁻¹ * f) ∈ H :=
      H.mul_mem (Subgroup.mem_subgroupOf.mp hh') (hQH hfQ)
    simpa using key

theorem b2_sup_decomp {G : Type} [Group G] (R₀ S T : Subgroup G) (hS : S ≤ R₀) (hT : T ≤ R₀)
    (hSn : ∀ r ∈ R₀, ∀ s ∈ S, r * s * r⁻¹ ∈ S) (hTn : ∀ r ∈ R₀, ∀ t ∈ T, r * t * r⁻¹ ∈ T)
    (x : G) (hx : x ∈ S ⊔ T) : ∃ s ∈ S, ∃ t ∈ T, s * t = x := by
  let U : Subgroup G :=
    { carrier := {x | ∃ s ∈ S, ∃ t ∈ T, s * t = x}
      mul_mem' := by
        rintro _ _ ⟨s₁, hs₁, t₁, ht₁, rfl⟩ ⟨s₂, hs₂, t₂, ht₂, rfl⟩
        exact ⟨s₁ * (t₁ * s₂ * t₁⁻¹), S.mul_mem hs₁ (hSn t₁ (hT ht₁) s₂ hs₂), t₁ * t₂,
          T.mul_mem ht₁ ht₂, by group⟩
      one_mem' := ⟨1, S.one_mem, 1, T.one_mem, by group⟩
      inv_mem' := by
        rintro _ ⟨s, hs, t, ht, rfl⟩
        exact ⟨t⁻¹ * s⁻¹ * t⁻¹⁻¹, hSn t⁻¹ (R₀.inv_mem (hT ht)) s⁻¹ (S.inv_mem hs), t⁻¹,
          T.inv_mem ht, by group⟩ }
  have hle : S ⊔ T ≤ U :=
    sup_le (fun s hs => ⟨s, hs, 1, T.one_mem, mul_one s⟩)
      (fun t ht => ⟨1, S.one_mem, t, ht, one_mul t⟩)
  obtain ⟨s, hs, t, ht, h⟩ := hle hx
  exact ⟨s, hs, t, ht, h⟩

theorem b2_one_sided {K : Type} [Group K] [Finite K] (A C F Q₀ : Subgroup K)
    [hA : A.Normal] [hC : C.Normal] (hAC : A ⊔ C = ⊤) (hAC' : A ⊓ C = Q₀) (hQF : Q₀ ≤ F)
    (hFA : F ⊓ A = Q₀) (hcard : Nat.card F = Nat.card C)
    (hZ : ∀ c ∈ C, (∀ c' ∈ C, ⁅c, c'⁆ ∈ Q₀) → c ∈ Q₀) (x : K)
    (hx : ∀ f ∈ F, ⁅f, x⁆ ∈ Q₀) : x ∈ A := by
  classical
  have hQA : Q₀ ≤ A := hAC' ▸ inf_le_left
  have hQC : Q₀ ≤ C := hAC' ▸ inf_le_right
  set p : K →* K ⧸ A := QuotientGroup.mk' A with hp
  set φ : ↥F →* K ⧸ A := p.comp F.subtype with hφ
  set ψ : ↥C →* K ⧸ A := p.comp C.subtype with hψ
  have hkerφ : φ.ker = Q₀.subgroupOf F := by
    ext ⟨f, hf⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h' : f ∈ A := (QuotientGroup.eq_one_iff f).mp h
      have : f ∈ F ⊓ A := ⟨hf, h'⟩
      rw [hFA] at this
      exact this
    · intro h
      exact (QuotientGroup.eq_one_iff f).mpr (hQA h)
  have hkerψ : ψ.ker = Q₀.subgroupOf C := by
    ext ⟨c, hc⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h' : c ∈ A := (QuotientGroup.eq_one_iff c).mp h
      have : c ∈ A ⊓ C := ⟨h', hc⟩
      rw [hAC'] at this
      exact this
    · intro h
      exact (QuotientGroup.eq_one_iff c).mpr (hQA h)
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective A y
    have hk : k ∈ A ⊔ C := by rw [hAC]; exact Subgroup.mem_top k
    obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hk
    refine ⟨⟨c, hc⟩, ?_⟩
    have hpa : p a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
    show p c = p (a * c)
    rw [map_mul, hpa, one_mul]
  have hm : 0 < Nat.card Q₀ := Nat.card_pos
  have hsurjφ : φ.range = ⊤ := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
    have hφk : Nat.card φ.ker = Nat.card Q₀ := by
      rw [hkerφ]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQF).toEquiv
    have hψk : Nat.card ψ.ker = Nat.card Q₀ := by
      rw [hkerψ]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv
    rw [hφk] at h1
    rw [hψk] at h2
    have hab : Nat.card (↥F ⧸ φ.ker) = Nat.card (↥C ⧸ ψ.ker) := by
      have h3 : Nat.card (↥F ⧸ φ.ker) * Nat.card Q₀ = Nat.card (↥C ⧸ ψ.ker) * Nat.card Q₀ := by
        rw [← h1, ← h2, hcard]
      exact Nat.eq_of_mul_eq_mul_right hm h3
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv.symm, hab,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj).toEquiv]
  have hcomm : ∀ k : K, ⁅x, k⁆ ∈ A := by
    intro k
    have hpk : p k ∈ φ.range := by rw [hsurjφ]; exact Subgroup.mem_top _
    obtain ⟨f, hf⟩ := MonoidHom.mem_range.mp hpk
    have hfA : ⁅(f : K), x⁆ ∈ A := hQA (hx f f.2)
    have h2 : p ⁅(f : K), x⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hfA
    have h4 : ⁅x, (f : K)⁆ = ⁅(f : K), x⁆⁻¹ := (commutatorElement_inv _ _).symm
    have hpf : p (f : K) = p k := hf
    have h1 : p ⁅x, k⁆ = 1 := by
      rw [map_commutatorElement, ← hpf, ← map_commutatorElement, h4, map_inv, h2, inv_one]
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hxsup : x ∈ A ⊔ C := by rw [hAC]; exact Subgroup.mem_top x
  obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hxsup
  have hcQ : c ∈ Q₀ := hZ c hc (fun c' hc' => by
    have hA' : ⁅c, c'⁆ ∈ A := by
      have e1 : ⁅c, c'⁆ = a⁻¹ * ⁅a * c, c'⁆ * (c' * a * c'⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e1]
      exact A.mul_mem (A.mul_mem (A.inv_mem ha) (hcomm c')) (hA.conj_mem a ha c')
    have hC' : ⁅c, c'⁆ ∈ C :=
      C.mul_mem (C.mul_mem (C.mul_mem hc hc') (C.inv_mem hc)) (C.inv_mem hc')
    have hmem : ⁅c, c'⁆ ∈ A ⊓ C := ⟨hA', hC'⟩
    rwa [hAC'] at hmem)
  exact A.mul_mem ha (hQA hcQ)

theorem b2_diag_core {K : Type} [Group K] [Finite K] (A C F Q₀ : Subgroup K)
    [A.Normal] [C.Normal] (hAC : A ⊔ C = ⊤) (hAC' : A ⊓ C = Q₀) (hQF : Q₀ ≤ F)
    (hFA : F ⊓ A = Q₀) (hFC : F ⊓ C = Q₀) (hcC : Nat.card F = Nat.card C)
    (hcA : Nat.card F = Nat.card A)
    (hZA : ∀ a ∈ A, (∀ a' ∈ A, ⁅a, a'⁆ ∈ Q₀) → a ∈ Q₀)
    (hZC : ∀ c ∈ C, (∀ c' ∈ C, ⁅c, c'⁆ ∈ Q₀) → c ∈ Q₀) (x : K)
    (hx : ∀ f ∈ F, ⁅f, x⁆ ∈ Q₀) : x ∈ Q₀ := by
  have hxA : x ∈ A := b2_one_sided A C F Q₀ hAC hAC' hQF hFA hcC hZC x hx
  have hxC : x ∈ C :=
    b2_one_sided C A F Q₀ (by rw [sup_comm]; exact hAC) (by rw [inf_comm]; exact hAC') hQF hFC
      hcA hZA x hx
  have hmem : x ∈ A ⊓ C := ⟨hxA, hxC⟩
  rwa [hAC'] at hmem

theorem b2_diag_G {G : Type} [Group G] [Finite G] {X' A C F Q₀ : Subgroup G}
    (hAX : A ≤ X') (hCX : C ≤ X') (hFX : F ≤ X') (hQ₀F : Q₀ ≤ F)
    (hAn : ∀ r ∈ X', ∀ a ∈ A, r * a * r⁻¹ ∈ A) (hCn : ∀ r ∈ X', ∀ c ∈ C, r * c * r⁻¹ ∈ C)
    (hsup : A ⊔ C = X') (hint : A ⊓ C = Q₀) (hFA : F ⊓ A = Q₀) (hFC : F ⊓ C = Q₀)
    (hcC : Nat.card F = Nat.card C) (hcA : Nat.card F = Nat.card A)
    (hZA : ∀ a ∈ A, (∀ a' ∈ A, ⁅a, a'⁆ ∈ Q₀) → a ∈ Q₀)
    (hZC : ∀ c ∈ C, (∀ c' ∈ C, ⁅c, c'⁆ ∈ Q₀) → c ∈ Q₀) {x : G} (hxX : x ∈ X')
    (hx : ∀ f ∈ F, ⁅f, x⁆ ∈ Q₀) : x ∈ Q₀ := by
  haveI hA1 : (A.subgroupOf X').Normal :=
    (Subgroup.normal_subgroupOf_iff hAX).mpr fun h k hh hk => hAn k hk h hh
  haveI hC1 : (C.subgroupOf X').Normal :=
    (Subgroup.normal_subgroupOf_iff hCX).mpr fun h k hh hk => hCn k hk h hh
  have hsup1 : A.subgroupOf X' ⊔ C.subgroupOf X' = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨k, hk⟩ -
    have hk' : k ∈ A ⊔ C := by rw [hsup]; exact hk
    obtain ⟨a, ha, c, hc, hac⟩ := b2_sup_decomp X' A C hAX hCX hAn hCn k hk'
    have e : (⟨k, hk⟩ : ↥X') = (⟨a, hAX ha⟩ : ↥X') * ⟨c, hCX hc⟩ := Subtype.ext (by simp [← hac])
    rw [e]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mpr ha) (Subgroup.mem_subgroupOf.mpr hc)
  have hint1 : A.subgroupOf X' ⊓ C.subgroupOf X' = Q₀.subgroupOf X' := by
    ext ⟨k, hk⟩
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, ← Subgroup.mem_inf, hint]
  have hFA1 : F.subgroupOf X' ⊓ A.subgroupOf X' = Q₀.subgroupOf X' := by
    ext ⟨k, hk⟩
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, ← Subgroup.mem_inf, hFA]
  have hFC1 : F.subgroupOf X' ⊓ C.subgroupOf X' = Q₀.subgroupOf X' := by
    ext ⟨k, hk⟩
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, ← Subgroup.mem_inf, hFC]
  have hQF1 : Q₀.subgroupOf X' ≤ F.subgroupOf X' := fun k hk =>
    Subgroup.mem_subgroupOf.mpr (hQ₀F (Subgroup.mem_subgroupOf.mp hk))
  have cardF : Nat.card (F.subgroupOf X') = Nat.card F :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFX).toEquiv
  have cardA : Nat.card (A.subgroupOf X') = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv
  have cardC : Nat.card (C.subgroupOf X') = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCX).toEquiv
  have hZA1 : ∀ a ∈ A.subgroupOf X', (∀ a' ∈ A.subgroupOf X',
      ⁅a, a'⁆ ∈ Q₀.subgroupOf X') → a ∈ Q₀.subgroupOf X' := by
    intro a ha h
    have h1 := hZA a.1 (Subgroup.mem_subgroupOf.mp ha) (fun c' hc' => by
      have hc'' : (⟨c', hAX hc'⟩ : ↥X') ∈ A.subgroupOf X' := Subgroup.mem_subgroupOf.mpr hc'
      have h' := Subgroup.mem_subgroupOf.mp (h ⟨c', hAX hc'⟩ hc'')
      simpa [commutatorElement_def] using h')
    exact Subgroup.mem_subgroupOf.mpr h1
  have hZC1 : ∀ c ∈ C.subgroupOf X', (∀ c' ∈ C.subgroupOf X',
      ⁅c, c'⁆ ∈ Q₀.subgroupOf X') → c ∈ Q₀.subgroupOf X' := by
    intro c hc h
    have h1 := hZC c.1 (Subgroup.mem_subgroupOf.mp hc) (fun c' hc' => by
      have hc'' : (⟨c', hCX hc'⟩ : ↥X') ∈ C.subgroupOf X' := Subgroup.mem_subgroupOf.mpr hc'
      have h' := Subgroup.mem_subgroupOf.mp (h ⟨c', hCX hc'⟩ hc'')
      simpa [commutatorElement_def] using h')
    exact Subgroup.mem_subgroupOf.mpr h1
  have hx1 : ∀ f ∈ F.subgroupOf X', ⁅f, (⟨x, hxX⟩ : ↥X')⁆ ∈ Q₀.subgroupOf X' := by
    intro f hf
    have h1 := hx f.1 (Subgroup.mem_subgroupOf.mp hf)
    exact Subgroup.mem_subgroupOf.mpr (by simpa [commutatorElement_def] using h1)
  have key := b2_diag_core (K := ↥X') (A.subgroupOf X') (C.subgroupOf X') (F.subgroupOf X')
    (Q₀.subgroupOf X') hsup1 hint1 hQF1 hFA1 hFC1 (by rw [cardF, cardC, hcC])
    (by rw [cardF, cardA, hcA]) hZA1 hZC1 ⟨x, hxX⟩ hx1
  exact Subgroup.mem_subgroupOf.mp key

end B2Generic

section B2E1

variable {G : Type} [Group G] [Finite G]

theorem b2_conj_mem_of_comm {A B Q : Subgroup G} (hQA : Q ≤ A)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, ⁅a, b⁆ ∈ Q) {c : G} (hc : c ∈ B) {f : G} (hf : f ∈ A) :
    c * f * c⁻¹ ∈ A := by
  have h1 : ⁅f, c⁆ ∈ Q := hcomm f hf c hc
  have h2 : c * f * c⁻¹ = ⁅f, c⁆⁻¹ * f := by simp only [commutatorElement_def]; group
  rw [h2]
  exact A.mul_mem (hQA (Q.inv_mem h1)) hf

theorem b2_factor_normal {X Q F₁ F₂ : Subgroup G} {q : ℕ} (hT : TwoFactors Q X F₁ F₂ q) :
    (∀ x ∈ X, ∀ f ∈ F₁, x * f * x⁻¹ ∈ F₁) ∧ (∀ x ∈ X, ∀ f ∈ F₂, x * f * x⁻¹ ∈ F₂) := by
  obtain ⟨hQ1, hQ2, -, -, hsup, -, hcomm, -, -⟩ := hT
  have hcomm' : ∀ a ∈ F₂, ∀ b ∈ F₁, ⁅a, b⁆ ∈ Q := fun a ha b hb => by
    have h := Q.inv_mem (hcomm b hb a ha)
    rwa [commutatorElement_inv] at h
  have h21 : F₂ ≤ Subgroup.normalizer (F₁ : Set G) := fun c hc => by
    rw [Subgroup.mem_normalizer_iff]
    intro f
    constructor
    · intro hf; exact b2_conj_mem_of_comm hQ1 hcomm hc hf
    · intro hf
      have := b2_conj_mem_of_comm hQ1 hcomm (F₂.inv_mem hc) hf
      have e : c⁻¹ * (c * f * c⁻¹) * c⁻¹⁻¹ = f := by group
      rwa [e] at this
  have h12 : F₁ ≤ Subgroup.normalizer (F₂ : Set G) := fun c hc => by
    rw [Subgroup.mem_normalizer_iff]
    intro f
    constructor
    · intro hf; exact b2_conj_mem_of_comm hQ2 hcomm' hc hf
    · intro hf
      have := b2_conj_mem_of_comm hQ2 hcomm' (F₁.inv_mem hc) hf
      have e : c⁻¹ * (c * f * c⁻¹) * c⁻¹⁻¹ = f := by group
      rwa [e] at this
  constructor
  · have hX : X ≤ Subgroup.normalizer (F₁ : Set G) := by
      rw [← hsup]; exact sup_le (fun x hx => Subgroup.le_normalizer hx) h21
    exact fun x hx f hf => (Subgroup.mem_normalizer_iff.mp (hX hx) f).mp hf
  · have hX : X ≤ Subgroup.normalizer (F₂ : Set G) := by
      rw [← hsup]; exact sup_le h12 (fun x hx => Subgroup.le_normalizer hx)
    exact fun x hx f hf => (Subgroup.mem_normalizer_iff.mp (hX hx) f).mp hf

theorem b2_nt_facts {M Q Z B : Subgroup G} {t : G} (hSplit : RtSplitStatement)
    (hH : E1Hyp M Q Z B t) :
    Nt M (LB M Q B) t ≤ LB M Q B ∧ Nt M (LB M Q B) t ⊓ E1Xpre M Q B t = Q ∧
      Nt M (LB M Q B) t ⊔ E1Xpre M Q B t = Rt M (LB M Q B) t ∧
      (∀ r ∈ Rt M (LB M Q B) t, ∀ x ∈ E1Xpre M Q B t, r * x * r⁻¹ ∈ E1Xpre M Q B t) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hSplit G M Q Z B t hH
  exact ⟨h1, h2, h3, h4⟩

theorem b2_comm_NX {M Q Z B : Subgroup G} {t : G}
    (h2 : Nt M (LB M Q B) t ⊓ E1Xpre M Q B t = Q)
    (h3 : Nt M (LB M Q B) t ⊔ E1Xpre M Q B t = Rt M (LB M Q B) t)
    (h4 : ∀ r ∈ Rt M (LB M Q B) t, ∀ x ∈ E1Xpre M Q B t, r * x * r⁻¹ ∈ E1Xpre M Q B t) :
    ∀ n ∈ Nt M (LB M Q B) t, ∀ x ∈ E1Xpre M Q B t, ⁅n, x⁆ ∈ Q := by
  intro n hn x hx
  have hnR : n ∈ Rt M (LB M Q B) t := by rw [← h3]; exact Subgroup.mem_sup_left hn
  have hxR : x ∈ Rt M (LB M Q B) t := by rw [← h3]; exact Subgroup.mem_sup_right hx
  have hu : x * n⁻¹ * x⁻¹ ∈ Nt M (LB M Q B) t :=
    nt_conj_mem_Rt M (LB M Q B) t x hxR n⁻¹ ((Nt M (LB M Q B) t).inv_mem hn)
  have hv : n * x * n⁻¹ ∈ E1Xpre M Q B t := h4 n hnR x hx
  have hmemN : n * (x * n⁻¹ * x⁻¹) ∈ Nt M (LB M Q B) t :=
    (Nt M (LB M Q B) t).mul_mem hn hu
  have hmemX : (n * x * n⁻¹) * x⁻¹ ∈ E1Xpre M Q B t :=
    (E1Xpre M Q B t).mul_mem hv ((E1Xpre M Q B t).inv_mem hx)
  have e1 : ⁅n, x⁆ = n * (x * n⁻¹ * x⁻¹) := by simp only [commutatorElement_def, mul_assoc]
  have e2 : ⁅n, x⁆ = (n * x * n⁻¹) * x⁻¹ := by simp only [commutatorElement_def, mul_assoc]
  have hmem : ⁅n, x⁆ ∈ Nt M (LB M Q B) t ⊓ E1Xpre M Q B t := by
    refine ⟨?_, ?_⟩
    · rw [e1]; exact hmemN
    · rw [e2]; exact hmemX
  rw [h2] at hmem
  exact hmem

end B2E1

section B2Fc

variable {G : Type} [Group G] [Finite G]

theorem b2_Fc_le (hCt : CtStructureStatement) (hSplit : RtSplitStatement)
    {M Q Z B : Subgroup G} {t : G} (hH : E1Hyp M Q Z B t) {g : G} (hg : E1CaseBHyp M Q B t g)
    {Fb Fc : Subgroup G} (hTF : TwoFactors Q (E1Xpre M Q B t) Fb Fc (Nat.card Z))
    (hN' : conjSubgroup g (Nt M (LB M Q B) t) ≤ Nt M (LB M Q B) t ⊔ Fb) :
    Fc ≤ conjSubgroup g (E1Xpre M Q B t) := by
  classical
  have hQn : M ≤ Subgroup.normalizer (Q : Set G) := hH.ctx.hyp.Q_normal.2
  have hZn : M ≤ Subgroup.normalizer (Z : Set G) := hH.ctx.hyp.Z_normal.2
  have hq4 : 4 ≤ Nat.card Z := hH.ctx.hyp.q4
  have htL : t ∈ LB M Q B := hH.mem
  obtain ⟨hNL, hNX, hNR, hXR⟩ := b2_nt_facts hSplit hH
  have hcommNX := b2_comm_NX (Z := Z) hNX hNR hXR
  obtain ⟨hQFb, hQFc, hFbX, hFcX, hsupF, hintF, hcommF, hSb, hSc⟩ := hTF
  have hXR' : E1Xpre M Q B t ≤ Rt M (LB M Q B) t := by rw [← hNR]; exact le_sup_right
  have hRM : Rt M (LB M Q B) t ≤ M := hH.ctx.Rt_le_M t
  have hXM : E1Xpre M Q B t ≤ M := hXR'.trans hRM
  have hNM : Nt M (LB M Q B) t ≤ M := (orthE1_Nt_le_Rt M (LB M Q B) t).trans hRM
  have hFcM : Fc ≤ M := hFcX.trans hXM
  have hFbM : Fb ≤ M := hFbX.trans hXM
  have hRH0 : Rt M (LB M Q B) t ≤ H0 M Z := hH.ctx.Rt_le_H0 t
  have hconjM : ∀ m ∈ M, conjSubgroup m (LB M Q B) ≤ M := by
    intro m hm x hx
    have h1 := hH.ctx.LB_le_M (mem_conjSubgroup.mp hx)
    have h2 := M.mul_mem (M.mul_mem hm h1) (M.inv_mem hm)
    have e : m * (m⁻¹ * x * m) * m⁻¹ = x := by group
    rwa [e] at h2
  have hgM : g ∈ M := by
    have hLgM : Lgen M (LB M Q B) ≤ M := by unfold Lgen; exact iSup₂_le hconjM
    exact hLgM hg.1
  have hgQ : g ∈ Subgroup.normalizer (Q : Set G) := hQn hgM
  have hgZ : g ∈ Subgroup.normalizer (Z : Set G) := hZn hgM
  have hgQ' : conjSubgroup g⁻¹ Q = Q := conjSubgroup_eq_self_iff.mpr (hQn (M.inv_mem hgM))
  let T : Subgroup G := ⨅ (c : G) (_ : c ∈ Fc), CommQ hQn c
  have hT : ∀ y, y ∈ T ↔ ∀ c ∈ Fc, y ∈ M ∧ ⁅y, c⁆ ∈ Q := by
    intro y
    simp only [T, Subgroup.mem_iInf, mem_CommQ]
  have hNT : Nt M (LB M Q B) t ≤ T := fun n hn => (hT n).mpr fun c hc' =>
    ⟨hNM hn, hcommNX n hn c (hFcX hc')⟩
  have hFbT : Fb ≤ T := fun f hf => (hT f).mpr fun c hc' =>
    ⟨hFbM hf, hcommF f hf c hc'⟩
  have hNgT : conjSubgroup g (Nt M (LB M Q B) t) ≤ T := fun y hy =>
    (sup_le hNT hFbT) (hN' hy)
  set P : Subgroup G := conjSubgroup g⁻¹ Fc with hPdef
  have hP_mem : ∀ x, x ∈ P ↔ g * x * g⁻¹ ∈ Fc := fun x => by
    rw [hPdef, mem_conjSubgroup, inv_inv]
  have hQP : Q ≤ P := fun u hu => by
    rw [hP_mem]
    exact hQFc ((Subgroup.mem_normalizer_iff.mp hgQ u).mp hu)
  have hP_E1 : P ≤ E1Ct hH.ctx t := by
    intro x hx
    have hc' : g * x * g⁻¹ ∈ Fc := (hP_mem x).mp hx
    have hxM : x ∈ M := by
      have h1 := hFcM hc'
      have h2 := M.mul_mem (M.mul_mem (M.inv_mem hgM) h1) hgM
      have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rwa [e] at h2
    have hs : g * t * g⁻¹ ∈ conjSubgroup g (Nt M (LB M Q B) t) := by
      have e : g⁻¹ * (g * t * g⁻¹) * g = t := by group
      rw [mem_conjSubgroup, e]
      exact tMemNt_aux hH
    have hcs : ⁅g * x * g⁻¹, g * t * g⁻¹⁆ ∈ Q := by
      have h1 := ((hT _).mp (hNgT hs) (g * x * g⁻¹) hc').2
      have h2 := Q.inv_mem h1
      rwa [commutatorElement_inv] at h2
    have hxt : ⁅x, t⁆ ∈ Q := by
      have e : ⁅x, t⁆ = g⁻¹ * ⁅g * x * g⁻¹, g * t * g⁻¹⁆ * g⁻¹⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hQn (M.inv_mem hgM)) _).mp hcs
    have hcH0 : g * x * g⁻¹ ∈ H0 M Z := hRH0 (hXR' (hFcX hc'))
    have hcC : g * x * g⁻¹ ∈ Subgroup.centralizer (Z : Set G) :=
      (Subgroup.mem_inf.mp (show g * x * g⁻¹ ∈ M ⊓ Subgroup.centralizer (Z : Set G) from hcH0)).2
    have hxH0 : x ∈ H0 M Z := by
      show x ∈ M ⊓ Subgroup.centralizer (Z : Set G)
      refine Subgroup.mem_inf.mpr ⟨hxM, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hz' : g * z * g⁻¹ ∈ (Z : Set G) := (Subgroup.mem_normalizer_iff.mp hgZ z).mp hz
      have hcom := (Subgroup.mem_centralizer_iff.mp hcC) (g * z * g⁻¹) hz'
      calc z * x = g⁻¹ * ((g * z * g⁻¹) * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * (g * z * g⁻¹)) * g := by rw [hcom]
        _ = x * z := by group
    show x ∈ CommQ hQn t ⊓ H0 M Z
    exact Subgroup.mem_inf.mpr ⟨mem_CommQ.mpr ⟨hxM, hxt⟩, hxH0⟩
  have hP_perf : ⁅P, P⁆ ⊔ Q = P := by
    apply le_antisymm
    · exact sup_le (Subgroup.commutator_le.mpr fun a ha b hb =>
        P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)) hQP
    · have hF : Fc ≤ ⁅Fc, Fc⁆ ⊔ Q := b7a_le_commutator_sup_of_sl hq4 hQFc hSc
      have hmap : P ≤ Subgroup.map (MulAut.conj g⁻¹).toMonoidHom (⁅Fc, Fc⁆ ⊔ Q) :=
        Subgroup.map_mono hF
      have hmap' : Subgroup.map (MulAut.conj g⁻¹).toMonoidHom (⁅Fc, Fc⁆ ⊔ Q) = ⁅P, P⁆ ⊔ Q := by
        have hgQ'' : Subgroup.map (MulAut.conj g⁻¹).toMonoidHom Q = Q := hgQ'
        rw [Subgroup.map_sup, Subgroup.map_commutator, hgQ'']
        rfl
      exact hmap.trans hmap'.le
  have hPX : P ≤ E1Xpre M Q B t := (hCt G M Q Z B t hH).2.2 P hQP hP_E1 hP_perf
  intro c hcF
  rw [mem_conjSubgroup]
  apply hPX
  rw [hP_mem]
  have e : g * (g⁻¹ * c * g) * g⁻¹ = c := by group
  rw [e]
  exact hcF

end B2Fc

section B2Assembly

variable {G : Type} [Group G] [Finite G]

theorem b2_comm_symm {a b : G} {Q : Subgroup G} (h : ⁅a, b⁆ ∈ Q) : ⁅b, a⁆ ∈ Q := by
  have h' := Q.inv_mem h
  rwa [commutatorElement_inv] at h'

theorem b2_isSL_iso {X Y : Type} [Group X] [Group Y] {q : ℕ} (e : X ≃* Y)
    (h : IsSLModel 2 q X) : IsSLModel 2 q Y := by
  obtain ⟨K, hK, hfin, hcard, ⟨e'⟩⟩ := h
  exact ⟨K, hK, hfin, hcard, ⟨e.symm.trans e'⟩⟩

theorem b2_twoFactors_swap {X Q F₁ F₂ : Subgroup G} {q : ℕ} (hT : TwoFactors Q X F₁ F₂ q) :
    TwoFactors Q X F₂ F₁ q := by
  obtain ⟨hQ1, hQ2, hF1, hF2, hsup, hint, hcomm, hS1, hS2⟩ := hT
  refine ⟨hQ2, hQ1, hF2, hF1, ?_, ?_, fun a ha b hb => ?_, hS2, hS1⟩
  · rw [sup_comm]; exact hsup
  · rw [inf_comm]; exact hint
  · exact b2_comm_symm (hcomm b hb a ha)

theorem b2_twoFactors_conj {X Q F₁ F₂ : Subgroup G} {q : ℕ} (hT : TwoFactors Q X F₁ F₂ q) {g : G}
    (hgQ : conjSubgroup g Q = Q) :
    TwoFactors Q (conjSubgroup g X) (conjSubgroup g F₁) (conjSubgroup g F₂) q := by
  obtain ⟨hQ1, hQ2, hF1, hF2, hsup, hint, hcomm, hS1, hS2⟩ := hT
  refine ⟨?_, ?_, Subgroup.map_mono hF1, Subgroup.map_mono hF2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hgQ]; exact Subgroup.map_mono hQ1
  · rw [← hgQ]; exact Subgroup.map_mono hQ2
  · rw [← conjSubgroup_sup', hsup]
  · rw [← conjSubgroup_inf, hint, hgQ]
  · intro a ha b hb
    rw [← hgQ, mem_conjSubgroup]
    have ha' := mem_conjSubgroup.mp ha
    have hb' := mem_conjSubgroup.mp hb
    have e : g⁻¹ * ⁅a, b⁆ * g = ⁅g⁻¹ * a * g, g⁻¹ * b * g⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact hcomm _ ha' _ hb'
  · have h := QuotSat.conj (fun _ _ _ _ e h => b2_isSL_iso e h) hS1 g
    rw [hgQ] at h
    exact h
  · have h := QuotSat.conj (fun _ _ _ _ e h => b2_isSL_iso e h) hS2 g
    rw [hgQ] at h
    exact h

theorem b2_conj_normal {X F : Subgroup G} {g : G}
    (hN : ∀ x ∈ X, ∀ f ∈ F, x * f * x⁻¹ ∈ F) :
    ∀ r ∈ conjSubgroup g X, ∀ a ∈ conjSubgroup g F, r * a * r⁻¹ ∈ conjSubgroup g F := by
  intro r hr a ha
  rw [mem_conjSubgroup] at hr ha ⊢
  have e : g⁻¹ * (r * a * r⁻¹) * g = (g⁻¹ * r * g) * (g⁻¹ * a * g) * (g⁻¹ * r * g)⁻¹ := by
    group
  rw [e]
  exact hN _ hr _ ha

theorem b2_conj_center {S Q : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (Q : Set G))
    (hcen : ∀ x ∈ S, (∀ y ∈ S, ⁅x, y⁆ ∈ Q) → x ∈ Q) :
    ∀ x ∈ conjSubgroup g S, (∀ y ∈ conjSubgroup g S, ⁅x, y⁆ ∈ Q) → x ∈ Q := by
  intro x hx hc
  have hconj_inv : ∀ u ∈ Q, g⁻¹ * u * g ∈ Q := fun u hu => by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) u).mp hu
    rwa [inv_inv] at h
  have key : g⁻¹ * x * g ∈ Q := by
    apply hcen (g⁻¹ * x * g) (mem_conjSubgroup.mp hx)
    intro y hy
    have hy' : g * y * g⁻¹ ∈ conjSubgroup g S := by
      rw [mem_conjSubgroup]
      have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
      rw [e]; exact hy
    have h1 := hc _ hy'
    have h2 := hconj_inv _ h1
    have e : g⁻¹ * ⁅x, g * y * g⁻¹⁆ * g = ⁅g⁻¹ * x * g, y⁆ := by
      simp only [commutatorElement_def]; group
    rwa [e] at h2
  have h3 := (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * x * g)).mp key
  have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  rwa [e] at h3

theorem b2_centralizer_sup {M Q Fc H₁ H₂ : Subgroup G}
    (hQn : M ≤ Subgroup.normalizer (Q : Set G)) (hH₁M : H₁ ≤ M) (hH₂M : H₂ ≤ M)
    (h₁ : ∀ c ∈ Fc, ∀ h ∈ H₁, ⁅c, h⁆ ∈ Q) (h₂ : ∀ c ∈ Fc, ∀ h ∈ H₂, ⁅c, h⁆ ∈ Q) :
    ∀ c ∈ Fc, ∀ y ∈ H₁ ⊔ H₂, ⁅c, y⁆ ∈ Q := by
  classical
  let T : Subgroup G := ⨅ (c : G) (_ : c ∈ Fc), CommQ hQn c
  have hT : ∀ y, y ∈ T ↔ ∀ c ∈ Fc, y ∈ M ∧ ⁅y, c⁆ ∈ Q := by
    intro y
    simp only [T, Subgroup.mem_iInf, mem_CommQ]
  have hsup : H₁ ⊔ H₂ ≤ T := by
    refine sup_le (fun h hh => (hT h).mpr fun c hc => ⟨hH₁M hh, b2_comm_symm (h₁ c hc h hh)⟩)
      (fun h hh => (hT h).mpr fun c hc => ⟨hH₂M hh, b2_comm_symm (h₂ c hc h hh)⟩)
  intro c hc y hy
  exact b2_comm_symm ((hT y).mp (hsup hy) c hc).2

end B2Assembly

section B2Main


theorem b2_of (hCt : CtStructureStatement) (hSplit : RtSplitStatement) (hTI : NtTIStatement) :
    B2Statement := by
  intro G _ _ M Q Z B t hH g hg hplus Fb Fc hTF hN'
  classical
  have hQn : M ≤ Subgroup.normalizer (Q : Set G) := hH.ctx.hyp.Q_normal.2
  have hq4 : 4 ≤ Nat.card Z := hH.ctx.hyp.q4
  obtain ⟨n, k, hn2, -⟩ := hH.ctx.hyp.cp
  have htL : t ∈ LB M Q B := hH.mem
  obtain ⟨hNL, hNX, hNR, hXR⟩ := b2_nt_facts hSplit hH
  have hcommNX := b2_comm_NX (Z := Z) hNX hNR hXR
  have hRM : Rt M (LB M Q B) t ≤ M := hH.ctx.Rt_le_M t
  have hXR' : E1Xpre M Q B t ≤ Rt M (LB M Q B) t := by rw [← hNR]; exact le_sup_right
  have hXM : E1Xpre M Q B t ≤ M := hXR'.trans hRM
  have hNRle : Nt M (LB M Q B) t ≤ Rt M (LB M Q B) t := orthE1_Nt_le_Rt M (LB M Q B) t
  have hNM : Nt M (LB M Q B) t ≤ M := hNRle.trans hRM
  have hTF0 := hTF
  obtain ⟨hQFb, hQFc, hFbX, hFcX, hsupF, hintF, hcommF, hSb, hSc⟩ := hTF
  have hFbM : Fb ≤ M := hFbX.trans hXM
  have hFcM : Fc ≤ M := hFcX.trans hXM
  have hconjM : ∀ m ∈ M, conjSubgroup m (LB M Q B) ≤ M := by
    intro m hm x hx
    have h1 := hH.ctx.LB_le_M (mem_conjSubgroup.mp hx)
    have h2 := M.mul_mem (M.mul_mem hm h1) (M.inv_mem hm)
    have e : m * (m⁻¹ * x * m) * m⁻¹ = x := by group
    rwa [e] at h2
  have hgM : g ∈ M := by
    have hLgM : Lgen M (LB M Q B) ≤ M := by unfold Lgen; exact iSup₂_le hconjM
    exact hLgM hg.1
  have hgQn : g ∈ Subgroup.normalizer (Q : Set G) := hQn hgM
  have hgQ : conjSubgroup g Q = Q := conjSubgroup_eq_self_iff.mpr hgQn
  have hconj_inv : ∀ u ∈ Q, g⁻¹ * u * g ∈ Q := fun u hu => by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgQn) u).mp hu
    rwa [inv_inv] at h
  have hFcX' : Fc ≤ conjSubgroup g (E1Xpre M Q B t) := b2_Fc_le hCt hSplit hH hg hTF0 hN'
  have hTA := b2_twoFactors_conj hTF0 hgQ
  have hTA0 := hTA
  obtain ⟨hQA, hQC, hAX, hCX, hsup, hint, hcomm', hSA, hSC⟩ := hTA
  set X' := conjSubgroup g (E1Xpre M Q B t) with hX'def
  set A := conjSubgroup g Fb with hAdef
  set C := conjSubgroup g Fc with hCdef
  have hnorm1 := b2_factor_normal hTF0
  have hAn : ∀ r ∈ X', ∀ a ∈ A, r * a * r⁻¹ ∈ A := b2_conj_normal hnorm1.1
  have hCn : ∀ r ∈ X', ∀ c ∈ C, r * c * r⁻¹ ∈ C := b2_conj_normal hnorm1.2
  have hcFb : Nat.card Fb = Nat.card Q * (Nat.card Z * (Nat.card Z ^ 2 - 1)) :=
    b2_sl_card hQFb hSb hn2 hq4
  have hcFc : Nat.card Fc = Nat.card Q * (Nat.card Z * (Nat.card Z ^ 2 - 1)) :=
    b2_sl_card hQFc hSc hn2 hq4
  have hFbFc : Nat.card Fb = Nat.card Fc := by rw [hcFb, hcFc]
  have hcFcC : Nat.card Fc = Nat.card C := (card_conjSubgroup g Fc).symm
  have hcFcA : Nat.card Fc = Nat.card A := by
    rw [← hFbFc]; exact (card_conjSubgroup g Fb).symm
  have hZA : ∀ a ∈ A, (∀ a' ∈ A, ⁅a, a'⁆ ∈ Q) → a ∈ Q :=
    b2_conj_center hgQn (fun x hx hy => b2_sl_center_elem hSb hn2 hq4 hx hy)
  have hZC : ∀ c ∈ C, (∀ c' ∈ C, ⁅c, c'⁆ ∈ Q) → c ∈ Q :=
    b2_conj_center hgQn (fun x hx hy => b2_sl_center_elem hSc hn2 hq4 hx hy)
  have hNFc : (Q.subgroupOf Fc).Normal := by
    obtain ⟨h, -⟩ := hSc
    exact h
  haveI := hNFc
  have hsimpFc : IsSimpleGroup (↥Fc ⧸ Q.subgroupOf Fc) := by
    obtain ⟨hN1, hX1⟩ := hSc
    exact (b2_sl_facts hX1 hn2 hq4).2.1
  have hdich1 : Fc ⊓ C = Q ∨ Fc ⊓ C = Fc :=
    b2_sl_dich hQFc hNFc hsimpFc (le_inf hQFc hQC) inf_le_left
      (fun f hf h hh => ⟨Fc.mul_mem (Fc.mul_mem hf hh.1) (Fc.inv_mem hf), hCn f (hFcX' hf) h hh.2⟩)
  rcases hdich1 with hFC_Q | hFC_F
  swap
  · have hle : Fc ≤ C := inf_eq_left.mp hFC_F
    have hFeqC : Fc = C := Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcFcC.symm)
    exact ⟨A, by rw [hFeqC]; exact hTA0⟩
  have hdich2 : Fc ⊓ A = Q ∨ Fc ⊓ A = Fc :=
    b2_sl_dich hQFc hNFc hsimpFc (le_inf hQFc hQA) inf_le_left
      (fun f hf h hh => ⟨Fc.mul_mem (Fc.mul_mem hf hh.1) (Fc.inv_mem hf), hAn f (hFcX' hf) h hh.2⟩)
  rcases hdich2 with hFA_Q | hFA_F
  swap
  · have hle : Fc ≤ A := inf_eq_left.mp hFA_F
    have hFeqA : Fc = A := Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcFcA.symm)
    exact ⟨C, by rw [hFeqA]; exact b2_twoFactors_swap hTA0⟩
  exfalso
  obtain ⟨n₀, hn₀N, hn₀⟩ : ∃ n₀ ∈ Nt M (LB M Q B) t,
      n₀ ∉ conjSubgroup g (Nt M (LB M Q B) t) := by
    by_contra hcon
    have hle : Nt M (LB M Q B) t ≤ conjSubgroup g (Nt M (LB M Q B) t) := fun n hn => by
      by_contra hn'
      exact hcon ⟨n, hn, hn'⟩
    exact hg.2.2.2 (Subgroup.eq_of_le_of_card_ge hle (le_of_eq (card_conjSubgroup g _))).symm
  have hR'N : n₀ ∈ conjSubgroup g (Rt M (LB M Q B) t) := by
    rw [mem_conjSubgroup]
    have h1 : g⁻¹ * n₀ * g ∈ LB M Q B := by
      have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg.2.1) n₀).mp (hNL hn₀N)
      rwa [inv_inv] at h
    exact le_Rt (LB M Q B) htL h1
  have hN'R : conjSubgroup g (Nt M (LB M Q B) t) ≤ conjSubgroup g (Rt M (LB M Q B) t) :=
    Subgroup.map_mono hNRle
  have hX'R : X' ≤ conjSubgroup g (Rt M (LB M Q B) t) := Subgroup.map_mono hXR'
  have hsupR : conjSubgroup g (Nt M (LB M Q B) t) ⊔ X' = conjSubgroup g (Rt M (LB M Q B) t) := by
    rw [← conjSubgroup_sup', hNR]
  have hn₀R' : n₀ ∈ conjSubgroup g (Nt M (LB M Q B) t) ⊔ X' := by
    rw [hsupR]; exact hR'N
  obtain ⟨y, hy, z, hz, hyz⟩ := b2_sup_decomp _ _ _ hN'R hX'R
    (b2_conj_normal (fun r hr s hs => nt_conj_mem_Rt M (LB M Q B) t r hr s hs))
    (b2_conj_normal hXR) n₀ hn₀R'
  have hQNt : Q ≤ Nt M (LB M Q B) t := smith23E1_Q_le_Nt hH.ctx htL
  have hzQ : z ∉ Q := by
    intro hzQ
    apply hn₀
    rw [← hyz]
    refine (conjSubgroup g (Nt M (LB M Q B) t)).mul_mem hy ?_
    exact mem_conjSubgroup.mpr (hQNt (hconj_inv z hzQ))
  have h₁ : ∀ c ∈ Fc, ∀ h ∈ Nt M (LB M Q B) t, ⁅c, h⁆ ∈ Q :=
    fun c hc h hh => b2_comm_symm (hcommNX h hh c (hFcX hc))
  have h₂ : ∀ c ∈ Fc, ∀ h ∈ Fb, ⁅c, h⁆ ∈ Q :=
    fun c hc h hh => b2_comm_symm (hcommF h hh c hc)
  have hzsup : z ∈ Nt M (LB M Q B) t ⊔ Fb := by
    have hz_eq : z = y⁻¹ * n₀ := by rw [← hyz]; group
    rw [hz_eq]
    exact (Nt M (LB M Q B) t ⊔ Fb).mul_mem ((Nt M (LB M Q B) t ⊔ Fb).inv_mem (hN' hy))
      (le_sup_left (a := Nt M (LB M Q B) t) (b := Fb) hn₀N)
  have hzcent : ∀ c ∈ Fc, ⁅c, z⁆ ∈ Q := fun c hc =>
    b2_centralizer_sup hQn hNM hFbM h₁ h₂ c hc z hzsup
  exact hzQ (b2_diag_G hAX hCX hFcX' hQFc hAn hCn hsup hint hFA_Q hFC_Q hcFcC hcFcA hZA hZC
    hz hzcent)

end B2Main

end CFSG.RankThree.GF2n.Smith81.Smith23E1

end
