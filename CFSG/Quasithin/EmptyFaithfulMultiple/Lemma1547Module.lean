module

public import CFSG.Quasithin.Background.B1NaturalL2
public import CFSG.Quasithin.Background.B2FactorizationOffender
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1547Block

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace L1547

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {W : Type*} [CommGroup W]

structure ModData (A S P : Subgroup (MulAut W)) (I : Finset (Subgroup (MulAut W))) (z₀ : W) :
    Prop where
  exp2 : ∀ w : W, w ^ 2 = 1
  SA : S ≤ A
  S2 : IsPGroup 2 S
  PS : P ≤ S
  Psyl : IsSylowTwoOf P (⨆ L ∈ I, L)
  comm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a
  ind : ∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥
  nat : ∀ L ∈ I, ActsAsNaturalL2 L (commV L)
  span : fixV (⨆ L ∈ I, L) ⊔ ⨆ L ∈ I, commV L = ⊤
  cind : ∀ L ∈ I, commV L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), commV L' = ⊥
  perm : ∀ g ∈ A, ∀ L ∈ I,
    B1.conjAut g L ∈ I ∧ (commV L).map g.toMonoidHom = commV (B1.conjAut g L)
  z_ne : z₀ ≠ 1
  fix : ∀ w : W, w ∈ fixV S ↔ w = 1 ∨ w = z₀
  gen : ∀ U : Subgroup W, (∀ g ∈ A, ∀ u ∈ U, g u ∈ U) → z₀ ∈ U → U = ⊤
  ne : I.Nonempty

theorem card_SL2 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide

section Fixed

variable [Finite W]

theorem exists_fixed_of_isPGroup {S : Subgroup (MulAut W)} (hS : IsPGroup 2 S) {U : Subgroup W}
    (hU : ∀ s ∈ S, ∀ u ∈ U, s u ∈ U) (hUne : U ≠ ⊥) (hU2 : IsPGroup 2 U) :
    ∃ u ∈ U, u ≠ 1 ∧ ∀ s ∈ S, s u = u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let act : MulAction S U :=
    { smul := fun s u => ⟨(s : MulAut W) u, hU s s.2 u u.2⟩
      one_smul := fun u => Subtype.ext rfl
      mul_smul := fun s t u => Subtype.ext rfl }
  have hdvd : 2 ∣ Nat.card U := by
    obtain ⟨n, hn⟩ := hU2.exists_card_eq
    rcases n with _ | n
    · exact absurd (Subgroup.card_eq_one.mp (by simpa using hn)) hUne
    · rw [hn]
      exact dvd_pow_self 2 (Nat.succ_ne_zero n)
  have h1 : (1 : U) ∈ MulAction.fixedPoints S U := fun s =>
    Subtype.ext (map_one (s : MulAut W))
  obtain ⟨b, hb, hb1⟩ := hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point U hdvd h1
  refine ⟨b, b.2, fun h => hb1 (Subtype.ext h.symm), fun s hs => ?_⟩
  exact congrArg Subtype.val (hb ⟨s, hs⟩)

end Fixed

theorem eq_of_mul_eq_mul {U₁ U₂ : Subgroup W} (hU : U₁ ⊓ U₂ = ⊥) {a a' b b' : W} (ha : a ∈ U₁)
    (ha' : a' ∈ U₁) (hb : b ∈ U₂) (hb' : b' ∈ U₂) (hab : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [hab]
      _ = b' * b⁻¹ := by group
  have h2 : a'⁻¹ * a ∈ U₁ ⊓ U₂ :=
    ⟨U₁.mul_mem (U₁.inv_mem ha') ha, h1 ▸ U₂.mul_mem hb' (U₂.inv_mem hb)⟩
  rw [hU, Subgroup.mem_bot] at h2
  have h3 : a = a' := by
    calc a = a' * (a'⁻¹ * a) := by group
      _ = a' := by rw [h2, mul_one]
  refine ⟨h3, ?_⟩
  rw [h3] at hab
  exact mul_left_cancel hab

theorem iSup_eq_of_pair {α β : Type*} [CompleteLattice β] {I : Finset α} {a b : α}
    (hI : ∀ x, x ∈ I ↔ x = a ∨ x = b) (f : α → β) : ⨆ x ∈ I, f x = f a ⊔ f b := by
  refine le_antisymm (iSup₂_le fun x hx => ?_) (sup_le ?_ ?_)
  · rcases (hI x).mp hx with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  · exact le_iSup₂_of_le (f := fun x (_ : x ∈ I) => f x) a ((hI a).mpr (Or.inl rfl)) le_rfl
  · exact le_iSup₂_of_le (f := fun x (_ : x ∈ I) => f x) b ((hI b).mpr (Or.inr rfl)) le_rfl

theorem iSup_ne_eq_of_pair {α β : Type*} [CompleteLattice β] {I : Finset α} {a b : α}
    (hab : a ≠ b) (hI : ∀ x, x ∈ I ↔ x = a ∨ x = b) (f : α → β) :
    ⨆ x ∈ I, ⨆ (_ : x ≠ a), f x = f b := by
  rw [iSup_eq_of_pair hI (fun x => ⨆ (_ : x ≠ a), f x)]
  simp [hab.symm]

theorem conjAut_eq_of_mem_normalizer {g : MulAut W} {L : Subgroup (MulAut W)}
    (hg : g ∈ Subgroup.normalizer (L : Set (MulAut W))) : B1.conjAut g L = L := by
  ext x
  rw [B1.mem_conjAut]
  have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (L : Set (MulAut W))).inv_mem hg)
    x)
  rw [inv_inv] at this
  exact this.symm

@[expose] def slRho : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) := ⟨!![0, 1; 1, 1], by decide⟩

@[expose] def slTau : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) := ⟨!![0, 1; 1, 0], by decide⟩

theorem orderOf_slRho : orderOf slRho = 3 :=
  orderOf_eq_prime (by decide) (by decide)

theorem slRho_normal : ∀ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2), ∀ i : Fin 3,
    ∃ j : Fin 3, g * slRho ^ (i : ℕ) * g⁻¹ = slRho ^ (j : ℕ) := by
  decide

theorem exists_three_two {H : Type*} [Group H] {L : Subgroup H}
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :
    ∃ R : Subgroup H, R ≤ L ∧ Nat.card R = 3 ∧ (∀ ℓ ∈ L, ∀ r ∈ R, ℓ * r * ℓ⁻¹ ∈ R) ∧
      ∃ τ ∈ L, τ ^ 2 = 1 ∧ ∃ r ∈ R, τ * r ≠ r * τ := by
  let ι : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) →* H := L.subtype.comp e.symm.toMonoidHom
  have hι : Function.Injective ι := L.subtype_injective.comp e.symm.injective
  have hιL : ∀ g, ι g ∈ L := fun g => (e.symm g).2
  refine ⟨(Subgroup.zpowers slRho).map ι, ?_, ?_, ?_, ι slTau, hιL _, ?_, ι slRho,
    ⟨slRho, Subgroup.mem_zpowers _, rfl⟩, ?_⟩
  · rintro _ ⟨g, -, rfl⟩
    exact hιL g
  · rw [Subgroup.card_map_of_injective hι, Nat.card_zpowers, orderOf_slRho]
  · rintro ℓ hℓ _ ⟨x, hx, rfl⟩
    obtain ⟨n, rfl⟩ := (mem_powers_iff_mem_zpowers.mpr hx : x ∈ Submonoid.powers slRho)
    have hn : slRho ^ n = slRho ^ ((⟨n % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) : ℕ) := by
      rw [← pow_mod_orderOf, orderOf_slRho]
    obtain ⟨j, hj⟩ := slRho_normal (e ⟨ℓ, hℓ⟩) ⟨n % 3, Nat.mod_lt _ (by norm_num)⟩
    refine ⟨slRho ^ (j : ℕ), Subgroup.npow_mem_zpowers _ _, ?_⟩
    have hℓι : ℓ = ι (e ⟨ℓ, hℓ⟩) := by simp [ι]
    rw [← hj, map_mul, map_mul, map_inv, ← hn, ← hℓι]
  · rw [← map_pow, show slTau ^ 2 = 1 by decide, map_one]
  · intro hc
    exact (show slTau * slRho ≠ slRho * slTau by decide) (hι (by rw [map_mul, map_mul, hc]))

theorem comm_of_card_three {H : Type*} [Group H] {R : Subgroup H} (hR : Nat.card R = 3) :
    ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic R := isCyclic_of_prime_card hR
  intro a ha b hb
  have := (IsCyclic.commGroup (α := R)).mul_comm ⟨a, ha⟩ ⟨b, hb⟩
  exact congrArg Subtype.val this

theorem pow_three_of_card_three {H : Type*} [Group H] {R : Subgroup H} (hR : Nat.card R = 3)
    {a : H} (ha : a ∈ R) : a ^ 3 = 1 := by
  have := Subgroup.orderOf_dvd_natCard R ha
  rw [hR] at this
  exact orderOf_dvd_iff_pow_eq_one.mp this

theorem le_centralizer_of_comm {H : Type*} [Group H] {A B : Subgroup H}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : B ≤ Subgroup.centralizer (A : Set H) :=
  fun b hb => Subgroup.mem_centralizer_iff.mpr fun a ha => h a ha b hb

theorem comm_sup {H : Type*} [Group H] {A B : Subgroup H} {x : H}
    (hA : ∀ a ∈ A, x * a = a * x) (hB : ∀ b ∈ B, x * b = b * x) :
    ∀ y ∈ A ⊔ B, x * y = y * x := by
  have hle : A ⊔ B ≤ Subgroup.centralizer ({x} : Set H) :=
    sup_le (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hA a ha).symm)
      (fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr (hB b hb).symm)
  exact fun y hy => (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm

namespace ModData

variable {A S P : Subgroup (MulAut W)} {I : Finset (Subgroup (MulAut W))} {z₀ : W}

theorem card_commV (h : ModData A S P I z₀) {L : Subgroup (MulAut W)} (hL : L ∈ I) :
    Nat.card (commV L) = 4 := by
  obtain ⟨-, φ, -⟩ := h.nat L hL
  rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card]
  rfl

theorem card_L (h : ModData A S P I z₀) {L : Subgroup (MulAut W)} (hL : L ∈ I) :
    Nat.card L = 6 := by
  obtain ⟨e, -, -⟩ := h.nat L hL
  rw [Nat.card_congr e.toEquiv, card_SL2]

theorem isPGroup_of_le (h : ModData A S P I z₀) (U : Subgroup W) : IsPGroup 2 U :=
  fun u => ⟨1, Subtype.ext (by simpa using h.exp2 u)⟩

theorem conjAut_iSup_le (h : ModData A S P I z₀) {g : MulAut W} (hg : g ∈ A) :
    B1.conjAut g (⨆ L ∈ I, L) ≤ ⨆ L ∈ I, L := by
  rw [conjAut_eq_map, Subgroup.map_iSup]
  refine iSup_le fun L => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hL => ?_
  have := (h.perm g hg L hL).1
  rw [← conjAut_eq_map]
  exact le_iSup₂_of_le (f := fun (K : Subgroup (MulAut W)) (_ : K ∈ I) => K) _ this le_rfl

theorem fixV_eq_bot [Finite W] (h : ModData A S P I z₀) : fixV (⨆ L ∈ I, L) = ⊥ := by
  set J : Subgroup (MulAut W) := ⨆ L ∈ I, L with hJ
  have hinv : ∀ g ∈ A, ∀ u ∈ fixV J, g u ∈ fixV J := by
    intro g hg u hu j hj
    have hj' : g⁻¹ * j * g ∈ J := by
      have := h.conjAut_iSup_le (A.inv_mem hg)
      refine this (B1.mem_conjAut.mpr ?_)
      rw [show g⁻¹⁻¹ * (g⁻¹ * j * g) * g⁻¹ = j by group]
      exact hj
    have := hu _ hj'
    simp only [MulAut.mul_apply] at this
    have h2 := congrArg g this
    simpa using h2
  by_contra hne
  obtain ⟨u, huF, hu1, hufix⟩ := exists_fixed_of_isPGroup h.S2
    (fun s hs u hu => hinv s (h.SA hs) u hu) hne (h.isPGroup_of_le _)
  have huz : u = z₀ := ((h.fix u).mp hufix).resolve_left hu1
  have htop := h.gen _ hinv (huz ▸ huF)
  obtain ⟨L, hL⟩ := h.ne
  have hLJ : L ≤ J := le_iSup₂_of_le (f := fun (K : Subgroup (MulAut W)) (_ : K ∈ I) => K) L hL
    le_rfl
  have hLbot : L = ⊥ := by
    refine eq_bot_iff.mpr fun a ha => ?_
    rw [Subgroup.mem_bot]
    ext w
    have hw : w ∈ fixV J := by rw [htop]; trivial
    exact hw a (hLJ ha)
  have := h.card_L hL
  rw [hLbot, Subgroup.card_bot] at this
  omega

theorem iSup_commV_eq_top [Finite W] (h : ModData A S P I z₀) : ⨆ L ∈ I, commV L = ⊤ := by
  have := h.span
  rwa [h.fixV_eq_bot, bot_sup_eq] at this

theorem conjAut_injective (g : MulAut W) : Function.Injective (B1.conjAut g) := by
  intro A₁ A₂ h12
  rw [← B1.conjAut_inv_conjAut g A₁, h12, B1.conjAut_inv_conjAut]

theorem conjAut_mul (g h' : MulAut W) (L : Subgroup (MulAut W)) :
    B1.conjAut (g * h') L = B1.conjAut g (B1.conjAut h' L) := by
  ext x
  simp only [B1.mem_conjAut]
  rw [show (g * h')⁻¹ * x * (g * h') = h'⁻¹ * (g⁻¹ * x * g) * h' by group]

theorem conjAut_one (L : Subgroup (MulAut W)) : B1.conjAut 1 L = L := by
  ext x
  simp [B1.mem_conjAut]

theorem conjAut_eq_of_odd (h : ModData A S P I z₀) (hI : I.card ≤ 2) {g : MulAut W} (hg : g ∈ A)
    {k : ℕ} (hk : Odd k) (hgk : g ^ k = 1) {L : Subgroup (MulAut W)} (hL : L ∈ I) :
    B1.conjAut g L = L := by
  classical
  by_contra hne
  set L' := B1.conjAut g L with hL'
  have hL'I : L' ∈ I := (h.perm g hg L hL).1
  have hgL' : B1.conjAut g L' = L := by
    have hmem : B1.conjAut g L' ∈ I := (h.perm g hg L' hL'I).1
    have hne' : B1.conjAut g L' ≠ L' := fun heq => hne (conjAut_injective g (heq.trans hL'))
    have hsub : ({L, L'} : Finset _) = I := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hL
        · exact hL'I
      · rw [Finset.card_pair (fun heq => hne heq.symm)]
        exact hI
    rw [← hsub] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    exact hmem.resolve_right hne'
  have hsq : ∀ K ∈ ({L, L'} : Finset (Subgroup (MulAut W))), B1.conjAut (g ^ 2) K = K := by
    intro K hK
    simp only [Finset.mem_insert, Finset.mem_singleton] at hK
    rw [pow_two, conjAut_mul]
    rcases hK with rfl | rfl
    · rw [← hL', hgL']
    · rw [hgL']
  have hpow : ∀ K ∈ ({L, L'} : Finset (Subgroup (MulAut W))), ∀ n : ℕ,
      B1.conjAut ((g ^ 2) ^ n) K = K := by
    intro K hK n
    induction n with
    | zero => rw [pow_zero, conjAut_one]
    | succ n ih => rw [pow_succ, conjAut_mul, hsq K hK, ih]
  obtain ⟨j, rfl⟩ := hk
  have h1 : B1.conjAut (g ^ (2 * j + 1)) L = L' := by
    rw [pow_succ, pow_mul, conjAut_mul, ← hL']
    exact hpow L' (by simp) j
  rw [hgk, conjAut_one] at h1
  exact hne h1.symm

theorem commV_ne_bot (h : ModData A S P I z₀) {L : Subgroup (MulAut W)} (hL : L ∈ I) :
    commV L ≠ ⊥ := by
  intro hb
  have := h.card_commV hL
  rw [hb, Subgroup.card_bot] at this
  omega

theorem maps_commV (h : ModData A S P I z₀) {g : MulAut W} (hg : g ∈ A) {L : Subgroup (MulAut W)}
    (hL : L ∈ I) {u : W} (hu : u ∈ commV L) : g u ∈ commV (B1.conjAut g L) := by
  rw [← (h.perm g hg L hL).2]
  exact ⟨u, hu, rfl⟩

theorem exists_swap [Finite W] (h : ModData A S P I z₀) {L₁ L₂ : Subgroup (MulAut W)}
    (hne : L₁ ≠ L₂) (hI : ∀ L, L ∈ I ↔ L = L₁ ∨ L = L₂) : ∃ s ∈ S, B1.conjAut s L₁ = L₂ := by
  classical
  by_contra hns
  push Not at hns
  have hL₁I : L₁ ∈ I := (hI L₁).mpr (Or.inl rfl)
  have hL₂I : L₂ ∈ I := (hI L₂).mpr (Or.inr rfl)
  have hfix1 : ∀ s ∈ S, B1.conjAut s L₁ = L₁ := by
    intro s hs
    have hmem := (hI _).mp (h.perm s (h.SA hs) L₁ hL₁I).1
    exact hmem.resolve_right (hns s hs)
  have hfix2 : ∀ s ∈ S, B1.conjAut s L₂ = L₂ := by
    intro s hs
    have hmem := (hI _).mp (h.perm s (h.SA hs) L₂ hL₂I).1
    rcases hmem with h1 | h1
    · exact absurd (conjAut_injective s ((hfix1 s hs).trans h1.symm)) hne
    · exact h1
  have hz : ∀ L ∈ I, (∀ s ∈ S, B1.conjAut s L = L) → z₀ ∈ commV L := by
    intro L hL hfixL
    have hinv : ∀ s ∈ S, ∀ u ∈ commV L, s u ∈ commV L := by
      intro s hs u hu
      have := h.maps_commV (h.SA hs) hL hu
      rwa [hfixL s hs] at this
    obtain ⟨u, hu, hu1, hufix⟩ :=
      exists_fixed_of_isPGroup h.S2 hinv (h.commV_ne_bot hL) (h.isPGroup_of_le _)
    have := ((h.fix u).mp hufix).resolve_left hu1
    rwa [← this]
  have h1 := hz L₁ hL₁I hfix1
  have h2 := hz L₂ hL₂I hfix2
  have hdisj := h.cind L₁ hL₁I
  rw [iSup_ne_eq_of_pair hne hI] at hdisj
  have : z₀ ∈ commV L₁ ⊓ commV L₂ := ⟨h1, h2⟩
  rw [hdisj, Subgroup.mem_bot] at this
  exact h.z_ne this

theorem sup_eq_top_of_pair [Finite W] (h : ModData A S P I z₀) {L₁ L₂ : Subgroup (MulAut W)}
    (hI : ∀ L, L ∈ I ↔ L = L₁ ∨ L = L₂) : commV L₁ ⊔ commV L₂ = ⊤ := by
  have := h.iSup_commV_eq_top
  rwa [iSup_eq_of_pair hI] at this

theorem inf_eq_bot_of_pair (h : ModData A S P I z₀) {L₁ L₂ : Subgroup (MulAut W)}
    (hne : L₁ ≠ L₂) (hI : ∀ L, L ∈ I ↔ L = L₁ ∨ L = L₂) : commV L₁ ⊓ commV L₂ = ⊥ := by
  have := h.cind L₁ ((hI L₁).mpr (Or.inl rfl))
  rwa [iSup_ne_eq_of_pair hne hI] at this

theorem exists_components [Finite W] (h : ModData A S P I z₀) {L₁ L₂ : Subgroup (MulAut W)}
    (hne : L₁ ≠ L₂) (hI : ∀ L, L ∈ I ↔ L = L₁ ∨ L = L₂) :
    ∃ z₁ ∈ commV L₁, ∃ z₂ ∈ commV L₂, z₁ ≠ 1 ∧ z₂ ≠ 1 ∧ z₀ = z₁ * z₂ := by
  classical
  have hL₁I : L₁ ∈ I := (hI L₁).mpr (Or.inl rfl)
  have hL₂I : L₂ ∈ I := (hI L₂).mpr (Or.inr rfl)
  have hz : z₀ ∈ commV L₁ ⊔ commV L₂ := by rw [h.sup_eq_top_of_pair hI]; trivial
  obtain ⟨z₁, hz₁, z₂, hz₂, hz₀⟩ := Subgroup.mem_sup.mp hz
  obtain ⟨s, hs, hsL⟩ := h.exists_swap hne hI
  have hsL₂ : B1.conjAut s L₂ = L₁ := by
    have hmem := (hI _).mp (h.perm s (h.SA hs) L₂ hL₂I).1
    rcases hmem with h1 | h1
    · exact h1
    · exact absurd (conjAut_injective s (hsL.trans h1.symm)) hne
  have hs1 : s z₁ ∈ commV L₂ := hsL ▸ h.maps_commV (h.SA hs) hL₁I hz₁
  have hs2 : s z₂ ∈ commV L₁ := hsL₂ ▸ h.maps_commV (h.SA hs) hL₂I hz₂
  have hsz : s z₀ = z₀ := ((h.fix z₀).mpr (Or.inr rfl)) s hs
  have heq : s z₂ * s z₁ = z₁ * z₂ := by
    rw [mul_comm, ← map_mul, hz₀, hsz]
  obtain ⟨e1, e2⟩ := eq_of_mul_eq_mul (h.inf_eq_bot_of_pair hne hI) hs2 hz₁ hs1 hz₂ heq
  refine ⟨z₁, hz₁, z₂, hz₂, ?_, ?_, hz₀.symm⟩
  · intro h1
    apply h.z_ne
    rw [← hz₀, h1, one_mul, ← e2, h1, map_one]
  · intro h2
    apply h.z_ne
    rw [← hz₀, h2, mul_one, ← e1, h2, map_one]

theorem eq_one_of_odd_of_fix [Finite W] (h : ModData A S P I z₀) (hI : I.card ≤ 2)
    {g : MulAut W} (hg : g ∈ A) {k : ℕ} (hk : Odd k) (hgk : g ^ k = 1) (hgz : g z₀ = z₀) :
    g = 1 := by
  classical
  have hfixL : ∀ L ∈ I, ∀ u ∈ commV L, g u ∈ commV L := by
    intro L hL u hu
    have := h.maps_commV hg hL hu
    rwa [h.conjAut_eq_of_odd hI hg hk hgk hL] at this
  have hpos : 0 < I.card := Finset.card_pos.mpr h.ne
  have hc : I.card = 1 ∨ I.card = 2 := by omega
  rcases hc with hc | hc
  · obtain ⟨L₁, hI⟩ := Finset.card_eq_one.mp hc
    have hL₁I : L₁ ∈ I := by rw [hI]; exact Finset.mem_singleton_self L₁
    have htop : commV L₁ = ⊤ := by
      have := h.iSup_commV_eq_top
      rwa [hI, Finset.iSup_singleton] at this
    have hfx := mulAut_fix_of_card_eq_four (h.card_commV hL₁I) (fun u _ => h.exp2 u) g
      (hfixL L₁ hL₁I) (htop ▸ Subgroup.mem_top z₀) h.z_ne hgz hk hgk
    ext w
    exact hfx w (htop ▸ Subgroup.mem_top w)
  · obtain ⟨L₁, L₂, hne, hI'⟩ := Finset.card_eq_two.mp hc
    have hI : ∀ L, L ∈ I ↔ L = L₁ ∨ L = L₂ := fun L => by
      rw [hI']; simp only [Finset.mem_insert, Finset.mem_singleton]
    have hL₁I : L₁ ∈ I := (hI L₁).mpr (Or.inl rfl)
    have hL₂I : L₂ ∈ I := (hI L₂).mpr (Or.inr rfl)
    obtain ⟨z₁, hz₁, z₂, hz₂, hz₁1, hz₂1, hz₀⟩ := h.exists_components hne hI
    have hdec : g z₁ * g z₂ = z₁ * z₂ := by rw [← map_mul, ← hz₀, hgz]
    obtain ⟨e1, e2⟩ := eq_of_mul_eq_mul (h.inf_eq_bot_of_pair hne hI) (hfixL L₁ hL₁I z₁ hz₁) hz₁
      (hfixL L₂ hL₂I z₂ hz₂) hz₂ hdec
    have hf1 := mulAut_fix_of_card_eq_four (h.card_commV hL₁I) (fun u _ => h.exp2 u) g
      (hfixL L₁ hL₁I) hz₁ hz₁1 e1 hk hgk
    have hf2 := mulAut_fix_of_card_eq_four (h.card_commV hL₂I) (fun u _ => h.exp2 u) g
      (hfixL L₂ hL₂I) hz₂ hz₂1 e2 hk hgk
    ext w
    have hw : w ∈ commV L₁ ⊔ commV L₂ := by rw [h.sup_eq_top_of_pair hI]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hw
    rw [map_mul, hf1 a ha, hf2 b hb]
    rfl

theorem stabilizer_le [Finite W] (h : ModData A S P I z₀) (hI : I.card ≤ 2)
    (hsyl : IsSylowTwoOf S A) {g : MulAut W} (hg : g ∈ A) (hgz : g z₀ = z₀) : g ∈ S := by
  classical
  let St : Subgroup (MulAut W) :=
    { carrier := {x | x ∈ A ∧ x z₀ = z₀}
      mul_mem' := fun {a b} ha hb => ⟨A.mul_mem ha.1 hb.1, by
        simp only [MulAut.mul_apply, hb.2, ha.2]⟩
      one_mem' := ⟨A.one_mem, rfl⟩
      inv_mem' := fun {a} ha => ⟨A.inv_mem ha.1, by
        have h1 : (a⁻¹ : MulAut W) (a z₀) = (a⁻¹ : MulAut W) z₀ := by rw [ha.2]
        rw [MulAut.inv_apply_self] at h1
        exact h1.symm⟩ }
  have hSt : S ≤ St := fun s hs => ⟨h.SA hs, ((h.fix z₀).mpr (Or.inr rfl)) s hs⟩
  have hSt2 : IsPGroup 2 St := by
    rintro ⟨x, hxA, hxz⟩
    obtain ⟨a, m, hm, hxm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    refine ⟨a, Subtype.ext ?_⟩
    show x ^ 2 ^ a = 1
    refine h.eq_one_of_odd_of_fix hI (A.pow_mem hxA _) hm ?_ ?_
    · rw [← pow_mul, ← hxm, pow_orderOf_eq_one]
    · have hiter : ∀ n : ℕ, (x ^ n) z₀ = z₀ := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih => rw [pow_succ, MulAut.mul_apply, hxz, ih]
      exact hiter _
  have heq : S = St := by
    refine le_antisymm hSt ?_
    have hle : St ≤ A := fun x hx => hx.1
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hmul := Subgroup.relIndex_mul_relIndex S St A hSt hle
    have hodd : ¬ 2 ∣ S.relIndex St := fun h2 => hsyl.2.2 (h2.trans (Dvd.intro _ hmul))
    have hcard := Subgroup.relIndex_mul_card S St
    rw [inf_eq_left.mpr hSt] at hcard
    obtain ⟨n, hn⟩ := hSt2.exists_card_eq
    have hdvd : S.relIndex St ∣ 2 ^ n := hn ▸ hcard ▸ dvd_mul_right _ _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hj0 : j = 0 := by
      by_contra hj0
      exact hodd (hj ▸ dvd_pow_self 2 hj0)
    rw [hj0, pow_zero] at hj
    exact Subgroup.relIndex_eq_one.mp hj
  exact heq ▸ ⟨hg, hgz⟩

theorem card_eq_four_of_card_one [Finite W] (h : ModData A S P I z₀) (hc : I.card = 1) :
    Nat.card W = 4 := by
  obtain ⟨L₁, hI⟩ := Finset.card_eq_one.mp hc
  have hL₁I : L₁ ∈ I := by rw [hI]; exact Finset.mem_singleton_self L₁
  have htop : commV L₁ = ⊤ := by
    have := h.iSup_commV_eq_top
    rwa [hI, Finset.iSup_singleton] at this
  rw [← Subgroup.card_top (G := W), ← htop, h.card_commV hL₁I]

theorem inf_eq_bot (h : ModData A S P I z₀) {L₁ L₂ : Subgroup (MulAut W)} (hL₁ : L₁ ∈ I)
    (hL₂ : L₂ ∈ I) (hne : L₁ ≠ L₂) : L₁ ⊓ L₂ = ⊥ := by
  have := h.ind L₁ hL₁
  refine le_bot_iff.mp (le_trans (inf_le_inf_left L₁ ?_) this.le)
  exact le_iSup₂_of_le (f := fun (L' : Subgroup (MulAut W)) (_ : L' ∈ I) => ⨆ (_ : L' ≠ L₁), L')
    L₂ hL₂ (le_iSup_of_le hne.symm le_rfl)

theorem eight_le_card [Finite W] (h : ModData A S P I z₀) {L₁ L₂ : Subgroup (MulAut W)}
    (hne : L₁ ≠ L₂) (hI : ∀ L, L ∈ I ↔ L = L₁ ∨ L = L₂) : 8 ≤ Nat.card S := by
  have hL₁I : L₁ ∈ I := (hI L₁).mpr (Or.inl rfl)
  have hL₂I : L₂ ∈ I := (hI L₂).mpr (Or.inr rfl)
  have hJ : (⨆ L ∈ I, L) = L₁ ⊔ L₂ := iSup_eq_of_pair hI (fun L => L)
  have hcomm12 : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a := h.comm L₁ hL₁I L₂ hL₂I hne
  have hcardJ : Nat.card ↥(L₁ ⊔ L₂) = 36 := by
    have := B2F.card_sup_mul_card_inf_of_commute hcomm12
    rw [h.inf_eq_bot hL₁I hL₂I hne, Subgroup.card_bot, mul_one, h.card_L hL₁I,
      h.card_L hL₂I] at this
    exact this
  have hP := h.Psyl
  rw [hJ] at hP
  have hcardP : 4 ≤ Nat.card P := by
    obtain ⟨n, hn⟩ := hP.2.1.exists_card_eq
    have hmul := Subgroup.relIndex_mul_card P (L₁ ⊔ L₂)
    rw [inf_eq_left.mpr hP.1, hn, hcardJ] at hmul
    have hodd : ¬ 2 ∣ P.relIndex (L₁ ⊔ L₂) := hP.2.2
    have hle : 2 ^ n ≤ 36 := hmul ▸ Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (by
      intro h0; rw [h0, zero_mul] at hmul; omega))
    have hn5 : n ≤ 5 := by
      by_contra hn5
      have : 2 ^ 6 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [hn]
    interval_cases n <;> omega
  obtain ⟨s, hs, hsL⟩ := h.exists_swap hne hI
  have hsP : s ∉ P := by
    intro hsP
    have hN : L₁ ⊔ L₂ ≤ Subgroup.normalizer (L₁ : Set (MulAut W)) := by
      refine sup_le Subgroup.le_normalizer (le_trans ?_ (Subgroup.centralizer_le_normalizer _))
      intro b hb
      exact Subgroup.mem_centralizer_iff.mpr fun a ha => hcomm12 a ha b hb
    exact hne ((conjAut_eq_of_mem_normalizer (hN (hP.1 hsP))).symm.trans hsL)
  have hle : P ⊔ Subgroup.zpowers s ≤ S := sup_le h.PS (Subgroup.zpowers_le.mpr hs)
  have hdvd : Nat.card P ∣ Nat.card ↥(P ⊔ Subgroup.zpowers s) :=
    Subgroup.card_dvd_of_le le_sup_left
  obtain ⟨m, hm⟩ := hdvd
  have hm1 : m ≠ 1 := by
    intro hm1
    rw [hm1, mul_one] at hm
    have heq := Subgroup.eq_of_le_of_card_ge (le_sup_left : P ≤ P ⊔ Subgroup.zpowers s) hm.le
    exact hsP (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
  have hm0 : m ≠ 0 := by
    intro hm0
    rw [hm0, mul_zero] at hm
    exact (Nat.card_pos (α := ↥(P ⊔ Subgroup.zpowers s))).ne' hm
  calc 8 = 4 * 2 := by norm_num
    _ ≤ Nat.card P * m := Nat.mul_le_mul hcardP (by omega)
    _ = Nat.card ↥(P ⊔ Subgroup.zpowers s) := hm.symm
    _ ≤ Nat.card S := Subgroup.card_le_of_le hle

theorem exists_noncyclic [Finite W] (h : ModData A S P I z₀) (h3 : 2 < I.card) :
    ∃ Q : Subgroup (MulAut W), Q ≤ ⨆ L ∈ I, L ∧
      Subgroup.centralizer (CFSG.Open.pCore 3 Q : Set Q) ≤ CFSG.Open.pCore 3 Q ∧
      ∃ T' : Subgroup Q, IsPGroup 2 T' ∧ T' ≠ ⊥ ∧
        ¬ IsCyclic ↥(CFSG.Open.pCore 3 Q ⊓ Subgroup.centralizer (T' : Set Q)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨L₁, hL₁, L₂, hL₂, L₃, hL₃, h12, h13, h23⟩ := Finset.two_lt_card.mp h3
  obtain ⟨e₁, -⟩ := h.nat L₁ hL₁
  obtain ⟨e₂, -⟩ := h.nat L₂ hL₂
  obtain ⟨e₃, -⟩ := h.nat L₃ hL₃
  obtain ⟨R₁, hR₁L, hR₁c, hR₁n, τ, hτL, hτ2, r₁, hr₁, hτr₁⟩ := exists_three_two e₁
  obtain ⟨R₂, hR₂L, hR₂c, -, -⟩ := exists_three_two e₂
  obtain ⟨R₃, hR₃L, hR₃c, -, -⟩ := exists_three_two e₃
  have hLJ : ∀ L ∈ I, L ≤ ⨆ L ∈ I, L := fun L hL =>
    le_iSup₂_of_le (f := fun (K : Subgroup (MulAut W)) (_ : K ∈ I) => K) L hL le_rfl
  have c12 := h.comm L₁ hL₁ L₂ hL₂ h12
  have c13 := h.comm L₁ hL₁ L₃ hL₃ h13
  have c23 := h.comm L₂ hL₂ L₃ hL₃ h23
  set E : Subgroup (MulAut W) := R₂ ⊔ R₃ with hEdef
  set R : Subgroup (MulAut W) := R₁ ⊔ E with hRdef
  set Q : Subgroup (MulAut W) := R ⊔ Subgroup.zpowers τ with hQdef
  have hτE : ∀ x ∈ E, τ * x = x * τ :=
    comm_sup (fun b hb => c12 τ hτL b (hR₂L hb)) (fun b hb => c13 τ hτL b (hR₃L hb))
  have hR₁E : ∀ a ∈ R₁, ∀ x ∈ E, a * x = x * a := fun a ha =>
    comm_sup (fun b hb => c12 a (hR₁L ha) b (hR₂L hb)) (fun b hb => c13 a (hR₁L ha) b (hR₃L hb))
  have hR₂R₃ : ∀ a ∈ R₂, ∀ b ∈ R₃, a * b = b * a := fun a ha b hb => c23 a (hR₂L ha) b (hR₃L hb)
  have hinf23 : R₂ ⊓ R₃ = ⊥ := le_bot_iff.mp (le_trans (inf_le_inf hR₂L hR₃L)
    (h.inf_eq_bot hL₂ hL₃ h23).le)
  have hcardE : Nat.card E = 9 := by
    have := B2F.card_sup_mul_card_inf_of_commute hR₂R₃
    rw [hinf23, Subgroup.card_bot, mul_one, hR₂c, hR₃c] at this
    exact this
  have hEcube : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    have hN : R₃ ≤ Subgroup.normalizer (R₂ : Set (MulAut W)) :=
      (le_centralizer_of_comm hR₂R₃).trans (Subgroup.centralizer_le_normalizer _)
    have hx' : x ∈ ((R₂ ⊔ R₃ : Subgroup (MulAut W)) : Set (MulAut W)) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left R₂ R₃ hN] at hx'
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    show (a * b) ^ 3 = 1
    rw [(Commute.mul_pow (hR₂R₃ a ha b hb) 3), pow_three_of_card_three hR₂c ha,
      pow_three_of_card_three hR₃c hb, one_mul]
  have hEnc : ¬ IsCyclic E := by
    intro hc
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := E)
    have hord : orderOf g = 9 := by
      rw [← hcardE]
      exact orderOf_eq_card_of_forall_mem_zpowers hg
    have h3' : g ^ 3 = 1 := Subtype.ext (hEcube g g.2)
    have := orderOf_dvd_of_pow_eq_one h3'
    rw [hord] at this
    omega
  have hRab : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := by
    have hN : E ≤ Subgroup.normalizer (R₁ : Set (MulAut W)) :=
      (le_centralizer_of_comm hR₁E).trans (Subgroup.centralizer_le_normalizer _)
    have hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
      intro x hx y hy
      have hN' : R₃ ≤ Subgroup.normalizer (R₂ : Set (MulAut W)) :=
        (le_centralizer_of_comm hR₂R₃).trans (Subgroup.centralizer_le_normalizer _)
      have hx' : x ∈ ((R₂ ⊔ R₃ : Subgroup (MulAut W)) : Set (MulAut W)) := hx
      rw [Subgroup.coe_mul_of_right_le_normalizer_left R₂ R₃ hN'] at hx'
      obtain ⟨a, ha, b, hb, rfl⟩ := hx'
      show (a * b) * y = y * (a * b)
      refine comm_sup (x := a * b) (fun c hc => ?_) (fun c hc => ?_) y hy
      · exact (calc c * (a * b) = (c * a) * b := by group
          _ = (a * c) * b := by rw [comm_of_card_three hR₂c c hc a ha]
          _ = a * (c * b) := by group
          _ = a * (b * c) := by rw [hR₂R₃ c hc b hb]
          _ = a * b * c := by group).symm
      · exact (calc c * (a * b) = (c * a) * b := by group
          _ = (a * c) * b := by rw [(hR₂R₃ a ha c hc).symm]
          _ = a * (c * b) := by group
          _ = a * (b * c) := by rw [comm_of_card_three hR₃c c hc b hb]
          _ = a * b * c := by group).symm
    intro x hx y hy
    have hx' : x ∈ ((R₁ ⊔ E : Subgroup (MulAut W)) : Set (MulAut W)) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left R₁ E hN] at hx'
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    show (a * b) * y = y * (a * b)
    refine comm_sup (x := a * b) (fun c hc => ?_) (fun c hc => ?_) y hy
    · exact (calc c * (a * b) = (c * a) * b := by group
        _ = (a * c) * b := by rw [comm_of_card_three hR₁c c hc a ha]
        _ = a * (c * b) := by group
        _ = a * (b * c) := by rw [hR₁E c hc b hb]
        _ = a * b * c := by group).symm
    · exact (calc c * (a * b) = (c * a) * b := by group
        _ = (a * c) * b := by rw [(hR₁E a ha c hc).symm]
        _ = a * (c * b) := by group
        _ = a * (b * c) := by rw [hEab c hc b hb]
        _ = a * b * c := by group).symm
  have hR3 : IsPGroup 3 R := by
    have := B2F.card_sup_mul_card_inf_of_commute hR₁E
    rw [hR₁c, hcardE] at this
    have hdvd : Nat.card R ∣ 3 ^ 3 := Dvd.intro _ (this.trans (by norm_num))
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    exact IsPGroup.of_card hk
  have hτR : τ ∈ Subgroup.normalizer (R : Set (MulAut W)) := by
    refine le_normalizer_sup (C := Subgroup.zpowers τ) ?_ ?_ (Subgroup.mem_zpowers τ)
    · exact Subgroup.zpowers_le.mpr (mem_normalizer_of_conj_mem fun r hr => hR₁n τ hτL r hr)
    · refine Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ ?_)
      exact Subgroup.mem_centralizer_iff.mpr fun x hx => (hτE x hx).symm
  have hτRle : Subgroup.zpowers τ ≤ Subgroup.normalizer (R : Set (MulAut W)) :=
    Subgroup.zpowers_le.mpr hτR
  have hQR : Q ≤ Subgroup.normalizer (R : Set (MulAut W)) := sup_le Subgroup.le_normalizer hτRle
  have hRQ : R ≤ Q := le_sup_left
  have hτQ : τ ∈ Q := Subgroup.mem_sup_right (Subgroup.mem_zpowers τ)
  have hτ1 : τ ≠ 1 := by
    intro h1
    apply hτr₁
    rw [h1, one_mul, mul_one]
  have hCQ : ∀ x ∈ Q, (∀ r ∈ R, x * r = r * x) → x ∈ R := by
    intro x hx hxc
    have hx' : x ∈ ((R ⊔ Subgroup.zpowers τ : Subgroup (MulAut W)) : Set (MulAut W)) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left R _ hτRle] at hx'
    obtain ⟨r, hr, y, hy, hxy⟩ := hx'
    have hxy' : r * y = x := hxy
    obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers.mpr hy : y ∈ Submonoid.powers τ)
    have hn' : τ ^ n = y := hn
    rw [← hxy', ← hn'] at hxc ⊢
    rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [← two_mul, pow_mul, hτ2, one_pow, mul_one]
      exact hr
    · exfalso
      rw [pow_succ, pow_mul, hτ2, one_pow, one_mul] at hxc
      apply hτr₁
      have hr₁R : r₁ ∈ R := Subgroup.mem_sup_left hr₁
      have h1 := hxc r₁ hr₁R
      have h2 := hRab r hr r₁ hr₁R
      calc τ * r₁ = r⁻¹ * ((r * τ) * r₁) := by group
        _ = r⁻¹ * (r₁ * (r * τ)) := by rw [h1]
        _ = r⁻¹ * ((r₁ * r) * τ) := by group
        _ = r⁻¹ * ((r * r₁) * τ) := by rw [h2]
        _ = r₁ * τ := by group
  refine ⟨Q, sup_le (sup_le (hR₁L.trans (hLJ L₁ hL₁))
    (sup_le (hR₂L.trans (hLJ L₂ hL₂)) (hR₃L.trans (hLJ L₃ hL₃))))
    (Subgroup.zpowers_le.mpr (hLJ L₁ hL₁ hτL)), ?_, ?_⟩
  · have hRn : (R.subgroupOf Q).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hRQ).mpr hQR
    have hRp : IsPGroup 3 (R.subgroupOf Q) :=
      hR3.of_equiv (Subgroup.subgroupOfEquivOfLe hRQ).symm
    have hRle : R.subgroupOf Q ≤ CFSG.Open.pCore 3 Q := CFSG.LieType.BorelTits.le_pCore 3 hRn hRp
    intro x hx
    apply hRle
    rw [Subgroup.mem_subgroupOf]
    refine hCQ x x.2 fun r hr => ?_
    have := Subgroup.mem_centralizer_iff.mp hx ⟨r, hRQ hr⟩
      (hRle (Subgroup.mem_subgroupOf.mpr hr))
    exact (congrArg Subtype.val this).symm
  · refine ⟨Subgroup.zpowers ⟨τ, hτQ⟩, ?_, ?_, ?_⟩
    · refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, pow_one, Subgroup.orderOf_mk]
      exact orderOf_eq_prime hτ2 hτ1
    · intro hb
      apply hτ1
      have := Subgroup.zpowers_eq_bot.mp hb
      exact congrArg Subtype.val this
    · intro hc
      apply hEnc
      have hEQ : E ≤ Q := le_sup_right.trans hRQ
      have hle : E.subgroupOf Q ≤
          CFSG.Open.pCore 3 Q ⊓ Subgroup.centralizer
            ((Subgroup.zpowers (⟨τ, hτQ⟩ : Q) : Subgroup Q) : Set Q) := by
        have hRn : (R.subgroupOf Q).Normal :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hRQ).mpr hQR
        have hRp : IsPGroup 3 (R.subgroupOf Q) :=
          hR3.of_equiv (Subgroup.subgroupOfEquivOfLe hRQ).symm
        have hRle : R.subgroupOf Q ≤ CFSG.Open.pCore 3 Q :=
          CFSG.LieType.BorelTits.le_pCore 3 hRn hRp
        intro x hx
        refine ⟨hRle (Subgroup.mem_subgroupOf.mpr
          (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hx))), ?_⟩
        show x ∈ Subgroup.centralizer _
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        apply Subtype.ext
        have hxτ := hτE x (Subgroup.mem_subgroupOf.mp hx)
        show ((⟨τ, hτQ⟩ : Q) ^ k : Q).1 * x.1 = x.1 * ((⟨τ, hτQ⟩ : Q) ^ k : Q).1
        rw [Subgroup.coe_zpow]
        exact (Commute.zpow_left hxτ k).eq
      have : IsCyclic (E.subgroupOf Q) := Subgroup.isCyclic_of_le hle
      exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hEQ).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hEQ).surjective

end ModData

end L1547

end CFSG.Quasithin.EmptyFaithfulMultiple
