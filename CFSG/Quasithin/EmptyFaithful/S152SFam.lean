module

public import CFSG.Quasithin.EmptyFaithful.S152SMax
public import CFSG.Quasithin.EmptyFaithful.S152QF
public import CFSG.LieType.BorelTits.AllModels

public section

namespace CFSG.Quasithin

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Assembly.LowTwoRank CFSG.Blueprint
  CFSG.LieType.BorelTits


@[expose] def IsBigQLieGroup (X : Type) [Group X] : Prop :=
  ∃ f : ℕ, 2 ≤ f ∧ (StatedClassicalModel X .PSL 2 2 f ∨ StatedClassicalModel X .PSL 3 2 f ∨
    StatedClassicalModel X .PSU 3 2 f ∨ StatedClassicalModel X .PSp 2 2 f ∨
    ChevalleyExceptionalModel X .G2 2 f ∨ ChevalleyExceptionalModel X .trialityD4 2 f ∨
    (Odd f ∧ 3 ≤ f ∧ ReeTitsModel X .twistedF4 2 f) ∨ (Odd f ∧ 3 ≤ f ∧ SuzukiModel X 2 f))

theorem lemma115LieCharTwo_cases {Y : Type} [Group Y] (h : Lemma115LieCharTwo Y)
    (hF2 : ¬ IsF2RankTwoGroup Y) (hA6 : ¬ Nonempty (Y ≃* alternatingGroup (Fin 6))) :
    IsBigQLieGroup Y ∨ IsPSL 3 2 1 Y := by
  rcases h with h | h | h
  · rcases h with (⟨f, h | h | h | h | h | h | h | h⟩ | h) | ⟨n, hn, h⟩
    · exact Or.inl ⟨f, h.1, Or.inl h.2⟩
    · obtain ⟨hf, h⟩ := h
      by_cases hf1 : f = 1
      · subst hf1
        exact Or.inr h
      · exact Or.inl ⟨f, by omega, Or.inr (Or.inl h)⟩
    · exact Or.inl ⟨f, h.1, Or.inr (Or.inr (Or.inl h.2))⟩
    · exact Or.inl ⟨f, h.1, Or.inr (Or.inr (Or.inr (Or.inl h.2)))⟩
    · exact Or.inl ⟨f, h.1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.2))))⟩
    · obtain ⟨hf, h⟩ := h
      by_cases hf1 : f = 1
      · subst hf1
        exact absurd (Or.inr (Or.inr (Or.inr (Or.inr h)))) hF2
      · exact Or.inl ⟨f, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))⟩
    · obtain ⟨hodd, hf3, h⟩ := h
      exact Or.inl ⟨f, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hodd, hf3, h⟩))))))⟩
    · obtain ⟨hodd, hf3, h⟩ := h
      exact Or.inl ⟨f, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hodd, hf3, h⟩))))))⟩
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inl h)))) hF2
    · rcases hn with rfl | rfl
      · exact absurd (Or.inr (Or.inl h)) hF2
      · exact absurd (Or.inr (Or.inr (Or.inl h))) hF2
  · exact absurd h hA6
  · exact absurd (Or.inl h) hF2

section BT


theorem holds_of_isBigQLieGroup {X : Type} [Group X] (h : IsBigQLieGroup X) : Holds X 2 := by
  obtain ⟨f, hf, h | h | h | h | h | h | h | h⟩ := h
  · exact holds_of_lieModel (t := .PSL) (n := 2) (f := f) (Or.inl ⟨by decide, h⟩) (by decide)
  · exact holds_of_lieModel (t := .PSL) (n := 3) (f := f) (Or.inl ⟨by decide, h⟩) (by decide)
  · exact holds_of_lieModel (t := .PSU) (n := 3) (f := f) (Or.inl ⟨by decide, h⟩) (by decide)
  · exact holds_of_lieModel (t := .PSp) (n := 2) (f := f) (Or.inl ⟨by decide, h⟩) (by decide)
  · exact holds_of_lieModel (t := .G2) (n := 0) (f := f) (Or.inr (Or.inl ⟨rfl, by decide, h⟩)) (by decide)
  · exact holds_of_lieModel (t := .trialityD4) (n := 0) (f := f)
      (Or.inr (Or.inl ⟨rfl, by decide, h⟩)) (by decide)
  · exact holds_of_lieModel (t := .twistedF4) (n := 0) (f := f)
      (Or.inr (Or.inr (Or.inl ⟨rfl, by decide, h.2.2⟩))) (by decide)
  · exact holds_of_lieModel (t := .twistedB2) (n := 0) (f := f)
      (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, h.2.2⟩))) (by decide)

end BT

section Products

theorem isPGroup_two_prod {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y] {H : Subgroup X}
    {K : Subgroup Y} (hH : IsPGroup 2 H) (hK : IsPGroup 2 K) : IsPGroup 2 (H.prod K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hH
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 hK
  refine IsPGroup.of_card (n := a + b) ?_
  rw [Nat.card_congr (Subgroup.prodEquiv H K).toEquiv, Nat.card_prod, ha, hb, pow_add]

theorem prod_mem_normalizer_prod {X Y : Type} [Group X] [Group Y] {H : Subgroup X} {K : Subgroup Y}
    {a : X} {b : Y} (ha : a ∈ Subgroup.normalizer (H : Set X)) (hb : b ∈ Subgroup.normalizer (K : Set Y)) :
    ((a, b) : X × Y) ∈ Subgroup.normalizer ((H.prod K : Subgroup (X × Y)) : Set (X × Y)) := by
  rw [Subgroup.mem_normalizer_iff] at ha hb ⊢
  rintro ⟨p, q⟩
  simp only [Subgroup.mem_prod, Prod.mk_mul_mk, Prod.inv_mk]
  rw [ha p, hb q]

theorem fst_mem_normalizer_of_prod {X Y : Type} [Group X] [Group Y] {H : Subgroup X} {K : Subgroup Y}
    {a : X} {b : Y} (h : ((a, b) : X × Y) ∈ Subgroup.normalizer ((H.prod K : Subgroup (X × Y)) : Set (X × Y)))
    (hK : (1 : Y) ∈ K) : a ∈ Subgroup.normalizer (H : Set X) := by
  rw [Subgroup.mem_normalizer_iff] at h ⊢
  intro p
  have := h (p, 1)
  simpa [Subgroup.mem_prod, hK] using this

theorem snd_mem_normalizer_of_prod {X Y : Type} [Group X] [Group Y] {H : Subgroup X} {K : Subgroup Y}
    {a : X} {b : Y} (h : ((a, b) : X × Y) ∈ Subgroup.normalizer ((H.prod K : Subgroup (X × Y)) : Set (X × Y)))
    (hH : (1 : X) ∈ H) : b ∈ Subgroup.normalizer (K : Set Y) := by
  rw [Subgroup.mem_normalizer_iff] at h ⊢
  intro q
  have := h (1, q)
  simpa [Subgroup.mem_prod, hH] using this

theorem fst_mem_normalizer_map {X Y : Type} [Group X] [Group Y] {U : Subgroup (X × Y)} {a : X} {b : Y}
    (h : ((a, b) : X × Y) ∈ Subgroup.normalizer (U : Set (X × Y))) :
    a ∈ Subgroup.normalizer ((U.map (MonoidHom.fst X Y) : Subgroup X) : Set X) := by
  have hi : ((a, b) : X × Y)⁻¹ ∈ Subgroup.normalizer (U : Set (X × Y)) := Subgroup.inv_mem _ h
  rw [Subgroup.mem_normalizer_iff] at h hi ⊢
  intro x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨_, (h u).1 hu, by simp⟩
  · rintro ⟨u', hu', hu'x⟩
    refine ⟨_, (hi u').1 hu', ?_⟩
    simp only [MonoidHom.coe_fst, Prod.inv_mk, Prod.fst_mul] at hu'x ⊢
    rw [hu'x]
    group

theorem snd_mem_normalizer_map {X Y : Type} [Group X] [Group Y] {U : Subgroup (X × Y)} {a : X} {b : Y}
    (h : ((a, b) : X × Y) ∈ Subgroup.normalizer (U : Set (X × Y))) :
    b ∈ Subgroup.normalizer ((U.map (MonoidHom.snd X Y) : Subgroup Y) : Set Y) := by
  have hi : ((a, b) : X × Y)⁻¹ ∈ Subgroup.normalizer (U : Set (X × Y)) := Subgroup.inv_mem _ h
  rw [Subgroup.mem_normalizer_iff] at h hi ⊢
  intro x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨_, (h u).1 hu, by simp⟩
  · rintro ⟨u', hu', hu'x⟩
    refine ⟨_, (hi u').1 hu', ?_⟩
    simp only [MonoidHom.coe_snd, Prod.inv_mk, Prod.snd_mul] at hu'x ⊢
    rw [hu'x]
    group

end Products

section ProductsMain

theorem eq_prod_map_of_sylow {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    {U : Subgroup (X × Y)} (hp : IsPGroup 2 U) (hidx : ¬ 2 ∣ U.index) :
    U = (U.map (MonoidHom.fst X Y)).prod (U.map (MonoidHom.snd X Y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K : Subgroup (X × Y) := (U.map (MonoidHom.fst X Y)).prod (U.map (MonoidHom.snd X Y)) with hK
  have hUK : U ≤ K := fun u hu => Subgroup.mem_prod.2 ⟨⟨u, hu, rfl⟩, ⟨u, hu, rfl⟩⟩
  have hKp : IsPGroup 2 K := isPGroup_two_prod (hp.map _) (hp.map _)
  have h1 : U.relIndex K * K.index = U.index := Subgroup.relIndex_mul_index hUK
  have h2 : U.relIndex K * Nat.card ↥(U ⊓ K) = Nat.card ↥K := Subgroup.relIndex_mul_card U K
  rw [inf_eq_left.2 hUK] at h2
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hKp
  have hdvd : U.relIndex K ∣ 2 ^ a := by rw [← ha, ← h2]; exact dvd_mul_right _ _
  obtain ⟨j, hj, hrel⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hodd : ¬ 2 ∣ U.relIndex K := fun h => hidx (h.trans ⟨K.index, h1.symm⟩)
  have hj0 : j = 0 := by
    by_contra hne
    exact hodd (hrel ▸ dvd_pow_self 2 hne)
  rw [hj0, pow_zero] at hrel
  exact le_antisymm hUK (Subgroup.relIndex_eq_one.1 hrel)

theorem BorelTitsLite.prod {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (hX : BorelTitsLite X) (hY : BorelTitsLite Y) : BorelTitsLite (X × Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro U hU hp
  set U₁ : Subgroup X := U.map (MonoidHom.fst X Y) with hU₁
  set U₂ : Subgroup Y := U.map (MonoidHom.snd X Y) with hU₂
  have hp₁ : IsPGroup 2 U₁ := hp.map _
  have hp₂ : IsPGroup 2 U₂ := hp.map _
  have h1 : ∃ (S : Sylow 2 X) (P : Subgroup X), (U₁ ≠ ⊥ → P ≠ ⊤) ∧
      Subgroup.normalizer (U₁ : Set X) ≤ P ∧ Subgroup.normalizer ((S : Subgroup X) : Set X) ≤ P := by
    by_cases h : U₁ = ⊥
    · exact ⟨Classical.arbitrary _, ⊤, fun h' => absurd h h', le_top, le_top⟩
    · obtain ⟨S, P, hP, hN, hS⟩ := hX U₁ h hp₁
      exact ⟨S, P, fun _ => hP, hN, hS⟩
  have h2 : ∃ (S : Sylow 2 Y) (P : Subgroup Y), (U₂ ≠ ⊥ → P ≠ ⊤) ∧
      Subgroup.normalizer (U₂ : Set Y) ≤ P ∧ Subgroup.normalizer ((S : Subgroup Y) : Set Y) ≤ P := by
    by_cases h : U₂ = ⊥
    · exact ⟨Classical.arbitrary _, ⊤, fun h' => absurd h h', le_top, le_top⟩
    · obtain ⟨S, P, hP, hN, hS⟩ := hY U₂ h hp₂
      exact ⟨S, P, fun _ => hP, hN, hS⟩
  obtain ⟨S₁, P₁, hP₁, hN₁, hS₁⟩ := h1
  obtain ⟨S₂, P₂, hP₂, hN₂, hS₂⟩ := h2
  let S : Sylow 2 (X × Y) := IsPGroup.toSylow
    (P := (S₁ : Subgroup X).prod (S₂ : Subgroup Y))
    (isPGroup_two_prod S₁.isPGroup' S₂.isPGroup')
    (by
      rw [Subgroup.index_prod]
      intro h
      rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h with h | h
      · exact Sylow.not_dvd_index S₁ h
      · exact Sylow.not_dvd_index S₂ h)
  refine ⟨S, P₁.prod P₂, ?_, ?_, ?_⟩
  · intro htop
    obtain ⟨u, huU⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hU
    by_cases hu : (u : X × Y).1 = 1
    · have hu2 : (u : X × Y).2 ≠ 1 := fun h2' => huU (Subtype.ext (Prod.ext hu h2'))
      have hU₂ne : U₂ ≠ ⊥ := fun h => hu2 (by
        have : (u : X × Y).2 ∈ U₂ := ⟨u, u.2, rfl⟩
        rw [h, Subgroup.mem_bot] at this
        exact this)
      apply hP₂ hU₂ne
      rw [eq_top_iff]
      intro q _
      have : ((1 : X), q) ∈ P₁.prod P₂ := htop ▸ Subgroup.mem_top _
      exact (Subgroup.mem_prod.1 this).2
    · have hU₁ne : U₁ ≠ ⊥ := fun h => hu (by
        have : (u : X × Y).1 ∈ U₁ := ⟨u, u.2, rfl⟩
        rw [h, Subgroup.mem_bot] at this
        exact this)
      apply hP₁ hU₁ne
      rw [eq_top_iff]
      intro p _
      have : (p, (1 : Y)) ∈ P₁.prod P₂ := htop ▸ Subgroup.mem_top _
      exact (Subgroup.mem_prod.1 this).1
  · rintro ⟨a, b⟩ hab
    refine Subgroup.mem_prod.2 ⟨?_, ?_⟩
    · exact hN₁ (fst_mem_normalizer_map hab)
    · exact hN₂ (snd_mem_normalizer_map hab)
  · rintro ⟨a, b⟩ hab
    refine Subgroup.mem_prod.2 ⟨?_, ?_⟩
    · exact hS₁ (fst_mem_normalizer_of_prod hab (Subgroup.one_mem _))
    · exact hS₂ (snd_mem_normalizer_of_prod hab (Subgroup.one_mem _))

theorem BorelCentralizerTrivial.prod {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (hX : BorelCentralizerTrivial X) (hY : BorelCentralizerTrivial Y) :
    BorelCentralizerTrivial (X × Y) := by
  intro U hp hidx ⟨a, b⟩ hx
  have hU := eq_prod_map_of_sylow hp hidx
  set U₁ : Subgroup X := U.map (MonoidHom.fst X Y) with hU₁
  set U₂ : Subgroup Y := U.map (MonoidHom.snd X Y) with hU₂
  have hp₁ : IsPGroup 2 U₁ := hp.map _
  have hp₂ : IsPGroup 2 U₂ := hp.map _
  have hidx' : ¬ 2 ∣ U₁.index * U₂.index := by
    rw [← Subgroup.index_prod, ← hU]
    exact hidx
  have hid₁ : ¬ 2 ∣ U₁.index := fun h => hidx' (h.mul_right _)
  have hid₂ : ¬ 2 ∣ U₂.index := fun h => hidx' (h.mul_left _)
  have h1 : a = 1 := by
    apply hX U₁ hp₁ hid₁ a
    intro n hn
    have hmem : ((n, (1 : Y)) : X × Y) ∈ Subgroup.normalizer ((U : Subgroup (X × Y)) : Set (X × Y)) := by
      rw [hU]
      exact prod_mem_normalizer_prod hn (Subgroup.one_mem (Subgroup.normalizer (U₂ : Set Y)))
    have := hx _ hmem
    exact (Prod.ext_iff.1 this).1
  have h2 : b = 1 := by
    apply hY U₂ hp₂ hid₂ b
    intro n hn
    have hmem : (((1 : X), n) : X × Y) ∈ Subgroup.normalizer ((U : Subgroup (X × Y)) : Set (X × Y)) := by
      rw [hU]
      exact prod_mem_normalizer_prod (Subgroup.one_mem (Subgroup.normalizer (U₁ : Set X))) hn
    have := hx _ hmem
    exact (Prod.ext_iff.1 this).2
  rw [h1, h2]
  rfl

end ProductsMain

section Transport

variable {X Y : Type} [Group X] [Group Y]

theorem BorelTitsLite.of_mulEquiv [Finite X] (e : X ≃* Y) (h : BorelTitsLite X) : BorelTitsLite Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro V hV hVp
  have hVeq : (V.map e.symm.toMonoidHom).map e.toMonoidHom = V := by
    rw [Subgroup.map_map]
    have hid : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Y := by ext x; simp
    rw [hid, Subgroup.map_id]
  have hne : V.map e.symm.toMonoidHom ≠ ⊥ := by
    intro hbot
    apply hV
    rw [← hVeq, hbot, Subgroup.map_bot]
  obtain ⟨S, P, hP, hN, hS⟩ := h _ hne (hVp.map e.symm.toMonoidHom)
  have hmap : ∀ A B : Subgroup X, A ≤ B → A.map e.toMonoidHom ≤ B.map e.toMonoidHom :=
    fun A B h => Subgroup.map_mono h
  have hsurj : Function.Surjective e.toMonoidHom := e.surjective
  refine ⟨Sylow.mapSurjective hsurj S, P.map e.toMonoidHom, ?_, ?_, ?_⟩
  · intro htop
    apply hP
    have := congrArg (Subgroup.map e.symm.toMonoidHom) htop
    rw [Subgroup.map_map] at this
    have hid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id X := by ext x; simp
    rw [hid, Subgroup.map_id] at this
    rw [this]
    exact Subgroup.map_top_of_surjective _ e.symm.surjective
  · have := hmap _ _ hN
    rw [Subgroup.map_equiv_normalizer_eq] at this
    rw [hVeq] at this
    exact this
  · rw [Sylow.coe_mapSurjective, ← Subgroup.map_equiv_normalizer_eq]
    exact hmap _ _ hS

theorem BorelCentralizerTrivial.of_mulEquiv (e : X ≃* Y) (h : BorelCentralizerTrivial X) :
    BorelCentralizerTrivial Y := by
  intro U hp hidx y hy
  have hU : (U.map e.symm.toMonoidHom).map e.toMonoidHom = U := by
    rw [Subgroup.map_map]
    have hid : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Y := by ext x; simp
    rw [hid, Subgroup.map_id]
  have hp' : IsPGroup 2 (U.map e.symm.toMonoidHom) := hp.map _
  have hidx' : ¬ 2 ∣ (U.map e.symm.toMonoidHom).index := by
    rw [Subgroup.index_map_of_bijective (f := e.symm.toMonoidHom) e.symm.bijective]
    exact hidx
  have := h _ hp' hidx' (e.symm y) (by
    intro b hb
    have hb' : e b ∈ Subgroup.normalizer (U : Set Y) := by
      rw [← hU, ← Subgroup.map_equiv_normalizer_eq]
      exact ⟨b, hb, rfl⟩
    have := hy (e b) hb'
    have h2 := congrArg e.symm this
    simpa using h2)
  have h3 := congrArg e this
  simpa using h3

end Transport

@[expose] def BTProps (X : Type) [Group X] : Prop := BorelTitsLite X ∧ BorelCentralizerTrivial X

theorem BTProps.of_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite X] (e : X ≃* Y) (h : BTProps X) :
    BTProps Y :=
  ⟨BorelTitsLite.of_mulEquiv e h.1, BorelCentralizerTrivial.of_mulEquiv e h.2⟩

theorem BTProps.prod {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y] (hX : BTProps X)
    (hY : BTProps Y) : BTProps (X × Y) :=
  ⟨BorelTitsLite.prod hX.1 hY.1, BorelCentralizerTrivial.prod hX.2 hY.2⟩

@[expose] def BigQBorelCentralizerTrivial : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsBigQLieGroup X → BorelCentralizerTrivial X

section BTDerived


theorem BTProps.of_isBigQLieGroup (hBQ : BigQBorelCentralizerTrivial) {X : Type} [Group X] [Finite X]
    (h : IsBigQLieGroup X) : BTProps X :=
  ⟨BorelTitsLite.of_holds (holds_of_isBigQLieGroup h), hBQ X h⟩

end BTDerived

end CFSG.Quasithin
