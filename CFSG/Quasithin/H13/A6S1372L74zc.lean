module

public import CFSG.Quasithin.H13.A6S1372L74zb
public import CFSG.Quasithin.H13.A6S1372L74y
public import CFSG.Quasithin.H13.A6S1372L74z
public import CFSG.Quasithin.H13.A6S1372L74za

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique Matrix
open scoped commutatorElement

namespace A6L74

section Four

variable {Γ₀ : Type*} [Group Γ₀]

@[expose] def IsFourPair (a b : Γ₀) : Prop :=
  a * a = 1 ∧ b * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * b = b * a

@[expose] def InFour (a b g : Γ₀) : Prop := g = 1 ∨ g = a ∨ g = b ∨ g = a * b

instance [DecidableEq Γ₀] (a b : Γ₀) : Decidable (IsFourPair a b) := by
  unfold IsFourPair
  infer_instance

instance [DecidableEq Γ₀] (a b g : Γ₀) : Decidable (InFour a b g) := by
  unfold InFour
  infer_instance

theorem IsFourPair.map {Γ₁ : Type*} [Group Γ₁] {f : Γ₀ →* Γ₁} (hf : Function.Injective f)
    {a b : Γ₀} (h : IsFourPair a b) : IsFourPair (f a) (f b) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨by rw [← map_mul, h1, map_one], by rw [← map_mul, h2, map_one],
    fun h => h3 (hf (h.trans (map_one f).symm)), fun h => h4 (hf (h.trans (map_one f).symm)),
    fun h => h5 (hf h), by rw [← map_mul, ← map_mul, h6]⟩

theorem InFour.of_map {Γ₁ : Type*} [Group Γ₁] {f : Γ₀ →* Γ₁} (hf : Function.Injective f)
    {a b g : Γ₀} (h : InFour (f a) (f b) (f g)) : InFour a b g := by
  rcases h with h | h | h | h
  · exact Or.inl (hf (h.trans (map_one f).symm))
  · exact Or.inr (Or.inl (hf h))
  · exact Or.inr (Or.inr (Or.inl (hf h)))
  · exact Or.inr (Or.inr (Or.inr (hf (h.trans (map_mul f a b).symm))))

theorem InFour.map {Γ₁ : Type*} [Group Γ₁] (f : Γ₀ →* Γ₁) {a b g : Γ₀} (h : InFour a b g) :
    InFour (f a) (f b) (f g) := by
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl (map_one f)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (map_mul f a b)))

theorem a5_centralizer : ∀ a b : alternatingGroup (Fin 5), IsFourPair a b →
    ∀ g : alternatingGroup (Fin 5), (g * a = a * g ∧ g * b = b * g) → InFour a b g := by
  decide +kernel

theorem a5_normalizer : ∀ a b : alternatingGroup (Fin 5), IsFourPair a b →
    ∃ g : alternatingGroup (Fin 5), (g ^ 3 = 1 ∧ g ≠ 1) ∧
      (InFour a b (g * a * g⁻¹) ∧ InFour a b (g * b * g⁻¹)) := by
  decide +kernel

theorem sl3_centralizer : ∀ a b : L3.Γ, IsFourPair a b →
    ∀ g : L3.Γ, (g * a = a * g ∧ g * b = b * g) → InFour a b g := by
  decide +kernel

theorem sl3_normalizer : ∀ a b : L3.Γ, IsFourPair a b →
    ∃ g : L3.Γ, (g ^ 3 = 1 ∧ g ≠ 1) ∧ (InFour a b (g * a * g⁻¹) ∧ InFour a b (g * b * g⁻¹)) := by
  decide +kernel

theorem four_facts {K : Type*} [Group K]
    (hiso : Nonempty (K ≃* alternatingGroup (Fin 5)) ∨ Nonempty (K ≃* L3.Γ)) {a b : K}
    (hab : IsFourPair a b) :
    (∀ g : K, (g * a = a * g ∧ g * b = b * g) → InFour a b g) ∧
      ∃ g : K, (g ^ 3 = 1 ∧ g ≠ 1) ∧ (InFour a b (g * a * g⁻¹) ∧ InFour a b (g * b * g⁻¹)) := by
  have key : ∀ {Γ₁ : Type} [Group Γ₁] (e : K ≃* Γ₁),
      (∀ a b : Γ₁, IsFourPair a b →
        ∀ g : Γ₁, (g * a = a * g ∧ g * b = b * g) → InFour a b g) →
      (∀ a b : Γ₁, IsFourPair a b → ∃ g : Γ₁, (g ^ 3 = 1 ∧ g ≠ 1) ∧
        (InFour a b (g * a * g⁻¹) ∧ InFour a b (g * b * g⁻¹))) →
      (∀ g : K, (g * a = a * g ∧ g * b = b * g) → InFour a b g) ∧
        ∃ g : K, (g ^ 3 = 1 ∧ g ≠ 1) ∧
          (InFour a b (g * a * g⁻¹) ∧ InFour a b (g * b * g⁻¹)) := by
    intro Γ₁ _ e hc hn
    have hinj : Function.Injective e.toMonoidHom := e.injective
    have hab' := hab.map hinj
    refine ⟨fun g hg => ?_, ?_⟩
    · refine InFour.of_map hinj (hc _ _ hab' _ ⟨?_, ?_⟩)
      · show e g * e a = e a * e g
        rw [← map_mul, ← map_mul, hg.1]
      · show e g * e b = e b * e g
        rw [← map_mul, ← map_mul, hg.2]
    · obtain ⟨g, ⟨hg3, hg1⟩, hga, hgb⟩ := hn _ _ hab'
      refine ⟨e.symm g, ⟨?_, ?_⟩, ?_, ?_⟩
      · rw [← map_pow, hg3, map_one]
      · intro h
        apply hg1
        have := congrArg e h
        simpa using this
      · refine InFour.of_map hinj ?_
        show InFour (e a) (e b) (e (e.symm g * a * (e.symm g)⁻¹))
        simpa using hga
      · refine InFour.of_map hinj ?_
        show InFour (e a) (e b) (e (e.symm g * b * (e.symm g)⁻¹))
        simpa using hgb
  rcases hiso with he | he
  · obtain ⟨e⟩ := he
    exact key e a5_centralizer a5_normalizer
  · obtain ⟨e⟩ := he
    exact key e sl3_centralizer sl3_normalizer

end Four

section Eq

variable {V : Type} [CommGroup V] [Finite V]

theorem isQuasisimple_of_simple {Q : Type*} [Group Q] (hs : IsSimpleGroup Q)
    (hnc : ∃ x y : Q, x * y ≠ y * x) : CFSG.IsQuasisimple Q := by
  have hperf : Group.IsPerfect Q := by
    rcases hs.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      apply hxy
      have : ⁅x, y⁆ ∈ commutator Q :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    · exact ⟨h⟩
  have hs' : IsSimpleGroup (Q ⧸ (⊥ : Subgroup Q)) := by
    have : Nontrivial (Q ⧸ (⊥ : Subgroup Q)) := QuotientGroup.quotientBot.symm.injective.nontrivial
    exact IsSimpleGroup.isSimpleGroup_of_surjective (QuotientGroup.mk' (⊥ : Subgroup Q))
      (QuotientGroup.mk'_surjective _)
  refine CFSG.LieType.CurtisTits.isQuasisimple_of_isSimpleGroup_quotient (⊥ : Subgroup Q) bot_le
    hperf hs' ?_
  obtain ⟨x, y, hxy⟩ := hnc
  refine ⟨x, y, fun h => hxy ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_bot,
    inv_mul_eq_one] at h
  exact h

omit [Finite V] in
theorem fixV_stable {K : Subgroup (MulAut V)} {t : MulAut V}
    (ht : t ∈ Subgroup.normalizer (K : Set (MulAut V))) {c : V} (hc : c ∈ fixV K) :
    t c ∈ fixV K :=
  CFSG.Quasithin.fixV_apply_mem_of_mem_normalizer ht hc

theorem eq_of_b51
    (h51 : AsB51) (hV : ∀ v : V, v ^ 2 = 1) {Γ K : Subgroup (MulAut V)} {ω : MulAut V}
    (hSQ : SQTKGroup ↥K) (hKΓ : K ≤ Γ) (hΓK : Γ ≤ Subgroup.normalizer (K : Set (MulAut V)))
    (hiso : Nonempty (↥K ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (↥K ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hCΓ : Γ ⊓ Subgroup.centralizer (K : Set (MulAut V)) = ⊥) (hcomm : commV K = ⊤)
    (hω3 : ω ^ 3 = 1) (hωf : ∀ v : V, ω v = v → v = 1) (hωΓ : ∀ g ∈ Γ, ω * g = g * ω)
    {D : Subgroup (MulAut V)} (hD : IsFFStarOffender Γ D) : Γ = K := by
  classical
  have hV' : ∀ v : V, v * v = 1 := fun v => by rw [← pow_two]; exact hV v
  have hs : IsSimpleGroup ↥K := by
    rcases hiso with he | he
    · obtain ⟨e⟩ := he
      exact (MulEquiv.isSimpleGroup_congr e).mpr inferInstance
    · obtain ⟨e⟩ := he
      exact (MulEquiv.isSimpleGroup_congr e).mpr L3Small.isSimpleGroup_Γ
  have hnc : ∃ a b : ↥K, a * b ≠ b * a := by
    rcases hiso with he | he
    · obtain ⟨e⟩ := he
      obtain ⟨a, b, hab'⟩ : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a :=
        ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, by decide⟩, ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by decide⟩,
          by decide⟩
      exact ⟨e.symm a, e.symm b, fun h => hab' (by simpa using congrArg e h)⟩
    · obtain ⟨e⟩ := he
      obtain ⟨a, b, hab'⟩ := L3Split.L3_not_comm
      exact ⟨e.symm a, e.symm b, fun h => hab' (by simpa using congrArg e h)⟩
  have hcard : Nat.card ↥K = 60 ∨ Nat.card ↥K = 168 := by
    rcases hiso with he | he
    · obtain ⟨e⟩ := he
      left
      rw [Nat.card_congr e.toEquiv, card_alternatingGroup1527d 5 (by norm_num)]
      rfl
    · obtain ⟨e⟩ := he
      right
      rw [Nat.card_congr e.toEquiv, L3Small.card_Γ]
  have hq := isQuasisimple_of_simple hs hnc
  have hfaith : ∀ Y ≤ Γ, IsPGroup 2 ↥Y → Y ⊓ Subgroup.centralizer (K : Set (MulAut V)) = ⊥ :=
    fun Y hY _ => le_bot_iff.mp (hCΓ ▸ inf_le_inf_right _ hY)
  obtain ⟨hb51, -, -⟩ := A6B51.b51Hyp_ffJ_sup hq hSQ hKΓ hΓK hfaith hD
  obtain ⟨⟨-, hcases⟩, -⟩ := h51 V hV _ _ hb51
  have hinner : (∀ t ∈ Γ, ∃ l ∈ K, ∀ x ∈ K, t * x * t⁻¹ = l * x * l⁻¹) → Γ = K := by
    intro h
    refine le_antisymm (fun t ht => ?_) hKΓ
    obtain ⟨l, hl, hlx⟩ := h t ht
    have h1 : l⁻¹ * t ∈ Γ ⊓ Subgroup.centralizer (K : Set (MulAut V)) := by
      refine ⟨Γ.mul_mem (Γ.inv_mem (hKΓ hl)) ht, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      have e := hlx x hx
      calc x * (l⁻¹ * t) = l⁻¹ * (l * x * l⁻¹) * t := by group
        _ = l⁻¹ * (t * x * t⁻¹) * t := by rw [e]
        _ = l⁻¹ * t * x := by group
    rw [hCΓ, Subgroup.mem_bot, inv_mul_eq_one] at h1
    rw [← h1]
    exact hl
  have hωK : ∀ k ∈ K, ω * k = k * ω := fun k hk => hωΓ k (hKΓ hk)
  have hωN : ω ∈ Subgroup.normalizer (K : Set (MulAut V)) := by
    refine A6L19.mem_normalizer_of_conj fun k hk => ?_
    rw [hωK k hk, mul_inv_cancel_right]
    exact hk
  have hfin : Finite (MulAut V) :=
    Finite.of_injective (fun φ : MulAut V => (φ : V → V)) DFunLike.coe_injective
  have hωC : ∀ c ∈ fixV K ⊓ (⊤ : Subgroup V), ω c ∈ fixV K ⊓ (⊤ : Subgroup V) :=
    fun c hc => ⟨fixV_stable hωN hc.1, trivial⟩
  have hωC' : ∀ c ∈ fixV K ⊓ (⊤ : Subgroup V), ω⁻¹ c ∈ fixV K ⊓ (⊤ : Subgroup V) :=
    fun c hc => ⟨fixV_stable ((Subgroup.normalizer _).inv_mem hωN) hc.1, trivial⟩
  have hωf' : ∀ u ∈ (⊤ : Subgroup V), ω u * u⁻¹ ∈ fixV K ⊓ (⊤ : Subgroup V) →
      u ∈ fixV K ⊓ (⊤ : Subgroup V) := fun u _ h =>
    mem_of_omega_mul_inv_mem hV' hω3 hωf hωC h
  rcases hcases with hi | hii | ⟨n, hiii⟩ | hiv
  ·
    have hpair := hi.2.1
    rw [hcomm] at hpair
    rcases hcard with h60 | h168
    · rcases b42_cases_60 h60 hpair with hsl2 | halt
      · obtain ⟨F, _, _, hF, π, hπ⟩ := hsl2
        refine hinner fun t ht => ?_
        exact SL2Twist.inner_of_natural_sl2_four (by rw [hF]; norm_num) hπ
          (fun _ _ => trivial) (fun _ _ => trivial) (fun c hc => hωC c hc)
          (fun c hc => hωC' c hc) hωK hωf' (fun _ _ => trivial) (fun _ _ => trivial)
          (fun c hc => ⟨fixV_stable (hΓK ht) hc.1, trivial⟩)
          (fun c hc => ⟨fixV_stable ((Subgroup.normalizer _).inv_mem (hΓK ht)) hc.1, trivial⟩)
          (hωΓ t ht) (fun l hl => (Subgroup.mem_normalizer_iff.mp (hΓK ht) l).mp hl)
      · exfalso
        obtain ⟨π, hπ⟩ := halt
        exact false_of_altDn5_of_omega hπ (fun _ _ => trivial)
          (fun c hc => hωC c hc) (fun c hc => hωC' c hc) hωK hωf'
    · exfalso
      obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod (b42_cases_168 h168 hpair)
      exact false_of_natural_sl3_of_omega hπ (fun _ _ => trivial)
        (fun c hc => hωC c hc) (fun c hc => hωC' c hc) hωK hωf'
  ·
    obtain ⟨-, n, F, _, _, hF, I, π, hindep, hsup, hR, -, -⟩ := hii
    have hc := A6B51.card_eq_of_realizesVia_nat (hR 0)
    rw [card_statedSL_three1527d] at hc
    have hF2 : Nat.card F = 2 := by
      rcases hcard with h60 | h168
      · exact absurd (hc.trans h60) sl3_card_ne_60
      · exact S1549D.eq_two_of_sl3_card (hc.trans h168)
    have hDS : DirectSumOfCopies K ⊤ ⊥ (FFModel.nat (StatedSL 3 (ZMod 2))) 2 := by
      refine ⟨I, π.comp (FFC.slOfZMod (FFC.ringEquivZModTwo F hF2) 3), fun _ => bot_le,
        fun i => ?_, by rw [bot_sup_eq, hsup, hcomm], fun i => FFC.realizesVia_zmod hF2 (hR i)⟩
      rw [bot_sup_eq]
      exact disjoint_iff.mp (hindep i)
    refine hinner fun t ht => ?_
    exact LRed5.inner_of_two_natural hDS (fun _ _ => trivial) (fun _ _ => trivial)
      (fun z hz => by rw [Subgroup.mem_bot.mp hz, map_one]; exact Subgroup.one_mem _)
      (fun z hz => by rw [Subgroup.mem_bot.mp hz, map_one]; exact Subgroup.one_mem _)
      (fun l hl => (Subgroup.mem_normalizer_iff.mp (hΓK ht) l).mp hl)
  ·
    exfalso
    obtain ⟨-, hn45, π, U₁, U₂, -, hR1, -⟩ := hiii
    have hc := A6B51.card_eq_of_realizesVia_nat hR1
    rcases hn45 with rfl | rfl
    · rw [A6B51.card_statedSL_four_two] at hc
      omega
    · rw [A6B51.card_statedSL_five_two] at hc
      omega
  ·
    exfalso
    obtain ⟨-, n, hn45, k, hk1, -, I, π, -, -, -, hR⟩ := hiv
    have hc := A6B51.card_eq_of_realizesVia_nat (hR ⟨0, hk1⟩)
    rcases hn45 with rfl | rfl
    · rw [A6B51.card_statedSL_four_two] at hc
      omega
    · rw [A6B51.card_statedSL_five_two] at hc
      omega

end Eq

section Offenders

variable {V : Type} [CommGroup V] [Finite V]

theorem card_le_four_of_elemAbelian {K A : Subgroup (MulAut V)}
    (hiso : Nonempty (↥K ≃* alternatingGroup (Fin 5)) ∨ Nonempty (↥K ≃* L3.Γ)) (hAK : A ≤ K)
    (hA : IsElemAbelian2 A) (h4 : 4 ≤ Nat.card A) :
    Nat.card A = 4 ∧ ∃ a ∈ A, ∃ b ∈ A, IsFourPair a b ∧ ∀ x ∈ A, InFour a b x := by
  classical
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => by rw [← pow_two]; exact hA.2 x hx
  obtain ⟨a, ha, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra h
    push Not at h
    have : A = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (h x hx)
    rw [this, Subgroup.card_bot] at h4
    omega
  obtain ⟨b, hb, hb1, hba⟩ : ∃ b ∈ A, b ≠ 1 ∧ b ≠ a := by
    by_contra h
    push Not at h
    have hle : (A : Set (MulAut V)) ⊆ {1, a} := fun x hx => by
      by_cases hx1 : x = 1
      · simp [hx1]
      · simp [h x hx hx1]
    have h1 : (A : Set (MulAut V)).ncard ≤ ({1, a} : Set (MulAut V)).ncard :=
      Set.ncard_le_ncard hle (Set.toFinite _)
    have h2 : ({1, a} : Set (MulAut V)).ncard ≤ 2 :=
      (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    have h0 : Nat.card ↥A = (A : Set (MulAut V)).ncard := Nat.card_coe_set_eq _
    omega
  have hab : IsFourPair a b :=
    ⟨hsq a ha, hsq b hb, ha1, hb1, fun h => hba h.symm, hA.1 a ha b hb⟩
  have hab' : IsFourPair (⟨a, hAK ha⟩ : ↥K) ⟨b, hAK hb⟩ :=
    ⟨Subtype.ext (hsq a ha), Subtype.ext (hsq b hb), fun h => ha1 (congrArg Subtype.val h),
      fun h => hb1 (congrArg Subtype.val h), fun h => hba (congrArg Subtype.val h).symm,
      Subtype.ext (hA.1 a ha b hb)⟩
  have hcent := (four_facts hiso hab').1
  have hin : ∀ x ∈ A, InFour a b x := fun x hx =>
    InFour.map K.subtype (hcent ⟨x, hAK hx⟩ ⟨Subtype.ext (hA.1 x hx a ha),
      Subtype.ext (hA.1 x hx b hb)⟩)
  refine ⟨le_antisymm ?_ h4, a, ha, b, hb, hab, hin⟩
  have hle : (A : Set (MulAut V)) ⊆ {1, a, b, a * b} := fun x hx => by
    rcases hin x hx with rfl | rfl | rfl | rfl <;> simp
  have h1 : (A : Set (MulAut V)).ncard ≤ ({1, a, b, a * b} : Set (MulAut V)).ncard :=
    Set.ncard_le_ncard hle (Set.toFinite _)
  have h2 : ({1, a, b, a * b} : Set (MulAut V)).ncard ≤ 4 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    refine Nat.add_le_add_right ((Set.ncard_insert_le _ _).trans ?_) 1
    refine Nat.add_le_add_right ((Set.ncard_insert_le _ _).trans ?_) 1
    rw [Set.ncard_singleton]
  have h0 : Nat.card ↥A = (A : Set (MulAut V)).ncard := Nat.card_coe_set_eq _
  omega

omit [Finite V] in
theorem fixV_stable_of_commute {B : Subgroup (MulAut V)} {ω : MulAut V}
    (hωB : ∀ b ∈ B, ω * b = b * ω) {h : V} (hh : h ∈ fixV B) : ω h ∈ fixV B := by
  intro b hb
  have e := congrArg (fun φ : MulAut V => φ h) (hωB b hb)
  simp only [MulAut.mul_apply] at e
  rw [← e, hh b hb]

theorem InFour.mem {G₀ : Type*} [Group G₀] {D : Subgroup G₀} {a b x : G₀} (ha : a ∈ D)
    (hb : b ∈ D) (h : InFour a b x) : x ∈ D := by
  rcases h with rfl | rfl | rfl | rfl
  · exact D.one_mem
  · exact ha
  · exact hb
  · exact D.mul_mem ha hb

theorem eq_or_eq_top_of_index_four (hV : ∀ v : V, v * v = 1) {ω : MulAut V} (hω3 : ω ^ 3 = 1)
    (hωf : ∀ v, ω v = v → v = 1) {H M : Subgroup V} (hH4 : H.index = 4) (hHM : H ≤ M)
    (hM : ∀ m ∈ M, ω m ∈ M) : M = H ∨ M = ⊤ := by
  by_cases htop : M = ⊤
  · exact Or.inr htop
  left
  have h4 := four_le_index hV hω3 hωf hM htop
  have hdvd : M.index ∣ H.index := Subgroup.index_dvd_of_le hHM
  rw [hH4] at hdvd
  have hM4 : M.index = 4 := le_antisymm (Nat.le_of_dvd (by norm_num) hdvd) h4
  have hrel := Subgroup.relIndex_mul_index hHM
  rw [hM4, hH4] at hrel
  have h1 : H.relIndex M = 1 := by omega
  exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hHM

end Offenders

end A6L74

open A6L74 in
theorem lem1374OneSimpleMod_of
    (h51 : AsB51) : Lem1374OneSimpleMod := by
  intro V _ _ hV Γ K R ω hSQ hKΓ hΓK hiso hCΓ hcomm hω3 hωf hωΓ hsyl hoff
  classical
  have hV' : ∀ v : V, v * v = 1 := fun v => by rw [← pow_two]; exact hV v
  have hfin : Finite (MulAut V) :=
    Finite.of_injective (fun φ : MulAut V => (φ : V → V)) DFunLike.coe_injective
  obtain ⟨D, hD⟩ := hoff
  have hDΓ : IsFFStarOffender Γ D := ⟨hD.1.trans hsyl.1, hD.2⟩
  have hΓeq := eq_of_b51 h51 hV hSQ hKΓ hΓK hiso hCΓ hcomm hω3 hωf hωΓ hDΓ
  have hRK : R ≤ K := hΓeq ▸ hsyl.1
  have hR2 : IsPGroup 2 ↥R := hsyl.2.1
  have hωR : ∀ r ∈ R, ω * r = r * ω := fun r hr => hωΓ r (hsyl.1 hr)
  have hcardK : Nat.card ↥K = 60 ∨ Nat.card ↥K = 168 := by
    rcases hiso with he | he
    · obtain ⟨e⟩ := he
      left
      rw [Nat.card_congr e.toEquiv, card_alternatingGroup1527d 5 (by norm_num)]
      rfl
    · obtain ⟨e⟩ := he
      right
      rw [Nat.card_congr e.toEquiv, L3Small.card_Γ]
  have hR8 : Nat.card ↥R ≤ 8 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR2
    have hdvd : Nat.card ↥R ∣ Nat.card ↥K := Subgroup.card_dvd_of_le hRK
    rw [hk] at hdvd ⊢
    have hk3 : k ≤ 3 := by
      by_contra h
      have h16 : 2 ^ 4 ∣ Nat.card ↥K := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
      rcases hcardK with h' | h' <;> rw [h'] at h16 <;> norm_num at h16
    calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
      _ = 8 := by norm_num
  have hoff4 : ∀ B, IsFFStarOffender R B → Nat.card ↥B = 4 ∧ (fixV B).index = 4 ∧
      ∃ a ∈ B, ∃ b ∈ B, IsFourPair a b ∧ ∀ x ∈ B, InFour a b x := by
    intro B hB
    have hωB : ∀ b ∈ B, ω * b = b * ω := fun b hb => hωR b (hB.1 hb)
    obtain ⟨hle, h4⟩ := four_le_card_of_offender hV' hω3 hωf hB hωB
    obtain ⟨hB4, a, ha, b, hb, hab, hin⟩ :=
      card_le_four_of_elemAbelian hiso (hB.1.trans hRK) hB.2.2.1 h4
    have hne : fixV B ≠ ⊤ := by
      intro htop
      apply hab.2.2.1
      refine MulEquiv.ext fun v => ?_
      have hv : v ∈ fixV B := by rw [htop]; exact Subgroup.mem_top v
      exact hv a ha
    have hi4 := four_le_index hV' hω3 hωf (fun h hh => fixV_stable_of_commute hωB hh) hne
    exact ⟨hB4, le_antisymm (hB4 ▸ hle) hi4, a, ha, b, hb, hab, hin⟩
  obtain ⟨hA4, hAi, a, ha, b, hb, hab, hin⟩ := hoff4 D hD
  have hωD : ∀ x ∈ D, ω * x = x * ω := fun x hx => hωR x (hD.1 hx)
  have hfixD : ∀ h ∈ fixV D, ω h ∈ fixV D := fun h hh => fixV_stable_of_commute hωD hh
  have htriv : ∀ g ∈ R, (∀ h ∈ fixV D, g h = h) → ∀ v, g v * v⁻¹ ∈ fixV D := by
    intro g hg hgH v
    obtain ⟨n, hn⟩ := hR2 ⟨g, hg⟩
    have hgn : g ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    exact mul_inv_mem_of_fix hV' hω3 hωf (hωR g hg) hfixD hAi hgH hgn v
  have hcommH : ∀ g ∈ R, ∀ g' ∈ R, (∀ h ∈ fixV D, g h = h) → (∀ h ∈ fixV D, g' h = h) →
      g * g' = g' * g := fun g hg g' hg' hgH hg'H =>
    commute_of_fix hgH hg'H (htriv g hg hgH) (htriv g' hg' hg'H)
  have habK : IsFourPair (⟨a, hRK (hD.1 ha)⟩ : ↥K) ⟨b, hRK (hD.1 hb)⟩ :=
    ⟨Subtype.ext hab.1, Subtype.ext hab.2.1, fun h => hab.2.2.1 (congrArg Subtype.val h),
      fun h => hab.2.2.2.1 (congrArg Subtype.val h),
      fun h => hab.2.2.2.2.1 (congrArg Subtype.val h), Subtype.ext hab.2.2.2.2.2⟩
  obtain ⟨hcentK, hnormK⟩ := four_facts hiso habK
  have hAC : D = R ⊓ centSub (fixV D) := by
    refine le_antisymm (le_inf hD.1 fun x hx v hv => hv x hx) ?_
    rintro g ⟨hgR, hgH⟩
    have hgH' : ∀ h ∈ fixV D, g h = h := hgH
    have hga := hcommH g hgR a (hD.1 ha) hgH' (fun h hh => hh a ha)
    have hgb := hcommH g hgR b (hD.1 hb) hgH' (fun h hh => hh b hb)
    have h1 := hcentK ⟨g, hRK hgR⟩ ⟨Subtype.ext hga, Subtype.ext hgb⟩
    exact InFour.mem ha hb (InFour.map K.subtype h1)
  have hu : ∀ B, IsFFStarOffender R B → B = D := by
    intro B hB
    obtain ⟨hB4, hBi, -⟩ := hoff4 B hB
    have hωB : ∀ x ∈ B, ω * x = x * ω := fun x hx => hωR x (hB.1 hx)
    by_cases hHB : fixV B = fixV D
    · have hBD : B ≤ D := by
        rw [hAC]
        refine fun x hx => ⟨hB.1 hx, fun v hv => ?_⟩
        rw [← hHB] at hv
        exact hv x hx
      exact Subgroup.eq_of_le_of_card_ge hBD (by rw [hA4, hB4])
    · exfalso
      have hMω : ∀ m ∈ fixV D ⊔ fixV B, ω m ∈ fixV D ⊔ fixV B := by
        intro m hm
        obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hm
        rw [map_mul]
        exact Subgroup.mul_mem_sup (hfixD y hy) (fixV_stable_of_commute hωB hz)
      have hsup : fixV D ⊔ fixV B = ⊤ := by
        rcases eq_or_eq_top_of_index_four hV' hω3 hωf hAi le_sup_left hMω with h | h
        · exfalso
          have hBD : fixV B ≤ fixV D := h ▸ le_sup_right
          have hrel := Subgroup.relIndex_mul_index hBD
          rw [hAi, hBi] at hrel
          have h1 : (fixV B).relIndex (fixV D) = 1 := by omega
          exact hHB (le_antisymm hBD (Subgroup.relIndex_eq_one.mp h1))
        · exact h
      have hinf : D ⊓ B = ⊥ := by
        rw [eq_bot_iff]
        rintro x ⟨hxD, hxB⟩
        rw [Subgroup.mem_bot]
        refine MulEquiv.ext fun v => ?_
        have hv : v ∈ fixV D ⊔ fixV B := by rw [hsup]; exact Subgroup.mem_top v
        obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hv
        rw [map_mul, hy x hxD, hz x hxB]
        rfl
      have hinj : Function.Injective (fun p : ↥D × ↥B =>
          (⟨(p.1 : MulAut V) * p.2, R.mul_mem (hD.1 p.1.2) (hB.1 p.2.2)⟩ : ↥R)) := by
        rintro ⟨d₁, b₁⟩ ⟨d₂, b₂⟩ h
        have h1 : (d₁ : MulAut V) * b₁ = d₂ * b₂ := congrArg Subtype.val h
        have h2 : (d₂ : MulAut V)⁻¹ * d₁ = b₂ * (b₁ : MulAut V)⁻¹ := by
          calc (d₂ : MulAut V)⁻¹ * d₁ = (d₂ : MulAut V)⁻¹ * (d₁ * b₁) * (b₁ : MulAut V)⁻¹ := by
                group
            _ = b₂ * (b₁ : MulAut V)⁻¹ := by rw [h1]; group
        have h3 : (d₂ : MulAut V)⁻¹ * d₁ ∈ D ⊓ B :=
          ⟨D.mul_mem (D.inv_mem d₂.2) d₁.2, h2 ▸ B.mul_mem b₂.2 (B.inv_mem b₁.2)⟩
        rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at h3
        have h4 : b₂ * (b₁ : MulAut V)⁻¹ = 1 := by rw [← h2, h3, inv_mul_cancel]
        rw [mul_inv_eq_one] at h4
        exact Prod.ext (Subtype.ext h3.symm) (Subtype.ext h4.symm)
      have hle := Nat.card_le_card_of_injective _ hinj
      rw [Nat.card_prod, hA4, hB4] at hle
      omega
  obtain ⟨g, ⟨hg3, hg1⟩, hga, hgb⟩ := hnormK
  refine ⟨D, hu, hAC, (g : MulAut V), g.2, ?_, fun h => hg1 (Subtype.ext h), ?_⟩
  · simpa using congrArg Subtype.val hg3
  · refine A6L19.mem_normalizer_of_conj fun x hx => ?_
    have hga' := InFour.mem ha hb (InFour.map K.subtype hga)
    have hgb' := InFour.mem ha hb (InFour.map K.subtype hgb)
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hga' hgb'
    rcases hin x hx with rfl | rfl | rfl | rfl
    · rw [mul_one, mul_inv_cancel]
      exact D.one_mem
    · exact hga'
    · exact hgb'
    · have e : (g : MulAut V) * (a * b) * (g : MulAut V)⁻¹ =
          ((g : MulAut V) * a * (g : MulAut V)⁻¹) * ((g : MulAut V) * b * (g : MulAut V)⁻¹) := by
        group
      rw [e]
      exact D.mul_mem hga' hgb'


end CFSG.Quasithin.H13.A6
