module

public import CFSG.Quasithin.EmptyFaithful.S152He6Pair
public import CFSG.Quasithin.EmptyFaithful.S152He6Rank

public section

namespace CFSG.Quasithin.He6

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1
open scoped MatrixGroups

section Prod

variable {G : Type*} [Group G]

theorem mem_sup_of_commute {A B : Subgroup G} (h : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) {z : G}
    (hz : z ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, z = a * b := by
  let S : Subgroup G :=
    { carrier := {z | ∃ a ∈ A, ∃ b ∈ B, z = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
        have := h a₂ ha₂ b₁ hb₁
        calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
          _ = a₁ * (a₂ * b₁) * b₂ := by rw [this]
          _ = a₁ * a₂ * (b₁ * b₂) := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have := h a⁻¹ (A.inv_mem ha) b hb
        calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
          _ = a⁻¹ * b⁻¹ := by
            have h2 := h a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)
            exact h2.symm }
  have hle : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact hle hz

end Prod

section Restrict

variable {W : Type} [CommGroup W]

@[expose] def restrAut (U : Subgroup W) (g : MulAut W) (h1 : ∀ u ∈ U, g u ∈ U)
    (h2 : ∀ u ∈ U, g⁻¹ u ∈ U) : MulAut ↥U where
  toFun u := ⟨g u, h1 u u.2⟩
  invFun u := ⟨g⁻¹ u, h2 u u.2⟩
  left_inv u := Subtype.ext (MulAut.inv_apply_self W g (u : W))
  right_inv u := Subtype.ext (MulAut.apply_inv_self W g (u : W))
  map_mul' a b := Subtype.ext (map_mul g (a : W) (b : W))

@[expose] def restrHom (A : Subgroup (MulAut W)) (U : Subgroup W)
    (hU : ∀ g ∈ A, ∀ u ∈ U, g u ∈ U) : ↥A →* MulAut ↥U :=
  MonoidHom.mk' (fun g => restrAut U g (hU g g.2) (hU g⁻¹ (A.inv_mem g.2)))
    (fun g h => by
      ext u
      rfl)

theorem restrHom_injective {A : Subgroup (MulAut W)} (hA : IsSimpleGroup ↥A) {U : Subgroup W}
    (hU : ∀ g ∈ A, ∀ u ∈ U, g u ∈ U) (hnt : ∃ g ∈ A, ∃ u ∈ U, g u ≠ u) :
    Function.Injective (restrHom A U hU) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases hA.eq_bot_or_eq_top_of_normal (restrHom A U hU).ker with h | h
  · exact h
  · exfalso
    obtain ⟨g, hg, u, hu, hne⟩ := hnt
    have hmem : (⟨g, hg⟩ : ↥A) ∈ (restrHom A U hU).ker := by
      rw [h]
      exact Subgroup.mem_top _
    have h1 : restrHom A U hU ⟨g, hg⟩ = 1 := hmem
    apply hne
    have := congrArg (fun m : MulAut ↥U => ((m ⟨u, hu⟩ : ↥U) : W)) h1
    exact this

omit [CommGroup W] in
theorem ne_bot_of_simple {G : Type*} [Group G] {A : Subgroup G} (hA : IsSimpleGroup ↥A) : A ≠ ⊥ := by
  intro h
  obtain ⟨x, hx⟩ := exists_ne (1 : ↥A)
  apply hx
  have : (x : G) ∈ (⊥ : Subgroup G) := h ▸ x.2
  exact Subtype.ext (Subgroup.mem_bot.1 this)

theorem index_restr_eq (U : Subgroup W) (g : MulAut W) (h1 : ∀ u ∈ U, g u ∈ U)
    (h2 : ∀ u ∈ U, g⁻¹ u ∈ U) :
    (fixV (Subgroup.zpowers (restrAut U g h1 h2))).index = Nat.card (cmt g U) := by
  rw [index_fixV_zpowers_eq_card_cmt]
  have hmap : (cmt (restrAut U g h1 h2) ⊤).map U.subtype = cmt g U := by
    ext v
    simp only [Subgroup.mem_map, mem_cmt, Subgroup.mem_top, true_and, Subgroup.subtype_apply]
    constructor
    · rintro ⟨w, ⟨u, rfl⟩, rfl⟩
      exact ⟨u, u.2, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, ⟨⟨u, hu⟩, rfl⟩, rfl⟩
  rw [← hmap]
  exact (Subgroup.card_map_of_injective U.subtype_injective).symm

theorem false_of_transvection [Finite W] {A : Subgroup (MulAut W)} (hAs : IsSimpleGroup ↥A)
    (hW : ∀ w : W, w * w = 1)
    (hfam : (∃ f : ℕ, Even f ∧ 2 ≤ f ∧ Nonempty (↥A ≃* PSL(2, GaloisField 2 f))) ∨
      (∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ≠ 7 ∧ Nonempty (↥A ≃* PSL(2, ZMod p))))
    {U : Subgroup W} (hU : ∀ g ∈ A, ∀ u ∈ U, g u ∈ U) {a : MulAut W} (haA : a ∈ A)
    (ha2 : a * a = 1) (hcard : Nat.card (cmt a U) = 2) : False := by
  have hne : cmt a U ≠ ⊥ := by
    intro h
    rw [h] at hcard
    simp at hcard
  have hnt : ∃ g ∈ A, ∃ u ∈ U, g u ≠ u := by
    refine ⟨a, haA, ?_⟩
    by_contra hall
    push Not at hall
    exact hne (cmt_eq_bot_iff.2 hall)
  have hinj := restrHom_injective hAs hU hnt
  have hWU : ∀ w : ↥U, w * w = 1 := fun w => Subtype.ext (hW w)
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hne (cmt_eq_bot_iff.2 fun u _ => rfl)
  have hx : orderOf (⟨a, haA⟩ : ↥A) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact Subtype.ext ha2)
      (fun h => ha1 (congrArg Subtype.val h))
  have h0 := no_transvection_of_l2 hWU hfam (restrHom A U hU) hinj hx
  apply h0
  have := index_restr_eq U a (hU a haA) (hU a⁻¹ (A.inv_mem haA))
  rw [hcard] at this
  exact this

end Restrict

namespace PairData

variable {W : Type} [CommGroup W] (P : PairData W)

theorem inf_eq_bot : P.A ⊓ P.A' = ⊥ := by
  have hnorm : ∀ g ∈ P.A, ∀ n ∈ P.A ⊓ P.A', g * n * g⁻¹ ∈ P.A ⊓ P.A' := by
    intro g hg n hn
    have h1 : g * n = n * g := P.comm g hg n hn.2
    have : g * n * g⁻¹ = n := by rw [h1]; group
    rw [this]
    exact hn
  rcases eq_bot_or_eq_of_normal P.simpA inf_le_left hnorm with h | h
  · exact h
  · exfalso
    have hAA' : P.A ≤ P.A' := by
      intro x hx
      have : x ∈ P.A ⊓ P.A' := by rw [h]; exact hx
      exact this.2
    have hab : ⁅P.A, P.A⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro x hx y hy
      rw [Subgroup.mem_bot, commutatorElement_def]
      have := P.comm x hx y (hAA' hy)
      rw [this]
      group
    exact ne_bot_of_simple P.simpA (by rw [← P.perfA, hab])

theorem exists_pair_of_inf_ne_bot {Tb Vb : Subgroup (MulAut W)} {τ : MulAut W}
    (hT2 : IsPGroup 2 Tb) (hVT : Vb ≤ Tb) (hVn : ∀ s ∈ Tb, ∀ v ∈ Vb, s * v * s⁻¹ ∈ Vb)
    (hτ : τ ∈ Tb) (hτA : ∀ x ∈ P.A, τ * x * τ⁻¹ ∈ P.A') (hτA' : ∀ x ∈ P.A', τ * x * τ⁻¹ ∈ P.A)
    (hne : Vb ⊓ (P.A ⊔ P.A') ≠ ⊥) :
    ∃ a ∈ P.A, ∃ a' ∈ P.A', a * a = 1 ∧ a' * a' = 1 ∧ a ≠ 1 ∧ a' ≠ 1 ∧ a * a' ∈ Vb := by
  obtain ⟨u, hu, hu1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hne
  obtain ⟨huV, huK⟩ := hu
  obtain ⟨n, hn⟩ := hT2 ⟨u, hVT huV⟩
  have hun : u ^ 2 ^ n = 1 := congrArg Subtype.val hn
  have hord : orderOf u ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hun
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
  have hj1 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hj
    exact hu1 (orderOf_eq_one_iff.1 hj)
  have h2dvd : 2 ∣ orderOf u := by
    rw [hj]
    exact dvd_pow_self 2 hj1
  have hord0 : orderOf u ≠ 0 := by
    rw [hj]
    positivity
  set z := u ^ (orderOf u / 2) with hz
  have hz2 : orderOf z = 2 := orderOf_pow_orderOf_div hord0 h2dvd
  have hzV : z ∈ Vb := Vb.pow_mem huV _
  have hzK : z ∈ P.A ⊔ P.A' := (P.A ⊔ P.A').pow_mem huK _
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, sq] at this
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  obtain ⟨a, ha, a'', ha'', hzaa⟩ := mem_sup_of_commute P.comm hzK
  have hcomm : a'' * a = a * a'' := (P.comm a ha a'' ha'').symm
  have hsq : (a * a) * (a'' * a'') = 1 := by
    have : z * z = (a * a) * (a'' * a'') := by
      rw [hzaa]
      calc a * a'' * (a * a'') = a * (a'' * a) * a'' := by group
        _ = a * (a * a'') * a'' := by rw [hcomm]
        _ = (a * a) * (a'' * a'') := by group
    rw [← this]
    exact hzz
  have haa : a * a = 1 := by
    have h1 : a * a ∈ P.A ⊓ P.A' := by
      refine ⟨P.A.mul_mem ha ha, ?_⟩
      have : a * a = (a'' * a'')⁻¹ := eq_inv_of_mul_eq_one_left hsq
      rw [this]
      exact P.A'.inv_mem (P.A'.mul_mem ha'' ha'')
    rw [P.inf_eq_bot, Subgroup.mem_bot] at h1
    exact h1
  have ha''a'' : a'' * a'' = 1 := by
    rw [haa, one_mul] at hsq
    exact hsq
  by_cases hA1 : a = 1
  ·
    have ha''1 : a'' ≠ 1 := by
      intro h
      apply hz1
      rw [hzaa, hA1, h, one_mul]
    have hzeq : z = a'' := by rw [hzaa, hA1, one_mul]
    refine ⟨τ * a'' * τ⁻¹, hτA' a'' ha'', a'', ha'', ?_, ha''a'', ?_, ha''1, ?_⟩
    · calc τ * a'' * τ⁻¹ * (τ * a'' * τ⁻¹) = τ * (a'' * a'') * τ⁻¹ := by group
        _ = 1 := by rw [ha''a'']; group
    · intro h
      apply ha''1
      have : τ * a'' * τ⁻¹ = 1 := h
      calc a'' = τ⁻¹ * (τ * a'' * τ⁻¹) * τ := by group
        _ = 1 := by rw [this]; group
    · rw [← hzeq]
      exact Vb.mul_mem (hVn τ hτ z hzV) hzV
  · by_cases hA'1 : a'' = 1
    ·
      have hzeq : z = a := by rw [hzaa, hA'1, mul_one]
      refine ⟨a, ha, τ * a * τ⁻¹, hτA a ha, haa, ?_, hA1, ?_, ?_⟩
      · calc τ * a * τ⁻¹ * (τ * a * τ⁻¹) = τ * (a * a) * τ⁻¹ := by group
          _ = 1 := by rw [haa]; group
      · intro h
        apply hA1
        have : τ * a * τ⁻¹ = 1 := h
        calc a = τ⁻¹ * (τ * a * τ⁻¹) * τ := by group
          _ = 1 := by rw [this]; group
      · rw [← hzeq]
        exact Vb.mul_mem hzV (hVn τ hτ z hzV)
    · refine ⟨a, ha, a'', ha'', haa, ha''a'', hA1, hA'1, ?_⟩
      rw [← hzaa]
      exact hzV

theorem trans_caseA_false [Finite W] {Tb Vb : Subgroup (MulAut W)} {τ : MulAut W}
    (hT2 : IsPGroup 2 Tb) (hVT : Vb ≤ Tb) (hVn : ∀ s ∈ Tb, ∀ v ∈ Vb, s * v * s⁻¹ ∈ Vb)
    (hτ : τ ∈ Tb) (hτA : ∀ x ∈ P.A, τ * x * τ⁻¹ ∈ P.A') (hτA' : ∀ x ∈ P.A', τ * x * τ⁻¹ ∈ P.A)
    (hne : Vb ⊓ (P.A ⊔ P.A') ≠ ⊥) (hz : ∀ v ∈ Vb, Nat.card (cmt v ⊤) ≤ 2) : False := by
  obtain ⟨a, ha, a', ha', ha2, -, ha1, ha'1, hmem⟩ :=
    P.exists_pair_of_inf_ne_bot hT2 hVT hVn hτ hτA hτA' hne
  exact P.pair_core_le_two ha ha' ha2 ha1 ha'1 (hz _ hmem)

theorem shape_caseA_false [Finite W] {Tb Vb : Subgroup (MulAut W)} {τ : MulAut W}
    (hT2 : IsPGroup 2 Tb) (hVT : Vb ≤ Tb) (hVn : ∀ s ∈ Tb, ∀ v ∈ Vb, s * v * s⁻¹ ∈ Vb)
    (hτ : τ ∈ Tb) (hτA : ∀ x ∈ P.A, τ * x * τ⁻¹ ∈ P.A') (hτA' : ∀ x ∈ P.A', τ * x * τ⁻¹ ∈ P.A)
    (hne : Vb ⊓ (P.A ⊔ P.A') ≠ ⊥) (hz : ∀ v ∈ Vb, Nat.card (cmt v ⊤) ≤ 4)
    (hfam : (∃ f : ℕ, Even f ∧ 2 ≤ f ∧ Nonempty (↥P.A ≃* PSL(2, GaloisField 2 f))) ∨
      (∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ≠ 7 ∧ Nonempty (↥P.A ≃* PSL(2, ZMod p))))
    (hfam' : (∃ f : ℕ, Even f ∧ 2 ≤ f ∧ Nonempty (↥P.A' ≃* PSL(2, GaloisField 2 f))) ∨
      (∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ≠ 7 ∧ Nonempty (↥P.A' ≃* PSL(2, ZMod p)))) : False := by
  obtain ⟨a, ha, a', ha', ha2, ha'2, ha1, ha'1, hmem⟩ :=
    P.exists_pair_of_inf_ne_bot hT2 hVT hVn hτ hτA hτA' hne
  rcases P.pair_core_le_four ha ha' ha2 ha1 ha'1 (hz _ hmem) with ⟨U, hU, hcard⟩ | ⟨U, hU, hcard⟩
  · exact false_of_transvection P.simpA P.hW hfam hU ha ha2 hcard
  · exact false_of_transvection P.simpA' P.hW hfam' hU ha' ha'2 hcard

end PairData

end CFSG.Quasithin.He6
