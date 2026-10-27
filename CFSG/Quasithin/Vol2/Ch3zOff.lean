module

public import CFSG.Quasithin.Vol2.Ch3zWreath
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open G6

namespace Ch3z

section Finite

@[expose] def fixCore (m : ℕ) (P : Subgroup (Equiv.Perm (Fin m))) : Subgroup (coreMod m) where
  carrier := {v | ∀ a ∈ P, coreAct m a v = v}
  one_mem' := fun a _ => map_one (coreAct m a)
  mul_mem' := fun {x y} hx hy a ha => by rw [map_mul, hx a ha, hy a ha]
  inv_mem' := fun {x} hx a ha => by rw [map_inv, hx a ha]

theorem alt3_trivial : ∀ a : Equiv.Perm (Fin 3), a * a = 1 → Equiv.Perm.sign a = 1 → a = 1 := by
  decide

private def dt5 : Finset (Equiv.Perm (Fin 5)) :=
  Finset.univ.filter fun a => a ≠ 1 ∧ a * a = 1 ∧ Equiv.Perm.sign a = 1

set_option synthInstance.maxSize 4096 in
private theorem fix_one5 : ∀ a ∈ dt5,
    Nat.card {v : coreMod 5 // coreAct 5 a v = v} ≤ 4 := by
  intro a ha
  rw [Nat.card_eq_fintype_card]
  revert a
  decide +kernel

set_option synthInstance.maxSize 4096 in
private theorem fix_two5 : ∀ a ∈ dt5, ∀ b ∈ dt5, a ≠ b → a * b = b * a →
    Nat.card {v : coreMod 5 // coreAct 5 a v = v ∧ coreAct 5 b v = v} ≤ 2 := by
  intro a ha b hb hab hc
  rw [Nat.card_eq_fintype_card]
  revert a b
  decide +kernel

theorem card_coreMod_five : Nat.card (coreMod 5) = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_alt_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem mem_dt5 {a : Equiv.Perm (Fin 5)} (h1 : a ≠ 1) (h2 : a * a = 1)
    (h3 : a ∈ alternatingGroup (Fin 5)) : a ∈ dt5 := by
  unfold dt5
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, h1, h2, Equiv.Perm.mem_alternatingGroup.mp h3⟩

private theorem card_fixCore_le_of_mem {P : Subgroup (Equiv.Perm (Fin 5))} {a : Equiv.Perm (Fin 5)}
    (ha : a ∈ P) : Nat.card (fixCore 5 P) ≤ Nat.card {v : coreMod 5 // coreAct 5 a v = v} := by
  refine Nat.card_le_card_of_injective (fun v => ⟨(v : coreMod 5), v.2 a ha⟩) ?_
  intro x y hxy
  apply Subtype.ext
  have h := congrArg Subtype.val hxy
  exact h

private theorem card_fixCore_le_of_mem₂ {P : Subgroup (Equiv.Perm (Fin 5))}
    {a b : Equiv.Perm (Fin 5)} (ha : a ∈ P) (hb : b ∈ P) :
    Nat.card (fixCore 5 P) ≤
      Nat.card {v : coreMod 5 // coreAct 5 a v = v ∧ coreAct 5 b v = v} := by
  refine Nat.card_le_card_of_injective (fun v => ⟨(v : coreMod 5), v.2 a ha, v.2 b hb⟩) ?_
  intro x y hxy
  apply Subtype.ext
  have h := congrArg Subtype.val hxy
  exact h

theorem sb2_five (P : Subgroup (Equiv.Perm (Fin 5))) (hPA : P ≤ alternatingGroup (Fin 5))
    (hPe : ∀ a ∈ P, a * a = 1) (hP : P ≠ ⊥) :
    2 * (Nat.card P * Nat.card (fixCore 5 P)) ≤ Nat.card (coreMod 5) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hP
  have haP' : (a : Equiv.Perm (Fin 5)) ∈ P := a.2
  have ha1' : (a : Equiv.Perm (Fin 5)) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hadt : (a : Equiv.Perm (Fin 5)) ∈ dt5 := mem_dt5 ha1' (hPe a haP') (hPA haP')
  have hfix1 : Nat.card (fixCore 5 P) ≤ 4 :=
    (card_fixCore_le_of_mem haP').trans (fix_one5 _ hadt)
  rw [card_coreMod_five]
  by_cases hsub : ∀ b ∈ P, b = 1 ∨ b = (a : Equiv.Perm (Fin 5))
  · have hcard : Nat.card P ≤ 2 := by
      have h2 : Nat.card P ≤ Nat.card Bool := by
        refine Nat.card_le_card_of_injective
          (fun b : ↥P => if (b : Equiv.Perm (Fin 5)) = 1 then true else false) ?_
        intro x y hxy
        simp only at hxy
        refine Subtype.ext ?_
        rcases hsub x x.2 with hx | hx <;> rcases hsub y y.2 with hy | hy
        · rw [hx, hy]
        · rw [hx, hy] at hxy
          simp [ha1'] at hxy
        · rw [hx, hy] at hxy
          simp [ha1'] at hxy
        · rw [hx, hy]
      have h3 : Nat.card Bool = 2 := by
        rw [Nat.card_eq_fintype_card]
        rfl
      rw [h3] at h2
      exact h2
    calc 2 * (Nat.card P * Nat.card (fixCore 5 P)) ≤ 2 * (2 * 4) := by gcongr
      _ = 16 := by norm_num
  · push Not at hsub
    obtain ⟨b, hbP, hb1, hba⟩ := hsub
    have hbdt : b ∈ dt5 := mem_dt5 hb1 (hPe b hbP) (hPA hbP)
    have hcomm : (a : Equiv.Perm (Fin 5)) * b = b * a := by
      have h1 := hPe ((a : Equiv.Perm (Fin 5)) * b) (P.mul_mem haP' hbP)
      have ha2 := hPe a haP'
      have hb2 := hPe b hbP
      have ha' : (a : Equiv.Perm (Fin 5))⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
      have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
      have := inv_eq_of_mul_eq_one_right h1
      rw [mul_inv_rev, ha', hb'] at this
      exact this.symm
    have hfix2 : Nat.card (fixCore 5 P) ≤ 2 :=
      (card_fixCore_le_of_mem₂ haP' hbP).trans (fix_two5 _ hadt b hbdt (Ne.symm hba) hcomm)
    have hcard : Nat.card P ≤ 4 := by
      have hdvd : Nat.card P ∣ 60 := by
        rw [← card_alt_five]
        exact Subgroup.card_dvd_of_le hPA
      have hpg : IsPGroup 2 P := fun x =>
        ⟨1, Subtype.ext (by simpa [pow_one, sq] using hPe x x.2)⟩
      obtain ⟨n, hn⟩ := hpg.exists_card_eq
      rw [hn] at hdvd ⊢
      by_contra hlt
      push Not at hlt
      have h3 : 3 ≤ n := by
        by_contra hn3
        push Not at hn3
        interval_cases n <;> simp at hlt
      have h8 : 8 ∣ 2 ^ n := by
        have := pow_dvd_pow 2 h3
        simpa using this
      have := h8.trans hdvd
      omega
    calc 2 * (Nat.card P * Nat.card (fixCore 5 P)) ≤ 2 * (4 * 2) := by gcongr
      _ = 16 := by norm_num

theorem exists_odd_of_offender (m : ℕ) (hm : m = 3 ∨ m = 5) (P : Subgroup (Equiv.Perm (Fin m)))
    (hPe : ∀ a ∈ P, a * a = 1) (hP : P ≠ ⊥)
    (hoff : Nat.card (coreMod m) ≤ Nat.card P * Nat.card (fixCore m P)) :
    ∃ a ∈ P, Equiv.Perm.sign a = -1 := by
  by_contra hcon
  push Not at hcon
  have hPA : P ≤ alternatingGroup (Fin m) := fun a ha => by
    rw [Equiv.Perm.mem_alternatingGroup]
    rcases Int.units_eq_one_or (Equiv.Perm.sign a) with h | h
    · exact h
    · exact absurd h (hcon a ha)
  rcases hm with rfl | rfl
  · apply hP
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    exact alt3_trivial a (hPe a ha) (Equiv.Perm.mem_alternatingGroup.mp (hPA ha))
  · have h1 := sb2_five P hPA hPe hP
    have hpos : 0 < Nat.card (coreMod 5) := Nat.card_pos
    omega

end Finite

section Transport

variable {V : Type} [CommGroup V]

theorem fixCore_map_eq {H : Subgroup (MulAut V)} {m : ℕ} (θ : ↥H ≃* Equiv.Perm (Fin m))
    (β : ↥(coreMod m) →* V) (hβinj : Function.Injective β)
    (hβeq : ∀ (x : ↥H) (u : ↥(coreMod m)), β (coreAct m (θ x) u) = (x : MulAut V) (β u))
    (A : Subgroup (MulAut V)) (hAH : A ≤ H) :
    (fixCore m ((A.subgroupOf H).map θ.toMonoidHom)).map β = fixV A ⊓ β.range := by
  ext v
  rw [Subgroup.mem_map, Subgroup.mem_inf, mem_fixV]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun x hx => ?_, ⟨u, rfl⟩⟩
    have hxP : θ ⟨x, hAH hx⟩ ∈ (A.subgroupOf H).map θ.toMonoidHom :=
      ⟨⟨x, hAH hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have := hu _ hxP
    have h2 := hβeq ⟨x, hAH hx⟩ u
    rw [this] at h2
    exact h2.symm
  · rintro ⟨hv, u, rfl⟩
    refine ⟨u, fun a ha => ?_, rfl⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    apply hβinj
    show β (coreAct m (θ x) u) = β u
    rw [hβeq]
    exact hv _ (Subgroup.mem_subgroupOf.mp hx)

theorem card_map_subgroupOf {H A : Subgroup (MulAut V)} {m : ℕ} (θ : ↥H ≃* Equiv.Perm (Fin m))
    (hAH : A ≤ H) : Nat.card ((A.subgroupOf H).map θ.toMonoidHom) = Nat.card A := by
  rw [Subgroup.card_map_of_injective θ.injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv

theorem card_fixCore_eq {H : Subgroup (MulAut V)} {m : ℕ} (θ : ↥H ≃* Equiv.Perm (Fin m))
    (β : ↥(coreMod m) →* V) (hβinj : Function.Injective β)
    (hβeq : ∀ (x : ↥H) (u : ↥(coreMod m)), β (coreAct m (θ x) u) = (x : MulAut V) (β u))
    (A : Subgroup (MulAut V)) (hAH : A ≤ H) :
    Nat.card (fixCore m ((A.subgroupOf H).map θ.toMonoidHom)) = Nat.card ↥(fixV A ⊓ β.range) := by
  rw [← fixCore_map_eq θ β hβinj hβeq A hAH, Subgroup.card_map_of_injective hβinj]

theorem image_elemAbelian {H A : Subgroup (MulAut V)} {m : ℕ} (θ : ↥H ≃* Equiv.Perm (Fin m))
    (hAe : IsElemAbelian2 A) : ∀ a ∈ (A.subgroupOf H).map θ.toMonoidHom, a * a = 1 := by
  rintro _ ⟨x, hx, rfl⟩
  have h2 := hAe.2 x.1 (Subgroup.mem_subgroupOf.mp hx)
  have : x * x = 1 := Subtype.ext (by simpa [sq] using h2)
  show θ x * θ x = 1
  rw [← map_mul, this, map_one]

theorem image_ne_bot {H A : Subgroup (MulAut V)} {m : ℕ} (θ : ↥H ≃* Equiv.Perm (Fin m))
    (hAH : A ≤ H) (hA1 : A ≠ ⊥) : (A.subgroupOf H).map θ.toMonoidHom ≠ ⊥ := by
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA1
  intro hbot
  have hmem : θ ⟨(a : MulAut V), hAH a.2⟩ ∈ (A.subgroupOf H).map θ.toMonoidHom :=
    ⟨⟨(a : MulAut V), hAH a.2⟩, Subgroup.mem_subgroupOf.mpr a.2, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  apply ha
  have h1 : (⟨(a : MulAut V), hAH a.2⟩ : ↥H) = 1 := θ.injective (hmem.trans (map_one θ).symm)
  have h3 := congrArg Subtype.val h1
  exact Subtype.ext h3

end Transport

section OneBlock

variable {V : Type} [CommGroup V]

theorem exists_odd_block {H P : Subgroup (MulAut V)} {U : Subgroup V} {m : ℕ} (hm : m = 3 ∨ m = 5)
    (θ : ↥H ≃* Equiv.Perm (Fin m)) (β : ↥(coreMod m) →* V)
    (hβeq : ∀ (x : ↥H) (u : ↥(coreMod m)), β (coreAct m (θ x) u) = (x : MulAut V) (β u))
    (hβr : β.range = U) (hβk : β.ker = ⊥)
    (hPH : P ≤ H) (hPe : IsElemAbelian2 P) (hP1 : P ≠ ⊥)
    (hoff : Nat.card U ≤ Nat.card P * Nat.card ↥(fixV P ⊓ U)) :
    ∃ p ∈ P, ∃ hp : p ∈ H, Equiv.Perm.sign (θ ⟨p, hp⟩) = -1 := by
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have : u ∈ β.ker := hu
    rw [hβk] at this
    simpa using this
  have hcardU : Nat.card (coreMod m) = Nat.card U := by
    rw [← hβr]
    exact Nat.card_congr (Equiv.ofInjective β hβinj)
  have hfix := card_fixCore_eq θ β hβinj hβeq P hPH
  rw [hβr] at hfix
  obtain ⟨a, haQ, hsg⟩ := exists_odd_of_offender m hm _ (image_elemAbelian θ hPe)
    (image_ne_bot θ hPH hP1)
    (by rw [hcardU, card_map_subgroupOf θ hPH, hfix]; exact hoff)
  obtain ⟨x, hxP, rfl⟩ := Subgroup.mem_map.mp haQ
  exact ⟨x.1, Subgroup.mem_subgroupOf.mp hxP, x.2, hsg⟩

theorem exists_odd_sym {X A : Subgroup (MulAut V)} {m : ℕ} (hm : m = 3 ∨ m = 5)
    (θ : ↥X ≃* Equiv.Perm (Fin m)) (β : ↥(coreMod m) →* V)
    (hβeq : ∀ (x : ↥X) (u : ↥(coreMod m)), β (coreAct m (θ x) u) = (x : MulAut V) (β u))
    (hβr : β.range = ⊤) (hβk : β.ker = ⊥) (hAX : A ≤ X) (hAe : IsElemAbelian2 A) (hA1 : A ≠ ⊥)
    (hoff : Nat.card V ≤ Nat.card A * Nat.card (fixV A)) :
    ∃ a ∈ A, ∃ ha : a ∈ X, Equiv.Perm.sign (θ ⟨a, ha⟩) = -1 :=
  exists_odd_block hm θ β hβeq hβr hβk hAX hAe hA1 (by
    rw [inf_top_eq, Subgroup.card_top]
    exact hoff)

end OneBlock

section TwoBlocksCount

variable {V : Type} [CommGroup V]

theorem card_sup_mul_card_inf_comm (S T : Subgroup V) :
    Nat.card ↥(S ⊔ T) * Nat.card ↥(S ⊓ T) = Nat.card S * Nat.card T := by
  have e1 := Subgroup.relIndex_mul_card T (S ⊔ T)
  have e2 := Subgroup.relIndex_mul_card T S
  rw [inf_eq_left.mpr le_sup_right] at e1
  have : T.Normal := Subgroup.normal_of_isMulCommutative T
  rw [Subgroup.relIndex_sup_right] at e1
  rw [inf_comm] at e2
  calc Nat.card ↥(S ⊔ T) * Nat.card ↥(S ⊓ T)
      = (T.relIndex S * Nat.card T) * Nat.card ↥(S ⊓ T) := by rw [e1]
    _ = Nat.card T * (T.relIndex S * Nat.card ↥(S ⊓ T)) := by ring
    _ = Nat.card T * Nat.card S := by rw [e2]
    _ = Nat.card S * Nat.card T := mul_comm _ _

theorem card_fixV_split {V₁ V₂ : Subgroup V} (hsup : V₁ ⊔ V₂ = ⊤) (hinf : V₁ ⊓ V₂ = ⊥)
    (B : Subgroup (MulAut V)) (hB₁ : ∀ b ∈ B, ∀ e ∈ V₁, b e ∈ V₁)
    (hB₂ : ∀ b ∈ B, ∀ e ∈ V₂, b e ∈ V₂) :
    Nat.card (fixV B) = Nat.card ↥(fixV B ⊓ V₁) * Nat.card ↥(fixV B ⊓ V₂) := by
  have hle : fixV B ≤ (fixV B ⊓ V₁) ⊔ (fixV B ⊓ V₂) := by
    intro v hv
    have hv' : v ∈ V₁ ⊔ V₂ := by rw [hsup]; trivial
    obtain ⟨e₁, he₁, e₂, he₂, rfl⟩ := Subgroup.mem_sup.mp hv'
    have key : ∀ b ∈ B, b e₁ = e₁ ∧ b e₂ = e₂ := by
      intro b hb
      have h1 := hv b hb
      rw [map_mul] at h1
      have hmem : (b e₁) * e₁⁻¹ ∈ V₁ ⊓ V₂ := by
        refine ⟨V₁.mul_mem (hB₁ b hb e₁ he₁) (V₁.inv_mem he₁), ?_⟩
        have : (b e₁) * e₁⁻¹ = e₂ * (b e₂)⁻¹ := by
          have h2 : (b e₁) * (b e₂) = e₁ * e₂ := h1
          have h3 : (b e₁) * e₁⁻¹ * (b e₂) = e₂ := by
            calc (b e₁) * e₁⁻¹ * (b e₂) = ((b e₁) * (b e₂)) * e₁⁻¹ := by rw [mul_right_comm]
              _ = e₁ * e₂ * e₁⁻¹ := by rw [h2]
              _ = e₂ := by rw [mul_comm e₁ e₂, mul_assoc, mul_inv_cancel, mul_one]
          exact eq_mul_inv_of_mul_eq h3
        rw [this]
        exact V₂.mul_mem he₂ (V₂.inv_mem (hB₂ b hb e₂ he₂))
      rw [hinf, Subgroup.mem_bot, mul_inv_eq_one] at hmem
      refine ⟨hmem, ?_⟩
      rw [hmem] at h1
      exact mul_left_cancel h1
    exact Subgroup.mul_mem_sup ⟨fun b hb => (key b hb).1, he₁⟩ ⟨fun b hb => (key b hb).2, he₂⟩
  have hle' : (fixV B ⊓ V₁) ⊔ (fixV B ⊓ V₂) ≤ fixV B :=
    sup_le inf_le_left inf_le_left
  have heq : (fixV B ⊓ V₁) ⊔ (fixV B ⊓ V₂) = fixV B := le_antisymm hle' hle
  have hbot : (fixV B ⊓ V₁) ⊓ (fixV B ⊓ V₂) = ⊥ := by
    rw [eq_bot_iff, ← hinf]
    exact inf_le_inf inf_le_right inf_le_right
  have h := card_sup_mul_card_inf_comm (fixV B ⊓ V₁) (fixV B ⊓ V₂)
  rw [heq, hbot, Subgroup.card_bot, mul_one] at h
  exact h

theorem card_split {V₁ V₂ : Subgroup V} (hsup : V₁ ⊔ V₂ = ⊤) (hinf : V₁ ⊓ V₂ = ⊥) :
    Nat.card V = Nat.card V₁ * Nat.card V₂ := by
  have h := card_sup_mul_card_inf_comm V₁ V₂
  rw [hsup, hinf, Subgroup.card_bot, mul_one, Subgroup.card_top] at h
  exact h

end TwoBlocksCount

section Proj

variable {V : Type} [CommGroup V]

@[expose] def projSub (H₁ H₂ A : Subgroup (MulAut V))
    (hc : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a) : Subgroup (MulAut V) where
  carrier := {x | x ∈ H₁ ∧ ∃ y ∈ H₂, x * y ∈ A}
  one_mem' := ⟨H₁.one_mem, 1, H₂.one_mem, by simp⟩
  mul_mem' := by
    rintro x x' ⟨hx, y, hy, hxy⟩ ⟨hx', y', hy', hxy'⟩
    refine ⟨H₁.mul_mem hx hx', y * y', H₂.mul_mem hy hy', ?_⟩
    have e : x * x' * (y * y') = (x * y) * (x' * y') := by
      have h1 : x' * y = y * x' := hc x' hx' y hy
      calc x * x' * (y * y') = x * (x' * y) * y' := by group
        _ = x * (y * x') * y' := by rw [h1]
        _ = (x * y) * (x' * y') := by group
    rw [e]
    exact A.mul_mem hxy hxy'
  inv_mem' := by
    rintro x ⟨hx, y, hy, hxy⟩
    refine ⟨H₁.inv_mem hx, y⁻¹, H₂.inv_mem hy, ?_⟩
    have : x⁻¹ * y⁻¹ = (x * y)⁻¹ := by rw [hc x hx y hy, mul_inv_rev]
    rw [this]
    exact A.inv_mem hxy

variable {H₁ H₂ A : Subgroup (MulAut V)} {hc : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a}

theorem projSub_le : projSub H₁ H₂ A hc ≤ H₁ := fun _ hx => hx.1

theorem inf_eq_one_of_mul {a b : MulAut V} (hinf : H₁ ⊓ H₂ = ⊥) (ha : a ∈ H₁) (hb : b ∈ H₂)
    (hab : a * b = 1) : a = 1 ∧ b = 1 := by
  have h1 : a ∈ H₁ ⊓ H₂ := ⟨ha, by
    have := H₂.inv_mem hb
    rwa [← eq_inv_of_mul_eq_one_left hab] at this⟩
  rw [hinf, Subgroup.mem_bot] at h1
  subst h1
  exact ⟨rfl, by simpa using hab⟩

theorem projSub_elemAbelian (hinf : H₁ ⊓ H₂ = ⊥) (hAe : IsElemAbelian2 A) :
    IsElemAbelian2 (projSub H₁ H₂ A hc) := by
  refine ⟨?_, ?_⟩
  · rintro x ⟨hx, y, hy, hxy⟩ x' ⟨hx', y', hy', hxy'⟩
    have E : (x * y) * (x' * y') = (x' * y') * (x * y) := hAe.1 _ hxy _ hxy'
    have hxx' : x * x' * (y * y') = x' * x * (y' * y) := by
      have e1 : x * x' * (y * y') = (x * y) * (x' * y') := by
        have h1 : x' * y = y * x' := hc x' hx' y hy
        calc x * x' * (y * y') = x * (x' * y) * y' := by group
          _ = x * (y * x') * y' := by rw [h1]
          _ = (x * y) * (x' * y') := by group
      have e2 : x' * x * (y' * y) = (x' * y') * (x * y) := by
        have h1 : x * y' = y' * x := hc x hx y' hy'
        calc x' * x * (y' * y) = x' * (x * y') * y := by group
          _ = x' * (y' * x) * y := by rw [h1]
          _ = (x' * y') * (x * y) := by group
      rw [e1, e2, E]
    have hu : (x' * x)⁻¹ * (x * x') ∈ H₁ :=
      H₁.mul_mem (H₁.inv_mem (H₁.mul_mem hx' hx)) (H₁.mul_mem hx hx')
    have hw : (y * y') * (y' * y)⁻¹ ∈ H₂ :=
      H₂.mul_mem (H₂.mul_mem hy hy') (H₂.inv_mem (H₂.mul_mem hy' hy))
    have huw : (x' * x)⁻¹ * (x * x') * ((y * y') * (y' * y)⁻¹) = 1 := by
      calc (x' * x)⁻¹ * (x * x') * ((y * y') * (y' * y)⁻¹)
          = (x' * x)⁻¹ * ((x * x') * (y * y')) * (y' * y)⁻¹ := by group
        _ = (x' * x)⁻¹ * ((x' * x) * (y' * y)) * (y' * y)⁻¹ := by rw [hxx']
        _ = 1 := by group
    have := (inf_eq_one_of_mul hinf hu hw huw).1
    exact (inv_mul_eq_one.mp this).symm
  · rintro x ⟨hx, y, hy, hxy⟩
    have hsq : (x * y) ^ 2 = 1 := hAe.2 _ hxy
    have hxy2 : x ^ 2 * y ^ 2 = 1 := by
      have : (x * y) ^ 2 = x ^ 2 * y ^ 2 := by
        have h1 : x * y = y * x := hc x hx y hy
        simp only [pow_two]
        calc x * y * (x * y) = x * (y * x) * y := by group
          _ = x * (x * y) * y := by rw [h1]
          _ = x * x * (y * y) := by group
      rw [← this]
      exact hsq
    exact (inf_eq_one_of_mul hinf (H₁.pow_mem hx 2) (H₂.pow_mem hy 2) hxy2).1

theorem exists_decomp (hc' : ∀ a ∈ H₂, ∀ b ∈ H₁, a * b = b * a) {a : MulAut V} (haA : a ∈ A)
    (haJ : a ∈ H₁ ⊔ H₂) : ∃ x ∈ projSub H₁ H₂ A hc, ∃ y ∈ projSub H₂ H₁ A hc', a = x * y := by
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_sup_of_commute hc haJ
  refine ⟨x, ⟨hx, y, hy, haA⟩, y, ⟨hy, x, hx, ?_⟩, rfl⟩
  rw [← hc x hx y hy]
  exact haA

end Proj

section TwoBlkOffender

variable {V : Type} [CommGroup V] [Finite V] {X H₁ H₂ A : Subgroup (MulAut V)} {m : ℕ}

omit [Finite V] in
theorem TwoBlk.preserve₂ (h : TwoBlk X H₁ H₂ m) {y : MulAut V} (hy : y ∈ H₁ ⊔ H₂) {w : V}
    (hw : w ∈ commV H₂) : y w ∈ commV H₂ := by
  have h' := h.symm
  rw [sup_comm] at hy
  exact h'.preserve₁ hy hw

omit [Finite V] in
theorem TwoBlk.fixV_inf_eq (h : TwoBlk X H₁ H₂ m) (hAJ : A ≤ H₁ ⊔ H₂) :
    fixV A ⊓ commV H₁ = fixV (projSub H₁ H₂ A h.comm) ⊓ commV H₁ := by
  have hc' : ∀ a ∈ H₂, ∀ b ∈ H₁, a * b = b * a := fun a ha b hb => (h.comm b hb a ha).symm
  ext e
  simp only [Subgroup.mem_inf, mem_fixV]
  constructor
  · rintro ⟨hfix, he⟩
    refine ⟨fun x hx => ?_, he⟩
    obtain ⟨hxH, y, hy, hxyA⟩ := hx
    have := hfix _ hxyA
    rw [MulAut.mul_apply, h.act₂ y hy e he] at this
    exact this
  · rintro ⟨hfix, he⟩
    refine ⟨fun a ha => ?_, he⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_decomp (hc := h.comm) hc' ha (hAJ ha)
    rw [MulAut.mul_apply, h.act₂ y hy.1 e he]
    exact hfix x hx

theorem card_eq_of_le_mul {a b c d : ℕ} (hc : 0 < c) (hd : 0 < d) (hab : a ≤ c) (hbd : b ≤ d)
    (h : c * d ≤ a * b) : a = c ∧ b = d := by
  constructor
  · by_contra hne
    have hlt : a < c := lt_of_le_of_ne hab hne
    have : a * b < c * d := by
      calc a * b ≤ a * d := Nat.mul_le_mul_left a hbd
        _ < c * d := Nat.mul_lt_mul_of_pos_right hlt hd
    omega
  · by_contra hne
    have hlt : b < d := lt_of_le_of_ne hbd hne
    have : a * b < c * d := by
      calc a * b ≤ c * b := Nat.mul_le_mul_right b hab
        _ < c * d := Nat.mul_lt_mul_of_pos_left hlt hc
    omega

theorem TwoBlk.exists_odd_offender (h : TwoBlk X H₁ H₂ m)
    (θ₁ : ↥H₁ ≃* Equiv.Perm (Fin m)) (θ₂ : ↥H₂ ≃* Equiv.Perm (Fin m)) (β₁ β₂ : ↥(coreMod m) →* V)
    (hβ₁eq : ∀ (x : ↥H₁) (u : ↥(coreMod m)), β₁ (coreAct m (θ₁ x) u) = (x : MulAut V) (β₁ u))
    (hβ₁r : β₁.range = commV H₁) (hβ₁k : β₁.ker = ⊥)
    (hβ₂eq : ∀ (x : ↥H₂) (u : ↥(coreMod m)), β₂ (coreAct m (θ₂ x) u) = (x : MulAut V) (β₂ u))
    (hβ₂r : β₂.range = commV H₂) (hβ₂k : β₂.ker = ⊥)
    (hstrong : ¬ IsStrongFFModule X)
    (hAJ : A ≤ H₁ ⊔ H₂) (hAe : IsElemAbelian2 A) (hA1 : A ≠ ⊥)
    (hoff : Nat.card V ≤ Nat.card A * Nat.card (fixV A)) :
    (∃ a ∈ A, ∃ ha : a ∈ H₁, Equiv.Perm.sign (θ₁ ⟨a, ha⟩) = -1) ∨
      ∃ a ∈ A, ∃ ha : a ∈ H₂, Equiv.Perm.sign (θ₂ ⟨a, ha⟩) = -1 := by
  classical
  have hc' : ∀ a ∈ H₂, ∀ b ∈ H₁, a * b = b * a := fun a ha b hb => (h.comm b hb a ha).symm
  have hinf' : H₂ ⊓ H₁ = ⊥ := by rw [inf_comm]; exact h.inf
  set P₁ := projSub H₁ H₂ A h.comm with hP₁
  set P₂ := projSub H₂ H₁ A hc' with hP₂
  have hP₁e : IsElemAbelian2 P₁ := projSub_elemAbelian h.inf hAe
  have hP₂e : IsElemAbelian2 P₂ := projSub_elemAbelian hinf' hAe
  have hP₁H : P₁ ≤ H₁ := projSub_le
  have hP₂H : P₂ ≤ H₂ := projSub_le
  have hA₁ : ∀ b ∈ A, ∀ e ∈ commV H₁, b e ∈ commV H₁ := fun b hb e he => h.preserve₁ (hAJ hb) he
  have hA₂ : ∀ b ∈ A, ∀ e ∈ commV H₂, b e ∈ commV H₂ := fun b hb e he => h.preserve₂ (hAJ hb) he
  have hP₁₁ : ∀ b ∈ P₁, ∀ e ∈ commV H₁, b e ∈ commV H₁ := fun b hb e he =>
    apply_mem_commV_of_mem hb.1 he
  have hP₁₂ : ∀ b ∈ P₁, ∀ e ∈ commV H₂, b e ∈ commV H₂ := fun b hb e he => by
    rw [h.act₁ b hb.1 e he]
    exact he
  have hP₂₂ : ∀ b ∈ P₂, ∀ e ∈ commV H₂, b e ∈ commV H₂ := fun b hb e he =>
    apply_mem_commV_of_mem hb.1 he
  have hP₂₁ : ∀ b ∈ P₂, ∀ e ∈ commV H₁, b e ∈ commV H₁ := fun b hb e he => by
    rw [h.act₂ b hb.1 e he]
    exact he
  have hV : Nat.card V = Nat.card (commV H₁) * Nat.card (commV H₂) := card_split h.supV h.infV
  have hfA := card_fixV_split h.supV h.infV A hA₁ hA₂
  have hF₁ : fixV A ⊓ commV H₁ = fixV P₁ ⊓ commV H₁ := h.fixV_inf_eq hAJ
  have hF₂ : fixV A ⊓ commV H₂ = fixV P₂ ⊓ commV H₂ := by
    have := h.symm.fixV_inf_eq (A := A) (by rw [sup_comm]; exact hAJ)
    exact this
  rw [hF₁, hF₂] at hfA
  set F₁ := Nat.card ↥(fixV P₁ ⊓ commV H₁) with hF₁def
  set F₂ := Nat.card ↥(fixV P₂ ⊓ commV H₂) with hF₂def
  have hfixP₁ : Nat.card (fixV P₁) = F₁ * Nat.card (commV H₂) := by
    have := card_fixV_split h.supV h.infV P₁ hP₁₁ hP₁₂
    have e : fixV P₁ ⊓ commV H₂ = commV H₂ :=
      inf_eq_right.mpr fun v hv x hx => h.act₁ x hx.1 v hv
    rw [e] at this
    exact this
  have hfixP₂ : Nat.card (fixV P₂) = Nat.card (commV H₁) * F₂ := by
    have := card_fixV_split h.supV h.infV P₂ hP₂₁ hP₂₂
    have e : fixV P₂ ⊓ commV H₁ = commV H₁ :=
      inf_eq_right.mpr fun v hv x hx => h.act₂ x hx.1 v hv
    rw [e] at this
    exact this
  have hFF : ∀ B : Subgroup (MulAut V), B ≤ X → B ≠ ⊥ → IsElemAbelian2 B →
      Nat.card B * Nat.card (fixV B) ≤ Nat.card V := by
    intro B hBX hB1 hBe
    by_contra hlt
    push Not at hlt
    exact hstrong ⟨B, hBX, hB1, hBe, hlt⟩
  have hpos₁ : 0 < Nat.card (commV H₁) := Nat.card_pos
  have hpos₂ : 0 < Nat.card (commV H₂) := Nat.card_pos
  have hbound₁ : Nat.card P₁ * F₁ ≤ Nat.card (commV H₁) := by
    by_cases hP1 : P₁ = ⊥
    · have hfix : fixV P₁ = ⊤ := by
        ext v
        simp only [mem_fixV, Subgroup.mem_top, iff_true]
        intro x hx
        rw [hP1, Subgroup.mem_bot] at hx
        rw [hx]
        rfl
      have : F₁ = Nat.card (commV H₁) := by
        rw [hF₁def, hfix, top_inf_eq]
      rw [this, hP1, Subgroup.card_bot, one_mul]
    · have := hFF P₁ (hP₁H.trans h.h1X) hP1 hP₁e
      rw [hfixP₁, hV] at this
      have h2 : (Nat.card P₁ * F₁) * Nat.card (commV H₂) ≤ Nat.card (commV H₁) * Nat.card (commV H₂) := by
        calc (Nat.card P₁ * F₁) * Nat.card (commV H₂) = Nat.card P₁ * (F₁ * Nat.card (commV H₂)) := by ring
          _ ≤ _ := this
      exact Nat.le_of_mul_le_mul_right h2 hpos₂
  have hbound₂ : Nat.card P₂ * F₂ ≤ Nat.card (commV H₂) := by
    by_cases hP2 : P₂ = ⊥
    · have hfix : fixV P₂ = ⊤ := by
        ext v
        simp only [mem_fixV, Subgroup.mem_top, iff_true]
        intro x hx
        rw [hP2, Subgroup.mem_bot] at hx
        rw [hx]
        rfl
      have : F₂ = Nat.card (commV H₂) := by
        rw [hF₂def, hfix, top_inf_eq]
      rw [this, hP2, Subgroup.card_bot, one_mul]
    · have := hFF P₂ (hP₂H.trans h.h2X) hP2 hP₂e
      rw [hfixP₂, hV] at this
      have h2 : (Nat.card P₂ * F₂) * Nat.card (commV H₁) ≤ Nat.card (commV H₁) * Nat.card (commV H₂) := by
        calc (Nat.card P₂ * F₂) * Nat.card (commV H₁) = Nat.card P₂ * (Nat.card (commV H₁) * F₂) := by ring
          _ ≤ _ := this
      rw [mul_comm (Nat.card (commV H₁)) (Nat.card (commV H₂))] at h2
      exact Nat.le_of_mul_le_mul_right h2 hpos₁
  let f : ↥P₁ × ↥P₂ → MulAut V := fun pq => (pq.1 : MulAut V) * pq.2
  have hAsub : (A : Set (MulAut V)) ⊆ Set.range f := by
    intro a ha
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_decomp (hc := h.comm) hc' ha (hAJ ha)
    exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  have hrange : (Set.range f).ncard ≤ Nat.card P₁ * Nat.card P₂ := by
    rw [← Set.image_univ, ← Nat.card_prod, ← Set.ncard_univ]
    exact Set.ncard_image_le (Set.toFinite _)
  have hrange' : Nat.card ↥(Set.range f) ≤ Nat.card P₁ * Nat.card P₂ := by
    rw [Nat.card_coe_set_eq]
    exact hrange
  have hAle : Nat.card A ≤ Nat.card P₁ * Nat.card P₂ := by
    have h1 : Nat.card ↥(A : Set (MulAut V)) ≤ Nat.card ↥(Set.range f) := by
      rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
      exact Set.ncard_le_ncard hAsub (Set.toFinite _)
    exact h1.trans hrange'
  have h1 : Nat.card (commV H₁) * Nat.card (commV H₂) ≤ Nat.card A * (F₁ * F₂) := by
    rw [← hV]
    have := hoff
    rw [hfA] at this
    exact this
  have h2 : Nat.card A * (F₁ * F₂) ≤ (Nat.card P₁ * F₁) * (Nat.card P₂ * F₂) := by
    calc Nat.card A * (F₁ * F₂) ≤ (Nat.card P₁ * Nat.card P₂) * (F₁ * F₂) :=
          Nat.mul_le_mul_right _ hAle
      _ = (Nat.card P₁ * F₁) * (Nat.card P₂ * F₂) := by ring
  obtain ⟨hq₁, hq₂⟩ := card_eq_of_le_mul hpos₁ hpos₂ hbound₁ hbound₂ (h1.trans h2)
  have hF₁pos : 0 < F₁ := Nat.card_pos
  have hF₂pos : 0 < F₂ := Nat.card_pos
  have hAeq : Nat.card A = Nat.card P₁ * Nat.card P₂ := by
    have h3 : (Nat.card P₁ * Nat.card P₂) * (F₁ * F₂) ≤ Nat.card A * (F₁ * F₂) := by
      calc (Nat.card P₁ * Nat.card P₂) * (F₁ * F₂) = (Nat.card P₁ * F₁) * (Nat.card P₂ * F₂) := by
            ring
        _ = Nat.card (commV H₁) * Nat.card (commV H₂) := by rw [hq₁, hq₂]
        _ ≤ _ := h1
    have h4 := Nat.le_of_mul_le_mul_right h3 (Nat.mul_pos hF₁pos hF₂pos)
    exact le_antisymm hAle h4
  have hAS : (A : Set (MulAut V)) = Set.range f := by
    refine Set.eq_of_subset_of_ncard_le hAsub ?_ (Set.toFinite _)
    have h5 : (A : Set (MulAut V)).ncard = Nat.card A := (Nat.card_coe_set_eq _).symm
    rw [h5, hAeq]
    exact hrange
  have hne : P₁ ≠ ⊥ ∨ P₂ ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    apply hA1
    rw [eq_bot_iff]
    intro a ha
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_decomp (hc := h.comm) hc' ha (hAJ ha)
    have hx' : x ∈ P₁ := hx
    have hy' : y ∈ P₂ := hy
    rw [hcon.1, Subgroup.mem_bot] at hx'
    rw [hcon.2, Subgroup.mem_bot] at hy'
    rw [hx', hy', mul_one]
    exact Subgroup.one_mem _
  have hcard₁ : Nat.card (commV H₁) = Nat.card P₁ * F₁ := hq₁.symm
  have hcard₂ : Nat.card (commV H₂) = Nat.card P₂ * F₂ := hq₂.symm
  rcases hne with hP1 | hP2
  · left
    obtain ⟨p, hpP, hpH, hsg⟩ := exists_odd_block h.m35 θ₁ β₁ hβ₁eq hβ₁r hβ₁k hP₁H hP₁e hP1
      (by rw [hcard₁])
    refine ⟨p, ?_, hpH, hsg⟩
    have : p * 1 ∈ A := by
      rw [← SetLike.mem_coe, hAS]
      exact ⟨(⟨p, hpP⟩, 1), rfl⟩
    simpa using this
  · right
    obtain ⟨p, hpP, hpH, hsg⟩ := exists_odd_block h.m35 θ₂ β₂ hβ₂eq hβ₂r hβ₂k hP₂H hP₂e hP2
      (by rw [hcard₂])
    refine ⟨p, ?_, hpH, hsg⟩
    have : 1 * p ∈ A := by
      rw [← SetLike.mem_coe, hAS]
      exact ⟨(1, ⟨p, hpP⟩), rfl⟩
    simpa using this

end TwoBlkOffender

end Ch3z

end CFSG.Quasithin
