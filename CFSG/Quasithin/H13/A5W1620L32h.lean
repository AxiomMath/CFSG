module

public import CFSG.Quasithin.H13.A5W1620L32g

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped Matrix commutatorElement

namespace L32

variable {G : Type} [Group G] {F : Type} [Field F]

noncomputable abbrev coord2 {Q : Subgroup G} (β : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F))
    (i : Fin 2) : ↥Q →* Multiplicative (Fin 3 → F) :=
  (Pi.evalAddMonoidHom (fun _ : Fin 2 => Fin 3 → F) i).toMultiplicative.comp β

theorem fin_two_eq_or (i x : Fin 2) : x = i ∨ x = i + 1 := by
  revert i x
  decide

theorem mul_comm_of_sum_two {Q : Subgroup G} {β : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F)}
    (hβk : β.ker = ⊥) : ∀ q ∈ Q, ∀ q' ∈ Q, q * q' = q' * q := by
  have hinj : Function.Injective β := (MonoidHom.ker_eq_bot_iff β).mp hβk
  intro q hq q' hq'
  have h : β (⟨q, hq⟩ * ⟨q', hq'⟩) = β (⟨q', hq'⟩ * ⟨q, hq⟩) := by
    rw [map_mul, map_mul, mul_comm]
  exact congrArg Subtype.val (hinj h)

theorem sq_eq_one_of_sum_two [Finite F] (hF : Nat.card F = 2) {Q : Subgroup G}
    {β : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F)} (hβk : β.ker = ⊥) : ∀ q ∈ Q, q ^ 2 = 1 := by
  have h2 := two_eq_zero_of_natCard_two hF
  have hinj : Function.Injective β := (MonoidHom.ker_eq_bot_iff β).mp hβk
  intro q hq
  have h : β (⟨q, hq⟩ * ⟨q, hq⟩) = β 1 := by
    rw [map_mul, map_one]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one]
    funext a b
    rw [Pi.add_apply, Pi.add_apply, Pi.zero_apply, Pi.zero_apply, ← two_mul, h2, zero_mul]
  rw [pow_two]
  exact congrArg Subtype.val (hinj h)

theorem eq_one_of_forall_conj_eq_sum_two [Finite F] (hF : Nat.card F = 2) {K Q : Subgroup G}
    {α : ↥K →* ↥(StatedSL 3 F)} (hα : Function.Surjective α)
    {β : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F)} (hβk : β.ker = ⊥)
    (hβe : ∀ (a : ↥K) (u v : ↥Q), (v : G) = a * u * a⁻¹ → ∀ i : Fin 2,
      Multiplicative.toAdd (β v) i =
        (moduleAct false (α a : Matrix.GeneralLinearGroup (Fin 3) F)).mulVec
          (Multiplicative.toAdd (β u) i))
    {q : G} (hq : q ∈ Q) (hfix : ∀ k ∈ K, k * q * k⁻¹ = q) : q = 1 := by
  have h01 := eq_zero_or_eq_one_of_natCard_two hF
  have hinj : Function.Injective β := (MonoidHom.ker_eq_bot_iff β).mp hβk
  have h0 : ∀ i : Fin 2, Multiplicative.toAdd (β ⟨q, hq⟩) i = 0 := by
    intro i
    refine eq_zero_of_forall_fixed h01 fun γ => ?_
    obtain ⟨a, rfl⟩ := hα γ
    exact (coord_natural hβe i a ⟨q, hq⟩ ⟨q, hq⟩ (hfix a a.2).symm).symm
  have h1 : β ⟨q, hq⟩ = 1 := toAdd_eq_zero.mp (funext h0)
  exact congrArg Subtype.val (hinj (h1.trans (map_one β).symm))

theorem le_of_not_le_coord [Finite F] (hF : Nat.card F = 2) {K Q D : Subgroup G}
    {α : ↥K →* ↥(StatedSL 3 F)} (hα : Function.Surjective α)
    (hKQ : K ≤ Subgroup.normalizer (Q : Set G))
    {β : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F)} (hβk : β.ker = ⊥)
    (hβe : ∀ (a : ↥K) (u v : ↥Q), (v : G) = a * u * a⁻¹ → ∀ i : Fin 2,
      Multiplicative.toAdd (β v) i =
        (moduleAct false (α a : Matrix.GeneralLinearGroup (Fin 3) F)).mulVec
          (Multiplicative.toAdd (β u) i))
    (hDQ : D ≤ Q) (hKD : ∀ k ∈ K, ∀ d ∈ D, k * d * k⁻¹ ∈ D) {y : G}
    (hyD : ∀ d ∈ D, y * d * y⁻¹ ∈ D)
    (hcomm : ∀ k ∈ K, ∀ d ∈ D, k * (y * d * y⁻¹) * k⁻¹ = y * (k * d * k⁻¹) * y⁻¹)
    (hfp : ∀ d ∈ D, y * d * y⁻¹ = d → d = 1) {i : Fin 2}
    (hi : ¬ D ≤ (coord2 β i).ker.map Q.subtype) : Q ≤ D := by
  classical
  have hinj : Function.Injective β := (MonoidHom.ker_eq_bot_iff β).mp hβk
  set Zi := (coord2 β i).ker.map Q.subtype with hZi
  have hZiQ : Zi ≤ Q := Subgroup.map_subtype_le _
  have hβik : (coord2 β i).ker = Zi.subgroupOf Q :=
    (Subgroup.comap_map_eq_self_of_injective Q.subtype_injective _).symm
  have hβie := coord_natural hβe i
  have hmemZi : ∀ q (hq : q ∈ Q), q ∈ Zi ↔ Multiplicative.toAdd (β ⟨q, hq⟩) i = 0 := by
    intro q hq
    constructor
    · rintro ⟨q', hq', rfl⟩
      have h1 : coord2 β i q' = 1 := hq'
      exact congrArg Multiplicative.toAdd h1
    · intro h
      exact ⟨⟨q, hq⟩, MonoidHom.mem_ker.mpr (toAdd_eq_zero.mp h), rfl⟩
  have hsurj := exists_mem_of_not_le hF hα hβik hβie hDQ hKD hi
  have hKZ : ∀ k ∈ K, ∀ q ∈ Zi, k * q * k⁻¹ ∈ Zi := by
    intro k hk q hq
    have hqQ := hZiQ hq
    have hkq : k * q * k⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hKQ hk) q).mp hqQ
    rw [hmemZi _ hkq, hβe ⟨k, hk⟩ ⟨q, hqQ⟩ ⟨_, hkq⟩ rfl i, (hmemZi q hqQ).mp hq,
      Matrix.mulVec_zero]
  by_cases hDZ : D ⊓ Zi = ⊥
  ·
    exfalso
    have hDZ' : ∀ u ∈ D, u ∈ Zi → u = 1 := fun u hu hu' => by
      have h : u ∈ D ⊓ Zi := ⟨hu, hu'⟩
      rw [hDZ] at h
      exact h
    have hyZ : ∀ u ∈ D, u ∈ Zi → y * u * y⁻¹ ∈ Zi := fun u hu hu' => by
      rw [hDZ' u hu hu', mul_one, mul_inv_cancel]
      exact Zi.one_mem
    have hyZ' : ∀ u ∈ D, y * u * y⁻¹ ∈ Zi → u ∈ Zi := fun u hu h => by
      have h1 := hDZ' _ (hyD u hu) h
      have h2 : u = 1 := by
        calc u = y⁻¹ * (y * u * y⁻¹) * y := by group
          _ = 1 := by rw [h1]; group
      rw [h2]
      exact Zi.one_mem
    have hmod := conj_mul_inv_mem_of_commute hF hα hβik hβie hDQ hKD hi hyD hyZ hyZ' hcomm
    apply hi
    intro u hu
    have h1 := hDZ' _ (D.mul_mem (hyD u hu) (D.inv_mem hu)) (hmod u hu)
    have h2 : y * u * y⁻¹ = u := by
      calc y * u * y⁻¹ = (y * u * y⁻¹ * u⁻¹) * u := by group
        _ = u := by rw [h1, one_mul]
    rw [hfp u hu h2]
    exact Zi.one_mem
  ·
    let βj : ↥Zi →* Multiplicative (Fin 3 → F) := (coord2 β (i + 1)).comp (Subgroup.inclusion hZiQ)
    have hβjk : βj.ker = ⊥ := by
      rw [eq_bot_iff]
      intro q hq
      rw [Subgroup.mem_bot]
      have hq0 : Multiplicative.toAdd (β (Subgroup.inclusion hZiQ q)) (i + 1) = 0 :=
        congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp hq)
      have hqi : Multiplicative.toAdd (β (Subgroup.inclusion hZiQ q)) i = 0 :=
        (hmemZi _ (hZiQ q.2)).mp q.2
      have h1 : β (Subgroup.inclusion hZiQ q) = 1 := by
        refine toAdd_eq_zero.mp (funext fun x => ?_)
        rcases fin_two_eq_or i x with rfl | rfl
        · exact hqi
        · exact hq0
      have h2 : Subgroup.inclusion hZiQ q = 1 := hinj (h1.trans (map_one β).symm)
      have h3 : ((Subgroup.inclusion hZiQ q : ↥Q) : G) = 1 := by rw [h2]; rfl
      exact Subtype.ext h3
    have hβje : ∀ (a : ↥K) (u v : ↥Zi), (v : G) = a * u * a⁻¹ →
        Multiplicative.toAdd (βj v) =
          ((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (βj u) :=
      fun a u v huv => coord_natural hβe (i + 1) a (Subgroup.inclusion hZiQ u)
        (Subgroup.inclusion hZiQ v) huv
    have hKDZ : ∀ k ∈ K, ∀ u ∈ D ⊓ Zi, k * u * k⁻¹ ∈ D ⊓ Zi := fun k hk u hu =>
      ⟨hKD k hk u hu.1, hKZ k hk u hu.2⟩
    have hle := le_of_ne_bot hF hα hβjk hβje (inf_le_right : D ⊓ Zi ≤ Zi) hKDZ hDZ
    intro q hq
    obtain ⟨d, hd⟩ := hsurj (Multiplicative.toAdd (coord2 β i ⟨q, hq⟩))
    have hdQ : (d : G) ∈ Q := hDQ d.2
    have hqdQ : q * (d : G)⁻¹ ∈ Q := Q.mul_mem hq (Q.inv_mem hdQ)
    have hqd : q * (d : G)⁻¹ ∈ Zi := by
      rw [hmemZi _ hqdQ]
      have e : (⟨q * (d : G)⁻¹, hqdQ⟩ : ↥Q) = ⟨q, hq⟩ * (Subgroup.inclusion hDQ d)⁻¹ := rfl
      have hd' : Multiplicative.toAdd (β (Subgroup.inclusion hDQ d)) i =
          Multiplicative.toAdd (β ⟨q, hq⟩) i := hd
      rw [e, map_mul, map_inv, toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, hd',
        add_neg_cancel]
    have h1 : q * (d : G)⁻¹ ∈ D := (hle hqd).1
    have h2 : q = (q * (d : G)⁻¹) * d := by group
    rw [h2]
    exact D.mul_mem h1 d.2

theorem conj_eq_or_fixedPointFree_of_sum_two [Finite F] (hF : Nat.card F = 2)
    {K Q M : Subgroup G} {α : ↥K →* ↥(StatedSL 3 F)} (hα : Function.Surjective α)
    (hKQ : K ≤ Subgroup.normalizer (Q : Set G))
    {β : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F)} (hβk : β.ker = ⊥)
    (hβe : ∀ (a : ↥K) (u v : ↥Q), (v : G) = a * u * a⁻¹ → ∀ i : Fin 2,
      Multiplicative.toAdd (β v) i =
        (moduleAct false (α a : Matrix.GeneralLinearGroup (Fin 3) F)).mulVec
          (Multiplicative.toAdd (β u) i))
    (hMQ : M ≤ Q) (hKM : ∀ k ∈ K, ∀ u ∈ M, k * u * k⁻¹ ∈ M) {y : G} (hy3 : y ^ 3 = 1)
    (hyM : ∀ u ∈ M, y * u * y⁻¹ ∈ M)
    (hcomm : ∀ k ∈ K, ∀ u ∈ M, k * (y * u * y⁻¹) * k⁻¹ = y * (k * u * k⁻¹) * y⁻¹) :
    (∀ u ∈ M, y * u * y⁻¹ = u) ∨ (M = Q ∧ ∀ q ∈ Q, y * q * y⁻¹ = q → q = 1) := by
  classical
  have hinj : Function.Injective β := (MonoidHom.ker_eq_bot_iff β).mp hβk
  have hQc := mul_comm_of_sum_two hβk
  have hQ2 : ∀ q ∈ Q, q * q = 1 := fun q hq => by
    rw [← pow_two]
    exact sq_eq_one_of_sum_two hF hβk q hq
  by_cases hfix : ∀ u ∈ M, y * u * y⁻¹ = u
  · exact Or.inl hfix
  right
  push Not at hfix
  obtain ⟨u₀, hu₀, hu₀y⟩ := hfix
  have hMc : ∀ u ∈ M, ∀ w ∈ M, u * w = w * u := fun u hu w hw => hQc u (hMQ hu) w (hMQ hw)
  have hM2 : ∀ u ∈ M, u * u = 1 := fun u hu => hQ2 u (hMQ hu)
  let D : Subgroup G :=
    { carrier := {d | ∃ u ∈ M, d = y * u * y⁻¹ * u⁻¹}
      mul_mem' := by
        rintro _ _ ⟨u, hu, rfl⟩ ⟨w, hw, rfl⟩
        refine ⟨u * w, M.mul_mem hu hw, ?_⟩
        have hc : u⁻¹ * (y * w * y⁻¹ * w⁻¹) = (y * w * y⁻¹ * w⁻¹) * u⁻¹ :=
          hMc _ (M.inv_mem hu) _ (M.mul_mem (hyM w hw) (M.inv_mem hw))
        calc y * u * y⁻¹ * u⁻¹ * (y * w * y⁻¹ * w⁻¹) =
            y * u * y⁻¹ * (u⁻¹ * (y * w * y⁻¹ * w⁻¹)) := by group
          _ = y * u * y⁻¹ * ((y * w * y⁻¹ * w⁻¹) * u⁻¹) := by rw [hc]
          _ = y * (u * w) * y⁻¹ * (u * w)⁻¹ := by group
      one_mem' := ⟨1, M.one_mem, by group⟩
      inv_mem' := by
        rintro _ ⟨u, hu, rfl⟩
        refine ⟨u⁻¹, M.inv_mem hu, ?_⟩
        have hc : u * (y * u⁻¹ * y⁻¹) = (y * u⁻¹ * y⁻¹) * u :=
          hMc _ hu _ (hyM _ (M.inv_mem hu))
        calc (y * u * y⁻¹ * u⁻¹)⁻¹ = u * (y * u⁻¹ * y⁻¹) := by group
          _ = (y * u⁻¹ * y⁻¹) * u := hc
          _ = y * u⁻¹ * y⁻¹ * u⁻¹⁻¹ := by group }
  have hDM : D ≤ M := by
    rintro _ ⟨u, hu, rfl⟩
    exact M.mul_mem (hyM u hu) (M.inv_mem hu)
  have hDQ : D ≤ Q := hDM.trans hMQ
  have hKD : ∀ k ∈ K, ∀ d ∈ D, k * d * k⁻¹ ∈ D := by
    rintro k hk _ ⟨u, hu, rfl⟩
    refine ⟨k * u * k⁻¹, hKM k hk u hu, ?_⟩
    have h1 := hcomm k hk u hu
    calc k * (y * u * y⁻¹ * u⁻¹) * k⁻¹ = (k * (y * u * y⁻¹) * k⁻¹) * (k * u * k⁻¹)⁻¹ := by
          group
      _ = y * (k * u * k⁻¹) * y⁻¹ * (k * u * k⁻¹)⁻¹ := by rw [h1]
  have hyD : ∀ d ∈ D, y * d * y⁻¹ ∈ D := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨y * u * y⁻¹, hyM u hu, by group⟩
  have hcommD : ∀ k ∈ K, ∀ d ∈ D, k * (y * d * y⁻¹) * k⁻¹ = y * (k * d * k⁻¹) * y⁻¹ :=
    fun k hk d hd => hcomm k hk d (hDM hd)
  have hfp : ∀ d ∈ D, y * d * y⁻¹ = d → d = 1 := by
    rintro _ ⟨u, hu, rfl⟩ h
    have hu₁M : y * u * y⁻¹ ∈ M := hyM u hu
    have h1 : y * (y * u * y⁻¹) * y⁻¹ * (y * u * y⁻¹)⁻¹ = y * u * y⁻¹ * u⁻¹ := by
      calc y * (y * u * y⁻¹) * y⁻¹ * (y * u * y⁻¹)⁻¹ = y * (y * u * y⁻¹ * u⁻¹) * y⁻¹ := by
            group
        _ = y * u * y⁻¹ * u⁻¹ := h
    have hc : u⁻¹ * (y * u * y⁻¹) = (y * u * y⁻¹) * u⁻¹ := hMc _ (M.inv_mem hu) _ hu₁M
    have hu1sq : (y * u * y⁻¹) * (y * u * y⁻¹) = 1 := hM2 _ hu₁M
    have husq : u * u = 1 := hM2 _ hu
    have hu₂ : y * (y * u * y⁻¹) * y⁻¹ = u := by
      calc y * (y * u * y⁻¹) * y⁻¹ =
          (y * (y * u * y⁻¹) * y⁻¹ * (y * u * y⁻¹)⁻¹) * (y * u * y⁻¹) := by group
        _ = (y * u * y⁻¹) * (u⁻¹ * (y * u * y⁻¹)) := by rw [h1]; group
        _ = (y * u * y⁻¹) * ((y * u * y⁻¹) * u⁻¹) := by rw [hc]
        _ = ((y * u * y⁻¹) * (y * u * y⁻¹)) * u⁻¹ := by group
        _ = u := by rw [hu1sq, one_mul, inv_eq_of_mul_eq_one_right husq]
    have hy3' : y * (y * y) = 1 := by rw [← pow_three]; exact hy3
    have hyu : y * u * y⁻¹ = u := by
      calc y * u * y⁻¹ = y * (y * (y * u * y⁻¹) * y⁻¹) * y⁻¹ := by rw [hu₂]
        _ = (y * (y * y)) * u * (y * (y * y))⁻¹ := by group
        _ = u := by rw [hy3']; group
    rw [hyu, mul_inv_cancel]
  have hd₀ : y * u₀ * y⁻¹ * u₀⁻¹ ∈ D := ⟨u₀, hu₀, rfl⟩
  have hd₀1 : y * u₀ * y⁻¹ * u₀⁻¹ ≠ 1 := by
    intro h
    apply hu₀y
    calc y * u₀ * y⁻¹ = (y * u₀ * y⁻¹ * u₀⁻¹) * u₀ := by group
      _ = u₀ := by rw [h, one_mul]
  have hd₀Q := hDQ hd₀
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, Multiplicative.toAdd (β ⟨_, hd₀Q⟩) i ≠ 0 := by
    by_contra h
    push Not at h
    apply hd₀1
    have h1 : β ⟨_, hd₀Q⟩ = 1 := toAdd_eq_zero.mp (funext h)
    exact congrArg Subtype.val (hinj (h1.trans (map_one β).symm))
  have hnot : ¬ D ≤ (coord2 β i).ker.map Q.subtype := by
    intro h
    obtain ⟨q', hq', hq'e⟩ := h hd₀
    apply hi
    have e : (⟨_, hd₀Q⟩ : ↥Q) = q' := Subtype.ext hq'e.symm
    rw [e]
    exact congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp hq')
  have hQD := le_of_not_le_coord hF hα hKQ hβk hβe hDQ hKD hyD hcommD hfp hnot
  exact ⟨le_antisymm hMQ (hQD.trans hDM), fun q hq hyq => hfp q (hQD hq) hyq⟩

end L32

end CFSG.Quasithin.H13.A5
