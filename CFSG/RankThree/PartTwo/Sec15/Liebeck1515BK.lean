module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
import CFSG.RankThree.PartTwo.Sec15.Liebeck1515BInn
import CFSG.RankThree.PartTwo.Sec15.LiebeckA6Inv
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck1515

open CFSG CFSG.RankThree.PartTwo

variable {Q Γ : Type*} [Group Q] [Finite Q] [Group Γ] [Finite Γ]

theorem range_le_closure_orderOf {A : Type*} [Group A] (ψ : Γ →* A) {c : Γ}
    (hgen : (⊤ : Subgroup Γ) ≤ Subgroup.closure {x | ∃ g, x = g * c * g⁻¹}) :
    ψ.range ≤ Subgroup.closure {k | k ∈ ψ.range ∧ orderOf k = orderOf (ψ c)} := by
  conv_lhs => rw [MonoidHom.range_eq_map]
  refine (Subgroup.map_mono hgen).trans ?_
  rw [MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨x, ⟨g, rfl⟩, rfl⟩
  refine ⟨⟨g * c * g⁻¹, rfl⟩, ?_⟩
  have h := orderOf_injective (MulAut.conj (ψ g)).toMonoidHom (MulAut.conj (ψ g)).injective (ψ c)
  rw [map_mul, map_mul, map_inv]
  simpa [MulAut.conj_apply] using h

theorem not_nine_dvd_card_range (ψ : Γ →* alternatingGroup (Fin 6))
    (hcyc : ∀ S : Subgroup Γ, IsPGroup 3 S → IsCyclic ↥S) : ¬ 9 ∣ Nat.card ψ.range := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h9
  obtain ⟨S⟩ : Nonempty (Sylow 3 Γ) := inferInstance
  set S' : Sylow 3 ↥ψ.range := S.mapSurjective ψ.rangeRestrict_surjective with hS'
  have hS'card : Nat.card S' = 3 ^ (Nat.card ψ.range).factorization 3 := Sylow.card_eq_multiplicity S'
  have h9' : 9 ∣ Nat.card S' := by
    rw [hS'card]
    have h2 : 2 ≤ (Nat.card ψ.range).factorization 3 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp
        (by norm_num; exact h9)
    calc (9 : ℕ) = 3 ^ 2 := by norm_num
      _ ∣ 3 ^ (Nat.card ψ.range).factorization 3 := pow_dvd_pow 3 h2
  have hScyc : IsCyclic ↥(S : Subgroup Γ) := hcyc S S.isPGroup'
  have hS'cyc : IsCyclic ↥(S' : Subgroup ↥ψ.range) := by
    have hsurj : Function.Surjective ((ψ.rangeRestrict.comp (S : Subgroup Γ).subtype).codRestrict
        (S' : Subgroup ↥ψ.range) fun x => ⟨x, x.2, rfl⟩) := by
      rintro ⟨y, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    exact isCyclic_of_surjective _ hsurj
  obtain ⟨g, hg⟩ := hS'cyc.exists_generator
  have hord : orderOf g = Nat.card S' := orderOf_eq_card_of_forall_mem_zpowers hg
  have h3 : IsPGroup 3 (Subgroup.zpowers ((g : ↥ψ.range) : alternatingGroup (Fin 6))) := by
    have : orderOf ((g : ↥ψ.range) : alternatingGroup (Fin 6)) = orderOf g := by
      rw [orderOf_submonoid, orderOf_submonoid]
    refine IsPGroup.of_card (n := (Nat.card ψ.range).factorization 3) ?_
    rw [Nat.card_zpowers, this, hord, hS'card]
  have hx3 := LiebeckA6.pow_three_eq_one_of_isPGroup h3
  have hdvd : orderOf g ∣ 3 := by
    rw [← orderOf_submonoid, ← orderOf_submonoid]
    exact orderOf_dvd_of_pow_eq_one hx3
  rw [hord] at hdvd
  have := Nat.le_of_dvd (by norm_num) (h9'.trans hdvd)
  omega

theorem range_eq_or_of_isCyclic {U V : Subgroup Q} [U.Normal] (hUV : U ⊔ V = ⊤)
    (hc : ⁅U, V⁆ = ⊥) (hV : Nonempty (↥V ⧸ Subgroup.center ↥V ≃* alternatingGroup (Fin 6)))
    (κ : Γ →* MulAut Q) (hκV : κ.range ≤ V.map (MulAut.conj : Q →* MulAut Q)) {c : Γ}
    (hgen : (⊤ : Subgroup Γ) ≤ Subgroup.closure {x | ∃ g, x = g * c * g⁻¹})
    (hc3 : orderOf (κ c) = 3) (hcyc : ∀ S : Subgroup Γ, IsPGroup 3 S → IsCyclic ↥S)
    {Γ₀ : Subgroup Γ} (h12 : Nat.card (Γ₀.map κ) = 12) :
    κ.range = Γ₀.map κ ∨
      ∀ W : Subgroup (MulAut Q), W ≤ κ.range →
        κ.range ≤ Subgroup.normalizer (W : Set (MulAut Q)) → IsPGroup 2 W → W = ⊥ := by
  obtain ⟨Φ⟩ := nonempty_mulEquiv_map_conj hUV hc hV
  set I := V.map (MulAut.conj : Q →* MulAut Q) with hI
  set κ' : Γ →* ↥I := κ.codRestrict I (fun g => hκV ⟨g, rfl⟩) with hκ'
  set ψ : Γ →* alternatingGroup (Fin 6) := Φ.toMonoidHom.comp κ' with hψ
  have hκκ' : ∀ g, κ g = (κ' g : MulAut Q) := fun g => rfl
  have hκψ : ∀ g g', ψ g = ψ g' → κ g = κ g' := by
    intro g g' h
    have h1 : κ' g = κ' g' := Φ.injective h
    rw [hκκ', hκκ', h1]
  have hmapψ : ∀ S : Subgroup Γ, S.map ψ = (S.map κ').map Φ.toMonoidHom := fun S => by
    rw [hψ, Subgroup.map_map]
  have hmapκ : ∀ S : Subgroup Γ, S.map κ = (S.map κ').map I.subtype := fun S => by
    rw [Subgroup.map_map]
    rfl
  have hcard : ∀ S : Subgroup Γ, Nat.card (S.map ψ) = Nat.card (S.map κ) := fun S => by
    rw [hmapψ, hmapκ, Subgroup.card_map_of_injective Φ.injective,
      Subgroup.card_map_of_injective I.subtype_injective]
  have hc3' : orderOf (ψ c) = 3 := by
    rw [hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq, ← hc3, hκκ',
      Subgroup.orderOf_coe]
  have hgen' := range_le_closure_orderOf ψ hgen
  rw [hc3'] at hgen'
  have h9 := not_nine_dvd_card_range ψ hcyc
  have h12' : Nat.card (Γ₀.map ψ) = 12 := (hcard Γ₀).trans h12
  by_cases hW : ∃ W : Subgroup (alternatingGroup (Fin 6)), IsPGroup 2 W ∧ W ≠ ⊥ ∧ W ≤ ψ.range ∧
      ψ.range ≤ Subgroup.normalizer (W : Set (alternatingGroup (Fin 6)))
  · left
    obtain ⟨W, hW2, hW1, hWK, hKW⟩ := hW
    have heq := LiebeckA6.eq_of_card_twelve (Subgroup.map_le_range ψ Γ₀) h12' h9 hgen' hW2 hW1
      hWK hKW
    refine le_antisymm ?_ (Subgroup.map_le_range κ Γ₀)
    rintro _ ⟨g, rfl⟩
    have hg : ψ g ∈ Γ₀.map ψ := heq ▸ ⟨g, rfl⟩
    obtain ⟨g₀, hg₀, hgg⟩ := hg
    exact ⟨g₀, hg₀, hκψ g₀ g hgg⟩
  · right
    intro W hWK hKW hW2
    have hWI : W ≤ I := hWK.trans (fun _ ⟨g, hg⟩ => hg ▸ (κ' g).2)
    by_contra hW1
    apply hW
    refine ⟨(W.subgroupOf I).map Φ.toMonoidHom,
      (hW2.comap_of_injective I.subtype Subtype.val_injective).map _, ?_, ?_, ?_⟩
    · intro h
      apply hW1
      rw [eq_bot_iff]
      intro w hw
      have hm : Φ ⟨w, hWI hw⟩ ∈ (W.subgroupOf I).map Φ.toMonoidHom :=
        ⟨⟨w, hWI hw⟩, Subgroup.mem_subgroupOf.mpr hw, rfl⟩
      rw [h, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hm
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hm)
    · rintro _ ⟨w, hw, rfl⟩
      obtain ⟨g, hg⟩ := hWK (Subgroup.mem_subgroupOf.mp hw)
      refine ⟨g, ?_⟩
      rw [hψ, MonoidHom.comp_apply]
      congr 1
      exact Subtype.ext hg
    · rintro _ ⟨g, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hgN : κ g ∈ Subgroup.normalizer (W : Set (MulAut Q)) := hKW ⟨g, rfl⟩
      obtain ⟨y', rfl⟩ := Φ.surjective y
      have key : ∀ z : ↥I, Φ z ∈ (W.subgroupOf I).map Φ.toMonoidHom ↔ (z : MulAut Q) ∈ W := by
        intro z
        constructor
        · rintro ⟨z', hz', hzz⟩
          have : z' = z := Φ.injective hzz
          exact this ▸ Subgroup.mem_subgroupOf.mp hz'
        · intro hz
          exact ⟨z, Subgroup.mem_subgroupOf.mpr hz, rfl⟩
      have hconj : ψ g * Φ y' * (ψ g)⁻¹ = Φ (κ' g * y' * (κ' g)⁻¹) := by
        rw [hψ]
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_mul, map_inv]
      rw [hconj, key, key]
      exact Subgroup.mem_normalizer_iff.mp hgN (y' : MulAut Q)

end CFSG.RankThree.PartTwo.Sec15.Liebeck1515
