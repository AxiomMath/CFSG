module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KLie
public import CFSG.RankThree.PartTwo.Sec12.Hering129KYa
public import CFSG.RankThree.PartTwo.Sec12.Hering129KYb
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane
public import CFSG.RankThree.PartTwo.Sec12.Hering129HEnd

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section SLTwo

theorem inf_eq_zpowers_of_sl2_quotient {G : Type} [Group G] [Finite G] {A X : Subgroup G}
    {c : G} (hAe : CFSG.Assembly.IsElemAbelian 3 A) (hcA : c ∈ A) (hcX : c ∈ X)
    (hc3 : orderOf c = 3) {F : Type} [Field F] [Finite F] (h3F : ¬ 3 ∣ Nat.card F)
    (φ : ↥X →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hker : φ.ker ≤ aschbacherSolvableCore 3 ↥X) : A ⊓ X = Subgroup.zpowers c := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAc : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  set E : Subgroup ↥X := (A ⊓ X).subgroupOf X with hE
  have hmemE : ∀ z : ↥X, z ∈ E ↔ (z : G) ∈ A := fun z => by
    simp only [hE, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, z.2⟩⟩
  have hEcomm : ∀ y ∈ E, ∀ z ∈ E, y * z = z * y := fun y hy z hz =>
    Subtype.ext (hAc _ ((hmemE y).mp hy) _ ((hmemE z).mp hz))
  have hE3 : ∀ y ∈ E, y ^ 3 = 1 := fun y hy =>
    Subtype.ext (by simpa using hAe.2 _ ((hmemE y).mp hy))
  set M : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) := E.map φ with hM
  have hMe : CFSG.Assembly.IsElemAbelian 3 M := by
    refine ⟨⟨⟨fun y z => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨_, y', hy', rfl⟩ := y
      obtain ⟨_, z', hz', rfl⟩ := z
      apply Subtype.ext
      change φ y' * φ z' = φ z' * φ y'
      rw [← map_mul, ← map_mul, hEcomm y' hy' z' hz']
    · obtain ⟨y', hy', hyy⟩ := Subgroup.mem_map.mp hy
      rw [← hyy, ← map_pow, hE3 y' hy', map_one]
  have hM3 : Nat.card M ≤ 3 :=
    Hering129KYb.card_le_three_of_isElemAbelian_sl2 h3F M hMe
  have hinj : Function.Injective (φ.comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hy1 : φ (y : ↥X) = 1 := hy
    have hyker : (y : ↥X) ∈ aschbacherSolvableCore 3 ↥X := hker hy1
    have hy3 : (y : ↥X) ^ 3 = 1 := hE3 y y.2
    exact Subtype.ext (eq_one_of_mem_theta_of_pow_three hyker hy3)
  have hEcard : Nat.card E ≤ 3 := by
    have hinj' : Function.Injective
        ((φ.comp E.subtype).codRestrict M (fun y => ⟨y, y.2, rfl⟩)) := by
      intro y z h
      apply hinj
      exact congrArg Subtype.val h
    exact (Nat.card_le_card_of_injective _ hinj').trans hM3
  have hcE : (⟨c, hcX⟩ : ↥X) ∈ E := (hmemE _).mpr hcA
  have hc'3 : orderOf (⟨c, hcX⟩ : ↥X) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact hc3
  have hzp : Subgroup.zpowers (⟨c, hcX⟩ : ↥X) ≤ E := Subgroup.zpowers_le.mpr hcE
  have hzcard : Nat.card (Subgroup.zpowers (⟨c, hcX⟩ : ↥X)) = 3 := by
    rw [Nat.card_zpowers, hc'3]
  have hEeq : Subgroup.zpowers (⟨c, hcX⟩ : ↥X) = E :=
    Subgroup.eq_of_le_of_card_ge hzp (by rw [hzcard]; exact hEcard)
  apply le_antisymm
  · intro z hz
    have hzX : z ∈ X := hz.2
    have : (⟨z, hzX⟩ : ↥X) ∈ E := (hmemE _).mpr hz.1
    rw [← hEeq] at this
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp this
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
  · intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ⟨A.zpow_mem hcA k, X.zpow_mem hcX k⟩

theorem pow_cases_of_two_sl2_quotients {X : Type} [Group X] [Finite X] {p n p' n' : ℕ}
    [Fact p.Prime] [Fact p'.Prime] {F F' : Type} [Field F] [Finite F] [Field F'] [Finite F']
    (hF : Nat.card F = p ^ n) (hF' : Nat.card F' = p' ^ n') (h4 : 4 ≤ p ^ n)
    (h4' : 4 ≤ p' ^ n') (φ : X →* Matrix.SpecialLinearGroup (Fin 2) F)
    (φ' : X →* Matrix.SpecialLinearGroup (Fin 2) F') (hφ : Function.Surjective φ)
    (hφ' : Function.Surjective φ') (hk : φ.ker ≤ aschbacherSolvableCore 3 X)
    (hk' : φ'.ker ≤ aschbacherSolvableCore 3 X) :
    p ^ n = p' ^ n' ∨ (p ^ n = 4 ∧ p' ^ n' = 5) ∨ (p ^ n = 5 ∧ p' ^ n' = 4) := by
  obtain ⟨e⟩ := Hering129KYa.nonempty_quotTheta_equiv_projSL hF (by rw [hF]; exact h4) φ hφ hk
  obtain ⟨e'⟩ := Hering129KYa.nonempty_quotTheta_equiv_projSL hF' (by rw [hF']; exact h4') φ' hφ'
    hk'
  exact psl2IsoOrders_holds p n p' n' h4 h4' ⟨e.symm.trans e'⟩

end SLTwo

section PrimePowers

theorem primePower_eq_of_card_eq {r q : TauCeti.PrimePower} (h : r.card = q.card) : r = q := by
  have := Nat.Prime.pow_inj' r.prime_p q.prime_p r.exponent_pos.ne' q.exponent_pos.ne'
    (by simpa using h)
  exact TauCeti.PrimePower.ext this.1 this.2

theorem primePower_eq_cube {r q : TauCeti.PrimePower} (h : r.card = q.card ^ 3) :
    r = ⟨q.p, 3 * q.exponent, q.prime_p, Nat.mul_pos (by norm_num) q.exponent_pos⟩ := by
  apply primePower_eq_of_card_eq
  rw [h]
  simp only [TauCeti.PrimePower.card_def]
  rw [← pow_mul, mul_comm]

theorem two_le_card_primePower (r : TauCeti.PrimePower) : 2 ≤ r.card := by
  rw [TauCeti.PrimePower.card_def]
  exact r.prime_p.two_le.trans (Nat.le_self_pow r.exponent_pos.ne' _)

end PrimePowers

section Table

variable {G : Type} [Group G] [Finite G]


theorem typ129IIIcType_of_d4 {L Y : Subgroup G} {r : TauCeti.PrimePower}
    (hL : ∃ q' : TauCeti.PrimePower, Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) q'.card)
    (hY : ∃ hr : (TauCeti.LieTypeIndex.trialityD4 r).Valid,
      Nonempty (Y ⧸ CFSG.pCore 2 Y ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 r, hr⟩).Group)) :
    Typ129IIIcType L Y := by
  obtain ⟨hr, ⟨e⟩⟩ := hY
  refine ⟨hL, Or.inr ⟨r, hr, ⟨e⟩⟩, ?_⟩
  exact Hering129KModels.center_eq_bot_of_isG2D4 (Or.inr ⟨rfl, hr, ⟨e⟩⟩ : IsG2D4 _ r 3)

theorem typ129_of_lie_table {K Y : Subgroup G} {q r : TauCeti.PrimePower} {δ δ' : ℕ}
    (hGK : IsG2D4 (K ⧸ CFSG.pCore 2 K) q δ) (hGY : IsG2D4 (Y ⧸ CFSG.pCore 2 Y) r δ')
    (hcase : ¬ (δ = 1 ∧ δ' = 3))
    (hs : q.card ^ δ = r.card ^ δ' ∨ (q.card ^ δ = 4 ∧ r.card ^ δ' = 5) ∨
      (q.card ^ δ = 5 ∧ r.card ^ δ' = 4)) :
    Typ129I K Y ∨ Typ129II K Y ∨ Typ129IV q Y := by
  have hq2 := two_le_card_primePower q
  have hr2 := two_le_card_primePower r
  have hq8 : 2 ^ 3 ≤ q.card ^ 3 := Nat.pow_le_pow_left hq2 3
  have hr8 : 2 ^ 3 ≤ r.card ^ 3 := Nat.pow_le_pow_left hr2 3
  rcases hGK with ⟨hδ, hK2⟩ | ⟨hδ, hK3, ⟨eK⟩⟩ <;>
    rcases hGY with ⟨hδ', hY2⟩ | ⟨hδ', hY3, ⟨eY⟩⟩
  ·
    subst hδ hδ'
    simp only [pow_one] at hs
    rcases hs with h | ⟨h4, h5⟩ | ⟨h5, h4⟩
    · have hrq : r = q := primePower_eq_of_card_eq h.symm
      subst hrq
      obtain ⟨hK, ⟨eK⟩⟩ := hK2
      obtain ⟨hY, ⟨eY⟩⟩ := hY2
      exact Or.inl ⟨eY.trans eK.symm⟩
    · exact Or.inr (Or.inr ⟨Or.inl h4, r, Or.inr h5, by omega, hY2⟩)
    · exact Or.inr (Or.inr ⟨Or.inr h5, r, Or.inl h4, by omega, hY2⟩)
  · exact absurd ⟨hδ, hδ'⟩ hcase
  ·
    subst hδ hδ'
    simp only [pow_one] at hs
    rcases hs with h | ⟨h4, h5⟩ | ⟨h5, h4⟩
    · have hr := primePower_eq_cube h.symm
      subst hr
      exact Or.inr (Or.inl ⟨q, ⟨hK3, ⟨eK⟩⟩, hY2⟩)
    · omega
    · omega
  ·
    subst hδ hδ'
    rcases hs with h | ⟨h4, h5⟩ | ⟨h5, h4⟩
    · have hqr : q.card = r.card := Nat.pow_left_injective (by norm_num) h
      have hrq : r = q := primePower_eq_of_card_eq hqr.symm
      subst hrq
      exact Or.inl ⟨eY.trans eK.symm⟩
    · omega
    · omega

end Table


end CFSG.RankThree.PartTwo.Sec12
