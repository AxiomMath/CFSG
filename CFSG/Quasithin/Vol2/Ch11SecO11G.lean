module

public import CFSG.Quasithin.Vol2.Ch11SecO11F

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.O11

open CFSG.Open CFSG.Blueprint QuasithinUnique

theorem center_sl2_four {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  have := Fintype.ofFinite F
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  have hq : r ^ 3 = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one r hr0
    rwa [Fintype.card_eq_nat_card, hF] at h
  have hr1 : r = 1 := by
    have h : r ^ Nat.gcd 2 3 = 1 := pow_gcd_eq_one.2 ⟨hr, hq⟩
    rwa [show Nat.gcd 2 3 = 1 from rfl, pow_one] at h
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1]
  simp

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem eq_one_of_mem_center {S B : Subgroup Q} (hB : IsL24Sub S B)
    (hZ : Odd (Nat.card (Subgroup.center Q))) {z : Q} (hzB : z ∈ B)
    (hzZ : z ∈ Subgroup.center Q) : z = 1 := by
  obtain ⟨-, -, -, F, _, _, hF, ⟨e⟩⟩ := hB
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : e (QuotientGroup.mk ⟨z, hzB⟩) ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective (e.symm g)
    have hg : g = e (QuotientGroup.mk b) := by rw [hb, MulEquiv.apply_symm_apply]
    rw [hg, ← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 2
    exact Subtype.ext ((Subgroup.mem_center_iff.mp hzZ) b)
  rw [center_sl2_four hF, Subgroup.mem_bot] at hc
  have h1 : (⟨z, hzB⟩ : ↥B) ∈ CFSG.pCore 2 ↥B := by
    rw [← QuotientGroup.eq_one_iff]
    exact e.injective (hc.trans (map_one e).symm)
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥B) ⟨_, h1⟩
  have h2 : z ^ 2 ^ k = 1 := by
    have := congrArg (fun x : ↥(CFSG.pCore 2 ↥B) => ((x : ↥B) : Q)) hk
    simpa using this
  have h3 : orderOf z ∣ Nat.card (Subgroup.center Q) := Subgroup.orderOf_dvd_natCard _ hzZ
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (Subgroup.center Q)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hZ)
  exact orderOf_eq_one_iff.mp
    ((Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h2) hcop).eq_one_of_dvd h3)

theorem l24Unique_of_quot_center (hZ : Odd (Nat.card (Subgroup.center Q))) {S : Subgroup Q}
    (h : L24Unique (S.map (QuotientGroup.mk' (Subgroup.center Q)))) : L24Unique S := by
  set π := QuotientGroup.mk' (Subgroup.center Q)
  have hinj : ∀ {B : Subgroup Q}, IsL24Sub S B → Function.Injective (π.comp B.subtype) := by
    intro B hB
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxZ : (x : Q) ∈ Subgroup.center Q := (QuotientGroup.eq_one_iff _).mp hx
    exact Subgroup.mem_bot.mpr (Subtype.ext (eq_one_of_mem_center hB hZ x.2 hxZ))
  intro B₁ B₂ h₁ h₂
  have e := h _ _ (IsL24Sub.map h₁ π (hinj h₁)) (IsL24Sub.map h₂ π (hinj h₂))
  rw [Subgroup.map_eq_map_iff, QuotientGroup.ker_mk'] at e
  rw [← perfectCore_sup_eq h₁.2.1 inferInstance (Subgroup.center_le_normalizer _), e,
    perfectCore_sup_eq h₂.2.1 inferInstance (Subgroup.center_le_normalizer _)]

theorem l24Unique_of_isHat {X : Type} [Group X] (hQ : IsHat Q X)
    (hX : ∀ S' : Subgroup X, IsSylowTwoOf S' ⊤ → L24Unique S') {S : Subgroup Q}
    (hS : IsSylowTwoOf S ⊤) : L24Unique S := by
  obtain ⟨-, hZ, ⟨e⟩⟩ := hQ
  refine l24Unique_of_quot_center (by rw [hZ]; decide) ?_
  have hS' := isSylowTwoOf_top_map_of_surjective hS (QuotientGroup.mk' (Subgroup.center Q))
    (QuotientGroup.mk'_surjective _)
  exact l24Unique_of_equiv (isSylowTwoOf_map_equiv e hS') (hX _ (isSylowTwoOf_map_equiv e hS'))
    ⟨e⟩ hS'

theorem l24Unique_hat7 (hQ : IsHat Q (alternatingGroup (Fin 7))) {S : Subgroup Q}
    (hS : IsSylowTwoOf S ⊤) : L24Unique S :=
  l24Unique_of_isHat hQ (fun _ hS' => l24Unique_alt7 ⟨MulEquiv.refl _⟩ hS') hS

end CFSG.Quasithin.Vol2.Ch11.SecS.O11
