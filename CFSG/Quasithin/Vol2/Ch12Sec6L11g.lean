module

public import CFSG.Quasithin.H13.A7Nat1238YTools
public import CFSG.Quasithin.Background.InternalSecB56
public import CFSG.Quasithin.Background.InternalSecB56M
public import CFSG.Quasithin.Vol2.Ch11SecA11SL2
public import CFSG.Quasithin.Background.InternalSecTwo

public section

namespace CFSG.Quasithin.H13.S126L11g

open CFSG.Quasithin CFSG.Quasithin.InternalSec CFSG.Assembly.LowTwoRank Subgroup Matrix

section SLQuot

theorem exists_card_SL_eq {n : ℕ} (hn : 1 ≤ n) {F : Type} [Field F] [Finite F]
    (hq : CFSG.IsQuasisimple (SpecialLinearGroup (Fin n) F)) {Ω : Type*} [Group Ω]
    {X Kst : Subgroup Ω} (π : ↥(StatedSL n F) →* ↥X) (hπ : Function.Surjective π)
    (hKX : Kst ≤ X) (hXK : X ≤ normalizer (Kst : Set Ω))
    (hna : ∃ a ∈ Kst, ∃ b ∈ Kst, a * b ≠ b * a) :
    ∃ c, 1 ≤ c ∧ c ≤ n ∧ Nat.card (SpecialLinearGroup (Fin n) F) = Nat.card Kst * c := by
  set ψ : SpecialLinearGroup (Fin n) F →* ↥X :=
    π.comp (specialLinearGroupEquivStatedSL n F).toMonoidHom with hψ
  have hψs : Function.Surjective ψ := hπ.comp (specialLinearGroupEquivStatedSL n F).surjective
  have hX1 : ∃ x : ↥X, x ≠ 1 := by
    obtain ⟨a, ha, b, hb, hab⟩ := hna
    refine ⟨⟨a, hKX ha⟩, fun h1 => hab ?_⟩
    have : a = 1 := congrArg Subtype.val h1
    rw [this, one_mul, mul_one]
  have hker : ψ.ker ≤ center (SpecialLinearGroup (Fin n) F) := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq ψ.normal_ker with h | h
    · exfalso
      obtain ⟨x, hx⟩ := hX1
      obtain ⟨s, rfl⟩ := hψs x
      exact hx (MonoidHom.mem_ker.1 (h ▸ mem_top s))
    · exact h
  have hXq : CFSG.IsQuasisimple ↥X := CFSG.LocalCores.isQuasisimple_of_surjective hq ψ hψs hker
  have hKn : (Kst.subgroupOf X).Normal :=
    (normal_subgroupOf_iff_le_normalizer hKX).2 hXK
  have hKeq : Kst = X := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hXq hKn with h | h
    · exact le_antisymm hKX fun x hx => (Subgroup.subgroupOf_eq_top.1 h) hx
    · exfalso
      obtain ⟨a, ha, b, hb, hab⟩ := hna
      have hc := Subgroup.mem_center_iff.1 (h (show (⟨a, hKX ha⟩ : ↥X) ∈ Kst.subgroupOf X from ha))
        ⟨b, hKX hb⟩
      exact hab (congrArg Subtype.val hc).symm
  have hcard : Nat.card (SpecialLinearGroup (Fin n) F) = Nat.card Kst * Nat.card ψ.ker := by
    rw [hKeq, ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).toEquiv,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  have hZ : Nat.card ψ.ker ≤ n := by
    have h1 : Nat.card ψ.ker ≤ Nat.card (center (SpecialLinearGroup (Fin n) F)) :=
      Subgroup.card_le_of_le hker
    have h2 := Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity
      (n := Fin n) (R := F)).toEquiv
    have e1 : max (Fintype.card (Fin n)) 1 = n := by rw [Fintype.card_fin]; omega
    rw [e1] at h2
    have : NeZero n := ⟨by omega⟩
    have h3 : Nat.card (rootsOfUnity n F) ≤ n := card_rootsOfUnity F n
    omega
  exact ⟨_, Nat.card_pos, hZ, hcard⟩

theorem false_of_surj_SL360 {n : ℕ} {F : Type} [Field F] [Finite F]
    (hn : (n = 2 ∧ ∃ a, Nat.card F = 2 ^ a) ∨ n = 3 ∨ (Nat.card F = 2 ∧ (n = 4 ∨ n = 5)))
    {Ω : Type*} [Group Ω] {X Kst : Subgroup Ω} (π : ↥(StatedSL n F) →* ↥X)
    (hπ : Function.Surjective π) (hKX : Kst ≤ X) (hXK : X ≤ normalizer (Kst : Set Ω))
    (hna : ∃ a ∈ Kst, ∃ b ∈ Kst, a * b ≠ b * a) (h360 : Nat.card Kst = 360) : False := by
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  rcases hn with ⟨rfl, a, ha⟩ | rfl | ⟨hF2, h45⟩
  · rcases Nat.lt_or_ge a 2 with ha2 | ha2
    ·
      have hF : Nat.card F = 2 := by
        interval_cases a
        · rw [ha] at hq2
          norm_num at hq2
        · rw [ha]
          norm_num
      have : Finite ↥X := Finite.of_surjective π hπ
      have h1 : Nat.card Kst ≤ Nat.card X := Subgroup.card_le_of_le hKX
      have h2 : Nat.card X ≤ Nat.card ↥(StatedSL 2 F) := Nat.card_le_card_of_surjective π hπ
      have h3 : Nat.card ↥(StatedSL 2 F) = 6 := by
        rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 2 F).toEquiv,
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hF]
        have hI : Finset.Icc 2 2 = {2} := by decide
        rw [hI, Finset.prod_singleton]
        norm_num
      omega
    · obtain ⟨c, hc1, hc2, hcard⟩ := exists_card_SL_eq (by norm_num)
        (Vol2.Ch11.SecA.isQuasisimple_SL2 (Vol2.Ch11.SecA.exists_finset_card_four ha2 ha))
        π hπ hKX hXK hna
      rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), h360]
        at hcard
      have hI : Finset.Icc 2 2 = {2} := by decide
      have e : 2 * (2 - 1) / 2 = 1 := rfl
      rw [hI, Finset.prod_singleton, e, pow_one] at hcard
      set q := Nat.card F with hqdef
      rcases (show a = 2 ∨ a = 3 ∨ 4 ≤ a by omega) with rfl | rfl | ha4
      · rw [ha] at hcard
        norm_num at hcard
        omega
      · rw [ha] at hcard
        norm_num at hcard
        omega
      · have h16 : 16 ≤ q := by
          rw [ha]
          calc 16 = 2 ^ 4 := by norm_num
            _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha4
        have h255 : 255 ≤ q ^ 2 - 1 := by
          have : 256 ≤ q ^ 2 := by
            calc 256 = 16 ^ 2 := by norm_num
              _ ≤ q ^ 2 := Nat.pow_le_pow_left h16 2
          omega
        have := Nat.mul_le_mul h16 h255
        omega
  · obtain ⟨c, hc1, hc2, hcard⟩ := exists_card_SL_eq (by norm_num)
      (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 F le_rfl) π hπ hKX hXK hna
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), h360] at hcard
    have hI : Finset.Icc 2 3 = {2, 3} := by decide
    have e : 3 * (3 - 1) / 2 = 3 := rfl
    rw [hI, Finset.prod_pair (by norm_num), e] at hcard
    set q := Nat.card F with hqdef
    rcases Nat.lt_or_ge q 3 with hq3 | hq3
    · have hq2' : q = 2 := by omega
      rw [hq2'] at hcard
      norm_num at hcard
      omega
    · have h1 : 27 ≤ q ^ 3 := by
        calc 27 = 3 ^ 3 := by norm_num
          _ ≤ q ^ 3 := Nat.pow_le_pow_left hq3 3
      have h2 : 8 ≤ q ^ 2 - 1 := by
        have : 9 ≤ q ^ 2 := by
          calc 9 = 3 ^ 2 := by norm_num
            _ ≤ q ^ 2 := Nat.pow_le_pow_left hq3 2
        omega
      have h3' : 26 ≤ q ^ 3 - 1 := by omega
      have h4 : 27 * (8 * 26) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3')
      omega
  · rcases h45 with rfl | rfl
    · obtain ⟨c, hc1, hc2, hcard⟩ := exists_card_SL_eq (by norm_num)
        (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 3 F (by norm_num)) π hπ hKX hXK hna
      rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), h360, hF2]
        at hcard
      have hI : Finset.Icc 2 4 = {2, 3, 4} := by decide
      rw [hI] at hcard
      norm_num at hcard
      omega
    · obtain ⟨c, hc1, hc2, hcard⟩ := exists_card_SL_eq (by norm_num)
        (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 4 F (by norm_num)) π hπ hKX hXK hna
      rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), h360, hF2]
        at hcard
      have hI : Finset.Icc 2 5 = {2, 3, 4, 5} := by decide
      rw [hI] at hcard
      norm_num at hcard
      omega

end SLQuot

section Irr

variable {V : Type} [CommGroup V]

theorem le_of_isIrrPlus {X : Subgroup (MulAut V)} {M P : Subgroup V}
    (hM : XMod.IsIrrPlus ↥X M) (hPM : P ≤ M) (hPinv : ∀ x ∈ X, ∀ p ∈ P, x p ∈ P)
    (hPf : ¬ P ≤ fixV X) : M ≤ P := by
  obtain ⟨-, hcomm, -, hirr⟩ := hM
  set F := XMod.fixed ↥X M with hF
  have hFfix : F ≤ fixV X := fun v hv x hx => hv.2 ⟨x, hx⟩
  have hJinv : XMod.IsInv ↥X (P ⊔ F) := by
    intro a l hl
    obtain ⟨p, hp, f, hf, rfl⟩ := Subgroup.mem_sup.1 hl
    show (a : MulAut V) (p * f) ∈ P ⊔ F
    rw [map_mul, hFfix hf a a.2]
    exact Subgroup.mul_mem_sup (hPinv _ a.2 p hp) hf
  rcases hirr (P ⊔ F) hJinv le_sup_right (sup_le hPM fun v hv => hv.1) with h | h
  · exact absurd ((le_sup_left.trans h.le).trans hFfix) hPf
  · calc M = XMod.commOf ↥X M := hcomm.symm
      _ = XMod.commOf ↥X (P ⊔ F) := by rw [h]
      _ ≤ P := A7.commOf_sup_le hPinv hFfix

end Irr

variable {W : Type} [CommGroup W] [Finite W]

theorem commV_eq_of_b56_A6 {J Kst : Subgroup (MulAut W)} {P : Subgroup W} (hKJ : Kst ≤ J)
    (hn : ∀ x ∈ J, ∀ k ∈ Kst, x * k * x⁻¹ ∈ Kst) (h360 : Nat.card ↥Kst = 360)
    (hKq : CFSG.IsQuasisimple ↥Kst) (hPX : P ≤ commV Kst)
    (hPinv : ∀ x ∈ Kst, ∀ p ∈ P, x p ∈ P) (hPf : ¬ P ≤ fixV Kst) (hP32 : Nat.card ↥P = 32)
    (hcases : B56Case1 J ∨ B56Case2 J ∨ B56Case3 J ∨ B56Case4 J ∨ B56Case5 J) :
    commV Kst = P := by
  have hna : ∃ a ∈ Kst, ∃ b ∈ Kst, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact not_commute_of_isQuasisimple hKq h
  have hJK : J ≤ normalizer (Kst : Set (MulAut W)) := fun x hx =>
    mem_normalizer_iff.mpr fun k => ⟨fun hk => hn x hx k hk, fun hk => by
      have := hn x⁻¹ (J.inv_mem hx) _ hk
      simpa [mul_assoc] using this⟩
  have factor : ∀ {Gi : Subgroup (MulAut W)}, Kst ≤ Gi →
      Gi ≤ normalizer (Kst : Set (MulAut W)) → B56FactorList ↥Gi → False := by
    intro Gi hKG hGK hf
    rcases hf with ⟨n, K, _, _, -, hK, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨m, K, _, _, -, -, -, ⟨e⟩⟩
    · exact false_of_surj_SL360 (Or.inl ⟨rfl, n, hK⟩) e.symm.toMonoidHom e.symm.surjective hKG
        hGK hna h360
    · have h1 : Nat.card ↥Kst ≤ Nat.card ↥Gi := Subgroup.card_le_of_le hKG
      rw [Nat.card_congr e.toEquiv, h360, Nat.card_eq_fintype_card, Fintype.card_perm,
        Fintype.card_fin] at h1
      norm_num [Nat.factorial] at h1
    · exact false_of_surj_SL360 (Or.inr (Or.inl rfl)) e.symm.toMonoidHom e.symm.surjective hKG
        hGK hna h360
  rcases hcases with h1 | ⟨⟨e⟩, -⟩ | ⟨G₁, G₂, hsup, -, hc, hf₁, hf₂, -⟩ |
      ⟨G₁, G₂, t, hJt, -, hc, -, hc₂, -, -, -, hV1, -, ht₁, ht₂, -⟩ |
      ⟨G₁, G₂, hsup, -, hc, -, ⟨e₁⟩, -, -, h₂⟩
  ·
    have hF := eq_of_le_quasisimple hKJ hn hKq h1.1
    have hB : B51Conclusion J Kst := hF ▸ h1.2.1
    rcases hB.1.2 with hi | ⟨-, n, F, _, _, -, I, π, -, -, hreal, -⟩ |
        ⟨n, -, hn', π, U₁, U₂, -, hreal, -⟩ | ⟨-, n, hn', k, hk, -, I, π, -, -, -, hreal⟩
    · exact le_antisymm (le_of_isIrrPlus hi.1.2 hPX hPinv hPf) hPX
    · exact (false_of_surj_SL360 (Or.inr (Or.inl rfl)) π (hreal 0).1 le_rfl le_normalizer hna
        h360).elim
    · exact (false_of_surj_SL360 (Or.inr (Or.inr ⟨Nat.card_zmod 2, hn'⟩)) π hreal.1 le_rfl
        le_normalizer hna h360).elim
    · exact (false_of_surj_SL360 (Or.inr (Or.inr ⟨Nat.card_zmod 2, hn'⟩)) π (hreal ⟨0, hk⟩).1
        le_rfl le_normalizer hna h360).elim
  ·
    exact (not_le_perm_three hKq hKJ e).elim
  ·
    exfalso
    have h₁J : G₁ ≤ J := hsup ▸ le_sup_left
    have h₂J : G₂ ≤ J := hsup ▸ le_sup_right
    rcases le_or_le_of_sup_eq hsup hc hKJ hn hKq with h | h
    · exact factor h (h₁J.trans hJK) hf₁
    · exact factor h (h₂J.trans hJK) hf₂
  ·
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rcases le_or_le_of_sup_zpowers hJt hc ht₁ ht₂ hKJ hn hKq with h | h
    · have hle : commV Kst ≤ commV G₁ := commV_le_commV h
      have hcard : Nat.card ↥(commV G₁) ≤ Nat.card ↥P := by
        rw [hP32]
        rcases hV1 with h4 | h5
        · rw [h4]
          norm_num
        · rw [h5]
          norm_num
      have heq : P = commV G₁ := Subgroup.eq_of_le_of_card_ge (hPX.trans hle) hcard
      exact le_antisymm (heq ▸ hle) hPX
    · exact (not_le_of_card_prime hKq h hc₂).elim
  ·
    exfalso
    have h₁J : G₁ ≤ J := hsup ▸ le_sup_left
    have h₂J : G₂ ≤ J := hsup ▸ le_sup_right
    rcases le_or_le_of_sup_eq hsup hc hKJ hn hKq with h | h
    · exact false_of_surj_SL360 (Or.inr (Or.inl rfl)) e₁.symm.toMonoidHom e₁.symm.surjective h
        (h₁J.trans hJK) hna h360
    · rcases h₂ with ⟨⟨e₂⟩, -⟩ | ⟨n, hnat⟩
      · exact false_of_surj_SL360 (Or.inr (Or.inl rfl)) e₂.symm.toMonoidHom e₂.symm.surjective h
          (h₂J.trans hJK) hna h360
      · obtain ⟨F, _, _, hF, π, hπs, -⟩ := hnat
        exact false_of_surj_SL360 (Or.inl ⟨rfl, n, hF⟩) π hπs h (h₂J.trans hJK) hna h360

end CFSG.Quasithin.H13.S126L11g
