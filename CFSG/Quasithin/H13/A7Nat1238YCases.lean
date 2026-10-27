module

public import CFSG.Quasithin.H13.A7Nat1238YTools
public import CFSG.Quasithin.Background.InternalSecB56
public import CFSG.Quasithin.Background.InternalSecB56M
public import CFSG.Quasithin.Background.G64SymCase
public import CFSG.Quasithin.Background.InternalSecTwo

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Quasithin CFSG.Quasithin.InternalSec CFSG.Assembly.LowTwoRank Subgroup

variable {W : Type} [CommGroup W] [Finite W]

theorem commV_eq_of_b56 {J Kst : Subgroup (MulAut W)} {P : Subgroup W}
    (hKJ : Kst ≤ J) (hn : ∀ x ∈ J, ∀ k ∈ Kst, x * k * x⁻¹ ∈ Kst) (hKs : IsSimpleGroup ↥Kst)
    (h60 : Nat.card ↥Kst = 60) (hna : ∃ a ∈ Kst, ∃ b ∈ Kst, a * b ≠ b * a)
    (hPX : P ≤ commV Kst) (hPinv : ∀ x ∈ Kst, ∀ p ∈ P, x p ∈ P) (hPfix : P ⊓ fixV Kst = ⊥)
    (hP16 : Nat.card ↥P = 16)
    (hfix : ∃ k ∈ Kst, ∃ w₁ ∈ commV Kst, w₁ ∉ fixV Kst ∧ k w₁ = w₁ ∧ ∃ w₂, (k * k) w₂ ≠ w₂)
    (hcases : B56Case1 J ∨ B56Case2 J ∨ B56Case3 J ∨ B56Case4 J ∨ B56Case5 J) :
    commV Kst = P := by
  have hna' : ∃ a b : ↥Kst, a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hna
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  have hKq : CFSG.IsQuasisimple ↥Kst := isQuasisimple_of_simple hna'
  have hperf : Group.IsPerfect ↥Kst := hKq.1
  have hJK : J ≤ normalizer (Kst : Set (MulAut W)) := fun x hx =>
    mem_normalizer_iff.mpr fun k => ⟨fun hk => hn x hx k hk, fun hk => by
      have := hn x⁻¹ (J.inv_mem hx) _ hk
      simpa [mul_assoc] using this⟩
  have hP1 : P ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hP16
    norm_num at hP16
  have piece : ∀ {Gi : Subgroup (MulAut W)} {Wi C : Subgroup W}, Kst ≤ Gi →
      Gi ≤ normalizer (Kst : Set (MulAut W)) → C ≤ fixV Kst → C ≤ Wi → B56Piece Gi Wi C →
      commV Kst = P := by
    intro Gi Wi C hKG hGK hCK hCW hp
    obtain ⟨k, hk, w₁, hw₁, hw₁f, hkw, w₂, hk2⟩ := hfix
    rcases hp with ⟨hWi, ⟨n, hnat⟩ | ⟨π, hπ⟩ | ⟨m, F, _, _, hF, π, hπ⟩⟩ |
        ⟨hWi, m, F, _, _, hF, I, π, -, -, -, hreal⟩ | ⟨⟨e⟩, -⟩
    ·
      exfalso
      refine false_of_binaryNaturalSL_of_fix hnat hKG hk ?_ (fun hc => hw₁f (hCK hc)) hkw hk2
      rw [hWi]
      exact Subgroup.mem_sup_left (commV_le_commV hKG hw₁)
    ·
      have hcard := G64.RealizesVia.card_eq hπ
      rw [G64.card_symDn_mod (by norm_num), ite_eq_right (by decide)] at hcard
      refine eq_of_card_le hperf hPX hPinv hPfix ?_ hCK hCW ?_
      · rw [hWi]
        exact (commV_le_commV hKG).trans le_sup_left
      · rw [hcard, hP16]
        norm_num
    · exact (false_of_surj_statedSL (Or.inl rfl) π hπ.1 hKG hGK hna h60).elim
    · exact (false_of_surj_statedSL (Or.inl rfl) π (hreal 0).1 hKG hGK hna h60).elim
    · exact (false_of_surj_statedSL (Or.inl rfl) e.symm.toMonoidHom e.symm.surjective hKG hGK
        hna h60).elim
  rcases hcases with h1 | ⟨⟨e⟩, -⟩ |
      ⟨G₁, G₂, hsup, -, hc, -, -, W₁, W₂, hC₁, hC₂, -, -, -, -, hp₁, hp₂⟩ |
      ⟨G₁, G₂, t, hJt, -, hc, ⟨e₁⟩, hc₂, -, -, -, -, -, ht₁, ht₂, -⟩ |
      ⟨G₁, G₂, hsup, -, hc, -, ⟨e₁⟩, -, -, h₂⟩
  ·
    have hF := eq_of_le_quasisimple hKJ hn hKq h1.1
    have hB : B51Conclusion J Kst := hF ▸ h1.2.1
    rcases hB.1.2 with hi | ⟨-, n, F, _, _, hF', I, π, -, -, hreal, -⟩ |
        ⟨n, -, hn', π, U₁, U₂, -, hreal, -⟩ | ⟨-, n, hn', k, hk, -, I, π, -, -, -, hreal⟩
    · exact eq_of_isIrrPlus hi.1.2 hPX hPinv hPfix hP1
    · exact (false_of_surj_statedSL (Or.inl rfl) π (hreal 0).1 le_rfl le_normalizer hna
        h60).elim
    · exact (false_of_surj_statedSL (Or.inr ⟨Nat.card_zmod 2, hn'⟩) π hreal.1 le_rfl
        le_normalizer hna h60).elim
    · exact (false_of_surj_statedSL (Or.inr ⟨Nat.card_zmod 2, hn'⟩) π (hreal ⟨0, hk⟩).1 le_rfl
        le_normalizer hna h60).elim
  ·
    exact (not_le_perm_three hKq hKJ e).elim
  ·
    have h₁J : G₁ ≤ J := hsup ▸ le_sup_left
    have h₂J : G₂ ≤ J := hsup ▸ le_sup_right
    have hCK : fixV J ≤ fixV Kst := fun v hv x hx => hv x (hKJ hx)
    rcases le_or_le_of_sup_eq hsup hc hKJ hn hKq with h | h
    · exact piece h (h₁J.trans hJK) hCK hC₁ hp₁
    · exact piece h (h₂J.trans hJK) hCK hC₂ hp₂
  ·
    exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rcases le_or_le_of_sup_zpowers hJt hc ht₁ ht₂ hKJ hn hKq with h | h
    · have h₁J : G₁ ≤ J := by
        rw [hJt]
        exact le_sup_left.trans le_sup_left
      have hA6 : IsSimpleGroup (alternatingGroup (Fin 6)) :=
        alternatingGroup.isSimpleGroup (by simp)
      have hG₁ : IsSimpleGroup ↥G₁ := e₁.isSimpleGroup
      have hnorm : (Kst.subgroupOf G₁).Normal :=
        (normal_subgroupOf_iff_le_normalizer h).2 (h₁J.trans hJK)
      have hcK : Nat.card ↥(Kst.subgroupOf G₁) = 60 := by
        rw [Nat.card_congr (subgroupOfEquivOfLe h).toEquiv, h60]
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Kst.subgroupOf G₁) with h0 | h0
      · rw [h0, Subgroup.card_bot] at hcK
        norm_num at hcK
      · rw [h0, Subgroup.card_top, Nat.card_congr e₁.toEquiv, nat_card_alternatingGroup,
          Nat.card_eq_fintype_card, Fintype.card_fin] at hcK
        norm_num [Nat.factorial] at hcK
    · exact not_le_of_card_prime hKq h hc₂
  ·
    exfalso
    have h₁J : G₁ ≤ J := hsup ▸ le_sup_left
    have h₂J : G₂ ≤ J := hsup ▸ le_sup_right
    rcases le_or_le_of_sup_eq hsup hc hKJ hn hKq with h | h
    · exact false_of_surj_statedSL (Or.inl rfl) e₁.symm.toMonoidHom e₁.symm.surjective h
        (h₁J.trans hJK) hna h60
    · rcases h₂ with ⟨⟨e₂⟩, -⟩ | ⟨n, hnat⟩
      · exact false_of_surj_statedSL (Or.inl rfl) e₂.symm.toMonoidHom e₂.symm.surjective h
          (h₂J.trans hJK) hna h60
      · obtain ⟨k, hk, w₁, hw₁, hw₁f, hkw, w₂, hk2⟩ := hfix
        exact false_of_binaryNaturalSL_of_fix hnat h hk (commV_le_commV h hw₁)
          (fun hz => hw₁f fun x hx => hz.1 x (h hx)) hkw hk2

end CFSG.Quasithin.H13.A7
