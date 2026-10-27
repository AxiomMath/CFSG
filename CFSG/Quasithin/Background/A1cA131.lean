module

public import CFSG.Quasithin.Background.A1cA131Three

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

@[expose] def IsIrreducibleOn {Q : Type*} [Group Q] (P : Subgroup Q) : Prop :=
  P ≠ ⊥ ∧ ∀ W : Subgroup Q, W ≤ P → W.Normal → W = ⊥ ∨ W = P

namespace A1c

universe u v

variable {p : ℕ} [Fact p.Prime]

@[expose] def A131Concl (p : ℕ) (Q : Type*) [Group Q] [Finite Q] : Prop :=
  (∀ T : Subgroup Q, IsPGroup 2 T → T ≠ ⊥ →
      IsCyclic ↥(pCore p Q ⊓ Subgroup.centralizer (T : Set Q))) ∧
    pRank 2 (⊤ : Subgroup Q) ≤ 2 ∧
    (IsElemAbelian p (pCore p Q) → Nat.card (pCore p Q) = p ^ 3 →
      1 < pRank 2 (⊤ : Subgroup Q) →
      ∃ W : Subgroup Q, W ≤ pCore p Q ∧ W.Normal ∧ W ≠ ⊥ ∧ W ≠ pCore p Q)

theorem A131Concl_of_surjective (hp2 : p ≠ 2) {Q : Type v} [Group Q] [Finite Q]
    (hF : Subgroup.centralizer (pCore p Q : Set Q) ≤ pCore p Q) :
    ∀ (n : ℕ) (G : Type u) [Group G] [Finite G] (φ : G →* Q), Function.Surjective φ →
      Nat.card G = n → pRank p (⊤ : Subgroup G) ≤ 2 → A131Concl p Q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ φ hφ hn hrk
    have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
    by_cases hker : IsPGroup p φ.ker
    · exact ⟨fun T hT hT1 => reduced_isCyclic_centralizer hp2 hφ hker hrk hF hT hT1,
        reduced_pRank_two_le hp2 hφ hker hrk hF,
        fun hel hcard h2 => reduced_exists_invariant_subgroup hp2 hφ hker hrk hF hel hcard h2⟩
    ·
      obtain ⟨r, hr, hrdvd, hrp⟩ : ∃ r : ℕ, r.Prime ∧ r ∣ Nat.card φ.ker ∧ r ≠ p := by
        by_contra hcon
        push Not at hcon
        apply hker
        refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_)
        intro d hd hdd
        exact hcon d hd hdd
      have : Fact r.Prime := ⟨hr⟩
      obtain ⟨R₀⟩ := (inferInstance : Nonempty (Sylow r φ.ker))
      set R : Subgroup G := (R₀ : Subgroup φ.ker).map φ.ker.subtype with hR
      have hRbot : R ≠ ⊥ := by
        intro h
        have h0 : (R₀ : Subgroup φ.ker) = ⊥ :=
          (Subgroup.map_eq_bot_iff_of_injective (R₀ : Subgroup φ.ker) φ.ker.subtype_injective).1 h
        exact Sylow.ne_bot_of_dvd_card R₀ hrdvd h0
      have hRker : R ≤ φ.ker := Subgroup.map_subtype_le _
      have hRcard : Nat.card R = Nat.card R₀ :=
        Subgroup.card_map_of_injective φ.ker.subtype_injective
      by_cases hRn : R.Normal
      ·
        have hRp : ¬ p ∣ Nat.card R := by
          obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 R₀.isPGroup'
          rw [hRcard, hm]
          intro h
          exact hrp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hr).1
            (Nat.Prime.dvd_of_dvd_pow (Fact.out : p.Prime) h)).symm
        have hrk' : pRank p (⊤ : Subgroup (G ⧸ R)) ≤ 2 := by
          rw [CFSG.SectionRank.pRank_quotient_eq R hRp]; exact hrk
        have hlt : Nat.card (G ⧸ R) < n := by
          have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup R
          rw [← hn, h1]
          have : 1 < Nat.card R := by
            rw [hRcard]
            refine Nat.one_lt_iff_ne_zero_and_ne_one.2 ⟨Nat.card_pos.ne', fun h => hRbot ?_⟩
            rw [← hRcard] at h
            exact Subgroup.card_eq_one.1 h
          have hpos : 0 < Nat.card (G ⧸ R) := Nat.card_pos
          nlinarith
        refine ih _ hlt (G ⧸ R) (QuotientGroup.lift R φ fun x hx => hRker hx) ?_ rfl hrk'
        intro q
        obtain ⟨g, rfl⟩ := hφ q
        exact ⟨(g : G ⧸ R), rfl⟩
      ·
        have hfrat := Sylow.normalizer_sup_eq_top R₀
        have hNtop : Subgroup.normalizer (R : Set G) ≠ ⊤ := fun h =>
          hRn (Subgroup.normalizer_eq_top_iff.1 h)
        have hrk' : pRank p (⊤ : Subgroup ↥(Subgroup.normalizer (R : Set G))) ≤ 2 :=
          le_trans (CFSG.SectionRank.pRank_top_le_of_injective hp1 (Subgroup.subtype _)
            (Subgroup.subtype_injective _)) hrk
        have hlt : Nat.card ↥(Subgroup.normalizer (R : Set G)) < n := by
          rw [← hn]
          exact lt_of_le_of_ne (Subgroup.card_le_card_group _) fun h =>
            hNtop (Subgroup.card_eq_iff_eq_top _ |>.1 h)
        refine ih _ hlt ↥(Subgroup.normalizer (R : Set G)) (φ.comp (Subgroup.subtype _)) ?_ rfl hrk'
        intro q
        obtain ⟨g, rfl⟩ := hφ q
        have hg : g ∈ Subgroup.normalizer (R : Set G) ⊔ φ.ker := by
          rw [hfrat]; exact Subgroup.mem_top g
        obtain ⟨n', hn', k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hg
        refine ⟨⟨n', hn'⟩, ?_⟩
        show φ n' = φ (n' * k)
        rw [map_mul, MonoidHom.mem_ker.1 hk, mul_one]

end A1c

section A131

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem isCyclic_pCore_inf_centralizer_of_quotient (hp2 : p ≠ 2)
    (hG : pRank p (⊤ : Subgroup G) ≤ 2) (H : Subgroup G) [H.Normal]
    (hF : Subgroup.centralizer (pCore p (G ⧸ H) : Set (G ⧸ H)) ≤ pCore p (G ⧸ H))
    {T : Subgroup (G ⧸ H)} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥) :
    IsCyclic ↥(pCore p (G ⧸ H) ⊓ Subgroup.centralizer (T : Set (G ⧸ H))) :=
  (A1c.A131Concl_of_surjective hp2 hF _ G (QuotientGroup.mk' H)
    (QuotientGroup.mk'_surjective H) rfl hG).1 T hT hT1

theorem pRank_two_le_of_quotient (hp2 : p ≠ 2) (hG : pRank p (⊤ : Subgroup G) ≤ 2)
    (H : Subgroup G) [H.Normal]
    (hF : Subgroup.centralizer (pCore p (G ⧸ H) : Set (G ⧸ H)) ≤ pCore p (G ⧸ H)) :
    pRank 2 (⊤ : Subgroup (G ⧸ H)) ≤ 2 :=
  (A1c.A131Concl_of_surjective hp2 hF _ G (QuotientGroup.mk' H)
    (QuotientGroup.mk'_surjective H) rfl hG).2.1

theorem not_isIrreducibleOn_pCore_of_quotient (hp2 : p ≠ 2) (hG : pRank p (⊤ : Subgroup G) ≤ 2)
    (H : Subgroup G) [H.Normal]
    (hF : Subgroup.centralizer (pCore p (G ⧸ H) : Set (G ⧸ H)) ≤ pCore p (G ⧸ H))
    (hel : IsElemAbelian p (pCore p (G ⧸ H))) (hcard : Nat.card (pCore p (G ⧸ H)) = p ^ 3)
    (h2 : 1 < pRank 2 (⊤ : Subgroup (G ⧸ H))) :
    ¬ IsIrreducibleOn (pCore p (G ⧸ H)) := by
  obtain ⟨W, hW1, hWn, hW2, hW3⟩ :=
    (A1c.A131Concl_of_surjective hp2 hF _ G (QuotientGroup.mk' H)
      (QuotientGroup.mk'_surjective H) rfl hG).2.2 hel hcard h2
  rintro ⟨-, hirr⟩
  rcases hirr W hW1 hWn with h | h
  · exact hW2 h
  · exact hW3 h

end A131

end CFSG.Quasithin
