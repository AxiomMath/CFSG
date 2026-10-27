module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactsNineteenElevenTwentyOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenEleven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyFiveTrichotomy

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

variable {G : Type} [Group G] [Finite G]

section Certificates


theorem shape1911_of_ctx (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (h42 : S17.R17_42At D V₀ V) :
    (IsSp4 (Bar2 (IOf D p L)) (S17.nOf L) ∧ Odd (S17.nOf L) ∧ 1 < S17.nOf L ∧
        (2 : ℤ) ^ S17.nOf L ≡ -1 [ZMOD (p : ℤ)]) ∨
      ((IsL2Square (Bar2 (IOf D p L)) (S17.nOf L) ∨
          (S17.IsL2U3Product (Bar2 (IOf D p L)) (S17.nOf L) ∧ IsPowTwo (S17.nOf L))) ∧
        2 < S17.nOf L ∧ (2 : ℤ) ^ S17.nOf L ≡ -1 [ZMOD (p : ℤ)]) ∨
      (IsSzSquare (Bar2 (IOf D p L)) (S17.nOf L) ∧ 2 < S17.nOf L ∧
        (2 : ℤ) ^ (2 * S17.nOf L) ≡ -1 [ZMOD (p : ℤ)]) := by
  have hset := h.h1910
  simp only [Setting1910] at hset
  obtain ⟨-, h1 | h2 | h3⟩ := hset
  · refine Or.inl ⟨h1.1, h1.2.1, ?_, h1.2.2.2⟩
    by_contra hn
    have hn1 : S17.nOf L = 1 := by
      obtain ⟨k, hk⟩ := h1.2.1
      omega
    have hcard := card_eq_of_isZModSq h.hAcard
    rw [hn1] at hcard
    have hc1 : Nat.card A = 1 := by rw [hcard]; norm_num
    have hdvd := h.hr.2
    rw [hc1] at hdvd
    exact h.hr.1.one_lt.ne' (Nat.dvd_one.mp hdvd)
  · have hL : L ∈ calC D.M := h.hyp.hL.1
    obtain ⟨-, x, hxM, hXsup, hne, -, -⟩ := S17.p42_alt2_of_ne h42 h.hyp.hp hL h2.2.1
    rcases h2.2.2.2 with ⟨hL2, hc⟩ | ⟨hSz, hc⟩
    · have hsq := isL2Square_bar2_conjClosure hL hxM hXsup hne hL2
      rw [← h2.1] at hsq
      exact Or.inr (Or.inl ⟨Or.inl hsq, h2.2.2.1, hc⟩)
    · have hsq := isSzSquare_bar2_conjClosure hL hxM hXsup hne hSz
      rw [← h2.1] at hsq
      exact Or.inr (Or.inr ⟨hsq, h2.2.2.1, hc⟩)
  · obtain ⟨hsh, h2n, hpow, hc⟩ := h3
    rcases hsh with hU | hL2
    · exact Or.inr (Or.inl ⟨Or.inr ⟨hU, hpow⟩, h2n, hc⟩)
    · exact Or.inr (Or.inl ⟨Or.inl hL2, h2n, hc⟩)

theorem gap19_11_rank_at (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (h42 : S17.R17_42At D V₀ V) (hK : K_19_11_torusFixed) (R : Subgroup G)
    (hR : InNM2 D (IOf D p L) B R) :
    ∃ E : Subgroup G, E ≤ IOf D p L ⊓ normalizer (R : Set G) ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ 2 := by
  classical
  set I := IOf D p L with hIdef
  obtain ⟨hp, hp2⟩ := D.sig_prime p h.hyp.hp
  have hMI : D.M ≤ normalizer (I : Set G) := le_normalizer_IOf D h.hyp.hL.1
  obtain ⟨hRM, hR2, hOR, hBR⟩ := hR
  have hAB : A ≤ B := h.hB ▸ le_sup_left
  have htB : t ∈ B := h.hB ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  let ρ := UC6S846.rhoL I
  let Q : Subgroup (MulAut (Bar2 I)) := (R.subgroupOf (normalizer (I : Set G))).map ρ
  have hQ2 : IsPGroup 2 Q := hR2.comap_subtype.map ρ
  have hρN : ∀ g : ↥(normalizer (I : Set G)), (g : G) ∈ normalizer (R : Set G) →
      ρ g ∈ normalizer (Q : Set (MulAut (Bar2 I))) := fun g hg =>
    Subgroup.le_normalizer_map ρ (Subgroup.mem_map_of_mem ρ
      (Subgroup.le_normalizer_comap (normalizer (I : Set G)).subtype hg))
  have hconj : ∀ x : ↥I, (x : G) ∈ B →
      MulAut.conj (QuotientGroup.mk x : Bar2 I) ∈ normalizer (Q : Set (MulAut (Bar2 I))) := by
    intro x hx
    have := hρN ⟨x, Subgroup.le_normalizer x.2⟩ (hBR hx)
    rwa [show ρ ⟨x, Subgroup.le_normalizer x.2⟩ = _ from UC6S846.rhoL_inner I x x.2] at this
  have hAbar : IsZModSq (barImage I A) (S17.nOf L) :=
    isZModSq_barImage h.hA (odd_card_of_ctx19_10 h) h.hAcard
  let tI : ↥I := ⟨t, h.htA⟩
  let tbar : Bar2 I := QuotientGroup.mk tI
  have ht2 : ∃ k : ℕ, orderOf tbar = 2 ^ k := by
    obtain ⟨k, hk⟩ := h.ht2
    have hdvd : orderOf tbar ∣ 2 ^ k := by
      rw [← hk, ← Subgroup.orderOf_mk t h.htA]
      exact orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) tI
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨j, hj⟩
  have hinv : ∀ a ∈ barImage I A, tbar * a * tbar⁻¹ = a⁻¹ := by
    rintro _ ⟨a, ha, rfl⟩
    have ha' : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp ha
    have hta : tI * a * tI⁻¹ = a⁻¹ := Subtype.ext (by simpa using h.hinv _ ha')
    change (QuotientGroup.mk' (CFSG.pCore 2 ↥I) tI) * (QuotientGroup.mk' _ a) *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥I) tI)⁻¹ = (QuotientGroup.mk' _ a)⁻¹
    rw [← map_mul, ← map_inv, ← map_mul, hta, map_inv]
  have hnorm : ∀ b ∈ barImage I A ⊔ Subgroup.zpowers tbar,
      MulAut.conj b ∈ normalizer (Q : Set (MulAut (Bar2 I))) := by
    intro b hb
    have hle : barImage I A ⊔ Subgroup.zpowers tbar ≤
        (normalizer (Q : Set (MulAut (Bar2 I)))).comap MulAut.conj := by
      refine sup_le ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩
        exact hconj a (hAB (Subgroup.mem_subgroupOf.mp ha))
      · exact (Subgroup.zpowers_le).mpr (hconj tI htB)
    exact hle hb
  obtain ⟨Ebar, hEel, hEcard, hEfix⟩ :=
    hK (Bar2 I) (S17.nOf L) p hp (shape1911_of_ctx D h h42) (barImage I A) tbar hAbar ht2
      hinv Q hQ2 hnorm
  obtain ⟨E', hE'le, hE'el, hE'card⟩ :=
    uc22p20d_lift_elemAbelian (CFSG.pCore 2 ↥I) (CFSG.pCore_isPGroup (p := 2) (G := ↥I)) hp hp2
      (Ebar.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥I))) Ebar hEel hEcard
      (by rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)])
  refine ⟨E'.map I.subtype, le_inf (Subgroup.map_subtype_le E') ?_, hE'el.map I.subtype, ?_⟩
  ·
    rw [Subgroup.le_normalizer_iff_commutator_le_left, Subgroup.commutator_le]
    rintro x hx _ ⟨e, he, rfl⟩
    have hxI : x ∈ normalizer (I : Set G) := hMI (hRM hx)
    have hfix := hEfix (ρ ⟨x, hxI⟩)
      (Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.mpr hx)) _ (hE'le he)
    exact hOR ((UC6S846.rhoL_fix_iff I ⟨x, hxI⟩ e).mp hfix)
  · rw [Subgroup.card_map_of_injective I.subtype_injective, hE'card]

theorem nineteen_eleven_of_K (D : Data G) {V₀ V : Subgroup G} (h61 : UC6.R6_1 D)
    (h42 : S17.R17_42At D V₀ V) (hK : K_19_11_torusFixed) :
    ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (h : Ctx19_10 D V₀ V p L A t B r), R19_11At D V₀ V p L A t B r h :=
  fun _p _L _A _t _B _r h =>
    nineteen_eleven_of_exists D h h61 (fun R hR => gap19_11_rank_at D h h42 hK R hR)

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
