module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResCore
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qk

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem uc22p22qp_Op_le_sup {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime] {S : Subgroup H}
    (hS : IsSylowOf p S (CFSG.Op_p'p p H)) :
    CFSG.Op_p'p p H ≤ CFSG.pPrimeCore p H ⊔ S := by
  set K₀ : Subgroup H := CFSG.Op_p'p p H with hK₀
  set Q' : Subgroup H := CFSG.pPrimeCore p H with hQ'
  have hQK : Q' ≤ K₀ := pPrimeCore_le_Op_p'p
  have hpow : ∃ k : ℕ, Q'.relIndex K₀ = p ^ k := by
    haveI : (Q'.subgroupOf K₀).Normal := Subgroup.normal_subgroupOf
    have hp : IsPGroup p (↥K₀ ⧸ Q'.subgroupOf K₀) := by
      intro x
      induction x using QuotientGroup.induction_on with
      | H y =>
        obtain ⟨k, hk⟩ := exists_pow_mem_pPrimeCore_of_mem_Op_p'p (p := p) y.2
        refine ⟨k, ?_⟩
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
        exact (Subgroup.mem_subgroupOf).2 (by simpa using hk)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hp
    refine ⟨k, ?_⟩
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
    exact hk
  obtain ⟨k, hk⟩ := hpow
  have hT : (Q' ⊔ S).relIndex K₀ = 1 := by
    have h1 : (Q' ⊔ S).relIndex K₀ ∣ Q'.relIndex K₀ := Subgroup.relIndex_dvd_of_le_left K₀ le_sup_left
    have h2 : (Q' ⊔ S).relIndex K₀ ∣ S.relIndex K₀ := Subgroup.relIndex_dvd_of_le_left K₀ le_sup_right
    rw [hk] at h1
    obtain ⟨i, -, hi'⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 h1
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · rw [hi', h0, pow_zero]
    · exfalso
      have : p ∣ (Q' ⊔ S).relIndex K₀ := by
        rw [hi']
        exact dvd_pow_self p hpos.ne'
      exact (isSylowOf_iff.1 hS).2.2 (this.trans h2)
  exact Subgroup.relIndex_eq_one.1 hT

theorem uc22p22qp_K_le_sup {p : ℕ} [Fact p.Prime] {M S : Subgroup G}
    (hS : IsSylowOf p S ((CFSG.Op_p'p p ↥M).map M.subtype)) :
    (CFSG.Op_p'p p ↥M).map M.subtype ≤ (CFSG.pPrimeCore p ↥M).map M.subtype ⊔ S := by
  have hSM : S ≤ M := hS.le.trans (Subgroup.map_subtype_le _)
  have hS' : IsSylowOf p (S.subgroupOf M) (CFSG.Op_p'p p ↥M) := by
    refine (isSylowOf_map_subtype_iff (p := p) M (A := S.subgroupOf M) (B := CFSG.Op_p'p p ↥M)).1 ?_
    rwa [Subgroup.map_subgroupOf_eq_of_le hSM]
  have h := Subgroup.map_mono (f := M.subtype) (uc22p22qp_Op_le_sup hS')
  rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hSM] at h

theorem uc22p22qp_normal_of_strongly_closed {p : ℕ} [Fact p.Prime] {M P A : Subgroup G}
    (hsolv : Group.IsSolvable ↥M) (hP : IsSylowOf p P M) (hAP : A ≤ P) (hA1 : A ≠ ⊥)
    (hsc : ∀ a ∈ A, ∀ m ∈ M, m⁻¹ * a * m ∈ P → m⁻¹ * a * m ∈ A)
    (hirr : ∀ N : Subgroup G, N ≤ M → (∀ m ∈ M, ∀ k ∈ N, m * k * m⁻¹ ∈ N) → A ⊓ N = ⊥ ∨ A ≤ N) :
    M ≤ normalizer ((A ⊔ uniqueFourPrimeCore p M : Subgroup G) : Set G) := by
  have hpP : p.Prime := Fact.out
  have hPM : P ≤ M := hP.le
  have hAM : A ≤ M := hAP.trans hPM
  set K : Subgroup G := (CFSG.Op_p'p p ↥M).map M.subtype with hK
  set Q : Subgroup G := uniqueFourPrimeCore p M with hQ
  have hQ' : Q = (CFSG.pPrimeCore p ↥M).map M.subtype :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map hpP M
  have hKM : K ≤ M := Subgroup.map_subtype_le _
  have hKnorm : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K := by
    intro m hm k hk
    obtain ⟨k₀, hk₀, rfl⟩ := hk
    exact ⟨⟨m, hm⟩ * k₀ * ⟨m, hm⟩⁻¹, (CFSG.Op_p'p_normal p ↥M).conj_mem k₀ hk₀ ⟨m, hm⟩, by simp⟩
  have hQK : Q ≤ K := by
    rw [hQ']
    exact Subgroup.map_mono pPrimeCore_le_Op_p'p
  have hQnorm : ∀ m ∈ M, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q := fun m hm q hq =>
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_conj_mem hq hm
  have hKN : M ≤ normalizer (K : Set G) := fun m hm => uc22p22qk_mem_normalizer fun k hk => hKnorm m hm k hk
  set S₀ : Subgroup G := P ⊓ K with hS₀def
  have hS₀ : IsSylowOf p S₀ K := hP.inf_of_le_normalizer hKM hKN
  have hS₀M : S₀ ≤ M := inf_le_left.trans hPM
  have hHH : ∀ x ∈ M, (∀ s ∈ S₀, x * s = s * x) → x ∈ K := by
    intro x hx hc
    have hS' : IsSylowOf p (S₀.subgroupOf M) (CFSG.Op_p'p p ↥M) := by
      refine (isSylowOf_map_subtype_iff (p := p) M (A := S₀.subgroupOf M) (B := CFSG.Op_p'p p ↥M)).1 ?_
      rwa [Subgroup.map_subgroupOf_eq_of_le hS₀M]
    have h1 := isPConstrained_of_isSolvable (p := p) (H := ↥M) hsolv (S₀.subgroupOf M) hS'
    have h2 : (⟨x, hx⟩ : ↥M) ∈ centralizer ((S₀.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      apply Subtype.ext
      exact (hc (s : G) hs).symm
    exact ⟨⟨x, hx⟩, h1 h2, rfl⟩
  have hAK : A ≤ K := by
    rcases hirr K hKM hKnorm with h | h
    · exfalso
      apply hA1
      rw [eq_bot_iff]
      intro a ha
      have hac : ∀ s ∈ S₀, a * s = s * a := by
        intro s hs
        have hsP : s ∈ P := hs.1
        have hsK : s ∈ K := hs.2
        have hsM : s ∈ M := hS₀M hs
        have h1 : s⁻¹ * a * s ∈ A :=
          hsc a ha s hsM (P.mul_mem (P.mul_mem (P.inv_mem hsP) (hAP ha)) hsP)
        have h2 : s⁻¹ * a * s * a⁻¹ ∈ K := by
          have := K.mul_mem (K.inv_mem hsK) (hKnorm a (hAM ha) s hsK)
          simpa [mul_assoc] using this
        have h3 : s⁻¹ * a * s * a⁻¹ ∈ A := A.mul_mem h1 (A.inv_mem ha)
        have h4 : s⁻¹ * a * s * a⁻¹ ∈ A ⊓ K := ⟨h3, h2⟩
        rw [h, Subgroup.mem_bot] at h4
        have h5 : s⁻¹ * a * s = a := by
          calc s⁻¹ * a * s = (s⁻¹ * a * s * a⁻¹) * a := by group
            _ = a := by rw [h4, one_mul]
        calc a * s = s * (s⁻¹ * a * s) := by group
          _ = s * a := by rw [h5]
      have hmem : a ∈ K := hHH a (hAM ha) hac
      have h6 : a ∈ A ⊓ K := ⟨ha, hmem⟩
      rw [h] at h6
      exact h6
    · exact h
  have hdec : ∀ k ∈ K, ∃ q ∈ Q, ∃ s ∈ S₀, k = q * s := by
    intro k hk
    have hk' : k ∈ Q ⊔ S₀ := by
      have h := uc22p22qp_K_le_sup (M := M) (S := S₀) hS₀
      rw [← hQ'] at h
      exact h hk
    have hSN : S₀ ≤ normalizer (Q : Set G) := fun s hs =>
      uc22p22qk_mem_normalizer fun q hq => hQnorm s (hS₀M hs) q hq
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left Q S₀ hSN] at hk'
    obtain ⟨q, hq, s, hs, hqs⟩ := hk'
    have hqs' : q * s = k := hqs
    exact ⟨q, hq, s, hs, hqs'.symm⟩
  have key : ∀ m ∈ M, ∀ a ∈ A, m * a * m⁻¹ ∈ A ⊔ Q := by
    intro m hm a ha
    have hAp : IsPGroup p ↥A := hP.isPGroup.to_le hAP
    have hXp : IsPGroup p ↥(A.map (MulAut.conj m).toMonoidHom) :=
      hAp.of_equiv (Subgroup.equivMapOfInjective _ _ (MulAut.conj m).injective)
    have hXK : A.map (MulAut.conj m).toMonoidHom ≤ K := by
      rintro _ ⟨a', ha', rfl⟩
      exact hKnorm m hm a' (hAK ha')
    obtain ⟨k, hkK, hk⟩ := UC6.exists_conj_le_of_isSylowOf hS₀ hXK hXp
    obtain ⟨q, hq, s, hs, rfl⟩ := hdec k hkK
    have hb : q⁻¹ * (m * a * m⁻¹) * q ∈ S₀ := by
      have h1 := hk (m * a * m⁻¹) ⟨a, ha, rfl⟩
      have h2 : q⁻¹ * (m * a * m⁻¹) * q =
          s * ((q * s)⁻¹ * (m * a * m⁻¹) * (q * s)) * s⁻¹ := by group
      rw [h2]
      exact S₀.mul_mem (S₀.mul_mem hs h1) (S₀.inv_mem hs)
    have hqM : q ∈ M := hKM (hQK hq)
    have hbA : q⁻¹ * (m * a * m⁻¹) * q ∈ A := by
      have h3 := hsc a ha (m⁻¹ * q) (M.mul_mem (M.inv_mem hm) hqM) (by
        have e : (m⁻¹ * q)⁻¹ * a * (m⁻¹ * q) = q⁻¹ * (m * a * m⁻¹) * q := by group
        rw [e]
        exact hb.1)
      have e : (m⁻¹ * q)⁻¹ * a * (m⁻¹ * q) = q⁻¹ * (m * a * m⁻¹) * q := by group
      rwa [e] at h3
    set b : G := q⁻¹ * (m * a * m⁻¹) * q with hbdef
    have hbM : b ∈ M := hAM hbA
    have hq2 : b⁻¹ * q * b * q⁻¹ ∈ Q := by
      have h4 := hQnorm b⁻¹ (M.inv_mem hbM) q hq
      have h5 : b⁻¹ * q * b ∈ Q := by simpa using h4
      exact Q.mul_mem h5 (Q.inv_mem hq)
    have hexp : m * a * m⁻¹ = b * (b⁻¹ * q * b * q⁻¹) := by
      rw [hbdef]
      group
    rw [hexp]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hbA) (Subgroup.mem_sup_right hq2)
  intro m hm
  have hmap : (A ⊔ Q).map (MulAut.conj m).toMonoidHom ≤ A ⊔ Q := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact key m hm a ha
    · rintro _ ⟨q, hq, rfl⟩
      exact Subgroup.mem_sup_right (hQnorm m hm q hq)
  exact CFSG.Goldschmidt.G310.mem_normalizer_of_map_le hmap

end CFSG.LocalAnalysis.UniquenessCase.UC22
