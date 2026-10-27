module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S214U
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20yc
public import CFSG.Quasithin.Background.B2FactorizationResidual

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def uc22pwAlike (D : Data G) (L : Subgroup G) (F : Subgroup (Bar2 L)) : Prop :=
  ∀ φ ∈ uc22p20uA D L, ∀ φ' ∈ uc22p20uA D L, (∀ x ∈ F, φ x ∈ F) → (∀ x ∈ F, φ' x ∈ F) →
    (∀ x ∈ F, φ (φ x) = x) → (∃ x ∈ F, φ x ≠ x) → (∀ x ∈ F, φ' (φ' x) = x) → (∃ x ∈ F, φ' x ≠ x) →
      ∀ x ∈ F, φ x = φ' x

@[expose] def uc22pwNoInv (D : Data G) (L : Subgroup G) (F : Subgroup (Bar2 L)) : Prop :=
  ∀ φ ∈ uc22p20uA D L, ¬ ∀ x ∈ F, φ x = x⁻¹

theorem uc22pwc_fifteen_dvd {n : ℕ} (hp2 : IsPowTwo n) (hn : 2 < n) : 15 ∣ 2 ^ n - 1 := by
  obtain ⟨e, rfl⟩ := hp2
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 2 := by
    refine ⟨e - 2, ?_⟩
    rcases Nat.lt_or_ge e 2 with h | h
    · interval_cases e <;> simp at hn
    · omega
  have h4 : 2 ^ (k + 2) = 4 * 2 ^ k := by rw [pow_add]; ring
  rw [h4, pow_mul]
  have h := Nat.sub_dvd_pow_sub_pow (2 ^ 4) 1 (2 ^ k)
  rwa [show (2 : ℕ) ^ 4 - 1 = 15 by norm_num, one_pow] at h

theorem uc22pw_lift214_sel (D : Data G) (hB : ListBNonabelian) (h1930 : H1930 D) {L : Subgroup G}
    (hL : L ∈ calL D.T D.M) {n : ℕ} {E : Subgroup (Bar2 L)} (hE : uc22pwGood D L n E)
    {Bb Cb : Subgroup (Bar2 L)} (hBE : Bb ≤ E) (hCE : Cb ≤ E) (hcyc : IsCyclic Bb)
    (hsqf : Squarefree (Nat.card Bb))
    (hBinv : ∀ φ ∈ uc22p20uA D L, ∀ x ∈ Bb, φ x ∈ Bb ⊔ uc22p20iSylowBar D L)
    (hCinv : ∀ φ ∈ uc22p20uA D L, ∀ x ∈ Cb, φ x ∈ Cb ⊔ uc22p20iSylowBar D L)
    (hpiBC : piSet (Bb ⊔ Cb) = piSet E)
    (hCsyl : ∀ p : ℕ, p.Prime → p ∣ Nat.card Cb → ∃ P : Sylow p Cb, Nat.card P = p ^ 2 ∧ ¬ IsCyclic P)
    (hCirr : ∀ p : ℕ, p.Prime → p ∣ Nat.card Cb → ∀ W : Subgroup (Bar2 L), W ≤ pCoreOf p (Bb ⊔ Cb) →
      (∀ φ ∈ uc22p20uA D L, ∀ x ∈ W, φ x ∈ W ⊔ uc22p20iSylowBar D L) → W = ⊥ ∨ W = pCoreOf p (Bb ⊔ Cb))
    (hC1 : IsCyclic ↥(Bb ⊔ Cb) → uc22pwAlike D L (Bb ⊔ Cb))
    (hC2 : IsPowTwo n → uc22pwNoInv D L (Bb ⊔ Cb)) :
    ∃ B0 : Subgroup G, Choice214U D L B0 ∧ B0 ∈ calB1 D.T D.M L ∧ piSet B0 = etaSet n ∧
      AlphaCond D.T B0 n ∧ B0 ≤ D.M := by
  obtain ⟨A, hA, hcal, hpi, hα, hAM⟩ :=
    uc22pw_lift_sel D hB h1930 hL hE hBE hCE hcyc hsqf hBinv hCinv hpiBC hCsyl hCirr
  refine ⟨A, ?_, hcal, hpi, hα, hAM⟩
  by_cases hn : Odd n
  · exact choice214U_of_odd D hn hpi hα
  have hTL : D.T ≤ normalizer (L : Set G) := hL.1
  have hconj : ∀ {t : G} (htT : t ∈ D.T) {a : G}, a ∈ A →
      uc22pwrBar L (t * a * t⁻¹) = uc22p20uInd L t (hTL htT) (uc22pwrBar L a) :=
    fun htT _ ha => uc22pwrBar_conj (hTL htT) (hA.le ha)
  have hmaps : ∀ {t : G} (htT : t ∈ D.T), t ∈ normalizer (A : Set G) →
      ∀ x ∈ Bb ⊔ Cb, uc22p20uInd L t (hTL htT) x ∈ Bb ⊔ Cb := by
    intro t htT htA x hx
    obtain ⟨a, ha, rfl⟩ := hA.onto x hx
    rw [← hconj htT ha]
    exact hA.maps _ ((mem_normalizer_iff.1 htA a).1 ha)
  have hinvol : ∀ {t : G} (htT : t ∈ D.T), t ∈ normalizer (A : Set G) → ActsAsInvolution t A →
      (∀ x ∈ Bb ⊔ Cb, uc22p20uInd L t (hTL htT) (uc22p20uInd L t (hTL htT) x) = x) ∧
        ∃ x ∈ Bb ⊔ Cb, uc22p20uInd L t (hTL htT) x ≠ x := by
    rintro t htT htA ⟨h2, b, hb, hne⟩
    refine ⟨fun x hx => ?_, uc22pwrBar L b, hA.maps b hb, fun h => hne ?_⟩
    · obtain ⟨a, ha, rfl⟩ := hA.onto x hx
      have ha' : t * a * t⁻¹ ∈ A := (mem_normalizer_iff.1 htA a).1 ha
      rw [← hconj htT ha, ← hconj htT ha',
        show t * (t * a * t⁻¹) * t⁻¹ = t ^ 2 * a * (t ^ 2)⁻¹ by rw [pow_two]; group, h2 a ha]
    · refine hA.inj _ ((mem_normalizer_iff.1 htA b).1 hb) b hb ?_
      rw [hconj htT hb]
      exact h
  refine ⟨fun _ t htT htA hinv => ?_, fun hcycA s hsT t htT hsA htA hs ht b hb => ?_⟩
  · by_cases hp2 : IsPowTwo n
    · refine hC2 hp2 _ ⟨t, hTL htT, htT, rfl⟩ fun x hx => ?_
      obtain ⟨a, ha, rfl⟩ := hA.onto x hx
      rw [← hconj htT ha, hinv a ha, uc22pwrBar_inv (hA.le ha)]
    · exact ch214_inv_of_not_powTwo D hp2 hcal.2.1 hpi hα t htT htA hinv
  · haveI : IsCyclic ↥A := hcycA
    have hcycE : IsCyclic ↥(Bb ⊔ Cb) :=
      isCyclic_of_surjective hA.equiv.toMonoidHom hA.equiv.surjective
    obtain ⟨hs2, hs1⟩ := hinvol hsT hsA hs
    obtain ⟨ht2, ht1⟩ := hinvol htT htA ht
    have key := hC1 hcycE _ ⟨s, hTL hsT, hsT, rfl⟩ _ ⟨t, hTL htT, htT, rfl⟩ (hmaps hsT hsA)
      (hmaps htT htA) hs2 hs1 ht2 ht1 (uc22pwrBar L b) (hA.maps b hb)
    refine hA.inj _ ((mem_normalizer_iff.1 hsA b).1 hb) _ ((mem_normalizer_iff.1 htA b).1 hb) ?_
    rw [hconj hsT hb, hconj htT hb]
    exact key

theorem uc22pw_lift214 (D : Data G) (hB : ListBNonabelian) (h1930 : H1930 D) {L : Subgroup G}
    (hL : L ∈ calL D.T D.M) {n : ℕ} (hn : 2 < n) {E : Subgroup (Bar2 L)} (hE : uc22pwGood D L n E)
    (hC1 : ∀ F : Subgroup (Bar2 L), F ≤ E → uc22pwAlike D L F)
    (hC2 : ∀ φ ∈ uc22p20uA D L, ∀ x₃ ∈ E, ∀ x₅ ∈ E, orderOf x₃ = 3 → orderOf x₅ = 5 →
      φ x₃ * x₃ ∈ uc22p20iSylowBar D L → φ x₅ * x₅ ∈ uc22p20iSylowBar D L → False) :
    ∃ B0 : Subgroup G, Choice214U D L B0 ∧ B0 ∈ calB1 D.T D.M L ∧ piSet B0 = etaSet n ∧
      AlphaCond D.T B0 n ∧ B0 ≤ D.M := by
  obtain ⟨hEU, hEab, hEodd, hrank, hpi, hinv, -⟩ := id hE
  have hΦU : ∀ φ ∈ uc22p20uA D L, ∀ x : Bar2 L,
      x ∈ uc22p20iSylowBar D L ↔ φ x ∈ uc22p20iSylowBar D L := by
    rintro _ ⟨t, ht, htT, rfl⟩ x
    exact uc22p20u_ind_sylowBar D hL ht htT x
  have hΦE : ∀ φ ∈ uc22p20uA D L, ∀ x ∈ E, φ x ∈ E ⊔ uc22p20iSylowBar D L := by
    rintro _ ⟨t, ht, htT, rfl⟩ x hx
    exact hinv t ht htT x hx
  obtain ⟨Bb, Cb, hBE, hCE, -, hcyc, hsqf, hBinv, hCinv, hpiBC, hCsyl, hCirr⟩ :=
    uc22pw_select_mod hEU (uc22p20i_sylowBar_isPGroup D) hEab hEodd hrank (uc22p20uA D L) hΦU hΦE
  have hE₀E : Bb ⊔ Cb ≤ E := sup_le hBE hCE
  refine uc22pw_lift214_sel D hB h1930 hL hE hBE hCE hcyc hsqf hBinv hCinv hpiBC hCsyl hCirr
    (fun _ => hC1 _ hE₀E) fun hp2 φ hφ hinvφ => ?_
  have hel : ∀ p : ℕ, p.Prime → p ∣ 15 → ∃ x ∈ Bb ⊔ Cb, orderOf x = p := by
    intro p hp hp15
    have hpE : p ∈ piSet (Bb ⊔ Cb) := by
      rw [hpiBC, hpi]
      exact ⟨hp, hp15.trans (uc22pwc_fifteen_dvd hp2 hn)⟩
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Bb ⊔ Cb)) p hpE.2
    exact ⟨x, x.2, by rw [Subgroup.orderOf_coe, hx]⟩
  obtain ⟨x₃, hx₃, ho₃⟩ := hel 3 Nat.prime_three (by norm_num)
  obtain ⟨x₅, hx₅, ho₅⟩ := hel 5 Nat.prime_five (by norm_num)
  refine hC2 φ hφ x₃ (hE₀E hx₃) x₅ (hE₀E hx₅) ho₃ ho₅ ?_ ?_
  · rw [hinvφ x₃ hx₃, inv_mul_cancel]
    exact one_mem _
  · rw [hinvφ x₅ hx₅, inv_mul_cancel]
    exact one_mem _

end CFSG.LocalAnalysis.UniquenessCase.UC22
