module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBShapeB1

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L : Subgroup G} {F0 : Type} [Field F0] [Finite F0]
  [CharP F0 2] {m : ℕ} {ψ : Su F0 2 1 m →* G}
  {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)}

theorem qtwoDB3_exists_t_of_aug {m : ℕ} (hBs : GGBstar 3 B Bs) (hxB : x ∈ B)
    (hBmax : LargeEvenIsBmax 3 B)
    (hT : ∃ T : Subgroup G, T ≤ Subgroup.centralizer ({x} : Set G) ∧ IsPGroup 2 T ∧
      B ≤ Subgroup.normalizer (T : Set G) ∧ (⁅T, B⁆ : Subgroup G) ≠ ⊥)
    (hBsCard : Nat.card ↥Bs = 3 ^ m)
    (hAug : 3 ^ (m - 1) ≤ Nat.card ↥(Subgroup.zpowers x ⊔ (Bs ⊓ L)))
    (hcase : B ≠ Bs ∨ Subgroup.zpowers x ⊔ (Bs ⊓ L) = Bs) :
    ∃ T : Subgroup G, T ≤ Subgroup.centralizer ({x} : Set G) ∧ IsPGroup 2 T ∧
      B ≤ Subgroup.normalizer (T : Set G) ∧
      ∃ t ∈ T, ∃ b ∈ B, ⁅t, b⁆ ∉ Subgroup.centralizer (L : Set G) := by
  obtain ⟨T, hTx, hT2, hBT, hTB⟩ := hT
  refine ⟨T, hTx, hT2, hBT, ?_⟩
  by_contra hcon
  push Not at hcon
  have hpp : Nat.Prime 3 := Nat.prime_three
  let K : Subgroup G := ⁅T, B⁆
  have hKne : K ≠ ⊥ := hTB
  have hKcent : K ≤ Subgroup.centralizer (L : Set G) := Subgroup.commutator_le.mpr hcon
  have hKleT : K ≤ T := by
    refine Subgroup.commutator_le.mpr ?_
    intro t ht b hb
    have hbT : b * t⁻¹ * b⁻¹ ∈ T :=
      ((Subgroup.mem_normalizer_iff.mp (hBT hb)) t⁻¹).mp (T.inv_mem ht)
    have hmem := T.mul_mem ht hbT
    simpa only [commutatorElement_def, mul_assoc] using hmem
  have hK2 : IsPGroup 2 K := hT2.to_le hKleT
  have hBK : B ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.normalizer_commutator_ge_right T B
  have hSK : Bs ⊓ L ≤ Subgroup.normalizer (K : Set G) := by
    have hLnorm : L ≤ Subgroup.normalizer (K : Set G) :=
      (Subgroup.le_centralizer_iff.mpr hKcent).trans
        (Subgroup.centralizer_le_normalizer (K : Set G))
    exact (inf_le_right : Bs ⊓ L ≤ L).trans hLnorm
  have hEK : B ⊔ (Bs ⊓ L) ≤ Subgroup.normalizer (K : Set G) := sup_le hBK hSK
  have hEab : CFSG.Open.IsElemAbelian 3 (B ⊔ (Bs ⊓ L)) :=
    hBs.2.1.mono (sup_le hBs.1 inf_le_left)
  have hEcard : Nat.card ↥(B ⊔ (Bs ⊓ L)) ≤ Nat.card ↥B :=
    qtwoDB3_bmax_le hpp hBmax hEab ⟨K, hKne, hK2, hEK⟩
  have hEeqB : B ⊔ (Bs ⊓ L) = B :=
    (Subgroup.eq_of_le_of_card_ge le_sup_left hEcard).symm
  have hSB : Bs ⊓ L ≤ B := by
    rw [← hEeqB]
    exact le_sup_right
  have hQB : Subgroup.zpowers x ⊔ (Bs ⊓ L) ≤ B :=
    sup_le (Subgroup.zpowers_le.mpr hxB) hSB
  have hQeqB : Subgroup.zpowers x ⊔ (Bs ⊓ L) = B := by
    rcases hcase with hne | haug
    · have hQcard_ge : 3 ^ (m - 1) ≤ Nat.card ↥(Subgroup.zpowers x ⊔ (Bs ⊓ L)) :=
        hAug
      have hQleB : Nat.card ↥(Subgroup.zpowers x ⊔ (Bs ⊓ L)) ≤ Nat.card ↥B :=
        Subgroup.card_le_of_le hQB
      have hBdvd : Nat.card ↥B ∣ 3 ^ m := by
        have h := Subgroup.card_dvd_of_le hBs.1
        rwa [hBsCard] at h
      have hBne : Nat.card ↥B ≠ 3 ^ m := by
        intro hcard
        exact hne (Subgroup.eq_of_le_of_card_ge hBs.1 (by rw [hcard, hBsCard]))
      obtain ⟨k, hkm, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hBdvd
      have hklt : k < m := by
        rcases lt_or_eq_of_le hkm with h | h
        · exact h
        · exfalso
          exact hBne (by rw [hk, h])
      have hBcard_le : Nat.card ↥B ≤ 3 ^ (m - 1) := by
        rw [hk]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have hQcard : Nat.card ↥(Subgroup.zpowers x ⊔ (Bs ⊓ L)) = Nat.card ↥B :=
        le_antisymm hQleB (hBcard_le.trans hQcard_ge)
      exact Subgroup.eq_of_le_of_card_ge hQB (le_of_eq hQcard.symm)
    · exact le_antisymm hQB (haug.symm ▸ hBs.1)
  have hTcentB : T ≤ Subgroup.centralizer (B : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hQcent : Subgroup.zpowers x ⊔ (Bs ⊓ L) ≤ Subgroup.centralizer ({t} : Set G) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp (hTx ht)).symm
      · intro l hl
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hlL : l ∈ L := hl.2
        have hlB : l ∈ B := hSB hl
        have hz1 : ⁅t, l⁆ = 1 := by
          have hzcent : ⁅t, l⁆ ∈ Subgroup.centralizer (L : Set G) :=
            hKcent (Subgroup.commutator_mem_commutator ht hlB)
          have hzT : ⁅t, l⁆ ∈ T := by
            have hbT : l * t⁻¹ * l⁻¹ ∈ T :=
              ((Subgroup.mem_normalizer_iff.mp (hBT hlB)) t⁻¹).mp (T.inv_mem ht)
            have hmem := T.mul_mem ht hbT
            simpa only [commutatorElement_def, mul_assoc] using hmem
          have hl3 : l ^ 3 = 1 := hBs.2.1.2 l hl.1
          have hzl : Commute ⁅t, l⁆ l :=
            (commute_iff_eq _ _).mpr ((Subgroup.mem_centralizer_iff.mp hzcent) l hlL).symm
          have hpow : (⁅t, l⁆ * l) ^ 3 = 1 := by
            calc (⁅t, l⁆ * l) ^ 3 = (t * l * t⁻¹) ^ 3 := by
                  rw [commutatorElement_def]
                  group
              _ = t * l ^ 3 * t⁻¹ := by
                  simpa only [MulAut.conj_apply] using (map_pow (MulAut.conj t) l 3).symm
              _ = 1 := by rw [hl3]; group
          have hz3 : ⁅t, l⁆ ^ 3 = 1 := by
            rwa [hzl.mul_pow, hl3, mul_one] at hpow
          obtain ⟨k', hk'⟩ := hT2 ⟨⁅t, l⁆, hzT⟩
          have hz2 : ⁅t, l⁆ ^ (2 ^ k') = 1 := by
            have hcoe := congrArg (fun w : T => (w : G)) hk'
            simpa using hcoe
          have hcop : Nat.Coprime 3 (2 ^ k') :=
            Nat.prime_two.coprime_pow_of_not_dvd (m := k') (by norm_num)
          have hord3 : orderOf ⁅t, l⁆ ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hz3
          have hord2 : orderOf ⁅t, l⁆ ∣ 2 ^ k' := orderOf_dvd_iff_pow_eq_one.mpr hz2
          exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hord3 hord2)
        rw [commutatorElement_eq_one_iff_mul_comm] at hz1
        exact hz1.symm
    have hbQ : b ∈ Subgroup.zpowers x ⊔ (Bs ⊓ L) := by rw [hQeqB]; exact hb
    exact Subgroup.mem_centralizer_singleton_iff.mp (hQcent hbQ)
  exact hTB (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hTcentB)

theorem qtwoDB3_exists_t (hbase : QTwoUnitBase p B Bs x L ψ ε) (hm : 5 ≤ m)
    (hBs : GGBstar p B Bs) (hxB : x ∈ B) (_hBL : B ≤ Subgroup.normalizer (L : Set G))
    (_hLn : ∀ g ∈ Subgroup.centralizer ({x} : Set G), g ∈ Subgroup.normalizer (L : Set G))
    (hBmax : LargeEvenIsBmax p B)
    (hT : ∃ T : Subgroup G, T ≤ Subgroup.centralizer ({x} : Set G) ∧ IsPGroup 2 T ∧
      B ≤ Subgroup.normalizer (T : Set G) ∧ (⁅T, B⁆ : Subgroup G) ≠ ⊥) (hne : B ≠ Bs ∨ ¬ 3 ∣ m) :
    ∃ T : Subgroup G, T ≤ Subgroup.centralizer ({x} : Set G) ∧ IsPGroup 2 T ∧
      B ≤ Subgroup.normalizer (T : Set G) ∧
      ∃ t ∈ T, ∃ b ∈ B, ⁅t, b⁆ ∉ Subgroup.centralizer (L : Set G) := by
  have hp3 := hbase.p_eq
  subst p
  have hcase : B ≠ Bs ∨ Subgroup.zpowers x ⊔ (Bs ⊓ L) = Bs := by
    rcases hne with hne | hm3
    · exact Or.inl hne
    · exact Or.inr (qtwoDB3_aug_eq_of_not_dvd hbase hm hm3)
  exact qtwoDB3_exists_t_of_aug hBs hxB hBmax hT hbase.card_bs
    (qtwoDB3_card_aug hbase hm) hcase

end CFSG.StandardType.QTwo

end
