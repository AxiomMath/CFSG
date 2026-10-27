module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGAltE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.Open

theorem s1614_hyp2iii_alt {n : ℕ} (hn : 6 ≤ n) : S1614Hyp2iii (FFModel.altDn n) := by
  intro H hkH hHs h2
  obtain ⟨a, b, c, hab, hac, hbc, hpab, hpac⟩ := s1614_exists_three_pairs hn hHs h2
  obtain ⟨E, hEab, hE9, hEst⟩ := s1614_alt_exists_E hn hab hac hbc
  have hkl : s1614_altKlein n a b c ≤ H :=
    (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨hpab, Set.singleton_subset_iff.2 hpac⟩)
  have hinf : (Subgroup.zpowers (allOnes n) ⊓ coreMod n) ⊓ s1614_altKlein n a b c = ⊥ := by
    rw [inf_comm]
    exact s1614_altKlein_inf_ker hn hab hac hbc
  refine ⟨(Subgroup.zpowers (allOnes n) ⊓ coreMod n) ⊔ s1614_altKlein n a b c, le_sup_left,
    sup_le hkH hkl, ?_, E, hEab, hE9, ?_, ?_⟩
  · have h : Nat.card ↥((Subgroup.zpowers (allOnes n) ⊓ coreMod n) ⊔ s1614_altKlein n a b c) *
        Nat.card ↥((Subgroup.zpowers (allOnes n) ⊓ coreMod n) ⊓ s1614_altKlein n a b c) =
        Nat.card ↥(Subgroup.zpowers (allOnes n) ⊓ coreMod n) *
          Nat.card ↥(s1614_altKlein n a b c) :=
      card_sup_mul_card_inf (Subgroup.zpowers (allOnes n) ⊓ coreMod n) (s1614_altKlein n a b c)
    rw [hinf, Subgroup.card_bot, mul_one, s1614_altKlein_card hab hac hbc] at h
    show Nat.card ↥((Subgroup.zpowers (allOnes n) ⊓ coreMod n) ⊔ s1614_altKlein n a b c) =
      4 * Nat.card ↥(Subgroup.zpowers (allOnes n) ⊓ coreMod n)
    rw [h, mul_comm]
  · rintro (e : ↥(alternatingGroup (Fin n))) he x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hx
    show permAct n (e : Equiv.Perm (Fin n)) (y * z) ∈ _
    have hm : permAct n (e : Equiv.Perm (Fin n)) (y * z) =
        permAct n (e : Equiv.Perm (Fin n)) y * permAct n (e : Equiv.Perm (Fin n)) z :=
      (permAct n (e : Equiv.Perm (Fin n))).map_mul y z
    rw [hm]
    refine Subgroup.mul_mem_sup ?_ (hEst e he z hz)
    obtain ⟨hy1, hy2⟩ := hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy1
    have hk : permAct n (e : Equiv.Perm (Fin n)) (allOnes n ^ k) = allOnes n ^ k := by
      rw [map_zpow, s1614_permAct_allOnes]
      rfl
    have hmem : permAct n (e : Equiv.Perm (Fin n)) (allOnes n ^ k) ∈
        Subgroup.zpowers (allOnes n) := by
      rw [hk]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
    exact Subgroup.mem_inf.2 ⟨hmem, permAct_mem_coreMod _ hy2⟩
  · rintro (e : ↥(alternatingGroup (Fin n))) _ h
    exact Subtype.ext (s1614_alt_faithful (n := n) (by omega) (e : Equiv.Perm (Fin n)) h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
