module

public import CFSG.LocalAnalysis.StandardType.GGF4H4ListSpCore
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUSigned
import CFSG.LocalAnalysis.StandardType.GGKGASp
import CFSG.LocalAnalysis.StandardType.GGKGAAutomizer
import CFSG.LocalAnalysis.StandardType.GGTBWNormSymplectic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggF4H4Sp_symplectic_labelAll
    {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime) (hp2 : p ≠ 2)
    (htag : lab.tag = .B ∨ lab.tag = .C) (hℓ : 2 ≤ lab.rank)
    (hpq : p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ =>
      GGCenterPrime p R ∧ GGTorusSignedEltSC p R ∧ Subgroup.center R = ⊥ ∧
        I ⊆ Set.range (MulAut.conj : R →* MulAut R) ∧ GGTorusSCRank p lab.rank R I ∧
        ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
          ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → ∀ A : Subgroup (MulAut L'),
            IsElemAbelian p A → (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
              Nat.card A ≤ p ^ lab.rank := by
  obtain ⟨t, ℓ, n⟩ := lab
  dsimp only at htag hℓ hpq ⊢
  have : NeZero ℓ := ⟨by omega⟩
  have hpq2 : p ∣ (2 ^ n) ^ 2 - 1 := by
    have hfac : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      obtain ⟨q, hq⟩ : ∃ q, 2 ^ n = q + 1 := ⟨2 ^ n - 1, by omega⟩
      rw [hq]
      simp only [Nat.add_sub_cancel]
      ring_nf
      omega
    rw [hfac]
    rcases hpq with h | h
    · exact Dvd.dvd.mul_left h _
    · exact Dvd.dvd.mul_right h _
  rcases htag with rfl | rfl <;>
  · intro Q hQ
    obtain ⟨F, _, _, hF, hQF⟩ := hQ
    have : CharP F 2 := charP_two_of_card hF
    refine ⟨F, inferInstance, inferInstance, hF, hQF, ggCenterPrime_sp hp hp2, ?_,
      TableBSymp.center_spProj_eq_bot, TableBSymp.sp_I_subset_inn,
      KGA.kga_torusSCRank_sp (by omega) hp hp2 (by rwa [hF]),
      fun L' _ _ ψ hψ hker hperf A hA hAI => KGA.kga_card_le_sp hp hp2 hψ hker hperf hA hAI⟩
    rcases hpq with hs | hn
    · exact SpModel.ggTorusSignedEltSC_sp hp hp2 (by rwa [hF])
    · exact ggSpNonsplitSignedEltInput_holds F ℓ p hℓ hp (by rwa [hF])

theorem ggF4H4ListSp_BC :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (ks : Finset (Subgroup G)), GGF4SmallRes p B Bs x L D J ks →
      (∀ K ∈ ks, GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer K Bs)) → ∀ K ∈ ks,
        ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → (lab.tag = .B ∨ lab.tag = .C) →
          GGHasLabel lab (K ⧸ Subgroup.center K) → GGF4NbrList p K := by
  intro G _ _ p B Bs x L D J ks hres hB K hK lab hΛ htag hlab
  classical
  have hcfg : GGConfig p B Bs x L D J := hres.1.1.1
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hℓ : 2 ≤ lab.rank := by
    obtain ⟨t, ℓ, n⟩ := lab
    rcases htag with h | h <;> dsimp only at h <;> subst h <;> exact hΛ.2.1
  have hpq := F4H4Sp.halfSplit_dvd_at_nbr hres hK hΛ
    (by rcases htag with h | h <;> simp [GGF4TagClassical, h])
    (htag.elim Or.inl fun h => Or.inr (Or.inl h)) hlab
  obtain ⟨R, _, I, F, θ, hN, ⟨hcp, hsgnSC, hZ, hI, hSCr, hle⟩, hTB, -, -, hW48⟩ :=
    F4H4Sp.exists_model_at_nbr hres hB hK hΛ hlab
      (ggF4H4Sp_symplectic_labelAll hp hp2 htag hℓ hpq) (fun _ _ _ _ h => h.1)
  obtain ⟨hψ, hker, hperf, hA, hAI, -, h3, hsc⟩ := hTB
  obtain ⟨k, Θ, -, hW, hsgn, hperm, hsp⟩ :=
    exists_signedModelSC hp hp2 hI hZ hcp hsgnSC hψ hker hperf hA hAI h3 hsc
  have hk : k = 3 := by
    have h := KGA.kga_card_automizer hp hp2 Θ hsgn hperm hsp
    rw [hW48 hW] at h
    exact F4H4Sp.eq_three_of_two_pow_mul_factorial h.symm
  have hkℓ : k = lab.rank := KGA.kga_k_eq hp Θ
    (hSCr K (ggQuotHom θ) hψ hker hperf _ hA hAI hsc) (hle K (ggQuotHom θ) hψ hker hperf _ hA hAI)
  refine Or.inl ⟨lab.n, hΛ.1, hpq, Or.inl ?_⟩
  have h3r : lab.rank = 3 := by omega
  have hC := F4H4Sp.ggHasLabel_C_of_tag htag hlab
  rwa [h3r] at hC

end CFSG.StandardType

end
