module

public import CFSG.Quasithin.Vol2.Ch11SecB36Fin1
public import CFSG.Quasithin.Vol2.Ch11SecB36K2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem false_of_VH_two (hFV : FactsVM) (hFL : FactsL2) (hG16 : ASInputs.AS_G_1_6)
    {V₁ V₂ H K : Subgroup G} (hfl : Flag36 L (fsuV T I) (VM T L I) ⊤ T V₁ V₂ n)
    (hVHel : IsElemAbelian 2 (VZ T H)) (hKN : K ≤ Subgroup.normalizer (VZ T H : Set G))
    (hKC : ¬ K ≤ Subgroup.centralizer (VZ T H : Set G)) (hHKT : K ⊔ T = H)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) {g : G}
    (hBT : conjSubgroup (VM T L I) g ≤ T)
    (hBN : conjSubgroup (VM T L I) g ≤ Subgroup.normalizer (VZ T H : Set G))
    (haS : autI hVHel (conjSubgroup (VM T L I) g) ∈ E3.aSet (2 * n) (autI hVHel H))
    (hBS : QuasithinUnique.IsSylowTwoOf (autI hVHel (conjSubgroup (VM T L I) g))
      (autI hVHel K))
    (hBcard : Nat.card ↥(autI hVHel (conjSubgroup (VM T L I) g)) = 2 ^ (2 * n))
    (hBm : E3.mQuot (conjSubgroup (VM T L I) g)
      (conjSubgroup (VM T L I) g ⊓ Subgroup.centralizer (VZ T H : Set G)) = 2 * n)
    (hVHB : VZ T H ≤ Subgroup.normalizer (conjSubgroup (VM T L I) g : Set G))
    (hGm : ∃ (F' : Type) (_ : Field F') (_ : Finite F'), Nat.card F' = 2 ^ (2 * n) ∧
      Nonempty (↥(autI hVHel K) ≃* Matrix.SpecialLinearGroup (Fin 2) F')) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn := hfl.two_le
  set W := VM T L I with hWdef
  set VH := VZ T H with hVHdef
  set B := conjSubgroup W g with hBdef
  have hVHK : VH = conjClosure (quasithinOmegaOneCenter T) K := VZ_eq_conjClosure hTK hHKT
  have hBZ : B ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := fun b hb =>
    Subgroup.mem_centralizer_iff.mpr fun z hz =>
      (Subgroup.mem_centralizer_iff.mp (E3.omegaOneCenter_le_inf_centralizer T hz).2 b
        (hBT hb)).symm
  have hgen := iSup_map_fixV_eq_top hVHel hVHK hKN hBN hBZ
  have hfix : ∀ r ∈ autI hVHel B, r ≠ 1 → fixV (Subgroup.zpowers r) = fixV (autI hVHel B) := by
    intro r hr hr1
    refine haS.2.2.2 _ (Subgroup.zpowers_le.mpr hr) ?_
    have hr2 : r ^ 2 = 1 := haS.2.2.1.2 r hr
    have hord : orderOf r = 2 := orderOf_eq_prime hr2 hr1
    have hle : Subgroup.zpowers r ≤ autI hVHel B := Subgroup.zpowers_le.mpr hr
    have h1 := Subgroup.relIndex_mul_card (H := Subgroup.zpowers r) (K := autI hVHel B)
    rw [inf_eq_left.mpr hle, Nat.card_zpowers, hord, hBcard] at h1
    have h2 : (Subgroup.zpowers r).relIndex (autI hVHel B) = 2 ^ (2 * n - 1) := by
      have e : 2 ^ (2 * n) = 2 ^ (2 * n - 1) * 2 := by
        rw [← pow_succ]
        congr 1
        omega
      rw [e] at h1
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
    unfold E3.mQuot
    rw [h2, padicValNat.prime_pow]
    omega
  obtain ⟨s, W', hW'1, hW'2, hW'3, hW'4⟩ := hG16 (IntMod VH hVHel) IntMod.sq_eq_one
    (autI hVHel K) (autI hVHel B) (2 * n) (by omega) hGm hBS hgen hfix
  have hrk := hFL.natRank (IntMod VH hVHel) IntMod.sq_eq_one (autI hVHel K) (autI hVHel B)
    (2 * n) (by omega) hGm hBS s W' hW'1 hW'2 hW'3 hW'4
  rw [E3.rkIdx_fixV_autI hVHel hBN] at hrk
  have hBW : conjSubgroup B g⁻¹ = W := E3.conjSubgroup_conj_inv W g
  have hEN : conjSubgroup VH g⁻¹ ≤ ⊤ ⊓ Subgroup.normalizer (W : Set G) := by
    refine le_inf le_top ?_
    have := E3.conjSubgroup_mono_left g⁻¹ hVHB
    rwa [E3.conjSubgroup_normalizer, hBW] at this
  have hEel : IsElemAbelian 2 (conjSubgroup VH g⁻¹) := E3.isElemAbelian_conjSubgroup hVHel g⁻¹
  have hEm : E3.mQuot (conjSubgroup VH g⁻¹)
      (conjSubgroup VH g⁻¹ ⊓ Subgroup.centralizer (W : Set G)) = s * (2 * n) := by
    have := E3.mQuot_conjSubgroup VH (VH ⊓ Subgroup.centralizer (B : Set G)) g⁻¹
    rw [conjSubgroup_inf_centralizer, hBW, hrk] at this
    exact this
  have hrank := hFV.rank G L (fsuV T I) W ⊤ T V₁ V₂ n hfl _ hEN hEel
  rw [hEm] at hrank
  have hs1 : s = 1 := by
    by_contra hs1
    rcases Nat.lt_or_ge s 1 with h | h
    · have hs0 : s = 0 := by omega
      subst hs0
      apply hKC
      simp only [iSup_of_empty, sup_bot_eq] at hW'3
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv' : (IntMod.mk hVHel ⟨v, hv⟩ : IntMod VH hVHel) ∈ fixV (autI hVHel K) := by
        rw [hW'3]
        exact Subgroup.mem_top _
      have := (mem_fixV_autI hVHel hKN _).mp hv'
      exact (Subgroup.mem_centralizer_iff.mp this k hk).symm
    · have h2 : 2 ≤ s := by omega
      have : 2 * (2 * n) ≤ s * (2 * n) := Nat.mul_le_mul_right _ h2
      omega
  subst hs1
  have htop : W' 0 = ⊤ := by
    rw [iSup_unique] at hW'3
    rw [← hW'3]
    exact (sup_eq_right.mpr (hW'1 _)).symm
  have hnat : BinaryNaturalSL (autI hVHel K) ⊤ (fixV (autI hVHel K)) 2 (2 * n) := by
    have := hW'4 0
    rwa [htop] at this
  have hWE : E3.mQuot W (W ⊓ Subgroup.centralizer (conjSubgroup VH g⁻¹ : Set G)) = 2 * n := by
    have := E3.mQuot_conjSubgroup B (B ⊓ Subgroup.centralizer (VH : Set G)) g⁻¹
    rw [conjSubgroup_inf_centralizer, hBW, hBm] at this
    exact this
  obtain ⟨hcm, a, haW, b, hbW, hab, habE, haE⟩ := hFV.r2Pair G L (fsuV T I) W ⊤ T V₁ V₂ n hfl
    _ hEN hEel (by rw [hEm, one_mul]) hWE
  exact false_of_pair hFL hn hVHel hBN hnat hBS hGm hcm haW hbW hab habE haE

end CFSG.Quasithin.Vol2.Ch11.SecB
