module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetRowTw
public import CFSG.LocalAnalysis.StandardType.GGKGAF4Aut
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLine
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicExcSix
public import Certificates.Certificate1002
public import Certificates.Certificate1003

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule

theorem ggR4RowFact_F4
  {f : ℕ} :
    LargeEvenLabelAll ⟨.F4, 0, f⟩ fun R _ I _ => GGR4RowFact R I := by
  have h1 : LargeEvenLabelAll ⟨.F4, 0, f⟩ fun R _ I _ =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        GGHasLabel ⟨.F4, 0, f⟩ R ∧ ∀ φ ∈ I, ∃ r : R, φ = MulAut.conj r :=
    KGA.ggF4_basics_label (f := f)
  have hinn : LargeEvenLabelAll ⟨.F4, 0, f⟩ fun R _ I _ =>
      ∀ φ ∈ I, ∃ r : R, φ = MulAut.conj r :=
    h1.mono fun R _ I _ h => h.2.2.2
  have hcen : LargeEvenLabelAll ⟨.F4, 0, f⟩ fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ g ∈ Subgroup.center L', Nat.Coprime 3 (orderOf g) := by
    intro Q hQ
    obtain ⟨K, hField, hFinite, hK, hq⟩ := hQ
    letI : Field K := hField
    letI : Finite K := hFinite
    haveI : CharP K 2 := charP_two_of_card hK
    refine ⟨K, hField, hFinite, hK, hq, ?_⟩
    intro L' _ _ ψ hψ hker hperf g hg
    have hcp := ExcSplitL.ggCenterPrime_recipe_F4 (K := K) Nat.prime_three (by decide)
    have hnd : ¬ 3 ∣ Nat.card (Subgroup.center L') := hcp L' ψ hψ hker hperf
    have hdvd : orderOf g ∣ Nat.card (Subgroup.center L') := by
      have h2 : orderOf (⟨g, hg⟩ : Subgroup.center L') ∣ Nat.card (Subgroup.center L') :=
        orderOf_dvd_natCard _
      rwa [Subgroup.orderOf_mk] at h2
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h3d => hnd (h3d.trans hdvd)
  exact (largeEvenLabelAll_and hinn hcen).mono fun R _ I _ h => h

private theorem rwf_odd_of_three_dvd_two_pow_add_one {f : ℕ} (h : 3 ∣ 2 ^ f + 1) :
    Odd f := by
  rcases Nat.even_or_odd f with he | ho
  · exfalso
    obtain ⟨k, hk⟩ := he
    subst hk
    have h2 : 2 ^ (k + k) = 4 ^ k := by
      rw [show k + k = 2 * k by ring, pow_mul]
      norm_num
    have h4 : 4 ^ k % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    have hmod : (2 ^ (k + k) + 1) % 3 = 2 := by
      rw [h2, Nat.add_mod, h4]
    have h0 := Nat.dvd_iff_mod_eq_zero.mp h
    omega
  · exact ho

theorem ggR4RowFact_E6
  {f : ℕ} (h3 : 3 ∣ 2 ^ f + 1) :
    LargeEvenLabelAll ⟨.E6, 0, f⟩ fun R _ I _ => GGR4RowFact R I := by
  have hodd : Odd f := rwf_odd_of_three_dvd_two_pow_add_one h3
  intro Q hQ
  obtain ⟨K, hField, hFinite, hK, hq⟩ := hQ
  letI : Field K := hField
  letI : Finite K := hFinite
  refine ⟨K, hField, hFinite, hK, hq, ?_⟩
  refine ⟨?_, ?_⟩
  · intro φ hφ
    have hcop : (Nat.card Kˣ).Coprime 3 := by
      rw [Nat.card_units, hK]
      exact coprime_two_pow_sub_one_three hodd
    have hmem : φ ∈ LargeEvenInnSet (TableBExc.RecipeGroup .E6 K) :=
      chevIDImage_subset_inn_of_top (τ := .E6)
        (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K TableB.cartanE6_adj fun s =>
          ⟨(powCoprime hcop).symm s, by rw [← powCoprime_apply hcop, Equiv.apply_symm_apply]⟩) hφ
    obtain ⟨r, hr⟩ := hmem
    exact ⟨r, hr.symm⟩
  · intro L' _ _ ψ hψ hker hperf g hg
    set fiso := CFSG.LieType.Steinberg.Isogeny.e6Isogeny K with hfiso
    set qmap : e6Data_valid.minGroup K →* TableBExc.RecipeGroup .E6 K :=
      (TableBExc.recipeEquiv .E6 K).symm.toMonoidHom.comp fiso
    have hqsurj : Function.Surjective qmap := (TableBExc.recipeEquiv .E6 K).symm.surjective.comp
      (CFSG.LieType.Steinberg.Isogeny.e6Isogeny_surjective K)
    have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* e6Data_valid.minGroup K),
        Function.Surjective π → π.ker ≤ Subgroup.center E →
          ∃ s : e6Data_valid.minGroup K →* E, ∀ h, π (s h) = h :=
      fun E _ _ π hπ hcen => LayerCycExc.e6_minGroup_exists_section hK E π hπ hcen
    have hdvd := E6ThreeKernel.card_ker_dvd_of_split hqsurj hsplit hψ hker hperf
    have hqk : qmap.ker ≤ Subgroup.center (e6Data_valid.minGroup K) := by
      intro z hz
      have hz' : z ∈ fiso.ker := by
        rw [MonoidHom.mem_ker] at hz ⊢
        have h2 : (TableBExc.recipeEquiv .E6 K).symm (fiso z) = 1 := hz
        rwa [MulEquiv.map_eq_one_iff] at h2
      rwa [hfiso, CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center] at hz'
    have h1 : Nat.card ψ.ker ∣ 1 := by
      have hcard : Nat.card (Subgroup.center (e6Data_valid.minGroup K)) =
          Nat.gcd 3 (Nat.card K - 1) :=
        (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 K).1
      have hcop : Nat.gcd 3 (2 ^ f - 1) = 1 := by
        rw [Nat.gcd_comm]
        exact coprime_two_pow_sub_one_three hodd
      refine hdvd.trans ((Subgroup.card_dvd_of_le hqk).trans ?_)
      rw [hcard, hK, hcop]
    have hker1 : Nat.card ψ.ker = 1 := Nat.dvd_one.mp h1
    have hcenter_le : Subgroup.center L' ≤ ψ.ker := by
      intro z hz
      rw [MonoidHom.mem_ker]
      have hzR : ψ z ∈ Subgroup.center (LargeEvenCenterQuot
          (LargeEvenChevH (LargeEvenCartanE 6) K false)) := by
        rw [Subgroup.mem_center_iff]
        intro r
        obtain ⟨x, rfl⟩ := hψ r
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
      have hZbot : Subgroup.center (LargeEvenCenterQuot
          (LargeEvenChevH (LargeEvenCartanE 6) K false)) = ⊥ :=
        TableBExc.center_recipeGroup_eq_bot .E6 K
      rw [hZbot, Subgroup.mem_bot] at hzR
      exact hzR
    have hgker : g ∈ ψ.ker := hcenter_le hg
    have hord : orderOf g ∣ Nat.card ψ.ker := by
      have h2 : orderOf (⟨g, hgker⟩ : ψ.ker) ∣ Nat.card ψ.ker := orderOf_dvd_natCard _
      rwa [Subgroup.orderOf_mk] at h2
    rw [hker1, Nat.dvd_one] at hord
    rw [hord]
    exact Nat.coprime_one_right 3

theorem ggR4SurvivorRow_holds :
    GGR4SurvivorRow := by
  intro lab hlab hs
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  rcases hs with h | ⟨h, h3⟩ | ⟨h, h3⟩
  · dsimp only at h
    subst h
    have hl : l = 0 := hlab.2
    subst hl
    exact ggR4RowFact_F4
  · dsimp only at h h3
    subst h
    have hl : l = 0 := hlab.2
    subst hl
    exact ggR4RowFact_E6 h3
  · dsimp only at h h3
    subst h
    have hl : l = 0 := hlab.2
    subst hl
    exact ggR4RowFact_twE6 hn h3

end CFSG.StandardType

end
