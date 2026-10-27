module

public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicExcAdj
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerRestExc
public import CFSG.LieType.Steinberg.CentralExt.FieldTwoMultiplier
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier
public import CFSG.LieType.Steinberg.CentralExt.MinusculeCentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.MinusculeCenter
public import CFSG.LieType.Steinberg.Isogeny.E6

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule

theorem ggLayerCenterCyclic_of_pow_eq_one {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (h : GGLayerCenterCyclic p R {φ | φ ∈ I ∧ φ ^ p = 1}) : GGLayerCenterCyclic p R I := by
  intro L' _ _ ψ hψ hker hperf hZ a ha1 hap hind
  obtain ⟨φ, hφI, hφ⟩ := hind
  have hφp : φ ^ p = 1 := LayerCC.eq_one_of_comp_eq hψ fun l => by
    rw [← LayerCC.map_pow_apply (fun x => (hφ x).symm) p l, hap, MulAut.one_apply]
  exact h L' ψ hψ hker hperf hZ a ha1 hap ⟨φ, ⟨hφI, hφp⟩, hφ⟩

section E6


theorem LayerCycExc.e6_minGroup_exists_section {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (E : Type) [Group E] [Finite E]
    (π : E →* e6Data_valid.minGroup K) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) : ∃ σ : e6Data_valid.minGroup K →* E, ∀ g, π (σ g) = g := by
  have := LayerCC.charP_two_of_natCard hK
  rcases n with _ | _ | _ | n
  · exfalso
    have h1 := Finite.one_lt_card (α := K)
    rw [hK, pow_zero] at h1
    exact lt_irrefl 1 h1
  · exact CFSG.LieType.Steinberg.CentralExt.FieldTwo.e6_two_exists_section (by rw [hK]; norm_num) E
      π hπ hcen
  · exact CFSG.LieType.Steinberg.CentralExt.FieldFour.e6_four_exists_section hK E π hπ hcen
  · refine CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.e6_exists_section_of_central ?_ hπ hcen
    rw [hK]
    calc 5 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (n + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem ggPSections_adjointGroup_E6 {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3 ∨ ¬ 3 ∣ 2 ^ n - 1) :
    GGPSections p (adjointGroup .E6 K) := by
  have := LayerCC.charP_two_of_natCard hK
  have := CFSG.LieType.Steinberg.CentralExt.FieldFour.finite_minGroup' (K := K) e6Data_valid
  intro E _ _ η hη hker hpk
  set ι := CFSG.LieType.Steinberg.Isogeny.e6Isogeny K with hιdef
  have hι : Function.Surjective ι := CFSG.LieType.Steinberg.Isogeny.e6Isogeny_surjective K
  let Pb : Subgroup (E × e6Data_valid.minGroup K) :=
    MonoidHom.eqLocus (η.comp (MonoidHom.fst _ _)) (ι.comp (MonoidHom.snd _ _))
  let π₂ : Pb →* e6Data_valid.minGroup K := (MonoidHom.snd _ _).comp Pb.subtype
  have hπ₂ : Function.Surjective π₂ := fun m => by
    obtain ⟨e, he⟩ := hη (ι m)
    exact ⟨⟨(e, m), he⟩, rfl⟩
  have hπ₂ker : π₂.ker ≤ Subgroup.center Pb := by
    rintro ⟨⟨e, m⟩, hx⟩ hk
    have hm : m = 1 := hk
    have he : e ∈ η.ker := by
      have hx' : η e = ι m := hx
      rw [MonoidHom.mem_ker, hx', hm, map_one]
    rw [Subgroup.mem_center_iff]
    rintro ⟨⟨e', m'⟩, -⟩
    apply Subtype.ext
    change (e' * e, m' * m) = (e * e', m * m')
    rw [hm, one_mul, mul_one, Subgroup.mem_center_iff.mp (hker he) e']
  obtain ⟨s, hs⟩ := LayerCycExc.e6_minGroup_exists_section hK Pb π₂ hπ₂ hπ₂ker
  let ρ : e6Data_valid.minGroup K →* E := (MonoidHom.fst _ _).comp (Pb.subtype.comp s)
  have hρ : ∀ m, η (ρ m) = ι m := fun m => by
    have h1 : η ((s m : E × e6Data_valid.minGroup K).1) =
        ι ((s m : E × e6Data_valid.minGroup K).2) := (s m).2
    have h2 : (s m : E × e6Data_valid.minGroup K).2 = m := hs m
    change η ((s m : E × e6Data_valid.minGroup K).1) = _
    rw [h1, h2]
  have hZ : ι.ker ≤ ρ.ker := by
    intro z hz
    have hzη : ρ z ∈ η.ker := by
      rw [MonoidHom.mem_ker, hρ]
      exact MonoidHom.mem_ker.mp hz
    have hzc : z ∈ Subgroup.center (e6Data_valid.minGroup K) := by
      rw [← CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center]
      exact hz
    have hord : orderOf (ρ z) ∣ Nat.gcd 3 (2 ^ n - 1) := by
      rw [← hK, ← (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 K).1]
      exact (orderOf_map_dvd ρ z).trans (Subgroup.orderOf_dvd_natCard _ hzc)
    obtain ⟨k, hk⟩ := hpk ⟨ρ z, hzη⟩
    have hk' : (ρ z) ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hk')
    rw [MonoidHom.mem_ker, ← orderOf_eq_one_iff, hj]
    rcases j with _ | j
    · rfl
    · exfalso
      have hpd : p ∣ Nat.gcd 3 (2 ^ n - 1) :=
        (dvd_pow_self p (Nat.succ_ne_zero j)).trans (hj ▸ hord)
      have hp3' : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
        (hpd.trans (Nat.gcd_dvd_left _ _))
      rcases hp3 with h | h
      · exact h hp3'
      · exact h (hp3' ▸ hpd.trans (Nat.gcd_dvd_right _ _))
  let σ : adjointGroup .E6 K →* E := (QuotientGroup.lift ι.ker ρ hZ).comp
    (QuotientGroup.quotientKerEquivOfSurjective ι hι).symm.toMonoidHom
  refine ⟨σ, fun g => ?_⟩
  obtain ⟨m, rfl⟩ := hι g
  have hsymm : (QuotientGroup.quotientKerEquivOfSurjective ι hι).symm (ι m) =
      (m : e6Data_valid.minGroup K ⧸ ι.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  change η (QuotientGroup.lift ι.ker ρ hZ
    ((QuotientGroup.quotientKerEquivOfSurjective ι hι).symm (ι m))) = ι m
  rw [hsymm, QuotientGroup.lift_mk, hρ]

theorem mem_inn_of_mem_recipeID_E6 {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3 ∨ ¬ 3 ∣ 2 ^ n - 1)
    {φ : MulAut (TableBExc.RecipeGroup .E6 K)} (hφ : φ ∈ TableBExc.RecipeID .E6 K)
    (hφp : φ ^ p = 1) : φ ∈ LargeEvenInnSet (TableBExc.RecipeGroup .E6 K) := by
  rcases hp3 with hp3 | h3
  · exact mem_range_conj_of_mem_recipeID_E6 hp hp3 hφ hφp
  · have hcube : ∀ s : Kˣ, ∃ u : Kˣ, u ^ 3 = s := by
      intro s
      have h1 : orderOf s ∣ 2 ^ n - 1 := by
        rw [← hK, ← Nat.card_units]
        exact orderOf_dvd_natCard s
      have hcop : Nat.Coprime 3 (orderOf s) :=
        Nat.Coprime.coprime_dvd_right h1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
      exact ⟨s ^ m, by rw [← pow_mul, mul_comm, pow_mul, hm]⟩
    exact TableBExc.idImage_subset_inn_of_top .E6 K
      (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K TableB.cartanE6_adj hcube) hφ

@[expose] def GGE6AdjLayerCycInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = 2 ^ n →
    ∀ p : ℕ, p.Prime → p ≠ 2 → (p ∣ 2 ^ n - 1 ∨ (n = 1 ∧ p = 3)) →
      (p ≠ 3 ∨ ¬ 3 ∣ 2 ^ n - 1) →
        ∀ h : adjointGroup .E6 K, GGModelLayerCyclic p (MulAut.conj h)

theorem largeEvenLabelAll_layerCenterCyclic_E6 (hE6 : GGE6AdjLayerCycInput) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .E6) (hs : LargeEvenSplit p lab) (hp3 : p ≠ 3 ∨ ¬ 3 ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGLayerCenterCyclic p R I) := by
  have hu : LargeEvenUntwisted lab.tag := by
    rw [ht]
    exact trivial
  have hsplit := LayerCycExc.dvd_or_of_largeEvenSplit_untwisted hu hs
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  dsimp only at ht hsplit hn hp3
  subst ht
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, fun hsimple hnab => ?_⟩
  have := LayerCC.charP_two_of_natCard hK
  have : Finite (adjointGroup .E6 K) := CFSG.LieType.Chevalley.generated_group_finite .E6 K
  refine ggLayerCenterCyclic_of_pow_eq_one ?_
  exact ggLayerCenterCyclic_of_mulEquiv_inn hp (TableBExc.recipeEquiv .E6 K)
    (fun φ hφ => mem_inn_of_mem_recipeID_E6 hK hp hp3 hφ.1 hφ.2)
    (LayerCycExc.commutator_eq_top_of_simple hsimple hnab) (ggPSections_adjointGroup_E6 hK hp hp3)
    (hE6 K n hn hK p hp hp2 hsplit hp3)

end E6

end CFSG.StandardType

end
