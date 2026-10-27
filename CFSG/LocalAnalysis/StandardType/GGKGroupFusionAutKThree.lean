module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAutKAssembly
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InnerAction
import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicThreeFamilies

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.OutStructure
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.TauCetiBridge CFSG.GorensteinWalter
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

theorem ggOutPNice_PSL_two_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X]
    {ℓ f : ℕ} (hℓ2 : ℓ ≠ 2) (h : StatedClassicalModel X .PSL 2 ℓ f) : OutPNice p X :=
  CFSG.LocalAnalysis.RankThreeTheoremC.outPNice_PSL_two_odd_of_ne_two hp hp2 hℓ2 h

theorem ggLieOutRankTwoAt_A_one (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) : GGLieOutRankTwoAt ⟨.A 1 q, hv⟩ := by
  refine ggLieOutRankTwoAt_of_char (TauCeti.LieTypeIndex.characteristic_A 1 q) fun hp2 => ?_
  have hm := ggStatedClassicalModel_of_lieModel (Or.inl rfl)
    (CFSG.Models.lieModel_A (G := (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group) 1 q hv
      (MulEquiv.refl _))
  exact (ggOutPNice_PSL_two_odd q.prime_p hp2 hp2 hm).toChain

theorem ggMem_of_mem_sup_of_coprime {Γ : Type*} [Group Γ] {I Δ : Subgroup Γ} [I.Normal]
    {n m : ℕ} (hnm : Nat.Coprime n m) (hn : ∀ a : ↥(I ⊔ Δ) ⧸ I.subgroupOf (I ⊔ Δ), a ^ n = 1)
    (hm : ∀ d ∈ Δ, d ^ m = 1) {δ : Γ} (hδ : δ ∈ I ⊔ Δ) : δ ∈ I := by
  have hδ' : δ ∈ (I : Set Γ) * (Δ : Set Γ) := by rw [← Subgroup.normal_mul]; exact hδ
  obtain ⟨i, hi, d, hd, rfl⟩ := hδ'
  have hiS : i ∈ I ⊔ Δ := Subgroup.mem_sup_left hi
  have hdS : d ∈ I ⊔ Δ := Subgroup.mem_sup_right hd
  set x : ↥(I ⊔ Δ) ⧸ I.subgroupOf (I ⊔ Δ) := QuotientGroup.mk ⟨i * d, hδ⟩ with hx
  have hxd : x = QuotientGroup.mk ⟨d, hdS⟩ := by
    have h1 : (⟨i * d, hδ⟩ : ↥(I ⊔ Δ)) = ⟨i, hiS⟩ * ⟨d, hdS⟩ := rfl
    have h2 : (QuotientGroup.mk ⟨i, hiS⟩ : ↥(I ⊔ Δ) ⧸ I.subgroupOf (I ⊔ Δ)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hi)
    rw [hx, h1, QuotientGroup.mk_mul, h2, one_mul]
  have hxm : x ^ m = 1 := by
    rw [hxd, ← QuotientGroup.mk_pow]
    have h3 : (⟨d, hdS⟩ : ↥(I ⊔ Δ)) ^ m = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, hm d hd]
      rfl)
    rw [h3, QuotientGroup.mk_one]
  have hx1 : x = 1 := by
    have h4 : orderOf x = 1 :=
      Nat.eq_one_of_dvd_coprimes hnm (orderOf_dvd_of_pow_eq_one (hn x))
        (orderOf_dvd_of_pow_eq_one hxm)
    exact orderOf_eq_one_iff.mp h4
  have h5 := (QuotientGroup.eq_one_iff (⟨i * d, hδ⟩ : ↥(I ⊔ Δ))).mp hx1
  exact Subgroup.mem_subgroupOf.mp h5

section ExceptionalOut

theorem ggOutPNice_E6_three {f : ℕ} {X : Type} [Group X]
    (h : ChevalleyExceptionalModel X .E6 3 f) : OutPNice 3 X := by
  obtain ⟨⟨-, hf1, -⟩, hm⟩ := h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hm
  obtain ⟨Φ, -, hkerΦ, hdvd⟩ := exists_outer_hom_E (K := K) (τ := .E6) (Or.inl rfl)
  have hring := card_ringAut_and_isCyclic Nat.prime_three K hK
  have : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hring.1]; omega)
  have : IsCyclic (RingAut K) := hring.2
  have hdet : Tag.E6.cartan.det.natAbs = 3 := by rw [det_cartan_E6]; rfl
  have hcop : ¬ 3 ∣ Nat.card Φ.ker := by
    intro h3
    have h1 : Nat.card Φ.ker ∣ Nat.card (Fin Tag.E6.rank → Kˣ) := by
      rw [hkerΦ]
      exact Subgroup.card_range_dvd _
    rw [Nat.card_fun, Nat.card_units, hK] at h1
    exact ggNot_prime_dvd_pow_sub_one Nat.prime_three hf1
      (Nat.prime_three.dvd_of_dvd_pow (h3.trans h1))
  have hfin : Finite Φ.ker := Nat.finite_of_card_ne_zero fun h0 => by
    rw [h0, hdet] at hdvd
    exact absurd (Nat.eq_zero_of_zero_dvd hdvd) (by norm_num)
  let Θ := Φ.comp (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
    (adjointGroup .E6 K)))
  refine OutPNice.of_mulEquiv e (outPNice_of_hom Θ ?_ ?_ ?_ ?_)
  · intro x y
    exact Prod.ext (ringAut_comm K _ _) (mul_comm _ _)
  · intro δ hδ
    have h1 : (QuotientGroup.mk δ : CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (adjointGroup .E6 K)) = 1 := (QuotientGroup.eq_one_iff _).mpr hδ
    show Φ (QuotientGroup.mk δ) = 1
    rw [h1, map_one]
  · intro δ hδ k hk
    have hx : (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (adjointGroup .E6 K)) δ) ∈ Φ.ker := hδ
    set x' : Φ.ker := ⟨_, hx⟩ with hx'
    have hxk : x' ^ (3 ^ k) = 1 := by
      apply Subtype.ext
      show (QuotientGroup.mk' _ δ) ^ (3 ^ k) = 1
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr hk
    have hcop' : Nat.Coprime (3 ^ k) (Nat.card Φ.ker) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hcop)
    have hx1 : orderOf x' = 1 := Nat.eq_one_of_dvd_coprimes hcop'
      (orderOf_dvd_of_pow_eq_one hxk) (orderOf_dvd_natCard x')
    have h1 : x' = 1 := orderOf_eq_one_iff.mp hx1
    have h2 : (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (adjointGroup .E6 K)) δ) = 1 := congrArg Subtype.val h1
    exact (QuotientGroup.eq_one_iff _).mp h2
  · have he : exactE Tag.E6 = 2 := rfl
    refine pChain_prod (pChain_of_isCyclic Nat.prime_three)
      (multiplicative_zmod_pElement Nat.prime_three ?_)
    rw [he]
    norm_num

theorem ggOutPNice_twistedE6_three {f : ℕ} {X : Type} [Group X]
    (h : ChevalleyExceptionalModel X .twistedE6 3 f) : OutPNice 3 X := by
  obtain ⟨⟨-, hf1, -⟩, hm⟩ := h
  have hm' : TwistedChevalleyModel X .E6 (3 ^ f) := hm
  obtain ⟨K, _, _, hcard, σ, hσ, ⟨e⟩⟩ := hm'
  obtain ⟨σ', hσ', -⟩ := finite_graph_field_parameter_fields .E6 Nat.prime_three hf1 K hcard
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ', hσ]
  subst hσσ'
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -, hcube, -⟩, -, -, -, ⟨E⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_three hf1 K hcard σ'
      hσ'
  have hK2 : Nat.card K = 3 ^ (f * 2) := by rw [hcard, ← pow_mul]; rfl
  have hring := card_ringAut_and_isCyclic Nat.prime_three K hK2
  have : Finite (RingAut K) :=
    Nat.finite_of_card_ne_zero (by rw [hring.1]; omega)
  have : IsCyclic (RingAut K) := hring.2
  have hunit : ∀ (L : Subfield K) (x : Lˣ), x ^ Nat.card Kˣ = 1 := by
    intro L x
    apply Units.map_injective (f := L.subtype.toMonoidHom) fun _ _ h => Subtype.ext h
    rw [map_pow, map_one]
    exact pow_card_eq_one'
  have hΔ : ∀ d ∈ twistedE6Diag K σ', d ^ Nat.card Kˣ = 1 := by
    rintro _ ⟨u, rfl⟩
    rw [← map_pow]
    have hu : u ^ Nat.card Kˣ = 1 :=
      funext fun a => by rw [Pi.pow_apply, Pi.one_apply]; exact hunit _ (u a)
    rw [hu, map_one]
  have hcop : Nat.Coprime 3 (Nat.card Kˣ) := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr ?_
    rw [Nat.card_units, hK2]
    exact ggNot_prime_dvd_pow_sub_one Nat.prime_three (by omega)
  have hker' : Θ.ker = twistedE6Inn K σ' := by
    rw [hker]
    exact le_antisymm (fun δ hδ => ggMem_of_mem_sup_of_coprime hcop hcube hΔ hδ) le_sup_left
  exact OutPNice.of_mulEquiv (e.trans E) (outPNice_of_hom_cyclic Nat.prime_three Θ hker')

end ExceptionalOut

section ExceptionalAt

theorem ggLieOutRankTwoAt_E6_three (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E6 q).Valid) (hq3 : q.p = 3) : GGLieOutRankTwoAt ⟨.E6 q, hv⟩ := by
  refine ggLieOutRankTwoAt_of_char (TauCeti.LieTypeIndex.characteristic_E6 q) fun hp2 => ?_
  have hm : ChevalleyExceptionalModel (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group .E6 q.p
      q.exponent := ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
    untwistedModel_of_bridge chevalleyBridges.e6 q hv hp2 (MulEquiv.refl _)⟩
  rw [hq3] at hm ⊢
  exact (ggOutPNice_E6_three hm).toChain

theorem ggLieOutRankTwoAt_twistedE6_three (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) (hq3 : q.p = 3) :
    GGLieOutRankTwoAt ⟨.twistedE6 q, hv⟩ := by
  refine ggLieOutRankTwoAt_of_char (TauCeti.LieTypeIndex.characteristic_twistedE6 q)
    fun hp2 => ?_
  have hm : ChevalleyExceptionalModel (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group
      .twistedE6 q.p q.exponent := ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
    twistedModel_of_bridge chevalleyBridges.twistedE6 q hv hp2 (by decide) (MulEquiv.refl _)⟩
  rw [hq3] at hm ⊢
  exact (ggOutPNice_twistedE6_three hm).toChain

end ExceptionalAt

end CFSG.StandardType
