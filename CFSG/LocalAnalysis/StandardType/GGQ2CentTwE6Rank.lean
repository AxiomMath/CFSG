module

public import CFSG.LocalAnalysis.StandardType.GGTwE6R5Holds
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Cover
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitTwE6Tag

public section

namespace CFSG.StandardType.GGQ2CentPort.Q2TwE6

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open

theorem card_le_of_isElemAbelian
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2) {E : Subgroup ↥(twistedE6RootGroup K σ)}
    (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 5 := by
  by_contra hle
  have hlt : 3 ^ 5 < Nat.card E := Nat.lt_of_not_ge hle
  have hfin : Finite ↥E :=
    @Finite.of_injective ↥E (ModGL TwistTag.E6.tag K)
      (finite_modGL (τ := TwistTag.E6.tag) (K := K))
      (fun x => ((x : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K))
      (fun a b h => Subtype.ext (Subtype.ext h))
  obtain ⟨k, hk⟩ :=
    @IsPGroup.exists_card_eq 3 ↥E _ Nat.fact_prime_three hfin hE.isPGroup
  have hk6 : 6 ≤ k := by
    have h53 : 3 ^ 5 < 3 ^ k := hk ▸ hlt
    exact Nat.succ_le_of_lt ((pow_lt_pow_iff_right₀ (by norm_num : 1 < 3)).1 h53)
  obtain ⟨E6', hE6'card⟩ :=
    @Sylow.exists_subgroup_card_pow_prime ↥E _ hfin 3 6 Nat.fact_prime_three
      (by rw [hk]; exact Nat.pow_dvd_pow 3 hk6)
  let E6 : Subgroup ↥(twistedE6RootGroup K σ) := E6'.map (Subgroup.subtype E)
  have hE6card : Nat.card E6 = 3 ^ 6 :=
    (Subgroup.card_map_of_injective (K := E6') (f := Subgroup.subtype E)
      (Subgroup.subtype_injective E)).trans hE6'card
  have hE6le : E6 ≤ E := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  let Y : Subgroup (MulAut ↥(twistedE6RootGroup K σ)) := E6.map MulAut.conj
  have hY : IsElemAbelian 3 Y := (hE.mono hE6le).map MulAut.conj
  have hYI : Y ≤ (RecipeExcLang.twConj K σ).range := by
    rintro _ ⟨c, -, rfl⟩
    exact ⟨⟨c, RecipeExcLang.graphFixedRootGroup_le_twInndiag σ c.2⟩,
      RecipeExcLang.twConj_of_mem_C0 σ c⟩
  have hc := CFSG.SeitzReduction.mulAut_conj_injective_of_center_eq_bot
    (exceptional_fixed_center_trivial TwistTag.E6 K σ)
  have hYc : Nat.card Y = 3 ^ 6 :=
    (Subgroup.card_map_of_injective (K := E6) (f := MulAut.conj) hc).trans hE6card
  exact (TwE6R5.not_le_inn_of_card (n := 1) (Y := Y) le_rfl
    (by rw [hK]; norm_num) σ (by intro c; rw [hσ c]; norm_num)
    (by norm_num) (by norm_num) hY hYI hYc)
    (Subgroup.map_le_range (f := MulAut.conj) E6)

theorem center_pow_three
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2) {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* ↥(twistedE6RootGroup K σ)} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) {z : L'}
    (hz : z ∈ Subgroup.center L') (hz3 : IsPGroup 3 (Subgroup.zpowers z)) : z ^ 3 = 1 := by
  obtain ⟨ε, -⟩ := TwE6DD2.exists_recipeEquiv (n := 1) (K := K) le_rfl
    (by rw [hK]; norm_num) σ (by intro c; rw [hσ c]; norm_num)
  let ψ' : L' →* TwE6Delta.RecipeR K 1 := ε.toMonoidHom.comp ψ
  have hψ' : Function.Surjective ψ' := ε.surjective.comp hψ
  have hker' : ψ'.ker ≤ Subgroup.center L' := fun x hx =>
    hker ((MulEquiv.map_eq_one_iff ε).1 (show ε (ψ x) = 1 from hx))
  obtain ⟨q, α, hq, hqk, hαs, hα⟩ :=
    TwE6DD2.exists_sc_quot (n := 1) (K := K) (L' := L') (ψ := ψ') le_rfl
      (by rw [hK]; norm_num) hψ' hker' hperf
  have hpsi1 : ψ z = 1 := by
    have hzcenter : ψ z ∈ Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := hψ y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz x]
    rw [exceptional_fixed_center_trivial TwistTag.E6 K σ] at hzcenter
    exact Subgroup.mem_bot.1 hzcenter
  let N := TableBU.twoPartOf ψ'.ker hker' (Nat.card L')
  obtain ⟨u, hu⟩ := hαs (z : L' ⧸ N)
  have hu3 : u ^ 3 = 1 := by
    have h := hα u
    rw [hu, QuotientGroup.lift_mk] at h
    change ε (ψ z) = q u at h
    rw [hpsi1, map_one] at h
    refine TwE6Nonsplit.center_pow_three 1 le_rfl (hqk ?_)
    rw [MonoidHom.mem_ker]
    exact h.symm
  have h1 : ((z ^ 3 : L') : L' ⧸ N) = 1 := by
    rw [QuotientGroup.mk_pow, ← hu, ← map_pow, hu3, map_one]
  have hord2 : orderOf (z ^ 3) ∣ 2 ^ Nat.card L' := by
    refine orderOf_dvd_of_pow_eq_one ?_
    exact (TableBU.mem_twoPartOf.1 ((QuotientGroup.eq_one_iff (z ^ 3)).1 h1)).2
  obtain ⟨k, hk⟩ := hz3.exists_card_eq
  have hcop : Nat.Coprime (orderOf (z ^ 3)) (2 ^ Nat.card L') :=
    Nat.Coprime.coprime_dvd_left
      (by rw [← hk]; exact Subgroup.orderOf_dvd_natCard _ (pow_mem (Subgroup.mem_zpowers z) 3))
      (Nat.Coprime.pow k (Nat.card L') (by norm_num : Nat.Coprime 3 2))
  exact orderOf_eq_one_iff.1 (hcop.eq_one_of_dvd hord2)

end CFSG.StandardType.GGQ2CentPort.Q2TwE6

end
