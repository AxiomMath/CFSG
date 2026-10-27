module

public import CFSG.Quasithin.EmptyFaithful.S153E58C
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporCrit

public section

namespace CFSG.Quasithin

open scoped commutatorElement

namespace S15223P4.Kc

theorem eq_bot_of_perfect_of_solvable {Γ : Type*} [Group Γ] {R : Subgroup Γ} (hR : ⁅R, R⁆ = R)
    [Group.IsSolvable R] : R = ⊥ := by
  have htop : commutator R = ⊤ := by
    apply Subgroup.map_injective R.subtype_injective
    rw [Subgroup.map_subtype_commutator, hR, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hder : ∀ n, derivedSeries R n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih, ← commutator_def, htop]
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := R)
  have h1 : (⊤ : Subgroup R) = ⊥ := by rw [← hder n]; exact hn
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hx⟩ : R) ∈ (⊥ : Subgroup R) := h1 ▸ Subgroup.mem_top _
  have h2 : (⟨x, hx⟩ : R) = 1 := this
  exact congrArg Subtype.val h2

theorem eq_bot_of_perfect_stab {Q : Type} [Group Q]
    (ψ : Q ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))) {M' : Subgroup Q}
    (h8 : 8 ∣ Nat.card M') (h3 : 3 ∣ Nat.card M') (hM : M' ≠ ⊤) {R : Subgroup (MulAut Q)}
    (hR : ⁅R, R⁆ = R) (hstab : ∀ α ∈ R, M'.map α.toMonoidHom = M') : R = ⊥ := by
  have hfin : Finite Q := Finite.of_equiv _ ψ.symm.toEquiv
  have hQ : Nat.card Q = 168 := by
    rw [Nat.card_congr ψ.toEquiv]
    exact S153E58.card_statedSL_three_two
  have hΓ : Nat.card (MulAut Q) = 336 := by
    rw [Nat.card_congr (MulAut.congr ψ).toEquiv]
    exact S153E58.card_mulAut_statedSL_three_two
  have hsimple : IsSimpleGroup Q := by
    have := S153E58.isSimpleGroup_statedSL_three_two
    exact ψ.isSimpleGroup
  have hcent : ∀ z : Q, (∀ t, z * t = t * z) → z = 1 := fun z hz =>
    ψ.injective (by
      rw [map_one]
      refine S153E58.statedSL_center fun t => ?_
      obtain ⟨t', rfl⟩ := ψ.surjective t
      rw [← map_mul, ← map_mul, hz t'])
  have hinj : Function.Injective (MulAut.conj : Q →* MulAut Q) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    have : ∀ g, g * z = z * g := fun g => by
      have h := DFunLike.congr_fun hz g
      rw [MulAut.conj_apply, MulAut.one_apply] at h
      calc g * z = (z * g * z⁻¹) * z := by rw [h]
        _ = z * g := by group
    exact Subgroup.mem_bot.mpr (hcent z fun t => (this t).symm)
  set Inn : Subgroup (MulAut Q) := (MulAut.conj : Q →* MulAut Q).range with hInnDef
  have hInn : Nat.card Inn = 168 := by
    rw [← hQ]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hidx : Inn.index = 2 := by
    have := Subgroup.card_mul_index Inn
    rw [hInn, hΓ] at this
    omega
  have : Inn.Normal := Subgroup.normal_of_index_eq_two hidx
  have hcomm : ∀ a b : MulAut Q, ⁅a, b⁆ ∈ Inn := by
    have : Fact (Nat.Prime (Nat.card (MulAut Q ⧸ Inn))) := ⟨by
      rw [← Subgroup.index_eq_card, hidx]
      exact Nat.prime_two⟩
    have : IsCyclic (MulAut Q ⧸ Inn) := isCyclic_of_prime_card rfl
    intro a b
    have h1 : (QuotientGroup.mk' Inn) ⁅a, b⁆ =
        ⁅(QuotientGroup.mk' Inn) a, (QuotientGroup.mk' Inn) b⁆ :=
      map_commutatorElement _ _ _
    have h2 : (QuotientGroup.mk' Inn) ⁅a, b⁆ = 1 := by
      rw [h1]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        ((@IsCyclic.commGroup (MulAut Q ⧸ Inn) _ this).mul_comm _ _)
    exact (QuotientGroup.eq_one_iff _).mp h2
  have hRInn : R ≤ Inn := by
    have hc : ⁅R, R⁆ ≤ Inn := Subgroup.commutator_le.mpr fun a _ b _ => hcomm a b
    rwa [hR] at hc
  set Ñ : Subgroup Q := Subgroup.normalizer (M' : Set Q) with hÑ
  have hN24 : Nat.card Ñ = 24 := by
    have h8N : 8 ∣ Nat.card Ñ := h8.trans (Subgroup.card_dvd_of_le Subgroup.le_normalizer)
    have h3N : 3 ∣ Nat.card Ñ := h3.trans (Subgroup.card_dvd_of_le Subgroup.le_normalizer)
    have h24 : 24 ∣ Nat.card Ñ :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 8 3) h8N h3N
    have hdvd : Nat.card Ñ ∣ 168 := hQ ▸ Subgroup.card_subgroup_dvd_card Ñ
    obtain ⟨k, hk⟩ := h24
    have hle : Nat.card Ñ ≤ 168 := Nat.le_of_dvd (by norm_num) hdvd
    have hk7 : k ≤ 7 := by omega
    rw [hk] at hdvd ⊢
    interval_cases k <;> first | omega | skip
    · exfalso
      have hÑtop : Ñ = ⊤ := Subgroup.eq_top_of_card_eq Ñ (by rw [hQ]; omega)
      have : M'.Normal := Subgroup.normalizer_eq_top_iff.mp hÑtop
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M' with h | h
      · rw [h] at h3
        simp at h3
      · exact hM h
  have hNsolv : Group.IsSolvable ↥Ñ :=
    E6.Spor.isSolvable_of_card_two_pow_mul_three_pow (a := 3) (b := 1) (by rw [hN24]; norm_num)
  have hS : Group.IsSolvable ↥(Ñ.map (MulAut.conj : Q →* MulAut Q)) :=
    Group.isSolvable_of_surjective (f := (MulAut.conj : Q →* MulAut Q).subgroupMap Ñ)
      (MonoidHom.subgroupMap_surjective _ _)
  have hRS : R ≤ Ñ.map (MulAut.conj : Q →* MulAut Q) := by
    intro α hα
    obtain ⟨q, hq⟩ := hRInn hα
    refine ⟨q, ?_, hq⟩
    show q ∈ Subgroup.normalizer (M' : Set Q)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have := hstab α hα
    rwa [← hq] at this
  have : Group.IsSolvable ↥R :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hRS)
      (Subgroup.inclusion_injective hRS)
  exact eq_bot_of_perfect_of_solvable hR

end S15223P4.Kc

end CFSG.Quasithin
