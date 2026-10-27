module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1Defs
public import CFSG.RankThree.PartTwo.Sec16.Item166StepsProofNoSz
public import CFSG.RankThree.PartTwo.KFacts.KS14Sz

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148K

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open scoped commutatorElement

theorem exists_maximal_normal_ne_top (Q : Type) [Group Q] [Finite Q] (hne : Nontrivial Q) :
    ∃ N : Subgroup Q, N.Normal ∧ N ≠ ⊤ ∧ ∀ K : Subgroup Q, K.Normal → N ≤ K → K = N ∨ K = ⊤ := by
  haveI : Finite (Subgroup Q) :=
    Finite.of_injective (fun K : Subgroup Q => (K : Set Q)) SetLike.coe_injective
  haveI : Nontrivial (Subgroup Q) := Subgroup.nontrivial_iff.mpr hne
  let 𝓝 : Set (Subgroup Q) := {K | K.Normal ∧ K ≠ ⊤}
  have hbot : (⊥ : Subgroup Q) ∈ 𝓝 := ⟨inferInstance, bot_ne_top⟩
  obtain ⟨N, hNmem, hNmax⟩ := Set.Finite.exists_maximal (Set.toFinite 𝓝) ⟨⊥, hbot⟩
  obtain ⟨hNn, hNt⟩ : N.Normal ∧ N ≠ ⊤ := hNmem
  refine ⟨N, hNn, hNt, fun K hKn hNK => ?_⟩
  by_cases hKt : K = ⊤
  · exact Or.inr hKt
  · have hK𝓝 : K ∈ 𝓝 := ⟨hKn, hKt⟩
    exact Or.inl (le_antisymm (hNmax hK𝓝 hNK) hNK)

theorem exists_suzuki_section_of_isPerfect
    {Q : Type} [Group Q] [Finite Q] (hK : IsKGroup Q) (hp : Group.IsPerfect Q)
    (h3 : ¬ 3 ∣ Nat.card Q) (hne : Nontrivial Q) :
    ∃ (N : Subgroup Q) (_ : N.Normal) (f : ℕ), CFSG.Blueprint.SuzukiModel (Q ⧸ N) 2 f := by
  obtain ⟨N, hNn, hNt, hmax⟩ := exists_maximal_normal_ne_top Q hne
  haveI := hNn
  have hnab : ∃ a b : Q ⧸ N, a * b ≠ b * a := by
    by_contra hcon
    have hcomm : ∀ a b : Q ⧸ N, a * b = b * a := fun a b => by
      by_contra hab
      exact hcon ⟨a, b, hab⟩
    apply hNt
    have hle : commutator Q ≤ N := by
      refine Subgroup.commutator_le.mpr fun g _ h _ => ?_
      have key : QuotientGroup.mk' N ⁅g, h⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact hcomm _ _
      exact (QuotientGroup.eq_one_iff ⁅g, h⁆).mp key
    have htop : (⊤ : Subgroup Q) ≤ N := by
      rw [← hp.commutator_eq_top]
      exact hle
    exact eq_top_iff.mpr htop
  have hnt : Nontrivial (Q ⧸ N) := by
    obtain ⟨a, b, hab⟩ := hnab
    exact nontrivial_of_ne _ _ hab
  have hsimp : IsSimpleGroup (Q ⧸ N) :=
    { toNontrivial := hnt
      eq_bot_or_eq_top_of_normal := fun K hK' => by
        have hcomap : (K.comap (QuotientGroup.mk' N)).map (QuotientGroup.mk' N) = K :=
          Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) K
        have hNK : N ≤ K.comap (QuotientGroup.mk' N) := by
          intro x hx
          rw [Subgroup.mem_comap,
            show QuotientGroup.mk' N x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
          exact K.one_mem
        rcases hmax (K.comap (QuotientGroup.mk' N)) (Subgroup.Normal.comap hK' _) hNK with
          h | h
        · left
          rw [← hcomap, h, QuotientGroup.map_mk'_self]
        · right
          rw [← hcomap, h, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] }
  have hφ : Function.Surjective ((QuotientGroup.mk' N).comp (⊤ : Subgroup Q).subtype) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    exact ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩
  have hcat := hK.inCatalog_of_surjective ⊤ _ hφ
  have h3' : ¬ 3 ∣ Nat.card (Q ⧸ N) := fun h => h3 (h.trans (Subgroup.card_quotient_dvd_card N))
  obtain ⟨f, hf⟩ :=
    CFSG.RankThree.PartTwo.KFacts.KS14.suzukiModel_of_inCatalog_of_not_three_dvd (Q ⧸ N) hnab hcat
      h3'
  exact ⟨N, hNn, f, hf⟩

theorem row143_of_noSzSection
    {S : Type} [Group S] [Finite S]
    (h : CFSG.RankThree.PartTwo.Sec16.Steps166.NoSzSection (MulAut S)) : Row143 S := by
  unfold Row143
  intro β _ _ D _ _ _ P hPK _ _ hPperf hP3
  by_contra hP
  haveI : Finite (MulAut S) :=
    Finite.of_injective (fun φ : MulAut S => (φ : S → S)) DFunLike.coe_injective
  haveI : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP
  obtain ⟨N, hN, f, hf⟩ := exists_suzuki_section_of_isPerfect hPK hPperf hP3 inferInstance
  exact h P N 2 f hf

theorem mulAut_conj_comm_apply {S : Type} [Group S] (β : MulAut S) (y : S) :
    MulAut.conj (β y) * β = β * MulAut.conj y := by
  ext x
  simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, mul_assoc]

theorem conj_injective_of_isSimpleGroup {S : Type} [Group S] (hS : IsSimpleGroup S)
    (hnc : ∃ a b : S, a * b ≠ b * a) : Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h1 : g * x * g⁻¹ = x := by
      have := congrArg (fun φ : MulAut S => φ x) hg
      simpa [MulAut.conj_apply] using this
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center S) with h | h
  · rw [h] at hc
    exact Subgroup.mem_bot.mp hc
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have ha : a ∈ Subgroup.center S := by
      rw [h]
      exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

theorem isSubnormal_subgroupOf_of_normalizes {S : Type} [Group S] {A D Y : Subgroup S}
    (hYD : Y ≤ D) (hDn : (D.subgroupOf A).Normal)
    (hYn : ∀ d ∈ D, ∀ y ∈ Y, d * y * d⁻¹ ∈ Y) : (Y.subgroupOf A).IsSubnormal := by
  have hN : ((Y.subgroupOf A).subgroupOf (D.subgroupOf A)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hn ⊢
    have hg : ((g : A) : S) ∈ D := Subgroup.mem_subgroupOf.mp g.2
    simpa using hYn _ hg _ hn
  exact Subgroup.IsSubnormal.trans (Subgroup.subgroupOf_mono A hYD) hN.isSubnormal
    hDn.isSubnormal

theorem row143_of_inner {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnc : ∃ a b : S, a * b ≠ b * a)
    (hOut : ∀ P : Subgroup (MulAut S), IsKGroup ↥P → Group.IsPerfect ↥P → ¬ 3 ∣ Nat.card ↥P →
      P ≤ (MulAut.conj : S →* MulAut S).range)
    (hNoSz : ∀ β : MulAut S, β ^ 3 = 1 → ∀ Y : Subgroup S, Y ≤ Sec4.autFix β →
      (Y.subgroupOf (Sec4.autFix β)).IsSubnormal → Group.IsPerfect ↥Y → ¬ 3 ∣ Nat.card ↥Y →
      Y = ⊥) :
    Row143 S := by
  unfold Row143
  intro β hβ3 _ D hDfix hDnorm hDpow P hPK hPcent hPnorm hPperf hP3
  have hPle : P ≤ (MulAut.conj : S →* MulAut S).range := hOut P hPK hPperf hP3
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) :=
    conj_injective_of_isSimpleGroup hS hnc
  set Y : Subgroup S := P.comap (MulAut.conj : S →* MulAut S) with hYdef
  have hYmap : Y.map (MulAut.conj : S →* MulAut S) = P := by
    rw [hYdef, Subgroup.map_comap_eq, inf_eq_right.mpr hPle]
  let e : Y ≃* P :=
    (Y.equivMapOfInjective (MulAut.conj : S →* MulAut S) hinj).trans (MulEquiv.subgroupCongr hYmap)
  have hcard : Nat.card Y = Nat.card P := Nat.card_congr e.toEquiv
  have hY3 : ¬ 3 ∣ Nat.card Y := by
    rw [hcard]
    exact hP3
  have hYperf : Group.IsPerfect Y :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hYfix : Y ≤ Sec4.autFix β := by
    intro y hy
    have hyP : MulAut.conj y ∈ P := hy
    have hcent : MulAut.conj y * β = β * MulAut.conj y :=
      Subgroup.mem_centralizer_singleton_iff.mp (hPcent hyP)
    have h2 : MulAut.conj (β y) * β = MulAut.conj y * β :=
      (mulAut_conj_comm_apply β y).trans hcent.symm
    have h3 : MulAut.conj (β y) = MulAut.conj y := mul_right_cancel h2
    exact Sec4.mem_autFix.mpr (hinj h3)
  have hYnorm : ∀ d ∈ D, ∀ y ∈ Y, d * y * d⁻¹ ∈ Y := by
    intro d hd y hy
    have hyP : MulAut.conj y ∈ P := hy
    have hn := (Subgroup.mem_set_normalizer_iff.mp (hPnorm d hd) (MulAut.conj y)).mp hyP
    show MulAut.conj (d * y * d⁻¹) ∈ P
    rw [map_mul, map_mul, map_inv]
    exact hn
  have hYD : Y ≤ D := by
    intro y hy
    obtain ⟨n, hn⟩ := hDpow y (hYfix hy)
    have hcop : Nat.Coprime (3 ^ n) (orderOf y) := by
      refine Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr ?_)
      intro h
      exact hY3 (h.trans (Subgroup.orderOf_dvd_natCard Y hy))
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    have hmem : (y ^ 3 ^ n) ^ m ∈ D := D.pow_mem hn m
    rwa [hm] at hmem
  have hYsub : (Y.subgroupOf (Sec4.autFix β)).IsSubnormal :=
    isSubnormal_subgroupOf_of_normalizes hYD hDnorm hYnorm
  have hYbot : Y = ⊥ := hNoSz β hβ3 Y hYfix hYsub hYperf hY3
  rw [eq_bot_iff]
  intro p hp
  obtain ⟨y, rfl⟩ := hPle hp
  have hyY : y ∈ Y := hp
  rw [hYbot, Subgroup.mem_bot] at hyY
  rw [Subgroup.mem_bot, hyY, map_one]

end CFSG.RankThree.PartTwo.Sec14.Ronan148K
