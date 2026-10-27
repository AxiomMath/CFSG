module

public import CFSG.RankThree.PartTwo.Sec15.Item156StepsProofPoint
public import CFSG.RankThree.PartTwo.Sec15.Item156StepsProofA5
import CFSG.RankThree.PartTwo.KFacts.KS14HJCentralizer

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec15.Proof152Gen CFSG.RankThree.PartTwo.Sec15.Proof156

namespace Proof156

theorem isQuasisimple_of_isPerfect_of_quot_six {Q : Type*} [Group Q] (hQ : Group.IsPerfect Q)
    (e : Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin 6)) : IsQuasisimple Q := by
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  refine ⟨hQ, e.isSimpleGroup, ?_⟩
  let a : alternatingGroup (Fin 6) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
      rw [Equiv.Perm.mem_alternatingGroup]; simp [Equiv.Perm.sign_mul]⟩
  let b : alternatingGroup (Fin 6) :=
    ⟨Equiv.swap 1 2 * Equiv.swap 3 4, by
      rw [Equiv.Perm.mem_alternatingGroup]; simp [Equiv.Perm.sign_mul]⟩
  have hab : a * b ≠ b * a := by
    intro hh
    have := congrArg Subtype.val hh
    revert this
    decide
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  have h' := congrArg e h
  simpa using h'

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem eq_bot_of_isPGroup_of_centralizer_le_normalizer
    (hΓ : Nonempty (Γ ≃* CFSG.Blueprint.NativeSporadic.J2))
    {z : Γ} (hz1 : z ≠ 1)
    (hzc : ∃ S : Sylow 3 Γ, z ∈ (S : Subgroup Γ) ∧
      (S : Subgroup Γ) ≤ Subgroup.centralizer ({z} : Set Γ))
    {R₀ : Subgroup Γ} (hR₀ : IsPGroup 2 R₀)
    (hN : Subgroup.centralizer ({z} : Set Γ) ≤ Subgroup.normalizer (R₀ : Set Γ)) : R₀ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  set C := Subgroup.centralizer ({z} : Set Γ) with hC
  have hCp : Group.IsPerfect C := KFacts.KS14.j2_centralizer_isPerfect h415 hΓ hz1 hzc
  have hO2 : CFSG.pCore 2 ↥C = ⊥ := KFacts.KS14.j2_pCore_two_centralizer_eq_bot h415 hΓ hz1 hzc
  have hCcen := KFacts.KS14.j2_center_centralizer h415 hΓ hz1 hzc
  have h6 := KFacts.KS14.j2_centralizer_isTripleCover h415 hΓ hz1 hzc
  obtain ⟨hZc, hZ3, hZn, ⟨eA⟩⟩ := KFacts.KS14.j2_centralizer_quotient h415 hΓ hz1 hzc
  have hC1080 : Nat.card C = 1080 := by
    rw [card_of_isTripleCover h6, card_alternatingGroup_six]
  have hΓ604800 : Nat.card Γ = 604800 := by
    obtain ⟨e⟩ := hΓ
    rw [Nat.card_congr e.toEquiv, KFacts.KS14.card_nativeJ2]
  have hRC : R₀ ⊓ C = ⊥ := by
    have hn : ((R₀ ⊓ C).subgroupOf C).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr ?_
      exact Late.le_normalizer_inf hN Subgroup.le_normalizer
    have h2 : IsPGroup 2 ((R₀ ⊓ C).subgroupOf C) :=
      (hR₀.to_le inf_le_left).comap_of_injective C.subtype C.subtype_injective
    have hle : (R₀ ⊓ C).subgroupOf C ≤ CFSG.pCore 2 ↥C := le_sSup ⟨hn, h2⟩
    rw [hO2, le_bot_iff, Subgroup.subgroupOf_eq_bot] at hle
    exact disjoint_self.mp (hle.mono_right inf_le_right)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR₀
  by_cases hk3 : 3 ≤ k
  ·
    obtain ⟨T⟩ : Nonempty (Sylow 2 ↥C) := inferInstance
    set T' : Subgroup Γ := (T : Subgroup ↥C).map C.subtype with hT'
    have hT'C : T' ≤ C := Subgroup.map_subtype_le _
    have hT'2 : IsPGroup 2 T' := T.isPGroup'.map C.subtype
    have hT'8 : 8 ∣ Nat.card T' := by
      rw [hT', Subgroup.card_map_of_injective C.subtype_injective]
      have h1 := Sylow.card_eq_multiplicity T
      have h2 : (1080 : ℕ).factorization 2 = 3 := by
        rw [show (1080 : ℕ) = 2 ^ 3 * 135 by norm_num,
          Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
          Nat.Prime.factorization_pow Nat.prime_two,
          Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
        simp
      rw [h1, hC1080, h2]
      norm_num
    set Q := R₀ ⊔ T' with hQ
    have hT'N : T' ≤ Subgroup.normalizer (R₀ : Set Γ) := hT'C.trans hN
    have hQ2 : IsPGroup 2 Q := hR₀.to_sup_of_normal_left' hT'2 hT'N
    have hRQ : R₀ ≤ Q := le_sup_left
    have hRn : (R₀.subgroupOf Q).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hRQ).mpr
        (sup_le Subgroup.le_normalizer hT'N)
    have hcardQ := Subgroup.card_eq_card_quotient_mul_card_subgroup (R₀.subgroupOf Q)
    have hR₀' : Nat.card (R₀.subgroupOf Q) = Nat.card R₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRQ).toEquiv
    let f : ↥(T'.subgroupOf Q) →* ↥Q ⧸ R₀.subgroupOf Q :=
      (QuotientGroup.mk' (R₀.subgroupOf Q)).comp (T'.subgroupOf Q).subtype
    have hfinj : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      have h1 : ((x : ↥Q) : Γ) ∈ R₀ := by
        have := (QuotientGroup.eq_one_iff _).mp hx
        exact Subgroup.mem_subgroupOf.mp this
      have h2 : ((x : ↥Q) : Γ) ∈ T' := Subgroup.mem_subgroupOf.mp x.2
      have h3 : ((x : ↥Q) : Γ) ∈ R₀ ⊓ C := ⟨h1, hT'C h2⟩
      rw [hRC, Subgroup.mem_bot] at h3
      exact (Subgroup.mem_bot).mpr (Subtype.ext (Subtype.ext h3))
    have hT'Q : Nat.card (T'.subgroupOf Q) = Nat.card T' :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
    have hdvdT : Nat.card T' ∣ Nat.card (↥Q ⧸ R₀.subgroupOf Q) := by
      rw [← hT'Q, Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    have h64 : 64 ∣ Nat.card Q := by
      rw [hcardQ, hR₀', hk]
      have h8 : 2 ^ 3 ∣ 2 ^ k := Nat.pow_dvd_pow 2 hk3
      exact (show (64 : ℕ) = 8 * 8 by norm_num) ▸ Nat.mul_dvd_mul (hT'8.trans hdvdT) h8
    obtain ⟨F₀, hF₀p, hF₀60⟩ := exists_isPerfect_card_sixty_of_quotient_six
      ((Subgroup.zpowers z).subgroupOf C) hZc hZ3 eA
    set F := F₀.map C.subtype with hF
    have hFC : F ≤ C := Subgroup.map_subtype_le _
    have hFp : Group.IsPerfect F := isPerfect_map_subtype hF₀p
    have hF60 : Nat.card F = 60 := by
      rw [hF, Subgroup.card_map_of_injective C.subtype_injective, hF₀60]
    have htop := ks152J2Gen_holds Γ hΓ z hz1 hzc Q F hQ2 h64 hFC hFp hF60
    have hRCtop : R₀ ⊔ C = ⊤ := by
      rw [eq_top_iff, ← htop]
      exact sup_le (sup_le le_sup_left (hT'C.trans le_sup_right)) (hFC.trans le_sup_right)
    have hRnorm : R₀.Normal := by
      have hle : (⊤ : Subgroup Γ) ≤ Subgroup.normalizer (R₀ : Set Γ) := by
        rw [← hRCtop]
        exact sup_le Subgroup.le_normalizer hN
      exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hle)
    have hs : IsSimpleGroup Γ := by
      obtain ⟨e⟩ := hΓ
      have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
      exact e.isSimpleGroup
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R₀ with h | h
    · exact h
    · exfalso
      rw [h, Subgroup.card_top, hΓ604800] at hk
      have h3 : 3 ∣ 2 ^ k := by
        rw [← hk]
        norm_num
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  ·
    have hk2 : k ≤ 2 := by omega
    have hR4 : Nat.card R₀ ≤ 4 := by
      rw [hk]
      calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
        _ = 4 := by norm_num
    let ψ : ↥C →* MulAut ↥R₀ := R₀.normalizerMonoidHom.comp (Subgroup.inclusion hN)
    have hψ : ∀ (c : ↥C) (x : ↥R₀), ((ψ c x : ↥R₀) : Γ) = (c : Γ) * x * (c : Γ)⁻¹ :=
      fun c x => Sec4.normalizerMonoidHom_apply_coe _ x
    have hAut : Nat.card (MulAut ↥R₀) ≤ 24 := by
      have h1 : Nat.card (MulAut ↥R₀) ≤ Nat.card (Equiv.Perm ↥R₀) :=
        Nat.card_le_card_of_injective _ MulEquiv.toEquiv_injective
      have h2 : Nat.card (Equiv.Perm ↥R₀) = (Nat.card R₀).factorial := Nat.card_perm
      rw [h2] at h1
      have h3 : (Nat.card R₀).factorial ≤ (4 : ℕ).factorial := Nat.factorial_le hR4
      exact h1.trans (h3.trans (by decide))
    have hq := isQuasisimple_of_isPerfect_of_quot_six hCp
      ((QuotientGroup.quotientMulEquivOfEq hCcen).trans eA)
    have hker : ψ.ker = ⊤ := by
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hq ψ.normal_ker with h | h
      · exact h
      · exfalso
        have h1 : Nat.card ψ.ker ≤ 3 := by
          have := Subgroup.card_le_of_le h
          rw [hCcen] at this
          rw [← hZ3]
          exact this
        have h2 := Subgroup.card_mul_index ψ.ker
        rw [Subgroup.index_ker, hC1080] at h2
        have h3 : Nat.card ψ.range ≤ 24 :=
          (Subgroup.card_le_card_group _).trans hAut
        have h4 : 0 < Nat.card ψ.ker := Nat.card_pos
        nlinarith
    have hRle : R₀ ≤ C := by
      intro x hx
      have hzC : z ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
      have h1 : ψ ⟨z, hzC⟩ = 1 := MonoidHom.mem_ker.mp (hker ▸ Subgroup.mem_top _)
      have h2 := congrArg (fun σ : MulAut ↥R₀ => ((σ ⟨x, hx⟩ : ↥R₀) : Γ)) h1
      simp only [hψ, MulAut.one_apply] at h2
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * z = z * x * z⁻¹ * z := by rw [h2]
        _ = z * x := by group
    have h1 : R₀ ≤ R₀ ⊓ C := le_inf le_rfl hRle
    rw [hRC] at h1
    exact le_bot_iff.mp h1

end Proof156

theorem ks156J2Norm_holds :
    KS156J2Norm := by
  intro Γ _ _ hΓ z hz1 hzc R hR2 hRN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hZΓ : Subgroup.center Γ = ⊥ := KFacts.KS14.center_eq_bot_of_j2 h415 hΓ
  have hinj : Function.Injective (MulAut.conj : Γ →* MulAut Γ) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    have hgc : g ∈ Subgroup.center Γ := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h1 := congrArg (fun σ : MulAut Γ => σ x) (MonoidHom.mem_ker.mp hg)
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc x * g = g * x * g⁻¹ * g := by rw [h1]
        _ = g * x := by group
    rw [hZΓ] at hgc
    exact hgc
  set R₀ := R.comap (MulAut.conj : Γ →* MulAut Γ) with hR₀def
  have hR₀2 : IsPGroup 2 R₀ := hR2.comap_of_injective _ hinj
  have hR₀N : Subgroup.centralizer ({z} : Set Γ) ≤ Subgroup.normalizer (R₀ : Set Γ) := by
    refine Sec6.le_normalizer_of_forall_conj_mem fun c hc g hg => ?_
    show MulAut.conj (c * g * c⁻¹) ∈ R
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hRN ⟨c, hc, rfl⟩) _).mp hg
  have hR₀ := eq_bot_of_isPGroup_of_centralizer_le_normalizer hΓ hz1 hzc hR₀2 hR₀N
  have hfix : ∀ r ∈ R, ∀ c ∈ Subgroup.centralizer ({z} : Set Γ), r c = c := by
    intro r hr c hc
    have h1 : MulAut.conj c * r * (MulAut.conj c)⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp (hRN ⟨c, hc, rfl⟩) r).mp hr
    have h2 : MulAut.conj c * r * (MulAut.conj c)⁻¹ * r⁻¹ ∈ R := mul_mem h1 (inv_mem hr)
    have h3 : MulAut.conj c * r * (MulAut.conj c)⁻¹ * r⁻¹ = MulAut.conj (c * (r c)⁻¹) := by
      ext x
      simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, map_mul, map_inv,
        MulAut.apply_inv_self]
    rw [h3] at h2
    have h4 : c * (r c)⁻¹ ∈ R₀ := h2
    rw [hR₀, Subgroup.mem_bot] at h4
    exact (mul_inv_eq_one.mp h4).symm
  obtain ⟨S, -, hSC⟩ := hzc
  have hS27 : Nat.card (S : Subgroup Γ) = 27 := (h415 Γ hΓ S _ rfl _ rfl).1.1.2.1
  obtain ⟨E, hE9⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(S : Subgroup Γ)) 3 (n := 2)
    (by rw [hS27]; norm_num)
  set E' := E.map (S : Subgroup Γ).subtype with hE'
  have hE'9 : Nat.card E' = 9 := by
    rw [hE', Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hE9]
    norm_num
  have hE'C : E' ≤ Subgroup.centralizer ({z} : Set Γ) := (Subgroup.map_subtype_le E).trans hSC
  rw [eq_bot_iff]
  intro r hr
  obtain ⟨n, hn⟩ := hR2 ⟨r, hr⟩
  have hn' : r ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
  rw [Subgroup.mem_bot]
  exact eq_one_of_pow_two_pow ks152J2InvolNine_holds hΓ hE'9
    (fun e he => hfix r hr e (hE'C he)) n hn'

theorem step156CQR_of_a5_faith
    (h142 : Item142AllS14) (hA5 : Step156CQA5R)
    (hΩ : Step156CQOmegaR) (hF : Step156CQFaithR) : Step156CQR :=
  step156CQR_of_faith h142 (step156CQA6R_of_a5 hA5) hΩ ks156J2Norm_holds hF

end CFSG.RankThree.PartTwo.Sec15
