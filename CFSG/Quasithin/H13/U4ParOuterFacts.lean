module

public import CFSG.Quasithin.H13.U4ParSp
public import CFSG.Quasithin.Background.B3FourConj
import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Rk2B

public section

namespace CFSG.Quasithin.H13.U4Par

open Matrix CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.BorelTits

theorem map_inf_centralizer_singleton {A B : Type*} [Group A] [Group B] {φ : A →* B}
    (hφ : Function.Injective φ) (X : Subgroup A) (a : A) :
    (X ⊓ Subgroup.centralizer ({a} : Set A)).map φ =
      X.map φ ⊓ Subgroup.centralizer ({φ a} : Set B) := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hc⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    rw [Set.mem_singleton_iff] at hz
    rw [hz, ← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hc a (Set.mem_singleton a)]
  · rintro ⟨⟨x, hx, rfl⟩, hc⟩
    refine ⟨x, ⟨hx, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩, rfl⟩
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    apply hφ
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp hc (φ a) (Set.mem_singleton _)

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem perfectCore_eq_of_inf_range {Ŷ : Type} [Group Ŷ] [Finite Ŷ] {ψ : hypSU h 2 0 →* Ŷ}
    (hidx : ψ.range.index = 2) {M : Subgroup Ŷ} {X : Subgroup (hypSU h 2 0)}
    (hMX : M ⊓ ψ.range = X.map ψ) : perfectCore M = (perfectCore X).map ψ := by
  have := h.finite
  have := finite_hypSU h
  have hle : perfectCore M ≤ ψ.range :=
    (perfectCore_le_derivedSeriesOf M 1).trans ((Subgroup.commutator_mono le_top le_top).trans
      (U4V.commutator_le_of_index_le_two (le_of_eq hidx)))
  have hXM : X.map ψ ≤ M := hMX ▸ inf_le_left
  apply le_antisymm
  · rw [map_perfectCore, ← hMX]
    calc perfectCore M = perfectCore (perfectCore M) :=
          (perfectCore_eq_self_of_perfect (perfectCore_perfect M)).symm
      _ ≤ perfectCore (M ⊓ ψ.range) := perfectCore_mono (le_inf (perfectCore_le M) hle)
  · rw [map_perfectCore]
    exact perfectCore_mono hXM

theorem ext_facts (hm : 2 ≤ m) {Ŷ : Type} [Group Ŷ] [Finite Ŷ] {ψ : hypSU h 2 0 →* Ŷ}
    (hψ : Function.Injective ψ) (hidx : ψ.range.index = 2)
    (hC : Subgroup.centralizer (ψ.range : Set Ŷ) = ⊥)
    {T M₁ M₂ : Subgroup Ŷ} (hpair : IsYAmalgamPair T M₁ M₂)
    (hU : (hypUnitriangular h 2 0).map ψ = T ⊓ ψ.range)
    (hM₁ : M₁ = Subgroup.normalizer (((parP2 h).map ψ : Subgroup Ŷ) : Set Ŷ))
    (hM₁ψ : M₁ ⊓ ψ.range = (parP2 h).map ψ)
    (hM₂ : M₂ = Subgroup.normalizer (((parP h).map ψ : Subgroup Ŷ) : Set Ŷ))
    (hM₂ψ : M₂ ⊓ ψ.range = (parP h).map ψ)
    {S : Subgroup Ŷ} (hS : IsSylowTwoOf S (M₁ ⊓ M₂)) :
    pCoreOf 2 M₁ = pCoreOf 2 (perfectCore M₁) ∧ pCoreOf 2 M₂ = pCoreOf 2 (perfectCore M₂) ∧
    ∃ t ∈ S, orderOf t = 2 ∧ t ∉ pCoreOf 2 (perfectCore M₂) ∧
      pCoreOf 2 (perfectCore M₂ ⊔ S) = pCoreOf 2 (perfectCore M₂) ⊔ Subgroup.zpowers t ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ m ∧
        ∃ P : Subgroup ↥(StatedSp 2 F), IsMaxParabolic2 ⊤ P ∧
          Nonempty (↥(perfectCore M₂ ⊓ Subgroup.centralizer ({t} : Set Ŷ)) ≃*
            ↥(perfectCore P)) := by
  classical
  have := h.finite
  have := finite_hypSU h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : ψ.range.Normal := Subgroup.normal_of_index_eq_two hidx
  obtain ⟨y₀, hy₀, hy2, hact⟩ := exists_frob_elt h ψ hψ hidx hC
  have hc₂ : perfectCore M₂ = (perfectCore (parP h)).map ψ :=
    perfectCore_eq_of_inf_range h hidx hM₂ψ
  have hc₁ : perfectCore M₁ = (perfectCore (parP2 h)).map ψ :=
    perfectCore_eq_of_inf_range h hidx hM₁ψ
  have hO₂ : pCoreOf 2 (perfectCore M₂) = (radQ h).map ψ := by
    rw [hc₂, pCoreOf_map_of_inj hψ, pCoreOf_perfectCore_parP h hm]
  have hO₁ : pCoreOf 2 (perfectCore M₁) = (radQ2 h).map ψ := by
    rw [hc₁, pCoreOf_map_of_inj hψ, pCoreOf_perfectCore_parP2_eq h hm]
  refine ⟨?_, ?_, ?_⟩
  · rw [hO₁, pCoreOf_normalizer_parP2 h hact hm hψ hidx hy₀ hM₁ hM₁ψ]
  · rw [hO₂, pCoreOf_normalizer_parP h hact hm hψ hidx hy₀ hM₂ hM₂ψ]
  set U₀ := (hypUnitriangular h 2 0).map ψ with hU₀
  set S₀ := U₀ ⊔ Subgroup.zpowers y₀ with hS₀
  have hy₀M₁ : y₀ ∈ M₁ := hM₁ ▸ mem_normalizer_map_of_frob h hact fun g hg =>
    frobElt_mem_parP2 h hg
  have hy₀M₂ : y₀ ∈ M₂ := hM₂ ▸ mem_normalizer_map_of_frob h hact fun g hg =>
    frobElt_mem_parP h hg
  have hTM : ∀ M' : Subgroup Ŷ, M' = M₁ ∨ M' = M₂ → T ≤ M' := fun M' hM' =>
    Subgroup.le_normalizer.trans ((hpair.2.2 M').mpr hM').2
  have hU₀M : ∀ M' : Subgroup Ŷ, M' = M₁ ∨ M' = M₂ → U₀ ≤ M' := fun M' hM' =>
    (hU ▸ inf_le_left : U₀ ≤ T).trans (hTM M' hM')
  have hS₀X : S₀ ≤ M₁ ⊓ M₂ := sup_le (le_inf (hU₀M M₁ (Or.inl rfl)) (hU₀M M₂ (Or.inr rfl)))
    ((Subgroup.zpowers_le (H := M₁ ⊓ M₂)).mpr ⟨hy₀M₁, hy₀M₂⟩)
  have hyU : Subgroup.zpowers y₀ ≤ Subgroup.normalizer (U₀ : Set Ŷ) :=
    (Subgroup.zpowers_le (H := Subgroup.normalizer _)).mpr
      (mem_normalizer_map_of_frob h hact fun g hg => frobElt_mem_hypUnitriangular h hg)
  have hU2 : IsPGroup 2 (hypUnitriangular h 2 0) := (isSylowTwoOf_hypUnitriangular h).2.1
  have hy2' : y₀ ^ 2 ^ 1 = 1 := by rw [pow_one, pow_two, hy2]
  have hS₀2 : IsPGroup 2 S₀ :=
    IsPGroup.to_sup_of_normal_left' (hU2.map ψ) (isPGroup_zpowers_of_pow hy2') hyU
  have hzinf : Subgroup.zpowers y₀ ⊓ U₀ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_inf.mp hz).1
    have hz2 := (Subgroup.mem_inf.mp hz).2
    have hyo : orderOf y₀ = 2 := orderOf_eq_prime (by rw [pow_two, hy2])
      (fun e => hy₀ (by rw [e]; exact ψ.range.one_mem))
    rcases Int.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · have hsq : y₀ ^ (2 : ℤ) = 1 := by rw [_root_.zpow_two, hy2]
      rw [← two_mul, _root_.zpow_mul, hsq, _root_.one_zpow]
      exact Subgroup.one_mem _
    · exfalso
      have e : y₀ ^ (2 * j + 1) = y₀ := by
        have hsq : y₀ ^ (2 : ℤ) = 1 := by rw [_root_.zpow_two, hy2]
        rw [_root_.zpow_add, _root_.zpow_mul, hsq, _root_.one_zpow, one_mul,
          zpow_one]
      rw [e] at hz2
      exact hy₀ ((Subgroup.map_le_range ψ _) hz2)
  have hcardS₀ : Nat.card S₀ = Nat.card U₀ * 2 := by
    have hprod := Sec526.card_sup_mul_card_inf_of_normalizes hyU
    rw [hzinf, Subgroup.card_bot, mul_one, sup_comm, Nat.card_zpowers,
      orderOf_eq_prime (by rw [pow_two, hy2])
        (fun e => hy₀ (by rw [e]; exact ψ.range.one_mem))] at hprod
    rw [hS₀, hprod, mul_comm]
  have hT2 : Nat.card T = Nat.card U₀ * 2 := by
    have hTn : ¬ T ≤ ψ.range := by
      intro hle
      apply hpair.1.2.2
      have h1 : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right T
      rw [h1, ← Subgroup.relIndex_mul_index hle, hidx]
      exact dvd_mul_left 2 _
    have hrel : (T ⊓ ψ.range).relIndex T = 2 := by
      have h1 : (T ⊓ ψ.range).relIndex T = ψ.range.relIndex T := by
        rw [inf_comm, Subgroup.inf_relIndex_right]
      rw [h1]
      have h2 : ψ.range.relIndex T ∣ 2 := by
        have := Subgroup.relIndex_dvd_index_of_normal ψ.range T
        rwa [hidx] at this
      have h3 : ψ.range.relIndex T ≠ 1 := fun e => hTn (Subgroup.relIndex_eq_one.mp e)
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h4 | h4
      · exact absurd h4 h3
      · exact h4
    have e1 : (T ⊓ ψ.range) ⊓ T = U₀ := by
      rw [hU]
      exact inf_eq_left.mpr inf_le_left
    have := Subgroup.relIndex_mul_card (H := T ⊓ ψ.range) (K := T)
    rw [hrel, e1] at this
    rw [← this, mul_comm]
  have hS₀syl : IsSylowTwoOf S₀ (M₁ ⊓ M₂) := by
    have hTX : IsSylowTwoOf T (M₁ ⊓ M₂) := by
      refine ⟨le_inf (hTM M₁ (Or.inl rfl)) (hTM M₂ (Or.inr rfl)), hpair.1.2.1, fun h2 => ?_⟩
      apply hpair.1.2.2
      rw [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T,
        ← Subgroup.relIndex_mul_index (le_inf (hTM M₁ (Or.inl rfl)) (hTM M₂ (Or.inr rfl)))]
      exact Dvd.dvd.mul_right h2 _
    refine ⟨hS₀X, hS₀2, fun h2 => hTX.2.2 ?_⟩
    have e1 := Subgroup.relIndex_mul_card (H := S₀) (K := M₁ ⊓ M₂)
    have e2 := Subgroup.relIndex_mul_card (H := T) (K := M₁ ⊓ M₂)
    rw [inf_eq_left.mpr hS₀X] at e1
    rw [inf_eq_left.mpr hTX.1] at e2
    have hcard : Nat.card S₀ = Nat.card T := by rw [hcardS₀, hT2]
    rw [hcard] at e1
    have hidxeq : S₀.relIndex (M₁ ⊓ M₂) = T.relIndex (M₁ ⊓ M₂) :=
      Nat.eq_of_mul_eq_mul_right Nat.card_pos (e1.trans e2.symm)
    change 2 ∣ T.relIndex (M₁ ⊓ M₂)
    rw [← hidxeq]
    exact h2
  obtain ⟨c, hcX, hcS⟩ := B3.exists_conj_eq_sylow hS hS₀syl
  have hcM₂ : c ∈ M₂ := (Subgroup.mem_inf.mp hcX).2
  set t := c * y₀ * c⁻¹ with ht
  have htS : t ∈ S := by
    rw [← hcS]
    exact ⟨y₀, Subgroup.mem_sup_right (Subgroup.mem_zpowers y₀), rfl⟩
  have hinj : Function.Injective (MulAut.conj c).toMonoidHom := (MulAut.conj c).injective
  have hcN : c ∈ Subgroup.normalizer ((perfectCore M₂ : Subgroup Ŷ) : Set Ŷ) :=
    normalizer_le_normalizer_perfectCore M₂ (Subgroup.le_normalizer hcM₂)
  have hcNQ : c ∈ Subgroup.normalizer ((pCoreOf 2 (perfectCore M₂) : Subgroup Ŷ) : Set Ŷ) :=
    normalizer_le_normalizer_pCoreOf 2 _ hcN
  have hcP : B3.cj c (perfectCore M₂) = perfectCore M₂ :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hcN
  have hcQ : B3.cj c (pCoreOf 2 (perfectCore M₂)) = pCoreOf 2 (perfectCore M₂) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hcNQ
  have hyo : orderOf y₀ = 2 := orderOf_eq_prime (by rw [pow_two, hy2])
    (fun e => hy₀ (by rw [e]; exact ψ.range.one_mem))
  refine ⟨t, htS, ?_, ?_, ?_, ?_⟩
  · have := MulEquiv.orderOf_eq (MulAut.conj c) y₀
    rw [MulAut.conj_apply] at this
    rw [ht, this, hyo]
  · intro htQ
    have htR : t ∈ ψ.range := by
      rw [hO₂] at htQ
      exact (Subgroup.map_le_range ψ _) htQ
    apply hy₀
    have e : y₀ = c⁻¹ * t * c⁻¹⁻¹ := by rw [ht]; group
    rw [e]
    exact hn.conj_mem _ htR _
  ·
    have hU₀c : U₀ ≤ perfectCore M₂ := by
      rw [hc₂]
      exact Subgroup.map_mono (hypUnitriangular_le_perfectCore_parP h hm)
    have hsup : perfectCore M₂ ⊔ S₀ = perfectCore M₂ ⊔ Subgroup.zpowers y₀ := by
      rw [hS₀, ← sup_assoc, sup_eq_left.mpr hU₀c]
    have hsup' : perfectCore M₂ ⊔ S = B3.cj c (perfectCore M₂ ⊔ Subgroup.zpowers y₀) := by
      rw [← hsup, B3.cj, Subgroup.map_sup, ← B3.cj, ← B3.cj, hcP, hcS]
    rw [hsup', B3.cj, pCoreOf_map_of_inj hinj, ← B3.cj, hc₂,
      pCoreOf_perfectCore_sup_zpowers h hact hm hψ hy2, ← hO₂, ← hc₂, B3.cj, Subgroup.map_sup,
      ← B3.cj, hcQ, MonoidHom.map_zpowers]
    rfl
  ·
    obtain ⟨F, _, _, hF, P, hP, ⟨e⟩⟩ := exists_sp4_parabolic_equiv h hm
    refine ⟨F, inferInstance, inferInstance, hF, P, hP, ⟨?_⟩⟩
    have hW : perfectCore M₂ ⊓ Subgroup.centralizer ({t} : Set Ŷ) =
        (perfectCore (parP h) ⊓ frobFix h).map ((MulAut.conj c).toMonoidHom.comp ψ) := by
      rw [← Subgroup.map_map, ← map_inf_centralizer h hact hψ, ← hc₂,
        map_inf_centralizer_singleton hinj, ← B3.cj, hcP]
      rfl
    exact (MulEquiv.subgroupCongr hW).trans
      (((perfectCore (parP h) ⊓ frobFix h).equivMapOfInjective _ (hinj.comp hψ)).symm.trans e)

end CFSG.Quasithin.H13.U4Par
