module

public import CFSG.RankThree.PartOne.KF.R56Final
public import CFSG.RankThree.PartOne.KF.R5Levi
public import CFSG.RankThree.PartOne.KF.LayerTransfer
public import CFSG.RankThree.PartOne.KF.FratRows
public import CFSG.RankThree.PartOne.KF.LayerFrame

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg Matrix

theorem kf1212LayerRow5 : KF1212LayerRow 5 := by
  intro G _ _ p A c L E ctx hmodel hEA _
  have hEA' : E = A := hEA (by norm_num)
  have h := ctx.hyp
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hcore := ctx.table_core
  obtain ⟨f, K, hKf, hKfin, hchar, hK, hf1, hpq, -, ε, hε, hFT₁, hFT₂⟩ :=
    exists_runitary_frame (n := 4) (Or.inl rfl) d8Comb_four hcore hmodel
  have : Fact p.Prime := ⟨hp⟩
  let σ : K ≃+* K := unitaryInvolution K 2 f
  have hFq : Nat.card (fixF σ) = 2 ^ f := card_fixedSubfield hK
  have hpf : p ≤ 2 ^ f - 1 := Nat.le_of_dvd (by
    have := Nat.one_lt_two_pow (n := f) (by omega)
    omega) hpq
  have hK6 : 6 ≤ 2 ^ f := by omega
  have hK4 : 4 ≤ Nat.card (fixF σ) := by rw [hFq]; omega
  obtain ⟨ζ', hζ'⟩ : ∃ ζ : (fixF σ)ˣ, IsPrimitiveRoot ζ p := by
    have hdvd : p ∣ Nat.card (fixF σ)ˣ := by
      rw [Nat.card_units, hFq]
      exact hpq
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
    refine ⟨z, ?_⟩
    have := IsPrimitiveRoot.orderOf z
    rwa [hz] at this
  let ζ : Kˣ := upU σ ζ'
  have hσζ : σ (ζ : K) = ζ := σ_upU σ ζ'
  have hζp' : ζ' ^ p = 1 := hζ'.pow_eq_one
  have hζ'1 : ζ' ≠ 1 := hζ'.ne_one (by omega)
  have hζp : ζ ^ p = 1 := by rw [← map_pow, hζp', map_one]
  have hζ1 : ζ ≠ 1 := fun h1 => hζ'1 (upU_injective σ (by rw [map_one]; exact h1))
  have hζ2' : ζ' ^ 2 ≠ 1 := hζ'.pow_ne_one_of_pos_of_lt (by norm_num) (by omega)
  have hζ2 : ζ ^ 2 ≠ 1 := fun h2 =>
    hζ2' (upU_injective σ (by rw [map_pow, map_one]; exact h2))
  have hq : IsCentralPQuot p (suQ 4 hK) := isCentralPQuot_suQ hp hp2 (by norm_num) hpq hf1 hK
  have hbMT : b5 σ ζ hσζ ∈ torus5 σ p := b5_mem_torus5 hσζ hζp
  have hbMp : b5 σ ζ hσζ ^ p = 1 := torus5_pow_eq_one hbMT
  have hbMne : b5 σ ζ hσζ ≠ 1 := by
    intro h1
    have := congrArg (fun x : ↥(SU σ 4) => gu x 1 1) h1
    simp only [gu_one, Matrix.one_apply_eq] at this
    have h11 : gu (b5 σ ζ hσζ) 1 1 = (ζ : K) := by
      show ((diagU (dvec4 1 ζ) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 1 = _
      simp [diagU_val, dvec4]
    exact hζ1 (Units.ext (by rw [← h11]; exact this))
  obtain ⟨x, hx⟩ := hFT₁ (b5 σ ζ hσζ) hbMT
  have hxL : (x : G) ∈ L := hcore.F_le x.2
  have hxA : (x : G) ∈ A := hEA' ▸ x.2.1
  have hbb : ε ⟨(x : G), hxL⟩ = suQ 4 hK (b5 σ ζ hσζ) := hx
  have hb1 : (x : G) ≠ 1 := by
    intro h1
    have h2 : suQ 4 hK (b5 σ ζ hσζ) = suQ 4 hK 1 := by
      rw [← hbb, map_one]
      have : (⟨(x : G), hxL⟩ : ↥L) = 1 := Subtype.ext h1
      rw [this, map_one]
    exact hbMne (hq.eq_of_map_eq hbMp (one_pow p) h2)
  have hAL : A ⊓ L = E ⊓ L := by rw [hEA']
  have hAT : ((A ⊓ L).subgroupOf L).map ε = (torus5 σ p).map (suQ 4 hK) := by
    rw [hAL]
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨t, ht, hta⟩ := hFT₂ ⟨(a : G), Subgroup.mem_subgroupOf.1 ha⟩
      exact ⟨t, ht, hta.symm⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨x', hx'⟩ := hFT₁ t ht
      exact ⟨Subgroup.inclusion hcore.F_le x', Subgroup.mem_subgroupOf.2 x'.2, hx'⟩
  have hKM := perfectResidual_centralizer_b5 σ hK4 hσζ hζ1 hζ2
  have hA : A ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by
    calc A = E := hEA'.symm
      _ = (E ⊓ L) ⊔ Subgroup.zpowers c := ctx.generic.E_eq
      _ ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by rw [sup_comm, hAL]
  obtain ⟨KL, hKLeq, hKLq, hKLz, hAK, htwo, ⟨eqv⟩⟩ := exists_layerCore_of_cover hp hp2
    (IsPGroup.of_card h.A_card) h.A_elem ctx.L_le_centralizer hA ε
    (suQ 4 hK) hε hq hxA hxL hbMp hbb
    (T₀ := torus5 σ p) (U := rootU5 σ) (fun t ht => torus5_pow_eq_one ht) hAT
    (isQuasisimple_perfectResidual_centralizer_b5 σ hK4 hσζ hζ1 hζ2)
    (by
      rw [hKM, card_center_range_suBlock]
      exact hp.not_dvd_one)
    (by
      rw [hKM]
      exact card_torus5_inf_range hp.pos ⟨ζ', hζ'⟩)
    (by rw [hKM]; exact rootU5_le_range) isPGroup_rootU5 torus5_le_normalizer_rootU5
    ⟨suBlock σ (tr2 1), suBlock_tr2_mem_rootU5 1, rho5 σ ζ', rho5_mem_torus5 hζp',
      suBlock_tr2_one_not_commute_rho5 hζ'1⟩
  refine ⟨(x : G), KL, ⟨⟨hxA, hxL, hb1⟩, hKLeq, hKLq, hKLz, hAK, htwo⟩, ?_⟩
  refine ⟨by norm_num, by norm_num, f, hf1, hpq, ⟨Nat.prime_two, hf1, by norm_num, ?_, ?_⟩,
    fixF σ, inferInstance, inferInstance, hFq, ?_⟩
  · intro h2
    have := congrArg Prod.snd h2
    simp only at this
    omega
  · intro h2
    have := congrArg Prod.snd h2
    simp only at this
    omega
  · obtain ⟨e₃⟩ := exists_centerQuotient_mulEquiv (MulEquiv.subgroupCongr hKM)
    obtain ⟨e₄⟩ := exists_centerQuotient_mulEquiv
      (MonoidHom.ofInjective (suBlock_injective σ)).symm
    exact ⟨eqv.trans (e₃.trans (e₄.trans (projectiveSpecialLinearGroupEquivStatedProj 2 (fixF σ))))⟩

end CFSG.RankThree.PartOne
