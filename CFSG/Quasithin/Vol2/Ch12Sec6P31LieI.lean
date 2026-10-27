module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31LieB
public import CFSG.Quasithin.Vol2.Ch12Sec6P31LieC
public import CFSG.Quasithin.Vol2.Ch12Sec6P31LieD
public import CFSG.Quasithin.Vol2.Ch12Sec6P31LieE
public import CFSG.Quasithin.Vol2.Ch12Sec6P31LieF
public import CFSG.Quasithin.Vol2.Ch12Sec6P31LieG
public import CFSG.Quasithin.Vol2.Ch12Sec6P31LieH

public section

namespace CFSG.Quasithin.H13.S126P31

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem psl34_out_exp {K : Type} [Group K] [Finite K]
    (hK : IsPSL 3 2 2 K) :
    ∀ β : MulAut K, β ^ 4 ∈ (MulAut.conj : K →* MulAut K).range →
      β ^ 2 ∈ (MulAut.conj : K →* MulAut K).range := by
  have haut := psl34_card_aut hK
  obtain ⟨P, hPn, hPi, hIP, hsq⟩ := psl34_aut_structure hK haut
  obtain ⟨hsimple, hcard⟩ := isPSL_three_two_two_props hK
  haveI := hsimple
  have hcen : Subgroup.center K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
    · exact h
    · exfalso
      refine not_comm_of_simple_card (X := K) (by rw [hcard]; norm_num) fun a b => ?_
      have : a ∈ Subgroup.center K := by rw [h]; exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.1 this b).symm
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    intro x y hxy
    have h1 : MulAut.conj (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
    have h2 : x⁻¹ * y ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun f : MulAut K => f g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * (x⁻¹ * y) = ((x⁻¹ * y) * g * (x⁻¹ * y)⁻¹) * (x⁻¹ * y) := by rw [this]
        _ = (x⁻¹ * y) * g := by group
    rw [hcen, Subgroup.mem_bot] at h2
    exact (inv_mul_eq_one.1 h2)
  set I : Subgroup (MulAut K) := (MulAut.conj : K →* MulAut K).range with hI
  haveI : I.Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal K
  have hIc : Nat.card I = 20160 := by
    rw [← hcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hPc : Nat.card P = 60480 := by
    have := Subgroup.card_mul_index P
    rw [hPi, haut] at this
    omega
  have hIdx : (I.subgroupOf P).index = 3 := by
    have h1 := Subgroup.card_mul_index (I.subgroupOf P)
    have h2 : Nat.card (I.subgroupOf P) = Nat.card I :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIP).toEquiv
    rw [h2, hIc, hPc] at h1
    omega
  intro β hβ
  have hb : (⟨β ^ 2, hsq β⟩ : P) ^ 3 ∈ I.subgroupOf P := by
    have := Subgroup.pow_index_mem (I.subgroupOf P) (⟨β ^ 2, hsq β⟩ : P)
    rwa [hIdx] at this
  rw [Subgroup.mem_subgroupOf] at hb
  have hb' : β ^ 6 ∈ I := by simpa [← pow_mul] using hb
  have h6 : β ^ 2 = β ^ 6 * (β ^ 4)⁻¹ := by group
  rw [h6]
  exact I.mul_mem hb' (I.inv_mem hβ)

theorem sl34_card_aut_dvd {K : Type} [Group K] [Finite K]
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) (e : K ≃* ↥(StatedSL 3 F)) :
    Nat.card (MulAut K) ∣ 241920 := by
  obtain ⟨hperf, -, hPSL⟩ := sl34_central_extension hF e
  have h1 := card_mulAut_dvd_of_perfect_central hperf
  rwa [psl34_card_aut hPSL] at h1

theorem sl34_out_exp {K : Type} [Group K] [Finite K]
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) (e : K ≃* ↥(StatedSL 3 F)) :
    ∀ α : MulAut K, α ^ 4 ∈ (MulAut.conj : K →* MulAut K).range →
      α ^ 2 ∈ (MulAut.conj : K →* MulAut K).range := by
  obtain ⟨hperf, -, hPSL⟩ := sl34_central_extension hF e
  exact out_exp_of_perfect_central hperf (psl34_out_exp hPSL)

theorem sl34_card_normalizer_sylow {K : Type} [Group K] [Finite K] {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = 4) (e : K ≃* ↥(StatedSL 3 F)) (T : Subgroup K)
    (hT : IsSylowTwoOf T ⊤) :
    Nat.card ↥(Subgroup.normalizer (T : Set K)) = 576 := by
  obtain ⟨hperf, hZ, hPSL⟩ := sl34_central_extension hF e
  have h1 := card_normalizer_of_central_odd (Subgroup.center K) le_rfl
    (by rw [hZ]; omega) hT.2.1
  have h2 := psl34_card_normalizer_sylow hPSL _ (isSylowTwoOf_map_mk' (Subgroup.center K) hT)
  rw [h1, hZ, h2]

theorem sl34_overgroup
    {K : Type} [Group K] [Finite K] {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : K ≃* ↥(StatedSL 3 F)) (T N W : Subgroup K) (hT : IsSylowTwoOf T ⊤)
    (hB : Subgroup.normalizer (T : Set K) ≤ N) (hNB : N ≠ Subgroup.normalizer (T : Set K))
    (hNK : N ≠ ⊤) (hWN : W ≤ N) (hWnorm : (W.subgroupOf N).Normal)
    (hW23 : ∀ p : ℕ, p.Prime → p ∣ Nat.card W → p = 2 ∨ p = 3) : ¬ 9 ∣ Nat.card W := by
  obtain ⟨hperf, hZ, hPSL⟩ := sl34_central_extension hF e
  refine overgroup_of_central_quotient (Subgroup.center K) le_rfl hZ ?_ T N W hT hB hNB hNK hWN
    hWnorm hW23
  intro T' N' W' hT' hB' hN'B hN'K hW'N hW'norm hW'23
  exact psl34_overgroup hPSL T' N' W' hT' (psl34_card_normalizer_sylow hPSL T' hT') hB' hN'B
    hN'K hW'N hW'norm hW'23

end CFSG.Quasithin.H13.S126P31
