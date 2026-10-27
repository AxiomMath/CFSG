module

public import CFSG.LocalAnalysis.StandardType.GGQ2CentralizerPort
public import CFSG.LocalAnalysis.StandardType.GGQTwoAssemble
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBLemmas

public section

namespace CFSG.StandardType.GGQ2CentPort

open CFSG CFSG.Assembly

theorem ggQ2Cent_isPGroup_zpowers_three {G : Type*} [Group G] {z : G} {k : ℕ}
    (hz : z ^ 3 ^ k = 1) : IsPGroup 3 (Subgroup.zpowers z) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hz)
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

theorem ggQ2Cent_center_eq_bot {G : Type} [Group G] {L : Subgroup G} (hperf : commutator L = ⊤)
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R) : Subgroup.center R = ⊥ := by
  haveI : Group.IsPerfect L := Group.isPerfect_def.mpr hperf
  have h := Group.IsPerfect.center_quotient_center_eq_bot L
  rw [Subgroup.eq_bot_iff_forall]
  intro r hr
  have hmem : θ.symm r ∈ Subgroup.center (L ⧸ Subgroup.center L) := by
    rw [Subgroup.mem_center_iff]
    intro q
    apply θ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_center_iff.mp hr (θ q)
  rw [h, Subgroup.mem_bot] at hmem
  have := congrArg θ hmem
  simpa using this

theorem ggQ2Cent_eq_of_conj_eq {R : Type} [Group R] (hC : Subgroup.center R = ⊥) {a b : R}
    (h : MulAut.conj a = MulAut.conj b) : a = b := by
  have hmem : b⁻¹ * a ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hy : a * y * a⁻¹ = b * y * b⁻¹ := by
      simpa [MulAut.conj_apply] using DFunLike.congr_fun h y
    calc y * (b⁻¹ * a) = b⁻¹ * (b * y * b⁻¹) * a := by group
      _ = b⁻¹ * (a * y * a⁻¹) * a := by rw [hy]
      _ = (b⁻¹ * a) * y := by group
  rw [hC, Subgroup.mem_bot] at hmem
  exact (inv_mul_eq_one.mp hmem).symm

theorem internalTransfer_holds :
    internalTransfer := by
  intro G instG instFin p B Bs x L D J hS R instR θ hN hxL hT hI j hjL hjC hjP
  have hp3 : p = 3 := ggQ2_pThree hS
  subst hp3
  have hLperf : commutator L = ⊤ :=
    (isQuasisimple_of_largeEvenMarking (K := L) hS.2.1).1
  have hCR : Subgroup.center R = ⊥ := ggQ2Cent_center_eq_bot hLperf θ
  obtain ⟨jL, rfl⟩ : ∃ jL : L, (jL : G) = j := ⟨⟨j, hjL⟩, rfl⟩
  let q : L →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  obtain ⟨m, hm⟩ := hjP.exists_card_eq
  have hjo : orderOf (jL : G) = 3 ^ m := by
    rw [← Nat.card_zpowers]
    exact hm
  have hjm : (jL : G) ^ 3 ^ m = 1 := by
    rw [← hjo]
    exact pow_orderOf_eq_one _
  have hLpow : jL ^ 3 ^ m = 1 := Subtype.ext (by simpa using hjm)
  have hrpow : q jL ^ 3 ^ m = 1 := by
    rw [← map_pow, hLpow, map_one]
  have hrP : IsPGroup 3 (Subgroup.zpowers (q jL)) := ggQ2Cent_isPGroup_zpowers_three hrpow
  have hfix : ∀ a ∈ (ggBeta L θ hN).range, a (q jL) = q jL := by
    rintro a ⟨b, rfl⟩
    have hbj : (b : G) * (jL : G) * (b : G)⁻¹ = (jL : G) := by
      have hcomm : (b : G) * (jL : G) = (jL : G) * (b : G) :=
        Subgroup.mem_centralizer_iff.mp hjC (b : G) b.2
      rw [hcomm]
      group
    have hLeq : L.normalizerMonoidHom ⟨b, hN b.2⟩ jL = jL := by
      apply Subtype.ext
      rw [normalizerMonoidHom_coe]
      exact hbj
    change ggBeta L θ hN b (θ (jL : L ⧸ Subgroup.center L)) = θ (jL : L ⧸ Subgroup.center L)
    rw [ggBeta_eq, ggLAut_apply, hLeq]
  have hA : MulAut.conj (q jL) ∈ (ggBeta L θ hN).range := hT (q jL) hfix hrP
  obtain ⟨U, hUel, hUBs, hUmap, hUcent⟩ := hI
  have hconj : MulAut.conj (q jL) ∈
      (ggBeta L θ hN).range ⊓ (MulAut.conj : R →* MulAut R).range := ⟨hA, ⟨q jL, rfl⟩⟩
  rw [← hUmap] at hconj
  obtain ⟨u, hu, hueq⟩ := Subgroup.mem_map.mp hconj
  have hueq' : MulAut.conj (q u) = MulAut.conj (q jL) := hueq
  have hur : θ (QuotientGroup.mk u) = θ (QuotientGroup.mk jL) :=
    ggQ2Cent_eq_of_conj_eq hCR hueq'
  have hz0 : u⁻¹ * jL ∈ Subgroup.center L := QuotientGroup.eq.mp (θ.injective hur)
  have huBs : (u : G) ∈ Bs := Subgroup.mem_subgroupOf.mp (hUBs hu)
  have hu3 : u ^ 3 = 1 := hUel.2 u hu
  have hcomm : u * jL = jL * u := by
    apply Subtype.ext
    have h := Subgroup.mem_centralizer_iff.mp hjC (u : G) huBs
    simpa using h
  have hcm : Commute u⁻¹ jL := (show Commute u jL from hcomm).inv_left
  have hz0P : IsPGroup 3 (Subgroup.zpowers (u⁻¹ * jL)) := by
    refine ggQ2Cent_isPGroup_zpowers_three (k := m + 1) ?_
    have e1 : 3 ^ (m + 1) = 3 * 3 ^ m := pow_succ' 3 m
    have e2 : 3 ^ (m + 1) = 3 ^ m * 3 := pow_succ 3 m
    have h1 : u ^ 3 ^ (m + 1) = 1 := by
      rw [e1, pow_mul, hu3, one_pow]
    have h2 : jL ^ 3 ^ (m + 1) = 1 := by
      rw [e2, pow_mul, hLpow, one_pow]
    rw [hcm.mul_pow, inv_pow, h1, h2, inv_one, one_mul]
  have hz0U : u⁻¹ * jL ∈ U := hUcent _ hz0 hz0P
  have hjU : jL ∈ U := by
    have := U.mul_mem hu hz0U
    simpa using this
  exact Subgroup.mem_subgroupOf.mp (hUBs hjU)

end CFSG.StandardType.GGQ2CentPort

end
