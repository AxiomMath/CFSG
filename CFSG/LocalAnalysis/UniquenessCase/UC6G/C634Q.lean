module

public import CFSG.LocalAnalysis.UniquenessCase.UC6C634Q
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.O633Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase

open Subgroup CFSG.Open CFSG.ABGLocalTools
open scoped commutatorElement

namespace UC6G

open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

theorem commutator_U_le_pCoreOf (hZU : ⁅m.Z, m.U⁆ ≤ CFSG.Open.pCoreOf 2 m.K) :
    ∀ k ∈ m.K, ∀ u ∈ m.U, k * u * k⁻¹ * u⁻¹ ∈ CFSG.Open.pCoreOf 2 m.K := by
  have hnorm : ∀ g ∈ m.M, ∀ c ∈ CFSG.Open.pCoreOf 2 m.K, g * c * g⁻¹ ∈ CFSG.Open.pCoreOf 2 m.K := by
    intro g hg c hc
    have := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.pCore 2 ↥m.K) (m.mem_normalizer_K hg)
    exact (mem_normalizer_iff.1 this c).1 hc
  intro k hk
  induction hk using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨g, hg, z, hz, rfl⟩ := hx
    intro u hu
    have hu' : g⁻¹ * u * g⁻¹⁻¹ ∈ m.U := m.conj_U_le (m.M.inv_mem hg) u hu
    have hc : ⁅z, g⁻¹ * u * g⁻¹⁻¹⁆ ∈ CFSG.Open.pCoreOf 2 m.K :=
      hZU (Subgroup.commutator_mem_commutator hz hu')
    have := hnorm g hg _ hc
    convert this using 1
    simp only [commutatorElement_def]
    group
  | one => intro u hu; simpa using (CFSG.Open.pCoreOf 2 m.K).one_mem
  | mul x y hx hy ihx ihy =>
    intro u hu
    have h1 := hnorm x (m.K_le_M hx) _ (ihy u hu)
    have h2 := (CFSG.Open.pCoreOf 2 m.K).mul_mem h1 (ihx u hu)
    convert h2 using 1
    group
  | inv x hx ihx =>
    intro u hu
    have h1 := hnorm x⁻¹ (m.M.inv_mem (m.K_le_M hx)) _ ((CFSG.Open.pCoreOf 2 m.K).inv_mem (ihx u hu))
    convert h1 using 1
    group

theorem c634Q_of_inputs (h629 : m.C629) : m.C634Q := by
  intro hZU
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  obtain ⟨hsimple, a, b, hab⟩ := h629
  haveI hTn : (CFSG.pCore 2 ↥m.K).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hTp : IsPGroup 2 (CFSG.pCore 2 ↥m.K) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  set T : Subgroup ↥m.K := CFSG.pCore 2 ↥m.K with hT
  set P : Subgroup ↥m.K := CFSG.pPrimeCore m.r ↥m.K with hP
  have hcopT : Nat.Coprime m.r (Nat.card T) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hTp
    rw [hn]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes m.hr Nat.prime_two).2 m.d.odd)
  have hTP : T ≤ P := le_sSup ⟨hTn, hcopT⟩
  have hcomm : ∀ k : ↥m.K, ∀ u ∈ P, k * u * k⁻¹ * u⁻¹ ∈ T := by
    intro k u hu
    have hu' : (u : G) ∈ m.U := ⟨u, hu, rfl⟩
    obtain ⟨t, ht, hte⟩ := m.commutator_U_le_pCoreOf hZU k.1 k.2 u hu'
    have : t = k * u * k⁻¹ * u⁻¹ := Subtype.ext hte
    rwa [← this]
  have hcomm' : ∀ k : ↥m.K, ∀ u ∈ P,
      (QuotientGroup.mk k * QuotientGroup.mk u : ↥m.K ⧸ T) = QuotientGroup.mk u * QuotientGroup.mk k := by
    intro k u hu
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have := T.inv_mem (hcomm k⁻¹ u⁻¹ (P.inv_mem hu))
    convert this using 1
    group
  let ψ : (↥m.K ⧸ T) →* m.Kbar := QuotientGroup.lift T (QuotientGroup.mk' P)
    (fun t ht => (QuotientGroup.eq_one_iff t).2 (hTP ht))
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk k, rfl⟩
  have hker_le : ψ.ker ≤ center (↥m.K ⧸ T) := by
    intro x hx
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    have hkP : k ∈ P := (QuotientGroup.eq_one_iff k).1 (show ψ (QuotientGroup.mk k) = 1 from hx)
    rw [mem_center_iff]
    intro y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    exact hcomm' l k hkP
  have hcenter_le : center (↥m.K ⧸ T) ≤ ψ.ker := by
    intro z hz
    have hψz : ψ z ∈ center m.Kbar := by
      rw [mem_center_iff]
      intro w
      obtain ⟨y, rfl⟩ := hψ w
      rw [← map_mul, ← map_mul, mem_center_iff.1 hz y]
    rcases hsimple.eq_bot_or_eq_top_of_normal (center m.Kbar) with h | h
    · rw [h, Subgroup.mem_bot] at hψz
      exact hψz
    · exfalso
      have ha : a ∈ center m.Kbar := by rw [h]; trivial
      exact hab (mem_center_iff.1 ha b).symm
  have hker : ψ.ker = center (↥m.K ⧸ T) := le_antisymm hker_le hcenter_le
  refine ⟨?_, ?_⟩
  ·
    have hcK : commutator m.Kbar = ⊤ := by
      rcases hsimple.eq_bot_or_eq_top_of_normal (commutator m.Kbar) with h | h
      · exfalso
        have hm : ⁅a, b⁆ ∈ (⁅(⊤ : Subgroup m.Kbar), ⊤⁆ : Subgroup m.Kbar) :=
          Subgroup.commutator_mem_commutator trivial trivial
        have hm' : ⁅a, b⁆ ∈ commutator m.Kbar := hm
        rw [h, Subgroup.mem_bot] at hm'
        exact hab (commutatorElement_eq_one_iff_mul_comm.1 hm')
      · exact h
    have hcomsup : commutator ↥m.K ⊔ P = ⊤ := by
      have htopmap : (⊤ : Subgroup ↥m.K).map (QuotientGroup.mk' P) = ⊤ := by
        rw [← MonoidHom.range_eq_map]
        exact MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective P)
      have h1 := Subgroup.map_commutator (⊤ : Subgroup ↥m.K) ⊤ (QuotientGroup.mk' P)
      rw [htopmap] at h1
      have h2 : (commutator ↥m.K).map (QuotientGroup.mk' P) = ⊤ := h1.trans hcK
      have h3 := Subgroup.comap_map_eq (QuotientGroup.mk' P) (commutator ↥m.K)
      rw [h2, Subgroup.comap_top, QuotientGroup.ker_mk'] at h3
      exact h3.symm
    let ab : ↥m.K →* Abelianization (↥m.K ⧸ T) := (Abelianization.of).comp (QuotientGroup.mk' T)
    have htop : (Subgroup.closure (((↑) : ↥m.K → G) ⁻¹'
        {x | ∃ g ∈ m.M, ∃ z ∈ m.Z, x = g * z * g⁻¹}) : Subgroup ↥m.K) = ⊤ :=
      Subgroup.closure_closure_coe_preimage
    have hpow : ∀ k : ↥m.K, ab k ^ m.r = 1 := by
      intro k
      have hk : k ∈ Subgroup.closure (((↑) : ↥m.K → G) ⁻¹'
          {x | ∃ g ∈ m.M, ∃ z ∈ m.Z, x = g * z * g⁻¹}) := by rw [htop]; trivial
      induction hk using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨g, hg, z, hz, hxe⟩ := hx
        have hz1 : z ^ m.r = 1 :=
          orderOf_dvd_iff_pow_eq_one.1 (m.card_Z ▸ Subgroup.orderOf_dvd_natCard m.Z hz)
        have hx1 : x ^ m.r = 1 := Subtype.ext (by
          rw [Subgroup.coe_pow, hxe, conj_pow, hz1]; simp)
        rw [← map_pow, hx1, map_one]
      | one => simp
      | mul x y _ _ hx hy => rw [map_mul, mul_pow, hx, hy, one_mul]
      | inv x _ hx => rw [map_inv, inv_pow, hx, inv_one]
    have hcopP : Nat.Coprime m.r (Nat.card P) := CFSG.pPrimeCore_coprime_card
    have hab1 : ∀ k : ↥m.K, ab k = 1 := by
      intro k
      have hk : k ∈ commutator ↥m.K ⊔ P := by rw [hcomsup]; trivial
      obtain ⟨c, hc, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hk
      have hc1 : ab c = 1 := Abelianization.commutator_subset_ker ab hc
      have hu1 : ab u = 1 := by
        have h1 : orderOf (ab u) ∣ m.r := orderOf_dvd_of_pow_eq_one (hpow u)
        have h2 : orderOf (ab u) ∣ Nat.card P :=
          (orderOf_map_dvd ab u).trans (Subgroup.orderOf_dvd_natCard P hu)
        have hg : orderOf (ab u) ∣ Nat.gcd m.r (Nat.card P) := Nat.dvd_gcd h1 h2
        rw [hcopP.gcd_eq_one] at hg
        exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hg)
      rw [map_mul, hc1, hu1, one_mul]
    rw [eq_top_iff]
    intro x _
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    have : Abelianization.of (QuotientGroup.mk k : ↥m.K ⧸ T) = 1 := hab1 k
    rw [← Abelianization.ker_of]
    exact this
  ·
    haveI := hsimple
    exact isSimpleGroup_of_mulEquiv_uc6
      ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ))

end Mz614

end UC6G

end CFSG.LocalAnalysis.UniquenessCase
