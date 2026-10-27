module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.F1Models
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rl
import CFSG.LocalAnalysis.UniquenessCase.UC22S13d
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Facts13
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyFive
import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.LocalOfData
import CFSG.Quasithin.Background.F1Basic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.Shape
import TauCeti.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem rho1_incl_eq_conj {K R : Subgroup G}
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) (k : ↥K) :
    uc22p22rRho1 K R hRK ⟨k, Subgroup.mem_sup_left k.2⟩ =
      MulAut.conj (QuotientGroup.mk k : Bar2 K) := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective x
  have h : (uc22p22rRho0 K R hRK ⟨k, Subgroup.mem_sup_left k.2⟩ k' : ↥K) = k * k' * k⁻¹ :=
    Subtype.ext (uc22p22rRho0_apply hRK ⟨k, Subgroup.mem_sup_left k.2⟩ k')
  rw [uc22p22rRho1_mk, h, MulAut.conj_apply]
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]

private theorem rho1_inclR_mem_conj_range {K R : Subgroup G}
    {n : ℕ} (hSz : IsSz (Bar2 K) n) (hR : IsPGroup 2 R)
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) (r : ↥R) :
    uc22p22rRho1 K R hRK ⟨r, Subgroup.mem_sup_right r.2⟩ ∈
      (MulAut.conj : Bar2 K →* MulAut (Bar2 K)).range := by
  obtain ⟨m, hm⟩ := hR r
  have hodd : Odd n := (CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_odd_three_le_of_isSz hSz).1
  refine uc22s13d_inner_of_two (T := Bar2 K) (n := n) (Or.inr hSz) hodd
    (uc22p22rRho1 K R hRK ⟨r, Subgroup.mem_sup_right r.2⟩) (k := m) ?_
  have hr1 : (⟨r, Subgroup.mem_sup_right r.2⟩ : ↥(K ⊔ R)) ^ (2 ^ m) = 1 :=
    Subtype.ext (congrArg (fun x : ↥R => (x : G)) hm)
  rw [← map_pow, hr1, map_one]

private theorem rho1_range_le_conj_range {K R : Subgroup G}
    {n : ℕ} (hSz : IsSz (Bar2 K) n) (hR : IsPGroup 2 R)
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) :
    (uc22p22rRho1 K R hRK).range ≤
      (MulAut.conj : Bar2 K →* MulAut (Bar2 K)).range := by
  rintro _ ⟨h, rfl⟩
  obtain ⟨k, hk, r, hr, hkr⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hRK).1 h.2
  have hh : h = ⟨k, Subgroup.mem_sup_left hk⟩ * ⟨r, Subgroup.mem_sup_right hr⟩ :=
    Subtype.ext (by simpa using hkr)
  rw [hh, map_mul]
  refine Subgroup.mul_mem _ ?_ (rho1_inclR_mem_conj_range hSz hR hRK ⟨r, hr⟩)
  have h1 : uc22p22rRho1 K R hRK ⟨k, Subgroup.mem_sup_left hk⟩ =
      MulAut.conj (QuotientGroup.mk (⟨k, hk⟩ : ↥K)) :=
    rho1_incl_eq_conj hRK ⟨k, hk⟩
  rw [h1]
  exact MonoidHom.mem_range.2 ⟨_, rfl⟩

theorem nonempty_oTwoQuot_sup_mulEquiv {K R : Subgroup G} {n : ℕ}
    (hSz : IsSz (Bar2 K) n) (hR : IsPGroup 2 R) (hRK : R ≤ normalizer (K : Set G)) :
    Nonempty (CFSG.Quasithin.oTwoQuot ↥(K ⊔ R) ≃* Bar2 K) := by
  classical
  let H : Subgroup G := K ⊔ R
  have hHnorm : H ≤ Subgroup.normalizer (K : Set G) :=
    sup_le Subgroup.le_normalizer hRK
  have hKH : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_left : K ≤ H)).2 hHnorm
  let incl : ↥K →* ↥H := Subgroup.inclusion (le_sup_left : K ≤ H)
  let ρ : ↥H →* MulAut (Bar2 K) := uc22p22rRho1 K R hRK
  have hρrange : ρ.range ≤ (MulAut.conj : Bar2 K →* MulAut (Bar2 K)).range :=
    rho1_range_le_conj_range hSz hR hRK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcenter : Subgroup.center (Bar2 K) = ⊥ := center_eq_bot_of_isSz hSz
  have hconj : Function.Injective (MulAut.conj : Bar2 K →* MulAut (Bar2 K)) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxc : x ∈ Subgroup.center (Bar2 K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 := DFunLike.congr_fun hx y
      rw [MulAut.conj_apply, MulAut.one_apply] at h1
      calc y * x = x * y * x⁻¹ * x * 1 := by rw [h1]; group
        _ = x * y := by group
    rwa [hcenter, Subgroup.mem_bot] at hxc
  let e : Bar2 K ≃* (MulAut.conj : Bar2 K →* MulAut (Bar2 K)).range :=
    MonoidHom.ofInjective hconj
  let ρ' : ↥H →* (MulAut.conj : Bar2 K →* MulAut (Bar2 K)).range :=
    ρ.codRestrict _ fun h => hρrange (MonoidHom.mem_range.2 ⟨h, rfl⟩)
  let ψ : ↥H →* Bar2 K := e.symm.toMonoidHom.comp ρ'
  have hψ_incl : ∀ k : ↥K, ψ (incl k) = QuotientGroup.mk k := by
    intro k
    refine hconj ?_
    change MulAut.conj (e.symm (ρ' (incl k))) = MulAut.conj (QuotientGroup.mk k)
    rw [MonoidHom.apply_ofInjective_symm]
    rw [show (ρ' (incl k) : MulAut (Bar2 K)) = ρ (incl k) from rfl]
    exact rho1_incl_eq_conj hRK k
  have hψ_surj : Function.Surjective ψ := by
    intro x
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨incl k, hψ_incl k⟩
  let K' : Subgroup ↥H := K.subgroupOf H
  let pcmap : Subgroup ↥H := (CFSG.pCore 2 ↥K).map incl
  let C : Subgroup ↥H := ψ.ker
  have hCK : C ⊓ K' = pcmap := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, rfl⟩ : ∃ k : ↥K, incl k = x :=
        ⟨⟨(x : G), hx.2⟩, Subtype.ext rfl⟩
      have hψk : ψ (incl k) = 1 := hx.1
      have hk : k ∈ CFSG.pCore 2 ↥K := by
        rw [← QuotientGroup.eq_one_iff, ← hψ_incl k]
        exact hψk
      exact Subgroup.mem_map.2 ⟨k, hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      refine ⟨?_, k.2⟩
      change ψ (incl k) = 1
      rw [hψ_incl]
      exact (QuotientGroup.eq_one_iff k).2 hk
  have hHquot : IsPGroup 2 (↥H ⧸ K') := by
    let inclR : ↥R →* ↥H := Subgroup.inclusion (le_sup_right : R ≤ H)
    let φR : ↥R →* (↥H ⧸ K') := (QuotientGroup.mk' K').comp inclR
    have hφR : Function.Surjective φR := by
      intro y
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨k, hk, r, hr, hkr⟩ :=
        (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hRK).1 h.2
      refine ⟨⟨r, hr⟩, ?_⟩
      have hh : h = ⟨k, Subgroup.mem_sup_left hk⟩ * inclR ⟨r, hr⟩ :=
        Subtype.ext (by simpa [inclR] using hkr)
      rw [hh]
      change QuotientGroup.mk' K' (inclR ⟨r, hr⟩) =
        QuotientGroup.mk' K' (⟨k, Subgroup.mem_sup_left hk⟩ * inclR ⟨r, hr⟩)
      have hk' : QuotientGroup.mk' K' (⟨k, Subgroup.mem_sup_left hk⟩ : ↥H) = 1 :=
        (QuotientGroup.eq_one_iff (⟨k, Subgroup.mem_sup_left hk⟩ : ↥H)).2 (by
          change k ∈ K
          exact hk)
      rw [map_mul, hk', one_mul]
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hR
    refine IsPGroup.of_card_dvd_pow (n := m) ?_
    rw [← hm]
    exact Subgroup.card_dvd_of_surjective (f := φR) hφR
  have hincl_inj : Function.Injective incl := Subgroup.inclusion_injective (le_sup_left : K ≤ H)
  have hpcmap : IsPGroup 2 ↥pcmap :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).of_equiv
      (Subgroup.equivMapOfInjective (CFSG.pCore 2 ↥K) incl hincl_inj)
  have hpcle : pcmap ≤ C := hCK ▸ inf_le_left
  have hN2 : IsPGroup 2 ↥((C ⊓ K').subgroupOf C) := by
    rw [hCK]
    exact hpcmap.of_equiv (Subgroup.subgroupOfEquivOfLe hpcle).symm
  have hCnorm : C.Normal := MonoidHom.normal_ker ψ
  have hCKnorm : (C ⊓ K').Normal := Subgroup.normal_inf_normal C K'
  have hNnorm : ((C ⊓ K').subgroupOf C).Normal := Subgroup.normal_subgroupOf
  let f : ↥C →* (↥H ⧸ K') := (QuotientGroup.mk' K').comp C.subtype
  have hfker : f.ker = (C ⊓ K').subgroupOf C := by
    ext c
    change f c = 1 ↔ c ∈ (C ⊓ K').subgroupOf C
    change (QuotientGroup.mk (c : ↥H) : ↥H ⧸ K') = 1 ↔ c ∈ (C ⊓ K').subgroupOf C
    rw [QuotientGroup.eq_one_iff]
    exact ⟨fun h => Subgroup.mem_subgroupOf.2 ⟨c.2, h⟩,
      fun h => (Subgroup.mem_subgroupOf.1 h).2⟩
  have hfrange : IsPGroup 2 ↥f.range :=
    (hHquot.of_equiv Subgroup.topEquiv.symm).to_le le_top
  have hCquot : IsPGroup 2 (↥C ⧸ (C ⊓ K').subgroupOf C) :=
    hfrange.of_equiv ((QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
      (QuotientGroup.quotientKerEquivRange f)).symm
  have hC2 : IsPGroup 2 ↥C :=
    IsPGroup.of_subgroup_of_quotient (N := (C ⊓ K').subgroupOf C) hN2 hCquot
  have hSsimple : IsSimpleGroup (Bar2 K) :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.isSimpleGroup_bar2_of_isL2_or_isSz (Or.inr hSz)
  have hSnot2 : ¬ IsPGroup 2 (Bar2 K) := by
    intro h2p
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp h2p
    have h5 := five_dvd_card_of_isSz hSz
    rw [hj] at h5
    have h52 : 5 ∣ 2 := (by norm_num : Nat.Prime 5).dvd_of_dvd_pow h5
    norm_num at h52
  have hpcore : CFSG.pCore 2 ↥H = C :=
    CFSG.EvenSporadicStandard.TwoB.pCore_eq_of_quotient_simple hCnorm hC2 hSsimple
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ_surj) hSnot2
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hpcore).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ_surj)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight
