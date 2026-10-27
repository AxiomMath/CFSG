module

public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootPSU
public import CFSG.GroupTheory.PerfectLeOfPGroupQuotient

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.ChevTwo CFSG.LieType.Universal CFSG.LieType.BorelTits
open CFSG.LieType.Universal.Unitary
open CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree (iotaHom)
open Subgroup

theorem ggRootInvol_exists_levi_PSU {G : Type} [Group G] [Finite G] {f k : ℕ} (hf : 1 ≤ f)
    (hk : 2 ≤ k)
    {ψ : CFSG.LieType.Universal.Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (k + 2) →* G}
    (hker : ψ.ker ≤ Subgroup.center (CFSG.LieType.Universal.Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (k + 2)))
    {r : G}
    (hr : GGRootInvolution (CFSG.LieType.Universal.Unitary.rootDatum
      (CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf) (k + 2)) .PSU ψ r) :
    ∃ h : CFSG.LieType.Universal.Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (k + 2),
      r = ψ (h * ggInvSU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * f)) 2 f)
        (k + 2) 1 * h⁻¹) ∧
      ∀ C : Subgroup (GGInvolCentBar ψ.range r), CFSG.Open.IsComponentOf C ⊤ →
        C ≤ ((ψ.comp ((MulAut.conj h).toMonoidHom.comp
              (CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.iotaHom
                (σ := CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * f)) 2 f)
                (m := k)))).range.subgroupOf
            (Subgroup.centralizer ({r} : Set G) ⊓ ψ.range)).map
          (QuotientGroup.mk' (CFSG.Open.pCore 2
            ↥(Subgroup.centralizer ({r} : Set G) ⊓ ψ.range))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let σ := unitaryInvolution (GaloisField 2 (2 * f)) 2 f
  have hF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 :=
    card_galoisField_two_mul 2 f hf
  obtain ⟨hr2, γ, ⟨-, hlong⟩, u₀, hru⟩ := hr
  obtain ⟨y, ⟨x, hx, hyx⟩, hry⟩ := hru
  have hx1 : x ≠ 1 := by
    rintro rfl
    have hy1 : y = 1 := by rw [← hyx, map_one]
    rw [← hry, hy1, map_one] at hr2
    rw [orderOf_one] at hr2
    omega
  obtain ⟨a, ha⟩ := exists_conj_ggInvSU_of_longRoot hF (hlong (Or.inl rfl)) hx hx1
  let h := u₀ * a
  let ψ' := ψ.comp (MulAut.conj h).toMonoidHom
  have hconj : h * ggInvSU σ (k + 2) 1 * h⁻¹ = (MulAut.conj u₀).toMonoidHom x := by
    change u₀ * a * ggInvSU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f)
      (k + 2) 1 * (u₀ * a)⁻¹ = (MulAut.conj u₀).toMonoidHom x
    rw [ha]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hr' : ψ' (ggInvSU σ (k + 2) 1) = r := by
    change ψ (h * ggInvSU σ (k + 2) 1 * h⁻¹) = r
    rw [hconj, hyx, hry]
  have hrange : ψ'.range = ψ.range := by
    change (ψ.comp (MulAut.conj h).toMonoidHom).range = ψ.range
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map]
  have hker' : ψ'.ker ≤ center (SU σ (k + 2)) := by
    intro v hv
    have hz : h * v * h⁻¹ ∈ center (SU σ (k + 2)) := hker hv
    have h1 := (inferInstance : (center (SU σ (k + 2))).Normal).conj_mem _ hz h⁻¹
    rwa [inv_inv, show h⁻¹ * (h * v * h⁻¹) * h = v by group] at h1
  have hQ2 : IsPGroup 2 ((RCSTSU.suRad σ k).map ψ') := RCSTSU.suRad_isPGroup.map ψ'
  have hQX : (RCSTSU.suRad σ k).map ψ' ≤
      ggRCSX ψ'.range (ψ' (ggInvSU σ (k + 2) 1)) :=
    ggRCST_map_le_ggRCSX_of_isPGroup ψ' (RCSTSU.suRad_le_centralizer (k := k))
      RCSTSU.suRad_isPGroup
  have hXQ : ggRCSX ψ'.range (ψ' (ggInvSU σ (k + 2) 1)) ≤
      normalizer (((RCSTSU.suRad σ k).map ψ') : Set G) :=
    ggRCST_ggRCSX_le_normalizer hker' (RCSTSU.hZ_su _) RCSTSU.ggInvSU_mul_self
      (RCSTSU.centralizer_le_normalizer_suRad (σ := σ) (k := k))
  have hL₀X : (ψ'.comp (iotaHom (σ := σ) (m := k))).range ≤
      ggRCSX ψ'.range (ψ' (ggInvSU σ (k + 2) 1)) :=
    ggRCST_range_le_ggRCSX ψ' iotaHom RCSTSU.range_iotaHom_le_centralizer
      (RootCentSU.top_le_closure_SU hF (by omega))
  have hXle := RCSTSU.ggRCSX_le_sup hf ψ' hker'
  have hXeq : ggRCSX ψ'.range (ψ' (ggInvSU σ (k + 2) 1)) =
      (RCSTSU.suRad σ k).map ψ' ⊔ (ψ'.comp (iotaHom (σ := σ) (m := k))).range :=
    le_antisymm hXle (sup_le hQX hL₀X)
  let Q : Subgroup G := (RCSTSU.suRad σ k).map ψ'
  let L₀ : Subgroup G := (ψ'.comp (iotaHom (σ := σ) (m := k))).range
  have hXeq' : ggRCSX ψ.range r = Q ⊔ L₀ := by
    change ggRCSX ψ.range r = (RCSTSU.suRad σ k).map ψ' ⊔
      (ψ'.comp (iotaHom (σ := σ) (m := k))).range
    rw [← hrange, ← hr']
    exact hXeq
  let V : Subgroup G := Subgroup.centralizer ({r} : Set G) ⊓ ψ.range
  let N : Subgroup G := ggRCSX ψ.range r
  have hQN : Q ≤ N := by
    change Q ≤ ggRCSX ψ.range r
    rw [hXeq']
    exact le_sup_left
  have hL₀N : L₀ ≤ N := by
    change L₀ ≤ ggRCSX ψ.range r
    rw [hXeq']
    exact le_sup_right
  have hNV : N ≤ V := by
    change ggRCSX ψ.range r ≤ Subgroup.centralizer ({r} : Set G) ⊓ ψ.range
    rw [show ggRCSX ψ.range r = ggOTwoPrime (ψ.range ⊓ Subgroup.centralizer {r}) from rfl,
      inf_comm]
    exact ggOTwoPrime_le _
  have hQV : Q ≤ V := hQN.trans hNV
  have hL₀V : L₀ ≤ V := hL₀N.trans hNV
  have hXQ' : N ≤ Subgroup.normalizer (Q : Set G) := by
    change ggRCSX ψ.range r ≤ Subgroup.normalizer (Q : Set G)
    rw [← hrange, ← hr']
    exact hXQ
  have hNnormal : (N.subgroupOf V).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNV]
    intro v hv
    have hvY : v ∈ ψ.range ⊓ Subgroup.centralizer ({r} : Set G) := by
      rw [inf_comm]
      exact hv
    exact ggMem_normalizer_oTwoPrime (Subgroup.le_normalizer hvY)
  let Nv : Subgroup ↥V := N.subgroupOf V
  let O : Subgroup ↥V := CFSG.Open.pCore 2 ↥V
  let π : ↥V →* (↥V ⧸ O) := QuotientGroup.mk' O
  haveI hNvN : Nv.Normal := hNnormal
  let e : ↥Nv ≃* ↥N := Subgroup.subgroupOfEquivOfLe hNV
  have hQNsub : Q ≤ N := hQN
  have hQNnormal : (Q.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQNsub).2 hXQ'
  have hQN2 : IsPGroup 2 ↥(Q.subgroupOf N) :=
    hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQNsub).symm
  have hQpN : Q.subgroupOf N ≤ CFSG.Open.pCore 2 ↥N :=
    le_sSup ⟨hQNnormal, hQN2⟩
  have hcomap : Subgroup.comap e.toMonoidHom (Q.subgroupOf N) =
      (Q.subgroupOf V).subgroupOf Nv := by
    ext z
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf]
    rfl
  have hQpNv : (Q.subgroupOf V).subgroupOf Nv ≤ CFSG.Open.pCore 2 ↥Nv := by
    rw [← hcomap]
    calc Subgroup.comap e.toMonoidHom (Q.subgroupOf N)
        ≤ Subgroup.comap e.toMonoidHom (CFSG.Open.pCore 2 ↥N) :=
          Subgroup.comap_mono hQpN
      _ = Subgroup.comap e.toMonoidHom ((CFSG.Open.pCore 2 ↥Nv).map e.toMonoidHom) := by
          rw [pCore_map_iso]
      _ = CFSG.Open.pCore 2 ↥Nv := Subgroup.comap_map_eq_self_of_injective e.injective _
  have hHv_normal : ((CFSG.Open.pCore 2 ↥Nv).map Nv.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hHv_2 : IsPGroup 2 ↥((CFSG.Open.pCore 2 ↥Nv).map Nv.subtype) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥Nv)).map Nv.subtype
  have hQvNv : Q.subgroupOf V ≤ Nv := Subgroup.subgroupOf_mono V hQN
  have hQvO : Q.subgroupOf V ≤ O := by
    change Q.subgroupOf V ≤ CFSG.Open.pCore 2 ↥V
    have h1 : Q.subgroupOf V ≤ (CFSG.Open.pCore 2 ↥Nv).map Nv.subtype := by
      calc Q.subgroupOf V = ((Q.subgroupOf V).subgroupOf Nv).map Nv.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hQvNv).symm
        _ ≤ _ := Subgroup.map_mono hQpNv
    exact h1.trans (le_sSup ⟨hHv_normal, hHv_2⟩)
  have hQmap : (Q.subgroupOf V).map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hQvO
  have hNsup : N.subgroupOf V = Q.subgroupOf V ⊔ L₀.subgroupOf V := by
    change (ggRCSX ψ.range r).subgroupOf V = Q.subgroupOf V ⊔ L₀.subgroupOf V
    rw [hXeq', Subgroup.subgroupOf_sup hQV hL₀V]
  have hMmap : (N.subgroupOf V).map π = (L₀.subgroupOf V).map π := by
    rw [hNsup, Subgroup.map_sup, hQmap, bot_sup_eq]
  have hgen_le : ggOTwoPrime V ≤ N := by
    change ggOTwoPrime (Subgroup.centralizer ({r} : Set G) ⊓ ψ.range) ≤
      ggOTwoPrime (ψ.range ⊓ Subgroup.centralizer ({r} : Set G))
    rw [inf_comm]
  have hodd_order : ∀ z : ↥V ⧸ Nv, Odd (orderOf z) := by
    intro z
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective Nv z
    obtain ⟨m₀, m, hm, horder⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos v).ne'
    have hvm : ((v : G) ^ m) ∈ ggOTwoPrime V := by
      refine Subgroup.subset_closure ⟨V.pow_mem v.2 m, m₀, ?_⟩
      rw [← pow_mul, mul_comm m (2 ^ m₀), ← horder, ← Subgroup.orderOf_coe v,
        pow_orderOf_eq_one]
    have hz : (QuotientGroup.mk' Nv v) ^ m = 1 := by
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr (hgen_le hvm)
    exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hz)
  have hodd : Odd (Nat.card (↥V ⧸ Nv)) := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 (Even.two_dvd heven)
    have hzodd := hodd_order z
    rw [hz] at hzodd
    exact (by norm_num : ¬ Odd 2) hzodd
  have hVNsolv : Group.IsSolvable (↥V ⧸ Nv) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  let f : ↥Nv →* (↥V ⧸ O) := π.comp Nv.subtype
  have hfrange : f.range = (N.subgroupOf V).map π := by
    change (π.comp Nv.subtype).range = (N.subgroupOf V).map π
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hMnormal : ((N.subgroupOf V).map π).Normal :=
    hNvN.map π (QuotientGroup.mk'_surjective O)
  haveI hfrange_normal : f.range.Normal := hfrange ▸ hMnormal
  have hsolv : Group.IsSolvable (↥V ⧸ (Nv ⊔ O)) := by
    have hmap : Function.Surjective (QuotientGroup.map Nv (Nv ⊔ O) (MonoidHom.id ↥V)
        (by simpa using (show Nv ≤ Nv ⊔ O from fun z hz => Subgroup.mem_sup_left hz))) := by
      intro z
      obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (Nv ⊔ O) z
      refine ⟨QuotientGroup.mk' Nv v, ?_⟩
      rw [QuotientGroup.map_mk']
      rfl
    haveI : Group.IsSolvable (↥V ⧸ Nv) := hVNsolv
    exact Group.isSolvable_of_surjective hmap
  have hquot : Group.IsSolvable ((↥V ⧸ O) ⧸ f.range) := by
    have hker : Nv ⊔ O ≤ Subgroup.comap (QuotientGroup.mk' O) f.range := by
      intro z hz
      obtain ⟨n, hn, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hz
      have hn' : QuotientGroup.mk' O n ∈ f.range := by
        rw [hfrange]
        exact Subgroup.mem_map_of_mem (QuotientGroup.mk' O) hn
      have ho' : QuotientGroup.mk' O o = 1 := (QuotientGroup.eq_one_iff o).2 ho
      change QuotientGroup.mk' O (n * o) ∈ f.range
      rw [map_mul, ho', mul_one]
      exact hn'
    let φ : (↥V ⧸ (Nv ⊔ O)) →* ((↥V ⧸ O) ⧸ f.range) :=
      QuotientGroup.map (Nv ⊔ O) f.range (QuotientGroup.mk' O) hker
    have hφ : Function.Surjective φ := by
      intro z
      obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective f.range z
      obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective O w
      refine ⟨QuotientGroup.mk' (Nv ⊔ O) v, ?_⟩
      exact QuotientGroup.map_mk' (Nv ⊔ O) f.range (QuotientGroup.mk' O) hker v
    haveI : Group.IsSolvable (↥V ⧸ (Nv ⊔ O)) := hsolv
    exact Group.isSolvable_of_surjective hφ
  have hMsolv : Group.IsSolvable ((↥V ⧸ O) ⧸ (N.subgroupOf V).map π) := by
    let e := QuotientGroup.quotientMulEquivOfEq hfrange
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  haveI hMn : ((N.subgroupOf V).map π).Normal := hMnormal
  haveI hMs : Group.IsSolvable ((↥V ⧸ O) ⧸ (N.subgroupOf V).map π) := hMsolv
  have hMcomp : ∀ C : Subgroup (GGInvolCentBar ψ.range r), CFSG.Open.IsComponentOf C ⊤ →
      C ≤ (N.subgroupOf V).map π := by
    intro C hC
    have hperf : ⁅C, C⁆ = C := Subgroup.isPerfect_iff.mp ⟨hC.2.2.1⟩
    exact Subgroup.le_of_commutator_eq_self_of_isSolvable_quotient (M :=
      (N.subgroupOf V).map π) (H := C) hperf
  refine ⟨h, hr'.symm, ?_⟩
  intro C hC
  have h1 := hMcomp C hC
  rw [hMmap] at h1
  exact h1

end CFSG.StandardType
