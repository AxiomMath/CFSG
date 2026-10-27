module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.Claim5D
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.SevenD
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.Star

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

theorem card_Iv_p2_le_eight : Nat.card (Iv ((critPathOf C.hc).p 2)) ≤ 8 := by
  set P := critPathOf C.hc with hP
  have hb5 := C.hb5
  have hν : P.p 2 ∈ nbrs β := by
    have := P.isGeodesic.mem_nbrs_succ (i := 1) (by omega)
    rwa [P.p_one] at this
  have hν1 : P.p 3 ∈ nbrs (P.p 2) := P.isGeodesic.mem_nbrs_succ (i := 2) (by omega)
  have hvν : vtype (P.p 2) = true := vtype_true_of_mem_nbrs_false hν C.vtype_beta
  obtain ⟨y, hy, hyQ⟩ := Set.not_subset.mp C.not_Vn_alpha'_le
  have hy2 : y ^ 2 = 1 := (isElemAbelian_Vn C.hA C.hb3 α').2 y hy
  have hys : y ∈ stab β := C.Vn_alpha'_le_stab hy
  have hVst : Vn β ≤ stab β :=
    (C.Vn_le_Qv_self C.vtype_beta).trans (CFSG.Quasithin.F53B3.N37.Qv_le_stab_self β)
  have hstabN := CFSG.Quasithin.F53B3.N37.stab_le_normalizer_Cv (H := H) (M := M) β
  have hIcent : Iv (P.p 2) ≤ Subgroup.centralizer {y} := by
    intro z hz
    have hz1 : z ∈ Vn (P.p 3) := Iv_le_Vn hν1 hz
    have hd : dist (P.p 3) α' + 3 ≤ bMin H M := by
      have := P.dist_of_le (i := 3) (j := bMin H M) (by omega) le_rfl
      rw [P.p_b] at this
      omega
    have hcb := C.comm_Vn_Vn (δ := P.p 3) (δ' := α') C.vtype_alpha' hd
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have := Subgroup.commutator_mem_commutator hz1 hy
    rw [hcb, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this.symm
  obtain ⟨hN, θ, βm, -, hθk, hsd⟩ := C.exists_secData C.vtype_beta
  have hLX : F53B3.Cv β ≤ Vn β := inf_le_left
  have hAK : Subgroup.zpowers y ≤ stab β := Subgroup.zpowers_le.mpr hys
  have hmap := map_zpowers_subgroupOf hys θ
  have ht1 : θ ⟨y, hys⟩ ≠ 1 := by
    intro h1
    have : (⟨y, hys⟩ : ↥(stab β)) ∈ θ.ker := h1
    rw [hθk, Subgroup.mem_subgroupOf] at this
    exact hyQ this
  have htt : θ ⟨y, hys⟩ * θ ⟨y, hys⟩ = 1 := by
    rw [← map_mul]
    have : (⟨y, hys⟩ * ⟨y, hys⟩ : ↥(stab β)) = 1 := Subtype.ext (by simpa [pow_two] using hy2)
    rw [this, map_one]
  set F := fixSecIn (Subgroup.zpowers y) (F53B3.Cv β) (Vn β) with hF
  have hF4 : F.relIndex (Vn β) = 4 := by
    rw [hF, hsd.relIndex_fixSecIn hLX hAK, hmap]
    exact idx_nat_invol htt ht1
  have hFV : F ≤ Vn β := by
    rw [hF]; unfold fixSecIn
    rw [Subgroup.closure_le]
    exact fun x hx => hx.1
  have hCF : F53B3.Cv β ≤ F := by
    intro c hc
    refine Subgroup.subset_closure ⟨hLX hc, fun a ha => ?_⟩
    have has : a ∈ stab β := hAK ha
    have h1 := (Subgroup.mem_normalizer_iff.mp (hstabN has) c).mp hc
    exact (F53B3.Cv β).mul_mem h1 ((F53B3.Cv β).inv_mem hc)
  have hIF : Iv (P.p 2) ≤ F := by
    intro c hc
    refine Subgroup.subset_closure ⟨Iv_le_Vn (mem_nbrs_comm hν) hc, fun a ha => ?_⟩
    have hcy : Commute c y := Subgroup.mem_centralizer_singleton_iff.mp (hIcent hc)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hck : Commute c (y ^ k) := hcy.zpow_right k
    have : y ^ k * c * (y ^ k)⁻¹ * c⁻¹ = 1 := by
      rw [← hck.eq]
      group
    rw [this]
    exact one_mem _
  have hCF4 : (F53B3.Cv β).relIndex F = 4 := by
    have h := Subgroup.relIndex_mul_relIndex (F53B3.Cv β) F (Vn β) hCF hFV
    rw [hF4, C.relIndex_Cv_Vn C.vtype_beta] at h
    omega
  have hINC : Iv (P.p 2) ≤ Subgroup.normalizer ((F53B3.Cv β : Subgroup G) : Set G) := fun x hx =>
    hstabN (hVst (Iv_le_Vn (mem_nbrs_comm hν) hx))
  have hrel := relIndex_sup_eq_inf hINC
  have hle : (Iv (P.p 2) ⊔ F53B3.Cv β) ≤ F := sup_le hIF hCF
  have hm := Subgroup.relIndex_mul_relIndex (F53B3.Cv β) (Iv (P.p 2) ⊔ F53B3.Cv β) F
    le_sup_right hle
  rw [hCF4] at hm
  have hr4 : (Iv (P.p 2) ⊓ F53B3.Cv β).relIndex (Iv (P.p 2)) ≤ 4 := by
    rw [← hrel]
    exact Nat.le_of_dvd (by norm_num) (Dvd.intro _ hm)
  have hIC : Iv (P.p 2) ⊓ F53B3.Cv β = Zv β := C.Iv_inf_Cv_eq hvν (mem_nbrs_comm hν)
  have hcard := Subgroup.relIndex_mul_card (H := Iv (P.p 2) ⊓ F53B3.Cv β) (K := Iv (P.p 2))
  rw [inf_of_le_left inf_le_left, hIC, C.card_Zv_false C.vtype_beta] at hcard
  rw [hIC] at hr4
  omega

theorem card_Iv_le_eight {ν : Geo H M} (hν : vtype ν = true) : Nat.card (Iv ν) ≤ 8 := by
  have hb5 := C.hb5
  set P := critPathOf C.hc with hP
  have hβ : P.p 2 ∈ nbrs β := by
    have := P.isGeodesic.mem_nbrs_succ (i := 1) (by omega)
    rwa [P.p_one] at this
  have hvν : vtype (P.p 2) = true := vtype_true_of_mem_nbrs_false hβ C.vtype_beta
  obtain ⟨g, hg⟩ := exists_smul_of_vtype_eq (δ := P.p 2) (δ' := ν) (by rw [hν, hvν])
  rw [hg, Iv_smul_conj, card_conjSub]
  exact C.card_Iv_p2_le_eight

end Ctx

theorem ivBoundSpec : IvBoundSpec H M S := fun C _ hν => C.card_Iv_le_eight hν

theorem starSpec : StarSpec H M S := fun C _ _ hδ hμ => C.star hδ hμ

end CFSG.Quasithin.Kleidman.F53Hss36
