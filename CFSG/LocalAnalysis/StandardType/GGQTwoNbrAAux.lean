module

public import CFSG.LocalAnalysis.StandardType.GGQTwoFrameLDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrontMData
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMPrimeCBase
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCover
import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Lift

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.ClassicalInvolution.Phan

variable {G : Type} [Group G] [Finite G]

theorem qTwoNbrA_exists_y {B Bs L D J : Subgroup G} {x : G} (hT : GGThmIHyp 3 B x L)
    (hBs : GGBstar 3 B Bs) (hstd : LargeEvenStdSub 3 B x L D J) :
    ∃ y ∈ Bs, y ∉ Subgroup.zpowers x ∧ y ^ 3 = 1 ∧
      IsComponentOf J (L ⊓ Subgroup.centralizer ({y} : Set G)) := by
  obtain ⟨hDB, hDe, hDc, hxD, -, hJcomp, -⟩ := hstd.1
  obtain ⟨y, hyD, hyx⟩ := qTwoFrontM_exists_y hDe hDc hxD
  have hyB : y ∈ B := hDB hyD
  have hyBs : y ∈ Bs := hBs.1 hyB
  have hy3 : y ^ 3 = 1 := hDe.2 y hyD
  have hx3 : x ^ 3 = 1 := hDe.2 x hxD
  have hx1 : x ≠ 1 := hT.2.2.2.2.2.2.1.2.2.1
  have hxcard : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  let H : Subgroup G := Subgroup.zpowers x ⊔ Subgroup.zpowers y
  have hle_sup : H ≤ D := by
    change Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ D
    exact sup_le (Subgroup.zpowers_le.mpr hxD) (Subgroup.zpowers_le.mpr hyD)
  have hlt : Subgroup.zpowers x < H := by
    rw [lt_iff_le_and_ne]
    refine ⟨?_, ?_⟩
    · change Subgroup.zpowers x ≤ Subgroup.zpowers x ⊔ Subgroup.zpowers y
      exact le_sup_left
    · intro heq
      have hy_mem : y ∈ Subgroup.zpowers x := by
        rw [heq]
        change y ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
      exact hyx hy_mem
  have hsup_card_gt3 : 3 < Nat.card H := by
    have h := Subgroup.card_lt_of_lt hlt
    rw [hxcard] at h
    exact h
  have hsup_card : Nat.card H = 9 := by
    have hdvd : Nat.card H ∣ 3 ^ 2 := by
      rw [← hDc]
      exact Subgroup.card_dvd_of_le hle_sup
    rw [Nat.dvd_prime_pow Nat.prime_three] at hdvd
    obtain ⟨k, hk_le, hk_eq⟩ := hdvd
    have hgt : 3 < 3 ^ k := by rw [← hk_eq]; exact hsup_card_gt3
    have hk_gt1 : 1 < k := by
      by_contra h
      have hk_le1 : k ≤ 1 := by omega
      interval_cases k <;> norm_num at hgt
    have hk2 : k = 2 := by omega
    rw [hk2] at hk_eq
    simpa using hk_eq
  have hle_card : Nat.card D ≤ Nat.card H := by
    rw [hDc, hsup_card]
    norm_num
  have hD_eq : D = H := (Subgroup.eq_of_le_of_card_ge hle_sup hle_card).symm
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hT.2.2.2.2.2.2.1.2.2.2.1.1
  have h_eq : L ⊓ Subgroup.centralizer (H : Set G) = L ⊓ Subgroup.centralizer ({y} : Set G) := by
    change L ⊓ Subgroup.centralizer
      ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) : Set G) =
      L ⊓ Subgroup.centralizer ({y} : Set G)
    exact inf_centralizer_sup_zpowers hLx
  rw [hD_eq, h_eq] at hJcomp
  exact ⟨y, hyBs, hyx, hy3, hJcomp⟩

theorem qTwoNbrA_rho_ne_one {B Bs L : Subgroup G} {x : G} (hT : GGThmIHyp 3 B x L)
    (hBs : GGBstar 3 B Bs) (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {L0 : Type} [Group L0]
    (c : ↥L →* L0) (hc_surj : Function.Surjective c) (hc_ker : c.ker ≤ Subgroup.center ↥L)
    (ρ : ↥Bs →* MulAut L0)
    (hρ : ∀ (b : ↥Bs) (l : ↥L), c (ggGamma L hN b l) = ρ b (c l)) {y : G} (hy : y ∈ Bs)
    (hyx : y ∉ Subgroup.zpowers x) : ρ ⟨y, hy⟩ ≠ 1 := by
  intro h1
  have hperfect : commutator ↥L = ⊤ := qTwoLMFrameC_perfect hT
  have ha1 : ggGamma L hN ⟨y, hy⟩ = 1 :=
    (SCFourCover.induced_eq_one_iff (ψ := c) hc_surj hc_ker hperfect
      (fun l => (hρ _ l).symm)).mp h1
  have hyC : y ∈ Subgroup.centralizer (L : Set G) :=
    (ggGamma_eq_one_iff L hN ⟨y, hy⟩).mp ha1
  have hy_inf : y ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := ⟨hy, hyC⟩
  have hker := qTwoLMPrimeC_ker hT hBs
  rw [hker] at hy_inf
  exact hyx hy_inf

theorem qTwoNbrA_image_isComponentOf {Bs L J : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {L0 : Type} [Group L0] (c : ↥L →* L0)
    (hc_surj : Function.Surjective c) (hc_ker : c.ker ≤ Subgroup.center ↥L)
    (ρ : ↥Bs →* MulAut L0)
    (hρ : ∀ (b : ↥Bs) (l : ↥L), c (ggGamma L hN b l) = ρ b (c l)) {y : G} (hy : y ∈ Bs)
    (hJ : IsComponentOf J (L ⊓ Subgroup.centralizer ({y} : Set G))) :
    IsComponentOf ((J.comap L.subtype).map c) (ggFix (ρ ⟨y, hy⟩)) := by
  have hmap_eq := map_ggFix_ggGamma L hN ⟨y, hy⟩
  rw [← hmap_eq] at hJ
  have hJ' : IsComponentOf (J.comap L.subtype) (ggFix (ggGamma L hN ⟨y, hy⟩)) :=
    (isComponentOf_comap_of_injective L.subtype Subtype.val_injective hJ).1
  have hperfect : ⁅J.comap L.subtype, J.comap L.subtype⁆ = J.comap L.subtype :=
    SCFourCover.commutator_eq_self_of_isComponentOf hJ'
  exact (SCFourCover.isComponentOf_map_iff hc_surj hc_ker
    (fun l => (hρ _ l).symm) hperfect).1 hJ'

theorem qTwoNbrA_center_quot_of_component {L J N : Subgroup G} (hJL : J ≤ L) {L0 : Type}
    [Group L0] (c : ↥L →* L0) (hc_ker : c.ker ≤ Subgroup.center ↥L) (hJ : IsComponentOf J N) :
    Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
      ↥((J.comap L.subtype).map c) ⧸ Subgroup.center ↥((J.comap L.subtype).map c)) ∧
      Nat.card ↥((J.comap L.subtype).map c) ∣ Nat.card ↥J := by
  let M : Subgroup L0 := (J.comap L.subtype).map c
  let f : ↥J →* ↥M := MonoidHom.codRestrict (c.comp (Subgroup.inclusion hJL)) M (fun j => by
    refine Subgroup.mem_map.mpr ⟨Subgroup.inclusion hJL j, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    simpa using j.2)
  have hf_surj : Function.Surjective f := by
    intro m
    obtain ⟨x, hx_mem, hx_eq⟩ := Subgroup.mem_map.mp m.2
    refine ⟨⟨↑x, Subgroup.mem_comap.mp hx_mem⟩, ?_⟩
    ext
    change c ((Subgroup.inclusion hJL) ⟨↑x, Subgroup.mem_comap.mp hx_mem⟩) = ↑m
    have hx_incl : Subgroup.inclusion hJL ⟨↑x, Subgroup.mem_comap.mp hx_mem⟩ = x := by
      ext
      rfl
    rw [hx_incl, hx_eq]
  have hf_ker : f.ker ≤ Subgroup.center ↥J := by
    intro j hj
    have hj1 : f j = 1 := (MonoidHom.mem_ker).mp hj
    rw [Subgroup.mem_center_iff]
    intro j'
    have hc_eq : c (Subgroup.inclusion hJL j) = 1 := by
      have h := congrArg Subtype.val hj1
      simpa [f] using h
    have h1 : Subgroup.inclusion hJL j ∈ Subgroup.center ↥L := hc_ker hc_eq
    have h2 := Subgroup.mem_center_iff.mp h1 (Subgroup.inclusion hJL j')
    have h3 := congrArg Subtype.val h2
    exact Subtype.ext h3
  have hJ_perfect : ⁅J, J⁆ = J := SCFourCover.commutator_eq_self_of_isComponentOf hJ
  have h_iso : Nonempty (↥J ⧸ Subgroup.center ↥J ≃* ↥M ⧸ Subgroup.center ↥M) :=
    CFSG.OddStandard.HigherRank.F3.nonempty_quotient_center_equiv_of_central_cover f hf_surj
      hf_ker (Subgroup.isPerfect_iff.2 hJ_perfect)
  have h_dvd : Nat.card ↥M ∣ Nat.card ↥J := Subgroup.card_dvd_of_surjective (f := f) hf_surj
  exact ⟨h_iso, h_dvd⟩

end CFSG.StandardType.QTwo

end
