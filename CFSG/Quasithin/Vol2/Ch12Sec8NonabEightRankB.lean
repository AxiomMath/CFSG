module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatSix
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabEightRankA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace Hyp1281Two

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

theorem centralizerMod_VZ_le (h : Hyp1281Two G T M L) :
    centralizerMod (quasithinOmegaOneCenter T)
      (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) (VZ T M) ≤ M := by
  intro x hx
  rw [← h.normalizer_VZ]
  apply mem_normalizer_of_conj_mem_of_finite
  intro v hv
  have h1 := hx.2.2 v hv
  have e : x * v * x⁻¹ = (x * v * x⁻¹ * v⁻¹) * v := by group
  rw [e]
  exact (VZ T M).mul_mem (omegaOneCenter_le_VZ T M h1) hv

theorem mem_centralizer_VZ_of_pow_three (h : Hyp1281Two G T M L) {y : G}
    (hy : y ∈ centralizerMod (quasithinOmegaOneCenter T)
      (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) (VZ T M))
    (hy3 : y ^ 3 = 1) : y ∈ Subgroup.centralizer (VZ T M : Set G) := by
  have hyV : y ∈ Subgroup.normalizer (VZ T M : Set G) := by
    rw [h.normalizer_VZ]
    exact h.centralizerMod_VZ_le hy
  have hyZ : y ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := by
    rw [h.normalizer_Z_eq_centralizer]
    exact hy.1
  have hodd : Odd (orderOf y) :=
    Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hy3)
  exact h.mem_centralizer_of_odd hyV hyZ hodd

theorem pRank_centralizerMod_le_one (h : Hyp1281Two G T M L) :
    CFSG.Open.pRank 3 (centralizerMod (quasithinOmegaOneCenter T)
      (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) (VZ T M)) ≤ 1 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := centralizerMod (quasithinOmegaOneCenter T)
    (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) (VZ T M) with hCdef
  obtain ⟨E, hEC, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) C
  have hEM : E ≤ M := hEC.trans h.centralizerMod_VZ_le
  have hEcV : ∀ e ∈ E, e ∈ Subgroup.centralizer (VZ T M : Set G) := fun e he =>
    h.mem_centralizer_VZ_of_pow_three (hEC he) (hE.2 e he)
  have hLM : L ≤ M := h.le
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := h.normalizer_VZ.ge
  have hNorm : M ≤ Subgroup.normalizer ((L ⊓ Subgroup.centralizer (VZ T M : Set G) :
      Subgroup G) : Set G) := by
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨h.normal hx, normalizer_le_normalizer_centralizer'' _ (hMV hx)⟩
  have hN2G : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (VZ T M : Set G)) := by
    have hle : L ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ pCoreOf 2 (L ⊔ T) := by
      rw [← h.centralizer]
      exact le_inf (inf_le_left.trans le_sup_left) inf_le_right
    exact (pCoreOf_isPGroup 2 (L ⊔ T)).to_le hle
  have hN₂M : L ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ M := inf_le_left.trans hLM
  have hNnormal : ((L ⊓ Subgroup.centralizer (VZ T M : Set G)).subgroupOf M).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hNorm
  have hN2 : IsPGroup 2 ↥((L ⊓ Subgroup.centralizer (VZ T M : Set G)).subgroupOf M) :=
    hN2G.of_equiv (Subgroup.subgroupOfEquivOfLe hN₂M).symm
  obtain ⟨g, hg⟩ := h.exists_goodElt_L
  have hgM : g ∈ M := hLM hg.mem
  have hg3 : g ^ 3 ∈ L ⊓ Subgroup.centralizer (VZ T M : Set G) :=
    ⟨L.pow_mem hg.mem 3, h.pCoreOf_LT_le_centralizer (h.pow_three_mem_pCoreOf_LT hg.mem)⟩
  have hgC : g ∉ Subgroup.centralizer (VZ T M : Set G) := fun hgC =>
    hg.not_mem (by
      rw [h.normalizer_Z_eq_centralizer]
      exact Subgroup.centralizer_le (omegaOneCenter_le_VZ T M) hgC)
  have hgNV : g ∈ Subgroup.normalizer (VZ T M : Set G) := hMV hgM
  have hAc : ∀ a b : ↥E, a * b = b * a := fun a b => hE.1.is_comm.comm a b
  have hAp : ∀ a : ↥E, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hE.2 a a.2)
  have hg3' : (⟨g, hgM⟩ : ↥M) ^ 3 ∈
      (L ⊓ Subgroup.centralizer (VZ T M : Set G)).subgroupOf M := by
    rw [Subgroup.mem_subgroupOf]
    simpa using hg3
  have hcomm' : ∀ a : ↥E, Subgroup.inclusion hEM a * (⟨g, hgM⟩ : ↥M) *
      (Subgroup.inclusion hEM a)⁻¹ * (⟨g, hgM⟩ : ↥M)⁻¹ ∈
        (L ⊓ Subgroup.centralizer (VZ T M : Set G)).subgroupOf M := by
    intro a
    rw [Subgroup.mem_subgroupOf]
    show (a : G) * g * (a : G)⁻¹ * g⁻¹ ∈ L ⊓ Subgroup.centralizer (VZ T M : Set G)
    have haM : (a : G) ∈ M := hEM a.2
    have haC : (a : G) ∈ Subgroup.centralizer (VZ T M : Set G) := hEcV a a.2
    constructor
    · have h1 : (a : G) * g * (a : G)⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (h.normal haM) g).mp hg.mem
      exact L.mul_mem h1 (L.inv_mem hg.mem)
    · have h1 : g * (a : G)⁻¹ * g⁻¹ ∈ Subgroup.centralizer (VZ T M : Set G) :=
        (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer'' _ hgNV) _).mp
          ((Subgroup.centralizer (VZ T M : Set G)).inv_mem haC)
      have e : (a : G) * g * (a : G)⁻¹ * g⁻¹ = (a : G) * (g * (a : G)⁻¹ * g⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ haC h1
  have hind' : ∀ (a : ↥E) (n : ↥M),
      n ∈ (L ⊓ Subgroup.centralizer (VZ T M : Set G)).subgroupOf M → ∀ m : ℤ,
        (⟨g, hgM⟩ : ↥M) ^ m = Subgroup.inclusion hEM a * n → (3 : ℤ) ∣ m := by
    intro a n hn m hm
    by_contra h3
    have hnC : (n : G) ∈ Subgroup.centralizer (VZ T M : Set G) :=
      (Subgroup.mem_subgroupOf.mp hn).2
    have hgm : g ^ m = (a : G) * (n : G) := by
      have := congrArg (fun x : ↥M => (x : G)) hm
      simpa using this
    have hgmC : g ^ m ∈ Subgroup.centralizer (VZ T M : Set G) := by
      rw [hgm]
      exact Subgroup.mul_mem _ (hEcV a a.2) hnC
    exact hgC (mem_of_zpow_mem_of_pow_three_mem _ hg3.2 hgmC h3)
  have key := succ_le_pRank_quotient
    ((L ⊓ Subgroup.centralizer (VZ T M : Set G)).subgroupOf M) hN2 hAc hAp hEcard
    (Subgroup.inclusion hEM) (Subgroup.inclusion_injective hEM) ⟨g, hgM⟩ hg3' hcomm' hind'
  have hN3 : ¬ 3 ∣ Nat.card ↥((L ⊓ Subgroup.centralizer (VZ T M : Set G)).subgroupOf M) := by
    obtain ⟨k, hk⟩ := hN2.exists_card_eq
    rw [hk]
    intro hdvd
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd)
    omega
  have hq := CFSG.SectionRank.pRank_quotient_eq (p := 3)
    ((L ⊓ Subgroup.centralizer (VZ T M : Set G)).subgroupOf M) hN3
  have hsub : CFSG.Open.pRank 3 (⊤ : Subgroup ↥M) = CFSG.Open.pRank 3 M :=
    pRank_top_subtype (p := 3) M
  have hMcore : pCoreOf 2 M ≠ ⊥ := by
    have hVT : VZ T M ≤ T := h.isTwoReducedIn.2
    have hVp : IsPGroup 2 (VZ T M) := h.sylow.1.to_le hVT
    have hVM : VZ T M ≤ M := (Subgroup.le_normalizer (H := VZ T M)).trans h.normalizer_VZ.le
    have hVle : VZ T M ≤ pCoreOf 2 M := le_pCoreOf_of_le_normalizer 2 hVM hMV hVp
    intro hbot
    have hVne : VZ T M = ⊥ := by
      rw [eq_bot_iff]
      rw [hbot] at hVle
      exact hVle
    have h4 := h.rank_two
    rw [hVne, Subgroup.card_bot] at h4
    omega
  have h2 : CFSG.Open.pRank 3 M ≤ 2 :=
    pRank_le_two_of_pCoreOf_ne_bot h.qtke hMcore Nat.prime_three (by norm_num)
  omega

end Hyp1281Two

end CFSG.Quasithin
