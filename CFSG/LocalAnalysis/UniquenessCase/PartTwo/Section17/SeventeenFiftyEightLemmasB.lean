module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftySeven
public import CFSG.GroupTheory.GL52.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyTwoFix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.RankThree.PartOne (pElementSubgroup)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_sup_pCoreOf_of_mem_barImage {D : Data G} {H : Subgroup G}
    {x : G} (hxM : x ∈ D.M)
    (hxbar : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨x, hxM⟩) ∈ barImage D.M H) :
    x ∈ H ⊔ pCoreOf 2 D.M := by
  rw [show barImage D.M H =
      (H.subgroupOf D.M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) from rfl] at hxbar
  obtain ⟨l, hl, hπ⟩ := Subgroup.mem_map.mp hxbar
  have hlH : (l : G) ∈ H := Subgroup.mem_subgroupOf.mp hl
  have hmemDM : (l : G)⁻¹ * x ∈ D.M := D.M.mul_mem (D.M.inv_mem l.2) hxM
  have hker : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M))
      ⟨(l : G)⁻¹ * x, hmemDM⟩ = 1 := by
    have hll : (⟨(l : G)⁻¹ * x, hmemDM⟩ : D.M) = l⁻¹ * ⟨x, hxM⟩ := rfl
    rw [hll, map_mul, map_inv, hπ, inv_mul_cancel]
  have hO2 : (l : G)⁻¹ * x ∈ pCoreOf 2 D.M := by
    have h0 : (⟨(l : G)⁻¹ * x, hmemDM⟩ : D.M) ∈ CFSG.pCore 2 ↥D.M :=
      (QuotientGroup.eq_one_iff _).mp hker
    exact Subgroup.mem_map_of_mem D.M.subtype h0
  have hxeq : x = (l : G) * ((l : G)⁻¹ * x) := by group
  rw [hxeq]
  exact Subgroup.mul_mem_sup hlH hO2

theorem mem_calC_Lp_of_dvd_card_barImage (D : Data G) {p : ℕ} (hp : Hyp1754 D p)
    (hns : s13_NormalSimple (Bar2 D.M))
    {K : Subgroup G} (hK : K ∈ calC D.M) (hdvd : p ∣ Nat.card (barImage D.M K)) :
    K ∈ calC (Lp D p) := by
  have hpp : p.Prime := (D.sig_prime p hp.1).1
  have hKM : K ≤ D.M := s13_le_of_mem_calC hK
  have hcomp : CFSG.IsComponent (barImage D.M K) := s13_barImage_isComponent hK
  have hmem : barImage D.M K ∈ s13_compsP (Bar2 D.M) p :=
    s13_mem_compsP.mpr ⟨hcomp, hdvd⟩
  have hbarle : barImage D.M K ≤ barImage D.M (Lp D p) := by
    rw [show Lp D p = F13.Lp D.M p from rfl, s13_barImage_Lp D.M hpp,
      s13_pElementSubgroup_layer_eq hns hpp]
    exact le_iSup₂ (f := fun J (_ : J ∈ s13_compsP (Bar2 D.M) p) => J) _ hmem
  have hKsup : K ≤ Lp D p ⊔ pCoreOf 2 D.M := by
    intro x hx
    exact mem_sup_pCoreOf_of_mem_barImage (hKM hx)
      (hbarle (Subgroup.mem_map_of_mem _ hx))
  have hsupM : Lp D p ⊔ pCoreOf 2 D.M ≤ D.M :=
    sup_le (Lp_le_M D p) (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)
  have hnormLp : D.M ≤ Subgroup.normalizer (Lp D p : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Lp_le_M D p)).mp (s13_Lp_normal D.M p)
  have hnormO2 : Lp D p ≤ Subgroup.normalizer (pCoreOf 2 D.M : Set G) :=
    (Lp_le_M D p).trans
      (Subgroup.le_normalizer.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 D.M))
  have hrel : (Lp D p).relIndex (Lp D p ⊔ pCoreOf 2 D.M) ∣ Nat.card (pCoreOf 2 D.M) := by
    rw [← CFSG.GroupTheory.FT63ChII.relIndex_eq_relIndex_sup_of_le_normalizer hnormO2]
    exact Subgroup.relIndex_dvd_card _ _
  have hO2p : IsPGroup 2 (pCoreOf 2 D.M) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥D.M)).map D.M.subtype
  obtain ⟨k, hk⟩ := hO2p.exists_card_eq
  rw [hk] at hrel
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hrel
  have hidx : (Lp D p).relIndex (Lp D p ⊔ pCoreOf 2 D.M) = 2 ^ j := hj
  have hKle : K ≤ Lp D p :=
    Subgroup.le_of_commutator_eq_self_of_relIndex_eq_prime_pow
      (D := Lp D p) (C := Lp D p ⊔ pCoreOf 2 D.M) (H := K) (p := 2) (k := j)
      Nat.prime_two le_sup_left (hsupM.trans hnormLp) hidx hKsup hK.2.1
  have hsub : CFSG.Open.IsSubnormal K (Lp D p) := by
    have h := CFSG.Open.IsSubnormal.inf_of_le hK.1 (Lp_le_M D p)
    rwa [inf_of_le_left hKle] at h
  exact ⟨hsub, hK.2.1, hK.2.2⟩

theorem Lp_eq_of_barImage_eq (D : Data G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hLnorm : (L.subgroupOf D.M).Normal)
    (hbar : barImage D.M (Lp D p) = barImage D.M L) : Lp D p = L := by
  have hLM : L ≤ D.M := s13_le_of_mem_calC hL
  have hLpM : Lp D p ≤ D.M := Lp_le_M D p
  have hO2M : pCoreOf 2 D.M ≤ D.M := CFSG.LieType.BorelTits.pCoreOf_le 2 D.M
  have hLp_to_sup : Lp D p ≤ L ⊔ pCoreOf 2 D.M := by
    intro x hx
    exact mem_sup_pCoreOf_of_mem_barImage (hLpM hx)
      (hbar ▸ Subgroup.mem_map_of_mem _ hx)
  have hL_to_sup : L ≤ Lp D p ⊔ pCoreOf 2 D.M := by
    intro x hx
    exact mem_sup_pCoreOf_of_mem_barImage (hLM hx)
      (hbar.symm ▸ Subgroup.mem_map_of_mem _ hx)
  have hsupM : Lp D p ⊔ pCoreOf 2 D.M ≤ D.M :=
    sup_le hLpM hO2M
  have hO2p : IsPGroup 2 (pCoreOf 2 D.M) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥D.M)).map D.M.subtype
  have hO2norm : D.M ≤ Subgroup.normalizer (pCoreOf 2 D.M : Set G) :=
    Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 D.M)
  have hLnormSup : (L.subgroupOf (L ⊔ pCoreOf 2 D.M)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr ?_
    exact (sup_le hLM hO2M).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLnorm)
  have hO2normSup : (pCoreOf 2 D.M).subgroupOf (L ⊔ pCoreOf 2 D.M) |>.Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr ?_
    exact (sup_le hLM hO2M).trans hO2norm
  have hsupH : (L.subgroupOf (L ⊔ pCoreOf 2 D.M)) ⊔
      (pCoreOf 2 D.M).subgroupOf (L ⊔ pCoreOf 2 D.M) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  let ψ : ↥((pCoreOf 2 D.M).subgroupOf (L ⊔ pCoreOf 2 D.M)) →*
      (↥(L ⊔ pCoreOf 2 D.M) ⧸ L.subgroupOf (L ⊔ pCoreOf 2 D.M)) :=
    (QuotientGroup.mk' (L.subgroupOf (L ⊔ pCoreOf 2 D.M))).comp
      (Subgroup.subtype ((pCoreOf 2 D.M).subgroupOf (L ⊔ pCoreOf 2 D.M)))
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective
      (L.subgroupOf (L ⊔ pCoreOf 2 D.M)) y
    have hx : h ∈ (L.subgroupOf (L ⊔ pCoreOf 2 D.M)) ⊔
        (pCoreOf 2 D.M).subgroupOf (L ⊔ pCoreOf 2 D.M) := by
      rw [hsupH]
      exact Subgroup.mem_top h
    obtain ⟨l, hl, o, ho, hlo⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    refine ⟨⟨o, ho⟩, ?_⟩
    have hlk : QuotientGroup.mk' (L.subgroupOf (L ⊔ pCoreOf 2 D.M)) l = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hl
    change QuotientGroup.mk' (L.subgroupOf (L ⊔ pCoreOf 2 D.M)) o =
      QuotientGroup.mk' (L.subgroupOf (L ⊔ pCoreOf 2 D.M)) h
    rw [← hlo, map_mul, hlk, one_mul]
  have hquotH2 : IsPGroup 2
      (↥(L ⊔ pCoreOf 2 D.M) ⧸ L.subgroupOf (L ⊔ pCoreOf 2 D.M)) := by
    have hO2sub : IsPGroup 2 ↥((pCoreOf 2 D.M).subgroupOf (L ⊔ pCoreOf 2 D.M)) :=
      hO2p.of_equiv (Subgroup.subgroupOfEquivOfLe le_sup_right).symm
    exact IsPGroup.of_surjective hO2sub ψ hψsurj
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have hLp_le_L : Lp D p ≤ L := by
    rw [Lp]
    show Subgroup.closure {x : G | x ∈ oTwoEOf D.M ∧ ∃ k : ℕ, orderOf x = p ^ k} ≤ L
    refine (Subgroup.closure_le L).mpr ?_
    rintro x ⟨hxE, k, hk⟩
    have hxH : x ∈ L ⊔ pCoreOf 2 D.M :=
      hLp_to_sup (Subgroup.subset_closure ⟨hxE, k, hk⟩)
    let H : Subgroup G := L ⊔ pCoreOf 2 D.M
    let P : Subgroup G := Subgroup.zpowers x
    have hPH : P ≤ H := Subgroup.zpowers_le.mpr hxH
    have hPp : IsPGroup p P :=
      IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
    have hPpH : IsPGroup p ↥(P.subgroupOf H) :=
      hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
    let φ : ↥H →* (↥H ⧸ L.subgroupOf H) := QuotientGroup.mk' (L.subgroupOf H)
    let I : Subgroup (↥H ⧸ L.subgroupOf H) := (P.subgroupOf H).map φ
    have hIp : IsPGroup p ↥I := hPpH.map φ
    have hI2 : IsPGroup 2 ↥I := hquotH2.to_subgroup I
    have hIpTop : IsPGroup p ↥(⊤ : Subgroup ↥I) :=
      hIp.of_equiv (Subgroup.topEquiv).symm
    have hI2Top : IsPGroup 2 ↥(⊤ : Subgroup ↥I) :=
      hI2.of_equiv (Subgroup.topEquiv).symm
    have hcardI : Nat.card ↥I = 1 := by
      have hcop : Nat.Coprime (Nat.card ↥(⊤ : Subgroup ↥I))
          (Nat.card ↥(⊤ : Subgroup ↥I)) :=
        IsPGroup.coprime_card_of_ne p 2 hp2 (⊤ : Subgroup ↥I) (⊤ : Subgroup ↥I)
          hIpTop hI2Top
      have h1 : Nat.card ↥(⊤ : Subgroup ↥I) = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) (dvd_refl _)
      simpa using h1
    have hIbot : I = ⊥ := Subgroup.eq_bot_of_card_eq I hcardI
    have hle : P.subgroupOf H ≤ (QuotientGroup.mk' (L.subgroupOf H)).ker :=
      (Subgroup.map_eq_bot_iff (P.subgroupOf H)).mp hIbot
    rw [QuotientGroup.ker_mk'] at hle
    have hxp : (⟨x, hxH⟩ : ↥H) ∈ P.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_zpowers x
    exact Subgroup.mem_subgroupOf.mp (hle hxp)
  have hnormO2Lp : Lp D p ≤ Subgroup.normalizer (pCoreOf 2 D.M : Set G) :=
    hLpM.trans hO2norm
  have hrel : (Lp D p).relIndex (Lp D p ⊔ pCoreOf 2 D.M) ∣ Nat.card (pCoreOf 2 D.M) := by
    rw [← CFSG.GroupTheory.FT63ChII.relIndex_eq_relIndex_sup_of_le_normalizer hnormO2Lp]
    exact Subgroup.relIndex_dvd_card _ _
  obtain ⟨n, hn⟩ := hO2p.exists_card_eq
  rw [hn] at hrel
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hrel
  have hL_eq_Lp : L ≤ Lp D p :=
    Subgroup.le_of_commutator_eq_self_of_relIndex_eq_prime_pow
      (D := Lp D p) (C := Lp D p ⊔ pCoreOf 2 D.M) (H := L) (p := 2) (k := j)
      Nat.prime_two le_sup_left (hsupM.trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hLpM).mp (s13_Lp_normal D.M p)))
      (by simpa [sup_comm] using hj) hL_to_sup hL.2.1
  exact le_antisymm hLp_le_L hL_eq_Lp

theorem Lp_ne_bot (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (h57 : R17_57At D V₀ V) (hp : Hyp1754 D p) : Lp D p ≠ ⊥ := by
  intro hbot
  have hpp : p.Prime := (D.sig_prime p hp.1).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp.1).2
  have hcent : centSection D.M (Lp D p) (pCoreOf 2 (Lp D p)) = D.M := by
    rw [hbot]
    have hbot' : pCoreOf 2 (⊥ : Subgroup G) = ⊥ := by
      rw [CFSG.Open.pCoreOf,
        Subgroup.eq_bot_of_subsingleton (CFSG.pCore 2 ↥(⊥ : Subgroup G))]
      simp
    rw [hbot', centSection_bot_bot]
  have hSp : Sp D p = Opp p D.M := by
    rw [Sp, hcent]
  have hrank : CFSG.Open.pRank p (Sp D p) = CFSG.Open.pRank p D.M := by
    rw [hSp]
    exact s13_pRank_pElementSubgroup hpp D.M
  have h3 : 3 ≤ CFSG.Open.pRank p D.M := hSg.three_le p hp.1
  have hle : CFSG.Open.pRank p (Sp D p) ≤ 1 := h57 p hp
  omega

theorem exists_component_Lp (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    (hV : Hyp125 D V₀ V) (hp : Hyp1754 D p) (hns : s13_NormalSimple (Bar2 D.M))
    {L : Subgroup G} (hL : L ∈ calC D.M) (hshape : IsL3 (Bar2 L) 2)
    (h60 : R17_60At D V₀ V)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (h57 : R17_57At D V₀ V) :
    ∃ K ∈ calC (Lp D p), K ≠ L ∧ p ∣ Nat.card (barImage D.M K) := by
  have hpp : p.Prime := (D.sig_prime p hp.1).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp.1).2
  have hLpne : Lp D p ≠ ⊥ := Lp_ne_bot D hSg h57 hp
  have hbar_ne : barImage D.M (Lp D p) ≠ barImage D.M L := by
    intro hbeq
    have hLp_eq : Lp D p = L :=
      Lp_eq_of_barImage_eq D hpp hp2 hL (hp.2 L hL).1 hbeq
    exact (h60 L p ⟨hV, hp, hL, hshape⟩) hLp_eq.symm
  have hEne : pElementSubgroup p (CFSG.layer (Bar2 D.M)) ≠ ⊥ := by
    intro hbot
    have hbar : barImage D.M (Lp D p) = ⊥ := by
      rw [show Lp D p = F13.Lp D.M p from rfl, s13_barImage_Lp D.M hpp, hbot]
    have hleO2 : Lp D p ≤ pCoreOf 2 D.M := by
      have hker : (Lp D p).subgroupOf D.M ≤
          (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)).ker := by
        rw [← Subgroup.map_eq_bot_iff]
        exact hbar
      rw [QuotientGroup.ker_mk'] at hker
      intro x hx
      have hxM : x ∈ D.M := Lp_le_M D p hx
      have hxsub : (⟨x, hxM⟩ : ↥D.M) ∈ (Lp D p).subgroupOf D.M :=
        Subgroup.mem_subgroupOf.mpr hx
      exact Subgroup.mem_map_of_mem D.M.subtype (hker hxsub)
    have hleOpp : Lp D p ≤ Opp p (pCoreOf 2 D.M) := by
      rw [Lp]
      show Subgroup.closure {x : G | x ∈ oTwoEOf D.M ∧ ∃ k : ℕ, orderOf x = p ^ k} ≤
        Opp p (pCoreOf 2 D.M)
      refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨hxE, k, hk⟩
      have hxLp : x ∈ Lp D p := Subgroup.subset_closure ⟨hxE, k, hk⟩
      exact Subgroup.subset_closure ⟨hleO2 hxLp, k, hk⟩
    rw [opp_pCoreOf_two_eq_bot hpp hp2] at hleOpp
    exact hLpne (le_bot_iff.mp hleOpp)
  let s : Finset (Subgroup (Bar2 D.M)) := s13_compsP (Bar2 D.M) p
  have hsup_eq : (⨆ J ∈ s, J) = pElementSubgroup p (CFSG.layer (Bar2 D.M)) :=
    (s13_pElementSubgroup_layer_eq hns hpp).symm
  have hsup_ne : (⨆ J ∈ s, J) ≠ ⊥ := by
    rw [hsup_eq]
    exact hEne
  have hsne : s ≠ ∅ := by
    intro h
    apply hsup_ne
    rw [h]
    simp
  obtain ⟨J0, hJ0⟩ := Finset.nonempty_iff_ne_empty.mpr hsne
  have hex : ∃ J ∈ s, J ≠ barImage D.M L := by
    by_contra h
    push Not at h
    have hsup_eq' : (⨆ J ∈ s, J) = barImage D.M L := by
      apply le_antisymm
      · apply iSup_le
        intro J
        apply iSup_le
        intro hJ
        rw [h J hJ]
      · rw [← h J0 hJ0]
        exact le_iSup₂ (f := fun J (_ : J ∈ s) => J) J0 hJ0
    have hmid : pElementSubgroup p (CFSG.layer (Bar2 D.M)) = barImage D.M L := by
      rw [← hsup_eq, hsup_eq']
    have hcontra : barImage D.M (Lp D p) = barImage D.M L := by
      rw [show Lp D p = F13.Lp D.M p from rfl, s13_barImage_Lp D.M hpp, hmid]
    exact hbar_ne hcontra
  obtain ⟨J, hJ, hJne⟩ := hex
  have hJcomp : CFSG.IsComponent J := (s13_mem_compsP.mp hJ).1
  have hJdvd : p ∣ Nat.card J := (s13_mem_compsP.mp hJ).2
  obtain ⟨K, hK, hKbar⟩ := s13_exists_calC_of_component D.M hJcomp
  have hKcalLp : K ∈ calC (Lp D p) := mem_calC_Lp_of_dvd_card_barImage D hp hns hK (hKbar ▸ hJdvd)
  refine ⟨K, hKcalLp, ?_, ?_⟩
  · intro hKL
    exact hJne (by rw [← hKbar, hKL])
  · rwa [hKbar]

theorem barImage_not_le_centralizer_of_conj (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G}
    (ctx : Ctx17_58 D V₀ V L p) (h59 : R17_59At D V₀ V) (h63 : UC6.R6_3 D)
    {X Y : Subgroup G} {g : G} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hYcard : Nat.card Y = r) (hYM : Y ≤ D.M)
    (hYeq : Y = X.map (MulAut.conj g).toMonoidHom)
    (hg : g ∉ D.M) (hCX : Subgroup.centralizer (X : Set G) ≤ D.M) :
    ¬ barImage D.M Y ≤ Subgroup.centralizer (barImage D.M L : Set (Bar2 D.M)) := by
  intro hYcent
  obtain ⟨A', hA'le, hA'syl⟩ :=
    exists_sylow_three_le_centralizer D ctx.hyp54 ctx.memC
      hr hr2 hYcard hYM hYcent
  have hA'leC : A' ≤ Subgroup.centralizer (Y : Set G) := hA'le.trans inf_le_right
  have hCYle : Subgroup.centralizer (Y : Set G) ≤
      D.M.map (MulAut.conj g).toMonoidHom := by
    rw [hYeq, CFSG.GroupTheory.GL52.centralizer_map_conj]
    exact Subgroup.map_mono hCX
  have hA'leMg : A' ≤ D.M.map (MulAut.conj g).toMonoidHom := by
    intro x hx
    exact hCYle (hA'leC hx)
  have hΓ : rankThreeGamma 1 3 A' ≤ D.M := h59 L p ctx A' hA'syl
  have hEU : UniqueMax D.M A' :=
    h63 3 Nat.prime_three (by norm_num) A'
      (hA'syl.le.trans (s13_le_of_mem_calC ctx.memC))
      (isElemAbelian_sylow_three ctx.shapeL hA'syl)
      (card_sylow_three_eq_nine ctx.shapeL hA'syl) hΓ
  have hmaxg : rankThreeIsMaxTwoLocal (D.M.map (MulAut.conj g).toMonoidHom) := by
    have := UC6.isMaxTwoLocal_conj D.maxLocal g⁻¹
    simpa [uniqueFourConj, rankThreeIsMaxTwoLocal] using this
  have hmem : D.M.map (MulAut.conj g).toMonoidHom ∈ calMOf A' := ⟨hmaxg, hA'leMg⟩
  rw [show calMOf A' = {D.M} from hEU, Set.mem_singleton_iff] at hmem
  exact hg (TwelveEight.mem_of_le_map_conj D (by rw [hmem]; exact D.sylowM.le))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
