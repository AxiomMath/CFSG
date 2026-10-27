module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoLemmaB
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTransvectionAutAll
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma5_2
public import TauCeti.Algebra.Group.Subgroup.ZPowers
public import TauCeti.GroupTheory.Sylow

public section

namespace CFSG.StandardType.USixTwo

open CFSG.Assembly CFSG.Open
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
  (coprime_card_relPPrimeCore)

open scoped Pointwise

variable {G : Type*} [Group G] {K : Type} [Field K]

namespace LocalSetting

variable {ω : K} {hω : ω ^ 2 + ω + 1 = 0} {b : G} {L : Subgroup G}
  {φ : L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))} {Bs : Subgroup G}

theorem conjEquiv_apply_inv_conj {t n : G} (htn : n⁻¹ * t * n ∈ L)
    (htM : t ∈ L.map (MulAut.conj n : G →* G)) :
    φ ⟨n⁻¹ * t * n, htn⟩ = conjEquiv φ n ⟨t, htM⟩ := by
  have hmem : n * (n⁻¹ * t * n) * n⁻¹ ∈ L.map (MulAut.conj n : G →* G) := by
    have : n * (n⁻¹ * t * n) * n⁻¹ = t := by group
    rw [this]
    exact htM
  have h := conjEquiv_apply (L := L) φ n htn hmem
  have hsub : (⟨t, htM⟩ : L.map (MulAut.conj n : G →* G)) =
      ⟨n * (n⁻¹ * t * n) * n⁻¹, hmem⟩ := by
    apply Subtype.ext
    show t = n * (n⁻¹ * t * n) * n⁻¹
    group
  rw [hsub]
  exact h.symm

theorem exists_mem_normalizer_torU [Finite G] [Finite K] (hG : IsCharTwoType G)
    (hS : LocalSetting hω b L φ Bs)
    {t : G} (ht : t ∈ Subgroup.normalizer (Bs : Set G)) (ht2 : orderOf t = 2)
    (htb : t * b * t⁻¹ = b⁻¹) (htL : t ∈ Subgroup.centralizer (L : Set G))
    {n : G} (hn : n ∈ Subgroup.normalizer (Bs : Set G)) (hnL : n * b * n⁻¹ ∈ L)
    (hnφ : φ ⟨n * b * n⁻¹, hnL⟩ = threeA hω)
    (htA : n⁻¹ * t * n ∈
      (L ⊓ Subgroup.normalizer (Bs : Set G)) ⊔ Subgroup.centralizer (Bs : Set G)) :
    ∃ htn : n⁻¹ * t * n ∈ L,
      φ ⟨n⁻¹ * t * n, htn⟩ ∈ Subgroup.normalizer
        (torU K : Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) ∧
      orderOf (φ ⟨n⁻¹ * t * n, htn⟩) = 2 ∧
      Nat.card ↥(torU K ⊓ Subgroup.centralizer {φ ⟨n⁻¹ * t * n, htn⟩}) = 3 ^ 3 := by
  classical
  set e : G := n * b * n⁻¹ with he
  set M : Subgroup G := L.map (MulAut.conj n).toMonoidHom with hM
  set φe : M ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) := conjEquiv φ n with hφe
  have hS' : LocalSetting hω e M φe Bs := hS.conj hn hnL hnφ
  have heL : e ∈ L := hnL
  have he3 : orderOf e = 3 := by
    have h := orderOf_injective (MulAut.conj n).toMonoidHom
      (MulAut.conj n).injective b
    simpa [he, MulAut.conj_apply, hS.orderOf_b] using h
  set R : Subgroup G := Subgroup.centralizer {b} ⊓ Subgroup.centralizer (L : Set G) with hR
  have htn2 : (n⁻¹ * t * n) ^ 2 = 1 := by
    have ht2' : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
    calc (n⁻¹ * t * n) ^ 2 = n⁻¹ * t ^ 2 * n := by rw [sq, sq]; group
      _ = 1 := by rw [ht2']; group
  have hxLR : n⁻¹ * t * n ∈ L ⊔ R := mem_sup_of_mem_sup_centralizer_of_sq_eq_one hS htA htn2
  have hRleCL : R ≤ Subgroup.centralizer (L : Set G) := by
    rw [hR]
    exact inf_le_right
  have hLleCR : L ≤ Subgroup.centralizer (R : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact (Subgroup.mem_centralizer_iff.mp (hRleCL hr) l hl).symm
  have hLnormR : L ≤ Subgroup.normalizer (R : Set G) :=
    hLleCR.trans (Subgroup.centralizer_le_normalizer (R : Set G))
  have hRodd : Odd (Nat.card R) := by
    rw [hR]
    exact odd_card_centralizer_inf_centralizer hG hS
  have hinfLR : L ⊓ R = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyL, hyR⟩ := Subgroup.mem_inf.mp hy
    have hyCL : y ∈ Subgroup.centralizer (L : Set G) := (Subgroup.mem_inf.mp hyR).2
    have hz : (⟨y, hyL⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro z
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hyCL z.1 z.2
    rw [center_L_eq_bot hS] at hz
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hz)
  obtain ⟨l, hlL, r, hrR, hlr⟩ : ∃ l ∈ L, ∃ r ∈ R, l * r = n⁻¹ * t * n := by
    have hmul : n⁻¹ * t * n ∈ (L : Set G) * (R : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right L R hLnormR]
      exact hxLR
    exact hmul
  have hx2 : (n⁻¹ * t * n) * (n⁻¹ * t * n) = 1 := by
    have hord : orderOf (n⁻¹ * t * n) = 2 := by
      have h := MulEquiv.orderOf_eq (MulAut.conj n⁻¹) t
      simpa [MulAut.conj_apply, ht2] using h
    have h := pow_orderOf_eq_one (n⁻¹ * t * n)
    rw [hord] at h
    simpa [pow_two] using h
  have hlrcomm : l * r = r * l := Subgroup.mem_centralizer_iff.mp (hRleCL hrR) l hlL
  have hsq : (l * l) * (r * r) = 1 := by
    have h := hx2
    rw [← hlr] at h
    calc (l * l) * (r * r) = l * (l * r) * r := by group
      _ = l * (r * l) * r := by rw [hlrcomm]
      _ = (l * r) * (l * r) := by group
      _ = 1 := h
  have hll_inf : l * l ∈ L ⊓ R := by
    refine Subgroup.mem_inf.mpr ⟨L.mul_mem hlL hlL, ?_⟩
    have h : l * l = (r * r)⁻¹ := by
      calc l * l = (l * l) * ((r * r) * (r * r)⁻¹) := by group
        _ = ((l * l) * (r * r)) * (r * r)⁻¹ := by group
        _ = (r * r)⁻¹ := by rw [hsq, one_mul]
    rw [h]
    exact R.inv_mem (R.mul_mem hrR hrR)
  have hll_one : l * l = 1 := by
    have h := hll_inf
    rw [hinfLR] at h
    exact Subgroup.mem_bot.mp h
  have hrr_one : r * r = 1 := by
    have h := hsq
    rw [hll_one, one_mul] at h
    exact h
  have hr_one : r = 1 := by
    have h2dvd : orderOf r ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      simpa [pow_two] using hrr_one
    have hdvd : orderOf r ∣ Nat.card R := Subgroup.orderOf_dvd_natCard R hrR
    have hcop2 : Nat.Coprime 2 (Nat.card R) := Nat.coprime_two_left.mpr hRodd
    have horder : orderOf r = 1 := Nat.eq_one_of_dvd_coprimes hcop2 h2dvd hdvd
    exact orderOf_eq_one_iff.mp horder
  have htn : n⁻¹ * t * n ∈ L := by
    rw [← hlr, hr_one, mul_one]
    exact hlL
  have hcardzp : Nat.card (Subgroup.zpowers e) = 3 := by
    rw [Nat.card_zpowers, he3]
  have htM : t ∈ M := by
    rw [hM]
    exact Subgroup.mem_map.mpr ⟨n⁻¹ * t * n, htn, by
      change n * (n⁻¹ * t * n) * n⁻¹ = t
      group⟩
  have heC_M : e ∈ Subgroup.centralizer (M : Set G) := by
    rw [hM, CFSG.GroupTheory.centralizer_map_conj n L]
    refine Subgroup.mem_map.mpr ⟨b, b_mem_centralizer_L hS, ?_⟩
    simp [he, MulAut.conj_apply]
  have hM_le_Ce : M ≤ Subgroup.centralizer ({e} : Set G) := by
    intro m hm
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp heC_M m hm
  set Be : Subgroup G := Bs ⊓ M with hBe
  set NM : Subgroup G := M ⊓ Subgroup.normalizer (Be : Set G) with hNM
  have hNMs : NM.subgroupOf M = Subgroup.normalizer ((Be).subgroupOf M) := by
    ext x
    constructor
    · intro hx
      have hxNM : (x : G) ∈ NM := Subgroup.mem_subgroupOf.mp hx
      rw [hNM] at hxNM
      obtain ⟨-, hxNBe⟩ := hxNM
      change x ∈ Subgroup.normalizer ((Be).subgroupOf M)
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        have hyBe : (y : G) ∈ Be := Subgroup.mem_subgroupOf.mp hy
        have hconj : (x : G) * (y : G) * (x : G)⁻¹ ∈ Be :=
          (Subgroup.mem_normalizer_iff.mp hxNBe (y : G)).mp hyBe
        rw [Subgroup.mem_subgroupOf]
        exact hconj
      · intro hy
        have hconjG : (x : G) * (y : G) * (x : G)⁻¹ ∈ Be := by
          have := Subgroup.mem_subgroupOf.mp hy
          simpa using this
        exact (Subgroup.mem_normalizer_iff.mp hxNBe (y : G)).mpr hconjG
    · intro hx
      rw [Subgroup.mem_subgroupOf]
      rw [hNM]
      constructor
      · exact x.2
      · change (x : G) ∈ Subgroup.normalizer (Be : Set G)
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          rw [hBe] at hy
          have hyM : y ∈ M := hy.2
          have hy' : (⟨y, hyM⟩ : M) ∈ (Be).subgroupOf M := by
            rw [Subgroup.mem_subgroupOf]
            exact hy
          have hconj := (Subgroup.mem_normalizer_iff.mp hx ⟨y, hyM⟩).mp hy'
          have := Subgroup.mem_subgroupOf.mp hconj
          simpa using this
        · intro hy
          rw [hBe] at hy
          obtain ⟨hyBs, hconjM⟩ := hy
          have hyM : y ∈ M := by
            rw [show y = (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹) * (x : G) by group]
            exact M.mul_mem (M.mul_mem (M.inv_mem x.2) hconjM) x.2
          have hconj' : ((x : M) * ⟨y, hyM⟩ * x⁻¹) ∈ (Be).subgroupOf M := by
            rw [Subgroup.mem_subgroupOf]
            show (x : G) * y * (x : G)⁻¹ ∈ Be
            rw [hBe]
            exact ⟨hyBs, hconjM⟩
          have hyH : (⟨y, hyM⟩ : M) ∈ (Be).subgroupOf M :=
            (Subgroup.mem_normalizer_iff.mp hx ⟨y, hyM⟩).mpr hconj'
          have := Subgroup.mem_subgroupOf.mp hyH
          simpa using this
  have hmapNM : (NM.subgroupOf M).map φe.toMonoidHom =
      Subgroup.normalizer (torU K : Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) := by
    rw [hNMs, Subgroup.map_equiv_normalizer_eq, hBe, hS'.map_inf]
  have hC_Bs_t : Subgroup.centralizer ({t} : Set G) ⊓ Bs = Bs ⊓ L := by
    apply le_antisymm
    · rintro x ⟨hxt, hxBs⟩
      obtain ⟨p, hp, y, hy, hpy⟩ := exists_mul_eq_of_mem_Bs hS hxBs
      have hyt : y ∈ Subgroup.centralizer ({t} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp htL y hy.2
      have hxt' : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hxt
      have hpt : p * t = t * p := by
        have hp_eq : p = x * y⁻¹ := by rw [← hpy]; group
        have hyinv : y⁻¹ * t = t * y⁻¹ := by
          have h := congrArg (fun z => y⁻¹ * z * y⁻¹)
            (Subgroup.mem_centralizer_singleton_iff.mp hyt)
          have h' : t * y⁻¹ = y⁻¹ * t := by simpa [mul_assoc] using h
          exact h'.symm
        rw [hp_eq]
        calc (x * y⁻¹) * t = x * (y⁻¹ * t) := by group
          _ = x * (t * y⁻¹) := by rw [hyinv]
          _ = (x * t) * y⁻¹ := by group
          _ = (t * x) * y⁻¹ := by rw [hxt']
          _ = t * (x * y⁻¹) := by group
      have hconj_p : t * p * t⁻¹ = p⁻¹ := by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
        rw [← conj_zpow, htb, inv_zpow]
      have hp_eq_inv : p = p⁻¹ := by
        have h1 : t * p * t⁻¹ = p := by rw [← hpt]; group
        exact h1.symm.trans hconj_p
      have hp2 : p ^ 2 = 1 := by
        rw [pow_two]
        have h := congrArg (fun z => p * z) hp_eq_inv
        rw [h, mul_inv_cancel]
      have h2dvd : orderOf p ∣ 2 := by
        rw [orderOf_dvd_iff_pow_eq_one]
        exact hp2
      have h3dvd : orderOf p ∣ 3 := by
        have := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers b) hp
        rwa [Nat.card_zpowers, hS.orderOf_b] at this
      have hp1 : p = 1 := by
        have h := Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 2 3) h2dvd h3dvd
        exact orderOf_eq_one_iff.mp h
      rw [← hpy, hp1, one_mul]
      exact hy
    · intro x hx
      exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp htL x hx.2), hx.1⟩
  have hcard_CBs_t : Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ Bs) = 3 ^ 4 := by
    rw [hC_Bs_t]
    exact card_Bbar hS
  have hC_Bs_split : Subgroup.centralizer ({t} : Set G) ⊓ Bs =
      Subgroup.zpowers e ⊔ (Subgroup.centralizer ({t} : Set G) ⊓ Be) := by
    apply le_antisymm
    · rintro x ⟨hxt, hxBs⟩
      obtain ⟨p, hp, y, hy, hpy⟩ := exists_mul_eq_of_mem_Bs hS' hxBs
      have heCt : e ∈ Subgroup.centralizer ({t} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp heC_M t htM).symm
      have hzp_le_Ct : Subgroup.zpowers e ≤ Subgroup.centralizer ({t} : Set G) :=
        Subgroup.zpowers_le.mpr heCt
      have hpt : p * t = t * p :=
        (Subgroup.mem_centralizer_iff.mp (hzp_le_Ct hp) t (by simp)).symm
      have hxt' : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hxt
      have hxconj : t * x * t⁻¹ = x := by rw [← hxt']; group
      have h1 : t * x * t⁻¹ = p * (t * y * t⁻¹) := by
        rw [← hpy]
        calc t * (p * y) * t⁻¹ = (t * p * t⁻¹) * (t * y * t⁻¹) := by group
          _ = p * (t * y * t⁻¹) := by rw [show t * p * t⁻¹ = p by rw [← hpt]; group]
      have hyt' : t * y * t⁻¹ = y := by
        rw [hxconj] at h1
        have : p * (t * y * t⁻¹) = p * y := by rw [← h1, ← hpy]
        exact mul_left_cancel this
      have hyt : y * t = t * y := by
        calc y * t = (t * y * t⁻¹) * t := by rw [hyt']
          _ = t * y := by group
      have hyC : y ∈ Subgroup.centralizer ({t} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr hyt
      rw [← hpy]
      exact Subgroup.mul_mem_sup hp ⟨hyC, by rw [hBe]; exact hy⟩
    · refine sup_le ?_ ?_
      · intro p hp
        have heCt : e ∈ Subgroup.centralizer ({t} : Set G) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_iff.mp heC_M t htM).symm
        exact ⟨Subgroup.zpowers_le.mpr heCt hp, Subgroup.zpowers_le.mpr hS'.mem hp⟩
      · intro y hy
        exact ⟨hy.1, hy.2.1⟩
  have hcard_CBe_t : Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ Be) = 3 ^ 3 := by
    have hnorm : Subgroup.centralizer ({t} : Set G) ⊓ Be ≤
        Subgroup.normalizer (Subgroup.zpowers e : Set G) := by
      intro y hy
      rw [CFSG.GroupTheory.mem_normalizer_zpowers_iff]
      have hyM : y ∈ M := hy.2.2
      have hye : y * e = e * y :=
        Subgroup.mem_centralizer_iff.mp heC_M y hyM
      rw [show y * e * y⁻¹ = e by rw [hye]; group]
      exact Subgroup.mem_zpowers e
    have hdisj : Disjoint (Subgroup.zpowers e)
        (Subgroup.centralizer ({t} : Set G) ⊓ Be) := by
      rw [disjoint_iff]
      apply le_antisymm _ bot_le
      intro x hx
      have hx' : x ∈ Subgroup.zpowers e ⊓ (Bs ⊓ M) := by
        rw [← hBe]
        exact ⟨hx.1, hx.2.2⟩
      rwa [hS'.zpowers_b_inf_Bbar] at hx'
    have hcard := hcard_CBs_t
    rw [hC_Bs_split,
      CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
        (Subgroup.zpowers e) (Subgroup.centralizer ({t} : Set G) ⊓ Be) hnorm hdisj,
      hcardzp] at hcard
    norm_num at hcard ⊢
    omega
  set m0 : G := n⁻¹ * t * n with hm0
  set u : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
    φ ⟨m0, htn⟩ with hu
  have huφ : u = φe ⟨t, htM⟩ := by
    have hmem : n * m0 * n⁻¹ ∈ L.map (MulAut.conj n).toMonoidHom := by
      have : n * m0 * n⁻¹ = t := by rw [hm0]; group
      rw [this]
      exact htM
    have h := conjEquiv_apply (L := L) φ n htn hmem
    have hsub : (⟨t, htM⟩ : M) = ⟨n * m0 * n⁻¹, hmem⟩ := by
      apply Subtype.ext
      show t = n * m0 * n⁻¹
      rw [hm0]
      group
    have hmain : φe ⟨t, htM⟩ = φ ⟨m0, htn⟩ := by
      rw [hφe, hsub]
      exact h
    exact hu.trans hmain.symm
  have htNM : t ∈ NM := by
    rw [hNM]
    refine ⟨htM, ?_⟩
    change t ∈ Subgroup.normalizer (Be : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hBe] at hy ⊢
      exact ⟨(Subgroup.mem_normalizer_iff.mp ht y).mp hy.1,
        M.mul_mem (M.mul_mem htM hy.2) (M.inv_mem htM)⟩
    · intro hy
      rw [hBe] at hy ⊢
      have hyM : y ∈ M := by
        have : y = t⁻¹ * (t * y * t⁻¹) * t := by group
        rw [this]
        exact M.mul_mem (M.mul_mem (M.inv_mem htM) hy.2) htM
      exact ⟨(Subgroup.mem_normalizer_iff.mp ht y).mpr hy.1, hyM⟩
  have huN : u ∈ Subgroup.normalizer
      (torU K : Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) := by
    rw [huφ]
    have hmem : φe ⟨t, htM⟩ ∈ (NM.subgroupOf M).map φe.toMonoidHom := by
      refine Subgroup.mem_map.mpr ⟨⟨t, htM⟩, ?_, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      exact htNM
    rwa [hmapNM] at hmem
  have hu2 : orderOf u = 2 := by
    rw [hu]
    have hm_ord : orderOf m0 = 2 := by
      have h := MulEquiv.orderOf_eq (MulAut.conj n⁻¹) t
      simpa [hm0, MulAut.conj_apply, ht2] using h
    rw [MulEquiv.orderOf_eq]
    simpa using hm_ord
  have hmapC : ((Subgroup.centralizer ({t} : Set G) ⊓ Be).subgroupOf M).map
      φe.toMonoidHom =
      torU K ⊓ Subgroup.centralizer ({u} :
        Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) := by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      have hx' : (x : G) ∈ Subgroup.centralizer ({t} : Set G) ⊓ Be :=
        Subgroup.mem_subgroupOf.mp hx
      obtain ⟨hxt, hxBe⟩ := hx'
      constructor
      · have hxmem : φe x ∈ ((Be).subgroupOf M).map φe.toMonoidHom :=
          Subgroup.mem_map.mpr ⟨x, by rw [Subgroup.mem_subgroupOf]; exact hxBe, rfl⟩
        rwa [hBe, hS'.map_inf] at hxmem
      · change φe x ∈ Subgroup.centralizer ({u} :
          Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))))
        rw [Subgroup.mem_centralizer_singleton_iff]
        rw [huφ]
        change φe x * φe ⟨t, htM⟩ = φe ⟨t, htM⟩ * φe x
        have hxtM : (x : M) * ⟨t, htM⟩ = ⟨t, htM⟩ * x :=
          Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hxt)
        simpa only [map_mul] using congrArg φe hxtM
    · rintro y ⟨hytor, hyu⟩
      have hmem : y ∈ ((Be).subgroupOf M).map φe.toMonoidHom := by
        rwa [hBe, hS'.map_inf]
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hmem
      refine ⟨z, ?_, hzy⟩
      have hzBe : (z : G) ∈ Be := Subgroup.mem_subgroupOf.mp hz
      have hzt : (z : M) * ⟨t, htM⟩ = ⟨t, htM⟩ * z := by
        apply φe.injective
        have hyuc : y * u = u * y :=
          Subgroup.mem_centralizer_singleton_iff.mp hyu
        rw [← hzy, huφ] at hyuc
        rw [map_mul, map_mul]
        exact hyuc
      change z ∈ (Subgroup.centralizer ({t} : Set G) ⊓ Be).subgroupOf M
      rw [Subgroup.mem_subgroupOf]
      refine ⟨?_, hzBe⟩
      change (z : G) ∈ Subgroup.centralizer ({t} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val hzt
  have hfix : Nat.card ↥(torU K ⊓ Subgroup.centralizer ({u} :
      Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))))) = 3 ^ 3 := by
    have hBeM : Be ≤ M := by rw [hBe]; exact inf_le_right
    calc Nat.card ↥(torU K ⊓ Subgroup.centralizer ({u} :
          Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))))
        = Nat.card ↥(((Subgroup.centralizer ({t} : Set G) ⊓ Be).subgroupOf M).map
            φe.toMonoidHom) := by rw [hmapC]
      _ = Nat.card ↥((Subgroup.centralizer ({t} : Set G) ⊓ Be).subgroupOf M) :=
          Subgroup.card_map_of_injective φe.injective
      _ = Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ Be) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe
            (h := inf_le_right.trans hBeM)).toEquiv
      _ = 3 ^ 3 := hcard_CBe_t
  refine ⟨htn, ?_, ?_, ?_⟩
  · simpa [hm0, hu] using huN
  · simpa [hm0, hu] using hu2
  · simpa [hm0, hu] using hfix

theorem exists_conj_tZero [Finite G] [Finite K] (hG : IsCharTwoType G)
    (hS : LocalSetting hω b L φ Bs)
    {t : G} (ht : t ∈ Subgroup.normalizer (Bs : Set G)) (ht2 : orderOf t = 2)
    (htb : t * b * t⁻¹ = b⁻¹) (htL : t ∈ Subgroup.centralizer (L : Set G))
    {n : G} (hn : n ∈ Subgroup.normalizer (Bs : Set G)) (hnL : n * b * n⁻¹ ∈ L)
    (hnφ : φ ⟨n * b * n⁻¹, hnL⟩ = threeA hω)
    (htA : n⁻¹ * t * n ∈
      (L ⊓ Subgroup.normalizer (Bs : Set G)) ⊔ Subgroup.centralizer (Bs : Set G)) :
    ∃ htn : n⁻¹ * t * n ∈ L, ∃ g : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)),
      g * φ ⟨n⁻¹ * t * n, htn⟩ * g⁻¹ = tZero hS.card_K := by
  obtain ⟨htn, huN, hu2, hfix⟩ :=
    exists_mem_normalizer_torU hG hS ht ht2 htb htL hn hnL hnφ htA
  obtain ⟨g, hg⟩ := exists_conj_eq_tZero hS.card_K huN hu2 hfix
  exact ⟨htn, g, hg⟩

theorem card_pCoreOf_centralizer_inf_le [Finite G] [Finite K] (hG : IsCharTwoType G)
    (hS : LocalSetting hω b L φ Bs)
    {t : G} (ht : t ∈ Subgroup.normalizer (Bs : Set G)) (ht2 : orderOf t = 2)
    (htb : t * b * t⁻¹ = b⁻¹) (htL : t ∈ Subgroup.centralizer (L : Set G))
    {n : G} (hn : n ∈ Subgroup.normalizer (Bs : Set G)) (hnL : n * b * n⁻¹ ∈ L)
    (hnφ : φ ⟨n * b * n⁻¹, hnL⟩ = threeA hω)
    (htA : n⁻¹ * t * n ∈
      (L ⊓ Subgroup.normalizer (Bs : Set G)) ⊔ Subgroup.centralizer (Bs : Set G)) :
    Nat.card (pCoreOf 2 (Subgroup.centralizer {n * b * n⁻¹} ⊓ Subgroup.centralizer {t})) ≤
      2 ^ 9 := by
  classical
  obtain ⟨htn, g, hg⟩ := exists_conj_tZero hG hS ht ht2 htb htL hn hnL hnφ htA
  set e : G := n * b * n⁻¹ with he
  set M : Subgroup G := L.map (MulAut.conj n : G →* G) with hM
  set φe : M ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) := conjEquiv φ n with hφe
  have hS' : LocalSetting hω e M φe Bs := hS.conj hn hnL hnφ
  have htM : t ∈ M := by
    rw [hM]
    exact Subgroup.mem_map.mpr ⟨n⁻¹ * t * n, htn, by
      change n * (n⁻¹ * t * n) * n⁻¹ = t
      group⟩
  have huφ : φ ⟨n⁻¹ * t * n, htn⟩ = φe ⟨t, htM⟩ :=
    conjEquiv_apply_inv_conj htn htM
  set u : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
    φ ⟨n⁻¹ * t * n, htn⟩ with hu
  have hgu : g * u * g⁻¹ = tZero hS.card_K := hg
  have htCe : t ∈ Subgroup.centralizer ({e} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp htL e hnL).symm
  have heC_M : e ∈ Subgroup.centralizer (M : Set G) := by
    rw [hM]
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hm
    have hbl : b * l = l * b :=
      (Subgroup.mem_centralizer_iff.mp (b_mem_centralizer_L hS) l hl).symm
    change ((MulAut.conj n) l) * e = e * ((MulAut.conj n) l)
    simp only [MulAut.conj_apply, he]
    calc (n * l * n⁻¹) * (n * b * n⁻¹) = n * (l * b) * n⁻¹ := by group
      _ = n * (b * l) * n⁻¹ := by rw [hbl]
      _ = (n * b * n⁻¹) * (n * l * n⁻¹) := by group
  set Re : Subgroup G := Subgroup.centralizer ({e} : Set G) ⊓
    Subgroup.centralizer (M : Set G) with hRe
  have hoddRe : Odd (Nat.card Re) := by
    have hOle : relPPrimeCore 3 (Subgroup.centralizer ({e} : Set G)) ≤
        Subgroup.centralizer ({e} : Set G) :=
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le _
    have hOnorm : ((relPPrimeCore 3 (Subgroup.centralizer ({e} : Set G))).subgroupOf
        (Subgroup.centralizer ({e} : Set G))).Normal :=
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
        Nat.prime_three _
    have hCeN : Subgroup.centralizer ({e} : Set G) ≤ Subgroup.normalizer
        (relPPrimeCore 3 (Subgroup.centralizer ({e} : Set G)) : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hOle).mp hOnorm
    have heCe : e ∈ Subgroup.centralizer ({e} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
    have hzpe : Subgroup.zpowers e ≤ Subgroup.normalizer
        (relPPrimeCore 3 (Subgroup.centralizer ({e} : Set G)) : Set G) :=
      (Subgroup.zpowers_le.mpr heCe).trans hCeN
    have hcopO : Nat.Coprime 3
        (Nat.card (relPPrimeCore 3 (Subgroup.centralizer ({e} : Set G)))) :=
      coprime_card_relPPrimeCore
        Nat.prime_three _
    have he3 : orderOf e = 3 := by
      have h := orderOf_injective (MulAut.conj n).toMonoidHom
        (MulAut.conj n).injective b
      simpa [he, MulAut.conj_apply, hS.orderOf_b] using h
    have hcardzp : Nat.card (Subgroup.zpowers e) = 3 := by
      rw [Nat.card_zpowers, he3]
    have hdisjO : Disjoint (relPPrimeCore 3 (Subgroup.centralizer ({e} : Set G)))
        (Subgroup.zpowers e) := by
      apply Subgroup.disjoint_of_coprime_natCard
      rw [hcardzp]
      exact hcopO.symm
    have hcardRe : Nat.card Re = Nat.card
        (relPPrimeCore 3 (Subgroup.centralizer ({e} : Set G))) *
        Nat.card (Subgroup.zpowers e) := by
      rw [hRe, centralizer_inf_eq hS']
      exact CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
        (relPPrimeCore 3 (Subgroup.centralizer ({e} : Set G)))
        (Subgroup.zpowers e) hzpe hdisjO
    rw [hcardRe, hcardzp]
    exact (odd_card_relPPrimeCore hG hS').mul (by norm_num : Odd 3)
  have hCeN : Subgroup.centralizer ({e} : Set G) ≤ Subgroup.normalizer (M : Set G) :=
    centralizer_b_le_normalizer_L hS'
  let φ' : M ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
    φe.trans (MulAut.conj g)
  let ψ : Subgroup.centralizer ({e} : Set G) →*
      MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :=
    (MulAut.congr φ').toMonoidHom.comp
      ((Subgroup.normalizerMonoidHom M).comp (Subgroup.inclusion hCeN))
  have hφ'_apply (m : M) : φ' m = g * φe m * g⁻¹ := by
    change (φe.trans (MulAut.conj g)) m = _
    rw [MulEquiv.trans_apply, MulAut.conj_apply]
  have hψ_apply (x : Subgroup.centralizer ({e} : Set G)) (m : M) :
      ψ x (φ' m) = φ' ((Subgroup.normalizerMonoidHom M
        (Subgroup.inclusion hCeN x)) m) := by
    change (φ'.symm.trans (((Subgroup.normalizerMonoidHom M
      (Subgroup.inclusion hCeN x)).trans φ'))) (φ' m) = _
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hψ_apply_coe (x : Subgroup.centralizer ({e} : Set G)) (m : M) :
      ψ x (φ' m) = φ' ⟨x.1 * (m : G) * x.1⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hCeN x.2) (m : G)).mp m.2⟩ := by
    rw [hψ_apply]
    apply congrArg φ'
    apply Subtype.ext
    exact Subgroup.normalizerMonoidHom_apply_apply_coe M
      (Subgroup.inclusion hCeN x) m
  have hM_le_Ce : M ≤ Subgroup.centralizer ({e} : Set G) := by
    intro m hm
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp heC_M m hm
  have hker : ψ.ker = Re.subgroupOf (Subgroup.centralizer ({e} : Set G)) := by
    ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      rw [Subgroup.mem_subgroupOf]
      refine ⟨x.2, ?_⟩
      change (x : G) ∈ Subgroup.centralizer (M : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      let mm : M := ⟨m, hm⟩
      have h := congrArg (fun α =>
        α (φ' mm)) hx
      rw [hψ_apply_coe] at h
      have hsub : (⟨x.1 * m * x.1⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hCeN x.2) (m : G)).mp mm.2⟩ : M) = mm :=
        φ'.injective h
      have hval : x.1 * m * x.1⁻¹ = m := congrArg Subtype.val hsub
      calc m * x.1 = (x.1 * m * x.1⁻¹) * x.1 := by rw [hval]
        _ = x.1 * m := by group
    · intro hx
      rw [MonoidHom.mem_ker]
      have hxM : x.1 ∈ Subgroup.centralizer (M : Set G) :=
        (Subgroup.mem_subgroupOf.mp hx).2
      ext u
      obtain ⟨m, rfl⟩ := φ'.surjective u
      rw [hψ_apply_coe]
      have hxm : x.1 * (m : G) * x.1⁻¹ = (m : G) := by
        have hmx : (m : G) * x.1 = x.1 * (m : G) :=
          Subgroup.mem_centralizer_iff.mp hxM m m.2
        calc x.1 * (m : G) * x.1⁻¹ = ((m : G) * x.1) * x.1⁻¹ := by rw [hmx]
          _ = (m : G) := by group
      apply congrArg φ'
      apply Subtype.ext
      exact hxm
  have hψ_mem (m : M) :
      ψ ⟨(m : G), hM_le_Ce m.2⟩ = MulAut.conj (φ' m) := by
    ext u
    obtain ⟨m', rfl⟩ := φ'.surjective u
    rw [hψ_apply_coe]
    rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    apply congrArg φ'
    apply Subtype.ext
    rfl
  have hmapM : (M.subgroupOf (Subgroup.centralizer ({e} : Set G))).map ψ =
      (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
        MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))).range := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hxM : (x : G) ∈ M := Subgroup.mem_subgroupOf.mp hx
      exact ⟨φ' ⟨(x : G), hxM⟩, by
        rw [show ψ x = ψ ⟨(x : G), hM_le_Ce hxM⟩ from
          congrArg ψ (Subtype.ext rfl)]
        exact (hψ_mem _).symm⟩
    · rintro _ ⟨u, rfl⟩
      obtain ⟨m, rfl⟩ := φ'.surjective u
      exact ⟨⟨(m : G), hM_le_Ce m.2⟩, Subgroup.mem_subgroupOf.mpr m.2, hψ_mem m⟩
  have hψt : ψ ⟨t, htCe⟩ = MulAut.conj (tZero hS.card_K) := by
    have hxeq : (⟨t, htCe⟩ : Subgroup.centralizer ({e} : Set G)) =
        ⟨((⟨t, htM⟩ : M) : G), hM_le_Ce htM⟩ := Subtype.ext rfl
    rw [hxeq, hψ_mem]
    rw [hφ'_apply]
    rw [show φe ⟨t, htM⟩ = u from huφ.symm, hgu]
  have htCe' : t * e * t⁻¹ = e := by
    have h : t * e = e * t := Subgroup.mem_centralizer_iff.mp heC_M t htM
    rw [h]; group
  have htRe : t ∈ Subgroup.normalizer (Re : Set G) := by
    apply CFSG.GroupTheory.mem_normalizer_of_conj_mem
    intro z hz
    rw [hRe] at hz ⊢
    constructor
    · change (t * z * t⁻¹) ∈ Subgroup.centralizer ({e} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hze : z * e = e * z := Subgroup.mem_centralizer_singleton_iff.mp hz.1
      have hte : t * e = e * t := Subgroup.mem_centralizer_iff.mp heC_M t htM
      have hte_inv : t⁻¹ * e = e * t⁻¹ := by
        calc t⁻¹ * e = t⁻¹ * (t * e * t⁻¹) := by rw [hte]; group
          _ = e * t⁻¹ := by group
      calc (t * z * t⁻¹) * e = t * z * (t⁻¹ * e) := by group
        _ = t * z * (e * t⁻¹) := by rw [hte_inv]
        _ = t * (z * e) * t⁻¹ := by group
        _ = t * (e * z) * t⁻¹ := by rw [hze]
        _ = (t * e) * z * t⁻¹ := by group
        _ = (e * t) * z * t⁻¹ := by rw [hte]
        _ = e * (t * z * t⁻¹) := by group
    · change (t * z * t⁻¹) ∈ Subgroup.centralizer (M : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have hm' : t⁻¹ * m * t ∈ M :=
        M.mul_mem (M.mul_mem (M.inv_mem htM) hm) htM
      have hcomm := Subgroup.mem_centralizer_iff.mp hz.2 (t⁻¹ * m * t) hm'
      have hcalc : (t * z * t⁻¹) * m = m * (t * z * t⁻¹) := by
        calc (t * z * t⁻¹) * m = t * z * (t⁻¹ * m * t) * t⁻¹ := by group
          _ = t * (z * (t⁻¹ * m * t)) * t⁻¹ := by group
          _ = t * ((t⁻¹ * m * t) * z) * t⁻¹ := by rw [hcomm]
          _ = m * (t * z * t⁻¹) := by group
      exact hcalc.symm
  have hzp_le_NRe : Subgroup.zpowers t ≤ Subgroup.normalizer (Re : Set G) :=
    Subgroup.zpowers_le.mpr htRe
  set H0 : Subgroup G := Re ⊔ Subgroup.zpowers t with hH0
  have htH0 : t ∈ H0 := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have htH0_ord : orderOf (⟨t, htH0⟩ : H0) = 2 := by
    rw [← Subgroup.orderOf_coe (⟨t, htH0⟩ : H0)]
    exact ht2
  have hcardH0 : Nat.card H0 = Nat.card Re * 2 := by
    rw [hH0, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      Re (Subgroup.zpowers t) hzp_le_NRe]
    · rw [Nat.card_zpowers, ht2]
    · apply Subgroup.disjoint_of_coprime_natCard
      rw [Nat.card_zpowers, ht2]
      exact Nat.coprime_two_right.mpr hoddRe
  have hnot4 : ¬ 4 ∣ Nat.card H0 := by
    rw [hcardH0, mul_comm]
    intro h4
    have hcop : Nat.Coprime 4 (Nat.card Re) :=
      (Nat.coprime_two_left.mpr hoddRe).pow_left 2
    have hdiv : 4 ∣ 2 := hcop.dvd_of_dvd_mul_right h4
    norm_num at hdiv
  have hconj_involutions : ∀ (h : H0), orderOf h = 2 →
      ∃ z ∈ Re, z * t * z⁻¹ = (h : G) := by
    intro h hh
    obtain ⟨y, hy⟩ := TauCeti.exists_mul_mul_inv_mem_zpowers_of_not_sq_dvd
      (p := 2) (G := H0) hnot4 (g := h) (h := ⟨t, htH0⟩) hh htH0_ord
    have hy' : y * ⟨t, htH0⟩ * y⁻¹ = h := by
      rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hh).mp hy with h1 | h1
      · exfalso
        have hord : orderOf (y * (⟨t, htH0⟩ : H0) * y⁻¹) = 2 := by
          have := MulEquiv.orderOf_eq (MulAut.conj y) (⟨t, htH0⟩ : H0)
          simpa [MulAut.conj_apply, htH0_ord] using this
        rw [h1, orderOf_one] at hord
        norm_num at hord
      · exact h1
    have hcarrier : (↑H0 : Set G) = (Re : Set G) * (Subgroup.zpowers t : Set G) := by
      rw [hH0]
      exact Subgroup.coe_mul_of_right_le_normalizer_left Re (Subgroup.zpowers t) hzp_le_NRe
    have hy_mem : (y : G) ∈ (Re : Set G) * (Subgroup.zpowers t : Set G) := by
      rw [← hcarrier]; exact y.2
    obtain ⟨z, hz, s, hs, hzs⟩ := Set.mem_mul.mp hy_mem
    have hs_cases : s = 1 ∨ s = t :=
      (Subgroup.mem_zpowers_iff_of_orderOf_eq_two ht2).mp hs
    have hz_conj : z * t * z⁻¹ = (y : G) * t * (y : G)⁻¹ := by
      rw [← hzs]
      rcases hs_cases with h | h
      · rw [h, mul_one]
      · rw [h]
        have htt : t * t = 1 := by
          have := pow_orderOf_eq_one t
          rw [ht2] at this
          simpa [pow_two] using this
        calc z * t * z⁻¹ = z * (t * t) * t * z⁻¹ := by rw [htt]; group
          _ = z * 1 * t * z⁻¹ := by rw [htt]
          _ = (z * t) * t * (z * t)⁻¹ := by group
    refine ⟨z, hz, ?_⟩
    rw [hz_conj]
    have := congrArg Subtype.val hy'
    simpa using this
  set D : Subgroup G := Subgroup.centralizer ({e} : Set G) ⊓
    Subgroup.centralizer ({t} : Set G) with hD
  have hD_le_Ce : D ≤ Subgroup.centralizer ({e} : Set G) := hD ▸ inf_le_left
  have hDimage : (D.subgroupOf (Subgroup.centralizer ({e} : Set G))).map ψ =
      ψ.range ⊓ Subgroup.centralizer ({ψ ⟨t, htCe⟩} :
        Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))))) := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hxD : (x : G) ∈ D := Subgroup.mem_subgroupOf.mp hx
      constructor
      · exact ⟨x, rfl⟩
      · change ψ x ∈ Subgroup.centralizer ({ψ ⟨t, htCe⟩} :
          Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))))
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hxt : (x : G) ∈ Subgroup.centralizer ({t} : Set G) := hxD.2
        have hxt' : (x : G) * t = t * (x : G) :=
          Subgroup.mem_centralizer_singleton_iff.mp hxt
        have hxtm : x * ⟨t, htCe⟩ = ⟨t, htCe⟩ * x := Subtype.ext hxt'
        simpa only [map_mul] using congrArg ψ hxtm
    · rintro y ⟨hy_range, hy_cent⟩
      obtain ⟨x, rfl⟩ := hy_range
      let r : G := x.1 * t * x.1⁻¹ * t⁻¹
      have hrCe : r ∈ Subgroup.centralizer ({e} : Set G) := by
        apply Subgroup.mul_mem
        · apply Subgroup.mul_mem
          · apply Subgroup.mul_mem
            · exact x.2
            · exact htCe
          · exact Subgroup.inv_mem _ x.2
        · exact Subgroup.inv_mem _ htCe
      let xr : Subgroup.centralizer ({e} : Set G) := ⟨r, hrCe⟩
      have hψr : ψ xr = 1 := by
        have hcomm : ψ x * ψ ⟨t, htCe⟩ = ψ ⟨t, htCe⟩ * ψ x := by
          simpa using Subgroup.mem_centralizer_singleton_iff.mp hy_cent
        have hr_eq : xr = x * ⟨t, htCe⟩ * x⁻¹ * ⟨t, htCe⟩⁻¹ := by
          apply Subtype.ext
          show r = x.1 * t * x.1⁻¹ * t⁻¹
          rfl
        rw [hr_eq, map_mul, map_mul, map_mul, map_inv, map_inv]
        rw [hcomm]
        group
      have hrRe : r ∈ Re := by
        have hker_mem : xr ∈ ψ.ker := by rw [MonoidHom.mem_ker]; exact hψr
        rw [hker] at hker_mem
        simpa using (Subgroup.mem_subgroupOf.mp hker_mem)
      have hrtH0 : r * t ∈ H0 :=
        Subgroup.mul_mem_sup hrRe (Subgroup.mem_zpowers t)
      have hrt_ord : orderOf (⟨r * t, hrtH0⟩ : H0) = 2 := by
        have hrt_eq : r * t = x.1 * t * x.1⁻¹ := by
          show x.1 * t * x.1⁻¹ * t⁻¹ * t = x.1 * t * x.1⁻¹
          group
        have hmem : x.1 * t * x.1⁻¹ ∈ H0 := hrt_eq ▸ hrtH0
        have harg : (⟨r * t, hrtH0⟩ : H0) = ⟨x.1 * t * x.1⁻¹, hmem⟩ :=
          Subtype.ext hrt_eq
        have h := MulEquiv.orderOf_eq (MulAut.conj x.1) t
        rw [MulAut.conj_apply, ht2] at h
        rw [harg, ← Subgroup.orderOf_coe (⟨x.1 * t * x.1⁻¹, hmem⟩ : H0)]
        exact h
      obtain ⟨z, hzRe, hzconj⟩ := hconj_involutions ⟨r * t, hrtH0⟩ hrt_ord
      let d : G := z⁻¹ * x.1
      have hdCe : d ∈ Subgroup.centralizer ({e} : Set G) :=
        (Subgroup.centralizer ({e} : Set G)).mul_mem
          (Subgroup.inv_mem _ hzRe.1) x.2
      have hdt : d * t * d⁻¹ = t := by
        show (z⁻¹ * x.1) * t * (z⁻¹ * x.1)⁻¹ = t
        have hxconj : x.1 * t * x.1⁻¹ = r * t := by
          show x.1 * t * x.1⁻¹ = x.1 * t * x.1⁻¹ * t⁻¹ * t
          group
        calc (z⁻¹ * x.1) * t * (z⁻¹ * x.1)⁻¹
            = z⁻¹ * (x.1 * t * x.1⁻¹) * z := by group
          _ = z⁻¹ * (r * t) * z := by rw [hxconj]
          _ = t := by
            have h := hzconj
            calc z⁻¹ * (r * t) * z = z⁻¹ * (z * t * z⁻¹) * z := by rw [h]
              _ = t := by group
      have hdt' : d * t = t * d := by
        calc d * t = (d * t * d⁻¹) * d := by group
          _ = t * d := by rw [hdt]
      have hdD : d ∈ D := ⟨hdCe, Subgroup.mem_centralizer_singleton_iff.mpr hdt'⟩
      refine ⟨⟨d, hdCe⟩, Subgroup.mem_subgroupOf.mpr hdD, ?_⟩
      let zC : Subgroup.centralizer ({e} : Set G) := ⟨z, hzRe.1⟩
      have hz_ker : ψ zC = 1 := by
        have : zC ∈ ψ.ker := by
          rw [hker]
          exact Subgroup.mem_subgroupOf.mpr hzRe
        rwa [MonoidHom.mem_ker] at this
      have hd_eq : (⟨d, hdCe⟩ : Subgroup.centralizer ({e} : Set G)) = zC⁻¹ * x := by
        apply Subtype.ext
        show d = z⁻¹ * x.1
        rfl
      rw [hd_eq, map_mul, map_inv, hz_ker, inv_one, one_mul]
  set H : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) :=
    ψ.range ⊓ Subgroup.centralizer ({ψ ⟨t, htCe⟩} :
      Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))))) with hH
  have hDimageH : (D.subgroupOf (Subgroup.centralizer ({e} : Set G))).map ψ = H :=
    hDimage
  let P : Subgroup G := pCoreOf 2 D
  let Psub : Subgroup D := P.subgroupOf D
  let gD : D →* MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :=
    ψ.comp (Subgroup.inclusion hD_le_Ce)
  let N : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) :=
    Psub.map gD
  have hHrange : H = gD.range := by
    rw [← hDimageH, MonoidHom.range_eq_map]
    ext x
    constructor
    · intro hx
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hx
      have hcD : (c : G) ∈ D := Subgroup.mem_subgroupOf.mp hc
      exact ⟨⟨c.1, hcD⟩, Subgroup.mem_top _, rfl⟩
    · rintro ⟨d, -, rfl⟩
      exact ⟨⟨d.1, hD_le_Ce d.2⟩, Subgroup.mem_subgroupOf.mpr d.2, rfl⟩
  have hP_le_D : P ≤ D := CFSG.LieType.BorelTits.pCoreOf_le 2 D
  have hP_le_Ce : P ≤ Subgroup.centralizer ({e} : Set G) := hP_le_D.trans hD_le_Ce
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D
  have hP2sub : IsPGroup 2 Psub :=
    hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hP_le_D).symm
  have hP_disj_Re : Disjoint P Re := by
    apply Subgroup.disjoint_of_coprime_natCard
    obtain ⟨n, hn⟩ := hP2.exists_card_eq
    rw [hn]
    exact (Nat.coprime_two_left.mpr hoddRe).pow_left n
  have hPnormD : (P.subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP_le_D).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D)
  have hN_le_H : N ≤ H := by
    rw [hHrange]
    exact Subgroup.map_le_range (H := Psub) (f := gD)
  have hN2 : IsPGroup 2 N := hP2sub.map gD
  have hNnorm : (N.subgroupOf H).Normal := by
    refine ⟨?conj_mem⟩
    intro n hn g
    have hnN : (n : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) ∈ N :=
      Subgroup.mem_subgroupOf.mp hn
    obtain ⟨p, hpP, hp_eq⟩ := Subgroup.mem_map.mp hnN
    have hgH : (g : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) ∈
        gD.range := by
      rw [← hHrange]; exact g.2
    obtain ⟨d, hd_eq⟩ := MonoidHom.mem_range.mp hgH
    have hd_eq' : (gD d : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) =
        (g : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) := hd_eq
    have hp_eq' : (gD p : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) =
        (n : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) := hp_eq
    have hconjP : d * p * d⁻¹ ∈ P.subgroupOf D :=
      hPnormD.conj_mem p hpP d
    have hmemN : gD (d * p * d⁻¹) ∈ N :=
      Subgroup.mem_map.mpr ⟨d * p * d⁻¹, hconjP, rfl⟩
    have hconj_val : (g * n * g⁻¹ : H).1 =
        gD (d * p * d⁻¹) := by
      change (g : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) *
        (n : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) *
        (g : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))))⁻¹ =
          (gD (d * p * d⁻¹) : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))))
      rw [← hd_eq', ← hp_eq', map_mul, map_mul, map_inv]
    rw [Subgroup.mem_subgroupOf, hconj_val]
    exact hmemN
  have hN_le_pCore : N ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 hN_le_H hNnorm hN2
  let gP : Psub →* MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :=
    gD.comp Psub.subtype
  have hN_eq_range : N = gP.range := by
    ext x
    constructor
    · intro hx
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
      exact ⟨⟨p, hp⟩, rfl⟩
    · rintro ⟨p, rfl⟩
      exact Subgroup.mem_map.mpr ⟨p, p.2, rfl⟩
  have hgP_inj : Function.Injective gP := by
    intro x y hxy
    have hgP_one : gP (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    let z : Psub := x * y⁻¹
    have hzC : (((z : D) : G)) ∈ Subgroup.centralizer ({e} : Set G) :=
      hP_le_Ce z.2
    let zC : Subgroup.centralizer ({e} : Set G) :=
      ⟨(((z : D) : G)), hzC⟩
    have hψ_eq : ψ zC = gP z := rfl
    have hz_ker : zC ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      rw [hψ_eq]
      exact hgP_one
    rw [hker] at hz_ker
    have hzRe : (((z : D) : G)) ∈ Re := Subgroup.mem_subgroupOf.mp hz_ker
    have hmem_inf : (((z : D) : G)) ∈ P ⊓ Re := ⟨z.2, hzRe⟩
    rw [hP_disj_Re.eq_bot] at hmem_inf
    have hone : z = 1 := by
      apply Subtype.ext
      exact Subtype.ext hmem_inf
    have hxy_one : x * y⁻¹ = 1 := hone
    calc x = (x * y⁻¹) * y := by group
      _ = y := by rw [hxy_one, one_mul]
  have hcardN : Nat.card N = Nat.card P := by
    rw [hN_eq_range, MonoidHom.range_eq_map,
      Subgroup.card_map_of_injective hgP_inj]
    rw [Nat.card_congr (Subgroup.topEquiv (G := Psub)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP_le_D).toEquiv]
  have hHbound : Nat.card (pCoreOf 2 H) ≤ 2 ^ 9 := by
    let H0 : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) :=
      ψ.range
    have hInn_le : (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
        MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))).range ≤ H0 := by
      rw [show H0 = ψ.range from rfl, ← hmapM]
      exact Subgroup.map_le_range (H := M.subgroupOf (Subgroup.centralizer ({e} : Set G)))
        (f := ψ)
    have hH_eq : H = H0 ⊓ Subgroup.centralizer
        ({MulAut.conj (tZero hS.card_K)} :
          Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))))) := by
      rw [hH, show H0 = ψ.range from rfl, hψt]
    have h := card_pCoreOf_inf_centralizer_le_of_le hS.card_K hInn_le
    rw [hH_eq]
    exact h
  have hcard_le : Nat.card P ≤ 2 ^ 9 := by
    rw [← hcardN]
    exact (Nat.card_le_card_of_injective (Subgroup.inclusion hN_le_pCore)
      (Subgroup.inclusion_injective hN_le_pCore)).trans hHbound
  simpa [P] using hcard_le

end LocalSetting

end CFSG.StandardType.USixTwo

end
