module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoLemmaC
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTransvectionNormalizer
public import CFSG.GroupTheory.PCore.PCoreOfMulEquiv
public import CFSG.Certificates.Kernel.ThDemp.OrbCent

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

theorem card_pCoreOf_conj_inf_centralizer [Finite G] [Finite K] (hG : IsCharTwoType G)
    (hS : LocalSetting hω b L φ Bs)
    {t : G} (ht : t ∈ Subgroup.normalizer (Bs : Set G)) (ht2 : orderOf t = 2)
    (htb : t * b * t⁻¹ = b⁻¹) (htL : t ∈ Subgroup.centralizer (L : Set G))
    {n : G} (hn : n ∈ Subgroup.normalizer (Bs : Set G)) (hnL : n * b * n⁻¹ ∈ L)
    (hnφ : φ ⟨n * b * n⁻¹, hnL⟩ = threeA hω)
    (htA : n⁻¹ * t * n ∈
      (L ⊓ Subgroup.normalizer (Bs : Set G)) ⊔ Subgroup.centralizer (Bs : Set G)) :
    Nat.card (pCoreOf 2 (L.map (MulAut.conj n : G →* G) ⊓ Subgroup.centralizer {t})) = 2 ^ 9 := by
  classical
  obtain ⟨htn, g, hg⟩ := exists_conj_tZero hG hS ht ht2 htb htL hn hnL hnφ htA
  set M : Subgroup G := L.map (MulAut.conj n : G →* G)
  have htM : t ∈ M := by
    refine Subgroup.mem_map.mpr ⟨n⁻¹ * t * n, htn, ?_⟩
    change MulAut.conj n (n⁻¹ * t * n) = t
    rw [MulAut.conj_apply]
    group
  let φe : ↥M ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) := conjEquiv φ n
  let ψ : ↥M ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
    φe.trans (MulAut.conj g)
  have hφet : φe ⟨t, htM⟩ = φ ⟨n⁻¹ * t * n, htn⟩ := by
    have hmem : n * (n⁻¹ * t * n) * n⁻¹ ∈ L.map (MulAut.conj n : G →* G) := by
      have hval : n * (n⁻¹ * t * n) * n⁻¹ = t := by group
      rw [hval]
      exact htM
    have h := conjEquiv_apply φ n (x := n⁻¹ * t * n) htn hmem
    have helem : (⟨t, htM⟩ : ↥(L.map (MulAut.conj n : G →* G))) =
        ⟨n * (n⁻¹ * t * n) * n⁻¹, hmem⟩ := Subtype.ext (by group)
    change conjEquiv φ n ⟨t, htM⟩ = φ ⟨n⁻¹ * t * n, htn⟩
    rw [helem, h]
  have hψt : ψ ⟨t, htM⟩ = tZero hS.card_K := by
    change (MulAut.conj g) (φe ⟨t, htM⟩) = tZero hS.card_K
    rw [hφet, MulAut.conj_apply]
    exact hg
  have hmap := CFSG.GroupTheory.map_pCoreOf_inf_centralizer_mulEquiv ψ htM
  rw [hψt] at hmap
  have hle : pCoreOf 2 (M ⊓ Subgroup.centralizer {t}) ≤ M :=
    (Subgroup.map_subtype_le (CFSG.pCore 2 ↥(M ⊓ Subgroup.centralizer {t}))).trans inf_le_left
  calc Nat.card (pCoreOf 2 (M ⊓ Subgroup.centralizer {t}))
      = Nat.card ((pCoreOf 2 (M ⊓ Subgroup.centralizer {t})).subgroupOf M) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).symm
    _ = Nat.card (((pCoreOf 2 (M ⊓ Subgroup.centralizer {t})).subgroupOf M).map
          ψ.toMonoidHom) := (Subgroup.card_map_of_injective ψ.injective).symm
    _ = Nat.card (pCoreOf 2 (Subgroup.centralizer
          ({tZero hS.card_K} :
            Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))))) := by rw [hmap]
    _ = 2 ^ 9 := card_pCoreOf_centralizer_tZero hS.card_K

theorem exists_ne_of_pCoreOf_conj_inf_centralizer [Finite G] [Finite K] (hG : IsCharTwoType G)
    (hS : LocalSetting hω b L φ Bs)
    {t : G} (ht : t ∈ Subgroup.normalizer (Bs : Set G)) (ht2 : orderOf t = 2)
    (htb : t * b * t⁻¹ = b⁻¹) (htL : t ∈ Subgroup.centralizer (L : Set G))
    {n : G} (hn : n ∈ Subgroup.normalizer (Bs : Set G)) (hnL : n * b * n⁻¹ ∈ L)
    (hnφ : φ ⟨n * b * n⁻¹, hnL⟩ = threeA hω)
    (htA : n⁻¹ * t * n ∈
      (L ⊓ Subgroup.normalizer (Bs : Set G)) ⊔ Subgroup.centralizer (Bs : Set G)) :
    ∃ x ∈ pCoreOf 2 (L.map (MulAut.conj n : G →* G) ⊓ Subgroup.centralizer {t}),
      ∃ y ∈ pCoreOf 2 (L.map (MulAut.conj n : G →* G) ⊓ Subgroup.centralizer {t}),
        x * y ≠ y * x := by
  classical
  obtain ⟨htn, g, hg⟩ := exists_conj_tZero hG hS ht ht2 htb htL hn hnL hnφ htA
  set M : Subgroup G := L.map (MulAut.conj n : G →* G)
  have htM : t ∈ M := by
    refine Subgroup.mem_map.mpr ⟨n⁻¹ * t * n, htn, ?_⟩
    change MulAut.conj n (n⁻¹ * t * n) = t
    rw [MulAut.conj_apply]
    group
  let φe : ↥M ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) := conjEquiv φ n
  let ψ : ↥M ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
    φe.trans (MulAut.conj g)
  have hφet : φe ⟨t, htM⟩ = φ ⟨n⁻¹ * t * n, htn⟩ := by
    have hmem : n * (n⁻¹ * t * n) * n⁻¹ ∈ L.map (MulAut.conj n : G →* G) := by
      have hval : n * (n⁻¹ * t * n) * n⁻¹ = t := by group
      rw [hval]
      exact htM
    have h := conjEquiv_apply φ n (x := n⁻¹ * t * n) htn hmem
    have helem : (⟨t, htM⟩ : ↥(L.map (MulAut.conj n : G →* G))) =
        ⟨n * (n⁻¹ * t * n) * n⁻¹, hmem⟩ := Subtype.ext (by group)
    change conjEquiv φ n ⟨t, htM⟩ = φ ⟨n⁻¹ * t * n, htn⟩
    rw [helem, h]
  have hψt : ψ ⟨t, htM⟩ = tZero hS.card_K := by
    change (MulAut.conj g) (φe ⟨t, htM⟩) = tZero hS.card_K
    rw [hφet, MulAut.conj_apply]
    exact hg
  have hmap := CFSG.GroupTheory.map_pCoreOf_inf_centralizer_mulEquiv ψ htM
  rw [hψt] at hmap
  obtain ⟨a, ha, c, hc, hne⟩ := exists_ne_of_pCoreOf_centralizer_tZero hS.card_K
  rw [← hmap] at ha hc
  obtain ⟨xa, hxa, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨xc, hxc, rfl⟩ := Subgroup.mem_map.mp hc
  refine ⟨xa, Subgroup.mem_subgroupOf.mp hxa, xc, Subgroup.mem_subgroupOf.mp hxc, ?_⟩
  intro hxy
  apply hne
  rw [← map_mul, ← map_mul]
  exact congrArg ψ (Subtype.ext hxy)

theorem eq_or_eq_of_le_pCoreOf_conj_inf_centralizer [Finite G] [Finite K] (hG : IsCharTwoType G)
    (hS : LocalSetting hω b L φ Bs)
    {t : G} (ht : t ∈ Subgroup.normalizer (Bs : Set G)) (ht2 : orderOf t = 2)
    (htb : t * b * t⁻¹ = b⁻¹) (htL : t ∈ Subgroup.centralizer (L : Set G))
    {n : G} (hn : n ∈ Subgroup.normalizer (Bs : Set G)) (hnL : n * b * n⁻¹ ∈ L)
    (hnφ : φ ⟨n * b * n⁻¹, hnL⟩ = threeA hω)
    (htA : n⁻¹ * t * n ∈
      (L ⊓ Subgroup.normalizer (Bs : Set G)) ⊔ Subgroup.centralizer (Bs : Set G)) {Y : Subgroup G}
    (hY₁ : Subgroup.zpowers t ≤ Y)
    (hY₂ : Y ≤ pCoreOf 2 (L.map (MulAut.conj n : G →* G) ⊓ Subgroup.centralizer {t}))
    (hLY : L ⊓ Subgroup.centralizer {n * b * n⁻¹} ≤ Subgroup.normalizer (Y : Set G)) :
    Y = Subgroup.zpowers t ∨
      Y = pCoreOf 2 (L.map (MulAut.conj n : G →* G) ⊓ Subgroup.centralizer {t}) := by
  classical
  obtain ⟨htn, g, hg⟩ := exists_conj_tZero hG hS ht ht2 htb htL hn hnL hnφ htA
  set M : Subgroup G := L.map (MulAut.conj n : G →* G)
  have htM : t ∈ M := by
    refine Subgroup.mem_map.mpr ⟨n⁻¹ * t * n, htn, ?_⟩
    change MulAut.conj n (n⁻¹ * t * n) = t
    rw [MulAut.conj_apply]
    group
  have hS' : LocalSetting hω (n * b * n⁻¹) M (conjEquiv φ n) Bs := hS.conj hn hnL hnφ
  let U := LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
  let φe : ↥M ≃* U := conjEquiv φ n
  have hφet : φe ⟨t, htM⟩ = φ ⟨n⁻¹ * t * n, htn⟩ := by
    have hmem : n * (n⁻¹ * t * n) * n⁻¹ ∈ L.map (MulAut.conj n : G →* G) := by
      have hval : n * (n⁻¹ * t * n) * n⁻¹ = t := by group
      rw [hval]
      exact htM
    have h := conjEquiv_apply φ n (x := n⁻¹ * t * n) htn hmem
    have helem : (⟨t, htM⟩ : ↥(L.map (MulAut.conj n : G →* G))) =
        ⟨n * (n⁻¹ * t * n) * n⁻¹, hmem⟩ := Subtype.ext (by group)
    change conjEquiv φ n ⟨t, htM⟩ = φ ⟨n⁻¹ * t * n, htn⟩
    rw [helem, h]
  let ψ : ↥M ≃* U := φe.trans (MulAut.conj g)
  have hψt : ψ ⟨t, htM⟩ = tZero hS.card_K := by
    change (MulAut.conj g) (φe ⟨t, htM⟩) = tZero hS.card_K
    rw [hφet, MulAut.conj_apply]
    exact hg
  let C : Subgroup G := Subgroup.centralizer ({n * b * n⁻¹} : Set G)
  let R : Subgroup G := C ⊓ Subgroup.centralizer (M : Set G)
  have hCNM : C ≤ Subgroup.normalizer (M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (show M ≤ C from hS'.le_centralizer)).mp
      (show (M.subgroupOf C).Normal from hS'.normal)
  let XL : Subgroup L := (blockFourU hS.card_K).comap φ.toMonoidHom
  let X : Subgroup G := XL.map L.subtype
  have hXLle : X ≤ L := Subgroup.map_subtype_le XL
  have hXC : X ≤ C := by
    intro x hx
    obtain ⟨xl, hxl, rfl⟩ := Subgroup.mem_map.mp hx
    have hφx : φ xl ∈ blockFourU hS.card_K := by
      simpa only [XL, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom] using hxl
    have hcent := blockFourU_le_centralizer_threeA hS.card_K hω hφx
    rw [Subgroup.mem_centralizer_singleton_iff] at hcent
    change (xl : G) ∈ Subgroup.centralizer ({n * b * n⁻¹} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    change (xl : G) * (n * b * n⁻¹) = (n * b * n⁻¹) * (xl : G)
    have hpre : (⟨(xl : G) * (n * b * n⁻¹), L.mul_mem xl.2 hnL⟩ : L) =
        ⟨(n * b * n⁻¹) * (xl : G), L.mul_mem hnL xl.2⟩ := by
      have h1 : (⟨(xl : G) * (n * b * n⁻¹), L.mul_mem xl.2 hnL⟩ : L) =
          xl * ⟨n * b * n⁻¹, hnL⟩ := Subtype.ext rfl
      have h2 : (⟨(n * b * n⁻¹) * (xl : G), L.mul_mem hnL xl.2⟩ : L) =
          ⟨n * b * n⁻¹, hnL⟩ * xl := Subtype.ext rfl
      rw [h1, h2]
      apply φ.injective
      rw [map_mul, map_mul]
      rw [hnφ]
      exact hcent
    exact congrArg Subtype.val hpre
  have hXt : X ≤ Subgroup.centralizer ({t} : Set G) := by
    intro x hx
    obtain ⟨xl, hxl, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp htL) xl.1 xl.2
  have hXY : X ≤ Subgroup.normalizer (Y : Set G) :=
    (le_inf hXLle hXC).trans hLY
  have hXNM : X ≤ Subgroup.normalizer (M : Set G) := hXC.trans hCNM
  have hXLmap : XL.map φ.toMonoidHom = blockFourU hS.card_K :=
    Subgroup.map_comap_eq_self_of_surjective φ.surjective _
  let eXφ : ↥XL ≃* ↥(XL.map φ.toMonoidHom) :=
    Subgroup.equivMapOfInjective XL φ.toMonoidHom φ.injective
  let eXL : ↥XL ≃* ↥(blockFourU hS.card_K) :=
    eXφ.trans (MulEquiv.subgroupCongr hXLmap)
  let eX' : ↥XL ≃* ↥X := Subgroup.equivMapOfInjective XL L.subtype L.subtype_injective
  let eX : ↥X ≃* ↥(blockFourU hS.card_K) := eX'.symm.trans eXL
  haveI hBLsimple : IsSimpleGroup ↥(blockFourU hS.card_K) := isSimpleGroup_blockFourU hS.card_K
  haveI hXsimple : IsSimpleGroup ↥X := MulEquiv.isSimpleGroup eX
  have hXcard : Nat.card ↥X = 25920 := by
    have h1 : Nat.card ↥XL = 25920 := by
      rw [Nat.card_congr eXL.toEquiv, card_blockFourU hS.card_K]
    rw [← Nat.card_congr eX'.toEquiv, h1]
  have hXR_M : X ≤ R ⊔ M := by
    set H : Subgroup G := R ⊔ M with hH
    obtain ⟨hHnorm, hidx⟩ : (H.subgroupOf C).Normal ∧ (H.subgroupOf C).index ∣ 6 := by
      have h := normal_and_index_dvd_six hS'
      simpa only [H, R, C] using h
    haveI : (H.subgroupOf C).Normal := hHnorm
    let q : ↥C →* (↥C ⧸ (H.subgroupOf C)) := QuotientGroup.mk' _
    let fq : ↥(X.subgroupOf C) →* (↥C ⧸ (H.subgroupOf C)) := q.comp (X.subgroupOf C).subtype
    haveI : IsSimpleGroup ↥(X.subgroupOf C) :=
      MulEquiv.isSimpleGroup (Subgroup.subgroupOfEquivOfLe hXC)
    rcases Subgroup.Normal.eq_bot_or_eq_top fq.ker with hbot | htop
    · exfalso
      have hinj : Function.Injective fq := (MonoidHom.ker_eq_bot_iff fq).mp hbot
      have hle : Nat.card ↥(X.subgroupOf C) ≤ Nat.card (↥C ⧸ (H.subgroupOf C)) :=
        Nat.card_le_card_of_injective fq hinj
      have hq2 : Nat.card (↥C ⧸ (H.subgroupOf C)) ≤ 6 := by
        rw [← Subgroup.index_eq_card]
        exact Nat.le_of_dvd (by norm_num) hidx
      have hXc : Nat.card ↥(X.subgroupOf C) = 25920 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXC).toEquiv, hXcard]
      omega
    · intro x hx
      have hxC : x ∈ C := hXC hx
      have hxsub : (⟨x, hxC⟩ : ↥C) ∈ X.subgroupOf C := by
        rw [Subgroup.mem_subgroupOf]
        exact hx
      have hker : (⟨⟨x, hxC⟩, hxsub⟩ : ↥(X.subgroupOf C)) ∈ fq.ker := by
        rw [htop]
        exact Subgroup.mem_top _
      have hq1 : q ⟨x, hxC⟩ = 1 := by
        have h := MonoidHom.mem_ker.mp hker
        change q ⟨x, hxC⟩ = 1 at h
        exact h
      exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (⟨x, hxC⟩ : ↥C)).mp hq1)
  have he3 : orderOf (n * b * n⁻¹) = 3 := by
    have h : orderOf (n * b * n⁻¹) = orderOf b := by
      rw [show n * b * n⁻¹ = (MulAut.conj n) b from rfl]
      exact orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective b
    rw [h, hS.orderOf_b]
  have hRodd : Odd (Nat.card R) := by
    have hOodd : Odd (Nat.card (relPPrimeCore 3 C)) := by
      have h := odd_card_relPPrimeCore hG hS'
      simpa only [C] using h
    have hOcop : Nat.Coprime 3 (Nat.card (relPPrimeCore 3 C)) :=
      coprime_card_relPPrimeCore
        Nat.prime_three C
    have hRe : R = relPPrimeCore 3 C ⊔ Subgroup.zpowers (n * b * n⁻¹) := by
      have h := centralizer_inf_eq hS'
      simpa only [R, C] using h
    have hOleC : relPPrimeCore 3 C ≤ C :=
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le C
    have hOnormal : ((relPPrimeCore 3 C).subgroupOf C).Normal :=
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
        Nat.prime_three C
    have hCnO : C ≤ Subgroup.normalizer (relPPrimeCore 3 C : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hOleC).mp hOnormal
    have heC : (n * b * n⁻¹) ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have hnormO : Subgroup.zpowers (n * b * n⁻¹) ≤
        Subgroup.normalizer (relPPrimeCore 3 C : Set G) :=
      (Subgroup.zpowers_le.mpr heC).trans hCnO
    have hdisj : Disjoint (relPPrimeCore 3 C) (Subgroup.zpowers (n * b * n⁻¹)) := by
      apply Subgroup.disjoint_of_coprime_natCard
      rw [Nat.card_zpowers, he3]
      exact hOcop.symm
    have hcardR : Nat.card R = Nat.card (relPPrimeCore 3 C) * 3 := by
      rw [hRe, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnormO hdisj,
        Nat.card_zpowers, he3]
    rw [hcardR]
    exact hOodd.mul (by norm_num : Odd 3)
  have hXRbot : X ⊓ R = ⊥ := by
    have hRnormalC : (R.subgroupOf C).Normal := by
      rw [Subgroup.normal_subgroupOf_iff (inf_le_left : R ≤ C)]
      intro r c hr hc
      refine ⟨C.mul_mem (C.mul_mem hc hr.1) (C.inv_mem hc), ?_⟩
      change c * r * c⁻¹ ∈ Subgroup.centralizer (M : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have hcM' : c⁻¹ * m * c ∈ M := by
        have h := (Subgroup.mem_normalizer_iff.mp (hCNM (C.inv_mem hc)) m).mp hm
        simpa using h
      have hrm' : r * (c⁻¹ * m * c) = (c⁻¹ * m * c) * r :=
        ((Subgroup.mem_centralizer_iff.mp hr.2) (c⁻¹ * m * c) hcM').symm
      calc m * (c * r * c⁻¹) = c * (c⁻¹ * m * c) * r * c⁻¹ := by group
        _ = c * ((c⁻¹ * m * c) * r) * c⁻¹ := by group
        _ = c * (r * (c⁻¹ * m * c)) * c⁻¹ := by rw [← hrm']
        _ = (c * r * c⁻¹) * m := by group
    have hXNR : X ≤ Subgroup.normalizer (R : Set G) :=
      hXC.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_left : R ≤ C)).mp hRnormalC)
    have hnormal : ((X ⊓ R).subgroupOf X).Normal := by
      rw [Subgroup.normal_subgroupOf_iff (inf_le_left : X ⊓ R ≤ X)]
      intro r x hr hx
      exact ⟨X.mul_mem (X.mul_mem hx hr.1) (X.inv_mem hx),
        (Subgroup.mem_normalizer_iff.mp (hXNR hx) r).mp hr.2⟩
    haveI : ((X ⊓ R).subgroupOf X).Normal := hnormal
    rcases Subgroup.Normal.eq_bot_or_eq_top ((X ⊓ R).subgroupOf X) with hbot | htop
    · exact (Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le inf_le_left
    · exfalso
      have hXR : X ≤ R := by
        intro x hx
        have hxmem : (⟨x, hx⟩ : ↥X) ∈ (X ⊓ R).subgroupOf X := by
          rw [htop]
          exact Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.mp hxmem).2
      have hoddX : Odd (Nat.card ↥X) := hRodd.of_dvd_nat (Subgroup.card_dvd_of_le hXR)
      rw [hXcard] at hoddX
      norm_num at hoddX

  let Q : Subgroup G := pCoreOf 2 (M ⊓ Subgroup.centralizer {t})
  have hQleM : Q ≤ M :=
    (Subgroup.map_subtype_le (CFSG.pCore 2 ↥(M ⊓ Subgroup.centralizer {t}))).trans inf_le_left
  let QM : Subgroup ↥M := Q.subgroupOf M
  have hYleM : Y ≤ M := hY₂.trans hQleM
  let YM : Subgroup ↥M := Y.subgroupOf M
  have hMRbot : M ⊓ R = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    have hmcenter : (⟨m, hm.1⟩ : ↥M) ∈ Subgroup.center ↥M := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hm.2.2) (y : G) y.2
    rw [center_L_eq_bot hS'] at hmcenter
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hmcenter)
  have hex : ∀ x : ↥X, ∃ m : ↥M, (x : G) * (m : G)⁻¹ ∈ R := by
    intro x
    have hRM : (↑(R ⊔ M) : Set G) = (R : Set G) * (M : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right R M
        (inf_le_right.trans (Subgroup.centralizer_le_normalizer (M : Set G)))
    have hx : (x : G) ∈ (R : Set G) * (M : Set G) := by
      rw [← hRM]
      exact hXR_M x.2
    obtain ⟨r, hr, m, hm, hrm⟩ := hx
    refine ⟨⟨m, hm⟩, ?_⟩
    rw [← hrm]
    simpa using hr
  have huniq : ∀ (x : ↥X) (m₁ m₂ : ↥M), (x : G) * (m₁ : G)⁻¹ ∈ R →
      (x : G) * (m₂ : G)⁻¹ ∈ R → m₁ = m₂ := by
    intro x m₁ m₂ h₁ h₂
    have hmemR : (m₁ : G) * (m₂ : G)⁻¹ ∈ R := by
      have h := R.mul_mem (R.inv_mem h₁) h₂
      convert h using 1
      group
    have hmemM : (m₁ : G) * (m₂ : G)⁻¹ ∈ M :=
      M.mul_mem m₁.2 (M.inv_mem m₂.2)
    have hbot : (m₁ : G) * (m₂ : G)⁻¹ = 1 := by
      have h : (m₁ : G) * (m₂ : G)⁻¹ ∈ M ⊓ R := ⟨hmemM, hmemR⟩
      rw [hMRbot, Subgroup.mem_bot] at h
      exact h
    apply Subtype.ext
    have h := congrArg (fun z => z * (m₂ : G)) hbot
    simpa using h
  let f : ↥X →* ↥M :=
    { toFun := fun x => (hex x).choose
      map_one' := by
        refine huniq 1 (hex 1).choose ⟨1, M.one_mem⟩ (hex 1).choose_spec ?_
        simpa using R.one_mem
      map_mul' := fun x y => by
        symm
        refine huniq (x * y) ((hex x).choose * (hex y).choose) (hex (x * y)).choose ?_
          (hex (x * y)).choose_spec
        have hx := (hex x).choose_spec
        have hy := (hex y).choose_spec
        have hRCM : R ≤ Subgroup.centralizer (M : Set G) := inf_le_right
        set p : G := ((hex x).choose : G) with hp
        set q : G := ((hex y).choose : G) with hq
        set ry : G := (y : G) * q⁻¹ with hry
        have hryR : ry ∈ R := hy
        have hcommp : Commute p ry :=
          Subgroup.mem_centralizer_iff.mp (hRCM hryR) p ((hex x).choose).2
        have hconj : p * ry * p⁻¹ = ry := by
          rw [hcommp.eq]
          group
        have hx'' : (x : G) * (y : G) * (q⁻¹ * p⁻¹) =
            ((x : G) * p⁻¹) * (p * ((y : G) * q⁻¹) * p⁻¹) := by
          conv_lhs => rw [show (x : G) = ((x : G) * p⁻¹) * p from by group]
          group
        have hmain : ((x * y : ↥X) : G) * (((hex x).choose * (hex y).choose : ↥M) : G)⁻¹ =
            ((x : G) * p⁻¹) * ry := by
          simp only [Subgroup.coe_mul, mul_inv_rev]
          calc (x : G) * (y : G) * (q⁻¹ * p⁻¹)
              = ((x : G) * p⁻¹) * (p * ((y : G) * q⁻¹) * p⁻¹) := hx''
            _ = ((x : G) * p⁻¹) * (p * ry * p⁻¹) := by
                  rw [show (y : G) * q⁻¹ = ry from rfl]
            _ = ((x : G) * p⁻¹) * ry := by rw [hconj]
        rw [hmain]
        exact R.mul_mem hx hryR }
  have hf_spec : ∀ x : ↥X, (x : G) * (f x : G)⁻¹ ∈ R := fun x => (hex x).choose_spec
  have hfinj : Function.Injective f := by
    intro x y hxy
    have hx := hf_spec x
    have hy := hf_spec y
    have hmemR : (x : G) * (y : G)⁻¹ ∈ R := by
      have h := R.mul_mem hx (R.inv_mem hy)
      rw [hxy] at h
      convert h using 1
      group
    have hmemX : (x : G) * (y : G)⁻¹ ∈ X := X.mul_mem x.2 (X.inv_mem y.2)
    have hbot : (x : G) * (y : G)⁻¹ = 1 := by
      have h : (x : G) * (y : G)⁻¹ ∈ X ⊓ R := ⟨hmemX, hmemR⟩
      rw [hXRbot, Subgroup.mem_bot] at h
      exact h
    apply Subtype.ext
    have h := congrArg (fun z => z * (y : G)) hbot
    simpa using h
  let X'M : Subgroup ↥M := f.range
  have hX'M_simple : IsSimpleGroup X'M :=
    MulEquiv.isSimpleGroup (MonoidHom.ofInjective (f := f) hfinj).symm
  have hX'M_card : Nat.card X'M = 25920 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (f := f) hfinj).toEquiv, hXcard]
  have hX'M_C : X'M ≤ Subgroup.centralizer ({⟨t, htM⟩} : Set ↥M) := by
    intro m hm
    obtain ⟨x, rfl⟩ := hm
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hxX : (x : G) ∈ Subgroup.centralizer ({t} : Set G) := hXt x.2
    have hxcomm : (x : G) * t = t * (x : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp hxX
    have hr := hf_spec x
    have hrcomm : ((x : G) * (f x : G)⁻¹) * t = t * ((x : G) * (f x : G)⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp hr.2 t htM).symm
    have hfx : (f x : G) = ((x : G) * (f x : G)⁻¹)⁻¹ * (x : G) := by group
    have hconj : (f x : G) * t * (f x : G)⁻¹ = t := by
      calc (f x : G) * t * (f x : G)⁻¹
          = ((x : G) * (f x : G)⁻¹)⁻¹ * ((x : G) * t * (x : G)⁻¹) *
              ((x : G) * (f x : G)⁻¹) := by
            rw [hfx]
            group
        _ = ((x : G) * (f x : G)⁻¹)⁻¹ * t * ((x : G) * (f x : G)⁻¹) := by
            rw [show (x : G) * t * (x : G)⁻¹ = t from by rw [hxcomm]; group]
        _ = t := by
            calc ((x : G) * (f x : G)⁻¹)⁻¹ * t * ((x : G) * (f x : G)⁻¹)
                = ((x : G) * (f x : G)⁻¹)⁻¹ *
                    (t * ((x : G) * (f x : G)⁻¹)) := by group
              _ = ((x : G) * (f x : G)⁻¹)⁻¹ *
                    (((x : G) * (f x : G)⁻¹) * t) := by rw [← hrcomm]
              _ = t := by group
    calc (f x : G) * t = ((f x : G) * t * (f x : G)⁻¹) * (f x : G) := by group
      _ = t * (f x : G) := by rw [hconj]
  have hconjY : ∀ (z : ↥X) (w : G), w ∈ Y → (f z : G) * w * (f z : G)⁻¹ ∈ Y := by
    intro z w hw
    have hz := hf_spec z
    have hzw : (z : G) * w * (z : G)⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (hXY z.2) w).mp hw
    have hrzY : ((z : G) * (f z : G)⁻¹) ∈ Subgroup.centralizer (Y : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w' hw'
      exact Subgroup.mem_centralizer_iff.mp hz.2 w' (hYleM hw')
    have hrzY' : ((z : G) * w * (z : G)⁻¹) * ((z : G) * (f z : G)⁻¹) =
        ((z : G) * (f z : G)⁻¹) * ((z : G) * w * (z : G)⁻¹) :=
      Subgroup.mem_centralizer_iff.mp hrzY ((z : G) * w * (z : G)⁻¹) hzw
    have hfz : (f z : G) = ((z : G) * (f z : G)⁻¹)⁻¹ * (z : G) := by group
    have hconj : (f z : G) * w * (f z : G)⁻¹ =
        ((z : G) * (f z : G)⁻¹)⁻¹ * ((z : G) * w * (z : G)⁻¹) *
          ((z : G) * (f z : G)⁻¹) := by
      rw [hfz]
      group
    rw [hconj]
    have hred : ((z : G) * (f z : G)⁻¹)⁻¹ * ((z : G) * w * (z : G)⁻¹) *
          ((z : G) * (f z : G)⁻¹) = ((z : G) * w * (z : G)⁻¹) := by
      calc ((z : G) * (f z : G)⁻¹)⁻¹ * ((z : G) * w * (z : G)⁻¹) *
            ((z : G) * (f z : G)⁻¹)
          = ((z : G) * (f z : G)⁻¹)⁻¹ *
              (((z : G) * w * (z : G)⁻¹) * ((z : G) * (f z : G)⁻¹)) := by group
        _ = ((z : G) * (f z : G)⁻¹)⁻¹ *
              (((z : G) * (f z : G)⁻¹) * ((z : G) * w * (z : G)⁻¹)) := by rw [← hrzY']
        _ = ((z : G) * w * (z : G)⁻¹) := by group
    rw [hred]
    exact hzw
  have hX'M_NY : X'M ≤ Subgroup.normalizer (YM : Set ↥M) := by
    intro m hm
    obtain ⟨x, rfl⟩ := hm
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [Subgroup.mem_subgroupOf]
      exact hconjY x y (Subgroup.mem_subgroupOf.mp hy)
    · intro hy
      have hyY : (f x : G) * (y : G) * (f x : G)⁻¹ ∈ Y := Subgroup.mem_subgroupOf.mp hy
      have h1 := hconjY x⁻¹ ((f x : G) * (y : G) * (f x : G)⁻¹) hyY
      have h2 : (y : G) ∈ Y := by
        have h1' := h1
        rw [show (f (x⁻¹) : G) = (f x : G)⁻¹ from by rw [map_inv]; rfl] at h1'
        convert h1' using 1 <;> group
      rw [Subgroup.mem_subgroupOf]
      exact h2
  have hXG_NQ : X'M.map M.subtype ≤ Subgroup.normalizer (Q : Set G) := by
    have hXG_NH0 : X'M.map M.subtype ≤
        Subgroup.normalizer ((M ⊓ Subgroup.centralizer ({t} : Set G)) : Set G) := by
      intro g hg
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hg
      obtain ⟨x, rfl⟩ := hm
      have hmC : (f x : ↥M) ∈ Subgroup.centralizer ({⟨t, htM⟩} : Set ↥M) :=
        hX'M_C (show f x ∈ X'M from ⟨x, rfl⟩)
      have hmCt : (f x : G) ∈ Subgroup.centralizer ({t} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hmC ⊢
        exact congrArg Subtype.val hmC
      change ((f x : G)) ∈ Subgroup.normalizer
        ((M ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G)
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        refine ⟨M.mul_mem (M.mul_mem (f x).2 hz.1) (M.inv_mem (f x).2), ?_⟩
        change ((f x : G) * z * (f x : G)⁻¹) ∈ Subgroup.centralizer ({t} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact mul_conj_commute (Subgroup.mem_centralizer_singleton_iff.mp hmCt)
          (Subgroup.mem_centralizer_singleton_iff.mp hz.2)
      · intro hz
        have hxinv : (f x : G)⁻¹ * t = t * (f x : G)⁻¹ := by
          have h := Subgroup.mem_centralizer_singleton_iff.mp hmCt
          calc (f x : G)⁻¹ * t = (f x : G)⁻¹ * (t * (f x : G)) * (f x : G)⁻¹ := by group
            _ = (f x : G)⁻¹ * ((f x : G) * t) * (f x : G)⁻¹ := by rw [← h]
            _ = t * (f x : G)⁻¹ := by group
        have hconjInv : ∀ z : G, z ∈ M ⊓ Subgroup.centralizer ({t} : Set G) →
            (f x : G)⁻¹ * z * ((f x : G)⁻¹)⁻¹ ∈
              M ⊓ Subgroup.centralizer ({t} : Set G) := by
          intro z hz'
          refine ⟨by simpa using M.mul_mem (M.mul_mem (M.inv_mem (f x).2) hz'.1) (f x).2, ?_⟩
          change ((f x : G)⁻¹ * z * ((f x : G)⁻¹)⁻¹) ∈ Subgroup.centralizer ({t} : Set G)
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact mul_conj_commute hxinv (Subgroup.mem_centralizer_singleton_iff.mp hz'.2)
        have hmem := hconjInv ((f x : G) * z * (f x : G)⁻¹) hz
        obtain ⟨h1, h2⟩ := hmem
        have hz_eq : ((f x : G)⁻¹ * ((f x : G) * z * (f x : G)⁻¹) * ((f x : G)⁻¹)⁻¹) = z := by
          group
        refine ⟨?_, ?_⟩
        · rwa [hz_eq] at h1
        · change (z : G) ∈ Subgroup.centralizer ({t} : Set G)
          rwa [hz_eq] at h2
    exact hXG_NH0.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf
      (r := 2) (H := M ⊓ Subgroup.centralizer ({t} : Set G)))
  have hX'M_normQ : X'M ≤ Subgroup.normalizer (QM : Set ↥M) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hmy : (m : G) * (y : G) * (m : G)⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp
          (hXG_NQ (Subgroup.mem_map.mpr ⟨m, hm, rfl⟩)) (y : G)).mp
          (Subgroup.mem_subgroupOf.mp hy)
      exact Subgroup.mem_subgroupOf.mpr (by
        show ((m * y * m⁻¹ : ↥M) : G) ∈ Q
        exact hmy)
    · intro hy
      have hyQ : ((m : G) * (y : G) * (m : G)⁻¹) ∈ Q := Subgroup.mem_subgroupOf.mp hy
      have h1 := (Subgroup.mem_normalizer_iff.mp
        (hXG_NQ (Subgroup.mem_map.mpr ⟨m⁻¹, X'M.inv_mem hm, rfl⟩))
        ((m : G) * (y : G) * (m : G)⁻¹)).mp hyQ
      have h2 : (y : G) ∈ Q := by
        have hy_eq : (M.subtype m⁻¹ * ((m : G) * (y : G) * (m : G)⁻¹) * (M.subtype m⁻¹)⁻¹) = y := by
          change ((m : G)⁻¹ * ((m : G) * (y : G) * (m : G)⁻¹) * (((m : G))⁻¹)⁻¹) = y
          group
        rwa [hy_eq] at h1
      exact Subgroup.mem_subgroupOf.mpr h2
  have hX'M_Q : X'M ⊓ QM = ⊥ := by
    have hQ2M : IsPGroup 2 QM :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2)
        (H := M ⊓ Subgroup.centralizer ({t} : Set G))).of_equiv
        (Subgroup.subgroupOfEquivOfLe hQleM).symm
    have hnormal : ((X'M ⊓ QM).subgroupOf X'M).Normal := by
      rw [Subgroup.normal_subgroupOf_iff (inf_le_left : X'M ⊓ QM ≤ X'M)]
      intro r x hr hx
      exact ⟨X'M.mul_mem (X'M.mul_mem hx hr.1) (X'M.inv_mem hx),
        (Subgroup.mem_normalizer_iff.mp (hX'M_normQ hx) r).mp hr.2⟩
    haveI : IsSimpleGroup X'M := hX'M_simple
    haveI : ((X'M ⊓ QM).subgroupOf X'M).Normal := hnormal
    rcases Subgroup.Normal.eq_bot_or_eq_top ((X'M ⊓ QM).subgroupOf X'M) with hbot | htop
    · exact (Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le inf_le_left
    · exfalso
      have hle : X'M ≤ QM := by
        intro x hx
        have hxmem : (⟨x, hx⟩ : ↥X'M) ∈ (X'M ⊓ QM).subgroupOf X'M := by
          rw [htop]
          exact Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.mp hxmem).2
      have h2 : IsPGroup 2 X'M := hQ2M.to_le hle
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
      have h3 : (3 : ℕ) ∣ Nat.card X'M := by
        rw [hX'M_card]
        norm_num
      rw [hk] at h3
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hQmapψ : QM.map ψ.toMonoidHom =
      pCoreOf 2 (Subgroup.centralizer ({tZero hS.card_K} : Set U)) := by
    have h := CFSG.GroupTheory.map_pCoreOf_inf_centralizer_mulEquiv ψ htM
    rw [show (ψ ⟨t, htM⟩) = tZero hS.card_K from hψt] at h
    exact h
  let XU : Subgroup U := X'M.map ψ.toMonoidHom
  let YU : Subgroup U := YM.map ψ.toMonoidHom
  have hXU_le : XU ≤ Subgroup.centralizer ({tZero hS.card_K} : Set U) := by
    have h := Subgroup.map_mono (f := ψ.toMonoidHom) hX'M_C
    rwa [CFSG.GroupTheory.map_centralizer_eq_of_mulEquiv, Set.image_singleton,
      show ψ.toMonoidHom ⟨t, htM⟩ = tZero hS.card_K from hψt] at h
  have hXU_card : Nat.card XU = 25920 := by
    rw [show XU = X'M.map ψ.toMonoidHom from rfl,
      Subgroup.card_map_of_injective ψ.injective, hX'M_card]
  have hXU_Q : XU ⊓ pCoreOf 2 (Subgroup.centralizer ({tZero hS.card_K} : Set U)) = ⊥ := by
    rw [← hQmapψ, ← Subgroup.map_inf X'M QM ψ.toMonoidHom ψ.injective, hX'M_Q,
      Subgroup.map_bot]
  have hYU_z : Subgroup.zpowers (tZero hS.card_K) ≤ YU := by
    have h1 : Subgroup.zpowers (⟨t, htM⟩ : ↥M) ≤ YM := by
      refine Subgroup.zpowers_le.mpr ?_
      rw [Subgroup.mem_subgroupOf]
      exact hY₁ (Subgroup.mem_zpowers t)
    have h2 : (Subgroup.zpowers (⟨t, htM⟩ : ↥M)).map ψ.toMonoidHom =
        Subgroup.zpowers (tZero hS.card_K) := by
      rw [MonoidHom.map_zpowers]
      exact congrArg Subgroup.zpowers (show ψ.toMonoidHom ⟨t, htM⟩ = tZero hS.card_K from hψt)
    rw [← h2]
    exact Subgroup.map_mono (f := ψ.toMonoidHom) h1
  have hYU_le : YU ≤ pCoreOf 2 (Subgroup.centralizer ({tZero hS.card_K} : Set U)) := by
    rw [← hQmapψ]
    exact Subgroup.map_mono (f := ψ.toMonoidHom) (Subgroup.subgroupOf_mono M hY₂)
  have hXU_norm : XU ≤ Subgroup.normalizer (YU : Set U) := by
    have h := Subgroup.map_mono (f := ψ.toMonoidHom) hX'M_NY
    rwa [Subgroup.map_normalizer_eq_of_bijective YM ψ.bijective] at h
  have hkey := eq_or_eq_of_le_pCoreOf_centralizer_tZero hS.card_K
    (X := XU) (Y := YU) hXU_le hXU_card hXU_Q hYU_z hYU_le hXU_norm
  rcases hkey with hz | hQ
  · left
    have hYM : YM = Subgroup.zpowers (⟨t, htM⟩ : ↥M) := by
      apply Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective
      rw [show YM.map ψ.toMonoidHom = YU from rfl, hz, MonoidHom.map_zpowers]
      exact congrArg Subgroup.zpowers
        (show tZero hS.card_K = ψ.toMonoidHom ⟨t, htM⟩ from hψt.symm)
    calc Y = (Y.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hYleM).symm
      _ = (Subgroup.zpowers (⟨t, htM⟩ : ↥M)).map M.subtype := by
            rw [show Y.subgroupOf M = YM from rfl, hYM]
      _ = Subgroup.zpowers t := by
            rw [MonoidHom.map_zpowers]
            rfl
  · right
    have hYM : YM = QM := by
      apply Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective
      rw [show YM.map ψ.toMonoidHom = YU from rfl, hQ, hQmapψ]
    calc Y = (Y.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hYleM).symm
      _ = (Q.subgroupOf M).map M.subtype := by
            rw [show Y.subgroupOf M = YM from rfl, hYM]
      _ = Q := Subgroup.map_subgroupOf_eq_of_le hQleM

theorem centralizer_inf_pCoreOf_conj_inf_centralizer [Finite G] [Finite K] (hG : IsCharTwoType G)
    (hS : LocalSetting hω b L φ Bs)
    {t : G} (ht : t ∈ Subgroup.normalizer (Bs : Set G)) (ht2 : orderOf t = 2)
    (htb : t * b * t⁻¹ = b⁻¹) (htL : t ∈ Subgroup.centralizer (L : Set G))
    {n : G} (hn : n ∈ Subgroup.normalizer (Bs : Set G)) (hnL : n * b * n⁻¹ ∈ L)
    (hnφ : φ ⟨n * b * n⁻¹, hnL⟩ = threeA hω)
    (htA : n⁻¹ * t * n ∈
      (L ⊓ Subgroup.normalizer (Bs : Set G)) ⊔ Subgroup.centralizer (Bs : Set G)) :
    Subgroup.centralizer ((Bs ⊓ L : Subgroup G) : Set G) ⊓
        pCoreOf 2 (L.map (MulAut.conj n : G →* G) ⊓ Subgroup.centralizer {t}) =
      Subgroup.zpowers t := by
  classical
  obtain ⟨htn, g, hg⟩ := exists_conj_tZero hG hS ht ht2 htb htL hn hnL hnφ htA
  obtain ⟨htn₂, huN₂, hu2₂, hfix₂⟩ :=
    exists_mem_normalizer_torU hG hS ht ht2 htb htL hn hnL hnφ htA
  set M : Subgroup G := L.map (MulAut.conj n : G →* G)
  have htM : t ∈ M := by
    refine Subgroup.mem_map.mpr ⟨n⁻¹ * t * n, htn, ?_⟩
    change MulAut.conj n (n⁻¹ * t * n) = t
    rw [MulAut.conj_apply]
    group
  have hS' : LocalSetting hω (n * b * n⁻¹) M (conjEquiv φ n) Bs := hS.conj hn hnL hnφ
  let U := LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
  let φe : ↥M ≃* U := conjEquiv φ n
  have hφet : φe ⟨t, htM⟩ = φ ⟨n⁻¹ * t * n, htn⟩ := by
    have hmem : n * (n⁻¹ * t * n) * n⁻¹ ∈ L.map (MulAut.conj n : G →* G) := by
      have hval : n * (n⁻¹ * t * n) * n⁻¹ = t := by group
      rw [hval]
      exact htM
    have h := conjEquiv_apply φ n (x := n⁻¹ * t * n) htn hmem
    have helem : (⟨t, htM⟩ : ↥(L.map (MulAut.conj n : G →* G))) =
        ⟨n * (n⁻¹ * t * n) * n⁻¹, hmem⟩ := Subtype.ext (by group)
    change conjEquiv φ n ⟨t, htM⟩ = φ ⟨n⁻¹ * t * n, htn⟩
    rw [helem, h]
  set u : U := φe ⟨t, htM⟩ with hu_def
  have hbridge : u = φ ⟨n⁻¹ * t * n, htn₂⟩ := by
    rw [hφet]
  have huN : u ∈ Subgroup.normalizer (torU K : Set U) := by
    rw [hbridge]; exact huN₂
  have hu2 : orderOf u = 2 := by
    rw [hbridge]; exact hu2₂
  have hfix : Nat.card ↥(torU K ⊓ Subgroup.centralizer ({u} : Set U)) = 3 ^ 3 := by
    rw [hbridge]; exact hfix₂
  set Q : Subgroup G := pCoreOf 2 (M ⊓ Subgroup.centralizer {t})
  set E : Subgroup G := Bs ⊓ L
  set Be : Subgroup G := Bs ⊓ M
  set D : Subgroup G := Be ⊓ Subgroup.centralizer ({t} : Set G)
  have hDE : D ≤ E := by
    intro y hy
    obtain ⟨hyBe, hyt⟩ := hy
    obtain ⟨hyBs, hyM⟩ := hyBe
    obtain ⟨p, hpP, z, hzB, hpy⟩ := exists_mul_eq_of_mem_Bs hS hyBs
    have hzC : z ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp htL) z hzB.2
    have hp_inv : t * p * t⁻¹ = p⁻¹ := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hpP
      rw [← hk]
      calc t * b ^ k * t⁻¹ = (MulAut.conj t) (b ^ k) := by rw [MulAut.conj_apply]
        _ = ((MulAut.conj t) b) ^ k := by rw [map_zpow]
        _ = (b⁻¹) ^ k := by rw [MulAut.conj_apply, htb]
        _ = (b ^ k)⁻¹ := by rw [inv_zpow]
    have hconjz : t * z * t⁻¹ = z := by
      have hzt : z * t = t * z := Subgroup.mem_centralizer_singleton_iff.mp hzC
      calc t * z * t⁻¹ = (z * t) * t⁻¹ := by rw [hzt]
        _ = z := by group
    have hconj_y : t * y * t⁻¹ = p⁻¹ * z := by
      rw [← hpy]
      calc t * (p * z) * t⁻¹ = (t * p * t⁻¹) * (t * z * t⁻¹) := by group
        _ = p⁻¹ * z := by rw [hp_inv, hconjz]
    have hconj_y' : t * y * t⁻¹ = y := by
      have hyt' : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp hyt
      calc t * y * t⁻¹ = (t * y) * t⁻¹ := by group
        _ = (y * t) * t⁻¹ := by rw [hyt']
        _ = y := by group
    have hp_inv_eq : p⁻¹ = p := by
      exact mul_right_cancel (by rw [← hconj_y, hconj_y', hpy])
    have hp2 : p ^ 2 = 1 := by
      have h : p * p⁻¹ = 1 := mul_inv_cancel p
      rw [hp_inv_eq] at h
      simpa [pow_two] using h
    have hp3 : p ^ 3 = 1 := by
      exact orderOf_dvd_iff_pow_eq_one.mp (by
        rw [← hS.orderOf_b]
        exact orderOf_dvd_of_mem_zpowers hpP)
    have hp1 : p = 1 := by
      calc p = p * p ^ 2 := by rw [hp2, mul_one]
        _ = p ^ 3 := by group
        _ = 1 := hp3
    have hyz : y = z := by rw [← hpy, hp1, one_mul]
    exact ⟨hyBs, by rw [hyz]; exact hzB.2⟩
  have htCE : t ∈ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (Subgroup.mem_centralizer_iff.mp htL) e he.2
  have htQ : t ∈ Q := by
    have htC : t ∈ Subgroup.centralizer ({t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have htH : t ∈ M ⊓ Subgroup.centralizer ({t} : Set G) := ⟨htM, htC⟩
    have hzp_le : Subgroup.zpowers t ≤ M ⊓ Subgroup.centralizer ({t} : Set G) :=
      Subgroup.zpowers_le.mpr htH
    have hnorm : ((Subgroup.zpowers t).subgroupOf
        (M ⊓ Subgroup.centralizer ({t} : Set G))).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hzp_le]
      intro x hx
      have hxcent : x ∈ Subgroup.centralizer (Subgroup.zpowers t : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact (Commute.zpow_left
          (Subgroup.mem_centralizer_singleton_iff.mp hx.2).symm k).eq
      exact Subgroup.centralizer_le_normalizer (Subgroup.zpowers t : Set G) hxcent
    have hp : IsPGroup 2 (Subgroup.zpowers t) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, ht2, pow_one]
    exact CFSG.LieType.BorelTits.le_pCoreOf (r := 2) hzp_le hnorm hp
      (Subgroup.mem_zpowers t)
  have hQleM : Q ≤ M :=
    (Subgroup.map_subtype_le (CFSG.pCore 2 ↥(M ⊓ Subgroup.centralizer {t}))).trans
      inf_le_left
  set H : Subgroup G := Subgroup.centralizer (E : Set G) ⊓ Q
  have hHleM : H ≤ M := inf_le_right.trans hQleM
  have hQmap : (Q.subgroupOf M).map φe.toMonoidHom =
      pCoreOf 2 (Subgroup.centralizer ({u} : Set U)) := by
    rw [show Q = pCoreOf 2 (M ⊓ Subgroup.centralizer {t}) from rfl]
    have h := CFSG.GroupTheory.map_pCoreOf_inf_centralizer_mulEquiv φe htM
    rw [show (φe ⟨t, htM⟩) = u from rfl] at h
    exact h
  have hcentM : (Subgroup.centralizer ({t} : Set G)).subgroupOf M =
      Subgroup.centralizer ({⟨t, htM⟩} : Set ↥M) :=
    CFSG.GroupTheory.centralizer_subgroupOf_singleton htM
  have hcentMmap : ((Subgroup.centralizer ({t} : Set G)).subgroupOf M).map φe.toMonoidHom =
      Subgroup.centralizer ({u} : Set U) := by
    rw [hcentM, CFSG.GroupTheory.map_centralizer_eq_of_mulEquiv φe
      ({⟨t, htM⟩} : Set ↥M), Set.image_singleton]
    rfl
  have hDmap : (D.subgroupOf M).map φe.toMonoidHom =
      torU K ⊓ Subgroup.centralizer ({u} : Set U) := by
    have hsub : D.subgroupOf M = ((Bs ⊓ M).subgroupOf M) ⊓
        (Subgroup.centralizer ({t} : Set G)).subgroupOf M := by
      simp only [D, Be, Subgroup.subgroupOf, Subgroup.comap_inf]
    rw [hsub, Subgroup.map_inf _ _ _ φe.injective, hS'.map_inf, hcentMmap]
  have hH_cent : H.subgroupOf M ≤
      Subgroup.centralizer ((D.subgroupOf M) : Set ↥M) := by
    intro h hh
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hhE : (h : G) ∈ Subgroup.centralizer (E : Set G) := (Subgroup.mem_subgroupOf.mp hh).1
    have hdE : (d : G) ∈ E := hDE (Subgroup.mem_subgroupOf.mp hd)
    have hcomm : (d : G) * (h : G) = (h : G) * (d : G) :=
      (Subgroup.mem_centralizer_iff.mp hhE) d hdE
    apply Subtype.ext
    simpa only [Subgroup.coe_mul] using hcomm
  have hmap1_raw : (H.subgroupOf M).map φe.toMonoidHom ≤
      Subgroup.centralizer (((D.subgroupOf M).map φe.toMonoidHom : Subgroup U) : Set U) := by
    rw [Subgroup.coe_map, ← CFSG.GroupTheory.map_centralizer_eq_of_mulEquiv φe
      ((D.subgroupOf M) : Set ↥M)]
    exact Subgroup.map_mono hH_cent
  have hmap1 : (H.subgroupOf M).map φe.toMonoidHom ≤
      Subgroup.centralizer ((torU K ⊓ Subgroup.centralizer ({u} : Set U) : Subgroup U) :
        Set U) := by
    rwa [hDmap] at hmap1_raw
  have hmap2 : (H.subgroupOf M).map φe.toMonoidHom ≤
      pCoreOf 2 (Subgroup.centralizer ({u} : Set U)) :=
    (Subgroup.map_mono (Subgroup.subgroupOf_mono M inf_le_right)).trans_eq hQmap
  have hH_image : (H.subgroupOf M).map φe.toMonoidHom ≤ Subgroup.zpowers u := by
    have hle := le_inf hmap1 hmap2
    rwa [centralizer_inf_pCoreOf_centralizer_eq_zpowers hS.card_K huN hu2 hfix] at hle
  have hH_le_zt : H ≤ Subgroup.zpowers t := by
    intro h hh
    have hhM : h ∈ M := hHleM hh
    have hmem : φe ⟨h, hhM⟩ ∈ Subgroup.zpowers u := by
      apply hH_image
      exact Subgroup.mem_map.mpr ⟨⟨h, hhM⟩, Subgroup.mem_subgroupOf.mpr hh, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨k, ?_⟩
    have heq : (⟨h, hhM⟩ : ↥M) = ⟨t, htM⟩ ^ k := by
      apply φe.injective
      rw [map_zpow]
      rw [← hk]
    have hval := congrArg Subtype.val heq
    simpa using hval.symm
  exact le_antisymm hH_le_zt (Subgroup.zpowers_le.mpr ⟨htCE, htQ⟩)

end LocalSetting

end CFSG.StandardType.USixTwo

end
