module

public import CFSG.Quasithin.Background.SzQTwoClosed
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4Exc
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1c
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.Components
import CFSG.LocalAnalysis.UniquenessCase.UC22BarLemmas
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2
import CFSG.Quasithin.AppendixH.H9.H92.CoreRad.PCoreOfBasic
import CFSG.GroupTheory.PCore.NormalPCoreOf
public import CFSG.Blueprint.LieModelAPI
public import CFSG.CGT.PushingUp.CampbellPair
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22v
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch12Sec6P31LieG
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214f
import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight
open CFSG.QuasithinUnique (IsSylowTwoOf)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc22r3e5c_pCoreOf_eq_inf {X L : Subgroup G} (hLX : L ≤ X)
    (hLXn : X ≤ normalizer (L : Set G)) :
    pCoreOf 2 L = pCoreOf 2 X ⊓ L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (le_inf (CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hLX hLXn)
    (CFSG.LieType.BorelTits.pCoreOf_le 2 L)) ?_
  have h2 : IsPGroup 2 ↥(pCoreOf 2 X ⊓ L : Subgroup G) :=
    IsPGroup.to_le (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X) inf_le_left
  have hN : ∀ s ∈ L, ∀ k ∈ (pCoreOf 2 X ⊓ L : Subgroup G), s * k * s⁻¹ ∈
      (pCoreOf 2 X ⊓ L : Subgroup G) := by
    intro s hs k hk
    exact ⟨CFSG.ASVolI.ChH.pCoreOf_conj_mem (hLX hs) hk.1, L.mul_mem (L.mul_mem hs hk.2)
      (L.inv_mem hs)⟩
  exact CFSG.ASVolI.ChH.le_pCoreOf_of_isPGroup_normal inf_le_right hN h2

theorem uc22r3e5c_bar2_map_range {X L : Subgroup G} (hLX : L ≤ X) :
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥X)).comp (Subgroup.inclusion hLX)).range =
      (L.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) := by
  ext z
  constructor
  · rintro ⟨l, rfl⟩
    exact Subgroup.mem_map.mpr ⟨⟨l, hLX l.2⟩, l.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

theorem uc22r3e5c_bar2_map_ker {X L : Subgroup G} (hLX : L ≤ X)
    (hLXn : X ≤ normalizer (L : Set G)) :
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥X)).comp (Subgroup.inclusion hLX)).ker =
      CFSG.pCore 2 ↥L := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Subgroup ↥X := CFSG.pCore 2 ↥X
  let π : ↥X →* Bar2 X := QuotientGroup.mk' Q
  have hQker : π.ker = Q := QuotientGroup.ker_mk' Q
  ext l
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have hmem : (⟨l, hLX l.2⟩ : ↥X) ∈ π.ker := by
      change π ⟨l, hLX l.2⟩ = 1
      exact h
    have hxQ : (⟨l, hLX l.2⟩ : ↥X) ∈ Q := by
      simpa [hQker] using hmem
    have hxG : (l : G) ∈ pCoreOf 2 X :=
      (CFSG.mem_openPCoreOf_iff (p := 2) (H := X) ⟨l, hLX l.2⟩).mpr hxQ
    have hx : (l : G) ∈ pCoreOf 2 L := by
      rw [uc22r3e5c_pCoreOf_eq_inf hLX hLXn]
      exact ⟨hxG, l.2⟩
    exact (CFSG.mem_openPCoreOf_iff (p := 2) (H := L) l).mp hx
  · intro h
    have hxG : (l : G) ∈ pCoreOf 2 L :=
      (CFSG.mem_openPCoreOf_iff (p := 2) (H := L) l).mpr h
    have hx : (l : G) ∈ pCoreOf 2 X := by
      rw [uc22r3e5c_pCoreOf_eq_inf hLX hLXn] at hxG
      exact hxG.1
    have hmem : (⟨l, hLX l.2⟩ : ↥X) ∈ π.ker := by
      rw [hQker]
      exact (CFSG.mem_openPCoreOf_iff (p := 2) (H := X) ⟨l, hLX l.2⟩).mp hx
    exact MonoidHom.mem_ker.mp hmem

theorem uc22r3e5c_bar2_map_mulEquiv {X L : Subgroup G} (hLX : L ≤ X)
    (hLXn : X ≤ normalizer (L : Set G)) :
    Nonempty (Bar2 L ≃* (L.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : ↥X →* Bar2 X := QuotientGroup.mk' (CFSG.pCore 2 ↥X)
  let φ : ↥L →* Bar2 X := π.comp (Subgroup.inclusion hLX)
  have hφrange : φ.range = (L.subgroupOf X).map π := uc22r3e5c_bar2_map_range hLX
  have hφker : φ.ker = CFSG.pCore 2 ↥L := uc22r3e5c_bar2_map_ker hLX hLXn
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
    ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hφrange))⟩


theorem uc22r3e5c_mulEquiv_prod_of_internal {Y : Type} [Group Y] [Finite Y]
    {U V : Subgroup Y} (hsup : U ⊔ V = ⊤) (hcomm : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u)
    (hdisj : U ⊓ V = ⊥) :
    Nonempty (Y ≃* ↥U × ↥V) := by
  have hUcent : U ≤ Subgroup.centralizer (V : Set Y) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (hcomm u hu v hv).symm
  have hUnorm : U ≤ Subgroup.normalizer (V : Set Y) :=
    hUcent.trans (Subgroup.centralizer_le_normalizer (V : Set Y))
  let mE : ↥U × ↥V ≃* Y :=
    (Subgroup.mulEquivProdOfInternalDirect U V ⊤ le_top le_top
      (fun {u v} hu hv => hcomm u hu v hv) hdisj
      (by
        intro h hh
        have hmem : h ∈ (U : Set Y) * (V : Set Y) := by
          rw [← Subgroup.coe_mul_of_left_le_normalizer_right U V hUnorm, hsup]
          exact Subgroup.mem_top h
        obtain ⟨u, hu, v, hv, huv⟩ := Set.mem_mul.mp hmem
        exact ⟨u, hu, v, hv, huv⟩)).trans Subgroup.topEquiv
  exact ⟨mE.symm⟩

theorem uc22r3e5c_bar2_sup_comm {X L K : Subgroup G}
    (hcomm : ⁅L, K⁆ ≤ pCoreOf 2 X) :
    ∀ u ∈ (L.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)),
      ∀ v ∈ (K.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)), u * v = v * u := by
  intro u hu v hv
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hu
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hv
  have haL : (a : G) ∈ L := Subgroup.mem_subgroupOf.mp ha
  have hbK : (b : G) ∈ K := Subgroup.mem_subgroupOf.mp hb
  have hmemComm : ⁅(a : G), (b : G)⁆ ∈ ⁅L, K⁆ :=
    Subgroup.commutator_mem_commutator haL hbK
  have hmemG : ((⁅a, b⁆ : ↥X) : G) ∈ pCoreOf 2 X := by
    have h1 : ((⁅a, b⁆ : ↥X) : G) = ⁅(a : G), (b : G)⁆ := by
      simp [commutatorElement_def]
    rw [h1]
    exact hcomm hmemComm
  have hmem : ⁅a, b⁆ ∈ CFSG.pCore 2 ↥X :=
    (CFSG.mem_openPCoreOf_iff (p := 2) (H := X) (⁅a, b⁆)).mp hmemG
  let π : ↥X →* Bar2 X := QuotientGroup.mk' (CFSG.pCore 2 ↥X)
  have h1 : π ⁅a, b⁆ = 1 := (QuotientGroup.eq_one_iff (⁅a, b⁆)).mpr hmem
  rw [map_commutatorElement] at h1
  have h2 := commutatorElement_eq_one_iff_mul_comm.mp h1
  calc π (a * b) = π a * π b := map_mul π a b
    _ = π b * π a := h2
    _ = π (b * a) := (map_mul π b a).symm

theorem uc22r3e5c_bar2_sup_eq_top {X L K : Subgroup G} (hLX : L ≤ X) (hKX : K ≤ X)
    (hsup : L ⊔ K = X) :
    (L.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) ⊔
      (K.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) = ⊤ := by
  let π : ↥X →* Bar2 X := QuotientGroup.mk' (CFSG.pCore 2 ↥X)
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have h : ((L.subgroupOf X) ⊔ (K.subgroupOf X)).map π = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hLX hKX, hsup, Subgroup.subgroupOf_self,
      Subgroup.map_top_of_surjective π hsurj]
  rwa [Subgroup.map_sup] at h

theorem uc22r3e5c_inf_eq_bot_of_center_eq_bot {Y : Type} [Group Y] {U V : Subgroup Y}
    (hU : Subgroup.center ↥U = ⊥) (hcomm : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) :
    U ⊓ V = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz1 : (⟨z, hz.1⟩ : ↥U) = 1 := by
    have hc : (⟨z, hz.1⟩ : ↥U) ∈ Subgroup.center ↥U := by
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      exact hcomm (w : Y) w.2 z hz.2
    rw [hU] at hc
    simpa using hc
  simpa using congrArg Subtype.val hz1

theorem uc22r3e5c_bar2_sup_mulEquiv {X L K : Subgroup G}
    (hLX : L ≤ X) (hKX : K ≤ X)
    (hLXn : X ≤ normalizer (L : Set G)) (hKXn : X ≤ normalizer (K : Set G))
    (hsup : L ⊔ K = X) (hcomm : ⁅L, K⁆ ≤ pCoreOf 2 X)
    (hLc : Subgroup.center (Bar2 L) = ⊥) :
    Nonempty (Bar2 X ≃* Bar2 L × Bar2 K) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Subgroup ↥X := CFSG.pCore 2 ↥X
  let π : ↥X →* Bar2 X := QuotientGroup.mk' Q
  let LX : Subgroup ↥X := L.subgroupOf X
  let KX : Subgroup ↥X := K.subgroupOf X
  let U : Subgroup (Bar2 X) := LX.map π
  let V : Subgroup (Bar2 X) := KX.map π
  have hcommUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u :=
    uc22r3e5c_bar2_sup_comm hcomm
  have hsupUV : U ⊔ V = ⊤ := uc22r3e5c_bar2_sup_eq_top hLX hKX hsup
  obtain ⟨eUL⟩ := uc22r3e5c_bar2_map_mulEquiv hLX hLXn
  obtain ⟨eKL⟩ := uc22r3e5c_bar2_map_mulEquiv hKX hKXn
  have hUcenter : Subgroup.center ↥U = ⊥ := by
    rw [← Subgroup.map_center_eq eUL, hLc, Subgroup.map_bot]
  have hdisj : U ⊓ V = ⊥ := uc22r3e5c_inf_eq_bot_of_center_eq_bot hUcenter hcommUV
  obtain ⟨e⟩ := uc22r3e5c_mulEquiv_prod_of_internal hsupUV hcommUV hdisj
  exact ⟨e.trans (MulEquiv.prodCongr eUL.symm eKL.symm)⟩


theorem uc22r3e5c_isPGroup_prod {A B : Type} [Group A] [Group B]
    {PA : Subgroup A} {PB : Subgroup B} (hA : IsPGroup 2 PA) (hB : IsPGroup 2 PB) :
    IsPGroup 2 (PA.prod PB) := by
  have main : IsPGroup 2 (PA.prod PB) := by
    intro x
    obtain ⟨m, hm⟩ := hA ⟨x.1.1, x.2.1⟩
    obtain ⟨k, hk⟩ := hB ⟨x.1.2, x.2.2⟩
    refine ⟨max m k, ?_⟩
    apply Subtype.ext
    have ham : x.1.1 ^ 2 ^ m = 1 := congrArg Subtype.val hm
    have hbk : x.1.2 ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have ham' : x.1.1 ^ 2 ^ max m k = 1 := by
      obtain ⟨c, hc⟩ := pow_dvd_pow 2 (le_max_left m k)
      calc x.1.1 ^ 2 ^ max m k = (x.1.1 ^ 2 ^ m) ^ c := by rw [← pow_mul, hc]
        _ = 1 := by rw [ham, one_pow]
    have hbk' : x.1.2 ^ 2 ^ max m k = 1 := by
      obtain ⟨c, hc⟩ := pow_dvd_pow 2 (le_max_right m k)
      calc x.1.2 ^ 2 ^ max m k = (x.1.2 ^ 2 ^ k) ^ c := by rw [← pow_mul, hc]
        _ = 1 := by rw [hbk, one_pow]
    show (x.1.1 ^ 2 ^ max m k, x.1.2 ^ 2 ^ max m k) = (1, 1)
    rw [ham', hbk']
  by_cases h : PA = ⊥ <;> exact main

theorem uc22r3e5c_prod_le_normalizer {A B : Type} [Group A] [Group B]
    {PA QA : Subgroup A} {PB QB : Subgroup B}
    (hA : QA ≤ Subgroup.normalizer (PA : Set A))
    (hB : QB ≤ Subgroup.normalizer (PB : Set B)) :
    QA.prod QB ≤ Subgroup.normalizer ((PA.prod PB : Subgroup (A × B)) : Set (A × B)) := by
  have main : QA.prod QB ≤ Subgroup.normalizer ((PA.prod PB : Subgroup (A × B)) :
      Set (A × B)) := by
    have hconj : ∀ x ∈ QA.prod QB, ∀ y ∈ PA.prod PB,
        x * y * x⁻¹ ∈ PA.prod PB := by
      rintro ⟨a, b⟩ hx ⟨p, q⟩ hy
      obtain ⟨ha, hb⟩ := Subgroup.mem_prod.mp hx
      obtain ⟨hp, hq⟩ := Subgroup.mem_prod.mp hy
      have hna := Subgroup.mem_normalizer_iff.mp (hA ha)
      have hnb := Subgroup.mem_normalizer_iff.mp (hB hb)
      have ha' : a * p * a⁻¹ ∈ PA := (hna p).mp hp
      have hb' : b * q * b⁻¹ ∈ PB := (hnb q).mp hq
      have hmem : (a * p * a⁻¹, b * q * b⁻¹) ∈ PA.prod PB :=
        Subgroup.mem_prod.mpr ⟨ha', hb'⟩
      simpa [Prod.mk_mul_mk, mul_assoc] using hmem
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hconj x hx y
    · intro h
      have hxinv : x⁻¹ ∈ QA.prod QB := (QA.prod QB).inv_mem hx
      have h2 := hconj x⁻¹ hxinv (x * y * x⁻¹) h
      simpa [mul_assoc] using h2
  by_cases h : PA = ⊥ <;> exact main

theorem uc22r3e5c_prod_map_fst_prod_snd {A B : Type} [Group A] [Finite A] [Group B] [Finite B]
    {P : Subgroup (A × B)} (hP : IsSylowTwoOf P ⊤) :
    (P.map (MonoidHom.fst A B)).prod (P.map (MonoidHom.snd A B)) = P := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let πA : A × B →* A := MonoidHom.fst A B
  let πB : A × B →* B := MonoidHom.snd A B
  have hPidx : ¬ 2 ∣ P.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hP.2.2
  have hPA2 : IsPGroup 2 (P.map πA) := hP.2.1.map πA
  have hPB2 : IsPGroup 2 (P.map πB) := hP.2.1.map πB
  have hPprod2 : IsPGroup 2 ((P.map πA).prod (P.map πB)) :=
    uc22r3e5c_isPGroup_prod hPA2 hPB2
  have hPle : P ≤ (P.map πA).prod (P.map πB) := by
    intro x hx
    exact Subgroup.mem_prod.mpr
      ⟨Subgroup.mem_map_of_mem πA hx, Subgroup.mem_map_of_mem πB hx⟩
  let sP : Sylow 2 (A × B) := hP.2.1.toSylow hPidx
  have hsP : (sP : Subgroup (A × B)) = P := IsPGroup.toSylow_coe hP.2.1 hPidx
  have h := sP.is_maximal' hPprod2 (hsP ▸ hPle)
  rwa [hsP] at h

theorem uc22r3e5c_solvable_map_fst_le_normalizer {n : ℕ}
    (hn : 1 ≤ n) {A B : Type} [Group A] [Finite A] [Group B] [Finite B]
    (eA : A ≃* ↥(Sz n)) {P : Subgroup (A × B)} (hP : IsSylowTwoOf P ⊤)
    {H : Subgroup (A × B)} (hHP : P ≤ H) (hHs : Group.IsSolvable ↥H) :
    H.map (MonoidHom.fst A B) ≤
      Subgroup.normalizer ((P.map (MonoidHom.fst A B) : Subgroup A) : Set A) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let πA : A × B →* A := MonoidHom.fst A B
  let PA : Subgroup A := P.map πA
  have hPidx : ¬ 2 ∣ P.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hP.2.2
  have hPA2 : IsPGroup 2 PA := hP.2.1.map πA
  have hPAidx : ¬ 2 ∣ PA.index := fun hd =>
    hPidx (hd.trans (Subgroup.index_map_dvd P (fun a => ⟨(a, 1), rfl⟩)))
  let sPA : Sylow 2 A := hPA2.toSylow hPAidx
  have hsPA : (sPA : Subgroup A) = PA := IsPGroup.toSylow_coe hPA2 hPAidx
  refine CFSG.Quasithin.SzQ.le_normalizer_of_solvable hn eA sPA ?_ ?_
  · rw [hsPA]
    exact Subgroup.map_mono hHP
  · haveI := hHs
    exact Group.isSolvable_of_surjective (πA.subgroupMap_surjective H)

theorem uc22r3e5c_solvable_map_snd_le_normalizer {n : ℕ}
    (hn : 1 ≤ n) {A B : Type} [Group A] [Finite A] [Group B] [Finite B]
    (eB : B ≃* ↥(Sz n)) {P : Subgroup (A × B)} (hP : IsSylowTwoOf P ⊤)
    {H : Subgroup (A × B)} (hHP : P ≤ H) (hHs : Group.IsSolvable ↥H) :
    H.map (MonoidHom.snd A B) ≤
      Subgroup.normalizer ((P.map (MonoidHom.snd A B) : Subgroup B) : Set B) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let πB : A × B →* B := MonoidHom.snd A B
  let PB : Subgroup B := P.map πB
  have hPidx : ¬ 2 ∣ P.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hP.2.2
  have hPB2 : IsPGroup 2 PB := hP.2.1.map πB
  have hPBidx : ¬ 2 ∣ PB.index := fun hd =>
    hPidx (hd.trans (Subgroup.index_map_dvd P (fun b => ⟨(1, b), rfl⟩)))
  let sPB : Sylow 2 B := hPB2.toSylow hPBidx
  have hsPB : (sPB : Subgroup B) = PB := IsPGroup.toSylow_coe hPB2 hPBidx
  refine CFSG.Quasithin.SzQ.le_normalizer_of_solvable hn eB sPB ?_ ?_
  · rw [hsPB]
    exact Subgroup.map_mono hHP
  · haveI := hHs
    exact Group.isSolvable_of_surjective (πB.subgroupMap_surjective H)

theorem uc22r3e5c_solvable_prod_le_normalizer
    {n : ℕ} (hn : 1 ≤ n)
    {A B : Type} [Group A] [Finite A] [Group B] [Finite B]
    (eA : A ≃* ↥(Sz n)) (eB : B ≃* ↥(Sz n))
    {P : Subgroup (A × B)} (hP : IsSylowTwoOf P ⊤)
    {H : Subgroup (A × B)} (hHP : P ≤ H) (hHs : Group.IsSolvable ↥H) :
    H ≤ Subgroup.normalizer (P : Set (A × B)) := by
  have hHA : H.map (MonoidHom.fst A B) ≤
      Subgroup.normalizer ((P.map (MonoidHom.fst A B) : Subgroup A) : Set A) :=
    uc22r3e5c_solvable_map_fst_le_normalizer hn eA hP hHP hHs
  have hHB : H.map (MonoidHom.snd A B) ≤
      Subgroup.normalizer ((P.map (MonoidHom.snd A B) : Subgroup B) : Set B) :=
    uc22r3e5c_solvable_map_snd_le_normalizer hn eB hP hHP hHs
  have hHprod : H ≤ (H.map (MonoidHom.fst A B)).prod (H.map (MonoidHom.snd A B)) :=
    Subgroup.le_prod_iff.mpr ⟨le_rfl, le_rfl⟩
  have hNorm : (H.map (MonoidHom.fst A B)).prod (H.map (MonoidHom.snd A B)) ≤
      Subgroup.normalizer (((P.map (MonoidHom.fst A B)).prod (P.map (MonoidHom.snd A B)) :
        Subgroup (A × B)) : Set (A × B)) :=
    uc22r3e5c_prod_le_normalizer hHA hHB
  have hEq : (P.map (MonoidHom.fst A B)).prod (P.map (MonoidHom.snd A B)) = P :=
    uc22r3e5c_prod_map_fst_prod_snd hP
  rw [hEq] at hNorm
  exact hHprod.trans hNorm


theorem uc22r3e5c_odd_card_B0 {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch) :
    Odd (Nat.card c.B0) := by
  by_contra h
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥c.B0) 2 h
  have h1 := uc22p21d_odd_orderOf_of_mem_calB1 c.hB0 x.2
  rw [Subgroup.orderOf_coe, hx] at h1
  exact (by decide : ¬ Odd 2) h1

theorem uc22r3e5c_comap_barImage {X S : Subgroup G} (hO2 : pCoreOf 2 X ≤ S) :
    (barImage X S).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) = S.subgroupOf X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine Subgroup.comap_map_eq_self ?_
  rw [QuotientGroup.ker_mk']
  intro q hq
  exact Subgroup.mem_subgroupOf.mpr (hO2 ((CFSG.mem_openPCoreOf_iff q).mpr hq))

theorem uc22r3e5c_mem_of_barImage_normalizer {X Y S : Subgroup G} (hYX : Y ≤ X)
    (hSX : S ≤ X) (hO2 : pCoreOf 2 X ≤ S)
    (hbar : barImage X Y ≤ Subgroup.normalizer (barImage X S : Set (Bar2 X))) :
    ∀ y ∈ Y, ∀ s ∈ S, y * s * y⁻¹ ∈ S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : ↥X →* Bar2 X := QuotientGroup.mk' (CFSG.pCore 2 ↥X)
  have hcomap : (barImage X S).comap π = S.subgroupOf X := uc22r3e5c_comap_barImage hO2
  intro y hy s hs
  have hyX : y ∈ X := hYX hy
  have hsX : s ∈ X := hSX hs
  have hybar : π ⟨y, hyX⟩ ∈ barImage X Y :=
    Subgroup.mem_map.mpr ⟨⟨y, hyX⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  have hsbar : π ⟨s, hsX⟩ ∈ barImage X S :=
    Subgroup.mem_map.mpr ⟨⟨s, hsX⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
  have hny := Subgroup.mem_normalizer_iff.mp (hbar hybar)
  have hmem : π ⟨y, hyX⟩ * π ⟨s, hsX⟩ * (π ⟨y, hyX⟩)⁻¹ ∈ barImage X S :=
    (hny (π ⟨s, hsX⟩)).mp hsbar
  have hsub : (⟨y * s * y⁻¹, X.mul_mem (X.mul_mem hyX hsX) (X.inv_mem hyX)⟩ : ↥X) =
      ⟨y, hyX⟩ * ⟨s, hsX⟩ * ⟨y, hyX⟩⁻¹ := by
    ext
    simp [mul_assoc]
  have hval : π ⟨y * s * y⁻¹, X.mul_mem (X.mul_mem hyX hsX) (X.inv_mem hyX)⟩ ∈
      barImage X S := by
    rw [hsub]
    exact hmem
  have hmem' : (⟨y * s * y⁻¹, X.mul_mem (X.mul_mem hyX hsX) (X.inv_mem hyX)⟩ : ↥X) ∈
      (barImage X S).comap π := hval
  rw [hcomap] at hmem'
  exact Subgroup.mem_subgroupOf.mp hmem'

theorem uc22r3e5c_le_normalizer_of_barImage {X Y S : Subgroup G} (hYX : Y ≤ X) (hSX : S ≤ X)
    (hO2 : pCoreOf 2 X ≤ S)
    (hbar : barImage X Y ≤ Subgroup.normalizer (barImage X S : Set (Bar2 X))) :
    Y ≤ Subgroup.normalizer (S : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · exact uc22r3e5c_mem_of_barImage_normalizer hYX hSX hO2 hbar y hy s
  · intro hs
    have h1 : y⁻¹ * (y * s * y⁻¹) * y⁻¹⁻¹ ∈ S :=
      uc22r3e5c_mem_of_barImage_normalizer hYX hSX hO2 hbar y⁻¹ (Y.inv_mem hy) _ hs
    simpa [mul_assoc] using h1


theorem uc22r3e5c_isSylowTwoOf_map_mulEquiv {Y Y' : Type} [Group Y] [Finite Y] [Group Y']
    [Finite Y'] (e : Y ≃* Y') {S : Subgroup Y} (h : IsSylowTwoOf S ⊤) :
    IsSylowTwoOf (S.map e.toMonoidHom) ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h' : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mp h
  have h'' : CFSG.ABGLocalTools.IsSylowOf 2 (S.map e.toMonoidHom) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff] at h' ⊢
    refine ⟨le_top, h'.2.1.map e.toMonoidHom, ?_⟩
    rw [Subgroup.relIndex_top_right] at h' ⊢
    rw [Subgroup.index_map_eq S e.surjective (by
      intro x hx
      have hx1 : x = 1 := e.injective (by simpa using hx)
      rw [hx1]
      exact S.one_mem)]
    exact h'.2.2
  exact CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr h''

theorem uc22r3e5c_isSylowTwoOf_of_le {S X Y : Subgroup G} (hS : IsSylowTwoOf S X)
    (hSY : S ≤ Y) (hYX : Y ≤ X) : IsSylowTwoOf S Y :=
  CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr
    ((CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mp hS).of_le hSY hYX)

theorem uc22r3e5c_le_normalizer_inf {Z X : Subgroup G}
    (hZX : Z ≤ Subgroup.normalizer (X : Set G)) :
    Z ≤ Subgroup.normalizer ((Z ⊓ X : Subgroup G) : Set G) :=
  (le_inf Subgroup.le_normalizer hZX).trans Subgroup.inf_normalizer_le_normalizer_inf

theorem uc22r3e5c_pCoreOf_le_of_sylow {X S : Subgroup G} (hS : IsSylowTwoOf S X) :
    pCoreOf 2 X ≤ S := by
  have hcore : CFSG.pCore 2 ↥X ≤ S.subgroupOf X :=
    CFSG.Quasithin.pCore_two_le_subgroupOf hS
  calc pCoreOf 2 X = (CFSG.pCore 2 ↥X).map X.subtype := rfl
    _ ≤ (S.subgroupOf X : Subgroup ↥X).map X.subtype := Subgroup.map_mono hcore
    _ = S := Subgroup.map_subgroupOf_eq_of_le hS.1

theorem uc22r3e5c_pCore_eq_subgroupOf_of_sylow_normal {S Y : Subgroup G}
    (hS : IsSylowTwoOf S Y) (hN : (S.subgroupOf Y).Normal) :
    S.subgroupOf Y = CFSG.pCore 2 ↥Y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 ↥(S.subgroupOf Y) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  have hSidx : ¬ 2 ∣ (S.subgroupOf Y).index := hS.2.2
  refine le_antisymm ?_ ?_
  · rw [CFSG.pCore_eq_iSup]
    exact le_iSup_of_le (S.subgroupOf Y) (le_iSup_of_le hN (le_iSup_of_le hS2 le_rfl))
  · let sY : Sylow 2 ↥Y := hS2.toSylow hSidx
    have hsY : (sY : Subgroup ↥Y) = S.subgroupOf Y := IsPGroup.toSylow_coe hS2 hSidx
    haveI : (CFSG.pCore 2 ↥Y).Normal := CFSG.pCore_normal
    have h := IsPGroup.le_sylow_of_normal (p := 2) (N := CFSG.pCore 2 ↥Y)
      CFSG.pCore_isPGroup sY
    rwa [hsY] at h

theorem uc22r3e5c_exists_sz_equiv {X : Type} [Group X] [Finite X] {n : ℕ} (h : IsSz X n) :
    ∃ a : ℕ, 1 ≤ a ∧ n = 2 * a + 1 ∧ Nonempty (X ≃* ↥(Sz a)) := by
  obtain ⟨-, -, a, ha, K, hK, hKf, hf, hcard, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.twistedB2_iff.1 h
  letI : Field K := hK
  letI : Finite K := hKf
  have hcard' : Nat.card K = 2 ^ (2 * a + 1) := by
    rw [← hf]
    exact hcard
  refine ⟨a, ha, hf, ⟨e.trans ?_⟩⟩
  exact (MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
    (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard')

theorem uc22r3e5c_isSz_of_mem_conjSetOf {M L K : Subgroup G} {n : ℕ}
    (hK : K ∈ conjSetOf M L) (hSz : IsSz (Bar2 L) n) : IsSz (Bar2 K) n := by
  obtain ⟨g, -, rfl⟩ := hK
  obtain ⟨econj⟩ := uc22p20d_bar2_conj g L
  exact CFSG.Blueprint.LieModel.of_mulEquiv econj hSz

theorem uc22r3e5c_exists_sz_pair_equiv {M L K : Subgroup G} {n : ℕ}
    (hK : K ∈ conjSetOf M L) (hSz : IsSz (Bar2 L) n) :
    ∃ a : ℕ, 1 ≤ a ∧ n = 2 * a + 1 ∧ Nonempty (Bar2 L ≃* ↥(Sz a)) ∧
      Nonempty (Bar2 K ≃* ↥(Sz a)) := by
  obtain ⟨a, ha, hna, ⟨eL⟩⟩ := uc22r3e5c_exists_sz_equiv hSz
  have hSzK : IsSz (Bar2 K) n := uc22r3e5c_isSz_of_mem_conjSetOf hK hSz
  obtain ⟨aK, haK, hnaK, ⟨eK⟩⟩ := uc22r3e5c_exists_sz_equiv hSzK
  have haeq : aK = a := by omega
  subst aK
  exact ⟨a, ha, hna, ⟨eL⟩, ⟨eK⟩⟩

theorem uc22r3e5c_isSolvable_barImage {X Y : Subgroup G} (hYX : Y ≤ X)
    (hY : Group.IsSolvable ↥Y) : Group.IsSolvable ↥(barImage X Y) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let eY : ↥(Y.subgroupOf X) ≃* ↥Y := Subgroup.subgroupOfEquivOfLe hYX
  have hYsub : Group.IsSolvable ↥(Y.subgroupOf X) := by
    haveI := hY
    exact Group.isSolvable_of_isSolvable_injective (f := eY.toMonoidHom) eY.injective
  haveI := hYsub
  exact Group.isSolvable_of_surjective
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥X)).subgroupMap_surjective (Y.subgroupOf X))

theorem uc22r3e5c_isSolvable_inf_sup_B0 {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch)
    (X : Subgroup G) : Group.IsSolvable ↥((c.B0 ⊔ D.T) ⊓ X) := by
  obtain ⟨-, hB0c, -, -, -, -, -, -, -, hperm, -⟩ := c.hB0
  have hB0odd := uc22r3e5c_odd_card_B0 c
  have hTp : IsPGroup 2 D.T := (CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM).2.1
  have hZsolv : Group.IsSolvable ↥(c.B0 ⊔ D.T) :=
    uc22p2214_isSolvable_sup hB0odd hB0c hTp hperm
  haveI := hZsolv
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective inf_le_left)

theorem uc22r3e5c_isSylowTwoOf_inf {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M) :
    IsSylowTwoOf (D.T ⊓ conjClosure D.M L) (conjClosure D.M L) := by
  have hXleM : conjClosure D.M L ≤ D.M :=
    uc22p22v_conjClosure_le (N := D.M) (E := L) (F := D.M)
      (Subgroup.le_normalizer (H := D.M)) hL.1.le
  have hXnormM : D.M ≤ normalizer (conjClosure D.M L : Set G) :=
    uc22p22v_le_normalizer_conjClosure D.M L
  exact CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr
    (CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer (P := D.T) (K := D.M)
      (N := conjClosure D.M L) D.sylowM hXleM hXnormM)

theorem uc22r3e5c_bar2_conjClosure_mulEquiv {D : Data G} {L K : Subgroup G}
    (hL : L ∈ calC D.M) (hKC : K ∈ calC D.M) (hKne : K ≠ L)
    (hset : conjSetOf D.M L = {L, K}) {n : ℕ} (hSz : IsSz (Bar2 L) n) :
    Nonempty (Bar2 (conjClosure D.M L) ≃* Bar2 L × Bar2 K) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let X : Subgroup G := conjClosure D.M L
  have hXsup : X = L ⊔ K := conjClosure_eq_sup_of_conjSetOf_eq hset
  have hLX : L ≤ X := by rw [hXsup]; exact le_sup_left
  have hKX : K ≤ X := by rw [hXsup]; exact le_sup_right
  have hLXn : X ≤ normalizer (L : Set G) := by
    rw [hXsup]
    exact sup_le Subgroup.le_normalizer (calC_le_normalizer_of_ne hL hKC hKne.symm)
  have hKXn : X ≤ normalizer (K : Set G) := by
    rw [hXsup]
    exact sup_le (calC_le_normalizer_of_ne hKC hL hKne) Subgroup.le_normalizer
  have hcomm : ⁅L, K⁆ ≤ pCoreOf 2 X :=
    (calC_commutator_le_of_ne hL hKC hKne.symm).trans
      (inf_le_left.trans (CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hLX hLXn))
  have hLc : Subgroup.center (Bar2 L) = ⊥ := center_eq_bot_of_isSz hL.2.2 hSz
  exact uc22r3e5c_bar2_sup_mulEquiv hLX hKX hLXn hKXn hXsup.symm hcomm hLc

theorem uc22r3e5c_le_normalizer_of_mulEquiv_prod {n : ℕ}
    (hn : 1 ≤ n) {B2 P Q : Type} [Group B2] [Finite B2] [Group P] [Finite P]
    [Group Q] [Finite Q] (e : B2 ≃* P × Q) (eP : P ≃* ↥(Sz n)) (eQ : Q ≃* ↥(Sz n))
    {S Y : Subgroup B2} (hS : IsSylowTwoOf S ⊤) (hSY : S ≤ Y)
    (hY : Group.IsSolvable ↥Y) :
    Y ≤ Subgroup.normalizer (S : Set B2) := by
  have hS' : IsSylowTwoOf (S.map e.toMonoidHom) ⊤ :=
    uc22r3e5c_isSylowTwoOf_map_mulEquiv e hS
  have hY' : Group.IsSolvable ↥(Y.map e.toMonoidHom) := by
    haveI := hY
    exact Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective Y)
  have hH := uc22r3e5c_solvable_prod_le_normalizer hn eP eQ hS' (Subgroup.map_mono hSY) hY'
  have hmapN : (Subgroup.normalizer (S : Set B2)).map e.toMonoidHom =
      Subgroup.normalizer ((S.map e.toMonoidHom) : Set (P × Q)) :=
    Subgroup.map_normalizer_eq_of_bijective _ e.bijective
  rw [← hmapN] at hH
  intro z hz
  obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp (hH (Subgroup.mem_map.mpr ⟨z, hz, rfl⟩))
  rwa [e.injective hwz] at hw

theorem uc22r3e5c_barImage_inf_le_normalizer {D : Data G}
    {Ch : Choice2011 G} (h5 : S21_5 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ}
    (hn : 2 < n) (hSz : IsSz (Bar2 L) n) :
    barImage (conjClosure D.M L) ((c.B0 ⊔ D.T) ⊓ conjClosure D.M L) ≤
      Subgroup.normalizer (barImage (conjClosure D.M L) (D.T ⊓ conjClosure D.M L) :
        Set (Bar2 (conjClosure D.M L))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hKne, hset, hKC⟩ := uc22s21ru4e_exists_second_member hc2 hL
  have hKmem : K ∈ conjSetOf D.M L := by rw [hset]; simp
  let X : Subgroup G := conjClosure D.M L
  obtain ⟨e⟩ := uc22r3e5c_bar2_conjClosure_mulEquiv hL hKC hKne hset hSz
  have hSylX : IsSylowTwoOf (D.T ⊓ X) X := uc22r3e5c_isSylowTwoOf_inf hL
  have hSbSyl : IsSylowTwoOf (barImage X (D.T ⊓ X)) ⊤ :=
    CFSG.Quasithin.H13.S126P31.isSylowTwoOf_map_mk' (Z := CFSG.pCore 2 ↥X)
      (CFSG.Quasithin.isSylowTwoOf_top_subgroupOf hSylX)
  let Y : Subgroup G := (c.B0 ⊔ D.T) ⊓ X
  have hYsolv : Group.IsSolvable ↥Y := uc22r3e5c_isSolvable_inf_sup_B0 c X
  have hYbs : Group.IsSolvable ↥(barImage X Y) :=
    uc22r3e5c_isSolvable_barImage inf_le_right hYsolv
  have hSb_le_Yb : barImage X (D.T ⊓ X) ≤ barImage X Y :=
    barImage_mono (le_inf (inf_le_left.trans le_sup_right) inf_le_right)
  obtain ⟨a, ha, -, ⟨eLa⟩, ⟨eKa⟩⟩ := uc22r3e5c_exists_sz_pair_equiv hKmem hSz
  exact uc22r3e5c_le_normalizer_of_mulEquiv_prod ha e eLa eKa hSbSyl hSb_le_Yb hYbs

theorem uc22r3e5c_B0_le_normalizer_conjClosure {D : Data G} {Ch : Choice2011 G}
    (h5 : S21_5 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hc2 : (conjSetOf D.M L).ncard = 2) :
    c.B0 ≤ Subgroup.normalizer (conjClosure D.M L : Set G) := by
  obtain ⟨K, hKne, hset, hKC⟩ := uc22s21ru4e_exists_second_member hc2 hL
  have hB0L : c.B0 ≤ normalizer (L : Set G) := by
    let c' : Ctx21 D Ch := { c with B := c.B0, hB := c.hB0, hle := le_rfl }
    exact h5 h1930 c' L hL
  have hB0K : c.B0 ≤ normalizer (K : Set G) := by
    let c' : Ctx21 D Ch := { c with B := c.B0, hB := c.hB0, hle := le_rfl }
    exact h5 h1930 c' K hKC
  calc c.B0 ≤ normalizer (L : Set G) ⊓ normalizer (K : Set G) := le_inf hB0L hB0K
    _ ≤ normalizer ((L ⊔ K : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_sup L K
    _ = normalizer (conjClosure D.M L : Set G) := by
      rw [conjClosure_eq_sup_of_conjSetOf_eq hset]

theorem uc22r3e5c_normalizes_inf {D : Data G}
    {Ch : Choice2011 G} (h5 : S21_5 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ}
    (hn : 2 < n) (hSz : IsSz (Bar2 L) n) :
    ∀ a ∈ c.B0, a ∈ normalizer ((D.T ⊓ conjClosure D.M L : Subgroup G) : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let X : Subgroup G := conjClosure D.M L
  let S : Subgroup G := D.T ⊓ X
  let Z : Subgroup G := c.B0 ⊔ D.T
  let Y : Subgroup G := Z ⊓ X
  have hbar := uc22r3e5c_barImage_inf_le_normalizer h5 h1930 c hL hc2 hn hSz
  have hSylX : IsSylowTwoOf S X := uc22r3e5c_isSylowTwoOf_inf hL
  have hO2 : pCoreOf 2 X ≤ S := uc22r3e5c_pCoreOf_le_of_sylow hSylX
  have hYnorm : Y ≤ Subgroup.normalizer (S : Set G) :=
    uc22r3e5c_le_normalizer_of_barImage inf_le_right inf_le_right hO2 hbar
  have hSleY : S ≤ Y := le_inf (inf_le_left.trans le_sup_right) inf_le_right
  have hSylY : IsSylowTwoOf S Y := uc22r3e5c_isSylowTwoOf_of_le hSylX hSleY inf_le_right
  have hSnormal : (S.subgroupOf Y).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hYnorm
  have hSchar : (S.subgroupOf Y).Characteristic := by
    rw [uc22r3e5c_pCore_eq_subgroupOf_of_sylow_normal hSylY hSnormal]
    exact inferInstance
  have hB0X := uc22r3e5c_B0_le_normalizer_conjClosure h5 h1930 c hL hc2
  have hTX : D.T ≤ Subgroup.normalizer (X : Set G) :=
    D.sylowM.le.trans (uc22p22v_le_normalizer_conjClosure D.M L)
  have hZX : Z ≤ Subgroup.normalizer (X : Set G) := sup_le hB0X hTX
  have hZY : Z ≤ Subgroup.normalizer (Y : Set G) := uc22r3e5c_le_normalizer_inf hZX
  have hSN : Z ≤ Subgroup.normalizer (S : Set G) :=
    hZY.trans (CFSG.CGT.PushingUp.normalizer_le_normalizer_of_characteristic' hSleY hSchar)
  intro a ha
  exact hSN (Subgroup.mem_sup_left ha)

end CFSG.LocalAnalysis.UniquenessCase.UC22
