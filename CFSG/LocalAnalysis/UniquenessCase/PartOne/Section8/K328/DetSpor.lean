module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.DetDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import Certificates.Certificate13513
import CFSG.CGT.PushingUpLit.CGT6.SixFourPrinted
import CFSG.CGT.PushingUpLit.T2KSW.Prop28
import CFSG.ClassicalInvolution.Q3.M11Kernel
import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporCard
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThree
import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeCent
import CFSG.Quasithin.Vol2.KGFactJ4BlockC
import CFSG.RankThree.Native.ONThreeCentralizer
import CFSG.RankThree.Native.ONThreeFusion
import CFSG.Sporadic.J3
import CFSG.Sporadic.Schreier.PairJ2Faithful
public import CFSG.Sporadic.J4.Local
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Sporadic.Schreier.PairJ2CertBase
public import CFSG.Sporadic.Schreier.RuDefs
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.M24
import CFSG.Sporadic.Schreier.M23Base

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor)

private theorem k328dso_card_of_isSpor {S : Type} [Group S] {s : TauCeti.SporadicName}
    (h : IsSpor S s) : Nat.card S = Nat.card (CFSG.Blueprint.NativeSporadic.Carrier s) := by
  obtain ⟨e⟩ := h
  exact Nat.card_congr e.toEquiv

theorem k328det_sporOrders :
    ∀ (S : Type) [Group S] [Finite S],
      (IsSpor S .M11 → Nat.card S = 7920) ∧ (IsSpor S .M12 → Nat.card S = 95040) ∧
      (IsSpor S .M22 → Nat.card S = 443520) ∧ (IsSpor S .M23 → Nat.card S = 10200960) ∧
      (IsSpor S .HS → Nat.card S = 44352000) ∧ (IsSpor S .J3 → Nat.card S = 50232960) := by
  intro S _ _
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [k328dso_card_of_isSpor h]
    exact CFSG.ClassicalInvolution.Q3.card_m11_kernel
  · rw [k328dso_card_of_isSpor h]
    exact CFSG.Sporadic.Mathieu.card_M12
  · rw [k328dso_card_of_isSpor h]
    exact CFSG.CGT.PushingUpLit.T2KSW.card_nativeM22_eq
  · rw [k328dso_card_of_isSpor h]
    exact CFSG.Sporadic.Schreier.m23_card
  · rw [k328dso_card_of_isSpor h]
    exact CFSG.Sporadic.HS.card_HS
  · rw [k328dso_card_of_isSpor h]
    exact CFSG.Sporadic.J3.card_J3

private theorem k328dsc_card_cent {S T : Type} [Group S] [Group T] (e : S ≃* T) (x : S) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set S)) =
      Nat.card ↥(Subgroup.centralizer ({e x} : Set T)) :=
  (Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective).symm.trans
    (congrArg (fun H : Subgroup T => Nat.card ↥H)
      (CFSG.Quasithin.H13.Ch4.J4Blk.map_centralizer_singleton e x))

private theorem k328dsc_perm {S : Type} [Group S] {n : ℕ} {P : Subgroup (Equiv.Perm (Fin n))}
    (e : S ≃* ↥P) {x : S} (hx : orderOf x = 3)
    (h : ∀ t ∈ P, orderOf t = 3 →
      ¬ 64 ∣ Nat.card ↥(P ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin n))))) :
    ¬ 64 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set S)) := by
  rw [CFSG.RankThree.Native.card_centralizer_eq_inf_of_mulEquiv e x, inf_comm]
  exact h _ (e x).2 (by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact hx)

private theorem k328dsc_conj {G : Type} [Group G] {P : Subgroup G} {g r : G} (hg : g ∈ P)
    (h : ¬ 64 ∣ Nat.card ↥(P ⊓ Subgroup.centralizer ({r} : Set G))) :
    ¬ 64 ∣ Nat.card ↥(P ⊓ Subgroup.centralizer ({g * r * g⁻¹} : Set G)) := by
  rw [CFSG.Sporadic.SmallOddCore.inf_centralizer_conj P hg r,
    Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective]
  exact h

private theorem k328dsc_cent_zpowers {G : Type} [Group G] {a b : G}
    (h : Subgroup.zpowers a = Subgroup.zpowers b) :
    Subgroup.centralizer ({a} : Set G) = Subgroup.centralizer ({b} : Set G) := by
  have key : ∀ g : G, Subgroup.centralizer ({g} : Set G) =
      Subgroup.centralizer ((Subgroup.zpowers g : Subgroup G) : Set G) := fun g => by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [key a, key b, h]

private theorem k328dsc_m24
    {S : Type} [Group S] (h : IsSpor S .M24) {x : S} (hx : orderOf x = 3) :
    ¬ 64 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set S)) := by
  obtain ⟨e⟩ := h
  refine k328dsc_perm (e : S ≃* ↥CFSG.Blueprint.NativeSporadic.M24) hx fun t ht ht3 => ?_
  obtain ⟨-, -, hrows, hcover, -⟩ := CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24.m24ThreeSpec
  obtain ⟨r, hr, g, hg, rfl⟩ := hcover t ht ht3
  refine k328dsc_conj hg ?_
  rw [(hrows r hr).2.2.1]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · change ¬ 64 ∣ 1080
    omega
  · change ¬ 64 ∣ 504
    omega

private theorem k328dsc_j2
    {S : Type} [Group S] (h : IsSpor S .J2) {x : S} (hx : orderOf x = 3) :
    ¬ 64 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set S)) := by
  obtain ⟨e⟩ := h
  refine k328dsc_perm (e.trans CFSG.Sporadic.Schreier.j2PermEquiv) hx fun t ht ht3 => ?_
  have hchk := Certificates.certificate13513
  obtain ⟨hvA, hvB⟩ := CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check_valid hchk
  obtain ⟨c, hc, hcard⟩ := CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check_card_sound
    CFSG.HardMathSupport.Solomon.Coordinator.B3S3.j2S3Data
    (CFSG.RankThree.Native.rep_of_validA hvA) (CFSG.RankThree.Native.rep_of_validA hvB) hchk t ht
    ht3
  have hcard' : Nat.card ↥(Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 315))) ⊓
      CFSG.Sporadic.Schreier.j2P) = _ := hcard
  have hne : ∀ c < CFSG.HardMathSupport.Solomon.Coordinator.B3S3.j2S3Data.cases.size,
      ¬ 64 ∣ CFSG.HardMathSupport.Solomon.Coordinator.B3S3.j2S3Data.cases[c]!.card := by
    decide +kernel
  rw [inf_comm, hcard']
  exact hne c hc

private theorem k328dsc_he
    {S : Type} [Group S] (h : IsSpor S .He) {x : S}
    (hx : orderOf x = 3) : ¬ 64 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set S)) := by
  obtain ⟨e⟩ := h
  refine k328dsc_perm (e.trans CFSG.Sporadic.HeldB.heEquivP) hx fun t ht ht3 => ?_
  rcases CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He.three_conj_cases ht ht3 with
    ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩
  · refine k328dsc_conj hg ?_
    have hA := CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He.card_cent_A
    unfold CFSG.Sporadic.Schreier.centralizerIn at hA
    rw [hA]
    omega
  · refine k328dsc_conj hg ?_
    have hB := CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He.card_cent_B
    unfold CFSG.Sporadic.Schreier.centralizerIn at hB
    rw [hB]
    omega

private theorem k328dsc_ru
    {S : Type} [Group S] (h : IsSpor S .Ru) {x : S} (hx : orderOf x = 3) :
    ¬ 64 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set S)) := by
  obtain ⟨e⟩ := h
  let e' : S ≃* ↥CFSG.Sporadic.RuSchreier.ruP := e.trans CFSG.Sporadic.RuSchreier.ruEquivP
  obtain ⟨c, hc⟩ := CFSG.EvenSporadicStandard.RuStd.S2.exists_conj_ruThree (e' x)
    (by rw [MulEquiv.orderOf_eq]; exact hx)
  have h1 := k328dsc_card_cent (MulAut.conj c) CFSG.EvenSporadicStandard.RuStd.S2.ruThreeX0
  rw [MulAut.conj_apply, CFSG.EvenSporadicStandard.RuStd.S2.card_centralizer_ruThreeX0] at h1
  rw [k328dsc_card_cent e' x, ← k328dsc_cent_zpowers hc, ← h1]
  omega

private theorem k328dsc_on
    {S : Type} [Group S] (h : IsSpor S .ONan) {x : S}
    (hx : orderOf x = 3) : ¬ 64 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set S)) := by
  obtain ⟨e⟩ := h
  let e' : S ≃* CFSG.Blueprint.NativeSporadic.ON := e
  obtain ⟨k, hk⟩ := CFSG.RankThree.Native.onThree_fusion
    CFSG.RankThree.Native.orderOf_onThreeElt
    (show orderOf (e' x) = 3 by rw [MulEquiv.orderOf_eq]; exact hx)
  have h1 := CFSG.RankThree.Native.card_centralizer_conj_eq CFSG.RankThree.Native.onThreeElt k⁻¹
  rw [inv_inv, hk, CFSG.RankThree.Native.card_centralizer_onThreeElt] at h1
  rw [@k328dsc_card_cent S CFSG.Blueprint.NativeSporadic.ON _ Units.instGroup e' x, h1]
  omega

theorem k328det_sporCentData :
    ∀ (S : Type) [Group S] [Finite S] (s : TauCeti.SporadicName),
      (s = .M24 ∨ s = .J2 ∨ s = .He ∨ s = .Ru ∨ s = .ONan) → IsSpor S s →
        ∀ x : S, orderOf x = 3 → ¬ 64 ∣ Nat.card (Subgroup.centralizer ({x} : Set S)) := by
  intro S _ _ s hs hS x hx
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact k328dsc_m24 hS hx
  · exact k328dsc_j2 hS hx
  · exact k328dsc_he hS hx
  · exact k328dsc_ru hS hx
  · exact k328dsc_on hS hx

private theorem k328dj4c_open_of_quasisimple {Q : Type} [Group Q] (h : CFSG.IsQuasisimple Q) :
    CFSG.Open.IsQuasisimple Q :=
  ⟨h.1.commutator_eq_top, h.2.1⟩

private theorem k328dj4c_centEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T) (x : S) :
    Nonempty (↥(Subgroup.centralizer ({x} : Set S)) ≃* ↥(Subgroup.centralizer ({e x} : Set T))) :=
  ⟨((Subgroup.centralizer ({x} : Set S)).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (CFSG.Quasithin.H13.Ch4.J4Blk.map_centralizer_singleton e x))⟩

private theorem k328dj4c_transport {S T : Type} [Group S] [Group T] (e : S ≃* T) {x : S}
    (hq : CFSG.Open.IsQuasisimple ↥(Subgroup.centralizer ({e x} : Set T)))
    (hc : Nat.card ↥(Subgroup.center ↥(Subgroup.centralizer ({e x} : Set T))) = 6) :
    CFSG.Open.IsQuasisimple ↥(Subgroup.centralizer ({x} : Set S)) ∧
      Nat.card ↥(Subgroup.center ↥(Subgroup.centralizer ({x} : Set S))) = 6 := by
  obtain ⟨eC⟩ := k328dj4c_centEquiv e x
  refine ⟨isQuasisimple_of_mulEquiv' eC.symm hq, ?_⟩
  rw [← hc]
  exact Nat.card_congr (Subgroup.centerCongr eC).toEquiv

theorem k328det_j4CentData :
    ∀ (S : Type) [Group S] [Finite S], IsSpor S .J4 → ∀ x : S, orderOf x = 3 →
      CFSG.Open.IsQuasisimple ↥(Subgroup.centralizer ({x} : Set S)) ∧
        Nat.card ↥(Subgroup.center ↥(Subgroup.centralizer ({x} : Set S))) = 6 := by
  intro S _ _ hS x hx
  obtain ⟨e⟩ := hS
  let φ : S ≃* ↥CFSG.Sporadic.J4.J :=
    e.trans (CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat)
  have hφx : orderOf (φ x) = 3 := by rw [MulEquiv.orderOf_eq]; exact hx
  obtain ⟨hq, hc, -⟩ := CFSG.Quasithin.H13.Ch4.J4Blk.centralizer_of_orderOf_three hφx
  exact @k328dj4c_transport S ↥CFSG.Sporadic.J4.J _ (Subgroup.toGroup _) φ x
    (k328dj4c_open_of_quasisimple hq) hc

private theorem k328dj4x_isQuasisimple_of_open {Q : Type} [Group Q]
    (h : CFSG.Open.IsQuasisimple Q) : CFSG.IsQuasisimple Q := by
  refine ⟨⟨h.1⟩, h.2, ?_⟩
  by_contra hcon
  push Not at hcon
  have : Group.IsPerfect Q := ⟨h.1⟩
  have := h.2.toNontrivial
  exact Group.IsPerfect.not_isMulCommutative (Q ⧸ Subgroup.center Q) ⟨⟨hcon⟩⟩

private theorem k328dj4x_exists_gen {S : Type} [Group S] [Finite S] {Z : Subgroup S}
    (hZ : Nat.card Z = 3) :
    ∃ z : S, orderOf z = 3 ∧
      Subgroup.centralizer (Z : Set S) = Subgroup.centralizer ({z} : Set S) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z) 3 (by rw [hZ])
  have hzo : orderOf (z : S) = 3 := by rw [Subgroup.orderOf_coe]; exact hz
  have hzp : Subgroup.zpowers (z : S) = Z := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 z.2) ?_
    rw [Nat.card_zpowers, hzo, hZ]
  have h1 : Subgroup.centralizer ((Subgroup.zpowers (z : S) : Subgroup S) : Set S) =
      Subgroup.centralizer ({(z : S)} : Set S) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hzp] at h1
  exact ⟨z, hzo, h1⟩

private theorem k328dj4x_false_of_central {S : Type} [Group S] {X C : Subgroup S} (hXC : X ≤ C)
    (hle : X.subgroupOf C ≤ Subgroup.center ↥C) (hperf : commutator ↥X = ⊤)
    (hcen : Nat.card ↥(Subgroup.center ↥X) = 3) : False := by
  have hcomm : ∀ a b : ↥X, a * b = b * a := fun a b => by
    have ha : (⟨a, hXC a.2⟩ : ↥C) ∈ Subgroup.center ↥C := hle (Subgroup.mem_subgroupOf.2 a.2)
    exact Subtype.ext (congrArg Subtype.val (Subgroup.mem_center_iff.1 ha ⟨b, hXC b.2⟩)).symm
  have : IsMulCommutative ↥X := ⟨⟨hcomm⟩⟩
  have : Group.IsPerfect ↥X := ⟨hperf⟩
  have : Subsingleton ↥X := inferInstance
  have h1 : Nat.card ↥(Subgroup.center ↥X) = 1 := Nat.card_of_subsingleton 1
  omega

theorem k328det_j4Excluded :
    (∀ (S : Type) [Group S] [Finite S], IsSpor S .J4 → ∀ x : S, orderOf x = 3 →
      CFSG.Open.IsQuasisimple ↥(Subgroup.centralizer ({x} : Set S)) ∧
        Nat.card ↥(Subgroup.center ↥(Subgroup.centralizer ({x} : Set S))) = 6) →
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → IsSpor S .J4 → ¬ K328DetPosIn S := by
  rintro hcent S _ _ _ hS ⟨Z, X, hp, -⟩
  obtain ⟨hZ, -, hXC, hsub, hq, hcen, -⟩ := hp
  obtain ⟨z, hzo, hC⟩ := k328dj4x_exists_gen hZ
  obtain ⟨hCq, hC6⟩ := hcent S hS z hzo
  rw [hC] at hXC hsub
  rcases CFSG.CGT.PushingUpLit.CGT6.isSubnormal_le_center_or_eq_top_of_quasisimple
      (k328dj4x_isQuasisimple_of_open hCq) hsub with hle | htop
  · exact k328dj4x_false_of_central hXC hle hq.1 hcen
  · have hXeq : X = Subgroup.centralizer ({z} : Set S) :=
      le_antisymm hXC (Subgroup.subgroupOf_eq_top.1 htop)
    rw [hXeq] at hcen
    omega

theorem k328det_spor_order_excluded
    {S : Type} [Group S] [Finite S] {s : TauCeti.SporadicName}
    (hs : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .HS ∨ s = .J3) (h : IsSpor S s) :
    ¬ K328DetPosIn S := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := k328det_sporOrders S
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact k328det_not_posIn_of_card (by rw [h1 h]; norm_num) (by rw [h1 h]; norm_num)
  · exact k328det_not_posIn_of_card (by rw [h2 h]; norm_num) (by rw [h2 h]; norm_num)
  · exact k328det_not_posIn_of_card (by rw [h3 h]; norm_num) (by rw [h3 h]; norm_num)
  · exact k328det_not_posIn_of_card (by rw [h4 h]; norm_num) (by rw [h4 h]; norm_num)
  · exact k328det_not_posIn_of_card (by rw [h5 h]; norm_num) (by rw [h5 h]; norm_num)
  · exact k328det_not_posIn_of_card (by rw [h6 h]; norm_num) (by rw [h6 h]; norm_num)

theorem k328det_spor_excluded
    {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    {s : TauCeti.SporadicName}
    (hs : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J2 ∨ s = .HS ∨ s = .He ∨
      s = .Ru ∨ s = .J4) (h : IsSpor S s) : ¬ K328DetPosIn S := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact k328det_spor_order_excluded (by simp) h
  · exact k328det_spor_order_excluded (by simp) h
  · exact k328det_spor_order_excluded (by simp) h
  · exact k328det_spor_order_excluded (by simp) h
  · exact k328det_not_posIn_of_cent (k328det_sporCentData S _ (by simp) h)
  · exact k328det_not_posIn_of_cent (k328det_sporCentData S _ (by simp) h)
  · exact k328det_spor_order_excluded (by simp) h
  · exact k328det_not_posIn_of_cent (k328det_sporCentData S _ (by simp) h)
  · exact k328det_not_posIn_of_cent (k328det_sporCentData S _ (by simp) h)
  · exact k328det_j4Excluded k328det_j4CentData S hS h

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
