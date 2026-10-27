module

public import CFSG.Timmesfeld.Bridge.OddRootLocal
import CFSG.Timmesfeld.Bridge.OddLocalRoot
import CFSG.Timmesfeld.Bridge.OddRootSplit
import CFSG.Timmesfeld.Bridge.OddTranspSecondKind
public import CFSG.StronglyEmbedded.PSL2Facts
public import CFSG.Timmesfeld.Bridge.OddRootBasic

public section

namespace CFSG.Timmesfeld.Bridge.OddRoot

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Bridge.OddTransp
  CFSG.Timmesfeld.Bridge.OddLocal CFSG.BenderSuzuki CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem mk_eq_one_iff_mem_Qof {d x s : G} (hsX : s ∈ rootGen D d x) :
    QuotientGroup.mk' (CFSG.pCore 2 (rootGen D d x)) (⟨s, hsX⟩ : rootGen D d x) = 1 ↔
      s ∈ Qof D d x := by
  let X := rootGen D d x
  let Q : Subgroup X := CFSG.pCore 2 X
  constructor
  · intro h
    exact ⟨⟨s, hsX⟩, (QuotientGroup.eq_one_iff (N := Q) _).mp h, rfl⟩
  · rintro ⟨q, hq, hqs⟩
    have hmem : (⟨s, hsX⟩ : X) ∈ Q := by
      rw [show (⟨s, hsX⟩ : X) = q from Subtype.ext hqs.symm]
      exact hq
    exact (QuotientGroup.eq_one_iff (N := Q) _).mpr hmem

private theorem mul_mem_Qof_of_mk_eq {d x s t : G} (hsX : s ∈ rootGen D d x)
    (htX : t ∈ rootGen D d x) (ht2 : t * t = 1)
    (h : QuotientGroup.mk' (CFSG.pCore 2 (rootGen D d x)) (⟨s, hsX⟩ : rootGen D d x) =
      QuotientGroup.mk' (CFSG.pCore 2 (rootGen D d x)) (⟨t, htX⟩ : rootGen D d x)) :
    s * t ∈ Qof D d x := by
  let X := rootGen D d x
  let Q : Subgroup X := CFSG.pCore 2 X
  have hstX : s * t ∈ X := X.mul_mem hsX htX
  apply (mk_eq_one_iff_mem_Qof hstX).mp
  have h1 : (⟨s * t, hstX⟩ : X) = (⟨s, hsX⟩ : X) * (⟨t, htX⟩ : X) := rfl
  rw [h1, map_mul, h]
  have h2 : (⟨t, htX⟩ : X) * (⟨t, htX⟩ : X) = 1 := Subtype.ext (by simpa using ht2)
  rw [← map_mul, h2, map_one]

private theorem conj_mem_rootSet_of_conj_eq (hS : Asc72.Setup G D) {z d e : G}
    (hzd : z * d * z⁻¹ = d) (he : e ∈ rootSet D d) : z * e * z⁻¹ ∈ rootSet D d := by
  have h := rootSet_conj hS.isClass z d
  rw [hzd] at h
  rw [h]
  exact ⟨e, he, rfl⟩

private theorem conjClosure_le_of_normal {X N A : Subgroup G} {w : G}
    (hNX : ∀ g ∈ X, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (hA : A ≤ X) (hw : w ∈ N) :
    conjClosure A w ≤ N := by
  rw [conjClosure, Subgroup.closure_le]
  rintro _ ⟨g, hg, rfl⟩
  exact hNX g (hA hg) w hw

private theorem map_sylow_is_maximal {Y : Subgroup G} (S : Sylow 2 Y) (T : Subgroup G)
    (hST : Subgroup.map Y.subtype (S : Subgroup Y) ≤ T) (hTY : T ≤ Y)
    (hT2 : IsPGroup 2 T) :
    T = Subgroup.map Y.subtype (S : Subgroup Y) := by
  have hT'2 : IsPGroup 2 (Subgroup.comap Y.subtype T) :=
    hT2.comap_of_injective Y.subtype Y.subtype_injective
  have hSle : (S : Subgroup Y) ≤ Subgroup.comap Y.subtype T := by
    intro s hs
    exact hST (Subgroup.mem_map_of_mem Y.subtype hs)
  have hEq : Subgroup.comap Y.subtype T = (S : Subgroup Y) := S.is_maximal' hT'2 hSle
  refine le_antisymm ?_ hST
  intro t ht
  have htY : t ∈ Y := hTY ht
  have ht' : (⟨t, htY⟩ : Y) ∈ (S : Subgroup Y) := by
    rw [← hEq]
    exact ht
  exact Subgroup.mem_map_of_mem Y.subtype ht'

theorem involution_mem_D_of_psl2 (h : Hyp G D) {Y : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (e : Y ≃* PSL2Model n) {a : G} (haY : a ∈ Y) (haD : a ∈ D) {t : G} (htY : t ∈ Y)
    (ht2 : t * t = 1) (ht1 : t ≠ 1) : t ∈ D := by
  let aY : Y := ⟨a, haY⟩
  have ha2 : aY * aY = 1 := Subtype.ext (by simpa [aY] using h.setup.oddT.mul_self_eq_one haD)
  have ha1 : aY ≠ 1 := by
    intro h1
    exact h.setup.oddT.ne_one haD (by simpa [aY] using congrArg Subtype.val h1)
  obtain ⟨S, haS⟩ := IsPGroup.exists_le_sylow (isPGroup_two_zpowers_of_mul_self_eq_one ha2)
  have hn0 : n ≠ 0 := Nat.ne_of_gt (by have := hn; omega)
  have hL2 : IsL2Pair Y (S : Subgroup Y) (2 ^ n) :=
    IsL2Pair.of_psl_sylow (f := n) hn0 ⟨e⟩ S
  let tY : Y := ⟨t, htY⟩
  have htY2 : tY * tY = 1 := Subtype.ext ht2
  have htY1 : tY ≠ 1 := fun h1 => ht1 (by simpa [tY] using congrArg Subtype.val h1)
  obtain ⟨k, hk⟩ := isConj_iff.mp (hL2.isConj_of_mul_self_eq_one ha2 ha1 htY2 htY1)
  have h' := h.setup.normal (k : G) a haD
  rwa [show (k : G) * a * (k : G)⁻¹ = t from by
    have := congrArg Subtype.val hk
    simpa [aY, tY, mul_assoc] using this] at h'

private theorem exists_sylow_rootSet (h : Hyp G D) {Y : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (e : Y ≃* PSL2Model n) {a : G} (haY : a ∈ Y) (haD : a ∈ D) :
    ∃ S : Sylow 2 Y, (⟨a, haY⟩ : Y) ∈ (S : Subgroup Y) ∧
      ∀ s ∈ S, (s : G) ≠ 1 → (s : G) ∈ rootSet D a := by
  let aY : Y := ⟨a, haY⟩
  have ha2 : aY * aY = 1 := Subtype.ext (by simpa using h.setup.oddT.mul_self_eq_one haD)
  have ha1 : aY ≠ 1 := by
    intro h1
    exact h.setup.oddT.ne_one haD (by simpa [aY] using congrArg Subtype.val h1)
  obtain ⟨S, haS⟩ := IsPGroup.exists_le_sylow (isPGroup_two_zpowers_of_mul_self_eq_one ha2)
  have hL2 : IsL2Pair Y (S : Subgroup Y) (2 ^ n) :=
    IsL2Pair.of_psl_sylow (f := n) (by omega) ⟨e⟩ S
  have hel : IsElemAbelian 2 (S : Subgroup Y) := hL2.isElemAbelian
  have memD : ∀ t : Y, t * t = 1 → t ≠ 1 → (t : G) ∈ D := fun t ht2 ht1 =>
    involution_mem_D_of_psl2 h hn e haY haD t.2 (by simpa using congrArg Subtype.val ht2)
      (fun h1 => ht1 (Subtype.ext h1))
  refine ⟨S, haS (Subgroup.mem_zpowers aY), ?_⟩
  intro s hsS hs1
  have hs2 : (s : Y) * (s : Y) = 1 := by
    have h2 := hel.2 s hsS
    simpa [pow_two] using h2
  have hs1' : s ≠ 1 := fun h1 => hs1 (by simpa using congrArg Subtype.val h1)
  have hsD : (s : G) ∈ D := memD s hs2 hs1'
  by_cases hsa : (s : G) = a
  · rw [hsa]
    exact mem_rootSet_self haD
  · have hscomm2 : (s : G) * a = a * (s : G) := by
      have hprev := CFSG.CGT.Timmesfeld75.elemAbelian_mul_comm hel
        (haS (Subgroup.mem_zpowers aY)) hsS
      exact (Subtype.ext_iff.mp hprev).symm
    have hs2G : (s : G) * (s : G) = 1 := by simpa using congrArg Subtype.val hs2
    have ha2G : a * a = 1 := by simpa [aY] using congrArg Subtype.val ha2
    have hsaD : (s : G) * a ∈ D := by
      let tY : Y := s * aY
      have htY : tY * tY = 1 := by
        refine Subtype.ext ?_
        show ((s : G) * a) * ((s : G) * a) = 1
        calc ((s : G) * a) * ((s : G) * a)
            = (s : G) * (a * (s : G)) * a := by group
          _ = (s : G) * ((s : G) * a) * a := by rw [← hscomm2]
          _ = ((s : G) * (s : G)) * (a * a) := by group
          _ = 1 := by rw [hs2G, ha2G, mul_one]
      have ht1 : tY ≠ 1 := by
        intro h1
        have h2 : (s : G) * a = 1 := by simpa [tY] using congrArg Subtype.val h1
        exact hsa (h.setup.oddT.eq_of_mul_eq_one hsD h2)
      have := memD tY htY ht1
      simpa [tY] using this
    exact ⟨hsD, fun f hf => by
      have hiff := OddTransp.commute_iff_of_mul_mem h.setup hsD haD hsa hscomm2 hsaD hf
      exact ⟨fun h => (hiff.mp h.symm).symm, fun h => (hiff.mpr h.symm).symm⟩⟩

private theorem exists_third_quot (h : Hyp G D) {d x v : G}
    (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x) (hv : v ∈ rootSet D d)
    (hvd : v ≠ d) (hdv : d * v ∈ rootSet D d) (hpx : PSL2Pair D d x) :
    let X := rootGen D d x
    let Q : Subgroup X := CFSG.pCore 2 X
    let π : X →* X ⧸ Q := QuotientGroup.mk' Q
    let dX : X := ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩
    let vX : X := ⟨v, mem_rootGen_of_mem hv⟩
    let dvX : X := ⟨d * v, mem_rootGen_of_mem hdv⟩
    ∃ (S : Sylow 2 (X ⧸ Q)) (t : X ⧸ Q),
      orderOf t = 2 ∧ t ∉ S ∧ π dX ∈ S ∧ π vX ∈ S ∧ π dvX ∈ S ∧
      π dX ≠ 1 ∧ π vX ≠ 1 ∧ π dvX ≠ 1 ∧
      Subgroup.closure ({π dX, π vX, t} : Set (X ⧸ Q)) = ⊤ := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hpx
  let X := rootGen D d x
  let Q : Subgroup X := CFSG.pCore 2 X
  let π : X →* X ⧸ Q := QuotientGroup.mk' Q
  let dX : X := ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩
  let xX : X := ⟨x, mem_rootGen_left d x⟩
  let vX : X := ⟨v, mem_rootGen_of_mem hv⟩
  let dvX : X := ⟨d * v, mem_rootGen_of_mem hdv⟩
  have hd2 : dX * dX = 1 := Subtype.ext (by simpa [dX] using h.setup.oddT.mul_self_eq_one hd)
  have hv2 : vX * vX = 1 := Subtype.ext (by simpa [vX] using h.setup.oddT.mul_self_eq_one hv.1)
  have hcommG : Commute d v := commute_of_mem_rootSet hd (mem_rootSet_self hd) hv
  have hcomm : Commute dX vX := Subtype.ext (by simpa [dX, vX] using hcommG.eq)
  have hne : dX ≠ vX := by
    intro h1
    exact hvd (by simpa [dX, vX] using (congrArg Subtype.val h1).symm)
  have hd1 : π dX ≠ 1 := (mk_eq_one_iff_mem_Qof dX.2).not.mpr
    (not_mem_Qof_self h.setup.oddT hd hx hdx)
  have hv1 : π vX ≠ 1 := (mk_eq_one_iff_mem_Qof vX.2).not.mpr
    (not_mem_Qof_of_mem_rootSet h.setup.oddT hx hdx hv)
  have hdv1 : π dvX ≠ 1 := (mk_eq_one_iff_mem_Qof dvX.2).not.mpr
    (not_mem_Qof_of_mem_rootSet h.setup.oddT hx hdx hdv)
  have hdord : orderOf (π dX) = 2 := orderOf_eq_prime (by rw [pow_two, ← map_mul, hd2, map_one]) hd1
  have hvord : orderOf (π vX) = 2 := orderOf_eq_prime (by rw [pow_two, ← map_mul, hv2, map_one]) hv1
  have hpre : IsOddTransp (((↑) : X → G) ⁻¹' D) := IsOddTransp.preimage h.setup.oddT X
  have hnotcommX : ¬ Commute dX xX := by
    intro hc
    exact hdx (by simpa [dX, xX] using hc.map X.subtype)
  have hnotcomm : ¬ Commute (π dX) (π xX) := fun hc =>
    hnotcommX ((OddLocal.commute_iff_of_mem_pCore (C := ((↑) : X → G) ⁻¹' D) hpre
      (CFSG.pCore_isPGroup (p := 2) (G := X)) (a := dX) hd (b := xX) hx).mp hc)
  obtain ⟨S, hdS⟩ := IsPGroup.exists_le_sylow
    (isPGroup_two_zpowers_of_mul_self_eq_one (show π dX * π dX = 1 by rw [← map_mul, hd2, map_one]))
  have hL2 : IsL2Pair (X ⧸ Q) (S : Subgroup (X ⧸ Q)) (2 ^ n) :=
    IsL2Pair.of_psl_sylow (f := n) (by omega) ⟨e⟩ S
  have hel : IsElemAbelian 2 (S : Subgroup (X ⧸ Q)) := hL2.isElemAbelian
  have hdS' : π dX ∈ S := hdS (Subgroup.mem_zpowers (π dX))
  have hvS : π vX ∈ S :=
    psl2_mem_sylow_of_commute e hn hd1 hdS' (hcomm.map π).symm
  have hdvS : π dvX ∈ S := by
    have h : (dvX : X ⧸ Q) = π dX * π vX := by
      show π dvX = π dX * π vX
      rw [← map_mul]
      rfl
    rw [show π dvX = (dvX : X ⧸ Q) from rfl, h]
    exact S.mul_mem hdS' hvS
  have hxS : π xX ∉ S := by
    intro hxS'
    exact hnotcomm (elemAbelian_mul_comm hel hdS' hxS')
  have hvpow : π vX ^ 2 = 1 := by
    simpa [hvord] using pow_orderOf_eq_one (π vX)
  have hneπ : π dX ≠ π vX := fun hdv => hdv1 <| by
    rw [show dvX = dX * vX from Subtype.ext rfl, map_mul, hdv]; simpa [pow_two] using hvpow
  obtain ⟨t, htord, hgen⟩ :=
    psl2_involutionThreeGen e hn (π dX) (π vX) hdord hvord hneπ (hcomm.map π)
  have ht1 : t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at htord
    exact absurd htord (by norm_num)
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [htord, pow_two] at this
  have htS : t ∉ S := fun ht => hxS <| (Subgroup.closure_le (S : Subgroup (↥X ⧸ Q))).mpr
    (by simp [Set.insert_subset_iff, hdS', hvS, ht]) (hgen ▸ Subgroup.mem_top (π xX))
  exact ⟨S, t, htord, htS, hdS', hvS, hdvS, hd1, hv1, hdv1, hgen⟩

private theorem exists_third_lift (h : Hyp G D) {d x v : G}
    (hd : d ∈ D) (hv : v ∈ rootSet D d) (hdv : d * v ∈ rootSet D d) (hpx : PSL2Pair D d x)
    (S : Sylow 2 (rootGen D d x ⧸ CFSG.pCore 2 (rootGen D d x)))
    (t : rootGen D d x ⧸ CFSG.pCore 2 (rootGen D d x))
    (htord : orderOf t = 2) (htS : t ∉ S)
    (hdS' : QuotientGroup.mk' (CFSG.pCore 2 (rootGen D d x))
      ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩ ∈ S)
    (hvS : QuotientGroup.mk' (CFSG.pCore 2 (rootGen D d x))
      ⟨v, mem_rootGen_of_mem hv⟩ ∈ S)
    (hdvS : QuotientGroup.mk' (CFSG.pCore 2 (rootGen D d x))
      ⟨d * v, mem_rootGen_of_mem hdv⟩ ∈ S)
    (hd1 : QuotientGroup.mk' (CFSG.pCore 2 (rootGen D d x))
      ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩ ≠ 1)
    (hv1 : QuotientGroup.mk' (CFSG.pCore 2 (rootGen D d x))
      ⟨v, mem_rootGen_of_mem hv⟩ ≠ 1)
    (hdv1 : QuotientGroup.mk' (CFSG.pCore 2 (rootGen D d x))
      ⟨d * v, mem_rootGen_of_mem hdv⟩ ≠ 1) :
    ∃ y : G, ∃ hy : y ∈ rootGen D d x, y ∈ D ∧
      QuotientGroup.mk' (CFSG.pCore 2 (rootGen D d x)) ⟨y, hy⟩ = t ∧
      ¬ Commute y d ∧ ¬ Commute y v ∧ ¬ Commute y (d * v) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hpx
  let X := rootGen D d x
  let Q : Subgroup X := CFSG.pCore 2 X
  let π : X →* X ⧸ Q := QuotientGroup.mk' Q
  let dX : X := ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩
  let vX : X := ⟨v, mem_rootGen_of_mem hv⟩
  let dvX : X := ⟨d * v, mem_rootGen_of_mem hdv⟩
  have hd2 : dX * dX = 1 := Subtype.ext (by simpa [dX] using h.setup.oddT.mul_self_eq_one hd)
  have hL2 : IsL2Pair (X ⧸ Q) (S : Subgroup (X ⧸ Q)) (2 ^ n) :=
    IsL2Pair.of_psl_sylow (f := n) (by omega) ⟨e⟩ S
  have ht1 : t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at htord
    exact absurd htord (by norm_num)
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [htord, pow_two] at this
  have hconj := hL2.isConj_of_mul_self_eq_one (by rw [← map_mul, hd2, map_one]) hd1
    (by simpa using ht2) ht1
  obtain ⟨k, hk⟩ := isConj_iff.mp hconj
  obtain ⟨kX, rfl⟩ := QuotientGroup.mk'_surjective Q k
  let y : G := (kX : X) * d * (kX : X)⁻¹
  have hyD : y ∈ D := h.setup.normal (kX : X) d hd
  have hyX : y ∈ X := X.mul_mem (X.mul_mem kX.2 (mem_rootGen_of_mem (mem_rootSet_self hd)))
    (X.inv_mem kX.2)
  have hybar : π ⟨y, hyX⟩ = t := by
    have h1 : (⟨y, hyX⟩ : X) = kX * dX * kX⁻¹ := rfl
    rw [h1]
    show π kX * π dX * (π kX)⁻¹ = t
    rw [hk]
  have hnotcomm_d : ¬ Commute y d := by
    intro hc
    have hcX : Commute (⟨y, hyX⟩ : X) dX := Subtype.ext (by simpa [dX] using hc.eq)
    have hc' : Commute t (π dX) := by
      rw [← hybar]
      exact hcX.map π
    exact htS (psl2_mem_sylow_of_commute e hn hd1 hdS' hc')
  have hnotcomm_v : ¬ Commute y v := by
    intro hc
    have hcX : Commute (⟨y, hyX⟩ : X) vX := Subtype.ext (by simpa [vX] using hc.eq)
    have hc' : Commute t (π vX) := by
      rw [← hybar]
      exact hcX.map π
    exact htS (psl2_mem_sylow_of_commute e hn hv1 hvS hc')
  have hnotcomm_dv : ¬ Commute y (d * v) := by
    intro hc
    have hcX : Commute (⟨y, hyX⟩ : X) dvX := Subtype.ext (by simpa [dvX] using hc.eq)
    have hc' : Commute t (π dvX) := by
      rw [← hybar]
      exact hcX.map π
    exact htS (psl2_mem_sylow_of_commute e hn hdv1 hdvS hc')
  exact ⟨y, hyX, hyD, hybar, hnotcomm_d, hnotcomm_v, hnotcomm_dv⟩

private theorem third_sup {d x v y : G}
    (hd : d ∈ D) (hv : v ∈ rootSet D d) (hyX : y ∈ rootGen D d x)
    (t : rootGen D d x ⧸ CFSG.pCore 2 (rootGen D d x))
    (hybar : QuotientGroup.mk' (CFSG.pCore 2 (rootGen D d x)) ⟨y, hyX⟩ = t)
    (hgen : let X := rootGen D d x
      let Q : Subgroup X := CFSG.pCore 2 X
      let π : X →* X ⧸ Q := QuotientGroup.mk' Q
      Subgroup.closure ({π ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩,
        π ⟨v, mem_rootGen_of_mem hv⟩, t} : Set (X ⧸ Q)) = ⊤) :
    Subgroup.closure ({y, d, v} : Set G) ⊔ Qof D d x = rootGen D d x := by
  let X := rootGen D d x
  let Q : Subgroup X := CFSG.pCore 2 X
  let π : X →* X ⧸ Q := QuotientGroup.mk' Q
  let dX : X := ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩
  let vX : X := ⟨v, mem_rootGen_of_mem hv⟩
  have hgen' : Subgroup.closure ({π dX, π vX, t} : Set (X ⧸ Q)) = ⊤ := by
    simpa only [X, Q, π, dX, vX] using hgen
  have hX0le : Subgroup.closure ({y, d, v} : Set G) ≤ X := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl | rfl)
    · exact hyX
    · exact mem_rootGen_of_mem (mem_rootSet_self hd)
    · exact mem_rootGen_of_mem hv
  apply le_antisymm (sup_le hX0le (Qof_le_rootGen d x))
  intro g hg
  have hmap : Subgroup.map π (Subgroup.closure ({⟨y, hyX⟩, dX, vX} : Set X)) = ⊤ := by
    rw [MonoidHom.map_closure]
    have hset : π '' ({⟨y, hyX⟩, dX, vX} : Set X) =
        ({π dX, π vX, t} : Set (X ⧸ Q)) := by
      ext z
      simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨w, (rfl | rfl | rfl), rfl⟩
        · exact Or.inr (Or.inr hybar)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · rintro (rfl | rfl | rfl)
        · exact ⟨dX, Or.inr (Or.inl rfl), rfl⟩
        · exact ⟨vX, Or.inr (Or.inr rfl), rfl⟩
        · exact ⟨⟨y, hyX⟩, Or.inl rfl, hybar⟩
    rw [hset, hgen']
  have hmem : π ⟨g, hg⟩ ∈ Subgroup.map π (Subgroup.closure ({⟨y, hyX⟩, dX, vX} : Set X)) := by
    rw [hmap]
    exact Subgroup.mem_top _
  obtain ⟨w, hw, hwπ⟩ := Subgroup.mem_map.mp hmem
  have hwG : (w : G) ∈ Subgroup.closure ({y, d, v} : Set G) := by
    have : (w : G) ∈ Subgroup.map X.subtype (Subgroup.closure ({⟨y, hyX⟩, dX, vX} : Set X)) :=
      Subgroup.mem_map_of_mem X.subtype hw
    rwa [show Subgroup.map X.subtype (Subgroup.closure ({⟨y, hyX⟩, dX, vX} : Set X)) =
      Subgroup.closure ({y, d, v} : Set G) from by
        rw [MonoidHom.map_closure]
        congr 1
        ext z
        simp [dX, vX]] at this
  have hq : (w : G)⁻¹ * g ∈ Qof D d x := by
    have h1 : (⟨(w : G)⁻¹ * g, X.mul_mem (X.inv_mem (hX0le hwG)) hg⟩ : X) ∈ Q := by
      rw [← QuotientGroup.ker_mk' Q, MonoidHom.mem_ker]
      have h2 : π ⟨(w : G)⁻¹ * g, X.mul_mem (X.inv_mem (hX0le hwG)) hg⟩ =
          (π w)⁻¹ * π ⟨g, hg⟩ := by
        rw [show (⟨(w : G)⁻¹ * g, X.mul_mem (X.inv_mem (hX0le hwG)) hg⟩ : X) =
          (w : X)⁻¹ * (⟨g, hg⟩ : X) from Subtype.ext rfl, map_mul, map_inv]
      rw [h2, hwπ, inv_mul_cancel]
    exact ⟨⟨_, X.mul_mem (X.inv_mem (hX0le hwG)) hg⟩, h1, rfl⟩
  have hgw : w * ((w : G)⁻¹ * g) = g := by group
  rw [← hgw]
  exact Subgroup.mul_mem (Subgroup.closure ({y, d, v} : Set G) ⊔ Qof D d x)
    (Subgroup.mem_sup_left (S := Subgroup.closure ({y, d, v} : Set G))
      (T := Qof D d x) hwG)
    (Subgroup.mem_sup_right (S := Subgroup.closure ({y, d, v} : Set G))
      (T := Qof D d x) hq)

private theorem exists_third_involution (h : Hyp G D) {d x : G}
    (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x) (hpx : PSL2Pair D d x) :
    ∃ v y : G, v ∈ rootSet D d ∧ d * v ∈ rootSet D d ∧ y ∈ D ∧ y ∈ rootGen D d x ∧
      Subgroup.closure ({y, d, v} : Set G) ⊔ Qof D d x = rootGen D d x ∧
      ¬ Commute y d ∧ ¬ Commute y v ∧ ¬ Commute y (d * v) := by
  obtain ⟨v, hv, hvd, hdv⟩ := exists_rootSet_triple h.setup h.sq hd
  let X := rootGen D d x
  let Q : Subgroup X := CFSG.pCore 2 X
  let π : X →* X ⧸ Q := QuotientGroup.mk' Q
  let dX : X := ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩
  let vX : X := ⟨v, mem_rootGen_of_mem hv⟩
  obtain ⟨S, t, htord, htS, hdS', hvS, hdvS, hd1, hv1, hdv1, hgen⟩ :=
    exists_third_quot h hd hx hdx hv hvd hdv hpx
  obtain ⟨y, hyX, hyD, hybar, hnotcomm_d, hnotcomm_v, hnotcomm_dv⟩ :=
    exists_third_lift h hd hv hdv hpx S t htord htS hdS' hvS hdvS hd1 hv1 hdv1
  exact ⟨v, y, hv, hdv, hyD, hyX, third_sup hd hv hyX t hybar hgen,
    hnotcomm_d, hnotcomm_v, hnotcomm_dv⟩


private theorem isConj_of_not_commute_subtype (hD : IsOddTransp D) {X : Subgroup G}
    {X₀ : Subgroup X} {a b : X} (haX₀ : a ∈ X₀) (hbX₀ : b ∈ X₀)
    (ha : (a : G) ∈ D) (hb : (b : G) ∈ D) (h : ¬ Commute a b) :
    IsConj (⟨a, haX₀⟩ : X₀) (⟨b, hbX₀⟩ : X₀) := by
  have h' : ¬ Commute (a : G) (b : G) := fun hc => h (Subtype.ext hc.eq)
  obtain ⟨g, hg, hge⟩ := hD.exists_conj ha hb h'
  have hgX₀ : g ∈ X₀.map X.subtype := by
    have hle : Subgroup.closure ({(a : G), (b : G)} : Set G) ≤ X₀.map X.subtype := by
      rw [Subgroup.closure_le]
      rintro z (rfl | rfl)
      · exact Subgroup.mem_map_of_mem X.subtype haX₀
      · exact Subgroup.mem_map_of_mem X.subtype hbX₀
    exact hle hg
  obtain ⟨g₀, hg₀, hg₀val⟩ := Subgroup.mem_map.mp hgX₀
  refine isConj_iff.mpr ⟨⟨g₀, hg₀⟩, Subtype.ext ?_⟩
  apply Subtype.ext
  show (g₀ : G) * (a : G) * (g₀ : G)⁻¹ = (b : G)
  subst hg₀val
  exact hge

private theorem compl_third_map {d x v y : G} (hd : d ∈ D)
    (hv : v ∈ rootSet D d) (hyX : y ∈ rootGen D d x) :
    Subgroup.map (rootGen D d x).subtype
      (Subgroup.closure ({⟨y, hyX⟩, ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩,
        ⟨v, mem_rootGen_of_mem hv⟩} : Set (rootGen D d x))) =
      Subgroup.closure ({y, d, v} : Set G) := by
  rw [MonoidHom.map_closure]
  congr 1
  ext z
  simp

private theorem compl_third_sup {d x v y : G} (hd : d ∈ D)
    (hv : v ∈ rootSet D d) (hyX : y ∈ rootGen D d x)
    (hsup : Subgroup.closure ({y, d, v} : Set G) ⊔ Qof D d x = rootGen D d x) :
    Subgroup.closure ({⟨y, hyX⟩, ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩,
      ⟨v, mem_rootGen_of_mem hv⟩} : Set (rootGen D d x)) ⊔
      CFSG.pCore 2 (rootGen D d x) = ⊤ := by
  apply Subgroup.map_injective (rootGen D d x).subtype_injective
  calc Subgroup.map (rootGen D d x).subtype
        (Subgroup.closure ({⟨y, hyX⟩, ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩,
          ⟨v, mem_rootGen_of_mem hv⟩} : Set (rootGen D d x)) ⊔
          CFSG.pCore 2 (rootGen D d x))
      = Subgroup.map (rootGen D d x).subtype
          (Subgroup.closure ({⟨y, hyX⟩, ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩,
            ⟨v, mem_rootGen_of_mem hv⟩} : Set (rootGen D d x))) ⊔
          Subgroup.map (rootGen D d x).subtype (CFSG.pCore 2 (rootGen D d x)) :=
        Subgroup.map_sup _ _ _
    _ = Subgroup.closure ({y, d, v} : Set G) ⊔ Qof D d x := by
        rw [compl_third_map hd hv hyX]
        rfl
    _ = rootGen D d x := hsup
    _ = Subgroup.map (rootGen D d x).subtype ⊤ := by
        rw [Subgroup.map_top, Subgroup.range_subtype]

private theorem N_eq_bot_of_third (h : Hyp G D)
    {X : Subgroup G} {X₀ : Subgroup X} {yX0 dX0 vX0 : ↥X₀} {yX dX vX : X} {y d v : G}
    {n : ℕ}
    (hyval : (yX0 : G) = y) (hdval : (dX0 : G) = d) (hvval : (vX0 : G) = v)
    (hyXval : (yX0 : X) = yX) (hdXval : (dX0 : X) = dX) (hvXval : (vX0 : X) = vX)
    (hd : d ∈ D) (hv : v ∈ rootSet D d) (hdv : d * v ∈ rootSet D d) (hy : y ∈ D)
    (hnotyd : ¬ Commute yX dX) (hnotyv : ¬ Commute yX vX)
    (hnotydv : ¬ Commute yX (dX * vX))
    (hgen : Subgroup.closure ({yX0, dX0, vX0} : Set ↥X₀) = ⊤)
    (N : Subgroup ↥X₀) [N.Normal] (hN2 : IsPGroup 2 N) (hn : 2 ≤ n)
    (eN : ↥X₀ ⧸ N ≃* PSL2Model n) : N = ⊥ := by
  have hD' : IsOddTransp (((↑) : ↥X₀ → G) ⁻¹' D) := by
    have h1 : IsOddTransp (((↑) : X → G) ⁻¹' D) := IsOddTransp.preimage h.setup.oddT X
    have h2 : IsOddTransp (((↑) : ↥X₀ → X) ⁻¹' (((↑) : X → G) ⁻¹' D)) :=
      IsOddTransp.preimage h1 X₀
    exact h2
  have hN' : IsNormalSet (((↑) : ↥X₀ → G) ⁻¹' D) := by
    intro g z hz
    exact h.setup.normal (g : G) (z : G) hz
  have hdX0D : (dX0 : G) ∈ D := by rwa [hdval]
  have hvX0D : (vX0 : G) ∈ D := by rw [hvval]; exact hv.1
  have hdvX0D : ((dX0 * vX0 : ↥X₀) : G) ∈ D := by
    rw [show ((dX0 * vX0 : ↥X₀) : G) = d * v from by
      show (dX0 : G) * (vX0 : G) = d * v
      rw [hdval, hvval]]
    exact hdv.1
  have hyX0D : (yX0 : G) ∈ D := by rw [hyval]; exact hy
  have hcomm : Commute dX0 vX0 :=
    Subtype.ext (Subtype.ext (by
      change (dX0 : G) * (vX0 : G) = (vX0 : G) * (dX0 : G)
      rw [hdval, hvval]
      exact (commute_of_mem_rootSet hd (mem_rootSet_self hd) hv).eq))
  have hnotydX0 : ¬ Commute (yX0 : X) (dX0 : X) := fun hc => hnotyd (by
    rw [← hyXval, ← hdXval]
    exact hc)
  have hnotyvX0 : ¬ Commute (yX0 : X) (vX0 : X) := fun hc => hnotyv (by
    rw [← hyXval, ← hvXval]
    exact hc)
  have hnotydvX0 : ¬ Commute (yX0 : X) ((dX0 : X) * (vX0 : X)) := fun hc => hnotydv (by
    simpa [hyXval, hdXval, hvXval] using hc)
  have hy_d : IsConj yX0 dX0 :=
    isConj_of_not_commute_subtype h.setup.oddT yX0.2 dX0.2 hyX0D hdX0D hnotydX0
  have hy_v : IsConj yX0 vX0 :=
    isConj_of_not_commute_subtype h.setup.oddT yX0.2 vX0.2 hyX0D hvX0D hnotyvX0
  have hy_dv : IsConj yX0 (dX0 * vX0) :=
    isConj_of_not_commute_subtype h.setup.oddT yX0.2 (X₀.mul_mem dX0.2 vX0.2)
      hyX0D hdvX0D hnotydvX0
  have hcb : IsConj dX0 vX0 := (hy_d.symm).trans hy_v
  have hcab : IsConj dX0 (dX0 * vX0) := (hy_d.symm).trans hy_dv
  have hcy : IsConj dX0 yX0 := hy_d.symm
  exact eq_bot_of_quotient_psl2 hD' hN' hdX0D hvX0D hdvX0D hyX0D hcomm hcb hcab hcy
    hgen N hN2 hn eN

private theorem compl_third_quot {X : Subgroup G} {X₀ : Subgroup X} {n : ℕ}
    (hX₀Q : X₀ ⊔ CFSG.pCore 2 X = ⊤)
    (e : X ⧸ CFSG.pCore 2 X ≃* PSL2Model n) :
    ∃ (N : Subgroup ↥X₀) (_ : N.Normal), IsPGroup 2 N ∧
      N = Subgroup.comap X₀.subtype (CFSG.pCore 2 X) ∧
      Nonempty (↥X₀ ⧸ N ≃* PSL2Model n) := by
  let Q : Subgroup X := CFSG.pCore 2 X
  let π : X →* X ⧸ Q := QuotientGroup.mk' Q
  have hmapQ : Subgroup.map π Q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hmapπ : Subgroup.map π X₀ = ⊤ := by
    calc Subgroup.map π X₀ = Subgroup.map π X₀ ⊔ ⊥ := (sup_bot_eq _).symm
      _ = Subgroup.map π X₀ ⊔ Subgroup.map π Q := by rw [hmapQ]
      _ = Subgroup.map π (X₀ ⊔ Q) := (Subgroup.map_sup X₀ Q π).symm
      _ = Subgroup.map π ⊤ := by rw [hX₀Q]
      _ = ⊤ := Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective Q)
  let φ : ↥X₀ →* X ⧸ Q := π.comp X₀.subtype
  have hφsurj : Function.Surjective φ := by
    intro z
    have hz : z ∈ Subgroup.map π X₀ := by rw [hmapπ]; exact Subgroup.mem_top z
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz
    exact ⟨⟨w, hw⟩, hwz⟩
  let N : Subgroup ↥X₀ := Subgroup.comap X₀.subtype Q
  have hNker : N = φ.ker := by
    have hQ : (QuotientGroup.mk' Q).ker = Q := QuotientGroup.ker_mk' Q
    rw [show N = Subgroup.comap X₀.subtype (QuotientGroup.mk' Q).ker from by
      rw [hQ]]
    exact MonoidHom.comap_ker π X₀.subtype
  have hN2 : IsPGroup 2 N :=
    (CFSG.pCore_isPGroup (p := 2) (G := X)).comap_of_injective X₀.subtype
      X₀.subtype_injective
  haveI : N.Normal := inferInstance
  let eN : ↥X₀ ⧸ N ≃* PSL2Model n :=
    ((QuotientGroup.quotientMulEquivOfEq hNker).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj)).trans e
  exact ⟨N, inferInstance, hN2, rfl, ⟨eN⟩⟩

private theorem compl_third_finish {d x v y : G}
    {X₀ : Subgroup (rootGen D d x)} {n : ℕ} (hd : d ∈ D) (hn : 2 ≤ n)
    (hdX₀ : (⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩ : rootGen D d x) ∈ X₀)
    (N : Subgroup ↥X₀) [N.Normal] (hNbot : N = ⊥)
    (hNcomap : N = Subgroup.comap X₀.subtype (CFSG.pCore 2 (rootGen D d x)))
    (eN : ↥X₀ ⧸ N ≃* PSL2Model n)
    (hX₀map : Subgroup.map (rootGen D d x).subtype X₀ = Subgroup.closure ({y, d, v} : Set G))
    (hsup : Subgroup.closure ({y, d, v} : Set G) ⊔ Qof D d x = rootGen D d x) :
    ∃ (X₀ : Subgroup (rootGen D d x)) (n : ℕ), 2 ≤ n ∧
      Nonempty (↥X₀ ≃* PSL2Model n) ∧
      Subgroup.map (rootGen D d x).subtype X₀ ⊔ Qof D d x = rootGen D d x ∧
      Subgroup.map (rootGen D d x).subtype X₀ ⊓ Qof D d x = ⊥ ∧
      d ∈ Subgroup.map (rootGen D d x).subtype X₀ := by
  have hinf : Subgroup.map (rootGen D d x).subtype X₀ ⊓ Qof D d x = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgX₀, hgQ⟩
    obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp hgX₀
    have hx₀Q : x₀ ∈ CFSG.pCore 2 (rootGen D d x) := by
      obtain ⟨q, hq, hqeq⟩ := hgQ
      have : (x₀ : rootGen D d x) = q := Subtype.ext hqeq.symm
      rwa [this]
    have hx₀N : (⟨x₀, hx₀⟩ : ↥X₀) ∈ N := by
      rw [hNcomap]
      show (x₀ : rootGen D d x) ∈ CFSG.pCore 2 (rootGen D d x)
      exact hx₀Q
    rw [hNbot] at hx₀N
    have hx₀1 : x₀ = 1 := congrArg Subtype.val (Subgroup.mem_bot.mp hx₀N)
    rw [hx₀1]
    exact Subgroup.mem_bot.mpr rfl
  have hdC : d ∈ Subgroup.map (rootGen D d x).subtype X₀ :=
    Subgroup.mem_map_of_mem (rootGen D d x).subtype hdX₀
  let e₀ : ↥X₀ ≃* PSL2Model n :=
    ((QuotientGroup.quotientMulEquivOfEq hNbot).trans QuotientGroup.quotientBot).symm.trans eN
  exact ⟨X₀, n, hn, ⟨e₀⟩, by rw [hX₀map]; exact hsup, hinf, hdC⟩

private theorem exists_compl_of_third (h : Hyp G D) {d x v y : G}
    (hd : d ∈ D) (hv : v ∈ rootSet D d)
    (hdv : d * v ∈ rootSet D d) (hy : y ∈ D) (hyX : y ∈ rootGen D d x)
    (hsup : Subgroup.closure ({y, d, v} : Set G) ⊔ Qof D d x = rootGen D d x)
    (hyd : ¬ Commute y d) (hyv : ¬ Commute y v) (hydv : ¬ Commute y (d * v))
    (hpx : PSL2Pair D d x) :
    ∃ (X₀ : Subgroup (rootGen D d x)) (n : ℕ), 2 ≤ n ∧
      Nonempty (↥X₀ ≃* PSL2Model n) ∧
      Subgroup.map (rootGen D d x).subtype X₀ ⊔ Qof D d x = rootGen D d x ∧
      Subgroup.map (rootGen D d x).subtype X₀ ⊓ Qof D d x = ⊥ ∧
      d ∈ Subgroup.map (rootGen D d x).subtype X₀ := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hpx
  let X := rootGen D d x
  let Q : Subgroup X := CFSG.pCore 2 X
  let π : X →* X ⧸ Q := QuotientGroup.mk' Q
  let dX : X := ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩
  let vX : X := ⟨v, mem_rootGen_of_mem hv⟩
  let yX : X := ⟨y, hyX⟩
  let X₀ : Subgroup X := Subgroup.closure ({yX, dX, vX} : Set X)
  have hdX₀ : dX ∈ X₀ := Subgroup.subset_closure (by simp)
  have hvX₀ : vX ∈ X₀ := Subgroup.subset_closure (by simp)
  have hyX₀ : yX ∈ X₀ := Subgroup.subset_closure (by simp)
  have hX₀map : Subgroup.map X.subtype X₀ = Subgroup.closure ({y, d, v} : Set G) :=
    compl_third_map hd hv hyX
  have hX₀Q : X₀ ⊔ Q = ⊤ := compl_third_sup hd hv hyX hsup
  obtain ⟨N, hNnorm, hN2, hNcomap, ⟨eN⟩⟩ := compl_third_quot hX₀Q e
  letI : N.Normal := hNnorm
  let yX0 : ↥X₀ := ⟨yX, hyX₀⟩
  let dX0 : ↥X₀ := ⟨dX, hdX₀⟩
  let vX0 : ↥X₀ := ⟨vX, hvX₀⟩
  have hnotydX : ¬ Commute yX dX := fun hc => hyd (by
    have h2 := hc.map X.subtype
    simpa [yX, dX] using h2)
  have hnotyvX : ¬ Commute yX vX := fun hc => hyv (by
    have h2 := hc.map X.subtype
    simpa [yX, vX] using h2)
  have hnotydvX : ¬ Commute yX (dX * vX) := fun hc => hydv (by
    have h2 := hc.map X.subtype
    simpa [yX, dX, vX] using h2)
  have hgen : Subgroup.closure ({yX0, dX0, vX0} : Set ↥X₀) = ⊤ := by
    apply OddLocal.eq_top_of_le_map
    have hmeq : Subgroup.map X₀.subtype (Subgroup.closure ({yX0, dX0, vX0} : Set ↥X₀)) = X₀ := by
      rw [MonoidHom.map_closure]
      congr 1
      ext z
      simp [yX0, dX0, vX0]
    rw [hmeq]
  have hNbot : N = ⊥ :=
    N_eq_bot_of_third h (y := y) (d := d) (v := v) rfl rfl rfl rfl rfl rfl hd hv hdv hy
      hnotydX hnotyvX hnotydvX hgen N hN2 hn eN
  exact compl_third_finish hd hn hdX₀ N hNbot hNcomap eN hX₀map hsup

private theorem surjective_of_sup {X C Q : Subgroup G} {L : Type*} [Group L] (π : X →* L)
    (hπ : Function.Surjective π) (hCX : C ≤ X) (hQX : Q ≤ X)
    (hN : ∀ g ∈ X, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q)
    (hker : ∀ (q : G) (hq : q ∈ Q), π ⟨q, hQX hq⟩ = 1) (hsup : C ⊔ Q = X) :
    Function.Surjective (π.comp (Subgroup.inclusion hCX)) := by
  have hnorm : C ≤ Subgroup.normalizer (Q : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      exact hN c (hCX hc) q hq
    · intro hq
      have h := hN c⁻¹ (X.inv_mem (hCX hc)) (c * q * c⁻¹) hq
      have e : c⁻¹ * (c * q * c⁻¹) * c⁻¹⁻¹ = q := by group
      rwa [e] at h
  intro z
  obtain ⟨g, rfl⟩ := hπ z
  have hmem : (g : G) ∈ (↑(C ⊔ Q) : Set G) := by rw [hsup]; exact g.2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right C Q hnorm] at hmem
  obtain ⟨c, hc, q, hq, hcq⟩ := Set.mem_mul.mp hmem
  refine ⟨⟨c, hc⟩, ?_⟩
  have hq1 : π ⟨q, hQX hq⟩ = 1 := hker q hq
  have hgX : (⟨c, hCX hc⟩ : X) * ⟨q, hQX hq⟩ = g := Subtype.ext hcq
  have e : π ⟨c, hCX hc⟩ = π g := by
    rw [← hgX, map_mul, hq1, mul_one]
  show (π.comp (Subgroup.inclusion hCX)) ⟨c, hc⟩ = π g
  exact e

theorem exists_mulEquiv_PSL2Model_of_compl {d x : G} {C : Subgroup G} (hpx : PSL2Pair D d x)
    (hCX : C ≤ rootGen D d x) (hinf : C ⊓ Qof D d x = ⊥)
    (hsup : C ⊔ Qof D d x = rootGen D d x) :
    ∃ (n : ℕ) (_ : 2 ≤ n), Nonempty (↥C ≃* PSL2Model n) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hpx
  let X := rootGen D d x
  let Q : Subgroup X := CFSG.pCore 2 X
  let π : X →* X ⧸ Q := QuotientGroup.mk' Q
  have hQX : Qof D d x ≤ X := Qof_le_rootGen d x
  have hker : ∀ (q : G) (hq : q ∈ Qof D d x), π ⟨q, hQX hq⟩ = 1 := fun q hq =>
    (mk_eq_one_iff_mem_Qof (hQX hq)).mpr hq
  have hφsurj : Function.Surjective (π.comp (Subgroup.inclusion hCX)) :=
    surjective_of_sup π (QuotientGroup.mk'_surjective Q) hCX hQX
      (fun g hg q hq => conj_mem_Qof d x hg hq) hker hsup
  let φ : ↥C →* X ⧸ Q := π.comp (Subgroup.inclusion hCX)
  have hkerbot : φ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rw [MonoidHom.mem_ker] at hc
    have hcQ : (c : G) ∈ Qof D d x := (mk_eq_one_iff_mem_Qof (hCX c.2)).mp hc
    have hcinf : (c : G) ∈ C ⊓ Qof D d x := ⟨c.2, hcQ⟩
    rw [hinf] at hcinf
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hcinf))
  exact ⟨n, hn, ⟨((QuotientGroup.quotientMulEquivOfEq hkerbot).trans
    QuotientGroup.quotientBot).symm.trans
      ((QuotientGroup.quotientKerEquivOfSurjective φ hφsurj).trans e)⟩⟩

private theorem exists_good_sylow (h : Hyp G D) {C : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (e : ↥C ≃* PSL2Model n) {d : G} (hdC : d ∈ C) (hd : d ∈ D) :
    ∃ S : Subgroup G, S ≤ C ∧ (∀ s ∈ S, s ≠ 1 → s ∈ rootSet D d) ∧
      ∀ T : Subgroup G, S ≤ T → T ≤ C → IsPGroup 2 T → T = S := by
  obtain ⟨S₀, -, hroot⟩ := exists_sylow_rootSet h hn e hdC hd
  refine ⟨Subgroup.map C.subtype (S₀ : Subgroup C), Subgroup.map_subtype_le _, ?_, ?_⟩
  · intro s hs hs1
    obtain ⟨s₀, hs₀, rfl⟩ := Subgroup.mem_map.mp hs
    exact hroot s₀ hs₀ hs1
  · intro T hST hTC hT2
    exact map_sylow_is_maximal S₀ T hST hTC hT2

private theorem exists_lift_compl {d x c : G} {C : Subgroup G} (hCX : C ≤ rootGen D d x)
    (hsup : C ⊔ Qof D d x = rootGen D d x) (hcX : c ∈ rootGen D d x) (hc2 : c * c = 1) :
    ∃ c' : C, (c' : G) * c ∈ Qof D d x := by
  let X := rootGen D d x
  let Q : Subgroup X := CFSG.pCore 2 X
  let π : X →* X ⧸ Q := QuotientGroup.mk' Q
  have hQX : Qof D d x ≤ X := Qof_le_rootGen d x
  have hker : ∀ (q : G) (hq : q ∈ Qof D d x), π ⟨q, hQX hq⟩ = 1 := fun q hq =>
    (mk_eq_one_iff_mem_Qof (hQX hq)).mpr hq
  have hφsurj : Function.Surjective (π.comp (Subgroup.inclusion hCX)) :=
    surjective_of_sup π (QuotientGroup.mk'_surjective Q) hCX hQX
      (fun g hg q hq => conj_mem_Qof d x hg hq) hker hsup
  obtain ⟨c', hc'⟩ := hφsurj (π ⟨c, hcX⟩)
  refine ⟨c', ?_⟩
  have hEq : QuotientGroup.mk' Q (⟨(c' : G), hCX c'.2⟩ : X) =
      QuotientGroup.mk' Q (⟨c, hcX⟩ : X) := hc'
  exact mul_mem_Qof_of_mk_eq (d := d) (x := x) (hCX c'.2) hcX hc2 hEq

private theorem lift_sq_eq_one (h : Hyp G D) {d x c : G} {C : Subgroup G} (hc : c ∈ D)
    (hCX : C ≤ rootGen D d x) (hinf : C ⊓ Qof D d x = ⊥) (hcX : c ∈ rootGen D d x)
    {c' : C} (hc'Q : (c' : G) * c ∈ Qof D d x) : (c' : G) * (c' : G) = 1 := by
  let X := rootGen D d x
  let Q : Subgroup X := CFSG.pCore 2 X
  let π : X →* X ⧸ Q := QuotientGroup.mk' Q
  have hc2 : c * c = 1 := h.setup.oddT.mul_self_eq_one hc
  have hc'X : (c' : G) ∈ X := hCX c'.2
  have hker1 : π ⟨(c' : G), hc'X⟩ * π ⟨c, hcX⟩ = 1 := by
    have h := (mk_eq_one_iff_mem_Qof (X.mul_mem hc'X hcX)).mpr hc'Q
    rw [show (⟨(c' : G) * c, X.mul_mem hc'X hcX⟩ : X) =
      ⟨(c' : G), hc'X⟩ * ⟨c, hcX⟩ from Subtype.ext rfl, map_mul] at h
    exact h
  have hcX2 : (⟨c, hcX⟩ : X) * ⟨c, hcX⟩ = 1 := Subtype.ext (by simpa using hc2)
  have hcπ2 : π ⟨c, hcX⟩ * π ⟨c, hcX⟩ = 1 := by
    rw [← map_mul, hcX2, map_one]
  have hc'π : π ⟨(c' : G), hc'X⟩ = π ⟨c, hcX⟩ := by
    calc π ⟨(c' : G), hc'X⟩ = π ⟨(c' : G), hc'X⟩ * 1 := (mul_one _).symm
      _ = π ⟨(c' : G), hc'X⟩ * (π ⟨c, hcX⟩ * π ⟨c, hcX⟩) := by rw [hcπ2]
      _ = (π ⟨(c' : G), hc'X⟩ * π ⟨c, hcX⟩) * π ⟨c, hcX⟩ := by group
      _ = π ⟨c, hcX⟩ := by rw [hker1, one_mul]
  have hsq : π ⟨(c' : G) * (c' : G), X.mul_mem hc'X hc'X⟩ = 1 := by
    rw [show (⟨(c' : G) * (c' : G), X.mul_mem hc'X hc'X⟩ : X) =
      ⟨(c' : G), hc'X⟩ * ⟨(c' : G), hc'X⟩ from Subtype.ext rfl, map_mul, hc'π, hcπ2]
  have hQ' : (c' : G) * (c' : G) ∈ Qof D d x :=
    (mk_eq_one_iff_mem_Qof (X.mul_mem hc'X hc'X)).mp hsq
  have hmem : (c' : G) * (c' : G) ∈ C ⊓ Qof D d x := ⟨C.mul_mem c'.2 c'.2, hQ'⟩
  rw [hinf] at hmem
  exact Subgroup.mem_bot.mp hmem

private theorem exists_second_kind_z (h : Hyp G D) {d x c c' : G} (hd : d ∈ D) (hx : x ∈ D)
    (hdx : ¬ Commute d x) (hc : c ∈ D) (hcX : c ∈ rootGen D d x)
    (hdc : ¬ Commute d c) (hc'D : c' ∈ D) (hc'X : c' ∈ rootGen D d x)
    (hne : c' ≠ c) (hc'Q : c' * c ∈ Qof D d x) :
    ∃ z : G, z ∈ Qof D d x ∧ Commute z d ∧ z * c' * z⁻¹ = c := by
  have htri : IsTriangle D c' d c :=
    isTriangle_of_mul_mem_Qof h.setup.oddT hd hc hdc hc'D hcX hc'X hne hc'Q
  have h4 : orderOf (c' * c * d) = 4 :=
    orderOf_mul_mul_eq_four h.setup.oddT h.setup.normal hd hx hdx hc hcX hdc
      hc'D hc'X hne hc'Q
  have hno : ∀ y ∈ D, y ∈ Subgroup.closure ({c', d} : Set G) →
      IsTriangle D c' y c → ¬ IsThirdKind c' y c := by
    intro y hyD hycl htriY
    refine not_isThirdKind_of_mul_mem_Qof h.setup.oddT hc'D hc hyD ?_ hc'Q
    have hle : Subgroup.closure ({c', d} : Set G) ≤ rootGen D d x := by
      rw [Subgroup.closure_le]
      rintro z (rfl | rfl)
      · exact hc'X
      · exact mem_rootGen_of_mem (mem_rootSet_self hd)
    exact hle hycl
  have hSKS : SecondKindStructure c' d c :=
    secondKind_structure (D := D) h.setup.oddT h.setup.normal htri h4 hno
  obtain ⟨z, hzmem, hzx⟩ := hSKS.conj
  let Q₀ : Subgroup G := conjClosure (Subgroup.closure ({c', d} : Set G)) (c' * c)
  have hQ₀ : Q₀ ≤ Qof D d x :=
    conjClosure_le_of_normal (fun g hg q hq => conj_mem_Qof d x hg hq)
      (by
        rw [Subgroup.closure_le]
        rintro w (rfl | rfl)
        · exact hc'X
        · exact mem_rootGen_of_mem (mem_rootSet_self hd)) hc'Q
  have hdN : ∀ q ∈ Q₀, d * q * d⁻¹ ∈ Q₀ := fun q hq =>
    hSKS.normal d (Subgroup.subset_closure (by simp)) q hq
  have hzpowN : Subgroup.zpowers d ≤ Subgroup.normalizer (Q₀ : Set G) := by
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    refine Subgroup.zpow_mem (Subgroup.normalizer (Q₀ : Set G)) ?_ k
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · exact fun hq => hdN q hq
    · intro hq
      have h2 := hdN (d * q * d⁻¹) hq
      have hd2 := h.setup.oddT.mul_self_eq_one hd
      have hdi : d⁻¹ = d := h.setup.oddT.inv_eq hd
      have e : d * (d * q * d⁻¹) * d⁻¹ = q := by
        calc d * (d * q * d⁻¹) * d⁻¹ = (d * d) * q * (d⁻¹ * d⁻¹) := by group
          _ = q := by rw [hd2, one_mul, hdi, hd2, mul_one]
      rwa [e] at h2
  have hzQ : z ∈ Qof D d x :=
    hQ₀ ((Subgroup.le_normalizer_iff_commutator_le_left (H := Subgroup.zpowers d)
      (K := Q₀)).mp hzpowN hzmem)
  have hzd : Commute z d := Subgroup.mem_centralizer_singleton_iff.mp (hSKS.le_centralizer hzmem)
  exact ⟨z, hzQ, hzd, hzx⟩

theorem exists_conj_mem_of_compl (h : Hyp G D) {d x c : G} (hd : d ∈ D) (hx : x ∈ D)
    (hdx : ¬ Commute d x) (hpx : PSL2Pair D d x) {C : Subgroup G}
    (hCX : C ≤ rootGen D d x) (hinf : C ⊓ Qof D d x = ⊥)
    (hsup : C ⊔ Qof D d x = rootGen D d x) (haC : ∃ a ∈ C, a ∈ D)
    (hc : c ∈ D) (hcX : c ∈ rootGen D d x) (hdc : ¬ Commute d c) :
    ∃ z ∈ Qof D d x, Commute z d ∧ c ∈ conjSubgroup z C := by
  obtain ⟨a, haC, haD⟩ := haC
  obtain ⟨n, hn, ⟨eC⟩⟩ := exists_mulEquiv_PSL2Model_of_compl hpx hCX hinf hsup
  have hc2 : c * c = 1 := h.setup.oddT.mul_self_eq_one hc
  obtain ⟨c', hc'Q⟩ := exists_lift_compl hCX hsup hcX hc2
  have hc'X : (c' : G) ∈ rootGen D d x := hCX c'.2
  have hc'2 : (c' : G) * (c' : G) = 1 := lift_sq_eq_one h hc hCX hinf hcX hc'Q
  have hc'1 : (c' : G) ≠ 1 := by
    intro h1
    have hcQ : c ∈ Qof D d x := by simpa [h1] using hc'Q
    have hcomm := commute_of_mem_D_of_mem_Qof h.setup.oddT hx hc hcQ d
      (mem_rootGen_of_mem (mem_rootSet_self hd))
    exact hdc hcomm.symm
  have hc'D : (c' : G) ∈ D :=
    involution_mem_D_of_psl2 h hn eC haC haD c'.2 hc'2 hc'1
  by_cases hcc' : (c' : G) = c
  · refine ⟨1, (Qof D d x).one_mem, Commute.one_left d, ?_⟩
    rw [conjSubgroup_one, ← hcc']
    exact c'.2
  · obtain ⟨z, hzQ, hzd, hzc⟩ :=
      exists_second_kind_z h hd hx hdx hc hcX hdc hc'D hc'X hcc' hc'Q
    refine ⟨z, hzQ, hzd, ?_⟩
    rw [mem_conjSubgroup]
    have hcz : z⁻¹ * c * z = c' := by
      calc z⁻¹ * c * z = z⁻¹ * (z * c' * z⁻¹) * z := by rw [← hzc]
        _ = c' := by group
    rw [hcz]
    exact c'.2

private theorem conj_compl_basic' {d x z : G} {C : Subgroup G}
    (hCX : C ≤ rootGen D d x) (hinf : C ⊓ Qof D d x = ⊥)
    (hsup : C ⊔ Qof D d x = rootGen D d x) (hzQ : z ∈ Qof D d x) :
    conjSubgroup z C ≤ rootGen D d x ∧ conjSubgroup z C ⊓ Qof D d x = ⊥ ∧
      conjSubgroup z C ⊔ Qof D d x = rootGen D d x := by
  let X := rootGen D d x
  have hzX : z ∈ X := Qof_le_rootGen d x hzQ
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    change g ∈ conjSubgroup z C at hg
    rw [mem_conjSubgroup] at hg
    have h := X.mul_mem (X.mul_mem hzX (hCX hg)) (X.inv_mem hzX)
    have e : z * (z⁻¹ * g * z) * z⁻¹ = g := by group
    rwa [e] at h
  · rw [eq_bot_iff]
    rintro g ⟨hgc, hgq⟩
    change g ∈ conjSubgroup z C at hgc
    rw [mem_conjSubgroup] at hgc
    have hgq' : z⁻¹ * g * z ∈ Qof D d x := by
      have := conj_mem_Qof d x (X.inv_mem hzX) hgq
      simpa using this
    have hmem : z⁻¹ * g * z ∈ C ⊓ Qof D d x := ⟨hgc, hgq'⟩
    rw [hinf] at hmem
    have h1 : z⁻¹ * g * z = 1 := Subgroup.mem_bot.mp hmem
    have hg1 : g = 1 := by
      calc g = z * (z⁻¹ * g * z) * z⁻¹ := by group
        _ = 1 := by rw [h1]; group
    exact Subgroup.mem_bot.mpr hg1
  · have hQz : conjSubgroup z (Qof D d x) = Qof D d x := by
      ext q
      rw [mem_conjSubgroup]
      constructor
      · intro h
        have h2 := conj_mem_Qof d x hzX h
        have e : z * (z⁻¹ * q * z) * z⁻¹ = q := by group
        rwa [e] at h2
      · intro h
        simpa using conj_mem_Qof d x (X.inv_mem hzX) h
    have hXz : conjSubgroup z X = X := by
      ext q
      rw [mem_conjSubgroup]
      constructor
      · intro h
        have h2 := X.mul_mem (X.mul_mem hzX h) (X.inv_mem hzX)
        have e : z * (z⁻¹ * q * z) * z⁻¹ = q := by group
        rwa [e] at h2
      · intro h
        exact X.mul_mem (X.mul_mem (X.inv_mem hzX) h) hzX
    have h1 : conjSubgroup z C ⊔ Qof D d x = conjSubgroup z C ⊔ conjSubgroup z (Qof D d x) := by
      rw [hQz]
    have h2 : conjSubgroup z C ⊔ conjSubgroup z (Qof D d x) =
        conjSubgroup z (C ⊔ Qof D d x) := by
      simp only [conjSubgroup]
      exact (Subgroup.map_sup C (Qof D d x) (MulAut.conj z).toMonoidHom).symm
    rw [h1, h2, hsup]
    exact hXz

private theorem conj_sylow_basic (h : Hyp G D) {d x z : G} {C S Cz : Subgroup G}
    (hCz : Cz = conjSubgroup z C) (hzQ : z ∈ Qof D d x) (hzd : Commute z d)
    (hSC : S ≤ C) (hSroot : ∀ s ∈ S, s ≠ 1 → s ∈ rootSet D d)
    (hSsylow : ∀ T : Subgroup G, S ≤ T → T ≤ C → IsPGroup 2 T → T = S) :
    conjSubgroup z S ≤ Cz ∧
      (∀ s ∈ conjSubgroup z S, s ≠ 1 → s ∈ rootSet D d) ∧
      ∀ T : Subgroup G, conjSubgroup z S ≤ T → T ≤ Cz → IsPGroup 2 T → T = conjSubgroup z S := by
  let X := rootGen D d x
  have hzX : z ∈ X := Qof_le_rootGen d x hzQ
  refine ⟨?_, ?_, ?_⟩
  · rw [hCz]
    exact Subgroup.map_mono hSC
  · intro s hs hs1
    change s ∈ conjSubgroup z S at hs
    rw [mem_conjSubgroup] at hs
    have hzd' : z * d * z⁻¹ = d := by
      rw [hzd.eq]
      group
    have hs1' : z⁻¹ * s * z ≠ 1 := by
      intro h1
      apply hs1
      calc s = z * (z⁻¹ * s * z) * z⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have hthis := conj_mem_rootSet_of_conj_eq h.setup (z := z) (d := d) hzd'
      (hSroot _ hs hs1')
    have h2 : z * (z⁻¹ * s * z) * z⁻¹ = s := by group
    rwa [h2] at hthis
  · intro T hST hTC hT2
    have hT'C : conjSubgroup z⁻¹ T ≤ C := by
      intro t ht
      rw [mem_conjSubgroup] at ht
      have ht' : z * t * z⁻¹ ∈ T := by simpa using ht
      have h1 : z * t * z⁻¹ ∈ Cz := hTC ht'
      rw [hCz] at h1
      change z * t * z⁻¹ ∈ conjSubgroup z C at h1
      rw [mem_conjSubgroup] at h1
      have h2 : z⁻¹ * (z * t * z⁻¹) * z = t := by group
      rwa [h2] at h1
    have hST' : S ≤ conjSubgroup z⁻¹ T := by
      intro s hs
      rw [mem_conjSubgroup]
      have h1 : z * s * z⁻¹ ∈ conjSubgroup z S :=
        Subgroup.mem_map_of_mem (MulAut.conj z).toMonoidHom hs
      simpa using hST h1
    have hT'2 : IsPGroup 2 (conjSubgroup z⁻¹ T) := by
      rw [show conjSubgroup z⁻¹ T = Subgroup.map (MulAut.conj z⁻¹).toMonoidHom T from rfl]
      exact hT2.map (MulAut.conj z⁻¹).toMonoidHom
    have hEq : conjSubgroup z⁻¹ T = S := hSsylow _ hST' hT'C hT'2
    calc T = conjSubgroup z (conjSubgroup z⁻¹ T) := by
          rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
      _ = conjSubgroup z S := by rw [hEq]

theorem IsRootCompl.conj (h : Hyp G D) {d x : G} {C S : Subgroup G}
    (hC : IsRootCompl D d x C S) {z : G}
    (hz : z ∈ Qof D d x) (hzd : Commute z d) :
    IsRootCompl D d x (conjSubgroup z C) (conjSubgroup z S) := by
  obtain ⟨h1, h2, h3⟩ := conj_compl_basic' hC.le hC.inf hC.sup hz
  obtain ⟨hSzCz, hSzroot, hSzSylow⟩ :=
    conj_sylow_basic h rfl hz hzd hC.S_le hC.S_root hC.S_sylow
  exact IsRootCompl.mk h1 h2 h3 hSzCz hSzroot hSzSylow

private theorem exists_goodCompl_aux
    (h : Hyp G D) {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x)
    (hpx : PSL2Pair D d x) : ∃ C S : Subgroup G, GoodCompl D d x C S := by
  obtain ⟨v, y, hv, hdv, hy, hyX, hsup, hyd, hyv, hydv⟩ :=
    exists_third_involution h hd hx hdx hpx
  obtain ⟨X₀, n, hn, ⟨e₀⟩, hsupX, hinfX, hdX₀⟩ :=
    exists_compl_of_third h hd hv hdv hy hyX hsup hyd hyv hydv hpx
  let X := rootGen D d x
  let C : Subgroup G := Subgroup.map X.subtype X₀
  have hCX : C ≤ X := Subgroup.map_subtype_le X₀
  have hinfC : C ⊓ Qof D d x = ⊥ := hinfX
  have hsupC : C ⊔ Qof D d x = X := hsupX
  have hdC : d ∈ C := hdX₀
  obtain ⟨n', hn', ⟨eC⟩⟩ := exists_mulEquiv_PSL2Model_of_compl hpx hCX hinfC hsupC
  obtain ⟨S, hSC, hSroot, hSsylow⟩ := exists_good_sylow h hn' eC hdC hd
  obtain ⟨z, hzQ, hzd, hxz⟩ :=
    exists_conj_mem_of_compl h hd hx hdx hpx hCX hinfC hsupC ⟨d, hdC, hd⟩ hx
      (mem_rootGen_left d x) hdx
  exact ⟨conjSubgroup z C, conjSubgroup z S,
    GoodCompl.mk (IsRootCompl.conj h (IsRootCompl.mk hCX hinfC hsupC hSC hSroot hSsylow)
      hzQ hzd) hxz⟩

theorem exists_goodCompl
    {G : Type} [Group G] [Finite G] {D : Set G} (h : Hyp G D) {d x : G} (hd : d ∈ D)
    (hx : x ∈ D) (hdx : ¬ Commute d x) (hpx : PSL2Pair D d x) :
    ∃ C S, GoodCompl D d x C S :=
  exists_goodCompl_aux h hd hx hdx hpx

theorem IsRootCompl.isPGroup (h : Hyp G D) {C S : Subgroup G} {d x : G}
    (hC : IsRootCompl D d x C S) : IsPGroup 2 S := by
  refine (IsPGroup.iff_orderOf (p := 2) (G := ↥S)).mpr ?_
  intro s
  by_cases h1 : s = 1
  · exact ⟨0, by simp [h1]⟩
  · have h1G : (s : G) ≠ 1 := fun h => h1 (Subtype.ext h)
    have hsD : (s : G) ∈ D := (hC.S_root s s.2 h1G).1
    have h2 : (s : G) * (s : G) = 1 := h.setup.oddT.mul_self_eq_one hsD
    have h2' : s * s = 1 := Subtype.ext h2
    have hdvd : orderOf s ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2')
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) h1
    · exact ⟨1, h⟩

private theorem exists_sylow_of_goodCompl (h : Hyp G D) {C S : Subgroup G} {d x s : G} {n : ℕ}
    (hn : 2 ≤ n) (eC : ↥C ≃* PSL2Model n)
    (hC : GoodCompl D d x C S) (hsS : s ∈ S) (hs1 : s ≠ 1) :
    ∃ Sd : Sylow 2 ↥C, (⟨s, hC.S_le hsS⟩ : ↥C) ∈ Sd ∧
      (∀ t ∈ Sd, (t : G) ≠ 1 → (t : G) ∈ rootSet D d) ∧
      Subgroup.map C.subtype (Sd : Subgroup ↥C) = S := by
  have hs1' : s ≠ 1 := hs1
  have hsC : s ∈ C := hC.S_le hsS
  have hsE : s ∈ rootSet D d := hC.S_root _ hsS hs1'
  have hsD : s ∈ D := hsE.1
  obtain ⟨Sd, hsdSd, hSdroot⟩ := exists_sylow_rootSet h hn eC hsC hsD
  have hSdroot' : ∀ t ∈ Sd, (t : G) ≠ 1 → (t : G) ∈ rootSet D d := by
    intro t ht ht1
    rw [← rootSet_eq_of_mem hsE]
    exact hSdroot t ht ht1
  have hs1C : (⟨s, hsC⟩ : ↥C) ≠ 1 := fun h1 =>
    hs1 (by simpa using congrArg (fun z : ↥C => (z : G)) h1)
  have hS2 : IsPGroup 2 S := hC.toIsRootCompl.isPGroup h
  have hSC2 : IsPGroup 2 (S.subgroupOf C) :=
    hS2.comap_of_injective C.subtype C.subtype_injective
  obtain ⟨P, hSP⟩ := IsPGroup.exists_le_sylow hSC2
  have hsdP : (⟨s, hsC⟩ : ↥C) ∈ P :=
    hSP (show (⟨s, hsC⟩ : ↥C) ∈ S.subgroupOf C from by
      rw [Subgroup.mem_subgroupOf]; exact hsS)
  have hPsd : P = Sd := psl2_sylow_eq_of_mem eC hn hs1C hsdP hsdSd
  have hSmap : Subgroup.map C.subtype (Sd : Subgroup ↥C) = S := by
    have hle : S ≤ Subgroup.map C.subtype (Sd : Subgroup ↥C) := by
      rw [← hPsd]
      have h1 : Subgroup.map C.subtype (S.subgroupOf C) = S := by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hC.S_le]
      rw [← h1]
      exact Subgroup.map_mono hSP
    exact hC.S_sylow _ hle (Subgroup.map_subtype_le _) ((Sd.isPGroup').map C.subtype)
  exact ⟨Sd, hsdSd, hSdroot', hSmap⟩

private theorem exists_nonidentity_sylow (h : Hyp G D)
    {d x : G} (hx : x ∈ D) {C S : Subgroup G}
    (hC : GoodCompl D d x C S) {n : ℕ} (hn : 2 ≤ n) (eC : ↥C ≃* PSL2Model n) :
    ∃ (s : ↥S) (Sd : Sylow 2 ↥C), (s : G) ≠ 1 ∧
      (⟨s, hC.S_le s.2⟩ : ↥C) ∈ Sd ∧
      (∀ t ∈ Sd, ((t : ↥C) : G) ≠ 1 → ((t : ↥C) : G) ∈ rootSet D d) ∧
      Subgroup.map C.subtype (Sd : Subgroup ↥C) = S := by
  have hSne : S ≠ ⊥ := by
    intro hbot
    have hEq : Subgroup.zpowers x = S := by
      refine hC.S_sylow (Subgroup.zpowers x) ?_ ?_ ?_
      · rw [hbot]; exact bot_le
      · intro g hg
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
        exact Subgroup.zpow_mem C hC.x_mem k
      · exact isPGroup_two_zpowers_of_mul_self_eq_one (h.setup.oddT.mul_self_eq_one hx)
    have hxS : x ∈ S := by rw [← hEq]; exact Subgroup.mem_zpowers x
    exact h.setup.oddT.ne_one hx (Subgroup.mem_bot.mp (hbot ▸ hxS))
  haveI : Nontrivial ↥S := (Subgroup.nontrivial_iff_ne_bot S).mpr hSne
  obtain ⟨s, hs1⟩ := exists_ne (1 : ↥S)
  have hsS : (s : G) ∈ S := s.2
  have hs1' : (s : G) ≠ 1 := fun h1 => hs1 (Subtype.ext h1)
  obtain ⟨Sd, hsdSd, hSdroot, hSmap⟩ :=
    exists_sylow_of_goodCompl h hn eC hC hsS hs1'
  exact ⟨s, Sd, hs1', hsdSd, hSdroot, hSmap⟩

private theorem exists_conj_sylow (h : Hyp G D)
    {d x : G} (hx : x ∈ D) (hpx : PSL2Pair D d x)
    {C S : Subgroup G} (hC : GoodCompl D d x C S) :
    ∃ m : C, (∀ s ∈ S, s ≠ 1 → (m : G) * s * (m : G)⁻¹ ∈ rootSet D x) ∧
      rootSet D x = (fun z => (m : G) * z * (m : G)⁻¹) '' rootSet D d := by
  obtain ⟨n, hn, ⟨eC⟩⟩ := exists_mulEquiv_PSL2Model_of_compl hpx hC.le hC.inf hC.sup
  obtain ⟨s, Sd, hs1', hsdSd, hSdroot, hSmap⟩ := exists_nonidentity_sylow h hx hC hn eC
  have hsS : (s : G) ∈ S := s.2
  have hsC : (s : G) ∈ C := hC.S_le hsS
  have hsE : (s : G) ∈ rootSet D d := hC.S_root _ hsS hs1'
  obtain ⟨Sx, hxSx, hSxroot⟩ := exists_sylow_rootSet h hn eC hC.x_mem hx
  obtain ⟨m, hm⟩ := exists_conjSubgroup_eq_of_sylow Sd Sx
  let t : ↥C := ⟨s, hsC⟩
  have htSd : t ∈ Sd := hsdSd
  have ht1C : (t : C) ≠ 1 := fun h1 => hs1' (by simpa [t] using congrArg (fun z : C => (z : G)) h1)
  have ht1G : (t : G) ≠ 1 := hs1'
  have htE : (t : G) ∈ rootSet D d := hsE
  have hmtSx : (m : C) * t * (m : C)⁻¹ ∈ Sx := by
    change (m : C) * t * (m : C)⁻¹ ∈ (Sx : Subgroup ↥C)
    rw [← hm]
    exact Subgroup.mem_map_of_mem (MulAut.conj (m : C)).toMonoidHom htSd
  have hmt1 : ((m : C) * t * (m : C)⁻¹ : C) ≠ 1 := by
    intro h1
    apply ht1C
    have h2 := congrArg (fun z : C => (m : C)⁻¹ * z * (m : C)) h1
    have hR : (m : C)⁻¹ * (1 : C) * (m : C) = 1 := by group
    rw [hR] at h2
    have e : (m : C)⁻¹ * ((m : C) * t * (m : C)⁻¹) * (m : C) = t := by group
    rwa [e] at h2
  have hmt1G : (((m : C) * t * (m : C)⁻¹ : C) : G) ≠ 1 := fun h1 =>
    hmt1 (Subtype.ext h1)
  have hmtE : ((m : C) : G) * ((t : C) : G) * ((m : C) : G)⁻¹ ∈ rootSet D x := by
    have h := hSxroot _ hmtSx hmt1G
    simpa using h
  have hEx : rootSet D x =
      (fun z => ((m : C) : G) * z * ((m : C) : G)⁻¹) '' rootSet D d := by
    have h1 : rootSet D (((m : C) : G) * ((t : C) : G) * ((m : C) : G)⁻¹) =
        (fun z => ((m : C) : G) * z * ((m : C) : G)⁻¹) '' rootSet D ((t : C) : G) :=
      rootSet_conj h.setup.isClass ((m : C) : G) ((t : C) : G)
    rw [← rootSet_eq_of_mem hmtE, h1, rootSet_eq_of_mem htE]
  refine ⟨m, ?_, hEx⟩
  intro s' hs' hs1'
  rw [← hSmap] at hs'
  obtain ⟨t', ht'Sd, rfl⟩ := Subgroup.mem_map.mp hs'
  have ht'1 : (t' : C) ≠ 1 := by
    intro h1
    exact hs1' (by simpa using congrArg (fun z : C => (z : G)) h1)
  have hmt'Sx : (m : C) * t' * (m : C)⁻¹ ∈ Sx := by
    change (m : C) * t' * (m : C)⁻¹ ∈ (Sx : Subgroup ↥C)
    rw [← hm]
    exact Subgroup.mem_map_of_mem (MulAut.conj (m : C)).toMonoidHom ht'Sd
  have hmt'1 : (((m : C) * t' * (m : C)⁻¹ : C) : G) ≠ 1 := by
    intro h1
    apply ht'1
    have h2 := congrArg (fun z : C => (m : C)⁻¹ * z * (m : C))
      (Subtype.ext h1 : (m : C) * t' * (m : C)⁻¹ = 1)
    have hR : (m : C)⁻¹ * (1 : C) * (m : C) = 1 := by group
    rw [hR] at h2
    have e : (m : C)⁻¹ * ((m : C) * t' * (m : C)⁻¹) * (m : C) = t' := by group
    rwa [e] at h2
  have h := hSxroot _ hmt'Sx hmt'1
  simpa using h

theorem rootSet_subset_rootGen
    (h : Hyp G D) {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x)
    (hpx : PSL2Pair D d x) : rootSet D x ⊆ rootGen D d x := by
  obtain ⟨C, S, hC⟩ := exists_goodCompl h hd hx hdx hpx
  obtain ⟨m, -, hEx⟩ := exists_conj_sylow h hx hpx hC
  intro e he
  rw [hEx] at he
  obtain ⟨e₀, he₀, rfl⟩ := he
  exact (rootGen D d x).mul_mem ((rootGen D d x).mul_mem (hC.le m.2)
    (rootGroup_le_rootGen d x (rootSet_subset_rootGroup D d he₀)))
    ((rootGen D d x).inv_mem (hC.le m.2))

theorem exists_conj_rootGroup
    (h : Hyp G D) {d x : G} (hx : x ∈ D) (hpx : PSL2Pair D d x)
    {C S : Subgroup G} (hC : GoodCompl D d x C S) :
    ∃ n₀ ∈ C, (∀ s ∈ S, s ≠ 1 → n₀ * s * n₀⁻¹ ∈ rootSet D x) ∧
      conjSubgroup n₀ (rootGroup D d) = rootGroup D x ∧
      conjSubgroup n₀ (Wof D d x) = rootGroup D x ⊓ Qof D d x := by
  obtain ⟨m, hmS, hEx⟩ := exists_conj_sylow h hx hpx hC
  have hroot : Subgroup.map (MulAut.conj (m : G)).toMonoidHom (rootGroup D d) = rootGroup D x := by
    rw [rootGroup, rootGroup]
    rw [hEx]
    rw [MonoidHom.map_closure]
    rfl
  have hQm : Subgroup.map (MulAut.conj (m : G)).toMonoidHom (Qof D d x) = Qof D d x := by
    apply le_antisymm
    · rintro q ⟨p, hp, rfl⟩
      simpa [MulAut.conj_apply] using conj_mem_Qof d x (hC.le m.2) hp
    · intro q hq
      refine ⟨(m : G)⁻¹ * q * (m : G), ?_, ?_⟩
      · simpa using conj_mem_Qof d x ((rootGen D d x).inv_mem (hC.le m.2)) hq
      · change (m : G) * ((m : G)⁻¹ * q * (m : G)) * (m : G)⁻¹ = q
        group
  refine ⟨(m : G), m.2, hmS, hroot, ?_⟩
  change Subgroup.map (MulAut.conj (m : G)).toMonoidHom (Wof D d x) =
    rootGroup D x ⊓ Qof D d x
  rw [Wof, Subgroup.map_inf _ _ _ (MulAut.conj (m : G)).injective, hroot, hQm]

theorem rootGen_comm
    (h : Hyp G D) {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x)
    (hpx : PSL2Pair D d x) (hpx' : PSL2Pair D x d) :
    rootGen D d x = rootGen D x d := by
  apply le_antisymm
  · rw [rootGen]
    refine (Subgroup.closure_le (rootGen D x d)).mpr ?_
    rintro z (rfl | hz)
    · exact mem_rootGen_of_mem (mem_rootSet_self hx)
    · exact rootSet_subset_rootGen h hx hd (fun h => hdx h.symm) hpx' hz
  · rw [rootGen]
    refine (Subgroup.closure_le (rootGen D d x)).mpr ?_
    rintro z (rfl | hz)
    · exact mem_rootGen_of_mem (mem_rootSet_self hd)
    · exact rootSet_subset_rootGen h hd hx hdx hpx hz

private theorem mem_Wof_mul_sylow_of_sylow
    (h : Hyp G D) {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x)
    {C S : Subgroup G} (hC : GoodCompl D d x C S) {n : ℕ} (hn : 2 ≤ n)
    (eL : (rootGen D d x ⧸ CFSG.pCore 2 (rootGen D d x)) ≃* PSL2Model n)
    (Sd : Sylow 2 ↥C)
    (hSdroot : ∀ t ∈ Sd, ((t : ↥C) : G) ≠ 1 → ((t : ↥C) : G) ∈ rootSet D d)
    (hSmap : Subgroup.map C.subtype (Sd : Subgroup ↥C) = S)
    (mapSd : Sylow 2 (rootGen D d x ⧸ CFSG.pCore 2 (rootGen D d x)))
    (hmapSd : (mapSd : Subgroup (rootGen D d x ⧸ CFSG.pCore 2 (rootGen D d x))) =
      Subgroup.map ((QuotientGroup.mk' (CFSG.pCore 2 (rootGen D d x))).comp
        (Subgroup.inclusion hC.le)) (Sd : Subgroup ↥C))
    (hdbar_ne : QuotientGroup.mk' (CFSG.pCore 2 (rootGen D d x))
      ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩ ≠ 1)
    (hdbar_mem : QuotientGroup.mk' (CFSG.pCore 2 (rootGen D d x))
      ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩ ∈ mapSd) :
    rootSet D d ⊆ (Wof D d x : Set G) * (S : Set G) := by
  let X := rootGen D d x
  let Q : Subgroup X := CFSG.pCore 2 X
  let π : X →* X ⧸ Q := QuotientGroup.mk' Q
  let φ : ↥C →* X ⧸ Q := π.comp (Subgroup.inclusion hC.le)
  intro e he
  have heX : e ∈ X := mem_rootGen_of_mem he
  have hebar_comm : Commute (π ⟨e, heX⟩) (π ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩) := by
    have hcomm : Commute e d := (he.2 d hd).mpr (Commute.refl d)
    have hcX : Commute (⟨e, heX⟩ : X) ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩ :=
      Subtype.ext (by simpa using hcomm.eq)
    exact hcX.map π
  have hebar1 : π ⟨e, heX⟩ ≠ 1 :=
    (mk_eq_one_iff_mem_Qof heX).not.mpr (not_mem_Qof_of_mem_rootSet h.setup.oddT hx hdx he)
  have hebarS : π ⟨e, heX⟩ ∈ mapSd :=
    psl2_mem_sylow_of_commute eL hn hdbar_ne hdbar_mem hebar_comm
  change π ⟨e, heX⟩ ∈ (mapSd : Subgroup (X ⧸ Q)) at hebarS
  rw [show (mapSd : Subgroup (X ⧸ Q)) = Subgroup.map φ (Sd : Subgroup ↥C) from hmapSd] at hebarS
  obtain ⟨t, htSd, htφ⟩ := Subgroup.mem_map.mp hebarS
  have ht1 : (t : ↥C) ≠ 1 := by
    intro h1
    exact hebar1 (by rw [← htφ, h1, map_one])
  have htE : ((t : ↥C) : G) ∈ rootSet D d := hSdroot _ htSd (fun h1 => ht1 (Subtype.ext h1))
  have hetQ : e * ((t : ↥C) : G) ∈ Qof D d x := by
    have h1 : π ⟨e * ((t : ↥C) : G), X.mul_mem heX (hC.le (t : ↥C).2)⟩ = 1 := by
      have h2 : (⟨e * ((t : ↥C) : G), X.mul_mem heX (hC.le (t : ↥C).2)⟩ : X) =
          ⟨e, heX⟩ * ⟨((t : ↥C) : G), hC.le (t : ↥C).2⟩ := Subtype.ext rfl
      have htφ' : π ⟨((t : ↥C) : G), hC.le (t : ↥C).2⟩ = π ⟨e, heX⟩ := htφ
      rw [h2, map_mul, htφ']
      rw [← map_mul, show (⟨e, heX⟩ : X) * ⟨e, heX⟩ = 1 from
        Subtype.ext (by simpa using h.setup.oddT.mul_self_eq_one he.1), map_one]
    exact (mk_eq_one_iff_mem_Qof (X.mul_mem heX (hC.le (t : ↥C).2))).mp h1
  have hetW : e * ((t : ↥C) : G) ∈ Wof D d x :=
    ⟨Subgroup.mul_mem (rootGroup D d) (rootSet_subset_rootGroup D d he)
      (rootSet_subset_rootGroup D d htE), hetQ⟩
  have htS : ((t : ↥C) : G) ∈ S := by
    rw [← hSmap]
    exact Subgroup.mem_map_of_mem C.subtype htSd
  have heq : e = (e * ((t : ↥C) : G)) * (((t : ↥C) : G))⁻¹ := by group
  rw [heq]
  exact ⟨e * ((t : ↥C) : G), hetW, (((t : ↥C) : G))⁻¹, S.inv_mem htS, rfl⟩

theorem rootSet_subset_Wof_mul_sylow
    (h : Hyp G D) {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x)
    (hpx : PSL2Pair D d x) {C S : Subgroup G} (hC : GoodCompl D d x C S) :
    rootSet D d ⊆ (Wof D d x : Set G) * (S : Set G) := by
  obtain ⟨n, hn, ⟨eC⟩⟩ := exists_mulEquiv_PSL2Model_of_compl hpx hC.le hC.inf hC.sup
  let X := rootGen D d x
  let Q : Subgroup X := CFSG.pCore 2 X
  let π : X →* X ⧸ Q := QuotientGroup.mk' Q
  let φ : ↥C →* X ⧸ Q := π.comp (Subgroup.inclusion hC.le)
  have hQX : Qof D d x ≤ X := Qof_le_rootGen d x
  have hker : ∀ (q : G) (hq : q ∈ Qof D d x), π ⟨q, hQX hq⟩ = 1 := fun q hq =>
    (mk_eq_one_iff_mem_Qof (hQX hq)).mpr hq
  have hφsurj : Function.Surjective φ :=
    surjective_of_sup π (QuotientGroup.mk'_surjective Q) hC.le hQX
      (fun g hg q hq => conj_mem_Qof d x hg hq) hker hC.sup
  have hφker : φ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rw [MonoidHom.mem_ker] at hc
    have hcQ : (c : G) ∈ Qof D d x := (mk_eq_one_iff_mem_Qof (hC.le c.2)).mp hc
    have hcinf : (c : G) ∈ C ⊓ Qof D d x := ⟨c.2, hcQ⟩
    rw [hC.inf] at hcinf
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hcinf))
  have hφinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hφker
  let eCL : ↥C ≃* X ⧸ Q := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  let eL : X ⧸ Q ≃* PSL2Model n := eCL.symm.trans eC
  obtain ⟨s, Sd, hs1', hsdSd, hSdroot, hSmap⟩ := exists_nonidentity_sylow h hx hC hn eC
  have hsS : (s : G) ∈ S := s.2
  have hdbar_ne : π ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩ ≠ 1 :=
    (mk_eq_one_iff_mem_Qof _).not.mpr (not_mem_Qof_self h.setup.oddT hd hx hdx)
  have hdbar2 : π ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩ *
      π ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩ = 1 := by
    rw [← map_mul, show (⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩ : X) *
      ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩ = 1 from
      Subtype.ext (by simpa using h.setup.oddT.mul_self_eq_one hd), map_one]
  obtain ⟨Sbar, hdbarSbar⟩ := IsPGroup.exists_le_sylow
    (isPGroup_two_zpowers_of_mul_self_eq_one hdbar2)
  have hdbarSbar' : π ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩ ∈ Sbar :=
    hdbarSbar (Subgroup.mem_zpowers _)
  have hsC : (s : G) ∈ C := hC.S_le hsS
  have hsE : (s : G) ∈ rootSet D d := hC.S_root _ hsS hs1'
  have hs1C : (⟨s, hsC⟩ : ↥C) ≠ 1 := fun h1 =>
    hs1' (by simpa using congrArg (fun z : ↥C => (z : G)) h1)
  let mapSd : Sylow 2 (X ⧸ Q) := Sylow.mapSurjective (f := eCL.toMonoidHom) eCL.surjective Sd
  have hmapSd : (mapSd : Subgroup (X ⧸ Q)) = Subgroup.map φ (Sd : Subgroup ↥C) := rfl
  have hφs_mem : φ ⟨s, hsC⟩ ∈ mapSd := by
    change φ ⟨s, hsC⟩ ∈ (mapSd : Subgroup (X ⧸ Q))
    rw [hmapSd]
    exact Subgroup.mem_map_of_mem φ hsdSd
  have hφs_comm : Commute (φ ⟨s, hsC⟩) (π ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩) := by
    have hcomm : Commute (s : G) d :=
      (commute_of_mem_rootSet hd (mem_rootSet_self hd) hsE).symm
    have hcX : Commute (⟨s, hC.le hsC⟩ : X) ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩ :=
      Subtype.ext (by simpa using hcomm.eq)
    exact hcX.map π
  have hφs1 : φ ⟨s, hsC⟩ ≠ 1 := by
    intro h1
    have hmem : (⟨s, hsC⟩ : ↥C) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]; exact h1
    rw [hφker] at hmem
    exact hs1C (Subgroup.mem_bot.mp hmem)
  have hmapSd_eq : mapSd = Sbar :=
    psl2_sylow_eq_of_mem eL hn hφs1 hφs_mem
      (psl2_mem_sylow_of_commute eL hn hdbar_ne hdbarSbar' hφs_comm)
  have hdbar_mem : π ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩ ∈ mapSd := by
    change π ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩ ∈ (mapSd : Subgroup (X ⧸ Q))
    rw [show (mapSd : Subgroup (X ⧸ Q)) = Sbar from congrArg (fun P : Sylow 2 (X ⧸ Q) =>
      (P : Subgroup (X ⧸ Q))) hmapSd_eq]
    exact hdbarSbar'
  exact mem_Wof_mul_sylow_of_sylow h hd hx hdx hC hn eL Sd hSdroot hSmap mapSd hmapSd
    hdbar_ne hdbar_mem

end CFSG.Timmesfeld.Bridge.OddRoot
