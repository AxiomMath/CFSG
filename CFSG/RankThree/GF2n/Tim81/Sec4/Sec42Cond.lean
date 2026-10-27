module

public import CFSG.RankThree.GF2n.Tim81.Sec4.ConjH
public import CFSG.RankThree.GF2n.Tim79aWCQ
public import CFSG.CGT.Timmesfeld75.CentralQuotient
public import CFSG.RankThree.GF2n.Tim81.Sec4.KElem

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open RootHyp
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G}

theorem RootHyp.weaklyClosedIn_pCore (h : RootHyp M V) :
    WeaklyClosedIn V (inSubgroup (pCore 2) M) := by
  refine ⟨h.toHyp.le_Q, ?_⟩
  intro g hg
  have hgM : conjSubgroup g V ≤ M := hg.trans (inSubgroup_pCore_two M).2.1
  have hne : conjSubgroup g V ⊓ M ≠ ⊥ := by
    rw [inf_eq_left.mpr hgM]
    intro hbot
    exact h.toHyp.ne_bot (conjSubgroup_eq_bot_iff.mp hbot)
  have hcomm := h.toHyp.commute_of_conj_inf_ne_bot h.rootType hne
  have hP : conjSubgroup g V ≤ Pc M V := by
    refine le_inf hg ?_
    rw [Subgroup.le_centralizer_iff]
    intro v hv b hb
    exact (hcomm v hv b hb).symm
  exact h.weaklyClosed_P.2 g hP

theorem RootHyp.le_pCore_of_isHMember (h79 : Tim79aStatementWCQ) (h : RootHyp M V)
    (hmem : IsHMember M V H) : V ≤ inSubgroup (pCore 2) H := by
  rcases h79 G h.o2 M h.maxLocal h.fitting V h.maxAb h.elem h.ti h.four_le_card
      h.weaklyClosedIn_pCore with hwc | hle
  · exact absurd hwc h.not_weaklyClosed
  · exact hle H hmem.1 hmem.2.1

theorem RootHyp.conjSubgroup_eq_self_of_sup_conj_Pc_eq (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {y : G} (hy : y ∈ H)
    (hsup : conjSubgroup y (Pc M V) ⊔ kOf V H = Pc M V ⊔ kOf V H) :
    y ∈ M ∧ conjSubgroup y (Pc M V) = Pc M V ∧ conjSubgroup y V = V := by
  have hV : conjSubgroup y V = V := by
    have h1 := RootHyp.xOf_inf_centralizer_sup_kOf_eq h hPH hy
    have h2 := RootHyp.xOf_inf_centralizer_sup_kOf_eq (H := H) h hPH (x := 1) H.one_mem
    rw [hsup] at h1
    exact h1.symm.trans (by simpa only [conjSubgroup_one] using h2)
  have hyM : y ∈ M := by
    rw [← h.toHyp.normalizer_eq]
    exact conjSubgroup_eq_self_iff.mp hV
  refine ⟨hyM, ?_, hV⟩
  rw [conjSubgroup_eq_self_iff]
  exact h.toHyp.le_normalizer_Pc hyM

theorem IsL2OrSzGroup.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsL2OrSzGroup X) : IsL2OrSzGroup Y := by
  rcases h with ⟨F, hF, hFintype, hCharP, hcard, ⟨φ⟩⟩ |
    ⟨a, F, hF, hFintype, hCharP, ha, hcard, ⟨φ⟩⟩
  · exact Or.inl ⟨F, hF, hFintype, hCharP, hcard, ⟨e.symm.trans φ⟩⟩
  · exact Or.inr ⟨a, F, hF, hFintype, hCharP, ha, hcard, ⟨e.symm.trans φ⟩⟩

theorem normalClosure_imgK_eq_top (h : RootHyp M V) (hPH : Pc M V ≤ H) {y : G}
    (hy : y ∈ H) (hH : H = Pc M V ⊔ conjSubgroup y (Pc M V)) :
    Subgroup.normalClosure ((imgK V H (Pc M V) : Subgroup (HBar V H)) :
      Set (HBar V H)) = ⊤ := by
  have hPyH : conjSubgroup y (Pc M V) ≤ H := conjSubgroup_le_of_le_of_mem hPH hy
  have hgen : imgK V H (Pc M V) ⊔
      conjSubgroup (piK V H ⟨y, hy⟩) (imgK V H (Pc M V)) = ⊤ := by
    calc imgK V H (Pc M V) ⊔ conjSubgroup (piK V H ⟨y, hy⟩) (imgK V H (Pc M V))
        = imgK V H (Pc M V) ⊔ imgK V H (conjSubgroup y (Pc M V)) := by
          rw [imgK_conjSubgroup hy hPH]
      _ = imgK V H (Pc M V ⊔ conjSubgroup y (Pc M V)) :=
          imgK_sup hPH hPyH
      _ = imgK V H H := by rw [← hH]
      _ = ⊤ := imgK_self V H
  let N : Subgroup (HBar V H) :=
    Subgroup.normalClosure ((imgK V H (Pc M V) : Subgroup (HBar V H)) : Set (HBar V H))
  have hN : N.Normal := Subgroup.normalClosure_normal
  have hconj_le : conjSubgroup (piK V H ⟨y, hy⟩) (imgK V H (Pc M V)) ≤ N := by
    intro z hz
    rw [mem_conjSubgroup] at hz
    have hzN : (piK V H ⟨y, hy⟩)⁻¹ * z * piK V H ⟨y, hy⟩ ∈ N :=
      Subgroup.subset_normalClosure hz
    have h := hN.conj_mem ((piK V H ⟨y, hy⟩)⁻¹ * z * piK V H ⟨y, hy⟩) hzN
      (piK V H ⟨y, hy⟩)
    have heq : piK V H ⟨y, hy⟩ * ((piK V H ⟨y, hy⟩)⁻¹ * z * piK V H ⟨y, hy⟩) *
        (piK V H ⟨y, hy⟩)⁻¹ = z := by group
    rwa [heq] at h
  refine le_antisymm le_top ?_
  rw [← hgen]
  exact sup_le Subgroup.subset_normalClosure hconj_le

private def kOne (M V H : Subgroup G) (y : G) : Subgroup G :=
  (Pc M V ⊓ kOf V H) ⊔ (conjSubgroup y (Pc M V) ⊓ kOf V H)

private theorem normalClosure_eq_top_of_sup_conj_eq_top {X : Type} [Group X] {L : Subgroup X}
    {x : X} (hgen : L ⊔ conjSubgroup x L = ⊤) :
    Subgroup.normalClosure (L : Set X) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← hgen]
  exact sup_le Subgroup.le_normalClosure (conjSubgroup_le_normalClosure L x)

private theorem le_normalizer_sup_of_le_normalizer_left {P A B : Subgroup G}
    (hPA : P ≤ Subgroup.normalizer (A : Set G))
    (hPB : ⁅P, B⁆ ≤ A ⊔ B) (hB : B ≤ A ⊔ B) :
    P ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro p hp
  rw [← conjSubgroup_eq_self_iff]
  have hA : conjSubgroup p A = A := conjSubgroup_eq_self_iff.mpr (hPA hp)
  have hBle : conjSubgroup p B ≤ A ⊔ B := by
    intro x hx
    rw [mem_conjSubgroup] at hx
    have hcomm : ⁅p, p⁻¹ * x * p⁆ ∈ A ⊔ B :=
      hPB (Subgroup.commutator_mem_commutator hp hx)
    have hx' : x = ⁅p, p⁻¹ * x * p⁆ * (p⁻¹ * x * p) := by
      rw [commutatorElement_def]; group
    rw [hx']
    exact (A ⊔ B).mul_mem hcomm (hB hx)
  have hle : conjSubgroup p (A ⊔ B) ≤ A ⊔ B := by
    rw [show conjSubgroup p (A ⊔ B) = conjSubgroup p A ⊔ conjSubgroup p B from
      Subgroup.map_sup _ _ _, hA]
    exact sup_le le_sup_left hBle
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])

private theorem commutator_Pc_inf_conj_le (h : RootHyp M V) (hPH : Pc M V ≤ H) {y : G} :
    ⁅Pc M V, conjSubgroup y (Pc M V) ⊓ kOf V H⁆ ≤ Pc M V ⊓ kOf V H := by
  set B : Subgroup G := conjSubgroup y (Pc M V) ⊓ kOf V H with hB
  have hB_le_K : B ≤ kOf V H := by rw [hB]; exact inf_le_right
  have hB_le_M : B ≤ M := hB_le_K.trans (kOf_le_M h)
  have hPB_le_P : ⁅Pc M V, B⁆ ≤ Pc M V := by
    have hBnorm : B ≤ Subgroup.normalizer (Pc M V : Set G) :=
      hB_le_M.trans h.toHyp.le_normalizer_Pc
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hBnorm
  have hPB_le_K : ⁅Pc M V, B⁆ ≤ kOf V H := by
    have hPnormK : Pc M V ≤ Subgroup.normalizer (kOf V H : Set G) :=
      hPH.trans (le_normalizer_kOf V H)
    have hPK : ⁅kOf V H, Pc M V⁆ ≤ kOf V H :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp hPnormK
    calc ⁅Pc M V, B⁆ ≤ ⁅Pc M V, kOf V H⁆ := Subgroup.commutator_mono le_rfl hB_le_K
      _ = ⁅kOf V H, Pc M V⁆ := Subgroup.commutator_comm _ _
      _ ≤ kOf V H := hPK
  exact le_inf hPB_le_P hPB_le_K

private theorem commutator_conj_Pc_inf_le (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {y : G} (hy : y ∈ H) :
    ⁅conjSubgroup y (Pc M V), Pc M V ⊓ kOf V H⁆ ≤
      conjSubgroup y (Pc M V) ⊓ kOf V H := by
  set A : Subgroup G := Pc M V ⊓ kOf V H with hA
  have hA_le_K : A ≤ kOf V H := by rw [hA]; exact inf_le_right
  have hA_norm : A ≤ Subgroup.normalizer (conjSubgroup y (Pc M V) : Set G) :=
    hA_le_K.trans (RootHyp.kOf_le_normalizer_conjSubgroup_Pc_of_mem h hy)
  have hPyA_le_Py : ⁅conjSubgroup y (Pc M V), A⁆ ≤ conjSubgroup y (Pc M V) := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hA_norm
  have hPyA_le_K : ⁅conjSubgroup y (Pc M V), A⁆ ≤ kOf V H := by
    have hPynormK : conjSubgroup y (Pc M V) ≤ Subgroup.normalizer (kOf V H : Set G) :=
      (conjSubgroup_le_of_le_of_mem hPH hy).trans (le_normalizer_kOf V H)
    have hPyK : ⁅kOf V H, conjSubgroup y (Pc M V)⁆ ≤ kOf V H :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp hPynormK
    calc ⁅conjSubgroup y (Pc M V), A⁆ ≤ ⁅conjSubgroup y (Pc M V), kOf V H⁆ :=
          Subgroup.commutator_mono le_rfl hA_le_K
      _ = ⁅kOf V H, conjSubgroup y (Pc M V)⁆ := Subgroup.commutator_comm _ _
      _ ≤ kOf V H := hPyK
  exact le_inf hPyA_le_Py hPyA_le_K

private theorem kOne_normal (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {y : G} (hy : y ∈ H)
    (hH : H = Pc M V ⊔ conjSubgroup y (Pc M V)) :
    ((kOne M V H y).subgroupOf H).Normal := by
  have hPyH : conjSubgroup y (Pc M V) ≤ H := conjSubgroup_le_of_le_of_mem hPH hy
  have hK1_le_H : kOne M V H y ≤ H := by
    rw [kOne]
    exact sup_le (inf_le_right.trans (kOf_le V H)) (inf_le_right.trans (kOf_le V H))
  have hP_normA : Pc M V ≤ Subgroup.normalizer (Pc M V ⊓ kOf V H : Set G) := by
    have h1 : Pc M V ≤ Subgroup.normalizer (Pc M V : Set G) := Subgroup.le_normalizer
    have h2 : Pc M V ≤ Subgroup.normalizer (kOf V H : Set G) :=
      hPH.trans (le_normalizer_kOf V H)
    exact (le_inf h1 h2).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hPB_le_K1 : ⁅Pc M V, conjSubgroup y (Pc M V) ⊓ kOf V H⁆ ≤ kOne M V H y :=
    (commutator_Pc_inf_conj_le h hPH).trans (by rw [kOne]; exact le_sup_left)
  have hB_le_K1 : conjSubgroup y (Pc M V) ⊓ kOf V H ≤ kOne M V H y := by
    rw [kOne]; exact le_sup_right
  have hP_normK1 : Pc M V ≤ Subgroup.normalizer (kOne M V H y : Set G) :=
    le_normalizer_sup_of_le_normalizer_left hP_normA hPB_le_K1 hB_le_K1
  have hPy_normB : conjSubgroup y (Pc M V) ≤
      Subgroup.normalizer (conjSubgroup y (Pc M V) ⊓ kOf V H : Set G) := by
    have h1 : conjSubgroup y (Pc M V) ≤
        Subgroup.normalizer (conjSubgroup y (Pc M V) : Set G) := Subgroup.le_normalizer
    have h2 : conjSubgroup y (Pc M V) ≤ Subgroup.normalizer (kOf V H : Set G) :=
      hPyH.trans (le_normalizer_kOf V H)
    exact (le_inf h1 h2).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hPyA_le_K1 : ⁅conjSubgroup y (Pc M V), Pc M V ⊓ kOf V H⁆ ≤ kOne M V H y :=
    (commutator_conj_Pc_inf_le h hPH hy).trans (by rw [kOne]; exact le_sup_right)
  have hA_le_K1 : Pc M V ⊓ kOf V H ≤ kOne M V H y := by
    rw [kOne]; exact le_sup_left
  have hPy_normK1 : conjSubgroup y (Pc M V) ≤ Subgroup.normalizer (kOne M V H y : Set G) := by
    have h := le_normalizer_sup_of_le_normalizer_left (P := conjSubgroup y (Pc M V))
      (A := conjSubgroup y (Pc M V) ⊓ kOf V H) (B := Pc M V ⊓ kOf V H)
      hPy_normB (by
        show ⁅conjSubgroup y (Pc M V), Pc M V ⊓ kOf V H⁆ ≤
          conjSubgroup y (Pc M V) ⊓ kOf V H ⊔ Pc M V ⊓ kOf V H
        rw [sup_comm]
        exact hPyA_le_K1) (by
        show Pc M V ⊓ kOf V H ≤
          conjSubgroup y (Pc M V) ⊓ kOf V H ⊔ Pc M V ⊓ kOf V H
        rw [sup_comm]
        exact hA_le_K1)
    rw [kOne, sup_comm]
    exact h
  have hH_normK1 : H ≤ Subgroup.normalizer (kOne M V H y : Set G) :=
    hH.le.trans (sup_le hP_normK1 hPy_normK1)
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hK1_le_H).mpr hH_normK1

private theorem commutator_kOf_le_kOne (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {y : G} (hy : y ∈ H)
    (hH : H = Pc M V ⊔ conjSubgroup y (Pc M V)) :
    ⁅kOf V H, H⁆ ≤ kOne M V H y := by
  have hPyH : conjSubgroup y (Pc M V) ≤ H := conjSubgroup_le_of_le_of_mem hPH hy
  have hKP_le_K1 : ⁅kOf V H, Pc M V⁆ ≤ kOne M V H y := by
    have hK_le_NP : kOf V H ≤ Subgroup.normalizer (Pc M V : Set G) :=
      (kOf_le_M h).trans h.toHyp.le_normalizer_Pc
    have hKP_le_P : ⁅kOf V H, Pc M V⁆ ≤ Pc M V :=
      Subgroup.le_normalizer_iff_commutator_le_right.mp hK_le_NP
    have hPnormK : Pc M V ≤ Subgroup.normalizer (kOf V H : Set G) :=
      hPH.trans (le_normalizer_kOf V H)
    have hKP_le_K : ⁅kOf V H, Pc M V⁆ ≤ kOf V H :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp hPnormK
    exact (le_inf hKP_le_P hKP_le_K).trans (by rw [kOne]; exact le_sup_left)
  have hKPy_le_K1 : ⁅kOf V H, conjSubgroup y (Pc M V)⁆ ≤ kOne M V H y := by
    have hK_le_NPy : kOf V H ≤ Subgroup.normalizer (conjSubgroup y (Pc M V) : Set G) :=
      RootHyp.kOf_le_normalizer_conjSubgroup_Pc_of_mem h hy
    have hKPy_le_Py : ⁅kOf V H, conjSubgroup y (Pc M V)⁆ ≤ conjSubgroup y (Pc M V) :=
      Subgroup.le_normalizer_iff_commutator_le_right.mp hK_le_NPy
    have hPynormK : conjSubgroup y (Pc M V) ≤ Subgroup.normalizer (kOf V H : Set G) :=
      hPyH.trans (le_normalizer_kOf V H)
    have hKPy_le_K : ⁅kOf V H, conjSubgroup y (Pc M V)⁆ ≤ kOf V H :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp hPynormK
    exact (le_inf hKPy_le_Py hKPy_le_K).trans (by rw [kOne]; exact le_sup_right)
  let P0 : Subgroup ↥H := (Pc M V).subgroupOf H
  let Py0 : Subgroup ↥H := (conjSubgroup y (Pc M V)).subgroupOf H
  let K0 : Subgroup ↥H := (kOf V H).subgroupOf H
  haveI : K0.Normal := kOf_normal V H
  have hmap := congrArg (Subgroup.map H.subtype)
    (Subgroup.commutator_sup_right P0 Py0 K0)
  simp only [P0, Py0, K0, Subgroup.map_commutator, Subgroup.map_sup,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPH, inf_eq_left.mpr hPyH,
    inf_eq_left.mpr (kOf_le V H)] at hmap
  calc ⁅kOf V H, H⁆ = ⁅H, kOf V H⁆ := Subgroup.commutator_comm _ _
    _ = ⁅Pc M V ⊔ conjSubgroup y (Pc M V), kOf V H⁆ := by rw [hH]
    _ = ⁅Pc M V, kOf V H⁆ ⊔ ⁅conjSubgroup y (Pc M V), kOf V H⁆ := hmap
    _ ≤ kOne M V H y :=
      sup_le (by rwa [Subgroup.commutator_comm]) (by rwa [Subgroup.commutator_comm])

private theorem kFactorization_Z_center (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {y : G} (hyH : y ∈ H)
    (hH : H = Pc M V ⊔ conjSubgroup y (Pc M V))
    (K0 K10 : Subgroup ↥H) [K10.Normal]
    (hK0 : K0 = (kOf V H).subgroupOf H)
    (hK10 : K10 = (kOne M V H y).subgroupOf H) :
    K0.map (QuotientGroup.mk' K10) ≤ Subgroup.center (↥H ⧸ K10) := by
  intro z hz
  obtain ⟨k, hkK0, rfl⟩ := Subgroup.mem_map.mp hz
  rw [Subgroup.mem_center_iff]
  intro w
  obtain ⟨hh, rfl⟩ := QuotientGroup.mk'_surjective K10 w
  rw [← map_mul, ← map_mul]
  apply (QuotientGroup.eq_iff_div_mem).mpr
  rw [hK10, Subgroup.mem_subgroupOf]
  have hcomm : ⁅(hh : G), (k : G)⁆ ∈ kOne M V H y := by
    have hcomm_sub : ⁅H, kOf V H⁆ ≤ kOne M V H y := by
      rw [Subgroup.commutator_comm]
      exact commutator_kOf_le_kOne h hPH hyH hH
    refine hcomm_sub (Subgroup.commutator_mem_commutator hh.2 ?_)
    rw [hK0] at hkK0
    exact Subgroup.mem_subgroupOf.mp hkK0
  have hcoe : (((hh * k) / (k * hh) : ↥H) : G) = ⁅(hh : G), (k : G)⁆ := by
    simp [div_eq_mul_inv, commutatorElement_def, mul_assoc]
  rwa [hcoe]

private theorem kFactorization_map_ker {K0 K10 : Subgroup ↥H} [K10.Normal]
    (π : (↥H ⧸ K10) →* HBar V H)
    (hπ : ∀ x : ↥H, π (QuotientGroup.mk' K10 x) = piK V H x)
    (T : Subgroup (↥H ⧸ K10))
    (hT : T = ((Pc M V).subgroupOf H).map (QuotientGroup.mk' K10))
    (Z : Subgroup (↥H ⧸ K10)) [Z.Normal]
    (hZ : Z = K0.map (QuotientGroup.mk' K10))
    (hK0 : K0 = (kOf V H).subgroupOf H) :
    T.map π = imgK V H (Pc M V) ∧ (∀ u : (↥H ⧸ K10), π u = 1 → u ∈ Z) := by
  constructor
  · rw [hT]
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨p, hpP0, rfl⟩ := Subgroup.mem_map.mp hu
      exact Subgroup.mem_map.mpr ⟨p, Subgroup.mem_subgroupOf.mpr hpP0, (hπ p).symm⟩
    · rintro ⟨p, hpP, rfl⟩
      exact Subgroup.mem_map.mpr ⟨QuotientGroup.mk' K10 p,
        Subgroup.mem_map.mpr ⟨p, Subgroup.mem_subgroupOf.mpr hpP, rfl⟩, hπ p⟩
  · intro u hu
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K10 u
    rw [hπ x] at hu
    rw [hZ, hK0]
    exact Subgroup.mem_map.mpr ⟨x, (piK_eq_one_iff x).mp hu, rfl⟩

private theorem kFactorization_TZ {y : G} (K0 K10 : Subgroup ↥H) [K10.Normal]
    (T Z : Subgroup (↥H ⧸ K10))
    (hT : T = ((Pc M V).subgroupOf H).map (QuotientGroup.mk' K10))
    (hZ : Z = K0.map (QuotientGroup.mk' K10))
    (hK0 : K0 = (kOf V H).subgroupOf H)
    (hK10 : K10 = (kOne M V H y).subgroupOf H) :
    T ⊓ Z = ⊥ := by
  have hK1_le_K : kOne M V H y ≤ kOf V H := by
    rw [kOne]; exact sup_le inf_le_right inf_le_right
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxT, hxZ⟩ := Subgroup.mem_inf.mp hx
  rw [hT] at hxT
  rw [hZ] at hxZ
  obtain ⟨p, hpP0, rfl⟩ := Subgroup.mem_map.mp hxT
  obtain ⟨k, hkK0, hk⟩ := Subgroup.mem_map.mp hxZ
  have hdiv : k / p ∈ K10 := (QuotientGroup.eq_iff_div_mem).mp hk
  have hdivK : k / p ∈ K0 := by
    rw [hK10, Subgroup.mem_subgroupOf] at hdiv
    rw [hK0, Subgroup.mem_subgroupOf]
    exact hK1_le_K hdiv
  have hp_invK0 : p⁻¹ ∈ K0 := by
    have h1 : k⁻¹ * (k / p) ∈ K0 := K0.mul_mem (K0.inv_mem hkK0) hdivK
    simpa [div_eq_mul_inv, mul_assoc] using h1
  have hpK0 : p ∈ K0 := by simpa using K0.inv_mem hp_invK0
  have hpA : (p : G) ∈ Pc M V ⊓ kOf V H :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hpP0,
      Subgroup.mem_subgroupOf.mp (by rwa [hK0] at hpK0)⟩
  have hpK10 : p ∈ K10 := by
    rw [hK10, Subgroup.mem_subgroupOf]
    exact (show Pc M V ⊓ kOf V H ≤ kOne M V H y from by rw [kOne]; exact le_sup_left) hpA
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff p).mpr hpK10

private theorem kFactorization_T_elem (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {y : G}
    (K10 : Subgroup ↥H) [K10.Normal]
    (hK10 : K10 = (kOne M V H y).subgroupOf H)
    (T : Subgroup (↥H ⧸ K10))
    (hT : T = ((Pc M V).subgroupOf H).map (QuotientGroup.mk' K10)) :
    Assembly.IsElemAbelian 2 T := by
  rw [hT]
  let P0 : Subgroup ↥H := (Pc M V).subgroupOf H
  change Assembly.IsElemAbelian 2 (P0.map (QuotientGroup.mk' K10))
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hV_le_A : V ≤ Pc M V ⊓ kOf V H := le_inf h.toHyp.le_Pc (le_kOf h hPH hVH)
  have hPhiK : inSubgroup frattini (Pc M V) ≤ kOne M V H y :=
    h.toHyp.frattini_Pc_le.trans (hV_le_A.trans (by rw [kOne]; exact le_sup_left))
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨p, hpP0, hp⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨q, hqP0, hq⟩ := Subgroup.mem_map.mp b.2
    have hpP : (p : G) ∈ Pc M V := Subgroup.mem_subgroupOf.mp hpP0
    have hqP : (q : G) ∈ Pc M V := Subgroup.mem_subgroupOf.mp hqP0
    have hdiv : (p * q) / (q * p) ∈ K10 := by
      rw [hK10, Subgroup.mem_subgroupOf]
      have hcoe : (((p * q) / (q * p) : ↥H) : G) = ⁅(p : G), (q : G)⁆ := by
        simp [div_eq_mul_inv, commutatorElement_def, mul_assoc]
      rw [hcoe]
      exact hPhiK (commutatorElement_mem_inSubgroup_frattini hP2 hpP hqP)
    have heq : (QuotientGroup.mk' K10) (p * q) = (QuotientGroup.mk' K10) (q * p) :=
      (QuotientGroup.eq_iff_div_mem).mpr hdiv
    have hmain : (a : ↥H ⧸ K10) * b = (b : ↥H ⧸ K10) * a := by
      calc (a : ↥H ⧸ K10) * b = (QuotientGroup.mk' K10) (p * q) := by
            rw [← hp, ← hq, map_mul]
        _ = (QuotientGroup.mk' K10) (q * p) := heq
        _ = (b : ↥H ⧸ K10) * a := by rw [← hp, ← hq, map_mul]
    exact Subtype.ext hmain
  · intro a ha
    obtain ⟨p, hpP0, hp⟩ := Subgroup.mem_map.mp ha
    have hpP : (p : G) ∈ Pc M V := Subgroup.mem_subgroupOf.mp hpP0
    have hsq : p ^ 2 ∈ K10 := by
      rw [hK10, Subgroup.mem_subgroupOf]
      have hcoe : (((p ^ 2 : ↥H) : G)) = (p : G) ^ 2 := by simp
      rw [hcoe]
      exact hPhiK (sq_mem_inSubgroup_frattini hP2 hpP)
    have h1 : (QuotientGroup.mk' K10) (p ^ 2) = 1 :=
      (QuotientGroup.eq_one_iff (p ^ 2)).mpr hsq
    calc a ^ 2 = ((QuotientGroup.mk' K10) p) ^ 2 := by rw [← hp]
      _ = (QuotientGroup.mk' K10) (p ^ 2) := (map_pow _ _ _).symm
      _ = 1 := h1

private theorem kFactorization_normalClosure (hPH : Pc M V ≤ H) {y : G} (hyH : y ∈ H)
    (hH : H = Pc M V ⊔ conjSubgroup y (Pc M V))
    (K10 : Subgroup ↥H) [K10.Normal]
    (T : Subgroup (↥H ⧸ K10))
    (hT : T = ((Pc M V).subgroupOf H).map (QuotientGroup.mk' K10)) :
    Subgroup.normalClosure (T : Set (↥H ⧸ K10)) = ⊤ := by
  rw [hT]
  let P0 : Subgroup ↥H := (Pc M V).subgroupOf H
  let T0 : Subgroup (↥H ⧸ K10) := P0.map (QuotientGroup.mk' K10)
  change Subgroup.normalClosure (T0 : Set (↥H ⧸ K10)) = ⊤
  have hPyH : conjSubgroup y (Pc M V) ≤ H := conjSubgroup_le_of_le_of_mem hPH hyH
  have hconjP0 : (conjSubgroup y (Pc M V)).subgroupOf H = conjSubgroup ⟨y, hyH⟩ P0 := by
    ext z
    simp only [P0, Subgroup.mem_subgroupOf, mem_conjSubgroup, Subgroup.coe_mul,
      Subgroup.coe_inv]
  have hP0_sup : P0 ⊔ conjSubgroup ⟨y, hyH⟩ P0 = ⊤ := by
    rw [← hconjP0, ← Subgroup.subgroupOf_sup hPH hPyH, hH, Subgroup.subgroupOf_self]
  have hgenT : T0 ⊔ conjSubgroup (QuotientGroup.mk' K10 ⟨y, hyH⟩) T0 = ⊤ := by
    calc T0 ⊔ conjSubgroup (QuotientGroup.mk' K10 ⟨y, hyH⟩) T0
        = P0.map (QuotientGroup.mk' K10) ⊔
            (conjSubgroup ⟨y, hyH⟩ P0).map (QuotientGroup.mk' K10) := by
          rw [show conjSubgroup (QuotientGroup.mk' K10 ⟨y, hyH⟩) T0 =
              (conjSubgroup ⟨y, hyH⟩ P0).map (QuotientGroup.mk' K10) from
            (map_conjSubgroup (QuotientGroup.mk' K10) ⟨y, hyH⟩ P0).symm]
      _ = (P0 ⊔ conjSubgroup ⟨y, hyH⟩ P0).map (QuotientGroup.mk' K10) :=
          (Subgroup.map_sup _ _ _).symm
      _ = (⊤ : Subgroup ↥H).map (QuotientGroup.mk' K10) := by rw [hP0_sup]
      _ = ⊤ := Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective K10)
  exact normalClosure_eq_top_of_sup_conj_eq_top hgenT

private theorem kFactorization_conjT_of_eq (K10 : Subgroup ↥H) [K10.Normal]
    (T : Subgroup (↥H ⧸ K10))
    (hT : T = ((Pc M V).subgroupOf H).map (QuotientGroup.mk' K10)) :
    ∀ {x : ↥H}, conjSubgroup (x : G) (Pc M V) = Pc M V →
      conjSubgroup (QuotientGroup.mk' K10 x) T = T := by
  intro x hPx
  rw [hT]
  let P0 : Subgroup ↥H := (Pc M V).subgroupOf H
  change conjSubgroup (QuotientGroup.mk' K10 x) (P0.map (QuotientGroup.mk' K10)) =
    P0.map (QuotientGroup.mk' K10)
  have hconjP0x : (conjSubgroup (x : G) (Pc M V)).subgroupOf H = conjSubgroup x P0 := by
    ext z
    simp only [P0, Subgroup.mem_subgroupOf, mem_conjSubgroup, Subgroup.coe_mul,
      Subgroup.coe_inv]
  calc conjSubgroup (QuotientGroup.mk' K10 x) (P0.map (QuotientGroup.mk' K10))
      = (conjSubgroup x P0).map (QuotientGroup.mk' K10) :=
        (map_conjSubgroup (QuotientGroup.mk' K10) x P0).symm
    _ = P0.map (QuotientGroup.mk' K10) := by
        rw [← hconjP0x, hPx]

private theorem kFactorization_isTI_T (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H)
    (K10 : Subgroup ↥H) [K10.Normal]
    (π : (↥H ⧸ K10) →* HBar V H)
    (hπ : ∀ x : ↥H, π (QuotientGroup.mk' K10 x) = piK V H x)
    (T Z : Subgroup (↥H ⧸ K10)) [Z.Normal]
    (hTZ : T ⊓ Z = ⊥) (hkerπ : ∀ u : (↥H ⧸ K10), π u = 1 → u ∈ Z)
    (hmapT : T.map π = imgK V H (Pc M V))
    (hconjT_of_eq : ∀ {x : ↥H}, conjSubgroup (x : G) (Pc M V) = Pc M V →
      conjSubgroup (QuotientGroup.mk' K10 x) T = T) :
    IsTI T := by
  intro g
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K10 g
  by_cases hbot : T ⊓ conjSubgroup (QuotientGroup.mk' K10 x) T = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨u, hu_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
    have huT : (u : ↥H ⧸ K10) ∈ T := (Subgroup.mem_inf.mp u.2).1
    have hux : (u : ↥H ⧸ K10) ∈ conjSubgroup (QuotientGroup.mk' K10 x) T :=
      (Subgroup.mem_inf.mp u.2).2
    have hπu_ne : π (u : ↥H ⧸ K10) ≠ 1 := by
      intro h1
      have hmem : (u : ↥H ⧸ K10) ∈ T ⊓ Z :=
        Subgroup.mem_inf.mpr ⟨huT, hkerπ (u : ↥H ⧸ K10) h1⟩
      rw [hTZ] at hmem
      exact hu_ne (Subtype.ext (Subgroup.mem_bot.mp hmem))
    have hπu_T : π (u : ↥H ⧸ K10) ∈ imgK V H (Pc M V) := by
      rw [← hmapT]
      exact Subgroup.mem_map_of_mem π huT
    have hπu_Tx : π (u : ↥H ⧸ K10) ∈
        conjSubgroup (piK V H x) (imgK V H (Pc M V)) := by
      have hmap : (conjSubgroup (QuotientGroup.mk' K10 x) T).map π =
          conjSubgroup (π (QuotientGroup.mk' K10 x)) (T.map π) :=
        map_conjSubgroup π (QuotientGroup.mk' K10 x) T
      have hmem : π (u : ↥H ⧸ K10) ∈ (conjSubgroup (QuotientGroup.mk' K10 x) T).map π :=
        Subgroup.mem_map_of_mem π hux
      rwa [hmap, hmapT, hπ x] at hmem
    have hne : imgK V H (Pc M V) ⊓ conjSubgroup (piK V H x) (imgK V H (Pc M V)) ≠ ⊥ := by
      intro hbot2
      have hmem : π (u : ↥H ⧸ K10) ∈ imgK V H (Pc M V) ⊓
          conjSubgroup (piK V H x) (imgK V H (Pc M V)) :=
        Subgroup.mem_inf.mpr ⟨hπu_T, hπu_Tx⟩
      rw [hbot2] at hmem
      exact hπu_ne (Subgroup.mem_bot.mp hmem)
    have heq : conjSubgroup (piK V H x) (imgK V H (Pc M V)) = imgK V H (Pc M V) :=
      conjSubgroup_eq_of_isTI (isTI_imgK h hPH hVH) hne
    have himg : imgK V H (conjSubgroup (x : G) (Pc M V)) = imgK V H (Pc M V) := by
      rw [imgK_conjSubgroup x.2 hPH]
      exact heq
    have hsup : conjSubgroup (x : G) (Pc M V) ⊔ kOf V H = Pc M V ⊔ kOf V H :=
      (imgK_eq_iff_sup_kOf_eq (V := V) (H := H)
        (conjSubgroup_le_of_le_of_mem hPH x.2) hPH).mp himg
    have hPx : conjSubgroup (x : G) (Pc M V) = Pc M V :=
      (h.conjSubgroup_eq_self_of_sup_conj_Pc_eq hPH x.2 hsup).2.1
    rw [hconjT_of_eq hPx, inf_idem]

private theorem kFactorization_weaklyClosed_T (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (K10 : Subgroup ↥H) [K10.Normal]
    (π : (↥H ⧸ K10) →* HBar V H)
    (hπ : ∀ x : ↥H, π (QuotientGroup.mk' K10 x) = piK V H x)
    (T : Subgroup (↥H ⧸ K10))
    (hmapT : T.map π = imgK V H (Pc M V))
    (hconjT_of_eq : ∀ {x : ↥H}, conjSubgroup (x : G) (Pc M V) = Pc M V →
      conjSubgroup (QuotientGroup.mk' K10 x) T = T) :
    WeaklyClosedIn T (Subgroup.normalizer (T : Set (↥H ⧸ K10))) := by
  refine ⟨Subgroup.le_normalizer, ?_⟩
  intro g hg
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K10 g
  have hmap_conj : (conjSubgroup (QuotientGroup.mk' K10 x) T).map π =
      conjSubgroup (piK V H x) (imgK V H (Pc M V)) := by
    rw [map_conjSubgroup, hmapT, hπ x]
  have hle : conjSubgroup (piK V H x) (imgK V H (Pc M V)) ≤
      Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H)) := by
    intro z hz
    rw [← hmap_conj] at hz
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hz
    have huN : u ∈ Subgroup.normalizer (T : Set (↥H ⧸ K10)) := hg hu
    have hconj : conjSubgroup (π u) (T.map π) = T.map π := by
      rw [← map_conjSubgroup, conjSubgroup_eq_self_iff.mpr huN]
    rw [← conjSubgroup_eq_self_iff, ← hmapT]
    exact hconj
  have hle' : imgK V H (conjSubgroup (x : G) (Pc M V)) ≤
      Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H)) := by
    rwa [imgK_conjSubgroup x.2 hPH]
  have hbar := weaklyClosed_imgK h hPH x.2 hle'
  have hconjbar : conjSubgroup (piK V H x) (imgK V H (Pc M V)) = imgK V H (Pc M V) := by
    rw [← imgK_conjSubgroup x.2 hPH]
    exact hbar
  have hsup : conjSubgroup (x : G) (Pc M V) ⊔ kOf V H = Pc M V ⊔ kOf V H := by
    have himg : imgK V H (conjSubgroup (x : G) (Pc M V)) = imgK V H (Pc M V) := by
      rw [imgK_conjSubgroup x.2 hPH]
      exact hconjbar
    exact (imgK_eq_iff_sup_kOf_eq (V := V) (H := H)
      (conjSubgroup_le_of_le_of_mem hPH x.2) hPH).mp himg
  have hPx : conjSubgroup (x : G) (Pc M V) = Pc M V :=
    (h.conjSubgroup_eq_self_of_sup_conj_Pc_eq hPH x.2 hsup).2.1
  exact hconjT_of_eq hPx

private theorem kFactorization_Z_eq_bot (hCT : CentralTIStatement) (hL : IsL2OrSz V H)
    {K0 K10 : Subgroup ↥H} [K10.Normal] [K0.Normal]
    (hK10_le_K0 : K10 ≤ K0) (hK0 : K0 = (kOf V H).subgroupOf H)
    (T Z : Subgroup (↥H ⧸ K10)) [Z.Normal]
    (hZ : Z = K0.map (QuotientGroup.mk' K10))
    (hT_elem : Assembly.IsElemAbelian 2 T)
    (hgen : Subgroup.normalClosure (T : Set (↥H ⧸ K10)) = ⊤)
    (hTI : IsTI T)
    (hwc : WeaklyClosedIn T (Subgroup.normalizer (T : Set (↥H ⧸ K10))))
    (hZ_center : Z ≤ Subgroup.center (↥H ⧸ K10)) :
    Z = ⊥ := by
  haveI : (K0.map (QuotientGroup.mk' K10)).Normal :=
    QuotientGroup.map_normal (G := ↥H) K10 K0
  haveI : Finite (↥H ⧸ K10) := inferInstance
  refine hCT (↥H ⧸ K10) T Z hT_elem hgen hTI hwc hZ_center ?_
  have e0 : (↥H ⧸ K10) ⧸ (K0.map (QuotientGroup.mk' K10)) ≃* ↥H ⧸ K0 :=
    QuotientGroup.quotientQuotientEquivQuotient (G := ↥H) (N := K10) (M := K0) hK10_le_K0
  have eK : (↥H ⧸ K0) ≃* HBar V H := QuotientGroup.quotientMulEquivOfEq hK0
  have eZ : (↥H ⧸ K10) ⧸ (K0.map (QuotientGroup.mk' K10)) ≃* (↥H ⧸ K10) ⧸ Z :=
    (QuotientGroup.quotientMulEquivOfEq hZ).symm
  have e1 : (↥H ⧸ K10) ⧸ Z ≃* HBar V H := (eZ.symm.trans e0).trans eK
  exact IsL2OrSzGroup.of_mulEquiv e1.symm hL

private theorem kFactorization_kOf_le_kOne {y : G} {K0 K10 : Subgroup ↥H} [K10.Normal]
    (hK0 : K0 = (kOf V H).subgroupOf H)
    (hK10 : K10 = (kOne M V H y).subgroupOf H)
    (hZ_bot : K0.map (QuotientGroup.mk' K10) = ⊥) :
    kOf V H ≤ kOne M V H y := by
  intro k hk
  have hkH : k ∈ H := kOf_le V H hk
  have hkK0 : (⟨k, hkH⟩ : ↥H) ∈ K0 := by
    rw [hK0]
    exact Subgroup.mem_subgroupOf.mpr hk
  have hmem : (QuotientGroup.mk' K10) ⟨k, hkH⟩ ∈ K0.map (QuotientGroup.mk' K10) :=
    Subgroup.mem_map.mpr ⟨⟨k, hkH⟩, hkK0, rfl⟩
  rw [hZ_bot] at hmem
  have h1 : (QuotientGroup.mk' K10) ⟨k, hkH⟩ = 1 := Subgroup.mem_bot.mp hmem
  have hkK10 : (⟨k, hkH⟩ : ↥H) ∈ K10 := (QuotientGroup.eq_one_iff _).mp h1
  rw [hK10, Subgroup.mem_subgroupOf] at hkK10
  exact hkK10

theorem RootHyp.kFactorization_of_centralTI (hCT : CentralTIStatement) (h : RootHyp M V)
    (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V))
    (hL : IsL2OrSz V H) : KFactorization M V H h₀ := by
  classical
  obtain ⟨y, hyH, hPy, hVy, hHy⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  rw [KFactorization, hPy]
  have hK1_le_K : kOne M V H y ≤ kOf V H := by
    rw [kOne]; exact sup_le inf_le_right inf_le_right
  let K0 : Subgroup ↥H := (kOf V H).subgroupOf H
  let K10 : Subgroup ↥H := (kOne M V H y).subgroupOf H
  haveI hK0_normal : K0.Normal := kOf_normal V H
  haveI hK10_normal : K10.Normal := kOne_normal h hPH hyH hHy
  have hK10_le_K0 : K10 ≤ K0 := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hK1_le_K (Subgroup.mem_subgroupOf.mp hx))
  let Y := ↥H ⧸ K10
  haveI : Finite Y := inferInstance
  let P0 : Subgroup ↥H := (Pc M V).subgroupOf H
  let T : Subgroup Y := P0.map (QuotientGroup.mk' K10)
  let Z : Subgroup Y := K0.map (QuotientGroup.mk' K10)
  haveI hZ_normal : Z.Normal := QuotientGroup.map_normal (G := ↥H) K10 K0
  let π : Y →* HBar V H := QuotientGroup.lift K10 (piK V H) (by
    intro x hx
    exact (piK_eq_one_iff x).mpr (hK1_le_K (Subgroup.mem_subgroupOf.mp hx)))
  have hπ_mk : ∀ x : ↥H, π (QuotientGroup.mk' K10 x) = piK V H x := fun x => rfl
  obtain ⟨hmapT, hkerπ⟩ := kFactorization_map_ker (K0 := K0) (K10 := K10)
    π hπ_mk T rfl Z rfl rfl
  have hZ_center : Z ≤ Subgroup.center Y :=
    kFactorization_Z_center h hPH hyH hHy K0 K10 rfl rfl
  have hTZ : T ⊓ Z = ⊥ :=
    kFactorization_TZ (y := y) (K0 := K0) (K10 := K10) T Z rfl rfl rfl rfl
  have hT_elem : Assembly.IsElemAbelian 2 T :=
    kFactorization_T_elem h hPH hVH (y := y) (K10 := K10) rfl T rfl
  have hgen : Subgroup.normalClosure (T : Set Y) = ⊤ :=
    kFactorization_normalClosure hPH hyH hHy (K10 := K10) T rfl
  have hconjT_of_eq : ∀ {x : ↥H}, conjSubgroup (x : G) (Pc M V) = Pc M V →
      conjSubgroup (QuotientGroup.mk' K10 x) T = T :=
    kFactorization_conjT_of_eq (K10 := K10) T rfl
  have hTI_T : IsTI T :=
    kFactorization_isTI_T h hPH hVH (K10 := K10) π hπ_mk T Z hTZ hkerπ hmapT hconjT_of_eq
  have hwc_T : WeaklyClosedIn T (Subgroup.normalizer (T : Set Y)) :=
    kFactorization_weaklyClosed_T h hPH (K10 := K10) π hπ_mk T hmapT hconjT_of_eq
  have hZ_bot : Z = ⊥ :=
    kFactorization_Z_eq_bot hCT hL (K0 := K0) (K10 := K10) hK10_le_K0 rfl T Z rfl
      hT_elem hgen hTI_T hwc_T hZ_center
  exact le_antisymm
    (kFactorization_kOf_le_kOne (y := y) (K0 := K0) (K10 := K10) rfl rfl hZ_bot)
    hK1_le_K

end CFSG.RankThree.GF2n.Tim81
