module

public import CFSG.Quasithin.Recognition.Stroth.MoufangR2
public import CFSG.Quasithin.Recognition.Stroth.MoufangRankTwoSystem
public import CFSG.Quasithin.Recognition.Stroth.Weiss80AssemblyFacts
public import CFSG.Quasithin.Recognition.Stroth.MoufangBN

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.Geometry.GeneralizedPolygons

open scoped Pointwise

variable {V : Type} [Fintype V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
  {n : ℕ} {D : Type} [Group D] [MulAction D V] [FaithfulSMul D V] [GraphAction D Γ]

private theorem finite_of_faithfulSMul (V : Type) [Fintype V] (D : Type) [Group D]
    [MulAction D V] [FaithfulSMul D V] : Finite D :=
  Finite.of_injective (MulAction.toPermHom D V) MulAction.toPerm_injective

theorem rootD_eq_aptRoot_of_pos (t : ZMod (2 * n) → V) {i : ℤ} (hi : 0 < i) :
    rootD (D := D) (Γ := Γ) (n := n) t i = aptRoot D Γ n t i := by
  rw [rootD, if_pos hi]

theorem rootD_eq_aptRoot_of_nonpos (t : ZMod (2 * n) → V) {i : ℤ} (hi : i ≤ 0) :
    rootD (D := D) (Γ := Γ) (n := n) t i = aptRoot D Γ n t ((n : ℤ) - i) := by
  rw [rootD, if_neg (by omega)]

theorem exists_card_rootL_pos {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    (hdeg : ∀ v : V, ∃ e : ℕ, Γ.degree v = 2 ^ e + 1) {i : ℤ} (hi1 : 1 ≤ i)
    (hin : i ≤ (n : ℤ)) :
    ∃ e : ℕ, Nat.card (rootL (D := D) (Γ := Γ) (n := n) t i) = 2 ^ e := by
  obtain ⟨e, he⟩ := hdeg (apt t (i + (n : ℤ)))
  refine ⟨e, ?_⟩
  have hpath := card_pathRootGroup_add_one (D := D) (Γ := Γ) (n := n) hn hP hT hM
    (aptPath ht.2 i) (aptPath_noBack (by omega) ht i)
  have hpath' : Nat.card (pathRootGroup D Γ (aptPath ht.2 i)) + 1 = 2 ^ e + 1 := by
    rw [hpath, aptPath_apply ht.2 i le_rfl, he]
  have hc : Nat.card (pathRootGroup D Γ (aptPath ht.2 i)) = 2 ^ e := by omega
  have hcardD : Nat.card (rootD (D := D) (Γ := Γ) (n := n) t i) = 2 ^ e := by
    rw [rootD_eq_aptRoot_of_pos (t := t) (by omega), aptRoot_eq_pathRootGroup ht i]
    exact hc
  have hle : rootD (D := D) (Γ := Γ) (n := n) t i ≤ littleGroup D Γ n :=
    rootD_le_littleGroup (t := t) ht (by omega) i
  rw [rootL]
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
  exact hcardD

theorem card_rootU {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    Nat.card (rootU (D := D) (Γ := Γ) (n := n) t) =
      ((intList 1 (n : ℤ)).map fun k => Nat.card
        (rootL (D := D) (Γ := Γ) (n := n) t k)).prod := by
  have hcard : Nat.card (rootU (D := D) (Γ := Γ) (n := n) t) =
      Nat.card (chainProd (rootL (D := D) (Γ := Γ) (n := n) t) (intList 1 (n : ℤ))) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
    intro x
    exact Set.ext_iff.mp (rootU_coe (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) x
  rw [hcard]
  exact cardU_card_chainProd (rootL (D := D) (Γ := Γ) (n := n) t) (intList 1 (n : ℤ))
    (chain_intList_nodup 1 (n : ℤ))
    (fun f g hf hg heq => rootL_prod_unique (t := t) ht hn hP hT hM hf hg heq)

theorem exists_card_rootU {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    (hdeg : ∀ v : V, ∃ e : ℕ, Γ.degree v = 2 ^ e + 1) :
    ∃ e : ℕ, Nat.card (rootU (D := D) (Γ := Γ) (n := n) t) = 2 ^ e := by
  rw [card_rootU (t := t) ht hn hP hT hM]
  refine cardU_prod_isPow _ ?_
  intro a ha
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 ha
  have hk' := mem_intList_iff.1 hk
  exact exists_card_rootL_pos (t := t) ht hn hP hT hM hdeg hk'.1 hk'.2

theorem isPGroup_rootU {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    (hdeg : ∀ v : V, ∃ e : ℕ, Γ.degree v = 2 ^ e + 1) :
    IsPGroup 2 (rootU (D := D) (Γ := Γ) (n := n) t) := by
  obtain ⟨e, he⟩ := exists_card_rootU (t := t) ht hn hP hT hM hdeg
  exact IsPGroup.of_card he

theorem isNilpotent_rootU {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    (hdeg : ∀ v : V, ∃ e : ℕ, Γ.degree v = 2 ^ e + 1) :
    Group.IsNilpotent (rootU (D := D) (Γ := Γ) (n := n) t) := by
  haveI : Finite D := finite_of_faithfulSMul V D
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  exact (isPGroup_rootU (t := t) ht hn hP hT hM hdeg).isNilpotent

theorem rootL_le_littleBorel {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    {k : ℤ} (hk1 : 1 ≤ k) (hkn : k ≤ (n : ℤ)) :
    rootL (D := D) (Γ := Γ) (n := n) t k ≤ moufangB D Γ n t := by
  intro x hx
  have hxD : (x : D) ∈ aptRoot D Γ n t k := by
    have h := hx
    rw [rootL, Subgroup.mem_subgroupOf] at h
    rwa [rootD_eq_aptRoot_of_pos (t := t) (by omega)] at h
  change x ∈ moufangB D Γ n t
  rw [mem_moufangB]
  constructor
  · have hfix := aptRoot_fix (t := t) ht hxD hn (r := (n : ℤ) - k) (by omega) (by omega)
    rw [show k + ((n : ℤ) - k) = (n : ℤ) by ring] at hfix
    simpa [apt] using hfix
  · have hfix := aptRoot_fix (t := t) ht hxD hn (r := (n : ℤ) + 1 - k) (by omega) (by omega)
    rw [show k + ((n : ℤ) + 1 - k) = (n : ℤ) + 1 by ring] at hfix
    simpa [apt] using hfix

theorem rootU_le_littleBorel {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    rootU (D := D) (Γ := Γ) (n := n) t ≤ moufangB D Γ n t := by
  intro x hx
  have hx' : (x : ↥(littleGroup D Γ n)) ∈
      chainProd (rootL (D := D) (Γ := Γ) (n := n) t) (intList 1 (n : ℤ)) := by
    change (x : ↥(littleGroup D Γ n)) ∈ (rootU (D := D) (Γ := Γ) (n := n) t :
      Set ↥(littleGroup D Γ n)) at hx
    rwa [rootU_coe] at hx
  refine chainProd_subset (rootL (D := D) (Γ := Γ) (n := n) t) (moufangB D Γ n t)
    (intList 1 (n : ℤ)) (fun k hk => ?_) hx'
  exact rootL_le_littleBorel (t := t) ht hn (mem_intList_iff.1 hk).1 (mem_intList_iff.1 hk).2

theorem baseRootProduct_le_rootU_map {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) :
    baseRootProduct D Γ n t ≤
      (rootU (D := D) (Γ := Γ) (n := n) t).map
        (littleGroup D Γ n).subtype := by
  rw [baseRootProduct]
  refine iSup_le fun k => iSup_le fun hk => ?_
  intro x hx
  have hk' : 1 ≤ k ∧ k ≤ (n : ℤ) := hk
  have hxL : x ∈ littleGroup D Γ n := aptRoot_le_littleGroup ht (by omega) k hx
  refine ⟨⟨x, hxL⟩, ?_, rfl⟩
  have hxroot : (⟨x, hxL⟩ : ↥(littleGroup D Γ n)) ∈ rootL (D := D) (Γ := Γ) (n := n) t k := by
    rw [rootL, Subgroup.mem_subgroupOf, rootD_eq_aptRoot_of_pos (t := t) (by omega)]
    exact hx
  have hxU : (⟨x, hxL⟩ : ↥(littleGroup D Γ n)) ∈
      rootU (D := D) (Γ := Γ) (n := n) t := by
    change (⟨x, hxL⟩ : ↥(littleGroup D Γ n)) ∈
      (rootU (D := D) (Γ := Γ) (n := n) t : Set ↥(littleGroup D Γ n))
    rw [rootU_coe (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM]
    exact mem_chainProd_of_mem (rootL (D := D) (Γ := Γ) (n := n) t)
      (mem_intList_iff.2 ⟨hk'.1, hk'.2⟩) hxroot
  exact hxU

theorem moufangB_le_cartan_mul_rootU {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) :
    (moufangB D Γ n t : Set ↥(littleGroup D Γ n)) ⊆
      ((moufangCartan D Γ n t : Subgroup ↥(littleGroup D Γ n)) :
        Set ↥(littleGroup D Γ n)) *
      ((rootU (D := D) (Γ := Γ) (n := n) t) :
        Set ↥(littleGroup D Γ n)) := by
  intro g hg
  have hgB : (g : D) • t (n : ZMod (2 * n)) = t (n : ZMod (2 * n)) ∧
      (g : D) • t ((n : ZMod (2 * n)) + 1) = t ((n : ZMod (2 * n)) + 1) := by
    have hg' : g ∈ moufangB D Γ n t := hg
    exact mem_moufangB.mp hg'
  have hinv : (g : D)⁻¹ • t (n : ZMod (2 * n)) = t (n : ZMod (2 * n)) ∧
      (g : D)⁻¹ • t ((n : ZMod (2 * n)) + 1) = t ((n : ZMod (2 * n)) + 1) := by
    constructor
    · calc (g : D)⁻¹ • t (n : ZMod (2 * n))
          = (g : D)⁻¹ • ((g : D) • t (n : ZMod (2 * n))) := by rw [hgB.1]
        _ = t (n : ZMod (2 * n)) := inv_smul_smul _ _
    · calc (g : D)⁻¹ • t ((n : ZMod (2 * n)) + 1)
          = (g : D)⁻¹ • ((g : D) • t ((n : ZMod (2 * n)) + 1)) := by rw [hgB.2]
        _ = t ((n : ZMod (2 * n)) + 1) := inv_smul_smul _ _
  let t' : ZMod (2 * n) → V := fun k => (g : D)⁻¹ • t k
  have ht' : IsPolygonApartment Γ n t' := by
    constructor
    · intro a b hab
      have h : t a = t b := by
        have h := congrArg (fun v => (g : D) • v) hab
        simpa [t'] using h
      exact ht.1 h
    · intro k
      have h := (GraphAction.adj_smul (Γ := Γ) (g : D)⁻¹ (t k) (t (k + 1))).mpr (ht.2 k)
      simpa [t'] using h
  obtain ⟨u, hu, huact⟩ := exists_smul_apartment_through_chamber (t := t) (t' := t') ht ht'
    hn hP hT hM (by simpa [t'] using hinv.1) (by simpa [t'] using hinv.2)
  obtain ⟨u', hu'U, hu'val⟩ := baseRootProduct_le_rootU_map (t := t) ht hn hP hT hM hu
  have huD : (u' : D) = u := hu'val
  have hfix : ∀ k : ZMod (2 * n), ((g * u' : ↥(littleGroup D Γ n)) : D) • t k = t k := by
    intro k
    have hu'act : (u' : D) • t k = (g : D)⁻¹ • t k := by
      rw [huD]
      exact huact k
    calc ((g * u' : ↥(littleGroup D Γ n)) : D) • t k
        = (g : D) • ((u' : D) • t k) := by rw [Subgroup.coe_mul, mul_smul]
      _ = (g : D) • ((g : D)⁻¹ • t k) := by rw [hu'act]
      _ = t k := by simp
  have hmemH : (g * u' : ↥(littleGroup D Γ n)) ∈ moufangCartan D Γ n t := by
    rw [moufangCartan_eq_fixingSubgroup (t := t) ht hn hP hT]
    refine Subgroup.mem_subgroupOf.mpr ?_
    exact (mem_fixingSubgroup_iff D).mpr (fun x hx => by
      obtain ⟨k, rfl⟩ := hx
      exact hfix k)
  refine Set.mem_mul.2 ⟨g * u', hmemH, u'⁻¹, ?_, ?_⟩
  · exact rootU (D := D) (Γ := Γ) (n := n) t |>.inv_mem hu'U
  · simp

theorem moufangB_eq_cartan_mul_rootU {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) :
    (moufangB D Γ n t : Set ↥(littleGroup D Γ n)) =
      ((moufangCartan D Γ n t : Subgroup ↥(littleGroup D Γ n)) :
        Set ↥(littleGroup D Γ n)) *
      ((rootU (D := D) (Γ := Γ) (n := n) t) :
        Set ↥(littleGroup D Γ n)) := by
  refine le_antisymm (moufangB_le_cartan_mul_rootU (t := t) ht hn hP hT hM) ?_
  intro x hx
  obtain ⟨h, hh, u, hu, rfl⟩ := Set.mem_mul.1 hx
  exact (moufangB D Γ n t).mul_mem hh.1
    (rootU_le_littleBorel (t := t) ht hn hP hT hM hu)

theorem isSplit_moufangB {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    (hdeg : ∀ v : V, ∃ e : ℕ, Γ.degree v = 2 ^ e + 1) :
    IsSplit (moufangB D Γ n t) (moufangN D Γ n t)
      (rootU (D := D) (Γ := Γ) (n := n) t) := by
  refine ⟨isNilpotent_rootU (t := t) ht hn hP hT hM hdeg, ?_⟩
  simpa [moufangCartan] using
    (moufangB_eq_cartan_mul_rootU (t := t) ht hn hP hT hM)

private theorem coloring_eq_of_connected {c c' : Γ.Coloring (Fin 2)} (hconn : Γ.Connected)
    {v : V} (hv : c v = c' v) : c = c' := by
  refine DFunLike.ext c c' ?_
  intro x
  obtain ⟨p, -, hlen⟩ := hconn.exists_path_of_dist v x
  have h1 := Geometry.GeneralizedPolygons.eq_iff_even_length c p
  have h2 := Geometry.GeneralizedPolygons.eq_iff_even_length c' p
  rw [hlen] at h1 h2
  by_cases hE : Even (Γ.dist v x)
  · calc c x = c v := (h1.mpr hE).symm
      _ = c' v := hv
      _ = c' x := h2.mpr hE
  · have hne1 : c x ≠ c v := by
      intro h
      exact hE (h1.mp h.symm)
    have hne2 : c' x ≠ c' v := by
      intro h
      exact hE (h2.mp h.symm)
    have hv' : (c v).val = (c' v).val := congrArg Fin.val hv
    have hx1 : (c x).val = 1 - (c v).val := by
      have hlt1 : (c x).val < 2 := (c x).isLt
      have hlt2 : (c v).val < 2 := (c v).isLt
      have hneq : (c x).val ≠ (c v).val := fun h => hne1 (Fin.ext h)
      omega
    have hx2 : (c' x).val = 1 - (c' v).val := by
      have hlt1 : (c' x).val < 2 := (c' x).isLt
      have hlt2 : (c' v).val < 2 := (c' v).isLt
      have hneq : (c' x).val ≠ (c' v).val := fun h => hne2 (Fin.ext h)
      omega
    exact Fin.ext (by omega)

theorem preserves_coloring_of_fixes (hconn : Γ.Connected) {c : Γ.Coloring (Fin 2)} {g : D}
    (hG : ∀ a b : V, Γ.Adj (g • a) (g • b) ↔ Γ.Adj a b) {v : V} (hv : g • v = v) :
    ∀ x : V, c (g • x) = c x := by
  let c' : Γ.Coloring (Fin 2) :=
    SimpleGraph.Coloring.mk (fun x => c (g • x)) (fun {a b} hab => c.valid ((hG a b).mpr hab))
  have hc' : c' = c := coloring_eq_of_connected hconn (v := v) (by
    show c (g • v) = c v
    rw [hv])
  intro x
  exact DFunLike.congr_fun hc' x

@[expose] def partsSubgroup (c : Γ.Coloring (Fin 2)) : Subgroup D where
  carrier := {g : D | ∀ x : V, c (g • x) = c x}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro g h hg hh x
    calc c ((g * h) • x) = c (g • (h • x)) := by rw [mul_smul]
      _ = c (h • x) := hg _
      _ = c x := hh x
  inv_mem' := by
    intro g hg x
    have h := hg (g⁻¹ • x)
    simpa using h.symm

theorem pathRootGroup_le_partsSubgroup (hconn : Γ.Connected) {c : Γ.Coloring (Fin 2)}
    {p : GPath Γ n} (hp : p.NoBack) (hn : 2 ≤ n) :
    pathRootGroup D Γ p ≤ partsSubgroup (D := D) c := by
  intro g hg
  change ∀ x : V, c (g • x) = c x
  refine preserves_coloring_of_fixes (D := D) (c := c) (g := g) hconn ?_ (v := p n) ?_
  · intro a b
    exact GraphAction.adj_smul g a b
  · exact MulAction.mem_stabilizer_iff.mp
      (pathRootGroup_le_stabilizer_last (D := D) (Γ := Γ) (n := n) hn (p := p) hg)

theorem littleGroup_le_partsSubgroup (hconn : Γ.Connected) {c : Γ.Coloring (Fin 2)}
    (hn : 2 ≤ n) :
    littleGroup D Γ n ≤ partsSubgroup (D := D) c := by
  rw [littleGroup]
  exact iSup_le fun p => iSup_le fun hp =>
    pathRootGroup_le_partsSubgroup (D := D) (Γ := Γ) (n := n) hconn hp hn

noncomputable def reflOneN (t : ZMod (2 * n) → V) (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    ↥(moufangN D Γ n t) :=
  ⟨⟨reflOne ht hn hP hT hM, reflOne_mem ht hn hP hT hM⟩, by
    rw [mem_moufangN]
    exact MulAction.mem_stabilizer_iff.mp (reflOne_mem_stabilizer ht hn hP hT hM)⟩

noncomputable def reflTwoN (t : ZMod (2 * n) → V) (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    ↥(moufangN D Γ n t) :=
  ⟨⟨reflTwo ht hn hP hT hM, reflTwo_mem ht hn hP hT hM⟩, by
    rw [mem_moufangN]
    exact MulAction.mem_stabilizer_iff.mp (reflTwo_mem_stabilizer ht hn hP hT hM)⟩

@[simp] theorem reflOneN_coe (t : ZMod (2 * n) → V) (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    ((reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM : ↥(moufangN D Γ n t)) :
      ↥(littleGroup D Γ n)) = ⟨reflOne ht hn hP hT hM, reflOne_mem ht hn hP hT hM⟩ := by
  refine Subtype.ext ?_
  rfl

@[simp] theorem reflTwoN_coe (t : ZMod (2 * n) → V) (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    ((reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM : ↥(moufangN D Γ n t)) :
      ↥(littleGroup D Γ n)) = ⟨reflTwo ht hn hP hT hM, reflTwo_mem ht hn hP hT hM⟩ := by
  refine Subtype.ext ?_
  rfl

@[simp] theorem reflOneN_coeD (t : ZMod (2 * n) → V) (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    (reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM : D) =
      reflOne ht hn hP hT hM := by
  change (((reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM :
    ↥(moufangN D Γ n t)) : ↥(littleGroup D Γ n)) : D) = reflOne ht hn hP hT hM
  rw [reflOneN_coe]

@[simp] theorem reflTwoN_coeD (t : ZMod (2 * n) → V) (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    (reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM : D) =
      reflTwo ht hn hP hT hM := by
  change (((reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM :
    ↥(moufangN D Γ n t)) : ↥(littleGroup D Γ n)) : D) = reflTwo ht hn hP hT hM
  rw [reflTwoN_coe]

@[expose] noncomputable def titsW1 (t : ZMod (2 * n) → V) (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) :
    WeylGroup (moufangB D Γ n t) (moufangN D Γ n t) :=
  QuotientGroup.mk (reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM)

@[expose] noncomputable def titsW2 (t : ZMod (2 * n) → V) (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) :
    WeylGroup (moufangB D Γ n t) (moufangN D Γ n t) :=
  QuotientGroup.mk (reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM)

@[simp] theorem titsW1_eq_mk {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM =
      QuotientGroup.mk (reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) := rfl

@[simp] theorem titsW2_eq_mk {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM =
      QuotientGroup.mk (reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) := rfl

theorem reflOneN_smul (t : ZMod (2 * n) → V) (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) (k : ℤ) :
    (reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM : D) • apt t k =
      apt t (2 * ((n : ℤ) + 1) - k) :=
  reflOne_smul ht hn hP hT hM k

theorem reflTwoN_smul (t : ZMod (2 * n) → V) (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) (k : ℤ) :
    (reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM : D) • apt t k =
      apt t (2 * (n : ℤ) - k) :=
  reflTwo_smul ht hn hP hT hM k

@[expose] def aptEdge (t : ZMod (2 * n) → V) (k : ZMod (2 * n)) : Set V :=
  {t k, t (k + 1)}

theorem aptEdge_injective {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n) :
    Function.Injective (aptEdge t) := by
  intro a b h
  have ha : t a ∈ aptEdge t b := by
    rw [← h]
    exact Set.mem_insert_iff.2 (Or.inl rfl)
  have hb : t (a + 1) ∈ aptEdge t b := by
    rw [← h]
    exact Set.mem_insert_of_mem _ rfl
  simp only [aptEdge, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with h0 | h0
  · exact ht.1 h0
  · rcases hb with h1 | h1
    · have e1 : a = b + 1 := ht.1 h0
      have e2 : a + 1 = b := ht.1 h1
      have hb2 : b = b + 2 := by
        calc b = a + 1 := e2.symm
          _ = (b + 1) + 1 := by rw [e1]
          _ = b + 2 := by ring
      have h0eq : b + 0 = b + 2 := by rw [add_zero]; exact hb2
      have htwo : (2 : ZMod (2 * n)) = 0 := (add_left_cancel h0eq).symm
      exact absurd htwo (two_ne_zero_zmod (by omega))
    · have e1 : a = b + 1 := ht.1 h0
      have e2 : a + 1 = b + 1 := ht.1 h1
      have e3 : a = b := add_right_cancel e2
      have hb1 : b = b + 1 := by
        calc b = a := e3.symm
          _ = b + 1 := e1
      have h0eq : b + 0 = b + 1 := by rw [add_zero]; exact hb1
      have hone : (1 : ZMod (2 * n)) = 0 := (add_left_cancel h0eq).symm
      have htwo : (2 : ZMod (2 * n)) = 0 := by
        calc (2 : ZMod (2 * n)) = 1 + 1 := by norm_num
          _ = 0 + 0 := by rw [hone]
          _ = 0 := zero_add 0
      exact absurd htwo (two_ne_zero_zmod (by omega))

abbrev AptEdge (t : ZMod (2 * n) → V) : Type := ↥(Set.range (aptEdge t))

@[expose] def aptEdgeOf (t : ZMod (2 * n) → V) (k : ZMod (2 * n)) : AptEdge t :=
  ⟨aptEdge t k, Set.mem_range_self k⟩

noncomputable def aptEdgeEquiv {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) : ZMod (2 * n) ≃ AptEdge t :=
  Equiv.ofBijective (aptEdgeOf t)
    ⟨fun a b h => aptEdge_injective ht hn (congrArg Subtype.val h), fun e => by
      obtain ⟨k, hk⟩ := Set.mem_range.mp e.2
      exact ⟨k, Subtype.ext hk⟩⟩

theorem card_aptEdge {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n) :
    Nat.card (AptEdge t) = 2 * n := by
  rw [← Nat.card_zmod (2 * n)]
  exact (Nat.card_congr (aptEdgeEquiv (Γ := Γ) ht hn)).symm

theorem exists_aptEdge_smul {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (m : ↥(moufangN D Γ n t))
    (k : ZMod (2 * n)) :
    ∃ k' : ZMod (2 * n), (m : D) • aptEdge t k = aptEdge t k' := by
  classical
  have hmN : (m : D) ∈ MulAction.stabilizer D (Set.range t) := by
    have h : (m.1 : ↥(littleGroup D Γ n)) ∈ moufangN D Γ n t := m.2
    exact mem_moufangN.mp h
  obtain ⟨a, ha⟩ := Set.mem_range.mp
    (smul_mem_range_of_mem_stabilizer (t := t) hmN (Set.mem_range_self (f := t) k))
  obtain ⟨b, hb⟩ := Set.mem_range.mp
    (smul_mem_range_of_mem_stabilizer (t := t) hmN (Set.mem_range_self (f := t) (k + 1)))
  have hadj : Γ.Adj ((m : D) • t k) ((m : D) • t (k + 1)) :=
    (GraphAction.adj_smul (Γ := Γ) (m : D) (t k) (t (k + 1))).mpr (ht.2 k)
  have hadj' : Γ.Adj (t a) (t b) := by
    rw [ha, hb]
    exact hadj
  have hstep : b = a + 1 ∨ b = a - 1 := (apt_adj_iff ht hn hP hT).mp hadj'
  have hset : (m : D) • aptEdge t k = {t a, t b} := by
    rw [aptEdge, Set.smul_set_insert, Set.smul_set_singleton, ha, hb]
  rcases hstep with hb1 | hb1
  · refine ⟨a, ?_⟩
    rw [hset, hb1, aptEdge]
  · refine ⟨a - 1, ?_⟩
    rw [hset, hb1, aptEdge, show a - 1 + 1 = a by ring, Set.pair_comm]

@[expose]
noncomputable def aptEdgeSmul {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (m : ↥(moufangN D Γ n t))
    (e : AptEdge t) : AptEdge t :=
  ⟨(m : D) • e.1, by
    obtain ⟨k, hk⟩ := Set.mem_range.mp e.2
    obtain ⟨k', hk'⟩ := exists_aptEdge_smul (D := D) (Γ := Γ) (n := n) ht hn hP hT m k
    exact ⟨k', by rw [← hk, hk']⟩⟩

@[expose, instance_reducible] noncomputable def aptEdgeMulAction {t : ZMod (2 * n) → V}
    (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n)
    (hT : IsThick Γ) :
    MulAction ↥(moufangN D Γ n t) (AptEdge t) where
  smul := aptEdgeSmul ht hn hP hT
  one_smul e := by
    apply Subtype.ext
    show ((1 : ↥(moufangN D Γ n t)) : D) • e.1 = e.1
    simp
  mul_smul m m' e := by
    apply Subtype.ext
    show (((m * m') : ↥(moufangN D Γ n t)) : D) • e.1 = (m : D) • ((m' : D) • e.1)
    simp only [Subgroup.coe_mul, mul_smul]

private theorem exists_aptRoot_index_Icc {t : ZMod (2 * n) → V} (hn : 1 ≤ n) (k : ℤ) :
    ∃ k' : ℤ, k' ∈ Set.Icc (1 : ℤ) (2 * (n : ℤ)) ∧
      aptRoot D Γ n t k = aptRoot D Γ n t k' := by
  have hpos : (0 : ℤ) < 2 * (n : ℤ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast (Nat.mul_pos (by norm_num) this)
  let q : ℤ := (k - 1) / (2 * (n : ℤ))
  let r : ℤ := (k - 1) % (2 * (n : ℤ))
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hpos.ne'
  have hrlt : r < 2 * (n : ℤ) := Int.emod_lt_of_pos _ hpos
  refine ⟨r + 1, ⟨by omega, by omega⟩, ?_⟩
  have hdec : r + 2 * (n : ℤ) * q = k - 1 := Int.emod_add_mul_ediv (k - 1) (2 * (n : ℤ))
  have hk : k = (r + 1) + 2 * (n : ℤ) * q := by linarith
  rw [hk, aptRoot_add_two_mul]

theorem aptRootGroup_eq_iSup_Icc {t : ZMod (2 * n) → V} (hn : 1 ≤ n) :
    aptRootGroup D Γ n t =
      ⨆ k ∈ Set.Icc (1 : ℤ) (2 * (n : ℤ)), aptRoot D Γ n t k := by
  refine le_antisymm ?_ ?_
  · rw [aptRootGroup]
    refine iSup_le fun k => ?_
    obtain ⟨k', hk', heq⟩ := exists_aptRoot_index_Icc (D := D) (Γ := Γ) (n := n) (t := t) hn k
    rw [heq]
    exact le_iSup₂_of_le k' hk' le_rfl
  · rw [aptRootGroup]
    exact iSup_le fun k => iSup_le fun _ => le_iSup (fun j => aptRoot D Γ n t j) k

theorem iSup_rootD_eq_aptRootGroup {t : ZMod (2 * n) → V} (hn : 3 ≤ n) :
    (⨆ i ∈ {i : ℤ | IsRoot n i}, rootD (D := D) (Γ := Γ) (n := n) t i) =
      aptRootGroup D Γ n t := by
  refine le_antisymm ?_ ?_
  · refine iSup_le fun i => iSup_le fun hi => ?_
    rcases lt_or_ge 0 i with hi0 | hi0
    · rw [rootD_eq_aptRoot_of_pos (t := t) hi0]
      exact aptRoot_le_aptRootGroup i
    · rw [rootD_eq_aptRoot_of_nonpos (t := t) hi0]
      exact aptRoot_le_aptRootGroup ((n : ℤ) - i)
  · rw [aptRootGroup_eq_iSup_Icc (D := D) (Γ := Γ) (n := n) (t := t) (by omega)]
    refine iSup_le fun k => iSup_le fun hk => ?_
    by_cases hkn : k ≤ (n : ℤ)
    · have hk1 : 1 ≤ k := hk.1
      have hi : IsRoot n k := by
        constructor
        · omega
        · have h1 : k.natAbs = k.toNat := by
            have h1z : ((k.natAbs : ℤ)) = k := Int.natAbs_of_nonneg (by omega)
            have h2 : (((k.toNat : ℕ)) : ℤ) = k := Int.toNat_of_nonneg (by omega)
            exact_mod_cast (h1z.trans h2.symm)
          rw [h1]
          omega
      refine le_iSup₂_of_le k hi ?_
      rw [rootD_eq_aptRoot_of_pos (t := t) (by omega)]
    · have hk2 : k ≤ 2 * (n : ℤ) := hk.2
      let i : ℤ := (n : ℤ) - k
      have hi : IsRoot n i := by
        have hi1 : i < 0 := by omega
        have hi2 : -(n : ℤ) ≤ i := by omega
        constructor
        · omega
        · have h1 : i.natAbs = (k - (n : ℤ)).toNat := by
            have h1z : ((i.natAbs : ℤ)) = (((k - (n : ℤ)).toNat : ℕ) : ℤ) := by
              rw [show i = -(k - (n : ℤ)) by omega, Int.natAbs_neg,
                Int.natAbs_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
            exact_mod_cast h1z
          rw [h1]
          have h3 : ((k - (n : ℤ)).toNat : ℤ) = k - (n : ℤ) :=
            Int.toNat_of_nonneg (by omega)
          omega
      refine le_iSup₂_of_le i hi ?_
      rw [rootD_eq_aptRoot_of_nonpos (t := t) (by omega)]
      rw [show (n : ℤ) - i = k by omega]

theorem rootL_closure_eq_top {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    Subgroup.closure (⋃ i ∈ {i : ℤ | IsRoot n i},
      (rootL (D := D) (Γ := Γ) (n := n) t i : Set ↥(littleGroup D Γ n))) = ⊤ := by
  apply Subgroup.map_injective (littleGroup D Γ n).subtype_injective
  rw [Subgroup.map_top]
  have hmap : Subgroup.map (littleGroup D Γ n).subtype
      (Subgroup.closure (⋃ i ∈ {i : ℤ | IsRoot n i},
        (rootL (D := D) (Γ := Γ) (n := n) t i : Set ↥(littleGroup D Γ n)))) =
      Subgroup.closure (⋃ i ∈ {i : ℤ | IsRoot n i},
        (rootD (D := D) (Γ := Γ) (n := n) t i : Set D)) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨y, ⟨i, hi, hyi⟩, rfl⟩
      have hy' : (littleGroup D Γ n).subtype y ∈
          (rootL (D := D) (Γ := Γ) (n := n) t i).map (littleGroup D Γ n).subtype :=
        ⟨y, hyi, rfl⟩
      exact ⟨i, hi, by rwa [rootL_map_subtype ht hn i] at hy'⟩
    · rintro ⟨i, hi, hxi⟩
      refine ⟨⟨x, rootD_le_littleGroup ht (by omega) i hxi⟩, ⟨i, hi, ?_⟩, rfl⟩
      change (⟨x, rootD_le_littleGroup ht (by omega) i hxi⟩ : ↥(littleGroup D Γ n)) ∈
        rootL (D := D) (Γ := Γ) (n := n) t i
      rw [rootL, Subgroup.mem_subgroupOf]
      exact hxi
  rw [hmap, Subgroup.range_subtype]
  have hsub : (⋃ i ∈ {i : ℤ | IsRoot n i},
      (rootD (D := D) (Γ := Γ) (n := n) t i : Set D)) =
      ⋃ x : {i : ℤ // i ∈ {i : ℤ | IsRoot n i}},
        (rootD (D := D) (Γ := Γ) (n := n) t x.1 : Set D) := by
    ext x
    simp only [Set.mem_iUnion, Subtype.exists, exists_prop]
  rw [hsub, ← Subgroup.iSup_eq_closure]
  rw [show (⨆ x : {i : ℤ // i ∈ {i : ℤ | IsRoot n i}},
      rootD (D := D) (Γ := Γ) (n := n) t x.1) =
      ⨆ i ∈ {i : ℤ | IsRoot n i}, rootD (D := D) (Γ := Γ) (n := n) t i by
    rw [iSup_subtype]]
  rw [iSup_rootD_eq_aptRootGroup (D := D) (Γ := Γ) (n := n) (t := t) hn]
  exact aptRootGroup_eq_littleGroup (t := t) ht hn hP hT hM

theorem aptRoot_map_conj_of_reflect {t : ZMod (2 * n) → V} {m : D} {i : ℤ}
    (hm : ∀ k : ℤ, m • apt t k = apt t (2 * i - k)) (j : ℤ) :
    (aptRoot D Γ n t j).map (MulAut.conj m).toMonoidHom =
      aptRoot D Γ n t (2 * i + (n : ℤ) - j) := by
  rw [aptRoot_map_conj (g := m) (t := t) (k := j)]
  refine Subgroup.ext fun x => ?_
  rw [mem_aptRoot, mem_aptRoot]
  constructor
  · intro h i' hi1 hi2 z hz
    have hi1' : 1 ≤ (n : ℤ) - i' := by omega
    have hi2' : (n : ℤ) - i' ≤ (n : ℤ) - 1 := by omega
    refine h ((n : ℤ) - i') hi1' hi2' z ?_
    show Γ.Adj (m • apt t (j + ((n : ℤ) - i'))) z
    rw [hm]
    rw [show 2 * i - (j + ((n : ℤ) - i')) =
      (2 * i + (n : ℤ) - j + i') + 2 * (n : ℤ) * (-1) by ring, apt_add_two_mul]
    exact hz
  · intro h i' hi1 hi2 z hz
    have hi1' : 1 ≤ (n : ℤ) - i' := by omega
    have hi2' : (n : ℤ) - i' ≤ (n : ℤ) - 1 := by omega
    have hz' : Γ.Adj (apt t (2 * i - (j + i'))) z := by
      have hh := hz
      change Γ.Adj (m • apt t (j + i')) z at hh
      rwa [hm] at hh
    refine h ((n : ℤ) - i') hi1' hi2' z ?_
    rw [show 2 * i + (n : ℤ) - j + ((n : ℤ) - i') =
      (2 * i - (j + i')) + 2 * (n : ℤ) * 1 by ring, apt_add_two_mul]
    exact hz'

theorem conjBy_aptRoot_of_map_conj_action {t : ZMod (2 * n) → V} {m : D} {i : ℤ}
    (hm : ∀ j : ℤ, (aptRoot D Γ n t j).map (MulAut.conj m).toMonoidHom =
      aptRoot D Γ n t (2 * i + (n : ℤ) - j)) (j : ℤ) :
    CFSG.GH74.BNPair.conjBy m (aptRoot D Γ n t j) =
      aptRoot D Γ n t (2 * i + (n : ℤ) - j) := by
  unfold CFSG.GH74.BNPair.conjBy
  have h := hm (2 * i + (n : ℤ) - j)
  rw [show 2 * i + (n : ℤ) - (2 * i + (n : ℤ) - j) = j by ring] at h
  rw [← h, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem exists_refl_conj_rootL_neg {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) {j : ℤ} (hj1 : 1 ≤ j) (hjn : j ≤ (n : ℤ)) :
    ∃ m : ↥(littleGroup D Γ n), m ∈ moufangN D Γ n t ∧
      CFSG.GH74.BNPair.conjBy m (rootL (D := D) (Γ := Γ) (n := n) t j) =
        rootL (D := D) (Γ := Γ) (n := n) t (-j) := by
  obtain ⟨m, hmL, hact⟩ :=
    exists_aptReflection (Γ := Γ) (n := n) (t := t) ht hn hP hT hM j
  let mN : ↥(littleGroup D Γ n) := ⟨m, hmL⟩
  have hmN' : mN ∈ moufangN D Γ n t := by
    refine reflection_mem_normalizer (Γ := Γ) (n := n) (t := t) (m := m) (i := j)
      hn hmL ?_
    intro k
    exact hact k
  refine ⟨mN, hmN', ?_⟩
  have hmap := aptRoot_map_conj_of_reflect (Γ := Γ) (n := n) (t := t) (m := m) (i := j) hact
  have hconjD : CFSG.GH74.BNPair.conjBy m
      (rootD (D := D) (Γ := Γ) (n := n) t j) =
      rootD (D := D) (Γ := Γ) (n := n) t (-j) := by
    rw [rootD_eq_aptRoot_of_pos (t := t) (by omega),
      conjBy_aptRoot_of_map_conj_action hmap j,
      rootD_eq_aptRoot_of_nonpos (t := t) (by omega)]
    congr 1
    ring
  exact conjBy_subgroupOf mN (rootD_le_littleGroup ht (by omega) _)
    (rootD_le_littleGroup ht (by omega) _) hconjD

theorem moufangB_sup_moufangN_eq_top {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    moufangB D Γ n t ⊔ moufangN D Γ n t = ⊤ := by
  rw [eq_top_iff]
  rw [← rootL_closure_eq_top (t := t) ht hn hP hT hM]
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hiS, hxi⟩ := Set.mem_iUnion.mp hi
  obtain ⟨hi0, hinabs⟩ := hiS
  by_cases hipos : 0 < i
  · have hi1 : 1 ≤ i := by omega
    have hin : i ≤ (n : ℤ) := by
      have hcast : ((i.natAbs : ℕ) : ℤ) = i := Int.natAbs_of_nonneg (by omega)
      have hle : ((i.natAbs : ℕ) : ℤ) ≤ (n : ℤ) := by exact_mod_cast hinabs
      omega
    have hle : rootL (D := D) (Γ := Γ) (n := n) t i ≤ moufangB D Γ n t :=
      rootL_le_littleBorel (t := t) ht hn hi1 hin
    exact (hle.trans le_sup_left) hxi
  · have hineg : i < 0 := by omega
    let j : ℤ := -i
    have hj1 : 1 ≤ j := by omega
    have hjn : j ≤ (n : ℤ) := by
      have h1 : j.natAbs = i.natAbs := by
        rw [show j = -i by omega, Int.natAbs_neg]
      have hle : ((j.natAbs : ℕ) : ℤ) ≤ (n : ℤ) := by
        rw [h1]
        exact_mod_cast hinabs
      have hcast : ((j.natAbs : ℕ) : ℤ) = j := Int.natAbs_of_nonneg (by omega)
      omega
    obtain ⟨m, hmN, hconj⟩ := exists_refl_conj_rootL_neg (t := t) ht hn hP hT hM hj1 hjn
    have hconj' : CFSG.GH74.BNPair.conjBy m (rootL (D := D) (Γ := Γ) (n := n) t j) =
        rootL (D := D) (Γ := Γ) (n := n) t i := by
      rw [hconj]
      congr 1
      show -j = i
      omega
    have hrootj : rootL (D := D) (Γ := Γ) (n := n) t j ≤ moufangB D Γ n t :=
      rootL_le_littleBorel (t := t) ht hn hj1 hjn
    have hmS : m ∈ moufangB D Γ n t ⊔ moufangN D Γ n t :=
      (le_sup_right : moufangN D Γ n t ≤ moufangB D Γ n t ⊔ moufangN D Γ n t) hmN
    have him : m⁻¹ ∈ moufangB D Γ n t ⊔ moufangN D Γ n t := Subgroup.inv_mem _ hmS
    have hconjle : CFSG.GH74.BNPair.conjBy m (rootL (D := D) (Γ := Γ) (n := n) t j) ≤
        moufangB D Γ n t ⊔ moufangN D Γ n t := by
      intro y hy
      rw [CFSG.GH74.BNPair.mem_conjBy_iff] at hy
      have h1 : m * y * m⁻¹ ∈ moufangB D Γ n t ⊔ moufangN D Γ n t :=
        (hrootj.trans le_sup_left) hy
      have hy_eq : y = m⁻¹ * (m * y * m⁻¹) * m := by group
      rw [hy_eq]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ him h1) hmS
    rw [← hconj'] at hxi
    exact hconjle hxi

theorem reflOneN_sq_mem_cartan {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) :
    reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
        reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM ∈
      cartan (moufangB D Γ n t) (moufangN D Γ n t) := by
  rw [cartan, Subgroup.mem_subgroupOf]
  have hval : (((reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
      reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM :
      ↥(moufangN D Γ n t)) : ↥(littleGroup D Γ n))) =
      (⟨reflOne ht hn hP hT hM * reflOne ht hn hP hT hM, by
        exact (littleGroup D Γ n).mul_mem (reflOne_mem ht hn hP hT hM)
          (reflOne_mem ht hn hP hT hM)⟩ : ↥(littleGroup D Γ n)) := by
    apply Subtype.ext
    rfl
  rw [hval]
  have hfix : reflOne ht hn hP hT hM * reflOne ht hn hP hT hM ∈
      fixingSubgroup D (Set.range t) := reflOne_sq_fix ht hn hP hT hM
  have hmem : (⟨reflOne ht hn hP hT hM * reflOne ht hn hP hT hM, by
      exact (littleGroup D Γ n).mul_mem (reflOne_mem ht hn hP hT hM)
        (reflOne_mem ht hn hP hT hM)⟩ : ↥(littleGroup D Γ n)) ∈
      moufangB D Γ n t ⊓ moufangN D Γ n t :=
    mem_moufangB_inf_moufangN_of_fix hfix
  simpa [moufangB, moufangN] using hmem

theorem reflTwoN_sq_mem_cartan {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) :
    reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
        reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM ∈
      cartan (moufangB D Γ n t) (moufangN D Γ n t) := by
  rw [cartan, Subgroup.mem_subgroupOf]
  have hval : (((reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
      reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM :
      ↥(moufangN D Γ n t)) : ↥(littleGroup D Γ n))) =
      (⟨reflTwo ht hn hP hT hM * reflTwo ht hn hP hT hM, by
        exact (littleGroup D Γ n).mul_mem (reflTwo_mem ht hn hP hT hM)
          (reflTwo_mem ht hn hP hT hM)⟩ : ↥(littleGroup D Γ n)) := by
    apply Subtype.ext
    rfl
  rw [hval]
  have hfix : reflTwo ht hn hP hT hM * reflTwo ht hn hP hT hM ∈
      fixingSubgroup D (Set.range t) := reflTwo_sq_fix ht hn hP hT hM
  have hmem : (⟨reflTwo ht hn hP hT hM * reflTwo ht hn hP hT hM, by
      exact (littleGroup D Γ n).mul_mem (reflTwo_mem ht hn hP hT hM)
        (reflTwo_mem ht hn hP hT hM)⟩ : ↥(littleGroup D Γ n)) ∈
      moufangB D Γ n t ⊓ moufangN D Γ n t :=
    mem_moufangB_inf_moufangN_of_fix hfix
  simpa [moufangB, moufangN] using hmem

theorem reflOneN_not_mem_cartan {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) :
    reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM ∉
      cartan (moufangB D Γ n t) (moufangN D Γ n t) := by
  intro h
  rw [cartan, Subgroup.mem_subgroupOf] at h
  have hmem : (⟨reflOne ht hn hP hT hM, reflOne_mem ht hn hP hT hM⟩ :
      ↥(littleGroup D Γ n)) ∈ moufangB D Γ n t ⊓ moufangN D Γ n t := by
    simpa [moufangB, moufangN] using h
  exact reflOne_not_fix ht hn hP hT hM (moufangB_inf_moufangN_fix ht hn hP hT hmem)

theorem reflTwoN_not_mem_cartan {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) :
    reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM ∉
      cartan (moufangB D Γ n t) (moufangN D Γ n t) := by
  intro h
  rw [cartan, Subgroup.mem_subgroupOf] at h
  have hmem : (⟨reflTwo ht hn hP hT hM, reflTwo_mem ht hn hP hT hM⟩ :
      ↥(littleGroup D Γ n)) ∈ moufangB D Γ n t ⊓ moufangN D Γ n t := by
    simpa [moufangB, moufangN] using h
  exact reflTwo_not_fix ht hn hP hT hM (by
    have hfix := moufangB_inf_moufangN_fix ht hn hP hT hmem
    simpa using hfix)

theorem reflTwo_inv_smul {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) (k : ℤ) :
    (reflTwo ht hn hP hT hM)⁻¹ • apt t k = apt t (2 * (n : ℤ) - k) := by
  have h := reflTwo_smul (t := t) ht hn hP hT hM (2 * (n : ℤ) - k)
  rw [show 2 * (n : ℤ) - (2 * (n : ℤ) - k) = k by ring] at h
  rw [← h]
  simp

theorem reflOne_inv_smul {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) (k : ℤ) :
    (reflOne ht hn hP hT hM)⁻¹ • apt t k = apt t (2 * ((n : ℤ) + 1) - k) := by
  have h := reflOne_smul (t := t) ht hn hP hT hM (2 * ((n : ℤ) + 1) - k)
  rw [show 2 * ((n : ℤ) + 1) - (2 * ((n : ℤ) + 1) - k) = k by ring] at h
  rw [← h]
  simp

theorem titsW1_sq {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    [(cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal] :
    titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
        titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM = 1 := by
  change QuotientGroup.mk (reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) *
      QuotientGroup.mk (reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) = 1
  rw [← QuotientGroup.mk_mul]
  exact (QuotientGroup.eq_one_iff _).mpr (reflOneN_sq_mem_cartan (t := t) ht hn hP hT hM)

theorem titsW2_sq {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    [(cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal] :
    titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
        titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM = 1 := by
  change QuotientGroup.mk (reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) *
      QuotientGroup.mk (reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) = 1
  rw [← QuotientGroup.mk_mul]
  exact (QuotientGroup.eq_one_iff _).mpr (reflTwoN_sq_mem_cartan (t := t) ht hn hP hT hM)

theorem titsW1_ne_one {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    [(cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal] :
    titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM ≠ 1 := by
  intro h
  change QuotientGroup.mk (reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) = 1 at h
  exact reflOneN_not_mem_cartan (t := t) ht hn hP hT hM ((QuotientGroup.eq_one_iff _).mp h)

theorem titsW2_ne_one {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    [(cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal] :
    titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM ≠ 1 := by
  intro h
  change QuotientGroup.mk (reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) = 1 at h
  exact reflTwoN_not_mem_cartan (t := t) ht hn hP hT hM ((QuotientGroup.eq_one_iff _).mp h)

theorem orderOf_titsW1 {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    [(cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal] :
    orderOf (titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ (titsW1_ne_one (t := t) ht hn hP hT hM)
  simpa [pow_two] using titsW1_sq (t := t) ht hn hP hT hM

theorem orderOf_titsW2 {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    [(cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal] :
    orderOf (titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ (titsW2_ne_one (t := t) ht hn hP hT hM)
  simpa [pow_two] using titsW2_sq (t := t) ht hn hP hT hM

theorem titsW1_ne_titsW2 {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    [(cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal] :
    titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM ≠
      titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM := by
  intro h
  have hquot : QuotientGroup.mk (reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) =
      QuotientGroup.mk (reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) := h
  have hmem : reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
      (reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM)⁻¹ ∈
      cartan (moufangB D Γ n t) (moufangN D Γ n t) := by
    have h' : QuotientGroup.mk (s := cartan (moufangB D Γ n t) (moufangN D Γ n t))
        (reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
        (reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM)⁻¹) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hquot, mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff (N := cartan (moufangB D Γ n t) (moufangN D Γ n t)) _).mp h'
  have hmemL : (((reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
      (reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM)⁻¹ :
      ↥(moufangN D Γ n t)) : ↥(littleGroup D Γ n))) ∈
      moufangB D Γ n t ⊓ moufangN D Γ n t :=
    (Subgroup.mem_subgroupOf).mp hmem
  have hmem' : (((reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
      (reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM)⁻¹ :
      ↥(moufangN D Γ n t)) : ↥(littleGroup D Γ n))) ∈
      moufangB D Γ n t ⊓ moufangN D Γ n t := by
    simpa [moufangB, moufangN] using hmemL
  have hfix := moufangB_inf_moufangN_fix ht hn hP hT hmem'
  have hfixn : (((reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
      (reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM)⁻¹ :
      ↥(moufangN D Γ n t)) : D)) • apt t (n : ℤ) = apt t (n : ℤ) :=
    (mem_fixingSubgroup_iff D).mp hfix (apt t (n : ℤ)) (Set.mem_range_self (f := t) (n : ℤ))
  have hact : (((reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
      (reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM)⁻¹ :
      ↥(moufangN D Γ n t)) : D)) • apt t (n : ℤ) = apt t ((n : ℤ) + 2) := by
    have hco : (((reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
        (reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM)⁻¹ :
        ↥(moufangN D Γ n t)) : D)) =
        (reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM : D) *
          (reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM : D)⁻¹ := rfl
    rw [hco, mul_smul, reflTwoN_coeD, reflOneN_coeD,
      reflTwo_inv_smul (t := t) ht hn hP hT hM,
      reflOne_smul (t := t) ht hn hP hT hM]
    congr 1
    ring
  rw [hact] at hfixn
  have hne : apt t (n : ℤ) ≠ apt t ((n : ℤ) + 2) :=
    apt_ne_two (by omega : 2 ≤ n) ht (n : ℤ)
  exact hne hfixn.symm

private theorem apt_val_zmod {t : ZMod (2 * n) → V} (hn : 3 ≤ n) (k : ZMod (2 * n)) :
    apt t (k.val : ℤ) = t k := by
  haveI : NeZero (2 * n) := ⟨by omega⟩
  show t (((k.val : ℤ) : ZMod (2 * n))) = t k
  congr 1
  push_cast
  rw [ZMod.natCast_zmod_val]

theorem reflOne_mul_reflTwo_smul_zmod {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) (k : ZMod (2 * n)) :
    (reflOne ht hn hP hT hM * reflTwo ht hn hP hT hM) • t k = t (k + 2) := by
  haveI : NeZero (2 * n) := ⟨by omega⟩
  have hcast : (((k.val : ℤ) + 2 : ℤ) : ZMod (2 * n)) = k + 2 := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  calc (reflOne ht hn hP hT hM * reflTwo ht hn hP hT hM) • t k
      = (reflOne ht hn hP hT hM * reflTwo ht hn hP hT hM) • apt t (k.val : ℤ) := by
        rw [apt_val_zmod (t := t) hn]
    _ = apt t ((k.val : ℤ) + 2) := reflOne_mul_reflTwo_smul (t := t) ht hn hP hT hM (k.val : ℤ)
    _ = t (k + 2) := by
        show t ((((k.val : ℤ) + 2 : ℤ) : ZMod (2 * n))) = t (k + 2)
        rw [hcast]

theorem reflOneN_mul_reflTwoN_smul_zmod {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) (k : ZMod (2 * n)) :
    (((reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
      reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) : ↥(moufangN D Γ n t)) : D) •
        t k = t (k + 2) := by
  have hco : (((reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
      reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) : ↥(moufangN D Γ n t)) : D) =
      reflOne ht hn hP hT hM * reflTwo ht hn hP hT hM := by
    change (((reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM : ↥(moufangN D Γ n t)) :
      ↥(littleGroup D Γ n)) * ((reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM :
      ↥(moufangN D Γ n t)) : ↥(littleGroup D Γ n)) : D) = _
    rw [reflOneN_coe, reflTwoN_coe]
  rw [hco]
  exact reflOne_mul_reflTwo_smul_zmod (t := t) ht hn hP hT hM k

theorem reflOneN_smul_zmod {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) (k : ZMod (2 * n)) :
    ((reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM : ↥(moufangN D Γ n t)) : D) •
        t k = t (2 * ((n : ZMod (2 * n)) + 1) - k) := by
  haveI : NeZero (2 * n) := ⟨by omega⟩
  have hcast : ((2 * ((n : ℤ) + 1) - (k.val : ℤ) : ℤ) : ZMod (2 * n)) =
      2 * ((n : ZMod (2 * n)) + 1) - k := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  calc ((reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM : ↥(moufangN D Γ n t)) : D) • t k
      = (reflOne ht hn hP hT hM) • apt t (k.val : ℤ) := by
        rw [reflOneN_coeD, apt_val_zmod (t := t) hn]
    _ = apt t (2 * ((n : ℤ) + 1) - (k.val : ℤ)) :=
        reflOne_smul (t := t) ht hn hP hT hM (k.val : ℤ)
    _ = t (2 * ((n : ZMod (2 * n)) + 1) - k) := by
        show t ((((2 * ((n : ℤ) + 1) - (k.val : ℤ) : ℤ)) : ZMod (2 * n))) = _
        rw [hcast]

theorem reflOneN_mul_reflTwoN_smul_aptEdge {t : ZMod (2 * n) → V}
    (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n)
    (hT : IsThick Γ) (hM : MoufangCondition D Γ n) (k : ZMod (2 * n)) :
    (((reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
      reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) : ↥(moufangN D Γ n t)) : D) •
        aptEdge t k = aptEdge t (k + 2) := by
  rw [aptEdge, Set.smul_set_insert, Set.smul_set_singleton,
    reflOneN_mul_reflTwoN_smul_zmod (t := t) ht hn hP hT hM k,
    reflOneN_mul_reflTwoN_smul_zmod (t := t) ht hn hP hT hM (k + 1)]
  rw [aptEdge, show k + 1 + 2 = k + 2 + 1 by ring]

theorem reflOneN_smul_aptEdge {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) (k : ZMod (2 * n)) :
    ((reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM : ↥(moufangN D Γ n t)) : D) •
        aptEdge t k = aptEdge t (2 * ((n : ZMod (2 * n)) + 1) - k - 1) := by
  let A : ZMod (2 * n) := 2 * ((n : ZMod (2 * n)) + 1) - k
  have hA : 2 * ((n : ZMod (2 * n)) + 1) - (k + 1) = A - 1 := by
    dsimp [A]
    ring
  have hset : ((reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM :
      ↥(moufangN D Γ n t)) : D) • aptEdge t k = {t A, t (A - 1)} := by
    rw [aptEdge, Set.smul_set_insert, Set.smul_set_singleton,
      reflOneN_smul_zmod (t := t) ht hn hP hT hM k,
      reflOneN_smul_zmod (t := t) ht hn hP hT hM (k + 1), hA]
  rw [hset, show 2 * ((n : ZMod (2 * n)) + 1) - k - 1 = A - 1 by rfl, aptEdge,
    show A - 1 + 1 = A by ring, Set.pair_comm]

theorem pow_reflOneN_mul_reflTwoN_smul_aptEdge {t : ZMod (2 * n) → V}
    (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n)
    (hT : IsThick Γ) (hM : MoufangCondition D Γ n) (j : ℕ) (k : ZMod (2 * n)) :
    ((((reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
      reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) ^ j :
      ↥(moufangN D Γ n t)) : D)) • aptEdge t k =
      aptEdge t (k + 2 * (j : ZMod (2 * n))) := by
  induction j generalizing k with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Subgroup.coe_mul, Subgroup.coe_mul, mul_smul,
      reflOneN_mul_reflTwoN_smul_aptEdge (t := t) ht hn hP hT hM, ih]
    congr 1
    push_cast
    ring

theorem reflOneN_smul_rot_edge {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) (j : ℕ) :
    ((reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM : ↥(moufangN D Γ n t)) : D) •
        ((((reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
          reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) ^ j :
          ↥(moufangN D Γ n t)) : D) • aptEdge t (n : ZMod (2 * n))) =
      aptEdge t (2 * ((n : ZMod (2 * n)) + 1) -
        ((n : ZMod (2 * n)) + 2 * (j : ZMod (2 * n))) - 1) := by
  rw [pow_reflOneN_mul_reflTwoN_smul_aptEdge (t := t) ht hn hP hT hM j
      (n : ZMod (2 * n)), reflOneN_smul_aptEdge (t := t) ht hn hP hT hM]

section EdgeOrbit

variable {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
  (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)

theorem stabilizer_aptEdge_base_eq_cartan :
    letI : MulAction ↥(moufangN D Γ n t) (AptEdge t) := aptEdgeMulAction ht hn hP hT
    MulAction.stabilizer ↥(moufangN D Γ n t) (aptEdgeOf t (n : ZMod (2 * n))) =
      cartan (moufangB D Γ n t) (moufangN D Γ n t) := by
  letI : MulAction ↥(moufangN D Γ n t) (AptEdge t) := aptEdgeMulAction ht hn hP hT
  classical
  obtain ⟨c⟩ := hP.isBipartite
  have hparts : littleGroup D Γ n ≤ partsSubgroup (D := D) c :=
    littleGroup_le_partsSubgroup (D := D) (Γ := Γ) (n := n) hP.connected (by omega)
  ext m
  constructor
  · intro hm
    rw [MulAction.mem_stabilizer_iff] at hm
    have hval : (m : D) • aptEdge t (n : ZMod (2 * n)) = aptEdge t (n : ZMod (2 * n)) :=
      congrArg Subtype.val hm
    have hcn : c ((m : D) • t (n : ZMod (2 * n))) = c (t (n : ZMod (2 * n))) :=
      hparts m.1.2 (t (n : ZMod (2 * n)))
    have hmem1 : (m : D) • t (n : ZMod (2 * n)) ∈ aptEdge t (n : ZMod (2 * n)) := by
      rw [← hval]
      exact Set.smul_mem_smul_set (a := (m : D)) (Set.mem_insert_iff.2 (Or.inl rfl))
    have hmem2 : (m : D) • t ((n : ZMod (2 * n)) + 1) ∈ aptEdge t (n : ZMod (2 * n)) := by
      rw [← hval]
      exact Set.smul_mem_smul_set (a := (m : D)) (Set.mem_insert_of_mem _ rfl)
    have hfix1 : (m : D) • t (n : ZMod (2 * n)) = t (n : ZMod (2 * n)) := by
      rw [aptEdge, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem1
      rcases hmem1 with h | h
      · exact h
      · exfalso
        have hadj : Γ.Adj (t (n : ZMod (2 * n))) (t ((n : ZMod (2 * n)) + 1)) := ht.2 _
        exact c.valid hadj (by rw [h] at hcn; exact hcn.symm)
    have hfix2 : (m : D) • t ((n : ZMod (2 * n)) + 1) = t ((n : ZMod (2 * n)) + 1) := by
      rw [aptEdge, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem2
      rcases hmem2 with h | h
      · exfalso
        have hc' : c ((m : D) • t ((n : ZMod (2 * n)) + 1)) =
            c (t ((n : ZMod (2 * n)) + 1)) := hparts m.1.2 _
        have hadj : Γ.Adj (t (n : ZMod (2 * n))) (t ((n : ZMod (2 * n)) + 1)) := ht.2 _
        exact c.valid hadj (by rw [h] at hc'; exact hc')
      · exact h
    rw [cartan, Subgroup.mem_subgroupOf]
    have hB : m.1 ∈ moufangB D Γ n t := by
      rw [mem_moufangB]
      exact ⟨hfix1, hfix2⟩
    have hN : m.1 ∈ moufangN D Γ n t := m.2
    simpa [moufangB, moufangN] using ⟨hB, hN⟩
  · intro hm
    rw [cartan, Subgroup.mem_subgroupOf] at hm
    have hmB : m.1 ∈ moufangB D Γ n t := by
      have h := hm.1
      rwa [moufangB] at h
    have hfix := mem_moufangB.mp hmB
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    show (m : D) • aptEdge t (n : ZMod (2 * n)) = aptEdge t (n : ZMod (2 * n))
    rw [aptEdge, Set.smul_set_insert, Set.smul_set_singleton, hfix.1, hfix.2]

private theorem two_mul_zmod_inj {j j' : ℕ} (hj : j < n) (hj' : j' < n)
    (h : 2 * (j : ZMod (2 * n)) = 2 * (j' : ZMod (2 * n))) : j = j' := by
  have hcast : ((2 * j : ℕ) : ZMod (2 * n)) = 2 * (j : ZMod (2 * n)) := by
    push_cast
    ring
  have hcast' : ((2 * j' : ℕ) : ZMod (2 * n)) = 2 * (j' : ZMod (2 * n)) := by
    push_cast
    ring
  have heq : ((2 * j : ℕ) : ZMod (2 * n)) = ((2 * j' : ℕ) : ZMod (2 * n)) := by
    rw [hcast, hcast']
    exact h
  have hmod := (ZMod.natCast_eq_natCast_iff (2 * j) (2 * j') (2 * n)).mp heq
  have hlt : 2 * j < 2 * n := by omega
  have hlt' : 2 * j' < 2 * n := by omega
  have hjeq : 2 * j = 2 * j' := hmod.eq_of_lt_of_lt hlt hlt'
  omega

theorem card_orbit_aptEdge_base (hM : MoufangCondition D Γ n) :
    letI : MulAction ↥(moufangN D Γ n t) (AptEdge t) := aptEdgeMulAction ht hn hP hT
    (MulAction.orbit ↥(moufangN D Γ n t) (aptEdgeOf t (n : ZMod (2 * n)))).ncard = 2 * n := by
  letI : MulAction ↥(moufangN D Γ n t) (AptEdge t) := aptEdgeMulAction ht hn hP hT
  classical
  let rN : ↥(moufangN D Γ n t) :=
    reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
      reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM
  let sN : ↥(moufangN D Γ n t) := reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM
  let rotEdge : ℕ → AptEdge t := fun j =>
    aptEdgeOf t ((n : ZMod (2 * n)) + 2 * (j : ZMod (2 * n)))
  let reflEdge : ℕ → AptEdge t := fun j =>
    aptEdgeOf t (2 * ((n : ZMod (2 * n)) + 1) -
      ((n : ZMod (2 * n)) + 2 * (j : ZMod (2 * n))) - 1)
  let A : Finset (AptEdge t) := (Finset.range n).image rotEdge
  let B : Finset (AptEdge t) := (Finset.range n).image reflEdge
  have hrot_inj : Set.InjOn rotEdge ↑(Finset.range n) := by
    intro j hj j' hj' h
    simp only [Finset.coe_range, Set.mem_Iio] at hj hj'
    have hidx : (n : ZMod (2 * n)) + 2 * (j : ZMod (2 * n)) =
        (n : ZMod (2 * n)) + 2 * (j' : ZMod (2 * n)) :=
      aptEdge_injective ht hn (congrArg Subtype.val h)
    exact two_mul_zmod_inj hj hj' (add_left_cancel hidx)
  have hrefl_inj : Set.InjOn reflEdge ↑(Finset.range n) := by
    intro j hj j' hj' h
    simp only [Finset.coe_range, Set.mem_Iio] at hj hj'
    have hidx : (n : ZMod (2 * n)) + 1 - 2 * (j : ZMod (2 * n)) =
        (n : ZMod (2 * n)) + 1 - 2 * (j' : ZMod (2 * n)) := by
      have h' := aptEdge_injective ht hn (congrArg Subtype.val h)
      rw [show 2 * ((n : ZMod (2 * n)) + 1) -
          ((n : ZMod (2 * n)) + 2 * (j : ZMod (2 * n))) - 1 =
          (n : ZMod (2 * n)) + 1 - 2 * (j : ZMod (2 * n)) by ring,
        show 2 * ((n : ZMod (2 * n)) + 1) -
          ((n : ZMod (2 * n)) + 2 * (j' : ZMod (2 * n))) - 1 =
          (n : ZMod (2 * n)) + 1 - 2 * (j' : ZMod (2 * n)) by ring] at h'
      exact h'
    exact two_mul_zmod_inj hj hj' (sub_right_inj.mp hidx)
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    dsimp [A] at hxA
    dsimp [B] at hxB
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hxA
    obtain ⟨j, hj, hBj⟩ := Finset.mem_image.mp hxB
    have hidx : (n : ZMod (2 * n)) + 2 * (i : ZMod (2 * n)) =
        (n : ZMod (2 * n)) + 1 - 2 * (j : ZMod (2 * n)) := by
      have h' := aptEdge_injective ht hn (congrArg Subtype.val hBj)
      rw [show 2 * ((n : ZMod (2 * n)) + 1) -
          ((n : ZMod (2 * n)) + 2 * (j : ZMod (2 * n))) - 1 =
          (n : ZMod (2 * n)) + 1 - 2 * (j : ZMod (2 * n)) by ring] at h'
      exact h'.symm
    have htwo : 2 * ((i + j : ℕ) : ZMod (2 * n)) = 1 := by
      have h' : 2 * (i : ZMod (2 * n)) + 2 * (j : ZMod (2 * n)) = 1 := by
        have h3 : (n : ZMod (2 * n)) + (2 * (i : ZMod (2 * n)) + 2 * (j : ZMod (2 * n))) =
            (n : ZMod (2 * n)) + 1 := by
          calc (n : ZMod (2 * n)) + (2 * (i : ZMod (2 * n)) + 2 * (j : ZMod (2 * n)))
              = ((n : ZMod (2 * n)) + 2 * (i : ZMod (2 * n))) +
                  2 * (j : ZMod (2 * n)) := by ring
            _ = ((n : ZMod (2 * n)) + 1 - 2 * (j : ZMod (2 * n))) +
                  2 * (j : ZMod (2 * n)) := by rw [hidx]
            _ = (n : ZMod (2 * n)) + 1 := by ring
        exact add_left_cancel h3
      calc 2 * ((i + j : ℕ) : ZMod (2 * n))
          = 2 * (i : ZMod (2 * n)) + 2 * (j : ZMod (2 * n)) := by push_cast; ring
        _ = 1 := h'
    have htwo' : ((2 * (i + j) : ℕ) : ZMod (2 * n)) = ((1 : ℕ) : ZMod (2 * n)) := by
      simpa using htwo
    have hmod : (2 * (i + j)) ≡ 1 [MOD 2 * n] :=
      (ZMod.natCast_eq_natCast_iff (2 * (i + j)) 1 (2 * n)).mp htwo'
    have hmod2 : (2 * (i + j)) ≡ 1 [MOD 2] :=
      Nat.ModEq.of_dvd (by omega : 2 ∣ 2 * n) hmod
    have h0 : (2 * (i + j)) % 2 = 1 % 2 := hmod2
    simp at h0
  have hAcard : A.card = n := by
    dsimp [A]
    rw [Finset.card_image_of_injOn hrot_inj]
    simp
  have hBcard : B.card = n := by
    dsimp [B]
    rw [Finset.card_image_of_injOn hrefl_inj]
    simp
  have hunion : (A ∪ B).card = 2 * n := by
    rw [Finset.card_union_of_disjoint hdisj, hAcard, hBcard]
    omega
  let orbit := MulAction.orbit ↥(moufangN D Γ n t) (aptEdgeOf t (n : ZMod (2 * n)))
  have hsubA : (A : Set (AptEdge t)) ⊆ orbit := by
    intro e he
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he
    refine ⟨rN ^ j, ?_⟩
    apply Subtype.ext
    change (((rN ^ j : ↥(moufangN D Γ n t)) : D)) • aptEdge t (n : ZMod (2 * n)) =
      aptEdge t ((n : ZMod (2 * n)) + 2 * (j : ZMod (2 * n)))
    exact pow_reflOneN_mul_reflTwoN_smul_aptEdge (t := t) ht hn hP hT hM j
      (n : ZMod (2 * n))
  have hsubB : (B : Set (AptEdge t)) ⊆ orbit := by
    intro e he
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he
    refine ⟨sN * rN ^ j, ?_⟩
    apply Subtype.ext
    change ((((sN * rN ^ j) : ↥(moufangN D Γ n t)) : D)) • aptEdge t (n : ZMod (2 * n)) =
      aptEdge t (2 * ((n : ZMod (2 * n)) + 1) -
        ((n : ZMod (2 * n)) + 2 * (j : ZMod (2 * n))) - 1)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, mul_smul]
    dsimp [sN, rN]
    exact reflOneN_smul_rot_edge (t := t) ht hn hP hT hM j
  have hge : 2 * n ≤ orbit.ncard := by
    rw [← hunion, ← Set.ncard_coe_finset (A ∪ B)]
    refine Set.ncard_le_ncard ?_
    intro x hx
    rw [Finset.mem_coe] at hx
    rcases Finset.mem_union.mp hx with hxA | hxB
    · exact hsubA hxA
    · exact hsubB hxB
  have hle : orbit.ncard ≤ 2 * n := by
    rw [← card_aptEdge (Γ := Γ) (t := t) ht hn, ← Set.ncard_univ (AptEdge t)]
    exact Set.ncard_le_ncard (Set.subset_univ _)
  exact le_antisymm hle hge

end EdgeOrbit

theorem card_weyl_tits {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    Nat.card (WeylGroup (moufangB D Γ n t) (moufangN D Γ n t)) = 2 * n := by
  letI : MulAction ↥(moufangN D Γ n t) (AptEdge t) := aptEdgeMulAction ht hn hP hT
  have hidx : (cartan (moufangB D Γ n t) (moufangN D Γ n t)).index = 2 * n := by
    rw [← stabilizer_aptEdge_base_eq_cartan (t := t) ht hn hP hT]
    rw [MulAction.index_stabilizer]
    exact card_orbit_aptEdge_base (t := t) ht hn hP hT hM
  exact hidx

noncomputable def edgeOfW {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) :
    WeylGroup (moufangB D Γ n t) (moufangN D Γ n t) → AptEdge t := by
  letI : MulAction ↥(moufangN D Γ n t) (AptEdge t) := aptEdgeMulAction ht hn hP hT
  intro w
  refine Quotient.liftOn w (fun m : ↥(moufangN D Γ n t) =>
    m • aptEdgeOf t (n : ZMod (2 * n))) ?_
  intro m m' hrel
  have hH : m⁻¹ * m' ∈ cartan (moufangB D Γ n t) (moufangN D Γ n t) :=
    (QuotientGroup.leftRel_apply).mp hrel
  have hstab : m⁻¹ * m' ∈ MulAction.stabilizer ↥(moufangN D Γ n t)
      (aptEdgeOf t (n : ZMod (2 * n))) := by
    rw [stabilizer_aptEdge_base_eq_cartan (t := t) ht hn hP hT]
    exact hH
  rw [MulAction.mem_stabilizer_iff] at hstab
  have hm : m' = m * (m⁻¹ * m') := by group
  rw [hm, mul_smul, hstab]

theorem edgeOfW_mk {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (m : ↥(moufangN D Γ n t)) :
    letI : MulAction ↥(moufangN D Γ n t) (AptEdge t) := aptEdgeMulAction ht hn hP hT
    edgeOfW ht hn hP hT (QuotientGroup.mk m) =
      m • aptEdgeOf t (n : ZMod (2 * n)) := by
  letI : MulAction ↥(moufangN D Γ n t) (AptEdge t) := aptEdgeMulAction ht hn hP hT
  rw [edgeOfW]
  exact Quotient.liftOn_mk _ _ m

theorem edgeOfW_rot_pow {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    [(cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal] (j : ℕ) :
    edgeOfW ht hn hP hT
        ((titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
          titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) ^ j) =
      aptEdgeOf t ((n : ZMod (2 * n)) + 2 * (j : ZMod (2 * n))) := by
  have hr : titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
      titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM =
      QuotientGroup.mk (reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
        reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) := rfl
  have hpow' : (titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
      titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) ^ j =
      QuotientGroup.mk ((reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
        reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) ^ j) := by
    rw [hr, ← QuotientGroup.mk_pow]
  rw [hpow', edgeOfW_mk]
  apply Subtype.ext
  change (((reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
      reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) ^ j :
      ↥(moufangN D Γ n t)) : D) • aptEdge t (n : ZMod (2 * n)) =
    aptEdge t ((n : ZMod (2 * n)) + 2 * (j : ZMod (2 * n)))
  exact pow_reflOneN_mul_reflTwoN_smul_aptEdge (t := t) ht hn hP hT hM j
    (n : ZMod (2 * n))

theorem edgeOfW_refl_pow {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    [(cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal] (j : ℕ) :
    edgeOfW ht hn hP hT
        (titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
          (titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
            titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) ^ j) =
      aptEdgeOf t (2 * ((n : ZMod (2 * n)) + 1) -
        ((n : ZMod (2 * n)) + 2 * (j : ZMod (2 * n))) - 1) := by
  have hr : titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM =
      QuotientGroup.mk (reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) := rfl
  have hpow : (titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
      titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) ^ j =
      QuotientGroup.mk ((reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
        reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) ^ j) := by
    rw [show titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
      titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM =
      QuotientGroup.mk (reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
        reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) from rfl,
      ← QuotientGroup.mk_pow]
  rw [hpow, hr, ← QuotientGroup.mk_mul, edgeOfW_mk]
  apply Subtype.ext
  change (((reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) *
      ((reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
        reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) ^ j) :
      ↥(moufangN D Γ n t)) : D) • aptEdge t (n : ZMod (2 * n)) = _
  rw [Subgroup.coe_mul, Subgroup.coe_mul, mul_smul]
  exact reflOneN_smul_rot_edge (t := t) ht hn hP hT hM j

private theorem two_mul_sum_ne_one (i j : ℕ) :
    2 * ((i + j : ℕ) : ZMod (2 * n)) ≠ 1 := by
  intro htwo
  have htwo' : ((2 * (i + j) : ℕ) : ZMod (2 * n)) = ((1 : ℕ) : ZMod (2 * n)) := by
    simpa using htwo
  have hmod : (2 * (i + j)) ≡ 1 [MOD 2 * n] :=
    (ZMod.natCast_eq_natCast_iff (2 * (i + j)) 1 (2 * n)).mp htwo'
  have hmod2 : (2 * (i + j)) ≡ 1 [MOD 2] :=
    Nat.ModEq.of_dvd (by omega : 2 ∣ 2 * n) hmod
  have h0 : (2 * (i + j)) % 2 = 1 % 2 := hmod2
  simp at h0

private theorem refl_rot_index_ne (j j' : ℕ) :
    (n : ZMod (2 * n)) + 1 - 2 * (j : ZMod (2 * n)) ≠
      (n : ZMod (2 * n)) + 2 * (j' : ZMod (2 * n)) := by
  intro h
  have h2 : 2 * ((j + j' : ℕ) : ZMod (2 * n)) = 1 := by
    have h3 : (n : ZMod (2 * n)) + (2 * (j : ZMod (2 * n)) + 2 * (j' : ZMod (2 * n))) =
        (n : ZMod (2 * n)) + 1 := by
      calc (n : ZMod (2 * n)) + (2 * (j : ZMod (2 * n)) + 2 * (j' : ZMod (2 * n)))
          = ((n : ZMod (2 * n)) + 2 * (j' : ZMod (2 * n))) + 2 * (j : ZMod (2 * n)) := by ring
        _ = ((n : ZMod (2 * n)) + 1 - 2 * (j : ZMod (2 * n))) + 2 * (j : ZMod (2 * n)) := by
            rw [h]
        _ = (n : ZMod (2 * n)) + 1 := by ring
    have h4 := add_left_cancel h3
    calc 2 * ((j + j' : ℕ) : ZMod (2 * n))
        = 2 * (j : ZMod (2 * n)) + 2 * (j' : ZMod (2 * n)) := by push_cast; ring
      _ = 1 := h4
  exact two_mul_sum_ne_one j j' h2

theorem closure_titsW_eq_top {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    [(cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal] :
    Subgroup.closure ({titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM,
      titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM} :
        Set (WeylGroup (moufangB D Γ n t) (moufangN D Γ n t))) = ⊤ := by
  classical
  let W := WeylGroup (moufangB D Γ n t) (moufangN D Γ n t)
  let s : W := titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM
  let r : W := s * titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM
  let G : Subgroup W := Subgroup.closure
    ({titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM,
      titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM} : Set W)
  have hsG : s ∈ G := Subgroup.subset_closure (by simp [s, G])
  have hw2G : titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM ∈ G :=
    Subgroup.subset_closure (by simp [G])
  have hrG : r ∈ G := by
    dsimp [r]
    exact Subgroup.mul_mem _ hsG hw2G
  let φ : Bool × Fin n → W := fun p =>
    match p.1 with
    | false => r ^ p.2.val
    | true => s * r ^ p.2.val
  let ψ : Bool × Fin n → G := fun p =>
    ⟨φ p, by
      dsimp [φ]
      cases hp : p.1
      · exact Subgroup.pow_mem _ hrG _
      · exact Subgroup.mul_mem _ hsG (Subgroup.pow_mem _ hrG _)⟩
  have hψ_inj : Function.Injective ψ := by
    rintro ⟨b, j⟩ ⟨b', j'⟩ h
    have hW : φ (b, j) = φ (b', j') := congrArg Subtype.val h
    cases b <;> cases b'
    · dsimp [φ] at hW
      have hedge := congrArg (edgeOfW ht hn hP hT) hW
      rw [show r = titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
          titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM by dsimp [r, s],
        edgeOfW_rot_pow (t := t) ht hn hP hT hM j.val,
        edgeOfW_rot_pow (t := t) ht hn hP hT hM j'.val] at hedge
      have hidx := aptEdge_injective ht hn (congrArg Subtype.val hedge)
      have h2 := add_left_cancel hidx
      have hjeq := two_mul_zmod_inj (j := j.val) (j' := j'.val) j.isLt j'.isLt h2
      exact Prod.ext rfl (Fin.ext hjeq)
    · dsimp [φ] at hW
      have hedge := congrArg (edgeOfW ht hn hP hT) hW
      rw [show r = titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
          titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM by dsimp [r, s],
        show s = titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM by dsimp [s],
        edgeOfW_rot_pow (t := t) ht hn hP hT hM j.val,
        edgeOfW_refl_pow (t := t) ht hn hP hT hM j'.val] at hedge
      have hidx := aptEdge_injective ht hn (congrArg Subtype.val hedge)
      rw [show 2 * ((n : ZMod (2 * n)) + 1) -
          ((n : ZMod (2 * n)) + 2 * (j'.val : ZMod (2 * n))) - 1 =
          (n : ZMod (2 * n)) + 1 - 2 * (j'.val : ZMod (2 * n)) by ring] at hidx
      exfalso
      exact (refl_rot_index_ne j'.val j.val) hidx.symm
    · dsimp [φ] at hW
      have hedge := congrArg (edgeOfW ht hn hP hT) hW
      rw [show r = titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
          titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM by dsimp [r, s],
        show s = titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM by dsimp [s],
        edgeOfW_refl_pow (t := t) ht hn hP hT hM j.val,
        edgeOfW_rot_pow (t := t) ht hn hP hT hM j'.val] at hedge
      have hidx := aptEdge_injective ht hn (congrArg Subtype.val hedge)
      rw [show 2 * ((n : ZMod (2 * n)) + 1) -
          ((n : ZMod (2 * n)) + 2 * (j.val : ZMod (2 * n))) - 1 =
          (n : ZMod (2 * n)) + 1 - 2 * (j.val : ZMod (2 * n)) by ring] at hidx
      exfalso
      exact (refl_rot_index_ne j.val j'.val) hidx
    · dsimp [φ] at hW
      have hW' : r ^ j.val = r ^ j'.val := mul_left_cancel hW
      have hedge := congrArg (edgeOfW ht hn hP hT) hW'
      rw [show r = titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
          titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM by dsimp [r, s],
        edgeOfW_rot_pow (t := t) ht hn hP hT hM j.val,
        edgeOfW_rot_pow (t := t) ht hn hP hT hM j'.val] at hedge
      have hidx := aptEdge_injective ht hn (congrArg Subtype.val hedge)
      have h2 := add_left_cancel hidx
      have hjeq := two_mul_zmod_inj (j := j.val) (j' := j'.val) j.isLt j'.isLt h2
      exact Prod.ext rfl (Fin.ext hjeq)
  haveI : Finite D := finite_of_faithfulSMul V D
  haveI : Finite ↥(littleGroup D Γ n) := Subtype.finite
  haveI : Finite ↥(moufangN D Γ n t) := Subtype.finite
  haveI : Finite W := by
    dsimp [W]
    infer_instance
  haveI : Finite ↥G := Subtype.finite
  have hcardψ : Nat.card (Bool × Fin n) ≤ Nat.card ↥G :=
    Nat.card_le_card_of_injective ψ hψ_inj
  have hcard2 : Nat.card (Bool × Fin n) = 2 * n := by
    rw [Nat.card_prod]
    simp
  have hlower : 2 * n ≤ Nat.card ↥G := by
    rwa [hcard2] at hcardψ
  have hupper : Nat.card ↥G ≤ 2 * n := by
    have hinj : Function.Injective (fun g : ↥G => (g : W)) := Subtype.val_injective
    have hle := Nat.card_le_card_of_injective _ hinj
    rwa [show Nat.card W = 2 * n from card_weyl_tits (t := t) ht hn hP hT hM] at hle
  have hcardG : Nat.card ↥G = 2 * n := le_antisymm hupper hlower
  have htop : G = ⊤ := by
    refine Subgroup.eq_top_of_card_eq G ?_
    rw [hcardG, show Nat.card W = 2 * n from card_weyl_tits (t := t) ht hn hP hT hM]
  simpa [G] using htop

end CFSG.Quasithin.Stroth
