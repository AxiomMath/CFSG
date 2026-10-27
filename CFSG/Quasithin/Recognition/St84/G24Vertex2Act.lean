module

public import CFSG.Quasithin.Recognition.St84.G24Vertex2Change
import CFSG.GroupTheory.CommutingProductFixedSubgroup
import CFSG.Quasithin.Recognition.St84.G24Tools
import CFSG.Quasithin.Background.SpecialPGroupCenter
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.GH74.QTGen4.DSGen4 CFSG.Quasithin.F7 CFSG.Quasithin.St84
open CFSG.Quasithin.KGC31 (eElt eElt_zero eElt_single eElt_add eElt_injective
  conj_eElt map_eElt)
open CFSG.GroupTheory (eElt_mem_of_forall_mem eElt_add_mul_inv_mem conj_eElt_mul_inv_mem
  eElt_eq_castAdd_mul_natAdd eElt_ofAdd_cols eElt_mul_inv_mem_of_cols eEltQuotEquiv
  eEltQuotEquiv_ofAdd quadMapOfCoeffs quadMapOfCoeffs_conj)
open Certificates.A5GL42 (aN bN)
open CFSG.QuasithinUnique.A5.Delta5 (Alt5 a5_card)
open CFSG.Quasithin.H.Q13 (om)
open scoped commutatorElement Matrix

variable {G : Type} [Group G]
variable {L1 L2 S : Subgroup G}

private theorem nLift_fpow_toAdd [Finite G] (F : G24Frame2 L1 L2 S)
    {n : Fin 4 → G} (hn : F.IsNLift n) (v : Fin 4 → ZMod 2) :
    Multiplicative.toAdd (F.FN.φ ⟨eElt n v,
      eElt_mem_of_forall_mem (fun j => (hn j).choose) v⟩) = v := by
  have hfusion : ∀ j, F.FN.φ ⟨n j, (hn j).choose⟩ =
      Multiplicative.ofAdd (Pi.single j (1 : ZMod 2)) := by
    intro j
    obtain ⟨h, hh⟩ := hn j
    have hsub : (⟨n j, (hn j).choose⟩ : ↥(dsQ L2 L1 S)) = ⟨n j, h⟩ := Subtype.ext rfl
    rw [hsub]
    exact hh
  exact G24Vertex2.toAdd_phi_eElt F.FN.φ n (fun j => (hn j).choose) hfusion v

private theorem eElt_v2Block_col_N_zero (k u : G) (n : Fin 4 → G)
    (N : Matrix (Fin 4) (Fin 4) (ZMod 2)) (d : Fin 4) :
    eElt (v2Frame k u n) (fun i => v2Block 1 0 N i (Fin.natAdd 2 d)) =
      eElt n (fun k => N k d) := by
  rw [v2Frame_eq_append, eElt_eq_castAdd_mul_natAdd]
  have h1 : (fun i : Fin 2 => v2Block 1 0 N (Fin.castAdd 4 i) (Fin.natAdd 2 d)) =
      fun _ : Fin 2 => (0 : ZMod 2) := by
    funext i
    rw [v2Block_castAdd_natAdd]
    rfl
  have h2 : (fun j : Fin 4 => v2Block 1 0 N (Fin.natAdd 2 j) (Fin.natAdd 2 d)) =
      fun k : Fin 4 => N k d := by
    funext j
    rw [v2Block_natAdd_natAdd]
  rw [h1, h2]
  change eElt (show Fin 2 → G from ![u, k * u * k⁻¹]) 0 * eElt n (fun k => N k d) =
    eElt n (fun k => N k d)
  rw [eElt_zero, one_mul]

private theorem conj_lift_mem_of_act_zero [Finite G] (F : G24Frame2 L1 L2 S)
    {u : G} {n : Fin 4 → G}
    {X0 : Matrix (Fin 2) (Fin 4) (ZMod 2)}
    (N : Matrix (Fin 4) (Fin 4) (ZMod 2)) {g : G}
    (hline : ∀ j : Fin 6, g * v2Frame F.k u n j * g⁻¹ *
      (eElt (v2Frame F.k u n) fun i => v2Block 1 X0 N i j)⁻¹ ∈
        centerOf (dsQ L2 L1 S))
    (hX0 : X0 = 0) (d : Fin 4) :
    g * n d * g⁻¹ ∈ Subgroup.closure (Set.range n) ⊔ centerOf (dsQ L2 L1 S) := by
  classical
  let Z2 : Subgroup G := centerOf (dsQ L2 L1 S)
  let K : Subgroup G := Subgroup.closure (Set.range n)
  let N' : Subgroup G := K ⊔ Z2
  have hcol : eElt (v2Frame F.k u n) (fun i => v2Block 1 0 N i (Fin.natAdd 2 d)) =
      eElt n (fun k => N k d) := by
    simpa only [hX0] using eElt_v2Block_col_N_zero F.k u n N d
  have hmem : g * n d * g⁻¹ * (eElt n (fun k => N k d))⁻¹ ∈ Z2 := by
    have h := hline (Fin.natAdd 2 d)
    rw [hX0] at h
    rw [v2Frame_natAdd] at h
    rwa [hcol] at h
  have hK : eElt n (fun k => N k d) ∈ K :=
    eElt_mem_of_forall_mem (fun j => Subgroup.subset_closure (Set.mem_range_self j)) _
  have hmemN : g * n d * g⁻¹ * (eElt n (fun k => N k d))⁻¹ ∈ N' :=
    Subgroup.mem_sup_right hmem
  have hqN : eElt n (fun k => N k d) ∈ N' := Subgroup.mem_sup_left hK
  rw [show g * n d * g⁻¹ =
      (g * n d * g⁻¹ * (eElt n (fun k => N k d))⁻¹) * eElt n (fun k => N k d)
      from by group]
  exact N'.mul_mem hmemN hqN

private def G24Frame2.ActsTrivOnW (F : G24Frame2 L1 L2 S) (g : G) : Prop :=
  ∀ w ∈ F.W, ∃ z ∈ centerOf (dsQ L2 L1 S), g * w * g⁻¹ = z * w

private theorem G24Frame2.actsTrivOnW_mul [Finite G] (F : G24Frame2 L1 L2 S)
    {g h : G} (hg : F.ActsTrivOnW g) (hh : F.ActsTrivOnW h) :
    F.ActsTrivOnW (g * h) := by
  intro w hw
  obtain ⟨z₁, hz₁, h₁⟩ := hh w hw
  have hwW : h * w * h⁻¹ ∈ F.W := by
    rw [h₁]
    exact F.W.mul_mem (F.Z2_le_W hz₁) hw
  obtain ⟨z₂, hz₂, h₂⟩ := hg (h * w * h⁻¹) hwW
  refine ⟨z₂ * z₁, (centerOf (dsQ L2 L1 S)).mul_mem hz₂ hz₁, ?_⟩
  calc (g * h) * w * (g * h)⁻¹ = g * (h * w * h⁻¹) * g⁻¹ := by group
    _ = z₂ * (h * w * h⁻¹) := h₂
    _ = z₂ * (z₁ * w) := by rw [h₁]
    _ = (z₂ * z₁) * w := by rw [mul_assoc]

private theorem G24Frame2.actsTrivOnW_inv [Finite G] (F : G24Frame2 L1 L2 S)
    {g : G} (hgP : g ∈ L2 ⊔ bigB L1 L2 S) (hg : F.ActsTrivOnW g) :
    F.ActsTrivOnW g⁻¹ := by
  intro w hw
  obtain ⟨z, hz, h₁⟩ := hg w hw
  have hgP' : g⁻¹ ∈ L2 ⊔ bigB L1 L2 S :=
    (L2 ⊔ bigB L1 L2 S).inv_mem hgP
  have hz' : g⁻¹ * z * g ∈ centerOf (dsQ L2 L1 S) := by
    simpa only [inv_inv] using
      (Subgroup.mem_normalizer_iff.mp (P_le_normalizer_centerOf_dsQ_right L1 L2 S hgP') z).mp hz
  refine ⟨(g⁻¹ * z * g)⁻¹, (centerOf (dsQ L2 L1 S)).inv_mem hz', ?_⟩
  have heq : (g⁻¹ * z * g) * (g⁻¹ * w * g) = w := by
    calc (g⁻¹ * z * g) * (g⁻¹ * w * g) = g⁻¹ * (z * w) * g := by group
      _ = g⁻¹ * (g * w * g⁻¹) * g := by rw [← h₁]
      _ = w := by group
  have hB : g⁻¹ * w * g = (g⁻¹ * z * g)⁻¹ * w := by
    calc g⁻¹ * w * g = (g⁻¹ * z * g)⁻¹ * ((g⁻¹ * z * g) * (g⁻¹ * w * g)) := by
          group
      _ = (g⁻¹ * z * g)⁻¹ * w := by rw [heq]
  simpa only [inv_inv] using hB

private theorem G24Frame2.Q2_actsTrivOnW [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {q : G} (hq : q ∈ dsQ L2 L1 S) :
    F.ActsTrivOnW q := by
  intro w hw
  have hwQ : w ∈ dsQ L2 L1 S := ((F.mem_W w).mp hw).1
  have hcomm : ⁅q, w⁆ ∈ centerOf (dsQ L2 L1 S) :=
    CFSG.Quasithin.IsSpecialPGroup.commutator_le_centerOf hD.special_right
      (Subgroup.commutator_mem_commutator hq hwQ)
  refine ⟨⁅q, w⁆, hcomm, ?_⟩
  rw [commutatorElement_def]
  group

private theorem G24Frame2.L2_actsTrivOnW [Finite G] (F : G24Frame2 L1 L2 S)
    {l : G} (hl : l ∈ L2) : F.ActsTrivOnW l := by
  intro w hw
  have hcomm : ⁅w, l⁆ ∈ centerOf (dsQ L2 L1 S) := ((F.mem_W w).mp hw).2 l hl
  refine ⟨⁅l, w⁆, ?_, ?_⟩
  · have h : ⁅l, w⁆ = ⁅w, l⁆⁻¹ :=
      (commutatorElement_inv (g₁ := w) (g₂ := l)).symm
    rw [h]
    exact (centerOf (dsQ L2 L1 S)).inv_mem hcomm
  · rw [commutatorElement_def]
    group

private theorem G24Frame2.A_eq_closure_ab_sup_zpowers [Finite G] (F : G24Frame2 L1 L2 S) :
    F.A = Subgroup.closure ({F.a, F.b} : Set G) ⊔ Subgroup.zpowers F.k := by
  rw [← F.closure_eq]
  rw [show ({F.a, F.b, F.k} : Set G) = ({F.a, F.b} : Set G) ∪ {F.k} from by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    tauto]
  rw [Subgroup.closure_union, Subgroup.zpowers_eq_closure]

private theorem not_actsTrivOnW_of_fixed_free [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {g : G}
    (hfree : ∀ w ∈ F.W,
      g * w * g⁻¹ * w⁻¹ ∈ centerOf (dsQ L2 L1 S) → w ∈ centerOf (dsQ L2 L1 S))
    (htriv : F.ActsTrivOnW g) : False := by
  have hWZ : F.W ≤ centerOf (dsQ L2 L1 S) := by
    intro w hw
    obtain ⟨z, hz, hzw⟩ := htriv w hw
    have hfix : g * w * g⁻¹ * w⁻¹ ∈ centerOf (dsQ L2 L1 S) := by
      rw [hzw]
      simpa using hz
    exact hfree w hw hfix
  have hle := Subgroup.card_le_of_le hWZ
  rw [F.card_W, hD.card_center_right] at hle
  norm_num at hle

private theorem conj_sup_closure_mem {K Z : Subgroup G} {n : Fin 4 → G}
    (hK : K = Subgroup.closure (Set.range n)) {g : G}
    (hgen : ∀ d, g * n d * g⁻¹ ∈ K ⊔ Z)
    (hZ : ∀ z ∈ Z, g * z * g⁻¹ ∈ Z) :
    ∀ x ∈ K ⊔ Z, g * x * g⁻¹ ∈ K ⊔ Z := by
  subst hK
  have hmap : (Subgroup.closure (Set.range n) ⊔ Z).map (MulAut.conj g).toMonoidHom ≤
      Subgroup.closure (Set.range n) ⊔ Z := by
    rw [Subgroup.map_le_iff_le_comap]
    apply sup_le
    · refine (Subgroup.closure_le _).mpr (Set.range_subset_iff.mpr ?_)
      intro d
      simpa [MulAut.conj_apply] using hgen d
    · intro z hz
      exact Subgroup.mem_sup_right (hZ z hz)
  intro x hx
  simpa [MulAut.conj_apply] using hmap (Subgroup.mem_map_of_mem _ hx)

private theorem mem_normalizer_closure_sup_centerOf [Finite G] {K Z : Subgroup G} {n : Fin 4 → G}
    (hK : K = Subgroup.closure (Set.range n)) {g : G}
    (hgen : ∀ d, g * n d * g⁻¹ ∈ K ⊔ Z)
    (hZ : ∀ z ∈ Z, g * z * g⁻¹ ∈ Z) :
    g ∈ Subgroup.normalizer ((K ⊔ Z : Subgroup G) : Set G) := by
  haveI : Finite ((K ⊔ Z : Subgroup G) : Set G) :=
    Set.toFinite ((K ⊔ Z : Subgroup G) : Set G)
  exact Subgroup.mem_normalizer_fintype (conj_sup_closure_mem hK hgen hZ)

private theorem G24Frame2.a_mem_normalizer_span [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {u : G} {n : Fin 4 → G}
    (hn : F.IsNLift n) {X : Fin 3 → Matrix (Fin 2) (Fin 4) (ZMod 2)}
    (hX : F.IsAct u n X) (hX0 : X 0 = 0) :
    F.a ∈ Subgroup.normalizer
      (((Subgroup.closure (Set.range n) ⊔ centerOf (dsQ L2 L1 S) : Subgroup G)) : Set G) := by
  classical
  let Z2 : Subgroup G := centerOf (dsQ L2 L1 S)
  let K : Subgroup G := Subgroup.closure (Set.range n)
  have hKQ : K ≤ dsQ L2 L1 S := by
    refine (Subgroup.closure_le (K := dsQ L2 L1 S)).mpr ?_
    intro x hx
    obtain ⟨d, rfl⟩ := hx
    exact (hn d).choose
  have hspec := F.special_data hD
  have haZ : ∀ z ∈ Z2, F.a * z * F.a⁻¹ ∈ Z2 :=
    fun z hz => hspec.2.2.2.2.2.2.1 F.a F.a_mem.1 z hz
  have hgen : ∀ d, F.a * n d * F.a⁻¹ ∈ K ⊔ Z2 :=
    fun d => conj_lift_mem_of_act_zero F (X0 := X 0) aN (g := F.a) hX.1 hX0 d
  exact mem_normalizer_closure_sup_centerOf (K := K) (Z := Z2) (n := n) (g := F.a)
    rfl hgen haZ

private theorem G24Frame2.b_mem_normalizer_span [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {u : G} {n : Fin 4 → G}
    (hn : F.IsNLift n) {X : Fin 3 → Matrix (Fin 2) (Fin 4) (ZMod 2)}
    (hX : F.IsAct u n X) (hX1 : X 1 = 0) :
    F.b ∈ Subgroup.normalizer
      (((Subgroup.closure (Set.range n) ⊔ centerOf (dsQ L2 L1 S) : Subgroup G)) : Set G) := by
  classical
  let Z2 : Subgroup G := centerOf (dsQ L2 L1 S)
  let K : Subgroup G := Subgroup.closure (Set.range n)
  have hKQ : K ≤ dsQ L2 L1 S := by
    refine (Subgroup.closure_le (K := dsQ L2 L1 S)).mpr ?_
    intro x hx
    obtain ⟨d, rfl⟩ := hx
    exact (hn d).choose
  have hspec := F.special_data hD
  have hbZ : ∀ z ∈ Z2, F.b * z * F.b⁻¹ ∈ Z2 :=
    fun z hz => hspec.2.2.2.2.2.2.1 F.b F.b_mem.1 z hz
  have hgen : ∀ d, F.b * n d * F.b⁻¹ ∈ K ⊔ Z2 :=
    fun d => conj_lift_mem_of_act_zero F (X0 := X 1) bN (g := F.b) hX.2.1 hX1 d
  exact mem_normalizer_closure_sup_centerOf (K := K) (Z := Z2) (n := n) (g := F.b)
    rfl hgen hbZ

private theorem G24Frame2.Q2_mem_normalizer_span [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {n : Fin 4 → G} (hn : F.IsNLift n) {q : G}
    (hq : q ∈ dsQ L2 L1 S) :
    q ∈ Subgroup.normalizer
      (((Subgroup.closure (Set.range n) ⊔ centerOf (dsQ L2 L1 S) : Subgroup G)) : Set G) := by
  classical
  let Z2 : Subgroup G := centerOf (dsQ L2 L1 S)
  let K : Subgroup G := Subgroup.closure (Set.range n)
  have hKQ : K ≤ dsQ L2 L1 S := by
    refine (Subgroup.closure_le (K := dsQ L2 L1 S)).mpr ?_
    intro x hx
    obtain ⟨d, rfl⟩ := hx
    exact (hn d).choose
  have hnQ : ∀ d, n d ∈ dsQ L2 L1 S := fun d => (hn d).choose
  have hcommq : ∀ d, ⁅q, n d⁆ ∈ Z2 := fun d =>
    CFSG.Quasithin.IsSpecialPGroup.commutator_le_centerOf hD.special_right
      (Subgroup.commutator_mem_commutator hq (hnQ d))
  have hgen : ∀ d, q * n d * q⁻¹ ∈ K ⊔ Z2 := by
    intro d
    have heq : q * n d * q⁻¹ = ⁅q, n d⁆ * n d := by
      rw [commutatorElement_def]
      group
    rw [heq]
    exact (K ⊔ Z2).mul_mem (Subgroup.mem_sup_right (hcommq d))
      (Subgroup.mem_sup_left (Subgroup.subset_closure (Set.mem_range_self d)))
  have hZ : ∀ z ∈ Z2, q * z * q⁻¹ ∈ Z2 := by
    intro z hz
    rw [G24Vertex2.conj_eq_of_mem_centerOf hz hq]
    exact hz
  exact mem_normalizer_closure_sup_centerOf (K := K) (Z := Z2) (n := n) (g := q)
    rfl hgen hZ

private def spanLiftCenter (L1 L2 S : Subgroup G) (n : Fin 4 → G) : Subgroup G :=
  Subgroup.closure (Set.range n) ⊔ centerOf (dsQ L2 L1 S)

private theorem exists_quotient_map_of_isNLift [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {n : Fin 4 → G} (hn : F.IsNLift n)
    [(centerOf (dsQ L2 L1 S)).subgroupOf (spanLiftCenter L1 L2 S n) |>.Normal] :
    ∃ φN : Multiplicative (Fin 4 → ZMod 2) →*
        (↥(spanLiftCenter L1 L2 S n) ⧸
          (centerOf (dsQ L2 L1 S)).subgroupOf (spanLiftCenter L1 L2 S n)),
      ∀ d : Fin 4,
        φN (Multiplicative.ofAdd (Pi.single d (1 : ZMod 2))) =
          (QuotientGroup.mk (⟨n d, show n d ∈ spanLiftCenter L1 L2 S n from
            Subgroup.mem_sup_left (Subgroup.subset_closure (Set.mem_range_self d))⟩ :
            ↥(spanLiftCenter L1 L2 S n)) :
            ↥(spanLiftCenter L1 L2 S n) ⧸
              (centerOf (dsQ L2 L1 S)).subgroupOf (spanLiftCenter L1 L2 S n)) := by
  classical
  let Q2 : Subgroup G := dsQ L2 L1 S
  let Z2 : Subgroup G := centerOf (dsQ L2 L1 S)
  let K : Subgroup G := Subgroup.closure (Set.range n)
  let N' : Subgroup G := spanLiftCenter L1 L2 S n
  have hN'eq : N' = K ⊔ Z2 := rfl
  have hKQ : K ≤ Q2 := by
    refine (Subgroup.closure_le (K := Q2)).mpr ?_
    intro x hx
    obtain ⟨d, rfl⟩ := hx
    exact (hn d).choose
  have hNQ : N' ≤ Q2 := by
    rw [hN'eq]
    exact sup_le hKQ inf_le_left
  have hKN : K ≤ N' := hN'eq ▸ le_sup_left
  have hZ2N : Z2 ≤ N' := hN'eq ▸ le_sup_right
  have hnN : ∀ d, n d ∈ N' := fun d =>
    hKN (Subgroup.subset_closure (Set.mem_range_self d))
  have hZc : ∀ z ∈ Z2, ∀ x ∈ N', z * x = x * z := by
    intro z hz x hx
    exact (F.special_data hD).2.2.2.1 z hz x (hNQ hx)
  haveI : (Z2.subgroupOf N').Normal :=
    Subgroup.normal_of_le_center fun z hz =>
      Subgroup.mem_center_iff.mpr fun x => Subtype.ext (hZc z hz x x.2).symm
  have hZc_gen : ∀ z ∈ Z2, ∀ i, z * n i = n i * z := by
    intro z hz i
    exact hZc z hz (n i) (hnN i)
  have hsquare := (F.special_data hD).2.2.2.2.2.1
  have hsq : ∀ i, n i ^ 2 ∈ Z2 := fun i => hsquare (n i) ((hn i).choose)
  have hcm : ∀ i j, ⁅n i, n j⁆ ∈ Z2 := by
    intro i j
    exact CFSG.Quasithin.IsSpecialPGroup.commutator_le_centerOf hD.special_right
      (Subgroup.commutator_mem_commutator ((hn i).choose) ((hn j).choose))
  let φN : Multiplicative (Fin 4 → ZMod 2) →* ↥N' ⧸ Z2.subgroupOf N' :=
    { toFun := fun v => QuotientGroup.mk ⟨eElt n v.toAdd, eElt_mem_of_forall_mem hnN v.toAdd⟩
      map_one' := by
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        show eElt n 0 ∈ Z2
        rw [eElt_zero]
        exact Z2.one_mem
      map_mul' := by
        intro v w
        have h := eElt_add_mul_inv_mem hZc_gen hsq hcm v.toAdd w.toAdd
        rw [← QuotientGroup.mk_mul]
        refine QuotientGroup.eq_iff_div_mem.mpr ?_
        rw [Subgroup.mem_subgroupOf]
        simpa [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv] using h }
  refine ⟨φN, ?_⟩
  intro d
  apply congrArg QuotientGroup.mk
  apply Subtype.ext
  change eElt n (Pi.single d 1) = n d
  rw [eElt_single]

private theorem quotient_values_of_generators [Finite G]
    {n : Fin 4 → G}
    [(centerOf (dsQ L2 L1 S)).subgroupOf (spanLiftCenter L1 L2 S n) |>.Normal]
    (φN : Multiplicative (Fin 4 → ZMod 2) →*
      (↥(spanLiftCenter L1 L2 S n) ⧸
        (centerOf (dsQ L2 L1 S)).subgroupOf (spanLiftCenter L1 L2 S n)))
    (hgen : ∀ d : Fin 4,
      φN (Multiplicative.ofAdd (Pi.single d (1 : ZMod 2))) =
        (QuotientGroup.mk (⟨n d, show n d ∈ spanLiftCenter L1 L2 S n from
          Subgroup.mem_sup_left (Subgroup.subset_closure (Set.mem_range_self d))⟩ :
          ↥(spanLiftCenter L1 L2 S n)) :
          ↥(spanLiftCenter L1 L2 S n) ⧸
            (centerOf (dsQ L2 L1 S)).subgroupOf (spanLiftCenter L1 L2 S n))) :
    ∀ x (hx : x ∈ Subgroup.closure (Set.range n)),
      ∃ v : Fin 4 → ZMod 2,
        (QuotientGroup.mk (⟨x, show x ∈ spanLiftCenter L1 L2 S n from
          Subgroup.mem_sup_left hx⟩ : ↥(spanLiftCenter L1 L2 S n)) :
          ↥(spanLiftCenter L1 L2 S n) ⧸
            (centerOf (dsQ L2 L1 S)).subgroupOf (spanLiftCenter L1 L2 S n)) =
        φN (Multiplicative.ofAdd v) := by
  classical
  let Q2 : Subgroup G := dsQ L2 L1 S
  let Z2 : Subgroup G := centerOf (dsQ L2 L1 S)
  let K : Subgroup G := Subgroup.closure (Set.range n)
  let N' : Subgroup G := spanLiftCenter L1 L2 S n
  have hN'eq : N' = K ⊔ Z2 := rfl
  have hKN : K ≤ N' := hN'eq ▸ le_sup_left
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨d, rfl⟩ := hy
      exact ⟨Pi.single d 1, (hgen d).symm⟩
  | one =>
      refine ⟨0, ?_⟩
      show QuotientGroup.mk (⟨1, hKN (K.one_mem)⟩ : ↥N') =
        φN (Multiplicative.ofAdd (0 : Fin 4 → ZMod 2))
      rw [show φN (Multiplicative.ofAdd (0 : Fin 4 → ZMod 2)) = 1 from map_one φN]
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr
        (Z2.one_mem))
  | mul a b ha hb iha ihb =>
      obtain ⟨va, hva⟩ := iha
      obtain ⟨vb, hvb⟩ := ihb
      refine ⟨va + vb, ?_⟩
      calc QuotientGroup.mk (⟨a * b, hKN (K.mul_mem ha hb)⟩ : ↥N')
          = QuotientGroup.mk (⟨a, hKN ha⟩ : ↥N') *
            QuotientGroup.mk (⟨b, hKN hb⟩ : ↥N') := by
            rw [← QuotientGroup.mk_mul]
            exact congrArg QuotientGroup.mk (Subtype.ext rfl)
        _ = φN (Multiplicative.ofAdd va) * φN (Multiplicative.ofAdd vb) := by
            rw [hva, hvb]
        _ = φN (Multiplicative.ofAdd (va + vb)) := by
            rw [← map_mul]
            rfl
  | inv a ha iha =>
      obtain ⟨va, hva⟩ := iha
      refine ⟨-va, ?_⟩
      calc QuotientGroup.mk (⟨a⁻¹, hKN (K.inv_mem ha)⟩ : ↥N')
          = (QuotientGroup.mk (⟨a, hKN ha⟩ : ↥N'))⁻¹ := by
            rw [← QuotientGroup.mk_inv]
            exact congrArg QuotientGroup.mk (Subtype.ext rfl)
        _ = (φN (Multiplicative.ofAdd va))⁻¹ := by rw [hva]
        _ = φN (Multiplicative.ofAdd (-va)) := by
            rw [← map_inv]
            rfl

private theorem surjective_quotient_map_of_K [Finite G] (F : G24Frame2 L1 L2 S)
    {n : Fin 4 → G} (hn : F.IsNLift n)
    [(centerOf (dsQ L2 L1 S)).subgroupOf (spanLiftCenter L1 L2 S n) |>.Normal]
    (φN : Multiplicative (Fin 4 → ZMod 2) →*
      (↥(spanLiftCenter L1 L2 S n) ⧸
        (centerOf (dsQ L2 L1 S)).subgroupOf (spanLiftCenter L1 L2 S n)))
    (hKsurj : ∀ x (hx : x ∈ Subgroup.closure (Set.range n)),
      ∃ v : Fin 4 → ZMod 2,
        (QuotientGroup.mk (⟨x, show x ∈ spanLiftCenter L1 L2 S n from
          Subgroup.mem_sup_left hx⟩ : ↥(spanLiftCenter L1 L2 S n)) :
          ↥(spanLiftCenter L1 L2 S n) ⧸
            (centerOf (dsQ L2 L1 S)).subgroupOf (spanLiftCenter L1 L2 S n)) =
        φN (Multiplicative.ofAdd v)) :
    Function.Surjective (fun v : Fin 4 → ZMod 2 => φN (Multiplicative.ofAdd v)) := by
  classical
  let Q2 : Subgroup G := dsQ L2 L1 S
  let Z2 : Subgroup G := centerOf Q2
  let K : Subgroup G := Subgroup.closure (Set.range n)
  let N' : Subgroup G := spanLiftCenter L1 L2 S n
  have hN'eq : N' = K ⊔ Z2 := rfl
  have hKQ : K ≤ Q2 := by
    refine (Subgroup.closure_le (K := Q2)).mpr ?_
    intro x hx
    obtain ⟨d, rfl⟩ := hx
    exact (hn d).choose
  have hKN : K ≤ N' := hN'eq ▸ le_sup_left
  have hZ2N : Z2 ≤ N' := hN'eq ▸ le_sup_right
  have hNsurj : ∀ x (hx : x ∈ N'), ∃ v : Fin 4 → ZMod 2,
      (QuotientGroup.mk (⟨x, hx⟩ : ↥N') : ↥N' ⧸ Z2.subgroupOf N') =
        φN (Multiplicative.ofAdd v) := by
    intro x hx
    have hcomm : ∀ k ∈ K, ∀ z ∈ Z2, k * z = z * k := by
      intro k hk z hz
      exact Subgroup.mem_centralizer_iff.mp hz.2 k (hKQ hk)
    obtain ⟨k, hk, z, hz, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm hx
    obtain ⟨v, hv⟩ := hKsurj k hk
    refine ⟨v, ?_⟩
    have hz1 : (QuotientGroup.mk (⟨z, hZ2N hz⟩ : ↥N') :
        ↥N' ⧸ Z2.subgroupOf N') = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hz)
    calc QuotientGroup.mk (⟨k * z, N'.mul_mem (hKN hk) (hZ2N hz)⟩ : ↥N')
        = QuotientGroup.mk (⟨k, hKN hk⟩ : ↥N') *
          QuotientGroup.mk (⟨z, hZ2N hz⟩ : ↥N') := by
          rw [← QuotientGroup.mk_mul]
          exact congrArg QuotientGroup.mk (Subtype.ext rfl)
      _ = QuotientGroup.mk (⟨k, hKN hk⟩ : ↥N') := by rw [hz1, mul_one]
      _ = φN (Multiplicative.ofAdd v) := hv
  intro y
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective y
  obtain ⟨v, hv⟩ := hNsurj x x.2
  exact ⟨v, hv.symm.trans hx⟩

private theorem card_closure_sup_centerOf_le [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {n : Fin 4 → G} (hn : F.IsNLift n) :
    Nat.card ↥(Subgroup.closure (Set.range n) ⊔ centerOf (dsQ L2 L1 S)) ≤ 2 ^ 8 := by
  classical
  let Z2 : Subgroup G := centerOf (dsQ L2 L1 S)
  let N' : Subgroup G := spanLiftCenter L1 L2 S n
  have hN'eq : N' = Subgroup.closure (Set.range n) ⊔ centerOf (dsQ L2 L1 S) := rfl
  have hNQ : N' ≤ dsQ L2 L1 S := by
    rw [hN'eq]
    exact sup_le ((Subgroup.closure_le (K := dsQ L2 L1 S)).mpr fun x hx => by
      obtain ⟨d, rfl⟩ := hx
      exact (hn d).choose) inf_le_left
  have hZc : ∀ z ∈ Z2, ∀ x ∈ N', z * x = x * z := by
    intro z hz x hx
    exact (F.special_data hD).2.2.2.1 z hz x (hNQ hx)
  haveI : (Z2.subgroupOf N').Normal :=
    Subgroup.normal_of_le_center fun z hz =>
      Subgroup.mem_center_iff.mpr fun x => Subtype.ext (hZc z hz x x.2).symm
  obtain ⟨φN, hgen⟩ := exists_quotient_map_of_isNLift F hD hn
  have hKsurj := quotient_values_of_generators φN hgen
  have hsurj := surjective_quotient_map_of_K F hn φN hKsurj
  have hZ2N : Z2 ≤ N' := hN'eq ▸ le_sup_right
  have hcardquot : Nat.card (↥N' ⧸ Z2.subgroupOf N') ≤ 16 := by
    have hdom : Nat.card (Fin 4 → ZMod 2) = 16 := by
      rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]
      norm_num
    have h := Nat.card_le_card_of_surjective
      (fun v : Fin 4 → ZMod 2 => φN (Multiplicative.ofAdd v)) hsurj
    rwa [hdom] at h
  have hZcard : Nat.card ↥(Z2.subgroupOf N') = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ2N).toEquiv,
      hD.card_center_right]
    norm_num
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z2.subgroupOf N')
  change Nat.card ↥N' ≤ 2 ^ 8
  rw [hcard, hZcard]
  calc Nat.card (↥N' ⧸ Z2.subgroupOf N') * 16 ≤ 16 * 16 :=
        Nat.mul_le_mul_right 16 hcardquot
    _ = 2 ^ 8 := by norm_num

private theorem exists_W_mul_span [Finite G] (F : G24Frame2 L1 L2 S)
    {n : Fin 4 → G} (hn : F.IsNLift n) {x : G}
    (hx : x ∈ dsQ L2 L1 S) :
    ∃ w ∈ F.W, ∃ z ∈ Subgroup.closure (Set.range n) ⊔ centerOf (dsQ L2 L1 S),
      x = w * z := by
  classical
  let Q2 : Subgroup G := dsQ L2 L1 S
  let Z2 : Subgroup G := centerOf (dsQ L2 L1 S)
  let K : Subgroup G := Subgroup.closure (Set.range n)
  let N' : Subgroup G := K ⊔ Z2
  have hnQ : ∀ j, n j ∈ Q2 := fun j => (hn j).choose
  have hqQ : ∀ v : Fin 4 → ZMod 2, eElt n v ∈ Q2 := fun v => eElt_mem_of_forall_mem hnQ v
  have hqN : ∀ v : Fin 4 → ZMod 2, eElt n v ∈ N' := fun v =>
    Subgroup.mem_sup_left
      (eElt_mem_of_forall_mem (fun j => Subgroup.subset_closure (Set.mem_range_self j)) v)
  let v : Fin 4 → ZMod 2 := Multiplicative.toAdd (F.FN.φ ⟨x, hx⟩)
  let w : G := x * (eElt n v)⁻¹
  have hwQ : w ∈ Q2 := Q2.mul_mem hx (Q2.inv_mem (hqQ v))
  have hφw : F.FN.φ ⟨w, hwQ⟩ = 1 := by
    have hsub : (⟨w, hwQ⟩ : ↥Q2) = ⟨x, hx⟩ * (⟨eElt n v, hqQ v⟩)⁻¹ :=
      Subtype.ext rfl
    rw [hsub, map_mul, map_inv]
    apply Multiplicative.toAdd.injective
    have hqφ : Multiplicative.toAdd (F.FN.φ ⟨eElt n v, hqQ v⟩) = v :=
      nLift_fpow_toAdd F hn v
    simp only [toAdd_mul, toAdd_inv, hqφ]
    abel
  have hwW : w ∈ F.W := by
    simpa using (F.FN.ker ⟨w, hwQ⟩).mp hφw
  refine ⟨w, hwW, eElt n v, hqN v, ?_⟩
  show x = w * eElt n v
  dsimp only [w]
  group

private theorem dvd_three_of_actsTrivOnW_pow [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {x : G} (hx : F.ActsTrivOnW x) {m : ℕ}
    (hkm : F.k ^ m = x) : 3 ∣ m := by
  have hk3 : F.k ^ 3 = 1 := by rw [← F.orderOf_k]; exact pow_orderOf_eq_one F.k
  have hk3' : F.k * (F.k * F.k) = 1 := by
    simpa [pow_succ, pow_two, mul_assoc] using hk3
  have hkinv : F.k⁻¹ = F.k * F.k := inv_eq_of_mul_eq_one_right hk3'
  have hk_not : ¬ F.ActsTrivOnW F.k :=
    not_actsTrivOnW_of_fixed_free F hD (g := F.k)
      (fun w hw hfix => F.mem_Z2_of_fixed_on_W hD hw hfix)
  have hkinv_not : ¬ F.ActsTrivOnW F.inv.k :=
    not_actsTrivOnW_of_fixed_free F hD (g := F.inv.k)
      (fun w hw hfix => F.inv.mem_Z2_of_fixed_on_W hD hw hfix)
  have hkm_eq : F.k ^ m = F.k ^ (m % 3) := by
    have h := pow_mod_orderOf F.k m
    rw [F.orderOf_k] at h
    exact h.symm
  have hx' : F.ActsTrivOnW (F.k ^ m) := by rwa [hkm]
  have hxmod : F.ActsTrivOnW (F.k ^ (m % 3)) := by rwa [hkm_eq] at hx'
  have hlt : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases h : m % 3
  · exact Nat.dvd_of_mod_eq_zero h
  · exfalso
    apply hk_not
    simpa [h] using hxmod
  · exfalso
    apply hkinv_not
    have hk2 : F.ActsTrivOnW (F.k ^ 2) := by simpa [h] using hxmod
    have hkinv_eq : F.inv.k = F.k ^ 2 := by
      rw [G24Frame2.inv_k, hkinv, pow_two]
    rwa [hkinv_eq]

private theorem L2_le_Q2_mul_closure_ab [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) :
    ∀ l ∈ L2, ∃ q ∈ dsQ L2 L1 S,
      ∃ c0 ∈ Subgroup.closure ({F.a, F.b} : Set G), l = q * c0 := by
  classical
  let P2 : Subgroup G := L2 ⊔ bigB L1 L2 S
  let Q2 : Subgroup G := dsQ L2 L1 S
  let Z2 : Subgroup G := centerOf (dsQ L2 L1 S)
  let A0 : Subgroup G := Subgroup.closure ({F.a, F.b} : Set G)
  have hQ2P2 : Q2 ≤ P2 := dsQ_le_P_right L1 L2 S
  have hA0P2 : A0 ≤ P2 := by
    intro c hc
    have hcAL : c ∈ F.A ⊓ L2 := F.closure_ab ▸ hc
    exact (le_sup_left : L2 ≤ P2) hcAL.2
  have hAeq : F.A = A0 ⊔ Subgroup.zpowers F.k :=
    F.A_eq_closure_ab_sup_zpowers
  have hk3 : F.k ^ 3 = 1 := by rw [← F.orderOf_k]; exact pow_orderOf_eq_one F.k
  have hk3' : F.k * (F.k * F.k) = 1 := by
    simpa [pow_succ, pow_two, mul_assoc] using hk3
  have hkinv : F.k⁻¹ = F.k * F.k := inv_eq_of_mul_eq_one_right hk3'
  have hk_not : ¬ F.ActsTrivOnW F.k :=
    not_actsTrivOnW_of_fixed_free F hD (g := F.k)
      (fun w hw hfix => F.mem_Z2_of_fixed_on_W hD hw hfix)
  have hkinv_not : ¬ F.ActsTrivOnW F.inv.k :=
    not_actsTrivOnW_of_fixed_free F hD (g := F.inv.k)
      (fun w hw hfix => F.inv.mem_Z2_of_fixed_on_W hD hw hfix)
  intro l hl
  have hlP : l ∈ P2 := (le_sup_left : L2 ≤ P2) hl
  obtain ⟨q, hq, c, hcA, hqc⟩ := F.decomp l hlP
  have hcAeq : c ∈ A0 ⊔ Subgroup.zpowers F.k := hAeq ▸ hcA
  have hcommA : ∀ c0 ∈ A0, ∀ t ∈ Subgroup.zpowers F.k, c0 * t = t * c0 := by
    intro c0 hc0 t ht
    have hc0A : c0 ∈ F.A := by
      have hc0AL : c0 ∈ F.A ⊓ L2 := F.closure_ab ▸ hc0
      exact hc0AL.1
    have hc0k : c0 ∈ Subgroup.centralizer ({F.k} : Set G) := (F.A_le hc0A).2
    have hkc0 : F.k ∈ Subgroup.centralizer ({c0} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hc0k).symm
    have hzp : Subgroup.zpowers F.k ≤ Subgroup.centralizer ({c0} : Set G) :=
      Subgroup.zpowers_le_of_mem hkc0
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hzp ht)).symm
  obtain ⟨c0, hc0, t, ht, hc0t⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcommA hcAeq
  have htpow : t ∈ Submonoid.powers F.k :=
    (isOfFinOrder_of_finite F.k).mem_powers_iff_mem_zpowers.mpr ht
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff t F.k).mp htpow
  have hc0t' : c0 * F.k ^ m = c := by
    rw [← hm] at hc0t
    exact hc0t
  have hqtriv : F.ActsTrivOnW q := F.Q2_actsTrivOnW hD hq
  have hc0L : c0 ∈ L2 := by
    have hc0' : c0 ∈ Subgroup.closure ({F.a, F.b} : Set G) := by
      simpa [A0] using hc0
    exact (F.closure_ab ▸ hc0').2
  have hc0triv : F.ActsTrivOnW c0 := F.L2_actsTrivOnW hc0L
  have hltriv : F.ActsTrivOnW l := F.L2_actsTrivOnW hl
  have hqP : q ∈ P2 := hQ2P2 hq
  have hc0P : c0 ∈ P2 := hA0P2 hc0
  have hqc0triv : F.ActsTrivOnW (q * c0) := F.actsTrivOnW_mul hqtriv hc0triv
  have hqc0P : q * c0 ∈ P2 := P2.mul_mem hqP hc0P
  have hqc0invtriv : F.ActsTrivOnW (q * c0)⁻¹ :=
    F.actsTrivOnW_inv hqc0P hqc0triv
  have hkm : F.k ^ m = (q * c0)⁻¹ * l := by
    rw [hqc, ← hc0t']
    group
  have hkpowtriv : F.ActsTrivOnW (F.k ^ m) := by
    rw [hkm]
    exact F.actsTrivOnW_mul hqc0invtriv hltriv
  have h3m : 3 ∣ m := dvd_three_of_actsTrivOnW_pow F hD hkpowtriv rfl
  obtain ⟨j, hj⟩ := h3m
  have hkm1 : F.k ^ m = 1 := by
    rw [hj, pow_mul, hk3, one_pow]
  refine ⟨q, hq, c0, hc0, ?_⟩
  rw [hqc, ← hc0t', hkm1, mul_one]

private theorem matrix_add_self_add_self (x y : Matrix (Fin 2) (Fin 4) (ZMod 2)) :
    x + y + x + y = 0 := by
  ext i j
  calc x i j + y i j + x i j + y i j = (x i j + y i j) + (x i j + y i j) := by abel
    _ = 0 := CharTwo.add_self_eq_zero _

theorem G24Frame2.nonsplit [Finite G] (F : G24Frame2 L1 L2 S) (hD : G24LocalData L1 L2 S)
    {u : G} {n : Fin 4 → G} {X : Fin 3 → Matrix (Fin 2) (Fin 4) (ZMod 2)} (hu : u ∈ F.W)
    (hu' : u ∉ centerOf (dsQ L2 L1 S)) (hn : F.IsNLift n) (hX : F.IsAct u n X) :
    ¬ ∃ m : Matrix (Fin 2) (Fin 4) (ZMod 2), X 0 = m * aN + m ∧ X 1 = m * bN + m := by
  rintro ⟨m, hm0, hm1⟩
  obtain ⟨hn'0, hX'0⟩ := F.isAct_shift hD hu hu' hn hX m
  let n' : Fin 4 → G := fun j => n j * eElt ![u, F.k * u * F.k⁻¹] fun s => m s j
  let X' : Fin 3 → Matrix (Fin 2) (Fin 4) (ZMod 2) :=
    ![X 0 + m * aN + m, X 1 + m * bN + m, X 2 + m * F.Mk + om * m]
  have hn' : F.IsNLift n' := hn'0
  have hX' : F.IsAct u n' X' := hX'0
  have hzero0 : X' 0 = 0 := by
    show X 0 + m * aN + m = 0
    rw [hm0]
    exact matrix_add_self_add_self (m * aN) m
  have hzero1 : X' 1 = 0 := by
    show X 1 + m * bN + m = 0
    rw [hm1]
    exact matrix_add_self_add_self (m * bN) m
  let Q2 : Subgroup G := dsQ L2 L1 S
  let Z2 : Subgroup G := centerOf (dsQ L2 L1 S)
  let K : Subgroup G := Subgroup.closure (Set.range n')
  let N' : Subgroup G := K ⊔ Z2
  have hn'Q : ∀ j, n' j ∈ Q2 := fun j => (hn' j).choose
  have hKQ : K ≤ Q2 := by
    refine (Subgroup.closure_le (K := Q2)).mpr ?_
    intro x hx
    obtain ⟨j, rfl⟩ := hx
    exact hn'Q j
  have hN'Q : N' ≤ Q2 := sup_le hKQ inf_le_left
  have hcardN : Nat.card ↥N' ≤ 2 ^ 8 := card_closure_sup_centerOf_le F hD hn'
  have ha_norm : F.a ∈ Subgroup.normalizer (N' : Set G) :=
    F.a_mem_normalizer_span hD hn' hX' hzero0
  have hb_norm : F.b ∈ Subgroup.normalizer (N' : Set G) :=
    F.b_mem_normalizer_span hD hn' hX' hzero1
  let A0 : Subgroup G := Subgroup.closure ({F.a, F.b} : Set G)
  have hA0_norm : A0 ≤ Subgroup.normalizer (N' : Set G) := by
    refine (Subgroup.closure_le (K := Subgroup.normalizer (N' : Set G))).mpr ?_
    intro x hx
    rcases hx with rfl | rfl
    · exact ha_norm
    · exact hb_norm
  have hQ2_norm : Q2 ≤ Subgroup.normalizer (N' : Set G) :=
    fun q hq => F.Q2_mem_normalizer_span hD hn' hq
  have hL2_norm : L2 ≤ Subgroup.normalizer (N' : Set G) := by
    intro l hl
    obtain ⟨q, hq, c0, hc0, hlq⟩ := L2_le_Q2_mul_closure_ab F hD l hl
    rw [hlq]
    exact (Subgroup.normalizer (N' : Set G)).mul_mem (hQ2_norm hq) (hA0_norm hc0)
  have hcomm_le : ⁅Q2, L2⁆ ≤ N' := by
    refine Subgroup.commutator_le.mpr ?_
    intro x hx l hl
    obtain ⟨w, hwW, z, hzN, hxwz⟩ := exists_W_mul_span F hn' hx
    have hwQ : w ∈ Q2 := ((F.mem_W w).mp hwW).1
    have hwN : w ∈ Subgroup.normalizer (N' : Set G) := hQ2_norm hwQ
    have hlN : l ∈ Subgroup.normalizer (N' : Set G) := hL2_norm hl
    have hln : l * z * l⁻¹ ∈ N' := (Subgroup.mem_normalizer_iff.mp hlN z).mp hzN
    have hzinv : l * z⁻¹ * l⁻¹ ∈ N' := by
      rw [show l * z⁻¹ * l⁻¹ = (l * z * l⁻¹)⁻¹ by group]
      exact N'.inv_mem hln
    have hzl : ⁅z, l⁆ ∈ N' := by
      rw [commutatorElement_def, show z * l * z⁻¹ * l⁻¹ = z * (l * z⁻¹ * l⁻¹) by group]
      exact N'.mul_mem hzN hzinv
    have hwzl : w * ⁅z, l⁆ * w⁻¹ ∈ N' :=
      (Subgroup.mem_normalizer_iff.mp hwN _).mp hzl
    have hwl : ⁅w, l⁆ ∈ Z2 := ((F.mem_W w).mp hwW).2 l hl
    rw [hxwz, commutatorElement_mul_left_eq_conj_mul]
    exact N'.mul_mem hwzl (Subgroup.mem_sup_right hwl)
  have hQ2le : Q2 ≤ N' := by
    have h := hcomm_le
    rwa [hD.comm_right] at h
  have hcard_le := Subgroup.card_le_of_le hQ2le
  rw [hD.card_right] at hcard_le
  have hcontra : 2 ^ 10 ≤ 2 ^ 8 := le_trans hcard_le hcardN
  norm_num at hcontra

end CFSG.Quasithin.F112R.St84

