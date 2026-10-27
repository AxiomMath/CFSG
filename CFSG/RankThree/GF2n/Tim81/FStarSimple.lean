module

public import CFSG.RankThree.GF2n.Tim81.Components
public import CFSG.RankThree.GF2n.Tim81.ConjugatesInM
public import CFSG.GroupTheory.PrimeCorefreeQuasisimple
public import CFSG.Walter.AStar.Subnormal
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.LocalCores
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}

private theorem mul_ne_one_of_mem_of_components {X Y : Subgroup G} (hinf : X ⊓ Y = ⊥)
    {a b : G} (ha : a ∈ X) (hb : b ∈ Y) (ha1 : a ≠ 1) : a * b ≠ 1 := by
  intro h
  have haY : a ∈ Y := by
    have h' : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [h']; exact Y.inv_mem hb
  exact ha1 (Subgroup.mem_bot.mp (hinf ▸ Subgroup.mem_inf.mpr ⟨ha, haY⟩))

private theorem exists_conjSubgroup_ne_of_not_le_normalizer {H P : Subgroup G}
    (h : ¬ P ≤ Subgroup.normalizer (H : Set G)) :
    ∃ x ∈ P, conjSubgroup x H ≠ H := by
  have hex : ∃ x ∈ P, x ∉ Subgroup.normalizer (H : Set G) := by
    by_contra hcon
    apply h
    intro x hx
    by_contra hxN
    exact hcon ⟨x, hx, hxN⟩
  obtain ⟨x, hxP, hxN⟩ := hex
  exact ⟨x, hxP, fun heq => hxN (mem_normalizer_iff_conjSubgroup_eq.mpr heq)⟩

private theorem normalizes_of_normalizes_of_two_components {X Y : Subgroup G}
    (hXY : X ≠ Y) (hY : IsComponent Y)
    (honly : ∀ Z : Subgroup G, IsComponent Z → Z = X ∨ Z = Y)
    {p : G} (hp : p ∈ Subgroup.normalizer (X : Set G)) :
    p ∈ Subgroup.normalizer (Y : Set G) := by
  rcases honly (conjSubgroup p Y) (isComponent_conjSubgroup hY p) with h | h
  · exfalso
    have hpX : conjSubgroup p X = X := mem_normalizer_iff_conjSubgroup_eq.mp hp
    have h1 : Y = conjSubgroup p⁻¹ X := by
      calc Y = conjSubgroup p⁻¹ (conjSubgroup p Y) := by
              rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
        _ = conjSubgroup p⁻¹ X := by rw [h]
    have h2 : conjSubgroup p⁻¹ X = X := by
      calc conjSubgroup p⁻¹ X = conjSubgroup p⁻¹ (conjSubgroup p X) := by rw [hpX]
        _ = X := by rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
    exact hXY (h1.trans h2).symm
  · exact mem_normalizer_iff_conjSubgroup_eq.mpr h

private theorem conjSubgroup_eq_of_not_normalizes_of_two_components {X Y : Subgroup G}
    (hX : IsComponent X)
    (honly : ∀ Z : Subgroup G, IsComponent Z → Z = X ∨ Z = Y)
    {p : G} (hp : p ∉ Subgroup.normalizer (X : Set G)) :
    conjSubgroup p X = Y := by
  rcases honly (conjSubgroup p X) (isComponent_conjSubgroup hX p) with h | h
  · exact absurd (mem_normalizer_iff_conjSubgroup_eq.mpr h) hp
  · exact h

private theorem conjSubgroup_eq_of_not_normalizes_of_two_components' {X Y : Subgroup G}
    (hXY : X ≠ Y) (hX : IsComponent X) (hY : IsComponent Y)
    (honly : ∀ Z : Subgroup G, IsComponent Z → Z = X ∨ Z = Y)
    {p : G} (hp : p ∉ Subgroup.normalizer (X : Set G)) :
    conjSubgroup p Y = X := by
  have hpX : conjSubgroup p X = Y :=
    conjSubgroup_eq_of_not_normalizes_of_two_components hX honly hp
  rcases honly (conjSubgroup p Y) (isComponent_conjSubgroup hY p) with h | h
  · exact h
  · exfalso
    have h1 : X = conjSubgroup p⁻¹ Y := by
      calc X = conjSubgroup p⁻¹ (conjSubgroup p X) := by
              rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
        _ = conjSubgroup p⁻¹ Y := by rw [hpX]
    have h2 : conjSubgroup p⁻¹ Y = Y := by
      calc conjSubgroup p⁻¹ Y = conjSubgroup p⁻¹ (conjSubgroup p Y) := by rw [h]
        _ = Y := by rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
    exact hXY (h1.trans h2)

private theorem commute_list_prod {ι : Type*} {x : ι → G} {v : G} {l : List ι}
    (h : ∀ i ∈ l, Commute v (x i)) : Commute v ((l.map x).prod) := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.map_cons, List.prod_cons]
      exact (h a (by simp)).mul_right (ih (fun i hi => h i (by simp [hi])))

private theorem list_prod_mul_self_eq_one {ι : Type*} {x : ι → G} {l : List ι}
    (hl : l.Nodup) (hsq : ∀ i ∈ l, x i * x i = 1)
    (hcomm : ∀ i ∈ l, ∀ j ∈ l, i ≠ j → Commute (x i) (x j)) :
    (l.map x).prod * (l.map x).prod = 1 := by
  induction l with
  | nil => simp
  | cons a t ih =>
      obtain ⟨ha_notin, ht_nodup⟩ := List.nodup_cons.mp hl
      have hsq_a : x a * x a = 1 := hsq a (by simp)
      have hsq_t : ∀ i ∈ t, x i * x i = 1 := fun i hi => hsq i (by simp [hi])
      have hcomm_t : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → Commute (x i) (x j) :=
        fun i hi j hj hij => hcomm i (by simp [hi]) j (by simp [hj]) hij
      have hcomm_a_t : Commute (x a) ((t.map x).prod) := by
        refine commute_list_prod fun i hi => ?_
        exact hcomm a (by simp) i (by simp [hi]) (fun h => ha_notin (h ▸ hi))
      have hprod_t : (t.map x).prod * (t.map x).prod = 1 := ih ht_nodup hsq_t hcomm_t
      rw [List.map_cons, List.prod_cons]
      calc (x a * (t.map x).prod) * (x a * (t.map x).prod)
          = (x a * x a) * ((t.map x).prod * (t.map x).prod) :=
            (hcomm_a_t.mul_mul_mul_comm (x a) ((t.map x).prod)).symm
        _ = 1 := by rw [hsq_a, hprod_t, mul_one]

private noncomputable def diagonalHom (X : Subgroup G) (v : G)
    (hcomm : ∀ a b : X, Commute (a : G) (v * (b : G) * v⁻¹)) : X →* G where
  toFun a := (a : G) * (v * (a : G) * v⁻¹)
  map_one' := by simp
  map_mul' := by
    intro a b
    have hcomm_ab : (b : G) * (v * (a : G) * v⁻¹) = (v * (a : G) * v⁻¹) * (b : G) :=
      hcomm b a
    show ((a * b : X) : G) * (v * ((a * b : X) : G) * v⁻¹)
      = ((a : G) * (v * (a : G) * v⁻¹)) * ((b : G) * (v * (b : G) * v⁻¹))
    rw [Subgroup.coe_mul]
    calc (a : G) * (b : G) * (v * ((a : G) * (b : G)) * v⁻¹)
        = (a : G) * ((b : G) * (v * (a : G) * v⁻¹)) * (v * (b : G) * v⁻¹) := by group
      _ = (a : G) * ((v * (a : G) * v⁻¹) * (b : G)) * (v * (b : G) * v⁻¹) := by
          rw [hcomm_ab]
      _ = ((a : G) * (v * (a : G) * v⁻¹)) * ((b : G) * (v * (b : G) * v⁻¹)) := by group

private theorem diagonalHom_apply (X : Subgroup G) (v : G)
    (hcomm : ∀ a b : X, Commute (a : G) (v * (b : G) * v⁻¹)) (a : X) :
    diagonalHom X v hcomm a = (a : G) * (v * (a : G) * v⁻¹) := rfl

namespace Hyp

theorem fittingSubgroup_eq_bot (h : Hyp M V) (hV : 4 ≤ Nat.card V) :
    fittingSubgroup G = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Fitting_eq_pcore G 2 (h.pPrimeCore_eq_bot hV), h.o2]

theorem exists_isComponent (h : Hyp M V) (hV : 4 ≤ Nat.card V) :
    ∃ K : Subgroup G, IsComponent K := by
  by_contra hno
  push Not at hno
  have hlayer : layer G = ⊥ := CFSG.LocalCores.layer_eq_bot_of_forall hno
  have hF : fittingSubgroup G = ⊥ := h.fittingSubgroup_eq_bot hV
  have hFstar : generalizedFitting G = ⊥ := by
    rw [generalizedFitting, hF, hlayer, bot_sup_eq]
  have hVle : V ≤ Subgroup.centralizer (generalizedFitting G : Set G) := by
    rw [hFstar]
    intro v _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy1 : y = 1 := by simpa using hy
    subst hy1
    simp
  have hVle' : V ≤ (⊥ : Subgroup G) := hVle.trans (hFstar ▸ centralizer_generalizedFitting_le G)
  exact h.ne_bot (le_bot_iff.mp hVle')

theorem exists_sylow_le_M (h : Hyp M V) :
    ∃ T : Sylow 2 G, (T : Subgroup G) ≤ M ∧ inSubgroup (pCore 2) M ≤ (T : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 M) := Sylow.nonempty
  obtain ⟨T, hT⟩ := h.isSylow_of_sylow_M S
  refine ⟨T, ?_, ?_⟩
  · rw [hT]
    exact Subgroup.map_subtype_le _
  · rw [hT]
    exact Subgroup.map_mono ((pCore_isPGroup (p := 2) (G := M)).le_sylow_of_normal S)

theorem two_dvd_card_of_isComponent (h : Hyp M V) (hV : 4 ≤ Nat.card V)
    {X : Subgroup G} (hX : IsComponent X) : 2 ∣ Nat.card X := by
  have hcoreG : pPrimeCore 2 G = ⊥ := h.pPrimeCore_eq_bot hV
  have hcoreX : pPrimeCore 2 X = ⊥ := by
    have hle := CFSG.Walter.map_pPrimeCore_le_of_isSubnormal (G := G) hX.2
    rw [hcoreG] at hle
    exact Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective |>.mp
      (le_bot_iff.mp hle)
  obtain ⟨hdvd, -⟩ :=
    CFSG.GroupTheory.prime_corefree_quasisimple_prime_generation hX.1 Nat.prime_two hcoreX
  rw [← Subgroup.index_eq_card] at hdvd
  rw [← Subgroup.card_mul_index (Subgroup.center X)]
  exact dvd_mul_of_dvd_right hdvd _

theorem sylow_inf_component_ne_bot (h : Hyp M V) (hV : 4 ≤ Nat.card V)
    (T : Sylow 2 G) {X : Subgroup G} (hX : IsComponent X) :
    (T : Subgroup G) ⊓ X ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨PX, hPX⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal T hX.2
  have hne : (PX : Subgroup X) ≠ ⊥ := PX.ne_bot_of_dvd_card (h.two_dvd_card_of_isComponent hV hX)
  rw [← hPX]
  intro hbot
  exact hne (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective |>.mp hbot)

private theorem not_le_normalizer_of_isComponent (h : Hyp M V) (hV : 4 ≤ Nat.card V)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    {X Y : Subgroup G} (hX : IsComponent X) (hY : IsComponent Y) (hXY : X ≠ Y) :
    ¬ Pc M V ≤ Subgroup.normalizer (X : Set G) := by
  intro hPN
  have hF : fittingSubgroup G = ⊥ := h.fittingSubgroup_eq_bot hV
  have hSX_ne : (T : Subgroup G) ⊓ X ≠ ⊥ := h.sylow_inf_component_ne_bot hV T hX
  have hSX_M : (T : Subgroup G) ⊓ X ≤ M := inf_le_left.trans hTM
  have hSX_NP : (T : Subgroup G) ⊓ X ≤
      Subgroup.normalizer (Pc M V : Set G) := hSX_M.trans h.le_normalizer_Pc
  have hcomm_le_P : ⁅Pc M V, (T : Subgroup G) ⊓ X⁆ ≤ Pc M V :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp hSX_NP
  have hcomm_le_X : ⁅Pc M V, (T : Subgroup G) ⊓ X⁆ ≤ X :=
    (Subgroup.commutator_mono_right inf_le_right).trans
      ((Subgroup.le_normalizer_iff_commutator_le_right).mp hPN)
  have hPXbot : Pc M V ⊓ X = ⊥ := h.inf_Pc_eq_bot_of_ne hF hX hY hXY
  have hcomm_bot : ⁅Pc M V, (T : Subgroup G) ⊓ X⁆ = ⊥ :=
    le_bot_iff.mp (hPXbot ▸ le_inf hcomm_le_P hcomm_le_X)
  have hP_cent_SX : Pc M V ≤
      Subgroup.centralizer (((T : Subgroup G) ⊓ X) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm_bot
  have hSX_cent : (T : Subgroup G) ⊓ X ≤
      Subgroup.centralizer (Pc M V : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hcomm_bot
  have hSX_V : (T : Subgroup G) ⊓ X ≤ V := by
    calc (T : Subgroup G) ⊓ X
        ≤ Subgroup.centralizer (Pc M V : Set G) := hSX_cent
      _ = V := h.centralizer_Pc
  have hVXbot : V ⊓ X = ⊥ := h.inf_V_eq_bot_of_ne hF hX hY hXY
  exact hSX_ne (le_bot_iff.mp (hVXbot ▸ le_inf hSX_V inf_le_right))

private theorem commutes_of_mem_Pc_of_normalizes (h : Hyp M V) (hV : 4 ≤ Nat.card V)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    {X Y : Subgroup G} (hX : IsComponent X) (hY : IsComponent Y) (hXY : X ≠ Y)
    {p : G} (hpP : p ∈ Pc M V) (hpN : p ∈ Subgroup.normalizer (X : Set G))
    {s : G} (hs : s ∈ (T : Subgroup G) ⊓ X) : p * s = s * p := by
  have hF : fittingSubgroup G = ⊥ := h.fittingSubgroup_eq_bot hV
  have hSX_M : (T : Subgroup G) ⊓ X ≤ M := inf_le_left.trans hTM
  have hSX_NP : (T : Subgroup G) ⊓ X ≤
      Subgroup.normalizer (Pc M V : Set G) := hSX_M.trans h.le_normalizer_Pc
  have hPXbot : Pc M V ⊓ X = ⊥ := h.inf_Pc_eq_bot_of_ne hF hX hY hXY
  have hpsN : s ∈ Subgroup.normalizer (Pc M V : Set G) := hSX_NP hs
  have hpSX : p * s * p⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hpN s).mp hs.2
  have hsp' : s * p⁻¹ * s⁻¹ ∈ Pc M V :=
    (Subgroup.mem_normalizer_iff.mp hpsN p⁻¹).mp ((Pc M V).inv_mem hpP)
  have hcommP : ⁅p, s⁆ ∈ Pc M V := by
    simpa [commutatorElement_def, mul_assoc] using (Pc M V).mul_mem hpP hsp'
  have hcommX : ⁅p, s⁆ ∈ X := by
    simpa [commutatorElement_def, mul_assoc] using X.mul_mem hpSX (X.inv_mem hs.2)
  have hcomm_bot : ⁅p, s⁆ = 1 :=
    Subgroup.mem_bot.mp (hPXbot ▸ Subgroup.mem_inf.mpr ⟨hcommP, hcommX⟩)
  exact commutatorElement_eq_one_iff_mul_comm.mp hcomm_bot

private theorem commute_diagonal_setup (h : Hyp M V) (hV : 4 ≤ Nat.card V)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hQT : inSubgroup (pCore 2) M ≤ (T : Subgroup G))
    {X Y : Subgroup G} (hX : IsComponent X) (hY : IsComponent Y) (hXY : X ≠ Y)
    (honly : ∀ Z : Subgroup G, IsComponent Z → Z = X ∨ Z = Y)
    {x s : G} (hxP : x ∈ Pc M V) (hxSwap : conjSubgroup x X = Y)
    (hs : s ∈ (T : Subgroup G) ⊓ X) :
    Commute x (s * (x * s * x⁻¹)) ∧
      x * s * x⁻¹ ∈ (T : Subgroup G) ⊓ Y ∧
      conjSubgroup x Y = X := by
  have hF : fittingSubgroup G = ⊥ := h.fittingSubgroup_eq_bot hV
  have hsX : s ∈ X := hs.2
  have hsxY : x * s * x⁻¹ ∈ Y := by
    rw [← hxSwap]
    exact mem_conjSubgroup.mpr (by convert hsX using 1; group)
  have hsxT : x * s * x⁻¹ ∈ (T : Subgroup G) :=
    T.mul_mem (T.mul_mem (hQT hxP.1) hs.1) (T.inv_mem (hQT hxP.1))
  have hsx_mem : x * s * x⁻¹ ∈ (T : Subgroup G) ⊓ Y := ⟨hsxT, hsxY⟩
  have hxnotN : x ∉ Subgroup.normalizer (X : Set G) := by
    intro hxN
    exact hXY ((mem_normalizer_iff_conjSubgroup_eq.mp hxN).symm.trans hxSwap)
  have hxSwapY : conjSubgroup x Y = X :=
    conjSubgroup_eq_of_not_normalizes_of_two_components' hXY hX hY honly hxnotN
  have hsx_conj : x * (s * (x * s * x⁻¹)) * x⁻¹ = s * (x * s * x⁻¹) := by
    have hx2P : x * x ∈ Pc M V := (Pc M V).mul_mem hxP hxP
    have hx2swap : conjSubgroup (x * x) X = X := by
      rw [← conjSubgroup_conjSubgroup, hxSwap, hxSwapY]
    have hx2N : x * x ∈ Subgroup.normalizer (X : Set G) :=
      mem_normalizer_iff_conjSubgroup_eq.mpr hx2swap
    have hx2comm : (x * x) * s = s * (x * x) :=
      commutes_of_mem_Pc_of_normalizes h hV T hTM hX hY hXY hx2P hx2N hs
    have hcomm_ssx : Commute s (x * s * x⁻¹) := by
      exact (components_commute_inf hF hX hY hXY).1 s hsX (x * s * x⁻¹) hsxY
    calc x * (s * (x * s * x⁻¹)) * x⁻¹
        = (x * s * x⁻¹) * ((x * x) * s * (x * x)⁻¹) := by group
      _ = (x * s * x⁻¹) * s := by
          rw [show (x * x) * s * (x * x)⁻¹ = s from by
            rw [hx2comm]; group]
      _ = s * (x * s * x⁻¹) := hcomm_ssx.symm
  have hxcomm : Commute x (s * (x * s * x⁻¹)) := by
    rw [Commute]
    calc x * (s * (x * s * x⁻¹))
        = (x * (s * (x * s * x⁻¹)) * x⁻¹) * x := by group
      _ = (s * (x * s * x⁻¹)) * x := by rw [hsx_conj]
  exact ⟨hxcomm, hsx_mem, hxSwapY⟩

private theorem commute_diagonal_of_mem_Pc (h : Hyp M V) (hV : 4 ≤ Nat.card V)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hQT : inSubgroup (pCore 2) M ≤ (T : Subgroup G))
    {X Y : Subgroup G} (hX : IsComponent X) (hY : IsComponent Y) (hXY : X ≠ Y)
    (honly : ∀ Z : Subgroup G, IsComponent Z → Z = X ∨ Z = Y)
    {x s : G} (hxP : x ∈ Pc M V) (hxSwap : conjSubgroup x X = Y)
    (hs : s ∈ (T : Subgroup G) ⊓ X) :
    ∀ p ∈ Pc M V, p * (s * (x * s * x⁻¹)) = (s * (x * s * x⁻¹)) * p := by
  obtain ⟨hxcomm, hsx_mem, hxSwapY⟩ :=
    commute_diagonal_setup h hV T hTM hQT hX hY hXY honly hxP hxSwap hs
  intro p hpP
  by_cases hpN : p ∈ Subgroup.normalizer (X : Set G)
  · have hpNY : p ∈ Subgroup.normalizer (Y : Set G) :=
      normalizes_of_normalizes_of_two_components hXY hY honly hpN
    have hps : p * s = s * p :=
      commutes_of_mem_Pc_of_normalizes h hV T hTM hX hY hXY hpP hpN hs
    have hpsx : p * (x * s * x⁻¹) = (x * s * x⁻¹) * p :=
      commutes_of_mem_Pc_of_normalizes h hV T hTM hY hX hXY.symm hpP hpNY
        (s := x * s * x⁻¹) hsx_mem
    exact (Commute.mul_right (show Commute p s from hps)
      (show Commute p (x * s * x⁻¹) from hpsx)).eq
  · have hpSwap : conjSubgroup p X = Y :=
      conjSubgroup_eq_of_not_normalizes_of_two_components hX honly hpN
    have hpSwapY : conjSubgroup p Y = X :=
      conjSubgroup_eq_of_not_normalizes_of_two_components' hXY hX hY honly hpN
    set n : G := p * x⁻¹ with hn_def
    have hnP : n ∈ Pc M V := (Pc M V).mul_mem hpP ((Pc M V).inv_mem hxP)
    have hxinvY : conjSubgroup x⁻¹ X = Y := by
      have h1 : conjSubgroup x⁻¹ (conjSubgroup x Y) = conjSubgroup x⁻¹ X := by
        rw [hxSwapY]
      rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h1
      exact h1.symm
    have hnX : conjSubgroup n X = X := by
      calc conjSubgroup n X = conjSubgroup p (conjSubgroup x⁻¹ X) := by
              rw [hn_def, conjSubgroup_conjSubgroup]
        _ = conjSubgroup p Y := by rw [hxinvY]
        _ = X := hpSwapY
    have hnN : n ∈ Subgroup.normalizer (X : Set G) :=
      mem_normalizer_iff_conjSubgroup_eq.mpr hnX
    have hnNY : n ∈ Subgroup.normalizer (Y : Set G) :=
      normalizes_of_normalizes_of_two_components hXY hY honly hnN
    have hns : n * s = s * n :=
      commutes_of_mem_Pc_of_normalizes h hV T hTM hX hY hXY hnP hnN hs
    have hnsx : n * (x * s * x⁻¹) = (x * s * x⁻¹) * n :=
      commutes_of_mem_Pc_of_normalizes h hV T hTM hY hX hXY.symm hnP hnNY
        (s := x * s * x⁻¹) hsx_mem
    have hncomm : Commute n (s * (x * s * x⁻¹)) :=
      Commute.mul_right (show Commute n s from hns) (show Commute n (x * s * x⁻¹) from hnsx)
    have hpx : p = n * x := by rw [hn_def]; group
    rw [hpx]
    exact (Commute.mul_left hncomm hxcomm).eq

private theorem only_two_components_setup (h : Hyp M V) (hV : 4 ≤ Nat.card V)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    {X Y' : Subgroup G} (hX : IsComponent X) (hY' : IsComponent Y') (hXY' : X ≠ Y')
    {s x : G} (hsX : s ∈ X) (hsT : s ∈ (T : Subgroup G))
    (hsxY' : x * s * x⁻¹ ∈ Y') (hxP : x ∈ Pc M V) (hs2 : s * s ≠ 1) :
    ∃ t : G, t = s⁻¹ * (x * s * x⁻¹) ∧ t * t ∈ V ∧ t * t ≠ 1 := by
  have hF : fittingSubgroup G = ⊥ := h.fittingSubgroup_eq_bot hV
  have hcomm_ssx : Commute s (x * s * x⁻¹) :=
    (components_commute_inf hF hX hY' hXY').1 s hsX (x * s * x⁻¹) hsxY'
  set t : G := s⁻¹ * (x * s * x⁻¹) with ht_def
  have htP : t ∈ Pc M V := by
    have hsM : s ∈ M := hTM hsT
    have hconj : s⁻¹ * x * s ∈ Pc M V := by
      have hmemN : s⁻¹ ∈ Subgroup.normalizer (Pc M V : Set G) :=
        h.le_normalizer_Pc (M.inv_mem hsM)
      simpa using (Subgroup.mem_normalizer_iff.mp hmemN x).mp hxP
    have ht_eq : t = (s⁻¹ * x * s) * x⁻¹ := by rw [ht_def]; group
    rw [ht_eq]
    exact (Pc M V).mul_mem hconj ((Pc M V).inv_mem hxP)
  have ht2V : t * t ∈ V := by
    have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
    let _ : Fact (IsPGroup 2 (Pc M V)) := ⟨hP2⟩
    have hfr : (⟨t, htP⟩ : Pc M V) ^ 2 ∈ frattini (Pc M V) :=
      CFSG.pth_power_mem_frattini_of_isPGroup (R := Pc M V) (p := 2) ⟨t, htP⟩
    have hfrG : (((⟨t, htP⟩ : Pc M V) ^ 2 : Pc M V) : G) ∈
        inSubgroup frattini (Pc M V) :=
      Subgroup.mem_map_of_mem (Pc M V).subtype hfr
    have hval : (((⟨t, htP⟩ : Pc M V) ^ 2 : Pc M V) : G) = t * t := by
      rw [SubgroupClass.coe_pow, pow_two]
    rw [hval] at hfrG
    exact h.frattini_Pc_le hfrG
  have ht_sq : t * t = (s⁻¹ * s⁻¹) * ((x * s * x⁻¹) * (x * s * x⁻¹)) := by
    calc t * t = (s⁻¹ * (x * s * x⁻¹)) * (s⁻¹ * (x * s * x⁻¹)) := rfl
      _ = s⁻¹ * ((x * s * x⁻¹) * s⁻¹) * (x * s * x⁻¹) := by group
      _ = s⁻¹ * (s⁻¹ * (x * s * x⁻¹)) * (x * s * x⁻¹) := by
          rw [show (x * s * x⁻¹) * s⁻¹ = s⁻¹ * (x * s * x⁻¹) from
            hcomm_ssx.symm.inv_right]
      _ = (s⁻¹ * s⁻¹) * ((x * s * x⁻¹) * (x * s * x⁻¹)) := by group
  have hinv2 : s⁻¹ * s⁻¹ ≠ 1 := by
    intro h1
    apply hs2
    have h2 : (s⁻¹ * s⁻¹)⁻¹ = 1 := by rw [h1, inv_one]
    simpa [mul_inv_rev, inv_inv] using h2
  have ht2ne : t * t ≠ 1 := by
    rw [ht_sq]
    exact mul_ne_one_of_mem_of_components
      ((components_commute_inf hF hX hY' hXY').2)
      (X.mul_mem (X.inv_mem hsX) (X.inv_mem hsX))
      (Y'.mul_mem hsxY' hsxY') hinv2
  exact ⟨t, ht_def, ht2V, ht2ne⟩

private theorem only_two_components_of_four (h : Hyp M V) (hV : 4 ≤ Nat.card V)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    {X Y' : Subgroup G} (hX : IsComponent X) (hY' : IsComponent Y') (hXY' : X ≠ Y')
    {s x : G} (hsX : s ∈ X) (hsT : s ∈ (T : Subgroup G))
    (hsxY' : x * s * x⁻¹ ∈ Y') (hxP : x ∈ Pc M V) (hs2 : s * s ≠ 1) :
    ∀ Z : Subgroup G, IsComponent Z → Z = X ∨ Z = Y' := by
  obtain ⟨t, ht_def, ht2V, ht2ne⟩ :=
    only_two_components_setup h hV T hTM hX hY' hXY' hsX hsT hsxY' hxP hs2
  have hF : fittingSubgroup G = ⊥ := h.fittingSubgroup_eq_bot hV
  intro Z hZ
  by_cases hZX : Z = X
  · exact Or.inl hZX
  · right
    by_contra hZY
    have hz_comm_X := (components_commute_inf hF hZ hX hZX).1
    have hz_comm_Y := (components_commute_inf hF hZ hY' hZY).1
    have hZcent : Z ≤ Subgroup.centralizer ({t * t} : Set G) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have hzs : Commute z s := hz_comm_X z hz s hsX
      have hzsx : Commute z (x * s * x⁻¹) := hz_comm_Y z hz (x * s * x⁻¹) hsxY'
      have hzt : Commute z t := by
        rw [ht_def]
        exact (hzs.inv_right).mul_right hzsx
      exact (hzt.mul_right hzt).eq.symm
    have hZM : Z ≤ M := hZcent.trans (h.centralizer_le_M ht2V ht2ne)
    exact false_of_isComponent_le_of_fitting_eq_pCore hF h.fitting hZ hZM

private theorem sq_eq_one_of_mem_sylow_inf_component (h : Hyp M V) (hV : 4 ≤ Nat.card V)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hQT : inSubgroup (pCore 2) M ≤ (T : Subgroup G))
    {X Y : Subgroup G} (hX : IsComponent X) (hY : IsComponent Y) (hXY : X ≠ Y)
    {s : G} (hs : s ∈ (T : Subgroup G) ⊓ X) : s * s = 1 := by
  by_contra hs2
  have hF : fittingSubgroup G = ⊥ := h.fittingSubgroup_eq_bot hV
  have hPnotN : ¬ Pc M V ≤ Subgroup.normalizer (X : Set G) :=
    not_le_normalizer_of_isComponent h hV T hTM hX hY hXY
  obtain ⟨x, hxP, hxX⟩ := exists_conjSubgroup_ne_of_not_le_normalizer hPnotN
  set Y' : Subgroup G := conjSubgroup x X with hY'_def
  have hY' : IsComponent Y' := isComponent_conjSubgroup hX x
  have hXY' : X ≠ Y' := fun h => hxX h.symm
  have hxSwap : conjSubgroup x X = Y' := rfl
  have hsX : s ∈ X := hs.2
  have hsxY : x * s * x⁻¹ ∈ Y' := by
    change x * s * x⁻¹ ∈ conjSubgroup x X
    exact mem_conjSubgroup.mpr (by convert hsX using 1; group)
  have honly : ∀ Z : Subgroup G, IsComponent Z → Z = X ∨ Z = Y' :=
    only_two_components_of_four h hV T hTM hX hY' hXY' hsX hs.1 hsxY hxP hs2
  have hcomm_all : ∀ p ∈ Pc M V,
      p * (s * (x * s * x⁻¹)) = (s * (x * s * x⁻¹)) * p :=
    commute_diagonal_of_mem_Pc h hV T hTM hQT hX hY' hXY' honly hxP hxSwap hs
  have hcomm_ssx : Commute s (x * s * x⁻¹) :=
    (components_commute_inf hF hX hY' hXY').1 s hsX (x * s * x⁻¹) hsxY
  have hfV : s * (x * s * x⁻¹) ∈ V := by
    rw [← h.centralizer_Pc, Subgroup.mem_centralizer_iff]
    intro p hp
    exact hcomm_all p hp
  have hf2 : (s * (x * s * x⁻¹)) * (s * (x * s * x⁻¹)) = 1 := by
    have hsq := h.elem.2 (s * (x * s * x⁻¹)) hfV
    simpa [pow_two] using hsq
  have hdiag : (s * (x * s * x⁻¹)) * (s * (x * s * x⁻¹))
      = s * s * ((x * s * x⁻¹) * (x * s * x⁻¹)) := by
    calc (s * (x * s * x⁻¹)) * (s * (x * s * x⁻¹))
        = s * ((x * s * x⁻¹) * s) * (x * s * x⁻¹) := by group
      _ = s * (s * (x * s * x⁻¹)) * (x * s * x⁻¹) := by
          rw [show (x * s * x⁻¹) * s = s * (x * s * x⁻¹) from hcomm_ssx.symm]
      _ = s * s * ((x * s * x⁻¹) * (x * s * x⁻¹)) := by group
  have hpair : s * s * ((x * s * x⁻¹) * (x * s * x⁻¹)) = 1 := by
    rw [← hdiag]
    exact hf2
  exact mul_ne_one_of_mem_of_components
    ((components_commute_inf hF hX hY' hXY').2)
    (X.mul_mem hsX hsX) (Y'.mul_mem hsxY hsxY) hs2 hpair

private theorem diagonalHom_injective {X : Subgroup G} {v : G}
    (hcomm : ∀ a b : X, Commute (a : G) (v * (b : G) * v⁻¹))
    (hinf : X ⊓ conjSubgroup v X = ⊥) :
    Function.Injective (diagonalHom X v hcomm) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [eq_bot_iff]
  intro a ha
  rw [MonoidHom.mem_ker, diagonalHom_apply] at ha
  have haY : (a : G) ∈ conjSubgroup v X := by
    have h1 : (a : G) = (v * (a : G) * v⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left ha
    rw [h1]
    exact (conjSubgroup v X).inv_mem (mem_conjSubgroup.mpr (by convert a.2 using 1; group))
  have ha1 : (a : G) = 1 :=
    Subgroup.mem_bot.mp (hinf ▸ Subgroup.mem_inf.mpr ⟨a.2, haY⟩)
  exact Subtype.ext ha1

private theorem diagonalHom_range_le_M (h : Hyp M V)
    {X : Subgroup G} {v : G} (hvV : v ∈ V) (hv1 : v ≠ 1)
    (hcomm : ∀ a b : X, Commute (a : G) (v * (b : G) * v⁻¹)) :
    (diagonalHom X v hcomm).range ≤ M := by
  have hv2 : v * v = 1 := by simpa [pow_two] using h.elem.2 v hvV
  have hv2inv : v⁻¹ * v⁻¹ = 1 := by
    rw [← mul_inv_rev, hv2, inv_one]
  intro y hy
  obtain ⟨a, rfl⟩ := hy
  have hcent : diagonalHom X v hcomm a ∈ Subgroup.centralizer ({v} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst w
    have hconj : v * diagonalHom X v hcomm a * v⁻¹ = diagonalHom X v hcomm a := by
      have hcomm_a : Commute (a : G) (v * (a : G) * v⁻¹) := hcomm a a
      rw [diagonalHom_apply]
      calc v * ((a : G) * (v * (a : G) * v⁻¹)) * v⁻¹
          = (v * (a : G) * v⁻¹) * (v * v * (a : G) * (v⁻¹ * v⁻¹)) := by group
        _ = (v * (a : G) * v⁻¹) * (a : G) := by rw [hv2, hv2inv]; group
        _ = (a : G) * (v * (a : G) * v⁻¹) := hcomm_a.symm
    show v * diagonalHom X v hcomm a = diagonalHom X v hcomm a * v
    calc v * diagonalHom X v hcomm a
        = (v * diagonalHom X v hcomm a * v⁻¹) * v := by group
      _ = diagonalHom X v hcomm a * v := by rw [hconj]
  exact h.centralizer_le_M hvV hv1 hcent

private theorem diagonal_range_contradiction_setup (h : Hyp M V) (hV : 4 ≤ Nat.card V)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hQT : inSubgroup (pCore 2) M ≤ (T : Subgroup G))
    {X Y : Subgroup G} (hX : IsComponent X) (hY : IsComponent Y) (hXY : X ≠ Y)
    {v : G} (hvV : v ∈ V) (f : X →* G) (hfinj : Function.Injective f)
    (hfeq : ∀ a : X, f a = (a : G) * (v * (a : G) * v⁻¹)) :
    f.range ⊓ V ≠ ⊥ := by
  obtain ⟨⟨s, hsSX⟩, hs1'⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (h.sylow_inf_component_ne_bot hV T hX)
  have hs1 : s ≠ 1 := fun h => hs1' (Subtype.ext h)
  have hs2 : s * s = 1 :=
    sq_eq_one_of_mem_sylow_inf_component h hV T hTM hQT hX hY hXY hsSX
  have hfsV : f ⟨s, hsSX.2⟩ ∈ V := by
    have hsN : s ∈ Subgroup.normalizer (V : Set G) := h.le_normalizer (hTM hsSX.1)
    have hconjV : s * v * s⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hsN v).mp hvV
    have hfs : f ⟨s, hsSX.2⟩ = ⁅s, v⁆ := by
      rw [hfeq ⟨s, hsSX.2⟩]
      show s * (v * s * v⁻¹) = s * v * s⁻¹ * v⁻¹
      rw [show s⁻¹ = s from inv_eq_of_mul_eq_one_right hs2]
      group
    rw [hfs]
    dsimp [commutatorElement_def]
    exact V.mul_mem hconjV (V.inv_mem hvV)
  have hfs_ne : f ⟨s, hsSX.2⟩ ≠ 1 := by
    intro h1
    have h2 : (⟨s, hsSX.2⟩ : X) = 1 := hfinj (by simpa using h1)
    exact hs1 (congrArg Subtype.val h2)
  have hNV : f.range ⊓ V ≠ ⊥ := by
    intro hbot
    have hmem : f ⟨s, hsSX.2⟩ ∈ f.range ⊓ V :=
      ⟨⟨⟨s, hsSX.2⟩, rfl⟩, hfsV⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hfs_ne hmem
  exact hNV

private theorem diagonal_range_contradiction (h : Hyp M V) (hV : 4 ≤ Nat.card V)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hQT : inSubgroup (pCore 2) M ≤ (T : Subgroup G))
    {X Y : Subgroup G} (hX : IsComponent X) (hY : IsComponent Y) (hXY : X ≠ Y)
    {v : G} (hvV : v ∈ V) (f : X →* G)
    (hfinj : Function.Injective f) (hfM : f.range ≤ M)
    (hfeq : ∀ a : X, f a = (a : G) * (v * (a : G) * v⁻¹))
    (hsimple : IsSimpleGroup f.range)
    (hnab : ∃ a b : f.range, a * b ≠ b * a) : False := by
  have hNV : f.range ⊓ V ≠ ⊥ :=
    diagonal_range_contradiction_setup h hV T hTM hQT hX hY hXY hvV f hfinj hfeq
  let N : Subgroup f.range := (f.range ⊓ V).subgroupOf f.range
  have hNnormal : N.Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr ?_
    intro g hg
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, h.le_normalizer (hfM hg)⟩
  haveI : N.Normal := hNnormal
  rcases hsimple.eq_bot_or_eq_top_of_normal N with hNbot | hNtop
  · have hinfbot : f.range ⊓ V = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxN : (⟨x, hx.1⟩ : f.range) ∈ N := Subgroup.mem_subgroupOf.mpr hx
      rw [hNbot, Subgroup.mem_bot] at hxN
      exact Subtype.ext_iff.mp hxN
    exact hNV hinfbot
  · have hXhat_le_V : f.range ≤ V := by
      intro x hx
      have hxN : (⟨x, hx⟩ : f.range) ∈ N := by rw [hNtop]; exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp hxN).2
    have hXhat_ab : IsMulCommutative f.range := by
      refine ⟨⟨fun a b => ?_⟩⟩
      apply Subtype.ext
      show (a : G) * (b : G) = (b : G) * (a : G)
      exact congrArg Subtype.val (h.maxAb.prop.2.2.is_comm.comm
        ⟨a, hXhat_le_V a.2⟩ ⟨b, hXhat_le_V b.2⟩)
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (Subtype.ext (congrArg Subtype.val (hXhat_ab.is_comm.comm a b)))

private theorem le_normalizer_of_isComponent (h : Hyp M V) (hV : 4 ≤ Nat.card V)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hQT : inSubgroup (pCore 2) M ≤ (T : Subgroup G))
    {X Y : Subgroup G} (hX : IsComponent X) (hY : IsComponent Y) (hXY : X ≠ Y) :
    V ≤ Subgroup.normalizer (X : Set G) := by
  intro v hvV
  by_contra hnotN
  have hF : fittingSubgroup G = ⊥ := h.fittingSubgroup_eq_bot hV
  have hne : conjSubgroup v X ≠ X := fun h => hnotN (mem_normalizer_iff_conjSubgroup_eq.mpr h)
  set Y' : Subgroup G := conjSubgroup v X with hY'_def
  have hY' : IsComponent Y' := isComponent_conjSubgroup hX v
  have hXY' : X ≠ Y' := fun h => hne h.symm
  have hv1 : v ≠ 1 := by
    intro hv
    apply hne
    rw [hY'_def, hv, conjSubgroup_one]
  have hcomm : ∀ (a : X) (b : X), Commute (a : G) (v * (b : G) * v⁻¹) := by
    intro a b
    exact (components_commute_inf hF hX hY' hXY').1 (a : G) a.2 (v * (b : G) * v⁻¹)
      (by
        rw [hY'_def]
        exact mem_conjSubgroup.mpr (by convert b.2 using 1; group))
  let f : X →* G := diagonalHom X v hcomm
  have hfeq : ∀ a : X, f a = (a : G) * (v * (a : G) * v⁻¹) :=
    fun a => diagonalHom_apply X v hcomm a
  have hfinj : Function.Injective f :=
    diagonalHom_injective hcomm ((components_commute_inf hF hX hY' hXY').2)
  have hfM : f.range ≤ M := diagonalHom_range_le_M h hvV hv1 hcomm
  let e : X ≃* f.range := MonoidHom.ofInjective hfinj
  have hXhat_simple : IsSimpleGroup f.range :=
    (e.isSimpleGroup_congr).1 (component_isSimple hF hX).1
  have hXhat_nab : ∃ a b : f.range, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := (component_isSimple hF hX).2
    refine ⟨e a, e b, fun h => hab (e.injective ?_)⟩
    rw [map_mul, map_mul, h]
  obtain ⟨⟨s, hsSX⟩, hs1'⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (h.sylow_inf_component_ne_bot hV T hX)
  have hs1 : s ≠ 1 := fun h => hs1' (Subtype.ext h)
  have hs2 : s * s = 1 :=
    sq_eq_one_of_mem_sylow_inf_component h hV T hTM hQT hX hY hXY hsSX
  exact diagonal_range_contradiction h hV T hTM hQT hX hY hXY hvV f hfinj hfM hfeq
    hXhat_simple hXhat_nab

private theorem commutator_V_sylow_inf_component_eq_bot (h : Hyp M V) (hV : 4 ≤ Nat.card V)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hQT : inSubgroup (pCore 2) M ≤ (T : Subgroup G))
    {X Y : Subgroup G} (hX : IsComponent X) (hY : IsComponent Y) (hXY : X ≠ Y) :
    ⁅V, (T : Subgroup G) ⊓ X⁆ = ⊥ := by
  have hF : fittingSubgroup G = ⊥ := h.fittingSubgroup_eq_bot hV
  have hVX : V ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_of_isComponent h hV T hTM hQT hX hY hXY
  have hSX_M : (T : Subgroup G) ⊓ X ≤ M := inf_le_left.trans hTM
  have hSX_NV : (T : Subgroup G) ⊓ X ≤
      Subgroup.normalizer (V : Set G) := hSX_M.trans h.le_normalizer
  have hcomm_le_V : ⁅V, (T : Subgroup G) ⊓ X⁆ ≤ V :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp hSX_NV
  have hcomm_le_X : ⁅V, (T : Subgroup G) ⊓ X⁆ ≤ X :=
    (Subgroup.commutator_mono_right inf_le_right).trans
      ((Subgroup.le_normalizer_iff_commutator_le_right).mp hVX)
  have hVXbot : V ⊓ X = ⊥ := h.inf_V_eq_bot_of_ne hF hX hY hXY
  exact le_bot_iff.mp (hVXbot ▸ le_inf hcomm_le_V hcomm_le_X)

private theorem mem_sylow_of_layerMul_eq_coord (T : Sylow 2 G)
    {e : G} (heT : e ∈ (T : Subgroup G)) (heL : e ∈ layer G)
    {x : ∀ K : ComponentIndex G, K.1} (hx : layerMul G x = e)
    (hinj : Function.Injective (layerMul G)) :
    ∀ K : ComponentIndex G, (x K : G) ∈ (T : Subgroup G) := by
  let S0 : Subgroup G := (T : Subgroup G) ⊓ layer G
  let P0 : Subgroup (∀ K : ComponentIndex G, K.1) :=
    Subgroup.comap (layerMul G) S0
  have hS02 : IsPGroup 2 S0 := T.isPGroup'.to_le inf_le_left
  have hP02 : IsPGroup 2 P0 := by
    intro y
    obtain ⟨k, hk⟩ := hS02 ⟨layerMul G y, y.2⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    apply hinj
    rw [SubgroupClass.coe_pow, map_pow]
    have hk' : ((layerMul G y) : G) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    simpa using hk'
  intro K
  let π : (∀ K : ComponentIndex G, K.1) →* K.1 := Pi.evalMonoidHom _ K
  have hπ2 : IsPGroup 2 (P0.map π) := hP02.map π
  obtain ⟨PX, hPX⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal T K.2.2
  have hPXle : (PX : Subgroup K.1) ≤ P0.map π := by
    intro u hu
    refine ⟨Pi.mulSingle K u, ?_, ?_⟩
    · change layerMul G (Pi.mulSingle K u) ∈ S0
      rw [CFSG.LocalCores.layerMul_mulSingle]
      refine ⟨?_, ?_⟩
      · have huTK : (u : G) ∈ (T : Subgroup G) ⊓ K.1 := by
          rw [← hPX]
          exact Subgroup.mem_map_of_mem K.1.subtype hu
        exact huTK.1
      · exact CFSG.LocalCores.component_le_layer K.2 u.2
    · simp [π]
  have hP0eq : P0.map π = PX := PX.is_maximal' hπ2 hPXle
  have hxP0 : x ∈ P0 := by
    rw [Subgroup.mem_comap, hx]
    exact ⟨heT, heL⟩
  have hxPX : π x ∈ PX := by
    have h := Subgroup.mem_map_of_mem π hxP0
    rwa [hP0eq] at h
  have hxT : (π x : G) ∈ (T : Subgroup G) := by
    have hxTK : (π x : G) ∈ (T : Subgroup G) ⊓ K.1 := by
      rw [← hPX]
      exact Subgroup.mem_map_of_mem K.1.subtype hxPX
    exact hxTK.1
  simpa [π] using hxT

private theorem mem_sylow_of_layerMul_eq (h : Hyp M V) (hV : 4 ≤ Nat.card V)
    (T : Sylow 2 G)
    {e : G} (heT : e ∈ (T : Subgroup G)) (heL : e ∈ layer G)
    {x : ∀ K : ComponentIndex G, K.1} (hx : layerMul G x = e) :
    ∀ K : ComponentIndex G, (x K : G) ∈ (T : Subgroup G) := by
  have hF : fittingSubgroup G = ⊥ := h.fittingSubgroup_eq_bot hV
  have hker : (layerMul G).ker = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    funext K
    have hyK := CFSG.LocalCores.layerMul_ker_le hy K (Set.mem_univ K)
    have hbot : Subgroup.center K.1 = ⊥ := center_component_eq_bot hF K.2
    have hyK' : y K ∈ Subgroup.center K.1 := hyK
    have hy1 : (y K : G) = 1 := by
      have hmem : y K ∈ (⊥ : Subgroup K.1) := hbot ▸ hyK'
      exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
    exact Subtype.ext hy1
  have hinj : Function.Injective (layerMul G) :=
    (MonoidHom.ker_eq_bot_iff (layerMul G)).mp hker
  exact mem_sylow_of_layerMul_eq_coord T heT heL hx hinj

private theorem sq_eq_one_of_mem_sylow_inf_layer (h : Hyp M V) (hV : 4 ≤ Nat.card V)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hQT : inSubgroup (pCore 2) M ≤ (T : Subgroup G))
    {X Y : Subgroup G} (hX : IsComponent X) (hY : IsComponent Y) (hXY : X ≠ Y) :
    ∀ e ∈ (T : Subgroup G) ⊓ layer G, e * e = 1 := by
  have hF : fittingSubgroup G = ⊥ := h.fittingSubgroup_eq_bot hV
  have hother : ∀ K : ComponentIndex G, ∃ L : Subgroup G, IsComponent L ∧ K.1 ≠ L := by
    intro K
    by_cases hKX : K.1 = X
    · exact ⟨Y, hY, fun h => hXY (hKX.symm.trans h)⟩
    · exact ⟨X, hX, hKX⟩
  intro e he
  have heT : e ∈ (T : Subgroup G) := he.1
  have heL : e ∈ layer G := he.2
  obtain ⟨x, hx⟩ := CFSG.LocalCores.exists_layerMul_eq heL
  let l : List (ComponentIndex G) := (Finset.univ : Finset (ComponentIndex G)).toList
  have hl_nodup : l.Nodup := Finset.nodup_toList _
  have hl_mem : ∀ K : ComponentIndex G, K ∈ l := fun K =>
    Finset.mem_toList.mpr (Finset.mem_univ K)
  have hprod : e = (l.map fun K => (x K : G)).prod := by
    rw [← hx, CFSG.LocalCores.layerMul_eq_prod x hl_nodup hl_mem]
  have hxT : ∀ K, (x K : G) ∈ (T : Subgroup G) :=
    mem_sylow_of_layerMul_eq h hV T heT heL hx
  have hsq : ∀ K ∈ l, (x K : G) * (x K : G) = 1 := by
    intro K _
    obtain ⟨L, hL, hKL⟩ := hother K
    exact sq_eq_one_of_mem_sylow_inf_component h hV T hTM hQT K.2 hL hKL
      ⟨hxT K, (x K).2⟩
  have hcomm : ∀ K ∈ l, ∀ L ∈ l, K ≠ L → Commute (x K : G) (x L : G) := by
    intro K _ L _ hKL
    exact (components_commute_inf hF K.2 L.2 (fun h => hKL (Subtype.ext h))).1
      (x K : G) (x K).2 (x L : G) (x L).2
  rw [hprod]
  exact list_prod_mul_self_eq_one hl_nodup hsq hcomm

private theorem V_le_centralizer_sylow_inf_layer (h : Hyp M V) (hV : 4 ≤ Nat.card V)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hQT : inSubgroup (pCore 2) M ≤ (T : Subgroup G))
    {X Y : Subgroup G} (hX : IsComponent X) (hY : IsComponent Y) (hXY : X ≠ Y) :
    V ≤ Subgroup.centralizer (((T : Subgroup G) ⊓ layer G) : Set G) := by
  have hother : ∀ K : ComponentIndex G, ∃ L : Subgroup G, IsComponent L ∧ K.1 ≠ L := by
    intro K
    by_cases hKX : K.1 = X
    · exact ⟨Y, hY, fun h => hXY (hKX.symm.trans h)⟩
    · exact ⟨X, hX, hKX⟩
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have heT : e ∈ (T : Subgroup G) := he.1
  have heL : e ∈ layer G := he.2
  obtain ⟨x, hx⟩ := CFSG.LocalCores.exists_layerMul_eq heL
  let l : List (ComponentIndex G) := (Finset.univ : Finset (ComponentIndex G)).toList
  have hl_nodup : l.Nodup := Finset.nodup_toList _
  have hl_mem : ∀ K : ComponentIndex G, K ∈ l := fun K =>
    Finset.mem_toList.mpr (Finset.mem_univ K)
  have hprod : e = (l.map fun K => (x K : G)).prod := by
    rw [← hx, CFSG.LocalCores.layerMul_eq_prod x hl_nodup hl_mem]
  have hxT : ∀ K, (x K : G) ∈ (T : Subgroup G) :=
    mem_sylow_of_layerMul_eq h hV T heT heL hx
  have hcomm : ∀ K ∈ l, Commute v (x K : G) := by
    intro K _
    obtain ⟨L, hL, hKL⟩ := hother K
    have hbot : ⁅V, (T : Subgroup G) ⊓ K.1⁆ = ⊥ :=
      commutator_V_sylow_inf_component_eq_bot h hV T hTM hQT K.2 hL hKL
    have hVcent : V ≤ Subgroup.centralizer (((T : Subgroup G) ⊓ K.1) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    exact ((Subgroup.mem_centralizer_iff.mp (hVcent hv)) (x K) ⟨hxT K, (x K).2⟩).symm
  rw [hprod]
  exact (commute_list_prod hcomm).symm

private theorem sylow_inf_layer_isElemAbelian (h : Hyp M V) (hV : 4 ≤ Nat.card V)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hQT : inSubgroup (pCore 2) M ≤ (T : Subgroup G))
    {X Y : Subgroup G} (hX : IsComponent X) (hY : IsComponent Y) (hXY : X ≠ Y) :
    Assembly.IsElemAbelian 2 ((T : Subgroup G) ⊓ layer G) := by
  have hsq := sq_eq_one_of_mem_sylow_inf_layer h hV T hTM hQT hX hY hXY
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun e he => ?_⟩
  · have hab : ((a : G) * (b : G)) * ((a : G) * (b : G)) = 1 :=
      hsq ((a : G) * (b : G)) (mul_mem a.2 b.2)
    have hai : (a : G)⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a a.2)
    have hbi : (b : G)⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b b.2)
    apply Subtype.ext
    have hcomm : ⁅(a : G), (b : G)⁆ = 1 := by
      rw [commutatorElement_def, hai, hbi]
      simpa [mul_assoc] using hab
    exact commutatorElement_eq_one_iff_mul_comm.mp hcomm
  · have h := hsq e he
    simpa [pow_two] using h

private theorem commutator_Pc_sylow_inf_layer_aux (h : Hyp M V) (hV : 4 ≤ Nat.card V)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hQT : inSubgroup (pCore 2) M ≤ (T : Subgroup G))
    {X Y : Subgroup G} (hX : IsComponent X) (hY : IsComponent Y) (hXY : X ≠ Y) :
    Pc M V ⊓ layer G ≤ V := by
  haveI hlayerChar : (layer G).Characteristic := CFSG.LocalCores.layer_characteristic
  let P : Subgroup G := Pc M V
  let S0 : Subgroup G := (T : Subgroup G) ⊓ layer G
  let PS : Subgroup G := P ⊓ layer G
  have hPT : P ≤ (T : Subgroup G) := fun x hx => hQT hx.1
  have hS0_M : S0 ≤ M := inf_le_left.trans hTM
  have hPS_M : PS ≤ M := inf_le_left.trans h.Pc_le_M
  have hM_layer : M ≤ Subgroup.normalizer ((layer G : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (layer G).Normal)]
    exact le_top
  have hM_PS : M ≤ Subgroup.normalizer (PS : Set G) := by
    intro m hm
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨h.le_normalizer_Pc hm, hM_layer hm⟩
  have hS0elem : Assembly.IsElemAbelian 2 S0 :=
    sylow_inf_layer_isElemAbelian h hV T hTM hQT hX hY hXY
  haveI hS0class : IsElementaryAbelian 2 S0 :=
    { toIsMulCommutative := hS0elem.1
      exponent_dvd_p :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x =>
          Subtype.ext (by simpa using hS0elem.2 (x : G) x.2) }
  have hPS_le_S0 : PS ≤ S0 := by
    show P ⊓ layer G ≤ (T : Subgroup G) ⊓ layer G
    exact inf_le_inf hPT le_rfl
  haveI hPSclass : IsElementaryAbelian 2 PS := CFSG.IsElementaryAbelian.of_le hS0class hPS_le_S0
  haveI hVclass : IsElementaryAbelian 2 V :=
    { toIsMulCommutative := h.maxAb.prop.2.2
      exponent_dvd_p :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x =>
          Subtype.ext (by simpa using h.elem.2 (x : G) x.2) }
  have hVS0 : V ≤ Subgroup.centralizer (S0 : Set G) :=
    V_le_centralizer_sylow_inf_layer h hV T hTM hQT hX hY hXY
  have hPS_cent_V : PS ≤ Subgroup.centralizer (V : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact ((Subgroup.mem_centralizer_iff.mp (hVS0 hv)) x (hPS_le_S0 hx)).symm
  have hVPS_elem : IsElementaryAbelian 2 ↥(V ⊔ PS : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer (p := 2) (E := V) (C := PS) hPS_cent_V
  have hVPS_ab : IsMulCommutative ↥(V ⊔ PS : Subgroup G) := hVPS_elem.toIsMulCommutative
  have hVPS_M : V ⊔ PS ≤ M := sup_le h.le_M hPS_M
  have hM_VPS : M ≤ Subgroup.normalizer ((V ⊔ PS : Subgroup G) : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup]
    change Subgroup.map (MulAut.conj m).toMonoidHom V ⊔
      Subgroup.map (MulAut.conj m).toMonoidHom PS = V ⊔ PS
    rw [Quasithin.MS93.map_conj_eq_of_mem_normalizer (h.le_normalizer hm),
      Quasithin.MS93.map_conj_eq_of_mem_normalizer (hM_PS hm)]
  have hmax : V ⊔ PS ≤ V :=
    h.maxAb.le_of_ge ⟨hVPS_M, hM_VPS, hVPS_ab⟩ le_sup_left
  have hPS_le_V : PS ≤ V := le_sup_right.trans hmax
  exact hPS_le_V

private theorem commutator_Pc_sylow_inf_layer_le_V (h : Hyp M V) (hV : 4 ≤ Nat.card V)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hQT : inSubgroup (pCore 2) M ≤ (T : Subgroup G))
    {X Y : Subgroup G} (hX : IsComponent X) (hY : IsComponent Y) (hXY : X ≠ Y) :
    ⁅Pc M V, (T : Subgroup G) ⊓ layer G⁆ ≤ V := by
  have hPT : Pc M V ≤ (T : Subgroup G) := fun x hx => hQT hx.1
  have hS0_M : (T : Subgroup G) ⊓ layer G ≤ M := inf_le_left.trans hTM
  have hPS_le_V : Pc M V ⊓ layer G ≤ V :=
    commutator_Pc_sylow_inf_layer_aux h hV T hTM hQT hX hY hXY
  haveI hlayerChar : (layer G).Characteristic := CFSG.LocalCores.layer_characteristic
  have hM_layer : M ≤ Subgroup.normalizer ((layer G : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (layer G).Normal)]
    exact le_top
  have hT_S0 : (T : Subgroup G) ≤
      Subgroup.normalizer (((T : Subgroup G) ⊓ layer G) : Set G) := by
    intro t ht
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer ht, hM_layer (hTM ht)⟩
  have hcomm_le_P : ⁅Pc M V, (T : Subgroup G) ⊓ layer G⁆ ≤ Pc M V :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp (hS0_M.trans h.le_normalizer_Pc)
  have hcomm_le_S0 :
      ⁅Pc M V, (T : Subgroup G) ⊓ layer G⁆ ≤ (T : Subgroup G) ⊓ layer G :=
    (Subgroup.le_normalizer_iff_commutator_le_right).mp (hPT.trans hT_S0)
  have hPS'_le_V : Pc M V ⊓ ((T : Subgroup G) ⊓ layer G) ≤ V :=
    (le_inf inf_le_left (inf_le_right.trans inf_le_right)).trans hPS_le_V
  exact (le_inf hcomm_le_P hcomm_le_S0).trans hPS'_le_V

private theorem sylow_inf_layer_le_Pc (h : Hyp M V) (hV : 4 ≤ Nat.card V)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hQT : inSubgroup (pCore 2) M ≤ (T : Subgroup G))
    {X Y : Subgroup G} (hX : IsComponent X) (hY : IsComponent Y) (hXY : X ≠ Y) :
    (T : Subgroup G) ⊓ layer G ≤ Pc M V := by
  let S0 : Subgroup G := (T : Subgroup G) ⊓ layer G
  have hS0_M : S0 ≤ M := inf_le_left.trans hTM
  have hVS0 : V ≤ Subgroup.centralizer (S0 : Set G) :=
    V_le_centralizer_sylow_inf_layer h hV T hTM hQT hX hY hXY
  have hS0_V : S0 ≤ Subgroup.centralizer (V : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact ((Subgroup.mem_centralizer_iff.mp (hVS0 hv)) s hs).symm
  have hS0Q : S0 ≤ inSubgroup (pCore 2) M :=
    h.le_pCore_of_commutator_le hS0_M hS0_V
      (commutator_Pc_sylow_inf_layer_le_V h hV T hTM hQT hX hY hXY)
  exact le_inf hS0Q hS0_V

private theorem false_of_isComponent_ne (h : Hyp M V) (hV : 4 ≤ Nat.card V)
    {X Y : Subgroup G} (hX : IsComponent X) (hY : IsComponent Y) (hXY : X ≠ Y) : False := by
  obtain ⟨T, hTM, hQT⟩ := h.exists_sylow_le_M
  have hS0_le_P : (T : Subgroup G) ⊓ layer G ≤ Pc M V :=
    sylow_inf_layer_le_Pc h hV T hTM hQT hX hY hXY
  have hSX_le_S0 : (T : Subgroup G) ⊓ X ≤ (T : Subgroup G) ⊓ layer G :=
    inf_le_inf_left _ (CFSG.LocalCores.component_le_layer hX)
  have hSX_le_P : (T : Subgroup G) ⊓ X ≤ Pc M V := hSX_le_S0.trans hS0_le_P
  have hbot : Pc M V ⊓ X = ⊥ :=
    h.inf_Pc_eq_bot_of_ne (h.fittingSubgroup_eq_bot hV) hX hY hXY
  have hSX_bot : (T : Subgroup G) ⊓ X = ⊥ :=
    le_bot_iff.mp (hbot ▸ le_inf hSX_le_P inf_le_right)
  exact h.sylow_inf_component_ne_bot hV T hX hSX_bot

theorem unique_component (h : Hyp M V) (hV : 4 ≤ Nat.card V)
    {K L : Subgroup G} (hK : IsComponent K) (hL : IsComponent L) : L = K := by
  by_contra hne
  exact false_of_isComponent_ne h hV hK hL (fun h => hne h.symm)

theorem isSimpleGroup_generalizedFitting (h : Hyp M V) (hV : 4 ≤ Nat.card V) :
    IsSimpleGroup (generalizedFitting G) ∧ ∃ a b : generalizedFitting G, a * b ≠ b * a := by
  obtain ⟨K, hK⟩ := h.exists_isComponent hV
  exact generalizedFitting_simple_of_unique (h.fittingSubgroup_eq_bot hV) hK
    (fun L hL => h.unique_component hV hK hL)

end Hyp

end CFSG.RankThree.GF2n.Tim81

