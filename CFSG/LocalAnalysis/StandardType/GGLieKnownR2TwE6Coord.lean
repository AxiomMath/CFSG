module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Comm

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg.Minuscule
open scoped commutatorElement

@[expose] def IsTwE6Coord
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    (Φ : fixedGroup k θ → (Fin 8 → k)) : Prop :=
  (∀ g ∈ twE6Rad θ, ∀ h ∈ twE6Rad θ, Φ (g * h) = Φ g + Φ h) ∧
    (∀ g ∈ twE6Rad θ, (Φ g = 0 ↔ g ∈ twE6Cen θ)) ∧
    (∀ (i : Fin 8) (c : k), Φ (twE6X θ hθ i c) = Pi.single i c)

private theorem twE6Gamma_last (i : Fin 8) : twE6Gamma i twE6Last = 1 := by
  fin_cases i <;> decide +kernel

private theorem twE6Gamma_isRoot
    (i : Fin 8) : IsRoot .F4 (twE6Gamma i) := by
  rw [← twE6_proj_lift i]
  exact isRoot_proj (twE6Lift_isRoot i)

private def twE6L2vec : Fin 7 → (Fin (Tag.rank .F4) → ℤ) :=
  ![![0, 1, 2, 2], ![1, 1, 2, 2], ![1, 2, 2, 2], twE6Alpha, ![1, 2, 4, 2], ![1, 3, 4, 2],
    ![2, 3, 4, 2]]

private theorem twE6L2vec_isRoot
    (i : Fin 7) : IsRoot .F4 (twE6L2vec i) :=
  (StringData.memDec_iff (Tag.rootCertificate_check .F4) (Tag.stringData_check .F4)).1 (by
    change memF4 (twE6L2vec i) = true
    fin_cases i <;> decide +kernel)

private theorem twE6L2vec_last (i : Fin 7) : twE6L2vec i twE6Last = 2 := by
  fin_cases i <;> decide +kernel

private def twE6Q0List : List (Fin (Tag.rank .F4) → ℤ) :=
  [twE6Gamma 0, twE6Gamma 1, twE6Gamma 2, twE6Gamma 3, twE6Gamma 4, twE6Gamma 5,
   twE6L2vec 0, twE6Gamma 6, twE6L2vec 1, twE6Gamma 7, twE6L2vec 2, twE6L2vec 3,
   twE6L2vec 4, twE6L2vec 5, twE6L2vec 6]

private theorem twE6Q0List_nodup : twE6Q0List.Nodup := by decide +kernel

private theorem twE6Q0List_hL :
    ∀ γ ∈ twE6Q0List, IsRoot .F4 γ ∧ 0 < (1 : ℤ) * ht γ := by
  intro γ hγ
  have h : twE6Q0List.all (fun γ => memF4 γ && decide (0 < (1 : ℤ) * ht γ)) = true := by
    decide +kernel
  have h' := List.all_eq_true.mp h γ hγ
  rw [Bool.and_eq_true] at h'
  exact ⟨(StringData.memDec_iff (Tag.rootCertificate_check .F4)
    (Tag.stringData_check .F4)).1 h'.1, of_decide_eq_true h'.2⟩

private theorem twE6Q0List_sort :
    twE6Q0List.Pairwise (fun γ δ => (1 : ℤ) * ht γ ≤ (1 : ℤ) * ht δ) := by
  decide +kernel

private theorem twE6Last_le_two
    (γ : Fin (Tag.rank .F4) → ℤ) (hγ : IsRoot .F4 γ) :
    γ twE6Last ≤ 2 := by
  obtain ⟨m, hm, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .F4) hγ
  have h : (List.range (Tag.rootCertificate .F4).roots.length).all
      (fun m => decide ((Tag.rootCertificate .F4).root m twE6Last ≤ 2)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h m (List.mem_range.mpr hm))

private theorem twE6Gamma_complete
    (γ : Fin (Tag.rank .F4) → ℤ) (hγ : IsRoot .F4 γ)
    (hl : γ twE6Last = 1) : ∃ i : Fin 8, twE6Gamma i = γ := by
  obtain ⟨m, hm, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .F4) hγ
  have h : (List.range (Tag.rootCertificate .F4).roots.length).all (fun m =>
      decide ((Tag.rootCertificate .F4).root m twE6Last ≠ 1) ||
        (List.finRange 8).any fun i => decide (twE6Gamma i =
          (Tag.rootCertificate .F4).root m)) = true := by
    decide +kernel
  have h' := List.all_eq_true.mp h m (List.mem_range.mpr hm)
  rw [Bool.or_eq_true] at h'
  rcases h' with h' | h'
  · exact absurd hl (of_decide_eq_true h')
  · obtain ⟨i, -, hi⟩ := List.any_eq_true.mp h'
    exact ⟨i, of_decide_eq_true hi⟩

private theorem twE6L2_complete
    (γ : Fin (Tag.rank .F4) → ℤ) (hγ : IsRoot .F4 γ)
    (hl : γ twE6Last = 2) : γ ∈ Set.range twE6L2vec := by
  obtain ⟨m, hm, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .F4) hγ
  have h : (List.range (Tag.rootCertificate .F4).roots.length).all (fun m =>
      decide ((Tag.rootCertificate .F4).root m twE6Last ≠ 2) ||
        (List.ofFn twE6L2vec).any fun v => decide (v =
          (Tag.rootCertificate .F4).root m)) = true := by
    decide +kernel
  have h' := List.all_eq_true.mp h m (List.mem_range.mpr hm)
  rw [Bool.or_eq_true] at h'
  rcases h' with h' | h'
  · exact absurd hl (of_decide_eq_true h')
  · obtain ⟨v, hv, hv2⟩ := List.any_eq_true.mp h'
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
    exact ⟨i, of_decide_eq_true hv2⟩

private theorem twE6X_mem_rootGroup
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (i : Fin 8) (c : k) :
    twE6X θ hθ i c ∈ (twistedDatum k θ).rootGroup (twE6Gamma i) := by
  show twE6X θ hθ i c ∈ twistedRootGroup k θ (twE6Gamma i)
  rw [← twE6_proj_lift i]
  exact xPair_mem θ hθ (twE6Lift_isRoot i) (twE6Lift_ne_rho i) c

theorem twE6X_mem_rad
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (i : Fin 8) (c : k) :
    twE6X θ hθ i c ∈ twE6Rad θ := by
  rw [twE6Rad]
  have hmem : twE6Gamma i ∈ {γ : Fin (Tag.rank .F4) → ℤ |
      γ ∈ (twistedDatum k θ).roots ∧ 1 ≤ γ twE6Last} := by
    refine ⟨?_, ?_⟩
    · rw [twistedDatum_roots]
      exact twE6Gamma_isRoot i
    · rw [twE6Gamma_last i]
  exact rootGroup_le_ggSub hmem (twE6X_mem_rootGroup θ hθ i c)

private theorem twE6X_mul
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (i : Fin 8) (c d : k) :
    twE6X θ hθ i c * twE6X θ hθ i d = twE6X θ hθ i (c + d) := by
  apply Subtype.ext
  show (twE6X θ hθ i c : e6Data_valid.minGroup k) *
      (twE6X θ hθ i d : e6Data_valid.minGroup k) =
      (twE6X θ hθ i (c + d) : e6Data_valid.minGroup k)
  rw [twE6X, twE6X, twE6X, xPair_val, xPair_val, xPair_val]
  have hcomm := (commute_xm_rho (twE6Lift_isRoot i) (twE6Lift_ne_rho i) d
    ((twistSign (twE6Lift i) : k) * θ c)).eq
  calc e6Data_valid.xm k (twE6Lift i) c *
        e6Data_valid.xm k (rho (twE6Lift i)) ((twistSign (twE6Lift i) : k) * θ c) *
        (e6Data_valid.xm k (twE6Lift i) d *
          e6Data_valid.xm k (rho (twE6Lift i)) ((twistSign (twE6Lift i) : k) * θ d))
      = e6Data_valid.xm k (twE6Lift i) c *
          (e6Data_valid.xm k (rho (twE6Lift i)) ((twistSign (twE6Lift i) : k) * θ c) *
            e6Data_valid.xm k (twE6Lift i) d) *
          e6Data_valid.xm k (rho (twE6Lift i)) ((twistSign (twE6Lift i) : k) * θ d) := by
        group
    _ = e6Data_valid.xm k (twE6Lift i) c *
          (e6Data_valid.xm k (twE6Lift i) d *
            e6Data_valid.xm k (rho (twE6Lift i)) ((twistSign (twE6Lift i) : k) * θ c)) *
          e6Data_valid.xm k (rho (twE6Lift i)) ((twistSign (twE6Lift i) : k) * θ d) := by
        rw [← hcomm]
    _ = (e6Data_valid.xm k (twE6Lift i) c * e6Data_valid.xm k (twE6Lift i) d) *
          (e6Data_valid.xm k (rho (twE6Lift i)) ((twistSign (twE6Lift i) : k) * θ c) *
            e6Data_valid.xm k (rho (twE6Lift i)) ((twistSign (twE6Lift i) : k) * θ d)) := by
        group
    _ = e6Data_valid.xm k (twE6Lift i) (c + d) *
          e6Data_valid.xm k (rho (twE6Lift i))
            ((twistSign (twE6Lift i) : k) * θ c + (twistSign (twE6Lift i) : k) * θ d) := by
        rw [e6Data_valid.xm_add, e6Data_valid.xm_add]
    _ = e6Data_valid.xm k (twE6Lift i) (c + d) *
          e6Data_valid.xm k (rho (twE6Lift i)) ((twistSign (twE6Lift i) : k) * θ (c + d)) := by
        rw [map_add, mul_add]

private theorem twE6X_zero
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (i : Fin 8) :
    twE6X θ hθ i 0 = 1 := by
  apply Subtype.ext
  rw [twE6X, xPair_val]
  simp [e6Data_valid.xm_zero]

private theorem twE6X_injective
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (i : Fin 8) {c d : k}
    (h : twE6X θ hθ i c = twE6X θ hθ i d) : c = d := by
  have h' := congrArg Subtype.val h
  rw [twE6X, twE6X, xPair_val, xPair_val] at h'
  exact (xm_mul_xm_rho_inj (twE6Lift_isRoot i) (twE6Lift_ne_rho i) h').1

private theorem list_ofFn_prod_single {G : Type*} [Group G] :
    ∀ (n : ℕ) (i : Fin n) (x : G),
      (List.ofFn (fun j : Fin n => if j = i then x else 1)).prod = x
  | 0, i, _ => i.elim0
  | n + 1, i, x => by
      rw [List.ofFn_succ]
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
      · rw [if_pos rfl]
        have h : (List.ofFn fun j : Fin n =>
              (if (j.succ : Fin (n + 1)) = 0 then x else 1)) =
            List.ofFn (fun _ : Fin n => (1 : G)) := by
          apply congrArg List.ofFn
          funext j
          rw [if_neg (Fin.succ_ne_zero j)]
        rw [h]
        simp
      · rw [if_neg (fun h => Fin.succ_ne_zero i' h.symm)]
        have h : (List.ofFn fun j : Fin n =>
              (if (j.succ : Fin (n + 1)) = i'.succ then x else 1)) =
            List.ofFn (fun j : Fin n => if j = i' then x else 1) := by
          apply congrArg List.ofFn
          funext j
          simp only [Fin.succ_inj]
        rw [h, List.prod_cons, one_mul, list_ofFn_prod_single n i' x]

private theorem list_prod_inv_of_pairwise_commute {G : Type*} [Group G] {l : List G}
    (h : l.Pairwise Commute) : l.prod⁻¹ = (l.map (·⁻¹)).prod := by
  rw [List.prod_inv_reverse]
  refine List.Perm.prod_eq' (List.reverse_perm _) ?_
  exact List.pairwise_reverse.mpr (List.Pairwise.imp (fun hab => hab.symm)
    (List.Pairwise.map (·⁻¹) (fun a b hab => hab.inv_left.inv_right) h))

private theorem exists_prod_mul_eq_mul_prod_z {G : Type*} [Group G] (Z A : Subgroup G)
    (hcent : Z ≤ Subgroup.centralizer (A : Set G))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, ⁅a, b⁆ ∈ Z)
    (l : List G) (hl : ∀ a ∈ l, a ∈ A) (b : G) (hb : b ∈ A) :
    ∃ z ∈ Z, l.prod * b = b * l.prod * z := by
  induction l with
  | nil => exact ⟨1, Z.one_mem, by simp⟩
  | cons a l ih =>
    obtain ⟨z1, hz1, hz1eq⟩ := ih (fun x hx => hl x (List.mem_cons_of_mem a hx))
    have ha : a ∈ A := hl a List.mem_cons_self
    have hlp : l.prod ∈ A :=
      Subgroup.list_prod_mem A (fun x hx => hl x (List.mem_cons_of_mem a hx))
    have hcommab : a * b = b * a * ⁅a⁻¹, b⁻¹⁆ := by
      rw [commutatorElement_def]; group
    have hw : ⁅a⁻¹, b⁻¹⁆ ∈ Z := hcomm a⁻¹ (A.inv_mem ha) b⁻¹ (A.inv_mem hb)
    have hcw : ⁅a⁻¹, b⁻¹⁆ * l.prod = l.prod * ⁅a⁻¹, b⁻¹⁆ :=
      (Subgroup.mem_centralizer_iff.mp (hcent hw) l.prod hlp).symm
    refine ⟨⁅a⁻¹, b⁻¹⁆ * z1, Z.mul_mem hw hz1, ?_⟩
    rw [List.prod_cons]
    rw [show a * l.prod * b = a * (l.prod * b) from by group, hz1eq]
    calc a * (b * l.prod * z1)
        = a * b * l.prod * z1 := by group
      _ = b * a * ⁅a⁻¹, b⁻¹⁆ * l.prod * z1 := by rw [hcommab]
      _ = b * (a * l.prod) * (⁅a⁻¹, b⁻¹⁆ * z1) := by
            rw [show b * a * ⁅a⁻¹, b⁻¹⁆ * l.prod * z1 =
                b * a * (⁅a⁻¹, b⁻¹⁆ * l.prod) * z1 from by group, hcw]
            group

private theorem exists_prod_mul_prod_z {G : Type*} [Group G] (Z A : Subgroup G)
    (hcent : Z ≤ Subgroup.centralizer (A : Set G))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, ⁅a, b⁆ ∈ Z)
    (l m : List G) (hl : ∀ a ∈ l, a ∈ A) (hm : ∀ a ∈ m, a ∈ A)
    (hlen : l.length = m.length) :
    ∃ z ∈ Z, l.prod * m.prod = (l.zipWith (· * ·) m).prod * z := by
  induction l generalizing m with
  | nil =>
    cases m with
    | nil => exact ⟨1, Z.one_mem, by simp⟩
    | cons b m => simp at hlen
  | cons a l ih =>
    cases m with
    | nil => simp at hlen
    | cons b m =>
      obtain ⟨z1, hz1, hz1eq⟩ := exists_prod_mul_eq_mul_prod_z Z A hcent hcomm l
        (fun x hx => hl x (List.mem_cons_of_mem a hx)) b (hm b List.mem_cons_self)
      obtain ⟨z2, hz2, hz2eq⟩ := ih m (fun x hx => hl x (List.mem_cons_of_mem a hx))
        (fun x hx => hm x (List.mem_cons_of_mem b hx)) (by simpa using hlen)
      have hmp : m.prod ∈ A :=
        Subgroup.list_prod_mem A (fun x hx => hm x (List.mem_cons_of_mem b hx))
      have hcw1 : z1 * m.prod = m.prod * z1 :=
        (Subgroup.mem_centralizer_iff.mp (hcent hz1) m.prod hmp).symm
      refine ⟨z2 * z1, Z.mul_mem hz2 hz1, ?_⟩
      rw [List.prod_cons, List.prod_cons, List.zipWith_cons_cons, List.prod_cons]
      calc (a * l.prod) * (b * m.prod)
          = a * (l.prod * b) * m.prod := by group
        _ = a * (b * l.prod * z1) * m.prod := by rw [hz1eq]
        _ = a * b * l.prod * (z1 * m.prod) := by group
        _ = a * b * l.prod * (m.prod * z1) := by rw [hcw1]
        _ = a * b * (l.prod * m.prod) * z1 := by group
        _ = a * b * ((l.zipWith (· * ·) m).prod * z2) * z1 := by rw [hz2eq]
        _ = (a * b * (l.zipWith (· * ·) m).prod) * (z2 * z1) := by group

private theorem list_zipWith_ofFn {α β γ : Type*} (f : α → β → γ) :
    ∀ (n : ℕ) (x : Fin n → α) (y : Fin n → β),
      (List.ofFn x).zipWith f (List.ofFn y) = List.ofFn (fun i => f (x i) (y i))
  | 0, x, y => by simp
  | n + 1, x, y => by
      rw [List.ofFn_succ, List.ofFn_succ, List.zipWith_cons_cons, List.ofFn_succ,
        list_zipWith_ofFn f n (fun i => x i.succ) (fun i => y i.succ)]

private theorem twE6Cen_le_rad
    {k : Type} [Field k] (θ : k →+* k) : twE6Cen θ ≤ twE6Rad θ := by
  rw [twE6Cen, twE6Rad]
  refine iSup₂_le fun γ hγ => rootGroup_le_ggSub ⟨hγ.1, ?_⟩
  exact le_trans (by norm_num : (1 : ℤ) ≤ 2) hγ.2

private theorem twE6Cen_subgroupOf_le_center
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    (twE6Cen θ).subgroupOf (twE6Rad θ) ≤ Subgroup.center (twE6Rad θ) := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro q
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.mp
    (twE6Cen_le_centralizer_rad θ hθ (Subgroup.mem_subgroupOf.mp hz))
    (q : fixedGroup k θ) q.2

private theorem twE6Cen_subgroupOf_normal
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    ((twE6Cen θ).subgroupOf (twE6Rad θ)).Normal :=
  Subgroup.normal_of_le_center (twE6Cen_subgroupOf_le_center θ hθ)

private theorem twE6_commutator_subgroupOf
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    (a b : twE6Rad θ) : ⁅a, b⁆ ∈ (twE6Cen θ).subgroupOf (twE6Rad θ) := by
  rw [Subgroup.mem_subgroupOf]
  exact twE6_commutator_rad_le_cen θ hθ (Subgroup.commutator_mem_commutator a.2 b.2)

private theorem twE6Cen_comm
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {x y : fixedGroup k θ} (hx : x ∈ twE6Cen θ) (hy : y ∈ twE6Cen θ) : x * y = y * x := by
  have hyQ : y ∈ twE6Rad θ := twE6Cen_le_rad θ hy
  exact (Subgroup.mem_centralizer_iff.mp (twE6Cen_le_centralizer_rad θ hθ hx) y hyQ).symm

private theorem twE6L2vec_mem_cen
    {k : Type} [Field k] (θ : k →+* k) (i : Fin 7) :
    (twistedDatum k θ).rootGroup (twE6L2vec i) ≤ twE6Cen θ := by
  rw [twE6Cen]
  exact rootGroup_le_ggSub ⟨by rw [twistedDatum_roots]; exact twE6L2vec_isRoot i,
    by rw [twE6L2vec_last i]⟩

private theorem twE6Cen_eq_iSup
    {k : Type} [Field k] (θ : k →+* k) :
    twE6Cen θ = ⨆ i : Fin 7, (twistedDatum k θ).rootGroup (twE6L2vec i) := by
  refine le_antisymm ?_ ?_
  · rw [twE6Cen]
    refine iSup₂_le fun γ hγ => ?_
    have hγroot : IsRoot .F4 γ := isRoot_of_mem_twistedDatum_roots θ hγ.1
    have hl : γ twE6Last = 2 := le_antisymm (twE6Last_le_two γ hγroot) hγ.2
    obtain ⟨i, rfl⟩ := twE6L2_complete γ hγroot hl
    exact le_iSup (fun i => (twistedDatum k θ).rootGroup (twE6L2vec i)) i
  · refine iSup_le fun i => twE6L2vec_mem_cen θ i

private theorem twE6Cen_decomp
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {z : fixedGroup k θ} (hz : z ∈ twE6Cen θ) :
    ∃ f : Fin 7 → fixedGroup k θ,
      (∀ i, f i ∈ (twistedDatum k θ).rootGroup (twE6L2vec i)) ∧ z = (List.ofFn f).prod := by
  let H : Fin 7 → Subgroup (fixedGroup k θ) :=
    fun i => (twistedDatum k θ).rootGroup (twE6L2vec i)
  let P : Subgroup (fixedGroup k θ) :=
    { carrier := {x | ∃ f : Fin 7 → fixedGroup k θ, (∀ i, f i ∈ H i) ∧
        x = (List.ofFn f).prod}
      mul_mem' := by
        rintro x y ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
        obtain ⟨z0, hz0, hz0eq⟩ := exists_prod_mul_prod_z (⊥ : Subgroup _) (twE6Cen θ)
          (by simp)
          (fun a ha b hb => Subgroup.mem_bot.mpr
            (commutatorElement_eq_one_iff_mul_comm.mpr (twE6Cen_comm θ hθ ha hb)))
          (List.ofFn f) (List.ofFn g)
          (fun a ha => by
            obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
            exact twE6L2vec_mem_cen θ i (hf i))
          (fun a ha => by
            obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
            exact twE6L2vec_mem_cen θ i (hg i))
          (by simp)
        rw [list_zipWith_ofFn] at hz0eq
        rw [Subgroup.mem_bot.mp hz0, mul_one] at hz0eq
        exact ⟨fun i => f i * g i, fun i => (H i).mul_mem (hf i) (hg i), hz0eq⟩
      one_mem' := ⟨fun _ => 1, fun i => (H i).one_mem, by
        simp [List.ofFn_const, List.prod_replicate]⟩
      inv_mem' := by
        rintro x ⟨f, hf, rfl⟩
        have hpair : (List.ofFn f).Pairwise Commute := by
          rw [List.pairwise_ofFn]
          intro i j _
          exact twE6Cen_comm θ hθ (twE6L2vec_mem_cen θ i (hf i))
            (twE6L2vec_mem_cen θ j (hf j))
        refine ⟨fun i => (f i)⁻¹, fun i => (H i).inv_mem (hf i), ?_⟩
        rw [list_prod_inv_of_pairwise_commute hpair, List.map_ofFn]
        rfl }
  have hZle : twE6Cen θ ≤ P := by
    rw [twE6Cen_eq_iSup]
    refine iSup_le fun i => ?_
    intro x hx
    refine ⟨fun j => if j = i then x else 1, fun j => ?_, ?_⟩
    · show (if j = i then x else 1) ∈ H j
      by_cases hj : j = i
      · subst hj; simpa using hx
      · rw [if_neg hj]; exact (H j).one_mem
    · exact (list_ofFn_prod_single 7 i x).symm
  exact hZle hz

private noncomputable def twE6Xprod
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (c : Fin 8 → k) :
    twE6Rad θ :=
  (List.ofFn fun i : Fin 8 => ⟨twE6X θ hθ i (c i), twE6X_mem_rad θ hθ i (c i)⟩).prod

private theorem twE6Xprod_coe
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (c : Fin 8 → k) :
    (twE6Xprod θ hθ c : fixedGroup k θ) =
      (List.ofFn fun i : Fin 8 => twE6X θ hθ i (c i)).prod := by
  change (Subgroup.subtype (twE6Rad θ))
      (List.ofFn fun i : Fin 8 =>
        ⟨twE6X θ hθ i (c i), twE6X_mem_rad θ hθ i (c i)⟩).prod =
    (List.ofFn fun i : Fin 8 => twE6X θ hθ i (c i)).prod
  rw [map_list_prod, List.map_ofFn]
  rfl

private theorem twE6Xprod_zero
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    twE6Xprod θ hθ (0 : Fin 8 → k) = 1 := by
  apply Subtype.ext
  rw [twE6Xprod_coe]
  have hfun : (fun j : Fin 8 => twE6X θ hθ j ((0 : Fin 8 → k) j)) =
      (fun _ : Fin 8 => (1 : fixedGroup k θ)) := by
    funext j
    rw [Pi.zero_apply, twE6X_zero]
  rw [hfun]
  simp [List.ofFn_const]

private theorem twE6Xprod_single
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (i : Fin 8) (c : k) :
    twE6Xprod θ hθ (Pi.single i c) = ⟨twE6X θ hθ i c, twE6X_mem_rad θ hθ i c⟩ := by
  apply Subtype.ext
  rw [twE6Xprod_coe]
  have hfun : (fun j : Fin 8 => twE6X θ hθ j ((Pi.single i c : Fin 8 → k) j)) =
      (fun j : Fin 8 => if j = i then twE6X θ hθ i c else 1) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [Pi.single_eq_same]
    · simp [Pi.single_eq_of_ne, hj, Ne.symm hj, twE6X_zero]
  rw [hfun, list_ofFn_prod_single]

private theorem twE6Xprod_add
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (c d : Fin 8 → k) :
    ∃ z ∈ (twE6Cen θ).subgroupOf (twE6Rad θ),
      twE6Xprod θ hθ c * twE6Xprod θ hθ d = twE6Xprod θ hθ (c + d) * z := by
  let l : List (twE6Rad θ) :=
    List.ofFn fun i : Fin 8 => ⟨twE6X θ hθ i (c i), twE6X_mem_rad θ hθ i (c i)⟩
  let m : List (twE6Rad θ) :=
    List.ofFn fun i : Fin 8 => ⟨twE6X θ hθ i (d i), twE6X_mem_rad θ hθ i (d i)⟩
  have hcent : (twE6Cen θ).subgroupOf (twE6Rad θ) ≤
      Subgroup.centralizer (⊤ : Set (twE6Rad θ)) :=
    le_trans (twE6Cen_subgroupOf_le_center θ hθ) (Subgroup.center_le_centralizer _)
  obtain ⟨z, hz, hzX⟩ := exists_prod_mul_prod_z ((twE6Cen θ).subgroupOf (twE6Rad θ))
    (⊤ : Subgroup (twE6Rad θ)) hcent (fun a _ b _ => twE6_commutator_subgroupOf θ hθ a b)
    l m (by intro a _; exact Subgroup.mem_top a) (by intro a _; exact Subgroup.mem_top a)
    (by simp [l, m])
  rw [list_zipWith_ofFn] at hzX
  refine ⟨z, hz, ?_⟩
  change l.prod * m.prod =
    (List.ofFn fun i : Fin 8 =>
      ⟨twE6X θ hθ i ((c + d) i), twE6X_mem_rad θ hθ i ((c + d) i)⟩).prod * z
  rw [hzX, mul_right_cancel_iff]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  exact Subtype.ext (twE6X_mul θ hθ i (c i) (d i))

private theorem twE6Gamma_injective : Function.Injective twE6Gamma := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    first
      | rfl
      | exact absurd h (by decide +kernel)

private theorem twE6L2vec_injective : Function.Injective twE6L2vec := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    first
      | rfl
      | exact absurd h (by decide +kernel)

private theorem twE6L2vec_ne_Gamma (j : Fin 7) (k : Fin 8) : twE6L2vec j ≠ twE6Gamma k := by
  intro h
  have h' := congrFun h twE6Last
  rw [twE6L2vec_last j, twE6Gamma_last k] at h'
  norm_num at h'

private theorem twE6Gamma_ne_L2vec (k : Fin 8) (j : Fin 7) : twE6Gamma k ≠ twE6L2vec j :=
  fun h => twE6L2vec_ne_Gamma j k h.symm

private theorem twE6Q0List_mem_iff {γ : Fin (Tag.rank .F4) → ℤ} :
    γ ∈ twE6Q0List ↔ (∃ i : Fin 8, γ = twE6Gamma i) ∨ (∃ j : Fin 7, γ = twE6L2vec j) := by
  constructor
  · intro hγ
    simp only [twE6Q0List, List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl ⟨0, h⟩
    · exact Or.inl ⟨1, h⟩
    · exact Or.inl ⟨2, h⟩
    · exact Or.inl ⟨3, h⟩
    · exact Or.inl ⟨4, h⟩
    · exact Or.inl ⟨5, h⟩
    · exact Or.inr ⟨0, h⟩
    · exact Or.inl ⟨6, h⟩
    · exact Or.inr ⟨1, h⟩
    · exact Or.inl ⟨7, h⟩
    · exact Or.inr ⟨2, h⟩
    · exact Or.inr ⟨3, h⟩
    · exact Or.inr ⟨4, h⟩
    · exact Or.inr ⟨5, h⟩
    · exact Or.inr ⟨6, h⟩
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · fin_cases i <;> decide +kernel
    · fin_cases j <;> decide +kernel

private noncomputable def twE6CoordF₁
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (c : Fin 8 → k)
    (γ : Fin (Tag.rank .F4) → ℤ) : fixedGroup k θ :=
  if γ = twE6Gamma 0 then twE6X θ hθ 0 (c 0)
  else if γ = twE6Gamma 1 then twE6X θ hθ 1 (c 1)
  else if γ = twE6Gamma 2 then twE6X θ hθ 2 (c 2)
  else if γ = twE6Gamma 3 then twE6X θ hθ 3 (c 3)
  else if γ = twE6Gamma 4 then twE6X θ hθ 4 (c 4)
  else if γ = twE6Gamma 5 then twE6X θ hθ 5 (c 5)
  else if γ = twE6Gamma 6 then twE6X θ hθ 6 (c 6)
  else if γ = twE6Gamma 7 then twE6X θ hθ 7 (c 7)
  else 1

private noncomputable def twE6CoordF₂
    {k : Type} [Field k] (θ : k →+* k) (f : Fin 7 → fixedGroup k θ)
    (γ : Fin (Tag.rank .F4) → ℤ) : fixedGroup k θ :=
  if γ = twE6L2vec 0 then f 0
  else if γ = twE6L2vec 1 then f 1
  else if γ = twE6L2vec 2 then f 2
  else if γ = twE6L2vec 3 then f 3
  else if γ = twE6L2vec 4 then f 4
  else if γ = twE6L2vec 5 then f 5
  else if γ = twE6L2vec 6 then f 6
  else 1

private theorem twE6CoordF₁_gamma
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (c : Fin 8 → k) (i : Fin 8) :
    twE6CoordF₁ θ hθ c (twE6Gamma i) = twE6X θ hθ i (c i) := by
  fin_cases i <;> simp [twE6CoordF₁, twE6Gamma_injective.eq_iff]

private theorem twE6CoordF₁_l2
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (c : Fin 8 → k) (j : Fin 7) :
    twE6CoordF₁ θ hθ c (twE6L2vec j) = 1 := by
  simp [twE6CoordF₁, twE6L2vec_ne_Gamma]

private theorem twE6CoordF₂_gamma
    {k : Type} [Field k] (θ : k →+* k) (f : Fin 7 → fixedGroup k θ)
    (i : Fin 8) : twE6CoordF₂ θ f (twE6Gamma i) = 1 := by
  simp [twE6CoordF₂, twE6Gamma_ne_L2vec]

private theorem twE6CoordF₂_l2
    {k : Type} [Field k] (θ : k →+* k) (f : Fin 7 → fixedGroup k θ)
    (j : Fin 7) : twE6CoordF₂ θ f (twE6L2vec j) = f j := by
  fin_cases j <;> simp [twE6CoordF₂, twE6L2vec_injective.eq_iff]

private theorem twE6CoordF₁_prod
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (c : Fin 8 → k) :
    (twE6Q0List.map (twE6CoordF₁ θ hθ c)).prod = (twE6Xprod θ hθ c : fixedGroup k θ) := by
  rw [twE6Xprod_coe]
  simp [twE6Q0List, twE6CoordF₁, twE6Gamma_injective.eq_iff, twE6L2vec_ne_Gamma,
    List.ofFn_succ]

private theorem twE6CoordF₂_prod
    {k : Type} [Field k] (θ : k →+* k) (f : Fin 7 → fixedGroup k θ) :
    (twE6Q0List.map (twE6CoordF₂ θ f)).prod = (List.ofFn f).prod := by
  simp [twE6Q0List, twE6CoordF₂, twE6Gamma_ne_L2vec, twE6L2vec_injective.eq_iff,
    List.ofFn_succ]

private noncomputable def twE6Xbar
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    [hN : ((twE6Cen θ).subgroupOf (twE6Rad θ)).Normal] :
    Multiplicative (Fin 8 → k) →*
      (twE6Rad θ ⧸ (twE6Cen θ).subgroupOf (twE6Rad θ)) where
  toFun c := QuotientGroup.mk' ((twE6Cen θ).subgroupOf (twE6Rad θ)) (twE6Xprod θ hθ c.toAdd)
  map_one' := by
    rw [toAdd_one, twE6Xprod_zero]
    exact map_one (QuotientGroup.mk' ((twE6Cen θ).subgroupOf (twE6Rad θ)))
  map_mul' c d := by
    obtain ⟨z, hz, hzX⟩ := twE6Xprod_add θ hθ c.toAdd d.toAdd
    have hz1 : QuotientGroup.mk' ((twE6Cen θ).subgroupOf (twE6Rad θ)) z = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hz
    exact (((map_mul (QuotientGroup.mk' ((twE6Cen θ).subgroupOf (twE6Rad θ)))
          (twE6Xprod θ hθ c.toAdd) (twE6Xprod θ hθ d.toAdd)).symm.trans
        (congrArg (QuotientGroup.mk' ((twE6Cen θ).subgroupOf (twE6Rad θ))) hzX)).trans
      ((map_mul (QuotientGroup.mk' ((twE6Cen θ).subgroupOf (twE6Rad θ)))
          (twE6Xprod θ hθ (c.toAdd + d.toAdd)) z).trans
        ((congrArg (fun w => QuotientGroup.mk' ((twE6Cen θ).subgroupOf (twE6Rad θ))
            (twE6Xprod θ hθ (c.toAdd + d.toAdd)) * w) hz1).trans (mul_one _)))).symm

private theorem twE6Xbar_ofAdd
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    [hN : ((twE6Cen θ).subgroupOf (twE6Rad θ)).Normal] (c : Fin 8 → k) :
    twE6Xbar θ hθ (Multiplicative.ofAdd c) =
      QuotientGroup.mk' ((twE6Cen θ).subgroupOf (twE6Rad θ)) (twE6Xprod θ hθ c) := rfl

private theorem twE6Xbar_ker
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    [hN : ((twE6Cen θ).subgroupOf (twE6Rad θ)).Normal] {c : Fin 8 → k}
    (h : twE6Xbar θ hθ (Multiplicative.ofAdd c) = 1) : c = 0 := by
  classical
  have hc : QuotientGroup.mk' ((twE6Cen θ).subgroupOf (twE6Rad θ))
      (twE6Xprod θ hθ c) = 1 := h
  have hz : twE6Xprod θ hθ c ∈ (twE6Cen θ).subgroupOf (twE6Rad θ) :=
    (QuotientGroup.eq_one_iff _).mp hc
  obtain ⟨f, hf, hzf⟩ := twE6Cen_decomp θ hθ (Subgroup.mem_subgroupOf.mp hz)
  have hF₁ : ∀ γ ∈ twE6Q0List,
      twE6CoordF₁ θ hθ c γ ∈ (twistedDatum k θ).rootGroup γ := by
    intro γ hγ
    rcases twE6Q0List_mem_iff.mp hγ with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rw [twE6CoordF₁_gamma]
      exact twE6X_mem_rootGroup θ hθ i (c i)
    · rw [twE6CoordF₁_l2]
      exact Subgroup.one_mem _
  have hF₂ : ∀ γ ∈ twE6Q0List,
      twE6CoordF₂ θ f γ ∈ (twistedDatum k θ).rootGroup γ := by
    intro γ hγ
    rcases twE6Q0List_mem_iff.mp hγ with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rw [twE6CoordF₂_gamma]
      exact Subgroup.one_mem _
    · rw [twE6CoordF₂_l2]
      exact hf j
  have heq : (twE6Q0List.map (twE6CoordF₁ θ hθ c)).prod =
      (twE6Q0List.map (twE6CoordF₂ θ f)).prod := by
    rw [twE6CoordF₁_prod, twE6CoordF₂_prod, hzf]
  have hpair := prodInjective_twisted θ 1 twE6Q0List twE6Q0List_nodup twE6Q0List_hL
    twE6Q0List_sort (twE6CoordF₁ θ hθ c) (twE6CoordF₂ θ f) hF₁ hF₂ heq
  funext i
  have hi : twE6Gamma i ∈ twE6Q0List := twE6Q0List_mem_iff.mpr (Or.inl ⟨i, rfl⟩)
  have hxi := hpair (twE6Gamma i) hi
  rw [twE6CoordF₁_gamma, twE6CoordF₂_gamma] at hxi
  exact twE6X_injective θ hθ i (by rw [hxi, Pi.zero_apply, twE6X_zero])

private theorem twE6Xbar_injective
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    [hN : ((twE6Cen θ).subgroupOf (twE6Rad θ)).Normal] :
    Function.Injective (twE6Xbar θ hθ) := by
  intro a b hab
  have h1 : twE6Xbar θ hθ (Multiplicative.ofAdd (a.toAdd - b.toAdd)) = 1 := by
    have hsub : Multiplicative.ofAdd (a.toAdd - b.toAdd) = a * b⁻¹ := by
      rw [ofAdd_sub, div_eq_mul_inv, ofAdd_toAdd, ofAdd_toAdd]
    rw [hsub, map_mul, map_inv, hab, mul_inv_cancel]
  have h2 := twE6Xbar_ker θ hθ h1
  have h3 : a.toAdd = b.toAdd := sub_eq_zero.mp h2
  exact Multiplicative.toAdd.injective h3

private theorem twE6Xbar_mem_range
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    [hN : ((twE6Cen θ).subgroupOf (twE6Rad θ)).Normal]
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ (twistedDatum k θ).roots)
    (hγlev : 1 ≤ γ twE6Last)
    (x : twE6Rad θ) (hx : (x : fixedGroup k θ) ∈ (twistedDatum k θ).rootGroup γ) :
    QuotientGroup.mk' ((twE6Cen θ).subgroupOf (twE6Rad θ)) x ∈ (twE6Xbar θ hθ).range := by
  classical
  have hlevel : γ twE6Last = 1 ∨ 2 ≤ γ twE6Last := by omega
  rcases hlevel with hl | hl
  · obtain ⟨i, hi⟩ := twE6Gamma_complete γ (isRoot_of_mem_twistedDatum_roots θ hγ) hl
    subst hi
    obtain ⟨c, hc⟩ := (mem_twistedRootGroup_iff_of_pair θ (twE6Lift_isRoot i)
      (twE6_proj_lift i) (twE6Lift_ne_rho i) (x : fixedGroup k θ)).1 hx
    have hxc : (x : fixedGroup k θ) = twE6X θ hθ i c := by
      apply Subtype.ext
      rw [twE6X, xPair_val]
      exact hc
    refine ⟨Multiplicative.ofAdd (Pi.single i c), ?_⟩
    rw [twE6Xbar_ofAdd, twE6Xprod_single]
    congr 1
    exact Subtype.ext hxc.symm
  · have hxZ : (x : fixedGroup k θ) ∈ twE6Cen θ :=
      rootGroup_le_ggSub (D := twistedDatum k θ) (S := {δ : Fin (Tag.rank .F4) → ℤ |
        δ ∈ (twistedDatum k θ).roots ∧ 2 ≤ δ twE6Last}) (γ := γ) ⟨hγ, hl⟩ hx
    refine ⟨1, ?_⟩
    rw [map_one]
    symm
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hxZ

private theorem twE6Xbar_surjective
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    [hN : ((twE6Cen θ).subgroupOf (twE6Rad θ)).Normal] :
    Function.Surjective (twE6Xbar θ hθ) := by
  classical
  let Q := twE6Rad θ
  let P : Subgroup (fixedGroup k θ) :=
    (((twE6Xbar θ hθ).range).comap
      (QuotientGroup.mk' ((twE6Cen θ).subgroupOf Q))).map (Subgroup.subtype Q)
  have hP : Q ≤ P := by
    rw [show Q = ⨆ γ ∈ {γ : Fin (Tag.rank .F4) → ℤ |
        γ ∈ (twistedDatum k θ).roots ∧ 1 ≤ γ twE6Last},
        (twistedDatum k θ).rootGroup γ from rfl]
    refine iSup₂_le fun γ hγ x hx => ?_
    rw [Subgroup.mem_map]
    refine ⟨⟨x, Subgroup.mem_iSup_of_mem γ (Subgroup.mem_iSup_of_mem hγ hx)⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    exact twE6Xbar_mem_range θ hθ hγ.1 hγ.2
      ⟨x, Subgroup.mem_iSup_of_mem γ (Subgroup.mem_iSup_of_mem hγ hx)⟩ hx
  rw [← MonoidHom.range_eq_top, eq_top_iff]
  intro y _
  obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective ((twE6Cen θ).subgroupOf Q) y
  have hqP : (q : fixedGroup k θ) ∈ P := hP q.2
  rw [Subgroup.mem_map] at hqP
  obtain ⟨p, hp, hpq⟩ := hqP
  rw [Subgroup.mem_comap] at hp
  have hpq' : p = q := Subtype.ext hpq
  simpa [hpq'] using hp

theorem twE6_exists_coord
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    ∃ Φ : fixedGroup k θ → (Fin 8 → k), IsTwE6Coord θ hθ Φ := by
  classical
  haveI : ((twE6Cen θ).subgroupOf (twE6Rad θ)).Normal := twE6Cen_subgroupOf_normal θ hθ
  let e : Multiplicative (Fin 8 → k) ≃*
      (twE6Rad θ ⧸ (twE6Cen θ).subgroupOf (twE6Rad θ)) :=
    MulEquiv.ofBijective _ ⟨twE6Xbar_injective θ hθ, twE6Xbar_surjective θ hθ⟩
  let Φ : fixedGroup k θ → (Fin 8 → k) := fun g =>
    if hg : g ∈ twE6Rad θ then
      (e.symm (QuotientGroup.mk' ((twE6Cen θ).subgroupOf (twE6Rad θ)) ⟨g, hg⟩)).toAdd
    else 0
  refine ⟨Φ, ?_, ?_, ?_⟩
  · intro g hg h hh
    have hgh : g * h ∈ twE6Rad θ := (twE6Rad θ).mul_mem hg hh
    simp only [Φ, dif_pos hg, dif_pos hh, dif_pos hgh]
    refine (congrArg Multiplicative.toAdd ?_).trans (toAdd_mul _ _)
    exact map_mul e.symm (QuotientGroup.mk' ((twE6Cen θ).subgroupOf (twE6Rad θ)) ⟨g, hg⟩)
      (QuotientGroup.mk' ((twE6Cen θ).subgroupOf (twE6Rad θ)) ⟨h, hh⟩)
  · intro g hg
    simp only [Φ, dif_pos hg]
    constructor
    · intro h0
      have h1 : e.symm (QuotientGroup.mk' ((twE6Cen θ).subgroupOf (twE6Rad θ)) ⟨g, hg⟩) =
          1 := toAdd_eq_zero.mp h0
      have h2 : QuotientGroup.mk' ((twE6Cen θ).subgroupOf (twE6Rad θ)) ⟨g, hg⟩ = 1 :=
        (MulEquiv.apply_symm_apply e
          (QuotientGroup.mk' ((twE6Cen θ).subgroupOf (twE6Rad θ)) ⟨g, hg⟩)).symm.trans
          ((congrArg e h1).trans (map_one e))
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      exact h2
    · intro hgZ
      have h2 : QuotientGroup.mk' ((twE6Cen θ).subgroupOf (twE6Rad θ)) ⟨g, hg⟩ = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hgZ
      exact toAdd_eq_zero.mpr ((congrArg e.symm h2).trans (map_one e.symm))
  · intro i c
    have hg : twE6X θ hθ i c ∈ twE6Rad θ := twE6X_mem_rad θ hθ i c
    simp only [Φ, dif_pos hg]
    have hX : twE6Xprod θ hθ (Pi.single i c) = ⟨twE6X θ hθ i c, hg⟩ := by
      rw [twE6Xprod_single]
    have hmk : QuotientGroup.mk' ((twE6Cen θ).subgroupOf (twE6Rad θ))
          ⟨twE6X θ hθ i c, hg⟩ =
        twE6Xbar θ hθ (Multiplicative.ofAdd (Pi.single i c)) := by
      rw [twE6Xbar_ofAdd, ← hX]
    have hsym : e.symm (QuotientGroup.mk' ((twE6Cen θ).subgroupOf (twE6Rad θ))
          ⟨twE6X θ hθ i c, hg⟩) = Multiplicative.ofAdd (Pi.single i c) :=
      (congrArg e.symm hmk).trans
        (MulEquiv.symm_apply_apply e (Multiplicative.ofAdd (Pi.single i c)))
    exact congrArg Multiplicative.toAdd hsym

end CFSG.StandardType.LieKnownR2.Short
