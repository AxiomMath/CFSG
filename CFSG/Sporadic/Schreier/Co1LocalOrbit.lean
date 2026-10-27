module

public import CFSG.Sporadic.Schreier.Co1WeightStabPerfect
public import CFSG.Sporadic.Schreier.Co1OrbData
public meta import CFSG.Sporadic.Schreier.Co1OrbData
public meta import CFSG.Sporadic.Schreier.Co1ElemData
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeData
public meta import CFSG.Sporadic.Schreier.Co1SplitCheck
public import CFSG.Sporadic.Schreier.Co1LocalOrbitInputs
public import Certificates.Certificate2140
public import Certificates.Certificate2133
public import Certificates.Certificate2147
public import Certificates.Certificate2150
public import Certificates.Certificate3024

public section

namespace CFSG.Sporadic.Co1Schreier

open ElemThree Matrix

theorem eProd_nsmul (b : Fin 6 → ZMod 3) (k : ℕ) : eProd (k • b) = eProd b ^ k := by
  induction k with
  | zero => rw [zero_smul, eProd_zero, pow_zero]
  | succ k ih => rw [succ_nsmul, eProd_add, ih, pow_succ]

theorem eProd_list_sum (l : List (Fin 6 → ZMod 3)) : eProd l.sum = (l.map eProd).prod := by
  induction l with
  | nil => rw [List.sum_nil, eProd_zero, List.map_nil, List.prod_nil]
  | cons b l ih => rw [List.sum_cons, eProd_add, ih, List.map_cons, List.prod_cons]

theorem conj_list_prod (g : GL24) (l : List GL24) :
    g * l.prod * g⁻¹ = (l.map fun x => g * x * g⁻¹).prod := by
  induction l with
  | nil => rw [List.prod_nil, mul_one, mul_inv_cancel, List.map_nil, List.prod_nil]
  | cons x l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons, ← ih]
    simp only [mul_assoc, inv_mul_cancel_left]

theorem conj_eProd {g : GL24} {c : Fin 6 → Fin 6 → ZMod 3} (h : ∀ j, g * a j * g⁻¹ = eProd (c j))
    (b : Fin 6 → ZMod 3) : g * eProd b * g⁻¹ = eProd (∑ j, b j • c j) := by
  rw [Fin.sum_univ_def, eProd_list_sum, List.map_map]
  conv_lhs => unfold eProd
  rw [conj_list_prod, List.map_map]
  have hf : ((fun x => g * x * g⁻¹) ∘ fun i => a i ^ (b i).val) =
      (eProd ∘ fun j => b j • c j) := by
    funext j
    simp only [Function.comp_apply]
    rw [← conj_pow, h j, ← eProd_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
  rw [hf]

theorem charE_single (f : Fin 6 → ZMod 3) (j : Fin 6) :
    charE f ⟨eProd (Pi.single j 1), eProd_mem _⟩ = ω ^ (f j).val := by
  rw [charE_eProd]
  congr 2
  rw [Finset.sum_eq_single j (fun i _ hi => by rw [Pi.single_eq_of_ne hi, mul_zero])
    (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same, mul_one]

theorem charE_injective : Function.Injective charE := by
  intro f f' h
  funext j
  have := DFunLike.congr_fun h ⟨eProd (Pi.single j 1), eProd_mem _⟩
  rw [charE_single, charE_single] at this
  exact ω_pow_val_inj this

theorem F4_units_eq_pow (u : F4ˣ) : ∃ k : ZMod 3, u = ω ^ k.val := by
  have hinj : Function.Injective fun k : ZMod 3 => ω ^ k.val := fun m n h => ω_pow_val_inj h
  have hbij := hinj.bijective_of_nat_card_le (by rw [card_F4_units, Nat.card_zmod])
  obtain ⟨k, hk⟩ := hbij.2 u
  exact ⟨k, hk.symm⟩

theorem E_closure_top :
    Subgroup.closure (Subtype.val ⁻¹' (Set.range a) : Set E) = ⊤ :=
  Subgroup.closure_closure_coe_preimage

theorem exists_charE_eq (χ : E →* F4ˣ) : ∃ f, χ = charE f := by
  choose k hk using fun j : Fin 6 => F4_units_eq_pow (χ ⟨a j, a_mem_E j⟩)
  refine ⟨k, MonoidHom.eq_of_eqOn_dense E_closure_top ?_⟩
  rintro ⟨_, hx⟩ ⟨j, rfl⟩
  rw [hk j]
  have : (⟨a j, hx⟩ : E) = ⟨eProd (Pi.single j 1), eProd_mem _⟩ :=
    Subtype.ext (eProd_single j).symm
  rw [this, charE_single]

theorem actT_apply (i : Fin 3) (f : Fin 6 → ZMod 3) (j : Fin 6) :
    actT i f j = f ⬝ᵥ conjVec i j := by
  simp only [actT, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [j.isLt]

theorem g_conj_eProd (i : Fin 3) (b : Fin 6 → ZMod 3) :
    g i * eProd b * (g i)⁻¹ = eProd (∑ j, b j • conjVec i j) :=
  conj_eProd (fun j => g_conj_a i j) b

theorem A_conj_mem {x e : GL24} (hx : x ∈ A) (he : e ∈ E) : x⁻¹ * e * x ∈ E := by
  have h := (Subgroup.mem_normalizer_iff.mp (A_le_normalizer (A.inv_mem hx)) e).mp he
  rwa [inv_inv] at h

theorem g_mem_A3 (i : Fin 3) : g i ∈ A := by
  fin_cases i
  · exact g_mem_A 0
  · exact g_mem_A 1
  · exact r_mem_A

theorem charE_conj_g (i : Fin 3) (f : Fin 6 → ZMod 3) {e : GL24} (he : e ∈ E) :
    charV f (g i * e * (g i)⁻¹) = charV (actT i f) e := by
  obtain ⟨b, rfl⟩ : ∃ b, eProd b = e := ⟨_, eProd_eExp ⟨e, he⟩⟩
  rw [g_conj_eProd, charV_of_mem _ (eProd_mem _), charV_of_mem _ (eProd_mem _), charE_eProd,
    charE_eProd]
  refine congrArg (fun z : ZMod 3 => ω ^ z.val) ?_
  simp only [actT_apply, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

@[expose] noncomputable def charOrbit (f : Fin 6 → ZMod 3) : Set (Fin 6 → ZMod 3) :=
  {f' | ∃ x ∈ A, ∀ e ∈ E, charV f' e = charV f (x⁻¹ * e * x)}

@[expose] noncomputable def charConjE (f : Fin 6 → ZMod 3) {y : GL24} (hy : y ∈ A) :
    E →* F4ˣ where
  toFun e := charE f ⟨y⁻¹ * e * y, A_conj_mem hy e.2⟩
  map_one' := by
    rw [← map_one (charE f)]
    refine congrArg (charE f) (Subtype.ext ?_)
    show y⁻¹ * ((1 : E) : GL24) * y = ((1 : E) : GL24)
    rw [OneMemClass.coe_one, mul_one, inv_mul_cancel]
  map_mul' e e' := by
    rw [← map_mul]
    refine congrArg (charE f) (Subtype.ext ?_)
    show y⁻¹ * ((e * e' : E) : GL24) * y = (y⁻¹ * (e : GL24) * y) * (y⁻¹ * (e' : GL24) * y)
    rw [Subgroup.coe_mul]
    simp only [mul_assoc, mul_inv_cancel_left]

theorem charConjE_apply (f : Fin 6 → ZMod 3) {y : GL24} (hy : y ∈ A) (e : E) :
    charConjE f hy e = charV f (y⁻¹ * e * y) := by
  rw [charV_of_mem _ (A_conj_mem hy e.2)]
  rfl

theorem charV_eq_iff {f f' : Fin 6 → ZMod 3} : (∀ e ∈ E, charV f' e = charV f e) ↔ f' = f := by
  constructor
  · intro h
    apply charE_injective
    ext e
    rw [← charV_of_mem _ e.2, ← charV_of_mem _ e.2, h e e.2]
  · rintro rfl _ _
    rfl

theorem mem_charOrbit_self (f : Fin 6 → ZMod 3) : f ∈ charOrbit f :=
  ⟨1, A.one_mem, fun e _ => by rw [inv_one, one_mul, mul_one]⟩

theorem charOrbit_trans {f f' : Fin 6 → ZMod 3} (h : f' ∈ charOrbit f) :
    charOrbit f' ⊆ charOrbit f := by
  obtain ⟨x, hx, hxf⟩ := h
  rintro f'' ⟨y, hy, hyf⟩
  refine ⟨y * x, A.mul_mem hy hx, fun e he => ?_⟩
  rw [hyf e he, hxf _ (A_conj_mem hy he),
    show x⁻¹ * (y⁻¹ * e * y) * x = (y * x)⁻¹ * e * (y * x) by group]

theorem charOrbit_symm {f f' : Fin 6 → ZMod 3} (h : f' ∈ charOrbit f) : f ∈ charOrbit f' := by
  obtain ⟨x, hx, hxf⟩ := h
  refine ⟨x⁻¹, A.inv_mem hx, fun e he => ?_⟩
  rw [hxf _ (A_conj_mem (A.inv_mem hx) he),
    show x⁻¹ * (x⁻¹⁻¹ * e * x⁻¹) * x = e by group]

theorem charOrbit_eq_of_mem {f f' : Fin 6 → ZMod 3} (h : f' ∈ charOrbit f) :
    charOrbit f' = charOrbit f :=
  le_antisymm (charOrbit_trans h) (charOrbit_trans (charOrbit_symm h))

theorem actT_mem_charOrbit {f h : Fin 6 → ZMod 3} (i : Fin 3) (hh : h ∈ charOrbit f) :
    actT i h ∈ charOrbit f := by
  refine charOrbit_trans hh ⟨(g i)⁻¹, A.inv_mem (g_mem_A3 i), fun e he => ?_⟩
  rw [inv_inv, charE_conj_g i h he]

theorem actT_injective (i : Fin 3) : Function.Injective (actT i) := by
  intro h₁ h₂ heq
  rw [← charV_eq_iff]
  intro e he
  have he' : (g i)⁻¹ * e * g i ∈ E := A_conj_mem (g_mem_A3 i) he
  have h1 := charE_conj_g i h₁ he'
  have h2 := charE_conj_g i h₂ he'
  have : g i * ((g i)⁻¹ * e * g i) * (g i)⁻¹ = e := by group
  rw [this, heq] at h1
  rw [this] at h2
  rw [h1, h2]

theorem charOrbit_subset {f : Fin 6 → ZMod 3} {S : Finset (Fin 6 → ZMod 3)} (hf : f ∈ S)
    (hT : ∀ i, ∀ h ∈ S, actT i h ∈ S) : charOrbit f ⊆ ↑S := by
  have hTinv : ∀ i, ∀ h ∈ S, ∃ h' ∈ S, actT i h' = h := by
    intro i h hh
    obtain ⟨h', hh', he⟩ := Finset.surj_on_of_inj_on_of_card_le (s := S) (t := S)
      (fun h' _ => actT i h') (fun h' hh' => hT i h' hh')
      (fun h₁ h₂ _ _ e => actT_injective i e) le_rfl h hh
    exact ⟨h', hh', he.symm⟩
  let P : GL24 → Prop := fun x => x ∈ A ∧ ∀ h ∈ S, ∀ h' : Fin 6 → ZMod 3,
    (∀ e ∈ E, charV h' e = charV h (x⁻¹ * e * x)) → h' ∈ S
  have hP : ∀ x ∈ A, P x := by
    apply closure_induction_inv (P := P)
    · refine ⟨A.one_mem, fun h hh h' hh' => ?_⟩
      have : h' = h := charV_eq_iff.mp fun e he => by rw [hh' e he, inv_one, one_mul, mul_one]
      rwa [this]
    · rintro x y ⟨hx, Px⟩ ⟨hy, Py⟩
      refine ⟨A.mul_mem hx hy, fun h hh h' hh' => ?_⟩
      obtain ⟨h₁, hh₁⟩ := exists_charE_eq (charConjE h hy)
      have hh₁' : ∀ e ∈ E, charV h₁ e = charV h (y⁻¹ * e * y) := fun e he => by
        rw [charV_of_mem _ he, ← hh₁, charConjE_apply]
      refine Px h₁ (Py h hh h₁ hh₁') h' fun e he => ?_
      rw [hh' e he, hh₁' _ (A_conj_mem hx he),
        show (x * y)⁻¹ * e * (x * y) = y⁻¹ * (x⁻¹ * e * x) * y by group]
    · rintro x (hx | hx)
      · have hcomm : ∀ (z : GL24), z ∈ E → ∀ h h' : Fin 6 → ZMod 3,
            (∀ e ∈ E, charV h' e = charV h (z⁻¹ * e * z)) → h' = h := by
          intro z hz h h' hh'
          refine charV_eq_iff.mp fun e he => ?_
          rw [hh' e he, mul_assoc, (E_comm e he z hz).eq, inv_mul_cancel_left]
        refine ⟨⟨E_le_A hx, fun h hh h' hh' => ?_⟩,
          ⟨A.inv_mem (E_le_A hx), fun h hh h' hh' => ?_⟩⟩
        · rw [hcomm x hx h h' hh']
          exact hh
        · rw [hcomm x⁻¹ (E.inv_mem hx) h h' hh']
          exact hh
      · have hg : ∃ i : Fin 3, x = g i := by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl | rfl
          exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
        obtain ⟨i, rfl⟩ := hg
        refine ⟨⟨g_mem_A3 i, fun h hh h' hh' => ?_⟩,
          ⟨A.inv_mem (g_mem_A3 i), fun h hh h' hh' => ?_⟩⟩
        · obtain ⟨h₀, hh₀, rfl⟩ := hTinv i h hh
          have : h' = h₀ := charV_eq_iff.mp fun e he => by
            rw [hh' e he, ← charE_conj_g i h₀ (A_conj_mem (g_mem_A3 i) he),
              show g i * ((g i)⁻¹ * e * g i) * (g i)⁻¹ = e by group]
          rwa [this]
        · have : h' = actT i h := charV_eq_iff.mp fun e he => by
            rw [hh' e he, inv_inv, charE_conj_g i h he]
          rw [this]
          exact hT i h hh
  rintro f' ⟨x, hx, hxf⟩
  exact (hP x hx).2 f hf f' hxf

theorem tree_check : (∀ k, treeOK k = true ∧ treeClosed k = true ∧
      ∀ c ∈ treeCodes k, encodeF (decodeF c) = c) ∧
    (∀ f, ∃ k, encodeF f ∈ treeCodes k) ∧ (∀ f, decodeF (encodeF f) = f) ∧
    (∀ f, encodeF f ∈ treeCodes 1 ↔ ∃ j, f = γ j ∨ f = -γ j) :=
  Certificates.certificate2140

@[expose] def orbSet (k : Fin 4) : Finset (Fin 6 → ZMod 3) := ((treeCodes k).map decodeF).toFinset

theorem treeCodes_getD (k : Fin 4) {m : ℕ} (hm : m < (orbTree k).length) :
    ((orbTree k).getD m (0, 0, 0)).1 ∈ treeCodes k := by
  unfold treeCodes
  rw [List.getD_eq_getElem _ _ hm]
  exact List.mem_map_of_mem (List.getElem_mem hm)

theorem orbSet_subset (k : Fin 4) : ↑(orbSet k) ⊆ charOrbit (orbRep k) := by
  have hok := (tree_check.1 k).1
  simp only [treeOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨_, hroot⟩, hstep⟩ := hok
  have hdec := tree_check.2.2.1
  have key : ∀ m < (orbTree k).length,
      decodeF ((orbTree k).getD m (0, 0, 0)).1 ∈ charOrbit (orbRep k) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      rcases hstep m hm with h0 | ⟨⟨hp, _⟩, hc⟩
      · subst h0
        have : ((orbTree k).getD 0 (0, 0, 0)).1 = (treeCodes k).headD 0 := by
          unfold treeCodes
          cases orbTree k with
          | nil => rfl
          | cons x l => rfl
        rw [this, hroot, hdec]
        exact mem_charOrbit_self _
      · rw [hc, hdec]
        exact actT_mem_charOrbit _ (ih _ hp (hp.trans hm))
  intro f hf
  rw [Finset.mem_coe] at hf
  simp only [orbSet, List.mem_toFinset, List.mem_map] at hf
  obtain ⟨c, hc, rfl⟩ := hf
  unfold treeCodes at hc
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
  obtain ⟨m, hm, hxm⟩ := List.getElem_of_mem hx
  have := key m hm
  rwa [List.getD_eq_getElem _ _ hm, hxm] at this

theorem orbSet_closed (k : Fin 4) : ∀ i, ∀ h ∈ orbSet k, actT i h ∈ orbSet k := by
  have hcl := (tree_check.1 k).2.1
  simp only [treeClosed, List.all_eq_true, List.mem_finRange, true_implies,
    List.contains_iff_mem] at hcl
  intro i h hh
  simp only [orbSet, List.mem_toFinset, List.mem_map] at hh ⊢
  obtain ⟨c, hc, rfl⟩ := hh
  exact ⟨_, hcl c hc i, tree_check.2.2.1 _⟩

theorem card_orbSet (k : Fin 4) : (orbSet k).card = orbSize k := by
  have hok := (tree_check.1 k).1
  simp only [treeOK, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨hlen, hnd⟩, _⟩, _⟩ := hok
  rw [orbSet, List.toFinset_card_of_nodup (by simpa using hnd), List.length_map, treeCodes,
    List.length_map, hlen]

theorem orbRep_mem (k : Fin 4) : orbRep k ∈ orbSet k := by
  have hok := (tree_check.1 k).1
  simp only [treeOK, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨hlen, _⟩, hroot⟩, _⟩ := hok
  have hpos : 0 < (treeCodes k).length := by
    rw [treeCodes, List.length_map, hlen]
    fin_cases k <;> simp [orbSize]
  simp only [orbSet, List.mem_toFinset, List.mem_map]
  refine ⟨(treeCodes k).headD 0, ?_, by rw [hroot, tree_check.2.2.1]⟩
  cases h : treeCodes k with
  | nil => rw [h] at hpos; simp at hpos
  | cons x l => exact List.mem_cons_self

theorem charOrbit_orbRep (k : Fin 4) : charOrbit (orbRep k) = ↑(orbSet k) :=
  le_antisymm (charOrbit_subset (orbRep_mem k) (orbSet_closed k)) (orbSet_subset k)

theorem charOrbit_eq (f : Fin 6 → ZMod 3) : ∃ k, charOrbit f = ↑(orbSet k) := by
  obtain ⟨k, hk⟩ := tree_check.2.1 f
  refine ⟨k, ?_⟩
  have hf : f ∈ orbSet k := by
    simp only [orbSet, List.mem_toFinset, List.mem_map]
    exact ⟨_, hk, tree_check.2.2.1 f⟩
  rw [charOrbit_eq_of_mem (orbSet_subset k hf), charOrbit_orbRep]

theorem ncard_charOrbit_orbRep (k : Fin 4) : (charOrbit (orbRep k)).ncard = orbSize k := by
  rw [charOrbit_orbRep, Set.ncard_coe_finset, card_orbSet]

theorem orbSet_one : (orbSet 1 : Set (Fin 6 → ZMod 3)) = {f | ∃ j, f = γ j ∨ f = -γ j} := by
  ext f
  simp only [orbSet, List.coe_toFinset, List.mem_map, Set.mem_ofPred_eq]
  rw [← tree_check.2.2.2 f]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rwa [(tree_check.1 1).2.2 c hc]
  · intro hf
    exact ⟨_, hf, tree_check.2.2.1 f⟩

theorem charOrbit_facts :
    Set.ncard (Set.range charOrbit) = 4 ∧
    (∀ f, (charOrbit f).ncard = 1 ∨ (charOrbit f).ncard = 24 ∨ (charOrbit f).ncard = 264 ∨
      (charOrbit f).ncard = 440) ∧
    (∀ n ∈ ({1, 24, 264, 440} : Finset ℕ), ∃ f, (charOrbit f).ncard = n) ∧
    ∀ f, (charOrbit f).ncard = 24 ↔ charOrbit f = {f' | ∃ j, f' = γ j ∨ f' = -γ j} := by
  have hrange : Set.range charOrbit = Set.range fun k => charOrbit (orbRep k) := by
    ext s
    constructor
    · rintro ⟨f, rfl⟩
      obtain ⟨k, hk⟩ := charOrbit_eq f
      exact ⟨k, (charOrbit_orbRep k).trans hk.symm⟩
    · rintro ⟨k, rfl⟩
      exact ⟨_, rfl⟩
  have hinj : Function.Injective fun k => charOrbit (orbRep k) := by
    intro k l h
    have h' : orbSize k = orbSize l := by
      have := congrArg Set.ncard h
      simpa only [ncard_charOrbit_orbRep] using this
    clear h
    revert k l
    decide
  have h24 : charOrbit (orbRep 1) = {f' | ∃ j, f' = γ j ∨ f' = -γ j} := by
    rw [charOrbit_orbRep, orbSet_one]
  refine ⟨?_, fun f => ?_, ?_, fun f => ?_⟩
  · rw [hrange, Set.ncard_range_of_injective hinj, Nat.card_fin]
  · obtain ⟨k, hk⟩ := charOrbit_eq f
    rw [hk, Set.ncard_coe_finset, card_orbSet]
    fin_cases k <;> simp [orbSize]
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl
    exacts [⟨_, ncard_charOrbit_orbRep 0⟩, ⟨_, ncard_charOrbit_orbRep 1⟩,
      ⟨_, ncard_charOrbit_orbRep 2⟩, ⟨_, ncard_charOrbit_orbRep 3⟩]
  · obtain ⟨k, hk⟩ := charOrbit_eq f
    constructor
    · intro h
      rw [hk, Set.ncard_coe_finset, card_orbSet] at h
      have hk1 : k = 1 := by
        revert h
        fin_cases k <;> simp [orbSize]
      rw [hk, hk1, ← charOrbit_orbRep]
      exact h24
    · intro h
      rw [h, ← h24]
      exact ncard_charOrbit_orbRep 1

end CFSG.Sporadic.Co1Schreier
