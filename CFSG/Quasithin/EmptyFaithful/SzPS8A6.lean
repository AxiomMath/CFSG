module

public import CFSG.Quasithin.EmptyFaithful.SzPS8Excl2Defs
public import CFSG.Quasithin.EmptyFaithful.SzPS8OvgMap
public import CFSG.Quasithin.EmptyFaithful.SzPS8A8Data
public import CFSG.Quasithin.Background.P4InspSpEmbed

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.G11
  CFSG.Quasithin.G11.P4InspSp

namespace SzPS8

abbrev Perm6 : Type := Equiv.Perm (Fin 6)

section Data6

@[expose] def u1 : Perm6 := Equiv.swap 0 1

@[expose] def u2 : Perm6 := Equiv.swap 2 3

@[expose] def u3 : Perm6 := Equiv.swap 0 2 * Equiv.swap 1 3

@[expose] def u4 : Perm6 := Equiv.swap 4 5

@[expose] def f1 : Perm6 := u1 * u4

@[expose] def f2 : Perm6 := u2 * u4

@[expose] def f3 : Perm6 := u3

@[expose] def r6 : Perm6 := Equiv.swap 0 4 * Equiv.swap 1 5

@[expose] def y6 : Perm6 := r6 * f3 * r6

@[expose] def ugens : List Perm6 := [u1, u2, u3, u4]

@[expose] def J6gens : List Perm6 := [f1, f2, f3, r6]

@[expose] def T6list : List Perm6 :=
  (List.range 2).flatMap fun a => (List.range 2).flatMap fun b => (List.range 2).flatMap fun c =>
    (List.range 2).map fun d => u1 ^ a * u2 ^ b * u3 ^ c * u4 ^ d

@[expose] def D6list : List Perm6 :=
  (List.range 2).flatMap fun a => (List.range 2).flatMap fun b => (List.range 2).map fun c =>
    f1 ^ a * f2 ^ b * f3 ^ c

@[expose] def J6list : List Perm6 := D6list.flatMap fun d => [d, d * r6, d * y6]

theorem T6_len : T6list.length = 16 := by decide +kernel

theorem T6_nodup : T6list.Nodup := by decide +kernel

theorem D6_len : D6list.length = 8 := by decide +kernel

theorem D6_nodup : D6list.Nodup := by decide +kernel

theorem J6_len : J6list.length = 24 := by decide +kernel

theorem J6_nodup : J6list.Nodup := by decide +kernel

theorem D6_alt : (D6list.all fun a => decide (Equiv.Perm.sign a = 1)) = true := by decide +kernel

theorem D6_inT : (D6list.all fun a => decide (a ∈ T6list)) = true := by decide +kernel

theorem T6_even_inD :
    (T6list.all fun a => !decide (Equiv.Perm.sign a = 1) || decide (a ∈ D6list)) = true := by
  decide +kernel

theorem T6_closed : (T6list.all fun a => ugens.all fun g => decide (a * g ∈ T6list)) = true := by
  decide +kernel

theorem T6_invol : (ugens.all fun g => decide (g⁻¹ = g)) = true := by decide +kernel

theorem J6_closed : (J6list.all fun a => J6gens.all fun g => decide (a * g ∈ J6list)) = true := by
  decide +kernel

theorem J6_invol : (J6gens.all fun g => decide (g⁻¹ = g)) = true := by decide +kernel

theorem J6_alt : (J6list.all fun a => decide (Equiv.Perm.sign a = 1)) = true := by decide +kernel

theorem J6_conj :
    (ugens.all fun s => J6gens.all fun j => decide (s * j * s⁻¹ ∈ J6list)) = true := by
  decide +kernel

theorem J6_inf : (D6list.all fun a => decide (a ∈ J6list)) = true := by decide +kernel

theorem one_mem_T6list : (1 : Perm6) ∈ T6list := by decide +kernel

theorem one_mem_J6list : (1 : Perm6) ∈ J6list := by decide +kernel

theorem w_y6 : y6 = r6 * f3 * r6⁻¹ := by decide +kernel

theorem T6_closed' : ∀ a ∈ T6list, ∀ g ∈ ugens, a * g ∈ T6list := by
  simpa [List.all_eq_true] using T6_closed

theorem T6_invol' : ∀ g ∈ ugens, g⁻¹ = g := by simpa [List.all_eq_true] using T6_invol

theorem J6_closed' : ∀ a ∈ J6list, ∀ g ∈ J6gens, a * g ∈ J6list := by
  simpa [List.all_eq_true] using J6_closed

theorem J6_invol' : ∀ g ∈ J6gens, g⁻¹ = g := by simpa [List.all_eq_true] using J6_invol

theorem J6_alt' : ∀ a ∈ J6list, Equiv.Perm.sign a = 1 := by
  simpa [List.all_eq_true] using J6_alt

theorem D6_alt' : ∀ a ∈ D6list, Equiv.Perm.sign a = 1 := by simpa [List.all_eq_true] using D6_alt

theorem D6_inT' : ∀ a ∈ D6list, a ∈ T6list := by simpa [List.all_eq_true] using D6_inT

theorem T6_even_inD' : ∀ a ∈ T6list, Equiv.Perm.sign a = 1 → a ∈ D6list := by
  simpa [List.all_eq_true, imp_iff_not_or] using T6_even_inD

theorem J6_conj' : ∀ s ∈ ugens, ∀ j ∈ J6gens, s * j * s⁻¹ ∈ J6list := by
  simpa [List.all_eq_true] using J6_conj

theorem J6_inf' : ∀ a ∈ D6list, a ∈ J6list := by simpa [List.all_eq_true] using J6_inf

end Data6

section Groups6

@[expose] def T6 : Subgroup Perm6 := Subgroup.closure {u1, u2, u3, u4}

@[expose] def J6 : Subgroup Perm6 := Subgroup.closure {f1, f2, f3, r6}

theorem u1_mem : u1 ∈ T6 := Subgroup.subset_closure (by simp)

theorem u2_mem : u2 ∈ T6 := Subgroup.subset_closure (by simp)

theorem u3_mem : u3 ∈ T6 := Subgroup.subset_closure (by simp)

theorem u4_mem : u4 ∈ T6 := Subgroup.subset_closure (by simp)

theorem mem_T6_iff {x : Perm6} : x ∈ T6 ↔ x ∈ T6list := by
  constructor
  · intro hx
    have hgen : ∀ y ∈ ({u1, u2, u3, u4} : Set Perm6), y ∈ ugens := by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> simp [ugens]
    induction hx using Subgroup.closure_induction_right with
    | one => exact one_mem_T6list
    | mul_right x hx y hy ih => exact T6_closed' x ih y (hgen y hy)
    | mul_inv_cancel x hx y hy ih =>
        rw [T6_invol' y (hgen y hy)]
        exact T6_closed' x ih y (hgen y hy)
  · intro hx
    simp only [T6list, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨a, -, b, -, c, -, d, -, rfl⟩ := hx
    exact T6.mul_mem (T6.mul_mem (T6.mul_mem (T6.pow_mem u1_mem a) (T6.pow_mem u2_mem b))
      (T6.pow_mem u3_mem c)) (T6.pow_mem u4_mem d)

theorem mem_T6_inf_iff {x : Perm6} : x ∈ T6 ⊓ alternatingGroup (Fin 6) ↔ x ∈ D6list := by
  constructor
  · rintro ⟨hx1, hx2⟩
    exact T6_even_inD' x (mem_T6_iff.1 hx1) ((Equiv.Perm.mem_alternatingGroup).1 hx2)
  · intro hx
    exact ⟨mem_T6_iff.2 (D6_inT' x hx), (Equiv.Perm.mem_alternatingGroup).2 (D6_alt' x hx)⟩

theorem f1_mem : f1 ∈ J6 := Subgroup.subset_closure (by simp)

theorem f2_mem : f2 ∈ J6 := Subgroup.subset_closure (by simp)

theorem f3_mem : f3 ∈ J6 := Subgroup.subset_closure (by simp)

theorem r6_mem : r6 ∈ J6 := Subgroup.subset_closure (by simp)

theorem y6_mem : y6 ∈ J6 := by
  rw [w_y6]
  exact J6.mul_mem (J6.mul_mem r6_mem f3_mem) (J6.inv_mem r6_mem)

theorem D6_mem_J6 {d : Perm6} (hd : d ∈ D6list) : d ∈ J6 := by
  simp only [D6list, List.mem_flatMap, List.mem_map, List.mem_range] at hd
  obtain ⟨a, -, b, -, c, -, rfl⟩ := hd
  exact J6.mul_mem (J6.mul_mem (J6.pow_mem f1_mem a) (J6.pow_mem f2_mem b)) (J6.pow_mem f3_mem c)

theorem mem_J6_iff {x : Perm6} : x ∈ J6 ↔ x ∈ J6list := by
  constructor
  · intro hx
    have hgen : ∀ y ∈ ({f1, f2, f3, r6} : Set Perm6), y ∈ J6gens := by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> simp [J6gens]
    induction hx using Subgroup.closure_induction_right with
    | one => exact one_mem_J6list
    | mul_right x hx y hy ih => exact J6_closed' x ih y (hgen y hy)
    | mul_inv_cancel x hx y hy ih =>
        rw [J6_invol' y (hgen y hy)]
        exact J6_closed' x ih y (hgen y hy)
  · intro hx
    obtain ⟨d, hd, hx⟩ := List.mem_flatMap.1 hx
    have hdJ : d ∈ J6 := D6_mem_J6 hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hdJ
    · exact J6.mul_mem hdJ r6_mem
    · exact J6.mul_mem hdJ y6_mem

theorem J6_le_alt : J6 ≤ alternatingGroup (Fin 6) := fun x hx =>
  (Equiv.Perm.mem_alternatingGroup).2 (J6_alt' x (mem_J6_iff.1 hx))

theorem card_T6 : Nat.card T6 = 16 := by
  rw [card_eq_length8 (H := T6) (l := T6list) (fun x => mem_T6_iff) T6_nodup, T6_len]

theorem card_T6_inf : Nat.card ↥(T6 ⊓ alternatingGroup (Fin 6)) = 8 := by
  rw [card_eq_length8 (H := T6 ⊓ alternatingGroup (Fin 6)) (l := D6list)
    (fun x => mem_T6_inf_iff) D6_nodup, D6_len]

theorem card_J6 : Nat.card J6 = 24 := by
  rw [card_eq_length8 (H := J6) (l := J6list) (fun x => mem_J6_iff) J6_nodup, J6_len]

theorem card_perm_six : Nat.card Perm6 = 720 := by
  rw [Nat.card_perm, Nat.card_fin]
  rfl

theorem card_alt_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  have h := two_mul_card_alternatingGroup (α := Fin 6)
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_perm_six] at h
  omega

theorem isSylowTwoOf_T6_top : IsSylowTwoOf T6 ⊤ := by
  refine ⟨le_top, IsPGroup.of_card (n := 4) (by rw [card_T6]; norm_num), ?_⟩
  have h1 := Subgroup.card_mul_index T6
  rw [card_T6, card_perm_six] at h1
  have h2 : (T6.subgroupOf ⊤).index = T6.index := by
    rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
  rw [h2]
  omega

theorem isSylowTwoOf_T6_inf :
    IsSylowTwoOf (T6 ⊓ alternatingGroup (Fin 6)) (alternatingGroup (Fin 6)) := by
  refine ⟨inf_le_right, IsPGroup.of_card (n := 3) (by rw [card_T6_inf]; norm_num), ?_⟩
  have h1 := Subgroup.relIndex_mul_card (T6 ⊓ alternatingGroup (Fin 6)) (alternatingGroup (Fin 6))
  rw [inf_eq_left.2 inf_le_right, card_T6_inf, card_alt_six] at h1
  show ¬ 2 ∣ (T6 ⊓ alternatingGroup (Fin 6)).relIndex (alternatingGroup (Fin 6))
  omega

theorem T6_le_normalizer_J6 : T6 ≤ Subgroup.normalizer (J6 : Set Perm6) := by
  rw [T6, Subgroup.closure_le]
  intro g hg
  have hgen : g ∈ ugens := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp [ugens]
  have h1 : ∀ j ∈ J6, g * j * g⁻¹ ∈ J6 := by
    intro j hj
    induction hj using Subgroup.closure_induction with
    | mem y hy =>
        have hy' : y ∈ J6gens := by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl | rfl | rfl <;> simp [J6gens]
        exact mem_J6_iff.2 (J6_conj' g hgen y hy')
    | one => simp [J6.one_mem]
    | mul a b _ _ ha hb =>
        have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
        rw [this]
        exact J6.mul_mem ha hb
    | inv a _ ha =>
        have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
        rw [this]
        exact J6.inv_mem ha
  show g ∈ Subgroup.normalizer (J6 : Set Perm6)
  rw [Subgroup.mem_normalizer_iff]
  intro j
  refine ⟨fun hj => h1 j hj, fun hj => ?_⟩
  have h2 := h1 _ hj
  have hg' : g⁻¹ = g := T6_invol' g hgen
  have hgg : g * g = 1 := by
    have := mul_inv_cancel g
    rwa [hg'] at this
  rw [hg'] at h2
  have e : g * (g * j * g) * g = j := by
    calc g * (g * j * g) * g = (g * g) * j * (g * g) := by simp only [mul_assoc]
      _ = j := by rw [hgg]; simp
  rw [e] at h2
  exact h2

theorem relIndex_T6_J6 : T6.relIndex J6 = 3 := by
  have h1 := Subgroup.relIndex_mul_card (H := T6) (K := J6)
  have h2 : T6 ⊓ J6 = T6 ⊓ alternatingGroup (Fin 6) := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨hx1, J6_le_alt hx2⟩
    · intro hx
      exact ⟨hx.1, mem_J6_iff.2 (J6_inf' x (mem_T6_inf_iff.1 hx))⟩
  rw [h2, card_T6_inf, card_J6] at h1
  omega

end Groups6

section Vec6

@[expose] def a6 : ↥(permCore 6) :=
  ⟨![0, 0, 0, 0, 1, 1], by
    show ∑ i : Fin 6, (![0, 0, 0, 0, 1, 1] : Fin 6 → ZMod 2) i = 0
    decide⟩

theorem f1_memD : f1 ∈ T6 ⊓ alternatingGroup (Fin 6) := mem_T6_inf_iff.2 (by decide +kernel)

theorem f2_memD : f2 ∈ T6 ⊓ alternatingGroup (Fin 6) := mem_T6_inf_iff.2 (by decide +kernel)

theorem f3_memD : f3 ∈ T6 ⊓ alternatingGroup (Fin 6) := mem_T6_inf_iff.2 (by decide +kernel)

theorem fixed_finite6 : ∀ x : Fin 6 → ZMod 2, ∑ i, x i = 0 →
    ((∀ i, x (f1⁻¹ i) = x i) ∨ (∀ i, x (f1⁻¹ i) = x i + 1)) →
    ((∀ i, x (f2⁻¹ i) = x i) ∨ (∀ i, x (f2⁻¹ i) = x i + 1)) →
    ((∀ i, x (f3⁻¹ i) = x i) ∨ (∀ i, x (f3⁻¹ i) = x i + 1)) →
    x = 0 ∨ x = (fun _ => 1) ∨ x = ![0, 0, 0, 0, 1, 1] ∨ x = ![1, 1, 1, 1, 0, 0] := by
  decide +kernel

theorem r6_move_fin :
    ¬ ((∀ i : Fin 6, (![0, 0, 0, 0, 1, 1] : Fin 6 → ZMod 2) (r6⁻¹ i) = ![0, 0, 0, 0, 1, 1] i) ∨
      (∀ i : Fin 6, (![0, 0, 0, 0, 1, 1] : Fin 6 → ZMod 2) (r6⁻¹ i) =
        ![0, 0, 0, 0, 1, 1] i + 1)) := by
  decide +kernel

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] {f : LinearMap.BilinForm (ZMod 2) U}

theorem beta_fix_iff (M : A6Model f) (ρ : Perm6 →* GLV U)
    (hρβ : ∀ σ x, ρ σ (M.β x) = M.β (permLin σ x)) (σ : Perm6) (x : ↥(permCore 6)) :
    ρ σ (M.β x) = M.β x ↔
      ((∀ i, permAct σ (x : Fin 6 → ZMod 2) i = (x : Fin 6 → ZMod 2) i) ∨
        (∀ i, permAct σ (x : Fin 6 → ZMod 2) i = (x : Fin 6 → ZMod 2) i + 1)) := by
  rw [hρβ, ← sub_eq_zero, ← map_sub, M.ker]
  constructor
  · rintro (h | h)
    · left
      intro i
      have := congrFun h i
      simpa [permLin_coe, sub_eq_zero] using this
    · right
      intro i
      have := h i
      simp only [Submodule.coe_sub, Pi.sub_apply, permLin_coe] at this
      exact sub_eq_iff_eq_add'.1 this
  · rintro (h | h)
    · left
      funext i
      simp [permLin_coe, h i]
    · right
      intro i
      simp [permLin_coe, h i]

theorem fixed_class6 (M : A6Model f) (ρ : Perm6 →* GLV U)
    (hρβ : ∀ σ x, ρ σ (M.β x) = M.β (permLin σ x)) (w : U) (hw0 : w ≠ 0)
    (hfix : ∀ s ∈ T6 ⊓ alternatingGroup (Fin 6), ρ s w = w) : w = M.β a6 := by
  obtain ⟨x, rfl⟩ := M.surj w
  have h1 := (beta_fix_iff M ρ hρβ f1 x).1 (hfix f1 f1_memD)
  have h2 := (beta_fix_iff M ρ hρβ f2 x).1 (hfix f2 f2_memD)
  have h3 := (beta_fix_iff M ρ hρβ f3 x).1 (hfix f3 f3_memD)
  have hsum : ∑ i, (x : Fin 6 → ZMod 2) i = 0 := x.2
  have key := fixed_finite6 (x : Fin 6 → ZMod 2) hsum h1 h2 h3
  rcases key with h | h | h | h
  · exfalso
    apply hw0
    have : x = 0 := Subtype.ext h
    rw [this, map_zero]
  · exfalso
    apply hw0
    rw [M.ker]
    exact Or.inr fun i => by rw [h]
  · have : x = a6 := Subtype.ext h
    rw [this]
  · have h0 : M.β (x - a6) = 0 := by
      rw [M.ker]
      right
      intro i
      simp only [Submodule.coe_sub, Pi.sub_apply, h, a6]
      fin_cases i <;> decide
    rw [map_sub, sub_eq_zero] at h0
    exact h0

theorem r6_moves (M : A6Model f) (ρ : Perm6 →* GLV U)
    (hρβ : ∀ σ x, ρ σ (M.β x) = M.β (permLin σ x)) : ρ r6 (M.β a6) ≠ M.β a6 := by
  rw [Ne, beta_fix_iff M ρ hρβ]
  exact r6_move_fin

end Vec6

section Model6

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] {f : LinearMap.BilinForm (ZMod 2) U}

theorem false_of_model6 [Finite U] (M : A6Model f) (ρ : Perm6 →* GLV U)
    (hinj : Function.Injective ρ) (hρβ : ∀ σ x, ρ σ (M.β x) = M.β (permLin σ x))
    {K : Subgroup Perm6} (hK : K = alternatingGroup (Fin 6) ∨ K = ⊤)
    {S' : Subgroup (GLV U)} (hS' : IsSylowTwoOf S' (K.map ρ)) {v' : U} (hv0 : v' ≠ 0)
    (hfix : ∀ s ∈ S', s v' = v') (hF : OvgFix S' ((alternatingGroup (Fin 6)).map ρ) v') :
    False := by
  have hAK : alternatingGroup (Fin 6) ≤ K := by
    rcases hK with rfl | rfl
    · exact le_rfl
    · exact le_top
  have hT6K : IsSylowTwoOf (T6 ⊓ K) K := by
    rcases hK with rfl | rfl
    · exact isSylowTwoOf_T6_inf
    · rw [inf_top_eq]
      exact isSylowTwoOf_T6_top
  have hT' : IsSylowTwoOf ((T6 ⊓ K).map ρ) (K.map ρ) := isSylowTwoOf_map_of_injective hinj hT6K
  obtain ⟨γ, hγ, hγT⟩ := exists_conj_eq_of_isSylowTwoOf hS' hT'
  obtain ⟨g, hgK, rfl⟩ := hγ
  have hnorm : ∀ n ∈ (alternatingGroup (Fin 6)).map ρ,
      (ρ g)⁻¹ * n * ρ g ∈ (alternatingGroup (Fin 6)).map ρ := by
    rintro _ ⟨τ, hτ, rfl⟩
    refine ⟨g⁻¹ * τ * g, ?_, by simp [map_mul, map_inv]⟩
    have := (alternatingGroup.normal : (alternatingGroup (Fin 6)).Normal).conj_mem τ hτ g⁻¹
    simpa using this
  have hF' := hF.conj_of hnorm hγT
  have hw0 : ρ g v' ≠ 0 := fun h0 => hv0 ((map_eq_zero_iff (ρ g) (ρ g).injective).mp h0)
  have hwfix : ∀ s ∈ T6 ⊓ alternatingGroup (Fin 6), ρ s (ρ g v') = ρ g v' := by
    intro s hs
    have hs' : ρ s ∈ (T6 ⊓ K).map ρ := ⟨s, ⟨hs.1, hAK hs.2⟩, rfl⟩
    obtain ⟨y, hy, hys⟩ := (hγT _).mp hs'
    have h1 : ρ g (y v') = ρ g v' := by rw [hfix y hy]
    calc ρ s (ρ g v') = (ρ g * y * (ρ g)⁻¹) (ρ g v') := by rw [← hys]
      _ = ρ g (y v') := by simp
      _ = ρ g v' := h1
  have hw := fixed_class6 M ρ hρβ _ hw0 hwfix
  have hJA : J6.map ρ ≤ (alternatingGroup (Fin 6)).map ρ := Subgroup.map_mono J6_le_alt
  have hJn : ∀ t ∈ (T6 ⊓ K).map ρ, ∀ j' ∈ J6.map ρ, t * j' * t⁻¹ ∈ J6.map ρ := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨j, hj, rfl⟩
    refine ⟨s * j * s⁻¹, ?_, by simp [map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.1 (T6_le_normalizer_J6 hs.1) j).1 hj
  have hidx : ((T6 ⊓ K).map ρ).relIndex (J6.map ρ) = 3 := by
    rw [Subgroup.relIndex_map_map_of_injective _ _ hinj, ← Subgroup.relIndex_inf_mul_relIndex,
      inf_of_le_right (J6_le_alt.trans hAK), Subgroup.relIndex_eq_one.mpr (J6_le_alt.trans hAK),
      mul_one]
    exact relIndex_T6_J6
  have := hF' (J6.map ρ) hJA hJn (Or.inl hidx) (ρ r6) ⟨r6, r6_mem, rfl⟩
  rw [hw] at this
  exact r6_moves M ρ hρβ this

end Model6

section Concl6

theorem alt_le_of_normal_fin {n : ℕ} (hn : 5 ≤ n) {K N : Subgroup (Equiv.Perm (Fin n))}
    (hK : K = alternatingGroup (Fin n) ∨ K = ⊤) (hNK : N ≤ K)
    (hnorm : ∀ k ∈ K, ∀ m ∈ N, k * m * k⁻¹ ∈ N) (hN1 : N ≠ ⊥) : alternatingGroup (Fin n) ≤ N := by
  rcases hK with rfl | rfl
  · have : IsSimpleGroup ↥(alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by simpa using hn)
    have hnorm' : (N.subgroupOf (alternatingGroup (Fin n))).Normal := by
      refine ⟨fun m hm g => ?_⟩
      exact hnorm g.1 g.2 m hm
    have := hnorm'
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (alternatingGroup (Fin n)))
      with h | h
    · exfalso
      apply hN1
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hNK hx⟩ : ↥(alternatingGroup (Fin n))) ∈
          N.subgroupOf (alternatingGroup (Fin n)) := hx
      rw [h, Subgroup.mem_bot] at this
      exact (Subgroup.mem_bot).2 (congrArg Subtype.val this)
    · intro x hx
      have : (⟨x, hx⟩ : ↥(alternatingGroup (Fin n))) ∈ N.subgroupOf (alternatingGroup (Fin n)) := by
        rw [h]
        exact Subgroup.mem_top _
      exact this
  · have : N.Normal := ⟨fun m hm g => hnorm g (Subgroup.mem_top g) m hm⟩
    exact Equiv.Perm.alternatingGroup_le_of_normal (by simpa using hn)
      ((Subgroup.nontrivial_iff_ne_bot N).2 hN1)

theorem false_of_a6 {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {B : LinearMap.BilinForm (ZMod 2) V} {Γ T0 : Subgroup (V ≃ₗ[ZMod 2] V)} {v : V}
    (S : OvgSymp B Γ T0 v) (hdim : Module.finrank (ZMod 2) V = 4) (N6 : Subgroup ↥Γ)
    (hcard : Nat.card ↥N6 = 360) : False := by
  classical
  have : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun e => (e : V → V)) fun _ _ h => LinearEquiv.ext (congrFun h)
  have hf : IsSymplectic B := ⟨S.alt, S.nondegenerate⟩
  obtain ⟨M⟩ := p4inspsp_exists_model hf hdim
  obtain ⟨ρ, hinj, -, hρβ, hrange⟩ := p4inspsp_exists_embedding hf hdim M
  have hΓsp : Γ ≤ ρ.range := fun γ hγ => hrange (fun x y => S.isometry γ hγ x y)
  set K := Γ.comap ρ with hKdef
  have hΓK : Γ = K.map ρ := by
    rw [hKdef, Subgroup.map_comap_eq, inf_eq_right.2 hΓsp]
  have hdvd1 : 360 ∣ Nat.card K := by
    have h1 : Nat.card ↥N6 ∣ Nat.card ↥Γ := N6.card_subgroup_dvd_card
    rw [hcard, hΓK, Subgroup.card_map_of_injective hinj] at h1
    exact h1
  have hdvd2 : Nat.card K ∣ 720 := by
    have := K.card_subgroup_dvd_card
    rwa [card_perm_six] at this
  have hKidx : K.index ≤ 2 := by
    have h1 := Subgroup.card_mul_index K
    rw [card_perm_six] at h1
    obtain ⟨c, hc⟩ := hdvd1
    have hpos : 0 < Nat.card K := Nat.card_pos
    rw [hc] at h1 hpos hdvd2
    have hc2 : c ≤ 2 := by
      have := Nat.le_of_dvd (by norm_num) hdvd2
      omega
    interval_cases c <;> omega
  have hK : K = alternatingGroup (Fin 6) ∨ K = ⊤ := by
    have h0 : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rcases (by omega : K.index = 1 ∨ K.index = 2) with h | h
    · exact Or.inr (Subgroup.index_eq_one.1 h)
    · exact Or.inl (Equiv.Perm.eq_alternatingGroup_of_index_eq_two h)
  obtain ⟨N, hNn, hN1, hF0⟩ := S.toOvgSetting.exists_normal_subtype
  set N'' := (N.map Γ.subtype).comap ρ with hN''def
  have hN''K : N'' ≤ K := fun n hn => by
    have : ρ n ∈ N.map Γ.subtype := hn
    exact Subgroup.map_subtype_le N this
  have hN''norm : ∀ k ∈ K, ∀ n ∈ N'', k * n * k⁻¹ ∈ N'' := by
    intro k hk n hn
    obtain ⟨m, hm, hmn⟩ := (hn : ρ n ∈ N.map Γ.subtype)
    have hk' : ρ k ∈ Γ := hk
    show ρ (k * n * k⁻¹) ∈ N.map Γ.subtype
    refine ⟨⟨ρ k, hk'⟩ * m * ⟨ρ k, hk'⟩⁻¹, hNn.conj_mem m hm ⟨ρ k, hk'⟩, ?_⟩
    have e : ρ (k * n * k⁻¹) = ρ k * ρ n * (ρ k)⁻¹ := by simp [map_mul, map_inv]
    rw [e, ← hmn]
    rfl
  have hN''1 : N'' ≠ ⊥ := by
    intro hbot
    apply hN1
    have h1 : N.map Γ.subtype = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨n, rfl⟩ := hΓsp (Subgroup.map_subtype_le N hx)
      have hn : n ∈ N'' := hx
      rw [hbot, Subgroup.mem_bot] at hn
      rw [hn, map_one]
      exact Subgroup.one_mem _
    exact (Subgroup.map_eq_bot_iff_of_injective _ Γ.subtype_injective).mp h1
  have hAN'' : alternatingGroup (Fin 6) ≤ N'' :=
    alt_le_of_normal_fin (by norm_num) hK hN''K hN''norm hN''1
  have hAN : (alternatingGroup (Fin 6)).map ρ ≤ N.map Γ.subtype := by
    rintro _ ⟨τ, hτ, rfl⟩
    exact hAN'' hτ
  have hF1 : OvgFix T0 ((alternatingGroup (Fin 6)).map ρ) v := hF0.mono hAN
  have hS'syl : IsSylowTwoOf T0 (K.map ρ) := by
    rw [← hΓK]
    exact S.sylow
  exact false_of_model6 M ρ hinj hρβ hK hS'syl S.ne_zero S.fix hF1

end Concl6

theorem excl2NoNormalA6 (h11 : StageLemma14111) (h113 : StageLemma14113) (h35 : Lemma1435) :
    Excl2NoNormalA6 := by
  intro G _ _ T M hyp hnot hU D hdim hN
  obtain ⟨N, -, ⟨e⟩⟩ := hN
  obtain ⟨v, S⟩ := exists_ovgSymp h11 h113 h35 hyp hnot hU D
  have hcard : Nat.card ↥N = 360 := by
    rw [Nat.card_congr e.toEquiv, card_alt_six]
  exact false_of_a6 S hdim N hcard

end SzPS8

end CFSG.Quasithin
