module

public import CFSG.LocalAnalysis.StandardType.GGResICellBasic
public import CFSG.LocalAnalysis.StandardType.GGResICertSound

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Line

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V] {n : ℕ}
  {T : Fin (n + 1) → Vector (ZMod p) (n + 2)} {g : Fin (n + 1) → (V ≃ₗ[ZMod p] V)}
  {h : Fin (n + 1) → V} {α : Fin (n + 1) → Module.Dual (ZMod p) V}

theorem ggResLettersWord_prod (F : List (Fin (n + 1) × List (Fin (n + 1)))) (jl : List (Fin n))
    (d : Fin n) (ws : List GGResLetter) :
    ((ggResLettersWord F jl d ws).map g).prod =
      (ws.map fun l => ((ggResLetterWord F jl d l).map g).prod).prod := by
  induction ws with
  | nil => rfl
  | cons l ws ih =>
    rw [List.map_cons, List.prod_cons, ← ih]
    simp only [ggResLettersWord, List.map_cons, List.flatten_cons, List.map_append, List.prod_append]

theorem ggGensWord_prod (F : List (Fin (n + 1) × List (Fin (n + 1)))) (jl : List (Fin n))
    (d : Fin n) (gens : List (List GGResLetter)) (e : List ℕ) :
    ((ggGensWord F jl d gens e).map g).prod =
      (e.map fun i => ((ggResLettersWord F jl d (gens.getD i [])).map g).prod).prod := by
  induction e with
  | nil => rfl
  | cons i e ih =>
    rw [List.map_cons, List.prod_cons, ← ih]
    simp only [ggGensWord, List.map_cons, List.flatten_cons, List.map_append, List.prod_append]

theorem ggResI_lineCheck_sound [Finite V] (hT : GGFTable (RingHom.id (ZMod p)) T h 0 α)
    (hg : ∀ k w, g k w = w - α k w • h k) (h2 : ∀ k, α k (h k) = 2)
    (hspan : Submodule.span (ZMod p) (Set.range h) = ⊤) (hind : LinearIndependent (ZMod p) h)
    {C : Matrix (Fin n) (Fin n) ℤ} {ib : Fin n} {allA : Bool} {P : Prop} (hP : allA = true → P)
    {TT : GGResLineJType} {jl : List (Fin n)} {K : List (List ℕ)} {z w : List ℕ}
    {F : List (Fin (n + 1) × List (Fin (n + 1)))} {gens : List (List GGResLetter)}
    {elts : List (List ℕ)} (hchk : ggResLineCheck T C ib allA TT jl K z w F gens elts = true) :
    GGResILineCertI ib C g α P := by
  simp only [ggResLineCheck, Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlen, hnd⟩, hne⟩, hall⟩, hcar⟩, hK⟩, hzw⟩, hz⟩, hF0⟩, hF⟩, hlet⟩,
    helts⟩, h1⟩, hcl⟩, hbad⟩ := hchk
  simp only [decide_eq_true_eq] at hlen hnd helts hbad
  simp only [List.all_eq_true, decide_eq_true_eq] at hne
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    decide_eq_true_eq] at hall
  simp only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] at hcar hK
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hzw
  simp only [List.any_eq_true, List.mem_finRange, true_and, decide_eq_true_eq] at hz
  simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff] at hF0
  simp only [List.all_eq_true] at hlet hF
  simp only [List.any_eq_true, decide_eq_true_eq] at h1
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, List.any_eq_true,
    decide_eq_true_eq] at hcl
  obtain ⟨e, he⟩ := ggResI_jlEquiv hlen hnd hne hall
  have hjl : ∀ j : Fin n, j ≠ ib → j ∈ jl := fun j hj => (hall j).resolve_left hj
  have hgetD : ∀ k : ℕ, k < jl.length → jl.getD k ib ∈ jl := fun k hk => by
    rw [List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem _
  set z' : V := ggFPi (RingHom.id (ZMod p)) h 0 (ggFVec z : Vector (ZMod p) (n + 2))
  set w' : V := ggFPi (RingHom.id (ZMod p)) h 0 (ggFVec w : Vector (ZMod p) (n + 2))
  have hroot : ∀ (k : Fin (n + 1)) (y : List ℕ), α k (ggFPi (RingHom.id (ZMod p)) h 0
      (ggFVec y : Vector (ZMod p) (n + 2))) = ggFDot (T k) (ggFVec y) :=
    fun k y => ggFPi_root hT k _
  set F' : List ((V ≃ₗ[ZMod p] V) × Fin (n + 1)) := F.map fun t => ((t.2.map g).prod, t.1)
  set genE : Fin gens.length → (V ≃ₗ[ZMod p] V) :=
    fun i => ((ggResLettersWord F jl ib (gens.getD i.val [])).map g).prod
  set eltE : List ℕ → (V ≃ₗ[ZMod p] V) := fun e => ((ggGensWord F jl ib gens e).map g).prod
  have hcons : ∀ (i : ℕ) (e : List ℕ),
      ggGensWord F jl ib gens (i :: e) = ggResLettersWord F jl ib (gens.getD i []) ++
        ggGensWord F jl ib gens e := fun i e => by
    simp only [ggGensWord, List.map_cons, List.flatten_cons]
  have hcard : Nat.card (Subgroup.closure (Set.range genE)) = elts.length := by
    rw [← List.length_map (f := eltE)]
    refine ggCard_closure_of_list ?_ ?_ ?_ ?_ ?_
    · refine List.Nodup.map_on (fun x hx y hy hxy => List.inj_on_of_nodup_map helts hx hy
        ((ggFMat_eq_iff hT hg hspan hind).mpr hxy)) (List.Nodup.of_map _ helts)
    · obtain ⟨e₀, he₀, he₀1⟩ := h1
      have : eltE e₀ = 1 := ggFMat_eq hT hg hspan he₀1
      exact this ▸ List.mem_map_of_mem he₀
    · rintro _ ⟨i, rfl⟩ _ hy
      obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp hy
      obtain ⟨e', he', hee'⟩ := ((hcl i.val i.isLt) e₀ he₀).1
      refine List.mem_map.mpr ⟨e', he', ?_⟩
      show ((ggGensWord F jl ib gens e').map g).prod =
        ((ggResLettersWord F jl ib (gens.getD i.val [])).map g).prod *
          ((ggGensWord F jl ib gens e₀).map g).prod
      rw [← ggFMat_eq hT hg hspan hee', hcons, List.map_append, List.prod_append]
    · rintro _ ⟨i, rfl⟩ _ hy
      obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp hy
      obtain ⟨e', he', hee'⟩ := ((hcl i.val i.isLt) e₀ he₀).2
      refine List.mem_map.mpr ⟨e', he', ?_⟩
      show ((ggGensWord F jl ib gens e').map g).prod =
        (((ggResLettersWord F jl ib (gens.getD i.val [])).map g).prod)⁻¹ *
          ((ggGensWord F jl ib gens e₀).map g).prod
      rw [← ggFMat_eq hT hg hspan hee', List.map_append, List.prod_append, ← ggF_word_inv hg h2]
    · intro y hy
      obtain ⟨e₀, -, rfl⟩ := List.mem_map.mp hy
      show ((ggGensWord F jl ib gens e₀).map g).prod ∈ _
      rw [ggGensWord_prod]
      refine Subgroup.list_prod_mem _ fun s hs => ?_
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hs
      by_cases hi : i < gens.length
      · exact Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩
      · rw [List.getD_eq_default _ _ (by omega)]
        exact Subgroup.one_mem _
  refine ⟨TT, e, fun k l => by rw [he k, he l]; exact hcar k l, ?_, z', w', F',
    Subgroup.closure (Set.range genE), fun j hj => ?_, fun j hj => ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hβ := ggResI_roots_indep hT (fun a : Fin TT.rank => (jl.getD a.val ib).castSucc)
      (fun l c => ((K.getD l.val []).getD c.val 0 : ZMod p)) hK
    refine (linearIndependent_equiv e).mp ?_
    convert hβ using 1
    funext a
    simp only [Function.comp_apply, he a]
  · rw [hroot]
    exact ((hzw j (hjl j hj)).1)
  · rw [hroot]
    exact ((hzw j (hjl j hj)).2)
  · obtain ⟨i, hi⟩ := hz
    exact ⟨i, by rw [hroot]; exact hi⟩
  · simpa [F'] using hF0
  · intro ψo hψo
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hψo
    have hFt := hF t ht
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hFt
    obtain ⟨⟨⟨hA, hzt⟩, hwt⟩, j, hj, hnc⟩ := hFt
    refine ⟨?_, ggResI_word_mem t.2, ?_, ?_, j, hne j hj, fun heq => hnc ?_⟩
    · rcases hA with hA | hA
      · exact Or.inl (hP hA)
      · exact Or.inr hA
    · show α t.1 (((t.2.map g).prod)⁻¹ z') = 0
      rw [ggF_root_conj hT hg h2 t, ggFFun_pi hT]
      exact hzt
    · show α t.1 (((t.2.map g).prod)⁻¹ w') ≠ 0
      rw [ggF_root_conj hT hg h2 t, ggFFun_pi hT]
      exact hwt
    · rw [ggFMat_eq_iff hT hg hspan hind]
      simp only [List.map_append, List.prod_append, List.map_cons, List.prod_cons, List.map_nil,
        List.prod_nil, mul_one, ggF_conjWord_prod hg h2]
      exact heq
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    show ((ggResLettersWord F jl ib (gens.getD i.val [])).map g).prod ∈ _
    rw [ggResLettersWord_prod]
    have hgi : gens.getD i.val [] ∈ gens := by
      rw [List.getD_eq_getElem _ _ i.isLt]
      exact List.getElem_mem _
    refine Subgroup.list_prod_mem _ fun s hs => ?_
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hs
    have hlok := hlet _ hgi l hl
    refine Subgroup.subset_closure ?_
    cases l with
    | f i' =>
      simp only [ggResLetterOk, decide_eq_true_eq] at hlok
      left
      have hmem : F.getD i' (0, []) ∈ F := by
        rw [List.getD_eq_getElem _ _ hlok]
        exact List.getElem_mem _
      refine ⟨(((F.getD i' (0, [])).2.map g).prod, (F.getD i' (0, [])).1), ?_, ?_⟩
      · exact List.mem_map.mpr ⟨_, hmem, rfl⟩
      · show ((ggConjWord (F.getD i' (0, []))).map g).prod = _
        rw [ggF_conjWord_prod hg h2]
    | j k =>
      simp only [ggResLetterOk, decide_eq_true_eq] at hlok
      right
      refine ⟨jl.getD k ib, hne _ (hgetD k hlok), ?_⟩
      show ([(jl.getD k ib).castSucc].map g).prod = _
      rw [List.map_singleton, List.prod_singleton]
  · rw [hcard]
    exact hbad

end Line

end CFSG.StandardType
