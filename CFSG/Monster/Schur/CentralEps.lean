module

public import CFSG.Monster.Schur.Defs
public import CFSG.Certificates.CosetTablePresented
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star

public section

namespace CFSG.Monster.Schur

open CFSG.CosetTable

section DoubleCover

variable {E G : Type*} [Group E] [Group G] (π : E →* G)

theorem sq_eq_one_of_mem_ker (h : Nat.card π.ker = 2) {x : E} (hx : x ∈ π.ker) : x ^ 2 = 1 := by
  have := pow_card_eq_one' (G := π.ker) (x := ⟨x, hx⟩)
  rw [h] at this
  exact congrArg Subtype.val this

theorem mem_center_of_mem_ker (h : Nat.card π.ker = 2) {x : E} (hx : x ∈ π.ker) :
    x ∈ Subgroup.center E := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨t, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : π.ker)).mp h
  by_cases hx1 : x = 1
  · subst hx1; simp
  · have hxt : (⟨x, hx⟩ : π.ker) = t := huniq _ (fun h' => hx1 (congrArg Subtype.val h'))
    have hmem : g * x * g⁻¹ ∈ π.ker := π.normal_ker.conj_mem x hx g
    have hne : (⟨g * x * g⁻¹, hmem⟩ : π.ker) ≠ 1 := by
      intro h'
      apply hx1
      have h'' : g * x * g⁻¹ = 1 := congrArg Subtype.val h'
      simpa using h''
    have e : g * x * g⁻¹ = x := congrArg Subtype.val ((huniq _ hne).trans hxt.symm)
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [e]

theorem exists_ker_elem (h : Nat.card π.ker = 2) :
    ∃ z : E, z ∈ π.ker ∧ z ≠ 1 ∧ ∀ k ∈ π.ker, k = 1 ∨ k = z := by
  obtain ⟨t, ht, huniq⟩ := (Nat.card_eq_two_iff' (1 : π.ker)).mp h
  refine ⟨t, t.2, fun h' => ht (Subtype.ext h'), fun k hk => ?_⟩
  by_cases hk1 : k = 1
  · exact Or.inl hk1
  · exact Or.inr (congrArg Subtype.val (huniq ⟨k, hk⟩ (fun h' => hk1 (congrArg Subtype.val h'))))

theorem exists_lift_pow_eq_one (h : Nat.card π.ker = 2) {x : E} {n : ℕ} (hn : Odd n)
    (hx : π x ^ n = 1) : ∃ y : E, π y = π x ∧ y ^ n = 1 := by
  have hu : x ^ n ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow]; exact hx
  have hu2 := sq_eq_one_of_mem_ker π h hu
  refine ⟨x ^ (n + 1), by rw [pow_succ, map_mul, map_pow, hx, one_mul], ?_⟩
  obtain ⟨k, hk⟩ := hn
  have hnk : n + 1 = 2 * (k + 1) := by omega
  calc (x ^ (n + 1)) ^ n = (x ^ n) ^ (n + 1) := by rw [← pow_mul, ← pow_mul, mul_comm]
    _ = ((x ^ n) ^ 2) ^ (k + 1) := by rw [← pow_mul (x ^ n) 2 (k + 1), ← hnk]
    _ = 1 := by rw [hu2, one_pow]

theorem exists_lift_pair (h : Nat.card π.ker = 2) (a b : E) {p q : ℕ} (hp : Odd p) (hq : Odd q)
    (hb : π b ^ p = 1) (hab : (π a * π b) ^ q = 1) :
    ∃ a' b' : E, π a' = π a ∧ π b' = π b ∧ b' ^ p = 1 ∧ (a' * b') ^ q = 1 := by
  obtain ⟨b', hb'π, hb'p⟩ := exists_lift_pow_eq_one π h hp hb
  have hζ : (a * b') ^ q ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, map_mul, hb'π]; exact hab
  have hζ2 := sq_eq_one_of_mem_ker π h hζ
  have hζc := mem_center_of_mem_ker π h hζ
  refine ⟨a * (a * b') ^ q, b', ?_, hb'π, hb'p, ?_⟩
  · rw [map_mul, MonoidHom.mem_ker.mp hζ, mul_one]
  · have hcomm : Commute ((a * b') ^ q) (a * b') := (Commute.refl _).pow_left q
    have hcz : Commute ((a * b') ^ q) a := Subgroup.mem_center_iff.mp hζc a |>.symm
    have e : a * (a * b') ^ q * b' = (a * b') ^ q * (a * b') := by
      rw [← hcz.eq, mul_assoc]
    rw [e, hcomm.mul_pow, ← pow_succ]
    obtain ⟨k, hk⟩ := hq
    have hqk : q + 1 = 2 * (k + 1) := by omega
    calc ((a * b') ^ q) ^ (q + 1) = (((a * b') ^ q) ^ 2) ^ (k + 1) := by
          rw [← pow_mul ((a * b') ^ q) 2 (k + 1), ← hqk]
      _ = 1 := by rw [hζ2, one_pow]

end DoubleCover

theorem card_eq_mul_card_ker {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Surjective f) : Nat.card A = Nat.card B * Nat.card f.ker := by
  rw [← Subgroup.index_mul_card f.ker, Subgroup.index_ker]
  congr 1
  rw [MonoidHom.range_eq_top.mpr hf, Subgroup.card_top]

theorem false_of_card_le {G : Type*} [Group G] [Finite G] {Γ : Type*} [Group Γ] [Finite Γ]
    (hcard : Nat.card Γ ≤ Nat.card G) {E : Type} [Group E] [Group.IsPerfect E] (π : E →* G)
    (hπ : Function.Surjective π) (hk : Nat.card π.ker = 2) (ρ : Γ →* E)
    (hρ : Function.Surjective (π.comp ρ)) : False := by
  set S := ρ.range with hSdef
  have hfinS : Finite S := Finite.of_surjective _ ρ.rangeRestrict_surjective
  have hres : Function.Surjective (π.comp S.subtype) := by
    intro g
    obtain ⟨γ, hγ⟩ := hρ g
    exact ⟨⟨ρ γ, ρ.mem_range.mpr ⟨γ, rfl⟩⟩, hγ⟩
  have h1 := card_eq_mul_card_ker (π.comp S.subtype) hres
  have hSΓ : Nat.card S ≤ Nat.card Γ :=
    Nat.card_le_card_of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hGpos : 0 < Nat.card G := Nat.card_pos
  have hkpos : 0 < Nat.card (π.comp S.subtype).ker := Nat.card_pos
  have hk1 : Nat.card (π.comp S.subtype).ker = 1 := by
    by_contra hne
    have : 2 ≤ Nat.card (π.comp S.subtype).ker := by omega
    nlinarith
  have hSG : Nat.card S = Nat.card G := by rw [h1, hk1, mul_one]
  have hE := card_eq_mul_card_ker π hπ
  rw [hk] at hE
  have hidx : S.index * Nat.card S = Nat.card E := Subgroup.index_mul_card S
  rw [hSG, hE] at hidx
  have hidx2 : S.index = 2 := by
    have h3 : S.index * Nat.card G = 2 * Nat.card G := by rw [hidx]; ring
    exact Nat.eq_of_mul_eq_mul_right hGpos h3
  have hS2 : S.Normal := Subgroup.normal_of_index_eq_two hidx2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : Nat.card (E ⧸ S) = 2 := hidx2
  have : IsCyclic (E ⧸ S) := isCyclic_of_prime_card hc
  have : Finite (E ⧸ S) := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial (E ⧸ S) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  exact Group.IsPerfect.not_isMulCommutative (E ⧸ S) inferInstance

@[expose] def zLetter (m : ℕ) : Fin (m + 1) × Bool := (Fin.last m, true)

@[expose] def castWord {m : ℕ} (w : List (Fin m × Bool)) : List (Fin (m + 1) × Bool) :=
  w.map fun x => (x.1.castSucc, x.2)

@[expose] def epsRels {m k : ℕ} (U : List (List (Fin m × Bool))) (T : Fin k → List (Fin m × Bool))
    (e : Fin k → Bool) : List (List (Fin (m + 1) × Bool)) :=
  [zLetter m, zLetter m] ::
    ((List.finRange m).map fun i =>
      [zLetter m, (i.castSucc, true), zLetter m, (i.castSucc, false)]) ++
    U.map castWord ++
    (List.finRange k).map fun i => castWord (T i) ++ (if e i then [zLetter m] else [])

section Lift

variable {E : Type*} [Group E]

theorem lift_mk_append {α : Type*} (f : α → E) (u v : List (α × Bool)) :
    FreeGroup.lift f (FreeGroup.mk (u ++ v)) =
      FreeGroup.lift f (FreeGroup.mk u) * FreeGroup.lift f (FreeGroup.mk v) := by
  rw [← FreeGroup.mul_mk, map_mul]

theorem lift_mk_castWord {m : ℕ} (f : Fin (m + 1) → E) (w : List (Fin m × Bool)) :
    FreeGroup.lift f (FreeGroup.mk (castWord w)) =
      FreeGroup.lift (fun i : Fin m => f i.castSucc) (FreeGroup.mk w) := by
  simp [castWord, FreeGroup.lift_mk, List.map_map, Function.comp_def]

end Lift

section Main

variable {G : Type*} [Group G] [Finite G] {m k : ℕ}

theorem surjective_of_gens {A B : Type*} [Group A] [Group B] (φ : A →* B) {n : ℕ} (g : Fin n → B)
    (hg : Subgroup.closure (Set.range g) = ⊤) (h : ∀ i, g i ∈ φ.range) :
    Function.Surjective φ := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← hg, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact h i

theorem noPerfectDoubleCover_of_eps_cases (g : Fin m → G)
    (hg : Subgroup.closure (Set.range g) = ⊤) (U : List (List (Fin m × Bool)))
    (T : Fin k → List (Fin m × Bool))
    (hadj : ∀ (E : Type) [Group E] (π : E →* G), Function.Surjective π → Nat.card π.ker = 2 →
      ∃ ĝ : Fin m → E, (∀ i, π (ĝ i) = g i) ∧ ∀ r ∈ U, FreeGroup.lift ĝ (FreeGroup.mk r) = 1)
    (hT : ∀ i, FreeGroup.lift g (FreeGroup.mk (T i)) = 1)
    (h0 : Finite (PG m (U ++ (List.finRange k).map T)) ∧
      Nat.card (PG m (U ++ (List.finRange k).map T)) ≤ Nat.card G)
    (hε : ∀ e : Fin k → Bool, (∃ i, e i = true) →
      Finite (PG (m + 1) (epsRels U T e)) ∧ Nat.card (PG (m + 1) (epsRels U T e)) ≤ Nat.card G) :
    NoPerfectDoubleCover G := by
  classical
  intro E _ π hπ hperf hk
  obtain ⟨ĝ, hĝ, hU⟩ := hadj E π hπ hk
  obtain ⟨z, hzK, hz1, hzall⟩ := exists_ker_elem π hk
  have hzc : z ∈ Subgroup.center E := mem_center_of_mem_ker π hk hzK
  have hz2 : z ^ 2 = 1 := sq_eq_one_of_mem_ker π hk hzK
  have hlift : ∀ w, π (FreeGroup.lift ĝ (FreeGroup.mk w)) =
      FreeGroup.lift g (FreeGroup.mk w) := by
    intro w
    have : π.comp (FreeGroup.lift ĝ) = FreeGroup.lift g := by
      apply FreeGroup.ext_hom
      intro i
      simp [hĝ]
    exact DFunLike.congr_fun this (FreeGroup.mk w)
  have hTK : ∀ i, FreeGroup.lift ĝ (FreeGroup.mk (T i)) ∈ π.ker := fun i => by
    rw [MonoidHom.mem_ker, hlift, hT]
  set e : Fin k → Bool := fun i => decide (FreeGroup.lift ĝ (FreeGroup.mk (T i)) = z) with he
  by_cases hne : ∃ i, e i = true
  · obtain ⟨hfin, hcard⟩ := hε e hne
    set f : Fin (m + 1) → E := Fin.snoc (α := fun _ => E) ĝ z with hf
    have hfc : ∀ i : Fin m, f i.castSucc = ĝ i := fun i => Fin.snoc_castSucc _ _ _
    have hfl : f (Fin.last m) = z := Fin.snoc_last _ _
    have hfun : (fun i : Fin m => f i.castSucc) = ĝ := funext hfc
    have hrel : ∀ r ∈ {r : FreeGroup (Fin (m + 1)) |
        r ∈ (epsRels U T e).map FreeGroup.mk}, FreeGroup.lift f r = 1 := by
      intro r hr
      simp only [Set.mem_ofPred_eq, List.mem_map] at hr
      obtain ⟨w, hw, rfl⟩ := hr
      simp only [epsRels, List.cons_append, List.mem_cons, List.mem_append, List.mem_map,
        List.mem_finRange, true_and] at hw
      rcases hw with rfl | (⟨i, rfl⟩ | ⟨u, hu, rfl⟩) | ⟨i, rfl⟩
      · simp only [FreeGroup.lift_mk, zLetter, hfl, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, Bool.cond_true, mul_one]
        rw [← pow_two, hz2]
      · simp only [FreeGroup.lift_mk, zLetter, hfl, hfc, List.map_cons, List.map_nil,
          List.prod_cons, List.prod_nil, Bool.cond_true, Bool.cond_false, mul_one]
        have hc := Subgroup.mem_center_iff.mp hzc (ĝ i)
        have h' : ĝ i * (z * (ĝ i)⁻¹) = z := by
          rw [← mul_assoc, hc, mul_assoc, mul_inv_cancel, mul_one]
        rw [h', ← pow_two, hz2]
      · rw [lift_mk_castWord, hfun]
        exact hU u hu
      · rw [lift_mk_append]
        rw [lift_mk_castWord, hfun]
        by_cases hei : e i = true
        · have hti : FreeGroup.lift ĝ (FreeGroup.mk (T i)) = z := by
            simpa [he] using hei
          simp only [hei, ite_true, FreeGroup.lift_mk, zLetter, hfl, List.map_cons, List.map_nil,
            List.prod_cons, List.prod_nil, Bool.cond_true, mul_one] at hti ⊢
          rw [hti, ← pow_two, hz2]
        · have hti : FreeGroup.lift ĝ (FreeGroup.mk (T i)) ≠ z := by
            intro h'
            exact hei (decide_eq_true h')
          have hone := (hzall _ (hTK i)).resolve_right hti
          have hnil : (if e i = true then [zLetter m] else []) =
              ([] : List (Fin (m + 1) × Bool)) := by simp [hei]
          rw [hnil, ← FreeGroup.one_eq_mk, map_one, mul_one]
          exact hone
    set ρ := PresentedGroup.toGroup hrel with hρ
    have := hfin
    refine false_of_card_le hcard π hπ hk ρ (surjective_of_gens _ g hg fun i => ?_)
    refine ⟨PresentedGroup.of i.castSucc, ?_⟩
    simp [hρ, PresentedGroup.toGroup.of, hfc, hĝ]
  · have hall : ∀ i, FreeGroup.lift ĝ (FreeGroup.mk (T i)) = 1 := by
      intro i
      have hti : FreeGroup.lift ĝ (FreeGroup.mk (T i)) ≠ z := by
        intro h'
        exact hne ⟨i, decide_eq_true h'⟩
      exact (hzall _ (hTK i)).resolve_right hti
    obtain ⟨hfin, hcard⟩ := h0
    have hrel : ∀ r ∈ {r : FreeGroup (Fin m) |
        r ∈ (U ++ (List.finRange k).map T).map FreeGroup.mk}, FreeGroup.lift ĝ r = 1 := by
      intro r hr
      simp only [Set.mem_ofPred_eq, List.mem_map, List.mem_append, List.mem_finRange,
        true_and] at hr
      obtain ⟨w, hw | ⟨i, rfl⟩, rfl⟩ := hr
      · exact hU w hw
      · exact hall i
    set ρ := PresentedGroup.toGroup hrel with hρ
    have := hfin
    refine false_of_card_le hcard π hπ hk ρ (surjective_of_gens _ g hg fun i => ?_)
    refine ⟨PresentedGroup.of i, ?_⟩
    simp [hρ, PresentedGroup.toGroup.of, hĝ]

end Main

end CFSG.Monster.Schur
