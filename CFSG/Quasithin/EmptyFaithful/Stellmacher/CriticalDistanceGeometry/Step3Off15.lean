module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModM10

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.F53Mod Equiv

namespace F53.Stellmacher

private def a5a : Perm (Fin 5) := swap 2 3 * swap 3 4

private def a5b : Perm (Fin 5) := swap 0 1 * swap 1 2

private def evalW (L : List (Perm (Fin 5))) (w : List ℕ) : Perm (Fin 5) := (w.map (fun i => L.getD i 1)).prod

private theorem evalW_mem {H : Subgroup (Perm (Fin 5))} {L : List (Perm (Fin 5))} (hL : ∀ x ∈ L, x ∈ H)
    (w : List ℕ) : evalW L w ∈ H := by
  unfold evalW
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  by_cases hi : i < L.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hL _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (not_lt.mp hi)]
    exact H.one_mem

private def a5Words : List (List ℕ) :=
  [[],
   [0],
   [2],
   [0, 3, 2, 1, 0],
   [0, 3, 2, 1],
   [2, 3, 0, 1],
   [3, 0, 1, 2],
   [3, 0, 1],
   [2, 3, 2, 1],
   [3, 2, 1, 0],
   [3, 2, 1],
   [0, 3, 0, 1],
   [0, 1, 2, 3, 0, 1],
   [1, 0, 3, 2, 1],
   [1, 2, 3, 0, 1],
   [1],
   [1, 0],
   [1, 2],
   [0, 1],
   [0, 1, 2],
   [0, 1, 0],
   [2, 1],
   [2, 1, 0],
   [2, 1, 2],
   [3],
   [3, 0],
   [3, 2],
   [0, 1, 2, 3, 0],
   [0, 1, 2, 3],
   [2, 1, 0, 3],
   [0, 3, 2, 3],
   [1, 0, 1],
   [1, 0, 1, 0],
   [1, 2, 1, 0],
   [1, 2, 1],
   [1, 2, 1, 2],
   [0, 3],
   [0, 3, 2],
   [0, 3, 0],
   [1, 0, 3, 2],
   [1, 0, 3],
   [1, 0, 3, 0],
   [3, 0, 3],
   [0, 1, 2, 1],
   [3, 0, 3, 0],
   [2, 3, 2, 3],
   [0, 1, 0, 1],
   [0, 1, 0, 1, 0],
   [2, 3],
   [2, 3, 0],
   [2, 3, 2],
   [1, 2, 3, 0],
   [1, 2, 3],
   [0, 1, 0, 3],
   [3, 2, 3],
   [2, 1, 0, 1],
   [3, 2, 3, 2],
   [0, 3, 0, 3],
   [2, 1, 2, 1],
   [0, 3, 0, 3, 0]]

set_option maxRecDepth 100000 in
private theorem a5_words : ∀ x : Perm (Fin 5), Perm.sign x = 1 →
    ∃ w ∈ a5Words, evalW [a5a, a5b, a5a⁻¹, a5b⁻¹] w = x := by
  unfold a5Words evalW a5a a5b
  decide +kernel

private theorem alt5_le_of_ab {H : Subgroup (Perm (Fin 5))} (ha : a5a ∈ H) (hb : a5b ∈ H) :
    alternatingGroup (Fin 5) ≤ H := by
  intro x hx
  obtain ⟨w, -, rfl⟩ := a5_words x (Perm.mem_alternatingGroup.mp hx)
  refine evalW_mem ?_ w
  intro y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact H.inv_mem ha
  · exact H.inv_mem hb

private def letters (bs : List (Perm (Fin 5))) (g : Perm (Fin 5)) : List (Perm (Fin 5)) :=
  bs ++ bs.map (fun x => g * x * g⁻¹)

private theorem p13_core {B : Subgroup (Perm (Fin 5))} {bs : List (Perm (Fin 5))}
    {cert : List (Perm (Fin 5) × List ℕ × List ℕ)}
    (hbs : ∀ x ∈ bs, x ∈ B) (hne : ∀ x ∈ bs, x ≠ 1)
    (hnorm : ∀ s ∈ S5SylF, ∀ x ∈ bs, s⁻¹ * x * s ∈ B)
    (hcert : ∀ e ∈ cert, evalW (letters bs e.1) e.2.1 = a5a ∧ evalW (letters bs e.1) e.2.2 = a5b)
    (hcov : ∀ g : Perm (Fin 5), (∀ x ∈ bs, g⁻¹ * x * g ∉ S5SylF) →
      ∃ e ∈ cert, ∃ s ∈ S5SylF, g = e.1 * s)
    {g : Perm (Fin 5)} (hg : B ⊓ S5Syl.map (MulAut.conj g).toMonoidHom = ⊥) :
    alternatingGroup (Fin 5) ≤ B ⊔ B.map (MulAut.conj g).toMonoidHom := by
  have hreg : ∀ x ∈ bs, g⁻¹ * x * g ∉ S5SylF := by
    intro x hx hS
    have h1 : x ∈ B ⊓ S5Syl.map (MulAut.conj g).toMonoidHom :=
      ⟨hbs x hx, g⁻¹ * x * g, (mem_S5Syl_iff _).mpr hS, by
        show g * (g⁻¹ * x * g) * g⁻¹ = x
        group⟩
    rw [hg, Subgroup.mem_bot] at h1
    exact hne x hx h1
  obtain ⟨⟨r, wa, wb⟩, he, s, hs, rfl⟩ := hcov g hreg
  obtain ⟨ha, hb⟩ := hcert _ he
  have hL : ∀ x ∈ letters bs r, x ∈ B ⊔ B.map (MulAut.conj (r * s)).toMonoidHom := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact Subgroup.mem_sup_left (hbs x hx)
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      refine Subgroup.mem_sup_right ⟨s⁻¹ * y * s, hnorm s hs y hy, ?_⟩
      show r * s * (s⁻¹ * y * s) * (r * s)⁻¹ = r * y * r⁻¹
      group
  exact alt5_le_of_ab (ha ▸ evalW_mem hL wa) (hb ▸ evalW_mem hL wb)

private def thatList : List (Perm (Fin 5)) := [swap 0 2, swap 1 3, swap 0 2 * swap 1 3]

private def tList : List (Perm (Fin 5)) := [swap 0 1 * swap 2 3, swap 0 3 * swap 1 2, swap 0 2 * swap 1 3]

private def thatCert : List (Perm (Fin 5) × List ℕ × List ℕ) :=
  [(swap (2 : Fin 5) 3 * swap 3 4, [0, 5, 2, 4], [2, 3, 1]),
   (swap (2 : Fin 5) 4 * swap 3 4, [3, 2, 5, 1], [4, 0]),
   (swap (1 : Fin 5) 2 * swap 3 4, [4, 2, 3, 2], [0, 3]),
   (swap (1 : Fin 5) 2 * swap 2 3 * swap 3 4, [5, 0, 3], [2, 3, 1]),
   (swap (1 : Fin 5) 2 * swap 2 4, [3, 0, 5], [1, 4, 2]),
   (swap (1 : Fin 5) 3 * swap 2 3 * swap 3 4, [2, 3, 2, 4], [0, 3]),
   (swap (0 : Fin 5) 1 * swap 1 2 * swap 2 4, [5, 1, 3], [1, 4, 2]),
   (swap (0 : Fin 5) 1 * swap 1 3 * swap 3 4, [3, 1, 5], [3, 0])]

private def tCert : List (Perm (Fin 5) × List ℕ × List ℕ) :=
  [(swap (3 : Fin 5) 4, [3, 0], [0, 5, 1, 3]),
   (swap (2 : Fin 5) 3 * swap 3 4, [0, 3], [5, 0, 4]),
   (swap (2 : Fin 5) 4 * swap 3 4, [3, 0], [0, 4, 1, 3]),
   (swap (2 : Fin 5) 4, [0, 3], [4, 0, 5]),
   (swap (1 : Fin 5) 2 * swap 3 4, [5, 0], [0, 3, 1, 5]),
   (swap (1 : Fin 5) 2 * swap 2 3 * swap 3 4, [2, 4, 1], [4, 2, 5]),
   (swap (1 : Fin 5) 2 * swap 2 4, [2, 5, 1], [5, 2, 4]),
   (swap (1 : Fin 5) 3 * swap 2 3 * swap 3 4, [0, 5], [3, 0, 4]),
   (swap (1 : Fin 5) 3 * swap 3 4, [2, 4, 1], [4, 2, 3]),
   (swap (0 : Fin 5) 1 * swap 1 2 * swap 2 3 * swap 3 4, [1, 4, 2], [5, 1, 4]),
   (swap (0 : Fin 5) 1 * swap 1 2 * swap 2 4, [1, 5, 2], [4, 1, 5]),
   (swap (0 : Fin 5) 1 * swap 1 3 * swap 3 4, [1, 4, 2], [3, 1, 4])]

set_option maxRecDepth 100000 in
private theorem thatCert_ok : ∀ e ∈ thatCert, evalW (letters thatList e.1) e.2.1 = a5a ∧
    evalW (letters thatList e.1) e.2.2 = a5b := by
  unfold thatCert thatList letters evalW a5a a5b
  decide +kernel

set_option maxRecDepth 100000 in
private theorem thatCov : ∀ g : Perm (Fin 5), (∀ x ∈ thatList, g⁻¹ * x * g ∉ S5SylF) →
    ∃ e ∈ thatCert, ∃ s ∈ S5SylF, g = e.1 * s := by
  unfold thatCert thatList
  rw [S5SylF]
  decide +kernel

set_option maxRecDepth 100000 in
private theorem tCert_ok : ∀ e ∈ tCert, evalW (letters tList e.1) e.2.1 = a5a ∧
    evalW (letters tList e.1) e.2.2 = a5b := by
  unfold tCert tList letters evalW a5a a5b
  decide +kernel

set_option maxRecDepth 100000 in
private theorem tCov : ∀ g : Perm (Fin 5), (∀ x ∈ tList, g⁻¹ * x * g ∉ S5SylF) →
    ∃ e ∈ tCert, ∃ s ∈ S5SylF, g = e.1 * s := by
  unfold tCert tList
  rw [S5SylF]
  decide +kernel

set_option maxRecDepth 100000 in
private theorem that_facts : (∀ x ∈ thatList, x ∈ S5That) ∧ (∀ x ∈ thatList, x ≠ 1) ∧
    ∀ s ∈ S5SylF, ∀ x ∈ thatList, s⁻¹ * x * s ∈ S5That := by
  simp only [mem_S5That_iff]
  unfold thatList
  rw [S5SylF, S5ThatF]
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

set_option maxRecDepth 100000 in
private theorem t_facts : (∀ x ∈ tList, x ∈ S5T) ∧ (∀ x ∈ tList, x ≠ 1) ∧
    ∀ s ∈ S5SylF, ∀ x ∈ tList, s⁻¹ * x * s ∈ S5T := by
  simp only [mem_S5T_iff]
  unfold tList
  rw [S5SylF, S5TF]
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem p13_that {g : Perm (Fin 5)} (hg : S5That ⊓ S5Syl.map (MulAut.conj g).toMonoidHom = ⊥) :
    S5That ⊔ S5That.map (MulAut.conj g).toMonoidHom = ⊤ := by
  obtain ⟨h1, h2, h3⟩ := that_facts
  have hA := p13_core h1 h2 h3 thatCert_ok thatCov hg
  have ht : swap (0 : Fin 5) 2 ∈ S5That ⊔ S5That.map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  rw [eq_top_iff]
  intro σ _
  by_cases hs : Perm.sign σ = 1
  · exact hA (Perm.mem_alternatingGroup.mpr hs)
  · have hs' : Perm.sign (σ * swap 0 2) = 1 := by
      rw [map_mul, Perm.sign_swap (by decide)]
      rcases Int.units_eq_one_or (Perm.sign σ) with h | h
      · exact absurd h hs
      · rw [h]; decide
    have := Subgroup.mul_mem _ (hA (Perm.mem_alternatingGroup.mpr hs')) ht
    simpa [mul_assoc] using this

theorem p13_T {g : Perm (Fin 5)} (hg : S5T ⊓ S5Syl.map (MulAut.conj g).toMonoidHom = ⊥) :
    S5T ⊔ S5T.map (MulAut.conj g).toMonoidHom = alternatingGroup (Fin 5) := by
  obtain ⟨h1, h2, h3⟩ := t_facts
  refine le_antisymm (sup_le inf_le_right ?_) (p13_core h1 h2 h3 tCert_ok tCov hg)
  rintro _ ⟨x, hx, rfl⟩
  exact (alternatingGroup.normal (α := Fin 5)).conj_mem x (Subgroup.mem_inf.mp hx).2 g

private theorem map_conj_map_conj (g h : Perm (Fin 5)) (X : Subgroup (Perm (Fin 5))) :
    (X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      X.map (MulAut.conj (h * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

private theorem map_conj_inv_map_conj (g : Perm (Fin 5)) (X : Subgroup (Perm (Fin 5))) :
    (X.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = X := by
  rw [map_conj_map_conj, mul_inv_cancel]
  ext x
  simp

private theorem map_conj_bot_iff (g : Perm (Fin 5)) (X : Subgroup (Perm (Fin 5))) :
    X.map (MulAut.conj g).toMonoidHom = ⊥ ↔ X = ⊥ :=
  Subgroup.map_eq_bot_iff_of_injective X (MulAut.conj g).injective

private theorem S5T_le_alt : S5T ≤ alternatingGroup (Fin 5) := inf_le_right

private theorem swap02_mem_S5That : swap (0 : Fin 5) 2 ∈ S5That := Subgroup.subset_closure (by simp)

private theorem sign_swap02 : Perm.sign (swap (0 : Fin 5) 2) ≠ 1 := by
  rw [Perm.sign_swap (by decide)]; decide

theorem klein_cases {D B : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) (hBD : B ≤ D)
    (hexp : ∀ x ∈ B, x * x = 1) (hcard : Nat.card B = 4) :
    ∃ g : Perm (Fin 5), D = S5Syl.map (MulAut.conj g).toMonoidHom ∧
      ((B = S5T.map (MulAut.conj g).toMonoidHom ∧ B ≤ alternatingGroup (Fin 5)) ∨
        (B = S5That.map (MulAut.conj g).toMonoidHom ∧ ¬ B ≤ alternatingGroup (Fin 5))) := by
  obtain ⟨g, hg⟩ := exists_conj_S5Syl hD
  refine ⟨g, hg, ?_⟩
  set B' := B.map (MulAut.conj g⁻¹).toMonoidHom with hB'
  have hBB' : B = B'.map (MulAut.conj g).toMonoidHom := (map_conj_inv_map_conj g B).symm
  have hle : B' ≤ S5Syl := by
    rintro _ ⟨b, hb, rfl⟩
    have h1 := hBD hb
    rw [hg, mem_map_conj] at h1
    simpa [MulAut.conj_apply] using h1
  have hcard' : Nat.card B' = 4 := by
    rw [hB', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hcard]
  have hexp' : ∀ x ∈ B', x * x = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    have := hexp b hb
    show (g⁻¹ * b * g⁻¹⁻¹) * (g⁻¹ * b * g⁻¹⁻¹) = 1
    calc (g⁻¹ * b * g⁻¹⁻¹) * (g⁻¹ * b * g⁻¹⁻¹) = g⁻¹ * (b * b) * g⁻¹⁻¹ := by group
      _ = 1 := by rw [this]; group
  have hne : B' ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard'
    omega
  rcases le_syl_cases hle hexp' hne with ⟨t, -, -, -, h2⟩ | hT | hThat
  · omega
  · left
    refine ⟨by rw [hBB', hT], ?_⟩
    rw [hBB', hT]
    rintro _ ⟨x, hx, rfl⟩
    exact (alternatingGroup.normal (α := Fin 5)).conj_mem x (S5T_le_alt hx) g
  · right
    refine ⟨by rw [hBB', hThat], ?_⟩
    rw [hBB', hThat]
    intro hA
    have h1 := hA ⟨swap 0 2, swap02_mem_S5That, rfl⟩
    rw [Perm.mem_alternatingGroup, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      MulAut.conj_apply, map_mul, map_mul, map_inv] at h1
    apply sign_swap02
    rw [← h1]
    generalize Perm.sign g = a
    generalize Perm.sign (swap (0 : Fin 5) 2) = b
    revert a b; decide

theorem p13 {D B : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) (hBD : B ≤ D)
    (hexp : ∀ x ∈ B, x * x = 1) (hcard : Nat.card B = 4) {h : Perm (Fin 5)}
    (hreg : B ⊓ D.map (MulAut.conj h).toMonoidHom = ⊥) :
    (B ≤ alternatingGroup (Fin 5) → B ⊔ B.map (MulAut.conj h).toMonoidHom =
        alternatingGroup (Fin 5)) ∧
      (¬ B ≤ alternatingGroup (Fin 5) → B ⊔ B.map (MulAut.conj h).toMonoidHom = ⊤) := by
  obtain ⟨g, hg, hcases⟩ := klein_cases hD hBD hexp hcard
  set h' := g⁻¹ * h * g with hh'
  have hhg : h * g = g * h' := by rw [hh']; group
  have key : ∀ X : Subgroup (Perm (Fin 5)), B = X.map (MulAut.conj g).toMonoidHom →
      X ⊓ S5Syl.map (MulAut.conj h').toMonoidHom = ⊥ ∧
        B ⊔ B.map (MulAut.conj h).toMonoidHom =
          (X ⊔ X.map (MulAut.conj h').toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    intro X hX
    have hDh : D.map (MulAut.conj h).toMonoidHom =
        (S5Syl.map (MulAut.conj h').toMonoidHom).map (MulAut.conj g).toMonoidHom := by
      rw [hg, map_conj_map_conj, map_conj_map_conj, hhg]
    refine ⟨?_, ?_⟩
    · rw [← map_conj_bot_iff g, Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ← hX, ← hDh]
      exact hreg
    · rw [Subgroup.map_sup, hX, map_conj_map_conj, map_conj_map_conj, hhg]
  rcases hcases with ⟨hX, hA⟩ | ⟨hX, hA⟩
  · obtain ⟨hr, hsup⟩ := key _ hX
    refine ⟨fun _ => ?_, fun h => absurd hA h⟩
    rw [hsup, p13_T hr]
    ext x
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (alternatingGroup.normal (α := Fin 5)).conj_mem y hy g
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, ?_⟩
      · simpa using (alternatingGroup.normal (α := Fin 5)).conj_mem x hx g⁻¹
      · simp [MulAut.conj_apply, mul_assoc]
  · obtain ⟨hr, hsup⟩ := key _ hX
    refine ⟨fun h => absurd h hA, fun _ => ?_⟩
    rw [hsup, p13_that hr, Subgroup.map_top_of_surjective _ (MulEquiv.surjective _)]

theorem off15 (M : Model 5) (hA : fixW M (alternatingGroup (Fin 5)) ≠ ⊤)
    {B : Subgroup (Perm (Fin 5))} (hne : B ≠ ⊥) (hexp : ∀ x ∈ B, x * x = 1)
    (hoff : (fixW M B).index ≤ Nat.card B) :
    ((fixW M B).index = Nat.card B ∧ (fixW M.modA5 B).index = Nat.card B ∧
        (Nat.card B = 2 ∨ Nat.card B = 4)) ∧
      fixW M (alternatingGroup (Fin 5)) ≤ fixW M B ∧
      (∀ x : M.W, M.projA5 x ∈ fixW M.modA5 B → x ∈ fixW M B) ∧
      ((Nonempty (M.modA5.Iso orth) ∧
          ((∃ t : Perm (Fin 5), t.IsSwap ∧ B = Subgroup.zpowers t) ∨
            (Nat.card B = 4 ∧ ¬ B ≤ alternatingGroup (Fin 5)))) ∨
        (Nonempty (M.modA5.Iso nat) ∧ Nat.card B = 4 ∧ B ≤ alternatingGroup (Fin 5))) := by
  have hnt : ∃ w : M.modA5.W, w ≠ 1 := by
    by_contra h
    push Not at h
    apply hA
    rw [eq_top_iff]
    intro w _
    exact (M.projA5_eq_one_iff w).mp (h _)
  have hoff' : (fixW M.modA5 B).index ≤ Nat.card B := by
    rw [M.index_fixW_modA5]
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)
      (Subgroup.index_dvd_of_le (fixW_le_fixQ B _))).trans hoff
  obtain ⟨hidx, hcases⟩ := offender_dichotomy M.modA5 hnt M.fixW_modA5_top hne hexp hoff'
  have hle : (fixW M B).index ≤ (fixW M.modA5 B).index := hidx ▸ hoff
  have hge : (fixW M.modA5 B).index ≤ (fixW M B).index := by
    rw [M.index_fixW_modA5]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)
      (Subgroup.index_dvd_of_le (fixW_le_fixQ B _))
  have hE : ∀ x : M.W, M.projA5 x ∈ fixW M.modA5 B → x ∈ fixW M B :=
    fun x hx => M.mem_fixW_of_index_le hle hx
  have hc24 : Nat.card B = 2 ∨ Nat.card B = 4 := by
    rcases hcases with ⟨-, ⟨t, ht, rfl⟩ | ⟨h4, -⟩⟩ | ⟨-, h4, -⟩
    · left
      rw [Nat.card_zpowers]
      exact ht.orderOf
    · exact Or.inr h4
    · exact Or.inr h4
  refine ⟨⟨le_antisymm (hidx ▸ hle) (hidx ▸ hge), hidx, hc24⟩, ?_, hE, hcases⟩
  intro x hx
  exact hE x (by rw [(M.projA5_eq_one_iff x).mpr hx]; exact Subgroup.one_mem _)

theorem off15_of_faithful (M : Model 5) (hf : M.Faithful)
    {B : Subgroup (Perm (Fin 5))} (hne : B ≠ ⊥) (hexp : ∀ x ∈ B, x * x = 1)
    (hoff : (fixW M B).index ≤ Nat.card B) :
    ((fixW M B).index = Nat.card B ∧ (fixW M.modA5 B).index = Nat.card B ∧
        (Nat.card B = 2 ∨ Nat.card B = 4)) ∧
      fixW M (alternatingGroup (Fin 5)) ≤ fixW M B ∧
      (∀ x : M.W, M.projA5 x ∈ fixW M.modA5 B → x ∈ fixW M B) ∧
      ((Nonempty (M.modA5.Iso orth) ∧
          ((∃ t : Perm (Fin 5), t.IsSwap ∧ B = Subgroup.zpowers t) ∨
            (Nat.card B = 4 ∧ ¬ B ≤ alternatingGroup (Fin 5)))) ∨
        (Nonempty (M.modA5.Iso nat) ∧ Nat.card B = 4 ∧ B ≤ alternatingGroup (Fin 5))) :=
  off15 M (fixW_alt5_ne_top_of_faithful hf) hne hexp hoff

theorem isInvSub_modA5_fixW {M : Model 5} {B D : Subgroup (Perm (Fin 5))}
    (hE : ∀ x : M.W, M.projA5 x ∈ fixW M.modA5 B → x ∈ fixW M B)
    (hinv : IsInvSub M D (fixW M B)) : IsInvSub M.modA5 D (fixW M.modA5 B) := by
  intro d hd y hy
  obtain ⟨x, rfl⟩ := M.projA5_surjective y
  have hx := hE x hy
  rw [M.projA5_act]
  exact (M.projA5_mem_fixW_iff B _).mpr (fixW_le_fixQ B _ (hinv d hd x hx))

set_option maxRecDepth 100000 in
private theorem orth_swap_not_inv : ∀ s : Perm (Fin 5), (s = swap 0 2 ∨ s = swap 1 3) →
    ∃ u : orth.W, orth.act s u = u ∧ ∃ d ∈ S5SylF, orth.act s (orth.act d u) ≠ orth.act d u := by
  rintro s (rfl | rfl) <;> decide +kernel

theorem orth_fixW_swap_not_inv {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8)
    {t : Perm (Fin 5)} (ht : t.IsSwap) (htD : t ∈ D) :
    ¬ IsInvSub orth D (fixW orth (Subgroup.zpowers t)) := by
  intro hinv
  obtain ⟨g, hg⟩ := exists_conj_S5Syl hD
  have htS : g⁻¹ * t * g ∈ S5Syl := by
    rw [hg, mem_map_conj] at htD
    exact htD
  have hsw : (g⁻¹ * t * g).IsSwap := by
    obtain ⟨x, y, hxy, rfl⟩ := ht
    refine ⟨g⁻¹ x, g⁻¹ y, g.symm.injective.ne hxy, ?_⟩
    rw [Equiv.swap_apply_apply]
    simp [mul_assoc]
  obtain ⟨x, y, hxy, hs⟩ := hsw
  have hs02 : g⁻¹ * t * g = swap 0 2 ∨ g⁻¹ * t * g = swap 1 3 := by
    rw [hs] at htS ⊢
    exact swap_mem_S5Syl x y hxy ((mem_S5Syl_iff _).mp htS)
  obtain ⟨u, hu, d, hd, hdu⟩ := orth_swap_not_inv _ hs02
  have hB : Subgroup.zpowers t = (Subgroup.zpowers (g⁻¹ * t * g)).map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    congr 1
    simp [MulAut.conj_apply, mul_assoc]
  have h1 : orth.act g u ∈ fixW orth (Subgroup.zpowers t) := by
    rw [hB, mem_fixW_map_conj, act_inv_act, mem_fixW_zpowers_iff]
    exact hu
  have hdD : g * d * g⁻¹ ∈ D := by
    rw [hg, mem_map_conj]
    simpa [mul_assoc] using (mem_S5Syl_iff d).mpr hd
  have h2 := hinv _ hdD _ h1
  rw [hB, mem_fixW_map_conj, mem_fixW_zpowers_iff] at h2
  have e : orth.act g⁻¹ (orth.act (g * d * g⁻¹) (orth.act g u)) = orth.act d u := by
    rw [← act_mul_apply, ← act_mul_apply]
    congr 1
    group
  rw [e] at h2
  exact hdu h2

theorem off15_card_four_of_inv (M : Model 5) (hA : fixW M (alternatingGroup (Fin 5)) ≠ ⊤)
    {B D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) (hBD : B ≤ D) (hne : B ≠ ⊥)
    (hexp : ∀ x ∈ B, x * x = 1) (hoff : (fixW M B).index ≤ Nat.card B)
    (hinv : IsInvSub M D (fixW M B)) : Nat.card B = 4 := by
  obtain ⟨⟨-, -, hc24⟩, -, hE, hcases⟩ := off15 M hA hne hexp hoff
  rcases hc24 with h2 | h4
  · exfalso
    rcases hcases with ⟨⟨e⟩, ⟨t, ht, rfl⟩ | ⟨h4, -⟩⟩ | ⟨-, h4, -⟩
    · have hinv' := isInvSub_modA5_fixW hE hinv
      have htD : t ∈ D := hBD (Subgroup.mem_zpowers t)
      apply orth_fixW_swap_not_inv hD ht htD
      intro d hd v hv
      rw [e.fixW_eq] at hv ⊢
      obtain ⟨y, hy, rfl⟩ := hv
      exact ⟨M.modA5.act d y, hinv' d hd y hy, (e.map_act d y)⟩
    · omega
    · omega
  · exact h4

end F53.Stellmacher

end CFSG.Quasithin
