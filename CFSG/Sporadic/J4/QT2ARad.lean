module

public import CFSG.Sporadic.J4.QT2ACons
public import CFSG.Sporadic.J4.QT2ARadCheck

public section

namespace CFSG.Sporadic.J4.QT2A

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT Matrix

theorem le_relIndex_centralizer_of_conj {G : Type*} [Group G] [Finite G] (K : Subgroup G) (y : G)
    {n : ℕ} (q : Fin n → G) (hq : ∀ i, q i ∈ K)
    (hinj : Function.Injective fun i => q i * y * (q i)⁻¹) :
    n ≤ (Subgroup.centralizer ({y} : Set G)).relIndex K := by
  let H := (Subgroup.centralizer ({y} : Set G)).subgroupOf K
  let f : Fin n → K ⧸ H := fun i => QuotientGroup.mk ⟨q i, hq i⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply hinj
    have h1 : (⟨q i, hq i⟩ : K)⁻¹ * ⟨q j, hq j⟩ ∈ H := QuotientGroup.eq.1 hij
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 := Subgroup.mem_centralizer_iff.1 h1 y rfl
    have h3 : q i * y * (q i)⁻¹ * q j = q j * y := by
      have h4 : y * ((q i)⁻¹ * q j) = (q i)⁻¹ * q j * y := h2
      calc q i * y * (q i)⁻¹ * q j = q i * (y * ((q i)⁻¹ * q j)) := by group
        _ = q i * ((q i)⁻¹ * q j * y) := by rw [h4]
        _ = q j * y := by group
    show q i * y * (q i)⁻¹ = q j * y * (q j)⁻¹
    calc q i * y * (q i)⁻¹ = (q i * y * (q i)⁻¹ * q j) * (q j)⁻¹ := by group
      _ = q j * y * (q j)⁻¹ := by rw [h3]
  have h := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fin] at h
  exact h

theorem card_centralizer_conj {G : Type*} [Group G] (g x : G) :
    Nat.card (Subgroup.centralizer ({g * x * g⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  have h : Subgroup.centralizer ({g * x * g⁻¹} : Set G) =
      (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom := by
    ext z
    rw [Subgroup.mem_map]
    constructor
    · intro hz
      refine ⟨g⁻¹ * z * g, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro x' hx'
        rw [Set.mem_singleton_iff] at hx'
        rw [hx']
        have h1 := Subgroup.mem_centralizer_iff.1 hz (g * x * g⁻¹) rfl
        have h2 : g * x * g⁻¹ * z = z * (g * x * g⁻¹) := h1
        calc x * (g⁻¹ * z * g) = g⁻¹ * (g * x * g⁻¹ * z) * g := by group
          _ = g⁻¹ * (z * (g * x * g⁻¹)) * g := by rw [h2]
          _ = g⁻¹ * z * g * x := by group
      · have e : (MulAut.conj g).toMonoidHom (g⁻¹ * z * g) = g * (g⁻¹ * z * g) * g⁻¹ := rfl
        rw [e]
        group
    · rintro ⟨w, hw, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro x' hx'
      rw [Set.mem_singleton_iff] at hx'
      rw [hx']
      have h1 := Subgroup.mem_centralizer_iff.1 hw x rfl
      have h2 : x * w = w * x := h1
      have e : (MulAut.conj g).toMonoidHom w = g * w * g⁻¹ := rfl
      rw [e]
      calc g * x * g⁻¹ * (g * w * g⁻¹) = g * (x * w) * g⁻¹ := by group
        _ = g * (w * x) * g⁻¹ := by rw [h2]
        _ = g * w * g⁻¹ * (g * x * g⁻¹) := by group
  rw [h]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem el5_nil : el5 [] = 1 := by simp [el5, wordProd]

theorem el5_append (w w' : List ℤ) : el5 (w ++ w') = el5 w * el5 w' := wordProd_append gen5 w w'

theorem el5_flatMap_mem {Q : Subgroup J} (l : List ℕ) (f : ℕ → List ℤ)
    (h : ∀ i ∈ l, el5 (f i) ∈ Q) : el5 (l.flatMap f) ∈ Q := by
  induction l with
  | nil => simp [el5_nil]
  | cons i l ih =>
    rw [List.flatMap_cons, el5_append]
    exact Q.mul_mem (h i (List.mem_cons_self ..))
      (ih fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem getD_lt_twelve {sub : List ℕ} (hsub : ∀ k ∈ sub, k < 12) (i : ℕ) : sub.getD i 0 < 12 := by
  by_cases hi : i < sub.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hsub _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    norm_num

theorem el5_qWordG_mem_Qz (hM : MatFacts) {sub : List ℕ} (hsub : ∀ k ∈ sub, k < 12) (t : ℕ) :
    el5 (qWordG sub t) ∈ Qz := by
  unfold qWordG
  refine el5_flatMap_mem _ _ fun i _ => ?_
  by_cases hb : t.testBit i
  · rw [ite_eq_left hb]
    exact qJ_mem_Qz hM (getD_lt_twelve hsub i)
  · rw [ite_eq_right hb, el5_nil]
    exact Qz.one_mem

theorem qGenW_getD_ne (k : ℕ) : ∀ l ∈ qGenW.getD k [], l ≠ 0 := by
  have h := chkQlet_true
  unfold chkQlet at h
  rw [List.all_eq_true] at h
  intro l hl
  by_cases hk : k < qGenW.length
  · rw [List.getD_eq_getElem _ _ hk] at hl
    have := List.all_eq_true.1 (h _ (List.getElem_mem hk)) l hl
    simpa using this
  · rw [List.getD_eq_default _ _ (by omega)] at hl
    simp at hl

theorem qWordG_ne (sub : List ℕ) (t : ℕ) : ∀ l ∈ qWordG sub t, l ≠ 0 := by
  intro l hl
  unfold qWordG at hl
  rw [List.mem_flatMap] at hl
  obtain ⟨i, -, hi⟩ := hl
  by_cases hb : t.testBit i
  · rw [ite_eq_left hb] at hi
    exact qGenW_getD_ne _ l hi
  · rw [ite_eq_right hb] at hi
    simp at hi

theorem Mx_conj_qWordG
    (hM : MatFacts) (sub : List ℕ) (t : ℕ) {g : J} {X : Array V2}
    (hg : Mx g = rowsMatrix X) :
    Mx (el5 (qWordG sub t) * g * (el5 (qWordG sub t))⁻¹) =
      rowsMatrix (mulRows (mulRows (wR (qWordG sub t)) X) (wR (invW (qWordG sub t)))) := by
  have hinv : (el5 (qWordG sub t))⁻¹ = el5 (invW (qWordG sub t)) := by
    rw [invW_eq]
    unfold el5
    exact (wordProd_invWord gen5 _ (qWordG_ne sub t)).symm
  rw [hinv, map_mul, map_mul, Mx_el5 hM, hg, Mx_el5 hM, rowsMatrix_mulRows, rowsMatrix_mulRows]

theorem conj_injective
    (hM : MatFacts) {sub : List ℕ} {g : J} {X : Array V2}
    (hg : Mx g = rowsMatrix X) (hd : conjDistinct (qWordG sub) X = true) :
    Function.Injective fun t : Fin 64 => el5 (qWordG sub t) * g * (el5 (qWordG sub t))⁻¹ := by
  intro i j hij
  by_contra hne
  have hne' : (i : ℕ) ≠ j := fun h => hne (Fin.ext h)
  unfold conjDistinct at hd
  simp only [Bool.and_eq_true] at hd
  obtain ⟨hw, hdist⟩ := hd
  have h1 := allDistinct_spec hdist i j (by simp) (by simp) hne'
  have hwi := List.all_eq_true.1 hw _ (List.getElem_mem (by simp : (i : ℕ) < _))
  have hwj := List.all_eq_true.1 hw _ (List.getElem_mem (by simp : (j : ℕ) < _))
  simp only [List.getElem_map, List.getElem_zip, List.getElem_range] at h1 hwi hwj
  apply ne_of_eqRows_false hwi hwj h1
  rw [← Mx_conj_qWordG hM sub i hg, ← Mx_conj_qWordG hM sub j hg]
  exact congrArg Mx hij

theorem zJ_mem_Qz : zJ ∈ Qz := by
  refine mem_Qz.2 ⟨mem_Cz.2 rfl, fun v hv => ?_⟩
  have h : v ᵥ* phiM = 0 := mem_Kz.1 hv
  have h' : v ᵥ* (Mx zJ - 1) = 0 := h
  rw [h']
  exact Wz.zero_mem

theorem exists_normal_two_group_selfcentralizing_ge
    (hM : MatFacts)
    (hC : Nat.card Cz = 21799895040) :
    ∃ N : Subgroup J, Qz ≤ N ∧ N ≤ Cz ∧ (∀ c ∈ Cz, ∀ n ∈ N, c * n * c⁻¹ ∈ N) ∧ IsPGroup 2 N ∧
      ∀ q ∈ Cz, (∀ n ∈ N, q * n = n * q) → q ∈ N := by
  refine ⟨Qz ⊔ CQ, le_sup_left, sup_le Qz_le_Cz CQ_le_Cz, ?_, ?_, ?_⟩
  · intro c hc n hn
    exact conj_mem_sup Qz CQ c (fun a ha => Subgroup.mem_sup_left (Qz_conj hc ha))
      (fun b hb => Subgroup.mem_sup_right (CQ_conj hc hb)) n hn
  · exact IsPGroup.to_sup_of_normal_left' (isPGroup_Qz hM hC) (isPGroup_CQ hM hC)
      (CQ_le_Cz.trans Cz_le_normalizer_Qz)
  · intro q hq h
    have : q ∈ CQ := ⟨hq, Subgroup.mem_centralizer_iff.2 fun n hn =>
      (h n (Subgroup.mem_sup_left hn)).symm⟩
    exact Subgroup.mem_sup_right this

theorem lt_relIndex_centralizer_y5J
    (hM : MatFacts) :
    16 < (Subgroup.centralizer ({y5J} : Set J)).relIndex Qz := by
  have h := le_relIndex_centralizer_of_conj Qz y5J (n := 64) (fun t => el5 (qWordG qSub5 t))
    (fun t => el5_qWordG_mem_Qz hM (by decide) t)
    (conj_injective hM (Mx_y5J hM) chkQconj5_true)
  omega

theorem conjDistinct_yEl {n : ℕ} (hn : n < 27) (hn0 : n ≠ 0) :
    conjDistinct (qWordG qSub) (yEl n) = true := by
  have h := chkQconj_true
  unfold chkQconj at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq] at h
  rcases h.2 n hn with h0 | h1
  · exact absurd h0 hn0
  · unfold conjDistinct
    simp only [Bool.and_eq_true, List.all_eq_true]
    exact h1

end CFSG.Sporadic.J4.QT2A
