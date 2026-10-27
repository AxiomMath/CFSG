module

public import CFSG.Sporadic.SuzRecog.ModelGroupsChecks
public import CFSG.Certificates.NativeSchreierCard

public section

namespace CFSG.Sporadic.SuzRecog.ModelGroups

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.Sporadic.SuzRecog.ModelGroupsCheck

section Generic

variable {G : Type*} [Group G]

theorem conj_mem_closure {s : Set G} {c : G} (hc : ∀ x ∈ s, c * x * c⁻¹ ∈ closure s) {h : G}
    (hh : h ∈ closure s) : c * h * c⁻¹ ∈ closure s := by
  have hle : closure s ≤ (closure s).comap (MulAut.conj c).toMonoidHom :=
    (closure_le _).2 fun x hx => by simpa [MulAut.conj_apply] using hc x hx
  simpa [MulAut.conj_apply] using hle hh

theorem mem_normalizer_closure_of_conj {s : Set G} {g : G}
    (h1 : ∀ x ∈ s, g * x * g⁻¹ ∈ closure s) (h2 : ∀ x ∈ s, g⁻¹ * x * g ∈ closure s) :
    g ∈ normalizer (closure s : Set G) := by
  rw [mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_closure h1 hh, fun hh => ?_⟩
  have := conj_mem_closure (c := g⁻¹) (fun x hx => by simpa using h2 x hx) hh
  simpa [mul_assoc] using this

theorem eq_of_mem_closure_pair {a b x : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (hx : x ∈ closure {a, b}) : x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have haa : ∀ y, a * (a * y) = y := fun y => by rw [← mul_assoc, ha, one_mul]
  have hba : ∀ y, b * (a * y) = a * (b * y) := fun y => by rw [← mul_assoc, ← hab, mul_assoc]
  have hba' : b * a = a * b := hab.symm
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  induction hx using closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp [mul_assoc, ha, hb, haa, hba, hba']
  | inv x _ hx =>
    rcases hx with rfl | rfl | rfl | rfl <;> simp [hai, hbi, hba']

theorem mul_card_le_of_inv_mul_mem [Finite G] {H K : Subgroup G} (hKH : K ≤ H) {m : ℕ}
    (a : Fin m → G) (ha : ∀ i, a i ∈ H) (hd : ∀ i j, (a i)⁻¹ * a j ∈ K → i = j) :
    m * Nat.card K ≤ Nat.card H := by
  have hK' : Nat.card (K.subgroupOf H) = Nat.card K :=
    Nat.card_congr (subgroupOfEquivOfLe hKH).toEquiv
  have hidx := (K.subgroupOf H).card_mul_index
  let f : Fin m → H ⧸ K.subgroupOf H := fun i => ((⟨a i, ha i⟩ : H) : H ⧸ K.subgroupOf H)
  have hf : Function.Injective f := by
    intro i j hij
    apply hd
    have := QuotientGroup.eq.1 hij
    simpa [mem_subgroupOf] using this
  have hm : m ≤ (K.subgroupOf H).index := by
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin] at this
  calc m * Nat.card K ≤ (K.subgroupOf H).index * Nat.card K := Nat.mul_le_mul_right _ hm
    _ = Nat.card H := by rw [← hK', mul_comm, hidx]

theorem card_le_mul_of_cover [Finite G] {H K : Subgroup G} {m : ℕ} (c : Fin m → G)
    (hc : ∀ h ∈ H, ∃ i, (c i)⁻¹ * h ∈ K) : Nat.card H ≤ m * Nat.card K := by
  choose f hf using fun h : H => hc h h.2
  let F : H → Fin m × K := fun h => (f h, ⟨(c (f h))⁻¹ * h, hf h⟩)
  have hF : Function.Injective F := by
    intro x y hxy
    have h1 : f x = f y := congrArg Prod.fst hxy
    have h2 : (c (f x))⁻¹ * (x : G) = (c (f y))⁻¹ * y := congrArg (fun p => (p.2 : G)) hxy
    rw [h1] at h2
    exact Subtype.ext (mul_left_cancel h2)
  calc Nat.card H ≤ Nat.card (Fin m × K) := Nat.card_le_card_of_injective F hF
    _ = m * Nat.card K := by
      rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin]

theorem card_eq_two_mul [Finite G] {H K : Subgroup G} (hKH : K ≤ H) {a : G} (ha : a ∈ H)
    (hx : ∀ b ∈ H, b ∈ K ↔ a * b ∉ K) : Nat.card H = 2 * Nat.card K := by
  have ha' : a ∉ K := by
    have := (hx 1 (one_mem _)).1 (one_mem _)
    rwa [mul_one] at this
  apply le_antisymm
  · refine card_le_mul_of_cover ![1, a⁻¹] fun h hh => ?_
    by_cases hk : h ∈ K
    · exact ⟨0, by simpa using hk⟩
    · refine ⟨1, ?_⟩
      by_contra hc
      exact hk ((hx h hh).2 (by simpa using hc))
  · refine mul_card_le_of_inv_mul_mem hKH ![1, a⁻¹] (fun i => ?_) (fun i j hij => ?_)
    · fin_cases i
      · exact one_mem _
      · exact inv_mem ha
    · fin_cases i <;> fin_cases j
      · rfl
      · exact absurd (by simpa using hij) ha'
      · exact absurd (by simpa using hij) ha'
      · rfl

theorem mem_zpowers_of_orderOf_eq_three {x y : G} (hx : orderOf x = 3) :
    y ∈ zpowers x ↔ y = 1 ∨ y = x ∨ y = x * x := by
  classical
  have hfin : IsOfFinOrder x := orderOf_pos_iff.1 (by rw [hx]; norm_num)
  rw [hfin.mem_zpowers_iff_mem_range_orderOf, hx, Finset.mem_image]
  constructor
  · rintro ⟨n, hn, rfl⟩
    rw [Finset.mem_range] at hn
    interval_cases n
    · exact Or.inl (pow_zero x)
    · exact Or.inr (Or.inl (pow_one x))
    · exact Or.inr (Or.inr (pow_two x))
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by simp, pow_zero _⟩
    · exact ⟨1, by simp, pow_one _⟩
    · exact ⟨2, by simp, pow_two _⟩

theorem mul_comm_of_conj_eq {c x : G} (h : c * x * c⁻¹ = x) : c * x = x * c := by
  calc c * x = c * x * c⁻¹ * c := by group
    _ = x * c := by rw [h]

theorem conj_eq_of_mul_comm {c x : G} (h : c * x = x * c) : c * x * c⁻¹ = x := by
  rw [h, mul_inv_cancel_right]

end Generic

theorem invCand_eq_foldl (n : ℕ) (t : Array ℕ) :
    invCand n t = (List.range n).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0) := by
  unfold invCand
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
  rfl

theorem rep_invCand {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    Rep n (invCand n t) g⁻¹ := by
  have key : ∀ k ≤ n, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0)).size = n ∧ ∀ i < k, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0))[t[i]!]! = i := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨hs, hi⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set r := (List.range k).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0)
      have htk : t[k]! < n := ht.lt (by omega)
      refine ⟨by rw [Array.size_set!, hs], fun i hik => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hik with hlt | rfl
      · have hne : t[i]! ≠ t[k]! := by
          intro e
          rw [ht.apply (by omega : i < n), ht.apply (by omega : k < n)] at e
          have := g.injective (Fin.ext e)
          simp at this
          omega
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne)]
        exact hi i hlt
      · rw [Array.getElem!_set!_self _ _ _ (by rw [hs]; exact htk)]
  intro x
  obtain ⟨hs, hi⟩ := key n le_rfl
  rw [invCand_eq_foldl]
  have e : t[(g⁻¹ x : Fin n).val]! = x.val := by
    rw [ht.apply (g⁻¹ x).2]
    simp
  rw [← e, hi _ (g⁻¹ x).2]

theorem rep_conjA {g a : Array ℕ} {G A : Equiv.Perm (Fin 1782)} (hg : Rep 1782 g G)
    (ha : Rep 1782 a A) : Rep 1782 (conjA g a) (G * A * G⁻¹) := by
  rw [mul_assoc]
  exact rep_compA hg (rep_compA ha (rep_invCand hg))

theorem commA_iff {g h : Array ℕ} {G H : Equiv.Perm (Fin 1782)} (hg : Rep 1782 g G)
    (hh : Rep 1782 h H) : commA g h = true ↔ G * H = H * G :=
  eqA_iff (rep_compA hg hh) (rep_compA hh hg)

theorem inZ_iff {r x : Array ℕ} {R X : Equiv.Perm (Fin 1782)} (hr : Rep 1782 r R)
    (hx : Rep 1782 x X) : inZ r x = true ↔ X = R ∨ X = R * R := by
  rw [inZ, Bool.or_eq_true, eqA_iff hx hr, eqA_iff hx (rep_compA hr hr)]

theorem rep_of_eqA {t u : Array ℕ} {G : Equiv.Perm (Fin 1782)} (he : eqA 1782 t u = true)
    (hu : Rep 1782 u G) : Rep 1782 t G := fun x => by
  have := allLt_spec he x.2
  rw [beq_iff_eq] at this
  rw [this, hu x]

theorem getElem!_ofFn_arr {m : ℕ} (f : Fin m → Array ℕ) {i : ℕ} (hi : i < m) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

theorem range_five {α : Type*} (a b c d e : α) : Set.range ![a, b, c, d, e] = {a, b, c, d, e} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩]

theorem range_four {α : Type*} (a b c d : α) : Set.range ![a, b, c, d] = {a, b, c, d} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]

theorem range_three {α : Type*} (a b c : α) : Set.range ![a, b, c] = {a, b, c} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]

theorem range_two {α : Type*} (a b : α) : Set.range ![a, b] = {a, b} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩]

theorem card_closure_of_chainOK {S : Array (Array ℕ)} {k : ℕ} {base : List ℕ}
    {W : Array (List ℤ)} {orbits : List ℕ} (hk : k ≤ S.size) (hb : base.Nodup)
    (hlt : ∀ b ∈ base, b < 1782) (h : chainOK S k base W orbits = true)
    (gs : Fin k → Equiv.Perm (Fin 1782)) (hgs : ∀ i : Fin k, Rep 1782 S[(i : ℕ)]! (gs i)) :
    Nat.card (closure (Set.range gs)) = orbits.prod := by
  simp only [chainOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hc, horb⟩ := h
  let bs : List (Fin 1782) := base.pmap (fun b hb => ⟨b, hb⟩) hlt
  have hbs : (bs.map Fin.val).toArray = base.toArray := by
    congr 1
    simp [bs, List.map_pmap]
  have hbn : bs.Nodup := List.Nodup.pmap (fun _ _ _ _ e => congrArg Fin.val e) hb
  rw [← hbs] at hc horb
  have hcard := card_originalSubgroup_of_chainOK
    (chainArrays_ofArrays (n := 1782) (hn := by norm_num) (k := k) (hk := hk) (hb := hbn)
      (W := W) (chainCheckFacts hc).strong_inv) (by norm_num) hc
  rw [horb] at hcard
  rw [← hcard]
  have hrep : ∀ i : Fin k, permOfArr 1782 S[(i : ℕ)]! = gs i := fun i =>
    Rep.unique (rep_permOfArr ((chainCheckFacts hc).strong_inv i (by omega))).1 (hgs i)
  have hsub : closure (Set.range gs) = (RawSchreierDatum.ofArrays 1782 (by norm_num) S k hk bs hbn
      W).originalSubgroup := by
    rw [RawSchreierDatum.originalSubgroup]
    congr 1
    ext g
    simp only [Set.mem_range, Set.mem_ofPred_eq, RawSchreierDatum.mem_ofArrays_original]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.2, hrep i⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, (hrep ⟨i, hi⟩).symm⟩
  rw [hsub]

end CFSG.Sporadic.SuzRecog.ModelGroups
