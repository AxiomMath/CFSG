module

public import CFSG.RankThree.S4Free.Stellmacher24Sz
public import CFSG.RankThree.S4Free.StellmacherHosts
public import CFSG.GroupTheory.LocalCores.MinimalNormal

public section

universe u

namespace CFSG.RankThree.S4Free.Stell

open Subgroup CFSG.Blueprint Suzuki

section ElemAbelian

variable {H : Type*} [Group H] [Finite H]

theorem exists_union_mul {A X : Subgroup H} (hA : CFSG.Open.IsElemAbelian 2 A) (hXA : X ≤ A)
    {x : H} (hx : x ∈ A) : ∃ X' : Subgroup H, X' ≤ A ∧ ∀ y, y ∈ X' ↔ y ∈ X ∨ x * y ∈ X := by
  have hxx : x * x = 1 := by rw [← pow_two]; exact hA.2 x hx
  have hc : ∀ y ∈ A, x * y = y * x := fun y hy => isElemAbelian_comm hA hx hy
  refine ⟨{ carrier := {y | y ∈ A ∧ (y ∈ X ∨ x * y ∈ X)}
            mul_mem' := ?_
            one_mem' := ⟨A.one_mem, Or.inl X.one_mem⟩
            inv_mem' := ?_ }, fun y hy => hy.1, fun y => ⟨fun hy => hy.2, fun hy => ⟨?_, hy⟩⟩⟩
  · rintro y z ⟨hyA, hy⟩ ⟨hzA, hz⟩
    refine ⟨A.mul_mem hyA hzA, ?_⟩
    rcases hy with hy | hy <;> rcases hz with hz | hz
    · exact Or.inl (X.mul_mem hy hz)
    · right
      rw [← mul_assoc, hc y hyA, mul_assoc]
      exact X.mul_mem hy hz
    · right
      rw [← mul_assoc]
      exact X.mul_mem hy hz
    · left
      have := X.mul_mem hy hz
      rwa [show x * y * (x * z) = x * x * (y * z) by
        rw [mul_assoc, ← mul_assoc y, ← hc y hyA, mul_assoc, mul_assoc], hxx, one_mul] at this
  · rintro y ⟨hyA, hy⟩
    refine ⟨A.inv_mem hyA, ?_⟩
    rcases hy with hy | hy
    · exact Or.inl (X.inv_mem hy)
    · right
      have := X.inv_mem hy
      rwa [mul_inv_rev, inv_eq_of_mul_eq_one_right hxx, ← hc _ (A.inv_mem hyA)] at this
  · rcases hy with hy | hy
    · exact hXA hy
    · have := A.mul_mem hx (hXA hy)
      rwa [← mul_assoc, hxx, one_mul] at this

theorem exists_compl_of_isElemAbelian {A B : Subgroup H} (hA : CFSG.Open.IsElemAbelian 2 A)
    (hBA : B ≤ A) : ∃ C : Subgroup H, C ≤ A ∧ C ⊓ B = ⊥ ∧ ∀ x ∈ A, ∃ y ∈ C, ∃ z ∈ B, x = y * z := by
  classical
  obtain ⟨C, ⟨hCA, hCB⟩, hmax⟩ := (Set.toFinite {C : Subgroup H | C ≤ A ∧ C ⊓ B = ⊥}).exists_maximal
    ⟨⊥, bot_le, bot_inf_eq _⟩
  refine ⟨C, hCA, hCB, fun x hx => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨C', hC'A, hC'⟩ := exists_union_mul hA hCA hx
  have hxx : x * x = 1 := by rw [← pow_two]; exact hA.2 x hx
  have hC'B : C' ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyC', hyB⟩
    rcases (hC' y).mp hyC' with hy | hy
    · have : y ∈ C ⊓ B := ⟨hy, hyB⟩
      rwa [hCB] at this
    · exfalso
      refine hcon (x * y) hy y⁻¹ (inv_mem hyB) ?_
      rw [mul_inv_cancel_right]
  have hCC' : C ≤ C' := fun y hy => (hC' y).mpr (Or.inl hy)
  have hxC' : x ∈ C' := (hC' x).mpr (Or.inr (by rw [hxx]; exact C.one_mem))
  have hxC : x ∉ C := fun hxC => hcon x hxC 1 B.one_mem (mul_one x).symm
  exact hxC ((hmax ⟨hC'A, hC'B⟩ hCC') hxC')

theorem exists_hyperplane_of_isElemAbelian {A B : Subgroup H} (hA : CFSG.Open.IsElemAbelian 2 A)
    (hBA : B ≤ A) {x : H} (hxA : x ∈ A) (hxB : x ∉ B) :
    ∃ A₁ : Subgroup H, B ≤ A₁ ∧ A₁ ≤ A ∧ x ∉ A₁ ∧ A₁.relIndex A = 2 := by
  classical
  obtain ⟨A₁, ⟨hBA₁, hA₁A, hxA₁⟩, hmax⟩ :=
    (Set.toFinite {X : Subgroup H | B ≤ X ∧ X ≤ A ∧ x ∉ X}).exists_maximal ⟨B, le_rfl, hBA, hxB⟩
  have hxx : x * x = 1 := by rw [← pow_two]; exact hA.2 x hxA
  have hcov : ∀ y ∈ A, y ∈ A₁ ∨ x * y ∈ A₁ := by
    intro y hyA
    by_contra hcon
    push Not at hcon
    obtain ⟨A₁', hA₁'A, hA₁'⟩ := exists_union_mul hA hA₁A hyA
    have hle : A₁ ≤ A₁' := fun z hz => (hA₁' z).mpr (Or.inl hz)
    have hxA₁' : x ∉ A₁' := by
      intro hx'
      rcases (hA₁' x).mp hx' with h1 | h1
      · exact hxA₁ h1
      · apply hcon.2
        rwa [isElemAbelian_comm hA hyA hxA] at h1
    have hyA₁' : y ∈ A₁' := (hA₁' y).mpr (Or.inr (by
      rw [← pow_two, hA.2 y hyA]
      exact A₁.one_mem))
    exact hcon.1 ((hmax ⟨hBA₁.trans hle, hA₁'A, hxA₁'⟩ hle) hyA₁')
  refine ⟨A₁, hBA₁, hA₁A, hxA₁, ?_⟩
  change (A₁.subgroupOf A).index = 2
  rw [index_eq_two_iff]
  refine ⟨⟨x, hxA⟩, fun y => ?_⟩
  simp only [mem_subgroupOf, Subgroup.coe_mul]
  have hcomm : (y : H) * x = x * y := isElemAbelian_comm hA y.2 hxA
  rw [hcomm]
  rcases hcov y y.2 with h1 | h1
  · refine Or.inr ⟨h1, fun h2 => hxA₁ ?_⟩
    have := A₁.mul_mem h2 (A₁.inv_mem h1)
    rwa [mul_inv_cancel_right] at this
  · refine Or.inl ⟨h1, fun h2 => hxA₁ ?_⟩
    have := A₁.mul_mem h1 (A₁.inv_mem h2)
    rwa [mul_inv_cancel_right] at this

end ElemAbelian

structure Comps {H : Type*} [Group H] (N : Subgroup H) (r : ℕ) (E : Fin r → Subgroup H) where
  e : ((i : Fin r) → ↥(E i)) ≃* ↥N
  he : ∀ (i : Fin r) (x : (j : Fin r) → ↥(E j)), (∀ j, j ≠ i → x j = 1) → (e x : H) = x i
  le : ∀ i, E i ≤ N

namespace Comps

variable {H : Type*} [Group H] {N : Subgroup H} {r : ℕ} {E : Fin r → Subgroup H}
  (C : Comps N r E)

@[expose] noncomputable def coord (j : Fin r) : ↥N →* ↥(E j) :=
  (Pi.evalMonoidHom (fun i => ↥(E i)) j).comp C.e.symm.toMonoidHom

theorem coord_apply (j : Fin r) (n : ↥N) : C.coord j n = C.e.symm n j := rfl

theorem e_mulSingle (i : Fin r) (x : ↥(E i)) : (C.e (Pi.mulSingle i x) : H) = x := by
  classical
  rw [C.he i _ fun j hj => Pi.mulSingle_eq_of_ne hj _, Pi.mulSingle_eq_same]

theorem symm_of_mem {i : Fin r} {x : H} (hx : x ∈ E i) :
    C.e.symm ⟨x, C.le i hx⟩ = Pi.mulSingle i ⟨x, hx⟩ := by
  classical
  apply C.e.injective
  rw [MulEquiv.apply_symm_apply]
  exact Subtype.ext (C.e_mulSingle i ⟨x, hx⟩).symm

theorem coord_of_mem {i j : Fin r} {x : H} (hx : x ∈ E i) :
    (C.coord j ⟨x, C.le i hx⟩ : H) = if j = i then x else 1 := by
  classical
  rw [coord_apply, C.symm_of_mem hx]
  by_cases hji : j = i
  · subst hji
    rw [Pi.mulSingle_eq_same, if_pos rfl]
  · rw [Pi.mulSingle_eq_of_ne hji, if_neg hji, OneMemClass.coe_one]

theorem coord_of_mem_self {j : Fin r} {x : H} (hx : x ∈ E j) :
    (C.coord j ⟨x, C.le j hx⟩ : H) = x := by
  rw [C.coord_of_mem hx, if_pos rfl]

theorem coord_of_mem_ne {i j : Fin r} {x : H} (hx : x ∈ E i) (hij : i ≠ j) :
    (C.coord j ⟨x, C.le i hx⟩ : H) = 1 := by
  rw [C.coord_of_mem hx, if_neg (Ne.symm hij)]

theorem ext_coord {n m : ↥N} (h : ∀ j, C.coord j n = C.coord j m) : n = m :=
  C.e.symm.injective (funext h)

theorem hom_ext {G : Type*} [Group G] {f g : ↥N →* G}
    (h : ∀ i (x : H) (hx : x ∈ E i), f ⟨x, C.le i hx⟩ = g ⟨x, C.le i hx⟩) : f = g := by
  classical
  have : f.comp C.e.toMonoidHom = g.comp C.e.toMonoidHom := by
    refine MonoidHom.pi_ext fun i x => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    have hx : (C.e (Pi.mulSingle i x)) = ⟨(x : H), C.le i x.2⟩ := Subtype.ext (C.e_mulSingle i x)
    rw [hx]
    exact h i x x.2
  ext n
  have := congrArg (fun φ => φ (C.e.symm n)) this
  simpa using this

include C in
theorem le_of_forall_le {X : Subgroup H} (hX : ∀ i, E i ≤ X) : N ≤ X := by
  classical
  intro n hn
  have hf := Finset.noncommProd_mulSingle (C.e.symm ⟨n, hn⟩)
  have h1 := Finset.map_noncommProd Finset.univ
    (fun i => Pi.mulSingle i (C.e.symm ⟨n, hn⟩ i))
    (fun i _ j _ _ => Pi.mulSingle_apply_commute (C.e.symm ⟨n, hn⟩) i j)
    (N.subtype.comp C.e.toMonoidHom)
  rw [hf] at h1
  have hmem : (N.subtype.comp C.e.toMonoidHom) (C.e.symm ⟨n, hn⟩) ∈ X := by
    rw [h1]
    exact X.noncommProd_mem _ fun i _ => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, coe_subtype, C.e_mulSingle]
      exact hX i (C.e.symm ⟨n, hn⟩ i).2
  simpa using hmem

theorem conj_eq (n : ↥N) {j : Fin r} {x : H} (hx : x ∈ E j) :
    (n : H) * x * (n : H)⁻¹ = (C.coord j n : H) * x * (C.coord j n : H)⁻¹ := by
  classical
  have h1 : C.e.symm (n * ⟨x, C.le j hx⟩ * n⁻¹) =
      Pi.mulSingle j (C.coord j n * ⟨x, hx⟩ * (C.coord j n)⁻¹) := by
    rw [map_mul, map_mul, map_inv, C.symm_of_mem hx]
    funext k
    by_cases hkj : k = j
    · subst hkj
      simp [coord_apply]
    · simp [Pi.mulSingle_eq_of_ne hkj]
  have h2 := congrArg (fun f => (C.e f : H)) h1
  simp only [MulEquiv.apply_symm_apply, C.e_mulSingle] at h2
  simpa using h2

include C in
theorem exists_eq_of_simple (hZ : ∀ k (z : H), z ∈ E k → (∀ x ∈ E k, z * x = x * z) → z = 1)
    (hsimple : ∀ k, IsSimpleGroup (E k)) (hEn : ∀ k, ∀ n ∈ N, ∀ x ∈ E k, n * x * n⁻¹ ∈ E k)
    {K : Subgroup H} (hKN : K ≤ N) (hKn : ∀ n ∈ N, ∀ y ∈ K, n * y * n⁻¹ ∈ K)
    (hKs : IsSimpleGroup K) : ∃ k, K = E k := by
  by_contra hne
  push Not at hne
  have hKE : ∀ k, K ⊓ E k = ⊥ := by
    intro k
    have hn : ((K ⊓ E k).subgroupOf K).Normal := ⟨fun z hz y => by
      rw [mem_subgroupOf] at hz ⊢
      exact ⟨K.mul_mem (K.mul_mem y.2 hz.1) (K.inv_mem y.2),
        hEn k y (hKN y.2) z hz.2⟩⟩
    rcases hn.eq_bot_or_eq_top with h1 | h1
    · rw [eq_bot_iff]
      intro z hz
      have : (⟨z, hz.1⟩ : K) ∈ (K ⊓ E k).subgroupOf K := hz
      rw [h1, mem_bot] at this
      exact mem_bot.mpr (congrArg Subtype.val this)
    · exfalso
      have hKk : K ≤ E k := fun y hy => by
        have : (⟨y, hy⟩ : K) ∈ (K ⊓ E k).subgroupOf K := by rw [h1]; exact mem_top _
        exact this.2
      have hn' : (K.subgroupOf (E k)).Normal := ⟨fun y hy x => by
        rw [mem_subgroupOf] at hy ⊢
        exact hKn x (C.le k x.2) y hy⟩
      rcases hn'.eq_bot_or_eq_top with h2 | h2
      · obtain ⟨⟨y, hy⟩, hy1⟩ := exists_ne (1 : K)
        apply hy1
        have : (⟨y, hKk hy⟩ : E k) ∈ K.subgroupOf (E k) := hy
        rw [h2, mem_bot] at this
        have h3 : y = 1 := by simpa using congrArg Subtype.val this
        exact Subtype.ext h3
      · refine hne k (le_antisymm hKk fun x hx => ?_)
        have : (⟨x, hx⟩ : E k) ∈ K.subgroupOf (E k) := by rw [h2]; exact mem_top _
        exact this
  obtain ⟨⟨y, hy⟩, hy1⟩ := exists_ne (1 : K)
  apply hy1
  have hyc : ∀ k, (C.coord k ⟨y, hKN hy⟩ : H) = 1 := by
    intro k
    refine hZ k _ (C.coord k ⟨y, hKN hy⟩).2 fun x hx => ?_
    have h1 : y * x * y⁻¹ * x⁻¹ ∈ K ⊓ E k := by
      refine ⟨?_, ?_⟩
      · have := hKn x (C.le k hx) y⁻¹ (K.inv_mem hy)
        rw [show y * x * y⁻¹ * x⁻¹ = y * (x * y⁻¹ * x⁻¹) by group]
        exact K.mul_mem hy this
      · exact E k |>.mul_mem (hEn k y (hKN hy) x hx) ((E k).inv_mem hx)
    rw [hKE k, mem_bot] at h1
    have h2 : y * x * y⁻¹ = x := by
      calc y * x * y⁻¹ = y * x * y⁻¹ * x⁻¹ * x := by group
        _ = x := by rw [h1, one_mul]
    rw [C.conj_eq ⟨y, hKN hy⟩ hx] at h2
    calc (C.coord k ⟨y, hKN hy⟩ : H) * x
        = (C.coord k ⟨y, hKN hy⟩ : H) * x * (C.coord k ⟨y, hKN hy⟩ : H)⁻¹ *
            (C.coord k ⟨y, hKN hy⟩ : H) := by group
      _ = x * (C.coord k ⟨y, hKN hy⟩ : H) := by rw [h2]
  have : (⟨y, hKN hy⟩ : N) = 1 :=
    C.ext_coord fun k => Subtype.ext (by rw [hyc k, map_one, OneMemClass.coe_one])
  have h3 : y = 1 := by simpa using congrArg Subtype.val this
  exact Subtype.ext h3

include C in
theorem eq_of_eq (hsimple : ∀ k, IsSimpleGroup (E k)) {i j : Fin r} (h : E i = E j) : i = j := by
  by_contra hij
  obtain ⟨⟨x, hx⟩, hx1⟩ := exists_ne (1 : E i)
  apply hx1
  have hxj : x ∈ E j := h ▸ hx
  have h1 := C.coord_of_mem_self hx
  have h2 : (C.coord i ⟨x, C.le j hxj⟩ : H) = 1 := C.coord_of_mem_ne hxj (Ne.symm hij)
  exact Subtype.ext (h1.symm.trans h2)

theorem coord_conj [N.Normal] (hsimple : ∀ k, IsSimpleGroup (E k)) (b : H)
    (hσ : ∀ i, ∃ k', (E i).map (MulAut.conj b).toMonoidHom = E k') {j k : Fin r}
    (hjk : (E j).map (MulAut.conj b).toMonoidHom = E k) (n : ↥N) :
    (C.coord k (MulAut.conjNormal b n) : H) = b * (C.coord j n : H) * b⁻¹ := by
  have key := C.hom_ext
    (f := (E k).subtype.comp ((C.coord k).comp (MulAut.conjNormal b).toMonoidHom))
    (g := (MulAut.conj b).toMonoidHom.comp ((E j).subtype.comp (C.coord j))) fun i x hx => by
      obtain ⟨k', hk'⟩ := hσ i
      have hbx : b * x * b⁻¹ ∈ E k' := by rw [← hk']; exact ⟨x, hx, rfl⟩
      have hconj : MulAut.conjNormal b (⟨x, C.le i hx⟩ : N) = ⟨b * x * b⁻¹, C.le k' hbx⟩ :=
        Subtype.ext rfl
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, coe_subtype, hconj,
        MulAut.conj_apply]
      by_cases hij : i = j
      · subst hij
        have hkk : k' = k := C.eq_of_eq hsimple (hk'.symm.trans hjk)
        subst hkk
        rw [C.coord_of_mem_self hbx, C.coord_of_mem_self hx]
      · have hkk : k' ≠ k := fun hkk => hij (C.eq_of_eq hsimple
          ((map_injective (MulAut.conj b).injective) (hk'.trans (hkk ▸ hjk.symm))))
        rw [C.coord_of_mem_ne hbx hkk, C.coord_of_mem_ne hx hij, mul_one, mul_inv_cancel]
  have := congrArg (fun φ => φ n) key
  simpa [MulAut.conj_apply] using this

end Comps

theorem mem_sylow_of_mem_normalizer {X : Type*} [Group X] [Finite X] (P : Sylow 2 X) {g : X}
    (hg : g ∈ normalizer ((P : Subgroup X) : Set X)) {k : ℕ} (hk : g ^ 2 ^ k = 1) :
    g ∈ (P : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hg2 : IsPGroup 2 (zpowers g) := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hm])
  have h1 : g ∈ zpowers g ⊓ normalizer ((P : Subgroup X) : Set X) := ⟨mem_zpowers _, hg⟩
  have h3 := hg2.inf_normalizer_sylow P
  change zpowers _ ⊓ normalizer ((P : Subgroup X) : Set X) = zpowers _ ⊓ (P : Subgroup X) at h3
  rw [h3] at h1
  exact h1.2

section Diag

variable {H : Type*} [Group H] {N : Subgroup H} {r : ℕ} {E : Fin r → Subgroup H}

@[expose] def InOrbit (E : Fin r → Subgroup H) (A₁ : Subgroup H) (i₀ j : Fin r) : Prop :=
  ∃ c ∈ A₁, (E i₀).map (MulAut.conj c).toMonoidHom = E j

theorem conj_mem_of_inOrbit {A₁ : Subgroup H} {i₀ j : Fin r} (h : InOrbit E A₁ i₀ j)
    (x : E i₀) : h.choose * (x : H) * h.choose⁻¹ ∈ E j := by
  have hx : h.choose * (x : H) * h.choose⁻¹ ∈ (E i₀).map (MulAut.conj h.choose).toMonoidHom :=
    ⟨x, x.2, rfl⟩
  rwa [h.choose_spec.2] at hx

open _root_.Classical in
@[expose] noncomputable def diagFun (E : Fin r → Subgroup H) (A₁ : Subgroup H) (i₀ : Fin r)
    (x : E i₀) (j : Fin r) : E j :=
  if h : InOrbit E A₁ i₀ j then ⟨h.choose * x * h.choose⁻¹, conj_mem_of_inOrbit h x⟩ else 1

theorem diagFun_of_mem {A₁ : Subgroup H} {i₀ j : Fin r} (h : InOrbit E A₁ i₀ j) (x : E i₀) :
    (diagFun E A₁ i₀ x j : H) = h.choose * x * h.choose⁻¹ := by
  classical
  unfold diagFun
  rw [dif_pos h]

theorem diagFun_of_not_mem {A₁ : Subgroup H} {i₀ j : Fin r} (h : ¬ InOrbit E A₁ i₀ j)
    (x : E i₀) : diagFun E A₁ i₀ x j = 1 := by
  classical
  unfold diagFun
  rw [dif_neg h]

noncomputable def diag (C : Comps N r E) (A₁ : Subgroup H) (i₀ : Fin r) : E i₀ →* N where
  toFun x := C.e (diagFun E A₁ i₀ x)
  map_one' := by
    rw [← map_one C.e]
    congr 1
    funext j
    by_cases h : InOrbit E A₁ i₀ j
    · exact Subtype.ext (by rw [diagFun_of_mem h]; simp)
    · rw [diagFun_of_not_mem h]
      rfl
  map_mul' x y := by
    rw [← map_mul]
    congr 1
    funext j
    by_cases h : InOrbit E A₁ i₀ j
    · refine Subtype.ext ?_
      simp only [Pi.mul_apply, Subgroup.coe_mul]
      rw [diagFun_of_mem h, diagFun_of_mem h, diagFun_of_mem h, Subgroup.coe_mul]
      group
    · simp only [Pi.mul_apply]
      rw [diagFun_of_not_mem h, diagFun_of_not_mem h, diagFun_of_not_mem h, mul_one]

theorem coord_diag (C : Comps N r E) (A₁ : Subgroup H) (i₀ : Fin r) (x : E i₀) (j : Fin r) :
    C.coord j (diag C A₁ i₀ x) = diagFun E A₁ i₀ x j := by
  change C.e.symm (C.e _) j = _
  rw [MulEquiv.symm_apply_apply]

end Diag

theorem map_mem_normalizer_iff {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) {P : Subgroup X}
    {P' : Subgroup Y} (hφ : ∀ z, φ z ∈ P' ↔ z ∈ P) (w : X) :
    φ w ∈ normalizer (P' : Set Y) ↔ w ∈ normalizer (P : Set X) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h z
    have := h (φ z)
    rw [hφ, show φ w * φ z * (φ w)⁻¹ = φ (w * z * w⁻¹) by simp [map_mul, map_inv], hφ] at this
    exact this
  · intro h z'
    obtain ⟨z, rfl⟩ := φ.surjective z'
    rw [hφ, show φ w * φ z * (φ w)⁻¹ = φ (w * z * w⁻¹) by simp [map_mul, map_inv], hφ]
    exact h z

section Conj

variable {H : Type*} [Group H]

theorem conj_mem_of_map_eq {K : Subgroup H} {b : H}
    (hb : K.map (MulAut.conj b).toMonoidHom = K) {x : H} (hx : x ∈ K) : b * x * b⁻¹ ∈ K := by
  have : b * x * b⁻¹ ∈ K.map (MulAut.conj b).toMonoidHom := ⟨x, hx, rfl⟩
  rwa [hb] at this

theorem map_conj_one' (K : Subgroup H) : K.map (MulAut.conj (1 : H)).toMonoidHom = K := by
  ext x
  simp [MulAut.conj_apply]

theorem map_conj_mul (K : Subgroup H) (b c : H) :
    (K.map (MulAut.conj c).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      K.map (MulAut.conj (b * c)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

end Conj

theorem mem_normalizer_iff_map_conj_eq {H : Type*} [Group H] [Finite H] {E : Subgroup H} {c : H} :
    c ∈ normalizer (E : Set H) ↔ E.map (MulAut.conj c).toMonoidHom = E := by
  constructor
  · intro hc
    have hle : E.map (MulAut.conj c).toMonoidHom ≤ E := by
      rintro _ ⟨x, hx, rfl⟩
      exact (mem_normalizer_iff.mp hc x).mp hx
    exact eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj c).injective])
  · intro hc
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact conj_mem_of_map_eq hc hx
    · intro hx
      have : c * x * c⁻¹ ∈ E.map (MulAut.conj c).toMonoidHom := by rw [hc]; exact hx
      obtain ⟨y, hy, hyx⟩ := this
      have hyx : c * y * c⁻¹ = c * x * c⁻¹ := hyx
      rw [mul_left_inj, mul_right_inj] at hyx
      rw [← hyx]
      exact hy

structure SzConfig {H : Type*} [Group H] (S M A N : Subgroup H) (r : ℕ) (E : Fin r → Subgroup H)
    extends Comps N r E where
  hyp : Hyp24 S M A
  oTwo_eq : oTwo H = ⊥
  core_eq : M.normalCore = ⊥
  normal : N.Normal
  simple : ∀ i, IsSimpleGroup (E i)
  sz : ∀ i, ∃ a : ℕ, 1 ≤ a ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K),
    Nat.card K = 2 ^ (2 * a + 1) ∧ Nonempty (↥(E i) ≃* suzukiGroup a K)
  normal_in : ∀ k, ∀ n ∈ N, ∀ x ∈ E k, n * x * n⁻¹ ∈ E k
  conj : ∀ i j, ∃ g : H, E j = (E i).map (MulAut.conj g).toMonoidHom
  ne_bot : N ≠ ⊥

namespace SzConfig

variable {H : Type*} [Group H] [Finite H] {S M A N : Subgroup H} {r : ℕ}
  {E : Fin r → Subgroup H} (Q : SzConfig S M A N r E)

include Q in
theorem center_eq (k : Fin r) (z : H) (hz : z ∈ E k)
    (hzc : ∀ x ∈ E k, z * x = x * z) : z = 1 := by
  obtain ⟨a, ha, K, _, _, hK, ⟨eK⟩⟩ := Q.sz k
  have := eq_one_of_forall_commute ha hK eK (g := ⟨z, hz⟩) fun x => Subtype.ext (hzc x x.2)
  exact congrArg Subtype.val this

include Q in
theorem exists_map_conj_eq (b : H) (i : Fin r) :
    ∃ k, (E i).map (MulAut.conj b).toMonoidHom = E k := by
  have := Q.normal
  refine Q.toComps.exists_eq_of_simple Q.center_eq Q.simple Q.normal_in ?_ ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact Q.normal.conj_mem x (Q.le i hx) b
  · rintro n hn _ ⟨x, hx, rfl⟩
    refine ⟨b⁻¹ * n * b * x * (b⁻¹ * n * b)⁻¹, Q.normal_in i _ ?_ x hx, ?_⟩
    · have := Q.normal.conj_mem n hn b⁻¹
      rwa [inv_inv] at this
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  · have := Q.simple i
    exact (MulEquiv.isSimpleGroup
      ((E i).equivMapOfInjective _ (MulAut.conj b).injective).symm)

include Q in
theorem not_dvd_relIndex (j : Fin r) : ¬ 2 ∣ S.relIndex (E j) := by
  have := Q.normal
  have hSN : ¬ 2 ∣ (S.subgroupOf N).index := not_dvd_relIndex_of_normal Q.hyp N
  have hEn : ((E j).subgroupOf N).Normal := ⟨fun x hx n => by
    rw [mem_subgroupOf] at hx ⊢
    exact Q.normal_in j n n.2 x hx⟩
  rw [← relIndex_subgroupOf (Q.le j)]
  rw [← relIndex_sup_of_normal]
  exact fun hd => hSN (hd.trans (relIndex_dvd_index_of_le le_sup_left))

noncomputable def sylowE (j : Fin r) : Sylow 2 (E j) :=
  (Q.hyp.isPGroup.comap_subtype : IsPGroup 2 (S.subgroupOf (E j))).toSylow (Q.not_dvd_relIndex j)

theorem coe_sylowE (j : Fin r) : (Q.sylowE j : Subgroup (E j)) = S.subgroupOf (E j) :=
  IsPGroup.toSylow_coe _ _

theorem mem_iff_coord (n : ↥N) : (n : H) ∈ S ↔ ∀ j, (Q.coord j n : H) ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Q.normal
  have hSN : ¬ 2 ∣ (S.subgroupOf N).index := not_dvd_relIndex_of_normal Q.hyp N
  set SN := (Q.hyp.isPGroup.comap_subtype : IsPGroup 2 (S.subgroupOf N)).toSylow hSN with hSNdef
  have hSNc : (SN : Subgroup N) = S.subgroupOf N := IsPGroup.toSylow_coe _ _
  have hfwd : ∀ m : ↥N, (m : H) ∈ S → ∀ j, (Q.coord j m : H) ∈ S := by
    intro m hm j
    have h2 : IsPGroup 2 ((S.subgroupOf N).map (Q.coord j)) :=
      (Q.hyp.isPGroup.comap_subtype).map _
    have hle : (Q.sylowE j : Subgroup (E j)) ≤ (S.subgroupOf N).map (Q.coord j) := by
      intro x hx
      rw [Q.coe_sylowE] at hx
      refine ⟨⟨x, Q.le j x.2⟩, hx, Subtype.ext ?_⟩
      exact Q.coord_of_mem_self x.2
    have heq := (Q.sylowE j).is_maximal' h2 hle
    have : Q.coord j m ∈ (Q.sylowE j : Subgroup (E j)) := by
      rw [← heq]
      exact ⟨m, hm, rfl⟩
    rw [Q.coe_sylowE] at this
    exact this
  refine ⟨fun hn => hfwd n hn, fun hn => ?_⟩
  set Y : Subgroup N := ⨅ j, (S.subgroupOf (E j)).comap (Q.coord j) with hYdef
  have hY : ∀ m : ↥N, m ∈ Y ↔ ∀ j, (Q.coord j m : H) ∈ S := fun m => by
    simp only [hYdef, mem_iInf, mem_comap, mem_subgroupOf]
  obtain ⟨k, hk⟩ := Q.hyp.isPGroup.exists_card_eq
  have hY2 : IsPGroup 2 Y := by
    intro y
    refine ⟨k, Subtype.ext (Q.ext_coord fun j => Subtype.ext ?_)⟩
    have hyj : (Q.coord j y : H) ∈ S := (hY y).mp y.2 j
    have h1 : (⟨(Q.coord j y : H), hyj⟩ : S) ^ Nat.card S = 1 := pow_card_eq_one'
    rw [hk] at h1
    have h2 := congrArg Subtype.val h1
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h2
    simp only [Subgroup.coe_pow, map_pow, map_one, SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact h2
  have hle : (SN : Subgroup N) ≤ Y := by
    rw [hSNc]
    intro m hm
    exact (hY m).mpr (hfwd m hm)
  have heq := SN.is_maximal' hY2 hle
  have : n ∈ (SN : Subgroup N) := by
    rw [← heq]
    exact (hY n).mpr hn
  rw [hSNc] at this
  exact this

theorem sylowE_ne_bot (j : Fin r) :
    (Q.sylowE j : Subgroup (E j)) ≠ ⊥ := by
  obtain ⟨a, ha, K, _, _, hK, ⟨eK⟩⟩ := Q.sz j
  intro h
  have h1 := (card_sylow_and_center ha hK eK (Q.sylowE j)).1
  rw [h, card_bot] at h1
  have : 2 ≤ 2 ^ (2 * a + 1) := Nat.le_self_pow (by omega) 2
  have : 2 ^ 2 ≤ (2 ^ (2 * a + 1)) ^ 2 := Nat.pow_le_pow_left this 2
  omega

include Q in
theorem not_le : ¬ N ≤ M := fun hle => Q.ne_bot (by
  have := Q.normal
  rw [eq_bot_iff, ← Q.core_eq]
  exact normal_le_normalCore.mpr hle)

include Q in
theorem sup_eq_top : M ⊔ N = ⊤ :=
  Q.hyp.isCoatom.2 _ (lt_of_le_of_ne le_sup_left fun heq => Q.not_le (heq ▸ le_sup_right))

include Q in
theorem not_le_factor (j : Fin r) : ¬ E j ≤ M := by
  intro hle
  apply Q.not_le
  refine Q.le_of_forall_le fun k => ?_
  obtain ⟨g, hg⟩ := Q.conj j k
  have hg' : g ∈ ((M ⊔ N : Subgroup H) : Set H) := by rw [Q.sup_eq_top]; exact mem_top g
  have := Q.normal
  rw [mul_normal] at hg'
  obtain ⟨m, hm, n, hn, rfl⟩ := hg'
  rw [hg]
  rintro _ ⟨x, hx, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [show m * n * x * (m * n)⁻¹ = m * (n * x * n⁻¹) * m⁻¹ by group]
  exact M.mul_mem (M.mul_mem hm (hle (Q.normal_in j n hn x hx))) (M.inv_mem hm)

theorem coord_mem_normalizer (n : ↥N) (hn : (n : H) ∈ M)
    (j : Fin r) :
    Q.coord j n ∈ normalizer ((Q.sylowE j : Subgroup (E j)) : Set (E j)) := by
  obtain ⟨a, ha, K, _, _, hK, ⟨eK⟩⟩ := Q.sz j
  set P := (M.subgroupOf N).map (Q.coord j) with hPdef
  have hTP : (Q.sylowE j : Subgroup (E j)) ≤ P := by
    intro x hx
    rw [Q.coe_sylowE] at hx
    exact ⟨⟨x, Q.le j x.2⟩, Q.hyp.le_M hx, Subtype.ext (Q.coord_of_mem_self x.2)⟩
  have hPtop : P ≠ ⊤ := by
    intro htop
    have hn' : (M.subgroupOf (E j)).Normal := ⟨fun z hz x => by
      rw [mem_subgroupOf] at hz ⊢
      have hx : x ∈ P := by rw [htop]; exact mem_top x
      obtain ⟨k, hk, hkx⟩ := hx
      have h1 := Q.conj_eq k z.2
      rw [hkx] at h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← h1]
      exact M.mul_mem (M.mul_mem hk hz) (M.inv_mem hk)⟩
    have := Q.simple j
    rcases hn'.eq_bot_or_eq_top with h1 | h1
    · apply Q.sylowE_ne_bot j
      rw [eq_bot_iff, ← h1]
      intro x hx
      rw [Q.coe_sylowE] at hx
      exact Q.hyp.le_M hx
    · exact Q.not_le_factor j fun x hx => by
        have : (⟨x, hx⟩ : E j) ∈ M.subgroupOf (E j) := by rw [h1]; exact mem_top _
        exact this
  have hle := le_normalizer_of_sylow_le ha hK eK (Q.sylowE j) hTP hPtop
  exact hle ⟨n, hn, rfl⟩

theorem conj_mem_of_coord (n : ↥N)
    (hn : ∀ j, Q.coord j n ∈ normalizer ((Q.sylowE j : Subgroup (E j)) : Set (E j)))
    {q : H} (hq : q ∈ S ⊓ N) : (n : H) * q * (n : H)⁻¹ ∈ S ⊓ N := by
  have := Q.normal
  have hqN : (n : H) * q * (n : H)⁻¹ ∈ N := Q.normal.conj_mem q hq.2 n
  refine ⟨?_, hqN⟩
  have h1 := (Q.mem_iff_coord ⟨q, hq.2⟩).mp hq.1
  have h2 : ((n * ⟨q, hq.2⟩ * n⁻¹ : N) : H) ∈ S := by
    rw [Q.mem_iff_coord]
    intro j
    have h3 : Q.coord j ⟨q, hq.2⟩ ∈ (Q.sylowE j : Subgroup (E j)) := by
      rw [Q.coe_sylowE]
      exact h1 j
    have h4 := (mem_normalizer_iff.mp (hn j) _).mp h3
    rw [Q.coe_sylowE, mem_subgroupOf] at h4
    simpa [map_mul, map_inv] using h4
  simpa using h2

theorem mem_of_coord (n : ↥N)
    (hn : ∀ j, Q.coord j n ∈ normalizer ((Q.sylowE j : Subgroup (E j)) : Set (E j))) :
    (n : H) ∈ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Q.normal
  have hMN : M ≤ normalizer ((S ⊓ N : Subgroup H) : Set H) := by
    have hsub : ∀ m ∈ M, ∀ q ∈ S ⊓ N, m * q * m⁻¹ ∈ S ⊓ N := by
      intro m hm q hq
      have hqN : m * q * m⁻¹ ∈ N := Q.normal.conj_mem q hq.2 m
      refine mem_inf.mpr ⟨?_, hqN⟩
      obtain ⟨k, hk⟩ := (Q.hyp.isPGroup.to_le inf_le_left : IsPGroup 2 ↥(S ⊓ N)) ⟨q, hq⟩
      have hq2 : q ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hmq2 : (⟨m * q * m⁻¹, hqN⟩ : N) ^ 2 ^ k = 1 :=
        Subtype.ext (by simp [conj_pow, hq2])
      change ((⟨m * q * m⁻¹, hqN⟩ : N) : H) ∈ S
      rw [Q.mem_iff_coord]
      intro j
      have h1 := Q.coord_mem_normalizer ⟨m * q * m⁻¹, hqN⟩
        (M.mul_mem (M.mul_mem hm (Q.hyp.le_M hq.1)) (M.inv_mem hm)) j
      have h2 := mem_sylow_of_mem_normalizer (Q.sylowE j) h1
        (k := k) (by rw [← map_pow, hmq2, map_one])
      rw [Q.coe_sylowE] at h2
      exact h2
    intro m hm
    rw [mem_normalizer_iff]
    intro q
    refine ⟨fun hq => hsub m hm q hq, fun hq => ?_⟩
    have := hsub m⁻¹ (M.inv_mem hm) _ hq
    rwa [show m⁻¹ * (m * q * m⁻¹) * m⁻¹⁻¹ = q by group] at this
  have hne : normalizer ((S ⊓ N : Subgroup H) : Set H) ≠ ⊤ := by
    intro htop
    have hn' : (S ⊓ N).Normal := normalizer_eq_top_iff.mp htop
    have hle := le_oTwo (Q.hyp.isPGroup.to_le inf_le_left : IsPGroup 2 ↥(S ⊓ N))
    rw [Q.oTwo_eq] at hle
    obtain ⟨j⟩ : Nonempty (Fin r) := by
      by_contra hr
      rw [not_nonempty_iff] at hr
      exact Q.ne_bot (le_bot_iff.mp (Q.le_of_forall_le fun i => isEmptyElim i))
    apply Q.sylowE_ne_bot j
    rw [eq_bot_iff, Q.coe_sylowE]
    intro x hx
    have : (x : H) ∈ S ⊓ N := ⟨hx, Q.le j x.2⟩
    rw [le_bot_iff.mp hle] at this
    exact mem_bot.mpr (Subtype.ext (mem_bot.mp this))
  have hMeq : M = normalizer ((S ⊓ N : Subgroup H) : Set H) :=
    (Q.hyp.isCoatom.le_iff.mp hMN).resolve_left hne |>.symm
  rw [hMeq, mem_normalizer_iff]
  intro q
  refine ⟨fun hq => Q.conj_mem_of_coord n hn hq, fun hq => ?_⟩
  have hinv : ∀ j, Q.coord j n⁻¹ ∈ normalizer ((Q.sylowE j : Subgroup (E j)) : Set (E j)) :=
    fun j => by rw [map_inv]; exact inv_mem (hn j)
  have := Q.conj_mem_of_coord n⁻¹ hinv hq
  simpa [mul_assoc] using this

theorem coord_conjNormal (b : H) {j k : Fin r}
    (hjk : (E j).map (MulAut.conj b).toMonoidHom = E k) (n : ↥N) :
    haveI := Q.normal
    (Q.coord k (MulAut.conjNormal b n) : H) = b * (Q.coord j n : H) * b⁻¹ :=
  haveI := Q.normal
  Q.toComps.coord_conj Q.simple b (Q.exists_map_conj_eq b) hjk n

include Q in
theorem exists_map_conj_eq_symm (b : H) (k : Fin r) :
    ∃ j, (E j).map (MulAut.conj b).toMonoidHom = E k := by
  obtain ⟨j, hj⟩ := Q.exists_map_conj_eq b⁻¹ k
  refine ⟨j, ?_⟩
  rw [← hj, map_conj_mul, mul_inv_cancel, map_conj_one']

variable (A₁ : Subgroup H) (i₀ : Fin r)

theorem coord_diag_self
    (hstab : ∀ c ∈ A₁, (E i₀).map (MulAut.conj c).toMonoidHom = E i₀ → ∀ y ∈ E i₀, c * y * c⁻¹ = y)
    (x : E i₀) : (Q.coord i₀ (diag Q.toComps A₁ i₀ x) : H) = x := by
  have h : InOrbit E A₁ i₀ i₀ := ⟨1, A₁.one_mem, map_conj_one' _⟩
  rw [coord_diag, diagFun_of_mem h]
  exact hstab _ h.choose_spec.1 h.choose_spec.2 x x.2

theorem conj_diag_of_mem
    (hstab : ∀ c ∈ A₁, (E i₀).map (MulAut.conj c).toMonoidHom = E i₀ → ∀ y ∈ E i₀, c * y * c⁻¹ = y)
    {b : H} (hb : b ∈ A₁) (x : E i₀) :
    haveI := Q.normal
    MulAut.conjNormal b (diag Q.toComps A₁ i₀ x) = diag Q.toComps A₁ i₀ x := by
  haveI := Q.normal
  refine Q.ext_coord fun k => Subtype.ext ?_
  obtain ⟨j, hjk⟩ := Q.exists_map_conj_eq_symm b k
  rw [Q.coord_conjNormal b hjk, coord_diag, coord_diag]
  by_cases hj : InOrbit E A₁ i₀ j
  · have hk : InOrbit E A₁ i₀ k :=
      ⟨b * hj.choose, A₁.mul_mem hb hj.choose_spec.1, by
        rw [← map_conj_mul, hj.choose_spec.2, hjk]⟩
    rw [diagFun_of_mem hj, diagFun_of_mem hk]
    obtain ⟨cj, hcj⟩ : ∃ cj, cj = hj.choose := ⟨_, rfl⟩
    obtain ⟨ck, hck⟩ : ∃ ck, ck = hk.choose := ⟨_, rfl⟩
    have hcjA : cj ∈ A₁ := by rw [hcj]; exact hj.choose_spec.1
    have hcjE : (E i₀).map (MulAut.conj cj).toMonoidHom = E j := by
      rw [hcj]; exact hj.choose_spec.2
    have hckA : ck ∈ A₁ := by rw [hck]; exact hk.choose_spec.1
    have hckE : (E i₀).map (MulAut.conj ck).toMonoidHom = E k := by
      rw [hck]; exact hk.choose_spec.2
    rw [← hcj, ← hck]
    have hdA : ck⁻¹ * (b * cj) ∈ A₁ := A₁.mul_mem (A₁.inv_mem hckA) (A₁.mul_mem hb hcjA)
    have hdE : (E i₀).map (MulAut.conj (ck⁻¹ * (b * cj))).toMonoidHom = E i₀ := by
      rw [← map_conj_mul, ← map_conj_mul, hcjE, hjk, ← hckE, map_conj_mul, inv_mul_cancel,
        map_conj_one']
    have h1 := hstab _ hdA hdE x x.2
    calc b * (cj * (x : H) * cj⁻¹) * b⁻¹
        = ck * ((ck⁻¹ * (b * cj)) * x * (ck⁻¹ * (b * cj))⁻¹) * ck⁻¹ := by group
      _ = ck * x * ck⁻¹ := by rw [h1]
  · have hk : ¬ InOrbit E A₁ i₀ k := by
      rintro ⟨c, hc, hck⟩
      exact hj ⟨b⁻¹ * c, A₁.mul_mem (A₁.inv_mem hb) hc, by
        rw [← map_conj_mul, hck, ← hjk, map_conj_mul, inv_mul_cancel, map_conj_one']⟩
    rw [diagFun_of_not_mem hj, diagFun_of_not_mem hk]
    simp

theorem conj_diag_of_normalizes {b : H}
    (hbE : (E i₀).map (MulAut.conj b).toMonoidHom = E i₀) (hbc : ∀ c ∈ A₁, b * c = c * b)
    (x : E i₀) :
    haveI := Q.normal
    MulAut.conjNormal b (diag Q.toComps A₁ i₀ x) =
      diag Q.toComps A₁ i₀ ⟨b * x * b⁻¹, conj_mem_of_map_eq hbE x.2⟩ := by
  haveI := Q.normal
  refine Q.ext_coord fun k => Subtype.ext ?_
  obtain ⟨j, hjk⟩ := Q.exists_map_conj_eq_symm b k
  rw [Q.coord_conjNormal b hjk, coord_diag, coord_diag]
  have hfix : ∀ c ∈ A₁, ((E i₀).map (MulAut.conj c).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      (E i₀).map (MulAut.conj c).toMonoidHom := by
    intro c hc
    rw [map_conj_mul, hbc c hc, ← map_conj_mul, hbE]
  by_cases hj : InOrbit E A₁ i₀ j
  · obtain ⟨cj, hcj⟩ : ∃ cj, cj = hj.choose := ⟨_, rfl⟩
    have hcjA : cj ∈ A₁ := by rw [hcj]; exact hj.choose_spec.1
    have hcjE : (E i₀).map (MulAut.conj cj).toMonoidHom = E j := by
      rw [hcj]; exact hj.choose_spec.2
    have hkj : k = j := Q.eq_of_eq Q.simple (by rw [← hjk, ← hcjE, hfix cj hcjA])
    subst hkj
    rw [diagFun_of_mem hj, diagFun_of_mem hj, ← hcj]
    simp only
    rw [show b * (cj * (x : H) * cj⁻¹) * b⁻¹ = (b * cj) * x * (b * cj)⁻¹ by group, hbc cj hcjA]
    group
  · have hk : ¬ InOrbit E A₁ i₀ k := by
      rintro ⟨c, hc, hck⟩
      apply hj
      refine ⟨c, hc, ?_⟩
      have h1 : E j = E k := by
        rw [← hck, ← hfix c hc, hck] at hjk
        exact (map_injective (MulAut.conj b).injective) hjk |>.symm ▸ rfl
      rw [hck, h1]
    rw [diagFun_of_not_mem hj, diagFun_of_not_mem hk]
    simp

theorem coord_conj_diag_eq_one {a : H} (haA : a ∈ A) (haA₁ : a ∉ A₁)
    (hA₁A : A₁ ≤ A) (hcomm : ∀ c ∈ A, ∀ d ∈ A, c * d = d * c)
    (hN₀ : ∀ c ∈ A, (E i₀).map (MulAut.conj c).toMonoidHom = E i₀ → c ∈ A₁) (x : E i₀)
    {k : Fin r} (hk : InOrbit E A₁ i₀ k) :
    haveI := Q.normal
    Q.coord k (MulAut.conjNormal a (diag Q.toComps A₁ i₀ x)) = 1 := by
  haveI := Q.normal
  obtain ⟨j, hjk⟩ := Q.exists_map_conj_eq_symm a k
  refine Subtype.ext ?_
  rw [Q.coord_conjNormal a hjk, coord_diag]
  by_cases hj : InOrbit E A₁ i₀ j
  · exfalso
    obtain ⟨cj, hcjA, hcjE⟩ := hj
    obtain ⟨ck, hckA, hckE⟩ := hk
    have hd : (E i₀).map (MulAut.conj (ck⁻¹ * (a * cj))).toMonoidHom = E i₀ := by
      rw [← map_conj_mul, ← map_conj_mul, hcjE, hjk, ← hckE, map_conj_mul, inv_mul_cancel,
        map_conj_one']
    have h1 := hN₀ _ (A.mul_mem (A.inv_mem (hA₁A hckA)) (A.mul_mem haA (hA₁A hcjA))) hd
    apply haA₁
    have h2 := A₁.mul_mem (A₁.mul_mem hckA h1) (A₁.inv_mem hcjA)
    rwa [show ck * (ck⁻¹ * (a * cj)) * cj⁻¹ = a by group] at h2
  · rw [diagFun_of_not_mem hj]
    simp

theorem diag_mem_iff (hA₁S : A₁ ≤ S)
    (hstab : ∀ c ∈ A₁, (E i₀).map (MulAut.conj c).toMonoidHom = E i₀ → ∀ y ∈ E i₀, c * y * c⁻¹ = y)
    (x : E i₀) : ((diag Q.toComps A₁ i₀ x : N) : H) ∈ S ↔ (x : H) ∈ S := by
  rw [Q.mem_iff_coord]
  refine ⟨fun h => by simpa [Q.coord_diag_self A₁ i₀ hstab x] using h i₀, fun h k => ?_⟩
  rw [coord_diag]
  by_cases hk : InOrbit E A₁ i₀ k
  · rw [diagFun_of_mem hk]
    have hc := hA₁S hk.choose_spec.1
    exact S.mul_mem (S.mul_mem hc h) (S.inv_mem hc)
  · rw [diagFun_of_not_mem hk]
    exact S.one_mem

theorem diag_mem_M_iff (hA₁S : A₁ ≤ S)
    (hstab : ∀ c ∈ A₁, (E i₀).map (MulAut.conj c).toMonoidHom = E i₀ → ∀ y ∈ E i₀, c * y * c⁻¹ = y)
    (x : E i₀) : ((diag Q.toComps A₁ i₀ x : N) : H) ∈ M ↔
      x ∈ normalizer ((Q.sylowE i₀ : Subgroup (E i₀)) : Set (E i₀)) := by
  have hcoord : Q.coord i₀ (diag Q.toComps A₁ i₀ x) = x :=
    Subtype.ext (Q.coord_diag_self A₁ i₀ hstab x)
  refine ⟨fun h => hcoord ▸ Q.coord_mem_normalizer _ h i₀, fun h => Q.mem_of_coord _ fun k => ?_⟩
  rw [coord_diag]
  by_cases hk : InOrbit E A₁ i₀ k
  · obtain ⟨c, hcdef⟩ : ∃ c, c = hk.choose := ⟨_, rfl⟩
    have hcS : c ∈ S := by rw [hcdef]; exact hA₁S hk.choose_spec.1
    have hcE : (E i₀).map (MulAut.conj c).toMonoidHom = E k := by
      rw [hcdef]; exact hk.choose_spec.2
    have hmem : c * (x : H) * c⁻¹ ∈ E k := by rw [← hcE]; exact ⟨x, x.2, rfl⟩
    have hdf : diagFun E A₁ i₀ x k = ⟨c * x * c⁻¹, hmem⟩ :=
      Subtype.ext (by rw [diagFun_of_mem hk, ← hcdef])
    rw [hdf, mem_normalizer_iff]
    intro z
    rw [Q.coe_sylowE, mem_subgroupOf, mem_subgroupOf]
    have hz : (z : H) ∈ (E i₀).map (MulAut.conj c).toMonoidHom := by rw [hcE]; exact z.2
    obtain ⟨z', hz', hzz'⟩ := hz
    have hzz' : c * z' * c⁻¹ = z := hzz'
    have hN := (mem_normalizer_iff.mp h ⟨z', hz'⟩)
    rw [Q.coe_sylowE, mem_subgroupOf, mem_subgroupOf] at hN
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hN ⊢
    rw [← hzz']
    constructor
    · intro h1
      have h2 : z' ∈ S := by
        have := S.mul_mem (S.mul_mem (S.inv_mem hcS) h1) hcS
        rwa [show c⁻¹ * (c * z' * c⁻¹) * c = z' by group] at this
      have h3 := hN.mp h2
      have := S.mul_mem (S.mul_mem hcS h3) (S.inv_mem hcS)
      rwa [show c * ((x : H) * z' * (x : H)⁻¹) * c⁻¹ =
        c * x * c⁻¹ * (c * z' * c⁻¹) * (c * x * c⁻¹)⁻¹ by group] at this
    · intro h1
      have h2 : (x : H) * z' * (x : H)⁻¹ ∈ S := by
        have := S.mul_mem (S.mul_mem (S.inv_mem hcS) h1) hcS
        rwa [show c⁻¹ * (c * x * c⁻¹ * (c * z' * c⁻¹) * (c * x * c⁻¹)⁻¹) * c =
          (x : H) * z' * (x : H)⁻¹ by group] at this
      have h3 := hN.mpr h2
      exact S.mul_mem (S.mul_mem hcS h3) (S.inv_mem hcS)
  · rw [diagFun_of_not_mem hk]
    exact one_mem _

include Q in
theorem exists_orderOf_eq_five (i₀ : Fin r) :
    ∃ f : E i₀, orderOf f = 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha, K, _, _, hK, ⟨eK⟩⟩ := Q.sz i₀
  have h2 : 2 ∣ Nat.card (E i₀) := by
    have h1 := (card_sylow_and_center ha hK eK (Q.sylowE i₀)).1
    have hdvd := Subgroup.card_subgroup_dvd_card (Q.sylowE i₀ : Subgroup (E i₀))
    rw [h1] at hdvd
    exact (dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)).trans hdvd
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  obtain ⟨f, hf, -⟩ := exists_orderOf_eq_five_inv hK eK ht
  exact ⟨f, hf⟩

include Q in
theorem exists_isL24_of_hyperplane (i₀ : Fin r)
    {A₁ : Subgroup H} (hA₁A : A₁ ≤ A) (hidx : A₁.relIndex A = 2) {a : H} (haA : a ∈ A)
    (haA₁ : a ∉ A₁)
    (hN₀ : ∀ c ∈ A, (E i₀).map (MulAut.conj c).toMonoidHom = E i₀ → c ∈ A₁)
    (hC₀ : ∀ c ∈ A, (E i₀).map (MulAut.conj c).toMonoidHom = E i₀ → ∀ y ∈ E i₀, c * y * c⁻¹ = y) :
    ∃ L, IsL24 S M A L := by
  haveI := Q.normal
  have hcomm : ∀ c ∈ A, ∀ d ∈ A, c * d = d * c := fun c hc d hd =>
    isElemAbelian_comm Q.hyp.elemAb hc hd
  have hstab : ∀ c ∈ A₁, (E i₀).map (MulAut.conj c).toMonoidHom = E i₀ →
      ∀ y ∈ E i₀, c * y * c⁻¹ = y := fun c hc => hC₀ c (hA₁A hc)
  obtain ⟨a', ha', K, _, _, hK, ⟨eK⟩⟩ := Q.sz i₀
  obtain ⟨e, he⟩ := Q.exists_orderOf_eq_five i₀
  set x : N := diag Q.toComps A₁ i₀ e with hxdef
  set xa : N := MulAut.conjNormal a x with hxadef
  have ha2 : a * a = 1 := by rw [← pow_two]; exact Q.hyp.elemAb.2 a haA
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hxx : x * xa = xa * x := by
    refine Q.ext_coord fun k => ?_
    rw [map_mul, map_mul]
    by_cases hk : InOrbit E A₁ i₀ k
    · rw [hxadef, Q.coord_conj_diag_eq_one A₁ i₀ haA haA₁ hA₁A hcomm hN₀ e hk, mul_one, one_mul]
    · rw [hxdef, coord_diag, diagFun_of_not_mem hk, one_mul, mul_one]
  set y : N := x⁻¹ * xa with hydef
  have hyB : (y : H) ∈ centralizer (A₁ : Set H) := by
    rw [mem_centralizer_iff]
    intro b hb
    have h1 : b * (x : H) * b⁻¹ = x := by
      have := congrArg Subtype.val (Q.conj_diag_of_mem A₁ i₀ hstab hb e)
      simpa using this
    have h2 : b * (xa : H) * b⁻¹ = xa := by
      rw [hxadef, MulAut.conjNormal_apply]
      calc b * (a * x * a⁻¹) * b⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by
            rw [show b * (a * (x : H) * a⁻¹) * b⁻¹ = (b * a) * x * (a⁻¹ * b⁻¹) by group,
              hcomm b (hA₁A hb) a haA, ← mul_inv_rev, hcomm b (hA₁A hb) a haA]
            group
        _ = a * x * a⁻¹ := by rw [h1]
    have h3 : b * (y : H) * b⁻¹ = y := by
      rw [hydef, Subgroup.coe_mul, Subgroup.coe_inv]
      calc b * ((x : H)⁻¹ * xa) * b⁻¹ = (b * x * b⁻¹)⁻¹ * (b * xa * b⁻¹) := by group
        _ = (x : H)⁻¹ * xa := by rw [h1, h2]
    calc b * (y : H) = b * y * b⁻¹ * b := by group
      _ = y * b := by rw [h3]
  have hay : a * (y : H) * a⁻¹ = (y : H)⁻¹ := by
    rw [hydef, Subgroup.coe_mul, Subgroup.coe_inv, hxadef, MulAut.conjNormal_apply]
    calc a * ((x : H)⁻¹ * (a * x * a⁻¹)) * a⁻¹ = (a * x * a⁻¹)⁻¹ * ((a * a) * x * (a * a)⁻¹) := by
          group
      _ = ((x : H)⁻¹ * (a * x * a⁻¹))⁻¹ := by rw [ha2]; group
  have hy0 : Q.coord i₀ y = e⁻¹ := by
    have hi₀ : InOrbit E A₁ i₀ i₀ := ⟨1, A₁.one_mem, map_conj_one' _⟩
    rw [hydef, map_mul, map_inv, hxadef,
      Q.coord_conj_diag_eq_one A₁ i₀ haA haA₁ hA₁A hcomm hN₀ e hi₀, mul_one]
    exact congrArg (·⁻¹) (Subtype.ext (Q.coord_diag_self A₁ i₀ hstab e))
  have hyM : (y : H) ∉ M := by
    intro hyM
    have h1 := Q.coord_mem_normalizer y hyM i₀
    rw [hy0] at h1
    have h2 : e ∈ normalizer ((Q.sylowE i₀ : Subgroup (E i₀)) : Set (E i₀)) := by
      simpa using inv_mem h1
    apply not_five_dvd_card_normalizer hK eK (Q.sylowE i₀)
    rw [← he, ← Subgroup.orderOf_mk e h2]
    exact orderOf_dvd_natCard _
  have hy5 : (y : H) ^ 5 = 1 := by
    have hx5 : x ^ 5 = 1 := by rw [hxdef, ← map_pow, ← he, pow_orderOf_eq_one, map_one]
    have hxa5 : xa ^ 5 = 1 := by rw [hxadef, ← map_pow, hx5, map_one]
    have hc : Commute x⁻¹ xa := (show Commute x xa from hxx).inv_left
    have : y ^ 5 = 1 := by rw [hydef, hc.mul_pow, inv_pow, hx5, hxa5, inv_one, one_mul]
    simpa using congrArg Subtype.val this
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hyo : orderOf (y : H) = 5 :=
    orderOf_eq_prime hy5 fun h1 => hyM (by rw [h1]; exact M.one_mem)
  exact ⟨_, isL24_zpowers_sup Q.hyp hA₁A hidx haA haA₁ hyB hay (p := 5) (by norm_num) (by norm_num)
    hyo hyM⟩

include Q in
theorem exists_of_compl
    (hSub : CFSG.LocalAnalysis.WeakClosure81.SuzukiSubgroupInput) (i₀ : Fin r) {A₁ : Subgroup H}
    (hA₁A : A₁ ≤ A)
    (hdecomp : ∀ b ∈ A, ∃ c ∈ A₁, ∃ n ∈ A,
      (E i₀).map (MulAut.conj n).toMonoidHom = E i₀ ∧ b = c * n)
    (hA₁N : ∀ c ∈ A₁, (E i₀).map (MulAut.conj c).toMonoidHom = E i₀ → c = 1)
    (hnc : ∃ n ∈ A, (E i₀).map (MulAut.conj n).toMonoidHom = E i₀ ∧
      ∃ w ∈ E i₀, n * w * n⁻¹ ≠ w) :
    ∃ L, IsL24 S M A L ∨ IsL24Sz S M A L := by
  haveI := Q.normal
  have hcomm : ∀ c ∈ A, ∀ d ∈ A, c * d = d * c := fun c hc d hd =>
    isElemAbelian_comm Q.hyp.elemAb hc hd
  have hstab : ∀ c ∈ A₁, (E i₀).map (MulAut.conj c).toMonoidHom = E i₀ →
      ∀ y ∈ E i₀, c * y * c⁻¹ = y := fun c hc hcE y _ => by rw [hA₁N c hc hcE]; group
  have hA₁S : A₁ ≤ S := hA₁A.trans Q.hyp.le_S
  obtain ⟨a, ha, K, _, _, hK, ⟨eK⟩⟩ := Q.sz i₀
  set δ : E i₀ →* H := N.subtype.comp (diag Q.toComps A₁ i₀) with hδdef
  have hδ : ∀ w, δ w = ((diag Q.toComps A₁ i₀ w : N) : H) := fun w => rfl
  have hδinj : Function.Injective δ := by
    intro w w' h
    have h1 := congrArg (fun n : N => (Q.coord i₀ n : H))
      (Subtype.ext h : diag Q.toComps A₁ i₀ w = diag Q.toComps A₁ i₀ w')
    simp only [Q.coord_diag_self A₁ i₀ hstab] at h1
    exact Subtype.ext h1
  set Δ := δ.range with hΔdef
  set φ := MonoidHom.ofInjective hδinj with hφdef
  have hφ : ∀ w, ((φ w : Δ) : H) = δ w := fun w => rfl
  have hinner : ∀ b ∈ A, ∃ g ∈ Δ, ∀ x ∈ Δ, b * x * b⁻¹ = g * x * g⁻¹ := by
    intro b hb
    obtain ⟨c, hc, n, hn, hnE, rfl⟩ := hdecomp b hb
    have hn2 : n * n = 1 := by rw [← pow_two]; exact Q.hyp.elemAb.2 n hn
    set σ : MulAut (E i₀) := ((MulAut.conj n).subgroupMap (E i₀)).trans
      (MulEquiv.subgroupCongr (by simpa using hnE)) with hσdef
    have hσ : ∀ w : E i₀, (σ w : H) = n * w * n⁻¹ := fun w => rfl
    have hσ2 : σ ^ 2 ^ 1 = 1 := by
      ext w
      rw [pow_one, pow_two, MulAut.mul_apply, MulAut.one_apply, hσ, hσ]
      rw [show n * (n * (w : H) * n⁻¹) * n⁻¹ = (n * n) * w * (n * n)⁻¹ by group, hn2]
      group
    obtain ⟨g₀, hg₀⟩ := exists_conj_of_pow_eq_one ha hK eK hσ2
    refine ⟨δ g₀, ⟨g₀, rfl⟩, ?_⟩
    rintro _ ⟨w, rfl⟩
    have h1 : n * δ w * n⁻¹ = δ ⟨n * w * n⁻¹, conj_mem_of_map_eq hnE w.2⟩ := by
      have := congrArg Subtype.val (Q.conj_diag_of_normalizes A₁ i₀ hnE
        (fun c' hc' => hcomm n hn c' (hA₁A hc')) w)
      rw [hδ, hδ]
      simpa using this
    have h2 : ∀ v : E i₀, c * δ v * c⁻¹ = δ v := fun v => by
      have := congrArg Subtype.val (Q.conj_diag_of_mem A₁ i₀ hstab hc v)
      rw [hδ]
      simpa using this
    have h3 : (⟨n * w * n⁻¹, conj_mem_of_map_eq hnE w.2⟩ : E i₀) = g₀ * w * g₀⁻¹ := by
      have := congrArg (fun τ : MulAut (E i₀) => τ w) hg₀
      simp only [MulAut.conj_apply] at this
      exact Subtype.ext ((hσ w).symm.trans (congrArg Subtype.val this))
    calc c * n * δ w * (c * n)⁻¹ = c * (n * δ w * n⁻¹) * c⁻¹ := by group
      _ = δ (g₀ * w * g₀⁻¹) := by rw [h1, h2, h3]
      _ = δ g₀ * δ w * (δ g₀)⁻¹ := by simp [map_mul, map_inv]
  have hncΔ : ¬ A ≤ centralizer (Δ : Set H) := by
    intro hle
    obtain ⟨n, hn, hnE, w, hw, hnw⟩ := hnc
    apply hnw
    have h1 : n * δ ⟨w, hw⟩ * n⁻¹ = δ ⟨n * w * n⁻¹, conj_mem_of_map_eq hnE hw⟩ := by
      have := congrArg Subtype.val (Q.conj_diag_of_normalizes A₁ i₀ hnE
        (fun c' hc' => hcomm n hn c' (hA₁A hc')) ⟨w, hw⟩)
      rw [hδ, hδ]
      simpa using this
    have h2 : n * δ ⟨w, hw⟩ * n⁻¹ = δ ⟨w, hw⟩ := by
      have := (mem_centralizer_iff.mp (hle hn)) (δ ⟨w, hw⟩) ⟨⟨w, hw⟩, rfl⟩
      rw [← this]
      group
    have := hδinj (h1.symm.trans h2)
    exact congrArg Subtype.val this
  have hδS : ∀ w : E i₀, δ w ∈ S ↔ (w : H) ∈ S := fun w => Q.diag_mem_iff A₁ i₀ hA₁S hstab w
  have hSΔ : ¬ 2 ∣ S.relIndex Δ := by
    have h1 : S.comap δ = S.subgroupOf (E i₀) := by
      ext w
      rw [mem_comap, mem_subgroupOf]
      exact hδS w
    rw [hΔdef, ← index_comap, h1]
    exact Q.not_dvd_relIndex i₀
  have hMΔ : M.subgroupOf Δ = normalizer ((S.subgroupOf Δ : Subgroup Δ) : Set Δ) := by
    ext y
    obtain ⟨w, rfl⟩ := φ.surjective y
    rw [mem_subgroupOf, hφ, map_mem_normalizer_iff φ (P := S.subgroupOf (E i₀)) (fun z => by
      rw [mem_subgroupOf, mem_subgroupOf, hφ]; exact hδS z), hδ,
      Q.diag_mem_M_iff A₁ i₀ hA₁S hstab w, Q.coe_sylowE]
  exact exists_isL24_or_isL24Sz_of_inner hSub Q.hyp ha hK (φ.symm.trans eK) hinner hncΔ hSΔ hMΔ

end SzConfig

theorem exists_isL24_or_isL24Sz_of_nonsolvable
    (hSub : CFSG.LocalAnalysis.WeakClosure81.SuzukiSubgroupInput) {H : Type*} [Group H]
    [Finite H] {S M A : Subgroup H}
    (hSz : ∀ E : Subgroup H, IsSimpleGroup E → (∃ x y : E, x * y ≠ y * x) →
      ∃ a : ℕ, 1 ≤ a ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ (2 * a + 1) ∧
        Nonempty (↥E ≃* suzukiGroup a K))
    (h : Hyp24 S M A) (hO : oTwo H = ⊥) (hD : M.normalCore = ⊥) (N : Subgroup H)
    (hNn : N.Normal) (hN1 : N ≠ ⊥) (hmin : ∀ K : Subgroup H, K.Normal → K ≤ N → K = ⊥ ∨ K = N)
    (hNs : ¬ Group.IsSolvable N) : ∃ L, IsL24 S M A L ∨ IsL24Sz S M A L := by
  obtain ⟨r, E, -, hEN, hEs, hconj, hEnorm, e, he⟩ :=
    CFSG.LocalCores.minimal_normal_simple_factors hNn hN1 hmin
  set C : Comps N r E := ⟨e, he, hEN⟩ with hCdef
  have hnin : ∀ k, ∀ n ∈ N, ∀ x ∈ E k, n * x * n⁻¹ ∈ E k := by
    intro k n hn x hx
    have := (hEnorm k).conj_mem ⟨x, hEN k hx⟩ hx ⟨n, hn⟩
    exact this
  have hconj' : ∀ i j, ∃ g : H, E j = (E i).map (MulAut.conj g).toMonoidHom := by
    intro i j
    obtain ⟨g, hg⟩ := hconj i j
    exact ⟨g⁻¹, hg⟩
  have hEna : ∀ i, ∃ x y : E i, x * y ≠ y * x := by
    intro i
    by_contra hcon
    push Not at hcon
    apply hNs
    have hcomm : ∀ j (x y : H), x ∈ E j → y ∈ E j → x * y = y * x := by
      intro j x y hx hy
      obtain ⟨g, hg⟩ := hconj' i j
      rw [hg] at hx hy
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      have := congrArg Subtype.val (hcon ⟨x', hx'⟩ ⟨y', hy'⟩)
      simp only [Subgroup.coe_mul] at this
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * x' * g⁻¹ * (g * y' * g⁻¹) = g * (x' * y') * g⁻¹ := by group
        _ = g * (y' * x') * g⁻¹ := by rw [this]
        _ = g * y' * g⁻¹ * (g * x' * g⁻¹) := by group
    have : ∀ n m : N, n * m = m * n := fun n m => C.ext_coord fun j => Subtype.ext (by
      rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
      exact hcomm j _ _ (C.coord j n).2 (C.coord j m).2)
    exact isSolvable_of_comm this
  set Q : SzConfig S M A N r E :=
    SzConfig.mk C h hO hD hNn hEs (fun i => hSz _ (hEs i) (hEna i)) hnin hconj' hN1 with hQdef
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, ¬ A ≤ centralizer (E i₀ : Set H) := by
    by_contra hcon
    push Not at hcon
    apply h.not_le_normalCore
    have hNA : N ≤ centralizer (A : Set H) :=
      Q.le_of_forall_le fun i => le_centralizer_iff.mp (hcon i)
    intro a ha
    rw [mem_normalCore_iff]
    intro g
    have hg : g ∈ ((M ⊔ N : Subgroup H) : Set H) := by rw [Q.sup_eq_top]; exact mem_top g
    rw [mul_normal] at hg
    obtain ⟨m, hm, n, hn, rfl⟩ := hg
    have hna : n * a = a * n := ((mem_centralizer_iff.mp (hNA hn)) a ha).symm
    rw [show m * n * a * (m * n)⁻¹ = m * (n * a * n⁻¹) * m⁻¹ by group, hna, mul_inv_cancel_right]
    exact M.mul_mem (M.mul_mem hm (h.le_M (h.le_S ha))) (M.inv_mem hm)
  set N₀ : Subgroup H := A ⊓ normalizer ((E i₀ : Subgroup H) : Set H) with hN₀def
  have hN₀iff : ∀ c, c ∈ N₀ ↔ c ∈ A ∧ (E i₀).map (MulAut.conj c).toMonoidHom = E i₀ := fun c => by
    rw [hN₀def, mem_inf, mem_normalizer_iff_map_conj_eq]
  by_cases hcase : ∃ n ∈ A, (E i₀).map (MulAut.conj n).toMonoidHom = E i₀ ∧
      ∃ w ∈ E i₀, n * w * n⁻¹ ≠ w
  ·
    obtain ⟨A₁, hA₁A, hA₁N₀, hdec⟩ :=
      exists_compl_of_isElemAbelian h.elemAb (inf_le_left : N₀ ≤ A)
    refine Q.exists_of_compl hSub i₀ hA₁A ?_ ?_ hcase
    · intro b hb
      obtain ⟨c, hc, n, hn, rfl⟩ := hdec b hb
      exact ⟨c, hc, n, ((hN₀iff n).mp hn).1, ((hN₀iff n).mp hn).2, rfl⟩
    · intro c hc hcE
      have : c ∈ A₁ ⊓ N₀ := ⟨hc, (hN₀iff c).mpr ⟨hA₁A hc, hcE⟩⟩
      rw [hA₁N₀] at this
      exact mem_bot.mp this
  ·
    push Not at hcase
    obtain ⟨a, haA, haN⟩ : ∃ a ∈ A, a ∉ N₀ := by
      by_contra hcon
      push Not at hcon
      apply hi₀
      intro b hb
      rw [mem_centralizer_iff]
      intro w hw
      have := hcase b hb ((hN₀iff b).mp (hcon b hb)).2 w hw
      calc w * b = b * w * b⁻¹ * b := by rw [this]
        _ = b * w := by group
    obtain ⟨A₁, hN₀A₁, hA₁A, haA₁, hidx⟩ :=
      exists_hyperplane_of_isElemAbelian h.elemAb inf_le_left haA haN
    exact (Q.exists_isL24_of_hyperplane i₀ hA₁A hidx haA haA₁
      (fun c hc hcE => hN₀A₁ ((hN₀iff c).mpr ⟨hc, hcE⟩)) hcase).imp fun L hL => Or.inl hL

theorem step24_szSections
    (hSub : CFSG.LocalAnalysis.WeakClosure81.SuzukiSubgroupInput) :
    Step24.{u} (fun G _ => SzSections G) := by
  intro H _ _ S M A hP h hO hD N hNn hN1 hmin hNs
  refine exists_isL24_or_isL24Sz_of_nonsolvable hSub (fun E hE hna => ?_) h hO hD N hNn hN1 hmin
    hNs
  haveI := hE
  exact hP.isSzGroup E (MonoidHom.id E) Function.surjective_id hna

theorem exists_isL24_or_isL24Sz_of_szSections
    (hSub : CFSG.LocalAnalysis.WeakClosure81.SuzukiSubgroupInput) {H : Type u} [Group H]
    [Finite H] (hH : SzSections H) {S M A : Subgroup H} (h : Hyp24 S M A) :
    ∃ L, IsL24 S M A L ∨ IsL24Sz S M A L :=
  exists_isL24_or_isL24Sz_of_step (fun G _ => SzSections G) (fun _ _ K hG => hG.subgroup K)
    (fun _ _ N _ hG => hG.quotient N) (step24_szSections hSub) hH h

theorem exists_isL24_or_isL24Sz_of_szSections_subgroup
    (hSub : CFSG.LocalAnalysis.WeakClosure81.SuzukiSubgroupInput) {G : Type u} [Group G]
    [Finite G] {H : Subgroup G} (hH : SzSections H) {S M A : Subgroup G} (hS : IsPGroup 2 S)
    (hSH : S ≤ H) (hSi : ¬ 2 ∣ S.relIndex H) (hMH : M ≤ H) (hM : IsCoatom (M.subgroupOf H))
    (hSM : S ≤ M) (hAS : A ≤ S) (hA : CFSG.Open.IsElemAbelian 2 A)
    (hAD : ∃ h ∈ H, ∃ a ∈ A, h * a * h⁻¹ ∉ M) : ∃ L ≤ H, IsL24 S M A L ∨ IsL24Sz S M A L :=
  exists_isL24_or_isL24Sz_of_step_subgroup (fun G _ => SzSections G)
    (fun _ _ K hG => hG.subgroup K) (fun _ _ N _ hG => hG.quotient N) (step24_szSections hSub) hH
    hS hSH hSi hMH hM hSM hAS hA hAD

end CFSG.RankThree.S4Free.Stell
