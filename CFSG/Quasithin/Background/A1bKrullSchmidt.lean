module

public import Mathlib.GroupTheory.Index
public import Mathlib.Order.SupIndep
public import Mathlib.Data.SetLike.Fintype
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin

def IsIndecomposableGroup (A : Type*) [Group A] : Prop :=
  Nontrivial A ∧ ∀ B C : Subgroup A, B.Normal → C.Normal → B ⊓ C = ⊥ → B ⊔ C = ⊤ →
    B = ⊥ ∨ C = ⊥

structure IsIndexedDirectProduct {X : Type*} [Group X] {ι : Type*}
    (Xs : ι → Subgroup X) : Prop where
  normal : ∀ i, (Xs i).Normal
  independent : iSupIndep Xs
  iSup_eq_top : ⨆ i, Xs i = ⊤

namespace A1b

@[expose] def iterEnd {A : Type*} [Group A] (φ : A →* A) : ℕ → (A →* A)
  | 0 => MonoidHom.id A
  | k + 1 => φ.comp (iterEnd φ k)

theorem iterEnd_succ_apply {A : Type*} [Group A] (φ : A →* A) (k : ℕ) (x : A) :
    iterEnd φ (k + 1) x = φ (iterEnd φ k x) := rfl

theorem iterEnd_add {A : Type*} [Group A] (φ : A →* A) (a b : ℕ) (x : A) :
    iterEnd φ (a + b) x = iterEnd φ a (iterEnd φ b x) := by
  induction a with
  | zero => rw [Nat.zero_add]; rfl
  | succ a ih => rw [Nat.add_right_comm, iterEnd_succ_apply, ih]; rfl

theorem iterEnd_succ_apply' {A : Type*} [Group A] (φ : A →* A) (k : ℕ) (x : A) :
    iterEnd φ (k + 1) x = iterEnd φ k (φ x) := by
  rw [iterEnd_add φ k 1]
  rfl

theorem fitting_decomp {A : Type*} [Group A] [Finite A] (φ : A →* A)
    (hφ : ∀ g x : A, φ (g * x * g⁻¹) = g * φ x * g⁻¹) :
    ∃ N : ℕ, 0 < N ∧ (MonoidHom.ker (iterEnd φ N)).Normal ∧ (MonoidHom.range (iterEnd φ N)).Normal ∧
      MonoidHom.ker (iterEnd φ N) ⊓ MonoidHom.range (iterEnd φ N) = ⊥ ∧
      MonoidHom.ker (iterEnd φ N) ⊔ MonoidHom.range (iterEnd φ N) = ⊤ := by
  have hpow : ∀ (k : ℕ) (g x : A), iterEnd φ k (g * x * g⁻¹) = g * iterEnd φ k x * g⁻¹ := by
    intro k
    induction k with
    | zero => intro g x; rfl
    | succ k ih =>
      intro g x
      rw [iterEnd_succ_apply, iterEnd_succ_apply, ih, hφ]
  have hmono : Monotone (fun k : ℕ => MonoidHom.ker (iterEnd φ k)) := by
    refine monotone_nat_of_le_succ fun k x hx => ?_
    rw [MonoidHom.mem_ker] at hx ⊢
    rw [iterEnd_succ_apply, hx, map_one]
  obtain ⟨n, hn⟩ := wellFoundedGT_iff_monotone_chain_condition.1 inferInstance ⟨_, hmono⟩
  have hstab : ∀ m : ℕ, n + 1 ≤ m →
      MonoidHom.ker (iterEnd φ (n + 1)) = MonoidHom.ker (iterEnd φ m) :=
    fun m hm => (hn (n + 1) (by omega)).symm.trans (hn m (by omega))
  set N := n + 1 with hN
  have hKK : MonoidHom.ker (iterEnd φ N) = MonoidHom.ker (iterEnd φ (N + N)) := hstab _ (by omega)
  refine ⟨N, Nat.succ_pos n, inferInstance, ?_, ?_, ?_⟩
  · refine ⟨fun y hy g => ?_⟩
    obtain ⟨x, rfl⟩ := hy
    exact ⟨g * x * g⁻¹, hpow N g x⟩
  · rw [eq_bot_iff]
    rintro y ⟨hyk, ⟨x, rfl⟩⟩
    have hx : x ∈ MonoidHom.ker (iterEnd φ (N + N)) := by
      rw [MonoidHom.mem_ker, iterEnd_add φ N N x]
      exact hyk
    rw [← hKK, MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_bot]
    exact hx
  · have hR : MonoidHom.range (iterEnd φ (N + N)) ≤ MonoidHom.range (iterEnd φ N) := by
      rintro _ ⟨x, rfl⟩
      exact ⟨iterEnd φ N x, (iterEnd_add φ N N x).symm⟩
    have hcard : Nat.card (MonoidHom.range (iterEnd φ N)) ≤
        Nat.card (MonoidHom.range (iterEnd φ (N + N))) := by
      have h1 := Subgroup.card_ker_mul_card_range (iterEnd φ N)
      have h2 := Subgroup.card_ker_mul_card_range (iterEnd φ (N + N))
      rw [← hKK] at h2
      have hpos : 0 < Nat.card (MonoidHom.ker (iterEnd φ N)) := Nat.card_pos
      exact (Nat.mul_left_cancel hpos (h1.trans h2.symm)).le
    have hReq := Subgroup.eq_of_le_of_card_ge hR hcard
    rw [eq_top_iff]
    intro x _
    have hmem : iterEnd φ N x ∈ MonoidHom.range (iterEnd φ (N + N)) := by
      rw [hReq]
      exact ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := hmem
    have h1 : x * (iterEnd φ N z)⁻¹ ∈ MonoidHom.ker (iterEnd φ N) := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      have : iterEnd φ N (iterEnd φ N z) = iterEnd φ N x := by
        rw [← hz]
        exact (iterEnd_add φ N N z).symm
      rw [this, mul_inv_cancel]
    have h2 : iterEnd φ N z ∈ MonoidHom.range (iterEnd φ N) := ⟨z, rfl⟩
    have := Subgroup.mul_mem_sup h1 h2
    simpa using this

theorem fitting {A : Type*} [Group A] [Finite A] (hA : IsIndecomposableGroup A) (φ : A →* A)
    (hφ : ∀ g x : A, φ (g * x * g⁻¹) = g * φ x * g⁻¹) :
    (∀ x, φ x = 1 → x = 1) ∨ ∃ n : ℕ, ∀ x, iterEnd φ n x = 1 := by
  obtain ⟨N, hN0, hK, hR, hinf, hsup⟩ := fitting_decomp φ hφ
  rcases hA.2 _ _ hK hR hinf hsup with h | h
  · left
    intro x hx
    have h1 : iterEnd φ N x = 1 := by
      obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
      rw [iterEnd_succ_apply', hx, map_one]
    have hxk : x ∈ MonoidHom.ker (iterEnd φ N) := h1
    rw [h] at hxk
    exact hxk
  · right
    refine ⟨N, fun x => ?_⟩
    have : iterEnd φ N x ∈ MonoidHom.range (iterEnd φ N) := ⟨x, rfl⟩
    rw [h] at this
    exact Subgroup.mem_bot.1 this

theorem inj_or_inj_of_mul_eq {A : Type*} [Group A] [Finite A] (hA : IsIndecomposableGroup A)
    (φ ψ : A →* A) (hφ : ∀ g x : A, φ (g * x * g⁻¹) = g * φ x * g⁻¹)
    (hprod : ∀ x, φ x * ψ x = x) : (∀ x, φ x = 1 → x = 1) ∨ (∀ x, ψ x = 1 → x = 1) := by
  rcases fitting hA φ hφ with h | ⟨n, hn⟩
  · exact Or.inl h
  · right
    intro x hx
    have h1 : φ x = x := by
      have := hprod x
      rwa [hx, mul_one] at this
    have h2 : ∀ k : ℕ, iterEnd φ k x = x := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [iterEnd_succ_apply', h1]; exact ih
    rw [← h2 n]
    exact hn x


theorem exists_projs {X : Type*} [Group X] {Y Z : Subgroup X} (hY : Y.Normal) (hZ : Z.Normal)
    (hd : Y ⊓ Z = ⊥) (hs : Y ⊔ Z = ⊤) :
    ∃ πY πZ : X →* X, (∀ x, πY x ∈ Y) ∧ (∀ x, πZ x ∈ Z) ∧ (∀ x, πY x * πZ x = x) ∧
      (∀ z ∈ Z, πY z = 1) ∧ (∀ y ∈ Y, πZ y = 1) ∧
      (∀ g x, πY (g * x * g⁻¹) = g * πY x * g⁻¹) := by
  have hcomm : ∀ y ∈ Y, ∀ z ∈ Z, z * y = y * z := fun y hy z hz =>
    Subgroup.commute_of_normal_of_disjoint Y Z hY hZ (disjoint_iff.2 hd) y z hy hz |>.symm
  have hex : ∀ x : X, ∃ y ∈ Y, ∃ z ∈ Z, y * z = x := fun x => by
    have : x ∈ Y ⊔ Z := by rw [hs]; exact Subgroup.mem_top x
    exact Subgroup.mem_sup_of_normal_left.1 this
  have huniq : ∀ y ∈ Y, ∀ y' ∈ Y, ∀ z ∈ Z, ∀ z' ∈ Z, y * z = y' * z' → y = y' ∧ z = z' := by
    intro y hy y' hy' z hz z' hz' h
    have h1 : y'⁻¹ * y = z' * z⁻¹ := by
      calc y'⁻¹ * y = y'⁻¹ * (y * z) * z⁻¹ := by group
        _ = y'⁻¹ * (y' * z') * z⁻¹ := by rw [h]
        _ = z' * z⁻¹ := by group
    have h2 : y'⁻¹ * y ∈ Y ⊓ Z := ⟨Y.mul_mem (Y.inv_mem hy') hy, h1 ▸ Z.mul_mem hz' (Z.inv_mem hz)⟩
    rw [hd, Subgroup.mem_bot] at h2
    have hyy : y = y' := by
      have := congrArg (y' * ·) h2
      simpa using this
    refine ⟨hyy, ?_⟩
    rw [hyy] at h
    exact mul_left_cancel h
  choose f hfY g hgZ hfg using hex
  have hmul : ∀ x x', f (x * x') = f x * f x' ∧ g (x * x') = g x * g x' := by
    intro x x'
    have h1 : x * x' = (f x * f x') * (g x * g x') := by
      calc x * x' = (f x * g x) * (f x' * g x') := by rw [hfg, hfg]
        _ = f x * (g x * f x') * g x' := by group
        _ = f x * (f x' * g x) * g x' := by rw [hcomm (f x') (hfY x') (g x) (hgZ x)]
        _ = (f x * f x') * (g x * g x') := by group
    exact huniq (f (x * x')) (hfY _) (f x * f x') (Y.mul_mem (hfY x) (hfY x')) (g (x * x'))
      (hgZ _) (g x * g x') (Z.mul_mem (hgZ x) (hgZ x')) ((hfg _).trans h1)
  have hone : f 1 = 1 ∧ g 1 = 1 :=
    huniq (f 1) (hfY _) 1 Y.one_mem (g 1) (hgZ _) 1 Z.one_mem (by rw [hfg, mul_one])
  have hconj : ∀ (h : X) (x : X), f (h * x * h⁻¹) = h * f x * h⁻¹ ∧
      g (h * x * h⁻¹) = h * g x * h⁻¹ := by
    intro h x
    have h1 : h * x * h⁻¹ = (h * f x * h⁻¹) * (h * g x * h⁻¹) := by
      calc h * x * h⁻¹ = h * (f x * g x) * h⁻¹ := by rw [hfg]
        _ = (h * f x * h⁻¹) * (h * g x * h⁻¹) := by group
    exact huniq (f (h * x * h⁻¹)) (hfY _) (h * f x * h⁻¹) (hY.conj_mem _ (hfY x) h)
      (g (h * x * h⁻¹)) (hgZ _) (h * g x * h⁻¹) (hZ.conj_mem _ (hgZ x) h) ((hfg _).trans h1)
  have hkerZ : ∀ z ∈ Z, f z = 1 := fun z hz =>
    (huniq (f z) (hfY _) 1 Y.one_mem (g z) (hgZ _) z hz (by rw [hfg, one_mul])).1
  have hkerY : ∀ y ∈ Y, g y = 1 := fun y hy =>
    (huniq (f y) (hfY _) y hy (g y) (hgZ _) 1 Z.one_mem (by rw [hfg, mul_one])).2
  exact ⟨⟨⟨f, hone.1⟩, fun x x' => (hmul x x').1⟩, ⟨⟨g, hone.2⟩, fun x x' => (hmul x x').2⟩,
    hfY, hgZ, hfg, hkerZ, hkerY, fun h x => (hconj h x).1⟩

theorem aut_disjoint_or {X : Type*} [Group X] [Finite X] {A A' Y Z : Subgroup X}
    (hAn : A.Normal) (hA'n : A'.Normal) (hAd : A ⊓ A' = ⊥) (hAs : A ⊔ A' = ⊤)
    (hA : IsIndecomposableGroup A) (hYn : Y.Normal) (hZn : Z.Normal) (hYZ : Y ⊓ Z = ⊥)
    (hYZs : Y ⊔ Z = ⊤) (α : MulAut X) :
    A.map α.toMonoidHom ⊓ Z = ⊥ ∨ A.map α.toMonoidHom ⊓ Y = ⊥ := by
  obtain ⟨πA, πA', hπAmem, hπA'mem, hπAsum, hπA'ker, -, hπAnorm⟩ := exists_projs hAn hA'n hAd hAs
  obtain ⟨πY, πZ, hπYmem, hπZmem, hπYZ, hπYker, hπZker, hπYnorm⟩ :=
    exists_projs hYn hZn hYZ hYZs
  have hfixA : ∀ a ∈ A, πA a = a := by
    intro a ha
    have h1 := hπAsum a
    have h2 : πA' a = 1 := by
      have h3 : πA' a ∈ A ⊓ A' := by
        refine ⟨?_, hπA'mem a⟩
        have : πA' a = (πA a)⁻¹ * a := by
          calc πA' a = (πA a)⁻¹ * (πA a * πA' a) := by group
            _ = (πA a)⁻¹ * a := by rw [h1]
        rw [this]
        exact A.mul_mem (A.inv_mem (hπAmem a)) ha
      rw [hAd, Subgroup.mem_bot] at h3
      exact h3
    rw [h2, mul_one] at h1
    exact h1
  let θ : (X →* X) → (A →* A) := fun π =>
    ((πA.comp (α.symm.toMonoidHom.comp (π.comp α.toMonoidHom))).comp A.subtype).codRestrict A
      (fun a => hπAmem _)
  have hθ : ∀ (π : X →* X) (a : A), ((θ π a : A) : X) = πA (α.symm (π (α a))) := fun _ _ => rfl
  have hprod : ∀ a, θ πY a * θ πZ a = a := by
    intro a
    apply Subtype.ext
    rw [Subgroup.coe_mul, hθ, hθ, ← map_mul, ← map_mul, hπYZ, MulEquiv.symm_apply_apply]
    exact hfixA a a.2
  have hnorm : ∀ g x : A, θ πY (g * x * g⁻¹) = g * θ πY x * g⁻¹ := by
    intro g x
    apply Subtype.ext
    have e1 : (((g * x * g⁻¹ : A)) : X) = (g : X) * (x : X) * (g : X)⁻¹ := rfl
    have e2 : ((g * θ πY x * g⁻¹ : A) : X) = (g : X) * ((θ πY x : A) : X) * (g : X)⁻¹ := rfl
    have e3 : α ((g : X) * (x : X) * (g : X)⁻¹) = α g * α x * (α g)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    have e4 : ∀ y : X, α.symm (α g * y * (α g)⁻¹) = g * α.symm y * (g : X)⁻¹ := by
      intro y
      rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
    rw [e2, hθ, hθ, e1, e3, hπYnorm, e4, hπAnorm]
  have hinj := inj_or_inj_of_mul_eq hA (θ πY) (θ πZ) hnorm hprod
  rcases hinj with h | h
  · left
    rw [eq_bot_iff]
    rintro y ⟨⟨a, haA, rfl⟩, hyZ⟩
    have h1 : πY (α a) = 1 := hπYker _ hyZ
    have h2 : θ πY ⟨a, haA⟩ = 1 := by
      apply Subtype.ext
      rw [hθ]
      show πA (α.symm (πY (α a))) = 1
      rw [h1, map_one, map_one]
    have h3 := h _ h2
    have : a = 1 := congrArg Subtype.val h3
    rw [Subgroup.mem_bot]
    show α a = 1
    rw [this, map_one]
  · right
    rw [eq_bot_iff]
    rintro y ⟨⟨a, haA, rfl⟩, hyY⟩
    have h1 : πZ (α a) = 1 := hπZker _ hyY
    have h2 : θ πZ ⟨a, haA⟩ = 1 := by
      apply Subtype.ext
      rw [hθ]
      show πA (α.symm (πZ (α a))) = 1
      rw [h1, map_one, map_one]
    have h3 := h _ h2
    have : a = 1 := congrArg Subtype.val h3
    rw [Subgroup.mem_bot]
    show α a = 1
    rw [this, map_one]

def restProd {X : Type*} [Group X] {ι : Type*} (Xs : ι → Subgroup X) (k : ι) : Subgroup X :=
  ⨆ (l : ι) (_ : l ≠ k), Xs l

end A1b

open A1b

namespace IsIndexedDirectProduct

variable {X : Type*} [Group X] {ι : Type*} {Xs : ι → Subgroup X}

theorem le_restProd {l k : ι} (hlk : l ≠ k) : Xs l ≤ restProd Xs k :=
  le_iSup₂ (f := fun l (_ : l ≠ k) => Xs l) l hlk

theorem disjoint_restProd (h : IsIndexedDirectProduct Xs) (k : ι) :
    Disjoint (Xs k) (restProd Xs k) := h.independent k

theorem inf_restProd (h : IsIndexedDirectProduct Xs) (k : ι) : Xs k ⊓ restProd Xs k = ⊥ :=
  disjoint_iff.1 (h.disjoint_restProd k)

theorem sup_restProd (h : IsIndexedDirectProduct Xs) (k : ι) : Xs k ⊔ restProd Xs k = ⊤ := by
  rw [eq_top_iff, ← h.iSup_eq_top]
  refine iSup_le fun l => ?_
  by_cases hlk : l = k
  · subst hlk
    exact le_sup_left
  · exact (le_restProd hlk).trans le_sup_right

theorem normal_restProd (h : IsIndexedDirectProduct Xs) (k : ι) : (restProd Xs k).Normal := by
  have := h.normal
  unfold restProd
  infer_instance

theorem disjoint (h : IsIndexedDirectProduct Xs) {i j : ι} (hij : i ≠ j) :
    Disjoint (Xs i) (Xs j) :=
  (h.disjoint_restProd i).mono_right (le_restProd hij.symm)

theorem commute (h : IsIndexedDirectProduct Xs) {i j : ι} (hij : i ≠ j) {x y : X}
    (hx : x ∈ Xs i) (hy : y ∈ Xs j) : x * y = y * x :=
  Subgroup.commute_of_normal_of_disjoint (Xs i) (Xs j) (h.normal i) (h.normal j)
    (h.disjoint hij) x y hx hy

theorem mem_center_of_commute (h : IsIndexedDirectProduct Xs) {x : X}
    (hx : ∀ l, ∀ y ∈ Xs l, x * y = y * x) : x ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff]
  intro g
  have hle : ⨆ l, Xs l ≤ Subgroup.centralizer ({x} : Set X) := by
    refine iSup_le fun l y hy => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact hx l y hy
  have hg : g ∈ Subgroup.centralizer ({x} : Set X) := hle (h.iSup_eq_top ▸ Subgroup.mem_top g)
  rw [Subgroup.mem_centralizer_iff] at hg
  exact (hg x rfl).symm

theorem le_sup_center (h : IsIndexedDirectProduct Xs) (k : ι) {S : Subgroup X}
    (hS : ∀ l, l ≠ k → ∀ x ∈ S, ∀ y ∈ Xs l, x * y = y * x) :
    S ≤ Xs k ⊔ Subgroup.center X := by
  intro x hx
  have := h.normal k
  have hxX : x ∈ Xs k ⊔ restProd Xs k := by rw [h.sup_restProd k]; exact Subgroup.mem_top x
  obtain ⟨a, ha, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hxX
  have hzc : z ∈ Subgroup.center X := by
    refine h.mem_center_of_commute fun l y hy => ?_
    by_cases hlk : l = k
    · subst hlk
      exact (Subgroup.commute_of_normal_of_disjoint (Xs l) (restProd Xs l) (h.normal l)
        (h.normal_restProd l) (h.disjoint_restProd l) y z hy hz).symm
    · have h1 : a * z * y = y * (a * z) := hS l hlk _ hx y hy
      have h2 : a * y = y * a := h.commute (Ne.symm hlk) ha hy
      have h2' : a⁻¹ * y * a = y := by
        calc a⁻¹ * y * a = a⁻¹ * (y * a) := by group
          _ = a⁻¹ * (a * y) := by rw [h2]
          _ = y := by group
      calc z * y = a⁻¹ * (a * z * y) := by group
        _ = a⁻¹ * (y * (a * z)) := by rw [h1]
        _ = (a⁻¹ * y * a) * z := by group
        _ = y * z := by rw [h2']
  exact Subgroup.mul_mem_sup ha hzc

theorem exists_le_sup_center [Finite X] (h : IsIndexedDirectProduct Xs)
    (hind : ∀ i, IsIndecomposableGroup (Xs i)) (α : MulAut X) (i : ι) :
    ∃ k, (Xs i).map α.toMonoidHom ≤ Xs k ⊔ Subgroup.center X := by
  set S := (Xs i).map α.toMonoidHom with hS
  have hSn : S.Normal := (h.normal i).map α.toMonoidHom α.surjective
  have key : ∀ k, S ⊓ restProd Xs k = ⊥ ∨ S ⊓ Xs k = ⊥ := fun k =>
    aut_disjoint_or (h.normal i) (h.normal_restProd i) (h.inf_restProd i) (h.sup_restProd i)
      (hind i) (h.normal k) (h.normal_restProd k) (h.inf_restProd k) (h.sup_restProd k) α
  by_cases hex : ∃ k, S ⊓ restProd Xs k = ⊥
  · obtain ⟨k, hk⟩ := hex
    refine ⟨k, h.le_sup_center k fun l hlk x hx y hy => ?_⟩
    have hd : Disjoint S (Xs l) := (disjoint_iff.2 hk).mono_right (le_restProd hlk)
    exact Subgroup.commute_of_normal_of_disjoint S (Xs l) hSn (h.normal l) hd x y hx hy
  · push Not at hex
    have hall : ∀ l, S ⊓ Xs l = ⊥ := fun l => (key l).resolve_left (hex l)
    refine ⟨i, ?_⟩
    have : S ≤ Subgroup.center X := by
      intro x hx
      refine h.mem_center_of_commute fun l y hy => ?_
      exact Subgroup.commute_of_normal_of_disjoint S (Xs l) hSn (h.normal l)
        (disjoint_iff.2 (hall l)) x y hx hy
    exact this.trans le_sup_right

end IsIndexedDirectProduct

open IsIndexedDirectProduct in
theorem krull_schmidt_aut_permutes {X : Type*} [Group X] [Finite X] {ι : Type*} [Finite ι]
    {Xs : ι → Subgroup X} (h : IsIndexedDirectProduct Xs)
    (hind : ∀ i, IsIndecomposableGroup (Xs i)) (α : MulAut X) :
    ∃ τ : Equiv.Perm ι, ∀ i, (Xs i ⊔ Subgroup.center X).map α.toMonoidHom =
      Xs (τ i) ⊔ Subgroup.center X := by
  classical
  set Z := Subgroup.center X with hZ
  have hZinv : ∀ (e : MulAut X) (z : X), z ∈ Z → e z ∈ Z := by
    intro e z hz
    rw [hZ, Subgroup.mem_center_iff] at hz ⊢
    intro g
    have h2 := congrArg e (hz (e.symm g))
    simpa [map_mul] using h2
  choose f hf using fun i => exists_le_sup_center h hind α i
  choose g hg using fun i => exists_le_sup_center h hind α.symm i
  have hf' : ∀ i, ∀ x ∈ Xs i, α x ∈ Xs (f i) ⊔ Z := fun i x hx =>
    hf i (Subgroup.mem_map_of_mem α.toMonoidHom hx)
  have hg' : ∀ i, ∀ x ∈ Xs i, α.symm x ∈ Xs (g i) ⊔ Z := fun i x hx =>
    hg i (Subgroup.mem_map_of_mem α.symm.toMonoidHom hx)
  have hP1 : ∀ i j, ¬ Xs i ≤ Z → Xs i ≤ Xs j ⊔ Z → j = i := by
    intro i j hi hij
    by_contra hne
    apply hi
    intro x hx
    have := h.normal j
    obtain ⟨a, ha, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 (hij hx)
    refine h.mem_center_of_commute fun l y hy => ?_
    by_cases hlj : l = j
    · subst hlj
      exact h.commute (fun h' => hne h'.symm) hx hy
    · have h2 : a * y = y * a := h.commute (Ne.symm hlj) ha hy
      have h3 : y * z = z * y := Subgroup.mem_center_iff.1 hz y
      calc a * z * y = a * (z * y) := by group
        _ = a * (y * z) := by rw [h3]
        _ = (a * y) * z := by group
        _ = (y * a) * z := by rw [h2]
        _ = y * (a * z) := by group
  have hP2 : ∀ i, ¬ Xs i ≤ Z → ¬ Xs (f i) ≤ Z := by
    intro i hi hfi
    apply hi
    intro x hx
    have h1 : α x ∈ Z := by
      have := hf' i x hx
      exact (sup_le hfi le_rfl : Xs (f i) ⊔ Z ≤ Z) this
    have := hZinv α.symm _ h1
    simpa using this
  have hP3 : ∀ i, ¬ Xs i ≤ Z → g (f i) = i := by
    intro i hi
    refine hP1 i _ hi fun x hx => ?_
    have := h.normal (f i)
    obtain ⟨b, hb, z, hz, hbz⟩ := Subgroup.mem_sup_of_normal_left.1 (hf' i x hx)
    have hx' : x = α.symm b * α.symm z := by
      rw [← map_mul, hbz]; simp
    rw [hx']
    exact (Xs (g (f i)) ⊔ Z).mul_mem (hg' _ b hb) (Subgroup.mem_sup_right (hZinv α.symm z hz))
  have hmapZ : Z.map α.toMonoidHom = Z := by
    ext y
    rw [Subgroup.mem_map_equiv]
    constructor
    · intro hy
      have := hZinv α _ hy
      simpa using this
    · intro hy
      exact hZinv α.symm y hy
  have hcentral : ∀ i, Xs i ≤ Z → (Xs i ⊔ Z).map α.toMonoidHom = Xs i ⊔ Z := by
    intro i hi
    rw [sup_eq_right.2 hi, hmapZ]
  have hnoncentral : ∀ i, ¬ Xs i ≤ Z →
      (Xs i ⊔ Z).map α.toMonoidHom = Xs (f i) ⊔ Z := by
    intro i hi
    ext y
    rw [Subgroup.mem_map_equiv]
    constructor
    · intro hy
      have := h.normal i
      obtain ⟨a, ha, z, hz, hax⟩ := Subgroup.mem_sup_of_normal_left.1 hy
      have hy' : y = α a * α z := by
        rw [← map_mul, hax]; simp
      rw [hy']
      exact (Xs (f i) ⊔ Z).mul_mem (hf' i a ha) (Subgroup.mem_sup_right (hZinv α z hz))
    · intro hy
      have := h.normal (f i)
      obtain ⟨b, hb, z, hz, hbz⟩ := Subgroup.mem_sup_of_normal_left.1 hy
      have hy' : α.symm y = α.symm b * α.symm z := by
        rw [← map_mul, hbz]
      rw [hy']
      have h1 := hg' (f i) b hb
      rw [hP3 i hi] at h1
      exact (Xs i ⊔ Z).mul_mem h1 (Subgroup.mem_sup_right (hZinv α.symm z hz))
  let τ : ι → ι := fun i => if Xs i ≤ Z then i else f i
  have hτinj : Function.Injective τ := by
    intro i j hij
    by_cases hi : Xs i ≤ Z <;> by_cases hj : Xs j ≤ Z
    · simpa [τ, hi, hj] using hij
    · exfalso
      have : f j = i := by simpa [τ, hi, hj] using hij.symm
      exact hP2 j hj (this ▸ hi)
    · exfalso
      have : f i = j := by simpa [τ, hi, hj] using hij
      exact hP2 i hi (this ▸ hj)
    · have : f i = f j := by simpa [τ, hi, hj] using hij
      calc i = g (f i) := (hP3 i hi).symm
        _ = g (f j) := by rw [this]
        _ = j := hP3 j hj
  refine ⟨Equiv.ofBijective τ (Finite.injective_iff_bijective.1 hτinj), fun i => ?_⟩
  by_cases hi : Xs i ≤ Z
  · have : τ i = i := by simp [τ, hi]
    show _ = Xs (τ i) ⊔ Z
    rw [this]
    exact hcentral i hi
  · have : τ i = f i := by simp [τ, hi]
    show _ = Xs (τ i) ⊔ Z
    rw [this]
    exact hnoncentral i hi


end CFSG.Quasithin
