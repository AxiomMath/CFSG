module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.J4Rad

section Conj

variable {Γ : Type*} [Group Γ]

@[expose] def conjSub (g : Γ) (A : Subgroup Γ) : Subgroup Γ where
  carrier := {x | g⁻¹ * x * g ∈ A}
  mul_mem' {a b} ha hb := by
    have : g⁻¹ * (a * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) := by group
    show g⁻¹ * (a * b) * g ∈ A
    rw [this]
    exact A.mul_mem ha hb
  one_mem' := by simp
  inv_mem' {a} ha := by
    have : g⁻¹ * a⁻¹ * g = (g⁻¹ * a * g)⁻¹ := by group
    show g⁻¹ * a⁻¹ * g ∈ A
    rw [this]
    exact A.inv_mem ha

theorem mem_conjSub {g x : Γ} {A : Subgroup Γ} : x ∈ conjSub g A ↔ g⁻¹ * x * g ∈ A := Iff.rfl

theorem conjSub_one (A : Subgroup Γ) : conjSub 1 A = A := by
  ext x
  simp [mem_conjSub]

theorem conjSub_mul (g h : Γ) (A : Subgroup Γ) : conjSub (g * h) A = conjSub g (conjSub h A) := by
  ext x
  have : (g * h)⁻¹ * x * (g * h) = h⁻¹ * (g⁻¹ * x * g) * h := by group
  rw [mem_conjSub, mem_conjSub, mem_conjSub, this]

@[expose, instance_reducible] def conjAction (C : Subgroup Γ) (X : Set (Subgroup Γ))
    (hX : ∀ c ∈ C, ∀ A ∈ X, conjSub c A ∈ X) : MulAction ↥C ↥X where
  smul c A := ⟨conjSub (c : Γ) A.1, hX c c.2 A.1 A.2⟩
  one_smul A := Subtype.ext (conjSub_one A.1)
  mul_smul c d A := Subtype.ext (conjSub_mul (c : Γ) (d : Γ) A.1)

@[expose] def kerSub (C : Subgroup Γ) (X : Set (Subgroup Γ)) : Subgroup Γ where
  carrier := {c | c ∈ C ∧ ∀ A ∈ X, conjSub c A = A}
  mul_mem' {a b} ha hb := by
    refine ⟨C.mul_mem ha.1 hb.1, fun A hA => ?_⟩
    rw [conjSub_mul, hb.2 A hA, ha.2 A hA]
  one_mem' := ⟨C.one_mem, fun A _ => conjSub_one A⟩
  inv_mem' {a} ha := by
    refine ⟨C.inv_mem ha.1, fun A hA => ?_⟩
    calc conjSub a⁻¹ A = conjSub a⁻¹ (conjSub a A) := by rw [ha.2 A hA]
      _ = conjSub (a⁻¹ * a) A := (conjSub_mul a⁻¹ a A).symm
      _ = A := by rw [inv_mul_cancel, conjSub_one]

theorem mem_kerSub {C : Subgroup Γ} {X : Set (Subgroup Γ)} {c : Γ} :
    c ∈ kerSub C X ↔ c ∈ C ∧ ∀ A ∈ X, conjSub c A = A := Iff.rfl

end Conj

section Nine

variable {Γ : Type*} [Group Γ]

theorem pow_three_of_mem_closure {G : Type*} [Group G] {a b : G} (hab : a * b = b * a)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) :
    ∀ x ∈ Subgroup.closure ({a, b} : Set G), x ^ 3 = 1 := by
  have hcomm : ∀ x ∈ Subgroup.closure ({a, b} : Set G), ∀ y ∈ Subgroup.closure ({a, b} : Set G),
      x * y = y * x := by
    intro x hx y hy
    induction hx, hy using Subgroup.closure_induction₂ with
    | mem x y hx hy =>
      rcases hx with rfl | hx
      · rcases hy with rfl | hy
        · rfl
        · rw [Set.mem_singleton_iff.mp hy]; exact hab
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        rcases hy with rfl | hy
        · exact hab.symm
        · rw [Set.mem_singleton_iff.mp hy]
    | one_left x _ => simp
    | one_right x _ => simp
    | mul_left x y z _ _ _ h1 h2 => rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
    | mul_right x y z _ _ _ h1 h2 => rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]
    | inv_left x y _ _ h => exact (Commute.inv_left (h : Commute x y)).eq
    | inv_right x y _ _ h => exact (Commute.inv_right (h : Commute x y)).eq
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ha
    · rw [Set.mem_singleton_iff.mp hx]; exact hb
  | one => simp
  | mul x y hx hy h1 h2 =>
    rw [(Commute.mul_pow (hcomm x hx y hy) 3), h1, h2, one_mul]
  | inv x hx h => rw [inv_pow, h, inv_one]

theorem nine_dvd_relIndex_kerSub [Finite Γ] (C : Subgroup Γ) (X : Set (Subgroup Γ))
    (hX : ∀ c ∈ C, ∀ A ∈ X, conjSub c A ∈ X) (g₁ g₂ : Γ) (hg₁ : g₁ ∈ C) (hg₂ : g₂ ∈ C)
    (hcomm : ∀ A ∈ X, conjSub g₁ (conjSub g₂ A) = conjSub g₂ (conjSub g₁ A))
    (h3a : ∀ A ∈ X, conjSub g₁ (conjSub g₁ (conjSub g₁ A)) = A)
    (h3b : ∀ A ∈ X, conjSub g₂ (conjSub g₂ (conjSub g₂ A)) = A)
    (hnea : ∃ A ∈ X, conjSub g₁ A ≠ A)
    (hneb₀ : ∃ A ∈ X, conjSub g₂ A ≠ A)
    (hneb₁ : ∃ A ∈ X, conjSub g₂ A ≠ conjSub g₁ A)
    (hneb₂ : ∃ A ∈ X, conjSub g₂ A ≠ conjSub g₁ (conjSub g₁ A)) :
    9 ∣ (kerSub C X).relIndex C := by
  let _ := conjAction C X hX
  have hfinS : Finite (Subgroup Γ) :=
    Finite.of_injective _ (SetLike.coe_injective (A := Subgroup Γ))
  have hfinX : Finite ↥X := inferInstance
  have hfinP : Finite (Equiv.Perm ↥X) := inferInstance
  let Φ : ↥C →* Equiv.Perm ↥X := MulAction.toPermHom ↥C ↥X
  have hsm : ∀ (c : ↥C) (A : ↥X), ((Φ c) A).1 = conjSub (c : Γ) A.1 := fun c A => rfl
  have hker : Φ.ker = (kerSub C X).subgroupOf C := by
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_kerSub]
    constructor
    · intro h
      refine ⟨c.2, fun A hA => ?_⟩
      have := congrArg (fun σ : Equiv.Perm ↥X => (σ ⟨A, hA⟩).1) h
      simpa [hsm] using this
    · rintro ⟨-, h⟩
      refine Equiv.ext fun A => Subtype.ext ?_
      rw [hsm]
      exact h A.1 A.2
  let c₁ : ↥C := ⟨g₁, hg₁⟩
  let c₂ : ↥C := ⟨g₂, hg₂⟩
  set σ₁ : Equiv.Perm ↥X := Φ c₁ with hσ₁
  set σ₂ : Equiv.Perm ↥X := Φ c₂ with hσ₂
  have e1 : ∀ A : ↥X, (σ₁ A).1 = conjSub g₁ A.1 := fun A => rfl
  have e2 : ∀ A : ↥X, (σ₂ A).1 = conjSub g₂ A.1 := fun A => rfl
  have hcomm' : σ₁ * σ₂ = σ₂ * σ₁ := by
    refine Equiv.ext fun A => Subtype.ext ?_
    show (σ₁ (σ₂ A)).1 = (σ₂ (σ₁ A)).1
    simp only [e1, e2]
    exact hcomm A.1 A.2
  have h3a' : σ₁ ^ 3 = 1 := by
    refine Equiv.ext fun A => Subtype.ext ?_
    rw [pow_three]
    show (σ₁ (σ₁ (σ₁ A))).1 = A.1
    simp only [e1]
    exact h3a A.1 A.2
  have h3b' : σ₂ ^ 3 = 1 := by
    refine Equiv.ext fun A => Subtype.ext ?_
    rw [pow_three]
    show (σ₂ (σ₂ (σ₂ A))).1 = A.1
    simp only [e2]
    exact h3b A.1 A.2
  have hσ₁ne : σ₁ ≠ 1 := by
    intro h
    obtain ⟨A, hA, hne⟩ := hnea
    apply hne
    have := congrArg (fun σ : Equiv.Perm ↥X => (σ ⟨A, hA⟩).1) h
    simpa [e1] using this
  have hord : orderOf σ₁ = 3 := orderOf_eq_prime h3a' hσ₁ne
  have hnot : σ₂ ∉ Subgroup.zpowers σ₁ := by
    rintro ⟨k, hk⟩
    have hk' : σ₁ ^ (k % (orderOf σ₁ : ℤ)) = σ₂ := by rw [zpow_mod_orderOf]; exact hk
    rw [hord] at hk'
    have hk3 : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
    rcases hk3 with h | h | h
    · rw [h, zpow_zero] at hk'
      obtain ⟨A, hA, hne⟩ := hneb₀
      apply hne
      have := congrArg (fun σ : Equiv.Perm ↥X => (σ ⟨A, hA⟩).1) hk'
      simpa [e2] using this.symm
    · rw [h, zpow_one] at hk'
      obtain ⟨A, hA, hne⟩ := hneb₁
      apply hne
      have := congrArg (fun σ : Equiv.Perm ↥X => (σ ⟨A, hA⟩).1) hk'
      simp only [e1, e2] at this
      exact this.symm
    · rw [h] at hk'
      have h2 : σ₁ ^ ((2 : ℤ)) = σ₁ * σ₁ := by rw [zpow_ofNat, pow_two]
      rw [show ((2 : ℤ)) = 2 from rfl, h2] at hk'
      obtain ⟨A, hA, hne⟩ := hneb₂
      apply hne
      have := congrArg (fun σ : Equiv.Perm ↥X => (σ ⟨A, hA⟩).1) hk'
      simp only [Equiv.Perm.mul_apply, e1, e2] at this
      exact this.symm
  set P : Subgroup (Equiv.Perm ↥X) := Subgroup.closure ({σ₁, σ₂} : Set (Equiv.Perm ↥X)) with hP
  have hP3 : ∀ x ∈ P, x ^ 3 = 1 := pow_three_of_mem_closure hcomm' h3a' h3b'
  have hPp : IsPGroup 3 ↥P := fun x => ⟨1, by
    refine Subtype.ext ?_
    simpa using hP3 x x.2⟩
  have hz₁P : Subgroup.zpowers σ₁ ≤ P := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hσ₂P : σ₂ ∈ P := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hPp
  have hge : 3 ≤ Nat.card ↥P := by
    have := Subgroup.card_le_of_le hz₁P
    rwa [Nat.card_zpowers, hord] at this
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hn1 : n ≤ 1 := by omega
    have : 3 ^ n ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
    have heq : Nat.card ↥P = 3 := by omega
    have hz : Subgroup.zpowers σ₁ = P :=
      Subgroup.eq_of_le_of_card_ge hz₁P (by rw [heq, Nat.card_zpowers, hord])
    exact hnot (hz ▸ hσ₂P)
  have h9P : 9 ∣ Nat.card ↥P := by
    rw [hn]
    exact ⟨3 ^ (n - 2), by
      rw [show 3 ^ n = 3 ^ 2 * 3 ^ (n - 2) by rw [← pow_add]; congr 1; omega]
      norm_num⟩
  have hPle : P ≤ Φ.range := by
    rw [hP, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨c₁, rfl⟩
    · exact ⟨c₂, rfl⟩
  have h9 : 9 ∣ Nat.card ↥Φ.range := h9P.trans (Subgroup.card_dvd_of_le hPle)
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  exact h9

end Nine

section Index

variable {Γ : Type*} [Group Γ]

theorem index_ge_of_injection [Finite Γ] (H C : Subgroup Γ) (N : ℕ)
    (f : Fin N → Γ) (hf : ∀ i, f i ∈ H) (hinj : ∀ i j, (f i)⁻¹ * f j ∈ C → i = j) :
    N ≤ (C.subgroupOf H).index := by
  let ψ : Fin N → ↥H ⧸ C.subgroupOf H := fun i => ((⟨f i, hf i⟩ : ↥H) : ↥H ⧸ C.subgroupOf H)
  have hψ : Function.Injective ψ := by
    intro i j hij
    have hq := QuotientGroup.eq.mp hij
    exact hinj i j (Subgroup.mem_subgroupOf.mp hq)
  have := Nat.card_le_card_of_injective ψ hψ
  rwa [Nat.card_eq_fintype_card (α := Fin N), Fintype.card_fin] at this

theorem mem_normalizer_of_conjSub_eq {V : Subgroup Γ} {a b : Γ}
    (h : conjSub a V = conjSub b V) : a⁻¹ * b ∈ Subgroup.normalizer (V : Set Γ) := by
  have h1 : ∀ x : Γ, a⁻¹ * x * a ∈ V ↔ b⁻¹ * x * b ∈ V := fun x => by
    have := SetLike.ext_iff.mp h x
    simpa [mem_conjSub] using this
  have hg : (a⁻¹ * b)⁻¹ ∈ Subgroup.normalizer (V : Set Γ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have := h1 (a * y * a⁻¹)
    have e1 : a⁻¹ * (a * y * a⁻¹) * a = y := by group
    have e2 : b⁻¹ * (a * y * a⁻¹) * b = (a⁻¹ * b)⁻¹ * y * (a⁻¹ * b)⁻¹⁻¹ := by group
    rw [e1, e2] at this
    exact this
  simpa using (Subgroup.normalizer (V : Set Γ)).inv_mem hg

theorem index_normalizer_le [Finite Γ] (H V : Subgroup Γ) (T : Set (Subgroup Γ))
    (hT : ∀ h ∈ H, conjSub h V ∈ T) :
    ((H ⊓ Subgroup.normalizer (V : Set Γ)).subgroupOf H).index ≤ T.ncard := by
  let ψ : ↥H ⧸ (H ⊓ Subgroup.normalizer (V : Set Γ)).subgroupOf H → ↥T :=
    fun q => ⟨conjSub (q.out : Γ) V, hT q.out q.out.2⟩
  have hψ : Function.Injective ψ := by
    intro q q' hqq
    have h1 : conjSub (q.out : Γ) V = conjSub (q'.out : Γ) V := congrArg Subtype.val hqq
    have h2 := mem_normalizer_of_conjSub_eq h1
    have h3 : (q.out)⁻¹ * q'.out ∈ (H ⊓ Subgroup.normalizer (V : Set Γ)).subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨H.mul_mem (H.inv_mem q.out.2) q'.out.2, h2⟩
    have h4 := QuotientGroup.eq.mpr h3
    rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h4
    exact h4
  have hfinS : Finite (Subgroup Γ) :=
    Finite.of_injective _ (SetLike.coe_injective (A := Subgroup Γ))
  have hfin : Finite ↥T := inferInstance
  have := Nat.card_le_card_of_injective ψ hψ
  rw [Nat.card_coe_set_eq] at this
  exact this

theorem normalizerMonoidHom_eq_one_iff' (V : Subgroup Γ) (n : Subgroup.normalizer (V : Set Γ)) :
    V.normalizerMonoidHom n = 1 ↔ (n : Γ) ∈ Subgroup.centralizer (V : Set Γ) := by
  constructor
  · intro h a ha
    have := congrArg (fun f : MulAut V => (f ⟨a, ha⟩ : Γ)) h
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at this
    calc a * (n : Γ) = ((n : Γ) * a * (n : Γ)⁻¹) * (n : Γ) := by rw [this]
      _ = (n : Γ) * a := by group
  · intro h
    ext a
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply]
    have := Subgroup.mem_centralizer_iff.mp h a a.2
    calc (n : Γ) * (a : Γ) * (n : Γ)⁻¹ = (a : Γ) * (n : Γ) * (n : Γ)⁻¹ := by rw [this]
      _ = a := by group

@[expose] def conjAut (V N : Subgroup Γ) (hN : N ≤ Subgroup.normalizer (V : Set Γ)) :
    ↥N →* MulAut ↥V :=
  (V.normalizerMonoidHom).comp (Subgroup.inclusion hN)

theorem ker_conjAut (V N : Subgroup Γ) (hN : N ≤ Subgroup.normalizer (V : Set Γ)) :
    (conjAut V N hN).ker = (N ⊓ Subgroup.centralizer (V : Set Γ)).subgroupOf N := by
  ext n
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  have := normalizerMonoidHom_eq_one_iff' V (Subgroup.inclusion hN n)
  constructor
  · intro h
    exact ⟨n.2, this.mp h⟩
  · rintro ⟨-, h⟩
    exact this.mpr h

theorem index_centralizer_eq (V N : Subgroup Γ) (hN : N ≤ Subgroup.normalizer (V : Set Γ)) :
    ((N ⊓ Subgroup.centralizer (V : Set Γ)).subgroupOf N).index =
      Nat.card (conjAut V N hN).range := by
  rw [← ker_conjAut V N hN, Subgroup.index_ker]

theorem card_mul_relIndex (H C : Subgroup Γ) (hC : C ≤ H) :
    Nat.card ↥C * (C.subgroupOf H).index = Nat.card ↥H := by
  have h := Subgroup.card_mul_index (C.subgroupOf H)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC).toEquiv] at h

theorem ncard_conjSub (g : Γ) (A : Subgroup Γ) :
    ((conjSub g A : Subgroup Γ) : Set Γ).ncard = (A : Set Γ).ncard := by
  have : ((conjSub g A : Subgroup Γ) : Set Γ) = (fun x => g * x * g⁻¹) '' (A : Set Γ) := by
    ext x
    constructor
    · intro hx
      refine ⟨g⁻¹ * x * g, hx, ?_⟩
      group
    · rintro ⟨y, hy, rfl⟩
      show g⁻¹ * (g * y * g⁻¹) * g ∈ A
      have : g⁻¹ * (g * y * g⁻¹) * g = y := by group
      rw [this]
      exact hy
  rw [this]
  exact Set.ncard_image_of_injective _ (fun a b h => by simpa using h)

end Index

end CFSG.Quasithin.J4Rad
