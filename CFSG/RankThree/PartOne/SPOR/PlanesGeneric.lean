module

public import CFSG.RankThree.PartOne.KS.PlaneWitness

public section

namespace CFSG.RankThree.PartOne.SPOR

open Subgroup CFSG.RankThree.PartOne

variable {A : Type} [Group A]

@[expose] def fixSub (r : MulAut A) : Subgroup A where
  carrier := {a | r a = a}
  one_mem' := map_one r
  mul_mem' := fun {a b} (ha : r a = a) (hb : r b = b) => by
    show r (a * b) = a * b
    rw [map_mul, ha, hb]
  inv_mem' := fun {a} (ha : r a = a) => by
    show r a⁻¹ = a⁻¹
    rw [map_inv, ha]

theorem mem_fixSub {r : MulAut A} {a : A} : a ∈ fixSub r ↔ r a = a := Iff.rfl

theorem aut_mul_conj_comm_of_fixed {r : MulAut A} {g : A} (hg : r g = g) :
    r * MulAut.conj g = MulAut.conj g * r := by
  ext y
  simp [MulAut.conj_apply, hg, map_mul, map_inv]

theorem conj_injective_of_trivial_center (hc : ∀ a : A, (∀ b : A, a * b = b * a) → a = 1) :
    Function.Injective (MulAut.conj : A →* MulAut A) := by
  intro a b hab
  have h : ∀ y : A, a * y * a⁻¹ = b * y * b⁻¹ := fun y => by
    simpa [MulAut.conj_apply] using congrArg (fun f : MulAut A => f y) hab
  have hcen : ∀ y : A, (b⁻¹ * a) * y = y * (b⁻¹ * a) := fun y => by
    calc b⁻¹ * a * y = b⁻¹ * (a * y * a⁻¹) * a := by group
      _ = b⁻¹ * (b * y * b⁻¹) * a := by rw [h y]
      _ = y * (b⁻¹ * a) := by group
  have := hc _ hcen
  exact (inv_mul_eq_one.1 this).symm

theorem conjWitness_of_cover {p : ℕ} (hc : ∀ a : A, (∀ b : A, a * b = b * a) → a = 1)
    {ι : Type*} (r : ι → MulAut A)
    (hr : ∀ v : MulAut A, orderOf v = 2 → ∃ j, IsConj v (r j))
    (hcover : ∀ j (y : A), r j y = y → orderOf y = p →
      ∃ l : List A, (∀ g ∈ l, g * y = y * g) ∧
        p ∣ orderOf ((l.map fun g => MulAut.conj g * r j * (MulAut.conj g)⁻¹).prod)) :
    ConjWitness A p := by
  intro v x hv hx hcomm
  obtain ⟨j, hj⟩ := hr v hv
  obtain ⟨φ, hφ⟩ := isConj_iff.1 hj
  have hvx : v x = x := by
    apply conj_injective_of_trivial_center hc
    show MulAut.conj (v x) = MulAut.conj x
    rw [conj_aut_apply_eq, hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hvr : v = φ⁻¹ * r j * φ := by rw [← hφ]; group
  have hfix : r j (φ x) = φ x := by
    have : (r j) = φ * v * φ⁻¹ := hφ.symm
    rw [this]
    show φ (v (φ⁻¹ (φ x))) = φ x
    rw [show φ⁻¹ (φ x) = x from by simp, hvx]
  have hord : orderOf (φ x) = p := by rw [MulEquiv.orderOf_eq]; exact hx
  obtain ⟨l', hl', hord'⟩ := hcover j (φ x) hfix hord
  refine ⟨l'.map (fun d => φ⁻¹ d), ?_, ?_⟩
  · intro g hg
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hg
    have h := congrArg (fun z => φ⁻¹ z) (hl' d hd)
    simpa [map_mul] using h
  · set Φ : MulAut (MulAut A) := MulAut.conj (φ⁻¹) with hΦ
    have key : ((l'.map fun d => φ⁻¹ d).map
        fun g => MulAut.conj g * v * (MulAut.conj g)⁻¹).prod =
        Φ ((l'.map fun g => MulAut.conj g * r j * (MulAut.conj g)⁻¹).prod) := by
      rw [map_list_prod, List.map_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro d _
      simp only [Function.comp, hΦ, MulAut.conj_apply, inv_inv, conj_aut_apply_eq, hvr]
      group
    rw [key, MulEquiv.orderOf_eq]
    exact hord'

theorem exists_sylow_subgroupOf_eq [Finite A] {p : ℕ} (hp : p.Prime) {P Q : Subgroup A}
    (hQP : Q ≤ P) (hQ : IsPGroup p Q) {k N m : ℕ} (hN : Nat.card P = N) (hNm : N = p ^ k * m)
    (hm : ¬ p ∣ m) (hk : Nat.card Q = p ^ k) :
    ∃ S : Sylow p P, (S : Subgroup P) = Q.subgroupOf P := by
  have : Fact p.Prime := ⟨hp⟩
  have hQ' : IsPGroup p (Q.subgroupOf P) := hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQP).symm
  obtain ⟨S, hS⟩ := hQ'.exists_le_sylow
  refine ⟨S, ?_⟩
  have hm0 : m ≠ 0 := fun h => by
    have := Nat.card_pos (α := P)
    rw [hN, hNm, h, mul_zero] at this
    exact lt_irrefl _ this
  have hcardS : Nat.card (S : Subgroup P) = p ^ k := by
    rw [Sylow.card_eq_multiplicity]
    have hPN : Nat.card P = p ^ k * m := hN.trans hNm
    rw [hPN, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm0]
    simp [Nat.Prime.factorization_pow hp, Nat.factorization_eq_zero_of_not_dvd hm]
  have hcardQ' : Nat.card (Q.subgroupOf P) = p ^ k :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv).trans hk
  exact (Subgroup.eq_of_le_of_card_ge hS (by rw [hcardS, hcardQ'])).symm

theorem exists_conj_of_cover {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    {P Q : Subgroup M} {κ : Type*} {xs : κ → M}
    (hSyl : ∃ S : Sylow p P, (S : Subgroup P) = Q.subgroupOf P)
    (hcov : ∀ z ∈ Q, orderOf z = p → ∃ i, zpowers z = zpowers (xs i))
    {y : M} (hyP : y ∈ P) (hord : orderOf y = p) :
    ∃ g : M, g ∈ P ∧ ∃ i : κ,
      centralizer ({g⁻¹ * y * g} : Set M) = centralizer ({xs i} : Set M) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S₀, hS₀⟩ := hSyl
  have hpgrp : IsPGroup p (zpowers (⟨y, hyP⟩ : P)) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, hord, pow_one])
  obtain ⟨S, hS⟩ := hpgrp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P S₀ S
  have hyS : (⟨y, hyP⟩ : P) ∈ (S : Subgroup P) := hS (Subgroup.mem_zpowers _)
  have hy'Q : (g : M)⁻¹ * y * (g : M) ∈ Q := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hyS
    rw [hS₀, Subgroup.mem_subgroupOf] at hyS
    simpa [MulAut.smul_def, ← map_inv, MulAut.conj_apply, mul_assoc] using hyS
  have hord' : orderOf ((g : M)⁻¹ * y * (g : M)) = p := by
    have := orderOf_injective (MulAut.conj (g : M)⁻¹).toMonoidHom
      (MulAut.conj (g : M)⁻¹).injective y
    rw [hord] at this
    rw [← this]
    simp [mul_assoc]
  obtain ⟨i, hi⟩ := hcov _ hy'Q hord'
  refine ⟨g, g.2, i, ?_⟩
  rw [CFSG.RankThree.GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers,
    CFSG.RankThree.GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers (xs i), hi]

theorem cover_of_lines [Finite A] {p : ℕ} (hp : p.Prime) (r : MulAut A) {Q : Subgroup A}
    (hSyl : ∃ S : Sylow p (fixSub r), (S : Subgroup (fixSub r)) = Q.subgroupOf (fixSub r))
    {κ : Type*} (xs : κ → A)
    (hcov : ∀ z ∈ Q, orderOf z = p → ∃ i, zpowers z = zpowers (xs i))
    (hwit : ∀ i, ∃ l : List A, (∀ g ∈ l, g * xs i = xs i * g) ∧
      p ∣ orderOf ((l.map fun g => MulAut.conj g * r * (MulAut.conj g)⁻¹).prod)) :
    ∀ y : A, r y = y → orderOf y = p →
      ∃ l : List A, (∀ g ∈ l, g * y = y * g) ∧
        p ∣ orderOf ((l.map fun g => MulAut.conj g * r * (MulAut.conj g)⁻¹).prod) := by
  intro y hy hord
  obtain ⟨g, hgP, i, hcent⟩ := exists_conj_of_cover hp hSyl hcov (mem_fixSub.2 hy) hord
  have hgf : r g = g := mem_fixSub.1 hgP
  obtain ⟨l, hl, hord'⟩ := hwit i
  have hconj : MulAut.conj g⁻¹ * r * MulAut.conj g = r := by
    have h := aut_mul_conj_comm_of_fixed hgf
    calc MulAut.conj g⁻¹ * r * MulAut.conj g = MulAut.conj g⁻¹ * (r * MulAut.conj g) := by group
      _ = MulAut.conj g⁻¹ * (MulAut.conj g * r) := by rw [h]
      _ = r := by rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  refine ⟨l.map (fun d => g * d * g⁻¹), ?_, ?_⟩
  · intro d' hd'
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hd'
    have hdc : d ∈ centralizer ({xs i} : Set A) := mem_centralizer_singleton_iff.2 (hl d hd)
    rw [← hcent, mem_centralizer_singleton_iff] at hdc
    calc (g * d * g⁻¹) * y = g * (d * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * d) * g⁻¹ := by rw [hdc]
      _ = y * (g * d * g⁻¹) := by group
  · set Ψ : MulAut (MulAut A) := MulAut.conj (MulAut.conj g) with hΨ
    have hconj' : (MulAut.conj g)⁻¹ * r * MulAut.conj g = r := by
      simpa [map_inv] using hconj
    have step : ∀ d : A, MulAut.conj (g * d * g⁻¹) * r * (MulAut.conj (g * d * g⁻¹))⁻¹ =
        Ψ (MulAut.conj d * r * (MulAut.conj d)⁻¹) := fun d => by
      rw [hΨ, MulAut.conj_apply]
      simp only [map_mul, map_inv]
      calc MulAut.conj g * MulAut.conj d * (MulAut.conj g)⁻¹ * r *
            (MulAut.conj g * MulAut.conj d * (MulAut.conj g)⁻¹)⁻¹
          = MulAut.conj g * MulAut.conj d * ((MulAut.conj g)⁻¹ * r * MulAut.conj g) *
              (MulAut.conj d)⁻¹ * (MulAut.conj g)⁻¹ := by group
        _ = MulAut.conj g * MulAut.conj d * r * (MulAut.conj d)⁻¹ * (MulAut.conj g)⁻¹ := by
            rw [hconj']
        _ = MulAut.conj g * (MulAut.conj d * r * (MulAut.conj d)⁻¹) * (MulAut.conj g)⁻¹ := by group
    have key : ((l.map fun d => g * d * g⁻¹).map
        fun h => MulAut.conj h * r * (MulAut.conj h)⁻¹).prod =
        Ψ ((l.map fun d => MulAut.conj d * r * (MulAut.conj d)⁻¹).prod) := by
      rw [map_list_prod, List.map_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro d _
      exact step d
    rw [key, MulEquiv.orderOf_eq]
    exact hord'

section Lines

variable {G : Type*} [Group G]

theorem mem_closure_pair {y₁ y₂ : G} (hc : y₁ * y₂ = y₂ * y₁) {z : G}
    (hz : z ∈ closure ({y₁, y₂} : Set G)) : ∃ a b : ℤ, z = y₁ ^ a * y₂ ^ b := by
  induction hz using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ⟨1, 0, by simp⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, d, rfl⟩ := hy
    refine ⟨a + c, b + d, ?_⟩
    have hcom : y₂ ^ b * y₁ ^ c = y₁ ^ c * y₂ ^ b :=
      (Commute.zpow_zpow (hc : Commute y₁ y₂) c b).eq.symm
    calc y₁ ^ a * y₂ ^ b * (y₁ ^ c * y₂ ^ d) = y₁ ^ a * (y₂ ^ b * y₁ ^ c) * y₂ ^ d := by group
      _ = y₁ ^ a * (y₁ ^ c * y₂ ^ b) * y₂ ^ d := by rw [hcom]
      _ = y₁ ^ (a + c) * y₂ ^ (b + d) := by rw [zpow_add, zpow_add]; group
  | inv x _ hx =>
    obtain ⟨a, b, rfl⟩ := hx
    refine ⟨-a, -b, ?_⟩
    have hcom : y₂ ^ (-b) * y₁ ^ (-a) = y₁ ^ (-a) * y₂ ^ (-b) :=
      (Commute.zpow_zpow (hc : Commute y₁ y₂) (-a) (-b)).eq.symm
    calc (y₁ ^ a * y₂ ^ b)⁻¹ = y₂ ^ (-b) * y₁ ^ (-a) := by group
      _ = y₁ ^ (-a) * y₂ ^ (-b) := hcom

theorem mem_closure_pair_nat {p : ℕ} (hp : 0 < p) {y₁ y₂ : G} (hc : y₁ * y₂ = y₂ * y₁)
    (h1 : y₁ ^ p = 1) (h2 : y₂ ^ p = 1) {z : G} (hz : z ∈ closure ({y₁, y₂} : Set G)) :
    ∃ a b : ℕ, a < p ∧ b < p ∧ z = y₁ ^ a * y₂ ^ b := by
  obtain ⟨a, b, rfl⟩ := mem_closure_pair hc hz
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have key : ∀ (y : G) (e : ℤ), y ^ p = 1 → y ^ e = y ^ (e % (p : ℤ)).toNat := fun y e hy => by
    rw [zpow_eq_zpow_emod (n := (p : ℤ)) e (by exact_mod_cast hy)]
    have h0 : 0 ≤ e % (p : ℤ) := Int.emod_nonneg _ hp'.ne'
    calc y ^ (e % (p : ℤ)) = y ^ (((e % (p : ℤ)).toNat : ℕ) : ℤ) := by rw [Int.toNat_of_nonneg h0]
      _ = y ^ (e % (p : ℤ)).toNat := zpow_natCast _ _
  refine ⟨(a % (p : ℤ)).toNat, (b % (p : ℤ)).toNat, ?_, ?_, ?_⟩
  · have := Int.emod_lt_of_pos a hp'
    have h0 := Int.emod_nonneg a hp'.ne'
    omega
  · have := Int.emod_lt_of_pos b hp'
    have h0 := Int.emod_nonneg b hp'.ne'
    omega
  · rw [← key y₁ a h1, ← key y₂ b h2]

theorem zpowers_eq_of_mem_of_orderOf {x z : G} {p : ℕ} (hp : 0 < p) (hz : z ∈ zpowers x)
    (hzo : orderOf z = p) (hx : x ^ p = 1) : zpowers z = zpowers x := by
  have : Finite (zpowers x) :=
    IsOfFinOrder.finite_zpowers (isOfFinOrder_iff_pow_eq_one.2 ⟨p, hp, hx⟩)
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hz)
  rw [Nat.card_zpowers, Nat.card_zpowers, hzo]
  exact Nat.le_of_dvd hp (orderOf_dvd_of_pow_eq_one hx)

theorem lines_pp {p : ℕ} (hp : p.Prime) {y₁ y₂ : G} (hc : y₁ * y₂ = y₂ * y₁) (h1 : y₁ ^ p = 1)
    (h2 : y₂ ^ p = 1) :
    ∀ z ∈ closure ({y₁, y₂} : Set G), orderOf z = p →
      ∃ i : Option (Fin p), zpowers z =
        zpowers (match i with | none => y₂ | some c => y₁ * y₂ ^ (c : ℕ)) := by
  intro z hz hzo
  obtain ⟨a, b, ha, hb, rfl⟩ := mem_closure_pair_nat hp.pos hc h1 h2 hz
  have hcomm : Commute (y₁ ^ a) (y₂ ^ b) := (Commute.pow_pow (hc : Commute y₁ y₂) a b)
  by_cases ha0 : a = 0
  · subst ha0
    refine ⟨none, ?_⟩
    simp only [pow_zero, one_mul] at hzo ⊢
    exact zpowers_eq_of_mem_of_orderOf hp.pos (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _) hzo h2
  · have hcop : Nat.Coprime p a :=
      (Nat.Prime.coprime_iff_not_dvd hp).2 (fun h => by
        have := Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) h
        omega)
    obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop.symm hp.one_lt
    have hkc : Nat.Coprime p k := by
      refine (Nat.Prime.coprime_iff_not_dvd hp).2 (fun h => ?_)
      have : a * k % p = 0 := Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left h a)
      omega
    have hzk : (y₁ ^ a * y₂ ^ b) ^ k = y₁ * y₂ ^ ((b * k) % p) := by
      rw [hcomm.mul_pow, ← pow_mul, ← pow_mul, pow_eq_pow_mod (a * k) h1, hk,
        pow_eq_pow_mod (b * k) h2]
      simp
    refine ⟨some ⟨(b * k) % p, Nat.mod_lt _ hp.pos⟩, ?_⟩
    have hord : orderOf ((y₁ ^ a * y₂ ^ b) ^ k) = p := by
      rw [Nat.Coprime.orderOf_pow (by rw [hzo]; exact hkc), hzo]
    have hzp : (y₁ ^ a * y₂ ^ b) ^ p = 1 := by rw [← hzo]; exact pow_orderOf_eq_one _
    have h3 := zpowers_eq_of_mem_of_orderOf hp.pos
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers (y₁ ^ a * y₂ ^ b)) k) hord hzp
    simp only
    rw [← hzk, ← h3]

end Lines

section Covers

theorem cover_of_plane [Finite A] {p : ℕ} (hp : p.Prime) (r : MulAut A) {N m : ℕ}
    (hN : Nat.card (fixSub r) = N) (hNm : N = p ^ 2 * m) (hm : ¬ p ∣ m)
    {y₁ y₂ : A} (h1 : r y₁ = y₁) (h2 : r y₂ = y₂) (hc : y₁ * y₂ = y₂ * y₁)
    (hp1 : y₁ ^ p = 1) (hp2 : y₂ ^ p = 1)
    (hinj : ∀ a b a' b' : ℕ, a < p → b < p → a' < p → b' < p →
      y₁ ^ a * y₂ ^ b = y₁ ^ a' * y₂ ^ b' → a = a' ∧ b = b')
    (hw₀ : ∃ l : List A, (∀ g ∈ l, g * y₂ = y₂ * g) ∧
      p ∣ orderOf ((l.map fun g => MulAut.conj g * r * (MulAut.conj g)⁻¹).prod))
    (hw : ∀ c : ℕ, c < p → ∃ l : List A, (∀ g ∈ l, g * (y₁ * y₂ ^ c) = (y₁ * y₂ ^ c) * g) ∧
      p ∣ orderOf ((l.map fun g => MulAut.conj g * r * (MulAut.conj g)⁻¹).prod)) :
    ∀ y : A, r y = y → orderOf y = p →
      ∃ l : List A, (∀ g ∈ l, g * y = y * g) ∧
        p ∣ orderOf ((l.map fun g => MulAut.conj g * r * (MulAut.conj g)⁻¹).prod) := by
  set Q : Subgroup A := closure ({y₁, y₂} : Set A) with hQ
  have hQfix : Q ≤ fixSub r := by
    rw [hQ, Subgroup.closure_le]
    rintro _ (rfl | hx)
    · exact h1
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact h2
  have hmem : ∀ a b : ℕ, y₁ ^ a * y₂ ^ b ∈ Q := fun a b =>
    Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
  let f : Fin p × Fin p → Q := fun ab => ⟨y₁ ^ (ab.1 : ℕ) * y₂ ^ (ab.2 : ℕ), hmem _ _⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      have h' : y₁ ^ (a : ℕ) * y₂ ^ (b : ℕ) = y₁ ^ (a' : ℕ) * y₂ ^ (b' : ℕ) :=
        congrArg Subtype.val h
      obtain ⟨e1, e2⟩ := hinj a b a' b' a.2 b.2 a'.2 b'.2 h'
      exact Prod.ext (Fin.ext e1) (Fin.ext e2)
    · rintro ⟨z, hz⟩
      obtain ⟨a, b, ha, hb, rfl⟩ := mem_closure_pair_nat hp.pos hc hp1 hp2 hz
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have hQcard : Nat.card Q = p ^ 2 := by
    rw [← Nat.card_eq_of_bijective f hf]
    simp [sq]
  have hQp : IsPGroup p Q := IsPGroup.of_card hQcard
  have hSyl := exists_sylow_subgroupOf_eq hp hQfix hQp hN hNm hm hQcard
  exact cover_of_lines hp r hSyl
    (fun i : Option (Fin p) => match i with | none => y₂ | some c => y₁ * y₂ ^ (c : ℕ))
    (lines_pp hp hc hp1 hp2)
    (fun i => match i with
      | none => hw₀
      | some c => hw c c.2)

theorem cover_of_line [Finite A] {p : ℕ} (hp : p.Prime) (r : MulAut A) {N m : ℕ}
    (hN : Nat.card (fixSub r) = N) (hNm : N = p ^ 1 * m) (hm : ¬ p ∣ m)
    {y : A} (h1 : r y = y) (ho : orderOf y = p)
    (hw : ∃ l : List A, (∀ g ∈ l, g * y = y * g) ∧
      p ∣ orderOf ((l.map fun g => MulAut.conj g * r * (MulAut.conj g)⁻¹).prod)) :
    ∀ y' : A, r y' = y' → orderOf y' = p →
      ∃ l : List A, (∀ g ∈ l, g * y' = y' * g) ∧
        p ∣ orderOf ((l.map fun g => MulAut.conj g * r * (MulAut.conj g)⁻¹).prod) := by
  have hQcard : Nat.card (zpowers y) = p ^ 1 := by rw [Nat.card_zpowers, ho, pow_one]
  have hQfix : zpowers y ≤ fixSub r := by
    rw [Subgroup.zpowers_le]
    exact h1
  have hQp : IsPGroup p (zpowers y) := IsPGroup.of_card hQcard
  have hSyl := exists_sylow_subgroupOf_eq hp hQfix hQp hN hNm hm hQcard
  exact cover_of_lines hp r hSyl (fun _ : Unit => y)
    (fun z hz hzo => ⟨(), zpowers_eq_of_mem_of_orderOf hp.pos (Subgroup.mem_zpowers_iff.2 (by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (by simpa using hz); exact ⟨k, hk⟩)) hzo
        (by rw [← ho]; exact pow_orderOf_eq_one y)⟩)
    (fun _ => hw)

end Covers

section Inner

theorem fixSub_conj (a : A) : fixSub (MulAut.conj a) = centralizer ({a} : Set A) := by
  ext y
  rw [mem_fixSub, mem_centralizer_singleton_iff]
  simp only [MulAut.conj_apply]
  rw [mul_inv_eq_iff_eq_mul, eq_comm]

theorem conj_prod_eq (t : A) (l : List A) :
    (l.map fun g => MulAut.conj g * MulAut.conj t * (MulAut.conj g)⁻¹).prod =
      MulAut.conj ((l.map fun g => g * t * g⁻¹).prod) := by
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro g _
  simp [map_mul, map_inv]

theorem orderOf_conj_prod (hc : ∀ a : A, (∀ b : A, a * b = b * a) → a = 1) (t : A)
    (l : List A) :
    orderOf ((l.map fun g => MulAut.conj g * MulAut.conj t * (MulAut.conj g)⁻¹).prod) =
      orderOf ((l.map fun g => g * t * g⁻¹).prod) := by
  rw [conj_prod_eq]
  exact orderOf_injective (MulAut.conj : A →* MulAut A) (conj_injective_of_trivial_center hc) _

theorem conjWitness_of_inner_cover {p : ℕ} (hc : ∀ a : A, (∀ b : A, a * b = b * a) → a = 1)
    (hin : ∀ φ : MulAut A, ∃ a : A, φ = MulAut.conj a) {ι : Type*} (t : ι → A)
    (hr : ∀ s : A, orderOf s = 2 → ∃ j, ∃ c : A, c * s * c⁻¹ = t j)
    (hcover : ∀ j (y : A), y * t j = t j * y → orderOf y = p →
      ∃ l : List A, (∀ g ∈ l, g * y = y * g) ∧
        p ∣ orderOf ((l.map fun g => g * t j * g⁻¹).prod)) :
    ConjWitness A p := by
  refine conjWitness_of_cover hc (fun j => MulAut.conj (t j)) ?_ ?_
  · intro v hv
    obtain ⟨s, rfl⟩ := hin v
    have hs : orderOf s = 2 := by
      rw [← hv]
      exact (orderOf_injective (MulAut.conj : A →* MulAut A)
        (conj_injective_of_trivial_center hc) s).symm
    obtain ⟨j, c, hc'⟩ := hr s hs
    refine ⟨j, isConj_iff.2 ⟨MulAut.conj c, ?_⟩⟩
    rw [← hc']
    simp [map_mul, map_inv]
  · intro j y hy hord
    have hy' : y * t j = t j * y := by
      have : t j * y * (t j)⁻¹ = y := hy
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    obtain ⟨l, hl, hpl⟩ := hcover j y hy' hord
    exact ⟨l, hl, by rw [orderOf_conj_prod hc]; exact hpl⟩

variable [Finite A]

theorem cover_of_plane_inner {p : ℕ} (hp : p.Prime)
    (hc : ∀ a : A, (∀ b : A, a * b = b * a) → a = 1) (t : A) {N m : ℕ}
    (hN : Nat.card (centralizer ({t} : Set A)) = N) (hNm : N = p ^ 2 * m) (hm : ¬ p ∣ m)
    {y₁ y₂ : A} (h1 : y₁ * t = t * y₁) (h2 : y₂ * t = t * y₂) (hc12 : y₁ * y₂ = y₂ * y₁)
    (hp1 : y₁ ^ p = 1) (hp2 : y₂ ^ p = 1)
    (hinj : ∀ a b a' b' : ℕ, a < p → b < p → a' < p → b' < p →
      y₁ ^ a * y₂ ^ b = y₁ ^ a' * y₂ ^ b' → a = a' ∧ b = b')
    (hw₀ : ∃ l : List A, (∀ g ∈ l, g * y₂ = y₂ * g) ∧
      p ∣ orderOf ((l.map fun g => g * t * g⁻¹).prod))
    (hw : ∀ c : ℕ, c < p → ∃ l : List A,
      (∀ g ∈ l, g * (y₁ * y₂ ^ c) = (y₁ * y₂ ^ c) * g) ∧
        p ∣ orderOf ((l.map fun g => g * t * g⁻¹).prod)) :
    ∀ y : A, y * t = t * y → orderOf y = p →
      ∃ l : List A, (∀ g ∈ l, g * y = y * g) ∧ p ∣ orderOf ((l.map fun g => g * t * g⁻¹).prod) := by
  have hfix : ∀ y : A, y * t = t * y → MulAut.conj t y = y := fun y hy => by
    show t * y * t⁻¹ = y
    rw [mul_inv_eq_iff_eq_mul]
    exact hy.symm
  have key := cover_of_plane hp (MulAut.conj t) (N := N) (m := m)
    (by rw [fixSub_conj]; exact hN) hNm hm
    (hfix _ h1) (hfix _ h2) hc12 hp1 hp2 hinj
    (by simpa only [orderOf_conj_prod hc] using hw₀)
    (fun c hc' => by simpa only [orderOf_conj_prod hc] using hw c hc')
  intro y hy ho
  obtain ⟨l, hl, hpl⟩ := key y (hfix y hy) ho
  exact ⟨l, hl, by rwa [orderOf_conj_prod hc] at hpl⟩

theorem cover_of_line_inner {p : ℕ} (hp : p.Prime)
    (hc : ∀ a : A, (∀ b : A, a * b = b * a) → a = 1) (t : A) {N m : ℕ}
    (hN : Nat.card (centralizer ({t} : Set A)) = N) (hNm : N = p ^ 1 * m) (hm : ¬ p ∣ m)
    {y : A} (h1 : y * t = t * y) (ho : orderOf y = p)
    (hw : ∃ l : List A, (∀ g ∈ l, g * y = y * g) ∧
      p ∣ orderOf ((l.map fun g => g * t * g⁻¹).prod)) :
    ∀ y' : A, y' * t = t * y' → orderOf y' = p →
      ∃ l : List A, (∀ g ∈ l, g * y' = y' * g) ∧
        p ∣ orderOf ((l.map fun g => g * t * g⁻¹).prod) := by
  have hfix : ∀ y : A, y * t = t * y → MulAut.conj t y = y := fun y hy => by
    show t * y * t⁻¹ = y
    rw [mul_inv_eq_iff_eq_mul]
    exact hy.symm
  have key := cover_of_line hp (MulAut.conj t) (N := N) (m := m)
    (by rw [fixSub_conj]; exact hN) hNm hm
    (hfix _ h1) ho (by simpa only [orderOf_conj_prod hc] using hw)
  intro y hy ho'
  obtain ⟨l, hl, hpl⟩ := key y (hfix y hy) ho'
  exact ⟨l, hl, by rwa [orderOf_conj_prod hc] at hpl⟩

omit [Finite A] in
theorem cover_of_none_inner {p : ℕ} (t : A) (hN : ¬ p ∣ Nat.card (centralizer ({t} : Set A))) :
    ∀ y : A, y * t = t * y → orderOf y = p →
      ∃ l : List A, (∀ g ∈ l, g * y = y * g) ∧
        p ∣ orderOf ((l.map fun g => g * t * g⁻¹).prod) := by
  intro y hy ho
  exfalso
  apply hN
  have := orderOf_dvd_natCard (⟨y, mem_centralizer_singleton_iff.2 hy⟩ :
    centralizer ({t} : Set A))
  rwa [Subgroup.orderOf_mk y (mem_centralizer_singleton_iff.2 hy), ho] at this

end Inner

section Transport

theorem not_commutative_of_simple_of_not_prime {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (h : ¬ (Nat.card G).Prime) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hcon
  have hcomm : ∀ a b : G, a * b = b * a := fun a b => by
    by_contra hne
    exact hcon ⟨a, b, hne⟩
  let _ : CommGroup G := { ‹Group G› with mul_comm := hcomm }
  exact h (IsSimpleGroup.prime_card (α := G))

theorem trivial_center_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) : ∀ a : G, (∀ b : G, a * b = b * a) → a = 1 := by
  intro a ha
  have : a ∈ center G := Subgroup.mem_center_iff.2 fun b => (ha b).symm
  rw [center_eq_bot_of_simple hnab] at this
  exact this

end Transport

section Predicates

@[expose] def TrivialCenter (G : Type*) [Group G] : Prop :=
  ∀ a : G, (∀ b : G, a * b = b * a) → a = 1

@[expose] def InvolutionReps {G : Type*} [Group G] {ι : Type*} (t : ι → G) : Prop :=
  ∀ s : G, orderOf s = 2 → ∃ j, ∃ c : G, c * s * c⁻¹ = t j

@[expose] def CoverP {G : Type*} [Group G] (p : ℕ) (t : G) : Prop :=
  ∀ y : G, y * t = t * y → orderOf y = p →
    ∃ l : List G, (∀ g ∈ l, g * y = y * g) ∧ p ∣ orderOf ((l.map fun g => g * t * g⁻¹).prod)

theorem conjWitness_of_covers {G : Type} [Group G] {p : ℕ} (hc : TrivialCenter G)
    (hin : ∀ φ : MulAut G, ∃ a : G, φ = MulAut.conj a) {ι : Type*} (t : ι → G)
    (hr : InvolutionReps t) (hcover : ∀ j, CoverP p (t j)) : ConjWitness G p :=
  conjWitness_of_inner_cover hc hin t hr hcover

end Predicates

end CFSG.RankThree.PartOne.SPOR
