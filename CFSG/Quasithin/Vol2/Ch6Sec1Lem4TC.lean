module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Data.Finite.Perm

public section

namespace CFSG.Quasithin.H13

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem eq_one_of_commute_of_orbit614 {Ω : Type*} {c g : Equiv.Perm Ω} {x₀ : Ω}
    (hgc : g * c = c * g) (hg : g x₀ = x₀) (horb : ∀ y : Ω, ∃ k : ℤ, (c ^ k) x₀ = y) : g = 1 := by
  ext y
  obtain ⟨k, rfl⟩ := horb y
  have hk : g * c ^ k = c ^ k * g := (Commute.zpow_right hgc k)
  have := congrArg (fun f : Equiv.Perm Ω => f x₀) hk
  simp only [Equiv.Perm.mul_apply, hg] at this
  simp [this]

theorem commutator_le_normalCore_of_index_five614 [Finite G] {S : Subgroup G}
    (hS : IsPGroup 2 S) (h5 : S.index = 5) : ⁅S, S⁆ ≤ S.normalCore := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set φ : G →* Equiv.Perm (G ⧸ S) := MulAction.toPermHom G (G ⧸ S) with hφ
  have hker : φ.ker = S.normalCore := (Subgroup.normalCore_eq_ker S).symm
  have hΩ : Nat.card (G ⧸ S) = 5 := h5
  set Q := φ.range with hQ
  obtain ⟨a, ha⟩ := hS.index (S.normalCore.subgroupOf S)
  have hcardQ : Nat.card Q = 5 * 2 ^ a := by
    rw [← Subgroup.index_ker, hker, ← Subgroup.relIndex_mul_index (Subgroup.normalCore_le S), h5]
    show (S.normalCore.subgroupOf S).index * 5 = 5 * 2 ^ a
    rw [ha, mul_comm]
  have hdvd120 : Nat.card Q ∣ 120 := by
    have := Subgroup.card_subgroup_dvd_card Q
    rwa [Nat.card_perm, hΩ] at this
  have ha3 : a ≤ 3 := by
    by_contra h
    have h16 : 2 ^ 4 ∣ 2 ^ a := pow_dvd_pow 2 (by omega)
    have : 5 * 2 ^ 4 ∣ 120 := (Nat.mul_dvd_mul_left 5 h16).trans (hcardQ ▸ hdvd120)
    norm_num at this
  obtain ⟨P₅⟩ := (inferInstance : Nonempty (Sylow 5 Q))
  have hP5 : Nat.card P₅ = 5 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P₅.isPGroup'
    have h5d : 5 ∣ Nat.card P₅ := P₅.dvd_card_of_dvd_card (by rw [hcardQ]; exact dvd_mul_right 5 _)
    have hdQ : Nat.card P₅ ∣ 5 * 2 ^ a := hcardQ ▸ Subgroup.card_subgroup_dvd_card (P₅ : Subgroup Q)
    rw [hk] at h5d hdQ ⊢
    rcases k with _ | _ | k
    · norm_num at h5d
    · simp
    · exfalso
      have h25 : 5 * 5 ∣ 5 * 2 ^ a := by
        have := (pow_dvd_pow 5 (by omega : 2 ≤ k + 2)).trans hdQ
        rwa [pow_two] at this
      have h5' : 5 ∣ 2 ^ a := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h25
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h5'
      norm_num at this
  have hidx : (P₅ : Subgroup Q).index = 2 ^ a := by
    have := (P₅ : Subgroup Q).card_mul_index
    rw [hP5, hcardQ] at this
    omega
  have hn5 : Nat.card (Sylow 5 Q) = 1 := by
    have hd : Nat.card (Sylow 5 Q) ∣ 8 :=
      (P₅.card_dvd_index.trans (hidx ▸ dvd_rfl)).trans (pow_dvd_pow 2 ha3)
    have hm := card_sylow_modEq_one 5 Q
    have hle : Nat.card (Sylow 5 Q) ≤ 8 := Nat.le_of_dvd (by norm_num) hd
    have hpos : 0 < Nat.card (Sylow 5 Q) := Nat.card_pos
    unfold Nat.ModEq at hm
    interval_cases h : Nat.card (Sylow 5 Q) <;> simp_all
  have : Subsingleton (Sylow 5 Q) := (Nat.card_eq_one_iff_unique.mp hn5).1
  have hP5n : (P₅ : Subgroup Q).Normal := P₅.normal_of_subsingleton
  have : IsCyclic P₅ := isCyclic_of_prime_card hP5
  obtain ⟨c₀, hc₀⟩ := IsCyclic.exists_generator (α := P₅)
  set c : Equiv.Perm (G ⧸ S) := ((c₀ : Q) : Equiv.Perm (G ⧸ S)) with hc
  have hc₀1 : c₀ ≠ 1 := by
    intro h
    have : ∀ x : P₅, x = 1 := fun x => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hc₀ x)
      rw [h, one_zpow]
    have h1 : Nat.card P₅ = 1 := Nat.card_eq_one_iff_unique.mpr ⟨⟨fun x y => by
      rw [this x, this y]⟩, ⟨1⟩⟩
    omega
  have hc5 : c ^ 5 = 1 := by
    have : c₀ ^ 5 = 1 := by
      have h := pow_card_eq_one' (G := P₅) (x := c₀)
      rwa [hP5] at h
    rw [hc]
    have := congrArg (fun x : P₅ => ((x : Q) : Equiv.Perm (G ⧸ S))) this
    simpa using this
  have hcne : c ≠ 1 := by
    intro h
    apply hc₀1
    apply Subtype.ext; apply Subtype.ext
    exact h
  have hconj : ∀ g : G, ∃ k : ℤ, φ g * c * (φ g)⁻¹ = c ^ k := by
    intro g
    have hmem : (⟨φ g, g, rfl⟩ : Q) * (c₀ : Q) * (⟨φ g, g, rfl⟩ : Q)⁻¹ ∈ (P₅ : Subgroup Q) :=
      hP5n.conj_mem _ c₀.2 _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hc₀ ⟨_, hmem⟩)
    refine ⟨k, ?_⟩
    have := congrArg (fun x : P₅ => ((x : Q) : Equiv.Perm (G ⧸ S))) hk
    simpa using this.symm
  set x₀ : G ⧸ S := ((1 : G) : G ⧸ S) with hx₀
  have hstab : ∀ g : G, φ g x₀ = x₀ ↔ g ∈ S := by
    intro g
    rw [hφ, MulAction.toPermHom_apply, MulAction.toPerm_apply, hx₀, MulAction.Quotient.smul_mk,
      smul_eq_mul, mul_one, QuotientGroup.eq, mul_one, inv_mem_iff]
  have hcx : c x₀ ≠ x₀ := by
    intro h
    obtain ⟨g, hg⟩ := (c₀ : Q).2
    have hgS : g ∈ S := (hstab g).mp (by rw [hg]; exact h)
    obtain ⟨m, hm⟩ := hS ⟨g, hgS⟩
    have hgm : g ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hcm : c ^ 2 ^ m = 1 := by rw [hc, ← hg, ← map_pow, hgm, map_one]
    have h1 : orderOf c = 5 := orderOf_eq_prime hc5 hcne
    have := orderOf_dvd_of_pow_eq_one hcm
    rw [h1] at this
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_five this
    norm_num at this
  have horb : ∀ y : G ⧸ S, ∃ k : ℤ, (c ^ k) x₀ = y := by
    set Z := Subgroup.zpowers c
    have hZ5 : Nat.card Z = 5 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hc5 hcne]
    have hcard := MulAction.index_stabilizer Z x₀
    have hdvd : (MulAction.stabilizer Z x₀).index ∣ 5 := hZ5 ▸ Subgroup.index_dvd_card _
    have hne1 : (MulAction.stabilizer Z x₀).index ≠ 1 := by
      intro h1
      rw [Subgroup.index_eq_one] at h1
      have : (⟨c, Subgroup.mem_zpowers c⟩ : Z) ∈ MulAction.stabilizer Z x₀ :=
        h1 ▸ Subgroup.mem_top _
      exact hcx (MulAction.mem_stabilizer_iff.mp this)
    have hidx5 : (MulAction.stabilizer Z x₀).index = 5 := by
      rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h | h
      · exact absurd h hne1
      · exact h
    have horbit : (MulAction.orbit Z x₀) = Set.univ := by
      apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
      rw [← hcard, hidx5, Set.ncard_univ, hΩ]
    intro y
    have hy : y ∈ MulAction.orbit Z x₀ := horbit ▸ Set.mem_univ y
    obtain ⟨⟨z, hz⟩, rfl⟩ := hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ⟨k, rfl⟩
  rw [hker.symm, Subgroup.commutator_le]
  have key : ∀ s ∈ S, ∀ t ∈ S, φ (s⁻¹ * t⁻¹ * s * t) * c = c * φ (s⁻¹ * t⁻¹ * s * t) := by
    intro s _ t _
    obtain ⟨i, hi⟩ := hconj s
    obtain ⟨j, hj⟩ := hconj t
    have hst : φ (s * t) * c * (φ (s * t))⁻¹ = c ^ (i * j) := by
      rw [map_mul, mul_inv_rev]
      calc φ s * φ t * c * ((φ t)⁻¹ * (φ s)⁻¹) = φ s * (φ t * c * (φ t)⁻¹) * (φ s)⁻¹ := by
            group
        _ = φ s * c ^ j * (φ s)⁻¹ := by rw [hj]
        _ = (φ s * c * (φ s)⁻¹) ^ j := conj_zpow.symm
        _ = c ^ (i * j) := by rw [hi, ← zpow_mul]
    have hts : φ (t * s) * c * (φ (t * s))⁻¹ = c ^ (i * j) := by
      rw [map_mul, mul_inv_rev]
      calc φ t * φ s * c * ((φ s)⁻¹ * (φ t)⁻¹) = φ t * (φ s * c * (φ s)⁻¹) * (φ t)⁻¹ := by
            group
        _ = φ t * c ^ i * (φ t)⁻¹ := by rw [hi]
        _ = (φ t * c * (φ t)⁻¹) ^ i := conj_zpow.symm
        _ = c ^ (i * j) := by rw [hj, ← zpow_mul, mul_comm]
    have e : s⁻¹ * t⁻¹ * s * t = (t * s)⁻¹ * (s * t) := by group
    rw [e, map_mul, map_inv]
    calc (φ (t * s))⁻¹ * φ (s * t) * c
        = (φ (t * s))⁻¹ * (φ (s * t) * c * (φ (s * t))⁻¹) * φ (s * t) := by group
      _ = (φ (t * s))⁻¹ * (φ (t * s) * c * (φ (t * s))⁻¹) * φ (s * t) := by rw [hst, hts]
      _ = c * ((φ (t * s))⁻¹ * φ (s * t)) := by group
  intro s hs t ht
  have hcomm : φ ⁅s, t⁆ * c = c * φ ⁅s, t⁆ := by
    have e : ⁅s, t⁆ = s⁻¹⁻¹ * t⁻¹⁻¹ * s⁻¹ * t⁻¹ := by rw [commutatorElement_def]; group
    rw [e]
    exact key _ (S.inv_mem hs) _ (S.inv_mem ht)
  have hfix : φ ⁅s, t⁆ x₀ = x₀ := (hstab _).mpr (by
    rw [commutatorElement_def]
    exact S.mul_mem (S.mul_mem (S.mul_mem hs ht) (S.inv_mem hs)) (S.inv_mem ht))
  exact (MonoidHom.mem_ker).mpr (eq_one_of_commute_of_orbit614 hcomm hfix horb)

theorem card_modEq_card_centralizer_five614 [Finite G] {X : Subgroup G} {p : G}
    (hp : p ^ 5 = 1) (hpX : p ∈ Subgroup.normalizer (X : Set G)) :
    Nat.card X ≡ Nat.card {x : X // p * x = x * p} [MOD 5] := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fintype X := Fintype.ofFinite X
  let f : Function.End X := fun x => ⟨p * x * p⁻¹, (Subgroup.mem_normalizer_iff.mp hpX x).mp x.2⟩
  have hfk : ∀ k : ℕ, ∀ x : X, ((f ^ k) x : G) = p ^ k * x * (p ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro x; simp; rfl
    | succ k ih =>
      intro x
      rw [pow_succ]
      show ((f ^ k) (f x) : G) = _
      rw [ih]
      show p ^ k * (p * x * p⁻¹) * (p ^ k)⁻¹ = p ^ (k + 1) * x * (p ^ (k + 1))⁻¹
      rw [pow_succ]
      group
  have hf5 : f ^ 5 ^ 1 = 1 := by
    funext x
    apply Subtype.ext
    rw [pow_one, hfk, hp]
    simp
    rfl
  have h := Equiv.Perm.card_fixedPoints_modEq (p := 5) (n := 1) hf5
  rw [Nat.card_eq_fintype_card]
  convert h using 1
  rw [Nat.card_eq_fintype_card]
  apply Fintype.card_congr
  refine Equiv.subtypeEquivRight fun x => ?_
  rw [Function.mem_fixedPoints, Function.IsFixedPt]
  constructor
  · intro hx
    apply Subtype.ext
    show p * x * p⁻¹ = x
    rw [hx, mul_inv_cancel_right]
  · intro hx
    have := congrArg Subtype.val hx
    change p * x * p⁻¹ = x at this
    calc p * x = p * x * p⁻¹ * p := by group
      _ = x * p := by rw [this]

theorem commutator_sup_le614 {U E : Subgroup G} (hE : E ≤ Subgroup.normalizer (U : Set G))
    (hab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) : ⁅U ⊔ E, U ⊔ E⁆ ≤ U := by
  set M := Subgroup.normalizer (U : Set G) with hM
  have hUM : U ≤ M := Subgroup.le_normalizer
  have hn : (U.subgroupOf M).Normal := Subgroup.normal_in_normalizer
  set π := QuotientGroup.mk' (U.subgroupOf M) with hπ
  have hπU : ∀ u (hu : u ∈ U), π ⟨u, hUM hu⟩ = 1 := fun u hu => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hu
  have hdecomp : ∀ x ∈ U ⊔ E, ∃ e, ∃ he : e ∈ E, ∃ hx : x ∈ M, π ⟨x, hx⟩ = π ⟨e, hE he⟩ := by
    intro x hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left U E hE] at hx
    obtain ⟨u, hu, e, he, rfl⟩ := hx
    refine ⟨e, he, M.mul_mem (hUM hu) (hE he), ?_⟩
    have : (⟨u * e, M.mul_mem (hUM hu) (hE he)⟩ : M) = ⟨u, hUM hu⟩ * ⟨e, hE he⟩ := rfl
    rw [this, map_mul, hπU u hu, one_mul]
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨e, he, hxM, hxe⟩ := hdecomp x hx
  obtain ⟨e', he', hyM, hye⟩ := hdecomp y hy
  have hc : ⁅x, y⁆ ∈ M := M.mul_mem (M.mul_mem (M.mul_mem hxM hyM) (M.inv_mem hxM)) (M.inv_mem hyM)
  have hπc : π ⟨⁅x, y⁆, hc⟩ = 1 := by
    have : (⟨⁅x, y⁆, hc⟩ : M) = ⁅(⟨x, hxM⟩ : M), (⟨y, hyM⟩ : M)⁆ := by
      apply Subtype.ext
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [this, map_commutatorElement, hxe, hye, ← map_commutatorElement]
    have hee : ⁅(⟨e, hE he⟩ : M), (⟨e', hE he'⟩ : M)⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact Subtype.ext (hab e he e' he')
    rw [hee, map_one]
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hπc
  exact hπc

theorem le_or_le_of_five614 [Finite G] {J E U : Subgroup G} {p z : G} (hEJ : E ≤ J)
    (hEc : E ≤ ⁅J, J⁆) (hJ : Nat.card J = 512) (hE : Nat.card E = 32)
    (hab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hp : p ^ 5 = 1)
    (hpE : p ∈ Subgroup.normalizer (E : Set G)) (hpU : p ∈ Subgroup.normalizer (U : Set G))
    (hUJ : U ≤ J) (hJU : J ≤ Subgroup.normalizer (U : Set G)) (hz : z ∈ E) (hz1 : z ≠ 1)
    (hzp : p * z = z * p) (hC : ∀ x ∈ J, p * x = x * p → x = 1 ∨ x = z) : U ≤ E ∨ J ≤ U := by
  classical
  set X := U ⊔ E with hX
  have hXJ : X ≤ J := sup_le hUJ hEJ
  have hpX : p ∈ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hpU hpE ⊢
    rw [Subgroup.map_sup, hpU, hpE]
  have hcount := card_modEq_card_centralizer_five614 hp hpX
  have hC2 : Nat.card {x : X // p * x = x * p} = 2 := by
    have e : {x : X // p * x = x * p} ≃ Fin 2 := by
      refine
        { toFun := fun x => if (x : X) = (1 : X) then 0 else 1
          invFun := fun i => if i = 0 then ⟨1, by simp⟩ else
            ⟨⟨z, Subgroup.mem_sup_right hz⟩, hzp⟩
          left_inv := ?_
          right_inv := ?_ }
      · rintro ⟨x, hx⟩
        rcases hC x (hXJ x.2) hx with h1 | h1
        · have : x = 1 := Subtype.ext h1
          subst this
          simp
        · have hx1 : x ≠ 1 := fun h => hz1 (by rw [← h1]; exact congrArg Subtype.val h)
          simp only [hx1, ↓reduceIte, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one]
          apply Subtype.ext; apply Subtype.ext
          exact h1.symm
      · intro i
        fin_cases i
        · simp
        · have : (⟨z, Subgroup.mem_sup_right hz⟩ : X) ≠ 1 := fun h =>
            hz1 (congrArg Subtype.val h)
          simp [this]
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [hC2] at hcount
  have hdvd : Nat.card X ∣ 2 ^ 9 := by
    rw [show (2 : ℕ) ^ 9 = 512 by norm_num, ← hJ]
    exact Subgroup.card_dvd_of_le hXJ
  obtain ⟨k, hk9, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hEX : E ≤ X := le_sup_right
  have h32 : 2 ^ 5 ∣ 2 ^ k := by
    rw [← hk, show (2 : ℕ) ^ 5 = 32 by norm_num, ← hE]
    exact Subgroup.card_dvd_of_le hEX
  have hk5 : 5 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h32
  rw [hk] at hcount
  unfold Nat.ModEq at hcount
  interval_cases k <;> norm_num at hcount
  ·
    left
    have : X = E := (Subgroup.eq_of_le_of_card_ge hEX (by rw [hk, hE]; norm_num)).symm
    exact this ▸ le_sup_left
  ·
    right
    have hXeq : X = J := Subgroup.eq_of_le_of_card_ge hXJ (by rw [hk, hJ]; norm_num)
    have hEN : E ≤ Subgroup.normalizer (U : Set G) := hEJ.trans hJU
    have hJ' : ⁅J, J⁆ ≤ U := hXeq ▸ commutator_sup_le614 hEN hab
    rw [← hXeq]
    exact sup_le le_rfl (hEc.trans hJ')

end CFSG.Quasithin.H13
