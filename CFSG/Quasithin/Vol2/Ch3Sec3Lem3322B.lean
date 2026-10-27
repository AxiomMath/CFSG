module

public import CFSG.Quasithin.H13.A7Nat1236Theta
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3317C

public section

namespace CFSG.Quasithin.H13.L3322

open Equiv Equiv.Perm
open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique hiding evenWeight
open CFSG.Quasithin.H13.A7 (IsCoordAct vec natLam)
open CFSG.Quasithin.SteinbergCB (permAct7 evenWeight sevenP)
open scoped IsMulCommutative

section Three

variable {Q : Type*} [Group Q] [Finite Q]

theorem exists_mul_pow_three_eq_one {C : Subgroup Q} (hC : C ≤ Subgroup.center Q)
    (h2 : ∀ c ∈ C, c * c = 1 → c = 1) {x y : Q} (hx3 : x ^ 3 ∈ C)
    (hxy : x * (y * x * y⁻¹) ∈ C) : ∃ w ∈ C, (x * w) ^ 3 = 1 := by
  set k := x * (y * x * y⁻¹) with hk
  have hn : Odd (orderOf k) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨m, hm⟩ := hev
    have hpos : 0 < orderOf k := orderOf_pos k
    have hsq : k ^ m * k ^ m = 1 := by rw [← pow_add, ← hm, pow_orderOf_eq_one]
    have h1 := h2 _ (C.pow_mem hxy m) hsq
    have := Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one h1)
    omega
  obtain ⟨j, hj⟩ := hn
  set w := k⁻¹ ^ (j + 1) with hw
  have hwC : w ∈ C := C.pow_mem (C.inv_mem hxy) _
  have hw2 : w * w = k⁻¹ := by
    rw [hw, ← pow_add, show j + 1 + (j + 1) = orderOf k + 1 by omega, pow_succ, inv_pow,
      pow_orderOf_eq_one, inv_one, one_mul]
  have hcen : ∀ c ∈ C, ∀ g : Q, g * c = c * g := fun c hc g =>
    Subgroup.mem_center_iff.1 (hC hc) g
  refine ⟨w, hwC, ?_⟩
  have hyx : y * x * y⁻¹ = x⁻¹ * k := by rw [hk]; group
  have h1 : y * (x * w) * y⁻¹ = (x * w)⁻¹ := by
    have hyw : y * w * y⁻¹ = w := by rw [hcen w hwC y, mul_inv_cancel_right]
    have hkw : k * w = w⁻¹ := by
      calc k * w = k * (w * w) * w⁻¹ := by group
        _ = k * k⁻¹ * w⁻¹ := by rw [hw2]
        _ = w⁻¹ := by group
    calc y * (x * w) * y⁻¹ = (y * x * y⁻¹) * (y * w * y⁻¹) := by group
      _ = x⁻¹ * (k * w) := by rw [hyx, hyw]; group
      _ = (w * x)⁻¹ := by rw [hkw]; group
      _ = (x * w)⁻¹ := by rw [hcen w hwC x]
  have hu : (x * w) ^ 3 ∈ C := by
    have : (x * w) ^ 3 = x ^ 3 * w ^ 3 := by
      have hxw : Commute x w := (hcen w hwC x)
      exact hxw.mul_pow 3
    rw [this]
    exact C.mul_mem hx3 (C.pow_mem hwC 3)
  have h3 : y * (x * w) ^ 3 * y⁻¹ = ((x * w) ^ 3)⁻¹ := by
    rw [← conj_pow, h1, inv_pow]
  have h4 : y * (x * w) ^ 3 * y⁻¹ = (x * w) ^ 3 := by
    rw [hcen _ hu y, mul_inv_cancel_right]
  rw [h4] at h3
  have h5 : (x * w) ^ 3 * (x * w) ^ 3 = 1 := by
    calc (x * w) ^ 3 * (x * w) ^ 3 = (x * w) ^ 3 * ((x * w) ^ 3)⁻¹ := by rw [← h3]
      _ = 1 := mul_inv_cancel _
  exact h2 _ hu h5

end Three

section Theta

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_ker_of_comm {X : Subgroup G} {S : Type*} [Group S] (φ : ↥X →* S)
    (hcen : ∀ x : ↥X, φ x = 1 → ∀ y : ↥X, x * y * x⁻¹ * y⁻¹ ∈ CFSG.pCore 2 ↥X) :
    Group.IsSolvable φ.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := φ.ker with hK
  set P := CFSG.pCore 2 ↥X with hP
  set π : ↥X →* ↥X ⧸ P := QuotientGroup.mk' P with hπ
  have hKc : ∀ a b : ↥(K.map π), a * b = b * a := by
    rintro ⟨_, a, ha, rfl⟩ ⟨_, b, -, rfl⟩
    apply Subtype.ext
    have h1 := hcen a (MonoidHom.mem_ker.1 ha) b
    have h2 : π (a * b * a⁻¹ * b⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 h1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    show π a * π b = π b * π a
    calc π a * π b = (π a * π b * (π a)⁻¹ * (π b)⁻¹) * (π b * π a) := by group
      _ = π b * π a := by rw [h2, one_mul]
  have : Group.IsSolvable ↥(K.map π) := Group.isSolvable_of_comm hKc
  have hP2 : IsPGroup 2 ↥(K ⊓ P) := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).to_le inf_le_right
  have : Group.IsNilpotent ↥(K ⊓ P) := hP2.isNilpotent
  let f : ↥(K ⊓ P) →* ↥K := Subgroup.inclusion inf_le_left
  let g : ↥K →* ↥(K.map π) := (π.comp K.subtype).codRestrict (K.map π) fun k => ⟨k, k.2, rfl⟩
  refine Group.isSolvable_of_ker_le_range f g fun k hk => ?_
  have hk1 : π (k : ↥X) = 1 := congrArg Subtype.val hk
  have hkP : (k : ↥X) ∈ P := (QuotientGroup.eq_one_iff _).1 hk1
  exact ⟨⟨k, k.2, hkP⟩, rfl⟩

theorem exists_orderOf_three_map {X : Subgroup G} {S : Type*} [Group S] (φ : ↥X →* S)
    (hcen : ∀ x : ↥X, φ x = 1 → ∀ y : ↥X, x * y * x⁻¹ * y⁻¹ ∈ CFSG.pCore 2 ↥X)
    {σ τ : S} (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) (hτσ : τ * σ * τ⁻¹ = σ⁻¹) (hσX : σ ∈ φ.range)
    (hτX : τ ∈ φ.range) : ∃ z : ↥X, orderOf z = 3 ∧ φ z ≠ 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.pCore 2 ↥X with hP
  set π : ↥X →* ↥X ⧸ P := QuotientGroup.mk' P with hπ
  set C := φ.ker.map π with hC
  have hCc : C ≤ Subgroup.center (↥X ⧸ P) := by
    rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective P q
    have h1 := hcen c hc y
    have h2 : π (c * y * c⁻¹ * y⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 h1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    calc π y * π c = (π c * π y * (π c)⁻¹ * (π y)⁻¹)⁻¹ * (π c * π y) := by group
      _ = π c * π y := by rw [h2, inv_one, one_mul]
  have hC2 : ∀ c ∈ C, c * c = 1 → c = 1 := by
    intro c hc hcc
    have hZ : Subgroup.zpowers c ≤ Subgroup.center (↥X ⧸ P) :=
      (Subgroup.zpowers_le).2 (hCc hc)
    have hp : IsPGroup 2 (Subgroup.zpowers c) := by
      rintro ⟨g, hg⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      refine ⟨1, Subtype.ext ?_⟩
      simp only [pow_one, SubmonoidClass.coe_pow, OneMemClass.coe_one]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_two, hcc, one_zpow]
    have hle : Subgroup.zpowers c ≤ CFSG.pCore 2 (↥X ⧸ P) :=
      le_sSup ⟨Subgroup.normal_of_le_center hZ, hp⟩
    rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot] at hle
    have := hle (Subgroup.mem_zpowers c)
    rwa [Subgroup.mem_bot] at this
  obtain ⟨x, hx⟩ := hσX
  obtain ⟨y, hy⟩ := hτX
  have hx3 : π x ^ 3 ∈ C := ⟨x ^ 3, SetLike.mem_coe.2 (MonoidHom.mem_ker.2 (by
    rw [map_pow, hx, hσ3])), by rw [map_pow]⟩
  have hxy : π x * (π y * π x * (π y)⁻¹) ∈ C := ⟨x * (y * x * y⁻¹),
    SetLike.mem_coe.2 (MonoidHom.mem_ker.2 (by
      rw [map_mul, map_mul, map_mul, map_inv, hx, hy, hτσ, mul_inv_cancel])), by
    rw [map_mul, map_mul, map_mul, map_inv]⟩
  obtain ⟨w, hwC, hw3⟩ := exists_mul_pow_three_eq_one hCc hC2 hx3 hxy
  obtain ⟨k, hk, rfl⟩ := hwC
  have hP3 : (x * k) ^ 3 ∈ P := by
    rw [← QuotientGroup.eq_one_iff]
    rw [← map_mul] at hw3
    rw [← map_pow] at hw3
    exact hw3
  obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup ⟨_, hP3⟩
  have hn' : ((x * k) ^ 3) ^ 2 ^ n = 1 := congrArg Subtype.val hn
  have hφ : φ ((x * k) ^ 2 ^ n) ≠ 1 := by
    rw [map_pow, map_mul, hx, MonoidHom.mem_ker.1 hk, mul_one]
    intro h1
    have hd := orderOf_dvd_of_pow_eq_one h1
    have h3 : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
    rw [h3] at hd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd) (by norm_num)
  refine ⟨(x * k) ^ 2 ^ n, ?_, hφ⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← pow_mul, mul_comm, pow_mul, hn']
  · intro h1
    rw [h1, map_one] at hφ
    exact hφ rfl

theorem le_thetaOf_of_map {X : Subgroup G} (hX : ⁅X, X⁆ = X) {S : Type*} [Group S]
    (φ : ↥X →* S) (hcen : ∀ x : ↥X, φ x = 1 → ∀ y : ↥X, x * y * x⁻¹ * y⁻¹ ∈ CFSG.pCore 2 ↥X)
    (hs : IsSimpleGroup φ.range) {z : ↥X} (hz3 : orderOf z = 3) (hz1 : φ z ≠ 1) :
    X ≤ thetaOf X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W' : Subgroup ↥X := (thetaOf X).subgroupOf X with hW'
  have hWn : W'.Normal := ⟨fun w hw g => by
    rw [hW', Subgroup.mem_subgroupOf] at hw ⊢
    show (g : G) * (w : G) * (g : G)⁻¹ ∈ thetaOf X
    exact A7.conj_mem_theta (Subgroup.le_normalizer g.2) hw⟩
  set ρ := φ.rangeRestrict with hρ
  have hρs : Function.Surjective ρ := φ.rangeRestrict_surjective
  have hN : (W'.map ρ).Normal := hWn.map ρ hρs
  have hzW : z ∈ W' := by
    rw [hW', Subgroup.mem_subgroupOf]
    exact Subgroup.subset_closure ⟨z.2, by rw [Subgroup.orderOf_coe]; exact hz3⟩
  have htop : W'.map ρ = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (W'.map ρ) with h | h
    · exfalso
      have : ρ z ∈ W'.map ρ := Subgroup.mem_map_of_mem ρ hzW
      rw [h, Subgroup.mem_bot] at this
      exact hz1 (congrArg Subtype.val this)
    · exact h
  have hks := isSolvable_ker_of_comm φ hcen
  have hsurj : Function.Surjective ((QuotientGroup.mk' W').comp φ.ker.subtype) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective W' q
    have : ρ g ∈ W'.map ρ := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨w, hw, hwg⟩ := this
    refine ⟨⟨w⁻¹ * g, ?_⟩, ?_⟩
    · rw [MonoidHom.mem_ker]
      have := congrArg Subtype.val hwg
      simp only [hρ, MonoidHom.coe_rangeRestrict] at this
      rw [map_mul, map_inv, this, inv_mul_cancel]
    · show (QuotientGroup.mk (w⁻¹ * g) : ↥X ⧸ W') = QuotientGroup.mk g
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, (QuotientGroup.eq_one_iff w).2 hw, inv_one,
        one_mul]
  have hsol : Group.IsSolvable (↥X ⧸ W') := Group.isSolvable_of_surjective hsurj
  have hperf : Group.IsPerfect ↥X := (Subgroup.isPerfect_iff).2 hX
  have htop' : W' = ⊤ := by
    by_contra hne
    have : Nontrivial (↥X ⧸ W') := QuotientGroup.nontrivial_iff.2 hne
    exact Group.IsPerfect.not_isSolvable (G := ↥X ⧸ W') hsol
  intro x hx
  have : (⟨x, hx⟩ : ↥X) ∈ W' := by rw [htop']; exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.1 this

omit [Finite G] in
theorem map_thetaOf_le (X : Subgroup G) (f : G →* G) (hf : Function.Injective f) :
    (thetaOf X).map f ≤ thetaOf (X.map f) := by
  rw [thetaOf, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨x, ⟨hx, hx3⟩, rfl⟩
  exact ⟨Subgroup.mem_map_of_mem f hx, by rw [orderOf_injective f hf]; exact hx3⟩

end Theta

section Kernel

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem range_comp_inclusion {X L : Subgroup G} (hXL : X ≤ L) {S : Type*} [Group S]
    (f : ↥L →* S) : (f.comp (Subgroup.inclusion hXL)).range = (X.subgroupOf L).map f := by
  rw [MonoidHom.range_comp]
  congr 1
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact Subgroup.mem_subgroupOf.2 y.2
  · intro hx
    exact ⟨⟨x, Subgroup.mem_subgroupOf.1 hx⟩, rfl⟩

omit [Finite G] in
theorem mul_mem_pCore_of_le {X L : Subgroup G} (hXL : X ≤ L) {S : Type*} [Group S]
    (f : ↥L →* S) (hf : ∀ x : ↥L, f x = 1 → ∀ y : ↥L, x * y * x⁻¹ * y⁻¹ ∈ CFSG.pCore 2 ↥L) :
    ∀ x : ↥X, (f.comp (Subgroup.inclusion hXL)) x = 1 → ∀ y : ↥X,
      x * y * x⁻¹ * y⁻¹ ∈ CFSG.pCore 2 ↥X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx y
  have hle : (CFSG.pCore 2 ↥L).comap (Subgroup.inclusion hXL) ≤ CFSG.pCore 2 ↥X :=
    le_sSup ⟨CFSG.pCore_normal.comap _, CFSG.pCore_isPGroup.comap_of_injective _
      (Subgroup.inclusion_injective hXL)⟩
  apply hle
  rw [Subgroup.mem_comap, map_mul, map_mul, map_mul, map_inv, map_inv]
  exact hf _ hx _

variable {L V : Subgroup G} {ψ : V ≃* Multiplicative (evenWeight 7)}

omit [Finite G] in
theorem mul_mem_pCore_of_natLam_eq_one (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hLact : ∀ l ∈ L, ∃ σ ∈ alternatingGroup (Fin 7), IsCoordAct ψ l σ)
    (hLonto : ∀ σ ∈ alternatingGroup (Fin 7), ∃ l ∈ L, IsCoordAct ψ l σ)
    (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (x : ↥L) (hx : natLam hLV hLact x = 1)
    (y : ↥L) : x * y * x⁻¹ * y⁻¹ ∈ CFSG.pCore 2 ↥L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set lam := natLam hLV hLact with hlam
  have hlams := A7.natLam_surjective hLV hLact hLonto
  set π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hA7s : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
  have hF1 : CFSG.pCore 2 ↥L ≤ lam.ker := by
    rw [← Subgroup.map_eq_bot_iff]
    have hN : ((CFSG.pCore 2 ↥L).map lam).Normal := CFSG.pCore_normal.map lam hlams
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hA7s _ hN with h | h
    · exact h
    · exfalso
      have h2 : IsPGroup 2 ((CFSG.pCore 2 ↥L).map lam) := CFSG.pCore_isPGroup.map lam
      rw [h] at h2
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
      rw [Subgroup.card_top, A7.coord_card_alternating_seven] at hk
      have h3 : 3 ∣ 2 ^ k := by rw [← hk]; norm_num
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  set lam' : (↥L ⧸ CFSG.pCore 2 ↥L) →* alternatingGroup (Fin 7) :=
    QuotientGroup.lift _ lam hF1 with hlam'
  have hlam's : Function.Surjective lam' := fun a => by
    obtain ⟨l, rfl⟩ := hlams a
    exact ⟨π l, rfl⟩
  have hK : lam'.ker ≤ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq lam'.normal_ker with h | h
    · exfalso
      have h1 : ∀ a, a = (1 : alternatingGroup (Fin 7)) := by
        intro a
        obtain ⟨x, rfl⟩ := hlam's a
        exact (MonoidHom.mem_ker).1 (h ▸ Subgroup.mem_top x)
      have h2 : Nat.card (alternatingGroup (Fin 7)) = 1 :=
        Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => (h1 a).trans (h1 b).symm⟩, inferInstance⟩
      rw [A7.coord_card_alternating_seven] at h2
      norm_num at h2
    · exact h
  have hxc : π x ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := hK (show lam' (π x) = 1 from hx)
  have h1 : π (x * y * x⁻¹ * y⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← Subgroup.mem_center_iff.1 hxc (π y)]
    group
  exact (QuotientGroup.eq_one_iff _).1 h1

end Kernel

section ThetaL

variable {G : Type} [Group G] [Finite G]

@[expose] def tau0134 : Perm (Fin 7) := swap 0 1 * swap 3 4

theorem tau0134_mem : tau0134 ∈ alternatingGroup (Fin 7) := by
  rw [mem_alternatingGroup]
  decide

theorem tau0134_mem_altFive :
    (⟨tau0134, tau0134_mem⟩ : alternatingGroup (Fin 7)) ∈ A7.altFive := by
  rw [A7.mem_altFive]
  decide

theorem cyc012_facts :
    (⟨L3317.cyc012, L3317.cyc012_mem⟩ : alternatingGroup (Fin 7)) ^ 3 = 1 ∧
      (⟨L3317.cyc012, L3317.cyc012_mem⟩ : alternatingGroup (Fin 7)) ≠ 1 ∧
      (⟨tau0134, tau0134_mem⟩ : alternatingGroup (Fin 7)) *
          ⟨L3317.cyc012, L3317.cyc012_mem⟩ * (⟨tau0134, tau0134_mem⟩)⁻¹ =
        (⟨L3317.cyc012, L3317.cyc012_mem⟩)⁻¹ := by
  refine ⟨Subtype.ext ?_, fun h => ?_, Subtype.ext ?_⟩
  · decide
  · have := congrArg Subtype.val h
    exact absurd this (by decide)
  · decide

theorem le_thetaOf_of_altFive_le {X L : Subgroup G} (hXL : X ≤ L) (hX : ⁅X, X⁆ = X)
    (f : ↥L →* alternatingGroup (Fin 7))
    (hf : ∀ x : ↥L, f x = 1 → ∀ y : ↥L, x * y * x⁻¹ * y⁻¹ ∈ CFSG.pCore 2 ↥L)
    (hs : IsSimpleGroup ↥((X.subgroupOf L).map f)) (h5 : A7.altFive ≤ (X.subgroupOf L).map f) :
    X ≤ thetaOf X := by
  set φ := f.comp (Subgroup.inclusion hXL) with hφ
  have hr : φ.range = (X.subgroupOf L).map f := range_comp_inclusion hXL f
  have hcen := mul_mem_pCore_of_le hXL f hf
  obtain ⟨h3, h1, hτ⟩ := cyc012_facts
  have hσ : (⟨L3317.cyc012, L3317.cyc012_mem⟩ : alternatingGroup (Fin 7)) ∈ φ.range :=
    hr ▸ h5 L3317.cyc012_mem_altFive
  have hτ' : (⟨tau0134, tau0134_mem⟩ : alternatingGroup (Fin 7)) ∈ φ.range :=
    hr ▸ h5 tau0134_mem_altFive
  obtain ⟨z, hz3, hz1⟩ := exists_orderOf_three_map φ hcen h3 h1 hτ hσ hτ'
  have hs' : IsSimpleGroup φ.range := by rw [hr]; exact hs
  exact le_thetaOf_of_map hX φ hcen hs' hz3 hz1

end ThetaL

end CFSG.Quasithin.H13.L3322
