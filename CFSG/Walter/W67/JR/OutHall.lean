module

public import CFSG.GroupTheory.SolvableHallNodes

public section

namespace CFSG.Walter.W67

namespace JROut

open scoped Pointwise

theorem mul_comm_of_mem {G : Type*} [Group G] {S : Subgroup G} [hS : IsMulCommutative S]
    {a b : G} (ha : a ∈ S) (hb : b ∈ S) : a * b = b * a :=
  congrArg Subtype.val (hS.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem exists_mul_of_mem_sup {G : Type*} [Group G] {N H : Subgroup G} [N.Normal] {x : G}
    (hx : x ∈ N ⊔ H) : ∃ n ∈ N, ∃ h ∈ H, n * h = x := by
  have hx' : x ∈ ((N ⊔ H : Subgroup G) : Set G) := hx
  rw [Subgroup.normal_mul] at hx'
  obtain ⟨n, hn, h, hh, rfl⟩ := hx'
  exact ⟨n, hn, h, hh, rfl⟩

theorem exists_conj_of_fix {X : Type*} [Group X] [Finite X] (S : Subgroup X) [hSn : S.Normal]
    [IsMulCommutative S] (hcop : Nat.Coprime (Nat.card S) S.index)
    (hC : ∀ x : X, (∀ s ∈ S, x * s * x⁻¹ = s) → x ∈ S)
    (φ : X →* X) (hφ : Function.Injective φ) (hφS : ∀ s ∈ S, φ s = s) :
    ∃ t ∈ S, ∀ x, φ x = t * x * t⁻¹ := by
  obtain ⟨D, hD⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hsup : S ⊔ D = ⊤ := hD.sup_eq_top
  have hinf : S ⊓ D = ⊥ := disjoint_iff.mp hD.disjoint
  set D' := D.map φ with hD'
  have hφsurj : Function.Surjective φ := Finite.injective_iff_surjective.mp hφ
  have hSmap : S.map φ = S := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      rw [hφS s hs]
      exact hs
    · intro hx
      exact ⟨x, hx, hφS x hx⟩
  have hsup' : S ⊔ D' = ⊤ := by
    rw [hD', ← hSmap, ← Subgroup.map_sup, hsup, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top]
    exact hφsurj
  have hinf' : S ⊓ D' = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨hs, ⟨d, hd, rfl⟩⟩
    have hdd : φ d = d := hφ (hφS _ hs)
    have hdS : d ∈ S := hdd ▸ hs
    have hd1 : d ∈ S ⊓ D := ⟨hdS, hd⟩
    rw [hinf, Subgroup.mem_bot] at hd1
    rw [hd1, map_one]
    exact Subgroup.one_mem _
  have hmul : ∀ H : Subgroup X, S ⊔ H = ⊤ → (S : Set X) * (H : Set X) = Set.univ := by
    intro H hH
    rw [← Subgroup.normal_mul, hH, Subgroup.coe_top]
  obtain ⟨n, hn, hn'⟩ := CFSG.SolvableHall.abelian_normal_hall_complement_conjugacy S hcop
    (hmul D hsup) (hmul D' hsup') hinf hinf'
  have hγD : ∀ d ∈ D, n * φ d * n⁻¹ ∈ D := by
    intro d hd
    have hφd : φ d ∈ D' := ⟨d, hd, rfl⟩
    rw [hn'] at hφd
    obtain ⟨d₂, hd₂, he⟩ := hφd
    have he' : φ d = n⁻¹ * d₂ * n := by
      rw [← he]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have h1 : n * (n⁻¹ * d₂ * n) * n⁻¹ = d₂ := by group
    rw [he', h1]
    exact hd₂
  have hγS : ∀ s ∈ S, n * φ s * n⁻¹ = s := by
    intro s hs
    rw [hφS s hs, mul_comm_of_mem hn hs, mul_inv_cancel_right]
  have hγd : ∀ d ∈ D, n * φ d * n⁻¹ = d := by
    intro d hd
    set e := d⁻¹ * (n * φ d * n⁻¹) with he
    have heD : e ∈ D := D.mul_mem (D.inv_mem hd) (hγD d hd)
    have heS : e ∈ S := hC e fun s hs => by
      have h1 : n * φ (d * s * d⁻¹) * n⁻¹ = d * s * d⁻¹ := hγS _ (hSn.conj_mem s hs d)
      have h2 : n * φ (d * s * d⁻¹) * n⁻¹ =
          (n * φ d * n⁻¹) * (n * φ s * n⁻¹) * (n * φ d * n⁻¹)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
        group
      rw [hγS s hs, h1] at h2
      calc e * s * e⁻¹ = d⁻¹ * ((n * φ d * n⁻¹) * s * (n * φ d * n⁻¹)⁻¹) * d := by
            rw [he]
            group
        _ = d⁻¹ * (d * s * d⁻¹) * d := by rw [← h2]
        _ = s := by group
    have he1 : e ∈ S ⊓ D := ⟨heS, heD⟩
    rw [hinf, Subgroup.mem_bot, he, inv_mul_eq_one] at he1
    exact he1.symm
  have hγ : ∀ x, n * φ x * n⁻¹ = x := by
    intro x
    obtain ⟨s, hs, d, hd, rfl⟩ := exists_mul_of_mem_sup (hsup ▸ Subgroup.mem_top x :
      x ∈ S ⊔ D)
    have h1 : n * φ (s * d) * n⁻¹ = (n * φ s * n⁻¹) * (n * φ d * n⁻¹) := by
      rw [map_mul]
      group
    rw [h1, hγS s hs, hγd d hd]
  refine ⟨n⁻¹, S.inv_mem hn, fun x => ?_⟩
  calc φ x = n⁻¹ * (n * φ x * n⁻¹) * n := by group
    _ = n⁻¹ * x * n⁻¹⁻¹ := by rw [hγ x, inv_inv]

theorem exists_conj_on_normalizer {G : Type*} [Group G] [Finite G] {S : Subgroup G}
    [hSc : IsMulCommutative S]
    (hcop : Nat.Coprime (Nat.card S) (S.subgroupOf (Subgroup.normalizer (S : Set G))).index)
    (hC : Subgroup.centralizer (S : Set G) ≤ S) (β : MulAut G) (hβS : ∀ s ∈ S, β s = s) :
    ∃ t ∈ S, ∀ x ∈ Subgroup.normalizer (S : Set G), β x = t * x * t⁻¹ := by
  set N := Subgroup.normalizer (S : Set G) with hN
  have hmem : ∀ y, y ∈ S ↔ β y ∈ S := by
    intro y
    constructor
    · intro hy
      rw [hβS y hy]
      exact hy
    · intro hy
      have : β y = y := β.injective (hβS _ hy)
      exact this ▸ hy
  have hβN : ∀ x ∈ N, β x ∈ N := by
    intro x hx
    rw [hN, Subgroup.mem_normalizer_iff] at hx ⊢
    intro y
    obtain ⟨y', rfl⟩ := β.surjective y
    rw [← map_inv, ← map_mul, ← map_mul, ← hmem, ← hmem]
    exact hx y'
  let φ : N →* N :=
    { toFun := fun x => ⟨β (x : G), hβN x x.2⟩
      map_one' := Subtype.ext (map_one β)
      map_mul' := fun x y => Subtype.ext (map_mul β (x : G) (y : G)) }
  have hφ : ∀ x : N, ((φ x : N) : G) = β (x : G) := fun x => rfl
  have hSN : S ≤ N := Subgroup.le_normalizer
  set S' := S.subgroupOf N with hS'
  have : S'.Normal := Subgroup.normal_in_normalizer
  have : IsMulCommutative S' :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext (mul_comm_of_mem (S := S) a.2 b.2))⟩⟩
  have hcard : Nat.card S' = Nat.card S := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv
  obtain ⟨t, ht, hφt⟩ := exists_conj_of_fix S' (by rw [hcard]; exact hcop)
    (fun x hx => by
      have hxC : (x : G) ∈ Subgroup.centralizer (S : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        have h1 := congrArg (fun y : N => (y : G)) (hx ⟨s, hSN hs⟩ hs)
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
        calc s * x = (x * s * (x : G)⁻¹) * x := by rw [h1]
          _ = x * s := by group
      exact hC hxC)
    φ (fun a b hab => Subtype.ext (β.injective (congrArg Subtype.val hab)))
    (fun s hs => Subtype.ext (hβS _ hs))
  refine ⟨t, ht, fun x hx => ?_⟩
  have := congrArg Subtype.val (hφt ⟨x, hx⟩)
  rw [hφ] at this
  simpa using this

end JROut

end CFSG.Walter.W67
