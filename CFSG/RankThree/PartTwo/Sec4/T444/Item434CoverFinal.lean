module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CoverKit
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CoverLift

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434Cover

open CFSG CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
open Item434Kit Item434Alt
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

structure LiftData (X : Type*) [Group X] where
  n : ℕ
  m : ℕ
  x : Fin n → X
  g : Fin m → X
  M : Fin m → Fin n → Fin n → ℕ
  k₀ : Fin n
  l₀ : Fin n
  cs : Fin n → Fin n → List (ℕ × ℕ)
  cs' : Fin n → List (ℕ × ℕ)
  hx3 : ∀ i, x i ^ 3 = 1
  hxc : ∀ i j, x i * x j = x j * x i
  hrel : ∀ j i, g j * x i * (g j)⁻¹ = (List.ofFn fun k => x k ^ M j k i).prod
  hlin : ∀ k l, Pi.single (k, l) 1 =
    ((cs k l).map fun p => p.1 • (pairingRelations M).getD p.2 0).sum
  hlin' : ∀ i, Pi.single i 1 = ((cs' i).map fun p => p.1 • (cubeRelations M).getD p.2 0).sum
  hx27 : 27 ≤ Nat.card (Subgroup.closure (Set.range x))

namespace LiftData

variable {X : Type*} [Group X]

def conj (d : LiftData X) (h : X) : LiftData X where
  n := d.n
  m := d.m
  x i := h⁻¹ * d.x i * h
  g j := h⁻¹ * d.g j * h
  M := d.M
  k₀ := d.k₀
  l₀ := d.l₀
  cs := d.cs
  cs' := d.cs'
  hx3 i := by
    have e : (h⁻¹ * d.x i * h) ^ 3 = h⁻¹ * d.x i ^ 3 * h := by
      have := conj_pow (a := h⁻¹) (b := d.x i) (i := 3)
      rwa [inv_inv] at this
    rw [e, d.hx3 i]
    group
  hxc i j := by
    have e := d.hxc i j
    calc h⁻¹ * d.x i * h * (h⁻¹ * d.x j * h) = h⁻¹ * (d.x i * d.x j) * h := by group
      _ = h⁻¹ * (d.x j * d.x i) * h := by rw [e]
      _ = h⁻¹ * d.x j * h * (h⁻¹ * d.x i * h) := by group
  hrel j i := by
    set φ : X →* X := (MulAut.conj h⁻¹).toMonoidHom with hφdef
    have hφ : ∀ y, φ y = h⁻¹ * y * h := fun y => by simp [hφdef]
    have h1 := congrArg φ (d.hrel j i)
    rw [map_mul, map_mul, map_inv, map_list_prod, List.map_ofFn] at h1
    rw [show (⇑φ ∘ fun k => d.x k ^ d.M j k i) = fun k => (h⁻¹ * d.x k * h) ^ d.M j k i from by
      funext k
      simp only [Function.comp_apply]
      rw [map_pow, hφ]] at h1
    simp only [hφ] at h1
    exact h1
  hlin := d.hlin
  hlin' := d.hlin'
  hx27 := by
    set φ : X →* X := (MulAut.conj h⁻¹).toMonoidHom with hφdef
    have hφ : ∀ y, φ y = h⁻¹ * y * h := fun y => by simp [hφdef]
    have hmap : Subgroup.closure (Set.range fun i => h⁻¹ * d.x i * h) =
        (Subgroup.closure (Set.range d.x)).map φ := by
      rw [MonoidHom.map_closure, ← Set.range_comp]
      congr 2
      funext i
      simp [hφ]
    rw [hmap, Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective]
    exact d.hx27

theorem conj_x_mem_centralizer (d : LiftData X) (h u : X)
    (hx : ∀ i, d.x i ∈ Subgroup.centralizer ({h * u * h⁻¹} : Set X)) :
    ∀ i, (d.conj h).x i ∈ Subgroup.centralizer ({u} : Set X) := by
  intro i
  have hxi := Subgroup.mem_centralizer_singleton_iff.mp (hx i)
  rw [Subgroup.mem_centralizer_singleton_iff]
  change h⁻¹ * d.x i * h * u = u * (h⁻¹ * d.x i * h)
  have h2 : d.x i * (h * u * h⁻¹) = (h * u * h⁻¹) * d.x i := hxi
  calc h⁻¹ * d.x i * h * u = h⁻¹ * (d.x i * (h * u * h⁻¹)) * h := by group
    _ = h⁻¹ * ((h * u * h⁻¹) * d.x i) * h := by rw [h2]
    _ = u * (h⁻¹ * d.x i * h) := by group

end LiftData

section Cover

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G} {X : Type*} [Group X] [Finite X]

theorem false_of_cover (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) (hcen : Subgroup.center X = ⊥)
    (hout : ¬ 3 ∣ Nat.card (Outer X)) (hZ : Subgroup.center (layer G) ≠ ⊥)
    (hX : ∀ U : Subgroup X, CFSG.Assembly.IsElemAbelian 3 U → Nat.card U = 9 →
      ∃ u ∈ U, u ≠ 1 ∧ ∃ d : LiftData X, ∀ i, d.x i ∈ Subgroup.centralizer ({u} : Set X)) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h9 : Nat.card h.layerStar = 9 := by
    rcases h.card_layerStar with h9 | ⟨-, hZ'⟩
    · exact h9
    · exact absurd hZ' hZ
  have hC3 : Nat.card (A ⊓ Subgroup.centralizer (layer G : Set G) : Subgroup G) = 3 := by
    have h1 := h.card_inf_mul_card_layerStar
    rw [h9] at h1
    omega
  set P := (A.map (quotConj e)).comap (MulAut.conj : X →* MulAut X) with hP
  have hPmap : P.map MulAut.conj = A.map (quotConj e) := map_comap_conj_eq h e hout
  have hinj := conj_injective_of_center_eq_bot hcen
  have hAmap : Nat.card (A.map (quotConj e)) = 9 := by
    rw [card_map_quotConj_eq h e]
    exact h9
  have hP9 : Nat.card P = 9 := by
    rw [← Subgroup.card_map_of_injective hinj, hPmap, hAmap]
  have hPe : CFSG.Assembly.IsElemAbelian 3 P :=
    isElemAbelian_of_map_injective hinj (hPmap ▸ isElemAbelian_map_quotConj h e)
  have hinn : A.map (quotConj e) ≤ (MulAut.conj : X →* MulAut X).range := by
    rw [← hPmap]
    exact Subgroup.map_le_range _ _
  obtain ⟨u, huP, hu1, d, hd⟩ := hX P hPe hP9
  have hu : (MulAut.conj : X →* MulAut X) u ∈ A.map (quotConj e) := by
    rw [← hPmap]
    exact ⟨u, huP, rfl⟩
  have hZp : IsPGroup 3 (Subgroup.center (layer G)) := h.isPGroup_center_layer
  have hZnt : Nontrivial (Subgroup.center (layer G)) := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    exact hZ
  have hdvd : 3 ∣ Nat.card (Subgroup.center (layer G)) := by
    obtain ⟨k, hk⟩ := hZp.exists_card_eq
    rcases k with _ | k
    · exfalso
      have : Nat.card (Subgroup.center (layer G)) = 1 := by simpa using hk
      exact (Subgroup.card_eq_one.mp this ▸ hZ) rfl |>.elim
    · rw [hk]
      exact dvd_pow_self 3 (Nat.succ_ne_zero k)
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center (layer G)) 3 hdvd
  have hc3 : (c : layer G) ^ 3 = 1 := by
    have := pow_orderOf_eq_one c
    rw [hc] at this
    exact congrArg Subtype.val this
  have hc1 : (c : layer G) ≠ 1 := by
    intro h1
    have : c = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hc
    omega
  have hcker : (c : layer G) ∈ (layerQuot e).ker := by
    rw [ker_layerQuot]
    exact c.2
  obtain ⟨E, hE, hE81, hEπ⟩ := exists_elemAbelian_lift (π := layerQuot e) (layerQuot_surjective e)
    (le_of_eq (ker_layerQuot e)) d.x d.hx3 d.hxc d.g d.M d.hrel d.k₀ d.l₀ d.cs d.hlin d.cs'
    d.hlin' d.hx27 hcker hc1 hc3
  refine false_of_lift h e hcen hinn hC3 hu1 hu hE hE81 fun y hy => ?_
  have hmem := hEπ y hy
  have hle : Subgroup.closure (Set.range d.x) ≤ Subgroup.centralizer ({u} : Set X) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact hd i
  exact hle hmem

end Cover

section Sylow

theorem ne_one_of_mem_four {J : Type*} [Group J] {a b t : J} (hb3 : b ^ 3 = 1) (ha1 : a ≠ 1)
    (hbz : b ∉ Subgroup.zpowers a) (ht : t ∈ ({a, b, a * b, a * b ^ 2} : Set J)) : t ≠ 1 := by
  intro ht1
  rcases ht with rfl | rfl | rfl | rfl
  · exact ha1 ht1
  · exact hbz (by rw [ht1]; exact Subgroup.one_mem _)
  · apply hbz
    rw [eq_inv_of_mul_eq_one_right ht1]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  · apply hbz
    have hb2 : b ^ 2 = a⁻¹ := by
      have : a * b ^ 2 = 1 := ht1
      exact eq_inv_of_mul_eq_one_right this
    have : b = (b ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 4 by norm_num, pow_succ _ 3, hb3, one_mul]
    rw [this, hb2]
    exact Subgroup.pow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)) 2

variable {J : Type*} [Group J] [Finite J]

theorem exists_lift_of_cover (S : Subgroup J)
    (hS : Nat.card S = 3 ^ (Nat.card J).factorization 3)
    (hcover : ∀ a ∈ S, ∀ b ∈ S, a ≠ 1 → a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a →
      b ∉ Subgroup.zpowers a → ∃ t ∈ ({a, b, a * b, a * b ^ 2} : Set J),
        ∃ h : J, ∃ z' ∈ S, (∀ q ∈ S, q * z' = z' * q) ∧ h * t * h⁻¹ = z')
    (d₀ : LiftData J) (hd₀ : ∀ i, d₀.x i ∈ S) (U : Subgroup J)
    (hU : CFSG.Assembly.IsElemAbelian 3 U) (hU9 : Nat.card U = 9) :
    ∃ u ∈ U, u ≠ 1 ∧ ∃ d : LiftData J, ∀ i, d.x i ∈ Subgroup.centralizer ({u} : Set J) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hUp : IsPGroup 3 U := IsPGroup.of_card (n := 2) (by rw [hU9]; norm_num)
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card hS hUp
  have hU'S : U.map (MulAut.conj g⁻¹).toMonoidHom ≤ S := Item434AltPerm.map_conj_inv_le hg
  have hUcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hU.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hUne : U ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hU9
    omega
  obtain ⟨⟨a, haU⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hUne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have ha3 : a ^ 3 = 1 := hU.2 a haU
  have hord : orderOf a = 3 := orderOf_eq_prime ha3 ha1'
  obtain ⟨b, hbU, hbz⟩ : ∃ b ∈ U, b ∉ Subgroup.zpowers a := by
    by_contra hall
    push Not at hall
    have := Subgroup.card_le_of_le (show U ≤ Subgroup.zpowers a from fun b hb => hall b hb)
    rw [Nat.card_zpowers, hord] at this
    omega
  have hb3 : b ^ 3 = 1 := hU.2 b hbU
  set c₀ := (MulAut.conj g⁻¹).toMonoidHom with hc₀
  have hc₀apply : ∀ x, c₀ x = g⁻¹ * x * g := fun x => by simp [hc₀]
  have hmemU' : ∀ x ∈ U, g⁻¹ * x * g ∈ S := fun x hx => by
    have := hU'S ⟨x, hx, rfl⟩
    rwa [hc₀apply] at this
  have ha'1 : g⁻¹ * a * g ≠ 1 := fun h => ha1' (by
    have := congrArg (fun y => g * y * g⁻¹) h
    simpa [mul_assoc] using this)
  have ha'3 : (g⁻¹ * a * g) ^ 3 = 1 := by
    rw [show (g⁻¹ * a * g) = (MulAut.conj g⁻¹ : MulAut J) a by simp, ← map_pow,
      ha3, map_one]
  have hb'3 : (g⁻¹ * b * g) ^ 3 = 1 := by
    rw [show (g⁻¹ * b * g) = (MulAut.conj g⁻¹ : MulAut J) b by simp, ← map_pow,
      hb3, map_one]
  have hab' : (g⁻¹ * a * g) * (g⁻¹ * b * g) = (g⁻¹ * b * g) * (g⁻¹ * a * g) := by
    calc (g⁻¹ * a * g) * (g⁻¹ * b * g) = g⁻¹ * (a * b) * g := by group
      _ = g⁻¹ * (b * a) * g := by rw [hUcomm a haU b hbU]
      _ = (g⁻¹ * b * g) * (g⁻¹ * a * g) := by group
  have hbz' : g⁻¹ * b * g ∉ Subgroup.zpowers (g⁻¹ * a * g) := by
    rintro ⟨k, hk⟩
    apply hbz
    refine ⟨k, ?_⟩
    have := congrArg (fun y => g * y * g⁻¹) hk
    simp only [] at this
    rw [show g * (g⁻¹ * a * g) ^ k * g⁻¹ = a ^ k by
      rw [show (g⁻¹ * a * g) = (MulAut.conj g⁻¹ : MulAut J) a by simp,
        ← map_zpow]
      simp [mul_assoc]] at this
    simpa [mul_assoc] using this
  obtain ⟨t, ht, h, z', hz'S, hz'c, htz⟩ := hcover _ (hmemU' a haU) _ (hmemU' b hbU) ha'1 ha'3 hb'3
    hab' hbz'
  have htU : g * t * g⁻¹ ∈ U := by
    have e1 : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    have e2 : g * (g⁻¹ * b * g) * g⁻¹ = b := by group
    rcases ht with rfl | rfl | rfl | rfl
    · rw [e1]; exact haU
    · rw [e2]; exact hbU
    · have : g * (g⁻¹ * a * g * (g⁻¹ * b * g)) * g⁻¹ = a * b := by group
      rw [this]; exact U.mul_mem haU hbU
    · have : g * (g⁻¹ * a * g * (g⁻¹ * b * g) ^ 2) * g⁻¹ = a * b ^ 2 := by
        rw [pow_two, pow_two]; group
      rw [this]; exact U.mul_mem haU (U.pow_mem hbU 2)
  have ht1 : g * t * g⁻¹ ≠ 1 := by
    intro h1
    have ht1' : t = 1 := by
      have := congrArg (fun y => g⁻¹ * y * g) h1
      simpa [mul_assoc] using this
    exact ne_one_of_mem_four hb'3 ha'1 hbz' ht ht1'
  refine ⟨g * t * g⁻¹, htU, ht1, d₀.conj (h * g⁻¹), ?_⟩
  refine LiftData.conj_x_mem_centralizer d₀ (h * g⁻¹) (g * t * g⁻¹) ?_
  intro i
  have : h * g⁻¹ * (g * t * g⁻¹) * (h * g⁻¹)⁻¹ = z' := by
    rw [← htz]
    group
  rw [this, Subgroup.mem_centralizer_singleton_iff]
  exact hz'c _ (hd₀ i)

end Sylow

end CFSG.RankThree.PartTwo.Sec4.Item434Cover
