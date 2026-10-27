module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelAbelianLiftDefs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Commutator.Basic

public section

open scoped commutatorElement

namespace CFSG.StandardType

private theorem mul_inv_mul_of_mem_center {G : Type*} [Group G] {z : G}
    (hz : z ∈ Subgroup.center G) (g : G) : g * z * g⁻¹ = z := by
  have h : g * z = z * g := Subgroup.mem_center_iff.mp hz g
  rw [h]
  group

private theorem commutatorElement_mul_of_mem_center_left {G : Type*} [Group G] {c : G}
    (hc : c ∈ Subgroup.center G) (a b : G) : ⁅a * c, b⁆ = ⁅a, b⁆ := by
  have h : ⁅c, b⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hc b).symm
  rw [commutatorElement_mul_left_eq_conj_mul, h, mul_one, mul_inv_cancel, one_mul]

private theorem commutatorElement_mul_of_mem_center_right {G : Type*} [Group G] {c : G}
    (hc : c ∈ Subgroup.center G) (a b : G) : ⁅a, b * c⁆ = ⁅a, b⁆ := by
  have h : ⁅a, c⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hc a)
  rw [commutatorElement_mul_right_eq_mul_conj, h, mul_one, mul_assoc, mul_inv_cancel, mul_one]

private theorem commutatorElement_mul_mul_of_mem_center {G : Type*} [Group G] {c d : G}
    (hc : c ∈ Subgroup.center G) (hd : d ∈ Subgroup.center G) (a b : G) :
    ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_of_mem_center_left hc, commutatorElement_mul_of_mem_center_right hd]

private theorem commutatorElement_eq_of_map_eq {L R : Type*} [Group L] [Group R] (ψ : L →* R)
    (hkc : ψ.ker ≤ Subgroup.center L) {l₁ l₂ l₁' l₂' : L}
    (h : ψ l₁ = ψ l₂) (h' : ψ l₁' = ψ l₂') :
    ⁅l₁, l₁'⁆ = ⁅l₂, l₂'⁆ := by
  have hz1 : l₁⁻¹ * l₂ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have hz2 : l₁'⁻¹ * l₂' ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h', inv_mul_cancel]
  have hc1 : l₁⁻¹ * l₂ ∈ Subgroup.center L := hkc hz1
  have hc2 : l₁'⁻¹ * l₂' ∈ Subgroup.center L := hkc hz2
  have e1 : l₁ * (l₁⁻¹ * l₂) = l₂ := by group
  have e2 : l₁' * (l₁'⁻¹ * l₂') = l₂' := by group
  have h2 : ⁅l₁ * (l₁⁻¹ * l₂), l₁' * (l₁'⁻¹ * l₂')⁆ = ⁅l₁, l₁'⁆ :=
    commutatorElement_mul_mul_of_mem_center hc1 hc2 l₁ l₁'
  rw [← e1, ← e2]
  exact h2.symm

private theorem mulAut_sq_eq_one_of_card_three {G : Type*} [Group G] (hG : Nat.card G = 3)
    (φ : MulAut G) : φ ^ 2 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  haveI : IsCyclic G := isCyclic_of_prime_card hG
  have hcard : Nat.card (MulAut G) = 2 := by
    rw [IsCyclic.card_mulAut, hG]
    decide
  have hdvd : orderOf φ ∣ 2 := hcard ▸ orderOf_dvd_natCard φ
  exact (orderOf_dvd_iff_pow_eq_one).mp hdvd

theorem ggAbelianLift : GGAbelianLift := by
  intro L R _ _ _ ψ hψ hkc hZ T N hTc hNT hF hAlt A hA hAT hAN
  rcases hZ with hZ1 | hZ3
  ·
    have hker : ψ.ker = ⊥ := Subgroup.card_eq_one.mp hZ1
    have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hker
    refine ⟨?_, ?_, ?_⟩
    · intro x hx y hy
      apply hinj
      rw [map_mul, map_mul]
      exact hTc (ψ x) hx (ψ y) hy
    · intro a ha x hx
      apply hinj
      exact hAT a ha x hx
    · intro V₀ hV₀ hexp hstab hG t ht
      have h3 : ψ (t ^ 3) = 1 := by rw [map_pow, hexp (ψ t) ht]
      have hmem : t ^ 3 ∈ ψ.ker := MonoidHom.mem_ker.mpr h3
      rw [hker] at hmem
      exact Subgroup.mem_bot.mp hmem
  ·
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI : IsCyclic ↥(ψ.ker) := isCyclic_of_prime_card (p := 3) hZ3
    haveI : IsCyclic (Multiplicative (ZMod 3)) := inferInstance
    have hcardZ3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    let e : ↥(ψ.ker) ≃* Multiplicative (ZMod 3) :=
      mulEquivOfCyclicCardEq (by rw [hZ3, hcardZ3])
    have hmemA : ∀ b ∈ A, ∀ z : L, z ∈ ψ.ker → b z ∈ ψ.ker := by
      intro b hb z hz
      rw [MonoidHom.mem_ker] at hz ⊢
      rw [hAT b hb z (by rw [hz]; exact T.one_mem), hz]
    have hZ_act : ∀ b ∈ A, ∀ z ∈ ψ.ker, b z = z := by
      intro b hb z hz
      let ρ : A →* MulAut ↥(ψ.ker) :=
        { toFun := fun c =>
            { toFun := fun w => ⟨(c : MulAut L) w, hmemA (c : MulAut L) c.property w w.property⟩
              invFun := fun w => ⟨(c : MulAut L).symm w,
                hmemA (c : MulAut L).symm (A.inv_mem c.property) w w.property⟩
              left_inv := by intro w; ext; exact (c : MulAut L).symm_apply_apply w
              right_inv := by intro w; ext; exact (c : MulAut L).apply_symm_apply w
              map_mul' := by intro w w'; ext; exact (c : MulAut L).map_mul w w' }
          map_one' := by ext w; rfl
          map_mul' := by intro c d; ext w; rfl }
      let bZ : MulAut ↥(ψ.ker) := ρ ⟨b, hb⟩
      have hb2 : bZ ^ 2 = 1 := mulAut_sq_eq_one_of_card_three hZ3 bZ
      obtain ⟨k, hk⟩ := hA ⟨b, hb⟩
      have hbZk : bZ ^ (3 ^ k) = 1 := by
        have hbZ : bZ = ρ ⟨b, hb⟩ := rfl
        rw [hbZ, ← map_pow, hk, map_one]
      have hdvd2 : orderOf bZ ∣ 2 := (orderOf_dvd_iff_pow_eq_one).mpr hb2
      have hdvdk : orderOf bZ ∣ 3 ^ k := (orderOf_dvd_iff_pow_eq_one).mpr hbZk
      have hcop : Nat.Coprime 2 (3 ^ k) :=
        Nat.coprime_two_left.mpr (Odd.pow (by decide : Odd 3))
      have hdvd1 : orderOf bZ ∣ 1 := by
        have := Nat.dvd_gcd hdvd2 hdvdk
        rwa [hcop] at this
      have hbZ1 : bZ = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)
      have hw : (bZ ⟨z, hz⟩ : L) = z := by
        rw [hbZ1]
        rfl
      exact hw
    let s : R → L := Function.surjInv hψ
    have hs : ∀ r : R, ψ (s r) = r := Function.surjInv_eq hψ
    have hmem_comm : ∀ x y : ↥T, ⁅s (x : R), s (y : R)⁆ ∈ ψ.ker := by
      intro x y
      rw [MonoidHom.mem_ker, map_commutatorElement, hs, hs]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hTc (x : R) x.property (y : R) y.property)
    let κ : ↥T → ↥T → Multiplicative (ZMod 3) :=
      fun x y => e ⟨⁅s (x : R), s (y : R)⁆, hmem_comm x y⟩
    have hcomm_mem : ∀ (x y : ↥T) (l l' : L), ψ l = (x : R) → ψ l' = (y : R) →
        ⁅l, l'⁆ ∈ ψ.ker := by
      intro x y l l' hl hl'
      rw [MonoidHom.mem_ker, map_commutatorElement, hl, hl']
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hTc (x : R) x.property (y : R) y.property)
    have hκ_val : ∀ (x y : ↥T) (l l' : L) (hl : ψ l = (x : R)) (hl' : ψ l' = (y : R)),
        κ x y = e ⟨⁅l, l'⁆, hcomm_mem x y l l' hl hl'⟩ := by
      intro x y l l' hl hl'
      have hval : (⟨⁅s (x : R), s (y : R)⁆, hmem_comm x y⟩ : ↥(ψ.ker))
          = ⟨⁅l, l'⁆, hcomm_mem x y l l' hl hl'⟩ := by
        apply Subtype.ext
        exact commutatorElement_eq_of_map_eq ψ hkc ((hs (x : R)).trans hl.symm)
          ((hs (y : R)).trans hl'.symm)
      exact congrArg e hval
    have hκ_mul_left : ∀ x y z : ↥T, κ (x * y) z = κ x z * κ y z := by
      intro x y z
      rw [hκ_val (x * y) z (s ((x * y : ↥T) : R)) (s (z : R)) (hs _) (hs _),
        hκ_val x z (s (x : R)) (s (z : R)) (hs _) (hs _),
        hκ_val y z (s (y : R)) (s (z : R)) (hs _) (hs _), ← map_mul]
      apply congrArg e
      apply Subtype.ext
      change ⁅s ((x * y : ↥T) : R), s (z : R)⁆
        = ⁅s (x : R), s (z : R)⁆ * ⁅s (y : R), s (z : R)⁆
      have hxy : ψ (s ((x * y : ↥T) : R)) = ψ (s (x : R) * s (y : R)) := by
        rw [hs, map_mul, hs, hs]
        rfl
      rw [commutatorElement_eq_of_map_eq ψ hkc hxy rfl]
      have hkey : ⁅s (x : R) * s (y : R), s (z : R)⁆
          = ⁅s (y : R), s (z : R)⁆ * ⁅s (x : R), s (z : R)⁆ := by
        rw [commutatorElement_mul_left_eq_conj_mul]
        rw [mul_inv_mul_of_mem_center (hkc (hmem_comm y z))]
      rw [hkey]
      exact Subgroup.mem_center_iff.mp (hkc (hmem_comm x z)) (⁅s (y : R), s (z : R)⁆)
    have hκ_mul_right : ∀ x y z : ↥T, κ x (y * z) = κ x y * κ x z := by
      intro x y z
      rw [hκ_val x (y * z) (s (x : R)) (s ((y * z : ↥T) : R)) (hs _) (hs _),
        hκ_val x y (s (x : R)) (s (y : R)) (hs _) (hs _),
        hκ_val x z (s (x : R)) (s (z : R)) (hs _) (hs _), ← map_mul]
      apply congrArg e
      apply Subtype.ext
      change ⁅s (x : R), s ((y * z : ↥T) : R)⁆
        = ⁅s (x : R), s (y : R)⁆ * ⁅s (x : R), s (z : R)⁆
      have hyz : ψ (s ((y * z : ↥T) : R)) = ψ (s (y : R) * s (z : R)) := by
        rw [hs, map_mul, hs, hs]
        rfl
      rw [commutatorElement_eq_of_map_eq ψ hkc rfl hyz]
      have hkey : ⁅s (x : R), s (y : R) * s (z : R)⁆
          = ⁅s (x : R), s (y : R)⁆ * ⁅s (x : R), s (z : R)⁆ := by
        calc ⁅s (x : R), s (y : R) * s (z : R)⁆
            = ⁅s (x : R), s (y : R)⁆ * s (y : R) * ⁅s (x : R), s (z : R)⁆ * (s (y : R))⁻¹ :=
              commutatorElement_mul_right_eq_mul_conj _ _ _
          _ = ⁅s (x : R), s (y : R)⁆ * (s (y : R) * ⁅s (x : R), s (z : R)⁆ * (s (y : R))⁻¹) := by
              group
          _ = ⁅s (x : R), s (y : R)⁆ * ⁅s (x : R), s (z : R)⁆ := by
              rw [mul_inv_mul_of_mem_center (hkc (hmem_comm x z))]
      rw [hkey]
    have hκ_self : ∀ x : ↥T, κ x x = 1 := by
      intro x
      change e ⟨⁅s (x : R), s (x : R)⁆, hmem_comm x x⟩ = 1
      have hval : (⟨⁅s (x : R), s (x : R)⁆, hmem_comm x x⟩ : ↥(ψ.ker)) = 1 := by
        apply Subtype.ext
        simp
      rw [hval, map_one]
    have hκ_inv : ∀ n ∈ N, ∀ x y x' y' : ↥T,
        (x' : R) = ψ n * x * (ψ n)⁻¹ → (y' : R) = ψ n * y * (ψ n)⁻¹ →
        κ x' y' = κ x y := by
      intro n hn x y x' y' hx' hy'
      rw [hκ_val x' y' (n * s (x : R) * n⁻¹) (n * s (y : R) * n⁻¹)
          (by rw [map_mul, map_mul, map_inv, hs, hx']) (by rw [map_mul, map_mul, map_inv, hs, hy']),
        hκ_val x y (s (x : R)) (s (y : R)) (hs _) (hs _)]
      apply congrArg e
      apply Subtype.ext
      change ⁅n * s (x : R) * n⁻¹, n * s (y : R) * n⁻¹⁆ = ⁅s (x : R), s (y : R)⁆
      rw [← conjugate_commutatorElement]
      rw [mul_inv_mul_of_mem_center (hkc (hmem_comm x y))]
    have hAlt_eq : ∀ x y : ↥T, κ x y = 1 :=
      hAlt κ hκ_mul_left hκ_mul_right hκ_self hκ_inv
    have hab : ∀ x ∈ T.comap ψ, ∀ y ∈ T.comap ψ, x * y = y * x := by
      intro x hx y hy
      have hxy := hAlt_eq ⟨ψ x, hx⟩ ⟨ψ y, hy⟩
      rw [hκ_val ⟨ψ x, hx⟩ ⟨ψ y, hy⟩ x y rfl rfl] at hxy
      have h1 : (⟨⁅x, y⁆, hcomm_mem ⟨ψ x, hx⟩ ⟨ψ y, hy⟩ x y rfl rfl⟩ : ↥(ψ.ker)) = 1 :=
        e.injective (by rw [map_one]; exact hxy)
      exact commutatorElement_eq_one_iff_mul_comm.mp (Subtype.ext_iff.mp h1)
    refine ⟨hab, ?_, ?_⟩
    ·
      intro a ha x hx
      have hδ_eq : ∀ l l' : L, ψ l = ψ l' → a l * l⁻¹ = a l' * l'⁻¹ := by
        intro l l' hl
        have hz : l⁻¹ * l' ∈ ψ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hl, inv_mul_cancel]
        have hact : a (l⁻¹ * l') = l⁻¹ * l' := hZ_act a ha (l⁻¹ * l') hz
        have he : l' = l * (l⁻¹ * l') := by group
        rw [he, map_mul, hact]
        group
      have hf_mem : ∀ w : ↥T, a (s (w : R)) * (s (w : R))⁻¹ ∈ ψ.ker := by
        intro w
        rw [MonoidHom.mem_ker, map_mul, map_inv,
          hAT a ha (s (w : R)) (by rw [hs]; exact w.property)]
        group
      let f : ↥T →* Multiplicative (ZMod 3) :=
        MonoidHom.mk' (fun w => e ⟨a (s (w : R)) * (s (w : R))⁻¹, hf_mem w⟩) (by
          intro w w'
          show e ⟨a (s ((w * w' : ↥T) : R)) * (s ((w * w' : ↥T) : R))⁻¹, hf_mem (w * w')⟩
             = e ⟨a (s (w : R)) * (s (w : R))⁻¹, hf_mem w⟩
               * e ⟨a (s (w' : R)) * (s (w' : R))⁻¹, hf_mem w'⟩
          rw [← map_mul]
          apply congrArg e
          apply Subtype.ext
          change a (s ((w * w' : ↥T) : R)) * (s ((w * w' : ↥T) : R))⁻¹
            = (a (s (w : R)) * (s (w : R))⁻¹) * (a (s (w' : R)) * (s (w' : R))⁻¹)
          rw [hδ_eq (s ((w * w' : ↥T) : R)) (s (w : R) * s (w' : R))
              (by rw [hs, map_mul, hs, hs]; rfl),
            map_mul, mul_inv_rev]
          have hc : a (s (w' : R)) * (s (w' : R))⁻¹ ∈ Subgroup.center L := hkc (hf_mem w')
          have hcomm : (a (s (w' : R)) * (s (w' : R))⁻¹) * (s (w : R))⁻¹
              = (s (w : R))⁻¹ * (a (s (w' : R)) * (s (w' : R))⁻¹) :=
            (Subgroup.mem_center_iff.mp hc (s (w : R))⁻¹).symm
          rw [show (a (s (w : R)) * a (s (w' : R))) * ((s (w' : R))⁻¹ * (s (w : R))⁻¹)
                = a (s (w : R)) * ((a (s (w' : R)) * (s (w' : R))⁻¹) * (s (w : R))⁻¹) by group,
              hcomm]
          group)
      have hδ_conj : ∀ (n : L) (hn : n ∈ N) (l : L), ψ l ∈ T →
          a (n * l * n⁻¹) * (n * l * n⁻¹)⁻¹ = a l * l⁻¹ := by
        intro n hn l hl
        have hk : n⁻¹ * a n ∈ T.comap ψ := hAN a ha n hn
        have hal : a l ∈ T.comap ψ := by
          rw [Subgroup.mem_comap, hAT a ha l hl]
          exact hl
        have hcomm : (n⁻¹ * a n) * a l = a l * (n⁻¹ * a n) := hab _ hk _ hal
        have han : a n = n * (n⁻¹ * a n) := by group
        have hconj : a (n * l * n⁻¹) = n * a l * n⁻¹ := by
          rw [map_mul, map_mul, map_inv, han, mul_inv_rev,
            show (n * (n⁻¹ * a n)) * a l * ((n⁻¹ * a n)⁻¹ * n⁻¹)
                = n * ((n⁻¹ * a n) * a l * (n⁻¹ * a n)⁻¹) * n⁻¹ by group,
            hcomm]
          group
        have hc : a l * l⁻¹ ∈ Subgroup.center L := by
          apply hkc
          rw [MonoidHom.mem_ker, map_mul, map_inv, hAT a ha l hl]
          group
        calc a (n * l * n⁻¹) * (n * l * n⁻¹)⁻¹
            = (n * a l * n⁻¹) * (n * l * n⁻¹)⁻¹ := by rw [hconj]
          _ = n * (a l * l⁻¹) * n⁻¹ := by group
          _ = a l * l⁻¹ := mul_inv_mul_of_mem_center hc n
      have hf_inv : ∀ n ∈ N, ∀ w w' : ↥T, (w' : R) = ψ n * w * (ψ n)⁻¹ → f w' = f w := by
        intro n hn w w' hw'
        have h1 : a (s (w' : R)) * (s (w' : R))⁻¹
            = a (n * s (w : R) * n⁻¹) * (n * s (w : R) * n⁻¹)⁻¹ :=
          hδ_eq (s (w' : R)) (n * s (w : R) * n⁻¹)
            (by rw [hs, map_mul, map_mul, map_inv, hs, hw'])
        have h2 : a (n * s (w : R) * n⁻¹) * (n * s (w : R) * n⁻¹)⁻¹
            = a (s (w : R)) * (s (w : R))⁻¹ :=
          hδ_conj n hn (s (w : R)) (by rw [hs]; exact w.property)
        show e ⟨a (s (w' : R)) * (s (w' : R))⁻¹, hf_mem w'⟩
           = e ⟨a (s (w : R)) * (s (w : R))⁻¹, hf_mem w⟩
        apply congrArg e
        apply Subtype.ext
        exact h1.trans h2
      have hf1 : f = 1 := hF f hf_inv
      have hδmem : a x * x⁻¹ ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hAT a ha x hx]
        group
      have hδx : a (s (ψ x)) * (s (ψ x))⁻¹ = a x * x⁻¹ := hδ_eq (s (ψ x)) x (hs (ψ x))
      have hfx : f ⟨ψ x, hx⟩ = 1 := by simp [hf1]
      have heq : f ⟨ψ x, hx⟩ = e ⟨a x * x⁻¹, hδmem⟩ := by
        apply congrArg e
        apply Subtype.ext
        exact hδx
      rw [heq] at hfx
      have h1 : (⟨a x * x⁻¹, hδmem⟩ : ↥(ψ.ker)) = 1 :=
        e.injective (by rw [map_one]; exact hfx)
      exact mul_inv_eq_one.mp (Subtype.ext_iff.mp h1)
    ·
      intro V₀ hV₀ hexp hstab hG t ht
      have hcube_eq : ∀ l l' : L, ψ l = ψ l' → l ^ 3 = l' ^ 3 := by
        intro l l' hl
        have hz : l⁻¹ * l' ∈ ψ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hl, inv_mul_cancel]
        have hz3 : (l⁻¹ * l') ^ 3 = 1 := by
          have hdvd : orderOf (l⁻¹ * l') ∣ 3 := by
            rw [← hZ3]
            exact Subgroup.orderOf_dvd_natCard ψ.ker hz
          exact (orderOf_dvd_iff_pow_eq_one).mp hdvd
        have hzcent : Commute l (l⁻¹ * l') := Subgroup.mem_center_iff.mp (hkc hz) l
        have he : l' = l * (l⁻¹ * l') := by group
        rw [he, hzcent.mul_pow, hz3, mul_one]
      have hg_mem : ∀ v : ↥V₀, (s (v : R)) ^ 3 ∈ ψ.ker := by
        intro v
        rw [MonoidHom.mem_ker, map_pow, hs, hexp (v : R) v.property]
      let g : ↥V₀ →* Multiplicative (ZMod 3) :=
        MonoidHom.mk' (fun v => e ⟨(s (v : R)) ^ 3, hg_mem v⟩) (by
          intro v w
          show e ⟨(s ((v * w : ↥V₀) : R)) ^ 3, hg_mem (v * w)⟩
             = e ⟨(s (v : R)) ^ 3, hg_mem v⟩ * e ⟨(s (w : R)) ^ 3, hg_mem w⟩
          rw [← map_mul]
          apply congrArg e
          apply Subtype.ext
          change (s ((v * w : ↥V₀) : R)) ^ 3 = (s (v : R)) ^ 3 * (s (w : R)) ^ 3
          rw [hcube_eq (s ((v * w : ↥V₀) : R)) (s (v : R) * s (w : R))
            (by rw [hs, map_mul, hs, hs]; rfl)]
          have hsv : s (v : R) ∈ T.comap ψ := by
            rw [Subgroup.mem_comap, hs]; exact hV₀ v.property
          have hsw : s (w : R) ∈ T.comap ψ := by
            rw [Subgroup.mem_comap, hs]; exact hV₀ w.property
          have hcvw : Commute (s (v : R)) (s (w : R)) := hab _ hsv _ hsw
          rw [hcvw.mul_pow])
      have hg_inv : ∀ n ∈ N, ∀ v v' : ↥V₀, (v' : R) = ψ n * v * (ψ n)⁻¹ → g v' = g v := by
        intro n hn v v' hv'
        have h1 : (s (v' : R)) ^ 3 = (n * s (v : R) * n⁻¹) ^ 3 :=
          hcube_eq (s (v' : R)) (n * s (v : R) * n⁻¹)
            (by rw [hs, map_mul, map_mul, map_inv, hs, hv'])
        have h2 : (n * s (v : R) * n⁻¹) ^ 3 = (s (v : R)) ^ 3 := by
          rw [conj_pow]
          exact mul_inv_mul_of_mem_center (hkc (hg_mem v)) n
        show e ⟨(s (v' : R)) ^ 3, hg_mem v'⟩ = e ⟨(s (v : R)) ^ 3, hg_mem v⟩
        apply congrArg e
        apply Subtype.ext
        exact h1.trans h2
      have hg1 : g = 1 := hG g hg_inv
      have hmemt : t ^ 3 ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_pow, hexp (ψ t) ht]
      have hcube : (s (ψ t)) ^ 3 = t ^ 3 := hcube_eq (s (ψ t)) t (hs (ψ t))
      have hgt : g ⟨ψ t, ht⟩ = 1 := by simp [hg1]
      have heq : g ⟨ψ t, ht⟩ = e ⟨t ^ 3, hmemt⟩ := by
        apply congrArg e
        apply Subtype.ext
        exact hcube
      rw [heq] at hgt
      have h1 : (⟨t ^ 3, hmemt⟩ : ↥(ψ.ker)) = 1 :=
        e.injective (by rw [map_one]; exact hgt)
      exact Subtype.ext_iff.mp h1

end CFSG.StandardType
