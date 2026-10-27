module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenYamakiSetup
public import CFSG.CGT.PushingUpLit.SolK.Basics

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Sp62Rec.I1 Equiv CFSG.Open

theorem zpow_involution {G : Type*} [Group G] {t : G} (ht : orderOf t = 2) (k : ℤ) :
    t ^ k = 1 ∨ t ^ k = t := by
  rw [← zpow_mod_orderOf, ht]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [show (k % ((2 : ℕ) : ℤ)) = 0 from h, zpow_zero]
  · right
    rw [show (k % ((2 : ℕ) : ℤ)) = 1 from h, zpow_one]

theorem isTwoLocal_centralizer_of_involution {G : Type*} [Group G] {t : G} (ht1 : t ≠ 1)
    (ht2 : t * t = 1) : IsTwoLocal (Subgroup.centralizer ({t} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht2) ht1
  refine ⟨Subgroup.zpowers t, ?_,
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one]), ?_⟩
  · rwa [Ne, Subgroup.zpowers_eq_bot]
  · refine le_antisymm ?_ ?_
    · rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
      exact Subgroup.centralizer_le_normalizer _
    · intro g hg
      have h1 : g * t * g⁻¹ ∈ Subgroup.zpowers t :=
        (Subgroup.mem_normalizer_iff.mp hg t).mp (Subgroup.mem_zpowers t)
      rw [Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
      rcases zpow_involution hord k with h | h
      · exfalso
        apply ht1
        have h2 : g * t * g⁻¹ = 1 := by rw [← hk, h]
        have := congrArg (fun x => g⁻¹ * x * g) h2
        simpa [mul_assoc] using this
      · have h4 : g * t * g⁻¹ = t := by rw [← hk, h]
        calc g * t = (g * t * g⁻¹) * g := by group
          _ = t * g := by rw [h4]

theorem pCoreOf_le_sylow_of_le {G : Type} [Group G] [Finite G] (W : Sylow 2 G) {L : Subgroup G}
    (hWL : (W : Subgroup G) ≤ L) : pCoreOf 2 L ≤ (W : Subgroup G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 (pCoreOf 2 L) := CFSG.CGT.PushingUpLit.SolK.isPGroup_pCoreOf' L
  have hWN : (W : Subgroup G) ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    hWL.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  have hsup : IsPGroup 2 ((W : Subgroup G) ⊔ pCoreOf 2 L : Subgroup G) :=
    W.isPGroup'.to_sup_of_normal_right' hQ2 hWN
  have := W.is_maximal' hsup le_sup_left
  exact le_sup_right.trans this.le

theorem wPi3_mem_Wsub : wPi3 ∈ Wsub := by show wsum wPi3 = 0; decide

theorem wPi12_mem_Wsub : wPi12 ∈ Wsub := by show wsum wPi12 = 0; decide

theorem wPi12_eq : wPi12 = Wr.allOnes 6 * wPi3 := by decide

theorem commute_wPi12_iff (a : Wr 6) : a * wPi12 = wPi12 * a ↔ a * wPi3 = wPi3 * a := by
  rw [wPi12_eq]
  have hc := (Wr.allOnes_comm a).symm
  constructor
  · intro h
    have h1 : Wr.allOnes 6 * (a * wPi3) = Wr.allOnes 6 * (wPi3 * a) := by
      calc Wr.allOnes 6 * (a * wPi3) = a * (Wr.allOnes 6 * wPi3) := by
            rw [← mul_assoc, ← hc, mul_assoc]
        _ = Wr.allOnes 6 * wPi3 * a := h
        _ = Wr.allOnes 6 * (wPi3 * a) := mul_assoc _ _ _
    exact mul_left_cancel h1
  · intro h
    calc a * (Wr.allOnes 6 * wPi3) = Wr.allOnes 6 * (a * wPi3) := by
          rw [← mul_assoc, hc, mul_assoc]
      _ = Wr.allOnes 6 * (wPi3 * a) := by rw [h]
      _ = Wr.allOnes 6 * wPi3 * a := (mul_assoc _ _ _).symm

namespace YData

variable {G : Type} [Group G] [Finite G] {z : G} (Y : YData z)

@[expose] noncomputable def π3 : G := Y.ι ⟨wPi3, wPi3_mem_Wsub⟩

@[expose] noncomputable def π12 : G := Y.ι ⟨wPi12, wPi12_mem_Wsub⟩

theorem π3_mem_C : Y.π3 ∈ Subgroup.centralizer ({z} : Set G) := Y.ι_mem_C _

theorem π12_mem_C : Y.π12 ∈ Subgroup.centralizer ({z} : Set G) := Y.ι_mem_C _

theorem ϑ_π3 : (Y.ϑ ⟨Y.π3, Y.π3_mem_C⟩ : Wr 6) = wPi3 := congrArg Subtype.val (Y.ϑ_ι _)

theorem ϑ_π12 : (Y.ϑ ⟨Y.π12, Y.π12_mem_C⟩ : Wr 6) = wPi12 := congrArg Subtype.val (Y.ϑ_ι _)

theorem ι_mul (a b : ↥Wsub) : Y.ι (a * b) = Y.ι a * Y.ι b := map_mul _ _ _

theorem ϑ_mul_coe {x y : G} (hx : x ∈ Subgroup.centralizer ({z} : Set G))
    (hy : y ∈ Subgroup.centralizer ({z} : Set G)) :
    (Y.ϑ ⟨x * y, Subgroup.mul_mem _ hx hy⟩ : Wr 6) = Y.ϑ ⟨x, hx⟩ * Y.ϑ ⟨y, hy⟩ := by
  rw [← Subgroup.coe_mul, ← map_mul]
  rfl

theorem ϑ_inv_coe {x : G} (hx : x ∈ Subgroup.centralizer ({z} : Set G)) :
    (Y.ϑ ⟨x⁻¹, Subgroup.inv_mem _ hx⟩ : Wr 6) = (Y.ϑ ⟨x, hx⟩ : Wr 6)⁻¹ := by
  rw [← Subgroup.coe_inv, ← map_inv]
  rfl

theorem eq_of_ϑ_eq {x y : G} {hx : x ∈ Subgroup.centralizer ({z} : Set G)}
    {hy : y ∈ Subgroup.centralizer ({z} : Set G)}
    (h : (Y.ϑ ⟨x, hx⟩ : Wr 6) = Y.ϑ ⟨y, hy⟩) : x = y :=
  congrArg Subtype.val (Y.ϑ.injective (Subtype.ext h))

theorem commute_of_ϑ {x y : G} (hx : x ∈ Subgroup.centralizer ({z} : Set G))
    (hy : y ∈ Subgroup.centralizer ({z} : Set G))
    (h : (Y.ϑ ⟨x, hx⟩ : Wr 6) * Y.ϑ ⟨y, hy⟩ = Y.ϑ ⟨y, hy⟩ * Y.ϑ ⟨x, hx⟩) : x * y = y * x := by
  have h1 : Y.ϑ (⟨x, hx⟩ * ⟨y, hy⟩) = Y.ϑ (⟨y, hy⟩ * ⟨x, hx⟩) := by
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul]
    exact h
  exact congrArg Subtype.val (Y.ϑ.injective h1)

theorem ϑ_commute {x y : G} (hx : x ∈ Subgroup.centralizer ({z} : Set G))
    (hy : y ∈ Subgroup.centralizer ({z} : Set G)) (h : x * y = y * x) :
    (Y.ϑ ⟨x, hx⟩ : Wr 6) * Y.ϑ ⟨y, hy⟩ = Y.ϑ ⟨y, hy⟩ * Y.ϑ ⟨x, hx⟩ := by
  have h1 : (⟨x, hx⟩ : ↥(Subgroup.centralizer ({z} : Set G))) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ :=
    Subtype.ext h
  have h2 := congrArg (fun c => (Y.ϑ c : Wr 6)) h1
  simpa only [map_mul, Subgroup.coe_mul] using h2

theorem commute_of_mem_T {t : G} (ht : t ∈ Y.T) :
    t * Y.π3 = Y.π3 * t ∧ t * Y.π12 = Y.π12 * t ∧ t * z = z * t := by
  obtain ⟨htC, htD⟩ := Y.mem_lift.mp ht
  refine ⟨Y.commute_of_ϑ htC Y.π3_mem_C ?_, Y.commute_of_ϑ htC Y.π12_mem_C ?_,
    Subgroup.mem_centralizer_singleton_iff.mp htC⟩
  · rw [Y.ϑ_π3]
    exact commute_wPi3_of_mem_DW htD
  · rw [Y.ϑ_π12]
    exact commute_wPi12_of_mem_DW htD

theorem π3_ne_one : Y.π3 ≠ 1 := by
  intro h
  have : (⟨wPi3, wPi3_mem_Wsub⟩ : ↥Wsub) = 1 := Y.ι_injective (by rw [map_one]; exact h)
  exact absurd (congrArg Subtype.val this) (by decide)

theorem π12_ne_one : Y.π12 ≠ 1 := by
  intro h
  have : (⟨wPi12, wPi12_mem_Wsub⟩ : ↥Wsub) = 1 := Y.ι_injective (by rw [map_one]; exact h)
  exact absurd (congrArg Subtype.val this) (by decide)

theorem π3_mul_self : Y.π3 * Y.π3 = 1 := by
  rw [π3, ← Y.ι_mul, show (⟨wPi3, wPi3_mem_Wsub⟩ : ↥Wsub) * ⟨wPi3, wPi3_mem_Wsub⟩ = 1 from
    Subtype.ext (by decide), map_one]

theorem π12_mul_self : Y.π12 * Y.π12 = 1 := by
  rw [π12, ← Y.ι_mul, show (⟨wPi12, wPi12_mem_Wsub⟩ : ↥Wsub) * ⟨wPi12, wPi12_mem_Wsub⟩ = 1 from
    Subtype.ext (by decide), map_one]

theorem z_mul_π3 : z * Y.π3 = Y.π12 := by
  have h : Y.ι ⟨Wr.allOnes 6, allOnes_mem_Wsub⟩ * Y.π3 = Y.π12 := by
    rw [π3, ← Y.ι_mul, π12]
    congr 1
    exact Subtype.ext wPi12_eq.symm
  rwa [Y.ι_allOnes] at h

theorem conj_z_perm (hchar : IsCharTwoType G) (P : Sylow 2 G) (hP : (P : Subgroup G) = Y.T)
    (hz : orderOf z = 2) {y : G} (hy : y = Y.π3 ∨ y = Y.π12) {g : G}
    (hg : g ∈ Subgroup.centralizer ({y} : Set G)) :
    ∃ hx : g * z * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G),
      (Y.ϑ ⟨g * z * g⁻¹, hx⟩ : Wr 6).perm = 1 ∨
        (Y.ϑ ⟨g * z * g⁻¹, hx⟩ : Wr 6).perm = swap 4 5 := by
  set L := Subgroup.centralizer ({y} : Set G) with hLdef
  have hyC : y ∈ Subgroup.centralizer ({z} : Set G) := by
    rcases hy with rfl | rfl
    · exact Y.π3_mem_C
    · exact Y.π12_mem_C
  have hy1 : y ≠ 1 := by rcases hy with rfl | rfl; exacts [Y.π3_ne_one, Y.π12_ne_one]
  have hy2 : y * y = 1 := by rcases hy with rfl | rfl; exacts [Y.π3_mul_self, Y.π12_mul_self]
  have hloc := isTwoLocal_centralizer_of_involution hy1 hy2
  have hcl := hchar L hloc
  have hTL : (P : Subgroup G) ≤ L := by
    intro t ht
    rw [hP] at ht
    rw [hLdef, Subgroup.mem_centralizer_singleton_iff]
    rcases hy with rfl | rfl
    · exact (Y.commute_of_mem_T ht).1
    · exact (Y.commute_of_mem_T ht).2.1
  have hRT : pCoreOf 2 L ≤ Y.T := hP ▸ pCoreOf_le_sylow_of_le P hTL
  have hRC : pCoreOf 2 L ≤ Subgroup.centralizer ({z} : Set G) := hRT.trans Y.T_le_C
  have hzL : z ∈ L := by
    rw [hLdef, Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp hyC).symm
  have hzcR : z ∈ Subgroup.centralizer (pCoreOf 2 L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact Subgroup.mem_centralizer_singleton_iff.mp (hRC hr)
  have hzR : z ∈ pCoreOf 2 L := hcl ⟨hzL, hzcR⟩
  have hconjR : ∀ g ∈ L, g * z * g⁻¹ ∈ pCoreOf 2 L := fun g hg =>
    CFSG.CGT.PushingUpLit.SolK.pCoreOf_normalized L hg hzR
  have hconjC : ∀ g ∈ L, g * z * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := fun g hg =>
    hRC (hconjR g hg)
  have hcentR : ∀ g ∈ L, ∀ r ∈ pCoreOf 2 L, (g * z * g⁻¹) * r = r * (g * z * g⁻¹) := by
    intro g hg r hr
    have hr' : g⁻¹ * r * g ∈ pCoreOf 2 L := by
      have := CFSG.CGT.PushingUpLit.SolK.pCoreOf_normalized L (L.inv_mem hg) hr
      rwa [inv_inv] at this
    have h1 := Subgroup.mem_centralizer_iff.mp hzcR _ hr'
    calc (g * z * g⁻¹) * r = g * (z * (g⁻¹ * r * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * r * g) * z) * g⁻¹ := by rw [h1]
      _ = r * (g * z * g⁻¹) := by group
  set X : Set (Wr 6) := {w | ∃ g ∈ L, ∃ hx : g * z * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G),
      (Y.ϑ ⟨g * z * g⁻¹, hx⟩ : Wr 6) = w} with hXdef
  have hX : ∀ w ∈ X, w * wPi3 = wPi3 * w := by
    rintro w ⟨g', hg', hx, rfl⟩
    have hxL : g' * z * g'⁻¹ ∈ L := L.mul_mem (L.mul_mem hg' hzL) (L.inv_mem hg')
    have hxy : (g' * z * g'⁻¹) * y = y * (g' * z * g'⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.mp hxL
    have h1 := Y.ϑ_commute hx hyC hxy
    rcases hy with rfl | rfl
    · rwa [Y.ϑ_π3] at h1
    · rw [Y.ϑ_π12] at h1
      exact (commute_wPi12_iff _).mp h1
  have hinv : ∀ w ∈ X, w * w = 1 := by
    rintro w ⟨g', hg', hx, rfl⟩
    have hzz : z * z = 1 := by rw [← sq, ← hz, pow_orderOf_eq_one]
    have hxx : (⟨g' * z * g'⁻¹, hx⟩ : ↥(Subgroup.centralizer ({z} : Set G))) *
        ⟨g' * z * g'⁻¹, hx⟩ = 1 := Subtype.ext (by
      show g' * z * g'⁻¹ * (g' * z * g'⁻¹) = 1
      calc g' * z * g'⁻¹ * (g' * z * g'⁻¹) = g' * (z * z) * g'⁻¹ := by group
        _ = 1 := by rw [hzz]; group)
    have h1 := congrArg (fun c => (Y.ϑ c : Wr 6)) hxx
    simpa only [map_mul, Subgroup.coe_mul, map_one, Subgroup.coe_one] using h1
  have hcomm : ∀ w₁ ∈ X, ∀ w₂ ∈ X, w₁ * w₂ = w₂ * w₁ := by
    rintro w₁ ⟨g₁, hg₁, hx₁, rfl⟩ w₂ ⟨g₂, hg₂, hx₂, rfl⟩
    exact Y.ϑ_commute hx₁ hx₂ (hcentR g₁ hg₁ _ (hconjR g₂ hg₂))
  have hconj : ∀ k ∈ Wsub, k * wPi3 = wPi3 * k → ∀ w ∈ X, k * w * k⁻¹ ∈ X := by
    rintro k hk hkc w ⟨g', hg', hx, rfl⟩
    set kG := Y.ι ⟨k, hk⟩ with hkG
    have hkGC := Y.ι_mem_C ⟨k, hk⟩
    have hϑk : (Y.ϑ ⟨kG, hkGC⟩ : Wr 6) = k := congrArg Subtype.val (Y.ϑ_ι _)
    have hkL : kG ∈ L := by
      rw [hLdef, Subgroup.mem_centralizer_singleton_iff]
      refine Y.commute_of_ϑ hkGC hyC ?_
      rw [hϑk]
      rcases hy with rfl | rfl
      · rw [Y.ϑ_π3]; exact hkc
      · rw [Y.ϑ_π12]; exact (commute_wPi12_iff _).mpr hkc
    refine ⟨kG * g', L.mul_mem hkL hg', hconjC _ (L.mul_mem hkL hg'), ?_⟩
    have he : (⟨kG * g' * z * (kG * g')⁻¹, hconjC _ (L.mul_mem hkL hg')⟩ :
        ↥(Subgroup.centralizer ({z} : Set G))) =
        ⟨kG, hkGC⟩ * ⟨g' * z * g'⁻¹, hx⟩ * (⟨kG, hkGC⟩)⁻¹ := Subtype.ext (by
      show kG * g' * z * (kG * g')⁻¹ = kG * (g' * z * g'⁻¹) * kG⁻¹
      group)
    rw [he]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hϑk]
  exact ⟨hconjC g hg, perm_of_commuting_class hX hinv hcomm hconj _ ⟨g, hg, hconjC g hg, rfl⟩⟩

theorem isConj_of_ϑ {x x' : G} (hx : x ∈ Subgroup.centralizer ({z} : Set G))
    (hx' : x' ∈ Subgroup.centralizer ({z} : Set G)) {k : Wr 6} (hk : k ∈ Wsub)
    (h : k * (Y.ϑ ⟨x, hx⟩ : Wr 6) * k⁻¹ = Y.ϑ ⟨x', hx'⟩) : IsConj x x' := by
  refine isConj_iff.mpr ⟨Y.ι ⟨k, hk⟩, ?_⟩
  have h1 : (⟨Y.ι ⟨k, hk⟩, Y.ι_mem_C _⟩ : ↥(Subgroup.centralizer ({z} : Set G))) * ⟨x, hx⟩ *
      (⟨Y.ι ⟨k, hk⟩, Y.ι_mem_C _⟩)⁻¹ = ⟨x', hx'⟩ := by
    apply Y.ϑ.injective
    apply Subtype.ext
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [show (Y.ϑ ⟨Y.ι ⟨k, hk⟩, Y.ι_mem_C _⟩ : Wr 6) = k from congrArg Subtype.val (Y.ϑ_ι _)]
    exact h
  exact congrArg Subtype.val h1

theorem vec_e04 : ∀ v : Fin 6 → ZMod 2,
    v6 [0, 4] + v + pact (swap 4 5) (v6 [0, 4]) = v + pact (swap 4 5) (v6 [4, 5]) := by decide

theorem eq_z_of_perm_one (hz : orderOf z = 2) (h3 : ¬ IsConj z Y.π3) (h12 : ¬ IsConj z Y.π12)
    {x : G} (hx : x ∈ Subgroup.centralizer ({z} : Set G)) (hzx : IsConj z x)
    (hp : (Y.ϑ ⟨x, hx⟩ : Wr 6).perm = 1) : x = z := by
  set W := (Y.ϑ ⟨x, hx⟩ : Wr 6) with hWdef
  have hWs : W ∈ Wsub := (Y.ϑ ⟨x, hx⟩).2
  have hW : W = ⟨W.vec, W.perm⟩ := rfl
  have hsum : ∑ i, W.vec i = 0 := hWs
  by_cases h1 : W.vec = fun _ => 1
  · apply Y.eq_of_ϑ_eq (hy := mem_centralizer_self' z)
    rw [Y.ϑ_z, ← hWdef, hW, h1, hp]
    rfl
  by_cases h0 : W.vec = 0
  · exfalso
    have hW1 : Y.ϑ ⟨x, hx⟩ = 1 := Subtype.ext (by
      show W = 1
      rw [hW, h0, hp]
      rfl)
    have hx1 : x = 1 := by
      have h2 := Y.ι_ϑ ⟨x, hx⟩
      rw [hW1, map_one] at h2
      exact h2.symm
    rw [hx1] at hzx
    have : z = 1 := isConj_one_left.mp hzx
    rw [this, orderOf_one] at hz
    omega
  exfalso
  obtain ⟨π, hπ⟩ := exists_perm_vec W.vec hsum h0 h1
  have hconj : wp π * W * (wp π)⁻¹ = ⟨pact π W.vec, 1⟩ := by
    rw [hW, conj_wp, hp, mul_one, mul_inv_cancel]
  rcases hπ with hπ | hπ
  · apply h3
    refine hzx.trans (Y.isConj_of_ϑ hx Y.π3_mem_C (wp_mem_Wsub π) ?_)
    rw [← hWdef, hconj, hπ, Y.ϑ_π3]
    rfl
  · apply h12
    refine hzx.trans (Y.isConj_of_ϑ hx Y.π12_mem_C (wp_mem_Wsub π) ?_)
    rw [← hWdef, hconj, hπ, Y.ϑ_π12]
    rfl

theorem centralizer_pi3_le (hchar : IsCharTwoType G) (P : Sylow 2 G) (hP : (P : Subgroup G) = Y.T)
    (hz : orderOf z = 2) (h3 : ¬ IsConj z Y.π3) (h12 : ¬ IsConj z Y.π12) :
    Subgroup.centralizer ({Y.π3} : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
  intro g hg
  obtain ⟨hx, hperm⟩ := Y.conj_z_perm hchar P hP hz (Or.inl rfl) hg
  have hzx : IsConj z (g * z * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
  have hfix : g * z * g⁻¹ = z := by
    rcases hperm with hσ | hσ
    · exact Y.eq_z_of_perm_one hz h3 h12 hx hzx hσ
    ·
      exfalso
      set x := g * z * g⁻¹ with hxdef
      set W := (Y.ϑ ⟨x, hx⟩ : Wr 6) with hWdef
      have hW : W = ⟨W.vec, W.perm⟩ := rfl
      have hxπ : x * Y.π3 ∈ Subgroup.centralizer ({z} : Set G) :=
        Subgroup.mul_mem _ hx Y.π3_mem_C
      have hu : (⟨v6 [0, 4], 1⟩ : Wr 6) ∈ Wsub := by show wsum (⟨v6 [0, 4], 1⟩ : Wr 6) = 0; decide
      have h1 : IsConj x (x * Y.π3) := by
        refine Y.isConj_of_ϑ hx hxπ hu ?_
        rw [Y.ϑ_mul_coe hx Y.π3_mem_C, Y.ϑ_π3, ← hWdef, conj_mkVec]
        conv_rhs => rw [hW]
        rw [hσ, vec_e04]
        rfl
      have hgπ : g * Y.π3 = Y.π3 * g := Subgroup.mem_centralizer_singleton_iff.mp hg
      have h2 : x * Y.π3 = g * Y.π12 * g⁻¹ := by
        rw [hxdef, ← Y.z_mul_π3]
        have hgi : g⁻¹ * Y.π3 = Y.π3 * g⁻¹ := by
          calc g⁻¹ * Y.π3 = g⁻¹ * (Y.π3 * g) * g⁻¹ := by group
            _ = g⁻¹ * (g * Y.π3) * g⁻¹ := by rw [hgπ]
            _ = Y.π3 * g⁻¹ := by group
        calc g * z * g⁻¹ * Y.π3 = g * z * (g⁻¹ * Y.π3) := by group
          _ = g * z * (Y.π3 * g⁻¹) := by rw [hgi]
          _ = g * (z * Y.π3) * g⁻¹ := by group
      apply h12
      refine (hzx.trans h1).trans ?_
      rw [h2]
      exact (isConj_iff.mpr ⟨g, rfl⟩).symm
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc g * z = (g * z * g⁻¹) * g := by group
    _ = z * g := by rw [hfix]

end YData

end CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki
