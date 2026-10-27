module

public import CFSG.RankThree.PartTwo.Sec8.Steps
public import CFSG.RankThree.PartTwo.Sec8.TransferExtremal
public import CFSG.RankThree.PartTwo.Sec8.Item812ProofOut
public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

section Steps

variable {G : Type*} [Group G]

theorem le_centralizer_of_mem_thetaComponentsAt_three {Y : Subgroup G} {a : G}
    (hY : Y ∈ thetaComponentsAt 3 a) : Y ≤ Subgroup.centralizer ({a} : Set G) := by
  obtain ⟨Y', -, rfl⟩ := hY
  exact Subgroup.map_subtype_le Y'

theorem conj_mem_zpowers_of_conj_eq_inv {h a : G} (hh : h * a * h⁻¹ = a⁻¹) {x : G}
    (hx : x ∈ Subgroup.zpowers a) : h * x * h⁻¹ ∈ Subgroup.zpowers a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← conj_zpow, hh]
  exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers a)) k

theorem mem_normalizer_zpowers_of_conj_eq_inv {g a : G} (h : g⁻¹ * a * g = a⁻¹) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
  have h' : g * a * g⁻¹ = a⁻¹ := by
    have ha : a = g * a⁻¹ * g⁻¹ := by
      rw [← h]
      group
    calc g * a * g⁻¹ = (g * a⁻¹ * g⁻¹)⁻¹ := by group
      _ = a⁻¹ := by rw [← ha]
  have h'' : g⁻¹ * a * g⁻¹⁻¹ = a⁻¹ := by rwa [inv_inv]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_zpowers_of_conj_eq_inv h', fun hx => ?_⟩
  have := conj_mem_zpowers_of_conj_eq_inv h'' hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

theorem card_inf_centralizer_le_of_conj [Finite G] {P : Subgroup G} {a g : G}
    (hg : ∀ y ∈ P ⊓ Subgroup.centralizer {a}, g⁻¹ * y * g ∈ P) :
    Nat.card (P ⊓ Subgroup.centralizer {a} : Subgroup G) ≤
      Nat.card (P ⊓ Subgroup.centralizer {g⁻¹ * a * g} : Subgroup G) := by
  set D := P ⊓ Subgroup.centralizer {a}
  have hle : D.map (MulAut.conj g⁻¹).toMonoidHom ≤
      P ⊓ Subgroup.centralizer {g⁻¹ * a * g} := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y * a = a * y :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hy).2
    have hconj : (MulAut.conj g⁻¹).toMonoidHom y = g⁻¹ * y * g := by
      simp
    rw [hconj, Subgroup.mem_inf]
    refine ⟨hg y hy, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc g⁻¹ * y * g * (g⁻¹ * a * g) = g⁻¹ * (y * a) * g := by group
        _ = g⁻¹ * (a * y) * g := by rw [hy']
        _ = g⁻¹ * a * g * (g⁻¹ * y * g) := by group
  calc Nat.card D = Nat.card (D.map (MulAut.conj g⁻¹).toMonoidHom) :=
        (Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective).symm
    _ ≤ _ := Subgroup.card_le_of_le hle

theorem centralizer_singleton_eq_of_zpowers_eq {x w : G}
    (h : Subgroup.zpowers x = Subgroup.zpowers w) :
    Subgroup.centralizer ({x} : Set G) = Subgroup.centralizer ({w} : Set G) := by
  have hx : Subgroup.centralizer ({x} : Set G) =
      Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hw : Subgroup.centralizer ({w} : Set G) =
      Subgroup.centralizer (Subgroup.zpowers w : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hx, hw, h]

theorem extremal_of_fusion [Finite G] {P R V : Subgroup G} {a : G} (hRP : R ≤ P)
    (ha3 : a ^ 3 = 1) (hV : ∀ g : G, g⁻¹ * a * g ∉ V)
    (hfus : ∀ z ∈ P, z ^ 3 = 1 → z ∉ V → ∃ r ∈ R, r * z * r⁻¹ ∈ Subgroup.zpowers a ∨
      ∃ w ∈ P, Subgroup.zpowers (r * z * r⁻¹) = Subgroup.zpowers w ∧
        Nat.card (P ⊓ Subgroup.centralizer {w} : Subgroup G) <
          Nat.card (P ⊓ Subgroup.centralizer {a} : Subgroup G))
    (g : G) (hg : g⁻¹ * a * g ∈ P)
    (hcard : Nat.card (P ⊓ Subgroup.centralizer {a} : Subgroup G) ≤
      Nat.card (P ⊓ Subgroup.centralizer {g⁻¹ * a * g} : Subgroup G)) :
    ∃ r ∈ R, r * (g⁻¹ * a * g) * r⁻¹ ∈ Subgroup.zpowers a := by
  have hz3 : (g⁻¹ * a * g) ^ 3 = 1 := by
    have h := conj_pow (a := g⁻¹) (b := a) (i := 3)
    rw [inv_inv] at h
    rw [h, ha3]
    group
  obtain ⟨r, hr, h | ⟨w, -, hw, hlt⟩⟩ := hfus _ hg hz3 (hV g)
  · exact ⟨r, hr, h⟩
  · exfalso
    have hrP : r ∈ P := hRP hr
    have hle := card_inf_centralizer_le_of_conj (P := P) (a := g⁻¹ * a * g) (g := r⁻¹)
      (fun y hy => by
        rw [inv_inv]
        exact P.mul_mem (P.mul_mem hrP (Subgroup.mem_inf.mp hy).1) (P.inv_mem hrP))
    rw [inv_inv, centralizer_singleton_eq_of_zpowers_eq hw] at hle
    omega

theorem eq_inv_of_mem_zpowers_of_mul_mem {V : Subgroup G} {a u : G} (ha3 : a ^ 3 = 1)
    (haV : a ∉ V) (hu : u ∈ Subgroup.zpowers a) (hau : a * u ∈ V) : u = a⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  have hk : a ^ k = a ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3, zpow_add, zpow_mul]
    rw [show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, ha3, one_zpow, mul_one]
  rw [hk] at hau ⊢
  obtain h | h | h : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  · rw [h, zpow_zero, mul_one] at hau
    exact absurd hau haV
  · rw [h, zpow_one] at hau
    refine absurd ?_ haV
    have e : a = (a * a) * (a * a) * (a ^ 3)⁻¹ := by group
    rw [e, ha3, inv_one, mul_one]
    exact V.mul_mem hau hau
  · rw [h]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← ha3]
    group

theorem exists_conj_eq_inv_of_extremal [Finite G] (hperf : commutator G = ⊤) (P : Sylow 3 G)
    {R V : Subgroup G} {a : G} (haP : a ∈ (P : Subgroup G)) (ha3 : a ^ 3 = 1) (hRV : R ≤ V)
    (hVP : V ≤ P)
    (habel : ∀ x ∈ (P : Subgroup G), ∀ y ∈ (P : Subgroup G), x * y * x⁻¹ * y⁻¹ ∈ V)
    (hcos : ∀ x ∈ (P : Subgroup G), x ∈ V ∨ a⁻¹ * x ∈ V ∨ a * x ∈ V)
    (hV : ∀ g : G, g⁻¹ * a * g ∉ V)
    (hext : ∀ g : G, g⁻¹ * a * g ∈ (P : Subgroup G) →
      Nat.card ((P : Subgroup G) ⊓ Subgroup.centralizer {a} : Subgroup G) ≤
        Nat.card ((P : Subgroup G) ⊓ Subgroup.centralizer {g⁻¹ * a * g} : Subgroup G) →
      ∃ r ∈ R, r * (g⁻¹ * a * g) * r⁻¹ ∈ Subgroup.zpowers a) :
    ∃ g : G, g⁻¹ * a * g = a⁻¹ := by
  have haV : a ∉ V := by simpa using hV 1
  by_contra hno'
  have hno : ∀ g : G, g⁻¹ * a * g ≠ a⁻¹ := not_exists.mp hno'
  refine commutator_ne_top_of_extremal P habel haP haV ha3 (fun g hg => ?_) hperf
  by_contra hgV
  have ht : g⁻¹ * a * g ∈ (P : Subgroup G) :=
    hg a ⟨haP, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hat : a * (g⁻¹ * a * g) ∈ V := by
    rcases hcos _ ht with h | h | h
    · exact absurd h (hV g)
    · exact absurd h hgV
    · exact h
  obtain ⟨r, hrR, hr⟩ := hext g ht (card_inf_centralizer_le_of_conj hg)
  have hrP : r ∈ (P : Subgroup G) := hVP (hRV hrR)
  have hau : a * (r * (g⁻¹ * a * g) * r⁻¹) ∈ V := by
    have h1 := habel a haP r hrP
    have h2 : r * (a * (g⁻¹ * a * g)) * r⁻¹ ∈ V := by
      have h3 := habel r hrP _ (hVP hat)
      have e : r * (a * (g⁻¹ * a * g)) * r⁻¹ =
          r * (a * (g⁻¹ * a * g)) * r⁻¹ * (a * (g⁻¹ * a * g))⁻¹ * (a * (g⁻¹ * a * g)) := by
        group
      rw [e]
      exact V.mul_mem h3 hat
    have e : a * (r * (g⁻¹ * a * g) * r⁻¹) =
        a * r * a⁻¹ * r⁻¹ * (r * (a * (g⁻¹ * a * g)) * r⁻¹) := by
      group
    rw [e]
    exact V.mul_mem h1 h2
  have hu : r * (g⁻¹ * a * g) * r⁻¹ = a⁻¹ := eq_inv_of_mem_zpowers_of_mul_mem ha3 haV hr hau
  exact hno (g * r⁻¹) (by rw [← hu]; group)

theorem not_inducesOuterTheta_of_conj_eq_inv_of_frattini [Finite G] {X Y : Subgroup G}
    {a b g : G} {m : ℕ} (hm : 1 ≤ m)
    (hX : Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSp 2 (GaloisField 2 m)))
    (ha3 : a ^ 3 = 1) (hYa : Y ≤ Subgroup.centralizer ({a} : Set G))
    (hFr : ∀ g ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G), ∃ y ∈ Y,
      ∃ k ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G) ⊓
        Subgroup.normalizer (Subgroup.zpowers b : Set G), g = y * k)
    (hXN : Subgroup.normalizer (Subgroup.zpowers b : Set G) ≤
      Subgroup.normalizer (X : Set G))
    (hg : g⁻¹ * a * g = a⁻¹) : ¬ InducesOuterTheta a X := by
  obtain ⟨y, hy, k, hk, rfl⟩ := hFr g (mem_normalizer_zpowers_of_conj_eq_inv hg)
  have hya : y * a = a * y := Subgroup.mem_centralizer_singleton_iff.mp (hYa hy)
  have hka : k⁻¹ * a * k = a⁻¹ := by
    have e : k⁻¹ * a * k = (y * k)⁻¹ * a * (y * k) := by
      calc k⁻¹ * a * k = k⁻¹ * y⁻¹ * (y * a) * k := by group
        _ = k⁻¹ * y⁻¹ * (a * y) * k := by rw [hya]
        _ = (y * k)⁻¹ * a * (y * k) := by group
    rw [e, hg]
  exact not_inducesOuterTheta_of_conj_eq_inv_of_projSp hm hX (hXN hk.2) ha3 hka

theorem commutator_eq_top_of_theoremFourHyp {G : Type} [Group G] [Finite G]
    (hG : TheoremFourHyp G) : commutator G = ⊤ := by
  have := hG.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · obtain ⟨x, y, hxy⟩ := hG.nonabelian
    exact absurd ((commutator_eq_bot_iff G).mp h) fun hc => hxy (hc.is_comm.comm x y)
  · exact h

end Steps

section Final


structure Sec8Final (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G)
    (a b : G) (X Y : Subgroup G) (n : ℕ) : Prop extends Sec8Pair G A c L a b X n where
  mem_thetaComponentsAt_Y : Y ∈ thetaComponentsAt 3 a
  le_Y : sec8I L a ⊔ sec8J X a ≤ Y
  item88 : ¬ (KFacts.InducesStdKind Y c .field ∨ KFacts.InducesStdKind Y c .graphField) ∧
    ¬ (KFacts.InducesStdKind Y b .field ∨ KFacts.InducesStdKind Y b .graphField)
  item89_X : Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSp 2 (GaloisField 2 3))
  item89_Y : Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* alternatingGroup (Fin 9)) ∨
    Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* projSp 3 (GaloisField 2 1))
  item89_omega : ∀ p ∈ pairOmega A, IsUnitaryTwo (p.2 ⧸ aschbacherSolvableCore 3 p.2) 3 ∨
    Nonempty (p.2 ⧸ aschbacherSolvableCore 3 p.2 ≃* projSp 2 (GaloisField 2 3))
  item810 : ∀ e ∈ sec8B A X, e ∉ Subgroup.zpowers b → e ∈ gammaSet A X
  item811 : ∀ (e : G) (Le : Subgroup G), PairRel A e Le b X → sec8B A X = sec8B A Le

@[expose] def Fin812Sylow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X Y : Subgroup G) (n : ℕ), Sec8Final G A c L a b X Y n →
    ∃ (P : Sylow 3 G) (R V : Subgroup G), a ∈ (P : Subgroup G) ∧ R ≤ V ∧
      V ≤ (P : Subgroup G) ∧
      (∀ x ∈ (P : Subgroup G), ∀ y ∈ (P : Subgroup G), x * y * x⁻¹ * y⁻¹ ∈ V) ∧
      (∀ x ∈ (P : Subgroup G), x ∈ V ∨ a⁻¹ * x ∈ V ∨ a * x ∈ V) ∧
      (∀ g : G, g⁻¹ * a * g ∉ V) ∧
      ∀ z ∈ (P : Subgroup G), z ^ 3 = 1 → z ∉ V → ∃ r ∈ R,
        r * z * r⁻¹ ∈ Subgroup.zpowers a ∨
          ∃ w ∈ (P : Subgroup G), Subgroup.zpowers (r * z * r⁻¹) = Subgroup.zpowers w ∧
            Nat.card ((P : Subgroup G) ⊓ Subgroup.centralizer {w} : Subgroup G) <
              Nat.card ((P : Subgroup G) ⊓ Subgroup.centralizer {a} : Subgroup G)

@[expose] def Fin812Frattini : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X Y : Subgroup G) (n : ℕ), Sec8Final G A c L a b X Y n →
    ∀ g ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G), ∃ y ∈ Y,
      ∃ k ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G) ⊓
        Subgroup.normalizer (Subgroup.zpowers b : Set G), g = y * k

@[expose] def Fin812XNormal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X Y : Subgroup G) (n : ℕ), Sec8Final G A c L a b X Y n →
    Subgroup.normalizer (Subgroup.zpowers b : Set G) ≤ Subgroup.normalizer (X : Set G)

@[expose] def Pair84A : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    KFacts.InducesStdKind X a .field ∨ KFacts.InducesStdKind X a .graphField

theorem exists_sec8Final_of (h87 : Item87) (h88 : Item88) (h89 : Item89) (h810 : Item810)
    (h811 : Item811) {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}
    {a b : G} {X : Subgroup G} {n : ℕ} (h : Sec8Pair G A c L a b X n) :
    ∃ Y : Subgroup G, Sec8Final G A c L a b X Y n := by
  obtain ⟨Y, hY, hIJ⟩ := h87 G A c L a b X n h
  obtain ⟨hX, hY', hΩ⟩ := h89 G A c L a b X n h Y hY hIJ
  exact ⟨Y, { h with
    mem_thetaComponentsAt_Y := hY
    le_Y := hIJ
    item88 := h88 G A c L a b X n h Y hY hIJ
    item89_X := hX
    item89_Y := hY'
    item89_omega := hΩ
    item810 := h810 G A c L a b X n h
    item811 := h811 G A c L a b X n h }⟩

theorem Sec8Final.false (hS : Fin812Sylow) (hF : Fin812Frattini) (hXN : Fin812XNormal)
    (h84 : Pair84A) {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}
    {a b : G} {X Y : Subgroup G} {n : ℕ} (h : Sec8Final G A c L a b X Y n) : False := by
  obtain ⟨P, R, V, haP, hRV, hVP, habel, hcos, hV, hfus⟩ := hS G A c L a b X Y n h
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hperf := commutator_eq_top_of_theoremFourHyp h.toTheoremFourHyp
  obtain ⟨g, hg⟩ := exists_conj_eq_inv_of_extremal hperf P haP ha3 hRV hVP habel hcos hV
    (extremal_of_fusion (hRV.trans hVP) ha3 hV hfus)
  have hout : InducesOuterTheta a X := by
    rcases h84 G A c L a b X n h.toSec8Pair with h' | h'
    · exact KFacts.InducesStdKind.inducesOuterTheta X h' (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta X h' (by decide)
  exact not_inducesOuterTheta_of_conj_eq_inv_of_frattini (by norm_num) h.item89_X ha3
    (le_centralizer_of_mem_thetaComponentsAt_three h.mem_thetaComponentsAt_Y)
    (hF G A c L a b X Y n h) (hXN G A c L a b X Y n h) hg hout

theorem sec8Never_of (h87 : Item87) (h88 : Item88) (h89 : Item89) (h810 : Item810)
    (h811 : Item811) (hS : Fin812Sylow) (hF : Fin812Frattini) (hXN : Fin812XNormal)
    (h84 : Pair84A) : Sec8Never := by
  intro G _ _ A c L a b X n h
  obtain ⟨Y, hY⟩ := exists_sec8Final_of h87 h88 h89 h810 h811 h
  exact hY.false hS hF hXN h84

end Final

end CFSG.RankThree.PartTwo.Sec8
