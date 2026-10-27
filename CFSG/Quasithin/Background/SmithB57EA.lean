module

public import CFSG.Quasithin.Background.FFC9J
public import CFSG.Quasithin.Background.SmithB57D
public import CFSG.Quasithin.Background.D2Z7
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin

namespace SmithB57E

open CFSG.Open CFSG.QuasithinUnique FFC
open scoped commutatorElement

variable {V : Type} [CommGroup V] [Finite V]

section Core

variable (G : Subgroup (MulAut V))

omit [Finite V] in
theorem pCore3_le : pCoreOf 3 G ≤ G := CFSG.openPCoreOf_le 3 G

theorem pCore3_isPGroup : IsPGroup 3 ↥(pCoreOf 3 G) :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 G

omit [Finite V] in
theorem le_normalizer_pCore3 : G ≤ Subgroup.normalizer (pCoreOf 3 G : Set (MulAut V)) :=
  CFSG.LieType.BorelTits.le_normalizer_pCoreOf 3 G

theorem pCore3_le_fitting : pCoreOf 3 G ≤ fittingOf G := by
  refine B56.le_fittingOf_of_nilpotent_normal (pCore3_le G) ?_ (pCore3_isPGroup G).isNilpotent
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (pCore3_le G)]
  exact le_normalizer_pCore3 G

end Core

structure Hyp (G L : Subgroup (MulAut V)) : Prop where
  hc : B56Counterex G
  hL : CFSG.Open.IsComponentOf L G
  h3 : ThreeRank2 ↥L
  hlayer : ∀ K : Subgroup (MulAut V), CFSG.Open.IsComponentOf K G → K = L
  hO3 : ¬ pCoreOf 3 G ≤ centerOf G

namespace Hyp

variable {G L : Subgroup (MulAut V)} (S : Hyp G L)
include S

theorem hV : ∀ v : V, v ^ 2 = 1 := S.hc.hV

theorem hO2 : pCoreOf 2 G = ⊥ := S.hc.hyp.1

theorem hJ : G = ffJ G := S.hc.hyp.2.1

theorem hq : IsQuotientOfSQTKTauCeti ↥G := isQuotientOfSQTKTauCeti_of_b53 S.hc.hyp

theorem hLq : CFSG.IsQuasisimple ↥L := B1Red.isQuasisimple_of_open S.hL.2.2

theorem hLG : L ≤ G := S.hL.1

theorem commute_X : ∀ x ∈ pCoreOf 3 G, ∀ l ∈ L, x * l = l * x := fun x hx l hl =>
  (SmithB57.comp_commute_fitting S.hL l hl x (pCore3_le_fitting G hx)).symm

theorem eq_one_of_inv_of_commute_X {s : MulAut V} (hs : s ∈ G) (hs2 : s * s = 1)
    (hsL : ∀ l ∈ L, s * l = l * s) (hsX : ∀ x ∈ pCoreOf 3 G, s * x = x * s) : s = 1 := by
  have hF : ∀ f ∈ fittingOf G, s * f = f * s := by
    have hle : fittingOf G ≤ Subgroup.centralizer ({s} : Set (MulAut V)) := by
      refine nilpotent_le_of_pCoreOf (fittingOf_le G) ?_ (fittingOf_nilpotent G) ?_
      · rw [Subgroup.normal_subgroupOf_iff_le_normalizer (fittingOf_le G)]
        intro g hg
        rw [Subgroup.mem_normalizer_iff]
        intro f
        refine ⟨fun hf => conj_mem_fittingOf hg hf, fun hf => ?_⟩
        have h := conj_mem_fittingOf (G.inv_mem hg) hf
        simpa [mul_assoc] using h
      · intro p hp
        by_cases h2 : p = 2
        · subst h2
          rw [S.hO2]
          exact bot_le
        by_cases h3 : p = 3
        · subst h3
          intro x hx
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (hsX x hx).symm
        · have : Fact p.Prime := ⟨hp⟩
          intro x hx
          have hxc := B55.pCoreOf_le_centralizer S.hV S.hJ h2 h3 hx
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_iff.1 hxc s hs).symm
    intro f hf
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hf)).symm
  refine SmithB57.eq_one_of_centralizes S.hO2 hs hs2 hF fun K hK x hx => ?_
  rw [S.hlayer K hK] at hx
  exact hsL x hx

end Hyp

section Inversion

variable {Ω : Type*} [Group Ω]

theorem exists_inv_of_order_prime {D : Subgroup Ω} {p : ℕ} (hp : p.Prime) (hDp : IsPGroup p ↥D)
    {a : Ω} (ha : a * a = 1) (haD : ∀ d ∈ D, a * d * a⁻¹ ∈ D)
    (hnc : ∃ x ∈ D, a * x ≠ x * a) : ∃ y ∈ D, orderOf y = p ∧ a * y * a⁻¹ = y⁻¹ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hxD, hxa⟩ := hnc
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  set w : Ω := x * a * x⁻¹ * a⁻¹ with hw
  have hwD : w ∈ D := by
    have : a * x⁻¹ * a⁻¹ ∈ D := haD _ (D.inv_mem hxD)
    have h2 := D.mul_mem hxD this
    simpa [hw, mul_assoc] using h2
  have hw1 : w ≠ 1 := by
    intro h
    apply hxa
    have : x * a * x⁻¹ * a⁻¹ = 1 := h
    have h' : x * a = a * x := by
      calc x * a = x * a * x⁻¹ * a⁻¹ * (a * x) := by group
        _ = a * x := by rw [this, one_mul]
    exact h'.symm
  have hwinv : a * w * a⁻¹ = w⁻¹ := by
    have e1 : w⁻¹ = a * x * a⁻¹ * x⁻¹ := by rw [hw]; group
    rw [e1, hw, hai]
    calc a * (x * a * x⁻¹ * a) * a = a * x * a * x⁻¹ * (a * a) := by group
      _ = a * x * a * x⁻¹ := by rw [ha, mul_one]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hDp) ⟨w, hwD⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hk
    exact hw1 hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  refine ⟨w ^ p ^ j, D.pow_mem hwD _, ?_, ?_⟩
  · rw [orderOf_pow_of_dvd (pow_ne_zero j hp.ne_zero)
      (by rw [hk]; exact pow_dvd_pow p (Nat.le_succ j)), hk, Nat.pow_div (Nat.le_succ j) hp.pos]
    simp
  · have h1 : a * w ^ p ^ j * a⁻¹ = (a * w * a⁻¹) ^ p ^ j := by
      rw [conj_pow]
    rw [h1, hwinv, inv_pow]

end Inversion

namespace Hyp

variable {G L : Subgroup (MulAut V)} (S : Hyp G L)
include S

theorem eq_one_of_inv_of_commute {s : MulAut V} (hs : s ∈ G) (hs2 : s * s = 1)
    (hsL : ∀ l ∈ L, s * l = l * s) : s = 1 := by
  by_contra hs1
  have hnc : ∃ x ∈ pCoreOf 3 G, s * x ≠ x * s := by
    by_contra hcon
    push Not at hcon
    exact hs1 (S.eq_one_of_inv_of_commute_X hs hs2 hsL hcon)
  have hsD : ∀ d ∈ pCoreOf 3 G, s * d * s⁻¹ ∈ pCoreOf 3 G := fun d hd =>
    (Subgroup.mem_normalizer_iff.1 ((le_normalizer_pCore3 G) hs) d).1 hd
  obtain ⟨c, hcX, hc3, hsc⟩ :=
    exists_inv_of_order_prime Nat.prime_three (pCore3_isPGroup G) hs2 hsD hnc
  obtain ⟨x, y, hx1, hx3, hy3, hxy, hyx⟩ := S.h3
  refine false_of_commuting_threes S.hq (t := s) (c := c) (x := (x : MulAut V))
    (y := (y : MulAut V)) hs ((pCore3_le G) hcX) (S.hLG x.2) (S.hLG y.2) hs2 hs1 ?_ ?_ hsc
    (fun h => hx1 (Subtype.ext h)) (by simpa using congrArg Subtype.val hx3)
    (by simpa using congrArg Subtype.val hy3) (congrArg Subtype.val hxy) ?_
    (hsL x x.2).symm (S.commute_X c hcX x x.2).symm (hsL y y.2).symm
    (S.commute_X c hcX y y.2).symm
  · rw [← hc3]
    exact pow_orderOf_eq_one c
  · intro h
    rw [h, orderOf_one] at hc3
    exact absurd hc3 (by norm_num)
  · intro hmem
    apply hyx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hmem
    exact Subgroup.mem_zpowers_iff.2 ⟨n, Subtype.ext (by simpa using hn)⟩

theorem odd_orderOf_of_commute {g : MulAut V} (hg : g ∈ G) (hgL : ∀ l ∈ L, g * l = l * g) :
    Odd (orderOf g) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨m, hm⟩ := hodd
  have hpos : 0 < orderOf g := orderOf_pos g
  set s := g ^ m with hsdef
  have hs2 : s * s = 1 := by
    rw [hsdef, ← pow_add, ← hm, pow_orderOf_eq_one]
  have hs1 : s ≠ 1 := by
    intro h
    have hle := orderOf_le_of_pow_eq_one (by omega) h
    omega
  apply hs1
  refine S.eq_one_of_inv_of_commute (G.pow_mem hg m) hs2 fun l hl => ?_
  exact ((Commute.pow_left (hgL l hl) m) : s * l = l * s)

theorem eq_bot_of_isPGroup_two {Q : Subgroup (MulAut V)} (hQ : IsPGroup 2 ↥Q) (hQG : Q ≤ G)
    (hQL : ∀ q ∈ Q, ∀ l ∈ L, q * l = l * q) : Q = ⊥ := by
  rw [eq_bot_iff]
  intro q hq
  have hodd := S.odd_orderOf_of_commute (hQG hq) (hQL q hq)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hQ) ⟨q, hq⟩
  rw [Subgroup.orderOf_mk] at hk
  rw [Subgroup.mem_bot, ← orderOf_eq_one_iff, hk]
  rcases k with _ | k
  · rfl
  · rw [hk, pow_succ] at hodd
    exact absurd hodd (by simp [Nat.odd_mul])

theorem eq_one_of_trivial_commV {x : MulAut V} (hx : x ∈ pCoreOf 3 G)
    (hxY : ∀ y ∈ commV (pCoreOf 3 G), x y = y) : x = 1 := by
  obtain ⟨hsup, -⟩ := isDirectSum_commV_fixV S.hV G
  ext v
  have hv : v ∈ commV (pCoreOf 3 G) ⊔ fixV (pCoreOf 3 G) := by
    rw [hsup]
    exact Subgroup.mem_top v
  obtain ⟨y, hy, w, hw, rfl⟩ := Subgroup.mem_sup.1 hv
  rw [map_mul, hxY y hy, (mem_fixV.1 hw) x hx, MulAut.one_apply]

theorem commute_X_of_trivial_commV {g : MulAut V} (hg : g ∈ G)
    (hgY : ∀ y ∈ commV (pCoreOf 3 G), g y = y) : ∀ x ∈ pCoreOf 3 G, g * x = x * g := by
  intro x hx
  have hc : g * x * g⁻¹ * x⁻¹ ∈ pCoreOf 3 G := by
    have h1 : g * x * g⁻¹ ∈ pCoreOf 3 G :=
      (Subgroup.mem_normalizer_iff.1 ((le_normalizer_pCore3 G) hg) x).1 hx
    exact (pCoreOf 3 G).mul_mem h1 ((pCoreOf 3 G).inv_mem hx)
  have hY : ∀ y ∈ commV (pCoreOf 3 G), (g * x * g⁻¹ * x⁻¹) y = y := by
    intro y hy
    have hxy : x⁻¹ y ∈ commV (pCoreOf 3 G) :=
      FFC.commV_invariant (fun z hz => by
        have : x⁻¹ * z * x⁻¹⁻¹ ∈ pCoreOf 3 G :=
          (pCoreOf 3 G).mul_mem ((pCoreOf 3 G).mul_mem ((pCoreOf 3 G).inv_mem hx) hz)
            ((pCoreOf 3 G).inv_mem ((pCoreOf 3 G).inv_mem hx))
        exact this) hy
    have hg' : g⁻¹ (x⁻¹ y) = x⁻¹ y := by
      conv_lhs => rw [← hgY _ hxy]
      simp
    simp only [MulAut.mul_apply, hg', MulAut.apply_inv_self, hgY y hy]
  have h1 := S.eq_one_of_trivial_commV hc hY
  have : g * x * g⁻¹ = x := by
    calc g * x * g⁻¹ = g * x * g⁻¹ * x⁻¹ * x := by group
      _ = x := by rw [h1, one_mul]
  calc g * x = g * x * g⁻¹ * g := by group
    _ = x * g := by rw [this]

end Hyp

end SmithB57E

end CFSG.Quasithin
