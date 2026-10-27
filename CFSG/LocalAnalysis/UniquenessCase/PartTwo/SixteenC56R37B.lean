module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Line
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenTwentyThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R34

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem centralizer_singleton_le_M_of_mem_V₀' (D : Data G) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) {z : G} (hzV₀ : z ∈ V₀) (hz : z ≠ 1) :
    centralizer ({z} : Set G) ≤ D.M := by
  have hXV : Subgroup.zpowers z ≤ V₀ := Subgroup.zpowers_le.2 hzV₀
  have hX1 : Subgroup.zpowers z ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hz
  have hN := h.hyp62.normalizer_le _ hXV hX1
  have hcent_eq : centralizer ({z} : Set G) = centralizer (Subgroup.zpowers z : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  exact ((le_of_eq hcent_eq).trans (Subgroup.centralizer_le_normalizer _)).trans hN

theorem card_preTil {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V)
    (P : Subgroup (Vtil V₀ V hV)) :
    Nat.card ↥(preTil V₀ V hV P) = Nat.card ↥V₀ * Nat.card ↥P := by
  have hinj : Function.Injective (valHom V hV) := fun _ _ h => IntMod.val_injective h
  have hmap : Nat.card ↥(preTil V₀ V hV P) = Nat.card ↥(P.comap (mkTil V₀ V hV)) := by
    unfold preTil
    exact Subgroup.card_map_of_injective hinj
  have hindex : (P.comap (mkTil V₀ V hV)).index = P.index :=
    Subgroup.index_comap_of_surjective (H := P) (mkTil_surjective V₀ V hV)
  have hker : (mkTil V₀ V hV).ker = modNull V₀ V hV := by
    unfold mkTil
    exact QuotientGroup.ker_mk' (N := modNull V₀ V hV)
  have hkercard : Nat.card ↥(mkTil V₀ V hV).ker = Nat.card ↥V₀ := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV₀).toEquiv
  have h1 : Nat.card ↥(P.comap (mkTil V₀ V hV)) * (P.comap (mkTil V₀ V hV)).index =
      Nat.card (IntMod V hV) := Subgroup.card_mul_index (H := P.comap (mkTil V₀ V hV))
  have h2 : Nat.card ↥(mkTil V₀ V hV).ker * Nat.card (Vtil V₀ V hV) =
      Nat.card (IntMod V hV) :=
    Subgroup.card_ker_mul_card_of_surjective (mkTil_surjective V₀ V hV)
  have h3 : Nat.card (Vtil V₀ V hV) = Nat.card ↥P * P.index :=
    (Subgroup.card_mul_index (H := P)).symm
  have hpos : 0 < P.index := by
    haveI : Nonempty (Vtil V₀ V hV ⧸ P) := ⟨1⟩
    rw [Subgroup.index]
    exact Nat.card_pos
  rw [hmap]
  apply Nat.mul_right_cancel hpos
  calc Nat.card ↥(P.comap (mkTil V₀ V hV)) * P.index
      = Nat.card ↥(P.comap (mkTil V₀ V hV)) * (P.comap (mkTil V₀ V hV)).index := by
        rw [hindex]
    _ = Nat.card (IntMod V hV) := h1
    _ = Nat.card ↥(mkTil V₀ V hV).ker * Nat.card (Vtil V₀ V hV) := h2.symm
    _ = Nat.card ↥V₀ * (Nat.card ↥P * P.index) := by rw [hkercard, h3]
    _ = Nat.card ↥V₀ * Nat.card ↥P * P.index := by rw [mul_assoc]

theorem commutator_mem_V₀_of_fixes {V₀ V B : Subgroup G} {hV : IsElemAbelian 2 V}
    (hBst : B ≤ stabTil V₀ V) {q : Vtil V₀ V hV}
    (hq : ∀ φ ∈ barSub V₀ V hV B, φ q = q) {x : G} (hxV : x ∈ V)
    (hxq : mkTil V₀ V hV (IntMod.mk hV ⟨x, hxV⟩) = q) : ∀ a ∈ B, ⁅x, a⁆ ∈ V₀ := by
  intro a ha
  have hs : a ∈ stabTil V₀ V := hBst ha
  let xi : IntMod V hV := IntMod.mk hV ⟨x, hxV⟩
  have hxq' : mkTil V₀ V hV xi = q := hxq
  have hfix : actTil V₀ V hV ⟨a, hs⟩ q = q :=
    hq (actTil V₀ V hV ⟨a, hs⟩) (actTil_mem_barSub V₀ V hV ha hs)
  have h1 : mkTil V₀ V hV (actStab V₀ V hV ⟨a, hs⟩ xi) = mkTil V₀ V hV xi := by
    calc mkTil V₀ V hV (actStab V₀ V hV ⟨a, hs⟩ xi)
        = actTil V₀ V hV ⟨a, hs⟩ (mkTil V₀ V hV xi) :=
          (actTil_mk V₀ V hV ⟨a, hs⟩ xi).symm
      _ = actTil V₀ V hV ⟨a, hs⟩ q := by rw [hxq']
      _ = q := hfix
      _ = mkTil V₀ V hV xi := hxq'.symm
  rw [mkTil_eq_iff, actStab_apply_val] at h1
  change ⁅xi.val, a⁆ ∈ V₀
  rw [commutatorElement_def]
  convert V₀.inv_mem h1 using 1
  group

theorem centralizer_le_M_of_mem_preTil_line (D : Data G) (h61 : UC6.R6_1 D) (hext : DataExt D)
    (h5 : R16_5 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    {m : ℕ} (hm : Case1633 D V₀ V hV L m) (S : OmegaModel (Vtil V₀ V hV))
    (hSω : S.omega = lBar V₀ V hV L) (hSK : Nat.card S.K = 2 ^ m) {p : ℕ} (hp : D.sig = {p})
    {e : Vtil V₀ V hV} (hQ : S.Q e ≠ 0) {x : G} (hx : x ∈ preTil V₀ V hV (S.line e))
    (hx1 : x ≠ 1) : centralizer ({x} : Set G) ≤ D.M := by
  have hxV : x ∈ V := preTil_le V₀ V hV _ hx
  let xi : IntMod V hV := IntMod.mk hV ⟨x, hxV⟩
  by_cases hx0 : x ∈ V₀
  · exact centralizer_singleton_le_M_of_mem_V₀' D hS.setting.hyp16.hyp125 hx0 hx1
  · have hxline : mkTil V₀ V hV xi ∈ S.line e :=
      (mem_preTil_iff_of_mem V₀ V hV _ hxV).1 hx
    have hxi1 : mkTil V₀ V hV xi ≠ 1 := fun h =>
      hx0 ((mem_modNull V₀ V hV xi).1
        ((QuotientGroup.eq_one_iff (N := modNull V₀ V hV) xi).1 h))
    have hQne : S.Q (mkTil V₀ V hV xi) ≠ 0 := S.Q_ne_zero_of_mem_line hQ hxline hxi1
    exact (r16_34_coord D h61 hext h5 hS hm S hSω hSK hp (x := xi) hQne).2

theorem exists_subgroup_of_line (D : Data G) (h61 : UC6.R6_1 D) (hext : DataExt D)
    (h5 : R16_5 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    {m : ℕ} (hm : Case1633 D V₀ V hV L m) (S : OmegaModel (Vtil V₀ V hV))
    (hSω : S.omega = lBar V₀ V hV L) (hSK : Nat.card S.K = 2 ^ m) {p : ℕ} (hp : D.sig = {p})
    {B : Subgroup G} (hBst : B ≤ stabTil V₀ V)
    (hcB : ∀ v ∈ V, (∀ a ∈ B, ⁅v, a⁆ ∈ V₀) → v ∈ centralizer (B : Set G))
    {e : Vtil V₀ V hV} (hQ : S.Q e ≠ 0)
    (hfix : ∀ φ ∈ barSub V₀ V hV B, ∀ c : S.K, φ (S.smul c e) = S.smul c e) :
    ∃ E : Subgroup G, E ≤ V ∧ E ≤ centralizer (B : Set G) ∧
      Nat.card ↥E = Nat.card ↥V₀ * Nat.card S.K ∧
      ∀ x ∈ E, x ≠ 1 → centralizer ({x} : Set G) ≤ D.M := by
  have hP : PairFacts D.M V₀ V := hS.setting.hyp16.hyp125.pairFacts
  have he1 : e ≠ 1 := fun h => hQ (by rw [h, S.Q_one])
  refine ⟨preTil V₀ V hV (S.line e), preTil_le V₀ V hV _, ?_, ?_, ?_⟩
  · intro x hx
    have hxV : x ∈ V := preTil_le V₀ V hV _ hx
    have hxl : mkTil V₀ V hV (IntMod.mk hV ⟨x, hxV⟩) ∈ S.line e :=
      (mem_preTil_iff_of_mem V₀ V hV _ hxV).1 hx
    obtain ⟨c, hc⟩ := hxl
    refine hcB x hxV (commutator_mem_V₀_of_fixes hBst
      (q := mkTil V₀ V hV (IntMod.mk hV ⟨x, hxV⟩)) (fun φ hφ => ?_) hxV rfl)
    rw [hc]
    exact hfix φ hφ c
  · rw [card_preTil hV hP.le, S.card_line he1]
  · intro x hx hx1
    exact centralizer_le_M_of_mem_preTil_line D h61 hext h5 hS hm S hSω hSK hp hQ hx hx1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
