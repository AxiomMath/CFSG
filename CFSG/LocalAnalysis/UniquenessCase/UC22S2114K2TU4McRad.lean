module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114K2TU4McGen
import CFSG.LocalAnalysis.UniquenessCase.UC22P22e
import CFSG.LieType.BorelTits.Basic
import CFSG.Quasithin.Background.BlueprintB2Bridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open CFSG.Quasithin (IsMaxElemAbelian thompsonJ)
open scoped commutatorElement

variable {G : Type} [Group G]

theorem uc22mc_comm_jOf_le [Finite G] (D : Data G) {L : Subgroup G} (hML : D.M ≤ normalizer (L : Set G))
    (h : ∀ A : Subgroup G, IsMaxElemAbelian D.T A → ⁅A, L⁆ ≤ pCoreOf 2 L) :
    ⁅jOf D.T, L⁆ ≤ pCoreOf 2 L := by
  have hTN : D.T ≤ normalizer (pCoreOf 2 L : Set G) :=
    D.sylowM.le.trans (hML.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
  let K₀ : Subgroup G :=
    { carrier := {t | t ∈ normalizer (pCoreOf 2 L : Set G) ∧ ∀ l ∈ L, ⁅t, l⁆ ∈ pCoreOf 2 L}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun l hl => by
        have e : ⁅a * b, l⁆ = a * ⁅b, l⁆ * a⁻¹ * ⁅a, l⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact mul_mem ((mem_normalizer_iff.mp ha.1 _).mp (hb.2 l hl)) (ha.2 l hl)⟩
      one_mem' := ⟨one_mem _, fun l _ => by rw [commutatorElement_one_left]; exact one_mem _⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun l hl => by
        have e : ⁅a⁻¹, l⁆ = a⁻¹ * ⁅a, l⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (mem_normalizer_iff.mp (inv_mem ha.1) _).mp (inv_mem (ha.2 l hl))⟩ }
  have hJ : jOf D.T ≤ K₀ := by
    rw [show jOf D.T = thompsonJ D.T from CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ D.T]
    refine iSup₂_le fun A hA a ha => ?_
    exact ⟨hTN (hA.1 ha), fun l hl => h A hA (commutator_mem_commutator ha hl)⟩
  rw [commutator_le]
  intro j hj l hl
  exact (hJ hj).2 l hl

theorem uc22mc_exists_gen {B : Subgroup G} (hB : Nat.card B = 3) :
    ∃ b ∈ B, b ^ 3 = 1 ∧ ∀ x : G, x * b = b * x → x ∈ centralizer (B : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite B := Nat.finite_of_card_ne_zero (by omega)
  have hcyc : IsCyclic B := isCyclic_of_prime_card hB
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  refine ⟨g, g.2, ?_, fun x hx => ?_⟩
  · have h1 : g ^ Nat.card B = 1 := pow_card_eq_one'
    rw [hB] at h1
    simpa using congrArg Subtype.val h1
  · rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hg ⟨y, hy⟩)
    have hc : Commute x (g : G) := hx
    have hy' : y = (g : G) ^ k := by
      have := congrArg Subtype.val hk
      simpa using this.symm
    rw [hy']
    exact ((hc.zpow_right k).eq).symm

@[expose] def uc22mcRad (X U W : Subgroup G) (hXU : X ≤ normalizer (U : Set G)) :
    Subgroup G where
  carrier := {x | x ∈ X ∧ x ∈ centralizer (W : Set G) ∧ ∀ v ∈ U, x * v * x⁻¹ * v⁻¹ ∈ W}
  mul_mem' := fun {x y} hx hy => by
    refine ⟨X.mul_mem hx.1 hy.1, Subgroup.mul_mem _ hx.2.1 hy.2.1, fun v hv => ?_⟩
    have hv' : y * v * y⁻¹ ∈ U := (mem_normalizer_iff.mp (hXU hy.1) v).mp hv
    have e : x * y * v * (x * y)⁻¹ * v⁻¹ =
        (x * (y * v * y⁻¹) * x⁻¹ * (y * v * y⁻¹)⁻¹) * (y * v * y⁻¹ * v⁻¹) := by group
    rw [e]
    exact W.mul_mem (hx.2.2 _ hv') (hy.2.2 v hv)
  one_mem' := ⟨X.one_mem, Subgroup.one_mem _, fun v _ => by
    rw [one_mul, inv_one, mul_one, mul_inv_cancel]
    exact W.one_mem⟩
  inv_mem' := fun {x} hx => by
    refine ⟨X.inv_mem hx.1, Subgroup.inv_mem _ hx.2.1, fun v hv => ?_⟩
    have hv' : x⁻¹ * v * x⁻¹⁻¹ ∈ U := (mem_normalizer_iff.mp (hXU (X.inv_mem hx.1)) v).mp hv
    have h1 := hx.2.2 _ hv'
    have e : x⁻¹ * v * x⁻¹⁻¹ * v⁻¹ = (x * (x⁻¹ * v * x⁻¹⁻¹) * x⁻¹ * (x⁻¹ * v * x⁻¹⁻¹)⁻¹)⁻¹ := by
      group
    rw [e]
    exact W.inv_mem h1

theorem uc22mcRad_le {X U W : Subgroup G} {hXU : X ≤ normalizer (U : Set G)} :
    uc22mcRad X U W hXU ≤ X := fun _ hx => hx.1

theorem uc22mcRad_le_normalizer {X U W : Subgroup G} (hXU : X ≤ normalizer (U : Set G))
    (hXW : X ≤ normalizer (W : Set G)) : X ≤ normalizer (uc22mcRad X U W hXU : Set G) := by
  intro y hy
  rw [mem_normalizer_iff]
  have key : ∀ g ∈ X, ∀ x ∈ uc22mcRad X U W hXU, g * x * g⁻¹ ∈ uc22mcRad X U W hXU := by
    intro g hg x hx
    refine ⟨X.mul_mem (X.mul_mem hg hx.1) (X.inv_mem hg),
      uc22mc_conj_mem_centralizer (hXW hg) hx.2.1, fun v hv => ?_⟩
    have hv' : g⁻¹ * v * g⁻¹⁻¹ ∈ U := (mem_normalizer_iff.mp (hXU (X.inv_mem hg)) v).mp hv
    have h1 := hx.2.2 _ hv'
    have e : g * x * g⁻¹ * v * (g * x * g⁻¹)⁻¹ * v⁻¹ =
        g * (x * (g⁻¹ * v * g⁻¹⁻¹) * x⁻¹ * (g⁻¹ * v * g⁻¹⁻¹)⁻¹) * g⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.mp (hXW hg) _).mp h1
  intro x
  refine ⟨fun hx => key y hy x hx, fun hx => ?_⟩
  have := key y⁻¹ (X.inv_mem hy) _ hx
  simpa [mul_assoc] using this

theorem uc22mcRad_isPGroup {X U W : Subgroup G} (hXU : X ≤ normalizer (U : Set G))
    (hW2 : ∀ w ∈ W, w ^ 2 = 1) (hC : IsPGroup 2 ↥(X ⊓ centralizer (U : Set G))) :
    IsPGroup 2 ↥(uc22mcRad X U W hXU) := by
  intro x
  have hx := x.2
  have hsq : (x : G) ^ 2 ∈ X ⊓ centralizer (U : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨X.pow_mem hx.1 2, ?_⟩
    rw [mem_centralizer_iff]
    intro v hv
    have hw := hx.2.2 v hv
    set w := (x : G) * v * (x : G)⁻¹ * v⁻¹ with hwdef
    have hxw : (x : G) * w * (x : G)⁻¹ = w := by
      have := mem_centralizer_iff.mp hx.2.1 w hw
      rw [← this, mul_assoc, mul_inv_cancel, mul_one]
    have hxv : (x : G) * v * (x : G)⁻¹ = w * v := by rw [hwdef]; group
    have hww : w * w = 1 := by rw [← sq]; exact hW2 w hw
    have h1 : (x : G) ^ 2 * v * ((x : G) ^ 2)⁻¹ = v := by
      calc (x : G) ^ 2 * v * ((x : G) ^ 2)⁻¹ = (x : G) * ((x : G) * v * (x : G)⁻¹) * (x : G)⁻¹ := by
            rw [sq, mul_inv_rev]
            group
        _ = (x : G) * (w * v) * (x : G)⁻¹ := by rw [hxv]
        _ = ((x : G) * w * (x : G)⁻¹) * ((x : G) * v * (x : G)⁻¹) := by group
        _ = w * (w * v) := by rw [hxw, hxv]
        _ = v := by rw [← mul_assoc, hww, one_mul]
    calc v * (x : G) ^ 2 = ((x : G) ^ 2 * v * ((x : G) ^ 2)⁻¹) * (x : G) ^ 2 := by rw [h1]
      _ = (x : G) ^ 2 * v := by rw [mul_assoc, inv_mul_cancel, mul_one]
  obtain ⟨k, hk⟩ := hC ⟨_, hsq⟩
  refine ⟨k + 1, Subtype.ext ?_⟩
  have hk' : ((x : G) ^ 2) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  rw [Subgroup.coe_pow, Subgroup.coe_one, pow_succ', pow_mul, hk']

theorem uc22mc_mem_normalizer_map {U : Subgroup G} {WS : Subgroup ↥U} {x : G}
    (h1 : ∀ s ∈ WS, ∃ t ∈ WS, (t : G) = x * s * x⁻¹)
    (h2 : ∀ s ∈ WS, ∃ t ∈ WS, (t : G) = x⁻¹ * s * x) :
    x ∈ normalizer ((WS.map U.subtype : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨t, ht, hts⟩ := h1 s hs
    exact ⟨t, ht, hts⟩
  · rintro ⟨t, ht, hts⟩
    obtain ⟨s, hs, hst⟩ := h2 t ht
    refine ⟨s, hs, ?_⟩
    rw [Subgroup.coe_subtype] at hts ⊢
    rw [hst, hts]
    group

end CFSG.LocalAnalysis.UniquenessCase.UC22
