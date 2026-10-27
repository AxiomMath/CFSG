module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearModelSubgroupTorus

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearModel

open CFSG.BenderSuzuki.MatrixGroups
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth

universe u

variable {K : Type u} [Field K] [Finite K]

theorem inverted_odd_centralizer_torus (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card K = 2 ^ f)
    (A : Subgroup (PSL2MatrixGroup K)) {u y : A} (hu : orderOf u = 2) (hy : y ≠ 1)
    (hyodd : Odd (orderOf y)) (huy : u * y * u⁻¹ = y⁻¹) :
    Subgroup.centralizer ({y} : Set A) ≠ ⊥ ∧ IsCyclic (Subgroup.centralizer ({y} : Set A)) ∧
    Odd (Nat.card (Subgroup.centralizer ({y} : Set A))) ∧
    (∀ w ∈ Subgroup.centralizer ({y} : Set A), u * w * u⁻¹ = w⁻¹) ∧
    Subgroup.centralizer ({y} : Set A) ⊓ Subgroup.zpowers u = ⊥ ∧
    ∀ W₀ : Subgroup A, W₀ ≤ Subgroup.centralizer ({y} : Set A) → W₀ ≠ ⊥ →
      Subgroup.centralizer (W₀ : Set A) = Subgroup.centralizer ({y} : Set A) ∧
      Subgroup.normalizer (W₀ : Set A) =
        Subgroup.centralizer ({y} : Set A) ⊔ Subgroup.zpowers u := by
  set W := Subgroup.centralizer ({y} : Set A) with hWdef
  set D := Subgroup.centralizer ({(y : PSL2MatrixGroup K)} : Set (PSL2MatrixGroup K))
    with hDdef
  have hyL : (y : PSL2MatrixGroup K) ≠ 1 := fun h => hy (Subtype.ext h)
  have hyLodd : Odd (orderOf (y : PSL2MatrixGroup K)) := (Subgroup.orderOf_coe y).symm ▸ hyodd
  obtain ⟨hDcyc, hDcard, hDinv⟩ :=
    psl2_even_odd_element_full_centralizer f hf hcard _ hyL hyLodd
  let : IsCyclic D := hDcyc
  have hmemW : ∀ a : A, a ∈ W ↔ (a : PSL2MatrixGroup K) ∈ D := by
    intro a
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hKeven : Even (Nat.card K) := by
    rw [hcard]
    exact even_two.pow_of_ne_zero (by omega)
  have hDodd : Odd (Nat.card D) := by
    rcases hDcard with h | h <;> rw [h]
    · exact Nat.Even.sub_odd Nat.card_pos hKeven odd_one
    · exact hKeven.add_odd odd_one
  let ι : W →* D :=
    { toFun := fun a => ⟨(a : A), (hmemW a).mp a.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun a b h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : D => (z : PSL2MatrixGroup K)) h))
  have hWcyc : IsCyclic W := isCyclic_of_injective ι hι
  have hWodd : Odd (Nat.card W) := hDodd.of_dvd_nat (Subgroup.card_dvd_of_injective ι hι)
  have huL : (u : PSL2MatrixGroup K) * y * (u : PSL2MatrixGroup K)⁻¹ =
      (y : PSL2MatrixGroup K)⁻¹ := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using congrArg Subtype.val huy
  have hWinv : ∀ w ∈ W, u * w * u⁻¹ = w⁻¹ := by
    intro w hw
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      hDinv (u : PSL2MatrixGroup K) huL (w : PSL2MatrixGroup K) ((hmemW w).mp hw)
  have hyW : y ∈ W := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hWne : W ≠ ⊥ := fun h => hy (by rw [h] at hyW; exact hyW)
  have hWodd_elt : ∀ x ∈ W, Odd (orderOf x) := by
    intro x hx
    have h := orderOf_dvd_natCard (⟨x, hx⟩ : W)
    rw [Subgroup.orderOf_mk] at h
    exact hWodd.of_dvd_nat h
  have hu2' : u ^ 2 = 1 := by
    have h := pow_orderOf_eq_one u
    rwa [hu] at h
  have hu2 : u * u = 1 := by rw [← pow_two, hu2']
  have hWu : W ⊓ Subgroup.zpowers u = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxW, hxu⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxu
    have hsq : (u ^ k) ^ 2 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu2', one_zpow]
    have hdvd : orderOf (u ^ k) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    have h1 : orderOf (u ^ k) = 1 :=
      (hWodd_elt _ hxW).coprime_two_right.eq_one_of_dvd hdvd
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h1)
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
    intro a ha b hb
    have h := (IsCyclic.isMulCommutative (α := W)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val h
  refine ⟨hWne, hWcyc, hWodd, hWinv, hWu, ?_⟩
  intro W₀ hW₀ hW₀1
  set R := W₀.map A.subtype
  have hRD : R ≤ D := by
    rintro _ ⟨a, ha, rfl⟩
    exact (hmemW a).mp (hW₀ ha)
  have hR1 : R ≠ ⊥ := fun h => hW₀1 ((Subgroup.map_eq_bot_iff_of_injective W₀
    A.subtype_injective).mp h)
  have hdich : ∀ g ∈ Subgroup.normalizer (W₀ : Set A),
      g ∈ W ∨ ∀ z ∈ W, g * z * g⁻¹ = z⁻¹ := by
    intro g hg
    have hgL : (g : PSL2MatrixGroup K) ∈ Subgroup.normalizer (R : Set (PSL2MatrixGroup K)) :=
      Subgroup.le_normalizer_map A.subtype (Subgroup.mem_map_of_mem A.subtype hg)
    rcases psl2_even_odd_torus_normalizer_dichotomy f hf hcard _ hyL hyLodd R hRD hR1 hgL with
      hgD | hgD
    · exact Or.inl ((hmemW g).mpr hgD)
    · refine Or.inr fun z hz => Subtype.ext ?_
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hgD _ ((hmemW z).mp hz)
  have hWC : W ≤ Subgroup.centralizer (W₀ : Set A) := fun w hw =>
    Subgroup.mem_centralizer_iff.mpr fun x hx => hWcomm x (hW₀ hx) w hw
  have hCN : Subgroup.centralizer (W₀ : Set A) ≤ Subgroup.normalizer (W₀ : Set A) :=
    Subgroup.centralizer_le_normalizer _
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW₀1
  have hx1' : (x : A) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hCW : Subgroup.centralizer (W₀ : Set A) ≤ W := by
    intro g hg
    rcases hdich g (hCN hg) with hgW | hginv
    · exact hgW
    · exfalso
      have hcomm : (x : A) * g = g * x := Subgroup.mem_centralizer_iff.mp hg _ x.property
      have hfix : g * x * g⁻¹ = x := by rw [← hcomm, mul_inv_cancel_right]
      have hinvx := hginv _ (hW₀ x.property)
      exact TwoCoreGrowth.odd_nonidentity_ne_inverse _ hx1' (hWodd_elt _ (hW₀ x.property))
        (hfix.symm.trans hinvx)
  have huN : u ∈ Subgroup.normalizer (W₀ : Set A) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hWinv h (hW₀ hh)]
      exact W₀.inv_mem hh
    · intro hh
      have hz := hWinv _ (hW₀ hh)
      have hh' : u * (u * h * u⁻¹) * u⁻¹ = h := by
        calc u * (u * h * u⁻¹) * u⁻¹ = (u * u) * h * (u * u)⁻¹ := by group
          _ = h := by rw [hu2, one_mul, inv_one, mul_one]
      rw [hh'] at hz
      rw [hz]
      exact W₀.inv_mem hh
  have hNW : Subgroup.normalizer (W₀ : Set A) ≤ W ⊔ Subgroup.zpowers u := by
    intro g hg
    rcases hdich g hg with hgW | hginv
    · exact Subgroup.mem_sup_left hgW
    · have hguW : g * u ∈ W := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hconj : g * u * y * (g * u)⁻¹ = y := by
          calc g * u * y * (g * u)⁻¹ = g * (u * y * u⁻¹) * g⁻¹ := by group
            _ = g * y⁻¹ * g⁻¹ := by rw [huy]
            _ = (g * y * g⁻¹)⁻¹ := by group
            _ = y := by rw [hginv y hyW, inv_inv]
        calc g * u * y = g * u * y * (g * u)⁻¹ * (g * u) := by group
          _ = y * (g * u) := by rw [hconj]
      have hg' : g = (g * u) * u⁻¹ := by group
      rw [hg']
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hguW)
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers u)))
  have hWN : W ⊔ Subgroup.zpowers u ≤ Subgroup.normalizer (W₀ : Set A) :=
    sup_le (hWC.trans hCN) (Subgroup.zpowers_le_of_mem huN)
  exact ⟨le_antisymm hCW hWC, le_antisymm hNW hWN⟩

end CFSG.ShultStronglyClosedTI.LinearModel
