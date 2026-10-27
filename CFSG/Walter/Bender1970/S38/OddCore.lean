module

public import CFSG.Walter.Bender1970.S3.Coprime
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Assembly.Defs
public import CFSG.Walter.Bender1970.S3.Basic

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oddCoreOf_map_conj (H : Subgroup G) (g : G) :
    oddCoreOf (H.map (MulAut.conj g).toMonoidHom) =
      (oddCoreOf H).map (MulAut.conj g).toMonoidHom := by
  set f : G →* G := (MulAut.conj g).toMonoidHom
  set B : Subgroup G := H.map f
  let e : H ≃* B := Subgroup.equivMapOfInjective H f (MulAut.conj g).injective
  have hmap : B.subtype.comp e.toMonoidHom = f.comp H.subtype := by
    ext x
    rfl
  calc oddCoreOf B = (pPrimeCore 2 B).map B.subtype := rfl
    _ = ((pPrimeCore 2 H).map e.toMonoidHom).map B.subtype := by
      rw [CFSG.pPrimeCore_map_iso 2 e]
    _ = (pPrimeCore 2 H).map (B.subtype.comp e.toMonoidHom) := by rw [Subgroup.map_map]
    _ = (pPrimeCore 2 H).map (f.comp H.subtype) := by rw [hmap]
    _ = ((pPrimeCore 2 H).map H.subtype).map f := by rw [Subgroup.map_map]

theorem fittingSubgroupOf_map_conj (X : Subgroup G) (g : G) :
    CFSG.fittingSubgroupOf (X.map (MulAut.conj g).toMonoidHom) =
      (CFSG.fittingSubgroupOf X).map (MulAut.conj g).toMonoidHom := by
  set f : G →* G := (MulAut.conj g).toMonoidHom
  set B : Subgroup G := X.map f
  let e : X ≃* B := Subgroup.equivMapOfInjective X f (MulAut.conj g).injective
  have hmap : B.subtype.comp e.toMonoidHom = f.comp X.subtype := by
    ext x
    rfl
  calc CFSG.fittingSubgroupOf B = (CFSG.fittingSubgroup B).map B.subtype := rfl
    _ = ((CFSG.fittingSubgroup X).map e.toMonoidHom).map B.subtype := by
      rw [map_fittingSubgroup_of_mulEquiv' e]
    _ = (CFSG.fittingSubgroup X).map (B.subtype.comp e.toMonoidHom) := by rw [Subgroup.map_map]
    _ = (CFSG.fittingSubgroup X).map (f.comp X.subtype) := by rw [hmap]
    _ = ((CFSG.fittingSubgroup X).map X.subtype).map f := by rw [Subgroup.map_map]

omit [Finite G] in
theorem oddCoreOf_isNormalIn' (H : Subgroup G) : IsNormalIn (oddCoreOf H) H :=
  map_characteristic_isNormalIn_of_isNormalIn _ inferInstance
    ⟨le_rfl, fun _ hh _ hk => H.mul_mem (H.mul_mem hh hk) (H.inv_mem hh)⟩

omit [Finite G] in
theorem fittingSubgroupOf_isNormalIn_of_isNormalIn {N X : Subgroup G} (hN : IsNormalIn N X) :
    IsNormalIn (CFSG.fittingSubgroupOf N) X :=
  map_characteristic_isNormalIn_of_isNormalIn _ inferInstance hN

omit [Finite G] in
theorem IsNormalIn.of_le {N X Y : Subgroup G} (hN : IsNormalIn N X) (hNY : N ≤ Y) (hYX : Y ≤ X) :
    IsNormalIn N Y :=
  ⟨hNY, fun y hy n hn => hN.2 y (hYX hy) n hn⟩

theorem fittingSubgroupOf_ne_bot_of_solvable {X : Subgroup G} (hX : Group.IsSolvable X)
    (hX1 : X ≠ ⊥) : CFSG.fittingSubgroupOf X ≠ ⊥ := by
  intro h
  have h1 : CFSG.fittingSubgroup X = ⊥ := by
    rw [← Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective]
    exact h
  have h2 := CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hX
  rw [h1] at h2
  have h3 : Subgroup.centralizer ((⊥ : Subgroup X) : Set X) = ⊤ := by
    rw [Subgroup.coe_bot, Subgroup.centralizer_eq_top_iff_subset]
    rintro x rfl
    exact Subgroup.mem_center_iff.mpr fun g => by rw [one_mul, mul_one]
  rw [h3, top_le_iff] at h2
  apply hX1
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hx⟩ : X) ∈ (⊥ : Subgroup X) := h2 ▸ Subgroup.mem_top _
  rw [Subgroup.mem_bot] at this
  exact congrArg Subtype.val this

namespace BenderCounterexample

variable (hG : BenderCounterexample G)
include hG

theorem oddCoreOf_eq_bot
    {H : Subgroup G} (hHco : IsCoatom H) {w : G} (hw2 : orderOf w = 2)
    (hHw : Subgroup.centralizer ({w} : Set G) = H) (T : Sylow 2 G)
    (hwT : w ∈ (T : Subgroup G))
    (hTO : ∀ x ∈ (T : Subgroup G), ∀ o ∈ oddCoreOf H, x * o = o * x)
    (hN : ¬ Subgroup.normalizer ((T : Subgroup G) : Set G) ≤ H) :
    oddCoreOf H = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hG.isSimpleGroup
  by_contra hO
  set O := oddCoreOf H with hOdef
  set F₁ := CFSG.fittingSubgroupOf O with hF₁
  have hOodd : Odd (Nat.card O) := odd_card_oddCoreOf H
  have hOsolv : Group.IsSolvable O := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hOodd
  have hF₁ne : F₁ ≠ ⊥ := fittingSubgroupOf_ne_bot_of_solvable hOsolv hO
  have hF₁O : F₁ ≤ O := Subgroup.map_subtype_le _
  have hOH : O ≤ H := Subgroup.map_subtype_le _
  have hOnH : IsNormalIn O H := oddCoreOf_isNormalIn' H
  have hF₁nH : IsNormalIn F₁ H := fittingSubgroupOf_isNormalIn_of_isNormalIn hOnH
  have hF₁nil : Group.IsNilpotent F₁ := CFSG.fittingSubgroupOf_isNilpotent O
  have hF₁odd : Odd (Nat.card F₁) := Odd.of_dvd_nat hOodd (Subgroup.card_dvd_of_le hF₁O)
  have hHN : H ≤ Subgroup.normalizer (F₁ : Set G) := le_normalizer_of_isNormalIn hF₁nH
  have hNF : Subgroup.normalizer (F₁ : Set G) = H := by
    refine ((hHco.le_iff.mp hHN).resolve_left fun htop => ?_)
    have hn : F₁.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal F₁ with h | h
    · exact hF₁ne h
    · exact hHco.1 (top_le_iff.mp (h ▸ hF₁O.trans hOH))
  apply hN
  intro n hn
  set s := n * w * n⁻¹ with hs
  have hsT : s ∈ (T : Subgroup G) := (Subgroup.mem_normalizer_iff.mp hn w).mp hwT
  set M := H.map (MulAut.conj n).toMonoidHom with hMdef
  have hMs : M = Subgroup.centralizer ({s} : Set G) := by
    rw [hMdef, ← hHw, map_conj_centralizer_singleton]
  have hMco : IsCoatom M := isCoatom_map_conj n hHco
  have hMA : IsAStar M := hG.isAStar_of_isCoatom hMco
  have hOM : oddCoreOf M = O.map (MulAut.conj n).toMonoidHom := oddCoreOf_map_conj H n
  have hTOM : ∀ x ∈ (T : Subgroup G), ∀ o ∈ oddCoreOf M, x * o = o * x := by
    intro x hx o ho
    rw [hOM] at ho
    obtain ⟨o', ho', rfl⟩ := ho
    have hx' : n⁻¹ * x * n ∈ (T : Subgroup G) := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) x).mp hx
      simpa using this
    have h1 := hTO _ hx' o' ho'
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc x * (n * o' * n⁻¹) = n * ((n⁻¹ * x * n) * o') * n⁻¹ := by group
      _ = n * (o' * (n⁻¹ * x * n)) * n⁻¹ := by rw [h1]
      _ = n * o' * n⁻¹ * x := by group
  have hTM : (T : Subgroup G) ≤ M := by
    rw [hMs]
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hG.hasAbelianSylowTwo T
    exact congrArg Subtype.val (this.is_comm.comm ⟨x, hx⟩ ⟨s, hsT⟩)
  have hOM_H : oddCoreOf M ≤ H := by
    intro o ho
    rw [← hHw, Subgroup.mem_centralizer_singleton_iff]
    exact (hTOM w hwT o ho).symm
  have hwM : w ∈ M := hTM hwT
  have hTsub : (⟨w, hwM⟩ : M) ∈ ((T.subtype hTM : Sylow 2 M) : Subgroup M) := by
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf]
    exact hwT
  obtain ⟨-, hCU, -⟩ := bender1970_2_5_subgroup hMA hwM hw2 (T.subtype hTM) hTsub rfl
  have hMC : M ⊓ Subgroup.centralizer ({w} : Set G) = M ⊓ H := by rw [hHw]
  have hF₁U : F₁ ≤ oddCoreOf (CFSG.fittingSubgroupOf (M ⊓ Subgroup.centralizer ({w} : Set G))) := by
    rw [hMC]
    refine le_oddCoreOf_fittingSubgroupOf (IsNormalIn.of_le hF₁nH ?_ inf_le_right) hF₁nil hF₁odd
    intro x hx
    refine ⟨?_, hOH (hF₁O hx)⟩
    show x ∈ M
    rw [hMs, Subgroup.mem_centralizer_singleton_iff]
    exact (hTO s hsT x (hF₁O hx)).symm
  have hF₁C : F₁ ≤ Subgroup.centralizer
      ((((T.subtype hTM : Sylow 2 M) : Subgroup M).map M.subtype : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    have hy' : ((y : M) : G) ∈ (T : Subgroup G) := hy
    exact hTO _ hy' x (hF₁O hx)
  have hF₁OM : F₁ ≤ oddCoreOf M := fun x hx => hCU ⟨hF₁U hx, hF₁C hx⟩
  have hF₁nOM : IsNormalIn F₁ (oddCoreOf M) := IsNormalIn.of_le hF₁nH hF₁OM hOM_H
  have hF₁F₂ : F₁ ≤ CFSG.fittingSubgroupOf (oddCoreOf M) :=
    le_fittingSubgroupOf_of_isNormalIn_nilpotent hF₁OM hF₁nOM hF₁nil
  have hcard : Nat.card (CFSG.fittingSubgroupOf (oddCoreOf M)) = Nat.card F₁ := by
    rw [hOM, fittingSubgroupOf_map_conj, Subgroup.card_map_of_injective (MulAut.conj n).injective]
  have heq : F₁ = CFSG.fittingSubgroupOf (oddCoreOf M) :=
    Subgroup.eq_of_le_of_card_ge hF₁F₂ hcard.le
  have hMN : M ≤ Subgroup.normalizer (F₁ : Set G) := by
    rw [heq]
    exact le_normalizer_of_isNormalIn
      (fittingSubgroupOf_isNormalIn_of_isNormalIn (oddCoreOf_isNormalIn' M))
  rw [hNF] at hMN
  have hMH : M = H := ((hMco.le_iff.mp hMN).resolve_left hHco.1).symm
  exact hG.mem_of_map_conj_eq hHco hMH

end BenderCounterexample

end CFSG.Walter
