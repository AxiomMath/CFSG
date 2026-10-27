module

public import CFSG.Quasithin.EmptyFaithful.SmithL3ResFin
public import CFSG.Quasithin.H13.GoldschmidtC137L32ZKey

public section

namespace CFSG.Quasithin.SmithL3Res

open Subgroup CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.L3
  CFSG.Quasithin.H13.U3.GC137 CFSG.Assembly.LowTwoRank
open CFSG.Open hiding StatedSL

variable {G : Type} [Group G]

theorem isSylowTwoOf_of_le_of_le' {P C A : Subgroup G} (hP : IsSylowTwoOf P A) (hPC : P ≤ C)
    (hCA : C ≤ A) : IsSylowTwoOf P C := by
  refine ⟨hPC, hP.2.1, fun hdvd => hP.2.2 ?_⟩
  have h1 := Subgroup.relIndex_mul_relIndex P C A hPC hCA
  have h2 : 2 ∣ P.relIndex A := by
    rw [← h1]
    exact Dvd.dvd.mul_right hdvd _
  exact h2

variable [Finite G]

theorem exists_pointStab {L M SL : Subgroup G} {F : Type} [Field F] [Fintype F]
    (hcard : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168) {α : ↥L →* ↥(StatedSL 3 F)}
    (hα : IsModO2Surj L α) {j : ℕ} (hj : j = 1 ∨ j = 2)
    (hM : IsSumOfNaturalModulesVia L M ⊥ α false j) (hSL : IsSylowTwoOf SL L) :
    ∃ K : Subgroup G, SL ≤ K ∧ K ≤ L ∧
      (∀ H : Subgroup G, K ≤ H → H ≤ L → H ≠ L → H ≤ K) ∧
      ∀ z : G, (∀ p ∈ SL, p * z = z * p) → (∀ k ∈ L, k * z * k⁻¹ * z⁻¹ ∈ M) →
        ∀ k ∈ K, k * z = z * k := by
  obtain ⟨α'', β', hsurj, -, hLM, hβ⟩ := exists_coords hcard hα hM
  have hSL2 : IsPGroup 2 ↥(SL.subgroupOf L) :=
    hSL.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSL.1).symm
  obtain ⟨e₀, he₀, hfix⟩ := exists_fixed_vec (hSL2.map α'')
  set x : Multiplicative (Fin j → Vec) := Multiplicative.ofAdd (fun _ => e₀) with hx
  set u : G := ((β'.symm x : ↥M) : G) with hu
  have huM : u ∈ M := (β'.symm x).2
  have hβu : β' ⟨u, huM⟩ = x := β'.apply_symm_apply x
  have i₀ : Fin j := ⟨0, by omega⟩
  have hu1 : u ≠ 1 := by
    intro h1
    have h2 : β' ⟨u, huM⟩ = 1 := by
      have : (⟨u, huM⟩ : ↥M) = 1 := Subtype.ext h1
      rw [this, map_one]
    rw [hβu] at h2
    exact he₀ (congrFun (congrArg Multiplicative.toAdd h2) i₀)
  have hLfix : ∀ l : ↥L, (l : G) * u = u * l ↔ act (α'' l) e₀ = e₀ := by
    intro l
    constructor
    · intro hl
      have hv : ((⟨u, huM⟩ : ↥M) : G) = (l : G) * ((⟨u, huM⟩ : ↥M) : G) * (l : G)⁻¹ := by
        show u = (l : G) * u * (l : G)⁻¹
        rw [hl]
        group
      have h1 := hβ l ⟨u, huM⟩ ⟨u, huM⟩ hv i₀
      rw [hβu] at h1
      exact h1.symm
    · intro hl
      have hmem : (l : G) * u * (l : G)⁻¹ ∈ M :=
        (Subgroup.mem_normalizer_iff.1 (hLM l.2) u).1 huM
      have h1 : β' ⟨(l : G) * u * (l : G)⁻¹, hmem⟩ = β' ⟨u, huM⟩ := by
        apply Multiplicative.toAdd.injective
        funext i
        rw [hβ l ⟨u, huM⟩ _ rfl i, hβu]
        exact hl
      have h3 : (l : G) * u * (l : G)⁻¹ = u := congrArg Subtype.val (β'.injective h1)
      calc (l : G) * u = ((l : G) * u * (l : G)⁻¹) * l := by group
        _ = u * l := by rw [h3]
  set K : Subgroup G := L ⊓ Subgroup.centralizer ({u} : Set G) with hK
  have hKu : ∀ l ∈ L, l * u = u * l → l ∈ K := fun l hl hlu =>
    ⟨hl, Subgroup.mem_centralizer_iff.2 fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hlu.symm⟩
  have hKu' : ∀ k ∈ K, k * u = u * k := fun k hk =>
    (Subgroup.mem_centralizer_iff.1 hk.2 u (Set.mem_singleton u)).symm
  have hKchar : ∀ l : ↥L, (l : G) ∈ K ↔ act (α'' l) e₀ = e₀ := fun l =>
    ⟨fun h => (hLfix l).1 (hKu' _ h), fun h => hKu _ l.2 ((hLfix l).2 h)⟩
  have hSLK : SL ≤ K := fun s hs =>
    (hKchar ⟨s, hSL.1 hs⟩).2 (hfix _ (Subgroup.mem_map_of_mem α''
      (show (⟨s, hSL.1 hs⟩ : ↥L) ∈ SL.subgroupOf L from hs)))
  refine ⟨K, hSLK, inf_le_left, fun H hKH hHL hH => le_of_stabChar hsurj he₀ hKchar hKH hHL hH,
    ?_⟩
  intro z hzSL hc k hk
  exact zcentral_of_sum hcard hα hj hM huM hu1 inf_le_left hKu hKu'
    (isSylowTwoOf_of_le_of_le' hSL hSLK inf_le_left) hzSL (fun k hk => hc k hk.1) k hk

end CFSG.Quasithin.SmithL3Res
