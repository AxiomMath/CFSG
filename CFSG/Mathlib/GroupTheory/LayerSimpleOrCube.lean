module

public import CFSG.Foundations.Basic
import CFSG.GroupTheory.LocalCores.Layer
import CFSG.Mathlib.GroupTheory.LayerAbelianSylow
import CFSG.Mathlib.GroupTheory.SimpleProductFixedPoints
import CFSG.GroupTheory.LocalCores.PrimeSetCore

@[expose] public section

namespace CFSG.LayerSimpleOrCube

open CFSG.LocalCores

private lemma exists_noncomm_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : ∃ a b : A, a * b ≠ b * a) : ∃ a b : B, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨e a, e b, fun hh => hab (e.injective (by rw [map_mul, map_mul, hh]))⟩

theorem simple_or_cube_layer {X : Type} [Group X] [Finite X] (hO : pPrimeCore 3 X = ⊥)
    (hab : ∀ P : Sylow 3 X, ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (β : MulAut ↥(layer X))
    (hβ : β ^ 3 = 1) {O J : Subgroup ↥(layer X)}
    (hfix : ∀ x : ↥(layer X), x ∈ O ⊔ J ↔ β x = x) (hOJ : O ⊓ J = ⊥)
    (hcom : ∀ x ∈ O, ∀ y ∈ J, x * y = y * x) (hO3 : Nat.Coprime (Nat.card O) 3)
    (hJ : IsSimpleGroup J) (hJn : ∃ x ∈ J, ∃ y ∈ J, x * y ≠ y * x) :
    IsSimpleGroup ↥(layer X) ∨
      ∃ S₀ S₁ S₂ : Subgroup ↥(layer X), Nonempty (↥S₀ ≃* ↥J) ∧ Nonempty (↥S₁ ≃* ↥J) ∧
        Nonempty (↥S₂ ≃* ↥J) ∧ (∀ x ∈ S₀, ∀ y ∈ S₁, x * y = y * x) ∧
        (∀ x ∈ S₀, ∀ y ∈ S₂, x * y = y * x) ∧ (∀ x ∈ S₁, ∀ y ∈ S₂, x * y = y * x) ∧
        S₀ ⊓ S₁ = ⊥ ∧ (S₀ ⊔ S₁) ⊓ S₂ = ⊥ ∧ S₀ ⊔ S₁ ⊔ S₂ = ⊤ := by
  classical
  let S : ComponentIndex X → Subgroup ↥(layer X) := fun i => i.1.subgroupOf (layer X)
  have hZ : ∀ i : ComponentIndex X, Subgroup.center i.1 = ⊥ := fun i =>
    (CFSG.LayerAbelianSylow.center_eq_bot_and_three_dvd hO hab i.2).1
  have h3dvd : ∀ i : ComponentIndex X, 3 ∣ Nat.card i.1 := fun i =>
    (CFSG.LayerAbelianSylow.center_eq_bot_and_three_dvd hO hab i.2).2
  have hS : ∀ i, IsSimpleGroup (S i) := by
    intro i
    have hQ : IsQuasisimple i.1 := i.2.1
    have hsimpleQ : IsSimpleGroup (i.1 ⧸ (⊥ : Subgroup i.1)) :=
      (MulEquiv.isSimpleGroup_congr (QuotientGroup.quotientMulEquivOfEq (hZ i))).mp hQ.2.1
    have hsimple : IsSimpleGroup i.1 :=
      (MulEquiv.isSimpleGroup_congr (QuotientGroup.quotientBot (G := i.1))).mp hsimpleQ
    exact (MulEquiv.isSimpleGroup_congr
      (Subgroup.subgroupOfEquivOfLe (component_le_layer i.2))).mpr hsimple
  have hnab : ∀ i, ∃ x ∈ S i, ∃ y ∈ S i, x * y ≠ y * x := by
    intro i
    have hQ : IsQuasisimple i.1 := i.2.1
    have hnabQ : ∃ a b : i.1 ⧸ (⊥ : Subgroup i.1), a * b ≠ b * a :=
      exists_noncomm_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq (hZ i)) hQ.2.2
    have hnab1 : ∃ a b : i.1, a * b ≠ b * a :=
      exists_noncomm_of_mulEquiv (QuotientGroup.quotientBot (G := i.1)) hnabQ
    obtain ⟨x, y, hxy⟩ := exists_noncomm_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (component_le_layer i.2)).symm hnab1
    have hxyL : (x : ↥(layer X)) * (y : ↥(layer X)) ≠
        (y : ↥(layer X)) * (x : ↥(layer X)) := by
      intro h
      exact hxy ((S i).subtype_injective (by simpa using h))
    exact ⟨(x : ↥(layer X)), x.2, (y : ↥(layer X)), y.2, hxyL⟩
  have h3 : ∀ i, 3 ∣ Nat.card (S i) := by
    intro i
    have he : Nat.card (S i) = Nat.card i.1 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (component_le_layer i.2)).toEquiv
    rw [he]
    exact h3dvd i
  have hcomm : ∀ i j, i ≠ j → ∀ x ∈ S i, ∀ y ∈ S j, x * y = y * x := by
    intro i j hij x hx y hy
    have hx' : (x : X) ∈ i.1 := Subgroup.mem_subgroupOf.mp hx
    have hy' : (y : X) ∈ j.1 := Subgroup.mem_subgroupOf.mp hy
    rcases distinct_components_commute i.2 j.2 with h | h
    · exact absurd (Subtype.ext h) hij
    · exact Subtype.ext (Subgroup.mem_centralizer_iff.mp
        ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp h) hx') (y : X) hy').symm
  have hmapS : ∀ i, (S i).map (layer X).subtype = i.1 := by
    intro i
    change (i.1.subgroupOf (layer X)).map (layer X).subtype = i.1
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (component_le_layer i.2)]
  have hlayer_iSup : (⨆ i : ComponentIndex X, i.1) = layer X := by
    rw [CFSG.layer.eq_sSup]
    exact le_antisymm (iSup_le fun i => le_sSup i.2)
      (sSup_le fun K hK => le_iSup (fun i : ComponentIndex X => i.1) ⟨K, hK⟩)
  have hsup : (⨆ i : ComponentIndex X, S i) = ⊤ := by
    apply Subgroup.map_injective (f := (layer X).subtype) (layer X).subtype_injective
    rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    simp_rw [hmapS]
    exact hlayer_iSup
  let P := ∀ K : ComponentIndex X, K.1
  let μ : P →* ↥(layer X) := layerMulOnto X
  have hμker : μ.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro u hu
    rw [MonoidHom.mem_ker] at hu
    have hulayer : layerMul X u = 1 := by
      change (μ u : X) = 1
      rw [hu]
      rfl
    have hpi : u ∈ Subgroup.pi Set.univ (fun K : ComponentIndex X => Subgroup.center K.1) :=
      layerMul_ker_le (MonoidHom.mem_ker.mpr hulayer)
    funext K
    have hKc : u K ∈ Subgroup.center K.1 := hpi K (Set.mem_univ K)
    rw [hZ K] at hKc
    exact Subgroup.mem_bot.mp hKc
  have hμinj : Function.Injective μ := (MonoidHom.ker_eq_bot_iff μ).mp hμker
  let Q : ComponentIndex X → Subgroup P := fun i =>
    (MonoidHom.mulSingle (fun K : ComponentIndex X => K.1) i).range
  have hmapQ : ∀ i, (Q i).map μ = S i := by
    intro i
    ext x
    change x ∈ (Q i).map μ ↔ x ∈ i.1.subgroupOf (layer X)
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨k, rfl⟩ := hu
      rw [Subgroup.mem_subgroupOf]
      change (layerMulOnto X (MonoidHom.mulSingle (fun K : ComponentIndex X => K.1) i k) : X)
        ∈ i.1
      rw [MonoidHom.mulSingle_apply, layerMulOnto_coe, layerMul_mulSingle]
      exact k.2
    · intro hx
      refine ⟨MonoidHom.mulSingle (fun K : ComponentIndex X => K.1) i
        ⟨(x : X), Subgroup.mem_subgroupOf.mp hx⟩, ?_, ?_⟩
      · exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
      · exact Subtype.ext (by
          change (layerMulOnto X (MonoidHom.mulSingle (fun K : ComponentIndex X => K.1) i
            ⟨(x : X), Subgroup.mem_subgroupOf.mp hx⟩) : X) = (x : X)
          rw [MonoidHom.mulSingle_apply, layerMulOnto_coe, layerMul_mulSingle])
  have hQdisj : ∀ i, Q i ⊓ ⨆ j : {j // j ≠ i}, Q j = ⊥ := by
    intro i
    have hle : (⨆ j : {j // j ≠ i}, Q j) ≤
        (Pi.evalMonoidHom (fun K : ComponentIndex X => K.1) i).ker := by
      apply iSup_le
      rintro ⟨j, hji⟩ u ⟨k, rfl⟩
      rw [MonoidHom.mem_ker]
      change (Pi.mulSingle (M := fun K : ComponentIndex X => K.1) j k) i = 1
      rw [Pi.mulSingle_eq_of_ne (Ne.symm hji)]
    refine le_antisymm ?_ bot_le
    intro u hu
    rw [Subgroup.mem_inf] at hu
    rw [Subgroup.mem_bot]
    obtain ⟨k, rfl⟩ := hu.1
    have hui : (MonoidHom.mulSingle (fun K : ComponentIndex X => K.1) i k) i = 1 := by
      have hmem : MonoidHom.mulSingle (fun K : ComponentIndex X => K.1) i k ∈
          (Pi.evalMonoidHom (fun K : ComponentIndex X => K.1) i).ker := hle hu.2
      simpa using hmem
    rw [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same] at hui
    rw [hui, map_one]
  have hind : ∀ i, S i ⊓ ⨆ j : {j // j ≠ i}, S j = ⊥ := by
    intro i
    have hSjsup : (⨆ j : {j // j ≠ i}, Q j).map μ = ⨆ j : {j // j ≠ i}, S j := by
      rw [Subgroup.map_iSup]
      exact iSup_congr fun j => hmapQ j
    calc S i ⊓ ⨆ j : {j // j ≠ i}, S j
        = (Q i).map μ ⊓ (⨆ j : {j // j ≠ i}, Q j).map μ := by rw [hmapQ i, hSjsup]
      _ = ((Q i) ⊓ ⨆ j : {j // j ≠ i}, Q j).map μ :=
            (Subgroup.map_inf (Q i) (⨆ j : {j // j ≠ i}, Q j) μ hμinj).symm
      _ = ⊥ := by rw [hQdisj i, Subgroup.map_bot]
  have hcomp_eq : ∀ L : Subgroup ↥(layer X), IsComponent L →
      ∃ j : ComponentIndex X, S j = L := by
    intro L hL
    have hKsub : (layer X).IsSubnormal :=
      (Subgroup.normal_of_characteristic
        (h := CFSG.LocalCores.layer_characteristic)).isSubnormal
    let M : Subgroup X := L.map (layer X).subtype
    have hMcomp : IsComponent M :=
      ⟨isQuasisimple_of_mulEquiv
          (L.equivMapOfInjective (layer X).subtype (layer X).subtype_injective) hL.1,
        hL.2.trans' hKsub⟩
    refine ⟨⟨M, hMcomp⟩, ?_⟩
    show M.subgroupOf (layer X) = L
    change Subgroup.comap (layer X).subtype (Subgroup.map (layer X).subtype L) = L
    rw [Subgroup.comap_map_eq_self_of_injective (layer X).subtype_injective L]
  have hperm : ∀ i : ComponentIndex X, ∃ j : ComponentIndex X,
      (S i).map β.toMonoidHom = S j := by
    intro i
    have hcomp : IsComponent ((S i).map β.toMonoidHom) :=
      isComponent_map_mulEquiv β (component_overgroup i.2 (component_le_layer i.2))
    obtain ⟨j, hj⟩ := hcomp_eq ((S i).map β.toMonoidHom) hcomp
    exact ⟨j, hj.symm⟩
  exact CFSG.SimpleProductFixedPoints.simple_or_cube β hβ (ComponentIndex X) S hS hnab h3
    hcomm hind hsup hperm hfix hOJ hcom hO3 hJ hJn

end CFSG.LayerSimpleOrCube

end
