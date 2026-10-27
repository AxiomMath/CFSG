module

public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalLeviA
public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalDefs
public import CFSG.Quasithin.Recognition.St84.Gen.L2SectionBorel
import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalBorel
import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalGlue
import CFSG.Quasithin.Recognition.St84.Gen.VertexIsoSylow
import CFSG.Quasithin.Recognition.St84.SemidirectRec
import CFSG.Quasithin.H13.J4Order

public noncomputable section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.Quasithin
open CFSG.ComponentClassification.UnbalancedCatalog
open scoped Pointwise commutatorElement


variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

private theorem mem_of_map_mem_of_card_eq {G' : Type} [Group G'] [Finite G']
    {P : Subgroup G} {M : Subgroup G'} (ψ : ↥P ≃* ↥M) {X : Subgroup G} {Y : Subgroup G'}
    (hX : X ≤ P) (hY : Y ≤ M)
    (hle : ∀ x : ↥P, (x : G) ∈ X → ((ψ x : ↥M) : G') ∈ Y)
    (hcard : Nat.card X = Nat.card Y) :
    ∀ x : ↥P, ((ψ x : ↥M) : G') ∈ Y → (x : G) ∈ X := by
  classical
  have hmap_le : (X.subgroupOf P).map ψ.toMonoidHom ≤ Y.subgroupOf M := by
    rintro _ ⟨x, hx, rfl⟩
    exact hle x hx
  have hcardX : Nat.card ↥((X.subgroupOf P).map ψ.toMonoidHom) = Nat.card X := by
    rw [Subgroup.card_map_of_injective ψ.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have hcardY : Nat.card ↥(Y.subgroupOf M) = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv
  have heq : (X.subgroupOf P).map ψ.toMonoidHom = Y.subgroupOf M :=
    Subgroup.eq_of_le_of_card_ge hmap_le (by rw [hcardX, hcardY, hcard])
  intro x hx
  have hxmap : ψ x ∈ (X.subgroupOf P).map ψ.toMonoidHom := by
    rw [heq]
    exact hx
  change ψ.toMonoidHom x ∈ (X.subgroupOf P).map ψ.toMonoidHom at hxmap
  rw [Subgroup.mem_map_iff_mem ψ.injective] at hxmap
  exact Subgroup.mem_subgroupOf.mp hxmap

theorem G2qLocalData.mem_bigB_iff_of_vertexTwo
    (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2))
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K))
    (hψ₂S : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ posUnipotentSub Tag.G2 K) :
    ∀ x : ↥(L2 ⊔ bigB L1 L2 S),
      (x : G) ∈ bigB L1 L2 S ↔
        ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ borelSub Tag.G2 K := by
  classical
  have hSP : S ≤ L2 ⊔ bigB L1 L2 S :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right
  have hle : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ bigB L1 L2 S →
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ borelSub Tag.G2 K := by
    intro x hxB
    have hxN : (x : G) ∈ Subgroup.normalizer (S : Set G) :=
      (hD.bigB_le_normalizer hH h1 h2 hxB).2
    have hxNU : ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈
        Subgroup.normalizer (posUnipotentSub Tag.G2 K :
          Set ↥(adjointGroup Tag.G2 K)) :=
      (mem_normalizer_iff_of_mulEquiv ψ₂ hSP G2q.posUnipotentSub_le_g2ParB hψ₂S x).mp hxN
    have hxAB : ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈
        g2ParA K ⊓ g2ParB K := by
      rwa [← G2q.normalizer_posUnipotentSub]
    simpa [G2q.g2ParA_inf_g2ParB] using hxAB
  have hUcard : Nat.card (posUnipotentSub Tag.G2 K) = 2 ^ (6 * f) := by
    let e : ↥S ≃* ↥(posUnipotentSub Tag.G2 K) :=
      restrictEquiv ψ₂ hSP hψ₂S G2q.posUnipotentSub_le_g2ParB
    rw [← Nat.card_congr e.toEquiv, hD.card_S]
  have hUpos : Nat.card (posUnipotent Tag.G2 K) = 2 ^ (6 * f) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (posUnipotent_le_adjointGroup (τ := Tag.G2) (K := K))).toEquiv]
    exact hUcard
  have hcardBorel : Nat.card (borelSub Tag.G2 K) =
      2 ^ (6 * f) * ((2 ^ f - 1) * (2 ^ f - 1)) := by
    calc
      Nat.card (borelSub Tag.G2 K) = Nat.card (borelGroup Tag.G2 K) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (borelGroup_le_adjointGroup' (τ := Tag.G2) (K := K))).toEquiv
      _ = Nat.card (torusGroup Tag.G2 K) * Nat.card (posUnipotent Tag.G2 K) :=
        card_borelGroup
      _ = (Nat.card K - 1) ^ 2 * Nat.card (posUnipotent Tag.G2 K) := by
        rw [G2q.card_torusGroup]
      _ = (2 ^ f - 1) ^ 2 * 2 ^ (6 * f) := by rw [hK, hUpos]
      _ = 2 ^ (6 * f) * ((2 ^ f - 1) * (2 ^ f - 1)) := by ring
  have hcardB : Nat.card (bigB L1 L2 S) = Nat.card (borelSub Tag.G2 K) := by
    rw [hD.card_bigB hH h1 h2, hcardBorel]
  intro x
  exact ⟨hle x, mem_of_map_mem_of_card_eq ψ₂
    (le_sup_right : bigB L1 L2 S ≤ L2 ⊔ bigB L1 L2 S)
    G2q.borelSub_le_g2ParB hle hcardB x⟩

theorem G2qLocalData.mem_trivOTwoQuot_iff_of_vertexTwo
    (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2)) {H : Subgroup G}
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S) (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ f - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K))
    (hψ₂S : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ posUnipotentSub Tag.G2 K)
    (hψ₂Q : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ pCoreOf 2 L1 ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ pCoreOf 2 (g2ParA K))
    (hψ₂H : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔
      (((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) ∈
        torusGroup Tag.G2 K) :
    ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ H ⊓ trivOTwoQuot L1 ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ G2q.torusASub K := by
  classical
  have hf1 : 1 ≤ f := by omega
  have hSL1 : S ≤ L1 := hD.le_left hH hf1 h1
  have hH0P : H ⊓ trivOTwoQuot L1 ≤ L2 ⊔ bigB L1 L2 S :=
    (inf_le_left.trans hHB).trans le_sup_right
  have hcardH0 : Nat.card ↥(H ⊓ trivOTwoQuot L1) = 2 ^ f - 1 :=
    (hD.torus_left_of_hall hf hH h1 h2 hHB hSH hSinfH hHcard hHcomm).2.1
  have hcardA : Nat.card (G2q.torusASub K) = 2 ^ f - 1 := G2q.card_torusASub hK
  have hle : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ H ⊓ trivOTwoQuot L1 →
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ G2q.torusASub K := by
    intro x hx
    obtain ⟨hxH, hxT⟩ := Subgroup.mem_inf.mp hx
    have hxT' := mem_trivOTwoQuot.mp hxT
    have hT : ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈
        torusSub Tag.G2 K :=
      Subgroup.mem_subgroupOf.mpr ((hψ₂H x).mp hxH)
    refine (G2q.mem_torusASub_iff_of_mem_torusSub hT).2 ?_
    intro u hu
    have huB : u ∈ g2ParB K := G2q.posUnipotentSub_le_g2ParB hu
    let uP : ↥(g2ParB K) := ⟨u, huB⟩
    let s : ↥(L2 ⊔ bigB L1 L2 S) := ψ₂.symm uP
    have hψs : ψ₂ s = uP := ψ₂.apply_symm_apply uP
    have hsS : (s : G) ∈ S := by
      refine (hψ₂S s).2 ?_
      rw [hψs]
      exact hu
    have hsL1 : (s : G) ∈ L1 := hSL1 hsS
    have hcommG : (x : G) * (s : G) * (x : G)⁻¹ * (s : G)⁻¹ ∈ pCoreOf 2 L1 :=
      hxT'.2 (s : G) hsL1
    have hcommP : ((x * s * x⁻¹ * s⁻¹ : ↥(L2 ⊔ bigB L1 L2 S)) : G) ∈
        pCoreOf 2 L1 := by
      simpa using hcommG
    have hψcomm : ((ψ₂ (x * s * x⁻¹ * s⁻¹) : ↥(g2ParB K)) :
        ↥(adjointGroup Tag.G2 K)) ∈ pCoreOf 2 (g2ParA K) :=
      (hψ₂Q (x * s * x⁻¹ * s⁻¹)).1 hcommP
    have hmap : ψ₂ (x * s * x⁻¹ * s⁻¹) = ψ₂ x * uP * (ψ₂ x)⁻¹ * uP⁻¹ := by
      simp only [map_mul, map_inv, hψs]
    rw [hmap] at hψcomm
    simpa [uP] using hψcomm
  intro x
  exact ⟨hle x, mem_of_map_mem_of_card_eq ψ₂ hH0P G2q.torusASub_le_g2ParB hle
    (by rw [hcardH0, hcardA]) x⟩

theorem G2qLocalData.mem_centerOf_left_iff_of_vertexTwo
    (hH : Hyp111 L1 L2 S)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K))
    (hψ₂Q : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ pCoreOf 2 L1 ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ pCoreOf 2 (g2ParA K)) :
    ∀ x : ↥(L2 ⊔ bigB L1 L2 S),
      (x : G) ∈ centerOf (pCoreOf 2 L1) ↔
        ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈
          centerOf (pCoreOf 2 (g2ParA K)) := by
  classical
  have hQ1P : pCoreOf 2 L1 ≤ L2 ⊔ bigB L1 L2 S :=
    (hH.pCoreOf_le_left.trans (le_sup_right : S ≤ bigB L1 L2 S)).trans le_sup_right
  have hQAP : pCoreOf 2 (g2ParA K) ≤ g2ParB K := G2q.pCoreOf_g2ParA_le_g2ParB
  intro x
  constructor
  · intro hx
    obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.mp hx
    have hψxQ : ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈
        pCoreOf 2 (g2ParA K) := (hψ₂Q x).1 hxQ
    refine Subgroup.mem_inf.mpr ⟨hψxQ, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzP : z ∈ g2ParB K := hQAP hz
    let zP : ↥(g2ParB K) := ⟨z, hzP⟩
    let y : ↥(L2 ⊔ bigB L1 L2 S) := ψ₂.symm zP
    have hψy : ψ₂ y = zP := ψ₂.apply_symm_apply zP
    have hyQ : (y : G) ∈ pCoreOf 2 L1 := by
      refine (hψ₂Q y).2 ?_
      rw [hψy]
      exact hz
    have hxy : (y : G) * (x : G) = (x : G) * (y : G) :=
      Subgroup.mem_centralizer_iff.mp hxC (y : G) hyQ
    have hxyP : y * x = x * y := Subtype.ext hxy
    have hψxy : ψ₂ y * ψ₂ x = ψ₂ x * ψ₂ y := by
      rw [← map_mul, ← map_mul, hxyP]
    change ((zP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) *
        ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) =
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) *
        ((zP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K))
    rw [← hψy]
    exact congrArg (fun w : ↥(g2ParB K) => ((w : ↥(adjointGroup Tag.G2 K)))) hψxy
  · intro hx
    obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxQ1 : (x : G) ∈ pCoreOf 2 L1 := (hψ₂Q x).2 hxQ
    refine Subgroup.mem_inf.mpr ⟨hxQ1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    let yP : ↥(L2 ⊔ bigB L1 L2 S) := ⟨y, hQ1P hy⟩
    have hψyQ : ((ψ₂ yP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈
        pCoreOf 2 (g2ParA K) := (hψ₂Q yP).1 hy
    have hcommA : ((ψ₂ yP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) *
        ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) =
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) *
        ((ψ₂ yP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) :=
      Subgroup.mem_centralizer_iff.mp hxC _ hψyQ
    have hcommP : ψ₂ yP * ψ₂ x = ψ₂ x * ψ₂ yP := by
      apply Subtype.ext
      simpa using hcommA
    have hxyP : yP * x = x * yP :=
      ψ₂.injective (by rw [map_mul, map_mul]; exact hcommP)
    exact congrArg Subtype.val hxyP

theorem G2qLocalData.eq_one_of_mem_pCoreOf_left_of_commute
    (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2)) {H : Subgroup G}
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S) (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ f - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K))
    (hψ₂S : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ posUnipotentSub Tag.G2 K)
    (hψ₂Q : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ pCoreOf 2 L1 ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ pCoreOf 2 (g2ParA K))
    (hψ₂H : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔
      (((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) ∈
        torusGroup Tag.G2 K) :
    ∀ x ∈ pCoreOf 2 L1, (∀ h ∈ H ⊓ trivOTwoQuot L1, h * x * h⁻¹ = x) → x = 1 := by
  classical
  have hf1 : 1 ≤ f := by omega
  have hQ1P : pCoreOf 2 L1 ≤ L2 ⊔ bigB L1 L2 S := by
    have hSB : S ≤ bigB L1 L2 S := by
      rw [← hSH]
      exact le_sup_left
    exact (hH.pCoreOf_le_left.trans hSB).trans le_sup_right
  have hT1 := hD.mem_trivOTwoQuot_iff_of_vertexTwo hf hH h1 h2 hHB hSH hSinfH hHcard
    hHcomm hK ψ₂ hψ₂S hψ₂Q hψ₂H
  intro x hx hfix
  let xP : ↥(L2 ⊔ bigB L1 L2 S) := ⟨x, hQ1P hx⟩
  have hxQA : ((ψ₂ xP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈
      pCoreOf 2 (g2ParA K) := (hψ₂Q xP).1 (by simpa [xP] using hx)
  have hcomm : ∀ a ∈ G2q.torusASub K,
      a * ((ψ₂ xP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) =
        ((ψ₂ xP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) * a := by
    intro a ha
    have haP : a ∈ g2ParB K := G2q.torusASub_le_g2ParB ha
    let aP : ↥(g2ParB K) := ⟨a, haP⟩
    let hP : ↥(L2 ⊔ bigB L1 L2 S) := ψ₂.symm aP
    have hψh : ψ₂ hP = aP := ψ₂.apply_symm_apply aP
    have hh0 : (hP : G) ∈ H ⊓ trivOTwoQuot L1 :=
      (hT1 hP).2 (by rw [hψh]; exact ha)
    have hconj : (hP : G) * x * (hP : G)⁻¹ = x := hfix hP hh0
    have hconjP : hP * xP * hP⁻¹ = xP := Subtype.ext hconj
    have hmul : hP * xP = xP * hP := by
      calc hP * xP = (hP * xP * hP⁻¹) * hP := by group
        _ = xP * hP := by rw [hconjP]
    have hcommP : ψ₂ hP * ψ₂ xP = ψ₂ xP * ψ₂ hP := by
      simpa [map_mul] using congrArg (fun z : ↥(L2 ⊔ bigB L1 L2 S) => ψ₂ z) hmul
    calc a * ((ψ₂ xP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K))
        = ((ψ₂ hP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) *
            ((ψ₂ xP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) := by
          rw [hψh]
      _ = ((ψ₂ xP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) *
            ((ψ₂ hP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) :=
          congrArg (fun w : ↥(g2ParB K) => ((w : ↥(adjointGroup Tag.G2 K)))) hcommP
      _ = ((ψ₂ xP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) * a := by
          rw [hψh]
  have hx1 : ((ψ₂ xP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) = 1 :=
    G2q.eq_one_of_mem_pCoreOf_of_commute_torusASub hK hf hxQA hcomm
  have hψxP1 : ψ₂ xP = 1 := by
    apply Subtype.ext
    simpa using hx1
  have hxP1 : xP = 1 := ψ₂.injective (by simpa using hψxP1)
  have hx1G : (xP : G) = 1 := congrArg Subtype.val hxP1
  simpa [xP] using hx1G

theorem G2qLocalData.mem_inf_left_iff_of_vertexTwo
    (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2)) {H : Subgroup G}
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S) (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ f - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K))
    (hψ₂Q : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ pCoreOf 2 L1 ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ pCoreOf 2 (g2ParA K))
    (hψ₂H : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔
      (((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) ∈
        torusGroup Tag.G2 K) :
    ∀ x : ↥(L2 ⊔ bigB L1 L2 S),
      (x : G) ∈ H ⊓ L1 ↔
        ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈
          torusSub Tag.G2 K ⊓ G2q.leviASub K := by
  classical
  have hT3 := G2qLocalData.mem_centerOf_left_iff_of_vertexTwo hH ψ₂ hψ₂Q
  have hHLP : H ⊓ L1 ≤ L2 ⊔ bigB L1 L2 S :=
    (inf_le_left.trans hHB).trans le_sup_right
  have hle : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ H ⊓ L1 →
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈
        torusSub Tag.G2 K ⊓ G2q.leviASub K := by
    intro x hx
    obtain ⟨hxH, hxL1⟩ := Subgroup.mem_inf.mp hx
    have hT : ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈
        torusSub Tag.G2 K :=
      Subgroup.mem_subgroupOf.mpr ((hψ₂H x).mp hxH)
    refine Subgroup.mem_inf.mpr ⟨hT, ?_⟩
    refine (G2q.mem_leviASub_iff_commute_centerOf hT).2 ?_
    intro z hz
    have hzP : z ∈ g2ParB K := G2q.pCoreOf_g2ParA_le_g2ParB (Subgroup.mem_inf.mp hz).1
    let zP : ↥(g2ParB K) := ⟨z, hzP⟩
    let y : ↥(L2 ⊔ bigB L1 L2 S) := ψ₂.symm zP
    have hψy : ψ₂ y = zP := ψ₂.apply_symm_apply zP
    have hyZ : (y : G) ∈ centerOf (pCoreOf 2 L1) := by
      refine (hT3 y).2 ?_
      rw [hψy]
      exact hz
    rw [hD.center_left] at hyZ
    have hxy : (x : G) * (y : G) = (y : G) * (x : G) :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hyZ).2 (x : G) hxL1
    have hxyP : x * y = y * x := Subtype.ext hxy
    have hψxy : ψ₂ x * ψ₂ y = ψ₂ y * ψ₂ x := by
      rw [← map_mul, ← map_mul, hxyP]
    change ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) *
        ((zP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) =
      ((zP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) *
        ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K))
    rw [← hψy]
    exact congrArg (fun w : ↥(g2ParB K) => ((w : ↥(adjointGroup Tag.G2 K)))) hψxy
  have hcardHL : Nat.card ↥(H ⊓ L1) = 2 ^ f - 1 :=
    (hD.torus_left_of_hall hf hH h1 h2 hHB hSH hSinfH hHcard hHcomm).1
  have hcardT : Nat.card ↥(torusSub Tag.G2 K ⊓ G2q.leviASub K) = 2 ^ f - 1 :=
    G2q.card_torusSub_inf_leviASub hK
  intro x
  exact ⟨hle x, mem_of_map_mem_of_card_eq ψ₂ hHLP G2q.torusSub_inf_leviASub_le_g2ParB hle
    (by rw [hcardHL, hcardT]) x⟩

theorem G2qLocalData.exists_mem_left_of_vertexTwo
    (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2)) {H : Subgroup G}
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S) (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ f - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K))
    (hψ₂S : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ posUnipotentSub Tag.G2 K)
    (hψ₂Q : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ pCoreOf 2 L1 ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ pCoreOf 2 (g2ParA K))
    (hψ₂H : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔
      (((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) ∈
        torusGroup Tag.G2 K) :
    ∃ x₁ ∈ L1 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G),
      x₁ ∈ S ∧ x₁ ∉ pCoreOf 2 L1 ∧
        ∀ y : ↥(L2 ⊔ bigB L1 L2 S), (y : G) = x₁ →
          (((ψ₂ y : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) =
            pinnedX Tag.G2 K g2r 1 := by
  classical
  have hf1 : 1 ≤ f := by omega
  have hSL1 : S ≤ L1 := hD.le_left hH hf1 h1
  have hH0P : H ⊓ trivOTwoQuot L1 ≤ L2 ⊔ bigB L1 L2 S :=
    (inf_le_left.trans hHB).trans le_sup_right
  have hT1 := hD.mem_trivOTwoQuot_iff_of_vertexTwo hf hH h1 h2 hHB hSH hSinfH hHcard
    hHcomm hK ψ₂ hψ₂S hψ₂Q hψ₂H
  let p : ↥(adjointGroup Tag.G2 K) :=
    ⟨pinnedX Tag.G2 K g2r 1, pinnedX_mem_adjointGroup g2r 1⟩
  have hpU : p ∈ posUnipotentSub Tag.G2 K := by
    rw [posUnipotentSub, Subgroup.mem_subgroupOf]
    rw [posUnipotent, rootSpan]
    refine Subgroup.mem_iSup_of_mem g2r ?_
    refine Subgroup.mem_iSup_of_mem ⟨isRoot_g2r, by decide⟩ ?_
    exact (mem_rootSubgroup (τ := Tag.G2) (R := K)).2 ⟨1, rfl⟩
  have hpB : p ∈ g2ParB K := G2q.posUnipotentSub_le_g2ParB hpU
  let m : ↥(g2ParB K) := ⟨p, hpB⟩
  let xP : ↥(L2 ⊔ bigB L1 L2 S) := ψ₂.symm m
  have hxPψ : ψ₂ xP = m := ψ₂.apply_symm_apply m
  have hxPS : (xP : G) ∈ S := by
    refine (hψ₂S xP).2 ?_
    rw [hxPψ]
    simpa [m, p] using hpU
  have hxPL1 : (xP : G) ∈ L1 := hSL1 hxPS
  have hxPQ : (xP : G) ∉ pCoreOf 2 L1 := by
    intro hQ
    have hQA : ((ψ₂ xP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈
        pCoreOf 2 (g2ParA K) := (hψ₂Q xP).1 hQ
    rw [hxPψ] at hQA
    exact G2q.X_r_one_not_mem_pCoreOf (h := p) rfl (by simpa [m, p] using hQA)
  have hfix : (xP : G) ∈
      Subgroup.centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    let hP : ↥(L2 ⊔ bigB L1 L2 S) := ⟨h, hH0P hh⟩
    have hHAL : ((ψ₂ hP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈
        G2q.torusASub K := (hT1 hP).1 hh
    have hpComm : ∀ a ∈ G2q.torusASub K, a * p = p * a :=
      (G2q.commute_torusASub_iff hK hf hpU).2 ⟨1, rfl⟩
    have hcommA : ((ψ₂ hP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) * p =
        p * ((ψ₂ hP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) :=
      hpComm _ hHAL
    have hcommP : ψ₂ hP * ψ₂ xP = ψ₂ xP * ψ₂ hP := by
      rw [hxPψ]
      apply Subtype.ext
      simpa [m, p] using hcommA
    have hxh : hP * xP = xP * hP :=
      ψ₂.injective (by rw [map_mul, map_mul]; exact hcommP)
    exact congrArg Subtype.val hxh
  refine ⟨(xP : G), Subgroup.mem_inf.mpr ⟨hxPL1, hfix⟩, hxPS, hxPQ, ?_⟩
  intro y hy
  have hyx : y = xP := Subtype.ext hy
  rw [hyx, hxPψ]

theorem G2qLocalData.mem_complA_of_vertexTwo
    (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2)) {H : Subgroup G}
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S) (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ f - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K))
    (hψ₂S : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ posUnipotentSub Tag.G2 K)
    (hψ₂Q : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ pCoreOf 2 L1 ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ pCoreOf 2 (g2ParA K))
    (hψ₂H : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔
      (((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) ∈
        torusGroup Tag.G2 K) :
    ∀ y : ↥(L2 ⊔ bigB L1 L2 S), (y : G) ∈ bigB L1 L2 S →
      (∀ h ∈ H ⊓ trivOTwoQuot L1, h * (y : G) = (y : G) * h) →
        ((ψ₂ y : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ G2q.complA K := by
  classical
  have hf1 : 1 ≤ f := by omega
  have hSP : S ≤ L2 ⊔ bigB L1 L2 S := (hD.le_right hH hf1 h2).trans le_sup_left
  have hT1 := hD.mem_trivOTwoQuot_iff_of_vertexTwo hf hH h1 h2 hHB hSH hSinfH hHcard
    hHcomm hK ψ₂ hψ₂S hψ₂Q hψ₂H
  intro y hyB hyC
  have hyNS : (y : G) ∈ Subgroup.normalizer (S : Set G) :=
    (hD.bigB_le_normalizer hH h1 h2 hyB).2
  have hN := mem_normalizer_iff_of_mulEquiv ψ₂ hSP G2q.posUnipotentSub_le_g2ParB hψ₂S y
  have hyNU : ((ψ₂ y : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈
      Subgroup.normalizer (posUnipotentSub Tag.G2 K :
        Set ↥(adjointGroup Tag.G2 K)) := hN.mp hyNS
  have hyAB : ((ψ₂ y : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈
      g2ParA K ⊓ g2ParB K := by
    rwa [← G2q.normalizer_posUnipotentSub]
  have hyBorel : ((ψ₂ y : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈
      borelSub Tag.G2 K := by
    simpa [G2q.g2ParA_inf_g2ParB] using hyAB
  refine G2q.mem_complA_of_mem_borelSub_of_commute hK hf hyBorel ?_
  intro a ha
  have haP : a ∈ g2ParB K := G2q.torusASub_le_g2ParB ha
  let aP : ↥(g2ParB K) := ⟨a, haP⟩
  let hP : ↥(L2 ⊔ bigB L1 L2 S) := ψ₂.symm aP
  have hψh : ψ₂ hP = aP := ψ₂.apply_symm_apply aP
  have hh0 : (hP : G) ∈ H ⊓ trivOTwoQuot L1 :=
    (hT1 hP).2 (by rw [hψh]; exact ha)
  have hcommG : (hP : G) * (y : G) = (y : G) * (hP : G) := hyC hP hh0
  have hcommP : hP * y = y * hP := Subtype.ext hcommG
  have hcommψ : ψ₂ hP * ψ₂ y = ψ₂ y * ψ₂ hP := by
    rw [← map_mul, ← map_mul, hcommP]
  calc a * ((ψ₂ y : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K))
      = ((ψ₂ hP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) *
          ((ψ₂ y : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) := by
        rw [hψh]
    _ = ((ψ₂ y : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) *
          ((ψ₂ hP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) :=
        congrArg (fun w : ↥(g2ParB K) => ((w : ↥(adjointGroup Tag.G2 K)))) hcommψ
    _ = ((ψ₂ y : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) * a := by
        rw [hψh]

private def hallPreimage {K : Type} [Field K]
    (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K)) : Subgroup G :=
  ((Subgroup.comap (g2ParB K).subtype (torusSub Tag.G2 K)).map ψ₂.symm.toMonoidHom).map
    (L2 ⊔ bigB L1 L2 S).subtype

private theorem mem_hallPreimage {K : Type} [Field K]
    (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K))
    (x : ↥(L2 ⊔ bigB L1 L2 S)) :
    (x : G) ∈ hallPreimage ψ₂ ↔
      (((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) ∈
        torusGroup Tag.G2 K := by
  classical
  let Tmodel : Subgroup ↥(g2ParB K) :=
    Subgroup.comap (g2ParB K).subtype (torusSub Tag.G2 K)
  have hTmodel : ∀ y : ↥(g2ParB K), y ∈ Tmodel ↔
      (((y : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) ∈
        torusGroup Tag.G2 K := by
    intro y
    change y ∈ Subgroup.comap (g2ParB K).subtype (torusSub Tag.G2 K) ↔ _
    rw [Subgroup.mem_comap, torusSub, Subgroup.mem_subgroupOf]
    rfl
  have h1 : (x : G) ∈ hallPreimage ψ₂ ↔ x ∈ Tmodel.map ψ₂.symm.toMonoidHom := by
    rw [show hallPreimage ψ₂ =
      (Tmodel.map ψ₂.symm.toMonoidHom).map (L2 ⊔ bigB L1 L2 S).subtype from rfl]
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      have hyx' : y = x := Subtype.ext hyx
      simpa [hyx'] using hy
    · intro hx
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have h2 : x ∈ Tmodel.map ψ₂.symm.toMonoidHom ↔ ψ₂ x ∈ Tmodel := by
    constructor
    · rintro ⟨t, ht, ht_eq⟩
      have ht' : ψ₂ (ψ₂.symm t) ∈ Tmodel := by simpa using ht
      rw [← ht_eq]
      exact ht'
    · intro hx
      exact ⟨ψ₂ x, hx, by simp⟩
  exact h1.trans (h2.trans (hTmodel (ψ₂ x)))

private theorem card_hallPreimage {K : Type} [Field K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f)
    (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K)) :
    Nat.card (hallPreimage ψ₂) = (2 ^ f - 1) * (2 ^ f - 1) := by
  classical
  let Tmodel : Subgroup ↥(g2ParB K) :=
    Subgroup.comap (g2ParB K).subtype (torusSub Tag.G2 K)
  have hTmodelEq : Tmodel = (torusSub Tag.G2 K).subgroupOf (g2ParB K) := rfl
  have hcardTmodel : Nat.card Tmodel = (2 ^ f - 1) * (2 ^ f - 1) := by
    have hle : torusSub Tag.G2 K ≤ g2ParB K :=
      G2q.torusSub_le_borelSub.trans G2q.borelSub_le_g2ParB
    rw [hTmodelEq]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show torusGroup Tag.G2 K ≤ adjointGroup Tag.G2 K from
        torusGroup_le_borelGroup.trans borelGroup_le_adjointGroup')).toEquiv]
    rw [G2q.card_torusGroup, hK]
    ring
  change Nat.card ((Tmodel.map ψ₂.symm.toMonoidHom).map
    (L2 ⊔ bigB L1 L2 S).subtype) = _
  have hcardHsub : Nat.card (Tmodel.map ψ₂.symm.toMonoidHom) = Nat.card Tmodel :=
    Subgroup.card_mapSubgroup (H := Tmodel) ψ₂.symm
  have hcardHmap : Nat.card ((Tmodel.map ψ₂.symm.toMonoidHom).map
      (L2 ⊔ bigB L1 L2 S).subtype) = Nat.card (Tmodel.map ψ₂.symm.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (L2 ⊔ bigB L1 L2 S).subtype_injective]
  rw [hcardHmap, hcardHsub, hcardTmodel]

private theorem hallPreimage_le_bigB (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2))
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K))
    (hψ₂S : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ posUnipotentSub Tag.G2 K) :
    hallPreimage ψ₂ ≤ bigB L1 L2 S := by
  classical
  have hHP : hallPreimage ψ₂ ≤ L2 ⊔ bigB L1 L2 S := by
    dsimp [hallPreimage]
    exact Subgroup.map_subtype_le _
  intro x hx
  let xP : ↥(L2 ⊔ bigB L1 L2 S) := ⟨x, hHP hx⟩
  have hxTor : ((ψ₂ xP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈
      torusSub Tag.G2 K :=
    Subgroup.mem_subgroupOf.mpr ((mem_hallPreimage ψ₂ xP).1 (by simpa [xP] using hx))
  have hxBorel : ((ψ₂ xP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈
      borelSub Tag.G2 K := G2q.torusSub_le_borelSub hxTor
  simpa [xP] using
    (hD.mem_bigB_iff_of_vertexTwo hH h1 h2 hK ψ₂ hψ₂S xP).2 hxBorel

private theorem comm_hallPreimage {K : Type} [Field K]
    (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K))
    {a b : G} (ha : a ∈ hallPreimage ψ₂) (hb : b ∈ hallPreimage ψ₂) :
    a * b = b * a := by
  classical
  have hHP : hallPreimage ψ₂ ≤ L2 ⊔ bigB L1 L2 S := by
    dsimp [hallPreimage]
    exact Subgroup.map_subtype_le _
  let aP : ↥(L2 ⊔ bigB L1 L2 S) := ⟨a, hHP ha⟩
  let bP : ↥(L2 ⊔ bigB L1 L2 S) := ⟨b, hHP hb⟩
  have haG : (((ψ₂ aP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) :
      ModGL Tag.G2 K) ∈ torusGroup Tag.G2 K :=
    (mem_hallPreimage ψ₂ aP).1 (by simpa [aP] using ha)
  have hbG : (((ψ₂ bP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) :
      ModGL Tag.G2 K) ∈ torusGroup Tag.G2 K :=
    (mem_hallPreimage ψ₂ bP).1 (by simpa [bP] using hb)
  have hcommTor : (ψ₂ aP : ↥(g2ParB K)) * ψ₂ bP = ψ₂ bP * ψ₂ aP := by
    apply Subtype.ext
    apply Subtype.ext
    exact (triangular_borel_structure.{0, 0} Tag.G2 K).1
      (((ψ₂ aP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) haG
      (((ψ₂ bP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) hbG
  have hcommP : aP * bP = bP * aP :=
    ψ₂.injective (by rw [map_mul, map_mul]; exact hcommTor)
  simpa [aP, bP] using congrArg Subtype.val hcommP

private theorem inf_hallPreimage_eq_bot {K : Type} [Field K]
    (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K))
    (hψ₂S : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ posUnipotentSub Tag.G2 K) :
    S ⊓ hallPreimage ψ₂ = ⊥ := by
  classical
  have hSP : S ≤ L2 ⊔ bigB L1 L2 S :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxS, hxH⟩ := Subgroup.mem_inf.mp hx
  let xP : ↥(L2 ⊔ bigB L1 L2 S) := ⟨x, hSP hxS⟩
  have hxTorG : (((ψ₂ xP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) :
      ModGL Tag.G2 K) ∈ torusGroup Tag.G2 K :=
    (mem_hallPreimage ψ₂ xP).1 (by simpa [xP] using hxH)
  have hxU : ((ψ₂ xP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈
      posUnipotentSub Tag.G2 K :=
    (hψ₂S xP).1 (by simpa [xP] using hxS)
  have hxUmod : (((ψ₂ xP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) :
      ModGL Tag.G2 K) ∈ posUnipotent Tag.G2 K :=
    Subgroup.mem_subgroupOf.mp hxU
  have hbot : (((ψ₂ xP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) :
      ModGL Tag.G2 K) ∈ (⊥ : Subgroup (ModGL Tag.G2 K)) := by
    rw [← torusGroup_inf_posUnipotent]
    exact Subgroup.mem_inf.mpr ⟨hxTorG, hxUmod⟩
  have hmod1 : (((ψ₂ xP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) :
      ModGL Tag.G2 K) = 1 := by simpa using hbot
  have hψ1 : ψ₂ xP = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact hmod1
  have hxP1 : xP = 1 := ψ₂.injective (by simpa using hψ1)
  exact congrArg Subtype.val hxP1

private theorem sup_hallPreimage_eq (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2))
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K))
    (hψ₂S : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ posUnipotentSub Tag.G2 K) :
    S ⊔ hallPreimage ψ₂ = bigB L1 L2 S := by
  classical
  have hHB : hallPreimage ψ₂ ≤ bigB L1 L2 S :=
    hallPreimage_le_bigB hH hD h1 h2 hK ψ₂ hψ₂S
  have hHcard : Nat.card (hallPreimage ψ₂) = (2 ^ f - 1) * (2 ^ f - 1) :=
    card_hallPreimage hK ψ₂
  have hSinfH : S ⊓ hallPreimage ψ₂ = ⊥ := inf_hallPreimage_eq_bot ψ₂ hψ₂S
  have hHnorm : hallPreimage ψ₂ ≤ Subgroup.normalizer (S : Set G) := by
    intro x hx
    exact (hD.bigB_le_normalizer hH h1 h2 (hHB hx)).2
  have hdisj : Disjoint S (hallPreimage ψ₂) := disjoint_iff.mpr hSinfH
  have hle : S ⊔ hallPreimage ψ₂ ≤ bigB L1 L2 S :=
    sup_le (le_sup_right : S ≤ bigB L1 L2 S) hHB
  have hcardSup : Nat.card ↥(S ⊔ hallPreimage ψ₂) = Nat.card ↥(bigB L1 L2 S) := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer S
      (hallPreimage ψ₂) hHnorm hdisj, hD.card_S, hHcard, hD.card_bigB hH h1 h2]
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardSup])

theorem G2qLocalData.exists_hall_of_vertexTwo
    (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2))
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K))
    (hψ₂S : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ posUnipotentSub Tag.G2 K) :
    ∃ H : Subgroup G, H ≤ bigB L1 L2 S ∧ S ⊔ H = bigB L1 L2 S ∧ S ⊓ H = ⊥ ∧
      Nat.card H = (2 ^ f - 1) * (2 ^ f - 1) ∧ (∀ a ∈ H, ∀ b ∈ H, a * b = b * a) ∧
      ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔
        (((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) ∈
          torusGroup Tag.G2 K := by
  refine ⟨hallPreimage ψ₂, hallPreimage_le_bigB hH hD h1 h2 hK ψ₂ hψ₂S,
    sup_hallPreimage_eq hH hD h1 h2 hK ψ₂ hψ₂S,
    inf_hallPreimage_eq_bot ψ₂ hψ₂S, card_hallPreimage hK ψ₂,
    fun a ha b hb => comm_hallPreimage ψ₂ ha hb, ?_⟩
  intro x
  exact mem_hallPreimage ψ₂ x

theorem G2qLocalData.exists_torus_left_of_vertexTwo (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K))
    (hψ₂S : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ posUnipotentSub Tag.G2 K)
    (hψ₂Q : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ pCoreOf 2 L1 ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ pCoreOf 2 (g2ParA K)) :
    ∃ J : Subgroup G, J ≤ bigB L1 L2 S ∧ Odd (Nat.card J) ∧
      (∀ j ∈ J, ∀ l ∈ L1, ⁅j, l⁆ ∈ pCoreOf 2 L1) ∧
      pCoreOf 2 L1 ⊓ Subgroup.centralizer (J : Set G) = ⊥ := by
  classical
  obtain ⟨H, hHB, hSH, hSinfH, hHcard, hHcomm, hψ₂H⟩ :=
    hD.exists_hall_of_vertexTwo hH h1 h2 hK ψ₂ hψ₂S
  let J : Subgroup G := H ⊓ trivOTwoQuot L1
  have hJB : J ≤ bigB L1 L2 S := inf_le_left.trans hHB
  have hcardJ : Nat.card J = 2 ^ f - 1 := by
    simpa [J] using
      (hD.torus_left_of_hall hf hH h1 h2 hHB hSH hSinfH hHcard hHcomm).2.1
  have hoddJ : Odd (Nat.card J) := by
    rw [hcardJ]
    exact CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)
  have hcommJ : ∀ j ∈ J, ∀ l ∈ L1, ⁅j, l⁆ ∈ pCoreOf 2 L1 := by
    intro j hj l hl
    have h := (mem_trivOTwoQuot.mp (Subgroup.mem_inf.mp hj).2).2 l hl
    simpa [commutatorElement_def] using h
  have hbot : pCoreOf 2 L1 ⊓ Subgroup.centralizer (J : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.mp hx
    have hfix : ∀ j ∈ J, j * x * j⁻¹ = x := by
      intro j hj
      have hcomm := Subgroup.mem_centralizer_iff.mp hxC j hj
      calc j * x * j⁻¹ = (x * j) * j⁻¹ := by rw [hcomm]
        _ = x := by group
    exact hD.eq_one_of_mem_pCoreOf_left_of_commute hf hH h1 h2 hHB hSH hSinfH hHcard
      hHcomm hK ψ₂ hψ₂S hψ₂Q hψ₂H x hxQ hfix
  exact ⟨J, hJB, hoddJ, hcommJ, hbot⟩

end CFSG.Quasithin.F112R.St84

end
