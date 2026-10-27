module

public import CFSG.Milestones.ASVolI.C135.P4c
public import CFSG.Quasithin.Vol2.Ch4Sec3C135Fin
public import CFSG.Milestones.ASVolI.C135.Cent
public import CFSG.Milestones.ASVolI.C135.P4a
public import CFSG.Milestones.ASVolI.C135.P4b

public section

namespace CFSG.ASVolI

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open CFSG.ASVolI.ChC
open CFSG.Quasithin.H13.Ch4.C135 (QC cnj coe_cnj slNat slNat_surjective dualHom coe_dualHom
  moduleAct_true_eq le_normalizer_centerOf le_normalizer_bot fixAll)
open scoped Matrix commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Bound

variable {X R L : Subgroup G} {F : Type} [Field F] [Fintype F] [CharP F 2]
  {α : ↥L →* ↥(StatedSL 3 F)}

theorem burnsideC135_card_elemAb_le {n : ℕ} (hF : Fintype.card F = 2 ^ n) (hMS : IsMSPair X R)
    (hG : (X : Set G) = (L : Set G) * (R : Set G)) (hα : IsModO2Surj L α) (hLX : L ≤ X)
    (hXL : X ≤ Subgroup.normalizer (L : Set G)) (hQO : pCoreOf 2 L = c134Q X L)
    (hP : pCoreOf 2 X = pCoreOf 2 L)
    (h1 : IsSumOfNaturalModulesVia L (centerOf (c134Q X L)) ⊥ α false 1)
    (h2 : IsSumOfNaturalModulesVia L (c134Q X L) (centerOf (c134Q X L)) α true 2)
    {B : Subgroup G} (hBX : B ≤ X) (hB : IsElemAbelian 2 B) :
    Nat.card B ≤ Fintype.card F ^ 6 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCU := burnsideC135_centralizer_U_le' hMS hG hα hLX hXL h1
  rw [← hQO] at h1 h2 hCU
  rw [hP] at hCU
  have hcomm : ∀ x ∈ pCoreOf 2 L, ∀ y ∈ pCoreOf 2 L,
      x * y * x⁻¹ * y⁻¹ ∈ centerOf (pCoreOf 2 L) := fun x hx y hy =>
    burnsideC135_comm_mem_U h2 hx hy
  have hXQ : X ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    hXL.trans (normalizer_le_normalizer_pCoreOf 2 L)
  have hXU : X ≤ Subgroup.normalizer (centerOf (pCoreOf 2 L) : Set G) :=
    le_normalizer_centerOf hXQ
  have hBp : IsPGroup 2 B := fun x => ⟨1, Subtype.ext (by simpa using hB.2 x x.2)⟩
  have hcommB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    CFSG.Quasithin.H13.Ch4.C135.mul_comm_of_isElemAbelian hB hx hy
  obtain ⟨S₀, hS₀, hBS₀⟩ := CFSG.QuasithinUnique.EscapingLocal.exists_isSylowTwoOf_ge hBX hBp
  have hQS₀ : pCoreOf 2 L ≤ S₀ := by
    rw [← hP]
    exact CFSG.Quasithin.pCoreOf_two_le_of_isSylowTwoOf hS₀
  obtain ⟨β', βU, hβ's, hβ'k, hβ'eq, hD, hS₀W⟩ :=
    burnsideC135_exists_invariant_dualSplit hα hLX hXL hS₀ hQS₀ hXQ h1 h2
  by_cases hBQ' : B ≤ pCoreOf 2 L
  · exact burnsideC135_card_abelian_le hD hcomm hβ'k hBQ' hcommB
  have hβUinj : Function.Injective βU := burnsideC135_βU_injective hD
  let q0 : QC (centerOf (pCoreOf 2 L)) ⊥ F :=
    { κ := fun u => Multiplicative.toAdd (βU u)
      mul := fun u v => by
        show Multiplicative.toAdd (βU (u * v)) =
          Multiplicative.toAdd (βU u) + Multiplicative.toAdd (βU v)
        rw [map_mul, toAdd_mul]
      surj := fun v => by
        obtain ⟨u, hu⟩ := hD.natU_onto (Multiplicative.ofAdd v)
        exact ⟨u, (congrArg Multiplicative.toAdd hu).trans (toAdd_ofAdd v)⟩
      ker := fun u => by
        show Multiplicative.toAdd (βU u) = 0 ↔ (u : G) ∈ (⊥ : Subgroup G)
        rw [Subgroup.mem_bot]
        constructor
        · intro h
          have h1 : βU u = βU 1 := by
            rw [map_one]
            exact Multiplicative.toAdd.injective h
          exact congrArg Subtype.val (hβUinj h1)
        · intro h
          have : u = 1 := Subtype.ext h
          rw [this, map_one]
          rfl }
  let q1 : QC (burnsideC135_Wc β' 1) (centerOf (pCoreOf 2 L)) F :=
    { κ := fun w => Multiplicative.toAdd (burnsideC135_βc β' 1 w)
      mul := fun u v => by
        show Multiplicative.toAdd (burnsideC135_βc β' 1 (u * v)) =
          Multiplicative.toAdd (burnsideC135_βc β' 1 u) +
            Multiplicative.toAdd (burnsideC135_βc β' 1 v)
        rw [map_mul, toAdd_mul]
      surj := fun v => by
        obtain ⟨u, hu⟩ := hD.dual₁_onto (Multiplicative.ofAdd v)
        exact ⟨u, (congrArg Multiplicative.toAdd hu).trans (toAdd_ofAdd v)⟩
      ker := fun w => by
        show Multiplicative.toAdd (burnsideC135_βc β' 1 w) = 0 ↔
          (w : G) ∈ centerOf (pCoreOf 2 L)
        have h := hD.dual₁_ker
        constructor
        · intro h0
          have h3 : w ∈ (burnsideC135_βc β' 1).ker := by
            rw [MonoidHom.mem_ker]
            exact Multiplicative.toAdd.injective h0
          rw [h, Subgroup.mem_subgroupOf] at h3
          exact h3
        · intro h0
          have h3 : w ∈ (burnsideC135_βc β' 1).ker := by
            rw [h, Subgroup.mem_subgroupOf]
            exact h0
          rw [MonoidHom.mem_ker] at h3
          rw [h3]
          rfl }
  let q2 : QC (pCoreOf 2 L) (burnsideC135_Wc β' 1) F :=
    { κ := fun q => Multiplicative.toAdd (β' q) 1
      mul := fun u v => by
        show Multiplicative.toAdd (β' (u * v)) 1 =
          Multiplicative.toAdd (β' u) 1 + Multiplicative.toAdd (β' v) 1
        rw [map_mul, toAdd_mul, Pi.add_apply]
      surj := fun v => by
        obtain ⟨u, hu⟩ := hβ's (Multiplicative.ofAdd (fun _ => v))
        refine ⟨u, ?_⟩
        show Multiplicative.toAdd (β' u) 1 = v
        rw [hu]
        rfl
      ker := fun q => by
        show Multiplicative.toAdd (β' q) 1 = 0 ↔ (q : G) ∈ burnsideC135_Wc β' 1
        constructor
        · intro h0
          exact burnsideC135_mem_Wc.mpr ⟨q.2, h0⟩
        · intro h0
          obtain ⟨hh, h3⟩ := burnsideC135_mem_Wc.mp h0
          exact h3 }
  have hLU : L ≤ Subgroup.normalizer (centerOf (pCoreOf 2 L) : Set G) := hLX.trans hXU
  have hLW : L ≤ Subgroup.normalizer (burnsideC135_Wc β' 1 : Set G) := hD.norm₁
  have hLQ : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := hLX.trans hXQ
  have hnat₀ : ∀ (g : ↥L) (x : ↥(centerOf (pCoreOf 2 L))), q0.κ (cnj (hLU g.2) x) =
      ((slNat α g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        q0.κ x := fun g x => hD.natU_act g x (cnj (hLU g.2) x) rfl
  have hnat₁ : ∀ (g : ↥L) (x : ↥(burnsideC135_Wc β' 1)), q1.κ (cnj (hLW g.2) x) =
      ((dualHom (slNat α g) : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        q1.κ x := fun g x => by
    show Multiplicative.toAdd (burnsideC135_βc β' 1 (cnj (hLW g.2) x)) =
      ((dualHom (slNat α g) : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        Multiplicative.toAdd (burnsideC135_βc β' 1 x)
    rw [hD.dual₁_act g x (cnj (hLW g.2) x) rfl, coe_dualHom]
  have hnat₂ : ∀ (g : ↥L) (x : ↥(pCoreOf 2 L)), q2.κ (cnj (hLQ g.2) x) =
      ((dualHom (slNat α g) : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        q2.κ x := fun g x => by
    show Multiplicative.toAdd (β' (cnj (hLQ g.2) x)) 1 =
      ((dualHom (slNat α g) : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        Multiplicative.toAdd (β' x) 1
    rw [hβ'eq g x (cnj (hLQ g.2) x) rfl 1, moduleAct_true_eq]
  have hBU : B ≤ Subgroup.normalizer (centerOf (pCoreOf 2 L) : Set G) := hBX.trans hXU
  have hBW : B ≤ Subgroup.normalizer (burnsideC135_Wc β' 1 : Set G) := hBS₀.trans hS₀W
  have hBQ : B ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := hBX.trans hXQ
  have hBL : B ≤ Subgroup.normalizer (L : Set G) := hBX.trans hXL
  have hBb := le_normalizer_bot B
  have hker₀ : ∀ b : ↥B, q0.rep hBU hBb b = 1 → (b : G) ∈ pCoreOf 2 L := by
    intro b h
    refine hCU ⟨hBX b.2, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    have h3 := q0.rep_κ hBU hBb b ⟨u, hu⟩
    rw [h, Equiv.Perm.one_apply] at h3
    have h4 : (⟨u, hu⟩ : ↥(centerOf (pCoreOf 2 L))) = cnj (hBU b.2) ⟨u, hu⟩ :=
      hβUinj (Multiplicative.toAdd.injective h3)
    have h7 : u = (b : G) * u * (b : G)⁻¹ := by
      have h8 := congrArg Subtype.val h4
      rw [coe_cnj] at h8
      exact h8
    calc u * (b : G) = (b : G) * u * (b : G)⁻¹ * b := by rw [← h7]
      _ = b * u := by group
  have hne : (q0.rep hBU hBb).range ≠ ⊥ := by
    intro h
    apply hBQ'
    intro b hb
    apply hker₀ ⟨b, hb⟩
    rw [← Subgroup.mem_bot, ← h]
    exact ⟨⟨b, hb⟩, rfl⟩
  obtain ⟨o1, o2⟩ := burnsideC135_offender (slNat α) (slNat_surjective hα.1) q0 q1 q2 hLU hLW
    hLQ hnat₀ hnat₁ hnat₂ hBU hBW hBQ hBL hB hne
  have hAB : Nat.card B ≤ Nat.card (q0.rep hBU hBb).range * Nat.card ↥(B ⊓ pCoreOf 2 L) := by
    rw [← Subgroup.card_ker_mul_card_range (q0.rep hBU hBb), mul_comm]
    refine Nat.mul_le_mul_left _ (Nat.card_le_card_of_injective (fun x => ⟨x.1.1, x.1.2,
      hker₀ x.1 (MonoidHom.mem_ker.mp x.2)⟩) ?_)
    intro x y hxy
    have h := Subtype.ext_iff.mp hxy
    exact Subtype.ext (Subtype.ext h)
  have hAU : Nat.card ↥(B ⊓ centerOf (pCoreOf 2 L)) ≤ Nat.card (fixAll (q0.rep hBU hBb)) := by
    refine Nat.card_le_card_of_injective (fun x => ⟨q0.κ ⟨x, x.2.2⟩, fun a =>
      q0.rep_κ_of_commute hBU hBb a ⟨x, x.2.2⟩ (hcommB _ a.2 _ x.2.1)⟩) ?_
    intro x y hxy
    have h : Multiplicative.toAdd (βU ⟨x, x.2.2⟩) = Multiplicative.toAdd (βU ⟨y, y.2.2⟩) :=
      Subtype.ext_iff.mp hxy
    have h' := hβUinj (Multiplicative.toAdd.injective h)
    exact Subtype.ext (congrArg (fun z : ↥(centerOf (pCoreOf 2 L)) => (z : G)) h')
  have hAW : Nat.card ↥(B ⊓ burnsideC135_Wc β' 1) ≤
      Nat.card (fixAll (q0.rep hBU hBb)) * Nat.card (fixAll (q1.rep hBW hBU)) := by
    have hle : B ⊓ burnsideC135_Wc β' 1 ≤ burnsideC135_Wc β' 1 := inf_le_right
    rw [← Subgroup.card_ker_mul_card_range (q1.hom.comp (Subgroup.inclusion hle))]
    refine Nat.mul_le_mul ((Nat.card_le_card_of_injective (fun x =>
      (⟨x.1.1, x.1.2.1, (q1.ker (Subgroup.inclusion hle x.1)).mp
        (congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp x.2))⟩ :
          ↥(B ⊓ centerOf (pCoreOf 2 L)))) ?_).trans hAU) ?_
    · intro x y h
      have h' := Subtype.ext_iff.mp h
      exact Subtype.ext (Subtype.ext h')
    · refine Nat.card_le_card_of_injective (fun y => ⟨Multiplicative.toAdd y.1, ?_⟩) ?_
      · obtain ⟨x, hx⟩ := y.2
        intro a
        rw [← hx]
        exact q1.rep_κ_of_commute _ _ a (Subgroup.inclusion hle x) (hcommB _ a.2 _ x.2.1)
      · intro x y h
        have h' := Subtype.ext_iff.mp h
        exact Subtype.ext (Multiplicative.toAdd.injective h')
  have hBT : ∀ S : Set (Fin 3 → F), (∀ x : ↥(B ⊓ pCoreOf 2 L), q2.κ ⟨x, x.2.2⟩ ∈ S) →
      Nat.card ↥(B ⊓ pCoreOf 2 L) ≤ Nat.card ↥(B ⊓ burnsideC135_Wc β' 1) * Nat.card S := by
    intro S hS
    have hle : B ⊓ burnsideC135_Wc β' 1 ≤ B ⊓ pCoreOf 2 L :=
      inf_le_inf_left _ (burnsideC135_Wc_le 1)
    refine burnsideC135_card_le_of_hom hle (fun x => q2.κ ⟨x, x.2.2⟩)
      (fun x y => q2.mul ⟨x, x.2.2⟩ ⟨y, y.2.2⟩) (fun x => ?_) S hS
    show q2.κ ⟨x, x.2.2⟩ = 0 ↔ (x : G) ∈ B ⊓ burnsideC135_Wc β' 1
    rw [q2.ker]
    exact ⟨fun h => ⟨x.2.1, h⟩, fun h => h.2⟩
  have hlt : Nat.card B < 2 * Nat.card F ^ 6 := by
    by_cases hII : ∃ w ∈ B ⊓ burnsideC135_Wc β' 1, w ∉ centerOf (pCoreOf 2 L)
    ·
      obtain ⟨w, hw, hwU⟩ := hII
      have hS : ∀ x : ↥(B ⊓ pCoreOf 2 L), q2.κ ⟨x, x.2.2⟩ ∈
          {v : Fin 3 → F | ∃ c : F, v = c • Multiplicative.toAdd
            (β' ⟨w, burnsideC135_Wc_le 1 hw.2⟩) 0} := fun x =>
        (burnsideC135_commute_iff_coords hD hcomm hw.2 hwU ⟨x, x.2.2⟩).mp
          (hcommB _ hw.1 _ x.2.1)
      have hB1 := hBT _ hS
      have hl := burnsideC135_card_line
        (Multiplicative.toAdd (β' ⟨w, burnsideC135_Wc_le 1 hw.2⟩) 0)
      calc Nat.card B ≤ Nat.card (q0.rep hBU hBb).range * Nat.card ↥(B ⊓ pCoreOf 2 L) := hAB
        _ ≤ Nat.card (q0.rep hBU hBb).range * ((Nat.card (fixAll (q0.rep hBU hBb)) *
              Nat.card (fixAll (q1.rep hBW hBU))) * Nat.card F) :=
            Nat.mul_le_mul_left _ (hB1.trans (Nat.mul_le_mul hAW
              (hl.trans Nat.card_eq_fintype_card.ge)))
        _ = Nat.card (q0.rep hBU hBb).range * Nat.card F * Nat.card (fixAll (q0.rep hBU hBb)) *
              Nat.card (fixAll (q1.rep hBW hBU)) := by ring
        _ < 2 * Nat.card F ^ 6 := o1
    ·
      push Not at hII
      have hWU : B ⊓ burnsideC135_Wc β' 1 ≤ B ⊓ centerOf (pCoreOf 2 L) := fun v hv =>
        ⟨hv.1, hII v hv⟩
      have hS : ∀ x : ↥(B ⊓ pCoreOf 2 L), q2.κ ⟨x, x.2.2⟩ ∈
          {v : Fin 3 → F | ∀ a, q2.rep hBQ hBW a v = v} := fun x a =>
        q2.rep_κ_of_commute hBQ hBW a ⟨x, x.2.2⟩ (hcommB _ a.2 _ x.2.1)
      have hB1 := hBT _ hS
      calc Nat.card B ≤ Nat.card (q0.rep hBU hBb).range * Nat.card ↥(B ⊓ pCoreOf 2 L) := hAB
        _ ≤ Nat.card (q0.rep hBU hBb).range * (Nat.card (fixAll (q0.rep hBU hBb)) *
              Nat.card (fixAll (q2.rep hBQ hBW))) :=
            Nat.mul_le_mul_left _ (hB1.trans (Nat.mul_le_mul
              ((Subgroup.card_le_of_le hWU).trans hAU) le_rfl))
        _ = Nat.card (q0.rep hBU hBb).range * Nat.card (fixAll (q0.rep hBU hBb)) *
              Nat.card (fixAll (q2.rep hBQ hBW)) := by ring
        _ < 2 * Nat.card F ^ 6 := o2
  obtain ⟨k, hk⟩ := hBp.exists_card_eq
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  rw [hFn, ← pow_mul, hk] at hlt
  rw [hk, hF, ← pow_mul]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  by_contra hcon
  push Not at hcon
  have h3 : 2 ^ (n * 6 + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hcon
  rw [pow_succ] at h3
  linarith

end Bound

end CFSG.ASVolI

end
