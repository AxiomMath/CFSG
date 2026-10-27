module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesInternal
public import CFSG.Quasithin.Recognition.Stroth.Str86LinearVertex
public import CFSG.Quasithin.Vol2.Ch3E215MH

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem l2_chiefStep_natural {H V L N A : Subgroup G} {m : ℕ} (hm2 : 2 ≤ m)
    (hL2 : IsL2Quot m (oTwoQuot ↥H))
    (hV : IsElemAbelian 2 V) (hVH : V ≤ H)
    (hstep : IsChiefStep H V L N) (hnc : ¬ IsCentralStep H L N)
    (hA : IsElemAbelian 2 A) (hAH : A ≤ H)
    (hstep_eq : (centralizerMod L N A).relIndex N = 2 ^ m)
    (hA_eq : (A ⊓ pCoreOf 2 H).relIndex A = 2 ^ m) :
    let hE := CFSG.Quasithin.isElemAbelian_chiefMod hstep hVH hV.isPGroup
    letI _cg : CommGroup ↥(Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
    letI _mod : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
    ∃ (e : oTwoQuot ↥H ≃* SL(2, GaloisField 2 m))
      (ρ : Representation (ZMod 2) SL(2, GaloisField 2 m) (Additive (Ch3z.chiefMod L N)))
      (φ : Additive (Ch3z.chiefMod L N) ≃+ (Fin 2 → GaloisField 2 m)),
      Fact ρ.IsIrreducible ∧ (∃ g, ρ g ≠ 1) ∧
        (∀ (h : ↥H) (w : Ch3z.chiefMod L N),
          ρ (e (QuotientGroup.mk h)) (Additive.ofMul w) =
            Additive.ofMul (l2ChiefSectionAction hstep hE h w)) ∧
        (∀ g w, φ (ρ g w) = (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 m)).mulVec (φ w)) ∧
        ∃ T : Sylow 2 (oTwoQuot ↥H),
          (T : Subgroup (oTwoQuot ↥H)) =
            (A.subgroupOf H).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)) := by
  classical
  let F := GaloisField 2 m
  haveI : Fintype F := Fintype.ofFinite _
  have hm1 : 1 ≤ m := by omega
  have hVp : IsPGroup 2 ↥V := hV.isPGroup
  let hE := CFSG.Quasithin.isElemAbelian_chiefMod hstep hVH hVp
  letI _cg : CommGroup ↥(Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
  letI _mod : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
  obtain ⟨e₀, ρ, hρirr, hρnt, hρcompat⟩ :=
    exists_l2ChiefSectionRep (H := H) (U := V) (L := L) (N := N) hm2 hL2 hVp hVH hstep hnc
  let e : oTwoQuot ↥H ≃* SL(2, F) := e₀
  let π : ↥H →* oTwoQuot ↥H := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)
  let φH : ↥H →* SL(2, F) := e.toMonoidHom.comp π
  let A₀ : Subgroup ↥H := A.subgroupOf H
  let B : Subgroup SL(2, F) := A₀.map φH
  have hFcard : Fintype.card F = 2 ^ m := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 m (by omega)]
  have hker : φH.ker = CFSG.Open.pCore 2 ↥H := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)) x = 1 :=
        e.injective (by rw [map_one]; exact hx)
      exact (QuotientGroup.eq_one_iff (N := CFSG.Open.pCore 2 ↥H) x).mp h1
    · intro hx
      have hq : (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)) x = 1 :=
        (QuotientGroup.eq_one_iff (N := CFSG.Open.pCore 2 ↥H) x).mpr hx
      show e.toMonoidHom (π x) = 1
      rw [show π x = (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)) x from rfl, hq, map_one]
  have hsub : (pCoreOf 2 H).subgroupOf H = CFSG.Open.pCore 2 ↥H := by
    unfold pCoreOf Subgroup.subgroupOf
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hrelA : (CFSG.Open.pCore 2 ↥H).relIndex A₀ = (A ⊓ pCoreOf 2 H).relIndex A := by
    rw [← hsub, Subgroup.relIndex_subgroupOf hAH,
      ← Subgroup.inf_relIndex_right (pCoreOf 2 H) A, inf_comm]
  have hcardB : Nat.card B = (A ⊓ pCoreOf 2 H).relIndex A := by
    have h := CFSG.Quasithin.Ch3E215M.card_map_eq_relIndex_ker φH A₀
    rw [hker, hrelA] at h
    exact h.symm
  have hBcard : Nat.card B = 2 ^ m := hcardB.trans hA_eq
  have hBe : IsElemAbelian 2 B :=
    CFSG.Quasithin.Ch3E215M.isElemAbelian_map φH
      (CFSG.Open.IsElemAbelian.subgroupOf hA H)
  have hBne : B ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hBcard
    have hge : 4 ≤ 2 ^ m := by
      simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hm2
    omega
  let δ : Subgroup (SecQuot (Subgroup.normalizer (L : Set G)) L) :=
    secImg (Subgroup.normalizer (L : Set G)) L A
  let C₀ : Subgroup (MulAut ↥(Ch3z.chiefMod L N)) := autOn δ (Ch3z.chiefMod L N)
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hstep.1.1.trans hVH).trans hHL
  have hAK : A ≤ Subgroup.normalizer (L : Set G) := hAH.trans hHL
  have hAN : A ≤ Subgroup.normalizer (N : Set G) := hAH.trans hHN
  have hC0eq : C₀ = Ch3z.chiefImg hHL hHN A :=
    (Ch3z.chiefImg_eq_autOn hHL hHN hAH).symm
  have haction_mem : ∀ (a : ↥H), (a : G) ∈ A →
      l2ChiefSectionAction hstep hE a ∈ C₀ := by
    intro a ha
    have hmem : Ch3z.chiefPsi hHL hHN a ∈ Ch3z.chiefImg hHL hHN A :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ha)
    have hEq : l2ChiefSectionAction hstep hE a = Ch3z.chiefPsi hHL hHN a :=
      l2ChiefSectionAction_eq_chiefPsi hstep hE a
    rw [hC0eq, hEq]
    exact hmem
  have hto : ∀ w : {w : Additive (Ch3z.chiefMod L N) // ∀ b ∈ B, ρ b w = w},
      Additive.toMul w.1 ∈ fixV C₀ := by
    intro w c hc
    have hmem : c ∈ Ch3z.chiefImg hHL hHN A := by
      rw [← hC0eq]
      exact hc
    obtain ⟨a₀, ha₀, haeq⟩ := Subgroup.mem_map.mp hmem
    have ha : (a₀ : G) ∈ A := Subgroup.mem_subgroupOf.mp ha₀
    have hb : φH a₀ ∈ B := Subgroup.mem_map_of_mem _ ha₀
    have h1 := w.2 (φH a₀) hb
    have h2 : ρ (e (QuotientGroup.mk a₀)) w.1 =
        Additive.ofMul (l2ChiefSectionAction hstep hE a₀ (Additive.toMul w.1)) := by
      simpa using hρcompat a₀ (Additive.toMul w.1)
    have h3 : Additive.toMul (ρ (e (QuotientGroup.mk a₀)) w.1) = Additive.toMul w.1 :=
      congrArg Additive.toMul h1
    have h4 : l2ChiefSectionAction hstep hE a₀ (Additive.toMul w.1) = Additive.toMul w.1 := by
      have h5 := h3
      rw [h2] at h5
      exact h5
    have hcval : (c : MulAut ↥(Ch3z.chiefMod L N)) = l2ChiefSectionAction hstep hE a₀ := by
      rw [← haeq]
      exact (l2ChiefSectionAction_eq_chiefPsi hstep hE a₀).symm
    rw [hcval]
    exact h4
  have hinv : ∀ v : ↥(fixV C₀), ∀ b ∈ B,
      ρ b (Additive.ofMul v.1) = Additive.ofMul v.1 := by
    intro v b hb
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp hb
    have ha : (a₀ : G) ∈ A := Subgroup.mem_subgroupOf.mp ha₀
    have h2 : ρ (φH a₀) (Additive.ofMul v.1) =
        Additive.ofMul (l2ChiefSectionAction hstep hE a₀ v.1) := by
      simpa [φH, π] using hρcompat a₀ v.1
    rw [h2]
    congr 1
    exact v.2 _ (haction_mem a₀ ha)
  have hleft : ∀ w : {w : Additive (Ch3z.chiefMod L N) // ∀ b ∈ B, ρ b w = w},
      (⟨Additive.ofMul (Additive.toMul w.1),
        hinv ⟨Additive.toMul w.1, hto w⟩⟩ : {w : Additive (Ch3z.chiefMod L N) //
          ∀ b ∈ B, ρ b w = w}) = w := by
    intro w
    apply Subtype.ext
    rfl
  have hright : ∀ v : ↥(fixV C₀),
      (⟨Additive.toMul (Additive.ofMul v.1), hto ⟨Additive.ofMul v.1, hinv v⟩⟩ :
        ↥(fixV C₀)) = v := by
    intro v
    apply Subtype.ext
    rfl
  have hfixcard : Nat.card {w : Additive (Ch3z.chiefMod L N) // ∀ b ∈ B, ρ b w = w} =
      Nat.card ↥(fixV C₀) :=
    Nat.card_congr (Equiv.mk (fun w => ⟨Additive.toMul w.1, hto w⟩)
      (fun v => ⟨Additive.ofMul v.1, hinv v⟩) hleft hright)
  have hfixindex : (fixV C₀).index = 2 ^ m := by
    let _ : IsMulCommutative ↥(Ch3z.chiefMod L N) := hE.1
    let _ : CommGroup ↥(Ch3z.chiefMod L N) := IsMulCommutative.instCommGroup
    have hfixeq : fixV C₀ =
        (Subgroup.centralizer δ : Subgroup (SecQuot (Subgroup.normalizer (L : Set G)) L)).subgroupOf
          (Ch3z.chiefMod L N) := by
      exact AutOn.fixV_autOn_eq (V := Ch3z.chiefMod L N) (L := δ)
        (secImg_le_normalizer_secImg hAN)
    have hrel : (Ch3z.chiefMod L N ⊓
        Subgroup.centralizer δ : Subgroup (SecQuot (Subgroup.normalizer (L : Set G)) L)).relIndex
          (Ch3z.chiefMod L N) = (centralizerMod L N A).relIndex N :=
      CFSG.Quasithin.relIndex_secImg_fix (K := L) (E := N) (X := A) hAK hNL
    have h1 : (fixV C₀).index = (Ch3z.chiefMod L N ⊓
        Subgroup.centralizer δ : Subgroup (SecQuot (Subgroup.normalizer (L : Set G)) L)).relIndex
          (Ch3z.chiefMod L N) := by
      rw [hfixeq]
      change (Subgroup.centralizer δ).relIndex (Ch3z.chiefMod L N) =
        (Ch3z.chiefMod L N ⊓ Subgroup.centralizer δ).relIndex (Ch3z.chiefMod L N)
      rw [← Subgroup.inf_relIndex_right (Subgroup.centralizer δ) (Ch3z.chiefMod L N), inf_comm]
    rw [h1, hrel, hstep_eq]
  have hoff : Nat.card (Additive (Ch3z.chiefMod L N)) ≤ Nat.card B *
      Nat.card {w : Additive (Ch3z.chiefMod L N) // ∀ b ∈ B, ρ b w = w} := by
    have hcardW : Nat.card (Additive (Ch3z.chiefMod L N)) = Nat.card (Ch3z.chiefMod L N) :=
      Nat.card_congr Additive.ofMul
    have hmul : Nat.card ↥(fixV C₀) * (fixV C₀).index = Nat.card (Ch3z.chiefMod L N) :=
      Subgroup.card_mul_index (fixV C₀)
    have hEq : Nat.card (Additive (Ch3z.chiefMod L N)) =
        Nat.card B * Nat.card {w : Additive (Ch3z.chiefMod L N) // ∀ b ∈ B, ρ b w = w} := by
      calc Nat.card (Additive (Ch3z.chiefMod L N))
          = Nat.card (Ch3z.chiefMod L N) := hcardW
        _ = Nat.card ↥(fixV C₀) * (fixV C₀).index := hmul.symm
        _ = Nat.card B * Nat.card {w : Additive (Ch3z.chiefMod L N) // ∀ b ∈ B, ρ b w = w} := by
            rw [hfixindex, hBcard, ← hfixcard, mul_comm]
    exact le_of_eq hEq
  haveI : CFSG.IsElementaryAbelian 2 B := hBe.isElementaryAbelian
  obtain ⟨φnat, hφnat, -, -, -, ⟨-, -, -, -, -, hP, -⟩⟩ :=
    CFSG.QuasithinUnique.Setup.SL2Modules.binary_SL2_internal_offender_natural_module
      hm1 hFcard ρ hρirr.1 hρnt B hBne hoff
  refine ⟨e, ρ, φnat, hρirr, hρnt, hρcompat, hφnat, ?_⟩
  obtain ⟨P, hP⟩ := hP
  refine ⟨Sylow.mapSurjective (f := e.symm.toMonoidHom)
    (by simpa using e.symm.surjective) P, ?_⟩
  rw [Sylow.coe_mapSurjective]
  rw [hP]
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx
    obtain ⟨a₀, ha₀, hay⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.mem_map.mpr ⟨a₀, ha₀, ?_⟩
    rw [← hxy, ← hay]
    simp [φH, π]
  · intro hx
    obtain ⟨a₀, ha₀, hax⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨φH a₀, Subgroup.mem_map_of_mem _ ha₀, ?_⟩
    rw [← hax]
    simp [φH, π]

end CFSG.Quasithin.Stroth
