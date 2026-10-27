module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGlobDefs
import CFSG.LocalAnalysis.StandardType.GGResIPumpLineAux
public import CFSG.LocalAnalysis.StandardType.GGQTwoLocalDefs

public section

namespace CFSG.StandardType.QTwo

private lemma qTwoGBB_ggLin_ofMul_mul_inv
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] {E : Type*} [Group E]
    (ι : Additive E ≃+ V) (φ : MulAut E) (b : E) :
    ι (Additive.ofMul (φ b * b⁻¹)) =
      ggLin (p := p) ι φ (ι (Additive.ofMul b)) - ι (Additive.ofMul b) := by
  rw [ofMul_mul, map_add, ofMul_inv, map_neg, ← ggLin_apply_ofMul (p := p) ι φ b]
  abel

private lemma qTwoGBB_mem_ggLinCom_of_mem_ggCommSpace
    {G : Type} [Group G] {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (A : Subgroup (MulAut ↥Bs))
    {b : ↥Bs} (hb : b ∈ ggCommSpace Bs A) :
    ι (Additive.ofMul b) ∈ ggLinCom ((A.map (ggLin (p := 3) ι)) : Set (V ≃ₗ[ZMod 3] V)) := by
  refine Subgroup.closure_induction (p := fun b _ => ι (Additive.ofMul b) ∈
    ggLinCom ((A.map (ggLin (p := 3) ι)) : Set (V ≃ₗ[ZMod 3] V))) ?_ ?_ ?_ ?_ hb
  · intro x hx
    obtain ⟨a, ha, b', hc⟩ := hx
    rw [hc, qTwoGBB_ggLin_ofMul_mul_inv (p := 3)]
    rw [ggLinCom]
    refine Submodule.mem_iSup_of_mem (ggLin (p := 3) ι a)
      (Submodule.mem_iSup_of_mem (Subgroup.mem_map_of_mem (ggLin (p := 3) ι) ha) ?_)
    rw [ggLinMove]
    exact LinearMap.mem_range.mpr ⟨ι (Additive.ofMul b'), rfl⟩
  · simp
  · intro x y _ _ ihx ihy
    rw [ofMul_mul, map_add]
    exact add_mem ihx ihy
  · intro x _ ih
    rw [ofMul_inv, map_neg]
    exact neg_mem ih

private lemma qTwoGBB_mem_ggCommSpace_of_mem_ggLinCom
    {G : Type} [Group G] {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (A : Subgroup (MulAut ↥Bs))
    {b : ↥Bs}
    (hb : ι (Additive.ofMul b) ∈ ggLinCom ((A.map (ggLin (p := 3) ι)) : Set (V ≃ₗ[ZMod 3] V))) :
    b ∈ ggCommSpace Bs A := by
  let Im : Submodule (ZMod 3) V :=
    AddSubgroup.toZModSubmodule 3 ((ggCommSpace Bs A).toAddSubgroup.map ι.toAddMonoidHom)
  have hW_le_Im : ggLinCom ((A.map (ggLin (p := 3) ι)) : Set (V ≃ₗ[ZMod 3] V)) ≤ Im := by
    rw [ggLinCom]
    refine _root_.iSup_le fun a => ?_
    refine _root_.iSup_le fun ha => ?_
    obtain ⟨a', ha', hga⟩ := Subgroup.mem_map.mp (SetLike.mem_coe.mp ha)
    rw [← hga]
    intro v hv
    rw [ggLinMove, LinearMap.mem_range] at hv
    obtain ⟨x, rfl⟩ := hv
    obtain ⟨b', rfl⟩ : ∃ b' : ↥Bs, ι (Additive.ofMul b') = x :=
      ⟨Additive.toMul (ι.symm x), by simp⟩
    show ((ggLin (p := 3) ι a') (ι (Additive.ofMul b')) - ι (Additive.ofMul b') : V) ∈ Im
    rw [← qTwoGBB_ggLin_ofMul_mul_inv (p := 3)]
    have hmem : a' b' * b'⁻¹ ∈ ggCommSpace Bs A :=
      Subgroup.subset_closure ⟨a', ha', b', rfl⟩
    exact AddSubgroup.mem_map_of_mem ι.toAddMonoidHom (by simpa using hmem)
  have hb_Im : ι (Additive.ofMul b) ∈ Im := hW_le_Im hb
  change ι (Additive.ofMul b) ∈ (ggCommSpace Bs A).toAddSubgroup.map ι.toAddMonoidHom at hb_Im
  rw [AddSubgroup.mem_map] at hb_Im
  obtain ⟨c, hc, hcv⟩ := hb_Im
  obtain ⟨c', hc'eq⟩ : ∃ c' : ↥Bs, c = Additive.ofMul c' := ⟨Additive.toMul c, by simp⟩
  rw [hc'eq] at hcv hc
  have hc'' : c' = b := by
    apply Additive.ofMul.injective
    apply ι.injective
    simpa using hcv
  rw [hc''] at hc
  simpa using hc

private lemma qTwoGBB_ggLinCom_mono
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {A B : Set (V ≃ₗ[ZMod 3] V)} (h : A ⊆ B) :
    ggLinCom A ≤ ggLinCom B := by
  rw [ggLinCom, ggLinCom]
  refine _root_.iSup_le fun a => ?_
  refine _root_.iSup_le fun ha => ?_
  exact le_iSup₂_of_le a (h ha) le_rfl

private lemma qTwoGBB_commSpace_eq_ggSpanSub
    {G : Type} [Group G] {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (A : Subgroup (MulAut ↥Bs)) :
    ggCommSpace Bs A =
      (ggSpanSub (p := 3) ι (ggLinCom ((A.map (ggLin (p := 3) ι)) : Set (V ≃ₗ[ZMod 3] V)))).subgroupOf Bs := by
  ext b
  rw [Subgroup.mem_subgroupOf, coe_mem_ggSpanSub_iff]
  constructor
  · intro hb
    exact qTwoGBB_mem_ggLinCom_of_mem_ggCommSpace ι A hb
  · intro hb
    exact qTwoGBB_mem_ggCommSpace_of_mem_ggLinCom ι A hb

private lemma qTwoGBB_bridge_card
    {G : Type} [Group G] [Finite G] (Bs : Subgroup G) (A : Subgroup (MulAut ↥Bs))
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V) [Finite V] :
    Nat.card (ggCommSpace Bs A) = 3 ^ Module.finrank (ZMod 3)
      (ggLinCom ((A.map (ggLin (p := 3) ι)) : Set (V ≃ₗ[ZMod 3] V))) := by
  let W : Submodule (ZMod 3) V := ggLinCom ((A.map (ggLin (p := 3) ι)) : Set (V ≃ₗ[ZMod 3] V))
  have hcard : Nat.card (ggCommSpace Bs A) = Nat.card W := by
    rw [qTwoGBB_commSpace_eq_ggSpanSub ι A]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (ggSpanSub_le_bs ι W)).toEquiv]
    exact card_ggSpanSub ι W
  rw [hcard, Module.natCard_eq_pow_finrank (K := ZMod 3) (V := W), Nat.card_zmod]

theorem qTwo_bar_dim
    {G : Type} [Group G] [Finite G] (B Bs L D J : Subgroup G) (x : G)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V)
    {m : ℕ} (hm : 5 ≤ m) (hLM : QTwoLocalModel m Bs L x) :
    3 ≤ Module.finrank (ZMod 3) (qTwoBarU B Bs L D J x ι) ∧
      (Module.finrank (ZMod 3) (qTwoBarU B Bs L D J x ι) = m ∨
        Module.finrank (ZMod 3) (qTwoBarU B Bs L D J x ι) + 1 = m) := by
  classical
  haveI : Finite V := by
    haveI : Finite ↥Bs := Subtype.finite
    exact Finite.of_injective (ι.symm : V → Additive ↥Bs) ι.symm.injective
  have hVcard : Nat.card V = 3 ^ m := by
    have h1 : Nat.card V = Nat.card ↥Bs := Nat.card_congr ι.toEquiv.symm
    rw [h1, hLM.card]
  have hVdim : Module.finrank (ZMod 3) V = m := by
    have h2 : Nat.card V = 3 ^ Module.finrank (ZMod 3) V := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V), Nat.card_zmod]
    exact (Nat.pow_right_injective (Fact.out : Nat.Prime 3).two_le (hVcard.symm.trans h2)).symm
  let AL : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs
  let AInf : Subgroup (MulAut ↥Bs) := ggAInf 3 B Bs x L D J
  have hAL_le : AL ≤ AInf := by
    unfold AL AInf ggAInf
    exact le_sup_left
  have hAL_map_le : AL.map (ggLin (p := 3) ι) ≤ AInf.map (ggLin (p := 3) ι) := by
    intro a ha
    rw [Subgroup.mem_map] at ha ⊢
    obtain ⟨a', ha', rfl⟩ := ha
    exact ⟨a', hAL_le ha', rfl⟩
  have hUL_le : ggLinCom ((AL.map (ggLin (p := 3) ι)) : Set (V ≃ₗ[ZMod 3] V)) ≤
      qTwoBarU B Bs L D J x ι := by
    unfold qTwoBarU qTwoBarA
    exact qTwoGBB_ggLinCom_mono hAL_map_le
  have hbridge_L : Nat.card (ggCommSpace Bs AL) =
      3 ^ Module.finrank (ZMod 3) (ggLinCom ((AL.map (ggLin (p := 3) ι)) : Set (V ≃ₗ[ZMod 3] V))) :=
    qTwoGBB_bridge_card Bs AL ι
  have hULdim : Module.finrank (ZMod 3) (ggLinCom ((AL.map (ggLin (p := 3) ι)) : Set (V ≃ₗ[ZMod 3] V))) = m - 1 := by
    have h := hbridge_L
    simp only [AL] at h
    rw [hLM.comm] at h
    exact (Nat.pow_right_injective (Fact.out : Nat.Prime 3).two_le h).symm
  have hd_ge : m - 1 ≤ Module.finrank (ZMod 3) (qTwoBarU B Bs L D J x ι) := by
    rw [← hULdim]
    exact Submodule.finrank_mono hUL_le
  have hd_le : Module.finrank (ZMod 3) (qTwoBarU B Bs L D J x ι) ≤ m := by
    have hle : Module.finrank (ZMod 3) (qTwoBarU B Bs L D J x ι) ≤ Module.finrank (ZMod 3) V :=
      Submodule.finrank_le _
    omega
  constructor
  · omega
  · omega

end CFSG.StandardType.QTwo

end
