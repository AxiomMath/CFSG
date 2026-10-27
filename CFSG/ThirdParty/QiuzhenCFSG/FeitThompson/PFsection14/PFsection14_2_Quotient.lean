module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection14.PFsection14_2_SourceData

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 14: (14.2) quotient and transport infrastructure
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section14

universe u v w

public theorem section14_subgroupOf_eq_bot_of_eq_bot
    {G : Type u} [Group G] {C U : Subgroup G}
    (hCbot : C = ⊥) :
    C.subgroupOf U = ⊥ := by
  ext x
  constructor
  · intro hx
    have hxC : (x : G) ∈ C := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
      simpa [hCbot] using hxC
    exact Subtype.ext (by simpa using hxbot)
  · intro hx
    have hxone : x = 1 := by simpa using hx
    rw [hxone]
    exact Subgroup.one_mem (C.subgroupOf U)

public theorem section14_quotient_bot_equiv_apply_eq_out
    {A : Type u} [Group A] {N : Subgroup A} [N.Normal]
    (hN : N = ⊥) (x : A ⧸ N) :
    ((QuotientGroup.quotientMulEquivOfEq hN).trans
      (QuotientGroup.quotientBot (G := A))) x = Quotient.out x := by
  let e : A ⧸ N ≃* A :=
    (QuotientGroup.quotientMulEquivOfEq hN).trans
      (QuotientGroup.quotientBot (G := A))
  have hmk_e : (QuotientGroup.mk' N) (e x) = x := by
    have hsymm (a : A) : e.symm a = (QuotientGroup.mk' N) a := by
      change (QuotientGroup.quotientMulEquivOfEq hN).symm
          (QuotientGroup.quotientBot.symm a) = _
      rw [QuotientGroup.quotientBot_symm_apply]
      exact QuotientGroup.quotientMulEquivOfEq_mk hN.symm a
    calc
      (QuotientGroup.mk' N) (e x) = e.symm (e x) := by rw [hsymm]
      _ = x := e.left_inv x
  have hmk_out : (QuotientGroup.mk' N) (Quotient.out x) = x := by
    rw [QuotientGroup.coe_mk']
    exact Quotient.out_eq' x
  have hmk_eq : (QuotientGroup.mk' N) (e x) =
      (QuotientGroup.mk' N) (Quotient.out x) := hmk_e.trans hmk_out.symm
  rw [QuotientGroup.mk'_eq_mk'] at hmk_eq
  rcases hmk_eq with ⟨z, hzN, hz⟩
  have hz1 : z = 1 := by
    have hzbot : z ∈ (⊥ : Subgroup A) := by
      simpa [hN] using hzN
    simpa using hzbot
  simpa [e, hz1] using hz

public theorem section14_quotient_bot_equiv_mk'_apply
    {A : Type u} [Group A] {N : Subgroup A} [N.Normal]
    (hN : N = ⊥) (x : A ⧸ N) :
  (QuotientGroup.mk' N)
      (((QuotientGroup.quotientMulEquivOfEq hN).trans
        (QuotientGroup.quotientBot (G := A))) x) = x := by
  rw [section14_quotient_bot_equiv_apply_eq_out hN x]
  rw [QuotientGroup.coe_mk']
  exact Quotient.out_eq' x

public theorem section14_quotient_bot_equiv_mk'_apply_eq
    {A : Type u} [Group A] {N : Subgroup A} [N.Normal]
    (hN : N = ⊥) (x : A) :
    ((QuotientGroup.quotientMulEquivOfEq hN).trans
      (QuotientGroup.quotientBot (G := A))) ((QuotientGroup.mk' N) x) = x := by
  let e : A ⧸ N ≃* A :=
    (QuotientGroup.quotientMulEquivOfEq hN).trans
      (QuotientGroup.quotientBot (G := A))
  have hmk :
      (QuotientGroup.mk' N) (e ((QuotientGroup.mk' N) x)) =
        (QuotientGroup.mk' N) x := by
    exact section14_quotient_bot_equiv_mk'_apply hN ((QuotientGroup.mk' N) x)
  rw [QuotientGroup.mk'_eq_mk'] at hmk
  rcases hmk with ⟨z, hzN, hz⟩
  have hz1 : z = 1 := by
    have hzbot : z ∈ (⊥ : Subgroup A) := by
      simpa [hN] using hzN
    simpa using hzbot
  simpa [e, hz1] using hz

public theorem section14_quotient_bot_equiv_map_mk'_subgroup_eq
    {A : Type u} [Group A] {N : Subgroup A} [N.Normal]
    (hN : N = ⊥) (L : Subgroup A) :
    Subgroup.map (((QuotientGroup.quotientMulEquivOfEq hN).trans
        (QuotientGroup.quotientBot (G := A))).toMonoidHom)
      (Subgroup.map (QuotientGroup.mk' N) L) = L := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy, hxy⟩
    rcases hy with ⟨z, hz, rfl⟩
    have hxz : x = z := by
      simpa using hxy.symm.trans
        (section14_quotient_bot_equiv_mk'_apply_eq hN z)
    simpa [hxz] using hz
  · intro hx
    refine ⟨QuotientGroup.mk' N x, ⟨x, hx, rfl⟩, ?_⟩
    exact section14_quotient_bot_equiv_mk'_apply_eq hN x

public theorem section14_map_trans_equiv
    {A : Type u} {B : Type v} {C : Type w}
    [Group A] [Group B] [Group C]
    (e₁ : A ≃* B) (e₂ : B ≃* C) (L : Subgroup A) :
    Subgroup.map (e₁.trans e₂).toMonoidHom L =
      Subgroup.map e₂.toMonoidHom (Subgroup.map e₁.toMonoidHom L) := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨x, hx, rfl⟩
    exact ⟨e₁ x, ⟨x, hx, rfl⟩, rfl⟩
  · intro hz
    rcases hz with ⟨y, hy, rfl⟩
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

public theorem section14_map_symm_map_equiv
    {A : Type u} {B : Type v} [Group A] [Group B]
    (e : A ≃* B) (L : Subgroup A) :
    Subgroup.map e.symm.toMonoidHom (Subgroup.map e.toMonoidHom L) = L := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy, hxy⟩
    rcases hy with ⟨z, hz, rfl⟩
    have hxz : x = z := by simpa using hxy.symm
    simpa [hxz] using hz
  · intro hx
    refine ⟨e x, ⟨x, hx, rfl⟩, ?_⟩
    simp

public theorem section14_isFrobeniusGroupWithKernelComplement_map_mulEquiv
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (e : A ≃* B) {K R : Subgroup A}
    (hFrob : IsFrobeniusGroupWithKernelComplement K R) :
    IsFrobeniusGroupWithKernelComplement
      (K.map e.toMonoidHom) (R.map e.toMonoidHom) := by
  classical
  rcases hFrob with ⟨hKnorm, hComp, hDisj, hKne, hRne⟩
  have hKmap_ne : K.map e.toMonoidHom ≠ ⊥ := by
    intro hbot
    exact hKne
      ((Subgroup.map_eq_bot_iff_of_injective
        (H := K) (f := e.toMonoidHom) e.injective).1 hbot)
  have hRmap_ne : R.map e.toMonoidHom ≠ ⊥ := by
    intro hbot
    exact hRne
      ((Subgroup.map_eq_bot_iff_of_injective
        (H := R) (f := e.toMonoidHom) e.injective).1 hbot)
  have hKmap_norm : (K.map e.toMonoidHom).Normal :=
    hKnorm.map e.toMonoidHom e.surjective
  have hCompMap :
      (K.map e.toMonoidHom).IsComplement' (R.map e.toMonoidHom) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxK hxR
      rcases Subgroup.mem_map.mp hxK with ⟨k, hkK, hkx⟩
      rcases Subgroup.mem_map.mp hxR with ⟨r, hrR, hrx⟩
      have hkr : k = r := e.injective (hkx.trans hrx.symm)
      have hkbot : k ∈ (⊥ : Subgroup A) :=
        hComp.disjoint.le_bot ⟨hkK, by simpa [hkr] using hrR⟩
      have hxone : x = 1 := by
        rw [← hkx]
        simpa using congrArg e hkbot
      simp [hxone]
    · rw [Set.eq_univ_iff_forall]
      intro b
      let a : A := e.symm b
      rcases hComp.2 a with ⟨kr, hkr⟩
      rcases kr with ⟨k, r⟩
      rcases k with ⟨k, hkK⟩
      rcases r with ⟨r, hrR⟩
      refine ⟨e k, Subgroup.mem_map.mpr ⟨k, hkK, rfl⟩,
        e r, Subgroup.mem_map.mpr ⟨r, hrR, rfl⟩, ?_⟩
      calc
        e k * e r = e (k * r) := (e.map_mul k r).symm
        _ = e a := by
          have hkrA : k * r = a := by
            simpa using hkr
          rw [hkrA]
        _ = b := e.apply_symm_apply b
  refine (lemma_3_1 (K.map e.toMonoidHom) (R.map e.toMonoidHom)
    hKmap_ne hRmap_ne hKmap_norm hCompMap).mpr ?_
  intro x hxne
  rcases x.property with ⟨r, hrR, hrx⟩
  let rSub : R := ⟨r, hrR⟩
  have hrne : rSub ≠ 1 := by
    intro hrone
    apply hxne
    apply Subtype.ext
    rw [← hrx]
    have hrA : r = 1 := by
      exact congrArg (fun x : R => (x : A)) hrone
    simp [hrA]
  have hcentral :=
    (lemma_3_1 K R hKne hRne hKnorm hComp).mp
      ⟨hKnorm, hComp, hDisj, hKne, hRne⟩ rSub hrne
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  rcases hy with ⟨hyK, hyCent⟩
  rcases Subgroup.mem_map.mp hyK with ⟨k, hkK, hky⟩
  have hkCent : k ∈ elementCentralizerIn K (r : A) := by
    refine ⟨hkK, ?_⟩
    change k ∈ Subgroup.centralizer ({r} : Set A)
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    have hcommB : y * (x : B) = (x : B) * y :=
      Subgroup.mem_centralizer_singleton_iff.mp hyCent
    rw [← hky, ← hrx] at hcommB
    simpa using hcommB
  have hkbot : k ∈ (⊥ : Subgroup A) := by
    rw [← hcentral]
    exact hkCent
  have hkone : k = 1 := by
    simpa using hkbot
  rw [← hky, hkone]
  simp

@[expose] public noncomputable def section14_addEquivToMulEquivMultiplicative
    (A : Type u) (F : Type v) [Group A] [AddGroup F]
    (e : Additive A ≃+ F) : A ≃* Multiplicative F :=
  { toFun := fun x => Multiplicative.ofAdd (e (Additive.ofMul x))
    invFun := fun y => Additive.toMul (e.symm (Multiplicative.toAdd y))
    left_inv := by
      intro x
      change Additive.toMul (e.symm (e (Additive.ofMul x))) = x
      simp
    right_inv := by
      intro y
      change Multiplicative.ofAdd (e (e.symm (Multiplicative.toAdd y))) = y
      simp
    map_mul' := by
      intro x y
      simp }

public theorem section14_algebraMap_zmod_intCast
    {F : Type u} [Ring F] {p : ℕ} [CharP F p] [Algebra (ZMod p) F]
    (n : ℤ) :
    algebraMap (ZMod p) F (n : ZMod p) = (n : F) := by
  have hF : (algebraMap (ZMod p) F) = ZMod.castHom (dvd_refl p) F := by
    exact RingHom.ext_zmod _ _
  rw [hF]
  simp

public theorem section14_ringEquiv_symm_algebraMap_zmod
    {F : Type u} {E : Type v} [Field F] [Field E] {p : ℕ}
    [CharP F p] [CharP E p]
    [Algebra (ZMod p) F] [Algebra (ZMod p) E]
    (e : F ≃+* E) (x : ZMod p) :
    e.symm (algebraMap (ZMod p) E x) = algebraMap (ZMod p) F x := by
  have hE : (algebraMap (ZMod p) E) = ZMod.castHom (dvd_refl p) E := by
    exact RingHom.ext_zmod _ _
  have hF : (algebraMap (ZMod p) F) = ZMod.castHom (dvd_refl p) F := by
    exact RingHom.ext_zmod _ _
  rw [hE, hF]
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
  simp

public theorem section14_appendixCP0InP_map_ePfield_eq_zpowers
    {F : Type u} [Field F] {p q : ℕ} [Fact p.Prime]
    [CharP F p] [Algebra (ZMod p) F]
    (eF : F ≃+* appendixCField p q) :
    Subgroup.map
        (section14_addEquivToMulEquivMultiplicative (appendixCP p q) F
          eF.symm.toAddEquiv).toMonoidHom
        (appendixCP0InP p q) =
      Subgroup.zpowers (Multiplicative.ofAdd (1 : F)) := by
  let ePfield : appendixCP p q ≃* Multiplicative F :=
    section14_addEquivToMulEquivMultiplicative (appendixCP p q) F
      eF.symm.toAddEquiv
  change Subgroup.map ePfield.toMonoidHom (appendixCP0InP p q) = _
  ext y
  constructor
  · intro hy
    rcases hy with ⟨x, hx, rfl⟩
    rcases (appendixCP0InP_mem_iff (p := p) (q := q) x).1 hx with
      ⟨c, rfl⟩
    have hc :
        eF.symm (algebraMap (ZMod p) (appendixCField p q) c) =
          algebraMap (ZMod p) F c :=
      section14_ringEquiv_symm_algebraMap_zmod eF c
    change Multiplicative.ofAdd
        (eF.symm (algebraMap (ZMod p) (appendixCField p q) c)) ∈
      Subgroup.zpowers (Multiplicative.ofAdd (1 : F))
    rw [hc]
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective c
    rw [section14_algebraMap_zmod_intCast (F := F) (p := p) n]
    convert Subgroup.zpow_mem_zpowers (Multiplicative.ofAdd (1 : F)) n using 1
    rw [← ofAdd_zsmul]
    simp only [zsmul_one]
  · intro hy
    rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
    refine ⟨Multiplicative.ofAdd
      (algebraMap (ZMod p) (appendixCField p q) (n : ZMod p)), ?_, ?_⟩
    · exact (appendixCP0InP_mem_iff (p := p) (q := q) _).2
        ⟨(n : ZMod p), rfl⟩
    · have hc :
          eF.symm
            (algebraMap (ZMod p) (appendixCField p q) (n : ZMod p)) =
            algebraMap (ZMod p) F (n : ZMod p) :=
        section14_ringEquiv_symm_algebraMap_zmod eF (n : ZMod p)
      change Multiplicative.ofAdd
          (eF.symm
            (algebraMap (ZMod p) (appendixCField p q) (n : ZMod p))) =
        (Multiplicative.ofAdd (1 : F)) ^ n
      rw [hc]
      rw [section14_algebraMap_zmod_intCast (F := F) (p := p) n]
      rw [← ofAdd_zsmul]
      simp only [zsmul_one]

@[expose] public noncomputable def section14_subgroupMapMulEquivOfInjective
    {A : Type u} {B : Type v} [Group A] [Group B]
    (K : Subgroup A) (f : A →* B) (hf : Function.Injective f) :
    K ≃* K.map f :=
  { toFun := fun x => ⟨f x, ⟨x, x.property, rfl⟩⟩
    invFun := fun y =>
      let x : A := Classical.choose y.property
      ⟨x, (Classical.choose_spec y.property).1⟩
    left_inv := by
      intro x
      apply Subtype.ext
      dsimp
      apply hf
      exact (Classical.choose_spec
        ((⟨f x, ⟨x, x.property, rfl⟩⟩ : K.map f).property)).2
    right_inv := by
      intro y
      apply Subtype.ext
      dsimp
      exact (Classical.choose_spec y.property).2
    map_mul' := by
      intro x y
      apply Subtype.ext
      simp }

@[expose] public noncomputable def section14_subgroupCongr
    {A : Type u} [Group A] {K L : Subgroup A} (h : K = L) :
    K ≃* L :=
  { toFun := fun x => ⟨x, by simpa [h] using x.property⟩
    invFun := fun x => ⟨x, by simp [h]⟩
    left_inv := by
      intro x
      rfl
    right_inv := by
      intro x
      rfl
    map_mul' := by
      intro x y
      rfl }

@[expose] public noncomputable def section14_invMulEquivOfComm
    (A : Type u) [CommGroup A] : A ≃* A :=
  { toFun := fun x => x⁻¹
    invFun := fun x => x⁻¹
    left_inv := by
      intro x
      simp
    right_inv := by
      intro x
      simp
    map_mul' := by
      intro x y
      simp [mul_comm] }

public theorem section14_map_subtype_comp_equiv_top
    {G : Type u} [Group G] {A : Type v} [Group A]
    (P : Subgroup G) (e : A ≃* P) :
    Subgroup.map (P.subtype.comp e.toMonoidHom) (⊤ : Subgroup A) = P := by
  ext g
  constructor
  · intro hg
    rcases hg with ⟨a, _ha, rfl⟩
    exact (e a).property
  · intro hg
    rcases e.surjective ⟨g, hg⟩ with ⟨a, ha⟩
    refine ⟨a, trivial, ?_⟩
    exact congrArg (fun x : P => (x : G)) ha

public theorem section14_map_subtype_comp_equiv_eq_of_subgroupOf_eq
    {G : Type u} [Group G] {A : Type v} [Group A]
    {P K : Subgroup G} (hK : K ≤ P) (e : A ≃* P) {L : Subgroup A}
    (h : Subgroup.map e.toMonoidHom L = K.subgroupOf P) :
    Subgroup.map (P.subtype.comp e.toMonoidHom) L = K := by
  ext g
  constructor
  · intro hg
    rcases hg with ⟨x, hx, rfl⟩
    have hxMap : e x ∈ Subgroup.map e.toMonoidHom L := ⟨x, hx, rfl⟩
    rw [h] at hxMap
    exact hxMap
  · intro hg
    have hxP : (⟨g, hK hg⟩ : P) ∈ K.subgroupOf P := by
      simpa [Subgroup.mem_subgroupOf] using hg
    rw [← h] at hxP
    rcases hxP with ⟨x, hx, hxeq⟩
    refine ⟨x, hx, ?_⟩
    exact congrArg (fun y : P => (y : G)) hxeq

public theorem section14_appendixCP0InP_map_ePmodel_eq_subgroupOf
    {G : Type u} [Group G] {F : Type v} [Field F]
    {P W2 : Subgroup G} {p q : ℕ} [Fact p.Prime]
    [CharP F p] [Algebra (ZMod p) F]
    [((⊥ : Subgroup G).subgroupOf P).Normal]
    (eF : F ≃+* appendixCField p q)
    (φH : P ⧸ (⊥ : Subgroup G).subgroupOf P ≃* Multiplicative F)
    (hbotSubP : (⊥ : Subgroup G).subgroupOf P = ⊥)
    (hW2 : W2 ≤ P ∧
      Subgroup.map φH.toMonoidHom
        (Subgroup.map (QuotientGroup.mk' ((⊥ : Subgroup G).subgroupOf P))
          (W2.subgroupOf P)) =
      Subgroup.zpowers (Multiplicative.ofAdd (1 : F))) :
    let ePquot : P ⧸ (⊥ : Subgroup G).subgroupOf P ≃* P :=
      (QuotientGroup.quotientMulEquivOfEq hbotSubP).trans
        (QuotientGroup.quotientBot (G := P))
    let ePfield : appendixCP p q ≃* Multiplicative F :=
      section14_addEquivToMulEquivMultiplicative (appendixCP p q) F
        eF.symm.toAddEquiv
    let ePmodel : appendixCP p q ≃* P :=
      (ePfield.trans φH.symm).trans ePquot
    Subgroup.map ePmodel.toMonoidHom (appendixCP0InP p q) =
      W2.subgroupOf P := by
  intro ePquot ePfield ePmodel
  have hP0field :
      Subgroup.map ePfield.toMonoidHom (appendixCP0InP p q) =
        Subgroup.zpowers (Multiplicative.ofAdd (1 : F)) := by
    simpa [ePfield] using
      section14_appendixCP0InP_map_ePfield_eq_zpowers
        (F := F) (p := p) (q := q) eF
  have hφ :
      Subgroup.map φH.symm.toMonoidHom
          (Subgroup.map ePfield.toMonoidHom (appendixCP0InP p q)) =
        Subgroup.map (QuotientGroup.mk' ((⊥ : Subgroup G).subgroupOf P))
          (W2.subgroupOf P) := by
    calc
      Subgroup.map φH.symm.toMonoidHom
          (Subgroup.map ePfield.toMonoidHom (appendixCP0InP p q)) =
          Subgroup.map φH.symm.toMonoidHom
            (Subgroup.zpowers (Multiplicative.ofAdd (1 : F))) := by
        rw [hP0field]
      _ = Subgroup.map φH.symm.toMonoidHom
            (Subgroup.map φH.toMonoidHom
              (Subgroup.map (QuotientGroup.mk' ((⊥ : Subgroup G).subgroupOf P))
                (W2.subgroupOf P))) := by
        rw [← hW2.2]
      _ = Subgroup.map (QuotientGroup.mk' ((⊥ : Subgroup G).subgroupOf P))
              (W2.subgroupOf P) :=
        section14_map_symm_map_equiv φH _
  calc
    Subgroup.map ePmodel.toMonoidHom (appendixCP0InP p q) =
        Subgroup.map ePquot.toMonoidHom
          (Subgroup.map (ePfield.trans φH.symm).toMonoidHom
            (appendixCP0InP p q)) := by
      simpa [ePmodel] using
        section14_map_trans_equiv (ePfield.trans φH.symm) ePquot
          (appendixCP0InP p q)
    _ = Subgroup.map ePquot.toMonoidHom
          (Subgroup.map φH.symm.toMonoidHom
            (Subgroup.map ePfield.toMonoidHom (appendixCP0InP p q))) := by
      rw [section14_map_trans_equiv ePfield φH.symm (appendixCP0InP p q)]
    _ = Subgroup.map ePquot.toMonoidHom
          (Subgroup.map (QuotientGroup.mk' ((⊥ : Subgroup G).subgroupOf P))
            (W2.subgroupOf P)) := by
      rw [hφ]
    _ = W2.subgroupOf P := by
      simpa [ePquot] using
        section14_quotient_bot_equiv_map_mk'_subgroup_eq
          (A := P) (N := ((⊥ : Subgroup G).subgroupOf P)) hbotSubP
          (W2.subgroupOf P)

public theorem section14_semidirect_lift_map_inl_range
    {N : Type u} {K : Type v} {H : Type w}
    [Group N] [Group K] [Group H] {φ : K →* MulAut N}
    (fn : N →* H) (fg : K →* H)
    (h : ∀ g : K,
      fn.comp (MulEquiv.toMonoidHom (φ g)) =
        (MulEquiv.toMonoidHom (MulAut.conj (fg g))).comp fn) :
    Subgroup.map (SemidirectProduct.lift fn fg h)
        (MonoidHom.range (SemidirectProduct.inl : N →* N ⋊[φ] K)) =
      Subgroup.map fn (⊤ : Subgroup N) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨s, hs, rfl⟩
    rcases hs with ⟨n, rfl⟩
    refine ⟨n, trivial, ?_⟩
    rw [SemidirectProduct.lift_inl]
  · intro hx
    rcases hx with ⟨n, _hn, rfl⟩
    refine ⟨SemidirectProduct.inl n, ?_, ?_⟩
    · exact ⟨n, rfl⟩
    · rw [SemidirectProduct.lift_inl]

public theorem section14_semidirect_lift_map_inl_subgroup
    {N : Type u} {K : Type v} {H : Type w}
    [Group N] [Group K] [Group H] {φ : K →* MulAut N}
    (fn : N →* H) (fg : K →* H)
    (h : ∀ g : K,
      fn.comp (MulEquiv.toMonoidHom (φ g)) =
        (MulEquiv.toMonoidHom (MulAut.conj (fg g))).comp fn)
    (L : Subgroup N) :
    Subgroup.map (SemidirectProduct.lift fn fg h)
        (Subgroup.map (SemidirectProduct.inl : N →* N ⋊[φ] K) L) =
      Subgroup.map fn L := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨s, hs, rfl⟩
    rcases hs with ⟨n, hn, rfl⟩
    refine ⟨n, hn, ?_⟩
    rw [SemidirectProduct.lift_inl]
  · intro hx
    rcases hx with ⟨n, hn, rfl⟩
    refine ⟨SemidirectProduct.inl n, ?_, ?_⟩
    · exact ⟨n, hn, rfl⟩
    · rw [SemidirectProduct.lift_inl]

public theorem section14_semidirect_lift_map_inr_range
    {N : Type u} {K : Type v} {H : Type w}
    [Group N] [Group K] [Group H] {φ : K →* MulAut N}
    (fn : N →* H) (fg : K →* H)
    (h : ∀ g : K,
      fn.comp (MulEquiv.toMonoidHom (φ g)) =
        (MulEquiv.toMonoidHom (MulAut.conj (fg g))).comp fn) :
    Subgroup.map (SemidirectProduct.lift fn fg h)
        (MonoidHom.range (SemidirectProduct.inr : K →* N ⋊[φ] K)) =
      Subgroup.map fg (⊤ : Subgroup K) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨s, hs, rfl⟩
    rcases hs with ⟨g, rfl⟩
    refine ⟨g, trivial, ?_⟩
    rw [SemidirectProduct.lift_inr]
  · intro hx
    rcases hx with ⟨g, _hg, rfl⟩
    refine ⟨SemidirectProduct.inr g, ?_, ?_⟩
    · exact ⟨g, rfl⟩
    · rw [SemidirectProduct.lift_inr]

public theorem section14_semidirect_lift_injective_of_disjoint_images
    {N : Type u} {K : Type v} {G : Type w}
    [Group N] [Group K] [Group G] {φ : K →* MulAut N}
    {P U : Subgroup G} (eN : N ≃* P) (eK : K ≃* U)
    (hdisj : Disjoint P U)
    (h : ∀ g : K,
      (P.subtype.comp eN.toMonoidHom).comp (MulEquiv.toMonoidHom (φ g)) =
        (MulEquiv.toMonoidHom (MulAut.conj ((U.subtype.comp eK.toMonoidHom) g))).comp
          (P.subtype.comp eN.toMonoidHom)) :
    Function.Injective
      (SemidirectProduct.lift (P.subtype.comp eN.toMonoidHom)
        (U.subtype.comp eK.toMonoidHom) h) := by
  let fn : N →* G := P.subtype.comp eN.toMonoidHom
  let fg : K →* G := U.subtype.comp eK.toMonoidHom
  let σ : N ⋊[φ] K →* G := SemidirectProduct.lift fn fg h
  have hker : ∀ z, σ z = 1 → z = 1 := by
    intro z hz
    have hmul : fn z.left * fg z.right = 1 := by
      simpa [σ, fn, fg, SemidirectProduct.lift] using hz
    have hleft_eq : fn z.left = (fg z.right)⁻¹ := by
      have h := congrArg (fun t : G => t * (fg z.right)⁻¹) hmul
      simpa [mul_assoc] using h
    have hleftP : fn z.left ∈ P := (eN z.left).property
    have hrightU : fg z.right ∈ U := (eK z.right).property
    have hleftU : fn z.left ∈ U := by
      rw [hleft_eq]
      exact U.inv_mem hrightU
    have hleftInf : fn z.left ∈ P ⊓ U := ⟨hleftP, hleftU⟩
    have hleftBot : fn z.left ∈ (⊥ : Subgroup G) := by
      rw [disjoint_iff] at hdisj
      simpa [hdisj] using hleftInf
    have hfn1 : fn z.left = 1 := by simpa using hleftBot
    have hfg1 : fg z.right = 1 := by
      simpa [hfn1] using hmul
    have hzleft : z.left = 1 := by
      apply eN.injective
      apply Subtype.ext
      simpa [fn] using hfn1
    have hzright : z.right = 1 := by
      apply eK.injective
      apply Subtype.ext
      simpa [fg] using hfg1
    ext <;> simp [hzleft, hzright]
  intro x y hxy
  change σ x = σ y at hxy
  have hxyker : σ (x⁻¹ * y) = 1 := by
    rw [map_mul, map_inv, hxy, inv_mul_cancel]
  have hxyone : x⁻¹ * y = 1 := hker (x⁻¹ * y) hxyker
  exact inv_mul_eq_one.mp hxyone

public theorem section14_finiteField_ringEquiv_appendixC
    {F : Type u} [Field F] [Fintype F]
    {p q : ℕ} (hp : Nat.Prime p)
    (hFcard : Nat.card F = p ^ q) :
    letI : Fact p.Prime := ⟨hp⟩
    Nonempty (F ≃+* appendixCField p q) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hFcard' : Fintype.card F = p ^ q := by
    simpa [Nat.card_eq_fintype_card] using hFcard
  haveI : CharP F p := charP_of_card_eq_prime_pow (R := F) hFcard'
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  let e : F ≃ₐ[ZMod p] GaloisField p q :=
    GaloisField.algEquivGaloisFieldOfFintype (K := F) (p := p) (n := q) hFcard'
  exact ⟨e.toRingEquiv⟩

public theorem section14_subgroup_pow_natCard_eq_one
    {A : Type u} [Group A] {L : Subgroup A} {y : A} (hyL : y ∈ L) :
    y ^ Nat.card L = 1 := by
  have hyPowL : (⟨y, hyL⟩ : L) ^ Nat.card L = 1 := pow_card_eq_one'
  rw [← L.coe_pow (⟨y, hyL⟩ : L) (Nat.card L)]
  change ((↑((⟨y, hyL⟩ : L) ^ Nat.card L) : A) = (↑(1 : L) : A))
  exact congrArg (fun z : L => (z : A)) hyPowL

public theorem section14_cyclic_subgroup_le_of_natCard_eq
    {A : Type u} [Group A] [Finite A] [IsCyclic A]
    {K L : Subgroup A}
    (hcard : Nat.card K = Nat.card L) :
    K ≤ L := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  intro x hxK
  let n : ℕ := Nat.card L
  have hnpos : 0 < n := Nat.card_pos
  let S : Finset A := Finset.univ.filter (fun a : A => a ^ n = 1)
  let T : Finset A := Finset.univ.image (fun y : L => (y : A))
  have hTcard : T.card = n := by
    rw [show T = Finset.univ.image (fun y : L => (y : A)) from rfl]
    rw [Finset.card_image_of_injective]
    · simp [n, Nat.card_eq_fintype_card]
    · intro a b h
      exact Subtype.ext h
  have hTsubS : T ⊆ S := by
    intro y hy
    have hyL : y ∈ L := by simpa [T] using hy
    have hyPowA : y ^ n = 1 := by
      simpa [n] using section14_subgroup_pow_natCard_eq_one (L := L) hyL
    simp [S, hyPowA]
  have hScard_le : S.card ≤ n := by
    simpa [S] using (IsCyclic.card_pow_eq_one_le (α := A) (n := n) hnpos)
  have hxpow : x ^ n = 1 := by
    have hxPowA : x ^ Nat.card K = 1 :=
      section14_subgroup_pow_natCard_eq_one (L := K) hxK
    have hxPowL : x ^ Nat.card L = 1 := by
      rw [← hcard]
      exact hxPowA
    simpa [n] using hxPowL
  by_contra hxnotL
  have hxS : x ∈ S := by simp [S, hxpow]
  have hxnotT : x ∉ T := by
    intro hxT
    have hxL : x ∈ L := by simpa [T] using hxT
    exact hxnotL hxL
  have hInsSub : insert x T ⊆ S := by
    intro y hy
    rw [Finset.mem_insert] at hy
    rcases hy with rfl | hyT
    · exact hxS
    · exact hTsubS hyT
  have hcardIns : (insert x T).card = n + 1 := by
    rw [Finset.card_insert_of_notMem hxnotT, hTcard]
  have : n + 1 ≤ n := by
    calc
      n + 1 = (insert x T).card := hcardIns.symm
      _ ≤ S.card := Finset.card_le_card hInsSub
      _ ≤ n := hScard_le
  omega

public theorem section14_cyclic_subgroup_eq_of_natCard_eq
    {A : Type u} [Group A] [Finite A] [IsCyclic A]
    {K L : Subgroup A}
    (hcard : Nat.card K = Nat.card L) :
    K = L := by
  exact le_antisymm
    (section14_cyclic_subgroup_le_of_natCard_eq hcard)
    (section14_cyclic_subgroup_le_of_natCard_eq hcard.symm)
end CFSG.Section14
