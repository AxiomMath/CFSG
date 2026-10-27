module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma6_2
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma7_2
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonExceptionalF9SL3
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.QdSLPCore
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
import Mathlib.LinearAlgebra.Pi

namespace CFSG
end CFSG
open CFSG

/-!
# Glauberman Lemma 6.3, Step 6: the aligned prime-field model

For a minimal non-`p`-stable group, Lemma 6.2 first realizes the faithful
irreducible quotient action over a finite extension field `K`.  Minimality
forces the embedded prime-field `SL₂(p)` to fill the quotient, hence `K =
GF(p)`.  The order-nine exceptional branch is eliminated by its aligned
24-element subgroup.  The result retains the original representation and
returns a compatible equivalence with `qdSL p`, as required by Step 7.
-/

noncomputable section

namespace CFSG.Glauberman

universe u

open scoped commutatorElement IsMulCommutative

private theorem normal_ambient_quotient_core_membership_iff_local
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (H : Subgroup Q) (hHnormal : H.Normal)
    (x : Q) (hx : x ∈ Subgroup.normalizer (H : Set Q)) :
    QuotientGroup.mk'
          ((Subgroup.centralizer (H : Set Q)).subgroupOf
            (Subgroup.normalizer (H : Set Q))) ⟨x, hx⟩ ∈
        pCore p ((Subgroup.normalizer (H : Set Q)) ⧸
          (Subgroup.centralizer (H : Set Q)).subgroupOf
            (Subgroup.normalizer (H : Set Q))) ↔
      QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) x ∈
        pCore p (Q ⧸ Subgroup.centralizer (H : Set Q)) := by
  classical
  let N : Subgroup Q := Subgroup.normalizer (H : Set Q)
  let C : Subgroup Q := Subgroup.centralizer (H : Set Q)
  have hNtop : N = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hHnormal
  let eN : N ≃* Q :=
    (MulEquiv.subgroupCongr hNtop).trans
      (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q)
  have hCmap : (C.subgroupOf N).map eN.toMonoidHom = C := by
    ext z
    constructor
    · rintro ⟨n, hn, rfl⟩
      have hnC : ((n : N) : Q) ∈ C := Subgroup.mem_subgroupOf.mp hn
      simpa [eN, MulEquiv.subgroupCongr_apply] using hnC
    · intro hz
      have hzN : z ∈ N := by rw [hNtop]; simp
      let n : N := ⟨z, hzN⟩
      refine ⟨n, Subgroup.mem_subgroupOf.mpr hz, ?_⟩
      simp [eN, n, MulEquiv.subgroupCongr_apply]
  let e : N ⧸ C.subgroupOf N ≃* Q ⧸ C :=
    QuotientGroup.congr
      (G := N) (H := Q) (G' := C.subgroupOf N) (H' := C) eN hCmap
  have he_mk :
      e (QuotientGroup.mk' (C.subgroupOf N) ⟨x, hx⟩) =
        QuotientGroup.mk' C x := by
    rfl
  have hcoreMap : (pCore p (N ⧸ C.subgroupOf N)).map e.toMonoidHom =
      pCore p (Q ⧸ C) :=
    pCore_map_iso (G := N ⧸ C.subgroupOf N) (G' := Q ⧸ C) (p := p) e
  constructor
  · intro hlocal
    have hmap : e (QuotientGroup.mk' (C.subgroupOf N) ⟨x, hx⟩) ∈
        (pCore p (N ⧸ C.subgroupOf N)).map e.toMonoidHom :=
      Subgroup.mem_map_of_mem e.toMonoidHom hlocal
    rw [hcoreMap, he_mk] at hmap
    simpa [N, C] using hmap
  · intro hambient
    have hambient' : QuotientGroup.mk' C x ∈ pCore p (Q ⧸ C) := by
      simpa [C] using hambient
    rw [← hcoreMap] at hambient'
    rcases Subgroup.mem_map.mp hambient' with ⟨z, hz, hzeq⟩
    have hzorig : z = QuotientGroup.mk' (C.subgroupOf N) ⟨x, hx⟩ := by
      apply e.injective
      exact hzeq.trans he_mk.symm
    simpa [N, C, hzorig] using hz

private theorem quotient_subgroup_eq_top_of_quadratic
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (hminSub : ∀ A : Subgroup Q,
      Nat.card A < Nat.card Q → pStable p A)
    (H : Subgroup Q) (hHnormal : H.Normal) (hHne : H ≠ ⊥)
    (hHp : IsPGroup p H) (hHcomm : IsMulCommutative H)
    (z : Q)
    (hcommz : ⁅⁅H, Subgroup.zpowers z⁆, Subgroup.zpowers z⁆ = ⊥)
    (L : Subgroup (Q ⧸ Subgroup.centralizer (H : Set Q)))
    (hzL : QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) z ∈ L)
    (hzout :
      (⟨QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) z, hzL⟩ : L) ∉
        pCore p L) :
    L = ⊤ := by
  classical
  let C : Subgroup Q := Subgroup.centralizer (H : Set Q)
  have hCnormal : C.Normal := Subgroup.normal_centralizer (H := H)
  let Cnormal : C.Normal := hCnormal
  let q : Q →* Q ⧸ C := QuotientGroup.mk' C
  let A : Subgroup Q := L.comap q
  have hC_le_A : C ≤ A := by
    intro c hc
    change q c ∈ L
    have hqc : q c = 1 := (QuotientGroup.eq_one_iff c).2 hc
    rw [hqc]
    exact L.one_mem
  have hH_le_C : H ≤ C := by
    exact (Subgroup.le_centralizer_iff_isMulCommutative (K := H)).2 hHcomm
  have hH_le_A : H ≤ A := hH_le_C.trans hC_le_A
  let HA : Subgroup A := H.subgroupOf A
  have hHA_normal : HA.Normal := Subgroup.Normal.subgroupOf hHnormal A
  let HAnormal : HA.Normal := hHA_normal
  have hHAp : IsPGroup p HA := by
    simpa [HA] using hHp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := H) (K := A) hH_le_A).symm
  have hHAne : HA ≠ ⊥ := by
    intro hbot
    apply hHne
    apply le_antisymm
    · intro h hh
      let hA : A := ⟨h, hH_le_A hh⟩
      have hhA : hA ∈ HA := Subgroup.mem_subgroupOf.mpr hh
      rw [hbot] at hhA
      have hAone : hA = 1 := by simpa using hhA
      have hone : h = 1 := congrArg Subtype.val hAone
      simp [hone]
    · exact bot_le
  have hzA : z ∈ A := by
    simpa [A, q, C] using hzL
  let zA : A := ⟨z, hzA⟩
  let f : A →* L :=
    (q.comp A.subtype).codRestrict L (fun a => a.2)
  have hf_surj : Function.Surjective f := by
    intro l
    rcases QuotientGroup.mk'_surjective C (l : Q ⧸ C) with ⟨g, hg⟩
    have hgA : g ∈ A := by
      change q g ∈ L
      rw [hg]
      exact l.2
    refine ⟨⟨g, hgA⟩, ?_⟩
    apply Subtype.ext
    exact hg
  have hker : Subgroup.centralizer (HA : Set A) = f.ker := by
    ext a
    constructor
    · intro ha
      apply MonoidHom.mem_ker.mpr
      apply Subtype.ext
      apply (QuotientGroup.eq_one_iff (N := C) (x := (a : Q))).2
      change (a : Q) ∈ Subgroup.centralizer (H : Set Q)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      let hA : A := ⟨h, hH_le_A hh⟩
      have hhA : hA ∈ HA := Subgroup.mem_subgroupOf.mpr hh
      exact congrArg Subtype.val
        (Subgroup.mem_centralizer_iff.mp ha hA hhA)
    · intro ha
      rw [Subgroup.mem_centralizer_iff]
      intro hA hhA
      apply Subtype.ext
      have haf : f a = 1 := MonoidHom.mem_ker.mp ha
      have haC : (a : Q) ∈ C := by
        apply (QuotientGroup.eq_one_iff (N := C) (x := (a : Q))).1
        exact congrArg Subtype.val haf
      have hhH : (hA : Q) ∈ H := Subgroup.mem_subgroupOf.mp hhA
      exact Subgroup.mem_centralizer_iff.mp haC (hA : Q) hhH
  let e : A ⧸ Subgroup.centralizer (HA : Set A) ≃* L :=
    QuotientGroup.liftEquiv (Subgroup.centralizer (HA : Set A)) hf_surj hker
  have he_z :
      e (QuotientGroup.mk' (Subgroup.centralizer (HA : Set A)) zA) =
        (⟨q z, by simpa [q, C] using hzL⟩ : L) := by
    rfl
  have hcommA :
      ⁅⁅HA, Subgroup.zpowers zA⁆, Subgroup.zpowers zA⁆ = ⊥ := by
    apply Subgroup.map_injective A.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_commutator]
    have hHAmap : HA.map A.subtype = H := by
      simpa [HA] using Subgroup.map_subgroupOf_eq_of_le hH_le_A
    have hzmap : (Subgroup.zpowers zA).map A.subtype = Subgroup.zpowers z := by
      rw [MonoidHom.map_zpowers]
      rfl
    rw [hHAmap, hzmap, hcommz, Subgroup.map_bot]
  by_contra hLtop
  have hAtop : A ≠ ⊤ := by
    intro hAeq
    apply hLtop
    have hmapcomap : A.map q = L := by
      calc
        A.map q = q.range ⊓ L := Subgroup.map_comap_eq q L
        _ = L := by
          rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective C), top_inf_eq]
    have htopmap : (⊤ : Subgroup Q).map q = ⊤ := by
      ext y
      constructor
      · intro _
        trivial
      · intro _
        rcases QuotientGroup.mk'_surjective C y with ⟨g, rfl⟩
        exact Subgroup.mem_map.mpr ⟨g, by trivial, rfl⟩
    rw [hAeq, htopmap] at hmapcomap
    exact hmapcomap.symm
  have hAlt : A < (⊤ : Subgroup Q) := lt_top_iff_ne_top.mpr hAtop
  have hAcard : Nat.card A < Nat.card Q := by
    simpa using natCard_lt_of_subgroup_lt hAlt
  have hstable : pStable p A := hminSub A hAcard
  have hcoreNe : pCore p A ≠ ⊥ := by
    intro hcoreBot
    apply hHAne
    apply le_antisymm
    · have hle : HA ≤ pCore p A := le_sSup ⟨hHA_normal, hHAp⟩
      rw [hcoreBot] at hle
      exact hle
    · exact bot_le
  have hlocal : pStableLocal p A :=
    Glauberman.pStableLocal_of_core_ne_bot (G := A) p hstable hcoreNe
  have hnorm : (pPrimeCore p A ⊔ HA).Normal :=
    Subgroup.sup_normal (pPrimeCore p A) HA
  have hzNorm : zA ∈ Subgroup.normalizer (HA : Set A) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hHA_normal]
    trivial
  have hzLocal := hlocal HA hHAp hnorm zA hzNorm hcommA
  have hzCore :
      QuotientGroup.mk' (Subgroup.centralizer (HA : Set A)) zA ∈
        pCore p (A ⧸ Subgroup.centralizer (HA : Set A)) := by
    exact (normal_ambient_quotient_core_membership_iff_local
      (p := p) HA hHA_normal zA hzNorm).mp hzLocal
  have hcoreMap :
      (pCore p (A ⧸ Subgroup.centralizer (HA : Set A))).map e.toMonoidHom =
        pCore p L :=
    pCore_map_iso (G := A ⧸ Subgroup.centralizer (HA : Set A))
      (G' := L) (p := p) e
  apply hzout
  have hzMap :
      e (QuotientGroup.mk' (Subgroup.centralizer (HA : Set A)) zA) ∈
        (pCore p (A ⧸ Subgroup.centralizer (HA : Set A))).map e.toMonoidHom :=
    Subgroup.mem_map_of_mem e.toMonoidHom hzCore
  rw [hcoreMap, he_z] at hzMap
  simpa [q, C] using hzMap

private def baseSLHom {p : ℕ} [Fact p.Prime]
    {K : Type*} [Field K] [Algebra (ZMod p) K] :
    Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →*
      Matrix.SpecialLinearGroup (Fin 2) K :=
  Matrix.SpecialLinearGroup.map (algebraMap (ZMod p) K)

private theorem baseSLHom_injective {p : ℕ} [Fact p.Prime]
    {K : Type*} [Field K] [Algebra (ZMod p) K] :
    Function.Injective (baseSLHom (p := p) (K := K)) := by
  intro A B hAB
  apply Subtype.ext
  apply Matrix.map_injective (RingHom.injective (algebraMap (ZMod p) K))
  exact congrArg Subtype.val hAB

private theorem baseSLRange_pCore_eq_bot {p : ℕ} [Fact p.Prime]
    (hpodd : p ≠ 2) {K : Type*} [Field K] [Algebra (ZMod p) K] :
    pCore p (baseSLHom (p := p) (K := K)).range = ⊥ := by
  let e : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) ≃*
      (baseSLHom (p := p) (K := K)).range :=
    MonoidHom.ofInjective (baseSLHom_injective (p := p) (K := K))
  have hmap := pCore_map_iso
    (G := Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
    (G' := (baseSLHom (p := p) (K := K)).range) (p := p) e
  rw [Glauberman.qdSL_pCore_eq_bot p hpodd] at hmap
  simpa using hmap.symm

private def comapMulEquivOfBijective
    {G₁ G₂ : Type*} [Group G₁] [Group G₂]
    (f : G₁ →* G₂) (hf : Function.Bijective f) (S : Subgroup G₂) :
    S.comap f ≃* S := by
  let fS : S.comap f →* S :=
    (f.comp (S.comap f).subtype).codRestrict S (fun g => g.2)
  apply MulEquiv.ofBijective fS
  constructor
  · intro a b hab
    apply Subtype.ext
    apply hf.1
    exact congrArg Subtype.val hab
  · intro s
    rcases hf.2 (s : G₂) with ⟨g, hg⟩
    have hgS : g ∈ S.comap f := by
      change f g ∈ S
      rw [hg]
      exact s.2
    refine ⟨⟨g, hgS⟩, ?_⟩
    apply Subtype.ext
    exact hg

private theorem baseSLComap_pCore_eq_bot
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {G K : Type*} [Group G] [Finite G]
    [Field K] [Algebra (ZMod p) K] [Finite K]
    (ρSL : G →* Matrix.SpecialLinearGroup (Fin 2) K)
    (hρSL : Function.Injective ρSL)
    (hρSLsurj : Function.Surjective ρSL) :
    pCore p ((baseSLHom (p := p) (K := K)).range.comap ρSL) = ⊥ := by
  let e := comapMulEquivOfBijective ρSL ⟨hρSL, hρSLsurj⟩
    (baseSLHom (p := p) (K := K)).range
  have hmap := pCore_map_iso
    (G := (baseSLHom (p := p) (K := K)).range.comap ρSL)
    (G' := (baseSLHom (p := p) (K := K)).range) (p := p) e
  rw [baseSLRange_pCore_eq_bot hpodd] at hmap
  apply le_bot_iff.mp
  intro g hg
  have hgm : e g ∈
      (pCore p ((baseSLHom (p := p) (K := K)).range.comap ρSL)).map
        e.toMonoidHom :=
    Subgroup.mem_map_of_mem e.toMonoidHom hg
  rw [hmap] at hgm
  have heone : e g = 1 := by simpa using hgm
  have gone : g = 1 := e.injective (by simpa using heone)
  simp [gone]

private def lowerTransvectionSL (R : Type*) [CommRing R] :
    Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩

set_option backward.isDefEq.respectTransparency false in
private theorem lowerTransvection_mem_baseSLRange
    {p : ℕ} [Fact p.Prime]
    {K : Type*} [Field K] [Algebra (ZMod p) K] :
    lowerTransvectionSL K ∈ (baseSLHom (p := p) (K := K)).range := by
  refine ⟨lowerTransvectionSL (ZMod p), ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [baseSLHom, lowerTransvectionSL,
      Matrix.SpecialLinearGroup.map_apply_coe]

private theorem step6_finrank_one
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {Q : Type u} [Group Q] [Finite Q]
    (hminSub : ∀ A : Subgroup Q,
      Nat.card A < Nat.card Q → pStable p A)
    (H : Subgroup Q) (hHnormal : H.Normal) (hHne : H ≠ ⊥)
    (hHp : IsPGroup p H) (hHcomm : IsMulCommutative H)
    (z : Q)
    (hcommz : ⁅⁅H, Subgroup.zpowers z⁆, Subgroup.zpowers z⁆ = ⊥)
    {K : Type*} [Field K] [Algebra (ZMod p) K] [Finite K]
    (r : K)
    (xq yq : Q ⧸ Subgroup.centralizer (H : Set Q))
    (hyrep : yq = QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) z)
    (hdegree : Module.finrank (ZMod p) K = (minpoly (ZMod p) r).natDegree)
    (ρSL : Q ⧸ Subgroup.centralizer (H : Set Q) →*
      Matrix.SpecialLinearGroup (Fin 2) K)
    (hρSL : Function.Injective ρSL)
    (hxmat : ((ρSL xq : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = !![1, r; 0, 1])
    (hymat : ((ρSL yq : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = !![1, 0; 1, 1])
    (hρSLsurj : Function.Surjective ρSL) :
    Module.finrank (ZMod p) K = 1 := by
  classical
  let S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    (baseSLHom (p := p) (K := K)).range
  let L : Subgroup (Q ⧸ Subgroup.centralizer (H : Set Q)) := S.comap ρSL
  have hyS : ρSL yq ∈ S := by
    have hY : ρSL yq = lowerTransvectionSL K := by
      apply Subtype.ext
      simpa [lowerTransvectionSL] using hymat
    rw [hY]
    exact lowerTransvection_mem_baseSLRange
  have hzL : QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) z ∈ L := by
    change ρSL (QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) z) ∈ S
    rw [← hyrep]
    exact hyS
  have hcoreL : pCore p L = ⊥ := by
    simpa [L, S] using
      (baseSLComap_pCore_eq_bot hpodd ρSL hρSL hρSLsurj)
  have hzout :
      (⟨QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) z, hzL⟩ : L) ∉
        pCore p L := by
    intro hzcore
    rw [hcoreL] at hzcore
    have hzOne :
        (⟨QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) z, hzL⟩ : L) = 1 := by
      simpa using hzcore
    have hyOne : yq = 1 := by
      rw [hyrep]
      exact congrArg Subtype.val hzOne
    have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 0) hymat
    simp [hyOne] at hentry
  have hLtop : L = ⊤ :=
    quotient_subgroup_eq_top_of_quadratic hminSub H hHnormal hHne hHp hHcomm
      z hcommz L hzL hzout
  have hxL : xq ∈ L := by rw [hLtop]; trivial
  have hxS : ρSL xq ∈ S := hxL
  rcases hxS with ⟨A, hA⟩
  let a : ZMod p := (A : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1
  have hrbase : algebraMap (ZMod p) K a = r := by
    have hentry := congrArg
      (fun M : Matrix.SpecialLinearGroup (Fin 2) K =>
        ((M : Matrix (Fin 2) (Fin 2) K) 0 1)) hA
    have hxentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) hxmat
    simpa [S, baseSLHom, a, Matrix.SpecialLinearGroup.map_apply_coe]
      using hentry.trans hxentry
  rw [hdegree]
  exact (minpoly.natDegree_eq_one_iff).2 ⟨a, hrbase⟩

private def comapMulEquivOfInjectiveOf_le_range
    {G₁ G₂ : Type*} [Group G₁] [Group G₂]
    (f : G₁ →* G₂) (hf : Function.Injective f) (S : Subgroup G₂)
    (hS : S ≤ f.range) :
    S.comap f ≃* S := by
  let fS : S.comap f →* S :=
    (f.comp (S.comap f).subtype).codRestrict S (fun g => g.2)
  apply MulEquiv.ofBijective fS
  constructor
  · intro a b hab
    apply Subtype.ext
    apply hf
    exact congrArg Subtype.val hab
  · intro s
    rcases hS s.2 with ⟨g, hg⟩
    have hgS : g ∈ S.comap f := by
      change f g ∈ S
      rw [hg]
      exact s.2
    refine ⟨⟨g, hgS⟩, ?_⟩
    apply Subtype.ext
    exact hg

private theorem quadratic_subgroup_forces_card_eq
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (hminSub : ∀ A : Subgroup Q,
      Nat.card A < Nat.card Q → pStable p A)
    (H : Subgroup Q) (hHnormal : H.Normal) (hHne : H ≠ ⊥)
    (hHp : IsPGroup p H) (hHcomm : IsMulCommutative H)
    (z : Q)
    (hcommz : ⁅⁅H, Subgroup.zpowers z⁆, Subgroup.zpowers z⁆ = ⊥)
    {G₂ : Type*} [Group G₂] [Finite G₂]
    (ρ₂ : Q ⧸ Subgroup.centralizer (H : Set Q) →* G₂)
    (hρ₂ : Function.Injective ρ₂)
    (S : Subgroup G₂) (hSrange : S ≤ ρ₂.range)
    (hzS : ρ₂ (QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) z) ∈ S)
    (hcoreS : pCore p S = ⊥)
    (hzρne : ρ₂ (QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) z) ≠ 1) :
    Nat.card (Q ⧸ Subgroup.centralizer (H : Set Q)) = Nat.card S := by
  classical
  let L : Subgroup (Q ⧸ Subgroup.centralizer (H : Set Q)) := S.comap ρ₂
  let e : L ≃* S :=
    comapMulEquivOfInjectiveOf_le_range ρ₂ hρ₂ S hSrange
  have hcoreL : pCore p L = ⊥ := by
    have hmap := pCore_map_iso (G := L) (G' := S) (p := p) e
    rw [hcoreS] at hmap
    apply le_bot_iff.mp
    intro g hg
    have hgm : e g ∈ (pCore p L).map e.toMonoidHom :=
      Subgroup.mem_map_of_mem e.toMonoidHom hg
    rw [hmap] at hgm
    have heone : e g = 1 := by simpa using hgm
    have gone : g = 1 := e.injective (by simpa using heone)
    simp [gone]
  have hzL : QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) z ∈ L := hzS
  have hzout :
      (⟨QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) z, hzL⟩ : L) ∉
        pCore p L := by
    intro hzcore
    rw [hcoreL] at hzcore
    have hzone :
        (⟨QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) z, hzL⟩ : L) = 1 := by
      simpa using hzcore
    apply hzρne
    have hzq : QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) z = 1 :=
      congrArg Subtype.val hzone
    simp [hzq]
  have hLtop : L = ⊤ :=
    quotient_subgroup_eq_top_of_quadratic hminSub H hHnormal hHne hHp hHcomm
      z hcommz L hzL hzout
  let eTop : L ≃* (Q ⧸ Subgroup.centralizer (H : Set Q)) :=
    (MulEquiv.subgroupCongr hLtop).trans Subgroup.topEquiv
  calc
    Nat.card (Q ⧸ Subgroup.centralizer (H : Set Q)) = Nat.card L :=
      (Nat.card_congr eTop.toEquiv).symm
    _ = Nat.card S := Nat.card_congr e.toEquiv

private theorem prime_eq_three_of_field_card_nine
    {p : ℕ} [Fact p.Prime]
    {K : Type*} [Field K] [Algebra (ZMod p) K] [Finite K]
    (hKcard : Nat.card K = 9) :
    p = 3 := by
  let f : ℕ := Module.finrank (ZMod p) K
  have hpow : p ^ f = 9 := by
    calc
      p ^ f = Nat.card K := FiniteField.pow_finrank_eq_natCard p K
      _ = 9 := hKcard
  have hfne : f ≠ 0 := by
    intro hf
    rw [hf, pow_zero] at hpow
    omega
  have hp9 : p ∣ 9 := by
    rw [← hpow]
    exact dvd_pow_self p hfne
  have hp3pow : p ∣ 3 ^ 2 := by simpa using hp9
  have hp3 : p ∣ 3 := (Fact.out : p.Prime).dvd_of_dvd_pow hp3pow
  exact (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime)
    (by decide : Nat.Prime 3)).mp hp3

set_option backward.isDefEq.respectTransparency false in
/-- The representation-compatible conclusion of paper Step 6.

The lower transvection `yq` is required to be the quotient image of the
quadratic element `z`.  The subgroup-minimality hypothesis is the exact form
used here: every proper subgroup of `Q` is `p`-stable. -/
public theorem lemma63_step6_aligned
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {Q : Type u} [Group Q] [Finite Q]
    (hminSub : ∀ B : Subgroup Q,
      Nat.card B < Nat.card Q → pStable p B)
    (A : Subgroup Q) (hAnormal : A.Normal) (hAne : A ≠ ⊥)
    (hAp : IsPGroup p A) (hAcomm : IsMulCommutative A)
    (z : Q)
    (hcommz : ⁅⁅A, Subgroup.zpowers z⁆, Subgroup.zpowers z⁆ = ⊥)
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V]
    (D : Lemma62Data p hpodd V
      (Q ⧸ Subgroup.centralizer (A : Set Q)))
    (xq yq : Q ⧸ Subgroup.centralizer (A : Set Q))
    (hyrep : yq =
      QuotientGroup.mk' (Subgroup.centralizer (A : Set Q)) z)
    (hgen : Subgroup.closure ({xq, yq} : Set
      (Q ⧸ Subgroup.centralizer (A : Set Q))) = ⊤)
    (hx2 : ((D.ρ xq : V →ₗ[ZMod p] V) - 1) ^ 2 = 0)
    (hxn : (D.ρ xq : V →ₗ[ZMod p] V) - 1 ≠ 0)
    (hy2 : ((D.ρ yq : V →ₗ[ZMod p] V) - 1) ^ 2 = 0)
    (hyn : (D.ρ yq : V →ₗ[ZMod p] V) - 1 ≠ 0) :
    ∃ (coord : V ≃ₗ[ZMod p] qdSpace p)
        (e : (Q ⧸ Subgroup.centralizer (A : Set Q)) ≃* qdSL p),
      ∀ (g : Q ⧸ Subgroup.centralizer (A : Set Q)) (v : V),
        coord ((D.ρ g : V →ₗ[ZMod p] V) v) =
          Matrix.SpecialLinearGroup.toLin' (e g) (coord v) := by
  classical
  rcases lemma6_2_model_of_generators hpodd D xq yq hgen hx2 hxn hy2 hyn with
    ⟨K, hK, hAlg, phi, r, hphi, hall, coord, hdegree, hrne,
      hgen', hxmodel, hymodel⟩
  let Kfield : Field K := hK
  let KAlgebra : Algebra (ZMod p) K := hAlg
  let KModule : Module K V := moduleOfAlgHom phi
  let Vfinite : Finite V := Module.finite_of_finite (ZMod p)
  let Kfinite : Finite K := Finite.of_injective
    (fun k : K => fun v : V => phi k v) (by
      intro a b hab
      apply hphi
      apply LinearMap.ext
      intro v
      exact congrFun hab v)
  have hlinear (g : Q ⧸ Subgroup.centralizer (A : Set Q))
      (k : K) (v : V) :
      (D.ρ g : V →ₗ[ZMod p] V) (k • v) =
        k • (D.ρ g : V →ₗ[ZMod p] V) v := by
    change D.lin g (phi k v) = phi k (D.lin g v)
    simpa [Module.End.mul_apply] using
      congrArg (fun f : Module.End (ZMod p) V => f v) (hall g k)
  rcases Dickson.two_transvections_classification_aligned (hpodd := hpodd)
      D.ρ D.faithful K hlinear coord r xq yq hdegree hrne hgen'
        hxmodel hymodel with
    ⟨coordFin, rhoSL, hrhoSL, hxmat, hymat, haction, hcase⟩
  have hrhoSLsurj : Function.Surjective rhoSL := by
    rcases hcase with hsurj | hexceptional
    · exact hsurj
    · rcases hexceptional with ⟨hKcard, hrquad, heq5⟩
      have hp3 : p = 3 := prime_eq_three_of_field_card_nine hKcard
      subst p
      let prime5 : Fact (Nat.Prime 5) := ⟨by decide⟩
      let X : Matrix.SpecialLinearGroup (Fin 2) K :=
        ⟨!![1, r; 0, 1], by simp [Matrix.det_fin_two]⟩
      let Y : Matrix.SpecialLinearGroup (Fin 2) K :=
        ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
      rcases Dickson.exceptionalF9_exists_pCore_trivial_subgroup hKcard r hrquad with
        ⟨L, hLclosure, hYL, hLcard, hLcore⟩
      have hrhox : rhoSL xq = X := by
        apply Subtype.ext
        simpa [X] using hxmat
      have hrhoy : rhoSL yq = Y := by
        apply Subtype.ext
        simpa [Y] using hymat
      have hclosureRange :
          Subgroup.closure ({X, Y} : Set _) ≤ rhoSL.range := by
        rw [Subgroup.closure_le]
        intro g hg
        have hg' : g = X ∨ g = Y := by simpa using hg
        rcases hg' with rfl | rfl
        · exact ⟨xq, hrhox⟩
        · exact ⟨yq, hrhoy⟩
      have hLrange : L ≤ rhoSL.range := hLclosure.trans hclosureRange
      have hzL :
          rhoSL (QuotientGroup.mk' (Subgroup.centralizer (A : Set Q)) z) ∈ L := by
        rw [← hyrep, hrhoy]
        exact hYL
      have hzrho_ne :
          rhoSL (QuotientGroup.mk' (Subgroup.centralizer (A : Set Q)) z) ≠ 1 := by
        intro hone
        have hymatZ :
            ((rhoSL (QuotientGroup.mk'
                (Subgroup.centralizer (A : Set Q)) z) :
                Matrix.SpecialLinearGroup (Fin 2) K) :
              Matrix (Fin 2) (Fin 2) K) = !![1, 0; 1, 1] := by
          rw [← hyrep]
          exact hymat
        have hentry := congrArg
          (fun M : Matrix (Fin 2) (Fin 2) K => M 1 0) hymatZ
        have hzero := congrArg
          (fun M : Matrix.SpecialLinearGroup (Fin 2) K =>
            ((M : Matrix (Fin 2) (Fin 2) K) 1 0)) hone
        have hfalse : (0 : K) = 1 := by
          exact (by simpa using hzero.symm.trans hentry)
        exact zero_ne_one hfalse
      have hcardQ :
          Nat.card (Q ⧸ Subgroup.centralizer (A : Set Q)) = 24 := by
        rw [← hLcard]
        exact quadratic_subgroup_forces_card_eq
          hminSub A hAnormal hAne hAp hAcomm z hcommz
          rhoSL hrhoSL L hLrange hzL hLcore hzrho_ne
      rcases heq5 with ⟨e5⟩
      have hcardQ5 :
          Nat.card (Q ⧸ Subgroup.centralizer (A : Set Q)) = 120 := by
        calc
          Nat.card (Q ⧸ Subgroup.centralizer (A : Set Q)) =
              Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) :=
            Nat.card_congr e5.toEquiv
          _ = 5 * (5 ^ 2 - 1) := by
            simpa [Nat.card_zmod] using
              (GorensteinWalter.sl2_card_formula (ZMod 5))
          _ = 120 := by norm_num
      omega
  have hfinrank : Module.finrank (ZMod p) K = 1 :=
    step6_finrank_one hpodd hminSub A hAnormal hAne hAp hAcomm
      z hcommz r xq yq hyrep hdegree rhoSL hrhoSL hxmat hymat hrhoSLsurj
  have halgBij : Function.Bijective (algebraMap (ZMod p) K) :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfinrank
  let eAlg : ZMod p ≃ₐ[ZMod p] K :=
    AlgEquiv.ofBijective (Algebra.ofId (ZMod p) K) halgBij
  let coordP : V ≃ₗ[ZMod p] qdSpace p :=
    (coordFin.restrictScalars (ZMod p)).trans
      (LinearEquiv.piCongrRight fun _ : Fin 2 => eAlg.symm.toLinearEquiv)
  let eK : (Q ⧸ Subgroup.centralizer (A : Set Q)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K :=
    MulEquiv.ofBijective rhoSL ⟨hrhoSL, hrhoSLsurj⟩
  let eP : (Q ⧸ Subgroup.centralizer (A : Set Q)) ≃* qdSL p :=
    eK.trans (Dickson.specialLinearMapEquiv eAlg.symm.toRingEquiv)
  refine ⟨coordP, eP, ?_⟩
  intro g v
  ext i
  have hcompat := haction g v
  change eAlg.symm (coordFin ((D.ρ g : V →ₗ[ZMod p] V) v) i) = _
  rw [hcompat]
  simp [coordP, eP, eK, Dickson.specialLinearMapEquiv,
    Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply,
    Matrix.mulVec, dotProduct]

end CFSG.Glauberman
