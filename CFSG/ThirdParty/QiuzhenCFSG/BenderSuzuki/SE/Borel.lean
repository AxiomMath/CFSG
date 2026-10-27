module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Interfaces
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_12
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.example_1_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.FrobeniusKernel
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_3_3
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

namespace CFSG
end CFSG
open CFSG

/-!
# Borel subgroups in the simple Bender models

This file develops the action-theoretic core needed to identify the standard
Sylow `2`-normalizers in the PSL, Suzuki, and PSU models with point
stabilizers, and then transport their doubly transitive natural actions to
Borel coset actions.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open MatrixGroups PFAppendixIII PFchapter1section1
open scoped LinearAlgebra.Projectivization

universe u v

/-- A nontrivial subgroup that fixes `alpha` and acts regularly away from
`alpha` has no ambient normalizer elements moving `alpha`.  Hence, if the
point stabilizer normalizes the subgroup, the two subgroups are equal. -/
public theorem normalizer_eq_stabilizer_of_regular_compl
    {G : Type u} {Omega : Type v} [Group G] [MulAction G Omega]
    (R : Subgroup G) (alpha : Omega)
    (hR_le : R ≤ MulAction.stabilizer G alpha)
    (hR_ne : R ≠ ⊥)
    (hregular : ∀ a b : Omega, a ≠ alpha → b ≠ alpha →
      ∃! r : R, (r : G) • a = b)
    (hstabilizer_le : MulAction.stabilizer G alpha ≤
      Subgroup.normalizer (R : Set G)) :
    Subgroup.normalizer (R : Set G) = MulAction.stabilizer G alpha := by
  apply le_antisymm
  · intro x hx
    rw [MulAction.mem_stabilizer_iff]
    by_contra hxmove
    have hxnormal := Subgroup.mem_normalizer_iff.mp hx
    have hfix_moved : ∀ r : R, (r : G) • (x • alpha) = x • alpha := by
      intro r
      have hconj_mem : x⁻¹ * (r : G) * x ∈ R := by
        apply (hxnormal (x⁻¹ * (r : G) * x)).2
        have hconj_back :
            x * (x⁻¹ * (r : G) * x) * x⁻¹ = (r : G) := by
          group
        rw [hconj_back]
        exact r.property
      let rconj : R := ⟨x⁻¹ * (r : G) * x, hconj_mem⟩
      calc
        (r : G) • (x • alpha) = ((r : G) * x) • alpha := by
          rw [mul_smul]
        _ = (x * (rconj : G)) • alpha := by
          congr 1
          dsimp [rconj]
          group
        _ = x • ((rconj : G) • alpha) := mul_smul _ _ _
        _ = x • alpha := by
          rw [MulAction.mem_stabilizer_iff.mp (hR_le rconj.property)]
    obtain ⟨_r0, _hr0, hr_unique⟩ :=
      hregular (x • alpha) (x • alpha) hxmove hxmove
    obtain ⟨r, hr_ne_one⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp hR_ne
    have hr_solution : (r : G) • (x • alpha) = x • alpha :=
      hfix_moved r
    have hone_solution : ((1 : R) : G) • (x • alpha) = x • alpha := by
      simp
    apply hr_ne_one
    exact (hr_unique r hr_solution).trans
      (hr_unique 1 hone_solution).symm
  · exact hstabilizer_le

/-- Normalizer control: if a Sylow subgroup of `M`, transported into `G`,
has ambient normalizer contained in `M`, then it is an ambient Sylow
subgroup. -/
public theorem exists_sylow_map_eq_of_normalizer_le
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {M : Subgroup G} (P : Sylow p M)
    (hN : Subgroup.normalizer
      (((P : Subgroup M).map M.subtype : Subgroup G) : Set G) ≤ M) :
    ∃ P0 : Sylow p G,
      (P0 : Subgroup G) = (P : Subgroup M).map M.subtype := by
  classical
  let P0sub : Subgroup G := (P : Subgroup M).map M.subtype
  have hP0p : IsPGroup p P0sub :=
    IsPGroup.map P.isPGroup' M.subtype
  refine ⟨⟨P0sub, hP0p, ?_⟩, rfl⟩
  intro Q hQp hP0Q
  have hQ_le_P0 : Q ≤ P0sub := by
    let K : Subgroup Q := P0sub.subgroupOf Q
    haveI : Fact (IsPGroup p Q) := ⟨hQp⟩
    have hQnil : Group.IsNilpotent Q :=
      IsPGroup.isNilpotent (p := p) (G := Q) hQp
    have hnc : NormalizerCondition Q := by
      letI : Group.IsNilpotent Q := hQnil
      exact normalizerCondition_of_isNilpotent (G := Q)
    have hnormalizerK_le : Subgroup.normalizer (K : Set Q) ≤ K := by
      intro x hxnormalizer
      have hxnormalizerP0 :
          (x : G) ∈ Subgroup.normalizer (P0sub : Set G) := by
        refine Subgroup.mem_normalizer_fintype ?_
        intro y hyP0
        have hyQ : y ∈ Q := hP0Q hyP0
        have hyK : (⟨y, hyQ⟩ : Q) ∈ K := hyP0
        have hconjK :
            x * (⟨y, hyQ⟩ : Q) * x⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp hxnormalizer
            (⟨y, hyQ⟩ : Q)).1 hyK
        exact hconjK
      have hxM : (x : G) ∈ M := hN hxnormalizerP0
      let R : Subgroup M := (Q ⊓ M).subgroupOf M
      have hRp : IsPGroup p R := by
        have hInfp : IsPGroup p (Q ⊓ M : Subgroup G) :=
          hQp.to_inf_left
        have e : R ≃* (Q ⊓ M : Subgroup G) :=
          Subgroup.subgroupOfEquivOfLe
            (H := Q ⊓ M) (K := M) inf_le_right
        exact hInfp.of_equiv e.symm
      have hP_le_R : (P : Subgroup M) ≤ R := by
        intro y hyP
        have hyP0 : (y : G) ∈ P0sub :=
          Subgroup.mem_map_of_mem M.subtype hyP
        exact ⟨hP0Q hyP0, y.property⟩
      have hR_eq : R = (P : Subgroup M) :=
        P.is_maximal' hRp hP_le_R
      have hxR : (⟨(x : G), hxM⟩ : M) ∈ R :=
        ⟨x.property, hxM⟩
      have hxP : (⟨(x : G), hxM⟩ : M) ∈ (P : Subgroup M) := by
        simpa [hR_eq] using hxR
      have hxP0 : (x : G) ∈ P0sub :=
        Subgroup.mem_map_of_mem M.subtype hxP
      exact hxP0
    have hnormalizerK_eq : Subgroup.normalizer (K : Set Q) = K :=
      le_antisymm hnormalizerK_le Subgroup.le_normalizer
    have hKtop : K = ⊤ :=
      normalizerCondition_iff_only_full_group_self_normalizing.mp
        hnc K hnormalizerK_eq
    intro x hxQ
    have hxK : (⟨x, hxQ⟩ : Q) ∈ K := by simp [hKtop]
    exact hxK
  exact le_antisymm hQ_le_P0 hP0Q

/-- A normal `p`-subgroup with a complement of `p`-prime cardinality is a
Sylow subgroup of the containing subgroup. -/
public theorem exists_sylow_map_eq_of_normal_complement
    {G : Type u} [Group G] {p : ℕ} [Fact p.Prime]
    {U R H : Subgroup G}
    (hR_le : R ≤ U) (hH_le : H ≤ U)
    (hU_le_normalizer : U ≤ Subgroup.normalizer (R : Set G))
    (hdisjoint : R ⊓ H = ⊥) (hsup : R ⊔ H = U)
    (hRp : IsPGroup p R) (hHcard : ¬ p ∣ Nat.card H) :
    ∃ P : Sylow p U,
      (P : Subgroup U).map U.subtype = R := by
  let Rsub : Subgroup U := R.subgroupOf U
  let Hsub : Subgroup U := H.subgroupOf U
  have hdisjoint_sub : Disjoint Rsub Hsub := by
    rw [Subgroup.disjoint_def]
    intro x hxR hxH
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp (by
      rw [disjoint_iff_inf_le, hdisjoint]) hxR hxH
  have hsup_sub : Rsub ⊔ Hsub = ⊤ := by
    simpa [Rsub, Hsub, hsup] using
      (Subgroup.subgroupOf_sup
        (A := R) (A' := H) (B := U) hR_le hH_le).symm
  letI : Rsub.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hU_le_normalizer
  have hcomplement : Rsub.IsComplement' Hsub := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
      hdisjoint_sub ?_
    rw [Set.eq_univ_iff_forall]
    intro x
    have hx : x ∈ Rsub ⊔ Hsub := by simp [hsup_sub]
    rcases (Subgroup.mem_sup_of_normal_left
      (x := x) (s := Rsub) (t := Hsub)).1 hx with
      ⟨r, hr, h, hh, hmul⟩
    exact ⟨r, hr, h, hh, hmul⟩
  have hRp_sub : IsPGroup p Rsub := by
    let e : Rsub ≃* R :=
      Subgroup.subgroupOfEquivOfLe
        (G := G) (H := R) (K := U) hR_le
    exact hRp.of_equiv e.symm
  have hHsub_card : Nat.card Hsub = Nat.card H :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe
        (G := G) (H := H) (K := U) hH_le).toEquiv
  have hindex : Rsub.index = Nat.card H := by
    calc
      Rsub.index = Nat.card Hsub := hcomplement.symm.index_eq_card
      _ = Nat.card H := hHsub_card
  let P : Sylow p U := hRp_sub.toSylow (by simpa [hindex] using hHcard)
  refine ⟨P, ?_⟩
  change Rsub.map U.subtype = R
  exact Subgroup.map_subgroupOf_eq_of_le hR_le

/-- A doubly transitive action remains doubly transitive after replacing the
acted-on set by the left cosets of a point stabilizer. -/
public theorem quotient_stabilizer_isTwoPretransitive
    {G : Type u} {Omega : Type v} [Group G] [MulAction G Omega]
    (alpha : Omega)
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2) :
    MulAction.IsMultiplyPretransitive G
      (G ⧸ MulAction.stabilizer G alpha) 2 := by
  rw [MulAction.is_two_pretransitive_iff] at htwo ⊢
  intro a b c d hab hcd
  have hab' : MulAction.ofQuotientStabilizer G alpha a ≠
      MulAction.ofQuotientStabilizer G alpha b := by
    intro h
    exact hab (MulAction.injective_ofQuotientStabilizer G alpha h)
  have hcd' : MulAction.ofQuotientStabilizer G alpha c ≠
      MulAction.ofQuotientStabilizer G alpha d := by
    intro h
    exact hcd (MulAction.injective_ofQuotientStabilizer G alpha h)
  obtain ⟨g, hga, hgb⟩ := htwo hab' hcd'
  refine ⟨g, ?_, ?_⟩
  · apply MulAction.injective_ofQuotientStabilizer G alpha
    rw [MulAction.ofQuotientStabilizer_smul, hga]
  · apply MulAction.injective_ofQuotientStabilizer G alpha
    rw [MulAction.ofQuotientStabilizer_smul, hgb]

/-- Pull double transitivity back along a surjective group homomorphism. -/
public theorem isTwoPretransitive_compHom_of_surjective
    {G : Type u} {Q : Type v} {Omega : Type*}
    [Group G] [Group Q] [MulAction Q Omega]
    (f : G →* Q) (hf : Function.Surjective f)
    (htwo : MulAction.IsMultiplyPretransitive Q Omega 2) :
    letI : MulAction G Omega := MulAction.compHom Omega f
    MulAction.IsMultiplyPretransitive G Omega 2 := by
  letI : MulAction G Omega := MulAction.compHom Omega f
  rw [MulAction.is_two_pretransitive_iff] at htwo ⊢
  intro a b c d hab hcd
  obtain ⟨q, hqa, hqb⟩ := htwo hab hcd
  obtain ⟨g, rfl⟩ := hf q
  exact ⟨g, hqa, hqb⟩

/-- A point stabilizer in a pulled-back action is the comap of the original
point stabilizer. -/
public theorem stabilizer_compHom
    {G : Type u} {Q : Type v} {Omega : Type*}
    [Group G] [Group Q] [MulAction Q Omega]
    (f : G →* Q) (alpha : Omega) :
    letI : MulAction G Omega := MulAction.compHom Omega f
    MulAction.stabilizer G alpha =
      (MulAction.stabilizer Q alpha).comap f := by
  letI : MulAction G Omega := MulAction.compHom Omega f
  ext g
  simp [MulAction.mem_stabilizer_iff, MulAction.compHom_smul_def]

/-- If the image of `B` has a doubly transitive coset action through a
surjective homomorphism whose kernel lies in `B`, then so does `B`. -/
public theorem coset_isTwoPretransitive_of_surjective
    {G : Type u} {Q : Type v} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f)
    (B : Subgroup G) (hker : f.ker ≤ B)
    (htwo : MulAction.IsMultiplyPretransitive Q (Q ⧸ B.map f) 2) :
    MulAction.IsMultiplyPretransitive G (G ⧸ B) 2 := by
  let Omega := Q ⧸ B.map f
  letI : MulAction G Omega := MulAction.compHom Omega f
  have htwo_pull : MulAction.IsMultiplyPretransitive G Omega 2 :=
    isTwoPretransitive_compHom_of_surjective f hf htwo
  have hstabilizer :
      MulAction.stabilizer G (QuotientGroup.mk 1 : Omega) = B := by
    calc
      MulAction.stabilizer G (QuotientGroup.mk 1 : Omega) =
          (MulAction.stabilizer Q
            (QuotientGroup.mk 1 : Omega)).comap f :=
        stabilizer_compHom f (QuotientGroup.mk 1 : Omega)
      _ = (B.map f).comap f := by
        rw [baseCoset_stabilizer (B.map f)]
      _ = B := Subgroup.comap_map_eq_self hker
  rw [← hstabilizer]
  exact quotient_stabilizer_isTwoPretransitive
    (QuotientGroup.mk 1 : Omega) htwo_pull

/-- Pull a coset action back across a group equivalence. -/
public theorem coset_isTwoPretransitive_of_mulEquiv
    {G : Type u} {Q : Type v} [Group G] [Group Q]
    (e : G ≃* Q) (B : Subgroup G)
    (htwo : MulAction.IsMultiplyPretransitive Q
      (Q ⧸ B.map e.toMonoidHom) 2) :
    MulAction.IsMultiplyPretransitive G (G ⧸ B) 2 := by
  apply coset_isTwoPretransitive_of_surjective
    e.toMonoidHom e.surjective B
  · rw [(MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective]
    exact bot_le
  · exact htwo

/-- Double transitivity on the cosets of the point stabilizer is equivalent
to the source-facing double transitivity statement on the actual orbit. -/
public theorem isTwoTransitiveOn_orbit_of_coset
    {X : Type u} {Omega : Type v} [Group X] [MulAction X Omega]
    (F : Subgroup X) (alpha : Omega)
    (htwo : MulAction.IsMultiplyPretransitive F
      (F ⧸ pointStabilizerIn F alpha) 2) :
    IsTwoTransitiveOn F {omega : Omega | InOrbit F alpha omega} := by
  letI : MulAction F Omega := MulAction.compHom Omega F.subtype
  have hstabilizer :
      MulAction.stabilizer F alpha = pointStabilizerIn F alpha := by
    rfl
  rw [← hstabilizer] at htwo
  rw [MulAction.is_two_pretransitive_iff] at htwo
  intro a b c d ha hb hc hd hab hcd
  rcases ha with ⟨fa, hfa⟩
  rcases hb with ⟨fb, hfb⟩
  rcases hc with ⟨fc, hfc⟩
  rcases hd with ⟨fd, hfd⟩
  let qa : F ⧸ MulAction.stabilizer F alpha := QuotientGroup.mk fa
  let qb : F ⧸ MulAction.stabilizer F alpha := QuotientGroup.mk fb
  let qc : F ⧸ MulAction.stabilizer F alpha := QuotientGroup.mk fc
  let qd : F ⧸ MulAction.stabilizer F alpha := QuotientGroup.mk fd
  have hqab : qa ≠ qb := by
    intro hq
    apply hab
    have himage := congrArg
      (MulAction.ofQuotientStabilizer F alpha) hq
    calc
      a = (fa : X) • alpha := hfa.symm
      _ = (fb : X) • alpha := by
        simpa [qa, qb, MulAction.compHom_smul_def] using himage
      _ = b := hfb
  have hqcd : qc ≠ qd := by
    intro hq
    apply hcd
    have himage := congrArg
      (MulAction.ofQuotientStabilizer F alpha) hq
    calc
      c = (fc : X) • alpha := hfc.symm
      _ = (fd : X) • alpha := by
        simpa [qc, qd, MulAction.compHom_smul_def] using himage
      _ = d := hfd
  obtain ⟨f, hfac, hfbd⟩ := htwo hqab hqcd
  refine ⟨f, ?_, ?_⟩
  · have himage :
        f • ((fa : F) • alpha) = (fc : F) • alpha := by
      calc
        f • ((fa : F) • alpha) =
            MulAction.ofQuotientStabilizer F alpha (f • qa) :=
          (MulAction.ofQuotientStabilizer_smul F alpha f qa).symm
        _ = MulAction.ofQuotientStabilizer F alpha qc := by rw [hfac]
        _ = (fc : F) • alpha := by rfl
    simpa [MulAction.compHom_smul_def, hfa, hfc] using himage
  · have himage :
        f • ((fb : F) • alpha) = (fd : F) • alpha := by
      calc
        f • ((fb : F) • alpha) =
            MulAction.ofQuotientStabilizer F alpha (f • qb) :=
          (MulAction.ofQuotientStabilizer_smul F alpha f qb).symm
        _ = MulAction.ofQuotientStabilizer F alpha qd := by rw [hfbd]
        _ = (fd : F) • alpha := by rfl
    simpa [MulAction.compHom_smul_def, hfb, hfd] using himage

/-- Pull a doubly transitive coset action of `F/N` back to the actual
`F`-orbit, provided `N` lies in the base-point stabilizer. -/
public theorem isTwoTransitiveOn_orbit_of_quotient_image
    {X : Type u} {Omega : Type v} [Group X] [MulAction X Omega]
    (F : Subgroup X) (alpha : Omega) (N : Subgroup F) [N.Normal]
    (hN : N ≤ pointStabilizerIn F alpha)
    (htwo : MulAction.IsMultiplyPretransitive (F ⧸ N)
      ((F ⧸ N) ⧸
        (pointStabilizerIn F alpha).map (QuotientGroup.mk' N)) 2) :
    IsTwoTransitiveOn F {omega : Omega | InOrbit F alpha omega} := by
  apply isTwoTransitiveOn_orbit_of_coset F alpha
  apply coset_isTwoPretransitive_of_surjective
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
      (pointStabilizerIn F alpha)
  · simpa using hN
  · exact htwo

/-- Regularity away from a fixed point descends to regularity on the
non-base cosets of its stabilizer. -/
public theorem regularOn_quotient_stabilizer
    {G : Type u} {Omega : Type v} [Group G] [MulAction G Omega]
    (R : Subgroup G) (alpha : Omega)
    (hreg : IsRegularOn R {omega : Omega | omega ≠ alpha}) :
    IsRegularOn R
      {q : G ⧸ MulAction.stabilizer G alpha |
        q ≠ QuotientGroup.mk 1} := by
  intro a b ha hb
  have ha' : MulAction.ofQuotientStabilizer G alpha a ≠ alpha := by
    intro h
    apply ha
    apply MulAction.injective_ofQuotientStabilizer G alpha
    simpa using h
  have hb' : MulAction.ofQuotientStabilizer G alpha b ≠ alpha := by
    intro h
    apply hb
    apply MulAction.injective_ofQuotientStabilizer G alpha
    simpa using h
  obtain ⟨r, hr, huniq⟩ := hreg ha' hb'
  refine ⟨r, ?_, ?_⟩
  · apply MulAction.injective_ofQuotientStabilizer G alpha
    rw [MulAction.ofQuotientStabilizer_smul]
    exact hr
  · intro s hs
    apply huniq s
    have hs' := congrArg (MulAction.ofQuotientStabilizer G alpha) hs
    simpa only [MulAction.ofQuotientStabilizer_smul] using hs'

/-- Regularity away from a fixed point transports along conjugation of both
the acting subgroup and the distinguished point. -/
public theorem regularOn_conjugate
    {G : Type u} {Omega : Type v} [Group G] [MulAction G Omega]
    (P P0 : Subgroup G) (g : G) (alpha : Omega)
    (hg : P.map (MulAut.conj g).toMonoidHom = P0)
    (hreg : IsRegularOn P0 {omega : Omega | omega ≠ alpha}) :
    IsRegularOn P {omega : Omega | omega ≠ g⁻¹ • alpha} := by
  intro a b ha hb
  have hga : g • a ≠ alpha := by
    intro h
    apply ha
    calc
      a = g⁻¹ • (g • a) := by simp
      _ = g⁻¹ • alpha := by rw [h]
  have hgb : g • b ≠ alpha := by
    intro h
    apply hb
    calc
      b = g⁻¹ • (g • b) := by simp
      _ = g⁻¹ • alpha := by rw [h]
  obtain ⟨r0, hr0, huniq0⟩ := hreg hga hgb
  let r0G : G := r0
  have hr0map : r0G ∈ P.map (MulAut.conj g).toMonoidHom := by
    rw [hg]
    exact r0.property
  rcases Subgroup.mem_map.mp hr0map with
    ⟨r, hrP, hgr⟩
  let rP : P := ⟨r, hrP⟩
  refine ⟨rP, ?_, ?_⟩
  · have hmove : g • ((rP : G) • a) = g • b := by
      calc
        g • ((rP : G) • a) = (g * r) • a := by rw [mul_smul]
        _ = ((g * r * g⁻¹) * g) • a := by
          congr 1
          group
        _ = (g * r * g⁻¹) • (g • a) := by rw [mul_smul]
        _ = (r0 : G) • (g • a) := by
          have hgr' : g * r * g⁻¹ = (r0 : G) := by
            simpa [MulAut.conj_apply, r0G] using hgr
          rw [hgr']
        _ = g • b := hr0
    calc
      (rP : G) • a = g⁻¹ • (g • ((rP : G) • a)) := by simp
      _ = g⁻¹ • (g • b) := by rw [hmove]
      _ = b := by simp
  · intro s hs
    have hgs_mem : g * (s : G) * g⁻¹ ∈ P0 := by
      rw [← hg]
      exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom s.property
    let s0 : P0 := ⟨g * (s : G) * g⁻¹, hgs_mem⟩
    have hs0 : (s0 : G) • (g • a) = g • b := by
      dsimp [s0]
      calc
        (g * (s : G) * g⁻¹) • (g • a) =
            g • ((s : G) • a) := by simp [mul_smul, mul_assoc]
        _ = g • b := by rw [hs]
    have hs0eq : s0 = r0 := huniq0 s0 hs0
    apply Subtype.ext
    have hconj : g * (s : G) * g⁻¹ =
        g * (rP : G) * g⁻¹ := by
      calc
        g * (s : G) * g⁻¹ = (s0 : G) := rfl
        _ = (r0 : G) := congrArg Subtype.val hs0eq
        _ = g * (rP : G) * g⁻¹ := by
          have hgr' : g * r * g⁻¹ = (r0 : G) := by
            simpa [MulAut.conj_apply, r0G] using hgr
          exact hgr'.symm
    have := congrArg (fun x : G => g⁻¹ * x * g) hconj
    simpa [mul_assoc] using this

/-- A subgroup of a point stabilizer that acts regularly on the complement,
viewed as `SubMulAction.ofStabilizer`, remains regular after mapping it into
the ambient group. -/
public theorem regularOn_compl_of_stabilizer_subgroup
    {G : Type u} {Omega : Type v} [Group G] [MulAction G Omega]
    (alpha : Omega) (F : Subgroup (MulAction.stabilizer G alpha))
    (hFregular : ∀ x y : SubMulAction.ofStabilizer G alpha,
      ∃! f : F, (f : MulAction.stabilizer G alpha) • x = y) :
    IsRegularOn
      (F.map (MulAction.stabilizer G alpha).subtype)
      {omega : Omega | omega ≠ alpha} := by
  let H := MulAction.stabilizer G alpha
  let X := SubMulAction.ofStabilizer G alpha
  intro a b ha hb
  let aX : X := ⟨a, ha⟩
  let bX : X := ⟨b, hb⟩
  obtain ⟨f, hf, huniq⟩ := hFregular aX bX
  have hfmap : (f : G) ∈ F.map H.subtype :=
    Subgroup.mem_map_of_mem H.subtype f.property
  let r : F.map H.subtype := ⟨(f : G), hfmap⟩
  refine ⟨r, ?_, ?_⟩
  · change (f : G) • a = b
    exact congrArg Subtype.val hf
  · intro s hs
    rcases Subgroup.mem_map.mp s.property with ⟨f', hf', hfs'⟩
    let f0 : F := ⟨f', hf'⟩
    have hf0 : (f0 : H) • aX = bX := by
      apply Subtype.ext
      change (f' : G) • a = b
      have hfsG : (f' : G) = (s : G) := hfs'
      rw [hfsG]
      exact hs
    have hfeq : f0 = f := huniq f0 hf0
    apply Subtype.ext
    change (s : G) = (f : G)
    calc
      (s : G) = (f' : G) := hfs'.symm
      _ = (f : G) :=
        congrArg (fun z : F => ((z : H) : G)) hfeq

/-- Pull regularity back across a group equivalence, using the action obtained
by composing with that equivalence. -/
public theorem regularOn_compHom_of_map_mulEquiv
    {G : Type u} {Q : Type v} {Omega : Type*}
    [Group G] [Group Q] [MulAction Q Omega]
    (e : G ≃* Q) (P : Subgroup G) (P0 : Subgroup Q)
    (hmap : P.map e.toMonoidHom = P0) (A : Set Omega)
    (hreg : IsRegularOn P0 A) :
    letI : MulAction G Omega := MulAction.compHom Omega e.toMonoidHom
    IsRegularOn P A := by
  letI : MulAction G Omega := MulAction.compHom Omega e.toMonoidHom
  intro a b ha hb
  obtain ⟨r0, hr0, huniq0⟩ := hreg ha hb
  have hr0map : (r0 : Q) ∈ P.map e.toMonoidHom := by
    rw [hmap]
    exact r0.property
  rcases Subgroup.mem_map.mp hr0map with ⟨r, hrP, her⟩
  let rP : P := ⟨r, hrP⟩
  refine ⟨rP, ?_, ?_⟩
  · change e r • a = b
    have her' : e r = (r0 : Q) := her
    rw [her']
    exact hr0
  · intro s hs
    have hs_mem : e (s : G) ∈ P0 := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem e.toMonoidHom s.property
    let s0 : P0 := ⟨e (s : G), hs_mem⟩
    have hs0 : (s0 : Q) • a = b := by
      change e (s : G) • a = b
      exact hs
    have hs0eq : s0 = r0 := huniq0 s0 hs0
    apply Subtype.ext
    apply e.injective
    calc
      e (s : G) = (s0 : Q) := rfl
      _ = (r0 : Q) := congrArg Subtype.val hs0eq
      _ = e r := her.symm

namespace IsBorelSubgroup

/-- The Borel property is invariant under group equivalence. -/
public theorem map_mulEquiv
    {G : Type u} {Q : Type v} [Group G] [Finite G]
    [Group Q] [Finite Q]
    {B : Subgroup G} (hB : IsBorelSubgroup B) (e : G ≃* Q) :
    IsBorelSubgroup (B.map e.toMonoidHom) := by
  rcases hB with ⟨hsolvable, P, hBnormalizer⟩
  constructor
  · let : Group.IsSolvable B := hsolvable
    exact Group.isSolvable_of_surjective
      (f := e.toMonoidHom.subgroupMap B)
      (MonoidHom.subgroupMap_surjective e.toMonoidHom B)
  · let Pmap : Sylow 2 Q :=
      P.mapSurjective (f := e.toMonoidHom) e.surjective
    refine ⟨Pmap, ?_⟩
    change B.map e.toMonoidHom =
      Subgroup.normalizer
        (((P : Subgroup G).map e.toMonoidHom : Subgroup Q) : Set Q)
    rw [hBnormalizer]
    exact Subgroup.map_equiv_normalizer_eq (P : Subgroup G) e

/-- If one Sylow `2`-normalizer is a point stabilizer, every Borel subgroup
is a point stabilizer in the same transitive action. -/
public theorem eq_stabilizer_of_sylow_normalizer
    {G : Type u} {Omega : Type v} [Group G] [Finite G]
    [MulAction G Omega]
    {B : Subgroup G} (hB : IsBorelSubgroup B)
    (P0 : Sylow 2 G) (alpha : Omega)
    (hnormalizer : Subgroup.normalizer ((P0 : Subgroup G) : Set G) =
      MulAction.stabilizer G alpha) :
    ∃ beta : Omega, B = MulAction.stabilizer G beta := by
  rcases hB with ⟨_hsolvable, P, rfl⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P P0
  refine ⟨g⁻¹ • alpha, ?_⟩
  rw [← rightConjugate_stabilizer alpha g, ← hnormalizer]
  have hPmap :
      (P0 : Subgroup G).map (MulAut.conj g).symm.toMonoidHom =
        (P : Subgroup G) := by
    apply (Subgroup.map_symm_eq_iff_map_eq
      (K := (P : Subgroup G)) (H := (P0 : Subgroup G))
        (e := MulAut.conj g)).2
    exact congrArg (fun Q : Sylow 2 G => (Q : Subgroup G)) hg
  calc
    Subgroup.normalizer ((P : Subgroup G) : Set G) =
        Subgroup.normalizer
          (((P0 : Subgroup G).map
            (MulAut.conj g).symm.toMonoidHom : Subgroup G) : Set G) := by
      rw [hPmap]
    _ = (Subgroup.normalizer ((P0 : Subgroup G) : Set G)).map
          (MulAut.conj g).symm.toMonoidHom :=
      (Subgroup.map_equiv_normalizer_eq
        (P0 : Subgroup G) (MulAut.conj g).symm).symm
    _ = rightConjugate
          (Subgroup.normalizer ((P0 : Subgroup G) : Set G)) g := by
      ext x
      simp [rightConjugate, Subgroup.conjBy,
        MulAut.conj_symm_apply]

/-- If a Sylow `2`-subgroup acts regularly away from a point and its
normalizer is the point stabilizer, every Borel subgroup has a normal Sylow
`2`-subgroup whose ambient image acts regularly on the non-base cosets. -/
public theorem exists_normal_sylow_regularOn_cosets_of_sylow_normalizer
    {G : Type u} [Group G] [Finite G]
    {Omega : Type v} [MulAction G Omega]
    {B : Subgroup G} (hB : IsBorelSubgroup B)
    (P0 : Sylow 2 G) (alpha : Omega)
    (hnormalizer : Subgroup.normalizer ((P0 : Subgroup G) : Set G) =
      MulAction.stabilizer G alpha)
    (hregular : IsRegularOn (P0 : Subgroup G)
      {omega : Omega | omega ≠ alpha}) :
    ∃ P : Sylow 2 B,
      (P : Subgroup B).Normal ∧
      IsRegularOn
        ((P : Subgroup B).map B.subtype)
        {q : G ⧸ B | q ≠ QuotientGroup.mk 1} := by
  rcases hB with ⟨_hsolvable, P, rfl⟩
  have hPle : (P : Subgroup G) ≤
      Subgroup.normalizer ((P : Subgroup G) : Set G) :=
    Subgroup.le_normalizer
  let PB : Sylow 2 (Subgroup.normalizer ((P : Subgroup G) : Set G)) :=
    P.subtype hPle
  have hPBnormal :
      (PB : Subgroup
        (Subgroup.normalizer ((P : Subgroup G) : Set G))).Normal := by
    rw [Sylow.coe_subtype]
    apply Subgroup.normal_subgroupOf_of_le_normalizer
    exact le_rfl
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P P0
  have hcoe :=
    congrArg (fun Q : Sylow 2 G => (Q : Subgroup G)) hg
  have hmap : (P : Subgroup G).map (MulAut.conj g).toMonoidHom =
      (P0 : Subgroup G) := by
    rw [← hcoe]
    rfl
  have hregP : IsRegularOn (P : Subgroup G)
      {omega : Omega | omega ≠ g⁻¹ • alpha} :=
    regularOn_conjugate (P : Subgroup G) (P0 : Subgroup G)
      g alpha hmap hregular
  have hBstab : Subgroup.normalizer ((P : Subgroup G) : Set G) =
      MulAction.stabilizer G (g⁻¹ • alpha) := by
    rw [← rightConjugate_stabilizer alpha g, ← hnormalizer]
    have hPmap :
        (P0 : Subgroup G).map (MulAut.conj g).symm.toMonoidHom =
          (P : Subgroup G) := by
      apply (Subgroup.map_symm_eq_iff_map_eq
        (K := (P : Subgroup G)) (H := (P0 : Subgroup G))
          (e := MulAut.conj g)).2
      exact hmap
    calc
      Subgroup.normalizer ((P : Subgroup G) : Set G) =
          Subgroup.normalizer
            (((P0 : Subgroup G).map
              (MulAut.conj g).symm.toMonoidHom : Subgroup G) : Set G) := by
        rw [hPmap]
      _ = (Subgroup.normalizer ((P0 : Subgroup G) : Set G)).map
          (MulAut.conj g).symm.toMonoidHom :=
        (Subgroup.map_equiv_normalizer_eq
          (P0 : Subgroup G) (MulAut.conj g).symm).symm
      _ = rightConjugate
          (Subgroup.normalizer ((P0 : Subgroup G) : Set G)) g := by
        ext x
        simp [rightConjugate, Subgroup.conjBy,
          MulAut.conj_symm_apply]
  have hregQ : IsRegularOn (P : Subgroup G)
      {q : G ⧸ Subgroup.normalizer ((P : Subgroup G) : Set G) |
        q ≠ QuotientGroup.mk 1} := by
    rw [hBstab]
    exact regularOn_quotient_stabilizer (P : Subgroup G)
      (g⁻¹ • alpha) hregP
  refine ⟨PB, hPBnormal, ?_⟩
  have hmapPB :
      (PB : Subgroup
        (Subgroup.normalizer ((P : Subgroup G) : Set G))).map
          (Subgroup.normalizer ((P : Subgroup G) : Set G)).subtype =
        (P : Subgroup G) := by
    rw [Sylow.coe_subtype]
    simpa [Subgroup.subgroupOf_map_subtype]
  rw [hmapPB]
  exact hregQ

/-- Pull a regular Sylow-normalizer model action across a group equivalence
and apply it to a Borel subgroup of the source group. -/
public theorem exists_normal_sylow_regularOn_cosets_of_mulEquiv
    {G : Type u} {Q : Type v} {Omega : Type*}
    [Group G] [Finite G] [Group Q] [Finite Q]
    [MulAction Q Omega]
    {B : Subgroup G} (hB : IsBorelSubgroup B) (e : G ≃* Q)
    (P0 : Sylow 2 Q) (alpha : Omega)
    (hnormalizer : Subgroup.normalizer ((P0 : Subgroup Q) : Set Q) =
      MulAction.stabilizer Q alpha)
    (hregular : IsRegularOn (P0 : Subgroup Q)
      {omega : Omega | omega ≠ alpha}) :
    ∃ P : Sylow 2 B,
      (P : Subgroup B).Normal ∧
      IsRegularOn ((P : Subgroup B).map B.subtype)
        {q : G ⧸ B | q ≠ QuotientGroup.mk 1} := by
  letI : MulAction G Omega := MulAction.compHom Omega e.toMonoidHom
  let P0G : Sylow 2 G :=
    P0.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hPmap : (P0G : Subgroup G).map e.toMonoidHom =
      (P0 : Subgroup Q) := by
    apply (Subgroup.map_symm_eq_iff_map_eq
      (K := (P0G : Subgroup G)) (H := (P0 : Subgroup Q))
        (e := e)).mp
    simp [P0G]
  have hnormalizerG :
      Subgroup.normalizer ((P0G : Subgroup G) : Set G) =
        MulAction.stabilizer G alpha := by
    apply (Subgroup.map_injective
      (f := e.toMonoidHom) e.injective)
    rw [Subgroup.map_equiv_normalizer_eq, hPmap, hnormalizer]
    rw [stabilizer_compHom]
    exact (Subgroup.map_comap_eq_self_of_surjective
      (f := e.toMonoidHom) e.surjective _).symm
  have hregularG : IsRegularOn (P0G : Subgroup G)
      {omega : Omega | omega ≠ alpha} :=
    regularOn_compHom_of_map_mulEquiv e (P0G : Subgroup G)
      (P0 : Subgroup Q) hPmap _ hregular
  exact hB.exists_normal_sylow_regularOn_cosets_of_sylow_normalizer
    P0G alpha hnormalizerG hregularG

/-- A doubly transitive model action with one Sylow normalizer as point
stabilizer induces the canonical doubly transitive action on the cosets of
every Borel subgroup. -/
public theorem coset_isTwoPretransitive_of_sylow_normalizer
    {G : Type u} {Omega : Type v} [Group G] [Finite G]
    [MulAction G Omega]
    {B : Subgroup G} (hB : IsBorelSubgroup B)
    (P0 : Sylow 2 G) (alpha : Omega)
    (hnormalizer : Subgroup.normalizer ((P0 : Subgroup G) : Set G) =
      MulAction.stabilizer G alpha)
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2) :
    MulAction.IsMultiplyPretransitive G (G ⧸ B) 2 := by
  obtain ⟨beta, hBstabilizer⟩ :=
    hB.eq_stabilizer_of_sylow_normalizer P0 alpha hnormalizer
  rw [hBstabilizer]
  exact quotient_stabilizer_isTwoPretransitive beta htwo

end IsBorelSubgroup

private theorem borel_card_pgl2
    {K : Type*} [Field K] [Finite K] :
    Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) =
      Nat.card K * (Nat.card K ^ 2 - 1) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  let GL2 := GL (Fin 2) K
  let PGL2 := Matrix.ProjGenLinGroup (Fin 2) K
  let centerGL := Subgroup.center GL2
  have hscalarInj : Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ → GL2) := by
    intro x y hxy
    apply Units.ext
    have h := congrArg (fun A : GL2 =>
      ((A : Matrix (Fin 2) (Fin 2) K) 0 0)) hxy
    simpa [Matrix.GeneralLinearGroup.scalar] using h
  have hcenter : Nat.card centerGL = Nat.card K - 1 := by
    dsimp [centerGL, GL2]
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    calc
      Nat.card (Matrix.GeneralLinearGroup.scalar (Fin 2)).range = Nat.card Kˣ :=
        (Nat.card_congr (Equiv.ofInjective
          (Matrix.GeneralLinearGroup.scalar (Fin 2)) hscalarInj)).symm
      _ = Nat.card K - 1 := by
        simpa [Nat.card_eq_fintype_card] using Fintype.card_units K
  have hGL : Nat.card GL2 =
      (Nat.card K ^ 2 - 1) * (Nat.card K ^ 2 - Nat.card K) := by
    simpa [GL2, Fin.prod_univ_two] using
      (Matrix.card_GL_field (𝔽 := K) 2)
  let mkPGL : GL2 →* PGL2 := Matrix.ProjGenLinGroup.mk
  have hrange : mkPGL.range = ⊤ :=
    MonoidHom.range_eq_top.mpr Matrix.ProjGenLinGroup.mk_surjective
  have hindex : centerGL.index = Nat.card PGL2 := by
    calc
      centerGL.index = mkPGL.ker.index := by
        rw [Matrix.ProjGenLinGroup.ker_mk]
      _ = Nat.card mkPGL.range := Subgroup.index_ker mkPGL
      _ = Nat.card PGL2 := by rw [hrange]; simp
  have hmul := centerGL.index_mul_card
  rw [hindex, hcenter, hGL] at hmul
  have hdiff : Nat.card K ^ 2 - Nat.card K =
      Nat.card K * (Nat.card K - 1) := by
    rw [pow_two]
    calc
      Nat.card K * Nat.card K - Nat.card K =
          Nat.card K * Nat.card K - Nat.card K * 1 := by simp
      _ = Nat.card K * (Nat.card K - 1) :=
        (Nat.mul_sub_left_distrib _ _ _).symm
  rw [hdiff] at hmul
  apply Nat.eq_of_mul_eq_mul_left
    (Nat.sub_pos_iff_lt.mpr (Finite.one_lt_card (α := K)))
  calc
    (Nat.card K - 1) * Nat.card PGL2 =
        Nat.card PGL2 * (Nat.card K - 1) := by ac_rfl
    _ = (Nat.card K ^ 2 - 1) *
        (Nat.card K * (Nat.card K - 1)) := hmul
    _ = (Nat.card K - 1) *
        (Nat.card K * (Nat.card K ^ 2 - 1)) := by ring

/-- In the natural projective action of `PGL(2, 2^n)`, a Sylow
`2`-subgroup has normalizer equal to a point stabilizer. -/
public theorem pgl_sylow_normalizer_action
    (n : ℕ) (hn : 2 ≤ n) :
    let K := BinaryGaloisField n
    let Omega := ℙ K (Fin 2 → K)
    let G := Matrix.ProjGenLinGroup (Fin 2) K
    ∃ (rho : G →* Equiv.Perm Omega) (pinf : Omega) (S : Sylow 2 G),
      (∀ (g : G) (z : Omega) (A : GL (Fin 2) K),
        Matrix.ProjGenLinGroup.mk A = g →
          rho g z =
            (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z) ∧
      Subgroup.normalizer ((S : Subgroup G) : Set G) =
        (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho ∧
      (∀ a b : Omega, a ≠ pinf → b ≠ pinf →
        ∃! s : S, rho (s : G) a = b) ∧
      (∀ a b c d : Omega, a ≠ b → c ≠ d →
        ∃ g : G, rho g a = c ∧ rho g b = d) := by
  let K := BinaryGaloisField n
  let q := 2 ^ n
  let Omega := ℙ K (Fin 2 → K)
  let G := Matrix.ProjGenLinGroup (Fin 2) K
  change ∃ (rho : G →* Equiv.Perm Omega) (pinf : Omega)
      (S : Sylow 2 G),
    (∀ (g : G) (z : Omega) (A : GL (Fin 2) K),
      Matrix.ProjGenLinGroup.mk A = g →
        rho g z =
          (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z) ∧
    Subgroup.normalizer ((S : Subgroup G) : Set G) =
      (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho ∧
    (∀ a b : Omega, a ≠ pinf → b ≠ pinf →
      ∃! s : S, rho (s : G) a = b) ∧
    (∀ a b c d : Omega, a ≠ b → c ≠ d →
      ∃ g : G, rho g a = c ∧ rho g b = d)
  classical
  letI : Fintype K := Fintype.ofFinite K
  letI : Finite G :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  have hn0 : n ≠ 0 := by omega
  have hKcard : Nat.card K = q := by
    simpa [K, q, BinaryGaloisField] using
      GaloisField.card 2 n hn0
  rcases External.huppert_blackburn_XI_example_1_3_a K with
    ⟨hOmegaCard, rho, iota, hrho, _hiota, hiota_apply, hrho_apply,
      _hiota_normal, _hiota_index, hsharp, hlarge,
      _hsmall_two, _hsmall_three⟩
  obtain ⟨rhoPSL, _hrhoPSL, hrhoPSL_apply, htwoPSL⟩ :=
    External.huppert_II_6_11_projective_action
      (K := K) 2 (by omega)
  have hcompat
      (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :
      rho (iota x) = rhoPSL x := by
    rcases QuotientGroup.mk'_surjective
        (Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) K)) x with
      ⟨A, rfl⟩
    apply Equiv.ext
    intro z
    rw [hiota_apply]
    rw [hrho_apply _ _ _ rfl, hrhoPSL_apply]
  letI : MulAction G Omega := MulAction.compHom Omega rho
  letI : FaithfulSMul G Omega :=
    faithfulSMul_iff.mpr (by
      intro g hg
      apply hrho
      apply Equiv.ext
      intro z
      have hgz := hg z
      change rho g z = z at hgz
      calc
        rho g z = z := hgz
        _ = rho 1 z := by rw [map_one]; rfl)
  have htwo : MulAction.IsMultiplyPretransitive G Omega 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    rcases htwoPSL a b c d hab hcd with ⟨x, hxa, hxb⟩
    refine ⟨iota x, ?_, ?_⟩
    · change rho (iota x) a = c
      rw [hcompat]
      exact hxa
    · change rho (iota x) b = d
      rw [hcompat]
      exact hxb
  have hat_most_two :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
          ¬ (g • a = a ∧ g • b = b ∧ g • c = c) := by
    intro g hg a b c hab hac hbc hfix
    have hu := hsharp a b c a b c hab hac hbc hab hac hbc
    apply hg
    change rho g a = a ∧ rho g b = b ∧ rho g c = c at hfix
    have hone_fix :
        rho (1 : G) a = a ∧
          rho (1 : G) b = b ∧ rho (1 : G) c = c := by
      rw [map_one]
      exact ⟨rfl, rfl, rfl⟩
    exact hu.unique hfix hone_fix
  have hq_ge_four : 4 ≤ q := by
    simpa [q] using
      (Nat.pow_le_pow_right (n := 2) (by omega) hn)
  have hKgt : 3 < Nat.card K := by omega
  rcases hlarge hKgt with
    ⟨_hsimple, _hnoncommutative, hno_regular⟩
  letI : Fintype Omega := Fintype.ofFinite Omega
  have hdegree : Fintype.card Omega = q + 1 := by
    rw [← Nat.card_eq_fintype_card, hOmegaCard, hKcard]
  have hdegree_gt_one : 1 < Fintype.card Omega := by
    rw [hdegree]
    omega
  obtain ⟨pinf, b, hpinf_b⟩ :=
    Fintype.one_lt_card_iff.mp hdegree_gt_one
  have hno_regular' :
      ¬ ∃ R : Subgroup G,
        R.Normal ∧ R ≠ ⊥ ∧
          ∀ x y : Omega, ∃! r : R, (r : G) • x = y := by
    intro h
    apply hno_regular
    rcases h with ⟨R, hRnormal, hRne, hRregular⟩
    refine ⟨R, hRnormal, hRne, ?_⟩
    intro x y
    rcases hRregular x y with ⟨r, hr, hr_unique⟩
    refine ⟨r, ?_, ?_⟩
    · change rho (r : G) x = y
      exact hr
    · intro s hs
      apply hr_unique s
      change rho (s : G) x = y at hs
      exact hs
  obtain ⟨F, hFrob⟩ :=
    External.huppert_blackburn_XI_pointStabilizer_frobeniusKernel_exists
      htwo hat_most_two hno_regular' pinf b hpinf_b
  have hFcard : Nat.card F = q :=
    External.huppert_blackburn_XI_pointStabilizer_frobeniusKernel_card
      q hdegree htwo pinf b hpinf_b F hFrob
  let H := MulAction.stabilizer G pinf
  let R : Subgroup G := F.map H.subtype
  let X := SubMulAction.ofStabilizer G pinf
  letI : MulAction.IsPretransitive G Omega :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have hstab_multi : MulAction.IsMultiplyPretransitive H X 1 :=
    (SubMulAction.ofStabilizer.isMultiplyPretransitive
      (G := G) (a := pinf)).mp htwo
  letI : MulAction.IsPretransitive H X :=
    (MulAction.is_one_pretransitive_iff (G := H) (α := X)).mp hstab_multi
  have hFregular : ∀ x y : X, ∃! f : F, (f : H) • x = y :=
    External.huppert_blackburn_XI_regular_of_isComplement_stabilizer
      hFrob.isComplement'
        (inferInstance : MulAction.IsPretransitive H X)
  have hRregular : IsRegularOn R
      {omega : Omega | omega ≠ pinf} :=
    regularOn_compl_of_stabilizer_subgroup pinf F hFregular
  have hRcard : Nat.card R = q := by
    calc
      Nat.card R = Nat.card F :=
        Subgroup.card_map_of_injective H.subtype_injective
      _ = q := hFcard
  have hRp : IsPGroup 2 R :=
    IsPGroup.of_card (by simpa [q] using hRcard)
  have hnormalizer :
      Subgroup.normalizer (R : Set G) = MulAction.stabilizer G pinf := by
    have hRle : R ≤ MulAction.stabilizer G pinf := by
      change R ≤ H
      apply Subgroup.map_le_iff_le_comap.mpr
      intro f hf
      exact f.property
    have hRne : R ≠ ⊥ := by
      intro hRbot
      change F.map H.subtype = (⊥ : Subgroup G) at hRbot
      have hFbot : F = ⊥ := by
        exact (Subgroup.map_eq_bot_iff_of_injective F
          H.subtype_injective).mp hRbot
      have hFcard_one : Nat.card F = 1 := by
        rw [hFbot, Subgroup.card_bot]
      have : q = 1 := hFcard.symm.trans hFcard_one
      omega
    have hHle : H ≤ Subgroup.normalizer (R : Set G) := by
      have hmap := Subgroup.le_normalizer_map (H := F) H.subtype
      rw [Subgroup.normalizer_eq_top_iff.mpr hFrob.normal] at hmap
      change H ≤ Subgroup.normalizer (F.map H.subtype : Set G)
      have htop : (⊤ : Subgroup H).map H.subtype = H := by
        ext g
        constructor
        · rintro ⟨h, _, rfl⟩
          exact h.property
        · intro hg
          exact ⟨⟨g, hg⟩, trivial, rfl⟩
      rw [htop] at hmap
      exact hmap
    exact normalizer_eq_stabilizer_of_regular_compl R pinf hRle hRne
      hRregular hHle
  have hGcard : Nat.card G = q * (q ^ 2 - 1) := by
    change Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) =
      q * (q ^ 2 - 1)
    rw [borel_card_pgl2, hKcard]
  have hqpos : 0 < q := by positivity
  have hRindex : R.index = q ^ 2 - 1 := by
    apply Nat.eq_of_mul_eq_mul_left hqpos
    calc
      q * R.index = Nat.card R * R.index := by rw [hRcard]
      _ = Nat.card G := R.card_mul_index
      _ = q * (q ^ 2 - 1) := hGcard
  have hq_even : Even q := by
    dsimp only [q]
    exact Nat.even_pow.mpr ⟨even_two, hn0⟩
  have hq_sq_even : Even (q ^ 2) :=
    hq_even.pow_of_ne_zero (by norm_num)
  have hq_sq_pos : 0 < q ^ 2 := pow_pos hqpos 2
  have hq_sq_sub_one_odd : Odd (q ^ 2 - 1) :=
    Nat.Even.sub_odd hq_sq_pos hq_sq_even odd_one
  have hRindex_not : ¬ 2 ∣ R.index := by
    rw [hRindex]
    intro htwo_dvd
    exact (Nat.not_even_iff_odd.mpr hq_sq_sub_one_odd)
      (even_iff_two_dvd.mpr htwo_dvd)
  let S : Sylow 2 G := hRp.toSylow hRindex_not
  have hSR : (S : Subgroup G) = R := rfl
  have hSnormalizer :
      Subgroup.normalizer ((S : Subgroup G) : Set G) =
        (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho := by
    rw [hSR, hnormalizer]
    ext g
    rw [MulAction.mem_stabilizer_iff]
    rfl
  have hSregular : IsRegularOn (S : Subgroup G)
      {omega : Omega | omega ≠ pinf} := by
    rw [hSR]
    exact hRregular
  have hSregular_rho :
      ∀ a b : Omega, a ≠ pinf → b ≠ pinf →
        ∃! s : S, rho (s : G) a = b := by
    intro a b ha hb
    exact hSregular ha hb
  have htwo_rho :
      ∀ a b c d : Omega, a ≠ b → c ≠ d →
        ∃ g : G, rho g a = c ∧ rho g b = d := by
    rw [MulAction.is_two_pretransitive_iff] at htwo
    intro a b c d hab hcd
    exact htwo hab hcd
  exact ⟨rho, pinf, S, hrho_apply, hSnormalizer,
    hSregular_rho, htwo_rho⟩

/-- Over a binary field, the natural inclusion `PSL(2,K) -> PGL(2,K)` is
an equivalence. -/
public theorem psl_charTwo_equiv_pgl
    (n : ℕ) (hn : 0 < n) :
    let K := BinaryGaloisField n
    Nonempty
      (PSL2BinaryMatrixGroup n ≃*
        Matrix.ProjGenLinGroup (Fin 2) K) := by
  let K := BinaryGaloisField n
  change Nonempty
    (PSL2MatrixGroup K ≃*
      Matrix.ProjGenLinGroup (Fin 2) K)
  classical
  letI : Fintype K := Fintype.ofFinite K
  letI : Finite (Matrix.ProjGenLinGroup (Fin 2) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  have hKcard : Nat.card K = 2 ^ n := by
    simpa [K, BinaryGaloisField] using
      GaloisField.card 2 n (Nat.ne_of_gt hn)
  have htwozero : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hneg_one : (-1 : K) = 1 := by
    apply (neg_eq_iff_add_eq_zero).2
    rw [show (1 : K) + 1 = 2 by norm_num, htwozero]
  have hcenter :
      Nat.card
          (Subgroup.center
            (Matrix.SpecialLinearGroup (Fin 2) K)) = 1 :=
    External.huppert614_card_center_of_neg_one_eq_one hneg_one
  have hPSLcard := External.huppert614_card_psl_mul_center (K := K)
  rw [hcenter, mul_one] at hPSLcard
  have hPSLPGLcard :
      Nat.card (PSL2MatrixGroup K) =
        Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) :=
    hPSLcard.trans (borel_card_pgl2 (K := K)).symm
  obtain ⟨_, _, iota, _, hiota, _⟩ :=
    External.huppert_blackburn_XI_example_1_3_a K
  exact ⟨MulEquiv.ofBijective iota
    ((Nat.bijective_iff_injective_and_card iota).2
      ⟨hiota, hPSLPGLcard⟩)⟩

/-- Every Borel subgroup of `PSL(2,2^n)` has a doubly transitive left-coset
action. -/
public theorem IsBorelSubgroup.psl_coset_isTwoPretransitive
    (n : ℕ) (hn : 2 ≤ n)
    {B : Subgroup (PSL2BinaryMatrixGroup n)}
    (hB : IsBorelSubgroup B) :
    MulAction.IsMultiplyPretransitive
      (PSL2BinaryMatrixGroup n) (PSL2BinaryMatrixGroup n ⧸ B) 2 := by
  let K := BinaryGaloisField n
  let Omega := ℙ K (Fin 2 → K)
  let Q := Matrix.ProjGenLinGroup (Fin 2) K
  letI : Finite Q :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let e : PSL2BinaryMatrixGroup n ≃* Q :=
    (psl_charTwo_equiv_pgl n (by omega)).some
  apply coset_isTwoPretransitive_of_mulEquiv e B
  have hBQ : IsBorelSubgroup (B.map e.toMonoidHom) :=
    hB.map_mulEquiv e
  rcases pgl_sylow_normalizer_action n hn with
    ⟨rho, pinf, S, _hrho_apply, hnormalizer, _hregular, htwo⟩
  letI : MulAction Q Omega := MulAction.compHom Omega rho
  have hnormalizer' :
      Subgroup.normalizer ((S : Subgroup Q) : Set Q) =
        MulAction.stabilizer Q pinf := by
    calc
      Subgroup.normalizer ((S : Subgroup Q) : Set Q) =
          (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho :=
        hnormalizer
      _ = MulAction.stabilizer Q pinf := by
        ext g
        change (rho g) pinf = pinf ↔ (rho g) pinf = pinf
        rfl
  have htwo' : MulAction.IsMultiplyPretransitive Q Omega 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    exact htwo a b c d hab hcd
  exact hBQ.coset_isTwoPretransitive_of_sylow_normalizer
    S pinf hnormalizer' htwo'

/-- The PSL alternative in Bender recognition supplies a doubly transitive
Borel coset action after transport through the recognizing equivalence. -/
public theorem IsBorelSubgroup.coset_isTwoPretransitive_of_isPSL2_model
    {G : Type u} [Group G] [Finite G] {B : Subgroup G}
    (hB : IsBorelSubgroup B)
    (hmodel : ∃ n : ℕ, 2 ≤ n ∧
      Nonempty (G ≃* PSL2BinaryMatrixGroup n)) :
    MulAction.IsMultiplyPretransitive G (G ⧸ B) 2 := by
  rcases hmodel with ⟨n, hn, e⟩
  let eG : G ≃* PSL2BinaryMatrixGroup n := e.some
  apply coset_isTwoPretransitive_of_mulEquiv eG B
  exact IsBorelSubgroup.psl_coset_isTwoPretransitive
    n hn (hB.map_mulEquiv eG)

/-- In the natural unitary action, the root subgroup from Huppert II.10.12
has normalizer exactly the isotropic-point stabilizer.  This isolates the
remaining model-specific Sylow calculation from the action argument. -/
public theorem psu_root_normalizer_action
    {K : Type u} [Field K] [Finite K]
    (J : HermitianForm 3 K) (q : ℕ)
    (hKcard : Nat.card K = q ^ 2)
    (hfixed_card : Nat.card {x : K // J.conj x = x} = q)
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hq : 1 < q) :
    let P := ℙ K (Fin 3 → K)
    let A : Set P :=
      {x | ∃ (v : Fin 3 → K) (hv : v ≠ 0),
        x = Projectivization.mk K v hv ∧
          dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
    let Omega := {x : P // x ∈ A}
    let G := ProjectiveSpecialUnitaryMatrixGroup J
    ∃ (rho : G →* Equiv.Perm Omega) (pinf : Omega) (R : Subgroup G),
      Function.Injective rho ∧
      Nat.card R = q ^ 3 ∧
      Subgroup.normalizer (R : Set G) =
        (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho ∧
      (∀ a b c d : Omega, a ≠ b → c ≠ d →
        ∃ g : G, rho g a = c ∧ rho g b = d) := by
  let P := ℙ K (Fin 3 → K)
  let A : Set P :=
    {x | ∃ (v : Fin 3 → K) (hv : v ≠ 0),
      x = Projectivization.mk K v hv ∧
        dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
  let Omega := {x : P // x ∈ A}
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  change ∃ (rho : G →* Equiv.Perm Omega) (pinf : Omega)
      (R : Subgroup G),
    Function.Injective rho ∧
    Nat.card R = q ^ 3 ∧
    Subgroup.normalizer (R : Set G) =
      (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho ∧
    (∀ a b c d : Omega, a ≠ b → c ≠ d →
      ∃ g : G, rho g a = c ∧ rho g b = d)
  rcases External.huppert_II_10_12 J q hKcard hfixed_card hJstandard with
    ⟨_hOmegaCard, rho, pinf, hrho, _hnatural, _hUcard,
      hroot, htwo, _hGcard, _hthree⟩
  rcases hroot with
    ⟨R, H, hR_le_U, _hH_le_U, hU_le_normalizer_R,
      _hR_disjoint_H, _hR_sup_H, _hH_cyclic, hRcard,
      _hcommutator_center, _hcommutator_card, _hHcard,
      hRregular, _hcoordR, _hHcoord, _hHcoord_surjective⟩
  letI : MulAction G Omega := MulAction.compHom Omega rho
  have hR_ne : R ≠ ⊥ := by
    intro hRbot
    have hRcard_one : Nat.card R = 1 := by
      rw [hRbot, Subgroup.card_bot]
    have hqcube_one : q ^ 3 = 1 := hRcard.symm.trans hRcard_one
    have hq_one : q = 1 :=
      (pow_eq_one_iff_left (by norm_num : (3 : ℕ) ≠ 0)).mp hqcube_one
    omega
  have hnormalizer :
      Subgroup.normalizer (R : Set G) = MulAction.stabilizer G pinf :=
    normalizer_eq_stabilizer_of_regular_compl R pinf hR_le_U hR_ne
      hRregular hU_le_normalizer_R
  exact ⟨rho, pinf, R, hrho, hRcard, hnormalizer, htwo⟩

/-- For `q = 2^n`, the root subgroup in the natural unitary action is a
Sylow `2`-subgroup, and its normalizer is the isotropic-point stabilizer. -/
public theorem psu_sylow_normalizer_action
    {K : Type u} [Field K] [Finite K]
    (J : HermitianForm 3 K) (n : ℕ) (hn : 2 ≤ n)
    (hKcard : Nat.card K = (2 ^ n) ^ 2)
    (hfixed_card : Nat.card {x : K // J.conj x = x} = 2 ^ n)
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    let q := 2 ^ n
    let P := ℙ K (Fin 3 → K)
    let A : Set P :=
      {x | ∃ (v : Fin 3 → K) (hv : v ≠ 0),
        x = Projectivization.mk K v hv ∧
          dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
    let Omega := {x : P // x ∈ A}
    let G := ProjectiveSpecialUnitaryMatrixGroup J
    ∃ (rho : G →* Equiv.Perm Omega) (pinf : Omega) (S : Sylow 2 G),
      Function.Injective rho ∧
      (∀ g : G, ∀ z : Omega, ∀ M : J.specialSubgroup,
        Matrix.ProjGenLinGroup.mk (M : GL (Fin 3) K) =
            (g : Matrix.ProjGenLinGroup (Fin 3) K) →
          ((rho g z : Omega) : P) =
            (Matrix.GeneralLinearGroup.toLin
              (M : GL (Fin 3) K)).toLinearEquiv • (z : P)) ∧
      Nat.card S = q ^ 3 ∧
      Subgroup.normalizer ((S : Subgroup G) : Set G) =
        (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho ∧
      (∀ a b : Omega, a ≠ pinf → b ≠ pinf →
        ∃! s : S, rho (s : G) a = b) ∧
      (∀ a b c d : Omega, a ≠ b → c ≠ d →
        ∃ g : G, rho g a = c ∧ rho g b = d) := by
  let q := 2 ^ n
  let P := ℙ K (Fin 3 → K)
  let A : Set P :=
    {x | ∃ (v : Fin 3 → K) (hv : v ≠ 0),
      x = Projectivization.mk K v hv ∧
        dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
  let Omega := {x : P // x ∈ A}
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  change ∃ (rho : G →* Equiv.Perm Omega) (pinf : Omega)
      (S : Sylow 2 G),
    Function.Injective rho ∧
    (∀ g : G, ∀ z : Omega, ∀ M : J.specialSubgroup,
      Matrix.ProjGenLinGroup.mk (M : GL (Fin 3) K) =
          (g : Matrix.ProjGenLinGroup (Fin 3) K) →
        ((rho g z : Omega) : P) =
          (Matrix.GeneralLinearGroup.toLin
            (M : GL (Fin 3) K)).toLinearEquiv • (z : P)) ∧
    Nat.card S = q ^ 3 ∧
    Subgroup.normalizer ((S : Subgroup G) : Set G) =
      (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho ∧
    (∀ a b : Omega, a ≠ pinf → b ≠ pinf →
      ∃! s : S, rho (s : G) a = b) ∧
    (∀ a b c d : Omega, a ≠ b → c ≠ d →
      ∃ g : G, rho g a = c ∧ rho g b = d)
  rcases External.huppert_II_10_12 J q
      (by simpa [q] using hKcard)
      (by simpa [q] using hfixed_card) hJstandard with
    ⟨_hOmegaCard, rho, pinf, hrho, hnatural, _hUcard,
      hroot, htwo, _hGcard, _hthree⟩
  rcases hroot with
    ⟨R, H, hR_le_U, hH_le_U, hU_le_normalizer_R,
      hR_disjoint_H, hR_sup_H, _hH_cyclic, hRcard,
      _hcommutator_center, _hcommutator_card, hHcard,
      hRregular, _hcoordR, _hHcoord, _hHcoord_surjective⟩
  letI : Fintype K := Fintype.ofFinite K
  letI : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  letI : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective
      (fun x : ProjectiveSpecialUnitaryMatrixGroup J =>
        (x : Matrix.ProjGenLinGroup (Fin 3) K)) Subtype.coe_injective
  have hq : 1 < q := by
    dsimp [q]
    exact one_lt_pow₀ (by norm_num) (by omega)
  have hRpower : Nat.card R = 2 ^ (n * 3) := by
    simpa [q, pow_mul] using hRcard
  have hRp : IsPGroup 2 R := IsPGroup.of_card hRpower
  have hq_even : Even q := by
    dsimp [q]
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hq_sq_even : Even (q ^ 2) :=
    hq_even.pow_of_ne_zero (by norm_num)
  have hq_sq_pos : 0 < q ^ 2 :=
    pow_pos (by omega) 2
  have hq_sq_sub_one_odd : Odd (q ^ 2 - 1) :=
    Nat.Even.sub_odd hq_sq_pos hq_sq_even odd_one
  have hgcd_dvd : Nat.gcd (q + 1) 3 ∣ q ^ 2 - 1 := by
    have hfactor : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      simpa [mul_comm] using Nat.sq_sub_sq q 1
    rw [hfactor]
    exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left (q + 1) 3) _
  have hHodd : Odd (Nat.card H) := by
    rw [hHcard]
    exact Odd.of_dvd_nat hq_sq_sub_one_odd
      (Nat.div_dvd_of_dvd hgcd_dvd)
  have hHnot : ¬ 2 ∣ Nat.card H := by
    intro htwo_dvd
    exact (Nat.not_even_iff_odd.mpr hHodd)
      (even_iff_two_dvd.mpr htwo_dvd)
  obtain ⟨PU, hPU⟩ :=
    exists_sylow_map_eq_of_normal_complement
      hR_le_U hH_le_U hU_le_normalizer_R
      hR_disjoint_H hR_sup_H hRp hHnot
  letI : MulAction G Omega := MulAction.compHom Omega rho
  have hR_ne : R ≠ ⊥ := by
    intro hRbot
    have hRcard_one : Nat.card R = 1 := by rw [hRbot]; simp
    have hqcube_one : q ^ 3 = 1 := hRcard.symm.trans hRcard_one
    have hq_one : q = 1 :=
      (pow_eq_one_iff_left (by norm_num : (3 : ℕ) ≠ 0)).mp hqcube_one
    omega
  have hnormalizer :
      Subgroup.normalizer (R : Set G) = MulAction.stabilizer G pinf :=
    normalizer_eq_stabilizer_of_regular_compl R pinf hR_le_U hR_ne
      hRregular hU_le_normalizer_R
  have hnormalizer_le :
      Subgroup.normalizer
          (((PU : Subgroup _).map
            ((MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho).subtype :
              Subgroup G) : Set G) ≤
        (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho := by
    rw [hPU]
    have hstab :
        (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho =
          MulAction.stabilizer G pinf := by
      ext g
      change (rho g) pinf = pinf ↔ (rho g) pinf = pinf
      rfl
    rw [hstab]
    exact hnormalizer.le
  obtain ⟨S, hSmap⟩ :=
    exists_sylow_map_eq_of_normalizer_le PU hnormalizer_le
  have hSR : (S : Subgroup G) = R := hSmap.trans hPU
  have hScard : Nat.card S = q ^ 3 := by
    change Nat.card (S : Subgroup G) = q ^ 3
    rw [hSR]
    exact hRcard
  have hSnormalizer :
      Subgroup.normalizer ((S : Subgroup G) : Set G) =
        (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho := by
    rw [hSR]
    exact hnormalizer
  have hSregular : IsRegularOn (S : Subgroup G)
      {omega : Omega | omega ≠ pinf} := by
    rw [hSR]
    exact hRregular
  have hSregular_rho :
      ∀ a b : Omega, a ≠ pinf → b ≠ pinf →
        ∃! s : S, rho (s : G) a = b := by
    intro a b ha hb
    exact hSregular ha hb
  exact
    ⟨rho, pinf, S, hrho, hnatural, hScard, hSnormalizer,
      hSregular_rho, htwo⟩

/-- Every Borel subgroup of `PSU(3, (2^n)^2)` has a doubly transitive
left-coset action. -/
public theorem IsBorelSubgroup.psu_coset_isTwoPretransitive
    {K : Type u} [Field K] [Finite K]
    (J : HermitianForm 3 K) (n : ℕ) (hn : 2 ≤ n)
    [Finite (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hKcard : Nat.card K = (2 ^ n) ^ 2)
    (hfixed_card : Nat.card {x : K // J.conj x = x} = 2 ^ n)
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {B : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hB : IsBorelSubgroup B) :
    MulAction.IsMultiplyPretransitive
      (ProjectiveSpecialUnitaryMatrixGroup J)
      (ProjectiveSpecialUnitaryMatrixGroup J ⧸ B) 2 := by
  let q := 2 ^ n
  let P := ℙ K (Fin 3 → K)
  let A : Set P :=
    {x | ∃ (v : Fin 3 → K) (hv : v ≠ 0),
      x = Projectivization.mk K v hv ∧
        dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
  let Omega := {x : P // x ∈ A}
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  change MulAction.IsMultiplyPretransitive G (G ⧸ B) 2
  have hdata :
      ∃ (rho : G →* Equiv.Perm Omega) (pinf : Omega) (S : Sylow 2 G),
        Function.Injective rho ∧
        Nat.card S = q ^ 3 ∧
        Subgroup.normalizer ((S : Subgroup G) : Set G) =
          (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho ∧
        (∀ a b : Omega, a ≠ pinf → b ≠ pinf →
          ∃! s : S, rho (s : G) a = b) ∧
          (∀ a b c d : Omega, a ≠ b → c ≠ d →
            ∃ g : G, rho g a = c ∧ rho g b = d) := by
    rcases psu_sylow_normalizer_action
        J n hn hKcard hfixed_card hJstandard with
      ⟨rho, pinf, S, hrho, _hnatural, hScard, hnormalizer,
        hregular, htwo⟩
    exact ⟨rho, pinf, S, hrho, hScard, hnormalizer,
      hregular, htwo⟩
  rcases hdata with
    ⟨rho, pinf, S, _hrho, _hScard, hnormalizer, _hregular, htwo⟩
  letI : MulAction G Omega := MulAction.compHom Omega rho
  have hnormalizer' :
      Subgroup.normalizer ((S : Subgroup G) : Set G) =
        MulAction.stabilizer G pinf := by
    calc
      Subgroup.normalizer ((S : Subgroup G) : Set G) =
          (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho :=
        hnormalizer
      _ = MulAction.stabilizer G pinf := by
        ext g
        change (rho g) pinf = pinf ↔ (rho g) pinf = pinf
        rfl
  have htwo' : MulAction.IsMultiplyPretransitive G Omega 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    exact htwo a b c d hab hcd
  exact hB.coset_isTwoPretransitive_of_sylow_normalizer
    S pinf hnormalizer' htwo'

/-- The PSU alternative in Bender recognition supplies a doubly transitive
Borel coset action after transport through the recognizing equivalence. -/
public theorem IsBorelSubgroup.coset_isTwoPretransitive_of_isPSU3_model
    {G : Type u} [Group G] [Finite G] {B : Subgroup G}
    (hB : IsBorelSubgroup B)
    (hmodel : ∃ n : ℕ, 2 ≤ n ∧
      ∃ (E : Type) (_ : Field E) (_ : Finite E)
          (J : HermitianForm 3 E),
        J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
        Nat.card E = (2 ^ n) ^ 2 ∧
        Nat.card {z : E // J.conj z = z} = 2 ^ n ∧
        Nonempty (G ≃* ProjectiveSpecialUnitaryMatrixGroup J)) :
    MulAction.IsMultiplyPretransitive G (G ⧸ B) 2 := by
  rcases hmodel with
    ⟨n, hn, E, hEfield, hEfinite, J, hJstandard,
      hEcard, hfixed_card, e⟩
  letI : Field E := hEfield
  letI : Finite E := hEfinite
  let eG : G ≃* ProjectiveSpecialUnitaryMatrixGroup J := e.some
  letI : Fintype E := Fintype.ofFinite E
  letI : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  letI : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective
      (fun x : ProjectiveSpecialUnitaryMatrixGroup J =>
        (x : Matrix.ProjGenLinGroup (Fin 3) E)) Subtype.coe_injective
  apply coset_isTwoPretransitive_of_mulEquiv eG B
  exact IsBorelSubgroup.psu_coset_isTwoPretransitive
    J n hn hEcard hfixed_card hJstandard (hB.map_mulEquiv eG)

/-- In the natural Suzuki ovoid action, a Sylow `2`-subgroup has normalizer
equal to the distinguished point stabilizer. -/
public theorem suzuki_sylow_normalizer_action
    (m : ℕ) (hm : 0 < m) :
    let K := BinaryGaloisField (2 * m + 1)
    let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) :=
      {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
    let Omega := {z : ℙ K (Fin 4 → K) // z ∈ O}
    let G := SuzukiMatrixGroup m
    ∃ (rho : G →* Equiv.Perm Omega) (pinfO : Omega) (S : Sylow 2 G),
      (∀ g : G, ∀ z : Omega,
        ((rho g z : Omega) : ℙ K (Fin 4 → K)) =
          (Matrix.GeneralLinearGroup.toLin
            (g : GL (Fin 4) K)).toLinearEquiv •
              (z : ℙ K (Fin 4 → K))) ∧
      Subgroup.normalizer ((S : Subgroup G) : Set G) =
        (MulAction.stabilizer (Equiv.Perm Omega) pinfO).comap rho ∧
      (∀ a b : Omega, a ≠ pinfO → b ≠ pinfO →
        ∃! s : S, rho (s : G) a = b) ∧
      (∀ a b c d : Omega, a ≠ b → c ≠ d →
        ∃ g : G, rho g a = c ∧ rho g b = d) := by
  let K := BinaryGaloisField (2 * m + 1)
  let q := 2 ^ (2 * m + 1)
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
  have hpi : ∀ x : K, pi x = x ^ (2 ^ (m + 1)) := by
    intro x
    exact iterateFrobeniusEquiv_def K 2 (m + 1) x
  have hpi_sq : ∀ x : K, pi (pi x) = x ^ 2 :=
    External.binaryGaloisField_tits_formula_sq m pi hpi
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let O : Set (ℙ K (Fin 4 → K)) :=
    {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
  let Omega := {z : ℙ K (Fin 4 → K) // z ∈ O}
  let G := SuzukiMatrixGroup m
  change ∃ (rho : G →* Equiv.Perm Omega) (pinfO : Omega)
      (S : Sylow 2 G),
    (∀ g : G, ∀ z : Omega,
      ((rho g z : Omega) : ℙ K (Fin 4 → K)) =
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv •
            (z : ℙ K (Fin 4 → K))) ∧
    Subgroup.normalizer ((S : Subgroup G) : Set G) =
      (MulAction.stabilizer (Equiv.Perm Omega) pinfO).comap rho ∧
    (∀ a b : Omega, a ≠ pinfO → b ≠ pinfO →
      ∃! s : S, rho (s : G) a = b) ∧
    (∀ a b c d : Omega, a ≠ b → c ≠ d →
      ∃ g : G, rho g a = c ∧ rho g b = d)
  let F : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
  let H : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ x : Kˣ, A = SuzukiTorusGL m x}
  rcases External.huppert_blackburn_XI_3_1 m hm pi hpi_sq with
    ⟨_hpi_unique, hpi_formula, hFp, _hF_pow_four,
      _hF_order_four, _hF_class, hFcard, _hF_typeA, _hroot_mul,
      _hcommutator, _hcommutator_coordinates, htorus_equiv,
      _htorus_conjugation, hdisjoint, _hfixed_point_free⟩
  rcases htorus_equiv with ⟨eH, _heH⟩
  rcases External.huppert_blackburn_XI_3_3 m hm pi hpi with
    ⟨hpres, _hrecognition, _hfaithful, htwo_raw, _hthree,
      _hOcard, _hGcard, hstabilizer_raw⟩
  have hKcard : Nat.card K = q := by
    simpa [K, q, BinaryGaloisField] using
      GaloisField.card 2 (2 * m + 1) (by omega)
  have hFcard' : Nat.card F = q ^ 2 := by
    simpa [F, q] using hFcard
  have hHcard : Nat.card H = q - 1 := by
    calc
      Nat.card H = Nat.card Kˣ := Nat.card_congr eH.symm.toEquiv
      _ = Nat.card K - 1 := Nat.card_units K
      _ = q - 1 := by rw [hKcard]
  have hF_le_G : F ≤ SuzukiMatrixGroup m := by
    dsimp only [F]
    rw [Subgroup.closure_le]
    intro A hA
    exact Subgroup.subset_closure (Or.inl hA)
  have hH_le_G : H ≤ SuzukiMatrixGroup m := by
    dsimp only [H]
    rw [Subgroup.closure_le]
    intro A hA
    exact Subgroup.subset_closure (Or.inr (Or.inl hA))
  let R : Subgroup G := F.subgroupOf (SuzukiMatrixGroup m)
  let T : Subgroup G := H.subgroupOf (SuzukiMatrixGroup m)
  let U : Subgroup G := (F ⊔ H).subgroupOf (SuzukiMatrixGroup m)
  have hR_le_U : R ≤ U := by
    intro r hr
    exact (le_sup_left : F ≤ F ⊔ H) hr
  have hT_le_U : T ≤ U := by
    intro t ht
    exact (le_sup_right : H ≤ F ⊔ H) ht
  have hRT_sup : R ⊔ T = U := by
    simpa only [R, T, U] using
      (Subgroup.subgroupOf_sup hF_le_G hH_le_G).symm
  have hRT_inf : R ⊓ T = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hx_one : ((x : G) : GL (Fin 4) K) = 1 :=
        Subgroup.disjoint_def.mp hdisjoint hx.1 hx.2
      show x = 1
      apply Subtype.ext
      exact hx_one
    · exact bot_le
  have hH_le_normalizerF : H ≤ Subgroup.normalizer (F : Set (GL (Fin 4) K)) :=
    External.suzukiTorusClosure_le_normalizer_rootClosure
      m pi hpi_sq hpi_formula
  have hFH_le_normalizerF :
      F ⊔ H ≤ Subgroup.normalizer (F : Set (GL (Fin 4) K)) :=
    sup_le Subgroup.le_normalizer hH_le_normalizerF
  have hU_le_normalizerR : U ≤ Subgroup.normalizer (R : Set G) := by
    intro g hg
    have hg_normalizes :
        ((g : G) : GL (Fin 4) K) ∈
          Subgroup.normalizer (F : Set (GL (Fin 4) K)) :=
      hFH_le_normalizerF hg
    rw [Subgroup.mem_normalizer_iff] at hg_normalizes ⊢
    intro r
    exact hg_normalizes ((r : G) : GL (Fin 4) K)
  let eR : R ≃* F := Subgroup.subgroupOfEquivOfLe hF_le_G
  let eT : T ≃* H := Subgroup.subgroupOfEquivOfLe hH_le_G
  have hRp : IsPGroup 2 R := hFp.of_equiv eR.symm
  have hTcard : Nat.card T = q - 1 := by
    calc
      Nat.card T = Nat.card H := Nat.card_congr eT.toEquiv
      _ = q - 1 := hHcard
  have hq_even : Even q := by
    dsimp only [q]
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hq_pos : 0 < q := by
    dsimp only [q]
    positivity
  have hq_sub_one_odd : Odd (q - 1) :=
    Nat.Even.sub_odd hq_pos hq_even odd_one
  have hTnot : ¬ 2 ∣ Nat.card T := by
    rw [hTcard]
    intro htwo_dvd
    exact (Nat.not_even_iff_odd.mpr hq_sub_one_odd)
      (even_iff_two_dvd.mpr htwo_dvd)
  obtain ⟨PU, hPU⟩ :=
    exists_sylow_map_eq_of_normal_complement
      hR_le_U hT_le_U hU_le_normalizerR hRT_inf hRT_sup hRp hTnot
  let linRep : G →* LinearMap.GeneralLinearGroup K (Fin 4 → K) :=
    Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp
      (SuzukiMatrixGroup m).subtype
  let : MulAction G (ℙ K (Fin 4 → K)) :=
    MulAction.compHom (ℙ K (Fin 4 → K)) linRep
  let ovoid : SubMulAction G (ℙ K (Fin 4 → K)) :=
    { carrier := O
      smul_mem' := by
        intro g z hz
        change (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • z ∈ O
        exact hpres g z hz }
  let : MulAction G Omega := ovoid.mulAction
  let rho : G →* Equiv.Perm Omega := MulAction.toPermHom G Omega
  let pinfO : Omega := ⟨pinf, Or.inl rfl⟩
  have hU_eq_stabilizer : U = MulAction.stabilizer G pinfO := by
    ext g
    rw [MulAction.mem_stabilizer_iff, ← Subtype.coe_inj]
    change (g : GL (Fin 4) K) ∈ F ⊔ H ↔
      (Matrix.GeneralLinearGroup.toLin
        (g : GL (Fin 4) K)).toLinearEquiv • pinf = pinf
    exact (hstabilizer_raw g).symm
  have htwo : MulAction.IsMultiplyPretransitive G Omega 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    have hab_raw : (a : ℙ K (Fin 4 → K)) ≠ b := by
      intro h
      exact hab (Subtype.ext h)
    have hcd_raw : (c : ℙ K (Fin 4 → K)) ≠ d := by
      intro h
      exact hcd (Subtype.ext h)
    rcases htwo_raw (a : ℙ K (Fin 4 → K)) b c d
        a.property b.property c.property d.property hab_raw hcd_raw with
      ⟨g, hga, hgb⟩
    exact ⟨g, Subtype.ext hga, Subtype.ext hgb⟩
  have hRregular : ∀ a b : Omega, a ≠ pinfO → b ≠ pinfO →
      ∃! r : R, (r : G) • a = b := by
    intro a b ha hb
    have ha_raw : (a : ℙ K (Fin 4 → K)) ≠ pinf := by
      intro h
      exact ha (Subtype.ext h)
    have hb_raw : (b : ℙ K (Fin 4 → K)) ≠ pinf := by
      intro h
      exact hb (Subtype.ext h)
    rcases External.suzukiRootClosure_regular_on_ovoid_complement
        m pi hpi (a : ℙ K (Fin 4 → K)) b
          a.property b.property ha_raw hb_raw with
      ⟨r, hr, hr_unique⟩
    let rR : R :=
      ⟨⟨(r : GL (Fin 4) K), hF_le_G r.property⟩, r.property⟩
    refine ⟨rR, ?_, ?_⟩
    · apply Subtype.ext
      change (Matrix.GeneralLinearGroup.toLin
        (r : GL (Fin 4) K)).toLinearEquiv •
          (a : ℙ K (Fin 4 → K)) = b
      exact hr
    · intro s hs
      let sF : F := ⟨((s : G) : GL (Fin 4) K), s.property⟩
      have hs_raw :
          (Matrix.GeneralLinearGroup.toLin
            (sF : GL (Fin 4) K)).toLinearEquiv •
              (a : ℙ K (Fin 4 → K)) = b := by
        exact congrArg Subtype.val hs
      have hsF_eq : sF = r := hr_unique sF hs_raw
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : F => (x : GL (Fin 4) K)) hsF_eq
  have hRcard : Nat.card R = q ^ 2 := by
    calc
      Nat.card R = Nat.card F := Nat.card_congr eR.toEquiv
      _ = q ^ 2 := hFcard'
  have hq_gt_one : 1 < q := by
    dsimp only [q]
    exact one_lt_pow₀ (by norm_num) (by omega)
  have hR_ne : R ≠ ⊥ := by
    intro hRbot
    have hRcard_one : Nat.card R = 1 := by rw [hRbot]; simp
    have hq_sq_one : q ^ 2 = 1 := hRcard.symm.trans hRcard_one
    nlinarith
  have hR_le_stabilizer : R ≤ MulAction.stabilizer G pinfO := by
    rw [← hU_eq_stabilizer]
    exact hR_le_U
  have hstabilizer_le_normalizer :
      MulAction.stabilizer G pinfO ≤ Subgroup.normalizer (R : Set G) := by
    rw [← hU_eq_stabilizer]
    exact hU_le_normalizerR
  have hnormalizer :
      Subgroup.normalizer (R : Set G) = MulAction.stabilizer G pinfO :=
    normalizer_eq_stabilizer_of_regular_compl R pinfO
      hR_le_stabilizer hR_ne hRregular hstabilizer_le_normalizer
  have hnormalizer_le :
      Subgroup.normalizer
          (((PU : Subgroup U).map U.subtype : Subgroup G) : Set G) ≤ U := by
    rw [hPU, hnormalizer, ← hU_eq_stabilizer]
  obtain ⟨S, hSmap⟩ :=
    exists_sylow_map_eq_of_normalizer_le PU hnormalizer_le
  have hSR : (S : Subgroup G) = R := hSmap.trans hPU
  have hSnormalizer :
      Subgroup.normalizer ((S : Subgroup G) : Set G) =
        (MulAction.stabilizer (Equiv.Perm Omega) pinfO).comap rho := by
    rw [hSR, hnormalizer]
    ext g
    simp [MulAction.mem_stabilizer_iff, rho]
  have hSregular : IsRegularOn (S : Subgroup G)
      {omega : Omega | omega ≠ pinfO} := by
    rw [hSR]
    exact hRregular
  have hSregular_rho :
      ∀ a b : Omega, a ≠ pinfO → b ≠ pinfO →
        ∃! s : S, rho (s : G) a = b := by
    intro a b ha hb
    exact hSregular ha hb
  have htwo_rho : ∀ a b c d : Omega, a ≠ b → c ≠ d →
      ∃ g : G, rho g a = c ∧ rho g b = d := by
    rw [MulAction.is_two_pretransitive_iff] at htwo
    intro a b c d hab hcd
    rcases htwo hab hcd with ⟨g, hga, hgb⟩
    exact ⟨g, hga, hgb⟩
  have hrho_apply (g : G) (z : Omega) :
      ((rho g z : Omega) : ℙ K (Fin 4 → K)) =
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv •
            (z : ℙ K (Fin 4 → K)) := by
    rfl
  exact ⟨rho, pinfO, S, hrho_apply, hSnormalizer,
    hSregular_rho, htwo_rho⟩

/-- Every Borel subgroup of a concrete Suzuki group has a doubly transitive
left-coset action. -/
public theorem IsBorelSubgroup.suzuki_coset_isTwoPretransitive
    (m : ℕ) (hm : 0 < m)
    {B : Subgroup (SuzukiMatrixGroup m)} (hB : IsBorelSubgroup B) :
    MulAction.IsMultiplyPretransitive
      (SuzukiMatrixGroup m) (SuzukiMatrixGroup m ⧸ B) 2 := by
  let K := BinaryGaloisField (2 * m + 1)
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let O : Set (ℙ K (Fin 4 → K)) :=
    {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
  let Omega := {z : ℙ K (Fin 4 → K) // z ∈ O}
  let G := SuzukiMatrixGroup m
  have hdata :
    ∃ (rho : G →* Equiv.Perm Omega) (pinfO : Omega) (S : Sylow 2 G),
        (∀ g : G, ∀ z : Omega,
          ((rho g z : Omega) : ℙ K (Fin 4 → K)) =
            (Matrix.GeneralLinearGroup.toLin
              (g : GL (Fin 4) K)).toLinearEquiv •
                (z : ℙ K (Fin 4 → K))) ∧
        Subgroup.normalizer ((S : Subgroup G) : Set G) =
          (MulAction.stabilizer (Equiv.Perm Omega) pinfO).comap rho ∧
        (∀ a b : Omega, a ≠ pinfO → b ≠ pinfO →
          ∃! s : S, rho (s : G) a = b) ∧
        (∀ a b c d : Omega, a ≠ b → c ≠ d →
          ∃ g : G, rho g a = c ∧ rho g b = d) := by
    exact suzuki_sylow_normalizer_action m hm
  rcases hdata with
    ⟨rho, pinfO, S, _hrho_apply, hnormalizer, _hregular, htwo⟩
  letI : MulAction G Omega := MulAction.compHom Omega rho
  have hnormalizer' :
      Subgroup.normalizer ((S : Subgroup G) : Set G) =
        MulAction.stabilizer G pinfO := by
    calc
      Subgroup.normalizer ((S : Subgroup G) : Set G) =
          (MulAction.stabilizer (Equiv.Perm Omega) pinfO).comap rho :=
        hnormalizer
      _ = MulAction.stabilizer G pinfO := by
        ext g
        change (rho g) pinfO = pinfO ↔ (rho g) pinfO = pinfO
        rfl
  have htwo' : MulAction.IsMultiplyPretransitive G Omega 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    exact htwo a b c d hab hcd
  exact hB.coset_isTwoPretransitive_of_sylow_normalizer
    S pinfO hnormalizer' htwo'

/-- The Suzuki alternative in Bender recognition supplies a doubly
transitive Borel coset action after transport through the recognizing
equivalence. -/
public theorem IsBorelSubgroup.coset_isTwoPretransitive_of_isSuzuki_model
    {G : Type u} [Group G] [Finite G] {B : Subgroup G}
    (hB : IsBorelSubgroup B)
    (hmodel : ∃ m : ℕ, 1 ≤ m ∧
      Nonempty (G ≃* SuzukiMatrixGroup m)) :
    MulAction.IsMultiplyPretransitive G (G ⧸ B) 2 := by
  rcases hmodel with ⟨m, hm, e⟩
  let eG : G ≃* SuzukiMatrixGroup m := e.some
  apply coset_isTwoPretransitive_of_mulEquiv eG B
  exact IsBorelSubgroup.suzuki_coset_isTwoPretransitive
    m hm (hB.map_mulEquiv eG)

/-- Every Borel subgroup in one of the three simple Bender models has a
doubly transitive left-coset action. -/
public theorem simpleBender_borel_coset_twoTransitive
    {G : Type u} [Group G] [Finite G] {B : Subgroup G}
    (hB : IsBorelSubgroup B) (hmodel : IsSimpleBenderGroup G) :
    MulAction.IsMultiplyPretransitive G (G ⧸ B) 2 := by
  rcases hmodel with ⟨hPSL⟩ | ⟨hSuzuki⟩ | ⟨hPSU⟩
  · exact hB.coset_isTwoPretransitive_of_isPSL2_model hPSL
  · exact hB.coset_isTwoPretransitive_of_isSuzuki_model hSuzuki
  · exact hB.coset_isTwoPretransitive_of_isPSU3_model hPSU

/-- Every Borel subgroup in a simple Bender model has a normal Sylow
`2`-subgroup acting regularly on the non-base cosets. -/
public theorem simpleBender_borel_normalSylow_regular
    {G : Type u} [Group G] [Finite G] {B : Subgroup G}
    (hB : IsBorelSubgroup B) (hmodel : IsSimpleBenderGroup G) :
    ∃ P : Sylow 2 B,
      (P : Subgroup B).Normal ∧
      IsRegularOn ((P : Subgroup B).map B.subtype)
        {q : G ⧸ B | q ≠ QuotientGroup.mk 1} := by
  rcases hmodel with ⟨hPSL⟩ | ⟨hSuzuki⟩ | ⟨hPSU⟩
  · rcases hPSL with ⟨n, hn, e⟩
    let K := BinaryGaloisField n
    let Omega := ℙ K (Fin 2 → K)
    let Q := Matrix.ProjGenLinGroup (Fin 2) K
    letI : Finite Q :=
      Finite.of_surjective Matrix.ProjGenLinGroup.mk
        Matrix.ProjGenLinGroup.mk_surjective
    let ePGL : PSL2BinaryMatrixGroup n ≃* Q :=
      (psl_charTwo_equiv_pgl n (by omega)).some
    let eG : G ≃* Q := e.some.trans ePGL
    rcases pgl_sylow_normalizer_action n hn with
      ⟨rho, pinf, S, _hrho_apply, hnormalizer, hregular, _htwo⟩
    letI : MulAction Q Omega := MulAction.compHom Omega rho
    have hnormalizer' :
        Subgroup.normalizer ((S : Subgroup Q) : Set Q) =
          MulAction.stabilizer Q pinf := by
      calc
        Subgroup.normalizer ((S : Subgroup Q) : Set Q) =
            (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho :=
          hnormalizer
        _ = MulAction.stabilizer Q pinf := by
          ext g
          change (rho g) pinf = pinf ↔ (rho g) pinf = pinf
          rfl
    have hregular' : IsRegularOn (S : Subgroup Q)
        {omega : Omega | omega ≠ pinf} := by
      intro a b ha hb
      exact hregular a b ha hb
    exact hB.exists_normal_sylow_regularOn_cosets_of_mulEquiv
      eG S pinf hnormalizer' hregular'
  · rcases hSuzuki with ⟨m, hm, e⟩
    let K := BinaryGaloisField (2 * m + 1)
    let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y ↦
      Projectivization.mk K
        ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) :=
      {pinf} ∪ Set.range fun z : K × K ↦ p z.1 z.2
    let Omega := {z : ℙ K (Fin 4 → K) // z ∈ O}
    let Q := SuzukiMatrixGroup m
    have hdata :
        ∃ (rho : Q →* Equiv.Perm Omega) (pinfO : Omega)
            (S : Sylow 2 Q),
          (∀ g : Q, ∀ z : Omega,
            ((rho g z : Omega) : ℙ K (Fin 4 → K)) =
              (Matrix.GeneralLinearGroup.toLin
                (g : GL (Fin 4) K)).toLinearEquiv •
                  (z : ℙ K (Fin 4 → K))) ∧
          Subgroup.normalizer ((S : Subgroup Q) : Set Q) =
            (MulAction.stabilizer (Equiv.Perm Omega) pinfO).comap rho ∧
          (∀ a b : Omega, a ≠ pinfO → b ≠ pinfO →
            ∃! s : S, rho (s : Q) a = b) ∧
          (∀ a b c d : Omega, a ≠ b → c ≠ d →
            ∃ g : Q, rho g a = c ∧ rho g b = d) := by
      exact suzuki_sylow_normalizer_action m hm
    rcases hdata with
      ⟨rho, pinfO, S, _hrho_apply, hnormalizer, hregular, _htwo⟩
    letI : MulAction Q Omega := MulAction.compHom Omega rho
    have hnormalizer' :
        Subgroup.normalizer ((S : Subgroup Q) : Set Q) =
          MulAction.stabilizer Q pinfO := by
      calc
        Subgroup.normalizer ((S : Subgroup Q) : Set Q) =
            (MulAction.stabilizer (Equiv.Perm Omega) pinfO).comap rho :=
          hnormalizer
        _ = MulAction.stabilizer Q pinfO := by
          ext g
          change (rho g) pinfO = pinfO ↔ (rho g) pinfO = pinfO
          rfl
    have hregular' : IsRegularOn (S : Subgroup Q)
        {omega : Omega | omega ≠ pinfO} := by
      intro a b ha hb
      exact hregular a b ha hb
    let eG : G ≃* Q := e.some
    exact hB.exists_normal_sylow_regularOn_cosets_of_mulEquiv
      eG S pinfO hnormalizer' hregular'
  · rcases hPSU with
      ⟨n, hn, E, hEfield, hEfinite, J, hJstandard,
        hEcard, hfixed_card, e⟩
    letI : Field E := hEfield
    letI : Finite E := hEfinite
    let q := 2 ^ n
    let P := ℙ E (Fin 3 → E)
    let A : Set P :=
      {x | ∃ (v : Fin 3 → E) (hv : v ≠ 0),
        x = Projectivization.mk E v hv ∧
          dotProduct (fun i ↦ J.conj (v i)) (J.form.mulVec v) = 0}
    let Omega := {x : P // x ∈ A}
    let Q := ProjectiveSpecialUnitaryMatrixGroup J
    letI : Fintype E := Fintype.ofFinite E
    letI : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
      Finite.of_surjective Matrix.ProjGenLinGroup.mk
        Matrix.ProjGenLinGroup.mk_surjective
    letI : Finite Q :=
      Finite.of_injective
        (fun x : Q =>
          (x : Matrix.ProjGenLinGroup (Fin 3) E)) Subtype.coe_injective
    have hdata :
        ∃ (rho : Q →* Equiv.Perm Omega) (pinf : Omega)
            (S : Sylow 2 Q),
          Function.Injective rho ∧
          Nat.card S = q ^ 3 ∧
          Subgroup.normalizer ((S : Subgroup Q) : Set Q) =
            (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho ∧
          (∀ a b : Omega, a ≠ pinf → b ≠ pinf →
            ∃! s : S, rho (s : Q) a = b) ∧
          (∀ a b c d : Omega, a ≠ b → c ≠ d →
            ∃ g : Q, rho g a = c ∧ rho g b = d) := by
      rcases psu_sylow_normalizer_action
          J n hn hEcard hfixed_card hJstandard with
        ⟨rho, pinf, S, hrho, _hnatural, hScard, hnormalizer,
          hregular, htwo⟩
      exact ⟨rho, pinf, S, hrho, hScard, hnormalizer,
        hregular, htwo⟩
    rcases hdata with
      ⟨rho, pinf, S, _hrho, _hScard, hnormalizer,
        hregular, _htwo⟩
    letI : MulAction Q Omega := MulAction.compHom Omega rho
    have hnormalizer' :
        Subgroup.normalizer ((S : Subgroup Q) : Set Q) =
          MulAction.stabilizer Q pinf := by
      calc
        Subgroup.normalizer ((S : Subgroup Q) : Set Q) =
            (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho :=
          hnormalizer
        _ = MulAction.stabilizer Q pinf := by
          ext g
          change (rho g) pinf = pinf ↔ (rho g) pinf = pinf
          rfl
    have hregular' : IsRegularOn (S : Subgroup Q)
        {omega : Omega | omega ≠ pinf} := by
      intro a b ha hb
      exact hregular a b ha hb
    let eG : G ≃* Q := e.some
    exact hB.exists_normal_sylow_regularOn_cosets_of_mulEquiv
      eG S pinf hnormalizer' hregular'

end CFSG.BenderSuzuki
