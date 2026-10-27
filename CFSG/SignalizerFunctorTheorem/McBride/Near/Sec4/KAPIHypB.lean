module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.KAPIDeg
public import CFSG.SignalizerFunctorTheorem.Inheritance.Sections

public section

open CFSG.SignalizerFunctorTheorem CFSG.SignalizerFunctorTheorem.Nonsolvable
  CFSG.SignalizerFunctorTheorem.McBride

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.KAPI

theorem kOf_map_mulEquiv {G G' : Type*} [Group G] [Group G'] [Finite G] (e : G ≃* G')
    (X : Subgroup G) : kOf (X.map (e : G →* G')) = (kOf X).map (e : G →* G') := by
  have h1 : (oStar ↥X).map (e.subgroupMap X).toMonoidHom = oStar ↥(X.map (e : G →* G')) :=
    oStar_map_mulEquiv _
  have hcomp : (X.map (e : G →* G')).subtype.comp (e.subgroupMap X).toMonoidHom =
      (e : G →* G').comp X.subtype := by
    ext x
    rfl
  calc kOf (X.map (e : G →* G'))
      = ((oStar ↥X).map (e.subgroupMap X).toMonoidHom).map (X.map (e : G →* G')).subtype := by
        rw [h1]
        rfl
    _ = (oStar ↥X).map ((X.map (e : G →* G')).subtype.comp (e.subgroupMap X).toMonoidHom) := by
        rw [Subgroup.map_map]
    _ = (oStar ↥X).map ((e : G →* G').comp X.subtype) := by rw [hcomp]
    _ = (kOf X).map (e : G →* G') := by
        rw [← Subgroup.map_map]
        rfl

theorem HypB.congr {H H' : Type*} [Group H] [Group H'] [Finite H] (h : HypB H) (e : H ≃* H') :
    HypB H' := by
  obtain ⟨hs, hnc, hX⟩ := h
  have : Finite H' := Finite.of_equiv H e.toEquiv
  refine ⟨?_, ?_, ?_⟩
  · exact e.symm.isSimpleGroup
  · obtain ⟨a, b, hab⟩ := hnc
    exact ⟨e a, e b, fun h => hab (e.injective (by simpa using h))⟩
  · intro X' hX' hperf hnot
    have hX'k : kOf X' = X' := hX'
    let ε : MulAut H ≃* MulAut H' := MulAut.congr e
    set X : Subgroup (MulAut H) := X'.map (ε.symm : MulAut H' →* MulAut H) with hXdef
    have hXk : kOf X = X := by
      rw [hXdef, kOf_map_mulEquiv ε.symm X', hX'k]
    have hXperf : Group.IsPerfect X := by
      rw [Subgroup.isPerfect_iff] at hperf ⊢
      rw [hXdef, ← Subgroup.map_commutator, hperf]
    have hXnot : ¬ X ≤ (MulAut.conj : H →* MulAut H).range := by
      intro hle
      apply hnot
      intro x' hx'
      have hx : ε.symm x' ∈ X := ⟨x', hx', rfl⟩
      obtain ⟨h, hh⟩ := hle hx
      refine ⟨e h, ?_⟩
      have key : ε (MulAut.conj h) = MulAut.conj (e h) := by
        ext y
        simp [ε, MulAut.congr]
      rw [← key]
      change ε (MulAut.conj h) = x'
      rw [hh]
      simp
    have h1 : deg X' = deg X := deg_congr (ε.symm.subgroupMap X')
    have h2 : deg X < deg H := hX X hXk hXperf hXnot
    have h3 : deg H = deg H' := deg_congr e
    omega


theorem hypB_of_isSectionOf {H : Type*} [Group H] [Finite H] (hC : HypC H) {Q : Type*} [Group Q]
    (hQ : IsSectionOf Q H) (hs : IsSimpleGroup Q) (hnc : ∃ a b : Q, a * b ≠ b * a) :
    HypB Q := by
  obtain ⟨K, f, hf⟩ := hQ
  have hLK : f.ker.map K.subtype ≤ K := Subgroup.map_subtype_le _
  have hLsub : (f.ker.map K.subtype).subgroupOf K = f.ker :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have hnormal : ((f.ker.map K.subtype).subgroupOf K).Normal := by
    rw [hLsub]
    exact f.normal_ker
  let e : K ⧸ (f.ker.map K.subtype).subgroupOf K ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hLsub).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hsimple : IsSimpleGroup (K ⧸ (f.ker.map K.subtype).subgroupOf K) := e.isSimpleGroup
  have hnc' : ∃ a b : K ⧸ (f.ker.map K.subtype).subgroupOf K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by simpa using h))⟩
  have h : HypB (K ⧸ (f.ker.map K.subtype).subgroupOf K) :=
    @hC K (f.ker.map K.subtype) hLK hnormal hsimple hnc'
  exact HypB.congr h e


theorem HypC.of_isSectionOf {H K : Type*} [Group H] [Finite H] [Group K] (hC : HypC H)
    (hK : IsSectionOf K H) : HypC K := by
  intro K' L' hL' _ hs hnc
  have hsec : IsSectionOf (K' ⧸ L'.subgroupOf K') K :=
    (IsSectionOf.of_surjective (QuotientGroup.mk' (L'.subgroupOf K'))
      (QuotientGroup.mk'_surjective _)).trans (IsSectionOf.of_subgroup K')
  exact hypB_of_isSectionOf hC (hsec.trans hK) hs hnc

theorem conj_injective_of_isSimpleGroup {J : Type*} [Group J] [IsSimpleGroup J]
    (hnc : ∃ a b : J, a * b ≠ b * a) : Function.Injective (MulAut.conj : J →* MulAut J) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  have hker : (MulAut.conj : J →* MulAut J).ker = Subgroup.center J := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro h y
      have := congrArg (fun φ : MulAut J => φ y) h
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * g = g * y * g⁻¹ * g := by rw [this]
        _ = g * y := by group
    · intro h
      ext y
      simp only [MulAut.conj_apply, MulAut.one_apply]
      rw [← h y]
      group
  rw [hker]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center J) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have : a ∈ Subgroup.center J := h ▸ Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.mp this b).symm)

theorem deg_quotient_ker_le {J A : Type*} [Group J] [Finite J] [Group A] [Finite A] (hJ : HypB J)
    (hA : oStar A = ⊤) (ρ : A →* MulAut J) :
    deg (A ⧸ ρ.ker) ≤ deg J ∧
      ((Group.IsPerfect A ∧ deg (A ⧸ ρ.ker) = deg J) →
        ρ.range ≤ (MulAut.conj : J →* MulAut J).range) := by
  obtain ⟨hs, hnc, hX⟩ := hJ
  have hdegJ : deg J = permDeg J := deg_eq_permDeg_of_isSimpleGroup J (by
    intro hcomm
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (hcomm.is_comm.comm a b))
  set B : Subgroup (MulAut J) := ρ.range with hB
  have hBo : oStar B = ⊤ := oStar_eq_top_of_surjective hA ρ.rangeRestrict_surjective
  have e1 : deg (A ⧸ ρ.ker) = deg B := deg_congr (QuotientGroup.quotientKerEquivRange ρ)
  set P : Subgroup (MulAut J) := (CFSG.perfectResidual B).map B.subtype with hP
  have ePB : ↥(CFSG.perfectResidual B) ≃* ↥P :=
    Subgroup.equivMapOfInjective _ B.subtype B.subtype_injective
  have hPo : oStar ↥P = ⊤ := by
    have : oStar ↥(CFSG.perfectResidual B) = ⊤ := oStar_eq_top_of_normal hBo _
    exact oStar_eq_top_of_surjective this (f := ePB.toMonoidHom) ePB.surjective
  have hPk : kOf P = P := (kOf_eq_self_iff_oStar_eq_top P).mpr hPo
  have hPperf : Group.IsPerfect P := isPerfect_perfectResidual_map B
  have hdegP : deg P = deg B := by
    rw [← deg_perfectResidual hBo]
    exact (deg_congr ePB).symm
  have key : ¬ P ≤ (MulAut.conj : J →* MulAut J).range → deg B < deg J := fun h => by
    rw [← hdegP]
    exact hX P hPk hPperf h
  have key2 : P ≤ (MulAut.conj : J →* MulAut J).range → deg B ≤ deg J := fun hle => by
    rw [← hdegP]
    have hconj := conj_injective_of_isSimpleGroup hnc
    let ψ : ↥P →* J :=
      ((MonoidHom.ofInjective hconj).symm.toMonoidHom).comp (Subgroup.inclusion hle)
    have hψ : Function.Injective ψ :=
      (MonoidHom.ofInjective hconj).symm.injective.comp (Subgroup.inclusion_injective hle)
    calc deg P ≤ permDeg P := deg_le_permDeg hPo
      _ ≤ permDeg J := permDeg_le_of_injective_hom hψ
      _ = deg J := hdegJ.symm
  refine ⟨?_, ?_⟩
  · rw [e1]
    by_cases h : P ≤ (MulAut.conj : J →* MulAut J).range
    · exact key2 h
    · exact (key h).le
  · rintro ⟨hAp, heq⟩
    by_contra hnot
    have hBperf : Group.IsPerfect B := by
      have := hAp
      exact Group.IsPerfect.range ρ
    have hPB : P = B := perfectResidual_map_eq_of_isPerfect hBperf
    have : ¬ P ≤ (MulAut.conj : J →* MulAut J).range := by rw [hPB]; exact hnot
    have := key this
    omega

end CFSG.SignalizerFunctorTheorem.McBride.Near.KAPI
