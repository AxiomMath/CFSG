module

public import CFSG.LocalAnalysis.StandardType.GGTBTorRelDNsTorus
public import CFSG.LocalAnalysis.StandardType.GGTBTorRelDPlane

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType

namespace RelDNs

open Polynomial QuadraticMap Module
open CFSG.RankThree.Classical2 CFSG.LocalAnalysis.GLTheoremA.S172C.Cent CFSG.Open

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p k : ℕ} {U : Fin k → Submodule F V}
  {e : Fin k → ↥(orthDerived Q)} {E : Subgroup ↥(orthDerived Q)} {u : Fin k → V} {c t : F}

private theorem restrictEquiv_pow_coe {W : Submodule F V} {g : V ≃ₗ[F] V}
    (h1 : ∀ w ∈ W, g w ∈ W) (h2 : ∀ w ∈ W, g.symm w ∈ W) (n : ℕ) (w : W) :
    ((CFSG.RankThree.PartOne.KCOrthogonal.restrictEquiv W g h1 h2 ^ n) w : V) = (g ^ n) (w : V) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', LinearEquiv.mul_apply,
        CFSG.RankThree.PartOne.KCOrthogonal.coe_restrictEquiv, ih, pow_succ',
        LinearEquiv.mul_apply]

theorem preserves_plane_of_commute (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    {g : ↥(orthDerived Q)} (hc : ∀ x ∈ E, g * x = x * g) (a : Fin k) :
    (∀ w ∈ U a, (g : V ≃ₗ[F] V) w ∈ U a) ∧
      (∀ w ∈ U a, (g : V ≃ₗ[F] V).symm w ∈ U a) ∧
      (∀ w ∈ polarPerp Q (U a), (g : V ≃ₗ[F] V) w ∈ polarPerp Q (U a)) := by
  have hge : (g : V ≃ₗ[F] V) * (e a : V ≃ₗ[F] V) = (e a : V ≃ₗ[F] V) * (g : V ≃ₗ[F] V) := by
    have h := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) (hc (e a) (hF.toIsPlaneFrame.mem a))
    simpa using h
  have hge' : (g : V ≃ₗ[F] V).symm * (e a : V ≃ₗ[F] V) =
      (e a : V ≃ₗ[F] V) * (g : V ≃ₗ[F] V).symm := (Commute.inv_left hge).eq
  have happ : ∀ x : V, (g : V ≃ₗ[F] V) ((e a : V ≃ₗ[F] V) x) =
      (e a : V ≃ₗ[F] V) ((g : V ≃ₗ[F] V) x) := by
    intro x
    have h := congrArg (fun f : V ≃ₗ[F] V => f x) hge
    simpa [LinearEquiv.mul_apply] using h
  have happ' : ∀ x : V, (g : V ≃ₗ[F] V).symm ((e a : V ≃ₗ[F] V) x) =
      (e a : V ≃ₗ[F] V) ((g : V ≃ₗ[F] V).symm x) := by
    intro x
    have h := congrArg (fun f : V ≃ₗ[F] V => f x) hge'
    simpa [LinearEquiv.mul_apply] using h
  have hgP : ∀ w ∈ polarPerp Q (U a), (g : V ≃ₗ[F] V) w ∈ polarPerp Q (U a) := by
    intro w hw
    rw [← (hF.toIsPlaneFrame).fixedSpace_eq_polarPerp a] at hw ⊢
    rw [CFSG.RankThree.PartOne.KCOrthogonal.mem_fixedSpace] at hw ⊢
    rw [← happ w, hw]
  have hcompl : IsCompl (U a) (polarPerp Q (U a)) := isCompl_polarPerp (hF.nondeg a)
  have hcommSpace : LinearMap.range (((e a : V ≃ₗ[F] V) : V →ₗ[F] V) - 1) = U a := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro w ⟨v, rfl⟩
      obtain ⟨uu, rr, huv⟩ :=
        CFSG.RankThree.PartOne.KCOrthogonal.exists_coe_add_of_isCompl hcompl v
      have hrr : (e a : V ≃ₗ[F] V) (rr : V) = (rr : V) :=
        (hF.toIsPlaneFrame).apply_of_perp a (rr : V) rr.2
      have hsplit : (((e a : V ≃ₗ[F] V) : V →ₗ[F] V) - 1) v =
          ((e a : V ≃ₗ[F] V) (uu : V) - (uu : V)) +
            ((e a : V ≃ₗ[F] V) (rr : V) - (rr : V)) := by
        rw [← huv]
        show (e a : V ≃ₗ[F] V) ((uu : V) + (rr : V)) - ((uu : V) + (rr : V)) =
          ((e a : V ≃ₗ[F] V) (uu : V) - (uu : V)) +
            ((e a : V ≃ₗ[F] V) (rr : V) - (rr : V))
        rw [map_add, hrr]
        abel
      rw [hsplit, hrr, sub_self, add_zero]
      exact (U a).sub_mem (hF.maps_to a (uu : V) uu.2) uu.2
    · have hker : LinearMap.ker (((e a : V ≃ₗ[F] V) : V →ₗ[F] V) - 1) =
          polarPerp Q (U a) := (hF.toIsPlaneFrame).fixedSpace_eq_polarPerp a
      have hrnk := LinearMap.finrank_range_add_finrank_ker
        (((e a : V ≃ₗ[F] V) : V →ₗ[F] V) - 1)
      have hdimV : Module.finrank F (U a) + Module.finrank F (polarPerp Q (U a)) =
          Module.finrank F V := Submodule.finrank_add_eq_of_isCompl hcompl
      rw [hker] at hrnk
      omega
  refine ⟨?_, ?_, hgP⟩
  · intro w hw
    have hw' : w ∈ LinearMap.range (((e a : V ≃ₗ[F] V) : V →ₗ[F] V) - 1) := by
      rw [hcommSpace]; exact hw
    obtain ⟨v, rfl⟩ := (LinearMap.mem_range).mp hw'
    rw [← hcommSpace]
    refine (LinearMap.mem_range).mpr ⟨(g : V ≃ₗ[F] V) v, ?_⟩
    show (e a : V ≃ₗ[F] V) ((g : V ≃ₗ[F] V) v) - (g : V ≃ₗ[F] V) v =
      (g : V ≃ₗ[F] V) ((e a : V ≃ₗ[F] V) v - v)
    rw [map_sub, ← happ v]
  · intro w hw
    have hw' : w ∈ LinearMap.range (((e a : V ≃ₗ[F] V) : V →ₗ[F] V) - 1) := by
      rw [hcommSpace]; exact hw
    obtain ⟨v, rfl⟩ := (LinearMap.mem_range).mp hw'
    rw [← hcommSpace]
    refine (LinearMap.mem_range).mpr ⟨(g : V ≃ₗ[F] V).symm v, ?_⟩
    show (e a : V ≃ₗ[F] V) ((g : V ≃ₗ[F] V).symm v) - (g : V ≃ₗ[F] V).symm v =
      (g : V ≃ₗ[F] V).symm ((e a : V ≃ₗ[F] V) v - v)
    rw [map_sub, ← happ' v]

theorem restrictEquiv_mem_centralizer (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    {g : ↥(orthDerived Q)} (hc : ∀ x ∈ E, g * x = x * g) (a : Fin k)
    {hgU : ∀ w ∈ U a, (g : V ≃ₗ[F] V) w ∈ U a}
    {hgU' : ∀ w ∈ U a, (g : V ≃ₗ[F] V).symm w ∈ U a} :
    CFSG.RankThree.PartOne.KCOrthogonal.restrictEquiv (U a) (g : V ≃ₗ[F] V) hgU hgU' ∈
      Subgroup.centralizer ({planeEquiv hF a} : Set (↥(U a) ≃ₗ[F] ↥(U a))) := by
  have hge : (g : V ≃ₗ[F] V) * (e a : V ≃ₗ[F] V) = (e a : V ≃ₗ[F] V) * (g : V ≃ₗ[F] V) := by
    have h := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) (hc (e a) (hF.toIsPlaneFrame.mem a))
    simpa using h
  have happ : ∀ x : V, (g : V ≃ₗ[F] V) ((e a : V ≃ₗ[F] V) x) =
      (e a : V ≃ₗ[F] V) ((g : V ≃ₗ[F] V) x) := by
    intro x
    have h := congrArg (fun f : V ≃ₗ[F] V => f x) hge
    simpa [LinearEquiv.mul_apply] using h
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  refine LinearEquiv.ext fun w => Subtype.ext ?_
  simp only [LinearEquiv.mul_apply, planeEquiv_apply,
    CFSG.RankThree.PartOne.KCOrthogonal.coe_restrictEquiv]
  exact (happ (w : V)).symm

theorem commute_planeRot_of_commute (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    [Fact (Irreducible (OmNsRootGen.framePoly t))]
    {g : ↥(orthDerived Q)} (hc : ∀ x ∈ E, g * x = x * g) (a : Fin k) (z : normOne t) :
    Commute (planeRot hF a z) (g : V ≃ₗ[F] V) := by
  classical
  obtain ⟨hgU, hgU', hgP⟩ := preserves_plane_of_commute hF hc a
  set G := CFSG.RankThree.PartOne.KCOrthogonal.restrictEquiv (U a) (g : V ≃ₗ[F] V) hgU hgU'
    with hGdef
  have hGcoe : ∀ w : ↥(U a), ((G w : ↥(U a)) : V) = (g : V ≃ₗ[F] V) (w : V) := by
    intro w
    rw [hGdef]
    exact CFSG.RankThree.PartOne.KCOrthogonal.coe_restrictEquiv (U a) (g : V ≃ₗ[F] V) hgU hgU' w
  have hGcent : G ∈ Subgroup.centralizer
      ({planeEquiv hF a} : Set (↥(U a) ≃ₗ[F] ↥(U a))) :=
    restrictEquiv_mem_centralizer hF hc a (hgU := hgU) (hgU' := hgU')
  have hφcent : planeLinEquiv hF a z ∈ Subgroup.centralizer
      ({planeEquiv hF a} : Set (↥(U a) ≃ₗ[F] ↥(U a))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    apply LinearEquiv.toLinearMap_injective
    simp only [LinearEquiv.coe_toLinearMap_mul, planeEquiv_toLinearMap]
    rw [show ((planeLinEquiv hF a z : ↥(U a) ≃ₗ[F] ↥(U a)) : Module.End F ↥(U a)) =
        planeAlg hF a (normOneVal (F := F) (t := t) z) from
      LinearMap.ext fun w => planeLinEquiv_apply hF a z w]
    exact (planeAlg_commute_planeEnd hF a (normOneVal (F := F) (t := t) z)).eq.symm
  have hcns : ∀ x : F, ((planeEquiv hF a : ↥(U a) ≃ₗ[F] ↥(U a)) : Module.End F ↥(U a)) ≠
      x • 1 :=
    RelDPlane.not_scalar (Q := Q.comp (U a).subtype) (hF.finrank_eq a) (hF.nondeg a)
      (planeEquiv hF a) (planeEquiv_mem_orthogonalGroup hF a)
      (planeEquiv_eq_self_imp_eq_zero hF a)
  have hcommU : G * planeLinEquiv hF a z = planeLinEquiv hF a z * G :=
    RelDPlane.centralizer_comm (K := F) (U := ↥(U a)) (c := planeEquiv hF a)
      (hF.finrank_eq a) hcns hGcent hφcent
  have hrot_mem : ∀ (w : V) (hw : w ∈ U a),
      planeRot hF a z w = ((planeLinEquiv hF a z ⟨w, hw⟩ : ↥(U a)) : V) := by
    intro w hw
    rw [planeRot_apply_mem hF a z hw, planeLinEquiv_apply]
  have hrot_perp : ∀ (w : V) (hw : w ∈ polarPerp Q (U a)), planeRot hF a z w = w :=
    fun w hw => planeRot_apply_perp hF a z hw
  have hcompl : IsCompl (U a) (polarPerp Q (U a)) := isCompl_polarPerp (hF.nondeg a)
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨uu, rr, huv⟩ :=
    CFSG.RankThree.PartOne.KCOrthogonal.exists_coe_add_of_isCompl hcompl v
  have hL : planeRot hF a z ((g : V ≃ₗ[F] V) v) =
      ((planeLinEquiv hF a z ⟨(g : V ≃ₗ[F] V) (uu : V), hgU uu uu.2⟩ : ↥(U a)) : V) +
        (g : V ≃ₗ[F] V) (rr : V) := by
    have h1 : (g : V ≃ₗ[F] V) v =
        (g : V ≃ₗ[F] V) (uu : V) + (g : V ≃ₗ[F] V) (rr : V) := by
      rw [← huv]
      exact map_add (g : V ≃ₗ[F] V) (uu : V) (rr : V)
    rw [h1, map_add (planeRot hF a z) ((g : V ≃ₗ[F] V) (uu : V))
      ((g : V ≃ₗ[F] V) (rr : V)), hrot_mem _ (hgU uu uu.2), hrot_perp _ (hgP rr rr.2)]
  have hR : (g : V ≃ₗ[F] V) (planeRot hF a z v) =
      (g : V ≃ₗ[F] V) ((planeLinEquiv hF a z uu : ↥(U a)) : V) + (g : V ≃ₗ[F] V) (rr : V) := by
    have h1 : planeRot hF a z v = ((planeLinEquiv hF a z uu : ↥(U a)) : V) + (rr : V) := by
      rw [← huv, map_add (planeRot hF a z) (uu : V) (rr : V), hrot_mem _ uu.2,
        hrot_perp _ rr.2]
    rw [h1, map_add (g : V ≃ₗ[F] V)]
  have hkey : (g : V ≃ₗ[F] V) ((planeLinEquiv hF a z uu : ↥(U a)) : V) =
      ((planeLinEquiv hF a z ⟨(g : V ≃ₗ[F] V) (uu : V), hgU uu uu.2⟩ : ↥(U a)) : V) := by
    have h := congrArg (fun (f : ↥(U a) ≃ₗ[F] ↥(U a)) => f uu) hcommU
    simp only [LinearEquiv.mul_apply] at h
    rw [← hGcoe (planeLinEquiv hF a z uu), h]
    exact congrArg (fun w : ↥(U a) => ((planeLinEquiv hF a z w : ↥(U a)) : V))
      (Subtype.ext (hGcoe uu))
  show planeRot hF a z ((g : V ≃ₗ[F] V) v) = (g : V ≃ₗ[F] V) (planeRot hF a z v)
  rw [hL, ← hkey, ← hR]

theorem commute_frameTorusFull_of_commute (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    [Fact (Irreducible (OmNsRootGen.framePoly t))]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F V, Module.finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {g : ↥(orthDerived Q)} (hc : ∀ x ∈ E, g * x = x * g) (y : Fin k → normOne t) :
    Commute (frameTorusFull hF hQ hT y) g := by
  classical
  refine Subtype.ext ?_
  have hnoncomm : ((frameTorusFull hF hQ hT y : ↥(orthDerived Q)) : V ≃ₗ[F] V) =
      Finset.univ.noncommProd (fun i => planeRot hF i (y i)) _ := frameTorusFull_coe hF hQ hT y
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hnoncomm]
  exact (Finset.noncommProd_commute (Finset.univ) (fun i => planeRot hF i (y i)) _
    (g : V ≃ₗ[F] V) (fun i _ => (commute_planeRot_of_commute hF hc i (y i)).symm)).symm

section Rigidity

variable [Fact (Irreducible (OmNsRootGen.framePoly t))]

private theorem normOne_pow_card_add_one (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (a : Fin k) (z : normOne t) : z ^ (Nat.card F + 1) = 1 := by
  refine planeRot_injective hF a ?_
  rw [map_pow, planeRot_pow_card_add_one hF a z, map_one]

private theorem normOne_eq_ker (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    normOne t = ((powMonoidHom (Nat.card F + 1) : (FrameField t)ˣ →* (FrameField t)ˣ)).ker := by
  classical
  have hle : normOne t ≤
      ((powMonoidHom (Nat.card F + 1) : (FrameField t)ˣ →* (FrameField t)ˣ)).ker := by
    intro z hz
    refine MonoidHom.mem_ker.mpr ?_
    rw [powMonoidHom_apply]
    simpa using normOne_pow_card_add_one hF a ⟨z, hz⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [natCard_normOne (F := F) (t := t), IsCyclic.card_powMonoidHom_ker]
  exact Nat.gcd_le_right _ (by omega)

private theorem exists_normOne_of_commute (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    {g : ↥(orthDerived Q)} (hc : ∀ x ∈ E, g * x = x * g)
    (hpow : g ^ (Nat.card F + 1) = 1) (a : Fin k) :
    ∃ z : normOne t, ∀ w ∈ U a, (g : V ≃ₗ[F] V) w = planeRot hF a z w := by
  classical
  obtain ⟨hgU, hgU', _⟩ := preserves_plane_of_commute hF hc a
  set G := CFSG.RankThree.PartOne.KCOrthogonal.restrictEquiv (U a) (g : V ≃ₗ[F] V) hgU hgU'
    with hGdef
  have hGcoe : ∀ w : ↥(U a), ((G w : ↥(U a)) : V) = (g : V ≃ₗ[F] V) (w : V) := by
    intro w
    rw [hGdef]
    exact CFSG.RankThree.PartOne.KCOrthogonal.coe_restrictEquiv (U a) (g : V ≃ₗ[F] V) hgU hgU' w
  have hGcent : G ∈ Subgroup.centralizer
      ({planeEquiv hF a} : Set (↥(U a) ≃ₗ[F] ↥(U a))) :=
    restrictEquiv_mem_centralizer hF hc a (hgU := hgU) (hgU' := hgU')
  have hcns : ∀ x : F, ((planeEquiv hF a : ↥(U a) ≃ₗ[F] ↥(U a)) : Module.End F ↥(U a)) ≠
      x • 1 :=
    RelDPlane.not_scalar (Q := Q.comp (U a).subtype) (hF.finrank_eq a) (hF.nondeg a)
      (planeEquiv hF a) (planeEquiv_mem_orthogonalGroup hF a)
      (planeEquiv_eq_self_imp_eq_zero hF a)
  have hGend : (G : Module.End F ↥(U a)) * planeEnd hF a =
      planeEnd hF a * (G : Module.End F ↥(U a)) := by
    have h := (Subgroup.mem_centralizer_iff.mp hGcent) (planeEquiv hF a) (Set.mem_singleton _)
    have h' : ((planeEquiv hF a * G : ↥(U a) ≃ₗ[F] ↥(U a)) : Module.End F ↥(U a)) =
        ((G * planeEquiv hF a : ↥(U a) ≃ₗ[F] ↥(U a)) : Module.End F ↥(U a)) :=
      congrArg (fun e : ↥(U a) ≃ₗ[F] ↥(U a) => (e : Module.End F ↥(U a))) h
    simp only [LinearEquiv.coe_toLinearMap_mul, planeEquiv_toLinearMap] at h'
    exact h'.symm
  set z : FrameField t := (planeFieldEquiv hF a).symm (G (frameU hF a)) with hzdef
  have hzU : planeAlg hF a z (frameU hF a) = G (frameU hF a) := by
    rw [← planeFieldEquiv_apply hF a z, hzdef, LinearEquiv.apply_symm_apply]
  have hzEU : planeAlg hF a z (frameEU hF a) = G (frameEU hF a) := by
    have h1 : (planeAlg hF a z) (planeEnd hF a (frameU hF a)) =
        planeEnd hF a ((planeAlg hF a z) (frameU hF a)) := by
      have h := congrArg (fun (f : Module.End F ↥(U a)) => f (frameU hF a))
        (planeAlg_commute_planeEnd hF a z).eq
      simpa [Module.End.mul_apply] using h
    have h2 : planeEnd hF a (G (frameU hF a)) =
        (G : Module.End F ↥(U a)) (planeEnd hF a (frameU hF a)) := by
      have h := congrArg (fun (f : Module.End F ↥(U a)) => f (frameU hF a)) hGend
      simpa [Module.End.mul_apply] using h.symm
    calc planeAlg hF a z (frameEU hF a)
        = planeAlg hF a z (planeEnd hF a (frameU hF a)) := by rw [planeEnd_frameU]
      _ = planeEnd hF a ((planeAlg hF a z) (frameU hF a)) := h1
      _ = planeEnd hF a (G (frameU hF a)) := by rw [hzU]
      _ = (G : Module.End F ↥(U a)) (planeEnd hF a (frameU hF a)) := h2
      _ = G (frameEU hF a) := by rw [planeEnd_frameU]; rfl
  have hzG : planeAlg hF a z = (G : Module.End F ↥(U a)) := by
    refine LinearMap.ext_on (span_frameU_eq_top hF a) ?_
    intro x hx
    rcases (by simpa using hx : x = frameU hF a ∨ x = frameEU hF a) with rfl | rfl
    · exact hzU
    · exact hzEU
  have hpowV : ((g : V ≃ₗ[F] V)) ^ (Nat.card F + 1) = 1 := by
    have h := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) hpow
    simpa using h
  have hGpow : G ^ (Nat.card F + 1) = 1 := by
    refine LinearEquiv.ext fun w => Subtype.ext ?_
    rw [restrictEquiv_pow_coe (W := U a) (g := (g : V ≃ₗ[F] V)) hgU hgU'
      (Nat.card F + 1) w, hpowV]
    rfl
  have hGcoePow : ∀ m : ℕ, ((G : Module.End F ↥(U a)) ^ m) =
      ((G ^ m : ↥(U a) ≃ₗ[F] ↥(U a)) : Module.End F ↥(U a)) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
        rw [pow_succ, ih, pow_succ, LinearEquiv.coe_toLinearMap_mul]
  have hAlgpow : (planeAlg hF a z) ^ (Nat.card F + 1) = 1 := by
    rw [hzG, hGcoePow, hGpow]
    rfl
  have hzn : z ^ (Nat.card F + 1) = 1 := by
    refine planeAlg_injective hF a ?_
    rw [map_pow, hAlgpow, map_one]
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : Nat.card F + 1 ≠ 0)] at hzn
    exact zero_ne_one hzn
  have hmem : (Units.mk0 z hz0) ^ (Nat.card F + 1) = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_one, Units.val_mk0]
    exact hzn
  have hmemNormOne : (Units.mk0 z hz0) ∈ normOne t := by
    rw [normOne_eq_ker hF a, MonoidHom.mem_ker, powMonoidHom_apply]
    exact hmem
  let zN : normOne t := ⟨Units.mk0 z hz0, hmemNormOne⟩
  refine ⟨zN, fun w hw => ?_⟩
  have hzval : normOneVal (F := F) (t := t) zN = z := rfl
  rw [planeRot_apply_mem hF a zN hw, hzval, hzG]
  exact (hGcoe ⟨w, hw⟩).symm

end Rigidity

theorem mem_range_frameTorusFull_of_commute (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    [Fact (Irreducible (OmNsRootGen.framePoly t))]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F V, Module.finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hdim : Module.finrank F V = 2 * k + 2)
    {f f' : V} (hf : f ∈ polarPerp Q (⨆ j, U j)) (hf' : f' ∈ polarPerp Q (⨆ j, U j))
    (hQf : Q f = 0) (hQf' : Q f' = 0) (hff' : QuadraticMap.polar Q f f' = 1)
    {g : ↥(orthDerived Q)} (hc : ∀ x ∈ E, g * x = x * g)
    (hpow : g ^ (Nat.card F + 1) = 1) :
    g ∈ (frameTorusFull hF hQ hT).range := by
  classical
  set P : Submodule F V := polarPerp Q (⨆ j, U j) with hPdef
  have hgorth : (g : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    CFSG.RankThree.Classical.orthDerived_le_orthogonalGroup Q g.2
  have hgV : ((g : V ≃ₗ[F] V)) ^ (Nat.card F + 1) = 1 := by
    have h := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) hpow
    simpa using h
  have hWfin : Module.finrank F ((⨆ j, U j) : Submodule F V) = 2 * k := by
    have h := (hF.toIsPlaneFrame.toIsPlaneSystem).finrank_biSup (Finset.univ : Finset (Fin k))
    have hsum : (⨆ j ∈ (Finset.univ : Finset (Fin k)), U j) = (⨆ j, U j) := by
      apply le_antisymm
      · refine iSup₂_le fun j _ => le_iSup U j
      · refine iSup_le fun j =>
          le_iSup₂ (f := fun j (_ : j ∈ Finset.univ) => U j) j (Finset.mem_univ j)
    rw [hsum, Finset.card_univ, Fintype.card_fin] at h
    exact h
  have hPfin : Module.finrank F P = 2 := by
    rw [hPdef, finrank_polarPerp hQ, hWfin, hdim]
    omega
  have hplane : ∀ j, (∀ w ∈ U j, (g : V ≃ₗ[F] V) w ∈ U j) ∧
      (∀ w ∈ U j, (g : V ≃ₗ[F] V).symm w ∈ U j) :=
    fun j => ⟨(preserves_plane_of_commute hF hc j).1, (preserves_plane_of_commute hF hc j).2.1⟩
  have hgW : ∀ w ∈ (⨆ j, U j), (g : V ≃ₗ[F] V) w ∈ (⨆ j, U j) := by
    intro w hw
    refine Submodule.iSup_induction U (motive := fun w => (g : V ≃ₗ[F] V) w ∈ (⨆ j, U j)) hw
      (fun j x hx => Submodule.mem_iSup_of_mem j ((hplane j).1 x hx)) ?_ ?_
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro x y hx hy
      rw [map_add]
      exact (⨆ j, U j).add_mem hx hy
  have hgW' : ∀ w ∈ (⨆ j, U j), (g : V ≃ₗ[F] V).symm w ∈ (⨆ j, U j) := by
    intro w hw
    refine Submodule.iSup_induction U
      (motive := fun w => (g : V ≃ₗ[F] V).symm w ∈ (⨆ j, U j)) hw
      (fun j x hx => Submodule.mem_iSup_of_mem j ((hplane j).2 x hx)) ?_ ?_
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro x y hx hy
      rw [map_add]
      exact (⨆ j, U j).add_mem hx hy
  have hPg : ∀ w ∈ P, (g : V ≃ₗ[F] V) w ∈ P := by
    intro w hw
    rw [hPdef, mem_polarPerp_iff] at hw ⊢
    intro y hy
    have hgy : (g : V ≃ₗ[F] V).symm y ∈ (⨆ j, U j) := hgW' y hy
    have hsymm : (g : V ≃ₗ[F] V) ((g : V ≃ₗ[F] V).symm y) = y :=
      LinearEquiv.apply_symm_apply (g : V ≃ₗ[F] V) y
    calc polar Q y ((g : V ≃ₗ[F] V) w)
        = polar Q ((g : V ≃ₗ[F] V) ((g : V ≃ₗ[F] V).symm y)) ((g : V ≃ₗ[F] V) w) := by
          rw [hsymm]
      _ = polar Q ((g : V ≃ₗ[F] V).symm y) w :=
          TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgorth _ _
      _ = 0 := hw _ hgy
  have hPg' : ∀ w ∈ P, (g : V ≃ₗ[F] V).symm w ∈ P := by
    intro w hw
    rw [hPdef, mem_polarPerp_iff] at hw ⊢
    intro y hy
    have hgy : (g : V ≃ₗ[F] V) y ∈ (⨆ j, U j) := hgW y hy
    calc polar Q y ((g : V ≃ₗ[F] V).symm w)
        = polar Q ((g : V ≃ₗ[F] V) y) ((g : V ≃ₗ[F] V) ((g : V ≃ₗ[F] V).symm w)) :=
          (TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgorth y _).symm
      _ = polar Q ((g : V ≃ₗ[F] V) y) w := by
          rw [LinearEquiv.apply_symm_apply]
      _ = 0 := hw _ hgy
  set gP : ↥P ≃ₗ[F] ↥P :=
    CFSG.RankThree.PartOne.KCOrthogonal.restrictEquiv P (g : V ≃ₗ[F] V) hPg hPg' with hgPdef
  have hgPcoe : ∀ w : ↥P, ((gP w : ↥P) : V) = (g : V ≃ₗ[F] V) (w : V) := by
    intro w
    rw [hgPdef]
    exact CFSG.RankThree.PartOne.KCOrthogonal.coe_restrictEquiv P (g : V ≃ₗ[F] V) hPg hPg' w
  have hgPpow : gP ^ (Nat.card F + 1) = 1 := by
    refine LinearEquiv.ext fun w => Subtype.ext ?_
    rw [restrictEquiv_pow_coe (W := P) (g := (g : V ≃ₗ[F] V)) hPg hPg' (Nat.card F + 1) w, hgV]
    rfl
  have hgPorth : gP ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp P.subtype) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro w
    show Q ((gP w : ↥P) : V) = Q (w : V)
    rw [hgPcoe]
    exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hgorth (w : V)
  have hf0 : f ≠ 0 := by
    intro h0
    rw [h0] at hff'
    simp at hff'
  have hspanPair : Submodule.span F ({f, f'} : Set V) = P :=
    OmNsRootGen.span_pair_eq_of_finrank_eq_two (W := P) (by rw [hPdef]; exact hf)
      (by rw [hPdef]; exact hf') hQf hQf' hff' hPfin
  have hPnd : (QuadraticMap.polarBilin (Q.comp P.subtype)).Nondegenerate := by
    refine ((isRefl_polarBilin (Q.comp P.subtype)).nondegenerate_iff_separatingLeft).2 ?_
    intro x hx
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp (by rw [hspanPair]; exact x.2)
    have h1 : polar Q (x : V) f' = 0 := by
      have h := hx ⟨f', hf'⟩
      rwa [QuadraticMap.polarBilin_apply_apply, polar_comp_subtype_cent] at h
    have h2 : polar Q (x : V) f = 0 := by
      have h := hx ⟨f, hf⟩
      rwa [QuadraticMap.polarBilin_apply_apply, polar_comp_subtype_cent] at h
    simp only [← hab, polar_add_left, CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq] at h1
    simp only [← hab, polar_add_left, CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq] at h2
    have ha : a = 0 := by
      rw [CFSG.ClassicalGroups.Orthogonal.polar_self_eq_zero hQf', hff', mul_one, mul_zero,
        add_zero] at h1
      exact h1
    have hb : b = 0 := by
      rw [CFSG.ClassicalGroups.Orthogonal.polar_self_eq_zero hQf, polar_comm Q f' f, hff',
        mul_one, mul_zero, zero_add] at h2
      exact h2
    refine Subtype.ext ?_
    rw [← hab]
    simp [ha, hb]
  have hsing : ∃ v : ↥P, v ≠ 0 ∧ (Q.comp P.subtype) v = 0 :=
    ⟨⟨f, hf⟩, fun h0 => hf0 (congrArg Subtype.val h0), hQf⟩
  have hgPone : gP = 1 :=
    RelDPlane.hyperbolic_isometry_eq_one_of_pow_card_add_one_of_exists_singular
      (Q := Q.comp P.subtype) (K := F) (U := ↥P) hPfin hPnd hsing hgPorth hgPpow
  have hgfixP : ∀ w ∈ P, (g : V ≃ₗ[F] V) w = w := by
    intro w hw
    have h := congrArg (fun (e : ↥P ≃ₗ[F] ↥P) => ((e ⟨w, hw⟩ : ↥P) : V)) hgPone
    simpa [hgPcoe] using h
  choose z hz using fun a => exists_normOne_of_commute hF hc hpow a
  have hagree : ∀ w ∈ (⨆ j, U j),
      ((frameTorusFull hF hQ hT z : ↥(orthDerived Q)) : V ≃ₗ[F] V) w = (g : V ≃ₗ[F] V) w := by
    intro w hw
    refine Submodule.iSup_induction U (motive := fun w =>
      ((frameTorusFull hF hQ hT z : ↥(orthDerived Q)) : V ≃ₗ[F] V) w = (g : V ≃ₗ[F] V) w) hw
      (fun j x hx => ?_) ?_ ?_
    · rw [frameTorusFull_apply_mem hF hQ hT z j hx, hz j x hx]
    · simp
    · intro x y hx hy
      rw [map_add ((frameTorusFull hF hQ hT z : ↥(orthDerived Q)) : V ≃ₗ[F] V) x y,
        map_add (g : V ≃ₗ[F] V) x y, hx, hy]
  have hcompl : IsCompl (⨆ j, U j) P := by
    rw [hPdef]
    exact hF.toIsPlaneFrame.toIsPlaneSystem.isCompl_iSup
  refine ⟨z, ?_⟩
  refine Subtype.ext ?_
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨s, hs, r, hr, hsv⟩ := Submodule.mem_sup.mp (hcompl.sup_eq_top ▸ Submodule.mem_top (x := v))
  rw [← hsv, map_add (g : V ≃ₗ[F] V) s r,
    map_add ((frameTorusFull hF hQ hT z : ↥(orthDerived Q)) : V ≃ₗ[F] V) s r,
    hagree s hs, frameTorusFull_apply_perp hF hQ hT z hr, hgfixP r hr]

end RelDNs

end CFSG.StandardType

end
