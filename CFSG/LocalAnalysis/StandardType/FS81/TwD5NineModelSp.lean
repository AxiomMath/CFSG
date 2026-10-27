module

public import CFSG.Fischer.Classification.Orthogonal2.Local
public import CFSG.LocalAnalysis.StandardType.FS81.OrthParity
public import CFSG.RankThree.PartOne.KC.OrthogonalComponentFacts
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionWork
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExc
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpAMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphFix
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowStepOneMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph

public section

namespace CFSG.StandardType.FrameRoute.FS81

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.Fischer.Classification.Recognition.SymO
open CFSG.Fischer.Classification.Orth2

theorem orthDerived_inf_centralizer_reflect {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {Q : QuadraticForm (ZMod 2) W}
    (hnd : (polarBilin Q).Nondegenerate) {m : ℕ} (hdim : finrank (ZMod 2) W = 2 * m)
    (hm : 4 ≤ m) {v : W} (hv : Q v = 1) :
    IsSimpleGroup ↥(orthDerived Q ⊓
        Subgroup.centralizer ({reflect Q v} : Set (W ≃ₗ[ZMod 2] W))) ∧
      6 ∣ Nat.card ↥(orthDerived Q ⊓
        Subgroup.centralizer ({reflect Q v} : Set (W ≃ₗ[ZMod 2] W))) ∧
      orthDerived Q ⊓ Subgroup.centralizer
        ((orthDerived Q ⊓ Subgroup.centralizer ({reflect Q v} : Set (W ≃ₗ[ZMod 2] W)) :
          Subgroup (W ≃ₗ[ZMod 2] W)) : Set (W ≃ₗ[ZMod 2] W)) = ⊥ := by
  classical
  obtain ⟨y, hyv⟩ := exists_polar_eq_one hnd hv
  set t : TauCeti.QuadraticMap.orthogonalGroup Q :=
    ⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ with htdef
  have ht : ∀ x : W, (t : W ≃ₗ[ZMod 2] W) x = x + polar Q x v • v :=
    fun x => reflect_apply_of_map_eq_one hv x
  set H : Subgroup (W ≃ₗ[ZMod 2] W) :=
    orthDerived Q ⊓ Subgroup.centralizer ({reflect Q v} : Set (W ≃ₗ[ZMod 2] W)) with hH
  have hΩO : orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup
  have htNotMem : (t : W ≃ₗ[ZMod 2] W) ∉ orthDerived Q := by
    change reflect Q v ∉ orthDerived Q
    intro hmem
    have h1 :=
      CFSG.RankThree.PartOne.KCOrthogonal.dicksonHom_eq_one_of_mem_orthDerived hnd hmem
    have h2 : CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hnd
        ⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ =
        Multiplicative.ofAdd (1 : ZMod 2) :=
      CFSG.RankThree.PartOne.KCOrthogonal.dicksonHom_reflect hnd
        (by rw [hv]; exact one_ne_zero)
    have h1' : CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hnd
        (⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ :
          TauCeti.QuadraticMap.orthogonalGroup Q) = 1 := by
      convert h1 using 1
    rw [h1'] at h2
    exact zero_ne_one (Multiplicative.ofAdd.injective (by simpa using h2) : (0 : ZMod 2) = 1)
  have hrefl : (polarBilin Q).IsRefl := by
    intro a b hab
    rw [polarBilin_apply_apply] at hab ⊢
    rwa [QuadraticMap.polar_comm]
  have hneg : ∀ x : W, -x = x :=
    fun x => neg_eq_self_of_two_eq_zero (K := ZMod 2) (V := W) (by decide) x
  have hvy : bil Q v y = 1 := by rw [bil_apply, polar_comm]; exact hyv
  obtain ⟨-, hsplit⟩ :=
    CFSG.ClassicalGroups.Alternating.alternating_hyperbolic_splitting (bil_isAlt Q) hnd
      (ne_zero_of_map_eq_one hv)
  obtain ⟨-, -, -, -, hndW, hdimW⟩ := hsplit y hvy
  have hdim₀ : finrank (ZMod 2) (perp Q v y) = 2 * (m - 1) := by
    rw [hdimW, hdim]
    omega
  have hAlt₀ : ((bil Q).restrict (perp Q v y)).IsAlt :=
    fun x => (bil_isAlt Q).self_eq_zero x
  have hW₀ne : ∃ w : perp Q v y, w ≠ 0 := by
    have : Nontrivial (perp Q v y) :=
      Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
    exact exists_ne 0
  have hS : IsSimpleGroup
      (TauCeti.BilinForm.isometryGroup ((bil Q).restrict (perp Q v y))) :=
    isSimpleGroup_isometryGroup _ hAlt₀ hndW hdim₀ (by omega)
  let tC : Subgroup.centralizer ({t} : Set (TauCeti.QuadraticMap.orthogonalGroup Q)) :=
    ⟨⟨(t : W ≃ₗ[ZMod 2] W), t.2⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hρt : rho hnd hv hyv t ht tC = 1 := by
    refine Subtype.ext (LinearEquiv.ext fun w => ?_)
    rw [rho_apply, restr_apply]
    have hw : polar Q (w : W) v = 0 := by
      rw [polar_comm]
      exact (mem_perp.mp w.2).1
    have htw : (t : W ≃ₗ[ZMod 2] W) (w : W) = (w : W) := by
      rw [ht, hw, zero_smul, add_zero]
    change (proj hyv) ((t : W ≃ₗ[ZMod 2] W) (w : W)) = (w : perp Q v y)
    rw [htw, proj_coe]
  let ψ : H →* Subgroup.centralizer
      ({t} : Set (TauCeti.QuadraticMap.orthogonalGroup Q)) :=
  { toFun := fun x =>
      ⟨⟨x.1, hΩO x.2.1⟩,
        Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext (by
          have hx : x.1 * reflect Q v = reflect Q v * x.1 :=
            Subgroup.mem_centralizer_singleton_iff.mp x.2.2
          simpa using hx))⟩
    map_one' := Subtype.ext (Subtype.ext rfl)
    map_mul' := fun a b => Subtype.ext (Subtype.ext rfl) }
  have hψval : ∀ x : H,
      (((ψ x : Subgroup.centralizer ({t} : Set (TauCeti.QuadraticMap.orthogonalGroup Q))) :
        TauCeti.QuadraticMap.orthogonalGroup Q) : W ≃ₗ[ZMod 2] W) =
      (x : W ≃ₗ[ZMod 2] W) := fun x => rfl
  have hψinj : Function.Injective ψ := fun a b hab =>
    Subtype.ext (congrArg
      (fun z : Subgroup.centralizer ({t} : Set (TauCeti.QuadraticMap.orthogonalGroup Q)) =>
        ((z : TauCeti.QuadraticMap.orthogonalGroup Q) : W ≃ₗ[ZMod 2] W)) hab)
  let Φ : H →* TauCeti.BilinForm.isometryGroup ((bil Q).restrict (perp Q v y)) :=
    (rho hnd hv hyv t ht).comp ψ
  have hΦsurj : Function.Surjective Φ := by
    intro σ
    obtain ⟨c, hc⟩ := rho_surjective hnd hv hyv t ht hS hW₀ne σ
    by_cases hcΩ : (c : W ≃ₗ[ZMod 2] W) ∈ orthDerived Q
    · have hc_cent : (c : W ≃ₗ[ZMod 2] W) ∈ Subgroup.centralizer
          ({reflect Q v} : Set (W ≃ₗ[ZMod 2] W)) :=
        Subgroup.mem_centralizer_singleton_iff.mpr (by
          have hcc : (c : W ≃ₗ[ZMod 2] W) * (t : W ≃ₗ[ZMod 2] W) =
              (t : W ≃ₗ[ZMod 2] W) * (c : W ≃ₗ[ZMod 2] W) :=
            congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp c.2)
          simpa using hcc)
      refine ⟨⟨c.1, ⟨hcΩ, hc_cent⟩⟩, ?_⟩
      have hψ : ψ ⟨c.1, ⟨hcΩ, hc_cent⟩⟩ = c := Subtype.ext (Subtype.ext rfl)
      have hΦx : Φ ⟨c.1, ⟨hcΩ, hc_cent⟩⟩ =
          rho hnd hv hyv t ht (ψ ⟨c.1, ⟨hcΩ, hc_cent⟩⟩) := rfl
      rw [hΦx, hψ, hc]
    · have htinv : (t : W ≃ₗ[ZMod 2] W)⁻¹ = t := by
        change (reflect Q v)⁻¹ = reflect Q v
        exact reflect_inv Q v
      have hmem : (c : W ≃ₗ[ZMod 2] W) * (t : W ≃ₗ[ZMod 2] W) ∈ orthDerived Q := by
        have h := mul_inv_mem_orthDerived_of_not_mem hnd (by omega)
          (g := (c : W ≃ₗ[ZMod 2] W)) (h := (t : W ≃ₗ[ZMod 2] W))
          c.1.2 t.2 hcΩ htNotMem
        rwa [htinv] at h
      have hcent : ((c : W ≃ₗ[ZMod 2] W) * (t : W ≃ₗ[ZMod 2] W)) * reflect Q v =
          reflect Q v * ((c : W ≃ₗ[ZMod 2] W) * (t : W ≃ₗ[ZMod 2] W)) := by
        have hcc : (c : W ≃ₗ[ZMod 2] W) * (t : W ≃ₗ[ZMod 2] W) =
            (t : W ≃ₗ[ZMod 2] W) * (c : W ≃ₗ[ZMod 2] W) :=
          congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp c.2)
        have hrr : (t : W ≃ₗ[ZMod 2] W) * (t : W ≃ₗ[ZMod 2] W) = 1 := by
          change reflect Q v * reflect Q v = 1
          exact reflect_mul_self Q v
        change ((c : W ≃ₗ[ZMod 2] W) * (t : W ≃ₗ[ZMod 2] W)) *
            (t : W ≃ₗ[ZMod 2] W) =
          (t : W ≃ₗ[ZMod 2] W) *
            ((c : W ≃ₗ[ZMod 2] W) * (t : W ≃ₗ[ZMod 2] W))
        rw [mul_assoc, hrr, mul_one, hcc, ← mul_assoc, hrr, one_mul]
      have hε_cent : ((c : W ≃ₗ[ZMod 2] W) * (t : W ≃ₗ[ZMod 2] W)) ∈
          Subgroup.centralizer ({reflect Q v} : Set (W ≃ₗ[ZMod 2] W)) :=
        Subgroup.mem_centralizer_singleton_iff.mpr hcent
      refine ⟨⟨(c : W ≃ₗ[ZMod 2] W) * (t : W ≃ₗ[ZMod 2] W), ⟨hmem, hε_cent⟩⟩, ?_⟩
      have hψ : ψ ⟨(c : W ≃ₗ[ZMod 2] W) * (t : W ≃ₗ[ZMod 2] W),
            ⟨hmem, hε_cent⟩⟩ = c * tC :=
        Subtype.ext (Subtype.ext rfl)
      have hΦx : Φ ⟨(c : W ≃ₗ[ZMod 2] W) * (t : W ≃ₗ[ZMod 2] W),
            ⟨hmem, hε_cent⟩⟩ =
          rho hnd hv hyv t ht (ψ ⟨(c : W ≃ₗ[ZMod 2] W) * (t : W ≃ₗ[ZMod 2] W),
            ⟨hmem, hε_cent⟩⟩) := rfl
      rw [hΦx, hψ, map_mul, hc, hρt, mul_one]
  have hΦinj : Function.Injective Φ := by
    intro a b hab
    have hd : ψ (a * b⁻¹) ∈ (rho hnd hv hyv t ht).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_inv]
      rw [show rho hnd hv hyv t ht (ψ a) = Φ a from rfl,
        show rho hnd hv hyv t ht (ψ b) = Φ b from rfl, hab, mul_inv_cancel]
    rcases eq_one_or_eq_of_mem_ker_rho hnd hv hyv t ht hd with h | h
    · have hone : a * b⁻¹ = 1 := hψinj (Subtype.ext h)
      rwa [mul_eq_one_iff_eq_inv, inv_inv] at hone
    · exfalso
      have hval : ((a * b⁻¹ : H) : W ≃ₗ[ZMod 2] W) = reflect Q v := by
        have := congrArg (fun z : TauCeti.QuadraticMap.orthogonalGroup Q =>
          (z : W ≃ₗ[ZMod 2] W)) h
        have htcoe : (t : W ≃ₗ[ZMod 2] W) = reflect Q v := rfl
        simpa [htcoe, hψval] using this
      have hmemΩ : ((a * b⁻¹ : H) : W ≃ₗ[ZMod 2] W) ∈ orthDerived Q := by
        simpa [hψval] using (a * b⁻¹).2.1
      rw [hval] at hmemΩ
      exact htNotMem hmemΩ
  let e : H ≃* TauCeti.BilinForm.isometryGroup ((bil Q).restrict (perp Q v y)) :=
    MulEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩
  have hHsimple : IsSimpleGroup H := by
    exact @MulEquiv.isSimpleGroup _ _ _ _ hS e
  have hcenter : Subgroup.center H = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    have hmap : e g ∈ Subgroup.center
        (TauCeti.BilinForm.isometryGroup ((bil Q).restrict (perp Q v y))) := by
      rw [Subgroup.mem_center_iff] at hg ⊢
      intro s
      obtain ⟨s', rfl⟩ := e.surjective s
      rw [← map_mul, ← map_mul, hg s']
    rw [center_isometryGroup_eq_bot hAlt₀ hndW] at hmap
    exact e.injective (by rw [map_one]; exact hmap)
  have hcard : Nat.card H = 2 ^ ((m - 1) ^ 2) *
      ∏ j ∈ Finset.Icc 1 (m - 1), (2 ^ (2 * j) - 1) := by
    rw [Nat.card_congr e.toEquiv]
    exact card_isometryGroup_two _ hAlt₀ hndW hdim₀
  have h6 : 6 ∣ Nat.card H := by
    rw [hcard]
    have h2 : 2 ∣ 2 ^ ((m - 1) ^ 2) :=
      dvd_pow_self 2 (by have : 0 < (m - 1) ^ 2 := pow_pos (by omega) 2; omega)
    have h3 : 3 ∣ ∏ j ∈ Finset.Icc 1 (m - 1), (2 ^ (2 * j) - 1) := by
      have hmem : 1 ∈ Finset.Icc 1 (m - 1) := by
        rw [Finset.mem_Icc]
        omega
      have h := Finset.dvd_prod_of_mem (fun j : ℕ => 2 ^ (2 * j) - 1) hmem
      simpa using h
    have h6' := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 2 3)
      (dvd_mul_of_dvd_left h2 _) (dvd_mul_of_dvd_right h3 _)
    simpa using h6'
  have hfix : ∀ z : W, (∀ h ∈ H, (h : W ≃ₗ[ZMod 2] W) z = z) →
      z ∈ Submodule.span (ZMod 2) {v} := by
    intro z hz
    obtain ⟨w, hw0⟩ := hW₀ne
    set u : W := lift Q v w with hu
    have huQ : Q u = 1 := map_lift hv w
    have huv : polar Q u v = 0 := polar_lift w
    have hu_ne_v : u ≠ v := by
      intro h
      have h2 := proj_lift (Q := Q) hyv w
      rw [← hu, h, proj_left] at h2
      exact hw0 h2.symm
    have hpair : ∀ a b : W, Q a = 1 → Q b = 1 → polar Q a v = 0 → polar Q b v = 0 →
        a ≠ b → (reflect Q a * reflect Q b : W ≃ₗ[ZMod 2] W) ∈ H := by
      intro a b ha hb hav hbv hab
      refine ⟨?_, ?_⟩
      · exact CFSG.RankThree.Literature.FSmith.reflect_mul_reflect_mem_commutator hnd
          (by omega) ha hb
      · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        show (reflect Q a * reflect Q b) * reflect Q v =
          reflect Q v * (reflect Q a * reflect Q b)
        rw [mul_assoc, (reflect_mul_comm_iff hb hv).mpr hbv, ← mul_assoc,
          (reflect_mul_comm_iff ha hv).mpr hav, mul_assoc]
    have hexp : ∀ a b : W, Q a = 1 → Q b = 1 → polar Q a v = 0 → polar Q b v = 0 →
        a ≠ b →
        polar Q z b • b + (polar Q z a + polar Q z b * polar Q b a) • a = 0 := by
      intro a b ha hb hav hbv hab
      have hzab := hz _ (hpair a b ha hb hav hbv hab)
      rw [LinearEquiv.mul_apply, reflect_apply_of_map_eq_one hb,
        reflect_apply_of_map_eq_one ha] at hzab
      have hcoef : polar Q (z + polar Q z b • b) a =
          polar Q z a + polar Q z b * polar Q b a := by
        rw [polar_add_left, polar_smul_left, smul_eq_mul]
      rw [hcoef] at hzab
      rw [add_assoc] at hzab
      exact add_left_cancel (hzab.trans (add_zero z).symm)
    have hcoeff : ∀ a b : W, Q a = 1 → Q b = 1 → polar Q a v = 0 → polar Q b v = 0 →
        a ≠ b → polar Q z a = 0 ∧ polar Q z b = 0 := by
      intro a b ha hb hav hbv hab
      have hzero := hexp a b ha hb hav hbv hab
      have hlin : LinearIndependent (ZMod 2) ![b, a] := by
        rw [LinearIndependent.pair_iff]
        intro s t hst
        have ha0 : a ≠ 0 := ne_zero_of_map_eq_one ha
        have hb0 : b ≠ 0 := ne_zero_of_map_eq_one hb
        rcases zmod_two_eq_zero_or_eq_one s with hs | hs <;>
          rcases zmod_two_eq_zero_or_eq_one t with ht | ht
        · rw [hs, ht]
          exact ⟨rfl, rfl⟩
        · rw [hs, ht, zero_smul, zero_add, one_smul] at hst
          exact absurd hst ha0
        · rw [hs, ht, one_smul, zero_smul, add_zero] at hst
          exact absurd hst hb0
        · rw [hs, ht, one_smul, one_smul] at hst
          have hab' : a = b := by
            have h : a = -b := add_eq_zero_iff_eq_neg'.mp hst
            rwa [hneg b] at h
          exact absurd hab' hab
      obtain ⟨hzb0, hc0⟩ := LinearIndependent.pair_iff.mp hlin (polar Q z b)
        (polar Q z a + polar Q z b * polar Q b a) hzero
      refine ⟨?_, hzb0⟩
      rw [hzb0, zero_mul, add_zero] at hc0
      exact hc0
    have hzv : polar Q z v = 0 :=
      (hcoeff u v huQ hv huv (polar_self_zmod_two v) hu_ne_v).2
    have hmain : ∀ p : W, polar Q v p = 0 → polar Q z p = 0 := by
      intro p hvp
      have hpv : polar Q p v = 0 := by rwa [polar_comm]
      by_cases hpQ : Q p = 1
      · by_cases hpv_eq : p = v
        · rw [hpv_eq]
          exact hzv
        · exact (hcoeff p v hpQ hv hpv (polar_self_zmod_two v) hpv_eq).1
      · have hpQ0 : Q p = 0 := by
          rcases zmod_two_eq_zero_or_eq_one (Q p) with h | h
          · exact h
          · exact absurd h hpQ
        by_cases hp0 : p = 0
        · rw [hp0]
          simp
        · have hpvQ : Q (p + v) = 1 := by
            rw [QuadraticMap.map_add (⇑Q) p v, hpQ0, hv, hpv]
            norm_num
          have hpvperp : polar Q (p + v) v = 0 := by
            rw [polar_add_left, hpv, polar_self_zmod_two, add_zero]
          have hpv_ne : p + v ≠ v := by
            intro h
            exact hp0 (by
              have := congrArg (fun q => q - v) h
              simpa using this)
          have h1 : polar Q z (p + v) = 0 :=
            (hcoeff (p + v) v hpvQ hv hpvperp (polar_self_zmod_two v) hpv_ne).1
          rw [polar_add_right, hzv, add_zero] at h1
          exact h1
    have hzorth : z ∈ LinearMap.BilinForm.orthogonal (polarBilin Q)
        (LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span (ZMod 2) {v})) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro p hp
      have hvp : polar Q v p = 0 :=
        (LinearMap.BilinForm.mem_orthogonal_iff.mp hp) v
          (Submodule.subset_span (Set.mem_singleton v))
      have hzp : polar Q z p = 0 := hmain p hvp
      rw [polarBilin_apply_apply, polar_comm]
      exact hzp
    have horth := LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl
      (Submodule.span (ZMod 2) {v})
    rwa [horth] at hzorth
  have hcenterΩ : orthDerived Q ⊓ Subgroup.centralizer
      ((H : Subgroup (W ≃ₗ[ZMod 2] W)) : Set (W ≃ₗ[ZMod 2] W)) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    have hgΩ : (g : W ≃ₗ[ZMod 2] W) ∈ orthDerived Q := hg.1
    have hgC : (g : W ≃ₗ[ZMod 2] W) ∈
        Subgroup.centralizer ((H : Subgroup (W ≃ₗ[ZMod 2] W)) :
          Set (W ≃ₗ[ZMod 2] W)) := hg.2
    have hgO : (g : W ≃ₗ[ZMod 2] W) ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hΩO hgΩ
    have hgv_fix : (g : W ≃ₗ[ZMod 2] W) v ∈ Submodule.span (ZMod 2) {v} := by
      refine hfix ((g : W ≃ₗ[ZMod 2] W) v) ?_
      intro h hh
      have hcomm : (h : W ≃ₗ[ZMod 2] W) * (g : W ≃ₗ[ZMod 2] W) =
          (g : W ≃ₗ[ZMod 2] W) * (h : W ≃ₗ[ZMod 2] W) :=
        Subgroup.mem_centralizer_iff.mp hgC h hh
      have hhv : (h : W ≃ₗ[ZMod 2] W) v = v :=
        apply_eq_self_of_commute hnd hv
          (t := reflect Q v) (g := (h : W ≃ₗ[ZMod 2] W))
          (fun x => reflect_apply_of_map_eq_one hv x)
          (Subgroup.mem_centralizer_singleton_iff.mp hh.2)
      calc (h : W ≃ₗ[ZMod 2] W) ((g : W ≃ₗ[ZMod 2] W) v)
          = ((h : W ≃ₗ[ZMod 2] W) * (g : W ≃ₗ[ZMod 2] W)) v := rfl
        _ = ((g : W ≃ₗ[ZMod 2] W) * (h : W ≃ₗ[ZMod 2] W)) v := by rw [hcomm]
        _ = (g : W ≃ₗ[ZMod 2] W) ((h : W ≃ₗ[ZMod 2] W) v) := rfl
        _ = (g : W ≃ₗ[ZMod 2] W) v := by rw [hhv]
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hgv_fix
    have hgQ : Q ((g : W ≃ₗ[ZMod 2] W) v) = 1 := by
      rw [map_of_mem hgO, hv]
    have hc1 : c = 1 := by
      rcases zmod_two_eq_zero_or_eq_one c with h | h
      · exfalso
        rw [h, zero_smul] at hc
        rw [← hc, QuadraticMap.map_zero] at hgQ
        exact zero_ne_one hgQ
      · exact h
    have hgv : (g : W ≃ₗ[ZMod 2] W) v = v := by
      rw [← hc, hc1, one_smul]
    have hconj : (g : W ≃ₗ[ZMod 2] W) * reflect Q v * (g : W ≃ₗ[ZMod 2] W)⁻¹ =
        reflect Q v := by
      rw [reflect_conj hgO v, hgv]
    have hcommr : (g : W ≃ₗ[ZMod 2] W) * reflect Q v =
        reflect Q v * (g : W ≃ₗ[ZMod 2] W) := by
      calc (g : W ≃ₗ[ZMod 2] W) * reflect Q v
          = (g : W ≃ₗ[ZMod 2] W) * reflect Q v * (g : W ≃ₗ[ZMod 2] W)⁻¹ *
              (g : W ≃ₗ[ZMod 2] W) := by group
        _ = reflect Q v * (g : W ≃ₗ[ZMod 2] W) := by rw [hconj]
    have hgH : (g : W ≃ₗ[ZMod 2] W) ∈ H :=
      ⟨hgΩ, Subgroup.mem_centralizer_singleton_iff.mpr hcommr⟩
    have hgcenter : (⟨(g : W ≃ₗ[ZMod 2] W), hgH⟩ : H) ∈ Subgroup.center H := by
      rw [Subgroup.mem_center_iff]
      intro h
      refine Subtype.ext ?_
      exact Subgroup.mem_centralizer_iff.mp hgC (h : W ≃ₗ[ZMod 2] W) h.2
    have hone : (⟨(g : W ≃ₗ[ZMod 2] W), hgH⟩ : H) = 1 :=
      Subgroup.mem_bot.mp (hcenter ▸ hgcenter)
    have hg1 : (g : W ≃ₗ[ZMod 2] W) = 1 := by
      simpa using congrArg (fun z : H => (z : W ≃ₗ[ZMod 2] W)) hone
    exact hg1
  exact ⟨hHsimple, h6, hcenterΩ⟩

end CFSG.StandardType.FrameRoute.FS81

end
