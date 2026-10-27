module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Solvable
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotPositionBasic
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7Split
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6B3
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public section

namespace CFSG.StandardType.OddLayerCentre

open Subgroup

variable {G : Type*} [Group G]

theorem le_of_perfect_of_centralizes_of_split {V C E : Subgroup G} (hVC : V ⊓ C = ⊥)
    (hE : ∀ e ∈ E, ∃ v ∈ V, ∃ c ∈ C, e = v * c)
    (hEV : E ≤ centralizer (V : Set G)) (hperf : ⁅E, E⁆ = E) (hVs : Group.IsSolvable V) :
    E ≤ C := by
  classical
  have uniq : ∀ {v v' c c' : G}, v ∈ V → v' ∈ V → c ∈ C → c' ∈ C → v * c = v' * c' →
      v = v' := by
    intro v v' c c' hv hv' hc hc' h
    have h1 : v'⁻¹ * v = c' * c⁻¹ := by
      calc v'⁻¹ * v = v'⁻¹ * (v * c) * c⁻¹ := by group
        _ = v'⁻¹ * (v' * c') * c⁻¹ := by rw [h]
        _ = c' * c⁻¹ := by group
    have hmem : v'⁻¹ * v ∈ V ⊓ C :=
      ⟨V.mul_mem (V.inv_mem hv') hv, h1 ▸ C.mul_mem hc' (C.inv_mem hc)⟩
    rw [hVC, Subgroup.mem_bot] at hmem
    calc v = v' * (v'⁻¹ * v) := by group
      _ = v' := by rw [hmem, mul_one]
  choose ν hνV c hcC hνc using hE
  have key : ∀ (e₁ : G) (h₁ : e₁ ∈ E) (e₂ : G) (h₂ : e₂ ∈ E),
      ν (e₁ * e₂) (E.mul_mem h₁ h₂) = ν e₂ h₂ * ν e₁ h₁ := by
    intro e₁ h₁ e₂ h₂
    have hcomm : ν e₂ h₂ * e₁ = e₁ * ν e₂ h₂ :=
      (Subgroup.mem_centralizer_iff.mp (hEV h₁)) _ (hνV e₂ h₂)
    have hdec : e₁ * e₂ = (ν e₂ h₂ * ν e₁ h₁) * (c e₁ h₁ * c e₂ h₂) := by
      have h1 := hνc e₁ h₁
      have h2 := hνc e₂ h₂
      have : c e₁ h₁ = (ν e₁ h₁)⁻¹ * e₁ := by
        rw [eq_inv_mul_iff_mul_eq]; exact h1.symm
      rw [this]
      calc e₁ * e₂ = e₁ * (ν e₂ h₂ * c e₂ h₂) := by rw [← h2]
        _ = (ν e₂ h₂ * e₁) * c e₂ h₂ := by rw [hcomm]; group
        _ = ν e₂ h₂ * ν e₁ h₁ * ((ν e₁ h₁)⁻¹ * e₁ * c e₂ h₂) := by group
    exact (uniq (hνV _ _) (V.mul_mem (hνV e₂ h₂) (hνV e₁ h₁)) (hcC _ _)
      (C.mul_mem (hcC e₁ h₁) (hcC e₂ h₂)) ((hνc _ _).symm.trans hdec))
  let f : E →* V :=
    { toFun := fun e => ⟨(ν e.1 e.2)⁻¹, V.inv_mem (hνV _ _)⟩
      map_one' := by
        ext
        have h := uniq (hνV 1 E.one_mem) V.one_mem (hcC 1 E.one_mem) C.one_mem
          ((hνc 1 E.one_mem).symm.trans (by simp : (1 : G) = 1 * 1))
        simp [h]
      map_mul' := by
        intro x y
        ext
        simp only [Subgroup.coe_mul]
        rw [key x.1 x.2 y.1 y.2]
        group }
  have htop : ∀ n, derivedSeries E n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [derivedSeries_succ, ih]
      have hmap : (⁅(⊤ : Subgroup E), (⊤ : Subgroup E)⁆ : Subgroup E).map E.subtype = E := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hperf]
      apply Subgroup.map_injective E.subtype_injective
      rw [hmap, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  obtain ⟨n, hn⟩ := hVs.solvable
  have hf : ∀ e : E, f e = 1 := by
    intro e
    have h := map_derivedSeries_le_derivedSeries f n
    rw [htop n, hn] at h
    exact (Subgroup.mem_bot.mp (h ⟨e, Subgroup.mem_top e, rfl⟩))
  intro e he
  have h1 : (ν e he)⁻¹ = 1 := congrArg Subtype.val (hf ⟨e, he⟩)
  have h2 : ν e he = 1 := inv_eq_one.mp h1
  rw [hνc e he, h2, one_mul]
  exact hcC e he

theorem central_involution_trivial_of_split [Finite G] {X E : Subgroup G} (hEX : E ≤ X)
    (hEn : X ≤ normalizer (E : Set G)) (hperf : ⁅E, E⁆ = E)
    (hcent : ∀ V : Subgroup G, IsPGroup 2 V → V ≤ X → X ≤ normalizer (V : Set G) →
      E ≤ centralizer (V : Set G))
    (hBT : ∀ U₀ : Subgroup G, U₀ ≠ ⊥ → IsPGroup 2 U₀ → U₀ ≤ X → X ≤ normalizer (U₀ : Set G) →
      ∃ Q C : Subgroup G, U₀ ≤ Q ∧ IsPGroup 2 Q ∧ X ≤ normalizer (Q : Set G) ∧ Q ⊓ C = ⊥ ∧
        ∀ x ∈ X, ∃ u ∈ Q, ∃ c ∈ C ⊓ X, x = u * c)
    {z : G} (hzE : z ∈ E) (hzc : ∀ e ∈ E, z * e = e * z) (hz2 : z ^ 2 = 1) : z = 1 := by
  classical
  by_contra hz1
  let U₀ : Subgroup G :=
    { carrier := {x | x ∈ E ∧ (∀ e ∈ E, x * e = e * x) ∧ x ^ 2 = 1}
      one_mem' := ⟨E.one_mem, by simp, by simp⟩
      mul_mem' := by
        rintro x y ⟨hx, hxc, hx2⟩ ⟨hy, hyc, hy2⟩
        refine ⟨E.mul_mem hx hy, fun e he => ?_, ?_⟩
        · rw [mul_assoc, hyc e he, ← mul_assoc, hxc e he, mul_assoc]
        · have hxy : x * y = y * x := hxc y hy
          rw [(Commute.mul_pow hxy 2), hx2, hy2, one_mul]
      inv_mem' := by
        rintro x ⟨hx, hxc, hx2⟩
        refine ⟨E.inv_mem hx, fun e he => ?_, by rw [inv_pow, hx2, inv_one]⟩
        have h := hxc e he
        calc x⁻¹ * e = x⁻¹ * (e * x) * x⁻¹ := by group
          _ = x⁻¹ * (x * e) * x⁻¹ := by rw [h]
          _ = e * x⁻¹ := by group }
  have hU₀p : IsPGroup 2 U₀ := fun x => ⟨1, by
    have := x.2.2.2
    ext; simpa using this⟩
  have hU₀X : U₀ ≤ X := fun x hx => hEX hx.1
  have hU₀n : X ≤ normalizer (U₀ : Set G) := by
    intro g hg
    rw [mem_normalizer_iff]
    have hgE := (mem_normalizer_iff.mp (hEn hg))
    have hgE' := (mem_normalizer_iff.mp (inv_mem (hEn hg)))
    intro x
    constructor
    · rintro ⟨hx, hxc, hx2⟩
      refine ⟨(hgE x).mp hx, fun e he => ?_, by rw [conj_pow, hx2]; group⟩
      have he' : g⁻¹ * e * g⁻¹⁻¹ ∈ E := (hgE' e).mp he
      have h := hxc _ he'
      calc g * x * g⁻¹ * e = g * (x * (g⁻¹ * e * g⁻¹⁻¹)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * e * g⁻¹⁻¹) * x) * g⁻¹ := by rw [h]
        _ = e * (g * x * g⁻¹) := by group
    · rintro ⟨hx, hxc, hx2⟩
      have hx' : x ∈ E := by
        have := (hgE' (g * x * g⁻¹)).mp hx
        simpa [mul_assoc] using this
      refine ⟨hx', fun e he => ?_, ?_⟩
      · have he' : g * e * g⁻¹ ∈ E := (hgE e).mp he
        have h := hxc _ he'
        have h2 : g * (x * e) * g⁻¹ = g * (e * x) * g⁻¹ := by
          calc g * (x * e) * g⁻¹ = g * x * g⁻¹ * (g * e * g⁻¹) := by group
            _ = g * e * g⁻¹ * (g * x * g⁻¹) := h
            _ = g * (e * x) * g⁻¹ := by group
        simpa using h2
      · have : g * x ^ 2 * g⁻¹ = 1 := by rw [← conj_pow, hx2]
        simpa using this
  have hU₀ne : U₀ ≠ ⊥ := by
    intro h
    have : z ∈ U₀ := ⟨hzE, hzc, hz2⟩
    rw [h, Subgroup.mem_bot] at this
    exact hz1 this
  obtain ⟨Q, C, hU₀Q, hQp, hXQ, hQC, hdec⟩ := hBT U₀ hU₀ne hU₀p hU₀X hU₀n
  set V : Subgroup G := Q ⊓ X with hV
  have hVp : IsPGroup 2 V := hQp.to_le inf_le_left
  have hVn : X ≤ normalizer (V : Set G) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    have h1 := (mem_normalizer_iff.mp (hXQ hg)) x
    have h2 := (mem_normalizer_iff.mp (Subgroup.le_normalizer (H := X) hg)) x
    simp only [hV, Subgroup.mem_inf]
    exact ⟨fun ⟨a, b⟩ => ⟨h1.mp a, h2.mp b⟩, fun ⟨a, b⟩ => ⟨h1.mpr a, h2.mpr b⟩⟩
  have hEV : E ≤ centralizer (V : Set G) := hcent V hVp inf_le_right hVn
  have hVs : Group.IsSolvable V := by
    haveI : Group.IsNilpotent V := hVp.isNilpotent
    infer_instance
  have hEC : E ≤ C ⊓ X := by
    refine le_of_perfect_of_centralizes_of_split (V := V) (C := C ⊓ X) ?_ ?_ hEV hperf hVs
    · rw [eq_bot_iff]
      rintro x ⟨⟨hxQ, -⟩, hxC, -⟩
      have : x ∈ Q ⊓ C := ⟨hxQ, hxC⟩
      rwa [hQC] at this
    · intro e he
      obtain ⟨u, hu, c, hc, hec⟩ := hdec e (hEX he)
      have huX : u ∈ X := by
        have : u = e * c⁻¹ := by rw [hec]; group
        rw [this]; exact X.mul_mem (hEX he) (X.inv_mem hc.2)
      exact ⟨u, ⟨hu, huX⟩, c, hc, hec⟩
  have hzV : z ∈ Q ⊓ C := ⟨hU₀Q ⟨hzE, hzc, hz2⟩, (hEC hzE).1⟩
  rw [hQC, Subgroup.mem_bot] at hzV
  exact hz1 hzV

theorem exists_fixed_complement_split [Finite G] {A Q M P : Subgroup G} (hQp : IsPGroup 2 Q)
    (hA : Odd (Nat.card A)) (hAP : A ≤ P) (hQP : Q ≤ P) (hPQ : P ≤ normalizer (Q : Set G))
    (hMP : M ≤ P) (hQM : Q ⊓ M = ⊥) (hdecP : ∀ x ∈ P, ∃ u ∈ Q, ∃ m ∈ M, x = u * m) :
    ∃ C : Subgroup G, Q ⊓ C = ⊥ ∧
      ∀ x ∈ P, x ∈ centralizer (A : Set G) →
        ∃ u ∈ Q, ∃ c ∈ C ⊓ centralizer (A : Set G), x = u * c := by
  classical
  set Z : Subgroup G := (Q ⊔ A) ⊓ M with hZ
  have hQAP : Q ⊔ A ≤ P := sup_le hQP hAP
  have hQA : Q ⊓ A = ⊥ := by
    rw [← disjoint_iff, Subgroup.disjoint_def]
    intro x hxQ hxA
    obtain ⟨k, hk⟩ := hQp ⟨x, hxQ⟩
    have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
      simpa using congrArg Subtype.val hk)
    have h2 : orderOf x ∣ Nat.card A := Subgroup.orderOf_dvd_natCard A hxA
    have h3 : Nat.Coprime (2 ^ k) (Nat.card A) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hA)
    have : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes h3 h1 h2
    exact orderOf_eq_one_iff.mp this
  have hQZ : Q ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ Q ⊓ M := ⟨hx.1, hx.2.2⟩
    rwa [hQM] at this
  have hA2 : ¬ 2 ∣ Nat.card A := by
    rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.mpr hA
  have hsup : Q ⊔ Z = Q ⊔ A := by
    apply le_antisymm
    · exact sup_le le_sup_left (inf_le_left)
    · refine sup_le le_sup_left (fun a ha => ?_)
      obtain ⟨u, hu, m, hm, ham⟩ := hdecP a (hAP ha)
      have hmQA : m ∈ Q ⊔ A := by
        have : m = u⁻¹ * a := by rw [ham]; group
        rw [this]
        exact (Q ⊔ A).mul_mem (Subgroup.mem_sup_left (Q.inv_mem hu)) (Subgroup.mem_sup_right ha)
      rw [ham]
      exact (Q ⊔ Z).mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right ⟨hmQA, hm⟩)
  obtain ⟨e, he, hZe⟩ := CFSG.SeitzReduction.F4Pilot.exists_mem_conj_eq_of_complement
    (p := 2) hQp hA2 (fun a ha => hPQ (hAP ha)) (fun z (hz : z ∈ Z) => hPQ (hQAP hz.1)) hQA hQZ
    hsup.symm
  refine ⟨M.map (MulAut.conj e).toMonoidHom, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxQ, m, hm, rfl⟩
    have hmQ : m ∈ Q := by
      have h := (Subgroup.mem_normalizer_iff.mp (hPQ (hQP (Q.inv_mem he))) _).mp hxQ
      simpa [MulAut.conj_apply, mul_assoc] using h
    have : m ∈ Q ⊓ M := ⟨hmQ, hm⟩
    rw [hQM, Subgroup.mem_bot] at this
    simp [this]
  · intro x hxP hxA
    have heP : e ∈ P := hQP he
    obtain ⟨u, hu, m, hm, hum⟩ :=
      hdecP (e⁻¹ * x * e) (P.mul_mem (P.mul_mem (P.inv_mem heP) hxP) heP)
    set c := e * m * e⁻¹ with hc
    have hcC : c ∈ M.map (MulAut.conj e).toMonoidHom := ⟨m, hm, by simp [hc, MulAut.conj_apply]⟩
    have huQ : e * u * e⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hPQ heP) u).mp hu
    have hxdec : x = (e * u * e⁻¹) * c := by
      rw [hc]
      calc x = e * (e⁻¹ * x * e) * e⁻¹ := by group
        _ = e * (u * m) * e⁻¹ := by rw [hum]
        _ = e * u * e⁻¹ * (e * m * e⁻¹) := by group
    have hAC : ∀ a ∈ A, a ∈ M.map (MulAut.conj e).toMonoidHom := by
      intro a ha
      have hz : e⁻¹ * a * e ∈ Z := by
        rw [hZe]; exact ⟨a, ha, by simp [MulAut.conj_apply]⟩
      exact ⟨e⁻¹ * a * e, hz.2, by simp [MulAut.conj_apply, mul_assoc]⟩
    refine ⟨e * u * e⁻¹, huQ, c, ⟨hcC, ?_⟩, hxdec⟩
    show c ∈ centralizer (A : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    set v := e * u * e⁻¹
    have hax : a * x * a⁻¹ = x := by
      have h := (Subgroup.mem_centralizer_iff.mp hxA) a ha
      calc a * x * a⁻¹ = x * a * a⁻¹ := by rw [h]
        _ = x := by group
    have hav : a * v * a⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hPQ (hAP ha)) v).mp huQ
    have hac : a * c * a⁻¹ ∈ M.map (MulAut.conj e).toMonoidHom :=
      (M.map (MulAut.conj e).toMonoidHom).mul_mem
        ((M.map (MulAut.conj e).toMonoidHom).mul_mem (hAC a ha) hcC)
        ((M.map (MulAut.conj e).toMonoidHom).inv_mem (hAC a ha))
    have heq : (a * v * a⁻¹) * (a * c * a⁻¹) = v * c := by
      calc (a * v * a⁻¹) * (a * c * a⁻¹) = a * (v * c) * a⁻¹ := by group
        _ = a * x * a⁻¹ := by rw [← hxdec]
        _ = x := hax
        _ = v * c := hxdec
    have hmem : v⁻¹ * (a * v * a⁻¹) ∈ Q ⊓ M.map (MulAut.conj e).toMonoidHom := by
      refine ⟨Q.mul_mem (Q.inv_mem huQ) hav, ?_⟩
      have : v⁻¹ * (a * v * a⁻¹) = c * (a * c * a⁻¹)⁻¹ := by
        calc v⁻¹ * (a * v * a⁻¹) = v⁻¹ * ((a * v * a⁻¹) * (a * c * a⁻¹)) * (a * c * a⁻¹)⁻¹ := by
              group
          _ = v⁻¹ * (v * c) * (a * c * a⁻¹)⁻¹ := by rw [heq]
          _ = c * (a * c * a⁻¹)⁻¹ := by group
      rw [this]
      exact (M.map (MulAut.conj e).toMonoidHom).mul_mem hcC
        ((M.map (MulAut.conj e).toMonoidHom).inv_mem hac)
    have hQC : Q ⊓ M.map (MulAut.conj e).toMonoidHom = ⊥ := by
      rw [eq_bot_iff]
      rintro y ⟨hyQ, m', hm', rfl⟩
      have hmQ : m' ∈ Q := by
        have h := (Subgroup.mem_normalizer_iff.mp (hPQ (hQP (Q.inv_mem he))) _).mp hyQ
        simpa [MulAut.conj_apply, mul_assoc] using h
      have : m' ∈ Q ⊓ M := ⟨hmQ, hm'⟩
      rw [hQM, Subgroup.mem_bot] at this
      simp [this]
    rw [hQC, Subgroup.mem_bot] at hmem
    have hv : a * v * a⁻¹ = v := by
      calc a * v * a⁻¹ = v * (v⁻¹ * (a * v * a⁻¹)) := by group
        _ = v := by rw [hmem, mul_one]
    have hcc : a * c * a⁻¹ = c := by
      rw [hv] at heq; exact mul_left_cancel heq
    calc a * c = a * c * a⁻¹ * a := by group
      _ = c * a := by rw [hcc]

end CFSG.StandardType.OddLayerCentre
