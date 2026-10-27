module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138SKNoComp
public import CFSG.RankThree.PartTwo.Sec13.Ronan138SQuot
import CFSG.RankThree.PartTwo.Sec13.Ronan138S131
import CFSG.RankThree.PartTwo.Sec13.Item138ProofExists
import CFSG.RankThree.PartTwo.Sec4.Item424Res6ProofSolv
import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo Matrix
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi zPi PiField ModThree Type123 diagE)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open scoped commutatorElement

section Mat

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem commute_of_type2 (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y s : GL (Fin 3) K} (hy : Type123 π (p ^ f) K y 2)
    (h : ProjGenLinGroup.mk y * ProjGenLinGroup.mk s =
      ProjGenLinGroup.mk s * ProjGenLinGroup.mk y) : y * s = s * y := by
  rw [← map_mul, ← map_mul] at h
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
  have h1 : s⁻¹ * y * s * GeneralLinearGroup.scalar (Fin 3) u = y := by
    calc s⁻¹ * y * s * GeneralLinearGroup.scalar (Fin 3) u =
        s⁻¹ * (y * s * GeneralLinearGroup.scalar (Fin 3) u) := by group
      _ = y := by rw [hu]; group
  have htr := Sec4.trace_inv_conj s y
  have htr' := Sec4.trace_mul_scalar (s⁻¹ * y * s) u
  rw [h1, htr] at htr'
  have h0 := Sec4.trace_ne_zero_of_type2 hK hq hy
  have hu1 : u = 1 := by
    apply Units.ext
    have h2 : ((u : K) - 1) * (y : Matrix (Fin 3) (Fin 3) K).trace = 0 := by
      rw [sub_mul, ← htr', one_mul, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right h0)
  rw [hu1, map_one, mul_one] at hu
  exact hu

theorem not_irreducible_of_commute_type2 (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y w : GL (Fin 3) K} (hy : Type123 π (p ^ f) K y 2) (hw : w * y = y * w) :
    ¬ ∀ W : Submodule K (Fin 3 → K), (∀ v ∈ W, (w : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
  intro hirr
  obtain ⟨ε, hε3, hε1, z, hz, g, -, hD⟩ := hy
  have hε : (ε : K) ≠ 1 := fun h => hε1 (Units.ext h)
  obtain ⟨ζ, -, rfl⟩ := Sec4.exists_scalar_of_mem_zPi hK hq hε3 hε hz
  set S := GeneralLinearGroup.scalar (Fin 3) ζ with hS
  have hwS : w * S = S * w := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ w).eq
  set M := g⁻¹ * w * g with hM
  have hMD : M * diagE ε = diagE ε * M := by
    have hwz : w * (y * S) = (y * S) * w := by
      calc w * (y * S) = (w * y) * S := by group
        _ = y * (w * S) := by rw [hw]; group
        _ = (y * S) * w := by rw [hwS]; group
    calc M * diagE ε = g⁻¹ * w * g * (g⁻¹ * (y * S) * g) := by rw [hD]
      _ = g⁻¹ * (w * (y * S)) * g := by group
      _ = g⁻¹ * ((y * S) * w) * g := by rw [hwz]
      _ = g⁻¹ * (y * S) * g * (g⁻¹ * w * g) := by group
      _ = diagE ε * M := by rw [hD]
  have hMDm : (M : Matrix (Fin 3) (Fin 3) K) * diagonal ![(ε : K), 1, 1] =
      diagonal ![(ε : K), 1, 1] * (M : Matrix (Fin 3) (Fin 3) K) := by
    have := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K)) hMD
    simpa only [Units.val_mul, Sec4.coe_diagE] using this
  have hM10 : (M : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 :=
    Sec4.entry_eq_zero_of_commute_diagonal hMDm (by simpa using hε.symm)
  have hM20 : (M : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 :=
    Sec4.entry_eq_zero_of_commute_diagonal hMDm (by simpa using hε.symm)
  set v : Fin 3 → K := (g : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1 with hv
  have hv0 : v ≠ 0 := by
    intro h0
    have := congrArg (fun u => ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ u) h0
    simp only [hv, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec, Matrix.mulVec_zero] at this
    have := congrFun this 0
    simp at this
  have hMe : (M : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single 0 1 : Fin 3 → K) =
      (M : Matrix (Fin 3) (Fin 3) K) 0 0 • Pi.single 0 1 := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hM10, hM20]
  have hwv : (w : Matrix (Fin 3) (Fin 3) K) *ᵥ v = (M : Matrix (Fin 3) (Fin 3) K) 0 0 • v := by
    have hwg : (w : Matrix (Fin 3) (Fin 3) K) * g = g * (M : Matrix (Fin 3) (Fin 3) K) := by
      rw [← Units.val_mul, ← Units.val_mul, hM]
      congr 1
      group
    rw [hv, Matrix.mulVec_mulVec, hwg, ← Matrix.mulVec_mulVec, hMe, Matrix.mulVec_smul]
  rcases hirr (K ∙ v) (fun u hu => by
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
      rw [Matrix.mulVec_smul, hwv, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)) with h | h
  · exact hv0 ((Submodule.span_singleton_eq_bot).mp h)
  · have := finrank_span_singleton (K := K) hv0
    rw [h, finrank_top, Module.finrank_fin_fun] at this
    omega

end Mat

section Fix

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}
variable {π : Bool} {p f : ℕ} {Fld : Type} [Field Fld]

theorem isSolvable_eqLocus_of_centMod
    {ψ : K ⧸ aschbacherSolvableCore 3 K ≃* projImage (slPi π 3 (p ^ f) Fld)} {c : G}
    {yc : GL (Fin 3) Fld} (hyc : ActsPGL ψ c yc) (hcN : c ∈ Subgroup.normalizer (K : Set G))
    (hsolC : Group.IsSolvable (Sec4.centMod (slPi π 3 (p ^ f) Fld) yc)) :
    Group.IsSolvable ((Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨c, hcN⟩)).toMonoidHom.eqLocus
      (MonoidHom.id (K ⧸ aschbacherSolvableCore 3 K))) := by
  set C := Sec4.centMod (slPi π 3 (p ^ f) Fld) yc with hC
  set Fix := (Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨c, hcN⟩)).toMonoidHom.eqLocus
    (MonoidHom.id (K ⧸ aschbacherSolvableCore 3 K)) with hFix
  let Φ : Fix →* ProjGenLinGroup (Fin 3) Fld :=
    (projImage (slPi π 3 (p ^ f) Fld)).subtype.comp (ψ.toMonoidHom.comp Fix.subtype)
  have hΦinj : Function.Injective Φ := fun z₁ z₂ h12 =>
    Subtype.ext (ψ.injective ((projImage (slPi π 3 (p ^ f) Fld)).subtype_injective h12))
  have hΦr : Φ.range ≤ C.map ProjGenLinGroup.mk := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨s', hs', hs'z⟩ := Subgroup.mem_map.mp (ψ (z : K ⧸ aschbacherSolvableCore 3 K)).2
    refine ⟨s', ?_, hs'z⟩
    have hz : Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨c, hcN⟩)
        (z : K ⧸ aschbacherSolvableCore 3 K) = z := z.2
    have h4 := hyc.2.2 z
    change ((ψ (Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨c, hcN⟩)
      (z : K ⧸ aschbacherSolvableCore 3 K)) : projImage _) : ProjGenLinGroup (Fin 3) Fld) = _
      at h4
    rw [hz, ← hs'z, ← map_inv, ← map_mul, ← map_mul] at h4
    obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h4.symm
    refine Sec4.mem_centMod_iff_scalar.mpr ⟨hs', GeneralLinearGroup.scalar (Fin 3) u,
      ⟨u, rfl⟩, ?_⟩
    have hsc' : ∀ (X : GL (Fin 3) Fld) (v : Fldˣ), X * GeneralLinearGroup.scalar (Fin 3) v =
        GeneralLinearGroup.scalar (Fin 3) v * X := fun X v =>
      (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar v X).eq
    have e1' : yc * s' = s' * GeneralLinearGroup.scalar (Fin 3) u⁻¹ * yc := by
      rw [map_inv]
      calc yc * s' = yc * s' * yc⁻¹ * GeneralLinearGroup.scalar (Fin 3) u *
            (GeneralLinearGroup.scalar (Fin 3) u)⁻¹ * yc := by group
        _ = s' * (GeneralLinearGroup.scalar (Fin 3) u)⁻¹ * yc := by rw [hu]
    calc s' * yc * s'⁻¹ = GeneralLinearGroup.scalar (Fin 3) u *
          (GeneralLinearGroup.scalar (Fin 3) u⁻¹ * s') * yc * s'⁻¹ := by
          rw [map_inv]; group
      _ = GeneralLinearGroup.scalar (Fin 3) u *
          (s' * GeneralLinearGroup.scalar (Fin 3) u⁻¹ * yc) * s'⁻¹ := by
          rw [← hsc' s' u⁻¹]; group
      _ = GeneralLinearGroup.scalar (Fin 3) u * (yc * s') * s'⁻¹ := by rw [← e1']
      _ = GeneralLinearGroup.scalar (Fin 3) u * yc := by group
  have : Group.IsSolvable (C.map (ProjGenLinGroup.mk :
      GL (Fin 3) Fld →* ProjGenLinGroup (Fin 3) Fld)) :=
    Group.isSolvable_of_surjective ((ProjGenLinGroup.mk).subgroupMap_surjective C)
  have : Group.IsSolvable Φ.range :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hΦr)
  exact Group.isSolvable_of_isSolvable_injective
    (f := (MonoidHom.ofInjective hΦinj).toMonoidHom) (MulEquiv.injective _)

end Fix

section Main


theorem step138CentPGL_of (h131 : Item131) (hspor : SporadicModels131) : Step138CentPGL := by
  intro G _ _ A c L E hH hPGL F hF e K heΩ hK heF hELK hPGLK hcN
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, y, t, hfr⟩ := exists_frame138_t hH hF hPGL
  have hH' := hH
  obtain ⟨h, -, hcE, hE3, hE27, -, -, -, -⟩ := hH'
  have hXF := mem_partTwoF_of_hyp138 hfr.hH
  have hD : Sec13Data G E e K :=
    { h.toPartTwoStanding with
      partTwoS_eq := h.partTwoS_eq
      mem_partTwoF := hXF.1
      not_mem_partTwoT := hXF.2
      zpowers_mem_omegaA := heΩ
      mem_lA := hK }
  have hEmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → E ≤ B → B = E := hXF.1.2.1
  have heE : e ∈ E := (zpowers_mem_omegaA_iff.mp heΩ).1
  have he3 : e ^ 3 = 1 := hE3.2 e heE
  have he1 : e ≠ 1 := by
    rintro rfl
    have := (zpowers_mem_omegaA_iff.mp heΩ).2.1
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at this
    norm_num at this
  have hc3 : c ^ 3 = 1 := hE3.2 c hcE
  obtain ⟨-, -, x₀, hx₀E, hx₀type⟩ := facts131_of_isZ3PGLThreePi h131 hspor hD hPGLK
  obtain ⟨hx₀N, π, p, f, Fld, _, hPi, hq, ψ, y₀, hy₀, hy₀3, hx₀act⟩ := hx₀type
  have hx₀ψ : ActsPGL ψ x₀ y₀ := ⟨hx₀N, hy₀, hx₀act⟩
  have hπ : π = false → UnitaryFieldData p f Fld := fun h => by subst h; exact hPi.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hK.1
  have hq2 : 2 < p ^ f := Item138Proof.two_lt_of_mulEquiv hKq hPi hq ψ
  haveI : Group.IsPerfect (K ⧸ aschbacherSolvableCore 3 K) := hKq.1
  haveI : Group.IsPerfect (projImage (slPi π 3 (p ^ f) Fld)) :=
    Group.IsPerfect.ofSurjective (f := ψ.toMonoidHom) ψ.surjective
  have hCEset := sectionCentralizer_eq_inf hK.2.1
  rw [hK.2.2.1] at hCEset
  have hCE : E ⊓ Sec4.thetaQuotCentralizer K = Subgroup.zpowers e :=
    SetLike.coe_injective hCEset.symm
  have heC : e ∈ Sec4.thetaQuotCentralizer K :=
    (Subgroup.mem_inf.mp (hCE.symm ▸ Subgroup.mem_zpowers e : e ∈ E ⊓ _)).2
  have hEact := actsPGL_of_maximal hKq hE3 hEmax hE27 hK.2.1 heE he1 hCE hPi hq hq2 ψ
  obtain ⟨yc, hyc⟩ := hEact c hcE
  have hdK : ⁅x, y⁆ ∈ K := hELK (hfr.hEL ▸ Subgroup.mem_zpowers _)
  obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp
    (ψ ((⟨⁅x, y⁆, hdK⟩ : K) : K ⧸ aschbacherSolvableCore 3 K)).2
  have hdψ : ActsPGL ψ ⁅x, y⁆ s := actsPGL_of_mem hπ hdK hs hse.symm
  have heψ : ActsPGL ψ e 1 := actsPGL_of_mem_thetaQuotCentralizer heC
  have hcomm : ∀ a ∈ Subgroup.zpowers e, ∀ b ∈ E ⊓ F, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_left (hfr.hEab e heE b (Subgroup.mem_inf.mp hb).1) k).eq
  obtain ⟨hcard, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  have heZ : e ∉ E ⊓ F := fun h' => heF (Subgroup.mem_inf.mp h').2
  rw [zpowers_inf_eq_bot he3 heZ, Subgroup.card_bot, mul_one,
    card_zpowers_of_pow_three he3 he1, hfr.h9] at hcard
  have heq : Subgroup.zpowers e ⊔ (E ⊓ F) = E :=
    Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr heE) inf_le_left)
      (by rw [hE27, hcard])
  have hx₀' : x₀ ∈ ((Subgroup.zpowers e ⊔ (E ⊓ F) : Subgroup G) : Set G) := by
    rw [heq]
    exact hx₀E
  rw [hset] at hx₀'
  obtain ⟨a, ha, b, hb, hab⟩ := hx₀'
  obtain ⟨n, rfl⟩ := exists_pow_eq_of_mem_zpowers ha
  obtain ⟨α, β, rfl⟩ := hfr.hZgen b hb
  have hx₀'' : ActsPGL ψ x₀ ((1 : GL (Fin 3) Fld) ^ n * (yc ^ α * s ^ β)) := by
    rw [← hab]
    exact (heψ.pow hπ n).mul ((hyc.pow hπ α).mul (hdψ.pow hπ β))
  have hmk₀ : ProjGenLinGroup.mk y₀ = ProjGenLinGroup.mk (yc ^ α * s ^ β) := by
    rw [ActsPGL.mk_eq hPi hq hx₀ψ hx₀'', one_pow, one_mul]
  obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau hPi hq
  have hycH : yc ∈ glPi π 3 (p ^ f) Fld := hyc.2.1
  have hycZ : yc ∉ zPi π 3 (p ^ f) Fld := by
    intro hz
    rw [Sec4.zPi_eq hπ hq' hτ hτ1] at hz
    have hcC := hyc.mem_thetaQuotCentralizer (Sec4.mk_eq_one_iff_mem_statedScalars.mpr hz.2)
    have hce : c ∈ Subgroup.zpowers e := hCE ▸ Subgroup.mem_inf.mpr ⟨hcE, hcC⟩
    apply heF
    have heq' := zpowers_eq_of_mem hc3 hfr.hc1 he3 he1 hce
    exact Subgroup.zpowers_le.mpr hfr.hcF (heq' ▸ Subgroup.mem_zpowers e)
  have hyc3 : yc ^ 3 ∈ zPi π 3 (p ^ f) Fld := by
    rw [Sec4.zPi_eq hπ hq' hτ hτ1]
    refine ⟨pow_mem hycH 3, ?_⟩
    have h1 := hyc.pow hπ 3
    rw [hc3] at h1
    have h2 := ActsPGL.mk_eq hPi hq h1 (actsPGL_one hπ)
    rw [map_one] at h2
    exact Sec4.mk_eq_one_iff_mem_statedScalars.mp h2
  rcases Sec4.type123_exhaust hPi hq hycH hycZ hyc3 with h1 | h2 | h3
  ·
    exfalso
    obtain ⟨l, hl, hlc⟩ : ∃ l ∈ slPi π 3 (p ^ f) Fld, ∀ m ∈ slPi π 3 (p ^ f) Fld,
        yc * m * yc⁻¹ = l * m * l⁻¹ := by
      obtain ⟨τ', hτ', hτ'1, z, hz, g, hg, hD'⟩ := h1
      exact (Sec4.rank3II_4_10_two hPi hq hτ' hτ'1 hycH hycZ hyc3).mpr
        (Or.inl ⟨yc * z, ⟨z, hz, rfl⟩, g, hg, hD'⟩)
    have hσ : l⁻¹ * yc ∈ StatedScalars (Fin 3) Fld :=
      Sec4.mem_statedScalars_of_commute hπ hq' hτ hτ1 fun m hm => by
        calc l⁻¹ * yc * m = l⁻¹ * (yc * m * yc⁻¹) * yc := by group
          _ = l⁻¹ * (l * m * l⁻¹) * yc := by rw [hlc m hm]
          _ = m * (l⁻¹ * yc) := by group
    have hlyc : ProjGenLinGroup.mk yc = ProjGenLinGroup.mk l := by
      have h4 := Sec4.mk_eq_one_iff_mem_statedScalars.mpr hσ
      rw [map_mul, map_inv, inv_mul_eq_one] at h4
      exact h4.symm
    have hmk : ProjGenLinGroup.mk y₀ = ProjGenLinGroup.mk (l ^ α * s ^ β) := by
      rw [hmk₀, map_mul, map_mul, map_pow, map_pow, map_pow, hlyc]
    have hsc0 : (l ^ α * s ^ β)⁻¹ * y₀ ∈ StatedScalars (Fin 3) Fld := by
      rw [← Sec4.mk_eq_one_iff_mem_statedScalars, map_mul, map_inv, ← hmk, inv_mul_cancel]
    refine Sec4.not_inner_of_type3 hPi hq hy₀ hy₀3
      ⟨l ^ α * s ^ β, mul_mem (pow_mem hl α) (pow_mem hs β), fun m _ => ?_⟩
    set w := l ^ α * s ^ β with hw
    have hc := Sec4.commute_of_mem_statedScalars hsc0 m
    calc y₀ * m * y₀⁻¹ = w * ((w⁻¹ * y₀) * m) * (w⁻¹ * y₀)⁻¹ * w⁻¹ := by group
      _ = w * (m * (w⁻¹ * y₀)) * (w⁻¹ * y₀)⁻¹ * w⁻¹ := by rw [← hc]
      _ = w * m * w⁻¹ := by group
  ·
    exfalso
    have hcd : c * ⁅x, y⁆ = ⁅x, y⁆ * c := hfr.hEab c hfr.hcE _ hfr.hdE
    have hys : yc * s = s * yc :=
      commute_of_type2 hPi hq h2 (ActsPGL.commute hPi hq hyc hdψ hcd)
    obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hmk₀.symm
    have hsy : Commute s yc := hys.symm
    have hc0 : Commute (yc ^ α * s ^ β * GeneralLinearGroup.scalar (Fin 3) u) yc :=
      (((Commute.refl yc).pow_left α).mul_left (hsy.pow_left β)).mul_left
        (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u yc).symm
    rw [hu] at hc0
    exact not_irreducible_of_commute_type2 hPi hq h2 hc0.eq hy₀3.2.2
  ·
    exact isSolvable_eqLocus_of_centMod hyc hcN
      (Sec4.Res424Six.isSolvable_centMod_of_type13 hPi hq hycH hycZ hyc3 (Or.inr h3))

end Main

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
