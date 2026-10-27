module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsSL3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22v
public import CFSG.CGT.PushingUpLit.BHS.Prelim

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem uc22s23sl3_Z_le_E {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch) :
    D.Z ≤ c.E :=
  (uc22p22v_le_conjClosure c.N D.Z).trans (uc22p22v_le_conjClosure D.M c.V)

theorem s23_12_of (D : Data G) (Ch : Choice2011 G) (h8 : S23_8 D Ch)
    (h91 : S23_9_1 D Ch) : S23_12 D Ch := by
  intro h1930 c
  rcases h91 h1930 c.toCtx23L with hbot | hcal
  · rw [Ctx2311.K, hbot]
    infer_instance
  · exact (h8 h1930 c.toCtx23L c.K hcal).1

private theorem uc22s23sl3_CME_le_CMETilde {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) : c.CME ≤ c.CMETilde := by
  intro x hx
  rw [Ctx2311.CME, Subgroup.mem_inf] at hx
  obtain ⟨hxM, hxcent⟩ := hx
  rw [Ctx2311.CMETilde, CFSG.Quasithin.mem_centralizerMod]
  refine ⟨hxM, ?_, ?_⟩
  · exact Subgroup.centralizer_le_normalizer (D.Z : Set G)
      ((Subgroup.centralizer_le (uc22s23sl3_Z_le_E c)) hxcent)
  · intro u hu
    have hcomm := (Subgroup.mem_centralizer_iff.1 hxcent) u hu
    have hxu : x * u * x⁻¹ = u := by
      rw [← hcomm]
      group
    rw [hxu]
    simpa using D.Z.one_mem

private def uc22s23sl3_conjAut {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch) (x : G)
    (hxE : ∀ u ∈ c.E, x * u * x⁻¹ ∈ c.E)
    (hxEinv : ∀ u ∈ c.E, x⁻¹ * u * x ∈ c.E) : MulAut ↥c.E where
  toFun u := ⟨x * (u : G) * x⁻¹, hxE u u.2⟩
  invFun u := ⟨x⁻¹ * (u : G) * x, hxEinv u u.2⟩
  left_inv u := Subtype.ext (by simp [mul_assoc])
  right_inv u := Subtype.ext (by simp [mul_assoc])
  map_mul' u v := Subtype.ext (by
    simp only [Subgroup.coe_mul]
    group)

private theorem uc22s23sl3_conjAut_apply {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (x : G)
    (hxE : ∀ u ∈ c.E, x * u * x⁻¹ ∈ c.E)
    (hxEinv : ∀ u ∈ c.E, x⁻¹ * u * x ∈ c.E) (u : ↥c.E) :
    ((uc22s23sl3_conjAut c x hxE hxEinv u : ↥c.E) : G) = x * (u : G) * x⁻¹ := rfl

private theorem uc22s23sl3_conjAut_pow {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (x : G)
    (hxE : ∀ u ∈ c.E, x * u * x⁻¹ ∈ c.E)
    (hxEinv : ∀ u ∈ c.E, x⁻¹ * u * x ∈ c.E) :
    ∀ n : ℕ, ∀ u : ↥c.E,
      ((((uc22s23sl3_conjAut c x hxE hxEinv) ^ n) u : ↥c.E) : G) =
        x ^ n * (u : G) * (x ^ n)⁻¹ := by
  intro n
  induction n with
  | zero => intro u; simp
  | succ n ih =>
      intro u
      rw [pow_succ', MulAut.mul_apply, uc22s23sl3_conjAut_apply, ih, pow_succ']
      group

private theorem uc22s23sl3_conjAut_orderOf_dvd {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (x : G)
    (hxE : ∀ u ∈ c.E, x * u * x⁻¹ ∈ c.E)
    (hxEinv : ∀ u ∈ c.E, x⁻¹ * u * x ∈ c.E) :
    orderOf (uc22s23sl3_conjAut c x hxE hxEinv) ∣ orderOf x := by
  refine orderOf_dvd_of_pow_eq_one ?_
  ext u
  rw [uc22s23sl3_conjAut_pow, pow_orderOf_eq_one]
  simp

private theorem uc22s23sl3_frattiniAut_eq_one {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h151 : S23_15_1 D Ch) (hE2 : IsPGroup 2 ↥c.E)
    (h1930 : H1930 D) {x : G} {τ : MulAut ↥c.E}
    (hτ : ∀ u : ↥c.E, ((τ u : ↥c.E) : G) = x * (u : G) * x⁻¹)
    (hxcomm : ∀ u ∈ c.E, x * u * x⁻¹ * u⁻¹ ∈ D.Z)
    (hcop : Nat.Coprime 2 (orderOf τ)) : τ = 1 := by
  have hfrat : CFSG.Walter.Huppert.frattiniAut ↥c.E τ = 1 := by
    ext q
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective q
    rw [CFSG.Walter.Huppert.frattiniAut_mk, MulAut.one_apply]
    have hmem : ((τ e) * e⁻¹ : ↥c.E) ∈ frattini ↥c.E := by
      rw [← Subgroup.mem_map_iff_mem c.E.subtype_injective]
      rw [h151 h1930 c]
      simpa [hτ] using hxcomm e e.2
    have hq : (QuotientGroup.mk ((τ e) * e⁻¹) : ↥c.E ⧸ frattini ↥c.E) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hmem
    have hq' : (QuotientGroup.mk (τ e) : ↥c.E ⧸ frattini ↥c.E) =
        QuotientGroup.mk e := by
      calc
        (QuotientGroup.mk (τ e) : ↥c.E ⧸ frattini ↥c.E) =
            (QuotientGroup.mk ((τ e) * e⁻¹) : ↥c.E ⧸ frattini ↥c.E) *
              QuotientGroup.mk e := by
              rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
              group
        _ = 1 * QuotientGroup.mk e := by rw [hq]
        _ = QuotientGroup.mk e := one_mul _
    simpa using hq'
  exact CFSG.Walter.Huppert.eq_one_of_frattiniAut_eq_one hE2 hcop hfrat

private theorem uc22s23sl3_odd_mem_CME {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (h151 : S23_15_1 D Ch) (hE2 : IsPGroup 2 ↥c.E) (h1930 : H1930 D)
    {x : G} (hx : x ∈ c.CMETilde) (hxodd : (orderOf x).Coprime 2) : x ∈ c.CME := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMnorm : D.M ≤ Subgroup.normalizer (c.E : Set G) :=
    uc22p22v_le_normalizer_conjClosure D.M c.V
  rw [Ctx2311.CMETilde, CFSG.Quasithin.mem_centralizerMod] at hx
  obtain ⟨hxM, -, hxcomm⟩ := hx
  have hxnorm : x ∈ Subgroup.normalizer (c.E : Set G) := hMnorm hxM
  have hxE : ∀ u ∈ c.E, x * u * x⁻¹ ∈ c.E := by
    intro u hu
    exact (Subgroup.mem_normalizer_iff.mp hxnorm u).mp hu
  have hxEinv : ∀ u ∈ c.E, x⁻¹ * u * x ∈ c.E := by
    intro u hu
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxnorm) u).mp hu
    simpa using h
  let τ := uc22s23sl3_conjAut c x hxE hxEinv
  have hτ : ∀ u : ↥c.E, ((τ u : ↥c.E) : G) = x * (u : G) * x⁻¹ :=
    uc22s23sl3_conjAut_apply c x hxE hxEinv
  have hτdvd : orderOf τ ∣ orderOf x :=
    uc22s23sl3_conjAut_orderOf_dvd c x hxE hxEinv
  have hcop : Nat.Coprime 2 (orderOf τ) :=
    Nat.Coprime.coprime_dvd_right hτdvd hxodd.symm
  have hτ1 : τ = 1 :=
    uc22s23sl3_frattiniAut_eq_one c h151 hE2 h1930 hτ hxcomm hcop
  rw [Ctx2311.CME, Subgroup.mem_inf]
  refine ⟨hxM, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have h := congrArg (fun σ : MulAut ↥c.E => ((σ ⟨e, he⟩ : ↥c.E) : G)) hτ1
  simp only [MulAut.one_apply, hτ] at h
  calc
    e * x = (x * e * x⁻¹) * x := by rw [h]
    _ = x * e := by group

theorem s23_19_of_isPGroup (D : Data G) (Ch : Choice2011 G) (h151 : S23_15_1 D Ch)
    (hE2 : H1930 D → ∀ c : Ctx2311 D Ch, IsPGroup 2 ↥c.E) : S23_19 D Ch := by
  intro h1930 c
  refine le_antisymm ?_ ?_
  · rw [CFSG.Quasithin.opResidual]
    refine (Subgroup.closure_le (K := CFSG.Quasithin.opResidual 2 c.CME)).2 ?_
    rintro x ⟨hx, hxodd⟩
    exact CFSG.Quasithin.mem_opResidual_of_coprime
      (uc22s23sl3_odd_mem_CME c h151 (hE2 h1930 c) h1930 hx hxodd) hxodd
  · exact CFSG.CGT.PushingUpLit.BHS.opResidual_mono 2 (uc22s23sl3_CME_le_CMETilde c)

end CFSG.LocalAnalysis.UniquenessCase.UC22
