module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326Crit
public import CFSG.GH74.GLS.Basic
public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.LocalAnalysis.SteinbergCERankTwoActionIndex

public section

open scoped IsMulCommutative

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

variable {G : Type} [Group G] [Finite G]

theorem frattini_ne_top_of_nontrivial {X : Type*} [Group X] [Finite X] [Nontrivial X] :
    frattini X ≠ ⊤ := by
  rcases eq_top_or_exists_le_coatom (⊥ : Subgroup X) with h | ⟨M, hM, -⟩
  · exact absurd h bot_ne_top
  · intro htop
    exact hM.1 (top_le_iff.mp (htop ▸ frattini_le_coatom hM))

theorem frattini_ne_bot_of_not_isMulCommutative {Q : Type*} [Group Q] [Finite Q]
    (hQp : IsPGroup 3 Q) (hnab : ¬ IsMulCommutative Q) : frattini Q ≠ ⊥ := by
  intro hbot
  apply hnab
  have hcomm : IsMulCommutative (Q ⧸ frattini Q) :=
    (CFSG.GroupTheory.frattini_elementary_quotient (p := 3) hQp).2.1
  haveI : IsMulCommutative (Q ⧸ frattini Q) := hcomm
  refine IsMulCommutative.of_comm (fun a b => ?_)
  have h1 : (((a * b)⁻¹ * (b * a) : Q) : Q ⧸ frattini Q) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [mul_comm' (a : Q ⧸ frattini Q) (b : Q ⧸ frattini Q), inv_mul_cancel]
  have h2 : (a * b)⁻¹ * (b * a) ∈ frattini Q := (QuotientGroup.eq_one_iff _).mp h1
  rw [hbot, Subgroup.mem_bot] at h2
  exact inv_mul_eq_one.mp h2

theorem isMulCommutative_of_frattini_quotient_card_three {Q : Type*} [Group Q] [Finite Q]
    (hcard : Nat.card (Q ⧸ frattini Q) = 3) : IsMulCommutative Q := by
  haveI : Nontrivial (Q ⧸ frattini Q) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  obtain ⟨y, hy1⟩ := exists_ne (1 : Q ⧸ frattini Q)
  have hzp : Subgroup.zpowers y = ⊤ := zpowers_eq_top_of_prime_card hcard hy1
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini Q) y
  have hmap : (Subgroup.zpowers x ⊔ frattini Q).map (QuotientGroup.mk' (frattini Q)) = ⊤ := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hzp]
    simp
  have hsup : Subgroup.zpowers x ⊔ frattini Q = ⊤ := by
    have h := Subgroup.comap_map_eq (QuotientGroup.mk' (frattini Q))
      (Subgroup.zpowers x ⊔ frattini Q)
    rw [hmap, QuotientGroup.ker_mk', Subgroup.comap_top] at h
    rw [sup_eq_left.mpr le_sup_right] at h
    exact h.symm
  have htop : Subgroup.zpowers x = ⊤ := frattini_nongenerating hsup
  haveI : IsCyclic Q := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨x, htop⟩
  infer_instance

theorem card_frattini_quotient_eq_nine {Q : Type*} [Group Q] [Finite Q]
    (hQp : IsPGroup 3 Q) (hQ27 : Nat.card Q = 27) (hnab : ¬ IsMulCommutative Q) :
    Nat.card (Q ⧸ frattini Q) = 9 := by
  obtain ⟨-, -, -, -, d, hd, -⟩ :=
    CFSG.GroupTheory.frattini_elementary_quotient (p := 3) hQp
  haveI : Nontrivial Q :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hQ27]; norm_num)
  have hΦtop : frattini Q ≠ ⊤ := frattini_ne_top_of_nontrivial
  have hΦbot : frattini Q ≠ ⊥ := frattini_ne_bot_of_not_isMulCommutative hQp hnab
  have hcardmul : 3 ^ d * Nat.card (frattini Q) = 27 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini Q)
    rw [hQ27, hd] at h
    exact h.symm
  have hΦgt : 1 < Nat.card (frattini Q) :=
    (Subgroup.one_lt_card_iff_ne_bot (frattini Q)).mpr hΦbot
  have hdle : d ≤ 2 := by
    have hpow : 3 ^ d < 3 ^ 3 := by
      calc 3 ^ d = 3 ^ d * 1 := (mul_one _).symm
        _ < 3 ^ d * Nat.card (frattini Q) :=
          Nat.mul_lt_mul_of_pos_left hΦgt (by positivity)
        _ = 27 := hcardmul
        _ = 3 ^ 3 := by norm_num
    have hlt : d < 3 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp hpow
    omega
  have hdge : 1 ≤ d := by
    by_contra h
    have hd0 : d = 0 := by omega
    apply hΦtop
    apply Subgroup.eq_top_of_card_eq
    have h : Nat.card (frattini Q) = 27 := by
      have hh := hcardmul
      rw [hd0, pow_zero, one_mul] at hh
      exact hh
    rw [h, hQ27]
  rcases (by omega : d = 1 ∨ d = 2) with hd1 | hd2
  · exact absurd (isMulCommutative_of_frattini_quotient_card_three
      (by rw [hd, hd1]; norm_num)) hnab
  · rw [hd, hd2]
    norm_num

noncomputable def frattiniQuotientActionGL (Q : Subgroup G) [Q.Normal]
    [IsElementaryAbelian 3 (Q ⧸ frattini Q)]
    (b : Module.Basis (Fin 2) (ZMod 3) (Additive (Q ⧸ frattini Q))) :
    G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
  (CFSG.LocalAnalysis.mulAutToGL b).comp
    ((CFSG.LargeEvenClassification.Helpers.frattiniAutAction Q).comp
      (MulAut.conjNormal : G →* MulAut Q))

theorem frattiniQuotientActionGL_eq_one_iff_trivial (Q : Subgroup G) [Q.Normal]
    [IsElementaryAbelian 3 (Q ⧸ frattini Q)]
    (b : Module.Basis (Fin 2) (ZMod 3) (Additive (Q ⧸ frattini Q))) {g : G} :
    frattiniQuotientActionGL Q b g = 1 ↔
      ∀ y : Q, ((MulAut.conjNormal g) y : Q ⧸ frattini Q) = (y : Q ⧸ frattini Q) := by
  constructor
  · intro hg y
    have h1 : (CFSG.LargeEvenClassification.Helpers.frattiniAutAction Q)
        (MulAut.conjNormal g) = 1 := by
      apply CFSG.LocalAnalysis.mulAutToGL_injective b
      rw [map_one]
      exact hg
    have h2 : MulAut.conjNormal g ∈
        CFSG.LargeEvenClassification.Helpers.frattiniKernel Q := by
      rw [← CFSG.LargeEvenClassification.Helpers.frattiniAutAction_ker]
      exact MonoidHom.mem_ker.mpr h1
    exact h2 y
  · intro htriv
    have h2 : MulAut.conjNormal g ∈
        CFSG.LargeEvenClassification.Helpers.frattiniKernel Q := fun y => htriv y
    have h1 : (CFSG.LargeEvenClassification.Helpers.frattiniAutAction Q)
        (MulAut.conjNormal g) = 1 := by
      rw [← MonoidHom.mem_ker,
        CFSG.LargeEvenClassification.Helpers.frattiniAutAction_ker]
      exact h2
    rw [frattiniQuotientActionGL, MonoidHom.comp_apply, MonoidHom.comp_apply, h1, map_one]

theorem mem_pCore_of_frattiniQuotientActionGL_eq_one
    (hcent : Subgroup.centralizer (CFSG.pCore 3 G : Set G) ≤ CFSG.pCore 3 G)
    [IsElementaryAbelian 3
      (CFSG.pCore 3 G ⧸ frattini (CFSG.pCore 3 G))]
    (b : Module.Basis (Fin 2) (ZMod 3)
      (Additive (CFSG.pCore 3 G ⧸ frattini (CFSG.pCore 3 G))))
    {g : G} (hg : frattiniQuotientActionGL (CFSG.pCore 3 G) b g = 1) :
    g ∈ CFSG.pCore 3 G := by
  apply mem_pCore_of_trivial_on_frattini (p := 3) hcent
  intro x hx
  have htriv :=
    (frattiniQuotientActionGL_eq_one_iff_trivial (CFSG.pCore 3 G) b).mp hg
  have hmem : (MulAut.conjNormal g (⟨x, hx⟩ : ↥(CFSG.pCore 3 G)) /
      (⟨x, hx⟩ : ↥(CFSG.pCore 3 G))) ∈ frattini ↥(CFSG.pCore 3 G) :=
    QuotientGroup.eq_iff_div_mem.mp (htriv ⟨x, hx⟩)
  refine ⟨MulAut.conjNormal g ⟨x, hx⟩ / ⟨x, hx⟩, hmem, ?_⟩
  change (↑(MulAut.conjNormal g ⟨x, hx⟩ / ⟨x, hx⟩) : G) = g * x * g⁻¹ * x⁻¹
  rw [Subgroup.coe_div, MulAut.conjNormal_apply, div_eq_mul_inv]

theorem frattiniQuotientActionGL_eq_one_of_mem (Q : Subgroup G) [Q.Normal]
    [IsElementaryAbelian 3 (Q ⧸ frattini Q)]
    (b : Module.Basis (Fin 2) (ZMod 3) (Additive (Q ⧸ frattini Q)))
    {g : G} (hg : g ∈ Q) : frattiniQuotientActionGL Q b g = 1 := by
  rw [frattiniQuotientActionGL_eq_one_iff_trivial]
  intro y
  haveI : IsMulCommutative (Q ⧸ frattini Q) := inferInstance
  have hconj : MulAut.conjNormal g y = MulAut.conj (⟨g, hg⟩ : Q) y := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hconj, MulAut.conj_apply]
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    mul_comm' ((⟨g, hg⟩ : Q) : Q ⧸ frattini Q) (y : Q ⧸ frattini Q), mul_inv_cancel_right]

theorem det_frattiniQuotientActionGL_eq_one_of_mem_oPrimeResidual (Q : Subgroup G) [Q.Normal]
    [IsElementaryAbelian 3 (Q ⧸ frattini Q)]
    (b : Module.Basis (Fin 2) (ZMod 3) (Additive (Q ⧸ frattini Q))) {x : G}
    (hx : x ∈ CFSG.GH74.GLS.oPrimeResidual 3 G) :
    Matrix.GeneralLinearGroup.det (frattiniQuotientActionGL Q b x) = 1 := by
  refine Subgroup.closure_induction (p := fun y _ =>
    Matrix.GeneralLinearGroup.det (frattiniQuotientActionGL Q b y) = 1) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨k, hk⟩
    have hu : (Matrix.GeneralLinearGroup.det (frattiniQuotientActionGL Q b y)) ^ (3 ^ k) =
        1 := by
      simp only [← map_pow, hk, map_one]
    have hcard_units : Nat.card (ZMod 3)ˣ = 2 := by
      rw [Nat.card_units, Nat.card_zmod]
    have hdiv1 : orderOf (Matrix.GeneralLinearGroup.det (frattiniQuotientActionGL Q b y)) ∣
        3 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hu
    have hdvd : orderOf (Matrix.GeneralLinearGroup.det (frattiniQuotientActionGL Q b y)) ∣
        Nat.card (ZMod 3)ˣ := orderOf_dvd_natCard _
    have hdiv2 : orderOf (Matrix.GeneralLinearGroup.det (frattiniQuotientActionGL Q b y)) ∣ 2 := by
      rwa [hcard_units] at hdvd
    have hcop : Nat.Coprime (3 ^ k) 2 := (by norm_num : Nat.Coprime 3 2).pow_left k
    refine orderOf_eq_one_iff.mp (Nat.dvd_one.mp ?_)
    have hgcd := Nat.dvd_gcd hdiv1 hdiv2
    rwa [hcop.gcd_eq_one] at hgcd
  · simp
  · intro y z _ _ hy hz
    rw [map_mul, map_mul, hy, hz, one_mul]
  · intro y _ hy
    rw [map_inv, map_inv, hy, inv_one]

@[expose] noncomputable def oPrimeResidualSL (Q : Subgroup G) [Q.Normal]
    [IsElementaryAbelian 3 (Q ⧸ frattini Q)]
    (b : Module.Basis (Fin 2) (ZMod 3) (Additive (Q ⧸ frattini Q))) :
    ↥(CFSG.GH74.GLS.oPrimeResidual 3 G) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) :=
  ((Matrix.SpecialLinearGroup.toGLKerEquiv (n := Fin 2) (R := ZMod 3)).symm :
      (Matrix.GeneralLinearGroup.det :
        Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) →* (ZMod 3)ˣ).ker →*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)).comp
    (((frattiniQuotientActionGL Q b).comp
      (CFSG.GH74.GLS.oPrimeResidual 3 G).subtype).codRestrict
      (Matrix.GeneralLinearGroup.det :
        Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) →* (ZMod 3)ˣ).ker
      (fun x => by
        rw [MonoidHom.mem_ker]
        exact det_frattiniQuotientActionGL_eq_one_of_mem_oPrimeResidual Q b x.2))

@[simp]
theorem oPrimeResidualSL_val (Q : Subgroup G) [Q.Normal]
    [IsElementaryAbelian 3 (Q ⧸ frattini Q)]
    (b : Module.Basis (Fin 2) (ZMod 3) (Additive (Q ⧸ frattini Q)))
    (x : ↥(CFSG.GH74.GLS.oPrimeResidual 3 G)) :
    ((oPrimeResidualSL Q b x : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) :
      Matrix (Fin 2) (Fin 2) (ZMod 3)) =
      (frattiniQuotientActionGL Q b (x : G) : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
  rw [oPrimeResidualSL]
  rfl

theorem oPrimeResidualSL_ker (Q : Subgroup G) [Q.Normal]
    [IsElementaryAbelian 3 (Q ⧸ frattini Q)]
    (b : Module.Basis (Fin 2) (ZMod 3) (Additive (Q ⧸ frattini Q)))
    (hker : ∀ g : G, frattiniQuotientActionGL Q b g = 1 → g ∈ Q) :
    (oPrimeResidualSL Q b).ker = Q.subgroupOf (CFSG.GH74.GLS.oPrimeResidual 3 G) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    refine hker (x : G) (Units.ext ?_)
    have h := Subtype.ext_iff.mp hx
    rw [oPrimeResidualSL_val] at h
    simpa using h
  · intro hx
    apply Subtype.ext
    rw [oPrimeResidualSL_val]
    simpa using congrArg (fun z : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) =>
      (z : Matrix (Fin 2) (Fin 2) (ZMod 3)))
      (frattiniQuotientActionGL_eq_one_of_mem Q b hx)

theorem exists_hom_sl23
    (hQ27 : Nat.card (CFSG.pCore 3 G) = 27) (hnab : ¬ IsMulCommutative (CFSG.pCore 3 G))
    (hcent : Subgroup.centralizer (CFSG.pCore 3 G : Set G) ≤ CFSG.pCore 3 G)
    (hQX : CFSG.pCore 3 G ≤ CFSG.GH74.GLS.oPrimeResidual 3 G) :
    ∃ σ : ↥(CFSG.GH74.GLS.oPrimeResidual 3 G) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3),
      σ.ker = (CFSG.pCore 3 G).subgroupOf (CFSG.GH74.GLS.oPrimeResidual 3 G) := by
  haveI : IsElementaryAbelian 3
      (CFSG.pCore 3 G ⧸ frattini (CFSG.pCore 3 G)) :=
    (CFSG.GroupTheory.frattini_elementary_quotient (p := 3)
      (CFSG.pCore_isPGroup (G := G) (p := 3))).2.2.2.1
  have hcard : Nat.card (CFSG.pCore 3 G ⧸ frattini (CFSG.pCore 3 G)) = 9 :=
    card_frattini_quotient_eq_nine (CFSG.pCore_isPGroup (G := G) (p := 3)) hQ27 hnab
  have hfin : Module.finrank (ZMod 3)
      (Additive (CFSG.pCore 3 G ⧸ frattini (CFSG.pCore 3 G))) = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 3)
      (V := Additive (CFSG.pCore 3 G ⧸ frattini (CFSG.pCore 3 G)))
    rw [Nat.card_zmod] at h
    have h' : Nat.card (Additive (CFSG.pCore 3 G ⧸ frattini (CFSG.pCore 3 G))) =
        Nat.card (CFSG.pCore 3 G ⧸ frattini (CFSG.pCore 3 G)) := rfl
    rw [h', hcard] at h
    have h9 : 9 = 3 ^ 2 := by norm_num
    rw [h9] at h
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h).symm
  let b := Module.finBasisOfFinrankEq (ZMod 3)
    (Additive (CFSG.pCore 3 G ⧸ frattini (CFSG.pCore 3 G))) hfin
  exact ⟨oPrimeResidualSL (CFSG.pCore 3 G) b,
    oPrimeResidualSL_ker (CFSG.pCore 3 G) b
      (fun g hg => mem_pCore_of_frattiniQuotientActionGL_eq_one hcent b hg)⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326
