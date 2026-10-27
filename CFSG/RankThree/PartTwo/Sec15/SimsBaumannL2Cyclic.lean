module

public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid
public import CFSG.RankThree.PartTwo.KFacts.K71Residual
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism

public section

namespace CFSG.RankThree.PartTwo.Sec15.SimsBaumann

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS
open scoped MatrixGroups
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
  (even_SL2_full_automorphism_semilinear_model)

variable {X : Type} [Group X] [Finite X]

private theorem sbl2cyc_pCore_quotient {Y : Type*} [Group Y] :
    CFSG.pCore 2 (Y ⧸ CFSG.pCore 2 Y) = ⊥ := by
  set N : Subgroup Y := CFSG.pCore 2 Y with hN
  set K : Subgroup Y := (CFSG.pCore 2 (Y ⧸ N)).comap (QuotientGroup.mk' N) with hK
  have hKp : IsPGroup 2 K := by
    rintro ⟨k, hk⟩
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (G := Y ⧸ N) (p := 2)) ⟨_, hk⟩
    have h1 : k ^ 2 ^ a ∈ N := by
      have := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (G := Y) (p := 2)) ⟨_, h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hKN : K ≤ N := le_sSup ⟨inferInstance, hKp⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  have hy : y ∈ N := hKN hx
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hy

private theorem sbl2cyc_exists_pow_mem {Y : Type*} [Group Y] [Finite Y] (y : Y) :
    ∃ a : ℕ, y ^ 2 ^ a ∈ oResidual 2 Y := by
  obtain ⟨a, m, hm, hmn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  refine ⟨a, Subgroup.subset_closure ?_⟩
  have hdvd : orderOf (y ^ 2 ^ a) ∣ m :=
    orderOf_dvd_of_pow_eq_one (by rw [← pow_mul, ← hmn, pow_orderOf_eq_one])
  exact Nat.Coprime.coprime_dvd_left hdvd (Nat.coprime_two_right.mpr hm)

private theorem sbl2cyc_eq_one_of_centralizes {Y : Type} [Group Y] [Finite Y]
    (hQ : CFSG.pCore 2 Y = ⊥) (hZ : Subgroup.center ↥(oResidual 2 Y) = ⊥) {c : Y}
    (hc : ∀ l ∈ oResidual 2 Y, l * c = c * l) : c = 1 := by
  haveI : (oResidual 2 Y).Normal := Stage1.Thm6.Prod.oResidual_normal 2 Y
  have hCn : (Subgroup.centralizer (oResidual 2 Y : Set Y)).Normal := inferInstance
  have hCp : IsPGroup 2 ↥(Subgroup.centralizer (oResidual 2 Y : Set Y)) := by
    rintro ⟨g, hg⟩
    obtain ⟨a, ha⟩ := sbl2cyc_exists_pow_mem g
    refine ⟨a, Subtype.ext ?_⟩
    have hz : (⟨g ^ 2 ^ a, ha⟩ : ↥(oResidual 2 Y)) ∈ Subgroup.center ↥(oResidual 2 Y) := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      exact (Commute.pow_right (Subgroup.mem_centralizer_iff.1 hg (l : Y) l.2) (2 ^ a)).eq
    rw [hZ, Subgroup.mem_bot] at hz
    have hz1 : g ^ 2 ^ a = 1 := congrArg Subtype.val hz
    exact hz1
  have hle : Subgroup.centralizer (oResidual 2 Y : Set Y) ≤ CFSG.pCore 2 Y :=
    le_sSup ⟨hCn, hCp⟩
  have hmem := hle (Subgroup.mem_centralizer_iff.2 hc)
  rwa [hQ, Subgroup.mem_bot] at hmem

private theorem sbl2cyc_center_sl2 (K : Type) [Field K] [CharP K 2] :
    Subgroup.center SL(2, K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hr1 : r = 1 := by
    have hr2 : r ^ 2 = 1 := by simpa using hr
    have : (r - 1) ^ 2 = 0 := by linear_combination hr2 + (1 - r) * h2
    have := pow_eq_zero_iff (two_ne_zero) |>.1 this
    linear_combination this
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1]
  simp

private noncomputable def sbl2cycAct (Y : Type) [Group Y] : Y →* Outer ↥(oResidual 2 Y) :=
  haveI : (oResidual 2 Y).Normal := Stage1.Thm6.Prod.oResidual_normal 2 Y
  (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner _)).comp
    MulAut.conjNormal

private theorem sbl2cycAct_ker {Y : Type} [Group Y] [Finite Y]
    (hQ : CFSG.pCore 2 Y = ⊥) (hZ : Subgroup.center ↥(oResidual 2 Y) = ⊥) {x : Y}
    (hx : sbl2cycAct Y x = 1) : x ∈ oResidual 2 Y := by
  haveI : (oResidual 2 Y).Normal := Stage1.Thm6.Prod.oResidual_normal 2 Y
  have hx' : (QuotientGroup.mk (MulAut.conjNormal x : MulAut ↥(oResidual 2 Y)) :
      Outer ↥(oResidual 2 Y)) = 1 := hx
  obtain ⟨l, hl⟩ := (QuotientGroup.eq_one_iff _).1 hx'
  have key : ∀ y ∈ oResidual 2 Y, y * ((l : Y)⁻¹ * x) = ((l : Y)⁻¹ * x) * y := by
    intro y hy
    have h := congrArg
      (fun α : MulAut ↥(oResidual 2 Y) => ((α ⟨y, hy⟩ : ↥(oResidual 2 Y)) : Y)) hl
    simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h
    have h2 : ((l : Y)⁻¹ * x) * y * ((l : Y)⁻¹ * x)⁻¹ = y := by
      calc ((l : Y)⁻¹ * x) * y * ((l : Y)⁻¹ * x)⁻¹ = (l : Y)⁻¹ * (x * y * x⁻¹) * l := by group
        _ = y := by rw [← h]; group
    exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  have h1 := sbl2cyc_eq_one_of_centralizes hQ hZ key
  have hxl : x = (l : Y) := (inv_mul_eq_one.1 h1).symm
  rw [hxl]
  exact l.2

private theorem sbl2cyc_exists_hom {n : ℕ} (hn : 2 ≤ n)
    (e : ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 n)) :
    ∃ Ψ : X →* Outer ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)),
      IsCyclic (Outer ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X))) ∧ CFSG.pCore 2 X ≤ Ψ.ker ∧
        Ψ.ker ≤ oResidual 2 X ⊔ CFSG.pCore 2 X := by
  have hmap : (oResidual 2 X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) =
      oResidual 2 (X ⧸ CFSG.pCore 2 X) :=
    Stage1.Thm6.Prod.map_oResidual _ (QuotientGroup.mk'_surjective _) Nat.prime_two
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  obtain ⟨σ⟩ := KFacts.nonempty_sl2_mulEquiv_projSL (F := GaloisField 2 n) hcard
  let ψ : ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) ≃* SL(2, GaloisField 2 n) := e.trans σ.symm
  have hZ : Subgroup.center ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) = ⊥ := by
    refine le_antisymm (fun z hz => ?_) bot_le
    have hz' : ψ z ∈ Subgroup.center SL(2, GaloisField 2 n) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      obtain ⟨g', rfl⟩ := ψ.surjective g
      rw [← map_mul, ← map_mul, hz g']
    rw [sbl2cyc_center_sl2, Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.2 (ψ.injective (by rw [hz', map_one]))
  refine ⟨(sbl2cycAct _).comp (QuotientGroup.mk' (CFSG.pCore 2 X)), ?_, ?_, ?_⟩
  · have h := (even_SL2_full_automorphism_semilinear_model (F := GaloisField 2 n) (by omega)
      hcard).2.2.1
    exact (CFSG.ComponentClassification.OuterAutomorphisms.equivalence ψ).isCyclic.2 h
  · intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff x).2 hx, map_one]
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' := sbl2cycAct_ker sbl2cyc_pCore_quotient hZ hx
    rw [← hmap, ← Subgroup.mem_comap, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at hx'
    exact hx'

theorem sup_normal_of_typeL2 {n : ℕ} (hn : 2 ≤ n)
    (e : ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 n)) (S : Subgroup X) :
    (S ⊔ oResidual 2 X ⊔ CFSG.pCore 2 X).Normal := by
  obtain ⟨Ψ, hcyc, -, hker⟩ := sbl2cyc_exists_hom hn e
  haveI := hcyc
  refine ⟨fun m hm g => ?_⟩
  have hcomm : Ψ (g * m * g⁻¹ * m⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [mul_comm' (Ψ g) (Ψ m)]
    group
  have hle : oResidual 2 X ⊔ CFSG.pCore 2 X ≤ S ⊔ oResidual 2 X ⊔ CFSG.pCore 2 X :=
    sup_le_sup_right le_sup_right _
  have hmem : g * m * g⁻¹ * m⁻¹ ∈ S ⊔ oResidual 2 X ⊔ CFSG.pCore 2 X := hle (hker hcomm)
  have hgm : g * m * g⁻¹ = (g * m * g⁻¹ * m⁻¹) * m := by group
  rw [hgm]
  exact Subgroup.mul_mem _ hmem hm

theorem relIndex_le_two_of_typeL2 {n : ℕ} (hn : 2 ≤ n)
    (e : ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 n))
    {E : Subgroup X} (hE : CFSG.Assembly.IsElemAbelian 2 E)
    (hEL : E ⊓ (oResidual 2 X ⊔ CFSG.pCore 2 X) ≤ CFSG.pCore 2 X) :
    (E ⊓ CFSG.pCore 2 X).relIndex E ≤ 2 := by
  obtain ⟨Ψ, hcyc, hQ, hker⟩ := sbl2cyc_exists_hom hn e
  haveI := hcyc
  have h1 : E ⊓ CFSG.pCore 2 X = E ⊓ Ψ.ker :=
    le_antisymm (inf_le_inf_left _ hQ) fun x hx => ⟨hx.1, hEL ⟨hx.1, hker hx.2⟩⟩
  rw [h1, Subgroup.inf_relIndex_left, Subgroup.relIndex_ker]
  have hexp : Monoid.exponent ↥(E.map Ψ) ∣ 2 := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun ⟨y, hy⟩ => ?_
    obtain ⟨x, hxE, rfl⟩ := hy
    refine Subtype.ext ?_
    change Ψ x ^ 2 = 1
    rw [← map_pow, hE.2 x hxE, map_one]
  rw [IsCyclic.exponent_eq_card] at hexp
  exact Nat.le_of_dvd two_pos hexp

end CFSG.RankThree.PartTwo.Sec15.SimsBaumann
