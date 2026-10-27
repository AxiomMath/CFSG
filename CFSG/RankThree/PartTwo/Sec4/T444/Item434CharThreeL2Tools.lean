module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Kit
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoFacts
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoAutCard
import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Cardinality
import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoPglFaithful
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Permutation.AlternatingAutomorphism

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434CharThree

open CFSG Matrix
open CFSG.GorensteinWalter (PSL2 PGL2 PGammaL2)
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo (pglAction semilinearAction
  semilinearEquivAut)
open CFSG.PSL2Table (unip unipSL unipotent)
open scoped MatrixGroups

section PGL

variable (K : Type) [Field K]

@[expose] noncomputable def unipPGL : Subgroup (PGL2 K) :=
  (unipotent K).map ProjectiveSpecialLinearGroup.toPGL

variable {K}

theorem exists_eq_mk_unip_of_mem {x : PSL(2, K)} (hx : x ∈ unipotent K) :
    ∃ t : K, x = PSL2Table.mk (unip t) := by
  obtain ⟨A, hA, rfl⟩ := hx
  obtain ⟨h10, h00, h11⟩ := (PSL2Table.mem_unipSL_iff A).mp hA
  refine ⟨(A : Matrix (Fin 2) (Fin 2) K) 0 1, ?_⟩
  congr 1
  apply PSL2Table.SL_ext <;> simp [h10, h00, h11]

theorem exists_eq_mk_toGL_unip_of_mem {w : PGL2 K} (hw : w ∈ unipPGL K) :
    ∃ t : K, w = ProjGenLinGroup.mk (SpecialLinearGroup.toGL (unip t)) := by
  obtain ⟨x, hx, rfl⟩ := hw
  obtain ⟨t, rfl⟩ := exists_eq_mk_unip_of_mem hx
  exact ⟨t, rfl⟩

theorem mk_toGL_unip_mem (t : K) :
    ProjGenLinGroup.mk (SpecialLinearGroup.toGL (unip t)) ∈ unipPGL K :=
  ⟨PSL2Table.mk (unip t), PSL2Table.mk_unip_mem_unipotent t, rfl⟩

theorem mem_unipPGL_of_commute {t : K} (ht : t ≠ 0) {c : PGL2 K}
    (hc : c * ProjGenLinGroup.mk (SpecialLinearGroup.toGL (unip t)) =
      ProjGenLinGroup.mk (SpecialLinearGroup.toGL (unip t)) * c) : c ∈ unipPGL K := by
  induction c using ProjGenLinGroup.induction_on with
  | mk C =>
  rw [← map_mul, ← map_mul] at hc
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hc
  have hm := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) hu
  have hU : ((SpecialLinearGroup.toGL (unip t) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![1, t; 0, 1] := rfl
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, hU] at hm
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 2) (Fin 2) K, (C : Matrix (Fin 2) (Fin 2) K) = M := ⟨_, rfl⟩
  rw [hM] at hm
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  have e10 := congrFun (congrFun hm 1) 0
  have e11 := congrFun (congrFun hm 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply] at e00 e01 e10 e11
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 ≠ 0 := by
    have h := (GeneralLinearGroup.det C).ne_zero
    rw [GeneralLinearGroup.val_det_apply, hM, Matrix.det_fin_two] at h
    exact h
  have hc0 : M 1 0 = 0 := by
    by_contra hc0
    have hu1 : (u : K) = 1 := by
      have : ((u : K) - 1) * M 1 0 = 0 := by linear_combination e10
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hc0)
    rw [hu1] at e00
    exact mul_ne_zero ht hc0 (by linear_combination -e00)
  rw [hc0, mul_zero, sub_zero] at hdet
  have ha0 : M 0 0 ≠ 0 := left_ne_zero_of_mul hdet
  have hu1 : (u : K) = 1 := by
    rw [hc0] at e00
    have : ((u : K) - 1) * M 0 0 = 0 := by linear_combination e00
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right ha0)
  rw [hu1] at e01
  have had : M 1 1 = M 0 0 := by
    have : t * (M 0 0 - M 1 1) = 0 := by linear_combination e01
    exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ht)).symm
  refine ⟨PSL2Table.mk (unip (M 0 1 / M 0 0)), PSL2Table.mk_unip_mem_unipotent _, ?_⟩
  change ProjGenLinGroup.mk (SpecialLinearGroup.toGL (unip (M 0 1 / M 0 0))) = ProjGenLinGroup.mk C
  refine ProjGenLinGroup.mk_eq_mk_iff.mpr ⟨Units.mk0 (M 0 0) ha0, Units.ext ?_⟩
  have hU' : ((SpecialLinearGroup.toGL (unip (M 0 1 / M 0 0)) : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = !![1, M 0 1 / M 0 0; 0, 1] := rfl
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar, hU', hM]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, hc0, had]
  field_simp

theorem unipPGL_commute {w w' : PGL2 K} (hw : w ∈ unipPGL K) (hw' : w' ∈ unipPGL K) :
    w * w' = w' * w := by
  obtain ⟨s, rfl⟩ := exists_eq_mk_toGL_unip_of_mem hw
  obtain ⟨t, rfl⟩ := exists_eq_mk_toGL_unip_of_mem hw'
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ← PSL2Table.unip_add, ← PSL2Table.unip_add,
    add_comm]

theorem pow_three_eq_one_of_mem_unipPGL [CharP K 3] {w : PGL2 K} (hw : w ∈ unipPGL K) :
    w ^ 3 = 1 := by
  obtain ⟨t, rfl⟩ := exists_eq_mk_toGL_unip_of_mem hw
  rw [← map_pow, ← map_pow, pow_three, ← PSL2Table.unip_add, ← PSL2Table.unip_add]
  have h3 : t + (t + t) = 0 := by
    have : (3 : K) = 0 := CharP.cast_eq_zero K 3
    linear_combination t * this
  rw [h3, PSL2Table.unip_zero, map_one, map_one]

theorem mem_map_conj_unipPGL_of_commute {h g c : PGL2 K}
    (hg : g ∈ (unipPGL K).map (MulAut.conj h).toMonoidHom) (hg1 : g ≠ 1) (hc : c * g = g * c) :
    c ∈ (unipPGL K).map (MulAut.conj h).toMonoidHom := by
  obtain ⟨w, hw, rfl⟩ := hg
  obtain ⟨t, rfl⟩ := exists_eq_mk_toGL_unip_of_mem hw
  have ht : t ≠ 0 := by
    rintro rfl
    apply hg1
    rw [PSL2Table.unip_zero, map_one, map_one, map_one]
  refine ⟨h⁻¹ * c * h, mem_unipPGL_of_commute ht ?_, ?_⟩
  · set w := ProjGenLinGroup.mk (SpecialLinearGroup.toGL (unip t)) with hw
    change c * (h * w * h⁻¹) = (h * w * h⁻¹) * c at hc
    calc h⁻¹ * c * h * w = h⁻¹ * (c * (h * w * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * w * h⁻¹) * c) * h := by rw [hc]
      _ = w * (h⁻¹ * c * h) := by group
  · change h * (h⁻¹ * c * h) * h⁻¹ = c
    group

theorem map_conj_unipPGL_commute {h w w' : PGL2 K}
    (hw : w ∈ (unipPGL K).map (MulAut.conj h).toMonoidHom)
    (hw' : w' ∈ (unipPGL K).map (MulAut.conj h).toMonoidHom) : w * w' = w' * w := by
  obtain ⟨v, hv, rfl⟩ := hw
  obtain ⟨v', hv', rfl⟩ := hw'
  rw [← map_mul, ← map_mul, unipPGL_commute hv hv']

theorem pow_three_eq_one_of_mem_map_conj [CharP K 3] {h w : PGL2 K}
    (hw : w ∈ (unipPGL K).map (MulAut.conj h).toMonoidHom) : w ^ 3 = 1 := by
  obtain ⟨v, hv, rfl⟩ := hw
  rw [← map_pow, pow_three_eq_one_of_mem_unipPGL hv, map_one]

theorem card_unipPGL [Finite K] (h2 : (2 : K) ≠ 0) : Nat.card (unipPGL K) = Nat.card K := by
  have : Fintype K := Fintype.ofFinite K
  rw [unipPGL, Subgroup.card_map_of_injective ProjectiveSpecialLinearGroup.toPGL_injective,
    PSL2Table.card_unipotent h2, Nat.card_eq_fintype_card]

theorem map_conj_unipPGL_le_range (h : PGL2 K) :
    (unipPGL K).map (MulAut.conj h).toMonoidHom ≤
      (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
  have := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglPSLRange_normal K
  rintro _ ⟨w, ⟨x, -, rfl⟩, rfl⟩
  exact this.conj_mem _ ⟨x, rfl⟩ h

end PGL

section Galois

variable {e : ℕ}

theorem two_ne_zero_galois : (2 : GaloisField 3 e) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : GaloisField 3 e) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff (GaloisField 3 e) 3] at h'
  norm_num at h'

theorem card_unipPGL_galois (he : e ≠ 0) : Nat.card (unipPGL (GaloisField 3 e)) = 3 ^ e := by
  rw [card_unipPGL two_ne_zero_galois, GaloisField.card 3 e he]

theorem factorization_card_pgl2 (he : e ≠ 0) :
    (Nat.card (PGL2 (GaloisField 3 e))).factorization 3 = e := by
  rw [CFSG.GorensteinWalter.pgl2_card_formula, GaloisField.card 3 e he]
  apply Item434AltPerm.factorization_three_pow_mul
  intro h3
  have h1 : 3 ∣ (3 ^ e) ^ 2 := dvd_pow (dvd_pow_self 3 he) two_ne_zero
  have h2 : 1 ≤ (3 ^ e) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  omega

theorem finite_pgl2 : Finite (PGL2 (GaloisField 3 e)) := by
  have : Finite (GL (Fin 2) (GaloisField 3 e)) := Finite.of_injective _ Units.val_injective
  exact Finite.of_surjective _ (ProjGenLinGroup.mk_surjective (n := Fin 2) (R := GaloisField 3 e))

theorem pglAction_injective (K : Type) [Field K] [Finite K] :
    Function.Injective (pglAction K) :=
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_injective K

theorem exists_pgl_part (he : e ≠ 0) {E : Subgroup (MulAut (PSL2 (GaloisField 3 e)))}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27) :
    ∃ (P : Subgroup (PGL2 (GaloisField 3 e))) (h : PGL2 (GaloisField 3 e)),
      P ≤ (unipPGL (GaloisField 3 e)).map (MulAut.conj h).toMonoidHom ∧ 9 ≤ Nat.card P ∧
        P.map (pglAction (GaloisField 3 e)) ≤ E := by
  set K := GaloisField 3 e with hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKc : Nat.card K = 3 ^ e := GaloisField.card 3 e he
  set S := semilinearEquivAut K with hS
  set E' : Subgroup (PGammaL2 K) := E.comap S.toMonoidHom with hE'
  have hE'map : E'.map S.toMonoidHom = E := Subgroup.map_comap_eq_self_of_surjective S.surjective E
  have hE'card : Nat.card E' = 27 := by
    rw [← hE27, ← hE'map, Subgroup.card_map_of_injective (f := S.toMonoidHom) S.injective]
  have hE'e : CFSG.Assembly.IsElemAbelian 3 E' :=
    Item434Kit.isElemAbelian_of_map_injective S.injective (hE'map ▸ hE)
  set ρ : PGammaL2 K →* (K ≃+* K) := SemidirectProduct.rightHom with hρ
  have hcyc : IsCyclic (K ≃+* K) :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_three K hKc).2
  have hρ3 : Nat.card (E'.map ρ) ∣ 3 := by
    rw [← IsCyclic.exponent_eq_card]
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
    obtain ⟨_, y, hy, rfl⟩ := x
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow, hE'e.2 y hy, map_one]
  have h9 : 9 ≤ Nat.card (E' ⊓ ρ.ker : Subgroup (PGammaL2 K)) := by
    have hcardE := Item434Alt.card_eq_card_inf_ker_mul_card_map ρ E'
    have hd := Nat.le_of_dvd (by norm_num) hρ3
    rw [hE'card] at hcardE
    by_contra hlt
    push Not at hlt
    have : Nat.card (E' ⊓ ρ.ker : Subgroup (PGammaL2 K)) * Nat.card (E'.map ρ) ≤ 8 * 3 :=
      Nat.mul_le_mul (by omega) hd
    omega
  set P : Subgroup (PGL2 K) := (E' ⊓ ρ.ker).comap SemidirectProduct.inl with hP
  have hPmap : P.map SemidirectProduct.inl = E' ⊓ ρ.ker := by
    apply Subgroup.map_comap_eq_self
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    exact inf_le_right
  have hPcard : Nat.card P = Nat.card (E' ⊓ ρ.ker : Subgroup (PGammaL2 K)) := by
    rw [← hPmap, Subgroup.card_map_of_injective SemidirectProduct.inl_injective]
  have hPp : IsPGroup 3 P := by
    have h1 : IsPGroup 3 (E' ⊓ ρ.ker : Subgroup (PGammaL2 K)) :=
      (Sec5.isPGroup_of_isElemAbelian hE'e).to_le inf_le_left
    exact h1.comap_of_injective _ SemidirectProduct.inl_injective
  have : Finite (PGL2 K) := finite_pgl2
  obtain ⟨h, hh⟩ := Item434AltPerm.exists_le_map_conj_of_card (P₀ := unipPGL K)
    (by rw [card_unipPGL_galois he, factorization_card_pgl2 he]) hPp
  refine ⟨P, h, hh, by rw [hPcard]; exact h9, ?_⟩
  rintro _ ⟨g, hg, rfl⟩
  have hg' : S (SemidirectProduct.inl g) ∈ E := hg.1
  rwa [show S (SemidirectProduct.inl g) = pglAction K g from
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction_inl K g] at hg'

end Galois

section TwentySeven

theorem mul_conj_mul_inv {X : Type*} [Group X] (φ : MulAut X) (x : X) :
    φ * MulAut.conj x * φ⁻¹ = MulAut.conj (φ x) := by
  ext y
  change φ (x * φ.symm y * x⁻¹) = φ x * y * (φ x)⁻¹
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem exists_ne_one_mem_inf {G : Type*} [Group G] {E H F : Subgroup G} [Finite E]
    (hH : H ≤ E) (hF : F ≤ E) (hcard : Nat.card E < Nat.card H * Nat.card F) :
    ∃ x ∈ H ⊓ F, x ≠ 1 := by
  by_contra hno
  push Not at hno
  have : Finite H := Finite.of_injective _ (Subgroup.inclusion_injective hH)
  have : Finite F := Finite.of_injective _ (Subgroup.inclusion_injective hF)
  have hinj : Function.Injective
      (fun p : H × F => (⟨(p.1 : G) * p.2, E.mul_mem (hH p.1.2) (hF p.2.2)⟩ : E)) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have hab' : (a : G) * b = a' * b' := congrArg Subtype.val hab
    have hmem : (a' : G)⁻¹ * a ∈ H ⊓ F := by
      refine ⟨H.mul_mem (H.inv_mem a'.2) a.2, ?_⟩
      have : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
        calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
          _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [hab']
          _ = b' * (b : G)⁻¹ := by group
      rw [this]
      exact F.mul_mem b'.2 (F.inv_mem b.2)
    have h1 : (a' : G)⁻¹ * a = 1 := hno _ hmem
    have ha : a = a' := Subtype.ext (by rw [← mul_inv_cancel_left (a' : G) a, h1, mul_one])
    subst ha
    have hb : b = b' := Subtype.ext (mul_left_cancel hab')
    rw [hb]
  have h := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod] at h
  omega

theorem eq_bot_of_le_normalizer_twentySeven
    {E : Subgroup (MulAut (PSL2 (GaloisField 3 3)))} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE27 : Nat.card E = 27) {Y : Subgroup (MulAut (PSL2 (GaloisField 3 3)))}
    (hY3 : ¬ 3 ∣ Nat.card Y)
    (hEY : E ≤ Subgroup.normalizer (Y : Set (MulAut (PSL2 (GaloisField 3 3))))) : Y = ⊥ := by
  set K := GaloisField 3 3 with hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (MulAut (PSL2 K)) := MulEquiv.finite_left
  obtain ⟨P, h, hPW, hP9, hPE⟩ := exists_pgl_part (by norm_num) hE hE27
  have hZ : Subgroup.center (PSL2 K) = ⊥ := CFSG.GorensteinWalter.psl2_center_eq_bot K
  have hinj := Item434Kit.conj_injective_of_center_eq_bot hZ
  have hpinj := pglAction_injective K
  have hfix : ∀ g ∈ P, g ≠ 1 → ∀ x : PSL2 K, pglAction K g x = x → x ^ 3 = 1 := by
    intro g hg hg1 x hx
    have hxW : ProjectiveSpecialLinearGroup.toPGL x ∈
        (unipPGL K).map (MulAut.conj h).toMonoidHom := by
      refine mem_map_conj_unipPGL_of_commute (hPW hg) hg1 ?_
      have h1 := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.toPGL_pglAction K g x
      rw [hx] at h1
      calc ProjectiveSpecialLinearGroup.toPGL x * g =
          g * ProjectiveSpecialLinearGroup.toPGL x * g⁻¹ * g := by rw [← h1]
        _ = g * ProjectiveSpecialLinearGroup.toPGL x := by group
    apply ProjectiveSpecialLinearGroup.toPGL_injective
    rw [map_pow, map_one]
    exact pow_three_eq_one_of_mem_map_conj hxW
  have hY1 : ∀ y ∈ Y, y ^ 3 = 1 → y = 1 := by
    intro y hy hy3
    have hd1 : orderOf (⟨y, hy⟩ : Y) ∣ 3 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact Subtype.ext (by rw [Subgroup.coe_pow, hy3, Subgroup.coe_one])
    have hd2 := orderOf_dvd_natCard (⟨y, hy⟩ : Y)
    have hcop : Nat.Coprime 3 (Nat.card Y) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hY3
    have h1 : orderOf (⟨y, hy⟩ : Y) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
    exact congrArg Subtype.val (orderOf_eq_one_iff.mp h1)
  set F : Subgroup (MulAut (PSL2 K)) := P.map (pglAction K) with hF
  have hFcard : Nat.card F = Nat.card P := Subgroup.card_map_of_injective hpinj
  set I := CFSG.ComponentClassification.OuterAutomorphisms.inner (PSL2 K) with hI
  have hYI : Y ⊓ I = ⊥ := by
    rw [eq_bot_iff]
    have hN : E ≤ Subgroup.normalizer ((Y ⊓ I : Subgroup _) : Set (MulAut (PSL2 K))) := by
      refine (le_inf hEY ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
      rw [Subgroup.normalizer_eq_top]
      exact le_top
    have hcop : Nat.Coprime 3 (Nat.card (Y ⊓ I : Subgroup (MulAut (PSL2 K)))) := by
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      exact fun h3 => hY3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
    refine Sec5.le_of_forall_inf_centralizer_sub_le (k := 2) Nat.prime_three hE
      (by rw [hE27]; norm_num) hN hcop fun H hHE hH9 => ?_
    have : Finite E := Nat.finite_of_card_ne_zero (by rw [hE27]; norm_num)
    obtain ⟨φ, ⟨hφH, hφF⟩, hφ1⟩ := exists_ne_one_mem_inf hHE hPE
      (by rw [hE27, hH9, hFcard]; nlinarith)
    obtain ⟨g, hgP, rfl⟩ := hφF
    have hg1 : g ≠ 1 := by
      rintro rfl
      exact hφ1 (map_one _)
    rintro y ⟨⟨hyY, x, rfl⟩, hyC⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp hyC _ hφH
    have hx : pglAction K g x = x := by
      apply hinj
      rw [← mul_conj_mul_inv, hcomm, mul_inv_cancel_right]
    have hx3 := hfix g hgP hg1 x hx
    rw [Subgroup.mem_bot]
    exact hY1 _ hyY (by rw [← map_pow, hx3, map_one])
  have hY6 : Nat.card Y ∣ 6 := by
    have hinjY : Function.Injective ((QuotientGroup.mk' I).comp Y.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro y hy
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hy
      have hmem : (y : MulAut (PSL2 K)) ∈ Y ⊓ I := ⟨y.2, hy⟩
      rw [hYI, Subgroup.mem_bot] at hmem
      exact (Subgroup.mem_bot).mpr (Subtype.ext hmem)
    have h1 := Subgroup.card_dvd_of_injective _ hinjY
    have hAut := AGLEmbedding.card_mulAut_psl2GF 3 3 (by norm_num)
    have hX : Nat.card (PSL2 K) = 9828 := by
      rw [CFSG.SectionRank.OddCover.card_psl_two Nat.prime_three (by norm_num)
        (GaloisField.card 3 3 (by norm_num))]
      norm_num
    have hIcard : Nat.card I = 9828 := by
      rw [hI, CFSG.ComponentClassification.OuterAutomorphisms.inner,
        ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hX]
    have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup I
    rw [hIcard] at hsplit
    have hOut : Nat.card (MulAut (PSL2 K) ⧸ I) = 6 := by
      have : Nat.card (MulAut (PSL2 K)) = 58968 := by rw [hAut]; norm_num
      omega
    rwa [hOut] at h1
  have hY2 : Nat.card Y ∣ 2 := by
    have hcop : Nat.Coprime (Nat.card Y) 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hY3).symm
    exact hcop.dvd_of_dvd_mul_right (by simpa using hY6)
  rcases (Nat.dvd_prime Nat.prime_two).mp hY2 with h1 | h2
  · exact Subgroup.card_eq_one.mp h1
  exfalso
  obtain ⟨y, hyY, hy1⟩ : ∃ y ∈ Y, y ≠ 1 := by
    by_contra hno
    push Not at hno
    have hbot : Y = ⊥ := (Subgroup.eq_bot_iff_forall Y).mpr hno
    rw [hbot, Subgroup.card_bot] at h2
    omega
  have hy2 : y ^ 2 = 1 := by
    have h := orderOf_dvd_natCard (⟨y, hyY⟩ : Y)
    rw [h2, orderOf_dvd_iff_pow_eq_one] at h
    simpa using congrArg Subtype.val h
  obtain ⟨g, hgP, hg1⟩ : ∃ g ∈ P, g ≠ 1 := by
    by_contra hno
    push Not at hno
    have hbot : P = ⊥ := (Subgroup.eq_bot_iff_forall P).mpr hno
    rw [hbot, Subgroup.card_bot] at hP9
    omega
  have hφE : pglAction K g ∈ E := hPE ⟨g, hgP, rfl⟩
  have hconjY : pglAction K g * y * (pglAction K g)⁻¹ ∈ Y :=
    (Subgroup.mem_normalizer_iff.mp (hEY hφE) y).mp hyY
  have hcomm : pglAction K g * y * (pglAction K g)⁻¹ = y := by
    obtain ⟨z, -, hz⟩ := (Nat.card_eq_two_iff' (1 : Y)).mp h2
    have hz1 : ∀ w : Y, w ≠ 1 → w = z := fun w hw => hz w hw
    have e1 := hz1 ⟨_, hconjY⟩ (by
      intro h0
      apply hy1
      have h0' : pglAction K g * y * (pglAction K g)⁻¹ = 1 := congrArg Subtype.val h0
      calc y = (pglAction K g)⁻¹ * (pglAction K g * y * (pglAction K g)⁻¹) * pglAction K g := by
            group
        _ = 1 := by rw [h0']; group)
    have e2 := hz1 ⟨y, hyY⟩ (fun h0 => hy1 (congrArg Subtype.val h0))
    exact congrArg Subtype.val (e1.trans e2.symm)
  set S := semilinearEquivAut K with hS
  obtain ⟨x, rfl⟩ := S.surjective y
  have hx2 : x ^ 2 = 1 := S.injective (by rw [map_pow, hy2, map_one])
  have hρx : SemidirectProduct.rightHom x = 1 := by
    have hcard : Nat.card (K ≃+* K) = 3 :=
      (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_three K
        (GaloisField.card 3 3 (by norm_num))).1
    have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    have h3 : (SemidirectProduct.rightHom x) ^ 3 = 1 := by
      have h := pow_card_eq_one' (G := K ≃+* K) (x := SemidirectProduct.rightHom x)
      rwa [hcard] at h
    have h2' : (SemidirectProduct.rightHom x) ^ 2 = 1 := by rw [← map_pow, hx2, map_one]
    calc SemidirectProduct.rightHom x =
        (SemidirectProduct.rightHom x) ^ 3 * ((SemidirectProduct.rightHom x) ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2']; group
  obtain ⟨gy, rfl⟩ : x ∈ (SemidirectProduct.inl :
      PGL2 K →* PGammaL2 K).range := by
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    exact hρx
  have hSgy : S (SemidirectProduct.inl gy) = pglAction K gy :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction_inl K gy
  rw [hSgy] at hcomm hy1 hy2
  have hgg : gy * g = g * gy := by
    apply hpinj
    rw [map_mul, map_mul]
    calc pglAction K gy * pglAction K g =
        (pglAction K g * pglAction K gy * (pglAction K g)⁻¹) * pglAction K g := by rw [hcomm]
      _ = pglAction K g * pglAction K gy := by group
  have hgyW := mem_map_conj_unipPGL_of_commute (hPW hgP) hg1 hgg
  have hgy3 := pow_three_eq_one_of_mem_map_conj hgyW
  have hgy2 : gy ^ 2 = 1 := hpinj (by rw [map_pow, hy2, map_one])
  apply hy1
  have hgy : gy = 1 := by
    calc gy = gy ^ 3 * (gy ^ 2)⁻¹ := by group
      _ = 1 := by rw [hgy3, hgy2]; group
  rw [hgy, map_one]

end TwentySeven

end CFSG.RankThree.PartTwo.Sec4.Item434CharThree
