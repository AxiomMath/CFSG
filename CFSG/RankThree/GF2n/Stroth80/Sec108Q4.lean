module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSp44Defs
import CFSG.RankThree.GF2n.Stroth80.Sec108GL24
import CFSG.Permutation.AlternatingNineFixedSimple
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6Quot
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec108Cent
public import CFSG.RankThree.GF2n.Tim79aCitedAS
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.Mathieu.M12

public section

namespace CFSG.RankThree.GF2n.Stroth80.Sec108

open CFSG CFSG.Open CFSG.Blueprint Matrix
open scoped commutatorElement

variable {𝓜 : Type} [Group 𝓜] [Finite 𝓜] {K : Type} [Field K] [Finite K] [CharP K 2]
  {L R N Y : Subgroup 𝓜} {ρ : ↥R →* GL (Fin 3) K} {μ : ↥N →* Multiplicative (Fin 3 → K)}
  {T : ↥(NLY L Y) →* AddMonoid.End (Fin 3 → K)}

private noncomputable def conjAction (hC : Levi108 K L R N Y ρ μ T) : GG L →* MulAut L :=
  QuotientGroup.lift (L.subgroupOf (NL L)) (Subgroup.normalizerMonoidHom L) (by
    rw [Subgroup.normalizerMonoidHom_ker]
    intro x hx
    exact (Subgroup.le_centralizer_iff_isMulCommutative.mpr hC.elemAb_L.1)
      (Subgroup.mem_subgroupOf.mp hx))

private lemma conjAction_mkG (hC : Levi108 K L R N Y ρ μ T) (g : ↥(NL L)) :
    conjAction hC (mkG L g) = Subgroup.normalizerMonoidHom L g := by
  rw [conjAction, mkG, QuotientGroup.mk'_apply, QuotientGroup.lift_mk']

private lemma conjAction_apply (hC : Levi108 K L R N Y ρ μ T) (g : ↥(NL L)) (l : L) :
    (conjAction hC (mkG L g) l : 𝓜) = (g : 𝓜) * (l : 𝓜) * (g : 𝓜)⁻¹ := by
  rw [conjAction_mkG]
  exact Subgroup.normalizerMonoidHom_apply_apply_coe L g l

private noncomputable def commMap (hC : Levi108 K L R N Y ρ μ T) (τ : ↥(NL L)) : L →* L where
  toFun l := l * (Subgroup.normalizerMonoidHom L τ l)⁻¹
  map_one' := by simp
  map_mul' l₁ l₂ := by
    haveI : IsMulCommutative L := hC.elemAb_L.1
    letI : CommGroup L := { (inferInstance : Group L) with mul_comm := fun a b => mul_comm' a b }
    simp only [map_mul, _root_.mul_inv_rev]
    ac_rfl

private noncomputable def commSub (hC : Levi108 K L R N Y ρ μ T) (τ : ↥(NL L)) : Subgroup L :=
  (commMap hC τ).range

private lemma commMap_apply (hC : Levi108 K L R N Y ρ μ T) (τ : ↥(NL L)) (l : L) :
    commMap hC τ l = l * (Subgroup.normalizerMonoidHom L τ l)⁻¹ := rfl

private lemma commMap_fixed_aux {G : Type} [CommGroup G] (f : MulAut G)
    (hf3 : f ^ 3 = 1) (hsq : ∀ x : G, x * x = 1) (l : G)
    (h : f (l * (f l)⁻¹) = l * (f l)⁻¹) : l * (f l)⁻¹ = 1 := by
  have hinv : ∀ x : G, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (hsq x)
  have h1 : f l * f (f l) = l * f l := by
    simpa [map_mul, hinv] using h
  have h2 : f (f l) = l := by
    have h1' := congrArg (fun x => x * f l) h1
    have h2' : f (f l) * (f l * f l) = l * (f l * f l) := by
      calc f (f l) * (f l * f l) = (f l * f (f l)) * f l := by ac_rfl
        _ = (l * f l) * f l := h1'
        _ = l * (f l * f l) := by ac_rfl
    simpa [hsq] using h2'
  have h3 : f l = l := by
    have h5 : f (f (f l)) = f l := congrArg f h2
    have h6 : f (f (f l)) = l := by
      have := congrArg (fun g : MulAut G => g l) hf3
      simpa [pow_succ, pow_two] using this
    rw [h6] at h5
    exact h5.symm
  rw [h3, mul_inv_cancel]

private lemma commMap_coe_eq (hC : Levi108 K L R N Y ρ μ T) (τ : ↥(NL L)) (l : L) :
    (commMap hC τ l : 𝓜) = ⁅(l : 𝓜), (τ : 𝓜)⁆ := by
  rw [commMap_apply, Subgroup.coe_mul, Subgroup.coe_inv,
    Subgroup.normalizerMonoidHom_apply_apply_coe, commutatorElement_def]
  group

private lemma commMap_mem_N (hC : Levi108 K L R N Y ρ μ T) {τ : ↥(NL L)}
    (hτR : (τ : 𝓜) ∈ R) {ω : K}
    (hτρ : (ρ ⟨(τ : 𝓜), hτR⟩ : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) ω)
    (l : L) : (commMap hC τ l : 𝓜) ∈ N := by
  have hlR : (l : 𝓜) ∈ R := hC.L_le_R l.2
  have hcR : (⁅(l : 𝓜), (τ : 𝓜)⁆) ∈ R :=
    R.mul_mem (R.mul_mem (R.mul_mem hlR hτR) (R.inv_mem hlR)) (R.inv_mem hτR)
  have hGL : (ρ ⟨(⁅(l : 𝓜), (τ : 𝓜)⁆), hcR⟩ : GL (Fin 3) K) = 1 := by
    have hcsub : (⟨(⁅(l : 𝓜), (τ : 𝓜)⁆), hcR⟩ : ↥R) =
        ⁅(⟨(l : 𝓜), hlR⟩ : ↥R), (⟨(τ : 𝓜), hτR⟩ : ↥R)⁆ := Subtype.ext rfl
    rw [show (ρ ⟨(⁅(l : 𝓜), (τ : 𝓜)⁆), hcR⟩ : GL (Fin 3) K) =
        ρ ⁅(⟨(l : 𝓜), hlR⟩ : ↥R), (⟨(τ : 𝓜), hτR⟩ : ↥R)⁆ from
        congrArg (fun x : ↥R => ρ x) hcsub, map_commutatorElement]
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    apply Units.ext
    change (ρ ⟨(l : 𝓜), hlR⟩ : Matrix (Fin 3) (Fin 3) K) *
        (ρ ⟨(τ : 𝓜), hτR⟩ : Matrix (Fin 3) (Fin 3) K) =
      (ρ ⟨(τ : 𝓜), hτR⟩ : Matrix (Fin 3) (Fin 3) K) *
        (ρ ⟨(l : 𝓜), hlR⟩ : Matrix (Fin 3) (Fin 3) K)
    rw [hτρ]
    exact (Matrix.scalar_comm (m := Fin 3) (n := Fin 3) ω (fun _ => Commute.all _ _) _).symm
  have hmem : (⟨(⁅(l : 𝓜), (τ : 𝓜)⁆), hcR⟩ : ↥R) ∈ ρ.ker :=
    MonoidHom.mem_ker.2 hGL
  rw [hC.ker_rho] at hmem
  rw [commMap_coe_eq]
  exact Subgroup.mem_subgroupOf.1 hmem

private lemma commSub_mem_N (hC : Levi108 K L R N Y ρ μ T) {τ : ↥(NL L)}
    (hτR : (τ : 𝓜) ∈ R) {ω : K}
    (hτρ : (ρ ⟨(τ : 𝓜), hτR⟩ : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) ω)
    (c : commSub hC τ) : ((c : L) : 𝓜) ∈ N := by
  obtain ⟨l, hl⟩ := c.2
  rw [← hl]
  exact commMap_mem_N hC hτR hτρ l

private lemma conj_mem_N_of_mem_R (hC : Levi108 K L R N Y ρ μ T) {r n : 𝓜}
    (hr : r ∈ R) (hn : n ∈ N) : r * n * r⁻¹ ∈ N := by
  have hnR : n ∈ R := hC.N_le_R hn
  have hrnR : r * n * r⁻¹ ∈ R := R.mul_mem (R.mul_mem hr hnR) (R.inv_mem hr)
  have hρn : ρ ⟨n, hnR⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hC.ker_rho]
    exact Subgroup.mem_subgroupOf.mpr hn
  have hGL : ρ ⟨r * n * r⁻¹, hrnR⟩ = 1 := by
    rw [show (⟨r * n * r⁻¹, hrnR⟩ : ↥R) = ⟨r, hr⟩ * ⟨n, hnR⟩ * (⟨r, hr⟩ : ↥R)⁻¹ by
      ext; rfl]
    rw [map_mul, map_mul, map_inv, hρn, mul_one, mul_inv_cancel]
  have hmem : (⟨r * n * r⁻¹, hrnR⟩ : ↥R) ∈ ρ.ker := MonoidHom.mem_ker.2 hGL
  rw [hC.ker_rho] at hmem
  exact Subgroup.mem_subgroupOf.1 hmem

private lemma exists_mem_L_inf_N_mu_ne_zero (hC : Levi108 K L R N Y ρ μ T) :
    ∃ (n : 𝓜) (hnN : n ∈ N) (hnL : n ∈ L),
      Multiplicative.toAdd (μ ⟨n, hnN⟩) ≠ 0 := by
  let v : Fin 3 → K := Pi.single 1 1
  have hv0 : v 0 = 0 := by simp [v]
  have hv1 : v 1 = 1 := by simp [v]
  obtain ⟨n, hn⟩ := hC.surjective_mu (Multiplicative.ofAdd v)
  refine ⟨n, n.2, ?_, ?_⟩
  · refine (hC.mem_L_iff_mu n n.2).mpr ?_
    rw [show Multiplicative.toAdd (μ n) = v from congrArg Multiplicative.toAdd hn]
    exact hv0
  · intro hzero
    have hv : v = 0 := by
      have h1 : Multiplicative.toAdd (μ n) = v := congrArg Multiplicative.toAdd hn
      rw [h1] at hzero
      exact hzero
    have : v 1 = 0 := by rw [hv]; rfl
    rw [hv1] at this
    exact one_ne_zero this

private lemma conj_mu_eq_smul (hC : Levi108 K L R N Y ρ μ T) {τ : ↥(NL L)}
    (hτR : (τ : 𝓜) ∈ R) {ω : K}
    (hτρ : (ρ ⟨(τ : 𝓜), hτR⟩ : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) ω)
    (hω0 : ω ≠ 0) (n : 𝓜) (hnN : n ∈ N) :
    Multiplicative.toAdd (μ ⟨(τ : 𝓜) * n * (τ : 𝓜)⁻¹,
      conj_mem_N_of_mem_R hC hτR hnN⟩) =
      ω⁻¹ • Multiplicative.toAdd (μ ⟨n, hnN⟩) := by
  have h := hC.mu_conj (τ : 𝓜) hτR n hnN ((τ : 𝓜) * n * (τ : 𝓜)⁻¹)
    (conj_mem_N_of_mem_R hC hτR hnN) rfl
  rw [h]
  have hM : Matrix.scalar (Fin 3) ω * Matrix.scalar (Fin 3) ω⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hω0, map_one]
  have hinv : ((ρ ⟨(τ : 𝓜), hτR⟩ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)⁻¹ = Matrix.scalar (Fin 3) ω⁻¹ := by
    rw [hτρ]
    exact Matrix.inv_eq_right_inv hM
  rw [Matrix.GeneralLinearGroup.coe_inv, hinv]
  change (Matrix.diagonal (fun _ : Fin 3 => ω⁻¹))ᵀ *ᵥ
      Multiplicative.toAdd (μ ⟨n, hnN⟩) = ω⁻¹ • Multiplicative.toAdd (μ ⟨n, hnN⟩)
  rw [Matrix.diagonal_transpose]
  funext i
  simp [Matrix.mulVec_diagonal]

private lemma commSub_ne_bot (hC : Levi108 K L R N Y ρ μ T) {τ : ↥(NL L)}
    (hτR : (τ : 𝓜) ∈ R) {ω : K}
    (hτρ : (ρ ⟨(τ : 𝓜), hτR⟩ : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) ω)
    (hω : ω ≠ 1) (hω0 : ω ≠ 0) : commSub hC τ ≠ ⊥ := by
  intro hbot
  obtain ⟨n, hnN, hnL, hnmu⟩ := exists_mem_L_inf_N_mu_ne_zero hC
  let l : L := ⟨n, hnL⟩
  have hcomm : commMap hC τ l = 1 := by
    have hmem : commMap hC τ l ∈ commSub hC τ := MonoidHom.mem_range.mpr ⟨l, rfl⟩
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hl : l = Subgroup.normalizerMonoidHom L τ l := by
    have h := hcomm
    rw [commMap_apply] at h
    exact mul_inv_eq_one.mp h
  have hamb : (τ : 𝓜) * n * (τ : 𝓜)⁻¹ = n := by
    have h := congrArg (fun x : L => (x : 𝓜)) hl
    have h' : n = (τ : 𝓜) * n * (τ : 𝓜)⁻¹ := by
      simpa [l, Subgroup.normalizerMonoidHom_apply_apply_coe] using h
    exact h'.symm
  have hconj := conj_mu_eq_smul hC hτR hτρ hω0 n hnN
  have hconjN : (τ : 𝓜) * n * (τ : 𝓜)⁻¹ ∈ N := conj_mem_N_of_mem_R hC hτR hnN
  have hsub : (⟨(τ : 𝓜) * n * (τ : 𝓜)⁻¹, hconjN⟩ : ↥N) = ⟨n, hnN⟩ := Subtype.ext hamb
  rw [hsub] at hconj
  have hv : Multiplicative.toAdd (μ ⟨n, hnN⟩) = 0 := by
    have hcoef : (1 - ω⁻¹) ≠ 0 := by
      intro hzero
      have hinv1 : ω⁻¹ = 1 := (sub_eq_zero.mp hzero).symm
      exact hω (inv_eq_one.mp hinv1)
    have hsm : (1 - ω⁻¹) • Multiplicative.toAdd (μ ⟨n, hnN⟩) = 0 := by
      rw [sub_smul, one_smul]
      nth_rewrite 1 [hconj]
      exact sub_self _
    rcases (smul_eq_zero.mp hsm) with h | h
    · exact absurd h hcoef
    · exact h
  exact hnmu hv

private lemma commSub_fixed_eq_one (hC : Levi108 K L R N Y ρ μ T) {τ : ↥(NL L)}
    (hτ3 : (τ : 𝓜) ^ 3 = 1) {c : commSub hC τ}
    (hfix : Subgroup.normalizerMonoidHom L τ (c : L) = (c : L)) : c = 1 := by
  haveI : IsMulCommutative L := hC.elemAb_L.1
  letI : CommGroup L := { (inferInstance : Group L) with mul_comm := fun a b => mul_comm' a b }
  have hτ3' : τ ^ 3 = 1 := Subtype.ext (by simpa using hτ3)
  have hf3 : Subgroup.normalizerMonoidHom L τ ^ 3 = 1 := by
    rw [← map_pow, hτ3', map_one]
  obtain ⟨l, hl⟩ := c.2
  have hc : (c : L) = commMap hC τ l := hl.symm
  apply Subtype.ext
  change (c : L) = 1
  rw [hc] at hfix ⊢
  exact commMap_fixed_aux (Subgroup.normalizerMonoidHom L τ) hf3
    (fun x : L => Subtype.ext (by simpa [pow_two] using hC.elemAb_L.2 (x : 𝓜) x.2)) l hfix

private noncomputable def commSubMu (hC : Levi108 K L R N Y ρ μ T) {τ : ↥(NL L)}
    (hτR : (τ : 𝓜) ∈ R) {ω : K}
    (hτρ : (ρ ⟨(τ : 𝓜), hτR⟩ : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) ω) :
    commSub hC τ → (Fin 2 → K) := fun c i =>
  Multiplicative.toAdd (μ ⟨((c : L) : 𝓜), commSub_mem_N hC hτR hτρ c⟩) i.succ

private lemma commSub_mu_zero (hC : Levi108 K L R N Y ρ μ T) {τ : ↥(NL L)}
    (hτR : (τ : 𝓜) ∈ R) {ω : K}
    (hτρ : (ρ ⟨(τ : 𝓜), hτR⟩ : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) ω)
    (c : commSub hC τ) :
    Multiplicative.toAdd (μ ⟨((c : L) : 𝓜), commSub_mem_N hC hτR hτρ c⟩) 0 = 0 :=
  (hC.mem_L_iff_mu _ (commSub_mem_N hC hτR hτρ c)).mp (c : L).2

private lemma commSub_eq_of_mu_eq (hC : Levi108 K L R N Y ρ μ T) {τ : ↥(NL L)}
    (hτR : (τ : 𝓜) ∈ R) (hτ3 : (τ : 𝓜) ^ 3 = 1) {ω : K}
    (hτρ : (ρ ⟨(τ : 𝓜), hτR⟩ : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) ω)
    {c d : commSub hC τ}
    (hmu : Multiplicative.toAdd (μ ⟨((c : L) : 𝓜), commSub_mem_N hC hτR hτρ c⟩) =
      Multiplicative.toAdd (μ ⟨((d : L) : 𝓜), commSub_mem_N hC hτR hτρ d⟩)) : c = d := by
  have hcN := commSub_mem_N hC hτR hτρ c
  have hdN := commSub_mem_N hC hτR hτρ d
  let g : commSub hC τ := c * d⁻¹
  have hgN : ((g : L) : 𝓜) ∈ N := commSub_mem_N hC hτR hτρ g
  have hsub : (⟨((g : L) : 𝓜), hgN⟩ : ↥N) =
      (⟨((c : L) : 𝓜), hcN⟩ : ↥N) * (⟨((d : L) : 𝓜), hdN⟩ : ↥N)⁻¹ := Subtype.ext (by
    simp [g])
  have hgmu : Multiplicative.toAdd (μ ⟨((g : L) : 𝓜), hgN⟩) = 0 := by
    rw [hsub, map_mul, map_inv, toAdd_mul, toAdd_inv, hmu, add_neg_cancel]
  have hgY : ((g : L) : 𝓜) ∈ Y := by
    have hmem : (⟨((g : L) : 𝓜), hgN⟩ : ↥N) ∈ μ.ker := by
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      simpa using hgmu
    rw [hC.ker_mu] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  have hgfix : Subgroup.normalizerMonoidHom L τ (g : L) = (g : L) := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hcomm : (τ : 𝓜) * ((g : L) : 𝓜) = ((g : L) : 𝓜) * (τ : 𝓜) :=
      (Subgroup.mem_centralizer_iff.mp (hC.Y_le_centralizer hgY)) (τ : 𝓜) hτR
    calc (τ : 𝓜) * ((g : L) : 𝓜) * (τ : 𝓜)⁻¹ =
        (((g : L) : 𝓜) * (τ : 𝓜)) * (τ : 𝓜)⁻¹ := by rw [hcomm]
      _ = ((g : L) : 𝓜) := by rw [mul_assoc, mul_inv_cancel, mul_one]
  have hg1 : g = 1 := commSub_fixed_eq_one hC hτ3 hgfix
  have hcd : c * d⁻¹ * d = d := by
    simpa [g] using congrArg (fun x : commSub hC τ => x * d) hg1
  simpa [mul_assoc] using hcd

private lemma commSubMu_injective (hC : Levi108 K L R N Y ρ μ T) {τ : ↥(NL L)}
    (hτR : (τ : 𝓜) ∈ R) (hτ3 : (τ : 𝓜) ^ 3 = 1) {ω : K}
    (hτρ : (ρ ⟨(τ : 𝓜), hτR⟩ : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) ω) :
    Function.Injective (commSubMu hC hτR hτρ) := by
  intro c d h
  have hcN := commSub_mem_N hC hτR hτρ c
  have hdN := commSub_mem_N hC hτR hτρ d
  have hmu : Multiplicative.toAdd (μ ⟨((c : L) : 𝓜), hcN⟩) =
      Multiplicative.toAdd (μ ⟨((d : L) : 𝓜), hdN⟩) := by
    funext i
    fin_cases i
    · show Multiplicative.toAdd (μ ⟨((c : L) : 𝓜), hcN⟩) 0 =
        Multiplicative.toAdd (μ ⟨((d : L) : 𝓜), hdN⟩) 0
      rw [commSub_mu_zero hC hτR hτρ c, commSub_mu_zero hC hτR hτρ d]
    · exact congrFun h 0
    · exact congrFun h 1
  exact commSub_eq_of_mu_eq hC hτR hτ3 hτρ hmu

private lemma commSub_card_le (hC : Levi108 K L R N Y ρ μ T) {τ : ↥(NL L)}
    (hτR : (τ : 𝓜) ∈ R) (hτ3 : (τ : 𝓜) ^ 3 = 1) {ω : K}
    (hτρ : (ρ ⟨(τ : 𝓜), hτR⟩ : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) ω)
    (hq : Nat.card K = 4) : Nat.card (commSub hC τ) ≤ 16 := by
  have hinj := commSubMu_injective hC hτR hτ3 hτρ
  have hle := Nat.card_le_card_of_injective (commSubMu hC hτR hτρ) hinj
  rw [Nat.card_fun, Nat.card_fin, hq] at hle
  norm_num at hle
  exact hle

private lemma conjAction_commMap (hC : Levi108 K L R N Y ρ μ T) {τ : ↥(NL L)}
    (w : GG L) (hw : w * mkG L τ = mkG L τ * w) (l : L) :
    conjAction hC w (commMap hC τ l) = commMap hC τ (conjAction hC w l) := by
  have hαf : conjAction hC w * conjAction hC (mkG L τ) =
      conjAction hC (mkG L τ) * conjAction hC w := by
    rw [← map_mul, ← map_mul, hw]
  have h1 : conjAction hC w (conjAction hC (mkG L τ) l) =
      conjAction hC (mkG L τ) (conjAction hC w l) := by
    have := congrArg (fun g : MulAut L => g l) hαf
    simpa [MulAut.mul_apply] using this
  simp only [commMap_apply, map_mul, map_inv]
  rw [← conjAction_mkG hC τ, h1]

private lemma commSub_map_conjAction_le (hC : Levi108 K L R N Y ρ μ T) {τ : ↥(NL L)}
    {w : GG L} (hw : w * mkG L τ = mkG L τ * w) :
    (commSub hC τ).map (conjAction hC w).toMonoidHom ≤ commSub hC τ := by
  intro x hx
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨l, hl⟩ := MonoidHom.mem_range.mp hc
  rw [← hl]
  change conjAction hC w (commMap hC τ l) ∈ commSub hC τ
  rw [conjAction_commMap hC w hw l]
  exact MonoidHom.mem_range.mpr ⟨conjAction hC w l, rfl⟩

private lemma commSub_map_conjAction (hC : Levi108 K L R N Y ρ μ T) {τ : ↥(NL L)}
    {w : GG L} (hw : w * mkG L τ = mkG L τ * w) :
    (commSub hC τ).map (conjAction hC w).toMonoidHom = commSub hC τ := by
  refine le_antisymm (commSub_map_conjAction_le hC hw) ?_
  have hw' : w⁻¹ * mkG L τ = mkG L τ * w⁻¹ := by
    have h1 : w * mkG L τ * w⁻¹ = mkG L τ := by rw [hw]; group
    calc w⁻¹ * mkG L τ = w⁻¹ * (w * mkG L τ * w⁻¹) := by rw [h1]
      _ = mkG L τ * w⁻¹ := by group
  intro c hc
  have hαinv : (conjAction hC w)⁻¹ = conjAction hC w⁻¹ := (map_inv (conjAction hC) w).symm
  have hcinv : (conjAction hC w)⁻¹ c ∈ commSub hC τ := by
    rw [hαinv]
    exact commSub_map_conjAction_le hC hw'
      (Subgroup.mem_map_of_mem (conjAction hC w⁻¹).toMonoidHom hc)
  have hc_eq : c = conjAction hC w ((conjAction hC w)⁻¹ c) := by simp
  rw [hc_eq]
  exact Subgroup.mem_map_of_mem (conjAction hC w).toMonoidHom hcinv

private lemma mem_centralizer_mkG_tau (hC : Levi108 K L R N Y ρ μ T) {τ : ↥(NL L)}
    {W₁ : Subgroup (GG L)}
    (hW₁τ : W₁ ≤ Subgroup.centralizer ({mkG L τ} : Set (GG L))) (w : W₁) :
    (w : GG L) * mkG L τ = mkG L τ * (w : GG L) :=
  ((Subgroup.mem_centralizer_iff.mp (hW₁τ w.2)) (mkG L τ) (by simp)).symm

private noncomputable def restrictConjAction (hC : Levi108 K L R N Y ρ μ T) {τ : ↥(NL L)}
    {W₁ : Subgroup (GG L)}
    (hW₁τ : W₁ ≤ Subgroup.centralizer ({mkG L τ} : Set (GG L)))
    (w : W₁) : MulAut (commSub hC τ) :=
  ((conjAction hC (w : GG L)).subgroupMap (commSub hC τ)).trans
    (MulEquiv.subgroupCongr (commSub_map_conjAction hC (mem_centralizer_mkG_tau hC hW₁τ w)))

private lemma restrictConjAction_coe (hC : Levi108 K L R N Y ρ μ T) {τ : ↥(NL L)}
    {W₁ : Subgroup (GG L)}
    (hW₁τ : W₁ ≤ Subgroup.centralizer ({mkG L τ} : Set (GG L)))
    (w : W₁) (c : commSub hC τ) :
    ((restrictConjAction hC hW₁τ w c : commSub hC τ) : L) =
      conjAction hC (w : GG L) (c : L) := rfl

private noncomputable def actionOnC (hC : Levi108 K L R N Y ρ μ T) {τ : ↥(NL L)}
    {W₁ : Subgroup (GG L)}
    (hW₁τ : W₁ ≤ Subgroup.centralizer ({mkG L τ} : Set (GG L))) :
    W₁ →* MulAut (commSub hC τ) where
  toFun := restrictConjAction hC hW₁τ
  map_one' := by
    apply MulEquiv.ext
    intro c
    apply Subtype.ext
    rw [MulAut.one_apply, restrictConjAction_coe]
    simp
  map_mul' w₁ w₂ := by
    apply MulEquiv.ext
    intro c
    apply Subtype.ext
    simp only [MulAut.mul_apply]
    rw [restrictConjAction_coe, restrictConjAction_coe, restrictConjAction_coe]
    simp

private lemma actionOnC_coe (hC : Levi108 K L R N Y ρ μ T) {τ : ↥(NL L)}
    {W₁ : Subgroup (GG L)}
    (hW₁τ : W₁ ≤ Subgroup.centralizer ({mkG L τ} : Set (GG L)))
    (w : W₁) (c : commSub hC τ) :
    ((actionOnC hC hW₁τ w c : commSub hC τ) : L) =
      conjAction hC (w : GG L) (c : L) := rfl

private noncomputable def tauOnC (hC : Levi108 K L R N Y ρ μ T) {τ : ↥(NL L)} :
    MulAut (commSub hC τ) :=
  actionOnC hC (W₁ := Subgroup.centralizer ({mkG L τ} : Set (GG L))) le_rfl
    ⟨mkG L τ, by rw [Subgroup.mem_centralizer_singleton_iff]⟩

private lemma tauOnC_coe (hC : Levi108 K L R N Y ρ μ T) {τ : ↥(NL L)}
    (c : commSub hC τ) :
    ((tauOnC hC c : commSub hC τ) : L) = conjAction hC (mkG L τ) (c : L) := by
  rw [tauOnC, actionOnC_coe]

private lemma tauOnC_pow_three (hC : Levi108 K L R N Y ρ μ T) {τ : ↥(NL L)}
    (hτ3 : (τ : 𝓜) ^ 3 = 1) : tauOnC hC (τ := τ) ^ 3 = 1 := by
  have hτ3' : τ ^ 3 = 1 := Subtype.ext (by simpa using hτ3)
  have hτhat3 : mkG L τ ^ 3 = 1 := by
    calc mkG L τ ^ 3 = mkG L (τ ^ 3) := (map_pow (mkG L) τ 3).symm
      _ = mkG L 1 := by rw [hτ3']
      _ = 1 := map_one _
  have hx3 : (⟨mkG L τ, by rw [Subgroup.mem_centralizer_singleton_iff]⟩ :
      Subgroup.centralizer ({mkG L τ} : Set (GG L))) ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, hτhat3]
  rw [tauOnC, ← map_pow, hx3, map_one]

private lemma tauOnC_fixed_eq_one (hC : Levi108 K L R N Y ρ μ T) {τ : ↥(NL L)}
    (hτ3 : (τ : 𝓜) ^ 3 = 1) {c : commSub hC τ} (hfix : tauOnC hC c = c) : c = 1 := by
  apply commSub_fixed_eq_one hC hτ3
  have h := congrArg (fun x : commSub hC τ => (x : L)) hfix
  rw [tauOnC_coe, conjAction_mkG] at h
  exact h

private lemma actionOnC_comm_tau (hC : Levi108 K L R N Y ρ μ T) {τ : ↥(NL L)}
    {W₁ : Subgroup (GG L)}
    (hW₁τ : W₁ ≤ Subgroup.centralizer ({mkG L τ} : Set (GG L))) (w : W₁) :
    actionOnC hC hW₁τ w * tauOnC hC = tauOnC hC * actionOnC hC hW₁τ w := by
  have hcomm : conjAction hC (w : GG L) * conjAction hC (mkG L τ) =
      conjAction hC (mkG L τ) * conjAction hC (w : GG L) := by
    rw [← map_mul, ← map_mul, mem_centralizer_mkG_tau hC hW₁τ w]
  apply MulEquiv.ext
  intro c
  apply Subtype.ext
  simp only [MulAut.mul_apply]
  rw [actionOnC_coe, tauOnC_coe, tauOnC_coe, actionOnC_coe]
  exact congrArg (fun g : MulAut L => g (c : L)) hcomm

private lemma commSub_le_Y (hC : Levi108 K L R N Y ρ μ T) {τ : ↥(NL L)}
    {W₁ : Subgroup (GG L)}
    (hW₁τ : W₁ ≤ Subgroup.centralizer ({mkG L τ} : Set (GG L)))
    (hXW : Xlevi L R ≤ W₁)
    (hφ1 : ∀ w : W₁, actionOnC hC hW₁τ w = 1) (c : commSub hC τ) :
    ((c : L) : 𝓜) ∈ Y := by
  rw [← hC.fix_Xlevi_iff (c : L).2]
  intro g hgX
  have hxW : mkG L g ∈ W₁ := hXW hgX
  have h1 : actionOnC hC hW₁τ ⟨mkG L g, hxW⟩ = 1 := hφ1 _
  have hfix : (actionOnC hC hW₁τ ⟨mkG L g, hxW⟩) c = c := by rw [h1]; rfl
  have hcoe := congrArg (fun x : commSub hC τ => (x : L)) hfix
  rw [actionOnC_coe] at hcoe
  have := congrArg (fun x : L => (x : 𝓜)) hcoe
  rwa [conjAction_apply] at this

private lemma omega_cube_of_tau (hC : Levi108 K L R N Y ρ μ T) {τ : ↥(NL L)}
    (hτ : (τ : 𝓜) ∈ R) (hτ3 : (τ : 𝓜) ^ 3 = 1) {ω : K}
    (hρτ : (ρ ⟨(τ : 𝓜), hτ⟩ : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) ω) :
    ω ^ 3 = 1 := by
  have hsub : (⟨(τ : 𝓜), hτ⟩ : ↥R) ^ 3 = 1 := Subtype.ext (by simpa using hτ3)
  have h1 : (ρ ⟨(τ : 𝓜), hτ⟩ : GL (Fin 3) K) ^ 3 = 1 := by
    rw [← map_pow, hsub, map_one]
  have h2 : (Matrix.scalar (Fin 3) ω : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    rw [← hρτ]
    exact congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) h1
  rw [show (Matrix.scalar (Fin 3) ω : Matrix (Fin 3) (Fin 3) K) ^ 3 =
      Matrix.scalar (Fin 3) (ω ^ 3) from (map_pow (Matrix.scalar (Fin 3)) ω 3).symm,
    show (1 : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) 1 from (map_one _).symm] at h2
  exact Matrix.scalar_inj.mp h2

private lemma card_Xlevi_eq_sixty (hC : Levi108 K L R N Y ρ μ T) (hq : Nat.card K = 4) :
    Nat.card (Xlevi L R) = 60 := by
  obtain ⟨eX⟩ := hC.nonempty_mulEquiv_SL2
  calc Nat.card (Xlevi L R) = Nat.card (SpecialLinearGroup (Fin 2) K) :=
        Nat.card_congr eX.toEquiv
    _ = Nat.card (StatedSL 2 K) :=
        Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).toEquiv
    _ = 60 := by
        rw [CFSG.Open.StatedAPI.card_statedSL_two, hq]
        norm_num

private lemma isSimpleGroup_Xlevi (hC : Levi108 K L R N Y ρ μ T) (hq : Nat.card K = 4) :
    IsSimpleGroup (Xlevi L R) := by
  have h4 : ∃ s : Finset K, s.card = 4 := by
    letI := Fintype.ofFinite K
    exact ⟨Finset.univ, by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hq]⟩
  haveI : IsSimpleGroup (SpecialLinearGroup (Fin 2) K) :=
    CFSG.ComponentClassification.GMS78.u3_isSimpleGroup_SL2 K h4
  obtain ⟨eX⟩ := hC.nonempty_mulEquiv_SL2
  exact MulEquiv.isSimpleGroup eX

theorem Levi108.false_of_simple_le_centralizer (hC : Levi108 K L R N Y ρ μ T)
    (hq : Nat.card K = 4) {τ : ↥(NL L)} (hτ : (τ : 𝓜) ∈ R) (hτ3 : (τ : 𝓜) ^ 3 = 1) {ω : K}
    (hω : ω ≠ 1) (hρτ : (ρ ⟨τ, hτ⟩ : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) ω)
    {W₁ : Subgroup (GG L)} (hW₁ : IsSimpleGroup W₁) (hW₁card : 180 < Nat.card W₁)
    (hXW : Xlevi L R ≤ W₁) (hW₁τ : W₁ ≤ Subgroup.centralizer ({mkG L τ} : Set (GG L))) :
    False := by
  have hω3 := omega_cube_of_tau hC hτ hτ3 hρτ
  have hω0 : ω ≠ 0 := by
    intro h0
    rw [h0] at hω3
    norm_num at hω3
  have hne : commSub hC τ ≠ ⊥ := commSub_ne_bot hC hτ hρτ hω hω0
  obtain ⟨c0, hc0⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  haveI : IsMulCommutative L := hC.elemAb_L.1
  letI : CommGroup L := { (inferInstance : Group L) with mul_comm := fun a b => mul_comm' a b }
  have h2 : ∀ c : commSub hC τ, c * c = 1 := fun c => by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one]
    apply Subtype.ext
    simpa [pow_two] using hC.elemAb_L.2 ((c : L) : 𝓜) (c : L).2
  have hφ1 : ∀ w : W₁, actionOnC hC hW₁τ w = 1 := fun w =>
    eq_one_of_commute_fixedPointFree (C := commSub hC τ) (W := W₁) h2
      (commSub_card_le hC hτ hτ3 hρτ hq) (tauOnC_pow_three hC hτ3)
      (fun c => tauOnC_fixed_eq_one hC hτ3) hW₁card (actionOnC hC hW₁τ)
      (actionOnC_comm_tau hC hW₁τ) w
  have hc0Y : ((c0 : L) : 𝓜) ∈ Y := commSub_le_Y hC hW₁τ hXW hφ1 c0
  have hcomm : (τ : 𝓜) * ((c0 : L) : 𝓜) = ((c0 : L) : 𝓜) * (τ : 𝓜) :=
    (Subgroup.mem_centralizer_iff.mp (hC.Y_le_centralizer hc0Y)) (τ : 𝓜) hτ
  have hfix : Subgroup.normalizerMonoidHom L τ (c0 : L) = (c0 : L) := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    calc (τ : 𝓜) * ((c0 : L) : 𝓜) * (τ : 𝓜)⁻¹ =
        (((c0 : L) : 𝓜) * (τ : 𝓜)) * (τ : 𝓜)⁻¹ := by rw [hcomm]
      _ = ((c0 : L) : 𝓜) := by rw [mul_assoc, mul_inv_cancel, mul_one]
  exact hc0 (commSub_fixed_eq_one hC hτ3 hfix)

private lemma j2_exists_L_not_Y (hC : Levi108 K L R N Y ρ μ T) :
    ∃ l : 𝓜, l ∈ L ∧ l ∉ Y := by
  let u : Fin 3 → K := Pi.single 1 1
  have hu0 : u 0 = 0 := by simp [u]
  obtain ⟨l, hlL, hlρ⟩ := hC.exists_L u hu0
  refine ⟨l, hlL, ?_⟩
  intro hlY
  have hlN : l ∈ N := hC.Y_le_N hlY
  have hρl1 : (ρ ⟨l, hC.L_le_R hlL⟩ : Matrix (Fin 3) (Fin 3) K) = 1 := by
    have hmem : (⟨l, hC.L_le_R hlL⟩ : ↥R) ∈ ρ.ker := by
      rw [hC.ker_rho]
      exact Subgroup.mem_subgroupOf.mpr hlN
    have := MonoidHom.mem_ker.mp hmem
    exact congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) this
  rw [hlρ] at hρl1
  have h01 : (1 + Matrix.vecMulVec (e₀ K) u : Matrix (Fin 3) (Fin 3) K) 0 1 = 1 := by
    simp [Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec, e₀, u]
  rw [hρl1] at h01
  simp at h01

private lemma j2_kernel_ne_top (hC : Levi108 K L R N Y ρ μ T) :
    ((conjAction hC).comp
      (Subgroup.normalClosure (Xlevi L R : Set (GG L))).subtype).ker ≠ ⊤ := by
  obtain ⟨l, hlL, hlY⟩ := j2_exists_L_not_Y hC
  have hnotfix : ¬ ∀ g : ↥(NL L), mkG L g ∈ Xlevi L R →
      (g : 𝓜) * l * (g : 𝓜)⁻¹ = l := by
    intro hfix
    exact hlY ((hC.fix_Xlevi_iff hlL).mp hfix)
  push Not at hnotfix
  obtain ⟨g, hgX, hgne⟩ := hnotfix
  let W : Subgroup (GG L) := Subgroup.normalClosure (Xlevi L R : Set (GG L))
  let φ : W →* MulAut L := (conjAction hC).comp W.subtype
  intro hker
  have hx : (⟨mkG L g, Subgroup.subset_normalClosure hgX⟩ : W) ∈ φ.ker := by
    rw [hker]
    exact Subgroup.mem_top _
  have hφ1 : φ ⟨mkG L g, Subgroup.subset_normalClosure hgX⟩ = 1 :=
    MonoidHom.mem_ker.mp hx
  have hc1 : conjAction hC (mkG L g) = 1 := by simpa [φ] using hφ1
  have hact : (conjAction hC (mkG L g)) (⟨l, hlL⟩ : L) = ⟨l, hlL⟩ := by rw [hc1]; rfl
  have hcoe := congrArg (fun x : L => (x : 𝓜)) hact
  rw [conjAction_apply] at hcoe
  exact hgne hcoe

private lemma j2_false_of_injective (hC : Levi108 K L R N Y ρ μ T)
    (hHJ : Tim79a.AschbacherHJRepresentationStatement) (hL : Nat.card L < 2 ^ 12)
    {W : Subgroup (GG L)} (eJ : W ≃* NativeSporadic.J2)
    {φ : W →* MulAut L} (hφinj : Function.Injective φ) : False := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hC.elemAb_L.isPGroup
  haveI : IsMulCommutative L := hC.elemAb_L.1
  obtain ⟨eL⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (fun a b => mul_comm' a b)
    (fun a => Subtype.ext (by simpa [pow_two] using hC.elemAb_L.2 (a : 𝓜) a.2)) hn
  let ρJ : NativeSporadic.J2 →* GL (Fin n) (ZMod 2) :=
    (CFSG.SectionRank.Ccomm.elemAutEquivGL eL).toMonoidHom.comp (φ.comp eJ.symm.toMonoidHom)
  have hρJ : Function.Injective ρJ :=
    (CFSG.SectionRank.Ccomm.elemAutEquivGL eL).injective.comp
      (hφinj.comp eJ.symm.injective)
  have h12 := hHJ n ρJ hρJ
  have hlt : 2 ^ n < 2 ^ 12 := by rw [← hn]; exact hL
  have hnlt : n < 12 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
  omega

theorem Levi108.not_J2 (hC : Levi108 K L R N Y ρ μ T)
    (hHJ : Tim79a.AschbacherHJRepresentationStatement) (hL : Nat.card L < 2 ^ 12) :
    ¬ NativeSporadic.IsSporadic (Subgroup.normalClosure (Xlevi L R : Set (GG L))) .J2 := by
  intro hSporadic
  let W : Subgroup (GG L) := Subgroup.normalClosure (Xlevi L R : Set (GG L))
  let φ : W →* MulAut L := (conjAction hC).comp W.subtype
  have hker_ne_top : φ.ker ≠ ⊤ := by simpa [W, φ] using j2_kernel_ne_top hC
  let eJ := hSporadic.some
  have hJ2simple : IsSimpleGroup (NativeSporadic.Carrier TauCeti.SporadicName.J2) := by
    change IsSimpleGroup NativeSporadic.J2
    exact CFSG.Sporadic.J2.isSimpleGroup_J2
  letI : IsSimpleGroup (NativeSporadic.Carrier TauCeti.SporadicName.J2) := hJ2simple
  haveI hWsimple : IsSimpleGroup W := MulEquiv.isSimpleGroup eJ
  haveI : φ.ker.Normal := MonoidHom.normal_ker φ
  have hker_bot : φ.ker = ⊥ := by
    rcases hWsimple.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact h
    · exact absurd h hker_ne_top
  have hφinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker_bot
  exact j2_false_of_injective hC hHJ hL eJ hφinj

private lemma exists_tau_conj_data (hC : Levi108 K L R N Y ρ μ T)
    (hq : Nat.card K = 4) :
    ∃ (τ : ↥(NL L)) (hτ : (τ : 𝓜) ∈ R) (ω : K),
      (τ : 𝓜) ^ 3 = 1 ∧ ω ≠ 1 ∧
      (ρ ⟨τ, hτ⟩ : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) ω ∧
      mkG L τ ∈ Kfrak L R ∧
      (MulAut.conjNormal (mkG L τ) :
        MulAut (Subgroup.normalClosure (Xlevi L R : Set (GG L)))) ^ 3 = 1 ∧
      (∀ x : Subgroup.normalClosure (Xlevi L R : Set (GG L)),
        (x : GG L) ∈ Xlevi L R →
          (MulAut.conjNormal (mkG L τ)) x = x) := by
  obtain ⟨τ, hτR, hτord, ω, hω, hω3, hρτ, hτK⟩ := hC.exists_tau hq
  let W : Subgroup (GG L) := Subgroup.normalClosure (Xlevi L R : Set (GG L))
  haveI hWnormal : W.Normal := Subgroup.normalClosure_normal
  let τhat : GG L := mkG L τ
  have hτ3 : (τ : 𝓜) ^ 3 = 1 := by
    rw [← hτord]
    exact pow_orderOf_eq_one _
  have hτ3' : τ ^ 3 = 1 := Subtype.ext (by simpa using hτ3)
  have hτhat3 : τhat ^ 3 = 1 := by
    calc τhat ^ 3 = mkG L (τ ^ 3) := (map_pow (mkG L) τ 3).symm
      _ = mkG L 1 := by rw [hτ3']
      _ = 1 := map_one _
  have hαW3 : (MulAut.conjNormal τhat : MulAut W) ^ 3 = 1 := by
    change (MulAut.conjNormal τhat) ^ 3 = 1
    rw [← map_pow, hτhat3, map_one]
  have hfixX : ∀ x : W, (x : GG L) ∈ Xlevi L R →
      (MulAut.conjNormal τhat : MulAut W) x = x := by
    intro x hx
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    have hcomm : (x : GG L) * τhat = τhat * (x : GG L) :=
      (Subgroup.mem_centralizer_iff.mp hτK) (x : GG L) hx
    calc τhat * (x : GG L) * τhat⁻¹ = ((x : GG L) * τhat) * τhat⁻¹ := by rw [hcomm]
      _ = (x : GG L) := by rw [mul_assoc, mul_inv_cancel, mul_one]
  exact ⟨τ, hτR, ω, hτ3, hω, hρτ, hτK, hαW3, hfixX⟩

private lemma m12_alpha_eq_one (hC : Levi108 K L R N Y ρ μ T)
    (hM12 : ComponentClassification.RankTwoClassical.M12AutThreeFive) (hq : Nat.card K = 4)
    {τ : ↥(NL L)} (hτR : (τ : 𝓜) ∈ R) (hτK : mkG L τ ∈ Kfrak L R)
    {ω : K} (hτ3 : (τ : 𝓜) ^ 3 = 1) (hω : ω ≠ 1)
    (hρτ : (ρ ⟨τ, hτR⟩ : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) ω)
    (hαW3 : (MulAut.conjNormal (mkG L τ) :
      MulAut (Subgroup.normalClosure (Xlevi L R : Set (GG L)))) ^ 3 = 1)
    (hfixX : ∀ x : Subgroup.normalClosure (Xlevi L R : Set (GG L)),
      (x : GG L) ∈ Xlevi L R →
        (MulAut.conjNormal (mkG L τ)) x = x)
    (hSporadic : NativeSporadic.IsSporadic
      (Subgroup.normalClosure (Xlevi L R : Set (GG L))) .M12) :
    (MulAut.conjNormal (mkG L τ) :
      MulAut (Subgroup.normalClosure (Xlevi L R : Set (GG L)))) = 1 := by
  let W : Subgroup (GG L) := Subgroup.normalClosure (Xlevi L R : Set (GG L))
  let αW : MulAut W := MulAut.conjNormal (mkG L τ)
  let eW := hSporadic.some
  have hM12simple : IsSimpleGroup (NativeSporadic.Carrier TauCeti.SporadicName.M12) := by
    change IsSimpleGroup NativeSporadic.M12
    exact (CFSG.Sporadic.Mathieu.fam_m12_simplicity).2.2
  letI : IsSimpleGroup (NativeSporadic.Carrier TauCeti.SporadicName.M12) := hM12simple
  haveI hWsimple : IsSimpleGroup W := MulEquiv.isSimpleGroup eW
  have hWcard : Nat.card W = 95040 := by
    rw [Nat.card_congr eW.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M12
  have h5dvd : 5 ∣ Nat.card (Xlevi L R) := by
    rw [card_Xlevi_eq_sixty hC hq]
    norm_num
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' 5 h5dvd
  have hxW : x.val ∈ W := Subgroup.subset_normalClosure x.2
  let h : W := ⟨x.val, hxW⟩
  have hh5 : orderOf h = 5 := by
    rw [← Subgroup.orderOf_coe h]
    change orderOf x.val = 5
    rw [Subgroup.orderOf_coe x]
    exact hxord
  have hfixh : αW h = h := hfixX h (by simpa [h] using x.2)
  exact hM12 W hSporadic αW ⟨1, by simpa [αW] using hαW3⟩ h hh5 hfixh

theorem Levi108.not_M12 (hC : Levi108 K L R N Y ρ μ T)
    (hM12 : ComponentClassification.RankTwoClassical.M12AutThreeFive) (hq : Nat.card K = 4) :
    ¬ NativeSporadic.IsSporadic (Subgroup.normalClosure (Xlevi L R : Set (GG L))) .M12 := by
  intro hSporadic
  obtain ⟨τ, hτR, ω, hτ3, hω, hρτ, hτK, hαW3, hfixX⟩ := exists_tau_conj_data hC hq
  let W : Subgroup (GG L) := Subgroup.normalClosure (Xlevi L R : Set (GG L))
  haveI hWnormal : W.Normal := Subgroup.normalClosure_normal
  let τhat : GG L := mkG L τ
  let αW : MulAut W := MulAut.conjNormal τhat
  have hαW1 : αW = 1 := m12_alpha_eq_one hC hM12 hq hτR hτK hτ3 hω hρτ hαW3 hfixX hSporadic
  obtain ⟨eW⟩ := hSporadic
  have hM12simple : IsSimpleGroup (NativeSporadic.Carrier TauCeti.SporadicName.M12) := by
    change IsSimpleGroup NativeSporadic.M12
    exact (CFSG.Sporadic.Mathieu.fam_m12_simplicity).2.2
  letI : IsSimpleGroup (NativeSporadic.Carrier TauCeti.SporadicName.M12) := hM12simple
  haveI hWsimple : IsSimpleGroup W := MulEquiv.isSimpleGroup eW
  have hWcard : Nat.card W = 95040 := by
    rw [Nat.card_congr eW.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M12
  have hWτ : W ≤ Subgroup.centralizer ({τhat} : Set (GG L)) := by
    intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h : αW ⟨w, hw⟩ = ⟨w, hw⟩ := by rw [hαW1]; rfl
    have h' := congrArg (fun y : W => (y : GG L)) h
    rw [MulAut.conjNormal_apply] at h'
    calc (w : GG L) * τhat = (τhat * w * τhat⁻¹) * τhat := by rw [h']
      _ = τhat * (w : GG L) := by group
  exact Levi108.false_of_simple_le_centralizer hC hq hτR hτ3 hω hρτ hWsimple
    (by rw [hWcard]; norm_num) Subgroup.subset_normalClosure hWτ

private lemma a9_fixXA (hC : Levi108 K L R N Y ρ μ T) (hq : Nat.card K = 4)
    {e : Subgroup.normalClosure (Xlevi L R : Set (GG L)) ≃* alternatingGroup (Fin 9)}
    {αW : MulAut (Subgroup.normalClosure (Xlevi L R : Set (GG L)))}
    (hfixX : ∀ x : Subgroup.normalClosure (Xlevi L R : Set (GG L)),
      (x : GG L) ∈ Xlevi L R → αW x = x) :
    ∀ x ∈ ((Xlevi L R).subgroupOf
        (Subgroup.normalClosure (Xlevi L R : Set (GG L)))).map e.toMonoidHom,
      (MulAut.congr e) αW x = x := by
  let W : Subgroup (GG L) := Subgroup.normalClosure (Xlevi L R : Set (GG L))
  intro x hx
  obtain ⟨xw, hxw, rfl⟩ := Subgroup.mem_map.mp hx
  have hfixw : αW (xw : W) = (xw : W) :=
    hfixX (xw : W) (Subgroup.mem_subgroupOf.mp hxw)
  change ((MulAut.congr e) αW) (e (xw : W)) = e (xw : W)
  rw [show ((MulAut.congr e) αW) (e (xw : W)) = e (αW (xw : W)) by
    rw [MulAut.congr_apply]
    simp [MulEquiv.trans_apply]]
  rw [hfixw]

private lemma a9_transport (hC : Levi108 K L R N Y ρ μ T) (hq : Nat.card K = 4)
    {e : Subgroup.normalClosure (Xlevi L R : Set (GG L)) ≃* alternatingGroup (Fin 9)}
    {αW : MulAut (Subgroup.normalClosure (Xlevi L R : Set (GG L)))}
    (hαW3 : αW ^ 3 = 1)
    (hfixX : ∀ x : Subgroup.normalClosure (Xlevi L R : Set (GG L)),
      (x : GG L) ∈ Xlevi L R → αW x = x) :
    ∃ WA : Subgroup (alternatingGroup (Fin 9)),
      ((Xlevi L R).subgroupOf (Subgroup.normalClosure (Xlevi L R : Set (GG L)))).map
          e.toMonoidHom ≤ WA ∧
      (∀ w ∈ WA, (MulAut.congr e) αW w = w) ∧
      IsSimpleGroup WA ∧ 180 < Nat.card WA := by
  let W : Subgroup (GG L) := Subgroup.normalClosure (Xlevi L R : Set (GG L))
  let αA : MulAut (alternatingGroup (Fin 9)) := (MulAut.congr e) αW
  have hαA3 : αA ^ 3 = 1 := by
    change ((MulAut.congr e) αW) ^ 3 = 1
    rw [← map_pow, hαW3, map_one]
  let hXW : Xlevi L R ≤ W := Subgroup.subset_normalClosure
  let XW : Subgroup W := (Xlevi L R).subgroupOf W
  let XA : Subgroup (alternatingGroup (Fin 9)) := XW.map e.toMonoidHom
  haveI hXsimple : IsSimpleGroup (Xlevi L R) := isSimpleGroup_Xlevi hC hq
  haveI hXWsimple : IsSimpleGroup XW := (Subgroup.subgroupOfEquivOfLe hXW).isSimpleGroup
  haveI hXAsimple : IsSimpleGroup (XW.map e.toMonoidHom) :=
    (e.subgroupMap XW).symm.isSimpleGroup
  have hXAcard : Nat.card XA = 60 := by
    rw [show Nat.card XA = Nat.card XW from
      Nat.card_congr (e.subgroupMap XW).symm.toEquiv]
    rw [show Nat.card XW = Nat.card (Xlevi L R) from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXW).toEquiv]
    exact card_Xlevi_eq_sixty hC hq
  have hfixXA : ∀ x ∈ XA, αA x = x := by
    have h := a9_fixXA (hC := hC) (hq := hq) (e := e) (αW := αW) hfixX
    simpa [XA, αA] using h
  obtain ⟨WA, hXWA, hfixWA, hWAsimple, hWAcard⟩ :=
    CFSG.Permutation.exists_simple_fixed_of_alternatingNine_aut_cube αA hαA3 XA hXAsimple
      hXAcard hfixXA
  exact ⟨WA, hXWA, hfixWA, hWAsimple, hWAcard⟩

private lemma a9_pullback (hC : Levi108 K L R N Y ρ μ T) (hq : Nat.card K = 4)
    {e : Subgroup.normalClosure (Xlevi L R : Set (GG L)) ≃* alternatingGroup (Fin 9)}
    {WA : Subgroup (alternatingGroup (Fin 9))}
    (hXWA : ((Xlevi L R).subgroupOf
        (Subgroup.normalClosure (Xlevi L R : Set (GG L)))).map e.toMonoidHom ≤ WA)
    (hWAsimple : IsSimpleGroup WA) (hWAcard : 180 < Nat.card WA) :
    ∃ W₁ : Subgroup (GG L), W₁ = (WA.map e.symm.toMonoidHom).map
        (Subgroup.normalClosure (Xlevi L R : Set (GG L))).subtype ∧
      IsSimpleGroup W₁ ∧ 180 < Nat.card W₁ ∧ Xlevi L R ≤ W₁ := by
  let W : Subgroup (GG L) := Subgroup.normalClosure (Xlevi L R : Set (GG L))
  let W₁W : Subgroup W := WA.map e.symm.toMonoidHom
  let W₁ : Subgroup (GG L) := W₁W.map W.subtype
  haveI hW₁Wsimple : IsSimpleGroup W₁W := (e.symm.subgroupMap WA).symm.isSimpleGroup
  haveI hW₁simple : IsSimpleGroup W₁ :=
    (Subgroup.equivMapOfInjective W₁W W.subtype W.subtype_injective).symm.isSimpleGroup
  have hW₁card : 180 < Nat.card W₁ := by
    rw [show Nat.card W₁ = Nat.card W₁W from
      (Nat.card_congr (Subgroup.equivMapOfInjective W₁W W.subtype
        W.subtype_injective).toEquiv).symm]
    rw [show Nat.card W₁W = Nat.card WA from
      (Nat.card_congr (e.symm.subgroupMap WA).toEquiv).symm]
    exact hWAcard
  have hXW₁ : Xlevi L R ≤ W₁ := by
    intro x hx
    have hxW : x ∈ W := Subgroup.subset_normalClosure hx
    let xw : (Xlevi L R).subgroupOf W := ⟨⟨x, hxW⟩, hx⟩
    have hxWA : e xw ∈ WA := hXWA (Subgroup.mem_map_of_mem e.toMonoidHom xw.2)
    have hxmap : x ∈ W₁W.map W.subtype := by
      refine Subgroup.mem_map.mpr ⟨e.symm (e xw), ?_, ?_⟩
      · exact Subgroup.mem_map_of_mem e.symm.toMonoidHom hxWA
      · simpa [xw] using congrArg (fun y : (Xlevi L R).subgroupOf W => ((y : W) : GG L))
          (e.symm_apply_apply xw)
    exact hxmap
  exact ⟨W₁, rfl, hW₁simple, hW₁card, hXW₁⟩

private lemma a9_pullback_centralizer (hC : Levi108 K L R N Y ρ μ T) {τ : ↥(NL L)}
    (hτR : (τ : 𝓜) ∈ R)
    {e : Subgroup.normalClosure (Xlevi L R : Set (GG L)) ≃* alternatingGroup (Fin 9)}
    {WA : Subgroup (alternatingGroup (Fin 9))}
    (hfixWA : ∀ w ∈ WA,
      (MulAut.congr e) (MulAut.conjNormal (mkG L τ)) w = w) :
    (WA.map e.symm.toMonoidHom).map
      (Subgroup.normalClosure (Xlevi L R : Set (GG L))).subtype ≤
        Subgroup.centralizer ({mkG L τ} : Set (GG L)) := by
  let W : Subgroup (GG L) := Subgroup.normalClosure (Xlevi L R : Set (GG L))
  let W₁W : Subgroup W := WA.map e.symm.toMonoidHom
  let W₁ : Subgroup (GG L) := W₁W.map W.subtype
  have hαinv : (MulAut.congr e.symm) ((MulAut.congr e) (MulAut.conjNormal (mkG L τ))) =
      (MulAut.conjNormal (mkG L τ) : MulAut W) := by
    change (MulAut.congr e).symm ((MulAut.congr e) (MulAut.conjNormal (mkG L τ))) = _
    rw [MulEquiv.symm_apply_apply]
  have hfixW₁ : ∀ w : W₁W,
      (MulAut.conjNormal (mkG L τ) : MulAut W) (w : W) = (w : W) := by
    intro w
    obtain ⟨wa, hwa, hwa_eq⟩ := Subgroup.mem_map.mp w.2
    rw [← hwa_eq]
    change (MulAut.conjNormal (mkG L τ) : MulAut W) (e.symm wa) = e.symm wa
    rw [show (MulAut.conjNormal (mkG L τ) : MulAut W) =
      (MulAut.congr e.symm) ((MulAut.congr e) (MulAut.conjNormal (mkG L τ))) from hαinv.symm]
    rw [show ((MulAut.congr e.symm) ((MulAut.congr e) (MulAut.conjNormal (mkG L τ))))
        (e.symm wa) = e.symm ((MulAut.congr e) (MulAut.conjNormal (mkG L τ)) wa) by
      rw [MulAut.congr_apply]
      simp [MulEquiv.trans_apply]]
    rw [hfixWA wa hwa]
  intro w hw
  obtain ⟨ww, hww, rfl⟩ := Subgroup.mem_map.mp hw
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hfix := hfixW₁ ⟨ww, hww⟩
  have h := congrArg (fun y : W => (y : GG L)) hfix
  rw [MulAut.conjNormal_apply] at h
  calc (ww : GG L) * mkG L τ = (mkG L τ * ww * (mkG L τ)⁻¹) * mkG L τ := by rw [h]
    _ = mkG L τ * (ww : GG L) := by group

theorem Levi108.not_A9 (hC : Levi108 K L R N Y ρ μ T) (hq : Nat.card K = 4) :
    ¬ Nonempty (Subgroup.normalClosure (Xlevi L R : Set (GG L)) ≃* alternatingGroup (Fin 9)) := by
  intro hA9
  obtain ⟨τ, hτR, ω, hτ3, hω, hρτ, hτK, hαW3, hfixX⟩ := exists_tau_conj_data hC hq
  let W : Subgroup (GG L) := Subgroup.normalClosure (Xlevi L R : Set (GG L))
  haveI hWnormal : W.Normal := Subgroup.normalClosure_normal
  let τhat : GG L := mkG L τ
  let αW : MulAut W := MulAut.conjNormal τhat
  let e : W ≃* alternatingGroup (Fin 9) := hA9.some
  obtain ⟨WA, hXWA, hfixWA, hWAsimple, hWAcard⟩ :=
    a9_transport (hC := hC) (hq := hq) (e := e) (αW := αW) hαW3 hfixX
  obtain ⟨W₁, hW₁eq, hW₁simple, hW₁card, hXW₁⟩ :=
    a9_pullback (hC := hC) (hq := hq) (e := e) hXWA hWAsimple hWAcard
  have hW₁τ : W₁ ≤ Subgroup.centralizer ({τhat} : Set (GG L)) := by
    rw [hW₁eq]
    exact a9_pullback_centralizer (hC := hC) (τ := τ) hτR (e := e) hfixWA
  exact Levi108.false_of_simple_le_centralizer hC hq hτR hτ3 hω hρτ hW₁simple hW₁card hXW₁ hW₁τ

theorem Levi108.not_exception
    (hC : Levi108 K L R N Y ρ μ T) (hHJ : Tim79a.AschbacherHJRepresentationStatement)
    (hM12 : ComponentClassification.RankTwoClassical.M12AutThreeFive) (hq : Nat.card K = 4)
    (hL : Nat.card L < 2 ^ 12) :
    ¬ (Nonempty (Subgroup.normalClosure (Xlevi L R : Set (GG L)) ≃* alternatingGroup (Fin 9)) ∨
      NativeSporadic.IsSporadic (Subgroup.normalClosure (Xlevi L R : Set (GG L))) .M12 ∨
      NativeSporadic.IsSporadic (Subgroup.normalClosure (Xlevi L R : Set (GG L))) .J2) := by
  rintro (hA9 | hM12sp | hJ2)
  · exact Levi108.not_A9 hC hq hA9
  · exact Levi108.not_M12 hC hM12 hq hM12sp
  · exact Levi108.not_J2 hC hHJ hL hJ2

end CFSG.RankThree.GF2n.Stroth80.Sec108
