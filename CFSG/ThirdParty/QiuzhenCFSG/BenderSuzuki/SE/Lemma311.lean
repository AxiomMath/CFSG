module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Theorem4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_4
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CoprimeHall
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

namespace CFSG
end CFSG
open CFSG

/-!
# Lemma 3.11

The generic action-theoretic construction used in Section 7.  Starting from
the operational Z-star factorization, it produces the odd prime orbit,
inversion action, pointwise-stabilizer control, and swapping involutions.
-/

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise IsMulCommutative

noncomputable section

universe u v

private theorem lemma311_conjugates_eq_inv_of_fixedPoint_free_involution
    {G : Type u} [Group G] (F : Subgroup G) [F.Normal]
    (hFcomm : IsMulCommutative F) {z : G} (hz : IsInvolution z)
    (hfixedFree : F ⊓ Subgroup.centralizer ({z} : Set G) = ⊥) :
    ∀ x : G, x ∈ F → z * x * z⁻¹ = x⁻¹ := by
  intro x hx
  let d : G := x * (z * x * z⁻¹)
  have hzxF : z * x * z⁻¹ ∈ F := by
    exact (inferInstance : F.Normal).conj_mem x hx z
  have hdF : d ∈ F := F.mul_mem hx hzxF
  have hcommF : ∀ a b : G, a ∈ F → b ∈ F → a * b = b * a := by
    intro a b ha hb
    letI : IsMulCommutative F := hFcomm
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : F) ⟨b, hb⟩)
  have hdFix : z * d * z⁻¹ = d := by
    dsimp [d]
    have hz2 : z * z = 1 := by
      simpa [pow_two] using hz.sq_eq_one
    have hxx : x * (z * x * z⁻¹) = (z * x * z⁻¹) * x :=
      hcommF x (z * x * z⁻¹) hx hzxF
    calc
      z * (x * (z * x * z⁻¹)) * z⁻¹ =
          z * ((z * x * z⁻¹) * x) * z⁻¹ := by rw [hxx]
      _ = x * (z * x * z⁻¹) := by
        rw [hz.inv_eq_self]
        calc
          z * (z * x * z * x) * z =
              (z * z) * x * (z * x * z) := by group
          _ = x * (z * x * z) := by rw [hz2]; simp
  have hdC : d ∈ Subgroup.centralizer ({z} : Set G) := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hmul := congrArg (fun t : G => t * z) hdFix
    simpa [mul_assoc] using hmul.symm
  have hdBot : d ∈ F ⊓ Subgroup.centralizer ({z} : Set G) := ⟨hdF, hdC⟩
  have hdOne : d = 1 := by
    rw [hfixedFree] at hdBot
    exact hdBot
  dsimp [d] at hdOne
  have hxEq : x = (z * x * z⁻¹)⁻¹ := mul_eq_one_iff_eq_inv.mp hdOne
  simpa using (congrArg Inv.inv hxEq).symm
/-!  The maximal, faithful branch of the source proof of Lemma 3.11.  The
factorization is the operational content of `z ∈ Z*(G)` used in the latex. -/
private theorem lemma311_maximal_regular_core
    {G : Type u} {Omega : Type v} [Group G] [Finite G]
    [MulAction G Omega] [Finite Omega] [FaithfulSMul G Omega]
    [MulAction.IsPretransitive G Omega]
    (Y : Subgroup G) (z : G) (alpha : Omega)
    (hY : MulAction.stabilizer G alpha = Y)
    (hYproper : Y ≠ ⊤)
    (hmax : IsCoatom Y)
    (hz : IsInvolution z)
    (hcent : Subgroup.centralizer ({z} : Set G) ≤ Y)
    (hfactor : pPrimeCore 2 G ⊔
      Subgroup.centralizer ({z} : Set G) = ⊤) :
    ∃ (F : Subgroup G) (r : ℕ),
      F.Normal ∧ Nat.Prime r ∧ IsElementaryAbelian r F ∧
      F ≠ ⊥ ∧ Odd (Nat.card F) ∧ MulAction.IsPretransitive F Omega ∧
      (∀ omega : Omega, MulAction.stabilizer F omega = ⊥) ∧
      Disjoint F Y ∧ F ⊔ Y = ⊤ ∧
      (∀ x : G, x ∈ F → z * x * z⁻¹ = x⁻¹) := by
  classical
  let N : Subgroup G := pPrimeCore 2 G
  have hNnormal : N.Normal := by
    dsimp [N]
    exact pPrimeCore_normal
  have hNodd : Odd (Nat.card N) := by
    dsimp [N]
    exact Nat.coprime_two_left.mp
      (by simpa using pPrimeCore_coprime_card (p := 2) (G := G))
  have hNne : N ≠ ⊥ := by
    intro hNbot
    have hcentTop : Subgroup.centralizer ({z} : Set G) = ⊤ := by
      simpa [N, hNbot] using hfactor
    have htopY : (⊤ : Subgroup G) ≤ Y := by
      rw [← hcentTop]
      exact hcent
    exact hYproper (top_unique htopY)
  have hNsolv : Group.IsSolvable N := odd_order_theorem N hNodd
  obtain ⟨F, hFnorm, hFleN, hFne, hFmin⟩ :=
    exists_minimal_normal_le (G := G) N hNnormal hNne
  letI : F.Normal := hFnorm
  letI : IsMinimalNormal F := {
    minimal := by
      intro K hKnormal hKF
      by_cases hKbot : K = ⊥
      · exact Or.inl hKbot
      · exact Or.inr (hFmin K hKnormal hKF hKbot)
  }
  let FN : Subgroup N := F.subgroupOf N
  let eFN : FN ≃* F := Subgroup.subgroupOfEquivOfLe hFleN
  letI : Group.IsSolvable N := hNsolv
  have hFNsolv : Group.IsSolvable FN := inferInstance
  letI : Group.IsSolvable FN := hFNsolv
  have hFsolv : Group.IsSolvable F :=
    Group.isSolvable_of_surjective (f := eFN.toMonoidHom) eFN.surjective
  letI : Group.IsSolvable F := hFsolv
  obtain ⟨r, hr, hFelem⟩ := minimalNormal_solvable_exists_isElementaryAbelian F
  letI : IsElementaryAbelian r F := hFelem
  have hFodd : Odd (Nat.card F) :=
    Odd.of_dvd_nat hNodd (Subgroup.card_dvd_of_le hFleN)
  have hOmegaNontriv : Nontrivial Omega := by
    rcases subsingleton_or_nontrivial Omega with hsub | hnon
    · letI : Subsingleton Omega := hsub
      have hstabTop : MulAction.stabilizer G alpha = ⊤ := by
        rw [eq_top_iff]
        intro g _
        exact MulAction.mem_stabilizer_iff.mpr (Subsingleton.elim _ _)
      apply False.elim
      apply hYproper
      rw [← hY, hstabTop]
    · exact hnon
  letI : Nontrivial Omega := hOmegaNontriv
  have hcoatomStab : IsCoatom (MulAction.stabilizer G alpha) := by
    simpa [hY] using hmax
  haveI : MulAction.IsPreprimitive G Omega :=
    (MulAction.isCoatom_stabilizer_iff_preprimitive (G := G) alpha).mp hcoatomStab
  haveI : MulAction.IsQuasiPreprimitive G Omega :=
    MulAction.IsPreprimitive.isQuasiPreprimitive
  have hfixed_ne_univ : MulAction.fixedPoints F Omega ≠ Set.univ := by
    intro hfixed
    apply hFne
    rw [eq_bot_iff]
    intro f hf
    have hfix_all : ∀ omega : Omega, f • omega = omega := by
      intro omega
      have hω : omega ∈ MulAction.fixedPoints F Omega := by
        rw [hfixed]
        trivial
      exact MulAction.mem_fixedPoints.mp hω ⟨f, hf⟩
    have hf_one : (f : G) = 1 :=
      FaithfulSMul.eq_of_smul_eq_smul (m₁ := (f : G)) (m₂ := (1 : G)) (by
        intro omega
        calc
          (f : G) • omega = omega := hfix_all omega
          _ = (1 : G) • omega := (one_smul G omega).symm)
    exact Subgroup.mem_bot.mpr hf_one
  have hFtrans : MulAction.IsPretransitive F Omega :=
    MulAction.IsQuasiPreprimitive.isPretransitive_of_normal hfixed_ne_univ
  letI : MulAction.IsPretransitive F Omega := hFtrans
  have hFregular : ∀ omega : Omega,
      MulAction.stabilizer F omega = ⊥ := by
    intro omega
    rw [eq_bot_iff]
    intro f hf
    have hfix_all : ∀ eta : Omega, f • eta = eta := by
      intro eta
      obtain ⟨a, ha⟩ :=
        @MulAction.IsPretransitive.exists_smul_eq F Omega
          inferInstance inferInstance omega eta
      have hcomm : f * a = a * f := mul_comm f a
      calc
        f • eta = f • (a • omega) := by rw [ha]
        _ = (f * a) • omega := by rw [mul_smul]
        _ = (a * f) • omega := by rw [hcomm]
        _ = a • (f • omega) := by rw [mul_smul]
        _ = a • omega := by rw [show f • omega = omega from hf]
        _ = eta := ha
    have hf_one : (f : G) = 1 :=
      FaithfulSMul.eq_of_smul_eq_smul (m₁ := (f : G)) (m₂ := (1 : G)) (by
        intro eta
        calc
          (f : G) • eta = eta := hfix_all eta
          _ = (1 : G) • eta := (one_smul G eta).symm)
    exact Subgroup.mem_bot.mpr (Subtype.ext hf_one)
  have hdis : Disjoint F Y := by
    rw [disjoint_iff, eq_bot_iff]
    intro g hg
    let gF : F := ⟨g, hg.1⟩
    have hgstab : gF ∈ MulAction.stabilizer F alpha := by
      have : (g : G) ∈ MulAction.stabilizer G alpha := by
        simpa [hY] using hg.2
      change gF • alpha = alpha
      simpa [gF] using this
    rw [hFregular alpha] at hgstab
    have hgFone : gF = (1 : F) := Subgroup.mem_bot.mp hgstab
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hgFone)
  have hsup : F ⊔ Y = ⊤ := by
    rw [eq_top_iff]
    intro g _hg
    obtain ⟨f, hf⟩ :=
      @MulAction.IsPretransitive.exists_smul_eq F Omega
        inferInstance inferInstance alpha (g • alpha)
    have hfgstab : (f : G)⁻¹ * g ∈
        MulAction.stabilizer G alpha := by
      change ((f : G)⁻¹ * g) • alpha = alpha
      rw [mul_smul, inv_smul_eq_iff]
      exact hf.symm
    have hfgY : (f : G)⁻¹ * g ∈ Y := by simpa [hY] using hfgstab
    have hprod : (f : G) * ((f : G)⁻¹ * g) ∈ F ⊔ Y :=
      Subgroup.mul_mem_sup f.property hfgY
    simpa using hprod
  have hfixedFree : F ⊓ Subgroup.centralizer ({z} : Set G) = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hxFY : x ∈ F ⊓ Y := ⟨hx.1, hcent hx.2⟩
      rw [disjoint_iff.mp hdis] at hxFY
      exact hxFY
    · exact bot_le
  have hzinv : ∀ x : G, x ∈ F → z * x * z⁻¹ = x⁻¹ :=
    lemma311_conjugates_eq_inv_of_fixedPoint_free_involution
      F (inferInstance : IsMulCommutative F) hz hfixedFree
  exact ⟨F, r, hFnorm, hr, hFelem, hFne, hFodd, hFtrans, hFregular,
    hdis, hsup, hzinv⟩

private theorem lemma311_stabilizer_eq_centralizer
    {G : Type u} {Omega : Type v} [Group G] [Finite G]
    [MulAction G Omega] [Finite Omega] [FaithfulSMul G Omega]
    (F Y : Subgroup G) [F.Normal]
    (z : G) (alpha : Omega)
    (hFtrans : MulAction.IsPretransitive F Omega)
    (hY : MulAction.stabilizer G alpha = Y)
    (hzY : z ∈ Y) (hz : IsInvolution z)
    (hcent : Subgroup.centralizer ({z} : Set G) ≤ Y)
    (hzinv : ∀ x : G, x ∈ F → z * x * z⁻¹ = x⁻¹) :
    Y = Subgroup.centralizer ({z} : Set G) := by
  letI : MulAction.IsPretransitive F Omega := hFtrans
  have hCFbot : Y ⊓ Subgroup.centralizer (F : Set G) = ⊥ := by
    apply le_antisymm
    · intro c hc
      have hcAlpha : c • alpha = alpha := by
        apply MulAction.mem_stabilizer_iff.mp
        rw [hY]
        exact hc.1
      have hcAll : ∀ omega : Omega, c • omega = omega := by
        intro omega
        obtain ⟨f, hf⟩ :=
          @MulAction.IsPretransitive.exists_smul_eq F Omega
            inferInstance inferInstance alpha omega
        have hfG : (f : G) • alpha = omega := hf
        have hcomm : (f : G) * c = c * (f : G) :=
          (Subgroup.mem_centralizer_iff.mp hc.2) (f : G) f.property
        calc
          c • omega = c • ((f : G) • alpha) := by rw [hfG]
          _ = (c * (f : G)) • alpha := by rw [mul_smul]
          _ = ((f : G) * c) • alpha := by rw [hcomm]
          _ = (f : G) • (c • alpha) := by rw [mul_smul]
          _ = (f : G) • alpha := by rw [hcAlpha]
          _ = omega := hf
      have hcOne : c = 1 :=
        FaithfulSMul.eq_of_smul_eq_smul (m₁ := c) (m₂ := (1 : G)) (by
          intro omega
          calc
            c • omega = omega := hcAll omega
            _ = (1 : G) • omega := (one_smul G omega).symm)
      exact Subgroup.mem_bot.mpr hcOne
    · exact bot_le
  apply le_antisymm
  · intro y hy
    have haInv : ∀ f : G, f ∈ F →
        (y * z * y⁻¹) * f * (y * z * y⁻¹)⁻¹ = f⁻¹ := by
      intro f hf
      have hyf : y⁻¹ * f * y ∈ F := by
        simpa using (inferInstance : F.Normal).conj_mem f hf y⁻¹
      have hzf := hzinv (y⁻¹ * f * y) hyf
      calc
        (y * z * y⁻¹) * f * (y * z * y⁻¹)⁻¹ =
            y * (z * (y⁻¹ * f * y) * z⁻¹) * y⁻¹ := by group
        _ = y * ((y⁻¹ * f * y)⁻¹) * y⁻¹ := by rw [hzf]
        _ = f⁻¹ := by group
    let c : G := (y * z * y⁻¹) * z
    have hcY : c ∈ Y := by
      dsimp [c]
      exact Y.mul_mem (Y.mul_mem (Y.mul_mem hy hzY) (Y.inv_mem hy)) hzY
    have hcF : c ∈ Subgroup.centralizer (F : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      have hcconj : c * f * c⁻¹ = f := by
        calc
          c * f * c⁻¹ =
              (y * z * y⁻¹) * (z * f * z⁻¹) *
                (y * z * y⁻¹)⁻¹ := by
                  dsimp [c]
                  group
          _ = (y * z * y⁻¹) * f⁻¹ * (y * z * y⁻¹)⁻¹ := by
            rw [hzinv f hf]
          _ = ((y * z * y⁻¹) * f * (y * z * y⁻¹)⁻¹)⁻¹ := by
            group
          _ = (f⁻¹)⁻¹ := by rw [haInv f hf]
          _ = f := inv_inv f
      have hcf : c * f = f * c := by
        calc
          c * f = (c * f * c⁻¹) * c := by group
          _ = f * c := by rw [hcconj]
      exact hcf.symm
    have hcBot : c ∈ Y ⊓ Subgroup.centralizer (F : Set G) := ⟨hcY, hcF⟩
    have hcOne : c = 1 := by
      rw [hCFbot] at hcBot
      exact hcBot
    have haEq : y * z * y⁻¹ = z := by
      have := mul_eq_one_iff_eq_inv.mp hcOne
      simpa [hz.inv_eq_self] using this
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    calc
      y * z = (y * z * y⁻¹) * y := by group
      _ = z * y := by rw [haEq]
  · exact hcent

private theorem lemma311_prime_orbit_pointwise
    {G : Type u} {Omega : Type v} [Group G] [Finite G]
    [MulAction G Omega] [Finite Omega]
    (F R Y : Subgroup G) (z : G) (alpha : Omega)
    (hRprime : Nat.Prime (Nat.card R))
    (hRodd : Odd (Nat.card R))
    (hRleF : R ≤ F) (hz : IsInvolution z)
    (hY : MulAction.stabilizer G alpha = Y)
    (hYC : Y = Subgroup.centralizer ({z} : Set G))
    (hzinv : ∀ f : G, f ∈ F → z * f * z⁻¹ = f⁻¹) :
    ∀ {beta gamma},
      beta ∈ MulAction.orbit R alpha →
      gamma ∈ MulAction.orbit R alpha → beta ≠ gamma →
      ∀ x : G, x • beta = beta → x • gamma = gamma →
        ∀ delta, delta ∈ MulAction.orbit R alpha → x • delta = delta := by
  classical
  intro beta gamma hbeta hgamma hne x hxbeta hxgamma delta hdelta
  rcases MulAction.mem_orbit_iff.mp hbeta with ⟨q, hq⟩
  rcases MulAction.mem_orbit_iff.mp hgamma with ⟨s, hs⟩
  have hqG : (q : G) • alpha = beta := hq
  have hsG : (s : G) • alpha = gamma := hs
  have hqs : q ≠ s := by
    intro hqs
    apply hne
    calc
      beta = (q : G) • alpha := hqG.symm
      _ = (s : G) • alpha := by rw [hqs]
      _ = gamma := hsG
  have hqfix : ((q : G)⁻¹ * x * (q : G)) • alpha = alpha := by
    calc
      ((q : G)⁻¹ * x * (q : G)) • alpha =
          (q : G)⁻¹ • (x • ((q : G) • alpha)) := by
            simp only [mul_smul]
      _ = (q : G)⁻¹ • (x • beta) := by rw [hqG]
      _ = (q : G)⁻¹ • beta := by rw [hxbeta]
      _ = alpha := by rw [← hqG]; simp
  have hsfix : ((s : G)⁻¹ * x * (s : G)) • alpha = alpha := by
    calc
      ((s : G)⁻¹ * x * (s : G)) • alpha =
          (s : G)⁻¹ • (x • ((s : G) • alpha)) := by
            simp only [mul_smul]
      _ = (s : G)⁻¹ • (x • gamma) := by rw [hsG]
      _ = (s : G)⁻¹ • gamma := by rw [hxgamma]
      _ = alpha := by rw [← hsG]; simp
  have hqY : (q : G)⁻¹ * x * (q : G) ∈ Y := by
    rw [← hY]
    exact MulAction.mem_stabilizer_iff.mpr hqfix
  have hsY : (s : G)⁻¹ * x * (s : G) ∈ Y := by
    rw [← hY]
    exact MulAction.mem_stabilizer_iff.mpr hsfix
  have hqC : (q : G)⁻¹ * x * (q : G) ∈
      Subgroup.centralizer ({z} : Set G) := by
    rw [← hYC]
    exact hqY
  have hsC : (s : G)⁻¹ * x * (s : G) ∈
      Subgroup.centralizer ({z} : Set G) := by
    rw [← hYC]
    exact hsY
  have hqcommz : ((q : G)⁻¹ * x * (q : G)) * z =
      z * ((q : G)⁻¹ * x * (q : G)) :=
    Subgroup.mem_centralizer_singleton_iff.mp hqC
  have hscommz : ((s : G)⁻¹ * x * (s : G)) * z =
      z * ((s : G)⁻¹ * x * (s : G)) :=
    Subgroup.mem_centralizer_singleton_iff.mp hsC
  let a : G := (q : G) * z * (q : G)⁻¹
  let b : G := (s : G) * z * (s : G)⁻¹
  have hxa : x * a = a * x := by
    dsimp [a]
    calc
      x * ((q : G) * z * (q : G)⁻¹) =
          (q : G) * (((q : G)⁻¹ * x * (q : G)) * z) * (q : G)⁻¹ := by
            group
      _ = (q : G) * (z * ((q : G)⁻¹ * x * (q : G))) * (q : G)⁻¹ := by
            rw [hqcommz]
      _ = ((q : G) * z * (q : G)⁻¹) * x := by
            group
  have hxb : x * b = b * x := by
    dsimp [b]
    calc
      x * ((s : G) * z * (s : G)⁻¹) =
          (s : G) * (((s : G)⁻¹ * x * (s : G)) * z) * (s : G)⁻¹ := by
            group
      _ = (s : G) * (z * ((s : G)⁻¹ * x * (s : G))) * (s : G)⁻¹ := by
            rw [hscommz]
      _ = ((s : G) * z * (s : G)⁻¹) * x := by
            group
  have hxab : x * (a * b) = (a * b) * x := by
    calc
      x * (a * b) = (x * a) * b := by group
      _ = (a * x) * b := by rw [hxa]
      _ = a * (x * b) := by group
      _ = a * (b * x) := by rw [hxb]
      _ = (a * b) * x := by group
  let d : R := q * s⁻¹
  have hqsF : (q : G)⁻¹ * (s : G) ∈ F := by
    exact F.mul_mem (F.inv_mem (hRleF q.property)) (hRleF s.property)
  have hzinvQS := hzinv ((q : G)⁻¹ * (s : G)) hqsF
  have hzinvQS' : z * ((q : G)⁻¹ * (s : G)) * z =
      ((q : G)⁻¹ * (s : G))⁻¹ := by
    simpa [hz.inv_eq_self] using hzinvQS
  have hab : a * b = (d : G) ^ 2 := by
    dsimp [a, b, d]
    calc
      ((q : G) * z * (q : G)⁻¹) *
          ((s : G) * z * (s : G)⁻¹) =
          (q : G) * (z * ((q : G)⁻¹ * (s : G)) * z⁻¹) *
            (s : G)⁻¹ := by
              rw [hz.inv_eq_self]
              group
      _ = (q : G) * (((q : G)⁻¹ * (s : G))⁻¹) * (s : G)⁻¹ := by
            rw [hzinvQS]
      _ = ((q : G) * (s : G)⁻¹) ^ 2 := by
            simp [pow_two, mul_assoc]
  have hdne : d ≠ (1 : R) := by
    intro hd
    apply hqs
    apply Subtype.ext
    apply eq_of_mul_inv_eq_one
    have hdG := congrArg Subtype.val hd
    simpa [d] using hdG
  let d2 : R := d ^ 2
  have hd2ne : d2 ≠ (1 : R) := by
    intro hd2
    have hd2pow : d ^ 2 = (1 : R) := by simpa [d2] using hd2
    have hdorder : orderOf d = 2 := by
      apply orderOf_eq_prime
      · simpa [pow_two] using hd2pow
      · exact hdne
    have hdvd : orderOf d ∣ Nat.card R := orderOf_dvd_natCard d
    have htwo : 2 ∣ Nat.card R := by simpa [hdorder] using hdvd
    exact hRodd.not_two_dvd_nat htwo
  have hxd2 : x * (d2 : G) = (d2 : G) * x := by
    have hxab' := hxab
    rw [hab] at hxab'
    simpa [d2] using hxab'
  have hgen : Subgroup.zpowers d2 = (⊤ : Subgroup R) :=
    zpowers_eq_top_of_prime_card_of_ne_one hRprime hd2ne
  have hcommR : ∀ u : R, x * (u : G) = (u : G) * x := by
    intro u
    have hu : u ∈ Subgroup.zpowers d2 := by
      rw [hgen]
      trivial
    rcases Subgroup.mem_zpowers_iff.mp hu with ⟨k, hk⟩
    have hkG : (d2 : G) ^ k = (u : G) := by
      simpa using congrArg Subtype.val hk
    have hcomm : Commute x (d2 : G) := hxd2
    have hcommk := hcomm.zpow_right k
    simpa [hkG] using hcommk.eq
  have hqcomm : x * (q : G) = (q : G) * x := hcommR q
  have hscomm : x * (s : G) = (s : G) * x := hcommR s
  have hxqconj : (q : G)⁻¹ * x * (q : G) = x := by
    calc
      (q : G)⁻¹ * x * (q : G) = (q : G)⁻¹ * (x * (q : G)) := by group
      _ = (q : G)⁻¹ * ((q : G) * x) := by rw [hqcomm]
      _ = x := by group
  have hxz : x * z = z * x := by
    calc
      x * z = ((q : G)⁻¹ * x * (q : G)) * z := by rw [hxqconj]
      _ = z * ((q : G)⁻¹ * x * (q : G)) := hqcommz
      _ = z * x := by rw [hxqconj]
  have hxY : x ∈ Y := by
    rw [hYC]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hxz
  have hxalpha : x • alpha = alpha := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [hY]
    exact hxY
  rcases MulAction.mem_orbit_iff.mp hdelta with ⟨u, hu⟩
  have huG : (u : G) • alpha = delta := hu
  calc
    x • delta = x • ((u : G) • alpha) := by rw [huG]
    _ = (x * (u : G)) • alpha := by rw [mul_smul]
    _ = ((u : G) * x) • alpha := by rw [hcommR u]
    _ = (u : G) • (x • alpha) := by rw [mul_smul]
    _ = delta := by rw [hxalpha, huG]

private def lemma311Output
    {G : Type u} {Omega : Type v} [Group G] [Finite G]
    [MulAction G Omega] [Finite Omega]
    (_Y : Subgroup G) (z : G) (alpha : Omega) : Prop :=
  ∃ R : Subgroup G, ∃ Gamma : Set Omega,
    Gamma = MulAction.orbit R alpha ∧
    (∃ r : ℕ, Nat.Prime r ∧ Odd r ∧ IsPGroup r R ∧ Nat.card Gamma = r) ∧
    IsCyclic R ∧
    (∀ q : G, q ∈ R → z * q * z⁻¹ = q⁻¹) ∧
    z ∈ Subgroup.normalizer (R : Set G) ∧
    (∀ beta, beta ∈ Gamma → z • beta ∈ Gamma) ∧
    (∀ {beta gamma}, beta ∈ Gamma → gamma ∈ Gamma → beta ≠ gamma →
      ∀ x : G, x • beta = beta → x • gamma = gamma →
        ∀ delta, delta ∈ Gamma → x • delta = delta) ∧
    (∀ beta, beta ∈ Gamma → beta ≠ alpha →
      ∃ t : G, IsInvolution t ∧ t • alpha = beta ∧ t • beta = alpha)

private theorem lemma311_zpowers_pow_eq_top_of_isPGroup_generator
    {Q : Type*} [Group Q] [Finite Q] {r n : ℕ} [Fact r.Prime]
    (R : Subgroup Q) (hP : IsPGroup r R) (hcyc : IsCyclic R)
    (hnot : ¬ r ∣ n) (x : R) (hx : ∀ y : R, y ∈ Subgroup.zpowers x) :
    Subgroup.zpowers (x ^ n) = (⊤ : Subgroup R) := by
  letI : IsCyclic R := hcyc
  let e : R ≃ R := hP.powEquiv' hnot
  obtain ⟨u, hu⟩ := e.surjective x
  have hun : u ^ n = x := by
    simpa [e, IsPGroup.powEquiv_apply] using hu
  rcases Subgroup.mem_zpowers_iff.mp (hx u) with ⟨m, hm⟩
  have hxPow : x ∈ Subgroup.zpowers (x ^ n) := by
    refine ⟨m, ?_⟩
    calc
      (x ^ n) ^ m = x ^ ((n : ℤ) * m) := by
        rw [← zpow_natCast x n]
        exact (zpow_mul x (n : ℤ) m).symm
      _ = x ^ (m * (n : ℤ)) := by rw [mul_comm]
      _ = (x ^ m) ^ n := by
        rw [← zpow_natCast (x ^ m) n]
        exact zpow_mul x m (n : ℤ)
      _ = u ^ n := by rw [hm]
      _ = x := hun
  rw [eq_top_iff]
  intro y _hy
  rcases Subgroup.mem_zpowers_iff.mp (hx y) with ⟨m, rfl⟩
  exact (Subgroup.zpowers (x ^ n)).zpow_mem hxPow m

private theorem lemma311_faithfulSMul_quotient_pointStabilizerCore
    {G Omega : Type*} [Group G] [MulAction G Omega]
    [hN : (pointStabilizerCore G Omega).Normal]
    (quotientAction : MulAction (G ⧸ pointStabilizerCore G Omega) Omega)
    (hsmul : ∀ (g : G) (w : Omega),
      @SMul.smul (G ⧸ pointStabilizerCore G Omega) Omega
        quotientAction.toSMul (QuotientGroup.mk g) w = g • w) :
    @FaithfulSMul (G ⧸ pointStabilizerCore G Omega) Omega
      quotientAction.toSMul := by
  letI : MulAction (G ⧸ pointStabilizerCore G Omega) Omega := quotientAction
  refine { eq_of_smul_eq_smul := ?_ }
  intro a b hab
  obtain ⟨g, rfl⟩ :=
    QuotientGroup.mk'_surjective (pointStabilizerCore G Omega) a
  obtain ⟨h, rfl⟩ :=
    QuotientGroup.mk'_surjective (pointStabilizerCore G Omega) b
  apply QuotientGroup.eq_iff_div_mem.mpr
  change g / h ∈ pointStabilizerCore G Omega
  simp only [pointStabilizerCore, Subgroup.mem_iInf,
    MulAction.mem_stabilizer_iff]
  intro w
  calc
    (g / h) • w = g • (h⁻¹ • w) := by simp [div_eq_mul_inv, mul_smul]
    _ = (QuotientGroup.mk g : G ⧸ pointStabilizerCore G Omega) •
        (h⁻¹ • w) := by exact (hsmul g (h⁻¹ • w)).symm
    _ = (QuotientGroup.mk h : G ⧸ pointStabilizerCore G Omega) •
        (h⁻¹ • w) := hab (h⁻¹ • w)
    _ = h • (h⁻¹ • w) := hsmul h (h⁻¹ • w)
    _ = w := by simp

private theorem lemma311_maximal_output
    {G : Type u} {Omega : Type v} [Group G] [Finite G]
    [MulAction G Omega] [Finite Omega] [FaithfulSMul G Omega]
    [MulAction.IsPretransitive G Omega]
    (Y : Subgroup G) (z : G) (alpha : Omega)
    (hY : MulAction.stabilizer G alpha = Y)
    (hYproper : Y ≠ ⊤) (hmax : IsCoatom Y)
    (hzY : z ∈ Y) (hz : IsInvolution z)
    (hcent : Subgroup.centralizer ({z} : Set G) ≤ Y)
    (hfactor : pPrimeCore 2 G ⊔
      Subgroup.centralizer ({z} : Set G) = ⊤) :
    lemma311Output Y z alpha := by
  classical
  obtain ⟨F, r, hFnorm, hr, hFelem, hFne, hFodd, hFtrans,
      hFregular, hdis, hsup, hzinv⟩ :=
    lemma311_maximal_regular_core
      Y z alpha hY hYproper hmax hz hcent hfactor
  letI : Fact r.Prime := ⟨hr⟩
  letI : IsElementaryAbelian r F := hFelem
  obtain ⟨x, hxF, hxnotbot⟩ :=
    SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hFne)
  have hxne : x ≠ 1 := by
    intro hxone
    apply hxnotbot
    simpa [hxone]
  have hxpow : x ^ r = 1 := elemPow_eq_one_of_isElementaryAbelian x hxF
  have hxorder : orderOf x = r := orderOf_eq_prime hxpow hxne
  let R : Subgroup G := Subgroup.zpowers x
  have hRleF : R ≤ F := Subgroup.zpowers_le.mpr hxF
  have hRcard : Nat.card R = r := by
    simpa [R, Nat.card_zpowers] using hxorder
  have hRp : IsPGroup r R := by
    exact IsPGroup.of_card (n := 1) (by simpa [pow_one] using hRcard)
  have hRstab : MulAction.stabilizer R alpha = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    let qF : F := ⟨q, hRleF q.property⟩
    have hqFstab : qF ∈ MulAction.stabilizer F alpha := by
      change (qF : G) • alpha = alpha
      change (q : G) • alpha = alpha at hq
      simpa [qF] using hq
    rw [hFregular alpha] at hqFstab
    have hqFone : qF = (1 : F) := Subgroup.mem_bot.mp hqFstab
    apply Subgroup.mem_bot.mpr
    have hqG : (q : G) = 1 :=
      congrArg (fun a : F => (a : G)) hqFone
    exact Subtype.ext hqG
  let Gamma : Set Omega := MulAction.orbit R alpha
  have hGammaCard : Nat.card Gamma = r := by
    let f : R → Gamma := fun q => ⟨q • alpha, MulAction.mem_orbit _ _⟩
    have hf : Function.Bijective f := by
      constructor
      · intro q s hqs
        have hfix : (q⁻¹ * s : R) • alpha = alpha := by
          rw [mul_smul]
          have hqeq : q • alpha = s • alpha :=
            congrArg Subtype.val hqs
          rw [← hqeq]
          simp
        have hmem : (q⁻¹ * s : R) ∈ MulAction.stabilizer R alpha :=
          MulAction.mem_stabilizer_iff.mpr hfix
        rw [hRstab] at hmem
        exact eq_of_inv_mul_eq_one (Subgroup.mem_bot.mp hmem)
      · intro y
        rcases y.2 with ⟨q, hq⟩
        refine ⟨q, ?_⟩
        exact Subtype.ext hq
    have hcard := Nat.card_congr (Equiv.ofBijective f hf)
    simpa [Gamma, hRcard] using hcard.symm
  have hrOdd : Odd r := by
    have hxorderF : orderOf (⟨x, hxF⟩ : F) = r := by
      simpa using hxorder
    apply Odd.of_dvd_nat hFodd
    rw [← hxorderF]
    exact orderOf_dvd_natCard (⟨x, hxF⟩ : F)
  have hzAlpha : z • alpha = alpha := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [hY]
    exact hzY
  have hzinvR : ∀ q : G, q ∈ R → z * q * z⁻¹ ∈ R := by
    intro q hq
    rw [hzinv q (hRleF hq)]
    exact R.inv_mem hq
  have hzNormR : z ∈ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · exact hzinvR q
    · intro hq
      have hback := hzinvR (z * q * z⁻¹) hq
      have hz2 : z * z = 1 := by simpa [pow_two] using hz.sq_eq_one
      have heq : z * (z * q * z⁻¹) * z⁻¹ = q := by
        rw [hz.inv_eq_self]
        calc
          z * (z * q * z) * z = (z * z) * q * (z * z) := by group
          _ = q := by rw [hz2]; simp
      rw [heq] at hback
      exact hback
  have hzGamma : ∀ beta : Omega, beta ∈ Gamma → z • beta ∈ Gamma := by
    intro beta hbeta
    rcases MulAction.mem_orbit_iff.mp hbeta with ⟨q, hq⟩
    have hqG : (q : G) • alpha = beta := hq
    let q' : R := ⟨z * (q : G) * z⁻¹, hzinvR (q : G) q.property⟩
    refine MulAction.mem_orbit_iff.mpr ⟨q', ?_⟩
    calc
      (q' : G) • alpha =
          (z * (q : G) * z⁻¹) • alpha := rfl
      _ = z • ((q : G) • (z⁻¹ • alpha)) := by
        rw [mul_smul, mul_smul]
      _ = z • ((q : G) • alpha) := by
        rw [hz.inv_eq_self, hzAlpha]
      _ = z • beta := by rw [hqG]
  have hswap : ∀ beta : Omega, beta ∈ Gamma → beta ≠ alpha →
      ∃ t : G, IsInvolution t ∧ t • alpha = beta ∧ t • beta = alpha := by
    intro beta hbeta _hbetaNe
    rcases MulAction.mem_orbit_iff.mp hbeta with ⟨q, hq⟩
    have hqG : (q : G) • alpha = beta := hq
    let t : G := (q : G) * z
    have hqconj : z * (q : G) * z⁻¹ = (q : G)⁻¹ :=
      hzinv (q : G) (hRleF q.property)
    have hqconj' : z * (q : G) * z = (q : G)⁻¹ := by
      simpa [hz.inv_eq_self] using hqconj
    have hsq : t * t = 1 := by
      dsimp [t]
      calc
        (q : G) * z * ((q : G) * z) =
            (q : G) * (z * (q : G) * z) := by group
        _ = (q : G) * (q : G)⁻¹ := by rw [hqconj']
        _ = 1 := by simp
    have htne : t ≠ 1 := by
      intro htone
      have hzF : z ∈ F := by
        have hzEq : z = (q : G)⁻¹ := by
          calc
            z = (q : G)⁻¹ * ((q : G) * z) := by simp
            _ = (q : G)⁻¹ * t := by rfl
            _ = (q : G)⁻¹ := by rw [htone]; simp
        rw [hzEq]
        exact F.inv_mem (hRleF q.property)
      have hzFY : z ∈ F ⊓ Y := ⟨hzF, hzY⟩
      rw [disjoint_iff.mp hdis] at hzFY
      exact hz.ne_one (Subgroup.mem_bot.mp hzFY)
    have ht : IsInvolution t := ⟨htne, by simpa [pow_two] using hsq⟩
    refine ⟨t, ht, ?_, ?_⟩
    · calc
        t • alpha = (q : G) • (z • alpha) := by
          dsimp [t]
          rw [mul_smul]
        _ = (q : G) • alpha := by rw [hzAlpha]
        _ = beta := hqG
    · have hbetaQ : beta = (q : G) • alpha := hqG.symm
      have hsq' : ((q : G) * z * (q : G)) * z = 1 := by
        simpa [t, mul_assoc] using hsq
      have hqzq : (q : G) * z * (q : G) = z := by
        simpa [hz.inv_eq_self] using (mul_eq_one_iff_eq_inv.mp hsq')
      calc
        t • beta = ((q : G) * z) • ((q : G) • alpha) := by
          rw [hbetaQ]
        _ = (((q : G) * z) * (q : G)) • alpha := by
          rw [smul_smul]
        _ = ((q : G) * z * (q : G)) • alpha := by rfl
        _ = z • alpha := by rw [hqzq]
        _ = alpha := hzAlpha
  have hYC : Y = Subgroup.centralizer ({z} : Set G) :=
    lemma311_stabilizer_eq_centralizer
      F Y z alpha hFtrans hY hzY hz hcent hzinv
  have hRprime : Nat.Prime (Nat.card R) := by
    simpa [hRcard] using hr
  have hRodd : Odd (Nat.card R) := by
    simpa [hRcard] using hrOdd
  have hRcyclic : IsCyclic R := by
    dsimp [R]
    infer_instance
  refine ⟨R, Gamma, rfl,
    ⟨r, hr, hrOdd, hRp, hGammaCard⟩,
    hRcyclic, (fun q hq => hzinv q (hRleF hq)),
    hzNormR, hzGamma, ?_, hswap⟩
  intro beta gamma hbeta hgamma hne x hxbeta hxgamma delta hdelta
  exact lemma311_prime_orbit_pointwise
    F R Y z alpha hRprime hRodd hRleF hz hY hYC hzinv
    (by simpa [Gamma] using hbeta) (by simpa [Gamma] using hgamma) hne x
    hxbeta hxgamma delta (by simpa [Gamma] using hdelta)

/-- The exact nonmaximal-subgroup transfer in the source proof of Lemma 3.11.
The recursive package is taken for the action of `M` on its orbit of `alpha`;
the conclusion is transported back to the original action. -/
private theorem lemma311_nonmaximal_transfer
    {G : Type u} {Omega : Type v} [Group G] [Finite G]
    [MulAction G Omega] [Finite Omega]
    (Y M : Subgroup G) (z : G) (alpha : Omega)
    (hYM : Y ≤ M) (hzM : z ∈ M)
    (hY : MulAction.stabilizer G alpha = Y)
    (hrec :
      let OmegaM := MulAction.orbit M alpha
      let alphaM : OmegaM := ⟨alpha, MulAction.mem_orbit_self alpha⟩
      let zM : M := ⟨z, hzM⟩
      lemma311Output (Y.comap M.subtype) zM alphaM) :
    lemma311Output Y z alpha := by
  classical
  let OmegaM := MulAction.orbit M alpha
  let alphaM : OmegaM := ⟨alpha, MulAction.mem_orbit_self alpha⟩
  let zM : M := ⟨z, hzM⟩
  letI : MulAction M OmegaM := inferInstance
  have hrec' : lemma311Output
      (Y.comap M.subtype) zM alphaM := by
    simpa [OmegaM, alphaM, zM] using hrec
  rcases hrec' with
    ⟨Rm, GammaM, hGammaM, hPrimeM, hRcyclicM, hzinvM,
      hzNormM, hzGammaM, hPointM, hSwapM⟩
  obtain ⟨r, hrPrime, hrOdd, hrPGroup, hGammaMCard⟩ := hPrimeM
  let R : Subgroup G := Rm.map M.subtype
  let Gamma : Set Omega :=
    (fun w : OmegaM => (w : Omega)) '' GammaM
  have hGammaCard : Nat.card Gamma = Nat.card GammaM := by
    calc
      Nat.card Gamma = Gamma.ncard := Nat.card_coe_set_eq Gamma
      _ = GammaM.ncard := by
        exact Set.ncard_image_of_injective _ Subtype.val_injective
      _ = Nat.card GammaM := (Nat.card_coe_set_eq GammaM).symm
  have hGammaOrbit : Gamma = MulAction.orbit R alpha := by
    ext beta
    constructor
    · rintro ⟨betaM, hbetaM, rfl⟩
      rw [hGammaM] at hbetaM
      rcases MulAction.mem_orbit_iff.mp hbetaM with ⟨qM, hqM⟩
      let q : R := ⟨(qM : G), ⟨qM, qM.property, rfl⟩⟩
      refine MulAction.mem_orbit_iff.mpr ⟨q, ?_⟩
      have hqM' : (qM : G) • alpha = (betaM : Omega) := by
        exact congrArg Subtype.val hqM
      exact hqM'
    · intro hbeta
      rcases MulAction.mem_orbit_iff.mp hbeta with ⟨q, hq⟩
      rcases Subgroup.mem_map.mp q.property with ⟨qM, hqM, hqEq⟩
      have hqEqG : (q : G) = (qM : G) := by simpa using hqEq.symm
      have hqMG : (qM : G) • alpha = beta := by
        have hqG : (q : G) • alpha = beta := hq
        rw [hqEqG] at hqG
        exact hqG
      have hbetaOrbitM : beta ∈ MulAction.orbit M alpha := by
        rw [MulAction.mem_orbit_iff]
        refine ⟨qM, ?_⟩
        exact hqMG
      let betaM : OmegaM := ⟨beta, hbetaOrbitM⟩
      have hbetaM : betaM ∈ GammaM := by
        rw [hGammaM]
        let qRm : Rm := ⟨qM, hqM⟩
        exact MulAction.mem_orbit_iff.mpr ⟨qRm, by
          apply Subtype.ext
          exact hqMG⟩
      exact ⟨betaM, hbetaM, rfl⟩
  have hRcard : Nat.card R = Nat.card Rm := by
    simpa [R] using
      (Subgroup.card_map_of_injective (K := Rm) M.subtype_injective)
  have hPGroup : IsPGroup r R := by
    simpa [R] using hrPGroup.map M.subtype
  have hRcyclic : IsCyclic R := by
    exact (MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective Rm M.subtype M.subtype_injective)).mp hRcyclicM
  have hzinv : ∀ q : G, q ∈ R → z * q * z⁻¹ = q⁻¹ := by
    intro q hq
    rcases Subgroup.mem_map.mp hq with ⟨qM, hqM, hqEq⟩
    have hqEqG : (qM : G) = q := by simpa using hqEq
    have hqInvM := hzinvM qM hqM
    exact hqEqG ▸ congrArg Subtype.val hqInvM
  have hzNorm : z ∈ Subgroup.normalizer (R : Set G) := by
    have hzMap : (z : G) ∈
        (Subgroup.normalizer (Rm : Set M)).map M.subtype :=
      Subgroup.mem_map_of_mem M.subtype hzNormM
    exact (Subgroup.le_normalizer_map (H := Rm) M.subtype) hzMap
  have hzGamma : ∀ beta : Omega, beta ∈ Gamma → z • beta ∈ Gamma := by
    intro beta hbeta
    rcases hbeta with ⟨betaM, hbetaM, rfl⟩
    have hzbetaM : zM • betaM ∈ GammaM := hzGammaM betaM hbetaM
    refine ⟨zM • betaM, hzbetaM, ?_⟩
    rfl
  have hPoint : ∀ {beta gamma}, beta ∈ Gamma → gamma ∈ Gamma →
      beta ≠ gamma → ∀ x : G, x • beta = beta → x • gamma = gamma →
        ∀ delta, delta ∈ Gamma → x • delta = delta := by
    intro beta gamma hbeta hgamma hne x hxbeta hxgamma delta hdelta
    rcases hbeta with ⟨betaM, hbetaM, rfl⟩
    rcases hgamma with ⟨gammaM, hgammaM', rfl⟩
    have hbetaOrbitM : (betaM : Omega) ∈ MulAction.orbit M alpha := betaM.property
    have hgammaOrbitM : (gammaM : Omega) ∈ MulAction.orbit M alpha := gammaM.property
    have hstabM : ∀ {eta : Omega}, eta ∈ MulAction.orbit M alpha →
        MulAction.stabilizer G eta ≤ M := by
      intro eta heta g hg
      rcases MulAction.mem_orbit_iff.mp heta with ⟨m, hm⟩
      have hmG : (m : G) • alpha = eta := hm
      have hmgFix : ((m : G)⁻¹ * g * (m : G)) • alpha = alpha := by
        calc
          ((m : G)⁻¹ * g * (m : G)) • alpha =
              (m : G)⁻¹ • (g • ((m : G) • alpha)) := by
                simp only [mul_smul]
          _ = (m : G)⁻¹ • (g • eta) := by rw [hmG]
          _ = (m : G)⁻¹ • eta := by rw [MulAction.mem_stabilizer_iff.mp hg]
          _ = alpha := by rw [← hmG]; simp
      have hmgY : (m : G)⁻¹ * g * (m : G) ∈ Y := by
        rw [← hY]
        exact MulAction.mem_stabilizer_iff.mpr hmgFix
      have hmgM : (m : G)⁻¹ * g * (m : G) ∈ M := hYM hmgY
      have hgM : g ∈ M := by
        have hprod : (m : G) * ((m : G)⁻¹ * g * (m : G)) * (m : G)⁻¹ ∈ M := by
          exact M.mul_mem (M.mul_mem (show (m : G) ∈ M from m.property) hmgM)
            (M.inv_mem m.property)
        have heq : (m : G) * ((m : G)⁻¹ * g * (m : G)) * (m : G)⁻¹ = g := by
          group
        rw [heq] at hprod
        exact hprod
      exact hgM
    have hxBetaM : x ∈ MulAction.stabilizer G (betaM : Omega) :=
      MulAction.mem_stabilizer_iff.mpr hxbeta
    have hxM : x ∈ M := hstabM betaM.property hxBetaM
    let xM : M := ⟨x, hxM⟩
    have hxbetaM : xM • betaM = betaM := by
      apply Subtype.ext
      exact hxbeta
    have hxgammaM : xM • gammaM = gammaM := by
      apply Subtype.ext
      exact hxgamma
    have hneM : betaM ≠ gammaM := by
      intro heq
      apply hne
      exact congrArg Subtype.val heq
    rcases hdelta with ⟨deltaM, hdeltaM, rfl⟩
    have hdeltaMfix := hPointM hbetaM hgammaM' hneM xM
      hxbetaM hxgammaM deltaM hdeltaM
    exact congrArg Subtype.val hdeltaMfix
  have hSwap : ∀ beta : Omega, beta ∈ Gamma → beta ≠ alpha →
      ∃ t : G, IsInvolution t ∧ t • alpha = beta ∧ t • beta = alpha := by
    intro beta hbeta hbetaNe
    rcases hbeta with ⟨betaM, hbetaM, rfl⟩
    have hbetaNeM : betaM ≠ alphaM := by
      intro heq
      apply hbetaNe
      exact congrArg Subtype.val heq
    obtain ⟨tM, htM, htalphaM, htbetaM⟩ := hSwapM betaM hbetaM hbetaNeM
    refine ⟨(tM : G), ?_, ?_, ?_⟩
    · exact ⟨fun htOne => htM.ne_one (Subtype.ext htOne), by
        simpa using congrArg Subtype.val htM.sq_eq_one⟩
    · exact congrArg Subtype.val htalphaM
    · exact congrArg Subtype.val htbetaM
  have hGammaCard' : Nat.card Gamma = r := by
    rw [hGammaCard]
    exact hGammaMCard
  refine ⟨R, Gamma, hGammaOrbit,
    ⟨r, hrPrime, hrOdd, ?_, hGammaCard'⟩,
    hRcyclic, hzinv, hzNorm, hzGamma, hPoint, hSwap⟩
  exact hPGroup

/-- The operational `Z*` factorization passes to a subgroup containing the
ambient involution centralizer.  This is the inheritance used in the
nonmaximal branch of Lemma 3.11. -/
private theorem lemma311_factorization_subgroup
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) {z : G} (hzM : z ∈ M)
    (hcentM : Subgroup.centralizer ({z} : Set G) ≤ M)
    (hfactor : pPrimeCore 2 G ⊔
      Subgroup.centralizer ({z} : Set G) = ⊤) :
    let zM : M := ⟨z, hzM⟩
    pPrimeCore 2 M ⊔ Subgroup.centralizer ({zM} : Set M) = ⊤ := by
  classical
  let zM : M := ⟨z, hzM⟩
  let O : Subgroup G := pPrimeCore 2 G
  let OM : Subgroup M := O.comap M.subtype
  have hOnormal : O.Normal := by
    dsimp [O]
    exact pPrimeCore_normal
  letI : O.Normal := hOnormal
  have hOMnormal : OM.Normal := by infer_instance
  letI : OM.Normal := hOMnormal
  have hOMmapLe : OM.map M.subtype ≤ O := by
    rw [Subgroup.map_le_iff_le_comap]
  have hOMcard : Nat.card OM ∣ Nat.card O := by
    calc
      Nat.card OM = Nat.card (OM.map M.subtype) := by
        symm
        exact Subgroup.card_map_of_injective M.subtype_injective
      _ ∣ Nat.card O := Subgroup.card_dvd_of_le hOMmapLe
  have hOcop : Nat.Coprime 2 (Nat.card O) := by
    simpa [O] using pPrimeCore_coprime_card (p := 2) (G := G)
  have hOMcop : Nat.Coprime 2 (Nat.card OM) :=
    Nat.Coprime.of_dvd_right hOMcard hOcop
  have hOMle : OM ≤ pPrimeCore 2 M := le_sSup ⟨hOMnormal, hOMcop⟩
  apply top_unique
  intro m _hm
  have hmSup : (m : G) ∈ O ⊔ Subgroup.centralizer ({z} : Set G) := by
    rw [hfactor]
    trivial
  rcases Subgroup.mem_sup_of_normal_left.mp hmSup with ⟨o, hoO, c, hcC, hoc⟩
  have hcM : c ∈ M := hcentM hcC
  have hoM : o ∈ M := by
    have : (m : G) * c⁻¹ ∈ M := M.mul_mem m.property (M.inv_mem hcM)
    rwa [← hoc, mul_inv_cancel_right] at this
  let oM : M := ⟨o, hoM⟩
  let cM : M := ⟨c, hcM⟩
  have hoOM : oM ∈ OM := hoO
  have hoCore : oM ∈ pPrimeCore 2 M := hOMle hoOM
  have hcCM : cM ∈ Subgroup.centralizer ({zM} : Set M) := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp hcC
  have hprod := Subgroup.mul_mem_sup hoCore hcCM
  have hprodEq : oM * cM = m := by
    apply Subtype.ext
    exact hoc
  rwa [hprodEq] at hprod

private theorem lemma311_odd_subgroup_eq_commutator_mul_centralizer
    {X : Type u} [Group X] [Finite X]
    (R A : Subgroup X)
    (hA_norm_R : A ≤ Subgroup.normalizer (R : Set X))
    (hAcard : Nat.card A = 2) (hRodd : Odd (Nat.card R)) :
    (R : Set X) =
      (⁅R, A⁆ : Subgroup X) *
        ((R ⊓ Subgroup.centralizer (A : Set X) : Subgroup X) : Set X) := by
  letI : Subgroup.Normalizes A R := ⟨hA_norm_R⟩
  let Cfix : Subgroup R := fixedPointSubgroup A R
  let Ccomm : Subgroup R := commutatorAction (A := A) (G := R)
  have hcop : Nat.Coprime (Nat.card A) (Nat.card R) := by
    rw [hAcard]
    exact hRodd.coprime_two_left
  have hsup : Cfix ⊔ Ccomm = ⊤ :=
    fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
      (odd_order_theorem R hRodd) hcop
  have hcommMap : Ccomm.map R.subtype = ⁅R, A⁆ :=
    commutatorAction_subgroup_conj_map_eq_commutator R A hA_norm_R
  have hfixEq : Cfix =
      ((R ⊓ Subgroup.centralizer (A : Set X)).subgroupOf R) := by
    simpa [subgroupCentralizerIn] using
      fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn
        R A hA_norm_R
  haveI : Ccomm.Normal :=
    (commutatorAction_normal_and_invariant (A := A) (G := R)).1
  apply Set.Subset.antisymm
  · intro x hxR
    let xR : R := ⟨x, hxR⟩
    have hxTop : xR ∈ Ccomm ⊔ Cfix := by
      rw [sup_comm, hsup]
      exact Subgroup.mem_top xR
    rcases Subgroup.mem_sup_of_normal_left.mp hxTop with
      ⟨k, hk, c, hc, hkc⟩
    rw [Set.mem_mul]
    refine ⟨(k : X), ?_, (c : X), ?_, ?_⟩
    · rw [← hcommMap]
      exact ⟨k, hk, rfl⟩
    · rw [hfixEq] at hc
      exact hc
    · exact congrArg Subtype.val hkc
  · intro x hx
    rw [Set.mem_mul] at hx
    rcases hx with ⟨k, hk, c, hc, rfl⟩
    have hkR : k ∈ R := by
      rw [← hcommMap] at hk
      exact Subgroup.map_subtype_le Ccomm hk
    exact R.mul_mem hkR hc.1

private theorem lemma311_z_not_mem_pointStabilizerCore
    {G : Type u} {Omega : Type v} [Group G] [Finite G]
    [MulAction G Omega] [Finite Omega]
    (Y : Subgroup G) (z : G)
    (hYproper : Y ≠ ⊤) (hz : IsInvolution z)
    (hcoreY : pointStabilizerCore G Omega ≤ Y)
    (hcent : Subgroup.centralizer ({z} : Set G) ≤ Y)
    (hfactor : pPrimeCore 2 G ⊔
      Subgroup.centralizer ({z} : Set G) = ⊤) :
    z ∉ pointStabilizerCore G Omega := by
  intro hzCore
  let N : Subgroup G := pointStabilizerCore G Omega
  let O : Subgroup G := pPrimeCore 2 G
  let A : Subgroup G := Subgroup.zpowers z
  have hNnormal : N.Normal := by
    dsimp [N]
    exact proposition_4_c_pointStabilizerCore_normal
  letI : N.Normal := hNnormal
  have hOnormal : O.Normal := by
    dsimp [O]
    exact pPrimeCore_normal
  letI : O.Normal := hOnormal
  have hAcard : Nat.card A = 2 := by
    have hzOrder : orderOf z = 2 :=
      orderOf_eq_prime hz.sq_eq_one hz.ne_one
    simpa [A, Nat.card_zpowers] using hzOrder
  have hOodd : Odd (Nat.card O) := by
    dsimp [O]
    exact Nat.coprime_two_left.mp
      (by simpa using pPrimeCore_coprime_card (p := 2) (G := G))
  have hAnormO : A ≤ Subgroup.normalizer (O : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hOnormal]
    exact le_top
  have hdecomp := lemma311_odd_subgroup_eq_commutator_mul_centralizer
    O A hAnormO hAcard hOodd
  have hAleN : A ≤ N := by
    rw [Subgroup.zpowers_le]
    exact hzCore
  have hcommLeN : ⁅O, A⁆ ≤ N :=
    (Subgroup.commutator_mono le_rfl hAleN).trans
      (Subgroup.commutator_le_right O N)
  have hfixLeY : O ⊓ Subgroup.centralizer (A : Set G) ≤ Y := by
    intro c hc
    apply hcent
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hcA := Subgroup.mem_centralizer_iff.mp hc.2 z
      (Subgroup.mem_zpowers z)
    exact hcA.symm
  have hOleY : O ≤ Y := by
    intro o ho
    have hoSet : o ∈ (O : Set G) := ho
    rw [hdecomp] at hoSet
    rcases hoSet with ⟨k, hk, c, hc, rfl⟩
    exact Y.mul_mem (hcoreY (hcommLeN hk)) (hfixLeY hc)
  have htopLeY : (⊤ : Subgroup G) ≤ Y := by
    rw [← hfactor]
    exact sup_le hOleY hcent
  exact hYproper (top_unique htopLeY)

/-- Lift the cyclic, elementwise-inverted rotation package through an arbitrary
normal quotient whose action on `Omega` is induced from the ambient action. -/
private theorem lemma311_lift_quotient_output
    {G : Type u} {Omega : Type v} [Group G] [Finite G]
    [MulAction G Omega] [Finite Omega]
    (N : Subgroup G) [N.Normal]
    (Y : Subgroup G) (z : G) (alpha : Omega)
    (hz : IsInvolution z) (hzAlpha : z • alpha = alpha)
    (quotientAction : MulAction (G ⧸ N) Omega)
    (hsmul : ∀ (g : G) (w : Omega),
      @SMul.smul (G ⧸ N) Omega quotientAction.toSMul
        (QuotientGroup.mk g) w = g • w)
    (hrec :
      let q : G →* G ⧸ N := QuotientGroup.mk' N
      letI : MulAction (G ⧸ N) Omega := quotientAction
      lemma311Output (Y.map q) (q z) alpha) :
    lemma311Output Y z alpha := by
  classical
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  letI : MulAction (G ⧸ N) Omega := quotientAction
  have hrec' : lemma311Output (Y.map q) (q z) alpha := by
    simpa [q] using hrec
  rcases hrec' with
    ⟨Rbar, Gamma, hGammaBar, hPrimeBar, hRbarCyclic, hzinvBar,
      hzNormBar, hzGammaBar, hPointBar, _hSwapBar⟩
  obtain ⟨r, hrPrime, hrOdd, hRbarP, hGammaCard⟩ := hPrimeBar
  letI : Fact r.Prime := ⟨hrPrime⟩
  letI : IsCyclic Rbar := hRbarCyclic
  obtain ⟨xbar, hxbarGen⟩ := IsCyclic.exists_generator (α := Rbar)
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N (xbar : G ⧸ N)
  let c : G := z * g * z⁻¹ * g⁻¹
  have hcinv : z * c * z⁻¹ = c⁻¹ := by
    have hz2 : z * z = 1 := by simpa [pow_two] using hz.sq_eq_one
    dsimp [c]
    calc
      z * (z * g * z⁻¹ * g⁻¹) * z⁻¹ =
          (z * z) * g * z⁻¹ * g⁻¹ * z⁻¹ := by group
      _ = g * z⁻¹ * g⁻¹ * z⁻¹ := by rw [hz2]; simp
      _ = (z * g * z⁻¹ * g⁻¹)⁻¹ := by
        simp [hz.inv_eq_self, mul_assoc]
  have hqc : q c = ((xbar⁻¹ ^ (2 : ℕ) : Rbar) : G ⧸ N) := by
    have hxInv := hzinvBar (xbar : G ⧸ N) xbar.property
    dsimp [c]
    simp only [map_mul, map_inv]
    rw [hg]
    rw [hxInv]
    simp [pow_two]
  have hrNotDvdTwo : ¬ r ∣ 2 :=
    hrPrime.coprime_iff_not_dvd.mp hrOdd.coprime_two_right
  have hxbarInvGen : ∀ y : Rbar, y ∈ Subgroup.zpowers xbar⁻¹ := by
    intro y
    rw [Subgroup.zpowers_inv]
    exact hxbarGen y
  have hqcGenSub :
      Subgroup.zpowers (xbar⁻¹ ^ (2 : ℕ)) = (⊤ : Subgroup Rbar) :=
    lemma311_zpowers_pow_eq_top_of_isPGroup_generator
      Rbar hRbarP hRbarCyclic hrNotDvdTwo xbar⁻¹ hxbarInvGen
  have hqcGen : Subgroup.zpowers (q c) = Rbar := by
    calc
      Subgroup.zpowers (q c) =
          Subgroup.zpowers (((xbar⁻¹ ^ (2 : ℕ) : Rbar) : G ⧸ N)) := by rw [hqc]
      _ = (Subgroup.zpowers (xbar⁻¹ ^ (2 : ℕ))).map Rbar.subtype := by
        exact (MonoidHom.map_zpowers Rbar.subtype
          (xbar⁻¹ ^ (2 : ℕ))).symm
      _ = (⊤ : Subgroup Rbar).map Rbar.subtype := by rw [hqcGenSub]
      _ = Rbar := by
        rw [← MonoidHom.range_eq_map]
        exact Subgroup.range_subtype Rbar
  let C : Subgroup G := Subgroup.zpowers c
  have hCcyclic : IsCyclic C := by
    dsimp [C]
    infer_instance
  let P : Sylow r C := Sylow.nonempty.some
  let R : Subgroup G := (P : Subgroup C).map C.subtype
  have hRmap : R.map q = Rbar := by
    let qcR : Rbar := xbar⁻¹ ^ (2 : ℕ)
    have hqcR : (qcR : G ⧸ N) = q c := by
      simpa [qcR] using hqc.symm
    have hPindexNot : ¬ r ∣ (P : Subgroup C).index := P.not_dvd_index
    have hqcPowGenSub :
        Subgroup.zpowers (qcR ^ (P : Subgroup C).index) = (⊤ : Subgroup Rbar) :=
      lemma311_zpowers_pow_eq_top_of_isPGroup_generator
        Rbar hRbarP hRbarCyclic hPindexNot qcR (by
          intro y
          have hyTop : y ∈ (⊤ : Subgroup Rbar) := trivial
          rw [← hqcGenSub] at hyTop
          simpa [qcR] using hyTop)
    have hqcPowGen :
        Subgroup.zpowers ((qcR ^ (P : Subgroup C).index : Rbar) : G ⧸ N) = Rbar := by
      calc
        Subgroup.zpowers ((qcR ^ (P : Subgroup C).index : Rbar) : G ⧸ N) =
            (Subgroup.zpowers (qcR ^ (P : Subgroup C).index)).map Rbar.subtype := by
          exact (MonoidHom.map_zpowers Rbar.subtype
            (qcR ^ (P : Subgroup C).index)).symm
        _ = (⊤ : Subgroup Rbar).map Rbar.subtype := by rw [hqcPowGenSub]
        _ = Rbar := by
          rw [← MonoidHom.range_eq_map]
          exact Subgroup.range_subtype Rbar
    let fC : C →* G ⧸ N := q.comp C.subtype
    have hCmap : (⊤ : Subgroup C).map fC = Rbar := by
      calc
        (⊤ : Subgroup C).map fC =
            ((⊤ : Subgroup C).map C.subtype).map q := by
          rw [Subgroup.map_map]
        _ = C.map q := by
          rw [← MonoidHom.range_eq_map]
          rw [Subgroup.range_subtype]
        _ = Subgroup.zpowers (q c) := by
          dsimp [C]
          exact MonoidHom.map_zpowers q c
        _ = Rbar := hqcGen
    have hPmapLe : (P : Subgroup C).map fC ≤ Rbar := by
      rw [← hCmap]
      exact Subgroup.map_mono le_top
    let cC : C := ⟨c, Subgroup.mem_zpowers c⟩
    have hcPow : cC ^ (P : Subgroup C).index ∈ (P : Subgroup C) := by
      exact (P : Subgroup C).pow_index_mem cC
    have hgenMem :
        ((qcR ^ (P : Subgroup C).index : Rbar) : G ⧸ N) ∈
          (P : Subgroup C).map fC := by
      refine ⟨cC ^ (P : Subgroup C).index, hcPow, ?_⟩
      change q ((cC ^ (P : Subgroup C).index : C) : G) =
        ((qcR ^ (P : Subgroup C).index : Rbar) : G ⧸ N)
      calc
        q ((cC ^ (P : Subgroup C).index : C) : G) =
            (q c) ^ (P : Subgroup C).index := by simp [cC]
        _ = ((qcR : G ⧸ N) ^ (P : Subgroup C).index) := by rw [hqcR]
        _ = ((qcR ^ (P : Subgroup C).index : Rbar) : G ⧸ N) := rfl
    have hRbarLe : Rbar ≤ (P : Subgroup C).map fC := by
      rw [← hqcPowGen]
      exact Subgroup.zpowers_le.mpr hgenMem
    have hPmapEq : (P : Subgroup C).map fC = Rbar :=
      le_antisymm hPmapLe hRbarLe
    simpa [R, fC, Subgroup.map_map] using hPmapEq
  have hRp : IsPGroup r R := by
    dsimp [R]
    exact P.isPGroup'.map C.subtype
  have hPcyclic : IsCyclic (P : Subgroup C) := by
    letI : IsCyclic C := hCcyclic
    exact Subgroup.isCyclic_of_le le_top
  have hRcyclic : IsCyclic R := by
    exact (MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective (P : Subgroup C) C.subtype
        C.subtype_injective)).mp hPcyclic
  have hzinvC : ∀ y : G, y ∈ C → z * y * z⁻¹ = y⁻¹ := by
    intro y hy
    rcases Subgroup.mem_zpowers_iff.mp hy with ⟨k, rfl⟩
    calc
      z * c ^ k * z⁻¹ = (z * c * z⁻¹) ^ k := by
        exact (conj_zpow (a := z) (b := c) (i := k)).symm
      _ = (c⁻¹) ^ k := by rw [hcinv]
      _ = (c ^ k)⁻¹ := by simp
  have hzinv : ∀ y : G, y ∈ R → z * y * z⁻¹ = y⁻¹ := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨p, hp, hpEq⟩
    have hpEqG : (p : G) = y := by simpa using hpEq
    exact hpEqG ▸ hzinvC (p : G) p.property
  have hzNorm : z ∈ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hzinv y hy]
      exact R.inv_mem hy
    · intro hy
      have hback := hzinv (z * y * z⁻¹) hy
      have hz2 : z * z = 1 := by simpa [pow_two] using hz.sq_eq_one
      have heq : z * (z * y * z⁻¹) * z⁻¹ = y := by
        rw [hz.inv_eq_self]
        calc
          z * (z * y * z) * z = (z * z) * y * (z * z) := by group
          _ = y := by rw [hz2]; simp
      rw [heq] at hback
      rw [hback]
      exact R.inv_mem hy
  have hOrbit : MulAction.orbit R alpha = MulAction.orbit Rbar alpha := by
    ext beta
    constructor
    · intro hbeta
      rcases MulAction.mem_orbit_iff.mp hbeta with ⟨a, ha⟩
      have hqa : q (a : G) ∈ Rbar := by
        rw [← hRmap]
        exact Subgroup.mem_map_of_mem q a.property
      let abar : Rbar := ⟨q (a : G), hqa⟩
      refine MulAction.mem_orbit_iff.mpr ⟨abar, ?_⟩
      change @SMul.smul (G ⧸ N) Omega quotientAction.toSMul
        (abar : G ⧸ N) alpha = beta
      change (a : G) • alpha = beta at ha
      simpa [abar, q] using (hsmul (a : G) alpha).trans ha
    · intro hbeta
      rcases MulAction.mem_orbit_iff.mp hbeta with ⟨abar, ha⟩
      have habarMap : (abar : G ⧸ N) ∈ R.map q := by
        rw [hRmap]
        exact abar.property
      rcases Subgroup.mem_map.mp habarMap with ⟨a, haR, haEq⟩
      let aR : R := ⟨a, haR⟩
      refine MulAction.mem_orbit_iff.mpr ⟨aR, ?_⟩
      change a • alpha = beta
      change (abar : G ⧸ N) • alpha = beta at ha
      rw [← haEq] at ha
      exact (hsmul a alpha).symm.trans ha
  have hGamma : Gamma = MulAction.orbit R alpha := by
    rw [hGammaBar, hOrbit]
  have hzGamma : ∀ beta : Omega, beta ∈ Gamma → z • beta ∈ Gamma := by
    intro beta hbeta
    have hbetaBar := hzGammaBar beta hbeta
    have hzsmul :
        @SMul.smul (G ⧸ N) Omega quotientAction.toSMul (q z) beta = z • beta := by
      simpa [q] using hsmul z beta
    change @SMul.smul (G ⧸ N) Omega quotientAction.toSMul (q z) beta ∈ Gamma at hbetaBar
    exact hzsmul ▸ hbetaBar
  have hPoint : ∀ {beta gamma}, beta ∈ Gamma → gamma ∈ Gamma →
      beta ≠ gamma → ∀ x : G, x • beta = beta → x • gamma = gamma →
        ∀ delta, delta ∈ Gamma → x • delta = delta := by
    intro beta gamma hbeta hgamma hne x hxbeta hxgamma delta hdelta
    have hxbetaBar : q x • beta = beta := (hsmul x beta).trans hxbeta
    have hxgammaBar : q x • gamma = gamma := (hsmul x gamma).trans hxgamma
    have hdeltaBar := hPointBar hbeta hgamma hne (q x)
      hxbetaBar hxgammaBar delta hdelta
    exact (hsmul x delta).symm.trans hdeltaBar
  have hSwap : ∀ beta : Omega, beta ∈ Gamma → beta ≠ alpha →
      ∃ t : G, IsInvolution t ∧ t • alpha = beta ∧ t • beta = alpha := by
    intro beta hbeta hbetaNe
    rw [hGamma] at hbeta
    rcases MulAction.mem_orbit_iff.mp hbeta with ⟨a, ha⟩
    let t : G := (a : G) * z
    have hainv := hzinv (a : G) a.property
    have hsq : t * t = 1 := by
      dsimp [t]
      have hainv' : z * (a : G) * z = (a : G)⁻¹ := by
        simpa [hz.inv_eq_self] using hainv
      calc
        (a : G) * z * ((a : G) * z) =
            (a : G) * (z * (a : G) * z) := by group
        _ = (a : G) * (a : G)⁻¹ := by rw [hainv']
        _ = 1 := by simp
    have htAlpha : t • alpha = beta := by
      calc
        t • alpha = (a : G) • (z • alpha) := by
          dsimp [t]
          rw [mul_smul]
        _ = (a : G) • alpha := by rw [hzAlpha]
        _ = beta := ha
    have htne : t ≠ 1 := by
      intro htone
      apply hbetaNe
      rw [← htAlpha, htone, one_smul]
    have ht : IsInvolution t :=
      ⟨htne, by simpa [pow_two] using hsq⟩
    refine ⟨t, ht, htAlpha, ?_⟩
    calc
      t • beta = t • (t • alpha) := by rw [htAlpha]
      _ = (t * t) • alpha := (mul_smul t t alpha).symm
      _ = alpha := by rw [hsq, one_smul]
  refine ⟨R, Gamma, hGamma,
    ⟨r, hrPrime, hrOdd, hRp, hGammaCard⟩,
    hRcyclic, hzinv, hzNorm, hzGamma, hPoint, hSwap⟩

private theorem lemma311_quotient_centralizer_le_map
    {G : Type u} {Omega : Type v} [Group G] [Finite G]
    [MulAction G Omega] [Finite Omega]
    (Y : Subgroup G) (z : G)
    (hz : IsInvolution z)
    (hcent : Subgroup.centralizer ({z} : Set G) ≤ Y)
    (hfactor : pPrimeCore 2 G ⊔
      Subgroup.centralizer ({z} : Set G) = ⊤) :
    let N : Subgroup G := pointStabilizerCore G Omega
    let _ : N.Normal := proposition_4_c_pointStabilizerCore_normal
    let q : G →* G ⧸ N := QuotientGroup.mk' N
    Subgroup.centralizer ({q z} : Set (G ⧸ N)) ≤ Y.map q := by
  classical
  dsimp only
  let N : Subgroup G := pointStabilizerCore G Omega
  let O : Subgroup G := pPrimeCore 2 G
  let A : Subgroup G := Subgroup.zpowers z
  let L : Subgroup O := N.comap O.subtype
  have hNnormal : N.Normal := by
    dsimp [N]
    exact proposition_4_c_pointStabilizerCore_normal
  letI : N.Normal := hNnormal
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hOnormal : O.Normal := by
    dsimp [O]
    exact pPrimeCore_normal
  letI : O.Normal := hOnormal
  have hLnormal : L.Normal := by infer_instance
  letI : L.Normal := hLnormal
  have hAnormO : A ≤ Subgroup.normalizer (O : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hOnormal]
    exact le_top
  letI : Subgroup.Normalizes A O := ⟨hAnormO⟩
  have hLinv : IsInvariant A O L := by
    refine ⟨?_⟩
    intro a x
    constructor
    · intro hx
      change (a : G) * (x : G) * (a : G)⁻¹ ∈ N
      exact hNnormal.conj_mem (x : G) hx (a : G)
    · intro hx
      change (a : G) * (x : G) * (a : G)⁻¹ ∈ N at hx
      have hback := hNnormal.conj_mem
        ((a : G) * (x : G) * (a : G)⁻¹) hx (a : G)⁻¹
      apply Subgroup.mem_subgroupOf.mpr
      simpa [mul_assoc] using hback
  have hOodd : Odd (Nat.card O) := by
    dsimp [O]
    exact Nat.coprime_two_left.mp
      (by simpa using pPrimeCore_coprime_card (p := 2) (G := G))
  have hAcard : Nat.card A = 2 := by
    have hzOrder : orderOf z = 2 :=
      orderOf_eq_prime hz.sq_eq_one hz.ne_one
    simpa [A, Nat.card_zpowers] using hzOrder
  have hcop : Nat.Coprime (Nat.card A) (Nat.card O) := by
    rw [hAcard]
    exact hOodd.coprime_two_left
  have hfixQ :
      letI : MulDistribMulAction A (O ⧸ L) :=
        quotientMulDistribMulAction (A := A) (G := O) L hLinv
      fixedPointSubgroup A (O ⧸ L) =
        (fixedPointSubgroup A O).map (QuotientGroup.mk' L) := by
    exact fixedPointSubgroup_quotient_eq_map_of_solvable_coprime_action
      (G := O) (A := A) (odd_order_theorem O hOodd) hcop
      (∅ : Set Nat.Primes) L hLinv
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
  have hgSup : g ∈ O ⊔ Subgroup.centralizer ({z} : Set G) := by
    rw [hfactor]
    exact Subgroup.mem_top g
  rcases Subgroup.mem_sup_of_normal_left.mp hgSup with
    ⟨o, hoO, c, hcC, hoc⟩
  have hxComm : q g * q z = q z * q g :=
    Subgroup.mem_centralizer_singleton_iff.mp hx
  have hcComm : q c * q z = q z * q c := by
    exact congrArg q (Subgroup.mem_centralizer_singleton_iff.mp hcC)
  have hoComm : q o * q z = q z * q o := by
    have hcancel : (q o * q z) * q c = (q z * q o) * q c := by
      calc
        (q o * q z) * q c = q o * (q z * q c) := by group
        _ = q o * (q c * q z) := by rw [hcComm]
        _ = q (o * c) * q z := by simp [mul_assoc]
        _ = q g * q z := by rw [hoc]
        _ = q z * q g := hxComm
        _ = q z * q (o * c) := by rw [hoc]
        _ = (q z * q o) * q c := by simp [mul_assoc]
    exact mul_right_cancel hcancel
  let oO : O := ⟨o, hoO⟩
  let az : A := ⟨z, Subgroup.mem_zpowers z⟩
  letI : MulDistribMulAction A (O ⧸ L) :=
    quotientMulDistribMulAction (A := A) (G := O) L hLinv
  let qL : O →* O ⧸ L := QuotientGroup.mk' L
  have hgenFixed : az • qL oO = qL oO := by
    change qL (az • oO) = qL oO
    apply QuotientGroup.eq_iff_div_mem.mpr
    change ((z * o * z⁻¹) / o : G) ∈ N
    rw [← QuotientGroup.eq_one_iff (N := N)]
    change q ((z * o * z⁻¹) / o) = 1
    simp only [map_div, map_mul, map_inv]
    rw [← hoComm]
    simp
  have hqLFixed : qL oO ∈ fixedPointSubgroup A (O ⧸ L) := by
    rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
    intro a
    have ha : a ∈ Subgroup.zpowers az := by
      rw [Subgroup.mem_zpowers_iff]
      have haG : (a : G) ∈ Subgroup.zpowers z := a.property
      rw [Subgroup.mem_zpowers_iff] at haG
      rcases haG with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      apply Subtype.ext
      exact hk
    exact smul_eq_self_of_mem_zpowers ha hgenFixed
  have hqLMap : qL oO ∈
      (fixedPointSubgroup A O).map qL := by
    rw [← hfixQ]
    exact hqLFixed
  rcases Subgroup.mem_map.mp hqLMap with ⟨dO, hdFix, hdEq⟩
  have hdGen : az • dO = dO := by
    rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hdFix
    exact hdFix az
  have hdConj : z * (dO : G) * z⁻¹ = (dO : G) := by
    exact congrArg Subtype.val hdGen
  have hdC : (dO : G) ∈ Subgroup.centralizer ({z} : Set G) := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hmul := congrArg (fun t : G => t * z) hdConj
    simpa [mul_assoc] using hmul.symm
  have hdoL : dO / oO ∈ L := by
    exact QuotientGroup.eq_iff_div_mem.mp hdEq
  have hdoN : (dO : G) / o ∈ N := by
    exact hdoL
  have hqdo : q (dO : G) = q o := by
    exact QuotientGroup.eq_iff_div_mem.mpr hdoN
  have hdcY : (dO : G) * c ∈ Y := by
    apply hcent
    exact (Subgroup.centralizer ({z} : Set G)).mul_mem hdC hcC
  apply Subgroup.mem_map.mpr
  refine ⟨(dO : G) * c, hdcY, ?_⟩
  calc
    q ((dO : G) * c) = q (dO : G) * q c := by simp
    _ = q o * q c := by rw [hqdo]
    _ = q (o * c) := by simp
    _ = q g := by rw [hoc]

/-- The sole remaining induction branch: quotient a nonfaithful transitive
action by its pointwise kernel and lift the resulting Lemma 3.11 package. -/
private theorem lemma311_nonfaithful_quotient
    {G : Type u} {Omega : Type v} [Group G] [Finite G]
    [MulAction G Omega] [Finite Omega]
    [MulAction.IsPretransitive G Omega]
    (Y : Subgroup G) (z : G) (alpha : Omega)
    (hY : MulAction.stabilizer G alpha = Y)
    (hYproper : Y ≠ ⊤) (hmax : IsCoatom Y)
    (hzY : z ∈ Y) (hz : IsInvolution z)
    (hcent : Subgroup.centralizer ({z} : Set G) ≤ Y)
    (hfactor : pPrimeCore 2 G ⊔
      Subgroup.centralizer ({z} : Set G) = ⊤)
    (_hnotfaith : ¬ FaithfulSMul G Omega) :
    lemma311Output Y z alpha := by
  classical
  let N : Subgroup G := pointStabilizerCore G Omega
  have hNnormal : N.Normal := by
    dsimp [N]
    exact proposition_4_c_pointStabilizerCore_normal
  letI : N.Normal := hNnormal
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hNker : N ≤ (MulAction.toPermHom G Omega).ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    apply Equiv.ext
    intro w
    change n • w = w
    exact MulAction.mem_stabilizer_iff.mp
      ((le_pointStabilizerCore_iff.mp
        (show N ≤ pointStabilizerCore G Omega by rfl) w) hn)
  let quotientPermHom : G ⧸ N →* Equiv.Perm Omega :=
    QuotientGroup.lift N (MulAction.toPermHom G Omega) hNker
  let quotientAction : MulAction (G ⧸ N) Omega :=
    MulAction.compHom Omega quotientPermHom
  letI : MulAction (G ⧸ N) Omega := quotientAction
  have hsmul : ∀ (g : G) (w : Omega),
      @SMul.smul (G ⧸ N) Omega quotientAction.toSMul
        (QuotientGroup.mk g) w = g • w := by
    intro g w
    change quotientPermHom (QuotientGroup.mk g : G ⧸ N) w = g • w
    simp [quotientPermHom, MulAction.toPermHom_apply]
  have hfaithQ : FaithfulSMul (G ⧸ N) Omega := by
    exact lemma311_faithfulSMul_quotient_pointStabilizerCore
      quotientAction (fun g w => by
        change @SMul.smul (G ⧸ N) Omega quotientAction.toSMul
          (QuotientGroup.mk g) w = g • w
        simpa [N] using hsmul g w)
  letI : FaithfulSMul (G ⧸ N) Omega := hfaithQ
  have htransQ : MulAction.IsPretransitive (G ⧸ N) Omega := by
    constructor
    intro beta gamma
    obtain ⟨g, hg⟩ :=
      @MulAction.IsPretransitive.exists_smul_eq G Omega
        inferInstance inferInstance beta gamma
    exact ⟨q g, (hsmul g beta).trans hg⟩
  letI : MulAction.IsPretransitive (G ⧸ N) Omega := htransQ
  let Ybar : Subgroup (G ⧸ N) := Y.map q
  have hNY : N ≤ Y := by
    intro n hn
    rw [← hY]
    exact (le_pointStabilizerCore_iff.mp
      (show N ≤ pointStabilizerCore G Omega by rfl) alpha) hn
  have hkerY : q.ker ≤ Y := by
    rw [show q.ker = N by exact QuotientGroup.ker_mk' N]
    exact hNY
  have hYbarStab : MulAction.stabilizer (G ⧸ N) alpha = Ybar := by
    have hstabComap :
        (MulAction.stabilizer (G ⧸ N) alpha).comap q = Y := by
      ext g
      change @SMul.smul (G ⧸ N) Omega quotientAction.toSMul
          (QuotientGroup.mk g) alpha = alpha ↔ g ∈ Y
      rw [hsmul]
      rw [← hY, MulAction.mem_stabilizer_iff]
    apply Subgroup.comap_injective (QuotientGroup.mk'_surjective N)
    change (MulAction.stabilizer (G ⧸ N) alpha).comap q =
      (Y.map q).comap q
    rw [hstabComap, Subgroup.comap_map_eq_self hkerY]
  have hYbarCoatom : IsCoatom Ybar := by
    have hYbarProper : Ybar ≠ ⊤ := by
      intro htop
      apply hYproper
      change Y.map q = ⊤ at htop
      have hc := congrArg (Subgroup.comap q) htop
      rw [Subgroup.comap_map_eq_self hkerY] at hc
      simpa using hc
    refine ⟨hYbarProper, ?_⟩
    intro K hlt
    have hcomaplt : Y < K.comap q := by
      change Y.map q < K at hlt
      have hc :=
        (Subgroup.comap_lt_comap_of_surjective
          (QuotientGroup.mk'_surjective N)).2 hlt
      rwa [Subgroup.comap_map_eq_self hkerY] at hc
    have hKtop : K.comap q = ⊤ := hmax.2 (K.comap q) hcomaplt
    apply Subgroup.comap_injective (QuotientGroup.mk'_surjective N)
    simpa using hKtop
  have hYbarProper : Ybar ≠ ⊤ := hYbarCoatom.ne_top
  have hzAlpha : z • alpha = alpha := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [hY]
    exact hzY
  have hzbarY : q z ∈ Ybar := Subgroup.mem_map_of_mem q hzY
  have hzNotN : z ∉ N := by
    simpa [N] using lemma311_z_not_mem_pointStabilizerCore
      Y z hYproper hz hNY hcent hfactor
  have hzbarNe : q z ≠ 1 := by
    intro hzone
    exact hzNotN ((QuotientGroup.eq_one_iff (N := N) z).mp hzone)
  have hzbar : IsInvolution (q z) := by
    refine ⟨hzbarNe, ?_⟩
    simpa using congrArg q hz.sq_eq_one
  have hcentBar :
      Subgroup.centralizer ({q z} : Set (G ⧸ N)) ≤ Ybar := by
    simpa [N, q, Ybar] using
      lemma311_quotient_centralizer_le_map Y z hz hcent hfactor
  have hfactorBar : pPrimeCore 2 (G ⧸ N) ⊔
      Subgroup.centralizer ({q z} : Set (G ⧸ N)) = ⊤ := by
    let O : Subgroup G := pPrimeCore 2 G
    let Obar : Subgroup (G ⧸ N) := O.map q
    have hOnormal : O.Normal := by
      dsimp [O]
      exact pPrimeCore_normal
    letI : O.Normal := hOnormal
    have hObarNormal : Obar.Normal := by
      dsimp [Obar]
      exact Subgroup.Normal.map (inferInstance : O.Normal) q
        (QuotientGroup.mk'_surjective N)
    have hOodd : Odd (Nat.card O) := by
      dsimp [O]
      exact Nat.coprime_two_left.mp
        (by simpa using pPrimeCore_coprime_card (p := 2) (G := G))
    have hObarCard : Nat.card Obar ∣ Nat.card O := by
      exact O.card_map_dvd q
    have hObarOdd : Odd (Nat.card Obar) :=
      Odd.of_dvd_nat hOodd hObarCard
    have hObarCop : Nat.Coprime 2 (Nat.card Obar) :=
      hObarOdd.coprime_two_left
    have hObarLe : Obar ≤ pPrimeCore 2 (G ⧸ N) :=
      le_sSup ⟨hObarNormal, hObarCop⟩
    apply top_unique
    intro xbar _hxbar
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N xbar
    have hxSup : x ∈ O ⊔ Subgroup.centralizer ({z} : Set G) := by
      rw [show O ⊔ Subgroup.centralizer ({z} : Set G) = ⊤ by
        simpa [O] using hfactor]
      trivial
    rcases Subgroup.mem_sup_of_normal_left.mp hxSup with
      ⟨o, hoO, c, hcC, hoc⟩
    have hqo : q o ∈ pPrimeCore 2 (G ⧸ N) :=
      hObarLe (Subgroup.mem_map_of_mem q hoO)
    have hqc : q c ∈
        Subgroup.centralizer ({q z} : Set (G ⧸ N)) := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact congrArg q (Subgroup.mem_centralizer_singleton_iff.mp hcC)
    have hprod := Subgroup.mul_mem_sup hqo hqc
    have hqprod : q o * q c = q x := by
      rw [← map_mul, hoc]
    rwa [hqprod] at hprod
  have hrec : lemma311Output Ybar (q z) alpha :=
    lemma311_maximal_output Ybar (q z) alpha
      hYbarStab hYbarProper hYbarCoatom hzbarY hzbar hcentBar hfactorBar
  exact lemma311_lift_quotient_output N Y z alpha hz hzAlpha
    quotientAction hsmul (by simpa [q, Ybar] using hrec)

private theorem lemma311_output_core_aux :
    ∀ n : ℕ, ∀ {G : Type u} {Omega : Type v},
      [Group G] → [Finite G] → [MulAction G Omega] → [Finite Omega] →
      [MulAction.IsPretransitive G Omega] → Nat.card G = n →
      ∀ (Y : Subgroup G) (z : G) (alpha : Omega),
        MulAction.stabilizer G alpha = Y → Y ≠ ⊤ → z ∈ Y →
        IsInvolution z → Subgroup.centralizer ({z} : Set G) ≤ Y →
        pPrimeCore 2 G ⊔ Subgroup.centralizer ({z} : Set G) = ⊤ →
        lemma311Output Y z alpha := by
  intro n
  refine Nat.strongRecOn
    (motive := fun n =>
      ∀ {G : Type u} {Omega : Type v},
        [Group G] → [Finite G] → [MulAction G Omega] → [Finite Omega] →
        [MulAction.IsPretransitive G Omega] → Nat.card G = n →
        ∀ (Y : Subgroup G) (z : G) (alpha : Omega),
          MulAction.stabilizer G alpha = Y → Y ≠ ⊤ → z ∈ Y →
          IsInvolution z → Subgroup.centralizer ({z} : Set G) ≤ Y →
          pPrimeCore 2 G ⊔ Subgroup.centralizer ({z} : Set G) = ⊤ →
          lemma311Output Y z alpha)
    n (fun n ih => by
      intro G Omega _instGroup _instFinite _instAction _instFiniteOmega
        _instTrans hcard Y z alpha hY hYproper hzY hz hcent hfactor
      classical
      by_cases hmax : IsCoatom Y
      · by_cases hfaith : FaithfulSMul G Omega
        · letI : FaithfulSMul G Omega := hfaith
          exact lemma311_maximal_output
            Y z alpha hY hYproper hmax hzY hz hcent hfactor
        · exact lemma311_nonfaithful_quotient
            Y z alpha hY hYproper hmax hzY hz hcent hfactor hfaith
      · rw [IsCoatom] at hmax
        push_neg at hmax
        obtain ⟨M, hYltM, hMne⟩ := hmax hYproper
        have hMlt : M < (⊤ : Subgroup G) := lt_top_iff_ne_top.mpr hMne
        let OmegaM := MulAction.orbit M alpha
        let alphaM : OmegaM := ⟨alpha, MulAction.mem_orbit_self alpha⟩
        let YM : Subgroup M := Y.comap M.subtype
        have hzMmem : z ∈ M := hYltM.le hzY
        let zM : M := ⟨z, hzMmem⟩
        letI : MulAction M OmegaM := inferInstance
        letI : MulAction.IsPretransitive M OmegaM := inferInstance
        have hYstabM : MulAction.stabilizer M alphaM = YM := by
          ext m
          constructor
          · intro hm
            have hmFix : m • alphaM = alphaM :=
              MulAction.mem_stabilizer_iff.mp hm
            have hmFixG : (m : G) • alpha = alpha :=
              congrArg Subtype.val hmFix
            change (m : G) ∈ Y
            rw [← hY]
            exact MulAction.mem_stabilizer_iff.mpr hmFixG
          · intro hm
            apply MulAction.mem_stabilizer_iff.mpr
            apply Subtype.ext
            change (m : G) ∈ Y at hm
            have hmStab : (m : G) ∈ MulAction.stabilizer G alpha := by
              rw [hY]
              exact hm
            exact MulAction.mem_stabilizer_iff.mp hmStab
        have hYMproper : YM ≠ ⊤ := by
          intro htop
          have hMY : M ≤ Y := by
            intro m hm
            let mM : M := ⟨m, hm⟩
            have hmYM : mM ∈ YM := by
              rw [htop]
              trivial
            exact hmYM
          exact (not_le_of_gt hYltM) hMY
        have hzMY : zM ∈ YM := hzY
        have hzMI : IsInvolution zM := IsInvolution.subtype hz hzMmem
        have hcentM : Subgroup.centralizer ({zM} : Set M) ≤ YM := by
          intro c hc
          change (c : G) ∈ Y
          apply hcent
          apply Subgroup.mem_centralizer_singleton_iff.mpr
          exact congrArg Subtype.val
            (Subgroup.mem_centralizer_singleton_iff.mp hc)
        have hfactorM : pPrimeCore 2 M ⊔
            Subgroup.centralizer ({zM} : Set M) = ⊤ := by
          simpa [zM] using lemma311_factorization_subgroup
            M hzMmem (hcent.trans hYltM.le) hfactor
        have hMcardLt : Nat.card M < n := by
          simpa [hcard] using natCard_lt_of_subgroup_lt hMlt
        have hrec := ih (Nat.card M) hMcardLt
          (G := M) (Omega := OmegaM) rfl YM zM alphaM
          hYstabM hYMproper hzMY hzMI hcentM hfactorM
        exact lemma311_nonmaximal_transfer
          Y M z alpha hYltM.le hzMmem hY (by
            simpa [OmegaM, alphaM, YM, zM] using hrec))

/-- Lemma 3.11: the orbit package obtained from the operational Z-star
factorization at an involution in a proper point stabilizer. -/
public theorem lemma_3_11
    {G : Type u} {Omega : Type v} [Group G] [Finite G]
    [MulAction G Omega] [Finite Omega]
    [MulAction.IsPretransitive G Omega]
    (Y : Subgroup G) (z : G) (alpha : Omega)
    (hY : MulAction.stabilizer G alpha = Y)
    (hYproper : Y ≠ ⊤) (hzY : z ∈ Y) (hz : IsInvolution z)
    (hcent : Subgroup.centralizer ({z} : Set G) ≤ Y)
    (hfactor : pPrimeCore 2 G ⊔
      Subgroup.centralizer ({z} : Set G) = ⊤) :
    ∃ R : Subgroup G, ∃ Gamma : Set Omega,
      Gamma = MulAction.orbit R alpha ∧
      (∃ r : ℕ, Nat.Prime r ∧ Odd r ∧ IsPGroup r R ∧
        Nat.card Gamma = r) ∧
      IsCyclic R ∧
      (∀ q : G, q ∈ R → z * q * z⁻¹ = q⁻¹) ∧
      z ∈ Subgroup.normalizer (R : Set G) ∧
      (∀ beta, beta ∈ Gamma → z • beta ∈ Gamma) ∧
      (∀ {beta gamma}, beta ∈ Gamma → gamma ∈ Gamma → beta ≠ gamma →
        ∀ x : G, x • beta = beta → x • gamma = gamma →
          ∀ delta, delta ∈ Gamma → x • delta = delta) ∧
      (∀ beta, beta ∈ Gamma → beta ≠ alpha →
        ∃ t : G, IsInvolution t ∧
          t • alpha = beta ∧ t • beta = alpha) := by
  change lemma311Output Y z alpha
  exact lemma311_output_core_aux (Nat.card G) rfl
    Y z alpha hY hYproper hzY hz hcent hfactor

end

end CFSG.BenderSuzuki
