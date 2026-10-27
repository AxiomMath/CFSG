module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1ExcInputs
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
import CFSG.LocalAnalysis.StandardType.KGLangS1EToralLiftE6Even
import CFSG.LocalAnalysis.StandardType.KGLangS1EIndexBridge
import CFSG.LocalAnalysis.StandardType.KGLangS1EFixedLift
import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeAt
import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeU
import CFSG.LocalAnalysis.StandardType.GGTBTorRelE6Cover
import CFSG.LocalAnalysis.StandardType.KGLangS1AGlue
import CFSG.LocalAnalysis.StandardType.KGLangTorAGeneric
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangChev
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldE6
import CFSG.LocalAnalysis.StandardType.MarkingChevalley
import CFSG.LieType.SeitzGeneration.ExcTorusThreeRank
import CFSG.LieType.Simplicity.Exceptional

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.C14Exc

private theorem kgLangS1EExcE6EvenAux_nonabelian {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : ∃ a b : A, a * b ≠ b * a) : ∃ a b : B, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨e a, e b, fun h' => hab (e.injective (by rw [map_mul, map_mul, h']))⟩

private theorem kgLangS1EExcE6EvenAux_fix_center {K : Type} [Group K] [Finite K]
    (hZ : Nat.card (Subgroup.center K) ∣ 3) (α : MulAut K) (hα : α ^ 3 = 1)
    (z : K) (hz : z ∈ Subgroup.center K) : α z = z := by
  classical
  by_cases hz1 : z = 1
  · rw [hz1, map_one]
  have hcen : α z ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    have h := hz (α.symm g)
    calc g * α z = α (α.symm g) * α z := by rw [MulEquiv.apply_symm_apply]
      _ = α (α.symm g * z) := (map_mul α _ _).symm
      _ = α (z * α.symm g) := by rw [h]
      _ = α z * α (α.symm g) := map_mul α _ _
      _ = α z * g := by rw [MulEquiv.apply_symm_apply]
  let z' : Subgroup.center K := ⟨z, hz⟩
  have hz'1 : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hdvd : orderOf z' ∣ 3 := (orderOf_dvd_natCard z').trans hZ
  have hord : orderOf z' = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz'1
    · exact h
  have hcard : Nat.card (Subgroup.center K) = 3 :=
    Nat.dvd_antisymm hZ (hord ▸ orderOf_dvd_natCard z')
  have hz3 : z ^ 3 = 1 := by
    have h1 : z' ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
    simpa using congrArg Subtype.val h1
  have htop : Subgroup.zpowers z' = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hord, hcard]
  have hmem : (⟨α z, hcen⟩ : Subgroup.center K) ∈ Subgroup.zpowers z' := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hαz : α z = z ^ m := by simpa using (congrArg Subtype.val hm).symm
  have hordz : orderOf z = 3 :=
    (orderOf_injective (Subgroup.center K).subtype Subtype.coe_injective z').trans hord
  have hmod : α z = z ^ (m % 3) := by
    rw [hαz, ← zpow_mod_orderOf z m, hordz]
    norm_num
  have hr : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hr with h | h | h
  · rw [h, zpow_zero] at hmod
    exact absurd (α.injective (hmod.trans (map_one α).symm)) hz1
  · rw [h, zpow_one] at hmod
    exact hmod
  · exfalso
    rw [h, zpow_two] at hmod
    have h3α : α (α (α z)) = z := by
      have h := congrArg (fun φ : MulAut K => φ z)
        (show α * (α * α) = 1 by rw [← pow_three]; exact hα)
      simpa only [MulAut.mul_apply, MulAut.one_apply] using h
    have hzz : z * z * (z * z) = z := by
      calc z * z * (z * z) = z * (z * z) * z := by simp only [mul_assoc]
        _ = z ^ 3 * z := by rw [pow_three]
        _ = z := by rw [hz3, one_mul]
    have h2α : α (α z) = z := by rw [hmod, map_mul, hmod, hzz]
    rw [h2α, hmod] at h3α
    exact hz1 (by simpa using h3α)

private theorem kgLangS1EExcE6EvenAux_center {K R : Type} [Group K] [Finite K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R)
    (hdvd : ∀ ψ : K →* R, Function.Surjective ψ → ψ.ker ≤ Subgroup.center K →
      Nat.card ψ.ker ∣ 3) (A : Subgroup (MulAut K)) (hA : IsElemAbelian 3 A) :
    (∀ z ∈ Subgroup.center K, z ^ 3 = 1) ∧ (∀ α ∈ A, ∀ z ∈ Subgroup.center K, α z = z) := by
  let ψ : K →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hψs : Function.Surjective ψ := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψker : ψ.ker = Subgroup.center K := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hx' : (QuotientGroup.mk x : K ⧸ Subgroup.center K) = 1 := by
        apply θ.injective
        rw [map_one]
        exact hx
      exact (QuotientGroup.eq_one_iff x).mp hx'
    · intro hx
      show θ (QuotientGroup.mk x) = 1
      rw [(QuotientGroup.eq_one_iff x).mpr hx, map_one]
  have hZ : Nat.card (Subgroup.center K) ∣ 3 := by
    have h := hdvd ψ hψs (le_of_eq hψker)
    rwa [hψker] at h
  refine ⟨fun z hz => ?_, fun α hα z hz => kgLangS1EExcE6EvenAux_fix_center hZ α (hA.2 α hα) z hz⟩
  have h1 : orderOf (⟨z, hz⟩ : Subgroup.center K) ∣ 3 := (orderOf_dvd_natCard _).trans hZ
  have h2 : (⟨z, hz⟩ : Subgroup.center K) ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp h1
  simpa using congrArg Subtype.val h2

private noncomputable def kgLangS1EExcE6EvenAux_I (K₁ : Type) [Field K₁] :
    Set (MulAut (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K₁ false))) :=
  LargeEvenChevIDImage (LargeEvenCartanE 6) K₁ (LargeEvenChevH (LargeEvenCartanE 6) K₁ false)

theorem kgLangS1E_cont_E6_even
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .E6)
    (h3 : 3 ∣ lab.n) (heven : Even lab.n) :
    LargeEvenLabelAll lab (KGLangAxisS1ExcCont 3) := by
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  subst htag
  have hfcAll : LargeEvenLabelAll ⟨.E6, l, n⟩ (GGRawFieldConj 3) :=
    ggRawFieldConjOn_chev 3 (by norm_num) (by norm_num) ⟨.E6, l, n⟩ hlab
      (Or.inr (Or.inr (Or.inl rfl)))
  have hifAll : LargeEvenLabelAll ⟨.E6, l, n⟩ (GGRawInnField 3) :=
    ggRawInnFieldOn_E6 3 (by norm_num) (by norm_num) ⟨.E6, l, n⟩ hlab rfl
  have hpcAll : LargeEvenLabelAll ⟨.E6, l, n⟩ (GGRawPCyclic 3) :=
    ggRawPCyclicOn_E6 3 (by norm_num) (by norm_num) ⟨.E6, l, n⟩ hlab rfl
  have hall := largeEvenLabelAll_and hfcAll (largeEvenLabelAll_and hifAll hpcAll)
  have hraw := hall Q hQ
  unfold CFSG.StandardType.LargeEvenRawDatum CFSG.Assembly.LargeEvenRecipeChevalley at hraw
  unfold CFSG.StandardType.LargeEvenRawDatum CFSG.Assembly.LargeEvenRecipeChevalley
  obtain ⟨K₁, hf₁, hfin₁, hK₁, hQ₁, hfc₁, hif₁, hpc₁⟩ := hraw
  refine ⟨K₁, hf₁, hfin₁, hK₁, hQ₁, ?_⟩
  letI : Field K₁ := hf₁
  letI : Finite K₁ := hfin₁
  haveI : CharP K₁ 2 := charP_two_of_card hK₁
  have hn6 : 6 ≤ n := by
    have h1 : 1 ≤ n := hlab.1
    obtain ⟨a, ha⟩ : ∃ a, n = a + a := heven
    obtain ⟨b, hb⟩ : ∃ b, n = 3 * b := h3
    omega
  have hk5 : 5 ≤ Nat.card K₁ := by
    rw [hK₁]
    calc 5 ≤ 2 ^ 6 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn6
  let L : Type := AlgebraicClosure K₁
  letI : Field L := inferInstanceAs (Field (AlgebraicClosure K₁))
  letI : IsAlgClosed L := inferInstanceAs (IsAlgClosed (AlgebraicClosure K₁))
  letI : Algebra K₁ L := inferInstanceAs (Algebra K₁ (AlgebraicClosure K₁))
  haveI : IsAlgClosure K₁ L := inferInstanceAs (IsAlgClosure K₁ (AlgebraicClosure K₁))
  haveI : Algebra.IsAlgebraic K₁ L :=
    inferInstanceAs (Algebra.IsAlgebraic K₁ (AlgebraicClosure K₁))
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K₁ L).injective 2
  have hq : CFSG.IsQuasisimple ↥(CFSG.Blueprint.Chevalley.adjointGroup .E6 K₁) :=
    CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 K₁
  obtain ⟨eQ⟩ := centerQuot_chevGroup_equiv K₁ .E6
  have hs : IsSimpleGroup (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K₁ false)) := by
    haveI : IsSimpleGroup (CFSG.Blueprint.AdjointQuotient .E6 K₁) := hq.2.1
    exact eQ.isSimpleGroup
  have hna : ∃ a b : LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K₁ false),
      a * b ≠ b * a := kgLangS1EExcE6EvenAux_nonabelian eQ.symm hq.2.2
  intro K _ _ θ hcomm A hA hAIF α₀ hα₀ hα₀I hcard2 ξ hξ hξI J₀ hJ₀ hTor
  obtain ⟨u, hu, f, hf, huf⟩ := hAIF ξ hξ
  have hufI : u * f ∉ kgLangS1EExcE6EvenAux_I K₁ := by rw [← huf]; exact hξI
  have hufp : (u * f) ^ 3 = 1 := by rw [← huf, ← map_pow, hA.2 ξ hξ, map_one]
  obtain ⟨f', hf'F, u', -, hf'ord, -⟩ := hfc₁ hs hna u hu f hf hufI hufp
  obtain ⟨eb, hebn, εb, he1, hQmat, ⟨hstab₀, Θ, hρ, hρG, hΘ, hI, hconjΘ, hFj⟩, -, hfinB⟩ :=
    CFSG.HardMathSupport.C14ExcBridgeE6.bridge_chev_spec (τ := .E6) (K := K₁) hlab.1 hK₁ L
      (p := 3) Nat.prime_three ⟨f', hf'F, hf'ord⟩
  let ρ := (baseChangeGL (τ := .E6) (algebraMap K₁ L)).comp
    ((adjointGroup .E6 K₁).subtype.comp εb.toMonoidHom)
  let F₀ : ModGL .E6 L →* ModGL .E6 L := frobTwistGL .E6 L 2 eb 1
  let G : Subgroup (ModGL .E6 L) := ratPts .E6 L (endPow F₀ 3)
  haveI : Finite G := hfinB
  have hstab : ∀ g ∈ G, F₀ g ∈ G := by
    intro g hg
    refine ⟨hstab₀ g hg.1, ?_⟩
    show endPow F₀ 3 (F₀ g) = F₀ g
    rw [endPow_comm_apply, ratPts_fix hg]
  have hfix : ∀ g ∈ G, endPow F₀ 3 g = g := fun g hg => ratPts_fix hg
  have hPconj : ∀ g ∈ G, ∀ E : Subgroup (ModGL .E6 L),
      ExcFramesHalf.IsToralSubgroup .E6 L E →
      ExcFramesHalf.IsToralSubgroup .E6 L
        (E.map (MulAut.conj (g : ModGL .E6 L)⁻¹).toMonoidHom) := by
    intro g hg E hE
    obtain ⟨h, hh, hEt⟩ := hE
    refine ⟨g⁻¹ * h, Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_inf.mp hg).1) hh, ?_⟩
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hconj : (g⁻¹ * h)⁻¹ * ((MulAut.conj (g : ModGL .E6 L)⁻¹) x) * (g⁻¹ * h) =
        h⁻¹ * x * h := by
      rw [MulAut.conj_apply, inv_inv]
      group
    exact hconj ▸ hEt x hx
  have hQconj : ∀ g ∈ G, ∀ N : Subgroup (ModGL .E6 L),
      (∃ c ∈ adjointGroup .E6 L, N.map (MulAut.conj c).toMonoidHom ≤ torusGroup .E6 L) →
      ∃ c ∈ adjointGroup .E6 L, (N.map (MulAut.conj (g : ModGL .E6 L)).toMonoidHom).map
        (MulAut.conj c).toMonoidHom ≤ torusGroup .E6 L := by
    intro g hg N hN
    obtain ⟨c, hc, hcN⟩ := hN
    refine ⟨c * (g : ModGL .E6 L)⁻¹,
      Subgroup.mul_mem _ hc (Subgroup.inv_mem _ (Subgroup.mem_inf.mp hg).1), ?_⟩
    intro y hy
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hw
    have hxy : (MulAut.conj (c * (g : ModGL .E6 L)⁻¹)).toMonoidHom
        ((MulAut.conj (g : ModGL .E6 L)).toMonoidHom x) = (MulAut.conj c).toMonoidHom x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hxy]
    exact hcN (Subgroup.mem_map_of_mem _ hx)
  have hT : ∀ E : Subgroup (ModGL .E6 L), IsElemAbelian 3 E →
      (∀ x ∈ E, x ∈ G ∧ F₀ x = x) → ExcFramesHalf.IsToralSubgroup .E6 L E →
      ∃ N : Subgroup (ModGL .E6 L), N ≤ G ∧ (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) ∧
        (∀ x ∈ N, F₀ x ∈ N) ∧
        (∀ c ∈ N, ((List.range 3).map fun i => endPow F₀ i c).prod = 1 →
          ∃ s ∈ N, c = s⁻¹ * F₀ s) ∧ E ≤ N ∧
        ∃ c ∈ adjointGroup .E6 L, N.map (MulAut.conj c).toMonoidHom ≤ torusGroup .E6 L := by
    intro E hEab hEG htoral
    exact kgLangExcTorusInput_of_toral_conj
      (hM2 := CFSG.StandardType.LieCore.ggLieLangPosition_holds)
      (hp := by norm_num) (hp2 := by norm_num) (he := he1) (hQ := hQmat) (hfin := hfinB)
      E hEab hEG htoral
  have hPtoral : ExcFramesHalf.IsToralSubgroup .E6 L (Subgroup.closure {x : ModGL .E6 L |
      x ∈ G ∧ ∃ α ∈ A, kgInducedAut θ α ∈ kgLangS1EExcE6EvenAux_I K₁ ∧
        ∀ r, ρ (kgInducedAut θ α r) = x * ρ r * x⁻¹}) :=
    kgLangS1E_toral_lift_E6_even (n := n) hlab.1 (K₁ := K₁) hK₁ heven (L := L) (e := eb) he1
      hebn ρ Θ hρ hρG hΘ hI hconjΘ hFj θ hcomm A hA hAIF hξ hξI hJ₀ hTor
  have hidx : ρ.range.relIndex G ≤ 3 := by
    have hrange : ρ.range = (adjointGroup .E6 K₁).map (baseChangeGL (algebraMap K₁ L)) := by
      change ((baseChangeGL (τ := .E6) (algebraMap K₁ L)).comp
        ((adjointGroup .E6 K₁).subtype.comp εb.toMonoidHom)).range = _
      rw [MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr εb.surjective,
        Subgroup.map_top, Subgroup.range_subtype]
    have hFr : ∀ c, iterateFrobenius L 2 (eb * 3) c = c ^ Nat.card K₁ := by
      intro c
      rw [iterateFrobenius_def, hK₁, hebn]
    have hXC : G ≤ adjointGroup .E6 L := fun x hx => (Subgroup.mem_inf.mp hx).1
    have hXF : ∀ x ∈ G, Units.map (entrywiseHom (iterateFrobenius L 2 (eb * 3))) x = x := by
      intro x hx
      have h1 : endPow F₀ 3 x = x := ratPts_fix hx
      have h2 := CFSG.HardMathSupport.C14ExcBridgeU.endPow_frobTwist_one (τ := .E6) (L := L)
        eb 3 x
      exact h2.symm.trans h1
    have hdvd := CFSG.LieType.SeitzGeneration.relIndex_dvd_untwisted 3 (Or.inl ⟨rfl, rfl⟩) K₁
      L (iterateFrobenius L 2 (eb * 3)) hFr G hXC hXF
    rw [hrange]
    exact Nat.le_of_dvd (by norm_num) hdvd
  obtain ⟨hZp, hZA⟩ := kgLangS1EExcE6EvenAux_center θ (fun ψ hψ hker =>
    (card_ker_dvd_gcd_recipe_E6 (K := K₁) ψ hψ hker hcomm).trans (Nat.gcd_dvd_left 3 _)) A hA
  have hFL := kgLangS1E_fixedLift_split K₁ hk5 L
    (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K₁ false)) εb F₀ Θ hconjΘ
  have hlift : ∀ N : Subgroup (ModGL .E6 L),
      (∃ c ∈ adjointGroup .E6 L, N.map (MulAut.conj c).toMonoidHom ≤ torusGroup .E6 L) →
      (∀ x ∈ G, (∃ α ∈ A, kgInducedAut θ α ∈ kgLangS1EExcE6EvenAux_I K₁ ∧
        ∀ r, ρ (kgInducedAut θ α r) = x * ρ r * x⁻¹) → x ∈ N) →
      ∀ α ∈ A, kgInducedAut θ α ∈ kgLangS1EExcE6EvenAux_I K₁ → ∀ r, ρ r ∈ N →
        ∀ k : K, θ (QuotientGroup.mk k) = r → α k = k := by
    intro N hN hxN α hα hαI r hrN k hk
    obtain ⟨c, hc, hcN⟩ := hN
    obtain ⟨x, hx⟩ := (hI (kgInducedAut θ α)).1 hαI
    have hxN' : (x : ModGL .E6 L) ∈ N := hxN (x : ModGL .E6 L) x.2
      ⟨α, hα, hαI, fun r' => by rw [← hx]; exact hconjΘ x r'⟩
    refine hFL K θ hcomm α x r k hk hx.symm ⟨c, hc, ?_, ?_⟩
    · exact hcN (Subgroup.mem_map_of_mem _ hxN')
    · exact hcN (Subgroup.mem_map_of_mem _ hrN)
  obtain ⟨B₀, X, u₀, f₀, hmem, hdec, hXcard, -, -, -, -, -, -, -, hXβ⟩ :=
    kgLangTorA_setup (p := 3) (by norm_num) hs hna hif₁ hpc₁ hfc₁ θ hcomm hA hAIF hξ hξI
  obtain ⟨hB₀AI, -⟩ := kgLangS1A_setup_eq θ hcomm hmem hXcard hXβ
  have hB₀A : B₀ ≤ A := fun β hβ => (hB₀AI β hβ).1
  have hB₀I : ∀ β ∈ B₀, kgInducedAut θ β ∈ kgLangS1EExcE6EvenAux_I K₁ :=
    fun β hβ => (hB₀AI β hβ).2
  have hdecI : ∀ α ∈ A, ∃ β ∈ A, kgInducedAut θ β ∈ kgLangS1EExcE6EvenAux_I K₁ ∧
      ∃ j : ℕ, α = β * ξ ^ j := by
    intro α hα
    obtain ⟨β, hβ, j, hj⟩ := hdec α hα
    exact ⟨β, hB₀A hβ, hB₀I β hβ, j, hj⟩
  obtain ⟨k, e', he'1, he'p, hAe, hAk, hke⟩ :=
    kgLangS1E_langPair_at_of_bridge_index (p := 3) Nat.prime_three (by norm_num) hs hna hfc₁
      (G := G) (F₀ := F₀) hstab hfix ρ Θ hρ hρG hΘ hI hconjΘ hFj hidx
      (fun E => ExcFramesHalf.IsToralSubgroup .E6 L E)
      (fun N => ∃ c ∈ adjointGroup .E6 L, N.map (MulAut.conj c).toMonoidHom ≤ torusGroup .E6 L)
      hPconj hQconj hT θ hcomm hZp A hA hZA hAIF hcard2 hPtoral hlift ξ hξ hξI hdecI
  have hBk : ∀ β ∈ B₀, β k = k := fun β hβ => hAk β (hB₀A hβ) (hB₀I β hβ)
  have hα₀B₀ : α₀ ∉ B₀ := fun h => hα₀I (hB₀I α₀ h)
  obtain ⟨e'', he''1, he''p, hAe'', hke''⟩ :=
    kgLangS1A_concl_of_xi (p := 3) (by norm_num) hA hB₀A hξ hdec hα₀ hα₀B₀ he'1 he'p hAe hBk hke
  exact ⟨k, e'', he''1, he''p, hAe'', hAk, hke''⟩

end CFSG.StandardType
