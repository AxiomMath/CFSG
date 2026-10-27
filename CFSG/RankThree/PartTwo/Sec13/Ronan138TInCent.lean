module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138TInRes
public import CFSG.RankThree.PartTwo.Sec13.Ronan138SKCentPGL
import CFSG.RankThree.PartTwo.Sec13.Ronan138SKCentL3
import CFSG.RankThree.PartTwo.Sec13.Ronan138S131
import CFSG.RankThree.PartTwo.Sec13.Item13Plane
import CFSG.RankThree.PartTwo.Sec13.Item13Prod
import CFSG.RankThree.PartTwo.Sec13.Item138ProofTools
import CFSG.RankThree.PartTwo.Sec13.Item138ProofExists
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec18.Components
import CFSG.RankThree.PartTwo.Sec4.Item424Res6ProofSolv
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarSetup
import CFSG.RankThree.PartTwo.Sec11.KS11LieProofSL2
import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138T

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo Matrix
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi zPi PiField ModThree Type123 diagE blockHom
  blockMat coe_blockHom)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.RankThree.PartTwo.Sec13.Item138Proof
open Ronan138S
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section PGL


theorem centPGL (h131 : Item131) (hspor : SporadicModels131)
    {A L E F : Subgroup G} {c x y t : G} (hfr : Ronan138S.Frame138Base A L E F c x y t) {e : G}
    {K : Subgroup G} (heΩ : Subgroup.zpowers e ∈ omegaA E) (hK : K ∈ lA E e) (heF : e ∉ F)
    (hdK : ⁅x, y⁆ ∈ K) (hPGLK : Sec8.IsZ3PGLThreePi (lBarA e K E))
    (hcN : c ∈ Subgroup.normalizer (K : Set G)) :
    Group.IsSolvable ((Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨c, hcN⟩)).toMonoidHom.eqLocus
      (MonoidHom.id (K ⧸ aschbacherSolvableCore 3 K))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hH := hfr.hH
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

end PGL

theorem centL3 (h48 : Sec4.Item4_8)
    {A L E F : Subgroup G} {c x y t : G} (hfr : Ronan138S.Frame138Base A L E F c x y t) {e : G}
    {K : Subgroup G} (heΩ : Subgroup.zpowers e ∈ omegaA E) (hK : K ∈ lA E e) (heF : e ∉ F)
    (hL3K : IsLThreePi (K ⧸ aschbacherSolvableCore 3 K))
    (hφ3 : Nonempty (lBarA e K E ≃* Multiplicative (ZMod 3) × Sec12.lBar e K))
    (hirr : Sec21.IsIrreducibleOn (Sec4.autIn (K ⊓ Subgroup.normalizer (E : Set G)) (E ⊓ K)))
    (hcN : c ∈ Subgroup.normalizer (K : Set G)) :
    Group.IsSolvable ((Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨c, hcN⟩)).toMonoidHom.eqLocus
      (MonoidHom.id (K ⧸ aschbacherSolvableCore 3 K))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hH := hfr.hH
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
  have heE : e ∈ E := (zpowers_mem_omegaA_iff.mp heΩ).1
  have he3 : e ^ 3 = 1 := hE3.2 e heE
  have he1 : e ≠ 1 := by
    rintro rfl
    have := (zpowers_mem_omegaA_iff.mp heΩ).2.1
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at this
    norm_num at this
  have hc3 : c ^ 3 = 1 := hE3.2 c hcE
  have hCEset := sectionCentralizer_eq_inf hK.2.1
  rw [hK.2.2.1] at hCEset
  have hCE : E ⊓ Sec4.thetaQuotCentralizer K = Subgroup.zpowers e :=
    SetLike.coe_injective hCEset.symm
  have heC : e ∈ Sec4.thetaQuotCentralizer K :=
    (Subgroup.mem_inf.mp (hCE.symm ▸ Subgroup.mem_zpowers e : e ∈ E ⊓ _)).2
  obtain ⟨φ3⟩ := hφ3
  have hB9 : Nat.card (E ⊓ K : Subgroup G) = 9 := card_inf_eq_nine hD (isPerfect_lBar hD) φ3
  set B := E ⊓ K with hBdef
  have hKe : ∀ k ∈ K, k * e = e * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hk)
  have heB : e ∉ B := by
    intro heB
    rcases eq_bot_or_eq_of_isIrreducibleOn hirr (Subgroup.zpowers_le.mpr heB) (fun k hk => by
      apply mem_normalizer_of_map_le
      rw [MonoidHom.map_zpowers]
      apply Subgroup.zpowers_le.mpr
      change k * e * k⁻¹ ∈ Subgroup.zpowers e
      rw [hKe k (Subgroup.mem_inf.mp hk).1, mul_inv_cancel_right]
      exact Subgroup.mem_zpowers e) with h0 | h0
    · exact he1 (by simpa using (Subgroup.zpowers_eq_bot).mp h0)
    · have : Nat.card (Subgroup.zpowers e) = Nat.card B := by rw [h0]
      rw [card_zpowers_of_pow_three he3 he1, hB9] at this
      norm_num at this
  have hcomm : ∀ a ∈ Subgroup.zpowers e, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_left (hfr.hEab e heE b (Subgroup.mem_inf.mp hb).1) k).eq
  obtain ⟨hcard, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  rw [zpowers_inf_eq_bot he3 heB, Subgroup.card_bot, mul_one,
    card_zpowers_of_pow_three he3 he1, hB9] at hcard
  have heq : Subgroup.zpowers e ⊔ B = E :=
    Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr heE) inf_le_left)
      (by rw [hE27, hcard])
  have hc' : c ∈ ((Subgroup.zpowers e ⊔ B : Subgroup G) : Set G) := by
    rw [heq]
    exact hcE
  rw [hset] at hc'
  obtain ⟨a, ha, b, hbB, hab⟩ := hc'
  obtain ⟨n, rfl⟩ := exists_pow_eq_of_mem_zpowers ha
  change e ^ n * b = c at hab
  have hbE : b ∈ E := (Subgroup.mem_inf.mp hbB).1
  have hbK : b ∈ K := (Subgroup.mem_inf.mp hbB).2
  have hb3 : b ^ 3 = 1 := hE3.2 b hbE
  set d := ⁅x, y⁆ with hd
  have hdK : d ∈ K := Ronan138T.comm_mem_of_not_mem h48 hfr heΩ hK heF
  have hdB : d ∈ B := Subgroup.mem_inf.mpr ⟨hfr.hdE, hdK⟩
  have hbd : b ∉ Subgroup.zpowers d := by
    intro hbd
    obtain ⟨k, rfl⟩ := exists_pow_eq_of_mem_zpowers hbd
    by_cases hn : 3 ∣ n
    · obtain ⟨m, rfl⟩ := hn
      apply hfr.hcL
      rw [← hab, pow_mul, he3, one_pow, one_mul]
      exact pow_mem hfr.hdL k
    · apply heF
      have hen : e ^ n ∈ F := by
        have : e ^ n = c * (d ^ k)⁻¹ := by rw [← hab]; group
        rw [this]
        exact mul_mem hfr.hcF (inv_mem (pow_mem (Subgroup.mem_inf.mp hfr.hdZ).2 k))
      exact Subgroup.zpowers_le.mpr hen (mem_zpowers_pow_of_not_dvd he3 hn)
  have hb1 : b ≠ 1 := fun h1 => hbd (h1 ▸ one_mem _)
  have hcomm2 : ∀ a ∈ Subgroup.zpowers b, ∀ a' ∈ Subgroup.zpowers d, a * a' = a' * a := by
    intro a ha a' ha'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨k', rfl⟩ := Subgroup.mem_zpowers_iff.mp ha'
    exact ((Commute.zpow_left (hfr.hEab b hbE d hfr.hdE) k).zpow_right k').eq
  obtain ⟨hcard2, hset2⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm2
  rw [zpowers_inf_eq_bot hb3 hbd, Subgroup.card_bot, mul_one,
    card_zpowers_of_pow_three hb3 hb1, card_zpowers_of_pow_three hfr.hd3 hfr.hd1] at hcard2
  have heq2 : Subgroup.zpowers b ⊔ Subgroup.zpowers d = B :=
    Subgroup.eq_of_le_of_card_ge
      (sup_le (Subgroup.zpowers_le.mpr hbB) (Subgroup.zpowers_le.mpr hdB)) (by rw [hB9, hcard2])
  obtain ⟨p, f₀, _, hf₀, hiso⟩ := hL3K
  obtain ⟨π, Fld, _, hPi, hq, ⟨ψ⟩⟩ := exists_projImage_model hf₀ hiso
  have hπ : π = false → UnitaryFieldData p f₀ Fld := fun h => by subst h; exact hPi.unitary
  have hq' : π = false → ModThree false (p ^ f₀) := fun h => by subst h; exact hq
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hK.1
  have hq2 : 2 < p ^ f₀ := Item138Proof.two_lt_of_mulEquiv hKq hPi hq ψ
  haveI : Group.IsPerfect (K ⧸ aschbacherSolvableCore 3 K) := hKq.1
  haveI : Group.IsPerfect (projImage (slPi π 3 (p ^ f₀) Fld)) :=
    Group.IsPerfect.ofSurjective (f := ψ.toMonoidHom) ψ.surjective
  obtain ⟨N, hN, hNe⟩ := Subgroup.mem_map.mp
    (ψ ((⟨b, hbK⟩ : K) : K ⧸ aschbacherSolvableCore 3 K)).2
  have hbψ : ActsPGL ψ b N := actsPGL_of_mem hπ hbK hN hNe.symm
  have heψ : ActsPGL ψ e 1 := actsPGL_of_mem_thetaQuotCentralizer heC
  have hcψ : ActsPGL ψ c N := by
    have h1 := (heψ.pow hπ n).mul hbψ
    rw [one_pow, one_mul, hab] at h1
    exact h1
  obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau hPi hq
  have hNH : N ∈ glPi π 3 (p ^ f₀) Fld := Sec4.slPi_le_glPi hπ hN
  have hNZ : N ∉ zPi π 3 (p ^ f₀) Fld := by
    intro hz
    rw [Sec4.zPi_eq hπ hq' hτ hτ1] at hz
    have hcC := hcψ.mem_thetaQuotCentralizer (Sec4.mk_eq_one_iff_mem_statedScalars.mpr hz.2)
    have hce : c ∈ Subgroup.zpowers e := hCE ▸ Subgroup.mem_inf.mpr ⟨hcE, hcC⟩
    apply heF
    have heq' := zpowers_eq_of_mem hc3 hfr.hc1 he3 he1 hce
    exact Subgroup.zpowers_le.mpr hfr.hcF (heq' ▸ Subgroup.mem_zpowers e)
  have hN3 : N ^ 3 ∈ zPi π 3 (p ^ f₀) Fld := by
    rw [Sec4.zPi_eq hπ hq' hτ hτ1]
    refine ⟨pow_mem hNH 3, ?_⟩
    have h1 := hcψ.pow hπ 3
    rw [hc3] at h1
    have h2 := ActsPGL.mk_eq hPi hq h1 (actsPGL_one hπ)
    rw [map_one] at h2
    exact Sec4.mk_eq_one_iff_mem_statedScalars.mp h2
  rcases Sec4.type123_exhaust hPi hq hNH hNZ hN3 with h1 | h2 | h3
  · exact isSolvable_eqLocus_of_centMod hcψ hcN
      (Sec4.Res424Six.isSolvable_centMod_of_type13 hPi hq hNH hNZ hN3 (Or.inl h1))
  · exfalso
    obtain ⟨ε, hε3, hε1, z, hz, g, hg, hDg⟩ := h2
    have hεK : (ε : Fld) ≠ 1 := fun h => hε1 (Units.ext h)
    obtain ⟨ζ, -, rfl⟩ := Sec4.exists_scalar_of_mem_zPi hPi hq hε3 hεK hz
    have hNy : N * GeneralLinearGroup.scalar (Fin 3) ζ = g * diagE ε * g⁻¹ := by
      rw [← hDg]
      group
    have hJK := Ronan138T.residual_le_of_not_mem h48 hfr heΩ hK heF
    obtain ⟨hdJ, -⟩ := typeTwo_frame hfr heE heF
    set J := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({e} : Set G)) with hJ
    have hJL : J ≤ L ⊓ Subgroup.centralizer ({e} : Set G) := Sec6.inSubgroup_perfectResidual_le _
    have hJb : J ≤ Subgroup.centralizer ({b} : Set G) := by
      intro j hj
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hje : Commute j e :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hJL hj)).2
      have hjc : Commute j c :=
        Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer (Subgroup.mem_inf.mp
          (hJL hj)).1)
      have hb' : b = (e ^ n)⁻¹ * c := by rw [← hab]; group
      rw [hb']
      exact ((hje.pow_right n).inv_right.mul_right hjc).eq
    have hdI : d ∈ inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({b} : Set G)) :=
      Sec18.le_inSubgroup_perfectResidual (Sec18.commutator_inSubgroup_perfectResidual _)
        (le_inf hJK hJb) hdJ
    obtain ⟨Bd, hBd, hBdψ⟩ :=
      exists_block_of_mem_residual hPi hq hq2 ψ hbK hb3 hε3 hε1 hg hbψ hNy hdK hdI
    have hdetBd : GeneralLinearGroup.det Bd = 1 :=
      Sec11.KS11LieProof.det_eq_one_of_mem_slPi hPi hBd
    have hD3 : ((⟨d, hdK⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow]
      have : (⟨d, hdK⟩ : K) ^ 3 = 1 := Subtype.ext (by simpa using hfr.hd3)
      rw [this, QuotientGroup.mk_one]
    have hBd3 : Bd ^ 3 = 1 := by
      have h1 : ProjGenLinGroup.mk (g * blockHom (Bd ^ 3) * g⁻¹) = 1 := by
        rw [map_pow, ← conj_pow, map_pow, hBdψ, ← Subgroup.coe_pow, ← map_pow, hD3, map_one,
          Subgroup.coe_one]
      have hsc := Sec11.KS11LieProof.conj_mem_statedScalars_iff.mp
        (Sec4.mk_eq_one_iff_mem_statedScalars.mp h1)
      exact Sec11.KS11LieProof.eq_one_of_blockHom_mem_statedScalars
        (by rw [map_pow, hdetBd, one_pow]) hsc
    have hBd1 : Bd ≠ 1 := by
      intro h1
      rw [h1, map_one, mul_one, mul_inv_cancel, map_one] at hBdψ
      have h2 : ψ ((⟨d, hdK⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) = 1 :=
        Subtype.ext hBdψ.symm
      rw [map_eq_one_iff _ ψ.injective, QuotientGroup.eq_one_iff] at h2
      have := Item134SylowBarProof.eq_one_of_mem_theta_of_pow h2 (k := 1)
        (Subtype.ext (by simpa using hfr.hd3))
      exact hfr.hd1 (congrArg Subtype.val this)
    have hdetM : (Bd : Matrix (Fin 2) (Fin 2) Fld).det = 1 := by
      rw [← GeneralLinearGroup.val_det_apply, hdetBd, Units.val_one]
    have hM3 : (Bd : Matrix (Fin 2) (Fin 2) Fld) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hBd3, Units.val_one]
    have hM1 : (Bd : Matrix (Fin 2) (Fin 2) Fld) ≠ 1 := fun h1 => hBd1 (Units.ext h1)
    have hBdtr := trace_pow_of_cube hdetM hM3 hM1
    have h3K : (3 : Fld) ≠ 0 := hPi.three_ne_zero hq
    have hKV : K ⊓ Subgroup.normalizer (E : Set G) ≤
        Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
      intro k hk
      obtain ⟨hkK, hkN⟩ := Subgroup.mem_inf.mp hk
      apply mem_normalizer_of_map_le
      rw [MonoidHom.map_zpowers]
      apply Subgroup.zpowers_le.mpr
      change k * d * k⁻¹ ∈ Subgroup.zpowers d
      have hwE : k * d * k⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hkN d).mp hfr.hdE
      have hwK : k * d * k⁻¹ ∈ K := mul_mem (mul_mem hkK hdK) (inv_mem hkK)
      have hw' : k * d * k⁻¹ ∈ ((Subgroup.zpowers b ⊔ Subgroup.zpowers d : Subgroup G) :
          Set G) := by
        rw [heq2]
        exact Subgroup.mem_inf.mpr ⟨hwE, hwK⟩
      rw [hset2] at hw'
      obtain ⟨u₁, hu₁, u₂, hu₂, hu⟩ := hw'
      obtain ⟨i, rfl⟩ := exists_pow_eq_of_mem_zpowers hu₁
      obtain ⟨j, rfl⟩ := exists_pow_eq_of_mem_zpowers hu₂
      change b ^ i * d ^ j = k * d * k⁻¹ at hu
      obtain ⟨Nk, -, hNke⟩ := Subgroup.mem_map.mp
        (ψ ((⟨k, hkK⟩ : K) : K ⧸ aschbacherSolvableCore 3 K)).2
      set X := g * blockHom Bd * g⁻¹ with hX
      set Y := g * (diagE (ε ^ i) * blockHom (Bd ^ j)) * g⁻¹ with hY
      have hwbar : ((⟨k * d * k⁻¹, hwK⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) =
          ((⟨k, hkK⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) *
            ((⟨d, hdK⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) *
            ((⟨k, hkK⟩ : K) : K ⧸ aschbacherSolvableCore 3 K)⁻¹ := by
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
        rfl
      have hwbar' : ((⟨k * d * k⁻¹, hwK⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) =
          ((⟨b, hbK⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) ^ i *
            ((⟨d, hdK⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) ^ j := by
        rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul]
        congr 1
        exact Subtype.ext (by simp [hu])
      have e1 : (ψ ((⟨k * d * k⁻¹, hwK⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) :
          ProjGenLinGroup (Fin 3) Fld) = ProjGenLinGroup.mk (Nk * X * Nk⁻¹) := by
        rw [hwbar, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
          Subgroup.coe_inv, ← hNke, ← hBdψ, ← map_inv, ← map_mul, ← map_mul]
      have hNmk : ProjGenLinGroup.mk N = ProjGenLinGroup.mk (g * diagE ε * g⁻¹) := by
        rw [← hNy, map_mul, ProjGenLinGroup.mk_scalar, mul_one]
      have e2 : (ψ ((⟨k * d * k⁻¹, hwK⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) :
          ProjGenLinGroup (Fin 3) Fld) = ProjGenLinGroup.mk Y := by
        rw [hwbar', map_mul, map_pow, map_pow, Subgroup.coe_mul, Subgroup.coe_pow,
          Subgroup.coe_pow, ← hNe, hNmk, ← hBdψ, ← map_pow, ← map_pow, ← map_mul, hY,
          conj_pow, conj_pow, Sec11.KS11LieProof.diagE_pow, map_pow]
        congr 1
        group
      have e3 := e1.symm.trans e2
      obtain ⟨u, hu'⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp e3
      have htrX : (X : Matrix (Fin 3) (Fin 3) Fld).trace = 0 := by
        have h1 := Sec4.trace_inv_conj g⁻¹ (blockHom Bd)
        rw [inv_inv] at h1
        rw [hX, h1, Sec11.KS11LieProof.coe_blockHom_of_det hdetBd, trace_blockMat]
        have := hBdtr 1
        simp only [pow_one, show (1 : ℕ) % 3 = 1 by rfl, one_ne_zero, if_false] at this
        rw [this]
        ring
      have htrY : (Y : Matrix (Fin 3) (Fin 3) Fld).trace = 0 := by
        rw [← hu', Sec4.trace_mul_scalar]
        have h1 := Sec4.trace_inv_conj Nk⁻¹ X
        rw [inv_inv] at h1
        rw [h1, htrX, mul_zero]
      have hdetj : GeneralLinearGroup.det (Bd ^ j) = 1 := by rw [map_pow, hdetBd, one_pow]
      rw [hY, trace_conj_diagE_mul_blockHom g (ε ^ i) hdetj, Units.val_pow_eq_pow_val,
        Units.val_pow_eq_pow_val, hBdtr j] at htrY
      have hi : i % 3 = 0 := by
        by_contra hi
        have hεi1 : (ε : Fld) ^ i ≠ 1 := by
          have hi' : (ε : Fld) ^ i = (ε : Fld) ^ (i % 3) := by
            conv_lhs => rw [← Nat.mod_add_div i 3, pow_add, pow_mul, hε3, one_pow, mul_one]
          rw [hi']
          have hlt : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
          interval_cases hr : i % 3
          · exact absurd rfl hi
          · simpa using hεK
          · intro h2
            apply hεK
            calc (ε : Fld) = (ε : Fld) ^ 3 / (ε : Fld) ^ 2 := by
                  field_simp [show (ε : Fld) ≠ 0 from ε.ne_zero]
              _ = 1 := by rw [hε3, h2, div_one]
        have hεi3 : ((ε : Fld) ^ i) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hε3, one_pow]
        split_ifs at htrY with hj
        · have h4 : (ε : Fld) ^ i = -2 := by linear_combination htrY
          rw [h4] at hεi3
          apply h3K
          have h9 : (3 : Fld) * 3 = 0 := by linear_combination -hεi3
          exact mul_self_eq_zero.mp h9
        · exact hεi1 (by linear_combination htrY)
      have hbi : b ^ i = 1 := by
        rw [← Nat.mod_add_div i 3, hi, zero_add, pow_mul, hb3, one_pow]
      rw [← hu, hbi, one_mul]
      exact pow_mem (Subgroup.mem_zpowers d) j
    rcases eq_bot_or_eq_of_isIrreducibleOn hirr (Subgroup.zpowers_le.mpr hdB) hKV with h0 | h0
    · exact hfr.hd1 (by simpa using (Subgroup.zpowers_eq_bot).mp h0)
    · have : Nat.card (Subgroup.zpowers d) = Nat.card B := by rw [h0]
      rw [card_zpowers_of_pow_three hfr.hd3 hfr.hd1, hB9] at this
      norm_num at this
  · exact absurd ⟨N, hN, fun m _ => rfl⟩ (Sec4.not_inner_of_type3 hPi hq hNH h3)

end CFSG.RankThree.PartTwo.Sec13.Ronan138T
