module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallKGAt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallKGCom
public import CFSG.Quasithin.Background.A3StructureDefs
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport
import CFSG.Quasithin.Background.F918Z4bL2
import CFSG.Quasithin.Background.F918Z4c2Real
import CFSG.Walter.PSL2Facts.Even
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallElem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

theorem s1667_kg_l2even_params {J : Type} [Group J] {f : ℕ} (h : LieModel J .PSL 2 2 f) :
    2 ≤ f ∧ CFSG.Quasithin.IsPSL 2 2 f J := by
  obtain ⟨-, hf1, -, h22, -⟩ := h.admissible
  refine ⟨?_, h.statedClassicalModel (by decide)⟩
  by_contra hlt
  have hf : f = 1 := by omega
  subst hf
  exact h22 rfl

theorem s1667_kg_psl2_even_comm_two {J : Type} [Group J] [Finite J] {f : ℕ} (hf : 2 ≤ f)
    (hJ : CFSG.Quasithin.IsPSL 2 2 f J) :
    ∀ P : Subgroup J, IsPGroup 2 P → ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
  obtain ⟨e⟩ := CFSG.Quasithin.exists_mulEquiv_psl2_galoisField hf hJ
  haveI : Finite (CFSG.GorensteinWalter.PSL2 (GaloisField 2 f)) := Finite.of_equiv J e.toEquiv
  intro P hP a ha b hb
  obtain ⟨U, hU⟩ := (hP.map e.toMonoidHom).exists_le_sylow
  have hcomm := (CFSG.Walter.psl2_even_sylow_two hf U).1
  have h1 : e a ∈ (U : Subgroup (CFSG.GorensteinWalter.PSL2 (GaloisField 2 f))) := hU ⟨a, ha, rfl⟩
  have h2 : e b ∈ (U : Subgroup (CFSG.GorensteinWalter.PSL2 (GaloisField 2 f))) := hU ⟨b, hb, rfl⟩
  have h3 := congrArg Subtype.val (hcomm.toIsMulCommutative.is_comm.comm ⟨e a, h1⟩ ⟨e b, h2⟩)
  apply e.injective
  simpa using h3

theorem k67BPrimeOneAt_psl2_even {Q : Type} [Group Q] [Finite Q] (J : Subgroup Q) (hJ : J.Normal)
    (hC : centralizer (J : Set Q) = ⊥) {f : ℕ}
    (h : LieModel ↥J .PSL 2 2 f) : K67BPrimeOneAt Q J := by
  haveI := hJ
  intro x hxJ hx3 A hA hAx hAn h4
  exfalso
  obtain ⟨hf2, hPSL⟩ := s1667_kg_l2even_params h
  obtain ⟨-, -, -, -, F, hF, hFin, hcard, ⟨e⟩⟩ :=
    CFSG.ComponentClassification.AutL2Facts.lieModel_psl2_data h
  haveI : CharP F 2 := CFSG.Quasithin.Z4c2.charP_two_of_card_eq_two_pow (by simpa using hcard)
  let φ : Q →* MulAut ↥J := MulAut.conjNormal
  have hinj : Function.Injective φ := s1667_kg_conjNormal_injective J hC
  let E : Subgroup (MulAut ↥J) := A.map φ
  have hA2 : CFSG.Quasithin.IsElemAb2 A :=
    ⟨fun a ha b hb => comm_of_isElemAbelian hA ha hb, hA.2⟩
  have hE : CFSG.Quasithin.IsElemAb2 E := hA2.map φ
  haveI : Finite ↥E := Finite.of_equiv ↥A (Subgroup.equivMapOfInjective A φ hinj).toEquiv
  have hcardE : Nat.card E = Nat.card A := Subgroup.card_map_of_injective hinj
  have hrk : 2 ≤ CFSG.Quasithin.rk E := by
    by_contra hlt
    have h1 : CFSG.Quasithin.rk E ≤ 1 := by omega
    have h2 : 2 ^ CFSG.Quasithin.rk E ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
    have h3 := hE.card_eq_two_pow
    omega
  obtain ⟨g, hgE, hg1⟩ := CFSG.Quasithin.exists_inner_of_two_le_rk hf2 hPSL hE hrk
  obtain ⟨a, haA, hag⟩ := hgE
  have hag' : φ a = φ (g : Q) := hag.trans (MulAut.conjNormal_val (H := J) (h := g)).symm
  have hag'' : a = (g : Q) := hinj hag'
  have hg1' : g ≠ 1 := by
    rintro rfl
    exact hg1 (map_one _)
  have hg2 : g ^ 2 = 1 := Subtype.ext (by simpa [hag''] using hA.2 a haA)
  have hgord : orderOf g = 2 := orderOf_eq_prime hg2 hg1'
  have hgx : g * (⟨x, hxJ⟩ : ↥J) = (⟨x, hxJ⟩ : ↥J) * g := by
    apply Subtype.ext
    have := Subgroup.mem_centralizer_singleton_iff.mp (hAx haA)
    simpa [hag''] using this
  have hx'3 : orderOf (⟨x, hxJ⟩ : ↥J) = 3 := (Subgroup.orderOf_coe ⟨x, hxJ⟩).symm.trans hx3
  have hte : orderOf (e g) = 2 := by rw [MulEquiv.orderOf_eq]; exact hgord
  have hxe : e ⟨x, hxJ⟩ ∈ centralizer ({e g} : Set (CFSG.GorensteinWalter.PSL2 F)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hgx]
  have hsq := CFSG.Walter.psl2_sq_eq_one_of_mem_centralizer_of_charTwo hte hxe
  have hxord : orderOf (e ⟨x, hxJ⟩) = 3 := by rw [MulEquiv.orderOf_eq]; exact hx'3
  have hdvd : orderOf (e ⟨x, hxJ⟩) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  rw [hxord] at hdvd
  omega

theorem k67CaseIIIAt_psl2_even {Q : Type} [Group Q] [Finite Q] (J : Subgroup Q) (hJ : J.Normal)
    (hC : centralizer (J : Set Q) = ⊥) {f : ℕ}
    (h : LieModel ↥J .PSL 2 2 f) : K67CaseIIIAt Q J := by
  haveI := hJ
  intro x hxJ hx3 E hE hE4 hEJ hEx W hW hW1 hWx hWE hN
  obtain ⟨hf2, hPSL⟩ := s1667_kg_l2even_params h
  let x' : ↥J := ⟨x, hxJ⟩
  have hx'3 : orderOf x' = 3 := (Subgroup.orderOf_coe x').symm.trans hx3
  obtain ⟨w, hw⟩ := CFSG.Quasithin.Z4c2.exists_inverting hPSL x'
  obtain ⟨s', -, hsx', k, hk⟩ := s1667_kg_exists_two_element_inverting hw
  have hsx : (s' : Q) * x * (s' : Q)⁻¹ = x⁻¹ := congrArg Subtype.val hsx'
  have hsmem : (s' : Q) ∈ normalizer ((zpowers x : Subgroup Q) : Set Q) :=
    s1667_kg_mem_normalizer_zpowers_of_inv hsx
  have hxmem : x ∈ normalizer ((zpowers x : Subgroup Q) : Set Q) :=
    Subgroup.le_normalizer (Subgroup.mem_zpowers x)
  exact s1667_kg_false_of_inverting_two_element
    (s1667_kg_comm_of_le J (s1667_kg_psl2_even_comm_two hf2 hPSL)) hx3
    ⟨k, (Subgroup.orderOf_coe s').trans hk⟩ s'.2 hsx hE4 hEJ hEx (hN x hxmem).1
    (hN _ hsmem).1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small
