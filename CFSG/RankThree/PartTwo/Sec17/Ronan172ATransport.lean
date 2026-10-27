module

public import CFSG.RankThree.PartTwo.Sec17.Item176StepsProof172
public import CFSG.RankThree.PartTwo.Sec16.Item167Proof
import CFSG.RankThree.PartTwo.Sec17.Item17ParaS
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartOne.S12.Sec12FusSyl

public section

namespace CFSG.RankThree.PartTwo.Sec17.Ronan172A

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem exists_mul_eq_of_mem_normalizer {A B : Subgroup G}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hA3 : ∀ a ∈ A, a ^ 3 = 1) (hBA : B ≤ A)
    (hF3 : ∀ x ∈ Subgroup.centralizer (A : Set G), x ^ 3 = 1 → x ∈ A)
    (hW : ∀ w ∈ Subgroup.normalizer (A : Set G), w ∈ Subgroup.centralizer (B : Set G) →
      (∃ k : ℕ, w ^ 3 ^ k = 1) → w ∈ Subgroup.centralizer (A : Set G))
    {g : G} (hg : g ∈ Subgroup.normalizer (B : Set G)) :
    ∃ h ∈ Subgroup.centralizer (B : Set G), ∃ w ∈ Subgroup.normalizer (A : Set G),
      w ∈ Subgroup.normalizer (B : Set G) ∧ g = h * w := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer (B : Set G) with hC
  have hlecent : ∀ {E : Subgroup G}, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → B ≤ E → E ≤ C :=
    fun hEab hBE x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => hEab y (hBE hy) x hx
  have hAC : A ≤ C := hlecent hAab hBA
  have hAp : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hA3 x x.2)⟩
  obtain ⟨P, hP, hAP⟩ := Sec13.Item134SylowBarProof.exists_isSylowOf_le hAC hAp
  have hNC : P ⊓ Subgroup.normalizer (A : Set G) ≤ Subgroup.centralizer (A : Set G) := by
    rintro y ⟨hyP, hyN⟩
    obtain ⟨k, hk⟩ := hP.isPGroup ⟨y, hyP⟩
    exact hW y hyN (hP.le hyP) ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hPN : P ≤ Subgroup.normalizer (A : Set G) := by
    by_contra hPN
    have hEP : P ⊓ Subgroup.normalizer (A : Set G) ≤ P := inf_le_left
    have hne : P ⊓ Subgroup.normalizer (A : Set G) ≠ P := fun h => hPN (h ▸ inf_le_right)
    obtain ⟨y, hyP, hyE, hyN⟩ :=
      CFSG.RankThree.PartOne.Sec12Fus.exists_mem_normalizer_sdiff hEP hP.isPGroup hne
    apply hyE
    refine ⟨hyP, Proof176Steps.mem_normalizer_of_map_le ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    have hyaE : y * a * y⁻¹ ∈ P ⊓ Subgroup.normalizer (A : Set G) :=
      (Subgroup.mem_normalizer_iff.mp hyN a).mp ⟨hAP ha, Subgroup.le_normalizer ha⟩
    refine hF3 _ (hNC hyaE) ?_
    show (y * a * y⁻¹) ^ 3 = 1
    rw [conj_pow, hA3 a ha, mul_one, mul_inv_cancel]
  have hPC : P ≤ Subgroup.centralizer (A : Set G) := fun y hy => hNC ⟨hy, hPN hy⟩
  set A' := A.map (MulAut.conj g).toMonoidHom with hA'
  have hBg : B.map (MulAut.conj g).toMonoidHom = B := Late.map_conj_eq_of_mem_normalizer hg
  have hA'ab : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ by group, hAab x hx y hy]
    group
  have hBA' : B ≤ A' := by
    rw [← hBg]
    exact Subgroup.map_mono hBA
  have hA'C : A' ≤ C := hlecent hA'ab hBA'
  have hA'p : IsPGroup 3 A' := hAp.map _
  obtain ⟨Q, hQ, hA'Q⟩ := Sec13.Item134SylowBarProof.exists_isSylowOf_le hA'C hA'p
  obtain ⟨m, hmC, hQm⟩ := Sec13.Item134SylowBarProof.exists_conj_of_isSylowOf hP hQ
  have hle : A' ≤ A.map (MulAut.conj m).toMonoidHom := by
    intro x hx
    have hxQ : x ∈ Q := hA'Q hx
    rw [hQm] at hxQ
    obtain ⟨p, hpP, hpx⟩ := hxQ
    have hx3 : x ^ 3 = 1 := by
      obtain ⟨a, ha, rfl⟩ := hx
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [conj_pow, hA3 a ha, mul_one, mul_inv_cancel]
    have hpx' : x = m * p * m⁻¹ := by
      rw [← hpx]
      rfl
    have hp3 : p ^ 3 = 1 := by
      have : p = m⁻¹ * x * m := by rw [hpx']; group
      rw [this, show m⁻¹ * x * m = m⁻¹ * x * m⁻¹⁻¹ by rw [inv_inv], conj_pow, hx3, mul_one,
        mul_inv_cancel]
    exact ⟨p, hF3 p (hPC hpP) hp3, hpx⟩
  have heq : A' = A.map (MulAut.conj m).toMonoidHom :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [hA', Subgroup.card_map_of_injective (MulAut.conj m).injective,
        Subgroup.card_map_of_injective (MulAut.conj g).injective])
  have hmN : m ∈ Subgroup.normalizer (B : Set G) := Subgroup.centralizer_le_normalizer _ hmC
  refine ⟨m, hmC, m⁻¹ * g, ?_, mul_mem (inv_mem hmN) hg, by group⟩
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  show A.map (MulAut.conj (m⁻¹ * g)).toMonoidHom = A
  rw [← Late.map_conj_map_conj, ← hA', heq, Late.map_conj_map_conj, inv_mul_cancel,
    Late.map_conj_one]

omit [Finite G] in
theorem map_conj_oPrimeResidualOf (g : G) (X : Subgroup G) :
    (oPrimeResidualOf 3 X).map (MulAut.conj g).toMonoidHom =
      oPrimeResidualOf 3 (X.map (MulAut.conj g).toMonoidHom) := by
  rw [Sec14.oPrimeResidualOf_eq_closure, Sec14.oPrimeResidualOf_eq_closure,
    MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hx, k, hk⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, k, by rw [← map_pow, hk, map_one]⟩
  · rintro ⟨⟨x, hx, rfl⟩, k, hk⟩
    refine ⟨x, ⟨hx, k, ?_⟩, rfl⟩
    apply (MulAut.conj g).injective
    rw [map_pow, map_one]
    exact hk

theorem map_conj_xb172 {A : Subgroup G} {w : G} (hw : w ∈ Subgroup.normalizer (A : Set G))
    (b : G) : (xb172 A b).map (MulAut.conj w).toMonoidHom = xb172 A (w * b * w⁻¹) := by
  rw [xb172, xb172, Subgroup.map_sup, map_pPrimeCoreOf 3 (MulAut.conj w),
    map_conj_oPrimeResidualOf, Sec17.map_conj_delta hw, map_centralizer_singleton (MulAut.conj w) b]
  rfl

theorem le_normalizer_xb172 (h149 : Sec16.Item149S14) {A L : Subgroup G} {c : G}
    (hS : Sec14Std G A c L) {b : G} (hb : b ∈ A) (hb1 : b ≠ 1) :
    Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (xb172 A b : Set G) := by
  set Y := Subgroup.centralizer ({b} : Set G) with hY
  have hA : Late.IsE27 A := hS.isE27
  have hAY : A ≤ Y := fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  have hYs : Y ∈ scriptY A :=
    ⟨Sec14.centralizer_singleton_ne_top hS.isSimpleGroup hS.nonabelian hb1,
      hAY.trans Subgroup.le_normalizer⟩
  obtain ⟨h1, h2, -⟩ := h149 G A c L hS Y hYs
  rw [← h1] at h2
  have hRY : oPrimeResidualOf 3 (delta A (lB A) Y) ≤ Y :=
    (Subgroup.map_subtype_le _).trans (Sec14.delta_le Y)
  have hYR : Y ≤ Subgroup.normalizer (oPrimeResidualOf 3 (delta A (lB A) Y) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRY).mp h2
  exact Sec14.le_normalizer_sup (le_normalizer_pPrimeCoreOf 3 Y) hYR

end CFSG.RankThree.PartTwo.Sec17.Ronan172A
