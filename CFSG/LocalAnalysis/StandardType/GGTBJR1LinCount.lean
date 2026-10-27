module

public import CFSG.LocalAnalysis.StandardType.GGTBJCount
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSLComp
import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeTypeA
import CFSG.LocalAnalysis.StandardType.GGLinearFusionFrame
import CFSG.LocalAnalysis.StandardType.GGSixBstarUniqueToralA
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerTypeADvdModel
import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndDvd
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.SeitzReduction.LinearPilot

private theorem actsDiag_apply_eq_self_of_const_on_block {n : ℕ} {F : Type} [Field F]
    {G : Type} [Group G] {φ : SpecialLinearGroup (Fin (n + 1)) F →* G}
    {a : MulAut G} {t : Fin (n + 1) → F} (ha : TypeANbrDvd.ActsDiag φ a t)
    {I : Finset (Fin (n + 1))} (ht : ∀ i ∈ I, ∀ j ∈ I, t i = t j)
    {u : SpecialLinearGroup (Fin (n + 1)) F} (hu : u ∈ blockSpecialLinear I) :
    a (φ u) = φ u := by
  obtain ⟨D, hD, haD⟩ := ha
  let e : Fin (n + 1) → Fˣ := fun k => Units.mk0 (t k) (TypeA.diag_ne_zero hD k)
  have hD' : D = InnerDiagA.diagGL e := by
    apply Units.ext
    rw [hD, InnerDiagA.coe_diagGL]
    ext k
    rfl
  have he : ∀ i ∈ I, ∀ j ∈ I, e i = e j := by
    intro i hi j hj
    apply Units.ext
    rw [Units.val_mk0, Units.val_mk0, ht i hi j hj]
  rw [haD, hD', RootPlaneA.slConjugation_eq_conjSL,
    LinFusion.conjSL_diagGL_of_mem_blockSpecialLinear he hu]

private theorem mem_ggFixingJ_of_actsDiag_const_on_block {G : Type} [Group G]
    {L J : Subgroup G} {F : Type} [Field F] {n : ℕ}
    {φ : SpecialLinearGroup (Fin (n + 1)) F →* L}
    {A : Subgroup (MulAut ↥L)} {a : MulAut ↥L} (ha : a ∈ A)
    {t : Fin (n + 1) → F} (ht : TypeANbrDvd.ActsDiag φ a t)
    {S : Finset (Fin (n + 1))} (hconst : ∀ i ∈ S, ∀ j ∈ S, t i = t j)
    (hJ : J = (blockSpecialLinear (K := F) S).map (L.subtype.comp φ)) :
    a ∈ ggFixingJ L J A := by
  rw [ggFixingJ, Subgroup.mem_inf]
  refine ⟨ha, ?_⟩
  rw [Subgroup.mem_iInf]
  intro l
  rw [MulAction.mem_stabilizer_iff]
  have hmem : (l.1 : G) ∈ (blockSpecialLinear (K := F) S).map (L.subtype.comp φ) := by
    rw [← hJ]
    exact l.2
  obtain ⟨u, hu, hlu⟩ := Subgroup.mem_map.mp hmem
  have hfix := actsDiag_apply_eq_self_of_const_on_block ht hconst hu
  have hl : l.1 = φ u := Subtype.ext hlu.symm
  rw [hl]
  simpa using hfix

private theorem relIndex_ggFixingJ_le_of_card_two {G : Type} [Group G]
    {p : ℕ} (hp : p.Prime) {L J : Subgroup G} {F : Type} [Field F] [Finite F]
    {n : ℕ} {φ : SpecialLinearGroup (Fin (n + 1)) F →* L}
    (hker : ∀ g, φ g = 1 → g ∈ scalars (n + 1) F)
    {A : Subgroup (MulAut ↥L)} (hAp : ∀ a ∈ A, a ^ p = 1)
    (hdiag : ∀ a ∈ A, ∃ t : Fin (n + 1) → F, TypeANbrDvd.ActsDiag φ a t)
    {i j : Fin (n + 1)} (hij : i ≠ j)
    (hJ : J = (blockSpecialLinear (K := F) ({i, j} : Finset (Fin (n + 1)))).map
      (L.subtype.comp φ)) :
    (ggFixingJ L J A).relIndex A ≤ p := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  let t : A → Fin (n + 1) → F := fun a => (hdiag (a : MulAut ↥L) a.2).choose
  have ht : ∀ a : A, TypeANbrDvd.ActsDiag φ (a : MulAut ↥L) (t a) := fun a =>
    (hdiag (a : MulAut ↥L) a.2).choose_spec
  let χf : A → Fˣ := fun a =>
    Units.mk0 (t a i * (t a j)⁻¹)
      (mul_ne_zero (TypeANbrDvd.ActsDiag.ne_zero (ht a) i)
        (inv_ne_zero (TypeANbrDvd.ActsDiag.ne_zero (ht a) j)))
  have hχmul : ∀ a b : A, χf (a * b) = χf a * χf b := by
    intro a b
    apply Units.ext
    simp only [χf, Units.val_mk0, Units.val_mul]
    rw [(ht (a * b)).ratio hker ((ht a).mul (ht b)) hij, mul_inv]
    ring
  let χ : A →* Fˣ := MonoidHom.mk' χf hχmul
  have hrange : χ.range ≤ rootsOfUnity p F := by
    rintro _ ⟨a, rfl⟩
    rw [mem_rootsOfUnity]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    simpa [χ, χf] using (ht a).ratio_pow hker (hAp (a : MulAut ↥L) a.2) i j
  have hker_le : χ.ker ≤ (ggFixingJ L J A).subgroupOf A := by
    intro a ha
    rw [Subgroup.mem_subgroupOf]
    have h1 : t a i = t a j := by
      have h2 : t a i * (t a j)⁻¹ = 1 := by
        have h3 := congrArg (fun u : Fˣ => (u : F)) (MonoidHom.mem_ker.mp ha)
        simpa [χ, χf] using h3
      exact (mul_inv_eq_one₀ (TypeANbrDvd.ActsDiag.ne_zero (ht a) j)).mp h2
    refine mem_ggFixingJ_of_actsDiag_const_on_block a.2 (ht a) ?_ hJ
    intro k hk l hl
    rw [Finset.mem_insert, Finset.mem_singleton] at hk hl
    rcases hk with rfl | rfl <;> rcases hl with rfl | rfl
    exacts [rfl, h1, h1.symm, rfl]
  calc (ggFixingJ L J A).relIndex A = ((ggFixingJ L J A).subgroupOf A).index := rfl
    _ ≤ χ.ker.index := Subgroup.index_antitone hker_le
    _ = Nat.card χ.range := Subgroup.index_ker χ
    _ ≤ p := (Subgroup.card_le_of_le hrange).trans (card_rootsOfUnity F p)

theorem ggTBJR1Lin_three_le_card {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {L J : Subgroup G} {F : Type} [Field F] [Finite F] [CharP F 2] {d : ℕ}
    {φ : SpecialLinearGroup (Fin d) F →* L} (hker : ∀ g, φ g = 1 → g ∈ scalars d F)
    {A : Subgroup (MulAut ↥L)} (hAp : ∀ a ∈ A, a ^ p = 1)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → F, TypeANbrDvd.ActsDiag φ a t)
    {S : Finset (Fin d)} (hS2 : 2 ≤ S.card)
    (hJ : J = (blockSpecialLinear (K := F) S).map (L.subtype.comp φ))
    (hcount : p ^ 2 * Nat.card ↥(ggFixingJ L J A) ≤ Nat.card ↥A) : 3 ≤ S.card := by
  classical
  have hS2pos : 0 < S.card := lt_of_lt_of_le (by norm_num) hS2
  have hd0 : d ≠ 0 := by
    obtain ⟨x, -⟩ := Finset.card_pos.mp hS2pos
    rintro rfl
    exact Nat.not_lt_zero _ x.isLt
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd0
  by_contra hlt
  have hS : S.card = 2 := by omega
  obtain ⟨i, j, hij, hSij⟩ := Finset.card_eq_two.mp hS
  have hJ' : J = (blockSpecialLinear (K := F) ({i, j} : Finset (Fin (n + 1)))).map
      (L.subtype.comp φ) := by simpa [hSij] using hJ
  have hidx := relIndex_ggFixingJ_le_of_card_two hp hker hAp hdiag hij hJ'
  have hle : ggFixingJ L J A ≤ A := by rw [ggFixingJ]; exact inf_le_left
  have hcard : Nat.card ↥A = (ggFixingJ L J A).relIndex A *
      Nat.card ↥(ggFixingJ L J A) := by
    rw [← Subgroup.relIndex_mul_card (ggFixingJ L J A) A, inf_eq_left.mpr hle]
  have hpos : 0 < Nat.card ↥(ggFixingJ L J A) := Nat.card_pos
  have h2 : p ^ 2 ≤ p := by
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc p ^ 2 * Nat.card ↥(ggFixingJ L J A) ≤ Nat.card ↥A := hcount
      _ = (ggFixingJ L J A).relIndex A * Nat.card ↥(ggFixingJ L J A) := hcard
      _ ≤ p * Nat.card ↥(ggFixingJ L J A) := Nat.mul_le_mul_right _ hidx
  nlinarith [h2, hp.two_le]

end CFSG.StandardType

end
