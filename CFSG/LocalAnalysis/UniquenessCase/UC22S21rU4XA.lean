module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4Exc
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rx
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214g
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.Adapters.LieModelSimple
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

section Generic

variable {Q : Type} [Group Q] [Finite Q]

theorem u4x_eq_one_of_comm {A B : Subgroup Q} (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hA : center ↥A = ⊥) {a b : Q} (ha : a ∈ A) (hb : b ∈ B)
    (h : ∀ x ∈ A, a * b * x = x * (a * b)) : a = 1 := by
  have hz : (⟨a, ha⟩ : ↥A) ∈ center ↥A := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    have h3 : a * (x : Q) * b = x * a * b := by
      calc a * (x : Q) * b = a * ((x : Q) * b) := mul_assoc _ _ _
        _ = a * (b * x) := by rw [hcomm x x.2 b hb]
        _ = a * b * x := (mul_assoc _ _ _).symm
        _ = x * (a * b) := h x x.2
        _ = x * a * b := (mul_assoc _ _ _).symm
    exact (mul_right_cancel h3).symm
  rw [hA, Subgroup.mem_bot] at hz
  simpa using congrArg Subtype.val hz

theorem u4x_eq_of_mul_eq {A B : Subgroup Q} (hAB : A ⊓ B = ⊥) {a a' b b' : Q} (ha : a ∈ A)
    (ha' : a' ∈ A) (hb : b ∈ B) (hb' : b' ∈ B) (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have h2 : a'⁻¹ * a ∈ A ⊓ B := ⟨A.mul_mem (A.inv_mem ha') ha, h1 ▸ B.mul_mem hb' (B.inv_mem hb)⟩
  rw [hAB, Subgroup.mem_bot, inv_mul_eq_one] at h2
  subst h2
  exact ⟨rfl, mul_left_cancel h⟩

theorem u4x_mem_sup {A B : Subgroup Q} (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) {x : Q}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  have hAB : A ≤ normalizer (B : Set Q) := fun a ha => by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hcomm a ha y hy, mul_inv_cancel_right]
      exact hy
    · intro hy
      have h' := hcomm a ha _ hy
      have h2 : a * y = a * (a * y * a⁻¹) := by
        calc a * y = a * y * a⁻¹ * a := by group
          _ = a * (a * y * a⁻¹) := h'.symm
      rw [← mul_left_cancel h2] at hy
      exact hy
  have hx' : x ∈ (A : Set Q) * (B : Set Q) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right A B hAB]
    exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hx'
  exact ⟨a, ha, b, hb, rfl⟩

theorem u4x_top_le_normalizer {H : Subgroup Q} (hN : H.Normal) : ⊤ ≤ normalizer (H : Set Q) :=
  fun g _ => Subgroup.mem_normalizer_iff.2 fun h =>
    ⟨fun hh => hN.conj_mem h hh g, fun hh => by simpa [mul_assoc] using hN.conj_mem _ hh g⁻¹⟩

theorem u4x_mem_of_mul_mem {p : ℕ} [Fact p.Prime] {A B S : Subgroup Q}
    (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) (hAB : A ⊓ B = ⊥)
    (hS : CFSG.ABGLocalTools.IsSylowOf p S ⊤) (hN : (A ⊔ B).Normal) {a b : Q} (ha : a ∈ A)
    (hb : b ∈ B) (habS : a * b ∈ S) : a ∈ S ∧ b ∈ S := by
  have hS' : CFSG.ABGLocalTools.IsSylowOf p (S ⊓ (A ⊔ B)) (A ⊔ B) :=
    hS.inf_of_le_normalizer le_top (u4x_top_le_normalizer hN)
  have hmem : a * b ∈ S ⊓ (A ⊔ B) :=
    ⟨habS, Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)⟩
  rw [uc22p22r_sylow_eq_sup hcomm hAB hS'] at hmem
  obtain ⟨a', ha', b', hb', hab'⟩ := u4x_mem_sup (A := S ⊓ (A ⊔ B) ⊓ A) (B := S ⊓ (A ⊔ B) ⊓ B)
    (fun x hx y hy => hcomm x hx.2 y hy.2) hmem
  obtain ⟨rfl, rfl⟩ := u4x_eq_of_mul_eq hAB ha ha'.2 hb hb'.2 hab'.symm
  exact ⟨ha'.1.1, hb'.1.1⟩

theorem u4x_inf_eq_bot {A B : Subgroup Q} (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hB : center ↥B = ⊥) : A ⊓ B = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hz : (⟨x, hx.2⟩ : ↥B) ∈ center ↥B := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hcomm x hx.1 y y.2).symm
  rw [hB, Subgroup.mem_bot] at hz
  rw [Subgroup.mem_bot]
  simpa using congrArg Subtype.val hz

theorem u4x_sup_inf_centralizer {F₀ F₁ : Subgroup Q} (hcomm : ∀ x ∈ F₀, ∀ y ∈ F₁, x * y = y * x)
    (h₀ : center ↥F₀ = ⊥) (h₁ : center ↥F₁ = ⊥) :
    (F₀ ⊔ F₁) ⊓ centralizer ((F₀ ⊔ F₁ : Subgroup Q) : Set Q) = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hz, hzc⟩
  obtain ⟨f₀, hf₀, f₁, hf₁, rfl⟩ := u4x_mem_sup hcomm hz
  have hc : ∀ x ∈ F₀ ⊔ F₁, f₀ * f₁ * x = x * (f₀ * f₁) := fun x hx =>
    ((Subgroup.mem_centralizer_iff.1 hzc) x hx).symm
  have h0 : f₀ = 1 := u4x_eq_one_of_comm hcomm h₀ hf₀ hf₁ fun x hx => hc x (mem_sup_left hx)
  have h1 : f₁ = 1 := by
    refine u4x_eq_one_of_comm (fun x hx y hy => (hcomm y hy x hx).symm) h₁ hf₁ hf₀ fun x hx => ?_
    rw [← hcomm f₀ hf₀ f₁ hf₁]
    exact hc x (mem_sup_right hx)
  rw [Subgroup.mem_bot, h0, h1, one_mul]

end Generic

theorem u4x_isSylowOf_barImage {M P : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hP : CFSG.ABGLocalTools.IsSylowOf p P M) :
    CFSG.ABGLocalTools.IsSylowOf p (barImage M P) ⊤ := by
  obtain ⟨-, hPp, hPidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hP
  refine CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨le_top, ?_, ?_⟩
  · exact hPp.comap_subtype.map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))
  · rw [Subgroup.relIndex_top_right]
    have hdvd : (barImage M P).index ∣ (P.subgroupOf M).index :=
      Subgroup.index_map_dvd (P.subgroupOf M) (QuotientGroup.mk'_surjective _)
    intro hd
    exact hPidx (hd.trans hdvd)

theorem u4x_barImage_sup {M L K : Subgroup G} (hLM : L ≤ M) (hKM : K ≤ M) :
    barImage M (L ⊔ K) = barImage M L ⊔ barImage M K := by
  simp only [barImage]
  rw [Subgroup.subgroupOf_sup hLM hKM, Subgroup.map_sup]

theorem u4x_barImage_normal {M X : Subgroup G} (hMX : M ≤ normalizer (X : Set G)) :
    (barImage M X).Normal := by
  refine ⟨fun y hy g => ?_⟩
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) g
  exact (Subgroup.mem_normalizer_iff.1 (uc22ine229_mk_mem_normalizer (L := X) (hMX m.2)) y).1 hy

theorem u4x_center_eq_bot {M L : Subgroup G} (hL : L ∈ calC M) {n : ℕ}
    (hS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) : center ↥(barImage M L) = ⊥ := by
  obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hL
  haveI : IsSimpleGroup (Bar2 L) := by
    rcases hS with h | h
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
    · exact CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 h
  rw [← uc22p2214_map_center e, uc22p21k_center_eq_bot hL.2.2, Subgroup.map_bot]

theorem u4x_bar_structure {M L K : Subgroup G} (hL : L ∈ calC M) (hK : K ∈ calC M) (hne : K ≠ L)
    (hset : conjSetOf M L = {L, K}) {n : ℕ} (hS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) :
    (∀ x ∈ barImage M L, ∀ y ∈ barImage M K, x * y = y * x) ∧
      barImage M L ⊓ barImage M K = ⊥ ∧ center ↥(barImage M L) = ⊥ ∧
      center ↥(barImage M K) = ⊥ ∧ barImage M (conjClosure M L) = barImage M L ⊔ barImage M K ∧
      (barImage M L ⊔ barImage M K).Normal ∧
      (barImage M L ⊔ barImage M K) ⊓
        centralizer ((barImage M L ⊔ barImage M K : Subgroup (Bar2 M)) : Set (Bar2 M)) = ⊥ := by
  have hcomm := uc22p22l_barImage_commute hL hK hne.symm
  have hKS := uc22s21ru4e_shape_conj (K := K) (by rw [hset]; simp) hS
  have h₀ := u4x_center_eq_bot hL hS
  have h₁ := u4x_center_eq_bot hK hKS
  have hX : barImage M (conjClosure M L) = barImage M L ⊔ barImage M K := by
    rw [(uc22s21ru4e_conjClosure_eq_sup_mul hset hL hK hne).1]
    exact u4x_barImage_sup hL.1.le hK.1.le
  have hN : (barImage M L ⊔ barImage M K).Normal := by
    rw [← hX]
    exact u4x_barImage_normal (uc22p22u_conjClosure_isProd le_rfl Subgroup.le_normalizer hL).2.1
  exact ⟨hcomm, u4x_inf_eq_bot hcomm h₁, h₀, h₁, hX, hN,
    u4x_sup_inf_centralizer hcomm h₀ h₁⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
