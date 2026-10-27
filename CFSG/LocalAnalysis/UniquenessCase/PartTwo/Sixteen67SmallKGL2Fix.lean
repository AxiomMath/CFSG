module

public import CFSG.Quasithin.Background.F918Z4bAut
import CFSG.GH74.GLS.IVK.L2.FieldProj
import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Orders
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoPglFaithful
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L2Cent
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeL2OddGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo Subgroup

theorem s1667_kg_inf_centralizer_equiv {Q : Type} [Group Q] (J : Subgroup Q) {x : Q} (hx : x ∈ J) :
    Nonempty (↥(J ⊓ centralizer ({x} : Set Q)) ≃*
      ↥(centralizer ({(⟨x, hx⟩ : ↥J)} : Set ↥J))) := by
  have heq : (J ⊓ centralizer ({x} : Set Q)).subgroupOf J =
      centralizer ({(⟨x, hx⟩ : ↥J)} : Set ↥J) := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun hh => Subtype.ext hh.2, fun hh => ⟨y.2, congrArg Subtype.val hh⟩⟩
  exact ⟨(Subgroup.subgroupOfEquivOfLe inf_le_left).symm.trans (MulEquiv.subgroupCongr heq)⟩

theorem s1667_kgl2_ringChar_eq {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hcard : Nat.card F = p ^ f) : ringChar F = p := by
  letI : Fintype F := Fintype.ofFinite F
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP F p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  exact ringChar.eq F p

theorem s1667_kgl2_card_le_two_of_forall_eq {G : Type*} [Group G] [Finite G]
    (h : ∀ a b : G, a ≠ 1 → b ≠ 1 → a = b) : Nat.card G ≤ 2 := by
  by_cases hG : ∃ a : G, a ≠ 1
  · obtain ⟨a₀, ha₀⟩ := hG
    have hsurj : Function.Surjective (fun i : Fin 2 => if i = 0 then (1 : G) else a₀) := by
      intro b
      by_cases hb : b = 1
      · exact ⟨0, by simp [hb]⟩
      · exact ⟨1, by simp [h b a₀ hb ha₀]⟩
    calc Nat.card G ≤ Nat.card (Fin 2) := Nat.card_le_card_of_surjective _ hsurj
      _ = 2 := by simp
  · have hG' : ∀ a : G, a = 1 := fun a => by
      by_contra hne
      exact hG ⟨a, hne⟩
    have : Subsingleton G := ⟨fun a b => by rw [hG' a, hG' b]⟩
    exact (Finite.card_le_one_iff_subsingleton.mpr this).trans (by norm_num)

theorem s1667_kgl2_exists_pglAction {K : Type} [Field K] [Finite K] {x : PSL2 K}
    {α : MulAut (PSL2 K)} (hα2 : α * α = 1) (hαx : α x = x)
    (hφ : CFSG.Quasithin.autFieldPart K α = 1) :
    ∃ g : PGL2 K, pglAction K g = α ∧ g * g = 1 ∧
      g * Matrix.ProjectiveSpecialLinearGroup.toPGL x =
        Matrix.ProjectiveSpecialLinearGroup.toPGL x * g := by
  obtain ⟨g, hg⟩ := CFSG.Quasithin.mem_range_pglAction_of_autFieldPart_eq_one hφ
  refine ⟨g, hg, pglAction_injective K ?_, ?_⟩
  · rw [map_mul, hg, map_one]
    exact hα2
  · rw [← hg] at hαx
    have h2 := toPGL_pglAction K g x
    rw [hαx] at h2
    exact mul_inv_eq_iff_eq_mul.mp h2.symm

theorem s1667_kgl2_ker_card_le_two {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2)
    (hK3 : ringChar K ≠ 3) {x : PSL2 K} (hx : orderOf x = 3)
    (E : Subgroup (MulAut (PSL2 K))) (hE2 : ∀ α ∈ E, α * α = 1) (hEx : ∀ α ∈ E, α x = x) :
    Nat.card ↥(E ⊓ (CFSG.Quasithin.autFieldPart K).ker) ≤ 2 := by
  apply s1667_kgl2_card_le_two_of_forall_eq
  rintro ⟨a, haE, hak⟩ ⟨b, hbE, hbk⟩ hna hnb
  have hne : ∀ (c : MulAut (PSL2 K)) (hc : c ∈ E ⊓ (CFSG.Quasithin.autFieldPart K).ker)
      (g : PGL2 K), pglAction K g = c → (⟨c, hc⟩ : ↥(E ⊓ (CFSG.Quasithin.autFieldPart K).ker)) ≠ 1 →
      g ≠ 1 := by
    rintro c hc g hg hne rfl
    exact hne (Subtype.ext (hg.symm.trans (map_one _)))
  obtain ⟨g₁, hg₁, hg₁2, hg₁c⟩ := s1667_kgl2_exists_pglAction (hE2 a haE) (hEx a haE)
    (MonoidHom.mem_ker.mp hak)
  obtain ⟨g₂, hg₂, hg₂2, hg₂c⟩ := s1667_kgl2_exists_pglAction (hE2 b hbE) (hEx b hbE)
    (MonoidHom.mem_ker.mp hbk)
  have := CFSG.RankThree.PartTwo.Sec20.eq_of_commute_toPGL hK2 hK3 hx hg₁2
    (hne a ⟨haE, hak⟩ g₁ hg₁ hna) hg₁c hg₂2 (hne b ⟨hbE, hbk⟩ g₂ hg₂ hnb) hg₂c
  exact Subtype.ext (hg₁.symm.trans ((congrArg (pglAction K) this).trans hg₂))

theorem s1667_kgl2_exists_fieldPart_ne_one {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2)
    (hK3 : ringChar K ≠ 3) {x : PSL2 K} (hx : orderOf x = 3)
    (E : Subgroup (MulAut (PSL2 K))) (hE2 : ∀ α ∈ E, α * α = 1) (hEx : ∀ α ∈ E, α x = x)
    (hE4 : Nat.card E = 4) : ∃ α ∈ E, CFSG.Quasithin.autFieldPart K α ≠ 1 := by
  by_contra hcon
  have hle : E ≤ E ⊓ (CFSG.Quasithin.autFieldPart K).ker := by
    refine le_inf le_rfl fun α hα => ?_
    rw [MonoidHom.mem_ker]
    by_contra hne
    exact hcon ⟨α, hα, hne⟩
  have h1 := s1667_kgl2_ker_card_le_two hK2 hK3 hx E hE2 hEx
  have h2 : Nat.card E ≤ Nat.card ↥(E ⊓ (CFSG.Quasithin.autFieldPart K).ker) :=
    Subgroup.card_le_of_le hle
  omega

theorem s1667_kgl2_fixed_orderOf_le {F : Type} [Field F] [Finite F] {K : Type} [Group K]
    (e : K ≃* PSL2 F) {u : MulAut K} (hu : orderOf u = 2)
    (hfield : CFSG.Quasithin.autFieldPart F (MulAut.congr e u) ≠ 1) {y : K} (hy : u y = y) :
    ∃ s : ℕ, s ^ 2 = Nat.card F ∧ orderOf y ≤ s + 1 := by
  let e' : K ≃* CFSG.GH74.GLS.IVK.L2 F := e.trans (CFSG.GH74.GLS.IVK.L2.equivPSL F).symm
  have hto : CFSG.GH74.GLS.IVK.toPSL e' = e := by
    ext k
    simp [CFSG.GH74.GLS.IVK.toPSL, e']
  have hud : u ∉ CFSG.GH74.GLS.IVK.innDiagSub e' := by
    rw [CFSG.GH74.GLS.IVK.mem_innDiagSub_iff]
    intro h
    apply hfield
    have h1 : CFSG.GH74.GLS.IVK.fieldProj e' u =
        CFSG.Quasithin.autFieldPart F (MulAut.congr e u) := by
      rw [← hto]
      rfl
    rw [← h1]
    exact h
  obtain ⟨F₀, _, _, hF₀, ⟨ψ⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec20.L2OddGroup.isPGL2_fixedSubgroup_of_not_mem_innDiagSub e' hu hud
  refine ⟨Nat.card F₀, hF₀, ?_⟩
  have hyfix : y ∈ CFSG.GH74.GLS.fixedSubgroup K u := hy
  have h1 := CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.pgl2_orderOf_le F₀
    (ψ ⟨y, hyfix⟩)
  rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk] at h1
  exact h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small
