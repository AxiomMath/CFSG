module

public import CFSG.LocalAnalysis.WeakClosure81.W183Br4Good
public import CFSG.LocalAnalysis.WeakClosure81.W183Br4NS
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Three
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Groups

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open Subgroup
open scoped MatrixGroups

theorem br4_false_case_one {Y S : Type} [Group Y] [Finite Y]
    [Group S] {A₁ A₂ : Subgroup S} (h : Br4TwoSimple S A₁ A₂) (g₁ : Br4Good ↥A₁)
    (g₂ : Br4Good ↥A₂) (θ : Y →* S) (hθ : Function.Surjective θ) (hQ : IsPGroup 3 θ.ker)
    (hperf : Group.IsPerfect Y) (hr : CFSG.pRank 3 Y ≤ 3)
    (hC : Subgroup.centralizer (θ.ker : Set Y) ≤ θ.ker) : False := by
  haveI : Finite S := Finite.of_surjective θ hθ
  have hker_le : θ.ker ≤ pCore 3 Y :=
    le_sSup ⟨MonoidHom.normal_ker θ, hQ⟩
  have hpCore_le : pCore 3 Y ≤ θ.ker := by
    have hnormal : ((pCore 3 Y).map θ).Normal := Subgroup.Normal.map pCore_normal θ hθ
    have hpgroup : IsPGroup 3 ↥((pCore 3 Y).map θ) := pCore_isPGroup.map θ
    exact (Subgroup.map_eq_bot_iff (pCore 3 Y)).mp (h.eq_bot_of_isPGroup hnormal hpgroup)
  have hpCore_eq : pCore 3 Y = θ.ker := le_antisymm hpCore_le hker_le
  have hne_top : pCore 3 Y ≠ ⊤ := by
    intro htop
    have hkertop : θ.ker = ⊤ := by rw [← hpCore_eq]; exact htop
    haveI : Subsingleton S := by
      refine ⟨fun x y => ?_⟩
      obtain ⟨a, rfl⟩ := hθ x
      obtain ⟨b, rfl⟩ := hθ y
      have ha : θ a = 1 := MonoidHom.mem_ker.mp (hkertop ▸ Subgroup.mem_top a)
      have hb : θ b = 1 := MonoidHom.mem_ker.mp (hkertop ▸ Subgroup.mem_top b)
      rw [ha, hb]
    obtain ⟨a, ha, b, hb, hab⟩ := h.nonab₁
    exact hab (Subsingleton.elim (a * b) (b * a))
  have hC' : Subgroup.centralizer (pCore 3 Y : Set Y) ≤ pCore 3 Y := by
    rw [hpCore_eq]; exact hC
  have hcases : Nonempty (Y ⧸ pCore 3 Y ≃* SL(3, ZMod 3)) ∨
      Nonempty (Y ⧸ pCore 3 Y ≃* SL(2, ZMod 5)) :=
    CFSG.RankThree.PartTwo.Sec4.Census.primeThreeLinear (Y := Y) hperf hC' hr hne_top
  obtain ⟨E₁, hE₁, hc₁⟩ := g₁.2.1
  obtain ⟨E₂, hE₂, hc₂⟩ := g₂.2.1
  have hF₁ : IsElemAbelian 3 (E₁.map A₁.subtype) := hE₁.map A₁.subtype
  have hF₂ : IsElemAbelian 3 (E₂.map A₂.subtype) := hE₂.map A₂.subtype
  have hcard₁ : Nat.card ↥(E₁.map A₁.subtype) = 9 := by
    rw [Subgroup.card_map_of_injective A₁.subtype_injective, hc₁]
  have hcard₂ : Nat.card ↥(E₂.map A₂.subtype) = 9 := by
    rw [Subgroup.card_map_of_injective A₂.subtype_injective, hc₂]
  have hcomm : ∀ a ∈ E₁.map A₁.subtype, ∀ b ∈ E₂.map A₂.subtype, a * b = b * a := by
    rintro a ⟨x, -, rfl⟩ b ⟨y, -, rfl⟩
    exact h.commute x.2 y.2
  have hdisj : E₁.map A₁.subtype ⊓ E₂.map A₂.subtype = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxinf : x ∈ A₁ ⊓ A₂ :=
      ⟨Subgroup.map_subtype_le E₁ hx.1, Subgroup.map_subtype_le E₂ hx.2⟩
    rwa [h.disj] at hxinf
  have hsup := br4_elem_sup hcomm hdisj hF₁ hF₂ hcard₁ hcard₂
  have hdvd : 81 ∣ Nat.card S := by
    have := Subgroup.card_subgroup_dvd_card (E₁.map A₁.subtype ⊔ E₂.map A₂.subtype)
    rwa [hsup.2] at this
  have hcardS : Nat.card S = Nat.card (Y ⧸ pCore 3 Y) := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ hθ).toEquiv]
    exact Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hpCore_eq.symm).toEquiv
  rcases hcases with hcase | hcase
  · obtain ⟨e⟩ := hcase
    have hcard' : Nat.card (Y ⧸ pCore 3 Y) = 5616 := by
      rw [Nat.card_congr e.toEquiv, CFSG.RankThree.PartTwo.Sec4.Census.card_SL3_three]
    rw [hcardS, hcard'] at hdvd
    norm_num at hdvd
  · obtain ⟨e⟩ := hcase
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hcard' : Nat.card (Y ⧸ pCore 3 Y) = 120 := by
      rw [Nat.card_congr e.toEquiv,
        CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, Nat.card_zmod]
      norm_num
    rw [hcardS, hcard'] at hdvd
    norm_num at hdvd

end CFSG.LocalAnalysis.WeakClosure81

end
