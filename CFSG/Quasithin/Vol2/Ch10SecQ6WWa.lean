module

public import CFSG.Quasithin.Vol2.Ch10SecQ6Aut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Aut
public import CFSG.Quasithin.Vol2.Ch10SecDL3
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1Restrict
public import CFSG.Quasithin.Background.B4L3Syl
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.H13.StatementsL1
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

open Matrix CFSG.Quasithin CFSG.ComponentClassification

local notation "σ₃" => CatalogueBGraphForm.slGraphAut 3 (ZMod 2)

set_option synthInstance.maxSize 2000 in
theorem invol_sym : ∀ C g : L3.Γ, (C : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = C → g * g = 1 →
    g ≠ 1 → (g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ * C = C * g →
      ∀ h : L3.Γ, h * h = 1 → h ≠ 1 → g * h = h * g →
      (h : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ * C = C * h → g = h := by
  decide +kernel

theorem card_le_two_of {G : Type*} [Group G] {H : Subgroup G}
    (h : ∀ a ∈ H, ∀ b ∈ H, a ≠ 1 → b ≠ 1 → a = b) : Nat.card H ≤ 2 := by
  classical
  have hinj : Function.Injective fun x : H => decide ((x : G) = 1) := by
    intro x y hxy
    simp only [decide_eq_decide] at hxy
    by_cases hx : (x : G) = 1
    · exact Subtype.ext (hx.trans (hxy.mp hx).symm)
    · exact Subtype.ext (h _ x.2 _ y.2 hx fun hy => hx (hxy.mpr hy))
  calc Nat.card H ≤ Nat.card Bool := Nat.card_le_card_of_injective _ hinj
    _ = 2 := by simp

theorem conj_injective_three : Function.Injective (MulAut.conj : L3.Γ →* MulAut L3.Γ) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have hc : g ∈ Subgroup.center L3.Γ := by
    rw [Subgroup.mem_center_iff]
    intro h
    have h1 := congrArg (fun α : MulAut L3.Γ => α h) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc h * g = g * h * g⁻¹ * g := by rw [h1]
      _ = g * h := by group
  rw [center_sl_zmod_two_eq_bot, Subgroup.mem_bot] at hc
  rw [hc, Subgroup.mem_bot]

@[expose] def slOf (A : GL (Fin 3) (ZMod 2)) : L3.Γ := ⟨A, det_eq_one A⟩

theorem slConj_eq_conj (A : GL (Fin 3) (ZMod 2)) :
    CatalogueBHigherLinearAction.slConjugation 3 (ZMod 2) A = MulAut.conj (slOf A) := by
  have hA : Matrix.SpecialLinearGroup.toGL (slOf A) = A := Units.ext rfl
  refine MulEquiv.ext fun g => Matrix.SpecialLinearGroup.toGL_injective ?_
  rw [CatalogueBHigherLinearAction.toGL_slConjugation, MulAut.conj_apply, map_mul, map_mul,
    map_inv, hA]

theorem mul_conj_mul_inv {G : Type*} [Group G] (φ : MulAut G) (g : G) :
    φ * MulAut.conj g * φ⁻¹ = MulAut.conj (φ g) := by
  refine MulEquiv.ext fun h => ?_
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem graph_mul_self : σ₃ * σ₃ = 1 :=
  MulEquiv.ext fun g => (σ₃).symm_apply_apply g

theorem P0_not_comm' : ∃ x ∈ L3.P0, ∃ y ∈ L3.P0, x * y ≠ y * x :=
  ⟨⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩, ⟨by decide, by decide, by decide⟩,
    ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide⟩, ⟨by decide, by decide, by decide⟩, by decide⟩

theorem card_le_four_sl3 {P : Subgroup L3.Γ} (hP : IsPGroup 2 P)
    (hc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) : Nat.card P ≤ 4 := by
  obtain ⟨e, he⟩ := (IsPGroup.iff_card).mp hP
  have hdvd : 2 ^ e ∣ 168 := by
    rw [← he, ← L3.card_Γ]
    exact Subgroup.card_subgroup_dvd_card P
  have he3 : e ≤ 3 := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ 4 ∣ 168 := (pow_dvd_pow 2 hlt).trans hdvd
    norm_num at this
  rcases (by omega : e ≤ 2 ∨ e = 3) with h2 | rfl
  · rw [he]
    calc 2 ^ e ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h2
      _ = 4 := by norm_num
  · exfalso
    obtain ⟨g, hg⟩ := L3.exists_conj_eq_P0 (by rw [he]; norm_num : Nat.card P = 8)
    obtain ⟨x, hx, y, hy, hxy⟩ := P0_not_comm'
    have hx' : (MulAut.conj g) x ∈ P := hg ▸ Subgroup.mem_map_of_mem _ hx
    have hy' : (MulAut.conj g) y ∈ P := hg ▸ Subgroup.mem_map_of_mem _ hy
    apply hxy
    apply (MulAut.conj g).injective
    rw [map_mul, map_mul]
    exact hc _ hx' _ hy'

theorem card_le_four_aut {A : Subgroup (MulAut L3.Γ)} (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (h2 : ∀ a ∈ A, a * a = 1) : Nat.card A ≤ 4 := by
  have hconj : ∀ g : L3.Γ, MulAut.conj g ∈ A → g * g = 1 := fun g hg =>
    conj_injective_three (by rw [map_mul, map_one]; exact h2 _ hg)
  by_cases hAI : A ≤ (MulAut.conj : L3.Γ →* MulAut L3.Γ).range
  · rw [← Subgroup.map_comap_eq_self hAI, Subgroup.card_map_of_injective conj_injective_three]
    refine card_le_four_sl3 (fun g => ⟨1, Subtype.ext ?_⟩) fun a ha b hb =>
      conj_injective_three ?_
    · rw [pow_one, Subgroup.coe_pow, sq]
      exact hconj _ g.2
    · rw [map_mul, map_mul]
      exact hc _ ha _ hb
  obtain ⟨τ, hτA, hτI⟩ := Set.not_subset.mp hAI
  rcases CFSG.QuasithinUnique.Setup.Family.aut_SL3_cases τ with ⟨B, hB⟩ | ⟨B, hB⟩
  · exact absurd ⟨_, (slConj_eq_conj B).symm.trans hB.symm⟩ hτI
  have hτ : τ = MulAut.conj (slOf B) * σ₃ := by rw [hB, slConj_eq_conj]
  have hσb : σ₃ (slOf B) = (slOf B)⁻¹ := by
    have h1 : MulAut.conj (slOf B * σ₃ (slOf B)) = 1 :=
      calc MulAut.conj (slOf B * σ₃ (slOf B))
          = MulAut.conj (slOf B) * (σ₃ * MulAut.conj (slOf B) * (σ₃)⁻¹) := by
            rw [mul_conj_mul_inv, map_mul]
        _ = MulAut.conj (slOf B) * σ₃ * (MulAut.conj (slOf B) * σ₃) * (σ₃ * σ₃)⁻¹ := by group
        _ = 1 := by rw [← hτ, h2 τ hτA, graph_mul_self, inv_one, mul_one]
    exact eq_inv_of_mul_eq_one_right (conj_injective_three (by rw [h1, map_one]))
  have hCsym : (((slOf B)⁻¹ : L3.Γ) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = ((slOf B)⁻¹ : L3.Γ) :=
    congrArg (fun x : L3.Γ => (x : Matrix (Fin 3) (Fin 3) (ZMod 2))) hσb
  have hcond : ∀ g : L3.Γ, MulAut.conj g ∈ A → (g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *
      ((slOf B)⁻¹ : L3.Γ) = (((slOf B)⁻¹ : L3.Γ) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * g := by
    intro g hg
    have h1 : τ g = g := by
      have h3 : τ * MulAut.conj g * τ⁻¹ = MulAut.conj g := by
        rw [hc τ hτA _ hg, mul_inv_cancel_right]
      rw [mul_conj_mul_inv] at h3
      exact conj_injective_three h3
    rw [hτ, MulAut.mul_apply, MulAut.conj_apply] at h1
    have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right (hconj g hg)
    have h3 : σ₃ g * (slOf B)⁻¹ = (slOf B)⁻¹ * g :=
      calc σ₃ g * (slOf B)⁻¹ = (slOf B)⁻¹ * (slOf B * σ₃ g * (slOf B)⁻¹) := by group
        _ = (slOf B)⁻¹ * g := by rw [h1]
    have h4 := congrArg (fun x : L3.Γ => (x : Matrix (Fin 3) (Fin 3) (ZMod 2))) h3
    simp only [Matrix.SpecialLinearGroup.coe_mul,
      CatalogueBGraphForm.slGraphAut_matrix, hginv] at h4
    exact h4
  have hτα : ∀ α ∈ A, α ∉ (MulAut.conj : L3.Γ →* MulAut L3.Γ).range →
      α * τ ∈ (MulAut.conj : L3.Γ →* MulAut L3.Γ).range := by
    intro α hα hαI
    rcases CFSG.QuasithinUnique.Setup.Family.aut_SL3_cases α with ⟨C, hC⟩ | ⟨C, hC⟩
    · exact absurd ⟨_, (slConj_eq_conj C).symm.trans hC.symm⟩ hαI
    refine ⟨slOf C * σ₃ (slOf B), ?_⟩
    rw [hC, slConj_eq_conj, hτ, map_mul, ← mul_conj_mul_inv]
    calc MulAut.conj (slOf C) * (σ₃ * MulAut.conj (slOf B) * (σ₃)⁻¹)
        = MulAut.conj (slOf C) * σ₃ * (MulAut.conj (slOf B) * σ₃) * (σ₃ * σ₃)⁻¹ := by group
      _ = MulAut.conj (slOf C) * σ₃ * (MulAut.conj (slOf B) * σ₃) := by
        rw [graph_mul_self, inv_one, mul_one]
  have hS : Nat.card ↥(A ⊓ (MulAut.conj : L3.Γ →* MulAut L3.Γ).range) ≤ 2 := by
    refine card_le_two_of fun α hα β hβ hα1 hβ1 => ?_
    obtain ⟨hαA, g, rfl⟩ := Subgroup.mem_inf.mp hα
    obtain ⟨hβA, h, rfl⟩ := Subgroup.mem_inf.mp hβ
    have hg1 : g ≠ 1 := fun h' => hα1 (by rw [h', map_one])
    have hh1 : h ≠ 1 := fun h' => hβ1 (by rw [h', map_one])
    have hgh : g * h = h * g :=
      conj_injective_three (by rw [map_mul, map_mul]; exact hc _ hαA _ hβA)
    rw [invol_sym _ g hCsym (hconj g hαA) hg1 (hcond g hαA) h (hconj h hβA) hh1 hgh
      (hcond h hβA)]
  classical
  let f : A → ↥(A ⊓ (MulAut.conj : L3.Γ →* MulAut L3.Γ).range) ⊕
      ↥(A ⊓ (MulAut.conj : L3.Γ →* MulAut L3.Γ).range) := fun α =>
    if h : (α : MulAut L3.Γ) ∈ (MulAut.conj : L3.Γ →* MulAut L3.Γ).range then
      Sum.inl ⟨α, Subgroup.mem_inf.mpr ⟨α.2, h⟩⟩
    else Sum.inr ⟨α * τ, Subgroup.mem_inf.mpr ⟨A.mul_mem α.2 hτA, hτα α α.2 h⟩⟩
  have hf : Function.Injective f := by
    intro α β hαβ
    simp only [f] at hαβ
    split_ifs at hαβ
    · have h3 := congrArg Subtype.val (Sum.inl.inj hαβ)
      exact Subtype.ext h3
    · have h3 := congrArg Subtype.val (Sum.inr.inj hαβ)
      exact Subtype.ext (mul_right_cancel h3)
  have : Finite (MulAut L3.Γ) :=
    Finite.of_injective (fun α : MulAut L3.Γ => (α : L3.Γ → L3.Γ)) fun α β h =>
      MulEquiv.ext (congrFun h)
  calc Nat.card A ≤ Nat.card (↥(A ⊓ (MulAut.conj : L3.Γ →* MulAut L3.Γ).range) ⊕
        ↥(A ⊓ (MulAut.conj : L3.Γ →* MulAut L3.Γ).range)) := Nat.card_le_card_of_injective f hf
    _ ≤ 4 := by
      rw [Nat.card_sum]
      omega

end C10P06

end CFSG.Quasithin.Vol2.Ch10.SecD
