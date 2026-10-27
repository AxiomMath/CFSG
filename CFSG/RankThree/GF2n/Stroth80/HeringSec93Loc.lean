module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Dict
public import CFSG.RankThree.GF2n.Stroth80.HeringSec91CentreA

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem exists_elation91 (h34 : Stroth34Statement) {n : ℕ} {C B₁ A₁ : Subgroup G}
    (hcC : Ctx M Q Z C) (hcB : Ctx M Q Z B₁) (hcA : Ctx M Q Z A₁)
    (hw : Width Q Z n) (hn : 2 < n) (hnoC : NoA2 Q Z (LB M Q C)) (hgenC : GenByB M Q C)
    (hB₁C : B₁ ≤ QB C) (hA₁C : A₁ ≤ QB C) {a₀ : G} (ha₀ : a₀ ∈ A₁)
    (hind : a₀ ∉ B₁ ⊔ C ⊔ Z) :
    ∃ l ∈ LB M Q C, (∀ b ∈ B₁, ⁅l, b⁆ ∈ Z) ∧
      ∃ c₁ ∈ C, c₁ ∉ Z ∧ (a₀ * c₁)⁻¹ * (l * a₀ * l⁻¹) ∈ Z := by
  classical
  have hcard := stroth_3_5 h34 hcC hw hn hnoC hgenC
  obtain ⟨nn, γ, M₀, -, h⟩ := stroth_globalModelDataGF hcC.hyp
  haveI : Finite M₀.E := Module.finite_of_finite (GaloisField 2 nn)
  obtain ⟨bC, hbC0, -, hBC, -, -⟩ := hcC.dictB h
  obtain ⟨bB, hbB0, -, hBB, -, -⟩ := hcB.dictB h
  obtain ⟨bA, hbA0, -, hBA, -, -⟩ := hcA.dictB h
  obtain ⟨φ₀, hφπ, -, -⟩ := exists_actionHom_H0 hcC.hyp h
  have hZQ : Z ≤ Q := hcC.Z_le_Q
  have hCQ : C ≤ Q := hcC.le
  have hB₁Q : B₁ ≤ Q := hcB.le
  have hA₁Q : A₁ ≤ Q := hcA.le
  have ha₀Q : a₀ ∈ Q := hA₁Q ha₀
  let S : Submodule (GaloisField 2 nn) M₀.E :=
    Submodule.span _ {bB} ⊔ Submodule.span _ {M₀.π a₀} ⊔ Submodule.span _ {bC}
  let Y : Subgroup G := preSub M₀ S.toAddSubgroup
  have hSmem : ∀ x ∈ Q, M₀.π x ∈ S →
      ∃ β ∈ B₁, ∃ α ∈ A₁, ∃ γ' ∈ C, x⁻¹ * (β * α * γ') ∈ Z := by
    intro x hxQ hxS
    obtain ⟨y₁, hy₁, y₃, hy₃, hsum⟩ := Submodule.mem_sup.mp hxS
    obtain ⟨z₁, hz₁, z₂, hz₂, hsum'⟩ := Submodule.mem_sup.mp hy₁
    obtain ⟨s₁, rfl⟩ := Submodule.mem_span_singleton.mp hz₁
    obtain ⟨s₂, rfl⟩ := Submodule.mem_span_singleton.mp hz₂
    obtain ⟨s₃, rfl⟩ := Submodule.mem_span_singleton.mp hy₃
    have hz₁B : s₁ • bB ∈ M₀.img B₁ := (hBB _).mpr ⟨s₁, rfl⟩
    obtain ⟨t, ht⟩ := (hBA _).mp (M₀.pi_mem_img ha₀ ha₀Q)
    have hz₂A : s₂ • M₀.π a₀ ∈ M₀.img A₁ := (hBA _).mpr ⟨s₂ * t, by rw [ht, smul_smul]⟩
    have hz₃C : s₃ • bC ∈ M₀.img C := (hBC _).mpr ⟨s₃, rfl⟩
    obtain ⟨β, hβB, hβQ, hβπ⟩ := hz₁B
    obtain ⟨α, hαA, hαQ, hαπ⟩ := hz₂A
    obtain ⟨γ', hγC, hγQ, hγπ⟩ := hz₃C
    refine ⟨β, hβB, α, hαA, γ', hγC, ?_⟩
    rw [← M₀.pi_eq_iff hxQ (Q.mul_mem (Q.mul_mem hβQ hαQ) hγQ),
      M₀.π_mul _ (Q.mul_mem hβQ hαQ) _ hγQ, M₀.π_mul _ hβQ _ hαQ, hβπ, hαπ, hγπ, ← hsum,
      ← hsum']
  have hYimg : M₀.img Y = S.toAddSubgroup := img_preSub M₀ S.toAddSubgroup
  have hY : ∀ (c : GaloisField 2 nn) (e : M₀.E), e ∈ M₀.img Y → c • e ∈ M₀.img Y := by
    intro c e he
    rw [hYimg] at he ⊢
    exact S.smul_mem c he
  have hbBS : bB ∈ S :=
    Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_span_singleton_self bB))
  have hbCS : bC ∈ S := Submodule.mem_sup_right (Submodule.mem_span_singleton_self bC)
  have hπaS : M₀.π a₀ ∈ S :=
    Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  have hCY : C ≤ Y := by
    intro x hx
    refine ⟨hCQ hx, ?_⟩
    obtain ⟨s, hs⟩ := (hBC _).mp (M₀.pi_mem_img hx (hCQ hx))
    show M₀.π x ∈ S
    rw [hs]
    exact S.smul_mem s hbCS
  have hYL : Y ≤ Q ⊓ QB C := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    obtain ⟨β, hβB, α, hαA, γ', hγC, hz⟩ := hSmem x hx.1 hx.2
    have hy : β * α * γ' ∈ QB C :=
      (QB C).mul_mem ((QB C).mul_mem (hB₁C hβB) (hA₁C hαA)) (hcC.B_le_QB hγC)
    have hz' : (β * α * γ')⁻¹ * x ∈ Z := by
      have := Z.inv_mem hz
      simpa using this
    have e : x = (β * α * γ') * ((β * α * γ')⁻¹ * x) := by group
    rw [e]
    exact (QB C).mul_mem hy (hcC.Z_le_QB.1 hz')
  obtain ⟨b₂, hb₂Y, hb₂0, hB₂, hel3, hel4, -⟩ := hcC.elation_package hw hn hnoC hcard.2.2.1
    hcard.2.2.2 h (Y := Y) hCY hYL hY
  have hWmem : ∀ e : M₀.E, e ∈ S → e ∈ imgSub M₀ Y hY := fun e he => by
    rw [mem_imgSub, hYimg]
    exact he
  let vB : ↥(imgSub M₀ Y hY) := ⟨bB, hWmem _ hbBS⟩
  let vC : ↥(imgSub M₀ Y hY) := ⟨b₂, hb₂Y⟩
  let x₀ : ↥(imgSub M₀ Y hY) := ⟨M₀.π a₀, hWmem _ hπaS⟩
  have hx₀ : x₀ ∉ Submodule.span (GaloisField 2 nn) {vB, vC} := by
    intro hmem
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hmem
    have hab' : a • bB + b • b₂ = M₀.π a₀ := congrArg Subtype.val hab
    have hz₁B : a • bB ∈ M₀.img B₁ := (hBB _).mpr ⟨a, rfl⟩
    have hz₃C : b • b₂ ∈ M₀.img C := (hB₂ _).mpr ⟨b, rfl⟩
    obtain ⟨β, hβB, hβQ, hβπ⟩ := hz₁B
    obtain ⟨γ', hγC, hγQ, hγπ⟩ := hz₃C
    apply hind
    have hπ : M₀.π a₀ = M₀.π (β * γ') := by
      rw [M₀.π_mul _ hβQ _ hγQ, hβπ, hγπ, hab']
    have hz := (M₀.pi_eq_iff ha₀Q (Q.mul_mem hβQ hγQ)).mp hπ
    have hz' : (β * γ')⁻¹ * a₀ ∈ Z := by simpa using Z.inv_mem hz
    have e : a₀ = (β * γ') * ((β * γ')⁻¹ * a₀) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left hβB))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right hγC))) (Subgroup.mem_sup_right hz')
  obtain ⟨f, hfx, hfp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx₀ inferInstance
  let f₂ : Module.Dual (GaloisField 2 nn) ↥(imgSub M₀ Y hY) := (f x₀)⁻¹ • f
  have hf₂x : f₂ x₀ = 1 := by
    simp only [f₂, LinearMap.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hfx
  have hf₂B : f₂ vB = 0 := by
    have h1 : f vB ∈ (Submodule.span (GaloisField 2 nn) {vB, vC}).map f :=
      Submodule.mem_map_of_mem (Submodule.subset_span (by simp))
    rw [hfp, Submodule.mem_bot] at h1
    simp only [f₂, LinearMap.smul_apply, smul_eq_mul, h1, mul_zero]
  have hf₂C : f₂ vC = 0 := by
    have h1 : f vC ∈ (Submodule.span (GaloisField 2 nn) {vB, vC}).map f :=
      Submodule.mem_map_of_mem (Submodule.subset_span (by simp))
    rw [hfp, Submodule.mem_bot] at h1
    simp only [f₂, LinearMap.smul_apply, smul_eq_mul, h1, mul_zero]
  obtain ⟨l, hl, hlS⟩ := hel4 f₂ hf₂C
  have hlM : l ∈ M := hcC.LB_le_M hl
  have hlH : l ∈ H0 M Z := hcC.LB_le_H0 hl
  have hS' : ∀ x ∈ Q, M₀.π (l * x * l⁻¹) = (φ₀ ⟨l, hlH⟩) (M₀.π x) :=
    fun x hx => hφπ ⟨l, hlH⟩ x hx
  have hact := hlS (φ₀ ⟨l, hlH⟩) hS'
  refine ⟨l, hl, ?_, ?_⟩
  · intro b hb
    have hbQ := hB₁Q hb
    obtain ⟨s, hs⟩ := (hBB _).mp (M₀.pi_mem_img hb hbQ)
    have hyW : M₀.π b ∈ imgSub M₀ Y hY := hWmem _ (by rw [hs]; exact S.smul_mem s hbBS)
    have hy := hact ⟨M₀.π b, hyW⟩
    have hyv : (⟨M₀.π b, hyW⟩ : ↥(imgSub M₀ Y hY)) = s • vB := Subtype.ext (by simp [vB, hs])
    have hf0 : f₂ ⟨M₀.π b, hyW⟩ = 0 := by rw [hyv, map_smul, hf₂B, smul_zero]
    rw [hf0, zero_smul, add_zero] at hy
    have hπ : M₀.π (l * b * l⁻¹) = M₀.π b := by rw [hS' b hbQ]; exact hy
    have hlbQ : l * b * l⁻¹ ∈ Q := conj_mem_Q91 hcC hlM hbQ
    have hz := (M₀.pi_eq_iff hlbQ hbQ).mp hπ
    have e : ⁅l, b⁆ = (l * b * l⁻¹) * ((l * b * l⁻¹)⁻¹ * b)⁻¹ * (l * b * l⁻¹)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e, hcC.conj_Z_of_mem_Q hlbQ (Z.inv_mem hz)]
    exact Z.inv_mem hz
  · obtain ⟨c₁, hc₁C, hc₁Q, hc₁π⟩ : b₂ ∈ M₀.img C := (hB₂ b₂).mpr ⟨1, (one_smul _ b₂).symm⟩
    refine ⟨c₁, hc₁C, ?_, ?_⟩
    · intro hz
      apply hb₂0
      rw [← hc₁π]
      exact (M₀.π_ker c₁ hc₁Q).mpr hz
    · have hy := hact x₀
      rw [hf₂x, one_smul] at hy
      have hπ : M₀.π (l * a₀ * l⁻¹) = M₀.π a₀ + b₂ := by rw [hS' a₀ ha₀Q]; exact hy
      have hπ' : M₀.π (a₀ * c₁) = M₀.π (l * a₀ * l⁻¹) := by
        rw [M₀.π_mul _ ha₀Q _ hc₁Q, hπ, hc₁π]
      exact (M₀.pi_eq_iff (Q.mul_mem ha₀Q hc₁Q) (conj_mem_Q91 hcC hlM ha₀Q)).mp hπ'

end HS9

end CFSG.RankThree.GF2n.Stroth80
