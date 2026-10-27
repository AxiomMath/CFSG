module

public import CFSG.RankThree.GF2n.Stroth80.Sec7ActOp
public import CFSG.RankThree.GF2n.Stroth80.Sec7SmithAlg

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

section

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {n : ℕ} {K : Type} [Field K] [Finite K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)} {b₀ : M₀.E}

theorem sec7_QBW_comm {C : Subgroup G} (hc' : Ctx M Q Z C) {V : Subgroup G}
    (hV : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) :
    ∀ x ∈ (QB C ⊓ Wt Q V) ⊔ V, ∀ y ∈ (QB C ⊓ Wt Q V) ⊔ V, x * y = y * x := by
  have hnorm : QB C ⊓ Wt Q V ≤ Subgroup.normalizer (V : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer _ ha.2.2
  intro x hx y hy
  obtain ⟨α, hα, c, hc1, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hnorm hx
  obtain ⟨α', hα', c', hc2, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hnorm hy
  have h1 : α * α' = α' * α :=
    congrArg Subtype.val (hc'.inf_QB_elemAbelian.1.is_comm.comm ⟨α, hα.2.1, hα.1⟩
      ⟨α', hα'.2.1, hα'.1⟩)
  have h2 : α * c' = c' * α := (Subgroup.mem_centralizer_iff.mp hα.2.2 c' hc2).symm
  have h3 : c * α' = α' * c := Subgroup.mem_centralizer_iff.mp hα'.2.2 c hc1
  have h4 : c * c' = c' * c := hV c hc1 c' hc2
  calc α * c * (α' * c') = α * (c * α') * c' := by simp only [mul_assoc]
    _ = α * (α' * c) * c' := by rw [h3]
    _ = (α * α') * (c * c') := by simp only [mul_assoc]
    _ = (α' * α) * (c' * c) := by rw [h1, h4]
    _ = α' * (α * c') * c := by simp only [mul_assoc]
    _ = α' * (c' * α) * c := by rw [h2]
    _ = α' * c' * (α * c) := by simp only [mul_assoc]

variable (hc : Ctx M Q Z B) (hS : IsTensorSetup hc n M₀ ρ b₀) (t : G)

@[expose] noncomputable def sec7Asub : Submodule K M₀.E where
  carrier := {e | e ∈ M₀.B.orthogonal (hc.VtSub hS.model t) ∧
    ∀ (l : G) (hl : l ∈ LB M Q B),
      sec7Op hc hS (hc.LB_le_H0 hl) e - e ∈ hc.VtSub hS.model t}
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨(M₀.B.orthogonal (hc.VtSub hS.model t)).add_mem ha1 hb1, fun l hl => ?_⟩
    have e : sec7Op hc hS (hc.LB_le_H0 hl) (a + b) - (a + b) =
        (sec7Op hc hS (hc.LB_le_H0 hl) a - a) + (sec7Op hc hS (hc.LB_le_H0 hl) b - b) := by
      rw [map_add]
      abel
    rw [e]
    exact (hc.VtSub hS.model t).add_mem (ha2 l hl) (hb2 l hl)
  zero_mem' := ⟨Submodule.zero_mem _, fun l hl => by
    rw [map_zero, sub_zero]
    exact Submodule.zero_mem _⟩
  smul_mem' := by
    rintro c a ⟨ha1, ha2⟩
    refine ⟨(M₀.B.orthogonal (hc.VtSub hS.model t)).smul_mem c ha1, fun l hl => ?_⟩
    have e : sec7Op hc hS (hc.LB_le_H0 hl) (c • a) - c • a =
        c • (sec7Op hc hS (hc.LB_le_H0 hl) a - a) := by
      rw [map_smul, smul_sub]
    rw [e]
    exact (hc.VtSub hS.model t).smul_mem c (ha2 l hl)

variable {hc hS t}

theorem sec7Asub_iff (hc : Ctx M Q Z B) (hS : IsTensorSetup hc n M₀ ρ b₀) {t : G}
    (ψ : M₀.E →ₗ[K] M₀.E)
    (hW : ∀ x ∈ Q, x ∈ Wt Q (Vt M (LB M Q B) B Z t) ↔ ψ (M₀.π x) = 0)
    {L₂ A₁ A₂ : Subgroup G}
    (hdec : IsOppDecomp (Wt Q (Vt M (LB M Q B) B Z t)) (Vt M (LB M Q B) B Z t) (LB M Q B) L₂
      A₁ A₂) {x : G} (hx : x ∈ Q) :
    M₀.π x ∈ sec7Asub hc hS t ↔ x ∈ A₁ := by
  obtain ⟨-, hA1P, -, -, -, -, -, -, hfix1, -⟩ := hdec
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hmem : ∀ y ∈ Q, M₀.π y ∈ hc.VtSub hS.model t ↔ y ∈ Vt M (LB M Q B) B Z t :=
    fun y hy => Tim79.QuadModel.mem_img_iff M₀ hZV hy
  constructor
  · rintro ⟨hperp, hl⟩
    have hxW : x ∈ Wt Q (Vt M (LB M Q B) B Z t) :=
      (sec7_mem_Wt_iff_perp hc hS ψ hW hx).mpr hperp
    refine (hfix1 x hxW).mpr fun l hl' => ?_
    have h1 := hl l hl'
    rw [sec7Op_sub_comm hc hS (hc.LB_le_H0 hl') hx] at h1
    exact (hmem _ (sec7_comm_mem_Q hc (hc.LB_le_M hl') hx)).mp h1
  · intro hxA
    have hxW : x ∈ Wt Q (Vt M (LB M Q B) B Z t) := hA1P hxA
    refine ⟨(sec7_mem_Wt_iff_perp hc hS ψ hW hx).mp hxW, fun l hl' => ?_⟩
    rw [sec7Op_sub_comm hc hS (hc.LB_le_H0 hl') hx]
    exact (hmem _ (sec7_comm_mem_Q hc (hc.LB_le_M hl') hx)).mpr
      ((hfix1 x hxW).mp hxA l hl')

theorem sec7Asub_lagr (hc : Ctx M Q Z B) (hS : IsTensorSetup hc n M₀ ρ b₀) {t : G}
    (ψ : M₀.E →ₗ[K] M₀.E)
    (hW : ∀ x ∈ Q, x ∈ Wt Q (Vt M (LB M Q B) B Z t) ↔ ψ (M₀.π x) = 0)
    {L₂ A₁ A₂ : Subgroup G}
    (hdec : IsOppDecomp (Wt Q (Vt M (LB M Q B) B Z t)) (Vt M (LB M Q B) B Z t) (LB M Q B) L₂
      A₁ A₂)
    (hcomm₁ : ∀ x ∈ A₁, ∀ y ∈ A₁, x * y = y * x) (hcomm₂ : ∀ x ∈ A₂, ∀ y ∈ A₂, x * y = y * x) :
    (hc.VtSub hS.model t ≤ sec7Asub hc hS t) ∧
      (∀ e ∈ sec7Asub hc hS t, ∀ e' ∈ sec7Asub hc hS t, M₀.B e e' = 0) ∧
      M₀.B.orthogonal (sec7Asub hc hS t) = sec7Asub hc hS t := by
  obtain ⟨hf, hr⟩ := sec7_model_form M₀
  have hdec' := hdec
  obtain ⟨hI1, hA1P, hI2, hA2P, hsup, -, hcomm, -, -, -⟩ := hdec
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hreg := hS.model.reg
  have hiso₁ : ∀ e ∈ sec7Asub hc hS t, ∀ e' ∈ sec7Asub hc hS t, M₀.B e e' = 0 := by
    intro e he e' he'
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
    obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj e'
    have hx := (sec7Asub_iff hc hS ψ hW hdec' hxQ).mp he
    have hy := (sec7Asub_iff hc hS ψ hW hdec' hyQ).mp he'
    exact (M₀.comm_iff_B hreg hxQ hyQ).mp (hcomm₁ x hx y hy)
  have hUA : hc.VtSub hS.model t ≤ sec7Asub hc hS t := by
    intro e he
    obtain ⟨v, hvV, hvQ, rfl⟩ := (hc.mem_VtSub hS.model t).mp he
    exact (sec7Asub_iff hc hS ψ hW hdec' hvQ).mpr (hI1 hvV)
  refine ⟨hUA, hiso₁, ?_⟩
  refine sec7_perp_eq_of_opp M₀.B hf hr (hc.VtSub hS.model t) (sec7Asub hc hS t)
    (M₀.img A₂ : Set M₀.E) hUA ?_ hiso₁ ?_
  · intro w hw
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj w
    have hxW : x ∈ Wt Q (Vt M (LB M Q B) B Z t) := (sec7_mem_Wt_iff_perp hc hS ψ hW hxQ).mpr hw
    have hxsup : x ∈ A₂ ⊔ A₁ := by
      rw [sup_comm, hsup]
      exact hxW
    have hnorm : A₂ ≤ Subgroup.normalizer (A₁ : Set G) := by
      intro a ha
      refine Subgroup.mem_normalizer_fintype fun y hy => ?_
      have h1 : a * y * a⁻¹ = ⁅a, y⁆ * y := by
        simp only [commutatorElement_def]
        group
      rw [h1]
      exact A₁.mul_mem (hI1 (hcomm a (hA2P ha) y (hA1P hy))) hy
    obtain ⟨a₂, ha₂, a₁, ha₁, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hnorm hxsup
    have ha₁Q : a₁ ∈ Q := hWQ (hA1P ha₁)
    have ha₂Q : a₂ ∈ Q := hWQ (hA2P ha₂)
    refine ⟨M₀.π a₁, (sec7Asub_iff hc hS ψ hW hdec' ha₁Q).mpr ha₁, M₀.π a₂,
      M₀.pi_mem_img ha₂ ha₂Q, ?_⟩
    rw [M₀.π_mul _ ha₂Q _ ha₁Q, add_comm]
  · rintro _ ⟨x, hx, hxQ, rfl⟩ _ ⟨y, hy, hyQ, rfl⟩
    exact (M₀.comm_iff_B hreg hxQ hyQ).mp (hcomm₂ x hx y hy)

end

section

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {n : ℕ} {K : Type} [Field K] [Finite K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)} {b₀ : M₀.E}
  (hc : Ctx M Q Z B) (hS : IsTensorSetup hc n M₀ ρ b₀) {t : G}

include hc hS

theorem sec7Asub_inv {m : G} (hm : m ∈ H0 M Z) (hmL : conjSubgroup m (LB M Q B) = LB M Q B)
    (hmW : ∀ w ∈ M₀.B.orthogonal (hc.VtSub hS.model t),
      sec7Op hc hS hm w ∈ M₀.B.orthogonal (hc.VtSub hS.model t))
    (hmU : ∀ u ∈ hc.VtSub hS.model t, sec7Op hc hS hm u ∈ hc.VtSub hS.model t) :
    ∀ a ∈ sec7Asub hc hS t, sec7Op hc hS hm a ∈ sec7Asub hc hS t := by
  rintro a ⟨ha1, ha2⟩
  refine ⟨hmW a ha1, fun l hl => ?_⟩
  have hl' : m⁻¹ * l * m ∈ LB M Q B := by
    have h1 : l ∈ conjSubgroup m (LB M Q B) := by rw [hmL]; exact hl
    exact mem_conjSubgroup.mp h1
  have hmlm : m * (m⁻¹ * l * m) ∈ H0 M Z :=
    (H0 M Z).mul_mem hm (hc.LB_le_H0 hl')
  have hlm : l * m ∈ H0 M Z := (H0 M Z).mul_mem (hc.LB_le_H0 hl) hm
  have h1 := sec7Op_mul hc hS (hc.LB_le_H0 hl) hm hlm
  have h2 := sec7Op_mul hc hS hm (hc.LB_le_H0 hl') hmlm
  have h3 := sec7Op_congr hc hS hlm hmlm (by group)
  have key : sec7Op hc hS (hc.LB_le_H0 hl) (sec7Op hc hS hm a) =
      sec7Op hc hS hm (sec7Op hc hS (hc.LB_le_H0 hl') a) := by
    have h4 := LinearMap.congr_fun h1 a
    have h5 := LinearMap.congr_fun h2 a
    rw [h3] at h4
    rw [Module.End.mul_apply] at h4 h5
    rw [← h4, h5]
  have e : sec7Op hc hS (hc.LB_le_H0 hl) (sec7Op hc hS hm a) - sec7Op hc hS hm a =
      sec7Op hc hS hm (sec7Op hc hS (hc.LB_le_H0 hl') a - a) := by
    rw [map_sub, key]
  show sec7Op hc hS (hc.LB_le_H0 hl) (sec7Op hc hS hm a) - sec7Op hc hS hm a ∈
    hc.VtSub hS.model t
  rw [e]
  exact hmU _ (ha2 _ hl')

end

end CFSG.RankThree.GF2n.Stroth80
