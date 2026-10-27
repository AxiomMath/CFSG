module

public import CFSG.RankThree.GF2n.Stroth80.Sec5Model
public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsLin
public import CFSG.RankThree.GF2n.Stroth80.Sec12Decomp
public import CFSG.RankThree.GF2n.Smith81.Sec1Main

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement Matrix

section LinearAlgebra

variable {F E : Type} [Field F] [AddCommGroup E] [Module F E] [FiniteDimensional F E]

theorem range_sub_one_eq_orthogonal_ker (β : LinearMap.BilinForm F E) (hnd : β.Nondegenerate)
    (hrefl : β.IsRefl) (u : E →ₗ[F] E) (hiso : ∀ e f, β (u e) (u f) = β e f)
    (hinv : ∀ e, u (u e) = e) :
    LinearMap.range (u - 1) = β.orthogonal (LinearMap.ker (u - 1)) := by
  have hsurj : Function.Surjective u := fun e => ⟨u e, hinv e⟩
  rw [ker_sub_one_eq_orthogonal_range β hnd hrefl u hiso hsurj]
  exact (LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl (LinearMap.range (u - 1))).symm

end LinearAlgebra

variable {G : Type} [Group G] [Finite G]
  {M Q Z B X : Subgroup G} {x : G}

def Ctx.commQ1Hom (hc : Ctx M Q Z B) {t : G} (htM : t ∈ M) : ↥(Q1 hc t) →* ↥Z where
  toFun x := ⟨⁅t, (x : G)⁆, ((hc.mem_Q1_iff htM).mp x.2).2⟩
  map_one' := Subtype.ext (by simp [commutatorElement_def])
  map_mul' x y := by
    refine Subtype.ext ?_
    have hxQ : (x : G) ∈ Q := ((hc.mem_Q1_iff htM).mp x.2).1
    have hyZ : ⁅t, (y : G)⁆ ∈ Z := ((hc.mem_Q1_iff htM).mp y.2).2
    have hconj : (x : G) * ⁅t, (y : G)⁆ * (x : G)⁻¹ = ⁅t, (y : G)⁆ := by
      rw [← Z_central hc.hyp hyZ hxQ]
      group
    show ⁅t, ((x : G) * y)⁆ = ⁅t, (x : G)⁆ * ⁅t, (y : G)⁆
    rw [show ⁅t, ((x : G) * y)⁆ =
      ⁅t, (x : G)⁆ * ((x : G) * ⁅t, (y : G)⁆ * (x : G)⁻¹) by
      simp only [commutatorElement_def]; group, hconj]

theorem Ctx.ker_commQ1Hom (hc : Ctx M Q Z B) {t : G} (htM : t ∈ M) :
    (Ctx.commQ1Hom hc htM).ker =
      (Q ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf (Q1 hc t) := by
  ext x
  simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Ctx.commQ1Hom, MonoidHom.coe_mk,
    MonoidHom.coe_coe]
  constructor
  · intro h1
    have h1' : ⁅t, (x : G)⁆ = 1 := congrArg Subtype.val h1
    have h2 : ⁅(x : G), t⁆ = 1 := by
      have h3 : ⁅(x : G), t⁆⁻¹ = 1 := by rw [commutatorElement_inv, h1']
      rwa [inv_eq_one] at h3
    refine ⟨((hc.mem_Q1_iff htM).mp x.2).1, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (commutatorElement_eq_one_iff_mul_comm.mp h2)
  · rintro ⟨hxQ, hxc⟩
    refine Subtype.ext ?_
    have hxt : t * (x : G) = (x : G) * t :=
      (Subgroup.mem_centralizer_singleton_iff.mp hxc).symm
    show ⁅t, (x : G)⁆ = 1
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact hxt

private def commAlphaHom (hc : Ctx M Q Z B) {t α : G} (htM : t ∈ M) (hαQ : α ∈ Q) :
    ↥(Q1 hc t) →* ↥Z where
  toFun h := ⟨⁅(h : G), α⁆, comm_mem_Z hc.hyp ((hc.mem_Q1_iff htM).mp h.2).1 hαQ⟩
  map_one' := Subtype.ext (by simp [commutatorElement_def])
  map_mul' h₁ h₂ := by
    refine Subtype.ext ?_
    have h₁Q : (h₁ : G) ∈ Q := ((hc.mem_Q1_iff htM).mp h₁.2).1
    have h₁Z : ⁅(h₁ : G), α⁆ ∈ Z := comm_mem_Z hc.hyp h₁Q hαQ
    have h₂Z : ⁅(h₂ : G), α⁆ ∈ Z :=
      comm_mem_Z hc.hyp ((hc.mem_Q1_iff htM).mp h₂.2).1 hαQ
    have hconj : (h₁ : G) * ⁅(h₂ : G), α⁆ * (h₁ : G)⁻¹ = ⁅(h₂ : G), α⁆ := by
      rw [← Z_central hc.hyp h₂Z h₁Q]
      group
    have e : ⁅((h₁ : G) * h₂), α⁆ = ⁅(h₂ : G), α⁆ * ⁅(h₁ : G), α⁆ := by
      rw [show ⁅((h₁ : G) * h₂), α⁆ =
        (h₁ : G) * ⁅(h₂ : G), α⁆ * (h₁ : G)⁻¹ * ⁅(h₁ : G), α⁆ by
        simp only [commutatorElement_def]; group, hconj]
    show ⁅((h₁ : G) * h₂), α⁆ = ⁅(h₁ : G), α⁆ * ⁅(h₂ : G), α⁆
    rw [e, Z_central hc.hyp h₂Z (hc.hyp.Z_normal.1 h₁Z)]

private theorem commAlphaHom_surjective (hc : Ctx M Q Z B) (hs : Sit M Q Z X x)
    {α : G} (hαQ : α ∈ Q) {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (R : Tim79.GammaReg Q Z γ) (A : XAct M₀ x) {f : M₀.E}
    (hf : A.T f = f) (hfB : M₀.B f (M₀.π α) ≠ 0) :
    Function.Surjective (commAlphaHom hc (t := x) (α := α) hs.memM hαQ) := by
  intro z'
  obtain ⟨h, hhQ, hπh⟩ := M₀.π_surj ((γ z' / M₀.B f (M₀.π α)) • f)
  have hQ1 : h ∈ Q1 hc x := by
    refine (hc.mem_Q1_iff hs.memM).mpr ⟨hhQ, ?_⟩
    refine (comm_mem_iff_fix (t := x) (T := A.T)
      (fun y hy => (Subgroup.mem_normalizer_iff.mp (hs.hyp.Q_normal.2 hs.memM) y).mp hy)
      A.hπ (x := h) hhQ).mpr ?_
    rw [hπh, map_smul, hf]
  have hγ : γ ⁅h, α⁆ = γ z' := by
    rw [M₀.comm_eq h hhQ α hαQ, hπh, map_smul, LinearMap.smul_apply, smul_eq_mul,
      div_mul_cancel₀ _ hfB]
  refine ⟨⟨h, hQ1⟩, Subtype.ext ?_⟩
  exact R.eq_of_γ_eq (comm_mem_Z hs.hyp hhQ hαQ) z'.2 hγ

private theorem commQ1Hom_surjective (hc : Ctx M Q Z B) (hs : Sit M Q Z X x) {α : G}
    (hα : α ∈ Q ⊓ QB X) {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (R : Tim79.GammaReg Q Z γ) (A : XAct M₀ x) {f : M₀.E}
    (hf : A.T f = f) (hfB : M₀.B f (M₀.π α) ≠ 0) :
    Function.Surjective (Ctx.commQ1Hom hc (t := x) hs.memM) := by
  let φ : ↥(Q1 hc x) →* ↥Z := commAlphaHom hc (t := x) (α := α) hs.memM hα.1
  have hφsurj : Function.Surjective φ :=
    commAlphaHom_surjective hc hs hα.1 R A hf hfB
  have hker_le : (Ctx.commQ1Hom hc (t := x) hs.memM).ker ≤ φ.ker := by
    intro u hu
    have hu_cent : (u : G) ∈ Q ⊓ Subgroup.centralizer ({x} : Set G) := by
      rw [Ctx.ker_commQ1Hom hc (t := x) hs.memM, Subgroup.mem_subgroupOf] at hu
      exact hu
    have hαu : α * (u : G) = (u : G) * α :=
      (smith_1_13 hs).2.2.2.2 α hα (u : G) hu_cent
    rw [MonoidHom.mem_ker]
    refine Subtype.ext ?_
    show ⁅(u : G), α⁆ = 1
    exact commutatorElement_eq_one_iff_mul_comm.mpr hαu.symm
  have hcard : Nat.card ↥Z ≤ Nat.card (Ctx.commQ1Hom hc (t := x) hs.memM).range := by
    calc Nat.card ↥Z = Nat.card φ.range := by
          rw [MonoidHom.range_eq_top.mpr hφsurj, Subgroup.card_top]
      _ = φ.ker.index := (Subgroup.index_ker φ).symm
      _ ≤ (Ctx.commQ1Hom hc (t := x) hs.memM).ker.index := Subgroup.index_antitone hker_le
      _ = Nat.card (Ctx.commQ1Hom hc (t := x) hs.memM).range := Subgroup.index_ker _
  have htop : (Ctx.commQ1Hom hc (t := x) hs.memM).range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    exact le_antisymm
      (Nat.card_le_card_of_injective
        (fun y : ↥((Ctx.commQ1Hom hc (t := x) hs.memM).range) => (y.1 : ↥Z))
        (fun a b h => Subtype.ext (Subtype.ext (congrArg Subtype.val h)))) hcard
  intro z
  exact MonoidHom.mem_range.mp (by rw [htop]; exact Subgroup.mem_top z)

private theorem exists_conj_of_comm_eq (hs : Sit M Q Z X x) {z h : G}
    (hz : z ∈ Z) (hhQ : h ∈ Q) (hh : ⁅x, h⁆ = z) :
    ∃ h' ∈ Q, h' * x * h'⁻¹ = x * z := by
  have h1 : x * h * x⁻¹ = h * z := by
    have h2 : x * h * x⁻¹ * h⁻¹ = z := hh
    calc x * h * x⁻¹ = (x * h * x⁻¹ * h⁻¹) * h := by group
      _ = z * h := by rw [h2]
      _ = h * z := Z_central hs.hyp hz hhQ
  refine ⟨h⁻¹, Q.inv_mem hhQ, ?_⟩
  rw [inv_inv]
  calc h⁻¹ * x * h = h⁻¹ * (x * h * x⁻¹) * x := by group
    _ = h⁻¹ * (h * z) * x := by rw [h1]
    _ = z * x := by group
    _ = x * z := by
      have hxcz : x * z * x⁻¹ = z := hs.x_cent (smith_1_12 hs) z hz
      calc z * x = (x * z * x⁻¹) * x := by rw [hxcz]
        _ = x * z := by group

private theorem mem_Ut_of_mem_range_sub_one (hs : Sit M Q Z X x)
    {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} (A : XAct M₀ x)
    {α : G} (hαQ : α ∈ Q) {f : M₀.E}
    (hf : (A.T : M₀.E →ₗ[K] M₀.E) f - f = M₀.π α) : α ∈ Ut Q Z x := by
  obtain ⟨q, hq, hπq⟩ := M₀.π_surj f
  have hxqQ : x * q * x⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hs.hyp.Q_normal.2 hs.memM) q).mp hq
  have hπd : M₀.π (x * q * x⁻¹ * q⁻¹) = M₀.π α := by
    rw [M₀.π_mul (x * q * x⁻¹) hxqQ q⁻¹ (Q.inv_mem hq), A.hπ q hq,
      Tim79.QuadModel.pi_inv M₀ hq, hπq]
    simpa [sub_eq_add_neg] using hf
  have hz : α⁻¹ * (x * q * x⁻¹ * q⁻¹) ∈ Z := by
    refine (M₀.π_ker _ (Q.mul_mem (Q.inv_mem hαQ) (Q.mul_mem hxqQ (Q.inv_mem hq)))).mp ?_
    rw [M₀.π_mul (α⁻¹) (Q.inv_mem hαQ) (x * q * x⁻¹ * q⁻¹)
      (Q.mul_mem hxqQ (Q.inv_mem hq)), Tim79.QuadModel.pi_inv M₀ hαQ, hπd]
    exact neg_add_cancel _
  have hcomm : (x * q * x⁻¹ * q⁻¹) ∈ ⁅Q, Subgroup.zpowers x⁆ := by
    have h := Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers x)
    have e : (x * q * x⁻¹ * q⁻¹) = ⁅q, x⁆⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (⁅Q, Subgroup.zpowers x⁆).inv_mem h
  have hαd : α = (x * q * x⁻¹ * q⁻¹) * (α⁻¹ * (x * q * x⁻¹ * q⁻¹))⁻¹ := by group
  rw [hαd]
  simpa [Ut] using Subgroup.mul_mem_sup hcomm (Z.inv_mem hz)

theorem Ctx.fuse_of_not_mem_Ut (hc : Ctx M Q Z B) (hs : Sit M Q Z X x) {α : G}
    (hα : α ∈ Q ⊓ QB X) (hαU : α ∉ Ut Q Z x) :
    ∀ z ∈ Z, ∃ h ∈ Q, h * x * h⁻¹ = x * z := by
  classical
  have hx2 : x * x = 1 := hs.x_sq
  have h12 : Post12 M Q Z X := smith_1_12 hs
  have hαQ : α ∈ Q := hα.1
  have hαx : α * x = x * α :=
    Subgroup.mem_centralizer_singleton_iff.mp ((smith_1_13 hs).2.2.2.1 hα).2
  obtain ⟨K, _, _, γ, M₀, hD, -, -, ⟨A⟩⟩ :=
    exists_model hs.hyp hs.memM (hs.x_cent h12)
  let N : M₀.E →ₗ[K] M₀.E := (A.T : M₀.E →ₗ[K] M₀.E) - 1
  have hfix : A.T (M₀.π α) = M₀.π α := by
    rw [← A.hπ α hαQ]
    congr 1
    rw [show x * α * x⁻¹ = α by rw [← hαx, mul_assoc, mul_inv_cancel, mul_one]]
  have hrange_eq : LinearMap.range N = M₀.B.orthogonal (LinearMap.ker N) :=
    range_sub_one_eq_orthogonal_ker M₀.B (modelB_nondegenerate M₀)
      (fun e f h => by rw [Tim79.QuadModel.B_comm, h, neg_zero])
      (A.T : M₀.E →ₗ[K] M₀.E) A.hB (fun e => A.T_T hs.hyp hs.memM hx2 e)
  have hnotrange : M₀.π α ∉ LinearMap.range N := by
    rintro ⟨f, hf⟩
    exact hαU (mem_Ut_of_mem_range_sub_one hs A hαQ (by simpa [N] using hf))
  obtain ⟨f, hfker, hfB⟩ : ∃ f, f ∈ LinearMap.ker N ∧ M₀.B f (M₀.π α) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hnotrange (by
      rw [hrange_eq]
      exact LinearMap.BilinForm.mem_orthogonal_iff.mpr hcon)
  have hf : A.T f = f := by
    have h0 : N f = 0 := LinearMap.mem_ker.mp hfker
    exact sub_eq_zero.mp (by simpa [N] using h0)
  have hsurj := commQ1Hom_surjective hc hs hα hD.reg A hf hfB
  intro z hz
  obtain ⟨h, hh⟩ : ∃ h, Ctx.commQ1Hom hc (t := x) hs.memM h = (⟨z, hz⟩ : ↥Z) :=
    hsurj ⟨z, hz⟩
  exact exists_conj_of_comm_eq hs hz ((hc.mem_Q1_iff hs.memM).mp h.2).1
    (congrArg Subtype.val hh)

theorem Ctx.inf_QB_le_Ut_or_fuse (hc : Ctx M Q Z B) (hs : Sit M Q Z X x) :
    Q ⊓ QB X ≤ Ut Q Z x ∨ ∀ z ∈ Z, ∃ h ∈ Q, h * x * h⁻¹ = x * z := by
  by_cases hU : Q ⊓ QB X ≤ Ut Q Z x
  · exact Or.inl hU
  · have h : ∃ α ∈ Q ⊓ QB X, α ∉ Ut Q Z x := by
      by_contra hcon
      push Not at hcon
      exact hU (fun α hα => hcon α hα)
    obtain ⟨α, hα, hαU⟩ := h
    exact Or.inr (Ctx.fuse_of_not_mem_Ut hc hs hα hαU)

end CFSG.RankThree.GF2n.Stroth80
