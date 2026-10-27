module

public import CFSG.Quasithin.Background.B5Part3

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank
open Matrix

theorem eq_zero_or_one_of_card_two_F {F : Type} [Field F] (hF : Nat.card F = 2) (c : F) :
    c = 0 ∨ c = 1 := by
  by_cases h0 : c = 0
  · exact Or.inl h0
  · right
    obtain ⟨x, hx⟩ := (Nat.card_eq_two_iff' (0 : F)).1 hF
    have h1 : c = x := hx.2 c h0
    have h2 : (1 : F) = x := hx.2 1 one_ne_zero
    rw [h1, h2]

theorem exists_stated_of_mulEquiv {F : Type} [Field F] (hF : Nat.card F = 2)
    (g : Multiplicative (Fin 3 → F) ≃* Multiplicative (Fin 3 → F)) :
    ∃ G : ↥(StatedSL 3 F), ∀ a, g a = natAct (StatedSL 3 F) G a := by
  classical
  have hc := eq_zero_or_one_of_card_two_F hF
  let gl : (Fin 3 → F) →ₗ[F] (Fin 3 → F) :=
    { toFun := fun v => Multiplicative.toAdd (g (Multiplicative.ofAdd v))
      map_add' := fun v w => by simp
      map_smul' := fun c v => by
        rcases hc c with h | h
        · subst h
          simp
        · subst h
          simp }
  have hbij : Function.Bijective gl := by
    constructor
    · intro v w h
      have := g.injective (Multiplicative.toAdd.injective h)
      simp at this
      exact this
    · intro w
      refine ⟨Multiplicative.toAdd (g.symm (Multiplicative.ofAdd w)), ?_⟩
      show Multiplicative.toAdd (g (Multiplicative.ofAdd
        (Multiplicative.toAdd (g.symm (Multiplicative.ofAdd w))))) = w
      simp
  let gle : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F) := LinearEquiv.ofBijective gl hbij
  let M : Matrix (Fin 3) (Fin 3) F := LinearMap.toMatrix' gl
  let M' : Matrix (Fin 3) (Fin 3) F := LinearMap.toMatrix' gle.symm.toLinearMap
  have h1 : M * M' = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    ext v
    simp [gle]
  have h2 : M' * M = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    ext v
    simp [gle]
  have hdet : IsUnit M.det := by
    rw [← Matrix.isUnit_iff_isUnit_det]
    exact ⟨⟨M, M', h1, h2⟩, rfl⟩
  let Gl : GL (Fin 3) F := Matrix.GeneralLinearGroup.mk'' M hdet
  have hdet1 : M.det = 1 := by
    rcases hc M.det with h | h
    · exact absurd h hdet.ne_zero
    · exact h
  refine ⟨⟨Gl, Subgroup.subset_closure hdet1⟩, fun a => ?_⟩
  show g a = Multiplicative.ofAdd (M.mulVec (Multiplicative.toAdd a))
  rw [LinearMap.toMatrix'_mulVec]
  show g a = Multiplicative.ofAdd (Multiplicative.toAdd (g (Multiplicative.ofAdd (Multiplicative.toAdd a))))
  simp

theorem natAct_injective {F : Type} [Field F] {n : ℕ} (Γ : Subgroup (GL (Fin n) F)) {γ δ : ↥Γ}
    (h : ∀ a, natAct Γ γ a = natAct Γ δ a) : γ = δ := by
  apply Subtype.ext
  apply Units.ext
  rw [Matrix.ext_iff_mulVec]
  intro v
  have := h (Multiplicative.ofAdd v)
  simpa [natAct] using congrArg Multiplicative.toAdd this

theorem natAct_mul_twist {F : Type} [Field F] {n : ℕ} (Γ : Subgroup (GL (Fin n) F)) (γ δ : ↥Γ)
    (a : Multiplicative (Fin n → F)) : natAct Γ (γ * δ) a = natAct Γ γ (natAct Γ δ a) := by
  simp [natAct, Matrix.mulVec_mulVec]

section Twist

variable {W : Type} [CommGroup W]

theorem exists_sec_equiv_nat {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (Γ : Subgroup (GL ι K)) {H : Subgroup (MulAut W)} {U Z : Subgroup W} {π : ↥Γ →* ↥H}
    (h : (FFModel.nat Γ).RealizesVia H U Z π) :
    ∃ ε : ↥U ⧸ Z.subgroupOf U ≃* Multiplicative (ι → K),
      ∀ (γ : ↥Γ) (u : ↥U) (hu : ((π γ : ↥H) : MulAut W) (u : W) ∈ U),
        ε (QuotientGroup.mk ⟨_, hu⟩) = natAct Γ γ (ε (QuotientGroup.mk u)) := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := h
  have hker : β.ker = Z.subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
  let q : ↥(⊤ : Subgroup (Multiplicative (ι → K))) ⧸
      (⊥ : Subgroup (Multiplicative (ι → K))).subgroupOf (⊤ : Subgroup (Multiplicative (ι → K))) ≃*
        Multiplicative (ι → K) :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf _)).trans
      (QuotientGroup.quotientBot.trans Subgroup.topEquiv)
  let ε : ↥U ⧸ Z.subgroupOf U ≃* Multiplicative (ι → K) :=
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective β hβs)).trans q
  have hε : ∀ u : ↥U, ε (QuotientGroup.mk u) = q (β u) := fun u => rfl
  refine ⟨ε, fun γ u hu => ?_⟩
  have hqs : ∀ x, x = (QuotientGroup.mk ⟨q x, trivial⟩ : ↥(⊤ : Subgroup (Multiplicative (ι → K))) ⧸
      (⊥ : Subgroup (Multiplicative (ι → K))).subgroupOf (⊤ : Subgroup (Multiplicative (ι → K)))) :=
    fun x => by
      induction x using QuotientGroup.induction_on with
      | H m => rfl
  have h1 : β u = QuotientGroup.mk ⟨q (β u), trivial⟩ := hqs _
  have h2 := hβe γ u ⟨q (β u), trivial⟩ hu trivial h1
  rw [hε, hε]
  exact congrArg q h2

theorem exists_inner_of_twist_sl3 {F : Type} [Field F] (hF : Nat.card F = 2)
    {L : Subgroup (MulAut W)} {U Z U' Z' : Subgroup W} {π : ↥(StatedSL 3 F) →* ↥L}
    (hπ : (FFModel.nat (StatedSL 3 F)).RealizesVia L U Z π)
    {σ : MulAut W} (hσL : ∀ x ∈ L, σ * x * σ⁻¹ ∈ L)
    (hU' : U' = U.map σ.toMonoidHom) (hZ' : Z' = Z.map σ.toMonoidHom)
    (hiso : SecIsoL L U' Z' U Z) :
    ∃ l₀ ∈ L, ∀ x ∈ L, (σ * l₀⁻¹) * x = x * (σ * l₀⁻¹) := by
  subst hU' hZ'
  obtain ⟨ε, hε⟩ := exists_sec_equiv_nat (StatedSL 3 F) hπ
  obtain ⟨hπs, -, -, hLU, -, -, -, -⟩ := hπ
  obtain ⟨-, -, -, -, -, -, β, hβs, hβk, hβe⟩ := B5.secIsoL_iff.1 hiso
  let σU : ↥U →* ↥(U.map σ.toMonoidHom) := σ.toMonoidHom.subgroupMap U
  have hσU : Function.Surjective σU := σ.toMonoidHom.subgroupMap_surjective U
  let F₀ : ↥U →* ↥U ⧸ Z.subgroupOf U := β.comp σU
  have hF₀s : Function.Surjective F₀ := hβs.comp hσU
  have hσmem : ∀ x : W, σ x ∈ Z.map σ.toMonoidHom ↔ x ∈ Z := fun x =>
    Subgroup.mem_map_iff_mem σ.injective
  have hF₀k : F₀.ker = Z.subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show β (σU u) = 1 ↔ (u : W) ∈ Z
    rw [hβk]
    exact hσmem (u : W)
  let Fbar : (↥U ⧸ Z.subgroupOf U) ≃* (↥U ⧸ Z.subgroupOf U) :=
    (QuotientGroup.quotientMulEquivOfEq hF₀k.symm).trans (QuotientGroup.quotientKerEquivOfSurjective F₀ hF₀s)
  have hFbar : ∀ u : ↥U, Fbar (QuotientGroup.mk u) = F₀ u := fun u => rfl
  let g : Multiplicative (Fin 3 → F) ≃* Multiplicative (Fin 3 → F) := ε.symm.trans (Fbar.trans ε)
  have hg : ∀ u : ↥U, g (ε (QuotientGroup.mk u)) = ε (F₀ u) := fun u => by
    simp [g, hFbar]
  obtain ⟨G, hG⟩ := exists_stated_of_mulEquiv hF g
  have hγ' : ∀ γ : ↥(StatedSL 3 F), ∃ γ' : ↥(StatedSL 3 F),
      ((π γ' : ↥L) : MulAut W) = σ * (π γ : MulAut W) * σ⁻¹ := fun γ => by
    obtain ⟨γ', hγ'⟩ := hπs ⟨σ * (π γ : MulAut W) * σ⁻¹, hσL _ (π γ).2⟩
    exact ⟨γ', congrArg Subtype.val hγ'⟩
  have key : ∀ γ : ↥(StatedSL 3 F), ∀ γ' : ↥(StatedSL 3 F),
      ((π γ' : ↥L) : MulAut W) = σ * (π γ : MulAut W) * σ⁻¹ →
      ∀ a, g (natAct (StatedSL 3 F) γ a) = natAct (StatedSL 3 F) γ' (g a) := by
    intro γ γ' hγγ' a
    obtain ⟨s, rfl⟩ := ε.surjective a
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective s
    have hu1 : ((π γ : ↥L) : MulAut W) (u : W) ∈ U := hLU (π γ) u u.2
    rw [← hε γ u hu1, hg, hg]
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (F₀ u)
    have hm1 : ((π γ' : ↥L) : MulAut W) (m : W) ∈ U := hLU (π γ') m m.2
    have hσu : ((π γ' : ↥L) : MulAut W) ((σU u : ↥(U.map σ.toMonoidHom)) : W) ∈ U.map σ.toMonoidHom := by
      refine ⟨((π γ : ↥L) : MulAut W) (u : W), hu1, ?_⟩
      have : ((π γ' : ↥L) : MulAut W) = σ * (π γ : MulAut W) * σ⁻¹ := hγγ'
      show σ (((π γ : ↥L) : MulAut W) (u : W)) = ((π γ' : ↥L) : MulAut W) (σ (u : W))
      rw [this]
      simp [MulAut.mul_apply]
    have hm' : β (σU u) = (m : ↥U ⧸ Z.subgroupOf U) := hm.symm
    have h1 := hβe (π γ') (σU u) m hσu hm1 hm'
    have h2 : (⟨((π γ' : ↥L) : MulAut W) ((σU u : ↥(U.map σ.toMonoidHom)) : W), hσu⟩ :
        ↥(U.map σ.toMonoidHom)) = σU ⟨((π γ : ↥L) : MulAut W) (u : W), hu1⟩ := by
      apply Subtype.ext
      have : ((π γ' : ↥L) : MulAut W) = σ * (π γ : MulAut W) * σ⁻¹ := hγγ'
      show ((π γ' : ↥L) : MulAut W) (σ (u : W)) = σ (((π γ : ↥L) : MulAut W) (u : W))
      rw [this]
      simp [MulAut.mul_apply]
    rw [h2] at h1
    have h3 := hε γ' m hm1
    show ε (β (σU ⟨((π γ : ↥L) : MulAut W) (u : W), hu1⟩)) = natAct (StatedSL 3 F) γ' (ε (β (σU u)))
    rw [h1, hm']
    exact h3
  have hconj : ∀ γ : ↥(StatedSL 3 F), σ * (π γ : MulAut W) * σ⁻¹ =
      (π G : MulAut W) * (π γ : MulAut W) * (π G : MulAut W)⁻¹ := by
    intro γ
    obtain ⟨γ', hγ''⟩ := hγ' γ
    have hk := key γ γ' hγ''
    have heq : G * γ = γ' * G := by
      apply natAct_injective (StatedSL 3 F)
      intro a
      rw [natAct_mul_twist, natAct_mul_twist, ← hG, ← hG]
      exact hk a
    have hγeq : γ' = G * γ * G⁻¹ := by
      rw [heq]
      group
    rw [← hγ'', hγeq]
    simp
  refine ⟨((π G : ↥L) : MulAut W), (π G).2, fun x hx => ?_⟩
  obtain ⟨γ, hγ⟩ := hπs ⟨x, hx⟩
  have hxγ : x = (π γ : MulAut W) := (congrArg Subtype.val hγ).symm
  have hy : (π G : MulAut W)⁻¹ * x * (π G : MulAut W) ∈ L :=
    L.mul_mem (L.mul_mem (L.inv_mem (π G).2) hx) (π G).2
  obtain ⟨δ, hδ⟩ := hπs ⟨_, hy⟩
  have hyδ : (π G : MulAut W)⁻¹ * x * (π G : MulAut W) = (π δ : MulAut W) := (congrArg Subtype.val hδ).symm
  have h := hconj δ
  rw [← hyδ] at h
  calc (σ * (π G : MulAut W)⁻¹) * x
      = σ * ((π G : MulAut W)⁻¹ * x * (π G : MulAut W)) * σ⁻¹ * (σ * (π G : MulAut W)⁻¹) := by group
    _ = x * (σ * (π G : MulAut W)⁻¹) := by rw [h]; group

end Twist

end CFSG.Quasithin
