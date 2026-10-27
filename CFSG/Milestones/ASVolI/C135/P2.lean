module

public import CFSG.Milestones.ASVolI.C1
public import CFSG.Quasithin.Vol2.Ch4Sec3C135H1
public import CFSG.Quasithin.MS93.ASC134

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open CFSG.Quasithin.H13.Ch4.C135 (dualHom coe_dualHom dualHom_dualHom
  eq_zero_of_dual_equivariant)
open scoped Matrix

variable {G : Type} [Group G]

section Stab

variable {F : Type} [Field F]

theorem burnsideC135_eq_top_of_stab_invariant {x : Fin 3 → F} (hx : x ≠ 0)
    (Y : AddSubgroup (Fin 3 → F)) (hYx : ∀ c : F, c • x ∈ Y)
    (hY : ∀ δ : Matrix.SpecialLinearGroup (Fin 3) F,
      (δ : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x → ∀ y ∈ Y, (δ : Matrix (Fin 3) (Fin 3) F) *ᵥ y ∈ Y)
    {y : Fin 3 → F} (hyY : y ∈ Y) (hy : ∀ c : F, y ≠ c • x) : Y = ⊤ := by
  classical
  obtain ⟨g, hg⟩ := CFSG.Quasithin.H13.Ch4.SL3Pt.exists_mulVec_e0 hx
  set Y' : AddSubgroup (Fin 3 → F) := Y.comap
    (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) F)).toAddMonoidHom with hY'
  have hmem : ∀ v, v ∈ Y' ↔ (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ Y := fun v => Iff.rfl
  set e₀ : Fin 3 → F := ![1, 0, 0] with he₀
  have hY'e : ∀ c : F, c • e₀ ∈ Y' := by
    intro c
    rw [hmem, Matrix.mulVec_smul, hg]
    exact hYx c
  have hgm : ∀ (a b : Matrix.SpecialLinearGroup (Fin 3) F) (v : Fin 3 → F),
      ((a * b : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
        (a : Matrix (Fin 3) (Fin 3) F) *ᵥ ((b : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by
    intro a b v
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec]
  have hginv : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x =
      e₀ := by
    rw [← hg, ← hgm, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  have hY'inv : ∀ δ : Matrix.SpecialLinearGroup (Fin 3) F,
      (δ : Matrix (Fin 3) (Fin 3) F) *ᵥ e₀ = e₀ → ∀ v ∈ Y',
        (δ : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ Y' := by
    intro δ hδ v hv
    rw [hmem] at hv ⊢
    have hfix : ((g * δ * g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) *ᵥ x = x := by
      rw [hgm, hgm, hginv, hδ, hg]
    have := hY (g * δ * g⁻¹) hfix _ hv
    rwa [hgm, hgm, ← hgm g⁻¹ g, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_mulVec] at this
  set y' := ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y with hy'
  have hgy' : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ y' = y := by
    rw [hy', Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  have hy'Y : y' ∈ Y' := by rw [hmem, hgy']; exact hyY
  have hy'12 : y' 1 ≠ 0 ∨ y' 2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hy (y' 0)
    rw [← hgy', ← hg, ← Matrix.mulVec_smul]
    congr 1
    funext i
    fin_cases i <;> simp [he₀, h.1, h.2]
  have hroot : ∀ (i j : Fin 3) (hij : i ≠ j), j ≠ 0 → ∀ b : F, ∀ v ∈ Y',
      v + Pi.single i (b * v j) ∈ Y' := by
    intro i j hij hj0 b v hv
    have hfix : ((Matrix.SpecialLinearGroup.transvection hij b :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ e₀ = e₀ := by
      rw [CFSG.Quasithin.H13.Ch4.transvection_mulVec]
      have : e₀ j = 0 := by fin_cases j <;> simp_all [he₀]
      rw [this, mul_zero, Pi.single_zero, add_zero]
    have := hY'inv _ hfix v hv
    rwa [CFSG.Quasithin.H13.Ch4.transvection_mulVec] at this
  have hsingle : ∀ (i j : Fin 3) (hij : i ≠ j), j ≠ 0 → ∀ v ∈ Y', v j ≠ 0 →
      ∀ a : F, Pi.single i a ∈ Y' := by
    intro i j hij hj0 v hv hvj a
    have h1 := Y'.sub_mem (hroot i j hij hj0 (a / v j) v hv) hv
    rwa [add_sub_cancel_left, div_mul_cancel₀ a hvj] at h1
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have he1 : ∀ a : F, Pi.single 1 a ∈ Y' := by
    rcases hy'12 with h1 | h2
    ·
      have he2 : ∀ a : F, Pi.single 2 a ∈ Y' := hsingle 2 1 h21 (by decide) y' hy'Y h1
      exact hsingle 1 2 h12 (by decide) (Pi.single 2 1) (he2 1) (by simp)
    · exact hsingle 1 2 h12 (by decide) y' hy'Y h2
  have he2 : ∀ a : F, Pi.single 2 a ∈ Y' :=
    hsingle 2 1 h21 (by decide) (Pi.single 1 1) (he1 1) (by simp)
  have he0 : ∀ a : F, Pi.single 0 a ∈ Y' := by
    intro a
    have := hY'e a
    convert this using 1
    funext i
    fin_cases i <;> simp [he₀]
  have hall : Y' = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : v = Pi.single 0 (v 0) + Pi.single 1 (v 1) + Pi.single 2 (v 2) := by
      funext i
      fin_cases i <;> simp
    rw [hv]
    exact Y'.add_mem (Y'.add_mem (he0 _) (he1 _)) (he2 _)
  rw [eq_top_iff]
  intro v _
  have h1 : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ Y' := by
    rw [hall]; exact AddSubgroup.mem_top _
  rw [hmem, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at h1
  exact h1

end Stab

section Struct

structure burnsideC135_DSG (Q L W₁ W₂ : Subgroup G) {F : Type} [Field F]
    (α : ↥L →* Matrix.SpecialLinearGroup (Fin 3) F)
    (βU : ↥(centerOf Q) →* Multiplicative (Fin 3 → F))
    (β₁ : ↥W₁ →* Multiplicative (Fin 3 → F))
    (β₂ : ↥W₂ →* Multiplicative (Fin 3 → F)) : Prop where
  alpha_onto : Function.Surjective α
  normQ : L ≤ Subgroup.normalizer (Q : Set G)
  le₁ : centerOf Q ≤ W₁
  le₂ : centerOf Q ≤ W₂
  le_Q₁ : W₁ ≤ Q
  le_Q₂ : W₂ ≤ Q
  join : W₁ ⊔ W₂ = Q
  meet : W₁ ⊓ W₂ = centerOf Q
  norm₁ : L ≤ Subgroup.normalizer (W₁ : Set G)
  norm₂ : L ≤ Subgroup.normalizer (W₂ : Set G)
  natU_onto : Function.Surjective βU
  natU_ker : βU.ker = ⊥
  natU_act : ∀ (ℓ : ↥L) (u v : ↥(centerOf Q)), (v : G) = ℓ * u * ℓ⁻¹ →
    Multiplicative.toAdd (βU v) =
      ((α ℓ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
        (Multiplicative.toAdd (βU u))
  dual₁_onto : Function.Surjective β₁
  dual₁_ker : β₁.ker = (centerOf Q).subgroupOf W₁
  dual₁_act : ∀ (ℓ : ↥L) (u v : ↥W₁), (v : G) = ℓ * u * ℓ⁻¹ →
    Multiplicative.toAdd (β₁ v) =
      (((α ℓ)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).transpose.mulVec
        (Multiplicative.toAdd (β₁ u))
  dual₂_onto : Function.Surjective β₂
  dual₂_ker : β₂.ker = (centerOf Q).subgroupOf W₂
  dual₂_act : ∀ (ℓ : ↥L) (u v : ↥W₂), (v : G) = ℓ * u * ℓ⁻¹ →
    Multiplicative.toAdd (β₂ v) =
      (((α ℓ)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).transpose.mulVec
        (Multiplicative.toAdd (β₂ u))

variable {L W₁ W₂ : Subgroup G} {F : Type} [Field F]
  {α : ↥L →* Matrix.SpecialLinearGroup (Fin 3) F}
  {βU : ↥(centerOf (pCoreOf 2 L)) →* Multiplicative (Fin 3 → F)}
  {β₁ : ↥W₁ →* Multiplicative (Fin 3 → F)} {β₂ : ↥W₂ →* Multiplicative (Fin 3 → F)}

theorem burnsideC135_dsg_of_dualSplit
    (hD : DualSplit L (centerOf (pCoreOf 2 L)) W₁ W₂ α βU β₁ β₂) :
    burnsideC135_DSG (pCoreOf 2 L) L W₁ W₂ α βU β₁ β₂ :=
  ⟨hD.alpha_onto, CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L, hD.le₁, hD.le₂, hD.le_Q₁,
    hD.le_Q₂, hD.join, hD.meet, hD.norm₁, hD.norm₂, hD.natU_onto, hD.natU_ker, hD.natU_act,
    hD.dual₁_onto, hD.dual₁_ker, hD.dual₁_act, hD.dual₂_onto, hD.dual₂_ker, hD.dual₂_act⟩

theorem burnsideC135_dualSplit_of_dsg
    (hD : burnsideC135_DSG (pCoreOf 2 L) L W₁ W₂ α βU β₁ β₂) (hker : α.ker = CFSG.pCore 2 ↥L) :
    DualSplit L (centerOf (pCoreOf 2 L)) W₁ W₂ α βU β₁ β₂ :=
  ⟨hD.alpha_onto, hker, hD.le₁, hD.le₂, hD.le_Q₁, hD.le_Q₂, hD.join, hD.meet, hD.norm₁, hD.norm₂,
    hD.natU_onto, hD.natU_ker, hD.natU_act, hD.dual₁_onto, hD.dual₁_ker, hD.dual₁_act,
    hD.dual₂_onto, hD.dual₂_ker, hD.dual₂_act⟩

end Struct

section Split

variable [Finite G] {Q L W₁ W₂ : Subgroup G} {F : Type} [Field F] [Fintype F] [CharP F 2]
  {α : ↥L →* Matrix.SpecialLinearGroup (Fin 3) F}
  {βU : ↥(centerOf Q) →* Multiplicative (Fin 3 → F)}
  {β₁ : ↥W₁ →* Multiplicative (Fin 3 → F)} {β₂ : ↥W₂ →* Multiplicative (Fin 3 → F)}

theorem burnsideC135_dualSplit_symm
    (hD : burnsideC135_DSG Q L W₁ W₂ α βU β₁ β₂) :
    burnsideC135_DSG Q L W₂ W₁ α βU β₂ β₁ :=
  ⟨hD.alpha_onto, hD.normQ, hD.le₂, hD.le₁, hD.le_Q₂, hD.le_Q₁,
    by rw [sup_comm]; exact hD.join, by rw [inf_comm]; exact hD.meet, hD.norm₂, hD.norm₁,
    hD.natU_onto, hD.natU_ker, hD.natU_act, hD.dual₂_onto, hD.dual₂_ker, hD.dual₂_act,
    hD.dual₁_onto, hD.dual₁_ker, hD.dual₁_act⟩

theorem burnsideC135_βU_injective
    (hD : burnsideC135_DSG Q L W₁ W₂ α βU β₁ β₂) : Function.Injective βU := by
  rw [← MonoidHom.ker_eq_bot_iff]
  exact hD.natU_ker

theorem burnsideC135_U_comm {u x : G} (hu : u ∈ centerOf (Q)) (hx : x ∈ Q) :
    u * x = x * u :=
  (Subgroup.mem_centralizer_iff.mp hu.2 x hx).symm

theorem burnsideC135_U_sq (hD : burnsideC135_DSG Q L W₁ W₂ α βU β₁ β₂) {u : G}
    (hu : u ∈ centerOf (Q)) : u * u = 1 := by
  have h1 : βU (⟨u, hu⟩ * ⟨u, hu⟩) = 1 := by
    rw [map_mul]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one]
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have h2 := burnsideC135_βU_injective hD (h1.trans (map_one βU).symm)
  exact congrArg Subtype.val h2

theorem burnsideC135_le_normalizer_centerOf {X H : Subgroup G}
    (h : H ≤ Subgroup.normalizer (X : Set G)) :
    H ≤ Subgroup.normalizer (centerOf X : Set G) := by
  have key : ∀ g ∈ H, ∀ c ∈ centerOf X, g * c * g⁻¹ ∈ centerOf X := by
    intro g hg c hc
    refine ⟨(Subgroup.mem_normalizer_iff.mp (h hg) c).mp hc.1,
      Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g ∈ X := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (h (H.inv_mem hg)) y).mp hy
      simpa using h1
    have h2 := Subgroup.mem_centralizer_iff.mp hc.2 _ hy'
    calc y * (g * c * g⁻¹) = g * ((g⁻¹ * y * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * y * g)) * g⁻¹ := by rw [h2]
      _ = g * c * g⁻¹ * y := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key g hg c, fun hc => ?_⟩
  have := key g⁻¹ (H.inv_mem hg) _ hc
  simpa [mul_assoc] using this

theorem burnsideC135_dual_sq (hD : burnsideC135_DSG Q L W₁ W₂ α βU β₁ β₂)
    {W : Subgroup G} (hUW : centerOf (Q) ≤ W) (hWQ : W ≤ Q)
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) {β : ↥W →* Multiplicative (Fin 3 → F)}
    (hβs : Function.Surjective β) (hβk : β.ker = (centerOf (Q)).subgroupOf W)
    (hβact : ∀ (ℓ : ↥L) (u v : ↥W), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        (((α ℓ)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F).transpose.mulVec (Multiplicative.toAdd (β u)))
    {w : G} (hw : w ∈ W) : w * w = 1 := by
  classical
  have hsqU : ∀ v : ↥W, ((v : G) * v) ∈ centerOf (Q) := by
    intro v
    have h1 : v * v ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_one]
      funext i
      simp only [Pi.add_apply, Pi.zero_apply]
      exact CharTwo.add_self_eq_zero _
    rw [hβk, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hsq_eq : ∀ v v' : ↥W, β v = β v' → (v : G) * v = (v' : G) * v' := by
    intro v v' h
    have hk : v⁻¹ * v' ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    rw [hβk, Subgroup.mem_subgroupOf] at hk
    set u := ((v⁻¹ * v' : ↥W) : G) with hu
    have hv' : (v' : G) = v * u := by rw [hu]; simp
    have huc : u * v = v * u := burnsideC135_U_comm hk (hWQ v.2)
    have huu : u * u = 1 := burnsideC135_U_sq hD hk
    rw [hv']
    symm
    calc (v : G) * u * (v * u) = v * (u * v) * u := by group
      _ = v * (v * u) * u := by rw [huc]
      _ = v * v * (u * u) := by group
      _ = v * v := by rw [huu, mul_one]
  let s : (Fin 3 → F) → ↥W := fun x => Function.surjInv hβs (Multiplicative.ofAdd x)
  have hs : ∀ x, β (s x) = Multiplicative.ofAdd x := fun x => Function.surjInv_eq hβs _
  let φ : (Fin 3 → F) → (Fin 3 → F) := fun x =>
    Multiplicative.toAdd (βU ⟨(s x : G) * s x, hsqU (s x)⟩)
  have hLU : L ≤ Subgroup.normalizer (centerOf (Q) : Set G) :=
    burnsideC135_le_normalizer_centerOf hD.normQ
  have hφ : ∀ (γ : Matrix.SpecialLinearGroup (Fin 3) F) (v : Fin 3 → F),
      φ (((dualHom γ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) =
        (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ φ v := by
    intro γ v
    obtain ⟨l, hl⟩ := hD.alpha_onto γ
    set x' := ((dualHom γ : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) *ᵥ v with hx'
    have hmem : (l : G) * s v * (l : G)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hLW l.2) _).mp (s v).2
    have hβw' : β ⟨_, hmem⟩ = β (s x') := by
      rw [hs]
      apply Multiplicative.toAdd.injective
      rw [hβact l (s v) ⟨_, hmem⟩ rfl, hs, hl, hx', coe_dualHom]
      rfl
    have hsq := hsq_eq _ _ hβw'
    have hmemU : (l : G) * ((s v : G) * s v) * (l : G)⁻¹ ∈ centerOf (Q) :=
      (Subgroup.mem_normalizer_iff.mp (hLU l.2) _).mp (hsqU (s v))
    have e1 : (⟨(s x' : G) * s x', hsqU (s x')⟩ : ↥(centerOf (Q))) =
        ⟨(l : G) * ((s v : G) * s v) * (l : G)⁻¹, hmemU⟩ := by
      apply Subtype.ext
      show (s x' : G) * s x' = (l : G) * ((s v : G) * s v) * (l : G)⁻¹
      rw [← hsq]
      show (l : G) * s v * (l : G)⁻¹ * ((l : G) * s v * (l : G)⁻¹) = _
      group
    have e2 := hD.natU_act l ⟨_, hsqU (s v)⟩ ⟨_, hmemU⟩ rfl
    show Multiplicative.toAdd (βU ⟨(s x' : G) * s x', hsqU (s x')⟩) = _
    rw [e1, e2, hl]
  have hφ0 := eq_zero_of_dual_equivariant φ hφ
  have h1 : (w : G) * w = (s (Multiplicative.toAdd (β ⟨w, hw⟩)) : G) *
      s (Multiplicative.toAdd (β ⟨w, hw⟩)) :=
    hsq_eq ⟨w, hw⟩ (s (Multiplicative.toAdd (β ⟨w, hw⟩))) (by rw [hs]; rfl)
  have h2 : βU ⟨(s (Multiplicative.toAdd (β ⟨w, hw⟩)) : G) *
      s (Multiplicative.toAdd (β ⟨w, hw⟩)), hsqU _⟩ = 1 := by
    apply Multiplicative.toAdd.injective
    exact hφ0 _
  have h3 := burnsideC135_βU_injective hD (h2.trans (map_one βU).symm)
  rw [h1]
  exact congrArg Subtype.val h3

theorem burnsideC135_W_sq (hD : burnsideC135_DSG Q L W₁ W₂ α βU β₁ β₂) :
    (∀ w ∈ W₁, w * w = 1) ∧ (∀ w ∈ W₂, w * w = 1) :=
  ⟨fun _ hw => burnsideC135_dual_sq hD hD.le₁ hD.le_Q₁ hD.norm₁ hD.dual₁_onto hD.dual₁_ker
      hD.dual₁_act hw,
    fun _ hw => burnsideC135_dual_sq hD hD.le₂ hD.le_Q₂ hD.norm₂ hD.dual₂_onto hD.dual₂_ker
      hD.dual₂_act hw⟩

theorem burnsideC135_comm_of_sq {W : Subgroup G} (h : ∀ w ∈ W, w * w = 1) {x y : G}
    (hx : x ∈ W) (hy : y ∈ W) : x * y = y * x := by
  have h1 := h _ (W.mul_mem hx hy)
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (h x hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (h y hy)
  calc x * y = (y⁻¹ * x⁻¹) := (eq_inv_of_mul_eq_one_left (by rw [← mul_assoc] at h1 ⊢; exact
        (by simpa [mul_assoc] using h1))).trans (by group)
    _ = y * x := by rw [hx', hy']

theorem burnsideC135_commutator_mul_central {a b u u' : G} (hub : u * b = b * u)
    (hu'a : u' * a = a * u') (hu'u : u' * u = u * u') :
    (a * u) * (b * u') * (a * u)⁻¹ * (b * u')⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have hu'a' : u' * a⁻¹ = a⁻¹ * u' := by
    calc u' * a⁻¹ = a⁻¹ * (a * u') * a⁻¹ := by group
      _ = a⁻¹ * (u' * a) * a⁻¹ := by rw [hu'a]
      _ = a⁻¹ * u' := by group
  calc (a * u) * (b * u') * (a * u)⁻¹ * (b * u')⁻¹ =
        a * (u * b) * u' * u⁻¹ * a⁻¹ * u'⁻¹ * b⁻¹ := by group
    _ = a * (b * u) * u' * u⁻¹ * a⁻¹ * u'⁻¹ * b⁻¹ := by rw [hub]
    _ = a * b * (u * u') * u⁻¹ * a⁻¹ * u'⁻¹ * b⁻¹ := by group
    _ = a * b * (u' * u) * u⁻¹ * a⁻¹ * u'⁻¹ * b⁻¹ := by rw [hu'u]
    _ = a * b * (u' * a⁻¹) * u'⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * u') * u'⁻¹ * b⁻¹ := by rw [hu'a']
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem burnsideC135_commute_iff (hD : burnsideC135_DSG Q L W₁ W₂ α βU β₁ β₂)
    (hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ centerOf (Q))
    (w : ↥W₁) (hw : (w : G) ∉ centerOf (Q)) (y : ↥W₂) :
    (w : G) * y = y * w ↔
      ∃ c : F, Multiplicative.toAdd (β₂ y) = c • Multiplicative.toAdd (β₁ w) := by
  classical
  obtain ⟨hsq₁, hsq₂⟩ := burnsideC135_W_sq hD
  have hLU : L ≤ Subgroup.normalizer (centerOf (Q) : Set G) :=
    burnsideC135_le_normalizer_centerOf hD.normQ
  let cm : ↥W₁ → ↥W₂ → ↥(centerOf (Q)) := fun a b =>
    ⟨(a : G) * b * (a : G)⁻¹ * (b : G)⁻¹, hcomm _ (hD.le_Q₁ a.2) _ (hD.le_Q₂ b.2)⟩
  have hwell : ∀ (a a' : ↥W₁) (b b' : ↥W₂), β₁ a = β₁ a' → β₂ b = β₂ b' → cm a b = cm a' b' := by
    intro a a' b b' ha hb
    have hka : a⁻¹ * a' ∈ β₁.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, ha, inv_mul_cancel]
    have hkb : b⁻¹ * b' ∈ β₂.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hb, inv_mul_cancel]
    rw [hD.dual₁_ker, Subgroup.mem_subgroupOf] at hka
    rw [hD.dual₂_ker, Subgroup.mem_subgroupOf] at hkb
    have hka' : (a : G)⁻¹ * a' ∈ centerOf (Q) := by simpa using hka
    have hkb' : (b : G)⁻¹ * b' ∈ centerOf (Q) := by simpa using hkb
    apply Subtype.ext
    show (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ = (a' : G) * b' * (a' : G)⁻¹ * (b' : G)⁻¹
    have ha' : (a' : G) = a * ((a : G)⁻¹ * a') := by group
    have hb' : (b' : G) = b * ((b : G)⁻¹ * b') := by group
    rw [ha', hb']
    exact (burnsideC135_commutator_mul_central (burnsideC135_U_comm hka' (hD.le_Q₂ b.2))
      (burnsideC135_U_comm hkb' (hD.le_Q₁ a.2))
      (burnsideC135_U_comm hkb' (hD.le_Q₁ (hD.le₁ hka')))).symm
  have hcmL : ∀ (l : ↥L) (a : ↥W₁) (b : ↥W₂),
      ((cm ⟨(l : G) * a * (l : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hD.norm₁ l.2) _).mp a.2⟩
        ⟨(l : G) * b * (l : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hD.norm₂ l.2) _).mp b.2⟩ :
          ↥(centerOf (Q))) : G) = (l : G) * (cm a b) * (l : G)⁻¹ := by
    intro l a b
    show (l : G) * a * (l : G)⁻¹ * ((l : G) * b * (l : G)⁻¹) * ((l : G) * a * (l : G)⁻¹)⁻¹ *
      ((l : G) * b * (l : G)⁻¹)⁻¹ = (l : G) * ((a : G) * b * (a : G)⁻¹ * (b : G)⁻¹) * (l : G)⁻¹
    group
  let s₁ : (Fin 3 → F) → ↥W₁ := fun x => Function.surjInv hD.dual₁_onto (Multiplicative.ofAdd x)
  let s₂ : (Fin 3 → F) → ↥W₂ := fun z => Function.surjInv hD.dual₂_onto (Multiplicative.ofAdd z)
  have hs₁ : ∀ x, β₁ (s₁ x) = Multiplicative.ofAdd x := fun x => Function.surjInv_eq _ _
  have hs₂ : ∀ z, β₂ (s₂ z) = Multiplicative.ofAdd z := fun z => Function.surjInv_eq _ _
  let Bf : (Fin 3 → F) → (Fin 3 → F) → (Fin 3 → F) := fun x z =>
    Multiplicative.toAdd (βU (cm (s₁ x) (s₂ z)))
  have hBf : ∀ (a : ↥W₁) (b : ↥W₂), Bf (Multiplicative.toAdd (β₁ a)) (Multiplicative.toAdd (β₂ b)) =
      Multiplicative.toAdd (βU (cm a b)) := by
    intro a b
    show Multiplicative.toAdd (βU (cm (s₁ _) (s₂ _))) = _
    rw [hwell (s₁ _) a (s₂ _) b (by rw [hs₁]; rfl) (by rw [hs₂]; rfl)]
  have hBfeq : ∀ (γ : Matrix.SpecialLinearGroup (Fin 3) F) (x z : Fin 3 → F),
      Bf (((dualHom γ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x)
        (((dualHom γ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ z) =
      (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ Bf x z := by
    intro γ x z
    obtain ⟨l, hl⟩ := hD.alpha_onto γ
    set a' : ↥W₁ := ⟨(l : G) * s₁ x * (l : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hD.norm₁ l.2) _).mp (s₁ x).2⟩ with ha'
    set b' : ↥W₂ := ⟨(l : G) * s₂ z * (l : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hD.norm₂ l.2) _).mp (s₂ z).2⟩ with hb'
    have h1 : Multiplicative.toAdd (β₁ a') =
        ((dualHom γ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x := by
      rw [hD.dual₁_act l (s₁ x) a' rfl, hs₁, hl, coe_dualHom]
      rfl
    have h2 : Multiplicative.toAdd (β₂ b') =
        ((dualHom γ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ z := by
      rw [hD.dual₂_act l (s₂ z) b' rfl, hs₂, hl, coe_dualHom]
      rfl
    rw [← h1, ← h2, hBf]
    have hmemU : (l : G) * (cm (s₁ x) (s₂ z)) * (l : G)⁻¹ ∈ centerOf (Q) :=
      (Subgroup.mem_normalizer_iff.mp (hLU l.2) _).mp (cm (s₁ x) (s₂ z)).2
    have e1 : cm a' b' = ⟨_, hmemU⟩ := Subtype.ext (hcmL l (s₁ x) (s₂ z))
    rw [e1, hD.natU_act l (cm (s₁ x) (s₂ z)) ⟨_, hmemU⟩ rfl, hl]
  have hzero : ∀ (c : F) (x : Fin 3 → F), Bf x (c • x) = 0 := by
    intro c
    refine eq_zero_of_dual_equivariant (fun x => Bf x (c • x)) fun γ v => ?_
    show Bf _ (c • _) = _
    rw [← Matrix.mulVec_smul, hBfeq]
  have hadd : ∀ x z z', Bf x (z + z') = Bf x z + Bf x z' := by
    intro x z z'
    have hmul : β₂ (s₂ z * s₂ z') = β₂ (s₂ (z + z')) := by
      rw [map_mul, hs₂, hs₂, hs₂]
      rfl
    have h1 : Bf x (z + z') = Multiplicative.toAdd (βU (cm (s₁ x) (s₂ z * s₂ z'))) := by
      show Multiplicative.toAdd (βU (cm (s₁ x) (s₂ (z + z')))) = _
      rw [hwell (s₁ x) (s₁ x) (s₂ (z + z')) (s₂ z * s₂ z') rfl hmul.symm]
    have hc' : (cm (s₁ x) (s₂ z') : G) * s₂ z = s₂ z * cm (s₁ x) (s₂ z') :=
      burnsideC135_U_comm (cm (s₁ x) (s₂ z')).2 (hD.le_Q₂ (s₂ z).2)
    have h2 : cm (s₁ x) (s₂ z * s₂ z') = cm (s₁ x) (s₂ z) * cm (s₁ x) (s₂ z') := by
      apply Subtype.ext
      show (s₁ x : G) * (s₂ z * s₂ z') * (s₁ x : G)⁻¹ * ((s₂ z : G) * s₂ z')⁻¹ =
        (s₁ x : G) * s₂ z * (s₁ x : G)⁻¹ * (s₂ z : G)⁻¹ *
          ((s₁ x : G) * s₂ z' * (s₁ x : G)⁻¹ * (s₂ z' : G)⁻¹)
      have hc'' : ((s₁ x : G) * s₂ z' * (s₁ x : G)⁻¹ * (s₂ z' : G)⁻¹) * s₂ z =
          s₂ z * ((s₁ x : G) * s₂ z' * (s₁ x : G)⁻¹ * (s₂ z' : G)⁻¹) := hc'
      calc (s₁ x : G) * (s₂ z * s₂ z') * (s₁ x : G)⁻¹ * ((s₂ z : G) * s₂ z')⁻¹ =
            (s₁ x : G) * s₂ z * (s₁ x : G)⁻¹ * (s₂ z : G)⁻¹ *
              (((s₂ z : G) * ((s₁ x : G) * s₂ z' * (s₁ x : G)⁻¹ * (s₂ z' : G)⁻¹)) *
                (s₂ z : G)⁻¹) := by group
        _ = (s₁ x : G) * s₂ z * (s₁ x : G)⁻¹ * (s₂ z : G)⁻¹ *
              ((((s₁ x : G) * s₂ z' * (s₁ x : G)⁻¹ * (s₂ z' : G)⁻¹) * s₂ z) *
                (s₂ z : G)⁻¹) := by rw [hc'']
        _ = _ := by group
    rw [h1, h2, map_mul, toAdd_mul]
  set x := Multiplicative.toAdd (β₁ w) with hxdef
  have hx0 : x ≠ 0 := by
    intro h
    apply hw
    have h1 : w ∈ β₁.ker := by
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      exact h
    rw [hD.dual₁_ker, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hBf0 : Bf x 0 = 0 := by simpa using hzero 0 x
  let K : AddSubgroup (Fin 3 → F) :=
    { carrier := {z | Bf x z = 0}
      add_mem' := fun {a b} ha hb => by
        show Bf x (a + b) = 0
        rw [hadd, ha, hb, add_zero]
      zero_mem' := hBf0
      neg_mem' := fun {a} ha => by
        show Bf x (-a) = 0
        have h1 := hadd x (-a) a
        rw [neg_add_cancel, hBf0, ha, add_zero] at h1
        exact h1.symm }
  have hKx : ∀ c : F, c • x ∈ K := fun c => hzero c x
  have hKinv : ∀ δ : Matrix.SpecialLinearGroup (Fin 3) F,
      (δ : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x → ∀ z ∈ K, (δ : Matrix (Fin 3) (Fin 3) F) *ᵥ z ∈ K := by
    intro δ hδ z hz
    show Bf x _ = 0
    have h1 := hBfeq (dualHom δ) x z
    rw [dualHom_dualHom, hδ] at h1
    rw [h1]
    show (dualHom δ : Matrix (Fin 3) (Fin 3) F) *ᵥ Bf x z = 0
    rw [show Bf x z = 0 from hz, Matrix.mulVec_zero]
  have hker : ∀ z, Bf x z = 0 ↔ ∃ c : F, z = c • x := by
    intro z
    refine ⟨fun hz => ?_, fun ⟨c, hc⟩ => hc ▸ hzero c x⟩
    by_contra hcon
    push Not at hcon
    have htop := burnsideC135_eq_top_of_stab_invariant hx0 K hKx hKinv hz hcon
    apply hw
    have hcW₂ : W₂ ≤ Subgroup.centralizer ({(w : G)} : Set G) := by
      intro b hb
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : Multiplicative.toAdd (β₂ ⟨b, hb⟩) ∈ K := by rw [htop]; exact AddSubgroup.mem_top _
      have h2 : Bf x (Multiplicative.toAdd (β₂ ⟨b, hb⟩)) = 0 := h1
      rw [hxdef, hBf] at h2
      have h3 : βU (cm w ⟨b, hb⟩) = 1 := Multiplicative.toAdd.injective h2
      have h4 := burnsideC135_βU_injective hD (h3.trans (map_one βU).symm)
      have h5 : (w : G) * b * (w : G)⁻¹ * b⁻¹ = 1 := congrArg Subtype.val h4
      calc b * (w : G) = ((w : G) * b * (w : G)⁻¹ * b⁻¹)⁻¹ * (w * b) := by group
        _ = w * b := by rw [h5, inv_one, one_mul]
    have hcW₁ : W₁ ≤ Subgroup.centralizer ({(w : G)} : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact burnsideC135_comm_of_sq hsq₁ ha w.2
    have hcQ : Q ≤ Subgroup.centralizer ({(w : G)} : Set G) := by
      rw [← hD.join]
      exact sup_le hcW₁ hcW₂
    refine ⟨hD.le_Q₁ w.2, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
    have := hcQ hq
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  have hiff : (w : G) * y = y * w ↔ Bf x (Multiplicative.toAdd (β₂ y)) = 0 := by
    rw [hxdef, hBf]
    constructor
    · intro h
      have h1 : cm w y = 1 := by
        apply Subtype.ext
        show (w : G) * y * (w : G)⁻¹ * (y : G)⁻¹ = 1
        rw [h]
        group
      rw [h1, map_one]
      rfl
    · intro h
      have h3 : βU (cm w y) = 1 := Multiplicative.toAdd.injective h
      have h4 := burnsideC135_βU_injective hD (h3.trans (map_one βU).symm)
      have h5 : (w : G) * y * (w : G)⁻¹ * (y : G)⁻¹ = 1 := congrArg Subtype.val h4
      calc (w : G) * y = ((w : G) * y * (w : G)⁻¹ * (y : G)⁻¹) * (y * w) := by group
        _ = y * w := by rw [h5, one_mul]
  rw [hiff, hker]

theorem burnsideC135_card_U (hD : burnsideC135_DSG Q L W₁ W₂ α βU β₁ β₂) :
    Nat.card ↥(centerOf (Q)) = Fintype.card F ^ 3 := by
  have hbij : Function.Bijective βU := ⟨burnsideC135_βU_injective hD, hD.natU_onto⟩
  rw [Nat.card_congr ((Equiv.ofBijective _ hbij).trans Multiplicative.toAdd), Nat.card_eq_fintype_card,
    Fintype.card_fun, Fintype.card_fin]

theorem burnsideC135_card_dual (hD : burnsideC135_DSG Q L W₁ W₂ α βU β₁ β₂)
    {W : Subgroup G} (hUW : centerOf (Q) ≤ W) {β : ↥W →* Multiplicative (Fin 3 → F)}
    (hβs : Function.Surjective β) (hβk : β.ker = (centerOf (Q)).subgroupOf W) :
    Nat.card W = Fintype.card F ^ 6 := by
  have h1 := Subgroup.card_ker_mul_card_range β
  rw [MonoidHom.range_eq_top_of_surjective β hβs, Subgroup.card_top, hβk,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUW).toEquiv, burnsideC135_card_U hD] at h1
  rw [← h1, Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun,
    Fintype.card_fin]
  ring

theorem burnsideC135_isE2_W (hD : burnsideC135_DSG Q L W₁ W₂ α βU β₁ β₂)
    {n : ℕ} (hF : Fintype.card F = 2 ^ n) : IsE2 (6 * n) ↥W₁ ∧ IsE2 (6 * n) ↥W₂ := by
  obtain ⟨hsq₁, hsq₂⟩ := burnsideC135_W_sq hD
  have hc : ∀ q : ℕ, q = Fintype.card F → q ^ 6 = 2 ^ (6 * n) := by
    intro q hq
    rw [hq, hF, ← pow_mul, mul_comm]
  refine ⟨MS93.isE2_of_card (fun a b => Subtype.ext (burnsideC135_comm_of_sq hsq₁ a.2 b.2))
    (fun a => Subtype.ext (hsq₁ _ a.2)) ?_,
    MS93.isE2_of_card (fun a b => Subtype.ext (burnsideC135_comm_of_sq hsq₂ a.2 b.2))
    (fun a => Subtype.ext (hsq₂ _ a.2)) ?_⟩
  · rw [burnsideC135_card_dual hD hD.le₁ hD.dual₁_onto hD.dual₁_ker, hc _ rfl]
  · rw [burnsideC135_card_dual hD hD.le₂ hD.dual₂_onto hD.dual₂_ker, hc _ rfl]

theorem burnsideC135_le_normalizer_W₁
    (hD : burnsideC135_DSG Q L W₁ W₂ α βU β₁ β₂)
    (hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ centerOf (Q)) :
    Q ≤ Subgroup.normalizer (W₁ : Set G) := by
  have key : ∀ q ∈ Q, ∀ a ∈ W₁, q * a * q⁻¹ ∈ W₁ := by
    intro q hq a ha
    have h1 := hD.le₁ (hcomm q hq a (hD.le_Q₁ ha))
    have e : q * a * q⁻¹ = (q * a * q⁻¹ * a⁻¹) * a := by group
    rw [e]
    exact W₁.mul_mem h1 ha
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨key q hq a, fun h => ?_⟩
  have := key q⁻¹ ((Q).inv_mem hq) _ h
  simpa [mul_assoc] using this

theorem burnsideC135_relIndex (hD : burnsideC135_DSG Q L W₁ W₂ α βU β₁ β₂)
    (hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ centerOf (Q))
    (w : ↥W₁) (hw : (w : G) ∉ centerOf (Q)) :
    W₁.relIndex (Q ⊓ Subgroup.centralizer ({(w : G)} : Set G)) = Fintype.card F := by
  classical
  obtain ⟨hsq₁, -⟩ := burnsideC135_W_sq hD
  set Y := W₂ ⊓ Subgroup.centralizer ({(w : G)} : Set G) with hY
  set C := Q ⊓ Subgroup.centralizer ({(w : G)} : Set G) with hC
  have hW₁C : W₁ ≤ C := fun a ha =>
    ⟨hD.le_Q₁ ha, Subgroup.mem_centralizer_singleton_iff.mpr (burnsideC135_comm_of_sq hsq₁ ha w.2)⟩
  have hQN := burnsideC135_le_normalizer_W₁ hD hcomm
  have hYN : Y ≤ Subgroup.normalizer (W₁ : Set G) := fun y hy => hQN (hD.le_Q₂ hy.1)
  have hCY : C = Y ⊔ W₁ := by
    refine le_antisymm (fun c hc => ?_) (sup_le (fun y hy => ⟨hD.le_Q₂ hy.1, hy.2⟩) hW₁C)
    have hcQ : c ∈ ((W₂ ⊔ W₁ : Subgroup G) : Set G) := by
      rw [sup_comm, hD.join]
      exact hc.1
    rw [Subgroup.coe_mul_of_left_le_normalizer_right W₂ W₁
      (fun b hb => hQN (hD.le_Q₂ hb))] at hcQ
    obtain ⟨b, hb, a, ha, rfl⟩ := hcQ
    have hbY : b ∈ Y := by
      refine ⟨hb, ?_⟩
      show b ∈ Subgroup.centralizer ({(w : G)} : Set G)
      have h1 : (b * a : G) ∈ Subgroup.centralizer ({(w : G)} : Set G) := hc.2
      rw [Subgroup.mem_centralizer_singleton_iff] at h1 ⊢
      have h2 : a * (w : G) = w * a := burnsideC135_comm_of_sq hsq₁ ha w.2
      calc b * (w : G) = b * a * w * a⁻¹ := by
            rw [mul_assoc b a, h2]; group
        _ = w * (b * a) * a⁻¹ := by rw [h1]
        _ = w * b := by group
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hbY) (Subgroup.mem_sup_right ha)
  have hW₁Y : W₁ ⊓ Y = centerOf (Q) := by
    refine le_antisymm (fun g hg => ?_) (fun u hu => ⟨hD.le₁ hu, hD.le₂ hu, ?_⟩)
    · rw [← hD.meet]
      exact ⟨hg.1, hg.2.1⟩
    · show u ∈ Subgroup.centralizer ({(w : G)} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact burnsideC135_U_comm hu (hD.le_Q₁ w.2)
  set x := Multiplicative.toAdd (β₁ w) with hx
  have hx0 : x ≠ 0 := by
    intro h
    apply hw
    have h1 : w ∈ β₁.ker := by
      rw [MonoidHom.mem_ker]
      exact Multiplicative.toAdd.injective h
    rw [hD.dual₁_ker, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hYW₂ : Y ≤ W₂ := inf_le_left
  let βY : ↥Y →* Multiplicative (Fin 3 → F) := β₂.comp (Subgroup.inclusion hYW₂)
  have hβYk : βY.ker = (centerOf (Q)).subgroupOf Y := by
    refine Subgroup.ext fun y => ?_
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show β₂ (Subgroup.inclusion hYW₂ y) = 1 ↔ _
    rw [← MonoidHom.mem_ker, hD.dual₂_ker, Subgroup.mem_subgroupOf]
    rfl
  have hrange : Nat.card βY.range = Fintype.card F := by
    have hinj : Function.Injective (fun c : F => Multiplicative.ofAdd (c • x)) := by
      intro c c' h
      exact smul_left_injective F hx0 (Multiplicative.ofAdd.injective h)
    have hset : (βY.range : Set (Multiplicative (Fin 3 → F))) =
        Set.range (fun c : F => Multiplicative.ofAdd (c • x)) := by
      ext z
      constructor
      · rintro ⟨y, rfl⟩
        have h1 := (burnsideC135_commute_iff hD hcomm w hw ⟨y, y.2.1⟩).mp (by
          have : (y : G) ∈ Subgroup.centralizer ({(w : G)} : Set G) := y.2.2
          rw [Subgroup.mem_centralizer_singleton_iff] at this
          exact this.symm)
        obtain ⟨c, hc⟩ := h1
        refine ⟨c, ?_⟩
        show Multiplicative.ofAdd (c • x) = β₂ (Subgroup.inclusion hYW₂ y)
        rw [← hc]
        rfl
      · rintro ⟨c, rfl⟩
        obtain ⟨y, hy⟩ := hD.dual₂_onto (Multiplicative.ofAdd (c • x))
        have h1 := (burnsideC135_commute_iff hD hcomm w hw y).mpr ⟨c, by rw [hy]; rfl⟩
        refine ⟨⟨y, y.2, ?_⟩, hy⟩
        show (y : G) ∈ Subgroup.centralizer ({(w : G)} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact h1.symm
    have h1 : Nat.card βY.range =
        Nat.card (Set.range (fun c : F => Multiplicative.ofAdd (c • x))) := by
      rw [← hset]
      rfl
    rw [h1, Nat.card_range_of_injective hinj, Nat.card_eq_fintype_card]
  have hYcard : Nat.card Y = Nat.card ↥(centerOf (Q)) * Fintype.card F := by
    have h1 := Subgroup.card_ker_mul_card_range βY
    have hUY : centerOf (Q) ≤ Y := hW₁Y ▸ inf_le_right
    rw [hβYk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUY).toEquiv, hrange] at h1
    exact h1.symm
  rw [hCY, CFSG.Quasithin.B6.relIndex_sup_eq_of_le_normalizer hYN]
  have h1 := Subgroup.relIndex_mul_card W₁ Y
  rw [hW₁Y, hYcard] at h1
  have hU0 : 0 < Nat.card ↥(centerOf (Q)) := Nat.card_pos
  rw [mul_comm (Nat.card _)] at h1
  exact Nat.eq_of_mul_eq_mul_right hU0 h1

theorem burnsideC135_card_centralizer (hD : burnsideC135_DSG Q L W₁ W₂ α βU β₁ β₂)
    (hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ centerOf (Q))
    (w : ↥W₁) (hw : (w : G) ∉ centerOf (Q)) :
    Nat.card ↥(W₂ ⊓ Subgroup.centralizer ({(w : G)} : Set G)) =
      Nat.card ↥(centerOf (Q)) * Fintype.card F := by
  classical
  set Y := W₂ ⊓ Subgroup.centralizer ({(w : G)} : Set G) with hY
  have hUY : centerOf (Q) ≤ Y := fun u hu => ⟨hD.le₂ hu, by
    show u ∈ Subgroup.centralizer ({(w : G)} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact burnsideC135_U_comm hu (hD.le_Q₁ w.2)⟩
  set x := Multiplicative.toAdd (β₁ w) with hx
  have hx0 : x ≠ 0 := by
    intro h
    apply hw
    have h1 : w ∈ β₁.ker := by
      rw [MonoidHom.mem_ker]
      exact Multiplicative.toAdd.injective h
    rw [hD.dual₁_ker, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hYW₂ : Y ≤ W₂ := inf_le_left
  let βY : ↥Y →* Multiplicative (Fin 3 → F) := β₂.comp (Subgroup.inclusion hYW₂)
  have hβYk : βY.ker = (centerOf (Q)).subgroupOf Y := by
    refine Subgroup.ext fun y => ?_
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show β₂ (Subgroup.inclusion hYW₂ y) = 1 ↔ _
    rw [← MonoidHom.mem_ker, hD.dual₂_ker, Subgroup.mem_subgroupOf]
    rfl
  have hinj : Function.Injective (fun c : F => Multiplicative.ofAdd (c • x)) := by
    intro c c' h
    exact smul_left_injective F hx0 (Multiplicative.ofAdd.injective h)
  have hset : (βY.range : Set (Multiplicative (Fin 3 → F))) =
      Set.range (fun c : F => Multiplicative.ofAdd (c • x)) := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      have h1 := (burnsideC135_commute_iff hD hcomm w hw ⟨y, y.2.1⟩).mp (by
        have : (y : G) ∈ Subgroup.centralizer ({(w : G)} : Set G) := y.2.2
        rw [Subgroup.mem_centralizer_singleton_iff] at this
        exact this.symm)
      obtain ⟨c, hc⟩ := h1
      refine ⟨c, ?_⟩
      show Multiplicative.ofAdd (c • x) = β₂ (Subgroup.inclusion hYW₂ y)
      rw [← hc]
      rfl
    · rintro ⟨c, rfl⟩
      obtain ⟨y, hy⟩ := hD.dual₂_onto (Multiplicative.ofAdd (c • x))
      have h1 := (burnsideC135_commute_iff hD hcomm w hw y).mpr ⟨c, by rw [hy]; rfl⟩
      refine ⟨⟨y, y.2, ?_⟩, hy⟩
      show (y : G) ∈ Subgroup.centralizer ({(w : G)} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact h1.symm
  have hrange : Nat.card βY.range = Fintype.card F := by
    have h1 : Nat.card βY.range =
        Nat.card (Set.range (fun c : F => Multiplicative.ofAdd (c • x))) := by
      rw [← hset]
      rfl
    rw [h1, Nat.card_range_of_injective hinj, Nat.card_eq_fintype_card]
  have h1 := Subgroup.card_ker_mul_card_range βY
  rw [hβYk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUY).toEquiv, hrange] at h1
  exact h1.symm

end Split


end CFSG.ASVolI

end
