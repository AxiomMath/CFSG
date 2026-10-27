module

public import CFSG.Quasithin.EmptyFaithful.SzN5Scalar
public import CFSG.Quasithin.EmptyFaithful.SzN3Lin2
public import CFSG.Quasithin.EmptyFaithful.SzN3R

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

section Helpers

variable {G : Type} [Group G]

theorem szN5_exists_not_pCore [Finite G] {L P : Subgroup G} {n : ℕ} (hlin : IsLin2Type L n)
    (hP : IsSylowTwoOf P L) : ∃ x ∈ P, x ∉ pCoreOf 2 L := by
  by_contra hno
  push Not at hno
  obtain ⟨F, hF, hFin, hcard, α, hαs, hαk, β, hβs, hβk, hβc⟩ := hlin
  have hS := isSylowTwoOf_top_subgroupOf hP
  have hŪ := isSylowTwoOf_top_map_of_surjective hS α hαs
  have hbot : (P.subgroupOf L).map α = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    have hxP : (x : G) ∈ P := Subgroup.mem_subgroupOf.mp hx
    have hxQ : x ∈ CFSG.pCore 2 ↥L := (szN4_mem_pCore_iff x).mpr (hno _ hxP)
    rw [← hαk] at hxQ
    exact MonoidHom.mem_ker.mp hxQ
  rw [hbot] at hŪ
  have h2 : ¬ 2 ∣ ((⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).subgroupOf ⊤).index := hŪ.2.2
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := Fintype.one_lt_card (α := F)
    rw [hcard] at this
    simp at this
  have h2F : (2 : F) = 0 := by
    have h0 : ((Fintype.card F : ℕ) : F) = 0 := Nat.cast_card_eq_zero F
    rw [hcard] at h0
    push_cast at h0
    exact (pow_eq_zero_iff hn0).mp h0
  let t : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  have ht1 : t ≠ 1 := by
    intro h
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simp [t] at this
  have h11 : (1 : F) + 1 = 0 := by rw [one_add_one_eq_two]; exact h2F
  have htv : (t : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 0, 1] := rfl
  have ht2 : t ^ 2 = 1 := by
    rw [pow_two]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, htv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h11]
  have hord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hdvd : 2 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
    have := orderOf_dvd_natCard t
    rwa [hord] at this
  apply h2
  rw [Subgroup.bot_subgroupOf, Subgroup.index_bot, Subgroup.card_top]
  exact hdvd

end Helpers


section Fixed

variable {F : Type} [Field F]

theorem szN5_fixed_proportional {g : Matrix.SpecialLinearGroup (Fin 2) F} (hg : g ≠ 1)
    {w₁ w₂ : Fin 2 → F} (h₁ : (g : Matrix (Fin 2) (Fin 2) F).mulVec w₁ = w₁)
    (h₂ : (g : Matrix (Fin 2) (Fin 2) F).mulVec w₂ = w₂) : w₁ 0 * w₂ 1 = w₁ 1 * w₂ 0 := by
  by_contra hD
  apply hg
  have hD0 : w₁ 0 * w₂ 1 - w₁ 1 * w₂ 0 ≠ 0 := sub_ne_zero.mpr hD
  let e0 : Fin 2 → F := ![1, 0]
  let e1 : Fin 2 → F := ![0, 1]
  have hE0 : (w₁ 0 * w₂ 1 - w₁ 1 * w₂ 0) • e0 = w₂ 1 • w₁ - w₁ 1 • w₂ := by
    ext i; fin_cases i <;> simp [e0] <;> ring
  have hE1 : (w₁ 0 * w₂ 1 - w₁ 1 * w₂ 0) • e1 = w₁ 0 • w₂ - w₂ 0 • w₁ := by
    ext i; fin_cases i <;> simp [e1] <;> ring
  have hf0 : (g : Matrix (Fin 2) (Fin 2) F).mulVec e0 = e0 := by
    have h := congrArg (fun v => (g : Matrix (Fin 2) (Fin 2) F).mulVec v) hE0
    simp only [Matrix.mulVec_smul, Matrix.mulVec_sub, h₁, h₂] at h
    rw [← hE0] at h
    exact smul_right_injective _ hD0 h
  have hf1 : (g : Matrix (Fin 2) (Fin 2) F).mulVec e1 = e1 := by
    have h := congrArg (fun v => (g : Matrix (Fin 2) (Fin 2) F).mulVec v) hE1
    simp only [Matrix.mulVec_smul, Matrix.mulVec_sub, h₁, h₂] at h
    rw [← hE1] at h
    exact smul_right_injective _ hD0 h
  have a00 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    have := congrFun hf0 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, e0] using this
  have a10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    have := congrFun hf0 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, e0] using this
  have a01 : (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    have := congrFun hf1 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, e1] using this
  have a11 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    have := congrFun hf1 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, e1] using this
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [a00, a10, a01, a11]

end Fixed


section VU

variable {G : Type} [Group G] [Finite G]

theorem szN5_VZ_le_blockU {T M L : Subgroup G} {hV : IsElemAbelian 2 (VZ T M)} {y : G}
    (hyN : y ∈ Subgroup.normalizer (VZ T M : Set G))
    (hfix : ∀ w : IntMod (VZ T M) hV, convI hV ⟨y, hyN⟩ w = w → w = 1) (hyL : y ∈ L)
    (hdec : ∀ v ∈ VZ T M, ∃ a ∈ blockU L, ∃ b ∈ Subgroup.centralizer (L : Set G), v = a * b) :
    VZ T M ≤ blockU L := by
  intro v hv
  obtain ⟨u, -, hu⟩ := szN3_exists_commutator_eq (U := ⊤) hyN (fun _ _ => Subgroup.mem_top _)
    (fun w _ h => hfix w h) (IntMod.mk hV ⟨v, hv⟩) (Subgroup.mem_top _)
  obtain ⟨a, ha, b, hb, hab⟩ := hdec u.val u.val_mem
  have hbc : b * y = y * b := (Subgroup.mem_centralizer_iff.mp hb y hyL).symm
  have hUy : y * a⁻¹ * y⁻¹ ∈ blockU L :=
    (Subgroup.mem_normalizer_iff.mp (szN4_mem_normalizer_blockU (Subgroup.le_normalizer hyL)) _).mp
      ((blockU L).inv_mem ha)
  have hcomm : ⁅u.val, y⁆ = a * (y * a⁻¹ * y⁻¹) := by
    rw [hab, commutatorElement_def]
    calc a * b * y * (a * b)⁻¹ * y⁻¹ = a * (b * y) * b⁻¹ * a⁻¹ * y⁻¹ := by group
      _ = a * (y * b) * b⁻¹ * a⁻¹ * y⁻¹ := by rw [hbc]
      _ = a * (y * a⁻¹ * y⁻¹) := by group
  have h2 : ⁅u.val, y⁆ = v := hu
  rw [← h2, hcomm]
  exact (blockU L).mul_mem ha hUy

end VU


section Act

variable {G : Type} [Group G] {L : Subgroup G} {F : Type} [Field F]

@[expose] def SzN5Act (β : ↥(blockU L) →* Multiplicative (Fin 2 → F)) (g : G)
    (A : Matrix (Fin 2) (Fin 2) F) : Prop :=
  ∀ u : ↥(blockU L), ∃ hu' : g * (u : G) * g⁻¹ ∈ blockU L,
    Multiplicative.toAdd (β ⟨g * (u : G) * g⁻¹, hu'⟩) = A.mulVec (Multiplicative.toAdd (β u))

theorem szN5Act_one (β : ↥(blockU L) →* Multiplicative (Fin 2 → F)) : SzN5Act β 1 1 := by
  intro u
  refine ⟨by simp, ?_⟩
  simp

theorem szN5Act_mul {β : ↥(blockU L) →* Multiplicative (Fin 2 → F)} {g h : G}
    {A B : Matrix (Fin 2) (Fin 2) F} (hg : SzN5Act β g A) (hh : SzN5Act β h B) :
    SzN5Act β (g * h) (A * B) := by
  intro u
  obtain ⟨hu₁, e₁⟩ := hh u
  obtain ⟨hu₂, e₂⟩ := hg ⟨h * (u : G) * h⁻¹, hu₁⟩
  have e : g * h * (u : G) * (g * h)⁻¹ = g * (h * (u : G) * h⁻¹) * g⁻¹ := by group
  refine ⟨by rw [e]; exact hu₂, ?_⟩
  have h1 : (⟨g * h * (u : G) * (g * h)⁻¹, by rw [e]; exact hu₂⟩ : ↥(blockU L)) =
      ⟨g * (h * (u : G) * h⁻¹) * g⁻¹, hu₂⟩ := Subtype.ext e
  rw [h1, e₂]
  simp only [e₁, Matrix.mulVec_mulVec]

theorem szN5Act_of_mem {α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) F}
    {β : ↥(blockU L) →* Multiplicative (Fin 2 → F)}
    (hβc : ∀ ℓ : ↥L, ∀ u v : ↥(blockU L), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    {g : G} (hg : g ∈ L) : SzN5Act β g (α ⟨g, hg⟩ : Matrix (Fin 2) (Fin 2) F) := by
  intro u
  have hgN : g ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hg
  have hu' : g * (u : G) * g⁻¹ ∈ blockU L :=
    (Subgroup.mem_normalizer_iff.mp (szN4_mem_normalizer_blockU hgN) u).mp u.2
  exact ⟨hu', hβc ⟨g, hg⟩ u ⟨g * (u : G) * g⁻¹, hu'⟩ rfl⟩

theorem szN5Act_of_smul {β : ↥(blockU L) →* Multiplicative (Fin 2 → F)} {g : G} {a : F}
    (h : ∀ u : ↥(blockU L), ∀ hu' : g * (u : G) * g⁻¹ ∈ blockU L,
      Multiplicative.toAdd (β ⟨g * (u : G) * g⁻¹, hu'⟩) = a • Multiplicative.toAdd (β u))
    (hgN : g ∈ Subgroup.normalizer (L : Set G)) :
    SzN5Act β g ((a • (1 : Matrix (Fin 2) (Fin 2) F))) := by
  intro u
  have hu' : g * (u : G) * g⁻¹ ∈ blockU L :=
    (Subgroup.mem_normalizer_iff.mp (szN4_mem_normalizer_blockU hgN) u).mp u.2
  refine ⟨hu', ?_⟩
  rw [h u hu']
  simp [Matrix.smul_mulVec]

end Act


section Proportional

variable {F : Type} [Field F]

theorem szN5_exists_smul {w w' : Fin 2 → F} (hw : w ≠ 0) (h : w' 0 * w 1 = w' 1 * w 0) :
    ∃ μ : F, w' = μ • w := by
  by_cases h0 : w 0 = 0
  · have h1 : w 1 ≠ 0 := by
      intro h1
      apply hw
      funext i; fin_cases i
      · exact h0
      · exact h1
    refine ⟨w' 1 / w 1, ?_⟩
    funext i; fin_cases i
    · have : w' 0 * w 1 = 0 := by rw [h, h0, mul_zero]
      have := (mul_eq_zero.mp this).resolve_right h1
      simp [h0, this]
    · simp [h1]
  · refine ⟨w' 0 / w 0, ?_⟩
    funext i; fin_cases i
    · simp [h0]
    · have : w' 1 = (w' 0 / w 0) * w 1 := by
        rw [div_mul_eq_mul_div, eq_div_iff h0]
        exact h.symm
      simpa using this

end Proportional


@[expose] def Lin2RLSylow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) →
      IsSylowTwoOf (R153 T V₁ Yp ⊓ L) L

section Main

variable {G : Type} [Group G] [Finite G]

theorem szN5_fpf_false (h113 : StageLemma14113) (kS : Lin2Setup) (kR : Lin2RLSylow)
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G} (ctx : Ctx15316 T Mc M V₁ V₂ Yp I L t)
    (hn : ∃ n : ℕ, 1 < n ∧ IsLin2Type L n) (hYY : Yp = Y153 Mc M)
    {hV : IsElemAbelian 2 (VZ T M)} {La Lb : Subgroup (MulAut (IntMod (VZ T M) hV))}
    {tb : MulAut (IntMod (VZ T M) hV)} (hS : OfourStruct (autI hV M) La Lb tb)
    {y : G} (hyYL : y ∈ YL153 Yp L) (hyN : y ∈ Subgroup.normalizer (VZ T M : Set G))
    (hfix : ∀ w : IntMod (VZ T M) hV, convI hV ⟨y, hyN⟩ w = w → w = 1) : False := by
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := ctx.ctx.hyp
  obtain ⟨hYpeq, hE9, hVdec⟩ := kS G T Mc M V₁ V₂ Yp I L t ctx hn
  have hRL := kR G T Mc M V₁ V₂ Yp I L t ctx hn
  subst hYY
  have hcore := szN3_core_eq h113 hh.hyp hE9
  have hMN := hh.hyp.le_normalizer
  set Y := Y153 Mc M with hY
  have hYM : Y ≤ M := Y153_le Mc M
  have hYN : Y ≤ Subgroup.normalizer (VZ T M : Set G) := hYM.trans hMN
  have hyL : y ∈ L := ((oTwoUpper_le _).trans inf_le_right) hyYL
  have hVU : VZ T M ≤ blockU L := szN5_VZ_le_blockU hyN hfix hyL fun v hv => by
    obtain ⟨a, ha, b, hb, hab⟩ := hVdec v hv
    exact ⟨a, ha.1, b, hb, hab⟩
  have hVZ : ∀ z ∈ VZ T M, z ∈ Subgroup.centralizer (L : Set G) → z = 1 := by
    intro z hz hzC
    have hyz : y * z = z * y := Subgroup.mem_centralizer_iff.mp hzC y hyL
    have h1 := hfix (IntMod.mk hV ⟨z, hz⟩) (IntMod.val_injective (by
      rw [convI_apply_val]
      show y * z * y⁻¹ = z
      rw [hyz]; group))
    exact congrArg IntMod.val h1
  obtain ⟨n, -, hnL⟩ := hn
  obtain ⟨x₀, hx₀P, hx₀Q⟩ := szN5_exists_not_pCore hnL hRL
  have hx₀L : x₀ ∈ L := hRL.1 hx₀P
  obtain ⟨F, hF, hFin, hcard, α, hαs, hαk, β, hβs, hβk, hβc⟩ := hnL
  have hg₀1 : α ⟨x₀, hx₀L⟩ ≠ 1 := by
    intro h
    apply hx₀Q
    have : (⟨x₀, hx₀L⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := hαk ▸ MonoidHom.mem_ker.mpr h
    exact (szN4_mem_pCore_iff _).mp this
  let θ : G → (Fin 2 → F) := fun v =>
    if h : v ∈ blockU L then Multiplicative.toAdd (β ⟨v, h⟩) else 0
  have hθ : ∀ (v : G) (h : v ∈ blockU L), θ v = Multiplicative.toAdd (β ⟨v, h⟩) := fun v h => by
    simp [θ, h]
  have hθmul : ∀ v v' : G, ∀ (hv : v ∈ blockU L) (hv' : v' ∈ blockU L),
      θ (v * v') = θ v + θ v' := by
    intro v v' hv hv'
    rw [hθ _ ((blockU L).mul_mem hv hv'), hθ v hv, hθ v' hv']
    have : (⟨v * v', (blockU L).mul_mem hv hv'⟩ : ↥(blockU L)) = ⟨v, hv⟩ * ⟨v', hv'⟩ := rfl
    rw [this, map_mul, toAdd_mul]
  have hθinj : ∀ v ∈ VZ T M, ∀ v' ∈ VZ T M, θ v = θ v' → v = v' := by
    intro v hv v' hv' h
    have hvU := hVU hv
    have hv'U := hVU hv'
    rw [hθ v hvU, hθ v' hv'U] at h
    have hβeq : β ⟨v, hvU⟩ = β ⟨v', hv'U⟩ := Multiplicative.toAdd.injective h
    have hm : (⟨v, hvU⟩ : ↥(blockU L))⁻¹ * ⟨v', hv'U⟩ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hβeq, inv_mul_cancel]
    rw [hβk, Subgroup.mem_subgroupOf] at hm
    have hVm : v⁻¹ * v' ∈ VZ T M := (VZ T M).mul_mem ((VZ T M).inv_mem hv) hv'
    have h1 : v⁻¹ * v' = 1 := hVZ _ hVm hm.2
    calc v = v * (v⁻¹ * v') := by rw [h1, mul_one]
      _ = v' := by group
  have hfixθ : ∀ v ∈ VZ T M,
      (α ⟨x₀, hx₀L⟩ : Matrix (Fin 2) (Fin 2) F).mulVec (θ v) = θ v := by
    intro v hv
    obtain ⟨a', ha', b', hb', hvab⟩ := hVdec v hv
    have hvU := hVU hv
    have hb'U : b' ∈ blockU L := by
      have : a'⁻¹ * v = b' := by rw [hvab]; group
      rw [← this]
      exact (blockU L).mul_mem ((blockU L).inv_mem ha'.1) hvU
    have hb'Z : (⟨b', hb'U⟩ : ↥(blockU L)) ∈ β.ker := by
      rw [hβk, Subgroup.mem_subgroupOf]
      exact ⟨hb'U, hb'⟩
    have hβb' : β ⟨b', hb'U⟩ = 1 := MonoidHom.mem_ker.mp hb'Z
    have hβv : β ⟨v, hvU⟩ = β ⟨a', ha'.1⟩ := by
      have : (⟨v, hvU⟩ : ↥(blockU L)) = ⟨a', ha'.1⟩ * ⟨b', hb'U⟩ := Subtype.ext hvab
      rw [this, map_mul, hβb', mul_one]
    have hxa : x₀ * a' * x₀⁻¹ = a' := by
      have := Subgroup.mem_centralizer_iff.mp ha'.2 x₀ hx₀P
      rw [this]; group
    have h := hβc ⟨x₀, hx₀L⟩ ⟨a', ha'.1⟩ ⟨a', ha'.1⟩ hxa.symm
    rw [hθ v hvU, hβv]
    exact h.symm
  have hprop : ∀ v ∈ VZ T M, ∀ v' ∈ VZ T M, θ v 0 * θ v' 1 = θ v 1 * θ v' 0 :=
    fun v hv v' hv' => szN5_fixed_proportional hg₀1 (hfixθ v hv) (hfixθ v' hv')
  have hscalar : ∀ c ∈ centralizerSection Y L (pCoreOf 2 L), ∃ A, SzN5Act β c A := by
    intro c hc
    obtain ⟨hcY, hcN, hcQN, hcc⟩ := mem_centralizerSection.mp hc
    have hcQ : ∀ x ∈ L, c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 L := by
      intro x hx
      have := (pCoreOf 2 L).inv_mem (hcc x hx)
      have e : (x * c * x⁻¹ * c⁻¹)⁻¹ = c * x * c⁻¹ * x⁻¹ := by group
      rwa [e] at this
    obtain ⟨a, ha⟩ := szN5_scalar_action α hαs hαk β hβs hβk hβc hcN hcQ
    exact ⟨_, szN5Act_of_smul ha hcN⟩
  have hact : ∀ g ∈ YL153 Y L ⊔ YC153 Y L, (∃ A, SzN5Act β g A) ∧ (∃ B, SzN5Act β g⁻¹ B) := by
    intro g hg
    rw [Subgroup.sup_eq_closure] at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · have hxL : x ∈ L := ((oTwoUpper_le _).trans inf_le_right) hx
        have hxiL : x⁻¹ ∈ L := L.inv_mem hxL
        exact ⟨⟨_, szN5Act_of_mem hβc hxL⟩, ⟨_, szN5Act_of_mem hβc hxiL⟩⟩
      · have hxc : x ∈ centralizerSection Y L (pCoreOf 2 L) := oTwoUpper_le _ hx
        exact ⟨hscalar x hxc, hscalar x⁻¹ ((centralizerSection Y L (pCoreOf 2 L)).inv_mem hxc)⟩
    | one => exact ⟨⟨1, szN5Act_one β⟩, ⟨1, by simpa using szN5Act_one β⟩⟩
    | mul x y _ _ hx hy =>
      obtain ⟨⟨A, hA⟩, ⟨A', hA'⟩⟩ := hx
      obtain ⟨⟨B, hB⟩, ⟨B', hB'⟩⟩ := hy
      refine ⟨⟨A * B, szN5Act_mul hA hB⟩, ⟨B' * A', ?_⟩⟩
      have := szN5Act_mul hB' hA'
      simpa [mul_inv_rev] using this
    | inv x _ hx => exact ⟨hx.2, by simpa using hx.1⟩
  have hYe : autI hV Y = oTwoUpper (autI hV M) := hh.hyp.autOn_Y153 h113
  have hθ1 : θ 1 = 0 := by
    rw [hθ 1 (blockU L).one_mem]
    have : (⟨1, (blockU L).one_mem⟩ : ↥(blockU L)) = 1 := rfl
    rw [this, map_one]
    simp
  obtain ⟨v₀, hv₀V, hv₀1⟩ : ∃ v ∈ VZ T M, v ≠ 1 := by
    by_contra hno
    push Not at hno
    have h1 := hh.decomp.card₁
    have hbot : V₁ = ⊥ := by
      rw [eq_bot_iff]
      exact fun v hv => Subgroup.mem_bot.mpr (hno v (hh.decomp.le₁ hv))
    rw [hbot] at h1
    simp at h1
  have hv₀ : θ v₀ ≠ 0 := fun h =>
    hv₀1 (hθinj v₀ hv₀V 1 (VZ T M).one_mem (by rw [h, hθ1]))
  have hgV : ∀ g ∈ Y, ∀ v ∈ VZ T M, g * v * g⁻¹ ∈ VZ T M := fun g hg v hv =>
    (Subgroup.mem_normalizer_iff.mp (hYN hg) v).mp hv
  have hKC : ∀ g ∈ Y, ∃ μ : F, ∀ v ∈ VZ T M, θ (g * v * g⁻¹) = μ • θ v := by
    intro g hgY
    obtain ⟨⟨A, hA⟩, -⟩ := hact g (by rw [← hYpeq]; exact hgY)
    have hAv : ∀ v ∈ VZ T M, θ (g * v * g⁻¹) = A.mulVec (θ v) := by
      intro v hv
      obtain ⟨hu', e⟩ := hA ⟨v, hVU hv⟩
      rw [hθ _ hu', hθ v (hVU hv)]
      exact e
    obtain ⟨μ, hμ⟩ := szN5_exists_smul hv₀ (hprop _ (hgV g hgY v₀ hv₀V) v₀ hv₀V)
    refine ⟨μ, fun v hv => ?_⟩
    obtain ⟨x, hx⟩ := szN5_exists_smul hv₀ (hprop v hv v₀ hv₀V)
    rw [hAv v hv, hx, Matrix.mulVec_smul, ← hAv v₀ hv₀V, hμ, smul_comm]
  have hcube : ∀ g ∈ Y, ∃ μ : F, μ ^ 3 = 1 ∧ ∀ v ∈ VZ T M, θ (g * v * g⁻¹) = μ • θ v := by
    intro g hgY
    obtain ⟨μ, hμ⟩ := hKC g hgY
    refine ⟨μ, ?_, hμ⟩
    have hgNV : g ∈ Subgroup.normalizer (VZ T M : Set G) := hYN hgY
    have hgbar : convI hV ⟨g, hgNV⟩ ∈ oTwoUpper (autI hV M) := by
      have := convI_mem_autI hV hgY hgNV
      rwa [hYe] at this
    have hg3 : (convI hV ⟨g, hgNV⟩) ^ 3 = 1 := hS.pow_three_of_mem_oTwoUpper hgbar
    have hthree : g * (g * (g * v₀ * g⁻¹) * g⁻¹) * g⁻¹ = v₀ := by
      have h := congrArg (fun φ : MulAut (IntMod (VZ T M) hV) =>
        (φ (IntMod.mk hV ⟨v₀, hv₀V⟩)).val) hg3
      simp only [pow_three', MulAut.mul_apply, convI_apply_val, MulAut.one_apply] at h
      exact h
    have hv1 := hgV g hgY v₀ hv₀V
    have hv2 := hgV g hgY _ hv1
    have e1 := hμ v₀ hv₀V
    have e2 := hμ _ hv1
    have e3 := hμ _ hv2
    rw [hthree] at e3
    rw [e2, e1, smul_smul, smul_smul] at e3
    have h0 : (μ ^ 3 - 1) • θ v₀ = 0 := by
      rw [sub_smul, one_smul, show μ ^ 3 = μ * μ * μ by ring, ← e3, sub_self]
    obtain ⟨i, hi⟩ : ∃ i, θ v₀ i ≠ 0 := by
      by_contra hno
      push Not at hno
      exact hv₀ (funext hno)
    have h1 := congrFun h0 i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact sub_eq_zero.mp h2
    · exact absurd h2 hi
  have hex : ∀ φ : ↥(autI hV Y), ∃ μ : F, μ ^ 3 = 1 ∧ ∀ v (hv : v ∈ VZ T M),
      θ ((φ.1 (IntMod.mk hV ⟨v, hv⟩)).val) = μ • θ v := by
    intro φ
    obtain ⟨g, hgY, hg⟩ := (mem_autI hV).1 φ.2
    obtain ⟨μ, hμ3, hμ⟩ := hcube g hgY
    refine ⟨μ, hμ3, fun v hv => ?_⟩
    have : (φ.1 (IntMod.mk hV ⟨v, hv⟩)).val = g * v * (g : G)⁻¹ := by
      rw [← hg, convI_apply_val]
      try rfl
    rw [this]
    exact hμ v hv
  choose f hf3 hfθ using hex
  have hfinj : Function.Injective (fun φ => (⟨f φ, hf3 φ⟩ : {μ : F // μ ^ 3 = 1})) := by
    intro φ₁ φ₂ h
    have hf : f φ₁ = f φ₂ := congrArg Subtype.val h
    apply Subtype.ext
    apply MulEquiv.ext
    intro w
    have hw : w = IntMod.mk hV ⟨w.val, w.val_mem⟩ := IntMod.val_injective rfl
    apply IntMod.val_injective
    apply hθinj _ (φ₁.1 w).val_mem _ (φ₂.1 w).val_mem
    have e1 := hfθ φ₁ w.val w.val_mem
    have e2 := hfθ φ₂ w.val w.val_mem
    rw [← hw] at e1 e2
    rw [e1, e2, hf]
  have hroots : Nat.card {μ : F // μ ^ 3 = 1} ≤ 3 := by
    classical
    have hsub : ∀ μ : F, μ ^ 3 = 1 → μ ∈ (Polynomial.nthRoots 3 (1 : F)).toFinset := by
      intro μ h
      rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by norm_num)]
      exact h
    have h1 : Nat.card {μ : F // μ ^ 3 = 1} ≤
        Nat.card ↥((Polynomial.nthRoots 3 (1 : F)).toFinset) := by
      refine Nat.card_le_card_of_injective
        (fun μ : {μ : F // μ ^ 3 = 1} =>
          (⟨μ.1, hsub μ.1 μ.2⟩ : ↥((Polynomial.nthRoots 3 (1 : F)).toFinset)))
        (fun a b h => Subtype.ext (Subtype.mk.inj h))
    rw [Nat.card_eq_finsetCard] at h1
    exact h1.trans ((Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots 3 1))
  have hcardY : Nat.card ↥(autI hV Y) = 9 := by
    have e1 := card_autI_mul_card_inf hV hYN
    have h9 := S153F.card_eq_nine_of_isElemAbelianOfRank hE9
    have e2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥Y)
    have e3 : Nat.card ↥(pCoreOf 2 Y) = Nat.card ↥(CFSG.Open.pCore 2 ↥Y) :=
      Subgroup.card_map_of_injective Y.subtype_injective
    have e4 : Nat.card ↥(Y ⊓ Subgroup.centralizer (VZ T M : Set G)) =
        Nat.card ↥(CFSG.Open.pCore 2 ↥Y) := by rw [← hcore]; exact e3
    rw [e4] at e1
    have hpos : 0 < Nat.card ↥(CFSG.Open.pCore 2 ↥Y) := Nat.card_pos
    have : Nat.card ↥(autI hV Y) * Nat.card ↥(CFSG.Open.pCore 2 ↥Y) =
        9 * Nat.card ↥(CFSG.Open.pCore 2 ↥Y) := by
      have h9' : Nat.card (↥Y ⧸ CFSG.Open.pCore 2 ↥Y) = 9 := h9
      rw [e1, e2, h9']
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hle := Nat.card_le_card_of_injective _ hfinj
  omega

end Main


section Label

variable {G : Type} [Group G] [Finite G]

theorem lin2YLLabel_of_RL (h113 : StageLemma14113) (kS : Lin2Setup) (kR : Lin2RLSylow) :
    Lin2YLLabel := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hn hYLV
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  rcases hh.cases with hYY | ⟨-, hY2⟩
  swap
  · left
    have h1 : Yp ≤ Subgroup.centralizer (V₁ : Set G) := by
      rw [hY2]
      exact (oTwoUpper_le _).trans inf_le_right
    exact ((oTwoUpper_le _).trans inf_le_left).trans h1
  obtain ⟨hV, L₁, L₂, tb, hS, hV₁, hV₂, -⟩ := hh.decomp.model
  have hMN := hh.hyp.le_normalizer
  have hYM : Yp ≤ M := hYY ▸ Y153_le Mc M
  have hYN : Yp ≤ Subgroup.normalizer (VZ T M : Set G) := hYM.trans hMN
  have hYLle : YL153 Yp L ≤ Yp ⊓ L := oTwoUpper_le _
  have hYLY : YL153 Yp L ≤ Yp := hYLle.trans inf_le_left
  have hYe : autI hV Yp = oTwoUpper (autI hV M) := hYY ▸ hh.hyp.autOn_Y153 h113
  have hall : ∀ (y : G) (hy : y ∈ YL153 Yp L), convI hV ⟨y, hYN (hYLY hy)⟩ ∈ L₁ ∨
      convI hV ⟨y, hYN (hYLY hy)⟩ ∈ L₂ := by
    intro y hy
    by_contra hno
    push Not at hno
    obtain ⟨hn1, hn2⟩ := hno
    have hyN : y ∈ Subgroup.normalizer (VZ T M : Set G) := hYN (hYLY hy)
    have hzY : convI hV ⟨y, hyN⟩ ∈ autI hV Yp := convI_mem_autI hV (hYLY hy) hyN
    rw [hYe] at hzY
    have hz3 : (convI hV ⟨y, hyN⟩) ^ 3 = 1 := hS.pow_three_of_mem_oTwoUpper hzY
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_commute hS.comm
      (hS.oTwoUpper_le_sup hzY)
    have hcomm : Commute a b := hS.comm a ha b hb
    have h3 : a ^ 3 * b ^ 3 = 1 := by rw [← hcomm.mul_pow, hab]; exact hz3
    have ha3 : a ^ 3 = 1 := by
      have : a ^ 3 ∈ L₁ ⊓ L₂ := ⟨L₁.pow_mem ha 3, by
        rw [eq_inv_of_mul_eq_one_left h3]
        exact L₂.inv_mem (L₂.pow_mem hb 3)⟩
      rw [hS.Linf, Subgroup.mem_bot] at this
      exact this
    have hb3 : b ^ 3 = 1 := by
      rw [ha3, one_mul] at h3
      exact h3
    have ha1 : a ≠ 1 := by
      rintro rfl
      rw [one_mul] at hab
      exact hn2 (hab ▸ hb)
    have hb1 : b ≠ 1 := by
      rintro rfl
      rw [mul_one] at hab
      exact hn1 (hab ▸ ha)
    have hfpf : ∀ w, convI hV ⟨y, hyN⟩ w = w → w = 1 := by
      rw [← hab]
      exact szN3_fpf_mul hS ha hb ha1 hb1 ha3 hb3
    exact szN5_fpf_false h113 kS kR c hn hYY hS hy hyN hfpf
  refine szN3_le_or_le_of_forall fun y hy => ?_
  have hyN : y ∈ Subgroup.normalizer (VZ T M : Set G) := hYN (hYLY hy)
  rcases hall y hy with h | h
  · right
    rw [hV₂]
    exact (mem_centralizer_map_inclMod_iff hV hyN (commV L₂)).2 fun u hu => hS.L₁_fix₂ h hu
  · left
    rw [hV₁]
    exact (mem_centralizer_map_inclMod_iff hV hyN (commV L₁)).2 fun u hu => hS.L₂_fix₁ h hu

end Label

end CFSG.Quasithin
