module

public import CFSG.RankThree.GF2n.Stroth80.Sec11BCent
public import CFSG.RankThree.GF2n.Stroth80.Sec12MixedRoot
public import CFSG.RankThree.GF2n.Stroth80.Sec111
public import CFSG.RankThree.GF2n.Smith81.LinTLOfConj
public import CFSG.RankThree.GF2n.Stroth80.Sec12Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank Matrix
  CFSG.ClassicalGroups.SpecialLinear
open scoped commutatorElement

section ElationCount

variable {F : Type} [Field F] [Finite F] {n : ℕ}

theorem card_statedSLElations_le (u : Fin n → F) (hu : u ≠ 0) :
    Nat.card (statedSLElations n F u) ≤ Nat.card F ^ (n - 1) := by
  classical
  haveI : Finite (Module.Dual F (Fin n → F)) := Module.finite_of_finite F
  have hex : ∀ A : statedSLElations n F u, ∃ f : Module.Dual F (Fin n → F), f u = 0 ∧
      ∀ x, (A.1 : Matrix (Fin n) (Fin n) F) *ᵥ x = x + f x • u := by
    intro A
    have hc : ∀ x : Fin n → F, ∃ c : F, (A.1 : Matrix (Fin n) (Fin n) F) *ᵥ x - x = c • u :=
      A.2.2.2
    choose c hc using hc
    have hcadd : ∀ x y, c (x + y) = c x + c y := fun x y => by
      apply smul_left_injective F hu
      simp only [add_smul, ← hc, Matrix.mulVec_add]
      abel
    have hcsmul : ∀ (a : F) x, c (a • x) = a * c x := fun a x => by
      apply smul_left_injective F hu
      simp only [mul_smul, ← hc, Matrix.mulVec_smul, smul_sub]
    refine ⟨{ toFun := c, map_add' := hcadd, map_smul' := fun a x => hcsmul a x }, ?_, ?_⟩
    · apply smul_left_injective F hu
      have h1 := hc u
      rw [A.2.2.1, sub_self] at h1
      simpa using h1.symm
    · intro x
      have := hc x
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [← this]
      abel
  choose f hf0 hf using hex
  have hinj : Function.Injective (fun A : statedSLElations n F u =>
      (⟨f A, (Submodule.mem_dualAnnihilator _).mpr (fun w hw => by
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
        simp [hf0 A])⟩ : (Submodule.span F {u}).dualAnnihilator)) := by
    intro A B hAB
    have hfAB : f A = f B := congrArg Subtype.val hAB
    apply Subtype.ext
    apply Units.ext
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun x => ?_
    simp only [Matrix.toLin'_apply]
    rw [hf A x, hf B x, hfAB]
  have h1 := Nat.card_le_card_of_injective _ hinj
  refine h1.trans (le_of_eq ?_)
  rw [Module.natCard_eq_pow_finrank (K := F)]
  congr 1
  have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq (Submodule.span F {u})
  rw [finrank_span_singleton hu, Module.finrank_fin_fun] at h2
  omega

end ElationCount

section ElationOfLB

variable {G : Type} [Group G] [Finite G] {M Q Z A : Subgroup G}
  {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
  {F : Type} [Field F] [Finite F] {n : ℕ}

theorem elation_of_mem_LB (hcA : Ctx M Q Z A) (h : GlobalModelData M Q Z γ M₀)
    {S V : Subgroup G} (hSH : S ≤ H0 M Z) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (ρ' : ↥S →* GL (Fin n) F) (hrange : ρ'.range = StatedSL n F)
    (C : NatDualCoord (φ.comp (Subgroup.inclusion hSH)) ρ')
    (hV : ∀ e : M₀.E, e ∈ M₀.img V ↔ (C.Ψ e).2 = 0) (hAV : A ≤ V)
    (hLS : LB M Q A ≤ S) (hcomm : ∀ t ∈ LB M Q A, ∀ v ∈ V, ⁅v, t⁆ ∈ A ⊔ Z) :
    ∃ u : Fin n → F, u ≠ 0 ∧ (∀ e : M₀.E, e ∈ M₀.img A ↔ ∃ c : F, C.Ψ e = (c • u, 0)) ∧
      ∀ (t : G) (ht : t ∈ LB M Q A), (ρ' ⟨t, hLS ht⟩ : GL (Fin n) F) ∈
        statedSLElations n F u := by
  classical
  obtain ⟨b, hb0, hbs, hAline, hcent, -⟩ := hcA.dictB h
  have hbA : b ∈ M₀.img A := (hAline b).mpr ⟨1, (one_smul K b).symm⟩
  have hbV : b ∈ M₀.img V := M₀.img_mono hAV hbA
  have hb2 : (C.Ψ b).2 = 0 := (hV b).mp hbV
  set u : Fin n → F := (C.Ψ b).1 with hu
  have hΨb : C.Ψ b = (u, 0) := Prod.ext rfl hb2
  have hu0 : u ≠ 0 := by
    intro h0
    apply hb0
    apply C.Ψ.injective
    rw [hΨb, h0, map_zero]
    rfl
  have hline : ∀ e : M₀.E, e ∈ M₀.img A ↔ ∃ c : F, C.Ψ e = (c • u, 0) := by
    intro e
    rw [hAline]
    constructor
    · rintro ⟨s, rfl⟩
      refine ⟨C.θ₁ s, ?_⟩
      rw [C.smul, hΨb]
      simp
    · rintro ⟨c, hc⟩
      refine ⟨C.θ₁.symm c, ?_⟩
      apply C.Ψ.injective
      rw [C.smul, hΨb, hc]
      simp
  refine ⟨u, hu0, hline, ?_⟩
  intro t ht
  have hLH : t ∈ H0 M Z := hcA.LB_le_H0 ht
  have hQn : ∀ x ∈ Q, t * x * t⁻¹ ∈ Q := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hcA.hyp.Q_normal.2 (hcA.LB_le_M ht)) x).mp hx
  have hTπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = φ ⟨t, hLH⟩ (M₀.π x) := fun x hx =>
    hφπ ⟨t, hLH⟩ x hx
  have hfix := hcA.LB_act_fix_line h hAline ht (T := (φ ⟨t, hLH⟩ : M₀.E →ₗ[K] M₀.E)) hTπ
  have hAmem : (ρ' ⟨t, hLS ht⟩ : GL (Fin n) F) ∈ StatedSL n F :=
    hrange ▸ MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hact := C.act ⟨t, hLS ht⟩
  have hρ : ∀ e : M₀.E, ((φ.comp (Subgroup.inclusion hSH)) ⟨t, hLS ht⟩) e = φ ⟨t, hLH⟩ e :=
    fun e => rfl
  refine mem_statedSLElations_iff.mpr ⟨hAmem, ?_, fun x => ?_⟩
  · have hfix1 : φ ⟨t, hLH⟩ b = b := hfix.1
    have h1 := hact b
    rw [hρ, hfix1, hΨb] at h1
    have h2 := congrArg Prod.fst h1
    simp only at h2
    exact h2.symm
  · have hxV : C.inl x ∈ M₀.img V := (hV _).mpr (by rw [C.Ψ_inl])
    obtain ⟨v, hvV, hvQ, hvπ⟩ := hxV
    have hvc := hcomm t ht v hvV
    have hcQ : ⁅v, t⁆ ∈ Q := by
      have := sup_le hcA.le hcA.Z_le_Q hvc
      exact this
    have hAQ : A ≤ Q := hcA.le
    have hmem := stroth_sup_le_lift h hAQ hvc
    have e1 : ⁅v, t⁆ * (t * v * t⁻¹) = v := by
      simp only [commutatorElement_def]
      group
    have e2 := M₀.π_mul _ hcQ _ (hQn v hvQ)
    rw [e1, hTπ v hvQ, hvπ] at e2
    have e3 : M₀.π ⁅v, t⁆ = C.inl x - φ ⟨t, hLH⟩ (C.inl x) := eq_sub_of_add_eq e2.symm
    obtain ⟨c, hc⟩ := (hline _).mp (e3 ▸ hmem.2)
    refine ⟨-c, ?_⟩
    have h4 := hact (C.inl x)
    rw [hρ, C.Ψ_inl] at h4
    have h5 : C.Ψ (C.inl x - φ ⟨t, hLH⟩ (C.inl x)) =
        (x - (ρ' ⟨t, hLS ht⟩ : Matrix (Fin n) (Fin n) F) *ᵥ x, 0) := by
      rw [map_sub, C.Ψ_inl, h4]
      simp
    rw [h5] at hc
    have h6 := congrArg Prod.fst hc
    simp only at h6
    rw [neg_smul, ← h6]
    abel

theorem exists_mem_LB_of_mem_elations (hcA : Ctx M Q Z A) {S : Subgroup G}
    (hLS : LB M Q A ≤ S) (ρ' : ↥S →* GL (Fin n) F) (hker : ρ'.ker = Q.subgroupOf S)
    (hw : Width Q Z n) (hn : 2 < n) (hFcard : Nat.card F = Nat.card Z) {u : Fin n → F}
    (hu : u ≠ 0) (hel : ∀ (t : G) (ht : t ∈ LB M Q A),
      (ρ' ⟨t, hLS ht⟩ : GL (Fin n) F) ∈ statedSLElations n F u) :
    ∀ A₀ ∈ statedSLElations n F u, ∃ (t : G) (ht : t ∈ LB M Q A),
      (ρ' ⟨t, hLS ht⟩ : GL (Fin n) F) = A₀ := by
  classical
  set Φ : ↥(LB M Q A) →* GL (Fin n) F := ρ'.comp (Subgroup.inclusion hLS) with hΦ
  have hΦker : ∀ r : ↥(LB M Q A), Φ r = 1 ↔ (r : G) ∈ Q := fun r => by
    show ρ' (Subgroup.inclusion hLS r) = 1 ↔ _
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    rfl
  have hQL : Q ≤ LB M Q A := le_sup_left
  have hcard := card_eq_card_mul_range hQL Φ hΦker
  have hge := hcA.card_LB_ge hw (by omega)
  have hpos : 0 < Nat.card Q := Nat.card_pos
  have h1 : Nat.card Z ^ (n - 1) ≤ Nat.card Φ.range := by
    rw [hcard] at hge
    exact Nat.le_of_mul_le_mul_left hge hpos
  have hrange_le : Φ.range ≤ statedSLElations n F u := by
    rintro _ ⟨r, rfl⟩
    exact hel r r.2
  have h2 := card_statedSLElations_le (F := F) (n := n) u hu
  rw [hFcard] at h2
  have heq : Φ.range = statedSLElations n F u :=
    Subgroup.eq_of_le_of_card_ge hrange_le (h2.trans h1)
  intro A₀ hA₀
  rw [← heq] at hA₀
  obtain ⟨r, hr⟩ := hA₀
  exact ⟨r, r.2, hr⟩

end ElationOfLB

section Swap

variable {Γ : Type} [Group Γ] {K F E : Type} [Field K] [Field F] [AddCommGroup E] [Module K E]
  {n : ℕ}

@[expose] def tinvGLHom (n : ℕ) (F : Type) [Field F] : GL (Fin n) F →* GL (Fin n) F where
  toFun := tinvGL
  map_one' := tinvGL_one
  map_mul' := tinvGL_mul

theorem tinvGLHom_injective : Function.Injective (tinvGLHom n F) := fun a b h => by
  rw [← tinvGL_tinvGL a, ← tinvGL_tinvGL b]
  exact congrArg tinvGL h

theorem range_tinvGLHom_comp (ρ' : Γ →* GL (Fin n) F) (h : ρ'.range = StatedSL n F) :
    ((tinvGLHom n F).comp ρ').range = StatedSL n F := by
  rw [MonoidHom.range_comp, h]
  refine le_antisymm ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact tinvGL_mem_statedSL hg
  · intro g hg
    exact ⟨tinvGL g, tinvGL_mem_statedSL hg, tinvGL_tinvGL g⟩

variable {ρ : Γ →* (E ≃ₗ[K] E)} {ρ' : Γ →* GL (Fin n) F}

@[expose] def NatDualCoord.swap (C : NatDualCoord ρ ρ') :
    NatDualCoord ρ ((tinvGLHom n F).comp ρ') where
  Ψ := C.Ψ.trans AddEquiv.prodComm
  θ₁ := C.θ₂
  θ₂ := C.θ₁
  smul c e := by
    simp [C.smul]
  act g e := by
    have h := C.act g e
    have e1 : ((tinvGLHom n F).comp ρ') g = tinvGL (ρ' g) := rfl
    have e3 : ∀ x, (C.Ψ.trans AddEquiv.prodComm) x = ((C.Ψ x).2, (C.Ψ x).1) := fun x => rfl
    rw [e3, e3, e1, tinvGL_tinvGL, h]

theorem NatDualCoord.swap_Ψ (C : NatDualCoord ρ ρ') (e : E) :
    C.swap.Ψ e = ((C.Ψ e).2, (C.Ψ e).1) := rfl

end Swap

section TinvElation

variable {F : Type} [Field F] [CharP F 2] {n : ℕ}

theorem tinvGL_mem_statedSLElations {u u' : Fin n → F} {A₀ : GL (Fin n) F}
    (hA₀SL : A₀ ∈ StatedSL n F) (hu : u' ⬝ᵥ u = 0)
    (hA₀ : ∀ z, (A₀ : Matrix (Fin n) (Fin n) F) *ᵥ z = z + (u' ⬝ᵥ z) • u) :
    tinvGL A₀ ∈ statedSLElations n F u' := by
  have hsq : ∀ z, (A₀ : Matrix (Fin n) (Fin n) F) *ᵥ ((A₀ : Matrix (Fin n) (Fin n) F) *ᵥ z) =
      z := by
    intro z
    rw [hA₀ z, Matrix.mulVec_add, Matrix.mulVec_smul, hA₀ z, hA₀ u, hu]
    simp only [zero_smul, add_zero]
    have h3 : z + (u' ⬝ᵥ z) • u + (u' ⬝ᵥ z) • u = z := by
      rw [add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]
    exact h3
  have hmat : (A₀ : Matrix (Fin n) (Fin n) F) * (A₀ : Matrix (Fin n) (Fin n) F) = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun z => ?_
    rw [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hsq z, Matrix.toLin'_one,
      LinearMap.id_apply]
  have hinv : A₀⁻¹ = A₀ := by
    apply inv_eq_of_mul_eq_one_right
    exact Units.ext (by rw [Units.val_mul, Units.val_one]; exact hmat)
  have hT : ∀ z, (tinvGL A₀ : Matrix (Fin n) (Fin n) F) *ᵥ z = z + (u ⬝ᵥ z) • u' := by
    intro z
    refine dotProduct_eq _ _ fun y => ?_
    rw [coe_tinvGL, hinv, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, hA₀ y,
      dotProduct_add, dotProduct_smul, add_dotProduct, smul_dotProduct, dotProduct_comm z u,
      smul_eq_mul, smul_eq_mul, dotProduct_comm u' y]
    ring
  refine mem_statedSLElations_iff.mpr ⟨tinvGL_mem_statedSL hA₀SL, ?_, fun z => ⟨u ⬝ᵥ z, ?_⟩⟩
  · rw [hT, dotProduct_comm u u', hu, zero_smul, add_zero]
  · rw [hT]
    abel

end TinvElation

section NotTI

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem IsTIMod.conj_of_mem {L : Subgroup G} (hc : Ctx M Q Z B) (h : IsTIMod M Q L) {g : G}
    (hg : g ∈ M) : IsTIMod M Q (conjSubgroup g L) := by
  intro m hm
  have hn : g⁻¹ * m * g ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hg) hm) hg
  have e : conjSubgroup g L ⊓ conjSubgroup m (conjSubgroup g L) =
      conjSubgroup g (L ⊓ conjSubgroup (g⁻¹ * m * g) L) := by
    rw [conjSubgroup_inf, ← conjSubgroup_mul, ← conjSubgroup_mul]
    congr 2
    · group
  rcases h _ hn with h1 | h1
  · left
    rw [e, h1, hc.conj_Q_eq hg]
  · right
    rw [e, h1]

theorem not_isTIMod_of_core (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hcore : CaseVICore M Q Z (Lgen M (LB M Q B)) n) : ¬ IsTIMod M Q (LB M Q B) := by
  classical
  have hn3 : 3 ≤ n := hn
  have hcd := centDvd_of_core hc hw hn hcore
  obtain ⟨K, _, _, _, γ, M₀, h⟩ := stroth_globalModelData hc.hyp
  obtain ⟨φ, hφπ, hφker, hφiso⟩ := exists_actionHom_H0 hc.hyp h
  set S := Lgen M (LB M Q B) with hS
  have hSH : S ≤ H0 M Z := Lgen_le_H0 hc
  obtain ⟨F, hFf, hFfin, hFcard, φ', hrange, hker, V₁, V₂, hZV₁, hV₁Q, hZV₂, hV₂Q, hinf, hsup,
    hact₁, hact₂, hx⟩ := hcore
  have hLin : Smith81.LinSetup M Q Z B n V₁ V₂ :=
    ⟨F, hFf, hFfin, hFcard, φ', hrange, hker, hZV₁, hV₁Q, hZV₂, hV₂Q, hinf, hsup, hact₁, hact₂,
      hx, (Smith81.centDvd_iff_centDvdN_one.mp hcd).mono (by norm_num)⟩
  obtain ⟨Φ, hΦ, hΦ₁, hΦ₂⟩ := exists_equivariant_coord M₀ (φ.comp (Subgroup.inclusion hSH))
    (fun s x hx => hφπ ⟨s, hSH s.2⟩ x hx) hZV₁ hV₁Q hZV₂ hV₂Q hinf hsup φ' hact₁ hact₂
  obtain ⟨C, hCΦ⟩ := exists_natDualCoord_of_equivariant (φ.comp (Subgroup.inclusion hSH)) φ'
    hn3 hrange (by rw [h.card, hFcard]) Φ hΦ
  have hW₁ : ∀ e : M₀.E, e ∈ M₀.img V₁ ↔ (C.Ψ e).2 = 0 := fun e => by
    rw [hCΦ]
    exact hΦ₁ e
  have hW₂ : ∀ e : M₀.E, e ∈ M₀.img V₂ ↔ (C.swap.Ψ e).2 = 0 := fun e => by
    show _ ↔ (C.Ψ e).1 = 0
    rw [hCΦ]
    exact hΦ₂ e
  haveI : CharP F 2 := charP_of_injective_ringHom C.θ₁.toRingHom.injective 2
  obtain ⟨x, hxM, hxV⟩ := hx
  have hSN₂ : ∀ s ∈ S, conjSubgroup s V₂ = V₂ := fun s hs =>
    conjSubgroup_eq_self_iff.mpr (hact₂.1 hs)
  have hSN₁ : ∀ s ∈ S, conjSubgroup s V₁ = V₁ := fun s hs =>
    conjSubgroup_eq_self_iff.mpr (hact₁.1 hs)
  have hSM : S ≤ M := fun y hy => (hSH hy).1
  have key : ∀ A : Subgroup G, Ctx M Q Z A → A ≤ V₁ → ¬ IsTIMod M Q (LB M Q A) := by
    intro A hcA hAV hTI
    have hLinA : Smith81.LinSetup M Q Z A n V₁ V₂ := hLin.of_conj hc hn3 hcA
    have hLS : LB M Q A ≤ S := hLin.LB_le_Lgen_of_le_V₁ hc hn3 hcA hAV
    have hcomm : ∀ t ∈ LB M Q A, ∀ v ∈ V₁, ⁅v, t⁆ ∈ A ⊔ Z := fun t ht v hv =>
      hLinA.comm_mem_sup_of_le_V₁ hcA hn3 hAV ht hv
    obtain ⟨u, hu0, -, hel⟩ := elation_of_mem_LB hcA h hSH φ hφπ φ' hrange C hW₁ hAV hLS hcomm
    have hsurj := exists_mem_LB_of_mem_elations hcA hLS φ' hker hw hn hFcard hu0 hel
    have hcx : Ctx M Q Z (conjSubgroup x A) := hcA.conj_of_mem hxM
    have hxV₂ : conjSubgroup x A ≤ V₂ := by
      rw [← hxV]
      exact Subgroup.map_mono hAV
    obtain ⟨b₂, hb₂0, -, hB₂line, -, -⟩ := hcx.dictB h
    have hb₂A : b₂ ∈ M₀.img (conjSubgroup x A) := (hB₂line b₂).mpr ⟨1, (one_smul K b₂).symm⟩
    have hb₂V : b₂ ∈ M₀.img V₂ := M₀.img_mono hxV₂ hb₂A
    have hb₂1 : (C.Ψ b₂).1 = 0 := (hW₂ b₂).mp hb₂V
    set w₂ : Fin n → F := (C.Ψ b₂).2 with hw₂
    have hΨb₂ : C.Ψ b₂ = (0, w₂) := Prod.ext hb₂1 rfl
    have hw₂0 : w₂ ≠ 0 := by
      intro h0
      apply hb₂0
      apply C.Ψ.injective
      rw [hΨb₂, h0, map_zero]
      rfl
    obtain ⟨α, hα0, hαu⟩ : ∃ α : Fin n → F, α ≠ 0 ∧ α ⬝ᵥ u = 0 := by
      obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hu0 (funext hcon)
      obtain ⟨j, hj⟩ : ∃ j : Fin n, j ≠ i := by
        by_contra hcon
        push Not at hcon
        have h0 : (⟨0, by omega⟩ : Fin n) = i := hcon _
        have h1 : (⟨1, by omega⟩ : Fin n) = i := hcon _
        have := h0.trans h1.symm
        simp [Fin.ext_iff] at this
      refine ⟨u j • Pi.single i 1 - u i • Pi.single j 1, ?_, ?_⟩
      · intro h0
        have := congrFun h0 j
        simp [Pi.single_apply, hj, hi] at this
      · simp [sub_dotProduct, smul_dotProduct, mul_comm]
    obtain ⟨A', hA'SL, hA'w⟩ := exists_statedSL_mulVec_eq (by omega : 2 ≤ n) hw₂0 hα0
    obtain ⟨s, hs⟩ := NatDualCoord.exists_eq_of_mem_statedSL hrange (tinvGL_mem_statedSL hA'SL)
    have hs' : tinvGL (φ' s) = A' := by rw [hs, tinvGL_tinvGL]
    set m : G := (s : G) * x with hm
    have hmM : m ∈ M := M.mul_mem (hSM s.2) hxM
    have hmV : conjSubgroup m V₁ = V₂ := by
      rw [hm, conjSubgroup_mul, hxV, hSN₂ s s.2]
    set A₂ := conjSubgroup m A with hA₂
    have hc₂ : Ctx M Q Z A₂ := hcA.conj_of_mem hmM
    have hA₂V : A₂ ≤ V₂ := by
      rw [← hmV]
      exact Subgroup.map_mono hAV
    have hLS₂ : LB M Q A₂ ≤ S := hLin.symm.LB_le_Lgen_of_le_V₁ hc hn3 hc₂ hA₂V
    have hcomm₂ : ∀ t ∈ LB M Q A₂, ∀ v ∈ V₂, ⁅v, t⁆ ∈ A₂ ⊔ Z := fun t ht v hv =>
      (hLin.of_conj hc hn3 hc₂).symm.comm_mem_sup_of_le_V₁ hc₂ hn3 hA₂V ht hv
    obtain ⟨u', hu'0, hline', hel'⟩ := elation_of_mem_LB hc₂ h hSH φ hφπ
      ((tinvGLHom n F).comp φ') (range_tinvGLHom_comp φ' hrange) C.swap hW₂ hA₂V hLS₂ hcomm₂
    have hker' : ((tinvGLHom n F).comp φ').ker = Q.subgroupOf S :=
      (MonoidHom.ker_comp_of_injective φ' (tinvGLHom n F) tinvGLHom_injective).trans hker
    have hsurj' := exists_mem_LB_of_mem_elations hc₂ hLS₂ ((tinvGLHom n F).comp φ') hker' hw hn
      hFcard hu'0 hel'
    obtain ⟨p, hpB₂, hpQ, hpπ⟩ := hb₂A
    have hspA₂ : (s : G) * p * (s : G)⁻¹ ∈ A₂ := by
      rw [hA₂, hm, conjSubgroup_mul]
      refine mem_conjSubgroup.mpr ?_
      rw [show (s : G)⁻¹ * ((s : G) * p * (s : G)⁻¹) * (s : G) = p by group]
      exact hpB₂
    have hTsb₂ : φ ⟨s, hSH s.2⟩ b₂ ∈ M₀.img A₂ := by
      refine ⟨(s : G) * p * (s : G)⁻¹, hspA₂, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hSM s.2)) p).mp hpQ
      · rw [hφπ ⟨s, hSH s.2⟩ p hpQ, hpπ]
    have hΨTs : C.Ψ (φ ⟨s, hSH s.2⟩ b₂) = (0, α) := by
      have h1 := C.act s b₂
      rw [hΨb₂] at h1
      have h2 : (φ.comp (Subgroup.inclusion hSH)) s b₂ = φ ⟨s, hSH s.2⟩ b₂ := rfl
      rw [h2] at h1
      rw [h1]
      simp only [hs', hA'w, Matrix.mulVec_zero]
    obtain ⟨c, hc'⟩ := (hline' _).mp hTsb₂
    have hcα : α = c • u' := by
      rw [NatDualCoord.swap_Ψ, hΨTs] at hc'
      exact congrArg Prod.fst hc'
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hcα
      exact hα0 hcα
    have hu'u : u' ⬝ᵥ u = 0 := by
      rw [hcα, smul_dotProduct, smul_eq_mul] at hαu
      exact (mul_eq_zero.mp hαu).resolve_left hc0
    let f : Module.Dual F (Fin n → F) :=
      { toFun := fun z => u' ⬝ᵥ z
        map_add' := fun a b => dotProduct_add u' a b
        map_smul' := fun a z => by simp [dotProduct_smul] }
    obtain ⟨A₀, hA₀SL, hA₀⟩ := exists_statedSL_mulVec_eq_transvection (v := u) f
      (by show u' ⬝ᵥ u = 0; exact hu'u)
    have hA₀' : ∀ z, (A₀ : Matrix (Fin n) (Fin n) F) *ᵥ z = z + (u' ⬝ᵥ z) • u := hA₀
    have hA₀el : A₀ ∈ statedSLElations n F u := by
      refine mem_statedSLElations_iff.mpr ⟨hA₀SL, ?_, fun z => ⟨u' ⬝ᵥ z, ?_⟩⟩
      · rw [hA₀' u, hu'u, zero_smul, add_zero]
      · rw [hA₀' z]
        abel
    have hA₀el' : tinvGL A₀ ∈ statedSLElations n F u' :=
      tinvGL_mem_statedSLElations hA₀SL hu'u hA₀'
    obtain ⟨t, ht, hti⟩ := hsurj A₀ hA₀el
    obtain ⟨t', ht', hti'⟩ := hsurj' (tinvGL A₀) hA₀el'
    have hti'' : φ' ⟨t', hLS₂ ht'⟩ = A₀ := by
      have h1 : tinvGL (φ' ⟨t', hLS₂ ht'⟩) = tinvGL A₀ := hti'
      rw [← tinvGL_tinvGL (φ' ⟨t', hLS₂ ht'⟩), h1, tinvGL_tinvGL]
    have hQ : t⁻¹ * t' ∈ Q := by
      have h1 : φ' ((⟨t, hLS ht⟩ : ↥S)⁻¹ * ⟨t', hLS₂ ht'⟩) = 1 := by
        rw [map_mul, map_inv, hti, hti'', inv_mul_cancel]
      have h2 : ((⟨t, hLS ht⟩ : ↥S)⁻¹ * ⟨t', hLS₂ ht'⟩) ∈ φ'.ker := h1
      rw [hker, Subgroup.mem_subgroupOf] at h2
      exact h2
    have ht'LA : t' ∈ LB M Q A := by
      have e : t' = t * (t⁻¹ * t') := by group
      rw [e]
      exact (LB M Q A).mul_mem ht ((le_sup_left : Q ≤ LB M Q A) hQ)
    have ht'Q : t' ∉ Q := by
      intro hq
      have h1 : φ' ⟨t', hLS₂ ht'⟩ = 1 := by
        have h2 : (⟨t', hLS₂ ht'⟩ : ↥S) ∈ φ'.ker := by
          rw [hker, Subgroup.mem_subgroupOf]
          exact hq
        exact h2
      rw [hti''] at h1
      have h3 : ∀ z : Fin n → F, (u' ⬝ᵥ z) • u = 0 := fun z => by
        have h4 := hA₀' z
        rw [h1, Units.val_one, Matrix.one_mulVec] at h4
        exact add_eq_left.mp h4.symm
      apply hu'0
      refine dotProduct_eq _ _ fun z => ?_
      rw [zero_dotProduct]
      exact (smul_eq_zero.mp (h3 z)).resolve_right hu0
    have hLB₂ : conjSubgroup m (LB M Q A) = LB M Q A₂ := (hcA.LB_conj hmM).symm
    have hmem : t' ∈ LB M Q A ⊓ conjSubgroup m (LB M Q A) :=
      ⟨ht'LA, by rw [hLB₂]; exact ht'⟩
    rcases hTI m hmM with h1 | h1
    · rw [h1] at hmem
      exact ht'Q hmem
    · have hle : LB M Q A ≤ conjSubgroup m (LB M Q A) := inf_eq_left.mp h1
      have heq : conjSubgroup m (LB M Q A) = LB M Q A :=
        (Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])).symm
      have hmN : m ∈ Subgroup.normalizer (LB M Q A : Set G) := conjSubgroup_eq_self_iff.mp heq
      have hmBZ := (stroth111a_holds G M Q Z A hcA n hw hn m hmM).mpr hmN
      have hAZ : conjSubgroup m (A ⊔ Z : Subgroup G) = A ⊔ Z := conjSubgroup_eq_self_iff.mpr hmBZ
      have hAZV₁ : A ⊔ Z ≤ V₁ := sup_le hAV hZV₁
      have hAZV₂ : A ⊔ Z ≤ V₂ := by
        rw [← hmV, ← hAZ]
        exact Subgroup.map_mono hAZV₁
      have hAZ' : A ≤ Z := by
        have h2 : A ≤ V₁ ⊓ V₂ := le_inf hAV ((le_sup_left : A ≤ A ⊔ Z).trans hAZV₂)
        rwa [hinf] at h2
      obtain ⟨g, hg⟩ := hcA.conj
      have hcardA : Nat.card ↥A = Nat.card ↥Z := by rw [hg, card_conjSubgroup]
      exact hcA.ne (Subgroup.eq_of_le_of_card_ge hAZ' (by rw [hcardA]))
  rcases Smith81.linBInStatement_holds G M Q Z B n V₁ V₂ hc hLin hn3 with hB | hB
  · exact key B hc hB
  ·
    have hxinv : conjSubgroup x⁻¹ V₂ = V₁ := by
      rw [← hxV, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    have hcA : Ctx M Q Z (conjSubgroup x⁻¹ B) := hc.conj_of_mem (M.inv_mem hxM)
    have hAV : conjSubgroup x⁻¹ B ≤ V₁ := by
      rw [← hxinv]
      exact Subgroup.map_mono hB
    intro hTI
    apply key _ hcA hAV
    have h1 := hTI.conj_of_mem hc (M.inv_mem hxM)
    rwa [← hc.LB_conj (M.inv_mem hxM)] at h1

theorem caseVICore_of_caseVI (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (h : CaseVI M Q Z (Lgen M (LB M Q B))) : CaseVICore M Q Z (Lgen M (LB M Q B)) n := by
  obtain ⟨n', K, hK, hf, hcard, φ, hr, hk, V₁, V₂, h1, h2, h3, h4, h5, h6, hA1, hA2, hx,
    hcd⟩ := h
  have hLin : Smith81.LinSetup M Q Z B n' V₁ V₂ :=
    ⟨K, hK, hf, hcard, φ, hr, hk, h1, h2, h3, h4, h5, h6, hA1, hA2, hx,
      (Smith81.centDvd_iff_centDvdN_one.mp hcd).mono (by norm_num)⟩
  have hw' : Width Q Z n' := hLin.width hc.hyp
  have hnn : n' = n := by
    have h7 : Nat.card Z ^ (2 * n' + 1) = Nat.card Z ^ (2 * n + 1) := hw'.symm.trans hw
    have hq : 1 < Nat.card Z := by
      have := hc.hyp.q4
      omega
    have := Nat.pow_right_injective hq h7
    omega
  subst hnn
  exact ⟨K, hK, hf, hcard, φ, hr, hk, V₁, V₂, h1, h2, h3, h4, h5, h6, hA1, hA2, hx⟩

theorem strothNotTI_of_1111 (h : Stroth1111Statement) : Stroth1111NotTIStatement := by
  intro G _ _ M Q Z B hc n hw hn ha
  exact not_isTIMod_of_core hc hw hn (caseVICore_of_caseVI hc hw (h G M Q Z B hc n hw hn ha))

end NotTI

end CFSG.RankThree.GF2n.Stroth80
