module

public import CFSG.Quasithin.MS93.S37Bad3
public import CFSG.Quasithin.MS93.S37ALR

public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36 CFSG.Quasithin.Vol2
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

theorem tImage_sup {S : Subgroup G} (θ : MulAut ↥S) {A B : Subgroup G} (hA : A ≤ S)
    (hB : B ≤ S) : tImage θ (A ⊔ B) = tImage θ A ⊔ tImage θ B := by
  rw [tImage, tImage, tImage, Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup,
    Subgroup.map_sup]

variable [Finite G]

namespace Cfg

variable {M T L : Subgroup G} {F : Type} [Field F] [Fintype F] (C : Cfg M T L F)
include C

theorem Usub_sup_inf_Uq' (W : Submodule F (V4 F)) :
    (C.Usub W ⊔ Dq M L) ⊓ Uq M T L = C.Usub W := by
  refine le_antisymm ?_ (le_inf le_sup_left (C.Usub_le _))
  rintro x ⟨hxP, hxU⟩
  have hn : C.Usub W ≤ Subgroup.normalizer (Dq M L : Set G) :=
    ((C.Usub_le _).trans (Uq_le C.h.L_le)).trans (le_normalizer_Dq C.h.le_normalizer)
  have hxP' : x ∈ ((C.Usub W ⊔ Dq M L : Subgroup G) : Set G) := hxP
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn] at hxP'
  obtain ⟨u, hu, d, hd, hxud⟩ := hxP'
  change u * d = x at hxud
  subst hxud
  obtain ⟨huU, hco⟩ := (C.mem_Usub).1 hu
  have hdU : d ∈ Uq M T L := by
    have e : d = u⁻¹ * (u * d) := by group
    rw [e]
    exact (Uq M T L).mul_mem ((Uq M T L).inv_mem huU) hxU
  refine (C.mem_Usub).2 ⟨hxU, ?_⟩
  have e : (⟨u * d, hxU⟩ : ↥(Uq M T L)) = ⟨u, huU⟩ * ⟨d, hdU⟩ := rfl
  rw [e, C.N.co_mul, (C.N.co_eq_zero_iff ⟨d, hdU⟩).2 ⟨hdU, hd.2⟩, add_zero]
  exact hco

theorem relIndex_Usub_ker (f : V4 F →ₗ[F] F × F) (hf : Function.Surjective f) :
    (C.Usub (LinearMap.ker f)).relIndex (Uq M T L) = Nat.card F * Nat.card F := by
  let g : ↥(Uq M T L) →* Multiplicative (F × F) :=
    { toFun := fun u => Multiplicative.ofAdd (f (C.N.co u))
      map_one' := by simp [C.N.co_one]
      map_mul' := fun u v => by simp [C.N.co_mul] }
  have hg : Function.Surjective g := by
    intro c
    obtain ⟨w, hw⟩ := hf (Multiplicative.toAdd c)
    obtain ⟨u, hu⟩ := C.N.co_surj w
    refine ⟨u, ?_⟩
    show Multiplicative.ofAdd (f (C.N.co u)) = c
    rw [hu, hw]
    rfl
  have hker : g.ker = (C.Usub (LinearMap.ker f)).subgroupOf (Uq M T L) := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, C.mem_Usub]
    constructor
    · intro h
      refine ⟨u.2, ?_⟩
      have h1 : Multiplicative.ofAdd (f (C.N.co u)) = 1 := h
      exact LinearMap.mem_ker.2 (by simpa using h1)
    · rintro ⟨hu, hp⟩
      show Multiplicative.ofAdd (f (C.N.co u)) = 1
      rw [LinearMap.mem_ker.1 hp]
      rfl
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hg,
    Subgroup.card_top]
  show Nat.card (F × F) = _
  rw [Nat.card_prod]

theorem relIndex_Usub_sup (W : Submodule F (V4 F)) :
    (C.Usub W ⊔ Dq M L).relIndex (Uq M T L ⊔ Dq M L) = (C.Usub W).relIndex (Uq M T L) := by
  have hPUD : C.Usub W ⊔ Dq M L ≤ Uq M T L ⊔ Dq M L := sup_le_sup_right (C.Usub_le _) _
  have hn : Uq M T L ⊔ Dq M L ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    (sup_le C.Uq_le_pCore inf_le_left).trans ((pCoreOf_le' M).trans C.hMU)
  have hsup : Uq M T L ⊔ (C.Usub W ⊔ Dq M L) = Uq M T L ⊔ Dq M L := by
    refine le_antisymm (sup_le le_sup_left hPUD) (sup_le le_sup_left ?_)
    exact le_sup_right.trans le_sup_right
  have e1 := relIndex_eq_of_sup le_sup_left hPUD hn hsup
  rw [← Subgroup.inf_relIndex_right, C.Usub_sup_inf_Uq'] at e1
  exact e1.symm

theorem Uq_inf_Dq : Uq M T L ⊓ Dq M L = Uq M T L ⊓ Subgroup.centralizer (L : Set G) := by
  rw [Dq, ← inf_assoc, inf_eq_left.2 C.Uq_le_pCore]

theorem A₁_props (φ : MulAut ↥(T1 M T L)) (hE : C.rhoIm (Ut M T L φ) = X₂ F) {d₀ : G}
    (hd₀ : d₀ ∈ Dt M L φ) {x₀ y₀ s₀ : F}
    (hρ : C.rho ⟨d₀, T1_le_sup (tImage_le φ _ hd₀)⟩ = qe x₀ y₀ s₀) (hxy : x₀ ≠ 0 ∨ y₀ ≠ 0) :
    (∀ a ∈ tImage φ (Uq M T L ⊓ Subgroup.centralizer (L : Set G)),
      ∃ ha : a ∈ Uq M T L, C.N.co ⟨a, ha⟩ ∈ pt₀ F) ∧
    tImage φ (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) ⊓ Dq M L = ⊥ ∧
    Nat.card ↥(tImage φ (Uq M T L ⊓ Subgroup.centralizer (L : Set G))) = Nat.card F := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  have hq : 2 < Nat.card F := by have := C.q_ge_four; omega
  set A := Uq M T L ⊓ Subgroup.centralizer (L : Set G) with hA
  set A₁ := tImage φ A with hA₁
  have hAR := C.A_le_Rt hq φ hE
  have hd₀K : d₀ ∈ L ⊔ pCoreOf 2 M := T1_le_sup (tImage_le φ _ hd₀)
  have hd₀M : d₀ ∈ M := C.sup_le_M hd₀K
  have hex : ∀ c : F, ∃ a : G, a ∈ A₁ ∧ ∃ ha : a ∈ Uq M T L, C.N.co ⟨a, ha⟩ = c • e₁ F := by
    intro c
    obtain ⟨v, hv3, hv⟩ : ∃ v : V4 F, v (.inr 0) = 0 ∧ x₀ * v (.inr 1) + y₀ * v (.inl 1) = c := by
      rcases hxy with hx | hy
      · exact ⟨(c / x₀) • f₂ F, by simp [f₂], by simp [f₂]; field_simp⟩
      · exact ⟨(c / y₀) • e₂ F, by simp [e₂], by simp [e₂]; field_simp⟩
    obtain ⟨u, rfl⟩ := C.N.co_surj v
    have hcU : ⁅d₀, (u : G)⁆ ∈ Uq M T L := by
      rw [commutatorElement_def]
      exact (Uq M T L).mul_mem ((Subgroup.mem_normalizer_iff.1 (C.hMU hd₀M) _).1 u.2)
        ((Uq M T L).inv_mem u.2)
    have hcD : ⁅d₀, (u : G)⁆ ∈ Dt M L φ := by
      have e : ⁅d₀, (u : G)⁆ = d₀ * ((u : G) * d₀⁻¹ * (u : G)⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact (Dt M L φ).mul_mem hd₀ (C.conj_mem_Dt_of_T1 φ (C.Uq_le_T1 u.2)
        ((Dt M L φ).inv_mem hd₀))
    have hco : C.N.co ⟨_, hcU⟩ = c • e₁ F := by
      rw [C.co_comm hd₀M u.2 hcU, show C.act hd₀M = C.act (C.sup_le_M hd₀K) from rfl,
        C.rho_spec ⟨d₀, hd₀K⟩, hρ, qe_mulVec, hv3]
      rw [show C.N.co ⟨(u : G), u.2⟩ = C.N.co u from rfl]
      refine ext4 ?_ ?_ ?_ ?_ <;> simp [e₁, e₂, f₂, hv3]
      linear_combination hv
    have hco' : C.N.co ⟨_, hcU⟩ ∈ pt₀ F := by
      rw [hco, pt₀_eq_span]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    have hpt : ⁅d₀, (u : G)⁆ ∈ C.Usub (pt₀ F) := (C.mem_Usub).2 ⟨hcU, hco'⟩
    obtain ⟨r, hr, hra⟩ := C.exists_Rt φ hE hpt
    have hxR : ⁅d₀, (u : G)⁆ ∈ Rt M T L φ := by
      have e : ⁅d₀, (u : G)⁆ = r * (r⁻¹ * ⁅d₀, (u : G)⁆) := by group
      rw [e]
      exact (Rt M T L φ).mul_mem hr (hAR hra)
    have hxU : ⁅d₀, (u : G)⁆ ∈ Ut M T L φ := by
      refine (Subgroup.commutator_le.2 fun a ha b hb => ?_) hxR
      have h := (C.comm_mem_inf C.pCore_le_T1 T1_le_T φ hb ha).2
      have e : ⁅a, b⁆ = ⁅b, a⁆⁻¹ := by simp only [commutatorElement_def]; group
      rw [e]
      exact (Ut M T L φ).inv_mem h
    refine ⟨_, ?_, hcU, hco⟩
    have h1 : ⁅d₀, (u : G)⁆ ∈ tImage φ (Uq M T L ⊓ Dq M L) := by
      rw [tImage_inf']
      exact ⟨hxU, hcD⟩
    rwa [C.Uq_inf_Dq] at h1
  choose a ha haU haco using hex
  let g : F → ↥A₁ := fun c => ⟨a c, ha c⟩
  have hg : Function.Injective g := by
    intro c c' hcc
    have h1 : a c = a c' := congrArg Subtype.val hcc
    have h2 : C.N.co ⟨a c, haU c⟩ = C.N.co ⟨a c', haU c'⟩ := by
      congr 1
      exact Subtype.ext h1
    rw [haco, haco] at h2
    have := congrFun h2 (.inl 0)
    simpa [e₁] using this
  have hAcard : Nat.card ↥A₁ ≤ Nat.card F := by
    rw [hA₁, card_tImage φ ((inf_le_left : A ≤ Uq M T L).trans C.Uq_le_T1)]
    have h := (lift_L C.h C.hα C.hnat C.hVU (by have := C.hk; omega) C.hF).1
    have hFn : Nat.card F = 2 ^ C.k := by rw [Nat.card_eq_fintype_card, C.hF]
    rw [hFn]
    exact h
  have hbij := hg.bijective_of_nat_card_le hAcard
  have hall : ∀ x ∈ A₁, ∃ c, a c = x := fun x hx => by
    obtain ⟨c, hc⟩ := hbij.2 ⟨x, hx⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  have ha0 : a 0 = 1 := by
    obtain ⟨c, hc⟩ := hall 1 A₁.one_mem
    have h2 : C.N.co ⟨a c, haU c⟩ = 0 := by
      have e : (⟨a c, haU c⟩ : ↥(Uq M T L)) = 1 := Subtype.ext hc
      rw [e, C.N.co_one]
    rw [haco] at h2
    have h3 : c = 0 := by simpa [e₁] using congrFun h2 (.inl 0)
    rw [← hc, h3]
  refine ⟨fun x hx => ?_, ?_, ?_⟩
  · obtain ⟨c, rfl⟩ := hall x hx
    refine ⟨haU c, ?_⟩
    rw [haco, pt₀_eq_span]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [eq_bot_iff]
    rintro x ⟨hx, hxD⟩
    obtain ⟨c, rfl⟩ := hall x hx
    have h1 : C.N.co ⟨a c, haU c⟩ = 0 := (C.N.co_eq_zero_iff _).2 ⟨haU c, hxD.2⟩
    rw [haco] at h1
    have h3 : c = 0 := by simpa [e₁] using congrFun h1 (.inl 0)
    rw [h3, ha0]
    exact Subgroup.one_mem _
  · exact (Nat.card_congr (Equiv.ofBijective g hbij)).symm

theorem false_of_bad_Q₂ (hT : C.T0bar = Q₂ F) (φ : MulAut ↥(T1 M T L))
    (hE : C.rhoIm (Ut M T L φ) = X₂ F) (hE' : C.rhoIm (Ut M T L φ⁻¹) = X₂ F)
    (hK : ∀ (t : G) (ht : t ∈ T ⊓ L), C.rho1 (φ ⟨t, T_inf_L_le_T1 ht⟩) ∈ X₂ F) : False := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hq4 := C.q_ge_four
  have hN := C.rhoIm_Qt_eq_T0bar φ hE hK
  obtain ⟨w, hw, hfix⟩ := C.exists_fix_Dt φ hE hK (C.sup_Qt_eq φ hN)
  set E := C.rhoIm (Dt M L φ) with hEdef
  set D₁ := Dt M L φ with hD₁
  set r := (Uq M T L ⊔ Dq M L).relIndex (pCoreOf 2 M) with hrdef
  have hsize : r * Nat.card F * Nat.card ↥E = Nat.card F ^ 3 := by
    have h1 := C.card_rhoIm_Dt φ
    have h2 := C.relIndex_Qt_eq_mul φ⁻¹ hE'
    rw [C.relIndex_Qt_inv φ, ← C.card_rhoIm (Qt_le_sup φ), hN, hT, card_Q₂, ← h1] at h2
    exact h2.symm
  have hr : r ≤ Nat.card F := C.relIndex_le_card
  have hr0 : 0 < r := Cfg.relIndex_pos' _ _
  have hEnt : ∃ (d₀ : G) (hd₀ : d₀ ∈ D₁), C.rho ⟨d₀, T1_le_sup (tImage_le φ _ hd₀)⟩ ≠ 1 := by
    by_contra h
    push Not at h
    have hE1 : E = ⊥ := by
      rw [eq_bot_iff]
      intro e he
      obtain ⟨d, hdK, hd, rfl⟩ := (C.mem_rhoIm).1 he
      exact h d hd
    rw [hE1, Subgroup.card_bot, mul_one] at hsize
    have : Nat.card F ^ 3 ≤ Nat.card F * Nat.card F := by
      rw [← hsize]
      exact Nat.mul_le_mul_right _ hr
    nlinarith
  obtain ⟨d₀, hd₀, hd₀1⟩ := hEnt
  have hd₀Q₂ : C.rho ⟨d₀, T1_le_sup (tImage_le φ _ hd₀)⟩ ∈ Q₂ F := by
    rw [← hT]
    exact ⟨⟨d₀, tImage_le φ _ hd₀⟩, rfl⟩
  obtain ⟨x₀, y₀, s₀, hρ₀⟩ := exists_eq_qe_of_mem_Q₂ hd₀Q₂
  have hxy : x₀ ≠ 0 ∨ y₀ ≠ 0 := by
    by_contra h
    push Not at h
    apply hd₀1
    refine C.rho_Dt_eq_one φ hE hE' hd₀ _ ?_
    rw [hρ₀, h.1, h.2, qe_zero_zero]
    exact transv_mem_X₂ _
  have hw0 := hfix d₀ hd₀
  rw [hρ₀, qe_mulVec] at hw0
  have hw3 : w (.inr 0) = 0 := by
    have e2 := congrFun hw0 (.inl 1)
    have e4 := congrFun hw0 (.inr 1)
    simp [e₁, e₂, f₂] at e2 e4
    rcases hxy with hx | hy
    · exact (e2.resolve_left hx)
    · exact (e4.resolve_left hy)
  have hw24 : w (.inl 1) ≠ 0 ∨ w (.inr 1) ≠ 0 := by
    by_contra h
    push Not at h
    exact hw (mem_pt₀.2 ⟨h.1, hw3, h.2⟩)
  have hEline : ∀ (d : G) (hd : d ∈ D₁) (x y s : F),
      C.rho ⟨d, T1_le_sup (tImage_le φ _ hd)⟩ = qe x y s → x * y₀ + y * x₀ = 0 := by
    intro d hd x y s hρ
    have h1 := congrFun hw0 (.inl 0)
    have h2' := hfix d hd
    rw [hρ, qe_mulVec] at h2'
    have h3 := congrFun h2' (.inl 0)
    simp [e₁, e₂, f₂, hw3] at h1 h3
    have f1 : (x * y₀ + y * x₀) * w (.inl 1) = 0 := by
      linear_combination x * h1 - x₀ * h3 + (x₀ * y * w (.inl 1)) * h2
    have f2 : (x * y₀ + y * x₀) * w (.inr 1) = 0 := by
      linear_combination -(y * h1) + y₀ * h3 + (y * x₀ * w (.inr 1)) * h2
    rcases hw24 with h | h
    · exact (mul_eq_zero.1 f1).resolve_right h
    · exact (mul_eq_zero.1 f2).resolve_right h
  let f : V4 F →ₗ[F] F × F :=
    { toFun := fun v => (v (.inr 0), x₀ * v (.inr 1) + y₀ * v (.inl 1))
      map_add' := fun u v => by
        refine Prod.ext ?_ ?_ <;> simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add]
        ring
      map_smul' := fun c v => by
        refine Prod.ext ?_ ?_ <;> simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
          Prod.smul_fst, Prod.smul_snd]
        ring }
  have hf : Function.Surjective f := by
    rintro ⟨a, b⟩
    rcases hxy with hx | hy
    · refine ⟨a • f₁ F + (b / x₀) • f₂ F, Prod.ext ?_ ?_⟩
      · simp [f, f₁, f₂]
      · simp [f, f₁, f₂]
        field_simp
    · refine ⟨a • f₁ F + (b / y₀) • e₂ F, Prod.ext ?_ ?_⟩
      · simp [f, f₁, e₂]
      · simp [f, f₁, e₂]
        field_simp
  set W₀ := LinearMap.ker f with hW₀
  have hfix₀ : ∀ v : V4 F, mat (C.rho ⟨d₀, T1_le_sup (tImage_le φ _ hd₀)⟩) *ᵥ v = v → v ∈ W₀ := by
    intro v hv
    rw [hρ₀, qe_mulVec] at hv
    have e1 := congrFun hv (.inl 0)
    have e2 := congrFun hv (.inl 1)
    have e4 := congrFun hv (.inr 1)
    simp [e₁, e₂, f₂] at e1 e2 e4
    have hv3 : v (.inr 0) = 0 := by
      rcases hxy with hx | hy
      · exact e2.resolve_left hx
      · exact e4.resolve_left hy
    rw [hv3, mul_zero, zero_add] at e1
    rw [LinearMap.mem_ker]
    exact Prod.ext hv3 e1
  have hcommW : ∀ (u : G) (hu : u ∈ Uq M T L) (d : G) (hd : d ∈ D₁), ⁅d, u⁆ ∈ C.Usub W₀ := by
    intro u hu d hd
    have hdK := T1_le_sup (tImage_le φ _ hd)
    have hdM := C.sup_le_M hdK
    have hcU : ⁅d, u⁆ ∈ Uq M T L := by
      rw [commutatorElement_def]
      exact (Uq M T L).mul_mem ((Subgroup.mem_normalizer_iff.1 (C.hMU hdM) _).1 hu)
        ((Uq M T L).inv_mem hu)
    refine (C.mem_Usub).2 ⟨hcU, ?_⟩
    have hdQ₂ : C.rho ⟨d, hdK⟩ ∈ Q₂ F := by
      rw [← hT]
      exact ⟨⟨d, tImage_le φ _ hd⟩, rfl⟩
    obtain ⟨x, y, s, hρ⟩ := exists_eq_qe_of_mem_Q₂ hdQ₂
    have hline := hEline d hd x y s hρ
    rw [C.co_comm hdM hu hcU, show C.act hdM = C.act (C.sup_le_M hdK) from rfl,
      C.rho_spec ⟨d, hdK⟩, hρ, qe_mulVec, LinearMap.mem_ker]
    refine Prod.ext ?_ ?_
    · simp [f, e₁, e₂, f₂]
    · simp [f, e₁, e₂, f₂]
      linear_combination (C.N.co ⟨u, hu⟩ (.inr 0)) * hline
  obtain ⟨hA₁U, hA₁D, hA₁card⟩ := C.A₁_props φ hE hd₀ hρ₀ hxy
  set A₁ := tImage φ (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) with hA₁
  set T0x := tImage φ (T ⊓ L) with hT0x
  set Qx := Qt M φ with hQx
  set UD := Uq M T L ⊔ Dq M L with hUD
  set P := C.Usub (perp (pt₀ F)) ⊔ Dq M L with hP
  set Y := T0x ⊔ Dq M L with hY
  set Z := T0x ⊔ D₁ with hZ
  set Q := pCoreOf 2 M with hQ
  have hDQ : Dq M L ≤ Q := inf_le_left
  have hDT : Dq M L ≤ T1 M T L := hDQ.trans C.pCore_le_T1
  have hT0xT : T0x ≤ T1 M T L := tImage_le φ _
  have hD₁T : D₁ ≤ T1 M T L := tImage_le φ _
  have hQxT : Qx ≤ T1 M T L := tImage_le φ _
  have hYT : Y ≤ T1 M T L := sup_le hT0xT hDT
  have hZT : Z ≤ T1 M T L := sup_le hT0xT hD₁T
  have hUDQ : UD ≤ Q := sup_le C.Uq_le_pCore hDQ
  have hUL : Uq M T L ≤ T ⊓ L := le_inf C.Uq_le_T (Uq_le_L C.h)
  have hUtT0x : Ut M T L φ ≤ T0x := tImage_mono' φ hUL
  have hAL : Uq M T L ⊓ Subgroup.centralizer (L : Set G) ≤ (T ⊓ L) ⊓ Dq M L :=
    le_inf (inf_le_left.trans hUL) (le_inf (inf_le_left.trans C.Uq_le_pCore) inf_le_right)
  have hA₁T0x : A₁ ≤ T0x := tImage_mono' φ (hAL.trans inf_le_left)
  have hA₁D₁ : A₁ ≤ D₁ := tImage_mono' φ (hAL.trans inf_le_right)
  have hnorm : ∀ {K : Subgroup G}, K ≤ T1 M T L → (∀ t ∈ T1 M T L, ∀ x ∈ K, t * x * t⁻¹ ∈ K) →
      T1 M T L ≤ Subgroup.normalizer (K : Set G) := by
    intro K _ hK t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hK t ht x, fun hx => ?_⟩
    have := hK t⁻¹ ((T1 M T L).inv_mem ht) _ hx
    simpa [mul_assoc] using this
  have hDn : T1 M T L ≤ Subgroup.normalizer (Dq M L : Set G) := fun t ht =>
    le_normalizer_Dq C.h.le_normalizer (C.h.le (T1_le_T ht))
  have hD₁n : T1 M T L ≤ Subgroup.normalizer (D₁ : Set G) :=
    hnorm hD₁T fun t ht x hx => C.conj_mem_Dt_of_T1 φ ht hx
  have hQxn : T1 M T L ≤ Subgroup.normalizer (Qx : Set G) :=
    hnorm hQxT fun t ht x hx => C.conj_mem_Qt_of_T1 φ ht hx
  have hUDn : T1 M T L ≤ Subgroup.normalizer (UD : Set G) := by
    refine hnorm (hUDQ.trans C.pCore_le_T1) fun t ht x hx => ?_
    have htM : t ∈ M := C.h.le (T1_le_T ht)
    have hn : Uq M T L ≤ Subgroup.normalizer (Dq M L : Set G) :=
      (Uq_le C.h.L_le).trans (le_normalizer_Dq C.h.le_normalizer)
    have hx' : x ∈ ((UD : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn] at hx'
    obtain ⟨u, hu, d, hd, hxud⟩ := hx'
    change u * d = x at hxud
    subst hxud
    have e : t * (u * d) * t⁻¹ = (t * u * t⁻¹) * (t * d * t⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem_sup ((Subgroup.mem_normalizer_iff.1 (C.hMU htM) u).1 hu)
      ((Subgroup.mem_normalizer_iff.1 (le_normalizer_Dq C.h.le_normalizer htM) d).1 hd)
  have hpos : ∀ H K : Subgroup G, H.relIndex K ≠ 0 := fun H K => (Cfg.relIndex_pos' H K).ne'
  have hqpos : 0 < Nat.card F := Nat.card_pos
  have hQT1 : Q.relIndex (T1 M T L) = Nat.card F ^ 3 := by
    rw [← C.card_rhoIm T1_le_sup]
    have e : C.rhoIm (T1 M T L) = C.T0bar := by
      ext g
      rw [C.mem_rhoIm]
      constructor
      · rintro ⟨x, hxK, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
      · rintro ⟨t, rfl⟩
        exact ⟨t, T1_le_sup t.2, t.2, rfl⟩
    rw [e, hT, card_Q₂]
  have hT0xQ : T0x ⊔ Q ≤ T1 M T L := sup_le hT0xT C.pCore_le_T1
  have hnQ : T0x ≤ Subgroup.normalizer (Q : Set G) :=
    hT0xT.trans fun t ht => le_normalizer_pCoreOf M (C.h.le (T1_le_T ht))
  have hQT0x : Q.relIndex (T0x ⊔ Q) ≤ Nat.card F := by
    rw [← C.card_rhoIm (hT0xQ.trans T1_le_sup)]
    refine (Subgroup.card_le_of_le ?_).trans card_X₂.le
    intro g hg
    obtain ⟨x, hxK, hx, rfl⟩ := (C.mem_rhoIm).1 hg
    have hx' : x ∈ ((T0x ⊔ Q : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnQ] at hx'
    obtain ⟨t, ht, q, hq, hxtq⟩ := hx'
    change t * q = x at hxtq
    subst hxtq
    obtain ⟨t₀, ht₀T, ht₀, rfl⟩ := mem_tImage.1 ht
    have htK := T1_le_sup (φ ⟨t₀, ht₀T⟩).2
    rw [C.rho_mul_eq htK (Subgroup.mem_sup_right hq) hxK,
      (C.rho_eq_one_iff ⟨q, Subgroup.mem_sup_right hq⟩).2 hq, mul_one]
    exact hK t₀ ht₀
  have hlow1 : Nat.card F ^ 2 ≤ (T0x ⊔ Q).relIndex (T1 M T L) := by
    have h := Subgroup.relIndex_mul_relIndex Q (T0x ⊔ Q) (T1 M T L) le_sup_right hT0xQ
    rw [hQT1] at h
    refine Nat.le_of_mul_le_mul_left ?_ hqpos
    calc Nat.card F * Nat.card F ^ 2 = Nat.card F ^ 3 := by ring
      _ = Q.relIndex (T0x ⊔ Q) * (T0x ⊔ Q).relIndex (T1 M T L) := h.symm
      _ ≤ Nat.card F * (T0x ⊔ Q).relIndex (T1 M T L) := Nat.mul_le_mul_right _ hQT0x
  have hYUD : Y ⊓ UD ≤ C.Usub W₀ ⊔ Dq M L := by
    rintro y ⟨hyY, hyUD⟩
    have hnD : T0x ≤ Subgroup.normalizer (Dq M L : Set G) := hT0xT.trans hDn
    have hy1 : y ∈ ((Y : Subgroup G) : Set G) := hyY
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnD] at hy1
    obtain ⟨t, ht, d, hd, hytd⟩ := hy1
    change t * d = y at hytd
    have hn : Uq M T L ≤ Subgroup.normalizer (Dq M L : Set G) :=
      (Uq_le C.h.L_le).trans (le_normalizer_Dq C.h.le_normalizer)
    have hy2 : y ∈ ((UD : Subgroup G) : Set G) := hyUD
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn] at hy2
    obtain ⟨u, hu, d', hd', hyud⟩ := hy2
    change u * d' = y at hyud
    obtain ⟨t₀, ht₀T, ht₀, ht₀e⟩ := mem_tImage.1 ht
    obtain ⟨d₁, hd₁T, hd₁, hd₁e⟩ := mem_tImage.1 hd₀
    have htc : t * d₀ = d₀ * t := by
      have h1 : t₀ * d₁ = d₁ * t₀ := Subgroup.mem_centralizer_iff.1 hd₁.2 t₀ ht₀.2
      have h2 : (⟨t₀, ht₀T⟩ : ↥(T1 M T L)) * ⟨d₁, hd₁T⟩ = ⟨d₁, hd₁T⟩ * ⟨t₀, ht₀T⟩ :=
        Subtype.ext h1
      have h3 := congrArg (fun x => ((φ x : ↥(T1 M T L)) : G)) h2
      simp only [map_mul, Subgroup.coe_mul] at h3
      rw [← ht₀e, ← hd₁e]
      exact h3
    have hd₀M : d₀ ∈ M := C.h.le (T1_le_T (tImage_le φ _ hd₀))
    have hDnorm : d₀ ∈ Subgroup.normalizer (Dq M L : Set G) :=
      le_normalizer_Dq C.h.le_normalizer hd₀M
    have hcu : d₀ * u * d₀⁻¹ ∈ Uq M T L := (Subgroup.mem_normalizer_iff.1 (C.hMU hd₀M) u).1 hu
    have h1 : u⁻¹ * (d₀ * u * d₀⁻¹) ∈ Dq M L := by
      have hu' : u = t * d * d'⁻¹ := by rw [hytd, ← hyud]; group
      have e : u⁻¹ * (d₀ * u * d₀⁻¹) = d' * d⁻¹ * (d₀ * (d * d'⁻¹) * d₀⁻¹) := by
        rw [hu']
        have : t⁻¹ * d₀ * t = d₀ := by rw [mul_assoc, ← htc]; group
        calc (t * d * d'⁻¹)⁻¹ * (d₀ * (t * d * d'⁻¹) * d₀⁻¹)
            = d' * d⁻¹ * (t⁻¹ * d₀ * t) * (d * d'⁻¹) * d₀⁻¹ := by group
          _ = d' * d⁻¹ * (d₀ * (d * d'⁻¹) * d₀⁻¹) := by rw [this]; group
      rw [e]
      exact (Dq M L).mul_mem ((Dq M L).mul_mem hd' ((Dq M L).inv_mem hd))
        ((Subgroup.mem_normalizer_iff.1 hDnorm _).1
          ((Dq M L).mul_mem hd ((Dq M L).inv_mem hd')))
    have h2 : C.N.co ⟨u, hu⟩ = C.N.co ⟨d₀ * u * d₀⁻¹, hcu⟩ := by
      rw [C.N.co_eq_co_iff]
      show u⁻¹ * (d₀ * u * d₀⁻¹) ∈ Uq M T L ⊓ Subgroup.centralizer (L : Set G)
      exact ⟨(Uq M T L).mul_mem ((Uq M T L).inv_mem hu) hcu, h1.2⟩
    have h3 : mat (C.rho ⟨d₀, T1_le_sup (tImage_le φ _ hd₀)⟩) *ᵥ C.N.co ⟨u, hu⟩ =
        C.N.co ⟨u, hu⟩ :=
      (C.co_conj ⟨d₀, T1_le_sup (tImage_le φ _ hd₀)⟩ (u := ⟨u, hu⟩)
        (v := ⟨d₀ * u * d₀⁻¹, hcu⟩) rfl).symm.trans h2.symm
    rw [← hyud]
    exact Subgroup.mul_mem_sup ((C.mem_Usub).2 ⟨hu, hfix₀ _ h3⟩) hd'
  have hlow2 : Nat.card F ^ 2 ≤ Y.relIndex (T0x ⊔ Q) := by
    have hUDY : UD ⊔ Y ≤ T0x ⊔ Q :=
      sup_le (hUDQ.trans le_sup_right) (sup_le le_sup_left (hDQ.trans le_sup_right))
    have h1 := Subgroup.relIndex_le_of_le_right hUDY (hpos Y (T0x ⊔ Q))
    have h2 : Y.relIndex UD = Y.relIndex (UD ⊔ Y) :=
      relIndex_eq_of_sup le_sup_left le_sup_right ((sup_le (hUDQ.trans C.pCore_le_T1) hYT).trans
        hUDn) rfl
    have h3 := Subgroup.relIndex_le_of_le_left hYUD (hpos (Y ⊓ UD) UD)
    rw [Subgroup.inf_relIndex_right, C.relIndex_Usub_sup, C.relIndex_Usub_ker f hf] at h3
    calc Nat.card F ^ 2 = Nat.card F * Nat.card F := by ring
      _ ≤ Y.relIndex UD := h3
      _ = Y.relIndex (UD ⊔ Y) := h2
      _ ≤ Y.relIndex (T0x ⊔ Q) := h1
  have hYle : Y ≤ T0x ⊔ Q := sup_le le_sup_left (hDQ.trans le_sup_right)
  have hlowY : Y.relIndex (T1 M T L) = Y.relIndex (T0x ⊔ Q) * (T0x ⊔ Q).relIndex (T1 M T L) :=
    (Subgroup.relIndex_mul_relIndex Y (T0x ⊔ Q) (T1 M T L) hYle hT0xQ).symm
  have hT1sup : T0x ⊔ Qx = T1 M T L := by
    refine le_antisymm (sup_le hT0xT hQxT) fun t ht => ?_
    obtain ⟨l, hl, q, hq, e⟩ := C.exists_mul_of_mem_T1 (φ⁻¹ ⟨t, ht⟩).2
    have hlT : l ∈ T1 M T L := T_inf_L_le_T1 hl
    have hqT := C.pCore_le_T1 hq
    have hte : t = ((φ ⟨l, hlT⟩ : ↥(T1 M T L)) : G) * ((φ ⟨q, hqT⟩ : ↥(T1 M T L)) : G) := by
      have : (⟨l, hlT⟩ * ⟨q, hqT⟩ : ↥(T1 M T L)) = φ⁻¹ ⟨t, ht⟩ := Subtype.ext e
      have h1 := congrArg (fun x => ((φ x : ↥(T1 M T L)) : G)) this
      simp only [map_mul, Subgroup.coe_mul, MulAut.apply_inv_self] at h1
      exact h1.symm
    rw [hte]
    exact Subgroup.mul_mem_sup (mem_tImage.2 ⟨l, hlT, hl, rfl⟩)
      (mem_tImage.2 ⟨q, hqT, hq, rfl⟩)
  have hZT1 : Z.relIndex (T1 M T L) ≤ r := by
    have e1 := relIndex_eq_of_sup hQxT hZT hQxn
      (le_antisymm (sup_le hQxT hZT) (hT1sup ▸ sup_le (le_sup_left.trans le_sup_right)
        le_sup_left))
    rw [← e1]
    have h2 := Subgroup.relIndex_le_of_le_left
      (sup_le (hUtT0x.trans le_sup_left) le_sup_right : Ut M T L φ ⊔ D₁ ≤ Z) (hpos _ Qx)
    have h3 : (Ut M T L φ ⊔ D₁).relIndex Qx = r := by
      rw [← tImage_sup φ C.Uq_le_T1 hDT, relIndex_tImage φ (sup_le C.Uq_le_T1 hDT)
        C.pCore_le_T1]
    rw [h3] at h2
    exact h2
  have hUB1 : Y.relIndex (T1 M T L) ≤ (Y ⊓ D₁).relIndex D₁ * r := by
    have h1 := Subgroup.relIndex_le_of_le_left (L := T1 M T L) (inf_le_left : Y ⊓ Z ≤ Y)
      (hpos _ _)
    have h2 := Subgroup.relIndex_mul_relIndex (Y ⊓ Z) Z (T1 M T L) inf_le_right hZT
    have h3 : (Y ⊓ Z).relIndex D₁ = (Y ⊓ Z).relIndex Z :=
      relIndex_eq_of_sup le_sup_right inf_le_right (hZT.trans hD₁n)
        (le_antisymm (sup_le le_sup_right inf_le_right)
          (sup_le (le_inf le_sup_left le_sup_left |>.trans le_sup_right) le_sup_left))
    have h4 : (Y ⊓ Z).relIndex D₁ = (Y ⊓ D₁).relIndex D₁ := by
      rw [← Subgroup.inf_relIndex_right (Y ⊓ Z), ← Subgroup.inf_relIndex_right (Y ⊓ D₁)]
      congr 1
      rw [inf_assoc, inf_eq_right.2 (le_sup_right : D₁ ≤ Z), inf_assoc, inf_idem]
    rw [← h3, h4] at h2
    calc Y.relIndex (T1 M T L) ≤ (Y ⊓ Z).relIndex (T1 M T L) := h1
      _ = (Y ⊓ D₁).relIndex D₁ * Z.relIndex (T1 M T L) := h2.symm
      _ ≤ (Y ⊓ D₁).relIndex D₁ * r := Nat.mul_le_mul_left _ hZT1
  have hD₁Dn : T1 M T L ≤ Subgroup.normalizer ((D₁ ⊓ Dq M L : Subgroup G) : Set G) :=
    hnorm (inf_le_left.trans hD₁T) fun t ht x hx =>
      ⟨C.conj_mem_Dt_of_T1 φ ht hx.1,
        (Subgroup.mem_normalizer_iff.1 (hDn ht) x).1 hx.2⟩
  have hA₁T : A₁ ≤ T1 M T L := hA₁D₁.trans hD₁T
  have hUB2 : (A₁ ⊔ (D₁ ⊓ Dq M L)).relIndex D₁ * Nat.card F = (D₁ ⊓ Dq M L).relIndex D₁ := by
    have h1 := Subgroup.relIndex_mul_relIndex (D₁ ⊓ Dq M L) (A₁ ⊔ (D₁ ⊓ Dq M L)) D₁
      le_sup_right (sup_le hA₁D₁ inf_le_left)
    have h2 : (D₁ ⊓ Dq M L).relIndex (A₁ ⊔ (D₁ ⊓ Dq M L)) = (D₁ ⊓ Dq M L).relIndex A₁ :=
      relIndex_eq_of_sup_normal le_sup_right le_sup_left
        ((sup_le hA₁T (inf_le_left.trans hD₁T)).trans hD₁Dn) (sup_comm _ _)
    have h3 : (D₁ ⊓ Dq M L).relIndex A₁ = Nat.card F := by
      rw [← Subgroup.inf_relIndex_right, inf_comm (D₁ ⊓ Dq M L), ← inf_assoc,
        inf_eq_left.2 hA₁D₁, hA₁D, Subgroup.relIndex_bot_left, hA₁card]
    rw [h2, h3, mul_comm] at h1
    exact h1
  have hDUD : (Dq M L).relIndex UD = Nat.card F ^ 4 := by
    rw [relIndex_eq_of_sup_normal le_sup_right le_sup_left
      ((sup_le (C.Uq_le_T1) hDT).trans hDn) (sup_comm _ _), ← Subgroup.inf_relIndex_right,
      inf_comm, C.Uq_inf_Dq]
    have c1 := Subgroup.relIndex_mul_card (Uq M T L ⊓ Subgroup.centralizer (L : Set G))
      (Uq M T L)
    rw [inf_eq_left.2 (inf_le_left : Uq M T L ⊓ Subgroup.centralizer (L : Set G) ≤ Uq M T L),
      C.card_Uq, C.card_V4] at c1
    have hFn : Nat.card F = 2 ^ C.k := by rw [Nat.card_eq_fintype_card, C.hF]
    rw [hFn]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos c1
  have hDP : (Dq M L).relIndex P = Nat.card F ^ 3 := by
    have h1 := Subgroup.relIndex_mul_relIndex (Dq M L) P UD le_sup_right
      (sup_le_sup_right (C.Usub_le _) _)
    rw [C.relIndex_Usub_sup, C.relIndex_Usub_perp, hDUD] at h1
    refine Nat.eq_of_mul_eq_mul_right hqpos ?_
    rw [h1]
    ring
  have hUB3 : (D₁ ⊓ Dq M L).relIndex D₁ ≤ Nat.card ↥E * Nat.card F ^ 3 := by
    rw [inf_comm]
    have h1 := Subgroup.relIndex_mul_relIndex (Dq M L ⊓ D₁) (Q ⊓ D₁) D₁
      (inf_le_inf_right _ hDQ) inf_le_right
    rw [Subgroup.inf_relIndex_right] at h1
    have h2 : Q.relIndex D₁ = Nat.card ↥E := by
      rw [hEdef, C.card_rhoIm (hD₁T.trans T1_le_sup)]
    have h3 : (Dq M L ⊓ D₁).relIndex (Q ⊓ D₁) = (Dq M L).relIndex (Q ⊓ D₁) := by
      rw [← Subgroup.inf_relIndex_right (Dq M L ⊓ D₁), ← Subgroup.inf_relIndex_right (Dq M L)]
      congr 1
      ext x
      simp only [Subgroup.mem_inf]
      tauto
    have h4 : Q ⊓ D₁ ≤ P := by
      intro x hx
      have hxQt : x ∈ Qx := tImage_mono' φ hDQ hx.2
      obtain ⟨u, hu, hud⟩ := C.inf_Qt_of_rhoIm φ hE x ⟨hx.1, hxQt⟩
      have e : x = u * (u⁻¹ * x) := by group
      rw [e]
      exact Subgroup.mul_mem_sup hu hud
    have h5 := Subgroup.relIndex_le_of_le_right h4 (hpos (Dq M L) P)
    rw [h2, h3] at h1
    rw [← h1, mul_comm]
    exact Nat.mul_le_mul_left _ (h5.trans hDP.le)
  have hYD₁ : A₁ ⊔ (D₁ ⊓ Dq M L) ≤ Y ⊓ D₁ :=
    sup_le (le_inf (hA₁T0x.trans le_sup_left) hA₁D₁)
      (le_inf (inf_le_right.trans le_sup_right) inf_le_left)
  have hcc' := Subgroup.relIndex_le_of_le_left (L := D₁) hYD₁ (hpos _ D₁)
  have hlow : Nat.card F ^ 4 ≤ Y.relIndex (T1 M T L) := by
    rw [hlowY]
    calc Nat.card F ^ 4 = Nat.card F ^ 2 * Nat.card F ^ 2 := by ring
      _ ≤ _ := Nat.mul_le_mul hlow2 hlow1
  have hchain : Y.relIndex (T1 M T L) * Nat.card F ≤ Nat.card F ^ 5 := by
    calc Y.relIndex (T1 M T L) * Nat.card F ≤ (Y ⊓ D₁).relIndex D₁ * r * Nat.card F :=
          Nat.mul_le_mul_right _ hUB1
      _ ≤ (A₁ ⊔ (D₁ ⊓ Dq M L)).relIndex D₁ * r * Nat.card F :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hcc')
      _ = (D₁ ⊓ Dq M L).relIndex D₁ * r := by rw [← hUB2]; ring
      _ ≤ Nat.card ↥E * Nat.card F ^ 3 * r := Nat.mul_le_mul_right _ hUB3
      _ = Nat.card F ^ 2 * (r * Nat.card F * Nat.card ↥E) := by ring
      _ = Nat.card F ^ 5 := by rw [hsize]; ring
  have hc : (Y ⊓ D₁).relIndex D₁ = (A₁ ⊔ (D₁ ⊓ Dq M L)).relIndex D₁ := by
    refine le_antisymm hcc' ?_
    have h1 : (A₁ ⊔ (D₁ ⊓ Dq M L)).relIndex D₁ * r * Nat.card F ≤ Nat.card F ^ 5 := by
      calc (A₁ ⊔ (D₁ ⊓ Dq M L)).relIndex D₁ * r * Nat.card F = (D₁ ⊓ Dq M L).relIndex D₁ * r :=
            by rw [← hUB2]; ring
        _ ≤ Nat.card ↥E * Nat.card F ^ 3 * r := Nat.mul_le_mul_right _ hUB3
        _ = Nat.card F ^ 2 * (r * Nat.card F * Nat.card ↥E) := by ring
        _ = Nat.card F ^ 5 := by rw [hsize]; ring
    have h2 : Nat.card F ^ 5 ≤ (Y ⊓ D₁).relIndex D₁ * r * Nat.card F := by
      calc Nat.card F ^ 5 = Nat.card F ^ 4 * Nat.card F := by ring
        _ ≤ Y.relIndex (T1 M T L) * Nat.card F := Nat.mul_le_mul_right _ hlow
        _ ≤ (Y ⊓ D₁).relIndex D₁ * r * Nat.card F := Nat.mul_le_mul_right _ hUB1
    have h3 := h1.trans h2
    have hrq : 0 < r * Nat.card F := Nat.mul_pos hr0 hqpos
    rw [mul_assoc, mul_assoc] at h3
    exact Nat.le_of_mul_le_mul_right h3 hrq
  have hYD₁eq : Y ⊓ D₁ ≤ A₁ ⊔ (D₁ ⊓ Dq M L) := by
    have h1 := Subgroup.relIndex_mul_relIndex (A₁ ⊔ (D₁ ⊓ Dq M L)) (Y ⊓ D₁) D₁ hYD₁ inf_le_right
    rw [hc] at h1
    have h2 : (A₁ ⊔ (D₁ ⊓ Dq M L)).relIndex (Y ⊓ D₁) = 1 := by
      have hp : 0 < (A₁ ⊔ (D₁ ⊓ Dq M L)).relIndex D₁ := Cfg.relIndex_pos' _ _
      have : (A₁ ⊔ (D₁ ⊓ Dq M L)).relIndex (Y ⊓ D₁) * (A₁ ⊔ (D₁ ⊓ Dq M L)).relIndex D₁ =
          1 * (A₁ ⊔ (D₁ ⊓ Dq M L)).relIndex D₁ := by rw [h1, one_mul]
      exact Nat.eq_of_mul_eq_mul_right hp this
    exact Subgroup.relIndex_eq_one.1 h2
  have hb1 : Y.relIndex (T0x ⊔ Q) = Nat.card F ^ 2 := by
    refine le_antisymm ?_ hlow2
    have h1 : Y.relIndex (T1 M T L) ≤ Nat.card F ^ 4 := by
      have := hchain
      have h5 : Nat.card F ^ 5 = Nat.card F ^ 4 * Nat.card F := by ring
      rw [h5] at this
      exact Nat.le_of_mul_le_mul_right this hqpos
    rw [hlowY] at h1
    by_contra hlt
    push Not at hlt
    have : Nat.card F ^ 2 * Nat.card F ^ 2 < Y.relIndex (T0x ⊔ Q) * (T0x ⊔ Q).relIndex
        (T1 M T L) := Nat.mul_lt_mul_of_lt_of_le hlt hlow1 (Nat.pos_of_ne_zero (hpos _ _))
    nlinarith
  have hW₀Y : C.Usub W₀ ≤ Y := by
    have hUDY : UD ⊔ Y ≤ T0x ⊔ Q :=
      sup_le (hUDQ.trans le_sup_right) (sup_le le_sup_left (hDQ.trans le_sup_right))
    have h1 := Subgroup.relIndex_le_of_le_right hUDY (hpos Y (T0x ⊔ Q))
    have h2 : Y.relIndex UD = Y.relIndex (UD ⊔ Y) :=
      relIndex_eq_of_sup le_sup_left le_sup_right ((sup_le (hUDQ.trans C.pCore_le_T1) hYT).trans
        hUDn) rfl
    have h3 := Subgroup.relIndex_mul_relIndex (Y ⊓ UD) (C.Usub W₀ ⊔ Dq M L) UD hYUD
      (sup_le_sup_right (C.Usub_le _) _)
    rw [Subgroup.inf_relIndex_right, C.relIndex_Usub_sup, C.relIndex_Usub_ker f hf] at h3
    have h4 : Y.relIndex UD ≤ Nat.card F * Nat.card F := by
      rw [h2]
      calc Y.relIndex (UD ⊔ Y) ≤ Y.relIndex (T0x ⊔ Q) := h1
        _ = Nat.card F * Nat.card F := by rw [hb1]; ring
    have h5 : (Y ⊓ UD).relIndex (C.Usub W₀ ⊔ Dq M L) = 1 := by
      have hp : 0 < Nat.card F * Nat.card F := Nat.mul_pos hqpos hqpos
      have h6 : (Y ⊓ UD).relIndex (C.Usub W₀ ⊔ Dq M L) * (Nat.card F * Nat.card F) ≤
          1 * (Nat.card F * Nat.card F) := by rw [h3, one_mul]; exact h4
      have h7 := Nat.le_of_mul_le_mul_right h6 hp
      have h8 := hpos (Y ⊓ UD) (C.Usub W₀ ⊔ Dq M L)
      omega
    exact (le_sup_left.trans (Subgroup.relIndex_eq_one.1 h5)).trans inf_le_left
  have hd₀K : d₀ ∈ L ⊔ pCoreOf 2 M := T1_le_sup (tImage_le φ _ hd₀)
  have hd₀M : d₀ ∈ M := C.sup_le_M hd₀K
  apply hd₀1
  refine C.rho_Dt_eq_one φ hE hE' hd₀ hd₀K (mem_X₂_of_sub_mem fun v => ?_)
  obtain ⟨u, rfl⟩ := C.N.co_surj v
  have hcW := hcommW u u.2 d₀ hd₀
  have hcU : ⁅d₀, (u : G)⁆ ∈ Uq M T L := C.Usub_le _ hcW
  have hcD : ⁅d₀, (u : G)⁆ ∈ D₁ := by
    have e : ⁅d₀, (u : G)⁆ = d₀ * ((u : G) * d₀⁻¹ * (u : G)⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact D₁.mul_mem hd₀ (C.conj_mem_Dt_of_T1 φ (C.Uq_le_T1 u.2) (D₁.inv_mem hd₀))
  have hcA : ⁅d₀, (u : G)⁆ ∈ A₁ ⊔ (D₁ ⊓ Dq M L) := hYD₁eq ⟨hW₀Y hcW, hcD⟩
  have hnA : A₁ ≤ Subgroup.normalizer ((D₁ ⊓ Dq M L : Subgroup G) : Set G) := hA₁T.trans hD₁Dn
  have hcA' : ⁅d₀, (u : G)⁆ ∈ ((A₁ ⊔ (D₁ ⊓ Dq M L) : Subgroup G) : Set G) := hcA
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnA] at hcA'
  obtain ⟨a, ha, x, hx, hax⟩ := hcA'
  change a * x = ⁅d₀, (u : G)⁆ at hax
  obtain ⟨haU, hapt⟩ := hA₁U a ha
  have hxU : x ∈ Uq M T L := by
    have e : x = a⁻¹ * ⁅d₀, (u : G)⁆ := by rw [← hax]; group
    rw [e]
    exact (Uq M T L).mul_mem ((Uq M T L).inv_mem haU) hcU
  have hco : C.N.co ⟨_, hcU⟩ = C.N.co ⟨a, haU⟩ := by
    have e : (⟨_, hcU⟩ : ↥(Uq M T L)) = ⟨a, haU⟩ * ⟨x, hxU⟩ := Subtype.ext hax.symm
    rw [e, C.N.co_mul, (C.N.co_eq_zero_iff ⟨x, hxU⟩).2 ⟨hxU, hx.2.2⟩, add_zero]
  have h1 := C.co_comm hd₀M u.2 hcU
  rw [show C.act hd₀M = C.act (C.sup_le_M hd₀K) from rfl, C.rho_spec ⟨d₀, hd₀K⟩] at h1
  rw [show C.N.co u = C.N.co ⟨(u : G), u.2⟩ from rfl, ← h1, hco]
  exact hapt

end Cfg

end CFSG.Quasithin.MS93.S37
