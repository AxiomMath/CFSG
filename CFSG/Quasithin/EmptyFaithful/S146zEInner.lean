module

public import CFSG.Quasithin.EmptyFaithful.S146zECount
public import CFSG.Quasithin.EmptyFaithful.S146zEPure

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin.ThreeD

section Inner

variable {G : Type} [Group G] [Finite G] {T M K Kp U₁ U₂ : Subgroup G} {s : G}

local notation "Zz" => quasithinOmegaOneCenter T

omit [Finite G] in
@[expose] def cPart (T M Kp : Subgroup G) : Subgroup G :=
  (⁅uOfL22 T M, Kp⁆ ⊔ quasithinOmegaOneCenter T) ⊔ cuOf T M

omit [Finite G] in
theorem cPart_le (hKp : Kp ≤ mcOf T) : cPart T M Kp ≤ uOfL22 T M :=
  sup_le (commutator_sup_le_U (T := T) (M := M) hKp) (cuOf_le T M)

theorem exists_decomp_three (S : Setting146 G T M) (hc23 : Conc14623 T M)
    (cK : ThreeC.CCtx T M K U₁ U₂ s) (hKp : Kp ∈ cComp (mcOf T))
    (hcomps : ∀ L ∈ cComp (mcOf T), L = K ∨ L = Kp) {v : G} (hv : v ∈ uOfL22 T M) :
    ∃ a ∈ U₁, ∃ b ∈ U₂, ∃ c ∈ cPart T M Kp, v = a * (b * c) := by
  classical
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := exists_decomp_two S hc23 hcomps cK.hKc hKp hv
  rw [cK.hsup] at ha
  have hUN : U₁ ≤ Subgroup.normalizer (U₂ : Set G) :=
    le_normalizer_of_forall_commute fun x hx y hy =>
      S.comm_of_mem_conjClosure (cK.hU₁U hx) (cK.hU₂U hy)
  have ha' : a ∈ ((U₁ ⊔ U₂ : Subgroup G) : Set G) := ha
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hUN] at ha'
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Set.mem_mul.mp ha'
  have hbc : b * c ∈ cPart T M Kp :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right hc)
  exact ⟨y₁, hy₁, y₂, hy₂, b * c, hbc, by group⟩

theorem mem_pCoreOf_of_trivial3 (S : Setting146 G T M) (hc23 : Conc14623 T M)
    (cK : ThreeC.CCtx T M K U₁ U₂ s) (hKp : Kp ∈ cComp (mcOf T))
    (hcomps : ∀ L ∈ cComp (mcOf T), L = K ∨ L = Kp) {x : G}
    (hxH : x ∈ mcOf T) (h₁ : ∀ y ∈ U₁, x * y * x⁻¹ * y⁻¹ ∈ Zz)
    (h₂ : ∀ y ∈ U₂, x * y * x⁻¹ * y⁻¹ ∈ Zz)
    (h₃ : ∀ y ∈ cPart T M Kp, x * y * x⁻¹ * y⁻¹ ∈ Zz) : x ∈ pCoreOf 2 (mcOf T) := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hcommU : ∀ a ∈ uOfL22 T M, ∀ b ∈ uOfL22 T M, a * b = b * a := fun a ha b hb =>
    S.comm_of_mem_conjClosure ha hb
  have haNU : x ∈ Subgroup.normalizer (uOfL22 T M : Set G) := le_normalizer_conjClosure _ _ hxH
  have haEU : ∀ a ∈ uOfL22 T M, x * a * x⁻¹ ∈ uOfL22 T M := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp haNU a).mp ha
  have hxZ : x ∈ Subgroup.normalizer (Zz : Set G) := by rw [S.normalizer_Z]; exact hxH
  rw [← S.lemma_14_5_15_four hG]
  refine ⟨hxH, hxZ, fun v hv => ?_⟩
  obtain ⟨y, hy, r₂, hr₂, d, hd, rfl⟩ := exists_decomp_three S hc23 cK hKp hcomps hv
  have hyU := cK.hU₁U hy
  have hr₂U := cK.hU₂U hr₂
  have hdU := cPart_le (le_of_mem_cComp hKp) hd
  have hr₂dU : r₂ * d ∈ uOfL22 T M := (uOfL22 T M).mul_mem hr₂U hdU
  rw [comm_mul_of_abelian hcommU haEU hyU hr₂dU, comm_mul_of_abelian hcommU haEU hr₂U hdU]
  exact Subgroup.mul_mem _ (h₁ y hy) (Subgroup.mul_mem _ (h₂ r₂ hr₂) (h₃ d hd))

theorem exists_mul_of_mem_cPart (S : Setting146 G T M) (hKp : Kp ≤ mcOf T) {y : G}
    (hy : y ∈ cPart T M Kp) :
    ∃ p ∈ ⁅uOfL22 T M, Kp⁆ ⊔ Zz, ∃ c ∈ cuOf T M, y = p * c := by
  have hUp := commutator_sup_le_U (T := T) (M := M) hKp
  have hN : ⁅uOfL22 T M, Kp⁆ ⊔ Zz ≤ Subgroup.normalizer ((cuOf T M : Subgroup G) : Set G) :=
    le_normalizer_of_forall_commute fun x hx y hy =>
      S.comm_of_mem_conjClosure (hUp hx) (cuOf_le T M hy)
  have hy' : y ∈ ((⁅uOfL22 T M, Kp⁆ ⊔ Zz ⊔ cuOf T M : Subgroup G) : Set G) := hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hy'
  obtain ⟨p, hp, c, hc, rfl⟩ := Set.mem_mul.mp hy'
  exact ⟨p, hp, c, hc, rfl⟩

theorem trivial_on_cPart (S : Setting146 G T M) (hKp : Kp ≤ mcOf T) {e : G} (heH : e ∈ mcOf T)
    (h : ∀ y ∈ ⁅uOfL22 T M, Kp⁆ ⊔ Zz, e * y * e⁻¹ * y⁻¹ ∈ Zz) :
    ∀ y ∈ cPart T M Kp, e * y * e⁻¹ * y⁻¹ ∈ Zz := by
  intro y hy
  obtain ⟨p, hp, c, hc, rfl⟩ := exists_mul_of_mem_cPart S hKp hy
  have hcommU : ∀ a ∈ uOfL22 T M, ∀ b ∈ uOfL22 T M, a * b = b * a := fun a ha b hb =>
    S.comm_of_mem_conjClosure ha hb
  have haNU : e ∈ Subgroup.normalizer (uOfL22 T M : Set G) := le_normalizer_conjClosure _ _ heH
  have haEU : ∀ a ∈ uOfL22 T M, e * a * e⁻¹ ∈ uOfL22 T M := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp haNU a).mp ha
  have hpU := commutator_sup_le_U (T := T) (M := M) hKp hp
  have hcU := cuOf_le T M hc
  rw [comm_mul_of_abelian hcommU haEU hpU hcU]
  refine Subgroup.mul_mem _ (h p hp) ?_
  have h1 := (mem_cuOf.mp hc).2.2 e heH
  have e1 : e * c * e⁻¹ * c⁻¹ = (c * e * c⁻¹ * e⁻¹)⁻¹ := by group
  rw [e1]; exact Subgroup.inv_mem _ h1

theorem all_inner3 (S : Setting146 G T M) (hc23 : Conc14623 T M)
    (cK : ThreeC.CCtx T M K U₁ U₂ s) (hKp : Kp ∈ cComp (mcOf T))
    (hcomps : ∀ L ∈ cComp (mcOf T), L = K ∨ L = Kp) {Ug Dg : Subgroup G}
    (hUgH : Ug ≤ mcOf T) (hUgK : Ug ≤ Subgroup.normalizer (K : Set G)) (hUgab : IsElemAbelian 2 Ug)
    (hDgeq : Dg = Ug ⊓ pCoreOf 2 (mcOf T)) (hrel : ¬ Dg.relIndex Ug ∣ 2)
    (hquad : ∀ b₁ ∈ Ug, ∀ b₂ ∈ Ug, ∀ x ∈ uOfL22 T M,
      b₂ * (b₁ * x * b₁⁻¹ * x⁻¹) * b₂⁻¹ * (b₁ * x * b₁⁻¹ * x⁻¹)⁻¹ ∈ Zz)
    (hUp : ∀ e ∈ Ug, ∀ y ∈ ⁅uOfL22 T M, Kp⁆ ⊔ Zz, e * y * e⁻¹ * y⁻¹ ∈ Zz) :
    ∀ b ∈ Ug, conjSub b U₁ = U₁ := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨b, hbUg, hne⟩ := hcon
  have hKpH : Kp ≤ mcOf T := le_of_mem_cComp hKp
  have hUab : IsElemAbelian 2 (uOfL22 T M) := S.lemma_14_5_15_two S.isHTM_mcOf
  have hcommU : ∀ a ∈ uOfL22 T M, ∀ b ∈ uOfL22 T M, a * b = b * a := fun a ha b hb =>
    S.comm_of_mem_conjClosure ha hb
  have hNU : ∀ d ∈ Ug, d ∈ Subgroup.normalizer (uOfL22 T M : Set G) := fun d hd =>
    le_normalizer_conjClosure _ _ (hUgH hd)
  have hNZ : ∀ d ∈ Ug, d ∈ Subgroup.normalizer (Zz : Set G) := fun d hd => by
    rw [S.normalizer_Z]; exact hUgH hd
  have hb2 : b * b = 1 := by
    have := isElemAbelian_pow_eq_one hUgab hbUg
    simpa [pow_two] using this
  have hbsw : conjSub b U₁ = U₂ :=
    (cK.normalizer_or S (hUgK hbUg) (hNU b hbUg) (hNZ b hbUg)).resolve_left hne
  have hswap2 : ∀ d : G, conjSub d U₁ = U₂ → d * d = 1 → conjSub d U₂ = U₁ := fun d hd hd2 => by
    rw [← hd, ← conjSub_mul, hd2, conjSub_one]
  have key : ∀ c' ∈ Ug, conjSub c' U₁ = U₁ → c' ∈ pCoreOf 2 (mcOf T) := by
    intro c' hc' hin
    have hc'H : c' ∈ mcOf T := hUgH hc'
    have hin₂ := cK.conjSub_U₂ S (hUgK hc') (hNU c' hc') (hNZ c' hc') hin
    have haN₁ : c' ∈ Subgroup.normalizer (U₁ : Set G) := mem_normalizer_of_conjSub_eq hin
    have haN₂ : c' ∈ Subgroup.normalizer (U₂ : Set G) := mem_normalizer_of_conjSub_eq hin₂
    have haNU : c' ∈ Subgroup.normalizer (uOfL22 T M : Set G) := hNU c' hc'
    have haEU : ∀ a ∈ uOfL22 T M, c' * a * c'⁻¹ ∈ uOfL22 T M := fun a ha =>
      (Subgroup.mem_normalizer_iff.mp haNU a).mp ha
    have hboth : ∀ x ∈ U₁, c' * (b * x * b⁻¹) * c'⁻¹ * (b * x * b⁻¹)⁻¹ ∈ Zz ∧
        c' * x * c'⁻¹ * x⁻¹ ∈ Zz := by
      intro x hx
      have hx₂ : b * x * b⁻¹ ∈ U₂ := by rw [← hbsw]; exact mul_mem_conjSub hx
      have h1 := hquad b hbUg c' hc' x (cK.hU₁U hx)
      have e1 : b * x * b⁻¹ * x⁻¹ = (b * x * b⁻¹) * x⁻¹ := rfl
      rw [e1, comm_mul_of_abelian hcommU haEU (cK.hU₂U hx₂) ((uOfL22 T M).inv_mem (cK.hU₁U hx))] at h1
      set p := c' * (b * x * b⁻¹) * c'⁻¹ * (b * x * b⁻¹)⁻¹ with hp
      set q := c' * x⁻¹ * c'⁻¹ * (x⁻¹)⁻¹ with hq
      have hpU₂ : p ∈ U₂ :=
        U₂.mul_mem ((Subgroup.mem_normalizer_iff.mp haN₂ _).mp hx₂) (U₂.inv_mem hx₂)
      have hqU₁ : q ∈ U₁ :=
        U₁.mul_mem ((Subgroup.mem_normalizer_iff.mp haN₁ _).mp (U₁.inv_mem hx)) (by simpa using hx)
      have hqZ : q ∈ Zz := by
        have e : q = p⁻¹ * (p * q) := by group
        have h2 : q ∈ U₂ := by
          rw [e]; exact U₂.mul_mem (U₂.inv_mem hpU₂) (cK.hZU₂ h1)
        exact cK.inf_U₂_eq ▸ ⟨hqU₁, h2⟩
      have hpZ : p ∈ Zz := by
        have e : p = (p * q) * q⁻¹ := by group
        rw [e]; exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hqZ)
      refine ⟨hpZ, ?_⟩
      have hr : c' * x * c'⁻¹ ∈ uOfL22 T M := haEU x (cK.hU₁U hx)
      have hc : (c' * x * c'⁻¹) * x⁻¹ = x⁻¹ * (c' * x * c'⁻¹) :=
        hcommU _ hr _ ((uOfL22 T M).inv_mem (cK.hU₁U hx))
      have e : c' * x * c'⁻¹ * x⁻¹ = q⁻¹ := by
        calc c' * x * c'⁻¹ * x⁻¹ = x⁻¹ * (c' * x * c'⁻¹) := hc
          _ = q⁻¹ := by rw [hq]; group
      rw [e]; exact Subgroup.inv_mem _ hqZ
    refine mem_pCoreOf_of_trivial3 S hc23 cK hKp hcomps hc'H (fun y hy => (hboth y hy).2)
      (fun y hy => ?_) (trivial_on_cPart S hKpH hc'H (hUp c' hc'))
    have hy' : b⁻¹ * y * b ∈ U₁ := mem_conjSub.mp (hbsw ▸ hy)
    have e : b * (b⁻¹ * y * b) * b⁻¹ = y := by group
    have := (hboth _ hy').1
    rwa [e] at this
  have hmem : ∀ d ∈ Ug, d * b ∈ Dg ∨ d ∈ Dg := by
    intro d hd
    rcases cK.normalizer_or S (hUgK hd) (hNU d hd) (hNZ d hd) with hin | hsw
    · right
      exact hDgeq ▸ ⟨hd, key d hd hin⟩
    · left
      have hd2 : d * d = 1 := by
        have := isElemAbelian_pow_eq_one hUgab hd
        simpa [pow_two] using this
      have hin : conjSub (d * b) U₁ = U₁ := by
        rw [conjSub_mul, hbsw, hswap2 d hsw hd2]
      exact hDgeq ▸ ⟨Ug.mul_mem hd hbUg, key _ (Ug.mul_mem hd hbUg) hin⟩
  exact hrel (Subgroup.relIndex_dvd_two_iff.mpr ⟨b, hbUg, hmem⟩)

end Inner

end CFSG.Quasithin.ThreeD
