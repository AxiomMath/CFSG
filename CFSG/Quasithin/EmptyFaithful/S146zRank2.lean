module

public import CFSG.Quasithin.EmptyFaithful.S146zCtx
public import CFSG.Quasithin.EmptyFaithful.S146zGen
public import CFSG.Quasithin.EmptyFaithful.S146F22
public import CFSG.Quasithin.Background.F9Sixteen
public import Certificates.Kernel.J4Count.FixCE

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin

section AllInner

variable {G : Type} [Group G] [Finite G] {T M K U₁ U₂ : Subgroup G} {s u : G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem FCtx.mem_pCoreOf_of_trivial (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u) {x : G}
    (hxH : x ∈ mcOf T) (h₁ : ∀ y ∈ U₁, x * y * x⁻¹ * y⁻¹ ∈ Zz)
    (h₂ : ∀ y ∈ U₂, x * y * x⁻¹ * y⁻¹ ∈ Zz) : x ∈ pCoreOf 2 (mcOf T) := by
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
  obtain ⟨y, hy, r₂, hr₂, d, hd, rfl⟩ := c.exists_decomp3 S hv
  have hyU := c.hU₁U hy
  have hr₂U := c.hU₂U hr₂
  have hdU := cuOf_le T M hd
  have hr₂dU : r₂ * d ∈ uOfL22 T M := (uOfL22 T M).mul_mem hr₂U hdU
  rw [comm_mul_of_abelian hcommU haEU hyU hr₂dU, comm_mul_of_abelian hcommU haEU hr₂U hdU]
  refine Subgroup.mul_mem _ (h₁ y hy) (Subgroup.mul_mem _ (h₂ r₂ hr₂) ?_)
  have h1 := (mem_cuOf.mp hd).2.2 x hxH
  have e : x * d * x⁻¹ * d⁻¹ = (d * x * d⁻¹ * x⁻¹)⁻¹ := by group
  rw [e]; exact Subgroup.inv_mem _ h1


theorem FCtx.all_inner (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u) {Ug Dg : Subgroup G}
    (hUgH : Ug ≤ mcOf T) (hUgab : IsElemAbelian 2 Ug)
    (hDgeq : Dg = Ug ⊓ pCoreOf 2 (mcOf T)) (hrel : ¬ Dg.relIndex Ug ∣ 2)
    (hquad : ∀ b₁ ∈ Ug, ∀ b₂ ∈ Ug, ∀ x ∈ uOfL22 T M,
      b₂ * (b₁ * x * b₁⁻¹ * x⁻¹) * b₂⁻¹ * (b₁ * x * b₁⁻¹ * x⁻¹)⁻¹ ∈ Zz) :
    ∀ b ∈ Ug, conjSub b U₁ = U₁ := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨b, hbUg, hne⟩ := hcon
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hUab : IsElemAbelian 2 (uOfL22 T M) := S.lemma_14_5_15_two hG
  have hcommU : ∀ a ∈ uOfL22 T M, ∀ b ∈ uOfL22 T M, a * b = b * a := fun a ha b hb =>
    S.comm_of_mem_conjClosure ha hb
  have hbH : b ∈ mcOf T := hUgH hbUg
  have hb2 : b * b = 1 := by
    have := isElemAbelian_pow_eq_one hUgab hbUg
    simpa [pow_two] using this
  have hbsw : conjSub b U₁ = U₂ := (c.normalizer_or S hbH).resolve_left hne
  have hswap2 : ∀ d : G, conjSub d U₁ = U₂ → d * d = 1 → conjSub d U₂ = U₁ := fun d hd hd2 => by
    rw [← hd, ← conjSub_mul, hd2, conjSub_one]
  have key : ∀ c' ∈ Ug, conjSub c' U₁ = U₁ → c' ∈ pCoreOf 2 (mcOf T) := by
    intro c' hc' hin
    have hc'H : c' ∈ mcOf T := hUgH hc'
    have hin₂ := c.conjSub_U₂ S hc'H hin
    have haN₁ : c' ∈ Subgroup.normalizer (U₁ : Set G) := mem_normalizer_of_conjSub_eq hin
    have haN₂ : c' ∈ Subgroup.normalizer (U₂ : Set G) := mem_normalizer_of_conjSub_eq hin₂
    have haNU : c' ∈ Subgroup.normalizer (uOfL22 T M : Set G) := le_normalizer_conjClosure _ _ hc'H
    have haEU : ∀ a ∈ uOfL22 T M, c' * a * c'⁻¹ ∈ uOfL22 T M := fun a ha =>
      (Subgroup.mem_normalizer_iff.mp haNU a).mp ha
    have hboth : ∀ x ∈ U₁, c' * (b * x * b⁻¹) * c'⁻¹ * (b * x * b⁻¹)⁻¹ ∈ Zz ∧
        c' * x * c'⁻¹ * x⁻¹ ∈ Zz := by
      intro x hx
      have hx₂ : b * x * b⁻¹ ∈ U₂ := by rw [← hbsw]; exact mul_mem_conjSub hx
      have h1 := hquad b hbUg c' hc' x (c.hU₁U hx)
      have e1 : b * x * b⁻¹ * x⁻¹ = (b * x * b⁻¹) * x⁻¹ := rfl
      rw [e1, comm_mul_of_abelian hcommU haEU (c.hU₂U hx₂) ((uOfL22 T M).inv_mem (c.hU₁U hx))] at h1
      set p := c' * (b * x * b⁻¹) * c'⁻¹ * (b * x * b⁻¹)⁻¹ with hp
      set q := c' * x⁻¹ * c'⁻¹ * (x⁻¹)⁻¹ with hq
      have hpU₂ : p ∈ U₂ := U₂.mul_mem ((Subgroup.mem_normalizer_iff.mp haN₂ _).mp hx₂) (U₂.inv_mem hx₂)
      have hqU₁ : q ∈ U₁ :=
        U₁.mul_mem ((Subgroup.mem_normalizer_iff.mp haN₁ _).mp (U₁.inv_mem hx)) (by simpa using hx)
      have hqZ : q ∈ Zz := by
        have e : q = p⁻¹ * (p * q) := by group
        have h2 : q ∈ U₂ := by
          rw [e]; exact U₂.mul_mem (U₂.inv_mem hpU₂) (c.hZU₂ h1)
        exact c.inf_U₂_eq ▸ ⟨hqU₁, h2⟩
      have hpZ : p ∈ Zz := by
        have e : p = (p * q) * q⁻¹ := by group
        rw [e]; exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hqZ)
      refine ⟨hpZ, ?_⟩
      have hr : c' * x * c'⁻¹ ∈ uOfL22 T M := haEU x (c.hU₁U hx)
      have hc : (c' * x * c'⁻¹) * x⁻¹ = x⁻¹ * (c' * x * c'⁻¹) :=
        hcommU _ hr _ ((uOfL22 T M).inv_mem (c.hU₁U hx))
      have e : c' * x * c'⁻¹ * x⁻¹ = q⁻¹ := by
        calc c' * x * c'⁻¹ * x⁻¹ = x⁻¹ * (c' * x * c'⁻¹) := hc
          _ = q⁻¹ := by rw [hq]; group
      rw [e]; exact Subgroup.inv_mem _ hqZ
    refine c.mem_pCoreOf_of_trivial S hc'H (fun y hy => (hboth y hy).2) (fun y hy => ?_)
    have hy' : b⁻¹ * y * b ∈ U₁ := mem_conjSub.mp (hbsw ▸ hy)
    have e : b * (b⁻¹ * y * b) * b⁻¹ = y := by group
    have := (hboth _ hy').1
    rwa [e] at this
  have hmem : ∀ d ∈ Ug, d * b ∈ Dg ∨ d ∈ Dg := by
    intro d hd
    rcases c.normalizer_or S (hUgH hd) with hin | hsw
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


omit [Finite G] in
theorem commutator_le_of_conjSub_eq {U₁ Ug : Subgroup G} (hin : ∀ b ∈ Ug, conjSub b U₁ = U₁) :
    ⁅Ug, U₁⁆ ≤ U₁ := by
  rw [Subgroup.commutator_le]
  intro b hb x hx
  have haN₁ : b ∈ Subgroup.normalizer (U₁ : Set G) := mem_normalizer_of_conjSub_eq (hin b hb)
  rw [commutatorElement_def]
  exact U₁.mul_mem ((Subgroup.mem_normalizer_iff.mp haN₁ x).mp hx) (U₁.inv_mem hx)

theorem FCtx.commutator_le_U₂ (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u) {Ug : Subgroup G}
    (hUgH : Ug ≤ mcOf T) (hin : ∀ b ∈ Ug, conjSub b U₁ = U₁) : ⁅Ug, U₂⁆ ≤ U₂ := by
  rw [Subgroup.commutator_le]
  intro b hb x hx
  have haN₂ : b ∈ Subgroup.normalizer (U₂ : Set G) :=
    mem_normalizer_of_conjSub_eq (c.conjSub_U₂ S (hUgH hb) (hin b hb))
  rw [commutatorElement_def]
  exact U₂.mul_mem ((Subgroup.mem_normalizer_iff.mp haN₂ x).mp hx) (U₂.inv_mem hx)

theorem FCtx.commutator_sup_le (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u) {Ug : Subgroup G}
    (hUgH : Ug ≤ mcOf T) :
    ⁅uOfL22 T M, Ug⁆ ⊔ Zz ≤ (Zz ⊔ ⁅Ug, U₁⁆) ⊔ (Zz ⊔ ⁅Ug, U₂⁆) := by
  classical
  have hcommU : ∀ a ∈ uOfL22 T M, ∀ b ∈ uOfL22 T M, a * b = b * a := fun a ha b hb =>
    S.comm_of_mem_conjClosure ha hb
  refine sup_le ?_ (le_sup_left.trans le_sup_left)
  rw [Subgroup.commutator_le]
  intro x hx b hb
  have hbH : b ∈ mcOf T := hUgH hb
  have haNU : b ∈ Subgroup.normalizer (uOfL22 T M : Set G) := le_normalizer_conjClosure _ _ hbH
  have haEU : ∀ a ∈ uOfL22 T M, b * a * b⁻¹ ∈ uOfL22 T M := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp haNU a).mp ha
  have e : ⁅x, b⁆ = ⁅b, x⁆⁻¹ := by rw [commutatorElement_def, commutatorElement_def]; group
  rw [e]
  refine Subgroup.inv_mem _ ?_
  obtain ⟨y, hy, r₂, hr₂, d, hd, rfl⟩ := c.exists_decomp3 S hx
  have hyU := c.hU₁U hy
  have hr₂U := c.hU₂U hr₂
  have hdU := cuOf_le T M hd
  have hr₂dU : r₂ * d ∈ uOfL22 T M := (uOfL22 T M).mul_mem hr₂U hdU
  rw [commutatorElement_def, comm_mul_of_abelian hcommU haEU hyU hr₂dU,
    comm_mul_of_abelian hcommU haEU hr₂U hdU]
  have f1 : b * y * b⁻¹ * y⁻¹ ∈ (Zz ⊔ ⁅Ug, U₁⁆) ⊔ (Zz ⊔ ⁅Ug, U₂⁆) :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (by
      have := Subgroup.commutator_mem_commutator hb hy
      simpa [commutatorElement_def] using this))
  have f2 : b * r₂ * b⁻¹ * r₂⁻¹ ∈ (Zz ⊔ ⁅Ug, U₁⁆) ⊔ (Zz ⊔ ⁅Ug, U₂⁆) :=
    Subgroup.mem_sup_right (Subgroup.mem_sup_right (by
      have := Subgroup.commutator_mem_commutator hb hr₂
      simpa [commutatorElement_def] using this))
  have f3 : b * d * b⁻¹ * d⁻¹ ∈ (Zz ⊔ ⁅Ug, U₁⁆) ⊔ (Zz ⊔ ⁅Ug, U₂⁆) := by
    refine Subgroup.mem_sup_left (Subgroup.mem_sup_left ?_)
    have h1 := (mem_cuOf.mp hd).2.2 b hbH
    have e3 : b * d * b⁻¹ * d⁻¹ = (d * b * d⁻¹ * b⁻¹)⁻¹ := by group
    rw [e3]; exact Subgroup.inv_mem _ h1
  exact Subgroup.mul_mem _ f1 (Subgroup.mul_mem _ f2 f3)

end AllInner

section Count

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem card_contra_of_decomp {J₁ J₂ J₁' J₂' T S Z A : Subgroup Ω}
    (hcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hJ₁T : J₁ ≤ T) (hJ₂T : J₂ ≤ T) (hJ₁'S : J₁' ≤ S) (hJ₂'S : J₂' ≤ S) (hST : S ≤ T)
    (hT : J₁ ⊔ J₂ = T) (hS : J₁' ⊔ J₂' = S) (hZ : J₁ ⊓ J₂ = Z) (hA : J₁' ⊓ J₂' = A)
    (hZc : Nat.card Z = 2) (hAc : Nat.card A = 2) (hTS : Nat.card T ≤ 2 * Nat.card S)
    (h12' : J₁ ⊓ J₂' = ⊥) (h21' : J₂ ⊓ J₁' = ⊥) : False := by
  have c1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute J₁ J₂
    (fun x hx y hy => hcomm x (hJ₁T hx) y (hJ₂T hy))).1
  rw [hT, hZ, hZc] at c1
  have c2 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute J₁' J₂'
    (fun x hx y hy => hcomm x (hST (hJ₁'S hx)) y (hST (hJ₂'S hy)))).1
  rw [hS, hA, hAc] at c2
  have c3 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute J₁ J₂'
    (fun x hx y hy => hcomm x (hJ₁T hx) y (hST (hJ₂'S hy)))).1
  rw [h12', Subgroup.card_bot, mul_one] at c3
  have c4 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute J₂ J₁'
    (fun x hx y hy => hcomm x (hJ₂T hx) y (hST (hJ₁'S hy)))).1
  rw [h21', Subgroup.card_bot, mul_one] at c4
  have d3 : Nat.card ↥(J₁ ⊔ J₂') ≤ Nat.card T :=
    Subgroup.card_le_of_le (sup_le hJ₁T (hJ₂'S.trans hST))
  have d4 : Nat.card ↥(J₂ ⊔ J₁') ≤ Nat.card T :=
    Subgroup.card_le_of_le (sup_le hJ₂T (hJ₁'S.trans hST))
  rw [c3] at d3
  rw [c4] at d4
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have hSpos : 0 < Nat.card S := Nat.card_pos
  have h5 : (Nat.card J₁ * Nat.card J₂') * (Nat.card J₂ * Nat.card J₁') ≤ Nat.card T * Nat.card T :=
    Nat.mul_le_mul d3 d4
  have h6 : (Nat.card J₁ * Nat.card J₂) * (Nat.card J₁' * Nat.card J₂') ≤ Nat.card T * Nat.card T := by
    calc (Nat.card J₁ * Nat.card J₂) * (Nat.card J₁' * Nat.card J₂')
        = (Nat.card J₁ * Nat.card J₂') * (Nat.card J₂ * Nat.card J₁') := by ring
      _ ≤ _ := h5
  rw [← c1, ← c2] at h6
  nlinarith

end Count

section Cover

variable {G : Type} [Group G] [Finite G]

theorem relIndex_le_card_of_cover {N U : Subgroup G} (R : Finset G) (hRU : ∀ r ∈ R, r ∈ U)
    (hcov : ∀ v ∈ U, ∃ r ∈ R, v * r ∈ N) : N.relIndex U ≤ R.card := by
  classical
  let f : R → ↥U ⧸ N.subgroupOf U := fun r => QuotientGroup.mk ⟨r.1, hRU r.1 r.2⟩
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨r, hr, hrw⟩ := hcov ((w : G)⁻¹) (U.inv_mem w.2)
    refine ⟨⟨r, hr⟩, ?_⟩
    show (QuotientGroup.mk ⟨r, hRU r hr⟩ : ↥U ⧸ N.subgroupOf U) = QuotientGroup.mk w
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have := N.inv_mem hrw
    simpa [mul_inv_rev] using this
  have h1 := Nat.card_le_card_of_surjective f hf
  have h2 : Nat.card ↥R = R.card := by simp
  rw [h2] at h1
  exact h1

theorem exists_rep_of_relIndex_two {D V U : Subgroup G} (hVU : V ≤ U) (h2 : D.relIndex U = 2) :
    ∃ b ∈ V, ∀ d ∈ V, d * b ∈ D ⊓ V ∨ d ∈ D ⊓ V := by
  have h1 : (D ⊓ V).relIndex V = D.relIndex V := Subgroup.inf_relIndex_right D V
  have h3 : D.relIndex V ≤ 2 := by
    have := Subgroup.relIndex_le_of_le_right (H := D) hVU (by rw [h2]; norm_num)
    rwa [h2] at this
  have h4 : D.relIndex V ≠ 0 := relIndex_ne_zero_fin _ _
  have hdvd : (D ⊓ V).relIndex V ∣ 2 := by
    rw [h1]
    have : D.relIndex V = 1 ∨ D.relIndex V = 2 := by omega
    rcases this with h | h <;> rw [h]
    · exact one_dvd _
  exact Subgroup.relIndex_dvd_two_iff.mp hdvd

end Cover

section RankTwo

variable {G : Type} [Group G] [Finite G] {T M K U₁ U₂ : Subgroup G} {s u : G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem FCtx.inner_of_rank_two (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u)
    {γ γ' : F8.Geom T (yOfL22 T M) (mcOf T)} {g : ↥(((yOfL22 T M) ⊔ T) ⊔ mcOf T)}
    (hsetup : F8Setup T (VZ T M) (yOfL22 T M) (mcOf T) γ γ' g)
    (h1 : mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G)) (F8.Dγ (VZ T M) Zz (mcOf T) (g : G)) = 2)
    (hle : mIdx (uOfL22 T M) (F8.DH (VZ T M) Zz (mcOf T) (g : G)) ≤ 2) :
    ∀ b ∈ F8.Uγ (VZ T M) (mcOf T) (g : G), conjSub b U₁ = U₁ := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hF98 := (S.lemma_14_5_14 (S.isHz_iff.mpr hG)).2
  have hUgH : F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ mcOf T := hF98.Uγ_le_H hsetup
  have hUgab : IsElemAbelian 2 (F8.Uγ (VZ T M) (mcOf T) (g : G)) := hF98.isElemAbelian_Uγ
  have hUgp : IsPGroup 2 (F8.Uγ (VZ T M) (mcOf T) (g : G)) := isPGroup_of_isElemAbelian hUgab
  have hDgeq : F8.Dγ (VZ T M) Zz (mcOf T) (g : G) =
      F8.Uγ (VZ T M) (mcOf T) (g : G) ⊓ pCoreOf 2 (mcOf T) := hF98.Dγ_eq_inf_pCoreOf hsetup
  have hpos : 0 < mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G)) (F8.Dγ (VZ T M) Zz (mcOf T) (g : G)) := by
    rw [h1]; norm_num
  have hle' : mIdx (uOfL22 T M) (F8.DH (VZ T M) Zz (mcOf T) (g : G)) ≤
      mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G)) (F8.Dγ (VZ T M) Zz (mcOf T) (g : G)) := by
    rw [h1]; exact hle
  have hQ := (hF98.F916_2_aux hsetup hpos hle').1
  have hrel : ¬ (F8.Dγ (VZ T M) Zz (mcOf T) (g : G)).relIndex
      (F8.Uγ (VZ T M) (mcOf T) (g : G)) ∣ 2 := by
    rw [HypF98.relIndex_eq_two_pow_mIdx hUgp, h1]; norm_num
  exact c.all_inner S hUgH hUgab hDgeq hrel hQ.2.2.2.1

theorem A₁_le_commutator_strict (S : Setting146 G T M) {g : ↥(((yOfL22 T M) ⊔ T) ⊔ mcOf T)}
    (hle : mIdx (uOfL22 T M) (F8.DH (VZ T M) Zz (mcOf T) (g : G)) ≤
      mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G)) (F8.Dγ (VZ T M) Zz (mcOf T) (g : G)))
    (hlt : mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G)) (F8.Dγ (VZ T M) Zz (mcOf T) (g : G)) <
      mIdx (uOfL22 T M) (centralizerMod Zz (uOfL22 T M) (F8.Uγ (VZ T M) (mcOf T) (g : G)))) :
    F8.A₁ Zz (g : G) ≤ ⁅uOfL22 T M, F8.Uγ (VZ T M) (mcOf T) (g : G)⁆ := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hF98 := (S.lemma_14_5_14 (S.isHz_iff.mpr hG)).2
  have hUab : IsElemAbelian 2 (uOfL22 T M) := S.lemma_14_5_15_two hG
  have hUp : IsPGroup 2 (uOfL22 T M) := isPGroup_of_isElemAbelian hUab
  have hDHle : ⁅F8.DH (VZ T M) Zz (mcOf T) (g : G), F8.Uγ (VZ T M) (mcOf T) (g : G)⁆ ≤
      F8.A₁ Zz (g : G) :=
    Subgroup.commutator_le.mpr fun d hd x hx => hd.2.2 x hx
  have hDHU : F8.DH (VZ T M) Zz (mcOf T) (g : G) ≤ uOfL22 T M := centralizerMod_le_left _ _ _
  have hne : ⁅F8.DH (VZ T M) Zz (mcOf T) (g : G), F8.Uγ (VZ T M) (mcOf T) (g : G)⁆ ≠ ⊥ := by
    intro hbot
    have hDC : F8.DH (VZ T M) Zz (mcOf T) (g : G) ≤
        centralizerMod Zz (uOfL22 T M) (F8.Uγ (VZ T M) (mcOf T) (g : G)) := by
      intro d hd
      refine ⟨hDHU hd, S.conjClosure_le_normalizer_Z hG (hDHU hd), fun b hb => ?_⟩
      have h1 : ⁅d, b⁆ ∈ ⁅F8.DH (VZ T M) Zz (mcOf T) (g : G),
          F8.Uγ (VZ T M) (mcOf T) (g : G)⁆ := Subgroup.commutator_mem_commutator hd hb
      rw [hbot, Subgroup.mem_bot] at h1
      rw [commutatorElement_def] at h1
      rw [h1]
      exact Subgroup.one_mem _
    have hdvd := Subgroup.relIndex_dvd_of_le_left (uOfL22 T M) hDC
    rw [HypF98.relIndex_eq_two_pow_mIdx hUp, HypF98.relIndex_eq_two_pow_mIdx hUp] at hdvd
    have hle2 := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdvd
    omega
  have hcardA := hF98.card_A₁ (g := g)
  have hcardge : Nat.card (F8.A₁ Zz (g : G)) ≤
      Nat.card ↥⁅F8.DH (VZ T M) Zz (mcOf T) (g : G), F8.Uγ (VZ T M) (mcOf T) (g : G)⁆ := by
    rw [hcardA]
    have := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
    omega
  have heq := Subgroup.eq_of_le_of_card_ge hDHle hcardge
  rw [← heq]
  exact Subgroup.commutator_mono hDHU le_rfl

end RankTwo

end CFSG.Quasithin
