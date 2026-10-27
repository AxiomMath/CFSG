module

public import CFSG.RankThree.GF2n.Smith81.S81JBasis

public section

namespace CFSG.RankThree.GF2n.Smith81.S81J

open CFSG.RankThree.GF2n.Smith81.A5Cube Matrix Module

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def I1 : Finset (Fin 6) := {1, 2, 3}

private theorem rkA_ne_of_mem : ∀ p : Fin 6, p ∈ ({1, 2, 4, 5} : Finset (Fin 6)) →
    (0 : Fin 6) ≠ p ∧ (3 : Fin 6) ≠ p := by
  decide

private theorem rkA_fin (J : Finset (Fin 6)) (hJ : J.card = 3) (hJ0 : J ≠ I0) (hJ1 : J ≠ I1) :
    ∃ p ∈ ({1, 2, 4, 5} : Finset (Fin 6)), ∃ r ∈ ({1, 2, 4, 5} : Finset (Fin 6)),
      (if p ∈ J then (1 : ℤ) else 0) - (if p ∈ I1 then (1 : ℤ) else 0) ≠
        (if r ∈ J then (1 : ℤ) else 0) - (if r ∈ I1 then (1 : ℤ) else 0) := by
  revert J
  decide

private theorem rkA_prod_cOn {p r : Fin 6} (hpr : p ≠ r) (c : Kˣ) (S : Finset (Fin 6)) :
    ∏ i ∈ S, cOn p r c i =
      c ^ ((if p ∈ S then (1 : ℤ) else 0) - (if r ∈ S then (1 : ℤ) else 0)) := by
  have key : ∀ i, cOn p r c i = (if i = p then c else 1) * (if i = r then c⁻¹ else 1) := by
    intro i
    by_cases hip : i = p
    · subst hip
      simp [cOn, hpr]
    · by_cases hir : i = r
      · subst hir
        simp [cOn, hip]
      · simp [cOn, hip, hir]
  rw [Finset.prod_congr rfl (fun i _ => key i), Finset.prod_mul_distrib, Finset.prod_ite_eq',
    Finset.prod_ite_eq']
  by_cases hp : p ∈ S <;> by_cases hr : r ∈ S <;> simp [hp, hr, _root_.zpow_neg, _root_.zpow_one]

private theorem rkA_zpow_eq_one [CharP K 2] {x : Kˣ} {n : ℤ}
    (hn : n = 1 ∨ n = -1 ∨ n = 2 ∨ n = -2) (h : x ^ n = 1) : x = 1 := by
  have hsq : x ^ (2 : ℤ) = 1 → x = 1 := by
    intro hx
    rw [_root_.zpow_two] at hx
    have hK : (x : K) * (x : K) = 1 := by
      have := congrArg Units.val hx
      simpa using this
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have h3 : ((x : K) - 1) * ((x : K) - 1) = 0 := by
      linear_combination hK + (1 - (x : K)) * h2
    exact Units.ext (sub_eq_zero.mp (mul_self_eq_zero.mp h3))
  rcases hn with rfl | rfl | rfl | rfl
  · simpa using h
  · rw [_root_.zpow_neg_one, inv_eq_one] at h
    exact h
  · exact hsq h
  · rw [_root_.zpow_neg, inv_eq_one] at h
    exact hsq h

private theorem rkA_zpow_sub_eq_one {x : Kˣ} {m n : ℤ} (h : x ^ m = x ^ n) :
    x ^ (m - n) = 1 := by
  rw [_root_.zpow_sub, h, mul_inv_cancel]

theorem Tprime_sep [CharP K 2] {ξ : Kˣ →* Kˣ} (hξ : ∃ c, ξ c ≠ 1) {J : Finset (Fin 6)}
    (hJ : J.card = 3) (hJ0 : J ≠ I0) (hJ1 : J ≠ I1) :
    ∃ d : Fin 6 → Kˣ, d 0 = d 3 ∧ ∏ i, d i = 1 ∧ ξ (∏ i ∈ J, d i) ≠ ξ (∏ i ∈ I1, d i) := by
  obtain ⟨c, hc⟩ := hξ
  obtain ⟨p, hp, r, hr, hne⟩ := rkA_fin J hJ hJ0 hJ1
  have hpr : p ≠ r := fun h => hne (by rw [h])
  refine ⟨cOn p r c, ?_, ?_, ?_⟩
  · obtain ⟨hp0, hp3⟩ := rkA_ne_of_mem p hp
    obtain ⟨hr0, hr3⟩ := rkA_ne_of_mem r hr
    simp [cOn, hp0, hp3, hr0, hr3]
  · rw [rkA_prod_cOn hpr c Finset.univ]
    simp
  · rw [rkA_prod_cOn hpr c J, rkA_prod_cOn hpr c I1]
    intro h
    simp only [map_zpow] at h
    exact hc (rkA_zpow_eq_one (by split_ifs at hne ⊢ <;> omega) (rkA_zpow_sub_eq_one h))

structure Setup [CharP K 2] (A : SLAct K V) (v₀ : V) (ξ : Kˣ →* Kˣ) : Prop where
  hV : finrank K V = 20
  h0 : finrank K (A.Fix (Wc K I0)) = 1
  hv₀ : v₀ ∈ A.Fix (Wc K I0)
  hv0 : v₀ ≠ 0
  hξ : ∀ c : Kˣ, ∀ v ∈ A.Fix (Wc K I0), A.act (dg (cOn 0 3 c)) v = ((ξ c : Kˣ) : K) • v
  hξ1 : ∃ c, ξ c ≠ 1

namespace SLAct

variable [CharP K 2] (A : SLAct K V)

@[expose] noncomputable def X (t : K) : V →ₗ[K] V := A.act (transvGL K 0 3 (by decide) t)

@[expose] noncomputable def Y (t : K) : V →ₗ[K] V := A.act (transvGL K 3 0 (by decide) t)

theorem X_add (s t : K) : A.X (s + t) = A.X s * A.X t := by
  have h03 : (0 : Fin 6) ≠ 3 := by decide
  show A.act (transvGL K 0 3 h03 (s + t)) =
    A.act (transvGL K 0 3 h03 s) * A.act (transvGL K 0 3 h03 t)
  rw [← tr_mul_tr h03 s t]
  exact A.act_mul _ _ (det_tr _ _) (det_tr _ _)

theorem X_zero : A.X 0 = 1 := by
  have h03 : (0 : Fin 6) ≠ 3 := by decide
  show A.act (transvGL K 0 3 h03 0) = 1
  rw [tr_zero h03, A.act_one]

theorem X_X_self (t : K) (v : V) : A.X t (A.X t v) = v := by
  have h : A.X t * A.X t = 1 := by
    rw [← A.X_add, CharTwo.add_self_eq_zero, A.X_zero]
  calc A.X t (A.X t v) = (A.X t * A.X t) v := rfl
    _ = v := by rw [h, Module.End.one_apply]

theorem X_fix_I0 {v : V} (hv : v ∈ A.Fix (Wc K I0)) (t : K) : A.X t v = v := by
  have h03 : (0 : Fin 6) ≠ 3 := by decide
  have h0 : (0 : Fin 6) ∈ I0 := by decide
  have h3 : (3 : Fin 6) ∉ I0 := by decide
  exact (A.mem_Fix.1 hv) _ (tr_mem_UnipGL h03 t h0 h3)

theorem dg_X (d : Fin 6 → Kˣ) (hd : ∏ i, d i = 1) (t : K) (v : V) :
    A.act (dg d) (A.X t v) = A.X ((d 0 : K) * ((d 3 : K))⁻¹ * t) (A.act (dg d) v) := by
  have h03 : (0 : Fin 6) ≠ 3 := by decide
  have hdet : ((dg d : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
    rw [det_dg, ← Units.coe_prod, hd, Units.val_one]
  have hcomm : dg d * transvGL K 0 3 h03 t =
      transvGL K 0 3 h03 ((d 0 : K) * ((d 3 : K))⁻¹ * t) * dg d :=
    mul_inv_eq_iff_eq_mul.1 (dg_conj_tr d h03 t)
  have e1 : A.act (dg d * transvGL K 0 3 h03 t) =
      A.act (dg d) * A.act (transvGL K 0 3 h03 t) :=
    A.act_mul _ _ hdet (det_tr _ _)
  have e2 : A.act (transvGL K 0 3 h03 ((d 0 : K) * ((d 3 : K))⁻¹ * t) * dg d) =
      A.act (transvGL K 0 3 h03 ((d 0 : K) * ((d 3 : K))⁻¹ * t)) * A.act (dg d) :=
    A.act_mul _ _ (det_tr _ _) hdet
  calc A.act (dg d) (A.X t v) = (A.act (dg d) * A.act (transvGL K 0 3 h03 t)) v := rfl
    _ = A.act (dg d * transvGL K 0 3 h03 t) v := by rw [e1]
    _ = A.act (transvGL K 0 3 h03 ((d 0 : K) * ((d 3 : K))⁻¹ * t) * dg d) v := by rw [hcomm]
    _ = (A.act (transvGL K 0 3 h03 ((d 0 : K) * ((d 3 : K))⁻¹ * t)) * A.act (dg d)) v := by
        rw [e2]
    _ = A.X ((d 0 : K) * ((d 3 : K))⁻¹ * t) (A.act (dg d) v) := rfl

theorem vI1_eq {v₀ : V} {ξ : Kˣ →* Kˣ} (S : Setup A v₀ ξ) :
    A.vI v₀ I1 = A.act (pm K (Equiv.swap 0 3)) v₀ := by
  have hI1eq : I1 = I0.image (Equiv.swap 0 3) := by decide
  rw [hI1eq]
  exact (A.vI_eq S.h0 S.hv₀ (Equiv.swap 0 3)).symm

theorem linearIndependent_v0_v1 {v₀ : V} {ξ : Kˣ →* Kˣ} (S : Setup A v₀ ξ) :
    LinearIndependent K ![v₀, A.act (pm K (Equiv.swap 0 3)) v₀] := by
  have hI0 : I0.card = 3 := by decide
  have hI1 : I1.card = 3 := by decide
  have hne : I0 ≠ I1 := by decide
  have hf : Function.Injective (![⟨I0, hI0⟩, ⟨I1, hI1⟩] : Fin 2 → J3) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | rfl
      | exact absurd (congrArg Subtype.val hij) hne
      | exact absurd (congrArg Subtype.val hij) hne.symm
  have h := (A.linearIndependent_vI S.h0 S.hv₀ S.hv0 S.hξ S.hξ1).comp _ hf
  have heq : ((fun I : J3 => A.vI v₀ I.1) ∘ (![⟨I0, hI0⟩, ⟨I1, hI1⟩] : Fin 2 → J3)) =
      ![v₀, A.act (pm K (Equiv.swap 0 3)) v₀] := by
    funext i
    fin_cases i
    · simp [A.vI_I0 S.h0 S.hv₀]
    · simp [A.vI1_eq S]
  rw [heq] at h
  exact h

theorem rkB1_repr_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V)
    (c : ι → K) (I : ι) :
    b.repr (∑ J, c J • b J) I = c I := by
  simp [Module.Basis.repr_self, Finsupp.single_apply]

theorem X_v1_mem_span {v₀ : V} {ξ : Kˣ →* Kˣ} (S : Setup A v₀ ξ) (t : K) :
    A.X t (A.act (pm K (Equiv.swap 0 3)) v₀) ∈
      Submodule.span K {v₀, A.act (pm K (Equiv.swap 0 3)) v₀} := by
  obtain ⟨v₁, hv₁⟩ : ∃ v₁ : V, v₁ = A.act (pm K (Equiv.swap 0 3)) v₀ := ⟨_, rfl⟩
  rw [← hv₁]
  have hI1 : A.vI v₀ I1 = v₁ := (A.vI1_eq S).trans hv₁.symm
  have hI1card : I1.card = 3 := by decide
  have hI0card : I0.card = 3 := by decide
  have hli : LinearIndependent K (fun I : J3 => A.vI v₀ I.1) :=
    A.linearIndependent_vI S.h0 S.hv₀ S.hv0 S.hξ S.hξ1
  have hsp : Submodule.span K (Set.range (fun I : J3 => A.vI v₀ I.1)) = ⊤ :=
    A.span_vI S.hV S.h0 S.hv₀ S.hv0 S.hξ S.hξ1
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis J3 K V, ∀ I : J3, b I = A.vI v₀ I.1 :=
    ⟨Module.Basis.mk hli hsp.ge, fun I => Module.Basis.mk_apply hli hsp.ge I⟩
  have hdiag : ∀ d : Fin 6 → Kˣ, ∏ i, d i = 1 → ∀ J : J3,
      A.act (dg d) (b J) = ((ξ (∏ i ∈ J.1, d i) : Kˣ) : K) • b J := by
    intro d hd J
    rw [hb J]
    exact A.act_dg_vI S.h0 S.hv₀ S.hξ J.2 d hd
  have hcoord : ∀ d : Fin 6 → Kˣ, ∏ i, d i = 1 → ∀ (x : V) (J : J3),
      b.repr (A.act (dg d) x) J = b.repr x J * ((ξ (∏ i ∈ J.1, d i) : Kˣ) : K) := by
    intro d hd x J
    have hx : A.act (dg d) x =
        ∑ J' : J3, (b.repr x J' * ((ξ (∏ i ∈ J'.1, d i) : Kˣ) : K)) • b J' := by
      conv_lhs => rw [← b.sum_repr x]
      simp only [map_sum, map_smul, hdiag d hd, smul_smul]
    rw [hx]
    exact rkB1_repr_sum b _ J
  obtain ⟨w, hw⟩ : ∃ w : V, w = A.X t v₁ := ⟨_, rfl⟩
  rw [← hw]
  have hw_eig : ∀ d : Fin 6 → Kˣ, ∏ i, d i = 1 → d 0 = d 3 →
      A.act (dg d) w = ((ξ (∏ i ∈ I1, d i) : Kˣ) : K) • w := by
    intro d hd hd03
    have hscal : ((d 0 : Kˣ) : K) * ((d 3 : Kˣ) : K)⁻¹ * t = t := by
      rw [hd03, mul_assoc]
      exact mul_inv_cancel_left₀ (Units.ne_zero _) t
    have hv1 : A.act (dg d) v₁ = ((ξ (∏ i ∈ I1, d i) : Kˣ) : K) • v₁ := by
      rw [← hI1]
      exact A.act_dg_vI S.h0 S.hv₀ S.hξ hI1card d hd
    rw [hw, A.dg_X d hd t v₁, hscal, hv1, map_smul]
  have hzero : ∀ J : J3, J.1 ≠ I0 → J.1 ≠ I1 → b.repr w J = 0 := by
    intro J hJ0 hJ1
    obtain ⟨d, hd03, hd, hne⟩ := Tprime_sep S.hξ1 J.2 hJ0 hJ1
    have h1 := hcoord d hd w J
    rw [hw_eig d hd hd03, map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
    have hne' : ((ξ (∏ i ∈ J.1, d i) : Kˣ) : K) ≠ ((ξ (∏ i ∈ I1, d i) : Kˣ) : K) :=
      fun h => hne (Units.ext h)
    have hmul : (((ξ (∏ i ∈ I1, d i) : Kˣ) : K) - ((ξ (∏ i ∈ J.1, d i) : Kˣ) : K)) *
        b.repr w J = 0 := by
      linear_combination h1
    rcases mul_eq_zero.mp hmul with h | h
    · exact absurd (sub_eq_zero.mp h).symm hne'
    · exact h
  have hIne : I0 ≠ I1 := by decide
  have hne01 : (⟨I0, hI0card⟩ : J3) ≠ ⟨I1, hI1card⟩ := fun h => hIne (congrArg Subtype.val h)
  have hsum : w = b.repr w ⟨I0, hI0card⟩ • v₀ + b.repr w ⟨I1, hI1card⟩ • v₁ := by
    have h0' : b ⟨I0, hI0card⟩ = v₀ := by
      rw [hb]
      exact A.vI_I0 S.h0 S.hv₀
    have h1' : b ⟨I1, hI1card⟩ = v₁ := by
      rw [hb]
      exact hI1
    conv_lhs => rw [← b.sum_repr w]
    rw [Fintype.sum_eq_add _ _ hne01]
    · simp only [h0', h1']
    · rintro J ⟨hJ0, hJ1⟩
      rw [hzero J (fun h => hJ0 (Subtype.ext h)) (fun h => hJ1 (Subtype.ext h)), zero_smul]
  rw [Submodule.mem_span_pair]
  exact ⟨_, _, hsum.symm⟩

theorem exists_beta {v₀ : V} {ξ : Kˣ →* Kˣ} (S : Setup A v₀ ξ) :
    ∃ β : K → K, ∀ t, A.X t (A.act (pm K (Equiv.swap 0 3)) v₀) =
      A.act (pm K (Equiv.swap 0 3)) v₀ + β t • v₀ := by
  obtain ⟨v₁, hv₁⟩ : ∃ v₁ : V, v₁ = A.act (pm K (Equiv.swap 0 3)) v₀ := ⟨_, rfl⟩
  have hli : LinearIndependent K ![v₀, v₁] := by
    rw [hv₁]
    exact A.linearIndependent_v0_v1 S
  have hmem : ∀ t, ∃ a b : K, a • v₀ + b • v₁ = A.X t v₁ := fun t => by
    have h := A.X_v1_mem_span S t
    rw [← hv₁] at h
    exact Submodule.mem_span_pair.mp h
  choose a b hab using hmem
  have hb : ∀ t, b t = 1 := by
    intro t
    have e0 : A.X t (A.X t v₁) = v₁ := A.X_X_self t v₁
    have h' : A.X t (A.X t v₁) = A.X t (a t • v₀ + b t • v₁) := by
      rw [hab t]
    have e1 : A.X t (A.X t v₁) = a t • v₀ + b t • (a t • v₀ + b t • v₁) := by
      rw [h', map_add, map_smul, map_smul, A.X_fix_I0 S.hv₀ t, hab t]
    have hE : a t • v₀ + b t • (a t • v₀ + b t • v₁) = v₁ := e1.symm.trans e0
    have hz : (a t + b t * a t) • v₀ + (b t * b t - 1) • v₁ = 0 := by
      have expand : (a t + b t * a t) • v₀ + (b t * b t - 1) • v₁ =
          (a t • v₀ + b t • (a t • v₀ + b t • v₁)) - v₁ := by
        module
      rw [expand, hE, sub_self]
    have hbb : b t * b t - 1 = 0 := (LinearIndependent.pair_iff.mp hli _ _ hz).2
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have hsq : (b t - 1) * (b t - 1) = 0 := by
      linear_combination hbb + (1 - b t) * h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp hsq)
  refine ⟨a, fun t => ?_⟩
  rw [← hv₁, ← hab t, hb t, one_smul, add_comm]

theorem beta_add {v₀ : V} {ξ : Kˣ →* Kˣ} (S : Setup A v₀ ξ) {β : K → K}
    (hβ : ∀ t, A.X t (A.act (pm K (Equiv.swap 0 3)) v₀) =
      A.act (pm K (Equiv.swap 0 3)) v₀ + β t • v₀) (s t : K) : β (s + t) = β s + β t := by
  have h1 := hβ (s + t)
  rw [A.X_add, Module.End.mul_apply, hβ t, map_add, map_smul, hβ s, A.X_fix_I0 S.hv₀ s] at h1
  rw [add_assoc] at h1
  have h2 := add_left_cancel h1
  have h4 : (β s + β t - β (s + t)) • v₀ = 0 := by
    rw [sub_smul, add_smul, h2, sub_self]
  rcases smul_eq_zero.1 h4 with h | h
  · exact (sub_eq_zero.1 h).symm
  · exact absurd h S.hv0

theorem beta_scale {v₀ : V} {ξ : Kˣ →* Kˣ} (S : Setup A v₀ ξ) {β : K → K}
    (hβ : ∀ t, A.X t (A.act (pm K (Equiv.swap 0 3)) v₀) =
      A.act (pm K (Equiv.swap 0 3)) v₀ + β t • v₀) (c : Kˣ) (t : K) :
    β (((c : Kˣ) : K) ^ 2 * t) = ((ξ c : Kˣ) : K) ^ 2 * β t := by
  have hI1card : I1.card = 3 := by decide
  have hd : ∏ i, cOn 0 3 c i = 1 := by
    simp [cOn, Fin.prod_univ_six]
  have hd0 : ((cOn 0 3 c 0 : Kˣ) : K) * ((cOn 0 3 c 3 : Kˣ) : K)⁻¹ * t =
      ((c : Kˣ) : K) ^ 2 * t := by
    have h0 : cOn 0 3 c 0 = c := by simp [cOn]
    have h3 : cOn 0 3 c 3 = c⁻¹ := by simp [cOn]
    rw [h0, h3, Units.val_inv_eq_inv_val, inv_inv, sq]
  have hI1prod : ∏ i ∈ I1, cOn 0 3 c i = c⁻¹ := by
    simp [I1, cOn, Finset.prod_insert]
  have hdv0 : A.act (dg (cOn 0 3 c)) v₀ = ((ξ c : Kˣ) : K) • v₀ := S.hξ c v₀ S.hv₀
  have hdv1 : A.act (dg (cOn 0 3 c)) (A.act (pm K (Equiv.swap 0 3)) v₀) =
      ((ξ c⁻¹ : Kˣ) : K) • A.act (pm K (Equiv.swap 0 3)) v₀ := by
    have h := A.act_dg_vI S.h0 S.hv₀ S.hξ hI1card (cOn 0 3 c) hd
    rw [A.vI1_eq S, hI1prod] at h
    exact h
  have hL : A.act (dg (cOn 0 3 c)) (A.X t (A.act (pm K (Equiv.swap 0 3)) v₀)) =
      ((ξ c⁻¹ : Kˣ) : K) • A.act (pm K (Equiv.swap 0 3)) v₀ +
        (β t * ((ξ c : Kˣ) : K)) • v₀ := by
    rw [hβ t, map_add, map_smul, hdv1, hdv0, smul_smul]
  have hR : A.act (dg (cOn 0 3 c)) (A.X t (A.act (pm K (Equiv.swap 0 3)) v₀)) =
      ((ξ c⁻¹ : Kˣ) : K) • (A.act (pm K (Equiv.swap 0 3)) v₀ +
        β (((c : Kˣ) : K) ^ 2 * t) • v₀) := by
    rw [A.dg_X (cOn 0 3 c) hd t, hd0, hdv1, map_smul, hβ]
  have hEq : (β t * ((ξ c : Kˣ) : K)) • v₀ =
      (((ξ c⁻¹ : Kˣ) : K) * β (((c : Kˣ) : K) ^ 2 * t)) • v₀ := by
    have h := hL.symm.trans hR
    rw [smul_add, smul_smul] at h
    exact add_left_cancel h
  have hscal : β t * ((ξ c : Kˣ) : K) = ((ξ c⁻¹ : Kˣ) : K) * β (((c : Kˣ) : K) ^ 2 * t) := by
    have h5 : (β t * ((ξ c : Kˣ) : K) - ((ξ c⁻¹ : Kˣ) : K) * β (((c : Kˣ) : K) ^ 2 * t)) • v₀ =
        0 := by
      rw [sub_smul, hEq, sub_self]
    rcases smul_eq_zero.1 h5 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h S.hv0
  have hinv : ((ξ c⁻¹ : Kˣ) : K) * ((ξ c : Kˣ) : K) = 1 := by
    rw [map_inv]
    exact Units.inv_mul _
  linear_combination (-((ξ c : Kˣ) : K)) * hscal - β (((c : Kˣ) : K) ^ 2 * t) * hinv

private theorem rkB2_unip_sq [CharP K 2] {W : Submodule K (Fin 6 → K)} {g : GL (Fin 6) K}
    (hg : g ∈ UnipGL K W) : g * g = 1 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_one]
  refine Matrix.ext_iff_mulVec.2 fun v => ?_
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  obtain ⟨-, h1, h2⟩ := mem_UnipGL_iff.1 hg
  have hn : (g : Matrix (Fin 6) (Fin 6) K).mulVec v - v ∈ W := h1 v
  have hfix := h2 _ hn
  rw [Matrix.mulVec_sub] at hfix
  have hz : ∀ x : Fin 6 → K, x + x = 0 := fun x => by
    funext i
    exact CharTwo.add_self_eq_zero (x i)
  have h3 : (g : Matrix (Fin 6) (Fin 6) K).mulVec ((g : Matrix (Fin 6) (Fin 6) K).mulVec v) - v =
      0 := by
    have e : (g : Matrix (Fin 6) (Fin 6) K).mulVec ((g : Matrix (Fin 6) (Fin 6) K).mulVec v) - v =
        ((g : Matrix (Fin 6) (Fin 6) K).mulVec ((g : Matrix (Fin 6) (Fin 6) K).mulVec v) -
          (g : Matrix (Fin 6) (Fin 6) K).mulVec v) +
          ((g : Matrix (Fin 6) (Fin 6) K).mulVec v - v) := by
      abel
    rw [e, hfix, hz]
  exact sub_eq_zero.1 h3

theorem beta_ne_zero {v₀ : V} {ξ : Kˣ →* Kˣ} (S : Setup A v₀ ξ) {β : K → K}
    (hβ : ∀ t, A.X t (A.act (pm K (Equiv.swap 0 3)) v₀) =
      A.act (pm K (Equiv.swap 0 3)) v₀ + β t • v₀) : ∃ t, β t ≠ 0 := by
  by_contra hcon
  simp only [not_exists, ne_eq, not_not] at hcon
  have hI1card : I1.card = 3 := by decide
  have hX : ∀ t, A.X t (A.act (pm K (Equiv.swap 0 3)) v₀) =
      A.act (pm K (Equiv.swap 0 3)) v₀ := by
    intro t
    rw [hβ t, hcon t, zero_smul, add_zero]
  have hv1I1 : A.act (pm K (Equiv.swap 0 3)) v₀ ∈ A.Fix (Wc K I1) := by
    have h := A.vI_mem S.h0 S.hv₀ hI1card
    rwa [A.vI1_eq S] at h
  have hfix0 : A.act (pm K (Equiv.swap 0 3)) v₀ ∈ A.Fix (Wc K I0) := by
    refine A.mem_Fix.2 fun u hu => ?_
    obtain ⟨hu', hstab⟩ := UnipGL_I0_decomp hu
    obtain ⟨u', hu'def⟩ : ∃ u' : GL (Fin 6) K,
        u' = u * transvGL K 0 3 (by decide) ((u : Matrix (Fin 6) (Fin 6) K) 0 3) := ⟨_, rfl⟩
    rw [← hu'def] at hu' hstab
    have hstab' : ∀ w ∈ Wc K I1, (u' : Matrix (Fin 6) (Fin 6) K).mulVec w ∈ Wc K I1 := hstab
    have hdet' : (u' : Matrix (Fin 6) (Fin 6) K).det = 1 := (mem_UnipGL_iff.1 hu').1
    have hinv' : ∀ v ∈ A.Fix (Wc K I1), A.act u' v = v :=
      A.act_invol_fix hdet' (rkB2_unip_sq hu') hstab' (A.finrank_Fix_Wc S.h0 hI1card)
    obtain ⟨T', hT'def⟩ : ∃ T' : GL (Fin 6) K,
        T' = transvGL K 0 3 (by decide) (-((u : Matrix (Fin 6) (Fin 6) K) 0 3)) := ⟨_, rfl⟩
    have hu_eq : u = u' * T' := by
      rw [hu'def, hT'def, ← tr_inv, mul_inv_cancel_right]
    have hdetT' : (T' : Matrix (Fin 6) (Fin 6) K).det = 1 := by
      rw [hT'def]
      exact det_tr _ _
    have hT'v1 : A.act T' (A.act (pm K (Equiv.swap 0 3)) v₀) =
        A.act (pm K (Equiv.swap 0 3)) v₀ := by
      rw [hT'def]
      exact hX (-((u : Matrix (Fin 6) (Fin 6) K) 0 3))
    rw [hu_eq, A.act_mul u' T' hdet' hdetT', Module.End.mul_apply, hT'v1, hinv' _ hv1I1]
  have hv0ne : (⟨v₀, S.hv₀⟩ : A.Fix (Wc K I0)) ≠ 0 := by
    intro h
    exact S.hv0 (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hv0ne).1 S.h0 ⟨_, hfix0⟩
  have hc' : c • v₀ = A.act (pm K (Equiv.swap 0 3)) v₀ := congrArg Subtype.val hc
  have hdep : c • v₀ + (-1 : K) • A.act (pm K (Equiv.swap 0 3)) v₀ = 0 := by
    rw [hc', neg_one_smul, add_neg_cancel]
  have h := (LinearIndependent.pair_iff.1 (A.linearIndependent_v0_v1 S)) c (-1) hdep
  exact one_ne_zero (neg_eq_zero.1 h.2)

private theorem rkC_transv_congr {a b c d : Fin 6} (hab : a ≠ b) (hcd : c ≠ d) (t : K)
    (h1 : a = c) (h2 : b = d) : transvGL K a b hab t = transvGL K c d hcd t := by
  subst h1 h2
  rfl

private theorem rkC_det_mul {g h : GL (Fin 6) K}
    (hg : (g : Matrix (Fin 6) (Fin 6) K).det = 1) (hh : (h : Matrix (Fin 6) (Fin 6) K).det = 1) :
    ((g * h : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
  rw [Units.val_mul, Matrix.det_mul, hg, hh, one_mul]

theorem rank_one [Finite K] {v₀ : V} {ξ : Kˣ →* Kˣ} (S : Setup A v₀ ξ) :
    ∃ (g : K ≃+* K) (lam : K), lam ≠ 0 ∧ (∀ c : Kˣ, ((ξ c : Kˣ) : K) = g c) ∧
      ∀ t, A.X t (A.act (pm K (Equiv.swap 0 3)) v₀) =
        A.act (pm K (Equiv.swap 0 3)) v₀ + (lam * g t) • v₀ := by
  obtain ⟨β, hβ⟩ := exists_beta A S
  have hadd := beta_add A S hβ
  have hsc := beta_scale A S hβ
  obtain ⟨t₀, ht₁⟩ := beta_ne_zero A S hβ
  have hβ0 : β 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    linear_combination -h
  have ht₀ : t₀ ≠ 0 := by
    rintro rfl
    exact ht₁ hβ0
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : K → K, ∀ s, g₀ s = β (s * t₀) * (β t₀)⁻¹ :=
    ⟨fun s => β (s * t₀) * (β t₀)⁻¹, fun s => rfl⟩
  have hg₀_add : ∀ s s', g₀ (s + s') = g₀ s + g₀ s' := by
    intro s s'
    simp only [hg₀, add_mul, hadd]
  have hg₀_zero : g₀ 0 = 0 := by
    simp only [hg₀, zero_mul, hβ0]
  have hg₀_one : g₀ 1 = 1 := by
    rw [hg₀, one_mul]
    exact mul_inv_cancel₀ ht₁
  have hg₀_scale : ∀ (c : Kˣ) (s : K),
      g₀ (((c : Kˣ) : K) ^ 2 * s) = ((ξ c : Kˣ) : K) ^ 2 * g₀ s := by
    intro c s
    simp only [hg₀]
    rw [show ((c : Kˣ) : K) ^ 2 * s * t₀ = ((c : Kˣ) : K) ^ 2 * (s * t₀) by ring, hsc]
    ring
  have h1 : ∀ c : Kˣ, g₀ (((c : Kˣ) : K) ^ 2) = ((ξ c : Kˣ) : K) ^ 2 := by
    intro c
    have h := hg₀_scale c 1
    rw [mul_one, hg₀_one, mul_one] at h
    exact h
  have hsq : ∀ x : K, x ≠ 0 → ∃ c : Kˣ, ((c : Kˣ) : K) ^ 2 = x := by
    intro x hx
    obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) x
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact hx (by rw [hr, zero_mul])
    exact ⟨Units.mk0 r hr0, by rw [Units.val_mk0, sq, hr]⟩
  have hmul : ∀ x y : K, g₀ (x * y) = g₀ x * g₀ y := by
    intro x y
    by_cases hx : x = 0
    · rw [hx, zero_mul, hg₀_zero, zero_mul]
    · obtain ⟨c, rfl⟩ := hsq x hx
      rw [hg₀_scale c y, h1 c]
  obtain ⟨f, hf⟩ : ∃ f : K →+* K, ∀ x, f x = g₀ x :=
    ⟨{ toFun := g₀, map_one' := hg₀_one, map_mul' := hmul, map_zero' := hg₀_zero,
        map_add' := hg₀_add }, fun x => rfl⟩
  have hbij : Function.Bijective f := Finite.injective_iff_bijective.1 f.injective
  obtain ⟨g, hg⟩ : ∃ g : K ≃+* K, ∀ x, g x = g₀ x :=
    ⟨RingEquiv.ofBijective f hbij, fun x => hf x⟩
  have hξg : ∀ c : Kˣ, ((ξ c : Kˣ) : K) = g c := by
    intro c
    have h2 : g (c : K) ^ 2 = ((ξ c : Kˣ) : K) ^ 2 := by
      rw [← map_pow, hg]
      exact h1 c
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
    · exact h.symm
    · rw [CharTwo.neg_eq] at h
      exact h.symm
  have hgt₀ : g t₀ ≠ 0 := (map_ne_zero g).2 ht₀
  have hkey : ∀ t, g t * (g t₀)⁻¹ = β t * (β t₀)⁻¹ := by
    intro t
    have h2 : g (t * t₀⁻¹) = g t * (g t₀)⁻¹ := by
      rw [map_mul, map_inv₀]
    have h3 : g₀ (t * t₀⁻¹) = β t * (β t₀)⁻¹ := by
      rw [hg₀, mul_assoc, inv_mul_cancel₀ ht₀, mul_one]
    rw [← h2, hg, h3]
  have hβt : ∀ t, β t = β t₀ * (g t₀)⁻¹ * g t := by
    intro t
    calc β t = β t * (β t₀)⁻¹ * β t₀ := by rw [mul_assoc, inv_mul_cancel₀ ht₁, mul_one]
      _ = g t * (g t₀)⁻¹ * β t₀ := by rw [hkey t]
      _ = β t₀ * (g t₀)⁻¹ * g t := by ring
  refine ⟨g, β t₀ * (g t₀)⁻¹, mul_ne_zero ht₁ (inv_ne_zero hgt₀), hξg, fun t => ?_⟩
  rw [hβ t, hβt t]

theorem rank_one_normalized [Finite K] {v₀ : V} {ξ : Kˣ →* Kˣ} (S : Setup A v₀ ξ) :
    ∃ g : K ≃+* K, (∀ c : Kˣ, ((ξ c : Kˣ) : K) = g c) ∧
      (∀ t, A.X t (A.act (pm K (Equiv.swap 0 3)) v₀) =
        A.act (pm K (Equiv.swap 0 3)) v₀ + g t • v₀) ∧
      ∀ t, A.Y t v₀ = v₀ + g t • A.act (pm K (Equiv.swap 0 3)) v₀ := by
  obtain ⟨g, lam, -, hξg, hX⟩ := rank_one A S
  have h03 : (0 : Fin 6) ≠ 3 := by decide
  have h30 : (3 : Fin 6) ≠ 0 := by decide
  have hdet_pm : ((pm K (Equiv.swap (0 : Fin 6) 3) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K).det = 1 := det_pm _
  have hss : pm K (Equiv.swap (0 : Fin 6) 3) * pm K (Equiv.swap (0 : Fin 6) 3) = 1 := by
    rw [← map_mul, Equiv.swap_mul_self, map_one]
  have hact_ss : A.act (pm K (Equiv.swap (0 : Fin 6) 3)) *
      A.act (pm K (Equiv.swap (0 : Fin 6) 3)) = 1 := by
    rw [← A.act_mul _ _ hdet_pm hdet_pm, hss, A.act_one]
  have hs : ∀ v, A.act (pm K (Equiv.swap (0 : Fin 6) 3))
      (A.act (pm K (Equiv.swap (0 : Fin 6) 3)) v) = v := by
    intro v
    have h := congrArg (fun f : V →ₗ[K] V => f v) hact_ss
    simpa using h
  have hyx : ∀ t : K, transvGL K 3 0 h30 t =
      pm K (Equiv.swap (0 : Fin 6) 3) * transvGL K 0 3 h03 t *
        pm K (Equiv.swap (0 : Fin 6) 3) := by
    intro t
    have h1 := pm_conj_tr (Equiv.swap (0 : Fin 6) 3) h03 t
    rw [inv_eq_of_mul_eq_one_right hss] at h1
    rw [h1]
    exact rkC_transv_congr h30 _ t (Equiv.swap_apply_left (0 : Fin 6) 3).symm
      (Equiv.swap_apply_right (0 : Fin 6) 3).symm
  have hconj : ∀ t : K, A.Y t = A.act (pm K (Equiv.swap (0 : Fin 6) 3)) * A.X t *
      A.act (pm K (Equiv.swap (0 : Fin 6) 3)) := by
    intro t
    have hdt : ((transvGL K 0 3 h03 t : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 :=
      det_tr h03 t
    show A.act (transvGL K 3 0 h30 t) = A.act (pm K (Equiv.swap (0 : Fin 6) 3)) *
      A.act (transvGL K 0 3 h03 t) * A.act (pm K (Equiv.swap (0 : Fin 6) 3))
    rw [hyx t, A.act_mul _ _ (rkC_det_mul hdet_pm hdt) hdet_pm, A.act_mul _ _ hdet_pm hdt]
  have hY : ∀ t : K,
      A.Y t v₀ = v₀ + (lam * g t) • A.act (pm K (Equiv.swap (0 : Fin 6) 3)) v₀ := by
    intro t
    have h1 : A.Y t v₀ = A.act (pm K (Equiv.swap (0 : Fin 6) 3))
        (A.X t (A.act (pm K (Equiv.swap (0 : Fin 6) 3)) v₀)) := by
      simp only [hconj t, Module.End.mul_apply]
    rw [h1, hX t, map_add, map_smul, hs]
  have hX1 : A.X 1 v₀ = v₀ := X_fix_I0 A S.hv₀ 1
  have hswap : transvGL K 0 3 h03 1 * transvGL K 3 0 h30 1 * transvGL K 0 3 h03 1 =
      pm K (Equiv.swap (0 : Fin 6) 3) := swap_eq h03
  have hv1 : A.act (pm K (Equiv.swap (0 : Fin 6) 3)) v₀ = A.X 1 (A.Y 1 v₀) := by
    rw [← hswap, A.act_mul _ _ (rkC_det_mul (det_tr h03 (1 : K)) (det_tr h30 (1 : K)))
        (det_tr h03 (1 : K)), A.act_mul _ _ (det_tr h03 (1 : K)) (det_tr h30 (1 : K))]
    show A.X 1 (A.Y 1 (A.X 1 v₀)) = A.X 1 (A.Y 1 v₀)
    rw [hX1]
  have hfin : A.act (pm K (Equiv.swap (0 : Fin 6) 3)) v₀ =
      v₀ + lam • (A.act (pm K (Equiv.swap (0 : Fin 6) 3)) v₀ + lam • v₀) := by
    have h1 := hv1
    rw [hY 1, map_add, map_smul, hX1, hX 1] at h1
    simp only [map_one, mul_one] at h1
    exact h1
  have hrel : (1 + lam ^ 2) • v₀ + (lam - 1) • A.act (pm K (Equiv.swap (0 : Fin 6) 3)) v₀
      = 0 := by
    have e : (1 + lam ^ 2) • v₀ + (lam - 1) • A.act (pm K (Equiv.swap (0 : Fin 6) 3)) v₀ =
        (v₀ + lam • (A.act (pm K (Equiv.swap (0 : Fin 6) 3)) v₀ + lam • v₀)) -
          A.act (pm K (Equiv.swap (0 : Fin 6) 3)) v₀ := by
      module
    rw [e, ← hfin, sub_self]
  have hind := LinearIndependent.pair_iff.1 (linearIndependent_v0_v1 A S)
  have hlam : lam = 1 := sub_eq_zero.1 (hind _ _ hrel).2
  refine ⟨g, hξg, fun t => ?_, fun t => ?_⟩
  · rw [hX t, hlam, one_mul]
  · rw [hY t, hlam, one_mul]

end SLAct

end CFSG.RankThree.GF2n.Smith81.S81J
