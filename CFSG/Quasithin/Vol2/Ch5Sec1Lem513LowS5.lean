module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem513LowNat
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem513LowD5
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Equiv

section S5

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem realizesVia_complement {D : FFModel} {H : Subgroup (MulAut V)} {I J : Subgroup V}
    {π : D.Gam →* ↥H} (h : D.RealizesVia H ⊤ I π) (hJ : ∀ k : ↥H, ∀ w ∈ J, (k : MulAut V) w ∈ J)
    (hIJ : I ⊓ J = ⊥) (hIJ' : I ⊔ J = ⊤) : D.RealizesVia H J ⊥ π := by
  obtain ⟨hs, -, hks, -, -, hsec, hker, β, hβs, hβk, hβe⟩ := h
  have hmem : ∀ v : V, ∃ i ∈ I, ∃ j ∈ J, v = i * j := by
    intro v
    have hv : v ∈ I ⊔ J := hIJ' ▸ Subgroup.mem_top v
    obtain ⟨i, hi, j, hj, hij⟩ := Subgroup.mem_sup.mp hv
    exact ⟨i, hi, j, hj, hij.symm⟩
  refine ⟨hs, bot_le, hks, hJ, fun k z hz => ?_, hsec, hker, β.comp (Subgroup.inclusion le_top),
    ?_, ?_, ?_⟩
  · rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro q
    obtain ⟨v, rfl⟩ := hβs q
    obtain ⟨i, hi, j, hj, hv⟩ := hmem v
    refine ⟨⟨j, hj⟩, ?_⟩
    have h1 : β ⟨i, trivial⟩ = 1 := (hβk _).2 hi
    have h2 : v = (⟨i, trivial⟩ * ⟨j, trivial⟩ : ↥(⊤ : Subgroup V)) := Subtype.ext hv
    show β ⟨j, trivial⟩ = β v
    rw [h2, map_mul, h1, one_mul]
  · intro u
    show β ⟨u, trivial⟩ = 1 ↔ (u : V) ∈ ⊥
    rw [hβk]
    constructor
    · intro hu
      rw [← hIJ]
      exact ⟨hu, u.2⟩
    · intro hu
      rw [Subgroup.mem_bot] at hu
      rw [hu]
      exact I.one_mem
  · intro γ u m hu hm hum
    exact hβe γ ⟨u, trivial⟩ m trivial hm hum


theorem zmod2_eq_of_zero_eq_add : ∀ a b : ZMod 2, 0 = a + b → b = a := by decide

omit [Finite V] in
theorem exists_complement_of_alternatingNatural_five (hV : ∀ v : V, v ^ 2 = 1)
    {K : Subgroup (MulAut V)} {I : Subgroup V} (h : AlternatingNatural K I ⊥ 5) :
    ∃ J : Subgroup V, (∀ k ∈ K, ∀ w ∈ J, k w ∈ J) ∧ I ⊓ J = ⊥ ∧ I ⊔ J = ⊤ := by
  classical
  obtain ⟨π, hπ⟩ : ∃ π : ↥(alternatingGroup (Fin 5)) →* ↥K,
      (FFModel.altDn 5).RealizesVia K I ⊥ π := h
  have hIinv : ∀ k : ↥K, ∀ u ∈ I, (k : MulAut V) u ∈ I := hπ.2.2.2.1
  have hπs : Function.Surjective π := hπ.1
  obtain ⟨vec, hvec_mul, hvec_ker, hvec_sum, hvec_surj, hvec_act⟩ := exists_d5_coords hπ
  have hvec_one : vec 1 = 0 := (hvec_ker 1).2 (Subgroup.mem_bot.mpr rfl)
  have hvec_inj : ∀ u w : ↥I, vec u = vec w → u = w := by
    intro u w huw
    have h1 : vec (u * w⁻¹) = 0 := by
      have h3 := hvec_mul (u * w⁻¹) w
      rw [inv_mul_cancel_right, huw] at h3
      exact right_eq_add.mp h3
    have h2 := (hvec_ker _).1 h1
    rw [Subgroup.mem_bot] at h2
    exact mul_inv_eq_one.mp (Subtype.ext h2)
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule fun u => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, hV]
    rfl
  let Isub : Submodule (ZMod 2) (Additive V) :=
    AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup I)
  have hmemI : ∀ v : V, Additive.ofMul v ∈ Isub ↔ v ∈ I := fun v => by
    rw [AddSubgroup.mem_toZModSubmodule]
    exact Iff.rfl
  let vecA : ↥Isub →+ (Fin 5 → ZMod 2) :=
    { toFun := fun x => vec ⟨Additive.toMul (x : Additive V), (hmemI _).1 x.2⟩
      map_zero' := hvec_one
      map_add' := fun x y => hvec_mul ⟨Additive.toMul (x : Additive V), (hmemI _).1 x.2⟩
        ⟨Additive.toMul (y : Additive V), (hmemI _).1 y.2⟩ }
  have hvecA_smul : ∀ (c : ZMod 2) (x : ↥Isub) (i : Fin 5), vecA (c • x) i = c * vecA x i := by
    intro c x i
    fin_cases c
    · show vecA ((0 : ZMod 2) • x) i = (0 : ZMod 2) * vecA x i
      rw [zero_smul, map_zero, Pi.zero_apply, zero_mul]
    · show vecA ((1 : ZMod 2) • x) i = (1 : ZMod 2) * vecA x i
      rw [one_smul, one_mul]
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl Isub
  let ℓ : Additive V →+ ZMod 2 := (Pi.evalAddMonoidHom (fun _ : Fin 5 => ZMod 2) 0).comp
    (vecA.comp (Submodule.projectionOnto Isub C hC).toAddMonoidHom)
  have hℓI : ∀ (u : V) (hu : u ∈ I), ℓ (Additive.ofMul u) = vec ⟨u, hu⟩ 0 := by
    intro u hu
    have h1 : Submodule.projectionOnto Isub C hC (Additive.ofMul u) =
        ⟨Additive.ofMul u, (hmemI u).2 hu⟩ :=
      Submodule.projectionOnto_apply_left hC ⟨Additive.ofMul u, (hmemI u).2 hu⟩
    show vecA (Submodule.projectionOnto Isub C hC (Additive.ofMul u)) 0 = _
    rw [h1]
    rfl
  obtain ⟨x₀, hx₀⟩ := hvec_surj pair04 (by decide)
  let act : ↥(alternatingGroup (Fin 5)) → Additive V →ₗ[ZMod 2] Additive V := fun σ =>
    (MulEquiv.toAdditive (((π σ : ↥K) : MulAut V) : V ≃* V)).toAddMonoidHom.toZModLinearMap 2
  have hact : ∀ σ v, act σ (Additive.ofMul v) = Additive.ofMul (((π σ : ↥K) : MulAut V) v) :=
    fun _ _ => rfl
  let term : ↥(alternatingGroup (Fin 5)) → Additive V →+ Additive V := fun σ =>
    { toFun := fun w => ℓ (act σ⁻¹ w) • act σ (Additive.ofMul (x₀ : V))
      map_zero' := by simp
      map_add' := fun w w' => by rw [map_add, map_add, add_smul] }
  obtain ⟨P, hPapp⟩ : ∃ P : Additive V →+ Additive V, ∀ w, P w = ∑ σ : ↥(alternatingGroup (Fin 5)),
      ℓ (act σ⁻¹ w) • act σ (Additive.ofMul (x₀ : V)) :=
    ⟨∑ σ : ↥(alternatingGroup (Fin 5)), term σ, fun w => by
      simp [term]⟩
  have hPI : ∀ w, P w ∈ Isub := by
    intro w
    rw [hPapp]
    refine Submodule.sum_mem _ fun σ _ => Submodule.smul_mem _ _ ?_
    rw [hact, hmemI]
    exact hIinv _ _ x₀.2
  have hPid : ∀ (u : V), u ∈ I → P (Additive.ofMul u) = Additive.ofMul u := by
    intro u hu
    have hp := hPI (Additive.ofMul u)
    set u' : V := Additive.toMul (P (Additive.ofMul u)) with hu'
    have hu'I : u' ∈ I := (hmemI u').1 (by rw [hu', ofMul_toMul]; exact hp)
    suffices hvv : vec ⟨u', hu'I⟩ = vec ⟨u, hu⟩ by
      have h1 : u' = u := congrArg Subtype.val (hvec_inj _ _ hvv)
      apply Additive.toMul.injective
      rw [toMul_ofMul]
      exact hu'.symm.trans h1
    have h1 : vecA ⟨P (Additive.ofMul u), hp⟩ = vec ⟨u', hu'I⟩ := rfl
    rw [← h1]
    have h2 : (⟨P (Additive.ofMul u), hp⟩ : ↥Isub) = ∑ σ : ↥(alternatingGroup (Fin 5)),
        ℓ (act σ⁻¹ (Additive.ofMul u)) •
          (⟨act σ (Additive.ofMul (x₀ : V)), by rw [hact, hmemI]; exact hIinv _ _ x₀.2⟩ :
            ↥Isub) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      exact hPapp _
    rw [h2, map_sum]
    funext i
    rw [Finset.sum_apply]
    simp only [hvecA_smul]
    have h4 : ∀ σ : ↥(alternatingGroup (Fin 5)),
        ℓ (act σ⁻¹ (Additive.ofMul u)) * vecA
          ⟨act σ (Additive.ofMul (x₀ : V)), by rw [hact, hmemI]; exact hIinv _ _ x₀.2⟩ i =
        vec ⟨u, hu⟩ ((σ : Perm (Fin 5)) 0) * pair04 (((σ : Perm (Fin 5)))⁻¹ i) := by
      intro σ
      have e1 := hvec_act σ⁻¹ ⟨u, hu⟩ (hIinv _ _ hu)
      have e2 := hvec_act σ x₀ (hIinv _ _ x₀.2)
      have e3 : vecA ⟨act σ (Additive.ofMul (x₀ : V)),
          by rw [hact, hmemI]; exact hIinv _ _ x₀.2⟩ =
          vec ⟨((π σ : ↥K) : MulAut V) (x₀ : V), hIinv _ _ x₀.2⟩ := rfl
      rw [e3, hact, hℓI _ (hIinv _ _ hu), e2, e1, hx₀]
      simp
    simp only [h4]
    rw [← Finset.sum_subtype (Finset.univ.filter fun σ : Perm (Fin 5) => Perm.sign σ = 1)
      (fun σ => by simp [Perm.mem_alternatingGroup])
      (fun σ => vec ⟨u, hu⟩ (σ 0) * pair04 (σ⁻¹ i))]
    exact d5_average _ (hvec_sum ⟨u, hu⟩) i
  have hact_mul : ∀ a b w, act (a * b) w = act a (act b w) := by
    intro a b w
    show Additive.ofMul (((π (a * b) : ↥K) : MulAut V) (Additive.toMul w)) =
      Additive.ofMul (((π a : ↥K) : MulAut V) (Additive.toMul (Additive.ofMul
        (((π b : ↥K) : MulAut V) (Additive.toMul w)))))
    rw [map_mul, Subgroup.coe_mul, MulAut.mul_apply, toMul_ofMul]
  have hact_one : ∀ w, act 1 w = w := by
    intro w
    show Additive.ofMul (((π 1 : ↥K) : MulAut V) (Additive.toMul w)) = w
    rw [map_one]
    rfl
  have hPequiv : ∀ (τ : ↥(alternatingGroup (Fin 5))) (w : Additive V),
      P (act τ w) = act τ (P w) := by
    intro τ w
    rw [hPapp, hPapp, map_sum]
    simp only [map_smul]
    rw [← Equiv.sum_comp (Equiv.mulLeft τ)]
    apply Finset.sum_congr rfl
    intro σ' _
    simp only [Equiv.coe_mulLeft]
    have e1 : act (τ * σ')⁻¹ (act τ w) = act σ'⁻¹ w := by
      rw [mul_inv_rev, hact_mul, ← hact_mul τ⁻¹ τ, inv_mul_cancel, hact_one]
    have e2 : act (τ * σ') (Additive.ofMul (x₀ : V)) =
        act τ (act σ' (Additive.ofMul (x₀ : V))) := hact_mul _ _ _
    rw [e1, e2]
  let J : Subgroup V :=
    { carrier := {v | P (Additive.ofMul v) = 0}
      one_mem' := by
        show P (Additive.ofMul 1) = 0
        rw [ofMul_one, map_zero]
      mul_mem' := fun {a b} ha hb => by
        show P (Additive.ofMul (a * b)) = 0
        rw [ofMul_mul, map_add, show P (Additive.ofMul a) = 0 from ha,
          show P (Additive.ofMul b) = 0 from hb, add_zero]
      inv_mem' := fun {a} ha => by
        show P (Additive.ofMul a⁻¹) = 0
        rw [ofMul_inv, map_neg, show P (Additive.ofMul a) = 0 from ha, neg_zero] }
  refine ⟨J, ?_, ?_, ?_⟩
  · intro k hk w hw
    obtain ⟨τ, hτ⟩ : ∃ τ : ↥(alternatingGroup (Fin 5)), π τ = ⟨k, hk⟩ := hπs ⟨k, hk⟩
    have hk' : k = ((π τ : ↥K) : MulAut V) := by rw [hτ]
    show P (Additive.ofMul (k w)) = 0
    rw [hk', ← hact, hPequiv, show P (Additive.ofMul w) = 0 from hw, map_zero]
  · rw [eq_bot_iff]
    rintro v ⟨hvI, hvJ⟩
    rw [Subgroup.mem_bot]
    apply Additive.ofMul.injective
    rw [← hPid v hvI]
    exact hvJ
  · rw [eq_top_iff]
    intro v _
    set p := Additive.toMul (P (Additive.ofMul v)) with hp
    have hpI : p ∈ I := (hmemI p).1 (by rw [hp, ofMul_toMul]; exact hPI _)
    have hpJ : p⁻¹ * v ∈ J := by
      show P (Additive.ofMul (p⁻¹ * v)) = 0
      rw [ofMul_mul, ofMul_inv, map_add, map_neg, hPid p hpI, hp, ofMul_toMul, neg_add_cancel]
    have hv : v = p * (p⁻¹ * v) := by group
    rw [hv]
    exact Subgroup.mul_mem_sup hpI hpJ

theorem card_sec_of_symmetricNatural_five {X : Subgroup (MulAut V)} {U Z : Subgroup V}
    (h : SymmetricNatural X U Z 5) : Nat.card U = 16 * Nat.card Z := by
  obtain ⟨π, -, hZU, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  have h1 := card_eq_card_range_mul_card_ker β
  rw [MonoidHom.range_eq_top.mpr hβs, Subgroup.card_top] at h1
  have hk : β.ker = Z.subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hβk u
  have h16 : Nat.card (↥(FFModel.symDn 5).sec ⧸
      (FFModel.symDn 5).ker.subgroupOf (FFModel.symDn 5).sec) = 16 := by
    show Nat.card (↥(FFModel.altDn 5).sec ⧸
      (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec) = 16
    rw [Nat.card_congr d5Rep]
    exact Explicit.card_coreMod (n := 5) (by norm_num)
  rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv, h16] at h1
  exact h1

omit [Finite V] in
theorem exists_proj_of_compl {I J : Subgroup V} (hIJ : I ⊓ J = ⊥) (hIJ' : I ⊔ J = ⊤) :
    ∃ p : V →* V, (∀ v, p v ∈ J) ∧ (∀ v, v * (p v)⁻¹ ∈ I) ∧ ∀ v, p v = 1 ↔ v ∈ I := by
  classical
  have hdec : ∀ v : V, ∃ i ∈ I, ∃ j ∈ J, v = i * j := by
    intro v
    have hv : v ∈ I ⊔ J := hIJ' ▸ Subgroup.mem_top v
    obtain ⟨i, hi, j, hj, hij⟩ := Subgroup.mem_sup.mp hv
    exact ⟨i, hi, j, hj, hij.symm⟩
  choose fi hfi fj hfj hv using hdec
  have huniq : ∀ i ∈ I, ∀ j ∈ J, ∀ i' ∈ I, ∀ j' ∈ J, i * j = i' * j' → j = j' := by
    intro i hi j hj i' hi' j' hj' he
    have h1 : j * j'⁻¹ ∈ I ⊓ J := by
      refine ⟨?_, J.mul_mem hj (J.inv_mem hj')⟩
      have : j * j'⁻¹ = i⁻¹ * i' := by
        calc j * j'⁻¹ = i⁻¹ * (i * j) * j'⁻¹ := by group
          _ = i⁻¹ * (i' * j') * j'⁻¹ := by rw [he]
          _ = i⁻¹ * i' := by group
      rw [this]
      exact I.mul_mem (I.inv_mem hi) hi'
    rw [hIJ, Subgroup.mem_bot] at h1
    exact mul_inv_eq_one.mp h1
  let p : V →* V :=
    { toFun := fj
      map_one' := (huniq _ (hfi 1) _ (hfj 1) 1 I.one_mem 1 J.one_mem
        (by rw [← hv 1, one_mul])).trans rfl
      map_mul' := fun v w => by
        refine huniq _ (hfi (v * w)) _ (hfj (v * w)) (fi v * fi w) (I.mul_mem (hfi v) (hfi w))
          _ (J.mul_mem (hfj v) (hfj w)) ?_
        rw [← hv (v * w)]
        calc v * w = (fi v * fj v) * (fi w * fj w) := by rw [← hv v, ← hv w]
          _ = fi v * fi w * (fj v * fj w) := by
            rw [mul_mul_mul_comm] }
  refine ⟨p, hfj, fun v => ?_, fun v => ?_⟩
  · have : v * (fj v)⁻¹ = fi v := by
      calc v * (fj v)⁻¹ = (fi v * fj v) * (fj v)⁻¹ := by rw [← hv v]
        _ = fi v := by group
    show v * (fj v)⁻¹ ∈ I
    rw [this]
    exact hfi v
  · constructor
    · intro h1
      have h2 : v = fi v * fj v := hv v
      show v ∈ I
      rw [h2, show fj v = 1 from h1, mul_one]
      exact hfi v
    · intro hvI
      exact (huniq _ (hfi v) _ (hfj v) v hvI 1 J.one_mem (by rw [← hv v, mul_one])).trans rfl

theorem card_le_four_of_dependent {G : Type} [Group G] (A : Subgroup G) [Finite A]
    (h : ∀ γ ∈ A, ∀ δ ∈ A, ∀ ε ∈ A,
      γ = 1 ∨ δ = 1 ∨ δ = γ ∨ ε = 1 ∨ ε = γ ∨ ε = δ ∨ ε = γ * δ) :
    Nat.card A ≤ 4 := by
  classical
  by_contra hlt
  push Not at hlt
  have hex : ∀ s : Finset G, s.card < Nat.card A → ∃ a ∈ A, a ∉ s := by
    intro s hs
    by_contra hcon
    push Not at hcon
    have hsub : (A : Set G) ⊆ (s : Set G) := fun a ha => hcon a ha
    have h1 : Nat.card A ≤ Nat.card (s : Set G) := Nat.card_mono s.finite_toSet hsub
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset] at h1
    omega
  obtain ⟨γ, hγ, hγ1⟩ := hex {1} (by rw [Finset.card_singleton]; omega)
  obtain ⟨δ, hδ, hδ1⟩ := hex {1, γ} (by have := Finset.card_le_two (a := (1 : G)) (b := γ); omega)
  obtain ⟨ε, hε, hε1⟩ := hex {1, γ, δ, γ * δ}
    (by have := Finset.card_le_four (a := (1 : G)) (b := γ) (c := δ) (d := γ * δ); omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hγ1 hδ1 hε1
  rcases h γ hγ δ hδ ε hε with h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exact hγ1 h1
  · exact hδ1.1 h1
  · exact hδ1.2 h1
  · exact hε1.1 h1
  · exact hε1.2.1 h1
  · exact hε1.2.2.1 h1
  · exact hε1.2.2.2 h1

theorem s5_sum_of_s5_s5 (hV : ∀ v : V, v ^ 2 = 1) {X K A : Subgroup (MulAut V)}
    {I : Subgroup V} (hKX : K ≤ X) (hKn : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K)
    (hK60 : Nat.card K = 60) (hX : Nonempty (↥X ≃* Perm (Fin 5)))
    (hI : SymmetricNatural X I ⊥ 5) (hQ : SymmetricNatural X ⊤ I 5) (hAX : A ≤ X)
    (hA2 : IsElemAbelian2 A) (hAK : ¬ A ≤ K)
    (hAI : Nat.card A * Nat.card ↥(I ⊓ fixV A) ≤ Nat.card I)
    (hr : rkIdx (fixV A) ≤ 2 * rk A) :
    ∃ W₁ W₂ : Subgroup V, (∀ x ∈ X, ∀ w ∈ W₁, x w ∈ W₁) ∧ (∀ x ∈ X, ∀ w ∈ W₂, x w ∈ W₂) ∧
      W₁ ⊓ W₂ = ⊥ ∧ W₁ ⊔ W₂ = ⊤ ∧ SymmetricNatural X W₁ ⊥ 5 ∧
        SymmetricNatural X W₂ ⊥ 5 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨πI, hπI⟩ : ∃ πI : Perm (Fin 5) →* ↥X, (FFModel.symDn 5).RealizesVia X I ⊥ πI := hI
  obtain ⟨πQ, hπQ⟩ : ∃ πQ : Perm (Fin 5) →* ↥X, (FFModel.symDn 5).RealizesVia X ⊤ I πQ := hQ
  have hIinv : ∀ x : ↥X, ∀ u ∈ I, (x : MulAut V) u ∈ I := hπI.2.2.2.1
  have hπIinj : Function.Injective πI :=
    G64.RealizesVia.injective_of_faithful' (G64.symDn_faithful le_rfl) hπI
  have hIc : Nat.card I = 16 := by
    have := card_sec_of_symmetricNatural_five ⟨πI, hπI⟩
    rwa [Subgroup.card_bot, mul_one] at this
  have hVc : Nat.card V = 16 * 16 := by
    have := card_sec_of_symmetricNatural_five ⟨πQ, hπQ⟩
    rwa [Subgroup.card_top, hIc] at this
  have hIalt := alternatingNatural_of_symmetricNatural_five ⟨πI, hπI⟩ hKX hK60
  obtain ⟨J, hJK, hIJ, hIJ'⟩ := exists_complement_of_alternatingNatural_five hV hIalt
  have hQalt := alternatingNatural_of_symmetricNatural_five ⟨πQ, hπQ⟩ hKX hK60
  have hIK : ∀ k ∈ K, ∀ u ∈ I, k u ∈ I := fun k hk u hu => hIinv ⟨k, hKX hk⟩ u hu
  have hJirr : ∀ J' : Subgroup V, (∀ k ∈ K, ∀ w ∈ J', k w ∈ J') → J' ≤ J → J' = ⊥ ∨ J' = J := by
    intro J' hJ' hJ'J
    have hY : ∀ k ∈ K, ∀ y ∈ I ⊔ J', k y ∈ I ⊔ J' := by
      intro k hk y hy
      obtain ⟨i, hi, j, hj, rfl⟩ := Subgroup.mem_sup.mp hy
      rw [map_mul]
      exact Subgroup.mul_mem_sup (hIK k hk i hi) (hJ' k hk j hj)
    rcases eq_or_eq_of_alternatingNatural_five hQalt hY le_sup_left le_top with h1 | h1
    · left
      rw [eq_bot_iff, ← hIJ]
      exact le_inf (h1 ▸ le_sup_right) hJ'J
    · right
      refine le_antisymm hJ'J fun j hj => ?_
      have hj' : j ∈ I ⊔ J' := h1 ▸ Subgroup.mem_top j
      obtain ⟨i, hi, j', hj'J', hij⟩ := Subgroup.mem_sup.mp hj'
      have hiJ : i ∈ J := by
        have : i = j * j'⁻¹ := by rw [← hij]; group
        rw [this]
        exact J.mul_mem hj (J.inv_mem (hJ'J hj'J'))
      have hi1 : i = 1 := by
        have : i ∈ I ⊓ J := ⟨hi, hiJ⟩
        rw [hIJ, Subgroup.mem_bot] at this
        exact this
      rw [← hij, hi1, one_mul]
      exact hj'J'
  obtain ⟨t, htA, htK⟩ := Set.not_subset.mp hAK
  have htX : t ∈ X := hAX htA
  have ht2 : t * t = 1 := by rw [← pow_two]; exact hA2.2 t htA
  have htJ : ∀ j ∈ J, t j ∈ J := by
    by_contra hcon
    push Not at hcon
    obtain ⟨j₀, hj₀J, hj₀t⟩ := hcon
    let J₀ : Subgroup V :=
      { carrier := {j | j ∈ J ∧ t j ∈ J}
        one_mem' := ⟨J.one_mem, by rw [map_one]; exact J.one_mem⟩
        mul_mem' := fun ha hb => ⟨J.mul_mem ha.1 hb.1, by rw [map_mul]; exact J.mul_mem ha.2 hb.2⟩
        inv_mem' := fun ha => ⟨J.inv_mem ha.1, by rw [map_inv]; exact J.inv_mem ha.2⟩ }
    have hJ₀K : ∀ k ∈ K, ∀ w ∈ J₀, k w ∈ J₀ := by
      rintro k hk w ⟨hwJ, hwt⟩
      refine ⟨hJK k hk w hwJ, ?_⟩
      have hk' : t * k * t⁻¹ ∈ K := hKn t htX k hk
      have : t (k w) = (t * k * t⁻¹) (t w) := by simp [MulAut.mul_apply]
      rw [this]
      exact hJK _ hk' _ hwt
    have hJ₀ : J₀ = ⊥ := by
      rcases hJirr J₀ hJ₀K (fun w hw => hw.1) with h1 | h1
      · exact h1
      · exfalso
        exact hj₀t (h1 ▸ (show j₀ ∈ J from hj₀J) |>.2)
    have hstar : ∀ j ∈ J, t j = j → j = 1 := by
      intro j hj htj
      have : j ∈ J₀ := ⟨hj, by rw [htj]; exact hj⟩
      rw [hJ₀, Subgroup.mem_bot] at this
      exact this
    obtain ⟨p, hpJ, hpI, hp1⟩ := exists_proj_of_compl hIJ hIJ'
    let δ : ↥I →* V :=
      { toFun := fun u => t (u : V) * (u : V)⁻¹
        map_one' := by simp
        map_mul' := fun u w => by
          simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
          rw [mul_comm ((w : V))⁻¹ ((u : V))⁻¹, mul_mul_mul_comm] }
    let χ : ↥(fixV A) →* V :=
      { toFun := fun v => t (p v) * (p v)⁻¹
        map_one' := by simp
        map_mul' := fun v w => by
          simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
          rw [mul_comm ((p w))⁻¹ ((p v))⁻¹, mul_mul_mul_comm] }
    have hχδ : χ.range ≤ δ.range := by
      rintro _ ⟨v, rfl⟩
      have hvt : t (v : V) = v := v.2 t htA
      set i := (v : V) * (p v)⁻¹ with hi
      have hiI : i ∈ I := hpI v
      refine ⟨⟨i, hiI⟩, ?_⟩
      show t i * i⁻¹ = t (p v) * (p v)⁻¹
      have hv' : (v : V) = i * p v := by rw [hi]; group
      have h1 : t i * t (p v) = i * p v := by rw [← map_mul, ← hv', hvt, hv']
      have h2 : t (p v) * (p v)⁻¹ = (t i * i⁻¹)⁻¹ := by
        have h3 : t (p v) = (t i)⁻¹ * (i * p v) := by rw [← h1]; group
        rw [h3, show (t i)⁻¹ * (i * p v) * (p v)⁻¹ = (t i)⁻¹ * i by group, mul_inv_rev,
          inv_inv, mul_comm]
      rw [h2]
      have hsq : ∀ w : V, w⁻¹ = w := fun w =>
        inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV w)
      exact (hsq _).symm
    have hχker : Nat.card χ.ker ≤ Nat.card ↥(I ⊓ fixV A) := by
      have hle : (χ.ker).map (fixV A).subtype ≤ I ⊓ fixV A := by
        rintro _ ⟨v, hv, rfl⟩
        refine ⟨?_, v.2⟩
        have h1 : t (p v) * (p v)⁻¹ = 1 := hv
        have h2 : t (p v) = p v := mul_inv_eq_one.mp h1
        have h3 : p v = 1 := hstar _ (hpJ v) h2
        exact (hp1 v).1 h3
      calc Nat.card χ.ker = Nat.card ((χ.ker).map (fixV A).subtype) :=
            (Subgroup.card_map_of_injective (fixV A).subtype_injective).symm
        _ ≤ Nat.card ↥(I ⊓ fixV A) := Subgroup.card_le_of_le hle
    have hδ : Nat.card δ.range ≤ 2 := by
      obtain ⟨vec, hvec_mul, hvec_ker, -, -, hvec_act⟩ := exists_s5_coords hπI
      obtain ⟨τ, hτ⟩ : ∃ τ : Perm (Fin 5), πI τ = ⟨t, htX⟩ := hπI.1 ⟨t, htX⟩
      have hτt : ((πI τ : ↥X) : MulAut V) = t := congrArg Subtype.val hτ
      have hτ2 : τ * τ = 1 := by
        apply hπIinj
        apply Subtype.ext
        rw [map_mul, map_one, Subgroup.coe_mul, hτt]
        exact ht2
      have hτsign : Perm.sign τ ≠ 1 := by
        intro hs
        apply htK
        rw [← hτt]
        exact (mem_iff_sign_eq_one_of_symmetricNatural hπI hKX hK60 τ).2 hs
      have hcoord : ∀ u : ↥I, ∃ hu : δ u ∈ I, vec ⟨δ u, hu⟩ = 0 ∨
          vec ⟨δ u, hu⟩ = (fun i => if τ i = i then (0 : ZMod 2) else 1) := by
        intro u
        have htu : ((πI τ : ↥X) : MulAut V) (u : V) ∈ I := hIinv _ _ u.2
        have hδu : δ u ∈ I := by
          show t (u : V) * (u : V)⁻¹ ∈ I
          exact I.mul_mem (hτt ▸ htu) (I.inv_mem u.2)
        refine ⟨hδu, ?_⟩
        have e1 : (⟨δ u, hδu⟩ : ↥I) = ⟨((πI τ : ↥X) : MulAut V) (u : V), htu⟩ * u⁻¹ := by
          apply Subtype.ext
          show t (u : V) * (u : V)⁻¹ = _
          rw [← hτt]
          rfl
        have e2 : vec (u⁻¹) = vec u := by
          have h3 := hvec_mul u u⁻¹
          rw [mul_inv_cancel, (hvec_ker 1).2 (Subgroup.mem_bot.mpr rfl)] at h3
          funext i
          have h4 := congrFun h3 i
          simp only [Pi.add_apply, Pi.zero_apply] at h4
          exact zmod2_eq_of_zero_eq_add _ _ h4
        rw [e1, hvec_mul, hvec_act τ u htu, e2]
        exact d5_comm_odd τ hτ2 hτsign (vec u)
      let f : ↥δ.range → Bool := fun x => by
        exact decide (x.1 = 1)
      have hinj : Function.Injective f := by
        rintro ⟨_, u, rfl⟩ ⟨_, w, rfl⟩ hfw
        apply Subtype.ext
        obtain ⟨hu, hu'⟩ := hcoord u
        obtain ⟨hw, hw'⟩ := hcoord w
        have hz : ∀ (x : V) (hx : x ∈ I), vec ⟨x, hx⟩ = 0 ↔ x = 1 := fun x hx => by
          rw [hvec_ker]
          exact Subgroup.mem_bot
        by_cases h1 : δ u = 1
        · have h2 : δ w = 1 := by
            have := hfw
            simp only [f, h1, decide_true] at this
            exact of_decide_eq_true this.symm
          show δ u = δ w
          rw [h1, h2]
        · have h2 : δ w ≠ 1 := by
            intro h2
            apply h1
            have := hfw
            simp only [f, h2, decide_true] at this
            exact of_decide_eq_true this
          have hu0 : vec ⟨δ u, hu⟩ ≠ 0 := fun h0 => h1 ((hz _ hu).1 h0)
          have hw0 : vec ⟨δ w, hw⟩ ≠ 0 := fun h0 => h2 ((hz _ hw).1 h0)
          have h3 : vec ⟨δ u, hu⟩ = vec ⟨δ w, hw⟩ := by
            rw [hu'.resolve_left hu0, hw'.resolve_left hw0]
          have h4 : vec (⟨δ u, hu⟩ * (⟨δ w, hw⟩ : ↥I)⁻¹) = 0 := by
            have h5 := hvec_mul (⟨δ u, hu⟩ * (⟨δ w, hw⟩ : ↥I)⁻¹) ⟨δ w, hw⟩
            rw [inv_mul_cancel_right, h3] at h5
            exact right_eq_add.mp h5
          have h6 := (hvec_ker _).1 h4
          rw [Subgroup.mem_bot] at h6
          exact mul_inv_eq_one.mp h6
      calc Nat.card δ.range ≤ Nat.card Bool := Nat.card_le_card_of_injective f hinj
        _ = 2 := by simp
    have hCA : Nat.card (fixV A) ≤ 2 * Nat.card ↥(I ⊓ fixV A) := by
      calc Nat.card (fixV A) = Nat.card χ.range * Nat.card χ.ker :=
            card_eq_card_range_mul_card_ker χ
        _ ≤ 2 * Nat.card ↥(I ⊓ fixV A) :=
            Nat.mul_le_mul ((Subgroup.card_le_of_le hχδ).trans hδ) hχker
    have hAc : Nat.card A = 2 ^ rk A := card_eq_two_pow_of_isPGroup hA2.isPGroup
    have hVle : Nat.card V ≤ Nat.card A ^ 2 * Nat.card (fixV A) := by
      have h1 := rk_add_rkIdx (fixV A)
      have h2 : Nat.card V = 2 ^ rk V :=
        card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hV)
      rw [h2, hAc, card_eq_two_pow hV (fixV A), ← pow_mul, ← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hA4 : Nat.card A ≤ 4 := by
      let φ : Perm (Fin 5) →* MulAut V := X.subtype.comp πI
      have hφ : Function.Injective φ := X.subtype_injective.comp hπIinj
      have hpre : ∀ a ∈ A, ∃ σ, φ σ = a := fun a ha => by
        obtain ⟨σ, hσ⟩ : ∃ σ : Perm (Fin 5), πI σ = ⟨a, hAX ha⟩ := hπI.1 ⟨a, hAX ha⟩
        exact ⟨σ, congrArg Subtype.val hσ⟩
      refine card_le_four_of_dependent A fun γ hγ δ hδ ε hε => ?_
      obtain ⟨γ', rfl⟩ := hpre γ hγ
      obtain ⟨δ', rfl⟩ := hpre δ hδ
      obtain ⟨ε', rfl⟩ := hpre ε hε
      have hsq : ∀ σ, φ σ ∈ A → σ * σ = 1 := fun σ hσ => hφ (by
        rw [map_mul, map_one, ← pow_two]
        exact hA2.2 _ hσ)
      have hcomm : ∀ σ ρ, φ σ ∈ A → φ ρ ∈ A → σ * ρ = ρ * σ := fun σ ρ hσ hρ => hφ (by
        rw [map_mul, map_mul]
        exact hA2.1 _ hσ _ hρ)
      rcases s5_elemAbelian_rank γ' (hsq _ hγ) δ' (hsq _ hδ) (hcomm _ _ hγ hδ) ε' (hsq _ hε)
          (hcomm _ _ hγ hε) (hcomm _ _ hδ hε) with h1 | h1 | h1 | h1 | h1 | h1 | h1
      · exact Or.inl (by rw [h1, map_one])
      · exact Or.inr (Or.inl (by rw [h1, map_one]))
      · exact Or.inr (Or.inr (Or.inl (by rw [h1])))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [h1, map_one]))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [h1])))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [h1]))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [h1, map_mul]))))))
    rw [hVc] at hVle
    rw [hIc] at hAI
    have hApos : 0 < Nat.card A := Nat.card_pos
    have h1 : 16 * 16 ≤ Nat.card A ^ 2 * (2 * Nat.card ↥(I ⊓ fixV A)) :=
      hVle.trans (Nat.mul_le_mul_left _ hCA)
    have h2 : Nat.card A ^ 2 * (2 * Nat.card ↥(I ⊓ fixV A)) ≤ Nat.card A * 32 := by
      calc Nat.card A ^ 2 * (2 * Nat.card ↥(I ⊓ fixV A)) =
          2 * Nat.card A * (Nat.card A * Nat.card ↥(I ⊓ fixV A)) := by ring
        _ ≤ 2 * Nat.card A * 16 := Nat.mul_le_mul_left _ hAI
        _ = Nat.card A * 32 := by ring
    have h3 := h1.trans h2
    omega
  have hidx : (K.subgroupOf X).index = 2 := by
    obtain ⟨e⟩ := hX
    have h1 := (K.subgroupOf X).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX).toEquiv, hK60,
      Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin] at h1
    have h120 : (5 : ℕ).factorial = 120 := by decide
    rw [h120] at h1
    omega
  have hJX : ∀ x ∈ X, ∀ w ∈ J, x w ∈ J := by
    intro x hx w hw
    by_cases hxK : x ∈ K
    · exact hJK x hxK w hw
    · have hxt : x * t ∈ K := by
        have h1 := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨x, hx⟩ : ↥X))
          (b := ⟨t, htX⟩)).2 (iff_of_false (by rw [Subgroup.mem_subgroupOf]; exact hxK)
            (by rw [Subgroup.mem_subgroupOf]; exact htK))
        rw [Subgroup.mem_subgroupOf] at h1
        exact h1
      have : x w = (x * t) (t w) := by
        rw [MulAut.mul_apply, ← MulAut.mul_apply (e₁ := t) (e₂ := t), ht2, MulAut.one_apply]
      rw [this]
      exact hJK _ hxt _ (htJ w hw)
  refine ⟨I, J, fun x hx w hw => hIinv ⟨x, hx⟩ w hw, hJX, hIJ, hIJ', ⟨πI, hπI⟩,
    ⟨πQ, realizesVia_complement hπQ (fun x w hw => hJX x x.2 w hw) hIJ hIJ'⟩⟩

end S5

end CFSG.Quasithin.H13
