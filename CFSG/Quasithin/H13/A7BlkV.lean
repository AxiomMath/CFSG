module

public import CFSG.Quasithin.H13.A7BlkMod

public section

namespace CFSG.Quasithin.H13.A7Blk

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Equiv Equiv.Perm
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def blockV (K : Subgroup G) : Subgroup G := ⁅blockU K, K⁆

theorem conj_mem_commutator {x : G} {H₁ H₂ : Subgroup G}
    (h₁ : x ∈ Subgroup.normalizer (H₁ : Set G)) (h₂ : x ∈ Subgroup.normalizer (H₂ : Set G))
    {v : G} (hv : v ∈ ⁅H₁, H₂⁆) : x * v * x⁻¹ ∈ ⁅H₁, H₂⁆ := by
  have hle : ∀ {H : Subgroup G}, x ∈ Subgroup.normalizer (H : Set G) →
      H.map (MulAut.conj x).toMonoidHom ≤ H := by
    intro H hH
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hH y).mp hy
  have h := Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom hv
  rw [Subgroup.map_commutator] at h
  exact Subgroup.commutator_mono (hle h₁) (hle h₂) h

variable {K : Subgroup G}

theorem blockV_le_blockU : blockV K ≤ blockU K := by
  rw [blockV, Subgroup.commutator_le]
  intro u hu k hk
  have e : ⁅u, k⁆ = u * (k * u⁻¹ * k⁻¹) := by rw [commutatorElement_def]; group
  rw [e]
  exact (blockU K).mul_mem hu (conj_mem_blockU hk ((blockU K).inv_mem hu))

theorem mem_normalizer_blockV {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer (blockV K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · exact conj_mem_commutator (C1.mem_normalizer_blockU hg) hg
  · intro hv
    have hg' := Subgroup.inv_mem _ hg
    have h := conj_mem_commutator (C1.mem_normalizer_blockU hg') hg' hv
    show v ∈ ⁅blockU K, K⁆
    simpa [mul_assoc] using h

theorem conj_mem_blockV {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) {v : G}
    (hv : v ∈ blockV K) : g * v * g⁻¹ ∈ blockV K :=
  (Subgroup.mem_normalizer_iff.mp (mem_normalizer_blockV hg) v).mp hv

theorem sum_eq_zero_of_evenWeight (x : ↥(evenWeight 7)) : ∑ i, (x : Fin 7 → ZMod 2) i = 0 := by
  have := x.2
  simpa [evenWeight] using this

theorem exists_two_avoid : ∀ a b j : Fin 7, ∃ c d : Fin 7,
    c ≠ a ∧ c ≠ b ∧ c ≠ j ∧ d ≠ a ∧ d ≠ b ∧ d ≠ j ∧ c ≠ d := by
  decide

theorem sum_single_ne (j : Fin 7) :
    ∑ i : Fin 7, (if i = j then (1 : ZMod 2) else 0) ≠ 0 := by
  fin_cases j <;> decide

theorem sum_one_ne (j : Fin 7) :
    ∑ i : Fin 7, (if i = j then (1 : ZMod 2) else 1) ≠ 0 := by
  fin_cases j <;> decide

theorem fix_stab (j : Fin 7) (x : ↥(evenWeight 7))
    (h : ∀ τ : Perm (Fin 7), Perm.sign τ = 1 → τ j = j → permWeight 7 τ x = x) :
    x = 0 ∨ x = omega j := by
  have hab : ∀ a b, a ≠ j → b ≠ j → (x : Fin 7 → ZMod 2) a = (x : Fin 7 → ZMod 2) b := by
    intro a b ha hb
    by_cases hab : a = b
    · rw [hab]
    obtain ⟨c, d, hca, hcb, hcj, hda, hdb, hdj, hcd⟩ := exists_two_avoid a b j
    have hsign : Perm.sign (swap a b * swap c d) = 1 := by
      rw [Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
      rfl
    have hτj : (swap a b * swap c d) j = j := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hcj.symm hdj.symm,
        swap_apply_of_ne_of_ne ha.symm hb.symm]
    have h1 : (permWeight 7 (swap a b * swap c d) x : Fin 7 → ZMod 2) b =
        (x : Fin 7 → ZMod 2) b := by rw [h _ hsign hτj]
    have hinv : (swap a b * swap c d)⁻¹ b = a := by
      rw [mul_inv_rev, swap_inv, swap_inv, Perm.mul_apply, swap_apply_right,
        swap_apply_of_ne_of_ne hca.symm hda.symm]
    have h2 : (permWeight 7 (swap a b * swap c d) x : Fin 7 → ZMod 2) b =
        (x : Fin 7 → ZMod 2) ((swap a b * swap c d)⁻¹ b) := rfl
    rw [h2, hinv] at h1
    exact h1
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : Fin 7, a₀ ≠ j := by
    by_cases hj : j = 0
    · exact ⟨1, by rw [hj]; decide⟩
    · exact ⟨0, fun h => hj h.symm⟩
  have hx : (x : Fin 7 → ZMod 2) = fun i => if i = j then (x : Fin 7 → ZMod 2) j
      else (x : Fin 7 → ZMod 2) a₀ := by
    funext i
    by_cases hi : i = j
    · rw [ite_eq_left hi, hi]
    · rw [ite_eq_right hi]
      exact hab i a₀ hi ha₀
  have hs := sum_eq_zero_of_evenWeight x
  rw [hx] at hs
  rcases zmod2_cases ((x : Fin 7 → ZMod 2) j) with hj | hj <;>
    rcases zmod2_cases ((x : Fin 7 → ZMod 2) a₀) with hc | hc
  · left
    apply Subtype.ext
    rw [hx, hj, hc]
    funext i
    simp
  · right
    apply Subtype.ext
    rw [hx, hj, hc]
    rfl
  · exfalso
    rw [hj, hc] at hs
    exact sum_single_ne j hs
  · exfalso
    rw [hj, hc] at hs
    exact sum_one_ne j hs

section Psi

variable (D : AltData K) (hshort : IsShort2 K) [Finite G]

theorem psi_single (j : Fin 7) : psi D hshort (Pi.single j 1) = yj D hshort j := by
  let _ := commU hshort
  unfold psi
  rw [Finset.prod_eq_single j]
  · simp
  · intro i _ hij
    rw [Pi.single_eq_of_ne hij]
    simp
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem yj_mul_yj6_mem (j : Fin 7) :
    ((yj D hshort j : G) * yj D hshort 6) ∈ blockV K := by
  have h1 := conj_yj D hshort (kj D j) 6
  rw [kj_spec] at h1
  have h2 : ⁅(yj D hshort 6 : G), (kj D j : G)⁆ = (yj D hshort j : G) * yj D hshort 6 := by
    have hsq : ((yj D hshort j : G))⁻¹ = yj D hshort j := by
      have := yj_mul_self D hshort j
      have h' := congrArg Subtype.val this
      simp only [Subgroup.coe_mul, OneMemClass.coe_one] at h'
      exact inv_eq_of_mul_eq_one_left h'
    calc ⁅(yj D hshort 6 : G), (kj D j : G)⁆
        = (yj D hshort 6 : G) * ((kj D j : G) * yj D hshort 6 * (kj D j : G)⁻¹)⁻¹ := by
          rw [commutatorElement_def]; group
      _ = (yj D hshort 6 : G) * yj D hshort j := by rw [h1, hsq]
      _ = (yj D hshort j : G) * yj D hshort 6 :=
          comm_blockU hshort (yj D hshort 6).2 (yj D hshort j).2
  rw [← h2]
  exact Subgroup.commutator_mem_commutator (yj D hshort 6).2 (kj D j).2

theorem psi_mem_blockV (f : Fin 7 → ZMod 2) (hf : ∑ i, f i = 0) :
    (psi D hshort f : G) ∈ blockV K := by
  have hdec : f = ∑ j, (if f j = 1 then (Pi.single j 1 + Pi.single 6 1 : Fin 7 → ZMod 2)
      else 0) := by
    funext i
    rw [Finset.sum_apply]
    have e : ∀ j, (if f j = 1 then (Pi.single j 1 + Pi.single 6 1 : Fin 7 → ZMod 2) else 0) i =
        f j * (Pi.single j 1 : Fin 7 → ZMod 2) i + f j * (Pi.single 6 1 : Fin 7 → ZMod 2) i := by
      intro j
      rcases zmod2_cases (f j) with h | h <;> simp [h]
    simp only [e, Finset.sum_add_distrib]
    have h1 : ∑ j, f j * (Pi.single j 1 : Fin 7 → ZMod 2) i = f i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        rw [Pi.single_eq_of_ne' hji]
        simp
      · intro h
        exact absurd (Finset.mem_univ i) h
    have h2 : ∑ j, f j * (Pi.single 6 1 : Fin 7 → ZMod 2) i = 0 := by
      rw [← Finset.sum_mul, hf, zero_mul]
    rw [h1, h2, add_zero]
  have hsum : ∀ s : Finset (Fin 7), (psi D hshort (∑ j ∈ s,
      (if f j = 1 then (Pi.single j 1 + Pi.single 6 1 : Fin 7 → ZMod 2) else 0)) : G) ∈
        blockV K := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, psi_zero]
      exact (blockV K).one_mem
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, psi_add, Subgroup.coe_mul]
      refine (blockV K).mul_mem ?_ ih
      split_ifs
      · rw [psi_add, psi_single, psi_single, Subgroup.coe_mul]
        exact yj_mul_yj6_mem D hshort a
      · rw [psi_zero]
        exact (blockV K).one_mem
  rw [hdec]
  exact hsum Finset.univ

theorem exists_psi_of_mem_blockV {v : G} (hv : v ∈ blockV K) :
    ∃ f : Fin 7 → ZMod 2, ∑ i, f i = 0 ∧ (psi D hshort f : G) = v := by
  let W : Subgroup G :=
    { carrier := {v | ∃ f : Fin 7 → ZMod 2, ∑ i, f i = 0 ∧ (psi D hshort f : G) = v}
      one_mem' := ⟨0, by simp, by rw [psi_zero]; rfl⟩
      mul_mem' := by
        rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
        refine ⟨f + g, ?_, ?_⟩
        · simp only [Pi.add_apply, Finset.sum_add_distrib, hf, hg, add_zero]
        · rw [psi_add, Subgroup.coe_mul]
      inv_mem' := by
        rintro _ ⟨f, hf, rfl⟩
        refine ⟨f, hf, ?_⟩
        have h := psi_mul_self D hshort f
        have h' := congrArg Subtype.val h
        simp only [Subgroup.coe_mul, OneMemClass.coe_one] at h'
        exact (inv_eq_of_mul_eq_one_left h').symm }
  have hle : blockV K ≤ W := by
    rw [blockV, Subgroup.commutator_le]
    intro u hu k hk
    set f₀ : Fin 7 → ZMod 2 :=
      ((Multiplicative.toAdd (D.β ⟨u, hu⟩) : ↥(evenWeight 7)) : Fin 7 → ZMod 2) with hf₀
    have hf₀e : ∑ i, f₀ i = 0 := sum_eq_zero_of_evenWeight _
    set σ : Perm (Fin 7) := (D.α ⟨k, hk⟩ : Perm (Fin 7)) with hσ
    set p : G := (psi D hshort f₀ : G) with hp
    have hz : p⁻¹ * u ∈ blockZ K := by
      have hU : p⁻¹ * u ∈ blockU K := (blockU K).mul_mem ((blockU K).inv_mem (psi D hshort f₀).2) hu
      have hker : (⟨p⁻¹ * u, hU⟩ : ↥(blockU K)) ∈ D.β.ker := by
        rw [MonoidHom.mem_ker]
        have e : (⟨p⁻¹ * u, hU⟩ : ↥(blockU K)) = (psi D hshort f₀)⁻¹ * ⟨u, hu⟩ := rfl
        rw [e, map_mul, map_inv]
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        rw [toAdd_mul, toAdd_inv, toAdd_one, AddSubgroup.coe_add, AddSubgroup.coe_neg,
          β_psi D hshort f₀ hf₀e]
        simp [hf₀]
      rw [D.βker] at hker
      exact hker
    have hzk : k * (p⁻¹ * u) = (p⁻¹ * u) * k := comm_blockZ hz hk
    have hq : k * p * k⁻¹ = (psi D hshort (fun i => f₀ (σ⁻¹ i)) : G) := by
      have h := congrArg Subtype.val (conj_psi D hshort ⟨k, hk⟩ f₀)
      rw [coe_conjU] at h
      exact h
    have hq2 : ((psi D hshort (fun i => f₀ (σ⁻¹ i)) : G))⁻¹ =
        (psi D hshort (fun i => f₀ (σ⁻¹ i)) : G) := by
      have h := psi_mul_self D hshort (fun i => f₀ (σ⁻¹ i))
      have h' := congrArg Subtype.val h
      simp only [Subgroup.coe_mul, OneMemClass.coe_one] at h'
      exact inv_eq_of_mul_eq_one_left h'
    refine ⟨f₀ + fun i => f₀ (σ⁻¹ i), ?_, ?_⟩
    · simp only [Pi.add_apply, Finset.sum_add_distrib, hf₀e, zero_add]
      rw [Equiv.sum_comp σ⁻¹ f₀, hf₀e]
    · rw [psi_add, Subgroup.coe_mul, ← hq2, ← hq]
      have e : u = p * (p⁻¹ * u) := by group
      calc p * (k * p * k⁻¹)⁻¹ = p * (p⁻¹ * u) * (k * (p⁻¹ * u)⁻¹ * k⁻¹) * (k * p * k⁻¹)⁻¹ := by
            have : k * (p⁻¹ * u)⁻¹ * k⁻¹ = (p⁻¹ * u)⁻¹ := by
              calc k * (p⁻¹ * u)⁻¹ * k⁻¹ = (k * (p⁻¹ * u) * k⁻¹)⁻¹ := by group
                _ = (p⁻¹ * u)⁻¹ := by rw [hzk, mul_inv_cancel_right]
            rw [this]
            group
        _ = ⁅u, k⁆ := by rw [commutatorElement_def]; group
  exact hle hv

@[expose] noncomputable def theta : ↥(blockV K) ≃* Multiplicative ↥(evenWeight 7) where
  toFun v := D.β ⟨v, blockV_le_blockU v.2⟩
  invFun x := ⟨psi D hshort ((Multiplicative.toAdd x : ↥(evenWeight 7)) : Fin 7 → ZMod 2),
    psi_mem_blockV D hshort _ (sum_eq_zero_of_evenWeight _)⟩
  left_inv v := by
    obtain ⟨f, hf, hv⟩ := exists_psi_of_mem_blockV D hshort v.2
    apply Subtype.ext
    have e : (⟨v, blockV_le_blockU v.2⟩ : ↥(blockU K)) = psi D hshort f := Subtype.ext hv.symm
    show (psi D hshort ((Multiplicative.toAdd (D.β ⟨v, blockV_le_blockU v.2⟩) :
      ↥(evenWeight 7)) : Fin 7 → ZMod 2) : G) = v
    rw [e, β_psi D hshort f hf]
    exact hv
  right_inv x := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact β_psi D hshort _ (sum_eq_zero_of_evenWeight _)
  map_mul' a b := by
    show D.β ⟨(a * b : ↥(blockV K)), _⟩ = D.β ⟨a, _⟩ * D.β ⟨b, _⟩
    rw [← map_mul]
    rfl

theorem theta_apply (v : ↥(blockV K)) :
    theta D hshort v = D.β ⟨v, blockV_le_blockU v.2⟩ := rfl

theorem coe_theta_symm_apply (x : Multiplicative ↥(evenWeight 7)) :
    (((theta D hshort).symm x : ↥(blockV K)) : G) =
      psi D hshort ((Multiplicative.toAdd x : ↥(evenWeight 7)) : Fin 7 → ZMod 2) := rfl

@[expose] def pwHom (σ : Perm (Fin 7)) : ↥(evenWeight 7) →+ ↥(evenWeight 7) where
  toFun := permWeight 7 σ
  map_zero' := rfl
  map_add' _ _ := rfl

omit [Finite G] in
theorem omega_ne_zero (j : Fin 7) : omega j ≠ 0 := by
  intro h
  obtain ⟨a, ha⟩ : ∃ a : Fin 7, a ≠ j := by
    by_cases hj : j = 0
    · exact ⟨1, by rw [hj]; decide⟩
    · exact ⟨0, fun h => hj h.symm⟩
  have h1 := congrArg (fun y : ↥(evenWeight 7) => (y : Fin 7 → ZMod 2) a) h
  simp only [omega, ite_eq_right ha] at h1
  exact one_ne_zero h1

theorem β_conjU_yj (g : ↥(Subgroup.normalizer (K : Set G))) (j : Fin 7) :
    Multiplicative.toAdd (D.β (conjU g (yj D hshort j))) = omega (D.act g j) := by
  set σ := D.act g with hσ
  set w := conjU g (yj D hshort j) with hw
  have hfix : ∀ τ : Perm (Fin 7), Perm.sign τ = 1 → τ (σ j) = σ j →
      permWeight 7 τ (Multiplicative.toAdd (D.β w)) = Multiplicative.toAdd (D.β w) := by
    intro τ hτ hτj
    obtain ⟨h, hh⟩ := D.surj ⟨τ, Perm.mem_alternatingGroup.mpr hτ⟩
    set h' : ↥K := conjAct K g⁻¹ h with hh'
    have hh'c : (h' : G) = (g : G)⁻¹ * h * g := by
      rw [hh', Setup.coe_conjAct_apply]
      simp
    have hα' : (D.α h' : Perm (Fin 7)) j = j := by
      have hs := permAct_spec D.α D.surj D.ker (by norm_num) (by norm_num) g⁻¹ h
      rw [← hh'] at hs
      rw [hs, map_inv, inv_inv]
      show σ⁻¹ ((D.α h : Perm (Fin 7)) (σ j)) = j
      rw [hh]
      show σ⁻¹ (τ (σ j)) = j
      rw [hτj, Perm.inv_def, Equiv.symm_apply_apply]
    have h1 : (h' : G) * yj D hshort j * (h' : G)⁻¹ = yj D hshort j := by
      rw [conj_yj D hshort h' j, hα']
    have h2 : (w : G) = (h : G) * w * (h : G)⁻¹ := by
      have e : (h : G) = g * h' * (g : G)⁻¹ := by rw [hh'c]; group
      rw [hw, coe_conjU, e]
      calc (g : G) * yj D hshort j * (g : G)⁻¹ =
          g * ((h' : G) * yj D hshort j * (h' : G)⁻¹) * (g : G)⁻¹ := by rw [h1]
        _ = _ := by group
    have h3 := D.βeq h w w h2
    rw [hh] at h3
    exact h3.symm
  rcases fix_stab (σ j) _ hfix with h0 | h0
  · exfalso
    have hker : w ∈ D.β.ker := by
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      rw [h0]
      rfl
    rw [D.βker, Subgroup.mem_subgroupOf] at hker
    have hZ : (g : G)⁻¹ * w * (g : G)⁻¹⁻¹ ∈ blockZ K :=
      (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockZ (Subgroup.inv_mem _ g.2)) _).mp
        hker
    have hy : (g : G)⁻¹ * w * (g : G)⁻¹⁻¹ = yj D hshort j := by
      rw [hw, coe_conjU]
      group
    rw [hy] at hZ
    have hker2 : yj D hshort j ∈ D.β.ker := by
      rw [D.βker, Subgroup.mem_subgroupOf]
      exact hZ
    rw [MonoidHom.mem_ker] at hker2
    have h5 := β_yj D hshort j
    rw [hker2] at h5
    exact omega_ne_zero j h5.symm
  · exact h0

theorem β_conjU_psi (g : ↥(Subgroup.normalizer (K : Set G))) (f : Fin 7 → ZMod 2) :
    Multiplicative.toAdd (D.β (conjU g (psi D hshort f))) =
      permWeight 7 (D.act g) (Multiplicative.toAdd (D.β (psi D hshort f))) := by
  let _ := commU hshort
  unfold psi
  rw [map_prod (conjU g), map_prod D.β, map_prod D.β, toAdd_prod, toAdd_prod]
  show _ = pwHom (D.act g) _
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rw [β_conjU_yj, β_yj]
    exact (permWeight_omega _ j).symm
  · rw [map_one, map_one, toAdd_one, map_zero]

theorem theta_conj (g : ↥(Subgroup.normalizer (K : Set G))) (v : ↥(blockV K)) :
    Multiplicative.toAdd (theta D hshort ⟨g * v * (g : G)⁻¹, conj_mem_blockV g.2 v.2⟩) =
      permWeight 7 (D.act g) (Multiplicative.toAdd (theta D hshort v)) := by
  obtain ⟨f, hf, hv⟩ := exists_psi_of_mem_blockV D hshort v.2
  have e1 : (⟨v, blockV_le_blockU v.2⟩ : ↥(blockU K)) = psi D hshort f := Subtype.ext hv.symm
  have e2 : (⟨g * v * (g : G)⁻¹, blockV_le_blockU (conj_mem_blockV g.2 v.2)⟩ : ↥(blockU K)) =
      conjU g (psi D hshort f) := by
    apply Subtype.ext
    rw [coe_conjU, hv]
  rw [theta_apply, theta_apply, e1, e2]
  exact β_conjU_psi D hshort g f

end Psi

end CFSG.Quasithin.H13.A7Blk

end
