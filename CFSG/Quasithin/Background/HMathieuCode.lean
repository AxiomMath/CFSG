module

public import CFSG.Quasithin.Background.HMathieuStd

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code

@[expose] def κC : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 11 → ZMod 2) where
  toFun x j := ψ x (emb11 j) + if (j : ℕ) < 5 then ψ x 5 else 0
  map_add' x y := by
    funext j
    simp only [map_add, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c x := by
    funext j
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem κC_apply (x : Fin 24 → ZMod 2) (j : Fin 11) :
    κC x j = ψ x (emb11 j) + if (j : ℕ) < 5 then ψ x 5 else 0 := rfl

@[expose] def code12 (w : Fin 11 → ZMod 2) (i : Fin 12) : ZMod 2 :=
  if h : (i : ℕ) < 5 then w ⟨i, by omega⟩ else if h' : (i : ℕ) = 5 then 0 else w ⟨i - 1, by omega⟩

@[expose] def liftC : (Fin 11 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) where
  toFun w := ∑ i, code12 w i • B i
  map_add' w w' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← add_smul]
    congr 1
    unfold code12
    split_ifs <;> simp
  map_smul' c w := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul]
    congr 1
    unfold code12
    split_ifs <;> simp

theorem liftC_apply (w : Fin 11 → ZMod 2) : liftC w = ∑ i, code12 w i • B i := rfl

theorem ψ_liftC (w : Fin 11 → ZMod 2) : ψ (liftC w) = code12 w := ψ_comb _

theorem code12_emb (w : Fin 11 → ZMod 2) (j : Fin 11) : code12 w (emb11 j) = w j := by
  unfold code12 emb11
  by_cases hj : (j : ℕ) < 5
  · simp [hj]
  · have h1 : ¬ ((j : ℕ) + 1 < 5) := by omega
    have h2 : ¬ ((j : ℕ) + 1 = 5) := by omega
    simp only [hj, dite_false, h1, h2]
    congr 1

theorem κC_liftC (w : Fin 11 → ZMod 2) : κC (liftC w) = w := by
  funext j
  rw [κC_apply, ψ_liftC, code12_emb]
  have : code12 w 5 = 0 := by simp [code12]
  rw [this]
  simp

theorem liftC_mem (w : Fin 11 → ZMod 2) : liftC w ∈ C := by
  rw [liftC_apply]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (B_mem_C i)

theorem ψ_Ω : ψ Ω = fun i : Fin 12 => if (i : ℕ) < 6 then (1 : ZMod 2) else 0 := by decide

theorem emb11_surj : ∀ i : Fin 12, i ≠ 5 → ∃ j, emb11 j = i := by decide

theorem κC_Ω : κC Ω = 0 := by
  funext j
  rw [κC_apply, ψ_Ω]
  unfold emb11
  by_cases hj : (j : ℕ) < 5
  · simp [hj, show (j : ℕ) < 6 by omega]
    decide
  · simp [hj, show ¬ ((j : ℕ) + 1 < 6) by omega]

theorem κC_eq_zero_iff {x : Fin 24 → ZMod 2} (hx : x ∈ C) : κC x = 0 ↔ x = 0 ∨ x = Ω := by
  constructor
  · intro h
    have hj : ∀ j : Fin 11, ψ x (emb11 j) = if (j : ℕ) < 5 then ψ x 5 else 0 := by
      intro j
      have := congrFun h j
      rw [κC_apply, Pi.zero_apply] at this
      exact zmod2_eq_of_add this
    rcases zmod2_cases (ψ x 5) with h5 | h5
    · left
      refine eq_zero_of_mem_C_of_ψ_eq_zero hx (funext fun i => ?_)
      by_cases hi : (i : ℕ) = 5
      · rw [show i = 5 from Fin.ext hi, h5]
        rfl
      · obtain ⟨j, rfl⟩ := emb11_surj i fun h => hi (by rw [h]; rfl)
        rw [hj, h5]
        split_ifs <;> rfl
    · right
      have hΩC : Ω ∈ C := Ω_mem_C
      have hsub : x - Ω = 0 := by
        refine eq_zero_of_mem_C_of_ψ_eq_zero (C.sub_mem hx hΩC) (funext fun i => ?_)
        rw [map_sub, Pi.sub_apply, ψ_Ω, Pi.zero_apply]
        by_cases hi : (i : ℕ) = 5
        · rw [show i = 5 from Fin.ext hi, h5]
          decide
        · obtain ⟨j, rfl⟩ := emb11_surj i fun h => hi (by rw [h]; rfl)
          rw [hj, h5]
          revert j
          decide
      exact sub_eq_zero.1 hsub
  · rintro (rfl | rfl)
    · exact map_zero κC
    · exact κC_Ω

theorem mem_zpowers_of_sq {G : Type*} [CommGroup G] {p : G} (hp : p * p = 1) (m : G) :
    m ∈ Subgroup.zpowers p ↔ m = 1 ∨ m = p := by
  have h := mem_sup_zpowers_iff (A := ⊥) hp m
  rw [bot_sup_eq, Subgroup.mem_bot, Subgroup.mem_bot] at h
  rw [h]
  refine or_congr_right ⟨fun h1 => ?_, fun h1 => by rw [h1, hp]⟩
  calc m = m * p * p := by rw [mul_assoc, hp, mul_one]
    _ = p := by rw [h1, one_mul]

theorem allOnes_sq : G6.allOnes 24 * G6.allOnes 24 = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [G6.allOnes, toAdd_mul, toAdd_ofAdd, toAdd_one, Pi.add_apply, Pi.zero_apply]
  decide

theorem mem_zpowers_allOnes (m : G6.PermMod 24) :
    m ∈ Subgroup.zpowers (G6.allOnes 24) ↔ Multiplicative.toAdd m = 0 ∨
      Multiplicative.toAdd m = Ω := by
  refine (mem_zpowers_of_sq allOnes_sq m).trans (or_congr ?_ ?_)
  · exact ⟨fun h => by rw [h]; rfl, fun h => Multiplicative.toAdd.injective h⟩
  · exact ⟨fun h => by rw [h]; rfl, fun h => Multiplicative.toAdd.injective h⟩

@[expose] def codeCoords :
    SecCoords golayC (Subgroup.zpowers (G6.allOnes 24)) (Multiplicative (Fin 11 → ZMod 2)) where
  κ := AddMonoidHom.toMultiplicative κC.toAddMonoidHom
  lift := AddMonoidHom.toMultiplicative liftC.toAddMonoidHom
  lift_mem w := liftC_mem (Multiplicative.toAdd w)
  κ_lift w := by
    change Multiplicative.ofAdd (κC (liftC (Multiplicative.toAdd w))) = w
    rw [κC_liftC]
    rfl
  ker_iff m hm := by
    change Multiplicative.ofAdd (κC (Multiplicative.toAdd m)) = 1 ↔ _
    rw [mem_zpowers_allOnes, ← κC_eq_zero_iff ((mem_golayC_iff m).1 hm)]
    exact ⟨fun h => congrArg Multiplicative.toAdd h, fun h => congrArg Multiplicative.ofAdd h⟩

theorem permAct_allOnes (σ : Equiv.Perm (Fin 24)) : G6.permAct 24 σ (G6.allOnes 24) = G6.allOnes 24 :=
  rfl

theorem permAct_mem_zpowers_allOnes (σ : Equiv.Perm (Fin 24)) {m : G6.PermMod 24}
    (hm : m ∈ Subgroup.zpowers (G6.allOnes 24)) :
    G6.permAct 24 σ m ∈ Subgroup.zpowers (G6.allOnes 24) := by
  rcases (mem_zpowers_of_sq (G := G6.PermMod 24) allOnes_sq m).1 hm with rfl | rfl
  · rw [map_one]
    exact Subgroup.one_mem _
  · rw [permAct_allOnes]
    exact Subgroup.mem_zpowers _

theorem preserves_code {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ AutPerm) :
    Preserves golayC (Subgroup.zpowers (G6.allOnes 24)) σ :=
  ⟨(preserves_cocode hσ).2, fun _ hm => permAct_mem_zpowers_allOnes σ hm⟩

@[expose] noncomputable def rhoC11 (Γ : Subgroup (Equiv.Perm (Fin 24))) (hΓ : Γ ≤ AutPerm) :
    ↥Γ →* MulAut W11 :=
  codeCoords.rho Γ fun _ hσ => preserves_code (hΓ hσ)

theorem code24_std {V : Type*} [CommGroup V] {L : Subgroup (MulAut V)}
    (h : MathieuCode24 L ⊤ ⊥) :
    ∃ e : V ≃* W11, L.map (congrHom e) = (rhoC11 AutPerm le_rfl).range :=
  codeCoords.exists_map_eq _ h

theorem zpowers_allOnes_iff (τ : Equiv.Perm (Fin 24)) (m : G6.PermMod 24) :
    m ∈ Subgroup.zpowers (G6.allOnes 24) ↔
      G6.permAct 24 τ⁻¹ m ∈ Subgroup.zpowers (G6.allOnes 24) := by
  refine ⟨permAct_mem_zpowers_allOnes τ⁻¹, fun h => ?_⟩
  have := permAct_mem_zpowers_allOnes τ h
  rwa [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] at this

theorem code23_std
    {V : Type*} [CommGroup V] {L : Subgroup (MulAut V)}
    (h : MathieuCode23 L ⊤ ⊥) :
    ∃ e : V ≃* W11, L.map (congrHom e) = (rhoC11 mog23 inf_le_left).range := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨τ, hτ, hτ0, -⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two x (x + 1) (by
    intro h
    have := congrArg Fin.val h
    simp [Fin.val_add] at this
    omega)
  have hn := (preserves_iff_of_mem hτ).2
  have hd := zpowers_allOnes_iff τ
  have hΓx : ∀ σ ∈ AutPerm ⊓ stab x, Preserves golayC (Subgroup.zpowers (G6.allOnes 24)) σ :=
    fun _ hσ => preserves_code hσ.1
  obtain ⟨e, he⟩ := (codeCoords.conj τ hn hd).exists_map_eq hΓx hx
  refine ⟨e, he.trans ?_⟩
  refine codeCoords.range_rho_conj τ hn hd _ hΓx fun σ => ?_
  have hτ0' : τ⁻¹ x = 0 := by rw [← hτ0, ← Equiv.Perm.mul_apply, inv_mul_cancel]; rfl
  simp only [Subgroup.mem_inf, mem_stab_iff, Equiv.Perm.mul_apply, hτ0]
  constructor
  · rintro ⟨hσ, hσx⟩
    refine ⟨AutPerm.mul_mem (AutPerm.mul_mem (AutPerm.inv_mem hτ) hσ) hτ, ?_⟩
    rw [hσx, hτ0']
  · rintro ⟨hσ, hσx⟩
    refine ⟨?_, ?_⟩
    · have := AutPerm.mul_mem (AutPerm.mul_mem hτ hσ) (AutPerm.inv_mem hτ)
      simpa [mul_assoc] using this
    · have := congrArg τ hσx
      simpa [hτ0] using this

theorem mem_pairKer (x y : Fin 24) (m : G6.PermMod 24) :
    m ∈ pairKer x y ↔ Multiplicative.toAdd m x + Multiplicative.toAdd m y = 0 := Iff.rfl

@[expose] def f22 (j : Fin 11) : ZMod 2 := B (emb11 j) 0 + B (emb11 j) 1

theorem f22_zero : f22 0 = 1 := by decide

theorem emb11_eq_succAbove : ∀ j : Fin 11, emb11 j = Fin.succAbove 5 j := by decide

theorem liftC_pair (u : Fin 11 → ZMod 2) : liftC u 0 + liftC u 1 = ∑ j, u j * f22 j := by
  simp only [liftC_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_add_distrib, Fin.sum_univ_succAbove _ 5]
  have h5 : code12 u 5 = 0 := by simp [code12]
  rw [h5, zero_mul, zero_mul, add_zero, zero_add]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← emb11_eq_succAbove, code12_emb, f22, mul_add]

@[expose] def κC22 : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 10 → ZMod 2) where
  toFun x j := κC x j.succ
  map_add' x y := by
    funext j
    simp
  map_smul' c x := by
    funext j
    simp

@[expose] def c22 (w : Fin 10 → ZMod 2) : ZMod 2 := ∑ j, w j * f22 j.succ

theorem c22_add (w w' : Fin 10 → ZMod 2) : c22 (w + w') = c22 w + c22 w' := by
  simp only [c22, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem c22_smul (c : ZMod 2) (w : Fin 10 → ZMod 2) : c22 (c • w) = c * c22 w := by
  simp only [c22, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

@[expose] def cons22 : (Fin 10 → ZMod 2) →ₗ[ZMod 2] (Fin 11 → ZMod 2) where
  toFun w := Fin.cons (c22 w) w
  map_add' w w' := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, Pi.add_apply, c22_add]
    · simp only [Fin.cons_succ, Pi.add_apply]
  map_smul' c w := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, Pi.smul_apply, smul_eq_mul, c22_smul, RingHom.id_apply]
    · simp only [Fin.cons_succ, Pi.smul_apply, RingHom.id_apply]

theorem cons22_apply (w : Fin 10 → ZMod 2) : cons22 w = Fin.cons (c22 w) w := rfl

@[expose] def lift22 : (Fin 10 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) := liftC.comp cons22

theorem lift22_apply (w : Fin 10 → ZMod 2) : lift22 w = liftC (Fin.cons (c22 w) w) := rfl

theorem lift22_mem (w : Fin 10 → ZMod 2) : lift22 w ∈ C := by
  rw [lift22_apply]
  exact liftC_mem _

theorem lift22_pair (w : Fin 10 → ZMod 2) : lift22 w 0 + lift22 w 1 = 0 := by
  rw [lift22_apply, liftC_pair, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, f22_zero, mul_one]
  exact CharTwo.add_self_eq_zero _

theorem κC22_lift22 (w : Fin 10 → ZMod 2) : κC22 (lift22 w) = w := by
  funext j
  change κC (lift22 w) j.succ = w j
  rw [lift22_apply, κC_liftC, Fin.cons_succ]

theorem κC22_eq_zero_iff {x : Fin 24 → ZMod 2} (hx : x ∈ C) (hx01 : x 0 + x 1 = 0) :
    κC22 x = 0 ↔ x = 0 ∨ x = Ω := by
  rw [← κC_eq_zero_iff hx]
  constructor
  · intro h
    set u := κC x with hu
    have hus : ∀ j : Fin 10, u j.succ = 0 := fun j => congrFun h j
    have hd : x - liftC u ∈ C := C.sub_mem hx (liftC_mem u)
    have hκ : κC (x - liftC u) = 0 := by rw [map_sub, κC_liftC, hu]; exact sub_self _
    have hpair : (x - liftC u) 0 + (x - liftC u) 1 = 0 := by
      rcases (κC_eq_zero_iff hd).1 hκ with h0 | h0
      · rw [h0]
        simp
      · rw [h0]
        decide
    have h0 : u 0 = 0 := by
      have h1 := liftC_pair u
      rw [Fin.sum_univ_succ] at h1
      simp only [hus, zero_mul, Finset.sum_const_zero, add_zero, f22_zero, mul_one] at h1
      have h2 : liftC u 0 + liftC u 1 = x 0 + x 1 - ((x - liftC u) 0 + (x - liftC u) 1) := by
        simp only [Pi.sub_apply]
        ring
      rw [hx01, hpair] at h2
      simp only [sub_self] at h2
      rw [← h1, h2]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact h0
    · exact hus j
  · intro h
    funext j
    change κC x j.succ = 0
    rw [h]
    rfl

theorem mem_code22 (m : G6.PermMod 24) :
    m ∈ golayC ⊓ pairKer 0 1 ↔ Multiplicative.toAdd m ∈ C ∧
      Multiplicative.toAdd m 0 + Multiplicative.toAdd m 1 = 0 := Iff.rfl

@[expose] def code22Coords :
    SecCoords (golayC ⊓ pairKer 0 1) (Subgroup.zpowers (G6.allOnes 24)) W10 where
  κ := AddMonoidHom.toMultiplicative κC22.toAddMonoidHom
  lift := AddMonoidHom.toMultiplicative lift22.toAddMonoidHom
  lift_mem w := (mem_code22 _).2 ⟨lift22_mem _, lift22_pair _⟩
  κ_lift w := by
    change Multiplicative.ofAdd (κC22 (lift22 (Multiplicative.toAdd w))) = w
    rw [κC22_lift22]
    rfl
  ker_iff m hm := by
    change Multiplicative.ofAdd (κC22 (Multiplicative.toAdd m)) = 1 ↔ _
    rw [mem_zpowers_allOnes, ← κC22_eq_zero_iff ((mem_code22 m).1 hm).1 ((mem_code22 m).1 hm).2]
    exact ⟨fun h => congrArg Multiplicative.toAdd h, fun h => congrArg Multiplicative.ofAdd h⟩

theorem preserves_code22 {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ mog22plus) :
    Preserves (golayC ⊓ pairKer 0 1) (Subgroup.zpowers (G6.allOnes 24)) σ := by
  refine ⟨fun m hm => ?_, fun _ hm => permAct_mem_zpowers_allOnes σ hm⟩
  obtain ⟨hmC, hm01⟩ := (mem_code22 m).1 hm
  refine (mem_code22 _).2 ⟨(preserves_cocode hσ.1).2 m hmC, ?_⟩
  rw [toAdd_permAct]
  simp only [permWord, Function.comp_apply]
  have hσi : σ⁻¹ ∈ mog22plus := mog22plus.inv_mem hσ
  rcases hσi.2 with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [h0, h1]
    exact hm01
  · rw [h0, h1, add_comm]
    exact hm01

@[expose] noncomputable def rhoC10 (Γ : Subgroup (Equiv.Perm (Fin 24))) (hΓ : Γ ≤ mog22plus) :
    ↥Γ →* MulAut W10 :=
  code22Coords.rho Γ fun _ hσ => preserves_code22 (hΓ hσ)

theorem code22_std
    {V : Type*} [CommGroup V] {L : Subgroup (MulAut V)}
    (h : MathieuCode22 L ⊤ ⊥) :
    ∃ e : V ≃* W10, L.map (congrHom e) = (rhoC10 mog22 mog22_le_mog22plus).range := by
  obtain ⟨x, y, hxy, hr⟩ := h
  obtain ⟨τ, hτ, hτ0, hτ1⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two x y hxy
  have hC := (preserves_iff_of_mem hτ).2
  have hn : ∀ m, m ∈ golayC ⊓ pairKer x y ↔ G6.permAct 24 τ⁻¹ m ∈ golayC ⊓ pairKer 0 1 := by
    intro m
    rw [mem_code22, Subgroup.mem_inf, mem_pairKer, hC m]
    refine and_congr Iff.rfl ?_
    rw [toAdd_permAct]
    simp only [permWord, Function.comp_apply, inv_inv, hτ0, hτ1]
  have hd := zpowers_allOnes_iff τ
  have hΓxy : ∀ σ ∈ AutPerm ⊓ stab x ⊓ stab y,
      Preserves (golayC ⊓ pairKer x y) (Subgroup.zpowers (G6.allOnes 24)) σ := by
    intro σ hσ
    have hσx : σ x = x := (mem_stab_iff x σ).1 hσ.1.2
    have hσy : σ y = y := (mem_stab_iff y σ).1 hσ.2
    refine ⟨fun m hm => ?_, fun _ hm => permAct_mem_zpowers_allOnes σ hm⟩
    obtain ⟨hmC, hmxy⟩ := hm
    refine ⟨(preserves_cocode hσ.1.1).2 m hmC, (mem_pairKer x y _).2 ?_⟩
    rw [toAdd_permAct]
    simp only [permWord, Function.comp_apply]
    have hx' : σ⁻¹ x = x := by rw [Equiv.Perm.inv_eq_iff_eq]; exact hσx.symm
    have hy' : σ⁻¹ y = y := by rw [Equiv.Perm.inv_eq_iff_eq]; exact hσy.symm
    rw [hx', hy']
    exact hmxy
  obtain ⟨e, he⟩ := (code22Coords.conj τ hn hd).exists_map_eq hΓxy hr
  refine ⟨e, he.trans ?_⟩
  refine code22Coords.range_rho_conj τ hn hd _ hΓxy fun σ => ?_
  have hτ0' : τ⁻¹ x = 0 := by rw [← hτ0]; simp
  have hτ1' : τ⁻¹ y = 1 := by rw [← hτ1]; simp
  simp only [Subgroup.mem_inf, mem_stab_iff, Equiv.Perm.mul_apply, hτ0, hτ1]
  constructor
  · rintro ⟨⟨hσ, hσx⟩, hσy⟩
    refine ⟨⟨AutPerm.mul_mem (AutPerm.mul_mem (AutPerm.inv_mem hτ) hσ) hτ, ?_⟩, ?_⟩
    · rw [hσx, hτ0']
    · rw [hσy, hτ1']
  · rintro ⟨⟨hσ, hσx⟩, hσy⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have := AutPerm.mul_mem (AutPerm.mul_mem hτ hσ) (AutPerm.inv_mem hτ)
      simpa [mul_assoc] using this
    · have := congrArg τ hσx
      simpa [hτ0] using this
    · have := congrArg τ hσy
      simpa [hτ1] using this

end CFSG.Quasithin.H.Mathieu
