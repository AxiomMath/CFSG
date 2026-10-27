module

public import CFSG.Quasithin.Background.HMathieuCoord
public import CFSG.Monster.B.TwoA.Base.PairStab

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code

abbrev W11 : Type := Multiplicative (Fin 11 → ZMod 2)

abbrev W10 : Type := Multiplicative (Fin 10 → ZMod 2)

abbrev mog23 : Subgroup (Equiv.Perm (Fin 24)) := AutPerm ⊓ stab 0

abbrev mog22 : Subgroup (Equiv.Perm (Fin 24)) := AutPerm ⊓ stab 0 ⊓ stab 1

@[expose] noncomputable def rho11 (Γ : Subgroup (Equiv.Perm (Fin 24))) (hΓ : Γ ≤ AutPerm) :
    ↥Γ →* MulAut W11 :=
  cocodeCoords.rho Γ fun _ hσ => preserves_cocode (hΓ hσ)

theorem mem_stab_iff (x : Fin 24) (σ : Equiv.Perm (Fin 24)) : σ ∈ stab x ↔ σ x = x :=
  MulAction.mem_stabilizer_iff

theorem preserves_iff_of_mem {τ : Equiv.Perm (Fin 24)} (hτ : τ ∈ AutPerm) :
    (∀ m, m ∈ G6.coreMod 24 ↔ G6.permAct 24 τ⁻¹ m ∈ G6.coreMod 24) ∧
      (∀ m, m ∈ golayC ↔ G6.permAct 24 τ⁻¹ m ∈ golayC) := by
  have h1 := preserves_cocode hτ
  have h2 := preserves_cocode (AutPerm.inv_mem hτ)
  have hback : ∀ m, G6.permAct 24 τ (G6.permAct 24 τ⁻¹ m) = m := by
    intro m
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  refine ⟨fun m => ⟨h2.1 m, fun h => ?_⟩, fun m => ⟨h2.2 m, fun h => ?_⟩⟩
  · rw [← hback m]
    exact h1.1 _ h
  · rw [← hback m]
    exact h1.2 _ h

theorem cocode24_std {V : Type*} [CommGroup V] {L : Subgroup (MulAut V)}
    (h : MathieuCocode24 L ⊤ ⊥) :
    ∃ e : V ≃* W11, L.map (congrHom e) = (rho11 AutPerm le_rfl).range :=
  cocodeCoords.exists_map_eq _ h

theorem cocode23_std
    {V : Type*} [CommGroup V] {L : Subgroup (MulAut V)}
    (h : MathieuCocode23 L ⊤ ⊥) :
    ∃ e : V ≃* W11, L.map (congrHom e) = (rho11 mog23 inf_le_left).range := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨τ, hτ, hτ0, -⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two x (x + 1) (by
    intro h
    have := congrArg Fin.val h
    simp [Fin.val_add] at this
    omega)
  obtain ⟨hn, hd⟩ := preserves_iff_of_mem hτ
  have hΓx : ∀ σ ∈ AutPerm ⊓ stab x, Preserves (G6.coreMod 24) golayC σ :=
    fun _ hσ => preserves_cocode hσ.1
  obtain ⟨e, he⟩ := (cocodeCoords.conj τ hn hd).exists_map_eq hΓx hx
  refine ⟨e, he.trans ?_⟩
  refine cocodeCoords.range_rho_conj τ hn hd _ hΓx fun σ => ?_
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

theorem toAdd_unitVec (x : Fin 24) : Multiplicative.toAdd (unitVec x) = Pi.single x 1 := rfl

theorem permAct_unitVec (σ : Equiv.Perm (Fin 24)) (x : Fin 24) :
    G6.permAct 24 σ (unitVec x) = unitVec (σ x) := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_permAct, toAdd_unitVec, toAdd_unitVec]
  funext i
  simp only [permWord, Function.comp_apply, Pi.single_apply]
  congr 1
  exact propext ⟨fun h => by rw [← h]; simp, fun h => by rw [h]; simp⟩

theorem permAct_pairVec (σ : Equiv.Perm (Fin 24)) (x y : Fin 24) :
    G6.permAct 24 σ (pairVec x y) = pairVec (σ x) (σ y) := by
  rw [pairVec, map_mul, permAct_unitVec, permAct_unitVec, pairVec]

theorem pairVec_sq (x y : Fin 24) : pairVec x y * pairVec x y = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [toAdd_mul, toAdd_one, Pi.add_apply, Pi.zero_apply]
  exact CharTwo.add_self_eq_zero _

theorem mem_sup_zpowers_iff {G : Type*} [CommGroup G] {A : Subgroup G} {p : G} (hp : p * p = 1)
    (m : G) : m ∈ A ⊔ Subgroup.zpowers p ↔ m ∈ A ∨ m * p ∈ A := by
  have hz : ∀ z ∈ Subgroup.zpowers p, z = 1 ∨ z = p := by
    rintro z ⟨k, rfl⟩
    have h2 : p ^ (2 : ℤ) = 1 := by rw [zpow_two, hp]
    rcases Int.even_or_odd' k with ⟨j, rfl | rfl⟩
    · left
      show p ^ (2 * j) = 1
      rw [zpow_mul, h2, one_zpow]
    · right
      show p ^ (2 * j + 1) = p
      rw [zpow_add_one, zpow_mul, h2, one_zpow, one_mul]
  constructor
  · intro h
    obtain ⟨a, ha, z, hzp, hm⟩ := Subgroup.mem_sup.1 h
    rcases hz z hzp with h1 | h1
    · left
      rw [← hm, h1, mul_one]
      exact ha
    · right
      rw [← hm, h1, mul_assoc, hp, mul_one]
      exact ha
  · rintro (h | h)
    · exact Subgroup.mem_sup_left h
    · have : m = (m * p) * p := by rw [mul_assoc, hp, mul_one]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers p))

theorem mem_sup_zpowers_iff' {A : Subgroup (G6.PermMod 24)} {p : G6.PermMod 24} (hp : p * p = 1)
    (m : G6.PermMod 24) : m ∈ A ⊔ Subgroup.zpowers p ↔ m ∈ A ∨ m * p ∈ A :=
  mem_sup_zpowers_iff (G := G6.PermMod 24) hp m

@[expose] def w0 : Fin 11 → ZMod 2 := ccE (Multiplicative.toAdd (pairVec 0 1))

private theorem w0_eq : w0 = ![1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0] := by decide

theorem w0_zero : w0 0 = 1 := by rw [w0_eq]; rfl

@[expose] def cc10 : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 10 → ZMod 2) where
  toFun x j := ccE x j.succ + w0 j.succ * ccE x 0
  map_add' x y := by
    funext j
    simp only [map_add, Pi.add_apply]
    ring
  map_smul' c x := by
    funext j
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem cc10_apply (x : Fin 24 → ZMod 2) (j : Fin 10) :
    cc10 x j = ccE x j.succ + w0 j.succ * ccE x 0 := rfl

@[expose] def lift10 : (Fin 10 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) :=
  liftE.comp (LinearMap.pi fun i : Fin 11 => Fin.cases 0 (fun j => LinearMap.proj j) i)

theorem ccE_lift10 (s : Fin 10 → ZMod 2) : ccE (lift10 s) = Fin.cons 0 s := by
  rw [lift10, LinearMap.comp_apply, ccE_liftE]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem cc10_lift10 (s : Fin 10 → ZMod 2) : cc10 (lift10 s) = s := by
  funext j
  rw [cc10_apply, ccE_lift10]
  simp

theorem sum_lift10 (s : Fin 10 → ZMod 2) : ∑ k, lift10 s k = 0 := by
  rw [lift10, LinearMap.comp_apply]
  exact sum_liftE _

theorem sum_pairVec (x y : Fin 24) : ∑ k, Multiplicative.toAdd (pairVec x y) k = 0 :=
  pairVec_mem_coreMod x y

theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem zmod2_eq_of_add : ∀ {a b : ZMod 2}, a + b = 0 → a = b := by decide

theorem cc10_eq_zero_iff {x : Fin 24 → ZMod 2} (hx : ∑ k, x k = 0) :
    cc10 x = 0 ↔ x ∈ C ∨ x + Multiplicative.toAdd (pairVec 0 1) ∈ C := by
  have hp : ∑ k, (x + Multiplicative.toAdd (pairVec 0 1)) k = 0 := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, hx, sum_pairVec, add_zero]
  have hw : ccE (Multiplicative.toAdd (pairVec 0 1)) = w0 := rfl
  rw [← ccE_eq_zero_iff hx, ← ccE_eq_zero_iff hp, map_add, hw]
  constructor
  · intro h
    have hj : ∀ j : Fin 10, ccE x j.succ = w0 j.succ * ccE x 0 := by
      intro j
      have := congrFun h j
      rw [cc10_apply, Pi.zero_apply] at this
      exact zmod2_eq_of_add this
    rcases zmod2_cases (ccE x 0) with h0 | h0
    · left
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact h0
      · rw [hj, h0, mul_zero]
        rfl
    · right
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [Pi.add_apply, h0, w0_zero]
        rfl
      · rw [Pi.add_apply, hj, h0, mul_one]
        exact CharTwo.add_self_eq_zero _
  · rintro (h | h)
    · funext j
      rw [cc10_apply, h]
      simp
    · have h1 : ccE x = w0 := by
        have h2 := congrArg (· + w0) h
        simp only [zero_add, add_assoc, CharTwo.add_self_eq_zero, add_zero] at h2
        exact h2
      funext j
      rw [cc10_apply, h1, w0_zero, mul_one]
      exact CharTwo.add_self_eq_zero _

@[expose] def cocode22Coords :
    SecCoords (G6.coreMod 24) (golayC ⊔ Subgroup.zpowers (pairVec 0 1)) W10 where
  κ := AddMonoidHom.toMultiplicative cc10.toAddMonoidHom
  lift := AddMonoidHom.toMultiplicative lift10.toAddMonoidHom
  lift_mem w := sum_lift10 (Multiplicative.toAdd w)
  κ_lift w := by
    change Multiplicative.ofAdd (cc10 (lift10 (Multiplicative.toAdd w))) = w
    rw [cc10_lift10]
    rfl
  ker_iff m hm := by
    change Multiplicative.ofAdd (cc10 (Multiplicative.toAdd m)) = 1 ↔ _
    refine Iff.trans ?_ (mem_sup_zpowers_iff' (pairVec_sq 0 1) m).symm
    rw [mem_golayC_iff, mem_golayC_iff, toAdd_mul, ← cc10_eq_zero_iff hm]
    exact ⟨fun h => congrArg Multiplicative.toAdd h, fun h => congrArg Multiplicative.ofAdd h⟩

@[expose] def stabPair01 : Subgroup (Equiv.Perm (Fin 24)) where
  carrier := {σ | (σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0)}
  mul_mem' {σ τ} hσ hτ := by
    simp only [Set.mem_ofPred_eq, Equiv.Perm.mul_apply] at hσ hτ ⊢
    rcases hτ with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0, h1] <;> tauto
  one_mem' := Or.inl ⟨rfl, rfl⟩
  inv_mem' {σ} hσ := by
    simp only [Set.mem_ofPred_eq] at hσ ⊢
    rcases hσ with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · left
      exact ⟨by rw [Equiv.Perm.inv_eq_iff_eq, h0], by rw [Equiv.Perm.inv_eq_iff_eq, h1]⟩
    · right
      exact ⟨by rw [Equiv.Perm.inv_eq_iff_eq, h1], by rw [Equiv.Perm.inv_eq_iff_eq, h0]⟩

abbrev mog22plus : Subgroup (Equiv.Perm (Fin 24)) := AutPerm ⊓ stabPair01

theorem mog22_le_mog22plus : mog22 ≤ mog22plus := by
  rintro σ ⟨⟨hσ, h0⟩, h1⟩
  exact ⟨hσ, Or.inl ⟨(mem_stab_iff 0 σ).1 h0, (mem_stab_iff 1 σ).1 h1⟩⟩

theorem pair_of_mem_mog22plus {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ mog22plus) :
    pairVec (σ 0) (σ 1) = pairVec 0 1 := by
  rcases hσ.2 with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [h0, h1]
  · rw [h0, h1, pairVec, pairVec, mul_comm]

theorem preserves_cocode22 {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ mog22plus) :
    Preserves (G6.coreMod 24) (golayC ⊔ Subgroup.zpowers (pairVec 0 1)) σ := by
  obtain ⟨h1, h2⟩ := preserves_cocode hσ.1
  refine ⟨h1, fun m hm => ?_⟩
  refine (mem_sup_zpowers_iff' (pairVec_sq 0 1) _).2 ?_
  rcases (mem_sup_zpowers_iff' (pairVec_sq 0 1) m).1 hm with hm | hm
  · exact Or.inl (h2 _ hm)
  · right
    have := h2 _ hm
    rwa [map_mul, permAct_pairVec, pair_of_mem_mog22plus hσ] at this

@[expose] noncomputable def rho10 (Γ : Subgroup (Equiv.Perm (Fin 24))) (hΓ : Γ ≤ mog22plus) :
    ↥Γ →* MulAut W10 :=
  cocode22Coords.rho Γ fun _ hσ => preserves_cocode22 (hΓ hσ)

theorem cocode22_std
    {V : Type*} [CommGroup V] {L : Subgroup (MulAut V)}
    (h : MathieuCocode22 L ⊤ ⊥) :
    ∃ e : V ≃* W10, L.map (congrHom e) = (rho10 mog22 mog22_le_mog22plus).range := by
  obtain ⟨x, y, hxy, hr⟩ := h
  obtain ⟨τ, hτ, hτ0, hτ1⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two x y hxy
  obtain ⟨hn, hC⟩ := preserves_iff_of_mem hτ
  have hτ0' : τ⁻¹ x = 0 := by rw [← hτ0]; simp
  have hτ1' : τ⁻¹ y = 1 := by rw [← hτ1]; simp
  have hd : ∀ m, m ∈ golayC ⊔ Subgroup.zpowers (pairVec x y) ↔
      G6.permAct 24 τ⁻¹ m ∈ golayC ⊔ Subgroup.zpowers (pairVec 0 1) := by
    intro m
    refine (mem_sup_zpowers_iff' (pairVec_sq x y) m).trans
      (Iff.trans ?_ (mem_sup_zpowers_iff' (pairVec_sq 0 1) _).symm)
    rw [hC m, hC (m * pairVec x y), map_mul, permAct_pairVec, hτ0', hτ1']
  have hΓxy : ∀ σ ∈ AutPerm ⊓ stab x ⊓ stab y,
      Preserves (G6.coreMod 24) (golayC ⊔ Subgroup.zpowers (pairVec x y)) σ := by
    intro σ hσ
    obtain ⟨h1, h2⟩ := preserves_cocode hσ.1.1
    have hσx : σ x = x := (mem_stab_iff x σ).1 hσ.1.2
    have hσy : σ y = y := (mem_stab_iff y σ).1 hσ.2
    refine ⟨h1, fun m hm => ?_⟩
    refine (mem_sup_zpowers_iff' (pairVec_sq x y) _).2 ?_
    rcases (mem_sup_zpowers_iff' (pairVec_sq x y) m).1 hm with hm | hm
    · exact Or.inl (h2 _ hm)
    · right
      have := h2 _ hm
      rwa [map_mul, permAct_pairVec, hσx, hσy] at this
  obtain ⟨e, he⟩ := (cocode22Coords.conj τ hn hd).exists_map_eq hΓxy hr
  refine ⟨e, he.trans ?_⟩
  refine cocode22Coords.range_rho_conj τ hn hd _ hΓxy fun σ => ?_
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
