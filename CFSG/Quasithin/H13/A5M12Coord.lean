module

public import CFSG.Quasithin.Background.HMathieuCode
public import CFSG.Quasithin.Vol2.Ch10SecQ1M12
public import CFSG.Quasithin.Background.B4ModelsAction

public section

namespace CFSG.Quasithin.H13.A5.M12

open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.Vol2.Ch10.SecA.C10P01

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def dY : Fin 11 → ZMod 2 := κC dodecadW

theorem dY_zero : dY 0 = 1 := by decide

@[expose] def projY : (Fin 11 → ZMod 2) →ₗ[ZMod 2] (Fin 10 → ZMod 2) where
  toFun u k := u k.succ + u 0 * dY k.succ
  map_add' u v := by
    funext k
    simp only [Pi.add_apply]
    ring
  map_smul' c u := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem projY_apply (u : Fin 11 → ZMod 2) (k : Fin 10) :
    projY u k = u k.succ + u 0 * dY k.succ := rfl

@[expose] def cons0 : (Fin 10 → ZMod 2) →ₗ[ZMod 2] (Fin 11 → ZMod 2) where
  toFun w := Fin.cons 0 w
  map_add' w w' := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, Pi.add_apply, add_zero]
    · simp only [Fin.cons_succ, Pi.add_apply]
  map_smul' c w := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, Pi.smul_apply, smul_eq_mul, mul_zero, RingHom.id_apply]
    · simp only [Fin.cons_succ, Pi.smul_apply, RingHom.id_apply]

theorem projY_cons0 (w : Fin 10 → ZMod 2) : projY (cons0 w) = w := by
  funext k
  change (Fin.cons 0 w : Fin 11 → ZMod 2) k.succ + (Fin.cons 0 w : Fin 11 → ZMod 2) 0 *
    dY k.succ = w k
  rw [Fin.cons_succ, Fin.cons_zero, zero_mul, add_zero]

theorem projY_dY : projY dY = 0 := by
  funext k
  rw [projY_apply, dY_zero, one_mul, Pi.zero_apply]
  exact CharTwo.add_self_eq_zero _

theorem projY_eq_zero_iff (u : Fin 11 → ZMod 2) : projY u = 0 ↔ u = 0 ∨ u = dY := by
  constructor
  · intro h
    have hk : ∀ k : Fin 10, u k.succ = u 0 * dY k.succ := fun k => by
      have := congrFun h k
      rw [projY_apply, Pi.zero_apply] at this
      exact zmod2_eq_of_add this
    rcases zmod2_cases (u 0) with h0 | h0
    · left
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact h0
      · rw [hk, h0, zero_mul]
        rfl
    · right
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [h0, dY_zero]
      · rw [hk, h0, one_mul]
  · rintro (rfl | rfl)
    · exact map_zero projY
    · exact projY_dY

@[expose] def κC12 : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 10 → ZMod 2) := projY.comp κC

@[expose] def lift12 : (Fin 10 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) := liftC.comp cons0

theorem κC12_apply (x : Fin 24 → ZMod 2) : κC12 x = projY (κC x) := rfl

theorem κC12_lift12 (w : Fin 10 → ZMod 2) : κC12 (lift12 w) = w := by
  change projY (κC (liftC (cons0 w))) = w
  rw [κC_liftC, projY_cons0]

theorem lift12_mem (w : Fin 10 → ZMod 2) : lift12 w ∈ C := liftC_mem _

theorem κC12_eq_zero_iff {x : Fin 24 → ZMod 2} (hx : x ∈ C) :
    κC12 x = 0 ↔ x = 0 ∨ x = Ω ∨ x = dodecadW ∨ x = dodecadW + Ω := by
  rw [κC12_apply, projY_eq_zero_iff]
  have hd : x - dodecadW ∈ C := C.sub_mem hx dodecadW_mem_C
  have hκ : κC x = dY ↔ κC (x - dodecadW) = 0 := by
    rw [map_sub, sub_eq_zero]
    rfl
  rw [κC_eq_zero_iff hx, hκ, κC_eq_zero_iff hd, sub_eq_zero, sub_eq_iff_eq_add']
  tauto

@[expose] def denomY : Subgroup (G6.PermMod 24) := Subgroup.closure {G6.allOnes 24, dodecadE}

theorem dodecadE_sq : dodecadE * dodecadE = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  exact CharTwo.add_self_eq_zero _

theorem mem_denomY (m : G6.PermMod 24) :
    m ∈ denomY ↔ m = 1 ∨ m = G6.allOnes 24 ∨ m = dodecadE ∨ m = dodecadE * G6.allOnes 24 := by
  have hpair : denomY = Subgroup.zpowers (G6.allOnes 24) ⊔ Subgroup.zpowers dodecadE := by
    rw [denomY, Set.insert_eq, Subgroup.closure_union, Subgroup.zpowers_eq_closure,
      Subgroup.zpowers_eq_closure]
  rw [hpair]
  constructor
  · intro hm
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hm
    rcases (mem_zpowers_of_sq allOnes_sq a).1 ha with rfl | rfl <;>
      rcases (mem_zpowers_of_sq dodecadE_sq b).1 hb with rfl | rfl
    · left
      rw [mul_one]
    · right; right; left
      rw [one_mul]
    · right; left
      rw [mul_one]
    · right; right; right
      rw [mul_comm]
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))

theorem mem_denomY_iff_toAdd (m : G6.PermMod 24) :
    m ∈ denomY ↔ Multiplicative.toAdd m = 0 ∨ Multiplicative.toAdd m = Ω ∨
      Multiplicative.toAdd m = dodecadW ∨ Multiplicative.toAdd m = dodecadW + Ω := by
  rw [mem_denomY]
  refine or_congr ?_ (or_congr ?_ (or_congr ?_ ?_))
  · exact ⟨fun h => by rw [h]; rfl, fun h => Multiplicative.toAdd.injective h⟩
  · exact ⟨fun h => by rw [h]; rfl, fun h => Multiplicative.toAdd.injective h⟩
  · exact ⟨fun h => by rw [h]; rfl, fun h => Multiplicative.toAdd.injective h⟩
  · exact ⟨fun h => by rw [h]; rfl, fun h => Multiplicative.toAdd.injective h⟩

@[expose] def code12Coords : SecCoords golayC denomY W10 where
  κ := AddMonoidHom.toMultiplicative κC12.toAddMonoidHom
  lift := AddMonoidHom.toMultiplicative lift12.toAddMonoidHom
  lift_mem w := lift12_mem (Multiplicative.toAdd w)
  κ_lift w := by
    change Multiplicative.ofAdd (κC12 (lift12 (Multiplicative.toAdd w))) = w
    rw [κC12_lift12]
    rfl
  ker_iff m hm := by
    change Multiplicative.ofAdd (κC12 (Multiplicative.toAdd m)) = 1 ↔ _
    rw [mem_denomY_iff_toAdd, ← κC12_eq_zero_iff ((H.Mathieu.mem_golayC_iff m).1 hm)]
    exact ⟨fun h => congrArg Multiplicative.toAdd h, fun h => congrArg Multiplicative.ofAdd h⟩

@[expose] def m24Pair : Subgroup (Equiv.Perm (Fin 24)) where
  carrier := {σ | σ ∈ AutPerm ∧ G6.permAct 24 σ dodecadE ∈ ({dodecadE, dodecadE * G6.allOnes 24} :
    Set (G6.PermMod 24))}
  one_mem' := ⟨AutPerm.one_mem, by rw [map_one, MulAut.one_apply]; exact Or.inl rfl⟩
  mul_mem' {σ τ} hσ hτ := ⟨AutPerm.mul_mem hσ.1 hτ.1, by
    rw [map_mul, MulAut.mul_apply]
    rcases hτ.2 with h | h <;> rw [h]
    · exact hσ.2
    · rw [map_mul, H.Mathieu.permAct_allOnes]
      rcases hσ.2 with h' | h' <;> rw [h']
      · exact Or.inr rfl
      · left
        rw [mul_assoc, allOnes_sq, mul_one]⟩
  inv_mem' {σ} hσ := ⟨AutPerm.inv_mem hσ.1, by
    have hback : ∀ m, G6.permAct 24 σ⁻¹ (G6.permAct 24 σ m) = m := fun m => by
      rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
    rcases hσ.2 with h | h
    · left
      conv_lhs => rw [← h]
      exact hback _
    · right
      have h1 := hback dodecadE
      rw [h, map_mul, H.Mathieu.permAct_allOnes] at h1
      calc G6.permAct 24 σ⁻¹ dodecadE
          = G6.permAct 24 σ⁻¹ dodecadE * G6.allOnes 24 * G6.allOnes 24 := by
            rw [mul_assoc, allOnes_sq, mul_one]
        _ = dodecadE * G6.allOnes 24 := by rw [h1]⟩

theorem mem_m24Pair {σ : Equiv.Perm (Fin 24)} :
    σ ∈ m24Pair ↔ σ ∈ AutPerm ∧ (G6.permAct 24 σ dodecadE = dodecadE ∨
      G6.permAct 24 σ dodecadE = dodecadE * G6.allOnes 24) := Iff.rfl

theorem m24Fix_le_m24Pair : m24Fix dodecadE ≤ m24Pair := fun _ hσ => ⟨hσ.1, Or.inl hσ.2⟩

theorem preserves_code12 {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ m24Pair) :
    Preserves golayC denomY σ := by
  refine ⟨(preserves_code hσ.1).1, fun m hm => ?_⟩
  have hΩ : G6.permAct 24 σ (G6.allOnes 24) = G6.allOnes 24 := H.Mathieu.permAct_allOnes σ
  have hY : G6.permAct 24 σ dodecadE ∈ denomY := by
    rcases hσ.2 with h | h <;> rw [h, mem_denomY]
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  rcases (mem_denomY m).1 hm with rfl | rfl | rfl | rfl
  · rw [map_one]
    exact Subgroup.one_mem _
  · rw [hΩ, mem_denomY]
    exact Or.inr (Or.inl rfl)
  · exact hY
  · rw [map_mul, hΩ]
    exact Subgroup.mul_mem _ hY ((mem_denomY _).2 (Or.inr (Or.inl rfl)))

@[expose] noncomputable def rhoC12 (Γ : Subgroup (Equiv.Perm (Fin 24))) (hΓ : Γ ≤ m24Pair) :
    ↥Γ →* MulAut W10 :=
  code12Coords.rho Γ fun _ hσ => preserves_code12 (hΓ hσ)

@[expose] def projYW : W11 →* W10 := AddMonoidHom.toMultiplicative projY.toAddMonoidHom

theorem projYW_apply (u : W11) :
    projYW u = Multiplicative.ofAdd (projY (Multiplicative.toAdd u)) := rfl

@[expose] def cons0W : W10 →* W11 := AddMonoidHom.toMultiplicative cons0.toAddMonoidHom

theorem projYW_cons0W (w : W10) : projYW (cons0W w) = w := by
  change Multiplicative.ofAdd (projY (cons0 (Multiplicative.toAdd w))) = w
  rw [projY_cons0]
  rfl

@[expose] def dYW : W11 := Multiplicative.ofAdd dY

theorem codeCoords_κ_dodecadE : codeCoords.κ dodecadE = dYW := rfl

theorem projYW_eq_one_iff (u : W11) : projYW u = 1 ↔ u = 1 ∨ u = dYW := by
  rw [projYW_apply]
  have h := projY_eq_zero_iff (Multiplicative.toAdd u)
  constructor
  · intro h1
    rcases h.1 (congrArg Multiplicative.toAdd h1) with h2 | h2
    · exact Or.inl (Multiplicative.toAdd.injective h2)
    · exact Or.inr (Multiplicative.toAdd.injective h2)
  · rintro (rfl | rfl)
    · change Multiplicative.ofAdd (projY 0) = 1
      rw [map_zero]
      rfl
    · exact congrArg Multiplicative.ofAdd projY_dY

theorem projYW_surjective : Function.Surjective projYW := fun w => ⟨_, projYW_cons0W w⟩

theorem rhoHom_dYW {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ m24Pair) :
    codeCoords.rhoHom σ dYW = dYW := by
  have h1 := codeCoords.κ_permAct (preserves_code hσ.1) dodecadE_mem_golayC
  rw [← codeCoords_κ_dodecadE, ← h1]
  rcases hσ.2 with h | h
  · rw [h]
  · rw [h, map_mul, (codeCoords.ker_iff _ allOnes_mem_golayC).2 (Subgroup.mem_zpowers _)]
    exact mul_one _

theorem projYW_rhoHom {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ m24Pair) (u : W11) :
    projYW (codeCoords.rhoHom σ u) = code12Coords.rhoHom σ (projYW u) := by
  have hu : u = (u * (cons0W (projYW u))⁻¹) * cons0W (projYW u) :=
    (inv_mul_cancel_right _ _).symm
  have hδ1 : projYW (u * (cons0W (projYW u))⁻¹) = 1 := by
    rw [map_mul, map_inv, projYW_cons0W, mul_inv_cancel]
  have hfix : projYW (codeCoords.rhoHom σ (u * (cons0W (projYW u))⁻¹)) = 1 := by
    rcases (projYW_eq_one_iff _).1 hδ1 with h | h
    · rw [h, map_one, map_one]
    · rw [h, rhoHom_dYW hσ, ← h, hδ1]
  change projYW (codeCoords.rhoHom σ u) = projYW (codeCoords.rhoHom σ (cons0W (projYW u)))
  conv_lhs => rw [hu]
  rw [map_mul, map_mul, hfix, one_mul]

theorem m12_std
    {V : Type*} [CommGroup V] {L : Subgroup (MulAut V)} (h : M12Ten L ⊤ ⊥) :
    ∃ e : V ≃* W10, L.map (congrHom e) = (rhoC12 (m24Fix dodecadE) m24Fix_le_m24Pair).range := by
  obtain ⟨eY, hY, hw, hr⟩ := h
  obtain ⟨p, hp, hpe⟩ := exists_permAct_eq hY hw
  have hC := (preserves_iff_of_mem hp).2
  have hpinv : G6.permAct 24 p⁻¹ eY = dodecadE := by
    rw [← hpe, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
  have hd : ∀ m, m ∈ Subgroup.closure {G6.allOnes 24, eY} ↔ G6.permAct 24 p⁻¹ m ∈ denomY := by
    intro m
    have hmap : (Subgroup.closure {G6.allOnes 24, eY}).map (G6.permAct 24 p⁻¹).toMonoidHom =
        denomY := by
      rw [MonoidHom.map_closure, denomY]
      congr 1
      ext x
      simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
        MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨y, rfl | rfl, rfl⟩
        · exact Or.inl (H.Mathieu.permAct_allOnes _)
        · exact Or.inr hpinv
      · rintro (rfl | rfl)
        · exact ⟨_, Or.inl rfl, H.Mathieu.permAct_allOnes _⟩
        · exact ⟨_, Or.inr rfl, hpinv⟩
    rw [← hmap, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hΓ : ∀ σ ∈ m24Fix eY, Preserves golayC (Subgroup.closure {G6.allOnes 24, eY}) σ := by
    intro σ hσ
    refine ⟨(preserves_code hσ.1).1, fun m hm => ?_⟩
    have hle : Subgroup.closure {G6.allOnes 24, eY} ≤
        (Subgroup.closure {G6.allOnes 24, eY}).comap (G6.permAct 24 σ).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact Subgroup.subset_closure (Or.inl (H.Mathieu.permAct_allOnes σ))
      · exact Subgroup.subset_closure (Or.inr hσ.2)
    exact hle hm
  obtain ⟨e, he⟩ := (code12Coords.conj p hC hd).exists_map_eq hΓ hr
  refine ⟨e, he.trans ?_⟩
  refine code12Coords.range_rho_conj p hC hd _ hΓ fun σ => ?_
  rw [← hpe, m24Fix_permAct hp]
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    change p⁻¹ * (p * ρ * p⁻¹) * p ∈ m24Fix dodecadE
    rwa [show p⁻¹ * (p * ρ * p⁻¹) * p = ρ by group]
  · intro hσ
    exact ⟨_, hσ, by change p * (p⁻¹ * σ * p) * p⁻¹ = σ; group⟩

end CFSG.Quasithin.H13.A5.M12
