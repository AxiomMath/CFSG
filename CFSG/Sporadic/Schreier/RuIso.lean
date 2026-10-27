module

public import CFSG.Sporadic.Schreier.RuCheckIso
public import CFSG.Sporadic.Ru
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Sporadic.Schreier.RuReps

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SmallF2

abbrev ruD : CFSG.Sporadic.SmallF2.Native.VecData := CFSG.Sporadic.Ru.Native.ruData

theorem ruD_base :
    BaseFacts ruD := CFSG.Sporadic.Ru.ruFacts.toBaseFacts

theorem ruD_n : ruD.n = 4060 := rfl

@[expose] def ruTau : Equiv.Perm (Fin 4060) := CFSG.Monster.B.Co2.permOfArr 4060 ruSigmaA

theorem rep_ruTau : CFSG.Monster.B.Co2.Rep 4060 ruSigmaA ruTau :=
  (CFSG.Monster.B.Co2.rep_permOfArr ruIso_check.1).1

@[expose] def ruJPerm : J ruD →* Equiv.Perm (Fin 4060) :=
  (Equiv.permCongrHom (finCongr ruD_n)).toMonoidHom.comp (MulAction.toPermHom (J ruD) (Fin ruD.n))

@[expose] def ruJtoP : J ruD →* Equiv.Perm (Fin 4060) :=
  (MulAut.conj ruTau⁻¹).toMonoidHom.comp ruJPerm

theorem ruJPerm_apply (g : J ruD) (x : Fin 4060) :
    ((ruJPerm g x : Fin 4060) : ℕ) = CFSG.Sporadic.Th.idx ruD.n g x := by
  have hx : (x : ℕ) < ruD.n := lt_of_lt_of_eq x.2 ruD_n.symm
  rw [CFSG.Sporadic.Th.idx_of_lt g hx]
  have e : Fin.cast ruD_n.symm x = ⟨x, hx⟩ := Fin.ext rfl
  simp only [ruJPerm, MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, Equiv.permCongrHom_coe,
    Equiv.permCongr_apply, MulAction.toPermHom_apply, MulAction.toPerm_apply, finCongr_apply,
    finCongr_symm, Fin.val_cast, e]

theorem perm_conj_inv_apply {α : Type*} (τ f : Equiv.Perm α) (x : α) :
    (MulAut.conj τ⁻¹ f) x = τ⁻¹ (f (τ x)) := by
  rw [MulAut.conj_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, inv_inv]

theorem perm_inv_apply_self {α : Type*} (τ : Equiv.Perm α) (x : α) : τ⁻¹ (τ x) = x :=
  τ.symm_apply_apply x

theorem ruJtoP_apply_conj (g : J ruD) (x : Fin 4060) :
    ruJtoP g x = (MulAut.conj ruTau⁻¹ (ruJPerm g)) x := by
  rw [ruJtoP, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]

theorem ruTau_conj_apply (f : Equiv.Perm (Fin 4060)) (x : Fin 4060) :
    (MulAut.conj ruTau⁻¹ f) x = ruTau⁻¹ (f (ruTau x)) :=
  perm_conj_inv_apply ruTau f x

theorem ruJtoP_apply (g : J ruD) (x : Fin 4060) :
    ruJtoP g x = ruTau⁻¹ (ruJPerm g (ruTau x)) := by
  rw [ruJtoP_apply_conj, ruTau_conj_apply]

theorem ruJtoP_gen
    {g : J ruD} {T : CFSG.Sporadic.Th.Native.Table} {a : Array ℕ}
    {A : Equiv.Perm (Fin 4060)} (hT : CFSG.Sporadic.Th.Rep ruD.n T g)
    (ha : CFSG.Monster.B.Co2.Rep 4060 a A)
    (h : ∀ i < 4060, ruSigmaA[a[i]!]! = CFSG.Sporadic.Th.Native.ap T ruSigmaA[i]!) :
    ruJtoP g = A := by
  apply Equiv.ext
  intro x
  have h1 : ruJPerm g (ruTau x) = ruTau (A x) := by
    apply Fin.ext
    rw [ruJPerm_apply, ← hT _ (lt_of_lt_of_eq (ruTau x).2 ruD_n.symm), ← rep_ruTau x, ← h x x.2,
      ha x, rep_ruTau (A x)]
  rw [ruJtoP_apply, h1, perm_inv_apply_self]

theorem ruJtoP_a :
    ruJtoP (a ruD) = ruA0 :=
  ruJtoP_gen (rep_a ruD_base) rep_ruA0 fun i hi => (ruIso_check.2 i hi).1

theorem ruJtoP_b :
    ruJtoP (b ruD) = ruA1 :=
  ruJtoP_gen (rep_b ruD_base) rep_ruA1 fun i hi => (ruIso_check.2 i hi).2

theorem ruJtoP_injective : Function.Injective ruJtoP := by
  have := faithful ruD_base
  have hinj : Function.Injective ruJPerm :=
    (Equiv.permCongrHom (finCongr ruD_n)).injective.comp MulAction.toPerm_injective
  exact (MulAut.conj ruTau⁻¹).injective.comp hinj

theorem ruJtoP_range :
    ruJtoP.range = ruP := by
  rw [MonoidHom.range_eq_map, ← closure_ab ruD, MonoidHom.map_closure, Set.image_pair, ruJtoP_a,
    ruJtoP_b]
  rfl

@[expose] def ruJEquivP :
    J ruD ≃* ruP :=
  (MonoidHom.ofInjective ruJtoP_injective).trans (MulEquiv.subgroupCongr ruJtoP_range)

def ruSeedEquiv :
    CFSG.Blueprint.NativeSporadic.Ru ≃* J CFSG.Sporadic.Ru.Native.ruData :=
  seedEquiv CFSG.Sporadic.Ru.ruFacts.toBaseFacts

def ruEquivP :

    CFSG.Blueprint.NativeSporadic.Ru ≃* ruP := ruSeedEquiv.trans ruJEquivP

theorem card_ruP' :
    Nat.card ruP = 145926144000 := by
  rw [← Nat.card_congr (MulEquiv.toEquiv ruEquivP)]
  exact CFSG.Sporadic.Ru.card_Ru

theorem isSimpleGroup_ruJ : IsSimpleGroup (J ruD) :=
  isSimpleGroup_J CFSG.Sporadic.Ru.ruFacts (by decide) (by decide) (k := 2) rfl (by decide)
    (by norm_num [CFSG.Sporadic.Ru.Native.ruData]) (by norm_num [CFSG.Sporadic.Ru.Native.ruData])
    (by norm_num [CFSG.Sporadic.Ru.Native.ruData]) (by decide) (by decide)

theorem isSimpleGroup_ruP :
    IsSimpleGroup ruP :=
  @MulEquiv.isSimpleGroup _ _ _ _ isSimpleGroup_ruJ ruJEquivP.symm

end CFSG.Sporadic.RuSchreier
