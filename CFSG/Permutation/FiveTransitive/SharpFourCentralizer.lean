module

public import CFSG.Permutation.FiveTransitive.SharpFourBound

public section

namespace CFSG

namespace FiveTransitive.Research.SharpFourDegreeCompletion

open MulAction
open Research.SharpFourBound

variable {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]

private def fixedByEquivOfConjugate
    (g h q : G) (hconj : q * g * q⁻¹ = h) :
    MulAction.fixedBy X g ≃ MulAction.fixedBy X h where
  toFun x :=
    ⟨q • (x : X), by
      change h • (q • (x : X)) = q • (x : X)
      rw [← hconj, mul_smul, mul_smul, inv_smul_smul, x.prop]⟩
  invFun x :=
    ⟨q⁻¹ • (x : X), by
      change g • (q⁻¹ • (x : X)) = q⁻¹ • (x : X)
      have hg : g = q⁻¹ * h * q := by
        rw [← hconj]
        group
      rw [hg, mul_smul, mul_smul, smul_inv_smul, x.prop]⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv x := by
    apply Subtype.ext
    simp

theorem fixedBy_ncard_eq_of_conjugate
    (g h q : G) (hconj : q * g * q⁻¹ = h) :
    (MulAction.fixedBy X g).ncard =
      (MulAction.fixedBy X h).ncard := by
  classical
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_congr (fixedByEquivOfConjugate g h q hconj)

private theorem involution_fixedBy_ncard_eq_two_or_three
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hcard : Nat.card G = (Fintype.card X).descFactorial 4)
    (hX : 8 ≤ Fintype.card X)
    (e : Fin 4 ↪ X)
    (g : G) (hgTwo : g ^ 2 = 1) (hg : g ≠ 1) :
    (MulAction.fixedBy X g).ncard = 2 ∨
      (MulAction.fixedBy X g).ncard = 3 := by
  classical
  let s := sharpSingleInvolution h4 hcard e
  let d := sharpDoubleInvolution h4 hcard e
  obtain ⟨qg, hqg⟩ :=
    involution_conjugate_sharpDouble h4 hcard hX e g hgTwo hg
  obtain ⟨qs, hqs⟩ :=
    involution_conjugate_sharpDouble h4 hcard hX e s
      (sharpSingleInvolution_sq h4 hcard e)
      (sharpSingleInvolution_ne_one h4 hcard e)
  have hfixEq :
      (MulAction.fixedBy X g).ncard =
        (MulAction.fixedBy X s).ncard := by
    calc
      (MulAction.fixedBy X g).ncard =
          (MulAction.fixedBy X d).ncard :=
        fixedBy_ncard_eq_of_conjugate g d qg hqg
      _ = (MulAction.fixedBy X s).ncard :=
        (fixedBy_ncard_eq_of_conjugate s d qs hqs).symm
  have he01 : e 0 ≠ e 1 := by
    intro h
    exact (by decide : (0 : Fin 4) ≠ 1) (e.injective h)
  have hpair :
      ({e 0, e 1} : Set X) ⊆ MulAction.fixedBy X s := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · change sharpSingleInvolution h4 hcard e • e 0 = e 0
      have hb : baseSingleSwap (0 : Fin 4) = 0 := by decide
      change sharpLift h4 hcard e baseSingleSwap • e 0 = e 0
      rw [sharpLift_smul_apply, hb]
    · change sharpSingleInvolution h4 hcard e • e 1 = e 1
      have hb : baseSingleSwap (1 : Fin 4) = 1 := by decide
      change sharpLift h4 hcard e baseSingleSwap • e 1 = e 1
      rw [sharpLift_smul_apply, hb]
  have hlower : 2 ≤ (MulAction.fixedBy X s).ncard := by
    have := Set.ncard_le_ncard hpair
    simpa [Set.ncard_pair he01] using this
  have hupper :
      (MulAction.fixedBy X s).ncard ≤ 3 :=
    fixedBy_ncard_le_three_of_ne_one h4 hcard s
      (sharpSingleInvolution_ne_one h4 hcard e)
  rw [hfixEq]
  omega

private def movedBy (t : G) : Set X := {x | t • x ≠ x}

private theorem movedBy_eq_compl_fixedBy (t : G) :
    movedBy (X := X) t = (MulAction.fixedBy X t)ᶜ := by
  ext x
  simp [movedBy, MulAction.mem_fixedBy]

private theorem movedBy_ncard (t : G) :
    (movedBy (X := X) t).ncard =
      Fintype.card X - (MulAction.fixedBy X t).ncard := by
  rw [movedBy_eq_compl_fixedBy, Set.ncard_compl,
    Nat.card_eq_fintype_card]

@[expose] def IntertwiningEmbeddings (t : G) (σ : Equiv.Perm (Fin 4)) :=
  {a : Fin 4 ↪ X // ∀ i, t • a i = a (σ i)}

@[expose] noncomputable def sharpTransport
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (e a : Fin 4 ↪ X) : G :=
  Classical.choose (exists_maps_embedding h4 e a)

@[simp] theorem sharpTransport_smul_apply
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (e a : Fin 4 ↪ X) (i : Fin 4) :
    sharpTransport h4 e a • e i = a i :=
  Classical.choose_spec (exists_maps_embedding h4 e a) i

private noncomputable def centralizerEquivIntertwining
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hcard : Nat.card G = (Fintype.card X).descFactorial 4)
    (e : Fin 4 ↪ X) (t : G) (σ : Equiv.Perm (Fin 4))
    (hbase : ∀ i, t • e i = e (σ i)) :
    (Subgroup.centralizer {t} : Type) ≃ IntertwiningEmbeddings (X := X) t σ where
  toFun g :=
    ⟨(g : G) • e, by
      intro i
      have hcomm : (g : G) * t = t * (g : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp g.property
      change t • ((g : G) • e i) = (g : G) • e (σ i)
      rw [← mul_smul, ← hcomm, mul_smul, hbase]⟩
  invFun a :=
    ⟨sharpTransport h4 e a.1, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply eq_of_agrees_four h4 hcard e
      intro i
      rw [mul_smul, mul_smul, hbase,
        sharpTransport_smul_apply, sharpTransport_smul_apply, a.property]⟩
  left_inv g := by
    apply Subtype.ext
    apply eq_of_agrees_four h4 hcard e
    intro i
    exact sharpTransport_smul_apply h4 e ((g : G) • e) i
  right_inv a := by
    apply Subtype.ext
    ext i
    exact sharpTransport_smul_apply h4 e a.1 i

private theorem centralizer_ncard_eq_intertwining
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hcard : Nat.card G = (Fintype.card X).descFactorial 4)
    (e : Fin 4 ↪ X) (t : G) (σ : Equiv.Perm (Fin 4))
    (hbase : ∀ i, t • e i = e (σ i)) :
    Nat.card (Subgroup.centralizer {t}) =
      Nat.card (IntertwiningEmbeddings (X := X) t σ) :=
  Nat.card_congr (centralizerEquivIntertwining h4 hcard e t σ hbase)

theorem centralizer_ncard_eq_of_conjugate
    (g h q : G) (hconj : q * g * q⁻¹ = h) :
    Nat.card (Subgroup.centralizer {g}) =
      Nat.card (Subgroup.centralizer {h}) := by
  rw [Subgroup.nat_card_centralizer_nat_card_stabilizer,
    Subgroup.nat_card_centralizer_nat_card_stabilizer]
  exact Nat.card_congr
    (MulAction.stabilizerEquivStabilizer
      (g := ConjAct.toConjAct q) hconj.symm).toEquiv

private theorem involution_smul_smul (t : G) (htwo : t ^ 2 = 1) (x : X) :
    t • (t • x) = x := by
  rw [← mul_smul, ← pow_two, htwo, one_smul]

private def SingleParameters (t : G) :=
  (Fin 2 ↪ MulAction.fixedBy X t) × movedBy (X := X) t

private def singleParamsEmbedding
    (t : G) (htwo : t ^ 2 = 1) (p : SingleParameters (X := X) t) :
    Fin 4 ↪ X where
  toFun := ![(p.1 0 : X), (p.1 1 : X), (p.2 : X), t • (p.2 : X)]
  inj' := by
    have hinvol := involution_smul_smul (X := X) t htwo
    have h01 : (p.1 0 : X) ≠ (p.1 1 : X) := by
      intro h
      have : (0 : Fin 2) = 1 := p.1.injective (Subtype.ext h)
      exact (show (0 : Fin 2) ≠ 1 by decide) this
    have h0x : (p.1 0 : X) ≠ (p.2 : X) := by
      intro h
      apply p.2.property
      rw [← h]
      exact (p.1 0).property
    have h1x : (p.1 1 : X) ≠ (p.2 : X) := by
      intro h
      apply p.2.property
      rw [← h]
      exact (p.1 1).property
    have h0tx : (p.1 0 : X) ≠ t • (p.2 : X) := by
      intro h
      have hh := congrArg (fun y : X => t • y) h
      rw [(p.1 0).property, hinvol] at hh
      exact h0x hh
    have h1tx : (p.1 1 : X) ≠ t • (p.2 : X) := by
      intro h
      have hh := congrArg (fun y : X => t • y) h
      rw [(p.1 1).property, hinvol] at hh
      exact h1x hh
    have hxtx : (p.2 : X) ≠ t • (p.2 : X) := p.2.property.symm
    have h10 := h01.symm
    have hx0 := h0x.symm
    have hx1 := h1x.symm
    have htx0 := h0tx.symm
    have htx1 := h1tx.symm
    have htxx := hxtx.symm
    intro i j
    fin_cases i <;> fin_cases j <;> simp_all

private def singleParamsToIntertwining
    (t : G) (htwo : t ^ 2 = 1) (p : SingleParameters (X := X) t) :
    IntertwiningEmbeddings (X := X) t baseSingleSwap :=
  ⟨singleParamsEmbedding t htwo p, by
    intro i
    have hinvol := involution_smul_smul (X := X) t htwo
    fin_cases i
    ·
      change t • (p.1 0 : X) = (p.1 0 : X)
      exact (p.1 0).property
    ·
      change t • (p.1 1 : X) = (p.1 1 : X)
      exact (p.1 1).property
    ·
      change t • (p.2 : X) = t • (p.2 : X)
      rfl
    ·
      change t • (t • (p.2 : X)) = (p.2 : X)
      exact hinvol (p.2 : X)⟩

private def singleIntertwiningToParams
    (t : G) (a : IntertwiningEmbeddings (X := X) t baseSingleSwap) :
    SingleParameters (X := X) t :=
  (⟨fun i => ⟨a.1 (Fin.castLE (by omega) i), by
        fin_cases i
        · change t • a.1 0 = a.1 0
          have hb : baseSingleSwap (0 : Fin 4) = 0 := by decide
          simpa only [hb] using a.property (0 : Fin 4)
        · change t • a.1 1 = a.1 1
          have hb : baseSingleSwap (1 : Fin 4) = 1 := by decide
          simpa only [hb] using a.property (1 : Fin 4)⟩, by
      intro i j hij
      apply Fin.castLE_injective (by omega : 2 ≤ 4)
      apply a.1.injective
      exact congrArg Subtype.val hij⟩,
   ⟨a.1 2, by
      intro hfix
      have ha := a.property (2 : Fin 4)
      have hb : baseSingleSwap (2 : Fin 4) = 3 := by decide
      rw [hb] at ha
      have h23 : a.1 2 = a.1 3 := hfix.symm.trans ha
      exact (show (2 : Fin 4) ≠ 3 by decide) (a.1.injective h23)⟩)

private def singleIntertwiningEquiv
    (t : G) (htwo : t ^ 2 = 1) :
    IntertwiningEmbeddings (X := X) t baseSingleSwap ≃
      SingleParameters (X := X) t where
  toFun := singleIntertwiningToParams t
  invFun := singleParamsToIntertwining t htwo
  left_inv a := by
    apply Subtype.ext
    ext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    ·
      change t • a.1 2 = a.1 3
      have ha := a.property (2 : Fin 4)
      have hb : baseSingleSwap (2 : Fin 4) = 3 := by decide
      simpa only [hb] using ha
  right_inv p := by
    apply Prod.ext
    · apply Function.Embedding.ext
      intro i
      apply Subtype.ext
      fin_cases i <;> rfl
    · apply Subtype.ext
      rfl

theorem singleIntertwining_ncard
    (t : G) (htwo : t ^ 2 = 1) :
    Nat.card (IntertwiningEmbeddings (X := X) t baseSingleSwap) =
      (MulAction.fixedBy X t).ncard.descFactorial 2 *
        (Fintype.card X - (MulAction.fixedBy X t).ncard) := by
  classical
  letI : Fintype (MulAction.fixedBy X t) := Fintype.ofFinite _
  letI : Fintype (Fin 2 ↪ MulAction.fixedBy X t) := Fintype.ofFinite _
  calc
    Nat.card (IntertwiningEmbeddings (X := X) t baseSingleSwap) =
        Nat.card (SingleParameters (X := X) t) :=
      Nat.card_congr (singleIntertwiningEquiv (X := X) t htwo)
    _ = Nat.card (Fin 2 ↪ MulAction.fixedBy X t) *
        Nat.card (movedBy (X := X) t) := Nat.card_prod _ _
    _ = (MulAction.fixedBy X t).ncard.descFactorial 2 *
        (Fintype.card X - (MulAction.fixedBy X t).ncard) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq,
        Fintype.card_fin, ← Nat.card_eq_fintype_card,
        Nat.card_coe_set_eq, Nat.card_coe_set_eq, movedBy_ncard]

private def movedImage (t : G) (x : movedBy (X := X) t) : movedBy (X := X) t :=
  ⟨t • (x : X), by
    intro h
    exact x.property ((MulAction.injective t) h)⟩

private theorem movedImage_ne (t : G) (x : movedBy (X := X) t) :
    movedImage t x ≠ x := by
  intro h
  exact x.property (congrArg Subtype.val h)

private def DoubleParameters (t : G) :=
  Σ x : movedBy (X := X) t,
    {z : movedBy (X := X) t // z ≠ x ∧ z ≠ movedImage t x}

private def doubleParamsEmbedding
    (t : G) (htwo : t ^ 2 = 1) (p : DoubleParameters (X := X) t) :
    Fin 4 ↪ X where
  toFun :=
    ![(p.1 : X), t • (p.1 : X), (p.2.1 : X), t • (p.2.1 : X)]
  inj' := by
    have hinvol := involution_smul_smul (X := X) t htwo
    have hxtx : (p.1 : X) ≠ t • (p.1 : X) := p.1.property.symm
    have hztz : (p.2.1 : X) ≠ t • (p.2.1 : X) := p.2.1.property.symm
    have hzx : (p.2.1 : X) ≠ (p.1 : X) := by
      intro h
      exact p.2.2.1 (Subtype.ext h)
    have hztx : (p.2.1 : X) ≠ t • (p.1 : X) := by
      intro h
      apply p.2.2.2
      apply Subtype.ext
      exact h
    have hxtz : (p.1 : X) ≠ t • (p.2.1 : X) := by
      intro h
      have hh := congrArg (fun y : X => t • y) h
      have hh' : t • (p.1 : X) = (p.2.1 : X) :=
        hh.trans (hinvol (p.2.1 : X))
      exact hztx hh'.symm
    have htxtz : t • (p.1 : X) ≠ t • (p.2.1 : X) := by
      intro h
      exact hzx ((MulAction.injective t) h).symm
    have htxx := hxtx.symm
    have hxz := hzx.symm
    have htxz := hztx.symm
    have htzx := hxtz.symm
    have htztx := htxtz.symm
    have htzz := hztz.symm
    intro i j
    fin_cases i <;> fin_cases j <;> simp_all

private def doubleParamsToIntertwining
    (t : G) (htwo : t ^ 2 = 1) (p : DoubleParameters (X := X) t) :
    IntertwiningEmbeddings (X := X) t baseDoubleSwap :=
  ⟨doubleParamsEmbedding t htwo p, by
    intro i
    have hinvol := involution_smul_smul (X := X) t htwo
    fin_cases i
    · change t • (p.1 : X) = t • (p.1 : X)
      rfl
    · change t • (t • (p.1 : X)) = (p.1 : X)
      exact hinvol (p.1 : X)
    · change t • (p.2.1 : X) = t • (p.2.1 : X)
      rfl
    · change t • (t • (p.2.1 : X)) = (p.2.1 : X)
      exact hinvol (p.2.1 : X)⟩

private def doubleIntertwiningToParams
    (t : G) (a : IntertwiningEmbeddings (X := X) t baseDoubleSwap) :
    DoubleParameters (X := X) t := by
  let x : movedBy (X := X) t := ⟨a.1 0, by
    intro hfix
    have ha := a.property (0 : Fin 4)
    have hb : baseDoubleSwap (0 : Fin 4) = 1 := by decide
    rw [hb] at ha
    have h01 : a.1 0 = a.1 1 := hfix.symm.trans ha
    exact (show (0 : Fin 4) ≠ 1 by decide) (a.1.injective h01)⟩
  let z : movedBy (X := X) t := ⟨a.1 2, by
    intro hfix
    have ha := a.property (2 : Fin 4)
    have hb : baseDoubleSwap (2 : Fin 4) = 3 := by decide
    rw [hb] at ha
    have h23 : a.1 2 = a.1 3 := hfix.symm.trans ha
    exact (show (2 : Fin 4) ≠ 3 by decide) (a.1.injective h23)⟩
  refine ⟨x, ⟨z, ?_, ?_⟩⟩
  · intro h
    have hv : a.1 2 = a.1 0 := congrArg Subtype.val h
    exact (show (2 : Fin 4) ≠ 0 by decide) (a.1.injective hv)
  · intro h
    have hv : a.1 2 = t • a.1 0 := congrArg Subtype.val h
    have ha := a.property (0 : Fin 4)
    have hb : baseDoubleSwap (0 : Fin 4) = 1 := by decide
    rw [hb] at ha
    have h21 : a.1 2 = a.1 1 := hv.trans ha
    exact (show (2 : Fin 4) ≠ 1 by decide) (a.1.injective h21)

private def doubleIntertwiningEquiv
    (t : G) (htwo : t ^ 2 = 1) :
    IntertwiningEmbeddings (X := X) t baseDoubleSwap ≃
      DoubleParameters (X := X) t where
  toFun := doubleIntertwiningToParams t
  invFun := doubleParamsToIntertwining t htwo
  left_inv a := by
    apply Subtype.ext
    ext i
    fin_cases i
    · rfl
    ·
      change t • a.1 0 = a.1 1
      have ha := a.property (0 : Fin 4)
      have hb : baseDoubleSwap (0 : Fin 4) = 1 := by decide
      simpa only [hb] using ha
    · rfl
    ·
      change t • a.1 2 = a.1 3
      have ha := a.property (2 : Fin 4)
      have hb : baseDoubleSwap (2 : Fin 4) = 3 := by decide
      simpa only [hb] using ha
  right_inv p := by
    rcases p with ⟨⟨x, hx⟩, ⟨⟨z, hz⟩, hzx, hztx⟩⟩
    rfl

private theorem doubleParameterFiber_ncard
    (t : G) (x : movedBy (X := X) t) :
    Nat.card {z : movedBy (X := X) t //
      z ≠ x ∧ z ≠ movedImage t x} =
      Nat.card (movedBy (X := X) t) - 2 := by
  classical
  letI : Fintype (movedBy (X := X) t) := Fintype.ofFinite _
  calc
    Nat.card {z : movedBy (X := X) t //
        z ≠ x ∧ z ≠ movedImage t x} =
        Fintype.card {z : movedBy (X := X) t //
          z ≠ x ∧ z ≠ movedImage t x} :=
      Nat.card_eq_fintype_card
    _ = Fintype.card (movedBy (X := X) t) -
        Fintype.card {z : movedBy (X := X) t //
          z = x ∨ z = movedImage t x} := by
      simpa only [not_or] using
        (Fintype.card_subtype_compl
          (fun z : movedBy (X := X) t =>
            z = x ∨ z = movedImage t x))
    _ = Fintype.card (movedBy (X := X) t) - 2 := by
      have hpair : Fintype.card {z : movedBy (X := X) t //
          z = x ∨ z = movedImage t x} = 2 :=
        Fintype.card_subtype_eq_or_eq_of_ne (movedImage_ne t x).symm
      rw [hpair]
    _ = Nat.card (movedBy (X := X) t) - 2 := by
      rw [Nat.card_eq_fintype_card]

private theorem doubleParameters_ncard (t : G) :
    Nat.card (DoubleParameters (X := X) t) =
      Nat.card (movedBy (X := X) t) *
        (Nat.card (movedBy (X := X) t) - 2) := by
  classical
  letI : Fintype (movedBy (X := X) t) := Fintype.ofFinite _
  letI : ∀ x : movedBy (X := X) t,
      Fintype {z : movedBy (X := X) t //
        z ≠ x ∧ z ≠ movedImage t x} := fun _ => Fintype.ofFinite _
  unfold DoubleParameters
  rw [Nat.card_sigma]
  simp_rw [doubleParameterFiber_ncard]
  simp [Nat.card_eq_fintype_card]

theorem doubleIntertwining_ncard
    (t : G) (htwo : t ^ 2 = 1) :
    Nat.card (IntertwiningEmbeddings (X := X) t baseDoubleSwap) =
      (Fintype.card X - (MulAction.fixedBy X t).ncard) *
        (Fintype.card X - (MulAction.fixedBy X t).ncard - 2) := by
  calc
    Nat.card (IntertwiningEmbeddings (X := X) t baseDoubleSwap) =
        Nat.card (DoubleParameters (X := X) t) :=
      Nat.card_congr (doubleIntertwiningEquiv (X := X) t htwo)
    _ = Nat.card (movedBy (X := X) t) *
        (Nat.card (movedBy (X := X) t) - 2) :=
      doubleParameters_ncard t
    _ = (Fintype.card X - (MulAction.fixedBy X t).ncard) *
        (Fintype.card X - (MulAction.fixedBy X t).ncard - 2) := by
      rw [Nat.card_coe_set_eq, movedBy_ncard]

private theorem sharpSingleInvolution_smul_apply
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hcard : Nat.card G = (Fintype.card X).descFactorial 4)
    (e : Fin 4 ↪ X) (i : Fin 4) :
    sharpSingleInvolution h4 hcard e • e i = e (baseSingleSwap i) := by
  change sharpLift h4 hcard e baseSingleSwap • e i = e (baseSingleSwap i)
  exact sharpLift_smul_apply h4 hcard e baseSingleSwap i

private theorem sharpDoubleInvolution_smul_apply
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hcard : Nat.card G = (Fintype.card X).descFactorial 4)
    (e : Fin 4 ↪ X) (i : Fin 4) :
    sharpDoubleInvolution h4 hcard e • e i = e (baseDoubleSwap i) := by
  change sharpLift h4 hcard e baseDoubleSwap • e i = e (baseDoubleSwap i)
  exact sharpLift_smul_apply h4 hcard e baseDoubleSwap i

private theorem sharpSingle_centralizer_ncard
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hcard : Nat.card G = (Fintype.card X).descFactorial 4)
    (e : Fin 4 ↪ X) :
    Nat.card (Subgroup.centralizer
        {sharpSingleInvolution h4 hcard e}) =
      (MulAction.fixedBy X
          (sharpSingleInvolution h4 hcard e)).ncard.descFactorial 2 *
        (Fintype.card X - (MulAction.fixedBy X
          (sharpSingleInvolution h4 hcard e)).ncard) := by
  calc
    Nat.card (Subgroup.centralizer
        {sharpSingleInvolution h4 hcard e}) =
        Nat.card (IntertwiningEmbeddings (X := X)
          (sharpSingleInvolution h4 hcard e) baseSingleSwap) :=
      centralizer_ncard_eq_intertwining h4 hcard e _ _
        (sharpSingleInvolution_smul_apply h4 hcard e)
    _ = _ := singleIntertwining_ncard _
      (sharpSingleInvolution_sq h4 hcard e)

private theorem sharpDouble_centralizer_ncard
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hcard : Nat.card G = (Fintype.card X).descFactorial 4)
    (e : Fin 4 ↪ X) :
    Nat.card (Subgroup.centralizer
        {sharpDoubleInvolution h4 hcard e}) =
      (Fintype.card X - (MulAction.fixedBy X
          (sharpDoubleInvolution h4 hcard e)).ncard) *
        (Fintype.card X - (MulAction.fixedBy X
          (sharpDoubleInvolution h4 hcard e)).ncard - 2) := by
  calc
    Nat.card (Subgroup.centralizer
        {sharpDoubleInvolution h4 hcard e}) =
        Nat.card (IntertwiningEmbeddings (X := X)
          (sharpDoubleInvolution h4 hcard e) baseDoubleSwap) :=
      centralizer_ncard_eq_intertwining h4 hcard e _ _
        (sharpDoubleInvolution_smul_apply h4 hcard e)
    _ = _ := doubleIntertwining_ncard _
      (sharpDoubleInvolution_sq h4 hcard e)

private theorem sharp_four_degree_eq_eleven_of_eight_le
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hcard : Nat.card G = (Fintype.card X).descFactorial 4)
    (hX : 8 ≤ Fintype.card X) :
    Fintype.card X = 11 := by
  classical
  let e : Fin 4 ↪ X := Classical.choice
    (Function.Embedding.nonempty_iff_card_le.mpr (by
      simpa using (show 4 ≤ Fintype.card X by omega)))
  let s := sharpSingleInvolution h4 hcard e
  let d := sharpDoubleInvolution h4 hcard e
  obtain ⟨q, hq⟩ :=
    involution_conjugate_sharpDouble h4 hcard hX e s
      (sharpSingleInvolution_sq h4 hcard e)
      (sharpSingleInvolution_ne_one h4 hcard e)
  have hfix : (MulAction.fixedBy X s).ncard =
      (MulAction.fixedBy X d).ncard :=
    fixedBy_ncard_eq_of_conjugate s d q hq
  have hcent : Nat.card (Subgroup.centralizer {s}) =
      Nat.card (Subgroup.centralizer {d}) :=
    centralizer_ncard_eq_of_conjugate s d q hq
  have heq :
      (MulAction.fixedBy X s).ncard.descFactorial 2 *
          (Fintype.card X - (MulAction.fixedBy X s).ncard) =
        (Fintype.card X - (MulAction.fixedBy X s).ncard) *
          (Fintype.card X - (MulAction.fixedBy X s).ncard - 2) := by
    calc
      (MulAction.fixedBy X s).ncard.descFactorial 2 *
          (Fintype.card X - (MulAction.fixedBy X s).ncard) =
          Nat.card (Subgroup.centralizer {s}) := by
        simpa [s] using (sharpSingle_centralizer_ncard h4 hcard e).symm
      _ = Nat.card (Subgroup.centralizer {d}) := hcent
      _ = (Fintype.card X - (MulAction.fixedBy X d).ncard) *
          (Fintype.card X - (MulAction.fixedBy X d).ncard - 2) := by
        simpa [d] using sharpDouble_centralizer_ncard h4 hcard e
      _ = (Fintype.card X - (MulAction.fixedBy X s).ncard) *
          (Fintype.card X - (MulAction.fixedBy X s).ncard - 2) := by
        rw [hfix]
  have hf := involution_fixedBy_ncard_eq_two_or_three h4 hcard hX e s
    (sharpSingleInvolution_sq h4 hcard e)
    (sharpSingleInvolution_ne_one h4 hcard e)
  have hmpos : 0 < Fintype.card X - (MulAction.fixedBy X s).ncard := by
    rcases hf with hf | hf <;> omega
  have hcore : (MulAction.fixedBy X s).ncard.descFactorial 2 =
      Fintype.card X - (MulAction.fixedBy X s).ncard - 2 := by
    apply Nat.eq_of_mul_eq_mul_left hmpos
    simpa [Nat.mul_comm] using heq
  rcases hf with hf | hf
  · rw [hf] at hcore
    norm_num [Nat.descFactorial] at hcore
    omega
  · rw [hf] at hcore
    norm_num [Nat.descFactorial] at hcore
    omega

theorem sharp_five_degree_le_twelve
    (h5 : MulAction.IsMultiplyPretransitive G X 5)
    (hcard : Nat.card G = (Fintype.card X).descFactorial 5) :
    Fintype.card X ≤ 12 := by
  classical
  have hdescPos : 0 < (Fintype.card X).descFactorial 5 := by
    rw [← hcard]
    exact Nat.card_pos
  have hX5 : 5 ≤ Fintype.card X := Nat.descFactorial_pos.mp hdescPos
  have hX5nat : 5 ≤ Nat.card X := by
    simpa [Nat.card_eq_fintype_card] using hX5
  let _ : MulAction.IsMultiplyPretransitive G X 5 := h5
  have h2 : MulAction.IsMultiplyPretransitive G X 2 :=
    MulAction.isMultiplyPretransitive_of_le (by omega) hX5nat
  let _ : MulAction.IsMultiplyPretransitive G X 2 := h2
  let _ : MulAction.IsPretransitive G X :=
    MulAction.isPretransitive_of_is_two_pretransitive
  let x : X := Classical.choice
    (Fintype.card_pos_iff.mp (show 0 < Fintype.card X by omega))
  let K : Subgroup G := MulAction.stabilizer G x
  let Y := SubMulAction.ofStabilizer G x
  letI : Fintype Y := Fintype.ofFinite _
  have h4K : MulAction.IsMultiplyPretransitive K Y 4 := by
    simpa [K, Y] using
      (SubMulAction.ofStabilizer.isMultiplyPretransitive
        (G := G) (α := X) (n := 4) (a := x)).mp h5
  have hYcard : Fintype.card Y = Fintype.card X - 1 := by
    rw [← Nat.card_eq_fintype_card]
    simpa [Y, Nat.card_eq_fintype_card] using
      SubMulAction.nat_card_ofStabilizer_eq G x
  have hindex : K.index = Nat.card X := by
    simpa [K] using MulAction.index_stabilizer_of_transitive G x
  have hmul := K.card_mul_index
  rw [hindex, hcard] at hmul
  have hdesc :
      (Fintype.card X).descFactorial 5 =
        Fintype.card X *
          (Fintype.card X - 1).descFactorial 4 := by
    nth_rewrite 1 [show Fintype.card X =
      (Fintype.card X - 1) + 1 by omega]
    rw [Nat.succ_descFactorial_succ]
    rw [Nat.sub_add_cancel (show 1 ≤ Fintype.card X by omega)]
  have hKcard :
      Nat.card K = (Fintype.card Y).descFactorial 4 := by
    rw [hYcard]
    apply Nat.eq_of_mul_eq_mul_left
      (show 0 < Fintype.card X by omega)
    calc
      Fintype.card X * Nat.card K =
          Nat.card K * Fintype.card X := Nat.mul_comm _ _
      _ = Nat.card K * Nat.card X := by
        congr 1
        exact Nat.card_eq_fintype_card.symm
      _ = (Fintype.card X).descFactorial 5 := hmul
      _ = Fintype.card X *
          (Fintype.card X - 1).descFactorial 4 := hdesc
  by_cases hY8 : 8 ≤ Fintype.card Y
  · have hYeq : Fintype.card Y = 11 :=
      sharp_four_degree_eq_eleven_of_eight_le h4K hKcard hY8
    rw [hYcard] at hYeq
    omega
  · rw [hYcard] at hY8
    omega

end FiveTransitive.Research.SharpFourDegreeCompletion

end CFSG
