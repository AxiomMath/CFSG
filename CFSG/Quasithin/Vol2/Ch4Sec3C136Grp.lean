module

public import CFSG.Quasithin.Vol2.Ch4Sec3C136Off3

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

section Coords

variable {Q : Subgroup G} {F : Type} [Field F] (β : ↥Q ≃* Multiplicative (Fin 2 → Fin 3 → F))

@[expose] def crd (u : ↥Q) : Fin 2 → Fin 3 → F := Multiplicative.toAdd (β u)

@[expose] def elt (v : Fin 2 → Fin 3 → F) : ↥Q := β.symm (Multiplicative.ofAdd v)

theorem crd_elt (v : Fin 2 → Fin 3 → F) : crd β (elt β v) = v := by
  simp [crd, elt]

theorem elt_crd (u : ↥Q) : elt β (crd β u) = u := by
  simp [crd, elt]

theorem crd_mul (u u' : ↥Q) : crd β (u * u') = crd β u + crd β u' := by
  simp [crd]

theorem crd_injective : Function.Injective (crd β) := fun u u' h => by
  rw [← elt_crd β u, h, elt_crd]

theorem elt_add (v w : Fin 2 → Fin 3 → F) : elt β (v + w) = elt β v * elt β w := by
  apply crd_injective β
  rw [crd_mul, crd_elt, crd_elt, crd_elt]

@[expose] def cAct (g : ↥(Subgroup.normalizer (Q : Set G))) (v : Fin 2 → Fin 3 → F) :
    Fin 2 → Fin 3 → F :=
  crd β ⟨g * (elt β v : G) * (g : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp g.2 _).mp (elt β v).2⟩

theorem cAct_crd (g : ↥(Subgroup.normalizer (Q : Set G))) (u : ↥Q) :
    cAct β g (crd β u) =
      crd β ⟨g * (u : G) * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp g.2 _).mp u.2⟩ := by
  simp only [cAct, elt_crd]

theorem cAct_mul (g h : ↥(Subgroup.normalizer (Q : Set G))) (v : Fin 2 → Fin 3 → F) :
    cAct β (g * h) v = cAct β g (cAct β h v) := by
  rw [cAct, cAct, cAct]
  congr 1
  apply Subtype.ext
  simp only [elt_crd, Subgroup.coe_mul, mul_inv_rev]
  group

theorem cAct_one (v : Fin 2 → Fin 3 → F) : cAct β 1 v = v := by
  rw [cAct]
  simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one, Subtype.coe_eta, crd_elt]

@[expose] noncomputable def cHom :
    ↥(Subgroup.normalizer (Q : Set G)) →* Equiv.Perm (Fin 2 → Fin 3 → F) where
  toFun g :=
    { toFun := cAct β g
      invFun := cAct β g⁻¹
      left_inv := fun v => by rw [← cAct_mul, inv_mul_cancel, cAct_one]
      right_inv := fun v => by rw [← cAct_mul, mul_inv_cancel, cAct_one] }
  map_one' := Equiv.ext fun v => cAct_one β v
  map_mul' := fun g h => Equiv.ext fun v => cAct_mul β g h v

theorem cHom_apply (g : ↥(Subgroup.normalizer (Q : Set G))) (v : Fin 2 → Fin 3 → F) :
    cHom β g v = cAct β g v := rfl

theorem cHom_mem_addPerms (g : ↥(Subgroup.normalizer (Q : Set G))) : cHom β g ∈ addPerms F := by
  intro v w
  rw [cHom_apply, cHom_apply, cHom_apply, cAct, cAct, cAct, ← crd_mul]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, elt_add]
  group

theorem cHom_eq_one_iff (g : ↥(Subgroup.normalizer (Q : Set G))) :
    cHom β g = 1 ↔ (g : G) ∈ Subgroup.centralizer (Q : Set G) := by
  constructor
  · intro h
    refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
    have h1 := congrArg (fun f : Equiv.Perm (Fin 2 → Fin 3 → F) => f (crd β ⟨u, hu⟩)) h
    simp only [cHom_apply, cAct_crd, Equiv.Perm.one_apply] at h1
    have h2 : (g : G) * u * (g : G)⁻¹ = u := congrArg Subtype.val (crd_injective β h1)
    calc u * (g : G) = (g : G) * u * (g : G)⁻¹ * g := by rw [h2]
      _ = g * u := by group
  · intro h
    refine Equiv.ext fun v => ?_
    rw [cHom_apply, Equiv.Perm.one_apply, cAct]
    conv_rhs => rw [← crd_elt β v]
    congr 1
    apply Subtype.ext
    show (g : G) * (elt β v : G) * (g : G)⁻¹ = elt β v
    rw [← Subgroup.mem_centralizer_iff.mp h _ (elt β v).2]
    group

end Coords

section Bound

variable [Finite G] {G₀ L : Subgroup G} {F : Type} [Field F] [Finite F] [CharP F 2]
  {α : ↥L →* ↥(StatedSL 3 F)}

omit [Finite G] [Finite F] [CharP F 2] in
theorem cHom_of_mem {Q : Subgroup G} {β : ↥Q ≃* Multiplicative (Fin 2 → Fin 3 → F)}
    (hβ : ∀ (a : ↥L) (u v : ↥Q), (v : G) = a * u * a⁻¹ → ∀ i : Fin 2,
      Multiplicative.toAdd (β v) i =
        ((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (Multiplicative.toAdd (β u) i))
    (l : ↥(Subgroup.normalizer (Q : Set G))) (hl : (l : G) ∈ L)
    (v : Fin 2 → Fin 3 → F) :
    cHom β l v = dact ((α ⟨l, hl⟩ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) v := by
  funext i
  rw [cHom_apply, cAct]
  have h := hβ ⟨l, hl⟩ (elt β v) ⟨_, (Subgroup.mem_normalizer_iff.mp l.2 _).mp (elt β v).2⟩ rfl i
  rw [show Multiplicative.toAdd (β (elt β v)) = v from crd_elt β v] at h
  exact h

theorem card_le_of_c136 {Q : Subgroup G} (hα : IsModO2Surj L α) (hLG : L ≤ G₀)
    (hGL : G₀ ≤ Subgroup.normalizer (L : Set G)) (hQL : Q ≤ L)
    (hGN : G₀ ≤ Subgroup.normalizer (Q : Set G))
    (hQ : G₀ ⊓ Subgroup.centralizer (Q : Set G) = Q)
    (β : ↥Q ≃* Multiplicative (Fin 2 → Fin 3 → F))
    (hβ : ∀ (a : ↥L) (u v : ↥Q), (v : G) = a * u * a⁻¹ → ∀ i : Fin 2,
      Multiplicative.toAdd (β v) i =
        ((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (Multiplicative.toAdd (β u) i))
    {B : Subgroup G} (hBG : B ≤ G₀) (hB : IsElemAbelian 2 B) :
    Nat.card B ≤ Nat.card F ^ 6 ∧
      (Nat.card B = Nat.card F ^ 6 →
        B = Q ∨ (B ≤ L ∧ Nat.card ↥(B ⊓ Q) = Nat.card F ^ 4 ∧
          Nat.card ↥(Q ⊓ Subgroup.centralizer (B : Set G)) = Nat.card F ^ 4)) := by
  classical
  set N := Subgroup.normalizer (Q : Set G) with hN
  have hBN : B ≤ N := hBG.trans hGN
  have hLN : L ≤ N := hLG.trans hGN
  set B' := B.subgroupOf N with hB'
  set φ := (cHom β).comp B'.subtype with hφ
  set E := φ.range with hE
  have hcardB : Nat.card B = Nat.card B' :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv).symm
  have hadd : E ≤ addPerms F := by
    rintro _ ⟨b, rfl⟩
    exact cHom_mem_addPerms β _
  have hcommB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    have := hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hcomm : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    exact hcommB _ x.2 _ y.2
  have hinv : ∀ e ∈ E, e * e = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_mul]
    have h1 : x * x = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      have := hB.2 _ x.2
      rw [sq] at this
      exact this
    rw [h1, map_one]
  let e₀ := specialLinearGroupEquivStatedSL 3 F
  have hnorm : ∀ e ∈ E, NormalizesDact ⇑e := by
    rintro _ ⟨b, rfl⟩ X
    obtain ⟨l, hl⟩ := hα.1 (e₀ X)
    have hbN : ((b : ↥N) : G) ∈ N := (b : ↥N).2
    have hbG : ((b : ↥N) : G) ∈ G₀ := hBG b.2
    have hlbl : ((b : ↥N) : G) * l * ((b : ↥N) : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hGL hbG) _).mp l.2
    refine ⟨e₀.symm (α ⟨_, hlbl⟩), fun v => ?_⟩
    have hX : (X : Matrix (Fin 3) (Fin 3) F) =
        ((α l : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      rw [hl]
      exact (specialLinearGroupEquivStatedSL_coe 3 F X).symm
    have hY : ((e₀.symm (α ⟨_, hlbl⟩) : Matrix.SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = ((α ⟨_, hlbl⟩ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      have h1 := specialLinearGroupEquivStatedSL_coe 3 F (e₀.symm (α ⟨_, hlbl⟩))
      rw [MulEquiv.apply_symm_apply] at h1
      exact h1.symm
    rw [hX, hY]
    let lN : ↥N := ⟨l, hLN l.2⟩
    let mN : ↥N := ⟨_, hLN hlbl⟩
    have h1 : ∀ w, cHom β lN w = dact ((α l : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) w :=
      fun w => cHom_of_mem hβ lN l.2 w
    have h2 : ∀ w, cHom β mN w =
        dact ((α ⟨_, hlbl⟩ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) w :=
      fun w => cHom_of_mem hβ mN hlbl w
    have h3 : (b : ↥N) * lN = mN * (b : ↥N) := by
      apply Subtype.ext
      show ((b : ↥N) : G) * l = ((b : ↥N) : G) * l * ((b : ↥N) : G)⁻¹ * ((b : ↥N) : G)
      group
    show cHom β (b : ↥N) (dact _ v) = dact _ (cHom β (b : ↥N) v)
    rw [← h1, ← h2, ← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← map_mul, ← map_mul, h3]
  obtain ⟨hbound, heq⟩ := card_mul_card_fixPts_le hadd hnorm hcomm hinv
  have hkerQ : ∀ b : ↥B', b ∈ φ.ker → (((b : ↥N) : G)) ∈ Q := by
    intro b hb
    have h1 : cHom β (b : ↥N) = 1 := hb
    rw [cHom_eq_one_iff] at h1
    rw [← hQ]
    exact ⟨hBG b.2, h1⟩
  have hkerfix : Nat.card φ.ker ≤
      Nat.card (fixPts (E : Set (Equiv.Perm (Fin 2 → Fin 3 → F)))) := by
    refine Nat.card_le_card_of_injective
      (fun b : ↥φ.ker => (⟨crd β ⟨_, hkerQ b.1 b.2⟩, ?_⟩ :
        ↥(fixPts (E : Set (Equiv.Perm (Fin 2 → Fin 3 → F)))))) fun x y hxy => ?_
    · rintro _ ⟨c, rfl⟩
      show cHom β (c : ↥N) (crd β _) = _
      rw [cHom_apply, cAct_crd]
      congr 1
      apply Subtype.ext
      show ((c : ↥N) : G) * (((b : ↥B') : ↥N) : G) * ((c : ↥N) : G)⁻¹ = (((b : ↥B') : ↥N) : G)
      have hcb : ((c : ↥N) : G) * (((b : ↥B') : ↥N) : G) =
          (((b : ↥B') : ↥N) : G) * ((c : ↥N) : G) := hcommB _ c.2 _ (b : ↥B').2
      rw [hcb]
      group
    · have h1 := crd_injective β (congrArg Subtype.val hxy)
      have h2 : ((((x : ↥φ.ker) : ↥B') : ↥N) : G) = ((((y : ↥φ.ker) : ↥B') : ↥N) : G) :=
        congrArg (fun z : ↥Q => (z : G)) h1
      exact Subtype.ext (Subtype.ext (Subtype.ext h2))
  have hcardB' : Nat.card B' = Nat.card φ.ker * Nat.card E := by
    rw [hE, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv,
      Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker, mul_comm]
  have hle : Nat.card B ≤ Nat.card E *
      Nat.card (fixPts (E : Set (Equiv.Perm (Fin 2 → Fin 3 → F)))) := by
    rw [hcardB, hcardB', mul_comm]
    exact Nat.mul_le_mul_left _ hkerfix
  refine ⟨hle.trans hbound, fun hB6 => ?_⟩
  have hE6 : Nat.card E * Nat.card (fixPts (E : Set (Equiv.Perm (Fin 2 → Fin 3 → F)))) =
      Nat.card F ^ 6 := le_antisymm hbound (hB6 ▸ hle)
  obtain ⟨hdiag, hEcases⟩ := heq hE6
  have hBL : B ≤ L := by
    intro b hb
    obtain ⟨X, hX⟩ := hdiag ⟨⟨⟨b, hBN hb⟩, hb⟩, rfl⟩
    obtain ⟨l, hl⟩ := hα.1 (e₀ X)
    let lN : ↥N := ⟨l, hLN l.2⟩
    have h1 : cHom β (⟨b, hBN hb⟩ : ↥N) = cHom β lN := by
      refine Equiv.ext fun v => ?_
      rw [show cHom β (⟨b, hBN hb⟩ : ↥N) v = φ ⟨⟨b, hBN hb⟩, hb⟩ v from rfl, hX v,
        cHom_of_mem hβ lN l.2 v, hl]
      rfl
    have h2 : cHom β (lN⁻¹ * ⟨b, hBN hb⟩) = 1 := by
      rw [map_mul, h1, map_inv, inv_mul_cancel]
    rw [cHom_eq_one_iff] at h2
    have h3 : (l : G)⁻¹ * b ∈ Q := by
      rw [← hQ]
      exact ⟨G₀.mul_mem (G₀.inv_mem (hLG l.2)) (hBG hb), h2⟩
    have h4 : (l : G)⁻¹ * b ∈ L := hQL h3
    have h5 : b = l * ((l : G)⁻¹ * b) := by group
    rw [h5]
    exact L.mul_mem l.2 h4
  rcases hEcases with hEbot | hfix4
  ·
    left
    have hBQ : B ≤ Q := by
      intro b hb
      have h1 : φ ⟨⟨b, hBN hb⟩, hb⟩ = 1 := by
        have : φ ⟨⟨b, hBN hb⟩, hb⟩ ∈ E := ⟨_, rfl⟩
        rw [hEbot] at this
        exact this
      exact hkerQ ⟨⟨b, hBN hb⟩, hb⟩ h1
    have hQcard : Nat.card Q = Nat.card F ^ 6 := by
      rw [Nat.card_congr (β.toEquiv.trans Multiplicative.toAdd), card_pairs]
    exact Subgroup.eq_of_le_of_card_ge hBQ (by rw [hQcard, hB6])
  · right
    have hCB : Nat.card ↥(Q ⊓ Subgroup.centralizer (B : Set G)) =
        Nat.card (fixPts (E : Set (Equiv.Perm (Fin 2 → Fin 3 → F)))) := by
      refine le_antisymm ?_ ?_
      · refine Nat.card_le_card_of_injective
          (fun u : ↥(Q ⊓ Subgroup.centralizer (B : Set G)) => (⟨crd β ⟨u, u.2.1⟩, ?_⟩ :
            ↥(fixPts (E : Set (Equiv.Perm (Fin 2 → Fin 3 → F)))))) fun x y hxy => ?_
        · rintro _ ⟨c, rfl⟩
          show cHom β (c : ↥N) (crd β _) = _
          rw [cHom_apply, cAct_crd]
          congr 1
          apply Subtype.ext
          show ((c : ↥N) : G) * (u : G) * ((c : ↥N) : G)⁻¹ = u
          have hcu : ((c : ↥N) : G) * (u : G) = (u : G) * ((c : ↥N) : G) :=
            Subgroup.mem_centralizer_iff.mp u.2.2 _ c.2
          rw [hcu]
          group
        · have h1 := crd_injective β (congrArg Subtype.val hxy)
          exact Subtype.ext (congrArg (fun z : ↥Q => (z : G)) h1)
      · refine Nat.card_le_card_of_injective
          (fun v : ↥(fixPts (E : Set (Equiv.Perm (Fin 2 → Fin 3 → F)))) =>
            (⟨elt β v.1, (elt β v.1).2, ?_⟩ : ↥(Q ⊓ Subgroup.centralizer (B : Set G))))
          fun x y hxy => ?_
        · refine Subgroup.mem_centralizer_iff.mpr fun b hb => ?_
          have h1 := v.2 _ ⟨⟨⟨b, hBN hb⟩, hb⟩, rfl⟩
          have h2 : cAct β (⟨b, hBN hb⟩ : ↥N) v.1 = v.1 := h1
          rw [cAct] at h2
          conv_rhs at h2 => rw [← crd_elt β v.1]
          have h3 := congrArg Subtype.val (crd_injective β h2)
          have h4 : b * (elt β v.1 : G) * b⁻¹ = elt β v.1 := h3
          calc b * (elt β v.1 : G) = b * (elt β v.1 : G) * b⁻¹ * b := by group
            _ = elt β v.1 * b := by rw [h4]
        · have h1 : elt β x.1 = elt β y.1 :=
            Subtype.ext (congrArg (fun z : ↥(Q ⊓ Subgroup.centralizer (B : Set G)) => (z : G)) hxy)
          have h2 := congrArg (crd β) h1
          rw [crd_elt, crd_elt] at h2
          exact Subtype.ext h2
    refine ⟨hBL, ?_, by rw [hCB, hfix4]⟩
    have hEcard : Nat.card E = Nat.card F ^ 2 := by
      rw [hfix4] at hE6
      have hq : 0 < Nat.card F ^ 4 := pow_pos Nat.card_pos 4
      have : Nat.card E * Nat.card F ^ 4 = Nat.card F ^ 2 * Nat.card F ^ 4 := by
        rw [hE6]; ring
      exact Nat.eq_of_mul_eq_mul_right hq this
    have hker : Nat.card φ.ker = Nat.card F ^ 4 := by
      rw [hcardB, hcardB', hEcard] at hB6
      have hq : 0 < Nat.card F ^ 2 := pow_pos Nat.card_pos 2
      have : Nat.card φ.ker * Nat.card F ^ 2 = Nat.card F ^ 4 * Nat.card F ^ 2 := by
        rw [hB6]; ring
      exact Nat.eq_of_mul_eq_mul_right hq this
    have hQab : ∀ {x y : G}, x ∈ Q → y ∈ Q → x * y = y * x := by
      intro x y hx hy
      have h1 : β (⟨x, hx⟩ * ⟨y, hy⟩) = β (⟨y, hy⟩ * ⟨x, hx⟩) := by
        rw [map_mul, map_mul, mul_comm]
      exact congrArg Subtype.val (β.injective h1)
    have h1 : Nat.card φ.ker ≤ Nat.card ↥(B ⊓ Q) :=
      Nat.card_le_card_of_injective
        (fun x : ↥φ.ker => (⟨(((x : ↥B') : ↥N) : G), (x : ↥B').2, hkerQ x x.2⟩ : ↥(B ⊓ Q)))
        (fun x y hxy => Subtype.ext (Subtype.ext (Subtype.ext
          (congrArg (fun z : ↥(B ⊓ Q) => (z : G)) hxy))))
    have h2 : Nat.card ↥(B ⊓ Q) ≤ Nat.card φ.ker := by
      refine Nat.card_le_card_of_injective
        (fun y : ↥(B ⊓ Q) => (⟨⟨⟨y, hBN y.2.1⟩, y.2.1⟩, ?_⟩ : ↥φ.ker)) ?_
      · show cHom β _ = 1
        rw [cHom_eq_one_iff]
        exact Subgroup.mem_centralizer_iff.mpr fun u hu => hQab hu y.2.2
      · intro x y hxy
        exact Subtype.ext (congrArg (fun z : ↥φ.ker => (((z : ↥B') : ↥N) : G)) hxy)
    rw [← hker]
    exact le_antisymm h2 h1

end Bound

end CFSG.Quasithin.H13.Ch4
