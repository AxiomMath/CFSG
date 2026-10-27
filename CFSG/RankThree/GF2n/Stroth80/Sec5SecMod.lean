module

public import CFSG.RankThree.GF2n.Stroth80.Sec5Defs
public import CFSG.ClassicalGroups.F2Fixed

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)
open CFSG.ClassicalGroups.F2Fixed (fixedSub mem_fixedSub)
open scoped commutatorElement

variable {G : Type} [Group G]

structure SecHyp (R P I : Subgroup G) : Prop where
  le : I ≤ P
  comm : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ I
  sq : ∀ x ∈ P, x ^ 2 ∈ I
  normP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P
  normI : ∀ r ∈ R, ∀ x ∈ I, r * x * r⁻¹ ∈ I

structure IsSecMod (R P I : Subgroup G) (M : Type) [AddCommGroup M] [DistribMulAction ↥R M]
    (κ : ↥P →* Multiplicative M) : Prop where
  surj : Function.Surjective κ
  ker : ∀ x : ↥P, κ x = 1 ↔ (x : G) ∈ I
  act : ∀ (r : ↥R) (x y : ↥P), (y : G) = (r : G) * x * (r : G)⁻¹ →
    κ y = Multiplicative.ofAdd (r • Multiplicative.toAdd (κ x))
  two : ∀ a : M, a + a = 0

theorem SecHyp.of_isOppDecomp {R P I L₁ L₂ A₁ A₂ : Subgroup G}
    (hd : IsOppDecomp P I L₁ L₂ A₁ A₂) (hP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P)
    (hI : ∀ r ∈ R, ∀ x ∈ I, r * x * r⁻¹ ∈ I) : SecHyp R P I := by
  obtain ⟨hIA₁, hA₁P, -, -, -, -, hcomm, hsq, -, -⟩ := hd
  exact ⟨hIA₁.trans hA₁P, hcomm, hsq, hP, hI⟩

theorem exists_sectionModule {R P I : Subgroup G} (h : SecHyp R P I) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : DistribMulAction ↥R M)
      (κ : ↥P →* Multiplicative M), IsSecMod R P I M κ := by
  haveI hN : (I.subgroupOf P).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hc := h.comm g g.2 n n.2
    have e : ((g * n * g⁻¹ : ↥P) : G) = ⁅(g : G), (n : G)⁆ * n := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [e]
    exact I.mul_mem hc hn⟩
  letI : CommGroup (↥P ⧸ I.subgroupOf P) :=
    { (inferInstance : Group (↥P ⧸ I.subgroupOf P)) with
      mul_comm := fun u v => by
        induction u using QuotientGroup.induction_on with
        | H x =>
          induction v using QuotientGroup.induction_on with
          | H y =>
            rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
              Subgroup.mem_subgroupOf]
            have e : (((x * y)⁻¹ * (y * x) : ↥P) : G) = ⁅(y : G)⁻¹, (x : G)⁻¹⁆ := by
              simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
              group
            rw [e]
            exact h.comm _ (P.inv_mem y.2) _ (P.inv_mem x.2) }
  let cP : ↥R → ↥P →* ↥P := fun r =>
    { toFun := fun x => ⟨(r : G) * x * (r : G)⁻¹, h.normP r r.2 x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  let cQ : ↥R → (↥P ⧸ I.subgroupOf P) →* (↥P ⧸ I.subgroupOf P) := fun r =>
    QuotientGroup.map (I.subgroupOf P) (I.subgroupOf P) (cP r) (fun x hx => by
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      exact h.normI r r.2 x (Subgroup.mem_subgroupOf.mp hx))
  have cQ_one : ∀ q : ↥P ⧸ I.subgroupOf P, cQ 1 q = q := fun q => by
    induction q using QuotientGroup.induction_on with
    | H x => exact congrArg _ (Subtype.ext (by simp [cP]))
  have cQ_mul : ∀ (r s : ↥R) (q : ↥P ⧸ I.subgroupOf P), cQ (r * s) q = cQ r (cQ s q) :=
    fun r s q => by
      induction q using QuotientGroup.induction_on with
      | H x => exact congrArg _ (Subtype.ext (by simp [cP, mul_assoc]))
  let act : DistribMulAction ↥R (Additive (↥P ⧸ I.subgroupOf P)) :=
    { smul := fun r a => Additive.ofMul (cQ r (Additive.toMul a))
      one_smul := fun a => cQ_one (Additive.toMul a)
      mul_smul := fun r s a => cQ_mul r s (Additive.toMul a)
      smul_zero := fun r => map_one (cQ r)
      smul_add := fun r a b => map_mul (cQ r) (Additive.toMul a) (Additive.toMul b) }
  let κ : ↥P →* Multiplicative (Additive (↥P ⧸ I.subgroupOf P)) :=
    { toFun := fun x => Multiplicative.ofAdd (Additive.ofMul (x : ↥P ⧸ I.subgroupOf P))
      map_one' := rfl
      map_mul' := fun x y => rfl }
  refine ⟨Additive (↥P ⧸ I.subgroupOf P), inferInstance, act, κ, ?_, ?_, ?_, ?_⟩
  · intro a
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul (Multiplicative.toAdd a))
    exact ⟨x, hx⟩
  · intro x
    exact (QuotientGroup.eq_one_iff x).trans Subgroup.mem_subgroupOf
  · intro r x y hxy
    have hy : y = cP r x := Subtype.ext hxy
    subst hy
    rfl
  · intro a
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul a)
    have hxx : (x : ↥P ⧸ I.subgroupOf P) * (x : ↥P ⧸ I.subgroupOf P) = 1 := by
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa [sq] using h.sq x x.2
    have h1 : Additive.toMul a * Additive.toMul a = 1 := by
      rw [← hx]
      exact hxx
    exact congrArg Additive.ofMul h1

section Module

variable {R P I : Subgroup G} {M : Type} [AddCommGroup M] [DistribMulAction ↥R M]
  {κ : ↥P →* Multiplicative M}

theorem IsSecMod.eq_iff (hκ : IsSecMod R P I M κ) (x y : ↥P) :
    κ x = κ y ↔ (x : G) * (y : G)⁻¹ ∈ I := by
  have e : κ x = κ y ↔ κ (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, mul_inv_eq_one]
  exact e.trans (hκ.ker (x * y⁻¹))

theorem IsSecMod.finite [Finite ↥P] (hκ : IsSecMod R P I M κ) : Finite M :=
  Finite.of_surjective (fun x : ↥P => Multiplicative.toAdd (κ x)) fun a => by
    obtain ⟨x, hx⟩ := hκ.surj (Multiplicative.ofAdd a)
    exact ⟨x, by show Multiplicative.toAdd (κ x) = a; rw [hx]; rfl⟩

theorem natCard_eq_of_isSecMod (hIP : I ≤ P) (hκ : IsSecMod R P I M κ) :
    Nat.card ↥P = Nat.card ↥I * Nat.card M := by
  have hker : κ.ker = I.subgroupOf P := by
    ext x
    rw [MonoidHom.mem_ker, hκ.ker, Subgroup.mem_subgroupOf]
  have h1 := Subgroup.card_ker_mul_card_of_surjective hκ.surj
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIP).toEquiv,
    Nat.card_congr Multiplicative.toAdd] at h1
  exact h1.symm

theorem mem_fixedSub_iff (hP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P)
    (hκ : IsSecMod R P I M κ) {L : Subgroup G} (hL : L ≤ R) {a : M} :
    a ∈ fixedSub M ((L.subgroupOf R : Subgroup ↥R) : Set ↥R) ↔
      ∃ x : ↥P, κ x = Multiplicative.ofAdd a ∧ ∀ l ∈ L, ⁅l, (x : G)⁆ ∈ I := by
  rw [mem_fixedSub]
  constructor
  · intro ha
    obtain ⟨x, hx⟩ := hκ.surj (Multiplicative.ofAdd a)
    refine ⟨x, hx, fun l hl => ?_⟩
    have hr : (⟨l, hL hl⟩ : ↥R) • a = a := ha _ (Subgroup.mem_subgroupOf.mpr hl)
    have hy := hκ.act ⟨l, hL hl⟩ x ⟨l * x * l⁻¹, hP l (hL hl) x x.2⟩ rfl
    rw [hx, toAdd_ofAdd, hr, ← hx] at hy
    exact (hκ.eq_iff _ x).mp hy
  · rintro ⟨x, hx, hc⟩ r hr
    have hy := hκ.act r x ⟨r * x * r⁻¹, hP r r.2 x x.2⟩ rfl
    have h2 := (hκ.eq_iff ⟨r * x * r⁻¹, hP r r.2 x x.2⟩ x).mpr
      (hc r (Subgroup.mem_subgroupOf.mp hr))
    rw [hy, hx, toAdd_ofAdd] at h2
    exact Multiplicative.ofAdd.injective h2

end Module

@[expose] def secSub {P : Subgroup G} {M : Type} [AddCommGroup M] (κ : ↥P →* Multiplicative M)
    (U : Subgroup G) : AddSubgroup M :=
  Subgroup.toAddSubgroup' ((U.subgroupOf P).map κ)

section SecSub

variable {R P I : Subgroup G} {M : Type} [AddCommGroup M] [DistribMulAction ↥R M]
  {κ : ↥P →* Multiplicative M} {U V : Subgroup G}

theorem mem_secSub {a : M} :
    a ∈ secSub κ U ↔ ∃ x : ↥P, (x : G) ∈ U ∧ κ x = Multiplicative.ofAdd a :=
  Iff.rfl

theorem secSub_mono (h : U ≤ V) : secSub κ U ≤ secSub κ V := by
  intro a ha
  obtain ⟨x, hx, hxa⟩ := mem_secSub.mp ha
  exact mem_secSub.mpr ⟨x, h hx, hxa⟩

theorem toAdd_mem_secSub_iff (hκ : IsSecMod R P I M κ) (hIU : I ≤ U) (x : ↥P) :
    Multiplicative.toAdd (κ x) ∈ secSub κ U ↔ (x : G) ∈ U := by
  rw [mem_secSub]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have h1 : (x : G) * (y : G)⁻¹ ∈ I := (hκ.eq_iff x y).mp hyx.symm
    simpa using U.mul_mem (hIU h1) hy
  · exact fun hx => ⟨x, hx, rfl⟩

theorem secSub_le_secSub_iff (hκ : IsSecMod R P I M κ) (hUP : U ≤ P) (hIV : I ≤ V) :
    secSub κ U ≤ secSub κ V ↔ U ≤ V := by
  refine ⟨fun h u hu => ?_, secSub_mono⟩
  have h1 : Multiplicative.toAdd (κ ⟨u, hUP hu⟩) ∈ secSub κ U := mem_secSub.mpr ⟨_, hu, rfl⟩
  exact (toAdd_mem_secSub_iff hκ hIV ⟨u, hUP hu⟩).mp (h h1)

theorem secSub_inj (hκ : IsSecMod R P I M κ) (hIU : I ≤ U) (hUP : U ≤ P) (hIV : I ≤ V)
    (hVP : V ≤ P) : secSub κ U = secSub κ V ↔ U = V := by
  refine ⟨fun h => le_antisymm ?_ ?_, fun h => h ▸ rfl⟩
  · exact (secSub_le_secSub_iff hκ hUP hIV).mp h.le
  · exact (secSub_le_secSub_iff hκ hVP hIU).mp h.ge

theorem secSub_sup (hUP : U ≤ P) (hVP : V ≤ P) :
    secSub κ (U ⊔ V) = secSub κ U ⊔ secSub κ V := by
  unfold secSub
  rw [Subgroup.subgroupOf_sup hUP hVP, Subgroup.map_sup]
  exact OrderIso.map_sup _ _ _

theorem secSub_inf (hκ : IsSecMod R P I M κ) (hIU : I ≤ U) :
    secSub κ (U ⊓ V) = secSub κ U ⊓ secSub κ V := by
  refine le_antisymm (le_inf (secSub_mono inf_le_left) (secSub_mono inf_le_right)) ?_
  rintro a ⟨ha, hb⟩
  obtain ⟨x, hxU, hxa⟩ := mem_secSub.mp ha
  obtain ⟨y, hyV, hya⟩ := mem_secSub.mp hb
  have h1 : (y : G) * (x : G)⁻¹ ∈ I := (hκ.eq_iff y x).mp (hya.trans hxa.symm)
  have hyU : (y : G) ∈ U := by simpa using U.mul_mem (hIU h1) hxU
  exact mem_secSub.mpr ⟨y, ⟨hyU, hyV⟩, hya⟩

theorem secSub_eq_top (hκ : IsSecMod R P I M κ) : secSub κ P = ⊤ := by
  refine eq_top_iff.mpr fun a _ => ?_
  obtain ⟨x, hx⟩ := hκ.surj (Multiplicative.ofAdd a)
  exact mem_secSub.mpr ⟨x, x.2, hx⟩

theorem secSub_eq_bot (hκ : IsSecMod R P I M κ) : secSub κ I = ⊥ := by
  refine le_antisymm (fun a ha => ?_) bot_le
  obtain ⟨x, hx, hxa⟩ := mem_secSub.mp ha
  rw [AddSubgroup.mem_bot]
  have h1 : κ x = 1 := (hκ.ker x).mpr hx
  exact ofAdd_eq_one.mp (hxa.symm.trans h1)

end SecSub

section Decomp

variable {R P I : Subgroup G} {M : Type} [AddCommGroup M] [DistribMulAction ↥R M]
  {κ : ↥P →* Multiplicative M}

theorem fixedSub_eq_secSub (hP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P)
    (hκ : IsSecMod R P I M κ) {L A : Subgroup G} (hL : L ≤ R)
    (hA : ∀ x ∈ P, (x ∈ A ↔ ∀ l ∈ L, ⁅l, x⁆ ∈ I)) :
    fixedSub M ((L.subgroupOf R : Subgroup ↥R) : Set ↥R) = secSub κ A := by
  ext a
  rw [mem_fixedSub_iff hP hκ hL, mem_secSub]
  constructor
  · rintro ⟨x, hx, hc⟩
    exact ⟨x, (hA x x.2).mpr hc, hx⟩
  · rintro ⟨x, hxA, hx⟩
    exact ⟨x, hx, (hA x x.2).mp hxA⟩

theorem fixedSub_eq_secSub_of_isOppDecomp (hP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P)
    (hκ : IsSecMod R P I M κ) {L₁ L₂ A₁ A₂ : Subgroup G}
    (hd : IsOppDecomp P I L₁ L₂ A₁ A₂) (h₁ : L₁ ≤ R) (h₂ : L₂ ≤ R) :
    fixedSub M ((L₁.subgroupOf R : Subgroup ↥R) : Set ↥R) = secSub κ A₁ ∧
      fixedSub M ((L₂.subgroupOf R : Subgroup ↥R) : Set ↥R) = secSub κ A₂ := by
  obtain ⟨-, -, -, -, -, -, -, -, hL₁, hL₂⟩ := hd
  exact ⟨fixedSub_eq_secSub hP hκ h₁ hL₁, fixedSub_eq_secSub hP hκ h₂ hL₂⟩

theorem isCompl_fixedSub_of_isOppDecomp (hP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P)
    (hκ : IsSecMod R P I M κ) {L₁ L₂ A₁ A₂ : Subgroup G}
    (hd : IsOppDecomp P I L₁ L₂ A₁ A₂) (h₁ : L₁ ≤ R) (h₂ : L₂ ≤ R) :
    IsCompl (fixedSub M ((L₁.subgroupOf R : Subgroup ↥R) : Set ↥R))
      (fixedSub M ((L₂.subgroupOf R : Subgroup ↥R) : Set ↥R)) := by
  obtain ⟨e₁, e₂⟩ := fixedSub_eq_secSub_of_isOppDecomp hP hκ hd h₁ h₂
  obtain ⟨hIA₁, hA₁P, -, hA₂P, hsup, hinf, -⟩ := hd
  rw [e₁, e₂]
  constructor
  · rw [disjoint_iff, ← secSub_inf hκ hIA₁, hinf, secSub_eq_bot hκ]
  · rw [codisjoint_iff, ← secSub_sup hA₁P hA₂P, hsup, secSub_eq_top hκ]

theorem secSub_conjSubgroup (hP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P)
    (hκ : IsSecMod R P I M κ) (r : ↥R) (U : Subgroup G) :
    secSub κ (conjSubgroup (r : G) U) = (secSub κ U).map (DistribSMul.toAddMonoidHom M r) := by
  ext a
  rw [AddSubgroup.mem_map]
  constructor
  · intro ha
    obtain ⟨x, hx, hxa⟩ := mem_secSub.mp ha
    rw [mem_conjSubgroup] at hx
    have hyP : (r : G)⁻¹ * x * r ∈ P := by
      simpa using hP (r : G)⁻¹ (R.inv_mem r.2) x x.2
    have hact := hκ.act r ⟨(r : G)⁻¹ * x * r, hyP⟩ x (by
      show (x : G) = (r : G) * ((r : G)⁻¹ * x * r) * (r : G)⁻¹
      group)
    exact ⟨Multiplicative.toAdd (κ ⟨(r : G)⁻¹ * x * r, hyP⟩), mem_secSub.mpr ⟨_, hx, rfl⟩,
      Multiplicative.ofAdd.injective (hact.symm.trans hxa)⟩
  · rintro ⟨_, hb, rfl⟩
    obtain ⟨y, hy, hyb⟩ := mem_secSub.mp hb
    refine mem_secSub.mpr ⟨⟨(r : G) * y * (r : G)⁻¹, hP r r.2 y y.2⟩, ?_, ?_⟩
    · rw [mem_conjSubgroup]
      have e : (r : G)⁻¹ * ((r : G) * y * (r : G)⁻¹) * r = y := by group
      show (r : G)⁻¹ * ((r : G) * y * (r : G)⁻¹) * r ∈ U
      rw [e]
      exact hy
    · rw [hκ.act r y ⟨(r : G) * y * (r : G)⁻¹, hP r r.2 y y.2⟩ rfl, hyb, toAdd_ofAdd]
      rfl

end Decomp

section Between

variable {R P I : Subgroup G} {M : Type} [AddCommGroup M] [DistribMulAction ↥R M]
  {κ : ↥P →* Multiplicative M} {U : Subgroup G}

theorem conjSubgroup_between (h : SecHyp R P I) (r : ↥R) (hIU : I ≤ U) (hUP : U ≤ P) :
    I ≤ conjSubgroup (r : G) U ∧ conjSubgroup (r : G) U ≤ P := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [mem_conjSubgroup]
    apply hIU
    simpa using h.normI (r : G)⁻¹ (R.inv_mem r.2) x hx
  · rw [mem_conjSubgroup] at hx
    have h1 := h.normP (r : G) r.2 _ (hUP hx)
    have e : (r : G) * ((r : G)⁻¹ * x * r) * (r : G)⁻¹ = x := by group
    rwa [e] at h1

theorem conjSubgroup_eq_self_iff_secSub (h : SecHyp R P I) (hκ : IsSecMod R P I M κ) (r : ↥R)
    (hIU : I ≤ U) (hUP : U ≤ P) :
    conjSubgroup (r : G) U = U ↔
      (secSub κ U).map (DistribSMul.toAddMonoidHom M r) = secSub κ U := by
  obtain ⟨h1, h2⟩ := conjSubgroup_between h r hIU hUP
  rw [← secSub_conjSubgroup h.normP hκ, secSub_inj hκ h1 h2 hIU hUP]

theorem natCard_secSub_mul (hIP : I ≤ P) (hκ : IsSecMod R P I M κ) (hIU : I ≤ U) (hUP : U ≤ P) :
    Nat.card ↥(secSub κ U) * Nat.card ↥I = Nat.card ↥U := by
  have hker : κ.ker = I.subgroupOf P := by
    ext x
    rw [MonoidHom.mem_ker, hκ.ker, Subgroup.mem_subgroupOf]
  have hle : κ.ker ≤ U.subgroupOf P := by
    rw [hker]
    exact fun x hx => Subgroup.mem_subgroupOf.mpr (hIU (Subgroup.mem_subgroupOf.mp hx))
  have h1 : Nat.card ↥(secSub κ U) = Nat.card ↥((U.subgroupOf P).map κ) :=
    Nat.card_congr (Equiv.subtypeEquiv Multiplicative.ofAdd (fun a => Iff.rfl))
  have h2 : Nat.card ↥((U.subgroupOf P).map κ) = (κ.ker.subgroupOf (U.subgroupOf P)).index :=
    (Subgroup.relIndex_ker (K := U.subgroupOf P) κ).symm
  have h3 := Subgroup.card_mul_index (κ.ker.subgroupOf (U.subgroupOf P))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, ← h2, ← h1, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIP).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUP).toEquiv] at h3
  rw [mul_comm]
  exact h3

theorem exists_secSub_eq (hIP : I ≤ P) (hκ : IsSecMod R P I M κ) (W : AddSubgroup M) :
    ∃ U : Subgroup G, I ≤ U ∧ U ≤ P ∧ secSub κ U = W := by
  set U : Subgroup G := ((AddSubgroup.toSubgroup W).comap κ).map P.subtype
  have hmem : ∀ x : ↥P, (x : G) ∈ U ↔ Multiplicative.toAdd (κ x) ∈ W := fun x =>
    Subgroup.mem_map_iff_mem P.subtype_injective
  refine ⟨U, fun x hx => ?_, Subgroup.map_subtype_le _, ?_⟩
  · have h1 : κ ⟨x, hIP hx⟩ = 1 := (hκ.ker _).mpr hx
    exact (hmem ⟨x, hIP hx⟩).mpr (by rw [h1]; exact W.zero_mem)
  · ext a
    rw [mem_secSub]
    constructor
    · rintro ⟨x, hx, hxa⟩
      have h1 := (hmem x).mp hx
      rwa [show Multiplicative.toAdd (κ x) = a by rw [hxa]; rfl] at h1
    · intro ha
      obtain ⟨x, hx⟩ := hκ.surj (Multiplicative.ofAdd a)
      exact ⟨x, (hmem x).mpr (by rw [hx]; exact ha), hx⟩

end Between

end CFSG.RankThree.GF2n.Stroth80
