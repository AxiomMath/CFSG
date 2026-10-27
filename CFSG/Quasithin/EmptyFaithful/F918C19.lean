module

public import CFSG.Quasithin.EmptyFaithful.F918C15
public import CFSG.Quasithin.EmptyFaithful.F918C1
public import CFSG.Quasithin.EmptyFaithful.S153E58C
public import CFSG.Quasithin.Background.InternalSecB56

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank
open scoped Matrix commutatorElement

section Transport

variable {W : Type} [CommGroup W]

@[expose] noncomputable def restrTop (Mp : Subgroup (MulAut W)) :
    ↥Mp →* ↥(autSub Mp (⊤ : Subgroup W)) :=
  ((resHom (⊤ : Subgroup W)).comp (Subgroup.inclusion (le_stabSub_top Mp))).codRestrict
    (autSub Mp ⊤) (fun x => mem_autSub.mpr ⟨⟨x, mem_stabSub_top _⟩, x.2, rfl⟩)

theorem restrTop_bijective (Mp : Subgroup (MulAut W)) : Function.Bijective (restrTop Mp) := by
  constructor
  · intro a b hab
    have h1 := congrArg (fun y : ↥(autSub Mp (⊤ : Subgroup W)) => (y : MulAut ↥(⊤ : Subgroup W))) hab
    have h2 := resHom_top_injective h1
    exact Subtype.ext (congrArg (fun g : ↥(stabSub (⊤ : Subgroup W)) => (g : MulAut W)) h2)
  · intro y
    obtain ⟨g, hg, hgy⟩ := mem_autSub.mp y.2
    exact ⟨⟨g, hg⟩, Subtype.ext hgy⟩

abbrev TensorE : Type := Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))

abbrev TensorG : Type := ↥(StatedSL 3 (ZMod 2)) × ↥(StatedSL 3 (ZMod 2))

@[expose] def IsTensorData (Mp : Subgroup (MulAut W)) (π : TensorG →* ↥Mp) (β : W ≃* TensorE) :
    Prop :=
  ∀ (γ : TensorG) (w : W), β ((π γ : MulAut W) w) = tensorAct 3 (ZMod 2) γ (β w)

theorem exists_tensorData {Mp : Subgroup (MulAut W)}
    (h : TensorNatL32 (autSub Mp (⊤ : Subgroup W))) :
    ∃ (π : TensorG →* ↥Mp) (β : W ≃* TensorE), Function.Surjective π ∧ IsTensorData Mp π β := by
  obtain ⟨π', hπ'⟩ := h
  obtain ⟨hs, -, -, -, -, -, -, β₀, hβs₀, hβk₀, hβe₀⟩ := hπ'
  let β' : ↥(⊤ : Subgroup ↥(⊤ : Subgroup W)) →* (↥(⊤ : Subgroup TensorE) ⧸
      (⊥ : Subgroup TensorE).subgroupOf ⊤) := β₀
  have hβs : Function.Surjective β' := hβs₀
  have hβk : ∀ u, β' u = 1 ↔ (u : ↥(⊤ : Subgroup W)) ∈ (⊥ : Subgroup ↥(⊤ : Subgroup W)) := hβk₀
  have hβe : ∀ (γ : TensorG) (u : ↥(⊤ : Subgroup ↥(⊤ : Subgroup W))) (m : ↥(⊤ : Subgroup TensorE))
      (hu : (((π' γ : ↥(autSub Mp (⊤ : Subgroup W))) : MulAut ↥(⊤ : Subgroup W))
        (u : ↥(⊤ : Subgroup W))) ∈ (⊤ : Subgroup ↥(⊤ : Subgroup W)))
      (hm : tensorAct 3 (ZMod 2) γ (m : TensorE) ∈ (⊤ : Subgroup TensorE)),
      β' u = QuotientGroup.mk m →
        β' ⟨(((π' γ : ↥(autSub Mp (⊤ : Subgroup W))) : MulAut ↥(⊤ : Subgroup W))
          (u : ↥(⊤ : Subgroup W))), hu⟩ = QuotientGroup.mk ⟨tensorAct 3 (ZMod 2) γ (m : TensorE), hm⟩ :=
    hβe₀
  let eq : ↥Mp ≃* ↥(autSub Mp (⊤ : Subgroup W)) :=
    MulEquiv.ofBijective (restrTop Mp) (restrTop_bijective Mp)
  let π : TensorG →* ↥Mp := eq.symm.toMonoidHom.comp π'
  have hπs : Function.Surjective π := eq.symm.surjective.comp hs
  have hinj : Function.Injective β' := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
  let e3 : ↥(⊤ : Subgroup ↥(⊤ : Subgroup W)) ≃*
      (↥(⊤ : Subgroup TensorE) ⧸ (⊥ : Subgroup TensorE).subgroupOf ⊤) :=
    MulEquiv.ofBijective β' ⟨hinj, hβs⟩
  let β : W ≃* TensorE :=
    ((Subgroup.topEquiv (G := W)).symm.trans
      (Subgroup.topEquiv (G := ↥(⊤ : Subgroup W))).symm).trans (e3.trans (B5.natQuotEquiv TensorE))
  refine ⟨π, β, hπs, fun γ w => ?_⟩
  have hrestr : restrTop Mp (π γ) = π' γ := eq.apply_symm_apply (π' γ)
  have hact : ∀ u : ↥(⊤ : Subgroup W),
      (((π' γ : ↥(autSub Mp (⊤ : Subgroup W))) : MulAut ↥(⊤ : Subgroup W)) u : W) =
        ((π γ : ↥Mp) : MulAut W) (u : W) := by
    intro u
    rw [← hrestr]
    rfl
  let uw : ↥(⊤ : Subgroup W) := ⟨w, trivial⟩
  let u₀ : ↥(⊤ : Subgroup ↥(⊤ : Subgroup W)) := ⟨uw, trivial⟩
  let m : ↥(⊤ : Subgroup TensorE) := ⟨β w, trivial⟩
  have hm : β' u₀ = QuotientGroup.mk m := by
    apply (B5.natQuotEquiv TensorE).injective
    exact (B5.natQuotEquiv_mk TensorE (β w)).symm
  have hu : (((π' γ : ↥(autSub Mp (⊤ : Subgroup W))) : MulAut ↥(⊤ : Subgroup W))
      (u₀ : ↥(⊤ : Subgroup W))) ∈ (⊤ : Subgroup ↥(⊤ : Subgroup W)) := trivial
  have hm' : tensorAct 3 (ZMod 2) γ (m : TensorE) ∈ (⊤ : Subgroup TensorE) := trivial
  have h1 := hβe γ u₀ m hu hm' hm
  have h2 : (⟨((π' γ : ↥(autSub Mp (⊤ : Subgroup W))) : MulAut ↥(⊤ : Subgroup W))
      (u₀ : ↥(⊤ : Subgroup W)), hu⟩ : ↥(⊤ : Subgroup ↥(⊤ : Subgroup W))) =
      ⟨⟨((π γ : ↥Mp) : MulAut W) w, trivial⟩, trivial⟩ := Subtype.ext (Subtype.ext (hact uw))
  rw [h2] at h1
  have h3 : β ((π γ : MulAut W) w) = B5.natQuotEquiv TensorE (β' ⟨⟨((π γ : ↥Mp) : MulAut W) w,
    trivial⟩, trivial⟩) := rfl
  rw [h3, h1]
  exact B5.natQuotEquiv_mk TensorE _

end Transport

section Faithful

variable {W : Type} [CommGroup W]

theorem tensor_faithful (γ : TensorG) (h : ∀ X : TensorE, tensorAct 3 (ZMod 2) γ X = X) : γ = 1 := by
  have hf := CFSG.Quasithin.Vol2.Ch10.SecA.tensorPair_faithful (StatedSL 3 (ZMod 2))
    (StatedSL 3 (ZMod 2)) CFSG.Quasithin.Vol2.Ch10.SecA.scalar_statedSL_three_two
  exact hf γ fun m _ => Subgroup.mem_bot.mpr (by rw [show (CFSG.Quasithin.H13.tensorPairModel
    (StatedSL 3 (ZMod 2)) (StatedSL 3 (ZMod 2))).act γ m = m from h m]; exact mul_inv_cancel m)

theorem IsTensorData.injective {Mp : Subgroup (MulAut W)} {π : TensorG →* ↥Mp} {β : W ≃* TensorE}
    (hd : IsTensorData Mp π β) : Function.Injective π := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  refine tensor_faithful γ fun X => ?_
  obtain ⟨w, rfl⟩ := β.surjective X
  rw [← hd γ w, hγ]
  rfl

theorem isQuasisimple_of_isPSL_three_two {Y : Type} [Group Y] (h : IsPSL 3 2 1 Y) :
    CFSG.IsQuasisimple Y := by
  have hs : IsSimpleGroup Y := (CFSG.LieType.Simplicity.fam_PSL_simplicity Y 3 2 1 h).2
  have hcard : Nat.card Y = 168 := by
    have := CFSG.Quasithin.Vol2.Ch11.SecA.card_L32 h
    omega
  have hnc : ∃ a b : Y, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hfin : Finite Y := Nat.finite_of_card_ne_zero (by omega)
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Y) 2 (by rw [hcard]; norm_num)
    have hnorm : (Subgroup.zpowers x).Normal := ⟨fun n hn g => by
      rw [hcon g n, mul_assoc, mul_inv_cancel, mul_one]
      exact hn⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x) with h0 | h1
    · have hx1 : x = 1 := Subgroup.mem_bot.mp (h0 ▸ Subgroup.mem_zpowers x)
      rw [hx1, orderOf_one] at hx
      omega
    · have h2 : Nat.card (Subgroup.zpowers x) = Nat.card Y := by rw [h1]; exact Subgroup.card_top
      rw [Nat.card_zpowers, hx, hcard] at h2
      omega
  exact isQuasisimple_of_perfect_of_isSimpleGroup (by
    have hc : (commutator Y).Normal := inferInstance
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Y) with h0 | h1
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have : ⁅a, b⁆ ∈ commutator Y := Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h0, Subgroup.mem_bot, commutatorElement_def] at this
      exact hab (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp this))
    · exact ⟨h1⟩) hs

end Faithful

section Ident

variable {W : Type} [CommGroup W]

theorem eq_of_le_of_simple {A L : Subgroup (MulAut W)} [IsSimpleGroup ↥A] (hLA : L ≤ A)
    (hAn : A ≤ Subgroup.normalizer (L : Set (MulAut W))) (hL1 : L ≠ ⊥) : L = A := by
  have hnorm : (L.subgroupOf A).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLA).mpr hAn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (L.subgroupOf A) with h0 | h1
  · exfalso
    apply hL1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hLA hx⟩ : ↥A) ∈ L.subgroupOf A := hx
    rw [h0, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  · refine le_antisymm hLA fun a ha => ?_
    have : (⟨a, ha⟩ : ↥A) ∈ L.subgroupOf A := by rw [h1]; exact Subgroup.mem_top _
    exact this

@[expose] def factorL (Mp : Subgroup (MulAut W)) (π : TensorG →* ↥Mp) : Subgroup (MulAut W) :=
  (Mp.subtype.comp (π.comp (MonoidHom.inl _ _))).range

@[expose] def factorR (Mp : Subgroup (MulAut W)) (π : TensorG →* ↥Mp) : Subgroup (MulAut W) :=
  (Mp.subtype.comp (π.comp (MonoidHom.inr _ _))).range

theorem mem_factorL {Mp : Subgroup (MulAut W)} {π : TensorG →* ↥Mp} {x : MulAut W} :
    x ∈ factorL Mp π ↔ ∃ g : ↥(StatedSL 3 (ZMod 2)), ((π (g, 1) : ↥Mp) : MulAut W) = x := by
  simp [factorL, MonoidHom.mem_range]

theorem mem_factorR {Mp : Subgroup (MulAut W)} {π : TensorG →* ↥Mp} {x : MulAut W} :
    x ∈ factorR Mp π ↔ ∃ g : ↥(StatedSL 3 (ZMod 2)), ((π (1, g) : ↥Mp) : MulAut W) = x := by
  simp [factorR, MonoidHom.mem_range]

theorem eq_factor_or {Mp L L' : Subgroup (MulAut W)} {π : TensorG →* ↥Mp} {β : W ≃* TensorE}
    (hd : IsTensorData Mp π β) (hπs : Function.Surjective π) (hMp : Mp = L ⊔ L')
    (hLL' : ∀ x ∈ L, ∀ y ∈ L', x * y = y * x) (hL : IsPSL 3 2 1 ↥L) :
    L = factorL Mp π ∨ L = factorR Mp π := by
  have hinj := hd.injective
  have hLMp : L ≤ Mp := hMp ▸ le_sup_left
  have hAMp : factorL Mp π ≤ Mp := by
    rintro _ ⟨g, rfl⟩
    exact (π (g, 1)).2
  have hBMp : factorR Mp π ≤ Mp := by
    rintro _ ⟨g, rfl⟩
    exact (π (1, g)).2
  have hsup : factorL Mp π ⊔ factorR Mp π = Mp := by
    refine le_antisymm (sup_le hAMp hBMp) fun x hx => ?_
    obtain ⟨⟨g, h⟩, hγ⟩ := hπs ⟨x, hx⟩
    have e : ((π (g, h) : ↥Mp) : MulAut W) = ((π (g, 1) : ↥Mp) : MulAut W) * ((π (1, h) : ↥Mp) : MulAut W) := by
      rw [← Subgroup.coe_mul, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
    have hx' : x = ((π (g, h) : ↥Mp) : MulAut W) := by rw [hγ]
    rw [hx', e]
    exact Subgroup.mul_mem_sup (mem_factorL.mpr ⟨g, rfl⟩) (mem_factorR.mpr ⟨h, rfl⟩)
  have hcomm : ∀ a ∈ factorL Mp π, ∀ b ∈ factorR Mp π, a * b = b * a := by
    rintro _ ha _ hb
    obtain ⟨g, rfl⟩ := mem_factorL.mp ha
    obtain ⟨h, rfl⟩ := mem_factorR.mp hb
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul]
    congr 2
    simp
  have hLn : ∀ x ∈ Mp, ∀ k ∈ L, x * k * x⁻¹ ∈ L := fun x hx k hk =>
    InternalSec.conj_mem_of_mem_sup_of_commute hLL' x (hMp ▸ hx) k hk
  have hLnorm : Mp ≤ Subgroup.normalizer (L : Set (MulAut W)) := fun x hx =>
    Subgroup.mem_normalizer_iff.mpr fun k =>
      ⟨fun hk => hLn x hx k hk, fun hk => by
        have := hLn x⁻¹ (Mp.inv_mem hx) _ hk
        simpa [mul_assoc] using this⟩
  have hLq := isQuasisimple_of_isPSL_three_two hL
  have hL1 : L ≠ ⊥ := by
    intro h0
    have hcard := CFSG.Quasithin.Vol2.Ch11.SecA.card_L32 hL
    rw [h0, Subgroup.card_bot] at hcard
    omega
  have hAs : IsSimpleGroup ↥(factorL Mp π) := by
    have := S153E58.isSimpleGroup_statedSL_three_two
    exact MulEquiv.isSimpleGroup (MonoidHom.ofInjective (f := Mp.subtype.comp (π.comp (MonoidHom.inl _ _)))
      (fun a b hab => (Prod.mk.inj (hinj (Subtype.ext hab))).1)).symm
  have hBs : IsSimpleGroup ↥(factorR Mp π) := by
    have := S153E58.isSimpleGroup_statedSL_three_two
    exact MulEquiv.isSimpleGroup (MonoidHom.ofInjective (f := Mp.subtype.comp (π.comp (MonoidHom.inr _ _)))
      (fun a b hab => (Prod.mk.inj (hinj (Subtype.ext hab))).2)).symm
  rcases InternalSec.le_or_le_of_sup_eq hsup hcomm hLMp hLn hLq with h | h
  · exact Or.inl (eq_of_le_of_simple h (hAMp.trans hLnorm) hL1)
  · exact Or.inr (eq_of_le_of_simple h (hBMp.trans hLnorm) hL1)

end Ident

section Matrices

abbrev TensorV : Type := Multiplicative (Fin 3 → ZMod 2)

@[expose] def colHom (k : Fin 3) : TensorE →* TensorV where
  toFun X := Multiplicative.ofAdd (fun i => Multiplicative.toAdd X i k)
  map_one' := by
    apply Multiplicative.toAdd.injective
    ext i
    simp
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    ext i
    simp

@[expose] def insHom : TensorV →* TensorE where
  toFun v := Multiplicative.ofAdd (Matrix.of fun i j => if j = 0 then Multiplicative.toAdd v i else 0)
  map_one' := by
    apply Multiplicative.toAdd.injective
    ext i j
    simp
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    ext i j
    by_cases hj : j = 0 <;> simp [hj]

theorem tensorAct_inl (g : ↥(StatedSL 3 (ZMod 2))) (X : TensorE) :
    tensorAct 3 (ZMod 2) (g, 1) X =
      Multiplicative.ofAdd (((g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        Multiplicative.toAdd X) := by
  simp [tensorAct]

theorem insHom_natAct (g : ↥(StatedSL 3 (ZMod 2))) (v : TensorV) :
    tensorAct 3 (ZMod 2) (g, 1) (insHom v) = insHom (natAct (StatedSL 3 (ZMod 2)) g v) := by
  rw [tensorAct_inl]
  apply Multiplicative.toAdd.injective
  ext i j
  by_cases hj : j = 0
  · simp [insHom, natAct, hj, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · simp [insHom, natAct, hj, Matrix.mul_apply]

theorem colHom_tensorAct (k : Fin 3) (g : ↥(StatedSL 3 (ZMod 2))) (X : TensorE) :
    colHom k (tensorAct 3 (ZMod 2) (g, 1) X) = natAct (StatedSL 3 (ZMod 2)) g (colHom k X) := by
  rw [tensorAct_inl]
  apply Multiplicative.toAdd.injective
  ext i
  simp [colHom, natAct, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem eq_one_of_colHom (X : TensorE) (h : ∀ k, colHom k X = 1) : X = 1 := by
  apply Multiplicative.toAdd.injective
  ext i k
  have := congrArg (fun v : TensorV => Multiplicative.toAdd v i) (h k)
  simpa [colHom] using this

theorem insHom_ne_one : insHom (Multiplicative.ofAdd (Pi.single 0 1 : Fin 3 → ZMod 2)) ≠ 1 := by
  intro h
  have := congrArg (fun X : TensorE => Multiplicative.toAdd X 0 0) h
  simp [insHom] at this

end Matrices

section Twist

variable {W : Type} [CommGroup W]

theorem commute_of_conj_eq {Ω : Type} [Group Ω] {L : Subgroup Ω} {σ l₀ : Ω} (hl₀ : l₀ ∈ L)
    (h : ∀ y ∈ L, σ * y * σ⁻¹ = l₀ * y * l₀⁻¹) : ∀ x ∈ L, (σ * l₀⁻¹) * x = x * (σ * l₀⁻¹) := by
  intro x hx
  have hy : l₀⁻¹ * x * l₀ ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hl₀) hx) hl₀
  have h1 := h _ hy
  have e1 : l₀ * (l₀⁻¹ * x * l₀) * l₀⁻¹ = x := by group
  rw [e1] at h1
  calc (σ * l₀⁻¹) * x = σ * (l₀⁻¹ * x * l₀) * l₀⁻¹ := by group
    _ = (σ * (l₀⁻¹ * x * l₀) * σ⁻¹) * (σ * l₀⁻¹) := by group
    _ = x * (σ * l₀⁻¹) := by rw [h1]

theorem twist_columns {Mp L : Subgroup (MulAut W)} {π : TensorG →* ↥Mp} {β : W ≃* TensorE}
    (hd : IsTensorData Mp π β) (hL : L = factorL Mp π) {σ : MulAut W}
    (hσ : σ ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    ∃ l₀ ∈ L, ∀ x ∈ L, (σ * l₀⁻¹) * x = x * (σ * l₀⁻¹) := by
  subst hL
  have hσL : ∀ x ∈ factorL Mp π, σ * x * σ⁻¹ ∈ factorL Mp π := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 hσ x).1 hx
  have hα : ∀ g : ↥(StatedSL 3 (ZMod 2)), ∃ g' : ↥(StatedSL 3 (ZMod 2)),
      ((π (g', 1) : ↥Mp) : MulAut W) = σ * ((π (g, 1) : ↥Mp) : MulAut W) * σ⁻¹ := fun g =>
    mem_factorL.mp (hσL _ (mem_factorL.mpr ⟨g, rfl⟩))
  choose α hα using hα
  let ψ : TensorE ≃* TensorE := β.symm.trans (σ.trans β)
  have hψ : ∀ (g : ↥(StatedSL 3 (ZMod 2))) (X : TensorE),
      ψ (tensorAct 3 (ZMod 2) (g, 1) X) = tensorAct 3 (ZMod 2) (α g, 1) (ψ X) := by
    intro g X
    obtain ⟨w, rfl⟩ := β.surjective X
    have h1 : ψ (tensorAct 3 (ZMod 2) (g, 1) (β w)) = β (σ (((π (g, 1) : ↥Mp) : MulAut W) w)) := by
      rw [← hd (g, 1) w]
      show β (σ (β.symm (β _))) = _
      rw [MulEquiv.symm_apply_apply]
    have h2 : ψ (β w) = β (σ w) := by
      show β (σ (β.symm (β w))) = _
      rw [MulEquiv.symm_apply_apply]
    rw [h1, h2, ← hd (α g, 1) (σ w), hα g]
    show _ = β ((σ * ((π (g, 1) : ↥Mp) : MulAut W) * σ⁻¹) (σ w))
    simp [MulAut.mul_apply]
  let φ : Fin 3 → TensorV →* TensorV := fun k => (colHom k).comp (ψ.toMonoidHom.comp insHom)
  have hφ : ∀ (k : Fin 3) (g : ↥(StatedSL 3 (ZMod 2))) (v : TensorV),
      φ k (natAct (StatedSL 3 (ZMod 2)) g v) = natAct (StatedSL 3 (ZMod 2)) (α g) (φ k v) := by
    intro k g v
    show colHom k (ψ (insHom (natAct (StatedSL 3 (ZMod 2)) g v))) =
      natAct (StatedSL 3 (ZMod 2)) (α g) (colHom k (ψ (insHom v)))
    rw [← insHom_natAct, hψ, colHom_tensorAct]
  have hker : ∀ k, (φ k).ker = ⊥ ∨ (φ k).ker = ⊤ := fun k =>
    B5.natural_invariant_eq (by norm_num) _ fun γ x hx => by
      rw [MonoidHom.mem_ker] at hx ⊢
      rw [hφ, hx]
      simp [natAct]
  obtain ⟨k, hk⟩ : ∃ k, (φ k).ker = ⊥ := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ k, (φ k).ker = ⊤ := fun k => (hker k).resolve_left (hcon k)
    set v₀ : TensorV := Multiplicative.ofAdd (Pi.single 0 1 : Fin 3 → ZMod 2) with hv₀
    have h1 : ψ (insHom v₀) = 1 := by
      apply eq_one_of_colHom
      intro k
      have : v₀ ∈ (φ k).ker := by rw [hall k]; exact Subgroup.mem_top _
      exact this
    exact insHom_ne_one (ψ.injective (h1.trans (map_one ψ).symm))
  have hinj : Function.Injective (φ k) := (MonoidHom.ker_eq_bot_iff _).mp hk
  have hsurj : Function.Surjective (φ k) := Finite.injective_iff_surjective.mp hinj
  obtain ⟨G₀, hG₀⟩ := exists_stated_of_mulEquiv (F := ZMod 2) (by simp)
    (MulEquiv.ofBijective (φ k) ⟨hinj, hsurj⟩)
  have hG₀' : ∀ v, φ k v = natAct (StatedSL 3 (ZMod 2)) G₀ v := fun v => hG₀ v
  have hαG : ∀ g, α g * G₀ = G₀ * g := by
    intro g
    apply natAct_injective (StatedSL 3 (ZMod 2))
    intro v
    rw [natAct_mul_twist, natAct_mul_twist, ← hG₀', ← hG₀', hφ k g v]
  refine ⟨((π (G₀, 1) : ↥Mp) : MulAut W), mem_factorL.mpr ⟨G₀, rfl⟩, ?_⟩
  refine commute_of_conj_eq (mem_factorL.mpr ⟨G₀, rfl⟩) fun y hy => ?_
  obtain ⟨g, rfl⟩ := mem_factorL.mp hy
  rw [← hα g]
  have hg : α g = G₀ * g * G₀⁻¹ := by rw [← hαG g]; group
  have e : ((G₀ * g * G₀⁻¹, 1) : TensorG) = (G₀, 1) * (g, 1) * (G₀, 1)⁻¹ := by
    ext <;> simp
  rw [hg, e, map_mul, map_mul, map_inv]
  rfl

end Twist

section Final

variable {W : Type} [CommGroup W]

@[expose] def transposeE : TensorE ≃* TensorE :=
  AddEquiv.toMultiplicative (Matrix.transposeAddEquiv (Fin 3) (Fin 3) (ZMod 2))

theorem IsTensorData.swap {Mp : Subgroup (MulAut W)} {π : TensorG →* ↥Mp} {β : W ≃* TensorE}
    (hd : IsTensorData Mp π β) :
    IsTensorData Mp (π.comp (MulEquiv.prodComm (M := ↥(StatedSL 3 (ZMod 2)))
      (N := ↥(StatedSL 3 (ZMod 2)))).toMonoidHom) (β.trans transposeE) := by
  intro γ w
  obtain ⟨g, h⟩ := γ
  show transposeE (β (((π (h, g) : ↥Mp) : MulAut W) w)) = tensorAct 3 (ZMod 2) (g, h) (transposeE (β w))
  rw [hd (h, g) w]
  apply Multiplicative.toAdd.injective
  simp [transposeE, tensorAct, Matrix.transpose_mul, mul_assoc]

theorem tensorTwistL32 : TensorTwistL32 := by
  intro W _ _ Mp L L' σ hL _ hMp hLL' hT hσL _
  obtain ⟨π, β, hπs, hd⟩ := exists_tensorData hT
  rcases eq_factor_or hd hπs hMp hLL' hL with h | h
  · exact twist_columns hd h hσL
  · refine twist_columns (hd.swap) ?_ hσL
    rw [h]
    ext x
    simp only [mem_factorL, mem_factorR]
    rfl

end Final

end CFSG.Quasithin
