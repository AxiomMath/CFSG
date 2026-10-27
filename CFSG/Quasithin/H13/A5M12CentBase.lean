
module

public import CFSG.Quasithin.H13.A5M12Coord
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12
public import Certificates.Certificate7105
public import CFSG.Quasithin.Background.HMathieuFacts22Base

@[expose] public section

namespace CFSG.Quasithin.H13.A5.M12

open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.Vol2.Ch10.SecA.C10P01 CFSG.Blueprint

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem κC12_cols : ∀ j < 24, κC12 (bvec 24 (2 ^ j)) = bvec 10 (κC12Cols.getD j 0) := by
  decide +kernel

theorem lift12_cols : ∀ j < 10, lift12 (bvec 10 (2 ^ j)) = bvec 24 (lift12Cols.getD j 0) := by
  decide +kernel

theorem κC12_bvec (x : ℕ) : κC12 (bvec 24 x) = bvec 10 (actM κC12Cols x) :=
  addHom_bvec κC12.toAddMonoidHom κC12Cols rfl κC12_cols x

theorem lift12_bvec (x : ℕ) : lift12 (bvec 10 x) = bvec 24 (actM lift12Cols x) :=
  addHom_bvec lift12.toAddMonoidHom lift12Cols rfl lift12_cols x

theorem κC12Cols_lt : ∀ c ∈ κC12Cols, c < 2 ^ 10 := by decide

theorem actC12_lt (a : Array ℕ) (m : ℕ) : actC12 a m < 2 ^ 10 := actM_lt κC12Cols_lt _

theorem rhoC12_toW (Γ : Subgroup (Equiv.Perm (Fin 24))) (hΓ : Γ ≤ m24Pair) (σ : ↥Γ)
    {a : Array ℕ} (ha : HasArr (σ : Equiv.Perm (Fin 24)) a) (m : ℕ) :
    rhoC12 Γ hΓ σ (toW 10 m) = toW 10 (actC12 a m) := by
  have h1 : rhoC12 Γ hΓ σ (toW 10 m) =
      code12Coords.κ (G6.permAct 24 σ (code12Coords.lift (toW 10 m))) := rfl
  have h2 : Multiplicative.toAdd (code12Coords.lift (toW 10 m)) = lift12 (bvec 10 m) := rfl
  have h3 : ∀ x, code12Coords.κ x = Multiplicative.ofAdd (κC12 (Multiplicative.toAdd x)) :=
    fun _ => rfl
  rw [h1, h3, toAdd_permAct, h2, lift12_bvec, permWord_bvec ha, κC12_bvec]
  rfl

theorem cert12_mem :
    ∀ a ∈ cent12H ++ cent12S, inAutOK a = true ∧ permM a dodecadMask = dodecadMask :=
  Certificates.certificate7105.1

theorem cert12_fix0 : ∀ a ∈ cent12H, actC12 a 360 = 360 :=
  Certificates.certificate7105.2.1

theorem cert12_fix :
    ∀ m < 1024, (∀ a ∈ cent12H, actC12 a m = m) → m = 0 ∨ m = 360 :=
  Certificates.certificate7105.2.2.1

theorem cert12_span :
    ∀ m < 1024, m ∈ combos (cent12S.map fun a => actC12 a 360) :=
  Certificates.certificate7105.2.2.2.1

theorem cert12_tau :
    inAutOK tau12 = true ∧ permM tau12 dodecadMask = dodecadMask ^^^ (2 ^ 24 - 1) :=
  Certificates.certificate7105.2.2.2.2

theorem permAct_dodecadE_of_arr {σ : Equiv.Perm (Fin 24)} {a : Array ℕ} (ha : HasArr σ a)
    {x : ℕ} (hx : permM a dodecadMask = x) :
    G6.permAct 24 σ dodecadE = Multiplicative.ofAdd (bvec 24 x) := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_permAct]
  change permWord σ (bvec 24 dodecadMask) = bvec 24 x
  rw [permWord_bvec ha, hx]

theorem mem_m24Fix_of_arr {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ AutPerm) {a : Array ℕ}
    (ha : HasArr σ a) (hY : permM a dodecadMask = dodecadMask) : σ ∈ m24Fix dodecadE :=
  ⟨hσ, permAct_dodecadE_of_arr ha hY⟩

theorem bvec_compl : bvec 24 (dodecadMask ^^^ (2 ^ 24 - 1)) = dodecadW + Ω := by decide +kernel

theorem exists_mem_m24Pair_not_mem :
    ∃ τ ∈ m24Pair, τ ∉ m24Fix dodecadE := by
  obtain ⟨hok, hY⟩ := cert12_tau
  obtain ⟨τ, hτ, hτa⟩ := exists_of_inAutOK hok
  have h1 : G6.permAct 24 τ dodecadE = dodecadE * G6.allOnes 24 := by
    rw [permAct_dodecadE_of_arr hτa hY, bvec_compl]
    rfl
  refine ⟨τ, ⟨hτ, Or.inr h1⟩, fun h => ?_⟩
  have h2 := h.2
  rw [h1] at h2
  have h3 := congrFun (congrArg Multiplicative.toAdd h2) 0
  revert h3
  decide +kernel

theorem centralizer_rhoC12 :
    Subgroup.centralizer ((rhoC12 (m24Fix dodecadE) m24Fix_le_m24Pair).range :
      Set (MulAut W10)) = ⊥ := by
  refine centralizer_eq_bot_of_masks (n := 10) actC12 cent12H cent12S (fun a ha => ?_)
    actC12_lt (v0 := 360) (by norm_num) (by norm_num) cert12_fix0 cert12_fix cert12_span
  obtain ⟨hok, hY⟩ := cert12_mem a ha
  obtain ⟨σ, hσ, hσa⟩ := exists_of_inAutOK hok
  exact ⟨rhoC12 (m24Fix dodecadE) m24Fix_le_m24Pair ⟨σ, mem_m24Fix_of_arr hσ hσa hY⟩, ⟨_, rfl⟩,
    fun m _ => rhoC12_toW _ _ ⟨σ, _⟩ hσa m⟩

section Realize

variable {numer denom : Subgroup (G6.PermMod 24)} {W : Type*} [CommGroup W]

theorem mul_inv_eq_inv_mul_inv' {G : Type*} [CommGroup G] (a b : G) : a * b⁻¹ = (b * a⁻¹)⁻¹ := by
  rw [mul_inv_rev, inv_inv]

theorem mul_inv_eq_of_three {G : Type*} [CommGroup G] (a b c : G) :
    b * c⁻¹ = (a * b⁻¹)⁻¹ * (a * c⁻¹) := by
  rw [mul_inv_rev, inv_inv, mul_assoc, ← mul_assoc a⁻¹, inv_mul_cancel, one_mul]

theorem realizes_rho_of_coords (c : SecCoords numer denom W)
    {Γ : Subgroup (Equiv.Perm (Fin 24))} (hΓ : ∀ σ ∈ Γ, Preserves numer denom σ)
    (hdn : denom ≤ numer) :
    (FFModel.golaySec Γ numer denom).Realizes (c.rho Γ hΓ).range ⊤ ⊥ := by
  have hmk : ∀ m m' : ↥numer, (QuotientGroup.mk m : ↥numer ⧸ denom.subgroupOf numer) =
      QuotientGroup.mk m' ↔ (m : G6.PermMod 24) * (m' : G6.PermMod 24)⁻¹ ∈ denom := by
    intro m m'
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
      ← inv_mem_iff, mul_inv_rev, inv_inv, mul_comm]
  refine ⟨(c.rho Γ hΓ).rangeRestrict, (c.rho Γ hΓ).rangeRestrict_surjective, bot_le, hdn,
    fun _ _ _ => Subgroup.mem_top _, fun h z hz => ?_, fun γ m hm => (hΓ _ γ.2).1 m hm,
    fun γ m hm => (hΓ _ γ.2).2 m hm,
    (QuotientGroup.mk' (denom.subgroupOf numer)).comp
      ((c.lift.codRestrict numer c.lift_mem).comp (⊤ : Subgroup W).subtype),
    fun q => ?_, fun u => ?_, fun γ u m hu hm h => ?_⟩
  · rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · obtain ⟨m, hm⟩ : ∃ m : ↥numer,
        (QuotientGroup.mk m : ↥numer ⧸ denom.subgroupOf numer) = q :=
      QuotientGroup.mk_surjective q
    rw [← hm]
    refine ⟨⟨c.κ (m : G6.PermMod 24), Subgroup.mem_top _⟩, ?_⟩
    change (QuotientGroup.mk ⟨c.lift (c.κ (m : G6.PermMod 24)), c.lift_mem _⟩ :
      ↥numer ⧸ denom.subgroupOf numer) = QuotientGroup.mk m
    rw [hmk]
    change c.lift (c.κ (m : G6.PermMod 24)) * (m : G6.PermMod 24)⁻¹ ∈ denom
    rw [mul_inv_eq_inv_mul_inv']
    exact denom.inv_mem (c.mul_lift_inv_mem m.2)
  · change (QuotientGroup.mk ⟨c.lift u, c.lift_mem u⟩ : ↥numer ⧸ denom.subgroupOf numer) = 1 ↔
      (u : W) ∈ ⊥
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_bot]
    change c.lift u ∈ denom ↔ (u : W) = 1
    constructor
    · intro h1
      have h2 := (c.ker_iff _ (c.lift_mem u)).2 h1
      rwa [c.κ_lift] at h2
    · intro h1
      rw [h1, map_one]
      exact denom.one_mem
  · obtain ⟨γ, hγ⟩ := γ
    obtain ⟨m, hm'⟩ := m
    change (QuotientGroup.mk ⟨c.lift u, c.lift_mem u⟩ : ↥numer ⧸ denom.subgroupOf numer) =
      QuotientGroup.mk (⟨m, hm'⟩ : ↥numer) at h
    change (QuotientGroup.mk ⟨c.lift (c.κ (G6.permAct 24 γ (c.lift u))), c.lift_mem _⟩ :
      ↥numer ⧸ denom.subgroupOf numer) = QuotientGroup.mk (⟨G6.permAct 24 γ m, hm⟩ : ↥numer)
    rw [hmk] at h ⊢
    have h1 := c.mul_lift_inv_mem ((hΓ γ hγ).1 _ (c.lift_mem u))
    have h2 := (hΓ γ hγ).2 _ h
    rw [map_mul, map_inv] at h2
    have h3 := denom.mul_mem (denom.inv_mem h1) h2
    rw [mul_inv_eq_of_three (G6.permAct 24 γ (c.lift u))]
    exact h3

end Realize

theorem codeCoords_realizes : MathieuCode24 (rhoC11 AutPerm le_rfl).range ⊤ ⊥ :=
  realizes_rho_of_coords codeCoords _ (Subgroup.zpowers_le.mpr allOnes_mem_golayC)

theorem index_eq_two_pow {W : Type*} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (H : Subgroup W) : ∃ k, H.index = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, hN⟩ := IsPGroup.iff_card.mp (show IsPGroup 2 W from
    fun w => ⟨1, by rw [pow_one]; exact hW w⟩)
  have hdvd : H.index ∣ 2 ^ N := by
    rw [← hN]
    exact H.index_dvd_card
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨k, hk⟩

theorem rkIdx_le_of_proj {W W' : Type*} [CommGroup W] [CommGroup W'] [Finite W] [Finite W']
    (hW' : ∀ w : W', w ^ 2 = 1) (p : W →* W') (hp : Function.Surjective p) {d : W}
    (hker : ∀ u, p u = 1 ↔ u = 1 ∨ u = d) {φ : MulAut W} {φ' : MulAut W'}
    (hφ : ∀ u, p (φ u) = φ' (p u)) :
    rkIdx (fixV (Subgroup.zpowers φ)) ≤ rkIdx (fixV (Subgroup.zpowers φ')) + 1 := by
  have hCC : fixV (Subgroup.zpowers φ) ≤ (fixV (Subgroup.zpowers φ')).comap p := by
    intro u hu
    rw [Subgroup.mem_comap, H.Mathieu.mem_fixV_zpowers_iff, ← hφ,
      (H.Mathieu.mem_fixV_zpowers_iff).1 hu]
  let χ : ↥((fixV (Subgroup.zpowers φ')).comap p) →* W :=
    { toFun := fun u => φ u * (u : W)⁻¹
      map_one' := by simp
      map_mul' := fun u v => by
        simp only [Subgroup.coe_mul, map_mul, mul_inv]
        exact mul_mul_mul_comm _ _ _ _ }
  have hχker : χ.ker = (fixV (Subgroup.zpowers φ)).subgroupOf
      ((fixV (Subgroup.zpowers φ')).comap p) := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, H.Mathieu.mem_fixV_zpowers_iff]
    exact mul_inv_eq_one
  have hχrange : ∀ w ∈ χ.range, w = 1 ∨ w = d := by
    rintro _ ⟨u, rfl⟩
    refine (hker _).1 ?_
    have hu := (H.Mathieu.mem_fixV_zpowers_iff).1 (Subgroup.mem_comap.1 u.2)
    change p (φ u * (u : W)⁻¹) = 1
    rw [map_mul, map_inv, hφ, hu, mul_inv_cancel]
  have hcard : Nat.card χ.range ≤ 2 := by
    classical
    have h1 : Nat.card χ.range ≤ Nat.card ({1, d} : Finset W) := by
      refine Nat.card_le_card_of_injective (fun w => ⟨w.1, ?_⟩) ?_
      · rcases hχrange w.1 w.2 with h | h <;> simp [h]
      · intro w w' h
        have h' := congrArg Subtype.val h
        exact Subtype.ext h'
    refine h1.trans ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact Finset.card_le_two
  have hrel : (fixV (Subgroup.zpowers φ)).relIndex ((fixV (Subgroup.zpowers φ')).comap p) ≤ 2 := by
    rw [Subgroup.relIndex, ← hχker, Subgroup.index_ker]
    exact hcard
  have hidx : (fixV (Subgroup.zpowers φ)).index = (fixV (Subgroup.zpowers φ')).index *
      (fixV (Subgroup.zpowers φ)).relIndex ((fixV (Subgroup.zpowers φ')).comap p) := by
    rw [← Subgroup.relIndex_mul_index hCC, Subgroup.index_comap_of_surjective _ hp, mul_comm]
  obtain ⟨k, hk⟩ := index_eq_two_pow hW' (fixV (Subgroup.zpowers φ'))
  obtain ⟨r, hr⟩ : ∃ r, r = (fixV (Subgroup.zpowers φ)).relIndex
      ((fixV (Subgroup.zpowers φ')).comap p) := ⟨_, rfl⟩
  rw [← hr] at hrel hidx
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hidx
    exact Subgroup.index_ne_zero_of_finite hidx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrv : padicValNat 2 r ≤ 1 := by
    interval_cases r
    · exact absurd rfl hr0
    · simp
    · rw [padicValNat_self]
  unfold rkIdx
  rw [hidx, padicValNat.mul (by rw [hk]; positivity) hr0]
  omega

theorem dYW_sq : dYW * dYW = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  exact CharTwo.add_self_eq_zero _

theorem W10_sq (w : W10) : w ^ 2 = 1 := by
  rw [sq]
  apply Multiplicative.toAdd.injective
  funext i
  exact CharTwo.add_self_eq_zero _

theorem m24Fix_normal : ((m24Fix dodecadE).subgroupOf m24Pair).Normal := by
  constructor
  intro σ hσ τ
  rw [Subgroup.mem_subgroupOf] at hσ ⊢
  have hτ := τ.2
  refine ⟨AutPerm.mul_mem (AutPerm.mul_mem hτ.1 hσ.1) (AutPerm.inv_mem hτ.1), ?_⟩
  have hσ' : ∀ m ∈ ({dodecadE, dodecadE * G6.allOnes 24} : Set (G6.PermMod 24)),
      G6.permAct 24 (σ : Equiv.Perm (Fin 24)) m = m := by
    rintro m (rfl | rfl)
    · exact hσ.2
    · rw [map_mul, hσ.2, H.Mathieu.permAct_allOnes]
  have hback : G6.permAct 24 (τ : Equiv.Perm (Fin 24))
      (G6.permAct 24 (τ : Equiv.Perm (Fin 24))⁻¹ dodecadE) = dodecadE := by
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, MulAut.mul_apply]
  rw [hσ' _ (m24Pair.inv_mem hτ).2, hback]

theorem card_mulAut_m12_le :
    Nat.card (MulAut ↥((m24Fix dodecadE).subgroupOf m24Pair)) ≤ Nat.card ↥m24Pair := by
  obtain ⟨⟨e⟩, hcard⟩ := m24Fix_dodecadE_props
  have h1 : Nat.card (MulAut ↥((m24Fix dodecadE).subgroupOf m24Pair)) =
      Nat.card (MulAut NativeSporadic.M12) :=
    card_mulAut_congr ((Subgroup.subgroupOfEquivOfLe m24Fix_le_m24Pair).trans e)
  have h2 := CFSG.Sporadic.Schreier.m12_mulAut_card
  rw [CFSG.Sporadic.Mathieu.card_M12] at h2
  obtain ⟨τ, hτ, hτn⟩ := exists_mem_m24Pair_not_mem
  have h3 := Subgroup.relIndex_mul_card (H := m24Fix dodecadE) (K := m24Pair)
  rw [inf_of_le_left m24Fix_le_m24Pair, hcard] at h3
  have h4 : (m24Fix dodecadE).relIndex m24Pair ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    exact fun h => hτn (h hτ)
  have h5 : (m24Fix dodecadE).relIndex m24Pair ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h3
    exact (Nat.card_pos (α := ↥m24Pair)).ne' h3.symm
  rw [h1]
  omega

end CFSG.Quasithin.H13.A5.M12
