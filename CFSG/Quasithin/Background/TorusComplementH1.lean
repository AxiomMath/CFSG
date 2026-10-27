module

public import CFSG.Quasithin.Background.B4Models
public import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.Quasithin

open scoped Matrix

section TorusComplement

variable {W : Type} [CommGroup W]

theorem eq_one_of_mem_range_commHom (hW : ∀ w : W, w ^ 2 = 1) {t : MulAut W}
    (hodd : Odd (orderOf t)) {u : W} (hu : u ∈ (CFSG.Quasithin.commHom t).range)
    (hfix : t u = u) : u = 1 := by
  obtain ⟨w, rfl⟩ := hu
  set u := CFSG.Quasithin.commHom t w with hu
  have htw : t w = u * w := by rw [hu, CFSG.Quasithin.commHom_apply, inv_mul_cancel_right]
  have hpow : ∀ k : ℕ, (t ^ k) w = w * u ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hfix, htw, mul_comm u w, mul_assoc,
        ← pow_succ']
  have h1 : u ^ orderOf t = 1 := by
    have := hpow (orderOf t)
    rw [pow_orderOf_eq_one, MulAut.one_apply] at this
    exact (mul_eq_left.mp this.symm)
  obtain ⟨j, hj⟩ := hodd
  rw [hj, pow_succ, pow_mul, hW, one_pow, one_mul] at h1
  exact h1

theorem exists_commHom_eq [Finite W] {t : MulAut W} {U : Subgroup W} (hU : ∀ u ∈ U, t u ∈ U)
    (hfpf : ∀ u ∈ U, t u = u → u = 1) {u : W} (hu : u ∈ U) : ∃ v ∈ U, t v * v⁻¹ = u := by
  let f : U → U := fun v => ⟨t v * v⁻¹, U.mul_mem (hU v v.2) (U.inv_mem v.2)⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h : t (a : W) * (a : W)⁻¹ = t b * (b : W)⁻¹ := congrArg Subtype.val hab
    have h2 : t ((a : W) * (b : W)⁻¹) = (a : W) * (b : W)⁻¹ := by
      rw [map_mul, map_inv]
      calc t (a : W) * (t (b : W))⁻¹ = (t (a : W) * (a : W)⁻¹) * (a : W) * (t (b : W))⁻¹ := by
            group
        _ = (t (b : W) * (b : W)⁻¹) * (a : W) * (t (b : W))⁻¹ := by rw [h]
        _ = (a : W) * (b : W)⁻¹ := by rw [mul_right_comm, mul_inv_cancel_comm, mul_comm]
    have h3 := hfpf _ (U.mul_mem a.2 (U.inv_mem b.2)) h2
    exact Subtype.ext (mul_inv_eq_one.mp h3)
  obtain ⟨v, hv⟩ := (Finite.injective_iff_surjective.mp hf) ⟨u, hu⟩
  exact ⟨v, v.2, congrArg Subtype.val hv⟩

theorem fixV_eq_bot_of_torus [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {H : Subgroup (MulAut W)}
    {T : Set (MulAut W)} {t₀ : MulAut W} (ht₀ : t₀ ∈ T) (hTH : T ⊆ H)
    (hodd : ∀ t ∈ T, Odd (orderOf t)) (hfix : ∀ t ∈ T, ∀ w : W, t w = w → w ∈ fixV H)
    (hcomm : ∀ t ∈ T, ∀ t' ∈ T, Commute t t')
    (hgen : H ≤ Subgroup.closure {g | ∃ t ∈ T, Commute g t})
    (hHW : commSub ⊤ H = ⊤) : fixV H = ⊥ := by
  have hZt : ∀ t ∈ T, ∀ w ∈ fixV H, t w = w := fun t ht w hw => hw t (hTH ht)
  have hfpf : ∀ t ∈ T, ∀ t' ∈ T, ∀ u ∈ (CFSG.Quasithin.commHom t).range, t' u = u → u = 1 :=
    fun t ht t' ht' u hu h =>
      eq_one_of_mem_range_commHom hW (hodd t ht) hu (hZt t ht u (hfix t' ht' u h))
  have hinv : ∀ t : MulAut W, ∀ g : MulAut W, Commute g t → ∀ u ∈ (CFSG.Quasithin.commHom t).range,
      g u ∈ (CFSG.Quasithin.commHom t).range := by
    rintro t g hg _ ⟨w, rfl⟩
    refine ⟨g w, ?_⟩
    rw [CFSG.Quasithin.commHom_apply, CFSG.Quasithin.commHom_apply, map_mul, map_inv,
      ← MulAut.mul_apply, ← hg.eq, MulAut.mul_apply]
  have hle : ∀ t ∈ T, ∀ t' ∈ T,
      (CFSG.Quasithin.commHom t).range ≤ (CFSG.Quasithin.commHom t').range := by
    intro t ht t' ht' u hu
    obtain ⟨v, -, hv⟩ := exists_commHom_eq (U := (CFSG.Quasithin.commHom t).range)
      (fun x hx => hinv t t' (hcomm t' ht' t ht) x hx) (fun x hx h => hfpf t ht t' ht' x hx h) hu
    exact ⟨v, hv⟩
  set U := (CFSG.Quasithin.commHom t₀).range with hUdef
  have hU : ∀ t ∈ T, (CFSG.Quasithin.commHom t).range = U := fun t ht =>
    le_antisymm (hle t ht t₀ ht₀) (hle t₀ ht₀ t ht)
  let S : Subgroup (MulAut W) :=
    { carrier := {g | ∀ u ∈ U, g u ∈ U ∧ g⁻¹ u ∈ U}
      one_mem' := fun u hu => ⟨hu, by simpa using hu⟩
      mul_mem' := by
        intro a b ha hb u hu
        refine ⟨?_, ?_⟩
        · rw [MulAut.mul_apply]
          exact (ha _ (hb u hu).1).1
        · rw [mul_inv_rev, MulAut.mul_apply]
          exact (hb _ (ha u hu).2).2
      inv_mem' := by
        intro a ha u hu
        exact ⟨(ha u hu).2, by simpa using (ha u hu).1⟩ }
  have hHS : H ≤ S := by
    refine hgen.trans ((Subgroup.closure_le S).mpr ?_)
    rintro g ⟨t, ht, hg⟩ u hu
    rw [← hU t ht] at hu ⊢
    exact ⟨hinv t g hg u hu, hinv t g⁻¹ hg.inv_left u hu⟩
  have hdec : ∀ w : W, ∃ v ∈ U, w * v⁻¹ ∈ fixV H := by
    intro w
    have h0 : CFSG.Quasithin.commHom t₀ w ∈ U := ⟨w, rfl⟩
    obtain ⟨v, hvU, hv⟩ := exists_commHom_eq (U := U)
      (fun x hx => hinv t₀ t₀ (Commute.refl t₀) x hx) (fun x hx h => hfpf t₀ ht₀ t₀ ht₀ x hx h) h0
    refine ⟨v, hvU, hfix t₀ ht₀ _ ?_⟩
    rw [CFSG.Quasithin.commHom_apply] at hv
    rw [map_mul, map_inv]
    calc t₀ w * (t₀ v)⁻¹ = (t₀ w * w⁻¹) * w * (t₀ v)⁻¹ := by group
      _ = (t₀ v * v⁻¹) * w * (t₀ v)⁻¹ := by rw [hv]
      _ = w * v⁻¹ := by rw [mul_right_comm, mul_inv_cancel_comm, mul_comm]
  have hcU : commSub ⊤ H ≤ U := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, -, rfl⟩
    obtain ⟨v, hvU, hz⟩ := hdec w
    have hxz : x (w * v⁻¹) = w * v⁻¹ := hz x hx
    have : x w * w⁻¹ = x v * v⁻¹ := by
      obtain ⟨a, rfl⟩ : ∃ a, w = a * v := ⟨w * v⁻¹, by group⟩
      have hxa : x a = a := by simpa using hxz
      rw [map_mul, hxa, mul_inv_rev, mul_comm v⁻¹ a⁻¹, mul_assoc, ← mul_assoc (x v),
        mul_comm (x v) a⁻¹, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [SetLike.mem_coe, this]
    exact U.mul_mem (hHS hx v hvU).1 (U.inv_mem hvU)
  rw [hHW] at hcU
  rw [eq_bot_iff]
  intro z hz
  exact Subgroup.mem_bot.mpr
    (eq_one_of_mem_range_commHom hW (hodd t₀ ht₀) (hcU (Subgroup.mem_top z)) (hZt t₀ ht₀ z hz))

end TorusComplement

section Realization

@[expose] def HasFpfTorusGen {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) : Prop :=
  ∃ T₀ : Set ↥Γ, T₀.Nonempty ∧ (∀ γ ∈ T₀, Odd (orderOf γ)) ∧
    (∀ γ ∈ T₀, ∀ v : ι → K,
      ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ v = v → v = 0) ∧
    (∀ γ ∈ T₀, ∀ γ' ∈ T₀, Commute γ γ') ∧
    (⊤ : Subgroup ↥Γ) ≤ Subgroup.closure {g | ∃ γ ∈ T₀, Commute g γ}

variable {W : Type} [CommGroup W] [Finite W]

theorem fixV_eq_bot_of_realizesVia_nat {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [CharP K 2] {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} (hΓ : HasFpfTorusGen Γ)
    {H : Subgroup (MulAut W)} {π : ↥Γ →* ↥H}
    (hπ : (FFModel.nat Γ).RealizesVia H ⊤ (fixV H) π)
    (hHW : commSub ⊤ H = ⊤) : fixV H = ⊥ := by
  classical
  obtain ⟨T₀, ⟨γ₀, hγ₀⟩, hodd, hfpf, hcomm, hgen⟩ := hΓ
  obtain ⟨hsurj, -, -, -, -, -, -, β, -, hβker, hβe⟩ := hπ
  have hamb : ∀ x : Multiplicative (ι → K), x ^ 2 = 1 := by
    intro x
    rw [pow_two]
    show Multiplicative.ofAdd (Multiplicative.toAdd x + Multiplicative.toAdd x) = 1
    have h0 : Multiplicative.toAdd x + Multiplicative.toAdd x = 0 := by
      funext i
      exact CharTwo.add_self_eq_zero _
    rw [h0]
    rfl
  have hq : ∀ y : ↥(FFModel.nat Γ).sec ⧸ (FFModel.nat Γ).ker.subgroupOf (FFModel.nat Γ).sec,
      y ^ 2 = 1 := by
    intro y
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_pow, show m ^ 2 = 1 from Subtype.ext (hamb _), QuotientGroup.mk_one]
  have hsq : ∀ w : W, w ^ 2 ∈ fixV H := by
    intro w
    refine (hβker ⟨w ^ 2, Subgroup.mem_top _⟩).1 ?_
    have : (⟨w ^ 2, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup W)) = ⟨w, Subgroup.mem_top _⟩ ^ 2 := rfl
    rw [this, map_pow, hq]
  have hW : ∀ w : W, w ^ 2 = 1 := by
    intro w
    have hw : w ∈ commSub ⊤ H := by
      rw [hHW]
      exact Subgroup.mem_top w
    induction hw using Subgroup.closure_induction with
    | mem c hc =>
      obtain ⟨x, hx, v, -, rfl⟩ := hc
      rw [mul_pow, ← map_pow, hsq v x hx, inv_pow, mul_inv_cancel]
    | one => exact one_pow 2
    | mul a b _ _ ha hb => rw [mul_pow, ha, hb, one_mul]
    | inv a _ ha => rw [inv_pow, ha, inv_one]
  let f : ↥Γ →* MulAut W := H.subtype.comp π
  let T : Set (MulAut W) := f '' T₀
  refine fixV_eq_bot_of_torus hW (T := T) (t₀ := f γ₀) ⟨γ₀, hγ₀, rfl⟩ ?_ ?_ ?_ ?_ ?_ hHW
  · rintro _ ⟨γ, -, rfl⟩
    exact (π γ).2
  · rintro _ ⟨γ, hγ, rfl⟩
    exact (hodd γ hγ).of_dvd_nat (orderOf_map_dvd f γ)
  · rintro _ ⟨γ, hγ, rfl⟩ w hw
    refine (hβker ⟨w, Subgroup.mem_top _⟩).1 ?_
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨w, Subgroup.mem_top _⟩)
    have he := hβe γ ⟨w, Subgroup.mem_top _⟩ m (Subgroup.mem_top _) (Subgroup.mem_top _) hm.symm
    have hw' : (⟨((π γ : ↥H) : MulAut W) w, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup W)) =
        ⟨w, Subgroup.mem_top _⟩ := Subtype.ext hw
    have he' : β ⟨w, Subgroup.mem_top _⟩ = QuotientGroup.mk
        ⟨(FFModel.nat Γ).act γ (m : (FFModel.nat Γ).Amb), Subgroup.mem_top _⟩ := by
      rw [← hw']
      exact he
    rw [← hm, QuotientGroup.eq] at he'
    replace he := he'
    have h1 : m⁻¹ * ⟨(FFModel.nat Γ).act γ (m : (FFModel.nat Γ).Amb), Subgroup.mem_top _⟩ = 1 := by
      have h0 := Subgroup.mem_subgroupOf.mp he
      exact Subtype.ext (Subgroup.mem_bot.mp h0)
    let m' : Multiplicative (ι → K) := (m : (FFModel.nat Γ).Amb)
    have h2 : (FFModel.nat Γ).act γ m' = m' :=
      congrArg Subtype.val (inv_mul_eq_one.mp h1).symm
    have h3 : ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd m' =
        Multiplicative.toAdd m' :=
      congrArg Multiplicative.toAdd h2
    have h4 := hfpf γ hγ _ h3
    rw [← hm]
    have hm1 : m = 1 := Subtype.ext (by
      show m' = 1
      rw [← ofAdd_toAdd m', h4]
      rfl)
    rw [hm1, QuotientGroup.mk_one]
  · rintro _ ⟨γ, hγ, rfl⟩ _ ⟨γ', hγ', rfl⟩
    exact (hcomm γ hγ γ' hγ').map f
  · intro h hh
    obtain ⟨γ, hγ⟩ := hsurj ⟨h, hh⟩
    have hmem : f γ ∈ (Subgroup.closure {g | ∃ γ ∈ T₀, Commute g γ}).map f :=
      Subgroup.mem_map_of_mem f (hgen (Subgroup.mem_top γ))
    rw [MonoidHom.map_closure] at hmem
    have hfγ : f γ = h := by
      show ((π γ : ↥H) : MulAut W) = h
      exact congrArg Subtype.val hγ
    rw [hfγ] at hmem
    refine Subgroup.closure_mono ?_ hmem
    rintro _ ⟨g, ⟨γ', hγ', hc⟩, rfl⟩
    exact ⟨f γ', ⟨γ', hγ', rfl⟩, hc.map f⟩

end Realization

end CFSG.Quasithin

