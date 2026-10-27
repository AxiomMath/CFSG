module

public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

namespace B1

noncomputable def traceY [Finite V] (Y : Subgroup (MulAut V)) : V →* V :=
  have : Fintype Y := Fintype.ofFinite Y
  { toFun := fun m => ∏ y : Y, (y : MulAut V) m
    map_one' := by simp
    map_mul' := fun a b => by simp [Finset.prod_mul_distrib] }

theorem traceY_apply [Finite V] (Y : Subgroup (MulAut V)) [inst : Fintype Y] (m : V) :
    traceY Y m = ∏ y : Y, (y : MulAut V) m := by
  unfold traceY
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  have : (Fintype.ofFinite Y) = inst := Subsingleton.elim _ _
  subst this
  rfl

theorem traceY_mem_fixV [Finite V] (Y : Subgroup (MulAut V)) (m : V) : traceY Y m ∈ fixV Y := by
  have : Fintype Y := Fintype.ofFinite Y
  rw [traceY_apply]
  intro z hz
  rw [map_prod]
  rw [← Equiv.prod_comp (Equiv.mulLeft (⟨z, hz⟩ : Y)) (fun y : Y => (y : MulAut V) m)]
  exact Finset.prod_congr rfl fun y _ => rfl

theorem traceY_smul [Finite V] (Y : Subgroup (MulAut V)) {y : MulAut V} (hy : y ∈ Y) (m : V) :
    traceY Y (y m) = traceY Y m := by
  have : Fintype Y := Fintype.ofFinite Y
  rw [traceY_apply, traceY_apply]
  rw [← Equiv.prod_comp (Equiv.mulRight (⟨y, hy⟩ : Y)) (fun z : Y => (z : MulAut V) m)]
  exact Finset.prod_congr rfl fun z _ => rfl

theorem traceY_of_mem_fixV [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)}
    (hY : Odd (Nat.card Y)) {m : V} (hm : m ∈ fixV Y) : traceY Y m = m := by
  have : Fintype Y := Fintype.ofFinite Y
  rw [traceY_apply]
  have : ∀ y : Y, (y : MulAut V) m = m := fun y => hm y y.2
  rw [Finset.prod_congr rfl fun y _ => this y, Finset.prod_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card]
  obtain ⟨k, hk⟩ := hY
  rw [hk, pow_succ, pow_mul, hV m, one_pow, one_mul]

theorem coprime_decomp [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)}
    (hY : Odd (Nat.card Y)) {M : Subgroup V} (hM : ∀ y ∈ Y, ∀ m ∈ M, y m ∈ M) :
    (M ⊓ fixV Y) ⊔ commSub M Y = M ∧ (M ⊓ fixV Y) ⊓ commSub M Y = ⊥ := by
  have hker : ∀ c ∈ commSub M Y, traceY Y c = 1 := by
    intro c hc
    refine Subgroup.closure_induction (p := fun c _ => traceY Y c = 1) ?_ ?_ ?_ ?_ hc
    · rintro _ ⟨x, hx, w, hw, rfl⟩
      rw [map_mul, map_inv, traceY_smul Y hx, mul_inv_cancel]
    · exact map_one _
    · intro a b _ _ ha hb
      rw [map_mul, ha, hb, mul_one]
    · intro a _ ha
      rw [map_inv, ha, inv_one]
  constructor
  · refine le_antisymm (sup_le inf_le_left (commSub_le_of_invariant hM)) fun m hm => ?_
    have : Fintype Y := Fintype.ofFinite Y
    have h1 : traceY Y m ∈ M ⊓ fixV Y := by
      refine ⟨?_, traceY_mem_fixV Y m⟩
      rw [traceY_apply]
      exact M.prod_mem fun y _ => hM y y.2 m hm
    have h2 : m * (traceY Y m)⁻¹ ∈ commSub M Y := by
      have hm' : m = m ^ Nat.card Y := by
        obtain ⟨k, hk⟩ := hY
        rw [hk, pow_succ, pow_mul, hV m, one_pow, one_mul]
      have : m * (traceY Y m)⁻¹ = ∏ y : Y, (m * ((y : MulAut V) m)⁻¹) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
          ← hm', Finset.prod_inv_distrib, traceY_apply]
      rw [this]
      refine (commSub M Y).prod_mem fun y _ => ?_
      have : (m * ((y : MulAut V) m)⁻¹) = ((y : MulAut V) m * m⁻¹)⁻¹ := by
        rw [mul_inv_rev, inv_inv, mul_comm]
      rw [this]
      exact (commSub M Y).inv_mem (Subgroup.subset_closure ⟨y, y.2, m, hm, rfl⟩)
    have : m = traceY Y m * (m * (traceY Y m)⁻¹) := by
      rw [mul_comm m (traceY Y m)⁻¹, mul_inv_cancel_left]
    rw [this]
    exact Subgroup.mul_mem_sup h1 h2
  · refine (Subgroup.eq_bot_iff_forall _).2 fun m hm => ?_
    have h1 := traceY_of_mem_fixV hV hY hm.1.2
    have h2 := hker m hm.2
    rw [← h1, h2]

theorem exists_fixed_ne_one [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {B : Subgroup (MulAut V)}
    (hB : IsPGroup 2 B) {M : Subgroup V} (hM : ∀ b ∈ B, ∀ m ∈ M, b m ∈ M) (hne : M ≠ ⊥) :
    ∃ m ∈ M, m ≠ 1 ∧ ∀ b ∈ B, b m = m := by
  let _ : MulAction B M :=
    { smul := fun b m => ⟨(b : MulAut V) m, hM b b.2 m m.2⟩
      one_smul := fun m => Subtype.ext rfl
      mul_smul := fun a b m => Subtype.ext rfl }
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM2 : IsPGroup 2 M := (isPGroup_two_of_sq_eq_one hV).to_subgroup M
  have hdvd : 2 ∣ Nat.card M := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hM2
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne (Subgroup.card_eq_one.mp (by simpa using hn))
    rw [hn]
    exact dvd_pow_self 2 hn0
  have h1 : (1 : M) ∈ MulAction.fixedPoints B M := fun b => Subtype.ext (map_one _)
  obtain ⟨m, hm, hne1⟩ := hB.exists_fixed_point_of_prime_dvd_card_of_fixed_point M hdvd h1
  refine ⟨m, m.2, fun h => hne1 (Subtype.ext h.symm), fun b hb => ?_⟩
  have := hm ⟨b, hb⟩
  exact congrArg Subtype.val this

theorem commSub_invariant_of_commute {Y B : Subgroup (MulAut V)} {M : Subgroup V}
    (hcomm : ∀ y ∈ Y, ∀ b ∈ B, y * b = b * y) (hMB : ∀ b ∈ B, ∀ m ∈ M, b m ∈ M) :
    ∀ b ∈ B, ∀ c ∈ commSub M Y, b c ∈ commSub M Y := by
  intro b hb c hc
  refine Subgroup.closure_induction (p := fun c _ => b c ∈ commSub M Y) ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨y, hy, w, hw, rfl⟩
    have h0 : b (y w) = y (b w) := by
      have := congrArg (fun t : MulAut V => t w) (hcomm y hy b hb)
      simpa only [MulAut.mul_apply] using this.symm
    have h1 : b (y w * w⁻¹) = y (b w) * (b w)⁻¹ := by rw [map_mul, map_inv, h0]
    rw [h1]
    exact Subgroup.subset_closure ⟨y, hy, b w, hMB b hb w hw, rfl⟩
  · rw [map_one]
    exact (commSub M Y).one_mem
  · intro a a' _ _ ha ha'
    rw [map_mul]
    exact (commSub M Y).mul_mem ha ha'
  · intro a _ ha
    rw [map_inv]
    exact (commSub M Y).inv_mem ha

theorem axb [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {Y B : Subgroup (MulAut V)}
    (hY : Odd (Nat.card Y)) (hB : IsPGroup 2 B) (hcomm : ∀ y ∈ Y, ∀ b ∈ B, y * b = b * y)
    {M : Subgroup V} (hMY : ∀ y ∈ Y, ∀ m ∈ M, y m ∈ M) (hMB : ∀ b ∈ B, ∀ m ∈ M, b m ∈ M)
    (hfix : ∀ y ∈ Y, ∀ m ∈ M ⊓ fixV B, y m = m) : M ≤ fixV Y := by
  obtain ⟨hsup, hinf⟩ := coprime_decomp hV hY hMY
  have hM1 : commSub M Y = ⊥ := by
    by_contra hne
    obtain ⟨m, hm, hm1, hmfix⟩ := exists_fixed_ne_one hV hB
      (commSub_invariant_of_commute hcomm hMB) hne
    have hmM : m ∈ M := commSub_le_of_invariant hMY hm
    have hmY : m ∈ fixV Y := fun y hy => hfix y hy m ⟨hmM, hmfix⟩
    have : m ∈ (M ⊓ fixV Y) ⊓ commSub M Y := ⟨⟨hmM, hmY⟩, hm⟩
    rw [hinf] at this
    exact hm1 this
  exact commSub_eq_bot_iff.1 hM1

end B1

end CFSG.Quasithin
