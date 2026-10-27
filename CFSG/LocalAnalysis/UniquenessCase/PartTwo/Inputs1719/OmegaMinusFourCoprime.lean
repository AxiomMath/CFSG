module

public import CFSG.Quasithin.Background.RonanD39Count

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin

theorem card_inf_fixV_sylow_le_of_isPGroup {W : Type} [CommGroup W] [Finite W]
    {X : Subgroup (MulAut W)} {I : Subgroup W} (hI : ∀ x ∈ X, ∀ w ∈ I, x w ∈ I)
    {T : Subgroup ↥X} (hT : IsPGroup 2 ↥T) (P : Sylow 2 ↥X) :
    Nat.card ↥(I ⊓ CFSG.Quasithin.fixV ((P : Subgroup ↥X).map X.subtype)) ≤
      Nat.card ↥(I ⊓ CFSG.Quasithin.fixV (T.map X.subtype)) := by
  classical
  obtain ⟨Q, hTQ⟩ := hT.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥X Q P
  have hconj : ∀ t ∈ T, g * t * g⁻¹ ∈ (P : Subgroup ↥X) := by
    intro t ht
    rw [← hg, Sylow.coe_subgroup_smul]
    have h1 := Subgroup.smul_mem_pointwise_smul t (MulAut.conj g) (Q : Subgroup ↥X) (hTQ ht)
    rwa [MulAut.smul_def, MulAut.conj_apply] at h1
  let f : ↥(I ⊓ CFSG.Quasithin.fixV ((P : Subgroup ↥X).map X.subtype)) →
      ↥(I ⊓ CFSG.Quasithin.fixV (T.map X.subtype)) := fun w =>
    ⟨((g⁻¹ : ↥X) : MulAut W) (w : W), Subgroup.mem_inf.2
      ⟨hI _ (g⁻¹ : ↥X).2 _ (Subgroup.mem_inf.1 w.2).1, by
        rintro _ ⟨t, ht, rfl⟩
        have hfix := (Subgroup.mem_inf.1 w.2).2
        have h1 : ((g * t * g⁻¹ : ↥X) : MulAut W) (w : W) = w :=
          hfix _ ⟨g * t * g⁻¹, hconj t ht, rfl⟩
        have h2 : ((g : ↥X) : MulAut W) ((t : MulAut W) (((g⁻¹ : ↥X) : MulAut W) (w : W))) =
            w := by
          simpa only [Subgroup.coe_mul, MulAut.mul_apply] using h1
        have h3 := congrArg (((g⁻¹ : ↥X) : MulAut W)) h2
        rw [← MulAut.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
          MulAut.one_apply] at h3
        exact h3⟩⟩
  have hf : Function.Injective f := by
    intro w w' hww'
    have h1 : ((g⁻¹ : ↥X) : MulAut W) (w : W) = ((g⁻¹ : ↥X) : MulAut W) (w' : W) :=
      congrArg Subtype.val hww'
    exact Subtype.ext (((g⁻¹ : ↥X) : MulAut W).injective h1)
  exact Nat.card_le_card_of_injective f hf

theorem card_fixV_le_prod_inf_fixV {W : Type} [CommGroup W] [Finite W] {k : ℕ}
    {I : Fin k → Subgroup W} (hind : ∀ i, I i ⊓ (⊥ ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j) ≤ ⊥)
    (hsup : (⊥ ⊔ ⨆ i, I i) = ⊤) {R : Subgroup (MulAut W)}
    (hR : ∀ r ∈ R, ∀ i, ∀ w ∈ I i, r w ∈ I i) :
    Nat.card ↥(CFSG.Quasithin.fixV R) ≤ ∏ i, Nat.card ↥(I i ⊓ CFSG.Quasithin.fixV R) := by
  classical
  have hindI : iSupIndep I := by
    rw [iSupIndep_def]
    intro i
    rw [disjoint_iff, ← le_bot_iff]
    simpa using hind i
  have hsupI : (⨆ i : Fin k, I i) = ⊤ := by simpa using hsup
  have hcomm : Pairwise fun i j : Fin k => ∀ x y : W, x ∈ I i → y ∈ I j → Commute x y :=
    fun _ _ _ x y _ _ => mul_comm x y
  let ψ : (∀ i : Fin k, ↥(I i)) →* W := Subgroup.noncommPiCoprod hcomm
  have hinj : Function.Injective ψ := Subgroup.injective_noncommPiCoprod_of_iSupIndep hindI
  have hsurj : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top, Subgroup.noncommPiCoprod_range, hsupI]
  let Ψ : (∀ i : Fin k, ↥(I i)) ≃* W := MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  have hψ : ∀ u, ψ u = ∏ i, ((u i : ↥(I i)) : W) := fun u => by
    rw [Subgroup.noncommPiCoprod_apply, Finset.noncommProd_eq_prod]
  have hcompfix : ∀ w ∈ CFSG.Quasithin.fixV R, ∀ i,
      ((Ψ.symm w i : ↥(I i)) : W) ∈ CFSG.Quasithin.fixV R := by
    intro w hw i r hr
    let u : ∀ j, ↥(I j) := fun j => ⟨r (Ψ.symm w j), hR r hr j _ (Ψ.symm w j).2⟩
    have hu : ψ u = ψ (Ψ.symm w) := by
      rw [hψ u]
      change ∏ j, r ((Ψ.symm w j : ↥(I j)) : W) = ψ (Ψ.symm w)
      rw [← map_prod, ← hψ]
      change r (Ψ (Ψ.symm w)) = Ψ (Ψ.symm w)
      rw [MulEquiv.apply_symm_apply]
      exact hw r hr
    exact congrArg Subtype.val (congrFun (hinj hu) i)
  let f : ↥(CFSG.Quasithin.fixV R) → ∀ i, ↥(I i ⊓ CFSG.Quasithin.fixV R) := fun w i =>
    ⟨(Ψ.symm w i : W), Subgroup.mem_inf.2 ⟨(Ψ.symm w i).2, hcompfix w w.2 i⟩⟩
  have hf : Function.Injective f := by
    intro w w' h
    have h1 : Ψ.symm w = Ψ.symm w' := by
      funext i
      have h2 : ((Ψ.symm w i : ↥(I i)) : W) = ((Ψ.symm w' i : ↥(I i)) : W) :=
        congrArg (fun u : ↥(I i ⊓ CFSG.Quasithin.fixV R) => (u : W)) (congrFun h i)
      exact Subtype.ext h2
    exact Subtype.ext (Ψ.symm.injective h1)
  calc Nat.card ↥(CFSG.Quasithin.fixV R)
      ≤ Nat.card (∀ i, ↥(I i ⊓ CFSG.Quasithin.fixV R)) := Nat.card_le_card_of_injective f hf
    _ = ∏ i, Nat.card ↥(I i ⊓ CFSG.Quasithin.fixV R) := Nat.card_pi

theorem isPGroup_zpowers_of_pow_seventeen {W : Type} [CommGroup W] {c : MulAut W} {k : ℕ}
    (hc : c ^ (17 ^ k) = 1) : IsPGroup 17 ↥(Subgroup.zpowers c) := by
  intro g
  refine ⟨k, ?_⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 g.2
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm,
    zpow_mul, zpow_natCast, hc, one_zpow]

theorem apply_mem_of_mem_zpowers_of_pow_seventeen {W : Type} [CommGroup W] {c : MulAut W}
    {k : ℕ} (hc : c ^ (17 ^ k) = 1) {D : Subgroup W} (hD : ∀ d ∈ D, c d ∈ D) {g : MulAut W}
    (hg : g ∈ Subgroup.zpowers c) : ∀ d ∈ D, g d ∈ D := by
  have hfin : IsOfFinOrder c :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨17 ^ k, pow_pos (by norm_num) k, hc⟩
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff g c).1 (hfin.mem_powers_iff_mem_zpowers.2 hg)
  subst hn
  clear hg
  induction n with
  | zero => intro d hd; simpa using hd
  | succ n ih =>
    intro d hd
    rw [pow_succ', MulAut.mul_apply]
    exact hD _ (ih d hd)

theorem apply_eq_of_pow_seventeen_of_card_lt {W : Type} [CommGroup W] [Finite W]
    (hsq : ∀ w : W, w ^ 2 = 1) {c : MulAut W} {k : ℕ} (hc : c ^ (17 ^ k) = 1)
    {D : Subgroup W} (hD : ∀ d ∈ D, c d ∈ D) (hcard : Nat.card D < 2 ^ 8) :
    ∀ d ∈ D, c d = d := by
  classical
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  let F := Subgroup.zpowers c
  let Sm : SubMulAction ↥F W :=
    { carrier := D
      smul_mem' := fun g d hd => apply_mem_of_mem_zpowers_of_pow_seventeen hc hD g.2 d hd }
  have hmod := (isPGroup_zpowers_of_pow_seventeen hc).card_modEq_card_fixedPoints ↥Sm
  let E : Subgroup W := D ⊓ CFSG.Quasithin.fixV F
  have hE : Nat.card ↥(MulAction.fixedPoints ↥F ↥Sm) = Nat.card E := by
    refine Nat.card_congr
      { toFun := fun x => ⟨((x : ↥Sm) : W), Subgroup.mem_inf.2 ⟨(x : ↥Sm).2, fun g hg => by
          have h1 := x.2 ⟨g, hg⟩
          exact congrArg Subtype.val h1⟩⟩
        invFun := fun x => ⟨⟨(x : W), (Subgroup.mem_inf.1 x.2).1⟩, fun g => by
          apply Subtype.ext
          exact (Subgroup.mem_inf.1 x.2).2 g g.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hSm : Nat.card ↥Sm = Nat.card D := rfl
  rw [hE, hSm] at hmod
  have h2W : IsPGroup 2 W := fun w => ⟨1, by rw [pow_one]; exact hsq w⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 (h2W.to_subgroup D)
  have hED : E ≤ D := inf_le_left
  obtain ⟨b, hb, hbE⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (ha ▸ Subgroup.card_dvd_of_le hED)
  have ha8 : a < 8 := by
    rw [ha] at hcard
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 hcard
  have key : ∀ a < 8, ∀ b ≤ a, 2 ^ a % 17 = 2 ^ b % 17 → b = a := by decide
  have hba : b = a := key a ha8 b hb (by rw [← ha, ← hbE]; exact hmod)
  have hEeq : E = D := Subgroup.eq_of_le_of_card_ge hED (by rw [ha, hbE, hba])
  intro d hd
  have hdE : d ∈ E := hEeq ▸ hd
  exact (Subgroup.mem_inf.1 hdE).2 c (Subgroup.mem_zpowers c)

theorem eq_one_of_commute_of_fixV_le {W : Type} [CommGroup W] [Finite W]
    (hsq : ∀ w : W, w ^ 2 = 1) {c : MulAut W} {k : ℕ} (hc : c ^ (17 ^ k) = 1)
    {R : Subgroup (MulAut W)} (hR : IsPGroup 2 ↥R) (hRc : ∀ r ∈ R, r * c = c * r)
    (hfix : ∀ w ∈ CFSG.Quasithin.fixV R, c w = w) : c = 1 := by
  let φ : W →* W :=
    { toFun := fun w => c w * w⁻¹
      map_one' := by rw [map_one, inv_one, mul_one]
      map_mul' := fun x y => by
        rw [map_mul, mul_inv]
        exact mul_mul_mul_comm _ _ _ _ }
  have hφ : ∀ w, φ w = c w * w⁻¹ := fun w => rfl
  have hcap : ∀ w ∈ φ.range, c w = w → w = 1 := by
    rintro w ⟨v, rfl⟩ hw
    have hcv : c v = φ v * v := by rw [hφ, inv_mul_cancel_right]
    have hpow : ∀ n : ℕ, (c ^ n) v = φ v ^ n * v := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hw, hcv, pow_succ, mul_assoc]
    have h1 := hpow (17 ^ k)
    rw [hc, MulAut.one_apply] at h1
    have h2 : φ v ^ (17 ^ k) = 1 := by
      have := congrArg (· * v⁻¹) h1
      simpa using this.symm
    obtain ⟨m, hm⟩ : Odd (17 ^ k) := Odd.pow (by norm_num)
    rw [hm, pow_succ, pow_mul, hsq, one_pow, one_mul] at h2
    exact h2
  have hRφ : ∀ r ∈ R, ∀ w ∈ φ.range, r w ∈ φ.range := by
    rintro r hr w ⟨v, rfl⟩
    refine ⟨r v, ?_⟩
    rw [hφ, hφ, map_mul, map_inv, ← MulAut.mul_apply, ← MulAut.mul_apply, hRc r hr]
  have hbot : φ.range = ⊥ := by
    by_contra hne
    obtain ⟨d, hd, hd1, hdR⟩ :=
      CFSG.Quasithin.RonanD39.exists_fixed_ne_one_of_isPGroup hsq hR hRφ hne
    exact hd1 (hcap d hd (hfix d hdR))
  ext v
  have hv : φ v = 1 := by
    have : φ v ∈ φ.range := ⟨v, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  rw [hφ, mul_inv_eq_one] at hv
  rw [hv, MulAut.one_apply]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
