module

public import CFSG.GroupTheory.FourGroupOddOrderIdentity
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer

public section

namespace CFSG.RankThree.PartTwo.Sec17.HeadProof

open CFSG

section FourGroup

variable {X : Type*} [Group X] [Finite X]

theorem mem_of_fpf {U : Subgroup X} (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hU2 : ∀ u ∈ U, u ^ 2 = 1) (hU4 : Nat.card U = 4) (σ : MulAut X)
    (hσU : ∀ u ∈ U, σ u ∈ U) (hfpf : ∀ u ∈ U, σ u = u → u = 1) {u : X} (hu : u ∈ U)
    (hu1 : u ≠ 1) : ∀ v ∈ U, v = 1 ∨ v = u ∨ v = σ u ∨ v = σ (σ u) := by
  classical
  have hσu : σ u ∈ U := hσU u hu
  have hσσu : σ (σ u) ∈ U := hσU _ hσu
  have h1 : σ u ≠ u := fun h => hu1 (hfpf u hu h)
  have h2 : σ u ≠ 1 := fun h => hu1 (σ.injective (h.trans σ.map_one.symm))
  have h3 : σ (σ u) ≠ 1 := fun h => h2 (σ.injective (h.trans σ.map_one.symm))
  have h4 : σ (σ u) ≠ σ u := fun h => h1 (σ.injective h)
  have h5 : σ (σ u) ≠ u := by
    intro h
    have hw : σ (u * σ u) = u * σ u := by
      rw [map_mul, h, hUc _ hσu _ hu]
    have hw1 := hfpf _ (U.mul_mem hu hσu) hw
    have hinv : σ u = u⁻¹ := eq_inv_of_mul_eq_one_right hw1
    have huu : u⁻¹ = u := by
      have := hU2 u hu
      rw [sq] at this
      exact inv_eq_of_mul_eq_one_right this
    exact h1 (hinv.trans huu)
  intro v hv
  by_contra hne
  push Not at hne
  obtain ⟨hv1, hvu, hvσ, hvσσ⟩ := hne
  set s : Finset X := {1, u, σ u, σ (σ u), v} with hs
  have hscard : s.card = 5 := by
    rw [hs, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_pair hvσσ.symm]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h4.symm, hvσ.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h1.symm, h5.symm, hvu.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hu1.symm, h2.symm, h3.symm, hv1.symm⟩
  have hsub : (s : Set X) ⊆ (U : Set X) := by
    intro x hx
    simp only [hs, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    exacts [U.one_mem, hu, hσu, hσσu, hv]
  have hle : (s : Set X).ncard ≤ (U : Set X).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hscard, ← Nat.card_coe_set_eq] at hle
  change 5 ≤ Nat.card U at hle
  omega

theorem eq_bot_or_eq_of_fpf {U : Subgroup X} (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hU2 : ∀ u ∈ U, u ^ 2 = 1) (hU4 : Nat.card U = 4) (σ : MulAut X)
    (hσU : ∀ u ∈ U, σ u ∈ U) (hfpf : ∀ u ∈ U, σ u = u → u = 1) {K : Subgroup X} (hKU : K ≤ U)
    (hσK : ∀ k ∈ K, σ k ∈ K) : K = ⊥ ∨ K = U := by
  rcases K.bot_or_exists_ne_one with hK | ⟨u, huK, hu1⟩
  · exact Or.inl hK
  refine Or.inr (le_antisymm hKU fun v hv => ?_)
  rcases mem_of_fpf hUc hU2 hU4 σ hσU hfpf (hKU huK) hu1 v hv with rfl | rfl | rfl | rfl
  exacts [K.one_mem, huK, hσK _ huK, hσK _ (hσK _ huK)]

end FourGroup

section BW

variable {Q : Type*} [Group Q] [Finite Q]

omit [Finite Q] in
theorem map_inf_centralizer_le {V : Subgroup Q} (σ : MulAut Q) (hσV : ∀ v ∈ V, σ v ∈ V) (x : Q) :
    (V ⊓ Subgroup.centralizer ({x} : Set Q)).map σ.toMonoidHom ≤
      V ⊓ Subgroup.centralizer ({σ x} : Set Q) := by
  rintro _ ⟨y, ⟨hyV, hyx⟩, rfl⟩
  refine ⟨hσV y hyV, ?_⟩
  have hyx' : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.mp hyx
  show σ y ∈ Subgroup.centralizer ({σ x} : Set Q)
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hyx']

theorem card_inf_centralizer_map {V : Subgroup Q} (σ : MulAut Q) (hσV : ∀ v ∈ V, σ v ∈ V)
    (x : Q) : Nat.card (V ⊓ Subgroup.centralizer ({σ x} : Set Q) : Subgroup Q) =
      Nat.card (V ⊓ Subgroup.centralizer ({x} : Set Q) : Subgroup Q) := by
  have hVmap : V.map σ.toMonoidHom = V := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨v, hv, rfl⟩
      exact hσV v hv
    · rw [Subgroup.card_map_of_injective σ.injective]
  have hσinvV : ∀ v ∈ V, σ.symm v ∈ V := by
    intro v hv
    rw [← hVmap] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    simpa using hw
  refine le_antisymm ?_ ?_
  · have h := Subgroup.card_le_of_le (map_inf_centralizer_le σ.symm hσinvV (σ x))
    rwa [Subgroup.card_map_of_injective σ.symm.injective, MulEquiv.symm_apply_apply] at h
  · have h := Subgroup.card_le_of_le (map_inf_centralizer_le σ hσV x)
    rwa [Subgroup.card_map_of_injective σ.injective] at h

omit [Finite Q] in
theorem isKleinFour_of {U : Subgroup Q} (hU2 : ∀ u ∈ U, u ^ 2 = 1) (hU4 : Nat.card U = 4) :
    IsKleinFour U := by
  refine ⟨hU4, ?_⟩
  have hdvd : Monoid.exponent U ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by simpa using hU2 x x.2)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exfalso
    have : Subsingleton U := Monoid.exp_eq_one_iff.mp h1
    have := Finite.card_le_one_iff_subsingleton.mpr this
    omega
  · exact h2

theorem card_mul_sq_eq_cube {U V : Subgroup Q} [V.Normal] (hVodd : Odd (Nat.card V))
    (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hU2 : ∀ u ∈ U, u ^ 2 = 1) (hU4 : Nat.card U = 4)
    (σ : MulAut Q) (hσU : ∀ u ∈ U, σ u ∈ U) (hfpf : ∀ u ∈ U, σ u = u → u = 1)
    (hσV : ∀ v ∈ V, σ v ∈ V) {u : Q} (hu : u ∈ U) (hu1 : u ≠ 1) :
    Nat.card V * Nat.card (V ⊓ Subgroup.centralizer (U : Set Q) : Subgroup Q) ^ 2 =
      Nat.card (V ⊓ Subgroup.centralizer ({u} : Set Q) : Subgroup Q) ^ 3 := by
  classical
  have : IsKleinFour U := isKleinFour_of hU2 hU4
  have : Fintype U := Fintype.ofFinite U
  let _ : MulDistribMulAction U V :=
    MulDistribMulAction.compHom V ((MulAut.conjNormal (H := V)).comp U.subtype)
  have hsmul : ∀ (a : U) (v : V), ((a • v : V) : Q) = (a : Q) * v * (a : Q)⁻¹ := fun a v => rfl
  have hBW := (CFSG.GroupTheory.odd_group_four_group_centralizer_order_identity
    (A := U) (X := V) hVodd).1
  have hfixU : Nat.card (fixedPointSubgroup U V) =
      Nat.card (V ⊓ Subgroup.centralizer (U : Set Q) : Subgroup Q) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨((x : V) : Q), (x : V).2, ?_⟩
        invFun := fun y => ⟨⟨y, y.2.1⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · show ((x : V) : Q) ∈ Subgroup.centralizer (U : Set Q)
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h := congrArg Subtype.val ((FixedPoints.mem_subgroup U V _).mp x.2 ⟨a, ha⟩)
      rw [hsmul] at h
      calc a * (x : V) = a * (x : V) * a⁻¹ * a := by group
        _ = (x : V) * a := by rw [h]
    · rw [FixedPoints.mem_subgroup]
      intro a
      apply Subtype.ext
      rw [hsmul]
      have h := Subgroup.mem_centralizer_iff.mp y.2.2 a a.2
      calc (a : Q) * y * (a : Q)⁻¹ = y * a * (a : Q)⁻¹ := by rw [h]
        _ = y := by group
  have hfix : ∀ a : U, Nat.card (fixedPointSubgroup (Subgroup.zpowers a) V) =
      Nat.card (V ⊓ Subgroup.centralizer ({(a : Q)} : Set Q) : Subgroup Q) := by
    intro a
    have hmem : ∀ x : V, x ∈ fixedPointSubgroup (Subgroup.zpowers a) V ↔ a • x = x := by
      intro x
      constructor
      · intro h
        exact h ⟨a, Subgroup.mem_zpowers a⟩
      · intro h
        rintro ⟨g, hg⟩
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
        have hb : a ∈ MulAction.stabilizer U x := h
        exact (MulAction.stabilizer U x).zpow_mem hb m
    refine Nat.card_congr
      { toFun := fun x => ⟨((x : V) : Q), (x : V).2, ?_⟩
        invFun := fun y => ⟨⟨y, y.2.1⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · show ((x : V) : Q) ∈ Subgroup.centralizer ({(a : Q)} : Set Q)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := congrArg Subtype.val ((hmem x).mp x.2)
      rw [hsmul] at h
      calc (x : V) * (a : Q) = (a : Q) * (x : V) * (a : Q)⁻¹ * a := by rw [h]
        _ = a * (x : V) := by group
    · rw [hmem]
      apply Subtype.ext
      rw [hsmul]
      have h := Subgroup.mem_centralizer_singleton_iff.mp y.2.2
      change (a : Q) * y * (a : Q)⁻¹ = y
      calc (a : Q) * y * (a : Q)⁻¹ = y * a * (a : Q)⁻¹ := by rw [h]
        _ = y := by group
  have hall : ∀ a ∈ Finset.univ.erase (1 : U),
      Nat.card (fixedPointSubgroup (Subgroup.zpowers a) V) =
        Nat.card (V ⊓ Subgroup.centralizer ({u} : Set Q) : Subgroup Q) := by
    intro a ha
    have ha1 : (a : Q) ≠ 1 := fun h => (Finset.mem_erase.mp ha).1 (Subtype.ext h)
    rw [hfix a]
    rcases mem_of_fpf hUc hU2 hU4 σ hσU hfpf hu hu1 a a.2 with h | h | h | h
    · exact absurd h ha1
    · rw [h]
    · rw [h, card_inf_centralizer_map σ hσV]
    · rw [h, card_inf_centralizer_map σ hσV, card_inf_centralizer_map σ hσV]
  rw [hfixU, Finset.prod_congr rfl hall, Finset.prod_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    ← Nat.card_eq_fintype_card, hU4] at hBW
  exact hBW

end BW

section Aux

variable {Q : Type*} [Group Q]

omit [Group Q] in
theorem card_map_of_injOn {H : Type*} [Group Q] [Group H] (f : Q →* H) {T : Subgroup Q}
    (hinj : ∀ a ∈ T, ∀ b ∈ T, f a = f b → a = b) : Nat.card (T.map f) = Nat.card T := by
  change Nat.card (↑(T.map f) : Set H) = Nat.card (T : Set Q)
  rw [Subgroup.coe_map, Nat.card_image_of_injOn fun a ha b hb h => hinj a ha b hb h]

theorem pCore_quot_pCore_eq_bot [Finite Q] (p : ℕ) : pCore p (Q ⧸ pCore p Q) = ⊥ := by
  set N : Subgroup Q := pCore p Q with hN
  set K : Subgroup Q := (pCore p (Q ⧸ N)).comap (QuotientGroup.mk' N) with hK
  have hKp : IsPGroup p K := by
    rintro ⟨k, hk⟩
    obtain ⟨a, ha⟩ := (pCore_isPGroup (G := Q ⧸ N) (p := p)) ⟨_, hk⟩
    have h1 : k ^ p ^ a ∈ N := by
      have := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    obtain ⟨b, hb⟩ := (pCore_isPGroup (G := Q) (p := p)) ⟨_, h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hKN : K ≤ N := le_sSup ⟨inferInstance, hKp⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  have hyN : y ∈ N := hKN hx
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hyN

theorem map_eq_of_forall_mem [Finite Q] (σ : MulAut Q) {R : Subgroup Q}
    (hσR : ∀ x ∈ R, σ x ∈ R) : R.map σ.toMonoidHom = R := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact hσR x hx
  · rw [Subgroup.card_map_of_injective σ.injective]

theorem mem_map_of_characteristic [Finite Q] (σ : MulAut Q) {R : Subgroup Q}
    (hσR : ∀ x ∈ R, σ x ∈ R) (D₀ : Subgroup R) [hD₀ : D₀.Characteristic] :
    ∀ x ∈ D₀.map R.subtype, σ x ∈ D₀.map R.subtype := by
  have hRmap := map_eq_of_forall_mem σ hσR
  let τ : R ≃* R := (σ.subgroupMap R).trans (MulEquiv.subgroupCongr hRmap)
  have hτ : ∀ y : R, ((τ y : R) : Q) = σ y := fun y => rfl
  have hfix : D₀.map τ.toMonoidHom = D₀ := Subgroup.characteristic_iff_map_eq.mp hD₀ τ
  rintro _ ⟨d, hd, rfl⟩
  have hτd : τ d ∈ D₀ := by
    rw [← hfix]
    exact Subgroup.mem_map_of_mem _ hd
  exact ⟨τ d, hτd, hτ d⟩

theorem exists_pCore_not_le_centralizer [Finite Q] [Group.IsSolvable Q] (hO2 : pCore 2 Q = ⊥)
    {U : Subgroup Q} (hU2 : IsPGroup 2 U) (hU : U ≠ ⊥) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ ¬ U ≤ Subgroup.centralizer (pCore q Q : Set Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hall
  push Not at hall
  have hF : U ≤ Subgroup.centralizer (fittingSubgroup Q : Set Q) := by
    apply subgroup_le_centralizer_fitting_of_le_centralizer_pCores
    intro q
    have hq : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
    by_cases hq2 : q.1.1 = 2
    · intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [hq2, hO2] at hy
      rw [(Subgroup.mem_bot).mp hy, one_mul, mul_one]
    · exact hall _ hq hq2
  have hUF : U ≤ fittingSubgroup Q :=
    hF.trans (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable inferInstance)
  obtain ⟨P, hP⟩ := (hU2.comap_subtype (K := fittingSubgroup Q)).exists_le_sylow
  have hPle := Sylow.map_le_pCore (fittingSubgroup_normal) inferInstance 2 P
  apply hU
  rw [eq_bot_iff]
  intro x hx
  have hxF : x ∈ fittingSubgroup Q := hUF hx
  have hxP : (⟨x, hxF⟩ : fittingSubgroup Q) ∈ (P : Subgroup (fittingSubgroup Q)) :=
    hP (Subgroup.mem_comap.mpr hx)
  have := hPle ⟨⟨x, hxF⟩, hxP, rfl⟩
  rwa [hO2] at this

theorem exists_lift_of_quotient [Finite Q] {N : Subgroup Q} [N.Normal] (hN : IsPGroup 2 N)
    {q : ℕ} [hq : Fact q.Prime] (hq2 : q ≠ 2) (E : Subgroup (Q ⧸ N))
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hEq : ∀ x ∈ E, x ^ q = 1) :
    ∃ T : Subgroup Q, (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) ∧ (∀ x ∈ T, x ^ q = 1) ∧
      Nat.card T = Nat.card E := by
  set π := QuotientGroup.mk' N with hπ
  set E' : Subgroup Q := E.comap π with hE'
  let f : E' →* E := (π.comp E'.subtype).codRestrict E fun x => x.2
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hEp : IsPGroup q E := fun x => ⟨1, Subtype.ext (by simpa using hEq x x.2)⟩
  obtain ⟨P⟩ : Nonempty (Sylow q E') := inferInstance
  have hPtop : (P.mapSurjective hf : Subgroup E) = ⊤ :=
    ((P.mapSurjective hf).is_maximal' (IsPGroup.of_equiv hEp Subgroup.topEquiv.symm)
      le_top).symm
  set T : Subgroup Q := (P : Subgroup E').map E'.subtype with hT
  have hTq : IsPGroup q T := P.isPGroup'.map E'.subtype
  have hinj : ∀ a ∈ T, ∀ b ∈ T, π a = π b → a = b := by
    intro a ha b hb hab
    have hmem : a⁻¹ * b ∈ T := T.mul_mem (T.inv_mem ha) hb
    have hN' : a⁻¹ * b ∈ N := by
      rw [← QuotientGroup.eq_one_iff (N := N), QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      change (π a)⁻¹ * π b = 1
      rw [hab, inv_mul_cancel]
    obtain ⟨i, hi⟩ := hTq ⟨_, hmem⟩
    obtain ⟨j, hj⟩ := hN ⟨_, hN'⟩
    have hi' : (a⁻¹ * b) ^ q ^ i = 1 := by simpa using congrArg Subtype.val hi
    have hj' : (a⁻¹ * b) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hcop : Nat.Coprime (q ^ i) (2 ^ j) :=
      Nat.Coprime.pow i j ((Nat.coprime_primes hq.out Nat.prime_two).mpr hq2)
    have h1 : (a⁻¹ * b) ^ (q ^ i).gcd (2 ^ j) = 1 := pow_gcd_eq_one.mpr ⟨hi', hj'⟩
    rw [hcop, pow_one] at h1
    calc a = a * (a⁻¹ * b) := by rw [h1, mul_one]
      _ = b := by group
  have himage : T.map π = E := by
    ext y
    constructor
    · rintro ⟨x, ⟨x', hx', rfl⟩, rfl⟩
      exact x'.2
    · intro hy
      have hyP : (⟨y, hy⟩ : E) ∈ (P.mapSurjective hf : Subgroup E) := by
        rw [hPtop]
        exact Subgroup.mem_top _
      obtain ⟨x, hx, hxy⟩ := hyP
      exact ⟨x, ⟨x, hx, rfl⟩, congrArg Subtype.val hxy⟩
  refine ⟨T, ?_, ?_, ?_⟩
  · intro a ha b hb
    refine hinj _ (T.mul_mem ha hb) _ (T.mul_mem hb ha) ?_
    rw [map_mul, map_mul]
    exact hEc _ (himage ▸ Subgroup.mem_map_of_mem π ha) _ (himage ▸ Subgroup.mem_map_of_mem π hb)
  · intro x hx
    refine hinj _ (T.pow_mem hx q) _ T.one_mem ?_
    rw [map_pow, map_one]
    exact hEq _ (himage ▸ Subgroup.mem_map_of_mem π hx)
  · rw [← himage, card_map_of_injOn π hinj]

end Aux

section Main

variable {X : Type*} [Group X] [Finite X]

theorem exponents_of_card_eq {q : ℕ} [hq : Fact q.Prime] {Q : Type*} [Group Q] [Finite Q]
    {V C₁ C₂ : Subgroup Q} (hVq : IsPGroup q V) (h₁ : C₁ ≤ V) (h₂ : C₂ ≤ V)
    (heq : Nat.card V * Nat.card C₁ ^ 2 = Nat.card C₂ ^ 3) :
    ∃ a j k : ℕ, Nat.card V = q ^ a ∧ Nat.card C₁ = q ^ j ∧ Nat.card C₂ = q ^ k ∧
      a + 2 * j = 3 * k := by
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hVq
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (hVq.to_le h₁)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hVq.to_le h₂)
  refine ⟨a, j, k, ha, hj, hk, ?_⟩
  rw [ha, hj, hk, ← pow_mul, ← pow_mul, ← pow_add] at heq
  have h := Nat.pow_right_injective hq.out.two_le heq
  omega

theorem le_pCore_two_of_fpf (hsolv : Group.IsSolvable X)
    (hrank : ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ E : Subgroup X, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      (∀ x ∈ E, x ^ q = 1) → Nat.card E ≤ q ^ 2)
    (σ : MulAut X) {U : Subgroup X} (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hU2 : ∀ u ∈ U, u ^ 2 = 1) (hU4 : Nat.card U = 4) (hσU : ∀ u ∈ U, σ u ∈ U)
    (hfpf : ∀ u ∈ U, σ u = u → u = 1) : U ≤ pCore 2 X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := pCore 2 X with hN
  have hN2 : IsPGroup 2 N := pCore_isPGroup
  have hσN : N.map σ.toMonoidHom = N := pCore_map_iso 2 σ
  by_contra hUN
  have hUN1 : U ⊓ N = ⊥ := by
    rcases eq_bot_or_eq_of_fpf hUc hU2 hU4 σ hσU hfpf (K := U ⊓ N) inf_le_left
      (fun k hk => ⟨hσU k hk.1, hσN ▸ Subgroup.mem_map_of_mem _ hk.2⟩) with h | h
    · exact h
    · exact absurd (h ▸ inf_le_right) hUN
  set π := QuotientGroup.mk' N with hπ
  set σ' : MulAut (X ⧸ N) := QuotientGroup.congr N N σ hσN with hσ'
  have hσ'π : ∀ x : X, σ' (π x) = π (σ x) := fun x => rfl
  have hinj : ∀ a ∈ U, ∀ b ∈ U, π a = π b → a = b := by
    intro a ha b hb h
    have h1 : a⁻¹ * b ∈ U ⊓ N := ⟨U.mul_mem (U.inv_mem ha) hb, QuotientGroup.eq.mp h⟩
    rw [hUN1, Subgroup.mem_bot] at h1
    calc a = a * (a⁻¹ * b) := by rw [h1, mul_one]
      _ = b := by group
  set U' := U.map π with hU'
  have hU'c : ∀ a ∈ U', ∀ b ∈ U', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hUc a ha b hb]
  have hU'2 : ∀ u ∈ U', u ^ 2 = 1 := by
    rintro _ ⟨u, hu, rfl⟩
    rw [← map_pow, hU2 u hu, map_one]
  have hU'4 : Nat.card U' = 4 := by rw [hU', card_map_of_injOn π hinj, hU4]
  have hσU' : ∀ u ∈ U', σ' u ∈ U' := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨σ u, hσU u hu, (hσ'π u).symm⟩
  have hfpf' : ∀ u ∈ U', σ' u = u → u = 1 := by
    rintro _ ⟨u, hu, rfl⟩ h
    rw [hσ'π] at h
    rw [hfpf u hu (hinj _ (hσU u hu) _ hu h), map_one]
  have hU'2g : IsPGroup 2 U' := fun x => ⟨1, Subtype.ext (by simpa using hU'2 x x.2)⟩
  have hU'1 : U' ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hU'4
    omega
  have : Group.IsSolvable (X ⧸ N) := inferInstance
  obtain ⟨q, hq, hq2, hqU⟩ := exists_pCore_not_le_centralizer (pCore_quot_pCore_eq_bot 2) hU'2g hU'1
  have : Fact q.Prime := ⟨hq⟩
  set R := pCore q (X ⧸ N) with hR
  have hRq : IsPGroup q R := pCore_isPGroup
  have hσ'R : ∀ x ∈ R, σ' x ∈ R := by
    intro x hx
    have hmap : R.map σ'.toMonoidHom = R := pCore_map_iso q σ'
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hx
  have hσ'C : ∀ k ∈ U' ⊓ Subgroup.centralizer (R : Set (X ⧸ N)),
      σ' k ∈ U' ⊓ Subgroup.centralizer (R : Set (X ⧸ N)) := by
    intro k hk
    refine ⟨hσU' k hk.1, ?_⟩
    show σ' k ∈ Subgroup.centralizer (R : Set (X ⧸ N))
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hr' : σ'.symm r ∈ R := by
      rw [← map_eq_of_forall_mem σ' hσ'R] at hr
      obtain ⟨y, hy, rfl⟩ := hr
      simpa using hy
    have := Subgroup.mem_centralizer_iff.mp hk.2 _ hr'
    have h2 := congrArg σ' this
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h2
  have hCR : U' ⊓ Subgroup.centralizer (R : Set (X ⧸ N)) = ⊥ := by
    rcases eq_bot_or_eq_of_fpf hU'c hU'2 hU'4 σ' hσU' hfpf' inf_le_left hσ'C with h | h
    · exact h
    · exact absurd (h ▸ inf_le_right) hqU
  have hRne : Nontrivial R := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro h
    apply hqU
    rw [h]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [(Subgroup.mem_bot).mp hy, one_mul, mul_one]
  obtain ⟨D₀, hD₀c, hD₀1, -, hD₀exp, hD₀fix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hq2 hRq
  have := hD₀c
  set D : Subgroup (X ⧸ N) := D₀.map R.subtype with hD
  have hDle : D ≤ R := Subgroup.map_subtype_le _
  have hDq : IsPGroup q D := hRq.to_le hDle
  have hDexp : ∀ x ∈ D, x ^ q = 1 := by
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_pow, hD₀exp d hd, map_one]
  have hσ'D : ∀ x ∈ D, σ' x ∈ D := mem_map_of_characteristic σ' hσ'R D₀
  have hD1 : D ≠ ⊥ := fun h =>
    hD₀1 ((Subgroup.map_eq_bot_iff_of_injective _ R.subtype_injective).mp h)
  have hCD : U' ⊓ Subgroup.centralizer (D : Set (X ⧸ N)) = ⊥ := by
    rw [eq_bot_iff]
    rintro u ⟨huU, huD⟩
    rw [← hCR]
    refine ⟨huU, ?_⟩
    set τ : MulAut R := MulAut.conjNormal u with hτ
    have hτfix : τ ∈ fixingSubgroup (MulAut R) (D₀ : Set R) := by
      rw [mem_fixingSubgroup_iff]
      intro d hd
      apply Subtype.ext
      have := Subgroup.mem_centralizer_iff.mp huD (d : X ⧸ N) ⟨d, hd, rfl⟩
      show ((MulAut.conjNormal u d : R) : X ⧸ N) = (d : X ⧸ N)
      rw [MulAut.conjNormal_apply, ← this, mul_inv_cancel_right]
    obtain ⟨k, hk⟩ := hD₀fix ⟨τ, hτfix⟩
    have hk' : τ ^ q ^ k = 1 := congrArg Subtype.val hk
    have h2 : τ ^ 2 = 1 := by rw [hτ, ← map_pow, hU'2 u huU, map_one]
    have hcop : Nat.Coprime (q ^ k) 2 :=
      Nat.Coprime.pow_left k ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)
    have h1 : τ ^ (q ^ k).gcd 2 = 1 := pow_gcd_eq_one.mpr ⟨hk', h2⟩
    rw [hcop, pow_one] at h1
    show u ∈ Subgroup.centralizer (R : Set (X ⧸ N))
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have := congrArg (fun φ : MulAut R => ((φ ⟨r, hr⟩ : R) : X ⧸ N)) h1
    simp only [hτ, MulAut.conjNormal_apply, MulAut.one_apply] at this
    calc r * u = u * r * u⁻¹ * u := by rw [this]
      _ = u * r := by group
  have hrankD : ∀ E : Subgroup (X ⧸ N), E ≤ D → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      Nat.card E ≤ q ^ 2 := by
    intro E hED hEc
    obtain ⟨T, hTc, hTq, hTcard⟩ :=
      exists_lift_of_quotient hN2 hq2 E hEc fun x hx => hDexp x (hED hx)
    rw [← hTcard]
    exact hrank q hq hq2 T hTc hTq
  obtain ⟨u, huU, hu1⟩ := (Subgroup.bot_or_exists_ne_one U').resolve_left hU'1
  have hDodd : Odd (Nat.card D) := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hDq
    rw [ha]
    exact Odd.pow (hq.odd_of_ne_two hq2)
  have hBWD := card_mul_sq_eq_cube hDodd hU'c hU'2 hU'4 σ' hσU' hfpf' hσ'D huU hu1
  obtain ⟨a, j, k, ha, hj, hk, hajk⟩ := exponents_of_card_eq hDq inf_le_left inf_le_left hBWD
  have hka : k < a := by
    by_contra hka
    have hle : Nat.card D ≤ Nat.card (D ⊓ Subgroup.centralizer ({u} : Set (X ⧸ N)) :
        Subgroup (X ⧸ N)) := by
      rw [ha, hk]
      exact Nat.pow_le_pow_right hq.pos (by omega)
    have heqD := Subgroup.eq_of_le_of_card_ge (inf_le_left : D ⊓ _ ≤ D) hle
    have hu : u ∈ U' ⊓ Subgroup.centralizer (D : Set (X ⧸ N)) := by
      refine ⟨huU, Subgroup.mem_centralizer_iff.mpr fun d hd => ?_⟩
      rw [← heqD] at hd
      exact (Subgroup.mem_centralizer_singleton_iff.mp hd.2)
    rw [hCD, Subgroup.mem_bot] at hu
    exact hu1 hu
  have hjk : j ≤ k := by
    have hle : D ⊓ Subgroup.centralizer (U' : Set (X ⧸ N)) ≤
        D ⊓ Subgroup.centralizer ({u} : Set (X ⧸ N)) :=
      inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr huU))
    have := Subgroup.card_le_of_le hle
    rw [hj, hk] at this
    exact (Nat.pow_le_pow_iff_right hq.one_lt).mp this
  have hDstruct : a ≤ 2 ∨ (a = 3 ∧ Nat.card (D ⊓ Subgroup.centralizer (D : Set (X ⧸ N)) :
      Subgroup (X ⧸ N)) = q) := by
    by_cases ha2 : a ≤ 2
    · exact Or.inl ha2
    right
    have hDexp' : ∀ x : D, x ^ q = 1 := fun x => Subtype.ext (by simpa using hDexp x x.2)
    have hDp : IsPGroup q D := hDq
    have hlt : q < Nat.card D := by
      rw [ha]
      calc q = q ^ 1 := (pow_one q).symm
        _ < q ^ a := Nat.pow_lt_pow_right hq.one_lt (by omega)
    have h2 := CFSG.RankThree.PartTwo.two_le_pRank hDp hDexp' hlt
    have hle2 : CFSG.pRank q D ≤ 2 := by
      refine CFSG.RankThree.PartTwo.pRank_le_of_forall_isMulCommutative hq fun E hE => ?_
      have := hrankD (E.map D.subtype) (Subgroup.map_subtype_le _) ?_
      · rwa [Subgroup.card_map_of_injective D.subtype_injective] at this
      · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        have := congrArg Subtype.val (hE.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
        simpa using congrArg Subtype.val this
    have hrk : CFSG.pRank q D = 2 := le_antisymm hle2 h2
    rcases (CFSG.RankThree.PartTwo.exponent_prime_rank_two_structure hDp hDexp' hrk).1 with
      ⟨-, h⟩ | ⟨h3, hZ, -⟩
    · rw [ha] at h
      have := Nat.pow_right_injective hq.two_le h
      omega
    · rw [ha] at h3
      refine ⟨Nat.pow_right_injective hq.two_le h3, ?_⟩
      rw [← hZ]
      refine Nat.card_congr
        { toFun := fun z => ⟨⟨z, z.2.1⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_⟩
          invFun := fun z => ⟨((z : D) : X ⧸ N), (z : D).2, ?_⟩
          left_inv := fun z => rfl
          right_inv := fun z => rfl }
      · exact (Subgroup.mem_centralizer_iff.mp z.2.2 g g.2)
      · show ((z : D) : X ⧸ N) ∈ Subgroup.centralizer (D : Set (X ⧸ N))
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨g, hg⟩)
  rcases hDstruct with ha2 | ⟨ha3, hZ⟩
  ·
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [pow_zero] at ha
      exact hD1 (Subgroup.card_eq_one.mp ha)
    omega
  ·
    have hj0 : j = 0 := by omega
    set Z : Subgroup (X ⧸ N) := D ⊓ Subgroup.centralizer (D : Set (X ⧸ N)) with hZdef
    have hZnorm : Z.Normal := by
      have : D.Normal := inferInstance
      exact Subgroup.normal_inf_normal D _
    have hZodd : Odd (Nat.card Z) := by rw [hZ]; exact hq.odd_of_ne_two hq2
    have hDmap := map_eq_of_forall_mem σ' hσ'D
    have hσ'Z : ∀ x ∈ Z, σ' x ∈ Z := by
      rintro x ⟨hxD, hxC⟩
      refine ⟨hσ'D x hxD, Subgroup.mem_centralizer_iff.mpr fun d hd => ?_⟩
      rw [← hDmap] at hd
      obtain ⟨e, he, rfl⟩ := hd
      have := Subgroup.mem_centralizer_iff.mp hxC e he
      change σ' e * σ' x = σ' x * σ' e
      rw [← map_mul, ← map_mul, this]
    have hBWZ := card_mul_sq_eq_cube hZodd hU'c hU'2 hU'4 σ' hσU' hfpf' hσ'Z huU hu1
    have hZq : IsPGroup q Z := hDq.to_le inf_le_left
    obtain ⟨a', j', k', ha', hj', hk', hajk'⟩ :=
      exponents_of_card_eq hZq inf_le_left inf_le_left hBWZ
    have ha'1 : a' = 1 := by
      rw [hZ] at ha'
      exact (Nat.pow_right_injective hq.two_le (ha'.symm.trans (pow_one q).symm))
    have hj'0 : j' = 0 := by
      have hle : Z ⊓ Subgroup.centralizer (U' : Set (X ⧸ N)) ≤
          D ⊓ Subgroup.centralizer (U' : Set (X ⧸ N)) := inf_le_inf_right _ inf_le_left
      have := Subgroup.card_le_of_le hle
      rw [hj', hj, hj0, pow_zero] at this
      by_contra hne
      have : 1 < q ^ j' := Nat.one_lt_pow hne hq.one_lt
      omega
    omega

end Main

end CFSG.RankThree.PartTwo.Sec17.HeadProof
