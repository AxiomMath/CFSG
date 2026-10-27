module

public import CFSG.Quasithin.H13.LocDblCComp
public import CFSG.Quasithin.Background.A3Structure312Embed
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public section

namespace CFSG.Quasithin.H13.LocDbl

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem eq_bot_or_eq_of_subnormal {K B : Subgroup X} (hK : IsSimpleGroup ↥K)
    (hB : IsSubnormal B K) : B = ⊥ ∨ B = K := by
  by_cases hBK : B = K
  · exact Or.inr hBK
  · left
    obtain ⟨P, hPK, hPn, hBP⟩ :=
      A3.subnormal_exists_normal_of_lt hB (lt_of_le_of_ne (A3.subnormal_le hB) hBK)
    rcases hK.eq_bot_or_eq_top_of_normal (P.subgroupOf K) with h | h
    · rw [eq_bot_iff]
      intro x hx
      have hxK : x ∈ K := hPK.le (hBP hx)
      have : (⟨x, hxK⟩ : ↥K) ∈ P.subgroupOf K := hBP hx
      rw [h, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val this
    · exfalso
      refine hPK.ne (le_antisymm hPK.le fun x hx => ?_)
      have : (⟨x, hx⟩ : ↥K) ∈ P.subgroupOf K := by rw [h]; trivial
      exact this

omit [Finite X] in
theorem eq_bot_or_eq_of_le_normalizer {K B : Subgroup X} (hK : IsSimpleGroup ↥K) (hBK : B ≤ K)
    (hn : K ≤ Subgroup.normalizer (B : Set X)) : B = ⊥ ∨ B = K :=
  eq_bot_or_eq_of_subnormal hK
    (A3.subnormal_of_normal hBK ((Subgroup.normal_subgroupOf_iff_le_normalizer hBK).mpr hn))

omit [Finite X] in
theorem conj_mem_normalizer_map {H : Subgroup X} {g r : X}
    (hr : r ∈ Subgroup.normalizer (H : Set X)) :
    g * r * g⁻¹ ∈
      Subgroup.normalizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup X) : Set X) := by
  rw [← map_conj_eq_iff] at hr ⊢
  calc (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj (g * r * g⁻¹)).toMonoidHom
      = (H.map (MulAut.conj r).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
        rw [Subgroup.map_map, Subgroup.map_map]
        congr 1
        ext x
        simp [mul_assoc]
    _ = H.map (MulAut.conj g).toMonoidHom := by rw [hr]

theorem normalizer_le_of_no_conj_double {T K B : Subgroup X} (hK : IsSimpleGroup ↥K)
    (hBK : B ≤ K) (hB : B ∈ cComp (B ⊔ T))
    (hno : ∀ Y : Subgroup X, T ⊓ K ≤ Y → Y ≤ K → Y ≠ K → ∀ g : X,
      B ∈ cComp Y → B.map (MulAut.conj g).toMonoidHom ∈ cComp Y →
        B.map (MulAut.conj g).toMonoidHom = B) :
    T ⊓ Subgroup.normalizer (K : Set X) ≤ Subgroup.normalizer (B : Set X) := by
  intro u hu
  by_cases hBeq : B = K
  · rw [hBeq]
    exact hu.2
  have hBne : B ≠ ⊥ := ne_bot_of_mem_cComp hB
  set R : Subgroup X := T ⊓ K with hR
  have hRT : R ≤ T := inf_le_left
  have hRK : R ≤ K := inf_le_right
  set Y₀ : Subgroup X := B ⊔ R with hY₀
  have hY₀le : Y₀ ≤ B ⊔ T := sup_le le_sup_left (hRT.trans le_sup_right)
  have hBY₀ : B ∈ cComp Y₀ := cComp_mem_of_le hB le_sup_left hY₀le
  have hY₀K : Y₀ ≤ K := sup_le hBK hRK
  have hY₀ne : Y₀ ≠ K := by
    intro h
    have hsub : IsSubnormal B K := h ▸ subnormal_of_mem_cComp hBY₀
    rcases eq_bot_or_eq_of_subnormal hK hsub with h1 | h1
    · exact hBne h1
    · exact hBeq h1
  have hRN : R ≤ Subgroup.normalizer (B : Set X) := by
    intro r hr
    have hrY : r ∈ Subgroup.normalizer (Y₀ : Set X) :=
      Subgroup.le_normalizer (Subgroup.mem_sup_right hr)
    exact map_conj_eq_iff.mp
      (hno Y₀ le_sup_right hY₀K hY₀ne r hBY₀ (map_conj_mem_cComp hBY₀ hrY))
  have huT : u ∈ Subgroup.normalizer ((B ⊔ T : Subgroup X) : Set X) :=
    Subgroup.le_normalizer (Subgroup.mem_sup_right hu.1)
  set C : Subgroup X := B.map (MulAut.conj u).toMonoidHom with hC
  have hCc : C ∈ cComp (B ⊔ T) := map_conj_mem_cComp hB huT
  have hCK : C ≤ K := by
    rw [hC, ← map_conj_eq_iff.mpr hu.2]
    exact Subgroup.map_mono hBK
  have hCB : C ≤ Subgroup.normalizer (B : Set X) := le_normalizer_of_mem_cComp hB hCc
  have hRC : R ≤ Subgroup.normalizer (C : Set X) := by
    have huR : R.map (MulAut.conj u).toMonoidHom = R := by
      have hT : T.map (MulAut.conj u).toMonoidHom = T :=
        map_conj_eq_iff.mpr (Subgroup.le_normalizer hu.1)
      have hK' : K.map (MulAut.conj u).toMonoidHom = K := map_conj_eq_iff.mpr hu.2
      rw [hR, Subgroup.map_inf T K (MulAut.conj u).toMonoidHom (MulAut.conj u).injective, hT,
        hK']
    intro r hr
    rw [← huR] at hr
    obtain ⟨r', hr', rfl⟩ := hr
    exact conj_mem_normalizer_map (hRN hr')
  set Y₁ : Subgroup X := B ⊔ C ⊔ R with hY₁
  have hY₁le : Y₁ ≤ B ⊔ T :=
    sup_le (sup_le le_sup_left (le_of_mem_cComp hCc)) (hRT.trans le_sup_right)
  have hY₁K : Y₁ ≤ K := sup_le (sup_le hBK hCK) hRK
  have hY₁N : Y₁ ≤ Subgroup.normalizer (B : Set X) :=
    sup_le (sup_le Subgroup.le_normalizer hCB) hRN
  have hY₁ne : Y₁ ≠ K := by
    intro h
    rcases eq_bot_or_eq_of_le_normalizer hK hBK (h ▸ hY₁N) with h1 | h1
    · exact hBne h1
    · exact hBeq h1
  have hBY₁ : B ∈ cComp Y₁ := cComp_mem_of_le hB (le_sup_left.trans le_sup_left) hY₁le
  have hCY₁ : C ∈ cComp Y₁ := cComp_mem_of_le hCc (le_sup_right.trans le_sup_left) hY₁le
  have hRY₁ : R ≤ Y₁ := le_sup_right
  exact map_conj_eq_iff.mp (hno Y₁ hRY₁ hY₁K hY₁ne u hBY₁ hCY₁)

theorem simple_Sylow_overgroup_Ccomponent_uniqueness_normalizer {p : ℕ} [Fact p.Prime]
    (T : Sylow p X) {K : Subgroup X} (hK : IsSimpleGroup ↥K) (_hKn : ∃ a b : ↥K, a * b ≠ b * a)
    (_hKsub : K.IsSubnormal)
    (huniq : ∀ Y : Subgroup X, (T : Subgroup X) ⊓ K ≤ Y → Y < K → (cComp Y).Subsingleton)
    {B : Subgroup X} (hBK : B ≤ K) (hB : B ∈ cComp (B ⊔ (T : Subgroup X))) :
    (T : Subgroup X) ⊓ Subgroup.normalizer (K : Set X) ≤
      (T : Subgroup X) ⊓ Subgroup.normalizer (B : Set X) := fun _ hu =>
  ⟨hu.1, normalizer_le_of_no_conj_double hK hBK hB
    (fun Y hRY hYK hYne _ hB hBg => huniq Y hRY (lt_of_le_of_ne hYK hYne) hBg hB) hu⟩

theorem finite_sq_primes {n : ℕ} (hn : n ≠ 0) : {r : ℕ | r.Prime ∧ r ^ 2 ∣ n}.Finite := by
  refine (Set.finite_Iic n).subset fun r hr => ?_
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hr.2
  exact (Nat.le_self_pow (by norm_num) r).trans hle

theorem three_le_card_primeFactors_radQuot {Y B : Subgroup X} (hB : B ∈ cComp Y) :
    3 ≤ (Nat.card (↥B ⧸ CFSG.solvableRadical ↥B)).primeFactors.card := by
  obtain ⟨hsimple, -⟩ := radQuot_simple hB
  have := hsimple
  have hBp : Group.IsPerfect ↥B := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hB)
  have hperf : Group.IsPerfect (↥B ⧸ CFSG.solvableRadical ↥B) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  by_contra h
  push Not at h
  exact Group.IsPerfect.not_isSolvable _
    (CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
      (G := ↥B ⧸ CFSG.solvableRadical ↥B) (by omega))

theorem double_Ccomponent_three_squared_prime_divisors {H K B : Subgroup X} (hB : B ∈ cComp H)
    (hBK : B ≤ K) :
    (∀ s ∈ H ⊓ Subgroup.normalizer (K : Set X), CFSG.conjugate B s ≠ B →
      3 ≤ {r : ℕ | r.Prime ∧ r ^ 2 ∣ Nat.card K}.ncard) ∧
    ({r : ℕ | r.Prime ∧ r ^ 2 ∣ Nat.card K}.ncard ≤ 2 →
      H ⊓ Subgroup.normalizer (K : Set X) ≤ H ⊓ Subgroup.normalizer (B : Set X)) := by
  have key : ∀ s ∈ H ⊓ Subgroup.normalizer (K : Set X), CFSG.conjugate B s ≠ B →
      3 ≤ {r : ℕ | r.Prime ∧ r ^ 2 ∣ Nat.card K}.ncard := by
    intro s hs hne
    have hdvd := (Ccomponent_full_radical_product_divisor hB hBK).1 s hs hne
    have hsq : Nat.card (↥B ⧸ CFSG.solvableRadical ↥B) ^ 2 ∣ Nat.card K :=
      (pow_two (Nat.card (↥B ⧸ CFSG.solvableRadical ↥B)) ▸
        mul_dvd_mul_right (card_radQuot_dvd B) _).trans hdvd
    have h3 := three_le_card_primeFactors_radQuot hB
    have hsub : ((Nat.card (↥B ⧸ CFSG.solvableRadical ↥B)).primeFactors : Set ℕ) ⊆
        {r : ℕ | r.Prime ∧ r ^ 2 ∣ Nat.card K} := by
      intro r hr
      rw [Finset.mem_coe, Nat.mem_primeFactors] at hr
      exact ⟨hr.1, (pow_dvd_pow_of_dvd hr.2.1 2).trans hsq⟩
    calc 3 ≤ (Nat.card (↥B ⧸ CFSG.solvableRadical ↥B)).primeFactors.card := h3
      _ = ((Nat.card (↥B ⧸ CFSG.solvableRadical ↥B)).primeFactors : Set ℕ).ncard :=
          (Set.ncard_coe_finset _).symm
      _ ≤ _ := Set.ncard_le_ncard hsub (finite_sq_primes Nat.card_pos.ne')
  refine ⟨key, fun h2 s hs => ⟨hs.1, ?_⟩⟩
  by_contra hsB
  have hne : CFSG.conjugate B s ≠ B := by
    intro h
    apply hsB
    have : s⁻¹ ∈ Subgroup.normalizer (B : Set X) := map_conj_eq_iff.mp h
    simpa using Subgroup.inv_mem _ this
  have := key s hs hne
  omega

theorem three_le_sq_primes_of_conj {Y B : Subgroup X} (hB : B ∈ cComp Y) {g : X}
    (hBg : B.map (MulAut.conj g).toMonoidHom ∈ cComp Y)
    (hne : B.map (MulAut.conj g).toMonoidHom ≠ B) :
    3 ≤ {r : ℕ | r.Prime ∧ r ^ 2 ∣ Nat.card Y}.ncard := by
  set C : Subgroup X := B.map (MulAut.conj g).toMonoidHom with hC
  let e : ↥B ≃* ↥C := B.equivMapOfInjective _ (MulAut.conj g).injective
  have hdvd := card_dvd_of_mem_cComp hB hBg (Ne.symm hne)
    (sup_le (le_of_mem_cComp hB) (le_of_mem_cComp hBg))
  rw [← card_radQuot_congr e] at hdvd
  have hsq : Nat.card (↥B ⧸ CFSG.solvableRadical ↥B) ^ 2 ∣ Nat.card Y :=
    (pow_two (Nat.card (↥B ⧸ CFSG.solvableRadical ↥B)) ▸
      mul_dvd_mul_right (card_radQuot_dvd B) _).trans hdvd
  have h3 := three_le_card_primeFactors_radQuot hB
  have hsub : ((Nat.card (↥B ⧸ CFSG.solvableRadical ↥B)).primeFactors : Set ℕ) ⊆
      {r : ℕ | r.Prime ∧ r ^ 2 ∣ Nat.card Y} := by
    intro r hr
    rw [Finset.mem_coe, Nat.mem_primeFactors] at hr
    exact ⟨hr.1, (pow_dvd_pow_of_dvd hr.2.1 2).trans hsq⟩
  calc 3 ≤ (Nat.card (↥B ⧸ CFSG.solvableRadical ↥B)).primeFactors.card := h3
    _ = ((Nat.card (↥B ⧸ CFSG.solvableRadical ↥B)).primeFactors : Set ℕ).ncard :=
        (Set.ncard_coe_finset _).symm
    _ ≤ _ := Set.ncard_le_ncard hsub (finite_sq_primes Nat.card_pos.ne')

theorem simple_Sylow_overgroup_square_prime_normalizer {p : ℕ} [Fact p.Prime] (T : Sylow p X)
    {K : Subgroup X} (hK : IsSimpleGroup ↥K) (_hKsub : K.IsSubnormal)
    (hsq : ∀ Y : Subgroup X, (T : Subgroup X) ⊓ K ≤ Y → Y < K →
      {r : ℕ | r.Prime ∧ r ^ 2 ∣ Nat.card Y}.ncard ≤ 2)
    {B : Subgroup X} (hBK : B ≤ K) (hB : B ∈ cComp (B ⊔ (T : Subgroup X))) :
    (T : Subgroup X) ⊓ Subgroup.normalizer (K : Set X) ≤
      (T : Subgroup X) ⊓ Subgroup.normalizer (B : Set X) := fun u hu =>
  ⟨hu.1, normalizer_le_of_no_conj_double hK hBK hB (fun Y hRY hYK hYne g hBY hBg => by
    by_contra hne
    have h3 := three_le_sq_primes_of_conj hBY hBg hne
    have h2 := hsq Y hRY (lt_of_le_of_ne hYK hYne)
    omega) hu⟩

@[expose] def NoIsoDouble {A : Type*} [Group A] (Y : Subgroup A) : Prop :=
  ∀ U ∈ cComp Y, ∀ V ∈ cComp Y, Nonempty (↥U ≃* ↥V) → U = V

@[expose] def SylowNoDouble (A : Type*) [Group A] : Prop :=
  ∀ R : Subgroup A, IsSylowTwoOf R ⊤ → ∀ Y : Subgroup A, R ≤ Y → Y ≠ ⊤ → NoIsoDouble Y

theorem noIsoDouble_of_subsingleton' {A : Type*} [Group A] {Y : Subgroup A}
    (h : (cComp Y).Subsingleton) : NoIsoDouble Y := fun _ hU _ hV _ => h hU hV

theorem NoIsoDouble.map {A A' : Type*} [Group A] [Group A'] [Finite A] (e : A ≃* A')
    {Y : Subgroup A} (h : NoIsoDouble Y) : NoIsoDouble (Y.map e.toMonoidHom) := by
  have : Finite A' := Finite.of_equiv A e.toEquiv
  intro U hU V hV ⟨φ⟩
  have hU' := cComp_map_mulEquiv e.symm hU
  have hV' := cComp_map_mulEquiv e.symm hV
  have hY : (Y.map e.toMonoidHom).map e.symm.toMonoidHom = Y := by
    rw [Subgroup.map_map]
    simp
  rw [hY] at hU' hV'
  have hUe : (U.map e.symm.toMonoidHom).map e.toMonoidHom = U := by
    rw [Subgroup.map_map]
    simp
  have hVe : (V.map e.symm.toMonoidHom).map e.toMonoidHom = V := by
    rw [Subgroup.map_map]
    simp
  let eU : ↥(U.map e.symm.toMonoidHom) ≃* ↥U :=
    (U.equivMapOfInjective _ e.symm.injective).symm
  let eV : ↥(V.map e.symm.toMonoidHom) ≃* ↥V :=
    (V.equivMapOfInjective _ e.symm.injective).symm
  have h1 := h _ hU' _ hV' ⟨(eU.trans φ).trans eV.symm⟩
  rw [← hUe, ← hVe, h1]

theorem SylowNoDouble.of_mulEquiv {A A' : Type*} [Group A] [Group A'] [Finite A] (e : A ≃* A')
    (h : SylowNoDouble A) : SylowNoDouble A' := by
  have : Finite A' := Finite.of_equiv A e.toEquiv
  intro R hR Y hRY hY
  have hR' : IsSylowTwoOf (R.map e.symm.toMonoidHom) ⊤ :=
    A312.isSylowTwoOf_top_map e.symm.toMonoidHom e.symm.surjective hR
  have hYne : Y.map e.symm.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hY
    have := congrArg (Subgroup.map e.toMonoidHom) htop
    rw [Subgroup.map_map, Subgroup.map_top_of_surjective _ e.surjective] at this
    simpa using this
  have hnd := h _ hR' _ (Subgroup.map_mono hRY) hYne
  have := NoIsoDouble.map e hnd
  rwa [Subgroup.map_map, show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id A' by
    ext; simp, Subgroup.map_id] at this

omit [Finite X] in
theorem isSylowTwoOf_subgroupOf_top {S H : Subgroup X} (hS : IsSylowTwoOf S H) :
    IsSylowTwoOf (S.subgroupOf H) ⊤ := by
  refine ⟨le_top, hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm, ?_⟩
  rw [show ((S.subgroupOf H).subgroupOf ⊤).index = (S.subgroupOf H).index from
    Subgroup.relIndex_top_right _]
  exact hS.2.2

theorem normalizer_le_of_sylowNoDouble {Γ : Type} [Group Γ] [Finite Γ] {T K B : Subgroup Γ}
    (hT : IsSylowTwoOf T ⊤) (hK : IsSimpleGroup ↥K) (hKsub : IsSubnormal K ⊤)
    (hND : SylowNoDouble ↥K) (hBK : B ≤ K) (hB : B ∈ cComp (B ⊔ T)) :
    T ⊓ Subgroup.normalizer (K : Set Γ) ≤ Subgroup.normalizer (B : Set Γ) := by
  have hTK' : IsSylowTwoOf ((T ⊓ K).subgroupOf K) ⊤ :=
    isSylowTwoOf_subgroupOf_top (A312.isSylowTwoOf_inf_of_subnormal hKsub hT)
  refine normalizer_le_of_no_conj_double hK hBK hB fun Y hRY hYK hYne g hBY hBg => ?_
  have hYne' : Y.subgroupOf K ≠ ⊤ := by
    intro h
    apply hYne
    refine le_antisymm hYK fun x hx => ?_
    have : (⟨x, hx⟩ : ↥K) ∈ Y.subgroupOf K := by rw [h]; trivial
    exact this
  have hnd := hND _ hTK' (Y.subgroupOf K) (Subgroup.comap_mono hRY) hYne'
  set C : Subgroup Γ := B.map (MulAut.conj g).toMonoidHom with hC
  have hCK : C ≤ K := (le_of_mem_cComp hBg).trans hYK
  have hU := A312.mem_cComp_subgroupOf hYK hBY
  have hV := A312.mem_cComp_subgroupOf hYK hBg
  let e : ↥(B.subgroupOf K) ≃* ↥(C.subgroupOf K) :=
    ((Subgroup.subgroupOfEquivOfLe hBK).trans
      (B.equivMapOfInjective _ (MulAut.conj g).injective)).trans
      (Subgroup.subgroupOfEquivOfLe hCK).symm
  have h := hnd _ hU _ hV ⟨e⟩
  have h' := congrArg (Subgroup.map K.subtype) h
  rw [Subgroup.map_subgroupOf_eq_of_le hBK, Subgroup.map_subgroupOf_eq_of_le hCK] at h'
  exact h'.symm

end CFSG.Quasithin.H13.LocDbl
