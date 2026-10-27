module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bOuter

public section

namespace CFSG.Quasithin.F112Crit.APrime

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X5 CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag

private theorem mem_of_normalizerAct_inner_of_mem {V : Type} [CommGroup V]
    {L X : Subgroup (MulAut V)} [Group.IsPerfect L]
    (hLX : L ≤ X) (hXL : X ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hC : X ⊓ Subgroup.centralizer (L : Set (MulAut V)) ≤ L)
    {a : MulAut V} (haX : a ∈ X) (haN : a ∈ Subgroup.normalizer (L : Set (MulAut V)))
    (hinner : normalizerAct L ⟨a, haN⟩ ∈
      (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range) :
    a ∈ L := by
  obtain ⟨y, hy⟩ := hinner
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
  have h1 : normalizerAct L ⟨a, haN⟩ =
      normalizerAct L ⟨(l : MulAut V), Subgroup.le_normalizer l.2⟩ := by
    rw [← hy, normalizerAct_of_mem L l.2]
  have h2 : normalizerAct L (⟨a, haN⟩ * ⟨(l : MulAut V), Subgroup.le_normalizer l.2⟩⁻¹) = 1 := by
    rw [map_mul, map_inv, h1, mul_inv_cancel]
  have hc := mem_centralizer_of_normalizerAct_eq_one L h2
  have hc' : a * (l : MulAut V)⁻¹ ∈ Subgroup.centralizer (L : Set (MulAut V)) := by
    simpa using hc
  have hmem : a * (l : MulAut V)⁻¹ ∈
      X ⊓ Subgroup.centralizer (L : Set (MulAut V)) :=
    ⟨X.mul_mem haX (hLX (L.inv_mem l.2)), hc'⟩
  have hal : a = (a * (l : MulAut V)⁻¹) * (l : MulAut V) := by group
  rw [hal]
  exact L.mul_mem (hC hmem) l.2

theorem two_mul_card_lt_index_fixV_psu3
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1)
    {X L : Subgroup (MulAut V)} (hLX : L ≤ X)
    (hXL : X ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hperf : Group.IsPerfect ↥L) (hZ : Odd (Nat.card (Subgroup.center ↥L)))
    (hC : X ⊓ Subgroup.centralizer (L : Set (MulAut V)) ≤ L)
    {f : ℕ} (hf : 2 ≤ f) {F : Type} [Field F] [Finite F] (hF : Nat.card F = (2 ^ f) ^ 2)
    (α : ↥L ⧸ Subgroup.center ↥L ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ f) F))
    {A : Subgroup (MulAut V)} (hAX : A ≤ X) (hA : A ≠ ⊥) (hAe : IsElemAbelian2 A) :
    2 * Nat.card A < (fixV A).index := by
  haveI : Group.IsPerfect ↥L := hperf
  haveI : Finite (MulAut V) :=
    Finite.of_injective (fun σ : MulAut V => (σ : V → V)) DFunLike.coe_injective
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : UnitaryFieldData 2 f F :=
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
  haveI : CharP F 2 := hU.charP
  let α' : ↥L ⧸ Subgroup.center ↥L ≃* unitaryPSU hU 3 :=
    α.trans (unitaryPSUEquiv hU (by norm_num)).symm
  obtain ⟨φ, hφs, hφk, hφZ, -⟩ := exists_cover_map hf hU hZ α'
  have hZdvd : Nat.card (Subgroup.center ↥L) ∣ Nat.gcd 3 (2 ^ f + 1) := by
    rw [← card_unitaryScalars hU (by norm_num : 1 ≤ 3), ← hφZ]
    exact Subgroup.card_map_dvd _ _
  have hZ3 : ∀ z ∈ Subgroup.center ↥L, z ^ 3 = 1 := by
    intro z hz
    have h3 : Nat.card (Subgroup.center ↥L) ∣ 3 := hZdvd.trans (Nat.gcd_dvd_left _ _)
    obtain ⟨k, hk⟩ := h3
    have h1 : (⟨z, hz⟩ : Subgroup.center ↥L) ^ Nat.card (Subgroup.center ↥L) = 1 :=
      pow_card_eq_one'
    have h2 := congrArg (fun w : Subgroup.center ↥L => (w : ↥L)) h1
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2
    rw [hk, pow_mul, h2, one_pow]
  obtain ⟨ℓ, hℓ, hℓ2, hord, -, -, hnot3⟩ :=
    binary_multiple_six_exponents_have_primitive_prime_divisors hf
  have hℓ3 : ℓ ≠ 3 := fun h0 => hnot3 (by rw [h0]; exact dvd_mul_right 3 _)
  have hinv : ∀ {t : MulAut V}, t ∈ L → t * t = 1 → t ≠ 1 →
      2 ^ (2 * f) ≤ (fixV (Subgroup.zpowers t)).index :=
    fun {t} ht ht2 ht1 =>
      two_pow_le_index_involution hf hU threeInvolutionProduct_holds hℓ hℓ2 hℓ3 hord hV L
        hφs hφk ht ht2 ht1
  have houter := fun {a : MulAut V} (ha : a ∈ Subgroup.normalizer (L : Set (MulAut V)))
      (ha2 : a * a = 1) (hout : normalizerAct L ⟨a, ha⟩ ∉
        (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range) =>
    two_pow_le_index_outer hf hU outerInverter_holds hℓ hℓ2 hℓ3 hord hV L α' hZ3 ha ha2 hout
  have hAN : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := hAX.trans hXL
  have hAsq : ∀ a ∈ A, a * a = 1 := fun a ha => by simpa [sq] using hAe.2 a ha
  obtain ⟨Ψ, hΨ⟩ := exists_fieldFactor_hom hf hU
  let τ : Subgroup.normalizer (L : Set (MulAut V)) →* MulAut (unitaryPSU hU 3) :=
    (MulAut.congr α').toMonoidHom.comp (normalizerAct L)
  let ψ : A →* (F ≃+* F) := (Ψ.comp τ).comp (Subgroup.inclusion hAN)
  have hψ : ∀ a : A, ψ a = Ψ (τ ⟨(a : MulAut V), hAN a.2⟩) := fun a => rfl
  have hinner_iff : ∀ (a : MulAut V) (ha : a ∈ Subgroup.normalizer (L : Set (MulAut V))),
      τ ⟨a, ha⟩ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (unitaryPSU hU 3) →
        normalizerAct L ⟨a, ha⟩ ∈
          (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range := by
    rintro a ha ⟨x, hx⟩
    refine ⟨α'.symm x, ?_⟩
    have h1 : MulAut.congr α'.symm (MulAut.conj x) = MulAut.conj (α'.symm x) :=
      CFSG.ComponentClassification.OuterAutomorphisms.congr_conj α'.symm x
    have h2 : MulAut.congr α'.symm (τ ⟨a, ha⟩) = normalizerAct L ⟨a, ha⟩ := by
      ext y
      simp [τ, MulAut.congr_apply]
    show MulAut.conj (α'.symm x) = normalizerAct L ⟨a, ha⟩
    rw [← h1, ← h2]
    exact congrArg (MulAut.congr α'.symm) hx
  have hker : ∀ a : A, ψ a = 1 → (a : MulAut V) ∈ L := by
    intro a ha
    have haN : (a : MulAut V) ∈ Subgroup.normalizer (L : Set (MulAut V)) := hAN a.2
    have hββ : τ ⟨(a : MulAut V), haN⟩ * τ ⟨(a : MulAut V), haN⟩ = 1 := by
      rw [← map_mul]
      have h1 : (⟨(a : MulAut V), haN⟩ * ⟨(a : MulAut V), haN⟩ :
          Subgroup.normalizer (L : Set (MulAut V))) = 1 := Subtype.ext (hAsq a a.2)
      rw [h1, map_one]
    have hβ := hΨ _ (by rw [← hψ]; exact ha) hββ
    exact mem_of_normalizerAct_inner_of_mem hLX hXL hC (hAX a.2) haN (hinner_iff _ haN hβ)
  have hrange : Nat.card ψ.range ≤ 2 := by
    refine card_le_two_of_sq_eq_one (p := 2) ψ.range ?_
    rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have h1 : a ^ 2 = 1 := Subtype.ext (hAe.2 a a.2)
    rw [h1, map_one]
  have hc : Nat.card A ≤ 2 * Nat.card ψ.ker := card_le_two_mul_ker ψ hrange
  have hd : Nat.card ψ.ker ≤ Nat.card ↥(A ⊓ L) := by
    refine Nat.card_le_card_of_injective (fun a : ψ.ker =>
      (⟨((a : A) : MulAut V), ⟨(a : A).2, hker a a.2⟩⟩ : ↥(A ⊓ L))) ?_
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    have h1 := congrArg Subtype.val hab
    simpa using h1
  have he : Nat.card ↥(A ⊓ L) ≤ 2 ^ f := by
    set E : Subgroup ↥L := (A ⊓ L).subgroupOf L with hE
    have hEe : IsElemAbelianTwo E := by
      refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
      · exact Subtype.ext (hAe.1 _ ((Subgroup.mem_subgroupOf.mp hx).1) _
          ((Subgroup.mem_subgroupOf.mp hy).1))
      · exact Subtype.ext (hAe.2 _ ((Subgroup.mem_subgroupOf.mp hx).1))
    have hcardE : Nat.card E = Nat.card ↥(A ⊓ L) := by
      rw [← Subgroup.card_map_of_injective (f := L.subtype) L.subtype_injective,
        hE, Subgroup.map_subgroupOf_eq_of_le inf_le_right]
    rw [← hcardE]
    exact matrix_quotient_card_elemAbelian_le hU hφs hφk E hEe
  have hAbound : Nat.card A ≤ 2 * 2 ^ f :=
    hc.trans (Nat.mul_le_mul_left _ (hd.trans he))
  by_cases hAL : A ≤ L
  · have hAle : Nat.card ↥(A ⊓ L) = Nat.card A := by rw [inf_eq_left.mpr hAL]
    have hAcard : Nat.card A ≤ 2 ^ f := by rw [← hAle]; exact he
    obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA
    have ht1 : (a : MulAut V) ≠ 1 := fun h0 => ha1 (Subtype.ext h0)
    have h1 := hinv (hAL a.2) (hAsq a a.2) ht1
    have h2 : (fixV (Subgroup.zpowers (a : MulAut V))).index ≤ (fixV A).index :=
      index_fixV_antitone (Subgroup.zpowers_le.mpr a.2)
    have hlt : 2 * 2 ^ f < 2 ^ (2 * f) := by
      calc 2 * 2 ^ f = 2 ^ (f + 1) := by rw [pow_succ']
        _ < 2 ^ (2 * f) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    calc 2 * Nat.card A ≤ 2 * 2 ^ f := Nat.mul_le_mul_left 2 hAcard
      _ < 2 ^ (2 * f) := hlt
      _ ≤ (fixV (Subgroup.zpowers (a : MulAut V))).index := h1
      _ ≤ (fixV A).index := h2
  · rcases SetLike.not_le_iff_exists.mp hAL with ⟨a, haA, haL⟩
    have houta : normalizerAct L ⟨a, hAN haA⟩ ∉
        (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range :=
      fun hin => haL (mem_of_normalizerAct_inner_of_mem hLX hXL hC (hAX haA) (hAN haA) hin)
    have h1 := houter (hAN haA) (hAsq a haA) houta
    have h2 : (fixV (Subgroup.zpowers a)).index ≤ (fixV A).index :=
      index_fixV_antitone (Subgroup.zpowers_le.mpr haA)
    have hlt : 4 * 2 ^ f < 2 ^ (3 * f) := by
      calc 4 * 2 ^ f = 2 ^ (f + 2) := by
            rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, add_comm 2 f]
        _ < 2 ^ (3 * f) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    calc 2 * Nat.card A ≤ 2 * (2 * 2 ^ f) := Nat.mul_le_mul_left 2 hAbound
      _ = 4 * 2 ^ f := by ring
      _ < 2 ^ (3 * f) := hlt
      _ ≤ (fixV (Subgroup.zpowers a)).index := h1
      _ ≤ (fixV A).index := h2

end CFSG.Quasithin.F112Crit.APrime

end
