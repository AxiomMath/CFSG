module

public import CFSG.Quasithin.Background.SmithB42D4Lang
public import CFSG.Quasithin.Background.SmithB42D4Rank
public import CFSG.Quasithin.Background.SmithB42Disp
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.EvenTrialityCanonicalFieldCentralizer
public import CFSG.RankThree.Chevalley.SteinbergCBTrialityTransposition
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBruhat
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQuad
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof

public section

namespace CFSG.Quasithin.B42D4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin.B42Disp

theorem ppd_twelve {ℓ m : ℕ} (hℓ : ℓ.Prime) (hm : 1 ≤ m) (h : orderOf (2 : ZMod ℓ) = 12 * m) :
    3 < ℓ ∧ ℓ ∣ (2 ^ m) ^ 4 - (2 ^ m) ^ 2 + 1 := by
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    have h0 : (2 : ZMod 2) = 0 := rfl
    rw [h0, orderOf_eq_zero_iff'.2 (fun n hn => by rw [zero_pow (by omega)]; exact zero_ne_one)]
      at h
    omega
  have hℓ3 : ℓ ≠ 3 := by
    rintro rfl
    have h2 : orderOf (2 : ZMod 3) ∣ 2 := orderOf_dvd_of_pow_eq_one (by decide)
    rw [h] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have : Fact ℓ.Prime := ⟨hℓ⟩
  refine ⟨by have := hℓ.two_le; omega, ?_⟩
  set x : ZMod ℓ := 2 ^ m with hx
  have h12 : x ^ 12 = 1 := by rw [hx, ← pow_mul, mul_comm, ← h, pow_orderOf_eq_one]
  have h6 : x ^ 6 ≠ 1 := fun h1 => by
    have : 12 * m ∣ 6 * m := h ▸ orderOf_dvd_of_pow_eq_one (by rw [mul_comm, pow_mul, ← hx, h1])
    have := Nat.le_of_dvd (by omega) this
    omega
  have h4 : x ^ 4 ≠ 1 := fun h1 => by
    have : 12 * m ∣ 4 * m := h ▸ orderOf_dvd_of_pow_eq_one (by rw [mul_comm, pow_mul, ← hx, h1])
    have := Nat.le_of_dvd (by omega) this
    omega
  have e1 : (x ^ 6 - 1) * (x ^ 6 + 1) = 0 := by
    rw [show (x ^ 6 - 1) * (x ^ 6 + 1) = x ^ 12 - 1 by ring, h12, sub_self]
  have e2 : x ^ 6 + 1 = 0 := (mul_eq_zero.1 e1).resolve_left (sub_ne_zero.2 h6)
  have e3 : (x ^ 2 + 1) * (x ^ 4 - x ^ 2 + 1) = 0 := by rw [← e2]; ring
  have e4 : x ^ 2 + 1 ≠ 0 := fun h0 => h4 (by
    have : x ^ 4 - 1 = (x ^ 2 + 1) * (x ^ 2 - 1) := by ring
    rw [h0, zero_mul] at this
    exact sub_eq_zero.1 this)
  have e5 : x ^ 4 - x ^ 2 + 1 = 0 := (mul_eq_zero.1 e3).resolve_left e4
  have hle : (2 ^ m) ^ 2 ≤ (2 ^ m) ^ 4 :=
    Nat.pow_le_pow_right (Nat.one_le_two_pow) (by norm_num)
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast [Nat.cast_sub hle]
  rw [← hx]
  exact e5

theorem DispAt.conj {M : Type*} [Group M] {β : MulAut M} {n : ℕ} (h : DispAt M β n)
    (φ : MulAut M) : DispAt M (φ * β * φ⁻¹) n := by
  obtain ⟨ℓ, ms, hℓ, hℓ2, hdvd, hlt⟩ := h
  refine ⟨ℓ, ms.map φ, hℓ, hℓ2, ?_, by rwa [List.length_map]⟩
  have hc : ∀ m : M, MulAut.conj (φ m) = φ * MulAut.conj m * φ⁻¹ := fun m => by
    ext x
    simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]
  have e : ∀ l : List M,
      ((l.map φ).map fun m => MulAut.conj m * (φ * β * φ⁻¹) * (MulAut.conj m)⁻¹).prod =
        φ * (l.map fun m => MulAut.conj m * β * (MulAut.conj m)⁻¹).prod * φ⁻¹ := by
    intro l
    induction l with
    | nil => simp
    | cons m l ih =>
      simp only [List.map_cons, List.prod_cons] at ih ⊢
      rw [ih, hc]
      group
  rw [e]
  have h := orderOf_injective (MulAut.conj φ).toMonoidHom (MulAut.conj φ).injective
    (ms.map fun m => MulAut.conj m * β * (MulAut.conj m)⁻¹).prod
  change ℓ ∣ orderOf ((MulAut.conj φ).toMonoidHom
    (ms.map fun m => MulAut.conj m * β * (MulAut.conj m)⁻¹).prod)
  rw [h]
  exact hdvd

section Outer


theorem exists_fixed_inverting {e : ℕ} (he : 1 ≤ e) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (6 * e)) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ (2 * e))
    (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ 2 ^ (3 * e)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : p ∣ (2 ^ e) ^ 4 - (2 ^ e) ^ 2 + 1) :
    ∃ y t : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, y * y = 1 ∧ y * t * y⁻¹ = t⁻¹ ∧
      orderOf t = p ∧ fieldActor σ δ y = y ∧ fieldActor σ δ t = t := by
  obtain ⟨hmem, hK₀, -, hord, hJC, hJ, -⟩ :=
    even_triality_canonical_field_full_centralizer he K hK σ hσ δ hδ
  have : Finite (fixSubfield δ) := Subtype.finite
  set σ₀ := fixSubfieldRestrict σ δ with hσ₀
  have hσ₀3 : σ₀ ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one σ₀
  set τ := σ₀ ^ 2 with hτdef
  have hτ : ∀ c : fixSubfield δ, τ c = c ^ (2 ^ e) := by
    intro c
    apply Subtype.ext
    have hc : (c : K) ^ 2 ^ (3 * e) = c := (hmem c).1 c.2
    rw [hτdef, coe_fixSubfieldRestrict_pow, pow_two, RingAut.mul_apply, hσ, hσ, ← pow_mul,
      ← pow_add, SubmonoidClass.coe_pow,
      show 2 * e + 2 * e = 3 * e + e by ring, pow_add, pow_mul, hc]
  have hK₀' : Nat.card (fixSubfield δ) = (2 ^ e) ^ 3 := by rw [hK₀, ← pow_mul, mul_comm]
  obtain ⟨y, t, hy, hyt, hto⟩ :=
    exists_involution_inverting Nat.prime_two he (fixSubfield δ) hK₀' τ hτ hp hp3 hpd
  have hτ3 : τ ^ 3 = 1 := by rw [hτdef, ← pow_mul, mul_comm, pow_mul, hσ₀3, one_pow]
  have hτ2 : τ ^ 2 = σ₀ := by
    rw [hτdef, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hσ₀3, one_mul, pow_one]
  obtain ⟨eT, -⟩ :=
    (CFSG.RankThree.Chevalley.triality_diagram_transposition_exchanges_field_orientations
      (fixSubfield δ) τ hτ3
      ).2.2.2.2.2.2.2.2.2.2.2.1
  have hC : graphFixedRootGroup TwistTag.D4 (fixSubfield δ) (τ ^ 2).toRingHom =
      graphFixedRootGroup TwistTag.D4 (fixSubfield δ) σ₀.toRingHom := by rw [hτ2]
  set eT' := eT.trans (MulEquiv.subgroupCongr hC)
  set ι : graphFixedRootGroup TwistTag.D4 (fixSubfield δ) σ₀.toRingHom →*
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    MonoidHom.codRestrict ((baseChangeGL (fixSubfield δ).subtype).comp
      (graphFixedRootGroup TwistTag.D4 (fixSubfield δ) σ₀.toRingHom).subtype)
      _ (fun g => hJC ⟨g, g.2, rfl⟩) with hιdef
  have hιinj : Function.Injective ι := fun a b h =>
    Subtype.ext (baseChangeGL_injective (fixSubfield δ).subtype (congrArg Subtype.val h))
  have hfix : ∀ g, fieldActor σ δ (ι g) = ι g := by
    intro g
    have hg : ((ι g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
        ModGL TwistTag.D4.tag K) ∈ trialityFieldImage σ δ := ⟨g, g.2, rfl⟩
    rw [← hJ] at hg
    obtain ⟨x, hx, hxg⟩ := hg
    have hxe : x = ι g := Subtype.ext hxg
    rw [← hxe]
    exact hx
  refine ⟨ι (eT' y), ι (eT' t), ?_, ?_, ?_, hfix _, hfix _⟩
  · rw [← map_mul, ← map_mul, hy, map_one, map_one]
  · have h := congrArg (fun z => ι (eT' z)) hyt
    simpa only [map_mul, map_inv] using h
  · rw [orderOf_injective ι hιinj, MulEquiv.orderOf_eq, hto]

theorem dispAt_outer {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hα : α * α = 1)
    (hαo : α ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) :
    Even f ∧ DispAt (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) α (2 ^ (2 * f + 1)) := by
  classical
  have hα2 : α ^ 2 = 1 := by rw [sq, hα]
  obtain ⟨hev, δ, hδ, -, ψ, hψ, -⟩ :=
    even_triality_outer_involutions_canonical_field hf K hK σ hσ α hα2 hαo
  refine ⟨hev, ?_⟩
  obtain ⟨e, rfl⟩ : ∃ e, f = 2 * e := ⟨f / 2, by obtain ⟨r, hr⟩ := hev; omega⟩
  have he : 1 ≤ e := by omega
  have hK' : Nat.card K = 2 ^ (6 * e) := by rw [hK, ← pow_mul]; ring_nf
  have hσ' : ∀ c, σ c = c ^ 2 ^ (2 * e) := hσ
  have hδ' : ∀ c, δ c = c ^ 2 ^ (3 * e) := fun c => by
    rw [hδ]; congr 2; omega
  obtain ⟨-, hδ2, hδ1, -, -⟩ := triality_field_facts he hK' hσ' hδ'
  obtain ⟨ℓ, hℓ, hℓ2, hord⟩ := exists_prime_orderOf_two_eq (12 * e) (by omega) (by omega)
  obtain ⟨hℓ3, hℓd⟩ := ppd_twelve hℓ he hord
  obtain ⟨y, t, hy, hyt, hto, hfy, hft⟩ :=
    exists_fixed_inverting he K hK' σ hσ' δ hδ' hℓ hℓ3 hℓd
  obtain ⟨-, hNF, -⟩ := even_triality_exact_automorphism_normal_form hf K hK σ hσ
  have hZ := exceptional_fixed_center_trivial TwistTag.D4 K σ
  have hδ₀2 : (fieldActor (t := TwistTag.D4) σ δ) * fieldActor σ δ = 1 := by
    rw [← fieldActor_mul, ← sq, hδ2, fieldActor_one]
  have hconjδ : ∀ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      fieldActor σ δ * MulAut.conj g = MulAut.conj (fieldActor σ δ g) * fieldActor σ δ := by
    intro g
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
  have hβ2 : MulAut.conj y * fieldActor σ δ * (MulAut.conj y * fieldActor σ δ) = 1 := by
    rw [mul_assoc, ← mul_assoc (fieldActor σ δ), hconjδ, hfy, mul_assoc, hδ₀2, mul_one, ← map_mul,
      hy, map_one]
  have hβt : (MulAut.conj y * fieldActor σ δ :
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) t = t⁻¹ := by
    rw [MulAut.mul_apply, hft, MulAut.conj_apply, hyt]
  have hlt : (2 ^ (2 * (2 * e) + 1)) ^ 2 < 2 ^ orderOf (2 : ZMod ℓ) := by
    rw [hord, ← pow_mul]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hDβ : DispAt (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      (MulAut.conj y * fieldActor σ δ) (2 ^ (2 * (2 * e) + 1)) :=
    dispAt_of_inverts hZ hβ2 hβt hℓ hℓ2 (by rw [hto]) hlt
  have hβo : MulAut.conj y * fieldActor σ δ ∉
      (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
    rintro ⟨g, hg⟩
    have e1 : fieldActor σ δ = MulAut.conj (y⁻¹ * g) * fieldActor σ 1 := by
      rw [fieldActor_one, mul_one, map_mul, hg, map_inv, ← mul_assoc, inv_mul_cancel, one_mul]
    have e2 : fieldActor (t := TwistTag.D4) σ δ = MulAut.conj 1 * fieldActor σ δ := by
      rw [map_one, one_mul]
    obtain ⟨⟨g', δ'⟩, -, huniq⟩ := hNF (fieldActor σ δ)
    have h1 := huniq (y⁻¹ * g, 1) e1
    have h2 := huniq (1, δ) e2
    have : (1 : K ≃+* K) = δ := (congrArg Prod.snd h1).trans (congrArg Prod.snd h2).symm
    exact hδ1 this.symm
  have hβ2' : (MulAut.conj y * fieldActor σ δ) ^ 2 = 1 := by rw [sq, hβ2]
  obtain ⟨-, δ', hδ'c, -, ψ', hψ', -⟩ :=
    even_triality_outer_involutions_canonical_field hf K hK σ hσ _ hβ2' hβo
  have hδδ' : δ' = δ := RingEquiv.ext fun c => by rw [hδ'c, hδ]
  rw [hδδ'] at hψ'
  have hαβ : α = (ψ⁻¹ * ψ') * (MulAut.conj y * fieldActor σ δ) * (ψ⁻¹ * ψ')⁻¹ := by
    have e1 : α = ψ⁻¹ * fieldActor σ δ * ψ := by rw [← hψ]; group
    have e2 : (ψ⁻¹ * ψ') * (MulAut.conj y * fieldActor σ δ) * (ψ⁻¹ * ψ')⁻¹ =
        ψ⁻¹ * (ψ' * (MulAut.conj y * fieldActor σ δ) * ψ'⁻¹) * ψ := by group
    rw [e2, hψ', e1]
  rw [hαβ]
  exact DispAt.conj hDβ _

theorem card_le_index {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (F : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hF : IsElem2 F) :
    Nat.card F ≤ 2 ^ (if Even f then 1 else 0) *
      Nat.card (F ⊓ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range : Subgroup _) := by
  classical
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
    exact Subtype.finite
  have : Finite (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    Finite.of_injective (fun ψ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =>
      (ψ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) DFunLike.coe_injective
  obtain ⟨-, -, ⟨Θ, -, -, hker, hinv⟩, -⟩ :=
    even_triality_exact_automorphism_normal_form hf K hK σ hσ
  set φ := Θ.comp F.subtype with hφ
  have hcard := card_eq_range_mul_ker φ
  have hkerφ : Nat.card φ.ker = Nat.card (F ⊓ (MulAut.conj :
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range : Subgroup _) := by
    have hmem : ∀ x : F, x ∈ φ.ker ↔ (x : MulAut _) ∈ (MulAut.conj :
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
          MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := fun x => by
      rw [MonoidHom.mem_ker, ← hker, MonoidHom.mem_ker]
      rfl
    exact Nat.card_congr ⟨fun x => ⟨x, x.1.2, (hmem x.1).1 x.2⟩,
      fun y => ⟨⟨y, y.2.1⟩, (hmem ⟨y, y.2.1⟩).2 y.2.2⟩, fun x => rfl, fun y => rfl⟩
  have hsq : ∀ x : F, (x : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ^ 2 = 1 :=
    fun x => hF.2 x x.2
  have hrange : Nat.card φ.range ≤ 2 ^ (if Even f then 1 else 0) := by
    by_cases hev : Even f
    · simp only [hev, ↓reduceIte, pow_one]
      have hinj : Function.Injective (fun δ : φ.range => decide ((δ : K ≃+* K) = 1)) := by
        intro δ δ' h
        obtain ⟨x, hx⟩ := δ.2
        obtain ⟨x', hx'⟩ := δ'.2
        simp only [decide_eq_decide] at h
        by_cases h1 : (δ : K ≃+* K) = 1
        · exact Subtype.ext (h1.trans (h.1 h1).symm)
        · have h1' : (δ' : K ≃+* K) ≠ 1 := fun h2 => h1 (h.2 h2)
          have e1 := (hinv x (hsq x)).resolve_left (by rw [← hx] at h1; exact h1)
          have e2 := (hinv x' (hsq x')).resolve_left (by rw [← hx'] at h1'; exact h1')
          apply Subtype.ext
          rw [← hx, ← hx']
          exact RingEquiv.ext fun c => by
            change (Θ x) c = (Θ x') c
            rw [e1.2, e2.2]
      calc Nat.card φ.range ≤ Nat.card Bool := Nat.card_le_card_of_injective _ hinj
        _ = 2 := Nat.card_eq_two_iff' false |>.2 ⟨true, by decide, fun b hb => by
            cases b <;> simp_all⟩
    · simp only [hev, ↓reduceIte, pow_zero]
      have hall : ∀ δ ∈ φ.range, δ = 1 := by
        rintro _ ⟨x, rfl⟩
        rcases hinv x (hsq x) with h | h
        · exact h
        · exact absurd h.1 hev
      have hinj : Function.Injective (fun _ : φ.range => ()) := fun a b _ =>
        Subtype.ext ((hall a a.2).trans (hall b b.2).symm)
      calc Nat.card φ.range ≤ Nat.card Unit := Nat.card_le_card_of_injective _ hinj
        _ = 1 := Nat.card_unique
  rw [hcard, hkerφ]
  exact Nat.mul_le_mul_right _ hrange

end Outer

end CFSG.Quasithin.B42D4
