module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveLangTorus
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveSylowGroup
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveFixBound
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveOrder
public import CFSG.RankThree.PartOne.KE.CTLangData
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

namespace NoOffE8Five

local instance noOffE8FiveFactFiveCC : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

local instance noOffE8FiveNeZeroRankCC : NeZero Tag.E8.rank := ⟨by decide⟩

section Elementary

theorem exists_unit_orderOf_five_of_isAlgClosed {L : Type*} [Field L] [IsAlgClosed L]
    (h : ¬ ringChar L ∣ 5) : ∃ ζ : Lˣ, orderOf ζ = 5 := by
  have hcast : ((5 : ℕ) : L) ≠ 0 := fun hz => h ((ringChar.spec L 5).1 hz)
  haveI : NeZero ((5 : ℕ) : L) := ⟨hcast⟩
  obtain ⟨ε, hε⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 5
  have hu : IsUnit ε := hε.isUnit (by norm_num)
  refine ⟨hu.unit, ?_⟩
  rw [← orderOf_units, IsUnit.unit_spec]
  exact hε.eq_orderOf.symm

theorem isElemAbelian_range_of_module {p : ℕ} [Fact p.Prime] {V H : Type*} [AddCommGroup V]
    [Module (ZMod p) V] [Group H] (φ : Multiplicative V →* H) : IsElemAbelian p φ.range := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha⟩ := x.2
    obtain ⟨b, hb⟩ := y.2
    apply Subtype.ext
    change (x : H) * y = y * x
    rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨a, rfl⟩ := hx
    rw [← map_pow]
    have h : a ^ p = 1 := by
      refine Multiplicative.toAdd.injective ?_
      rw [toAdd_pow, toAdd_one]
      have : (p : ZMod p) • Multiplicative.toAdd a = 0 := by
        rw [ZMod.natCast_self, zero_smul]
      rwa [← Nat.cast_smul_eq_nsmul (ZMod p)]
    rw [h, map_one]

end Elementary

section ConjClass

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

theorem exists_conjClass_of_lang [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ]
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card K) (hℓK : ℓ ∣ Nat.card K) {ζ : Lˣ}
    (hζo : orderOf ζ = 5) (hζ : ζ ^ 5 = 1) {lam : ZMod 5} (hlam : lam * lam = -1)
    (hq : ((Nat.card K : ℕ) : ZMod 5) * lam = 1) (h5 : 5 ∣ Nat.card K * Nat.card K + 1)
    {g₀ : ModGL Tag.E8 L} (hg₀C : g₀ ∈ adjointGroup Tag.E8 L)
    (hg₀ : Units.map (entrywiseHom Fr) g₀ =
      g₀ * canonicalRep (coxeterSystem Tag.E8) L NoOffRest.weylE8W) :
    ∃ ι : Multiplicative (NoOffRest.eigE8 5 lam) →* adjointGroup Tag.E8 K,
      Function.Injective ι ∧
        ∀ A : Subgroup (adjointGroup Tag.E8 K), IsElemAbelian 5 A → 5 ^ 4 ≤ Nat.card A →
          ∃ c : adjointGroup Tag.E8 K, ι.range.map (MulAut.conj c).toMonoidHom = A := by
  classical
  haveI : Finite (ModGL Tag.E8 K) := finite_modGL
  obtain ⟨ι, hιinj, hιval⟩ := exists_langTorsionHom hFr hζo hζ hq hg₀C hg₀
  refine ⟨ι, hιinj, fun A hA hA4 => ?_⟩
  have hξ : ∀ s : NoOffRest.eigE8 5 lam,
      g₀ * ExcFrames.frameDiag (τ := Tag.E8) ζ hζ (s : Fin Tag.E8.rank → ZMod 5) * g₀⁻¹ =
        adjEmb Tag.E8 K L (ι (Multiplicative.ofAdd s)) := fun s => by
    rw [hιval s, frameElt_apply]
  have hXT : ι.range ≤ langTorusRat K Fr g₀ := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨s, hvs⟩ : ∃ s, v = Multiplicative.ofAdd s := ⟨Multiplicative.toAdd v, rfl⟩
    rw [hvs, mem_langTorusRat, langPhi_apply, hιval s, frameElt_apply]
    have : g₀⁻¹ * (g₀ * ExcFrames.frameDiag (τ := Tag.E8) ζ hζ (s : Fin Tag.E8.rank → ZMod 5) *
        g₀⁻¹) * g₀ = ExcFrames.frameDiag (τ := Tag.E8) ζ hζ (s : Fin Tag.E8.rank → ZMod 5) := by
      group
    rw [this]
    exact (frameDiag_mem_twistedTorus_iff hFr hζo hζ hq _).2 s.2
  have hTp : ∀ t ∈ langTorusRat K Fr g₀, t ^ 5 = 1 → t ∈ ι.range := by
    intro t ht ht5
    have hx5 : (langPhi K g₀ t) ^ 5 = 1 := by rw [← map_pow, ht5, map_one]
    obtain ⟨s, hs, hts⟩ := exists_frameDiag_of_mem_twistedTorus_pow hFr hζo hζ hq ht hx5
    refine ⟨Multiplicative.ofAdd ⟨s, hs⟩, ?_⟩
    apply adjEmb_injective (K := K) (L := L) (τ := Tag.E8)
    rw [← hξ ⟨s, hs⟩, adjEmb_eq_conj_langPhi g₀ t, hts]
  have hcent : ∀ c : adjointGroup Tag.E8 K, (∀ x ∈ ι.range, c * x = x * c) →
      c ∈ langTorusRat K Fr g₀ := by
    intro c hc
    refine mem_langTorusRat_of_commute hFr hζo hζ hlam hg₀C hg₀ fun s hs => ?_
    have h1 := hc (ι (Multiplicative.ofAdd ⟨s, hs⟩)) ⟨_, rfl⟩
    have h2 := congrArg (adjEmb Tag.E8 K L) h1
    rw [map_mul, map_mul] at h2
    change adjEmb Tag.E8 K L c * (g₀ * ExcFrames.frameDiag (τ := Tag.E8) ζ hζ s * g₀⁻¹) =
      (g₀ * ExcFrames.frameDiag (τ := Tag.E8) ζ hζ s * g₀⁻¹) * adjEmb Tag.E8 K L c
    exact (hξ ⟨s, hs⟩).symm ▸ h2
  have hcardX : Nat.card ι.range = 5 ^ 4 := by
    rw [← NoOffRest.card_eigE8 (p := 5) (by norm_num) hlam]
    exact (Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv).symm.trans
      (Nat.card_congr Multiplicative.toAdd)
  have hord : (Nat.card (adjointGroup Tag.E8 K)).factorization 5 =
      (Nat.card (langTorusRat K Fr g₀)).factorization 5 + 1 := by
    rw [factorization_card_adjointGroup_E8_five h5, card_langTorusRat hFr hℓK hg₀C hg₀,
      Nat.factorization_pow]
    simp
  have hfix : ∀ a : adjointGroup Tag.E8 K, a ∈ Subgroup.normalizer (ι.range : Set _) →
      a ^ 5 = 1 → (∃ x ∈ ι.range, a * x ≠ x * a) →
        Nat.card {x : ι.range // a * (x : adjointGroup Tag.E8 K) = (x : adjointGroup Tag.E8 K) * a}
          < 5 ^ 3 := by
    intro a ha ha5 hnc
    have hnorm : ∀ s : NoOffRest.eigE8 5 lam, ∃ t : NoOffRest.eigE8 5 lam,
        a * ι (Multiplicative.ofAdd s) * a⁻¹ = ι (Multiplicative.ofAdd t) := by
      intro s
      have h1 := (Subgroup.mem_normalizer_iff.mp ha (ι (Multiplicative.ofAdd s))).mp ⟨_, rfl⟩
      obtain ⟨v, hv⟩ := h1
      exact ⟨Multiplicative.toAdd v, hv.symm⟩
    exact card_centralizer_lt_of_automizer hlam ι hιinj
      (exists_centE8W_conj_of_langTorsion hζo hζ hlam hg₀C (fun s => by rw [hιval s]) hnorm) ha5 hnc
  obtain ⟨c, hc⟩ := exists_conj_map_eq_of_exponent_card (p := 5) (T := langTorusRat K Fr g₀)
    (X := ι.range) (fun x hx y hy => langTorusRat_comm hx hy) hXT
    (fun x hx => (isElemAbelian_range_of_module (p := 5) ι).2 x hx) hTp hcardX.le hord hcent hfix
    (fun x hx y hy => congrArg Subtype.val (hA.1.1.1 ⟨x, hx⟩ ⟨y, hy⟩)) hA.2 hA4
  exact ⟨c, hc⟩

end ConjClass

section Conjugacy


theorem exists_conj_map_eq_E8_five {K : Type} [Field K] [Finite K]
    (h5 : 5 ∣ Nat.card K * Nat.card K + 1)
    {A A' : Subgroup (adjointGroup Tag.E8 K)} (hA : IsElemAbelian 5 A) (hA' : IsElemAbelian 5 A')
    (h4 : 5 ^ 4 ≤ Nat.card A) (h4' : 5 ^ 4 ≤ Nat.card A') :
    ∃ c : adjointGroup Tag.E8 K, A.map (MulAut.conj c).toMonoidHom = A' := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have : CharP K (ringChar K) := ringChar.charP K
  let L := AlgebraicClosure K
  have : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let Fr : L →+* L := iterateFrobenius L (ringChar K) (f : ℕ)
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hq]
    exact iterateFrobenius_def (ringChar K) (f : ℕ) c
  have hℓq : ringChar K ∣ Nat.card K := by
    rw [hq]
    exact dvd_pow_self _ f.ne_zero
  obtain ⟨g₀, hg₀C, hg₀⟩ := lang_conjugator Tag.E8 K (ℓ := ringChar K) (f := (f : ℕ)) f.pos L
    NoOffRest.weylE8W
  have h5ℓ : ¬ ringChar L ∣ 5 := by
    rw [ringChar.eq L (ringChar K)]
    intro hd
    have h55 : ringChar K = 5 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_five).1 hd
    rw [h55] at hℓq
    have h1 : 5 ∣ Nat.card K * Nat.card K := Dvd.dvd.mul_right hℓq _
    have h2 := (Nat.dvd_add_right h1).1 h5
    exact absurd (Nat.le_of_dvd one_pos h2) (by norm_num)
  obtain ⟨ζ, hζo⟩ := exists_unit_orderOf_five_of_isAlgClosed (L := L) h5ℓ
  have hζ : ζ ^ 5 = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hkey : ∀ x : ZMod 5, x * x + 1 = 0 → (-x) * (-x) = -1 ∧ x * (-x) = 1 := by decide
  obtain ⟨hlam, hqlam⟩ := hkey ((Nat.card K : ℕ) : ZMod 5) (by
    have h := (ZMod.natCast_eq_zero_iff _ _).2 h5
    push_cast at h
    exact h)
  obtain ⟨ι, -, hcl⟩ := exists_conjClass_of_lang hFr hℓq hζo hζ hlam hqlam h5 hg₀C hg₀
  obtain ⟨c₁, hc₁⟩ := hcl A hA h4
  obtain ⟨c₂, hc₂⟩ := hcl A' hA' h4'
  refine ⟨c₂ * c₁⁻¹, ?_⟩
  rw [← hc₁, ← hc₂, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

end Conjugacy


end NoOffE8Five

end CFSG.StandardType
