module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddDefs
import CFSG.LocalAnalysis.GLTheoremA.S6.Setup
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Facts13

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup
open scoped commutatorElement
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

@[expose] def KOddLieAutSylow : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → ∀ (t : CFSG.Open.StatedLieTag) (n r f : ℕ),
    r ≠ 2 → CFSG.Open.StatedLieAdmissible t n r f → CFSG.Blueprint.LieModel X t n r f →
    t ≠ .twistedG2 → ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ S : Subgroup X,
      CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ → ∀ α : MulAut X, α ^ p = 1 →
        S.map α.toMonoidHom = S → ∀ x ∈ S, α x = x

@[expose] def KOddLieOutCentral : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → ∀ (t : CFSG.Open.StatedLieTag) (n r f : ℕ),
    r ≠ 2 → CFSG.Open.StatedLieAdmissible t n r f → CFSG.Blueprint.LieModel X t n r f →
    t ≠ .twistedG2 → ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ β : Outer X, β ^ p = 1 →
      ∀ R : Subgroup (Outer X), IsPGroup 2 R → β ∈ normalizer (R : Set (Outer X)) →
        ∀ ρ ∈ R, β * ρ = ρ * β

theorem fixes_of_fixes_isSylowOf {X : Type} [Group X] [Finite X] {p : ℕ} {S S₀ : Subgroup X}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) (hS₀ : CFSG.ABGLocalTools.IsSylowOf 2 S₀ ⊤)
    (hN : ∀ y ∈ normalizer (S : Set X), y ^ p ∈ centralizer (S : Set X) →
      y ∈ centralizer (S : Set X))
    {α : MulAut X} (hα : α ^ p = 1) (hαS : S.map α.toMonoidHom = S)
    (hαS₀ : ∀ x ∈ S₀, α x = x) : ∀ x ∈ S, α x = x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, -, hg⟩ := hS₀.exists_mem_conj hS
  let y : X := α g * g⁻¹
  have hαmem : ∀ z ∈ S, α z ∈ S := by
    intro z hz
    have h := Subgroup.mem_map_of_mem α.toMonoidHom hz
    rwa [hαS] at h
  have hparam : ∀ s ∈ S, ∃ s₀ ∈ S₀, g * s₀ * g⁻¹ = s := by
    intro s hs
    refine ⟨g⁻¹ * s * g, (hg s).mp hs, by group⟩
  have hact : ∀ s ∈ S, α s = y * s * y⁻¹ := by
    intro s hs
    obtain ⟨s₀, hs₀, rfl⟩ := hparam s hs
    change α (g * s₀ * g⁻¹) = (α g * g⁻¹) * (g * s₀ * g⁻¹) * (α g * g⁻¹)⁻¹
    rw [map_mul, map_mul, map_inv, hαS₀ s₀ hs₀]
    group
  have hyN : y ∈ normalizer (S : Set X) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      change (MulAut.conj y) z ∈ S
      rw [MulAut.conj_apply, show y * z * y⁻¹ = α z from (hact z hz).symm]
      exact hαmem z hz
    · intro x hx
      rw [Subgroup.mem_map]
      have hxmap : x ∈ S.map α.toMonoidHom := by rwa [hαS]
      rw [Subgroup.mem_map] at hxmap
      obtain ⟨z, hz, hzα⟩ := hxmap
      refine ⟨z, hz, ?_⟩
      change (MulAut.conj y) z = x
      rw [MulAut.conj_apply, ← hact z hz]
      simpa using hzα
  have hind : ∀ k : ℕ, ∀ s ∈ S, (α ^ k) s = y ^ k * s * (y ^ k)⁻¹ := by
    intro k
    induction k with
    | zero =>
        intro s hs
        simp
    | succ k ih =>
        intro s hs
        have hyk : y ^ k ∈ normalizer (S : Set X) :=
          (Subgroup.normalizer (S : Set X)).pow_mem hyN k
        have hzS : y ^ k * s * (y ^ k)⁻¹ ∈ S :=
          (Subgroup.mem_normalizer_iff.mp hyk s).mp hs
        calc (α ^ (k + 1)) s = α ((α ^ k) s) := by
              rw [pow_succ', MulAut.mul_apply]
          _ = α (y ^ k * s * (y ^ k)⁻¹) := by rw [ih s hs]
          _ = y * (y ^ k * s * (y ^ k)⁻¹) * y⁻¹ := hact _ hzS
          _ = y ^ (k + 1) * s * (y ^ (k + 1))⁻¹ := by
              rw [pow_succ']
              group
  have hcent : y ^ p ∈ centralizer (S : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h := hind p s hs
    rw [hα, MulAut.one_apply] at h
    calc s * y ^ p = (y ^ p * s * (y ^ p)⁻¹) * y ^ p := by
          conv_lhs => rw [h]
      _ = y ^ p * s := by group
  have hyC := hN y hyN hcent
  intro x hx
  have hcomm := (Subgroup.mem_centralizer_iff.mp hyC) x hx
  rw [hact x hx, ← hcomm]
  group

private theorem mem_of_conjNormal_mem_inner {A : Type} [Group A] {L : Subgroup A} [L.Normal]
    (hCL : centralizer (L : Set A) = ⊥) {a : A} (ha : (MulAut.conjNormal a : MulAut ↥L) ∈ inner ↥L) :
    a ∈ L := by
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp
    (show (MulAut.conjNormal a : MulAut ↥L) ∈
      (MulAut.conj : ↥L →* MulAut ↥L).range from ha)
  have hcomm : ∀ x : ↥L, (x : A) * ((y : A)⁻¹ * a) = ((y : A)⁻¹ * a) * (x : A) := by
    intro x
    have h := congrArg (fun (f : MulAut ↥L) => ((f x : ↥L) : A)) hy
    simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h
    calc (x : A) * ((y : A)⁻¹ * a)
        = (y : A)⁻¹ * ((y : A) * (x : A) * (y : A)⁻¹) * a := by group
      _ = (y : A)⁻¹ * (a * (x : A) * a⁻¹) * a := by rw [h]
      _ = ((y : A)⁻¹ * a) * (x : A) := by group
  have hz : ((y : A)⁻¹ * a) ∈ centralizer (L : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact hcomm ⟨w, hw⟩
  rw [hCL, Subgroup.mem_bot] at hz
  have ha' : a = (y : A) := by
    calc a = (y : A) * ((y : A)⁻¹ * a) := by group
      _ = (y : A) * 1 := by rw [hz]
      _ = (y : A) := mul_one _
  rw [ha']
  exact y.2

theorem kOddLieNormSylowAlpha_of_aut_out (hA : KOddLieAutSylow) (hO : KOddLieOutCentral) :
    KOddLieNormSylowAlpha := by
  intro A _ _ L hLn hLs hCL t n r f hr2 hadm hmod ht s p T B hs hp hdvd hT hBT hBp
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp7 : 7 ≤ p := CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_seven_le_of_dvd hs hp hdvd
  have hp5 : 5 ≤ p := by omega
  have hp2 : p ≠ 2 := by omega
  have hbpow : ∀ b ∈ B, b ^ p = 1 := by
    intro b hb
    have h := Subgroup.orderOf_dvd_natCard B hb
    rw [hBp] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  let S' : Subgroup ↥L := T.subgroupOf L
  have hS' : CFSG.ABGLocalTools.IsSylowOf 2 S' ⊤ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff L]
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.map_top, Subgroup.range_subtype]
    exact CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hT le_top
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hLn])
  have hcommTLB : ⁅T ⊓ L, B⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hmap : S'.map (MulAut.conjNormal (H := L) b).toMonoidHom = S' := by
      ext x
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨z, hz, rfl⟩
        rw [Subgroup.mem_subgroupOf] at hz ⊢
        change ((MulAut.conjNormal (H := L) b) z : A) ∈ T
        rw [MulAut.conjNormal_apply]
        exact (Subgroup.mem_normalizer_iff.mp (hBT hb) (z : A)).mp hz
      · intro hx
        refine ⟨(MulAut.conjNormal (H := L) b)⁻¹ x, ?_, ?_⟩
        · rw [Subgroup.mem_subgroupOf] at hx ⊢
          rw [← map_inv]
          change ((MulAut.conjNormal (H := L) b⁻¹) x : A) ∈ T
          rw [MulAut.conjNormal_apply]
          exact (Subgroup.mem_normalizer_iff.mp
            ((Subgroup.normalizer (T : Set A)).inv_mem (hBT hb)) (x : A)).mp hx
        · simp
    have hαp : (MulAut.conjNormal (H := L) b) ^ p = 1 := by
      rw [← map_pow, hbpow b hb, map_one]
    have hfix := hA ↥L hLs t n r f hr2 hadm hmod ht p hp hp5 S' hS'
      (MulAut.conjNormal (H := L) b) hαp hmap
    have hx : (⟨s, hs.2⟩ : ↥L) ∈ S' := by
      rw [Subgroup.mem_subgroupOf]
      exact hs.1
    have h := hfix ⟨s, hs.2⟩ hx
    have hcoe := congrArg Subtype.val h
    simp only [MulAut.conjNormal_apply] at hcoe
    calc b * s = (b * s * b⁻¹) * b := by group
      _ = s * b := by rw [hcoe]
  let φ : A →* Outer ↥L := (QuotientGroup.mk' (inner ↥L)).comp (MulAut.conjNormal (H := L))
  let R : Subgroup (Outer ↥L) := T.map φ
  have hR2 : IsPGroup 2 R := hT.isPGroup.map φ
  have hφbN : ∀ b ∈ B, φ b ∈ normalizer (R : Set (Outer ↥L)) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hTmap : T.map (MulAut.conj b).toMonoidHom = T :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hBT hb)
    have hcomp : (MulAut.conj (φ b)).toMonoidHom.comp φ =
        φ.comp (MulAut.conj b).toMonoidHom := by
      ext x
      change (MulAut.conj (φ b)) (φ x) = φ ((MulAut.conj b) x)
      rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
    calc R.map (MulAut.conj (φ b)).toMonoidHom
        = T.map ((MulAut.conj (φ b)).toMonoidHom.comp φ) := by
          rw [Subgroup.map_map]
      _ = T.map (φ.comp (MulAut.conj b).toMonoidHom) := by rw [hcomp]
      _ = (T.map (MulAut.conj b).toMonoidHom).map φ := by rw [Subgroup.map_map]
      _ = R := by rw [hTmap]
  have hcomm_le : ⁅T, B⁆ ≤ T ⊓ L := by
    rw [Subgroup.commutator_le]
    intro u hu b hb
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hbt : b * u⁻¹ * b⁻¹ ∈ T :=
        (Subgroup.mem_normalizer_iff.mp (hBT hb) u⁻¹).mp (T.inv_mem hu)
      rw [commutatorElement_def]
      rw [show u * b * u⁻¹ * b⁻¹ = u * (b * u⁻¹ * b⁻¹) by group]
      exact T.mul_mem hu hbt
    · have hβcomm := hO ↥L hLs t n r f hr2 hadm hmod ht p hp hp5 (φ b) ?_ R hR2 (hφbN b hb)
      · have hφuR : φ u ∈ R := Subgroup.mem_map_of_mem φ hu
        have hφb1 : φ (⁅u, b⁆) = 1 :=
          (map_commutatorElement φ u b).trans
            (commutatorElement_eq_one_iff_mul_comm.mpr (hβcomm (φ u) hφuR).symm)
        have hcinner : (MulAut.conjNormal (H := L) (⁅u, b⁆) : MulAut ↥L) ∈
            CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L := by
          refine (QuotientGroup.eq_one_iff (N :=
            CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L) _).mp ?_
          rw [← QuotientGroup.mk'_apply]
          exact hφb1
        exact mem_of_conjNormal_mem_inner hCL hcinner
      · rw [← map_pow, hbpow b hb, map_one]
  have hBpgroup : IsPGroup p B := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hBp)
  have hdouble : ⁅⁅T, B⁆, B⁆ = ⁅T, B⁆ :=
    CFSG.LocalAnalysis.GLTheoremA.commutator_commutator_eq_of_isPGroup hp hBpgroup
      hT.isPGroup hp2 hBT
  rw [eq_bot_iff]
  exact (by rw [← hdouble]; exact Subgroup.commutator_mono hcomm_le le_rfl :
    ⁅T, B⁆ ≤ ⁅T ⊓ L, B⁆).trans (le_of_eq hcommTLB)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
