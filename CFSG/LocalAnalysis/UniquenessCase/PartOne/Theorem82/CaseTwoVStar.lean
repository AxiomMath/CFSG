module

public import CFSG.GroupTheory.ABGLocalTools.PStabilityChief
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoShapeB
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKyNormal
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
import CFSG.SignalizerFunctorTheorem.Nonsolvable.ASimple.ThreeCentralizers
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndSmall
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoShape
public import CFSG.LocalAnalysis.UniquenessCase.UC6Mod
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

private theorem three_not_dvd_Oz : ¬ 3 ∣ Nat.card t.Oz := by
  intro h3
  have hcard : Nat.card t.Oz = Nat.card (CFSG.pPrimeCore 3 ↥t.Xz) :=
    Subgroup.card_map_of_injective t.Xz.subtype_injective
  rw [hcard] at h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime 3 (Nat.card (CFSG.pPrimeCore 3 ↥t.Xz)) :=
    CFSG.pPrimeCore_coprime_card
  have h : 3 ∣ Nat.gcd 3 (Nat.card (CFSG.pPrimeCore 3 ↥t.Xz)) := Nat.dvd_gcd dvd_rfl h3
  rw [hcop] at h
  norm_num at h

private theorem three_not_dvd_N : ¬ 3 ∣ Nat.card t.d.N := by
  obtain ⟨n, hn⟩ := t.d.N_isPGroup.exists_card_eq
  rw [hn]
  intro h
  have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) h
  norm_num at h32

private theorem Ky_le_normalizer_Oz (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) :
    t.Ky ≤ Subgroup.normalizer (t.Oz : Set G) :=
  (t.Ky_le_Xz hK32 hGA hSp).trans
    (CFSG.ABGLocalTools.le_normalizer_map_subtype t.Xz (CFSG.pPrimeCore 3 ↥t.Xz))

private theorem centralizer_conj_le_M (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M)
    {b : G} (hb : b ∈ c.S.M) :
    Subgroup.centralizer
      ((Subgroup.map (MulAut.conj b).toMonoidHom t.Z : Subgroup G) : Set G) ≤ c.S.M := by
  intro n hn
  have hkey : b⁻¹ * n * b ∈ Subgroup.centralizer (t.Z : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hmem : b * z * b⁻¹ ∈
        (Subgroup.map (MulAut.conj b).toMonoidHom t.Z : Subgroup G) :=
      Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
    have hcomm : (b * z * b⁻¹) * n = n * (b * z * b⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp hn) _ hmem
    calc z * (b⁻¹ * n * b) = b⁻¹ * ((b * z * b⁻¹) * n) * b := by group
      _ = b⁻¹ * (n * (b * z * b⁻¹)) * b := by rw [hcomm]
      _ = (b⁻¹ * n * b) * z := by group
  have hMn : b⁻¹ * n * b ∈ c.S.M := hZ hkey
  have hn_eq : n = b * (b⁻¹ * n * b) * b⁻¹ := by group
  rw [hn_eq]
  exact c.S.M.mul_mem (c.S.M.mul_mem hb hMn) (c.S.M.inv_mem hb)

private theorem exists_minimal_U (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hO : ¬ t.Oz ≤ c.S.M) :
    ∃ U : Subgroup G, U ≤ t.Oz ∧ t.Ky ≤ Subgroup.normalizer (U : Set G) ∧ ¬ U ≤ c.S.M ∧
      ∀ V : Subgroup G, V ≤ t.Oz → t.Ky ≤ Subgroup.normalizer (V : Set G) → ¬ V ≤ c.S.M →
        Nat.card U ≤ Nat.card V := by
  classical
  have hKyN : t.Ky ≤ Subgroup.normalizer (t.Oz : Set G) := t.Ky_le_normalizer_Oz hK32 hGA hSp
  have hex : ∃ n : ℕ, ∃ U : Subgroup G, U ≤ t.Oz ∧
      t.Ky ≤ Subgroup.normalizer (U : Set G) ∧ ¬ U ≤ c.S.M ∧ n = Nat.card U :=
    ⟨Nat.card t.Oz, t.Oz, le_rfl, hKyN, hO, rfl⟩
  obtain ⟨U, hUle, hUK, hUM, hUcard⟩ := Nat.find_spec hex
  refine ⟨U, hUle, hUK, hUM, fun V hVle hVK hVM => ?_⟩
  have hspec : ∃ U' : Subgroup G, U' ≤ t.Oz ∧
      t.Ky ≤ Subgroup.normalizer (U' : Set G) ∧ ¬ U' ≤ c.S.M ∧ Nat.card V = Nat.card U' :=
    ⟨V, hVle, hVK, hVM, rfl⟩
  have h : Nat.find hex ≤ Nat.card V := Nat.find_min' hex hspec
  rw [← hUcard]
  exact h

private theorem exists_maximal_W {U : Subgroup G} (hUbot : U ≠ ⊥) :
    ∃ W : Subgroup G, W ≤ U ∧ U ≤ Subgroup.normalizer (W : Set G) ∧
      t.Ky ≤ Subgroup.normalizer (W : Set G) ∧ W ≠ U ∧
      ∀ X : Subgroup G, W ≤ X → X ≤ U → U ≤ Subgroup.normalizer (X : Set G) →
        t.Ky ≤ Subgroup.normalizer (X : Set G) → X ≠ U → X = W := by
  classical
  have hbotU : U ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hbotK : t.Ky ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hbotne : (⊥ : Subgroup G) ≠ U := fun h => hUbot h.symm
  have hex : ∃ n : ℕ, ∃ W : Subgroup G, W ≤ U ∧ U ≤ Subgroup.normalizer (W : Set G) ∧
      t.Ky ≤ Subgroup.normalizer (W : Set G) ∧ W ≠ U ∧ n = Nat.card U - Nat.card W :=
    ⟨Nat.card U - Nat.card ↥(⊥ : Subgroup G), ⊥, bot_le, hbotU, hbotK, hbotne, rfl⟩
  obtain ⟨W, hWle, hWU, hWK, hWne, hWcard⟩ := Nat.find_spec hex
  refine ⟨W, hWle, hWU, hWK, hWne, fun X hWX hXU hXU' hXK hXne => ?_⟩
  have hspec : (fun n : ℕ => ∃ W' : Subgroup G, W' ≤ U ∧
      U ≤ Subgroup.normalizer (W' : Set G) ∧ t.Ky ≤ Subgroup.normalizer (W' : Set G) ∧
      W' ≠ U ∧ n = Nat.card U - Nat.card W') (Nat.card U - Nat.card X) :=
    ⟨X, hXU, hXU', hXK, hXne, rfl⟩
  have h : Nat.find hex ≤ Nat.card U - Nat.card X := Nat.find_min' hex hspec
  have hWU' : Nat.card W ≤ Nat.card U :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hWle)
  have hXU'' : Nat.card X ≤ Nat.card U :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hXU)
  have hcard : Nat.card X ≤ Nat.card W := by omega
  exact (Subgroup.eq_of_le_of_card_ge hWX hcard).symm


private theorem forall_fixed_of_fixed {U W : Subgroup G}
    (hWK : t.Ky ≤ Subgroup.normalizer (W : Set G))
    (hWU : U ≤ Subgroup.normalizer (W : Set G))
    {b z u : G} (hb : b ∈ t.Ky) (hzZ : z ∈ t.Z) (hz1 : z ≠ 1) (hu : u ∈ U)
    (hq : u⁻¹ * (b * z * b⁻¹) * u * (b * z * b⁻¹)⁻¹ ∈ W) :
    ∀ x ∈ t.Z, u⁻¹ * (b * x * b⁻¹) * u * (b * x * b⁻¹)⁻¹ ∈ W := by
  classical
  have hbN : b ∈ Subgroup.normalizer (W : Set G) := hWK hb
  have hbNinv : b⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.inv_mem (Subgroup.normalizer (W : Set G)) hbN
  have huN : u ∈ Subgroup.normalizer (W : Set G) := hWU hu
  let S : Subgroup G :=
    { carrier := {y : G | y ∈ Subgroup.normalizer (W : Set G) ∧
        u⁻¹ * (b * y * b⁻¹) * u * (b * y * b⁻¹)⁻¹ ∈ W},
      one_mem' := by
        refine ⟨Subgroup.one_mem _, ?_⟩
        simpa using W.one_mem,
      mul_mem' := by
        rintro y₁ y₂ ⟨h1N, h1⟩ ⟨h2N, h2⟩
        have hA1N : b * y₁ * b⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
          Subgroup.mul_mem (Subgroup.normalizer (W : Set G))
            (Subgroup.mul_mem (Subgroup.normalizer (W : Set G)) hbN h1N) hbNinv
        refine ⟨Subgroup.mul_mem (Subgroup.normalizer (W : Set G)) h1N h2N, ?_⟩
        have heq : u⁻¹ * (b * (y₁ * y₂) * b⁻¹) * u * (b * (y₁ * y₂) * b⁻¹)⁻¹ =
            (u⁻¹ * (b * y₁ * b⁻¹) * u * (b * y₁ * b⁻¹)⁻¹) *
              ((b * y₁ * b⁻¹) * (u⁻¹ * (b * y₂ * b⁻¹) * u * (b * y₂ * b⁻¹)⁻¹) *
                (b * y₁ * b⁻¹)⁻¹) := by group
        rw [heq]
        exact W.mul_mem h1 ((Subgroup.mem_normalizer_iff.mp hA1N _).mp h2),
      inv_mem' := by
        rintro y ⟨hyN, hy⟩
        have hAN : b * y * b⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
          Subgroup.mul_mem (Subgroup.normalizer (W : Set G))
            (Subgroup.mul_mem (Subgroup.normalizer (W : Set G)) hbN hyN) hbNinv
        refine ⟨Subgroup.inv_mem (Subgroup.normalizer (W : Set G)) hyN, ?_⟩
        have heq : u⁻¹ * (b * y⁻¹ * b⁻¹) * u * (b * y⁻¹ * b⁻¹)⁻¹ =
            (b * y * b⁻¹)⁻¹ * (u⁻¹ * (b * y * b⁻¹) * u * (b * y * b⁻¹)⁻¹)⁻¹ *
              (b * y * b⁻¹) := by group
        rw [heq]
        simpa using (Subgroup.mem_normalizer_iff.mp
          (Subgroup.inv_mem (Subgroup.normalizer (W : Set G)) hAN) _).mp (W.inv_mem hy) }
  have hz3 : z ^ 3 = 1 := t.d.isElemAbelian_AA.2 z (t.Z_le_AA hzZ)
  have hzord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hZgen : t.Z = Subgroup.zpowers z := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzZ) ?_).symm
    rw [Nat.card_zpowers, hzord, t.card_Z]
  have hzS : z ∈ S := ⟨hWK (t.Z_le_Ky hzZ), hq⟩
  have hle : Subgroup.zpowers z ≤ S := Subgroup.zpowers_le.mpr hzS
  intro x hx
  exact (hle (hZgen ▸ hx)).2

private theorem mem_sup_inf_of_fixed (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M)
    {U W : Subgroup G} (hFW : ¬ 3 ∣ Nat.card W) (hWle : W ≤ U)
    (hWU : U ≤ Subgroup.normalizer (W : Set G))
    (hWK : t.Ky ≤ Subgroup.normalizer (W : Set G))
    {b : G} (hb : b ∈ t.Ky) {u : G} (hu : u ∈ U)
    (hq : ∀ x ∈ t.Z, u⁻¹ * (b * x * b⁻¹) * u * (b * x * b⁻¹)⁻¹ ∈ W) :
    u ∈ ((U ⊓ c.S.M) ⊔ W) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbM : b ∈ c.S.M := c.hyp81.1 (t.Ky_le hb).1
  set X : Subgroup G := Subgroup.map (MulAut.conj b).toMonoidHom t.Z with hX
  have hXcard : Nat.card X = 3 := by
    rw [hX, Subgroup.card_map_of_injective (f := (MulAut.conj b).toMonoidHom)
      (fun x y hxy => (MulAut.conj b).injective hxy), t.card_Z]
  have hXpg : IsPGroup 3 ↥X := IsPGroup.of_card (n := 1) (by rw [hXcard]; norm_num)
  have hXNW : ∀ x ∈ X, ∀ f ∈ W, x * f * x⁻¹ ∈ W := by
    intro x hx f hf
    obtain ⟨z, hz, hxz⟩ := Subgroup.mem_map.mp hx
    rw [← hxz, show (MulEquiv.toMonoidHom (MulAut.conj b)) z = b * z * b⁻¹ from rfl]
    have hzN : z ∈ Subgroup.normalizer (W : Set G) := hWK (t.Z_le_Ky hz)
    have hbN : b ∈ Subgroup.normalizer (W : Set G) := hWK hb
    have hxN : b * z * b⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
      Subgroup.mul_mem (Subgroup.normalizer (W : Set G))
        (Subgroup.mul_mem (Subgroup.normalizer (W : Set G)) hbN hzN)
        (Subgroup.inv_mem (Subgroup.normalizer (W : Set G)) hbN)
    exact (Subgroup.mem_normalizer_iff.mp hxN f).mp hf
  have hq' : ∀ x ∈ X, u⁻¹ * (x * u * x⁻¹) ∈ W := by
    intro x hx
    obtain ⟨z, hz, hxz⟩ := Subgroup.mem_map.mp hx
    rw [← hxz, show (MulEquiv.toMonoidHom (MulAut.conj b)) z = b * z * b⁻¹ from rfl]
    simpa only [mul_assoc] using hq z hz
  obtain ⟨n, hnW, hnfix⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.exists_fixed_in_coset_uc6 X W hXpg hFW hXNW u hq'
  have hnU : n ∈ U := by
    have h2 : u * (u⁻¹ * n) = n := by group
    rw [← h2]
    exact U.mul_mem hu (hWle hnW)
  have hnC : n ∈ Subgroup.centralizer
      ((Subgroup.map (MulAut.conj b).toMonoidHom t.Z : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxX : x ∈ X := by rw [hX]; exact hx
    have hfix := hnfix x hxX
    calc x * n = (x * n * x⁻¹) * x := by group
      _ = n * x := by rw [hfix]
  have hnM : n ∈ c.S.M := t.centralizer_conj_le_M hZ hbM hnC
  have hn_inf : n ∈ U ⊓ c.S.M := Subgroup.mem_inf.mpr ⟨hnU, hnM⟩
  have hu_eq : u = n * (u⁻¹ * n)⁻¹ := by group
  rw [hu_eq]
  have h1 : n ∈ (U ⊓ c.S.M) ⊔ W :=
    (le_sup_left : (U ⊓ c.S.M) ≤ (U ⊓ c.S.M) ⊔ W) hn_inf
  have h2 : (u⁻¹ * n)⁻¹ ∈ (U ⊓ c.S.M) ⊔ W :=
    (le_sup_right : W ≤ (U ⊓ c.S.M) ⊔ W) (W.inv_mem hnW)
  exact Subgroup.mul_mem ((U ⊓ c.S.M) ⊔ W) h1 h2


private theorem inv_mul_conj_mem_of_mul_conj_mem {W : Subgroup G} {u x : G}
    (hu : u ∈ Subgroup.normalizer (W : Set G)) (h : x * u * x⁻¹ * u⁻¹ ∈ W) :
    u⁻¹ * (x * u * x⁻¹) ∈ W := by
  have heq : u⁻¹ * (x * u * x⁻¹) = u⁻¹ * (x * u * x⁻¹ * u⁻¹) * u := by group
  rw [heq]
  simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hu) _).mp h

theorem le_inf_sup_of_commutator_not_le
    (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M)
    {U W : Subgroup G} (hU3 : ¬ 3 ∣ Nat.card U) (hne : U ⊔ t.Ky ≠ ⊤)
    (hUK : t.Ky ≤ Subgroup.normalizer (U : Set G))
    (hWle : W ≤ U) (hWne : W ≠ U)
    (hWU : U ≤ Subgroup.normalizer (W : Set G))
    (hWK : t.Ky ≤ Subgroup.normalizer (W : Set G))
    (hWmax : ∀ X : Subgroup G, W ≤ X → X ≤ U → U ≤ Subgroup.normalizer (X : Set G) →
      t.Ky ≤ Subgroup.normalizer (X : Set G) → X ≠ U → X = W)
    (hcomm : ¬ ⁅U, U⁆ ≤ W) : U ≤ (U ⊓ c.S.M) ⊔ W := by
  classical
  let S : Subgroup G := U ⊔ t.Ky
  have hUS : U ≤ S := le_sup_left
  have hKS : t.Ky ≤ S := le_sup_right
  have hSnormW : S ≤ Subgroup.normalizer (W : Set G) := sup_le hWU hWK
  have hWSnormal : (W.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hWle.trans hUS)).mpr hSnormW
  letI : (W.subgroupOf S).Normal := hWSnormal
  let Γ : Type := ↥S ⧸ (W.subgroupOf S)
  let πS : ↥S →* Γ := QuotientGroup.mk' (W.subgroupOf S)
  let A : Subgroup Γ := (t.Ky.subgroupOf S).map πS
  let K : Subgroup Γ := (U.subgroupOf S).map πS
  let H₀ : Subgroup G := (U ⊓ c.S.M) ⊔ W
  let K₀ : Subgroup Γ := (H₀.subgroupOf S).map πS
  have hZS : t.Z ≤ S := t.Z_le_Ky.trans hKS
  have hzex : ∃ z ∈ t.Z, z ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : t.Z = ⊥ := (Subgroup.eq_bot_iff_forall t.Z).mpr h
    have hcard : Nat.card t.Z = 1 := by rw [hbot]; simp
    have h3card := t.card_Z
    omega
  obtain ⟨z, hzZ, hz1⟩ := hzex
  have hzS : z ∈ S := hZS hzZ
  let zbar : Γ := πS ⟨z, hzS⟩
  have hFW : ¬ 3 ∣ Nat.card W := fun h => hU3 (h.trans (Subgroup.card_dvd_of_le hWle))
  have hzbar3 : zbar ^ 3 = 1 := by
    have h3 : (⟨z, hzS⟩ : ↥S) ^ 3 = 1 := Subtype.ext (by
      show z ^ 3 = 1
      exact t.d.isElemAbelian_AA.2 z (t.Z_le_AA hzZ))
    show πS ⟨z, hzS⟩ ^ 3 = 1
    rw [← map_pow, h3, map_one]
  have hzbar_ne : zbar ≠ 1 := by
    intro h
    have hmem : (⟨z, hzS⟩ : ↥S) ∈ W.subgroupOf S := (QuotientGroup.eq_one_iff _).mp h
    have hzW : z ∈ W := Subgroup.mem_subgroupOf.mp hmem
    have hZW : 3 ∣ Nat.card W := by
      have hle : Subgroup.zpowers z ≤ W := Subgroup.zpowers_le.mpr hzW
      have hdiv := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_zpowers, orderOf_eq_prime (t.d.isElemAbelian_AA.2 z (t.Z_le_AA hzZ))
        hz1] at hdiv
    exact hFW hZW
  have hzbarord : orderOf zbar = 3 := orderOf_eq_prime hzbar3 hzbar_ne
  have hzA : zbar ∈ A :=
    Subgroup.mem_map.mpr ⟨⟨z, hzS⟩, Subgroup.mem_subgroupOf.mpr (t.Z_le_Ky hzZ), rfl⟩
  have hK3 : ¬ 3 ∣ Nat.card ↥K := by
    have h1 : Nat.card ↥K ∣ Nat.card ↥(U.subgroupOf S) := Subgroup.card_map_dvd _ _
    have h2 : Nat.card ↥(U.subgroupOf S) = Nat.card ↥U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUS).toEquiv
    intro hdvd
    rw [h2] at h1
    exact hU3 (hdvd.trans h1)
  have hperfA : ⁅A, A⁆ = A := by
    have hsub : ⁅t.Ky.subgroupOf S, t.Ky.subgroupOf S⁆ = (⁅t.Ky, t.Ky⁆).subgroupOf S := by
      refine Subgroup.map_injective S.subtype_injective ?_
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKS,
        Subgroup.map_subgroupOf_eq_of_le (by rw [t.commutator_Ky]; exact hKS),
        t.commutator_Ky]
    calc ⁅A, A⁆ = Subgroup.map πS ⁅t.Ky.subgroupOf S, t.Ky.subgroupOf S⁆ := by
          rw [Subgroup.map_commutator]
      _ = Subgroup.map πS ((⁅t.Ky, t.Ky⁆).subgroupOf S) := by rw [hsub]
      _ = Subgroup.map πS (t.Ky.subgroupOf S) := by rw [t.commutator_Ky]
      _ = A := rfl
  let πU : ↥U →* Γ := πS.comp (Subgroup.inclusion hUS)
  have hπU_range : πU.range = K := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_map]
    congr 1
    ext x
    constructor
    · intro hx
      obtain ⟨u, -, rfl⟩ := Subgroup.mem_map.mp hx
      exact u.2
    · intro hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  have hπU_eq : ∀ u : ↥U, πU u = πS ⟨(u : G), hUS u.2⟩ := fun u => rfl
  have hnormKi : A ≤ Subgroup.normalizer (K : Set Γ) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha k hk
    obtain ⟨b, hb, rfl⟩ := ha
    obtain ⟨u, hu, rfl⟩ := hk
    have hbKy : (b : G) ∈ t.Ky := Subgroup.mem_subgroupOf.mp hb
    have huU : (u : G) ∈ U := Subgroup.mem_subgroupOf.mp hu
    have hconjU : (b : G) * (u : G) * (b : G)⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hUK hbKy) (u : G)).mp huU
    refine Subgroup.mem_map.mpr ⟨⟨(b : G) * (u : G) * (b : G)⁻¹, hUS hconjU⟩,
      Subgroup.mem_subgroupOf.mpr hconjU, ?_⟩
    show πS ⟨(b : G) * (u : G) * (b : G)⁻¹, hUS hconjU⟩ = πS b * πS u * (πS b)⁻¹
    rw [show (⟨(b : G) * (u : G) * (b : G)⁻¹, hUS hconjU⟩ : ↥S) = b * u * b⁻¹ from rfl]
    simp only [map_mul, map_inv]
  have hnonabK : ∃ x ∈ K, ∃ y ∈ K, x * y ≠ y * x := by
    obtain ⟨u₁, hu₁, u₂, hu₂, hne⟩ : ∃ u₁ ∈ U, ∃ u₂ ∈ U, ⁅u₁, u₂⁆ ∉ W := by
      by_contra h
      push Not at h
      exact hcomm (Subgroup.commutator_le.mpr fun x hx y hy => h x hx y hy)
    have hmemU₁ : (⟨u₁, hUS hu₁⟩ : ↥S) ∈ U.subgroupOf S :=
      Subgroup.mem_subgroupOf.mpr hu₁
    have hmemU₂ : (⟨u₂, hUS hu₂⟩ : ↥S) ∈ U.subgroupOf S :=
      Subgroup.mem_subgroupOf.mpr hu₂
    refine ⟨πS ⟨u₁, hUS hu₁⟩, Subgroup.mem_map.mpr ⟨_, hmemU₁, rfl⟩,
      πS ⟨u₂, hUS hu₂⟩, Subgroup.mem_map.mpr ⟨_, hmemU₂, rfl⟩, ?_⟩
    intro heq
    apply hne
    have hmemS : ⁅u₁, u₂⁆ ∈ S := hUS (U.mul_mem (U.mul_mem (U.mul_mem hu₁ hu₂)
      (U.inv_mem hu₁)) (U.inv_mem hu₂))
    have hone : πS (⟨⁅u₁, u₂⁆, hmemS⟩ : ↥S) = 1 := by
      have hcomp : (⟨⁅u₁, u₂⁆, hmemS⟩ : ↥S) =
          ⟨u₁, hUS hu₁⟩ * ⟨u₂, hUS hu₂⟩ * (⟨u₁, hUS hu₁⟩)⁻¹ *
            (⟨u₂, hUS hu₂⟩)⁻¹ :=
        Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv,
          commutatorElement_def])
      rw [hcomp]
      simp only [map_mul, map_inv]
      rw [heq]
      group
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hone)
  have hmin : ∀ N : Subgroup Γ, N ≤ K → (N.subgroupOf K).Normal →
      A ≤ Subgroup.normalizer (N : Set Γ) → N = ⊥ ∨ N = K := by
    intro N hNK hNnorm hAN
    have hKN : K ≤ Subgroup.normalizer (N : Set Γ) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mp hNnorm
    have hNK' : N ≤ πU.range := by rwa [hπU_range]
    let N₁ : Subgroup ↥U := N.comap πU
    have hNmap : Subgroup.map πU N₁ = N := Subgroup.map_comap_eq_self hNK'
    have hWN₁ : W.subgroupOf U ≤ N₁ := by
      intro w hw
      rw [Subgroup.mem_comap]
      have hπw : πU w = 1 := by
        rw [hπU_eq]
        exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr
          (Subgroup.mem_subgroupOf.mp hw))
      rw [hπw]
      exact N.one_mem
    have hN₁U : U ≤ Subgroup.normalizer ((N₁.map U.subtype : Subgroup G) : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro u hu x hx
      obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
      have hx'U : (x' : G) ∈ U := x'.2
      have hx'U' : (x' : G) ∈ U := hx'U
      have hmem : (⟨u * (x' : G) * u⁻¹, U.mul_mem (U.mul_mem hu hx'U) (U.inv_mem hu)⟩ :
          ↥U) ∈ N₁ := by
        rw [Subgroup.mem_comap]
        have hx'N : πU x' ∈ N := Subgroup.mem_comap.mp hx'
        have hcomm : πU ⟨u * (x' : G) * u⁻¹,
            U.mul_mem (U.mul_mem hu hx'U) (U.inv_mem hu)⟩ =
            πU ⟨u, hu⟩ * πU x' * (πU ⟨u, hu⟩)⁻¹ := by
          rw [show (⟨u * (x' : G) * u⁻¹,
            U.mul_mem (U.mul_mem hu hx'U) (U.inv_mem hu)⟩ : ↥U) =
            ⟨u, hu⟩ * x' * (⟨u, hu⟩)⁻¹ from rfl]
          simp only [map_mul, map_inv]
        rw [hcomm]
        have huK : πU ⟨u, hu⟩ ∈ K := by
          rw [← hπU_range]
          exact MonoidHom.mem_range.mpr ⟨⟨u, hu⟩, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp (hKN huK) (πU x')).mp hx'N
      exact Subgroup.mem_map.mpr ⟨⟨u * (x' : G) * u⁻¹,
        U.mul_mem (U.mul_mem hu hx'U) (U.inv_mem hu)⟩, hmem, rfl⟩
    have hN₁K : t.Ky ≤ Subgroup.normalizer ((N₁.map U.subtype : Subgroup G) : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro b hb x hx
      obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
      have hx'U : (x' : G) ∈ U := x'.2
      have hconjU : (b : G) * (x' : G) * (b : G)⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp (hUK hb) (x' : G)).mp hx'U
      have hmem : (⟨(b : G) * (x' : G) * (b : G)⁻¹, hconjU⟩ : ↥U) ∈ N₁ := by
        rw [Subgroup.mem_comap]
        have hx'N : πU x' ∈ N := Subgroup.mem_comap.mp hx'
        have hcomm : πU ⟨(b : G) * (x' : G) * (b : G)⁻¹, hconjU⟩ =
            πS ⟨(b : G), hKS hb⟩ * πU x' * (πS ⟨(b : G), hKS hb⟩)⁻¹ := by
          show πS ⟨(b : G) * (x' : G) * (b : G)⁻¹, hUS hconjU⟩ = _
          rw [show (⟨(b : G) * (x' : G) * (b : G)⁻¹, hUS hconjU⟩ : ↥S) =
            ⟨(b : G), hKS hb⟩ * ⟨(x' : G), hUS x'.2⟩ * (⟨(b : G), hKS hb⟩)⁻¹ from rfl]
          simp only [map_mul, map_inv]
          rfl
        rw [hcomm]
        have hbA : πS ⟨(b : G), hKS hb⟩ ∈ A :=
          Subgroup.mem_map.mpr ⟨_, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp (hAN hbA) (πU x')).mp hx'N
      exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
    by_cases hU' : N₁.map U.subtype = U
    · right
      have hN₁top : N₁ = ⊤ := by
        have h := Subgroup.comap_map_eq_self_of_injective U.subtype_injective N₁
        rw [hU'] at h
        rw [← h, Subgroup.comap_subtype, Subgroup.subgroupOf_self]
      rw [← hNmap, hN₁top, Subgroup.map_top, hπU_range]
    · left
      have hWmax' := hWmax (N₁.map U.subtype) (by
          rw [← Subgroup.map_subgroupOf_eq_of_le hWle]
          exact Subgroup.map_mono hWN₁) (Subgroup.map_subtype_le N₁)
          hN₁U hN₁K hU'
      have hN₁W : N₁ = W.subgroupOf U := by
        have h := Subgroup.comap_map_eq_self_of_injective U.subtype_injective N₁
        rw [hWmax'] at h
        rw [← h]
        rfl
      rw [← hNmap, hN₁W]
      refine (Subgroup.eq_bot_iff_forall _).mpr ?_
      intro y hy
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy
      rw [hπU_eq]
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_subgroupOf.mp hw))
  have hAS : CFSG.SignalizerFunctorTheorem.Nonsolvable.IsASimple A K :=
    ⟨hnormKi, hnonabK, hmin⟩
  have hgen : ∀ B : Subgroup Γ, B ≤ A → A ≤ Subgroup.normalizer (B : Set Γ) →
      zbar ∈ B → B = A := by
    intro B hBA hAB hzB
    let Msub : Subgroup ↥S := B.comap πS ⊓ t.Ky.subgroupOf S
    have hMsub_le : Msub ≤ t.Ky.subgroupOf S := inf_le_right
    let M : Subgroup G := Msub.map S.subtype
    have hMK : M ≤ t.Ky := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact Subgroup.mem_subgroupOf.mp (hMsub_le hy)
    have hzM : z ∈ M := by
      have hzMsub : (⟨z, hzS⟩ : ↥S) ∈ Msub := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · rw [Subgroup.mem_comap]
          exact hzB
        · exact Subgroup.mem_subgroupOf.mpr (t.Z_le_Ky hzZ)
      exact Subgroup.mem_map.mpr ⟨_, hzMsub, rfl⟩
    have hMy : t.Ky ≤ Subgroup.normalizer (M : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro b hb x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      have hyKy : (y : G) ∈ t.Ky := hMsub_le hy
      have hconjKy : b * (y : G) * b⁻¹ ∈ t.Ky :=
        t.Ky.mul_mem (t.Ky.mul_mem hb hyKy) (t.Ky.inv_mem hb)
      have hconjS : b * (y : G) * b⁻¹ ∈ S := hKS hconjKy
      have hmemMsub : (⟨b * (y : G) * b⁻¹, hconjS⟩ : ↥S) ∈ Msub := by
        refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_subgroupOf.mpr hconjKy⟩
        rw [Subgroup.mem_comap]
        have hyB : πS y ∈ B := Subgroup.mem_comap.mp hy.1
        have hbA : πS ⟨b, hKS hb⟩ ∈ A :=
          Subgroup.mem_map.mpr ⟨_, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
        have hcomm : πS ⟨b * (y : G) * b⁻¹, hconjS⟩ =
            πS ⟨b, hKS hb⟩ * πS y * (πS ⟨b, hKS hb⟩)⁻¹ := by
          rw [show (⟨b * (y : G) * b⁻¹, hconjS⟩ : ↥S) =
            ⟨b, hKS hb⟩ * y * (⟨b, hKS hb⟩)⁻¹ from rfl]
          simp only [map_mul, map_inv]
        rw [hcomm]
        exact (Subgroup.mem_normalizer_iff.mp (hAB hbA) (πS y)).mp hyB
      exact Subgroup.mem_map.mpr ⟨_, hmemMsub, rfl⟩
    have hMN : ¬ M ≤ t.d.N := by
      intro hle
      have hzN : z ∈ t.d.N := hle hzM
      have h3dvd : 3 ∣ Nat.card t.d.N := by
        have h := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hzN)
        rwa [Nat.card_zpowers,
          orderOf_eq_prime (t.d.isElemAbelian_AA.2 z (t.Z_le_AA hzZ)) hz1] at h
      exact t.three_not_dvd_N h3dvd
    rcases t.le_N_or_eq_Ky hK32 hGA hSp hMK hMy with hle | heq
    · exact absurd hle hMN
    · refine le_antisymm hBA ?_
      intro a ha
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
      have hbKy : (b : G) ∈ t.Ky := Subgroup.mem_subgroupOf.mp hb
      have hbM : (b : G) ∈ M := by rw [heq]; exact hbKy
      obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp hbM
      have hyb' : y = b := Subtype.ext hyb
      subst hyb'
      exact Subgroup.mem_comap.mp hy.1
  have hKS : CFSG.Open.IsKGroup ↥S := c.standing.kProper.isKGroup S hne
  have hKΓ : CFSG.Open.IsKGroup Γ := CFSG.Open.IsKGroup.quotient hKS (W.subgroupOf S)
  have hKK : CFSG.Open.IsKGroup ↥K := CFSG.Open.IsKGroup.subgroup hKΓ K
  have hOut : ∀ T ∈ CFSG.SignalizerFunctorTheorem.Nonsolvable.simpleComponents K,
      Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥T) := by
    intro T hT
    have hTle : T ≤ K := hT.1
    have hTsimple : IsSimpleGroup ↥T := hT.2.2.1
    have hTnonab : ∃ a b : ↥T, a * b ≠ b * a := by
      obtain ⟨x, hx, y, hy, hxy⟩ := hT.2.2.2
      exact ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩
    have hKT : CFSG.Open.IsKGroup ↥T := CFSG.Open.IsKGroup.subgroup hKΓ T
    have hcat : CFSG.Open.IsCatalogGroup ↥T :=
      CFSG.Open.IsKGroup.isCatalogGroup_of_surjective hKT ⊤ hTnonab
        (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥T) ≃* ↥T).toMonoidHom
        (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥T) ≃* ↥T).surjective
    exact hSch ↥T hTsimple hTnonab hcat
  have hH₀U : H₀ ≤ U := sup_le inf_le_left hWle
  have hH₀S : H₀ ≤ S := hH₀U.trans hUS
  have hK₀le : K₀ ≤ K := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hxH : (x : G) ∈ H₀ := Subgroup.mem_subgroupOf.mp hx
    exact Subgroup.mem_map.mpr ⟨x, Subgroup.mem_subgroupOf.mpr (hH₀U hxH), rfl⟩
  have hH₀norm : t.Ky ≤ Subgroup.normalizer (H₀ : Set G) := by
    intro b hb
    have hbU : b ∈ Subgroup.normalizer (U : Set G) := hUK hb
    have hbM : b ∈ Subgroup.normalizer (c.S.M : Set G) :=
      Subgroup.le_normalizer (c.hyp81.1 (t.Ky_le hb).1)
    have hbInf : b ∈ Subgroup.normalizer ((U ⊓ c.S.M : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf (H := (U : Subgroup G)) (K := c.S.M)
        (Subgroup.mem_inf.mpr ⟨hbU, hbM⟩)
    have hbW : b ∈ Subgroup.normalizer (W : Set G) := hWK hb
    have hH₀eq : H₀ = (U ⊓ c.S.M) ⊔ W := rfl
    rw [hH₀eq]
    exact Subgroup.inf_normalizer_le_normalizer_sup _ _ (Subgroup.mem_inf.mpr ⟨hbInf, hbW⟩)
  have hK₀A : A ≤ Subgroup.normalizer (K₀ : Set Γ) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha y hy
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hbKy : (b : G) ∈ t.Ky := Subgroup.mem_subgroupOf.mp hb
    have hxH : (x : G) ∈ H₀ := Subgroup.mem_subgroupOf.mp hx
    have hconjH : (b : G) * (x : G) * (b : G)⁻¹ ∈ H₀ :=
      (Subgroup.mem_normalizer_iff.mp (hH₀norm hbKy) (x : G)).mp hxH
    refine Subgroup.mem_map.mpr ⟨⟨(b : G) * (x : G) * (b : G)⁻¹, hH₀S hconjH⟩,
      Subgroup.mem_subgroupOf.mpr hconjH, ?_⟩
    show πS ⟨(b : G) * (x : G) * (b : G)⁻¹, hH₀S hconjH⟩ = πS b * πS x * (πS b)⁻¹
    rw [show (⟨(b : G) * (x : G) * (b : G)⁻¹, hH₀S hconjH⟩ : ↥S) = b * x * b⁻¹ from rfl]
    simp only [map_mul, map_inv]
  have hfix : ∀ a ∈ A, K ⊓ Subgroup.centralizer ({a * zbar * a⁻¹} : Set Γ) ≤ K₀ := by
    intro a ha k hk
    obtain ⟨hkK, hkC⟩ := Subgroup.mem_inf.mp hk
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hkK
    have hbKy : (b : G) ∈ t.Ky := Subgroup.mem_subgroupOf.mp hb
    have huU : (u : G) ∈ U := Subgroup.mem_subgroupOf.mp hu
    have hcent : (πS b * zbar * (πS b)⁻¹) * πS u = πS u * (πS b * zbar * (πS b)⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp hkC) _ rfl
    have hzbar_eq : zbar = πS ⟨z, hzS⟩ := rfl
    have hone : πS (b * ⟨z, hzS⟩ * b⁻¹ * u * (b * ⟨z, hzS⟩ * b⁻¹)⁻¹ * u⁻¹) = 1 := by
      have hval : πS (b * ⟨z, hzS⟩ * b⁻¹ * u * (b * ⟨z, hzS⟩ * b⁻¹)⁻¹ * u⁻¹) =
          (πS b * πS ⟨z, hzS⟩ * (πS b)⁻¹) * πS u *
            (πS b * πS ⟨z, hzS⟩ * (πS b)⁻¹)⁻¹ * (πS u)⁻¹ := by
        rw [show (b * ⟨z, hzS⟩ * b⁻¹ * u * (b * ⟨z, hzS⟩ * b⁻¹)⁻¹ * u⁻¹ : ↥S) =
            (b * ⟨z, hzS⟩ * b⁻¹) * u * (b * ⟨z, hzS⟩ * b⁻¹)⁻¹ * u⁻¹ from rfl]
        simp only [map_mul, map_inv]
      rw [hval]
      rw [hzbar_eq] at hcent
      rw [hcent]
      group
    have hWmem : (b * ⟨z, hzS⟩ * b⁻¹ * u * (b * ⟨z, hzS⟩ * b⁻¹)⁻¹ * u⁻¹) ∈
        W.subgroupOf S := (QuotientGroup.eq_one_iff _).mp hone
    have hGmem : (b : G) * z * (b : G)⁻¹ * (u : G) * ((b : G) * z * (b : G)⁻¹)⁻¹ *
        (u : G)⁻¹ ∈ W := Subgroup.mem_subgroupOf.mp hWmem
    have hq0 : (u : G)⁻¹ * ((b : G) * z * (b : G)⁻¹ * (u : G) *
        ((b : G) * z * (b : G)⁻¹)⁻¹) ∈ W :=
      inv_mul_conj_mem_of_mul_conj_mem (hWU huU) (by simpa only [mul_assoc] using hGmem)
    have hq : ∀ x ∈ t.Z, (u : G)⁻¹ * ((b : G) * x * (b : G)⁻¹) * (u : G) *
        ((b : G) * x * (b : G)⁻¹)⁻¹ ∈ W :=
      t.forall_fixed_of_fixed hWK hWU hbKy hzZ hz1 huU (by simpa only [mul_assoc] using hq0)
    have hsup := t.mem_sup_inf_of_fixed hZ hFW hWle hWU hWK hbKy huU hq
    have huH : (u : G) ∈ H₀ := by
      have : H₀ = (U ⊓ c.S.M) ⊔ W := rfl
      rw [this]
      exact hsup
    exact Subgroup.mem_map.mpr ⟨⟨(u : G), hH₀S huH⟩, Subgroup.mem_subgroupOf.mpr huH, rfl⟩
  have hK₀eq : K₀ = K :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.IsASimple.eq_of_centralizers_le hAS hK3 hzA
      hzbarord hperfA hgen hOut hK₀le hK₀A hfix
  intro u hu
  have huS : u ∈ S := hUS hu
  have hmemK : πS ⟨u, huS⟩ ∈ K :=
    Subgroup.mem_map.mpr ⟨⟨u, huS⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
  rw [← hK₀eq] at hmemK
  obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hmemK
  have hxH : (x : G) ∈ H₀ := Subgroup.mem_subgroupOf.mp hx
  have hmemW : (x : G)⁻¹ * u ∈ W := by
    have h1 : πS (x⁻¹ * ⟨u, huS⟩) = 1 := by
      rw [map_mul, map_inv, hxeq]
      group
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
  have huH : u ∈ H₀ := by
    have heq : u = (x : G) * ((x : G)⁻¹ * u) := by group
    rw [heq]
    refine H₀.mul_mem hxH ?_
    rw [show H₀ = (U ⊓ c.S.M) ⊔ W from rfl]
    exact (le_sup_right : W ≤ (U ⊓ c.S.M) ⊔ W) hmemW
  exact huH


theorem exists_vStar (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) (hO : ¬ t.Oz ≤ c.S.M) :
    ∃ (r : ℕ) (U W : Subgroup G), r.Prime ∧ r ≠ 3 ∧
      CFSG.ABGLocalTools.IsChiefFactorUnder r t.Ky U W ∧ U ≤ t.Oz ∧ W ≤ c.S.M ∧
      U ⊓ c.S.M ≤ W ∧ ∀ u ∈ U, (∀ x ∈ t.Z, x * u * x⁻¹ * u⁻¹ ∈ W) → u ∈ W := by
  classical
  obtain ⟨U, hUle, hUK, hUnotM, hUmin⟩ := t.exists_minimal_U hK32 hGA hSp hO
  have hUbot : U ≠ ⊥ := by
    intro h
    exact hUnotM (h ▸ bot_le)
  obtain ⟨W, hWle, hWU, hWK, hWne, hWmax⟩ := t.exists_maximal_W (U := U) hUbot
  have hWM : W ≤ c.S.M := by
    by_contra hWnotM
    have hcard₁ : Nat.card U ≤ Nat.card W := hUmin W (hWle.trans hUle) hWK hWnotM
    have hcard₂ : Nat.card W ≤ Nat.card U :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hWle)
    exact hWne (Subgroup.eq_of_le_of_card_ge hWle hcard₁)
  have hU3 : ¬ 3 ∣ Nat.card U :=
    fun h => t.three_not_dvd_Oz (h.trans (Subgroup.card_dvd_of_le hUle))
  have hne : U ⊔ t.Ky ≠ ⊤ := by
    have hSleX : U ⊔ t.Ky ≤ t.Xz :=
      sup_le (hUle.trans t.Oz_le_Xz) (t.Ky_le_Xz hK32 hGA hSp)
    intro htop
    haveI : IsSimpleGroup G := c.standing.simple
    have hcent : Subgroup.centralizer ({t.y} : Set G) = ⊤ :=
      top_le_iff.mp (htop ▸ hSleX.trans t.Xz_le_centralizer)
    have hy : t.y ∈ Subgroup.center G :=
      Subgroup.centralizer_eq_top_iff_subset.mp hcent (Set.mem_singleton t.y)
    rw [CFSG.SignalizerFunctorTheorem.Diagonal.center_eq_bot c.standing.nonab,
      Subgroup.mem_bot] at hy
    simpa [hy] using t.orderOf_y
  have hcommU : ⁅U, U⁆ ≤ W := by
    by_contra hcon
    have hle := t.le_inf_sup_of_commutator_not_le hK32 hGA hSp hSch hZ hU3 hne hUK hWle
      hWne hWU hWK hWmax hcon
    exact hUnotM (hle.trans (sup_le inf_le_right hWM))
  have hNX : ∀ X : Subgroup G, W ≤ X → X ≤ U → U ≤ Subgroup.normalizer (X : Set G) := by
    intro X hWX hXU
    rw [Subgroup.le_normalizer_iff]
    intro u hu x hx
    have hc : ⁅u, x⁆ ∈ W := (Subgroup.commutator_le.mp hcommU) u hu x (hXU hx)
    have hux : u * x * u⁻¹ = ⁅u, x⁆ * x := by
      rw [commutatorElement_def]
      group
    rw [hux]
    exact X.mul_mem (hWX hc) hx
  have hKyInf : t.Ky ≤ Subgroup.normalizer ((U ⊓ c.S.M : Subgroup G) : Set G) := by
    intro b hb
    exact Subgroup.inf_normalizer_le_normalizer_inf (H := (U : Subgroup G)) (K := c.S.M)
      (Subgroup.mem_inf.mpr ⟨hUK hb, Subgroup.le_normalizer (c.hyp81.1 (t.Ky_le hb).1)⟩)
  have hKySupW : t.Ky ≤ Subgroup.normalizer (((U ⊓ c.S.M) ⊔ W : Subgroup G) : Set G) :=
    fun b hb => Subgroup.inf_normalizer_le_normalizer_sup _ _
      (Subgroup.mem_inf.mpr ⟨hKyInf hb, hWK hb⟩)
  have hUMleW : U ⊓ c.S.M ≤ W := by
    have hXle : (U ⊓ c.S.M) ⊔ W ≤ U := sup_le inf_le_left hWle
    have hXne : (U ⊓ c.S.M) ⊔ W ≠ U := by
      intro h
      apply hUnotM
      rw [← h]
      exact sup_le inf_le_right hWM
    have hXeq : (U ⊓ c.S.M) ⊔ W = W :=
      hWmax ((U ⊓ c.S.M) ⊔ W) le_sup_right hXle (hNX _ le_sup_right hXle) hKySupW hXne
    rw [← hXeq]
    exact le_sup_left
  haveI hWUnormal : (W.subgroupOf U).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWle).mpr hWU
  have hWsub_ne_top : W.subgroupOf U ≠ ⊤ := by
    intro htop
    apply hWne
    rw [← Subgroup.map_subgroupOf_eq_of_le hWle, htop, Subgroup.map_top, Subgroup.range_subtype]
  have hqne : Nat.card (↥U ⧸ (W.subgroupOf U)) ≠ 1 := by
    intro h
    apply hWsub_ne_top
    have hcard : Nat.card ↥(W.subgroupOf U) = Nat.card ↥U := by
      have hcm := Subgroup.card_mul_index (W.subgroupOf U)
      rw [Subgroup.index_eq_card, h, mul_one] at hcm
      exact hcm
    exact Subgroup.eq_top_of_card_eq (W.subgroupOf U) hcard
  obtain ⟨r, hprime, hdvd⟩ := Nat.exists_prime_and_dvd hqne
  have h3Q : ¬ 3 ∣ Nat.card (↥U ⧸ (W.subgroupOf U)) := by
    rw [← Subgroup.index_eq_card]
    have hcm := Subgroup.card_mul_index (W.subgroupOf U)
    have hdvd₂ : (W.subgroupOf U).index ∣ Nat.card ↥U :=
      ⟨Nat.card ↥(W.subgroupOf U), by rw [Nat.mul_comm]; exact hcm.symm⟩
    intro h3
    exact t.three_not_dvd_Oz ((h3.trans hdvd₂).trans (Subgroup.card_dvd_of_le hUle))
  have hr3 : r ≠ 3 := by
    intro h
    exact h3Q (h ▸ hdvd)
  have hQcomm : IsMulCommutative (↥U ⧸ (W.subgroupOf U)) := by
    refine isMulCommutative_iff.mpr fun a b => ?_
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective (s := W.subgroupOf U) a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective (s := W.subgroupOf U) b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hmem : ⁅b'⁻¹, a'⁻¹⁆ ∈ W.subgroupOf U := by
      rw [Subgroup.mem_subgroupOf]
      have hval : ((⁅b'⁻¹, a'⁻¹⁆ : ↥U) : G) = ⁅(b' : G)⁻¹, (a' : G)⁻¹⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        push_cast
        rfl
      rw [hval]
      exact hcommU (Subgroup.commutator_mem_commutator
        (Subgroup.inv_mem U b'.2) (Subgroup.inv_mem U a'.2))
    have hcomm : (a' * b')⁻¹ * (b' * a') = ⁅b'⁻¹, a'⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [hcomm]
    exact hmem
  let T : Subgroup (↥U ⧸ (W.subgroupOf U)) :=
    { carrier := {q | q ^ r = 1},
      one_mem' := by simp,
      mul_mem' := by
        intro a b ha hb
        have hc : Commute a b := isMulCommutative_iff.mp hQcomm a b
        show (a * b) ^ r = 1
        rw [hc.mul_pow, ha, hb, mul_one],
      inv_mem' := by
        intro a ha
        show a⁻¹ ^ r = 1
        rw [inv_pow, ha, inv_one] }
  let XU : Subgroup ↥U := T.comap (QuotientGroup.mk' (W.subgroupOf U))
  let X : Subgroup G := XU.map U.subtype
  have hWX : W ≤ X := by
    intro w hw
    refine Subgroup.mem_map.mpr ⟨⟨w, hWle hw⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
    rw [show (QuotientGroup.mk' (W.subgroupOf U)) ⟨w, hWle hw⟩ = 1 from
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hw)]
    exact T.one_mem
  have hXU : X ≤ U := Subgroup.map_subtype_le XU
  have hKX : t.Ky ≤ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    have hmemT : (QuotientGroup.mk' (W.subgroupOf U)) u ∈ T := Subgroup.mem_comap.mp hu
    have hupow : (u : G) ^ r ∈ W := by
      have h1 : ((QuotientGroup.mk' (W.subgroupOf U)) u) ^ r = 1 := hmemT
      rw [← map_pow] at h1
      exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
    have hconjU : (b : G) * (u : G) * b⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hUK hb) (u : G)).mp u.2
    refine Subgroup.mem_map.mpr ⟨⟨(b : G) * (u : G) * b⁻¹, hconjU⟩,
      Subgroup.mem_comap.mpr ?_, rfl⟩
    have hpow : ((b : G) * (u : G) * b⁻¹) ^ r ∈ W := by
      have hconj : (b * (u : G) * b⁻¹) ^ r = b * (u : G) ^ r * b⁻¹ := by
        rw [show b * (u : G) * b⁻¹ = (MulAut.conj b) (u : G) from
          (MulAut.conj_apply b (u : G)).symm, ← map_pow, MulAut.conj_apply]
      rw [hconj]
      exact (Subgroup.mem_normalizer_iff.mp (hWK hb) _).mp hupow
    show ((QuotientGroup.mk' (W.subgroupOf U)) ⟨(b : G) * (u : G) * b⁻¹, hconjU⟩) ^ r = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hpow)
  haveI : Fact r.Prime := ⟨hprime⟩
  obtain ⟨q, hqord⟩ := exists_prime_orderOf_dvd_card' r hdvd
  have hq_ne : q ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hqord
    exact hprime.ne_one hqord.symm
  obtain ⟨u₀, hu₀⟩ := QuotientGroup.mk_surjective (s := W.subgroupOf U) q
  have hu₀pow : ((QuotientGroup.mk' (W.subgroupOf U)) u₀) ^ r = 1 := by
    have hqpow : q ^ r = 1 := by
      rw [← hqord]
      exact pow_orderOf_eq_one q
    have h := congrArg (fun z => z ^ r) hu₀.symm
    rw [hqpow] at h
    simpa using h.symm
  have hu₀W : (u₀ : G) ∉ W := by
    intro hmem
    apply hq_ne
    rw [← hu₀, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hmem
  have hXne : X ≠ W := by
    intro h
    have hu₀X : (u₀ : G) ∈ X :=
      Subgroup.mem_map.mpr ⟨u₀, Subgroup.mem_comap.mpr hu₀pow, rfl⟩
    rw [h] at hu₀X
    exact hu₀W hu₀X
  have hXeqU : X = U := by
    by_cases hXU' : X = U
    · exact hXU'
    · exact absurd (hWmax X hWX hXU (hNX X hWX hXU) hKX hXU') hXne
  have hexp : ∀ u ∈ U, u ^ r ∈ W := by
    intro u hu
    have huX : u ∈ X := by rw [hXeqU]; exact hu
    obtain ⟨u', hu', hu'eq⟩ := Subgroup.mem_map.mp huX
    have hmemT : (QuotientGroup.mk' (W.subgroupOf U)) u' ∈ T := Subgroup.mem_comap.mp hu'
    have h1 : ((QuotientGroup.mk' (W.subgroupOf U)) u') ^ r = 1 := hmemT
    rw [← map_pow] at h1
    have hWu' : (u' : G) ^ r ∈ W :=
      Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
    rwa [← hu'eq]
  have hchief : CFSG.ABGLocalTools.IsChiefFactorUnder r t.Ky U W := by
    refine ⟨lt_of_le_of_ne hWle hWne, hUK, hWK, ?_, ?_, ?_, ?_⟩
    · intro x hx y hy
      exact (Subgroup.mem_normalizer_iff.mp (hWU hx) y).mp hy
    · intro x hx y hy
      exact (Subgroup.commutator_le.mp hcommU) x hx y hy
    · exact hexp
    · intro Y hWY hYU hKY
      by_cases hYU' : Y = U
      · exact Or.inr hYU'
      · exact Or.inl (hWmax Y hWY hYU (hNX Y hWY hYU) hKY hYU')
  refine ⟨r, U, W, hprime, hr3, hchief, hUle, hWM, hUMleW, ?_⟩
  intro u hu hcommZ
  have hq : ∀ x ∈ t.Z, u⁻¹ * ((1 : G) * x * (1 : G)⁻¹) * u *
      ((1 : G) * x * (1 : G)⁻¹)⁻¹ ∈ W := by
    intro x hx
    simpa only [one_mul, mul_one, inv_one, mul_assoc] using
      inv_mul_conj_mem_of_mul_conj_mem (hWU hu) (hcommZ x hx)
  have hW3 : ¬ 3 ∣ Nat.card W :=
    fun h => t.three_not_dvd_Oz (h.trans (Subgroup.card_dvd_of_le (hWle.trans hUle)))
  have hsup := t.mem_sup_inf_of_fixed hZ hW3 hWle hWU hWK (b := 1) t.Ky.one_mem hu hq
  have hsupW : (U ⊓ c.S.M) ⊔ W = W :=
    le_antisymm (sup_le hUMleW le_rfl) le_sup_right
  rwa [hsupW] at hsup

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
