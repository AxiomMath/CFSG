module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.ReeThreeAut
import CFSG.Quasithin.EmptyFaithful.R3c9Alt4
import CFSG.Sporadic.Recognition.LyonsAS44Gen
public import CFSG.Adapters.LinearCatalog
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72

open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (IsReeType)
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X]

theorem nonempty_mulEquiv_prod_psl23_of_card_24 {C U : Subgroup X} {t σ : X}
    (hC : Nat.card C = 24) (hUC : U ≤ C) (hU : Nat.card U = 8) (hU2 : ∀ u ∈ U, u * u = 1)
    (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (htU : t ∈ U) (ht1 : t ≠ 1)
    (htC : ∀ c ∈ C, c * t = t * c) (hσC : σ ∈ C) (hσ3 : orderOf σ = 3)
    (hσU : ∀ u ∈ U, σ * u * σ⁻¹ ∈ U) (hne : ∃ u ∈ U, σ * u * σ⁻¹ ≠ u) :
    Nonempty (↥C ≃* Multiplicative (ZMod 2) × PSL(2, ZMod 3)) := by
  classical
  have hσ3' : σ ^ 3 = 1 := by rw [← hσ3, pow_orderOf_eq_one]
  have hinv : ∀ u ∈ U, u⁻¹ = u := fun u hu => inv_eq_of_mul_eq_one_right (hU2 u hu)
  have hcube : ∀ y : X, σ * (σ * (σ * y * σ⁻¹) * σ⁻¹) * σ⁻¹ = y := fun y =>
    calc σ * (σ * (σ * y * σ⁻¹) * σ⁻¹) * σ⁻¹ = (σ * σ * σ) * y * (σ * σ * σ)⁻¹ := by
          simp only [mul_inv_rev, mul_assoc]
      _ = y := by rw [(pow_three' σ).symm.trans hσ3', inv_one, one_mul, mul_one]
  have htσ : σ * t * σ⁻¹ = t := by rw [htC σ hσC, mul_inv_cancel_right]
  let ψ : ↥U →* ↥U := MonoidHom.mk' (fun u => u * ⟨σ * u * σ⁻¹, hσU u u.2⟩) (by
    intro a b
    apply Subtype.ext
    have hab := hUc b b.2 (σ * a * σ⁻¹) (hσU a a.2)
    show (a : X) * b * (σ * (a * b) * σ⁻¹) = a * (σ * a * σ⁻¹) * (b * (σ * b * σ⁻¹))
    calc (a : X) * b * (σ * (a * b) * σ⁻¹) = a * (b * (σ * a * σ⁻¹)) * (σ * b * σ⁻¹) := by group
      _ = a * ((σ * a * σ⁻¹) * b) * (σ * b * σ⁻¹) := by rw [hab]
      _ = a * (σ * a * σ⁻¹) * (b * (σ * b * σ⁻¹)) := by group)
  have hψ : ∀ u : ↥U, ((ψ u : ↥U) : X) = u * (σ * u * σ⁻¹) := fun u => rfl
  have hker : ∀ u : ↥U, u ∈ ψ.ker ↔ σ * u * σ⁻¹ = u := by
    intro u
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h' : (u : X) * (σ * u * σ⁻¹) = 1 := by rw [← hψ, h, Subgroup.coe_one]
      calc σ * u * σ⁻¹ = (u : X)⁻¹ := eq_inv_of_mul_eq_one_right h'
        _ = u := hinv u u.2
    · intro h
      apply Subtype.ext
      rw [hψ, h, Subgroup.coe_one]
      exact hU2 u u.2
  have hfpf : ∀ u : ↥U, σ * ((ψ u : ↥U) : X) * σ⁻¹ = ψ u → ψ u = 1 := by
    intro u h
    have hc := hUc u u.2 (σ * u * σ⁻¹) (hσU u u.2)
    rw [hψ] at h
    have h3 : σ * (u * (σ * u * σ⁻¹)) * σ⁻¹ =
        (σ * u * σ⁻¹) * (σ * (σ * u * σ⁻¹) * σ⁻¹) := by group
    rw [h3, hc] at h
    have h4 := hcube u
    rw [mul_left_cancel h] at h4
    apply Subtype.ext
    rw [hψ, h4, Subgroup.coe_one]
    exact hU2 u u.2
  have hψσ : ∀ (u : X) (hu : u ∈ U),
      ((ψ ⟨σ * u * σ⁻¹, hσU u hu⟩ : ↥U) : X) = σ * ((ψ ⟨u, hu⟩ : ↥U) : X) * σ⁻¹ := by
    intro u hu
    rw [hψ, hψ]
    group
  obtain ⟨u₀, hu₀, hσu₀⟩ := hne
  have hw1 : ψ ⟨u₀, hu₀⟩ ≠ 1 := fun h => hσu₀ ((hker _).mp h)
  have hr2 : Nat.card ψ.range ≠ 2 := by
    intro h2
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ψ.range)).mp h2
    have hw : (⟨ψ ⟨u₀, hu₀⟩, MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩ : ψ.range) ≠ 1 :=
      fun h => hw1 (congrArg Subtype.val h)
    have hw' :
        (⟨ψ ⟨σ * u₀ * σ⁻¹, hσU u₀ hu₀⟩, MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩ : ψ.range) ≠ 1 := by
      intro h
      apply hw1
      have h' : ((ψ ⟨σ * u₀ * σ⁻¹, hσU u₀ hu₀⟩ : ↥U) : X) = 1 :=
        congrArg (fun z : ψ.range => ((z : ↥U) : X)) h
      rw [hψσ u₀ hu₀] at h'
      apply Subtype.ext
      calc ((ψ ⟨u₀, hu₀⟩ : ↥U) : X) = σ⁻¹ * (σ * ((ψ ⟨u₀, hu₀⟩ : ↥U) : X) * σ⁻¹) * σ := by group
        _ = 1 := by rw [h']; group
    have heq := (hy _ hw).trans (hy _ hw').symm
    have h5 : σ * ((ψ ⟨u₀, hu₀⟩ : ↥U) : X) * σ⁻¹ = ψ ⟨u₀, hu₀⟩ := by
      rw [← hψσ u₀ hu₀]
      exact (congrArg (fun z : ψ.range => ((z : ↥U) : X)) heq).symm
    exact hw1 (hfpf _ h5)
  have hkr : Nat.card ψ.ker * Nat.card ψ.range = 8 := by
    rw [Subgroup.card_ker_mul_card_range, hU]
  have hk2 : 2 ≤ Nat.card ψ.ker := by
    have hne : ψ.ker ≠ ⊥ := by
      intro h
      have ht' : (⟨t, htU⟩ : ↥U) ∈ ψ.ker := (hker _).mpr htσ
      rw [h, Subgroup.mem_bot] at ht'
      exact ht1 (congrArg Subtype.val ht')
    exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  have hr1 : 2 ≤ Nat.card ψ.range := by
    have hne : ψ.range ≠ ⊥ := by
      intro h
      have hm : ψ ⟨u₀, hu₀⟩ ∈ ψ.range := MonoidHom.mem_range.mpr ⟨_, rfl⟩
      rw [h, Subgroup.mem_bot] at hm
      exact hw1 hm
    exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  have hr4 : Nat.card ψ.range = 4 := by
    obtain ⟨r, hr⟩ : ∃ r, Nat.card ψ.range = r := ⟨_, rfl⟩
    rw [hr] at hkr hr1 hr2 ⊢
    have hle : r ≤ 8 := Nat.le_of_dvd (by norm_num) (Dvd.intro_left _ hkr)
    interval_cases r <;> omega
  set W : Subgroup X := ψ.range.map U.subtype with hWdef
  have hW4 : Nat.card W = 4 := by
    rw [hWdef, Subgroup.card_map_of_injective U.subtype_injective, hr4]
  have hWU : W ≤ U := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  have hmemW : ∀ x : X, x ∈ W ↔ ∃ u : ↥U, ((ψ u : ↥U) : X) = x := by
    intro x
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hw
      exact ⟨u, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨ψ u, MonoidHom.mem_range.mpr ⟨u, rfl⟩, rfl⟩
  have hσW : ∀ w ∈ W, σ * w * σ⁻¹ ∈ W := by
    intro w hw
    obtain ⟨u, rfl⟩ := (hmemW w).mp hw
    exact (hmemW _).mpr ⟨⟨σ * u * σ⁻¹, hσU u u.2⟩, hψσ u u.2⟩
  have hWfix : ∀ w ∈ W, σ * w * σ⁻¹ = w → w = 1 := by
    intro w hw h
    obtain ⟨u, rfl⟩ := (hmemW w).mp hw
    exact congrArg Subtype.val (hfpf u h)
  have htW : t ∉ W := fun h => ht1 (hWfix t h htσ)
  have hσN : σ ∈ normalizer (W : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hσW h, fun hh => ?_⟩
    have h1 := hσW _ (hσW _ hh)
    rwa [hcube h] at h1
  set A : Subgroup X := W ⊔ zpowers σ with hAdef
  have hAN : A ≤ normalizer (W : Set X) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hσN)
  have hAC : A ≤ C := sup_le (hWU.trans hUC) (Subgroup.zpowers_le.mpr hσC)
  have hWA : W ≤ A := le_sup_left
  have hσA : σ ∈ A := (le_sup_right : zpowers σ ≤ A) (Subgroup.mem_zpowers σ)
  have htA : t ∉ A := by
    intro h
    rw [← SetLike.mem_coe, hAdef, Subgroup.coe_mul_of_right_le_normalizer_left W (zpowers σ)
      (Subgroup.zpowers_le.mpr hσN)] at h
    obtain ⟨w, hw, z, hz, hwz⟩ := Set.mem_mul.mp h
    have hzU : z ∈ U := by
      have hz' : z = w⁻¹ * t := by rw [← hwz]; group
      rw [hz']
      exact U.mul_mem (U.inv_mem (hWU hw)) htU
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hz1 : σ ^ n = 1 := by
      have h3 : (σ ^ n) ^ 3 = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hσ3', one_zpow]
      calc σ ^ n = σ ^ n * (σ ^ n * σ ^ n) := by rw [hU2 _ hzU, mul_one]
        _ = (σ ^ n) ^ 3 := (pow_three _).symm
        _ = 1 := h3
    rw [hz1, mul_one] at hwz
    exact htW (hwz ▸ hw)
  have hA12 : Nat.card A = 12 := by
    have h4 : 4 ∣ Nat.card A := by
      rw [← hW4]
      exact Subgroup.card_dvd_of_le hWA
    have h3 : 3 ∣ Nat.card A := by
      have h := Subgroup.card_dvd_of_le (le_sup_right : zpowers σ ≤ A)
      rwa [Nat.card_zpowers, hσ3] at h
    have h12 : 3 * 4 ∣ Nat.card A := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h4
    have h24 : Nat.card A ∣ 24 := by
      rw [← hC]
      exact Subgroup.card_dvd_of_le hAC
    have hne24 : Nat.card A ≠ 24 := by
      intro h
      have hAeq : A = C := Subgroup.eq_of_le_of_card_ge hAC (by rw [h, hC])
      exact htA (hAeq ▸ hUC htU)
    obtain ⟨m, hm⟩ := h12
    have hle := Nat.le_of_dvd (by norm_num) h24
    have hpos : 0 < Nat.card A := Nat.card_pos
    omega
  haveI hWnA : (W.subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff hWA).mpr fun h k hh hk =>
      (Subgroup.mem_normalizer_iff.mp (hAN hk) h).mp hh
  obtain ⟨eA⟩ := CFSG.Quasithin.R3c9.isAlt4_of_structure (W.subgroupOf A) ⟨σ, hσA⟩
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWA).toEquiv, hW4])
    (by rw [Subgroup.orderOf_mk, hσ3])
    (by
      intro w hw hw1 h
      apply hw1
      have h' : σ * (w : X) * σ⁻¹ = w := congrArg Subtype.val h
      exact Subtype.ext (hWfix _ hw h'))
    hA12
  have hA'12 : Nat.card (A.subgroupOf C) = 12 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv, hA12]
  have hidx2 : (A.subgroupOf C).index = 2 := by
    have h := Subgroup.card_mul_index (A.subgroupOf C)
    rw [hA'12, hC] at h
    omega
  haveI : (A.subgroupOf C).Normal := Subgroup.normal_of_index_eq_two hidx2
  have hq2 : Nat.card (↥C ⧸ A.subgroupOf C) = 2 := by
    rw [← Subgroup.index_eq_card, hidx2]
  have hZ2 : Nat.card ℤˣ = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
  let χ : ↥C →* ℤˣ :=
    (mulEquivOfPrimeCardEq (p := 2) hq2 hZ2).toMonoidHom.comp (QuotientGroup.mk' (A.subgroupOf C))
  have hχker : χ.ker = A.subgroupOf C := by
    ext c
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ (MulEquiv.injective _), QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have htCm : t ∈ C := hUC htU
  have hχt : χ ⟨t, htCm⟩ = -1 := by
    rcases Int.units_eq_one_or (χ ⟨t, htCm⟩) with h | h
    · exfalso
      have hk : (⟨t, htCm⟩ : ↥C) ∈ χ.ker := h
      rw [hχker] at hk
      exact htA hk
    · exact h
  have hcen : (⟨t, htCm⟩ : ↥C) ∈ Subgroup.center ↥C := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (htC g g.2)
  obtain ⟨eC⟩ := CFSG.Sporadic.Recognition.LyonsSims.nonempty_mulEquiv_prod_of_hom_neg_one hcen
    (Subtype.ext (hU2 t htU)) (fun h => ht1 (congrArg Subtype.val h)) χ hχt
  exact ⟨eC.trans (MulEquiv.prodCongr (MulEquiv.refl _)
    (((MulEquiv.subgroupCongr hχker).trans (Subgroup.subgroupOfEquivOfLe hAC)).trans
      (eA.trans CFSG.GorensteinWalter.psl2_three_equiv_alternatingGroup.symm)))⟩

theorem isReeType_one_of_psl28 (K : Subgroup X) (hKn : K.Normal)
    (hKc : Subgroup.centralizer (K : Set X) = ⊥)
    (hK : IsoLie ↥K (.A 1 ⟨2, 3, Nat.prime_two, by norm_num⟩)) (hidx : K.index = 3) :
    IsReeType X 1 := by
  haveI := hKn
  obtain ⟨hv, ⟨e₀⟩⟩ := hK
  have e : K ≃* PSL(2, GaloisField 2 3) :=
    e₀.trans (@CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 _ ⟨Nat.prime_two⟩ hv)
  obtain ⟨t, σ, hto, htK, hC24, hU8, hU2, hUc, hσC, hσ3, hne⟩ :=
    exists_involution_of_psl28 e hidx hKc
  have ht1 : t ≠ 1 := fun h => by simp [h] at hto
  refine ⟨odd_one, isMulCommutative_sylow_two_of_psl28 e hidx, t, hto, ZMod 3, inferInstance,
    inferInstance, ZMod.card 3, ?_⟩
  exact nonempty_mulEquiv_prod_psl23_of_card_24 hC24 inf_le_right hU8 hU2 hUc
    (Subgroup.mem_inf.mpr ⟨htK, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩) ht1
    (fun c hc => Subgroup.mem_centralizer_singleton_iff.mp hc) hσC hσ3
    (fun u hu => Subgroup.mem_inf.mpr ⟨hKn.conj_mem u (Subgroup.mem_inf.mp hu).1 σ,
      (centralizer _).mul_mem ((centralizer _).mul_mem hσC (Subgroup.mem_inf.mp hu).2)
        ((centralizer _).inv_mem hσC)⟩) hne

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72
