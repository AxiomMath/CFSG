module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndPhi
import CFSG.GroupTheory.IsCyclicOfLeOfPRankLeOne
import CFSG.Quasithin.Vol2.Ch4Sec2T425C27A
import CFSG.GroupTheory.PGroup.PrimePartTransport
import CFSG.GroupTheory.CentralizerMapMulEquiv
import CFSG.GroupTheory.PGroup.LtInfNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace A10Perm

open Equiv Equiv.Perm Subgroup
open CFSG.GH74.Uniqueness.SU.SU13.TA.L10

theorem mem_zpowers_of_support_eq {x y : Perm (Fin 10)} (hx : x ∈ atilde) (hy : y ∈ atilde)
    (hxs : x.support.card = 3) (hxy : y.support = x.support) : y ∈ Subgroup.zpowers x := by
  obtain ⟨i, j, k, rfl⟩ := mem_atilde_iff.mp hx
  obtain ⟨i', j', k', rfl⟩ := mem_atilde_iff.mp hy
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first
      | (exfalso; revert hxs; decide +kernel)
      | (fin_cases i' <;> fin_cases j' <;> fin_cases k' <;>
          first
            | (exfalso; revert hxy; decide +kernel)
            | exact Subgroup.mem_zpowers_iff.mpr ⟨1, by decide +kernel⟩
            | exact Subgroup.mem_zpowers_iff.mpr ⟨2, by decide +kernel⟩)


theorem map_conj_altOff (σ : Equiv.Perm (Fin 10)) (s : Finset (Fin 10)) :
    (altOff s).map (MulAut.conj σ).toMonoidHom = altOff (s.map σ.toEmbedding) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change σ * y * σ⁻¹ ∈ altOff (s.map σ.toEmbedding)
    change y ∈ altOff s at hy
    rw [mem_altOff_iff] at hy
    rw [mem_altOff_iff]
    refine ⟨(inferInstance : (alternatingGroup (Fin 10)).Normal).conj_mem y hy.1 σ, ?_⟩
    intro z hz
    rw [Finset.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    calc (σ * y * σ⁻¹) (σ w) = σ (y (σ⁻¹ (σ w))) := rfl
      _ = σ (y w) := by simp
      _ = σ w := by rw [hy.2 w hw]
  · intro hx
    refine ⟨σ⁻¹ * x * σ, ?_, ?_⟩
    · change σ⁻¹ * x * σ ∈ altOff s
      change x ∈ altOff (s.map σ.toEmbedding) at hx
      rw [mem_altOff_iff] at hx
      rw [mem_altOff_iff]
      refine ⟨(inferInstance : (alternatingGroup (Fin 10)).Normal).conj_mem x hx.1 σ⁻¹, ?_⟩
      intro z hz
      have hz' : σ z ∈ s.map σ.toEmbedding := Finset.mem_map.mpr ⟨z, hz, rfl⟩
      have h := hx.2 (σ z) hz'
      calc (σ⁻¹ * x * σ) z = σ⁻¹ (x (σ z)) := rfl
        _ = σ⁻¹ (σ z) := by rw [h]
        _ = z := by simp
    · show σ * (σ⁻¹ * x * σ) * σ⁻¹ = x
      group

end A10Perm


namespace Ctx82E3.A10Frame

variable {c : Ctx82E3 D}

private noncomputable def centralizerToM {a : G}
    (hCa : Subgroup.centralizer ({a} : Set G) ≤ D.M) :
    ↥(Subgroup.centralizer ({a} : Set G)) →* ↥D.M :=
  { toFun := fun x => ⟨x, hCa x.2⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }

private noncomputable def centralizerHom (F : A10Frame c) {a : G}
    (hCa : Subgroup.centralizer ({a} : Set G) ≤ D.M) :
    ↥(Subgroup.centralizer ({a} : Set G)) →* Equiv.Perm (Fin 10) :=
  F.phiA.comp (centralizerToM hCa)

private theorem A_le_centralizer_of_deg_three (F : A10Frame c) {a : G} (haA : a ∈ F.A) :
    F.A ≤ Subgroup.centralizer ({a} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  exact congrArg (fun z : ↥F.A => (z : G))
    (F.elemAbelian.1.is_comm.comm ⟨a, haA⟩ ⟨x, hx⟩)

private theorem coprime_card_ker_centralizerHom (F : A10Frame c) {a : G}
    (hCa : Subgroup.centralizer ({a} : Set G) ≤ D.M) :
    ¬ 3 ∣ Nat.card (centralizerHom F hCa).ker := by
  have hg_inj : Function.Injective (centralizerToM hCa) := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : ↥D.M => (z : G)) h)
  have hdvd : Nat.card (centralizerHom F hCa).ker ∣ Nat.card F.phiA.ker := by
    rw [show (centralizerHom F hCa).ker = Subgroup.comap (centralizerToM hCa) F.phiA.ker from
      (MonoidHom.comap_ker F.phiA (centralizerToM hCa)).symm]
    exact Subgroup.card_comap_dvd_of_injective F.phiA.ker (centralizerToM hCa) hg_inj
  have h3 : ¬ 3 ∣ Nat.card F.phiA.ker :=
    Nat.prime_three.coprime_iff_not_dvd.mp F.coprime_card_ker_phiA.symm
  exact fun h => h3 (h.trans hdvd)

private theorem range_centralizerHom_le (F : A10Frame c) {a : G}
    (hCa : Subgroup.centralizer ({a} : Set G) ≤ D.M) (haA : a ∈ F.A) :
    (centralizerHom F hCa).range ≤
      Subgroup.centralizer ({F.phiA ⟨a, F.A_le_M haA⟩} : Set (Equiv.Perm (Fin 10))) := by
  rintro _ ⟨x, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst hz
  have hxcomm : (x : G) * a = a * (x : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp x.2
  have hgxcomm : centralizerToM hCa x * ⟨a, F.A_le_M haA⟩ =
      ⟨a, F.A_le_M haA⟩ * centralizerToM hCa x := by
    apply Subtype.ext
    exact hxcomm
  calc F.phiA ⟨a, F.A_le_M haA⟩ * centralizerHom F hCa x =
        F.phiA ⟨a, F.A_le_M haA⟩ * F.phiA (centralizerToM hCa x) := rfl
    _ = F.phiA (⟨a, F.A_le_M haA⟩ * centralizerToM hCa x) := (map_mul _ _ _).symm
    _ = F.phiA (centralizerToM hCa x * ⟨a, F.A_le_M haA⟩) := by rw [hgxcomm]
    _ = F.phiA (centralizerToM hCa x) * F.phiA ⟨a, F.A_le_M haA⟩ := map_mul _ _ _
    _ = centralizerHom F hCa x * F.phiA ⟨a, F.A_le_M haA⟩ := rfl

private theorem isSylowOf_atilde_centralizer_phiA (F : A10Frame c) {a : G} (haA : a ∈ F.A)
    (ha3 : F.deg (Subgroup.zpowers a) = 3) :
    CFSG.ABGLocalTools.IsSylowOf 3 A10Perm.atilde
      (Subgroup.centralizer ({F.phiA ⟨a, F.A_le_M haA⟩} : Set (Equiv.Perm (Fin 10)))) := by
  have hφa_at : F.phiA ⟨a, F.A_le_M haA⟩ ∈ A10Perm.atilde := by
    rw [← F.map_A_phiA]
    exact Subgroup.mem_map_of_mem F.phiA (Subgroup.mem_subgroupOf.mpr haA)
  have hsuppa : (F.phiA ⟨a, F.A_le_M haA⟩).support.card = 3 := by
    rw [← F.deg_zpowers_eq (F.P_le_L (F.A_le haA)), ha3]
  exact A10Perm.isSylowOf_atilde hφa_at (Or.inl hsuppa)

private theorem factorization_card_centralizer_le (F : A10Frame c) (hF : A10Facts F) {a : G}
    (haA : a ∈ F.A) (ha3 : F.deg (Subgroup.zpowers a) = 3) :
    (Nat.card (Subgroup.centralizer ({a} : Set G))).factorization 3 ≤ 3 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hCa : Subgroup.centralizer ({a} : Set G) ≤ D.M :=
    F.centralizer_le_M_of_deg_three hF haA ha3
  have hker := coprime_card_ker_centralizerHom F hCa
  have hrange := range_centralizerHom_le F hCa haA
  have hfac_eq : (Nat.card ↥(centralizerHom F hCa).range).factorization 3 =
      (Nat.card ↥(Subgroup.centralizer ({a} : Set G))).factorization 3 := by
    have h := CFSG.GroupTheory.factorization_eq_of_surjective_ker_not_dvd
      (centralizerHom F hCa).rangeRestrict (centralizerHom F hCa).rangeRestrict_surjective
      (by rwa [MonoidHom.ker_rangeRestrict])
    simpa [MonoidHom.ker_rangeRestrict] using h
  rw [← hfac_eq]
  have hle : (Nat.card ↥(centralizerHom F hCa).range).factorization 3 ≤
      (Nat.card ↥(Subgroup.centralizer
        ({F.phiA ⟨a, F.A_le_M haA⟩} : Set (Equiv.Perm (Fin 10))))).factorization 3 :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
      (Subgroup.card_dvd_of_le hrange) 3
  refine hle.trans ?_
  have hcard := (isSylowOf_atilde_centralizer_phiA F haA ha3).card_eq
  rw [A10Perm.card_atilde] at hcard
  have hpow : 3 ^ (Nat.card ↥(Subgroup.centralizer
      ({F.phiA ⟨a, F.A_le_M haA⟩} : Set (Equiv.Perm (Fin 10))))).factorization 3 = 3 ^ 3 := by
    rw [← hcard]
    norm_num
  exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpow).le

theorem isSylowOf_A_centralizer_of_deg_three (F : A10Frame c) (hF : A10Facts F) {a : G}
    (haA : a ∈ F.A) (ha3 : F.deg (Subgroup.zpowers a) = 3) :
    CFSG.ABGLocalTools.IsSylowOf 3 F.A (Subgroup.centralizer ({a} : Set G)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAC := A_le_centralizer_of_deg_three F haA
  have hfac_le := factorization_card_centralizer_le F hF haA ha3
  have hfac_ge : 3 ≤ (Nat.card (Subgroup.centralizer ({a} : Set G))).factorization 3 := by
    have hdvd : 3 ^ 3 ∣ Nat.card (Subgroup.centralizer ({a} : Set G)) := by
      have h := Subgroup.card_dvd_of_le hAC
      rw [F.card_A] at h
      norm_num at h ⊢
      exact h
    exact (Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hdvd
  exact CFSG.ABGLocalTools.isSylowOf_of_card hAC
    (by rw [F.card_A, le_antisymm hfac_le hfac_ge]; norm_num)

private theorem card_centralizer_conj_eq {a h : G} :
    Nat.card (Subgroup.centralizer ({h * a * h⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({a} : Set G)) := by
  have hb : h * a * h⁻¹ = (MulAut.conj h) a := by rw [MulAut.conj_apply]
  rw [hb]
  exact (CFSG.GroupTheory.card_centralizer_singleton_mulEquiv (MulAut.conj h) a).symm

private theorem isSylowOf_centralizer_conj (F : A10Frame c) (hF : A10Facts F) {a h : G}
    (haA : a ∈ F.A) (ha3 : F.deg (Subgroup.zpowers a) = 3)
    (hhA : h * a * h⁻¹ ∈ F.A) :
    CFSG.ABGLocalTools.IsSylowOf 3 F.A
      (Subgroup.centralizer ({h * a * h⁻¹} : Set G)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.ABGLocalTools.isSylowOf_of_card
    (A_le_centralizer_of_deg_three F hhA) ?_
  rw [(F.isSylowOf_A_centralizer_of_deg_three hF haA ha3).card_eq,
    card_centralizer_conj_eq]

private theorem map_conj_le_centralizer (F : A10Frame c) {H : Subgroup G} (hAH : F.A ≤ H)
    {a h : G} (haA : a ∈ F.A) (hh : h ∈ H) (hhA : h * a * h⁻¹ ∈ F.A) :
    F.A.map (MulAut.conj h).toMonoidHom ≤
      H ⊓ Subgroup.centralizer ({h * a * h⁻¹} : Set G) := by
  refine le_inf ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    exact H.mul_mem (H.mul_mem hh (hAH hy)) (H.inv_mem hh)
  · rintro x ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyc : y * a = a * y := congrArg (fun z : ↥F.A => (z : G))
      (F.elemAbelian.1.is_comm.comm ⟨y, hy⟩ ⟨a, haA⟩)
    calc (h * y * h⁻¹) * (h * a * h⁻¹) = h * (y * a) * h⁻¹ := by group
      _ = h * (a * y) * h⁻¹ := by rw [hyc]
      _ = (h * a * h⁻¹) * (h * y * h⁻¹) := by group

private theorem isSylowOf_map_conj_centralizer (F : A10Frame c) (hF : A10Facts F)
    {H : Subgroup G} (hAH : F.A ≤ H) {a h : G} (haA : a ∈ F.A)
    (ha3 : F.deg (Subgroup.zpowers a) = 3) (hh : h ∈ H) (hhA : h * a * h⁻¹ ∈ F.A) :
    CFSG.ABGLocalTools.IsSylowOf 3 (F.A.map (MulAut.conj h).toMonoidHom)
      (Subgroup.centralizer ({h * a * h⁻¹} : Set G)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle := map_conj_le_centralizer F hAH haA hh hhA
  refine CFSG.ABGLocalTools.isSylowOf_of_card (hle.trans inf_le_right) ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj h).injective,
    (isSylowOf_centralizer_conj F hF haA ha3 hhA).card_eq]

private theorem mem_normalizer_of_sylow_conj (F : A10Frame c) {h k : G}
    (hkconj : ∀ x : G, x ∈ F.A.map (MulAut.conj h).toMonoidHom ↔
      k⁻¹ * x * k ∈ F.A) :
    k⁻¹ * h ∈ Subgroup.normalizer (F.A : Set G) := by
  have hmem_map_conj (u v : G) :
      u ∈ F.A.map (MulAut.conj v).toMonoidHom ↔ v⁻¹ * u * v ∈ F.A := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      change v⁻¹ * (v * y * v⁻¹) * v ∈ F.A
      have h : v⁻¹ * (v * y * v⁻¹) * v = y := by group
      rwa [h]
    · intro hu
      exact Subgroup.mem_map.mpr ⟨v⁻¹ * u * v, hu, by
        show v * (v⁻¹ * u * v) * v⁻¹ = u
        group⟩
  have hAh_eq : F.A.map (MulAut.conj h).toMonoidHom =
      F.A.map (MulAut.conj k).toMonoidHom := by
    ext x
    exact (hkconj x).trans (hmem_map_conj x k).symm
  have h1 (x : G) : h * x * h⁻¹ ∈ F.A.map (MulAut.conj h).toMonoidHom ↔ x ∈ F.A := by
    rw [hmem_map_conj (h * x * h⁻¹) h,
      show h⁻¹ * (h * x * h⁻¹) * h = x by group]
  have hkconj' (y : G) :
      y ∈ F.A.map (MulAut.conj k).toMonoidHom ↔ k⁻¹ * y * k ∈ F.A := by
    rw [← hAh_eq]
    exact hkconj y
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hstep1 : x ∈ F.A ↔ h * x * h⁻¹ ∈ F.A.map (MulAut.conj k).toMonoidHom := by
    rw [← hAh_eq]
    exact (h1 x).symm
  have hstep2 : h * x * h⁻¹ ∈ F.A.map (MulAut.conj k).toMonoidHom ↔
      k⁻¹ * (h * x * h⁻¹) * k ∈ F.A := hkconj' _
  rw [show k⁻¹ * (h * x * h⁻¹) * k =
    (k⁻¹ * h) * x * (k⁻¹ * h)⁻¹ by group] at hstep2
  exact hstep1.trans hstep2

theorem exists_mem_normalizer_conj_eq (F : A10Frame c) (hF : A10Facts F) {H : Subgroup G}
    (hAH : F.A ≤ H) {a : G} (haA : a ∈ F.A) (ha3 : F.deg (Subgroup.zpowers a) = 3)
    {h : G} (hh : h ∈ H) (hhA : h * a * h⁻¹ ∈ F.A) :
    ∃ n ∈ H ⊓ Subgroup.normalizer (F.A : Set G), n * a * n⁻¹ = h * a * h⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let b : G := h * a * h⁻¹
  have hbA : b ∈ F.A := hhA
  have hAK : F.A ≤ H ⊓ Subgroup.centralizer ({b} : Set G) :=
    le_inf hAH (A_le_centralizer_of_deg_three F hbA)
  have hAsyl_K := (isSylowOf_centralizer_conj F hF haA ha3 hhA).of_le hAK inf_le_right
  have hAh_syl_K := (isSylowOf_map_conj_centralizer F hF hAH haA ha3 hh hhA).of_le
    (map_conj_le_centralizer F hAH haA hh hhA) inf_le_right
  obtain ⟨k, hkK, hkconj⟩ := hAsyl_K.exists_mem_conj hAh_syl_K
  refine ⟨k⁻¹ * h, ⟨H.mul_mem (H.inv_mem hkK.1) hh,
    mem_normalizer_of_sylow_conj F hkconj⟩, ?_⟩
  have hkcent : k * b = b * k := Subgroup.mem_centralizer_singleton_iff.mp hkK.2
  calc (k⁻¹ * h) * a * (k⁻¹ * h)⁻¹ = k⁻¹ * (h * a * h⁻¹) * k := by group
    _ = k⁻¹ * (b * k) := by rw [show h * a * h⁻¹ = b from rfl]; group
    _ = k⁻¹ * (k * b) := by rw [← hkcent]
    _ = b := by group

theorem mem_zpowers_of_phiA_mem_zpowers (F : A10Frame c) {a b : G}
    (haA : a ∈ F.A) (hbA : b ∈ F.A)
    (h : F.phiA ⟨b, F.A_le_M hbA⟩ ∈
      Subgroup.zpowers (F.phiA ⟨a, F.A_le_M haA⟩)) :
    b ∈ Subgroup.zpowers a := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  have haM := F.A_le_M haA
  have hbM := F.A_le_M hbA
  have hakA : a ^ k ∈ F.A := F.A.zpow_mem haA k
  have hcA : b * (a ^ k)⁻¹ ∈ F.A := F.A.mul_mem hbA (F.A.inv_mem hakA)
  have hφc : F.phiA ⟨b * (a ^ k)⁻¹, F.A_le_M hcA⟩ = 1 := by
    have hsub : (⟨b * (a ^ k)⁻¹, F.A_le_M hcA⟩ : ↥D.M) =
        ⟨b, hbM⟩ * (⟨a, haM⟩ ^ k)⁻¹ := by
      apply Subtype.ext
      simp
    rw [hsub, map_mul, map_inv, map_zpow, hk]
    simp
  have hcc : (b * (a ^ k)⁻¹) ^ 3 = 1 := F.elemAbelian.2 _ hcA
  have hord3 : orderOf (b * (a ^ k)⁻¹) ∣ 3 := orderOf_dvd_of_pow_eq_one hcc
  have hordK : orderOf (b * (a ^ k)⁻¹) ∣ Nat.card F.phiA.ker := by
    have h := Subgroup.orderOf_dvd_natCard F.phiA.ker
      (x := (⟨b * (a ^ k)⁻¹, F.A_le_M hcA⟩ : ↥D.M)) hφc
    simpa using h
  have hone : orderOf (b * (a ^ k)⁻¹) = 1 :=
    Nat.eq_one_of_dvd_coprimes F.coprime_card_ker_phiA.symm hord3 hordK
  have hc1 : b * (a ^ k)⁻¹ = 1 := orderOf_eq_one_iff.mp hone
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, (mul_inv_eq_one.mp hc1).symm⟩

theorem two_le_pRank_inf_of_noncyclic_five (F : A10Frame c) {H : Subgroup G}
    {E : Subgroup (Equiv.Perm (Fin 10))} (hE5 : IsPGroup 5 E) (hEnc : ¬ IsCyclic E)
    (hE : E ≤ ((H ⊓ D.M).subgroupOf D.M).map F.phiA) :
    2 ≤ CFSG.Open.pRank 5 (H ⊓ D.M) := by
  classical
  let K : Subgroup G := H ⊓ D.M
  let K₀ : Subgroup ↥D.M := K.subgroupOf D.M
  have hKbar : 2 ≤ CFSG.Open.pRank 5 (K₀.map F.phiA) := by
    by_contra h
    have hle : CFSG.Open.pRank 5 (K₀.map F.phiA) ≤ 1 := by omega
    exact hEnc (CFSG.isCyclic_of_le_of_pRank_le_one (p := 5) (by norm_num) (by norm_num)
      hE5 hE hle)
  have hQ : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup ↥(K₀.map F.phiA)) := by
    rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (K₀.map F.phiA)]
  let f : ↥K₀ →* Equiv.Perm (Fin 10) := F.phiA.comp K₀.subtype
  have hrange : f.range = K₀.map F.phiA := by
    rw [show f = F.phiA.comp K₀.subtype from rfl, MonoidHom.range_comp,
      Subgroup.range_subtype]
  have hQ' : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup ↥f.range) := by
    rwa [hrange]
  have hK₀ : 2 ≤ CFSG.Open.pRank 5 K₀ :=
    CFSG.Quasithin.H13.Ch4.T425C27.two_le_pRank_of_surjective (p := 5)
      f.rangeRestrict f.rangeRestrict_surjective (by norm_num) hQ'
  have hK₀' : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup ↥K₀) := by
    rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup K₀]
  have heq : CFSG.Open.pRank 5 (⊤ : Subgroup ↥K) =
      CFSG.Open.pRank 5 (⊤ : Subgroup ↥K₀) :=
    (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 5) (by norm_num : 1 < 5)
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : K ≤ D.M))).symm
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup K, heq]
  exact hK₀'

private theorem phiA_conj_data (F : A10Frame c) {a b n : G}
    (haA : a ∈ F.A) (hbA : b ∈ F.A) (hnM : n ∈ D.M)
    (hna : n * a * n⁻¹ = b) (ha3 : F.deg (Subgroup.zpowers a) = 3) :
    (F.phiA ⟨b, F.A_le_M hbA⟩).support =
        Finset.map (Equiv.toEmbedding (F.phiA ⟨n, hnM⟩))
          (F.phiA ⟨a, F.A_le_M haA⟩).support ∧
      (F.phiA ⟨b, F.A_le_M hbA⟩).support.card = 3 ∧
      (F.phiA ⟨a, F.A_le_M haA⟩).support.card = 3 ∧
      F.phiA ⟨a, F.A_le_M haA⟩ ∈ A10Perm.atilde ∧
      F.phiA ⟨b, F.A_le_M hbA⟩ ∈ A10Perm.atilde := by
  have haM := F.A_le_M haA
  have haL : a ∈ c.L := F.P_le_L (F.A_le haA)
  have hφb_eq : F.phiA ⟨b, F.A_le_M hbA⟩ =
      F.phiA ⟨n, hnM⟩ * F.phiA ⟨a, haM⟩ * (F.phiA ⟨n, hnM⟩)⁻¹ := by
    have hsub : (⟨b, F.A_le_M hbA⟩ : ↥D.M) =
        ⟨n, hnM⟩ * ⟨a, haM⟩ * ⟨n, hnM⟩⁻¹ := by
      apply Subtype.ext
      exact hna.symm
    rw [hsub, map_mul, map_mul, map_inv]
  have hsuppa : (F.phiA ⟨a, haM⟩).support.card = 3 := by
    rw [← F.deg_zpowers_eq haL, ha3]
  have hsuppb : (F.phiA ⟨b, F.A_le_M hbA⟩).support.card = 3 := by
    rw [hφb_eq, Equiv.Perm.card_support_conj, ← F.deg_zpowers_eq haL, ha3]
  refine ⟨?_, hsuppb, hsuppa, ?_, ?_⟩
  · rw [hφb_eq, Equiv.Perm.support_conj]
  · rw [← F.map_A_phiA]
    exact Subgroup.mem_map_of_mem F.phiA (Subgroup.mem_subgroupOf.mpr haA)
  · rw [← F.map_A_phiA]
    exact Subgroup.mem_map_of_mem F.phiA (Subgroup.mem_subgroupOf.mpr hbA)

private theorem phiA_support_ne (F : A10Frame c) {a b n : G}
    (haA : a ∈ F.A) (hbA : b ∈ F.A) (hha : b ∉ Subgroup.zpowers a)
    (hnM : n ∈ D.M) (hna : n * a * n⁻¹ = b)
    (hφa_at : F.phiA ⟨a, F.A_le_M haA⟩ ∈ A10Perm.atilde)
    (hφb_at : F.phiA ⟨b, F.A_le_M hbA⟩ ∈ A10Perm.atilde)
    (hsuppa : (F.phiA ⟨a, F.A_le_M haA⟩).support.card = 3)
    (hsuppb_eq : (F.phiA ⟨b, F.A_le_M hbA⟩).support =
      Finset.map (Equiv.toEmbedding (F.phiA ⟨n, hnM⟩))
        (F.phiA ⟨a, F.A_le_M haA⟩).support) :
    (F.phiA ⟨b, F.A_le_M hbA⟩).support ≠ (F.phiA ⟨a, F.A_le_M haA⟩).support := by
  intro heq
  have hmem : F.phiA ⟨b, F.A_le_M hbA⟩ ∈
      Subgroup.zpowers (F.phiA ⟨a, F.A_le_M haA⟩) :=
    A10Perm.mem_zpowers_of_support_eq hφa_at hφb_at hsuppa heq
  exact hha (mem_zpowers_of_phiA_mem_zpowers F haA hbA hmem)

private theorem altOff_support_conj_le (F : A10Frame c) {H : Subgroup G} {a b n : G}
    (haA : a ∈ F.A) (hbA : b ∈ F.A) (hnH : n ∈ H) (hnM : n ∈ D.M)
    (haltA : A10Perm.altOff (F.phiA ⟨a, F.A_le_M haA⟩).support ≤
      ((H ⊓ D.M).subgroupOf D.M).map F.phiA)
    (hsuppb_eq : (F.phiA ⟨b, F.A_le_M hbA⟩).support =
      Finset.map (Equiv.toEmbedding (F.phiA ⟨n, hnM⟩))
        (F.phiA ⟨a, F.A_le_M haA⟩).support) :
    A10Perm.altOff (F.phiA ⟨b, F.A_le_M hbA⟩).support ≤
      ((H ⊓ D.M).subgroupOf D.M).map F.phiA := by
  let K₀ : Subgroup ↥D.M := (H ⊓ D.M).subgroupOf D.M
  have hK₀conj : K₀.map (MulAut.conj (⟨n, hnM⟩ : ↥D.M)).toMonoidHom = K₀ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change y ∈ K₀ at hy
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      exact ⟨H.mul_mem (H.mul_mem hnH hy.1) (H.inv_mem hnH),
        D.M.mul_mem (D.M.mul_mem hnM hy.2) (D.M.inv_mem hnM)⟩
    · intro hx
      change x ∈ K₀ at hx
      rw [Subgroup.mem_subgroupOf] at hx
      refine Subgroup.mem_map.mpr ⟨⟨n, hnM⟩⁻¹ * x * ⟨n, hnM⟩, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf]
        exact ⟨H.mul_mem (H.mul_mem (H.inv_mem hnH) hx.1) hnH,
          D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hnM) hx.2) hnM⟩
      · show (MulAut.conj (⟨n, hnM⟩ : ↥D.M)) (⟨n, hnM⟩⁻¹ * x * ⟨n, hnM⟩) = x
        rw [MulAut.conj_apply]
        group
  have hcomp : (MulAut.conj (F.phiA ⟨n, hnM⟩)).toMonoidHom.comp F.phiA =
      F.phiA.comp (MulAut.conj (⟨n, hnM⟩ : ↥D.M)).toMonoidHom := by
    apply MonoidHom.ext
    intro x
    apply Equiv.ext
    intro y
    show (F.phiA ⟨n, hnM⟩ * F.phiA x * (F.phiA ⟨n, hnM⟩)⁻¹) y =
      F.phiA (⟨n, hnM⟩ * x * ⟨n, hnM⟩⁻¹) y
    rw [map_mul, map_mul, map_inv]
  have hmapK : (K₀.map F.phiA).map
      (MulAut.conj (F.phiA ⟨n, hnM⟩)).toMonoidHom = K₀.map F.phiA := by
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hK₀conj]
  have hconj_le := Subgroup.map_mono
    (f := (MulAut.conj (F.phiA ⟨n, hnM⟩)).toMonoidHom) haltA
  rw [A10Perm.map_conj_altOff, hmapK] at hconj_le
  rwa [← hsuppb_eq] at hconj_le

theorem le_M_of_not_weaklyClosed (F : A10Frame c) (hF : A10Facts F) {H : Subgroup G}
    (hH : CFSG.Open.IsTwoLocal H) (hAH : F.A ≤ H) {a : G} (haA : a ∈ F.A)
    (ha3 : F.deg (Subgroup.zpowers a) = 3)
    (halt : A10Perm.altOff (F.phiA ⟨a, F.A_le_M haA⟩).support ≤
      ((H ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf D.M).map F.phiA)
    {h : G} (hh : h ∈ H) (hhA : h * a * h⁻¹ ∈ F.A) (hha : h * a * h⁻¹ ∉ Subgroup.zpowers a) :
    H ≤ D.M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let b : G := h * a * h⁻¹
  have hbA : b ∈ F.A := hhA
  have hnex : ∃ n : G, n ∈ H ⊓ Subgroup.normalizer (F.A : Set G) ∧ n * a * n⁻¹ = b :=
    F.exists_mem_normalizer_conj_eq hF hAH haA ha3 hh hhA
  let n : G := Classical.choose hnex
  have hn_spec := Classical.choose_spec hnex
  have hnH : n ∈ H := hn_spec.1.1
  have hnN : n ∈ Subgroup.normalizer (F.A : Set G) := hn_spec.1.2
  have hnM : n ∈ D.M := hF.normalizer_A hnN
  have hna : n * a * n⁻¹ = b := hn_spec.2
  obtain ⟨hsuppb_eq, hsuppb, hsuppa, hφa_at, hφb_at⟩ :=
    phiA_conj_data F haA hbA hnM hna ha3
  have hsuppne := phiA_support_ne F haA hbA hha hnM hna hφa_at hφb_at hsuppa hsuppb_eq
  have haltA : A10Perm.altOff (F.phiA ⟨a, F.A_le_M haA⟩).support ≤
      ((H ⊓ D.M).subgroupOf D.M).map F.phiA :=
    halt.trans (Subgroup.map_mono (Subgroup.subgroupOf_mono D.M
      (inf_le_inf_left H (F.centralizer_le_M_of_deg_three hF haA ha3))))
  have haltB := altOff_support_conj_le F haA hbA hnH hnM haltA hsuppb_eq
  obtain ⟨E, hE_le, hE5, hEnc⟩ :=
    A10Perm.exists_noncyclic_five hφa_at hφb_at hsuppa hsuppb hsuppne.symm
  have hE : E ≤ ((H ⊓ D.M).subgroupOf D.M).map F.phiA :=
    le_trans hE_le (sup_le haltA haltB)
  exact c.u2 5 (by rw [F.sig]; simp) H hH
    (two_le_pRank_inf_of_noncyclic_five F hE5 hEnc hE)

private theorem zpowers_eq_of_mem_zpowers_of_ne_one {a c : G}
    (hca : c ∈ Subgroup.zpowers a) (hc1 : c ≠ 1) (ha3 : a ^ 3 = 1) :
    Subgroup.zpowers c = Subgroup.zpowers a := by
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [Subgroup.zpowers_one_eq_bot] at hca
    exact hc1 (Subgroup.mem_bot.mp hca)
  have horda : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hdvd : orderOf c ∣ 3 := (orderOf_dvd_of_mem_zpowers hca).trans (by rw [horda])
  have hc_ord : orderOf c = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hc1
    · exact h
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hca)
  rw [Nat.card_zpowers, Nat.card_zpowers, hc_ord, horda]

private theorem mem_normalizer_zpowers_of_conj_mem_zpowers {a y : G}
    (hya : y * a * y⁻¹ ∈ Subgroup.zpowers a) (ha1 : a ≠ 1) (ha3 : a ^ 3 = 1) :
    y ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
  let c : G := y * a * y⁻¹
  have hcZa : c ∈ Subgroup.zpowers a := hya
  have hc1 : c ≠ 1 := by
    intro hc
    have h : a = y⁻¹ * c * y := by simp [c]; group
    rw [hc] at h
    exact ha1 (by simpa using h)
  have hZaeq : Subgroup.zpowers c = Subgroup.zpowers a :=
    zpowers_eq_of_mem_zpowers_of_ne_one hcZa hc1 ha3
  have hmap : (Subgroup.zpowers a).map (MulAut.conj y).toMonoidHom = Subgroup.zpowers a := by
    have h1 : (Subgroup.zpowers a).map (MulAut.conj y).toMonoidHom = Subgroup.zpowers c := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
        calc c ^ k = (MulAut.conj y) a ^ k := by rw [MulAut.conj_apply]
          _ = (MulAut.conj y) (a ^ k) := (map_zpow _ _ _).symm
      · rintro ⟨k, rfl⟩
        refine Subgroup.mem_map.mpr ⟨a ^ k, Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩, ?_⟩
        calc (MulAut.conj y) (a ^ k) = (MulAut.conj y) a ^ k := map_zpow _ _ _
          _ = c ^ k := by rw [MulAut.conj_apply]
    rw [h1, hZaeq]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap

private theorem mem_centralizer_of_mem_normalizer_of_conj_mem_zpowers (F : A10Frame c) {a y : G}
    (haA : a ∈ F.A) (ha1 : a ≠ 1) (hya : y * a * y⁻¹ ∈ Subgroup.zpowers a)
    (hy2 : Nat.Coprime (orderOf y) 2) :
    y ∈ Subgroup.centralizer ({a} : Set G) := by
  classical
  have ha3 : a ^ 3 = 1 := F.elemAbelian.2 a haA
  have hcarda : Nat.card (Subgroup.zpowers a) = 3 := F.card_zpowers_of_mem_A haA ha1
  have hyU : y ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G) :=
    mem_normalizer_zpowers_of_conj_mem_zpowers hya ha1 ha3
  let act : ↥(Subgroup.normalizer (Subgroup.zpowers a : Set G)) →*
      MulAut ↥(Subgroup.zpowers a) := Subgroup.normalizerMonoidHom (Subgroup.zpowers a)
  have hpow : act ⟨y, hyU⟩ ^ orderOf y = 1 := by
    rw [← map_pow]
    have hx : (⟨y, hyU⟩ : ↥(Subgroup.normalizer (Subgroup.zpowers a : Set G))) ^
        orderOf y = 1 := by
      apply Subtype.ext
      simp [pow_orderOf_eq_one]
    rw [hx, map_one]
  have hdvdOrd : orderOf (act ⟨y, hyU⟩) ∣ orderOf y := by
    have h := orderOf_map_dvd act ⟨y, hyU⟩
    simpa [Subgroup.orderOf_coe] using h
  have hdvd2 : orderOf (act ⟨y, hyU⟩) ∣ 2 := by
    have h := orderOf_dvd_natCard (act ⟨y, hyU⟩)
    have hcard : Nat.card (MulAut ↥(Subgroup.zpowers a)) = 2 := by
      rw [IsCyclic.card_mulAut, hcarda, Nat.totient_prime Nat.prime_three]
    rwa [hcard] at h
  have hone : orderOf (act ⟨y, hyU⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.of_dvd_left hdvdOrd hy2) dvd_rfl hdvd2
  have hact : act ⟨y, hyU⟩ = 1 := orderOf_eq_one_iff.mp hone
  have hya_eq : y * a * y⁻¹ = a := by
    have hcoe := Subgroup.normalizerMonoidHom_apply_apply_coe (Subgroup.zpowers a)
      ⟨y, hyU⟩ ⟨a, Subgroup.mem_zpowers_iff.mpr ⟨1, zpow_one a⟩⟩
    rw [hact, MulAut.one_apply] at hcoe
    exact hcoe.symm
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  rw [hz]
  calc a * y = (y * a * y⁻¹) * y := by rw [hya_eq]
    _ = y * a := by group

theorem isSylowOf_A_of_weaklyClosed (F : A10Frame c) (hF : A10Facts F) {H : Subgroup G}
    (hAH : F.A ≤ H) {a : G} (haA : a ∈ F.A) (ha3 : F.deg (Subgroup.zpowers a) = 3)
    (hwc : ∀ h ∈ H, h * a * h⁻¹ ∈ F.A → h * a * h⁻¹ ∈ Subgroup.zpowers a) :
    CFSG.ABGLocalTools.IsSylowOf 3 F.A H := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have haL : a ∈ c.L := F.P_le_L (F.A_le haA)
  have ha1 : a ≠ 1 := F.ne_one_of_deg_ne_zero haL (by rw [ha3]; norm_num)
  have hAp : IsPGroup 3 (F.A.subgroupOf H) := F.elemAbelian.isPGroup.comap_subtype
  obtain ⟨S, hAS⟩ := hAp.exists_le_sylow
  let Q : Subgroup G := (S : Subgroup ↥H).map H.subtype
  have hQp : IsPGroup 3 Q := (S.isPGroup').map H.subtype
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 3 Q H := ⟨S, rfl⟩
  have hAQ : F.A ≤ Q := by
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hAH hx⟩, hAS (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hNQ_le_C : Q ⊓ Subgroup.normalizer (F.A : Set G) ≤
      Subgroup.centralizer ({a} : Set G) := by
    intro y hy
    obtain ⟨hyQ, hyN⟩ := hy
    have hyH : y ∈ H := hQsyl.le hyQ
    have hyaA : y * a * y⁻¹ ∈ F.A := (Subgroup.mem_normalizer_iff.mp hyN a).mp haA
    have hyaZa : y * a * y⁻¹ ∈ Subgroup.zpowers a := hwc y hyH hyaA
    have hy2 : Nat.Coprime (orderOf y) 2 := by
      obtain ⟨n, hn⟩ := hQp.exists_card_eq
      refine Nat.Coprime.of_dvd_left (Subgroup.orderOf_dvd_natCard Q hyQ) ?_
      rw [hn]
      exact Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 3 2)
    exact mem_centralizer_of_mem_normalizer_of_conj_mem_zpowers F haA ha1 hyaZa hy2
  have hNQ_eq : Q ⊓ Subgroup.normalizer (F.A : Set G) = F.A :=
    (F.isSylowOf_A_centralizer_of_deg_three hF haA ha3).eq_of_le
      (le_inf hAQ Subgroup.le_normalizer) hNQ_le_C hQp.to_inf_left
  have hQA : Q = F.A := by
    by_contra hne
    have hlt : F.A < Q := lt_of_le_of_ne hAQ (fun hq => hne hq.symm)
    have hgrowth := CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup (p := 3) hQp hlt
    rw [hNQ_eq] at hgrowth
    exact lt_irrefl _ hgrowth
  rwa [hQA] at hQsyl

end Ctx82E3.A10Frame

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
