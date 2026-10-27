module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoCover
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofTwo
public import CFSG.GroupTheory.IndexThreeCosets

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly
open scoped commutatorElement

private theorem eq_one_of_mem_zTwo_of_pow_three {L' : Type} [Group L'] [Finite L'] {u : L'}
    (hu : u ∈ USixTwo.zTwo L') (h3 : u ^ 3 = 1) : u = 1 := by
  have h2 : orderOf u ∣ 2 ^ Nat.card L' := orderOf_dvd_of_pow_eq_one hu.2
  have h13 : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hcop : Nat.Coprime 3 (2 ^ Nat.card L') := (by norm_num : Nat.Coprime 3 2).pow_right _
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h13 h2)

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]

theorem mem_zpowers_of_mem_center
    (hK : Nat.card K = 4) {Bs L : Subgroup G} {x : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hBs : IsElemAbelian 3 Bs)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G)) {z : G} (hzL : z ∈ L)
    (hzc : ∀ l ∈ L, z * l = l * z) {k : ℕ} (hzpow : z ^ 3 ^ k = 1) :
    z ∈ Subgroup.zpowers x := by
  classical
  let π : ↥L →* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπs : Function.Surjective π := by
    intro r
    obtain ⟨q, hq⟩ := θ.surjective r
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) q
    exact ⟨l, hq⟩
  have hπker : π.ker = Subgroup.center ↥L := by
    ext l
    rw [MonoidHom.mem_ker]
    exact ⟨fun hl => (QuotientGroup.eq_one_iff l).mp (θ.injective (by rw [map_one]; exact hl)),
      fun hl => by
        show θ (QuotientGroup.mk' (Subgroup.center ↥L) l) = 1
        rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff l).mpr hl, map_one]⟩
  have hzk : USixTwo.zTwo ↥L ≤ π.ker := by
    rw [hπker]
    exact USixTwo.zTwo_le_center
  let ψb : USixTwo.Qt ↥L →* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
    USixTwo.qLift π hzk
  have hψbmk : ∀ l, ψb (USixTwo.qmk ↥L l) = π l := fun l => USixTwo.qLift_mk hzk l
  have hψbs : Function.Surjective ψb := USixTwo.qLift_surjective hzk hπs
  have hψbker : ψb.ker ≤ Subgroup.center (USixTwo.Qt ↥L) :=
    USixTwo.qLift_ker_le_center hzk (le_of_eq hπker)
  have hψbperf : commutator (USixTwo.Qt ↥L) = ⊤ := USixTwo.qmk_perfect hperf
  have hψbodd : Odd (Nat.card ψb.ker) := USixTwo.qLift_odd_ker hzk (le_of_eq hπker)
  have hcov := LineU.unitaryCoverOddAt_six_two K hK
  obtain ⟨φ, hφ⟩ := hcov.2 (USixTwo.Qt ↥L) ψb hψbs hψbker hψbperf hψbodd
  have hφs : Function.Surjective φ := by
    have hcomm : ⁅(⊤ : Subgroup (USixTwo.Qt ↥L)), (⊤ : Subgroup (USixTwo.Qt ↥L))⁆ ≤
        φ.range := by
      rw [Subgroup.commutator_le]
      intro a _ b _
      obtain ⟨s, hs⟩ : ∃ s : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6),
          ψb a = LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) s := by
        obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (ψb a)
        exact ⟨s, hs.symm⟩
      obtain ⟨s', hs'⟩ : ∃ s : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6),
          ψb b = LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) s := by
        obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (ψb b)
        exact ⟨s, hs.symm⟩
      have hφs' : ψb (φ s) = LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) s := hφ s
      have hφs'' : ψb (φ s') = LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) s' := hφ s'
      have hza : a * (φ s)⁻¹ ∈ Subgroup.center (USixTwo.Qt ↥L) := by
        apply hψbker
        rw [MonoidHom.mem_ker, map_mul, map_inv, hφs', ← hs, mul_inv_cancel]
      have hzb : b * (φ s')⁻¹ ∈ Subgroup.center (USixTwo.Qt ↥L) := by
        apply hψbker
        rw [MonoidHom.mem_ker, map_mul, map_inv, hφs'', ← hs', mul_inv_cancel]
      have hae : a = (a * (φ s)⁻¹) * φ s := by group
      have hbe : b = (b * (φ s')⁻¹) * φ s' := by group
      rw [hae, hbe, LineU.comm_mul_central hza hzb (φ s) (φ s')]
      exact ⟨⁅s, s'⁆, map_commutatorElement φ s s'⟩
    have htop : (⁅(⊤ : Subgroup (USixTwo.Qt ↥L)), ⊤⁆ : Subgroup (USixTwo.Qt ↥L)) = ⊤ := hψbperf
    rw [htop] at hcomm
    intro q
    exact hcomm (Subgroup.mem_top q)
  have hscal : Nat.card ((LargeEvenScalars (Fin 6) K).subgroupOf
      (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) = 3 := USixTwo.card_scalars_subgroupOf_SU hK
  have hSUcard : Nat.card (↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) =
      3 * Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) := by
    have h := Subgroup.card_ker_mul_card_range
      (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :
        ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
          LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    have hsurj : Function.Surjective
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :
          ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
            LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :=
      QuotientGroup.mk'_surjective _
    rw [show (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))).ker =
        (LargeEvenScalars (Fin 6) K).subgroupOf (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) from
      QuotientGroup.ker_mk' _, hscal,
      MonoidHom.range_eq_top_of_surjective _ hsurj, Subgroup.card_top] at h
    rw [← h]
  have hQtcard : Nat.card (USixTwo.Qt ↥L) =
      Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) * Nat.card ψb.ker := by
    have h := Subgroup.card_ker_mul_card_of_surjective hψbs
    rw [mul_comm, h]
  have hφcard : Nat.card φ.ker * Nat.card (USixTwo.Qt ↥L) =
      Nat.card (↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) := by
    have h := Subgroup.card_ker_mul_card_range φ
    rwa [MonoidHom.range_eq_top_of_surjective φ hφs, Subgroup.card_top] at h
  have hRpos : 0 < Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :=
    Nat.card_pos
  have hkey : Nat.card φ.ker * Nat.card ψb.ker = 3 := by
    have h1 : Nat.card φ.ker * Nat.card ψb.ker *
        Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) =
        3 * Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) := by
      calc Nat.card φ.ker * Nat.card ψb.ker *
            Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
          = Nat.card φ.ker * (Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) *
              Nat.card ψb.ker) := by ring
        _ = Nat.card φ.ker * Nat.card (USixTwo.Qt ↥L) := by rw [← hQtcard]
        _ = Nat.card (↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) := hφcard
        _ = 3 * Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) := hSUcard
    exact Nat.eq_of_mul_eq_mul_right hRpos h1
  have hker_le : Nat.card ψb.ker ≤ 3 := by
    have h1 : 0 < Nat.card φ.ker := Nat.card_pos
    nlinarith [hkey, h1]
  have hzcen0 : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro u
    apply Subtype.ext
    exact (hzc (u : G) u.2).symm
  have hqmem : USixTwo.qmk ↥L ⟨z, hzL⟩ ∈ ψb.ker := by
    rw [MonoidHom.mem_ker, hψbmk]
    exact MonoidHom.mem_ker.mp (hπker.symm ▸ hzcen0)
  have hc3 : Nat.card ψb.ker ∣ 3 := by
    have hc : Nat.card ψb.ker = 1 ∨ Nat.card ψb.ker = 3 := by
      obtain ⟨m, hm⟩ := hψbodd
      omega
    rcases hc with h | h <;> rw [h] <;> norm_num
  have hq3 : (⟨USixTwo.qmk ↥L ⟨z, hzL⟩, hqmem⟩ : ψb.ker) ^ 3 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard _).trans hc3)
  have hz3l : (⟨z, hzL⟩ : ↥L) ^ 3 ∈ USixTwo.zTwo ↥L := by
    rw [← USixTwo.qmk_eq_one_iff, map_pow]
    simpa using congrArg Subtype.val hq3
  have hz3 : z ^ 3 = 1 := by
    have hu2 : orderOf ((⟨z, hzL⟩ : ↥L) ^ 3) ∣ 2 ^ Nat.card ↥L :=
      orderOf_dvd_of_pow_eq_one hz3l.2
    have hzk' : (⟨z, hzL⟩ : ↥L) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hzpow)
    have hu3 : orderOf ((⟨z, hzL⟩ : ↥L) ^ 3) ∣ 3 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul, mul_comm, pow_mul, hzk', one_pow]
    have hcop : Nat.Coprime (3 ^ k) (2 ^ Nat.card ↥L) :=
      Nat.Coprime.pow k (Nat.card ↥L) (by norm_num : Nat.Coprime 3 2)
    have h1 : (⟨z, hzL⟩ : ↥L) ^ 3 = 1 :=
      orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hu3 hu2)
    simpa using congrArg Subtype.val h1
  by_cases hzne : z = 1
  · rw [hzne]
    exact Subgroup.one_mem _
  have hzcen : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro u
    apply Subtype.ext
    exact (hzc (u : G) u.2).symm
  have hz3' : (⟨z, hzL⟩ : ↥L) ^ 3 = 1 := Subtype.ext hz3
  have hzne' : (⟨z, hzL⟩ : ↥L) ≠ 1 := fun h => hzne (by simpa using congrArg Subtype.val h)
  have hzo : orderOf (⟨z, hzL⟩ : ↥L) = 3 := orderOf_eq_prime hz3' hzne'
  have hqzmem : USixTwo.qmk ↥L ⟨z, hzL⟩ ∈ ψb.ker := by
    rw [MonoidHom.mem_ker, hψbmk]
    exact MonoidHom.mem_ker.mp (hπker.symm ▸ hzcen)
  have hqzo : orderOf (USixTwo.qmk ↥L ⟨z, hzL⟩) = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, hz3', map_one]
    · intro h1
      exact hzne' (eq_one_of_mem_zTwo_of_pow_three ((USixTwo.qmk_eq_one_iff).mp h1) hz3')
  have hker3 : Nat.card ψb.ker = 3 := by
    refine le_antisymm hker_le ?_
    rw [← hqzo]
    calc orderOf (USixTwo.qmk ↥L ⟨z, hzL⟩)
        = Nat.card (Subgroup.zpowers (USixTwo.qmk ↥L ⟨z, hzL⟩)) := (Nat.card_zpowers _).symm
      _ ≤ Nat.card ψb.ker := Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr hqzmem)
  have hzker : ψb.ker = Subgroup.zpowers (USixTwo.qmk ↥L ⟨z, hzL⟩) :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hqzmem) (by
      rw [Nat.card_zpowers, hqzo, hker3])).symm
  have hconj : ∀ (b : G) (hb : b ∈ Bs), b * z * b⁻¹ = z := by
    intro b hb
    have hzb : b * z * b⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hNL hb) z).mp hzL
    let w : ↥L := ⟨b * z * b⁻¹, hzb⟩
    have hwcen : w ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro u
      apply Subtype.ext
      have hu' : b⁻¹ * (u : G) * b ∈ L := by
        have h := (Subgroup.mem_normalizer_iff.mp
          (Subgroup.inv_mem (Subgroup.normalizer (L : Set G)) (hNL hb)) (u : G)).mp u.2
        simpa using h
      have hcomm : (b⁻¹ * (u : G) * b) * z = z * (b⁻¹ * (u : G) * b) := by
        simpa using congrArg Subtype.val (Subgroup.mem_center_iff.mp hzcen ⟨_, hu'⟩)
      show (u : G) * (b * z * b⁻¹) = b * z * b⁻¹ * (u : G)
      calc (u : G) * (b * z * b⁻¹) = b * (b⁻¹ * (u : G) * b) * z * b⁻¹ := by group
        _ = b * ((b⁻¹ * (u : G) * b) * z) * b⁻¹ := by group
        _ = b * (z * (b⁻¹ * (u : G) * b)) * b⁻¹ := by rw [hcomm]
        _ = b * z * b⁻¹ * (u : G) := by group
    have hw3 : w ^ 3 = 1 := by
      apply Subtype.ext
      show (b * z * b⁻¹) ^ 3 = 1
      rw [conj_pow, hz3]
      group
    have hwne : w ≠ 1 := by
      intro h
      apply hzne
      have h1 : b * z * b⁻¹ = 1 := congrArg Subtype.val h
      calc z = b⁻¹ * (b * z * b⁻¹) * b := by group
        _ = 1 := by rw [h1]; group
    have hqwmem : USixTwo.qmk ↥L w ∈ ψb.ker := by
      rw [MonoidHom.mem_ker, hψbmk]
      exact MonoidHom.mem_ker.mp (hπker.symm ▸ hwcen)
    have hqwo : orderOf (USixTwo.qmk ↥L w) = 3 := by
      refine orderOf_eq_prime ?_ ?_
      · rw [← map_pow, hw3, map_one]
      · intro h1
        exact hwne (eq_one_of_mem_zTwo_of_pow_three ((USixTwo.qmk_eq_one_iff).mp h1) hw3)
    have hqwne : USixTwo.qmk ↥L w ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hqwo
      exact (by norm_num : ¬ (1 = 3)) hqwo
    have hcases : USixTwo.qmk ↥L w = USixTwo.qmk ↥L ⟨z, hzL⟩ ∨
        USixTwo.qmk ↥L w = (USixTwo.qmk ↥L ⟨z, hzL⟩)⁻¹ := by
      have hmem : USixTwo.qmk ↥L w ∈ Subgroup.zpowers (USixTwo.qmk ↥L ⟨z, hzL⟩) := by
        rw [← hzker]
        exact hqwmem
      exact GroupTheory.eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_three hqzo hmem hqwne
    rcases hcases with hcase | hcase
    · have hmem : (⟨z, hzL⟩ : ↥L)⁻¹ * w ∈ USixTwo.zTwo ↥L := by
        rw [← USixTwo.qmk_eq_one_iff, map_mul, map_inv, hcase, inv_mul_cancel]
      have hcomm0 : Commute (⟨z, hzL⟩ : ↥L) w :=
        (Subgroup.mem_center_iff.mp hzcen w).symm
      have hcomm : Commute ((⟨z, hzL⟩ : ↥L)⁻¹) w := hcomm0.inv_left
      have hcube : ((⟨z, hzL⟩ : ↥L)⁻¹ * w) ^ 3 = 1 := by
        rw [hcomm.mul_pow 3, inv_pow, hz3', hw3, inv_one, one_mul]
      have h1 := eq_one_of_mem_zTwo_of_pow_three hmem hcube
      exact (congrArg Subtype.val (inv_mul_eq_one.mp h1)).symm
    · exfalso
      have hmem : (⟨z, hzL⟩ : ↥L) * w ∈ USixTwo.zTwo ↥L := by
        rw [← USixTwo.qmk_eq_one_iff, map_mul, hcase, mul_inv_cancel]
      have hcomm : Commute (⟨z, hzL⟩ : ↥L) w :=
        (Subgroup.mem_center_iff.mp hzcen w).symm
      have hcube : ((⟨z, hzL⟩ : ↥L) * w) ^ 3 = 1 := by
        rw [hcomm.mul_pow 3, hz3', hw3, one_mul]
      have h1 := eq_one_of_mem_zTwo_of_pow_three hmem hcube
      have hwinv : w = (⟨z, hzL⟩ : ↥L)⁻¹ := eq_inv_of_mul_eq_one_right h1
      let c : MulAut ↥L := Subgroup.normalizerMonoidHom L ⟨b, hNL hb⟩
      have hc3 : c ^ 3 = 1 := by
        change (Subgroup.normalizerMonoidHom L ⟨b, hNL hb⟩) ^ 3 = 1
        rw [← map_pow]
        rw [show (⟨b, hNL hb⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 3 = 1 from
          Subtype.ext (by simpa using hBs.2 b hb), map_one]
      have hcw : c ⟨z, hzL⟩ = w := by
        apply Subtype.ext
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      have hcz : c ⟨z, hzL⟩ = (⟨z, hzL⟩ : ↥L)⁻¹ := by rw [hcw, hwinv]
      have hc3z : (c ^ 3) ⟨z, hzL⟩ = (⟨z, hzL⟩ : ↥L)⁻¹ := by
        rw [show c ^ 3 = c * (c * c) by rw [pow_succ', pow_succ', pow_one]]
        rw [MulAut.mul_apply, MulAut.mul_apply, hcz, map_inv, hcz, inv_inv, hcz]
      have hzz : (⟨z, hzL⟩ : ↥L) = (⟨z, hzL⟩ : ↥L)⁻¹ := by
        calc (⟨z, hzL⟩ : ↥L) = (c ^ 3) ⟨z, hzL⟩ := by rw [hc3, MulAut.one_apply]
          _ = (⟨z, hzL⟩ : ↥L)⁻¹ := hc3z
      have hsq : (⟨z, hzL⟩ : ↥L) ^ 2 = 1 := by
        rw [pow_two]
        exact eq_inv_iff_mul_eq_one.mp hzz
      have hdvd : 3 ∣ 2 := by
        have h1 : 3 ∣ orderOf (⟨z, hzL⟩ : ↥L) := by rw [hzo]
        exact h1.trans (orderOf_dvd_of_pow_eq_one hsq)
      exact (by norm_num : ¬ (3 ∣ 2)) hdvd
  have hcent : z ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    calc b * z = (b * z * b⁻¹) * b := by group
      _ = z * b := by rw [hconj b hb]
  have hzBs : z ∈ Bs := hstar z hcent hz3
  have hzcentL : z ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (hzc l hl).symm
  have hzx : z ∈ Subgroup.zpowers x := by
    rw [← hBL]
    exact ⟨hzBs, hzcentL⟩
  exact hzx

theorem isPGroup_two_center_of_not_mem
    (hK : Nat.card K = 4) {Bs L : Subgroup G} {x : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hBs : IsElemAbelian 3 Bs) (hx : x ∈ Bs)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G)) (hxL : x ∉ L) :
    IsPGroup 2 (Subgroup.center L) := by
  have hK4 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hz : ∀ z ∈ L, (∀ l ∈ L, z * l = l * z) → z ^ 3 = 1 → z = 1 := by
    intro z hzL hzc hz3
    by_contra hzne
    have hzx : z ∈ Subgroup.zpowers x :=
      mem_zpowers_of_mem_center hK θ hperf hBs hBL hstar hNL hzL hzc (k := 1) (by simpa using hz3)
    have hzne' : (⟨z, hzL⟩ : ↥L) ≠ 1 := fun h => hzne (by simpa using congrArg Subtype.val h)
    have hzo : orderOf (⟨z, hzL⟩ : ↥L) = 3 := orderOf_eq_prime (Subtype.ext hz3) hzne'
    have hxne : x ≠ 1 := by
      intro hx1
      apply hzne
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzx
      rw [hx1] at hk
      rw [← hk]
      exact one_zpow k
    have hxo : orderOf x = 3 := orderOf_eq_prime (hBs.2 x hx) hxne
    have hcardx : Nat.card (Subgroup.zpowers x) = 3 := by
      rw [Nat.card_zpowers, hxo]
    have hzoG : orderOf z = 3 :=
      (Subgroup.orderOf_coe (⟨z, hzL⟩ : ↥L)).trans hzo
    have hcardz : Nat.card (Subgroup.zpowers z) = 3 := by
      rw [Nat.card_zpowers, hzoG]
    have hzeq : Subgroup.zpowers z = Subgroup.zpowers x := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzx)
      rw [hcardx, hcardz]
    have hxmem : x ∈ Subgroup.zpowers z := by
      rw [hzeq]
      exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
    exact hxL ((Subgroup.zpowers_le.mpr hzL) hxmem)
  exact Line63.H5.isPGroup_two_center (LineU.unitaryCoverOddAt_six_two K hK)
    (TableBU.unitaryFieldData_of_card hK4 le_rfl) (by norm_num) hperf θ hz

end CFSG.StandardType.E6QTwo

end
