module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameUHeart
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeBlock
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUDvdBound

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.SectionRank.OddCover (diagHom coe_diagHom)

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

theorem ggQTwoXInLU_compl {N : ℕ} {K : Type} [Field K] [Finite K]
    (hS : GGQTwoSetting 3 B Bs x L D J) (hN : 7 ≤ N)
    (F : GGQTwoXInLUFrame Bs (ggG0 3 B x L D J) N K) {I : Finset (Fin N)} {lam : Kˣ}
    {z : ↥(unitarySU 2 1 K N)} (hlam : lam ≠ 1) (hI : Iᶜ.Nonempty)
    (hL : L = (TableBUE.blockSU (K := K) (n := 1) I).map F.φ)
    (hz : (z : GL (Fin N) K) = diagHom N (fun i => if i ∈ I then lam else 1)) (hzx : F.φ z = x) :
    ∃ j₀ : Fin N, I = Finset.univ.erase j₀ := by
  classical
  by_contra hnot
  have hcard : 1 < Iᶜ.card := by
    by_contra hc
    have hc1 : Iᶜ.card ≤ 1 := by omega
    have hc0 : Iᶜ.card ≠ 0 := by
      intro h0
      rw [Finset.card_eq_zero] at h0
      exact hI.ne_empty h0
    have hc_eq : Iᶜ.card = 1 := by omega
    obtain ⟨j₀, hj₀⟩ := Finset.card_eq_one.mp hc_eq
    have hI_eq : I = Finset.univ.erase j₀ := by
      ext x
      rw [Finset.mem_erase]
      simp only [Finset.mem_univ, and_true]
      constructor
      · intro hx hxj
        have hj0c : j₀ ∈ Iᶜ := by
          rw [hj₀]
          exact Finset.mem_singleton_self j₀
        rw [Finset.mem_compl] at hj0c
        exact hj0c (hxj ▸ hx)
      · intro hx
        by_contra hxI
        have : x ∈ Iᶜ := by simpa using hxI
        rw [hj₀] at this
        exact hx (Finset.mem_singleton.mp this)
    exact hnot ⟨j₀, hI_eq⟩
  obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp hcard
  let t : Fin N → Kˣ := Function.update (Function.update 1 j lam) k lam⁻¹
  have hcardK : Nat.card K = 4 := by
    simpa using F.field.card
  have hcardKunits : Nat.card Kˣ = 3 := by
    rw [Nat.card_units, hcardK]
  have hτ : ∀ i, t i ^ 3 = 1 := by
    intro i
    have h := pow_card_eq_one' (x := t i) (G := Kˣ)
    rwa [hcardKunits] at h
  have hprod : ∏ i, t i = 1 := by
    have hk_mem : k ∈ (Finset.univ : Finset (Fin N)) := Finset.mem_univ _
    have hj_mem : j ∈ (Finset.univ \ {k} : Finset (Fin N)) := by
      rw [Finset.mem_sdiff]
      exact ⟨Finset.mem_univ j, by simpa using hjk⟩
    change ∏ i, Function.update (Function.update (1 : Fin N → Kˣ) j lam) k lam⁻¹ i = 1
    rw [Finset.prod_update_of_mem hk_mem, Finset.prod_update_of_mem hj_mem]
    simp [mul_comm]
  have hmem : diagHom N t ∈ unitarySU 2 1 K N :=
    TableBUDL.diagHom_mem_unitarySU F.field (by norm_num : 3 ∣ 2 ^ 1 + 1) hτ hprod
  let s : ↥(unitarySU 2 1 K N) := ⟨diagHom N t, hmem⟩
  have hs : (s : GL (Fin N) K) = diagHom N t := rfl
  have ht_const : ∀ i ∈ I, ∀ j' ∈ I, t i = t j' := by
    intro i hi j' hj'
    have hi1 : t i = 1 := by
      have hij : i ≠ j := by
        intro h
        subst h
        exact (Finset.mem_compl.mp hj) hi
      have hik : i ≠ k := by
        intro h
        subst h
        exact (Finset.mem_compl.mp hk) hi
      simp [t, Function.update, hij, hik]
    have hj'1 : t j' = 1 := by
      have hj'j : j' ≠ j := by
        intro h
        subst h
        exact (Finset.mem_compl.mp hj) hj'
      have hj'k : j' ≠ k := by
        intro h
        subst h
        exact (Finset.mem_compl.mp hk) hj'
      simp [t, Function.update, hj'j, hj'k]
    rw [hi1, hj'1]
  have hBs : F.φ s ∈ Bs := ggQTwoXInLU_heart hS F s t hs
  have hcommG : F.φ s ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [hL] at hh
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hh
    have hgs : g * s = s * g := by
      have hle := TableBUE.blockSU_le_centralizer (K := K) (n := 1) (d := N)
        (S := I) ht_const (t := s) hs
      have hmem := hle hg
      exact Subgroup.mem_centralizer_singleton_iff.mp hmem
    rw [← map_mul, hgs, map_mul]
  have hmem_inf : F.φ s ∈ Bs ⊓ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_inf.mpr ⟨hBs, hcommG⟩
  have hzpow : F.φ s ∈ Subgroup.zpowers x := by
    rw [← GGConfig.bstar_inf_centralizer_L hS.1.1]
    exact hmem_inf
  obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.mp hzpow
  have hker : s * z ^ (-e) ∈ F.φ.ker := by
    rw [MonoidHom.mem_ker]
    calc F.φ (s * z ^ (-e)) = F.φ s * F.φ (z ^ (-e)) := by rw [map_mul]
      _ = F.φ s * (F.φ z) ^ (-e) := by rw [map_zpow]
      _ = x ^ e * x ^ (-e) := by rw [he, hzx]
      _ = 1 := by group
  have hcentral : s * z ^ (-e) ∈ Subgroup.center ↥(unitarySU 2 1 K N) := F.ker_le hker
  have hsu : ((1 : G), ((s * z ^ (-e) : ↥(unitarySU 2 1 K N)) : GL (Fin N) K)) ∈
      SUTorus.suPairs F.φ := by
    constructor
    · exact Subgroup.le_normalizer (s * z ^ (-e)).2
    · intro u v hv
      have hcentral_u : (s * z ^ (-e) : ↥(unitarySU 2 1 K N)) * u =
          u * (s * z ^ (-e) : ↥(unitarySU 2 1 K N)) := by
        have := Subgroup.mem_center_iff.mp hcentral u
        exact this.symm
      have hv' : v = u := by
        apply Subtype.ext
        rw [hv]
        have hmat : ((s * z ^ (-e) : ↥(unitarySU 2 1 K N)) : GL (Fin N) K) *
            (u : GL (Fin N) K) =
            (u : GL (Fin N) K) *
              ((s * z ^ (-e) : ↥(unitarySU 2 1 K N)) : GL (Fin N) K) := by
          exact congrArg Subtype.val hcentral_u
        rw [hmat]
        group
      simp [hv']
  have hNq : (N, 2 ^ 1) ≠ (3, 2) := by
    intro h
    have hN3 : N = 3 := congrArg Prod.fst h
    omega
  obtain ⟨c, hc⟩ := SUTorus.exists_scalar_of_mem_suPairs_one (G := G) (f := 1) (n := N)
    F.field (by omega : 3 ≤ N) hNq (by norm_num : Nat.Prime 3)
    (by norm_num : 3 ∣ 2 ^ 1 + 1) F.ker_le hsu
  have hB_j : ((s * z ^ (-e) : ↥(unitarySU 2 1 K N)) : GL (Fin N) K) j j = lam := by
    rw [Subgroup.coe_mul, Subgroup.coe_zpow]
    rw [show (s : GL (Fin N) K) = diagHom N t from rfl]
    rw [hz]
    rw [← map_zpow (diagHom N) (fun i => if i ∈ I then lam else 1) (-e)]
    rw [← map_mul]
    rw [coe_diagHom]
    rw [Matrix.diagonal_apply_eq]
    have hg_j : (fun i => if i ∈ I then lam else 1) j = 1 := by
      have hj' : j ∉ I := Finset.mem_compl.mp hj
      simp [hj']
    have ht_j : t j = lam := by simp [t, Function.update, hjk]
    rw [Pi.mul_apply]
    rw [← Units.ext_iff]
    change t j * ((fun i => if i ∈ I then lam else 1) j) ^ (-e) = lam
    rw [ht_j, hg_j, one_zpow, mul_one]
  have hB_k : ((s * z ^ (-e) : ↥(unitarySU 2 1 K N)) : GL (Fin N) K) k k = lam⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_zpow]
    rw [show (s : GL (Fin N) K) = diagHom N t from rfl]
    rw [hz]
    rw [← map_zpow (diagHom N) (fun i => if i ∈ I then lam else 1) (-e)]
    rw [← map_mul]
    rw [coe_diagHom]
    rw [Matrix.diagonal_apply_eq]
    have hg_k : (fun i => if i ∈ I then lam else 1) k = 1 := by
      have hk' : k ∉ I := Finset.mem_compl.mp hk
      simp [hk']
    have ht_k : t k = lam⁻¹ := by simp [t]
    rw [Pi.mul_apply]
    rw [← Units.ext_iff]
    change t k * ((fun i => if i ∈ I then lam else 1) k) ^ (-e) = lam⁻¹
    rw [ht_k, hg_k, one_zpow, mul_one]
  have hc_j : ((s * z ^ (-e) : ↥(unitarySU 2 1 K N)) : GL (Fin N) K) j j = c := by
    rw [hc]
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  have hc_k : ((s * z ^ (-e) : ↥(unitarySU 2 1 K N)) : GL (Fin N) K) k k = c := by
    rw [hc]
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  have hlam_ne_inv : lam ≠ lam⁻¹ := by
    intro h
    have h2 : lam ^ 2 = 1 := by
      calc lam ^ 2 = lam * lam := by rw [pow_two]
        _ = lam * lam⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel lam
    have h3 : lam ^ 3 = 1 := by
      have h' := pow_card_eq_one' (x := lam) (G := Kˣ)
      rwa [hcardKunits] at h'
    have h1 : lam = 1 := by
      calc lam = 1 * lam := by rw [one_mul]
        _ = lam ^ 2 * lam := by rw [h2]
        _ = lam ^ 3 := by rw [← pow_succ]
        _ = 1 := h3
    exact hlam h1
  have h1 : lam = c := by
    apply Units.ext
    exact hB_j.symm.trans hc_j
  have h2 : c = lam⁻¹ := by
    apply Units.ext
    exact hc_k.symm.trans hB_k
  have h_eq : lam = lam⁻¹ := h1.trans h2
  exact hlam_ne_inv h_eq

end CFSG.StandardType

end
