module

public import CFSG.Sporadic.SmallOddCore.J2Check
public import CFSG.Sporadic.SmallOddCore.Normalizing
public import CFSG.Sporadic.Schreier.PairJ2Pairs
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Certificates
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.Blueprint

theorem rep_map_ofNat {n : ℕ} (hn : n < 2 ^ 32) {a : Array ℕ} {g : Equiv.Perm (Fin n)}
    (h : CFSG.Monster.B.Co2.Rep n a g) : Th.Rep n (a.map UInt32.ofNat) g := by
  intro i hi
  have h1 := h ⟨i, hi⟩
  rw [idx_of_lt _ hi]
  unfold ap
  by_cases hs : i < a.size
  · rw [getElem!_pos (a.map UInt32.ofNat) i (by simpa using hs), Array.getElem_map,
      UInt32.toNat_ofNat', ← getElem!_pos a i hs, h1, Nat.mod_eq_of_lt ((g _).isLt.trans hn)]
    rfl
  · rw [getElem!_neg (a.map UInt32.ofNat) i (by simpa using hs)]
    rw [getElem!_neg a i hs] at h1
    rw [show (g • (⟨i, hi⟩ : Fin n) : Fin n) = g ⟨i, hi⟩ from rfl, ← h1]
    rfl

theorem j2_groupData :
    GroupData 315 j2P j2PGTbls j2Gen j2Sift where
  lt := by norm_num
  rep := by
    intro l hl
    have hl2 : l < 2 := by simpa [j2PGTbls] using hl
    interval_cases l
    · exact rep_map_ofNat (by norm_num) (rep_j2StrongPerm (by norm_num))
    · exact rep_map_ofNat (by norm_num) (rep_j2StrongPerm (by norm_num))
  gen := by
    rw [j2P]
    congr 1
    ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image, Set.mem_ofPred_eq]
    have hsz : j2PGTbls.size = 2 := rfl
    rw [hsz]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, by norm_num, rfl⟩
      · exact ⟨1, by norm_num, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      interval_cases l
      · exact Or.inl rfl
      · exact Or.inr rfl
  sift := by
    intro T g hT
    rw [j2P_eq_original]
    exact siftA_iff_mem_originalSubgroup j2ChainArrays (by norm_num) PairJ2.chain_check.1
      (co2Rep_natArr_iff.2 hT)

theorem factorization_1209600 : (1209600 : ℕ).factorization 2 = 8 := by
  rw [show (1209600 : ℕ) = 2 ^ 8 * 4725 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem dvd_of_dvd_two_pow_mul {q a m : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (h : q ∣ 2 ^ a * m) :
    q ∣ m := by
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h)) hq2
  · exact h

theorem j2_primes : ∀ r ∈ j2Rows, ∀ q : ℕ, q.Prime → q ∣ r.centOrder → q ≠ 2 →
    q ∈ r.oddPrimes := by
  intro r hr q hq hdvd hq2
  simp only [j2Rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · have h := dvd_of_dvd_two_pow_mul (a := 4) (m := 21) hq hq2 (by simpa using hdvd)
    have hle := Nat.le_of_dvd (by norm_num) h
    interval_cases q <;> simp_all (config := { decide := true })
  · have h := dvd_of_dvd_two_pow_mul (a := 4) (m := 15) hq hq2 (by simpa using hdvd)
    have hle := Nat.le_of_dvd (by norm_num) h
    interval_cases q <;> simp_all (config := { decide := true })
  · have h := dvd_of_dvd_two_pow_mul (a := 7) (m := 15) hq hq2 (by simpa using hdvd)
    have hle := Nat.le_of_dvd (by norm_num) h
    interval_cases q <;> simp_all (config := { decide := true })

theorem j2_sylowOrder : j2SylowOrder = 2 ^ (2 * 604800).factorization 2 := by
  rw [show 2 * 604800 = 1209600 by norm_num, factorization_1209600]
  rfl

theorem j2_stab :
    ∀ x : Fin 315, x ≠ 1 → ∃ s ∈ j2P, s 1 = 1 ∧ s x ≠ x := by
  have h := j2_stabOK
  simp only [j2StabOK, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, Bool.or_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq, List.mem_range] at h
  obtain ⟨hst, hmove⟩ := h
  intro x hx
  obtain ⟨T, hT, hTx⟩ := (hmove x.val x.isLt).resolve_left (fun h => hx (Fin.ext h))
  have hT' := hT
  simp only [j2StabTbls, List.mem_filter, List.mem_map, List.mem_range] at hT'
  obtain ⟨⟨j, hj, rfl⟩, -⟩ := hT'
  have hrep := rep_map_ofNat (n := 315) (by norm_num) (rep_j2StrongPerm hj)
  obtain ⟨hsift, h1⟩ := hst _ hT
  refine ⟨j2StrongPerm j, (j2_groupData.sift _ _ hrep).1 hsift, ?_, ?_⟩
  · apply Fin.ext
    have := hrep 1 (by norm_num)
    rw [idx_of_lt _ (by norm_num), h1] at this
    exact this.symm
  · intro hfix
    apply hTx
    have := hrep x.val x.isLt
    rw [idx_of_lt _ x.isLt] at this
    rw [this]
    exact congrArg Fin.val hfix

theorem j2_centralizer_eq_bot :
    centralizer (j2P : Set (Equiv.Perm (Fin 315))) = ⊥ := by
  have h0 : 0 < j2Chain.baseCount := by rw [j2Chain_baseCount]; norm_num
  have hb : j2Chain.base.get ⟨0, h0⟩ = 1 := by
    apply Fin.ext
    have := j2Chain_base
    have h1 : (j2Chain.base.toList.map Fin.val)[0]'(by simp [h0]) = 1 := by simp [this]
    simpa [Vector.get_eq_getElem] using h1
  have htrans := transitive_of_orbitSize j2Chain j2Chain_valid.1 h0
    (by rw [j2Chain_orbitSize]; rfl)
  rw [hb, ← j2P_eq_original] at htrans
  exact centralizer_eq_bot_of_transitive 1 htrans j2_stab

theorem ctuc_j2_normalizing_involution_permutation_model :
    j2u ^ 2 = 1 ∧ j2u ≠ 1 ∧ j2u ∉ j2P ∧ j2P.map (MulAut.conj j2u).toMonoidHom = j2P ∧
      centralizer (j2P : Set (Equiv.Perm (Fin 315))) = ⊥ ∧
      (∀ x, x ∈ j2R ↔ x ∈ j2P ∨ x * j2u ∈ j2P) ∧ j2P ⊓ zpowers j2u = ⊥ ∧
      (j2P.subgroupOf j2R).Normal ∧ Nat.card j2R = 1209600 ∧
      ∃ φ : j2R →* MulAut j2P, Function.Injective φ ∧
        (∀ (x : j2R) (p : j2P),
          ((φ x p : j2P) : Equiv.Perm (Fin 315)) = (x : Equiv.Perm (Fin 315)) * p * (x : _)⁻¹) ∧
        (j2P.subgroupOf j2R).map φ = (MulAut.conj : j2P →* MulAut j2P).range ∧
        Function.Injective (MulAut.conj : j2P →* MulAut j2P) := by
  obtain ⟨hU2, hU1, hUP, hmap', -, -, -, -, -, -, -⟩ :=
    centData_spec j2_groupData card_j2P j2_primes j2_sylowOrder j2_centDataOK
  have hUn : ∀ p ∈ j2P, j2u * p * j2u⁻¹ ∈ j2P := fun p hp => by
    rw [← hmap']
    exact ⟨p, hp, rfl⟩
  obtain ⟨hmap, hRmem, hinf, hnormal, hcard, φ, hφinj, hφ, himage, hconjinj⟩ :=
    normalizing_model hU2 hUP hUn j2_centralizer_eq_bot
  refine ⟨hU2, hU1, hUP, hmap, j2_centralizer_eq_bot, hRmem, hinf, hnormal, ?_, φ, hφinj, hφ,
    himage, hconjinj⟩
  show Nat.card ↥(j2P ⊔ zpowers (tp 315 j2OuterTbl)) = 1209600
  rw [hcard, card_j2P]

theorem ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial :
    j2S ≤ j2R ∧ Nat.card j2S = 256 ∧ (∃ T : Sylow 2 j2R, (T : Subgroup j2R) = j2S.subgroupOf j2R) ∧
      (∀ r ∈ j2Rows, tp 315 r.rep ∈ j2R ∧ orderOf (tp 315 r.rep) = 2 ∧
        (r.outer = true ↔ tp 315 r.rep ∉ j2P) ∧
        j2C r = j2P ⊓ centralizer ({tp 315 r.rep} : Set _) ∧
        Nat.card ↥(j2P ⊓ centralizer ({tp 315 r.rep} : Set (Equiv.Perm (Fin 315)))) =
          r.centOrder ∧
        (conjClass j2P (tp 315 r.rep)).ncard = r.classSize) ∧
      (∀ t ∈ j2R, orderOf t = 2 → ∃ r ∈ j2Rows, ∃ g ∈ j2P, t = g * tp 315 r.rep * g⁻¹) ∧
      (∀ i j : Fin j2Rows.length, (∃ g ∈ j2P,
        tp 315 j2Rows[j].rep = g * tp 315 j2Rows[i].rep * g⁻¹) → i = j) ∧
      j2Rows.map (fun r => (r.outer, r.classSize, r.centOrder)) =
        [(true, 1800, 336), (false, 2520, 240), (false, 315, 1920)] ∧
      (∀ t ∈ j2R, orderOf t = 2 →
        CFSG.oddCore ↥(j2P ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 315)))) = ⊥) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, hRcard, hSR, hScard, hrows, hcover, hodd⟩ :=
    centData_spec j2_groupData card_j2P j2_primes j2_sylowOrder j2_centDataOK
  have hRcard' : Nat.card j2R = 1209600 := hRcard
  have hS256 : Nat.card j2S = 256 := hScard
  have hSR' : j2S ≤ j2R := hSR
  refine ⟨hSR, hS256, ?_, fun r hr => ?_, hcover, ?_, rfl, hodd⟩
  · refine ⟨Sylow.ofCard (j2S.subgroupOf j2R) ?_, Sylow.coe_ofCard _ _⟩
    rw [Nat.card_congr (subgroupOfEquivOfLe hSR').toEquiv, hS256, hRcard',
      factorization_1209600]
    norm_num
  · obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := hrows r hr
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  ·
    intro i j ⟨g, hg, hij⟩
    have hinv : ∀ r ∈ j2Rows, ∀ r' ∈ j2Rows, (∃ g ∈ j2P,
        tp 315 r'.rep = g * tp 315 r.rep * g⁻¹) →
          r.outer = r'.outer ∧ r.centOrder = r'.centOrder := by
      rintro r hr r' hr' ⟨g, hg, hgr⟩
      obtain ⟨-, -, hout, -, hcent, -, -⟩ := hrows r hr
      obtain ⟨-, -, hout', -, hcent', -, -⟩ := hrows r' hr'
      constructor
      · have hmem : tp 315 r.rep ∈ j2P ↔ tp 315 r'.rep ∈ j2P := by
          rw [hgr]
          constructor
          · intro h; exact j2P.mul_mem (j2P.mul_mem hg h) (j2P.inv_mem hg)
          · intro h
            have := j2P.mul_mem (j2P.mul_mem (j2P.inv_mem hg) h) hg
            rwa [show g⁻¹ * (g * tp 315 r.rep * g⁻¹) * g = tp 315 r.rep by group] at this
        cases hro : r.outer <;> cases hro' : r'.outer
        · rfl
        · rw [hro'] at hout'
          rw [hro, Bool.false_eq_true, false_iff, not_not] at hout
          exact absurd (hmem.1 hout) (hout'.1 rfl)
        · rw [hro] at hout
          rw [hro', Bool.false_eq_true, false_iff, not_not] at hout'
          exact absurd (hmem.2 hout') (hout.1 rfl)
        · rfl
      · rw [← hcent, ← hcent', hgr, inf_centralizer_conj j2P hg,
          Subgroup.card_map_of_injective (MulAut.conj g).injective]
    have h := hinv _ (List.getElem_mem _) _ (List.getElem_mem _) ⟨g, hg, hij⟩
    have hnodup : (j2Rows.map fun r => (r.outer, r.centOrder)).Nodup := by decide
    have hi : (i : ℕ) < (j2Rows.map fun r => (r.outer, r.centOrder)).length := by simp
    have hj : (j : ℕ) < (j2Rows.map fun r => (r.outer, r.centOrder)).length := by simp
    have hij' : (j2Rows.map fun r => (r.outer, r.centOrder))[(i : ℕ)] =
        (j2Rows.map fun r => (r.outer, r.centOrder))[(j : ℕ)] := by
      simp only [List.getElem_map]
      rw [h.1, h.2]
    exact Fin.ext (hnodup.getElem_inj_iff.mp hij')

theorem j2_outer_card_le :
    Nat.card (Outer j2P) ≤ 2 := by
  rw [← Nat.card_congr (equivalence j2PermEquiv).toEquiv]
  exact AT_J2_Schreier.1

theorem ctuc_j2_full_automorphism_permutation_model :
    ∃ e : j2R ≃* MulAut j2P,
      (∀ (x : j2R) (p : j2P),
        ((e x p : j2P) : Equiv.Perm (Fin 315)) = (x : Equiv.Perm (Fin 315)) * p * (x : _)⁻¹) ∧
      (j2P.subgroupOf j2R).map e.toMonoidHom = inner j2P ∧
      Nonempty (Outer j2P ≃* Multiplicative (ZMod 2)) ∧ Nat.card (MulAut j2P) = 1209600 := by
  obtain ⟨hU2, -, hUP, hmap, hC, -⟩ := ctuc_j2_normalizing_involution_permutation_model
  have hUn : ∀ p ∈ j2P, j2u * p * j2u⁻¹ ∈ j2P := fun p hp => by
    rw [← hmap]
    exact ⟨p, hp, rfl⟩
  obtain ⟨e, he, himage, hout, hcard⟩ := full_automorphism_model hU2 hUP hUn hC j2_outer_card_le
  exact ⟨e, he, himage, hout, by rw [hcard, card_j2P]⟩

theorem j2_autModel :
    AutModel j2P j2R := by
  obtain ⟨hU2, -, hUP, hmap, hC, hRmem, -⟩ := ctuc_j2_normalizing_involution_permutation_model
  have hUn : ∀ p ∈ j2P, j2u * p * j2u⁻¹ ∈ j2P := fun p hp => by
    rw [← hmap]
    exact ⟨p, hp, rfl⟩
  obtain ⟨e, he, -⟩ := ctuc_j2_full_automorphism_permutation_model
  refine autModel_of le_sup_left (fun x hx p hp => ?_) e he hC
  rcases (hRmem x).1 hx with hxP | hxU
  · exact j2P.mul_mem (j2P.mul_mem hxP hp) (j2P.inv_mem hxP)
  · have hUU : j2u * j2u = 1 := by rw [← sq, hU2]
    have hUinv : j2u⁻¹ = j2u := inv_eq_of_mul_eq_one_right hUU
    have h1 : j2u⁻¹ * p * j2u ∈ j2P := by
      have := hUn p hp
      rw [hUinv] at this ⊢
      exact this
    have : x * p * x⁻¹ = (x * j2u) * (j2u⁻¹ * p * j2u) * (x * j2u)⁻¹ := by group
    rw [this]
    exact j2P.mul_mem (j2P.mul_mem hxU h1) (j2P.inv_mem hxU)

theorem ctuc_j2_almost_simple_involution_centralizer_odd_core_trivial
    {X : Type*} [Group X]
    [Finite X] (S : Subgroup X) [S.Normal] (hS : Nonempty (S ≃* NativeSporadic.J2))
    (hC : centralizer (S : Set X) = ⊥) (t : X) (ht : orderOf t = 2) :
    CFSG.oddCore ↥(centralizer ({t} : Set X)) = ⊥ := by
  obtain ⟨ψ⟩ := hS
  obtain ⟨-, -, -, -, -, -, -, hodd⟩ :=
    ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  have hidx : Nat.card j2R ≤ 2 * Nat.card j2P := by
    rw [ctuc_j2_normalizing_involution_permutation_model.2.2.2.2.2.2.2.2.1, card_j2P]
  exact oddCore_centralizer_eq_bot j2_autModel hidx hodd S (ψ.trans j2PermEquiv) hC t ht

theorem j2_not_comm :
    ∃ a b : NativeSporadic.J2, a * b ≠ b * a := by
  obtain ⟨-, -, -, hc, -⟩ := AT_J2_image_pair_count
  refine ⟨j2PermEquiv.symm j2a, j2PermEquiv.symm j2b, fun h => ?_⟩
  have h' := congrArg (fun x => ((j2PermEquiv x : j2P) : Equiv.Perm (Fin 315))) h
  simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul] at h'
  exact mul_ne_mul_of_orderOf_commutator hc (by norm_num) h'

theorem ctuc_j2_generalized_fitting_involution_centralizer_odd_core_trivial
    {X : Type*}
    [Group X] [Finite X] (hF : IsSimpleGroup (CFSG.generalizedFitting X))
    (hJ : Nonempty (CFSG.generalizedFitting X ≃* NativeSporadic.J2)) (t : X)
    (ht : orderOf t = 2) : CFSG.oddCore ↥(centralizer ({t} : Set X)) = ⊥ := by
  have : (CFSG.generalizedFitting X).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  obtain ⟨ψ⟩ := hJ
  have hnab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := j2_not_comm
    refine ⟨ψ.symm a, ψ.symm b, fun h => hab ?_⟩
    have := congrArg ψ h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this
  exact ctuc_j2_almost_simple_involution_centralizer_odd_core_trivial _ ⟨ψ⟩
    (centralizer_generalizedFitting_eq_bot hF hnab) t ht

end CFSG.Sporadic.SmallOddCore
