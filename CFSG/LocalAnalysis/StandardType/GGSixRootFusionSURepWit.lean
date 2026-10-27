module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepWitt

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21 Matrix
open CFSG.SectionRank.OddCover (diagHom coe_diagHom det_diagHom diagHom_injective)
open CFSG.RankThree.Classical (permGL)
open CFSG.RankThree.Classical2 (diagHom_commute)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution)

namespace SURep

variable {G : Type} [Group G] {n f : ℕ} {F : Type} [Field F] [Finite F] [Fact (Nat.Prime 2)]
  [CharP F 2]

structure FrameCtxU (p : ℕ) (B Bs G₀ : Subgroup G) (hF : Nat.card F = (2 ^ f) ^ 2)
    (ψ : SU (unitaryInvolution F 2 f) n →* G) (P : GL (Fin n) F)
    (hP : conjTr (unitaryInvolution F 2 f) (P : Matrix (Fin n) (Fin n) F) *
      (P : Matrix (Fin n) (Fin n) F) = antidiag n) : Prop where
  data : UnitaryFieldData 2 f F
  bstar : GGBstar p B Bs
  ker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) n)
  range : ψ.range = G₀
  cent : Subgroup.centralizer (G₀ : Set G) = ⊥
  frame : ∀ b ∈ Bs, GGFrameDiagU (ggFrameU hF ψ P hP) b
  prime : p.Prime
  odd : p ≠ 2
  dvd : p ∣ 2 ^ f + 1
  five : 5 ≤ n

variable {p : ℕ} {B Bs D E G₀ M : Subgroup G} {t : StatedLieTag} {e : ℕ} {r : G}
  {hF : Nat.card F = (2 ^ f) ^ 2} {ψ : SU (unitaryInvolution F 2 f) n →* G} {P : GL (Fin n) F}
  {hP : conjTr (unitaryInvolution F 2 f) (P : Matrix (Fin n) (Fin n) F) *
    (P : Matrix (Fin n) (Fin n) F) = antidiag n}

namespace FrameCtxU

variable (hc : FrameCtxU p B Bs G₀ hF ψ P hP)
include hc

theorem frameKer : GGFrameKer (ggFrameU hF ψ P hP) :=
  ggFrameKer_ggFrameU hF ψ P hP (by have := hc.five; omega)
    (fun h => by have h1 : n = 3 := congrArg Prod.fst h; have h2 := hc.five; omega) hc.ker

theorem rangeφ : (ggFrameU hF ψ P hP).range = G₀ := (range_ggFrameU hF ψ P hP).trans hc.range

theorem centφ : Subgroup.centralizer ((ggFrameU hF ψ P hP).range : Set G) = ⊥ := by
  rw [hc.rangeφ]
  exact hc.cent

theorem dvdF : p ∣ Nat.card F - 1 := by
  rw [hF, show (1 : ℕ) = 1 ^ 2 from rfl, Nat.sq_sub_sq]
  exact Dvd.dvd.mul_right hc.dvd _

theorem norm_of_pow_eq_one {x : Fˣ} (hx : x ^ p = 1) : (x : F) ^ (2 ^ f + 1) = 1 := by
  obtain ⟨k, hk⟩ := hc.dvd
  rw [← Units.val_pow_eq_pow_val, hk, pow_mul, hx, one_pow, Units.val_one]

end FrameCtxU

omit [Finite F] [Fact (Nat.Prime 2)] [CharP F 2] in
theorem diagHom_mem_unitarySU' (h : UnitaryFieldData 2 f F) {δ : Fin n → Fˣ}
    (hδ : ∀ i, (δ i : F) ^ (2 ^ f + 1) = 1) (hprod : ∏ i, δ i = 1) :
    diagHom n δ ∈ unitarySU 2 f F n := by
  rw [mem_unitarySU_iff h]
  refine ⟨?_, CFSG.RankThree.Classical2.diagHom_unitary h hδ⟩
  rw [det_diagHom, ← Units.coe_prod, hprod, Units.val_one]

omit [Finite F] [Fact (Nat.Prime 2)] [CharP F 2] in
theorem frameActs_map (φ : ↥(unitarySU 2 f F n) →* G)
    {d : ↥(unitarySU 2 f F n)} {δ : Fin n → Fˣ} (hd : (d : GL (Fin n) F) = diagHom n δ)
    (hδ : ∀ i, (δ i : F) ^ (2 ^ f + 1) = 1) : GGFrameActs φ (φ d) δ := by
  refine ⟨hδ, fun s s' hs' => ?_⟩
  have : s' = d * s * d⁻¹ := Subtype.ext (by
    rw [hs', Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hd])
  rw [this, map_mul, map_mul, map_inv]

theorem ggRootFusionWitnessAlt_of_frameElt (hc : FrameCtxU p B Bs G₀ hF ψ P hP) (hle : G₀ ≤ M)
    {b : G} (hbBs : b ∈ Bs) (hb1 : b ≠ 1) {τ : Fin n → Fˣ}
    (hb : GGFrameActs (ggFrameU hF ψ P hP) b τ) {S : Finset (Fin n)} {μ : Fˣ}
    (hS : ∀ i ∈ S, τ i = μ) (hSc : ∀ i ∉ S, τ i ≠ μ) (hcard : Sᶜ.card < S.card)
    (hS4 : 4 ≤ S.card) (hSc2 : Sᶜ.card ≤ 2) {i₁ : Fin n} (hi₁ : i₁ ∉ S) {l : ℕ}
    (hl : 2 * l ≤ n) (ρ : Equiv.Perm (Fin n))
    (hpair : ∀ c : Fin n, (c : ℕ) < l → τ (ρ c) = τ (ρ (Fin.rev c))) :
    GGRootFusionWitnessAlt p Bs D E G₀ M t e r (ψ (ggInvSU (unitaryInvolution F 2 f) n l)) := by
  have hW : GGSixFusionWitness p Bs D E G₀ t e b :=
    ggSixFusionWitness_of_frameU hF hc.data hc.prime hc.dvdF (by have := hc.five; omega)
      hc.bstar hc.frameKer hc.rangeφ hc.cent hc.frame hbBs hb1 hb hS hSc hcard (by omega)
      (fun h' => by have h1 : S.card = 3 := congrArg Prod.fst h'; omega) hSc2 hi₁
  exact ggRootFusionWitnessAlt_of_frameU hF hc.data (by have := hc.five; omega) hl
    (hc.range.symm ▸ hle) hb hW ρ hpair

theorem ggRootFusionWitnessAlt_of_frameElt_bound (hc : FrameCtxU p B Bs G₀ hF ψ P hP)
    (hle : G₀ ≤ M) {b : G} (hbBs : b ∈ Bs) (hb1 : b ≠ 1) {τ : Fin n → Fˣ}
    (hb : GGFrameActs (ggFrameU hF ψ P hP) b τ) {S : Finset (Fin n)} {μ : Fˣ}
    (hS : ∀ i ∈ S, τ i = μ) (hSc : ∀ i ∉ S, τ i ≠ μ) (hcard : Sᶜ.card < S.card)
    (hS4 : 4 ≤ S.card) {i₁ : Fin n} (hi₁ : i₁ ∉ S)
    (hbound : Nat.card (Bs ⊓ Subgroup.centralizer
      (((TableBUE.blockSU (K := F) (n := f) S).map (ggFrameU hF ψ P hP) : Subgroup G) :
        Set G) : Subgroup G) ≤ p ^ 2)
    {l : ℕ} (hl : 2 * l ≤ n) (ρ : Equiv.Perm (Fin n))
    (hpair : ∀ c : Fin n, (c : ℕ) < l → τ (ρ c) = τ (ρ (Fin.rev c))) :
    GGRootFusionWitnessAlt p Bs D E G₀ M t e r (ψ (ggInvSU (unitaryInvolution F 2 f) n l)) := by
  have hW : GGSixFusionWitness p Bs D E G₀ t e b :=
    ggSixFusionWitness_of_frameU_bound hF hc.data hc.frameKer hc.rangeφ hbBs hb1 hb hS hSc hcard
      (by omega) (fun h' => by have h1 : S.card = 3 := congrArg Prod.fst h'; omega) hi₁ hbound
  exact ggRootFusionWitnessAlt_of_frameU hF hc.data (by have := hc.five; omega) hl
    (hc.range.symm ▸ hle) hb hW ρ hpair

theorem ggRootFusionWitnessAlt_of_innerU (hc : FrameCtxU p B Bs G₀ hF ψ P hP) (hle : G₀ ≤ M)
    {δ : Fin n → Fˣ} (hδ : ∏ i, δ i = 1) (hδp : ∀ i, δ i ^ p = 1) {S : Finset (Fin n)}
    {μ : Fˣ} (hS : ∀ i ∈ S, δ i = μ) (hSc : ∀ i ∉ S, δ i ≠ μ) (hcard : Sᶜ.card < S.card)
    (hS4 : 4 ≤ S.card) (hSc2 : Sᶜ.card ≤ 2) {i₁ : Fin n} (hi₁ : i₁ ∉ S) {l : ℕ}
    (hl : 2 * l ≤ n) (ρ : Equiv.Perm (Fin n))
    (hpair : ∀ c : Fin n, (c : ℕ) < l → δ (ρ c) = δ (ρ (Fin.rev c))) :
    GGRootFusionWitnessAlt p Bs D E G₀ M t e r (ψ (ggInvSU (unitaryInvolution F 2 f) n l)) := by
  have hnorm : ∀ i, (δ i : F) ^ (2 ^ f + 1) = 1 := fun i => hc.norm_of_pow_eq_one (hδp i)
  set d : ↥(unitarySU 2 f F n) := ⟨diagHom n δ, diagHom_mem_unitarySU' hc.data hnorm hδ⟩
    with hd
  have hdδ : (d : GL (Fin n) F) = diagHom n δ := rfl
  have hdp : d ^ p = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, hdδ, ← map_pow]
    have : δ ^ p = 1 := funext hδp
    rw [this, map_one, Subgroup.coe_one]
  have hbBs := mem_of_frame_inner hc.bstar hc.data hc.frame hdδ hdp
  have hb := frameActs_map (ggFrameU hF ψ P hP) hdδ hnorm
  obtain ⟨i₀, hi₀⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  have hne : δ i₁ ≠ δ i₀ := by rw [hS i₀ hi₀]; exact hSc i₁ hi₁
  have hb1 := ne_one_of_frameActs hc.frameKer hc.data (by have := hc.five; omega) hb hne
  exact ggRootFusionWitnessAlt_of_frameElt hc hle hbBs hb1 hb hS hSc hcard hS4 hSc2 hi₁ hl ρ
    hpair

omit [Finite F] [Fact (Nat.Prime 2)] [CharP F 2] in
theorem inv_pow_pow_eq_oneU {ζ : Fˣ} (hζp : ζ ^ p = 1) (a : ℕ) : (ζ⁻¹ ^ a) ^ p = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, inv_pow, hζp, inv_one, one_pow]

theorem ggRootFusionWitnessAlt_mid_coprimeU (hc : FrameCtxU p B Bs G₀ hF ψ P hP) (hle : G₀ ≤ M)
    {ζ : Fˣ} (hζ : orderOf ζ = p) {l : ℕ} (hl : 2 * l < n) (hpn : ¬ p ∣ n) :
    GGRootFusionWitnessAlt p Bs D E G₀ M t e r (ψ (ggInvSU (unitaryInvolution F 2 f) n l)) := by
  have hn5 := hc.five
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  set l' : Fin n := ⟨l, by omega⟩ with hl'
  set δ : Fin n → Fˣ := Function.update (fun _ => ζ) l' (ζ⁻¹ ^ (n - 1)) with hδdef
  have hδ : ∏ i, δ i = 1 := by
    rw [hδdef, SLRep.prod_update_const, inv_pow, inv_mul_cancel]
  have hval : ∀ i, i ≠ l' → δ i = ζ := fun i hi => by
    rw [hδdef, Function.update_of_ne hi]
  have hδp : ∀ i, δ i ^ p = 1 := by
    intro i
    by_cases hi : i = l'
    · rw [hi, hδdef, Function.update_self]
      exact inv_pow_pow_eq_oneU hζp _
    · rw [hval i hi, hζp]
  have hne : ζ⁻¹ ^ (n - 1) ≠ ζ := by
    intro h
    apply hpn
    rw [← hζ, orderOf_dvd_iff_pow_eq_one]
    calc ζ ^ n = ζ ^ (n - 1) * ζ := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      _ = ζ ^ (n - 1) * ζ⁻¹ ^ (n - 1) := by rw [h]
      _ = 1 := by rw [inv_pow, mul_inv_cancel]
  have hcS : ({l'} : Finset (Fin n))ᶜ.card = n - 1 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_singleton]
  refine ggRootFusionWitnessAlt_of_innerU hc hle hδ hδp (S := ({l'} : Finset (Fin n))ᶜ) (μ := ζ)
    (fun i hi => hval i (by simpa using hi)) (fun i hi => ?_) ?_ ?_ ?_ (i₁ := l') (by simp)
    (by omega) 1 ?_
  · obtain rfl : i = l' := by simpa using hi
    rw [hδdef, Function.update_self]
    exact hne
  · rw [compl_compl, Finset.card_singleton, hcS]
    omega
  · rw [hcS]
    omega
  · rw [compl_compl, Finset.card_singleton]
    omega
  · intro c hcl
    simp only [Equiv.Perm.one_apply]
    rw [hval c (fun h => by rw [h] at hcl; simp only [hl'] at hcl; omega),
      hval (Fin.rev c) (fun h => by
        have := congrArg Fin.val h
        simp only [Fin.val_rev, hl'] at this
        omega)]

theorem ggRootFusionWitnessAlt_pair_coprimeU (hc : FrameCtxU p B Bs G₀ hF ψ P hP) (hle : G₀ ≤ M)
    {ζ : Fˣ} (hζ : orderOf ζ = p) {l : ℕ} (hl2 : 2 ≤ l) (hn : n = 2 * l) (hpn : ¬ p ∣ n) :
    GGRootFusionWitnessAlt p Bs D E G₀ M t e r (ψ (ggInvSU (unitaryInvolution F 2 f) n l)) := by
  have hn5 := hc.five
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  set o' : Fin n := ⟨0, by omega⟩ with ho'
  set e' : Fin n := ⟨n - 1, by omega⟩ with he'
  have hoe : o' ≠ e' := by
    intro h
    have := congrArg Fin.val h
    simp only [ho', he'] at this
    omega
  set ν : Fˣ := ζ⁻¹ ^ (l - 1) with hν
  set δ : Fin n → Fˣ := Function.update (Function.update (fun _ => ζ) o' ν) e' ν with hδdef
  have hδ : ∏ i, δ i = 1 := by
    rw [hδdef, SLRep.prod_update_update_const hoe, hν, show n - 2 = (l - 1) + (l - 1) by omega,
      pow_add, inv_pow]
    group
  have hδe : δ e' = ν := by rw [hδdef, Function.update_self]
  have hδo : δ o' = ν := by
    rw [hδdef, Function.update_of_ne hoe, Function.update_self]
  have hval : ∀ i, i ≠ o' → i ≠ e' → δ i = ζ := fun i hio hie => by
    rw [hδdef, Function.update_of_ne hie, Function.update_of_ne hio]
  have hδp : ∀ i, δ i ^ p = 1 := by
    intro i
    by_cases hie : i = e'
    · rw [hie, hδe, hν]
      exact inv_pow_pow_eq_oneU hζp _
    by_cases hio : i = o'
    · rw [hio, hδo, hν]
      exact inv_pow_pow_eq_oneU hζp _
    · rw [hval i hio hie, hζp]
  have hne : ν ≠ ζ := by
    intro h
    apply hpn
    have h' : ζ⁻¹ ^ (l - 1) = ζ := h
    have h1 : ζ ^ l = 1 := by
      calc ζ ^ l = ζ ^ (l - 1) * ζ := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
        _ = ζ ^ (l - 1) * ζ⁻¹ ^ (l - 1) := by rw [h']
        _ = 1 := by rw [inv_pow, mul_inv_cancel]
    rw [hn]
    exact Dvd.dvd.mul_left (by rw [← hζ]; exact orderOf_dvd_of_pow_eq_one h1) 2
  have hpairc : ({o', e'} : Finset (Fin n)).card = 2 := Finset.card_pair hoe
  have hcS : ({o', e'} : Finset (Fin n))ᶜ.card = n - 2 := by
    rw [Finset.card_compl, Fintype.card_fin, hpairc]
  refine ggRootFusionWitnessAlt_of_innerU hc hle hδ hδp (S := ({o', e'} : Finset (Fin n))ᶜ)
    (μ := ζ) (fun i hi => ?_) (fun i hi => ?_) ?_ ?_ ?_ (i₁ := o') (by simp) (by omega) 1 ?_
  · simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact hval i hi.1 hi.2
  · simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or, not_and,
      not_not] at hi
    by_cases hio : i = o'
    · rw [hio, hδo]
      exact hne
    · rw [hi hio, hδe]
      exact hne
  · rw [compl_compl, hpairc, hcS]
    omega
  · rw [hcS]
    omega
  · rw [compl_compl, hpairc]
  · intro c hcl
    simp only [Equiv.Perm.one_apply]
    by_cases hc0 : (c : ℕ) = 0
    · have hco : c = o' := Fin.ext hc0
      have hce : Fin.rev c = e' := Fin.ext (by simp only [Fin.val_rev, he']; omega)
      rw [hce, hco, hδo, hδe]
    · rw [hval c (fun h => by rw [h] at hc0; exact hc0 rfl)
          (fun h => by rw [h] at hcl; simp only [he'] at hcl; omega),
        hval (Fin.rev c) (fun h => by
          have := congrArg Fin.val h
          simp only [Fin.val_rev, ho'] at this
          omega)
          (fun h => by
            have := congrArg Fin.val h
            simp only [Fin.val_rev, he'] at this
            omega)]

theorem ggRootFusionWitnessAlt_mid_twoU (hc : FrameCtxU p B Bs G₀ hF ψ P hP) (hle : G₀ ≤ M)
    {ζ : Fˣ} (hζ : orderOf ζ = p) {l : ℕ} (hl2 : 2 ≤ l) (hl : 2 * l + 2 ≤ n) :
    GGRootFusionWitnessAlt p Bs D E G₀ M t e r (ψ (ggInvSU (unitaryInvolution F 2 f) n l)) := by
  have hn5 := hc.five
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hζ
    exact hc.prime.one_lt.ne hζ
  set l' : Fin n := ⟨l, by omega⟩ with hl'
  set l1 : Fin n := ⟨l + 1, by omega⟩ with hl1
  have hll : l' ≠ l1 := by
    intro h
    have := congrArg Fin.val h
    simp only [hl', hl1] at this
    omega
  set δ : Fin n → Fˣ := Function.update (Function.update (fun _ => 1) l' ζ) l1 ζ⁻¹ with hδdef
  have hδ : ∏ i, δ i = 1 := by
    rw [hδdef, SLRep.prod_update_update_const hll, one_pow, mul_one, inv_mul_cancel]
  have hδ1 : δ l1 = ζ⁻¹ := by rw [hδdef, Function.update_self]
  have hδl : δ l' = ζ := by
    rw [hδdef, Function.update_of_ne hll, Function.update_self]
  have hval : ∀ i, i ≠ l' → i ≠ l1 → δ i = 1 := fun i hil hi1 => by
    rw [hδdef, Function.update_of_ne hi1, Function.update_of_ne hil]
  have hδp : ∀ i, δ i ^ p = 1 := by
    intro i
    by_cases hi1 : i = l1
    · rw [hi1, hδ1, inv_pow, hζp, inv_one]
    by_cases hil : i = l'
    · rw [hil, hδl, hζp]
    · rw [hval i hil hi1, one_pow]
  have hpairc : ({l', l1} : Finset (Fin n)).card = 2 := Finset.card_pair hll
  have hcS : ({l', l1} : Finset (Fin n))ᶜ.card = n - 2 := by
    rw [Finset.card_compl, Fintype.card_fin, hpairc]
  refine ggRootFusionWitnessAlt_of_innerU hc hle hδ hδp (S := ({l', l1} : Finset (Fin n))ᶜ)
    (μ := 1) (fun i hi => ?_) (fun i hi => ?_) ?_ ?_ ?_ (i₁ := l') (by simp) (by omega) 1 ?_
  · simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact hval i hi.1 hi.2
  · simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or, not_and,
      not_not] at hi
    by_cases hil : i = l'
    · rw [hil, hδl]
      exact hζ1
    · rw [hi hil, hδ1]
      exact inv_ne_one.mpr hζ1
  · rw [compl_compl, hpairc, hcS]
    omega
  · rw [hcS]
    omega
  · rw [compl_compl, hpairc]
  · intro c hcl
    simp only [Equiv.Perm.one_apply]
    rw [hval c (fun h => by rw [h] at hcl; simp only [hl'] at hcl; omega)
        (fun h => by rw [h] at hcl; simp only [hl1] at hcl; omega),
      hval (Fin.rev c) (fun h => by
          have := congrArg Fin.val h
          simp only [Fin.val_rev, hl'] at this
          omega)
        (fun h => by
          have := congrArg Fin.val h
          simp only [Fin.val_rev, hl1] at this
          omega)]

theorem ne_of_singleU (hc : FrameCtxU p B Bs G₀ hF ψ P hP) {b : G} (hb1 : b ≠ 1)
    {τ : Fin n → Fˣ} (hb : GGFrameActs (ggFrameU hF ψ P hP) b τ) {j : Fin n}
    (hconst : ∀ i i', i ≠ j → i' ≠ j → τ i = τ i') {i : Fin n} (hij : i ≠ j) : τ j ≠ τ i := by
  intro h
  apply hb1
  have hall : ∀ a, τ a = τ i := fun a => by
    by_cases ha : a = j
    · rw [ha, h]
    · exact hconst a i ha hij
  refine eq_of_act_eqU hc.centφ fun s => ?_
  rw [hb.apply hc.data, conjU_eq_of_ratio hc.data hb.1 (τ' := 1) (fun _ => by simp)
    (fun a c => by rw [hall a, hall c, mul_inv_cancel]; simp) s, conjU_one]
  simp

theorem ggRootFusionWitnessAlt_single_midU (hc : FrameCtxU p B Bs G₀ hF ψ P hP) (hle : G₀ ≤ M)
    {l : ℕ} (hl : 2 * l < n) {b₁ : G} (hb₁ : b₁ ∈ Bs)
    (hs : GGFrameSingleU (ggFrameU hF ψ P hP) b₁) :
    GGRootFusionWitnessAlt p Bs D E G₀ M t e r (ψ (ggInvSU (unitaryInvolution F 2 f) n l)) := by
  have hn5 := hc.five
  obtain ⟨hb1, τ₁, j, hact, hconst⟩ := hs
  obtain ⟨i, hij⟩ := SLRep.exists_ne_fin (by omega) j
  have hν := ne_of_singleU hc hb1 hact hconst hij
  set l' : Fin n := ⟨l, by omega⟩ with hl'
  have hcS : ({j} : Finset (Fin n))ᶜ.card = n - 1 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_singleton]
  refine ggRootFusionWitnessAlt_of_frameElt hc hle hb₁ hb1 hact (S := ({j} : Finset (Fin n))ᶜ)
    (μ := τ₁ i) (fun a ha => hconst a i (by simpa using ha) hij) (fun a ha => ?_) ?_ ?_ ?_
    (i₁ := j) (by simp) (by omega) (Equiv.swap j l') ?_
  · obtain rfl : a = j := by simpa using ha
    exact hν
  · rw [compl_compl, Finset.card_singleton, hcS]
    omega
  · rw [hcS]
    omega
  · rw [compl_compl, Finset.card_singleton]
    omega
  · intro c hcl
    have hcj : Equiv.swap j l' c ≠ j := by
      intro h
      rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h
      rw [h] at hcl
      simp only [hl'] at hcl
      omega
    have hrcj : Equiv.swap j l' (Fin.rev c) ≠ j := by
      intro h
      rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h
      have := congrArg Fin.val h
      simp only [Fin.val_rev, hl'] at this
      omega
    exact hconst _ _ hcj hrcj

theorem ggRootFusionWitnessAlt_single_pairU (hc : FrameCtxU p B Bs G₀ hF ψ P hP) (hle : G₀ ≤ M)
    {l : ℕ} (hl2 : 2 ≤ l) (hn : n = 2 * l) {b₁ : G} (hb₁ : b₁ ∈ Bs)
    (hs : GGFrameSingleU (ggFrameU hF ψ P hP) b₁) :
    GGRootFusionWitnessAlt p Bs D E G₀ M t e r (ψ (ggInvSU (unitaryInvolution F 2 f) n l)) := by
  have hn5 := hc.five
  obtain ⟨hb1, τ₁, j, hact, hconst⟩ := hs
  have hp := hc.prime
  have hp3 : 3 ≤ p := by have := hp.two_le; have := hc.odd; omega
  have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hc.odd
  obtain ⟨i, hij⟩ := SLRep.exists_ne_fin (by omega) j
  set μ := τ₁ i with hμ
  have hν := ne_of_singleU hc hb1 hact hconst hij
  have hval₁ : ∀ a, a ≠ j → τ₁ a = μ := fun a ha => hconst a i ha hij
  set ρ' := τ₁ j * μ⁻¹ with hρ'
  have hρp : ρ' ^ p = 1 := by
    rw [hρ', mul_pow, inv_pow, pow_eq_pow_of_frameActs hc.frameKer hc.data (by omega)
      (hc.bstar.2.1.2 b₁ hb₁) hact j i, mul_inv_cancel]
  have hρ1 : ρ' ≠ 1 := fun h => hν (mul_inv_eq_one.mp h)
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf ρ' = p := orderOf_eq_prime hρp hρ1
  set e₁ := ρ' ^ ((p - 1) / 2) with he₁
  set e₂ := ρ' ^ ((p + 1) / 2) with he₂
  have he12 : e₂ * e₁ = 1 := by
    rw [he₁, he₂, ← pow_add, show (p + 1) / 2 + (p - 1) / 2 = p by omega, hρp]
  have hτj : τ₁ j * e₁ = μ * e₂ := by
    have h1 : τ₁ j = μ * ρ' := by rw [hρ', mul_comm μ, mul_assoc, inv_mul_cancel, mul_one]
    rw [h1, he₁, he₂, mul_assoc, ← pow_succ', show (p - 1) / 2 + 1 = (p + 1) / 2 by omega]
  have he2 : e₂ ≠ 1 := by
    intro h
    have hdvd := orderOf_dvd_of_pow_eq_one h
    rw [hord] at hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hνμ : μ * e₂ ≠ μ := fun h => he2 (mul_left_cancel (h.trans (mul_one μ).symm))
  set o' : Fin n := ⟨0, by omega⟩ with ho'
  set e' : Fin n := ⟨n - 1, by omega⟩ with he'
  have hoe : o' ≠ e' := by
    intro h
    have := congrArg Fin.val h
    simp only [ho', he'] at this
    omega
  have hreo : Fin.rev o' = e' := Fin.ext (by simp only [Fin.val_rev, ho', he'])
  set σ : Equiv.Perm (Fin n) := Equiv.swap j o' with hσ
  set j₂ := σ e' with hj₂
  have hσj : σ j = o' := Equiv.swap_apply_left j o'
  have hσj₂ : σ j₂ = e' := Equiv.swap_apply_self j o' e'
  have hjj : j ≠ j₂ := by
    intro h
    apply hoe
    rw [← hσj, ← hσj₂, h]
  set δ : Fin n → Fˣ := Function.update (Function.update (fun _ => 1) j e₁) j₂ e₂ with hδdef
  have hδ : ∏ k, δ k = 1 := by
    rw [hδdef, SLRep.prod_update_update_const hjj, one_pow, mul_one, he12]
  have hδj₂ : δ j₂ = e₂ := by rw [hδdef, Function.update_self]
  have hδj : δ j = e₁ := by rw [hδdef, Function.update_of_ne hjj, Function.update_self]
  have hδo : ∀ a, a ≠ j → a ≠ j₂ → δ a = 1 := fun a haj ha2 => by
    rw [hδdef, Function.update_of_ne ha2, Function.update_of_ne haj]
  have hδp : ∀ k, δ k ^ p = 1 := by
    intro k
    by_cases h2 : k = j₂
    · rw [h2, hδj₂, he₂, ← pow_mul, mul_comm, pow_mul, hρp, one_pow]
    by_cases h1 : k = j
    · rw [h1, hδj, he₁, ← pow_mul, mul_comm, pow_mul, hρp, one_pow]
    · rw [hδo k h1 h2, one_pow]
  have hnorm : ∀ k, (δ k : F) ^ (2 ^ f + 1) = 1 := fun k => hc.norm_of_pow_eq_one (hδp k)
  set d : ↥(unitarySU 2 f F n) := ⟨diagHom n δ, diagHom_mem_unitarySU' hc.data hnorm hδ⟩
    with hd
  have hdδ : (d : GL (Fin n) F) = diagHom n δ := rfl
  have hdp : d ^ p = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, hdδ, ← map_pow]
    have : δ ^ p = 1 := funext hδp
    rw [this, map_one, Subgroup.coe_one]
  have hdBs := mem_of_frame_inner hc.bstar hc.data hc.frame hdδ hdp
  have hact₂ := hact.mul hc.data (frameActs_map (ggFrameU hF ψ P hP) hdδ hnorm)
  set τ₂ : Fin n → Fˣ := τ₁ * δ with hτ₂
  have hv₂ : ∀ a, a ≠ j → a ≠ j₂ → τ₂ a = μ := fun a haj ha2 => by
    rw [hτ₂, Pi.mul_apply, hval₁ a haj, hδo a haj ha2, mul_one]
  have hvj : τ₂ j = μ * e₂ := by rw [hτ₂, Pi.mul_apply, hδj, hτj]
  have hvj₂ : τ₂ j₂ = μ * e₂ := by
    rw [hτ₂, Pi.mul_apply, hδj₂, hval₁ j₂ (Ne.symm hjj)]
  have hpairc : ({j, j₂} : Finset (Fin n)).card = 2 := Finset.card_pair hjj
  have hcS : ({j, j₂} : Finset (Fin n))ᶜ.card = n - 2 := by
    rw [Finset.card_compl, Fintype.card_fin, hpairc]
  obtain ⟨i₀, hi₀⟩ : (({j, j₂} : Finset (Fin n))ᶜ).Nonempty :=
    Finset.card_pos.mp (by rw [hcS]; omega)
  have hi₀' : i₀ ≠ j ∧ i₀ ≠ j₂ := by simpa using hi₀
  have hb₂1 : b₁ * ggFrameU hF ψ P hP d ≠ 1 :=
    ne_one_of_frameActs hc.frameKer hc.data (by omega) hact₂ (i := j) (j := i₀)
      (by rw [hvj, hv₂ i₀ hi₀'.1 hi₀'.2]; exact hνμ)
  refine ggRootFusionWitnessAlt_of_frameElt hc hle (Bs.mul_mem hb₁ hdBs) hb₂1 hact₂
    (S := ({j, j₂} : Finset (Fin n))ᶜ) (μ := μ) (fun a ha => ?_) (fun a ha => ?_) ?_ ?_ ?_
    (i₁ := j) (by simp) (by omega) σ ?_
  · have ha' : a ≠ j ∧ a ≠ j₂ := by simpa using ha
    exact hv₂ a ha'.1 ha'.2
  · have ha'' : ¬a = j → a = j₂ := by simpa using ha
    rcases or_iff_not_imp_left.mpr ha'' with rfl | rfl
    · rw [hvj]
      exact hνμ
    · rw [hvj₂]
      exact hνμ
  · rw [compl_compl, hpairc, hcS]
    omega
  · rw [hcS]
    omega
  · rw [compl_compl, hpairc]
  · intro c hcl
    by_cases hc0 : c = o'
    · rw [hc0, hreo, Equiv.swap_apply_right, ← hj₂, hvj, hvj₂]
    · have hσc_j : σ c ≠ j := fun h => hc0 (by
        rw [hσ, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h
        exact h)
      have hσc_j₂ : σ c ≠ j₂ := fun h => by
        have h' : c = e' := σ.injective (h.trans hj₂)
        rw [h'] at hcl
        simp only [he'] at hcl
        omega
      have hrc_o : Fin.rev c ≠ o' := fun h => by
        have := congrArg Fin.val h
        simp only [Fin.val_rev, ho'] at this
        omega
      have hrc_e : Fin.rev c ≠ e' := fun h => hc0 (by
        rw [← hreo] at h
        exact Fin.rev_injective h)
      have hσrc_j : σ (Fin.rev c) ≠ j := fun h => hrc_o (by
        rw [hσ, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h
        exact h)
      have hσrc_j₂ : σ (Fin.rev c) ≠ j₂ := fun h => hrc_e (σ.injective (h.trans hj₂))
      rw [hv₂ _ hσc_j hσc_j₂, hv₂ _ hσrc_j hσrc_j₂]

theorem ggRootFusionWitnessAlt_odd_nosingleU (hc : FrameCtxU p B Bs G₀ hF ψ P hP)
    (hle : G₀ ≤ M) {ζ : Fˣ} (hζ : orderOf ζ = p) {l : ℕ} (hn : n = 2 * l + 1) (h7 : 7 ≤ n)
    (hns : ∀ b ∈ Bs, ¬ GGFrameSingleU (ggFrameU hF ψ P hP) b) :
    GGRootFusionWitnessAlt p Bs D E G₀ M t e r (ψ (ggInvSU (unitaryInvolution F 2 f) n l)) := by
  have hp := hc.prime
  have hp3 : 3 ≤ p := by have := hp.two_le; have := hc.odd; omega
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hζ
    exact hp.one_lt.ne hζ
  have hζ2 : ζ⁻¹ ^ 2 ≠ 1 := by
    rw [inv_pow, inv_ne_one]
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hζ] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  set o' : Fin n := ⟨0, by omega⟩ with ho'
  set l' : Fin n := ⟨l, by omega⟩ with hl'
  set e' : Fin n := ⟨n - 1, by omega⟩ with he'
  have hol : o' ≠ l' := by
    intro h; have := congrArg Fin.val h; simp only [ho', hl'] at this; omega
  have hoe : o' ≠ e' := by
    intro h; have := congrArg Fin.val h; simp only [ho', he'] at this; omega
  have hle' : l' ≠ e' := by
    intro h; have := congrArg Fin.val h; simp only [hl', he'] at this; omega
  set δ : Fin n → Fˣ := Function.update (Function.update (Function.update (fun _ => (1 : Fˣ)) o'
    ζ) l' (ζ⁻¹ ^ 2)) e' ζ with hδdef
  have hδ : ∏ i, δ i = 1 := by
    rw [hδdef, SLRep.prod_update_update_update_one hol hoe hle', inv_pow]
    group
  have hδe : δ e' = ζ := by rw [hδdef, Function.update_self]
  have hδl : δ l' = ζ⁻¹ ^ 2 := by
    rw [hδdef, Function.update_of_ne hle', Function.update_self]
  have hδo : δ o' = ζ := by
    rw [hδdef, Function.update_of_ne hoe, Function.update_of_ne hol, Function.update_self]
  have hval : ∀ i, i ≠ o' → i ≠ l' → i ≠ e' → δ i = 1 := fun i hio hil hie => by
    rw [hδdef, Function.update_of_ne hie, Function.update_of_ne hil, Function.update_of_ne hio]
  have hδp : ∀ i, δ i ^ p = 1 := by
    intro i
    by_cases hie : i = e'
    · rw [hie, hδe, hζp]
    by_cases hil : i = l'
    · rw [hil, hδl]
      exact inv_pow_pow_eq_oneU hζp 2
    by_cases hio : i = o'
    · rw [hio, hδo, hζp]
    · rw [hval i hio hil hie, one_pow]
  set T : Finset (Fin n) := {o', l', e'} with hT
  have hTc : T.card = 3 := by
    rw [hT, Finset.card_insert_of_notMem (by simp [hol, hoe]), Finset.card_pair hle']
  have hcS : Tᶜ.card = n - 3 := by rw [Finset.card_compl, Fintype.card_fin, hTc]
  have hmemT : ∀ i, i ∉ Tᶜ ↔ (i = o' ∨ i = l' ∨ i = e') := fun i => by
    rw [Finset.mem_compl, not_not, hT, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_singleton]
  obtain ⟨i₀, hi₀⟩ : Tᶜ.Nonempty := Finset.card_pos.mp (by rw [hcS]; omega)
  have hi₀' : i₀ ≠ o' ∧ i₀ ≠ l' ∧ i₀ ≠ e' := by simpa [hT] using hi₀
  have hnorm : ∀ k, (δ k : F) ^ (2 ^ f + 1) = 1 := fun k => hc.norm_of_pow_eq_one (hδp k)
  set d : ↥(unitarySU 2 f F n) := ⟨diagHom n δ, diagHom_mem_unitarySU' hc.data hnorm hδ⟩
    with hd
  have hdδ : (d : GL (Fin n) F) = diagHom n δ := rfl
  have hdp : d ^ p = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, hdδ, ← map_pow]
    have : δ ^ p = 1 := funext hδp
    rw [this, map_one, Subgroup.coe_one]
  have hbBs := mem_of_frame_inner hc.bstar hc.data hc.frame hdδ hdp
  have hb := frameActs_map (ggFrameU hF ψ P hP) hdδ hnorm
  have hb1 := ne_one_of_frameActs hc.frameKer hc.data (by omega) hb (i := o') (j := i₀)
    (by rw [hδo, hval i₀ hi₀'.1 hi₀'.2.1 hi₀'.2.2]; exact hζ1)
  have hbound := card_le_of_frameU_of_not_single hp hc.dvdF hc.data (by omega) hc.frameKer
    hc.centφ (X := Bs ⊓ Subgroup.centralizer
      (((TableBUE.blockSU (K := F) (n := f) Tᶜ).map (ggFrameU hF ψ P hP) : Subgroup G) : Set G))
    (fun c hc' => hc.bstar.2.1.2 c hc'.1) (fun c hc' => hc.frame c hc'.1) (S := Tᶜ) (i₀ := i₀)
    (fun c hc' τ' hτ' i hi =>
      const_of_mem_centralizer_blockSU hc.frameKer hc.data (by omega) hc'.2 hτ' hi₀ i hi)
    (fun c hc' => hns c hc'.1) (j₀ := o') (by simp [hT])
  rw [compl_compl, hTc] at hbound
  refine ggRootFusionWitnessAlt_of_frameElt_bound hc hle hbBs hb1 hb (S := Tᶜ) (μ := 1)
    (fun i hi => ?_) (fun i hi => ?_) ?_ ?_ (i₁ := o') (by simp [hT]) hbound (by omega) 1 ?_
  · have hi' : i ≠ o' ∧ i ≠ l' ∧ i ≠ e' := by simpa [hT] using hi
    exact hval i hi'.1 hi'.2.1 hi'.2.2
  · rcases (hmemT i).mp hi with rfl | rfl | rfl
    · rw [hδo]; exact hζ1
    · rw [hδl]; exact hζ2
    · rw [hδe]; exact hζ1
  · rw [compl_compl, hTc, hcS]
    omega
  · rw [hcS]
    omega
  · intro c hcl
    simp only [Equiv.Perm.one_apply]
    by_cases hc0 : (c : ℕ) = 0
    · have hco : c = o' := Fin.ext hc0
      have hce : Fin.rev c = e' := Fin.ext (by simp only [Fin.val_rev, he']; omega)
      rw [hce, hco, hδo, hδe]
    · rw [hval c (fun h => by rw [h] at hc0; exact hc0 rfl)
          (fun h => by rw [h] at hcl; simp only [hl'] at hcl; omega)
          (fun h => by rw [h] at hcl; simp only [he'] at hcl; omega),
        hval (Fin.rev c)
          (fun h => by
            have := congrArg Fin.val h
            simp only [Fin.val_rev, ho'] at this
            omega)
          (fun h => by
            have := congrArg Fin.val h
            simp only [Fin.val_rev, hl'] at this
            omega)
          (fun h => by
            have := congrArg Fin.val h
            simp only [Fin.val_rev, he'] at this
            omega)]

end SURep

end CFSG.StandardType
