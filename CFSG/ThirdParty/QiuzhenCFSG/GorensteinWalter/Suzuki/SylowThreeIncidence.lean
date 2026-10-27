module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.SylowThreeCount
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Sylow-3 incidence through `U`

The normalizer `Ĥ = N_G(U)` acts on the Sylow 3-subgroups of `G`.  This
module exposes the small incidence interface used by the odd-graph
reconstruction: the four Sylow 3-subgroups containing `U` form one
`Ĥ`-orbit, and the Sylow 3-subgroups lying inside `Ĥ` are exactly those
containing `U`.

The proofs are orbit--stabilizer calculations built on the count/fibre
modules; they deliberately do not import the Sylow-join recognition core.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The orbit of a Sylow 3-subgroup `P` under the conjugation action of a
subgroup `K` has size `[K : K ∩ N_G(P)]`. -/
public theorem sylow3_orbit_card
    {G : Type u} [Group G] [Finite G]
    (K : Subgroup G) (P : Sylow 3 G) :
    Nat.card (MulAction.orbit (↥K) P) =
      ((K ⊓ Subgroup.normalizer (P : Set G) : Subgroup G).subgroupOf K).index := by
  classical
  have hcardOrbit : Nat.card (MulAction.orbit (↥K) P) =
      (MulAction.stabilizer (↥K) P).index := by
    calc
      Nat.card (MulAction.orbit (↥K) P) =
          Nat.card (↥K ⧸ MulAction.stabilizer (↥K) P) :=
            Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (↥K) P)
      _ = (MulAction.stabilizer (↥K) P).index :=
            (MulAction.stabilizer (↥K) P).index_eq_card.symm
  rw [hcardOrbit]
  congr 1
  ext x
  rw [MulAction.mem_stabilizer_iff]
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    exact ⟨x.2, Sylow.smul_eq_iff_mem_normalizer.mp hx⟩
  · intro hx
    exact Sylow.smul_eq_iff_mem_normalizer.mpr hx.2

/-- A Sylow 3-subgroup containing `U` centralizes `U` (groups of order
`p²` are commutative). -/
private lemma sylow3_le_centralizer_U
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (d : FirstCaseCountData c)
    (P : Sylow 3 G) (hPU : c.U ≤ (P : Subgroup G)) :
    (P : Subgroup G) ≤ Subgroup.centralizer (c.U : Set G) := by
  intro p hp
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hP9' : Nat.card P = 3 ^ 2 := by
    simpa using firstCase_sylow3_card_nine c d P
  have : IsMulCommutative P :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hP9'
  exact (congrArg Subtype.val
    (((IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hP9').is_comm).comm
      ⟨p, hp⟩ ⟨u, hPU hu⟩)).symm

/-- A Sylow 3-subgroup containing `U` lies in `Ĥ = N_G(U)`. -/
private lemma sylow3_le_hhat
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c)
    (P : Sylow 3 G) (hPU : c.U ≤ (P : Subgroup G)) :
    (P : Subgroup G) ≤ c.Hhat := by
  have hPleC := sylow3_le_centralizer_U c d P hPU
  have hCleN : Subgroup.centralizer (c.U : Set G) ≤ Subgroup.normalizer (c.U : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro u
    rw [Subgroup.mem_centralizer_iff] at hx
    constructor
    · intro hu
      have hxu : x * u * x⁻¹ = u := by
        have hc := hx u hu
        calc
          x * u * x⁻¹ = u * x * x⁻¹ := by rw [hc]
          _ = u := by group
      simpa [hxu] using hu
    · intro hu
      have hxuv : x * (x * u * x⁻¹) = (x * u * x⁻¹) * x := (hx (x * u * x⁻¹) hu).symm
      have hxv' : (x * u * x⁻¹) * x⁻¹ = x⁻¹ * (x * u * x⁻¹) := by
        calc
          (x * u * x⁻¹) * x⁻¹ = x⁻¹ * (x * (x * u * x⁻¹)) * x⁻¹ := by group
          _ = x⁻¹ * ((x * u * x⁻¹) * x) * x⁻¹ := by rw [hxuv]
          _ = x⁻¹ * (x * u * x⁻¹) := by group
      have hxv : x⁻¹ * (x * u * x⁻¹) = (x * u * x⁻¹) * x⁻¹ := hxv'.symm
      have h_eq : u = x * u * x⁻¹ := by
        calc
          u = x⁻¹ * (x * u * x⁻¹) * x := by group
          _ = (x * u * x⁻¹) * x⁻¹ * x := by rw [hxv]
          _ = x * u * x⁻¹ := by group
      rw [h_eq]
      exact hu
  have hklein : IsKleinFour (pCore 2 c.Hhat) := firstCase_twoCore_isKleinFour hmin c hfirst
  have hVK : IsKleinFour (twoCoreOf c.Hhat) := firstCase_klein_V_klein c hklein
  have hO2 : twoCoreOf c.Hhat ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card (twoCoreOf c.Hhat) = 1 := by rw [hbot]; simp
    have hfour : Nat.card (twoCoreOf c.Hhat) = 4 := hVK.card_four
    omega
  have hUne : c.U ≠ ⊥ := (lemma_2_2 hmin c).2
  have hNorm : Subgroup.normalizer (c.U : Set G) = c.Hhat :=
    theorem26_normalizer_U_eq_Hhat hmin c hO2 hUne
  exact hPleC.trans (hCleN.trans (le_of_eq hNorm))

/-- `|Ĥ| = 72` from `[G : Ĥ] = 35` and `|G| = 2520`. -/
private lemma hhat_card
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (d : FirstCaseCountData c) :
    Nat.card (↥c.Hhat) = 72 := by
  rcases firstCase_index_card_of_countData c d with ⟨hHidx, hGcard⟩
  have hm := c.Hhat.index_mul_card
  rw [hHidx, hGcard] at hm
  have hm' : 35 * Nat.card (↥c.Hhat) = 35 * 72 := by
    rw [hm]
    norm_num
  exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 35) (by
    exact hm')

/-- If a subgroup `H` contains a Sylow 3-subgroup `P`, then the number of
Sylow 3-subgroups of `H` is the relative index `[N_G(P) : N_G(P) ∩ H]`. -/
private lemma sylow3_count_eq_relIndex
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G)
    (P : Sylow 3 G) (hPleH : (P : Subgroup G) ≤ H) :
    Nat.card (Sylow 3 (↥H)) =
      (Subgroup.normalizer (((P : Subgroup G) : Set G))).relIndex H := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Q : Sylow 3 (↥H) := P.subtype hPleH
  have hQ : (Q : Subgroup (↥H)) = (P : Subgroup G).subgroupOf H := by
    exact Sylow.coe_subtype P hPleH
  have hQset : (Q : Set (↥H)) = (((P : Subgroup G).subgroupOf H) : Set (↥H)) := by
    exact congrArg (fun S : Subgroup (↥H) => (S : Set (↥H))) hQ
  have hnorm : Subgroup.normalizer (Q : Set (↥H)) =
      (Subgroup.normalizer (((P : Subgroup G) : Set G))).subgroupOf H := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    rw [hQset]
    rw [Subgroup.mem_normalizer_iff]
    have hmemP : (x : G) ∈ Subgroup.normalizer (((P : Subgroup G) : Set G)) ↔
        ∀ g : G, g ∈ (P : Subgroup G) ↔ (x : G) * g * (x : G)⁻¹ ∈ (P : Subgroup G) :=
      Subgroup.mem_normalizer_iff
    rw [hmemP]
    constructor
    · intro hx g
      constructor
      · intro hgP
        have hx' := hx (⟨g, hPleH hgP⟩ : ↥H)
        have hleft : (⟨g, hPleH hgP⟩ : ↥H) ∈ (P : Subgroup G).subgroupOf H := by
          rw [Subgroup.mem_subgroupOf]
          exact hgP
        have hz : x * (⟨g, hPleH hgP⟩ : ↥H) * x⁻¹ ∈ (P : Subgroup G).subgroupOf H :=
          hx'.mp hleft
        rw [Subgroup.mem_subgroupOf] at hz
        change (x : G) * g * (x : G)⁻¹ ∈ P
        exact hz
      · intro hg'
        have hgH : g ∈ H := by
          have hxmem : (x : G) ∈ H := x.2
          have hxg : (x : G) * g * (x : G)⁻¹ ∈ H := hPleH hg'
          have hg_eq : g = (x : G)⁻¹ * ((x : G) * g * (x : G)⁻¹) * (x : G) := by
            group
          rw [hg_eq]
          exact H.mul_mem (H.mul_mem (H.inv_mem hxmem) hxg) x.2
        have hx' := hx (⟨g, hgH⟩ : ↥H)
        have hright : x * (⟨g, hgH⟩ : ↥H) * x⁻¹ ∈ (P : Subgroup G).subgroupOf H := by
          rw [Subgroup.mem_subgroupOf]
          change (x : G) * g * (x : G)⁻¹ ∈ P
          exact hg'
        have hz : (⟨g, hgH⟩ : ↥H) ∈ (P : Subgroup G).subgroupOf H := hx'.mpr hright
        rw [Subgroup.mem_subgroupOf] at hz
        exact hz
    · intro hxR h
      constructor
      · intro hh
        rw [Subgroup.mem_subgroupOf] at hh ⊢
        simpa using ((hxR (h : G)).mp hh)
      · intro hh
        rw [Subgroup.mem_subgroupOf] at hh ⊢
        simpa using ((hxR (h : G)).mpr hh)
  have hcard := Q.card_eq_index_normalizer
  rw [hnorm] at hcard
  change Nat.card (Sylow 3 (↥H)) =
    (Subgroup.normalizer (((P : Subgroup G) : Set G))).relIndex H
  exact hcard

/-- For a Sylow 3-subgroup `P` containing `U`, the intersection
`N_G(P) ∩ Ĥ` has order 18: `n₃(Ĥ) = [Ĥ : N_G(P) ∩ Ĥ] = 4`, because `Ĥ`
contains exactly the four Sylow 3-subgroups of `G` that contain `U`. -/
public theorem firstCase_normalizer_sylow3_inter_hhat_card
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c)
    (P : Sylow 3 G) (hPU : c.U ≤ (P : Subgroup G)) :
    Nat.card ↥((Subgroup.normalizer (P : Set G)) ⊓ c.Hhat) = 18 := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup G := Subgroup.normalizer (P : Set G)
  have hPleH : (P : Subgroup G) ≤ c.Hhat := sylow3_le_hhat hmin c hfirst d P hPU
  have hn3 := sylow3_count_eq_relIndex c.Hhat P hPleH
  have hPrel : (P : Subgroup G).relIndex c.Hhat = 8 := by
    have hsub : ((P : Subgroup G).subgroupOf c.Hhat).index = 8 := by
      have hcardPsub : Nat.card ↥((P : Subgroup G).subgroupOf c.Hhat) = 9 := by
        exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPleH).toEquiv).trans
          (firstCase_sylow3_card_nine c d P)
      have hm := ((P : Subgroup G).subgroupOf c.Hhat).index_mul_card
      rw [hcardPsub, hhat_card c d] at hm
      norm_num at hm
      exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 9) (by
        rw [mul_comm 9 ((P : Subgroup G).subgroupOf c.Hhat).index]
        rw [hm])
    change (P : Subgroup G).relIndex c.Hhat = 8
    exact hsub
  have hrelDvd : N.relIndex c.Hhat ∣ 8 := by
    have hdvd := Subgroup.relIndex_dvd_of_le_left (H := (P : Subgroup G)) (K := N) (L := c.Hhat)
      ((P : Subgroup G).le_normalizer)
    rwa [hPrel] at hdvd
  have hn3ge4 : 4 ≤ Nat.card (Sylow 3 (↥c.Hhat)) := by
    let f : {Q : Sylow 3 G // c.U ≤ (Q : Subgroup G)} → Sylow 3 (↥c.Hhat) := fun Q =>
      Q.1.subtype (sylow3_le_hhat hmin c hfirst d Q.1 Q.2)
    have hf_inj : Function.Injective f := by
      intro Q R h
      apply Subtype.ext
      have hsub : (f Q : Subgroup (↥c.Hhat)) = (f R : Subgroup (↥c.Hhat)) :=
        congrArg (fun S : Sylow 3 (↥c.Hhat) => (S : Subgroup (↥c.Hhat))) h
      exact Sylow.subtype_injective (P := Q.1) (Q := R.1) (N := c.Hhat)
        (Sylow.ext hsub)
    have hle := Nat.card_le_card_of_injective f hf_inj
    have hfiber : Nat.card {Q : Sylow 3 G // c.U ≤ (Q : Subgroup G)} = 4 := by
      have hconj : conjugateSubgroup c.U (1 : G) = c.U := by
        rw [conjugateSubgroup]
        have h1 : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
          ext x
          simp
        rw [h1]
        exact Subgroup.map_id c.U
      simpa [hconj] using (firstCase_UConjugates_fiber_card hmin c hfirst d (1 : G))
    omega
  have hn3mod : Nat.card (Sylow 3 (↥c.Hhat)) % 3 = 1 := by
    have hm := (card_sylow_modEq_one 3 (↥c.Hhat) : Nat.card (Sylow 3 (↥c.Hhat)) ≡ 1 [MOD 3])
    change Nat.card (Sylow 3 (↥c.Hhat)) % 3 = 1 % 3 at hm
    norm_num at hm
    exact hm
  have hn3val : Nat.card (Sylow 3 (↥c.Hhat)) = 4 := by
    have hn3dvd : Nat.card (Sylow 3 (↥c.Hhat)) ∣ 8 := by
      rw [hn3]
      simpa [N] using hrelDvd
    rcases hn3dvd with ⟨m, hm⟩
    have hmle : m ≤ 8 := by
      rw [mul_comm] at hm
      exact Nat.le_of_dvd (by norm_num : 0 < 8) ⟨Nat.card (Sylow 3 (↥c.Hhat)), hm⟩
    interval_cases m <;> try omega
  have hrel4 : N.relIndex c.Hhat = 4 := by
    exact hn3.symm.trans hn3val
  let Nsub : Subgroup (↥c.Hhat) := N.subgroupOf c.Hhat
  have hNsubcard : Nat.card ↥Nsub = Nat.card ↥(N ⊓ c.Hhat) := by
    apply Nat.card_congr
    exact {
      toFun := fun x => ⟨(x.1 : G), ⟨x.2, x.1.2⟩⟩
      invFun := fun y => ⟨⟨(y : G), y.2.2⟩, y.2.1⟩
      left_inv := by
        intro x
        apply Subtype.ext
        rfl
      right_inv := by
        intro y
        apply Subtype.ext
        rfl }
  have hm := Nsub.index_mul_card
  change N.relIndex c.Hhat * Nat.card ↥Nsub = Nat.card (↥c.Hhat) at hm
  rw [hrel4, hNsubcard, hhat_card c d] at hm
  norm_num at hm
  have hm' : 4 * Nat.card {x : G // x ∈ N ∧ x ∈ c.Hhat} = 4 * 18 := by
    rw [hm]
  exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 4) (by
    exact hm')

/-- `Ĥ` acts transitively on the four Sylow 3-subgroups containing `U`. -/
public theorem firstCase_hhat_sylow3_orbit_card
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c)
    (P : Sylow 3 G) (hPU : c.U ≤ (P : Subgroup G)) :
    Nat.card (MulAction.orbit (↥c.Hhat) P) = 4 := by
  classical
  let NP : Subgroup G := Subgroup.normalizer (P : Set G)
  let D : Subgroup G := c.Hhat ⊓ NP
  have hOrbit : Nat.card (MulAction.orbit (↥c.Hhat) P) =
      (D.subgroupOf c.Hhat).index := by
    simpa [D, NP] using sylow3_orbit_card c.Hhat P
  have hDcard : Nat.card ↥D = 18 := by
    simpa [D, NP, inf_comm] using firstCase_normalizer_sylow3_inter_hhat_card
      hmin c hfirst d P hPU
  have hDsubcard : Nat.card ↥(D.subgroupOf c.Hhat) = 18 := by
    exact (Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : D ≤ c.Hhat)).toEquiv).trans hDcard
  have hHhatcard : Nat.card ↥c.Hhat = 72 := hhat_card c d
  have hmul := (D.subgroupOf c.Hhat).index_mul_card
  change (D.subgroupOf c.Hhat).index *
      Nat.card ↥(D.subgroupOf c.Hhat) = Nat.card ↥c.Hhat at hmul
  rw [hDsubcard, hHhatcard] at hmul
  rw [hOrbit]
  omega

/-- A Sylow 3-subgroup lies in the `Ĥ`-orbit of `P` exactly when it
contains `U`. -/
public theorem firstCase_hhat_sylow3_orbit_eq_containing
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c)
    (P : Sylow 3 G) (hPU : c.U ≤ (P : Subgroup G)) :
    ∀ Q : Sylow 3 G,
      Q ∈ MulAction.orbit (↥c.Hhat) P ↔ c.U ≤ (Q : Subgroup G) := by
  classical
  let NP : Subgroup G := Subgroup.normalizer (P : Set G)
  have hPH : (P : Subgroup G) ≤ c.Hhat := sylow3_le_hhat hmin c hfirst d P hPU
  have hNormU : Subgroup.normalizer (c.U : Set G) = c.Hhat := by
    have hklein : IsKleinFour (pCore 2 c.Hhat) :=
      firstCase_twoCore_isKleinFour hmin c hfirst
    have hO2 : twoCoreOf c.Hhat ≠ ⊥ := by
      intro hbot
      have hcard : Nat.card (twoCoreOf c.Hhat) = 1 := by rw [hbot]; simp
      have hfour : Nat.card (twoCoreOf c.Hhat) = 4 :=
        (firstCase_klein_V_klein c hklein).card_four
      omega
    exact theorem26_normalizer_U_eq_Hhat hmin c hO2 (lemma_2_2 hmin c).2
  intro Q
  constructor
  · intro hQ
    rcases hQ with ⟨h, rfl⟩
    change c.U ≤ (h • P : Sylow 3 G)
    intro u hu
    have hh : (h : G) ∈ c.Hhat := h.2
    have hhn : (h : G) ∈ Subgroup.normalizer (c.U : Set G) := by
      rw [hNormU]
      exact hh
    change u ∈ conjugateSubgroup (P : Subgroup G) (h : G)
    refine Subgroup.mem_map.mpr ⟨(h : G)⁻¹ * u * (h : G), ?_, ?_⟩
    · have hni : (h : G)⁻¹ ∈ Subgroup.normalizer (c.U : Set G) :=
        (Subgroup.normalizer (c.U : Set G)).inv_mem hhn
      have hu' := (Subgroup.mem_normalizer_iff.mp hni u).1 hu
      simpa using (hPU hu')
    · simp [MulAut.conj_apply]
      group
  · intro hQ
    have hQH : (Q : Subgroup G) ≤ c.Hhat := sylow3_le_hhat hmin c hfirst d Q hQ
    let P' : Sylow 3 (↥c.Hhat) := P.subtype hPH
    let Q' : Sylow 3 (↥c.Hhat) := Q.subtype hQH
    obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (↥c.Hhat) P' Q'
    refine ⟨h, ?_⟩
    have hh' := congrArg (fun R : Sylow 3 (↥c.Hhat) =>
      (R : Subgroup (↥c.Hhat))) hh
    rw [Sylow.smul_subtype hPH h] at hh'
    rw [Sylow.coe_subtype] at hh'
    have hle : (((h : G) • P : Sylow 3 G) : Subgroup G) ≤ c.Hhat := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨p, hp, rfl⟩
      exact c.Hhat.mul_mem (c.Hhat.mul_mem h.2 (hPH hp)) (c.Hhat.inv_mem h.2)
    have hinf : (((h : G) • P : Sylow 3 G) : Subgroup G) ⊓ c.Hhat =
        (Q : Subgroup G) ⊓ c.Hhat := by
      exact Subgroup.subgroupOf_inj.mp hh'
    apply Sylow.ext
    apply le_antisymm
    · intro x hx
      have hx' : x ∈ (((h : G) • P : Sylow 3 G) : Subgroup G) ⊓ c.Hhat :=
        ⟨hx, hle hx⟩
      rw [hinf] at hx'
      exact hx'.1
    · intro x hx
      have hx' : x ∈ (Q : Subgroup G) ⊓ c.Hhat := ⟨hx, hQH hx⟩
      rw [← hinf] at hx'
      exact hx'.1

/-- There are exactly four Sylow 3-subgroups containing `U`. -/
public theorem firstCase_sylow3_containing_U_card
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c)
    (P : Sylow 3 G) (hPU : c.U ≤ (P : Subgroup G)) :
    Nat.card {Q : Sylow 3 G // c.U ≤ (Q : Subgroup G)} = 4 := by
  classical
  let Ω := {Q : Sylow 3 G // c.U ≤ (Q : Subgroup G)}
  let O := MulAction.orbit (↥c.Hhat) P
  let e : Ω ≃ O :=
    { toFun := fun Q => ⟨Q.1, by
        rw [firstCase_hhat_sylow3_orbit_eq_containing hmin c hfirst d P hPU]
        exact Q.2⟩
      invFun := fun Q => ⟨Q.1, by
        exact (firstCase_hhat_sylow3_orbit_eq_containing hmin c hfirst d P hPU Q.1).mp Q.2⟩
      left_inv := by intro Q; rfl
      right_inv := by intro Q; rfl }
  calc
    Nat.card Ω = Nat.card O := Nat.card_congr e
    _ = 4 := firstCase_hhat_sylow3_orbit_card hmin c hfirst d P hPU

/-- A Sylow 3-subgroup of `Ĥ` is exactly one of the four subgroups through
`U`. -/
public theorem firstCase_sylow3_le_hhat_iff_contains_U
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c)
    (P : Sylow 3 G) (hPU : c.U ≤ (P : Subgroup G))
    (Q : Sylow 3 G) :
    (Q : Subgroup G) ≤ c.Hhat ↔ c.U ≤ (Q : Subgroup G) := by
  constructor
  · intro hQH
    have hPH : (P : Subgroup G) ≤ c.Hhat :=
      sylow3_le_hhat hmin c hfirst d P hPU
    let P' : Sylow 3 (↥c.Hhat) := P.subtype hPH
    let Q' : Sylow 3 (↥c.Hhat) := Q.subtype hQH
    obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (↥c.Hhat) P' Q'
    have hh' := congrArg (fun R : Sylow 3 (↥c.Hhat) =>
      (R : Subgroup (↥c.Hhat))) hh
    rw [Sylow.smul_subtype hPH h] at hh'
    rw [Sylow.coe_subtype] at hh'
    have hle : (((h : G) • P : Sylow 3 G) : Subgroup G) ≤ c.Hhat := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨p, hp, rfl⟩
      exact c.Hhat.mul_mem (c.Hhat.mul_mem h.2 (hPH hp)) (c.Hhat.inv_mem h.2)
    have hinf : (((h : G) • P : Sylow 3 G) : Subgroup G) ⊓ c.Hhat =
        (Q : Subgroup G) ⊓ c.Hhat := by
      exact Subgroup.subgroupOf_inj.mp hh'
    have hPQ : (h : G) • P = Q := by
      apply Sylow.ext
      apply le_antisymm
      · intro x hx
        have hx' : x ∈ (((h : G) • P : Sylow 3 G) : Subgroup G) ⊓ c.Hhat :=
          ⟨hx, hle hx⟩
        rw [hinf] at hx'
        exact hx'.1
      · intro x hx
        have hx' : x ∈ (Q : Subgroup G) ⊓ c.Hhat := ⟨hx, hQH hx⟩
        rw [← hinf] at hx'
        exact hx'.1
    exact (firstCase_hhat_sylow3_orbit_eq_containing hmin c hfirst d P hPU Q).mp
      ⟨h, hPQ⟩
  · exact sylow3_le_hhat hmin c hfirst d Q

end CFSG.GorensteinWalter
