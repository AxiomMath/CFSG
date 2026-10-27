module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FreeActionCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSevenExact
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSevenWitness
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUCardThree
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCountDerived
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCosetInvolution
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCosetFiberCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseJNCoset
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CosetInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCountData
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-!
# `12 ∣ b₄`: the `VU`-action on the `b₄`-cosets is free

For a coset contributing to `b₄`, restriction (7) gives the trivial
intersection `D ∩ VU = 1` (`D = Ĥ ∩ Ĥ^y`).  Conjugation by `b ∈ VU` maps
the coset to another coset with the same involution count, so `V × U` acts
on the `b₄`-cosets.  The stabilizer of a coset is `(VU) ∩ D = 1`, hence
`|VU| = 12` divides `b₄`.
-/

public theorem conj_involution
    {G : Type u} [Group G] {b x : G} (hx : IsInvolution x) :
    IsInvolution (b * x * b⁻¹) := by
  refine ⟨?_, ?_⟩
  · intro h
    apply hx.1
    calc
      x = b⁻¹ * (b * x * b⁻¹) * b := by group
      _ = 1 := by simp [h]
  · calc
      (b * x * b⁻¹) ^ 2 = (b * x * b⁻¹) * (b * x * b⁻¹) := by rw [pow_two]
      _ = b * (x * x) * b⁻¹ := by group
      _ = b * 1 * b⁻¹ := by
        rw [show x * x = 1 from (by simpa [pow_two] using hx.2)]
      _ = 1 := by group

@[expose] public def conjFiberEquiv
    {G : Type u} [Group G] (H : Subgroup G) {b : G} (hb : b ∈ H)
    (ω : G ⧸ H) :
    cosetInvolution_fiber H (QuotientGroup.mk (b * ω.out)) ≃
      cosetInvolution_fiber H ω :=
  { toFun := fun x => ⟨b⁻¹ * x.1 * b, by
      refine ⟨?_, ?_⟩
      · have hxI := conj_involution (b := b⁻¹) x.2.1
        simpa [inv_inv] using hxI
      · change cosetInvolution_proj H (b⁻¹ * x.1 * b) = ω
        unfold cosetInvolution_proj
        have hgoal : QuotientGroup.mk (s := H) ((b⁻¹ * x.1 * b)⁻¹) =
            QuotientGroup.mk (s := H) (ω.out) := by
          apply (QuotientGroup.eq (s := H)).mpr
          have hxmem : x.1 * b * ω.out ∈ H := by
            have hq := (QuotientGroup.eq (s := H)).mp x.2.2
            simpa [mul_assoc] using hq
          have hmain : (b⁻¹ * x.1 * b) * ω.out = b⁻¹ * (x.1 * b * ω.out) := by
            group
          have hmem : (b⁻¹ * x.1 * b) * ω.out ∈ H := by
            rw [hmain]
            exact H.mul_mem (H.inv_mem hb) hxmem
          simpa using hmem
        exact hgoal.trans (QuotientGroup.out_eq' (s := H) (a := ω))
⟩
    invFun := fun x => ⟨b * x.1 * b⁻¹, by
      refine ⟨?_, ?_⟩
      · exact conj_involution x.2.1
      · change cosetInvolution_proj H (b * x.1 * b⁻¹) =
          QuotientGroup.mk (b * ω.out)
        unfold cosetInvolution_proj
        apply (QuotientGroup.eq (s := H)).mpr
        have hxmem : x.1 * ω.out ∈ H := by
          have hq := (QuotientGroup.eq (s := H)).mp
            (x.2.2.trans (QuotientGroup.out_eq' (s := H) (a := ω)).symm)
          simpa using hq
        have hmain : (b * x.1 * b⁻¹) * (b * ω.out) = b * x.1 * ω.out := by
          group
        have hmem : (b * x.1 * b⁻¹) * (b * ω.out) ∈ H := by
          rw [hmain]
          rw [mul_assoc]
          exact H.mul_mem hb hxmem
        simpa using hmem⟩
    left_inv := by
      intro x
      apply Subtype.ext
      group
    right_inv := by
      intro x
      apply Subtype.ext
      group }

public theorem fiber_card_conj
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) {b : G} (hb : b ∈ H) (ω : G ⧸ H) :
    Nat.card (cosetInvolution_fiber H (QuotientGroup.mk (b * ω.out))) =
      Nat.card (cosetInvolution_fiber H ω) :=
  Nat.card_congr (conjFiberEquiv H hb ω)

public theorem fiber_card_smul
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) {b : G} (hb : b ∈ H) (q : G ⧸ H) :
    Nat.card (cosetInvolution_fiber H (b • q)) =
      Nat.card (cosetInvolution_fiber H q) := by
  have hq : QuotientGroup.mk (b * q.out) = b • q := by
    simpa using (MulAction.Quotient.mk_smul_out (b := b) (q := q))
  rw [← hq]
  exact fiber_card_conj H hb q

public theorem smul_base_iff
    {G : Type u} [Group G] (H : Subgroup G) {b : G} (hb : b ∈ H)
    (q : G ⧸ H) :
    b • q = cosetInvolution_base H ↔ q = cosetInvolution_base H := by
  constructor
  · intro h
    have hbq : QuotientGroup.mk (b * q.out) = b • q := by
      simpa using (MulAction.Quotient.mk_smul_out (b := b) (q := q))
    have hq' : QuotientGroup.mk (b * q.out) = cosetInvolution_base H := hbq.trans h
    unfold cosetInvolution_base at hq'
    have hq := (QuotientGroup.eq (s := H)).mp hq'
    have hq'' : (b * q.out)⁻¹ ∈ H := by simpa using hq
    have hmem' : q.out⁻¹ ∈ H := by
      rw [show q.out⁻¹ = (b * q.out)⁻¹ * b from (by group)]
      exact H.mul_mem hq'' hb
    have hmk : QuotientGroup.mk (q.out) = cosetInvolution_base H := by
      unfold cosetInvolution_base
      apply (QuotientGroup.eq (s := H)).mpr
      simpa using hmem'
    rw [← QuotientGroup.out_eq' (s := H) (a := q)]
    exact hmk
  · intro h
    rw [h]
    unfold cosetInvolution_base
    rw [MulAction.Quotient.smul_mk]
    apply (QuotientGroup.eq (s := H)).mpr
    have hm : (b * (1 : G)⁻¹)⁻¹ * (1 : G)⁻¹ ∈ H := by
      rw [show (b * (1 : G)⁻¹)⁻¹ * (1 : G)⁻¹ = b⁻¹ from (by group)]
      exact H.inv_mem hb
    simpa using hm

public theorem smul_base_ne
    {G : Type u} [Group G] (H : Subgroup G) {b : G} (hb : b ∈ H)
    {q : G ⧸ H} (hne : q ≠ cosetInvolution_base H) :
    b • q ≠ cosetInvolution_base H := by
  intro h
  exact hne ((smul_base_iff H hb q).mp h)

public theorem firstCase_klein_twelve_dvd_b4
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    (K : Subgroup G) (b0 b1 b2 b3 b4 : ℕ)
    (hKHall : IsHallIn K c.FU) (hKne : K ≠ ⊥)
    (hJn : ∀ n : ℕ, n ≤ 4 →
      Nat.card {x : G // x ∈ firstCaseJ c n} =
        n * firstCaseBn b0 b1 b2 b3 b4 n)
    (h8 : 3 * b4 + b2 = 6 * (Nat.card K) ^ 2)
    (h9 : 6 * Nat.card K + b4 = 3 * b0 + 2 * b1 + b2) :
    12 ∣ b4 := by
  classical
  have hUcard : Nat.card c.U = 3 :=
    firstCase_klein_U_card_three_of_count hmin c hfirst hklein K b0 b1 b2 b3 b4
      hKHall hKne hJn h8 h9
  have hKcard : Nat.card K = 3 :=
    firstCase_klein_K_card_eq_three_of_U_card_three c hKHall hKne hUcard
  have hKge2 : 2 ≤ Nat.card K := by
    have hpos : 0 < Nat.card K := Nat.card_pos
    have hne1 : Nat.card K ≠ 1 := by
      intro hc
      apply hKne
      exact Subgroup.eq_bot_of_card_eq K hc
    omega
  have h4ne : b4 ≠ 0 :=
    firstCase_klein_b4_ne_zero_of_equations (Nat.card K) b0 b1 b2 b4 h8 h9 hKge2
  let V : Subgroup G := twoCoreOf c.Hhat
  let U : Subgroup G := c.U
  let Ω : Type u := {ω : G ⧸ c.Hhat // ω ≠ cosetInvolution_base c.Hhat ∧
    Nat.card (cosetInvolution_fiber c.Hhat ω) = 4}
  have hVleH : V ≤ c.Hhat := by
    dsimp [V]
    exact Subgroup.map_subtype_le (pCore 2 c.Hhat)
  have hUleH : U ≤ c.Hhat := by
    dsimp [U]
    rw [(theorem_2_6 hmin c).1]
    exact Subgroup.map_subtype_le (pPrimeCore 2 c.Hhat)
  have hVUleHhat : ∀ v : V, ∀ u : U, (v : G) * (u : G) ∈ c.Hhat := by
    intro v u
    exact c.Hhat.mul_mem (hVleH v.2) (hUleH u.2)
  have hVU_comm : ∀ v : V, ∀ u : U,
      (v : G) * (u : G) = (u : G) * (v : G) := by
    intro v u
    have hVcent : V ≤ Subgroup.centralizer (c.U : Set G) := by
      have h26 := theorem_2_6 hmin c
      simpa [V, h26.1] using twoCoreOf_centralizes_oddCoreOf c.Hhat
    exact (Subgroup.mem_centralizer_iff.mp (hVcent v.2) (u : G) u.2).symm
  let φ : V × U →* G :=
    { toFun := fun vu => (vu.1 : G) * (vu.2 : G)
      map_one' := by simp
      map_mul' := by
        intro vu1 vu2
        change (vu1.1 : G) * (vu2.1 : G) * ((vu1.2 : G) * (vu2.2 : G)) =
          (vu1.1 : G) * (vu1.2 : G) * ((vu2.1 : G) * (vu2.2 : G))
        have hswap : (vu2.1 : G) * (vu1.2 : G) = (vu1.2 : G) * (vu2.1 : G) :=
          hVU_comm vu2.1 vu1.2
        calc
          (vu1.1 : G) * (vu2.1 : G) * ((vu1.2 : G) * (vu2.2 : G)) =
              (vu1.1 : G) * ((vu2.1 : G) * (vu1.2 : G)) * (vu2.2 : G) := by
                group
          _ = (vu1.1 : G) * ((vu1.2 : G) * (vu2.1 : G)) * (vu2.2 : G) := by
                rw [hswap]
          _ = (vu1.1 : G) * (vu1.2 : G) * ((vu2.1 : G) * (vu2.2 : G)) := by
                group }
  let : MulAction (V × U) (G ⧸ c.Hhat) := MulAction.compHom (G ⧸ c.Hhat) φ
  let : MulAction (V × U) Ω :=
    { smul := fun vu ω => ⟨vu • ω.1, by
        have hb : (φ vu : G) ∈ c.Hhat := by
          change (vu.1 : G) * (vu.2 : G) ∈ c.Hhat
          exact hVUleHhat vu.1 vu.2
        refine ⟨?_, ?_⟩
        · exact smul_base_ne c.Hhat hb ω.2.1
        · have hcard := fiber_card_smul c.Hhat hb ω.1
          change Nat.card (cosetInvolution_fiber c.Hhat ((φ vu : G) • ω.1)) = 4
          rw [hcard]
          exact ω.2.2⟩
      one_smul := by
        intro ω
        apply Subtype.ext
        change (1 : V × U) • ω.1 = ω.1
        simp
      mul_smul := by
        intro vu1 vu2 ω
        apply Subtype.ext
        change (vu1 * vu2) • ω.1 = vu1 • (vu2 • ω.1)
        rw [mul_smul] }
  have hfree : ∀ ω : Ω, ∀ vu : V × U, vu • ω = ω → vu = 1 := by
    intro ω vu hfix
    let b : G := (vu.1 : G) * (vu.2 : G)
    have hfix' : QuotientGroup.mk (b * ω.1.out) = ω.1 := by
      have hbq : QuotientGroup.mk (b * ω.1.out) = vu • ω.1 := by
        change QuotientGroup.mk ((φ vu : G) * ω.1.out) = (φ vu : G) • ω.1
        exact (MulAction.Quotient.mk_smul_out (b := (φ vu : G)) (q := ω.1))
      exact hbq.trans (congrArg Subtype.val hfix)
    have hfib4 : Nat.card (cosetInvolution_fiber c.Hhat ω.1) = 4 := ω.2.2
    have hpos : 0 < Nat.card (cosetInvolution_fiber c.Hhat ω.1) := by
      rw [hfib4]
      norm_num
    obtain ⟨z, hz⟩ := (Nat.card_pos_iff.mp hpos).1
    have hzI : IsInvolution (z : G) := hz.1
    have hzproj : cosetInvolution_proj c.Hhat (z : G) = ω.1 := hz.2
    have hzH : (z : G) ∉ c.Hhat := by
      intro hzh
      have hbase : cosetInvolution_proj c.Hhat (z : G) =
          cosetInvolution_base c.Hhat := by
        unfold cosetInvolution_proj cosetInvolution_base
        apply (QuotientGroup.eq (s := c.Hhat)).mpr
        simpa using hzh
      have hωbase : ω.1 = cosetInvolution_base c.Hhat := by
        rw [← hzproj]
        exact hbase
      exact ω.2.1 hωbase
    have hzcard : firstCaseCosetInvolutions c (z : G) = 4 := by
      rw [firstCase_coset_fiber_card_eq c hzI, hzproj, hfib4]
    have hzJ : (z : G) ∈ firstCaseJ c 4 := by
      change IsInvolution (z : G) ∧ (z : G) ∉ c.Hhat ∧
        firstCaseCosetInvolutions c (z : G) = 4
      exact ⟨hzI, hzH, hzcard⟩
    obtain ⟨w, hwJ, hproj, X, hXne, hXle, hXodd, hXinv, hC, hN⟩ :=
      firstCase_klein_restrictionSeven_witness_of_mem_J_four
        hmin c hfirst hklein hzJ
    have hprojω : cosetInvolution_proj c.Hhat w = ω.1 := hproj.trans hzproj
    have hprojω' : QuotientGroup.mk (s := c.Hhat) (w⁻¹) = ω.1 := by
      change cosetInvolution_proj c.Hhat w = ω.1
      exact hprojω
    have hmkout : QuotientGroup.mk (s := c.Hhat) (ω.1.out) =
        QuotientGroup.mk (s := c.Hhat) (w⁻¹) := by
      exact (QuotientGroup.out_eq' (s := c.Hhat) (a := ω.1)).trans hprojω'.symm
    have hb_left : QuotientGroup.mk (s := c.Hhat) (b * ω.1.out) =
        QuotientGroup.mk (s := c.Hhat) (b * w⁻¹) := by
      apply (QuotientGroup.eq (s := c.Hhat)).mpr
      have hmem := (QuotientGroup.eq (s := c.Hhat)).mp hmkout
      have hgoal : (b * ω.1.out)⁻¹ * (b * w⁻¹) ∈ c.Hhat := by
        rw [show (b * ω.1.out)⁻¹ * (b * w⁻¹) = ω.1.out⁻¹ * w⁻¹ from (by group)]
        exact hmem
      simpa using hgoal
    have hfix'' : QuotientGroup.mk (s := c.Hhat) (b * w⁻¹) =
        QuotientGroup.mk (s := c.Hhat) (w⁻¹) := by
      calc
        QuotientGroup.mk (s := c.Hhat) (b * w⁻¹) =
            QuotientGroup.mk (s := c.Hhat) (b * ω.1.out) := hb_left.symm
        _ = ω.1 := hfix'
        _ = QuotientGroup.mk (s := c.Hhat) (w⁻¹) := hprojω'.symm
    have hstab : w * b⁻¹ * w⁻¹ ∈ c.Hhat := by
      have hq := (QuotientGroup.eq (s := c.Hhat)).mp hfix''
      have hgoal : w * b⁻¹ * w⁻¹ ∈ c.Hhat := by
        rw [show w * b⁻¹ * w⁻¹ = (b * w⁻¹)⁻¹ * w⁻¹ from (by group)]
        exact hq
      simpa using hgoal
    have hbD : b ∈ c.Hhat ⊓ conjugateSubgroup c.Hhat w := by
      refine ⟨?_, ?_⟩
      · change (vu.1 : G) * (vu.2 : G) ∈ c.Hhat
        exact hVUleHhat vu.1 vu.2
      · change b ∈ conjugateSubgroup c.Hhat w
        have hbInvConj : b⁻¹ ∈ conjugateSubgroup c.Hhat w := by
          apply Subgroup.mem_map.mpr
          refine ⟨w * b⁻¹ * w⁻¹, hstab, ?_⟩
          have hwJ' : IsInvolution w := by
            simpa [firstCaseJ] using hwJ |>.1
          have hw2 : w * w = 1 := by simpa [pow_two] using hwJ'.2
          have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
          calc
            w * (w * b⁻¹ * w⁻¹) * w⁻¹ = (w * w) * b⁻¹ * (w⁻¹ * w⁻¹) := by group
            _ = 1 * b⁻¹ * 1 := by rw [hw2, hwinv, hw2]
            _ = b⁻¹ := by simp
        simpa using (conjugateSubgroup c.Hhat w).inv_mem hbInvConj
    have hbB : b ∈ twoCoreOf c.Hhat ⊔ c.U := by
      change (vu.1 : G) * (vu.2 : G) ∈ twoCoreOf c.Hhat ⊔ c.U
      exact Subgroup.mul_mem_sup vu.1.2 vu.2.2
    have hbN : b ∈ (c.Hhat ⊓ conjugateSubgroup c.Hhat w) ⊓
        (twoCoreOf c.Hhat ⊔ c.U) := ⟨hbD, hbB⟩
    have hNbot := firstCase_klein_restrictionSeven_N_eq_bot
      hmin c hfirst hklein hwJ (by norm_num : 4 ≤ 4)
      hXne hXle hXodd hXinv hC hN
    have hb1 : b = 1 := by
      change (c.Hhat ⊓ conjugateSubgroup c.Hhat w) ⊓
          (twoCoreOf c.Hhat ⊔ c.U) = ⊥ at hNbot
      rw [hNbot] at hbN
      exact Subgroup.mem_bot.mp hbN
    have hVUinf : V ⊓ U = ⊥ := by
      have hV4 : Nat.card V = 4 := (firstCase_klein_V_klein c hklein).card_four
      have hVUcop : Nat.Coprime (Nat.card V) (Nat.card U) := by
        rw [hV4, hUcard]
        norm_num
      have hdisj : Disjoint V U := Subgroup.disjoint_of_coprime_natCard hVUcop
      exact le_antisymm (disjoint_iff_inf_le.mp hdisj) bot_le
    have hv1 : (vu.1 : G) = 1 := by
      have hvu1U : (vu.1 : G) ∈ U := by
        have hvueq : (vu.1 : G) = ((vu.2 : G)⁻¹) := by
          calc
            (vu.1 : G) = (vu.1 : G) * (vu.2 : G) * (vu.2 : G)⁻¹ := by group
            _ = 1 * (vu.2 : G)⁻¹ := by
              rw [show (vu.1 : G) * (vu.2 : G) = 1 from hb1]
            _ = (vu.2 : G)⁻¹ := by simp
        rw [hvueq]
        exact U.inv_mem vu.2.2
      have hvinf : (vu.1 : G) ∈ V ⊓ U := ⟨vu.1.2, hvu1U⟩
      rw [hVUinf] at hvinf
      exact Subgroup.mem_bot.mp hvinf
    have hv2 : (vu.2 : G) = 1 := by
      have hvu2V : (vu.2 : G) ∈ V := by
        have hvueq : (vu.2 : G) = ((vu.1 : G)⁻¹) := by
          calc
            (vu.2 : G) = (vu.1 : G)⁻¹ * (vu.1 : G) * (vu.2 : G) := by group
            _ = (vu.1 : G)⁻¹ * 1 := by
              rw [mul_assoc, show (vu.1 : G) * (vu.2 : G) = 1 from hb1]
            _ = (vu.1 : G)⁻¹ := by simp
        rw [hvueq]
        exact V.inv_mem vu.1.2
      have hvinf : (vu.2 : G) ∈ V ⊓ U := ⟨hvu2V, vu.2.2⟩
      rw [hVUinf] at hvinf
      exact Subgroup.mem_bot.mp hvinf
    apply Prod.ext
    · apply Subtype.ext
      exact hv1
    · apply Subtype.ext
      exact hv2
  let : Fintype (V × U) := Fintype.ofFinite _
  let : Fintype Ω := Fintype.ofFinite _
  have hdvd : Nat.card (V × U) ∣ Nat.card Ω :=
    natCard_dvd_of_free_action (G := V × U) (X := Ω) hfree
  have hVUcard : Nat.card (V × U) = 12 := by
    rw [Nat.card_prod]
    have hV4 : Nat.card V = 4 := (firstCase_klein_V_klein c hklein).card_four
    rw [hV4, hUcard]
  have hΩ : Nat.card Ω = b4 := by
    have hb' : cosetInvolution_b c.Hhat 4 = b4 := by
      have hJ4card : Nat.card {x : G // x ∈ firstCaseJ c 4} =
          4 * cosetInvolution_b c.Hhat 4 := firstCase_J_n_card c 4
      have hJ4b : Nat.card {x : G // x ∈ firstCaseJ c 4} =
          4 * firstCaseBn b0 b1 b2 b3 b4 4 := by
        simpa using hJn 4 (by norm_num)
      have hmul : 4 * cosetInvolution_b c.Hhat 4 = 4 * b4 := by
        rw [← hJ4card, hJ4b]
        rfl
      omega
    rw [cosetInvolution_b_card] at hb'
    simpa [Ω, cosetInvolution_fiber] using hb'
  rw [hVUcard, hΩ] at hdvd
  simpa using hdvd

end CFSG.GorensteinWalter
