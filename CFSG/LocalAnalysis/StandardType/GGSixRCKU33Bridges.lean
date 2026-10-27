module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKU33Transport
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MILabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIBase
public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeCent
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVQuot
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.Rest
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderE6Order
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneFieldRoot
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HG2InnMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelativePairInputs
public import CFSG.RankThree.PartOne.KF.F128Count
public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoSporadicOpen
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142TInd
public import CFSG.LocalAnalysis.StandardType.GGStructSOneHolds

public section

namespace CFSG.StandardType.RCKU33

open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

section Group

theorem mem_centralizer_of_conj_mul_center {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (hL : commutator ↥L = ⊤) {g : X}
    (hg : ∀ l ∈ L, ∃ z ∈ L, (∀ m ∈ L, z * m = m * z) ∧ g * l * g⁻¹ = l * z) :
    g ∈ Subgroup.centralizer (L : Set X) := by
  have hcomm : ∀ a ∈ L, ∀ b ∈ L, g * ⁅a, b⁆ * g⁻¹ = ⁅a, b⁆ := by
    intro a ha b hb
    obtain ⟨z₁, hz₁L, hz₁, ha'⟩ := hg a ha
    obtain ⟨z₂, hz₂L, hz₂, hb'⟩ := hg b hb
    have e : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    rw [e, ha', hb']
    exact CFSG.HardMathSupport.Solomon.Coordinator.commutatorElement_mul_mul'
      (hz₁ b hb) (hz₁ z₂ hz₂L) (hz₂ a ha)
  let F : Subgroup ↥L :=
    { carrier := {l | g * (l : X) * g⁻¹ = l}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, Subgroup.coe_mul] at ha hb ⊢
        calc g * ((a : X) * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
          _ = a * b := by rw [ha, hb]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq, Subgroup.coe_inv] at ha ⊢
        calc g * (a : X)⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
          _ = (a : X)⁻¹ := by rw [ha] }
  have hF : commutator ↥L ≤ F := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    show g * ⁅(a : X), (b : X)⁆ * g⁻¹ = ⁅(a : X), (b : X)⁆
    exact hcomm a a.2 b b.2
  rw [hL] at hF
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h1 : g * l * g⁻¹ = l := hF (Subgroup.mem_top ⟨l, hl⟩)
  calc l * g = (g * l * g⁻¹) * g := by rw [h1]
    _ = g * l := by group

theorem u33_glaPPrimeCore_le_center {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {L : Subgroup X}
    (hLq : CFSG.Open.IsQuasisimple ↥L) (hpL : p ∣ Nat.card ↥L) :
    CFSG.Open.GLAPPrimeCore p ↥L ≤ Subgroup.center ↥L := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hLq' : CFSG.IsQuasisimple ↥L :=
    ⟨⟨hLq.1⟩, hLq.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hLq⟩
  refine (CFSG.LocalCores.quasisimple_normal_subgroups hLq' inferInstance).resolve_left ?_
  intro htop
  have hc : Nat.Coprime p (Nat.card (CFSG.pPrimeCore p ↥L)) := CFSG.pPrimeCore_coprime_card
  have : Nat.card (CFSG.pPrimeCore p ↥L) = Nat.card ↥L := by
    show Nat.card (CFSG.Open.GLAPPrimeCore p ↥L) = _
    rw [htop, Subgroup.card_top]
  rw [this] at hc
  exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc hpL)

theorem u33_mem_centralizer_of_centMod {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {L : Subgroup X}
    (hLq : CFSG.Open.IsQuasisimple ↥L) (hpL : p ∣ Nat.card ↥L) {g : X}
    (hgN : g ∈ Subgroup.normalizer (L : Set X))
    (hcm : ∀ l ∈ L, ⁅l, g⁆ ∈ CFSG.Open.GLAPPrimeCoreOf p L) :
    g ∈ Subgroup.centralizer (L : Set X) := by
  refine mem_centralizer_of_conj_mul_center hLq.1 fun l hl => ?_
  have hgl : g * l * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hgN l).1 hl
  set z := l⁻¹ * (g * l * g⁻¹) with hz
  have hzL : z ∈ L := L.mul_mem (L.inv_mem hl) hgl
  have hzc : z ∈ CFSG.Open.GLAPPrimeCoreOf p L := by
    have := hcm l⁻¹ (L.inv_mem hl)
    have e : ⁅l⁻¹, g⁆ = z := by rw [hz, commutatorElement_def]; group
    rwa [e] at this
  have hzZ := u33_glaPPrimeCore_le_center hp hLq hpL ((chev_mem_glaPPrimeCoreOf_iff hzL).1 hzc)
  refine ⟨z, hzL, fun m hm => ?_, by rw [hz]; group⟩
  exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hzZ ⟨m, hm⟩).symm)

theorem center_eq_ker_chevQuotHom {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {L : Subgroup X}
    (hLq : CFSG.Open.IsQuasisimple ↥L) (hpL : p ∣ Nat.card ↥L) :
    Subgroup.center ↥L = (chevQuotHom p L).ker := by
  apply le_antisymm
  · intro z hz
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk' (Subgroup.center (PQuot p L))) (pQuotHom p L z) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    intro q
    obtain ⟨l, rfl⟩ := pQuotHom_surjective p L q
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz l)]
  · have hLq' : CFSG.IsQuasisimple ↥L :=
      ⟨⟨hLq.1⟩, hLq.2,
        CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hLq⟩
    refine
    (CFSG.LocalCores.quasisimple_normal_subgroups hLq' (chevQuotHom p L).normal_ker).resolve_left ?_
    intro htop
    have hab : ∀ a b : PQuot p L, a * b = b * a := by
      intro a b
      obtain ⟨l, rfl⟩ := pQuotHom_surjective p L a
      have hl0 : l ∈ (chevQuotHom p L).ker := htop ▸ Subgroup.mem_top l
      have hl : (QuotientGroup.mk' (Subgroup.center (PQuot p L))) (pQuotHom p L l) = 1 :=
        MonoidHom.mem_ker.1 hl0
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff] at hl
      exact (hl b).symm
    have hperf : commutator (PQuot p L) = ⊤ := by
      have h := congrArg (Subgroup.map (pQuotHom p L)) hLq.1
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _
        (pQuotHom_surjective p L)] at h
      rw [commutator_def]; exact h
    have hbot : commutator (PQuot p L) = ⊥ := by
      rw [eq_bot_iff, commutator_def]
      refine Subgroup.commutator_le.2 fun a _ b _ => ?_
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hab a b
    have hcore : CFSG.Open.GLAPPrimeCore p ↥L = ⊤ := by
      rw [eq_top_iff]
      intro l _
      have h1 : (pQuotHom p L l) ∈ (⊤ : Subgroup (PQuot p L)) := Subgroup.mem_top _
      rw [← hperf, hbot, Subgroup.mem_bot] at h1
      rw [← ker_pQuotHom]
      exact h1
    have hZ : Subgroup.center ↥L = ⊤ :=
      eq_top_iff.2 (hcore ▸ u33_glaPPrimeCore_le_center hp hLq hpL)
    haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hLq.2
    obtain ⟨q, hq⟩ := exists_ne (1 : ↥L ⧸ Subgroup.center ↥L)
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) q
    exact hq ((QuotientGroup.eq_one_iff _).2 (hZ ▸ Subgroup.mem_top l))

@[expose] noncomputable def u33_centerQuotEquivPSimple {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {L : Subgroup X}
    (hLq : CFSG.Open.IsQuasisimple ↥L) (hpL : p ∣ Nat.card ↥L) :
    ↥L ⧸ Subgroup.center ↥L ≃* PSimple p L :=
  (QuotientGroup.quotientMulEquivOfEq (center_eq_ker_chevQuotHom hp hLq hpL)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (chevQuotHom_surjective p L))

end Group

section Counting

theorem card_eq_of_le_of_card_sq {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {D H : Subgroup X} (hHD : H ≤ D)
    (hD : Nat.card ↥D = p ^ 2) : Nat.card ↥H = 1 ∨ Nat.card ↥H = p ∨ Nat.card ↥H = p ^ 2 := by
  have hdvd : Nat.card ↥H ∣ p ^ 2 := hD ▸ Subgroup.card_dvd_of_le hHD
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  interval_cases k <;> simp_all

theorem u33_inf_centralizer_eq {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {D L : Subgroup X}
    (hD : Nat.card ↥D = p ^ 2)
    {x d : X} (hxD : x ∈ D) (hx1 : x ≠ 1) (hxL : x ∈ Subgroup.centralizer (L : Set X))
    (hdD : d ∈ D) (hdL : d ∉ Subgroup.centralizer (L : Set X)) :
    L ⊓ Subgroup.centralizer (D : Set X) = L ⊓ Subgroup.centralizer ({d} : Set X) := by
  apply le_antisymm
  · exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hdD))
  · rintro l ⟨hlL, hld⟩
    refine ⟨hlL, ?_⟩
    have hK₁H : D ⊓ Subgroup.centralizer (L : Set X) ≤ D ⊓ Subgroup.centralizer ({l} : Set X) :=
      fun y hy => ⟨hy.1, Subgroup.mem_centralizer_iff.2 fun m hm => by
        rw [Set.mem_singleton_iff.1 hm]; exact ((Subgroup.mem_centralizer_iff.1 hy.2) l hlL)⟩
    have hdH : d ∈ D ⊓ Subgroup.centralizer ({l} : Set X) := ⟨hdD, Subgroup.mem_centralizer_iff.2
      fun m hm => by
        rw [Set.mem_singleton_iff.1 hm]
        exact ((Subgroup.mem_centralizer_iff.1 hld) d rfl).symm⟩
    have hdK₁ : d ∉ D ⊓ Subgroup.centralizer (L : Set X) := fun h => hdL h.2
    have hxK₁ : x ∈ D ⊓ Subgroup.centralizer (L : Set X) := ⟨hxD, hxL⟩
    have hK₁p : Nat.card ↥(D ⊓ Subgroup.centralizer (L : Set X)) = p := by
      rcases card_eq_of_le_of_card_sq hp inf_le_left hD with h | h | h
      · exfalso
        rw [Subgroup.card_eq_one.1 h, Subgroup.mem_bot] at hxK₁
        exact hx1 hxK₁
      · exact h
      · exfalso
        have heq := Subgroup.eq_of_le_of_card_ge
          (inf_le_left : D ⊓ Subgroup.centralizer (L : Set X) ≤ D) (by rw [h, hD])
        apply hdK₁
        rw [heq]
        exact hdD
    have hHD : D ⊓ Subgroup.centralizer ({l} : Set X) = D := by
      rcases card_eq_of_le_of_card_sq hp
          (inf_le_left : D ⊓ Subgroup.centralizer ({l} : Set X) ≤ D) hD with h | h | h
      · exfalso
        rw [Subgroup.card_eq_one.1 h, Subgroup.mem_bot] at hdH
        rw [hdH] at hdK₁
        exact hdK₁ (Subgroup.one_mem _)
      · exfalso
        have heq := Subgroup.eq_of_le_of_card_ge hK₁H (by rw [h, hK₁p])
        rw [← heq] at hdH
        exact hdK₁ hdH
      · exact Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hD])
    show l ∈ Subgroup.centralizer (D : Set X)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyH : y ∈ D ⊓ Subgroup.centralizer ({l} : Set X) := by rw [hHD]; exact hy
    exact ((Subgroup.mem_centralizer_iff.1 hyH.2) l rfl).symm

theorem u33_rank_bound {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {B₁ D J L : Subgroup X}
    (hD : Nat.card ↥D = p ^ 2)
    (hB₁J : B₁ ⊓ Subgroup.centralizer (J : Set X) = D) (hJL : J ≤ L) {d : X} (hdD : d ∈ D)
    (hdL : d ∉ Subgroup.centralizer (L : Set X)) (hB₁ : p ^ 4 ≤ Nat.card ↥B₁)
    (hcm : B₁ ⊓ centModSubgroup p L ≤ Subgroup.centralizer (L : Set X)) :
    p ^ 3 * Nat.card ↥(B₁ ⊓ centModSubgroup p L) ≤ Nat.card ↥B₁ := by
  set M := B₁ ⊓ centModSubgroup p L
  have hMD : M ≤ D := by
    rw [← hB₁J]
    exact fun g hg => ⟨hg.1, Subgroup.centralizer_le hJL (hcm hg)⟩
  have hM : Nat.card ↥M ≤ p := by
    rcases card_eq_of_le_of_card_sq hp hMD hD with h | h | h
    · rw [h]; exact hp.one_lt.le
    · exact h.le
    · exact absurd (hcm ((Subgroup.eq_of_le_of_card_ge hMD (by rw [h, hD])).symm ▸ hdD)) hdL
  calc p ^ 3 * Nat.card ↥M ≤ p ^ 3 * p := Nat.mul_le_mul_left _ hM
    _ = p ^ 4 := by ring
    _ ≤ Nat.card ↥B₁ := hB₁

theorem card_centerQuot_dvd {X : Type} [Group X] [Finite X] {J L : Subgroup X} (hJL : J ≤ L) :
    Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
  let f : ↥J →* ↥L ⧸ Subgroup.center ↥L :=
    (QuotientGroup.mk' (Subgroup.center ↥L)).comp (Subgroup.inclusion hJL)
  have hker : f.ker ≤ Subgroup.center ↥J := by
    intro j hj
    rw [Subgroup.mem_center_iff]
    intro g
    have hj' : Subgroup.inclusion hJL j ∈ Subgroup.center ↥L := by
      rw [← QuotientGroup.ker_mk' (Subgroup.center ↥L)]; exact hj
    have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hj' (Subgroup.inclusion hJL g))
    exact Subtype.ext this
  have h1 : Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ Nat.card (↥J ⧸ f.ker) := by
    rw [← Subgroup.index, ← Subgroup.index]
    exact Subgroup.index_dvd_of_le hker
  have h2 : Nat.card (↥J ⧸ f.ker) = Nat.card f.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  rw [h2] at h1
  exact h1.trans (Subgroup.card_subgroup_dvd_card f.range)

theorem not_derived_card {X : Type} [Group X] [Finite X] {L J : Subgroup X} {d : X}
    (hLq : CFSG.Open.IsQuasisimple ↥L)
    (hJL : J ≤ L) (hJd : J ≤ Subgroup.centralizer ({d} : Set X))
    (hdL : d ∉ Subgroup.centralizer (L : Set X)) (hJc : Nat.card (↥J ⧸ Subgroup.center ↥J) = 6048)
    (hL : Nat.card (↥L ⧸ Subgroup.center ↥L) = 6048 ∨
      Nat.card (↥L ⧸ Subgroup.center ↥L) = CFSG.Open.ordTits) : False := by
  have hdvd := card_centerQuot_dvd hJL
  rw [hJc] at hdvd
  rcases hL with hL | hL
  ·
    let f : ↥J →* ↥L ⧸ Subgroup.center ↥L :=
      (QuotientGroup.mk' (Subgroup.center ↥L)).comp (Subgroup.inclusion hJL)
    have hker : f.ker ≤ Subgroup.center ↥J := by
      intro j hj
      rw [Subgroup.mem_center_iff]
      intro g
      have hj' : Subgroup.inclusion hJL j ∈ Subgroup.center ↥L := by
        rw [← QuotientGroup.ker_mk' (Subgroup.center ↥L)]; exact hj
      have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hj' (Subgroup.inclusion hJL g))
      exact Subtype.ext this
    have h1 : 6048 ∣ Nat.card f.range := by
      rw [← hJc, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,
        ← Subgroup.index, ← Subgroup.index]
      exact Subgroup.index_dvd_of_le hker
    have h2 : Nat.card f.range ∣ 6048 := hL ▸ Subgroup.card_subgroup_dvd_card f.range
    have hrange : f.range = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [hL]; exact Nat.dvd_antisymm h2 h1
    have hdec : ∀ l : ↥L, ∃ j ∈ J, ∃ z : ↥L, z ∈ Subgroup.center ↥L ∧ (l : X) = j * z := by
      intro l
      obtain ⟨j, hj⟩ := hrange ▸ (Subgroup.mem_top (QuotientGroup.mk l : ↥L ⧸ Subgroup.center ↥L))
      refine ⟨j, j.2, (Subgroup.inclusion hJL j)⁻¹ * l, ?_, by simp⟩
      rw [← QuotientGroup.eq]
      exact hj
    have hcomm : ∀ a ∈ L, ∀ b ∈ L, ⁅a, b⁆ ∈ J := by
      intro a ha b hb
      obtain ⟨j₁, hj₁, z₁, hz₁, e₁⟩ := hdec ⟨a, ha⟩
      obtain ⟨j₂, hj₂, z₂, hz₂, e₂⟩ := hdec ⟨b, hb⟩
      have c1 : ∀ m : ↥L, Commute (z₁ : X) m := fun m =>
        (congrArg Subtype.val (Subgroup.mem_center_iff.1 hz₁ m)).symm
      have c2 : ∀ m : ↥L, Commute (z₂ : X) m := fun m =>
        (congrArg Subtype.val (Subgroup.mem_center_iff.1 hz₂ m)).symm
      simp only at e₁ e₂
      rw [e₁, e₂, CFSG.HardMathSupport.Solomon.Coordinator.commutatorElement_mul_mul'
        (c1 ⟨j₂, hJL hj₂⟩) (c1 z₂) (c2 ⟨j₁, hJL hj₁⟩)]
      show ⁅j₁, j₂⁆ ∈ J
      rw [commutatorElement_def]
      exact J.mul_mem (J.mul_mem (J.mul_mem hj₁ hj₂) (J.inv_mem hj₁)) (J.inv_mem hj₂)
    have hLJ : L ≤ J := by
      have hLL : (⁅L, L⁆ : Subgroup X) = L := by
        have h := congrArg (Subgroup.map L.subtype) hLq.1
        rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype] at h
        exact h
      rw [← hLL, Subgroup.commutator_le]
      exact fun a ha b hb => hcomm a ha b hb
    apply hdL
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact ((Subgroup.mem_centralizer_iff.1 (hJd (hLJ hl))) d rfl).symm
  · rw [hL, CFSG.LocalAnalysis.GLTheoremA.MI.ordTits_eq] at hdvd
    exact absurd hdvd (by norm_num)

end Counting

section Marking

theorem innDiagOn_or_derived
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) {L B₁ : Subgroup X}
    (hLq : CFSG.Open.IsQuasisimple ↥L) (hpL : p ∣ Nat.card ↥L)
    (hB₁N : B₁ ≤ Subgroup.normalizer (L : Set X))
    (hmark : CFSG.StandardType.LargeEvenMarking ↥L (fun _ _ _ I _ θ => ∀ b ∈ B₁, ∃ φ ∈ I,
      CFSG.Assembly.LargeEvenInduces θ (fun l l' => (l' : X) = b⁻¹ * l * b) φ)) :
    S10.InnDiagOn p B₁ L ∨
      ∃ lab : CFSG.Assembly.LargeEvenLabel, MI.DerivedLab lab ∧
        CFSG.StandardType.MarkedModel lab (↥L ⧸ Subgroup.center ↥L) := by
  obtain ⟨-, lab, hlab, hraw⟩ := CFSG.StandardType.largeEvenMarking_markedModel hmark
  by_cases hd : MI.DerivedLab lab
  · right
    obtain ⟨R, _, I, F, -, -, θ, -, hm⟩ := CFSG.StandardType.largeEvenRawDatum_exists hraw
    exact ⟨lab, hd, CFSG.StandardType.MarkedModel.of_mulEquiv θ.symm hm⟩
  · left
    have hraw' := (MI.rawDatum_iff_legacy hlab hd _).2 hraw
    have hperf : commutator (PQuot p L) = ⊤ := by
      have h := congrArg (Subgroup.map (pQuotHom p L)) hLq.1
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _
        (pQuotHom_surjective p L)] at h
      rw [commutator_def]; exact h
    refine ⟨hB₁N, hperf, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw'⟩
    rintro R _ I F ⟨hs, hna, θ, hP, -⟩
    refine ⟨hs, hna, (u33_centerQuotEquivPSimple hp hLq hpL).symm.trans θ, fun b hb => ?_⟩
    obtain ⟨φ, hφ, hind⟩ := hP b hb
    refine ⟨φ, hφ, ?_⟩
    rintro q q' ⟨l, l', rfl, rfl, hll'⟩
    have key : ∀ m : ↥L, (u33_centerQuotEquivPSimple hp hLq hpL).symm
        (QuotientGroup.mk (QuotientGroup.mk m : PQuot p L)) = QuotientGroup.mk m := fun m => by
      rw [MulEquiv.symm_apply_eq]; rfl
    simp only [MulEquiv.trans_apply, key]
    exact hind l l' hll'

end Marking

section Main

theorem isChevSimple_pSimple
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) {L : Subgroup X}
    (hLq : CFSG.Open.IsQuasisimple ↥L) (hpL : p ∣ Nat.card ↥L)
    {P : CFSG.Assembly.LargeEvenMarkProp ↥L} (hmark : CFSG.StandardType.LargeEvenMarking ↥L P) :
    IsChevSimple 2 (PSimple p L) := by
  have hcenQ : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.center_centerQuot_eq_bot hLq
  let e'' : ↥L ⧸ Subgroup.center ↥L ≃*
      (↥L ⧸ Subgroup.center ↥L) ⧸ Subgroup.center (↥L ⧸ Subgroup.center ↥L) :=
    ((QuotientGroup.quotientMulEquivOfEq hcenQ).trans QuotientGroup.quotientBot).symm
  have hperfQ : commutator (↥L ⧸ Subgroup.center ↥L) = ⊤ := by
    have h := congrArg (Subgroup.map (QuotientGroup.mk' (Subgroup.center ↥L))) hLq.1
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective _)] at h
    rw [commutator_def]; exact h
  have hmQ := CFSG.StandardType.ggLargeEvenMarking_of_centerQuot_equiv hperfQ e''
    (CFSG.StandardType.largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial) hmark)
  have hchevQ := CFSG.StandardType.isChevSimple_two_of_largeEvenMarking_of_isSimpleGroup hLq.2 hmQ
  have e := u33_centerQuotEquivPSimple hp hLq hpL
  rcases hchevQ with ⟨i, hi, ⟨f⟩⟩ | ⟨i, hi, ⟨f⟩⟩
  · exact Or.inl ⟨i, hi, ⟨e.symm.trans f⟩⟩
  · exact Or.inr ⟨i, hi, ⟨e.symm.trans f⟩⟩

theorem u33_card_ne_6048
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {G₀ A B₁ D J L : Subgroup X}
    (hA : CFSG.Open.IsElemAbelian p A) (hB₁A : B₁ ≤ A) (hDB₁ : D ≤ B₁)
    (hD : Nat.card ↥D = p ^ 2) (hB₁J : B₁ ⊓ Subgroup.centralizer (J : Set X) = D)
    (hB₁ : p ^ 4 ≤ Nat.card ↥B₁) (hB₁L : B₁ ≤ Subgroup.normalizer (L : Set X))
    (hmark : CFSG.StandardType.LargeEvenMarking ↥L (fun _ _ _ I _ θ => ∀ b ∈ B₁, ∃ φ ∈ I,
      CFSG.Assembly.LargeEvenInduces θ (fun l l' => (l' : X) = b⁻¹ * l * b) φ))
    (hLx : ∃ x ∈ D, x ≠ 1 ∧
      CFSG.Assembly.IsComponentOf L (G₀ ⊓ Subgroup.centralizer ({x} : Set X)))
    (hDL : ¬ D ≤ Subgroup.centralizer (L : Set X))
    (hJ : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set X)))
    (hpL : p ∣ Nat.card ↥L) :
    Nat.card (↥J ⧸ Subgroup.center ↥J) ≠ 6048 := by
  intro hJc
  obtain ⟨x, hxD, hx1, hLc⟩ := hLx
  have hLc' := CFSG.Assembly.isComponentOf_iff_open.1 hLc
  have hLq : CFSG.Open.IsQuasisimple ↥L := hLc'.2.2
  have hxL : x ∈ Subgroup.centralizer (L : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact ((Subgroup.mem_centralizer_iff.1 (hLc'.1 hl).2) x rfl).symm
  obtain ⟨d, hdD, hdL⟩ := Set.not_subset.1 hDL
  have hdB₁ : d ∈ B₁ := hDB₁ hdD
  have hJ' := CFSG.Assembly.isComponentOf_iff_open.1 hJ
  have hK : CFSG.Open.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set X)) := by
    rw [← u33_inf_centralizer_eq hp hD hxD hx1 hxL hdD hdL]; exact hJ'
  have hJL : J ≤ L := hJ'.1.trans inf_le_left
  have hJd : J ≤ Subgroup.centralizer ({d} : Set X) := hK.1.trans inf_le_right
  have hcm : ∀ g ∈ centModSubgroup p L, g ∈ Subgroup.centralizer (L : Set X) := fun g hg =>
    u33_mem_centralizer_of_centMod hp hLq hpL hg.1 hg.2
  have hyC : ¬ CentMod p L d := fun h => hdL (u33_mem_centralizer_of_centMod hp hLq hpL h.1
    fun l hl => h.2 (Subgroup.commutator_mem_commutator hl (Subgroup.mem_zpowers d)))
  have hrank := u33_rank_bound hp hD hB₁J hJL hdD hdL hB₁ (fun g hg => hcm g hg.2)
  have hAel : CFSG.Open.IsElemAbelian p B₁ :=
    ⟨⟨⟨fun a b => by
      have := congrArg Subtype.val (hA.1.is_comm.comm ⟨a, hB₁A a.2⟩ ⟨b, hB₁A b.2⟩)
      exact Subtype.ext this⟩⟩, fun y hy => hA.2 y (hB₁A hy)⟩
  have hchev := isChevSimple_pSimple hp hLq hpL hmark
  rcases innDiagOn_or_derived hp hLq hpL hB₁L hmark with hInn | ⟨lab, hd, hm⟩
  · exact I141F.i141DynkinAt_card_comp hp hp2 hchev hLq hAel hInn hrank hdB₁ hyC hK hJc
  · refine not_derived_card hLq hJL hJd hdL hJc ?_
    rcases hd with hg | ht
    · exact Or.inl (MI.card_markedModel_g2der hg hm)
    · exact Or.inr (MI.card_markedModel_twF4der ht hm)

end Main

end CFSG.StandardType.RCKU33
