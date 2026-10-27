module

public import CFSG.LocalAnalysis.StandardType.GGLemmaThreeThirteenBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section OrbitProd

variable {G : Type} [Group G]

@[expose] def ggOrbitProd (f k : G) : ℕ → G
  | 0 => 1
  | n + 1 => ggOrbitProd f k n * (f ^ n * k * (f ^ n)⁻¹)

theorem ggOrbitProd_succ (f k : G) (n : ℕ) :
    ggOrbitProd f k (n + 1) = ggOrbitProd f k n * (f ^ n * k * (f ^ n)⁻¹) := rfl

theorem ggOrbitProd_succ' (f k : G) (n : ℕ) :
    ggOrbitProd f k (n + 1) = k * (f * ggOrbitProd f k n * f⁻¹) := by
  induction n with
  | zero => simp [ggOrbitProd]
  | succ n ih =>
    have h1 : ggOrbitProd f k (n + 1 + 1) =
        k * (f * ggOrbitProd f k n * f⁻¹) * (f ^ (n + 1) * k * (f ^ (n + 1))⁻¹) := by
      rw [ggOrbitProd_succ, ih]
    rw [h1, ggOrbitProd_succ f k n, pow_succ']
    group

theorem ggOrbitProd_conj_mem (f k : G) {S : Subgroup G} :
    ∀ n : ℕ, (∀ i, 1 ≤ i → i ≤ n → f ^ i * k * (f ^ i)⁻¹ ∈ S) →
      f * ggOrbitProd f k n * f⁻¹ ∈ S
  | 0, _ => by simp [ggOrbitProd]
  | n + 1, hS => by
    have h1 := ggOrbitProd_conj_mem f k n (fun i hi hin => hS i hi (by omega))
    have h2 := hS (n + 1) (by omega) le_rfl
    have heq : f * ggOrbitProd f k (n + 1) * f⁻¹ =
        (f * ggOrbitProd f k n * f⁻¹) * (f ^ (n + 1) * k * (f ^ (n + 1))⁻¹) := by
      rw [ggOrbitProd_succ, pow_succ']
      group
    rw [heq]
    exact S.mul_mem h1 h2

theorem ggOrbitProd_mem_centralizer {f k : G} {n : ℕ} (hf : f ^ (n + 1) = 1)
    (hc : k * (f * ggOrbitProd f k n * f⁻¹) = (f * ggOrbitProd f k n * f⁻¹) * k) :
    ggOrbitProd f k (n + 1) ∈ Subgroup.centralizer {f} := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 : f * ggOrbitProd f k (n + 1) * f⁻¹ = (f * ggOrbitProd f k n * f⁻¹) * k := by
    rw [ggOrbitProd_succ]
    have hfk : f ^ (n + 1) * k * (f ^ (n + 1))⁻¹ = k := by rw [hf]; group
    calc f * (ggOrbitProd f k n * (f ^ n * k * (f ^ n)⁻¹)) * f⁻¹
        = (f * ggOrbitProd f k n * f⁻¹) * (f ^ (n + 1) * k * (f ^ (n + 1))⁻¹) := by
          rw [pow_succ']; group
      _ = (f * ggOrbitProd f k n * f⁻¹) * k := by rw [hfk]
  have h2 : ggOrbitProd f k (n + 1) = (f * ggOrbitProd f k n * f⁻¹) * k := by
    rw [ggOrbitProd_succ', hc]
  calc ggOrbitProd f k (n + 1) * f = (f * ggOrbitProd f k (n + 1) * f⁻¹) * f := by
        rw [h1, ← h2]
    _ = f * ggOrbitProd f k (n + 1) := by group

end OrbitProd

section Components

variable {G : Type} [Group G]

theorem ggIsComponent_conjSub {K : Subgroup G} (hK : CFSG.IsComponent K) (g : G) :
    CFSG.IsComponent (conjSub g K) :=
  CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hK

theorem ggCommute_of_isComponent_ne [Finite G] {K K' : Subgroup G} (hK : CFSG.IsComponent K)
    (hK' : CFSG.IsComponent K') (hne : K' ≠ K) {x y : G} (hx : x ∈ K') (hy : y ∈ K) :
    x * y = y * x := by
  rcases CFSG.LocalCores.distinct_components_commute hK' hK with h | h
  · exact absurd h hne
  · have hc : ⁅x, y⁆ ∈ ⁅K', K⁆ := Subgroup.commutator_mem_commutator hx hy
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc

theorem ggConj_mem_conjSub {K : Subgroup G} (g : G) {k : G} (hk : k ∈ K) :
    g * k * g⁻¹ ∈ conjSub g K :=
  ⟨k, hk, by simp [MulAut.conj_apply]⟩

theorem ggPow_not_mem_normalizer {p : ℕ} [hp : Fact p.Prime] {K : Subgroup G} {f : G}
    (hfp : f ^ p = 1) (hfK : f ∉ Subgroup.normalizer (K : Set G)) {i : ℕ} (hi : 1 ≤ i)
    (hip : i < p) : f ^ i ∉ Subgroup.normalizer (K : Set G) := by
  intro hfi
  have hf1 : f ≠ 1 := fun h1 => hfK (h1 ▸ Subgroup.one_mem _)
  have hord : orderOf f = p := orderOf_eq_prime hfp hf1
  have hfi1 : f ^ i ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (hord ▸ hip)
  have hmem := mem_zpowers_of_orderOf_prime (hord ▸ hp.out) (Subgroup.npow_mem_zpowers f i) hfi1
  exact hfK ((Subgroup.zpowers_le.mpr hfi) hmem)

theorem ggInv_mul_mem_normalizer_of_conjSub_eq {K : Subgroup G} {g h : G}
    (hgh : conjSub g K = conjSub h K) : h⁻¹ * g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change conjSub (h⁻¹ * g) K = K
  rw [conjSub_mul, hgh, conjSub_inv_conjSub]

end Components

section Main

variable {G : Type} [Group G] [Finite G] {p : ℕ} {H E : Subgroup G}

theorem ggOrbitProd_spec [Fact p.Prime] (h : GGControlsStrongFusion H E)
    (hE : IsElemAbelian p E) {K : Subgroup G} (hK : CFSG.IsComponent K) {f : G} (hfE : f ∈ E)
    (hfK : f ∉ Subgroup.normalizer (K : Set G)) {n : ℕ} (hn : p = n + 1) {k : G}
    (hk : k ∈ K) :
    ggOrbitProd f k (n + 1) ∈ H ∧
      f * ggOrbitProd f k n * f⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
  have hfp : f ^ p = 1 := hE.2 f hfE
  have hf1 : f ≠ 1 := fun h1 => hfK (h1 ▸ Subgroup.one_mem _)
  have hc : f * ggOrbitProd f k n * f⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
    refine ggOrbitProd_conj_mem f k n fun i hi hin => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hne : conjSub (f ^ i) K ≠ K := fun heq =>
      ggPow_not_mem_normalizer hfp hfK hi (by omega)
        (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq)
    exact (ggCommute_of_isComponent_ne hK (ggIsComponent_conjSub hK _) hne
      (ggConj_mem_conjSub (f ^ i) hk) hy).symm
  exact ⟨h.centralizer_le hfE hf1
    (ggOrbitProd_mem_centralizer (hn ▸ hfp) (Subgroup.mem_centralizer_iff.mp hc k hk)), hc⟩

theorem ggLemmaThreeThirteen_top [hp : Fact p.Prime] (h : GGControlsStrongFusion H E)
    (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2) {K : Subgroup G}
    (hK : CFSG.IsComponent K) (hKp : p ∣ Nat.card K) (hKH : ¬ K ≤ H) :
    E ≤ Subgroup.normalizer (K : Set G) := by
  by_contra hEK
  obtain ⟨f, hfE, hfK⟩ : ∃ f ∈ E, f ∉ Subgroup.normalizer (K : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hEK hcon
  obtain ⟨n, hn⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.out.one_lt; omega⟩
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hK.1.1
  by_cases hreg : ∃ e ∈ E, e ≠ 1 ∧ e ∈ Subgroup.normalizer (K : Set G)
  ·
    obtain ⟨e, heE, he1, heK⟩ := hreg
    have hYn : ((H ⊓ K).subgroupOf K).Normal := by
      rw [Subgroup.normal_subgroupOf_iff inf_le_right]
      intro y k hy hk
      obtain ⟨hδH, hc⟩ := ggOrbitProd_spec h hE hK hfE hfK hn hk
      have hcy := Subgroup.mem_centralizer_iff.mp hc y hy.2
      have hconj : ggOrbitProd f k (n + 1) * y * (ggOrbitProd f k (n + 1))⁻¹ =
          k * y * k⁻¹ := by
        rw [ggOrbitProd_succ']
        calc k * (f * ggOrbitProd f k n * f⁻¹) * y * (k * (f * ggOrbitProd f k n * f⁻¹))⁻¹
            = k * (y * (f * ggOrbitProd f k n * f⁻¹)) * (f * ggOrbitProd f k n * f⁻¹)⁻¹ *
                k⁻¹ := by rw [hcy]; group
          _ = k * y * k⁻¹ := by group
      refine ⟨?_, K.mul_mem (K.mul_mem hk hy.2) (K.inv_mem hk)⟩
      rw [← hconj]
      exact H.mul_mem (H.mul_mem hδH hy.1) (H.inv_mem hδH)
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hK.1 hYn with htop | hcen
    · apply hKH
      intro x hx
      have hx' : (⟨x, hx⟩ : K) ∈ (H ⊓ K).subgroupOf K := htop ▸ Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp hx').1
    · refine h.not_inf_le_centralizer hE heE he1 heK hK.1.1.commutator_eq_top hKp ?_
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hmem : (⟨y, hy.2⟩ : K) ∈ Subgroup.center K := hcen (Subgroup.mem_subgroupOf.mpr hy)
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hmem ⟨x, hx⟩)
  ·
    push Not at hreg
    obtain ⟨e, heE, he1⟩ := ggExists_ne_one_of_card hp.out hEcard
    have hep : e ^ p = 1 := hE.2 e heE
    have hord : orderOf e = p := orderOf_eq_prime hep he1
    obtain ⟨g, hgE, hge⟩ : ∃ g ∈ E, g ∉ Subgroup.zpowers e := by
      by_contra hcon
      push Not at hcon
      have hle := Subgroup.card_le_of_le (show E ≤ Subgroup.zpowers e from hcon)
      rw [hEcard, Nat.card_zpowers, hord] at hle
      have hlt : p < p ^ 2 := by rw [sq]; nlinarith [hp.out.two_le]
      omega
    have hg1 : g ≠ 1 := fun h1 => hge (h1 ▸ Subgroup.one_mem _)
    have hgord : orderOf g = p := orderOf_eq_prime (hE.2 g hgE) hg1
    have heK := hreg e heE he1
    have hgK := hreg g hgE hg1
    have hdist : ∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n →
        conjSub (e ^ i) K ≠ conjSub (g ^ j) K := by
      intro i j hi hin hj hjn heq
      have hmem := ggInv_mul_mem_normalizer_of_conjSub_eq heq
      have hE' : (g ^ j)⁻¹ * e ^ i ∈ E :=
        E.mul_mem (E.inv_mem (E.pow_mem hgE j)) (E.pow_mem heE i)
      by_cases h1 : (g ^ j)⁻¹ * e ^ i = 1
      · have hgj : g ^ j = e ^ i := inv_mul_eq_one.mp h1
        have hgj1 : g ^ j ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
        have hgmem := mem_zpowers_of_orderOf_prime (hgord ▸ hp.out)
          (Subgroup.npow_mem_zpowers g j) hgj1
        rw [hgj] at hgmem
        exact hge ((Subgroup.zpowers_le.mpr (Subgroup.npow_mem_zpowers e i)) hgmem)
      · exact hreg _ hE' h1 hmem
    have hkey : ∀ k ∈ K, ∀ l ∈ K, ⁅k, l⁆ ∈ H := by
      intro k hk l hl
      obtain ⟨hδe, hae⟩ := ggOrbitProd_spec h hE hK heE heK hn hk
      obtain ⟨hδg, hbg⟩ := ggOrbitProd_spec h hE hK hgE hgK hn hl
      set a := e * ggOrbitProd e k n * e⁻¹ with ha_def
      set b := g * ggOrbitProd g l n * g⁻¹ with hb_def
      have hb : b ∈ ⨆ (j : ℕ) (_ : 1 ≤ j ∧ j ≤ n), conjSub (g ^ j) K :=
        ggOrbitProd_conj_mem g l n fun j hj hjn =>
          (le_iSup₂ (f := fun (j : ℕ) (_ : 1 ≤ j ∧ j ≤ n) => conjSub (g ^ j) K) j ⟨hj, hjn⟩)
            (ggConj_mem_conjSub (g ^ j) hl)
      have ha : a ∈ ⨅ (j : ℕ) (_ : 1 ≤ j ∧ j ≤ n),
          Subgroup.centralizer (conjSub (g ^ j) K : Set G) := by
        refine ggOrbitProd_conj_mem e k n fun i hi hin => ?_
        rw [Subgroup.mem_iInf]
        intro j
        rw [Subgroup.mem_iInf]
        intro hj
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (ggCommute_of_isComponent_ne (ggIsComponent_conjSub hK _)
          (ggIsComponent_conjSub hK _) (hdist i j hi hin hj.1 hj.2)
          (ggConj_mem_conjSub (e ^ i) hk) hy).symm
      have hab : a * b = b * a := by
        have hle : (⨆ (j : ℕ) (_ : 1 ≤ j ∧ j ≤ n), conjSub (g ^ j) K) ≤
            Subgroup.centralizer {a} := by
          refine iSup₂_le fun j hj => ?_
          intro y hy
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subgroup.mem_centralizer_iff.mp
            ((Subgroup.mem_iInf.mp ((Subgroup.mem_iInf.mp ha) j)) hj) y hy
        exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hb)).symm
      have hal : a * l = l * a := (Subgroup.mem_centralizer_iff.mp hae l hl).symm
      have hbk : b * k⁻¹ = k⁻¹ * b :=
        (show Commute b k from (Subgroup.mem_centralizer_iff.mp hbg k hk).symm).inv_right.eq
      have hcomm : ⁅k * a, l * b⁆ = ⁅k, l⁆ := by
        simp only [commutatorElement_def]
        calc k * a * (l * b) * (k * a)⁻¹ * (l * b)⁻¹
            = k * (a * l) * b * a⁻¹ * k⁻¹ * b⁻¹ * l⁻¹ := by group
          _ = k * l * (a * b) * a⁻¹ * k⁻¹ * b⁻¹ * l⁻¹ := by rw [hal]; group
          _ = k * l * (b * k⁻¹) * b⁻¹ * l⁻¹ := by rw [hab]; group
          _ = k * l * k⁻¹ * l⁻¹ := by rw [hbk]; group
      rw [← hcomm, ← ggOrbitProd_succ' e k n, ← ggOrbitProd_succ' g l n,
        commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem hδe hδg) (H.inv_mem hδe)) (H.inv_mem hδg)
    apply hKH
    rw [← hperf]
    exact Subgroup.commutator_le.mpr hkey

end Main

section Transfer

variable {G : Type} [Group G]

theorem GGControlsStrongFusionIn.mem_of_conj_mem {X H E : Subgroup G}
    (h : GGControlsStrongFusionIn X H E) {e : G} (he : e ∈ E) (he1 : e ≠ 1) {g : G}
    (hgX : g ∈ X) (hg : g⁻¹ * e * g ∈ H) : g ∈ H := by
  refine h.2.2 g hgX fun hbot => he1 ?_
  have hmem : g⁻¹ * e * g ∈ E.map (MulAut.conj g⁻¹).toMonoidHom ⊓ H :=
    Subgroup.mem_inf.mpr ⟨⟨e, he, by simp⟩, hg⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  calc e = g * (g⁻¹ * e * g) * g⁻¹ := by group
    _ = 1 := by rw [hmem]; group

theorem GGControlsStrongFusionIn.subgroupOf {X H E : Subgroup G}
    (h : GGControlsStrongFusionIn X H E) :
    GGControlsStrongFusion (H.subgroupOf X) (E.subgroupOf X) := by
  refine ggControlsStrongFusion_iff.mpr ⟨fun x hx => ?_, fun e he he1 g hg => ?_⟩
  · exact Subgroup.mem_subgroupOf.mpr (h.1 (Subgroup.mem_subgroupOf.mp hx))
  · have he1' : (e : G) ≠ 1 := fun h1 => he1 (Subtype.ext h1)
    have hg' : (g : G)⁻¹ * e * g ∈ H := by
      have := Subgroup.mem_subgroupOf.mp hg
      simpa using this
    exact Subgroup.mem_subgroupOf.mpr
      (h.mem_of_conj_mem (Subgroup.mem_subgroupOf.mp he) he1' g.2 hg')

theorem ggMem_normalizer_of_subgroupOf {X K : Subgroup G} (hKX : K ≤ X) {g : X}
    (hg : g ∈ Subgroup.normalizer (K.subgroupOf X : Set X)) :
    (g : G) ∈ Subgroup.normalizer (K : Set G) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hKX] at hg
  exact Subgroup.mem_subgroupOf.mp hg

theorem ggLe_map_pPrimeCore {p : ℕ} {X K : Subgroup G} (hKX : K ≤ X)
    (h : K.subgroupOf X ≤ CFSG.pPrimeCore p ↥X) :
    K ≤ (CFSG.pPrimeCore p ↥X).map X.subtype := by
  rw [← Subgroup.map_subgroupOf_eq_of_le hKX]
  exact Subgroup.map_mono h

end Transfer

theorem ggLemmaThreeThirteenPInput_holds : GGLemmaThreeThirteenPInput := by
  intro G _ _ p hp _ X H E _ hE hEcard hfus K hK hKO hKH
  have : Fact p.Prime := ⟨hp⟩
  have hEX : E ≤ X := hfus.1.trans hfus.2.1
  have hKX : K ≤ X := hK.1
  have hEcard' : Nat.card (E.subgroupOf X) = p ^ 2 := by
    rw [← hEcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv
  have hK' : CFSG.IsComponent (K.subgroupOf X) :=
    (isComponentOf_iff_isComponent_subgroupOf hKX).mp hK
  have hKp' : p ∣ Nat.card (K.subgroupOf X) := by
    by_contra hnd
    exact hKO (ggLe_map_pPrimeCore hKX (ggLe_pPrimeCore_of_isSubnormal hK'.2 hnd))
  have hKH' : ¬ K.subgroupOf X ≤ H.subgroupOf X := fun hle =>
    hKH (CFSG.LocalCores.le_of_subgroupOf_le hKX hle)
  have hN := ggLemmaThreeThirteen_top hfus.subgroupOf (ggIsElemAbelian_subgroupOf hE X)
    hEcard' hK' hKp' hKH'
  intro e he
  exact ggMem_normalizer_of_subgroupOf hKX
    (hN (Subgroup.mem_subgroupOf.mpr he : (⟨e, hEX he⟩ : X) ∈ E.subgroupOf X))

end CFSG.StandardType
