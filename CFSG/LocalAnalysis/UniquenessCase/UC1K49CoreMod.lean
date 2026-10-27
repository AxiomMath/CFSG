module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CoreDefs
public import CFSG.GroupTheory.ABGLocalTools.PStabilityModule
public import CFSG.LocalAnalysis.UniquenessCase.UC1K49Trivial

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49

open scoped commutatorElement IsMulCommutative
open CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem Q_le_H49 {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) : Q ≤ H :=
  h.Q_eq.le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)

theorem I_eq_sup_conjugates49 {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hxX : x ∈ X) (hxgen : X = Subgroup.zpowers x) :
    I = L ⊔ CFSG.conjugate L x ⊔ CFSG.conjugate L (x ^ 2) := by
  have hx2X : x ^ 2 ∈ X := X.pow_mem hxX 2
  have hord3 : orderOf x = 3 := by
    have hcard : Nat.card (Subgroup.zpowers x) = 3 := by rw [← hxgen]; exact h.card_X
    rwa [Nat.card_zpowers] at hcard
  set L1 := CFSG.conjugate L x with hL1
  set L2 := CFSG.conjugate L (x ^ 2) with hL2
  refine le_antisymm ?_ ?_
  · rw [h.I_eq]
    refine iSup_le fun y => iSup_le fun hy => ?_
    have hy' : y ∈ Subgroup.zpowers x := hxgen ▸ hy
    rcases mem_zpowers_of_orderOf_eq_three hord3 hy' with rfl | rfl | rfl
    · rw [conjugate_one]
      exact (le_sup_left : L ≤ L ⊔ L1).trans le_sup_left
    · exact (le_sup_right : L1 ≤ L ⊔ L1).trans le_sup_left
    · exact le_sup_right
  · refine sup_le (sup_le (le_I h) ?_) ?_
    · rw [show I = I49 L X from h.I_eq.trans (I49_eq L X).symm, I49]
      exact le_iSup (fun x : X => CFSG.conjugate L (x : G)) ⟨x, hxX⟩
    · rw [show I = I49 L X from h.I_eq.trans (I49_eq L X).symm, I49]
      exact le_iSup (fun x : X => CFSG.conjugate L (x : G)) ⟨x ^ 2, hx2X⟩

private theorem modrest_commute_of_commutator_eq_bot {A B : Subgroup G}
    (h : ⁅A, B⁆ = ⊥) : ∀ a ∈ A, ∀ b ∈ B, Commute a b := fun a ha b hb =>
  commutatorElement_eq_one_iff_commute.mp
    (Subgroup.mem_bot.mp ((Subgroup.commutator_le.mp (le_of_eq h)) a ha b hb))

private theorem modrest_mem_centralizer_of_inf_eq_bot {N A : Subgroup G}
    (hN : N.Normal) (hA : A.Normal) (hNA : N ⊓ A = ⊥) {n : G} (hn : n ∈ N) :
    n ∈ Subgroup.centralizer (A : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have hmem : ⁅n, g⁆ ∈ N ⊓ A := by
    refine ⟨?_, ?_⟩
    · have h1 : g * n⁻¹ * g⁻¹ ∈ N := hN.conj_mem n⁻¹ (N.inv_mem hn) g
      rw [show ⁅n, g⁆ = n * (g * n⁻¹ * g⁻¹) by rw [commutatorElement_def]; group]
      exact N.mul_mem hn h1
    · have h1 : n * g * n⁻¹ ∈ A := hA.conj_mem g hg n
      rw [show ⁅n, g⁆ = (n * g * n⁻¹) * g⁻¹ by simp only [commutatorElement_def]]
      exact A.mul_mem h1 (A.inv_mem hg)
  exact (commutatorElement_eq_one_iff_commute.mp (Subgroup.mem_bot.mp (hNA ▸ hmem))).eq.symm

private theorem modrest_eq_one_of_forall_commutator_eq_one {A : Subgroup G}
    (hz : Subgroup.center ↥A = ⊥) {g : G} (hg : g ∈ A)
    (hcent : ∀ h ∈ A, ⁅g, h⁆ = 1) : g = 1 := by
  have hmem : (⟨g, hg⟩ : ↥A) ∈ Subgroup.center ↥A := by
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    exact (commutatorElement_eq_one_iff_commute.mp (hcent z.1 z.2)).eq.symm
  have hbot : (⟨g, hg⟩ : ↥A) ∈ (⊥ : Subgroup ↥A) := by rw [← hz]; exact hmem
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hbot)

private theorem modrest_left_eq_one_of_mul_eq {G₀ G₁ G₂ : Subgroup G} {n g0 g1 g2 : G}
    (h01 : ∀ a ∈ G₀, ∀ b ∈ G₁, Commute a b) (h02 : ∀ a ∈ G₀, ∀ b ∈ G₂, Commute a b)
    (hn : n = g0 * g1 * g2) (hg0 : g0 ∈ G₀) (hg1 : g1 ∈ G₁) (hg2 : g2 ∈ G₂)
    (hnc : ∀ h ∈ G₀, Commute n h) (hz : Subgroup.center ↥G₀ = ⊥) : g0 = 1 := by
  refine modrest_eq_one_of_forall_commutator_eq_one hz hg0 fun h hh => ?_
  have h1 : ⁅g1, h⁆ = 1 :=
    commutatorElement_eq_one_iff_commute.mpr (h01 h hh g1 hg1).symm
  have h2 : ⁅g2, h⁆ = 1 :=
    commutatorElement_eq_one_iff_commute.mpr (h02 h hh g2 hg2).symm
  have hn1 : ⁅n, h⁆ = 1 := commutatorElement_eq_one_iff_commute.mpr (hnc h hh)
  have key : ⁅n, h⁆ = ⁅g0, h⁆ := by
    rw [hn, commutatorElement_mul_left_eq_conj_mul,
      commutatorElement_mul_left_eq_conj_mul, h1, h2]
    group
  rwa [key] at hn1

private theorem modrest_mid_eq_one_of_mul_eq {G₀ G₁ G₂ : Subgroup G} {n g0 g1 g2 : G}
    (h01 : ∀ a ∈ G₀, ∀ b ∈ G₁, Commute a b) (h12 : ∀ a ∈ G₁, ∀ b ∈ G₂, Commute a b)
    (hn : n = g0 * g1 * g2) (hg0 : g0 ∈ G₀) (hg1 : g1 ∈ G₁) (hg2 : g2 ∈ G₂)
    (hnc : ∀ h ∈ G₁, Commute n h) (hz : Subgroup.center ↥G₁ = ⊥) : g1 = 1 := by
  refine modrest_eq_one_of_forall_commutator_eq_one hz hg1 fun h hh => ?_
  have h0 : ⁅g0, h⁆ = 1 :=
    commutatorElement_eq_one_iff_commute.mpr (h01 g0 hg0 h hh)
  have h2 : ⁅g2, h⁆ = 1 :=
    commutatorElement_eq_one_iff_commute.mpr (h12 h hh g2 hg2).symm
  have hn1 : ⁅n, h⁆ = 1 := commutatorElement_eq_one_iff_commute.mpr (hnc h hh)
  have key : ⁅n, h⁆ = g0 * ⁅g1, h⁆ * g0⁻¹ := by
    rw [hn, commutatorElement_mul_left_eq_conj_mul,
      commutatorElement_mul_left_eq_conj_mul, h0, h2]
    group
  have h1 : g0 * ⁅g1, h⁆ * g0⁻¹ = 1 := by rw [← key]; exact hn1
  have := congrArg (fun t => g0⁻¹ * t * g0) h1
  simpa [mul_assoc] using this

private theorem modrest_right_eq_one_of_mul_eq {G₀ G₁ G₂ : Subgroup G} {n g0 g1 g2 : G}
    (h02 : ∀ a ∈ G₀, ∀ b ∈ G₂, Commute a b) (h12 : ∀ a ∈ G₁, ∀ b ∈ G₂, Commute a b)
    (hn : n = g0 * g1 * g2) (hg0 : g0 ∈ G₀) (hg1 : g1 ∈ G₁) (hg2 : g2 ∈ G₂)
    (hnc : ∀ h ∈ G₂, Commute n h) (hz : Subgroup.center ↥G₂ = ⊥) : g2 = 1 := by
  refine modrest_eq_one_of_forall_commutator_eq_one hz hg2 fun h hh => ?_
  have h0 : ⁅g0, h⁆ = 1 :=
    commutatorElement_eq_one_iff_commute.mpr (h02 g0 hg0 h hh)
  have h1 : ⁅g1, h⁆ = 1 :=
    commutatorElement_eq_one_iff_commute.mpr (h12 g1 hg1 h hh)
  have hn1 : ⁅n, h⁆ = 1 := commutatorElement_eq_one_iff_commute.mpr (hnc h hh)
  have key : ⁅n, h⁆ = (g0 * g1) * ⁅g2, h⁆ * (g0 * g1)⁻¹ := by
    rw [hn, commutatorElement_mul_left_eq_conj_mul,
      commutatorElement_mul_left_eq_conj_mul, h0, h1]
    group
  have h2 : (g0 * g1) * ⁅g2, h⁆ * (g0 * g1)⁻¹ = 1 := by rw [← key]; exact hn1
  have := congrArg (fun t => (g0 * g1)⁻¹ * t * (g0 * g1)) h2
  simpa [mul_assoc] using this

theorem eq_bot_of_sup_commuting_center_eq_bot {G : Type} [Group G] [Finite G]
    {G₀ G₁ G₂ N : Subgroup G} (hsup : G₀ ⊔ G₁ ⊔ G₂ = ⊤)
    (h₀₁ : ⁅G₀, G₁⁆ = ⊥) (h₀₂ : ⁅G₀, G₂⁆ = ⊥) (h₁₂ : ⁅G₁, G₂⁆ = ⊥)
    (hn₀ : G₀.Normal) (hn₁ : G₁.Normal) (hn₂ : G₂.Normal)
    (hz₀ : Subgroup.center ↥G₀ = ⊥) (hz₁ : Subgroup.center ↥G₁ = ⊥)
    (hz₂ : Subgroup.center ↥G₂ = ⊥)
    (hN : N.Normal) (hN₀ : N ⊓ G₀ = ⊥) (hN₁ : N ⊓ G₁ = ⊥) (hN₂ : N ⊓ G₂ = ⊥) :
    N = ⊥ := by
  classical
  rw [eq_bot_iff]
  intro n hn
  have cm01 := modrest_commute_of_commutator_eq_bot h₀₁
  have cm02 := modrest_commute_of_commutator_eq_bot h₀₂
  have cm12 := modrest_commute_of_commutator_eq_bot h₁₂
  have cent0 : n ∈ Subgroup.centralizer (G₀ : Set G) :=
    modrest_mem_centralizer_of_inf_eq_bot hN hn₀ hN₀ hn
  have cent1 : n ∈ Subgroup.centralizer (G₁ : Set G) :=
    modrest_mem_centralizer_of_inf_eq_bot hN hn₁ hN₁ hn
  have cent2 : n ∈ Subgroup.centralizer (G₂ : Set G) :=
    modrest_mem_centralizer_of_inf_eq_bot hN hn₂ hN₂ hn
  have hN0N : G₀ ⊔ G₁ ≤ Subgroup.normalizer (G₂ : Set G) :=
    sup_le ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp h₀₂).trans
        (Subgroup.centralizer_le_normalizer _))
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp h₁₂).trans
        (Subgroup.centralizer_le_normalizer _))
  have hN01 : G₀ ≤ Subgroup.normalizer (G₁ : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h₀₁).trans
      (Subgroup.centralizer_le_normalizer _)
  have htop : n ∈ G₀ ⊔ G₁ ⊔ G₂ := hsup ▸ Subgroup.mem_top n
  obtain ⟨g01, hg01, g2, hg2, hg01_eq⟩ :=
    (mem_sup_of_le_normalizer (x := n) hN0N).mp htop
  obtain ⟨g0, hg0, g1, hg1, hg0_eq⟩ :=
    (mem_sup_of_le_normalizer (x := g01) hN01).mp hg01
  have hn_eq : n = (g0 * g1) * g2 := by rw [← hg01_eq, ← hg0_eq]
  have hg0one : g0 = 1 := modrest_left_eq_one_of_mul_eq cm01 cm02 hn_eq hg0 hg1 hg2
    (fun h hh => (Subgroup.mem_centralizer_iff.mp cent0 h hh).symm) hz₀
  have hg1one : g1 = 1 := modrest_mid_eq_one_of_mul_eq cm01 cm12 hn_eq hg0 hg1 hg2
    (fun h hh => (Subgroup.mem_centralizer_iff.mp cent1 h hh).symm) hz₁
  have hg2one : g2 = 1 := modrest_right_eq_one_of_mul_eq cm02 cm12 hn_eq hg0 hg1 hg2
    (fun h hh => (Subgroup.mem_centralizer_iff.mp cent2 h hh).symm) hz₂
  rw [hn_eq, hg0one, hg1one, hg2one]
  simp

private noncomputable def modrest_chiefFixedSubmodule {H X L Q I : Subgroup G}
    (h : Setup49 H X L Q I) {N M : Subgroup G} (hch : HChief H N M)
    [(M.subgroupOf N).Normal] [IsElementaryAbelian 2 (N ⧸ M.subgroupOf N)]
    [Fact (Nat.Prime 2)] :
    Submodule (ZMod 2) (Additive (N ⧸ M.subgroupOf N)) where
  carrier := {v | ∀ q : Q, (chiefRep (p := 2) hch.2.1 hch.2.2.1
      (Subgroup.inclusion (Q_le_H49 h) q)).val v = v}
  zero_mem' := fun q => map_zero _
  add_mem' := fun {v w} hv hw q => by rw [map_add, hv q, hw q]
  smul_mem' := fun c {v} hv q => by rw [map_smul, hv q]

private theorem modrest_chiefFixedSubmodule_invariant {H X L Q I : Subgroup G}
    (h : Setup49 H X L Q I) {N M : Subgroup G} (hch : HChief H N M)
    [(M.subgroupOf N).Normal] [IsElementaryAbelian 2 (N ⧸ M.subgroupOf N)]
    [Fact (Nat.Prime 2)] :
    ∀ n : H, ∀ v ∈ modrest_chiefFixedSubmodule h hch,
      (chiefRep (p := 2) hch.2.1 hch.2.2.1 n).val v ∈
        modrest_chiefFixedSubmodule h hch := by
  intro n v hv q
  let ρ : H →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive (N ⧸ M.subgroupOf N)) :=
    chiefRep (p := 2) hch.2.1 hch.2.2.1
  show (ρ (Subgroup.inclusion (Q_le_H49 h) q)).val ((ρ n).val v) = (ρ n).val v
  have hmem : (n : G)⁻¹ * (q : G) * n ∈ Q := by
    have hq' : (n : G)⁻¹ * (q : G) * ((n : G)⁻¹)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_Q h (H.inv_mem n.2)) (q : G)).mp q.2
    simpa using hq'
  let q' : Q := ⟨(n : G)⁻¹ * (q : G) * n, hmem⟩
  have hkey : Subgroup.inclusion (Q_le_H49 h) q * n =
      n * Subgroup.inclusion (Q_le_H49 h) q' := by
    apply Subtype.ext
    show (q : G) * n = n * ((n : G)⁻¹ * (q : G) * n)
    group
  have hkey' : ρ (Subgroup.inclusion (Q_le_H49 h) q) * ρ n =
      ρ n * ρ (Subgroup.inclusion (Q_le_H49 h) q') := by
    rw [← map_mul, ← map_mul, hkey]
  calc (ρ (Subgroup.inclusion (Q_le_H49 h) q)).val ((ρ n).val v)
      = ((ρ (Subgroup.inclusion (Q_le_H49 h) q) * ρ n).val) v := by
        rw [Units.val_mul, Module.End.mul_apply]
    _ = ((ρ n * ρ (Subgroup.inclusion (Q_le_H49 h) q')).val) v := by rw [hkey']
    _ = (ρ n).val ((ρ (Subgroup.inclusion (Q_le_H49 h) q')).val v) := by
        rw [Units.val_mul, Module.End.mul_apply]
    _ = (ρ n).val v := by
        rw [show (ρ (Subgroup.inclusion (Q_le_H49 h) q')).val v = v from hv q']

private theorem modrest_nontrivial_quotient_of_lt {N M : Subgroup G} [(M.subgroupOf N).Normal]
    (hMN : M < N) :
    Nontrivial (N ⧸ M.subgroupOf N) := by
  obtain ⟨w, hwN, hwM⟩ := SetLike.exists_of_lt hMN
  refine ⟨QuotientGroup.mk' (M.subgroupOf N) ⟨w, hwN⟩, 1, ?_⟩
  intro hcontra
  have : (⟨w, hwN⟩ : N) ∈ M.subgroupOf N := (QuotientGroup.eq_one_iff _).mp hcontra
  exact hwM (Subgroup.mem_subgroupOf.mp this)

private theorem modrest_two_dvd_card_of_nontrivial {V : Type*} [Group V] [Finite V]
    [IsElementaryAbelian 2 V] (hV : Nontrivial V) : 2 ∣ Nat.card V := by
  obtain ⟨k, hk, hcard⟩ := (IsElementaryAbelian.isPGroup 2 V).nontrivial_iff_card.mp hV
  rw [hcard]
  exact dvd_pow_self 2 hk.ne'

private theorem modrest_chiefFixedSubmodule_ne_bot {H X L Q I : Subgroup G}
    (h : Setup49 H X L Q I) {N M : Subgroup G} (hch : HChief H N M)
    [(M.subgroupOf N).Normal] [IsElementaryAbelian 2 (N ⧸ M.subgroupOf N)]
    [Fact (Nat.Prime 2)] :
    modrest_chiefFixedSubmodule h hch ≠ ⊥ := by
  let U : Submodule (ZMod 2) (Additive (N ⧸ M.subgroupOf N)) := modrest_chiefFixedSubmodule h hch
  let ρ : H →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive (N ⧸ M.subgroupOf N)) :=
    chiefRep (p := 2) hch.2.1 hch.2.2.1
  show U ≠ ⊥
  have hWnt : Nontrivial (N ⧸ M.subgroupOf N) := modrest_nontrivial_quotient_of_lt hch.1
  have hdvd : 2 ∣ Nat.card (N ⧸ M.subgroupOf N) :=
    modrest_two_dvd_card_of_nontrivial hWnt
  let act : Q →* MulAut (N ⧸ M.subgroupOf N) :=
    (chiefAction hch.2.1 hch.2.2.1).comp (Subgroup.inclusion (Q_le_H49 h))
  letI : MulAction Q (N ⧸ M.subgroupOf N) :=
    MulAction.compHom (N ⧸ M.subgroupOf N) act
  have hfix1 : (1 : N ⧸ M.subgroupOf N) ∈ MulAction.fixedPoints Q (N ⧸ M.subgroupOf N) := by
    rw [MulAction.mem_fixedPoints]
    intro q
    change act q 1 = 1
    exact map_one _
  obtain ⟨b, hb, hbne⟩ :=
    (isPGroup_Q h).exists_fixed_point_of_prime_dvd_card_of_fixed_point
      (N ⧸ M.subgroupOf N) hdvd hfix1
  have hb1 : b ≠ 1 := fun hcontra => hbne hcontra.symm
  obtain ⟨w, hw⟩ := QuotientGroup.mk'_surjective (M.subgroupOf N) b
  have hvU : (Additive.ofMul (w : N ⧸ M.subgroupOf N)) ∈ U := by
    intro q
    have hbq : act q (w : N ⧸ M.subgroupOf N) = (w : N ⧸ M.subgroupOf N) := by
      have hh := (MulAction.mem_fixedPoints.mp hb) q
      change act q b = b at hh
      rw [← hw] at hh
      exact hh
    rw [chiefRep_apply_mk (p := 2) hch.2.1 hch.2.2.1, ← chiefAction_mk hch.2.1 hch.2.2.1]
    change Additive.ofMul (act q (w : N ⧸ M.subgroupOf N)) =
      Additive.ofMul (w : N ⧸ M.subgroupOf N)
    rw [hbq]
  intro hbot
  have hmem : Additive.ofMul (w : N ⧸ M.subgroupOf N) ∈ (⊥ : Submodule (ZMod 2) _) := by
    rw [← hbot]; exact hvU
  rw [Submodule.mem_bot] at hmem
  have hw1 : (w : N ⧸ M.subgroupOf N) = 1 := by
    simpa using congrArg Additive.toMul hmem
  exact hb1 (hw ▸ hw1)

theorem chief_q_trivial49 {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {N M : Subgroup G} (hch : HChief H N M) (hNQ : N ≤ Q) : ⁅N, Q⁆ ≤ M := by
  classical
  haveI hNorm : (M.subgroupOf N).Normal := hch.normal
  haveI hElem : IsElementaryAbelian 2 (N ⧸ M.subgroupOf N) := hch.isElementaryAbelian
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQH : Q ≤ H := Q_le_H49 h
  have hU := modrest_chiefFixedSubmodule_invariant h hch
  have hUne : modrest_chiefFixedSubmodule h hch ≠ ⊥ :=
    modrest_chiefFixedSubmodule_ne_bot h hch
  have hUt : modrest_chiefFixedSubmodule h hch = ⊤ :=
    (chiefRep_irreducible hch _ hU).resolve_left hUne
  rw [Subgroup.commutator_le]
  intro n hnN q hqQ
  have hq1 : chiefRep (p := 2) hch.2.1 hch.2.2.1
      (Subgroup.inclusion hQH ⟨q, hqQ⟩) = 1 := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    have hv : v ∈ modrest_chiefFixedSubmodule h hch := by rw [hUt]; exact Submodule.mem_top
    exact hv ⟨q, hqQ⟩
  exact (chiefRep_eq_one_iff hch.2.1 hch.2.2.1 (Subgroup.inclusion hQH ⟨q, hqQ⟩)).mp hq1 n hnN

private theorem chief_faithful49_kernel_map_sup_eq_top
    {I Ī : Type*} [Group I] [Group Ī] (π : I →* Ī) (hπ : Function.Surjective π)
    {L0 L1 L2 : Subgroup I} (hsup : L0 ⊔ L1 ⊔ L2 = ⊤) :
    L0.map π ⊔ L1.map π ⊔ L2.map π = ⊤ := by
  rw [← Subgroup.map_sup, ← Subgroup.map_sup, hsup, Subgroup.map_top_of_surjective π hπ]

private theorem chief_faithful49_kernel_subgroupOf_sup_eq_top
    {I L0 L1 L2 : Subgroup G} (h0 : L0 ≤ I) (h1 : L1 ≤ I) (h2 : L2 ≤ I)
    (h : L0 ⊔ L1 ⊔ L2 = I) :
    L0.subgroupOf I ⊔ L1.subgroupOf I ⊔ L2.subgroupOf I = ⊤ := by
  rw [← Subgroup.subgroupOf_sup h0 h1, ← Subgroup.subgroupOf_sup (sup_le h0 h1) h2,
    h, Subgroup.subgroupOf_self]

private theorem chief_faithful49_kernel_map_commutator_eq_bot
    {I Q : Subgroup G} {Ī : Type*} [Group Ī] (π : I →* Ī)
    (hker : ∀ g : I, π g = 1 ↔ (g : G) ∈ Q)
    {A B : Subgroup G} (hAI : A ≤ I) (hBI : B ≤ I) (hAB : ⁅A, B⁆ ≤ Q) :
    ⁅(A.subgroupOf I).map π, (B.subgroupOf I).map π⁆ = ⊥ := by
  rw [eq_bot_iff]
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  rw [Subgroup.mem_bot]
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
  rw [← map_commutatorElement]
  exact (hker ⁅a', b'⁆).mpr
    ((Subgroup.commutator_le.mp hAB) (a' : G) (Subgroup.mem_subgroupOf.mp ha')
      (b' : G) (Subgroup.mem_subgroupOf.mp hb'))

private theorem chief_faithful49_kernel_map_center_eq_bot
    {I Q : Subgroup G} {Ī : Type*} [Group Ī] (π : I →* Ī)
    (hker : ∀ g : I, π g = 1 ↔ (g : G) ∈ Q)
    {K H : Subgroup G} (hKI : K ≤ I) (hKH : K ≤ H) (hKalt : IsAlt (Bar2 K) 5)
    (hKQ : K ⊓ Q = CFSG.Open.pCoreOf 2 K) :
    Subgroup.center ↥((K.subgroupOf I).map π) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  obtain ⟨l, hl, hl_eq⟩ := Subgroup.mem_map.mp z.2
  have hlK : (l : G) ∈ K := Subgroup.mem_subgroupOf.mp hl
  have hcent : ∀ m ∈ K, ⁅(l : G), m⁆ ∈ Q := by
    intro m hm
    have hmI : m ∈ I := hKI hm
    have hmK : (⟨m, hmI⟩ : I) ∈ K.subgroupOf I := Subgroup.mem_subgroupOf.mpr hm
    let w : ↥((K.subgroupOf I).map π) := ⟨π ⟨m, hmI⟩, Subgroup.mem_map_of_mem π hmK⟩
    have hwz : w * z = z * w := (Subgroup.mem_center_iff.mp hz) w
    have hmul : π ((⟨m, hmI⟩ : I) * l) = π (l * ⟨m, hmI⟩) := by
      have h := congrArg Subtype.val hwz
      simpa [w, hl_eq.symm] using h
    have hmlQ : ⁅(m : G), (l : G)⁆ ∈ Q := by
      have h1 : π ((⟨m, hmI⟩ : I) * l * (l * ⟨m, hmI⟩)⁻¹) = 1 := by
        rw [map_mul, map_inv, hmul, mul_inv_cancel]
      simpa [commutatorElement_def, mul_assoc] using (hker _).mp h1
    simpa only [commutatorElement_inv] using Q.inv_mem hmlQ
  have hlQ : (l : G) ∈ Q := mem_pCoreOf_of_centralizer_mod hKalt hKQ hKH hlK hcent
  exact Subtype.ext (by rw [← hl_eq]; exact (hker l).mpr hlQ)

private theorem chief_faithful49_kernel_T_map_inf_map_eq_bot
    {I Ī : Type*} [Group I] [Group Ī] (π : I →* Ī)
    {P T A : Subgroup I} (hker : π.ker = P) (hPT : P ≤ T) (hTA : T ⊓ A ≤ P) :
    T.map π ⊓ A.map π = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  obtain ⟨hzN, hzG⟩ := Subgroup.mem_inf.mp hz
  obtain ⟨t, ht, ht_eq⟩ := Subgroup.mem_map.mp hzN
  obtain ⟨l, hl, hl_eq⟩ := Subgroup.mem_map.mp hzG
  have ht1l : t⁻¹ * l ∈ P := by
    rw [← hker, MonoidHom.mem_ker]
    show π (t⁻¹ * l) = 1
    rw [map_mul, map_inv, ht_eq, hl_eq, inv_mul_cancel]
  have hlT : l ∈ T := by
    have h1 : t * (t⁻¹ * l) ∈ T := T.mul_mem ht (hPT ht1l)
    simpa [mul_assoc] using h1
  have hlP : l ∈ P := hTA ⟨hlT, hl⟩
  rw [← hl_eq, ← MonoidHom.mem_ker, hker]
  exact hlP

private theorem chief_faithful49_kernel_normalizer_map_ker
    {H : Subgroup G} {M : Type*} [Group M] (ρ : H →* M) :
    H ≤ Subgroup.normalizer (((MonoidHom.ker ρ).map H.subtype : Subgroup G) : Set G) := by
  have h_eq : ((MonoidHom.ker ρ).map H.subtype).subgroupOf H = MonoidHom.ker ρ := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨k, hk, hk_eq⟩
      have hk' : k = x := Subtype.ext hk_eq
      rwa [hk'] at hk
    · intro hx
      exact ⟨x, hx, rfl⟩
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp (by
    rw [h_eq]
    exact MonoidHom.normal_ker ρ)

private theorem chief_faithful49_kernel_le_Krho_of_conj
    {H X L Q I K : Subgroup G} (h : Setup49 H X L Q I)
    (hK_norm : H ≤ Subgroup.normalizer (K : Set G))
    {y : G} (hy : y ∈ X) (hyK : CFSG.conjugate L y ≤ K) : L ≤ K := by
  have hyK' : L.map (MulAut.conj y⁻¹).toMonoidHom ≤ K := hyK
  have h2 := Subgroup.map_mono (f := (MulAut.conj y).toMonoidHom) hyK'
  have hcomp : (MulAut.conj y).toMonoidHom.comp (MulAut.conj y⁻¹).toMonoidHom =
      MonoidHom.id G := by
    ext g
    change (MulAut.conj y) ((MulAut.conj y⁻¹) g) = g
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group
  have hmap1 : Subgroup.map (MulAut.conj y).toMonoidHom
      (Subgroup.map (MulAut.conj y⁻¹).toMonoidHom L) = L := by
    rw [Subgroup.map_map, hcomp, Subgroup.map_id]
  have hmap2 : Subgroup.map (MulAut.conj y).toMonoidHom K = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hK_norm (h.X_le hy))
  rwa [hmap1, hmap2] at h2

private theorem chief_faithful49_kernel_I_le_Krho_of_conj
    {H X L Q I K : Subgroup G} (h : Setup49 H X L Q I) {x : G} (hxX : x ∈ X)
    (hxgen : X = Subgroup.zpowers x) (hK_norm : H ≤ Subgroup.normalizer (K : Set G))
    (hL_of_conj : ∀ w ∈ X, CFSG.conjugate L w ≤ K → L ≤ K)
    {y : G} (hy : y ∈ X) (hyK : CFSG.conjugate L y ≤ K) : I ≤ K := by
  have hL : L ≤ K := hL_of_conj y hy hyK
  have hc : ∀ w ∈ X, CFSG.conjugate L w ≤ K := by
    intro w hw
    rw [CFSG.conjugate]
    exact (Subgroup.map_mono hL).trans
      (le_of_eq (Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (hK_norm (H.inv_mem (h.X_le hw)))))
  rw [I_eq_sup_conjugates49 h hxX hxgen]
  exact sup_le (sup_le hL (hc x hxX)) (hc (x ^ 2) (X.pow_mem hxX 2))

private abbrev chief_faithful49_kernel_coreK {I : Subgroup G} (T : Subgroup I)
    (K' : Subgroup G) : Subgroup (Bar2 K') :=
  (((T ⊓ K'.subgroupOf I).map I.subtype).subgroupOf K').map
    (QuotientGroup.mk' (CFSG.pCore 2 K'))

private theorem chief_faithful49_kernel_coreK_normal
    {I : Subgroup G} {T : Subgroup I} (hT : T.Normal)
    {K' : Subgroup G} (hK'I : K' ≤ I) (hK' : (K'.subgroupOf I).Normal) :
    (chief_faithful49_kernel_coreK T K').Normal := by
  have hKyle : (T ⊓ K'.subgroupOf I).map I.subtype ≤ K' := by
    rintro _ ⟨k, hk, rfl⟩
    exact Subgroup.mem_subgroupOf.mp hk.2
  have hcy : ∀ g : G, g ∈ K' → ∀ x ∈ (T ⊓ K'.subgroupOf I).map I.subtype,
      g * x * g⁻¹ ∈ (T ⊓ K'.subgroupOf I).map I.subtype := by
    intro g hg x hx
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx
    have hgI : g ∈ I := hK'I hg
    have hconj : (⟨g, hgI⟩ : I) * t * (⟨g, hgI⟩ : I)⁻¹ ∈ T ⊓ K'.subgroupOf I :=
      ⟨hT.conj_mem t ht.1 ⟨g, hgI⟩, hK'.conj_mem t ht.2 ⟨g, hgI⟩⟩
    exact ⟨_, hconj, by simp [mul_assoc]⟩
  have hnorm : K' ≤ Subgroup.normalizer ((T ⊓ K'.subgroupOf I).map I.subtype : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨hcy g hg x, fun hx => by
      have h2 := hcy g⁻¹ (K'.inv_mem hg) (g * x * g⁻¹) hx
      simpa [mul_assoc] using h2⟩
  exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hKyle).mpr hnorm).map _
    (QuotientGroup.mk'_surjective _)

private theorem chief_faithful49_kernel_coreK_bot
    {I Q : Subgroup G} {T : Subgroup I} {K' : Subgroup G}
    (hK'Q : K' ⊓ Q = CFSG.Open.pCoreOf 2 K')
    (hKbot : chief_faithful49_kernel_coreK T K' = ⊥) {l : I}
    (hl : l ∈ T ⊓ K'.subgroupOf I) : (l : G) ∈ Q := by
  have hlL : (l : G) ∈ K' := Subgroup.mem_subgroupOf.mp hl.2
  have hle : ((T ⊓ K'.subgroupOf I).map I.subtype).subgroupOf K' ≤ CFSG.pCore 2 K' := by
    have h := (Subgroup.map_eq_bot_iff
      (((T ⊓ K'.subgroupOf I).map I.subtype).subgroupOf K')
      (f := QuotientGroup.mk' (CFSG.pCore 2 K'))).mp hKbot
    rwa [QuotientGroup.ker_mk'] at h
  have hlK : (⟨(l : G), hlL⟩ : K') ∈ ((T ⊓ K'.subgroupOf I).map I.subtype).subgroupOf K' := by
    rw [Subgroup.mem_subgroupOf]
    exact ⟨l, hl, rfl⟩
  have hlcore : (l : G) ∈ CFSG.Open.pCoreOf 2 K' :=
    (mem_pCoreOf_iff hlL).mpr (hle hlK)
  exact (hK'Q.symm ▸ hlcore).2

private theorem chief_faithful49_kernel_coreK_top
    {I Q : Subgroup G} {T : Subgroup I} {K' : Subgroup G}
    (hK'Q : K' ⊓ Q = CFSG.Open.pCoreOf 2 K')
    (hKtop : chief_faithful49_kernel_coreK T K' = ⊤) :
    K' ≤ (T ⊓ K'.subgroupOf I).map I.subtype ⊔ Q := by
  intro m hm
  have hmK : (QuotientGroup.mk' (CFSG.pCore 2 K')) (⟨m, hm⟩ : K') ∈
      chief_faithful49_kernel_coreK T K' := by
    rw [hKtop]; exact Subgroup.mem_top _
  obtain ⟨k, hk, hk_eq⟩ := Subgroup.mem_map.mp hmK
  have hkmap : ((k : K') : G) ∈ (T ⊓ K'.subgroupOf I).map I.subtype :=
    Subgroup.mem_subgroupOf.mp hk
  have hmk : (⟨m, hm⟩ : K') * k⁻¹ ∈ CFSG.pCore 2 K' := by
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 K') ((⟨m, hm⟩ : K') * k⁻¹) = 1 := by
      rw [map_mul, map_inv, hk_eq, mul_inv_cancel]
    rw [QuotientGroup.mk'_apply] at h1
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hmkG : (m * ((k : K') : G)⁻¹ : G) ∈ CFSG.Open.pCoreOf 2 K' :=
    (mem_pCoreOf_iff (K'.mul_mem hm (K'.inv_mem k.2))).mpr hmk
  have hkQ : (m * ((k : K') : G)⁻¹ : G) ∈ Q := by
    have hmem : (m * ((k : K') : G)⁻¹ : G) ∈ K' ⊓ Q := by
      rw [hK'Q]; exact hmkG
    exact hmem.2
  have hthis : m = (m * ((k : K') : G)⁻¹) * ((k : K') : G) := by group
  rw [hthis]
  exact (sup_comm Q ((T ⊓ K'.subgroupOf I).map I.subtype)).le
    (Subgroup.mul_mem_sup hkQ hkmap)

private structure chief_faithful49_kernel_ActData (H I Q N M : Subgroup G) where
  T : Subgroup I
  T_normal : T.Normal
  T_iff : ∀ g : I, g ∈ T ↔ ∀ n ∈ N, ⁅n, (g : G)⁆ ∈ M
  hPT : (I ⊓ Q).subgroupOf I ≤ T
  Krho : Subgroup G
  TK : T.map I.subtype ≤ Krho
  QK : Q ≤ Krho
  Krho_norm : H ≤ Subgroup.normalizer (Krho : Set G)
  Krho_act : ∀ k ∈ Krho, ∀ n ∈ N, ⁅n, k⁆ ∈ M

private noncomputable def chief_faithful49_kernel_ActData.ofSetup
    {H I Q N M : Subgroup G} (hch : HChief H N M) (hIH : I ≤ H) (hQH : Q ≤ H)
    (hQtriv : ⁅N, Q⁆ ≤ M) : chief_faithful49_kernel_ActData H I Q N M := by
  classical
  haveI hNorm : (M.subgroupOf N).Normal := hch.normal
  haveI hElem : IsElementaryAbelian 2 (N ⧸ M.subgroupOf N) := hch.isElementaryAbelian
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ρ : H →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive (N ⧸ M.subgroupOf N)) :=
    chiefRep (p := 2) hch.2.1 hch.2.2.1
  let ρI : I →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive (N ⧸ M.subgroupOf N)) :=
    ρ.comp (Subgroup.inclusion hIH)
  have hT_iff : ∀ g : I, g ∈ MonoidHom.ker ρI ↔ ∀ n ∈ N, ⁅n, (g : G)⁆ ∈ M := by
    intro g
    rw [MonoidHom.mem_ker]
    exact chiefRep_eq_one_iff (p := 2) hch.2.1 hch.2.2.1 (Subgroup.inclusion hIH g)
  have hPT : (I ⊓ Q).subgroupOf I ≤ MonoidHom.ker ρI := fun p hp =>
    (hT_iff p).mpr fun n hn =>
      (Subgroup.commutator_le.mp hQtriv) n hn (p.1 : G) (Subgroup.mem_subgroupOf.mp hp).2
  let Krho : Subgroup G := (MonoidHom.ker ρ).map H.subtype
  have hTK : (MonoidHom.ker ρI).map I.subtype ≤ Krho := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨Subgroup.inclusion hIH t, ht, rfl⟩
  have hQK : Q ≤ Krho := fun q hq =>
    ⟨⟨q, hQH hq⟩, (chiefRep_eq_one_iff (p := 2) hch.2.1 hch.2.2.1
      (⟨q, hQH hq⟩ : H)).mpr (fun n hn => (Subgroup.commutator_le.mp hQtriv) n hn q hq), rfl⟩
  refine ⟨MonoidHom.ker ρI, MonoidHom.normal_ker ρI, hT_iff, hPT, Krho, hTK, hQK,
    chief_faithful49_kernel_normalizer_map_ker ρ, ?_⟩
  rintro k ⟨κ, hκ, rfl⟩ n hn
  exact (chiefRep_eq_one_iff (p := 2) hch.2.1 hch.2.2.1 κ).mp hκ n hn

private structure chief_faithful49_kernel_Ctx (H X L Q I N M : Subgroup G) where
  setup : Setup49 H X L Q I
  chief : HChief H N M
  NQ : N ≤ Q
  Ntriv : ¬ ⁅N, I⁆ ≤ M
  x : G
  hxX : x ∈ X
  hxgen : X = Subgroup.zpowers x
  hneL : CFSG.conjugate L x ≠ L
  hneL2 : CFSG.conjugate L (x ^ 2) ≠ L
  hne2 : CFSG.conjugate L (x ^ 2) ≠ CFSG.conjugate L x
  Ieq : I = L ⊔ CFSG.conjugate L x ⊔ CFSG.conjugate L (x ^ 2)
  Ī : Type
  [grp : Group Ī]
  [fin : Finite Ī]
  π : I →* Ī
  π_surj : Function.Surjective π
  ker_eq : π.ker = (I ⊓ Q).subgroupOf I
  T : Subgroup I
  T_normal : T.Normal
  T_iff : ∀ g : I, g ∈ T ↔ ∀ n ∈ N, ⁅n, (g : G)⁆ ∈ M
  hPT : (I ⊓ Q).subgroupOf I ≤ T
  Krho : Subgroup G
  TK : T.map I.subtype ≤ Krho
  QK : Q ≤ Krho
  Krho_norm : H ≤ Subgroup.normalizer (Krho : Set G)
  Krho_act : ∀ k ∈ Krho, ∀ n ∈ N, ⁅n, k⁆ ∈ M

attribute [instance] chief_faithful49_kernel_Ctx.grp chief_faithful49_kernel_Ctx.fin

private noncomputable def chief_faithful49_kernel_Ctx.ofSetup
    {H X L Q I N M : Subgroup G} (h : Setup49 H X L Q I) (hch : HChief H N M)
    (hNQ : N ≤ Q) (hI : ¬ ⁅N, I⁆ ≤ M) {x : G} (hxX : x ∈ X)
    (hxgen : X = Subgroup.zpowers x) (hneL : CFSG.conjugate L x ≠ L)
    (hneL2 : CFSG.conjugate L (x ^ 2) ≠ L)
    (hne2 : CFSG.conjugate L (x ^ 2) ≠ CFSG.conjugate L x) :
    chief_faithful49_kernel_Ctx H X L Q I N M := by
  have hIH : I ≤ H := I_le_H h
  let P : Subgroup G := I ⊓ Q
  have hPnorm : (P.subgroupOf I).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr (I_le_normalizer_inf_I_Q h)
  let Ī := I ⧸ P.subgroupOf I
  let π : I →* Ī := QuotientGroup.mk' (P.subgroupOf I)
  have hπker : π.ker = P.subgroupOf I := QuotientGroup.ker_mk' _
  let A := chief_faithful49_kernel_ActData.ofSetup hch hIH (Q_le_H49 h)
    (chief_q_trivial49 h hch hNQ)
  exact
    { setup := h, chief := hch, NQ := hNQ, Ntriv := hI, x := x, hxX := hxX, hxgen := hxgen,
      hneL := hneL, hneL2 := hneL2, hne2 := hne2,
      Ieq := I_eq_sup_conjugates49 h hxX hxgen,
      Ī := Ī, π := π, π_surj := QuotientGroup.mk'_surjective _, ker_eq := hπker,
      T := A.T, T_normal := A.T_normal, T_iff := A.T_iff, hPT := A.hPT,
      Krho := A.Krho, TK := A.TK, QK := A.QK, Krho_norm := A.Krho_norm, Krho_act := A.Krho_act }

variable {H X L Q I N M : Subgroup G}

private theorem chief_faithful49_kernel_Ctx.ker_iff
    (c : chief_faithful49_kernel_Ctx H X L Q I N M) (g : I) :
    c.π g = 1 ↔ (g : G) ∈ Q := by
  rw [← MonoidHom.mem_ker, c.ker_eq, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩

private theorem chief_faithful49_kernel_Ctx.I_le_Krho_of_conj
    (c : chief_faithful49_kernel_Ctx H X L Q I N M) {y : G} (hy : y ∈ X)
    (hyK : CFSG.conjugate L y ≤ c.Krho) : I ≤ c.Krho :=
  chief_faithful49_kernel_I_le_Krho_of_conj c.setup c.hxX c.hxgen c.Krho_norm
    (fun w hw hwK => chief_faithful49_kernel_le_Krho_of_conj c.setup c.Krho_norm hw hwK)
    hy hyK

private theorem chief_faithful49_kernel_Ctx.comm01
    (c : chief_faithful49_kernel_Ctx H X L Q I N M) :
    ⁅(L.subgroupOf I).map c.π, ((CFSG.conjugate L c.x).subgroupOf I).map c.π⁆ = ⊥ := by
  refine chief_faithful49_kernel_map_commutator_eq_bot c.π c.ker_iff
    (le_I c.setup) (conjugate_le_I c.setup c.hxX) ?_
  simpa only [conjugate_one] using commutator_conjugate_le c.setup X.one_mem c.hxX
    (by rw [conjugate_one]; exact Ne.symm c.hneL)

private theorem chief_faithful49_kernel_Ctx.comm02
    (c : chief_faithful49_kernel_Ctx H X L Q I N M) :
    ⁅(L.subgroupOf I).map c.π,
      ((CFSG.conjugate L (c.x ^ 2)).subgroupOf I).map c.π⁆ = ⊥ := by
  refine chief_faithful49_kernel_map_commutator_eq_bot c.π c.ker_iff
    (le_I c.setup) (conjugate_le_I c.setup (X.pow_mem c.hxX 2)) ?_
  simpa only [conjugate_one] using commutator_conjugate_le c.setup X.one_mem
    (X.pow_mem c.hxX 2) (by rw [conjugate_one]; exact Ne.symm c.hneL2)

private theorem chief_faithful49_kernel_Ctx.comm12
    (c : chief_faithful49_kernel_Ctx H X L Q I N M) :
    ⁅((CFSG.conjugate L c.x).subgroupOf I).map c.π,
      ((CFSG.conjugate L (c.x ^ 2)).subgroupOf I).map c.π⁆ = ⊥ := by
  refine chief_faithful49_kernel_map_commutator_eq_bot c.π c.ker_iff
    (conjugate_le_I c.setup c.hxX) (conjugate_le_I c.setup (X.pow_mem c.hxX 2)) ?_
  exact commutator_conjugate_le c.setup c.hxX (X.pow_mem c.hxX 2) (Ne.symm c.hne2)

private theorem chief_faithful49_kernel_Ctx.subgroupOf_normal0
    (c : chief_faithful49_kernel_Ctx H X L Q I N M) :
    (L.subgroupOf I).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (le_I c.setup)).mpr
    (I_le_normalizer_L c.setup)

private theorem chief_faithful49_kernel_Ctx.subgroupOf_normal1
    (c : chief_faithful49_kernel_Ctx H X L Q I N M) :
    ((CFSG.conjugate L c.x).subgroupOf I).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (conjugate_le_I c.setup c.hxX)).mpr
    (c.Ieq.le.trans ?_)
  refine sup_le (sup_le ?_ Subgroup.le_normalizer) ?_
  · exact (le_of_eq (conjugate_one L).symm).trans
      (conjugate_normalize_of_ne c.setup X.one_mem c.hxX
        (by rw [conjugate_one]; exact Ne.symm c.hneL))
  · exact conjugate_normalize_of_ne c.setup (X.pow_mem c.hxX 2) c.hxX c.hne2

private theorem chief_faithful49_kernel_Ctx.subgroupOf_normal2
    (c : chief_faithful49_kernel_Ctx H X L Q I N M) :
    ((CFSG.conjugate L (c.x ^ 2)).subgroupOf I).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer
    (conjugate_le_I c.setup (X.pow_mem c.hxX 2))).mpr (c.Ieq.le.trans ?_)
  refine sup_le (sup_le ?_ ?_) Subgroup.le_normalizer
  · exact (le_of_eq (conjugate_one L).symm).trans
      (conjugate_normalize_of_ne c.setup X.one_mem (X.pow_mem c.hxX 2)
        (by rw [conjugate_one]; exact Ne.symm c.hneL2))
  · exact conjugate_normalize_of_ne c.setup c.hxX (X.pow_mem c.hxX 2) (Ne.symm c.hne2)

private theorem chief_faithful49_kernel_Ctx.norm0
    (c : chief_faithful49_kernel_Ctx H X L Q I N M) :
    ((L.subgroupOf I).map c.π).Normal :=
  c.subgroupOf_normal0.map c.π c.π_surj

private theorem chief_faithful49_kernel_Ctx.norm1
    (c : chief_faithful49_kernel_Ctx H X L Q I N M) :
    (((CFSG.conjugate L c.x).subgroupOf I).map c.π).Normal :=
  c.subgroupOf_normal1.map c.π c.π_surj

private theorem chief_faithful49_kernel_Ctx.norm2
    (c : chief_faithful49_kernel_Ctx H X L Q I N M) :
    (((CFSG.conjugate L (c.x ^ 2)).subgroupOf I).map c.π).Normal :=
  c.subgroupOf_normal2.map c.π c.π_surj

private theorem chief_faithful49_kernel_Ctx.center0
    (c : chief_faithful49_kernel_Ctx H X L Q I N M) :
    Subgroup.center ↥((L.subgroupOf I).map c.π) = ⊥ :=
  chief_faithful49_kernel_map_center_eq_bot c.π c.ker_iff (le_I c.setup)
    (CFSG.RankThree.PartTwo.le_of_mem_oTwoComponentsIn c.setup.L_mem) c.setup.L_alt
    (by simpa only [conjugate_one] using conjugate_inf_pCoreOf_eq c.setup X.one_mem)

private theorem chief_faithful49_kernel_Ctx.center1
    (c : chief_faithful49_kernel_Ctx H X L Q I N M) :
    Subgroup.center ↥(((CFSG.conjugate L c.x).subgroupOf I).map c.π) = ⊥ :=
  chief_faithful49_kernel_map_center_eq_bot c.π c.ker_iff (conjugate_le_I c.setup c.hxX)
    (conjugate_le_of_mem_normalizer
      (CFSG.RankThree.PartTwo.le_of_mem_oTwoComponentsIn c.setup.L_mem)
      (Subgroup.le_normalizer (c.setup.X_le c.hxX)))
    (isAlt_bar2_conjugate c.setup.L_alt c.x) (conjugate_inf_pCoreOf_eq c.setup c.hxX)

private theorem chief_faithful49_kernel_Ctx.center2
    (c : chief_faithful49_kernel_Ctx H X L Q I N M) :
    Subgroup.center ↥(((CFSG.conjugate L (c.x ^ 2)).subgroupOf I).map c.π) = ⊥ :=
  chief_faithful49_kernel_map_center_eq_bot c.π c.ker_iff
    (conjugate_le_I c.setup (X.pow_mem c.hxX 2))
    (conjugate_le_of_mem_normalizer
      (CFSG.RankThree.PartTwo.le_of_mem_oTwoComponentsIn c.setup.L_mem)
      (Subgroup.le_normalizer (c.setup.X_le (X.pow_mem c.hxX 2))))
    (isAlt_bar2_conjugate c.setup.L_alt (c.x ^ 2))
    (conjugate_inf_pCoreOf_eq c.setup (X.pow_mem c.hxX 2))

private theorem chief_faithful49_kernel_Ctx.core_le
    (c : chief_faithful49_kernel_Ctx H X L Q I N M) {K' : Subgroup G}
    (hK'norm : (K'.subgroupOf I).Normal) (hK'alt : IsAlt (Bar2 K') 5)
    (hK'I : K' ≤ I) (hK'H : K' ≤ H) (hK'Q : K' ⊓ Q = CFSG.Open.pCoreOf 2 K')
    (hI_of : K' ≤ c.Krho → I ≤ c.Krho) :
    c.T ⊓ K'.subgroupOf I ≤ (I ⊓ Q).subgroupOf I := by
  intro l hl
  by_contra hnot
  have hlL : (l : G) ∈ K' := Subgroup.mem_subgroupOf.mp hl.2
  obtain ⟨e⟩ := hK'alt
  haveI : IsSimpleGroup (Bar2 K') := e.isSimpleGroup
  have hKnormal : (chief_faithful49_kernel_coreK c.T K').Normal :=
    chief_faithful49_kernel_coreK_normal c.T_normal hK'I hK'norm
  rcases eq_bot_or_eq_top_of_normal (chief_faithful49_kernel_coreK c.T K') hKnormal with
    hKbot | hKtop
  · exact hnot (by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨hK'I hlL, chief_faithful49_kernel_coreK_bot hK'Q hKbot hl⟩)
  · have hle : K' ≤ (c.T ⊓ K'.subgroupOf I).map I.subtype ⊔ Q :=
      chief_faithful49_kernel_coreK_top hK'Q hKtop
    have hK'Krho : K' ≤ c.Krho :=
      hle.trans (sup_le ((Subgroup.map_mono inf_le_left).trans c.TK) c.QK)
    have hNI : ⁅N, I⁆ ≤ M := by
      rw [Subgroup.commutator_le]
      intro n hn i hi
      exact c.Krho_act i (hI_of hK'Krho hi) n hn
    exact c.Ntriv hNI

private theorem chief_faithful49_kernel_Ctx.T_inf0
    (c : chief_faithful49_kernel_Ctx H X L Q I N M) :
    c.T.map c.π ⊓ (L.subgroupOf I).map c.π = ⊥ := by
  refine chief_faithful49_kernel_T_map_inf_map_eq_bot c.π c.ker_eq c.hPT ?_
  exact c.core_le c.subgroupOf_normal0 c.setup.L_alt (le_I c.setup)
    (CFSG.RankThree.PartTwo.le_of_mem_oTwoComponentsIn c.setup.L_mem)
    (by simpa only [conjugate_one] using conjugate_inf_pCoreOf_eq c.setup X.one_mem)
    (fun hL => c.I_le_Krho_of_conj X.one_mem (by simpa [conjugate_one] using hL))

private theorem chief_faithful49_kernel_Ctx.T_inf1
    (c : chief_faithful49_kernel_Ctx H X L Q I N M) :
    c.T.map c.π ⊓ ((CFSG.conjugate L c.x).subgroupOf I).map c.π = ⊥ := by
  refine chief_faithful49_kernel_T_map_inf_map_eq_bot c.π c.ker_eq c.hPT ?_
  exact c.core_le c.subgroupOf_normal1 (isAlt_bar2_conjugate c.setup.L_alt c.x)
    (conjugate_le_I c.setup c.hxX)
    (conjugate_le_of_mem_normalizer
      (CFSG.RankThree.PartTwo.le_of_mem_oTwoComponentsIn c.setup.L_mem)
      (Subgroup.le_normalizer (c.setup.X_le c.hxX)))
    (conjugate_inf_pCoreOf_eq c.setup c.hxX)
    (fun hK => c.I_le_Krho_of_conj c.hxX hK)

private theorem chief_faithful49_kernel_Ctx.T_inf2
    (c : chief_faithful49_kernel_Ctx H X L Q I N M) :
    c.T.map c.π ⊓ ((CFSG.conjugate L (c.x ^ 2)).subgroupOf I).map c.π = ⊥ := by
  refine chief_faithful49_kernel_T_map_inf_map_eq_bot c.π c.ker_eq c.hPT ?_
  exact c.core_le c.subgroupOf_normal2 (isAlt_bar2_conjugate c.setup.L_alt (c.x ^ 2))
    (conjugate_le_I c.setup (X.pow_mem c.hxX 2))
    (conjugate_le_of_mem_normalizer
      (CFSG.RankThree.PartTwo.le_of_mem_oTwoComponentsIn c.setup.L_mem)
      (Subgroup.le_normalizer (c.setup.X_le (X.pow_mem c.hxX 2))))
    (conjugate_inf_pCoreOf_eq c.setup (X.pow_mem c.hxX 2))
    (fun hK => c.I_le_Krho_of_conj (X.pow_mem c.hxX 2) hK)

private theorem chief_faithful49_kernel_Ctx.sup_eq_top
    (c : chief_faithful49_kernel_Ctx H X L Q I N M) :
    (L.subgroupOf I).map c.π ⊔ ((CFSG.conjugate L c.x).subgroupOf I).map c.π ⊔
      ((CFSG.conjugate L (c.x ^ 2)).subgroupOf I).map c.π = ⊤ := by
  refine chief_faithful49_kernel_map_sup_eq_top c.π c.π_surj ?_
  exact chief_faithful49_kernel_subgroupOf_sup_eq_top (le_I c.setup)
    (conjugate_le_I c.setup c.hxX) (conjugate_le_I c.setup (X.pow_mem c.hxX 2)) c.Ieq.symm

private theorem chief_faithful49_kernel_Ctx.Nbar_eq_bot
    (c : chief_faithful49_kernel_Ctx H X L Q I N M) : c.T.map c.π = ⊥ := by
  let G0 : Subgroup c.Ī := (L.subgroupOf I).map c.π
  let G1 : Subgroup c.Ī := ((CFSG.conjugate L c.x).subgroupOf I).map c.π
  let G2 : Subgroup c.Ī := ((CFSG.conjugate L (c.x ^ 2)).subgroupOf I).map c.π
  have hsup : G0 ⊔ G1 ⊔ G2 = ⊤ := by dsimp only [G0, G1, G2]; exact c.sup_eq_top
  have hcomm01 : ⁅G0, G1⁆ = ⊥ := by dsimp only [G0, G1]; exact c.comm01
  have hcomm02 : ⁅G0, G2⁆ = ⊥ := by dsimp only [G0, G2]; exact c.comm02
  have hcomm12 : ⁅G1, G2⁆ = ⊥ := by dsimp only [G1, G2]; exact c.comm12
  have hG0norm : G0.Normal := by dsimp only [G0]; exact c.norm0
  have hG1norm : G1.Normal := by dsimp only [G1]; exact c.norm1
  have hG2norm : G2.Normal := by dsimp only [G2]; exact c.norm2
  have hz0 : Subgroup.center ↥G0 = ⊥ := by dsimp only [G0]; exact c.center0
  have hz1 : Subgroup.center ↥G1 = ⊥ := by dsimp only [G1]; exact c.center1
  have hz2 : Subgroup.center ↥G2 = ⊥ := by dsimp only [G2]; exact c.center2
  have hN0 : c.T.map c.π ⊓ G0 = ⊥ := by dsimp only [G0]; exact c.T_inf0
  have hN1 : c.T.map c.π ⊓ G1 = ⊥ := by dsimp only [G1]; exact c.T_inf1
  have hN2 : c.T.map c.π ⊓ G2 = ⊥ := by dsimp only [G2]; exact c.T_inf2
  have hNbar : (c.T.map c.π).Normal := c.T_normal.map c.π c.π_surj
  exact eq_bot_of_sup_commuting_center_eq_bot hsup hcomm01 hcomm02 hcomm12
    hG0norm hG1norm hG2norm hz0 hz1 hz2 hNbar hN0 hN1 hN2

private theorem chief_faithful49_kernel_Ctx.faith
    (c : chief_faithful49_kernel_Ctx H X L Q I N M) :
    ∀ g ∈ I, (∀ n ∈ N, ⁅n, g⁆ ∈ M) → g ∈ Q := by
  intro g hg htriv
  have hgT : (⟨g, hg⟩ : I) ∈ c.T := (c.T_iff ⟨g, hg⟩).mpr htriv
  have hgN : c.π ⟨g, hg⟩ ∈ c.T.map c.π := Subgroup.mem_map_of_mem c.π hgT
  have hbot : c.π ⟨g, hg⟩ = 1 := by
    rw [c.Nbar_eq_bot] at hgN
    exact Subgroup.mem_bot.mp hgN
  exact (c.ker_iff ⟨g, hg⟩).mp hbot

theorem chief_faithful49_kernel {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {N M : Subgroup G} (hch : HChief H N M) (hNQ : N ≤ Q) (hI : ¬ ⁅N, I⁆ ≤ M) :
    ∀ g ∈ I, (∀ n ∈ N, ⁅n, g⁆ ∈ M) → g ∈ Q := by
  obtain ⟨x, hxX, hxgen, hneL, hneL2, hne2⟩ := exists_generator49 h
  exact (chief_faithful49_kernel_Ctx.ofSetup h hch hNQ hI hxX hxgen hneL hneL2 hne2).faith

theorem chief_faithful49 {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {N M : Subgroup G}
    (hch : HChief H N M) (hNQ : N ≤ Q) (hI : ¬ ⁅N, I⁆ ≤ M) :
    ⁅N, Q⁆ ≤ M ∧ ∀ g ∈ I, (∀ n ∈ N, ⁅n, g⁆ ∈ M) → g ∈ Q :=
  ⟨chief_q_trivial49 h hch hNQ, chief_faithful49_kernel h hch hNQ hI⟩

def e2 {R : Type*} [Ring R] (g : R) : R := 1 + g + g ^ 2

theorem e2_mul_self {R : Type*} [CommRing R] (h2 : (2 : R) = 0) {g : R} (hg : g ^ 3 = 1) :
    e2 g * e2 g = e2 g := by
  simp only [e2]
  linear_combination g * hg + (g + g ^ 2 + g ^ 3) * h2

theorem e2_mul_bz {R : Type*} [CommRing R] (h2 : (2 : R) = 0) {b z : R}
    (hb : b ^ 3 = 1) (hz : z ^ 3 = 1) :
    e2 b * e2 (b * z) = e2 b * e2 z := by
  simp only [e2]
  linear_combination (z + z ^ 2 + b * z ^ 2) * hb

theorem e2_mul_bz2 {R : Type*} [CommRing R] (h2 : (2 : R) = 0) {b z : R}
    (hb : b ^ 3 = 1) (hz : z ^ 3 = 1) :
    e2 b * e2 (b * z ^ 2) = e2 b * e2 z := by
  simp only [e2]
  linear_combination (z ^ 2 + z ^ 4 + b * z ^ 4) * hb + (z + b * z + b ^ 2 * z) * hz

theorem e2_bz_mul_bz2 {R : Type*} [CommRing R] (h2 : (2 : R) = 0) {b z : R}
    (hb : b ^ 3 = 1) (hz : z ^ 3 = 1) :
    e2 (b * z) * e2 (b * z ^ 2) = e2 b * e2 z := by
  simp only [e2]
  linear_combination (z ^ 4 + z ^ 5 + b * z ^ 6) * hb +
    (z + z ^ 2 + b + b * z ^ 3 + b ^ 2 + b ^ 2 * z) * hz

theorem e2_sum {R : Type*} [CommRing R] (h2 : (2 : R) = 0) {b z : R}
    (hb : b ^ 3 = 1) (hz : z ^ 3 = 1) :
    e2 b + e2 (b * z) + e2 (b * z ^ 2) + e2 z = 1 + e2 b * e2 z := by
  simp only [e2]
  linear_combination b ^ 2 * z * hz + h2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem two_end : (2 : Module.End (ZMod 2) V) = 0 := by
  ext v
  rw [show (2 : Module.End (ZMod 2) V) = (1 : Module.End (ZMod 2) V) + 1 by norm_num,
    LinearMap.add_apply, Module.End.one_apply, LinearMap.zero_apply]
  rw [← two_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 2) 2 v]
  rw [ZMod.natCast_self 2, zero_smul]

theorem pairwise_commute_pair {a b : Module.End (ZMod 2) V} (hab : a * b = b * a) :
    ({a, b} : Set (Module.End (ZMod 2) V)).Pairwise Commute :=
  (Set.pairwise_insert_of_symm_of_refl).2 ⟨Set.pairwise_singleton b Commute,
    fun c hc => by rw [Set.mem_singleton_iff] at hc; subst hc; exact hab⟩

theorem e2_end_mul_self (g : Module.End (ZMod 2) V) (hg : g ^ 3 = 1) :
    e2 g * e2 g = e2 g := by
  have hcomm : ({g} : Set (Module.End (ZMod 2) V)).Pairwise Commute :=
    Set.pairwise_singleton g Commute
  let S : Subring (Module.End (ZMod 2) V) := Subring.closure ({g} : Set _)
  letI : CommRing S := Subring.closureCommRingOfComm hcomm
  let g' : S := ⟨g, Subring.subset_closure (by simp)⟩
  have hg' : g' ^ 3 = 1 := Subtype.ext (by simpa using hg)
  have h2' : (2 : S) = 0 := by
    apply Subtype.ext
    push_cast
    exact two_end (V := V)
  have key := e2_mul_self (R := S) h2' hg'
  exact congrArg Subtype.val key

theorem e2_end_comm {a b : Module.End (ZMod 2) V} (hab : a * b = b * a) :
    e2 a * e2 b = e2 b * e2 a := by
  let S : Subring (Module.End (ZMod 2) V) := Subring.closure ({a, b} : Set _)
  letI : CommRing S := Subring.closureCommRingOfComm (pairwise_commute_pair hab)
  let a' : S := ⟨a, Subring.subset_closure (by simp)⟩
  let b' : S := ⟨b, Subring.subset_closure (by simp)⟩
  have key : e2 a' * e2 b' = e2 b' * e2 a' := mul_comm _ _
  exact congrArg Subtype.val key

theorem e2_end_mul_bz (B Z : Module.End (ZMod 2) V) (hB : B ^ 3 = 1) (hZ : Z ^ 3 = 1)
    (hBZ : B * Z = Z * B) : e2 B * e2 (B * Z) = e2 B * e2 Z := by
  let S : Subring (Module.End (ZMod 2) V) := Subring.closure ({B, Z} : Set _)
  letI : CommRing S := Subring.closureCommRingOfComm (pairwise_commute_pair hBZ)
  let B' : S := ⟨B, Subring.subset_closure (by simp)⟩
  let Z' : S := ⟨Z, Subring.subset_closure (by simp)⟩
  have hB' : B' ^ 3 = 1 := Subtype.ext (by simpa using hB)
  have hZ' : Z' ^ 3 = 1 := Subtype.ext (by simpa using hZ)
  have h2' : (2 : S) = 0 := by
    apply Subtype.ext
    push_cast
    exact two_end (V := V)
  have key := e2_mul_bz (R := S) h2' hB' hZ'
  exact congrArg Subtype.val key

theorem e2_end_mul_bz2 (B Z : Module.End (ZMod 2) V) (hB : B ^ 3 = 1) (hZ : Z ^ 3 = 1)
    (hBZ : B * Z = Z * B) : e2 B * e2 (B * Z ^ 2) = e2 B * e2 Z := by
  let S : Subring (Module.End (ZMod 2) V) := Subring.closure ({B, Z} : Set _)
  letI : CommRing S := Subring.closureCommRingOfComm (pairwise_commute_pair hBZ)
  let B' : S := ⟨B, Subring.subset_closure (by simp)⟩
  let Z' : S := ⟨Z, Subring.subset_closure (by simp)⟩
  have hB' : B' ^ 3 = 1 := Subtype.ext (by simpa using hB)
  have hZ' : Z' ^ 3 = 1 := Subtype.ext (by simpa using hZ)
  have h2' : (2 : S) = 0 := by
    apply Subtype.ext
    push_cast
    exact two_end (V := V)
  have key := e2_mul_bz2 (R := S) h2' hB' hZ'
  exact congrArg Subtype.val key

theorem e2_end_bz_mul_bz2 (B Z : Module.End (ZMod 2) V) (hB : B ^ 3 = 1) (hZ : Z ^ 3 = 1)
    (hBZ : B * Z = Z * B) : e2 (B * Z) * e2 (B * Z ^ 2) = e2 B * e2 Z := by
  let S : Subring (Module.End (ZMod 2) V) := Subring.closure ({B, Z} : Set _)
  letI : CommRing S := Subring.closureCommRingOfComm (pairwise_commute_pair hBZ)
  let B' : S := ⟨B, Subring.subset_closure (by simp)⟩
  let Z' : S := ⟨Z, Subring.subset_closure (by simp)⟩
  have hB' : B' ^ 3 = 1 := Subtype.ext (by simpa using hB)
  have hZ' : Z' ^ 3 = 1 := Subtype.ext (by simpa using hZ)
  have h2' : (2 : S) = 0 := by
    apply Subtype.ext
    push_cast
    exact two_end (V := V)
  have key := e2_bz_mul_bz2 (R := S) h2' hB' hZ'
  exact congrArg Subtype.val key

theorem e2_end_sum (B Z : Module.End (ZMod 2) V) (hB : B ^ 3 = 1) (hZ : Z ^ 3 = 1)
    (hBZ : B * Z = Z * B) :
    e2 B + e2 (B * Z) + e2 (B * Z ^ 2) + e2 Z = 1 + e2 B * e2 Z := by
  let S : Subring (Module.End (ZMod 2) V) := Subring.closure ({B, Z} : Set _)
  letI : CommRing S := Subring.closureCommRingOfComm (pairwise_commute_pair hBZ)
  let B' : S := ⟨B, Subring.subset_closure (by simp)⟩
  let Z' : S := ⟨Z, Subring.subset_closure (by simp)⟩
  have hB' : B' ^ 3 = 1 := Subtype.ext (by simpa using hB)
  have hZ' : Z' ^ 3 = 1 := Subtype.ext (by simpa using hZ)
  have h2' : (2 : S) = 0 := by
    apply Subtype.ext
    push_cast
    exact two_end (V := V)
  have key := e2_sum (R := S) h2' hB' hZ'
  exact congrArg Subtype.val key

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem add_self_eq_zero_zmod2 (v : V) : v + v = 0 := by
  rw [← two_nsmul]
  exact (Nat.cast_smul_eq_nsmul (ZMod 2) 2 v).symm.trans
    (by rw [ZMod.natCast_self 2, zero_smul])

theorem g_apply_e2 (g : Module.End (ZMod 2) V) (hg : g ^ 3 = 1) (w : V) :
    g (e2 g w) = e2 g w := by
  have h3 : g (g (g w)) = w := by
    have := congrArg (fun f : Module.End (ZMod 2) V => f w) hg
    simpa [pow_succ, mul_assoc, Module.End.mul_apply] using this
  simp only [e2, map_add, LinearMap.add_apply, Module.End.one_apply, pow_two,
    Module.End.mul_apply]
  rw [h3]
  abel

theorem e2_eq_self_iff (g : Module.End (ZMod 2) V) (hg : g ^ 3 = 1) (w : V) :
    e2 g w = w ↔ g w = w := by
  constructor
  · intro h
    have hfix := g_apply_e2 g hg w
    rwa [h] at hfix
  · intro h
    simp only [e2, LinearMap.add_apply, Module.End.one_apply, pow_two, Module.End.mul_apply, h]
    rw [add_assoc, add_self_eq_zero_zmod2, add_zero]

theorem mem_range_e2_iff (g : Module.End (ZMod 2) V) (hg : g ^ 3 = 1) (w : V) :
    w ∈ LinearMap.range (e2 g) ↔ g w = w := by
  constructor
  · intro hw
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hw
    exact g_apply_e2 g hg u
  · intro hw
    exact LinearMap.mem_range.mpr ⟨w, (e2_eq_self_iff g hg w).mpr hw⟩

theorem mul_e2_mul (X Xi B : Module.End (ZMod 2) V) (hXiX : Xi * X = 1) (hXXi : X * Xi = 1) :
    X * e2 B * Xi = e2 (X * B * Xi) := by
  have hB2 : X * B ^ 2 * Xi = (X * B * Xi) ^ 2 := by
    rw [pow_two, pow_two]
    calc X * (B * B) * Xi = X * B * (Xi * X) * B * Xi := by
          rw [hXiX]; noncomm_ring
      _ = (X * B * Xi) * (X * B * Xi) := by noncomm_ring
  simp only [e2, mul_add, add_mul, mul_one, one_mul, mul_assoc, hXiX, hXXi, hB2]

theorem two_pow_mod_three_even (d : ℕ) (h : 2 ^ d % 3 = 1) : Even d := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    rcases d with _ | _ | k
    · exact ⟨0, rfl⟩
    · norm_num at h
    · have h4 : 2 ^ (k + 2) = 4 * 2 ^ k := by
        rw [pow_add]; ring
      rw [h4, Nat.mul_mod] at h
      have h' : 2 ^ k % 3 = 1 := by simpa using h
      obtain ⟨m, hm⟩ := ih k (by omega) h'
      exact ⟨m + 1, by omega⟩

theorem card_eq_four_pow_of_fpf (W : Submodule (ZMod 2) V) (Z : Module.End (ZMod 2) V)
    (hZ : Z ^ 3 = 1) (hW : ∀ w : V, w ∈ W → Z w ∈ W)
    (hfpf : ∀ w : V, w ∈ W → Z w = w → w = 0) :
    ∃ k, Nat.card W = 4 ^ k := by
  classical
  haveI : Fintype W := Fintype.ofFinite W
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d, hd⟩ : ∃ d, Nat.card W = 2 ^ d := by
    refine ⟨Module.finrank (ZMod 2) W, ?_⟩
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2) (V := W), ZMod.card]
  let f : Function.End W := fun w => ⟨Z w.1, hW w.1 w.2⟩
  have hf3 : f ^ 3 = 1 := by
    funext w
    show f (f (f w)) = w
    apply Subtype.ext
    change Z (Z (Z w.1)) = w.1
    have h := congrArg (fun g : Module.End (ZMod 2) V => g w.1) hZ
    simpa [pow_succ, mul_assoc, Module.End.mul_apply] using h
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1)
    (by simpa using hf3)
  have hfix : Fintype.card f.fixedPoints = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨0, ?_⟩, ?_⟩
    · apply Subtype.ext; simp [f]
    · intro b
      apply Subtype.ext
      apply Subtype.ext
      have hb : Z b.1.1 = b.1.1 := by
        have := congrArg Subtype.val b.2
        simpa [f] using this
      exact hfpf b.1.1 b.1.2 hb
  rw [hfix] at hmod
  have hd1 : (2 : ℕ) ^ d % 3 = 1 := by
    have h2 : Fintype.card ↥W = 2 ^ d := by rw [← Nat.card_eq_fintype_card, hd]
    rw [Nat.ModEq, h2] at hmod
    simpa using hmod
  obtain ⟨k, hk⟩ := two_pow_mod_three_even d hd1
  refine ⟨k, ?_⟩
  rw [hd, hk, show k + k = 2 * k by omega, pow_mul]
  norm_num

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem e2_subring_coe {R : Type*} [Ring R] (S : Subring R) (x : S) :
    ((e2 x : S) : R) = e2 (x : R) := by
  simp [e2]

theorem e2_end_comm_of_mem (B Z g h : Module.End (ZMod 2) V) (hBZ : B * Z = Z * B)
    (hg : g ∈ Subring.closure ({B, Z} : Set (Module.End (ZMod 2) V)))
    (hh : h ∈ Subring.closure ({B, Z} : Set (Module.End (ZMod 2) V))) :
    e2 g * e2 h = e2 h * e2 g := by
  let S : Subring (Module.End (ZMod 2) V) := Subring.closure ({B, Z} : Set _)
  letI : CommRing S := Subring.closureCommRingOfComm (pairwise_commute_pair hBZ)
  have key : e2 (⟨g, hg⟩ : S) * e2 (⟨h, hh⟩ : S) = e2 (⟨h, hh⟩ : S) * e2 (⟨g, hg⟩ : S) :=
    mul_comm _ _
  have := congrArg Subtype.val key
  simpa [e2_subring_coe] using this

theorem conj_relations (B Z X Xi : Module.End (ZMod 2) V)
    (hXiX : Xi * X = 1) (hXXi : X * Xi = 1) (hZ : Z ^ 3 = 1)
    (hBZ : B * Z = Z * B) (hXZ : X * Z = Z * X) (hXB : Xi * B * X = B * Z ^ 2) :
    X * B * Xi = B * Z ∧ X * Z * Xi = Z ∧ X * Z ^ 2 * Xi = Z ^ 2 ∧
      X * (B * Z) * Xi = B * Z ^ 2 ∧ X * (B * Z ^ 2) * Xi = B := by
  have hBX : B * X = X * B * Z ^ 2 := by
    calc B * X = (X * Xi) * (B * X) := by rw [hXXi, one_mul]
      _ = X * ((Xi * B) * X) := by noncomm_ring
      _ = X * (B * Z ^ 2) := by rw [hXB]
      _ = X * B * Z ^ 2 := by rw [mul_assoc]
  have hXBX : X * B * Xi = B * Z := by
    have h1 : B * X * Z = X * B := by
      rw [hBX, mul_assoc, ← pow_succ, hZ, mul_one]
    have h2 : X * B = B * Z * X := by
      rw [← h1, mul_assoc, hXZ, mul_assoc]
    calc X * B * Xi = (B * Z * X) * Xi := by rw [h2]
      _ = B * Z * (X * Xi) := by rw [mul_assoc]
      _ = B * Z := by rw [hXXi, mul_one]
  have hXZXi : X * Z * Xi = Z := by rw [hXZ, mul_assoc, hXXi, mul_one]
  have hXZ2 : X * Z ^ 2 = Z ^ 2 * X := by
    rw [pow_two]
    calc X * (Z * Z) = (X * Z) * Z := by rw [mul_assoc]
      _ = (Z * X) * Z := by rw [hXZ]
      _ = Z * (X * Z) := by rw [mul_assoc]
      _ = Z * (Z * X) := by rw [hXZ]
      _ = (Z * Z) * X := by rw [mul_assoc]
  have hXZ2Xi : X * Z ^ 2 * Xi = Z ^ 2 := by rw [hXZ2, mul_assoc, hXXi, mul_one]
  have hXBZ : X * (B * Z) * Xi = B * Z ^ 2 :=
    calc X * (B * Z) * Xi = X * B * (Xi * X) * Z * Xi := by rw [hXiX]; noncomm_ring
      _ = (X * B * Xi) * (X * Z * Xi) := by noncomm_ring
      _ = (B * Z) * Z := by rw [hXBX, hXZXi]
      _ = B * Z ^ 2 := by rw [pow_two, mul_assoc]
  have hXBZ2 : X * (B * Z ^ 2) * Xi = B :=
    calc X * (B * Z ^ 2) * Xi = X * B * (Xi * X) * Z ^ 2 * Xi := by rw [hXiX]; noncomm_ring
      _ = (X * B * Xi) * (X * Z ^ 2 * Xi) := by noncomm_ring
      _ = (B * Z) * Z ^ 2 := by rw [hXBX, hXZ2Xi]
      _ = B * Z ^ 3 := by rw [mul_assoc, ← pow_succ']
      _ = B := by rw [hZ, mul_one]
  exact ⟨hXBX, hXZXi, hXZ2Xi, hXBZ, hXBZ2⟩

theorem mul_X_of_conj (X Xi F G : Module.End (ZMod 2) V) (h : X * F * Xi = G)
    (hXiX : Xi * X = 1) : G * X = X * F := by
  have h' : (X * F * Xi) * X = G * X := by rw [h]
  rw [mul_assoc, hXiX, mul_one] at h'
  exact h'.symm

theorem e2_conj_relations (B Z X Xi : Module.End (ZMod 2) V)
    (hXiX : Xi * X = 1) (hXXi : X * Xi = 1) (hB : B ^ 3 = 1) (hZ : Z ^ 3 = 1)
    (hBZ : B * Z = Z * B) (hXZ : X * Z = Z * X) (hXB : Xi * B * X = B * Z ^ 2) :
    (X * e2 B * Xi = e2 (B * Z)) ∧ (X * e2 (B * Z) * Xi = e2 (B * Z ^ 2)) ∧
      (X * e2 (B * Z ^ 2) * Xi = e2 B) ∧ (X * e2 Z = e2 Z * X) ∧
      (e2 (B * Z) * X = X * e2 B) ∧ (e2 (B * Z ^ 2) * X = X * e2 (B * Z)) ∧
      (e2 B * X = X * e2 (B * Z ^ 2)) := by
  obtain ⟨hXBX, hXZXi, hXZ2Xi, hXBZ, hXBZ2⟩ :=
    conj_relations B Z X Xi hXiX hXXi hZ hBZ hXZ hXB
  have hcB : X * e2 B * Xi = e2 (B * Z) := by rw [mul_e2_mul X Xi B hXiX hXXi, hXBX]
  have hcBZ : X * e2 (B * Z) * Xi = e2 (B * Z ^ 2) := by
    rw [mul_e2_mul X Xi (B * Z) hXiX hXXi, hXBZ]
  have hcBZ2 : X * e2 (B * Z ^ 2) * Xi = e2 B := by
    rw [mul_e2_mul X Xi (B * Z ^ 2) hXiX hXXi, hXBZ2]
  have hcZ : X * e2 Z = e2 Z * X := by
    have h : X * e2 Z * Xi = e2 Z := by rw [mul_e2_mul X Xi Z hXiX hXXi, hXZXi]
    calc X * e2 Z = X * e2 Z * (Xi * X) := by rw [hXiX, mul_one]
      _ = (X * e2 Z * Xi) * X := by noncomm_ring
      _ = e2 Z * X := by rw [h]
  exact ⟨hcB, hcBZ, hcBZ2, hcZ, mul_X_of_conj X Xi (e2 B) (e2 (B * Z)) hcB hXiX,
    mul_X_of_conj X Xi (e2 (B * Z)) (e2 (B * Z ^ 2)) hcBZ hXiX,
    mul_X_of_conj X Xi (e2 (B * Z ^ 2)) (e2 B) hcBZ2 hXiX⟩

theorem e2_mul_comm_of_mem (B Z g : Module.End (ZMod 2) V) (hBZ : B * Z = Z * B)
    (hg : g ∈ Subring.closure ({B, Z} : Set (Module.End (ZMod 2) V))) :
    Z * e2 g = e2 g * Z := by
  let S : Subring (Module.End (ZMod 2) V) := Subring.closure ({B, Z} : Set _)
  letI : CommRing S := Subring.closureCommRingOfComm (pairwise_commute_pair hBZ)
  have hZmem : Z ∈ S := Subring.subset_closure (by simp)
  have key : (⟨Z, hZmem⟩ : S) * e2 (⟨g, hg⟩ : S) = e2 (⟨g, hg⟩ : S) * ⟨Z, hZmem⟩ :=
    mul_comm _ _
  have := congrArg Subtype.val key
  simpa [e2_subring_coe] using this

private structure sixtyFour_le_index_fixed_end_rel (B Z : Module.End (ZMod 2) V) : Prop where
  idemB : IsIdempotentElem (e2 B)
  idemZ : IsIdempotentElem (e2 Z)
  idemBZ : IsIdempotentElem (e2 (B * Z))
  idemBZ2 : IsIdempotentElem (e2 (B * Z ^ 2))
  mulBBZ : e2 B * e2 (B * Z) = e2 B * e2 Z
  mulBBZ2 : e2 B * e2 (B * Z ^ 2) = e2 B * e2 Z
  mulBZBZ2 : e2 (B * Z) * e2 (B * Z ^ 2) = e2 B * e2 Z
  sum : e2 B + e2 (B * Z) + e2 (B * Z ^ 2) + e2 Z = 1 + e2 B * e2 Z
  commZeB : e2 Z * e2 B = e2 B * e2 Z
  commZeBZ : e2 Z * e2 (B * Z) = e2 (B * Z) * e2 Z
  commZeBZ2 : e2 Z * e2 (B * Z ^ 2) = e2 (B * Z ^ 2) * e2 Z
  commBZeB : e2 (B * Z) * e2 B = e2 B * e2 (B * Z)
  commBZ2eB : e2 (B * Z ^ 2) * e2 B = e2 B * e2 (B * Z ^ 2)
  commBZ2eBZ : e2 (B * Z ^ 2) * e2 (B * Z) = e2 (B * Z) * e2 (B * Z ^ 2)
  commZB : Z * e2 B = e2 B * Z
  commZBZ : Z * e2 (B * Z) = e2 (B * Z) * Z
  commZBZ2 : Z * e2 (B * Z ^ 2) = e2 (B * Z ^ 2) * Z
  commZZ : Z * e2 Z = e2 Z * Z

private theorem sixtyFour_le_index_fixed_end_rel_of (B Z : Module.End (ZMod 2) V)
    (hB : B ^ 3 = 1) (hZ : Z ^ 3 = 1) (hBZ : B * Z = Z * B) :
    sixtyFour_le_index_fixed_end_rel B Z := by
  have hBZ3 : (B * Z) ^ 3 = 1 := by rw [Commute.mul_pow hBZ 3, hB, hZ, mul_one]
  have hZ23 : (Z ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hZ, one_pow]
  have hBZ23 : (B * Z ^ 2) ^ 3 = 1 := by
    rw [Commute.mul_pow (Commute.pow_right hBZ 2) 3, hB, hZ23, mul_one]
  have hBmem : B ∈ Subring.closure ({B, Z} : Set (Module.End (ZMod 2) V)) :=
    Subring.subset_closure (by simp)
  have hZmem : Z ∈ Subring.closure ({B, Z} : Set (Module.End (ZMod 2) V)) :=
    Subring.subset_closure (by simp)
  have hBZmem : B * Z ∈ Subring.closure ({B, Z} : Set (Module.End (ZMod 2) V)) :=
    Subring.mul_mem _ hBmem hZmem
  have hBZ2mem : B * Z ^ 2 ∈ Subring.closure ({B, Z} : Set (Module.End (ZMod 2) V)) :=
    Subring.mul_mem _ hBmem (Subring.pow_mem _ hZmem 2)
  exact
    { idemB := e2_end_mul_self B hB
      idemZ := e2_end_mul_self Z hZ
      idemBZ := e2_end_mul_self (B * Z) hBZ3
      idemBZ2 := e2_end_mul_self (B * Z ^ 2) hBZ23
      mulBBZ := e2_end_mul_bz B Z hB hZ hBZ
      mulBBZ2 := e2_end_mul_bz2 B Z hB hZ hBZ
      mulBZBZ2 := e2_end_bz_mul_bz2 B Z hB hZ hBZ
      sum := e2_end_sum B Z hB hZ hBZ
      commZeB := e2_end_comm_of_mem B Z Z B hBZ hZmem hBmem
      commZeBZ := e2_end_comm_of_mem B Z Z (B * Z) hBZ hZmem hBZmem
      commZeBZ2 := e2_end_comm_of_mem B Z Z (B * Z ^ 2) hBZ hZmem hBZ2mem
      commBZeB := e2_end_comm_of_mem B Z (B * Z) B hBZ hBZmem hBmem
      commBZ2eB := e2_end_comm_of_mem B Z (B * Z ^ 2) B hBZ hBZ2mem hBmem
      commBZ2eBZ := e2_end_comm_of_mem B Z (B * Z ^ 2) (B * Z) hBZ hBZ2mem hBZmem
      commZB := e2_mul_comm_of_mem B Z B hBZ hBmem
      commZBZ := e2_mul_comm_of_mem B Z (B * Z) hBZ hBZmem
      commZBZ2 := e2_mul_comm_of_mem B Z (B * Z ^ 2) hBZ hBZ2mem
      commZZ := e2_mul_comm_of_mem B Z Z hBZ hZmem }

private def sixtyFour_le_index_fixed_end_U (Z : Module.End (ZMod 2) V) :
    Submodule (ZMod 2) V :=
  LinearMap.ker (e2 Z)

private def sixtyFour_le_index_fixed_end_Wb (B Z : Module.End (ZMod 2) V) :
    Submodule (ZMod 2) V :=
  LinearMap.range (e2 B) ⊓ sixtyFour_le_index_fixed_end_U Z

private def sixtyFour_le_index_fixed_end_Wbz (B Z : Module.End (ZMod 2) V) :
    Submodule (ZMod 2) V :=
  LinearMap.range (e2 (B * Z)) ⊓ sixtyFour_le_index_fixed_end_U Z

private def sixtyFour_le_index_fixed_end_Wbz2 (B Z : Module.End (ZMod 2) V) :
    Submodule (ZMod 2) V :=
  LinearMap.range (e2 (B * Z ^ 2)) ⊓ sixtyFour_le_index_fixed_end_U Z

private theorem sixtyFour_le_index_fixed_end_U_maps {B Z : Module.End (ZMod 2) V}
    (hrel : sixtyFour_le_index_fixed_end_rel B Z) :
    (∀ u : V, u ∈ sixtyFour_le_index_fixed_end_U Z →
      e2 B u ∈ sixtyFour_le_index_fixed_end_U Z) ∧
    (∀ u : V, u ∈ sixtyFour_le_index_fixed_end_U Z →
      e2 (B * Z) u ∈ sixtyFour_le_index_fixed_end_U Z) ∧
    (∀ u : V, u ∈ sixtyFour_le_index_fixed_end_U Z →
      e2 (B * Z ^ 2) u ∈ sixtyFour_le_index_fixed_end_U Z) ∧
    (∀ u : V, u ∈ sixtyFour_le_index_fixed_end_U Z →
      e2 B u + e2 (B * Z) u + e2 (B * Z ^ 2) u = u) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u hu
    change e2 Z u = 0 at hu
    change e2 Z (e2 B u) = 0
    rw [← Module.End.mul_apply, hrel.commZeB, Module.End.mul_apply, hu, map_zero]
  · intro u hu
    change e2 Z u = 0 at hu
    change e2 Z (e2 (B * Z) u) = 0
    rw [← Module.End.mul_apply, hrel.commZeBZ, Module.End.mul_apply, hu, map_zero]
  · intro u hu
    change e2 Z u = 0 at hu
    change e2 Z (e2 (B * Z ^ 2) u) = 0
    rw [← Module.End.mul_apply, hrel.commZeBZ2, Module.End.mul_apply, hu, map_zero]
  · intro u hu
    change e2 Z u = 0 at hu
    have h4 := congrArg (fun f : Module.End (ZMod 2) V => f u) hrel.sum
    simp only [LinearMap.add_apply, Module.End.one_apply, Module.End.mul_apply] at h4
    rw [hu, map_zero] at h4
    simpa using h4

private theorem sixtyFour_le_index_fixed_end_ann_Wb {B Z : Module.End (ZMod 2) V}
    (hrel : sixtyFour_le_index_fixed_end_rel B Z) :
    (∀ x : V, x ∈ sixtyFour_le_index_fixed_end_Wb B Z → e2 (B * Z) x = 0) ∧
    (∀ x : V, x ∈ sixtyFour_le_index_fixed_end_Wb B Z → e2 (B * Z ^ 2) x = 0) := by
  have hB_idem : ∀ x : V, x ∈ sixtyFour_le_index_fixed_end_Wb B Z → e2 B x = x := fun x hx =>
    (LinearMap.IsIdempotentElem.mem_range_iff hrel.idemB).mp (Submodule.mem_inf.mp hx).1
  constructor
  · intro x hx
    have hxB := hB_idem x hx
    have hxU : e2 Z x = 0 := (Submodule.mem_inf.mp hx).2
    calc e2 (B * Z) x = e2 (B * Z) (e2 B x) := by rw [hxB]
      _ = (e2 (B * Z) * e2 B) x := by rw [Module.End.mul_apply]
      _ = (e2 B * e2 (B * Z)) x := by rw [hrel.commBZeB]
      _ = (e2 B * e2 Z) x := by rw [hrel.mulBBZ]
      _ = e2 B (e2 Z x) := by rw [Module.End.mul_apply]
      _ = 0 := by rw [hxU, map_zero]
  · intro x hx
    have hxB := hB_idem x hx
    have hxU : e2 Z x = 0 := (Submodule.mem_inf.mp hx).2
    calc e2 (B * Z ^ 2) x = e2 (B * Z ^ 2) (e2 B x) := by rw [hxB]
      _ = (e2 (B * Z ^ 2) * e2 B) x := by rw [Module.End.mul_apply]
      _ = (e2 B * e2 (B * Z ^ 2)) x := by rw [hrel.commBZ2eB]
      _ = (e2 B * e2 Z) x := by rw [hrel.mulBBZ2]
      _ = e2 B (e2 Z x) := by rw [Module.End.mul_apply]
      _ = 0 := by rw [hxU, map_zero]

private theorem sixtyFour_le_index_fixed_end_ann_Wbz {B Z : Module.End (ZMod 2) V}
    (hrel : sixtyFour_le_index_fixed_end_rel B Z) :
    (∀ y : V, y ∈ sixtyFour_le_index_fixed_end_Wbz B Z → e2 B y = 0) ∧
    (∀ y : V, y ∈ sixtyFour_le_index_fixed_end_Wbz B Z → e2 (B * Z ^ 2) y = 0) := by
  have hBZ_idem : ∀ y : V, y ∈ sixtyFour_le_index_fixed_end_Wbz B Z →
      e2 (B * Z) y = y := fun y hy =>
    (LinearMap.IsIdempotentElem.mem_range_iff hrel.idemBZ).mp (Submodule.mem_inf.mp hy).1
  constructor
  · intro y hy
    have hyBZ := hBZ_idem y hy
    have hyU : e2 Z y = 0 := (Submodule.mem_inf.mp hy).2
    calc e2 B y = e2 B (e2 (B * Z) y) := by rw [hyBZ]
      _ = (e2 B * e2 (B * Z)) y := by rw [Module.End.mul_apply]
      _ = (e2 B * e2 Z) y := by rw [hrel.mulBBZ]
      _ = e2 B (e2 Z y) := by rw [Module.End.mul_apply]
      _ = 0 := by rw [hyU, map_zero]
  · intro y hy
    have hyBZ := hBZ_idem y hy
    have hyU : e2 Z y = 0 := (Submodule.mem_inf.mp hy).2
    calc e2 (B * Z ^ 2) y = e2 (B * Z ^ 2) (e2 (B * Z) y) := by rw [hyBZ]
      _ = (e2 (B * Z ^ 2) * e2 (B * Z)) y := by rw [Module.End.mul_apply]
      _ = (e2 (B * Z) * e2 (B * Z ^ 2)) y := by rw [hrel.commBZ2eBZ]
      _ = (e2 B * e2 Z) y := by rw [hrel.mulBZBZ2]
      _ = e2 B (e2 Z y) := by rw [Module.End.mul_apply]
      _ = 0 := by rw [hyU, map_zero]

private theorem sixtyFour_le_index_fixed_end_ann_Wbz2 {B Z : Module.End (ZMod 2) V}
    (hrel : sixtyFour_le_index_fixed_end_rel B Z) :
    (∀ z : V, z ∈ sixtyFour_le_index_fixed_end_Wbz2 B Z → e2 B z = 0) ∧
    (∀ z : V, z ∈ sixtyFour_le_index_fixed_end_Wbz2 B Z → e2 (B * Z) z = 0) := by
  have hBZ2_idem : ∀ z : V, z ∈ sixtyFour_le_index_fixed_end_Wbz2 B Z →
      e2 (B * Z ^ 2) z = z := fun z hz =>
    (LinearMap.IsIdempotentElem.mem_range_iff hrel.idemBZ2).mp (Submodule.mem_inf.mp hz).1
  constructor
  · intro z hz
    have hzBZ2 := hBZ2_idem z hz
    have hzU : e2 Z z = 0 := (Submodule.mem_inf.mp hz).2
    calc e2 B z = e2 B (e2 (B * Z ^ 2) z) := by rw [hzBZ2]
      _ = (e2 B * e2 (B * Z ^ 2)) z := by rw [Module.End.mul_apply]
      _ = (e2 B * e2 Z) z := by rw [hrel.mulBBZ2]
      _ = e2 B (e2 Z z) := by rw [Module.End.mul_apply]
      _ = 0 := by rw [hzU, map_zero]
  · intro z hz
    have hzBZ2 := hBZ2_idem z hz
    have hzU : e2 Z z = 0 := (Submodule.mem_inf.mp hz).2
    calc e2 (B * Z) z = e2 (B * Z) (e2 (B * Z ^ 2) z) := by rw [hzBZ2]
      _ = (e2 (B * Z) * e2 (B * Z ^ 2)) z := by rw [Module.End.mul_apply]
      _ = (e2 B * e2 Z) z := by rw [hrel.mulBZBZ2]
      _ = e2 B (e2 Z z) := by rw [Module.End.mul_apply]
      _ = 0 := by rw [hzU, map_zero]

private def sixtyFour_le_index_fixed_end_phi {B Z : Module.End (ZMod 2) V}
    (hrel : sixtyFour_le_index_fixed_end_rel B Z) :
    ↥(sixtyFour_le_index_fixed_end_U Z) →
      (↥(sixtyFour_le_index_fixed_end_Wb B Z) ×
        ↥(sixtyFour_le_index_fixed_end_Wbz B Z)) ×
        ↥(sixtyFour_le_index_fixed_end_Wbz2 B Z) :=
  fun u =>
    ((⟨e2 B u.1, ⟨⟨u.1, rfl⟩, by
        change e2 Z (e2 B u.1) = 0
        rw [← Module.End.mul_apply, hrel.commZeB, Module.End.mul_apply,
          LinearMap.mem_ker.mp u.2, map_zero]⟩⟩,
      ⟨e2 (B * Z) u.1, ⟨⟨u.1, rfl⟩, by
        change e2 Z (e2 (B * Z) u.1) = 0
        rw [← Module.End.mul_apply, hrel.commZeBZ, Module.End.mul_apply,
          LinearMap.mem_ker.mp u.2, map_zero]⟩⟩),
      ⟨e2 (B * Z ^ 2) u.1, ⟨⟨u.1, rfl⟩, by
        change e2 Z (e2 (B * Z ^ 2) u.1) = 0
        rw [← Module.End.mul_apply, hrel.commZeBZ2, Module.End.mul_apply,
          LinearMap.mem_ker.mp u.2, map_zero]⟩⟩)

private theorem sixtyFour_le_index_fixed_end_phi_injective {B Z : Module.End (ZMod 2) V}
    (hrel : sixtyFour_le_index_fixed_end_rel B Z) :
    Function.Injective (sixtyFour_le_index_fixed_end_phi hrel) := by
  obtain ⟨-, -, -, hsum⟩ := sixtyFour_le_index_fixed_end_U_maps hrel
  intro u v huv
  apply Subtype.ext
  have h1 : e2 B u.1 = e2 B v.1 := by
    have := congrArg (fun p : (↥(sixtyFour_le_index_fixed_end_Wb B Z) ×
      ↥(sixtyFour_le_index_fixed_end_Wbz B Z)) ×
      ↥(sixtyFour_le_index_fixed_end_Wbz2 B Z) => p.1.1.1) huv
    exact this
  have h2 : e2 (B * Z) u.1 = e2 (B * Z) v.1 := by
    have := congrArg (fun p : (↥(sixtyFour_le_index_fixed_end_Wb B Z) ×
      ↥(sixtyFour_le_index_fixed_end_Wbz B Z)) ×
      ↥(sixtyFour_le_index_fixed_end_Wbz2 B Z) => p.1.2.1) huv
    exact this
  have h3 : e2 (B * Z ^ 2) u.1 = e2 (B * Z ^ 2) v.1 := by
    have := congrArg (fun p : (↥(sixtyFour_le_index_fixed_end_Wb B Z) ×
      ↥(sixtyFour_le_index_fixed_end_Wbz B Z)) ×
      ↥(sixtyFour_le_index_fixed_end_Wbz2 B Z) => p.2.1) huv
    exact this
  calc u.1 = e2 B u.1 + e2 (B * Z) u.1 + e2 (B * Z ^ 2) u.1 := (hsum u.1 u.2).symm
    _ = e2 B v.1 + e2 (B * Z) v.1 + e2 (B * Z ^ 2) v.1 := by rw [h1, h2, h3]
    _ = v.1 := hsum v.1 v.2

private theorem sixtyFour_le_index_fixed_end_phi_surjective {B Z : Module.End (ZMod 2) V}
    (hrel : sixtyFour_le_index_fixed_end_rel B Z) :
    Function.Surjective (sixtyFour_le_index_fixed_end_phi hrel) := by
  obtain ⟨hBZ_ann, hBZ2_ann⟩ := sixtyFour_le_index_fixed_end_ann_Wb hrel
  obtain ⟨hB_ann, hBZ2_ann2⟩ := sixtyFour_le_index_fixed_end_ann_Wbz hrel
  obtain ⟨hB_ann2, hBZ_ann2⟩ := sixtyFour_le_index_fixed_end_ann_Wbz2 hrel
  have hB_idem : ∀ x : V, x ∈ sixtyFour_le_index_fixed_end_Wb B Z → e2 B x = x := fun x hx =>
    (LinearMap.IsIdempotentElem.mem_range_iff hrel.idemB).mp (Submodule.mem_inf.mp hx).1
  have hBZ_idem : ∀ y : V, y ∈ sixtyFour_le_index_fixed_end_Wbz B Z →
      e2 (B * Z) y = y := fun y hy =>
    (LinearMap.IsIdempotentElem.mem_range_iff hrel.idemBZ).mp (Submodule.mem_inf.mp hy).1
  have hBZ2_idem : ∀ z : V, z ∈ sixtyFour_le_index_fixed_end_Wbz2 B Z →
      e2 (B * Z ^ 2) z = z := fun z hz =>
    (LinearMap.IsIdempotentElem.mem_range_iff hrel.idemBZ2).mp (Submodule.mem_inf.mp hz).1
  intro p
  refine ⟨⟨p.1.1.1 + p.1.2.1 + p.2.1, ?_⟩, ?_⟩
  · exact (sixtyFour_le_index_fixed_end_U Z).add_mem
      ((sixtyFour_le_index_fixed_end_U Z).add_mem p.1.1.2.2 p.1.2.2.2) p.2.2.2
  · apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        change e2 B (p.1.1.1 + p.1.2.1 + p.2.1) = p.1.1.1
        rw [map_add, map_add, hB_idem p.1.1 p.1.1.2, hB_ann p.1.2 p.1.2.2,
          hB_ann2 p.2 p.2.2]
        abel
      · apply Subtype.ext
        change e2 (B * Z) (p.1.1.1 + p.1.2.1 + p.2.1) = p.1.2.1
        rw [map_add, map_add, hBZ_ann p.1.1 p.1.1.2, hBZ_idem p.1.2 p.1.2.2,
          hBZ_ann2 p.2 p.2.2]
        abel
    · apply Subtype.ext
      change e2 (B * Z ^ 2) (p.1.1.1 + p.1.2.1 + p.2.1) = p.2.1
      rw [map_add, map_add, hBZ2_ann p.1.1 p.1.1.2, hBZ2_ann2 p.1.2 p.1.2.2,
        hBZ2_idem p.2 p.2.2]
      abel

private theorem sixtyFour_le_index_fixed_end_card_U {B Z : Module.End (ZMod 2) V}
    (hrel : sixtyFour_le_index_fixed_end_rel B Z) :
    Nat.card ↥(sixtyFour_le_index_fixed_end_U Z) =
      Nat.card ↥(sixtyFour_le_index_fixed_end_Wb B Z) *
        Nat.card ↥(sixtyFour_le_index_fixed_end_Wbz B Z) *
        Nat.card ↥(sixtyFour_le_index_fixed_end_Wbz2 B Z) := by
  have hbij : Function.Bijective (sixtyFour_le_index_fixed_end_phi hrel) :=
    ⟨sixtyFour_le_index_fixed_end_phi_injective hrel,
      sixtyFour_le_index_fixed_end_phi_surjective hrel⟩
  have h := Nat.card_congr (Equiv.ofBijective _ hbij)
  rw [Nat.card_prod, Nat.card_prod] at h
  exact h

private theorem sixtyFour_le_index_fixed_end_card_le_of_maps {X : Module.End (ZMod 2) V}
    {W₁ W₂ : Submodule (ZMod 2) V} (hXinj : Function.Injective X)
    (hmap : ∀ w : V, w ∈ W₁ → X w ∈ W₂) :
    Nat.card ↥W₁ ≤ Nat.card ↥W₂ :=
  Nat.card_le_card_of_injective (fun w : ↥W₁ => ⟨X w.1, hmap w.1 w.2⟩) (fun a b hab =>
    Subtype.ext (hXinj (Subtype.ext_iff.mp hab)))

private theorem sixtyFour_le_index_fixed_end_X_maps {B Z X : Module.End (ZMod 2) V}
    (hrel : sixtyFour_le_index_fixed_end_rel B Z) (hXeZ : X * e2 Z = e2 Z * X)
    (hBZ_X : e2 (B * Z) * X = X * e2 B)
    (hBZ2_X : e2 (B * Z ^ 2) * X = X * e2 (B * Z))
    (hB_X : e2 B * X = X * e2 (B * Z ^ 2)) :
    (∀ w : V, w ∈ sixtyFour_le_index_fixed_end_Wb B Z →
        X w ∈ sixtyFour_le_index_fixed_end_Wbz B Z) ∧
      (∀ w : V, w ∈ sixtyFour_le_index_fixed_end_Wbz B Z →
        X w ∈ sixtyFour_le_index_fixed_end_Wbz2 B Z) ∧
      (∀ w : V, w ∈ sixtyFour_le_index_fixed_end_Wbz2 B Z →
        X w ∈ sixtyFour_le_index_fixed_end_Wb B Z) := by
  have hB_idem : ∀ x : V, x ∈ sixtyFour_le_index_fixed_end_Wb B Z → e2 B x = x := fun x hx =>
    (LinearMap.IsIdempotentElem.mem_range_iff hrel.idemB).mp (Submodule.mem_inf.mp hx).1
  have hBZ_idem : ∀ y : V, y ∈ sixtyFour_le_index_fixed_end_Wbz B Z →
      e2 (B * Z) y = y := fun y hy =>
    (LinearMap.IsIdempotentElem.mem_range_iff hrel.idemBZ).mp (Submodule.mem_inf.mp hy).1
  have hBZ2_idem : ∀ z : V, z ∈ sixtyFour_le_index_fixed_end_Wbz2 B Z →
      e2 (B * Z ^ 2) z = z := fun z hz =>
    (LinearMap.IsIdempotentElem.mem_range_iff hrel.idemBZ2).mp (Submodule.mem_inf.mp hz).1
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    exact ⟨(LinearMap.IsIdempotentElem.mem_range_iff hrel.idemBZ).mpr (by
        change e2 (B * Z) (X w) = X w
        rw [← Module.End.mul_apply, hBZ_X, Module.End.mul_apply, hB_idem w hw]), by
      change e2 Z (X w) = 0
      rw [← Module.End.mul_apply, hXeZ.symm, Module.End.mul_apply,
        (Submodule.mem_inf.mp hw).2, map_zero]⟩
  · intro w hw
    exact ⟨(LinearMap.IsIdempotentElem.mem_range_iff hrel.idemBZ2).mpr (by
        change e2 (B * Z ^ 2) (X w) = X w
        rw [← Module.End.mul_apply, hBZ2_X, Module.End.mul_apply, hBZ_idem w hw]), by
      change e2 Z (X w) = 0
      rw [← Module.End.mul_apply, hXeZ.symm, Module.End.mul_apply,
        (Submodule.mem_inf.mp hw).2, map_zero]⟩
  · intro w hw
    exact ⟨(LinearMap.IsIdempotentElem.mem_range_iff hrel.idemB).mpr (by
        change e2 B (X w) = X w
        rw [← Module.End.mul_apply, hB_X, Module.End.mul_apply, hBZ2_idem w hw]), by
      change e2 Z (X w) = 0
      rw [← Module.End.mul_apply, hXeZ.symm, Module.End.mul_apply,
        (Submodule.mem_inf.mp hw).2, map_zero]⟩

private theorem sixtyFour_le_index_fixed_end_card_eq
    (B Z X Xi : Module.End (ZMod 2) V)
    (hXiX : Xi * X = 1) (hXXi : X * Xi = 1) (hB : B ^ 3 = 1) (hZ : Z ^ 3 = 1)
    (hBZ : B * Z = Z * B) (hXZ : X * Z = Z * X) (hXB : Xi * B * X = B * Z ^ 2) :
    Nat.card ↥(sixtyFour_le_index_fixed_end_Wb B Z) =
        Nat.card ↥(sixtyFour_le_index_fixed_end_Wbz B Z) ∧
      Nat.card ↥(sixtyFour_le_index_fixed_end_Wb B Z) =
        Nat.card ↥(sixtyFour_le_index_fixed_end_Wbz2 B Z) := by
  obtain ⟨_, _, _, hXeZ, hBZ_X, hBZ2_X, hB_X⟩ :=
    e2_conj_relations B Z X Xi hXiX hXXi hB hZ hBZ hXZ hXB
  have hrel := sixtyFour_le_index_fixed_end_rel_of B Z hB hZ hBZ
  have hXinj : Function.Injective X := by
    intro a b hab
    have h := congrArg Xi hab
    simpa [← Module.End.mul_apply, hXiX] using h
  obtain ⟨hm1, hm2, hm3⟩ :=
    sixtyFour_le_index_fixed_end_X_maps hrel hXeZ hBZ_X hBZ2_X hB_X
  have hφ : Nat.card ↥(sixtyFour_le_index_fixed_end_Wb B Z) ≤
      Nat.card ↥(sixtyFour_le_index_fixed_end_Wbz B Z) :=
    sixtyFour_le_index_fixed_end_card_le_of_maps hXinj hm1
  have hψ : Nat.card ↥(sixtyFour_le_index_fixed_end_Wbz B Z) ≤
      Nat.card ↥(sixtyFour_le_index_fixed_end_Wbz2 B Z) :=
    sixtyFour_le_index_fixed_end_card_le_of_maps hXinj hm2
  have hχ : Nat.card ↥(sixtyFour_le_index_fixed_end_Wbz2 B Z) ≤
      Nat.card ↥(sixtyFour_le_index_fixed_end_Wb B Z) :=
    sixtyFour_le_index_fixed_end_card_le_of_maps hXinj hm3
  exact ⟨le_antisymm hφ (hψ.trans hχ), le_antisymm (hφ.trans hψ) hχ⟩

private theorem sixtyFour_le_index_fixed_end_card_Wb {B Z : Module.End (ZMod 2) V}
    (hrel : sixtyFour_le_index_fixed_end_rel B Z) (hZ : Z ^ 3 = 1) :
    ∃ k, Nat.card ↥(sixtyFour_le_index_fixed_end_Wb B Z) = 4 ^ k := by
  have hB_idem : ∀ x : V, x ∈ sixtyFour_le_index_fixed_end_Wb B Z → e2 B x = x := fun x hx =>
    (LinearMap.IsIdempotentElem.mem_range_iff hrel.idemB).mp (Submodule.mem_inf.mp hx).1
  have hWb_Z : ∀ w : V, w ∈ sixtyFour_le_index_fixed_end_Wb B Z →
      Z w ∈ sixtyFour_le_index_fixed_end_Wb B Z := by
    intro w hw
    refine ⟨?_, ?_⟩
    · exact (LinearMap.IsIdempotentElem.mem_range_iff hrel.idemB).mpr (by
        change e2 B (Z w) = Z w
        rw [← Module.End.mul_apply, hrel.commZB.symm, Module.End.mul_apply, hB_idem w hw])
    · change e2 Z (Z w) = 0
      rw [← Module.End.mul_apply, hrel.commZZ.symm, Module.End.mul_apply,
        (Submodule.mem_inf.mp hw).2, map_zero]
  have hWb_fpf : ∀ w : V, w ∈ sixtyFour_le_index_fixed_end_Wb B Z → Z w = w → w = 0 := by
    intro w hw hZw
    have hwU : e2 Z w = 0 := (Submodule.mem_inf.mp hw).2
    have hwE : e2 Z w = w := (e2_eq_self_iff Z hZ w).mpr hZw
    rw [hwE] at hwU
    exact hwU
  exact card_eq_four_pow_of_fpf (sixtyFour_le_index_fixed_end_Wb B Z) Z hZ hWb_Z hWb_fpf

private theorem sixtyFour_le_index_fixed_end_U_ne_bot {B Z : Module.End (ZMod 2) V}
    (hrel : sixtyFour_le_index_fixed_end_rel B Z) (hZ : Z ^ 3 = 1) (hZ1 : Z ≠ 1) :
    sixtyFour_le_index_fixed_end_U Z ≠ ⊥ := by
  have heZ : e2 Z * e2 Z = e2 Z := hrel.idemZ
  intro hbot
  apply hZ1
  ext v
  have hinj : ∀ a b : V, e2 Z a = e2 Z b → a = b := by
    intro a b hab
    have hab' : a - b ∈ sixtyFour_le_index_fixed_end_U Z := by
      change e2 Z (a - b) = 0
      rw [map_sub, hab, sub_self]
    rw [hbot] at hab'
    exact sub_eq_zero.mp (by simpa using hab')
  have h1 : e2 Z (e2 Z v - v) = 0 := by
    rw [map_sub, ← Module.End.mul_apply, heZ, sub_self]
  have h2 : e2 Z v - v = 0 := hinj _ _ (by rw [h1, map_zero])
  have h3 : e2 Z v = v := sub_eq_zero.mp h2
  rw [← h3]
  exact g_apply_e2 Z hZ v

private theorem sixtyFour_le_index_fixed_end_sixty_four_le_card_U {B Z : Module.End (ZMod 2) V}
    (hU_pow : Nat.card ↥(sixtyFour_le_index_fixed_end_U Z) =
      Nat.card ↥(sixtyFour_le_index_fixed_end_Wb B Z) ^ 3)
    (hk : ∃ k, Nat.card ↥(sixtyFour_le_index_fixed_end_Wb B Z) = 4 ^ k)
    (hUne : sixtyFour_le_index_fixed_end_U Z ≠ ⊥) :
    64 ≤ Nat.card ↥(sixtyFour_le_index_fixed_end_U Z) := by
  obtain ⟨k, hk⟩ := hk
  have hU_gt1 : 1 < Nat.card ↥(sixtyFour_le_index_fixed_end_U Z) := by
    have : Nontrivial ↥(sixtyFour_le_index_fixed_end_U Z) := by
      rwa [Submodule.nontrivial_iff_ne_bot]
    exact Finite.one_lt_card_iff_nontrivial.mpr this
  rw [hU_pow, hk]
  have hk1 : 1 ≤ k := by
    by_contra h
    have h0 : k = 0 := by omega
    rw [hU_pow, hk, h0, pow_zero] at hU_gt1
    norm_num at hU_gt1
  calc 64 = 4 ^ 3 := by norm_num
    _ ≤ 4 ^ (k * 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = (4 ^ k) ^ 3 := by rw [pow_mul]

theorem sixtyFour_le_index_fixed_end (B Z X Xi : Module.End (ZMod 2) V)
    (hXiX : Xi * X = 1) (hXXi : X * Xi = 1)
    (hB : B ^ 3 = 1) (hZ : Z ^ 3 = 1) (hBZ : B * Z = Z * B)
    (hXZ : X * Z = Z * X) (hXB : Xi * B * X = B * Z ^ 2) (hZ1 : Z ≠ 1) :
    64 * Nat.card {v : V // Z v = v} ≤ Nat.card V := by
  classical
  have hrel := sixtyFour_le_index_fixed_end_rel_of B Z hB hZ hBZ
  have hcardU := sixtyFour_le_index_fixed_end_card_U hrel
  obtain ⟨hcardWbWbz, hcardWbWbz2⟩ :=
    sixtyFour_le_index_fixed_end_card_eq B Z X Xi hXiX hXXi hB hZ hBZ hXZ hXB
  obtain ⟨k, hk⟩ := sixtyFour_le_index_fixed_end_card_Wb hrel hZ
  have hUne := sixtyFour_le_index_fixed_end_U_ne_bot hrel hZ hZ1
  have hU_pow : Nat.card ↥(sixtyFour_le_index_fixed_end_U Z) =
      Nat.card ↥(sixtyFour_le_index_fixed_end_Wb B Z) ^ 3 := by
    rw [hcardU, ← hcardWbWbz, ← hcardWbWbz2, pow_three]
    ring
  have h64U : 64 ≤ Nat.card ↥(sixtyFour_le_index_fixed_end_U Z) :=
    sixtyFour_le_index_fixed_end_sixty_four_le_card_U hU_pow ⟨k, hk⟩ hUne
  have hcardV : Nat.card ↥(LinearMap.range (e2 Z)) *
      Nat.card ↥(sixtyFour_le_index_fixed_end_U Z) = Nat.card V := by
    have h := Nat.card_congr
      (Submodule.prodEquivOfIsCompl (LinearMap.range (e2 Z))
        (sixtyFour_le_index_fixed_end_U Z)
        (LinearMap.IsIdempotentElem.isCompl hrel.idemZ)).toEquiv
    rw [Nat.card_prod] at h
    exact h
  have hfixcard : Nat.card ↥(LinearMap.range (e2 Z)) = Nat.card {v : V // Z v = v} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun v => mem_range_e2_iff Z hZ v))
  have hV' : Nat.card V = Nat.card {v : V // Z v = v} *
      Nat.card ↥(sixtyFour_le_index_fixed_end_U Z) := by
    rw [← hcardV, hfixcard]
  calc 64 * Nat.card {v : V // Z v = v}
      = Nat.card {v : V // Z v = v} * 64 := Nat.mul_comm _ _
    _ ≤ Nat.card {v : V // Z v = v} *
        Nat.card ↥(sixtyFour_le_index_fixed_end_U Z) := Nat.mul_le_mul_left _ h64U
    _ = Nat.card V := hV'.symm

theorem sixtyFour_le_index_fixed {Γ V : Type*} [Group Γ] [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V]
    (ρ : Γ →* LinearMap.GeneralLinearGroup (ZMod 2) V) {b z x : Γ}
    (hbz : b * z = z * b) (hb : b ^ 3 = 1) (hz : z ^ 3 = 1) (hxz : x * z = z * x)
    (hxb : x⁻¹ * b * x = b * z ^ 2) (hz1 : ρ z ≠ 1) :
    64 * Nat.card {v : V // (ρ z : V →ₗ[ZMod 2] V) v = v} ≤ Nat.card V := by
  let B : Module.End (ZMod 2) V := (ρ b : V →ₗ[ZMod 2] V)
  let Z : Module.End (ZMod 2) V := (ρ z : V →ₗ[ZMod 2] V)
  let X : Module.End (ZMod 2) V := (ρ x : V →ₗ[ZMod 2] V)
  let Xi : Module.End (ZMod 2) V := ((ρ x)⁻¹ : (Module.End (ZMod 2) V)ˣ)
  have hunit : (ρ x)⁻¹ * ρ b * ρ x = ρ b * (ρ z) ^ 2 := by
    rw [← map_inv, ← map_mul, ← map_mul, hxb, map_mul, map_pow]
  have hB : B ^ 3 = 1 := by
    dsimp only [B]
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hb, map_one, Units.val_one]
  have hZ : Z ^ 3 = 1 := by
    dsimp only [Z]
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hz, map_one, Units.val_one]
  have hBZ : B * Z = Z * B := by
    dsimp only [B, Z]
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, hbz]
  have hXZ : X * Z = Z * X := by
    dsimp only [X, Z]
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, hxz]
  have hXiX : Xi * X = 1 := by
    dsimp only [Xi, X]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hXXi : X * Xi = 1 := by
    dsimp only [Xi, X]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hXB : Xi * B * X = B * Z ^ 2 := by
    dsimp only [Xi, B, X, Z]
    rw [← Units.val_mul, ← Units.val_mul, hunit, Units.val_mul, Units.val_pow_eq_pow_val]
  have hZ1 : Z ≠ 1 := fun h => hz1 (Units.ext h)
  exact sixtyFour_le_index_fixed_end B Z X Xi hXiX hXXi hB hZ hBZ hXZ hXB hZ1

private theorem modrest_bA_zA_cube {A : Subgroup G} (hA : CFSG.Open.IsElemAbelian 3 A)
    (a0 a1 a2 : ↥A) :
    (a0 * a1⁻¹) ^ 3 = 1 ∧ (a0 * a1 * a2) ^ 3 = 1 ∧
      (a0 * a1⁻¹) * (a0 * a1 * a2) ^ 2 = a1 * a2⁻¹ := by
  haveI : IsMulCommutative ↥A := hA.1
  have h0 : a0 ^ 3 = 1 := Subtype.ext (hA.2 a0 a0.2)
  have h1 : a1 ^ 3 = 1 := Subtype.ext (hA.2 a1 a1.2)
  have h2 : a2 ^ 3 = 1 := Subtype.ext (hA.2 a2 a2.2)
  refine ⟨?_, ?_, ?_⟩
  · rw [Commute.mul_pow (Commute.all a0 a1⁻¹) 3, h0, inv_pow, h1, inv_one, mul_one]
  · rw [show a0 * a1 * a2 = (a0 * a1) * a2 from rfl,
      Commute.mul_pow (Commute.all (a0 * a1) a2) 3,
      Commute.mul_pow (Commute.all a0 a1) 3, h0, h1, h2, mul_one, mul_one]
  · have hz2 : (a0 * a1 * a2) ^ 2 = a0 ^ 2 * a1 ^ 2 * a2 ^ 2 := by
      rw [show a0 * a1 * a2 = (a0 * a1) * a2 from rfl,
        Commute.mul_pow (Commute.all (a0 * a1) a2) 2,
        Commute.mul_pow (Commute.all a0 a1) 2]
    have h2inv : a2 ^ 2 = a2⁻¹ := by
      have h2' : a2⁻¹ = a2 ^ 2 := by
        calc a2⁻¹ = a2⁻¹ * 1 := by rw [mul_one]
          _ = a2⁻¹ * a2 ^ 3 := by rw [h2]
          _ = a2 ^ 2 := by group
      exact h2'.symm
    rw [hz2, h2inv]
    calc (a0 * a1⁻¹) * (a0 ^ 2 * a1 ^ 2 * a2⁻¹)
        = a0 ^ 3 * a1 * a2⁻¹ := by
          conv_rhs => rw [show a0 ^ 3 = a0 * a0 ^ 2 by rw [pow_succ']]
          conv_rhs => rw [show a1 = a1⁻¹ * a1 ^ 2 by group]
          ac_rfl
      _ = a1 * a2⁻¹ := by rw [h0, one_mul]

private theorem modrest_conj_z_eq {A : Subgroup G} {x : G} {a0 a1 a2 : ↥A}
    (hxcj0 : cj x (a0 : G) = (a1 : G)) (hxcj1 : cj x (a1 : G) = (a2 : G))
    (hxcj2 : cj x (a2 : G) = (a0 : G))
    (hza : a1 * a2 * a0 = a0 * a1 * a2) :
    x * ((a0 : G) * (a1 : G) * (a2 : G)) = ((a0 : G) * (a1 : G) * (a2 : G)) * x := by
  have hcjz : cj x ((a0 : G) * (a1 : G) * (a2 : G)) = (a0 : G) * (a1 : G) * (a2 : G) := by
    have key : cj x ((a0 : G) * (a1 : G) * (a2 : G)) =
        (cj x (a0 : G) * cj x (a1 : G)) * cj x (a2 : G) := by
      rw [show (a0 : G) * (a1 : G) * (a2 : G) = ((a0 : G) * (a1 : G)) * (a2 : G) from rfl,
        cj_mul_cj, cj_mul_cj]
    rw [key, hxcj0, hxcj1, hxcj2]
    exact congrArg Subtype.val hza
  calc x * ((a0 : G) * (a1 : G) * (a2 : G))
      = x * (x⁻¹ * ((a0 : G) * (a1 : G) * (a2 : G)) * x) := by
        rw [show x⁻¹ * ((a0 : G) * (a1 : G) * (a2 : G)) * x =
          (a0 : G) * (a1 : G) * (a2 : G) from hcjz]
    _ = ((a0 : G) * (a1 : G) * (a2 : G)) * x := by group

private theorem modrest_conj_b_eq {A : Subgroup G} {x : G} {a0 a1 a2 : ↥A}
    (hxcj0 : cj x (a0 : G) = (a1 : G)) (hxcj1 : cj x (a1 : G) = (a2 : G))
    (hRkey : (a0 * a1⁻¹) * (a0 * a1 * a2) ^ 2 = a1 * a2⁻¹) :
    x⁻¹ * ((a0 : G) * ((a1 : G))⁻¹) * x = (a1 : G) * ((a2 : G))⁻¹ ∧
      ((a0 : G) * ((a1 : G))⁻¹) * ((a0 : G) * (a1 : G) * (a2 : G)) ^ 2 =
        (a1 : G) * ((a2 : G))⁻¹ := by
  refine ⟨?_, ?_⟩
  · show cj x ((a0 : G) * ((a1 : G))⁻¹) = (a1 : G) * ((a2 : G))⁻¹
    rw [cj_mul_cj]
    have hinv : cj x ((a1 : G)⁻¹) = (cj x (a1 : G))⁻¹ := by
      simp only [cj, inv_inv, mul_inv_rev]
      group
    rw [hinv, hxcj0, hxcj1]
  · have hh := congrArg Subtype.val hRkey
    simpa only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] using hh

private theorem modrest_w49_z_ne_one {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hx : X = Subgroup.zpowers x) {A : Subgroup G} {a n : G} (hd : XAData X L I x A a n)
    (hrel : a * cj x a * cj (x ^ 2) a = 1) : False := by
  have haA : a ∈ A := by rw [hd.gen]; exact Subgroup.subset_closure (by simp)
  have ha1A : cj x a ∈ A := by rw [hd.gen]; exact Subgroup.subset_closure (by simp)
  have ha2A : cj (x ^ 2) a ∈ A := by rw [hd.gen]; exact Subgroup.subset_closure (by simp)
  have hxX : x ∈ X := hx ▸ Subgroup.mem_zpowers x
  have hord3 : orderOf x = 3 := orderOf_eq_three_of_zpowers hx h.card_X
  have hbL : cj x a ∈ Lc L x 1 := by
    simpa only [Lc, pow_one] using conjugate_cj L a x hd.a_mem
  have hcL : cj (x ^ 2) a ∈ Lc L x 2 := conjugate_cj L a (x ^ 2) hd.a_mem
  have hb3 : orderOf (cj x a) = 3 := by
    have hsem : SemiconjBy x⁻¹ a (cj x a) := by simp only [SemiconjBy, cj]; group
    rw [← SemiconjBy.orderOf_eq x⁻¹ hsem]; exact hd.ord
  have hc3 : orderOf (cj (x ^ 2) a) = 3 := by
    have hsem : SemiconjBy (x ^ 2)⁻¹ a (cj (x ^ 2) a) := by simp only [SemiconjBy, cj]; group
    rw [← SemiconjBy.orderOf_eq (x ^ 2)⁻¹ hsem]; exact hd.ord
  have hTQ : A ⊓ Q = ⊥ := inf_eq_bot_of_isPGroup_three_two hd.A3 (isPGroup_Q h)
  have hrel' : a ^ 1 * (cj x a) ^ 1 * (cj (x ^ 2) a) ^ 1 = 1 := by
    simpa only [pow_one] using hrel
  have := independence h hxX hx hord3 hd.a_mem hbL hcL hd.ord hb3 hc3 haA ha1A ha2A hTQ
    (by norm_num) (by norm_num) (by norm_num) hrel'
  omega

theorem chief_w49_relations {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hx : X = Subgroup.zpowers x) {A : Subgroup G} {a n : G} (hd : XAData X L I x A a n) :
    ((a * (cj x a)⁻¹) * (a * cj x a * cj (x ^ 2) a) =
        (a * cj x a * cj (x ^ 2) a) * (a * (cj x a)⁻¹)) ∧
      (a * (cj x a)⁻¹) ^ 3 = 1 ∧
      (a * cj x a * cj (x ^ 2) a) ^ 3 = 1 ∧
      x * (a * cj x a * cj (x ^ 2) a) = (a * cj x a * cj (x ^ 2) a) * x ∧
      x⁻¹ * (a * (cj x a)⁻¹) * x =
        (a * (cj x a)⁻¹) * (a * cj x a * cj (x ^ 2) a) ^ 2 ∧
      (a * cj x a * cj (x ^ 2) a) ≠ 1 := by
  classical
  have haA : a ∈ A := by rw [hd.gen]; exact Subgroup.subset_closure (by simp)
  have ha1A : cj x a ∈ A := by rw [hd.gen]; exact Subgroup.subset_closure (by simp)
  have ha2A : cj (x ^ 2) a ∈ A := by rw [hd.gen]; exact Subgroup.subset_closure (by simp)
  have hbA : a * (cj x a)⁻¹ ∈ A := A.mul_mem haA (A.inv_mem ha1A)
  have hzA : a * cj x a * cj (x ^ 2) a ∈ A := A.mul_mem (A.mul_mem haA ha1A) ha2A
  have hA : CFSG.Open.IsElemAbelian 3 A := hd.reg.2.1
  haveI : IsMulCommutative ↥A := hA.1
  have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv => hA.comm hu hv
  let a0A : ↥A := ⟨a, haA⟩
  let a1A : ↥A := ⟨cj x a, ha1A⟩
  let a2A : ↥A := ⟨cj (x ^ 2) a, ha2A⟩
  obtain ⟨hbA3, hzA3, hRkey⟩ := modrest_bA_zA_cube hA a0A a1A a2A
  have hza : a1A * a2A * a0A = a0A * a1A * a2A := by ac_rfl
  have hxcj0 : cj x (a0A : G) = (a1A : G) := rfl
  have hxA1 : cj x (a1A : G) = (a2A : G) := by
    rw [cj_mul, show x * x = x ^ 2 by rw [pow_two]]
  have hx3 : x ^ 3 = 1 := by
    have hord : orderOf x = 3 := orderOf_eq_three_of_zpowers hx h.card_X
    rw [← hord]; exact pow_orderOf_eq_one x
  have hxA2 : cj x (a2A : G) = (a0A : G) := by
    rw [cj_mul, show x ^ 2 * x = x ^ 3 by group, hx3]
    simp [cj, a0A]
  have hxz := modrest_conj_z_eq hxcj0 hxA1 hxA2 hza
  have hbconj := modrest_conj_b_eq hxcj0 hxA1 hRkey
  refine ⟨hAc _ hbA _ hzA, ?_, ?_, hxz, ?_, ?_⟩
  · have hh := congrArg Subtype.val hbA3
    simpa only [a0A, a1A, Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_one] using hh
  · have hh := congrArg Subtype.val hzA3
    simpa only [a0A, a1A, a2A, Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_one] using hh
  · rw [hbconj.1, hbconj.2]
  · intro hz1
    exact modrest_w49_z_ne_one h hx hd hz1

private theorem modrest_ker_mk'_comp_inclusion {N M K : Subgroup G} [(M.subgroupOf N).Normal]
    (hK_N : K ≤ N) :
    ((QuotientGroup.mk' (M.subgroupOf N)).comp (Subgroup.inclusion hK_N)).ker =
      M.subgroupOf K := by
  rw [← MonoidHom.comap_ker (QuotientGroup.mk' (M.subgroupOf N)) (Subgroup.inclusion hK_N),
    QuotientGroup.ker_mk', Subgroup.subgroupOf, Subgroup.comap_comap,
    Subgroup.subtype_comp_inclusion]
  rfl

private theorem modrest_chiefRep_fixed_of_centralizer {H N M Z : Subgroup G}
    (hch : HChief H N M) [(M.subgroupOf N).Normal]
    [IsElementaryAbelian 2 (N ⧸ M.subgroupOf N)] (z : ↥H) (hz : (z : G) ∈ Z) (a : ↥N)
    (hc : (a : G) ∈ Subgroup.centralizer (Z : Set G)) :
    (chiefRep (p := 2) hch.2.1 hch.2.2.1 z :
      Additive (N ⧸ M.subgroupOf N) →ₗ[ZMod 2] Additive (N ⧸ M.subgroupOf N))
      (Additive.ofMul (a : N ⧸ M.subgroupOf N)) =
      Additive.ofMul (a : N ⧸ M.subgroupOf N) := by
  have hcomm : (z : G) * (a : G) = (a : G) * (z : G) :=
    Subgroup.mem_centralizer_iff.mp hc (z : G) hz
  have hconj : chiefConj hch.2.1 z a = a := by
    apply Subtype.ext
    rw [chiefConj_apply_coe, hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have h := chiefRep_apply_mk (p := 2) hch.2.1 hch.2.2.1 z a
  rw [hconj] at h
  exact h

theorem relIndex_sup_inf_centralizer_le_card_fixed {H N M Z : Subgroup G} (hch : HChief H N M)
    [(M.subgroupOf N).Normal] [IsElementaryAbelian 2 (N ⧸ M.subgroupOf N)]
    (z : ↥H) (hz : (z : G) ∈ Z) :
    M.relIndex ((N ⊓ Subgroup.centralizer (Z : Set G)) ⊔ M) ≤
      Nat.card {v : Additive (N ⧸ M.subgroupOf N) //
        (chiefRep (p := 2) hch.2.1 hch.2.2.1 z :
          Additive (N ⧸ M.subgroupOf N) →ₗ[ZMod 2] Additive (N ⧸ M.subgroupOf N)) v = v} := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A : Subgroup G := N ⊓ Subgroup.centralizer (Z : Set G)
  let K : Subgroup G := A ⊔ M
  have hA_N : A ≤ N := inf_le_left
  have hMN : M ≤ N := hch.1.le
  have hK_N : K ≤ N := sup_le hA_N hMN
  let f : ↥K →* N ⧸ M.subgroupOf N :=
    (QuotientGroup.mk' (M.subgroupOf N)).comp (Subgroup.inclusion hK_N)
  have hker : f.ker = M.subgroupOf K := modrest_ker_mk'_comp_inclusion hK_N
  have hrange : f.range = (A.subgroupOf N).map (QuotientGroup.mk' (M.subgroupOf N)) := by
    change ((QuotientGroup.mk' (M.subgroupOf N)).comp (Subgroup.inclusion hK_N)).range = _
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rw [show K.subgroupOf N = A.subgroupOf N ⊔ M.subgroupOf N from
      Subgroup.subgroupOf_sup hA_N hMN]
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
  have hfixed : ∀ q ∈ f.range,
      (chiefRep (p := 2) hch.2.1 hch.2.2.1 z :
        Additive (N ⧸ M.subgroupOf N) →ₗ[ZMod 2] Additive (N ⧸ M.subgroupOf N))
        (Additive.ofMul q) = Additive.ofMul q := by
    intro q hq
    rw [hrange] at hq
    rcases Subgroup.mem_map.mp hq with ⟨a, ha, rfl⟩
    exact modrest_chiefRep_fixed_of_centralizer hch z hz a (Subgroup.mem_subgroupOf.mp ha).2
  have hle : M.relIndex K ≤ Nat.card {v : Additive (N ⧸ M.subgroupOf N) //
      (chiefRep (p := 2) hch.2.1 hch.2.2.1 z :
        Additive (N ⧸ M.subgroupOf N) →ₗ[ZMod 2] Additive (N ⧸ M.subgroupOf N)) v = v} := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
    refine Nat.card_le_card_of_injective
      (fun q : f.range => (⟨Additive.ofMul (q : N ⧸ M.subgroupOf N),
        hfixed (q : N ⧸ M.subgroupOf N) q.2⟩ : _)) ?_
    intro a b hab
    exact Subtype.ext (Additive.ofMul.injective
      (congrArg (fun x : {v : Additive (N ⧸ M.subgroupOf N) //
          (chiefRep (p := 2) hch.2.1 hch.2.2.1 z :
            Additive (N ⧸ M.subgroupOf N) →ₗ[ZMod 2] Additive (N ⧸ M.subgroupOf N)) v = v} =>
        (x : Additive (N ⧸ M.subgroupOf N))) hab))
  simpa only [K, A] using hle

theorem chief_card_le_card_fixed_mul_wIdx {H N M Z : Subgroup G} (hch : HChief H N M)
    [(M.subgroupOf N).Normal] [IsElementaryAbelian 2 (N ⧸ M.subgroupOf N)]
    (z : ↥H) (hz : (z : G) ∈ Z) :
    Nat.card (Additive (N ⧸ M.subgroupOf N)) ≤
      Nat.card {v : Additive (N ⧸ M.subgroupOf N) //
        (chiefRep (p := 2) hch.2.1 hch.2.2.1 z :
          Additive (N ⧸ M.subgroupOf N) →ₗ[ZMod 2] Additive (N ⧸ M.subgroupOf N)) v = v} *
        wIdx Z N M := by
  have hMN : M ≤ N := hch.1.le
  have hle := relIndex_sup_inf_centralizer_le_card_fixed (hch := hch) (z := z) hz
  have hMK : M ≤ (N ⊓ Subgroup.centralizer (Z : Set G)) ⊔ M := le_sup_right
  have hK_N : (N ⊓ Subgroup.centralizer (Z : Set G)) ⊔ M ≤ N := sup_le inf_le_left hMN
  calc Nat.card (Additive (N ⧸ M.subgroupOf N))
      = Nat.card (N ⧸ M.subgroupOf N) := Nat.card_congr Additive.ofMul.symm
    _ = M.relIndex N := rfl
    _ = M.relIndex ((N ⊓ Subgroup.centralizer (Z : Set G)) ⊔ M) *
          ((N ⊓ Subgroup.centralizer (Z : Set G)) ⊔ M).relIndex N :=
        (Subgroup.relIndex_mul_relIndex M _ N hMK hK_N).symm
    _ ≤ Nat.card {v : Additive (N ⧸ M.subgroupOf N) //
          (chiefRep (p := 2) hch.2.1 hch.2.2.1 z :
            Additive (N ⧸ M.subgroupOf N) →ₗ[ZMod 2] Additive (N ⧸ M.subgroupOf N)) v = v} *
          ((N ⊓ Subgroup.centralizer (Z : Set G)) ⊔ M).relIndex N :=
        Nat.mul_le_mul_right _ hle
    _ = Nat.card {v : Additive (N ⧸ M.subgroupOf N) //
          (chiefRep (p := 2) hch.2.1 hch.2.2.1 z :
            Additive (N ⧸ M.subgroupOf N) →ₗ[ZMod 2] Additive (N ⧸ M.subgroupOf N)) v = v} *
          wIdx Z N M := rfl

private theorem modrest_w49_rho_ze_ne_one {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {N M : Subgroup G} (hch : HChief H N M) [(M.subgroupOf N).Normal]
    [IsElementaryAbelian 2 (N ⧸ M.subgroupOf N)] [Fact (Nat.Prime 2)]
    (hNQ : N ≤ Q) (hI : ¬ ⁅N, I⁆ ≤ M)
    {z : ↥H} (hzI : (z : G) ∈ I) (hz3 : (z : G) ^ 3 = 1) (hz_ne : (z : G) ≠ 1) :
    chiefRep (p := 2) hch.2.1 hch.2.2.1 z ≠ 1 := by
  intro hrho
  have htriv : ∀ nn ∈ N, ⁅nn, (z : G)⁆ ∈ M :=
    fun nn hn => (chiefRep_eq_one_iff (p := 2) hch.2.1 hch.2.2.1 z).mp hrho nn hn
  have hzQ : (z : G) ∈ Q := (chief_faithful49 h hch hNQ hI).2 _ hzI htriv
  obtain ⟨k, hk⟩ := (isPGroup_Q h).exists_card_eq
  let zQ : ↥Q := ⟨(z : G), hzQ⟩
  have hdvd : orderOf zQ ∣ 2 ^ k := by
    rw [← hk]
    exact orderOf_dvd_natCard zQ
  have hordz : orderOf zQ = 3 := by
    apply orderOf_eq_prime
    · exact Subtype.ext hz3
    · intro h1
      exact hz_ne (Subtype.ext_iff.mp h1)
  rw [hordz] at hdvd
  have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  norm_num at h32

private theorem modrest_ze_mem_Z49 {X A : Subgroup G} {x a : G} (hx : X = Subgroup.zpowers x)
    (hxz : x * (a * cj x a * cj (x ^ 2) a) =
      (a * cj x a * cj (x ^ 2) a) * x)
    (hzA : a * cj x a * cj (x ^ 2) a ∈ A) :
    a * cj x a * cj (x ^ 2) a ∈ Z49 X A := by
  refine Subgroup.mem_inf.mpr ⟨hzA, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [hx] at hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (Commute.zpow_left hxz n).eq

theorem chief_w49 {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hx : X = Subgroup.zpowers x) {A : Subgroup G} {a n : G} (hd : XAData X L I x A a n)
    {N M : Subgroup G} (hch : HChief H N M) (hNQ : N ≤ Q) (hI : ¬ ⁅N, I⁆ ≤ M) :
    64 ≤ wIdx (Z49 X A) N M := by
  classical
  haveI hNorm : (M.subgroupOf N).Normal := hch.normal
  haveI hElem : IsElementaryAbelian 2 (N ⧸ M.subgroupOf N) := hch.isElementaryAbelian
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let V := Additive (N ⧸ M.subgroupOf N)
  let ρ : H →* LinearMap.GeneralLinearGroup (ZMod 2) V :=
    chiefRep (p := 2) hch.2.1 hch.2.2.1
  obtain ⟨hbz, hb, hz, hxz, hxb, hz_ne⟩ := chief_w49_relations h hx hd
  have hxX : x ∈ X := hx ▸ Subgroup.mem_zpowers x
  have hxH : x ∈ H := h.X_le hxX
  have haA : a ∈ A := by rw [hd.gen]; exact Subgroup.subset_closure (by simp)
  have ha1A : cj x a ∈ A := by rw [hd.gen]; exact Subgroup.subset_closure (by simp)
  have ha2A : cj (x ^ 2) a ∈ A := by rw [hd.gen]; exact Subgroup.subset_closure (by simp)
  have hbA : a * (cj x a)⁻¹ ∈ A := A.mul_mem haA (A.inv_mem ha1A)
  have hzA : a * cj x a * cj (x ^ 2) a ∈ A := A.mul_mem (A.mul_mem haA ha1A) ha2A
  have hbI : a * (cj x a)⁻¹ ∈ I := hd.A_le hbA
  have hzI : a * cj x a * cj (x ^ 2) a ∈ I := hd.A_le hzA
  have hbH : a * (cj x a)⁻¹ ∈ H := I_le_H h hbI
  have hzH : a * cj x a * cj (x ^ 2) a ∈ H := I_le_H h hzI
  let xe : ↥H := ⟨x, hxH⟩
  let be : ↥H := ⟨a * (cj x a)⁻¹, hbH⟩
  let ze : ↥H := ⟨a * cj x a * cj (x ^ 2) a, hzH⟩
  have hbz' : be * ze = ze * be := Subtype.ext hbz
  have hb' : be ^ 3 = 1 := Subtype.ext hb
  have hz' : ze ^ 3 = 1 := Subtype.ext hz
  have hxz' : xe * ze = ze * xe := Subtype.ext hxz
  have hxb' : xe⁻¹ * be * xe = be * ze ^ 2 := Subtype.ext hxb
  have hz1 : ρ ze ≠ 1 := by
    simpa only [ρ] using modrest_w49_rho_ze_ne_one h hch hNQ hI hzI hz hz_ne
  have hstep := sixtyFour_le_index_fixed (ρ := ρ) (b := be) (z := ze) (x := xe)
    hbz' hb' hz' hxz' hxb' hz1
  have hze : (ze : G) ∈ Z49 X A := modrest_ze_mem_Z49 hx hxz hzA
  have hcard : Nat.card V ≤ Nat.card {v : V // (ρ ze : V →ₗ[ZMod 2] V) v = v} *
      wIdx (Z49 X A) N M := by
    simpa only [V, ρ] using chief_card_le_card_fixed_mul_wIdx (hch := hch) (z := ze) hze
  have hstep' : 64 * Nat.card {v : V // (ρ ze : V →ₗ[ZMod 2] V) v = v} ≤
      wIdx (Z49 X A) N M * Nat.card {v : V // (ρ ze : V →ₗ[ZMod 2] V) v = v} := by
    simpa [mul_comm] using hstep.trans hcard
  haveI : Nonempty {v : V // (ρ ze : V →ₗ[ZMod 2] V) v = v} :=
    Nonempty.intro ⟨0, map_zero (ρ ze : V →ₗ[ZMod 2] V)⟩
  exact Nat.le_of_mul_le_mul_right hstep' Nat.card_pos

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49
