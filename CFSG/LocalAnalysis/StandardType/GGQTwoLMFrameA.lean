module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrame
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBTransport

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord

private lemma qTwoLMFrameA_commSpace_le_subgroupOf {G : Type} [Group G] {Bs L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    ggCommSpace Bs (ggAutomizer L Bs) ≤ L.subgroupOf Bs := by
  rw [ggCommSpace, Subgroup.closure_le]
  rintro c ⟨a, ha, b, rfl⟩
  change ((a b * b⁻¹ : ↥Bs) : G) ∈ L
  rw [mem_ggAutomizer_iff] at ha
  obtain ⟨g, hgL, -, hgact⟩ := ha
  have h1 : ((a b : ↥Bs) : G) = g * b * g⁻¹ := hgact b
  have h2 : ((a b * b⁻¹ : ↥Bs) : G) = g * (b * g⁻¹ * b⁻¹) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, h1]
    group
  rw [h2]
  refine L.mul_mem hgL ?_
  have hbL : b * g * b⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (hN b.2) g).mp hgL
  simpa [mul_assoc] using L.inv_mem hbL

private lemma qTwoLMFrameA_subgroupOf_le_commSpace {G : Type} [Group G] {Bs L : Subgroup G}
    {x : G} {m : ℕ} {V VT : Type} [Group V] [Group VT] (F : QTwoFrame m V VT Bs L x)
    (hcomm : Subgroup.closure {w : VT | ∃ σ v, w = F.permVT σ v * v⁻¹} = ⊤) :
    L.subgroupOf Bs ≤ ggCommSpace Bs (ggAutomizer L Bs) := by
  let inc : ↥(Bs ⊓ L) →* ↥Bs := Subgroup.inclusion inf_le_left
  have hgen : ∀ w : VT, inc (F.thetaT w) ∈ ggCommSpace Bs (ggAutomizer L Bs) := by
    intro w
    have hw : w ∈ Subgroup.closure {w : VT | ∃ σ v, w = F.permVT σ v * v⁻¹} := by
      rw [hcomm]; exact Subgroup.mem_top w
    refine Subgroup.closure_induction
      (p := fun w _ => inc (F.thetaT w) ∈ ggCommSpace Bs (ggAutomizer L Bs)) ?_ ?_ ?_ ?_ hw
    · rintro w ⟨σ, u, rfl⟩
      obtain ⟨n, hnN, hnact⟩ := F.indT σ
      have hmem : ggConjAut Bs hnN (inc (F.thetaT u)) * (inc (F.thetaT u))⁻¹ ∈
          ggCommSpace Bs (ggAutomizer L Bs) :=
        Subgroup.subset_closure ⟨ggConjAut Bs hnN, ggConjAut_mem_ggAutomizer n.2 hnN,
          inc (F.thetaT u), rfl⟩
      convert hmem using 1
      apply Subtype.ext
      simp only [inc, map_mul, map_inv, Subgroup.coe_inclusion, Subgroup.coe_mul,
        Subgroup.coe_inv, ggConjAut_apply]
      rw [hnact u]
    · simp [inc]
    · intro u v _ _ hu hv
      rw [map_mul, map_mul]
      exact Subgroup.mul_mem _ hu hv
    · intro u _ hu
      rw [map_inv, map_inv]
      exact Subgroup.inv_mem _ hu
  intro b hb
  change (b : G) ∈ L at hb
  let t0 : ↥(Bs ⊓ L) := ⟨b, b.2, hb⟩
  have hb' : b = inc (F.thetaT (F.thetaT.symm t0)) := by
    apply Subtype.ext
    simp [inc, t0, Subgroup.coe_inclusion]
  rw [hb']
  exact hgen (F.thetaT.symm t0)

theorem qTwoLMSkel_AL_fixes {G : Type} [Group G] [Finite G] {B Bs L : Subgroup G} {x : G}
    (hG : GGThmIHyp 3 B x L) (hx : x ∈ Bs) :
    ∀ a ∈ ggAutomizer L Bs, a ⟨x, hx⟩ = ⟨x, hx⟩ := by
  intro a ha
  obtain ⟨g, hgL, -, hga⟩ := mem_ggAutomizer_iff.mp ha
  have hgx : x * g = g * x := Subgroup.mem_centralizer_iff.mp
    (hG.2.2.2.2.2.2.1.2.2.2.1.1 hgL) x (Set.mem_singleton x)
  exact Subtype.ext (by rw [hga, ← hgx, mul_inv_cancel_right])

theorem qTwoLMSkel_frame_card {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    {m : ℕ} {V VT : Type} [Group V] [Group VT] {d : ℕ} (F : QTwoFrame m V VT Bs L x)
    (hV : Nat.card V = 3 ^ (d - 1)) (hd : 1 ≤ d) : Nat.card Bs = 3 ^ d := by
  have hker : (ggGamma L F.hN).ker = Subgroup.zpowers (⟨x, F.hx⟩ : ↥Bs) := by
    ext b
    rw [MonoidHom.mem_ker, F.ker b, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hcardker : Nat.card (ggGamma L F.hN).ker = 3 := by
    rw [hker, Nat.card_zpowers, Subgroup.orderOf_mk, F.hord]
  have hcardrange : Nat.card (ggGamma L F.hN).range = 3 ^ (d - 1) := by
    rw [← hV, Nat.card_congr F.theta.toEquiv]
  have hmain := Subgroup.card_ker_mul_card_range (ggGamma L F.hN)
  rw [hcardker, hcardrange] at hmain
  have h3 : 3 * 3 ^ (d - 1) = 3 ^ d := by
    conv_rhs => rw [← Nat.sub_add_cancel hd, pow_succ']
  rw [h3] at hmain
  exact hmain.symm

theorem qTwoLMSkel_frame_fixed {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    {m : ℕ} {V VT : Type} [Group V] [Group VT] (F : QTwoFrame m V VT Bs L x)
    (hfix : ∀ v : V, (∀ σ, F.permV σ v = v) → v = 1) :
    ∀ b : ↥Bs, (∀ a ∈ ggAutomizer L Bs, a b = b) → (b : G) ∈ Subgroup.zpowers x := by
  intro b hb
  let W : Subgroup (MulAut ↥L) := (ggGamma L F.hN).range
  let w : ↥W := ⟨ggGamma L F.hN b, MonoidHom.mem_range.mpr ⟨b, rfl⟩⟩
  have hfixw : ∀ σ : Equiv.Perm (Fin m), F.permV σ (F.theta.symm w) = F.theta.symm w := by
    intro σ
    obtain ⟨n, hn, hncongr⟩ := F.perm_ind σ
    obtain ⟨n', hn'N, hn'conj⟩ := F.link n hn
    have hfixb : ggConjAut Bs hn'N b = b := hb _ (ggConjAut_mem_ggAutomizer n'.2 hn'N)
    have hbx : (n' : G) * b * (n' : G)⁻¹ = b := by
      have h := congrArg Subtype.val hfixb
      simpa [ggConjAut_apply] using h
    have hstep := ggGamma_conj L F.hN n' b ((Subgroup.mem_normalizer_iff.mp hn'N b).mp b.2)
    have hcoe : ((ggConjAut W hn w : ↥W) : MulAut ↥L) = (w : MulAut ↥L) := by
      rw [ggConjAut_apply, ← hn'conj]
      change MulAut.conj n' * ggGamma L F.hN b * (MulAut.conj n')⁻¹ =
        ggGamma L F.hN b
      rw [← hstep]
      exact congrArg (ggGamma L F.hN) (Subtype.ext hbx)
    have hconjw : ggConjAut W hn w = w := Subtype.ext hcoe
    rw [hncongr] at hconjw
    change F.theta (F.permV σ (F.theta.symm w)) = w at hconjw
    apply F.theta.injective
    rw [hconjw, F.theta.apply_symm_apply]
  have hv1 : F.theta.symm w = 1 := hfix _ hfixw
  have hw1 : w = 1 := by
    rw [← F.theta.apply_symm_apply w, hv1, map_one]
  have hγ : ggGamma L F.hN b = 1 := by
    have h := congrArg (fun z : ↥W => (z : MulAut ↥L)) hw1
    simpa [w] using h
  exact (F.ker b).mp hγ

theorem qTwoLMSkel_frame_comm {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    {m : ℕ} {V VT : Type} [Group V] [Group VT] (F : QTwoFrame m V VT Bs L x) (c : ℕ)
    (hcard : Nat.card VT = 3 ^ c)
    (hcomm : Subgroup.closure {w : VT | ∃ σ v, w = F.permVT σ v * v⁻¹} = ⊤) :
    Nat.card (ggCommSpace Bs (ggAutomizer L Bs)) = 3 ^ c := by
  have hE : ggCommSpace Bs (ggAutomizer L Bs) = L.subgroupOf Bs :=
    le_antisymm (qTwoLMFrameA_commSpace_le_subgroupOf F.hN)
      (qTwoLMFrameA_subgroupOf_le_commSpace F hcomm)
  rw [hE]
  calc Nat.card (L.subgroupOf Bs) = Nat.card ↥(Bs ⊓ L) := by
        rw [← Subgroup.inf_subgroupOf_left L Bs]
        exact Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (inf_le_left : Bs ⊓ L ≤ Bs)).toEquiv
    _ = Nat.card VT := (Nat.card_congr F.thetaT.toEquiv).symm
    _ = 3 ^ c := hcard

end CFSG.StandardType.QTwo

end
