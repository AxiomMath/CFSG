module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitSpMove

public section

namespace CFSG.StandardType

namespace OrdPNsGen

open Matrix Module SUTB NoOffOm CFSG.RankThree.PartOne.OddIso

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
  {B : (Fin d → K) →ₗ[K] (Fin d → K) →ₗ[K] K} {Γ : Subgroup (GL (Fin d) K)} {p : ℕ}
  {A : Subgroup (GL (Fin d) K)}

theorem card_le_pow_lcm (hBalt : ∀ v, B v v = 0) (hA : GenMax B Γ p A) :
    Nat.card A ≤ p ^ (d / Nat.lcm 2 (OrdPNS.ordQ K p)) := by
  obtain ⟨S, hS, hterm⟩ := exists_terminal_genPieceSet hA
  rw [card_eq_pow_of_terminal hA hS hterm]
  refine Nat.pow_le_pow_right hA.prime.pos ?_
  have hpK : (p : K) ≠ 0 := hA.natCast_ne_zero
  have hδ : 0 < Nat.lcm 2 (OrdPNS.ordQ K p) :=
    Nat.lcm_pos two_pos (OrdPNS.ordQ_pos hA.prime hpK)
  rw [Nat.le_div_iff_mul_le hδ]
  have hle : ∀ y ∈ S, Nat.lcm 2 (OrdPNS.ordQ K p) ≤ finrank K (grng y) := by
    intro y hy
    refine Nat.le_of_dvd ?_ (lcm_dvd_finrank_grng hA.symm hBalt hA.sep hA.prime hA.ne_two
      (hA.iso y (hS.mem y hy)) (hA.pow y (hS.mem y hy)))
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact grng_ne_bot (hS.ne_one y hy)
  calc S.card * Nat.lcm 2 (OrdPNS.ordQ K p) = ∑ _y ∈ S, Nat.lcm 2 (OrdPNS.ordQ K p) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ y ∈ S, finrank K (grng y) := Finset.sum_le_sum hle
    _ = finrank K (genPieceSpan S) := (finrank_genPieceSpan hA hS).symm
    _ ≤ finrank K (Fin d → K) := Submodule.finrank_le _
    _ = d := Module.finrank_fin_fun K

theorem pow_lcm_le_card (hBalt : ∀ v, B v v = 0) (hA : GenMax B Γ p A)
    (hΓ : ∀ g : GL (Fin d) K, (∀ v w, B (glin g v) (glin g w) = B v w) → g ∈ Γ)
    (hne : ∃ c ∈ A, c ≠ 1) : p ^ (d / Nat.lcm 2 (OrdPNS.ordQ K p)) ≤ Nat.card A := by
  classical
  obtain ⟨S, hS, hterm⟩ := exists_terminal_genPieceSet hA
  rw [card_eq_pow_of_terminal hA hS hterm]
  refine Nat.pow_le_pow_right hA.prime.pos ?_
  have hpK : (p : K) ≠ 0 := hA.natCast_ne_zero
  have hδ : 0 < Nat.lcm 2 (OrdPNS.ordQ K p) :=
    Nat.lcm_pos two_pos (OrdPNS.ordQ_pos hA.prime hpK)
  obtain ⟨y₀, hy₀⟩ : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    obtain ⟨c, hc, hc1⟩ := hne
    exact hc1 (hterm c hc fun v hv => by
      have : v = 0 := by simpa [genPieceSpan] using hv
      rw [this, map_zero])
  have hdim : ∀ y ∈ S, finrank K (grng y) = Nat.lcm 2 (OrdPNS.ordQ K p) := by
    intro y hy
    have hyA := hS.mem y hy
    have hne0 : grng y ≠ ⊥ := grng_ne_bot (hS.ne_one y hy)
    refine le_antisymm (finrank_le_lcm_of_minimal hA.symm hA.sep hA.prime hA.ne_two
      (hA.iso y hyA) (hA.pow y hyA) le_rfl hne0 (nondegOn_grng hA hyA) (grng_inv hA hyA hyA)
      fun W hWle hW0 hWnd hWy => OrdPNsGen.GenPieceSet.minimal hA hS hy hWle hW0 hWnd hWy) ?_
    refine Nat.le_of_dvd ?_ (lcm_dvd_finrank_grng hA.symm hBalt hA.sep hA.prime hA.ne_two
      (hA.iso y hyA) (hA.pow y hyA))
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact hne0
  have hX : finrank K (genPieceSpan S) = S.card * Nat.lcm 2 (OrdPNS.ordQ K p) := by
    rw [finrank_genPieceSpan hA hS, Finset.sum_congr rfl hdim, Finset.sum_const, smul_eq_mul]
  have hW := finrank_orth_genPieceSpan_lt hBalt hA hΓ hS hterm hy₀
  rw [hdim y₀ hy₀] at hW
  have hcompl := isCompl_orthogonalBilin_of_sep (B := B) (hS.nondegOn_card hA).1
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  rw [Module.finrank_fin_fun, hX] at hsum
  have hlt : d < (S.card + 1) * Nat.lcm 2 (OrdPNS.ordQ K p) := by
    rw [Nat.succ_mul]
    omega
  exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hδ).mpr hlt)

omit [Finite K] [CharP K 2] in
theorem closure_comm_pow {G : Type*} [Group G] {S : Set G}
    (hc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hp : ∀ x ∈ S, x ^ p = 1) :
    (∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a) ∧
      ∀ a ∈ Subgroup.closure S, a ^ p = 1 := by
  have hcomm : IsMulCommutative (Subgroup.closure S) :=
    Subgroup.isMulCommutative_closure fun x hx y hy _ => hc x hx y hy
  have hc' : ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  refine ⟨hc', fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hp x hx
  | one => exact one_pow p
  | mul x y hx hy ihx ihy =>
    rw [(show Commute x y from hc' x hx y hy).mul_pow, ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

omit [Finite K] [CharP K 2] in
variable (B) in
@[expose] def isoGL : Subgroup (GL (Fin d) K) where
  carrier := {g | ∀ v w, B (glin g v) (glin g w) = B v w}
  mul_mem' {g h} hg hh v w := by
    rw [glin_mul, Module.End.mul_apply, Module.End.mul_apply, hg, hh]
  one_mem' v w := by rw [glin_one]; rfl
  inv_mem' {g} hg v w := by
    rw [← hg (glin g⁻¹ v) (glin g⁻¹ w)]
    simp only [← Module.End.mul_apply, ← glin_mul, mul_inv_cancel, glin_one, Module.End.one_apply]

omit [Finite K] [CharP K 2] in
theorem mem_isoGL {g : GL (Fin d) K} : g ∈ isoGL B ↔ ∀ v w, B (glin g v) (glin g w) = B v w :=
  Iff.rfl

omit [CharP K 2] in
theorem exists_genMax_mem (hB : B.IsSymm) (hBsep : ∀ v, (∀ w, B v w = 0) → v = 0)
    (hp : p.Prime) (hp2 : p ≠ 2) {u : GL (Fin d) K} (hu : u ∈ isoGL B) (hup : u ^ p = 1) :
    ∃ E : Subgroup (GL (Fin d) K), GenMax B (isoGL B) p E ∧ u ∈ E := by
  classical
  set Q : Subgroup (GL (Fin d) K) → Prop := fun E =>
    E ≤ isoGL B ∧ u ∈ E ∧ (∀ a ∈ E, a ^ p = 1) ∧ ∀ a ∈ E, ∀ b ∈ E, a * b = b * a with hQ
  set P : ℕ → Prop := fun k => ∃ E, Q E ∧ Nat.card E = k with hP
  have hQ0 : Q (Subgroup.zpowers u) := by
    have h1 := closure_comm_pow (S := {u}) (p := p) (by simp) (by simpa using hup)
    rw [← Subgroup.zpowers_eq_closure] at h1
    exact ⟨(Subgroup.zpowers_le).mpr hu, Subgroup.mem_zpowers u, h1.2, h1.1⟩
  have hbound : ∀ k, P k → k ≤ Nat.card (GL (Fin d) K) := by
    rintro k ⟨E, -, rfl⟩
    exact Subgroup.card_le_card_group E
  have hP0 : P (Nat.card (Subgroup.zpowers u)) := ⟨_, hQ0, rfl⟩
  set N := Nat.findGreatest P (Nat.card (GL (Fin d) K)) with hN
  obtain ⟨E, hE, hEN⟩ : P N := Nat.findGreatest_spec (hbound _ hP0) hP0
  have hp1 : 1 ≤ p := hp.one_lt.le
  refine ⟨E, ⟨hB, hBsep, hp, hp2, hE.1, hE.2.2.1, hE.2.2.2, fun g hg hgp hgE => ?_,
    fun g hg => hE.1 hg, fun c hc W hW hWA => ?_⟩, hE.2.1⟩
  ·
    set E' := Subgroup.closure ((E : Set (GL (Fin d) K)) ∪ {g}) with hE'
    have h1 := closure_comm_pow (S := (E : Set (GL (Fin d) K)) ∪ {g}) (p := p)
      (by
        rintro x (hx | hx) y (hy | hy)
        · exact hE.2.2.2 x hx y hy
        · rw [Set.mem_singleton_iff.mp hy]; exact (hgE x hx).symm
        · rw [Set.mem_singleton_iff.mp hx]; exact hgE y hy
        · rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy])
      (by
        rintro x (hx | hx)
        · exact hE.2.2.1 x hx
        · rw [Set.mem_singleton_iff.mp hx]; exact hgp)
    have hEE' : E ≤ E' := fun x hx => Subgroup.subset_closure (Or.inl hx)
    have hE'iso : E' ≤ isoGL B := by
      rw [hE', Subgroup.closure_le]
      rintro x (hx | hx)
      · exact hE.1 hx
      · rw [Set.mem_singleton_iff.mp hx]; exact hg
    have hQ' : Q E' := ⟨hE'iso, hEE' hE.2.1, h1.2, h1.1⟩
    have hcard : Nat.card E' ≤ Nat.card E := by
      rw [hEN]
      exact Nat.le_findGreatest (hbound _ ⟨E', hQ', rfl⟩) ⟨E', hQ', rfl⟩
    have heq : E = E' := Subgroup.eq_of_le_of_card_ge hEE' hcard
    rw [heq]
    exact Subgroup.subset_closure (Or.inr rfl)
  ·
    have hcp : glin c ^ p = 1 := by rw [← glin_pow, hE.2.2.1 c hc, glin_one]
    have hzp := restrictElt_pow_eq_one hW (hWA c hc) hcp
    obtain ⟨g, hg⟩ := exists_gl_of_pow hp1 hzp
    refine ⟨g, ?_, hg⟩
    intro v w
    rw [hg]
    exact restrictElt_isometry hW _ hB (hE.1 hc) v w

end OrdPNsGen

end CFSG.StandardType
