module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXNCA
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrEightBC
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrNU

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

variable {A Q O : Subgroup (MulAut W)} {t : MulAut W}

theorem w16n_Q_rank (h : HNon A Q O t) : IsElemAbelianOfRank 3 2 ↥Q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine w16g_isElemAbelianOfRank_of_card (p := 3) (n := 2) ?_ ?_ ?_
  · intro a b
    exact h.hQe.1.is_comm.comm a b
  · intro a
    exact Subtype.ext (by simpa using h.hQe.2 (a : MulAut W) a.2)
  · have h9 := (w16n_shape_aux h).1
    rw [h9]
    norm_num

theorem w16n_Qg_rank (h : HNon A Q O t) (g : MulAut W) :
    IsElemAbelianOfRank 3 2 ↥(Q.map (MulAut.conj g).toMonoidHom) :=
  IsElemAbelianOfRank.of_mulEquiv
    (Subgroup.equivMapOfInjective Q (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
    (w16n_Q_rank h)

theorem w16n_Qg_le_O (h : HNon A Q O t) {g : MulAut W} (hg : g ∈ A) :
    Q.map (MulAut.conj g).toMonoidHom ≤ O := by
  rintro x ⟨q, hq, rfl⟩
  exact h.hOA g hg q (h.hQO hq)

theorem w16n_O_le_normalizer_Qg (h : HNon A Q O t) {g : MulAut W} (hg : g ∈ A) :
    O ≤ Subgroup.normalizer (Q.map (MulAut.conj g).toMonoidHom : Set (MulAut W)) := by
  refine Subgroup.le_normalizer_iff.mpr ?_
  intro n hn x hx
  obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
  have hn' : g⁻¹ * n * g ∈ O := by
    have h1 := h.hOA g⁻¹ (A.inv_mem hg) n hn
    simpa only [inv_inv] using h1
  refine Subgroup.mem_map.mpr ⟨(g⁻¹ * n * g) * q * (g⁻¹ * n * g)⁻¹,
    h.hQN (g⁻¹ * n * g) hn' q hq, ?_⟩
  change (MulAut.conj g) ((g⁻¹ * n * g) * q * (g⁻¹ * n * g)⁻¹) =
    n * (MulAut.conj g) q * n⁻¹
  simp only [MulAut.conj_apply]
  group

theorem w16n_isPOnePlusTwo_K (h : HNon A Q O t) {g : MulAut W} (hg : g ∈ A)
    (hcomm : ⁅Q, Q.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    IsPOnePlusTwo 3 ↥(Q ⊔ Q.map (MulAut.conj g).toMonoidHom) := by
  have hOQ : O ≤ Subgroup.normalizer (Q : Set (MulAut W)) :=
    Subgroup.le_normalizer_iff.mpr (fun n hn q hq => h.hQN n hn q hq)
  exact w16g_isPOnePlusTwo_sup (w16n_Q_rank h) (w16n_Qg_rank h g)
    ((w16n_Qg_le_O h hg).trans hOQ) (h.hQO.trans (w16n_O_le_normalizer_Qg h hg)) hcomm

theorem w16n_K_le_O (h : HNon A Q O t) {g : MulAut W} (hg : g ∈ A) :
    Q ⊔ Q.map (MulAut.conj g).toMonoidHom ≤ O :=
  sup_le h.hQO (w16n_Qg_le_O h hg)

theorem w16n_K_map_conj (h : HNon A Q O t) {g n : MulAut W} (hg : g ∈ A) (hn : n ∈ O) :
    (Q ⊔ Q.map (MulAut.conj g).toMonoidHom).map (MulAut.conj n).toMonoidHom =
      Q ⊔ Q.map (MulAut.conj g).toMonoidHom := by
  have hnorm : ∀ y ∈ O, ∀ x ∈ Q.map (MulAut.conj g).toMonoidHom,
      y * x * y⁻¹ ∈ Q.map (MulAut.conj g).toMonoidHom := by
    intro y hy x hx
    exact ((Subgroup.le_normalizer_iff.mp (w16n_O_le_normalizer_Qg h hg)) y hy) x hx
  have hQg : (Q.map (MulAut.conj g).toMonoidHom).map (MulAut.conj n).toMonoidHom =
      Q.map (MulAut.conj g).toMonoidHom :=
    s13_map_conj_eq_of_normalizes hnorm hn
  rw [Subgroup.map_sup, s13_map_conj_eq_of_normalizes (fun y hy x hx => h.hQN y hy x hx) hn, hQg]

theorem w16n_commutator_K_t (h : HNon A Q O t) {g : MulAut W} :
    ⁅Q ⊔ Q.map (MulAut.conj g).toMonoidHom, Subgroup.zpowers t⁆ ≠ ⊥ := by
  intro hbot
  have hle : Q ⊔ Q.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.centralizer (Subgroup.zpowers t : Set (MulAut W)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  have hQle : Q ≤ Subgroup.centralizer (Subgroup.zpowers t : Set (MulAut W)) :=
    le_trans le_sup_left hle
  apply h.hQ1
  rw [eq_bot_iff]
  intro q hq
  rw [Subgroup.mem_bot]
  have hcomm : t * q = q * t :=
    (Subgroup.mem_centralizer_iff.mp (hQle hq)) t (Subgroup.mem_zpowers t)
  have hfix : t * q * t⁻¹ = q := by rw [hcomm]; group
  have hqinv : q = q⁻¹ := hfix.symm.trans (h.hQinv q hq)
  have hq2 : q * q = 1 := by
    nth_rewrite 2 [hqinv]
    exact mul_inv_cancel q
  have hq3 : q ^ 3 = 1 := h.hQe.2 q hq
  have hq1 : q = 1 := by
    have h1 : q = q ^ 3 * (q ^ 2)⁻¹ := by group
    rw [hq3, pow_two, hq2] at h1
    simpa using h1
  exact hq1

end CFSG.LocalAnalysis.WeakClosure81
