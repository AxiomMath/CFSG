module

public import CFSG.Sporadic.ThSchreier.Max3Aut
public import CFSG.Sporadic.ThSchreier.AutAssembly
public import CFSG.GroupTheory.LocalCores.PrimeSetCoreIsomorphism
import CFSG.GroupTheory.PCore.Transport
public import CFSG.Assembly.DichotomyDefs

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Assembly.Dichotomy

theorem assemblyPCore_eq (p : ℕ) (X : Type*) [Group X] :
    CFSG.Assembly.pCore p X = CFSG.pCore p X := CFSG.Assembly.pCore_eq_pCore p X

theorem charP_of_equiv {H H' : Type*} [Group H] [Group H'] (e : H ≃* H') {p : ℕ}
    (h : dichotomyCharP p H) : dichotomyCharP p H' := by
  unfold dichotomyCharP at h ⊢
  have hpc := CFSG.pCore_map_iso p e
  intro x hx
  have hx' : e.symm x ∈ Subgroup.centralizer (CFSG.pCore p H : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hey : e y ∈ CFSG.pCore p H' := by
      rw [← hpc]
      exact ⟨y, hy, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 hx (e y) hey
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact this
  rw [← hpc, ← e.apply_symm_apply x]
  exact ⟨_, h hx', rfl⟩

theorem oddCore_eq_bot_of_equiv {H H' : Type*} [Group H] [Group H'] [Finite H] [Finite H']
    (e : H ≃* H') (h : CFSG.oddCore H = ⊥) : CFSG.oddCore H' = ⊥ := by
  rw [CFSG.oddCore_eq_piCore] at h ⊢
  rw [← CFSG.LocalCores.prime_set_core_isomorphism e, h, Subgroup.map_bot]

theorem centralizer_map_equiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (u : G) :
    (Subgroup.centralizer {u}).map e.toMonoidHom = Subgroup.centralizer {e u} := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← map_mul, hy, map_mul]
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply, hx]

@[expose] noncomputable def centralizerEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (u : G) : Subgroup.centralizer {u} ≃* Subgroup.centralizer {e u} :=
  (e.subgroupMap _).trans (MulEquiv.subgroupCongr (centralizer_map_equiv e u))

theorem charP_M :
    dichotomyCharP 2 ↥M := by
  unfold dichotomyCharP
  rw [pCore_M]
  intro m hm
  have hz := centralizer_QM m fun g hg => (Subgroup.mem_centralizer_iff.1 hm g hg).symm
  have hzQ : zM ∈ Q.subgroupOf M := Subgroup.mem_subgroupOf.2 z_mem_Q
  exact (Subgroup.zpowers_le.2 hzQ) hz

theorem card_QM :
    Nat.card (Q.subgroupOf M) = 512 := by
  rw [Nat.card_congr eQ.toEquiv, card_Q]

theorem oddCore_M :
    CFSG.oddCore ↥M = ⊥ := by
  refine sSup_eq_bot.2 fun N hN => ?_
  obtain ⟨hNn, hNodd⟩ := hN
  have hdis : Disjoint N (Q.subgroupOf M) := by
    rw [Subgroup.disjoint_def]
    intro x hxN hxQ
    have h1 := Subgroup.orderOf_dvd_natCard N hxN
    have h2 := Subgroup.orderOf_dvd_natCard _ hxQ
    rw [card_QM] at h2
    have h3 : orderOf x ∣ Nat.gcd (Nat.card N) 512 := Nat.dvd_gcd h1 h2
    have h4 : Nat.gcd (Nat.card N) 512 = 1 :=
      Nat.Coprime.pow_right 9 (Nat.coprime_two_right.2 hNodd)
    rw [h4, Nat.dvd_one, orderOf_eq_one_iff] at h3
    exact h3
  rw [eq_bot_iff]
  intro x hx
  have hQn : (Q.subgroupOf M).Normal := normal_Q_subgroupOf_M
  have hz := centralizer_QM x fun g hg =>
    (Subgroup.commute_of_normal_of_disjoint _ _ hNn hQn hdis x g hx hg).eq
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  have h2 : zM ^ (2 : ℤ) = 1 := by rw [zpow_two, zM_mul_self]
  have e : zM ^ k = zM ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
    rw [zpow_add, zpow_mul, h2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · rw [e, hk, zpow_zero]
    exact Subgroup.one_mem _
  · exfalso
    rw [e, hk, zpow_one] at hx
    have h1 := Subgroup.orderOf_dvd_natCard N hx
    have hzo : orderOf zM = 2 := orderOf_eq_prime (by rw [sq]; exact zM_mul_self) zM_ne_one
    rw [hzo] at h1
    exact (Nat.not_even_iff_odd.2 hNodd) (even_iff_two_dvd.2 h1)

theorem nonempty_centralizer_equiv_M
    (hM : Subgroup.centralizer {a} = M)
    (hInv : ∀ u : J, orderOf u = 2 → IsConj a u) {u : J} (hu : orderOf u = 2) :
    Nonempty (Subgroup.centralizer {u} ≃* ↥M) := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 (hInv u hu)
  have e1 : Subgroup.centralizer {a} ≃* Subgroup.centralizer {g * a * g⁻¹} :=
    ((MulAut.conj g).subgroupMap _).trans (MulEquiv.subgroupCongr (centralizer_map_conj g a))
  exact ⟨e1.symm.trans (MulEquiv.subgroupCongr hM)⟩

theorem charP_oddCore_J
    (hM : Subgroup.centralizer {a} = M)
    (hInv : ∀ u : J, orderOf u = 2 → IsConj a u) {u : J} (hu : orderOf u = 2) :
    dichotomyCharP 2 (Subgroup.centralizer {u}) ∧
      CFSG.oddCore (Subgroup.centralizer {u}) = ⊥ := by
  obtain ⟨g, hg⟩ := isConj_iff.1 (hInv u hu)
  have hg' : MulAut.conj g a = u := by rw [MulAut.conj_apply, hg]
  have f : Subgroup.centralizer {a} ≃* Subgroup.centralizer {u} :=
    (centralizerEquiv (MulAut.conj g) a).trans
      (MulEquiv.subgroupCongr (congrArg (fun x => Subgroup.centralizer {x}) hg'))
  have hcharP : dichotomyCharP 2 (Subgroup.centralizer {a} : Subgroup J) := hM ▸ charP_M
  have hodd : CFSG.oddCore (Subgroup.centralizer {a} : Subgroup J) = ⊥ := hM ▸ oddCore_M
  have hfinM : Finite ↥M := Nat.finite_of_card_ne_zero (by rw [card_M]; norm_num)
  have hfin : Finite (Subgroup.centralizer {a} : Subgroup J) := hM ▸ hfinM
  have hfinu : Finite (Subgroup.centralizer {u} : Subgroup J) :=
    Finite.of_equiv _ f.toEquiv
  exact ⟨@charP_of_equiv _ _ (Subgroup.toGroup _) (Subgroup.toGroup _) f 2 hcharP,
    @oddCore_eq_bot_of_equiv _ _ (Subgroup.toGroup _) (Subgroup.toGroup _) hfin hfinu f hodd⟩

end CFSG.Sporadic.ThSchreier
