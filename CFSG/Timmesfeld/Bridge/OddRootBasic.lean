module

import CFSG.Timmesfeld.Bridge.Asc72RootSet
import CFSG.Timmesfeld.Bridge.OddLocalQd
public import CFSG.Timmesfeld.Bridge.OddLocalDefs
public import CFSG.Timmesfeld.Bridge.OddTranspBasic

public section

namespace CFSG.Timmesfeld.Bridge.OddRoot

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Bridge.OddTransp CFSG.Timmesfeld.Bridge.OddLocal
  CFSG.BenderSuzuki

variable {G : Type} [Group G] {D : Set G}

theorem exists_rootSet_triple (hS : Asc72.Setup G D) (hsq : OddTransp.MeetsSq D) {d : G}
    (hd : d ∈ D) : ∃ v ∈ rootSet D d, v ≠ d ∧ d * v ∈ rootSet D d := by
  obtain ⟨v, hv, hdv, hcomm, hdvD⟩ := OddTransp.exists_mul_mem hS hsq hd
  have hiff : ∀ f ∈ D, Commute f d ↔ Commute f v :=
    Asc72.IsOddTransp.commute_iff_of_mul_mem hS.oddT hd hv hdv hcomm hdvD
  have hv_root : v ∈ rootSet D d := by
    refine ⟨hv, fun f hf => ?_⟩
    exact ⟨fun hvf => ((hiff f hf).mpr hvf.symm).symm,
      fun hdf => ((hiff f hf).mp hdf.symm).symm⟩
  have hdv_root : d * v ∈ rootSet D d := by
    refine ⟨hdvD, fun f hf => ?_⟩
    constructor
    · intro h
      have h' : Commute f (d * v) := h.symm
      exact ((hS.oddT.commute_mul_iff hd hv hf hdv hcomm).mp h').1.symm
    · intro hdf
      exact hdf.mul_left (((hiff f hf).mp hdf.symm).symm)
  exact ⟨v, hv_root, hdv.symm, hdv_root⟩

theorem rootGroup_le_normalizer (hN : IsNormalSet D) (d : G) :
    rootGroup D d ≤ Subgroup.normalizer (rootSet D d) := by
  rw [rootGroup, Subgroup.closure_le]
  intro e he
  have h := OddLocal.mem_normalizer_rootSet_of_commute (d := e) hN (u := e) (y := e)
    (fun f _ => Iff.rfl) (Commute.refl e)
  rwa [rootSet_eq_of_mem he] at h

theorem centralizer_mul_le_normalizer (hD : IsOddTransp D) (hN : IsNormalSet D) {d a b : G}
    (hd : d ∈ D) (ha : a ∈ rootSet D d) (hb : b ∈ rootSet D d) (hab : a ≠ b) :
    Subgroup.centralizer ({a * b} : Set G) ≤ Subgroup.normalizer (rootSet D d) := by
  intro g hg
  exact OddLocal.mem_normalizer_rootSet_of_commute hN
    (fun f hf => OddLocal.commute_mul_iff_of_mem_rootSet hD hd ha hb hab hf)
    (Subgroup.mem_centralizer_singleton_iff.mp hg)

theorem commute_conj_of_two_pow (hD : IsOddTransp D) {w y : G} (hw : w * w = 1) (hy : y ∈ D)
    (hwy : w * y * w⁻¹ ∈ D) (h2 : ∃ k : ℕ, (w * y) ^ 2 ^ k = 1) :
    Commute w (y * w * y⁻¹) := by
  obtain ⟨k, hk⟩ := h2
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  have hyi : y⁻¹ = y := hD.inv_eq hy
  set c : G := y * w * y⁻¹ with hc
  have hc2 : c * c = 1 := by
    rw [hc]
    calc (y * w * y⁻¹) * (y * w * y⁻¹) = y * (w * w) * y⁻¹ := by group
      _ = 1 := by rw [hw, mul_one, mul_inv_cancel]
  have hk' : (y * w) ^ 2 ^ k = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one] at hk ⊢
    rwa [← orderOf_mul_comm_eq y w]
  have hyy' : y * (w * y * w⁻¹) = (y * w) ^ 2 := by
    rw [pow_two, hwi]
    group
  have hdiv : orderOf (y * (w * y * w⁻¹)) ∣ 2 ^ k := by
    rw [hyy']
    exact (orderOf_pow_dvd (x := y * w) 2).trans
      ((orderOf_dvd_iff_pow_eq_one).mpr hk')
  have hdvd2 : orderOf (y * (w * y * w⁻¹)) ∣ 2 := by
    rcases hD.2 y hy (w * y * w⁻¹) hwy with h2dvd | hodd
    · exact h2dvd
    · obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
      rcases j with _ | j
      · rw [hj, pow_zero]
        exact one_dvd 2
      · exfalso
        rw [hj, pow_succ, mul_comm] at hodd
        exact Nat.not_odd_iff_even.mpr (even_two_mul (2 ^ j)) hodd
  have hw_c : w * c = (w * y) ^ 2 := by
    rw [hc, pow_two, hyi]
    group
  have hconj : w * (y * w) ^ 2 * w⁻¹ = (w * y) ^ 2 := by
    rw [hwi, pow_two, pow_two]
    calc w * (y * w * (y * w)) * w = w * y * w * y * (w * w) := by group
      _ = w * y * w * y := by rw [hw, mul_one]
      _ = (w * y) * (w * y) := by group
  have hord : orderOf (w * c) = orderOf (y * (w * y * w⁻¹)) := by
    rw [hw_c, hyy', ← hconj, orderOf_conj_eq]
  have hsq : (w * c) * (w * c) = 1 := by
    rw [← pow_two]
    exact (orderOf_dvd_iff_pow_eq_one).mp (by rwa [← hord] at hdvd2)
  have hcomm : Commute w c :=
    (commute_iff_mul_sq_eq_one hw hc2).mpr (by rw [pow_two]; exact hsq)
  simpa [hc] using hcomm

theorem map_rootGen_conj (hN : IsNormalSet D) (g d x : G) :
    (rootGen D d x).map (MulAut.conj g).toMonoidHom =
      rootGen D (g * d * g⁻¹) (g * x * g⁻¹) := by
  have himage : (MulAut.conj g) '' D = D := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [MulAut.conj_apply] using hN g z hz
    · intro hy
      refine ⟨g⁻¹ * y * g, by simpa [MulAut.conj_apply] using hN g⁻¹ y hy, ?_⟩
      simp only [MulAut.conj_apply]
      group
  have hroot : rootSet D (g * d * g⁻¹) = (MulAut.conj g) '' rootSet D d := by
    have h := rootSet_map (MulAut.conj g) himage d
    simpa [MulAut.conj_apply] using h
  rw [rootGen, rootGen, MonoidHom.map_closure, Set.image_insert_eq, hroot]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

end CFSG.Timmesfeld.Bridge.OddRoot
