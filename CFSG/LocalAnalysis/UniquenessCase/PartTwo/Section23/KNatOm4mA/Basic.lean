module

public import CFSG.Quasithin.Background.HTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatOm4mA

open CFSG.Quasithin

variable {V : Type} [CommGroup V]

private theorem padicValNat_two_le_A03 {n k : ℕ} (hn : 0 < n) (hk : n ≤ 2 ^ k) :
    padicValNat 2 n ≤ k := by
  have hdvd : 2 ^ padicValNat 2 n ∣ n := pow_padicValNat_dvd
  have hle : 2 ^ padicValNat 2 n ≤ n := Nat.le_of_dvd hn hdvd
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (hle.trans hk)

theorem conj_mem_aSet {k : ℕ} {X A : Subgroup (MulAut V)} (hA : A ∈ E3.aSet k X)
    (g : MulAut V) :
    A.map (MulAut.conj g).toMonoidHom ∈ E3.aSet k (X.map (MulAut.conj g).toMonoidHom) := by
  have hcongr : H.congrHom g = (MulAut.conj g).toMonoidHom :=
    MonoidHom.ext fun x => MulEquiv.ext fun w => by
      simp [H.congrHom_apply, MulAut.conj_apply]
  rw [← hcongr]
  exact (H.map_mem_aSet_iff g).mpr hA

theorem not_mem_aSet_succ_of_witness {k : ℕ} {X A : Subgroup (MulAut V)}
    (h : ∃ B : Subgroup (MulAut V), B ≤ A ∧ E3.mQuot A B ≤ k ∧ fixV B ≠ fixV A) :
    A ∉ E3.aSet (k + 1) X := by
  rintro hA
  simp only [E3.aSet, Set.mem_ofPred_eq] at hA
  obtain ⟨B, hBA, hm, hfix⟩ := h
  exact hfix (hA.2.2.2 B hBA (Nat.lt_succ_of_le hm))

theorem fixV_bot_ne_of_ne_bot {A : Subgroup (MulAut V)} (hA : A ≠ ⊥) :
    fixV (⊥ : Subgroup (MulAut V)) ≠ fixV A := by
  intro h
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA
  have hx1 : (x : MulAut V) ≠ 1 := fun h1 => hx (Subtype.ext h1)
  obtain ⟨v, hv⟩ : ∃ v : V, (x : MulAut V) v ≠ v := by
    by_contra hc
    push Not at hc
    exact hx1 (MulEquiv.ext fun v => by simpa using hc v)
  have hvbot : v ∈ fixV (⊥ : Subgroup (MulAut V)) := by
    rw [mem_fixV]
    intro y hy
    rw [Subgroup.mem_bot] at hy
    simp [hy]
  rw [h] at hvbot
  exact hv ((mem_fixV.mp hvbot) (x : MulAut V) x.2)

theorem map_le_normalizer_map {W : Type} [CommGroup W] (e : V ≃* W) {L X : Subgroup (MulAut V)}
    (h : X ≤ Subgroup.normalizer (L : Set (MulAut V))) :
    X.map (CFSG.Quasithin.H.congrHom e) ≤
      Subgroup.normalizer ((L.map (CFSG.Quasithin.H.congrHom e) : Subgroup (MulAut W)) :
        Set (MulAut W)) := by
  have h1 : X.map (H.congrHom e) ≤
      (Subgroup.normalizer (L : Set (MulAut V))).map (H.congrHom e) :=
    Subgroup.map_mono h
  rwa [Subgroup.map_equiv_normalizer_eq L (MulAut.congr e)] at h1

section Finite

variable [Finite V]

private instance finite_mulAut_A03 : Finite (MulAut V) :=
  Finite.of_injective (fun f : MulAut V => (f : V → V)) DFunLike.coe_injective

theorem exists_le_mQuot_le_of_orbit_subset (A : Subgroup (MulAut V)) (v : V) (S : Set V)
    (hS : ∀ x ∈ A, x v ∈ S) {k : ℕ} (hk : Nat.card S ≤ 2 ^ k) :
    ∃ B : Subgroup (MulAut V), B ≤ A ∧ E3.mQuot A B ≤ k ∧ v ∈ fixV B := by
  classical
  let S₁ : Subgroup ↥A := MulAction.stabilizer ↥A v
  let B : Subgroup (MulAut V) := S₁.map A.subtype
  have hBA : B ≤ A := Subgroup.map_subtype_le S₁
  have hfix : v ∈ fixV B := by
    rw [mem_fixV]
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
    exact ha
  refine ⟨B, hBA, ?_, hfix⟩
  have hsub : B.subgroupOf A = S₁ := by
    change (S₁.map A.subtype).comap A.subtype = S₁
    exact Subgroup.comap_map_eq_self_of_injective (f := A.subtype)
      (Subgroup.subtype_injective A) S₁
  have hrel : B.relIndex A = S₁.index := by rw [Subgroup.relIndex, hsub]
  have hidx : S₁.index = (MulAction.orbit ↥A v).ncard := MulAction.index_stabilizer ↥A v
  have hsub2 : MulAction.orbit ↥A v ⊆ S := by
    rintro w ⟨a, rfl⟩
    exact hS (a : MulAut V) a.2
  have horb : (MulAction.orbit ↥A v).ncard ≤ S.ncard := Set.ncard_le_ncard hsub2
  rw [Nat.card_coe_set_eq] at hk
  have hle : S₁.index ≤ 2 ^ k := by
    rw [hidx]
    exact horb.trans hk
  rw [E3.mQuot, hrel]
  exact padicValNat_two_le_A03
    (Nat.pos_of_ne_zero (by rw [← hrel]; exact E3.relIndex_ne_zero' A B)) hle

theorem mQuot_bot_le_of_card_le (A : Subgroup (MulAut V)) {k : ℕ} (hk : Nat.card A ≤ 2 ^ k) :
    E3.mQuot A ⊥ ≤ k := by
  rw [H.mQuot_bot_eq_rk A]
  exact padicValNat_two_le_A03 Nat.card_pos hk

theorem mQuot_zpowers_le_of_card_le {A : Subgroup (MulAut V)} {f : MulAut V} (hf : f ∈ A)
    (hf2 : orderOf f = 2) {k : ℕ} (hk : Nat.card A ≤ 2 ^ (k + 1)) :
    E3.mQuot A (Subgroup.zpowers f) ≤ k := by
  have hTA : Subgroup.zpowers f ≤ A := Subgroup.zpowers_le.mpr hf
  have hcard : Nat.card (Subgroup.zpowers f) = 2 := by
    rw [Nat.card_zpowers, hf2]
  have hrel : (Subgroup.zpowers f).relIndex A * 2 = Nat.card A := by
    have h := Subgroup.relIndex_mul_card (H := Subgroup.zpowers f) (K := A)
    rwa [inf_eq_left.mpr hTA, hcard] at h
  have hle : (Subgroup.zpowers f).relIndex A ≤ 2 ^ k := by
    have hk' := hk
    rw [← hrel, pow_succ] at hk'
    omega
  rw [E3.mQuot]
  exact padicValNat_two_le_A03
    (Nat.pos_of_ne_zero (E3.relIndex_ne_zero' A (Subgroup.zpowers f))) hle

end Finite

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatOm4mA
