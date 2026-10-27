module

public import CFSG.Quasithin.Background.C1PackS15212A
public import CFSG.Quasithin.Background.OddIndexAveraging
public import CFSG.Quasithin.Recognition.Stroth.BenderChief

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_chiefStep_above_of_count_le_one {H Q Z T : Subgroup G} {r : ℕ}
    (hQO : Q ≤ pCoreOf 2 H) (hHQ : H ≤ Subgroup.normalizer (Q : Set G))
    (hZ : IsNormalIn H Q Z)
    (hcount : ∀ c, F112W.IsChiefSeriesBetween H Q Z Q c → c ≤ 1)
    (hnat : ∀ Lo Hi : Subgroup G, Z ≤ Lo → IsChiefStep H Q Lo Hi → ¬ IsCentralStep H Lo Hi →
      Lo.relIndex (centralizerMod Lo Hi T) ≤ r)
    (hr : 1 ≤ r) (hfix : ∀ x ∈ Q, (∀ g ∈ H, g * x * g⁻¹ * x⁻¹ ∈ Z) → x ∈ Z) :
    ∃ N : Subgroup G, Z ≤ N ∧ N ≤ Q ∧ H ≤ Subgroup.normalizer (N : Set G) ∧
      ⁅Q, oTwoUpper H⁆ ≤ N ∧ ⁅N, Q⁆ ≤ Z ∧ (∀ a ∈ N, a * a ∈ Z) ∧
      Z.relIndex (centralizerMod Z N T) ≤ r := by
  classical
  have hQH : Q ≤ H := hQO.trans (pCoreOf_le (r := 2) H)
  have hQ : IsPGroup 2 Q := (pCoreOf_isPGroup (r := 2) H).to_le hQO
  have hQn : IsNormalIn H Q Q :=
    ⟨le_rfl, fun g hg x hx => (Subgroup.mem_normalizer_iff.mp (hHQ hg) x).mp hx⟩
  have hHZ : H ≤ Subgroup.normalizer (Z : Set G) := D14.le_normalizer_of_isNormalIn hZ
  by_cases hZQ : Z = Q
  · refine ⟨Z, le_rfl, hZQ.le, hHZ, ?_, ?_, fun a ha => Z.mul_mem ha ha, ?_⟩
    · rw [hZQ]
      exact F112W.commutator_le_self_of_le_normalizer ((oTwoUpper_le H).trans hHQ)
    · rw [hZQ]
      exact F112W.commutator_le_self_of_le_normalizer
        (Subgroup.le_normalizer : Q ≤ Subgroup.normalizer (Q : Set G))
    · rw [Subgroup.relIndex_eq_one.mpr (centralizerMod_le_left Z Z T)]
      exact hr
  · have hZQlt : Z < Q := lt_of_le_of_ne hZ.1 hZQ
    obtain ⟨N, hNmin⟩ := exists_minimalFor_of_wellFoundedLT
      (fun M : Subgroup G => IsNormalIn H Q M ∧ Z < M)
      (fun M : Subgroup G => Nat.card M) ⟨Q, hQn, hZQlt⟩
    obtain ⟨hNnormal, hZN⟩ := hNmin.prop
    have hstep : IsChiefStep H Q Z N := by
      refine ⟨hNnormal, hZ, hZN, ?_⟩
      intro K hK hZK hKN
      by_cases hKZ : K = Z
      · exact Or.inl hKZ
      · right
        exact Subgroup.eq_of_le_of_card_ge hKN
          (hNmin.le ⟨hK, lt_of_le_of_ne hZK (Ne.symm hKZ)⟩)
    have hnc : ¬ IsCentralStep H Z N := by
      intro hc
      have hNZ : N ≤ Z := fun x hx => hfix x (hstep.1.1 hx) (fun g hg => hc g hg x hx)
      exact (ne_of_lt hstep.2.2.1) (le_antisymm hNZ hstep.2.2.1.le).symm
    obtain ⟨b, hb⟩ := F112W.exists_isChiefSeriesBetween
      (H := H) (U := Q) (W := N) hstep.1 Q hQn hstep.1.1
    obtain ⟨c, hc⟩ := F112W.exists_isChiefSeriesBetween
      (H := H) (U := Q) (W := Z) hZ Q hQn hZ.1
    have ha : F112W.IsChiefSeriesBetween H Q Z N 1 :=
      F112W.IsChiefSeriesBetween.noncentral (n := 0) hstep hnc .refl
    have hA := F112W.eta_eq_add hQH hZ ha
    have hB := F112W.eta_eq_add hQH hstep.1 hb
    have hC := F112W.eta_eq_add hQH hZ hc
    have hc1 : c ≤ 1 := hcount c hc
    have hb0 : b = 0 := by omega
    have hO2N : ⁅Q, oTwoUpper H⁆ ≤ N :=
      (F112W.isChiefSeriesBetween_zero_iff (H := H) (U := Q) hQH hQO hstep.1 hQn
        hstep.1.1).mp (hb0 ▸ hb)
    have hNQZ : ⁅N, Q⁆ ≤ Z :=
      F112W.commutator_le_of_isChiefStep hQ hQH hHQ hstep hstep.1.1
    have hNsq : ∀ a ∈ N, a * a ∈ Z := fun a ha =>
      (chiefStep_section_sq_mem hQ hQH hstep a ha a ha).2
    exact ⟨N, hstep.2.2.1.le, hstep.1.1, D14.le_normalizer_of_isNormalIn hstep.1, hO2N,
      hNQZ, hNsq, hnat Z N le_rfl hstep hnc⟩

theorem commutator_mem_and_sq_mem_of_minimal {H Q Z N S : Subgroup G}
    (hS : IsSylowTwoOf S H) (hQS : Q ≤ S) (hZN : Z ≤ N) (hNQ : N ≤ Q)
    (hHZ : H ≤ Subgroup.normalizer (Z : Set G)) (hHN : H ≤ Subgroup.normalizer (N : Set G))
    (hHQ : H ≤ Subgroup.normalizer (Q : Set G))
    (hO2 : ⁅Q, oTwoUpper H⁆ ≤ N) (hNQZ : ⁅N, Q⁆ ≤ Z) (hNsq : ∀ a ∈ N, a * a ∈ Z)
    (hfix : ∀ x ∈ Q, (∀ g ∈ H, g * x * g⁻¹ * x⁻¹ ∈ Z) → x ∈ Z) :
    (∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ Z) ∧ ∀ x ∈ Q, x * x ∈ Z := by
  classical
  have hQH : Q ≤ H := hQS.trans hS.1
  have hZQ : Z ≤ Q := hZN.trans hNQ
  have hQZ : Q ≤ Subgroup.normalizer (Z : Set G) := hQH.trans hHZ
  set C : Subgroup G := centralizerMod Z Q (oTwoUpper H) with hCdef
  have hZC : Z ≤ C := by
    intro z hz
    rw [hCdef]
    refine ⟨hZQ hz, Subgroup.le_normalizer hz, fun u hu => ?_⟩
    have hw : u * z⁻¹ * u⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (hHZ (oTwoUpper_le H hu)) z⁻¹).mp (Z.inv_mem hz)
    have e : z * u * z⁻¹ * u⁻¹ = z * (u * z⁻¹ * u⁻¹) := by group
    rw [e]
    exact Z.mul_mem hz hw
  have hCeq : C ≤ Z := by
    by_contra hCZ
    have hZlt : Z < C := lt_of_le_of_ne hZC (fun hZC' => hCZ (le_of_eq hZC'.symm))
    have hCQ : C ≤ Q := by
      rw [hCdef]
      exact centralizerMod_le_left Z Q (oTwoUpper H)
    have hSC : S ≤ Subgroup.normalizer (C : Set G) :=
      le_normalizer_centralizerMod (hS.1.trans hHZ) (hS.1.trans hHQ)
        (hS.1.trans (le_normalizer_oTwoUpper H))
    obtain ⟨z0, hz0C, hz0Z, hz0fix⟩ :=
      exists_fixed_mod hS.2.1 (hCQ.trans hQS) hZlt hSC (hS.1.trans hHZ)
    have hz0C' : z0 ∈ centralizerMod Z Q (oTwoUpper H) := hCdef ▸ hz0C
    have hz0Q : z0 ∈ Q := (mem_centralizerMod.mp hz0C').1
    have hfixH : ∀ g ∈ H, g * z0 * g⁻¹ * z0⁻¹ ∈ Z := by
      have hmemO : oTwoUpper H ≤
          centralizerMod Z (Subgroup.normalizer (Z : Set G)) (Subgroup.zpowers z0) := by
        intro u hu
        refine (mem_centralizerMod_zpowers_iff_of_normalizer (N := Subgroup.normalizer (Z : Set G))
          (L := Z) le_rfl hz0C'.2.1 (hHZ (oTwoUpper_le H hu))).2 ?_
        have h2 := Z.inv_mem (hz0C'.2.2 u hu)
        have e : (z0 * u * z0⁻¹ * u⁻¹)⁻¹ = u * z0 * u⁻¹ * z0⁻¹ := by group
        rwa [e] at h2
      have hmemS : S ≤
          centralizerMod Z (Subgroup.normalizer (Z : Set G)) (Subgroup.zpowers z0) := by
        intro s hs
        exact (mem_centralizerMod_zpowers_iff_of_normalizer (N := Subgroup.normalizer (Z : Set G))
          (L := Z) le_rfl hz0C'.2.1 (hS.1.trans hHZ hs)).2 (hz0fix s hs)
      have hHM : H ≤
          centralizerMod Z (Subgroup.normalizer (Z : Set G)) (Subgroup.zpowers z0) := by
        rw [← C1Pack12.oTwoUpper_sup_eq_of_sylow hS]
        exact sup_le hmemO hmemS
      intro g hg
      exact (mem_centralizerMod.mp (hHM hg)).2.2 z0 (Subgroup.mem_zpowers z0)
    exact hz0Z (hfix z0 hz0Q hfixH)
  have hfixO : ∀ x ∈ Q, (∀ u ∈ oTwoUpper H, u * x * u⁻¹ * x⁻¹ ∈ Z) → x ∈ Z := by
    intro x hxQ hxO
    have hxC : x ∈ C := by
      rw [hCdef]
      refine ⟨hxQ, hQZ hxQ, fun u hu => ?_⟩
      have h1 := Z.inv_mem (hxO u hu)
      have e : (u * x * u⁻¹ * x⁻¹)⁻¹ = x * u * x⁻¹ * u⁻¹ := by group
      rwa [e] at h1
    exact hCeq hxC
  have hNab : ∀ a ∈ N, ∀ b ∈ N, a * b * a⁻¹ * b⁻¹ ∈ Z := by
    intro a ha b hb
    have h := hNQZ (Subgroup.commutator_mem_commutator ha (hNQ hb))
    rwa [commutatorElement_def] at h
  have hNQZinv : ∀ a ∈ N, ∀ x ∈ Q, x * a * x⁻¹ * a⁻¹ ∈ Z := by
    intro a ha x hx
    have h2 := Z.inv_mem (hNQZ (Subgroup.commutator_mem_commutator ha hx))
    have e : ⁅a, x⁆⁻¹ = x * a * x⁻¹ * a⁻¹ := by
      rw [commutatorElement_def]
      group
    rwa [e] at h2
  have htriv : ∀ h ∈ oTwoUpper H, ∀ x ∈ Q, h * x * h⁻¹ * x⁻¹ ∈ N := by
    intro h hh x hx
    have h2 := N.inv_mem (hO2 (Subgroup.commutator_mem_commutator hx hh))
    have e : ⁅x, h⁆⁻¹ = h * x * h⁻¹ * x⁻¹ := by
      rw [commutatorElement_def]
      group
    rwa [e] at h2
  exact commutator_mem_and_sq_mem_of_fixed (H := oTwoUpper H) hZN hNQ
    ((oTwoUpper_le H).trans hHZ) ((oTwoUpper_le H).trans hHN)
    ((oTwoUpper_le H).trans hHQ) hQZ hNab hNsq hNQZinv htriv hfixO

theorem centralizerMod_sylow_le_of_elemAbelian {H Q Z N S : Subgroup G}
    (hS : IsSylowTwoOf S H) (hZN : Z ≤ N) (hNQ : N ≤ Q)
    (hHZ : H ≤ Subgroup.normalizer (Z : Set G)) (hHN : H ≤ Subgroup.normalizer (N : Set G))
    (hHQ : H ≤ Subgroup.normalizer (Q : Set G)) (hHO : H = oTwoUpper H ⊔ Q)
    (hO2 : ⁅Q, oTwoUpper H⁆ ≤ N)
    (hab : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ Z) (hsq : ∀ x ∈ Q, x * x ∈ Z)
    (hfix : ∀ x ∈ Q, (∀ g ∈ H, g * x * g⁻¹ * x⁻¹ ∈ Z) → x ∈ Z) :
    centralizerMod Z Q S ≤ N := by
  classical
  have hQH : Q ≤ H := by
    rw [hHO]
    exact le_sup_right
  have hodd : Odd (S.relIndex H) := by
    rw [Subgroup.relIndex, ← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact hS.2.2
  have hsup : oTwoUpper H ⊔ Q ≤ centralizerMod N H Q := by
    refine sup_le ?_ ?_
    · intro o ho
      refine ⟨oTwoUpper_le H ho, hHN (oTwoUpper_le H ho), fun x hx => ?_⟩
      have h2 := N.inv_mem (hO2 (Subgroup.commutator_mem_commutator hx ho))
      have e : ⁅x, o⁆⁻¹ = o * x * o⁻¹ * x⁻¹ := by
        rw [commutatorElement_def]
        group
      rwa [e] at h2
    · intro q hq
      refine ⟨hQH hq, hHN (hQH hq), fun x hx => ?_⟩
      have h2 := N.inv_mem (hZN (hab x hx q hq))
      have e : (x * q * x⁻¹ * q⁻¹)⁻¹ = q * x * q⁻¹ * x⁻¹ := by group
      rwa [e] at h2
  have htriv : ∀ p ∈ H, ∀ x ∈ Q, p * x * p⁻¹ * x⁻¹ ∈ N := by
    intro p hp x hx
    exact (mem_centralizerMod.mp ((le_of_eq hHO).trans hsup hp)).2.2 x hx
  exact mem_of_centralizerMod_odd hS.1 hodd hZN hNQ hHZ hHN hHQ hab hsq htriv hfix

end CFSG.Quasithin.Stroth
