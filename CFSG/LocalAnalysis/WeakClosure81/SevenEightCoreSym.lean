module

public import CFSG.LocalAnalysis.WeakClosure81.SevenEightSteps

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem seven_eight_core_sym_relIndex_conjSubgroup_eq (A B : Subgroup G) (k : G) :
    (conjSubgroup A k).relIndex (conjSubgroup B k) = A.relIndex B := by
  simp only [CFSG.Quasithin.conjSubgroup]
  exact Subgroup.relIndex_map_map_of_injective A B (MulAut.conj k⁻¹).injective

private theorem seven_eight_core_sym_relIndex_eq_two {V H E J L : Subgroup G}
    (h : Hyp78 V H E J L) (hV2 : J.relIndex V = 2) {U : Subgroup G}
    (hU : U ∈ omegaSet V H E) : J.relIndex U = 2 := by
  obtain ⟨k, hkK, rfl⟩ := h.transitive U hU
  have hKleH : kSub V H E ≤ H := kSub_le_of_forall_le h.omega_le
  have hkH : k ∈ H := hKleH hkK
  have hJleH : J ≤ H := h.pcore_le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hJnormH : H ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_subgroupOf_normal hJleH h.jnormal
  have hJk : conjSubgroup J k = J :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (hJnormH hkH)
  have hstep : (conjSubgroup J k).relIndex (conjSubgroup V k) = J.relIndex V :=
    seven_eight_core_sym_relIndex_conjSubgroup_eq J V k
  rw [hJk, hV2] at hstep
  exact hstep

private theorem seven_eight_core_sym_inf_pCoreOf_eq_inf_J {V H E J L : Subgroup G}
    (h : Hyp78 V H E J L) (hV2 : J.relIndex V = 2) {U : Subgroup G}
    (hU : U ∈ omegaSet V H E) (hUleL : U ≤ L) (hUnleO : ¬ U ≤ pCoreOf 2 L) :
    U ⊓ pCoreOf 2 L = U ⊓ J := by
  have hJO : J ⊓ U ≤ pCoreOf 2 L ⊓ U := by
    intro x hx
    obtain ⟨hxJ, hxU⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr
      ⟨seven_eight_inf_J_le_pCoreOf h (Subgroup.mem_inf.mpr ⟨hUleL hxU, hxJ⟩), hxU⟩
  have hJU : (J ⊓ U).relIndex U = 2 := by
    rw [Subgroup.inf_relIndex_right]
    exact seven_eight_core_sym_relIndex_eq_two h hV2 hU
  have hprod : (J ⊓ U).relIndex (pCoreOf 2 L ⊓ U) * (pCoreOf 2 L ⊓ U).relIndex U = 2 := by
    rw [Subgroup.relIndex_mul_relIndex (J ⊓ U) (pCoreOf 2 L ⊓ U) U hJO inf_le_right, hJU]
  have hOne : (pCoreOf 2 L ⊓ U).relIndex U ≠ 1 := by
    intro h1
    rw [Subgroup.relIndex_eq_one] at h1
    exact hUnleO (h1.trans inf_le_left)
  have hb : (pCoreOf 2 L ⊓ U).relIndex U = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp
      ⟨(J ⊓ U).relIndex (pCoreOf 2 L ⊓ U), by rw [mul_comm]; exact hprod.symm⟩ with h1 | h2
    · exact absurd h1 hOne
    · exact h2
  have ha : (J ⊓ U).relIndex (pCoreOf 2 L ⊓ U) = 1 := by
    rw [hb] at hprod
    omega
  have hle : pCoreOf 2 L ⊓ U ≤ J ⊓ U := by
    rw [← Subgroup.relIndex_eq_one (H := J ⊓ U) (K := pCoreOf 2 L ⊓ U)]
    exact ha
  rw [inf_comm U (pCoreOf 2 L), inf_comm U J]
  exact le_antisymm hle hJO

private theorem seven_eight_core_sym_perm_sq_mul_sq :
    ∀ s t : Equiv.Perm (Fin 3), s * s = 1 → t * t = 1 → (s * t) * (s * t) = 1 →
      s = 1 ∨ t = 1 ∨ s = t := by
  decide

private theorem seven_eight_core_sym_perm_mul_pow_three :
    ∀ s t : Equiv.Perm (Fin 3), s * s = 1 → t * t = 1 → s ≠ 1 → t ≠ 1 → s ≠ t →
      (s * t) ^ 3 = 1 ∧ (s * t) ≠ 1 ∧ (s * t) * (s * t) ≠ 1 := by
  decide

private theorem seven_eight_core_sym_perm_exists_not :
    ∀ t : Equiv.Perm (Fin 3), ∃ s : Equiv.Perm (Fin 3), s ≠ 1 ∧ s ≠ t := by
  decide

private theorem seven_eight_core_sym_perm_sq_or_eq {s t : Equiv.Perm (Fin 3)}
    (hs : s * s = 1) (ht : t * t = 1) (hst : (s * t) * (s * t) = 1) (ht1 : t ≠ 1) :
    s = 1 ∨ s = t := by
  rcases seven_eight_core_sym_perm_sq_mul_sq s t hs ht hst with h | h | h
  · exact Or.inl h
  · exact absurd h ht1
  · exact Or.inr h

private theorem seven_eight_core_sym_perm_sq_mul_sq_of_commute {s t : Equiv.Perm (Fin 3)}
    (hs : s * s = 1) (ht : t * t = 1) (hc : s * t = t * s) :
    (s * t) * (s * t) = 1 := by
  calc (s * t) * (s * t) = s * (t * s) * t := by group
    _ = s * (s * t) * t := by rw [← hc]
    _ = (s * s) * (t * t) := by group
    _ = 1 := by rw [hs, ht, mul_one]

private theorem seven_eight_core_sym_pow_two_odd {n : ℕ} (h : Odd (2 ^ n)) : n = 0 := by
  cases n with
  | zero => rfl
  | succ k =>
    have he : Even (2 ^ (k + 1)) := by
      rw [pow_succ']
      exact even_two_mul (2 ^ k)
    exact absurd he (Nat.not_even_iff_odd.2 h)

theorem Hyp78.commutator_le_of_forall_commutator_mem {V H E J L N : Subgroup G}
    (h : Hyp78 V H E J L) (hV2 : J.relIndex V = 2) (hNK : N ≤ kSub V H E)
    (hNnorm : kSub V H E ≤ Subgroup.normalizer (N : Set G)) {v : G} (hv : v ∈ V) (hvJ : v ∉ J)
    (hvN : ∀ n ∈ N, ⁅v, n⁆ ∈ J) : ⁅L, N⁆ ≤ J := by
  have hKleH : kSub V H E ≤ H := kSub_le_of_forall_le h.omega_le
  have hLleH : L ≤ H := h.le_kSub.trans hKleH
  have hNleH : N ≤ H := hNK.trans hKleH
  have hJleH : J ≤ H := h.pcore_le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hJnormH : H ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_subgroupOf_normal hJleH h.jnormal
  have hVN : ⁅V, N⁆ ≤ J := by
    rw [Subgroup.commutator_le]
    intro w hw n hn
    have hnH : n ∈ H := hNleH hn
    by_cases hwJ : w ∈ J
    · have hconj : n * w⁻¹ * n⁻¹ ∈ J :=
        (Subgroup.mem_normalizer_iff.mp (hJnormH hnH) w⁻¹).mp (J.inv_mem hwJ)
      have hmem : w * (n * w⁻¹ * n⁻¹) ∈ J := J.mul_mem hwJ hconj
      simpa [commutatorElement_def, mul_assoc] using hmem
    · have hmem : (⟨w, hw⟩ : V) * (⟨v, hv⟩ : V)⁻¹ ∈ (J.subgroupOf V) := by
        rw [Subgroup.mul_mem_iff_of_index_two (H := J.subgroupOf V) hV2]
        constructor
        · intro hw'
          exact absurd (Subgroup.mem_subgroupOf.mp hw') hwJ
        · intro hv'
          exact absurd (by simpa using J.inv_mem (Subgroup.mem_subgroupOf.mp hv')) hvJ
      have hwv : w * v⁻¹ ∈ J := by
        simpa using Subgroup.mem_subgroupOf.mp hmem
      have hjn : ⁅w * v⁻¹, n⁆ ∈ J := by
        have hconj : n * (w * v⁻¹)⁻¹ * n⁻¹ ∈ J :=
          (Subgroup.mem_normalizer_iff.mp (hJnormH hnH) (w * v⁻¹)⁻¹).mp (J.inv_mem hwv)
        have hmem' : (w * v⁻¹) * (n * (w * v⁻¹)⁻¹ * n⁻¹) ∈ J := J.mul_mem hwv hconj
        simpa [commutatorElement_def, mul_assoc] using hmem'
      have hconj2 : (w * v⁻¹) * ⁅v, n⁆ * (w * v⁻¹)⁻¹ ∈ J :=
        (Subgroup.mem_normalizer_iff.mp (hJnormH (hJleH hwv)) ⁅v, n⁆).mp (hvN n hn)
      have hid := commutatorElement_mul_left_eq_conj_mul (w * v⁻¹) v n
      rw [show (w * v⁻¹) * v = w by group] at hid
      rw [hid]
      exact J.mul_mem hconj2 hjn
  have hUN : ∀ U ∈ omegaWithin V H E L, ⁅U, N⁆ ≤ J := by
    intro U hU
    obtain ⟨k, hkK, hUk⟩ := h.transitive U hU.1
    rw [hUk, Subgroup.commutator_le]
    intro u hu n hn
    have hkH : k ∈ H := hKleH hkK
    have hku : k * u * k⁻¹ ∈ V := (mem_conjSubgroup_iff.mp hu)
    have hkn : k * n * k⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hNnorm hkK) n).mp hn
    have hJ : ⁅k * u * k⁻¹, k * n * k⁻¹⁆ ∈ J :=
      (Subgroup.commutator_le.mp hVN) (k * u * k⁻¹) hku (k * n * k⁻¹) hkn
    have hmem : k⁻¹ * ⁅k * u * k⁻¹, k * n * k⁻¹⁆ * k ∈ J :=
      by simpa using (Subgroup.mem_normalizer_iff.mp (hJnormH (H.inv_mem hkH)) _).mp hJ
    have hid : k⁻¹ * ⁅k * u * k⁻¹, k * n * k⁻¹⁆ * k = ⁅u, n⁆ := by
      have := conjugate_commutatorElement (k * u * k⁻¹) (k * n * k⁻¹) k⁻¹
      simpa [mul_assoc] using this
    rw [← hid]
    exact hmem
  refine Subgroup.commutator_le.mpr fun l hl n hn => ?_
  have hgen : (⨆ U : {U : Subgroup G // U ∈ omegaWithin V H E L}, (U : Subgroup G)) = L := by
    rw [show (⨆ U : {U : Subgroup G // U ∈ omegaWithin V H E L}, (U : Subgroup G))
        = (⨆ (U : Subgroup G) (_ : U ∈ omegaWithin V H E L), U) from
      iSup_subtype'' (omegaWithin V H E L) (fun U : Subgroup G => U)]
    exact h.generated
  have hmem : ∀ (i : {U : Subgroup G // U ∈ omegaWithin V H E L}), ∀ x ∈ (i : Subgroup G),
      x ∈ L ∧ ∀ n ∈ N, ⁅x, n⁆ ∈ J := by
    intro i x hx
    exact ⟨i.2.2 hx, fun n hn => (Subgroup.commutator_le.mp (hUN i.1 i.2)) x hx n hn⟩
  have hone : (1 : G) ∈ L ∧ ∀ n ∈ N, ⁅(1 : G), n⁆ ∈ J :=
    ⟨L.one_mem, fun n _ => by simp⟩
  have hmul : ∀ x y : G, (x ∈ L ∧ ∀ n ∈ N, ⁅x, n⁆ ∈ J) →
      (y ∈ L ∧ ∀ n ∈ N, ⁅y, n⁆ ∈ J) →
      (x * y ∈ L ∧ ∀ n ∈ N, ⁅x * y, n⁆ ∈ J) := by
    rintro x y ⟨hxL, hxC⟩ ⟨hyL, hyC⟩
    refine ⟨L.mul_mem hxL hyL, fun n hn => ?_⟩
    have hxH : x ∈ H := hLleH hxL
    have hxn : x * ⁅y, n⁆ * x⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (hJnormH hxH) ⁅y, n⁆).mp (hyC n hn)
    rw [commutatorElement_mul_left_eq_conj_mul]
    exact J.mul_mem hxn (hxC n hn)
  have hCl : l ∈ L ∧ ∀ n ∈ N, ⁅l, n⁆ ∈ J :=
    Subgroup.iSup_induction
      (fun i : {U : Subgroup G // U ∈ omegaWithin V H E L} => (i : Subgroup G))
      (C := fun x => x ∈ L ∧ ∀ n ∈ N, ⁅x, n⁆ ∈ J)
      (by rw [hgen]; exact hl) hmem hone hmul
  exact hCl.2 n hn

theorem Hyp78.not_le_pCoreOf {V H E J L : Subgroup G} (h : Hyp78 V H E J L) :
    ¬ V ≤ pCoreOf 2 L := by
  intro hVleO
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  have hKleH : kSub V H E ≤ H := kSub_le_of_forall_le h.omega_le
  have hLleH : L ≤ H := h.le_kSub.trans hKleH
  have hO2 : IsPGroup 2 (pCoreOf 2 L) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) L
  have hLnormO : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hUV : ∀ U ∈ omegaWithin V H E L, ∀ u ∈ U, ∀ v ∈ V, u * v = v * u := by
    intro U hU u hu v hv
    have hUΩ : U ∈ omegaSet V H E := hU.1
    have hU2 : IsPGroup 2 U :=
      isPGroup_two_of_isElemAbelian (isElemAbelian_of_mem_omegaSet h.elemAbelian hUΩ)
    have hOsupU : IsPGroup 2 ↥(pCoreOf 2 L ⊔ U) :=
      IsPGroup.to_sup_of_normal_left' hO2 hU2 (hU.2.trans hLnormO)
    have hsup : U ⊔ V ≤ pCoreOf 2 L ⊔ U :=
      sup_le le_sup_right (hVleO.trans le_sup_left)
    have hP : IsPGroup 2 ↥(U ⊔ V) := hOsupU.to_le hsup
    obtain ⟨a, b, hUa, hVb, hNab⟩ :=
      nVSub_conj_ne_bot_of_mem_omegaSet h.ti h.abelian hUΩ h.mem
    have hN : U ⊓ Subgroup.normalizer (V : Set G) ≠ ⊥ := by
      have hn := congrArg (fun X : Subgroup G => Subgroup.normalizer (X : Set G)) hVb
      rw [hUa, hn]
      exact hNab
    exact commute_of_isPGroup_sup h.elemAbelian h.ti ⟨a, hUa⟩ ⟨b, hVb⟩ hN hP u hu v hv
  have hLcent : L ≤ Subgroup.centralizer (V : Set G) := by
    have hgen : (⨆ U ∈ omegaWithin V H E L, U) = L := h.generated
    rw [← hgen]
    refine iSup_le fun U => iSup_le fun hU => ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (hUV U hU x hx v hv).symm
  have hcen_norm : Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (V : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx k hk
    have hxk : k * x = x * k := (Subgroup.mem_centralizer_iff.mp hx) k hk
    rw [← hxk, mul_assoc, mul_inv_cancel, mul_one]
    exact hk
  have hfix : ∀ g ∈ pCoreOf 2 L, conjSubgroup V g = V := by
    intro g hg
    rw [conjSubgroup_eq_iff_mem_normalizer]
    exact hcen_norm (hLcent (CFSG.LieType.BorelTits.pCoreOf_le 2 L hg))
  have hset : {W : Subgroup G | ∃ g ∈ pCoreOf 2 L, W = conjSubgroup V g ⊔ J} = {V ⊔ J} := by
    ext W
    constructor
    · rintro ⟨g, hg, rfl⟩
      rw [hfix g hg]
      exact Set.mem_singleton _
    · intro hW
      rw [Set.mem_singleton_iff] at hW
      exact ⟨1, (pCoreOf 2 L).one_mem, by rw [hW, Quasithin.conjSubgroup_one]⟩
  have h4 := h.four_le
  rw [hset, Set.ncard_singleton] at h4
  omega

private theorem seven_eight_core_sym_exists_pi {V H E J L : Subgroup G}
    (h : Hyp78 V H E J L) :
    ∃ π : ↥L →* Equiv.Perm (Fin 3), Function.Surjective π ∧
      ∀ k : ↥L, π k = 1 ↔ (k : G) ∈ pCoreOf 2 L := by
  obtain ⟨X, _, φ, hsurj, hker, ⟨e⟩⟩ := h.quot
  refine ⟨e.toMonoidHom.comp φ, e.surjective.comp hsurj, fun k => ?_⟩
  have := hker k
  simpa [MonoidHom.comp_apply, MulEquiv.map_eq_one_iff] using this

private noncomputable def seven_eight_core_sym_piOf {V H E J L : Subgroup G}
    (h : Hyp78 V H E J L) : ↥L →* Equiv.Perm (Fin 3) :=
  Classical.choose (seven_eight_core_sym_exists_pi h)

private theorem seven_eight_core_sym_piOf_surjective {V H E J L : Subgroup G}
    (h : Hyp78 V H E J L) : Function.Surjective (seven_eight_core_sym_piOf h) :=
  (Classical.choose_spec (seven_eight_core_sym_exists_pi h)).1

private theorem seven_eight_core_sym_piOf_ker {V H E J L : Subgroup G}
    (h : Hyp78 V H E J L) (k : ↥L) :
    seven_eight_core_sym_piOf h k = 1 ↔ (k : G) ∈ pCoreOf 2 L :=
  (Classical.choose_spec (seven_eight_core_sym_exists_pi h)).2 k

private noncomputable def seven_eight_core_sym_v0Of {V H E J L : Subgroup G}
    (h : Hyp78 V H E J L) : G :=
  Classical.choose (SetLike.not_le_iff_exists.mp h.not_le_pCoreOf)

private theorem seven_eight_core_sym_v0Of_mem_V {V H E J L : Subgroup G}
    (h : Hyp78 V H E J L) : seven_eight_core_sym_v0Of h ∈ V :=
  (Classical.choose_spec (SetLike.not_le_iff_exists.mp h.not_le_pCoreOf)).1

private theorem seven_eight_core_sym_v0Of_not_mem {V H E J L : Subgroup G}
    (h : Hyp78 V H E J L) : seven_eight_core_sym_v0Of h ∉ pCoreOf 2 L :=
  (Classical.choose_spec (SetLike.not_le_iff_exists.mp h.not_le_pCoreOf)).2

private noncomputable def seven_eight_core_sym_t0Of {V H E J L : Subgroup G}
    (h : Hyp78 V H E J L) : Equiv.Perm (Fin 3) :=
  seven_eight_core_sym_piOf h
    ⟨seven_eight_core_sym_v0Of h, h.left_le (seven_eight_core_sym_v0Of_mem_V h)⟩

private theorem seven_eight_core_sym_t0Of_sq {V H E J L : Subgroup G}
    (h : Hyp78 V H E J L) :
    seven_eight_core_sym_t0Of h * seven_eight_core_sym_t0Of h = 1 := by
  have hv : seven_eight_core_sym_v0Of h * seven_eight_core_sym_v0Of h = 1 :=
    elemAbelian_mul_self h.elemAbelian (seven_eight_core_sym_v0Of_mem_V h)
  have hsq : (⟨seven_eight_core_sym_v0Of h,
        h.left_le (seven_eight_core_sym_v0Of_mem_V h)⟩ : ↥L) *
      ⟨seven_eight_core_sym_v0Of h, h.left_le (seven_eight_core_sym_v0Of_mem_V h)⟩ = 1 :=
    Subtype.ext hv
  have h1 := congrArg (seven_eight_core_sym_piOf h) hsq
  rw [map_mul, map_one] at h1
  simpa [seven_eight_core_sym_t0Of] using h1

private theorem seven_eight_core_sym_t0Of_ne_one {V H E J L : Subgroup G}
    (h : Hyp78 V H E J L) : seven_eight_core_sym_t0Of h ≠ 1 := by
  intro h1
  exact seven_eight_core_sym_v0Of_not_mem h
    ((seven_eight_core_sym_piOf_ker h ⟨seven_eight_core_sym_v0Of h,
      h.left_le (seven_eight_core_sym_v0Of_mem_V h)⟩).mp (by
        simpa [seven_eight_core_sym_t0Of] using h1))

private theorem seven_eight_core_sym_pi_eq_one_or_t0_of_comm {V H E J L : Subgroup G}
    (h : Hyp78 V H E J L) {a : G} (haL : a ∈ L) (ha_sq : a * a = 1)
    (hcomm : seven_eight_core_sym_v0Of h * a = a * seven_eight_core_sym_v0Of h) :
    seven_eight_core_sym_piOf h ⟨a, haL⟩ = 1 ∨
      seven_eight_core_sym_piOf h ⟨a, haL⟩ = seven_eight_core_sym_t0Of h := by
  have hv0L : seven_eight_core_sym_v0Of h ∈ L :=
    h.left_le (seven_eight_core_sym_v0Of_mem_V h)
  have hpermcomm : seven_eight_core_sym_piOf h ⟨a, haL⟩ * seven_eight_core_sym_t0Of h =
      seven_eight_core_sym_t0Of h * seven_eight_core_sym_piOf h ⟨a, haL⟩ := by
    have heq : (⟨a, haL⟩ * ⟨seven_eight_core_sym_v0Of h, hv0L⟩ : ↥L) =
        ⟨seven_eight_core_sym_v0Of h, hv0L⟩ * ⟨a, haL⟩ := Subtype.ext hcomm.symm
    have h1 := congrArg (seven_eight_core_sym_piOf h) heq
    rw [map_mul, map_mul] at h1
    simpa [seven_eight_core_sym_t0Of] using h1
  have ha_sq' : seven_eight_core_sym_piOf h ⟨a, haL⟩ *
      seven_eight_core_sym_piOf h ⟨a, haL⟩ = 1 := by
    have hsq : (⟨a, haL⟩ : ↥L) * ⟨a, haL⟩ = 1 := Subtype.ext ha_sq
    have h1 := congrArg (seven_eight_core_sym_piOf h) hsq
    rw [map_mul, map_one] at h1
    simpa using h1
  have hst := seven_eight_core_sym_perm_sq_mul_sq_of_commute ha_sq'
    (seven_eight_core_sym_t0Of_sq h) hpermcomm
  exact seven_eight_core_sym_perm_sq_or_eq ha_sq' (seven_eight_core_sym_t0Of_sq h) hst
    (seven_eight_core_sym_t0Of_ne_one h)

private theorem seven_eight_core_sym_pi_conj_eq_one_or_t0 {V H E J L : Subgroup G}
    (h : Hyp78 V H E J L) {x w : G} (hx : x ∈ pCoreOf 2 L)
    (hw : w ∈ conjSubgroup V x) (hwL : w ∈ L) :
    seven_eight_core_sym_piOf h ⟨w, hwL⟩ = 1 ∨
      seven_eight_core_sym_piOf h ⟨w, hwL⟩ = seven_eight_core_sym_t0Of h := by
  have hKleH : kSub V H E ≤ H := kSub_le_of_forall_le h.omega_le
  have hLleH : L ≤ H := h.le_kSub.trans hKleH
  have hxL : x ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L hx
  have hxΩ : conjSubgroup V x ∈ omegaSet V H E :=
    conjSubgroup_mem_omegaSet h.le h.normal h.mem (hLleH hxL)
  have hw_sq : w * w = 1 :=
    elemAbelian_mul_self (isElemAbelian_of_mem_omegaSet h.elemAbelian hxΩ) hw
  have hcommut : ⁅conjSubgroup V x, V⁆ = ⊥ := by
    have := seven_eight_commutator_conj_eq_bot h hx (one_mem (pCoreOf 2 L))
    simpa [Quasithin.conjSubgroup_one] using this
  have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommut
  have hcomm : seven_eight_core_sym_v0Of h * w = w * seven_eight_core_sym_v0Of h :=
    (Subgroup.mem_centralizer_iff.mp (hcent hw)) (seven_eight_core_sym_v0Of h)
      (seven_eight_core_sym_v0Of_mem_V h)
  exact seven_eight_core_sym_pi_eq_one_or_t0_of_comm h hwL hw_sq hcomm

private theorem seven_eight_core_sym_pi_ne_one_of_not_mem_J {V H E J L : Subgroup G}
    (h : Hyp78 V H E J L) (hV2 : J.relIndex V = 2) {U : Subgroup G}
    (hU : U ∈ omegaSet V H E) (hUleL : U ≤ L) (hUnleO : ¬ U ≤ pCoreOf 2 L)
    {u : G} (hu : u ∈ U) (huL : u ∈ L) (huJ : u ∉ J) :
    seven_eight_core_sym_piOf h ⟨u, huL⟩ ≠ 1 := by
  intro h1
  have huO : u ∈ pCoreOf 2 L := (seven_eight_core_sym_piOf_ker h ⟨u, huL⟩).mp h1
  have heq := seven_eight_core_sym_inf_pCoreOf_eq_inf_J h hV2 hU hUleL hUnleO
  have hmem : u ∈ U ⊓ pCoreOf 2 L := Subgroup.mem_inf.mpr ⟨hu, huO⟩
  rw [heq] at hmem
  exact huJ (Subgroup.mem_inf.mp hmem).2

private theorem seven_eight_core_sym_conj_not_le_pCoreOf {V H E J L : Subgroup G}
    (h : Hyp78 V H E J L) {x : G} (hx : x ∈ pCoreOf 2 L) :
    ¬ conjSubgroup V x ≤ pCoreOf 2 L := by
  intro hle
  have hxL : x ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L hx
  have hLnormO : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  apply h.not_le_pCoreOf
  intro v hv
  have hux : x⁻¹ * v * x ∈ conjSubgroup V x := by
    rw [mem_conjSubgroup_iff]
    convert hv using 1
    group
  have hO : x⁻¹ * v * x ∈ pCoreOf 2 L := hle hux
  have hmem : x * (x⁻¹ * v * x) * x⁻¹ ∈ pCoreOf 2 L :=
    (Subgroup.mem_normalizer_iff.mp (hLnormO hxL) _).mp hO
  rwa [show x * (x⁻¹ * v * x) * x⁻¹ = v by group] at hmem

private theorem seven_eight_core_sym_mem_sup_zpowers_of_pi {V H E J L : Subgroup G}
    (h : Hyp78 V H E J L) {a : G} (haL : a ∈ L)
    (h1 : seven_eight_core_sym_piOf h ⟨a, haL⟩ = 1 ∨
      seven_eight_core_sym_piOf h ⟨a, haL⟩ = seven_eight_core_sym_t0Of h) :
    a ∈ pCoreOf 2 L ⊔ Subgroup.zpowers (seven_eight_core_sym_v0Of h) := by
  have hv0L : seven_eight_core_sym_v0Of h ∈ L :=
    h.left_le (seven_eight_core_sym_v0Of_mem_V h)
  rcases h1 with h1 | h1
  · exact Subgroup.mem_sup_left ((seven_eight_core_sym_piOf_ker h ⟨a, haL⟩).mp h1)
  · have hk : seven_eight_core_sym_piOf h
        (⟨a, haL⟩ * ⟨seven_eight_core_sym_v0Of h, hv0L⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, h1]
      change seven_eight_core_sym_t0Of h * (seven_eight_core_sym_t0Of h)⁻¹ = 1
      exact mul_inv_cancel _
    have hmem : a * (seven_eight_core_sym_v0Of h)⁻¹ ∈ pCoreOf 2 L := by
      simpa using (seven_eight_core_sym_piOf_ker h _).mp hk
    have h2 : (a * (seven_eight_core_sym_v0Of h)⁻¹) * seven_eight_core_sym_v0Of h ∈
        pCoreOf 2 L ⊔ Subgroup.zpowers (seven_eight_core_sym_v0Of h) :=
      Subgroup.mul_mem_sup hmem (Subgroup.mem_zpowers _)
    rwa [show a * (seven_eight_core_sym_v0Of h)⁻¹ * seven_eight_core_sym_v0Of h = a by
      group] at h2

private theorem seven_eight_core_sym_not_isPGroup_closure {V H E J L : Subgroup G}
    (h : Hyp78 V H E J L) {w u : G} (hwL : w ∈ L) (huL : u ∈ L)
    {t : Equiv.Perm (Fin 3)}
    (hpi : seven_eight_core_sym_piOf h (⟨w, hwL⟩ * ⟨u, huL⟩) =
      seven_eight_core_sym_t0Of h * t)
    (horder : orderOf (seven_eight_core_sym_t0Of h * t) = 3) :
    ¬ IsPGroup 2 (Subgroup.closure ({w, u} : Set G)) := by
  intro hP
  have hclL : Subgroup.closure ({w, u} : Set G) ≤ L := by
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | rfl
    · exact hwL
    · exact huL
  let ψ : ↥(Subgroup.closure ({w, u} : Set G)) →* Equiv.Perm (Fin 3) :=
    (seven_eight_core_sym_piOf h).comp (Subgroup.inclusion hclL)
  have hwu : w * u ∈ Subgroup.closure ({w, u} : Set G) :=
    Subgroup.mul_mem _
      (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  have hψ : ψ ⟨w * u, hwu⟩ = seven_eight_core_sym_t0Of h * t := by
    show seven_eight_core_sym_piOf h (Subgroup.inclusion hclL ⟨w * u, hwu⟩) = _
    have heq : Subgroup.inclusion hclL ⟨w * u, hwu⟩ = (⟨w, hwL⟩ * ⟨u, huL⟩ : ↥L) := by
      apply Subtype.ext
      rw [Subgroup.coe_inclusion]
      rfl
    rw [heq]
    exact hpi
  obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hP ⟨w * u, hwu⟩
  have hdvd : orderOf (ψ ⟨w * u, hwu⟩) ∣ 2 ^ n := by
    rw [← hn]
    exact orderOf_map_dvd ψ ⟨w * u, hwu⟩
  rw [hψ, horder] at hdvd
  exact absurd (Nat.prime_three.dvd_of_dvd_pow hdvd) (by norm_num)

private theorem seven_eight_core_sym_pow_three_of_case_B {V H E J L : Subgroup G}
    (h : Hyp78 V H E J L) (hV2 : J.relIndex V = 2) {U : Subgroup G}
    (hU : U ∈ omegaWithin V H E L) (hUnleO : ¬ U ≤ pCoreOf 2 L)
    {u₁ : G} (hu₁ : u₁ ∈ U) (hu₁ne1 : seven_eight_core_sym_piOf h ⟨u₁, hU.2 hu₁⟩ ≠ 1)
    (hu₁net0 : seven_eight_core_sym_piOf h ⟨u₁, hU.2 hu₁⟩ ≠ seven_eight_core_sym_t0Of h)
    {x : G} (hx : x ∈ pCoreOf 2 L) {u w : G} (hu : u ∈ U) (huJ : u ∉ J)
    (hw : w ∈ conjSubgroup V x) (hwJ : w ∉ J) :
    (w * u) ^ 3 = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  have hUΩ : U ∈ omegaSet V H E := hU.1
  have hUleL : U ≤ L := hU.2
  have hKleH : kSub V H E ≤ H := kSub_le_of_forall_le h.omega_le
  have hLleH : L ≤ H := h.le_kSub.trans hKleH
  have hxL : x ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L hx
  have hxΩ : conjSubgroup V x ∈ omegaSet V H E :=
    conjSubgroup_mem_omegaSet h.le h.normal h.mem (hLleH hxL)
  have hxLle : conjSubgroup V x ≤ L := by
    intro y hy
    rw [mem_conjSubgroup_iff] at hy
    have hmem : x⁻¹ * (x * y * x⁻¹) * x ∈ L :=
      L.mul_mem (L.mul_mem (L.inv_mem hxL) (h.left_le hy)) hxL
    rwa [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at hmem
  have hxNleO : ¬ conjSubgroup V x ≤ pCoreOf 2 L :=
    seven_eight_core_sym_conj_not_le_pCoreOf h hx
  have huL : u ∈ L := hUleL hu
  have hu₁L : u₁ ∈ L := hUleL hu₁
  have hwL : w ∈ L := hxLle hw
  let t : Equiv.Perm (Fin 3) := seven_eight_core_sym_piOf h ⟨u₁, hu₁L⟩
  have ht1 : t ≠ 1 := hu₁ne1
  have htt0 : t ≠ seven_eight_core_sym_t0Of h := hu₁net0
  have ht_sq : t * t = 1 := by
    have hsq : (⟨u₁, hu₁L⟩ : ↥L) * ⟨u₁, hu₁L⟩ = 1 := by
      apply Subtype.ext
      exact elemAbelian_mul_self (isElemAbelian_of_mem_omegaSet h.elemAbelian hUΩ) hu₁
    have h1 := congrArg (seven_eight_core_sym_piOf h) hsq
    rw [map_mul, map_one] at h1
    simpa [t] using h1
  have hwp : seven_eight_core_sym_piOf h ⟨w, hwL⟩ = seven_eight_core_sym_t0Of h := by
    rcases seven_eight_core_sym_pi_conj_eq_one_or_t0 h hx hw hwL with h1 | h1
    · exact absurd h1 (seven_eight_core_sym_pi_ne_one_of_not_mem_J h hV2 hxΩ hxLle hxNleO
        hw hwL hwJ)
    · exact h1
  have hup : seven_eight_core_sym_piOf h ⟨u, huL⟩ = t := by
    have hu_sq : u * u = 1 :=
      elemAbelian_mul_self (isElemAbelian_of_mem_omegaSet h.elemAbelian hUΩ) hu
    have hcomm : u * u₁ = u₁ * u :=
      congrArg Subtype.val
        ((isElemAbelian_of_mem_omegaSet h.elemAbelian hUΩ).1.is_comm.comm
          ⟨u, hu⟩ ⟨u₁, hu₁⟩)
    have hpermcomm : seven_eight_core_sym_piOf h ⟨u, huL⟩ * t =
        t * seven_eight_core_sym_piOf h ⟨u, huL⟩ := by
      have heq : (⟨u, huL⟩ * ⟨u₁, hu₁L⟩ : ↥L) = ⟨u₁, hu₁L⟩ * ⟨u, huL⟩ :=
        Subtype.ext hcomm
      have h1 := congrArg (seven_eight_core_sym_piOf h) heq
      rw [map_mul, map_mul] at h1
      simpa [t] using h1
    have hu_sq' : seven_eight_core_sym_piOf h ⟨u, huL⟩ *
        seven_eight_core_sym_piOf h ⟨u, huL⟩ = 1 := by
      have hsq : (⟨u, huL⟩ : ↥L) * ⟨u, huL⟩ = 1 := Subtype.ext hu_sq
      have h1 := congrArg (seven_eight_core_sym_piOf h) hsq
      rw [map_mul, map_one] at h1
      simpa using h1
    have hst := seven_eight_core_sym_perm_sq_mul_sq_of_commute hu_sq' ht_sq hpermcomm
    rcases seven_eight_core_sym_perm_sq_mul_sq (seven_eight_core_sym_piOf h ⟨u, huL⟩) t
        hu_sq' ht_sq hst with h1 | h1 | h1
    · exact absurd h1
        (seven_eight_core_sym_pi_ne_one_of_not_mem_J h hV2 hUΩ hUleL hUnleO hu huL huJ)
    · exact absurd h1 ht1
    · exact h1
  have hwup : seven_eight_core_sym_piOf h (⟨w, hwL⟩ * ⟨u, huL⟩) =
      seven_eight_core_sym_t0Of h * t := by
    rw [map_mul, hwp, hup]
  have ht0t := seven_eight_core_sym_perm_mul_pow_three (seven_eight_core_sym_t0Of h) t
    (seven_eight_core_sym_t0Of_sq h) ht_sq (seven_eight_core_sym_t0Of_ne_one h) ht1 htt0.symm
  have horder : orderOf (seven_eight_core_sym_t0Of h * t) = 3 := by
    have hdvd : orderOf (seven_eight_core_sym_t0Of h * t) ∣ 3 :=
      orderOf_dvd_iff_pow_eq_one.mpr ht0t.1
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) ht0t.2.1
    · exact h3
  have hnot : ¬ IsPGroup 2 (Subgroup.closure ({w, u} : Set G)) :=
    seven_eight_core_sym_not_isPGroup_closure h hwL huL hwup horder
  have hOdd : Odd (orderOf (w * u)) :=
    seven_three_A h.elemAbelian h.ti h.abelian hxΩ hUΩ hw hu hnot
  let g : ↥L := ⟨w, hwL⟩ * ⟨u, huL⟩
  have hg : (g : G) = w * u := rfl
  have hgpow : (g : G) ^ 3 ∈ pCoreOf 2 L := by
    have hpi : seven_eight_core_sym_piOf h (g ^ 3) = 1 := by
      rw [map_pow]
      have hgval : seven_eight_core_sym_piOf h g = seven_eight_core_sym_t0Of h * t := by
        show seven_eight_core_sym_piOf h (⟨w, hwL⟩ * ⟨u, huL⟩) = _
        exact hwup
      rw [hgval, ht0t.1]
    simpa using (seven_eight_core_sym_piOf_ker h (g ^ 3)).mp hpi
  have hwu3O : (w * u) ^ 3 ∈ pCoreOf 2 L := by
    simpa [hg] using hgpow
  have hpowOdd : Odd (orderOf ((w * u) ^ 3)) := hOdd.of_dvd_nat (orderOf_pow_dvd 3)
  obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) L) ⟨(w * u) ^ 3, hwu3O⟩
  have horder3 : orderOf ((w * u) ^ 3) = 2 ^ n :=
    (Subgroup.orderOf_coe (⟨(w * u) ^ 3, hwu3O⟩ : ↥(pCoreOf 2 L))).trans hn
  have hn0 : n = 0 := seven_eight_core_sym_pow_two_odd (horder3 ▸ hpowOdd)
  rw [hn0, pow_zero] at horder3
  exact orderOf_eq_one_iff.mp horder3

theorem Hyp78.forall_commute_or_forall_pow_three {V H E J L : Subgroup G}
    (h : Hyp78 V H E J L) (hV2 : J.relIndex V = 2) {U : Subgroup G}
    (hU : U ∈ omegaWithin V H E L) :
    (∀ x ∈ pCoreOf 2 L, ∀ u ∈ U, ∀ w ∈ conjSubgroup V x, u * w = w * u) ∨
      (∀ x ∈ pCoreOf 2 L, ∀ u ∈ U, u ∉ J → ∀ w ∈ conjSubgroup V x, w ∉ J →
        (w * u) ^ 3 = 1) := by
  classical
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  have hLnormO : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hO2 : IsPGroup 2 (pCoreOf 2 L) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) L
  have hv0V : seven_eight_core_sym_v0Of h ∈ V := seven_eight_core_sym_v0Of_mem_V h
  have hv0L : seven_eight_core_sym_v0Of h ∈ L := h.left_le hv0V
  have hv0sq : seven_eight_core_sym_v0Of h * seven_eight_core_sym_v0Of h = 1 :=
    elemAbelian_mul_self h.elemAbelian hv0V
  have hzv2 : IsPGroup 2 (Subgroup.zpowers (seven_eight_core_sym_v0Of h)) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using hv0sq)
  have hzvnorm : Subgroup.zpowers (seven_eight_core_sym_v0Of h) ≤
      Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    (Subgroup.zpowers_le.mpr hv0L).trans hLnormO
  have hOsupv2 : IsPGroup 2
      ↥(pCoreOf 2 L ⊔ Subgroup.zpowers (seven_eight_core_sym_v0Of h)) :=
    IsPGroup.to_sup_of_normal_left' hO2 hzv2 hzvnorm
  by_cases hA : ∀ (u : G) (hu : u ∈ U),
      seven_eight_core_sym_piOf h ⟨u, hU.2 hu⟩ = 1 ∨
        seven_eight_core_sym_piOf h ⟨u, hU.2 hu⟩ = seven_eight_core_sym_t0Of h
  · left
    intro x hx u hu w hw
    have hKleH : kSub V H E ≤ H := kSub_le_of_forall_le h.omega_le
    have hLleH : L ≤ H := h.le_kSub.trans hKleH
    have hxL : x ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L hx
    have hxΩ : conjSubgroup V x ∈ omegaSet V H E :=
      conjSubgroup_mem_omegaSet h.le h.normal h.mem (hLleH hxL)
    have hxLle : conjSubgroup V x ≤ L := by
      intro y hy
      rw [mem_conjSubgroup_iff] at hy
      have hmem : x⁻¹ * (x * y * x⁻¹) * x ∈ L :=
        L.mul_mem (L.mul_mem (L.inv_mem hxL) (h.left_le hy)) hxL
      rwa [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at hmem
    have hle : U ⊔ conjSubgroup V x ≤
        pCoreOf 2 L ⊔ Subgroup.zpowers (seven_eight_core_sym_v0Of h) :=
      sup_le
        (fun a ha => seven_eight_core_sym_mem_sup_zpowers_of_pi h (hU.2 ha) (hA a ha))
        (fun y hy => seven_eight_core_sym_mem_sup_zpowers_of_pi h (hxLle hy)
          (seven_eight_core_sym_pi_conj_eq_one_or_t0 h hx hy (hxLle hy)))
    have hP : IsPGroup 2 ↥(U ⊔ conjSubgroup V x) := hOsupv2.to_le hle
    obtain ⟨a, b, hUa, hWb, hNab⟩ :=
      nVSub_conj_ne_bot_of_mem_omegaSet h.ti h.abelian hU.1 hxΩ
    have hN : U ⊓ Subgroup.normalizer (conjSubgroup V x : Set G) ≠ ⊥ := by
      rw [hUa, hWb]
      exact hNab
    exact commute_of_isPGroup_sup h.elemAbelian h.ti ⟨a, hUa⟩ ⟨b, hWb⟩ hN hP u hu w hw
  · right
    push Not at hA
    obtain ⟨u₁, hu₁, hu₁ne1, hu₁net0⟩ := hA
    have hu₁L : u₁ ∈ L := hU.2 hu₁
    have hUnleO : ¬ U ≤ pCoreOf 2 L := fun hUO =>
      hu₁ne1 ((seven_eight_core_sym_piOf_ker h ⟨u₁, hu₁L⟩).mpr (hUO hu₁))
    intro x hx u hu huJ w hw hwJ
    exact seven_eight_core_sym_pow_three_of_case_B h hV2 hU hUnleO hu₁ hu₁ne1 hu₁net0
      hx hu huJ hw hwJ

private theorem seven_eight_core_sym_mem_zpowers_involution {t s : Equiv.Perm (Fin 3)}
    (ht : t * t = 1) (ht1 : t ≠ 1) :
    s ∈ Subgroup.zpowers t ↔ s = 1 ∨ s = t := by
  constructor
  · intro hs
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hs
    have horder : orderOf t = 2 := by
      have hdvd : orderOf t ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using ht)
      rcases Nat.prime_two.eq_one_or_self_of_dvd _ hdvd with h1 | h2
      · exact absurd (orderOf_eq_one_iff.mp h1) ht1
      · exact h2
    have hmod : t ^ (k % (orderOf t : ℤ)) = t ^ k := zpow_mod_orderOf t k
    rw [hk, horder] at hmod
    change t ^ (k % (2 : ℤ)) = s at hmod
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      rw [h0] at hmod
      simpa using hmod.symm
    · right
      rw [h1] at hmod
      simpa using hmod.symm
  · rintro (h1 | h1)
    · rw [h1]
      exact Subgroup.one_mem _
    · rw [h1]
      exact Subgroup.mem_zpowers t

theorem Hyp78.exists_pow_three_eq_one {V H E J L : Subgroup G} (h : Hyp78 V H E J L)
    (hV2 : J.relIndex V = 2) :
    ∃ U ∈ omegaWithin V H E L, ∃ u ∈ U, u ∉ J ∧
      ∀ x ∈ pCoreOf 2 L, ∀ w ∈ conjSubgroup V x, w ∉ J → (w * u) ^ 3 = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  let P : Subgroup ↥L :=
    (Subgroup.zpowers (seven_eight_core_sym_t0Of h)).comap (seven_eight_core_sym_piOf h)
  let L0 : Subgroup G := P.map L.subtype
  have hLnotle : ¬ L ≤ L0 := by
    intro hle
    obtain ⟨s, hs1, hst0⟩ :=
      seven_eight_core_sym_perm_exists_not (seven_eight_core_sym_t0Of h)
    obtain ⟨l, hl⟩ := seven_eight_core_sym_piOf_surjective h s
    have hlL0 : (l : G) ∈ L0 := hle l.2
    rw [Subgroup.mem_map] at hlL0
    obtain ⟨y, hyP, hy⟩ := hlL0
    have hyl : y = l := Subtype.ext hy
    rw [hyl] at hyP
    have hs_mem : s ∈ Subgroup.zpowers (seven_eight_core_sym_t0Of h) := by
      rw [← hl]
      exact Subgroup.mem_comap.mp hyP
    rcases (seven_eight_core_sym_mem_zpowers_involution
      (seven_eight_core_sym_t0Of_sq h) (seven_eight_core_sym_t0Of_ne_one h)).mp hs_mem with
      h1 | h1
    · exact hs1 h1
    · exact hst0 h1
  have hex : ∃ U ∈ omegaWithin V H E L, ¬ U ≤ L0 := by
    by_contra hcon
    push Not at hcon
    exact hLnotle (by rw [← h.generated]; exact iSup_le fun U => iSup_le fun hU => hcon U hU)
  obtain ⟨U, hU, hUnleL0⟩ := hex
  obtain ⟨u, hu, huL0⟩ := SetLike.not_le_iff_exists.mp hUnleL0
  have huL : u ∈ L := hU.2 hu
  have hup : seven_eight_core_sym_piOf h ⟨u, huL⟩ ≠ 1 ∧
      seven_eight_core_sym_piOf h ⟨u, huL⟩ ≠ seven_eight_core_sym_t0Of h := by
    constructor
    · intro h1
      apply huL0
      rw [Subgroup.mem_map]
      refine ⟨⟨u, huL⟩, ?_, rfl⟩
      show seven_eight_core_sym_piOf h ⟨u, huL⟩ ∈
        Subgroup.zpowers (seven_eight_core_sym_t0Of h)
      rw [(seven_eight_core_sym_mem_zpowers_involution
        (seven_eight_core_sym_t0Of_sq h) (seven_eight_core_sym_t0Of_ne_one h))]
      exact Or.inl h1
    · intro h1
      apply huL0
      rw [Subgroup.mem_map]
      refine ⟨⟨u, huL⟩, ?_, rfl⟩
      show seven_eight_core_sym_piOf h ⟨u, huL⟩ ∈
        Subgroup.zpowers (seven_eight_core_sym_t0Of h)
      rw [(seven_eight_core_sym_mem_zpowers_involution
        (seven_eight_core_sym_t0Of_sq h) (seven_eight_core_sym_t0Of_ne_one h))]
      exact Or.inr h1
  have hUnleO : ¬ U ≤ pCoreOf 2 L := fun hUO =>
    hup.1 ((seven_eight_core_sym_piOf_ker h ⟨u, huL⟩).mpr (hUO hu))
  have huJ : u ∉ J := by
    intro huJ
    have hmem : u ∈ U ⊓ pCoreOf 2 L :=
      Subgroup.mem_inf.mpr ⟨hu, seven_eight_inf_J_le_pCoreOf h
        (Subgroup.mem_inf.mpr ⟨huL, huJ⟩)⟩
    exact hup.1 ((seven_eight_core_sym_piOf_ker h ⟨u, huL⟩).mpr
      (Subgroup.mem_inf.mp hmem).2)
  refine ⟨U, hU, u, hu, huJ, fun x hx w hw hwJ => ?_⟩
  exact seven_eight_core_sym_pow_three_of_case_B h hV2 hU hUnleO hu hup.1 hup.2 hx hu huJ
    hw hwJ

end CFSG.LocalAnalysis.WeakClosure81
