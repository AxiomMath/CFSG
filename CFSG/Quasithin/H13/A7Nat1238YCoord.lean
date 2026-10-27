module

public import CFSG.Quasithin.H13.A7Nat1238Ke

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB
open scoped commutatorElement

@[expose] def vecPair (a : Fin 7) : Fin 7 → ZMod 2 := Pi.single 0 1 + Pi.single a 1

@[expose] def pairIdx : Fin 4 → Fin 7 := ![1, 2, 3, 4]

@[expose] def sigP : Fin 4 → Perm (Fin 7) :=
  ![swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2, swap 0 4 * swap 1 2]

@[expose] def tauP : Fin 4 → Perm (Fin 7) :=
  ![swap 2 3 * swap 3 4, swap 1 3 * swap 3 4, swap 1 2 * swap 2 4, swap 1 2 * swap 2 3]

@[expose] def piP : Fin 4 → Perm (Fin 7) :=
  ![1, swap 1 2 * swap 3 4, swap 1 3 * swap 3 2, swap 1 4 * swap 4 2]

@[expose] def witP : Fin 6 → Perm (Fin 7) :=
  ![swap 0 4 * swap 4 3 * swap 3 2 * swap 2 1, swap 0 1 * swap 1 4,
    swap 0 4 * swap 4 1 * swap 1 2 * swap 2 3, swap 0 1 * swap 1 4 * swap 4 3 * swap 3 2,
    swap 1 4 * swap 4 3, swap 2 4 * swap 4 3]

theorem sigP_mem : ∀ a : Fin 4, sign (sigP a) = 1 ∧ sigP a 5 = 5 ∧ sigP a 6 = 6 := by
  decide +kernel

theorem tauP_mem : ∀ a : Fin 4, sign (tauP a) = 1 ∧ tauP a 5 = 5 ∧ tauP a 6 = 6 := by
  decide +kernel

theorem piP_mem : ∀ a : Fin 4, sign (piP a) = 1 ∧ piP a 5 = 5 ∧ piP a 6 = 6 := by
  decide +kernel

theorem witP_mem : ∀ i : Fin 6, sign (witP i) = 1 ∧ witP i 5 = 5 ∧ witP i 6 = 6 := by
  decide +kernel

theorem sigP_pair : ∀ a : Fin 4,
    permAct7 (sigP a) (vecPair (pairIdx a)) = vecPair (pairIdx a) := by
  decide +kernel

theorem tauP_pair : ∀ a : Fin 4,
    permAct7 (tauP a) (vecPair (pairIdx a)) = vecPair (pairIdx a) := by
  decide +kernel

theorem piP_pair : ∀ a : Fin 4, permAct7 (piP a) (vecPair 1) = vecPair (pairIdx a) := by
  decide +kernel

theorem sigP_e05 : ∀ a : Fin 4,
    (Pi.single 0 1 + Pi.single 5 1 : Fin 7 → ZMod 2) +
      permAct7 (sigP a) (Pi.single 0 1 + Pi.single 5 1) = vecPair (pairIdx a) := by
  decide +kernel

theorem e05_mem : (Pi.single 0 1 + Pi.single 5 1 : Fin 7 → ZMod 2) ∈ evenWeight 7 := by
  rw [mem_evenWeight]
  decide

theorem fixed_pair' : ∀ a : Fin 4, ∀ v : Fin 7 → ZMod 2, (∑ i, v i = 0 ∧ v 5 = 0 ∧ v 6 = 0 ∧
    permAct7 (sigP a) v = v ∧ permAct7 (tauP a) v = v) → v = 0 ∨ v = vecPair (pairIdx a) := by
  decide +kernel

theorem fixed_pair (a : Fin 4) (v : Fin 7 → ZMod 2) (h0 : ∑ i, v i = 0) (h5 : v 5 = 0)
    (h6 : v 6 = 0) (hs : permAct7 (sigP a) v = v) (ht : permAct7 (tauP a) v = v) :
    v = 0 ∨ v = vecPair (pairIdx a) :=
  fixed_pair' a v ⟨h0, h5, h6, hs, ht⟩

theorem eq_sum_vecPair : ∀ v : Fin 7 → ZMod 2, ∑ i, v i = 0 → v 5 = 0 → v 6 = 0 →
    v = v 1 • vecPair 1 + v 2 • vecPair 2 + v 3 • vecPair 3 + v 4 • vecPair 4 := by
  decide +kernel

theorem exists_witP : ∀ y : Fin 7 → ZMod 2, hammingNorm y = 4 →
    ∃ i j : Fin 6, permAct7 (witP i) y + permAct7 (witP j) y = vecPair 1 := by
  decide +kernel

theorem cyc012_fix : permAct7 (a5cyc012 : Perm (Fin 7)) (vecPair 3 + vecPair 4) =
    vecPair 3 + vecPair 4 ∧
    permAct7 ((a5cyc012 : Perm (Fin 7)) * a5cyc012) (vecPair 3) ≠ vecPair 3 := by
  decide +kernel

theorem card_D5 :
    Fintype.card {v : Fin 7 → ZMod 2 // ∑ i, v i = 0 ∧ v 5 = 0 ∧ v 6 = 0} = 16 := by
  decide +kernel

@[expose] def toAltFive (σ : Perm (Fin 7)) (h : sign σ = 1 ∧ σ 5 = 5 ∧ σ 6 = 6) :
    alternatingGroup (Fin 7) :=
  ⟨σ, (mem_alternatingGroup).2 h.1⟩

theorem toAltFive_mem (σ : Perm (Fin 7)) (h : sign σ = 1 ∧ σ 5 = 5 ∧ σ 6 = 6) :
    toAltFive σ h ∈ altFive :=
  ⟨h.2.1, h.2.2⟩

section Coord

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
  {ψ : V ≃* Multiplicative (evenWeight 7)}
  (hyp : Hyp1223 G T L V) (h : A7NatPre T L V ψ) {e : V} (he : vec ψ e = vecFS)

omit [Finite G] in
include h in
theorem conj_eq_of_permAct7 {l : L} {x : V}
    (hx : permAct7 (natLam h.L_le h.Lact l : Perm (Fin 7)) (vec ψ x) = vec ψ x) :
    (l : G) * x * (l : G)⁻¹ = x := by
  have hy : (l : G) * x * (l : G)⁻¹ ∈ V := (mem_normalizer_iff.1 (h.L_le l.2) _).1 x.2
  have h1 := natLam_spec h.L_le h.Lact l x ⟨_, hy⟩ rfl
  rw [hx] at h1
  exact congrArg Subtype.val (vec_injective ψ h1)

omit [Finite G] in
include h in
theorem vec_conj_natLam (l : L) (x : V) :
    ∃ hc : (l : G) * x * (l : G)⁻¹ ∈ V,
      vec ψ ⟨_, hc⟩ = permAct7 (natLam h.L_le h.Lact l : Perm (Fin 7)) (vec ψ x) := by
  have hy : (l : G) * x * (l : G)⁻¹ ∈ V := (mem_normalizer_iff.1 (h.L_le l.2) _).1 x.2
  exact ⟨hy, natLam_spec h.L_le h.Lact l x ⟨_, hy⟩ rfl⟩

include hyp in
theorem commutator_V_Kv_le : ⁅V, Kv hyp e⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro x hx k hk
  have hkV : k ∈ normalizer (V : Set G) := hyp.irrPlus.2.2.1 (Kv_le_L hyp e hk)
  have h1 : k * x⁻¹ * k⁻¹ ∈ V := (mem_normalizer_iff.1 hkV _).1 (V.inv_mem hx)
  have h2 := V.mul_mem hx h1
  rw [commutatorElement_def]
  simpa [mul_assoc] using h2

include h he in
theorem natLam_mem_altFive {k : L} (hk : (k : G) ∈ Kv hyp e) :
    natLam h.L_le h.Lact k ∈ altFive := by
  rw [← natLam_map_Kv hyp h he]
  exact ⟨k, hk, rfl⟩

include h he in
theorem vec_five_six_of_mem {x : V} (hx : (x : G) ∈ ⁅V, Kv hyp e⁆) :
    vec ψ x 5 = 0 ∧ vec ψ x 6 = 0 := by
  set W : Subgroup G :=
    { carrier := {g | ∃ hg : g ∈ V, vec ψ ⟨g, hg⟩ 5 = 0 ∧ vec ψ ⟨g, hg⟩ 6 = 0}
      one_mem' := ⟨V.one_mem, by
        have : (⟨1, V.one_mem⟩ : V) = 1 := rfl
        rw [this, vec_one]
        exact ⟨rfl, rfl⟩⟩
      mul_mem' := by
        rintro a b ⟨ha, ha5, ha6⟩ ⟨hb, hb5, hb6⟩
        refine ⟨V.mul_mem ha hb, ?_⟩
        have : (⟨a * b, V.mul_mem ha hb⟩ : V) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
        rw [this, vec_mul]
        simp only [Pi.add_apply, ha5, ha6, hb5, hb6, add_zero]
        exact ⟨trivial, trivial⟩
      inv_mem' := by
        rintro a ⟨ha, ha5, ha6⟩
        refine ⟨V.inv_mem ha, ?_⟩
        have : (⟨a⁻¹, V.inv_mem ha⟩ : V) = (⟨a, ha⟩ : V)⁻¹ := rfl
        rw [this, vec_inv]
        exact ⟨ha5, ha6⟩ } with hW
  have hle : ⁅V, Kv hyp e⁆ ≤ W := by
    rw [Subgroup.commutator_le]
    intro v hv k hk
    have hkL : k ∈ L := Kv_le_L hyp e hk
    obtain ⟨hc, hvec⟩ := vec_commutator_natLam h ⟨v, hv⟩ ⟨k, hkL⟩
    obtain ⟨h5, h6⟩ := mem_altFive.1 (natLam_mem_altFive hyp h he (k := ⟨k, hkL⟩) hk)
    rw [commutatorElement_def]
    refine ⟨hc, ?_⟩
    rw [hvec]
    have h5' : (natLam h.L_le h.Lact ⟨k, hkL⟩ : Perm (Fin 7))⁻¹ 5 = 5 := by
      rw [Perm.inv_eq_iff_eq]; exact h5.symm
    have h6' : (natLam h.L_le h.Lact ⟨k, hkL⟩ : Perm (Fin 7))⁻¹ 6 = 6 := by
      rw [Perm.inv_eq_iff_eq]; exact h6.symm
    simp only [Pi.add_apply, permAct7_apply, h5', h6']
    exact ⟨zmod_two_add_self _, zmod_two_add_self _⟩
  obtain ⟨hxV, h5, h6⟩ := hle hx
  exact ⟨h5, h6⟩

include h he in
theorem exists_pair_mem (a : Fin 4) :
    ∃ c : V, (c : G) ∈ ⁅V, Kv hyp e⁆ ∧ vec ψ c = vecPair (pairIdx a) := by
  obtain ⟨u, hu⟩ := exists_vec_eq ψ e05_mem
  obtain ⟨k, hkK, hk⟩ := exists_mem_Kv_natLam hyp h he
    (toAltFive_mem (sigP a) (sigP_mem a))
  obtain ⟨hc, hvec⟩ := vec_commutator_natLam h u k
  refine ⟨⟨_, hc⟩, Subgroup.commutator_mem_commutator u.2 hkK, ?_⟩
  rw [hvec, hu, hk]
  exact sigP_e05 a

omit [Finite G] in
theorem mem_of_pairs {S : Subgroup G}
    (hS : ∀ a : Fin 4, ∃ c : V, (c : G) ∈ S ∧ vec ψ c = vecPair (pairIdx a)) {x : V}
    (hx5 : vec ψ x 5 = 0) (hx6 : vec ψ x 6 = 0) : (x : G) ∈ S := by
  classical
  choose c hcS hc using hS
  have hd : ∀ a : Fin 4, ∃ d : V, (d : G) ∈ S ∧
      vec ψ d = vec ψ x (pairIdx a) • vecPair (pairIdx a) := by
    intro a
    rcases zmodTwo_eq_zero_or_one (vec ψ x (pairIdx a)) with h0 | h1
    · exact ⟨1, S.one_mem, by rw [vec_one, h0, zero_smul]⟩
    · exact ⟨c a, hcS a, by rw [hc a, h1, one_smul]⟩
  choose d hdS hd using hd
  have hsum := eq_sum_vecPair (vec ψ x) (mem_evenWeight.1 (vec_mem ψ x)) hx5 hx6
  have hx : x = d 0 * d 1 * d 2 * d 3 := by
    apply vec_injective ψ
    rw [vec_mul, vec_mul, vec_mul, hd 0, hd 1, hd 2, hd 3]
    exact hsum
  rw [hx]
  exact S.mul_mem (S.mul_mem (S.mul_mem (hdS 0) (hdS 1)) (hdS 2)) (hdS 3)

include h he in
theorem mem_commutator_V_Kv_iff (x : V) :
    (x : G) ∈ ⁅V, Kv hyp e⁆ ↔ vec ψ x 5 = 0 ∧ vec ψ x 6 = 0 :=
  ⟨vec_five_six_of_mem hyp h he, fun hx => mem_of_pairs (exists_pair_mem hyp h he) hx.1 hx.2⟩

include h he in
theorem centralizes_commutator_of_commutes {y : G}
    (hyN : y ∈ normalizer ((⁅V, Kv hyp e⁆ : Subgroup G) : Set G))
    (hyc : ∀ k ∈ Kv hyp e, ∀ w ∈ ⁅V, Kv hyp e⁆,
      y * (k * w * k⁻¹) * y⁻¹ = k * (y * w * y⁻¹) * k⁻¹) :
    y ∈ centralizer ((⁅V, Kv hyp e⁆ : Subgroup G) : Set G) := by
  set W := ⁅V, Kv hyp e⁆ with hW
  have hWV : W ≤ V := commutator_V_Kv_le hyp
  have hfix : ∀ a : Fin 4, ∃ c : V, (c : G) ∈ W ∧ vec ψ c = vecPair (pairIdx a) ∧
      y * c * y⁻¹ = c := by
    intro a
    obtain ⟨c, hcW, hc⟩ := exists_pair_mem hyp h he a
    refine ⟨c, hcW, hc, ?_⟩
    have hxW : y * c * y⁻¹ ∈ W := (mem_normalizer_iff.1 hyN _).1 hcW
    set x : V := ⟨_, hWV hxW⟩ with hx
    have hstab : ∀ σ : Perm (Fin 7), (hσ : sign σ = 1 ∧ σ 5 = 5 ∧ σ 6 = 6) →
        permAct7 σ (vecPair (pairIdx a)) = vecPair (pairIdx a) →
        permAct7 σ (vec ψ x) = vec ψ x := by
      intro σ hσ hσc
      obtain ⟨k, hkK, hk⟩ := exists_mem_Kv_natLam hyp h he (toAltFive_mem σ hσ)
      have hkc : (k : G) * c * (k : G)⁻¹ = c := conj_eq_of_permAct7 h (by rw [hk, hc]; exact hσc)
      obtain ⟨hcx, hvx⟩ := vec_conj_natLam h k x
      have h1 : (k : G) * x * (k : G)⁻¹ = x := by
        show (k : G) * (y * c * y⁻¹) * (k : G)⁻¹ = y * c * y⁻¹
        rw [← hyc k hkK c hcW, hkc]
      have h2 : (⟨_, hcx⟩ : V) = x := Subtype.ext h1
      rw [h2, hk] at hvx
      exact hvx.symm
    have hx5 := vec_five_six_of_mem hyp h he (x := x) hxW
    rcases fixed_pair a (vec ψ x) (mem_evenWeight.1 (vec_mem ψ x)) hx5.1 hx5.2
        (hstab _ (sigP_mem a) (sigP_pair a)) (hstab _ (tauP_mem a) (tauP_pair a)) with h0 | h1
    · exfalso
      have hx1 : x = 1 := (vec_eq_zero_iff ψ x).1 h0
      have hc1 : c ≠ 1 := by
        intro hc1
        rw [hc1, vec_one] at hc
        exact absurd (congrFun hc 0) (by
          have : vecPair (pairIdx a) 0 = 1 := by fin_cases a <;> decide
          rw [this]
          decide)
      apply hc1
      have : y * (c : G) * y⁻¹ = 1 := congrArg Subtype.val hx1
      have h3 : (c : G) = 1 := by
        have := congrArg (fun g => y⁻¹ * g * y) this
        simpa [mul_assoc] using this
      exact Subtype.ext h3
    · have : x = c := vec_injective ψ (h1.trans hc.symm)
      exact congrArg Subtype.val this
  set C := centralizer ({y} : Set G) with hC
  have hWC : W ≤ C := by
    intro w hw
    have hwV : w ∈ V := hWV hw
    have h56 := vec_five_six_of_mem hyp h he (x := ⟨w, hwV⟩) hw
    have hmem : ((⟨w, hwV⟩ : V) : G) ∈ C := by
      refine mem_of_pairs (S := C) (fun a => ?_) h56.1 h56.2
      obtain ⟨c, -, hc, hyc'⟩ := hfix a
      refine ⟨c, ?_, hc⟩
      rw [hC, mem_centralizer_singleton_iff]
      have := congrArg (· * y) hyc'
      simpa [mul_assoc] using this.symm
    exact hmem
  rw [mem_centralizer_iff]
  intro w hw
  exact mem_centralizer_singleton_iff.1 (hWC hw)

include h he in
theorem commutator_le_commutator_of_weight_four {U : Subgroup G} {y : V} (hyU : (y : G) ∈ U)
    (hy : hammingNorm (vec ψ y) = 4) : ⁅V, Kv hyp e⁆ ≤ ⁅U, Kv hyp e⁆ := by
  have hst : ∀ σ τ : Perm (Fin 7), (sign σ = 1 ∧ σ 5 = 5 ∧ σ 6 = 6) →
      (sign τ = 1 ∧ τ 5 = 5 ∧ τ 6 = 6) → ∃ c : V, (c : G) ∈ ⁅U, Kv hyp e⁆ ∧
        vec ψ c = permAct7 σ (vec ψ y) + permAct7 τ (vec ψ y) := by
    intro σ τ hσ hτ
    obtain ⟨k, hkK, hk⟩ := exists_mem_Kv_natLam hyp h he (toAltFive_mem σ hσ)
    obtain ⟨k', hkK', hk'⟩ := exists_mem_Kv_natLam hyp h he (toAltFive_mem τ hτ)
    obtain ⟨hc, hvec⟩ := vec_commutator_natLam h y k
    obtain ⟨hc', hvec'⟩ := vec_commutator_natLam h y k'
    refine ⟨⟨_, hc⟩ * ⟨_, hc'⟩, ?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator hyU hkK)
        (Subgroup.commutator_mem_commutator hyU hkK')
    · rw [vec_mul, hvec, hvec', hk, hk']
      show vec ψ y + permAct7 σ (vec ψ y) + (vec ψ y + permAct7 τ (vec ψ y)) = _
      have : vec ψ y + vec ψ y = 0 := fun_add_self_eq_zero _
      calc vec ψ y + permAct7 σ (vec ψ y) + (vec ψ y + permAct7 τ (vec ψ y))
          = (vec ψ y + vec ψ y) + (permAct7 σ (vec ψ y) + permAct7 τ (vec ψ y)) := by abel
        _ = _ := by rw [this, zero_add]
  obtain ⟨i, j, hij⟩ := exists_witP (vec ψ y) hy
  have hpair : ∀ a : Fin 4, ∃ c : V, (c : G) ∈ ⁅U, Kv hyp e⁆ ∧
      vec ψ c = vecPair (pairIdx a) := by
    intro a
    have hσ : sign (piP a * witP i) = 1 ∧ (piP a * witP i) 5 = 5 ∧ (piP a * witP i) 6 = 6 := by
      obtain ⟨s1, s2, s3⟩ := piP_mem a
      obtain ⟨t1, t2, t3⟩ := witP_mem i
      refine ⟨by rw [Perm.sign_mul, s1, t1, one_mul], ?_, ?_⟩
      · rw [Perm.mul_apply, t2, s2]
      · rw [Perm.mul_apply, t3, s3]
    have hτ : sign (piP a * witP j) = 1 ∧ (piP a * witP j) 5 = 5 ∧ (piP a * witP j) 6 = 6 := by
      obtain ⟨s1, s2, s3⟩ := piP_mem a
      obtain ⟨t1, t2, t3⟩ := witP_mem j
      refine ⟨by rw [Perm.sign_mul, s1, t1, one_mul], ?_, ?_⟩
      · rw [Perm.mul_apply, t2, s2]
      · rw [Perm.mul_apply, t3, s3]
    obtain ⟨c, hcU, hc⟩ := hst _ _ hσ hτ
    refine ⟨c, hcU, ?_⟩
    rw [hc, permAct7_mul, permAct7_mul, ← map_add, hij, piP_pair]
  intro x hx
  have hxV : x ∈ V := commutator_V_Kv_le hyp hx
  have h56 := vec_five_six_of_mem hyp h he (x := ⟨x, hxV⟩) hx
  exact mem_of_pairs (S := ⁅U, Kv hyp e⁆) hpair h56.1 h56.2

include h he in
theorem eq_one_of_mem_commutator_of_centralizes {x : V} (hx : (x : G) ∈ ⁅V, Kv hyp e⁆)
    (hxc : ∀ k ∈ Kv hyp e, k * (x : G) * k⁻¹ = x) : x = 1 := by
  have h56 := vec_five_six_of_mem hyp h he hx
  have hstab : ∀ σ : Perm (Fin 7), (hσ : sign σ = 1 ∧ σ 5 = 5 ∧ σ 6 = 6) →
      permAct7 σ (vec ψ x) = vec ψ x := by
    intro σ hσ
    obtain ⟨k, hkK, hk⟩ := exists_mem_Kv_natLam hyp h he (toAltFive_mem σ hσ)
    obtain ⟨hcx, hvx⟩ := vec_conj_natLam h k x
    have h2 : (⟨_, hcx⟩ : V) = x := Subtype.ext (hxc k hkK)
    rw [h2, hk] at hvx
    exact hvx.symm
  have hev := mem_evenWeight.1 (vec_mem ψ x)
  rcases fixed_pair 0 (vec ψ x) hev h56.1 h56.2 (hstab _ (sigP_mem 0))
      (hstab _ (tauP_mem 0)) with h0 | h1
  · exact (vec_eq_zero_iff ψ x).1 h0
  · rcases fixed_pair 1 (vec ψ x) hev h56.1 h56.2 (hstab _ (sigP_mem 1))
        (hstab _ (tauP_mem 1)) with h0' | h1'
    · exact (vec_eq_zero_iff ψ x).1 h0'
    · exfalso
      have h3 := h1.symm.trans h1'
      have h4 := congrFun h3 1
      revert h4
      decide

include h he in
theorem card_commutator_V_Kv : Nat.card ↥⁅V, Kv hyp e⁆ = 16 := by
  classical
  have hle : ⁅V, Kv hyp e⁆ ≤ V := commutator_V_Kv_le hyp
  let f : ↥⁅V, Kv hyp e⁆ → {v : Fin 7 → ZMod 2 // ∑ i, v i = 0 ∧ v 5 = 0 ∧ v 6 = 0} :=
    fun w => ⟨vec ψ ⟨w, hle w.2⟩, mem_evenWeight.1 (vec_mem ψ _),
      vec_five_six_of_mem hyp h he (x := ⟨w, hle w.2⟩) w.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have h1 := congrArg Subtype.val hab
      change vec ψ ⟨a, hle a.2⟩ = vec ψ ⟨b, hle b.2⟩ at h1
      have h2 := congrArg Subtype.val (vec_injective ψ h1)
      exact Subtype.ext h2
    · rintro ⟨v, hv0, hv5, hv6⟩
      obtain ⟨x, hx⟩ := exists_vec_eq ψ (mem_evenWeight.2 hv0)
      have hxW : (x : G) ∈ ⁅V, Kv hyp e⁆ :=
        (mem_commutator_V_Kv_iff hyp h he x).2 ⟨by rw [hx]; exact hv5, by rw [hx]; exact hv6⟩
      exact ⟨⟨x, hxW⟩, Subtype.ext hx⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, card_D5]

include h he in
theorem exists_fix_not_fix_sq :
    ∃ k ∈ Kv hyp e, ∃ w₁ w₂ : V, (w₁ : G) ∈ ⁅V, Kv hyp e⁆ ∧ (w₂ : G) ∈ ⁅V, Kv hyp e⁆ ∧
      w₁ ≠ 1 ∧ k * (w₁ : G) * k⁻¹ = w₁ ∧ (k * k) * (w₂ : G) * (k * k)⁻¹ ≠ w₂ := by
  obtain ⟨k, hkK, hk⟩ := exists_mem_Kv_natLam hyp h he a5cyc012_mem
  have hm1 : vecPair 3 + vecPair 4 ∈ evenWeight 7 := by
    rw [mem_evenWeight]
    decide
  have hm2 : vecPair 3 ∈ evenWeight 7 := by
    rw [mem_evenWeight]
    decide
  obtain ⟨w₁, hw₁⟩ := exists_vec_eq ψ hm1
  obtain ⟨w₂, hw₂⟩ := exists_vec_eq ψ hm2
  obtain ⟨hfix, hmove⟩ := cyc012_fix
  refine ⟨k, hkK, w₁, w₂, ?_, ?_, ?_, ?_, ?_⟩
  · exact (mem_commutator_V_Kv_iff hyp h he w₁).2 (by rw [hw₁]; decide)
  · exact (mem_commutator_V_Kv_iff hyp h he w₂).2 (by rw [hw₂]; decide)
  · intro h1
    rw [h1, vec_one] at hw₁
    have := congrFun hw₁ 3
    revert this
    decide
  · exact conj_eq_of_permAct7 h (by rw [hk, hw₁]; exact hfix)
  · intro h1
    apply hmove
    have hkk : natLam h.L_le h.Lact (k * k) = a5cyc012 * a5cyc012 := by rw [map_mul, hk]
    obtain ⟨hc, hvec⟩ := vec_conj_natLam h (k * k) w₂
    have h2 : (⟨_, hc⟩ : V) = w₂ := Subtype.ext h1
    rw [h2, hkk, hw₂] at hvec
    exact hvec.symm

end Coord

end CFSG.Quasithin.H13.A7
