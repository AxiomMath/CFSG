module

public import CFSG.Certificates.NativeSchreierCard
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec
public import CFSG.Sporadic.SuzOddCore.CTIChainInputs
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

theorem card_closure_of_rawChainOK_tabRep {n : ℕ} (hn : 1 ≤ n) {O S : Array (Array ℕ)}
    {W : Array (List ℤ)} {base : List (Fin n)} (hb : base.Nodup) (hOS : O.size ≤ S.size)
    (hSO : ∀ i < O.size, S[i]! = O[i]!)
    (h : rawChainOK n (S.extract 0 O.size) S (base.map Fin.val).toArray W 4 = true)
    {f : ℕ → Equiv.Perm (Fin n)} (hf : ∀ k < O.size, TabRep O[k]! (f k)) :
    Nat.card (Subgroup.closure {g | ∃ k < O.size, f k = g}) =
      (rawOrbitSizes n S (base.map Fin.val).toArray).prod := by
  have hF := chainCheckFacts h
  have hA := chainArrays_ofArrays (hn := hn) (k := O.size) (hk := hOS) (hb := hb) (W := W)
    hF.strong_inv
  have hcard := card_originalSubgroup_of_chainOK hA (by norm_num) h
  have hpe : ∀ k < O.size, permOfArr n S[k]! = f k := fun k hk => by
    have hr := (rep_permOfArr (hF.strong_inv k (by omega))).1
    refine Rep.unique hr fun x => ?_
    rw [hSO k hk]
    exact (hf k hk).2 x
  have hQ : (RawSchreierDatum.ofArrays n hn S O.size hOS base hb W).originalSubgroup =
      Subgroup.closure {g | ∃ k < O.size, f k = g} := by
    unfold RawSchreierDatum.originalSubgroup
    congr 1
    ext g
    rw [Set.mem_ofPred_eq, Set.mem_setOf_eq, RawSchreierDatum.mem_ofArrays_original]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, (hpe i hi).symm⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, hpe i hi⟩
  rw [← hQ]
  exact hcard

theorem pushStrong_size (n : ℕ) :
    ∀ (ws : List (List ℤ)) (S : Array (Array ℕ)), (pushStrong n S ws).size = S.size + ws.length
  | [], S => by simp [pushStrong]
  | w :: ws, S => by
    rw [pushStrong, pushStrong_size n ws, Array.size_push, List.length_cons]
    omega

theorem pushStrong_get (n : ℕ) :
    ∀ (ws : List (List ℤ)) (S : Array (Array ℕ)) {i : ℕ}, i < S.size →
      (pushStrong n S ws)[i]! = S[i]!
  | [], _, _, _ => rfl
  | w :: ws, S, i, hi => by
    rw [pushStrong, pushStrong_get n ws _ (by rw [Array.size_push]; omega),
      getElem!_pos _ i (by rw [Array.size_push]; omega), getElem!_pos S i hi,
      Array.getElem_push_lt]

section Centralizer

variable {n m : ℕ} {H Q : Subgroup (Equiv.Perm (Fin n))} {E : Array Tab}

noncomputable def enumElt (hQ : Enumerates Q E.toList) (hm : E.size = m) (p : Fin m) : Q :=
  ⟨(hQ.exists_elt (k := p) (hm ▸ p.2)).choose, (hQ.exists_elt (k := p) (hm ▸ p.2)).choose_spec.1⟩

theorem tabRep_enumElt (hQ : Enumerates Q E.toList) (hm : E.size = m) (p : Fin m) :
    TabRep E[(p : ℕ)]! (enumElt hQ hm p : Equiv.Perm (Fin n)) :=
  (hQ.exists_elt (k := p) (hm ▸ p.2)).choose_spec.2

theorem enumElt_bijective (hQ : Enumerates Q E.toList) (hm : E.size = m) :
    Function.Bijective (enumElt hQ hm) := by
  constructor
  · intro p q hpq
    have h1 := tabRep_enumElt hQ hm p
    have h2 := tabRep_enumElt hQ hm q
    rw [hpq] at h1
    exact Fin.ext (hQ.pos_unique (hm ▸ p.2) (hm ▸ q.2) h1 h2)
  · intro x
    obtain ⟨k, hk, hr⟩ := hQ.exists_pos x.2
    refine ⟨⟨k, hm ▸ hk⟩, Subtype.ext ?_⟩
    exact (tabRep_enumElt hQ hm ⟨k, hm ▸ hk⟩).perm_eq hr

theorem card_mul_card_centralizer_le (hQ : Enumerates Q E.toList) (hm : E.size = m)
    (hHN : H ≤ Subgroup.normalizer (Q : Set (Equiv.Perm (Fin n)))) {k : ℕ}
    (g : ℕ → Equiv.Perm (Fin n)) (hg : ∀ j < k, g j ∈ H) (σ : ℕ → Equiv.Perm (Fin m))
    (hσ : ∀ j < k, ∀ p : Fin m, ∀ x : Equiv.Perm (Fin n), TabRep E[(p : ℕ)]! x →
      TabRep E[(σ j p : ℕ)]! (g j * x * (g j)⁻¹)) :
    Nat.card (Subgroup.closure {s | ∃ j < k, σ j = s}) *
      Nat.card ((Subgroup.centralizer (Q : Set (Equiv.Perm (Fin n)))).subgroupOf H) ≤
      Nat.card H := by
  classical
  let e : Fin m ≃ Q := Equiv.ofBijective _ (enumElt_bijective hQ hm)
  let φ : H →* Equiv.Perm (Fin m) :=
    (e.symm.permCongrHom.toMonoidHom.comp (MulAut.toPerm Q)).comp
      (Q.normalizerMonoidHom.comp (Subgroup.inclusion hHN))
  have hφ : ∀ (h : H) (p : Fin m),
      ((e (φ h p) : Q) : Equiv.Perm (Fin n)) = (h : Equiv.Perm (Fin n)) * e p * (h : _)⁻¹ :=
    fun h p => by
      change ((e (e.symm (Q.normalizerMonoidHom (Subgroup.inclusion hHN h) (e p))) : Q) :
        Equiv.Perm (Fin n)) = _
      rw [Equiv.apply_symm_apply]
      rfl
  have hker : φ.ker = (Subgroup.centralizer (Q : Set (Equiv.Perm (Fin n)))).subgroupOf H := by
    ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro h1 x hx
      have h2 := hφ h (e.symm ⟨x, hx⟩)
      rw [h1, Equiv.Perm.coe_one, id_eq, Equiv.apply_symm_apply] at h2
      have h3 : x = (h : Equiv.Perm (Fin n)) * x * (h : Equiv.Perm (Fin n))⁻¹ := by simpa using h2
      rw [eq_mul_inv_iff_mul_eq] at h3
      exact h3
    · intro h1
      ext p
      have h2 := hφ h p
      rw [Subgroup.coe_inv, ← h1 _ (e p).2, mul_inv_cancel_right] at h2
      rw [Equiv.Perm.one_apply]
      exact congrArg Fin.val (e.injective (Subtype.ext h2))
  have hσφ : ∀ j (hj : j < k), σ j = φ ⟨g j, hg j hj⟩ := fun j hj => by
    ext p
    have h1 := hσ j hj p _ (tabRep_enumElt hQ hm p)
    have h2 := tabRep_enumElt hQ hm (σ j p)
    have h3 := hφ ⟨g j, hg j hj⟩ p
    have h4 : e (σ j p) = e (φ ⟨g j, hg j hj⟩ p) := Subtype.ext ((h2.perm_eq h1).trans h3.symm)
    rw [e.injective h4]
  have hle : Subgroup.closure {s | ∃ j < k, σ j = s} ≤ φ.range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact ⟨_, (hσφ j hj).symm⟩
  rw [← Subgroup.card_ker_mul_card_range φ, hker, mul_comm]
  exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hle)

end Centralizer

end CFSG.Sporadic.SuzOddCore
