
module

public import CFSG.Sporadic.HNOddCore.FourPairABase
public import CFSG.Sporadic.HNOddCore.CCheckInputs
public meta import CFSG.Sporadic.HNSchreier.ThreeCheck
public import CFSG.Sporadic.HNOddCore.DCheckInputs
public import CFSG.Sporadic.HNOddCore.NatCheckInputs
public meta import CFSG.Sporadic.HNOddCore.InvData
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
public import CFSG.Sporadic.HNOddCore.QCheckInputs
public import CFSG.Sporadic.HNOddCore.SCheckInputs
public import CFSG.Sporadic.HNOddCore.XCheckInputs
public meta import CFSG.Sporadic.HNOddCore.CCheck
public meta import CFSG.Sporadic.HNOddCore.InvArrays
public meta import Certificates.Data.CFSGNative.ONSchreier.Tools
public import CFSG.Sporadic.HNSchreier.ChainCheckInputs
public import CFSG.Sporadic.HNSchreier.LevelInputs
public meta import CFSG.Sporadic.HNSchreier.OrbitCheck
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
public import CFSG.Sporadic.HNSchreier.InvolCheckInputs
public meta import CFSG.Sporadic.HNSchreier.SeedsCheck
public import CFSG.Sporadic.HNSchreier.LocalCheckInputs
public meta import CFSG.Sporadic.HNSchreier.PrimCheck
public meta import CFSG.Sporadic.HNSchreier.LocalData
public meta import CFSG.Sporadic.HNSchreier.MaskCheck
public import CFSG.Sporadic.HNSchreier.OrbitCheckInputs
public import CFSG.Sporadic.HNSchreier.PrimCheckInputs
public meta import Certificates.Data.CFSGNative.Perm.Chain
public import CFSG.Sporadic.HNSchreier.VectorData

@[expose] public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv

theorem closure_subset_of_mul_mem {G : Type*} [Group G] [Finite G] {S T : Set G}
    (h1 : (1 : G) ∈ T) (hT : ∀ s ∈ S, ∀ t ∈ T, s * t ∈ T) :
    (Subgroup.closure S : Set G) ⊆ T := by
  have hmul : ∀ x y : G, (∀ t ∈ T, x * t ∈ T) → (∀ t ∈ T, y * t ∈ T) →
      ∀ t ∈ T, x * y * t ∈ T := fun x y hx hy t ht => by
    rw [mul_assoc]
    exact hx _ (hy t ht)
  have hpow : ∀ x : G, (∀ t ∈ T, x * t ∈ T) → ∀ k : ℕ, ∀ t ∈ T, x ^ k * t ∈ T := by
    intro x hx k
    induction k with
    | zero => intro t ht; rwa [pow_zero, one_mul]
    | succ k ih => rw [pow_succ]; exact hmul _ _ ih hx
  let M : Subgroup G :=
    { carrier := {x | ∀ t ∈ T, x * t ∈ T}
      mul_mem' := fun {x y} hx hy => hmul x y hx hy
      one_mem' := fun t ht => by rwa [one_mul]
      inv_mem' := fun {x} hx => by
        have e : x⁻¹ = x ^ (orderOf x - 1) := by
          rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ,
            Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
        show ∀ t ∈ T, x⁻¹ * t ∈ T
        rw [e]
        exact hpow x hx _ }
  have hle : Subgroup.closure S ≤ M := by
    rw [Subgroup.closure_le]
    intro s hs t ht
    exact hT s hs t ht
  intro x hx
  have := hle hx 1 h1
  rwa [mul_one] at this

theorem mem_normalizer_of_conj {G : Type*} [Group G] {H : Subgroup G} [Finite H] {x : G}
    (h : ∀ y ∈ H, x * y * x⁻¹ ∈ H) : x ∈ Subgroup.normalizer (H : Set G) := by
  refine Subgroup.mem_normalizer_iff.2 fun y => ⟨h y, fun hy => ?_⟩
  let c : H → H := fun z => ⟨x * z * x⁻¹, h z z.2⟩
  have hc : Function.Injective c := fun a b hab => by
    have := congrArg Subtype.val hab
    exact Subtype.ext (mul_left_cancel (mul_right_cancel this))
  obtain ⟨z, hz⟩ := (Finite.injective_iff_surjective.1 hc) ⟨x * y * x⁻¹, hy⟩
  have e : (z : G) = y := mul_left_cancel (mul_right_cancel (congrArg Subtype.val hz))
  rw [← e]
  exact z.2

theorem prep_pword_mem {n : ℕ} {S Sinv : Array (Array ℕ)} {gs : ℕ → Perm (Fin n)} {j : ℕ}
    (hS : ∀ h < j, PRep n S[h]! (gs h)) (hSinv : ∀ h < j, PRep n Sinv[h]! (gs h)⁻¹)
    {K : Subgroup (Perm (Fin n))} (hK : ∀ h < j, gs h ∈ K) :
    ∀ w : List ℤ, plettersOK j w = true → ∃ σ ∈ K, PRep n (pword n S Sinv w) σ
  | [], _ => ⟨1, K.one_mem, by simpa [pword] using (prep_pid (n := n))⟩
  | l :: w, hw => by
    simp only [plettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlj⟩, hw⟩ := hw
    have hw' : plettersOK j w = true := by
      simpa [plettersOK, List.all_eq_true] using hw
    obtain ⟨σ, hσ, hp⟩ := prep_pword_mem hS hSinv hK w hw'
    have hlet := prep_pletter hS hSinv ⟨hl0, hlj⟩
    rw [pword]
    by_cases hpos : 0 < l
    · rw [ite_eq_left (decide_eq_true hpos)] at hlet
      exact ⟨_, K.mul_mem (hK _ (by omega)) hσ, prep_pcomp hlet hp⟩
    · rw [ite_eq_right (by simpa using hpos)] at hlet
      exact ⟨_, K.mul_mem (K.inv_mem (hK _ (by omega))) hσ, prep_pcomp hlet hp⟩

theorem q_parts :
    InvData.s4Perms.size = 11 ∧ InvData.qPerms.size = 8 ∧
    (qbList 800 InvData.qPerms).size = 256 ∧ colPerms.size = 11 ∧
    (∀ g < 11, pisInv 800 InvData.s4Perms[g]! (pinvs 800 InvData.s4Perms)[g]! = true) ∧
    (∀ i < 8, plettersOK 11 QData.qFlat[i]! = true ∧ peq 800 (pword 800 InvData.s4Perms
      (pinvs 800 InvData.s4Perms) QData.qFlat[i]!) InvData.qPerms[i]! = true) ∧
    (∀ i < 8, ∀ j < 8, peq 800 (pcomp 800 InvData.qPerms[i]! InvData.qPerms[j]!)
      (pcomp 800 InvData.qPerms[j]! InvData.qPerms[i]!) = true) ∧
    (∀ i < 8, peq 800 (pcomp 800 InvData.qPerms[i]! InvData.qPerms[i]!) (pid 800) = true) ∧
    (∀ i < 8, ∀ m < 256, m ^^^ (1 <<< i) < 256 ∧ peq 800 (pcomp 800 InvData.qPerms[i]!
      (qbList 800 InvData.qPerms)[m]!) (qbList 800 InvData.qPerms)[m ^^^ (1 <<< i)]! = true) ∧
    (∀ g < 11, pisInv 256 colPerms[g]! (pinvCand 256 colPerms[g]!) = true ∧ ∀ m < 256,
      (colPerms[g]!)[m]! < 256 ∧ peq 800 (pcomp 800 (pinvs 800 InvData.s4Perms)[g]!
        (pcomp 800 (qbList 800 InvData.qPerms)[m]! InvData.s4Perms[g]!))
        (qbList 800 InvData.qPerms)[(colPerms[g]!)[m]!]! = true) ∧
    chainCheck 800 InvData.qPerms QData.qWords QData.qBase QData.qSizes = true ∧
    chainCheck 256 colPerms QData.conjWords QData.conjBase QData.conjSizes = true := by
  have h := q_cert
  unfold qChecks qChecksH at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, -⟩, h12⟩, h13⟩ := h
  refine ⟨h1, h2, h3, h4, fun g hg => allBelowN_spec h5 hg, fun i hi => ?_,
    fun i hi j hj => allBelowN_spec (allBelowN_spec h7 hi) hj, fun i hi => allBelowN_spec h8 hi,
    fun i hi m hm => ?_, fun g hg => ?_, h12, h13⟩
  · have := allBelowN_spec h6 hi
    simpa only [Bool.and_eq_true] using this
  · have := allBelowN_spec (allBelowN_spec h9 hi) hm
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using this
  · have := allBelowN_spec h10 hg
    simp only [Bool.and_eq_true] at this
    refine ⟨this.1, fun m hm => ?_⟩
    have := allBelowN_spec this.2 hm
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using this

def qbar (i : ℕ) : Perm (Fin 800) := Monster.B.Co2.permOfArr 800 InvData.qPerms[i]!

abbrev Qbar : Subgroup (Perm (Fin 800)) := Subgroup.closure (Set.range fun i : Fin 8 => qbar i)

theorem qbar_mem {i : ℕ} (hi : i < 8) : qbar i ∈ Qbar :=
  Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩

theorem qPerms_size : InvData.qPerms.size = 8 := q_parts.2.1

theorem qbList_get {m : ℕ} (hm : m < 256) :
    (qbList 800 InvData.qPerms)[m]! = subQ 800 InvData.qPerms m := by
  rw [qbList, getElem!_pos _ m (by simp [hm]), Array.getElem_ofFn]

def qb (m : ℕ) : Perm (Fin 800) :=
  Monster.B.Co2.permOfArr 800 (qbList 800 InvData.qPerms)[m]!

theorem foldl_acc {α : Type*} : ∀ (L : List ℕ) (acc : α), L.foldl (fun acc _ => acc) acc = acc
  | [], _ => rfl
  | _ :: L, acc => foldl_acc L acc

theorem colPerm_lt
    {g : ℕ} (hg : g < 11) {m : ℕ} (hm : m < 256) : (colPerms[g]!)[m]! < 256 :=
  ((q_parts.2.2.2.2.2.2.2.2.2.1 g hg).2 m hm).1

end CFSG.Sporadic.HNOddCore
