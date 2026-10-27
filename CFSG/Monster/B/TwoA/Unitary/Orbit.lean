
module

public import CFSG.Monster.B.TwoA.Unitary.OrbitBase

public import CFSG.Monster.B.TwoA.Unitary.Action
public import CFSG.Monster.B.TwoA.Census.NatCert
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public meta import CFSG.Monster.B.TwoA.Unitary.NData
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Unitary.OrbitInputs
public import Certificates.Certificate3041
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Unitary.Bridge
public import CFSG.Monster.B.TwoA.Unitary.ActionInputs

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.VisQuot CFSG.Monster.VisCert
  CFSG.Monster.SpinLattice CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Census

theorem n6Vec_lt : ∀ j < 891, n6VecArr[j]! < 2 ^ 22 :=
  Certificates.certificate3041.1

theorem n6Vec_inj :
    ∀ i < 891, ∀ j < 891, n6VecArr[i]! = n6VecArr[j]! → i = j :=
  Certificates.certificate3041.2.1

theorem n6Perm_lt :
    ∀ k < 17, ∀ j < 891, (n6PermsArr[k]!)[j]! < 891 :=
  Certificates.certificate3041.2.2.1

theorem n6Perm_act : ∀ k < 17, ∀ j < 891,
    Native.actD 22 n6RowArr[k]! n6VecArr[j]! = n6VecArr[(n6PermsArr[k]!)[j]!]! :=
  Certificates.certificate3041.2.2.2.1

theorem n6vec_injective : Function.Injective n6vec := by
  intro i j h
  exact Fin.ext (n6Vec_inj i i.2 j j.2 (decW_injective (n6Vec_lt i i.2) (n6Vec_lt j j.2) h))

theorem n6perm_val (k : Fin 17) (j : Fin 891) :
    ((n6perm k j : Fin 891) : ℕ) = (n6PermsArr[(k : ℕ)]!)[(j : ℕ)]! :=
  Nat.mod_eq_of_lt (n6Perm_lt k k.2 j j.2)

theorem wAct_genK_n6vec
    (k : Fin 17) (j : Fin 891) :
    wAct v0 (genK k) (n6vec j) = n6vec (n6perm k j) := by
  rw [n6vec, wAct_genK_decW, genRows, n6Perm_act k k.2 j j.2, n6vec, n6perm_val]

theorem wAct_genK_sigma
    (k : Fin 17) : wAct v0 (genK k) sigmaW = sigmaW := by
  rw [sigmaW_eq_decW, wAct_genK_decW, genRows, n6Rows_fix_sigma k k.2]

theorem genK_mem_Usig
    (k : Fin 17) : genK k ∈ Usig := wAct_genK_sigma k

@[expose] def H6K :
    Subgroup (Kstab v0) := Subgroup.closure (Set.range genK)

theorem map_H6K :
    H6K.map (Kstab v0).subtype = H6 := by
  rw [H6K, MonoidHom.map_closure, H6, ← Set.range_comp]
  rfl

theorem H6K_le_Usig :
    H6K ≤ Usig := by
  rw [H6K, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  exact genK_mem_Usig k

theorem orbitCert_ok :
    natCertOK genAct 17 (fun a => decide (a < 2 ^ 22)) 31 orbitCert = true :=
  Certificates.certificate3041.2.2.2.2.1

theorem orbitCert_pts : orbitCert.pts = n6VecArr :=
  Certificates.certificate3041.2.2.2.2.2

attribute [local instance] wLeftAction

@[expose] def gensL
    (k : ℕ) : Kstab v0 := if h : k < 17 then (genK ⟨k, h⟩)⁻¹ else 1

theorem gensL_smul
    {k : ℕ} (hk : k < 17) (x : Wv v0) : gensL k • x = wAct v0
    (genK ⟨k, hk⟩) x := by
  rw [gensL, dite_eq_left hk]
  change wAct v0 (genK ⟨k, hk⟩)⁻¹⁻¹ x = _
  rw [inv_inv]

theorem closure_gensL :
    Subgroup.closure (gensL '' {k | k < 17}) = H6K := by
  have e : gensL '' {k | k < 17} = (Set.range genK)⁻¹ := by
    ext g
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_inv, Set.mem_range]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, by rw [gensL, dite_eq_left hk, inv_inv]⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, k.2, ?_⟩
      rw [gensL, dite_eq_left k.2, hk, inv_inv]
  rw [e, Subgroup.closure_inv, H6K]

theorem gensL_act :
    ∀ k < 17, ∀ a, decide (a < 2 ^ 22) = true →
    decW (genAct k a) = gensL k • decW a := by
  intro k hk a _
  rw [gensL_smul hk, wAct_genK_decW]
  rfl

theorem orbit_H6K :
    MulAction.orbit H6K wFr =
    Set.range n6vec := by
  have h := orbit_of_natCertOK (gens := gensL) (dec := decW) orbitCert_ok gensL_act
  rw [closure_gensL, ← wFr_eq_decW, orbitCert_pts, n6Vec_size] at h
  rw [h]
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, j.2, rfl⟩

theorem ncard_range_n6vec : (Set.range n6vec).ncard = 891 := by
  rw [← Set.image_univ, Set.ncard_image_of_injective _ n6vec_injective, Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin]

end CFSG.Monster.B.TwoA.Unitary
