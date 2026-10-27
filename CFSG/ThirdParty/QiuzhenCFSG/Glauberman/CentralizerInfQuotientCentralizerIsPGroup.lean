module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma5_3
public import Mathlib.GroupTheory.GroupAction.ConjAct

namespace CFSG
end CFSG
open CFSG

/-!
# Centralizers of a normal subgroup and its quotient factor

This is the Lemma 5.3 input used in paper step 4 of Glauberman Lemma 6.3.
For normal `K ≤ H ◁ Q`, the elements centralizing `K` and inducing the
identity on `H/K` act on `H` through `lemma5_3Centralizer K`.  If both `H`
and `C_Q(H)` are `p`-groups, this ambient intersection is therefore a
`p`-group.
-/

namespace CFSG.Glauberman

universe u

public theorem centralizer_inf_quotientCentralizer_isPGroup
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (H : Subgroup Q) [H.Normal] (hHp : IsPGroup p H)
    (hCp : IsPGroup p (Subgroup.centralizer (H : Set Q)))
    (K : Subgroup Q) [K.Normal] (hKH : K ≤ H) :
    let q : Q →* Q ⧸ K := QuotientGroup.mk' K
    let Hbar : Subgroup (Q ⧸ K) := H.map q
    let D : Subgroup Q :=
      (Subgroup.centralizer (Hbar : Set (Q ⧸ K))).comap q
    IsPGroup p (↑(Subgroup.centralizer (K : Set Q) ⊓ D)) := by
  classical
  let q : Q →* Q ⧸ K := QuotientGroup.mk' K
  let Hbar : Subgroup (Q ⧸ K) := H.map q
  let D : Subgroup Q :=
    (Subgroup.centralizer (Hbar : Set (Q ⧸ K))).comap q
  let CK : Subgroup Q := Subgroup.centralizer (K : Set Q)
  let C : Subgroup Q := Subgroup.centralizer (H : Set Q)
  let E : Subgroup Q := CK ⊓ D
  let P : Subgroup H := K.subgroupOf H
  have hPnormal : P.Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : K.Normal) H
  letI : P.Normal := hPnormal
  have hCE : C ≤ E := by
    intro c hc
    constructor
    · change c ∈ Subgroup.centralizer (K : Set Q)
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact Subgroup.mem_centralizer_iff.mp hc k (hKH hk)
    · change q c ∈ Subgroup.centralizer (Hbar : Set (Q ⧸ K))
      rw [Subgroup.mem_centralizer_iff]
      intro hbar hhbar
      rcases Subgroup.mem_map.mp hhbar with ⟨h, hh, rfl⟩
      simpa only [map_mul] using congrArg q
        (Subgroup.mem_centralizer_iff.mp hc h hh)
  let conjE : E →* MulAut H :=
    (MulAut.conjNormal (H := H)).comp E.subtype
  have hconjE_mem : ∀ e : E, conjE e ∈ lemma5_3Centralizer P := by
    intro e
    rw [mem_lemma5_3Centralizer]
    constructor
    · intro k hk
      apply Subtype.ext
      have hkK : (k : Q) ∈ K := Subgroup.mem_subgroupOf.mp hk
      have heCK : (e : Q) ∈ CK := e.2.1
      have hcomm : (k : Q) * (e : Q) = (e : Q) * (k : Q) :=
        Subgroup.mem_centralizer_iff.mp heCK (k : Q) hkK
      change (e : Q) * (k : Q) * (e : Q)⁻¹ = (k : Q)
      rw [← hcomm]
      group
    · intro h
      apply QuotientGroup.eq.mpr
      apply Subgroup.mem_subgroupOf.mpr
      have heD : (e : Q) ∈ D := e.2.2
      have heCent : q (e : Q) ∈
          Subgroup.centralizer (Hbar : Set (Q ⧸ K)) := heD
      have hhbar : q (h : Q) ∈ Hbar :=
        Subgroup.mem_map.mpr ⟨(h : Q), h.2, rfl⟩
      have hcomm : q (h : Q) * q (e : Q) = q (e : Q) * q (h : Q) :=
        Subgroup.mem_centralizer_iff.mp heCent (q (h : Q)) hhbar
      have hconjEq :
          q ((e : Q) * (h : Q) * (e : Q)⁻¹) = q (h : Q) := by
        simp only [map_mul, map_inv]
        rw [← hcomm]
        group
      exact QuotientGroup.eq.mp hconjEq
  let psi : E →* lemma5_3Centralizer P :=
    conjE.codRestrict (lemma5_3Centralizer P) hconjE_mem
  have hker : psi.ker = C.subgroupOf E := by
    ext e
    constructor
    · intro he
      apply Subgroup.mem_subgroupOf.mpr
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have heone : psi e = 1 := he
      have hconjOne : conjE e = 1 := congrArg Subtype.val heone
      have heval := congrArg (fun a : MulAut H => a ⟨h, hh⟩) hconjOne
      have hconj : (e : Q) * h * (e : Q)⁻¹ = h :=
        congrArg Subtype.val heval
      calc
        h * (e : Q) = ((e : Q) * h * (e : Q)⁻¹) * (e : Q) := by rw [hconj]
        _ = (e : Q) * h := by group
    · intro he
      change psi e = 1
      apply Subtype.ext
      apply MulEquiv.ext
      intro h
      apply Subtype.ext
      have heC : (e : Q) ∈ C := Subgroup.mem_subgroupOf.mp he
      have hcomm : (h : Q) * (e : Q) = (e : Q) * (h : Q) :=
        Subgroup.mem_centralizer_iff.mp heC (h : Q) h.2
      change (e : Q) * (h : Q) * (e : Q)⁻¹ = (h : Q)
      rw [← hcomm]
      group
  have hCsubp : IsPGroup p (C.subgroupOf E) :=
    hCp.of_equiv (Subgroup.subgroupOfEquivOfLe hCE).symm
  have hkerp : IsPGroup p psi.ker := by
    rw [hker]
    exact hCsubp
  have htargetp : IsPGroup p (lemma5_3Centralizer P) :=
    lemma5_3 hHp P
  have hcomap : IsPGroup p ((⊤ : Subgroup (lemma5_3Centralizer P)).comap psi) :=
    (htargetp.to_subgroup (⊤ : Subgroup (lemma5_3Centralizer P))).comap_of_ker_isPGroup
      psi hkerp
  have hcomapEq :
      (⊤ : Subgroup (lemma5_3Centralizer P)).comap psi = (⊤ : Subgroup E) := by
    ext e
    simp
  have htopE : IsPGroup p (⊤ : Subgroup E) := by
    rw [← hcomapEq]
    exact hcomap
  have hEp : IsPGroup p E :=
    htopE.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup E) ≃* E)
  simpa [E, CK, D, Hbar, q] using hEp

end CFSG.Glauberman
