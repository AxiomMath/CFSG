module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.CentralizerInfQuotientCentralizerIsPGroup
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Definitions

namespace CFSG
end CFSG
open CFSG

/-!
# The p-core preimage centralizing a normal p-subgroup

This packages the p-group extension at the end of paper step 4 of
Glauberman Lemma 6.3.  With `D = C_Q(H/K)` and `N/D = O_p(Q/D)`, the group
`C_N(K)` is a `p`-group once `H` and `C_Q(H)` are `p`-groups.
-/

namespace CFSG.Glauberman

universe u

public theorem centralizer_inf_pCorePreimage_isPGroup
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (H : Subgroup Q) [H.Normal] (hHp : IsPGroup p H)
    (hCp : IsPGroup p (Subgroup.centralizer (H : Set Q)))
    (K : Subgroup Q) [K.Normal] (hKH : K ≤ H) :
    let qK : Q →* Q ⧸ K := QuotientGroup.mk' K
    let Hbar : Subgroup (Q ⧸ K) := H.map qK
    let D : Subgroup Q :=
      (Subgroup.centralizer (Hbar : Set (Q ⧸ K))).comap qK
    let qD : Q →* Q ⧸ D := QuotientGroup.mk' D
    let N : Subgroup Q := (pCore p (Q ⧸ D)).comap qD
    IsPGroup p (↑(Subgroup.centralizer (K : Set Q) ⊓ N)) := by
  classical
  let qK : Q →* Q ⧸ K := QuotientGroup.mk' K
  let Hbar : Subgroup (Q ⧸ K) := H.map qK
  let D : Subgroup Q :=
    (Subgroup.centralizer (Hbar : Set (Q ⧸ K))).comap qK
  have hHbarNormal : Hbar.Normal :=
    Subgroup.Normal.map (inferInstance : H.Normal) qK
      (QuotientGroup.mk'_surjective K)
  let : Hbar.Normal := hHbarNormal
  have hDnormal : D.Normal :=
    Subgroup.Normal.comap (Subgroup.normal_centralizer (H := Hbar)) qK
  let : D.Normal := hDnormal
  let qD : Q →* Q ⧸ D := QuotientGroup.mk' D
  let N : Subgroup Q := (pCore p (Q ⧸ D)).comap qD
  let CK : Subgroup Q := Subgroup.centralizer (K : Set Q)
  let CN : Subgroup Q := CK ⊓ N
  let E : Subgroup Q := CK ⊓ D
  have hEp : IsPGroup p E := by
    simpa [E, CK, D, Hbar, qK] using
      (centralizer_inf_quotientCentralizer_isPGroup
        (p := p) H hHp hCp K hKH)
  let phi0 : CN →* Q ⧸ D := qD.comp CN.subtype
  let phi : CN →* pCore p (Q ⧸ D) :=
    phi0.codRestrict (pCore p (Q ⧸ D)) (by
      intro z
      exact z.2.2)
  have hker_mem_E : ∀ z : phi.ker, (z : Q) ∈ E := by
    intro z
    constructor
    · exact z.1.2.1
    · have hzphi : phi z.1 = 1 := z.2
      have hzq : qD (z : Q) = 1 := congrArg Subtype.val hzphi
      exact (QuotientGroup.eq_one_iff (z : Q)).mp hzq
  let kerToE : phi.ker →* E :=
    (CN.subtype.comp phi.ker.subtype).codRestrict E hker_mem_E
  have hkerToE_inj : Function.Injective kerToE := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun e : E => (e : Q)) hab
  have hkerp : IsPGroup p phi.ker :=
    hEp.of_injective kerToE hkerToE_inj
  have hcomap : IsPGroup p ((⊤ : Subgroup (pCore p (Q ⧸ D))).comap phi) :=
    ((pCore_isPGroup (p := p) (G := Q ⧸ D)).to_subgroup
      (⊤ : Subgroup (pCore p (Q ⧸ D)))).comap_of_ker_isPGroup phi hkerp
  have hcomapEq :
      (⊤ : Subgroup (pCore p (Q ⧸ D))).comap phi = (⊤ : Subgroup CN) := by
    ext z
    simp
  have htopCN : IsPGroup p (⊤ : Subgroup CN) := by
    rw [← hcomapEq]
    exact hcomap
  have hCNp : IsPGroup p CN :=
    htopCN.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup CN) ≃* CN)
  simpa [CN, CK, N, qD, D, Hbar, qK] using hCNp

end CFSG.Glauberman
