module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CoprimeActionSupNontrivial
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.MinimalInvariantInvolutionCommutator

namespace CFSG
end CFSG
open CFSG

/-!
# The Fact 1.1(iv) normalizer–centralizer equation

This is the source-facing Theorem 2.6 step
`P = N_P(O_p(H)) = C_P(O_p(H))`.
-/

namespace CFSG.GorensteinWalter

universe u

open scoped Pointwise

/-- Let `P` be minimal among the `H`-invariant odd `p`-subgroups on which
the central involution `t` acts nontrivially.  Then `P` both normalizes and
centralizes `O_p(H)`, in the exact intersection form used by the source. -/
public theorem normalizer_inf_qCoreOf_eq_self_and_centralizer_inf_qCoreOf_eq_self_of_minimal_invariant
    {G : Type u} [Group G] [Finite G]
    (H P : Subgroup G) (p : ℕ) {t : G}
    (hp : p.Prime) (hpodd : Odd p)
    (ht : IsInvolution t) (htH : t ∈ H)
    (hHt : H ≤ Subgroup.centralizer ({t} : Set G))
    (hHP : H ≤ Subgroup.normalizer (P : Set G))
    (hPp : IsPGroup p P)
    (hnontriv : ⁅P, Subgroup.zpowers t⁆ ≠ ⊥)
    (hmin : ∀ R : Subgroup G, R ≤ P →
      H ≤ Subgroup.normalizer (R : Set G) →
      ⁅R, Subgroup.zpowers t⁆ ≠ ⊥ → P ≤ R) :
    P ⊓ Subgroup.normalizer (qCoreOf H p : Set G) = P ∧
      P ⊓ Subgroup.centralizer (qCoreOf H p : Set G) = P := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let O : Subgroup G := qCoreOf H p
  let Q : Subgroup G := Subgroup.zpowers t
  let K : Subgroup G := O ⊔ P
  let R : Subgroup G := P ⊓ Subgroup.normalizer (O : Set G)
  have hOleH : O ≤ H := by
    simpa [O] using qCoreOf_le H p
  have hOp : IsPGroup p O := by
    simpa [O] using qCoreOf_isPGroup H p
  have hHnormO : H ≤ Subgroup.normalizer (O : Set G) := by
    simpa [O] using le_normalizer_of_isNormalIn (qCoreOf_normal_in H p)
  have hOnormP : O ≤ Subgroup.normalizer (P : Set G) := hOleH.trans hHP
  have hKp : IsPGroup p K := by
    simpa [K] using IsPGroup.to_sup_of_normal_right' hOp hPp hOnormP
  have hKnil : Group.IsNilpotent K := hKp.isNilpotent
  let : Group.IsNilpotent K := hKnil
  have hKsolv : Group.IsSolvable K := by infer_instance
  have hPoddCard : Odd (Nat.card P) := by
    obtain ⟨n, hn⟩ := hPp.exists_card_eq
    rw [hn]
    exact hpodd.pow
  have hKoddCard : Odd (Nat.card K) := by
    obtain ⟨n, hn⟩ := hKp.exists_card_eq
    rw [hn]
    exact hpodd.pow
  have hQleH : Q ≤ H := by
    simpa [Q] using (Subgroup.zpowers_le.mpr htH)
  have hQnormO : Q ≤ Subgroup.normalizer (O : Set G) := hQleH.trans hHnormO
  have hQnormP : Q ≤ Subgroup.normalizer (P : Set G) := hQleH.trans hHP
  have hQnormK : Q ≤ Subgroup.normalizer (K : Set G) := by
    exact (le_inf hQnormO hQnormP).trans
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup O P)
  have hQcentO : Q ≤ Subgroup.centralizer (O : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro o ho
    rcases Subgroup.mem_zpowers_iff.mp hq with ⟨n, rfl⟩
    have hto : t * o = o * t :=
      (Subgroup.mem_centralizer_iff.mp (hHt (hOleH ho))) t (by simp)
    exact ((show Commute o t from hto.symm).zpow_right n).eq
  have htorder : orderOf t = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using ht.2) ht.1
  have hQcopK : Nat.Coprime (Nat.card Q) (Nat.card K) := by
    simpa [Q, Nat.card_zpowers, htorder] using hKoddCard.coprime_two_left
  have hPleK : P ≤ K := by
    dsimp [K]
    exact le_sup_right
  have hQnotCentK : ¬ Q ≤ Subgroup.centralizer (K : Set G) := by
    intro hQK
    have hQcentP : Q ≤ Subgroup.centralizer (P : Set G) :=
      hQK.trans (Subgroup.centralizer_le
        (show (P : Set G) ⊆ (K : Set G) from hPleK))
    have hPcentQ : P ≤ Subgroup.centralizer (Q : Set G) :=
      Subgroup.le_centralizer_iff.mp hQcentP
    exact hnontriv ((Subgroup.commutator_eq_bot_iff_le_centralizer).mpr (by
      simpa [Q] using hPcentQ))
  have hRleP : R ≤ P := inf_le_left
  have hRnormO : R ≤ Subgroup.normalizer (O : Set G) := inf_le_right
  have hORleK : O ⊔ R ≤ K := by
    exact sup_le le_sup_left (hRleP.trans le_sup_right)
  have hORsub : ((O ⊔ R).subgroupOf K).IsSubnormal :=
    isSubnormal_of_nilpotent hKnil (O ⊔ R) hORleK
  have hOleOR : O ≤ O ⊔ R := le_sup_left
  have hKcarrier : (K : Set G) = (O : Set G) * (P : Set G) := by
    simpa [K] using
      (Subgroup.coe_mul_of_left_le_normalizer_right O P hOnormP)
  have hORcarrier : ((O ⊔ R : Subgroup G) : Set G) =
      (K : Set G) ∩ (Subgroup.normalizer (O : Set G) : Set G) := by
    calc
      ((O ⊔ R : Subgroup G) : Set G) = (O : Set G) * (R : Set G) :=
        Subgroup.coe_mul_of_right_le_normalizer_left O R hRnormO
      _ = (O : Set G) * (P : Set G) ∩
          (Subgroup.normalizer (O : Set G) : Set G) := by
        simpa [R] using
          (Subgroup.mul_inf_assoc O P (Subgroup.normalizer (O : Set G))
            (Subgroup.le_normalizer : O ≤ Subgroup.normalizer (O : Set G)))
      _ = (K : Set G) ∩
          (Subgroup.normalizer (O : Set G) : Set G) := by rw [hKcarrier]
  have hORself :
      K ⊓ Subgroup.centralizer ((O ⊔ R : Subgroup G) : Set G) ≤ O ⊔ R := by
    intro x hx
    have hxCentO : x ∈ Subgroup.centralizer (O : Set G) :=
      (Subgroup.centralizer_le
        (show (O : Set G) ⊆ ((O ⊔ R : Subgroup G) : Set G) from hOleOR)) hx.2
    have hxNormO : x ∈ Subgroup.normalizer (O : Set G) :=
      Subgroup.centralizer_le_normalizer (O : Set G) hxCentO
    have hxInter : x ∈ (K : Set G) ∩
        (Subgroup.normalizer (O : Set G) : Set G) := ⟨hx.1, hxNormO⟩
    rw [← hORcarrier] at hxInter
    exact hxInter
  have hRQne : ⁅R, Q⁆ ≠ ⊥ :=
    commutator_right_ne_bot_of_sup_subnormal_selfCentralizing_coprime
      Q K O R hQnormK hORleK hORsub hORself hQcentO hQcopK hKsolv hQnotCentK
  have hHnormR : H ≤ Subgroup.normalizer (R : Set G) := by
    have hHnormNormO : H ≤
        Subgroup.normalizer (Subgroup.normalizer (O : Set G) : Set G) :=
      hHnormO.trans Subgroup.le_normalizer
    exact (le_inf hHP hHnormNormO).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := P)
        (K := Subgroup.normalizer (O : Set G)))
  have hPleR : P ≤ R := hmin R hRleP hHnormR (by simpa [Q] using hRQne)
  have hPnormO : P ≤ Subgroup.normalizer (O : Set G) := hPleR.trans hRnormO
  have hcomm : ⁅P, Q⁆ = P := by
    simpa [Q] using
      (commutator_zpowers_eq_self_of_minimal_invariant
        H P ht htH hHt hHP hPoddCard.coprime_two_left hnontriv hmin)
  have hQO : ⁅Q, O⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hQcentO
  have hOQ : ⁅O, Q⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact hQO
  have hOPleO : ⁅O, P⁆ ≤ O :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := P) (K := O)).1 hPnormO
  have h1 : ⁅⁅Q, O⁆, P⁆ = ⊥ := by simp [hQO]
  have h2 : ⁅⁅O, P⁆, Q⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (Subgroup.commutator_mono hOPleO le_rfl).trans (by simp [hOQ])
  have hrot : ⁅⁅P, Q⁆, O⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate
      (H₁ := P) (H₂ := Q) (H₃ := O) h1 h2
  have hPO : ⁅P, O⁆ = ⊥ := by simpa [hcomm] using hrot
  have hPcentO : P ≤ Subgroup.centralizer (O : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hPO
  constructor
  · simpa [O] using (inf_eq_left.mpr hPnormO)
  · simpa [O] using (inf_eq_left.mpr hPcentO)

end CFSG.GorensteinWalter
