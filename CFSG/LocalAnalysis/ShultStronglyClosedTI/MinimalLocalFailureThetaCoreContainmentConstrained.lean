module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.TBS.TBS
public import CFSG.Assembly.Defs
public import CFSG.Foundations.Basic

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.ThetaCoreContainment

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem constrained_of_complement_quotient_characteristic_p
    {p : ℕ} [Fact p.Prime]
    (hchar : CFSG.IsCharacteristicP p (G ⧸ CFSG.pPrimeCore p G)) :
    CFSG.PConstrainedGroup (G := G) p := by
  let R := CFSG.pPrimeCore p G
  let q := QuotientGroup.mk' R
  intro Q _hQ hcover
  have hRmap : R.map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff (f := q) R).mpr
    rw [QuotientGroup.ker_mk']
  have hOmap : (CFSG.Op_p'p p G).map q = CFSG.pCore p (G ⧸ R) := by
    change (Subgroup.comap q (CFSG.pCore p (G ⧸ R))).map q = _
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective R) _
  have hQmap : Q.map q = CFSG.pCore p (G ⧸ R) := by
    have hm := congrArg (Subgroup.map q) hcover
    change (R ⊔ Q).map q = (CFSG.Op_p'p p G).map q at hm
    rw [Subgroup.map_sup, hRmap, bot_sup_eq, hOmap] at hm
    exact hm
  intro x hx
  change q x ∈ CFSG.pCore p (G ⧸ R)
  apply hchar
  rw [← hQmap]
  apply Subgroup.mem_centralizer_iff.mpr
  rintro y ⟨a, ha, rfl⟩
  exact (by simpa only [map_mul] using
    congrArg q ((Subgroup.mem_centralizer_iff.mp hx) a ha))

theorem thompson_bender_core_of_characteristic_quotient
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hchar : CFSG.IsCharacteristicP p (G ⧸ CFSG.pPrimeCore p G))
    (P : Subgroup G) (hP : IsPGroup p P)
    (hcentral : ∀ x : G, x ∈ Subgroup.centralizer (P : Set G) →
      orderOf x = p → x ∈ P)
    (W : Subgroup G) (hWcop : Nat.Coprime p (Nat.card W))
    (hPW : P ≤ Subgroup.normalizer (W : Set G)) :
    W ≤ CFSG.pPrimeCore p G := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  have hcop : Nat.Coprime (Nat.card W) (Nat.card P) := by
    rw [hn]
    exact hWcop.symm.pow_right n
  have hinf : W ⊓ P = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hpne : p ≠ 2 := by
    intro hp2
    rw [hp2] at hpodd
    exact (by decide : ¬ Odd 2) hpodd
  exact CFSG.thompson_bender_signalizer_lemma hpne
    (constrained_of_complement_quotient_characteristic_p hchar) hP hcentral hPW hinf

end CFSG.ShultStronglyClosedTI.ThetaCoreContainment
