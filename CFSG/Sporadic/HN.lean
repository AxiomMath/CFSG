
module

public import CFSG.Sporadic.HNBase

public import CFSG.Sporadic.HN.Commutant
public import CFSG.Sporadic.HN.CoprimeSimple
public import CFSG.Sporadic.HN.Certificate
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Sporadic.HN.F5Group
public import CFSG.Sporadic.HN.F5Chain

public section

namespace CFSG.Sporadic.HN

open CFSG.Blueprint CFSG.Sporadic.F5 CFSG.Sporadic.F5.Native

noncomputable def hnSeedEquiv : NativeSporadic.HN ≃* J Native.hnData :=
  seedEquiv' (by decide) hn_certificate.1 hn_certificate.2.1

theorem card_HN : Nat.card NativeSporadic.HN = 273030912000000 := by
  rw [Nat.card_congr hnSeedEquiv.toEquiv]
  exact hn_certificate.2.2.2.2.1

theorem isSimpleGroup_HN : IsSimpleGroup NativeSporadic.HN := by
  obtain ⟨g, hg⟩ := hn_certificate.2.2.1
  have hJ : IsSimpleGroup (J Native.hnData) :=
    simple_of_facts hn_certificate.1 hn_certificate.2.1 hg (by decide) hn_certificate.2.2.2.1
      hn_certificate.2.2.2.2.1
  exact @MulEquiv.isSimpleGroup _ _ _ _ hJ hnSeedEquiv

theorem fam_hn_simplicity :
    Finite NativeSporadic.HN ∧ Nontrivial NativeSporadic.HN ∧
    IsSimpleGroup NativeSporadic.HN := by
  have hs := isSimpleGroup_HN
  refine ⟨Nat.finite_of_card_ne_zero (by rw [card_HN]; norm_num), inferInstance, hs⟩

end CFSG.Sporadic.HN
