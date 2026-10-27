module

public import CFSG.LocalAnalysis.WeakClosure81.SevenNineCore
public import CFSG.LocalAnalysis.WeakClosure81.SevenNineAct

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {V H E J : Subgroup G}

theorem seven_nine_in (hIn : OrthReflParabolic) (h : Hyp73 V H E J) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) J φ) {L : Subgroup X}
    (hVL : barSub (kSub V H E) φ V ≤ L)
    (hL : IsSevenNineGroup ↥L {x : ↥L | (x : X) ∈ barSub (kSub V H E) φ V ∧ x ≠ 1}) : False := by
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  obtain ⟨_, -, -, hVnotle⟩ := mem_omegaSet.mp h.mem
  obtain ⟨v, hvV, hvO⟩ := SetLike.not_le_iff_exists.mp hVnotle
  have hvJ : v ∉ J := fun hvJ => hvO (h.pcore_le hvJ)
  have hS : barSub (kSub V H E) φ V ≠ ⊥ := by
    intro hbot
    have hmem : φ ⟨v, le_kSub h.mem hvV⟩ ∈ barSub (kSub V H E) φ V :=
      mem_barSub.mpr ⟨⟨v, le_kSub h.mem hvV⟩, hvV, rfl⟩
    rw [hbot] at hmem
    exact hvJ ((hφ.ker_iff ⟨v, le_kSub h.mem hvV⟩).mp (Subgroup.mem_bot.mp hmem))
  obtain ⟨p, Yb, Zb, hc⟩ := hIn X L (barSub (kSub V H E) φ V) hVL hS hL
  haveI : Fact p.Prime := ⟨hc.prime⟩
  obtain ⟨P, hP⟩ := exists_sevenNineCompl h hφ hc hvV hvJ
  have hI : IsElemAbelian 2 (iSub V H E) :=
    seven_two_iSub_isElemAbelian_uncond h.elemAbelian h.ti h.abelian h.omega_le
  have hIleH : iSub V H E ≤ H :=
    h.iSub_le.trans (h.pcore_le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H))
  have hInorm : ((iSub V H E).subgroupOf H).Normal := iSub_subgroupOf_normal h.le h.normal
  have hPI : P ≤ Subgroup.normalizer (iSub V H E : Set G) :=
    hP.le.trans ((barPre_le (kSub V H E) φ Yb).trans
      ((kSub_le_of_forall_le h.omega_le).trans
        (le_normalizer_of_subgroupOf_normal hIleH hInorm)))
  have htI : v ∈ Subgroup.normalizer (iSub V H E : Set G) :=
    le_normalizer_of_subgroupOf_normal hIleH hInorm (h.omega_le V h.mem hvV)
  exact seven_nine_core (I := iSub V H E) (Z := P ⊓ Subgroup.centralizer ({v} : Set G))
    (t := v) hc.ne_two hI (SevenNineCompl.isElemAbelian hφ hc hP) hPI
    (SevenNineCompl.commutator_iSub_ne_bot h hφ hc hvV hvJ hP) htI hP.mem_normalizer
    inf_le_left inf_le_right (SevenNineCompl.card_inf_centralizer h hφ hc hvV hvJ hP)
    (SevenNineCompl.commutator_iSub_le_centralizer h hφ hc hvV hvJ hP)
    (fun B hB hBcard => SevenNineCompl.exists_conj h hφ hc hvV hvJ hP hB hBcard)

end CFSG.LocalAnalysis.WeakClosure81
