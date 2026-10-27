module

public import CFSG.Timmesfeld.Bridge.OddRootDefs
import CFSG.Timmesfeld.Bridge.OddRootBasic
import CFSG.Timmesfeld.Bridge.OddRootSqOut
import CFSG.Timmesfeld.Bridge.OddLocalMain

public section

namespace CFSG.Timmesfeld.Bridge.OddRoot

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
  CFSG.Timmesfeld.Bridge.OddLocal CFSG.BenderSuzuki

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem psl2Pair_of_not_sqOut
    (h : Hyp G D) {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x)
    (hno : ¬ SqOut ↥(rootGen D d x)) : PSL2Pair D d x := by
  rcases rootGen_quotient_bender_or_dihedral h.setup.oddT h.setup.normal hd hx hdx with
    ⟨n, hn, he⟩ | ⟨n, hn, he⟩ | hdih
  · obtain ⟨e⟩ := he
    exact ⟨n, hn, ⟨e⟩⟩
  · obtain ⟨e⟩ := he
    exact absurd (sqOut_of_sz n e) hno
  · dsimp only at hdih
    obtain ⟨-, hd2, -, -, -, hE⟩ := hdih
    exfalso
    have hD := h.setup.oddT
    obtain ⟨v, hv, -, hdv⟩ := exists_rootSet_triple h.setup h.sq hd
    let X' := rootGen D d x
    let Q' := CFSG.pCore 2 X'
    let π : X' →* X' ⧸ Q' := QuotientGroup.mk' Q'
    have hdvQ : d * v ∈ Q'.map X'.subtype := by
      have h1 := hE v hv
      rw [hD.inv_eq hv.1] at h1
      rwa [(commute_of_mem_rootSet hd hv (mem_rootSet_self hd)).eq] at h1
    have hvQ : v ∈ Q'.map X'.subtype := by
      have h1 := hE (d * v) hdv
      have hval : (d * v)⁻¹ * d = v := by
        rw [mul_inv_rev, hD.inv_eq hv.1, hD.inv_eq hd, mul_assoc,
          hD.mul_self_eq_one hd, mul_one]
      rwa [hval] at h1
    have hdQ : d ∈ Q'.map X'.subtype := by
      have h1 : (d * v) * v ∈ Q'.map X'.subtype :=
        (Q'.map X'.subtype).mul_mem hdvQ hvQ
      rwa [mul_assoc, hD.mul_self_eq_one hv.1, mul_one] at h1
    have hdsub : (⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩ : X') ∈ Q' := by
      obtain ⟨q, hq, hqeq⟩ := Subgroup.mem_map.mp hdQ
      have hq' : (⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩ : X') = q := by
        ext
        simpa using hqeq.symm
      rwa [hq']
    have hone : π ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩ = 1 :=
      (QuotientGroup.eq_one_iff (N := Q') _).mpr hdsub
    rw [hone] at hd2
    exact absurd hd2 (by simp)

end CFSG.Timmesfeld.Bridge.OddRoot
