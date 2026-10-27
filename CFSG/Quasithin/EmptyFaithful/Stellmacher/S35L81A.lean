module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35L81Base
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35G7B
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits

namespace F53.Stellmacher

open CosetGeom F53 Equiv
open CFSG.Quasithin.F53.Stellmacher.S43.Even
open scoped commutatorElement

namespace S35.L81

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem not_comm_le_E0 (hS : Sit H M S) (hII : CaseII H M) (h6 : Claim6b H M) {β : Geo H M}
    (hβ : vtype β = false) (hs : IsSec (stab β) (Vn β) (Wb β)) :
    ¬ ⁅Wb β, oTwoRes (stab β)⁆ ≤ S35.G7.B.E0 β := by
  intro h
  have hWV : ⁅Wb β, oTwoRes (stab β)⁆ ≤ Vn β :=
    comm_oTwoRes_le_trans hs h (S35.G7.B.comm_E0_le hS β)
  obtain ⟨l, hl, δ, hδl, hδne⟩ := S35.C56.exists_arc hS hβ
  have hlδ : l ∈ nbrs δ := Std.mem_nbrs_symm.mp hδl
  have h1 := h6 β l δ (Wb β) hβ hl hlδ hδne (Std.Wb_normal β) (Std.Vn_le_Wb_self hS hβ) le_rfl hWV
  have hd : dist δ β = 2 := Std.dist_eq_two_iff.mpr ⟨l, hl, hδl, hδne⟩
  have h2 : Vn δ ≤ Vn β := by
    have : Vn δ ≤ Vn δ ⊓ Wb β := le_inf le_rfl (Std.Vn_le_Wb hd)
    rw [h1] at this
    exact this.trans inf_le_right
  have h3 := relIndex_ge_eight hS hII hβ hl hlδ hδne
  rw [inf_eq_left.mpr h2, Subgroup.relIndex_self] at h3
  omega

theorem lem81II (hS : Sit H M S) (hII : CaseII H M) (h5 : Claim5b H M) (h6 : Claim6b H M) :
    S35.II.Lem81II H M := by
  intro β hβ hs y hy hyQ hidx
  have hq := S35.C56.quot_five hS hβ
  have hnW : Wb β ≤ stab β := S35.G7.B.Wb_le_stab' hS β
  have hnV : Wb β ≤ Subgroup.normalizer (Vn β : Set G) := S35.G7.B.Wb_le_normalizer_Vn hS β
  have hnE : stab β ≤ Subgroup.normalizer (S35.G7.B.E0 β : Set G) := S35.G7.B.E0_normal hS β
  have hVE : Vn β ≤ S35.G7.B.E0 β := S35.G7.B.Vn_le_E0 hS hβ
  have hEW : S35.G7.B.E0 β ≤ Wb β := S35.G7.B.E0_le_Wb hS β
  have hsE : IsSec (stab β) (S35.G7.B.E0 β) (Wb β) := EvenMod.isSec_of_ge hs hVE hEW hnE
  have hnot := not_comm_le_E0 hS hII h6 hβ hs
  obtain ⟨E', F', hEE', hF'W, hstep, hnc⟩ := exists_noncentral_of_not_le
    (X := stab β) (U := pCoreOf 2 (stab β)) hsE (Std.Wb_le_Qv hS β) hnot
  have h2 : secIdx (Subgroup.zpowers y) (S35.G7.B.E0 β) (Wb β) ≤ 2 := by
    refine (EvenMod.secIdx_le_secIdx hnW (Std.Vn_normal β) hnE (Std.Wb_normal β) hVE hEW le_rfl
      hy).trans ?_
    exact hidx.le
  obtain ⟨horth, hidx', -, -, hE'L, hWF'⟩ := S11_chief hq le_rfl (Std.Wb_le_Qv hS β) hsE hEE'
    hF'W hstep hnc hy hyQ h2
  have hE'W : E' ≤ Wb β := hstep.2.2.1.le.trans hF'W
  have hnE' : stab β ≤ Subgroup.normalizer (E' : Set G) :=
    EvenMod.le_normalizer_of_isNormalIn hstep.2.1
  have hsE' : IsSec (stab β) (Vn β) E' := EvenMod.isSec_of_le hs (hVE.trans hEE') hE'W hnE'
  have hE'V : ⁅E', oTwoRes (stab β)⁆ ≤ Vn β :=
    comm_oTwoRes_le_trans hsE' hE'L (S35.G7.B.comm_E0_le hS β)
  have hE'E : E' ≤ S35.G7.B.E0 β := fun e he =>
    (S35.G7.B.mem_E0_iff hS β).mpr
      ⟨hE'W he, fun a ha => EvenMod.commutator_le_iff.mp hE'V a ha e he⟩
  have hEeq : E' = S35.G7.B.E0 β := le_antisymm hE'E hEE'
  subst hEeq
  have hFW : F' = Wb β := by
    refine le_antisymm hF'W (Std.Wb_le fun ρ hρ => ?_)
    obtain ⟨l, hl, hρl, hρne⟩ := Std.dist_eq_two_iff.mp hρ
    have hρW : Vn ρ ≤ Wb β := Std.Vn_le_Wb hρ
    have hnF : stab β ≤ Subgroup.normalizer (F' : Set G) :=
      EvenMod.le_normalizer_of_isNormalIn hstep.1
    refine h5 β l ρ (S35.G7.B.E0 β) F' (Vn ρ) hβ hl (Std.mem_nbrs_symm.mp hρl) hρne hnE hnF
      hVE hstep.2.2.1.le hF'W horth (fun w hw h => S35.G7.B.mem_E0_of_central hS hs hβ hw h)
      le_rfl ?_ ?_
    · exact (Std.Qv_le_stab hS hρl).trans (Std.Vn_normal ρ)
    · exact (Subgroup.commutator_mono hρW le_rfl).trans hWF'
  subst hFW
  refine ⟨S35.G7.B.E0 β, hnE, hVE, hEW, S35.G7.B.comm_E0_le hS β, horth, ?_, hidx'⟩
  have hm := S43.secIdx_mul_le (x := y) hVE hEW hnV (hnW.trans hnE) (Std.Vn_normal β hy) (hnE hy)
  have hp := S43.secIdx_pos (Subgroup.zpowers y) (Vn β) (S35.G7.B.E0 β)
  rw [hidx', hidx] at hm
  omega

end S35.L81

end F53.Stellmacher

end CFSG.Quasithin
