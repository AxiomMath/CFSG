module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35G7Stmt
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C56Irr
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43EvenModChief

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits

namespace F53.Stellmacher

open CosetGeom F53 Equiv
open CFSG.Quasithin.F53.Stellmacher.S43.Even
open scoped commutatorElement

namespace S35.G7.B

variable {G : Type} [Group G]

theorem conj_mem' {X S : Subgroup G} (h : X ≤ Subgroup.normalizer (S : Set G)) {g s : G}
    (hg : g ∈ X) (hs : s ∈ S) : g * s * g⁻¹ ∈ S :=
  (Subgroup.mem_normalizer_iff.mp (h hg) s).mp hs

theorem conj_inv_mem {X S : Subgroup G} (h : X ≤ Subgroup.normalizer (S : Set G)) {g s : G}
    (hg : g ∈ X) (hs : s ∈ S) : g⁻¹ * s * g ∈ S := by
  have := (Subgroup.mem_normalizer_iff.mp (h (X.inv_mem hg)) s).mp hs
  simpa using this

theorem normalizer_fixSecIn {X A V W : Subgroup G}
    (hV : X ≤ Subgroup.normalizer (V : Set G)) (hW : X ≤ Subgroup.normalizer (W : Set G))
    (hA : X ≤ Subgroup.normalizer (A : Set G)) (hWV : W ≤ Subgroup.normalizer (V : Set G)) :
    X ≤ Subgroup.normalizer (fixSecIn A V W : Set G) := by
  have key : ∀ g ∈ X, ∀ x ∈ fixSecIn A V W, g * x * g⁻¹ ∈ fixSecIn A V W := by
    intro g hg x hx
    rw [mem_fixSecIn_iff hWV] at hx ⊢
    refine ⟨conj_mem' hW hg hx.1, fun a ha => ?_⟩
    have h1 := conj_mem' hV hg (hx.2 (g⁻¹ * a * g) (conj_inv_mem hA hg ha))
    convert h1 using 1
    group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key g hg h hh, fun hh => ?_⟩
  have := key g⁻¹ (X.inv_mem hg) _ hh
  convert this using 1
  group

variable [Finite G] {H M S : Subgroup G}

@[expose] noncomputable def E0 (β : Geo H M) : Subgroup G :=
  fixSecIn (oTwoRes (stab β)) (Vn β) (Wb β)

variable (hS : Sit H M S)
include hS

theorem Wb_le_stab' (β : Geo H M) : Wb β ≤ stab β :=
  (Std.Wb_le_Qv hS β).trans (pCoreOf_le 2 _)

theorem Wb_le_normalizer_Vn (β : Geo H M) : Wb β ≤ Subgroup.normalizer (Vn β : Set G) :=
  (Wb_le_stab' hS β).trans (Std.Vn_normal β)

theorem mem_E0_iff (β : Geo H M) {x : G} :
    x ∈ E0 β ↔ x ∈ Wb β ∧ ∀ a ∈ oTwoRes (stab β), a * x * a⁻¹ * x⁻¹ ∈ Vn β :=
  mem_fixSecIn_iff (Wb_le_normalizer_Vn hS β)

theorem E0_le_Wb (β : Geo H M) : E0 β ≤ Wb β := fun _ hx => ((mem_E0_iff hS β).mp hx).1

theorem E0_normal (β : Geo H M) : stab β ≤ Subgroup.normalizer (E0 β : Set G) :=
  normalizer_fixSecIn (Std.Vn_normal β) (Std.Wb_normal β) (le_normalizer_oTwoRes _)
    (Wb_le_normalizer_Vn hS β)

theorem Vn_le_E0 {β : Geo H M} (hβ : vtype β = false) : Vn β ≤ E0 β := by
  intro v hv
  refine (mem_E0_iff hS β).mpr ⟨Std.Vn_le_Wb_self hS hβ hv, fun a ha => ?_⟩
  have h1 := conj_mem' (Std.Vn_normal β) (oTwoRes_le _ ha) hv
  have e : a * v * a⁻¹ * v⁻¹ = (a * v * a⁻¹) * v⁻¹ := rfl
  rw [e]
  exact (Vn β).mul_mem h1 ((Vn β).inv_mem hv)

theorem comm_E0_le (β : Geo H M) : ⁅E0 β, oTwoRes (stab β)⁆ ≤ Vn β :=
  EvenMod.commutator_le_iff.mpr fun q hq _ hy => ((mem_E0_iff hS β).mp hy).2 q hq

theorem not_comm_le_E0 (hI : CaseI H M) (h6 : Claim6b H M) {β : Geo H M} (hβ : vtype β = false)
    (hs : IsSec (stab β) (Vn β) (Wb β)) : ¬ ⁅Wb β, oTwoRes (stab β)⁆ ≤ E0 β := by
  intro h
  have hWV : ⁅Wb β, oTwoRes (stab β)⁆ ≤ Vn β :=
    comm_oTwoRes_le_trans hs h (comm_E0_le hS β)
  obtain ⟨l, hl, δ, hδl, hδne⟩ := C56.exists_arc hS hβ
  have hlt : vtype l = true := Std.vtype_nbr_S5 hβ hl
  have hδ0 : vtype δ = false := Std.vtype_nbr_S3 hlt hδl
  have hlδ : l ∈ nbrs δ := Std.mem_nbrs_symm.mp hδl
  have h1 := h6 β l δ (Wb β) hβ hl hlδ hδne (Std.Wb_normal β) (Std.Vn_le_Wb_self hS hβ) le_rfl hWV
  have hd : dist δ β = 2 := Std.dist_eq_two_iff.mpr ⟨l, hl, hδl, hδne⟩
  have h2 : Vn δ ≤ Vn β := by
    have : Vn δ ≤ Vn δ ⊓ Wb β := le_inf le_rfl (Std.Vn_le_Wb hd)
    rw [h1] at this
    exact this.trans inf_le_right
  obtain ⟨hc8, hc32⟩ := hI δ l β hδ0 hlδ hl hδne.symm
  have : Vn δ ⊓ Vn β = Vn δ := inf_eq_left.mpr h2
  rw [this] at hc8
  omega


theorem mem_E0_of_central {β : Geo H M} (hs : IsSec (stab β) (Vn β) (Wb β)) (hβ : vtype β = false)
    {w : G} (hw : w ∈ Wb β) (h : ∀ g ∈ stab β, g * w * g⁻¹ * w⁻¹ ∈ E0 β) : w ∈ E0 β := by
  have hWE : Wb β ≤ Subgroup.normalizer (E0 β : Set G) := (Wb_le_stab' hS β).trans (E0_normal hS β)
  set N1 := fixSecIn (stab β) (E0 β) (Wb β) with hN1
  have hmem : ∀ x, x ∈ N1 ↔ x ∈ Wb β ∧ ∀ a ∈ stab β, a * x * a⁻¹ * x⁻¹ ∈ E0 β :=
    fun x => mem_fixSecIn_iff hWE
  have hnorm : stab β ≤ Subgroup.normalizer (N1 : Set G) :=
    normalizer_fixSecIn (E0_normal hS β) (Std.Wb_normal β) (Subgroup.le_normalizer)
      hWE
  have hE0N1 : E0 β ≤ N1 := by
    intro e he
    refine (hmem e).mpr ⟨E0_le_Wb hS β he, fun a ha => ?_⟩
    have h1 := conj_mem' (E0_normal hS β) ha he
    have e' : a * e * a⁻¹ * e⁻¹ = (a * e * a⁻¹) * e⁻¹ := rfl
    rw [e']
    exact (E0 β).mul_mem h1 ((E0 β).inv_mem he)
  have hN1W : N1 ≤ Wb β := fun x hx => ((hmem x).mp hx).1
  have hsN1 : IsSec (stab β) (Vn β) N1 :=
    EvenMod.isSec_of_le hs ((Vn_le_E0 hS hβ).trans hE0N1) hN1W hnorm
  have hcomm : ⁅N1, oTwoRes (stab β)⁆ ≤ Vn β := by
    refine comm_oTwoRes_le_trans hsN1 (K := E0 β) ?_ (comm_E0_le hS β)
    exact EvenMod.commutator_le_iff.mpr fun q hq y hy => ((hmem y).mp hy).2 q (oTwoRes_le _ hq)
  refine (mem_E0_iff hS β).mpr ⟨hw, fun a ha => ?_⟩
  exact EvenMod.commutator_le_iff.mp hcomm a ha w ((hmem w).mpr ⟨hw, h⟩)

end S35.G7.B

namespace S35.G7

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem lem81 : Lem81 H M S := by
  unfold Lem81
  intro hS hI h5 h6 β hβ hs y hy hyQ hidx
  have hq := C56.quot_five hS hβ
  have hnW : Wb β ≤ stab β := B.Wb_le_stab' hS β
  have hnV : Wb β ≤ Subgroup.normalizer (Vn β : Set G) := B.Wb_le_normalizer_Vn hS β
  have hnE : stab β ≤ Subgroup.normalizer (B.E0 β : Set G) := B.E0_normal hS β
  have hVE : Vn β ≤ B.E0 β := B.Vn_le_E0 hS hβ
  have hEW : B.E0 β ≤ Wb β := B.E0_le_Wb hS β
  have hsE : IsSec (stab β) (B.E0 β) (Wb β) := EvenMod.isSec_of_ge hs hVE hEW hnE
  have hnot := B.not_comm_le_E0 hS hI h6 hβ hs
  obtain ⟨E', F', hEE', hF'W, hstep, hnc⟩ := exists_noncentral_of_not_le
    (X := stab β) (U := pCoreOf 2 (stab β)) hsE (Std.Wb_le_Qv hS β) hnot
  have h2 : secIdx (Subgroup.zpowers y) (B.E0 β) (Wb β) ≤ 2 := by
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
    comm_oTwoRes_le_trans hsE' hE'L (B.comm_E0_le hS β)
  have hE'E : E' ≤ B.E0 β := fun e he =>
    (B.mem_E0_iff hS β).mpr ⟨hE'W he, fun a ha => EvenMod.commutator_le_iff.mp hE'V a ha e he⟩
  have hEeq : E' = B.E0 β := le_antisymm hE'E hEE'
  subst hEeq
  have hFW : F' = Wb β := by
    refine le_antisymm hF'W (Std.Wb_le fun ρ hρ => ?_)
    obtain ⟨l, hl, hρl, hρne⟩ := Std.dist_eq_two_iff.mp hρ
    have hρW : Vn ρ ≤ Wb β := Std.Vn_le_Wb hρ
    have hnF : stab β ≤ Subgroup.normalizer (F' : Set G) :=
      EvenMod.le_normalizer_of_isNormalIn hstep.1
    refine h5 β l ρ (B.E0 β) F' (Vn ρ) hβ hl (Std.mem_nbrs_symm.mp hρl) hρne hnE hnF hVE
      hstep.2.2.1.le hF'W horth (fun w hw h => B.mem_E0_of_central hS hs hβ hw h) le_rfl ?_ ?_
    · exact (Std.Qv_le_stab hS hρl).trans (Std.Vn_normal ρ)
    · exact (Subgroup.commutator_mono hρW le_rfl).trans hWF'
  subst hFW
  refine ⟨B.E0 β, hnE, hVE, hEW, B.comm_E0_le hS β, horth, ?_, hidx'⟩
  have hm := S43.secIdx_mul_le (x := y) hVE hEW hnV (hnW.trans hnE) (Std.Vn_normal β hy) (hnE hy)
  have hp := S43.secIdx_pos (Subgroup.zpowers y) (Vn β) (B.E0 β)
  rw [hidx', hidx] at hm
  omega

end S35.G7

end F53.Stellmacher

end CFSG.Quasithin
