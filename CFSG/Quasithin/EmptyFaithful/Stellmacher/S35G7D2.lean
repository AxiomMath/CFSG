module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35G7D1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChZl
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35G7Stmt
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.G7.D

open S35.Fin

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem exists_not_mem_zpowers_vp :
    ∀ σ : Perm (Fin 5), σ ≠ 1 → ∀ p : Fin 5, ∃ w : orth.W,
      w * (orth.act σ w)⁻¹ ≠ 1 ∧ w * (orth.act σ w)⁻¹ ≠ vp p := by
  set_option maxRecDepth 100000 in decide +kernel

theorem false_of_comm_le_Zv (hS : Sit H M S) (hZ : HypZ H M) {β m : Geo H M}
    (hβ : vtype β = false) (hm : m ∈ nbrs β) {x : G} (hx : x ∈ stab β) (hxQ : x ∉ Qv β)
    (h : ∀ v ∈ Vn β, ⁅v, x⁆ ∈ Zv m) : False := by
  obtain ⟨c⟩ := Ch.nonempty_chart (S34.Zv_le_Vn hS.glob hβ) (hZ β hβ)
  have hσ : c.θ ⟨x, hx⟩ ≠ 1 := fun h1 => hxQ ((c.ker_iff hS hβ ⟨x, hx⟩).mp h1)
  have himg := c.img_Zv_nbr hS hβ hm
  obtain ⟨w, hw1, hw2⟩ := exists_not_mem_zpowers_vp _ hσ (fixPt (c.Dl m))
  obtain ⟨v, rfl⟩ := c.π_surj w
  have hz : ((v * (Ch.conjV ⟨x, hx⟩ v)⁻¹ : ↥(Vn β)) : G) ∈ Zv m := by
    have : ((v * (Ch.conjV ⟨x, hx⟩ v)⁻¹ : ↥(Vn β)) : G) = ⁅(v : G), x⁆ := by
      simp [Ch.coe_conjV, commutatorElement_def, mul_assoc]
    rw [this]
    exact h v v.2
  have hin : c.π (v * (Ch.conjV ⟨x, hx⟩ v)⁻¹) ∈ c.img (Zv m) :=
    (c.mem_img_iff').mpr ⟨_, hz, rfl⟩
  rw [himg, map_mul, map_inv, c.π_conj, mem_zpowers_iff_of_mul_self (vp_mul_self _)] at hin
  exact hin.elim hw1 hw2

theorem exists_path (hS : Sit H M S) {β α' : Geo H M} (hp : S34.PD β α') :
    ∃ m γ μ : Geo H M, m ∈ nbrs β ∧ γ ∈ nbrs m ∧ μ ∈ nbrs γ ∧ dist γ α' + 3 = bMin H M ∧
      dist μ α' + 4 = bMin H M ∧ vtype γ = false ∧ dist γ β = 2 := by
  have hd := hp.dist_eq
  have hb := hS.b5
  obtain ⟨m, hm, hdm⟩ := Std.exists_nbr_dist_succ (δ := β) (ρ := α')
    (d := dist β α' - 1) (by omega)
  obtain ⟨γ, hγ, hdγ⟩ := Std.exists_nbr_dist_succ (δ := m) (ρ := α') (d := dist β α' - 2)
    (by omega)
  obtain ⟨μ, hμ, hdμ⟩ := Std.exists_nbr_dist_succ (δ := γ) (ρ := α') (d := dist β α' - 3)
    (by omega)
  have hne : γ ≠ β := by
    rintro rfl
    omega
  refine ⟨m, γ, μ, hm, hγ, hμ, by omega, by omega, ?_, Std.dist_eq_two_iff.mpr ⟨m, hm, hγ, hne⟩⟩
  rw [← Std.vtype_eq_of_nbrs (Std.mem_nbrs_symm.mp hm) hγ]
  exact hp.vδ

theorem claim7s_of_pm (hS : Sit H M S) (hZ : HypZ H M) (h15c : Claim15c H M)
    (h16d : Claim16d H M) (hPM : PM H M) : Claim7s H M := by
  intro β α' hp x hxα hxQ hs h2
  obtain ⟨m, γ, μ, hm, hγm, hμγ, hdγ, hdμ, hvγ, hγβ⟩ := exists_path hS hp
  have hvβ : vtype β = false := hp.vδ
  have hxβ : x ∈ stab β := (Std.PD_Vn_le_stab hS hp).2 hxα
  have hxQγ : x ∈ Qv γ :=
    Std.Vn_le_Qv_dist hS (δ := α') (ρ := γ) (by rw [CosetGeom.dist_comm]; omega) hxα
  have hcomm : ∀ v ∈ Vn γ, x * v = v * x := fun v hv =>
    Std.Vn_commute_dist hS (δ := α') (ρ := γ) (by rw [CosetGeom.dist_comm]; omega) x hxα v hv
  have hxK : x ∈ Kb γ :=
    ⟨hxQγ, Subgroup.mem_centralizer_iff.mpr fun v hv => (hcomm v hv).symm⟩
  have hxγ : x ∈ stab γ := Ch.Qv_le_stab' γ hxQγ
  obtain ⟨g, hg⟩ := exists_smul_of_vtype_eq (δ := β) (δ' := γ) (hvβ.trans hvγ.symm)
  obtain ⟨hs', hy, hyQ, hy2⟩ := transv_smul g hs hxβ hxQ h2
  rw [← hg] at hs' hy hyQ hy2
  have hWμ : ∀ w ∈ Wl μ, ⁅w, x⁆ = 1 := by
    have hle : Wl μ ≤ Subgroup.centralizer ({x} : Set G) := by
      refine iSup₂_le fun ρ hρ => ?_
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have hd : dist α' ρ + 3 ≤ bMin H M := by
        have h1 := dist_le_dist_nbr hρ α'
        rw [CosetGeom.dist_comm α' μ] at h1
        omega
      exact Std.Vn_commute_dist hS hd h hxα v hv
    intro w hw
    have := Subgroup.mem_centralizer_iff.mp (hle hw) x rfl
    rw [commutatorElement_def, ← this]
    group
  have hres := hPM γ hvγ hs' _ hy hyQ hy2 x hxγ
    (fun v hv => by rw [commutatorElement_def, hcomm v hv]; group)
    (fun w hw => h15c γ hvγ (Subgroup.commutator_mem_commutator hw hxK))
    (fun μ' hμ' δ hδ hne v hv => h16d γ μ' δ hvγ hμ' hδ hne x hxK v hv) ⟨μ, hμγ, hWμ⟩
  refine false_of_comm_le_Zv hS hZ hvβ hm hxβ hxQ fun v hv => ?_
  have hvW : v ∈ Wb γ := Std.Vn_le_Wb (by rw [CosetGeom.dist_comm]; exact hγβ) hv
  exact Std.Zv_le_Zv_of_nbr hS hvγ (Std.mem_nbrs_symm.mp hγm) (hres v hvW)

end S35.G7.D

end F53.Stellmacher

end CFSG.Quasithin
