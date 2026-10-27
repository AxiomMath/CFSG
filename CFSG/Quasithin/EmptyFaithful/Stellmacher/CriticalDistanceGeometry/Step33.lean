module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.S3Lines
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.ZvSupInf

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 CFSG.Quasithin.EmptyFaithful.Stellmacher

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

section Local

variable {α β α' : Geo H M}

theorem comm_le_Zv_nbr (hA : F53Amalgam H M S) (h113a : Hss113aAt H M) (hc : IsCritData α β α')
    (hv : vtype α = true) (hcomm : ⁅Zv α, Zv α'⁆ ≠ ⊥) (hz : Zv β ≤ centerOf (stab β)) :
    ⁅Zv α, Zv α'⁆ ≤ Zv β := by
  have hb := hc.bAt_eq
  have hcp : IsCritPair₁ α α' := ⟨hc.not_le, hc.dist_eq⟩
  obtain ⟨hbα', hZα'⟩ := Zv_le_stab_of_comm_ne hA hc hcomm
  have hZα'β : Zv α' ≤ stab β := by
    refine Zv_le_stab_of_dist_le hA ?_
    rw [CosetGeom.dist_comm, hbα']
    have := hc.dist_eq'
    omega
  have hf := zData_faithful hA hv hb
  have ht := zData_hasTransvection hA hv hb hcp hcomm h113a
  have hK : stab α ⊓ stab β ≤ stab α := inf_le_left
  have hcard := OrdinaryProofs.edge_image_card_two hA (psiAt_surj hA hv) (psiAt_ker hA hv)
    (show β ∈ nbrs α from hc.adj)
  obtain ⟨-, -, hcent⟩ := ZData.line_facts (D := zData hA hv) hf ht (K := stab α ⊓ stab β) hK hcard
  have hle : ⁅Zv α, Zv α'⁆ ≤ ⁅Zv α, stab α ⊓ stab β⁆ :=
    Subgroup.commutator_mono le_rfl (le_inf hZα' hZα'β)
  have h1 : ⁅Zv α, stab α ⊓ stab β⁆ ≤ Zv α := comm_Zv_le hA hK
  rw [← OrdinaryProofs.Zv_inf_centralizer_edge_eq hA hc.adj hz]
  exact le_inf (hle.trans h1) (hle.trans hcent)

theorem even_bMin_of_central (hA : F53Amalgam H M S) (hc : IsCritData α β α')
    (hv : vtype α = true) (hcomm : ⁅Zv α, Zv α'⁆ ≠ ⊥) (hz : Zv β ≤ centerOf (stab β)) :
    Even (bMin H M) := by
  by_contra hodd
  obtain ⟨hbα', hZα'⟩ := Zv_le_stab_of_comm_ne hA hc hcomm
  have hvβ : vtype β = false := by
    have := vtype_ne_of_adj hc.adj
    revert this; cases hvβ : vtype β <;> simp [hv]
  have hvα' : vtype α' = false := by
    by_contra h
    have h' : vtype α' = true := by simpa using h
    have : vtype α = vtype α' := by rw [hv, h']
    have heven := (vtype_eq_iff_even_dist hA.amalgam.gen α α').mp this
    rw [hc.dist_eq] at heven
    exact hodd heven
  have hZβ := Zv_eq_omegaOneCenter_of_central hA hz
  have hZα'c : Zv α' = quasithinOmegaOneCenter (stab α') :=
    Zv_central_of_conj hA (by rw [hvβ, hvα']) hZβ
  have h12 := centralizer_Zv_eq_Qv_of_bAt hA hbα'
  have hcen : stab α' ≤ Subgroup.centralizer (Zv α' : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hzz
    have hz' : z ∈ centerOf (stab α') := omegaOneCenter_le_centerOf_self _ (hZα'c ▸ hzz)
    exact ((Subgroup.mem_centralizer_iff.mp hz'.2) x hx).symm
  rw [inf_eq_left.mpr hcen] at h12
  exact pCoreOf_ne_stab hA α' h12.symm

theorem bMin_ne_four (hA : F53Amalgam H M S) (h32 : Hss32At H M) (h113a : Hss113aAt H M)
    (hc : IsCritData α β α') (hv : vtype α = true) (hcomm : ⁅Zv α, Zv α'⁆ ≠ ⊥) :
    bMin H M ≠ 4 := by
  intro h4
  have hz := h32 α β hc.adj hv hc.bAt_eq
  have heven := even_bMin_of_central hA hc hv hcomm hz
  obtain ⟨hbα', -⟩ := Zv_le_stab_of_comm_ne hA hc hcomm
  have hvα' : vtype α' = true := by
    have heven' : Even (dist α α') := by rw [hc.dist_eq]; exact heven
    have := (vtype_eq_iff_even_dist hA.amalgam.gen α α').mpr heven'
    rw [← this]; exact hv
  have hgen := hA.amalgam.gen
  have hdβα' : dist α' β = 3 := by
    have := hc.dist_eq'
    rw [CosetGeom.dist_comm]; omega
  obtain ⟨m, hβm, hdm⟩ := exists_adj_dist_eq hgen (α := α') (δ := β) (d := 2) hdβα'
  obtain ⟨β'', hmβ'', hdβ''⟩ := exists_adj_dist_eq hgen (α := α') (δ := m) (d := 1) hdm
  have hα'β'' : (graph (H ⊔ M) H M).Adj α' β'' := dist_eq_one_iff_adj.mp hdβ''
  have hαβ1 : dist α β = 1 := dist_eq_one_iff_adj.mpr hc.adj
  have hβm1 : dist β m = 1 := dist_eq_one_iff_adj.mpr hβm
  have hmβ1 : dist m β'' = 1 := dist_eq_one_iff_adj.mpr hmβ''
  have hα'α : dist α' α = 4 := by rw [CosetGeom.dist_comm, hc.dist_eq, h4]
  have hαβ''le : dist α β'' ≤ 3 := by
    have h1 := dist_triangle hgen α β m
    have h2 := dist_triangle hgen α m β''
    omega
  have hαβ''ge : 3 ≤ dist α β'' := by
    have h1 := dist_triangle hgen α β'' α'
    rw [CosetGeom.dist_comm β'' α'] at h1
    rw [CosetGeom.dist_comm α α'] at h1
    omega
  have hαα' : dist α α' = 4 := by rw [hc.dist_eq, h4]
  have hαm2 : dist α m = 2 := by
    have h1 := dist_triangle hgen α β m
    have h2 := dist_triangle hgen α m α'
    rw [CosetGeom.dist_comm m α'] at h2
    omega
  have hc' : IsCritData α' β'' α := by
    refine ⟨hα'β'', hbα', by rw [CosetGeom.dist_comm, hc.dist_eq], ?_,
      not_le_Qv_of_comm_ne hA hcomm⟩
    rw [CosetGeom.dist_comm]
    omega
  have hcomm' : ⁅Zv α', Zv α⁆ ≠ ⊥ := by rwa [Subgroup.commutator_comm]
  have hz'' := h32 α' β'' hα'β'' hvα' hbα'
  have hR1 := comm_le_Zv_nbr hA h113a hc hv hcomm hz
  have hR2 := comm_le_Zv_nbr hA h113a hc' hvα' hcomm' hz''
  rw [Subgroup.commutator_comm] at hR2
  have hvm : vtype m = true := by
    have := (vtype_eq_iff_even_dist hgen α m).mpr (by rw [hαm2]; exact even_two)
    rw [← this]; exact hv
  have hbm : bAt m = bMin H M := by rw [← hc.bAt_eq]; exact bAt_eq_of_vtype_eq (by rw [hv, hvm])
  have hne : β ≠ β'' := by
    rintro rfl
    omega
  obtain ⟨-, hinf⟩ := OrdinaryProofs.Zv_sup_eq_and_inf_eq_bot hA hvm hbm
    (show β ∈ nbrs m from hβm.symm) (show β'' ∈ nbrs m from hmβ'') hne hz
  exact hcomm (le_bot_iff.mp (hinf ▸ le_inf hR1 hR2))

end Local

variable {α β α' : Geo H M}

@[expose] def Hss33Step3At (H M : Subgroup G) : Prop :=
  Hss32At H M → ∀ α β α' : Geo H M, IsCritData α β α' → vtype α = true → ⁅Zv α, Zv α'⁆ ≠ ⊥ →
    6 ≤ bMin H M → Even (bMin H M) → False

theorem hss33At_of (hA : F53Amalgam H M S) (h32 : Hss32At H M) (h113a : Hss113aAt H M)
    (hM6 : NoA5Transvection) (h3 : Hss33Step3At H M) : Hss33At H M := by
  intro α β α' hc hv hcomm
  have h1 := one_lt_bMin_of_comm_ne hA h113a hM6 hc hv hcomm
  have hz := h32 α β hc.adj hv hc.bAt_eq
  have heven := even_bMin_of_central hA hc hv hcomm hz
  have h4 := bMin_ne_four hA h32 h113a hc hv hcomm
  by_contra hne
  obtain ⟨k, hk⟩ := heven
  exact h3 h32 α β α' hc hv hcomm (by omega) ⟨k, hk⟩

end F53.Stellmacher

end CFSG.Quasithin
