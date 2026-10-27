module

public import CFSG.Quasithin.Background.F918Z6Aux
public import CFSG.Quasithin.Background.F918Z6Irr
public import CFSG.Quasithin.Background.F918J2
public import CFSG.Quasithin.Background.F918J3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

structure D37Cfg {W : Type} [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W))
    (V : Subgroup W) (t : MulAut W) : Prop where
  std : D3Std M Mp T L V
  VT : V = orbSup T V
  tT : t ∈ T
  tn : t ∉ Subgroup.normalizer (L : Set (MulAut W))
  Mp_sup : Mp = L ⊔ conjAutSub t L
  a38 : A38Types ↥L
  comm : ⁅L, conjAutSub t L⁆ = ⊥
  cases : ∀ s ∈ T, conjAutSub s L = L ∨ conjAutSub s L = conjAutSub t L

theorem D37Cfg.of_d3L38 {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)}
    {V : Subgroup W} {t : MulAut W} (hL38 : D3L38) (hD : D3Std M Mp T L V) (hVT : V = orbSup T V)
    (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) : D37Cfg M Mp T L V t := by
  obtain ⟨ha, hc, -, hcases⟩ := hL38 W M Mp T L V hD t htT htL hMp
  exact ⟨hD, hVT, htT, htL, hMp, ha, hc, hcases⟩

namespace D37Cfg

section Basic

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

theorem T_le_stab (n : D37Cfg M Mp T L V t) : T ≤ stabSub V := fun x hx =>
  stab_of_orbSup_eq n.VT.symm x hx

theorem Mp_le_stab (n : D37Cfg M Mp T L V t) : Mp ≤ stabSub V :=
  insp5a_sec_Mp_le_stabSub n.std.hyp

theorem L_le_Mp (n : D37Cfg M Mp T L V t) : L ≤ Mp :=
  insp5a_sec_L_le_Mp n.std.hyp

theorem Lt_le_Mp (n : D37Cfg M Mp T L V t) : conjAutSub t L ≤ Mp :=
  le_of_le_of_eq le_sup_right n.Mp_sup.symm

theorem L_le_stab (n : D37Cfg M Mp T L V t) : L ≤ stabSub V :=
  n.L_le_Mp.trans n.Mp_le_stab

theorem Lt_le_stab (n : D37Cfg M Mp T L V t) : conjAutSub t L ≤ stabSub V :=
  n.Lt_le_Mp.trans n.Mp_le_stab

theorem t_stab (n : D37Cfg M Mp T L V t) : t ∈ stabSub V :=
  n.T_le_stab n.tT

theorem MpT_le_stab (n : D37Cfg M Mp T L V t) : Mp ⊔ T ≤ stabSub V :=
  sup_le n.Mp_le_stab n.T_le_stab

theorem Mp_le_M (n : D37Cfg M Mp T L V t) : Mp ≤ M := by
  rw [n.Mp_sup]
  exact sup_le (le_of_mem_cComp n.std.hyp.comp)
    (le_of_mem_cComp (conjAutSub_mem_cComp n.std.hyp.comp (n.std.hyp.sylow.1 n.tT)))

theorem MpT_le_M (n : D37Cfg M Mp T L V t) : Mp ⊔ T ≤ M :=
  sup_le n.Mp_le_M n.std.hyp.sylow.1

theorem conj_conj (n : D37Cfg M Mp T L V t) : conjAutSub t (conjAutSub t L) = L := by
  rcases n.cases (t * t) (T.mul_mem n.tT n.tT) with h | h
  · rw [← conjAutSub_mul]
    exact h
  · exfalso
    rw [conjAutSub_mul] at h
    have h' : conjAutSub t⁻¹ (conjAutSub t (conjAutSub t L)) =
        conjAutSub t⁻¹ (conjAutSub t L) := by rw [h]
    rw [conjAutSub_inv_conjAutSub, conjAutSub_inv_conjAutSub] at h'
    exact n.tn (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h')

theorem nontrivial (n : D37Cfg M Mp T L V t) : Nontrivial ↥V := by
  obtain ⟨-, -, hlt, -⟩ := mem_irrPlus_top_iff.mp n.std.hyp.irr
  rw [Subgroup.nontrivial_iff_ne_bot]
  intro h
  rw [h] at hlt
  exact not_lt_bot hlt

theorem exp (n : D37Cfg M Mp T L V t) : ∀ w : ↥V, w ^ 2 = 1 := fun w =>
  Subtype.ext (by simp [n.std.hyp.exp])

theorem comm_mem (n : D37Cfg M Mp T L V t) :
    ∀ x ∈ L, ∀ y ∈ conjAutSub t L, x * y = y * x := by
  intro x hx y hy
  have h := Subgroup.commutator_eq_bot_iff_le_centralizer.mp n.comm hx
  exact ((Subgroup.mem_centralizer_iff.mp h) y hy).symm

theorem sup_eq (n : D37Cfg M Mp T L V t) :
    autSub L V ⊔ autSub (conjAutSub t L) V = autSub Mp V := by
  rw [n.Mp_sup]
  exact (autSub_sup (sup_le n.L_le_stab n.Lt_le_stab)).symm

end Basic

section Faithful

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

theorem not_L_le_centSub (n : D37Cfg M Mp T L V t) : ¬ L ≤ centSub V := by
  intro hL
  have hLt : conjAutSub t L ≤ centSub V := by
    intro y hy v hv
    rw [mem_conjAutSub_iff] at hy
    have h1 := hL hy (t⁻¹ v) (((stabSub V).inv_mem n.t_stab v).mpr hv)
    have h2 : t⁻¹ (y v) = t⁻¹ v := by simpa [MulAut.mul_apply] using h1
    exact t⁻¹.injective h2
  have hMp : Mp ≤ centSub V := by
    rw [n.Mp_sup]
    exact sup_le hL hLt
  obtain ⟨-, -, hlt, -⟩ := mem_irrPlus_top_iff.mp n.std.hyp.irr
  apply hlt.not_ge
  intro v hv
  exact ⟨hv, fun m hm => hMp hm v hv⟩

theorem faithful (n : D37Cfg M Mp T L V t) : L ⊓ centSub V = ⊥ :=
  inf_centSub_eq_bot_of_isSimpleGroup (insp5a_sec_isSimpleGroup n.a38) n.L_le_stab
    n.not_L_le_centSub

noncomputable def eL (n : D37Cfg M Mp T L V t) :
    ↥L ≃* ↥(autSub L V) :=
  autSubEquivOfFaithful n.L_le_stab n.faithful

theorem simple (n : D37Cfg M Mp T L V t) :
    IsSimpleGroup ↥(autSub L V) := by
  have := insp5a_sec_isSimpleGroup n.a38
  exact MulEquiv.isSimpleGroup n.eL.symm

theorem nonab (n : D37Cfg M Mp T L V t) :
    ∃ a ∈ autSub L V, ∃ b ∈ autSub L V, a * b ≠ b * a := by
  have hns : ¬ Group.IsSolvable ↥L := not_isSolvable_of_mem_cComp n.std.hyp.comp
  by_contra h
  push Not at h
  apply hns
  refine Group.isSolvable_of_comm fun a b => ?_
  have h1 := h (n.eL a) (n.eL a).2 (n.eL b) (n.eL b).2
  have h2 : n.eL a * n.eL b = n.eL b * n.eL a := Subtype.ext h1
  rw [← map_mul, ← map_mul] at h2
  exact n.eL.injective h2

theorem typeD (n : D37Cfg M Mp T L V t) : A38Types ↥(autSub L V) :=
  a38Types_congr n.eL n.a38

theorem sqtk (hA21 : AsA21SQTKSection) (n : D37Cfg M Mp T L V t) :
    SQTKGroup ↥(autSub L V) := by
  have hLq : CFSG.IsQuasisimple ↥L := insp5a_sec_isQuasisimple n.std.hyp n.a38
  have hq : CFSG.IsQuasisimple ↥(autSub L V) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv n.eL hLq
  obtain ⟨S, _, _, hSQT, hK, φ, hφ⟩ := n.std.hyp.qsqtk
  have hS : SQTKGroup S := ⟨fun p hp hp2 => hSQT p hp hp2, hK⟩
  exact B69.sqtk_autSub hA21 n.L_le_stab
    (B69.sqtk_subgroup hA21 hS φ hφ (le_of_mem_cComp n.std.hyp.comp) hLq) hq

end Faithful

section Fields

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

theorem comm_aut (n : D37Cfg M Mp T L V t) :
    ∀ g ∈ autSub L V, ∀ x ∈ autSub (conjAutSub t L) V, g * x = x * g :=
  autSub_commute n.comm_mem

theorem swapDX (n : D37Cfg M Mp T L V t) :
    autSub (conjAutSub t L) V =
      (autSub L V).map (MulAut.conj (resHom V ⟨t, n.t_stab⟩)).toMonoidHom :=
  (autSub_map_conj ⟨t, n.t_stab⟩).symm

theorem swapXD (n : D37Cfg M Mp T L V t) :
    autSub L V =
      (autSub (conjAutSub t L) V).map (MulAut.conj (resHom V ⟨t, n.t_stab⟩)).toMonoidHom := by
  have h := autSub_map_conj (X := conjAutSub t L) (U := V) ⟨t, n.t_stab⟩
  rw [n.conj_conj] at h
  exact h.symm

theorem s_mem (n : D37Cfg M Mp T L V t) : resHom V ⟨t, n.t_stab⟩ ∈ autSub T V :=
  mem_autSub.mpr ⟨⟨t, n.t_stab⟩, n.tT, rfl⟩

theorem DX_le (n : D37Cfg M Mp T L V t) :
    autSub L V ⊔ autSub (conjAutSub t L) V ≤ autSub (Mp ⊔ T) V :=
  sup_le (autSub_mono (n.L_le_Mp.trans le_sup_left) V)
    (autSub_mono (n.Lt_le_Mp.trans le_sup_left) V)

theorem G_eq (n : D37Cfg M Mp T L V t) :
    autSub (Mp ⊔ T) V = (autSub L V ⊔ autSub (conjAutSub t L) V) ⊔ autSub T V := by
  have h1 : L ⊔ conjAutSub t L ≤ stabSub V := sup_le n.L_le_stab n.Lt_le_stab
  have h2 : (L ⊔ conjAutSub t L) ⊔ T ≤ stabSub V := sup_le h1 n.T_le_stab
  rw [n.Mp_sup, autSub_sup h2, autSub_sup h1]

theorem DX_norm (n : D37Cfg M Mp T L V t) :
    ∀ g ∈ autSub (Mp ⊔ T) V, ∀ h ∈ autSub L V ⊔ autSub (conjAutSub t L) V,
      g * h * g⁻¹ ∈ autSub L V ⊔ autSub (conjAutSub t L) V := by
  rw [n.sup_eq]
  exact insp5a_sec_normal (L := Mp) (Y := Mp ⊔ T)
    (fun g hg => insp5a_sec_sup_le_normalizer n.std.hyp hg.1)

theorem T_perm (n : D37Cfg M Mp T L V t) :
    ∀ g ∈ autSub T V, (autSub L V).map (MulAut.conj g).toMonoidHom = autSub L V ∨
      (autSub L V).map (MulAut.conj g).toMonoidHom = autSub (conjAutSub t L) V := by
  intro g hg
  obtain ⟨τ, hτ, rfl⟩ := mem_autSub.mp hg
  rw [autSub_map_conj τ]
  rcases n.cases (τ : MulAut W) hτ with h | h
  · left
    rw [h]
  · right
    rw [h]

theorem T_sylow (n : D37Cfg M Mp T L V t) : IsSylowTwoOf (autSub T V) (autSub (Mp ⊔ T) V) := by
  have hT : IsSylowTwoOf T (Mp ⊔ T) :=
    F7.isSylowTwoOf_mono_right n.std.hyp.sylow le_sup_right n.MpT_le_M
  have h := isSylowTwoOf_map_subgroupOf (resHomOn V n.MpT_le_stab) hT
  rwa [← autSub_eq_map_resHomOn (le_sup_right : T ≤ Mp ⊔ T) n.MpT_le_stab,
    ← autSub_eq_map_resHomOn (le_refl (Mp ⊔ T)) n.MpT_le_stab] at h

theorem qhat (n : D37Cfg M Mp T L V t) :
    qhatOf (autSub (Mp ⊔ T) V) ≤ ((2 : ℚ) : WithTop ℚ) :=
  (qhatOf_autSub_congr n.VT).trans_le n.std.qhat

end Fields

section Irred

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

theorem commV_aut (n : D37Cfg M Mp T L V t) :
    commV (autSub L V ⊔ autSub (conjAutSub t L) V) = ⊤ := by
  rw [n.sup_eq]
  exact insp5a_sec_comm n.Mp_le_stab (mem_irrPlus_top_iff.mp n.std.hyp.irr).2.1

theorem irrC (n : D37Cfg M Mp T L V t) :
    ∀ U : Subgroup ↥V, (∀ g ∈ autSub L V ⊔ autSub (conjAutSub t L) V, ∀ u ∈ U, g u ∈ U) →
      fixV (autSub L V ⊔ autSub (conjAutSub t L) V) ≤ U →
      U = fixV (autSub L V ⊔ autSub (conjAutSub t L) V) ∨ U = ⊤ := by
  rw [n.sup_eq]
  exact fun U hU hC => irrSec_autSub n.std.hyp.irr U hC hU

theorem irr (hZ1 : Z1Stmt) (n : D37Cfg M Mp T L V t) :
    ∀ U : Subgroup ↥V, (∀ g ∈ autSub L V ⊔ autSub (conjAutSub t L) V, ∀ u ∈ U, g u ∈ U) →
      U = ⊥ ∨ U = ⊤ := by
  have := n.nontrivial
  exact irr_of_Z1 hZ1 n.exp n.comm_aut n.swapDX n.swapXD n.commV_aut n.irrC

end Irred

end D37Cfg

section Bridge

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

theorem z37_of_cfg (hA21 : AsA21SQTKSection) (hZ1 : Z1Stmt)
    (n : D37Cfg M Mp T L V t) :
    Z37 (autSub L V) (autSub (conjAutSub t L) V) (autSub (Mp ⊔ T) V) (autSub T V)
      (resHom V ⟨t, n.t_stab⟩) where
  exp := n.exp
  nontrivial := n.nontrivial
  simple := n.simple
  nonab := n.nonab
  typeD := n.typeD
  sqtkD := n.sqtk hA21
  comm := n.comm_aut
  swapDX := n.swapDX
  swapXD := n.swapXD
  s_mem := n.s_mem
  DX_le := n.DX_le
  G_eq := n.G_eq
  DX_norm := n.DX_norm
  T_perm := n.T_perm
  T_sylow := n.T_sylow
  irr := n.irr hZ1
  qhat := n.qhat

end Bridge

end CFSG.Quasithin
