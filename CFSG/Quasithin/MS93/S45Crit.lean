module

public import CFSG.Quasithin.MS93.S45Edge
import CFSG.Quasithin.MS93.S4A42Coc

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped Matrix

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

omit [Finite G] [Fintype F] in
theorem commN_ne_bot {A : Subgroup (SL3 F)} (hA : A ≠ ⊥) : commN A ≠ ⊥ := by
  intro hbot
  apply hA
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  have hmat : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    ext i j
    have hx : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single j 1 - Pi.single j 1 = 0 := by
      have := sub_mem_commN hg (Pi.single j (1 : F))
      rw [hbot, Submodule.mem_bot] at this
      exact this
    have := congrFun (sub_eq_zero.mp hx) i
    simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this
  exact Subtype.ext hmat

omit [Finite G] [Fintype F] in
theorem fixN_ne_top {A : Subgroup (SL3 F)} (hA : A ≠ ⊥) : fixN A ≠ ⊤ := by
  intro htop
  apply commN_ne_bot hA
  rw [eq_bot_iff, commN, Submodule.span_le]
  rintro _ ⟨g, hg, x, rfl⟩
  have hx : x ∈ fixN A := htop ▸ Submodule.mem_top
  simp [hx g hg]

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

theorem dist_of_isCritical {x x' : Vtx (puAmalgam c.hyp.le)}
    (hc : IsCritical (puAmalgam c.hyp.le) x x') : (puAmalgam c.hyp.le).treeGraph.dist x x' = 8 :=
  hc.2.1.trans c.b8

theorem isCritical_symm {x x' : Vtx (puAmalgam c.hyp.le)}
    (hc : IsCritical (puAmalgam c.hyp.le) x x') : IsCritical (puAmalgam c.hyp.le) x' x :=
  ms22_iii _ c.hyp.hyp20 c.bpos c.cent hc

theorem critR_le_zloc {x x' : Vtx (puAmalgam c.hyp.le)}
    (hc : IsCritical (puAmalgam c.hyp.le) x x') :
    critR (puAmalgam c.hyp.le) x x' ≤ Zloc c.hyp.le L (geo _ x x' 2) := by
  have hd := c.dist_of_isCritical hc
  have hx := hc.1
  have hx' := (c.isCritical_symm hc).1
  have hy : IsMVtx (puAmalgam c.hyp.le) (geo _ x x' 2) := by
    rw [isMVtx_geo _ (by omega)]; exact ⟨fun _ => even_two, fun _ => hx⟩
  have hZx : ZM (puAmalgam c.hyp.le) x ≤ Vv _ (geo _ x x' 2) := by
    have := zv_le_vi (puAmalgam c.hyp.le) (δ := geo _ x x' 2) (ρ := x) (i := 2)
      (by rw [tdist_comm, dist_geo _ (by omega)])
    rwa [zv_of_isMVtx _ hx] at this
  have hZx' : ZM (puAmalgam c.hyp.le) x' ≤ Qv _ (geo _ x x' 2) := by
    apply zm_le_qv_of_dist_lt _ hx'
    rw [tdist_comm, dist_geo_right _ (by omega), hd, c.b8]
    norm_num
  exact (Subgroup.commutator_mono hZx hZx').trans (c.commutator_vv_qv_le_zloc hy)

theorem critR_comm (x x' : Vtx (puAmalgam c.hyp.le)) :
    critR (puAmalgam c.hyp.le) x x' = critR _ x' x := Subgroup.commutator_comm _ _

theorem critR_le_zloc' {x x' : Vtx (puAmalgam c.hyp.le)}
    (hc : IsCritical (puAmalgam c.hyp.le) x x') :
    critR (puAmalgam c.hyp.le) x x' ≤ Zloc c.hyp.le L (geo _ x' x 2) := by
  rw [c.critR_comm]; exact c.critR_le_zloc (c.isCritical_symm hc)

theorem critR_le_uloc {x x' : Vtx (puAmalgam c.hyp.le)}
    (hc : IsCritical (puAmalgam c.hyp.le) x x') :
    critR (puAmalgam c.hyp.le) x x' ≤ Uloc c.hyp.le L x := by
  have hx := hc.1
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc c.hyp c.via hx
  have hZs : ZM (puAmalgam c.hyp.le) x' ≤ stab _ x :=
    zm_le_stab_of_isCritical _ c.hyp.hyp20 c.bpos hc
  rw [critR, commutator_zm_eq_uloc c.hyp c.full hx hZs]
  exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hZs.trans hψ.1)

theorem critR_le_uloc' {x x' : Vtx (puAmalgam c.hyp.le)}
    (hc : IsCritical (puAmalgam c.hyp.le) x x') :
    critR (puAmalgam c.hyp.le) x x' ≤ Uloc c.hyp.le L x' := by
  rw [c.critR_comm]; exact c.critR_le_uloc (c.isCritical_symm hc)

section Natural

variable {x x' : Vtx (puAmalgam c.hyp.le)} {ψ : ↥(stab (puAmalgam c.hyp.le) x) →* ↥(StatedSL 3 F)}

theorem zm_le_qv_geo_one (hc : IsCritical (puAmalgam c.hyp.le) x x') :
    ZM (puAmalgam c.hyp.le) x' ≤ Qv _ (geo _ x x' 1) :=
  zm_le_qv_geo_one_left _ c.hyp.hyp20 c.bpos c.cent (c.isCritical_symm hc)

theorem fixN_natImage_zm (hc : IsCritical (puAmalgam c.hyp.le) x x')
    (hψ : IsSumOfNaturalModulesVia (stab _ x) (Uloc c.hyp.le L x) ⊥ ψ false 1) :
    fixN (natImage ψ (ZM (puAmalgam c.hyp.le) x')) = fixN (natImage ψ (Qv _ (geo _ x x' 1))) := by
  have hx := hc.1
  have hd := c.dist_of_isCritical hc
  have hadj : (puAmalgam c.hyp.le).treeGraph.Adj x (geo _ x x' 1) := adj_geo_one _ (by omega)
  have hZT := c.zm_le_qv_geo_one hc
  obtain ⟨ψ', -, hψ'⟩ := exists_natural_Uloc c.hyp c.via (c.isCritical_symm hc).1
  have hne := (s35_core c.hyp c.cent c.via hc hψ hψ').2.2.2.2.2
  have hle : fixN (natImage ψ (Qv (puAmalgam c.hyp.le) (geo _ x x' 1))) ≤
      fixN (natImage ψ (ZM (puAmalgam c.hyp.le) x')) := by
    intro v hv g hg
    obtain ⟨a, haZ, rfl⟩ := mem_natImage.mp hg
    exact hv _ (mem_natImage.mpr ⟨a, hZT haZ, rfl⟩)
  have h2 := (c.fixN_eq_commN_qv hψ hx hadj).2
  symm
  apply Submodule.eq_of_le_of_finrank_le hle
  have hlt : Module.finrank F ↥(fixN (natImage ψ (ZM (puAmalgam c.hyp.le) x'))) < 3 := by
    have := Submodule.finrank_lt (fixN_ne_top hne)
    rwa [Module.finrank_fin_fun] at this
  omega

theorem card_natImage_zm (hc : IsCritical (puAmalgam c.hyp.le) x x')
    (hψ : IsSumOfNaturalModulesVia (stab _ x) (Uloc c.hyp.le L x) ⊥ ψ false 1) :
    Nat.card ↥(natImage ψ (ZM (puAmalgam c.hyp.le) x')) = Fintype.card F := by
  have hx := hc.1
  have hd := c.dist_of_isCritical hc
  have hadj : (puAmalgam c.hyp.le).treeGraph.Adj x (geo _ x x' 1) := adj_geo_one _ (by omega)
  obtain ⟨ψ', -, hψ'⟩ := exists_natural_Uloc c.hyp c.via (c.isCritical_symm hc).1
  have hcore := s35_core c.hyp c.cent c.via (c.isCritical_symm hc) hψ' hψ
  have h2 : Module.finrank F ↥(fixN (natImage ψ (ZM (puAmalgam c.hyp.le) x'))) = 2 := by
    rw [c.fixN_natImage_zm hc hψ]; exact (c.fixN_eq_commN_qv hψ hx hadj).2
  have h2' : Module.finrank F ↥(fixN (natImage ψ' (ZM (puAmalgam c.hyp.le) x))) = 2 := by
    rw [← h2]; exact hcore.1.symm
  rw [hcore.2.1, hcore.2.2.1, h2', Nat.card_eq_fintype_card]
  norm_num

theorem uloc_inf_qv (hc : IsCritical (puAmalgam c.hyp.le) x x')
    (hψ : IsSumOfNaturalModulesVia (stab _ x) (Uloc c.hyp.le L x) ⊥ ψ false 1) :
    Uloc c.hyp.le L x ⊓ Qv _ x' = Usup _ x (geo _ x x' 1) := by
  have h20 := c.hyp.hyp20
  have hx := hc.1
  have hc' := c.isCritical_symm hc
  have hd := c.dist_of_isCritical hc
  have hadj : (puAmalgam c.hyp.le).treeGraph.Adj x (geo _ x x' 1) := adj_geo_one _ (by omega)
  have hd' : (puAmalgam c.hyp.le).treeGraph.dist x' x = 8 := c.dist_of_isCritical hc'
  have hadj' : (puAmalgam c.hyp.le).treeGraph.Adj x' (geo _ x' x 1) := adj_geo_one _ (by omega)
  have hZs : ZM (puAmalgam c.hyp.le) x' ≤ stab _ x := zm_le_stab_of_isCritical _ h20 c.bpos hc
  have hUZ : Uloc c.hyp.le L x ≤ ZM _ x := uloc_le_zm c.hyp c.full hx
  have hZT : ZM (puAmalgam c.hyp.le) x ≤ Qv _ (geo _ x' x 1) := c.zm_le_qv_geo_one hc'
  have hCent := c.cent x' (geo _ x' x 1) hc'.1 hadj'
  have hW := c.usup_eq_uloc_inf_centralizer hψ hx hadj
  have hfix := c.fixN_natImage_zm hc hψ
  ext u
  constructor
  · rintro ⟨huU, huQ⟩
    rw [hW]
    refine ⟨huU, ?_⟩
    have huC : u ∈ Subgroup.centralizer (ZM (puAmalgam c.hyp.le) x' : Set _) := by
      rw [← hCent] at huQ; exact huQ.2
    have h1 := (S4A.mem_centralizer_iff_natVec hψ hZs ⟨u, huU⟩).mp huC
    rw [hfix] at h1
    exact (S4A.mem_centralizer_iff_natVec hψ (qv_le_stab_of_adj _ hadj.symm) ⟨u, huU⟩).mpr h1
  · intro hu
    rw [hW] at hu
    obtain ⟨huU, huC⟩ := hu
    refine ⟨huU, ?_⟩
    have h1 := (S4A.mem_centralizer_iff_natVec hψ (qv_le_stab_of_adj _ hadj.symm) ⟨u, huU⟩).mp
      huC
    rw [← hfix] at h1
    have huC' := (S4A.mem_centralizer_iff_natVec hψ hZs ⟨u, huU⟩).mpr h1
    rw [← hCent]
    exact ⟨hZT (hUZ huU), huC'⟩

theorem zm_inf_qv (hc : IsCritical (puAmalgam c.hyp.le) x x')
    (hψ : IsSumOfNaturalModulesVia (stab _ x) (Uloc c.hyp.le L x) ⊥ ψ false 1) :
    ZM (puAmalgam c.hyp.le) x ⊓ Qv _ x' = ZH _ (geo _ x x' 1) := by
  have h := c.hyp
  have hx := hc.1
  have hd := c.dist_of_isCritical hc
  have hadj : (puAmalgam h.le).treeGraph.Adj x (geo _ x x' 1) := adj_geo_one _ (by omega)
  have hZQ : Zloc h.le L x ≤ Qv _ x' := zloc_le_qv_of_isCritical h c.full hc
  have hUs : Uloc h.le L x ≤ stab (puAmalgam h.le) x :=
    (uloc_le_zm h c.full hx).trans ((zm_le_qv_self _ hx h.critDist_pos).trans (qv_le_stab _ x))
  have hn : Zloc h.le L x ≤ Subgroup.normalizer (Uloc h.le L x : Set _) :=
    (zloc_le_centralizer_stab h c.full hx).trans ((Subgroup.centralizer_le hUs).trans
      (Subgroup.centralizer_le_normalizer _))
  rw [zm_eq_uloc_sup_zloc h c.full hx, sup_comm, sup_inf_eq_of_le hZQ hn, c.uloc_inf_qv hc hψ,
    c.zh_eq_usup_sup_zloc hψ hx hadj, sup_comm]

end Natural

end Ctx

end CFSG.Quasithin.MS93.S45
