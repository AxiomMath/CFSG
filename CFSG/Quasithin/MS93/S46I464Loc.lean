module

public import CFSG.Quasithin.MS93.S46I464Lin
public import CFSG.Quasithin.MS93.S46I465
public import CFSG.Quasithin.MS93.S4A42i

public section

namespace CFSG.Quasithin.MS93.S46.I464

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A
open scoped commutatorElement

section Grp

variable {𝔾 : Type*} [Group 𝔾]

theorem conjCl_le_of_le_normalizer {H K N : Subgroup 𝔾} (hK : K ≤ N)
    (hH : H ≤ Subgroup.normalizer (N : Set 𝔾)) : conjCl H K ≤ N :=
  iSup₂_le fun _ hg => (Subgroup.map_mono hK).trans (map_conj_eq_of_mem_normalizer (hH hg)).le

theorem map_conj_le_centralizer {H K : Subgroup 𝔾} (hH : H ≤ Subgroup.centralizer (K : Set 𝔾))
    (g : 𝔾) : H.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.centralizer ((K.map (MulAut.conj g).toMonoidHom : Subgroup 𝔾) : Set 𝔾) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  have hxy : y * x = x * y := Subgroup.mem_centralizer_iff.mp (hH hx) y hy
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
    _ = g * (x * y) * g⁻¹ := by rw [hxy]
    _ = g * x * g⁻¹ * (g * y * g⁻¹) := by group

theorem le_normalizer_of_le_centralizer {H K : Subgroup 𝔾}
    (h : K ≤ Subgroup.centralizer (H : Set 𝔾)) : K ≤ Subgroup.normalizer (H : Set 𝔾) :=
  h.trans (Subgroup.centralizer_le_normalizer _)

end Grp

section Vertex

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

omit hφ in
theorem zm_le_vv_of_dist {x y : Vtx (puAmalgam h.le)} (hy : IsMVtx _ y)
    (hd : (puAmalgam h.le).treeGraph.dist x y ≤ 2) : ZM (puAmalgam h.le) y ≤ Vv _ x :=
  le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx (puAmalgam h.le) |
    (puAmalgam h.le).treeGraph.dist x ρ ≤ 2}) => Zv (puAmalgam h.le) ρ) y hd
    (zv_of_isMVtx _ hy).ge

omit [Fintype F] hφ in
theorem isPGroup_natImage_of_le_qv {δ ρ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    (hρ : (puAmalgam h.le).treeGraph.Adj δ ρ) {A : Subgroup (puAmalgam h.le).Universal}
    (hA : A ≤ Qv _ ρ) (ψ : ↥(stab (puAmalgam h.le) δ) →* ↥(StatedSL 3 F)) :
    IsPGroup 2 (natImage ψ A) :=
  isPGroup_natImage ((isPGroup_qv _ h.hyp20 ((isMVtx_iff_of_adj _ hρ).mp hδ)).to_le hA)
    (hA.trans (qv_le_stab_of_adj _ hρ.symm))

theorem commutator_uloc_le_centralizer_of_card_le {δ ρ : Vtx (puAmalgam h.le)}
    (hδ : IsMVtx _ δ) (hρ : (puAmalgam h.le).treeGraph.Adj δ ρ)
    {A : Subgroup (puAmalgam h.le).Universal} (hA : A ≤ Qv _ ρ)
    (hcard : Nat.card ↥⁅Uloc h.le L δ, A⁆ ≤ Fintype.card F) :
    ⁅Uloc h.le L δ, A⁆ ≤ Subgroup.centralizer (A : Set _) := by
  have : CharP F 2 := charP_two_of_isSL3FullVia hφ
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hδ
  have hAK : A ≤ stab _ δ := hA.trans (qv_le_stab_of_adj _ hρ.symm)
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  rw [card_commutator_eq_pow hψ hAK, ← Nat.card_eq_fintype_card] at hcard
  have h1 : Module.finrank F (commN (natImage ψ A)) ≤ 1 := by
    by_contra hc
    have h2 : Nat.card F ^ 2 ≤ Nat.card F ^ Module.finrank F (commN (natImage ψ A)) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  exact commutator_le_centralizer_of_commN_le_fixN hψ hAK hAK
    (commN_le_fixN_of_finrank_le_one (isPGroup_natImage_of_le_qv h hδ hρ hA ψ) h1)

theorem commutator_commutator_uloc_le {δ ρ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    (hρ : (puAmalgam h.le).treeGraph.Adj δ ρ) {A : Subgroup (puAmalgam h.le).Universal}
    (hA : A ≤ Qv _ ρ) :
    ⁅⁅Uloc h.le L δ, A⁆, A⁆ ≤ Subgroup.centralizer (A : Set _) := by
  have : CharP F 2 := charP_two_of_isSL3FullVia hφ
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hδ
  exact commutator_commutator_le_centralizer hψ (hA.trans (qv_le_stab_of_adj _ hρ.symm))
    (isPGroup_natImage_of_le_qv h hδ hρ hA ψ)

theorem commutator_uloc_le_centralizer_of_card_ge {δ ρ : Vtx (puAmalgam h.le)}
    (hδ : IsMVtx _ δ) (hρ : (puAmalgam h.le).treeGraph.Adj δ ρ)
    {A : Subgroup (puAmalgam h.le).Universal} (hA : A ≤ Qv _ ρ)
    (hcard : Fintype.card F ^ 2 ≤
      Nat.card ↥(Uloc h.le L δ ⊓ Subgroup.centralizer (A : Set (puAmalgam h.le).Universal))) :
    ⁅Uloc h.le L δ, A⁆ ≤ Subgroup.centralizer (A : Set _) := by
  have : CharP F 2 := charP_two_of_isSL3FullVia hφ
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hδ
  have hAK : A ≤ stab _ δ := hA.trans (qv_le_stab_of_adj _ hρ.symm)
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  rw [card_inf_centralizer_eq_pow hψ hAK, ← Nat.card_eq_fintype_card] at hcard
  have h2 : 2 ≤ Module.finrank F (fixN (natImage ψ A)) :=
    (Nat.pow_le_pow_iff_right (by omega)).mp hcard
  exact commutator_le_centralizer_of_commN_le_fixN hψ hAK hAK
    (commN_le_fixN_of_two_le_finrank (isPGroup_natImage_of_le_qv h hδ hρ hA ψ) h2)

theorem card_uloc_inf_centralizer_le {δ ρ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    (hρ : (puAmalgam h.le).treeGraph.Adj δ ρ) {A : Subgroup (puAmalgam h.le).Universal}
    (hA : A ≤ Qv _ ρ) (hnot : ¬ ⁅Uloc h.le L δ, A⁆ ≤ Subgroup.centralizer (A : Set _)) :
    Nat.card ↥(Uloc h.le L δ ⊓ Subgroup.centralizer (A : Set (puAmalgam h.le).Universal)) ≤
      Fintype.card F := by
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hδ
  have hAK : A ≤ stab _ δ := hA.trans (qv_le_stab_of_adj _ hρ.symm)
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  refine not_lt.mp fun hlt => hnot (commutator_uloc_le_centralizer_of_card_ge h hφ hδ hρ hA ?_)
  rw [card_inf_centralizer_eq_pow hψ hAK, ← Nat.card_eq_fintype_card] at hlt ⊢
  have hf : 2 ≤ Module.finrank F (fixN (natImage ψ A)) := by
    by_contra hf
    have : Nat.card F ^ Module.finrank F (fixN (natImage ψ A)) ≤ Nat.card F ^ 1 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    rw [pow_one] at this
    omega
  exact Nat.pow_le_pow_right (by omega) hf

theorem exists_mem_ltil_smul_eq {μ ν : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ)
    (hν : Qv (puAmalgam h.le) μ ≤ stab _ ν) {g : (puAmalgam h.le).Universal}
    (hg : g ∈ stab _ μ) : ∃ l ∈ Ltil h.le L μ, l • ν = g • ν := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hnorm : Qv (puAmalgam h.le) μ ≤
      Subgroup.normalizer (Ltil h.le L μ : Set (puAmalgam h.le).Universal) :=
    (qv_le_stab _ μ).trans (stab_le_normalizer_ltil h μ)
  have hg' : g ∈ ((Ltil h.le L μ ⊔ Qv _ μ : Subgroup _) : Set (puAmalgam h.le).Universal) := by
    rw [← stab_eq_ltil_sup_qv h hfull hμ]
    exact hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm] at hg'
  obtain ⟨l, hl, y, hy, rfl⟩ := hg'
  refine ⟨l, hl, ?_⟩
  rw [mul_smul, (mem_stab _).mp (hν hy)]

theorem relIndex_le_of_le_centralizer {δ ρ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    (hρ : (puAmalgam h.le).treeGraph.Adj δ ρ) {A B : Subgroup (puAmalgam h.le).Universal}
    (hB : B ≤ Qv _ ρ) (hAB : A ≤ B)
    (hcard : Nat.card ↥⁅Uloc h.le L δ, B⁆ = Fintype.card F ^ 2)
    (hfix : ⁅Uloc h.le L δ, B⁆ ≤ Subgroup.centralizer (A : Set _))
    (hne : ⁅Uloc h.le L δ, A⁆ ≠ ⁅Uloc h.le L δ, B⁆) :
    (Qv (puAmalgam h.le) δ).relIndex A ≤ Fintype.card F := by
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hδ
  have hBK : B ≤ stab _ δ := hB.trans (qv_le_stab_of_adj _ hρ.symm)
  have hAK : A ≤ stab _ δ := hAB.trans hBK
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hfB := hcard
  rw [card_commutator_eq_pow hψ hBK, ← Nat.card_eq_fintype_card] at hfB
  have hfB2 : Module.finrank F (commN (natImage ψ B)) = 2 := Nat.pow_right_injective hq hfB
  have h2 : 2 ≤ Module.finrank F (fixN (natImage ψ A)) :=
    hfB2 ▸ Submodule.finrank_mono (commN_le_fixN_of_commutator_le_centralizer hψ hBK hfix)
  have hle : ⁅Uloc h.le L δ, A⁆ ≤ ⁅Uloc h.le L δ, B⁆ := Subgroup.commutator_mono le_rfl hAB
  have hfin : Finite ↥⁅Uloc h.le L δ, B⁆ :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hlt : Nat.card ↥⁅Uloc h.le L δ, A⁆ < Nat.card ↥⁅Uloc h.le L δ, B⁆ :=
    lt_of_le_of_ne (Subgroup.card_le_of_le hle)
      (fun he => hne (Subgroup.eq_of_le_of_card_ge hle he.ge))
  rw [card_commutator_eq_pow hψ hAK, card_commutator_eq_pow hψ hBK, hfB2] at hlt
  have h1 : Module.finrank F (commN (natImage ψ A)) ≤ 1 := by
    have := (Nat.pow_lt_pow_iff_right (by omega)).mp hlt
    omega
  rw [← card_natImage_eq_relIndex h hφ hδ hψ hAK, ← Nat.card_eq_fintype_card]
  exact card_le_of_finrank h2 h1

theorem uloc_inf_centralizer_stab {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) :
    Uloc h.le L δ ⊓ Subgroup.centralizer (stab (puAmalgam h.le) δ : Set _) = ⊥ := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb0 := h.critDist_pos
  rw [eq_bot_iff, ← uloc_inf_dloc_eq_bot h hφ δ]
  refine le_inf inf_le_left (le_dloc_of_commutator_le h hδ
    (inf_le_left.trans ((uloc_le_zm h hfull hδ).trans (zm_le_qv_self _ hδ hb0))) ?_)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (inf_le_right.trans (Subgroup.centralizer_le (ltil_le_stab h δ)))]
  exact bot_le

omit [Fintype F] hφ in
theorem usup_le_zm {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) :
    Usup (puAmalgam h.le) α β ≤ ZM _ α := by
  rw [Usup, zv_of_isMVtx _ hα]
  exact Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((qv_le_stab_of_adj _ hαβ.symm).trans (stab_le_normalizer_zm _ α))

omit [Fintype F] hφ in
theorem mem_zh_of_mem_zm {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) {z : (puAmalgam h.le).Universal}
    (hz : z ∈ ZM (puAmalgam h.le) α) (hzc : z ∈ Subgroup.centralizer (Qv _ β : Set _)) :
    z ∈ ZH (puAmalgam h.le) β := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hZQ : ZM (puAmalgam h.le) α ≤ Qv _ β :=
    (zm_le_qv_self _ hα hb0).trans (qv_le_qv _ h20 hα hαβ)
  exact Subgroup.subset_closure ⟨⟨hZQ hz, hzc⟩, (isElemAbelian_zm _ h20 hb0 hα).2 z hz⟩

theorem usup_le_zh_of_card_le {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β)
    (hcard : Nat.card ↥(Usup (puAmalgam h.le) α β) ≤ Fintype.card F) :
    Usup (puAmalgam h.le) α β ≤ ZH _ β := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hc : Usup (puAmalgam h.le) α β ≤ Subgroup.centralizer (Qv _ β : Set _) := by
    rw [S4A.usup_eq_commutator_uloc h hfull hα hαβ] at hcard ⊢
    exact commutator_uloc_le_centralizer_of_card_le h hφ hα hαβ le_rfl hcard
  exact fun z hz => mem_zh_of_mem_zm h hα hαβ (usup_le_zm h hα hαβ hz) (hc hz)

omit [Fintype F] hφ in
theorem not_usup_le_zh_of_edge {α β α₁ β₁ : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) (hα₁ : IsMVtx _ α₁)
    (hα₁β₁ : (puAmalgam h.le).treeGraph.Adj α₁ β₁)
    (hfail : ¬ Usup (puAmalgam h.le) α β ≤ ZH _ β) :
    ¬ Usup (puAmalgam h.le) α₁ β₁ ≤ ZH _ β₁ := by
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_of_isMVtx _ hα hαβ hα₁ hα₁β₁
  rwa [usup_smul, zh_smul, map_conj_le_map_conj_iff]

theorem card_usup_of_not_le {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β)
    (hfail : ¬ Usup (puAmalgam h.le) α β ≤ ZH _ β) :
    Nat.card ↥(Usup (puAmalgam h.le) α β) = Fintype.card F ^ 2 := by
  rcases card_usup_eq_or h hφ hα hαβ with h1 | h2
  · exact absurd (usup_le_zh_of_card_le h hφ hα hαβ h1.le) hfail
  · exact h2

end Vertex

section Bad

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
  (hC : CentHyp (puAmalgam h.le)) (hb4 : critDist (puAmalgam h.le) = 4)
  (h461 : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x → centerOf (Vv _ x) ≤ Bloc h.le L x)
  (h463 : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x →
    ⁅Vv (puAmalgam h.le) x, Qv _ x⁆ ≤ centerOf (Vv _ x))
include h hφ hb4

omit hφ hb4 in
theorem isMVtx_of_adj_adj {a b d : Vtx (puAmalgam h.le)} (ha : IsMVtx _ a)
    (hab : (puAmalgam h.le).treeGraph.Adj a b) (hbd : (puAmalgam h.le).treeGraph.Adj b d) :
    IsMVtx _ d := by
  have h1 := (isMVtx_iff_of_adj _ hab).mp ha
  have h2 := isMVtx_iff_of_adj _ hbd
  tauto

omit hφ hb4 in
theorem dist_le_two_of_adj_adj {a b d : Vtx (puAmalgam h.le)}
    (hab : (puAmalgam h.le).treeGraph.Adj a b) (hbd : (puAmalgam h.le).treeGraph.Adj b d) :
    (puAmalgam h.le).treeGraph.dist a d ≤ 2 := by
  have := dist_triangle _ a b d
  rw [dist_eq_one_of_adj _ hab, dist_eq_one_of_adj _ hbd] at this
  omega

omit hφ hb4 in
theorem critR_le_zm_left {a a' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) a a') :
    critR (puAmalgam h.le) a a' ≤ ZM _ a :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((zm_le_stab_of_isCritical _ h.hyp20 h.critDist_pos hc).trans (stab_le_normalizer_zm _ a))

include h461 h463 in
theorem card_commutator_zm_qv_of_bad {a b d : Vtx (puAmalgam h.le)} (ha : IsMVtx _ a)
    (hab : (puAmalgam h.le).treeGraph.Adj a b) (hbd : (puAmalgam h.le).treeGraph.Adj b d)
    (hbad : ¬ Usup (puAmalgam h.le) d b ≤ Bloc h.le L a) :
    Nat.card ↥⁅ZM (puAmalgam h.le) d, Qv _ a⁆ = Fintype.card F ∧
      ⁅ZM (puAmalgam h.le) d, Qv _ a⁆ ≤ centerOf (Vv _ a) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have h20 := h.hyp20
  have hd := isMVtx_of_adj_adj h ha hab hbd
  have hZdV : ZM (puAmalgam h.le) d ≤ Vv _ a :=
    zm_le_vv_of_dist h hd (dist_le_two_of_adj_adj h hab hbd)
  have hQab : Qv (puAmalgam h.le) a ≤ Qv _ b := qv_le_qv _ h20 ha hab
  have hTbd : Qv (puAmalgam h.le) b ≤ stab _ d := qv_le_stab_of_adj _ hbd
  have hXc : ⁅ZM (puAmalgam h.le) d, Qv _ a⁆ ≤ centerOf (Vv _ a) :=
    (Subgroup.commutator_mono hZdV le_rfl).trans (h463 a ha)
  have hXU : ⁅ZM (puAmalgam h.le) d, Qv _ a⁆ = ⁅Uloc h.le L d, Qv _ a⁆ :=
    commutator_zm_eq_uloc h hfull hd (hQab.trans hTbd)
  have hUdb : Usup (puAmalgam h.le) d b = ⁅Uloc h.le L d, Qv _ b⁆ :=
    S4A.usup_eq_commutator_uloc h hfull hd hbd.symm
  have hXle : ⁅ZM (puAmalgam h.le) d, Qv _ a⁆ ≤ Usup (puAmalgam h.le) d b := by
    rw [Usup, zv_of_isMVtx _ hd]
    exact Subgroup.commutator_mono le_rfl hQab
  have hUnc : ¬ Usup (puAmalgam h.le) d b ≤ centerOf (Vv _ a) := fun hle =>
    hbad (hle.trans (h461 a ha))
  obtain ⟨e₁, -, hX⟩ := card_commutator_uloc_le h hφ hd hbd.symm (P := Qv _ a) hQab
  obtain ⟨e₂, he₂, hU⟩ := card_commutator_uloc_le h hφ hd hbd.symm (P := Qv _ b) le_rfl
  rw [← hXU] at hX
  rw [← hUdb] at hU
  have hq : 2 ≤ Fintype.card F := by rw [← Nat.card_eq_fintype_card]; exact Finite.one_lt_card
  have hfin := finite_usup h hd hbd.symm
  have hlt : Nat.card ↥⁅ZM (puAmalgam h.le) d, Qv _ a⁆ <
      Nat.card ↥(Usup (puAmalgam h.le) d b) := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hXle) fun he => hUnc ?_
    rw [← Subgroup.eq_of_le_of_card_ge hXle he.ge]
    exact hXc
  rw [hX, hU] at hlt
  have hlt' := (Nat.pow_lt_pow_iff_right (by omega)).mp hlt
  have hne : ⁅ZM (puAmalgam h.le) d, Qv _ a⁆ ≠ ⊥ := by
    intro hbot
    apply hUnc
    refine (usup_le_zm h hd hbd.symm).trans (le_inf hZdV ?_)
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot).trans
      (Subgroup.centralizer_le (vv_le_qv h hb ha))
  have he₁ : e₁ ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hX
    exact hne (Subgroup.eq_bot_of_card_eq _ hX)
  refine ⟨?_, hXc⟩
  rw [hX, show e₁ = 1 by omega, pow_one]

include hC h461 h463 in
theorem exists_isCritical_of_bad {a b d : Vtx (puAmalgam h.le)} (ha : IsMVtx _ a)
    (hab : (puAmalgam h.le).treeGraph.Adj a b) (hbd : (puAmalgam h.le).treeGraph.Adj b d)
    (hbad : ¬ Usup (puAmalgam h.le) d b ≤ Bloc h.le L a) :
    ∃ l : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) l d ∧
      geo (puAmalgam h.le) l d 2 = a ∧
        critR (puAmalgam h.le) l d = ⁅ZM (puAmalgam h.le) d, Qv _ a⁆ := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have h20 := h.hyp20
  obtain ⟨hcard, -⟩ := card_commutator_zm_qv_of_bad h hφ hb4 h461 h463 ha hab hbd hbad
  have hd := isMVtx_of_adj_adj h ha hab hbd
  have hdist := dist_le_two_of_adj_adj h hab hbd
  have hQab : Qv (puAmalgam h.le) a ≤ Qv _ b := qv_le_qv _ h20 ha hab
  have hTbd : Qv (puAmalgam h.le) b ≤ stab _ d := qv_le_stab_of_adj _ hbd
  have hda2 : (puAmalgam h.le).treeGraph.dist d a = 2 := by
    have hne : d ≠ a := by
      rintro rfl
      exact hbad ((usup_le_zm h hd hbd.symm).trans (zm_le_bloc h hb hd))
    have hev : Even ((puAmalgam h.le).treeGraph.dist d a) := (even_dist_iff _ d a).mpr
      (iff_of_true hd ha)
    have h0 : (puAmalgam h.le).treeGraph.dist d a ≠ 0 := fun h0 =>
      hne ((dist_eq_zero_iff _).mp h0)
    rw [tdist_comm] at hdist
    rcases (by omega : (puAmalgam h.le).treeGraph.dist d a = 1 ∨
        (puAmalgam h.le).treeGraph.dist d a = 2) with e | e
    · exact absurd (by rw [e] at hev; exact hev) (by decide)
    · exact e
  have hZnc : ¬ ZM (puAmalgam h.le) d ≤ centerOf (Vv _ a) := fun hle =>
    hbad (((usup_le_zm h hd hbd.symm).trans hle).trans (h461 a ha))
  obtain ⟨l, hcl, hgeol⟩ : ∃ l, IsCritical (puAmalgam h.le) d l ∧
      geo (puAmalgam h.le) d l 2 = a := by
    by_contra hno
    apply hZnc
    have hcg : critGen (puAmalgam h.le) d a = ⊥ :=
      le_bot_iff.mp (iSup₂_le fun δ hδ => (hno ⟨δ, hδ⟩).elim)
    have hV := vv_le_critGen_sup h20 hC hb4 ha hda2
    rw [hcg, bot_sup_eq] at hV
    exact le_inf (zm_le_vv_of_dist h hd (by rw [tdist_comm]; omega))
      ((zm_le_centralizer_qv _ h20 hd).trans (Subgroup.centralizer_le hV))
  have hcl' := ms22_iii _ h20 hb0 hC hcl
  have hlM : IsMVtx _ l := hcl.isMVtx_right _ h20
  have hgeo : geo (puAmalgam h.le) l d 2 = a := by rw [geo_rev_two hb4 hcl]; exact hgeol
  have hla : (puAmalgam h.le).treeGraph.dist l a = 2 := by
    rw [← hgeo]
    exact dist_geo_crit hb4 hcl' (by omega)
  have hZlQa : ZM (puAmalgam h.le) l ≤ Qv _ a := zm_le_qv_of_dist_le_three hb4 hlM (by omega)
  refine ⟨l, hcl', hgeo, ?_⟩
  have hle : critR (puAmalgam h.le) l d ≤ ⁅ZM (puAmalgam h.le) d, Qv _ a⁆ := by
    rw [critR, Subgroup.commutator_comm]
    exact Subgroup.commutator_mono le_rfl hZlQa
  have hRU : critR (puAmalgam h.le) l d = ⁅Uloc h.le L d, ZM _ l⁆ := by
    rw [critR, Subgroup.commutator_comm]
    exact commutator_zm_eq_uloc h hfull hd (hZlQa.trans (hQab.trans hTbd))
  obtain ⟨e, -, he⟩ := card_commutator_uloc_le h hφ hd hbd.symm (P := ZM _ l)
    (hZlQa.trans hQab)
  rw [← hRU] at he
  have hne : critR (puAmalgam h.le) l d ≠ ⊥ := ms22_ii _ h20 hb0 hC hcl'
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [pow_zero] at he
    exact hne (Subgroup.eq_bot_of_card_eq _ he)
  have hfinX : Finite ↥⁅ZM (puAmalgam h.le) d, Qv _ a⁆ :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hcard, he]
  exact Nat.le_self_pow he0 _

include hC h461 h463 in
theorem exists_special_raw {a b d : Vtx (puAmalgam h.le)} (ha : IsMVtx _ a)
    (hab : (puAmalgam h.le).treeGraph.Adj a b) (hbd : (puAmalgam h.le).treeGraph.Adj b d)
    (hbad : ¬ Usup (puAmalgam h.le) d b ≤ Bloc h.le L a) :
    ∃ (l : Vtx (puAmalgam h.le)) (k : (puAmalgam h.le).Universal),
      IsCritical (puAmalgam h.le) l d ∧ geo (puAmalgam h.le) l d 2 = a ∧
      critR (puAmalgam h.le) l d = ⁅ZM (puAmalgam h.le) d, Qv _ a⁆ ∧ k • l = a ∧
      IsCritical (puAmalgam h.le) a (k • d) ∧ geo (puAmalgam h.le) a (k • d) 2 = k • a ∧
      ⁅ZM (puAmalgam h.le) (k • d), Qv _ (k • a)⁆ =
        (⁅ZM (puAmalgam h.le) d, Qv _ a⁆).map (MulAut.conj k).toMonoidHom ∧
      ⁅ZM (puAmalgam h.le) (k • d), Qv _ (k • a)⁆ = critR (puAmalgam h.le) a (k • d) := by
  have h20 := h.hyp20
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  obtain ⟨l, hcl, hgeo, hR⟩ := exists_isCritical_of_bad h hφ hC hb4 h461 h463 ha hab hbd hbad
  obtain ⟨k, hk⟩ := exists_smul_eq_of_isMVtx _ hcl.1 ha
  have hc : IsCritical (puAmalgam h.le) a (k • d) := by
    rw [← hk]
    exact (isCritical_smul _ k l d).mpr hcl
  have hgeo' : geo (puAmalgam h.le) a (k • d) 2 = k • a := by
    have := geo_smul _ k l d 2
    rwa [hk, hgeo] at this
  have hmap : ⁅ZM (puAmalgam h.le) (k • d), Qv _ (k • a)⁆ =
      (⁅ZM (puAmalgam h.le) d, Qv _ a⁆).map (MulAut.conj k).toMonoidHom := by
    rw [zm_smul, qv_smul, Subgroup.map_commutator]
  refine ⟨l, k, hcl, hgeo, hR, hk, hc, hgeo', hmap, ?_⟩
  rw [hmap, ← hR, critR, critR, Subgroup.map_commutator, ← zm_smul, ← zm_smul, hk]

omit hφ in
include hC in
theorem conjCl_not_le_qv {a b d a' : Vtx (puAmalgam h.le)} (ha : IsMVtx _ a)
    (hab : (puAmalgam h.le).treeGraph.Adj a b) (hbd : (puAmalgam h.le).treeGraph.Adj b d)
    (hbad : ¬ Usup (puAmalgam h.le) d b ≤ Bloc h.le L a) (hfull : IsSL3Full M T L)
    (hc : IsCritical (puAmalgam h.le) a a')
    (hR : ⁅ZM (puAmalgam h.le) a', Qv _ (geo (puAmalgam h.le) a a' 2)⁆ ≤ ZM _ a) :
    ¬ conjCl (stab (puAmalgam h.le) a) (ZM _ d) ≤ Qv _ (geo (puAmalgam h.le) a a' 2) := by
  intro hle
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have h20 := h.hyp20
  have hd := isMVtx_of_adj_adj h ha hab hbd
  have hc' := ms22_iii _ h20 hb0 hC hc
  have hVV : conjCl (stab (puAmalgam h.le) a) (ZM _ d) ≤ Vv _ a :=
    conjCl_le_of_le_normalizer (zm_le_vv_of_dist h hd (dist_le_two_of_adj_adj h hab hbd))
      (stab_le_normalizer_vv h a)
  have hAK : ⁅conjCl (stab (puAmalgam h.le) a) (ZM _ d), ZM (puAmalgam h.le) a'⁆ ≤ ZM _ a :=
    (Subgroup.commutator_mono hle le_rfl).trans ((Subgroup.commutator_comm _ _).le.trans hR)
  have hL := commutator_ltil_le_of_commutator_le h hfull ha (adj_geo_one_of_isCritical _ hb0 hc)
    (le_normalizer_conjCl _ _) (stab_le_normalizer_zm _ a) hAK (zm_le_qv_geo_one _ h20 hb0 hc)
    hc'.2.2
  apply hbad
  intro x hx
  have hx' : x ∈ conjCl (stab (puAmalgam h.le) a) (ZM _ d) :=
    le_conjCl _ _ (usup_le_zm h hd hbd.symm hx)
  exact (mem_bloc_iff h hb ha).mpr
    ⟨hVV hx', fun l hl => hL (Subgroup.commutator_mem_commutator hx' hl)⟩

include hC in
theorem commutator_zm_qv_le_zm {a x μ : Vtx (puAmalgam h.le)} (ha : IsMVtx _ a)
    (hx : IsMVtx _ x) (hμ : IsMVtx _ μ) (hax : (puAmalgam h.le).treeGraph.dist a x = 2)
    (haμ : (puAmalgam h.le).treeGraph.dist a μ = 2)
    (hcard : Nat.card ↥⁅ZM (puAmalgam h.le) x, Qv _ a⁆ ≤ Fintype.card F)
    (hZ : ¬ ZM (puAmalgam h.le) x ≤ Qv _ μ) :
    ⁅ZM (puAmalgam h.le) x, Qv _ a⁆ = ⁅ZM (puAmalgam h.le) x, ZM _ μ⁆ ∧
      ⁅ZM (puAmalgam h.le) x, Qv _ a⁆ ≤ ZM _ μ := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have h20 := h.hyp20
  have haρ : (puAmalgam h.le).treeGraph.Adj a (geo (puAmalgam h.le) a μ 1) :=
    adj_geo_one _ (by omega)
  have hρμ : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) a μ 1) μ := by
    have := adj_geo (puAmalgam h.le) (u := a) (w := μ) (i := 1) (by omega)
    rwa [geo_of_le _ (by omega : (puAmalgam h.le).treeGraph.dist a μ ≤ 1 + 1)] at this
  have haρ' : (puAmalgam h.le).treeGraph.Adj a (geo (puAmalgam h.le) a x 1) :=
    adj_geo_one _ (by omega)
  have hρ'x : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) a x 1) x := by
    have := adj_geo (puAmalgam h.le) (u := a) (w := x) (i := 1) (by omega)
    rwa [geo_of_le _ (by omega : (puAmalgam h.le).treeGraph.dist a x ≤ 1 + 1)] at this
  have hZμQa : ZM (puAmalgam h.le) μ ≤ Qv _ a :=
    zm_le_qv_of_dist_le_three hb4 hμ (by rw [tdist_comm]; omega)
  have hZxQa : ZM (puAmalgam h.le) x ≤ Qv _ a :=
    zm_le_qv_of_dist_le_three hb4 hx (by rw [tdist_comm]; omega)
  have hQax : Qv (puAmalgam h.le) a ≤ stab _ x := qv_le_stab_of_dist_le_two _ h20 ha hax.le
  have hQaμ : Qv (puAmalgam h.le) a ≤ stab _ μ := qv_le_stab_of_dist_le_two _ h20 ha haμ.le
  have hle : ⁅ZM (puAmalgam h.le) x, ZM _ μ⁆ ≤ ⁅ZM (puAmalgam h.le) x, Qv _ a⁆ :=
    Subgroup.commutator_mono le_rfl hZμQa
  have hne : ⁅ZM (puAmalgam h.le) x, ZM _ μ⁆ ≠ ⊥ := by
    intro hbot
    apply hZ
    rw [← hC μ _ hμ hρμ.symm]
    exact le_inf (hZxQa.trans (qv_le_qv _ h20 ha haρ))
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)
  have hU : ⁅ZM (puAmalgam h.le) x, ZM _ μ⁆ = ⁅Uloc h.le L x, ZM _ μ⁆ :=
    commutator_zm_eq_uloc h hfull hx (hZμQa.trans hQax)
  obtain ⟨e, -, he⟩ := card_commutator_uloc_le h hφ hx hρ'x.symm (P := ZM _ μ)
    (hZμQa.trans (qv_le_qv _ h20 ha haρ'))
  rw [← hU] at he
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [pow_zero] at he
    exact hne (Subgroup.eq_bot_of_card_eq _ he)
  have hfin : Finite ↥⁅ZM (puAmalgam h.le) x, Qv _ a⁆ := by
    have := finite_stab h ha
    refine Finite.of_injective _ (Subgroup.inclusion_injective (?_ :
      ⁅ZM (puAmalgam h.le) x, Qv _ a⁆ ≤ stab _ a))
    exact (Subgroup.le_normalizer_iff_commutator_le_right.mp
      (hZxQa.trans Subgroup.le_normalizer)).trans (qv_le_stab _ a)
  have heq : ⁅ZM (puAmalgam h.le) x, ZM _ μ⁆ = ⁅ZM (puAmalgam h.le) x, Qv _ a⁆ :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [he]; exact hcard.trans (Nat.le_self_pow he0 _))
  refine ⟨heq.symm, ?_⟩
  rw [← heq]
  exact Subgroup.le_normalizer_iff_commutator_le_right.mp
    ((hZxQa.trans hQaμ).trans (stab_le_normalizer_zm _ μ))

include hC h461 h463 in
theorem stab_le_normalizer_commutator {a b d a' : Vtx (puAmalgam h.le)} (ha : IsMVtx _ a)
    (hab : (puAmalgam h.le).treeGraph.Adj a b) (hbd : (puAmalgam h.le).treeGraph.Adj b d)
    (hbad : ¬ Usup (puAmalgam h.le) d b ≤ Bloc h.le L a)
    (hc : IsCritical (puAmalgam h.le) a a')
    (hR : ⁅ZM (puAmalgam h.le) a', Qv _ (geo (puAmalgam h.le) a a' 2)⁆ ≤ ZM _ a) :
    stab (puAmalgam h.le) a ≤
      Subgroup.normalizer ((⁅ZM (puAmalgam h.le) d, Qv _ a⁆ : Subgroup _) : Set _) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have h20 := h.hyp20
  obtain ⟨hcard, -⟩ := card_commutator_zm_qv_of_bad h hφ hb4 h461 h463 ha hab hbd hbad
  have hd := isMVtx_of_adj_adj h ha hab hbd
  have hc' := ms22_iii _ h20 hb0 hC hc
  have hβ := adj_geo_one_of_isCritical _ hb0 hc
  have hZ'β := zm_le_qv_geo_one _ h20 hb0 hc
  have hZ'a : ZM (puAmalgam h.le) a' ≤ stab _ a := zm_le_stab_of_isCritical _ h20 hb0 hc
  have hm : IsMVtx _ (geo (puAmalgam h.le) a a' 2) := isMVtx_geo_two' hb4 hc
  have ham : (puAmalgam h.le).treeGraph.dist a (geo (puAmalgam h.le) a a' 2) = 2 :=
    dist_geo_crit hb4 hc (by omega)
  have hma' : (puAmalgam h.le).treeGraph.dist (geo (puAmalgam h.le) a a' 2) a' ≤ 3 := by
    rw [dist_geo_crit_right hb4 hc (by omega)]
    omega
  have hTbd : Qv (puAmalgam h.le) b ≤ stab _ d := qv_le_stab_of_adj _ hbd
  have hTba : Qv (puAmalgam h.le) b ≤ stab _ a := qv_le_stab_of_isMVtx _ h20 ha hab
  have hQad : Qv (puAmalgam h.le) a ≤ stab _ d := (qv_le_qv _ h20 ha hab).trans hTbd
  have hdist := dist_le_two_of_adj_adj h hab hbd
  have hZdQa : ZM (puAmalgam h.le) d ≤ Qv _ a :=
    zm_le_qv_of_dist_le_three hb4 hd (by rw [tdist_comm]; omega)
  have hgen : stab (puAmalgam h.le) a =
      (⨆ g ∈ stab (puAmalgam h.le) a, (ZM (puAmalgam h.le) a').map (MulAut.conj g).toMonoidHom)
        ⊔ Qv _ b := by
    apply le_antisymm
    · refine (stab_eq_ltil_sup_qv_adj h hfull ha hab).le.trans (sup_le_sup_right ?_ _)
      exact ltil_le_of_normal h hfull ha hβ (conjCl_le_of_le hZ'a)
        (le_normalizer_conjCl _ _) (le_conjCl _ _) hZ'β hc'.2.2
    · exact sup_le (conjCl_le_of_le hZ'a) hTba
  have hQX : Qv (puAmalgam h.le) a ≤
      Subgroup.normalizer ((⁅ZM (puAmalgam h.le) d, Qv _ a⁆ : Subgroup _) : Set _) :=
    le_normalizer_of_map_conj_le fun t ht => by
      rw [Subgroup.map_commutator,
        map_conj_eq_of_mem_normalizer (stab_le_normalizer_zm _ d (hQad ht)),
        map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer ht)]
  have h₁ : Qv (puAmalgam h.le) b ≤
      Subgroup.normalizer ((⁅ZM (puAmalgam h.le) d, Qv _ a⁆ : Subgroup _) : Set _) :=
    le_normalizer_of_map_conj_le fun t ht => by
      rw [Subgroup.map_commutator,
        map_conj_eq_of_mem_normalizer (stab_le_normalizer_zm _ d (hTbd ht)),
        map_conj_eq_of_mem_normalizer (stab_le_normalizer_qv _ a (hTba ht))]
  have h₂ : Qv (puAmalgam h.le) b ≤
      Subgroup.normalizer ((ZM (puAmalgam h.le) d ⊔ ZM _ a : Subgroup _) : Set _) :=
    le_normalizer_sup (hTbd.trans (stab_le_normalizer_zm _ d))
      (hTba.trans (stab_le_normalizer_zm _ a))
  by_contra hXn
  by_cases hX2 : stab (puAmalgam h.le) a ≤
      Subgroup.normalizer ((ZM (puAmalgam h.le) d ⊔ ZM _ a : Subgroup _) : Set _)
  · apply hXn
    refine le_normalizer_of_map_conj_le fun g hg => ?_
    rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer (stab_le_normalizer_qv _ a hg)]
    have h1 : (ZM (puAmalgam h.le) d).map (MulAut.conj g).toMonoidHom ≤ ZM _ d ⊔ ZM _ a :=
      (Subgroup.map_mono le_sup_left).trans (map_conj_eq_of_mem_normalizer (hX2 hg)).le
    refine (Subgroup.commutator_mono h1 le_rfl).trans ?_
    exact S4A.commutator_sup_le_of le_rfl
      (by rw [commutator_zm_qv _ h20 ha]; exact bot_le) (hZdQa.trans hQX)
      ((zm_le_qv_self _ ha hb0).trans hQX)
  · obtain ⟨g, hg, hn1, hn2⟩ := ms21_vii _ hgen h₁ hXn h₂ hX2
    have hgd : (ZM (puAmalgam h.le) d).map (MulAut.conj g).toMonoidHom = ZM _ (g • d) :=
      (zm_smul _ g d).symm
    have hga : (ZM (puAmalgam h.le) a).map (MulAut.conj g).toMonoidHom = ZM _ a :=
      map_conj_eq_of_mem_normalizer (stab_le_normalizer_zm _ a hg)
    have hgq : (Qv (puAmalgam h.le) a).map (MulAut.conj g).toMonoidHom = Qv _ a :=
      map_conj_eq_of_mem_normalizer (stab_le_normalizer_qv _ a hg)
    rw [Subgroup.map_sup, hgd, hga] at hn2
    rw [Subgroup.map_commutator, hgd, hgq] at hn1
    have hgdM : IsMVtx _ (g • d) := (isMVtx_smul _ g d).mpr hd
    have hgdist : (puAmalgam h.le).treeGraph.dist a (g • d) = 2 := by
      have hga' : g • a = a := (mem_stab _).mp hg
      have e := dist_smul _ g a d
      rw [hga'] at e
      rw [e]
      have hne : a ≠ d := by
        rintro rfl
        exact hbad ((usup_le_zm h ha hbd.symm).trans (zm_le_bloc h (by omega) ha))
      have hev : Even ((puAmalgam h.le).treeGraph.dist a d) :=
        (even_dist_iff _ a d).mpr (iff_of_true ha hd)
      have h0 : (puAmalgam h.le).treeGraph.dist a d ≠ 0 := fun h0 =>
        hne ((dist_eq_zero_iff _).mp h0)
      rcases (by omega : (puAmalgam h.le).treeGraph.dist a d = 1 ∨
          (puAmalgam h.le).treeGraph.dist a d = 2) with e | e
      · exact absurd (by rw [e] at hev; exact hev) (by decide)
      · exact e
    by_cases hZm : ZM (puAmalgam h.le) (g • d) ≤ Qv _ (geo (puAmalgam h.le) a a' 2)
    · apply hn2
      refine le_normalizer_sup_of_commutator_le (hZ'a.trans (stab_le_normalizer_zm _ a)) ?_
      calc ⁅ZM (puAmalgam h.le) (g • d), ZM _ a'⁆ ≤
            ⁅Qv (puAmalgam h.le) (geo (puAmalgam h.le) a a' 2), ZM _ a'⁆ :=
            Subgroup.commutator_mono hZm le_rfl
        _ = ⁅ZM (puAmalgam h.le) a', Qv _ (geo (puAmalgam h.le) a a' 2)⁆ :=
            Subgroup.commutator_comm _ _
        _ ≤ ZM _ a := hR
        _ ≤ _ := le_sup_right
    · apply hn1
      have hcard' : Nat.card ↥⁅ZM (puAmalgam h.le) (g • d), Qv _ a⁆ ≤ Fintype.card F := by
        rw [← hgd, ← hgq, ← Subgroup.map_commutator,
          Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]
      have hle := (commutator_zm_qv_le_zm h hφ hC hb4 ha hgdM hm hgdist ham hcard' hZm).2
      have hcen : ZM (puAmalgam h.le) a' ≤ Subgroup.centralizer
          ((⁅ZM (puAmalgam h.le) (g • d), Qv _ a⁆ : Subgroup _) : Set _) :=
        (zm_le_centralizer_qv _ h20 hc'.1).trans (Subgroup.centralizer_le
          (hle.trans (zm_le_qv_of_dist_le_three hb4 hm hma')))
      exact le_normalizer_of_le_centralizer hcen

include hC h461 h463 in
theorem le_centralizer_stab_of_critical {a b d a' : Vtx (puAmalgam h.le)} (ha : IsMVtx _ a)
    (hab : (puAmalgam h.le).treeGraph.Adj a b) (hbd : (puAmalgam h.le).treeGraph.Adj b d)
    (hbad : ¬ Usup (puAmalgam h.le) d b ≤ Bloc h.le L a)
    (hc : IsCritical (puAmalgam h.le) a a')
    (hR : ⁅ZM (puAmalgam h.le) a', Qv _ (geo (puAmalgam h.le) a a' 2)⁆ ≤ ZM _ a) :
    ⁅ZM (puAmalgam h.le) d, Qv _ a⁆ ≤ Subgroup.centralizer (stab (puAmalgam h.le) a : Set _) ∧
      ⁅ZM (puAmalgam h.le) d, Qv _ a⁆ ≤ ZM _ (geo (puAmalgam h.le) a a' 2) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have h20 := h.hyp20
  obtain ⟨hcard, -⟩ := card_commutator_zm_qv_of_bad h hφ hb4 h461 h463 ha hab hbd hbad
  have hd := isMVtx_of_adj_adj h ha hab hbd
  have hc' := ms22_iii _ h20 hb0 hC hc
  have hm : IsMVtx _ (geo (puAmalgam h.le) a a' 2) := isMVtx_geo_two' hb4 hc
  have ham : (puAmalgam h.le).treeGraph.dist a (geo (puAmalgam h.le) a a' 2) = 2 :=
    dist_geo_crit hb4 hc (by omega)
  have hma' : (puAmalgam h.le).treeGraph.dist (geo (puAmalgam h.le) a a' 2) a' ≤ 3 := by
    rw [dist_geo_crit_right hb4 hc (by omega)]
    omega
  have hn := stab_le_normalizer_commutator h hφ hC hb4 h461 h463 ha hab hbd hbad hc hR
  have hV := conjCl_not_le_qv h hC hb4 ha hab hbd hbad hfull hc hR
  obtain ⟨g, hg, hgZ⟩ : ∃ g ∈ stab (puAmalgam h.le) a,
      ¬ (ZM (puAmalgam h.le) d).map (MulAut.conj g).toMonoidHom ≤
        Qv _ (geo (puAmalgam h.le) a a' 2) := by
    by_contra hno
    exact hV (iSup₂_le fun g hg => Classical.byContradiction fun h' => hno ⟨g, hg, h'⟩)
  rw [← zm_smul] at hgZ
  have hgdM : IsMVtx _ (g • d) := (isMVtx_smul _ g d).mpr hd
  have hgdist : (puAmalgam h.le).treeGraph.dist a (g • d) = 2 := by
    have hga' : g • a = a := (mem_stab _).mp hg
    have e := dist_smul _ g a d
    rw [hga'] at e
    rw [e]
    have hne : a ≠ d := by
      rintro rfl
      exact hbad ((usup_le_zm h ha hbd.symm).trans (zm_le_bloc h (by omega) ha))
    have hev : Even ((puAmalgam h.le).treeGraph.dist a d) :=
      (even_dist_iff _ a d).mpr (iff_of_true ha hd)
    have h0 : (puAmalgam h.le).treeGraph.dist a d ≠ 0 := fun h0 =>
      hne ((dist_eq_zero_iff _).mp h0)
    have hdist := dist_le_two_of_adj_adj h hab hbd
    rcases (by omega : (puAmalgam h.le).treeGraph.dist a d = 1 ∨
        (puAmalgam h.le).treeGraph.dist a d = 2) with e | e
    · exact absurd (by rw [e] at hev; exact hev) (by decide)
    · exact e
  have hX : ⁅ZM (puAmalgam h.le) d, Qv _ a⁆ = ⁅ZM (puAmalgam h.le) (g • d), Qv _ a⁆ := by
    rw [← (map_conj_eq_of_mem_normalizer (hn hg)), Subgroup.map_commutator, ← zm_smul,
      map_conj_eq_of_mem_normalizer (stab_le_normalizer_qv _ a hg)]
  have hcard' : Nat.card ↥⁅ZM (puAmalgam h.le) (g • d), Qv _ a⁆ ≤ Fintype.card F := by
    rw [← hX, hcard]
  have hXm : ⁅ZM (puAmalgam h.le) d, Qv _ a⁆ ≤ ZM _ (geo (puAmalgam h.le) a a' 2) := by
    rw [hX]
    exact (commutator_zm_qv_le_zm h hφ hC hb4 ha hgdM hm hgdist ham hcard' hgZ).2
  refine ⟨?_, hXm⟩
  have hXZ' : ⁅⁅ZM (puAmalgam h.le) d, Qv _ a⁆, ZM _ a'⁆ ≤ ⊥ := by
    rw [le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.le_centralizer_iff.mp ((zm_le_centralizer_qv _ h20 hc'.1).trans
      (Subgroup.centralizer_le (hXm.trans (zm_le_qv_of_dist_le_three hb4 hm hma'))))
  have hXL := commutator_ltil_le_of_commutator_le h hfull ha (adj_geo_one_of_isCritical _ hb0 hc)
    hn (le_top.trans (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge) hXZ'
    (zm_le_qv_geo_one _ h20 hb0 hc) hc'.2.2
  have hQab : Qv (puAmalgam h.le) a ≤ Qv _ b := qv_le_qv _ h20 ha hab
  have hXU : ⁅ZM (puAmalgam h.le) d, Qv _ a⁆ = ⁅Uloc h.le L d, Qv _ a⁆ :=
    commutator_zm_eq_uloc h hfull hd (hQab.trans (qv_le_stab_of_adj _ hbd))
  have hXQ : ⁅ZM (puAmalgam h.le) d, Qv _ a⁆ ≤ Subgroup.centralizer (Qv (puAmalgam h.le) a :
      Set _) := by
    rw [hXU] at hcard ⊢
    exact commutator_uloc_le_centralizer_of_card_le h hφ hd hbd.symm hQab hcard.le
  rw [Subgroup.le_centralizer_iff, stab_eq_ltil_sup_qv h hfull ha]
  refine sup_le ?_ (Subgroup.le_centralizer_iff.mp hXQ)
  exact Subgroup.le_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp hXL))

include hC h461 h463 in
theorem commutator_zm_qv_le_centralizer_stab {a b d : Vtx (puAmalgam h.le)} (ha : IsMVtx _ a)
    (hab : (puAmalgam h.le).treeGraph.Adj a b) (hbd : (puAmalgam h.le).treeGraph.Adj b d)
    (hbad : ¬ Usup (puAmalgam h.le) d b ≤ Bloc h.le L a) :
    ⁅ZM (puAmalgam h.le) d, Qv _ a⁆ ≤
      Subgroup.centralizer (stab (puAmalgam h.le) a : Set _) := by
  obtain ⟨l, k, -, -, -, -, hc, hgeo, -, hRe⟩ :=
    exists_special_raw h hφ hC hb4 h461 h463 ha hab hbd hbad
  have hR := hRe.le.trans (critR_le_zm_left h hc)
  rw [← hgeo] at hR
  exact (le_centralizer_stab_of_critical h hφ hC hb4 h461 h463 ha hab hbd hbad hc hR).1

include hC h461 h463 in
theorem exists_special {a b d : Vtx (puAmalgam h.le)} (ha : IsMVtx _ a)
    (hab : (puAmalgam h.le).treeGraph.Adj a b) (hbd : (puAmalgam h.le).treeGraph.Adj b d)
    (hbad : ¬ Usup (puAmalgam h.le) d b ≤ Bloc h.le L a) :
    ∃ a' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) a a' ∧
      ⁅ZM (puAmalgam h.le) a', Qv _ (geo (puAmalgam h.le) a a' 2)⁆ =
        critR (puAmalgam h.le) a a' ∧
      ⁅ZM (puAmalgam h.le) a', Qv _ (geo (puAmalgam h.le) a a' 2)⁆ ≤
        Subgroup.centralizer (stab (puAmalgam h.le) (geo (puAmalgam h.le) a a' 2) : Set _) ∧
      Nat.card ↥⁅ZM (puAmalgam h.le) a', Qv _ (geo (puAmalgam h.le) a a' 2)⁆ =
        Fintype.card F := by
  obtain ⟨hcard, -⟩ := card_commutator_zm_qv_of_bad h hφ hb4 h461 h463 ha hab hbd hbad
  obtain ⟨l, k, -, -, -, -, hc, hgeo, hmap, hR⟩ :=
    exists_special_raw h hφ hC hb4 h461 h463 ha hab hbd hbad
  have hcen := commutator_zm_qv_le_centralizer_stab h hφ hC hb4 h461 h463 ha hab hbd hbad
  refine ⟨k • d, hc, by rw [hgeo]; exact hR, ?_, ?_⟩
  · rw [hgeo, hmap, stab_smul]
    exact map_conj_le_centralizer hcen k
  · rw [hgeo, hmap, Subgroup.card_map_of_injective (MulAut.conj k).injective, hcard]

end Bad

end CFSG.Quasithin.MS93.S46.I464
