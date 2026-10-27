module

public import CFSG.Quasithin.MS93.S46I462
public import CFSG.Quasithin.MS93.ASIrr

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A
open scoped commutatorElement Matrix

section SL3

variable {F : Type} [Field F]

theorem mem_qPt_of_commute [Finite F] [CharP F 2] {g : SL3 F} {k : ℕ} (hg : g ^ 2 ^ k = 1)
    (h1 : g * rootElt 0 1 1 = rootElt 0 1 1 * g) (h2 : g * rootElt 0 2 1 = rootElt 0 2 1 * g) :
    g ∈ (qPt : Subgroup (SL3 F)) := by
  set m := ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) with hm
  have e1 : m * (1 + Matrix.single 0 1 1) = (1 + Matrix.single 0 1 1) * m := by
    have := congrArg (fun x : SL3 F => ((x : SL3 F) : Matrix (Fin 3) (Fin 3) F)) h1
    simpa [coe_mul_SL3, coe_rootElt (by decide : (0 : Fin 3) ≠ 1)] using this
  have e2 : m * (1 + Matrix.single 0 2 1) = (1 + Matrix.single 0 2 1) * m := by
    have := congrArg (fun x : SL3 F => ((x : SL3 F) : Matrix (Fin 3) (Fin 3) F)) h2
    simpa [coe_mul_SL3, coe_rootElt (by decide : (0 : Fin 3) ≠ 2)] using this
  have entry : ∀ (A B : Matrix (Fin 3) (Fin 3) F), A = B → ∀ i j, A i j = B i j :=
    fun A B h i j => by rw [h]
  have h10 := entry _ _ e1 1 1
  have h20 := entry _ _ e1 2 1
  have h00 := entry _ _ e1 0 1
  have h12 := entry _ _ e1 0 2
  have h22 := entry _ _ e2 0 2
  have h21 := entry _ _ e2 0 1
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.single_apply] at h10 h20 h00 h12 h22 h21
  simp at h10 h20 h00 h12 h22 h21
  have hinv : ∀ x ∈ (pt0 : Submodule F (Fin 3 → F)), (g : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ pt0 := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨?_, ?_⟩ <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hx1, hx2, ← hm, h10, h20]
  have he0 : ((![1, 0, 0] : Fin 3 → F)) ∈ (pt0 : Submodule F (Fin 3 → F)) := ⟨rfl, rfl⟩
  have hfix := mulVec_eq_of_finrank_le_one hg (le_of_eq finrank_pt0) hinv he0
  have ha : m 0 0 = 1 := by
    have := congrFun hfix 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, ← hm] using this
  have h11 : m 1 1 = 1 := by
    have h := h00
    rw [add_comm] at h
    exact (add_left_cancel h).symm.trans ha
  have h22' : m 2 2 = 1 := by
    have h := h22
    rw [add_comm] at h
    exact (add_left_cancel h).symm.trans ha
  rw [mem_qPt_iff_uniTri]
  refine ⟨m 0 1, m 0 2, Subtype.ext ?_⟩
  rw [coe_uniTri]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [← hm] <;> simp_all

theorem mem_of_commute_typeI [Finite F] [CharP F 2] {E : Subgroup (SL3 F)}
    (h2 : ∀ g ∈ E, g * g = 1) (hc : ∀ g ∈ E, ∀ g' ∈ E, g * g' = g' * g)
    (hcard : Nat.card E = Nat.card F ^ 2) (hfix : Module.finrank F (fixN E) = 1)
    {g : SL3 F} {k : ℕ} (hg : g ^ 2 ^ k = 1) (hgE : ∀ e ∈ E, g * e = e * g) : g ∈ E := by
  have hP : IsPGroup 2 E := fun e => ⟨1, Subtype.ext (by simpa [pow_one, sq] using h2 e e.2)⟩
  obtain ⟨x, hx⟩ := exists_conj_le_sStar hP
  set E' := E.map (MulAut.conj x).toMonoidHom with hE'
  have h2' : ∀ g ∈ E', g * g = 1 := by
    rintro _ ⟨e, he, rfl⟩
    rw [← map_mul, h2 e he, map_one]
  have hc' : ∀ g ∈ E', ∀ g' ∈ E', g * g' = g' * g := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    rw [← map_mul, ← map_mul, hc e he e' he']
  have hcard' : Nat.card E' = Nat.card F ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.conj x).injective, hcard]
  have hfix' : Module.finrank F (fixN E') = 1 := by
    rw [hE', fixN_map_conj, LinearEquiv.finrank_map_eq, hfix]
  have hgx : (MulAut.conj x g) ^ 2 ^ k = 1 := by rw [← map_pow, hg, map_one]
  have hcomm : ∀ r ∈ E', MulAut.conj x g * r = r * MulAut.conj x g := by
    rintro _ ⟨e, he, rfl⟩
    change MulAut.conj x g * MulAut.conj x e = MulAut.conj x e * MulAut.conj x g
    rw [← map_mul, ← map_mul, hgE e he]
  rcases le_qPt_or_le_qLn_of_elemAb hx h2' hc' with hle | hle
  · have hEq : E' = qPt := Subgroup.eq_of_le_of_card_ge hle (by rw [card_qPt, hcard'])
    have hr1 : rootElt 0 1 (1 : F) ∈ E' :=
      hEq ▸ (le_sup_left : rootGroup 0 1 ≤ qPt) (rootElt_mem_rootGroup 0 1 1)
    have hr2 : rootElt 0 2 (1 : F) ∈ E' :=
      hEq ▸ (le_sup_right : rootGroup 0 2 ≤ qPt) (rootElt_mem_rootGroup 0 2 1)
    have hgP := mem_qPt_of_commute hgx (hcomm _ hr1) (hcomm _ hr2)
    rw [← hEq] at hgP
    obtain ⟨e, he, hee⟩ := hgP
    have : e = g := (MulAut.conj x).injective hee
    rw [← this]
    exact he
  · exfalso
    have hEq : E' = qLn := Subgroup.eq_of_le_of_card_ge hle (by rw [card_qLn, hcard'])
    rw [hEq, fixN_qLn, finrank_ln01] at hfix'
    omega

theorem card_le_of_elemAb_SL3 [Finite F] [CharP F 2] {E : Subgroup (SL3 F)}
    (h2 : ∀ g ∈ E, g * g = 1) (hc : ∀ g ∈ E, ∀ g' ∈ E, g * g' = g' * g) :
    Nat.card E ≤ Nat.card F ^ 2 := by
  have hP : IsPGroup 2 E := fun e => ⟨1, Subtype.ext (by simpa [pow_one, sq] using h2 e e.2)⟩
  obtain ⟨x, hx⟩ := exists_conj_le_sStar hP
  have h2' : ∀ g ∈ E.map (MulAut.conj x).toMonoidHom, g * g = 1 := by
    rintro _ ⟨e, he, rfl⟩
    rw [← map_mul, h2 e he, map_one]
  have hc' : ∀ g ∈ E.map (MulAut.conj x).toMonoidHom, ∀ g' ∈ E.map (MulAut.conj x).toMonoidHom,
      g * g' = g' * g := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    rw [← map_mul, ← map_mul, hc e he e' he']
  rw [← Subgroup.card_map_of_injective (f := (MulAut.conj x).toMonoidHom)
    (MulAut.conj x).injective]
  rcases le_qPt_or_le_qLn_of_elemAb hx h2' hc' with hle | hle
  · exact (Subgroup.card_le_of_le hle).trans card_qPt.le
  · exact (Subgroup.card_le_of_le hle).trans card_qLn.le

end SL3

section Gen

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] {X : GoldAmalgam A C B}

theorem zm_le_vv_of_dist_le_two {δ μ : Vtx X} (hμ : IsMVtx X μ)
    (hd : X.treeGraph.dist δ μ ≤ 2) : ZM X μ ≤ Vv X δ :=
  le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx X | X.treeGraph.dist δ ρ ≤ 2}) => Zv X ρ) μ hd
    (zv_of_isMVtx X hμ).ge

end Gen

section I463

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
  (hC : CentHyp (puAmalgam h.le))
include h hφ hC

theorem commutator_vv_inf_qv_le_zm_typeI (hb4 : critDist (puAmalgam h.le) = 4)
    {δ ν : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) δ ν)
    (hI : (Qv (puAmalgam h.le) ν).relIndex (ZM (puAmalgam h.le) δ) = Nat.card F ^ 2) :
    ⁅Vv (puAmalgam h.le) δ ⊓ Qv _ (geo _ δ ν 2), ZM _ ν⁆ ≤ ZM (puAmalgam h.le) δ := by
  have h20 := h.hyp20
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have hc' := ms22_iii _ h20 hb0 hC hc
  have : CharP F 2 := charP_two_of_isSL3FullVia hφ
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hδ := hc.1
  have hν := hc'.1
  have hα : IsMVtx _ (geo (puAmalgam h.le) δ ν 2) := isMVtx_geo_two' hb4 hc
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hν
  obtain ⟨ψ', -, hψ'⟩ := exists_natural_Uloc h hφ hδ
  obtain ⟨-, -, -, -, hf2, -, hcf, -, hcardE⟩ := crit_dims h hφ hC hc' hψ hψ'
  rw [hI] at hcf hcardE
  have hf : Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) δ))) = 1 := by
    have := Nat.pow_right_injective hq hcf
    omega
  have hQs : Qv (puAmalgam h.le) (geo _ δ ν 2) ≤ stab _ ν :=
    qv_le_stab_of_dist_le_two _ h20 hα (by rw [dist_geo_crit_right hb4 hc (by omega)])
  rw [Subgroup.commutator_le]
  intro x hx w hw
  have hxs : x ∈ stab (puAmalgam h.le) ν := hQs hx.2
  obtain ⟨k, hk⟩ := isPGroup_qv_of_isMVtx h hα ⟨x, hx.2⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcomm : ∀ e ∈ natImage ψ (ZM (puAmalgam h.le) δ),
      toSL3 ψ ⟨x, hxs⟩ * e = e * toSL3 ψ ⟨x, hxs⟩ := by
    intro e he
    obtain ⟨a, haZ, rfl⟩ := mem_natImage.mp he
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (zm_le_centerOf_vv h hb hδ haZ).2 x hx.1)
  have hmem := mem_of_commute_typeI (natImage_zm_sq h hδ) (natImage_zm_comm h hδ) hcardE hf
    (toSL3_pow_two_pow (ψ := ψ) (a := ⟨x, hxs⟩) hk') hcomm
  obtain ⟨a, haZ, hae⟩ := mem_natImage.mp hmem
  have hyQ : (a : (puAmalgam h.le).Universal)⁻¹ * x ∈ Qv (puAmalgam h.le) ν := by
    have h1 : toSL3 ψ (a⁻¹ * ⟨x, hxs⟩) = 1 := by rw [map_mul, map_inv, hae, inv_mul_cancel]
    simpa using (toSL3_eq_one_iff_mem_qv h hφ hν hψ _).mp h1
  have hyw := Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hν hw) _ hyQ
  set z : (puAmalgam h.le).Universal := (a : (puAmalgam h.le).Universal) with hz
  have key : ⁅x, w⁆ = ⁅z, w⁆ := by
    calc ⁅x, w⁆ = z * (z⁻¹ * x * w) * (z⁻¹ * x)⁻¹ * z⁻¹ * w⁻¹ := by
          rw [commutatorElement_def]; group
      _ = z * (w * (z⁻¹ * x)) * (z⁻¹ * x)⁻¹ * z⁻¹ * w⁻¹ := by rw [hyw]
      _ = ⁅z, w⁆ := by rw [commutatorElement_def]; group
  have hws : w ∈ stab (puAmalgam h.le) δ := zm_le_stab_of_isCritical _ h20 hb0 hc hw
  have h2 : w * z⁻¹ * w⁻¹ ∈ ZM (puAmalgam h.le) δ :=
    (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_zm _ δ hws) _).mp (Subgroup.inv_mem _ haZ)
  rw [key, commutatorElement_def, show z * w * z⁻¹ * w⁻¹ = z * (w * z⁻¹ * w⁻¹) by group]
  exact Subgroup.mul_mem _ haZ h2

theorem relIndex_vv_le (h39 : S39) (hb4 : critDist (puAmalgam h.le) = 4)
    {α δ : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) (hδ : IsMVtx _ δ)
    (hd : (puAmalgam h.le).treeGraph.dist α δ = 2) :
    (Qv (puAmalgam h.le) α).relIndex (Vv _ δ) ≤ Nat.card F ^ 2 := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have : CharP F 2 := charP_two_of_isSL3FullVia hφ
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hα
  have hVs : Vv (puAmalgam h.le) δ ≤ stab _ α :=
    (vv_le_qv h hb hδ).trans (qv_le_stab_of_dist_le_two _ h.hyp20 hδ (by rw [tdist_comm]; omega))
  have hVQ : ⁅Vv (puAmalgam h.le) δ, Vv _ δ⁆ ≤ Qv _ α :=
    (h39 G M T L h hb4 hfull δ hδ).trans
      (centerOf_vv_le_qv h.hyp20 hC hb hδ hα (by rw [tdist_comm]; exact hd))
  rw [← card_natImage_eq_relIndex h hφ hα hψ hVs]
  refine card_le_of_elemAb_SL3 (fun g hg => ?_) (fun g hg g' hg' => ?_)
  · obtain ⟨a, haV, rfl⟩ := mem_natImage.mp hg
    rw [← map_mul]
    have := hVQ (sq_mem_commutator_vv h hb0 haV)
    exact (toSL3_eq_one_iff_mem_qv h hφ hα hψ _).mpr (by simpa [sq] using this)
  · obtain ⟨a, haV, rfl⟩ := mem_natImage.mp hg
    obtain ⟨b, hbV, rfl⟩ := mem_natImage.mp hg'
    have h1 : toSL3 ψ ⁅a, b⁆ = 1 := (toSL3_eq_one_iff_mem_qv h hφ hα hψ _).mpr (by
      simpa [commutatorElement_def] using hVQ (Subgroup.commutator_mem_commutator haV hbV))
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1

omit hC in
theorem card_zm_eq {x : Vtx (puAmalgam h.le)} (hx : IsMVtx _ x) :
    Nat.card ↥(ZM (puAmalgam h.le) x) = Nat.card F ^ 3 * Nat.card ↥(Zloc h.le L x) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hx
  have hUs : Uloc h.le L x ≤ stab (puAmalgam h.le) x :=
    (uloc_le_zm h hfull hx).trans ((zm_le_qv_self _ hx h.critDist_pos).trans (qv_le_stab _ x))
  rw [zm_eq_uloc_sup_zloc h hfull hx, card_sup_of_commute
    ((zloc_le_centralizer_stab h hfull hx).trans (Subgroup.centralizer_le hUs))
    (uloc_inf_zloc h hfull x), card_eq_of_natural hψ]

omit hC in
theorem card_zm_inf_uloc_le (hb4 : critDist (puAmalgam h.le) = 4)
    {δ ν : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) δ ν)
    (hI : (Qv (puAmalgam h.le) ν).relIndex (ZM (puAmalgam h.le) δ) = Nat.card F ^ 2) :
    Nat.card ↥(ZM (puAmalgam h.le) δ ⊓ Uloc h.le L (geo _ δ ν 2)) ≤ Nat.card F := by
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  set α := geo (puAmalgam h.le) δ ν 2 with hαdef
  have hα : IsMVtx _ α := isMVtx_geo_two' hb4 hc
  have hδ := hc.1
  have hdαν : (puAmalgam h.le).treeGraph.dist α ν ≤ 3 := by
    rw [hαdef, dist_geo_crit_right hb4 hc (by omega)]; omega
  have hδβ : (puAmalgam h.le).treeGraph.Adj δ (geo _ δ ν 1) := adj_geo_one_of_isCritical _ hb0 hc
  have hβα : (puAmalgam h.le).treeGraph.Adj (geo _ δ ν 1) α :=
    adj_geo_crit hb4 hc (i := 1) (by omega)
  have hZδs : ZM (puAmalgam h.le) δ ≤ stab _ δ := (zm_le_qv_self _ hδ hb0).trans (qv_le_stab _ δ)
  have hUαs : Uloc h.le L α ≤ stab _ α :=
    (uloc_le_zm h hfull hα).trans ((zm_le_qv_self _ hα hb0).trans (qv_le_stab _ α))
  have hZlαs : Zloc h.le L α ≤ stab _ α :=
    (zloc_le_zm h hfull hα).trans ((zm_le_qv_self _ hα hb0).trans (qv_le_stab _ α))
  have hfinδ : Finite ↥(stab (puAmalgam h.le) δ) := finite_stab h hδ
  have hfinα : Finite ↥(stab (puAmalgam h.le) α) := finite_stab h hα
  have hfinW : Finite ↥(Qv (puAmalgam h.le) ν ⊓ ZM _ δ) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_right.trans hZδs))
  have hfinZ : Finite ↥(Zloc h.le L α) := Finite.of_injective _ (Subgroup.inclusion_injective hZlαs)
  have hZloc : Nat.card ↥(Zloc h.le L δ) = Nat.card ↥(Zloc h.le L α) := by
    obtain ⟨g, hg⟩ := exists_smul_eq_of_isMVtx _ hα hδ
    rw [← hg, zloc_smul h g α, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hW : Nat.card ↥(Qv (puAmalgam h.le) ν ⊓ ZM _ δ) =
      Nat.card F * Nat.card ↥(Zloc h.le L δ) := by
    have h1 := relIndex_mul_card_inf (Qv (puAmalgam h.le) ν) (ZM _ δ)
    rw [hI, card_zm_eq h hφ hδ] at h1
    have hq : 0 < Nat.card F := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_left (by positivity : 0 < Nat.card F ^ 2) ?_
    rw [h1]
    ring
  have hZαν : ZM (puAmalgam h.le) α ≤ Qv _ ν := zm_le_qv_of_dist_le_three hb4 hα hdαν
  have hsub : (ZM (puAmalgam h.le) δ ⊓ Uloc h.le L α) ⊔ Zloc h.le L α ≤
      Qv (puAmalgam h.le) ν ⊓ ZM _ δ :=
    sup_le (le_inf (inf_le_right.trans ((uloc_le_zm h hfull hα).trans hZαν)) inf_le_left)
      (le_inf ((zloc_le_zm h hfull hα).trans hZαν)
        ((zloc_le_zh h hfull hα hβα.symm).trans (zh_le_zm _ hδβ)))
  have hcard := card_sup_of_commute (H := ZM (puAmalgam h.le) δ ⊓ Uloc h.le L α)
    (K := Zloc h.le L α)
    ((zloc_le_centralizer_stab h hfull hα).trans
      (Subgroup.centralizer_le (inf_le_right.trans hUαs)))
    (le_bot_iff.mp ((inf_le_inf_right _ inf_le_right).trans (uloc_inf_zloc h hfull α).le))
  have hle := Subgroup.card_le_of_le hsub
  rw [hcard, hW, hZloc] at hle
  have hpos : 0 < Nat.card ↥(Zloc h.le L α) := Nat.card_pos
  exact Nat.le_of_mul_le_mul_right hle hpos

omit hC in
theorem zm_inf_uloc_ne_bot {α δ : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hd : (puAmalgam h.le).treeGraph.dist α δ = 2) :
    ZM (puAmalgam h.le) δ ⊓ Uloc h.le L α ≠ ⊥ := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have : CharP F 2 := charP_two_of_isSL3FullVia hφ
  have hαβ : (puAmalgam h.le).treeGraph.Adj α (geo _ α δ 1) := adj_geo_one _ (by omega)
  have hβδ : (puAmalgam h.le).treeGraph.Adj (geo _ α δ 1) δ := by
    have := adj_geo (puAmalgam h.le) (u := α) (w := δ) (i := 1) (by omega)
    rwa [geo_of_le _ (by omega : (puAmalgam h.le).treeGraph.dist α δ ≤ 1 + 1)] at this
  have hβH : ¬ IsMVtx _ (geo (puAmalgam h.le) α δ 1) := by
    have := isMVtx_iff_of_adj _ hαβ; tauto
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hα
  have hTs : Qv (puAmalgam h.le) (geo _ α δ 1) ≤ stab _ α := qv_le_stab_of_adj _ hαβ.symm
  have hTp : IsPGroup 2 (natImage ψ (Qv (puAmalgam h.le) (geo _ α δ 1))) :=
    isPGroup_natImage (isPGroup_qv _ h20 hβH) hTs
  have hpos := finrank_fixN_pos hTp
  have hcard : 1 < Nat.card ↥(Uloc h.le L α ⊓
      Subgroup.centralizer (Qv (puAmalgam h.le) (geo _ α δ 1) : Set _)) := by
    rw [card_inf_centralizer_eq hψ hTs, Module.natCard_eq_pow_finrank (K := F)]
    exact Nat.one_lt_pow (by omega) Finite.one_lt_card
  have hle : Uloc h.le L α ⊓ Subgroup.centralizer (Qv (puAmalgam h.le) (geo _ α δ 1) : Set _) ≤
      ZM (puAmalgam h.le) δ ⊓ Uloc h.le L α := by
    refine le_inf ?_ inf_le_left
    rintro x ⟨hxU, hxc⟩
    have hxZ := uloc_le_zm h hfull hα hxU
    have hxQ : x ∈ Qv (puAmalgam h.le) (geo _ α δ 1) :=
      qv_le_qv _ h20 hα hαβ (zm_le_qv_self _ hα hb0 hxZ)
    have hx2 : x ^ 2 = 1 := (isElemAbelian_zm _ h20 hb0 hα).2 x hxZ
    exact zh_le_zm _ hβδ.symm
      (show x ∈ ZH (puAmalgam h.le) (geo _ α δ 1) from Subgroup.subset_closure ⟨⟨hxQ, hxc⟩, hx2⟩)
  intro hbot
  rw [hbot] at hle
  have := Subgroup.card_le_of_le hle
  rw [Subgroup.card_bot] at this
  omega

theorem not_typeI (h39 : S39) (h462 : I462) (hmin : PUMin M T L)
    (hb4 : critDist (puAmalgam h.le) = 4) {δ ν : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) δ ν) :
    (Qv (puAmalgam h.le) ν).relIndex (ZM (puAmalgam h.le) δ) ≠ Nat.card F ^ 2 := by
  intro hI
  have h20 := h.hyp20
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hc' := ms22_iii _ h20 hb0 hC hc
  have hδ := hc.1
  have hν := hc'.1
  set α := geo (puAmalgam h.le) δ ν 2 with hαdef
  set β := geo (puAmalgam h.le) δ ν 1 with hβdef
  have hα : IsMVtx _ α := isMVtx_geo_two' hb4 hc
  have hδβ : (puAmalgam h.le).treeGraph.Adj δ β := adj_geo_one_of_isCritical _ hb0 hc
  have hβα : (puAmalgam h.le).treeGraph.Adj β α := adj_geo_crit hb4 hc (i := 1) (by omega)
  have hdδα : (puAmalgam h.le).treeGraph.dist δ α = 2 := dist_geo_crit hb4 hc (by omega)
  have hdαν : (puAmalgam h.le).treeGraph.dist α ν = 2 := by
    rw [hαdef, dist_geo_crit_right hb4 hc (by omega)]
  have hZs : ZM (puAmalgam h.le) ν ≤ stab _ δ := zm_le_stab_of_isCritical _ h20 hb0 hc
  have hZβ : ZM (puAmalgam h.le) ν ≤ Qv _ β := zm_le_qv_geo_one _ h20 hb0 hc
  have hZQ : ¬ ZM (puAmalgam h.le) ν ≤ Qv _ δ := hc'.2.2
  have hfinS : Finite ↥(stab (puAmalgam h.le) δ) := finite_stab h hδ
  have hVs : Vv (puAmalgam h.le) δ ≤ stab _ δ := (vv_le_qv h hb hδ).trans (qv_le_stab _ δ)
  have hfinV : Finite ↥(Vv (puAmalgam h.le) δ) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hVs)
  have hBn := stab_le_normalizer_bloc h δ
  have hA := commutator_vv_inf_qv_le_zm_typeI h hφ hC hb4 hc hI
  have hB := relIndex_vv_le h hφ hC h39 hb4 hα hδ (by rw [tdist_comm]; exact hdδα)
  have hoff : IsOffenderOn (puAmalgam h.le) δ (Bloc h.le L δ) (ZM (puAmalgam h.le) ν) := by
    have hab := isElemAbelian_zm _ h20 hb0 hν
    refine ⟨⟨β, hδβ, hZβ⟩, hZQ, fun a ha => ?_, fun a ha b hb' => ?_,
      (Vv _ δ ⊓ Qv _ α) ⊔ Bloc h.le L δ, le_sup_right, sup_le inf_le_left (bloc_le_vv h δ), ?_, ?_⟩
    · rw [hab.2 a ha]; exact Subgroup.one_mem _
    · have hab' : a * b = b * a := by
        have := hab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb'⟩
        simpa using congrArg Subtype.val this
      rw [(commutatorElement_eq_one_iff_mul_comm).mpr hab']
      exact Subgroup.one_mem _
    · refine S4A.commutator_sup_le_of (hA.trans (zm_le_bloc h hb hδ)) ?_
        ((inf_le_left.trans hVs).trans hBn) (((bloc_le_vv h δ).trans hVs).trans hBn)
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hZs.trans hBn)
    · calc ((Vv (puAmalgam h.le) δ ⊓ Qv _ α) ⊔ Bloc h.le L δ).relIndex (Vv _ δ)
          ≤ (Vv (puAmalgam h.le) δ ⊓ Qv _ α).relIndex (Vv _ δ) :=
            Subgroup.relIndex_le_of_le_left le_sup_left (by
              rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
        _ = (Qv (puAmalgam h.le) α).relIndex (Vv _ δ) := Subgroup.inf_relIndex_left _ _
        _ ≤ Nat.card F ^ 2 := hB
        _ = (Qv (puAmalgam h.le) δ).relIndex (ZM _ ν) := by
            rw [← relIndex_zm_comm h hφ hC hc, hI]
  have hVU : ⁅Vv (puAmalgam h.le) δ, Vv _ δ⁆ ≤ Uloc h.le L δ :=
    h462 G M T L F φ ⟨h, hmin, hb4, hφ⟩ δ (ZM _ ν) hδ hoff
  have hcardαδ := card_zm_inf_uloc_le h hφ hb4 hc hI
  have hneαδ := zm_inf_uloc_ne_bot h hφ hα (by rw [tdist_comm]; exact hdδα)
  obtain ⟨k, hkα, hkβ⟩ := exists_smul_edge_of_isMVtx _ hα hβα.symm hδ hδβ
  have hβkδ : (puAmalgam h.le).treeGraph.Adj β (k • δ) := by
    have := (adj_smul _ k β δ).mpr hδβ.symm
    rwa [hkβ] at this
  have hkc : IsCritical (puAmalgam h.le) (k • δ) (k • ν) := (isCritical_smul _ k δ ν).mpr hc
  have hkgeo : geo (puAmalgam h.le) (k • δ) (k • ν) 2 = δ := by
    rw [geo_smul, ← hαdef, hkα]
  have hX₂k : ZM (puAmalgam h.le) (k • δ) ⊓ Uloc h.le L δ =
      (ZM (puAmalgam h.le) δ ⊓ Uloc h.le L α).map (MulAut.conj k).toMonoidHom := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj k).injective, ← zm_smul, ← uloc_smul h, hkα]
  have hβs : Qv (puAmalgam h.le) β ≤ stab _ δ := qv_le_stab_of_adj _ hδβ.symm
  have hβks : Qv (puAmalgam h.le) β ≤ stab _ (k • δ) := qv_le_stab_of_adj _ hβkδ
  have hUn : stab (puAmalgam h.le) δ ≤ Subgroup.normalizer (Uloc h.le L δ : Set _) :=
    stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) δ
  have h₁ : Qv (puAmalgam h.le) β ≤ Subgroup.normalizer
      ((ZM (puAmalgam h.le) (k • δ) ⊔ ZM _ δ : Subgroup _) : Set _) :=
    (le_inf (hβks.trans (stab_le_normalizer_zm _ _))
      (hβs.trans (stab_le_normalizer_zm _ δ))).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have h₁' : ¬ stab (puAmalgam h.le) δ ≤ Subgroup.normalizer
      ((ZM (puAmalgam h.le) (k • δ) ⊔ ZM _ δ : Subgroup _) : Set _) := by
    have := ms22_iv _ h20 hb0 hC hkc
    rwa [hkgeo, xm_eq_zm h hfull hδ] at this
  have h₂ : Qv (puAmalgam h.le) β ≤ Subgroup.normalizer
      ((ZM (puAmalgam h.le) (k • δ) ⊓ Uloc h.le L δ : Subgroup _) : Set _) :=
    (le_inf (hβks.trans (stab_le_normalizer_zm _ _)) (hβs.trans hUn)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have h₂' : ¬ stab (puAmalgam h.le) δ ≤ Subgroup.normalizer
      ((ZM (puAmalgam h.le) (k • δ) ⊓ Uloc h.le L δ : Subgroup _) : Set _) := by
    intro hn
    obtain ⟨ψ', hψ's, hψ'⟩ := exists_natural_Uloc h hφ hδ
    rcases eq_or_eq_of_natural hψ's statedSL3_transitive hψ' bot_le inf_le_right hn with
      hbot | htop
    · apply hneαδ
      rw [hX₂k] at hbot
      exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj k).injective).mp hbot
    · have h1 : Nat.card ↥(ZM (puAmalgam h.le) (k • δ) ⊓ Uloc h.le L δ) ≤ Nat.card F := by
        rw [hX₂k, Subgroup.card_map_of_injective (MulAut.conj k).injective]
        exact hcardαδ
      rw [htop, card_eq_of_natural hψ'] at h1
      have : Nat.card F ^ 1 < Nat.card F ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
      rw [pow_one] at this
      omega
  have hgen : stab (puAmalgam h.le) δ =
      (⨆ g ∈ stab (puAmalgam h.le) δ, (ZM _ ν).map (MulAut.conj g).toMonoidHom) ⊔ Qv _ β := by
    have hcl : conjCl (stab (puAmalgam h.le) δ) (ZM _ ν) =
        ⨆ g ∈ stab (puAmalgam h.le) δ, (ZM _ ν).map (MulAut.conj g).toMonoidHom := rfl
    rw [← hcl]
    apply le_antisymm
    · calc stab (puAmalgam h.le) δ = Ltil h.le L δ ⊔ Qv _ β :=
            stab_eq_ltil_sup_qv_adj h hfull hδ hδβ
        _ ≤ conjCl (stab (puAmalgam h.le) δ) (ZM _ ν) ⊔ Qv _ β :=
            sup_le_sup_right (ltil_le_of_normal h hfull hδ hδβ (conjCl_le_of_le hZs)
              (le_normalizer_conjCl _ _) (le_conjCl _ _) hZβ hZQ) _
    · exact sup_le (conjCl_le_of_le hZs) hβs
  obtain ⟨g, hg, hng₁, hng₂⟩ := ms21_vii _ hgen h₁ h₁' h₂ h₂'
  have hgδ : g • δ = δ := (mem_stab _).mp hg
  rw [Subgroup.map_sup, ← zm_smul, ← zm_smul, hgδ] at hng₁
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ← zm_smul, ← uloc_smul h, hgδ] at hng₂
  have hgk : (g * k) • α = δ := by rw [mul_smul, hkα, hgδ]
  have hgkδ : (g * k) • δ = g • k • δ := mul_smul g k δ
  set μ := g • k • δ with hμdef
  have hμ : IsMVtx _ μ := (isMVtx_smul _ g _).mpr ((isMVtx_smul _ k δ).mpr hδ)
  have hdμδ : (puAmalgam h.le).treeGraph.dist δ μ = 2 := by
    calc (puAmalgam h.le).treeGraph.dist δ μ
        = (puAmalgam h.le).treeGraph.dist ((g * k) • α) ((g * k) • δ) := by rw [hgk, hgkδ]
      _ = 2 := by rw [dist_smul, tdist_comm]; exact hdδα
  have hZμV : ZM (puAmalgam h.le) μ ≤ Vv _ δ := zm_le_vv_of_dist_le_two hμ hdμδ.le
  have hZαV : ZM (puAmalgam h.le) α ≤ Vv _ δ := zm_le_vv_of_dist_le_two hα hdδα.le
  have hμν : ¬ ⁅ZM (puAmalgam h.le) μ, ZM _ ν⁆ ≤ ZM _ δ := by
    intro hle
    apply hng₁
    rw [Subgroup.le_normalizer_iff_commutator_le_left]
    refine S4A.commutator_sup_le_of (hle.trans le_sup_right) ?_
      (le_sup_left.trans Subgroup.le_normalizer) (le_sup_right.trans Subgroup.le_normalizer)
    exact (Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hZs.trans (stab_le_normalizer_zm _ δ))).trans le_sup_right
  have hμν₂ : ⁅ZM (puAmalgam h.le) μ ⊓ Uloc h.le L δ, ZM _ ν⁆ ≠ ⊥ := by
    intro hbot
    apply hng₂
    refine le_normalizer_of_le_centralizer ?_
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hbot
  have hμQ : ¬ ZM (puAmalgam h.le) μ ≤ Qv _ α := fun hle =>
    hμν ((Subgroup.commutator_mono (le_inf hZμV hle) le_rfl).trans hA)
  have hdμα : (puAmalgam h.le).treeGraph.dist μ α = 4 := by
    have htri := dist_triangle (puAmalgam h.le) μ δ α
    rw [tdist_comm _ μ δ, hdμδ, hdδα] at htri
    by_contra hne
    exact hμQ (zm_le_qv_of_dist_le_three hb4 hμ (by omega))
  have hcμ : IsCritical (puAmalgam h.le) μ α := ⟨hμ, by rw [hdμα, hb4], hμQ⟩
  have hcμ' := ms22_iii _ h20 hb0 hC hcμ
  have hR1 : ⁅ZM (puAmalgam h.le) μ, ZM _ α⁆ ≤ ZM (puAmalgam h.le) μ ⊓ Uloc h.le L δ := by
    refine le_inf ?_ ((Subgroup.commutator_mono hZμV hZαV).trans hVU)
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((zm_le_stab_of_isCritical _ h20 hb0 hcμ).trans (stab_le_normalizer_zm _ μ))
  have hUδs : Uloc h.le L δ ≤ stab _ δ :=
    (uloc_le_zm h hfull hδ).trans ((zm_le_qv_self _ hδ hb0).trans (qv_le_stab _ δ))
  have hfinμ : Finite ↥(ZM (puAmalgam h.le) μ ⊓ Uloc h.le L δ) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_right.trans hUδs))
  have hcardμ : Nat.card ↥(ZM (puAmalgam h.le) μ ⊓ Uloc h.le L δ) ≤ Nat.card F := by
    have e : ZM (puAmalgam h.le) μ ⊓ Uloc h.le L δ =
        (ZM (puAmalgam h.le) δ ⊓ Uloc h.le L α).map (MulAut.conj (g * k)).toMonoidHom := by
      rw [Subgroup.map_inf _ _ _ (MulAut.conj (g * k)).injective, ← zm_smul, ← uloc_smul h, hgk,
        hgkδ]
    rw [e, Subgroup.card_map_of_injective (MulAut.conj (g * k)).injective]
    exact hcardαδ
  have hRcard : Nat.card F ≤ Nat.card ↥(critR (puAmalgam h.le) μ α) := by
    rcases crit_type h hφ hC hcμ with ⟨-, h1⟩ | ⟨-, h1⟩ | ⟨-, h1, -⟩
    · exact (h1.trans Nat.card_eq_fintype_card.symm).ge
    · exact (h1.trans Nat.card_eq_fintype_card.symm).ge
    · rw [h1, ← Nat.card_eq_fintype_card]
      exact Nat.le_self_pow (by norm_num) _
  have hReq : ⁅ZM (puAmalgam h.le) μ, ZM _ α⁆ = ZM (puAmalgam h.le) μ ⊓ Uloc h.le L δ :=
    Subgroup.eq_of_le_of_card_ge hR1 (hcardμ.trans hRcard)
  apply hμν₂
  rw [← hReq, ← le_bot_iff]
  calc ⁅⁅ZM (puAmalgam h.le) μ, ZM _ α⁆, ZM _ ν⁆ ≤ ⁅ZM (puAmalgam h.le) α, ZM _ ν⁆ := by
        refine Subgroup.commutator_mono ?_ le_rfl
        rw [Subgroup.commutator_comm]
        exact Subgroup.le_normalizer_iff_commutator_le_left.mp
          ((zm_le_stab_of_isCritical _ h20 hb0 hcμ').trans (stab_le_normalizer_zm _ α))
    _ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        exact (zm_le_qv_of_dist_le_three hb4 hα (by omega)).trans
          (Subgroup.le_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hν))

theorem commutator_commutator_zm_qv_eq_bot (h39 : S39) (h462 : I462) (hmin : PUMin M T L)
    (hb4 : critDist (puAmalgam h.le) = 4) {α δ ν : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hδ : IsMVtx _ δ) (hν : IsMVtx _ ν) (hdδ : (puAmalgam h.le).treeGraph.dist α δ ≤ 2)
    (hdν : (puAmalgam h.le).treeGraph.dist α ν ≤ 2) :
    ⁅⁅ZM (puAmalgam h.le) δ, Qv _ α⁆, ZM _ ν⁆ = ⊥ := by
  have h20 := h.hyp20
  have hQν : Qv (puAmalgam h.le) ν ≤ Subgroup.centralizer (ZM (puAmalgam h.le) ν : Set _) :=
    Subgroup.le_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hν)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  by_cases hQ : ZM (puAmalgam h.le) δ ≤ Qv _ ν
  · have h1 : ⁅ZM (puAmalgam h.le) δ, Qv _ α⁆ ≤ ZM _ δ :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((qv_le_stab_of_dist_le_two _ h20 hα hdδ).trans (stab_le_normalizer_zm _ δ))
    exact h1.trans (hQ.trans hQν)
  · have htri := dist_triangle (puAmalgam h.le) δ α ν
    rw [tdist_comm _ δ α] at htri
    have hd4 : (puAmalgam h.le).treeGraph.dist δ ν = 4 := by
      by_contra hne
      exact hQ (zm_le_qv_of_dist_le_three hb4 hδ (by omega))
    have hc : IsCritical (puAmalgam h.le) δ ν := ⟨hδ, by rw [hd4, hb4], hQ⟩
    have hgeo : α = geo (puAmalgam h.le) δ ν 2 :=
      eq_geo_of_dist _ (by rw [tdist_comm]; omega) (by rw [tdist_comm _ δ α, hd4]; omega)
    have hnI := not_typeI h hφ hC h39 h462 hmin hb4 hc
    have := commutator_zm_qv_mid_le h hφ hC hb4 hc
      (fun hI => hnI (hI.trans (by rw [Nat.card_eq_fintype_card])))
    rw [← hgeo] at this
    exact this.trans hQν

theorem commutator_vv_qv_le_centerOf (h39 : S39) (h462 : I462) (hmin : PUMin M T L)
    (hb4 : critDist (puAmalgam h.le) = 4) {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) :
    ⁅Vv (puAmalgam h.le) α, Qv _ α⁆ ≤ centerOf (Vv _ α) := by
  have h20 := h.hyp20
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hVs : Vv (puAmalgam h.le) α ≤ stab _ α := (vv_le_qv h hb hα).trans (qv_le_stab _ α)
  have hQV : ⁅Vv (puAmalgam h.le) α, Qv _ α⁆ ≤ Vv _ α :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp ((qv_le_stab _ α).trans
      (stab_le_normalizer_vv h α))
  have hV : Vv (puAmalgam h.le) α =
      ⨆ ρ : {ρ : Vtx (puAmalgam h.le) // (puAmalgam h.le).treeGraph.dist α ρ ≤ 2},
        Zv (puAmalgam h.le) ρ := by
    rw [show Vv (puAmalgam h.le) α = Vi (puAmalgam h.le) α 2 from rfl]
    unfold Vi
    exact iSup_subtype'
  have hZH : ∀ ρ : Vtx (puAmalgam h.le), (puAmalgam h.le).treeGraph.dist α ρ ≤ 2 →
      ¬ IsMVtx _ ρ → ZH (puAmalgam h.le) ρ ≤ ZM _ α := by
    intro ρ hd hρ
    have hodd : ¬ Even ((puAmalgam h.le).treeGraph.dist α ρ) := by
      rw [even_dist_iff]; tauto
    have h1 : (puAmalgam h.le).treeGraph.dist α ρ = 1 := by
      rcases (by omega : (puAmalgam h.le).treeGraph.dist α ρ = 0 ∨
          (puAmalgam h.le).treeGraph.dist α ρ = 1 ∨ (puAmalgam h.le).treeGraph.dist α ρ = 2) with
        h0 | h1 | h2
      · exact absurd (h0 ▸ ⟨0, rfl⟩) hodd
      · exact h1
      · exact absurd (h2 ▸ even_two) hodd
    exact zh_le_zm _ (SimpleGraph.dist_eq_one_iff_adj.mp h1)
  have hgen : ∀ ρ : {ρ : Vtx (puAmalgam h.le) // (puAmalgam h.le).treeGraph.dist α ρ ≤ 2},
      ⁅Zv (puAmalgam h.le) ρ, Qv _ α⁆ ≤ centerOf (Vv _ α) := by
    intro ρ
    by_cases hρ : IsMVtx (puAmalgam h.le) ρ.1
    · rw [zv_of_isMVtx _ hρ]
      have hZρs : ZM (puAmalgam h.le) ρ.1 ≤ stab _ α := (zm_le_vv_of_dist_le_two hρ ρ.2).trans hVs
      refine le_inf ((Subgroup.commutator_mono (zm_le_vv_of_dist_le_two hρ ρ.2) le_rfl).trans
        hQV) ?_
      rw [Subgroup.le_centralizer_iff, hV]
      refine iSup_le fun ν => ?_
      by_cases hν : IsMVtx (puAmalgam h.le) ν.1
      · rw [zv_of_isMVtx _ hν]
        exact Subgroup.le_centralizer_iff.mp ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp
          (commutator_commutator_zm_qv_eq_bot h hφ hC h39 h462 hmin hb4 hα hρ hν ρ.2 ν.2))
      · rw [zv_of_not_isMVtx _ hν]
        have hQ : ⁅ZM (puAmalgam h.le) ρ.1, Qv _ α⁆ ≤ Qv _ α := by
          rw [Subgroup.commutator_comm]
          exact Subgroup.le_normalizer_iff_commutator_le_left.mp
            (hZρs.trans (stab_le_normalizer_qv _ α))
        refine Subgroup.le_centralizer_iff.mp ((hQ.trans (Subgroup.le_centralizer_iff.mp
          (zm_le_centralizer_qv _ h20 hα))).trans (Subgroup.centralizer_le (hZH ν.1 ν.2 hν)))
    · rw [zv_of_not_isMVtx _ hρ]
      refine (Subgroup.commutator_mono (hZH ρ.1 ρ.2 hρ) le_rfl).trans ?_
      rw [commutator_zm_qv _ h20 hα]
      exact bot_le
  calc ⁅Vv (puAmalgam h.le) α, Qv _ α⁆
      = ⁅⨆ ρ : {ρ : Vtx (puAmalgam h.le) // (puAmalgam h.le).treeGraph.dist α ρ ≤ 2},
          Zv (puAmalgam h.le) ρ, Qv _ α⁆ := by rw [← hV]
    _ ≤ centerOf (Vv _ α) := commutator_iSup_le_of hgen (by
        rw [← hV]; exact hVs.trans (stab_le_normalizer_centerOf_vv h α))

theorem commutator_vv_le_zm (h39 : S39) (h462 : I462) (hmin : PUMin M T L)
    (hb4 : critDist (puAmalgam h.le) = 4) {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) :
    ⁅Vv (puAmalgam h.le) α, Vv _ α⁆ ≤ ZM _ α := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have h1 := commutator_vv_qv_le_centerOf h hφ hC h39 h462 hmin hb4 hα
  have hc1 : ⁅⁅Vv (puAmalgam h.le) α, Qv _ α⁆, Vv _ α⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr (h1.trans inf_le_right)
  have hc2 : ⁅⁅Qv (puAmalgam h.le) α, Vv _ α⁆, Vv _ α⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (Qv _ α)]; exact hc1
  have h3 : ⁅⁅Vv (puAmalgam h.le) α, Vv _ α⁆, Qv _ α⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate hc1 hc2
  have h39α := h39 G M T L h hb4 hfull α hα
  rw [← xm_eq_zm h hfull hα]
  intro x hx
  have hxQ : x ∈ Qv (puAmalgam h.le) α := vv_le_qv h hb hα (Subgroup.commutator_le_self _ hx)
  have hxc : x ∈ Subgroup.centralizer (Qv (puAmalgam h.le) α : Set _) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3) hx
  have hx2 : x ^ 2 = 1 :=
    sq_eq_one_of_mem_commutator h39α (fun a ha => sq_mem_commutator_vv h hb0 ha) hx
  exact Subgroup.subset_closure ⟨⟨hxQ, hxc⟩, hx2⟩

end I463

theorem i463_of (h32 : S32) (h39 : S39) (h462 : I462) : I463 := by
  intro G _ _ M T L F _ _ φ c α hα
  obtain ⟨h, hmin, hb4, hφ⟩ := c
  have hC := centHyp_of_S32 h32 h
  exact ⟨commutator_vv_qv_le_centerOf h hφ hC h39 h462 hmin hb4 hα,
    commutator_vv_le_zm h hφ hC h39 h462 hmin hb4 hα⟩

end CFSG.Quasithin.MS93.S46
