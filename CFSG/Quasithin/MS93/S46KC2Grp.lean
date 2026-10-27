module

public import CFSG.Quasithin.MS93.S46X3Grp
public import CFSG.Quasithin.MS93.S46KC2Lin

public section

namespace CFSG.Quasithin.MS93.S46.KC2

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46 CFSG.Quasithin.MS93.S46.X3
open scoped commutatorElement Matrix

section Comm

variable {𝔾 : Type} [Group 𝔾]

theorem commutator_mul_left_eq {x a y : 𝔾} (hay : Commute a y) : ⁅x * a, y⁆ = ⁅x, y⁆ := by
  simp only [commutatorElement_def]
  rw [mul_assoc x a y, hay.eq]
  group

theorem commutator_mul_right_eq {x y b : 𝔾} (hbx : Commute b x) : ⁅x, y * b⁆ = ⁅x, y⁆ := by
  have h1 : b * x⁻¹ = x⁻¹ * b := hbx.inv_right.eq
  simp only [commutatorElement_def]
  calc x * (y * b) * x⁻¹ * (y * b)⁻¹ = x * y * (b * x⁻¹) * b⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * b) * b⁻¹ * y⁻¹ := by rw [h1]
    _ = x * y * x⁻¹ * y⁻¹ := by group

end Comm

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)} {c : Hyp46 M T L φ} {α β γ : Vtx (puAmalgam c.pu.le)}
  {ψ : ↥(stab (puAmalgam c.pu.le) α) →* ↥(StatedSL 3 F)}

theorem inv_mul_mul_mem_vv (d : X3Data c α β γ ψ) {x : (puAmalgam c.pu.le).Universal}
    (hx : x ∈ Vv (puAmalgam c.pu.le) α) (k : ↥(stab (puAmalgam c.pu.le) α)) :
    (k : (puAmalgam c.pu.le).Universal)⁻¹ * x * k ∈ Vv (puAmalgam c.pu.le) α := by
  have := (Subgroup.mem_normalizer_iff.mp (d.lh.vN (Subgroup.inv_mem _ k.2)) x).mp hx
  simpa using this

theorem commutator_eq_of_inv_mul_mem (d : X3Data c α β γ ψ)
    {x x' y y' : (puAmalgam c.pu.le).Universal} (hx : x ∈ Qv (puAmalgam c.pu.le) α)
    (hy : y ∈ Qv (puAmalgam c.pu.le) α) (hxx : x⁻¹ * x' ∈ ZM (puAmalgam c.pu.le) α)
    (hyy : y⁻¹ * y' ∈ ZM (puAmalgam c.pu.le) α) : ⁅x', y'⁆ = ⁅x, y⁆ := by
  have hZQ : ZM (puAmalgam c.pu.le) α ≤ Qv _ α := d.lh.zv.trans d.lh.vq
  have hcomm : ∀ a ∈ ZM (puAmalgam c.pu.le) α, ∀ g ∈ Qv (puAmalgam c.pu.le) α, Commute a g :=
    fun a ha g hg => (Subgroup.mem_centralizer_iff.mp (d.lh.zq ha) g hg).symm
  obtain ⟨a, ha, rfl⟩ : ∃ a ∈ ZM (puAmalgam c.pu.le) α, x' = x * a := ⟨x⁻¹ * x', hxx, by group⟩
  obtain ⟨b, hb, rfl⟩ : ∃ b ∈ ZM (puAmalgam c.pu.le) α, y' = y * b := ⟨y⁻¹ * y', hyy, by group⟩
  rw [commutator_mul_left_eq (hcomm a ha _ ((Qv _ α).mul_mem hy (hZQ hb))),
    commutator_mul_right_eq (hcomm b hb x hx)]

theorem commutator_mem_of_row (d : X3Data c α β γ ψ)
    (h2 : ∀ k : ↥(stab (puAmalgam c.pu.le) α), toSL3 ψ k ∈ (rootGroup 2 1 : Subgroup (SL3 F)) →
      ∀ z ∈ ZM (puAmalgam c.pu.le) γ, ⁅z, (k : (puAmalgam c.pu.le).Universal)⁆ ∈ ZM _ α)
    {z : (puAmalgam c.pu.le).Universal} (hz : z ∈ ZM (puAmalgam c.pu.le) γ)
    {k : ↥(stab (puAmalgam c.pu.le) α)}
    (hk : (toSL3 ψ k : Matrix (Fin 3) (Fin 3) F) 0 = Pi.single 0 1) :
    ⁅z, (k : (puAmalgam c.pu.le).Universal)⁆ ∈ ZM (puAmalgam c.pu.le) α := by
  set S := commRight (stab (puAmalgam c.pu.le) α) (ZM _ α) (stab_le_normalizer_zm _ α) z with hS
  have hQS : Qv (puAmalgam c.pu.le) α ≤ S := fun q hq =>
    ⟨d.lh.qK hq, d.lh.vqc (Subgroup.commutator_mem_commutator (d.zγVα hz) hq)⟩
  have hmem : ∀ g : SL3 F, (∀ k : ↥(stab (puAmalgam c.pu.le) α), toSL3 ψ k = g →
      ⁅z, (k : (puAmalgam c.pu.le).Universal)⁆ ∈ ZM _ α) → g ∈ natImage ψ S := by
    intro g hg
    obtain ⟨k, hk⟩ := toSL3_surjective d.lh.surj g
    exact mem_natImage.mpr ⟨k, ⟨k.2, hg k hk⟩, hk⟩
  have hT : ∀ g : SL3 F, g ∈ (rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)) →
      g ∈ natImage ψ S := by
    intro g hg
    rw [← d.qvβ] at hg
    obtain ⟨t, ht, rfl⟩ := mem_natImage.mp hg
    exact mem_natImage.mpr ⟨t, ⟨t.2, d.commutator_sup_qv_le
      (Subgroup.commutator_mem_commutator (Subgroup.mem_sup_left hz) ht)⟩, rfl⟩
  have hA := mem_of_row_zero (D := natImage ψ S)
    (fun e => hT _ (Subgroup.mem_sup_left (rootElt_mem_rootGroup 1 0 e)))
    (fun e => hT _ (Subgroup.mem_sup_right (rootElt_mem_rootGroup 2 0 e)))
    (fun e => hmem _ fun k hk => d.commutator_mem_of_rootGroup12 h2
      (hk ▸ rootElt_mem_rootGroup 1 2 e) hz)
    (fun e => hmem _ fun k hk => h2 k (hk ▸ rootElt_mem_rootGroup 2 1 e) z hz) hk
  obtain ⟨s, hs, he⟩ := mem_natImage.mp hA
  exact (d.mem_of_toSL3_eq hQS hs he).2

theorem inv_mul_mem_of_row_eq (d : X3Data c α β γ ψ)
    (h2 : ∀ k : ↥(stab (puAmalgam c.pu.le) α), toSL3 ψ k ∈ (rootGroup 2 1 : Subgroup (SL3 F)) →
      ∀ z ∈ ZM (puAmalgam c.pu.le) γ, ⁅z, (k : (puAmalgam c.pu.le).Universal)⁆ ∈ ZM _ α)
    {z : (puAmalgam c.pu.le).Universal} (hz : z ∈ ZM (puAmalgam c.pu.le) γ)
    {h h' : ↥(stab (puAmalgam c.pu.le) α)}
    (hr : (toSL3 ψ h : Matrix (Fin 3) (Fin 3) F) 0 = (toSL3 ψ h' : Matrix (Fin 3) (Fin 3) F) 0) :
    ((h : (puAmalgam c.pu.le).Universal)⁻¹ * z * h)⁻¹ *
      ((h' : (puAmalgam c.pu.le).Universal)⁻¹ * z * h') ∈ ZM (puAmalgam c.pu.le) α := by
  have hc := commutator_mem_of_row d h2 hz (k := h' * h⁻¹) (by
    rw [map_mul, map_inv]
    exact row_mul_inv hr.symm)
  have hc' : ⁅z, (h' : (puAmalgam c.pu.le).Universal) * (h : (puAmalgam c.pu.le).Universal)⁻¹⁆ ∈
      ZM (puAmalgam c.pu.le) α := by
    simpa using hc
  have hmK : (h : (puAmalgam c.pu.le).Universal)⁻¹ * z⁻¹ *
      ((h' : (puAmalgam c.pu.le).Universal) * (h : (puAmalgam c.pu.le).Universal)⁻¹)⁻¹ ∈
      stab (puAmalgam c.pu.le) α :=
    (stab _ α).mul_mem ((stab _ α).mul_mem ((stab _ α).inv_mem h.2)
      ((stab _ α).inv_mem (d.zγK hz)))
      ((stab _ α).inv_mem ((stab _ α).mul_mem h'.2 ((stab _ α).inv_mem h.2)))
  have e : ((h : (puAmalgam c.pu.le).Universal)⁻¹ * z * h)⁻¹ *
      ((h' : (puAmalgam c.pu.le).Universal)⁻¹ * z * h') =
      ((h : (puAmalgam c.pu.le).Universal)⁻¹ * z⁻¹ *
        ((h' : (puAmalgam c.pu.le).Universal) * (h : (puAmalgam c.pu.le).Universal)⁻¹)⁻¹) *
      ⁅z, (h' : (puAmalgam c.pu.le).Universal) * (h : (puAmalgam c.pu.le).Universal)⁻¹⁆ *
      ((h : (puAmalgam c.pu.le).Universal)⁻¹ * z⁻¹ *
        ((h' : (puAmalgam c.pu.le).Universal) * (h : (puAmalgam c.pu.le).Universal)⁻¹)⁻¹)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_zm _ α hmK) _).mp hc'

theorem commutator_eq_conj (d : X3Data c α β γ ψ)
    (h2 : ∀ k : ↥(stab (puAmalgam c.pu.le) α), toSL3 ψ k ∈ (rootGroup 2 1 : Subgroup (SL3 F)) →
      ∀ z ∈ ZM (puAmalgam c.pu.le) γ, ⁅z, (k : (puAmalgam c.pu.le).Universal)⁆ ∈ ZM _ α)
    {z : (puAmalgam c.pu.le).Universal} (hz : z ∈ ZM (puAmalgam c.pu.le) γ)
    {E K h h' : ↥(stab (puAmalgam c.pu.le) α)}
    (hE : (toSL3 ψ E : Matrix (Fin 3) (Fin 3) F) 0 = Pi.single 1 1)
    (hh : (toSL3 ψ h : Matrix (Fin 3) (Fin 3) F) 0 = (toSL3 ψ K : Matrix (Fin 3) (Fin 3) F) 0)
    (hh' : (toSL3 ψ h' : Matrix (Fin 3) (Fin 3) F) 0 = (toSL3 ψ K : Matrix (Fin 3) (Fin 3) F) 1) :
    ⁅(h : (puAmalgam c.pu.le).Universal)⁻¹ * z * h,
      (h' : (puAmalgam c.pu.le).Universal)⁻¹ * z * h'⁆ =
      (K : (puAmalgam c.pu.le).Universal)⁻¹ *
        ⁅z, (E : (puAmalgam c.pu.le).Universal)⁻¹ * z * E⁆ * K := by
  have hzV : z ∈ Vv (puAmalgam c.pu.le) α := d.zγVα hz
  have e1 := inv_mul_mem_of_row_eq d h2 hz (h := K) (h' := h) hh.symm
  have e2 := inv_mul_mem_of_row_eq d h2 hz (h := E * K) (h' := h') (by
    rw [map_mul, row_mul_of_row_eq hE, hh'])
  rw [commutator_eq_of_inv_mul_mem d (d.lh.vq (inv_mul_mul_mem_vv d hzV K))
    (d.lh.vq (inv_mul_mul_mem_vv d hzV (E * K))) e1 e2]
  simp only [Subgroup.coe_mul, commutatorElement_def]
  group

theorem commutator_zm_smul_le' (d : X3Data c α β γ ψ) {g g' : (puAmalgam c.pu.le).Universal}
    (hg : g ∈ stab (puAmalgam c.pu.le) α) (hg' : g' ∈ stab (puAmalgam c.pu.le) α) :
    ⁅ZM (puAmalgam c.pu.le) (g • γ), ZM _ (g' • γ)⁆ ≤ Usup _ α (g • β) := by
  have hgα : g • α = α := hg
  have hg'α : g' • α = α := hg'
  have hadj : (puAmalgam c.pu.le).treeGraph.Adj α (g • β) := by
    have := (adj_smul _ g α β).mpr d.adjαβ
    rwa [hgα] at this
  have hQ : ZM (puAmalgam c.pu.le) (g' • γ) ≤ Qv _ (g • β) := by
    rw [zm_smul]
    calc (ZM (puAmalgam c.pu.le) γ).map (MulAut.conj g').toMonoidHom
        ≤ (Qv (puAmalgam c.pu.le) α).map (MulAut.conj g').toMonoidHom := Subgroup.map_mono d.zγα
      _ = Qv _ α := by rw [← qv_smul, hg'α]
      _ ≤ Qv _ (g • β) := qv_le_qv _ c.pu.hyp20 d.mα hadj
  calc ⁅ZM (puAmalgam c.pu.le) (g • γ), ZM _ (g' • γ)⁆
      ≤ ⁅ZM (puAmalgam c.pu.le) (g • γ), Qv _ (g • β)⁆ := Subgroup.commutator_mono le_rfl hQ
    _ = Usup _ (g • γ) (g • β) := by
        rw [Usup, zv_of_isMVtx _ ((isMVtx_smul _ g γ).mpr d.mγ)]
    _ = Usup _ α (g • β) := by rw [usup_smul, d.uγ, ← usup_smul, hgα]

variable (c) in
theorem inv_mul_mul_mem_zm {z : (puAmalgam c.pu.le).Universal}
    (hz : z ∈ ZM (puAmalgam c.pu.le) γ) (k : ↥(stab (puAmalgam c.pu.le) α)) :
    (k : (puAmalgam c.pu.le).Universal)⁻¹ * z * k ∈
      ZM (puAmalgam c.pu.le) (((k⁻¹ : ↥(stab (puAmalgam c.pu.le) α)) :
        (puAmalgam c.pu.le).Universal) • γ) := by
  rw [zm_smul, mem_map_conj]
  simpa [mul_assoc] using hz

theorem row_dotProduct_eq_zero (d : X3Data c α β γ ψ) {z : (puAmalgam c.pu.le).Universal}
    (hz : z ∈ ZM (puAmalgam c.pu.le) γ) {h h' : ↥(stab (puAmalgam c.pu.le) α)}
    {x : (puAmalgam c.pu.le).Universal}
    (hx : x = ⁅(h : (puAmalgam c.pu.le).Universal)⁻¹ * z * h,
      (h' : (puAmalgam c.pu.le).Universal)⁻¹ * z * h'⁆)
    (hxU : x ∈ Uloc c.pu.le L α) :
    (toSL3 ψ h : Matrix (Fin 3) (Fin 3) F) 0 ⬝ᵥ natVecG d.lh.nat x = 0 ∧
      (toSL3 ψ h' : Matrix (Fin 3) (Fin 3) F) 0 ⬝ᵥ natVecG d.lh.nat x = 0 := by
  have hm := Subgroup.commutator_mem_commutator (inv_mul_mul_mem_zm c hz h)
    (inv_mul_mul_mem_zm c hz h')
  have key : ∀ k : ↥(stab (puAmalgam c.pu.le) α),
      x ∈ Usup (puAmalgam c.pu.le) α (((k⁻¹ : ↥(stab (puAmalgam c.pu.le) α)) :
        (puAmalgam c.pu.le).Universal) • β) →
      (toSL3 ψ k : Matrix (Fin 3) (Fin 3) F) 0 ⬝ᵥ natVecG d.lh.nat x = 0 := by
    intro k hk
    have := d.apply_zero_of_mem_usup (g := k⁻¹) (u := ⟨x, hxU⟩) hk
    rw [map_inv, inv_inv] at this
    rw [natVecG_of_mem d.lh.nat hxU]
    exact this
  refine ⟨key h ?_, key h' ?_⟩
  · rw [hx]
    exact commutator_zm_smul_le' d (h⁻¹).2 (h'⁻¹).2 hm
  · rw [hx]
    rw [Subgroup.commutator_comm] at hm
    exact commutator_zm_smul_le' d (h'⁻¹).2 (h⁻¹).2 hm

theorem zm_smul_le_vStar (d : X3Data c α β γ ψ) {g : (puAmalgam c.pu.le).Universal}
    (hg : g ∈ stab (puAmalgam c.pu.le) α) :
    ZM (puAmalgam c.pu.le) (g • γ) ≤ vStar c.pu.le L α := by
  have hgα : g • α = α := hg
  have hαρ : (puAmalgam c.pu.le).treeGraph.Adj α (g • β) := by
    have := (adj_smul _ g α β).mpr d.adjαβ
    rwa [hgα] at this
  have hadj : (puAmalgam c.pu.le).treeGraph.Adj (g • β) (g • γ) :=
    (adj_smul _ g β γ).mpr d.adjβγ
  have hnB : ¬ ZM (puAmalgam c.pu.le) (g • γ) ≤ Bloc c.pu.le L α := by
    intro hle
    apply d.zγ
    have h1 := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hle
    rw [zm_smul, map_conj_inv_map_conj, ← hgα, bloc_smul c.pu, map_conj_inv_map_conj] at h1
    exact h1
  exact le_iSup₂_of_le (f := fun β (_ : β ∈ (puAmalgam c.pu.le).treeGraph.neighborSet α) =>
    vStarB c.pu.le L α β) (g • β) hαρ
    (le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx (puAmalgam c.pu.le) |
      (puAmalgam c.pu.le).treeGraph.Adj (g • β) ρ ∧
        ¬ ZM (puAmalgam c.pu.le) ρ ≤ Bloc c.pu.le L α}) => ZM (puAmalgam c.pu.le) ρ)
      (g • γ) ⟨hadj, hnB⟩ le_rfl)

variable [CharP F 2]

end CFSG.Quasithin.MS93.S46.KC2
