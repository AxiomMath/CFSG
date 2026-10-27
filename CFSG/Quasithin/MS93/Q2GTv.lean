module

public import CFSG.Quasithin.MS93.Q2GSpT
public import CFSG.Quasithin.MS93.S5AKer
public import CFSG.Quasithin.MS93.S5A53

public section

namespace CFSG.Quasithin.MS93.Q2G

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped Matrix commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {k : ℕ}
  {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

section Comm

variable (h : PUHyp M T L)
include h

theorem comm_mul_left {g : G} (hg : g ∈ M) {u v : G} (hu : u ∈ Uq M T L) (hv : v ∈ Uq M T L) :
    ⁅u * v, g⁆ = ⁅u, g⁆ * ⁅v, g⁆ := by
  have hx : g * u⁻¹ * g⁻¹ ∈ Uq M T L :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_Uq h.le_normalizer hg) _).1 (inv_mem hu)
  have hy : g * v⁻¹ * g⁻¹ ∈ Uq M T L :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_Uq h.le_normalizer hg) _).1 (inv_mem hv)
  have hU : ∀ {x y : G}, x ∈ Uq M T L → y ∈ Uq M T L → x * y = y * x := fun hx hy =>
    S5Q2.mul_comm_of_mem_Xq (h.Uq_le_Xq hx) (h.Uq_le_Xq hy)
  have h1 := hU hy hx
  have h2 := hU hv hx
  simp only [commutatorElement_def]
  calc u * v * g * (u * v)⁻¹ * g⁻¹ = u * (v * ((g * v⁻¹ * g⁻¹) * (g * u⁻¹ * g⁻¹))) := by group
    _ = u * (v * ((g * u⁻¹ * g⁻¹) * (g * v⁻¹ * g⁻¹))) := by rw [h1]
    _ = u * ((v * (g * u⁻¹ * g⁻¹)) * (g * v⁻¹ * g⁻¹)) := by group
    _ = u * (((g * u⁻¹ * g⁻¹) * v) * (g * v⁻¹ * g⁻¹)) := by rw [h2]
    _ = u * g * u⁻¹ * g⁻¹ * (v * g * v⁻¹ * g⁻¹) := by group

theorem comm_eq_of_map_eq (hd : S5.IsSp4Data M T L k F a) {g₁ g₂ : ↥M} (hg : a g₁ = a g₂)
    {u : G} (hu : u ∈ Uq M T L) : ⁅u, (g₁ : G)⁆ = ⁅u, (g₂ : G)⁆ := by
  have hk : ((g₁⁻¹ * g₂ : ↥M) : G) ∈ S5.kerG a :=
    (S5.mem_kerG a).2 ⟨(g₁⁻¹ * g₂).2, by rw [map_mul, map_inv, hg, inv_mul_cancel]⟩
  have hc : Commute ((g₁⁻¹ * g₂ : ↥M) : G) u :=
    (Subgroup.mem_centralizer_iff.1 (hd.kerG_le_centralizer_Z0q h hk) u
      (Uq_le_Z0q h.L_le hu)).symm
  have e : (g₂ : G) = g₁ * ((g₁⁻¹ * g₂ : ↥M) : G) := by simp
  rw [e]
  set c := ((g₁⁻¹ * g₂ : ↥M) : G)
  simp only [commutatorElement_def]
  symm
  calc u * (g₁ * c) * u⁻¹ * (g₁ * c)⁻¹ = u * g₁ * (c * u⁻¹) * c⁻¹ * (g₁ : G)⁻¹ := by group
    _ = u * g₁ * (u⁻¹ * c) * c⁻¹ * (g₁ : G)⁻¹ := by rw [hc.inv_right.eq]
    _ = u * g₁ * u⁻¹ * (g₁ : G)⁻¹ := by group

theorem comm_eq_one_of_vec (hd : S5.IsSp4Data M T L k F a) (nv : S5.NatVec M T L a) {g : ↥M}
    {u : ↥(Uq M T L)} (hgu : MSP.mat (a g) *ᵥ nv.vec u = nv.vec u) : ⁅(u : G), (g : G)⁆ = 1 := by
  have hlift := (S5.sp4Lift G M T L h k F _ _ a hd).2.2
  have hw : (g : G) * u * (g : G)⁻¹ ∈ Uq M T L :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_Uq h.le_normalizer g.2) u).1 u.2
  have hv := nv.vec_conj g u hw
  rw [hgu] at hv
  have h0 : nv.vec (⟨_, hw⟩ * u⁻¹) = 0 := by
    rw [nv.vec_mul, nv.vec_inv, hv, add_neg_cancel]
  have hC := (nv.vec_eq_zero_iff _).1 h0
  have hgu' := hlift g g.2 u u.2 hC
  have hc : (g : G) * u = u * g := by
    calc (g : G) * u = ((g : G) * u * (g : G)⁻¹) * g := by group
      _ = u * g := by rw [hgu']
  rw [commutatorElement_def, ← hc]
  group

end Comm

theorem comm_mem_of_mem_qLine (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l) {E : Subgroup G} (hEM : E ≤ M)
    (hE : S5.imSp a E = MSP.qLine l ⊓ commutator (MSP.Sp4 F)) {y : ↥M}
    (hy : a y ∈ MSP.qLine l) {u : G} (hu : u ∈ Uq M T L) : ⁅u, (y : G)⁆ ∈ ⁅Uq M T L, E⁆ := by
  have hK : Nat.card F = 2 := by rw [hd.nat_card_eq, pow_one]
  obtain ⟨nv⟩ := hd.nonempty_natVec
  set W := ⁅Uq M T L, E⁆ with hW
  have hEl : ∀ g : ↥M, a g ∈ MSP.qLine l ⊓ commutator (MSP.Sp4 F) →
      ∀ v ∈ Uq M T L, ⁅v, (g : G)⁆ ∈ W := by
    intro g hg v hv
    rw [← hE] at hg
    obtain ⟨f, hf, hfg⟩ := hg
    rw [← comm_eq_of_map_eq h hd hfg hv]
    exact Subgroup.commutator_mem_commutator hv (Subgroup.mem_subgroupOf.1 hf)
  have hWn : ∀ g : ↥M, a g ∈ MSP.qLine l → ∀ w ∈ W, (g : G) * w * (g : G)⁻¹ ∈ W := by
    intro g hg w hw
    have hle : W ≤ W.comap (MulAut.conj (g : G)).toMonoidHom := by
      rw [hW, Subgroup.commutator_le]
      intro v hv e he
      show (MulAut.conj (g : G)) ⁅v, e⁆ ∈ W
      rw [map_commutatorElement]
      have hv' : (MulAut.conj (g : G)) v ∈ Uq M T L := by
        rw [MulAut.conj_apply]
        exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_Uq h.le_normalizer g.2) v).1 hv
      have heM : e ∈ M := hEM he
      have hem : a ⟨e, heM⟩ ∈ MSP.qLine l := by
        have h1 : a ⟨e, heM⟩ ∈ S5.imSp a E := ⟨⟨e, heM⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩
        rw [hE] at h1
        exact h1.1
      have hae : a (g * ⟨e, heM⟩ * g⁻¹) = a ⟨e, heM⟩ := by
        rw [map_mul, map_mul, map_inv, S5.qLine_comm hl hg hem, mul_inv_cancel_right]
      have hce : (MulAut.conj (g : G)) e = ((g * ⟨e, heM⟩ * g⁻¹ : ↥M) : G) := by
        rw [MulAut.conj_apply]
        rfl
      rw [hce, comm_eq_of_map_eq h hd hae hv']
      exact Subgroup.commutator_mem_commutator hv' he
    have := hle hw
    simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using this
  obtain ⟨x, hxl, x', hx'l, hx0, hx'0, hxx⟩ := exists_ne_ne_mem_line hl
  obtain ⟨m, hm⟩ := hd.2.2.1 (MSP.transv x 1)
  obtain ⟨m', hm'⟩ := hd.2.2.1 (MSP.transv x' 1)
  have ht : MSP.transv x 1 ∈ MSP.qLine l := MSP.transv_mem_qLine hl hxl 1
  have ht' : MSP.transv x' 1 ∈ MSP.qLine l := MSP.transv_mem_qLine hl hx'l 1
  have htc : MSP.transv x 1 ∉ commutator (MSP.Sp4 F) := transv_one_not_mem_commutator hK hx0
  have ht'c : MSP.transv x' 1 ∉ commutator (MSP.Sp4 F) := transv_one_not_mem_commutator hK hx'0
  have hfix : ∀ (g : ↥M) (z : MSP.V4 F), z ≠ 0 → a g = MSP.transv z 1 → ∀ v : ↥(Uq M T L),
      MSP.form F z (nv.vec v) = 0 → ⁅(v : G), (g : G)⁆ = 1 := by
    intro g z hz hg v hv
    refine comm_eq_one_of_vec h hd nv ?_
    rw [hg]
    exact (transv_one_mulVec_eq_iff hz).2 hv
  have hmm' : ∀ v : ↥(Uq M T L), MSP.form F x' (nv.vec v) = 0 → ⁅(v : G), (m : G)⁆ ∈ W := by
    intro v hv
    have h1 := hfix m' x' hx'0 hm' v hv
    have e : ⁅(v : G), ((m * m' : ↥M) : G)⁆ = ⁅(v : G), (m : G)⁆ := by
      have e1 : ⁅(v : G), (m : G) * (m' : G)⁆ =
          ⁅(v : G), (m : G)⁆ * ((m : G) * ⁅(v : G), (m' : G)⁆ * (m : G)⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [Subgroup.coe_mul, e1, h1, mul_one, mul_inv_cancel, mul_one]
    rw [← e]
    refine hEl (m * m') ?_ v v.2
    rw [map_mul, hm, hm']
    exact ⟨(MSP.qLine l).mul_mem ht ht', S5Q2.mul_mem_commutator_of_not_mem hd htc ht'c⟩
  obtain ⟨v₀, hv₀', hv₀⟩ := exists_form_eq_zero_ne hK hx0 hx'0 hxx
  obtain ⟨u₀, hu₀⟩ := nv.surj (Multiplicative.ofAdd v₀)
  have hu₀v : nv.vec u₀ = v₀ := by
    rw [S5.NatVec.vec, hu₀]
    rfl
  have hmW : ∀ v : ↥(Uq M T L), ⁅(v : G), (m : G)⁆ ∈ W := by
    intro v
    by_cases hv : MSP.form F x (nv.vec v) = 0
    · rw [hfix m x hx0 hm v hv]
      exact Subgroup.one_mem _
    · have hd0 : MSP.form F x (nv.vec (v * u₀⁻¹)) = 0 := by
        rw [nv.vec_mul, nv.vec_inv, hu₀v, ← sub_eq_add_neg]
        exact form_sub_eq_zero hK hv (hu₀v ▸ hv₀)
      have h1 := hfix m x hx0 hm (v * u₀⁻¹) hd0
      have e : (v : G) = ((v * u₀⁻¹ : ↥(Uq M T L)) : G) * (u₀ : G) := by simp
      rw [e, comm_mul_left h m.2 (v * u₀⁻¹).2 u₀.2, h1, one_mul]
      exact hmm' u₀ (by rw [hu₀v]; exact hv₀')
  by_cases hyc : a y ∈ commutator (MSP.Sp4 F)
  · exact hEl y ⟨hy, hyc⟩ u hu
  · have hz : a (m⁻¹ * y) ∈ MSP.qLine l ⊓ commutator (MSP.Sp4 F) := by
      rw [map_mul, map_inv, hm]
      refine ⟨(MSP.qLine l).mul_mem ((MSP.qLine l).inv_mem ht) hy,
        S5Q2.mul_mem_commutator_of_not_mem hd ?_ hyc⟩
      exact fun h' => htc (by
        rw [← inv_inv (MSP.transv x 1)]
        exact Subgroup.inv_mem _ h')
    have h1 := hEl (m⁻¹ * y) hz u hu
    have e : ⁅u, (y : G)⁆ = ⁅u, (m : G)⁆ * ((m : G) * ⁅u, ((m⁻¹ * y : ↥M) : G)⁆ * (m : G)⁻¹) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      simp only [commutatorElement_def]
      group
    rw [e]
    refine mul_mem (hmW ⟨u, hu⟩) (hWn m ?_ _ h1)
    rw [hm]
    exact ht

end CFSG.Quasithin.MS93.Q2G
