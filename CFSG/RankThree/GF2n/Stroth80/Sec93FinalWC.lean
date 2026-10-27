module

public import CFSG.RankThree.GF2n.Stroth80.Sec9Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec39Rt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section ThreeSub

variable {G : Type} [Group G]

theorem sec93f_hallWitt_mem {Z : Subgroup G} {x y z : G}
    (hx : ∀ a ∈ Z, x * a * x⁻¹ ∈ Z) (hy : ∀ a ∈ Z, y * a * y⁻¹ ∈ Z)
    (hz : ∀ a ∈ Z, z * a * z⁻¹ ∈ Z)
    (h1 : ⁅y, ⁅z⁻¹, x⁻¹⁆⁆ ∈ Z) (h2 : ⁅x⁻¹, ⁅y⁻¹, z⁆⁆ ∈ Z) : ⁅⁅x, y⁆, z⁆ ∈ Z := by
  have e : ⁅⁅x, y⁆, z⁆ = (x * (y * ⁅x⁻¹, ⁅y⁻¹, z⁆⁆ * y⁻¹) * x⁻¹) *
      (x * (z * ⁅y, ⁅z⁻¹, x⁻¹⁆⁆ * z⁻¹) * x⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact Z.mul_mem (hx _ (hy _ h2)) (hx _ (hz _ h1))

theorem sec93f_comm_comm_mem {Z V A B C : Subgroup G}
    (hA : ∀ x ∈ A, ∀ a ∈ Z, x * a * x⁻¹ ∈ Z) (hB : ∀ x ∈ B, ∀ a ∈ Z, x * a * x⁻¹ ∈ Z)
    (hC : ∀ x ∈ C, ∀ a ∈ Z, x * a * x⁻¹ ∈ Z)
    (hAV : ∀ x ∈ A, ∀ v ∈ V, ⁅x, v⁆ ∈ Z) (hBV : ∀ x ∈ B, ∀ v ∈ V, ⁅x, v⁆ ∈ Z)
    (hCA : ∀ q ∈ C, ∀ x ∈ A, ⁅q, x⁆ ∈ V) (hCB : ∀ q ∈ C, ∀ x ∈ B, ⁅q, x⁆ ∈ V) :
    ∀ x ∈ A, ∀ y ∈ B, ∀ z ∈ C, ⁅⁅x, y⁆, z⁆ ∈ Z := by
  intro x hx y hy z hz
  refine sec93f_hallWitt_mem (hA x hx) (hB y hy) (hC z hz) ?_ ?_
  · exact hBV y hy _ (hCA z⁻¹ (C.inv_mem hz) x⁻¹ (A.inv_mem hx))
  · have h : ⁅y⁻¹, z⁆ ∈ V := by
      have h := hCB z hz y⁻¹ (B.inv_mem hy)
      rw [← commutatorElement_inv]
      exact V.inv_mem h
    exact hAV x⁻¹ (A.inv_mem hx) _ h

end ThreeSub

section Main

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec93f_conj_eq_of_wc (hc : Ctx M Q Z B) {t : G} {Z0 : Subgroup G} (hZ0M : Z0 ≤ M)
    (hZ0N : Z0 ≤ hc.CN t)
    (hcentre : ∀ s ∈ Z0, s ∉ Q → ⁅Q, Subgroup.zpowers s⁆ ⊔ Z = Vt M (LB M Q B) B Z t)
    (hwc : WeaklyClosedInCent M Q Z0) {g u : G} (hg : g ∈ M) (hu : u ∈ Z0) (huQ : u ∉ Q)
    (hgu : g * u * g⁻¹ ∈ Z0) : conjSubgroup g Z0 = Z0 := by
  set V := Vt M (LB M Q B) B Z t with hV
  have hQM : Q ≤ M := hc.hyp.Q_normal.1
  have hQn : ∀ m ∈ M, ∀ y ∈ Q, m * y * m⁻¹ ∈ Q := fun m hm y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hm) y).mp hy
  have hZn : ∀ m ∈ M, ∀ y ∈ Z, m * y * m⁻¹ ∈ Z := fun m hm y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hm) y).mp hy
  have hZV : Z ≤ V := sec39_Z_le_Vt
  have hwQ : g * u * g⁻¹ ∉ Q := by
    intro h
    apply huQ
    have := hQn g⁻¹ (M.inv_mem hg) _ h
    simpa [mul_assoc] using this
  have hVg : conjSubgroup g V = V := by
    have h1 := hcentre u hu huQ
    have h2 := hcentre _ hgu hwQ
    have hz : conjSubgroup g (Subgroup.zpowers u) = Subgroup.zpowers (g * u * g⁻¹) := by
      show (Subgroup.zpowers u).map (MulAut.conj g).toMonoidHom = _
      rw [MonoidHom.map_zpowers]
      rfl
    calc conjSubgroup g V = conjSubgroup g (⁅Q, Subgroup.zpowers u⁆ ⊔ Z) := by rw [h1]
      _ = ⁅Q, Subgroup.zpowers (g * u * g⁻¹)⁆ ⊔ Z := by
          rw [conjSubgroup_sup', conjSubgroup_commutator, hc.conj_Q_eq hg, hc.conj_Z_eq hg, hz]
      _ = V := h2
  have hVconj : ∀ v ∈ V, g⁻¹ * v * g ∈ V := fun v hv => by
    have : v ∈ conjSubgroup g V := by rw [hVg]; exact hv
    exact mem_conjSubgroup.mp this
  have hVconj' : ∀ v ∈ V, g * v * g⁻¹ ∈ V := fun v hv => by
    have : g * v * g⁻¹ ∈ conjSubgroup g V := mem_conjSubgroup.mpr (by simpa [mul_assoc] using hv)
    rwa [hVg] at this
  have hQ0 : ∀ q ∈ Q, ∀ s ∈ Z0, ⁅q, s⁆ ∈ V := by
    intro q hq s hs
    by_cases hsQ : s ∈ Q
    · exact hZV (hc.hyp.special.1 ▸ Subgroup.commutator_mem_commutator hq hsQ)
    · rw [← hcentre s hs hsQ]
      exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers s))
  have hCN0 : ∀ s ∈ Z0, ∀ v ∈ V, ⁅s, v⁆ ∈ Z := fun s hs v hv => (Ctx.mem_CN.mp (hZ0N hs)).2 v hv
  have hAM : ∀ x ∈ conjSubgroup g Z0, x ∈ M := fun x hx => by
    have h := hZ0M (mem_conjSubgroup.mp hx)
    have := M.mul_mem (M.mul_mem hg h) (M.inv_mem hg)
    simpa [mul_assoc] using this
  have hcomm : ∀ x ∈ conjSubgroup g Z0, ∀ y ∈ Z0, ⁅x, y⁆ ∈ Q := by
    intro x hx y hy
    have key := sec93f_comm_comm_mem (Z := Z) (V := V) (A := conjSubgroup g Z0) (B := Z0) (C := Q)
      (fun x hx a ha => hZn x (hAM x hx) a ha) (fun x hx a ha => hZn x (hZ0M hx) a ha)
      (fun x hx a ha => hZn x (hQM hx) a ha)
      (fun x hx v hv => by
        have hz0 : g⁻¹ * x * g ∈ Z0 := mem_conjSubgroup.mp hx
        have h1 := hCN0 _ hz0 _ (hVconj v hv)
        have h2 := hZn g hg _ h1
        have e : g * ⁅g⁻¹ * x * g, g⁻¹ * v * g⁆ * g⁻¹ = ⁅x, v⁆ := by
          simp only [commutatorElement_def]; group
        rwa [e] at h2)
      (fun x hx v hv => hCN0 x hx v hv)
      (fun q hq x hx => by
        have hz0 : g⁻¹ * x * g ∈ Z0 := mem_conjSubgroup.mp hx
        have h1 := hQ0 (g⁻¹ * q * g) (by simpa using hQn g⁻¹ (M.inv_mem hg) q hq) _ hz0
        have h2 := hVconj' _ h1
        have e : g * ⁅g⁻¹ * q * g, g⁻¹ * x * g⁆ * g⁻¹ = ⁅q, x⁆ := by
          simp only [commutatorElement_def]; group
        rwa [e] at h2)
      (fun q hq x hx => hQ0 q hq x hx)
    have hxM := hAM x hx
    have hyM := hZ0M hy
    refine hc.hyp.centralizer_Qt _ ?_ (fun z hz => key x hx y hy z hz)
    simpa [commutatorElement_def] using
      M.mul_mem (M.mul_mem (M.mul_mem hxM hyM) (M.inv_mem hxM)) (M.inv_mem hyM)
  have hle : conjSubgroup g Z0 ≤ Z0 := by
    have hall := hwc g hg (fun x hx y hy =>
      hcomm (g * x * g⁻¹) (mem_conjSubgroup.mpr (by simpa [mul_assoc] using hx)) y hy)
    intro x hx
    have hz0 : g⁻¹ * x * g ∈ Z0 := mem_conjSubgroup.mp hx
    have h2 := hall _ hz0
    simpa [mul_assoc] using h2
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])

end Main

end CFSG.RankThree.GF2n.Stroth80
