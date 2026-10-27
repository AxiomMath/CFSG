module

public import CFSG.Quasithin.Recognition.SzVBEvenGeo1
public import CFSG.Quasithin.Recognition.SzVBEvenGeo2
public import CFSG.Quasithin.Recognition.SzVBEvenVertex
public import CFSG.Quasithin.Recognition.SzVBEvenCore

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T V : Subgroup G} {z : G}

theorem even_critDist_false (hC : EvenCtx G₀ G₁ G₂ T V z) (hev : Even (critDist G₀ G₁ G₂ V))
    (hb : 3 ≤ critDist G₀ G₁ G₂ V) : False := by
  obtain ⟨p, hp, hp0, hp1, hcrit⟩ := exists_crit_geodesic hC.toGeoCtx
  have hN := hC.hyp.normalizes
  have hG := hC.hyp.gen
  set b := critDist G₀ G₁ G₂ V with hbdef
  have hbmod : b % 2 = 0 := Nat.even_iff.mp hev
  have h0 : vtype (p 0) = false := by rw [hp0]; exact vtype_γ₀
  have hvu : vtype (p (b - 1)) = true := by
    have h := vtype_geo_false_iff hC.toGeoCtx hp h0 (i := b - 1) (by omega)
    have hne : ¬ Even (b - 1) := by rw [Nat.even_iff]; omega
    cases hv : vtype (p (b - 1))
    · exact absurd (h.mp hv) hne
    · rfl
  have hadj : (graph G₀ G₁ G₂).Adj (p (b - 2)) (p (b - 1)) := by
    have := hp.adj (i := b - 2) (by omega)
    rwa [show b - 2 + 1 = b - 1 by omega] at this
  have hvδ : vtype (p (b - 2)) = false := by
    have h := vtype_geo_false_iff hC.toGeoCtx hp h0 (i := b - 2) (by omega)
    exact h.mpr (by rw [Nat.even_iff]; omega)
  obtain ⟨β, hβadj, hβne, hβnot⟩ := exists_nbr_not_le_pCoreOf_u hC.toGeoCtx hev hb hp hp0 hp1 hcrit
  have hvβ : vtype β = true := by
    have h := vtype_ne_of_adj hβadj
    rw [vtype_γ₀] at h
    cases hv : vtype β
    · exact absurd hv.symm h
    · rfl
  obtain ⟨P, S, Vu, zu, hPs, hPV, -, hK, hB⟩ := exists_vertexData hC hvu
  obtain ⟨P', S', Vb, zb, hPs', hPV', hPz', hK', hB'⟩ := exists_vertexData hC hvβ
  subst hPs hPs'
  have hWP : Vv V β ≤ stab (p (b - 1)) := by
    refine (Vv_B_le_iff hvβ).mpr fun x hx => ?_
    have hvx : vtype x = false := vtype_eq_false_of_adj hx hvβ
    have hxd : dist x (γ₀ G₀ G₁ G₂) ≤ 2 := by
      have h1 := dist_triangle hG x β (γ₀ G₀ G₁ G₂)
      have h2 : dist x β = 1 := dist_eq_one_iff_adj.mpr hx.symm
      have h3 : dist β (γ₀ G₀ G₁ G₂) = 1 := dist_eq_one_iff_adj.mpr hβadj.symm
      omega
    have h1 := Vv_le_pCoreOf_delta hC.toGeoCtx hev hb hp hp0 hp1 hcrit hvx hxd
    rw [← ballStab_one_eq_pCoreOf hC.toGeoCtx] at h1
    exact h1.trans (ballStab_le_stab_of_dist_le (dist_eq_one_iff_adj.mpr hadj).le)
  have hWabelβ : IsElemAbelian 2 (Vv V β) := isElemAbelian_Vv_of_vtype hC.toGeoCtx hvβ hb
  have hWabelu : IsElemAbelian 2 (Vv V (p (b - 1))) := isElemAbelian_Vv_of_vtype hC.toGeoCtx hvu hb
  refine even_case_false hK hB hK' hB' ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← hPV]; exact hWabelu
  · rw [← hPV']; exact hWabelβ
  · rw [← hPV']; exact hWP
  · rw [← hPV', ← hPV]
    exact hWP.trans (stab_le_normalizer_Vv hN _)
  ·
    by_contra hcon
    push Not at hcon
    apply hβnot
    intro w hw
    have hwP : w ∈ stab (p (b - 1)) := hWP hw
    have hker := hcon w (by rw [← hPV']; exact hw) hwP
    have hsq : (⟨w, hwP⟩ : ↥(stab (p (b - 1)))) * ⟨w, hwP⟩ = 1 := by
      have := F7.isElemAbelian_pow_eq_one hWabelβ hw
      exact Subtype.ext (by simpa [pow_two] using this)
    exact hB.ker_inv_le _ hsq hker
  ·
    rw [← hPV]
    obtain ⟨-, h2⟩ := relIndex_Vv_u hC.toGeoCtx hev hb hp hp0
    have hle : pCoreOf 2 (stab (γ₀ G₀ G₁ G₂)) ≤ stab β := by
      rw [← ballStab_one_eq_pCoreOf hC.toGeoCtx]
      exact ballStab_le_stab_of_dist_le (dist_eq_one_iff_adj.mpr hβadj).le
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.relIndex_dvd_of_le_left _ hle)).trans h2
  ·
    intro hz
    have hzb : zb ∈ Zv z β := by rw [hPz']; exact Subgroup.mem_zpowers zb
    have hZV : Zv z β ≤ V := by
      have := Zv_le_Vv_of_adj (V := V) (z := z) hC.klein.z_mem hN
        (G₂_le_normalizer_zpowers hC.toGeoCtx) hβadj (vtype_γ₀)
      rwa [Vv_γ₀ hN] at this
    have hA' : zb ∈ V ⊓ Vv V (p (b - 1)) := ⟨hZV hzb, by rw [hPV]; exact hz⟩
    rw [inf_Vv_u_eq_Zv hC.toGeoCtx hev hb hp hp0 hp1 hcrit] at hA'
    have hle : Zv z β ≤ Zv z (γ₁ G₀ G₁ G₂) := by
      rw [hPz']; exact Subgroup.zpowers_le.mpr hA'
    have heq : Zv z β = Zv z (γ₁ G₀ G₁ G₂) := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [card_Zv hC.toGeoCtx hvβ, card_Zv hC.toGeoCtx (vtype_γ₁)]
    exact Zv_ne_of_adj hC.toGeoCtx (vtype_γ₀) hβadj adj_γ₀_γ₁ hβne heq

end CFSG.Quasithin.SzVB
