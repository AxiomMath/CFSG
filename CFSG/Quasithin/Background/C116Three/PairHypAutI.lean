module

public import CFSG.Quasithin.Background.C116Three.GroupDefs
public import CFSG.Quasithin.Background.B2FactorizationR2
public import CFSG.Quasithin.Background.C116Three.ModuleDefs

public section

namespace CFSG.Quasithin.C116Three

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.R3c23 CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem C116_map_conj_map_conj (K : Subgroup G) (g h : G) :
    (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      K.map (MulAut.conj (h * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem C116_autI_map_conj {V : Subgroup G} (hV : IsElemAbelian 2 V) (K : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) :
    autI hV (K.map (MulAut.conj g).toMonoidHom) =
      (autI hV K).map (MulAut.conj (convI hV ⟨g, hg⟩)).toMonoidHom := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨h, hh, rfl⟩ := (mem_autI hV).1 hφ
    obtain ⟨k, hk, hkh⟩ := Subgroup.mem_map.1 hh
    have hkN : k ∈ Subgroup.normalizer (V : Set G) := by
      have e : k = g⁻¹ * (h : G) * g := by
        have hkh' : g * k * g⁻¹ = (h : G) := hkh
        rw [← hkh']
        group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hg) h.2) hg
    refine Subgroup.mem_map.2 ⟨convI hV ⟨k, hkN⟩, convI_mem_autI hV hk hkN, ?_⟩
    have e2 : (⟨g, hg⟩ * ⟨k, hkN⟩ * (⟨g, hg⟩)⁻¹ : Subgroup.normalizer (V : Set G)) = h :=
      Subtype.ext hkh
    show convI hV ⟨g, hg⟩ * convI hV ⟨k, hkN⟩ * (convI hV ⟨g, hg⟩)⁻¹ = convI hV h
    rw [← e2, map_mul, map_mul, map_inv]
  · intro hφ
    obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.1 hφ
    obtain ⟨k, hk, rfl⟩ := (mem_autI hV).1 hψ
    have hgk : g * (k : G) * g⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      mul_mem (mul_mem hg k.2) (inv_mem hg)
    refine (mem_autI hV).2 ⟨⟨g * (k : G) * g⁻¹, hgk⟩, Subgroup.mem_map.2 ⟨(k : G), hk, rfl⟩, ?_⟩
    have e3 : (⟨g * (k : G) * g⁻¹, hgk⟩ : Subgroup.normalizer (V : Set G)) =
        ⟨g, hg⟩ * k * (⟨g, hg⟩)⁻¹ :=
      Subtype.ext rfl
    show convI hV ⟨g * (k : G) * g⁻¹, hgk⟩ = convI hV ⟨g, hg⟩ * convI hV k * (convI hV ⟨g, hg⟩)⁻¹
    rw [e3, map_mul, map_mul, map_inv]

theorem C116_autI_comm {V : Subgroup G} (hV : IsElemAbelian 2 V) {L L' : Subgroup G}
    (hc : ⁅L, L'⁆ ≤ Subgroup.centralizer (V : Set G)) :
    ∀ a ∈ autI hV L, ∀ b ∈ autI hV L', a * b = b * a := by
  intro a ha b hb
  obtain ⟨x, hx, rfl⟩ := (mem_autI hV).1 ha
  obtain ⟨y, hy, rfl⟩ := (mem_autI hV).1 hb
  have e : ((⁅x, y⁆ : Subgroup.normalizer (V : Set G)) : G) = ⁅(x : G), (y : G)⁆ := rfl
  have hcent : ((⁅x, y⁆ : Subgroup.normalizer (V : Set G)) : G) ∈
      Subgroup.centralizer (V : Set G) := by
    rw [e]
    exact hc (Subgroup.commutator_mem_commutator hx hy)
  have h1 : convI hV ⁅x, y⁆ = 1 := (convI_eq_one_iff hV _).2 hcent
  rw [map_commutatorElement] at h1
  exact commutatorElement_eq_one_iff_mul_comm.1 h1

theorem C116_autI_sup_map_conj_le {V : Subgroup G} (hV : IsElemAbelian 2 V) {H L : Subgroup G}
    {t : G} (htH : t ∈ H)
    (hdich : ∀ x ∈ H, L.map (MulAut.conj x).toMonoidHom = L ∨
      L.map (MulAut.conj x).toMonoidHom = L.map (MulAut.conj t).toMonoidHom)
    {x : MulAut (IntMod V hV)} (hx : x ∈ autI hV H) :
    (autI hV L ⊔ autI hV (L.map (MulAut.conj t).toMonoidHom)).map
        (MulAut.conj x).toMonoidHom ≤
      autI hV L ⊔ autI hV (L.map (MulAut.conj t).toMonoidHom) := by
  obtain ⟨h, hh, rfl⟩ := (mem_autI hV).1 hx
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rw [← C116_autI_map_conj hV L h.2]
    rcases hdich h hh with e | e
    · rw [e]; exact le_sup_left
    · rw [e]; exact le_sup_right
  · rw [← C116_autI_map_conj hV _ h.2, C116_map_conj_map_conj]
    rcases hdich ((h : G) * t) (H.mul_mem hh htH) with e | e
    · rw [e]; exact le_sup_left
    · rw [e]; exact le_sup_right

theorem pairHyp_autI {H T V L : Subgroup G} {t : G} (hVred : IsTwoReducedIn H V)
    (hT : IsSylowTwoOf T H) (hL : L ∈ cComp H) (hq : QuasiData V L) (P : GroupPair H T L t) :
    PairHyp (autI hVred.2.2.1 H) (autI hVred.2.2.1 L)
      (autI hVred.2.2.1 (L.map (MulAut.conj t).toMonoidHom))
      (convI hVred.2.2.1 ⟨t, hVred.2.1 (hT.1 P.tT)⟩) := by
  have hVe : IsElemAbelian 2 V := hVred.2.2.1
  have hLH : L ≤ H := le_of_mem_cComp hL
  have hLtH : L.map (MulAut.conj t).toMonoidHom ≤ H := le_of_mem_cComp P.hLt
  have htH : t ∈ H := hT.1 P.tT
  have htN : t ∈ Subgroup.normalizer (V : Set G) := hVred.2.1 htH
  have hLN : L ≤ Subgroup.normalizer (V : Set G) := hLH.trans hVred.2.1
  obtain ⟨Q, hQg, φ, hφs, hφk, hQ⟩ := hq
  have hker : (convHom hVe L hLN).ker = φ.ker := by
    rw [ker_convHom, hφk]
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf, x.2]
  let e : ↥(autI hVe L) ≃* Q :=
    ((MulEquiv.subgroupCongr (range_convHom hVe L hLN).symm).trans
      (QuotientGroup.quotientKerEquivRange (convHom hVe L hLN)).symm).trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective φ hφs))
  have hq1 : CFSG.IsQuasisimple ↥(autI hVe L) := CFSG.IsQuasisimple.of_mulEquiv e hQ
  have hconj := C116_autI_map_conj hVe L htN
  refine ⟨convI_mem_autI hVe htH htN, autI_mono hVe hLH, autI_mono hVe hLtH, hconj, hq1, ?_, ?_, ?_⟩
  · rw [hconj]
    exact CFSG.IsQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective (autI hVe L) (MulAut.conj (convI hVe ⟨t, htN⟩)).toMonoidHom
        (MulAut.conj (convI hVe ⟨t, htN⟩)).injective).symm hq1
  · exact C116_autI_comm hVe ((P.comm).trans (pCoreOf_le_centralizer_of_isTwoReducedIn hVred))
  · intro x hx l hl
    exact C116_autI_sup_map_conj_le hVe htH P.dich hx (Subgroup.mem_map_of_mem _ hl)

end CFSG.Quasithin.C116Three
