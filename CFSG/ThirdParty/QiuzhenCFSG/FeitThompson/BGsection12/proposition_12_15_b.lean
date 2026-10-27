module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.proposition_12_15_a

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# proposition_12_15_b
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [IsMinCE G] in
private theorem CFSG.section12_inf_sylow_eq_sylow_of_normalizer_le
    {M Mstar : Subgroup G} {q : Nat.Primes}
    {S : Sylow q.val (M ⊓ Mstar : Subgroup G)}
    (T : Sylow q.val M)
    (hPamb_le_T :
      section10AmbientSylowSubgroup (M ⊓ Mstar) S ≤
        section10AmbientSylowSubgroup M T)
    (hnorm_le_Mstar :
      Subgroup.normalizer
        ((section10AmbientSylowSubgroup (M ⊓ Mstar) S : Subgroup G) : Set G) ≤
          Mstar) :
    section10AmbientSylowSubgroup (M ⊓ Mstar) S =
      section10AmbientSylowSubgroup M T := by
  classical
  have : Fact q.val.Prime := ⟨q.property⟩
  let Pamb : Subgroup G := section10AmbientSylowSubgroup (M ⊓ Mstar) S
  let TG : Subgroup G := section10AmbientSylowSubgroup M T
  let K : Subgroup TG := Pamb.subgroupOf TG
  have hKmap : section8SubgroupInAmbient K = Pamb := by
    change K.map TG.subtype = Pamb
    dsimp [K]
    exact Subgroup.map_subgroupOf_eq_of_le hPamb_le_T
  let Nloc : Subgroup TG := Subgroup.normalizer (K : Set TG)
  let Namb : Subgroup G := Nloc.map TG.subtype
  have hTGp : IsPGroup q.val TG := by
    change IsPGroup q.val ((T : Subgroup M).map M.subtype)
    exact IsPGroup.map T.isPGroup' M.subtype
  have hNamb_p : IsPGroup q.val Namb := by
    have hNloc_p : IsPGroup q.val Nloc := hTGp.to_subgroup Nloc
    exact IsPGroup.map hNloc_p TG.subtype
  have hNamb_le_inf : Namb ≤ M ⊓ Mstar := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyN, rfl⟩
    constructor
    · rcases y with ⟨y, hyTG⟩
      rcases Subgroup.mem_map.mp hyTG with ⟨ym, _hymT, rfl⟩
      exact ym.property
    · have hy_normPamb : (y : G) ∈ Subgroup.normalizer (Pamb : Set G) := by
        have hy_map : (y : G) ∈ (Subgroup.normalizer (K : Set TG)).map TG.subtype :=
          Subgroup.mem_map_of_mem TG.subtype hyN
        have hnorm_map :
            (Subgroup.normalizer (K : Set TG)).map TG.subtype ≤
              Subgroup.normalizer (section8SubgroupInAmbient K : Set G) :=
          section8_normalizer_subgroupInAmbient_le K
        simpa [hKmap] using hnorm_map hy_map
      exact hnorm_le_Mstar hy_normPamb
  have hPamb_le_Namb : Pamb ≤ Namb := by
    have hK_le_Nloc : K ≤ Nloc := Subgroup.le_normalizer
    have hKmap_le : section8SubgroupInAmbient K ≤ Namb := by
      change K.map TG.subtype ≤ Nloc.map TG.subtype
      exact Subgroup.map_mono hK_le_Nloc
    simpa [hKmap] using hKmap_le
  let Nsub : Subgroup (M ⊓ Mstar : Subgroup G) := Namb.subgroupOf (M ⊓ Mstar)
  have hNsub_p : IsPGroup q.val Nsub := by
    let e : Nsub ≃* Namb := Subgroup.subgroupOfEquivOfLe hNamb_le_inf
    exact hNamb_p.of_equiv e.symm
  have hS_le_Nsub : (S : Subgroup (M ⊓ Mstar : Subgroup G)) ≤ Nsub := by
    intro y hy
    have hyPamb : (y : G) ∈ Pamb := by
      exact Subgroup.mem_map_of_mem (M ⊓ Mstar : Subgroup G).subtype hy
    simpa [Nsub, Subgroup.mem_subgroupOf] using hPamb_le_Namb hyPamb
  have hNsub_eq : Nsub = (S : Subgroup (M ⊓ Mstar : Subgroup G)) :=
    S.is_maximal' hNsub_p hS_le_Nsub
  have hNamb_le_Pamb : Namb ≤ Pamb := by
    intro x hx
    have hxinf : x ∈ M ⊓ Mstar := hNamb_le_inf hx
    let xi : (M ⊓ Mstar : Subgroup G) := ⟨x, hxinf⟩
    have hxiN : xi ∈ Nsub := by
      simpa [Nsub, Subgroup.mem_subgroupOf, xi] using hx
    have hxiS : xi ∈ (S : Subgroup (M ⊓ Mstar : Subgroup G)) := by
      simpa [hNsub_eq] using hxiN
    exact Subgroup.mem_map.mpr ⟨xi, hxiS, rfl⟩
  have hNloc_le_K : Nloc ≤ K := by
    intro y hy
    have hyNamb : (y : G) ∈ Namb := Subgroup.mem_map_of_mem TG.subtype hy
    exact hNamb_le_Pamb hyNamb
  have hNloc_eq : Nloc = K := le_antisymm hNloc_le_K Subgroup.le_normalizer
  have hnc : NormalizerCondition TG := by
    let : Group.IsNilpotent TG := IsPGroup.isNilpotent (p := q.val) (G := TG) hTGp
    exact Group.normalizerCondition_of_isNilpotent (G := TG)
  have hKtop : K = ⊤ :=
    normalizerCondition_iff_only_full_group_self_normalizing.mp hnc K (by
      simpa [Nloc] using hNloc_eq)
  have hTG_le_Pamb : TG ≤ Pamb := by
    intro x hx
    have hxK : (⟨x, hx⟩ : TG) ∈ K := by
      simp [hKtop]
    simpa [K, Subgroup.mem_subgroupOf] using hxK
  exact le_antisymm hPamb_le_T hTG_le_Pamb

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_conjBy_eq_of_mem_normalizer
    {H : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    H.conjBy g = H := by
  ext x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).1 hy
  · intro hx
    refine Subgroup.mem_map.mpr ?_
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · have hgInv : g⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
        (Subgroup.normalizer (H : Set G)).inv_mem hg
      simpa [mul_assoc] using (Subgroup.mem_normalizer_iff.mp hgInv x).1 hx
    · simp [MulAut.conj_apply, mul_assoc]

/-- Proposition 12.15(b). -/
public theorem CFSG.proposition_12_15_b
    {M Mstar X : Subgroup G} {q : Nat.Primes}
    {S : Sylow q.val (M ⊓ Mstar : Subgroup G)}
    (hM : M ∈ section9MaximalSubgroups G)
    (hq : q ∈ section10SigmaPrimes M)
    (_hX : X ≤ M) (_hXne : X ≠ ⊥) (_hXq : IsPGroup q.val X)
    (hMstar : Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)))
    (_hMstar_ne : Mstar ≠ M)
    (hXS : X ≤ section10AmbientSylowSubgroup (M ⊓ Mstar) S) :
    Subgroup.normalizer ((section10AmbientSylowSubgroup (M ⊓ Mstar) S : Subgroup G) : Set G) ≤ M := by
  classical
  have : Fact q.val.Prime := ⟨q.property⟩
  let Pamb : Subgroup G := section10AmbientSylowSubgroup (M ⊓ Mstar) S
  have hPamb_p : IsPGroup q.val Pamb := by
    change IsPGroup q.val
      ((S : Subgroup (M ⊓ Mstar : Subgroup G)).map (M ⊓ Mstar : Subgroup G).subtype)
    exact IsPGroup.map S.isPGroup' (M ⊓ Mstar : Subgroup G).subtype
  have hPamb_le_M : Pamb ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.2.1
  by_cases hPcyc : IsCyclic Pamb
  · have : IsCyclic Pamb := hPcyc
    have hXchar : (X.subgroupOf Pamb).Characteristic :=
      section12_subgroup_characteristic_of_cyclic (X.subgroupOf Pamb)
    have hnormP_le_normX :
        Subgroup.normalizer (Pamb : Set G) ≤ Subgroup.normalizer (X : Set G) := by
      have hnormP_le_normXmap :
          Subgroup.normalizer (Pamb : Set G) ≤
            Subgroup.normalizer ((X.subgroupOf Pamb).map Pamb.subtype : Set G) := by
        simpa [Pamb] using
          (section8_normalizer_map_subtype_le_of_characteristic
            (H := Pamb) (K := X.subgroupOf Pamb))
      have hXmap : (X.subgroupOf Pamb).map Pamb.subtype = X :=
        Subgroup.map_subgroupOf_eq_of_le hXS
      simpa [hXmap] using hnormP_le_normXmap
    have hnormP_le_Mstar : Subgroup.normalizer (Pamb : Set G) ≤ Mstar :=
      hnormP_le_normX.trans hMstar.2
    have hPsub_p : IsPGroup q.val (Pamb.subgroupOf M) := by
      let e : Pamb.subgroupOf M ≃* Pamb := Subgroup.subgroupOfEquivOfLe hPamb_le_M
      exact hPamb_p.of_equiv e.symm
    obtain ⟨T, hPsub_le_T⟩ := IsPGroup.exists_le_sylow (G := M) (p := q.val) hPsub_p
    have hPamb_le_T :
        Pamb ≤ section10AmbientSylowSubgroup M T := by
      intro x hx
      exact Subgroup.mem_map.mpr
        ⟨⟨x, hPamb_le_M hx⟩, hPsub_le_T (by simpa [Subgroup.mem_subgroupOf] using hx), rfl⟩
    have hPamb_eq_T :
        Pamb = section10AmbientSylowSubgroup M T :=
      section12_inf_sylow_eq_sylow_of_normalizer_le
        (G := G) (M := M) (Mstar := Mstar) (q := q) (S := S) T
        (by simpa [Pamb] using hPamb_le_T)
        (by simpa [Pamb] using hnormP_le_Mstar)
    intro g hg
    have hgT :
        g ∈ Subgroup.normalizer ((section10AmbientSylowSubgroup M T : Subgroup G) : Set G) := by
      simpa [← hPamb_eq_T, Pamb] using hg
    have hconj :
        (section10AmbientSylowSubgroup M T).conjBy g =
          section10AmbientSylowSubgroup M T :=
      section12_conjBy_eq_of_mem_normalizer hgT
    exact theorem_10_1_d (G := G) (M := M) (p := q) hM hq T (by
      rw [hconj]
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.property)
  · exact corollary_12_10_d (G := G) (M := M) (P := Pamb) (p := q)
      hM hq hPamb_p hPamb_le_M hPcyc

end Section12
