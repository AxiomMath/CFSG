module

public import CFSG.Quasithin.EmptyFaithful.S153TDef
public import CFSG.Quasithin.EmptyFaithful.S1469CaseA0
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace S153T

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem card_le_of_isSylowTwoOf {S H P : Subgroup G} (hS : IsSylowTwoOf S H) (hP : IsPGroup 2 P)
    (hPH : P ≤ H) : Nat.card P ≤ Nat.card S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS' : IsPGroup 2 (S.subgroupOf H) := hS.2.1.comap_of_injective _ Subtype.val_injective
  let Sy : Sylow 2 ↥H := hS'.toSylow hS.2.2
  have hP' : IsPGroup 2 (P.subgroupOf H) := hP.comap_of_injective _ Subtype.val_injective
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  have h1 : Nat.card Q = Nat.card Sy := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have h2 : Nat.card (P.subgroupOf H) ≤ Nat.card Q := Subgroup.card_le_of_le hQ
  have e1 : Nat.card (P.subgroupOf H) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv
  have e2 : Nat.card (S.subgroupOf H) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv
  have e3 : Nat.card Sy = Nat.card (S.subgroupOf H) := rfl
  omega

theorem normalizer_tU_inf_mcOf (S : Setting146 G T M) (h2 : Stage1463Two) {H : Subgroup G}
    (hH : IsHTM T M H) {u : G} (hu : IsInvU T M H u) :
    Subgroup.normalizer (tU T u : Set G) ⊓ mcOf T = tZero T u := by
  obtain ⟨-, -, hT0N, hT0Q, -⟩ := S.stage1463_one hH hu
  have hN0 := h2 G T M S H hH u hu
  apply le_antisymm
  · rintro x ⟨hxN, hxG⟩
    have hxQ : x ∈ Subgroup.normalizer (pCoreOf 2 (mcOf T) : Set G) :=
      le_normalizer_pCoreOf 2 (mcOf T) hxG
    have hxT0 : x ∈ Subgroup.normalizer (tZero T u : Set G) := by
      rw [hT0Q]
      exact F1.le_normalizer_sup (X := Subgroup.zpowers x) (Subgroup.zpowers_le.mpr hxQ)
        (Subgroup.zpowers_le.mpr hxN) (Subgroup.mem_zpowers x)
    rw [hN0] at hxT0
    rw [hT0N]
    exact ⟨hxT0, hxN⟩
  · intro x hx
    exact ⟨S.tZero_le_normalizer_tU hH hu hx,
      le_centralizer_quasithinOmegaOneCenter T (S146T.tZero_le T u hx)⟩

theorem isSylowTwoOf_tZero (S : Setting146 G T M) (h2 : Stage1463Two) {H : Subgroup G}
    (hH : IsHTM T M H) {u : G} (hu : IsInvU T M H u) :
    IsSylowTwoOf (tZero T u) (Subgroup.normalizer (tU T u : Set G)) := by
  obtain ⟨-, -, hT0N, -, -⟩ := S.stage1463_one hH hu
  have hN0 := h2 G T M S H hH u hu
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  refine isSylowTwoOf_of_forall_normalizer (S.tZero_le_normalizer_tU hH hu)
    (hT2.to_le (S146T.tZero_le T u)) ?_
  intro x hx hxN _
  rw [hN0] at hxN
  rw [hT0N]
  exact ⟨hxN, hx⟩


theorem V_le_centralizer_tU (S : Setting146 G T M) {u : G} {n : G}
    (hnI : n ∈ Subgroup.normalizer (tU T u : Set G)) (hnM : n ∈ M) (hnG : n ∉ mcOf T) :
    VZ T M ≤ Subgroup.centralizer (tU T u : Set G) := by
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp S.hyp1281.omegaOneCenter_ne_bot
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hZV : quasithinOmegaOneCenter T ≤ VZ T M := le_conjClosure _ _
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_conjClosure _ _
  have hz'V : n * z * n⁻¹ ∈ VZ T M := (Subgroup.mem_normalizer_iff.mp (hMV hnM) z).mp (hZV hzZ)
  have hz'1 : n * z * n⁻¹ ≠ 1 := by
    intro h
    apply hz1'
    have : z = n⁻¹ * (n * z * n⁻¹) * n := by group
    rw [this, h]
    group
  have hz'z : n * z * n⁻¹ ≠ z := by
    intro h
    apply hnG
    rw [S.mcOf_eq_centralizer hzZ hz1']
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc n * z = (n * z * n⁻¹) * n := by group
      _ = z * n := by rw [h]
  have hz'Z : n * z * n⁻¹ ∉ quasithinOmegaOneCenter T := by
    intro h
    exact hz'z (S.Z_eq_of_iff h hzZ ⟨fun h1 => absurd h1 hz'1, fun h1 => absurd h1 hz1'⟩)
  have hZc : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (tU T u : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun t ht => S146T.comm_Z_T ht.1 hx
  have hz'c : n * z * n⁻¹ ∈ Subgroup.centralizer (tU T u : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun t ht => ?_
    have ht' : n⁻¹ * t * n⁻¹⁻¹ ∈ tU T u := (Subgroup.mem_normalizer_iff.mp (inv_mem hnI) t).mp ht
    have hc := S146T.comm_Z_T ht'.1 hzZ
    simp only [inv_inv] at hc
    calc t * (n * z * n⁻¹) = n * ((n⁻¹ * t * n) * z) * n⁻¹ := by group
      _ = n * (z * (n⁻¹ * t * n)) * n⁻¹ := by rw [hc]
      _ = (n * z * n⁻¹) * t := by group
  intro v hv
  by_cases hvZ : v ∈ quasithinOmegaOneCenter T
  · exact hZc hvZ
  · have h1 : v * (n * z * n⁻¹)⁻¹ ∈ quasithinOmegaOneCenter T :=
      S146T.mul_inv_mem_of_card hZV S.hyp.rank_two S.card_Z hv hz'V hvZ hz'Z
    have h2 : v = (v * (n * z * n⁻¹)⁻¹) * (n * z * n⁻¹) := by group
    rw [h2]
    exact Subgroup.mul_mem _ (hZc h1) hz'c

theorem false_of_V_le_centralizer_tU (S : Setting146 G T M) (h3 : Stage1463Three) {H : Subgroup G}
    (hH : IsHTM T M H) {u : G} (hu : IsInvU T M H u)
    (hV : VZ T M ≤ Subgroup.centralizer (tU T u : Set G)) : False := by
  apply (h3 G T M S H hH u hu).1
  intro q hq
  have hqT : q ∈ T :=
    pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hH.1.1) hq.1
  have hqU : q ∈ tU T u := ⟨hqT, hq.2⟩
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact ((Subgroup.mem_centralizer_iff.mp (hV hv)) q hqU).symm

theorem VZ_le_tU (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H) {u : G}
    (hu : IsInvU T M H u) : VZ T M ≤ tU T u := by
  have h91 := (S.lemma_14_5_14 (S.isHz_iff.mpr hH)).2.toHypF91
  have hUQ : conjClosure (VZ T M) H ≤ pCoreOf 2 H := h91.conjClosure_Vp_le_pCoreOf
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) H) := S.lemma_14_5_15_two hH
  have hOT : pCoreOf 2 H ≤ T :=
    pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hH.1.1)
  intro v hv
  have hvU : v ∈ conjClosure (VZ T M) H := le_conjClosure _ _ hv
  exact ⟨hOT (hUQ hvU), Subgroup.mem_centralizer_singleton_iff.mpr (F7.isElemAbelian_comm hUab hvU hu.mem)⟩

theorem star (S : Setting146 G T M) (h2 : Stage1463Two) (h3 : Stage1463Three) {H : Subgroup G}
    (hH : IsHTM T M H) {u : G} (hu : IsInvU T M H u) {C : Subgroup G} (hCT0 : C ≤ tZero T u)
    (hC1 : C ≠ ⊥) (hTC : T ≤ Subgroup.normalizer (C : Set G)) :
    Subgroup.normalizer (tU T u : Set G) ⊓ Subgroup.normalizer (C : Set G) ≤ tZero T u := by
  rintro g ⟨hgI, hgC⟩
  by_contra hgT0
  have hgG : g ∉ mcOf T := by
    intro hg
    exact hgT0 (normalizer_tU_inf_mcOf S h2 hH hu ▸ ⟨hgI, hg⟩)
  have hC2 : IsPGroup 2 C := S.hyp.sylow.1.to_le (hCT0.trans (S146T.tZero_le T u))
  have hloc : pCoreOf 2 (Subgroup.normalizer (C : Set G)) ≠ ⊥ := by
    intro hb
    exact hC1 (le_bot_iff.mp ((le_pCoreOf_normalizer 2 C hC2).trans hb.le))
  obtain ⟨K, hK⟩ := exists_inM_of_pCoreOf_ne_bot hloc
  have hKT : InM T K := ⟨hK.1, hTC.trans hK.2⟩
  rcases S.hyp.inM_iff.mp hKT with hKM | hKG
  · have hgM : g ∈ M := by
      rw [← hKM]
      exact hK.2 hgC
    exact false_of_V_le_centralizer_tU S h3 hH hu (V_le_centralizer_tU S hgI hgM hgG)
  · have hgK : g ∈ K := hK.2 hgC
    rw [hKG] at hgK
    exact hgG hgK


theorem pCoreOf_normalizer_tU (S : Setting146 G T M) (h2 : Stage1463Two) {H : Subgroup G}
    (hH : IsHTM T M H) {u : G} (hu : IsInvU T M H u)
    (hI : ¬ Subgroup.normalizer (tU T u : Set G) ≤ mcOf T) :
    pCoreOf 2 (Subgroup.normalizer (tU T u : Set G)) = tU T u := by
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hTu2 : IsPGroup 2 (tU T u) := hT2.to_le inf_le_left
  have hSyl := isSylowTwoOf_tZero S h2 hH hu
  have hle1 : tU T u ≤ pCoreOf 2 (Subgroup.normalizer (tU T u : Set G)) :=
    le_pCoreOf_normalizer 2 (tU T u) hTu2
  have hle2 : pCoreOf 2 (Subgroup.normalizer (tU T u : Set G)) ≤ tZero T u :=
    pCoreOf_two_le_of_isSylowTwoOf hSyl
  have hne : pCoreOf 2 (Subgroup.normalizer (tU T u : Set G)) ≠ tZero T u := by
    intro h
    apply hI
    have h1 := le_normalizer_pCoreOf 2 (Subgroup.normalizer (tU T u : Set G))
    rw [h, h2 G T M S H hH u hu] at h1
    exact h1.trans (le_centralizer_quasithinOmegaOneCenter T)
  rcases eq_or_eq_of_relIndex_two hle1 hle2 (S.relIndex_tU_tZero hH hu) with h | h
  · exact h
  · exact absurd h hne

theorem charTwo_normalizer_tU (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H) {u : G}
    (hu : IsInvU T M H u) : CharTwo (Subgroup.normalizer (tU T u : Set G)) := by
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp S.hyp1281.omegaOneCenter_ne_bot
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hTu2 : IsPGroup 2 (tU T u) := hT2.to_le inf_le_left
  have huG : u ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hH hu.mem
  have hzU : z ∈ tU T u :=
    ⟨S146T.Z_le hzZ, Subgroup.mem_centralizer_singleton_iff.mpr (S146T.comm_Z huG hzZ).symm⟩
  have hzc : z ∈ T ⊓ Subgroup.centralizer (T : Set G) := quasithinOmegaOneCenter_le_center T hzZ
  have hDZ : tU T u ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥ := fun hb =>
    hz1' (Subgroup.mem_bot.mp (hb ▸ (⟨hzU, hzc⟩ : z ∈ tU T u ⊓ (T ⊓ Subgroup.centralizer (T : Set G)))))
  exact charTwo_normalizer_of_inf_center S.hyp.qtke.2.1
    (isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow le_top) hTu2 hDZ

theorem stage1463Four_of_abel (iA : Input1463FourAbel) (h2 : Stage1463Two) (h3 : Stage1463Three) :
    Stage1463Four := by
  intro G _ _ T M S H hH u hu
  obtain ⟨hidx4, hidx2, hT0N, -, -⟩ := S.stage1463_one hH hu
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hIG : Subgroup.normalizer (tU T u : Set G) ≤ mcOf T := by
    by_contra hI
    have hQ := pCoreOf_normalizer_tU S h2 hH hu hI
    have hsq : IsSQTKTC (Subgroup.normalizer (tU T u : Set G)) :=
      S.isSQTKTC_of_pCoreOf_ne_bot (by
        rw [hQ]
        intro hb
        obtain ⟨⟨z, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp S.hyp1281.omegaOneCenter_ne_bot
        have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
        have huG : u ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hH hu.mem
        have hzU : z ∈ tU T u :=
          ⟨S146T.Z_le hzZ, Subgroup.mem_centralizer_singleton_iff.mpr (S146T.comm_Z huG hzZ).symm⟩
        exact hz1' (Subgroup.mem_bot.mp (hb ▸ hzU)))
    have hTI : T ⊓ Subgroup.normalizer (tU T u : Set G) = tZero T u := hT0N.symm
    have hab := iA G (Subgroup.normalizer (tU T u : Set G)) T (tZero T u) hsq
      (charTwo_normalizer_tU S hH hu) (isSylowTwoOf_tZero S h2 hH hu) hT2 (S146T.tZero_le T u)
      hu.index_two hTI (fun C hC hC1 hTC => star S h2 h3 hH hu hC hC1 hTC) (by rw [hQ]; exact hidx2)
    refine false_of_V_le_centralizer_tU S h3 hH hu ?_
    intro v hv
    refine Subgroup.mem_centralizer_iff.mpr fun t ht => ?_
    have hvU : v ∈ tU T u := VZ_le_tU S hH hu hv
    have ht' : t ∈ pCoreOf 2 (Subgroup.normalizer (tU T u : Set G)) := by rw [hQ]; exact ht
    have hv' : v ∈ pCoreOf 2 (Subgroup.normalizer (tU T u : Set G)) := by rw [hQ]; exact hvU
    exact hab t ht' v hv'
  have hN : Subgroup.normalizer (tU T u : Set G) = tZero T u := by
    rw [← normalizer_tU_inf_mcOf S h2 hH hu]
    exact (inf_eq_left.mpr hIG).symm
  have hSyl : IsSylowTwoOf (tU T u) (Subgroup.centralizer ({u} : Set G)) := by
    refine isSylowTwoOf_of_forall_normalizer (inf_le_right : tU T u ≤ _) (hT2.to_le inf_le_left) ?_
    intro x hx hxN _
    have hx0 : x ∈ tZero T u := hN ▸ hxN
    exact ⟨S146T.tZero_le T u hx0, hx⟩
  refine ⟨hN, hSyl, ?_⟩
  intro g z hz hz1 hgz
  have hPc : T.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer ({u} : Set G) := by
    rintro _ ⟨t, ht, rfl⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hc := S146T.comm_Z_T ht hz
    show g * t * g⁻¹ * u = u * (g * t * g⁻¹)
    rw [← hgz]
    calc g * t * g⁻¹ * (g * z * g⁻¹) = g * (t * z) * g⁻¹ := by group
      _ = g * (z * t) * g⁻¹ := by rw [hc]
      _ = g * z * g⁻¹ * (g * t * g⁻¹) := by group
  have hP2 : IsPGroup 2 (T.map (MulAut.conj g).toMonoidHom) := hT2.map _
  have hcard := card_le_of_isSylowTwoOf hSyl hP2 hPc
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective] at hcard
  have h4 := Subgroup.relIndex_mul_card (tU T u) T
  have htUT : tU T u ≤ T := inf_le_left
  rw [hidx4, inf_eq_left.mpr htUT] at h4
  have hpos : 0 < Nat.card (tU T u) := Nat.card_pos
  omega

end S153T

end CFSG.Quasithin
