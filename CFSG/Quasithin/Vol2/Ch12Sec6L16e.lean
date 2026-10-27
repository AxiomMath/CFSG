module

public import CFSG.Quasithin.Vol2.Ch12Sec6L16d
public import CFSG.Quasithin.Vol2.Ch12Sec6L16b

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise

namespace S126T2

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem part1216_two (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1228 : Stmt12_2_8)
    (h51 : AsB51) (hD2 : Lemma12_6_4_5) (hD3 : Lemma12_6_6_9) (hD5 : Lemma12_6_11)
    (hD8 : Lemma12_6_14) {F : Frame126 T L V} {v : G} {Kv S : Subgroup G}
    (hC : Ctx1262 F v Kv S) (hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥)
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) : ¬ IsAltBlockType L 8 := by
  intro hblock
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH := hC.hyp
  have hyp := hH.hyp
  have hv := hC.mem
  have hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1) := hC.coord
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hyp.normalizes
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := S126L19b.T_le_normalizer_V h1222 hH
  have hVL : ⁅V, L⁆ = V := hyp.irrPlus.2.2.2.1
  have hV1 : V ≠ ⊥ := hyp.irrPlus.2.1
  have hXL : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hXV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hTV
  have hVe := (V_facts h1222 hH).2
  have hVQ := V_le_Qv h1222 hH
  have hKvM : ¬ Kv ≤ Subgroup.normalizer (L : Set G) := (hD5 G T L V F v Kv S hC).2
  obtain ⟨g₁, hKv1, -, hR1, hLw⟩ := exists_g1 h331 h1222 h1228 h51 hD2 hD3 hD8 hC hZ hS
  set c₁ := (MulAut.conj g₁).toMonoidHom with hc₁
  set ca := (MulAut.conj g₁⁻¹).toMonoidHom with hca
  have hinv : ∀ H : Subgroup G, (H.map c₁).map ca = H := by
    intro H
    rw [Subgroup.map_map]
    conv_rhs => rw [← Subgroup.map_id H]
    congr 1
    ext x
    simp only [hc₁, hca, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  have hinv' : ∀ H : Subgroup G, (H.map ca).map c₁ = H := by
    intro H
    rw [Subgroup.map_map]
    conv_rhs => rw [← Subgroup.map_id H]
    congr 1
    ext x
    simp only [hc₁, hca, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  have hRvY := Rv_le_centralizerSection hD2 hC
  have hRa : (Rv T L v).map ca = Rv T L v :=
    calc (Rv T L v).map ca = ((Rv T L v).map c₁).map ca := by rw [hR1]
      _ = Rv T L v := hinv _
  have hRT : Rv T L v ≤ T :=
    (pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_Tv h1222 F hH hv hβ)).trans inf_le_left
  have hRX : Rv T L v ≤ L ⊔ T := (pCoreOf_le 2 _).trans inf_le_left
  have hQR : ¬ Rv T L v ≤ Qv T V := by
    intro h
    apply part1216_one h331 h1222 h1228 h51 hD2 hD3 hD5 hD8 hC hZ hS
    rw [le_antisymm h (Qv_le_Rv h1222 hH hv)]
    exact normalizer_Qv_le_M h331 h1222 hH
  obtain ⟨r, hr, hrQ⟩ := IsConcreteLE.not_le_iff_exists.1 hQR
  obtain ⟨σ, hσ, hσ1⟩ := actsAs_of_mem_centralizerSection h1222 F hH hv hβ (hRvY hr)
  have hrσ : ActsAs F r (Equiv.swap 0 1) := by
    rcases hσ1 with rfl | rfl
    · exact absurd ⟨hRT hr, mem_centralizer_of_actsAs_one F hVL hLV (hXL (hRX hr))
        (hXV (hRX hr)) hσ⟩ hrQ
    · exact hσ
  have hLT := sup_le_sup_Rv h1222 F hH hv hr hrσ
  have hVR : V ≤ Rv T L v := hVQ.trans (Qv_le_Rv h1222 hH hv)
  have hVaR : V.map ca ≤ Rv T L v := (Subgroup.map_mono hVR).trans hRa.le
  have hVgR : V.map c₁ ≤ Rv T L v := (Subgroup.map_mono hVR).trans hR1.le
  by_cases hVV : ⁅V, V.map ca⁆ = ⊥
  ·
    have hVaQ : V.map ca ≤ Qv T V := le_inf (hVaR.trans hRT)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 ((Subgroup.commutator_comm _ _).trans hVV))
    have hVV' : ⁅V.map c₁, V⁆ = ⊥ := by
      have h := congrArg (Subgroup.map c₁) hVV
      rwa [Subgroup.map_commutator, hinv', Subgroup.map_bot] at h
    have hVgQ : V.map c₁ ≤ Qv T V :=
      le_inf (hVgR.trans hRT) (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hVV')
    have hQL := comm_Qv_L_le_V h1222 hH hblock.1
    have hWL : ∀ W : Subgroup G, V ≤ W → W ≤ Qv T V → L ≤ Subgroup.normalizer (W : Set G) :=
      fun W hVW hWQ => le_normalizer_of_commutator_le
        (((Subgroup.commutator_mono hWQ le_rfl).trans hQL).trans hVW)
    have hLW := hWL (V ⊔ V.map ca) le_sup_left (sup_le hVQ hVaQ)
    have hLW' := hWL (V.map c₁ ⊔ V) le_sup_right (sup_le hVgQ hVQ)
    have hKvW : Kv ≤ Subgroup.normalizer ((V ⊔ V.map ca : Subgroup G) : Set G) := by
      have hKva : L.map ca = Kv := by rw [← hKv1, hinv]
      have hWa : (V.map c₁ ⊔ V).map ca = V ⊔ V.map ca := by rw [Subgroup.map_sup, hinv]
      rw [← hKva, ← hWa, hca, ← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.map_mono hLW'
    have hRVa : Rv T L v ≤ Subgroup.normalizer ((V.map ca : Subgroup G) : Set G) := by
      rw [← hRa, hca, ← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.map_mono (hRX.trans hXV)
    have hLTW : L ⊔ T ≤ Subgroup.normalizer ((V ⊔ V.map ca : Subgroup G) : Set G) :=
      hLT.trans (sup_le hLW (le_normalizer_sup_of_le (hRX.trans hXV) hRVa))
    have hW1 : V ⊔ V.map ca ≠ ⊥ := fun h => hV1 (le_bot_iff.1 (le_sup_left.trans h.le))
    have hW2 : IsPGroup 2 ↥(V ⊔ V.map ca) :=
      hyp.sylow.1.to_le ((sup_le hVQ hVaQ).trans inf_le_left)
    exact hKvM (hKvW.trans (normalizer_le_M h331 hH hW1 hW2 hLTW))
  ·
    have key : ∀ E : S126FE.Frame126E F, g₁ ∈ Gv ((E.γ.symm (pe 0 1) : ↥V) : G) := by
      intro E
      have heV : ((E.γ.symm (pe 0 1) : ↥V) : G) ∈ V := (E.γ.symm (pe 0 1)).2
      have he1 : ((E.γ.symm (pe 0 1) : ↥V) : G) ≠ 1 := by
        intro h
        have h1 : E.γ.symm (pe 0 1) = 1 := Subtype.ext h
        rw [MulEquiv.symm_apply_eq, map_one] at h1
        exact absurd h1 (by decide)
      have hee : ((E.γ.symm (pe 0 1) : ↥V) : G) * ((E.γ.symm (pe 0 1) : ↥V) : G) = 1 := by
        rw [← sq]
        exact hVe.2 _ heV
      set e : G := ((E.γ.symm (pe 0 1) : ↥V) : G) with he
      have hC1 : ⁅V, V.map ca⁆ ≤ Subgroup.zpowers e :=
        comm_le_zpowers h1222 F hH E hv hβ (hVaR.trans hRvY)
      have hC2 : ⁅V, V.map c₁⁆ ≤ Subgroup.zpowers e :=
        comm_le_zpowers h1222 F hH E hv hβ (hVgR.trans hRvY)
      have hmap : ⁅V, V.map ca⁆.map c₁ = ⁅V, V.map c₁⁆ := by
        rw [Subgroup.map_commutator, hinv', Subgroup.commutator_comm]
      have hne : ⁅V, V.map c₁⁆ ≠ ⊥ := by
        rw [← hmap]
        intro h
        apply hVV
        rw [← hinv ⁅V, V.map ca⁆, h, Subgroup.map_bot]
      obtain ⟨y, hy, hy1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hne
      have heC : e ∈ ⁅V, V.map c₁⁆ := by
        rcases eq_one_or_eq_of_mem_zpowers hee (hC2 hy) with h | h
        · exact absurd h hy1
        · exact h ▸ hy
      rw [← hmap] at heC
      obtain ⟨z, hz, hze⟩ := heC
      rcases eq_one_or_eq_of_mem_zpowers hee (hC1 hz) with h | h
      · exact absurd (hze.symm.trans (by rw [h, map_one])) he1
      · rw [h] at hze
        simp only [hc₁, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hze
        show g₁ ∈ Subgroup.centralizer {e}
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc g₁ * e = g₁ * e * g₁⁻¹ * g₁ := by group
          _ = e * g₁ := by rw [hze]
    obtain ⟨E₀⟩ := S126FE.exists_frame126E h1222 F hH hZ
    by_cases hwt : WtTwo F v
    ·
      obtain ⟨E, hv', hw⟩ := hwt
      have hγ : E.γ ⟨v, hv⟩ = pe 0 1 := gamma_eq_pe F E hv hβ hw
      have hve : ((E.γ.symm (pe 0 1) : ↥V) : G) = v := by
        rw [← hγ, MulEquiv.symm_apply_apply]
      have hg := key E
      rw [hve] at hg
      have hgv : g₁ * v * g₁⁻¹ = v := by
        have h1 : g₁ * v = v * g₁ := Subgroup.mem_centralizer_singleton_iff.1 hg
        rw [h1]
        group
      rw [hgv] at hLw
      exact not_le_Gv h1222 F hH hv hβ hLw
    ·
      have he2 : WtTwo F ((E₀.γ.symm (pe 0 1) : ↥V) : G) :=
        ⟨E₀, (E₀.γ.symm (pe 0 1)).2, by
          rw [Subtype.coe_eta, MulEquiv.apply_symm_apply]
          exact S126L20a.wt_pe (by decide)⟩
      have hGe : Gv ((E₀.γ.symm (pe 0 1) : ↥V) : G) ≤ Subgroup.normalizer (L : Set G) := by
        by_contra h
        exact hwt (hC.choice hZ ⟨_, he2, h⟩)
      have hL1 : L.map c₁ = L := (Subgroup.mem_normalizer_iff_map_conj_eq).1 (hGe (key E₀))
      have hKvL : Kv = L :=
        Subgroup.map_injective (MulAut.conj g₁).injective (hKv1.trans hL1.symm)
      exact hKvM (hKvL ▸ Subgroup.le_normalizer)

end S126T2

theorem lemma12_6_16_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1228 : Stmt12_2_8)
    (h51 : AsB51) (hD2 : Lemma12_6_4_5) (hD3 : Lemma12_6_6_9) (hD5 : Lemma12_6_11)
    (hD8 : Lemma12_6_14) : Lemma12_6_16 := by
  intro G _ _ T L V _ F v Kv S hC hZ hS
  exact ⟨S126T2.part1216_one h331 h1222 h1228 h51 hD2 hD3 hD5 hD8 hC hZ hS,
    S126T2.part1216_two h331 h1222 h1228 h51 hD2 hD3 hD5 hD8 hC hZ hS⟩

end CFSG.Quasithin.H13
