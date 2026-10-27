module

public import CFSG.Quasithin.EmptyFaithful.Gap6R2Base
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Gap6R2

variable {G : Type} [Group G] [Finite G]

section Basic

variable {T Mc M K N : Subgroup G}

theorem NonBorelK.T_le_K (hK : NonBorelK T Mc M K N) : T ≤ K := hK.minParabolic.isSylow.1

theorem NonBorelK.T_le_N (hK : NonBorelK T Mc M K N) : T ≤ N := hK.minParabolic.le

theorem NonBorelK.N_lt_K (hK : NonBorelK T Mc M K N) : N < K := hK.minParabolic.maximal.1

theorem NonBorelK.not_K_le_M (hK : NonBorelK T Mc M K N) : ¬ K ≤ M := fun h =>
  hK.not_le_M (hK.N_lt_K.le.trans h)

end Basic

theorem isSylowTwoOf_sup_of_inf {R D : Subgroup G} (hR : IsPGroup 2 R)
    (hRD : R ≤ Subgroup.normalizer (D : Set G)) (h : IsSylowTwoOf (R ⊓ D) D) :
    IsSylowTwoOf R (D ⊔ R) := by
  rw [A4.isSylowTwoOf_iff_maximal]
  refine ⟨le_sup_right, hR, fun P hPH hP hRP => ?_⟩
  intro t ht
  have htH : t ∈ R ⊔ D := by rw [sup_comm]; exact hPH ht
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right R D hRD] at htH
  obtain ⟨r, hr, k, hk, rfl⟩ := htH
  have hkP : k ∈ P := by
    have := P.mul_mem (P.inv_mem (hRP hr)) ht
    simpa using this
  have hmax := ((A4.isSylowTwoOf_iff_maximal).mp h).2.2 (P ⊓ D) inf_le_right (hP.to_inf_left)
    (le_inf (inf_le_left.trans hRP) inf_le_right)
  have hkR : k ∈ R := (hmax ⟨hkP, hk⟩).1
  exact R.mul_mem hr hkR

theorem normalizer_thompsonJ_le {T Mc M : Subgroup G} (h : quasithinQTFE14Cat G T Mc)
    (h159 : Lemma1519Concl T Mc M) : Subgroup.normalizer (thompsonJ T : Set G) ≤ M :=
  (S1414.normalizer_thompsonJ_le_CGS h.sylow.1 h.ne_bot).trans h159.one_cgs

section NonBorel

variable {T Mc M K N : Subgroup G}

theorem NonBorelK.not_thompsonJ_le_pCoreOf (h : quasithinQTFE14Cat G T Mc)
    (h159 : Lemma1519Concl T Mc M) (hK : NonBorelK T Mc M K N) :
    ¬ thompsonJ T ≤ pCoreOf 2 K := by
  intro hJQ
  have hJeq : thompsonJ (pCoreOf 2 K) = thompsonJ T :=
    B6.thompsonJ_eq_of_le hJQ (B6.pCoreOf_two_le_of_isSylowTwoOf hK.minParabolic.isSylow)
  have hKNJ : K ≤ Subgroup.normalizer (thompsonJ T : Set G) := by
    rw [← hJeq]
    exact (le_normalizer_pCoreOf 2 K).trans (normalizer_le_normalizer_thompsonJ _)
  exact hK.not_K_le_M (hKNJ.trans (normalizer_thompsonJ_le h h159))

theorem NonBorelK.not_inf_le_centralizer (hC58 : TheoremC58) (h : quasithinQTFE14Cat G T Mc)
    (hMf : IsMf T Mc M) (h159 : Lemma1519Concl T Mc M) (hK : NonBorelK T Mc M K N) :
    ¬ T ⊓ oTwoUpper K ≤ Subgroup.centralizer (V154 T Mc M : Set G) := by
  intro hle
  set R : Subgroup G := T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) with hR
  have hTM : T ≤ M := hMf.1.1.2
  have hT2 : IsPGroup 2 T := h.sylow.1
  have hTK := hK.T_le_K
  have hVT : V154 T Mc M ≤ T := (V154_le_VZ T Mc M).trans (isTwoReducedIn_VZ h hMf.1.1).2
  have hRT : R ≤ T := inf_le_left
  have hTV : T ≤ Subgroup.normalizer (V154 T Mc M : Set G) :=
    hTM.trans (le_normalizer_V154 T Mc M)
  have hTR : T ≤ Subgroup.normalizer (R : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht,
      Gap6.normalizer_le_normalizer_centralizer_gap6 _ (hTV ht)⟩
  have hZT : quasithinOmegaOneCenter T ≤ T :=
    (quasithinOmegaOneCenter_le_center T).trans inf_le_left
  have hZR : quasithinOmegaOneCenter T ≤ R := le_inf hZT fun z hz =>
    Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (Subgroup.mem_centralizer_iff.mp (le_centralizer_quasithinOmegaOneCenter T (hVT hv)) z hz).symm
  have hR1 : R ≠ ⊥ := fun hb => h.omegaOneCenter_ne_bot (le_bot_iff.mp (hZR.trans hb.le))
  have hR2 : IsPGroup 2 R := hT2.to_le hRT
  set M₀ : Subgroup G := M ⊓ Subgroup.normalizer (R : Set G) with hM₀
  have hM₀H : InH T M₀ := ⟨le_inf hTM hTR, fun h0 => hR1 (le_bot_iff.mp (by
    rw [← h0]
    exact le_pCoreOf_of_le_normalizer 2 (le_inf (hRT.trans hTM) Subgroup.le_normalizer)
      inf_le_right hR2))⟩
  have hZK : quasithinOmegaOneCenter T ≤ pCoreOf 2 K :=
    le_pCoreOf_of_le_normalizer 2 (hZT.trans hTK)
      (fun x hx => Subgroup.centralizer_le_normalizer _ (hK.le_centralizer hx))
      (hT2.to_le hZT)
  have hKH : InH T K := ⟨hTK, fun hb =>
    h.omegaOneCenter_ne_bot (le_bot_iff.mp (hZK.trans hb.le))⟩
  have hRle : T ⊓ oTwoUpper K ≤ R := le_inf inf_le_left hle
  have hRK : R ⊓ oTwoUpper K = T ⊓ oTwoUpper K :=
    le_antisymm (inf_le_inf_right _ hRT) (le_inf hRle inf_le_right)
  have hSyl : IsSylowTwoOf (T ⊓ oTwoUpper K) (oTwoUpper K) :=
    A4.isSylowTwoOf_inf_normal hK.minParabolic.isSylow (oTwoUpper_le K) (le_normalizer_oTwoUpper K)
  have hRS : IsSylowTwoOf R (oTwoUpper K ⊔ R) :=
    isSylowTwoOf_sup_of_inf hR2 ((hRT.trans hTK).trans (le_normalizer_oTwoUpper K))
      (by rw [hRK]; exact hSyl)
  obtain ⟨R₀, hR₀1, hR₀R, hR₀N⟩ := theorem311_of_C58 hC58 h.simple h.nonabelian h.qtke h.sylow hM₀H hKH
    ⟨N, hK.minParabolic.uniqueMax⟩ hR1 hRT hRS inf_le_right
  have hR₀2 : IsPGroup 2 R₀ := hR2.to_le hR₀R
  obtain ⟨M'', hM'', hNM''⟩ := exists_maxTwoLocal_ge
    (L := Subgroup.normalizer (R₀ : Set G)) ⟨R₀, hR₀1, hR₀2, rfl⟩
  have hM''M : M'' = M := h159.five.2 M'' ⟨hM'', le_sup_left.trans (hR₀N.trans hNM'')⟩
  exact hK.not_K_le_M (hM''M ▸ (le_sup_right.trans hR₀N).trans hNM'')

end NonBorel

end Gap6R2

end CFSG.Quasithin
