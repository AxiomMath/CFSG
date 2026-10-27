module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapF4Data
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapKill

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

private def wcgapm_twoSet {M : Type} [Group M] (N K : Subgroup M) : Set (Subgroup M) :=
  {W | N ≤ W ∧ W ≤ K ∧ (W.subgroupOf K).Normal ∧
    ∀ w ∈ W, ∃ k : ℕ, w ^ (2 ^ k) ∈ N}

private def wcgapm_oddSet {M : Type} [Group M] (N P : Subgroup M) : Set (Subgroup M) :=
  {Q | N ≤ Q ∧ Q ≤ P ∧ (Q.subgroupOf P).Normal ∧ Odd (Q.relIndex P)}

private theorem wcgapm_mem_map_iff {M M' : Type} [Group M] [Group M'] (e : M ≃* M')
    {N : Subgroup M} {x : M} : e.toMonoidHom x ∈ N.map e.toMonoidHom ↔ x ∈ N := by
  constructor
  · rintro ⟨n, hn, hfn⟩
    rwa [e.injective hfn] at hn
  · intro hx
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩

private theorem wcgapm_map_centralizer_eq {M M' : Type} [Group M] [Group M'] (e : M ≃* M')
    (S : Subgroup M) :
    (Subgroup.centralizer (S : Set M)).map e.toMonoidHom =
      Subgroup.centralizer ((S.map e.toMonoidHom : Subgroup M') : Set M') := by
  apply le_antisymm
  · exact Subgroup.map_centralizer_le_centralizer_image (S : Set M) e.toMonoidHom
  · intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx
    refine Subgroup.mem_map.mpr ⟨e.symm x, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hx (e.toMonoidHom s) (Subgroup.mem_map.mpr ⟨s, hs, rfl⟩)

private theorem wcgapm_normal_subgroupOf_map_iff {M M' : Type} [Group M] [Group M']
    (e : M ≃* M') {W K : Subgroup M} (hWK : W ≤ K) :
    ((W.map e.toMonoidHom).subgroupOf (K.map e.toMonoidHom)).Normal ↔
      (W.subgroupOf K).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_mono hWK),
    Subgroup.normal_subgroupOf_iff_le_normalizer hWK]
  constructor
  · intro h
    rw [← Subgroup.map_equiv_normalizer_eq W e] at h
    exact (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp h
  · intro h
    have h' : K.map e.toMonoidHom ≤ (Subgroup.normalizer (W : Set M)).map e.toMonoidHom :=
      Subgroup.map_mono h
    rwa [Subgroup.map_equiv_normalizer_eq W e] at h'

private theorem wcgapm_twoSet_map_mem_iff {M M' : Type} [Group M] [Group M'] (e : M ≃* M')
    (N K W : Subgroup M) :
    W.map e.toMonoidHom ∈ wcgapm_twoSet (N.map e.toMonoidHom) (K.map e.toMonoidHom) ↔
      W ∈ wcgapm_twoSet N K := by
  constructor
  · rintro ⟨hNW, hWK, hnorm, hpow⟩
    have hWK' : W ≤ K :=
      (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp hWK
    refine ⟨?_, hWK', (wcgapm_normal_subgroupOf_map_iff e hWK').mp hnorm, ?_⟩
    · intro n hn
      exact ((Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp hNW) hn
    · intro w hw
      obtain ⟨k, hk⟩ := hpow (e.toMonoidHom w) (Subgroup.mem_map.mpr ⟨w, hw, rfl⟩)
      refine ⟨k, (wcgapm_mem_map_iff e).mp ?_⟩
      rwa [map_pow]
  · rintro ⟨hNW, hWK, hnorm, hpow⟩
    refine ⟨Subgroup.map_mono hNW, Subgroup.map_mono hWK,
      (wcgapm_normal_subgroupOf_map_iff e hWK).mpr hnorm, ?_⟩
    intro w' hw'
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hw'
    obtain ⟨k, hk⟩ := hpow w hw
    exact ⟨k, Subgroup.mem_map.mpr ⟨w ^ (2 ^ k), hk, by rw [map_pow]⟩⟩

private theorem wcgapm_oTwoMod_map {M M' : Type} [Group M] [Group M'] (e : M ≃* M')
    (N K : Subgroup M) :
    oTwoMod (N.map e.toMonoidHom) (K.map e.toMonoidHom) = (oTwoMod N K).map e.toMonoidHom := by
  have hL : oTwoMod N K = ⨆ W : wcgapm_twoSet N K, (W : Subgroup M) :=
    (iSup_subtype'' (wcgapm_twoSet N K) (fun W : Subgroup M => W)).symm
  have hmap : (oTwoMod N K).map e.toMonoidHom =
      ⨆ W : wcgapm_twoSet N K, ((W : Subgroup M).map e.toMonoidHom) := by
    rw [hL, Subgroup.map_iSup]
  have hL' : oTwoMod (N.map e.toMonoidHom) (K.map e.toMonoidHom) =
      ⨆ W' : wcgapm_twoSet (N.map e.toMonoidHom) (K.map e.toMonoidHom),
        (W' : Subgroup M') :=
    (iSup_subtype'' _ (fun W' : Subgroup M' => W')).symm
  rw [hmap, hL']
  apply le_antisymm
  · refine iSup_le fun W' => ?_
    have hmem : ((W' : Subgroup M').comap e.toMonoidHom) ∈ wcgapm_twoSet N K :=
      (wcgapm_twoSet_map_mem_iff e N K ((W' : Subgroup M').comap e.toMonoidHom)).mp (by
        rw [Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective
          (W' : Subgroup M')]
        exact W'.2)
    calc (W' : Subgroup M') = (((W' : Subgroup M').comap e.toMonoidHom).map e.toMonoidHom) :=
          (Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective
            (W' : Subgroup M')).symm
      _ ≤ ⨆ W : wcgapm_twoSet N K, ((W : Subgroup M).map e.toMonoidHom) :=
          le_iSup (fun W : wcgapm_twoSet N K => ((W : Subgroup M).map e.toMonoidHom))
            ⟨(W' : Subgroup M').comap e.toMonoidHom, hmem⟩
  · refine iSup_le fun W => ?_
    exact le_iSup (fun W' : wcgapm_twoSet (N.map e.toMonoidHom) (K.map e.toMonoidHom) =>
      (W' : Subgroup M'))
      ⟨(W : Subgroup M).map e.toMonoidHom,
        (wcgapm_twoSet_map_mem_iff e N K (W : Subgroup M)).mpr W.2⟩

private theorem wcgapm_oTwoMod_bot_map {M M' : Type} [Group M] [Group M'] (e : M ≃* M')
    (K : Subgroup M) :
    oTwoMod (⊥ : Subgroup M') (K.map e.toMonoidHom) =
      (oTwoMod (⊥ : Subgroup M) K).map e.toMonoidHom := by
  have h := wcgapm_oTwoMod_map e (⊥ : Subgroup M) K
  rwa [Subgroup.map_bot] at h

private theorem wcgapm_isSylowIn_map {M M' : Type} [Group M] [Group M'] (e : M ≃* M')
    {p : ℕ} {P H : Subgroup M} (h : IsSylowIn p P H) :
    IsSylowIn p (P.map e.toMonoidHom) (H.map e.toMonoidHom) := by
  refine ⟨Subgroup.map_mono h.le, h.isPGroup.map e.toMonoidHom, ?_⟩
  rw [Subgroup.relIndex_map_map_of_injective (f := e.toMonoidHom) P H e.injective]
  exact h.not_dvd_relIndex

private theorem wcgapm_hasQuotShape_map {M M' : Type} [Group M] [Group M'] (e : M ≃* M')
    (K N : Subgroup M) (P : ∀ (X : Type) [Group X], Prop)
    (h : HasQuotShape K (N : Set M) P) :
    HasQuotShape (K.map e.toMonoidHom) ((N.map e.toMonoidHom : Subgroup M') : Set M') P := by
  obtain ⟨X, hX, φ, hφ, hker, hP⟩ := h
  letI : Group X := hX
  let ee := Subgroup.equivMapOfInjective K e.toMonoidHom e.injective
  refine ⟨X, hX, φ.comp ee.symm.toMonoidHom, ?_, ?_, hP⟩
  · intro x
    obtain ⟨k, hk⟩ := hφ x
    refine ⟨ee k, ?_⟩
    show φ (ee.symm (ee k)) = x
    rw [MulEquiv.symm_apply_apply, hk]
  · intro k
    show φ (ee.symm k) = 1 ↔ (k : M') ∈ (N.map e.toMonoidHom : Set M')
    rw [hker (ee.symm k)]
    have hcoe : e.toMonoidHom ((ee.symm k : ↥K) : M) = (k : M') := by
      have h := Subgroup.coe_equivMapOfInjective_apply K e.toMonoidHom e.injective (ee.symm k)
      rw [MulEquiv.apply_symm_apply] at h
      exact h.symm
    rw [← hcoe]
    exact (wcgapm_mem_map_iff e).symm

private theorem wcgapm_oddSet_map_mem_iff {M M' : Type} [Group M] [Group M'] (e : M ≃* M')
    (N P Q : Subgroup M) :
    Q.map e.toMonoidHom ∈ wcgapm_oddSet (N.map e.toMonoidHom) (P.map e.toMonoidHom) ↔
      Q ∈ wcgapm_oddSet N P := by
  constructor
  · rintro ⟨hNQ, hQP, hnorm, hodd⟩
    have hQP' : Q ≤ P :=
      (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp hQP
    refine ⟨?_, hQP', (wcgapm_normal_subgroupOf_map_iff e hQP').mp hnorm, ?_⟩
    · intro n hn
      exact ((Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp hNQ) hn
    · rwa [Subgroup.relIndex_map_map_of_injective (f := e.toMonoidHom) Q P e.injective] at hodd
  · rintro ⟨hNQ, hQP, hnorm, hodd⟩
    refine ⟨Subgroup.map_mono hNQ, Subgroup.map_mono hQP,
      (wcgapm_normal_subgroupOf_map_iff e hQP).mpr hnorm, ?_⟩
    rwa [Subgroup.relIndex_map_map_of_injective (f := e.toMonoidHom) Q P e.injective]

private theorem wcgapm_oddResMod_bot_map {M M' : Type} [Group M] [Group M'] (e : M ≃* M')
    (P : Subgroup M) :
    oddResMod (⊥ : Subgroup M') (P.map e.toMonoidHom) =
      (oddResMod (⊥ : Subgroup M) P).map e.toMonoidHom := by
  let s := wcgapm_oddSet (⊥ : Subgroup M) P
  haveI : Nonempty s :=
    ⟨⟨P, bot_le, le_rfl, by rw [Subgroup.subgroupOf_self]; infer_instance,
      by rw [Subgroup.relIndex_self]; norm_num⟩⟩
  have hL : oddResMod (⊥ : Subgroup M) P = ⨅ Q : s, (Q : Subgroup M) :=
    (iInf_subtype'' s (fun Q : Subgroup M => Q)).symm
  have hmap : (oddResMod (⊥ : Subgroup M) P).map e.toMonoidHom =
      ⨅ Q : s, ((Q : Subgroup M).map e.toMonoidHom) := by
    rw [hL, Subgroup.map_iInf e.toMonoidHom e.injective]
  have hL' : oddResMod (⊥ : Subgroup M') (P.map e.toMonoidHom) =
      ⨅ Q' : wcgapm_oddSet (⊥ : Subgroup M') (P.map e.toMonoidHom), (Q' : Subgroup M') :=
    (iInf_subtype'' _ (fun Q' : Subgroup M' => Q')).symm
  rw [hmap, hL']
  apply le_antisymm
  · refine le_iInf fun Q => ?_
    have hmem : ((Q : Subgroup M).map e.toMonoidHom) ∈
        wcgapm_oddSet (⊥ : Subgroup M') (P.map e.toMonoidHom) := by
      simpa only [Subgroup.map_bot] using
        (wcgapm_oddSet_map_mem_iff e (⊥ : Subgroup M) P (Q : Subgroup M)).mpr Q.2
    exact iInf_le (fun Q' : wcgapm_oddSet (⊥ : Subgroup M') (P.map e.toMonoidHom) =>
      (Q' : Subgroup M')) ⟨(Q : Subgroup M).map e.toMonoidHom, hmem⟩
  · refine le_iInf fun Q' => ?_
    have hmem : ((Q' : Subgroup M').comap e.toMonoidHom) ∈ s := by
      refine (wcgapm_oddSet_map_mem_iff e (⊥ : Subgroup M) P
        ((Q' : Subgroup M').comap e.toMonoidHom)).mp ?_
      rw [Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective
        (Q' : Subgroup M')]
      simpa only [Subgroup.map_bot] using Q'.2
    calc (⨅ Q : s, ((Q : Subgroup M).map e.toMonoidHom)) ≤
          (((Q' : Subgroup M').comap e.toMonoidHom).map e.toMonoidHom) :=
          iInf_le (fun Q : s => ((Q : Subgroup M).map e.toMonoidHom))
            ⟨(Q' : Subgroup M').comap e.toMonoidHom, hmem⟩
      _ = (Q' : Subgroup M') :=
          Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective
            (Q' : Subgroup M')

private theorem wcgapm_isMaxParabolicMod_map {M M' : Type} [Group M] [Group M'] (e : M ≃* M')
    {N L P : Subgroup M} (h : IsMaxParabolicMod N L P) :
    IsMaxParabolicMod (N.map e.toMonoidHom) (L.map e.toMonoidHom) (P.map e.toMonoidHom) := by
  obtain ⟨hNP, hPL, hmax, S, hNS, hSL, hSpow, hSodd, hSnorm⟩ := h
  refine ⟨Subgroup.map_mono hNP,
    (Subgroup.map_lt_map_iff_of_injective (f := e.toMonoidHom) e.injective).mpr hPL, ?_,
    S.map e.toMonoidHom, Subgroup.map_mono hNS, Subgroup.map_mono hSL, ?_, ?_, ?_⟩
  · intro Y hPY hYL
    have hPY' : P < Y.comap e.toMonoidHom := by
      rw [← Subgroup.map_lt_map_iff_of_injective (f := e.toMonoidHom) e.injective]
      rwa [Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective Y]
    have hYL' : Y.comap e.toMonoidHom ≤ L := by
      have h := Subgroup.comap_mono (f := e.toMonoidHom) hYL
      rwa [Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective L] at h
    have hEq : Y.comap e.toMonoidHom = L := hmax _ hPY' hYL'
    rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective Y, hEq]
  · intro s hs
    obtain ⟨s₀, hs₀, rfl⟩ := Subgroup.mem_map.mp hs
    obtain ⟨k, hk⟩ := hSpow s₀ hs₀
    exact ⟨k, Subgroup.mem_map.mpr ⟨s₀ ^ (2 ^ k), hk, by rw [map_pow]⟩⟩
  · rw [Subgroup.relIndex_map_map_of_injective (f := e.toMonoidHom) _ _ e.injective]
    exact hSodd
  · calc L.map e.toMonoidHom ⊓ Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup M') : Set M')
        = L.map e.toMonoidHom ⊓ (Subgroup.normalizer (S : Set M)).map e.toMonoidHom := by
            rw [Subgroup.map_equiv_normalizer_eq S e]
      _ = (L ⊓ Subgroup.normalizer (S : Set M)).map e.toMonoidHom :=
            (Subgroup.map_inf L (Subgroup.normalizer (S : Set M)) e.toMonoidHom e.injective).symm
      _ ≤ P.map e.toMonoidHom := Subgroup.map_mono hSnorm

theorem centralKData_map {M M' : Type} [Group M] [Group M'] (e : M ≃* M') {S A : Subgroup M}
    (h : CentralKData S A) :
    CentralKData (S.map e.toMonoidHom) (A.map e.toMonoidHom) := by
  obtain ⟨K, hAK, hnK, hshape, hsyl, hidx⟩ := h
  refine ⟨K.map e.toMonoidHom, Subgroup.map_mono hAK, ?_, ?_, ?_, ?_⟩
  · rw [wcgapm_oTwoMod_bot_map e K]
    intro hle
    exact hnK ((Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp hle)
  · rw [wcgapm_oTwoMod_bot_map e K]
    exact wcgapm_hasQuotShape_map e K (oTwoMod (⊥ : Subgroup M) K) _ hshape
  · rw [← Subgroup.map_inf S K e.toMonoidHom e.injective]
    exact wcgapm_isSylowIn_map e hsyl
  · have hset : K.map e.toMonoidHom ⊓
        ((⊤ : Subgroup M') ⊓ Subgroup.normalizer (S.map e.toMonoidHom : Set M')) =
        (K ⊓ ((⊤ : Subgroup M) ⊓ Subgroup.normalizer (S : Set M))).map e.toMonoidHom := by
      rw [Subgroup.map_inf K ((⊤ : Subgroup M) ⊓ Subgroup.normalizer (S : Set M)) e.toMonoidHom
          e.injective,
        Subgroup.map_inf (⊤ : Subgroup M) (Subgroup.normalizer (S : Set M)) e.toMonoidHom
          e.injective,
        Subgroup.map_equiv_normalizer_eq S e, Subgroup.map_top,
        MonoidHom.range_eq_top_of_surjective e.toMonoidHom e.surjective]
    rw [hset, Subgroup.relIndex_map_map_of_injective (f := e.toMonoidHom) _ _ e.injective]
    exact hidx

theorem rankTwoParabData_map {M M' : Type} [Group M] [Group M'] (e : M ≃* M')
    {S : Subgroup M} (h : RankTwoParabData S) :
    RankTwoParabData (S.map e.toMonoidHom) := by
  obtain ⟨P, hmax, hS, hshape, hidx, hcomm⟩ := h
  let P' : Fin 2 → Subgroup M' := fun i => (P i).map e.toMonoidHom
  have hP' : ∀ i, P' i = (P i).map e.toMonoidHom := fun i => rfl
  refine ⟨P', ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have h := wcgapm_isMaxParabolicMod_map e (hmax i)
    rw [hP' i]
    simpa only [Subgroup.map_bot, Subgroup.map_top,
      MonoidHom.range_eq_top_of_surjective e.toMonoidHom e.surjective] using h
  · intro i
    rw [hP' i, wcgapm_oddResMod_bot_map e (P i)]
    exact Subgroup.map_mono (hS i)
  · intro i
    rw [hP' i, wcgapm_oddResMod_bot_map e (P i),
      wcgapm_oTwoMod_bot_map e (oddResMod (⊥ : Subgroup M) (P i))]
    exact wcgapm_hasQuotShape_map e (oddResMod (⊥ : Subgroup M) (P i))
      (oTwoMod (⊥ : Subgroup M) (oddResMod (⊥ : Subgroup M) (P i))) _ (hshape i)
  · intro i
    rw [hP' i, wcgapm_oddResMod_bot_map e (P i)]
    have hset : (oddResMod (⊥ : Subgroup M) (P i)).map e.toMonoidHom ⊓
        ((⊤ : Subgroup M') ⊓ Subgroup.normalizer (S.map e.toMonoidHom : Set M')) =
        ((oddResMod (⊥ : Subgroup M) (P i)) ⊓
          ((⊤ : Subgroup M) ⊓ Subgroup.normalizer (S : Set M))).map e.toMonoidHom := by
      rw [Subgroup.map_inf _ ((⊤ : Subgroup M) ⊓ Subgroup.normalizer (S : Set M)) e.toMonoidHom
          e.injective,
        Subgroup.map_inf (⊤ : Subgroup M) (Subgroup.normalizer (S : Set M)) e.toMonoidHom
          e.injective,
        Subgroup.map_equiv_normalizer_eq S e, Subgroup.map_top,
        MonoidHom.range_eq_top_of_surjective e.toMonoidHom e.surjective]
    rw [hset, Subgroup.relIndex_map_map_of_injective (f := e.toMonoidHom) _ _ e.injective]
    exact hidx i
  · intro a' ha0' ha1' s' hs'
    rw [hP' 0, wcgapm_oddResMod_bot_map e (P 0),
      wcgapm_oTwoMod_bot_map e (oddResMod (⊥ : Subgroup M) (P 0))] at ha0'
    rw [hP' 1, wcgapm_oddResMod_bot_map e (P 1),
      wcgapm_oTwoMod_bot_map e (oddResMod (⊥ : Subgroup M) (P 1))] at ha1'
    obtain ⟨a, ha0, rfl⟩ := Subgroup.mem_map.mp ha0'
    have ha1 : a ∈ oTwoMod (⊥ : Subgroup M) (oddResMod (⊥ : Subgroup M) (P 1)) :=
      (wcgapm_mem_map_iff e).mp ha1'
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hs'
    rw [← map_mul, ← map_mul, hcomm a ha0 ha1 s hs]

theorem tisIn_top_map {M M' : Type} [Group M] [Group M'] (e : M ≃* M') {A : Subgroup M}
    (h : TISIn (⊤ : Subgroup M) A) :
    TISIn (⊤ : Subgroup M') (A.map e.toMonoidHom) := by
  intro S' hS'
  have hsyl : IsSylowIn 2 (S'.comap e.toMonoidHom) (⊤ : Subgroup M) := by
    refine ⟨le_top, hS'.isPGroup.comap_of_injective e.toMonoidHom e.injective, ?_⟩
    have h' := hS'.not_dvd_relIndex
    rw [Subgroup.relIndex_top_right] at h'
    rw [Subgroup.relIndex_top_right,
      Subgroup.index_comap_of_surjective S' (f := e.toMonoidHom) e.surjective]
    exact h'
  rcases h (S'.comap e.toMonoidHom) hsyl with hbot | hle
  · left
    calc A.map e.toMonoidHom ⊓ S'
        = A.map e.toMonoidHom ⊓ (S'.comap e.toMonoidHom).map e.toMonoidHom := by
          rw [Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective S']
      _ = (A ⊓ S'.comap e.toMonoidHom).map e.toMonoidHom :=
          (Subgroup.map_inf A (S'.comap e.toMonoidHom) e.toMonoidHom e.injective).symm
      _ = (⊥ : Subgroup M).map e.toMonoidHom := by rw [hbot]
      _ = ⊥ := Subgroup.map_bot e.toMonoidHom
  · right
    rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective S']
    exact Subgroup.map_mono hle

theorem centerIrred_map {M M' : Type} [Group M] [Group M'] (e : M ≃* M') {S : Subgroup M}
    (h : CenterIrred S) : CenterIrred (S.map e.toMonoidHom) := by
  intro x' hx'S hx'c Z'' hZ''le hZ''inv hZ''comm
  obtain ⟨x, hxS, rfl⟩ := Subgroup.mem_map.mp hx'S
  have hxc : x ∉ Subgroup.centralizer (S : Set M) := by
    intro hx
    apply hx'c
    rw [← wcgapm_map_centralizer_eq e S]
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hZ'le : Z''.comap e.toMonoidHom ≤ S ⊓ Subgroup.centralizer (S : Set M) := by
    have hle := Subgroup.comap_mono (f := e.toMonoidHom) hZ''le
    rw [Subgroup.comap_inf,
      Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective,
      ← wcgapm_map_centralizer_eq e S,
      Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective] at hle
    exact hle
  have hZ'inv : ∀ b ∈ Subgroup.normalizer (S : Set M),
      ∀ z ∈ Z''.comap e.toMonoidHom, b * z * b⁻¹ ∈ Z''.comap e.toMonoidHom := by
    intro b hb z hz
    rw [Subgroup.mem_comap] at hz ⊢
    have hb' : e.toMonoidHom b ∈
        Subgroup.normalizer (S.map e.toMonoidHom : Set M') := by
      rw [← Subgroup.map_equiv_normalizer_eq S e]
      exact Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
    have h := hZ''inv (e.toMonoidHom b) hb' (e.toMonoidHom z) hz
    simpa only [map_mul, map_inv] using h
  have hZ'comm : ∀ y ∈ S, x * y * x⁻¹ * y⁻¹ ∈ Z''.comap e.toMonoidHom := by
    intro y hy
    rw [Subgroup.mem_comap]
    have h := hZ''comm (e.toMonoidHom y) (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
    simpa only [map_mul, map_inv] using h
  have hres := h x hxS hxc (Z''.comap e.toMonoidHom) hZ'le hZ'inv hZ'comm
  calc Z'' = (Z''.comap e.toMonoidHom).map e.toMonoidHom :=
        (Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective Z'').symm
    _ = (S ⊓ Subgroup.centralizer (S : Set M)).map e.toMonoidHom := by rw [hres]
    _ = S.map e.toMonoidHom ⊓ Subgroup.centralizer (S.map e.toMonoidHom : Set M') := by
          rw [Subgroup.map_inf _ _ e.toMonoidHom e.injective, wcgapm_map_centralizer_eq e S]

end CFSG.LocalAnalysis.WeakClosure81

end
