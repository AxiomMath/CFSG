module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.InPStarCriteria
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22t
public import CFSG.LocalAnalysis.SteinbergBQControlSylowPromotion

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem inPStar_of_cyclic_sylow_frattini (D : Data G) {V₀ V : Subgroup G}
    (h1 : R17_2_1At D V₀ V) {D' X Y : Subgroup G} {q : ℕ} (hq : q.Prime)
    (hD'M : D' ≤ D.M) (hD'5 : IsPGroup 5 ↥D') (hD'nc : ¬ IsCyclic ↥D')
    (hD'exp : ∀ x ∈ D', x ^ 5 = 1) (hD'class : ⁅⁅D', D'⁆, D'⁆ = ⊥)
    (hnormal' : ((D' ⊔ CFSG.Open.pCoreOf 2 D.M).subgroupOf D.M).Normal)
    (hX : CFSG.ABGLocalTools.IsSylowOf q X D.M) (hXcyc : IsCyclic ↥X)
    (hcent : X ≤ Subgroup.centralizer (D' : Set G)) (hYX : Y ≤ X)
    (hS : ∃ S : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf 2 S (Subgroup.normalizer (Y : Set G) ⊓ D.M) ∧
      IsCyclic ↥S) :
    InPStar D V₀ D' := by
  classical
  set O : Subgroup G := CFSG.Open.pCoreOf 2 D.M with hO
  set V : Subgroup G := D' ⊔ O with hV
  set K : Subgroup G := F11.CTilde D.M O V with hK
  have hOM : O ≤ D.M := CFSG.LieType.BorelTits.pCoreOf_le 2 D.M
  have hOnorm : D.M ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M
  have hVM : V ≤ D.M := sup_le hD'M hOM
  have hVnorm : D.M ≤ Subgroup.normalizer (V : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVM).1 hnormal'
  have hKmem : ∀ c : G, c ∈ K ↔ c ∈ D.M ∧ c ∈ Subgroup.normalizer (O : Set G) ∧
      ∀ v ∈ V, c * v * c⁻¹ * v⁻¹ ∈ O := by
    intro c
    rw [hK]
    exact uc22p22q_mem_ctilde
  have hKM : K ≤ D.M := fun c hc => ((hKmem c).1 hc).1
  have hMK : D.M ≤ Subgroup.normalizer (K : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      exact uc22p22q_ctilde_conj_mem hVnorm hOnorm hm hc
    · intro hc
      have h2 := uc22p22q_ctilde_conj_mem hVnorm hOnorm (D.M.inv_mem hm) hc
      have h3 : m⁻¹ * (m * c * m⁻¹) * m⁻¹⁻¹ = c := by group
      rw [h3] at h2
      rw [hK]
      exact h2
  haveI hIK : (K.subgroupOf D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).2 hMK
  have hO_le_T : O ≤ D.T := by
    have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M
    have hOT2 : IsPGroup 2 (O ⊔ D.T : Subgroup G) :=
      hO2.to_sup_of_normal_left' D.sylowM.isPGroup (D.sylowM.le.trans hOnorm)
    have heq : O ⊔ D.T = D.T :=
      D.sylowM.eq_of_le le_sup_right (sup_le hOM D.sylowM.le) hOT2
    exact le_sup_left.trans (le_of_eq heq)
  have hXK : X ≤ K := by
    intro x hx
    refine (hKmem x).2 ⟨hX.le hx, hOnorm (hX.le hx), ?_⟩
    intro v hv
    have hD'O : D' ≤ Subgroup.normalizer (O : Set G) := hD'M.trans hOnorm
    have hVset : ((D' ⊔ O : Subgroup G) : Set G) = (D' : Set G) * (O : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right D' O hD'O
    have hv' : v ∈ (D' : Set G) * (O : Set G) := by
      rw [← hVset]
      simpa [hV] using hv
    obtain ⟨d, hd, z, hz, rfl⟩ := Set.mem_mul.mp hv'
    have hxd : x * d * x⁻¹ * d⁻¹ = 1 := by
      have hcomm : d * x = x * d := (Subgroup.mem_centralizer_iff.mp (hcent hx)) d hd
      rw [← hcomm]
      group
    have hxz : x * z * x⁻¹ * z⁻¹ ∈ O := by
      have h1 : x * z * x⁻¹ ∈ O :=
        (Subgroup.mem_normalizer_iff.mp (hOnorm (hX.le hx)) z).mp hz
      exact O.mul_mem h1 (O.inv_mem hz)
    have hdz : d * (x * z * x⁻¹ * z⁻¹) * d⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp (hOnorm (hD'M hd)) _).mp hxz
    have heq : x * (d * z) * x⁻¹ * (d * z)⁻¹ =
        d * (x * z * x⁻¹ * z⁻¹) * d⁻¹ := by
      calc x * (d * z) * x⁻¹ * (d * z)⁻¹
          = (x * d * x⁻¹ * d⁻¹) * (d * (x * z * x⁻¹ * z⁻¹) * d⁻¹) := by group
        _ = d * (x * z * x⁻¹ * z⁻¹) * d⁻¹ := by rw [hxd, one_mul]
    rwa [heq]
  haveI : Fact q.Prime := ⟨hq⟩
  have hXK_sylow : CFSG.ABGLocalTools.IsSylowOf q X K := hX.of_le hXK hKM
  have hFr : D.M ≤ K ⊔ (D.M ⊓ Subgroup.normalizer (X : Set G)) :=
    uc22p22t_frattini_sup hKM hMK hXK_sylow
  have hNXY : Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (Y : Set G) :=
    CFSG.LocalAnalysis.SteinbergBQ.normalizer_le_normalizer_of_le_isCyclic hYX hXcyc
  set L : Subgroup G := Subgroup.normalizer (Y : Set G) ⊓ D.M with hL
  have hLM : L ≤ D.M := inf_le_right
  have hML : D.M ≤ K ⊔ L := by
    refine hFr.trans (sup_le_sup_left ?_ K)
    intro x hx
    exact ⟨hNXY hx.2, hx.1⟩
  have hLKsup : K ⊔ L = D.M := le_antisymm (sup_le hKM hLM) hML
  let Mbar := D.M ⧸ (K.subgroupOf D.M)
  let π : ↥D.M →* Mbar := QuotientGroup.mk' (K.subgroupOf D.M)
  let f : ↥L →* Mbar := π.comp (Subgroup.inclusion hLM)
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (K.subgroupOf D.M) y
    have hKL : L ≤ Subgroup.normalizer (K : Set G) := hLM.trans hMK
    have hset : ((K ⊔ L : Subgroup G) : Set G) = (K : Set G) * (L : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left K L hKL
    have hm : (m : G) ∈ (K : Set G) * (L : Set G) := by
      rw [← hset, hLKsup]
      exact m.2
    obtain ⟨k, hk, l, hl, hkl⟩ := Set.mem_mul.mp hm
    refine ⟨⟨l, hl⟩, ?_⟩
    have hkK : (⟨k, hKM hk⟩ : ↥D.M) ∈ K.subgroupOf D.M := Subgroup.mem_subgroupOf.mpr hk
    have hπk : π ⟨k, hKM hk⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hkK
    have hmk : (⟨k, hKM hk⟩ : ↥D.M) * ⟨l, hLM hl⟩ = m := Subtype.ext (by simpa using hkl)
    calc f ⟨l, hl⟩ = π ⟨l, hLM hl⟩ := rfl
      _ = π (⟨k, hKM hk⟩ * ⟨l, hLM hl⟩) := by rw [map_mul, hπk, one_mul]
      _ = π m := by rw [hmk]
  obtain ⟨S, hSsyl, hScyc⟩ := hS
  have hSL : S ≤ L := hSsyl.le
  have hSsub : CFSG.ABGLocalTools.IsSylowOf 2 (S.subgroupOf L) ⊤ := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff L).mp ?_
    simpa [Subgroup.map_subgroupOf_eq_of_le hSL, Subgroup.map_top,
      Subgroup.range_subtype] using hSsyl
  have hSmap : CFSG.ABGLocalTools.IsSylowOf 2 ((S.subgroupOf L).map f) ⊤ := by
    have h := CFSG.QuasithinUnique.Setup.Lift.isSylowOf_map hSsub f
    rwa [Subgroup.map_top, MonoidHom.range_eq_top.mpr hfsurj] at h
  have hSsubcyc : IsCyclic ↥(S.subgroupOf L) :=
    (Subgroup.subgroupOfEquivOfLe hSL).isCyclic.mpr hScyc
  haveI : IsCyclic ↥(S.subgroupOf L) := hSsubcyc
  have hSmapcyc : IsCyclic ↥((S.subgroupOf L).map f) :=
    isCyclic_of_surjective (f.subgroupMap (S.subgroupOf L))
      (MonoidHom.subgroupMap_surjective f (S.subgroupOf L))
  have hPidx : ¬ 2 ∣ ((S.subgroupOf L).map f).index := by
    have hdvd := (CFSG.ABGLocalTools.isSylowOf_iff.mp hSmap).2.2
    rwa [Subgroup.relIndex_top_right] at hdvd
  let Q : Sylow 2 Mbar := hSmap.isPGroup.toSylow hPidx
  have hQcyc : IsCyclic ↥Q := by
    have hQ' : (Q : Subgroup Mbar) = (S.subgroupOf L).map f :=
      IsPGroup.toSylow_coe hSmap.isPGroup hPidx
    show IsCyclic ↥(Q : Subgroup Mbar)
    rw [hQ']
    exact hSmapcyc
  let g : ↥D.T →* Mbar := π.comp (Subgroup.inclusion D.sylowM.le)
  let Tbar : Subgroup Mbar := g.range
  have hgrange : Tbar = (D.T.subgroupOf D.M).map π := by
    change g.range = Subgroup.map π (D.T.subgroupOf D.M)
    rw [MonoidHom.range_eq_map]
    change Subgroup.map (π.comp (Subgroup.inclusion D.sylowM.le)) ⊤ =
      Subgroup.map π (D.T.subgroupOf D.M)
    rw [← Subgroup.map_map]
    congr 1
    ext x
    constructor
    · rintro ⟨t, -, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr t.2
    · intro hx
      exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, trivial, Subtype.ext rfl⟩
  have hTbar2 : IsPGroup 2 Tbar := by
    rw [hgrange]
    exact (D.sylowM.isPGroup.comap_subtype).map π
  haveI hTbarcyc : IsCyclic ↥Tbar :=
    CFSG.LocalAnalysis.RankThreeTheoremC.isCyclic_of_isPGroup_of_isCyclic_sylow
      Q hQcyc hTbar2
  let φ : ↥D.T →* ↥Tbar :=
    g.codRestrict Tbar (fun t => MonoidHom.mem_range.mpr ⟨t, rfl⟩)
  have hkerφ : ∀ u : ↥D.T, φ u = 1 → (u : G) ∈ D.T ⊓ K := by
    intro u hu
    have h1 : g u = 1 := congrArg Subtype.val hu
    have h1' : π ⟨(u : G), D.sylowM.le u.2⟩ = 1 := h1
    have h2 : (⟨(u : G), D.sylowM.le u.2⟩ : ↥D.M) ∈ K.subgroupOf D.M :=
      (QuotientGroup.eq_one_iff _).mp h1'
    exact Subgroup.mem_inf.mpr ⟨u.2, Subgroup.mem_subgroupOf.mp h2⟩
  have hT0T : D.T ⊓ K ≤ D.T := inf_le_left
  have hTT0 : D.T ≤ Subgroup.normalizer ((D.T ⊓ K : Subgroup G) : Set G) :=
    Subgroup.le_normalizer_inf Subgroup.le_normalizer (D.sylowM.le.trans hMK)
  have hD'T0 : D' ≤ Subgroup.normalizer ((D.T ⊓ K : Subgroup G) : Set G) := by
    have hforward : ∀ e ∈ D', ∀ t ∈ D.T ⊓ K, e * t * e⁻¹ ∈ D.T ⊓ K := by
      intro e he t ht
      have htT : t ∈ D.T := ht.1
      have htK : t ∈ K := ht.2
      have hcommO : t * e * t⁻¹ * e⁻¹ ∈ O :=
        ((hKmem t).1 htK).2.2 e (Subgroup.mem_sup_left he)
      have hcommO' : e * t * e⁻¹ * t⁻¹ ∈ O := by
        have h := O.inv_mem hcommO
        rwa [show (t * e * t⁻¹ * e⁻¹)⁻¹ = e * t * e⁻¹ * t⁻¹ by group] at h
      have heK : e * t * e⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hMK (hD'M he)) t).mp htK
      have heT : e * t * e⁻¹ ∈ D.T := by
        have h := D.T.mul_mem (hO_le_T hcommO') htT
        rwa [show e * t * e⁻¹ * t⁻¹ * t = e * t * e⁻¹ by group] at h
      exact Subgroup.mem_inf.mpr ⟨heT, heK⟩
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · exact hforward d hd t
    · intro ht
      have h2 := hforward d⁻¹ (D'.inv_mem hd) (d * t * d⁻¹) ht
      have h3 : d⁻¹ * (d * t * d⁻¹) * (d⁻¹)⁻¹ = t := by group
      rw [h3] at h2
      exact h2
  have hInP11 : F11.InP11 D D' :=
    h1 5 D' Nat.prime_five (by norm_num) hD'M hD'5 hD'nc hD'exp hD'class hnormal'
  exact inPStar_of_inP11_of_le_normalizer (D := D) (V₀ := V₀) (X := D')
    (T₀ := D.T ⊓ K) hInP11 hT0T hTT0 hD'T0 φ hkerφ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
