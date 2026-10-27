module

public import CFSG.Quasithin.H13.A7NaturalLocal
public import CFSG.Quasithin.H13.A7CentralCoverGen
public import CFSG.Quasithin.Vol2.Ch12Sec2Statements
public import CFSG.Quasithin.H13.A7InvolutionSeed

public section

namespace CFSG.Quasithin.H13.A7

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Blueprint

variable {G : Type} [Group G]

theorem eq_oTwoUpper_sup_sylow [Finite G] (T : Sylow 2 G) {H : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) : oTwoUpper H ⊔ T = H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (sup_le (oTwoUpper_le H) hTH) ?_
  set K := (oTwoUpper H).subgroupOf H with hK
  have hKn : K.Normal :=
    (normal_subgroupOf_iff_le_normalizer (oTwoUpper_le H)).2 (le_normalizer_oTwoUpper H)
  have hQ : IsPGroup 2 (↥H ⧸ K) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper H x.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact mem_subgroupOf.2 (by simpa using hk)
  set S : Sylow 2 (↥H ⧸ K) := (T.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective K)
  have hStop : (S : Subgroup (↥H ⧸ K)) = ⊤ := (S.is_maximal' (hQ.to_subgroup ⊤) le_top).symm
  intro h hh
  have hmem : (QuotientGroup.mk' K ⟨h, hh⟩) ∈ (S : Subgroup (↥H ⧸ K)) := hStop ▸ mem_top _
  obtain ⟨t, ht, hth⟩ := hmem
  have htT : (t : G) ∈ (T : Subgroup G) := ht
  have h1 : t⁻¹ * ⟨h, hh⟩ ∈ K := by
    rw [← QuotientGroup.eq]
    exact hth
  rw [hK, mem_subgroupOf] at h1
  have h2 : h = (t : G) * ((t⁻¹ * ⟨h, hh⟩ : H) : G) := by simp
  rw [h2]
  exact mul_mem (mem_sup_right htT) (mem_sup_left h1)

theorem le_of_alternating_seven_central_quotient [Finite G] (T : Sylow 2 G) {Y M : Subgroup G}
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hA7 : Nonempty ((↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸ center (↥Y ⧸ CFSG.pCore 2 ↥Y) ≃*
      alternatingGroup (Fin 7)))
    (hsolv : ∀ X : Subgroup G, (T : Subgroup G) ≤ X → Group.IsSolvable X → X ≤ M) : Y ≤ M := by
  classical
  obtain ⟨f⟩ := hA7
  set R := pCoreOf 2 Y with hR
  have hRY : R ≤ Y := map_subtype_le _
  have hRsub : R.subgroupOf Y = CFSG.pCore 2 ↥Y := by
    rw [hR, pCoreOf_eq_map_cfsgPCore]
    exact comap_map_eq_self_of_injective Y.subtype_injective _
  have hR2 : IsPGroup 2 R := by
    rw [hR, pCoreOf_eq_map_cfsgPCore]
    exact (CFSG.pCore_isPGroup (p := 2) (G := Y)).map Y.subtype
  have hRn : (R.subgroupOf (Y ⊔ T)).Normal :=
    (normal_subgroupOf_iff_le_normalizer (hRY.trans le_sup_left)).2
      ((sup_le le_normalizer hTY).trans normalizer_le_normalizer_pCoreOf_two)
  have : (R.subgroupOf Y).Normal := by
    rw [hRsub]
    infer_instance
  let e : ↥Y ⧸ R.subgroupOf Y ≃* ↥Y ⧸ CFSG.pCore 2 ↥Y := QuotientGroup.quotientMulEquivOfEq hRsub
  let θ : ↥Y ⧸ R.subgroupOf Y →* alternatingGroup (Fin 7) :=
    f.toMonoidHom.comp ((QuotientGroup.mk' (center (↥Y ⧸ CFSG.pCore 2 ↥Y))).comp e.toMonoidHom)
  have hθ : Function.Surjective θ :=
    f.surjective.comp ((QuotientGroup.mk'_surjective _).comp e.surjective)
  have hθc : θ.ker ≤ center (↥Y ⧸ R.subgroupOf Y) := by
    intro x hx
    have h1 : QuotientGroup.mk' (center (↥Y ⧸ CFSG.pCore 2 ↥Y)) (e x) = 1 := by
      apply f.injective
      rw [map_one]
      exact hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    rw [mem_center_iff] at h1 ⊢
    intro g
    apply e.injective
    rw [map_mul, map_mul]
    exact h1 (e g)
  exact (A7_every_normalized_central_cover_has_solvable_Sylow_generators T hTY hRY hR2 hRn θ hθ
    hθc).2 M hsolv

theorem A7_escape_oTwoUpper_local (h1227 : Stmt12_2_7) [Finite G] (T : Sylow 2 G)
    {L V H : Subgroup G} (hyp : Hyp1223 G T L V)
    (hCZ : centralizer (quasithinOmegaOneCenter (T : Subgroup G) : Set G) ≤
      normalizer (L : Set G))
    (hH : IsHStar (T : Subgroup G) (normalizer (L : Set G)) H) (hHs : ¬ Group.IsSolvable H)
    (hsolv : ∀ X : Subgroup G, (T : Subgroup G) ≤ X → Group.IsSolvable X →
      X ≤ normalizer (L : Set G)) :
    LieModel (↥(oTwoUpper H) ⧸ CFSG.pCore 2 ↥(oTwoUpper H)) .PSL 2 2 2 ∧
      quasithinIsMaximalLocal (T : Subgroup G) (oTwoUpper H) ∧
      quasithinIsFaithfulLocal (T : Subgroup G) (oTwoUpper H) ∧
      IsA5ModuleSum (oTwoUpper H) ⁅VZ (T : Subgroup G) H, oTwoUpper H⁆ ∧
      IsPrimeReduced 2 ((VZ (T : Subgroup G) H).subgroupOf H) ∧
      (T : Subgroup G) ⊓ centralizer (VZ (T : Subgroup G) H : Set G) = pCoreOf 2 H := by
  obtain ⟨⟨hred, hCT, -, -⟩, h2⟩ := h1227 G T L V H hyp hCZ hH
  obtain ⟨hLie, Y, hKY, hYmax, hYf, hcase⟩ := h2 hHs
  rcases hcase with ⟨hYK, hA5⟩ | ⟨hA7, -, hTY, -⟩
  · rw [hYK] at hYmax hYf
    exact ⟨hLie, hYmax, hYf, hA5, hred, hCT⟩
  · exfalso
    have hYM : Y ≤ normalizer (L : Set G) :=
      le_of_alternating_seven_central_quotient T hTY hA7 hsolv
    apply hH.2.1
    rw [← eq_oTwoUpper_sup_sylow T hH.1.1]
    exact sup_le (hKY.trans hYM) hyp.normalizes

theorem centralizer_le_normalizer_of_uniqueMax (h331 : Stmt3_3_1) [Finite G]
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hQTKE : QuasithinUnique.quasithinIsQTKECat G) (T : Sylow 2 G) {K : Subgroup G}
    (hKmax : quasithinIsMaximalLocal (T : Subgroup G) K)
    (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) {e : G} (he : orderOf e = 2)
    (hKe : K ⊔ T ≤ centralizer ({e} : Set G)) :
    centralizer ({e} : Set G) ≤ normalizer (K : Set G) := by
  have hTsyl : quasithinIsSylowTwo (T : Subgroup G) := ⟨T.isPGroup', T.not_dvd_index⟩
  obtain ⟨-, h331B⟩ := h331 G T hs hnab hQTKE hTsyl
  obtain ⟨⟨-, -, huniq⟩, -⟩ := h331B K hKmax hKq
  have hcl : conjClosure K T = K :=
    le_antisymm (conjClosure_le fun _ ht l hl => (mem_normalizer_iff.1 (hTK ht) l).1 hl)
      (le_conjClosure K T)
  rw [hcl] at huniq
  obtain ⟨P, hP1, hP2, hPe⟩ := isPLocal_two_centralizer_of_orderOf_eq_two he
  obtain ⟨M', hM', hle⟩ := U3.exists_maxTwoLocal_le (H := centralizer ({e} : Set G))
    ⟨P, hP1, hP2, hPe⟩
  rw [← huniq M' hM' (hKe.trans hle)]
  exact hle

end CFSG.Quasithin.H13.A7
