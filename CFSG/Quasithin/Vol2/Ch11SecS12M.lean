module

public import CFSG.Quasithin.Vol2.Ch11SecS12L
public import CFSG.Quasithin.Vol2.Ch11SecS12A
public import CFSG.Quasithin.Vol2.Ch11SecS12G
public import CFSG.Quasithin.Vol2.Ch11SecSX1
public import CFSG.Quasithin.Vol2.Ch11SecSXK

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL)
open CFSG.Quasithin.OperatorJH
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I V₁ V₂ X K : Subgroup G}

theorem modO2Image_L₁_ne_commutator (hN : SecA.NatFacts) (h1102 : Stmt11_0_2)
    (h : StarHyp G T L I V₁ V₂ X K) (hc : CartanL L V₁ V₂ X) :
    modO2Image (K ⊔ SecA.xOne X (LOf L V₁)) (LOf L V₁) ≠
      ⁅(⊤ : Subgroup (↥(K ⊔ SecA.xOne X (LOf L V₁)) ⧸
        CFSG.pCore 2 ↥(K ⊔ SecA.xOne X (LOf L V₁)))), ⊤⁆ := by
  set Y := K ⊔ SecA.xOne X (LOf L V₁) with hY
  have hKY : K ≤ Y := le_sup_left
  have hL₁Y : LOf L V₁ ≤ Y := h.L₁_le_K.trans hKY
  have hSY := h.isSylowTwoOf_inf_sup hN h1102 hc
  have hOY : pCoreOf 2 Y ≤ T ⊓ K := pCoreOf_two_le_of_isSylowTwoOf hSY
  have hQs := isSolvable_pCoreOf_two Y
  have hQ₁ : pCoreOf 2 Y ≤ Subgroup.normalizer (LOf L V₁ : Set G) :=
    hOY.trans (inf_le_left.trans h.T_le_normalizer_L₁)
  have hKR : modO2Image Y K ≤ ⁅(⊤ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)), ⊤⁆ := by
    rw [← modO2Image_perfect hKY h.perfect]
    exact Subgroup.commutator_mono le_top le_top
  intro heq
  apply h.L₁_ne_K
  refine le_antisymm h.L₁_le_K ?_
  have h1 := le_sup_of_modO2Image_le hKY hL₁Y (heq ▸ hKR)
  calc K = perfectCore K := (perfectCore_eq_self_of_perfect h.perfect).symm
    _ ≤ perfectCore (LOf L V₁ ⊔ pCoreOf 2 Y) := perfectCore_mono h1
    _ = LOf L V₁ := perfectCore_sup_eq h.perfect_L₁ hQs hQ₁

theorem card_map_alphaPGL_xOne (hc : CartanL L V₁ V₂ X) {F : Type} [Field F]
    (e : ↥(K ⊔ SecA.xOne X (LOf L V₁)) ⧸ CFSG.pCore 2 ↥(K ⊔ SecA.xOne X (LOf L V₁)) ≃*
      (GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F))) {x : G}
    (hx : x ∈ SecA.xOne X (LOf L V₁)) (hx1 : x ≠ 1) :
    Nat.card ↥(((SecA.xOne X (LOf L V₁)).subgroupOf (K ⊔ SecA.xOne X (LOf L V₁))).map
      (alphaPGL e)) = 3 := by
  have hX₁Γ : SecA.xOne X (LOf L V₁) ≤ K ⊔ SecA.xOne X (LOf L V₁) := le_sup_right
  have h3 : Nat.card ↥((SecA.xOne X (LOf L V₁)).subgroupOf (K ⊔ SecA.xOne X (LOf L V₁))) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX₁Γ).toEquiv]
    exact hc.cardX₁
  have hd := Subgroup.card_map_dvd
    (H := (SecA.xOne X (LOf L V₁)).subgroupOf (K ⊔ SecA.xOne X (LOf L V₁))) (alphaPGL e)
  rw [h3] at hd
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1
  · exfalso
    have hb := Subgroup.card_eq_one.mp h1
    have hmem : alphaPGL e ⟨x, hX₁Γ hx⟩ ∈
        ((SecA.xOne X (LOf L V₁)).subgroupOf (K ⊔ SecA.xOne X (LOf L V₁))).map (alphaPGL e) :=
      ⟨⟨x, hX₁Γ hx⟩, hx, rfl⟩
    rw [hb, Subgroup.mem_bot, alphaPGL_eq_one_iff] at hmem
    exact hx1 (eq_one_of_mem_of_isPGroup hc.cardX₁
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hx hmem)
  · exact h1

@[expose] noncomputable def pglCongr {F F' : Type} [Field F] [Field F'] (σ : F ≃+* F') :
    (GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)) ≃*
      (GL (Fin 3) F' ⧸ Subgroup.center (GL (Fin 3) F')) :=
  QuotientGroup.congr _ _ (Units.mapEquiv σ.mapMatrix.toMulEquiv) (Subgroup.map_center_eq _)

theorem hB_of_lemmaB414Head (hB : LemmaB414Head) (hN : SecA.NatFacts) (h1102 : Stmt11_0_2)
    (h : StarHyp G T L I V₁ V₂ X K) (hc : CartanL L V₁ V₂ X)
    (St : L3Setting 2 (fsuV T I) V₁ L T (Subgroup.normalizer (V₁ : Set G)))
    (hV₁V : V₁ ≤ fsuV T I) {x : G} (hx : x ∈ SecA.xOne X (LOf L V₁)) (hx1 : x ≠ 1)
    {l₀ : List (Subgroup G × Option (GaloisField 2 2))}
    (hl₀ : IsLabSeries (LOf L V₁ ⊔ SecA.xOne X (LOf L V₁)) (LOf L V₁) x
      (NatData3'.alpha0 St.D hV₁V) V₁ l₀
      (conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)))) :
    ∀ C S : Subgroup G, V₁ ≤ C → S ≤ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) →
      IsYSimple (K ⊔ SecA.xOne X (LOf L V₁)) C S →
      (∃ k ∈ K, ∃ s ∈ S, k * s * k⁻¹ * s⁻¹ ∉ C) →
      ∃ (μ : GaloisField 2 2) (j : ℕ), j < 3 ∧ μ ^ 3 = 1 ∧
        (∃ l : List (Subgroup G × Option (GaloisField 2 2)),
          IsLabSeries (LOf L V₁ ⊔ SecA.xOne X (LOf L V₁)) (LOf L V₁) x
            (NatData3'.alpha0 St.D hV₁V) C l S ∧
          labMultiset l = ({μ ^ (j + 1), (μ ^ j)⁻¹, μ ^ j * μ⁻¹} : Multiset (GaloisField 2 2))) ∧
        (j = 0 → ∀ J : Subgroup G, ⁅S, pCoreOf 2 (LOf L V₁)⁆ ⊔ C ≤ J → J ≤ S →
          (∀ v ∈ S, x * v * x⁻¹ * v⁻¹ ∈ J) → J = S) := by
  intro C S hV₁C hSU hsim hnc
  set U := conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) with hU
  set Γ := K ⊔ SecA.xOne X (LOf L V₁) with hΓ
  obtain ⟨F, _, _, hF, ⟨e₁⟩⟩ := h.pgl
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hF4 : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card, hF]
  have hF₀ : Fintype.card (GaloisField 2 2) = 4 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]
    norm_num
  let e := e₁.trans (pglCongr (FiniteField.ringEquivOfCardEq (hF4.trans hF₀.symm)))
  have hKΓ : K ≤ Γ := le_sup_left
  have hL₁Γ : LOf L V₁ ≤ Γ := h.L₁_le_K.trans hKΓ
  have hX₁Γ : SecA.xOne X (LOf L V₁) ≤ Γ := le_sup_right
  have hUab : ∀ u ∈ U, ∀ v ∈ U, u * v * u⁻¹ * v⁻¹ ∈ V₁ :=
    fun u hu v hv => St.hyp.base.G22_commutator_mem hu hv
  have hsimple : ∀ J : Subgroup G, C ≤ J → J ≤ S → Γ ≤ Subgroup.normalizer (J : Set G) →
      J = C ∨ J = S := fun J hCJ hJS hΓJ =>
    hsim.2.2.2.2 J hCJ hJS (le_normalizer_of_comm (hV₁C.trans hCJ) (hJS.trans hSU) hSU hUab) hΓJ
  have hSY := h.isSylowTwoOf_inf_sup hN h1102 hc
  have hα₀ := NatData3'.alpha0_surjective St.D le_rfl hV₁V
  have hK2 : IsPGroup 2 ↥(pCoreOf 2 (L ⊔ T)) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hL₁ne : LOf L V₁ ≠ ⊥ := by
    intro hb
    have h1 : ∀ w : Fin 3 → GaloisField 2 2,
        St.D.θ ⟨1, L.one_mem⟩ • w = (1 : GaloisField 2 2) • w := fun w => by
      rw [one_smul]
      have : (⟨1, L.one_mem⟩ : ↥L) = 1 := rfl
      rw [this, map_one, one_smul]
    refine IsNatEigSection.not_centralized (NatData3'.natEig_V St.D hV₁V L.one_mem h1) le_rfl
      hα₀ (NatData3'.lOf_le.trans St.D.hnorm) fun k hk v hv => ?_
    rw [hb, Subgroup.mem_bot] at hk
    subst hk
    simp
  have hxΓ : x ∈ Γ := hX₁Γ hx
  refine hB G Γ S C (LOf L V₁) (SecA.xOne X (LOf L V₁)) (GaloisField 2 2) hF₀
    hsim.2.2.2.1 hsim.2.2.1 hsim.1 (fun v hv => hV₁C (St.hyp.base.G22_sq_mem (hSU hv)))
    (fun v hv w hw => hV₁C (hUab v (hSU hv) w (hSU hw))) hsimple hL₁Γ hX₁Γ (alphaPGL e)
    (alphaPGL_surjective e) ?_ ?_ ?_ ?_ ?_ ?_ (card_map_alphaPGL_xOne hc e hx hx1)
    (fun y hy l hl => hy.2.2.2 l hl) (NatData3'.alpha0 St.D hV₁V) hα₀
    (NatData3'.alpha0_ker St.D le_rfl hV₁V hK2) ⟨x, hxΓ⟩ hx ?_
    (exists_isLabSeries_sub le_sup_left
      ((le_sup_right : SecA.xOne X (LOf L V₁) ≤ LOf L V₁ ⊔ SecA.xOne X (LOf L V₁)) hx) hα₀ hl₀
      hUab hV₁C hsim.1.le hSU
      ((sup_le_sup_right h.L₁_le_K _).trans hsim.2.2.1)
      ((sup_le_sup_right h.L₁_le_K _).trans hsim.2.2.2.1))
  ·
    intro γ hγ v hv
    have hγO := (alphaPGL_eq_one_iff e γ).1 hγ
    have hPΓ : pCoreOf 2 Γ ≤ Γ := Subgroup.map_subtype_le _
    have hle := commutator_le_of_isPGroup (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Γ)
      (St.isPGroup_U.to_le hSU) hsim.1 (hPΓ.trans hsim.2.2.2.1) (hPΓ.trans hsim.2.2.1)
      hsim.2.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Γ) hsim.2.2.2.1 hsim.2.2.1 hsimple
    have h1 := hle (Subgroup.commutator_mem_commutator hv hγO)
    have e1 : (γ : G) * v * (γ : G)⁻¹ * v⁻¹ = ⁅v, (γ : G)⁆⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e1]
    exact C.inv_mem h1
  ·
    obtain ⟨k, hk, s, hs, hks⟩ := hnc
    refine ⟨⟨k, hKΓ hk⟩, ?_, s, hs, hks⟩
    have hmem : alphaPGL e ⟨k, hKΓ hk⟩ ∈ (K.subgroupOf Γ).map (alphaPGL e) := ⟨_, hk, rfl⟩
    rw [map_alphaPGL, ← modO2Image_perfect hKΓ h.perfect, Subgroup.map_commutator] at hmem
    rw [commutator_eq_map e, Subgroup.map_commutator]
    exact Subgroup.commutator_mono (Subgroup.map_mono le_top) (Subgroup.map_mono le_top) hmem
  ·
    rw [map_alphaPGL, ← Subgroup.map_commutator, modO2Image_perfect hL₁Γ h.perfect_L₁]
  ·
    rw [map_alphaPGL]
    intro hb
    exact modO2Image_ne_bot hL₁Γ h.perfect_L₁ hL₁ne
      ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hb)
  ·
    rw [map_alphaPGL, commutator_eq_map e]
    intro heq
    exact modO2Image_L₁_ne_commutator hN h1102 h hc (Subgroup.map_injective e.injective heq)
  ·
    refine ⟨(modO2Image Γ (T ⊓ K)).map e.toMonoidHom,
      isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_modO2Image hSY) _ e.surjective, ?_⟩
    rw [map_alphaPGL]
    exact (Subgroup.map_mono (modO2Image_le_normalizer
      (inf_le_left.trans h.T_le_normalizer_L₁))).trans (Subgroup.le_normalizer_map _)
  ·
    intro h1
    exact hx1 (eq_one_of_mem_of_isPGroup hc.cardX₁
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Γ) hx ((alphaPGL_eq_one_iff e _).1 h1))

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
