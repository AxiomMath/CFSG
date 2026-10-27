module

public import CFSG.Milestones.ASVolI.C48.Two
public import CFSG.Quasithin.Background.C48SporS
public import CFSG.Milestones.ASVolI.A1

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem burnsideC48_c48Case1_of_c31Case1 {H R M L V K : Subgroup G} (h : HypC28 H R M L V)
    (hL0 : L = CFSG.Quasithin.conjClosure L M) (h1 : C31Case1 H R M L V K) :
    ChC.C48Case1 R L V := by
  obtain ⟨n, -, -, hcore, hpsl, hnat⟩ := h1
  have hM0K : CFSG.Quasithin.conjClosure L M ≤ K :=
    hcore ▸ (perfectCore_le (M ⊓ K)).trans inf_le_right
  have hLR := (c2_9_two h).1
  have hRV := C48.le_centralizer_V h
  rw [← C48.subgroupOf_conjClosure_eq h] at hnat
  refine ⟨n, by rw [hL0]; exact hpsl, Or.inl ?_⟩
  rcases hnat with ⟨F, hF, hFt, hcard, hNS⟩ | ⟨-, F, hF, hFt, hcard, hNS⟩
  · refine ⟨F, hF, hFt, hcard, ?_⟩
    have hZ : V ⊓ Subgroup.centralizer (CFSG.Quasithin.conjClosure L M : Set G) =
        V ⊓ centerOf K :=
      le_antisymm (C48.inf_centralizer_le_of_isNaturalSection hNS)
        (le_inf inf_le_left (inf_le_right.trans ((inf_le_right : centerOf K ≤ _).trans
          (Subgroup.centralizer_le hM0K))))
    have h2 := C48.isNaturalSection_sup hNS hLR hRV
    rw [← hZ, ← hL0] at h2
    exact h2
  · refine ⟨F, hF, hFt, hcard, ?_⟩
    have h2 := C48.isNaturalSection_sup hNS hLR hRV
    rw [← hL0] at h2
    exact h2

theorem burnsideC48_of_c41Case1 {H R M L V K : Subgroup G}
    (h : HypC28 H R M L V) (hL0 : L = CFSG.Quasithin.conjClosure L M)
    (h1 : ChC.C41Case1 R M L V K) : ChC.C48Case1 R L V ∨ C48Case8 H R M L V K := by
  obtain ⟨n, hn, hblk, hV, hKblk, -, -⟩ := h1
  have hN := C48.subgroupOf_conjClosure_eq h
  rw [← hL0] at hblk hV hN
  rcases hn with rfl | rfl
  · left
    obtain ⟨-, α, hα⟩ := hblk
    have hAlt := (exists_isAltBlockTypeWith_iff_isAltNaturalSection L 5
      (C48.le_normalizer_blockU L)).mp ⟨α, hα⟩
    rw [← hV, ← hN] at hAlt
    have hZ : blockZ L = V ⊓ Subgroup.centralizer (L : Set G) := by
      unfold blockZ
      rw [← hV]
    rw [hZ] at hAlt
    have hLR : L ≤ Subgroup.normalizer (R : Set G) := hL0 ▸ (c2_9_two h).1
    have hA5 : 2 = 2 ∧ IsAltNaturalSection (L ⊔ R) V (V ⊓ Subgroup.centralizer (L : Set G))
        (R.subgroupOf (L ⊔ R)) 5 :=
      ⟨rfl, C48.isAltNaturalSection_sup hAlt hLR (C48.le_centralizer_V h)⟩
    obtain ⟨e⟩ := C48.modO2_mulEquiv_of_surj α hα.1 hα.2.1
    exact ⟨2, C126.isPSL_two_two_two_of_alternating_five _ ⟨e⟩, Or.inr (Or.inl hA5)⟩
  · exact Or.inr ⟨hKblk, hblk⟩

theorem burnsideC48_le_normalizer_V {H R M L V : Subgroup G} (h : HypC28 H R M L V) :
    L ≤ Subgroup.normalizer (V : Set G) := by
  have h0 := A3.sup_le_normalizer_commutator V (CFSG.Quasithin.conjClosure L M)
  rw [h.V_comm] at h0
  exact (CFSG.Quasithin.le_conjClosure L M).trans (le_sup_right.trans h0)

theorem burnsideC48_c48Case1_of_c41Case2 {H R M L V K : Subgroup G} (h : HypC28 H R M L V)
    (hL0 : L = CFSG.Quasithin.conjClosure L M) (hLK : L ≤ K) (h2 : ChC.C41Case2 M L V K) :
    ChC.C48Case1 R L V := by
  obtain ⟨-, F, _, _, α, β, hF, ⟨-, -, hβs, hβker, hβeq⟩, hfl, -, -, hpsl0⟩ := h2
  have hpsl : IsPSL 2 2 2 (ModO2 L) := by
    rw [hL0]
    exact hpsl0
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := burnsideC48_le_normalizer_V h
  have hVL : ⁅V, L⁆ = V := by
    have h0 := h.V_comm
    rwa [← hL0] at h0
  have hVK : V ≤ K := by
    have h0 := h.V_le
    rw [← hL0] at h0
    exact h0.trans hLK
  have hLZ : L ≤ Subgroup.centralizer (blockZ K : Set G) := fun l hl =>
    Subgroup.mem_centralizer_iff.mpr fun z hz =>
      (Subgroup.mem_centralizer_iff.mp hz.2 l (hLK hl)).symm
  have hsupN : ∀ {A B : Subgroup G} {x : G}, x ∈ Subgroup.normalizer (A : Set G) →
      x ∈ Subgroup.normalizer (B : Set G) →
        x ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
    intro A B x hA hB
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
    rw [Subgroup.map_sup, hA, hB]
  have hLVZ : L ≤ Subgroup.normalizer ((V ⊔ blockZ K : Subgroup G) : Set G) := fun l hl =>
    hsupN (hLV hl) (C48.le_normalizer_of_le_centralizer hLZ hl)
  have hRV := C48.le_centralizer_V h
  have hO : pCoreOf 2 L ≤ Subgroup.centralizer ((V ⊔ blockZ K : Subgroup G) : Set G) := by
    have h0 := C48.pCoreOf_conjClosure_le h
    rw [← hL0] at h0
    rw [Subgroup.le_centralizer_iff]
    refine sup_le ?_ ?_
    · rw [← Subgroup.le_centralizer_iff]
      exact h0.trans hRV
    · rw [← Subgroup.le_centralizer_iff]
      exact (CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLZ
  have hnt : ¬ ⁅V ⊔ blockZ K, L⁆ ≤ blockZ K := by
    intro hle
    have hVZ : V ≤ blockZ K := by
      rw [← hVL]
      exact (Subgroup.commutator_mono le_sup_left le_rfl).trans hle
    apply h.V_ne
    rw [← hVL, eq_bot_iff]
    calc ⁅V, L⁆ ≤ ⁅blockZ K, L⁆ := Subgroup.commutator_mono hVZ le_rfl
      _ = ⊥ := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hLZ
  have hNS := C48.isNaturalSection_of_line α β hβs hβker hβeq hfl hLK hLVZ
    (perfect_of_mem_cComp h.comp) (n := 2) (by rw [Nat.card_eq_fintype_card, hF]; norm_num)
    hpsl hO hnt
  have hVZn : V ≤ Subgroup.normalizer (blockZ K : Set G) :=
    C48.le_normalizer_of_le_centralizer fun x hx => Subgroup.mem_centralizer_iff.mpr fun z hz =>
      (Subgroup.mem_centralizer_iff.mp hz.2 x (hVK hx)).symm
  have hNS' := C48.isNaturalSection_of_sup hNS hLV hVZn
  have hZL : blockZ K ≤ Subgroup.centralizer (L : Set G) := Subgroup.le_centralizer_iff.mp hLZ
  have hZeq : V ⊓ blockZ K = V ⊓ Subgroup.centralizer (L : Set G) :=
    le_antisymm (inf_le_inf_left V hZL) (C48.inf_centralizer_le_of_isNaturalSection hNS')
  rw [hZeq] at hNS'
  have hN := C48.subgroupOf_conjClosure_eq h
  rw [← hL0] at hN
  rw [← hN] at hNS'
  have hLR : L ≤ Subgroup.normalizer (R : Set G) := hL0 ▸ (c2_9_two h).1
  exact ⟨2, hpsl, Or.inl ⟨F, inferInstance, inferInstance, by rw [hF]; norm_num,
    C48.isNaturalSection_sup hNS' hLR hRV⟩⟩

theorem burnsideC48_c48Case1_of_c41Case3 {H R M L V K : Subgroup G} (h : HypC28 H R M L V)
    (hL0 : L = CFSG.Quasithin.conjClosure L M) (hLK : L ≤ K) (h3 : ChC.C41Case3 R M L V K) :
    ChC.C48Case1 R L V := by
  obtain ⟨n, F, _, _, hn, hF, -, -, -, -, hpsl0, hcase⟩ := h3
  have hpsl : IsPSL 2 2 n (ModO2 L) := by
    rw [hL0]
    exact hpsl0
  rcases hcase with hline | ⟨h134, V₁, V₂, hl1, hl2, hV12⟩
  · have hVne : ⁅V, L⁆ ≠ ⊥ := by
      have h0 := h.V_comm
      rw [← hL0] at h0
      rw [h0]
      exact h.V_ne
    exact ⟨n, hpsl, Or.inl ⟨F, inferInstance, inferInstance, hF,
      C48.isNaturalSection_of_isStabilizedLine h hL0 hLK hF hpsl le_rfl hline hVne⟩⟩
  · exact burnsideC48_c48Case1_of_twoLines h hL0 hLK hn hF hpsl h134 hl1 hl2 hV12

theorem burnsideC48_not_isC134Case_two {H K R : Subgroup G} (hK : CFSG.Open.IsComponentOf K H)
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) : ¬ IsC134Case 2 (K ⊔ R) R K := by
  rintro ⟨⟨n, F, _, _, α, -, ⟨hαs, -⟩, hsum⟩, -⟩
  obtain ⟨-, -, β, hβ, -, hβeq⟩ := hsum
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pCoreOf 2 (K ⊔ R) with hP
  have hKN : K ⊔ R ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hRK
  have hKP : K ≤ Subgroup.normalizer (P : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ R))
  have h1 : ⁅P, K⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro p hp k hk
    rw [commutatorElement_def]
    have hpK : p * k * p⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hKN (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hp)) k).mp hk
    exact K.mul_mem hpK (K.inv_mem hk)
  have h2 : ⁅P, K⁆ ≤ P := by
    rw [Subgroup.commutator_le]
    intro p hp s hs
    rw [commutatorElement_def]
    have h3 : s * p⁻¹ * s⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (hKP hs) _).mp (P.inv_mem hp)
    have := P.mul_mem hp h3
    simpa [mul_assoc] using this
  have hN : ((P ⊓ K).subgroupOf K).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hKP g.2) _).mp hx.1, ?_⟩
    exact K.mul_mem (K.mul_mem g.2 hx.2) (K.inv_mem g.2)
  rcases CFSG.ASVolI.A129Aux.normal_eq_top_or_le_center hK.2.2 hN with htop | hcen
  ·
    have hKle : K ≤ P := by
      intro k hk
      have : (⟨k, hk⟩ : ↥K) ∈ (P ⊓ K).subgroupOf K := htop ▸ Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp this).1
    have hKp : IsPGroup 2 ↥K := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (K ⊔ R)).to_le hKle
    have hbot : (⊥ : Subgroup ↥K) = ⊤ :=
      C48.eq_top_of_isPGroup_quotient (C48Spor.commutator_eq_of_isComponentOf hK) ⊥
        (hKp.of_equiv QuotientGroup.quotientBot.symm)
    have hsub : Subsingleton ↥K := by
      refine ⟨fun a b => ?_⟩
      have ha : a ∈ (⊥ : Subgroup ↥K) := hbot ▸ Subgroup.mem_top a
      have hb : b ∈ (⊥ : Subgroup ↥K) := hbot ▸ Subgroup.mem_top b
      rw [Subgroup.mem_bot] at ha hb
      rw [ha, hb]
    have hsimp := hK.2.2.2
    have hnt : Nontrivial (↥K ⧸ Subgroup.center ↥K) := hsimp.toNontrivial
    obtain ⟨x, y, hxy⟩ := hnt
    apply hxy
    obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) x
    obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) y
    rw [Subsingleton.elim x' y']
  ·
    obtain ⟨q, hq⟩ := hβ (Multiplicative.ofAdd (fun _ _ => (1 : F)))
    have hfw : (LinearMap.proj 1 : (Fin 3 → F) →ₗ[F] F) (Pi.single 0 1) = 0 := by simp
    obtain ⟨k, hk⟩ := hαs (burnsideC48_tvSL (LinearMap.proj 1) (Pi.single 0 1) hfw)
    have hqK : (q : G) ∈ K := h1 q.2
    have hqZ : (⟨q, hqK⟩ : ↥K) ∈ Subgroup.center ↥K := hcen ⟨h2 q.2, hqK⟩
    have hcomm : (q : G) = k * q * (k : G)⁻¹ := by
      have h3 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hqZ k)
      simp only [Subgroup.coe_mul] at h3
      rw [h3, mul_inv_cancel_right]
    have h3 := hβeq k q q hcomm 0
    rw [hq, hk] at h3
    have h4 := congrFun h3 0
    simp only [toAdd_ofAdd, moduleAct, Bool.false_eq_true, ↓reduceIte, burnsideC48_tvSL_mulVec,
      Pi.add_apply, Pi.smul_apply, LinearMap.proj_apply, Pi.single_eq_same, smul_eq_mul,
      mul_one] at h4
    have h5 : (1 : F) + 1 = 1 + 0 := by rw [add_zero]; exact h4.symm
    exact one_ne_zero (add_left_cancel h5)

theorem burnsideC48_c48Case1_of_wip {H R M L V K : Subgroup G} (hw : C48Case1 H R M L V K)
    (hno : ¬ IsC134Case 2 (K ⊔ R) R K) : ChC.C48Case1 R L V := by
  obtain ⟨n, hpsl, h1 | h2 | ⟨-, h134, -⟩⟩ := hw
  · exact ⟨n, hpsl, Or.inl h1⟩
  · exact ⟨n, hpsl, Or.inr (Or.inl h2)⟩
  · exact absurd h134 hno

theorem burnsideC48_or9_of_spor {H R M L V K : Subgroup G} (hno : ¬ IsC134Case 2 (K ⊔ R) R K)
    (hs : C48Case1 H R M L V K ∨ C48Case2 H R M L V K ∨ C48Case3 H R M L V K ∨
      C48Case4 H R M L V K ∨ C48Case5 H R M L V K ∨ C48Case6 H R M L V K ∨
      C48Case7 H R M L V K) :
    ChC.C48Case1 R L V ∨ C48Case2 H R M L V K ∨ C48Case3 H R M L V K ∨ C48Case4 H R M L V K ∨
      C48Case5 H R M L V K ∨ C48Case6 H R M L V K ∨ C48Case7 H R M L V K ∨
      C48Case8 H R M L V K ∨ C48Case9 H R M L V K := by
  rcases hs with c1 | c2 | c3 | c4 | c5 | c6 | c7
  · exact Or.inl (burnsideC48_c48Case1_of_wip c1 hno)
  · exact Or.inr (Or.inl c2)
  · exact Or.inr (Or.inr (Or.inl c3))
  · exact Or.inr (Or.inr (Or.inr (Or.inl c4)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c5))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c6)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c7))))))

end CFSG.ASVolI
