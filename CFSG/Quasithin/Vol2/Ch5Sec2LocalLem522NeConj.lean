module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522NeLt
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522NeIndex

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

@[expose] def Stmt5_2_2_ne_conj_c2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ Dp : Subgroup G) (n p : ℕ),
    Hyp5_2_2p G T M L V H B D L₂ Dp n p →
    pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H)) ≠ ⊥ →
    pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B) ≠ ⊥ →
    ¬ H ≤ Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B →
    T ⊓ Subgroup.normalizer (L₂ : Set G) < T → L₂ < oTwoUpper H →
    ¬ Dp ≤ Subgroup.normalizer (L₂ : Set G) →
    ∀ T₁ : Subgroup G,
      IsSylowTwoOf T₁ (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B) →
      T ⊓ Subgroup.normalizer (L₂ : Set G) < T₁ → quasithinIsSylowTwo T₁ → T₁ ≤ M →
      T₁ ≤ Subgroup.normalizer ((T ⊓ Subgroup.normalizer (L₂ : Set G) : Subgroup G) : Set G) →
      quasithinIsCComponent L₂ H → oTwoUpper H = conjClosure L₂ T →
    ∀ Kh₁ : Subgroup G,
      pCoreOf 2 (Subgroup.normalizer ((T ⊓ Subgroup.normalizer (L₂ : Set G) : Subgroup G) :
        Set G) ⊔ H) ≠ ⊥ →
      IsHatComp (Subgroup.normalizer ((T ⊓ Subgroup.normalizer (L₂ : Set G) : Subgroup G) :
        Set G) ⊔ H) L₂ Kh₁ →
      LieModel (O2Q L₂) .PSL 2 2 2 →
      (IsSporadic .J1 (O2Q Kh₁) ∨ ∃ q : ℕ, q.Prime ∧ q ^ 2 % 5 = 1 ∧ (q % 8 = 3 ∨ q % 8 = 5) ∧
        IsPSL 2 q 1 (O2Q Kh₁)) →
      oTwoUpper H = conjClosure L₂ T₁

section General

variable {G : Type} [Group G]

theorem conjClosure_map_conj_of_mem {Z H : Subgroup G} {t : G} (ht : t ∈ H) :
    conjClosure (Z.map (MulAut.conj t).toMonoidHom) H = conjClosure Z H := by
  apply le_antisymm
  · refine conjClosure_le fun h hh w hw => ?_
    obtain ⟨z, hz, rfl⟩ := hw
    have := mem_conjClosure (Z := Z) (H.mul_mem hh ht) hz
    simpa [MulAut.conj_apply, mul_assoc] using this
  · refine conjClosure_le fun h hh z hz => ?_
    have hzt : t * z * t⁻¹ ∈ Z.map (MulAut.conj t).toMonoidHom := ⟨z, hz, by simp⟩
    have := mem_conjClosure (Z := Z.map (MulAut.conj t).toMonoidHom)
      (H.mul_mem hh (H.inv_mem ht)) hzt
    simpa [mul_assoc] using this

end General

namespace Hyp5_2_2p

variable {G : Type} [Group G] [Finite G] {T M L V H B D L₂ Dp : Subgroup G} {n p : ℕ}

theorem false_of_simple_bender (hyp : Hyp5_2_2p G T M L V H B D L₂ Dp n p)
    (h38 : Vol2Native.A38ForSQTKCat) (hL₂K : L₂ < oTwoUpper H)
    (hsimple : IsSimpleGroup (O2Q (oTwoUpper H))) (hbend : IsBenderAny (O2Q (oTwoUpper H))) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have hHO : pCoreOf 2 H ≠ ⊥ := hyp.hStar.1.2
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  obtain ⟨K₁, hK₁, hKeq, hcase⟩ := hyp.choice
  rcases hcase with ⟨-, rfl⟩ | ⟨hnb, hK1eq, -⟩
  · obtain ⟨K₂, tc⟩ := exists_twoComp h38 hloc hHO hTH hK₁ hKeq hL₂K
    have hsup : oTwoUpper H = L₂ ⊔ K₂ := tc.sup
    set K := oTwoUpper H with hKdef
    have hL₂Kle : L₂ ≤ K := hL₂K.le
    have hK₂K : K₂ ≤ K := by rw [hsup]; exact le_sup_right
    have hKN : K ≤ Subgroup.normalizer (L₂ : Set G) := by
      rw [hsup]
      exact sup_le Subgroup.le_normalizer (le_normalizer_of_mem_cComp hK₁ tc.cK₂)
    have hKperf : ⁅K, K⁆ = K := by
      apply le_antisymm
      · rw [Subgroup.commutator_le]
        intro x hx y hy
        rw [commutatorElement_def]
        exact K.mul_mem (K.mul_mem (K.mul_mem hx hy) (K.inv_mem hx)) (K.inv_mem hy)
      · calc K = L₂ ⊔ K₂ := hsup
          _ = ⁅L₂, L₂⁆ ⊔ ⁅K₂, K₂⁆ := by rw [hK₁.2.1, tc.cK₂.2.1]
          _ ≤ ⁅K, K⁆ := sup_le (Subgroup.commutator_mono hL₂Kle hL₂Kle)
              (Subgroup.commutator_mono hK₂K hK₂K)
    have hn : (modO2Image K L₂).Normal :=
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hL₂Kle).mpr hKN).map _
        (QuotientGroup.mk'_surjective _)
    rcases hsimple.eq_bot_or_eq_top_of_normal (modO2Image K L₂) with h0 | h0
    · have hle : L₂.subgroupOf K ≤ CFSG.pCore 2 ↥K := by
        intro x hx
        have hx' : QuotientGroup.mk' (CFSG.pCore 2 ↥K) x ∈ modO2Image K L₂ := ⟨x, hx, rfl⟩
        rw [h0, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
        exact hx'
      have h2 : IsPGroup 2 ↥(L₂.subgroupOf K) :=
        (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).to_le hle
      have h2' : IsPGroup 2 ↥L₂ := h2.of_equiv (Subgroup.subgroupOfEquivOfLe hL₂Kle)
      exact hK₁.1 (Vol2Native.eq_bot_of_perfect_of_isPGroup L₂ h2' hK₁.2.1)
    · have hle := Vol2.Ch11.SecS.le_sup_of_modO2Image_eq_top hL₂Kle h0
      have hOK : pCoreOf 2 K ≤ Subgroup.normalizer (L₂ : Set G) := (pCoreOf_le 2 K).trans hKN
      exact hL₂K.ne (le_antisymm hL₂Kle
        (le_of_perfect_of_le_sup hKperf hle (pCoreOf_isPGroup 2 K) hOK))
  · apply hnb
    rw [hK1eq]
    exact hbend

theorem conjClosure_map_conj_eq (hyp : Hyp5_2_2p G T M L V H B D L₂ Dp n p)
    (h510 : Stmt5_1_10) (h38 : Vol2Native.A38ForSQTKCat) (hF : FactL2LieParabolic)
    (hL₂K : L₂ < oTwoUpper H) (hT₀ : T ⊓ Subgroup.normalizer (L₂ : Set G) < T) {x : G}
    (hxK : x ∈ Subgroup.normalizer (oTwoUpper H : Set G))
    (hxTK : x ∈ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G)) :
    conjClosure (L₂.map (MulAut.conj x).toMonoidHom) T = oTwoUpper H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have hHO : pCoreOf 2 H ≠ ⊥ := hyp.hStar.1.2
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hKN : ∀ s ∈ T, s ∈ Subgroup.normalizer (oTwoUpper H : Set G) := fun s hs =>
    le_normalizer_oTwoUpper H (hTH.1 hs)
  obtain ⟨K₁, hK₁, hKeq, hcase⟩ := hyp.choice
  rcases hcase with ⟨-, rfl⟩ | ⟨hnb, hK1eq, P, hP, hL₂P⟩
  ·
    obtain ⟨K₂, tc⟩ := exists_twoComp h38 hloc hHO hTH hK₁ hKeq hL₂K
    have hL₂c : L₂ ∈ cComp (oTwoUpper H) := cComp_mem_of_le hK₁ hL₂K.le (oTwoUpper_le H)
    have hx : L₂.map (MulAut.conj x).toMonoidHom ∈ cComp (oTwoUpper H) := by
      have := quasithinIsCComponent_map (MulAut.conj x) hL₂c
      rwa [map_conj_eq_of_mem_normalizer_ch6 hxK] at this
    rcases tc.cK _ hx with h1 | h1
    · rw [h1, hKeq]
    · obtain ⟨t, ht, ht₂⟩ := tc.conj
      rw [h1, ht₂, conjClosure_map_conj_of_mem ht, hKeq]
  ·
    have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
      A4.isSylowTwoOf_inf_normal hTH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
    obtain ⟨k, hk, htype, -, hMK⟩ :=
      nonBender_type h510 hyp.toHyp5_1_8 hyp.notation59 hK₁ hnb hK1eq
    obtain ⟨hL₂eq, -, -, -⟩ := l2Lie_nonBender hF hk htype hTK hMK hP hL₂P
    obtain ⟨Pj, hPj, -, -⟩ := exists_parabolics hF hk htype hTK
    have hOS : pCoreOf 2 (oTwoUpper H) ≤ T ⊓ oTwoUpper H := F7.isSylowTwoOf_pCoreOf_le hTK
    have hdet : ∀ A B : Subgroup G, IsMaxParabolicOver (oTwoUpper H) (T ⊓ oTwoUpper H) A →
        IsMaxParabolicOver (oTwoUpper H) (T ⊓ oTwoUpper H) B →
        modO2Image (oTwoUpper H) A = modO2Image (oTwoUpper H) B → A = B := by
      intro A B hA hB hAB
      rw [← map_comap_modO2Image_of_le hA.1 (hA.pCoreOf_le hTK.1 hOS),
        ← map_comap_modO2Image_of_le hB.1 (hB.pCoreOf_le hTK.1 hOS), hAB]
    have hL₂s : ∀ s : G, L₂.map (MulAut.conj s).toMonoidHom =
        perfectCore (P.map (MulAut.conj s).toMonoidHom) := fun s => by
      rw [hL₂eq, map_perfectCore]
    obtain ⟨t₁, ht₁, ht₁N⟩ : ∃ t₁ ∈ T, t₁ ∉ Subgroup.normalizer (L₂ : Set G) := by
      by_contra hall
      push Not at hall
      exact hT₀.ne (le_antisymm inf_le_left fun t ht => ⟨ht, hall t ht⟩)
    have hPt₁ : IsMaxParabolicOver (oTwoUpper H) (T ⊓ oTwoUpper H)
        (P.map (MulAut.conj t₁).toMonoidHom) :=
      hP.map_conj (hKN t₁ ht₁)
        (Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht₁, hKN t₁ ht₁⟩)
    have hPx : IsMaxParabolicOver (oTwoUpper H) (T ⊓ oTwoUpper H)
        (P.map (MulAut.conj x).toMonoidHom) := hP.map_conj hxK hxTK
    obtain ⟨j₀, hj₀⟩ := hPj P hP
    obtain ⟨j₁, hj₁⟩ := hPj _ hPt₁
    obtain ⟨jx, hjx⟩ := hPj _ hPx
    have hj : j₀ ≠ j₁ := by
      intro hj
      apply ht₁N
      rw [CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj, hL₂s,
        hdet _ _ hPt₁ hP (by rw [hj₁, hj₀, hj]), hL₂eq]
    have hKL₂ : oTwoUpper H = conjClosure L₂ T :=
      stmt5_2_L2Gen_of hF h510 G T M L H B D K₁ P L₂ n hyp.toHyp5_1_8 hyp.notation59 hK₁ hKeq
        hnb hK1eq hP hL₂P
    have hfin : ∀ a b c : Fin 2, a ≠ b → c = a ∨ c = b := by decide
    rcases hfin j₀ j₁ jx hj with rfl | rfl
    · rw [hL₂s, hdet _ _ hPx hP (by rw [hjx, hj₀]), ← hL₂eq, ← hKL₂]
    · rw [hL₂s, hdet _ _ hPx hPt₁ (by rw [hjx, hj₁]), ← hL₂s, conjClosure_map_conj_of_mem ht₁,
        ← hKL₂]

end Hyp5_2_2p

theorem stmt5_2_2_ne_conj_of (h510 : Stmt5_1_10)
    (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact) (h311 : Theorem311Stmt) (h512 : Stmt5_1_12)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hF : FactL2LieParabolic)
    (hc2 : Stmt5_2_2_ne_conj_c2) : Stmt5_2_2_ne_conj := by
  intro G _ _ T M L V H B D L₂ Dp n p hyp hO hOX hHX hT₀ hL₂K hDp T₁ hT₁ hlt hT₁syl hT₁M
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  set S := sec52S M H with hSdef
  set T₀ := T ⊓ Subgroup.normalizer (L₂ : Set G) with hT₀def
  set K := oTwoUpper H with hKdef
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hT₀2 : IsPGroup 2 ↥T₀ := h.sylow.1.to_le inf_le_left
  have hidx := stmt5_2_2_ne_index_of h510 h38 hF G T M L V H B D L₂ Dp n p hyp hL₂K hT₀
  have hT₀N : T ≤ Subgroup.normalizer (T₀ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mp
      (Subgroup.normal_of_index_eq_two hidx)
  have hT : Nat.card T = 2 * Nat.card T₀ := by
    have := Subgroup.relIndex_mul_card T₀ T
    rw [hidx, inf_eq_left.mpr inf_le_left] at this
    exact this.symm
  have hT₁card : Nat.card T₁ = Nat.card T :=
    le_antisymm (card_le_of_isPGroup_of_quasithinIsSylowTwo h.sylow hT₁syl.1)
      (card_le_of_isPGroup_of_quasithinIsSylowTwo hT₁syl h.sylow.1)
  have hidx₁ : T₀.relIndex T₁ = 2 := by
    have h1 := Subgroup.relIndex_mul_card T₀ T₁
    rw [inf_eq_left.mpr hlt.le, hT₁card, hT] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hT₁N : T₁ ≤ Subgroup.normalizer (T₀ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hlt.le).mp
      (Subgroup.normal_of_index_eq_two hidx₁)
  obtain ⟨hST, -, -, hSK, -, -, hOMS, -⟩ := hyp.S_facts h510 h331 hR
  have hST₀ : S ≤ T₀ := le_inf hST hyp.S_le
  have hT₀1 : T₀ ≠ ⊥ := by
    intro h0
    apply pCoreOf_ne_bot_of_isTwoLocal h.maxTwoLocal.1
    exact le_bot_iff.mp (h0 ▸ hOMS.trans hST₀)
  have hTKN : T ≤ Subgroup.normalizer (K : Set G) :=
    hyp.hStar.1.1.trans (le_normalizer_oTwoUpper H)
  have hKT : K ⊓ T ≤ T₀ := by
    intro x hx
    have hxS : x ∈ S ⊓ K := by
      rw [hSK]
      exact ⟨hx.2, hx.1⟩
    exact hST₀ hxS.1
  have hRS : IsSylowTwoOf T₀ (K ⊔ T₀) :=
    isSylowTwoOf_sup_of_inf_le inf_le_left hTKN hKT (h.isSylowTwoOf le_sup_right)
  have hu : ∃ N : Subgroup G, IsUniqueMaxOver H T N := by
    obtain ⟨P, hP⟩ := exists_sylow_coe_eq h.sylow
    have hstar : IsHStar (P : Subgroup G) M H := hP ▸ hyp.hStar
    have hTM : (P : Subgroup G) ≤ M := hP ▸ h.T_le
    exact ⟨H ⊓ M, hP ▸ hstar.isUniqueMaxOver P hTM⟩
  have hM₀ : InH T (Subgroup.normalizer (T₀ : Set G)) := by
    refine ⟨hT₀N, fun h0 => hT₀1 (le_bot_iff.mp ?_)⟩
    rw [← h0]
    exact le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hT₀2
  obtain ⟨R₀, hR₀1, hR₀T₀, hR₀N⟩ := h311 G T h.simple h.nonabelian h.qtke h.sylow _ H T₀ hM₀
    hyp.hStar.1 hu hT₀1 inf_le_left hRS le_rfl
  set X := Subgroup.normalizer (T₀ : Set G) ⊔ H with hXdef
  have hOX' : pCoreOf 2 X ≠ ⊥ := by
    intro h0
    apply hR₀1
    have hle : R₀ ≤ pCoreOf 2 X :=
      le_pCoreOf_of_le_normalizer 2 ((hR₀T₀.trans Subgroup.le_normalizer).trans le_sup_left)
        hR₀N (hT₀2.to_le hR₀T₀)
    rw [h0] at hle
    exact le_bot_iff.mp hle
  have hX : InH H X := ⟨le_sup_right, hOX'⟩
  have hTX : IsSylowTwoOf T X := h.isSylowTwoOf (hT₀N.trans le_sup_left)
  obtain ⟨k, hk⟩ := h510.exists_fieldParam hyp.toHyp5_1_8 hyp.notation59
  obtain ⟨K₁, hK₁, hKeq, hcase⟩ := hyp.choice
  obtain ⟨Kh₁, hhat, -, hcases⟩ :=
    h512 G T M L H B D K₁ n k hyp.toHyp5_1_8 hyp.notation59 hk hK₁ hKeq X hX
  rcases hcases with ha | ⟨hlt₁, hL4, hJ⟩ | ⟨hSz, -⟩ | ⟨hL2k, -⟩ | ⟨hL4', -⟩
  ·
    have hKX : X ≤ Subgroup.normalizer (K : Set G) := by
      rw [hKdef, ha]
      exact Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot hloc h37 h38 hOX' hTX hhat.1
    have hT₁K : T₁ ≤ Subgroup.normalizer (K : Set G) := (hT₁N.trans le_sup_left).trans hKX
    have hTY : IsSylowTwoOf T (T ⊔ T₁) := h.isSylowTwoOf le_sup_left
    have hT₁Y : IsSylowTwoOf T₁ (T ⊔ T₁) := isSylowTwoOf_of_isSylowTwo hT₁syl le_sup_right
    obtain ⟨y, hyY, hy⟩ := A4.exists_conj_of_isSylowTwoOf hTY hT₁Y
    have hT₁eq : T.map (MulAut.conj y).toMonoidHom = T₁ := by
      ext x
      rw [hy x, Subgroup.mem_map]
      constructor
      · rintro ⟨t, ht, rfl⟩
        have e : y⁻¹ * ((MulAut.conj y).toMonoidHom t) * y = t := by
          simp [MulAut.conj_apply, mul_assoc]
        rw [e]
        exact ht
      · intro hx
        exact ⟨y⁻¹ * x * y, hx, by simp [MulAut.conj_apply, mul_assoc]⟩
    have hyK : y ∈ Subgroup.normalizer (K : Set G) := (sup_le hTKN hT₁K) hyY
    have hKy : K.map (MulAut.conj y).toMonoidHom = K := map_conj_eq_of_mem_normalizer_ch6 hyK
    have hTKy : (T ⊓ K).map (MulAut.conj y).toMonoidHom = T₁ ⊓ K := by
      rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj y).injective, hT₁eq, hKy]
    have hTK₁ : T₁ ⊓ K = T ⊓ K := by
      have hle : T ⊓ K ≤ T₁ ⊓ K := le_inf ((inf_comm T K ▸ hKT).trans hlt.le) inf_le_right
      have hcard : Nat.card ↥(T₁ ⊓ K) = Nat.card ↥(T ⊓ K) := by
        rw [← hTKy, Subgroup.card_map_of_injective (MulAut.conj y).injective]
      exact (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm
    have hyTK : y ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
      rw [CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj, hTKy, hTK₁]
    have hc := hyp.conjClosure_map_conj_eq h510 h38 hF hL₂K hT₀ (x := y⁻¹)
      (Subgroup.inv_mem _ hyK) (Subgroup.inv_mem _ hyTK)
    have e1 : (L₂.map (MulAut.conj y⁻¹).toMonoidHom).map (MulAut.conj y).toMonoidHom = L₂ := by
      rw [Subgroup.map_map]
      ext z
      simp [MulAut.conj_apply, mul_assoc]
    have e2 := map_conjClosure_eq (MulAut.conj y).toMonoidHom
      (L₂.map (MulAut.conj y⁻¹).toMonoidHom) T
    rw [e1, hT₁eq, hc, hKy] at e2
    exact e2
  ·
    rcases hcase with ⟨-, rfl⟩ | ⟨-, hK1eq, -⟩
    · exact hc2 G T M L V H B D L₂ Dp n p hyp hO hOX hHX hT₀ hL₂K hDp T₁ hT₁ hlt hT₁syl hT₁M
        hT₁N hK₁ hKeq Kh₁ hOX' hhat hL4 hJ
    · exact absurd hK1eq hlt₁.ne
  ·
    have hsimple : IsSimpleGroup (O2Q K) := by
      obtain ⟨-, a, ha, F, _, _, hka, hF2, ⟨e⟩⟩ := hSz
      have hF2' : Nat.card F = 2 ^ (2 * a + 1) := by rw [← hka]; exact hF2
      have := (CFSG.LieType.Ree.suzuki_simple ha hF2').2.2
      exact e.isSimpleGroup
    exact (hyp.false_of_simple_bender h38 hL₂K hsimple ⟨k, hk.1.1, Or.inr (Or.inl hSz)⟩).elim
  · exact (hyp.false_of_simple_bender h38 hL₂K (isSimpleGroup_of_lieModel_PSL2 hL2k)
      ⟨k, hk.1.1, Or.inl hL2k⟩).elim
  · exact (hyp.false_of_lieModel_two h38 hL₂K hL4').elim

end CFSG.Quasithin.H13
