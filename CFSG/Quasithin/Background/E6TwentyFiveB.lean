module

public import CFSG.Quasithin.Background.E6TwentyTwoA
public import CFSG.Quasithin.Background.E6ElevenStrong

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique

@[expose] def E625NotTwoBlock : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U L X : Subgroup G) (hV : CFSG.Open.IsElemAbelian 2 V),
    E625Setting T M V U hV → E611Data hV M U L X → IsBlock2 (Subgroup.centralizer (U : Set G)) L →
    ∀ (Y : Fin 2 → Subgroup (MulAut (IntMod V hV))) (Vs : Fin 2 → Subgroup (IntMod V hV)),
      E624Body hV M X 2 Y Vs → Nat.card (autI hV X) = 3 → (∀ i, autI hV X ≠ Y i) → False

section Tools

variable {W : Type*} [CommGroup W]

theorem mem_fixV_zpowers_of_apply_eq {t : MulAut W} {v : W} (h : t v = v) :
    v ∈ fixV (Subgroup.zpowers t) :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply.2 h

end Tools

section Main

variable {G : Type} [Group G] [Finite G]

theorem e625NotTwo_of (hlist : Lemma115_3_List) (h621 : E621Stmt) (hCent : E68CentComp)
    (hAlt : E68AltRank) (hBlock : E625NotTwoBlock) : E625NotTwo := by
  intro G _ _ T M V U L X hV hset hD Y Vs hB hX3 hXY
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD' := hD
  obtain ⟨hLU, -, hLM, hCL, hXLM, hXcyc, hXcard, hUX1, hUX2, hreg, hnorm, -, -, htype⟩ := hD'
  obtain hLb | hLc : IsBlock2 (Subgroup.centralizer (U : Set G)) L ∨
      IsComponentIn L (Subgroup.centralizer (U : Set G)) := by
    rcases htype with ⟨⟨hLb, -⟩ | ⟨hLc, -⟩, -⟩ | ⟨hLc, -⟩
    · exact Or.inl hLb
    · exact Or.inr hLc
    · exact Or.inr hLc
  · exact hBlock G T M V U L X hV hset hD hLb Y Vs hB hX3 hXY
  obtain ⟨h, hm, hU, hr, hU1, hUm⟩ := hset
  have := h.simple
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := IntMod.sq_eq_one
  have hV2 : IsPGroup 2 V := h.isPGroup_V
  have hXMU : X ≤ M ⊓ Subgroup.centralizer (U : Set G) :=
    le_inf (hXLM.trans inf_le_right) ((hXLM.trans inf_le_left).trans hLU)
  have hXN : X ≤ Subgroup.normalizer (V : Set G) :=
    hXMU.trans (inf_centralizer_le_normalizer h hU.1 hU.2.1)
  obtain ⟨-, hfixmap, hcardc⟩ := hyp102_autI hV h hU hU1 hUm hXMU hXcyc hXcard hUX2 hreg hnorm
  obtain ⟨⟨hYsup, hYind, hYcomm⟩, ⟨-, hfix2⟩, ⟨hVsup, hVind, hVi⟩, ⟨hperm, -⟩, hdich⟩ := hB
  have hY0 : fixV (e624Y hV M X) = ⊥ := fixV_e624Y_eq_bot hV h hU hfixmap
  have hVtop : commSub ⊤ (e624Y hV M X) = ⊤ := by
    rw [hY0, bot_sup_eq] at hfix2
    exact hfix2
  rcases hdich with ⟨i, hi⟩ | ⟨-, i₀, hXY₀, hcl, h21, -, h8⟩
  · exact hXY i hi
  have hn2 : E3.mQuot V U = 2 := by
    rw [hXcard] at hX3
    have h4 : 2 ^ E3.mQuot V U = 2 ^ 2 := by omega
    exact Nat.pow_right_injective (le_refl 2) h4
  have hfin : ∀ k : Fin 2, k = 0 ∨ k = 1 := fun k => by fin_cases k <;> simp
  obtain ⟨j₀, hj₀, hj₀all⟩ : ∃ j₀ : Fin 2, j₀ ≠ i₀ ∧ ∀ k : Fin 2, k = i₀ ∨ k = j₀ := by
    rcases hfin i₀ with h0 | h1
    · refine ⟨1, by rw [h0]; decide, fun k => ?_⟩
      rcases hfin k with hk | hk
      · exact Or.inl (hk.trans h0.symm)
      · exact Or.inr hk
    · refine ⟨0, by rw [h1]; decide, fun k => ?_⟩
      rcases hfin k with hk | hk
      · exact Or.inr hk
      · exact Or.inl (hk.trans h1.symm)
  have hVdisj : Vs i₀ ⊓ Vs j₀ = ⊥ := disjoint_iff.1 (hVind.pairwiseDisjoint (Ne.symm hj₀))
  have hVsup2 : Vs i₀ ⊔ Vs j₀ = ⊤ := by
    rw [← hVtop, ← hVsup]
    refine le_antisymm (sup_le (le_iSup Vs i₀) (le_iSup Vs j₀)) (iSup_le fun k => ?_)
    rcases hj₀all k with hk | hk
    · rw [hk]
      exact le_sup_left
    · rw [hk]
      exact le_sup_right
  have hcardW : Nat.card (IntMod V hV) = 64 := by
    have h1 := card_sup_mul_card_inf (Vs i₀) (Vs j₀)
    rw [hVsup2, hVdisj, Subgroup.card_bot, mul_one, Subgroup.card_top, h8 i₀, h8 j₀] at h1
    exact h1
  have hcardV : Nat.card V = 64 := hcardW
  have hVne : ∀ k, Vs k ≠ ⊥ := fun k h0 => by
    have h1 := h8 k
    rw [h0, Subgroup.card_bot] at h1
    omega
  have hYne : Y i₀ ≠ ⊥ := fun h0 => by
    rw [h0, Subgroup.card_bot] at h21
    omega
  have hstab : ∀ y ∈ Y i₀, ∀ v ∈ Vs j₀, y v ∈ Vs j₀ := by
    intro y hy v hv
    have hYj : (Y j₀).map (MulAut.conj y).toMonoidHom = Y j₀ := by
      ext z
      constructor
      · rintro ⟨z', hz', rfl⟩
        have hc := hYcomm i₀ j₀ (Ne.symm hj₀) y hy z' hz'
        show y * z' * y⁻¹ ∈ Y j₀
        rw [hc, mul_inv_cancel_right]
        exact hz'
      · intro hz
        refine ⟨z, hz, ?_⟩
        have hc := hYcomm i₀ j₀ (Ne.symm hj₀) y hy z hz
        show y * z * y⁻¹ = z
        rw [hc, mul_inv_cancel_right]
    have h1 := Asc81c.commSub_map_conj (Y j₀) y
    rw [hYj, (hVi j₀).1] at h1
    have h2 : y v ∈ (Vs j₀).map y.toMonoidHom := ⟨v, hv, rfl⟩
    rw [← h1] at h2
    exact h2
  have hfixj : ∀ y ∈ Y i₀, ∀ v ∈ Vs j₀, y v = v := by
    intro y hy v hv
    have h1 : y v * v⁻¹ ∈ Vs i₀ := by
      rw [← (hVi i₀).1]
      exact Subgroup.subset_closure ⟨y, hy, v, Subgroup.mem_top v, rfl⟩
    have h2 : y v * v⁻¹ ∈ Vs j₀ := (Vs j₀).mul_mem (hstab y hy v hv) ((Vs j₀).inv_mem hv)
    have h3 : y v * v⁻¹ ∈ Vs i₀ ⊓ Vs j₀ := ⟨h1, h2⟩
    rw [hVdisj, Subgroup.mem_bot, mul_inv_eq_one] at h3
    exact h3
  have hodd21 : Odd (Nat.card (Y i₀)) := by
    rw [h21]
    decide
  have hfixY : fixV (Y i₀) = Vs j₀ := by
    symm
    apply Subgroup.eq_of_le_of_card_ge
      (show Vs j₀ ≤ fixV (Y i₀) from fun v hv y hy => hfixj y hy v hv)
    have h1 := Asc81c.card_fixV_mul_card_commSub hW hodd21
    rw [(hVi i₀).1, h8 i₀, hcardW] at h1
    rw [h8 j₀]
    omega
  set V₂ := (Vs j₀).map (E3.valHom hV) with hV₂def
  have hV₂V : V₂ ≤ V := E3.map_valHom_le hV _
  have hcardV₂ : Nat.card V₂ = 8 := by
    rw [hV₂def, Subgroup.card_map_of_injective (E3.valHom_injective hV), h8 j₀]
  have hV₂1 : V₂ ≠ ⊥ := fun h0 => by
    rw [h0, Subgroup.card_bot] at hcardV₂
    omega
  have hjfix : Vs j₀ ≤ fixV (autI hV X) := fun v hv x hx => hfixj x (hXY₀ hx) v hv
  have hV₂U : V₂ ≤ U := by
    rw [← hfixmap]
    exact Subgroup.map_mono hjfix
  have hcardU : Nat.card U = 16 := by
    have h1 := E3.card_eq_two_pow_mul hV2 hU.1
    rw [hn2, hcardV] at h1
    omega
  have hidx : V₂.relIndex U = 2 := by
    have h1 := Subgroup.relIndex_mul_card V₂ U
    rw [inf_eq_left.2 hV₂U, hcardV₂, hcardU] at h1
    omega
  have hV₂Γ : V₂ ∈ gammaE64 V M := by
    refine ⟨hV₂V, hV₂1, fun hle => hU.2.2.1 ((Subgroup.centralizer_le hV₂U).trans hle), ?_⟩
    set K := M ⊓ Subgroup.centralizer (V₂ : Set G) with hKdef
    have hKN : K ≤ Subgroup.normalizer (V : Set G) := inf_centralizer_le_normalizer h hV₂V hV₂1
    obtain ⟨S, hS⟩ := E1.exists_isSylowIn_two K
    have hSC : S ≤ Subgroup.centralizer (V : Set G) := by
      by_contra hSC
      have hSN : S ≤ Subgroup.normalizer (V : Set G) := hS.1.trans hKN
      have hA1 : autI hV S ≠ ⊥ := (autI_eq_bot_iff hV hSN).not.2 hSC
      have hA2 : IsPGroup 2 (autI hV S) := B6.isPGroup_autOn hS.2.1 V
      obtain ⟨t, htS, ht2⟩ := E3.exists_orderOf_two_of_isPGroup hA2 hA1
      have htM : t ∈ autI hV M := autI_mono hV (hS.1.trans inf_le_left) htS
      have htj : ∀ v ∈ Vs j₀, t v = v := by
        intro v hv
        obtain ⟨g, hgS, rfl⟩ := (mem_autI hV).1 htS
        apply IntMod.val_injective
        rw [convI_apply_val]
        have hgC : (g : G) ∈ Subgroup.centralizer (V₂ : Set G) := (hS.1 hgS).2
        have hvV₂ : v.val ∈ V₂ := ⟨v, hv, rfl⟩
        rw [← Subgroup.mem_centralizer_iff.1 hgC v.val hvV₂, mul_inv_cancel_right]
      have hmapj : (Vs j₀).map t.toMonoidHom = Vs j₀ := by
        ext v
        constructor
        · rintro ⟨w, hw, rfl⟩
          show t w ∈ Vs j₀
          rw [htj w hw]
          exact hw
        · intro hv
          exact ⟨v, hv, htj v hv⟩
      obtain ⟨j, hj⟩ := hperm t htM j₀
      have hj' : j = j₀ := by
        rcases hj₀all j with hji | hjj
        · exfalso
          have h1 := Asc81c.commSub_map_conj (Y j₀) t
          rw [hj, (hVi j).1, (hVi j₀).1, hmapj, hji] at h1
          apply hVne j₀
          rw [← hVdisj, h1, inf_idem]
        · exact hjj
      rw [hj'] at hj
      obtain ⟨k, hk⟩ := hperm t htM i₀
      have hk' : k = i₀ := by
        rcases hj₀all k with hki | hkj
        · exact hki
        · exfalso
          rw [hkj, ← hj] at hk
          have h2 := Subgroup.map_injective (MulAut.conj t).injective hk
          have hdisj : Disjoint (Y i₀) (Y j₀) := hYind.pairwiseDisjoint (Ne.symm hj₀)
          rw [h2, disjoint_self] at hdisj
          exact hYne (h2.trans hdisj)
      rw [hk'] at hk
      have hti : ∀ v ∈ Vs i₀, t v ∈ Vs i₀ := by
        intro v hv
        have h1 := Asc81c.commSub_map_conj (Y i₀) t
        rw [hk, (hVi i₀).1] at h1
        have h2 : t v ∈ (Vs i₀).map t.toMonoidHom := ⟨v, hv, rfl⟩
        rw [← h1] at h2
        exact h2
      obtain ⟨a, haV, ha1, hta⟩ : ∃ a ∈ Vs i₀, a ≠ 1 ∧ t a = a := by
        obtain ⟨⟨a₀, ha₀⟩, ha₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hVne i₀)
        have ha₀1' : a₀ ≠ 1 := fun h0 => ha₀1 (Subtype.ext h0)
        by_cases hfix : t a₀ = a₀
        · exact ⟨a₀, ha₀, ha₀1', hfix⟩
        · refine ⟨t a₀ * a₀⁻¹, (Vs i₀).mul_mem (hti a₀ ha₀) ((Vs i₀).inv_mem ha₀),
            fun h0 => hfix (mul_inv_eq_one.1 h0), ?_⟩
          have htt : t (t a₀) = a₀ := by
            have h1 := pow_orderOf_eq_one t
            rw [ht2, pow_two] at h1
            rw [← MulAut.mul_apply, h1, MulAut.one_apply]
          have hsq : ∀ w : IntMod V hV, w⁻¹ = w := fun w => by
            have h1 := hW w
            rw [pow_two] at h1
            exact inv_eq_of_mul_eq_one_right h1
          rw [map_mul, map_inv, htt, hsq, hsq, mul_comm]
      have ha2 : Nat.card (Subgroup.zpowers a) = 2 := by
        rw [Nat.card_zpowers]
        exact orderOf_eq_prime (hW a) ha1
      have hinfa : Vs j₀ ⊓ Subgroup.zpowers a = ⊥ := by
        have hdvd : Nat.card ↥(Vs j₀ ⊓ Subgroup.zpowers a) ∣ 2 :=
          ha2 ▸ Subgroup.card_dvd_of_le inf_le_right
        rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
        · exact Subgroup.eq_bot_of_card_eq _ h1
        · exfalso
          have heq : Vs j₀ ⊓ Subgroup.zpowers a = Subgroup.zpowers a :=
            Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h2, ha2])
          have haj : a ∈ Vs j₀ := (heq ▸ Subgroup.mem_zpowers a : a ∈ Vs j₀ ⊓ _).1
          have h3 : a ∈ Vs i₀ ⊓ Vs j₀ := ⟨haV, haj⟩
          rw [hVdisj, Subgroup.mem_bot] at h3
          exact ha1 h3
      have hfixt : Vs j₀ ⊔ Subgroup.zpowers a ≤ fixV (Subgroup.zpowers t) := by
        refine sup_le (fun v hv => mem_fixV_zpowers_of_apply_eq (htj v hv)) ?_
        rw [Subgroup.zpowers_le]
        exact mem_fixV_zpowers_of_apply_eq hta
      have hcardfix : 16 ≤ Nat.card (fixV (Subgroup.zpowers t)) := by
        have h1 := card_sup_mul_card_inf (Vs j₀) (Subgroup.zpowers a)
        rw [hinfa, Subgroup.card_bot, mul_one, h8 j₀, ha2] at h1
        have h2 := Subgroup.card_le_of_le hfixt
        omega
      have hrk : rkIdx (fixV (Subgroup.zpowers t)) ≤ 2 := by
        have h1 := B1.index_eq_two_pow hW (fixV (Subgroup.zpowers t))
        have h2 := (fixV (Subgroup.zpowers t)).index_mul_card
        rw [hcardW] at h2
        have h3 : (fixV (Subgroup.zpowers t)).index ≤ 4 := by
          by_contra h4
          push Not at h4
          nlinarith
        rw [h1] at h3
        by_contra h5
        push Not at h5
        have : 2 ^ 3 ≤ 2 ^ rkIdx (fixV (Subgroup.zpowers t)) :=
          Nat.pow_le_pow_right (by norm_num) h5
        omega
      have ht1 : t ≠ 1 := fun h0 => by
        rw [h0, orderOf_one] at ht2
        omega
      have hle := E3.mParam_le_rkIdx_fixV (Subgroup.zpowers_le.2 htM)
        (hA2.to_le (Subgroup.zpowers_le.2 htS)) (Subgroup.zpowers_ne_bot.2 ht1)
      omega
    refine (iInf₂_le (K ⊓ Subgroup.centralizer (V : Set G))
      ⟨inf_le_left, B2F.le_normalizer_inf Subgroup.le_normalizer
        (B2F.le_normalizer_centralizer hKN), fun h2 => ?_⟩).trans (inf_le_inf_right _ inf_le_left)
    exact hS.2.2 (h2.trans (Subgroup.relIndex_dvd_of_le_left K (le_inf hS.1 hSC)))
  have hXodd : Odd (Nat.card (autI hV X)) := by
    rw [hX3]
    decide
  have hjX : Vs j₀ ⊓ commSub ⊤ (autI hV X) = ⊥ := by
    have h1 := Asc81c.fixV_inf_commSub_eq_bot' hW hXodd
    rw [eq_bot_iff] at h1 ⊢
    exact (inf_le_inf_right _ hjfix).trans h1
  have hcommX := map_valHom_commSub_eq hV hXN
  set W'' := Vs j₀ ⊔ commSub ⊤ (autI hV X) with hW''def
  have hcardW'' : Nat.card W'' = 32 := by
    have h1 := card_sup_mul_card_inf (Vs j₀) (commSub ⊤ (autI hV X))
    rw [hjX, Subgroup.card_bot, mul_one, h8 j₀, hcardc, hn2] at h1
    norm_num at h1
    exact h1
  set W' := W''.map (E3.valHom hV) with hW'def
  have hW'eq : W' = V₂ ⊔ ⁅V, X⁆ := by
    rw [hW'def, hW''def, Subgroup.map_sup, hcommX]
  have hW'V : W' ≤ V := E3.map_valHom_le hV _
  have hcardW' : Nat.card W' = 32 := by
    rw [hW'def, Subgroup.card_map_of_injective (E3.valHom_injective hV), hcardW'']
  have hW'1 : E3.mQuot V W' = 1 := by
    have h1 := E3.card_eq_two_pow_mul hV2 hW'V
    rw [hcardV, hcardW'] at h1
    have h2 : 2 ^ E3.mQuot V W' = 2 := by omega
    exact Nat.pow_right_injective (le_refl 2) (h2.trans (pow_one 2).symm)
  have hW'M : Subgroup.centralizer (W' : Set G) ≤ M := by
    by_contra hWM
    have hWN : ¬ Subgroup.centralizer (W' : Set G) ≤ Subgroup.normalizer (V : Set G) :=
      fun hle => hWM (hle.trans h.normalizer_le)
    have h1 := rParam_le_mQuot hW'V hWN
    rw [← hr, hn2, hW'1] at h1
    exact absurd (Nat.cast_le.1 h1) (by norm_num)
  have hOU : oddCoreIn (Subgroup.centralizer (U : Set G)) = ⊥ :=
    h621 G T M V U hV h (Or.inr hm) hU.1 hU.2.1
  obtain ⟨-, hVNL, -, -⟩ := e68_setting hlist h hU hOU hLc
  have hVXL : ⁅V, X⁆ ≤ L := by
    rw [Subgroup.commutator_le]
    intro v hv x hx
    rw [commutatorElement_def]
    have hxL : x ∈ L := (hXLM hx).1
    exact L.mul_mem ((Subgroup.mem_normalizer_iff.1 (hVNL hv) x).1 hxL) (L.inv_mem hxL)
  obtain ⟨u, huU, huV₂⟩ : ∃ u ∈ U, u ∉ V₂ := by
    by_contra hall
    push Not at hall
    have h1 := Subgroup.card_le_of_le (show U ≤ V₂ from hall)
    omega
  have hCU := centralizer_eq_inf_of_relIndex_two hV₂U hidx huU huV₂
  set H₂ := Subgroup.centralizer (V₂ : Set G) with hH₂def
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  have hO₂ : oddCoreIn H₂ = ⊥ := h621 G T M V V₂ hV h (Or.inr hm) hV₂V hV₂1
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm h.isElemAbelian ha hb
  have huV : u ∈ V := hU.1 huU
  have huH₂ : u ∈ H₂ := Subgroup.mem_centralizer_iff.2 fun w hw => hVc _ (hV₂V hw) _ huV
  have hu1 : u ≠ 1 := fun h1 => huV₂ (h1 ▸ V₂.one_mem)
  have hu2 : u ^ 2 = 1 := h.isElemAbelian.2 u huV
  have hq : QTKECore G := qtkeCore_of_cat h.nonabelian h.qtke
  have hpc : pCoreOf 2 H₂ ≠ ⊥ := by
    intro h0
    apply hV₂1
    refine le_bot_iff.1 (h0 ▸ C1.le_pCoreOf_of_normalized ?_ (Subgroup.centralizer_le_normalizer _)
      (hV2.to_le hV₂V))
    exact fun w hw => Subgroup.mem_centralizer_iff.2 fun w' hw' => hVc _ (hV₂V hw') _ (hV₂V hw)
  have hKG : CFSG.SectionRank.IsKGroupCat ↥H₂ := (hq.1 H₂ hpc).2
  have hLq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hLc
  have hL2 : Id2519.IsTwoComponentIn L (H₂ ⊓ Subgroup.centralizer ({u} : Set G)) := by
    rw [← hCU]
    exact Id2519.isTwoComponentIn_of_isComponentIn hLc (two_dvd_card_of_isQuasisimple hLq)
  have hQH₂ : IsSylowTwoOf Q H₂ := e6_5_one h hV₂Γ
  have hVQ : V ≤ Q := h.le_inf_centralizer
  have hQV : Q ≤ Subgroup.centralizer (V : Set G) := inf_le_right
  have hcore : CFSG.pPrimeCore 2 ↥H₂ = ⊥ := pPrimeCore_eq_bot_of_oddCoreIn' hO₂
  have hQ2' : IsPGroup 2 (Q.subgroupOf H₂) :=
    hQH₂.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hQH₂.1).symm
  set P : Sylow 2 ↥H₂ := hQ2'.toSylow hQH₂.2.2 with hPdef
  have hnormJ : ∀ J : Subgroup G, IsComponentIn J H₂ → u ∈ Subgroup.normalizer (J : Set G) := by
    intro J hJ
    have hvz : (⟨u, huH₂⟩ : ↥H₂) ∈ Subgroup.centralizer ((P : Subgroup ↥H₂) : Set ↥H₂) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hQV (show (y : G) ∈ Q from hy)) u huV).symm
    have hvzS : (⟨u, huH₂⟩ : ↥H₂) ∈ (P : Subgroup ↥H₂) := show u ∈ Q from hVQ huV
    have hnorm' := central_sylow_normalizes_components hcore P hvz hvzS hJ.2
    have h2 : u ∈
        (Subgroup.normalizer ((J.subgroupOf H₂ : Subgroup ↥H₂) : Set ↥H₂)).map H₂.subtype :=
      ⟨_, hnorm', rfl⟩
    rw [map_subtype_normalizer hJ.1] at h2
    exact h2.2
  rcases I32.lemmaI32 G H₂ hKG u huH₂ hu1 hu2 L hL2 with ⟨hKt, -⟩ | ⟨J, hJ, hJne, -, -⟩
  swap
  · exact absurd ((BenderBranch.conjugate_eq_iff_mem_normalizer.2
      (hnormJ J (isComponentIn_of_isTwoComponentIn hJ hO₂))).symm) hJne
  set K := ⨆ g ∈ Id2519.oddLayer H₂, CFSG.conjugate L g with hKdef
  have hKc : IsComponentIn K H₂ := isComponentIn_of_isTwoComponentIn hKt hO₂
  have hLK : L ≤ K := by
    refine le_trans (le_of_eq (BenderBranch.conjugate_one L).symm) ?_
    exact le_iSup₂_of_le 1 (Subgroup.one_mem _) le_rfl
  have hKnorm : ∀ g ∈ M, g ∈ H₂ → g ∈ Subgroup.normalizer (K : Set G) := by
    intro g hgM hgH
    have hgN : g ∈ Subgroup.normalizer (H₂ : Set G) := Subgroup.le_normalizer hgH
    have hKg := isComponentIn_conjugate_of_mem_normalizer' hKc hgN
    rcases BenderBranch.eq_or_commute_of_isComponentIn hKc hKg with he | hc
    · exact BenderBranch.conjugate_eq_iff_mem_normalizer.1 he.symm
    · exfalso
      apply hLM
      have hKgW : CFSG.conjugate K g ≤ Subgroup.centralizer (W' : Set G) := by
        rw [Subgroup.le_centralizer_iff, hW'eq]
        refine sup_le (Subgroup.le_centralizer_iff.1 hKg.1) ?_
        have h1 : CFSG.conjugate K g ≤ Subgroup.centralizer (K : Set G) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.1
            (by rw [Subgroup.commutator_comm]; exact hc)
        exact Subgroup.le_centralizer_iff.1 (h1.trans (Subgroup.centralizer_le (hVXL.trans hLK)))
      intro l hl
      have hl' : g⁻¹ * l * g ∈ CFSG.conjugate K g :=
        BenderBranch.mem_conjugate_iff.2
          (by rw [show g * (g⁻¹ * l * g) * g⁻¹ = l by group]; exact hLK hl)
      have he : l = g * (g⁻¹ * l * g) * g⁻¹ := by group
      rw [he]
      exact M.mul_mem (M.mul_mem hgM (hW'M (hKgW hl'))) (M.inv_mem hgM)
  have hYM : Y i₀ ≤ autI hV M :=
    ((le_iSup Y i₀).trans hYsup.le).trans (e624Y_le hV (hXMU.trans inf_le_left))
  have hCK : V ⊓ Subgroup.centralizer (K : Set G) = V₂ := by
    refine le_antisymm ?_ (le_inf hV₂V (Subgroup.le_centralizer_iff.1 hKc.1))
    rintro v ⟨hvV, hvK⟩
    set w : IntMod V hV := IntMod.mk hV ⟨v, hvV⟩ with hwdef
    have hw : w ∈ fixV (Y i₀) := by
      intro ψ hψ
      rw [hcl] at hψ
      refine Subgroup.closure_induction (p := fun ψ _ => ψ w = w) ?_ ?_ ?_ ?_ hψ
      · rintro _ ⟨φ, hφ, ξ, hξ, rfl⟩
        obtain ⟨g, hgM, rfl⟩ := (mem_autI hV).1 (hYM hφ)
        obtain ⟨x, hxX, rfl⟩ := (mem_autI hV).1 hξ
        have hgH : (g : G) ∈ H₂ := by
          rw [Subgroup.mem_centralizer_iff]
          rintro _ ⟨c, hc, rfl⟩
          have h1 := congrArg IntMod.val (hfixj _ hφ c hc)
          rw [convI_apply_val] at h1
          rw [E3.valHom_apply]
          calc c.val * (g : G) = ((g : G) * c.val * (g : G)⁻¹) * g := by rw [h1]
            _ = (g : G) * c.val := by group
        have hgK := hKnorm g hgM hgH
        have hxK : (x : G) ∈ K := hLK (hXLM hxX).1
        have hgx : (g : G) * x * (g : G)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hgK x).1 hxK
        have hc := Subgroup.mem_centralizer_iff.1 hvK _ hgx
        apply IntMod.val_injective
        rw [← map_inv, ← map_mul, ← map_mul, convI_apply_val]
        show (g : G) * (x : G) * (g : G)⁻¹ * v * ((g : G) * (x : G) * (g : G)⁻¹)⁻¹ = v
        rw [hc, mul_inv_cancel_right]
      · rfl
      · intro a b _ _ ha hb
        rw [MulAut.mul_apply, hb, ha]
      · intro a _ ha
        calc a⁻¹ w = a⁻¹ (a w) := by rw [ha]
          _ = w := MulAut.inv_apply_self _ a w
    rw [hfixY] at hw
    exact ⟨w, hw, rfl⟩
  have hidxK : (V ⊓ Subgroup.centralizer (K : Set G)).relIndex V = 8 := by
    rw [hCK]
    have h1 := Subgroup.relIndex_mul_card V₂ V
    rw [inf_eq_left.2 hV₂V, hcardV₂, hcardV] at h1
    omega
  by_cases huK : u ∈ Subgroup.centralizer (K : Set G)
  ·
    have hKu : K ≤ Subgroup.centralizer ({u} : Set G) := fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 huK y hy)
    have hKCU : K ≤ Subgroup.centralizer (U : Set G) := by
      rw [hCU]
      exact le_inf hKc.1 hKu
    have hKc' : IsComponentIn K (Subgroup.centralizer (U : Set G)) :=
      BenderBranch.isComponentIn_of_le hKc hKCU (Subgroup.centralizer_le hV₂U)
    rcases BenderBranch.eq_or_commute_of_isComponentIn hLc hKc' with heq | hcomm
    · rw [← heq, hCL] at hCK
      rw [← hCK, hcardU] at hcardV₂
      omega
    · have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hLq.1
      have hbot : L = ⊥ := by
        rw [← hperf, eq_bot_iff, ← hcomm]
        exact Subgroup.commutator_mono le_rfl hLK
      have := CFSG.LocalCores.isQuasisimple_nontrivial hLq
      exact (Subgroup.nontrivial_iff_ne_bot L).mp this hbot
  ·
    obtain ⟨-, hVNK, hSK, z, hcases⟩ := e68_setting hlist h hV₂Γ hO₂ hKc
    set R := Q ⊓ Subgroup.normalizer (K : Set G) with hRdef
    have hRK : R ⊓ K = Q ⊓ K := by
      rw [hRdef, inf_assoc, inf_eq_right.2 (Subgroup.le_normalizer : K ≤ _)]
    have hE : E68CentHyp K R u :=
      { quasisimple := BenderBranch.isQuasisimple_of_isComponentIn hKc
        isPGroup := hQH₂.2.1.to_le inf_le_left
        normalizer := inf_le_right
        sylow := by rw [hRK]; exact hSK
        mem := ⟨hVQ huV, hVNK huV⟩
        central := fun r hr => Subgroup.mem_centralizer_iff.1 (hQV hr.1) u huV
        sq := hu2
        not_mem := huK }
    have hLu : L ≤ Subgroup.centralizer ({u} : Set G) := by
      have h1 := hLc.1
      rw [hCU] at h1
      exact h1.trans inf_le_right
    have hKuU : K ⊓ Subgroup.centralizer ({u} : Set G) ≤ Subgroup.centralizer (U : Set G) := by
      rw [hCU]
      exact inf_le_inf_right _ hKc.1
    have hLK' : IsComponentIn L (K ⊓ Subgroup.centralizer ({u} : Set G)) :=
      BenderBranch.isComponentIn_of_le hLc (le_inf hLK hLu) hKuU
    obtain ⟨hD7, -⟩ := hCent G K R L z u hcases hE hLK'
    have hbase : E68BaseHyp K V R :=
      { quasisimple := BenderBranch.isQuasisimple_of_isComponentIn hKc
        elemAbelian := hV
        isPGroup := hQH₂.2.1.to_le inf_le_left
        le := fun v hv => ⟨hVQ hv, hVNK hv⟩
        centralizer := inf_le_left.trans hQV
        normalizer := inf_le_right
        sylow := by rw [hRK]; exact hSK }
    have h4 := (hAlt G K V R z (Or.inr hD7) hbase).1
    omega

end Main

end E6

end CFSG.Quasithin
