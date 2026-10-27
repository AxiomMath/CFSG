module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.E6TwentyFiveB
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique

section Context

variable {G : Type} [Group G] [Finite G]

structure NotTwoCtx (T M V U L X : Subgroup G) (hV : CFSG.Open.IsElemAbelian 2 V)
    (Y : Fin 2 → Subgroup (MulAut (IntMod V hV))) (Vs : Fin 2 → Subgroup (IntMod V hV))
    (i₀ j₀ : Fin 2) (u : G) : Prop where
  ne : i₀ ≠ j₀
  le_Y : autI hV X ≤ Y i₀
  closure_Y : Y i₀ = Subgroup.closure {ψ | ∃ φ ∈ Y i₀, ∃ ξ ∈ autI hV X, ψ = φ * ξ * φ⁻¹}
  card_Y : Nat.card (Y i₀) = 21
  Y_le : Y i₀ ≤ autI hV M
  fix_j : ∀ y ∈ Y i₀, ∀ v ∈ Vs j₀, y v = v
  fixV_Y : fixV (Y i₀) = Vs j₀
  le_U : (Vs j₀).map (E3.valHom hV) ≤ U
  card_V₂ : Nat.card ((Vs j₀).map (E3.valHom hV)) = 8
  card_V : Nat.card V = 64
  card_U : Nat.card U = 16
  gamma : (Vs j₀).map (E3.valHom hV) ∈ gammaE64 V M
  centralizer_le : Subgroup.centralizer
    (((Vs j₀).map (E3.valHom hV) ⊔ ⁅V, X⁆ : Subgroup G) : Set G) ≤ M
  comm_le : ⁅V, X⁆ ≤ L
  mem_U : u ∈ U
  not_mem : u ∉ (Vs j₀).map (E3.valHom hV)
  centralizer_U : Subgroup.centralizer (U : Set G) =
    Subgroup.centralizer (((Vs j₀).map (E3.valHom hV) : Subgroup G) : Set G) ⊓
      Subgroup.centralizer ({u} : Set G)
  oddCore : oddCoreIn (Subgroup.centralizer (((Vs j₀).map (E3.valHom hV) : Subgroup G) : Set G)) = ⊥
  sylow : IsSylowTwoOf (T ⊓ Subgroup.centralizer (V : Set G))
    (Subgroup.centralizer (((Vs j₀).map (E3.valHom hV) : Subgroup G) : Set G))

theorem exists_notTwoCtx (h621 : E621Stmt) {T M V U L X : Subgroup G}
    {hV : CFSG.Open.IsElemAbelian 2 V} (hset : E625Setting T M V U hV) (hD : E611Data hV M U L X)
    {Y : Fin 2 → Subgroup (MulAut (IntMod V hV))} {Vs : Fin 2 → Subgroup (IntMod V hV)}
    (hB : E624Body hV M X 2 Y Vs) (hX3 : Nat.card (autI hV X) = 3) (hXY : ∀ i, autI hV X ≠ Y i) :
    ∃ (i₀ j₀ : Fin 2) (u : G), NotTwoCtx T M V U L X hV Y Vs i₀ j₀ u := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD' := hD
  obtain ⟨hLU, -, hLM, hCL, hXLM, hXcyc, hXcard, hUX1, hUX2, hreg, hnorm, hNL, -, -⟩ := hD'
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
  · exact (hXY i hi).elim
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
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm h.isElemAbelian ha hb
  have hVNL : V ≤ Subgroup.normalizer (L : Set G) := fun v hv =>
    hNL v ⟨h.inM.2 (h.le hv), Subgroup.le_normalizer hv⟩
      (Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.2 fun w hw => hVc _ (hU.1 hw) _ hv))
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
  have hO₂ : oddCoreIn (Subgroup.centralizer (V₂ : Set G)) = ⊥ :=
    h621 G T M V V₂ hV h (Or.inr hm) hV₂V hV₂1
  have hYM : Y i₀ ≤ autI hV M :=
    ((le_iSup Y i₀).trans hYsup.le).trans (e624Y_le hV (hXMU.trans inf_le_left))
  have hW'M' : Subgroup.centralizer ((V₂ ⊔ ⁅V, X⁆ : Subgroup G) : Set G) ≤ M := by
    rw [← hW'eq]
    exact hW'M
  exact ⟨i₀, j₀, u, ⟨hj₀.symm, hXY₀, hcl, h21, hYM, hfixj, hfixY, hV₂U, hcardV₂, hcardV, hcardU,
    hV₂Γ, hW'M', hVXL, huU, huV₂, hCU, hO₂, e6_5_one h hV₂Γ⟩⟩

end Context

section Block

variable {G : Type} [Group G] [Finite G] {T M V U L X : Subgroup G}
  {hV : CFSG.Open.IsElemAbelian 2 V} {Y : Fin 2 → Subgroup (MulAut (IntMod V hV))}
  {Vs : Fin 2 → Subgroup (IntMod V hV)} {i₀ j₀ : Fin 2} {u : G}

omit [Finite G] in
theorem mem_normalizer_of_ctx (hc : NotTwoCtx T M V U L X hV Y Vs i₀ j₀ u) (hLM : ¬ L ≤ M)
    {K : Subgroup G} (hLK : L ≤ K)
    (hKH : K ≤ Subgroup.centralizer (((Vs j₀).map (E3.valHom hV) : Subgroup G) : Set G))
    {g : G} (hgM : g ∈ M)
    (hgH : g ∈ Subgroup.centralizer (((Vs j₀).map (E3.valHom hV) : Subgroup G) : Set G))
    (hK : CFSG.conjugate K g = K ∨ ⁅CFSG.conjugate K g, K⁆ = ⊥) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  rcases hK with he | hcomm
  · exact BenderBranch.conjugate_eq_iff_mem_normalizer.1 he
  · exfalso
    apply hLM
    have hKgH : CFSG.conjugate K g ≤
        Subgroup.centralizer (((Vs j₀).map (E3.valHom hV) : Subgroup G) : Set G) := by
      intro x hx
      have h1 : g * x * g⁻¹ ∈ K := BenderBranch.mem_conjugate_iff.1 hx
      have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hgH) (hKH h1)) hgH
    have hKgW : CFSG.conjugate K g ≤ Subgroup.centralizer
        (((Vs j₀).map (E3.valHom hV) ⊔ ⁅V, X⁆ : Subgroup G) : Set G) := by
      rw [Subgroup.le_centralizer_iff]
      refine sup_le (Subgroup.le_centralizer_iff.1 hKgH) ?_
      have h1 : CFSG.conjugate K g ≤ Subgroup.centralizer (K : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
      exact Subgroup.le_centralizer_iff.1
        (h1.trans (Subgroup.centralizer_le (hc.comm_le.trans hLK)))
    intro l hl
    have hl' : g⁻¹ * l * g ∈ CFSG.conjugate K g :=
      BenderBranch.mem_conjugate_iff.2
        (by rw [show g * (g⁻¹ * l * g) * g⁻¹ = l by group]; exact hLK hl)
    have he : l = g * (g⁻¹ * l * g) * g⁻¹ := by group
    rw [he]
    exact M.mul_mem (M.mul_mem hgM (hc.centralizer_le (hKgW hl'))) (M.inv_mem hgM)

omit [Finite G] in
theorem mem_centralizer_of_ctx (hc : NotTwoCtx T M V U L X hV Y Vs i₀ j₀ u)
    {g : Subgroup.normalizer (V : Set G)} (hg : convI hV g ∈ Y i₀) :
    (g : G) ∈ Subgroup.centralizer (((Vs j₀).map (E3.valHom hV) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨c, hc', rfl⟩
  have h1 := congrArg IntMod.val (hc.fix_j _ hg c hc')
  rw [convI_apply_val] at h1
  rw [E3.valHom_apply]
  calc c.val * (g : G) = ((g : G) * c.val * (g : G)⁻¹) * g := by rw [h1]
    _ = (g : G) * c.val := by group

omit [Finite G] in
theorem inf_centralizer_le_of_ctx (hc : NotTwoCtx T M V U L X hV Y Vs i₀ j₀ u) {K : Subgroup G}
    (hXK : X ≤ K)
    (hN : ∀ g ∈ M, g ∈ Subgroup.centralizer (((Vs j₀).map (E3.valHom hV) : Subgroup G) : Set G) →
      g ∈ Subgroup.normalizer (K : Set G)) :
    V ⊓ Subgroup.centralizer (K : Set G) ≤ (Vs j₀).map (E3.valHom hV) := by
  rintro v ⟨hvV, hvK⟩
  set w : IntMod V hV := IntMod.mk hV ⟨v, hvV⟩ with hwdef
  have hw : w ∈ fixV (Y i₀) := by
    intro ψ hψ
    rw [hc.closure_Y] at hψ
    refine Subgroup.closure_induction (p := fun ψ _ => ψ w = w) ?_ ?_ ?_ ?_ hψ
    · rintro _ ⟨φ, hφ, ξ, hξ, rfl⟩
      obtain ⟨g, hgM, rfl⟩ := (mem_autI hV).1 (hc.Y_le hφ)
      obtain ⟨x, hxX, rfl⟩ := (mem_autI hV).1 hξ
      have hgK := hN g hgM (mem_centralizer_of_ctx hc hφ)
      have hgx : (g : G) * x * (g : G)⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.1 hgK x).1 (hXK hxX)
      have hcomm := Subgroup.mem_centralizer_iff.1 hvK _ hgx
      apply IntMod.val_injective
      rw [← map_inv, ← map_mul, ← map_mul, convI_apply_val]
      show (g : G) * (x : G) * (g : G)⁻¹ * v * ((g : G) * (x : G) * (g : G)⁻¹)⁻¹ = v
      rw [hcomm, mul_inv_cancel_right]
    · rfl
    · intro a b _ _ ha hb
      rw [MulAut.mul_apply, hb, ha]
    · intro a _ ha
      calc a⁻¹ w = a⁻¹ (a w) := by rw [ha]
        _ = w := MulAut.inv_apply_self _ a w
  rw [hc.fixV_Y] at hw
  exact ⟨w, hw, rfl⟩

omit [Finite G] in
theorem le_autI_of_ctx (hc : NotTwoCtx T M V U L X hV Y Vs i₀ j₀ u) {K : Subgroup G}
    (hXK : X ≤ K) (hXM : X ≤ M)
    (hN : ∀ g ∈ M, g ∈ Subgroup.centralizer (((Vs j₀).map (E3.valHom hV) : Subgroup G) : Set G) →
      g ∈ Subgroup.normalizer (K : Set G)) :
    Y i₀ ≤ autI hV (K ⊓ M) := by
  rw [hc.closure_Y, Subgroup.closure_le]
  rintro _ ⟨φ, hφ, ξ, hξ, rfl⟩
  obtain ⟨g, hgM, rfl⟩ := (mem_autI hV).1 (hc.Y_le hφ)
  obtain ⟨x, hxX, rfl⟩ := (mem_autI hV).1 hξ
  have hgK := hN g hgM (mem_centralizer_of_ctx hc hφ)
  refine (mem_autI hV).2 ⟨g * x * g⁻¹, ⟨(Subgroup.mem_normalizer_iff.1 hgK x).1 (hXK hxX),
    M.mul_mem (M.mul_mem hgM (hXM hxX)) (M.inv_mem hgM)⟩, ?_⟩
  rw [map_mul, map_mul, map_inv]

theorem card_ne_three_of_isQuasisimple {L : Subgroup G} (hq : CFSG.IsQuasisimple ↥L) :
    ¬ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3 := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsPerfect ↥L := hq.1
  have : Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (CFSG.pCore 2 ↥L))
      (QuotientGroup.mk'_surjective _)
  have : Nontrivial (↥L ⧸ CFSG.pCore 2 ↥L) :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [h3]; norm_num)
  have hcyc : IsCyclic (↥L ⧸ CFSG.pCore 2 ↥L) := isCyclic_of_prime_card h3
  have : Group.IsSolvable (↥L ⧸ CFSG.pCore 2 ↥L) :=
    Group.isSolvable_of_comm fun a b => hcyc.commGroup.mul_comm a b
  exact Group.IsPerfect.not_isSolvable _ this

@[expose] def E625NotTwoBlockNQ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U L X : Subgroup G) (hV : CFSG.Open.IsElemAbelian 2 V),
    E625Setting T M V U hV → E611Data hV M U L X → IsBlock2 (Subgroup.centralizer (U : Set G)) L →
    ∀ (Y : Fin 2 → Subgroup (MulAut (IntMod V hV))) (Vs : Fin 2 → Subgroup (IntMod V hV)),
      E624Body hV M X 2 Y Vs → Nat.card (autI hV X) = 3 → (∀ i, autI hV X ≠ Y i) →
      ∀ i₀ j₀ : Fin 2, i₀ ≠ j₀ → autI hV X ≤ Y i₀ →
      ∀ L₂ ∈ cComp (Subgroup.centralizer (((Vs j₀).map (E3.valHom hV) : Subgroup G) : Set G)),
        L ≤ L₂ → ¬ CFSG.IsQuasisimple ↥L₂ → L₂ = L

end Block

theorem e625NotTwoBlock_of (h68 : E68Stmt) (hNQ : E625NotTwoBlockNQ) (h621 : E621Stmt)
    (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) : E625NotTwoBlock := by
  intro G _ _ T M V U L X hV hset hD hLb Y Vs hB hX3 hXY
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨i₀, j₀, u, hc⟩ := exists_notTwoCtx h621 hset hD hB hX3 hXY
  have hset' := hset
  obtain ⟨h, hm, hU, -, -, -⟩ := hset'
  have hD' := hD
  obtain ⟨hLU, -, hLM, hCL, hXLM, -, hXcard, -, -, -, -, -, -, htype⟩ := hD'
  set V₂ := (Vs j₀).map (E3.valHom hV) with hV₂def
  set H₂ := Subgroup.centralizer (V₂ : Set G) with hH₂def
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  have hn2 : E3.mQuot V U = 2 := by
    rw [hXcard] at hX3
    have h4 : 2 ^ E3.mQuot V U = 2 ^ 2 := by omega
    exact Nat.pow_right_injective (le_refl 2) h4
  have hV₂V : V₂ ≤ V := E3.map_valHom_le hV _
  have hXL : X ≤ L := hXLM.trans inf_le_left
  have hXM : X ≤ M := hXLM.trans inf_le_right
  have h3 : ¬ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3 := by
    rcases htype with ⟨⟨-, hLin⟩ | ⟨hLc, -⟩, -⟩ | ⟨hLc, -⟩
    · exact L238.card_ne_three_of_isLin2Type (by omega) hLin
    · exact card_ne_three_of_isQuasisimple (BenderBranch.isQuasisimple_of_isComponentIn hLc)
    · exact card_ne_three_of_isQuasisimple (BenderBranch.isQuasisimple_of_isComponentIn hLc)
  have hqL : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := hLb.1.2.2.2.1.resolve_right h3
  have hLcU : L ∈ cComp (Subgroup.centralizer (U : Set G)) := L238.mem_cComp_of_isBlock2 hLb h3
  have hQU : Q ≤ Subgroup.centralizer (U : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le hU.1)
  have hLfam : L ∈ lFamily Q := cComp_subset_lFamily hQU hLcU
  have hLH₂ : L ≤ H₂ := hLU.trans (Subgroup.centralizer_le hc.le_U)
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm h.isElemAbelian ha hb
  have hpc : pCoreOf 2 H₂ ≠ ⊥ := by
    have hV₂1 : V₂ ≠ ⊥ := hc.gamma.2.1
    intro h0
    apply hV₂1
    refine le_bot_iff.1 (h0 ▸ C1.le_pCoreOf_of_normalized ?_ (Subgroup.centralizer_le_normalizer _)
      (h.isPGroup_V.to_le hV₂V))
    exact fun w hw => Subgroup.mem_centralizer_iff.2 fun w' hw' => hVc _ (hV₂V hw') _ (hV₂V hw)
  have := h.simple
  have hK : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  obtain ⟨L₂, hL₂, hLL₂⟩ := Vol2Native.lemma_1_2_4_exists hK h37 h39 hpc hc.sylow hLH₂ hLfam
  have hL₂H : L₂ ≤ H₂ := le_of_mem_cComp hL₂
  have hcardV₂U : Nat.card V₂ < Nat.card U := by rw [hc.card_V₂, hc.card_U]; norm_num
  by_cases hq : CFSG.IsQuasisimple ↥L₂
  ·
    have hL₂c : IsComponentIn L₂ H₂ := Id2519.isComponentIn_of_mem_cComp hL₂ hq
    have hN : ∀ g ∈ M, g ∈ H₂ → g ∈ Subgroup.normalizer (L₂ : Set G) := fun g hgM hgH => by
      refine mem_normalizer_of_ctx hc hLM hLL₂ hL₂H hgM hgH ?_
      have hgN : g ∈ Subgroup.normalizer (H₂ : Set G) := Subgroup.le_normalizer hgH
      rcases BenderBranch.eq_or_commute_of_isComponentIn hL₂c
        (isComponentIn_conjugate_of_mem_normalizer' hL₂c hgN) with he | hcomm
      · exact Or.inl he.symm
      · exact Or.inr (by rw [Subgroup.commutator_comm]; exact hcomm)
    have hCV : V ⊓ Subgroup.centralizer (L₂ : Set G) = V₂ :=
      le_antisymm (inf_centralizer_le_of_ctx hc (hXL.trans hLL₂) hN)
        (le_inf hV₂V (Subgroup.le_centralizer_iff.1 hL₂H))
    have hYle := le_autI_of_ctx hc (hXL.trans hLL₂) hXM hN
    have h21 : 21 ∣ Nat.card (autI hV (L₂ ⊓ M)) := hc.card_Y ▸ Subgroup.card_dvd_of_le hYle
    have hm3 : E3.mQuot V (V ⊓ Subgroup.centralizer (L₂ : Set G)) = 3 := by
      rw [hCV]
      have h1 := E3.card_eq_two_pow_mul h.isPGroup_V hV₂V
      rw [hc.card_V, hc.card_V₂] at h1
      have h2 : 2 ^ E3.mQuot V V₂ = 2 ^ 3 := by omega
      exact Nat.pow_right_injective (le_refl 2) h2
    obtain ⟨-, hcases⟩ := h68 G T M V V₂ L₂ hV h hc.gamma hL₂c
    rcases hcases with ⟨n, -, -, -, -, hcard, hmn, -, -⟩ | ⟨n, -, -, -, -, hab⟩ |
      ⟨-, -, -, hm1, -⟩ | ⟨-, -, -, hm2⟩ | ⟨-, -, hm1, -⟩
    · rw [hm3] at hmn
      subst hmn
      rw [hcard] at h21
      norm_num at h21
    · rcases hab with ⟨-, (⟨hm2n, -⟩ | ⟨-, hm1⟩)⟩ | ⟨-, -, -, hmn, hcyc⟩
      · omega
      · omega
      · rw [hm3] at hmn
        subst hmn
        obtain ⟨-, hcard⟩ := hcyc (by norm_num)
        rw [hcard] at h21
        norm_num at h21
    · omega
    · omega
    · omega
  ·
    have hL₂L := hNQ G T M V U L X hV hset hD hLb Y Vs hB hX3 hXY i₀ j₀ hc.ne hc.le_Y L₂ hL₂
      hLL₂ hq
    subst hL₂L
    have hLb₂ : IsBlock2 H₂ L₂ :=
      ⟨hLb.1, hLH₂, A5.C25.subgroupOf_isSubnormal_of_open (subnormal_of_mem_cComp hL₂)⟩
    have hN : ∀ g ∈ M, g ∈ H₂ → g ∈ Subgroup.normalizer (L₂ : Set G) := fun g hgM hgH => by
      refine mem_normalizer_of_ctx hc hLM le_rfl hLH₂ hgM hgH ?_
      by_cases he : CFSG.conjugate L₂ g = L₂
      · exact Or.inl he
      · right
        have hH : H₂.map (MulAut.conj g⁻¹).toMonoidHom = H₂ := by
          have := (BenderBranch.conjugate_eq_iff_mem_normalizer (H := H₂) (g := g)).2
            (Subgroup.le_normalizer hgH)
          exact this
        have hcc : CFSG.conjugate L₂ g ∈ cComp H₂ := by
          have := cComp_map_mulEquiv (MulAut.conj g⁻¹) hL₂
          rwa [hH] at this
        have hb : IsBlock2 H₂ (CFSG.conjugate L₂ g) :=
          ⟨Lin2.IsShort2.map_equiv hLb.1 (MulAut.conj g⁻¹), le_of_mem_cComp hcc,
            A5.C25.subgroupOf_isSubnormal_of_open (subnormal_of_mem_cComp hcc)⟩
        have h1 := C1Pack.commutator_eq_bot_of_quasisimple hLb₂ hqL hb (Ne.symm he)
        rw [Subgroup.commutator_comm]
        exact h1
    have h1 := inf_centralizer_le_of_ctx hc hXL hN
    rw [hCL] at h1
    exact absurd (Subgroup.card_le_of_le h1) (not_le.2 hcardV₂U)

end E6

end CFSG.Quasithin
