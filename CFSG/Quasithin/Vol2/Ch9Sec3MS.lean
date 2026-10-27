module

public import CFSG.Quasithin.Vol2.Ch9Lem934
public import CFSG.Quasithin.Vol2.Ch9Sec3Red

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

variable (S : Setup T L I n)
include S

theorem center_M0_eq_bot (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat) (h2 : n = 2)
    (h1 : zQ T I = fsuV T I) {K D : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hsyl : IsSylowTwoOf (T ⊓ Subgroup.normalizer (L : Set G))
      (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K))
    (hchar : CharTwo (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K)) :
    (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K) ⊓
      Subgroup.centralizer ((L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K : Subgroup G) :
        Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, _, e, ψ, hc, hdiag⟩ := S.exists_isCoord_diag h37c h38c hD
  set T₁ := T ⊓ Subgroup.normalizer (L : Set G) with hT₁
  set M₀ := L ⊔ D ⊔ T₁ ⊔ K with hM₀
  set C := M₀ ⊓ Subgroup.centralizer (M₀ : Set G) with hC
  set V₁ := fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) with hV₁
  have hDM₀ : D ≤ M₀ := le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hT₁M₀ : T₁ ≤ M₀ := le_sup_right.trans le_sup_left
  by_contra hne
  have hCO : C ≤ pCoreOf 2 M₀ := fun x hx =>
    hchar ⟨hx.1, Subgroup.centralizer_le (CFSG.LieType.BorelTits.pCoreOf_le 2 M₀) hx.2⟩
  have hCT₁ : C ≤ T₁ := hCO.trans (F7.isSylowTwoOf_pCoreOf_le hsyl)
  have hC2 : IsPGroup 2 C := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M₀).to_le hCO
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hC2
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero]))
  obtain ⟨⟨w, hwC⟩, hw2⟩ := exists_prime_orderOf_dvd_card' 2
    (show 2 ∣ Nat.card ↥C by rw [hk]; exact dvd_pow_self 2 hk0)
  have hw2' : w ^ 2 = 1 := by
    have h3 := pow_orderOf_eq_one (⟨w, hwC⟩ : ↥C)
    rw [hw2] at h3
    exact congrArg Subtype.val h3
  have hw1 : w ≠ 1 := by
    intro h0
    have h3 : (⟨w, hwC⟩ : ↥C) = 1 := Subtype.ext h0
    rw [h3, orderOf_one] at hw2
    exact absurd hw2 (by norm_num)
  have hQT₁ : T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ T₁ :=
    le_inf inf_le_left (le_sup_right.trans (hc.r0_le_normalizer_L h37 h38 h37c h38c))
  have hTL₀T₁ : T ⊓ fsuL0 T L ≤ T₁ :=
    le_inf inf_le_left (le_sup_left.trans (hc.r0_le_normalizer_L h37 h38 h37c h38c))
  have hwZ : w ∈ omegaOneCenterOf T₁ :=
    Subgroup.subset_closure ⟨⟨hCT₁ hwC, Subgroup.centralizer_le hT₁M₀ hwC.2⟩, hw2'⟩
  have hwV := S.omegaOneCenter_le h1 hQT₁ inf_le_left hwZ
  have hwV₁ : w ∈ V₁ := ⟨hwV.1, Subgroup.centralizer_le hTL₀T₁ hwV.2⟩
  have hK4 : Fintype.card F = 4 := by rw [hc.card, h2]; norm_num
  have : Nontrivial Fˣ := by
    classical
    exact Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_units, hK4]; norm_num)
  obtain ⟨ω, hω⟩ := exists_ne (1 : Fˣ)
  have hω' : (ω : F) ≠ 1 := fun h => hω (Units.ext h)
  obtain ⟨d, hdD, hdL, hψd⟩ := IsCoord.exists_mem_of_diag hdiag ω 1
  have hwd : d * w * d⁻¹ = w := by
    have h3 := Subgroup.mem_centralizer_iff.mp hwC.2 d (hDM₀ hdD)
    rw [h3, mul_inv_cancel_right]
  set c := (Multiplicative.toAdd (e ⟨w, hwV₁.1⟩) : Matrix (Fin 2) (Fin 2) F) 0 0 with hcdef
  have hew : e ⟨w, hwV₁.1⟩ = Multiplicative.ofAdd (c • !![(1 : F), 0; 0, 0]) := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    exact hc.toAdd_e_eq hwV₁
  have h3 : bar e (Subgroup.inclusion S.L0_le_normalizer_V ⟨d, hdL⟩) (e ⟨w, hwV₁.1⟩) =
      e ⟨w, hwV₁.1⟩ := by
    rw [bar_apply]
    congr 1
    exact Subtype.ext hwd
  rw [hc.bar_L0, hψd, hew, rho_diag_smul_e11] at h3
  have h4 := congrArg (fun X : Om4.VM F => (Multiplicative.toAdd X : Matrix (Fin 2) (Fin 2) F) 0 0)
    h3
  simp only [toAdd_ofAdd, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one, mul_one, Units.val_one] at h4
  have hc0 : c = 0 := by
    by_contra hc0
    exact hω' ((mul_eq_right₀ hc0).mp h4)
  apply hw1
  have h5 : e ⟨w, hwV₁.1⟩ = 1 := by rw [hew, hc0, zero_smul]; rfl
  exact congrArg Subtype.val ((map_eq_one_iff e e.injective).mp h5)

theorem isMSPair_M0' (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    {K D K₀ : Subgroup G} (hKM : ¬ K ≤ fsuM T L) (hKns : ¬ Group.IsSolvable ↥K)
    (hM₀O : pCoreOf 2 (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K) ≠ ⊥)
    (hsyl : IsSylowTwoOf (T ⊓ Subgroup.normalizer (L : Set G))
      (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K))
    (hchar : CharTwo (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K))
    (hK₀ : K₀ ∈ cComp (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K))
    (hK₀n : L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K ≤
      Subgroup.normalizer (K₀ : Set G))
    (hM₀eq : L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K =
      K₀ ⊔ (T ⊓ Subgroup.normalizer (L : Set G)))
    (hr : IsRankTwoLie2Derived ((↥K₀ ⧸ CFSG.pCore 2 ↥K₀) ⧸
      Subgroup.center (↥K₀ ⧸ CFSG.pCore 2 ↥K₀))) :
    IsMSPair (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K)
      (T ⊓ Subgroup.normalizer (L : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfsu := S.hyp.fsu
  set T₁ := T ⊓ Subgroup.normalizer (L : Set G) with hT₁
  set M₀ := L ⊔ D ⊔ T₁ ⊔ K with hM₀
  have hLM₀ : L ≤ M₀ := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hKM₀ : K ≤ M₀ := le_sup_right
  have hT₁M₀ : T₁ ≤ M₀ := le_sup_right.trans le_sup_left
  have hT₁2 : IsPGroup 2 T₁ := hfsu.sylow.1.to_le inf_le_left
  refine ⟨⟨sqtkGroup_of_pCoreOf_ne_bot hfsu.qtke hfsu.simple hfsu.nonabelian hM₀O, hchar, K₀, hK₀,
    ?_, hr⟩, Or.inl ⟨T₁, ?_, hsyl.2.2, (F6.pCoreOf_eq_self_of_isPGroup hT₁2).symm⟩, ?_⟩
  · rw [hM₀eq]
    exact Subgroup.coe_mul_of_right_le_normalizer_left K₀ T₁
      (le_sup_right.trans (hM₀eq ▸ hK₀n))
  · refine lt_of_le_of_ne hT₁M₀ fun h => ?_
    have hK2 : IsPGroup 2 K := hT₁2.to_le (h ▸ hKM₀)
    have : Group.IsNilpotent ↥K := hK2.isNilpotent
    exact hKns inferInstance
  · intro C hCT₁ hC1 hCchar hM₀C
    have := hCchar
    have hTT₁ : T ≤ Subgroup.normalizer (T₁ : Set G) := by
      have h1 := S.le_normalizer_inf_normalizer_L h37 h38
      intro t ht
      have h2 := Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht,
        h1 (Setup.T_le_fsuM ht)⟩
      have e' : T ⊓ (fsuM T L ⊓ Subgroup.normalizer (L : Set G)) = T₁ := by
        rw [← inf_assoc, inf_eq_left.mpr Setup.T_le_fsuM]
      rwa [e'] at h2
    have hCmap : (C.subgroupOf T₁).map T₁.subtype = C := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hCT₁]
    have hTC : T ≤ Subgroup.normalizer (C : Set G) := by
      have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (C.subgroupOf T₁)
      rw [hCmap] at h1
      exact hTT₁.trans h1
    have hle := S.normalizer_le_of_le (hT₁2.to_le hCT₁) hC1 (sup_le (hLM₀.trans hM₀C) hTC)
    exact hKM (hKM₀.trans (hM₀C.trans hle))

end Setup

end CFSG.Quasithin.H13.Ch9
