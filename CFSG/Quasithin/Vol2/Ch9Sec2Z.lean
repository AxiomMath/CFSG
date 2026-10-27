module

public import CFSG.Quasithin.Vol2.Ch9Sec1Coord
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3328Pre
public import CFSG.Quasithin.Vol2.Ch8Sec3L0Cent
public import CFSG.Quasithin.Background.S1549DL3M

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin.H CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem exists_fix_of_fix_eq_one {V : Subgroup G} [Finite V] {x u : G}
    (hxV : ∀ v ∈ V, x * v * x⁻¹ ∈ V) (hfix : ∀ v ∈ V, x * v * x⁻¹ = v → v = 1)
    (hu : x * u * x⁻¹ * u⁻¹ ∈ V) : ∃ v ∈ V, x * (v⁻¹ * u) * x⁻¹ = v⁻¹ * u := by
  let f : V → V := fun v => ⟨x * v * x⁻¹ * (v : G)⁻¹, V.mul_mem (hxV v v.2) (V.inv_mem v.2)⟩
  have hinj : Function.Injective f := by
    intro v w hvw
    have h : x * (v : G) * x⁻¹ * (v : G)⁻¹ = x * w * x⁻¹ * (w : G)⁻¹ := congrArg Subtype.val hvw
    have e1 : x * (v : G) * x⁻¹ = x * w * x⁻¹ * (w : G)⁻¹ * v := by rw [← h]; group
    have hwv : x * ((w : G)⁻¹ * v) * x⁻¹ = (w : G)⁻¹ * v := by
      calc x * ((w : G)⁻¹ * v) * x⁻¹ = (x * w * x⁻¹)⁻¹ * (x * v * x⁻¹) := by group
        _ = (w : G)⁻¹ * v := by rw [e1]; group
    have h1 := hfix _ (V.mul_mem (V.inv_mem w.2) v.2) hwv
    refine Subtype.ext ?_
    calc (v : G) = w * ((w : G)⁻¹ * v) := by group
      _ = w := by rw [h1, mul_one]
  obtain ⟨v, hv⟩ := Finite.surjective_of_injective hinj ⟨x * u * x⁻¹ * u⁻¹, hu⟩
  have h : x * (v : G) * x⁻¹ * (v : G)⁻¹ = x * u * x⁻¹ * u⁻¹ := congrArg Subtype.val hv
  refine ⟨v, v.2, ?_⟩
  have e1 : x * u * x⁻¹ = x * v * x⁻¹ * (v : G)⁻¹ * u := by rw [h]; group
  calc x * ((v : G)⁻¹ * u) * x⁻¹ = (x * v * x⁻¹)⁻¹ * (x * u * x⁻¹) := by group
    _ = (v : G)⁻¹ * u := by rw [e1]; group

theorem commute_of_fix_eq_one {U V : Subgroup G} {x g c : G}
    (hfix : ∀ v ∈ V, x * v * x⁻¹ = v → v = 1)
    (hz : x⁻¹ * g⁻¹ * x * g ∈ Subgroup.centralizer (U : Set G)) (hc : c ∈ U)
    (hcx : x * c * x⁻¹ = c) (hgc : g * c * g⁻¹ * c⁻¹ ∈ V) : g * c * g⁻¹ = c := by
  have hzc : x⁻¹ * g⁻¹ * x * g * c = c * (x⁻¹ * g⁻¹ * x * g) :=
    (Subgroup.mem_centralizer_iff.mp hz c hc).symm
  have hxg : x * (g * c * g⁻¹) * x⁻¹ = g * c * g⁻¹ := by
    calc x * (g * c * g⁻¹) * x⁻¹
        = g * x * (x⁻¹ * g⁻¹ * x * g * c) * (x⁻¹ * g⁻¹ * x * g)⁻¹ * x⁻¹ * g⁻¹ := by group
      _ = g * x * (c * (x⁻¹ * g⁻¹ * x * g)) * (x⁻¹ * g⁻¹ * x * g)⁻¹ * x⁻¹ * g⁻¹ := by rw [hzc]
      _ = g * (x * c * x⁻¹) * g⁻¹ := by group
      _ = g * c * g⁻¹ := by rw [hcx]
  have h1 := hfix _ hgc (by
    calc x * (g * c * g⁻¹ * c⁻¹) * x⁻¹ = (x * (g * c * g⁻¹) * x⁻¹) * (x * c * x⁻¹)⁻¹ := by group
      _ = g * c * g⁻¹ * c⁻¹ := by rw [hxg, hcx])
  calc g * c * g⁻¹ = (g * c * g⁻¹ * c⁻¹) * c := by group
    _ = c := by rw [h1, one_mul]

section Torus

variable {K : Type} [Field K]

@[expose] noncomputable def dg (a : K) (ha : a ≠ 0) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![a, 0; 0, a⁻¹], by rw [Matrix.det_fin_two_of, mul_inv_cancel₀ ha, mul_zero, sub_zero]⟩

theorem coe_dg (a : K) (ha : a ≠ 0) :
    ((dg a ha : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![a, 0; 0, a⁻¹] :=
  rfl

theorem eq_one_of_rho_dg_left {a : K} (ha : a ≠ 0) (ha1 : a ≠ 1) {X : Om4.VM K}
    (h : Om4.rho (dg a ha, 1) X = X) : X = 1 := by
  have h1 : !![a, 0; 0, a⁻¹] * Multiplicative.toAdd X = Multiplicative.toAdd X := by
    have := congrArg Multiplicative.toAdd h
    rw [Om4.rho_apply, Om4.toAdd_lr] at this
    simpa [coe_dg] using this
  have hai : a⁻¹ ≠ 1 := fun h' => ha1 (inv_eq_one.mp h')
  have hM : Multiplicative.toAdd X = 0 := by
    ext i j
    have hij := congrFun (congrFun h1 i) j
    fin_cases i
    · simp [Matrix.mul_apply, Fin.sum_univ_two] at hij
      rcases eq_or_ne (Multiplicative.toAdd X 0 j) 0 with h0 | h0
      · simpa using h0
      · exact absurd (mul_right_cancel₀ h0 (hij.trans (one_mul _).symm)) ha1
    · simp [Matrix.mul_apply, Fin.sum_univ_two] at hij
      rcases eq_or_ne (Multiplicative.toAdd X 1 j) 0 with h0 | h0
      · simpa using h0
      · exact absurd (mul_right_cancel₀ h0 (hij.trans (one_mul _).symm)) hai
  simpa using congrArg Multiplicative.ofAdd hM

theorem eq_one_of_rho_dg_right {a : K} (ha : a ≠ 0) (ha1 : a ≠ 1) {X : Om4.VM K}
    (h : Om4.rho (1, dg a ha) X = X) : X = 1 := by
  have h1 : Multiplicative.toAdd X * !![a, 0; 0, a⁻¹] = Multiplicative.toAdd X := by
    have := congrArg Multiplicative.toAdd h
    rw [Om4.rho_apply, Om4.toAdd_lr] at this
    have ht : Matrix.transpose (!![a, 0; 0, a⁻¹] : Matrix (Fin 2) (Fin 2) K) =
        !![a, 0; 0, a⁻¹] := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    simpa [coe_dg, ht] using this
  have hai : a⁻¹ ≠ 1 := fun h' => ha1 (inv_eq_one.mp h')
  have hM : Multiplicative.toAdd X = 0 := by
    ext i j
    have hij := congrFun (congrFun h1 i) j
    fin_cases j
    · simp [Matrix.mul_apply, Fin.sum_univ_two] at hij
      rcases eq_or_ne (Multiplicative.toAdd X i 0) 0 with h0 | h0
      · simpa using h0
      · exact absurd (mul_left_cancel₀ h0 (hij.trans (mul_one _).symm)) ha1
    · simp [Matrix.mul_apply, Fin.sum_univ_two] at hij
      rcases eq_or_ne (Multiplicative.toAdd X i 1) 0 with h0 | h0
      · simpa using h0
      · exact absurd (mul_left_cancel₀ h0 (hij.trans (mul_one _).symm)) hai
  simpa using congrArg Multiplicative.ofAdd hM

end Torus

abbrev zQ (T I : Subgroup G) : Subgroup G :=
  omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuV T I : Set G))

theorem zQ_le_Q (T I : Subgroup G) : zQ T I ≤ T ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
  A4.omegaOneCenterOf_le _

theorem Q_le_centralizer_zQ (T I : Subgroup G) :
    T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ Subgroup.centralizer (zQ T I : Set G) := by
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact (Subgroup.mem_centralizer_iff.mp (A4.omegaOneCenterOf_le_centerOf _ hz).2 q hq).symm

theorem isElemAbelian_zQ (T I : Subgroup G) : IsElemAbelian 2 (zQ T I) :=
  B2F.isElemAbelian_omegaOneCenterOf _

theorem coe_conjAct_apply (W : Subgroup G) (g : Subgroup.normalizer (W : Set G)) (w : W) :
    ((conjAct W g w : W) : G) = g * w * g⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe W (Subgroup.inclusion le_rfl g) w

variable [Finite G] {T L I : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem exists_mem_L0_of_rho {K : Type} [Field K] {e : ↥(fsuV T I) ≃* Om4.VM K}
    (he : (autOn (fsuL0 T L) (fsuV T I)).map (MulAut.congr e).toMonoidHom =
      (Om4.rho (K := K)).range)
    (γ : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :
    ∃ k : Subgroup.normalizer (fsuV T I : Set G), (k : G) ∈ fsuL0 T L ∧
      MulAut.congr e (conjAct (fsuV T I) k) = Om4.rho γ := by
  have hmem : Om4.rho γ ∈ (autOn (fsuL0 T L) (fsuV T I)).map (MulAut.congr e).toMonoidHom := by
    rw [he]
    exact ⟨γ, rfl⟩
  obtain ⟨φ, ⟨k, hk, rfl⟩, hφe⟩ := hmem
  exact ⟨k, hk, hφe⟩

omit [Finite G] in
theorem exists_rho_of_mem_L0 {K : Type} [Field K] {e : ↥(fsuV T I) ≃* Om4.VM K}
    (he : (autOn (fsuL0 T L) (fsuV T I)).map (MulAut.congr e).toMonoidHom =
      (Om4.rho (K := K)).range)
    {k : Subgroup.normalizer (fsuV T I : Set G)} (hk : (k : G) ∈ fsuL0 T L) :
    ∃ γ, MulAut.congr e (conjAct (fsuV T I) k) = Om4.rho γ := by
  have hmem : MulAut.congr e (conjAct (fsuV T I) k) ∈ (Om4.rho (K := K)).range := by
    rw [← he]
    exact ⟨conjAct _ k, ⟨k, hk, rfl⟩, rfl⟩
  obtain ⟨γ, hγ⟩ := hmem
  exact ⟨γ, hγ.symm⟩

namespace Setup

variable (S : Setup T L I n)
include S

theorem not_le_normalizer_L : ¬ T ≤ Subgroup.normalizer (L : Set G) := fun h => by
  obtain ⟨t, ht, htn⟩ := S.exists_not_mem_normalizer
  exact htn (h ht)

theorem inf_centralizer_L0_le (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) :
    fsuL0 T L ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ pCoreOf 2 (fsuL0 T L) := by
  rw [S.hVM]
  exact Vol2.Ch10.SecA.fsuL0_inf_centralizer_le_of_fsu h37c h38c S.hyp.fsu S.not_le_normalizer_L

theorem pCoreOf_L0_le_Q : pCoreOf 2 (fsuL0 T L) ≤ T ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
  rw [← S.hQ]
  exact S1549D.pCoreOf_le_pCoreOf_of_normalizes le_sup_left
    (sup_le Subgroup.le_normalizer T_le_normalizer_L0)

theorem sup_inf_centralizer_le (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) :
    (fsuL0 T L ⊔ T) ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤
      T ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
  rw [← S.hQ]
  exact Lem3328.sup_inf_centralizer_le_pCoreOf S.hyp.fsu.sylow.1 T_le_normalizer_L0 S.hN
    ((pCoreOf_isPGroup 2 _).to_le (S.inf_centralizer_L0_le h37c h38c))

theorem fsuV_le_zQ : fsuV T I ≤ zQ T I := by
  intro v hv
  refine Subgroup.subset_closure ⟨⟨S.fsuV_le_Q hv, Subgroup.mem_centralizer_iff.mpr fun q hq =>
    (Subgroup.mem_centralizer_iff.mp hq.2 v hv).symm⟩, S.hV.2 v hv⟩

theorem L0T_le_normalizer_zQ : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (zQ T I : Set G) :=
  S.L0T_le_normalizer_Q.trans
    (normalizer_le_normalizer_of_map_mulEquiv (F := fun X => omegaOneCenterOf X)
      (fun φ X => omegaOneCenterOf_map_mulEquiv φ X) _)

theorem inf_centralizer_zQ : T ⊓ Subgroup.centralizer (zQ T I : Set G) =
    T ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
  le_antisymm (inf_le_inf_left _ (Subgroup.centralizer_le S.fsuV_le_zQ))
    (le_inf inf_le_left (Q_le_centralizer_zQ T I))

theorem isTwoReducedIn_zQ (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) : IsTwoReducedIn (fsuL0 T L ⊔ T) (zQ T I) := by
  have hred := isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mpr ⟨S.hVLT, S.hRed⟩
  refine ⟨(zQ_le_Q T I).trans (inf_le_left.trans le_sup_right), S.L0T_le_normalizer_zQ,
    isElemAbelian_zQ T I, fun D hDH hHD hD => ?_⟩
  have hDV : D ≤ Subgroup.centralizer (fsuV T I : Set G) := hred.2.2.2 D hDH hHD fun d hd => by
    obtain ⟨k, hk⟩ := hD d hd
    exact ⟨k, Subgroup.centralizer_le S.fsuV_le_zQ hk⟩
  exact ((le_inf hDH hDV).trans (S.sup_inf_centralizer_le h37c h38c)).trans
    (Q_le_centralizer_zQ T I)

theorem zQ_eq_of_commutator_le (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (hZ : centerOf (fsuL0 T L ⊔ T) = ⊥)
    (h : ∀ u ∈ zQ T I, ∀ g ∈ fsuL0 T L, g * u * g⁻¹ * u⁻¹ ∈ fsuV T I) : zQ T I = fsuV T I := by
  classical
  obtain ⟨K, _, _, _, hK, e, he⟩ := S.exists_coord
  obtain ⟨a, ha0, ha1⟩ : ∃ a : K, a ≠ 0 ∧ a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun b _ => by
      by_cases h0 : b = 0
      · simp [h0]
      · simp [hcon b h0]
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ, hK] at h1
    have h2 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
    have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) S.two_le
    omega
  have hCL0 : ∀ k ∈ fsuL0 T L, k ∈ Subgroup.centralizer (fsuV T I : Set G) →
      k ∈ Subgroup.centralizer (zQ T I : Set G) := fun k hk hkC =>
    Q_le_centralizer_zQ T I (S.pCoreOf_L0_le_Q (S.inf_centralizer_L0_le h37c h38c ⟨hk, hkC⟩))
  have hcomm : ∀ k₁ k₂ : Subgroup.normalizer (fsuV T I : Set G), (k₁ : G) ∈ fsuL0 T L →
      (k₂ : G) ∈ fsuL0 T L → ∀ γ₁ γ₂, MulAut.congr e (conjAct (fsuV T I) k₁) = Om4.rho γ₁ →
      MulAut.congr e (conjAct (fsuV T I) k₂) = Om4.rho γ₂ → γ₁ * γ₂ = γ₂ * γ₁ →
      (k₁ : G)⁻¹ * (k₂ : G)⁻¹ * k₁ * k₂ ∈ Subgroup.centralizer (zQ T I : Set G) := by
    intro k₁ k₂ hk₁ hk₂ γ₁ γ₂ h₁ h₂ h₁₂
    have hc : conjAct (fsuV T I) (k₁⁻¹ * k₂⁻¹ * k₁ * k₂) = 1 := by
      apply (MulAut.congr e).injective
      rw [map_one, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, map_inv,
        map_inv, h₁, h₂, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
        show γ₁⁻¹ * γ₂⁻¹ * γ₁ * γ₂ = 1 by rw [mul_assoc, h₁₂]; group, map_one]
    refine hCL0 _ ?_ (A4.conjAct_eq_one_iff.mp hc)
    exact (fsuL0 T L).mul_mem ((fsuL0 T L).mul_mem ((fsuL0 T L).mul_mem
      ((fsuL0 T L).inv_mem hk₁) ((fsuL0 T L).inv_mem hk₂)) hk₁) hk₂
  have hfixγ : ∀ (k : Subgroup.normalizer (fsuV T I : Set G)) (γ),
      MulAut.congr e (conjAct (fsuV T I) k) = Om4.rho γ → (∀ X, Om4.rho γ X = X → X = 1) →
      ∀ v ∈ fsuV T I, (k : G) * v * (k : G)⁻¹ = v → v = 1 := by
    intro k γ hk hγ v hv hkv
    have hw : conjAct (fsuV T I) k ⟨v, hv⟩ = ⟨v, hv⟩ :=
      Subtype.ext (by rw [coe_conjAct_apply]; exact hkv)
    have h1 : Om4.rho γ (e ⟨v, hv⟩) = e ⟨v, hv⟩ := by
      rw [← hk, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply, hw]
    have h2 := hγ _ h1
    rw [map_eq_one_iff e e.injective] at h2
    exact congrArg Subtype.val h2
  obtain ⟨x, hxL, hx⟩ := exists_mem_L0_of_rho he (dg a ha0, 1)
  obtain ⟨y, hyL, hy⟩ := exists_mem_L0_of_rho he (1, dg a ha0)
  have hfx := hfixγ x _ hx fun X hX => eq_one_of_rho_dg_left ha0 ha1 hX
  have hfy := hfixγ y _ hy fun X hX => eq_one_of_rho_dg_right ha0 ha1 hX
  have hxy := hcomm x y hxL hyL _ _ hx hy (by ext <;> simp)
  have hyx := hcomm y x hyL hxL _ _ hy hx (by ext <;> simp)
  have hcxy : ∀ c ∈ zQ T I, (x : G) * c * (x : G)⁻¹ = c → (y : G) * c * (y : G)⁻¹ = c :=
    fun c hc hcx => commute_of_fix_eq_one hfx hxy hc hcx (h c hc y hyL)
  have hcyx : ∀ c ∈ zQ T I, (y : G) * c * (y : G)⁻¹ = c → (x : G) * c * (x : G)⁻¹ = c :=
    fun c hc hcy => commute_of_fix_eq_one hfy hyx hc hcy (h c hc x hxL)
  have hcL0 : ∀ c ∈ zQ T I, (x : G) * c * (x : G)⁻¹ = c →
      ∀ g ∈ fsuL0 T L, g * c * g⁻¹ = c := by
    intro c hc hcx g hg
    have hcy := hcxy c hc hcx
    obtain ⟨γ, hγ⟩ := exists_rho_of_mem_L0 he (k := ⟨g, S.L0_le_normalizer_V hg⟩) hg
    obtain ⟨g₁, hg₁L, hg₁⟩ := exists_mem_L0_of_rho he (γ.1, 1)
    obtain ⟨g₂, hg₂L, hg₂⟩ := exists_mem_L0_of_rho he (1, γ.2)
    have h₁ : (g₁ : G) * c * (g₁ : G)⁻¹ = c :=
      commute_of_fix_eq_one hfy (hcomm y g₁ hyL hg₁L _ _ hy hg₁ (by ext <;> simp)) hc hcy
        (h c hc g₁ hg₁L)
    have h₂ : (g₂ : G) * c * (g₂ : G)⁻¹ = c :=
      commute_of_fix_eq_one hfx (hcomm x g₂ hxL hg₂L _ _ hx hg₂ (by ext <;> simp)) hc hcx
        (h c hc g₂ hg₂L)
    have hd : conjAct (fsuV T I) (⟨g, S.L0_le_normalizer_V hg⟩ * (g₁ * g₂)⁻¹) = 1 := by
      apply (MulAut.congr e).injective
      rw [map_one, map_mul, map_mul, map_inv, map_mul, map_inv, map_mul, hγ, hg₁, hg₂,
        ← map_mul, ← map_inv, ← map_mul]
      have : γ * ((γ.1, 1) * (1, γ.2))⁻¹ = 1 := by ext <;> simp
      rw [this, map_one]
    have hdC := hCL0 _ ((fsuL0 T L).mul_mem hg ((fsuL0 T L).inv_mem
      ((fsuL0 T L).mul_mem hg₁L hg₂L))) (A4.conjAct_eq_one_iff.mp hd)
    have hdc : g * ((g₁ : G) * g₂)⁻¹ * c = c * (g * ((g₁ : G) * g₂)⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp hdC c hc).symm
    calc g * c * g⁻¹ = (g * ((g₁ : G) * g₂)⁻¹) * ((g₁ : G) * ((g₂ : G) * c * (g₂ : G)⁻¹) *
          (g₁ : G)⁻¹) * (g * ((g₁ : G) * g₂)⁻¹)⁻¹ := by group
      _ = (g * ((g₁ : G) * g₂)⁻¹ * c) * (g * ((g₁ : G) * g₂)⁻¹)⁻¹ := by rw [h₂, h₁]
      _ = c := by rw [hdc]; group
  have hW : zQ T I ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥ := by
    have hT2 : IsPGroup 2 T := S.hyp.fsu.sylow.1
    have : Group.IsNilpotent T := hT2.isNilpotent
    set W := zQ T I ⊓ Subgroup.centralizer (fsuL0 T L : Set G) with hWdef
    have hWT : W ≤ T := inf_le_left.trans ((zQ_le_Q T I).trans inf_le_left)
    have hTW : T ≤ Subgroup.normalizer (W : Set G) := fun t ht =>
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨S.L0T_le_normalizer_zQ (Subgroup.mem_sup_right ht),
          B2F.normalizer_le_normalizer_centralizer _ (T_le_normalizer_L0 ht)⟩
    by_contra hne
    have hnormal : (W.subgroupOf T).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hWT).mpr hTW
    have hne' : W.subgroupOf T ≠ ⊥ := by
      intro h0
      apply hne
      rw [← Subgroup.map_subgroupOf_eq_of_le hWT, h0, Subgroup.map_bot]
    obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hne')
    have hzW : (z : G) ∈ W := hz.1
    have hzT : ∀ t ∈ T, t * z = z * t := fun t ht =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hz.2 ⟨t, ht⟩)
    have hzC : (z : G) ∈ Subgroup.centralizer ((fsuL0 T L ⊔ T : Subgroup G) : Set G) := by
      have hle : fsuL0 T L ⊔ T ≤ Subgroup.centralizer ({(z : G)} : Set G) := by
        refine sup_le (fun l hl => ?_) (fun t ht => ?_)
        · rw [Subgroup.mem_centralizer_iff]
          rintro _ rfl
          exact (Subgroup.mem_centralizer_iff.mp hzW.2 l hl).symm
        · rw [Subgroup.mem_centralizer_iff]
          rintro _ rfl
          exact (hzT t ht).symm
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact (Subgroup.mem_centralizer_iff.mp (hle hh) _ rfl).symm
    have hmem : (z : G) ∈ centerOf (fsuL0 T L ⊔ T) := ⟨Subgroup.mem_sup_right z.2, hzC⟩
    rw [hZ, Subgroup.mem_bot] at hmem
    exact hz1 (Subtype.ext (Subtype.ext hmem))
  refine le_antisymm (fun u hu => ?_) S.fsuV_le_zQ
  have hxV : ∀ v ∈ fsuV T I, (x : G) * v * (x : G)⁻¹ ∈ fsuV T I := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp x.2 v).mp hv
  obtain ⟨v, hv, hvu⟩ := exists_fix_of_fix_eq_one hxV hfx (h u hu x hxL)
  have hcz : (v : G)⁻¹ * u ∈ zQ T I := (zQ T I).mul_mem ((zQ T I).inv_mem (S.fsuV_le_zQ hv)) hu
  have hcW : (v : G)⁻¹ * u ∈ zQ T I ⊓ Subgroup.centralizer (fsuL0 T L : Set G) := by
    refine ⟨hcz, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    have := hcL0 _ hcz hvu g hg
    calc g * ((v : G)⁻¹ * u) = (g * ((v : G)⁻¹ * u) * g⁻¹) * g := by group
      _ = (v : G)⁻¹ * u * g := by rw [this]
  rw [hW, Subgroup.mem_bot] at hcW
  have : u = v := by
    calc u = v * ((v : G)⁻¹ * u) := by group
      _ = v := by rw [hcW, mul_one]
  exact this ▸ hv

end Setup

end CFSG.Quasithin.H13.Ch9
