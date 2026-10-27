module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res2ProofXAutCount
public import CFSG.RankThree.PartTwo.Sec20.Item20ResProofLCentral
import CFSG.Quasithin.EmptyFaithful.SBc8Transfer
public import CFSG.RankThree.PartTwo.Sec20.Item20ResProofLNormal

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.CGT.T75N
open CFSG.RankThree.PartTwo.Sec20.Res2

variable {G : Type} [Group G] [Finite G]

theorem exists_vstab_coords {K V P D : Subgroup G} {Z : Set G}
    {F : Type} [Field F] [Fintype F] {n : ℕ} (hF : Fintype.card F = 2 ^ n)
    (α : ↥K →* SpecialLinearGroup (Fin 3) F) (hα : Function.Surjective α)
    (β : ↥V ≃* Multiplicative (Fin 3 → F))
    (hβ : ∀ (k : ↥K) (v w : ↥V), (w : G) = k * v * (k : G)⁻¹ →
      Multiplicative.toAdd (β w) =
        (α k : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β v))
    (hKV : K ≤ Subgroup.normalizer (V : Set G))
    (hP : CFSG.ABGLocalTools.IsSylowOf 2 P K)
    (hZV : ∀ z ∈ Z, ∀ v ∈ V, z * v * z⁻¹ = v)
    (hZP : ∀ z ∈ Z, ∀ p ∈ P, p * z * p⁻¹ * z⁻¹ = 1)
    (hZK : ∀ z ∈ Z, ∀ k ∈ K, k * z * k⁻¹ * z⁻¹ ∈ V)
    (hCZ : ∀ k ∈ K, (∀ z ∈ Z, k * z * k⁻¹ = z) → k ∈ D) :
    ∃ g : SpecialLinearGroup (Fin 3) F, ∀ k : ↥K,
      ((g⁻¹ * α k * g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        Pi.single 0 1 = Pi.single 0 1 → (k : G) ∈ D := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hF
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
    intro x hx y hy
    have h : β (⟨x, hx⟩ * ⟨y, hy⟩) = β (⟨y, hy⟩ * ⟨x, hx⟩) := by
      rw [map_mul, map_mul, mul_comm]
    exact congrArg Subtype.val (β.injective h)
  have hV2 : IsPGroup 2 V := by
    refine IsPGroup.of_card (n := n * 3) ?_
    rw [Nat.card_congr β.toEquiv, Nat.card_congr Multiplicative.ofAdd.symm,
      Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, hF, pow_mul]
  have hodd : ¬ 2 ∣ P.relIndex K := (CFSG.ABGLocalTools.isSylowOf_iff.mp hP).2.2
  have htr : ∀ z ∈ Z, ∃ m ∈ V, ∀ k ∈ K, k * (z * m⁻¹) * k⁻¹ = z * m⁻¹ := fun z hz =>
    CFSG.Quasithin.SBc8.exists_mul_centralizer_of_cocycle hKV hVc hV2 hP.le hodd (hZV z hz)
      (hZK z hz) (hZP z hz)
  choose! m hmV hmC using htr
  have hmP : ∀ z ∈ Z, ∀ p ∈ P, p * m z * p⁻¹ = m z := by
    intro z hz p hp
    have h1 := hmC z hz p (hP.le hp)
    have h2 : p * z * p⁻¹ = z := mul_inv_eq_one.mp (hZP z hz p hp)
    calc p * m z * p⁻¹ = (p * (z * (m z)⁻¹) * p⁻¹)⁻¹ * (p * z * p⁻¹) := by group
      _ = (z * (m z)⁻¹)⁻¹ * z := by rw [h1, h2]
      _ = m z := by group
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  obtain ⟨g, hg⟩ := exists_conj_unitriangular_le_sylow (Q.mapSurjective hα)
  have hU : ∀ u ∈ LinearFlag.unitriangular 3 F,
      ∃ p : ↥K, (p : G) ∈ P ∧ g⁻¹ * α p * g = u := by
    intro u hu
    have h := hg u hu
    rw [Sylow.coe_mapSurjective, hQ] at h
    obtain ⟨p, hp, hpu⟩ := h
    exact ⟨p, Subgroup.mem_subgroupOf.mp hp, by rw [hpu]; group⟩
  refine ⟨g, fun k hk => hCZ k k.2 fun z hz => ?_⟩
  set b : ↥V → Fin 3 → F := fun v =>
    ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      Multiplicative.toAdd (β v) with hbdef
  have hb_eq : ∀ (k' : ↥K) (v w : ↥V), (w : G) = k' * v * (k' : G)⁻¹ →
      b w = ((g⁻¹ * α k' * g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        b v := by
    intro k' v w hw
    simp only [hbdef, hβ k' v w hw]
    rw [Res2.mulVec_mul_mul, Res2.mulVec_inv_mulVec]
  have hb_inj : Function.Injective b := by
    intro v w hvw
    have h := congrArg (fun x => (g : Matrix (Fin 3) (Fin 3) F) *ᵥ x) hvw
    simp only [hbdef, Res2.mulVec_inv_mulVec] at h
    exact β.injective (Multiplicative.toAdd.injective h)
  have hmline : b ⟨m z, hmV z hz⟩ 1 = 0 ∧ b ⟨m z, hmV z hz⟩ 2 = 0 := by
    apply coords_eq_zero_of_unitriangular_fixed
    intro u hu
    obtain ⟨p, hp, rfl⟩ := hU u hu
    exact (hb_eq p ⟨m z, hmV z hz⟩ ⟨m z, hmV z hz⟩ (hmP z hz p hp).symm).symm
  have hkv : (k : G) * m z * (k : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (hKV k.2) (m z)).mp (hmV z hz)
  have hline : b ⟨m z, hmV z hz⟩ =
      b ⟨m z, hmV z hz⟩ 0 • (Pi.single 0 1 : Fin 3 → F) := Res2.eq_smul_e0 hmline.1 hmline.2
  have hfix : b ⟨_, hkv⟩ = b ⟨m z, hmV z hz⟩ := by
    rw [hb_eq k ⟨m z, hmV z hz⟩ ⟨_, hkv⟩ rfl, hline, mulVec_smul, hk]
  have hkm : (k : G) * m z * (k : G)⁻¹ = m z := congrArg Subtype.val (hb_inj hfix)
  calc (k : G) * z * (k : G)⁻¹
      = ((k : G) * (z * (m z)⁻¹) * (k : G)⁻¹) * ((k : G) * m z * (k : G)⁻¹) := by group
    _ = z * (m z)⁻¹ * m z := by rw [hmC z hz k k.2, hkm]
    _ = z := by group

theorem sl3_eq_one_of_fix_basis {F : Type} [Field F] {r : SpecialLinearGroup (Fin 3) F}
    (h : ∀ j : Fin 3, (r : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single j 1 = Pi.single j 1) : r = 1 := by
  apply Subtype.ext
  ext i j
  have := congrFun (h j) i
  rw [mulVec_single_one, col_apply] at this
  rw [this]
  simp [Pi.single_apply, Matrix.one_apply]

theorem eq_bot_of_normal_le_urad {F : Type} [Field F]
    {R : Subgroup (SpecialLinearGroup (Fin 3) F)} (hRu : R ≤ urad F)
    (hR : ∀ h : SpecialLinearGroup (Fin 3) F,
      h ∈ Subgroup.normalizer (R : Set (SpecialLinearGroup (Fin 3) F))) : R = ⊥ := by
  rw [eq_bot_iff]
  intro r hr
  rw [Subgroup.mem_bot]
  have hfix : ∀ r' ∈ R, (r' : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 = Pi.single 0 1 :=
    fun r' hr' => (mem_urad_iff.mp (hRu hr')).1
  have hmove : ∀ (i : Fin 3) (hi : i ≠ 0),
      (r : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single i 1 = Pi.single i 1 := by
    intro i hi
    set h := SpecialLinearGroup.transvection hi (1 : F) with hh
    have h1 : h⁻¹ * r * h ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp (hR h⁻¹) r).mp hr
      simpa using this
    have h2 := (Res2.conj_mulVec_eq_iff h r _ _).mp (hfix _ h1)
    have he : (h : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 =
        Pi.single 0 1 + Pi.single i 1 := by
      rw [hh, SpecialLinearGroup.transvection_coe, ← transvection, LinearFlag.transvection_mulVec]
      simp
    rw [he, mulVec_add, hfix r hr] at h2
    exact add_left_cancel h2
  refine sl3_eq_one_of_fix_basis fun j => ?_
  fin_cases j
  · exact hfix r hr
  · exact hmove 1 (by decide)
  · exact hmove 2 (by decide)

theorem urad_le_of_normal {F : Type} [Field F] [CharP F 2]
    {Y : Subgroup (SpecialLinearGroup (Fin 3) F)} (hYv : Y ≤ vstab F)
    (hY : vstab F ≤ Subgroup.normalizer (Y : Set (SpecialLinearGroup (Fin 3) F)))
    {c : SpecialLinearGroup (Fin 3) F} (hcY : c ∈ Y) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) :
    urad F ≤ Y := by
  have hcv : c ∈ vstab F := hYv hcY
  have hcu := not_mem_urad_of_pow_three hc3 hc1
  have hR : Y ⊓ urad F = urad F := by
    refine eq_urad_of_le inf_le_right (fun k hk => ?_) ?_
    · exact Sec20.mem_normalizer_inf_of_mem (hY hk) (Subgroup.mem_normalizer_iff.mpr fun u => by
        constructor
        · exact fun hu => conj_mem_urad (vstab_le_lstab hk) hu
        · intro hu
          have := conj_mem_urad (vstab_le_lstab ((vstab F).inv_mem hk)) hu
          simpa [mul_assoc] using this)
    · obtain ⟨u, hu, hne⟩ := exists_commutator_ne_one hcv hcu
      refine (Subgroup.ne_bot_iff_exists_ne_one).mpr ⟨⟨u * c * u⁻¹ * c⁻¹, ?_, ?_⟩, ?_⟩
      · exact Y.mul_mem ((Subgroup.mem_normalizer_iff.mp (hY (urad_le_vstab hu)) c).mp hcY)
          (Y.inv_mem hcY)
      · have := conj_mem_urad (vstab_le_lstab hcv) ((urad F).inv_mem hu)
        rw [show u * c * u⁻¹ * c⁻¹ = u * (c * u⁻¹ * c⁻¹) by group]
        exact (urad F).mul_mem hu this
      · intro h
        exact hne (congrArg Subtype.val h)
  rw [← hR]
  exact inf_le_left

omit [Finite G] in
theorem mem_normalizer_commutator_self {Q : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) :
    g ∈ Subgroup.normalizer ((⁅Q, Q⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
  rw [Subgroup.map_commutator, hg]

theorem mem_normalizer_commutator_sup_zQ {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G)) :
    g ∈ Subgroup.normalizer
      ((⁅CFSG.Open.pCoreOf 2 X, CFSG.Open.pCoreOf 2 X⁆ ⊔ zQ X : Subgroup G) : Set G) :=
  Subgroup.inf_normalizer_le_normalizer_sup _ _
    ⟨mem_normalizer_commutator_self hg, normalizer_le_normalizer_zQ hg⟩

theorem step209XAut_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) (hN : N = Subgroup.normalizer (L : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hTN : T ≤ N)
    (h7 : kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N)
    (hblock : IsBlock M (kTwenty M c)) (hVO : vTwenty M c T = CFSG.Open.pCoreOf 2 (kTwenty M c))
    {n : ℕ} (hn : Odd n) (hnat : IsNaturalL3Module (kTwenty M c) (vTwenty M c T) n) {y : G}
    (hyr : n = 1 ∧ y ^ 7 = 1 ∨ 1 < n ∧ y ^ 5 = 1)
    (hyX : y ∈ Subgroup.normalizer (normalClosureIn (kTwenty M c ⊓ N) c : Set G))
    (hyc : ∀ x ∈ normalClosureIn (kTwenty M c ⊓ N) c, y * x * y⁻¹ * x⁻¹ ∈
      CFSG.Open.pCoreOf 2 (normalClosureIn (kTwenty M c ⊓ N) c)) :
    y ∈ Subgroup.normalizer (vTwenty M c T : Set G) := by
  have hnat' := hnat
  set K := kTwenty M c with hKdef
  set V := vTwenty M c T with hVdef
  set X := normalClosureIn (K ⊓ N) c with hXdef
  obtain ⟨hVK, F, _, _, hF, α, hαs, hαk, β, hβ⟩ := hnat
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hF
  have hq3 : Nat.card F % 3 = 2 := by
    rw [Nat.card_eq_fintype_card, hF]
    exact two_pow_mod_three_of_odd hn
  have hKM : K ≤ M := kTwenty_le_of_hyp201 hT.toHyp201
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := le_normalizer_normalClosureIn M c
  have hMV : M ≤ Subgroup.normalizer (V : Set G) := by
    rw [hVO]
    exact hMK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hKV : K ≤ Subgroup.normalizer (V : Set G) := hKM.trans hMV
  have hV2 : IsPGroup 2 V := hVO ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (kTwenty M c)
  have hVT : V ≤ T :=
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hVK.trans hKM) hMV hV2).trans
      (pCoreOf_le_of_isSylowOf hT.sylow)
  have hVN : V ≤ N := hVT.trans hTN
  have hcA : c ∈ A := mem_of_hyp201 hT.toHyp201
  have hc3 : c ^ 3 = 1 := hT.mem_partTwoE.1.2 c hcA
  have hcK : c ∈ K := self_mem_normalClosureIn M c
  have hcN : c ∈ N := by
    rw [hN]
    exact hAL hcA
  have hVX : V ≤ X := step209V_core hT hTN h7 ⟨hblock, hVO, n, hn, hnat'⟩
  have hXKN : X ≤ K ⊓ N := normalClosureIn_le ⟨hcK, hcN⟩
  have hXK : X ≤ K := hXKN.trans inf_le_left
  have hcX : c ∈ X := self_mem_normalClosureIn (K ⊓ N) c
  obtain ⟨g, hg⟩ := exists_vstab_coords (P := T ⊓ K) (Z := (zTwenty T : Set G)) (D := N) hF α
    hαs β hβ hKV (hT.sylow.inf_of_le_normalizer hKM hMK)
    (fun z hz v hv => by rw [← (mem_and_commute_of_mem_zTwenty hz).2 v (hVT hv)]; group)
    (fun z hz p hp => by rw [(mem_and_commute_of_mem_zTwenty hz).2 p hp.1]; group)
    (fun z hz k hk => by
      have h1 : z * k * z⁻¹ * k⁻¹ ∈ vTwenty M c T := Subgroup.commutator_mem_commutator hz hk
      rw [show k * z * k⁻¹ * z⁻¹ = (z * k * z⁻¹ * k⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ h1)
    (fun k hk hkz => by
      refine h7 ⟨hk, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
      have := hkz z hz
      calc z * k = k * z * k⁻¹ * k := by rw [this]
        _ = k * z := by group)
  set α' : ↥K →* SpecialLinearGroup (Fin 3) F := (MulAut.conj g⁻¹).toMonoidHom.comp α with hα'
  have hα'_apply : ∀ k, α' k = g⁻¹ * α k * g := by
    intro k
    simp [hα']
  let Lg : (Fin 3 → F) ≃+ (Fin 3 → F) :=
    { toFun := fun x => ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x
      invFun := fun x => (g : Matrix (Fin 3) (Fin 3) F) *ᵥ x
      left_inv := fun x => Res2.mulVec_inv_mulVec g x
      right_inv := fun x => Res2.inv_mulVec_mulVec g x
      map_add' := fun x y => mulVec_add _ x y }
  let d : NatData G K V F :=
    { α := α'
      surj := fun x => by
        obtain ⟨k, hk⟩ := hαs (g * x * g⁻¹)
        exact ⟨k, by rw [hα'_apply, hk]; group⟩
      ker := by
        ext k
        rw [MonoidHom.mem_ker, hα'_apply, ← hαk, MonoidHom.mem_ker]
        constructor
        · intro h
          calc α k = g * (g⁻¹ * α k * g) * g⁻¹ := by group
            _ = 1 := by rw [h]; group
        · intro h
          rw [h]
          group
      β := β.trans (AddEquiv.toMultiplicative Lg)
      equiv := fun k v w hw => by
        change ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
            Multiplicative.toAdd (β w) =
          ((α' k : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
            (((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
              Multiplicative.toAdd (β v))
        rw [hβ k v w hw, hα'_apply, Res2.mulVec_mul_mul, Res2.mulVec_inv_mulVec] }
  have hdα : ∀ k, d.α k = g⁻¹ * α k * g := hα'_apply
  have hK0 : ∀ k : ↥K, d.α k ∈ vstab F → (k : G) ∈ N := by
    intro k hk
    refine hg k ?_
    rw [← hdα k]
    exact hk
  have hc1 : d.α ⟨c, hcK⟩ ≠ 1 := by
    intro h1
    have hαc : α ⟨c, hcK⟩ = 1 := by
      have := hdα ⟨c, hcK⟩
      rw [h1] at this
      calc α ⟨c, hcK⟩ = g * (g⁻¹ * α ⟨c, hcK⟩ * g) * g⁻¹ := by group
        _ = 1 := by rw [← this]; group
    have hcV : c ∈ V := by
      have : (⟨c, hcK⟩ : ↥K) ∈ V.subgroupOf K := by
        rw [← hαk, MonoidHom.mem_ker]
        exact hαc
      exact Subgroup.mem_subgroupOf.mp this
    have hKV' : K ≤ V := by
      rw [hKdef, kTwenty, normalClosureIn, Subgroup.closure_le]
      rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hMV hx) c).mp hcV
    have h01 : (0 : Fin 3) ≠ 1 := by decide
    obtain ⟨k, hk⟩ := hαs (Matrix.SpecialLinearGroup.transvection h01 (1 : F))
    have hk1 : α k = 1 := by
      rw [← MonoidHom.mem_ker, hαk, Subgroup.mem_subgroupOf]
      exact hKV' k.2
    rw [hk1] at hk
    have h2 := congrArg (fun B : Matrix.SpecialLinearGroup (Fin 3) F =>
      (B : Matrix (Fin 3) (Fin 3) F) 0 1) hk
    simp [Matrix.SpecialLinearGroup.transvection_coe] at h2
  have hc3' : d.α ⟨c, hcK⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨c, hcK⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this, map_one]
  have hyQ : y ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X hyX
  by_cases hKN : K ≤ N
  ·
    have hKX : K ≤ Subgroup.normalizer (X : Set G) := fun k hk =>
      le_normalizer_normalClosureIn (K ⊓ N) c ⟨hk, hKN hk⟩
    set Q := CFSG.Open.pCoreOf 2 X with hQ
    have hQK : Q ≤ K := (CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hXK
    set R := (Q.subgroupOf K).map d.α with hR
    have hR2 : IsPGroup 2 R :=
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).comap_subtype (K := K)).map _
    have hRn : ∀ h : SpecialLinearGroup (Fin 3) F,
        h ∈ Subgroup.normalizer (R : Set (SpecialLinearGroup (Fin 3) F)) := by
      intro h
      obtain ⟨k, rfl⟩ := d.surj h
      apply Sec20.mem_normalizer_of_map_conj_le
      rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
      refine ⟨k * r * k⁻¹, ?_, by simp⟩
      have hr' : (r : G) ∈ Q := Subgroup.mem_subgroupOf.mp hr
      refine Subgroup.mem_subgroupOf.mpr ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X (hKX k.2)) _).mp hr'
    have hRu : R ≤ urad F :=
      le_urad_of_isPGroup le_rfl irredModE0_vstab hR2 (fun h _ => hRn h)
    have hRbot := eq_bot_of_normal_le_urad hRu hRn
    have hQV : Q ≤ V := by
      intro q hq
      have hmem : d.α ⟨q, hQK hq⟩ ∈ R := ⟨⟨q, hQK hq⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
      rw [hRbot, Subgroup.mem_bot] at hmem
      have : (⟨q, hQK hq⟩ : ↥K) ∈ d.α.ker := hmem
      rw [d.ker, Subgroup.mem_subgroupOf] at this
      exact this
    have hVQ : V ≤ Q :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVX (hXK.trans hKV) hV2
    have hQeq : Q = V := le_antisymm hQV hVQ
    rw [← hQeq]
    exact hyQ
  set IKN := ((K ⊓ N).subgroupOf K).map d.α with hIKN
  have hvI : vstab F ≤ IKN := by
    intro h hh
    obtain ⟨k, rfl⟩ := d.surj h
    exact ⟨k, Subgroup.mem_subgroupOf.mpr ⟨k.2, hK0 k hh⟩, rfl⟩
  have hIl : IKN ≤ lstab F := by
    by_contra hnot
    apply hKN
    have htop := eq_top_of_vstab_le hvI hnot
    intro k hk
    have hmem : d.α ⟨k, hk⟩ ∈ IKN := htop ▸ Subgroup.mem_top _
    obtain ⟨k', hk', hkk'⟩ := hmem
    have hk'N : (k' : G) ∈ N := (Subgroup.mem_subgroupOf.mp hk').2
    have hker : k'⁻¹ * ⟨k, hk⟩ ∈ d.α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hkk', inv_mul_cancel]
    rw [d.ker, Subgroup.mem_subgroupOf] at hker
    have : k = k' * (k'⁻¹ * ⟨k, hk⟩ : ↥K) := by simp
    rw [this]
    exact N.mul_mem hk'N (hVN hker)
  set IX := (X.subgroupOf K).map d.α with hIX
  have hXv : IX ≤ vstab F := by
    have hle : X ≤ ((vstab F).comap d.α).map K.subtype := by
      rw [hXdef, normalClosureIn, Subgroup.closure_le]
      rintro _ ⟨k, hk, rfl⟩
      have hkc : k * c * k⁻¹ ∈ K ⊓ N :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hk ⟨hcK, hcN⟩) (Subgroup.inv_mem _ hk)
      refine ⟨⟨k * c * k⁻¹, hkc.1⟩, ?_, rfl⟩
      refine mem_vstab_of_mem_lstab_of_pow_three hq3
        (hIl ⟨_, Subgroup.mem_subgroupOf.mpr hkc, rfl⟩) ?_
      rw [← map_pow]
      have : (⟨k * c * k⁻¹, hkc.1⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by
        simp only [SubmonoidClass.coe_pow, Subgroup.coe_one]
        rw [conj_pow, hc3]
        group)
      rw [this, map_one]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, hk, hkx⟩ := hle (Subgroup.mem_subgroupOf.mp hx)
    have : k = x := Subtype.ext hkx
    rw [← this]
    exact hk
  have hXnv : vstab F ≤ Subgroup.normalizer (IX : Set (SpecialLinearGroup (Fin 3) F)) := by
    intro h hh
    obtain ⟨k, hk, rfl⟩ := hvI hh
    have hkKN : (k : G) ∈ K ⊓ N := Subgroup.mem_subgroupOf.mp hk
    apply Sec20.mem_normalizer_of_map_conj_le
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨k * x * k⁻¹, ?_, by simp⟩
    have hx' : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
    refine Subgroup.mem_subgroupOf.mpr ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_normalClosureIn (K ⊓ N) c hkKN) _).mp hx'
  have hcIX : d.α ⟨c, hcK⟩ ∈ IX := ⟨⟨c, hcK⟩, Subgroup.mem_subgroupOf.mpr hcX, rfl⟩
  have huX : urad F ≤ IX := urad_le_of_normal hXv hXnv hcIX hc3' hc1
  have hIXv : 1 < n → IX = vstab F := by
    intro hn1
    have h4 : 4 ≤ Nat.card F := by
      rw [Nat.card_eq_fintype_card, hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
    exact eq_vstab_of_normal h4 hXv hXnv hcIX hc3' hc1
  have hirr : IrredModE0 F IX := by
    rcases Nat.lt_or_ge 1 n with hn1 | hn1
    · rw [hIXv hn1]
      exact irredModE0_vstab
    · have hn1' : n = 1 := by
        obtain ⟨k, rfl⟩ := hn
        omega
      have h2 : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hF, hn1', pow_one]
      exact irredModE0_of_card_two h2 hXv huX hcIX hc3' hc1
  have hX : XData d X := ⟨hVX, hXK, hXv, hirr, huX⟩
  set Q := CFSG.Open.pCoreOf 2 X with hQ
  set D := ⁅Q, Q⁆ ⊔ zQ X with hD
  have hXD : X ≤ Subgroup.normalizer (D : Set G) := fun x hx =>
    mem_normalizer_commutator_sup_zQ (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hx)
  rcases hX.eq_or_eq_of_invariant hF le_sup_right (sup_le hX.commutator_le (hX.zQ_le hF)) hXD
    with hDz | hDV
  ·
    have hcomm : ⁅Q, Q⁆ ≤ zQ X := by
      rw [← hDz]
      exact le_sup_left
    rcases hyr with ⟨hn1, hy7⟩ | ⟨hn1, hy5⟩
    · subst hn1
      exact hX.mem_normalizer_of_seven hF hcomm hcX hc3 hc1 hyX hyc hy7
    · exact hX.mem_normalizer_of_five hF hn (hIXv hn1).ge hcomm hyX hyc hy5
  ·
    rw [← hDV]
    exact mem_normalizer_commutator_sup_zQ hyQ

theorem step209XAut_proof : Step209XAut := by
  intro G _ _ A M L N c T hT hTN h7 hblock hVO n hn hnat y hyr hyX hyc
  obtain ⟨H, -, -, -, hN⟩ := exists_sec18H_of_ctx20One hT
  exact step209XAut_core hT.toCtx20 hN (le_normalizer_of_hyp201One hT.hyp201One) hTN h7 hblock
    hVO hn hnat hyr hyX hyc

theorem item209One_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) (hN : N = Subgroup.normalizer (L : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hLq : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* CFSG.Assembly.RankThreeEven.projSL 3
      (GaloisField 2 2)))
    (hLp : ⁅L, L⁆ = L) (hLM : ¬ L ≤ M) (hO2L : CFSG.Open.pCoreOf 2 L ≤ M) (hTN : T ≤ N)
    (h7 : kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N)
    (h8 : IsBlock M (kTwenty M c) ∧ vTwenty M c T = CFSG.Open.pCoreOf 2 (kTwenty M c) ∧
      ∃ n : ℕ, Odd n ∧ IsNaturalL3Module (kTwenty M c) (vTwenty M c T) n) :
    ⁅L, vTwenty M c T⁆ = ⊥ :=
  (step209LCentral_core hT hN hAL hLq hLp hLM hTN h7 h8
    (fun _ hn hnat _ hyr hyX hyc =>
      step209XAut_core hT hN hAL hTN h7 h8.1 h8.2.1 hn hnat hyr hyX hyc)
    (step209LNormal_core hT hN hAL hO2L hTN h8)).elim

end CFSG.RankThree.PartTwo.Sec20
