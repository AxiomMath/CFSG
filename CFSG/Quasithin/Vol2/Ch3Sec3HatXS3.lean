module

public import CFSG.Quasithin.Vol2.Ch3Sec3HatRho
public import CFSG.Quasithin.Vol2.Ch3Sec3G2XS3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.Par32
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative commutatorElement

namespace HatX

open CFSG.Quasithin.H13.HatC CFSG.Quasithin.H13.HatM

variable {G : Type} [Group G]

theorem fix_line {x : MulAut W6} (hx : x ∈ Gam0) (hw : x w0 = w0) (k : ℕ) :
    x ((hom ^ k) w0) = (hom ^ k) w0 := by
  have hc : x * hom ^ k = hom ^ k * x := Commute.pow_right (comm_hom hx) k
  rw [← MulAut.mul_apply, hc, MulAut.mul_apply, hw]

theorem D0_le_Gam0 : D0 ≤ Gam0 := fun y hy =>
  (show y ∈ Gam0 ⊓ S0 by rw [inf_S0_eq]; exact hy).1

theorem cZ_eq [Finite G]
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) {T M L D : Subgroup G} (h : Hyp331 G T M L D)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hH : CFSG.Quasithin.IsHatA6Block L)
    (hG : Nat.card ↥Gam0 = 1080)
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* MulAut W6) (β : ↥(blockU L) ≃* W6)
    (hβe : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)),
      (u' : G) = g * u * g⁻¹ → β u' = ρ g (β u))
    (hρN : ∀ g, ρ g ∈ Nor0)
    (hρL : ∀ ℓ (hℓ : ℓ ∈ L), ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ ∈ Gam0)
    (hρL' : ∀ x ∈ Gam0, ∃ ℓ, ∃ hℓ : ℓ ∈ L, ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = x)
    (hρT : ∀ t (ht : t ∈ T), ρ ⟨t, hTL ht⟩ ∈ S0) :
    oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) =
      oTwoUpper (pre ρ (sup_le Subgroup.le_normalizer hTL) P0) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hshort := hH.1
  have hT2 : IsPGroup 2 T := h.toSetup331.isSylowTwoOf.2.1
  have hTidx : ¬ 2 ∣ T.index := h.sylow.2
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have : Finite ↥Gam0 := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  have hsylL : IsSylowTwoOf (T ⊓ L) L := by
    have hTsyl : IsSylowTwoOf T (L ⊔ T) :=
      ⟨le_sup_right, hT2, fun h2 =>
        hTidx (h2.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))⟩
    exact A4.isSylowTwoOf_inf_normal hTsyl le_sup_left hLTN
  have hSD : ∀ y ∈ D0, ∃ t ∈ T, ∃ ht : t ∈ L, ρ ⟨t, Subgroup.le_normalizer ht⟩ = y := by
    let ρL : ↥L →* ↥Gam0 :=
      (ρ.comp (Subgroup.inclusion Subgroup.le_normalizer)).codRestrict _ (fun ℓ => hρL ℓ.1 ℓ.2)
    have hρLs : Function.Surjective ρL := by
      intro y
      obtain ⟨ℓ, hℓ, e⟩ := hρL' y.1 y.2
      exact ⟨⟨ℓ, hℓ⟩, Subtype.ext e⟩
    have hPQ : ((T ⊓ L).subgroupOf L).map ρL ≤ D0.subgroupOf Gam0 := by
      rintro _ ⟨x, hx, rfl⟩
      refine Subgroup.mem_subgroupOf.mpr ?_
      rw [← inf_S0_eq]
      exact ⟨hρL x.1 x.2, hρT x.1 (Subgroup.mem_subgroupOf.mp hx).1⟩
    have hQ2 : IsPGroup 2 ↥(D0.subgroupOf Gam0) := IsPGroup.of_card (n := 3) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe D0_le_Gam0).toEquiv, card_D0]
      norm_num)
    have hPidx : ¬ 2 ∣ (((T ⊓ L).subgroupOf L).map ρL).index := fun h2 => hsylL.2.2
      (h2.trans (Subgroup.index_map_dvd _ hρLs))
    have hPQeq := G2XS3.eq_of_le_of_odd hPQ hQ2 hPidx
    intro y hyD
    have hyQ : (⟨y, D0_le_Gam0 hyD⟩ : ↥Gam0) ∈ ((T ⊓ L).subgroupOf L).map ρL := by
      rw [hPQeq]
      exact Subgroup.mem_subgroupOf.mpr hyD
    obtain ⟨x, hx, e⟩ := hyQ
    exact ⟨x.1, (Subgroup.mem_subgroupOf.mp hx).1, x.2, congrArg Subtype.val e⟩
  have hfix : ∀ v : W6, (∀ t (ht : t ∈ T), ρ ⟨t, hTL ht⟩ v = v) →
      v = 1 ∨ v = w0 ∨ v = hom w0 ∨ v = hom (hom w0) := by
    intro v hv
    apply fix_D0 v
    intro y hy
    obtain ⟨t, ht, htL, e⟩ := hSD y hy
    rw [← e]
    exact hv t ht
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hVQ : vPlus L T ≤ qL L T := hred.1.trans inf_le_left
  set Z := quasithinOmegaOneCenter T with hZdef
  have hMp := Hyp331.mPlus_eq_of_le hTL
  obtain ⟨-, -, -, ⟨-, hV4⟩⟩ := stmt3_3_7_of h38 h39 G T M L D h
  rw [hMp] at hV4
  have hVL : ⁅vPlus L T, L⁆ ≤ blockU L :=
    (Subgroup.commutator_mono hVQ le_rfl).trans (Hyp331.commutator_qL_le_blockU hshort hTL)
  have hZV : Z ≤ vPlus L T := le_conjClosure _ _
  have hUL : blockU L ≤ L := commutator_le_right_of_le_normalizer
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans Subgroup.le_normalizer)
  have hCZU : Z ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.normalizer (blockU L : Set G) :=
    fun c hc => Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hUL hc.2)
  have hZdec : ∀ z ∈ Z, ∃ u ∈ Z ⊓ blockU L, ∃ c ∈ Z ⊓ Subgroup.centralizer (L : Set G),
      z = u * c := by
    intro z hz
    have h1 : z ∈ blockU L ⊔ Z ⊓ Subgroup.centralizer (L : Set G) := by
      have h2 := hZV hz
      rw [hV4] at h2
      exact (sup_le_sup_right hVL _) h2
    obtain ⟨u, hu, c, hc, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hCZU).mp h1
    refine ⟨u, ⟨?_, hu⟩, c, hc, rfl⟩
    have := Z.mul_mem hz (Z.inv_mem hc.1)
    rwa [mul_inv_cancel_right] at this
  have hcentZ : ∀ y ∈ L, (∀ u ∈ Z ⊓ blockU L, u * y = y * u) →
      y ∈ Subgroup.centralizer (Z : Set G) := by
    intro y hy hyU
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨u, hu, c, hc, rfl⟩ := hZdec z hz
    have hcy : c * y = y * c := (Subgroup.mem_centralizer_iff.mp hc.2 y hy).symm
    calc u * c * y = u * (c * y) := mul_assoc _ _ _
      _ = u * (y * c) := by rw [hcy]
      _ = (u * y) * c := (mul_assoc _ _ _).symm
      _ = (y * u) * c := by rw [hyU u hu]
      _ = y * (u * c) := mul_assoc _ _ _
  have hnot : ¬ Z ⊓ blockU L ≤ blockZ L := by
    intro hle
    apply h.not_L_le_centralizer h38 h39
    have hZL : Z ≤ Subgroup.centralizer (L : Set G) := by
      intro z hz
      obtain ⟨u, hu, c, hc, rfl⟩ := hZdec z hz
      exact Subgroup.mul_mem _ (hle hu).2 hc.2
    have hVc : vPlus L T ≤ Subgroup.centralizer (L : Set G) := by
      show conjClosure Z (mPlus L T) ≤ _
      rw [hMp]
      refine conjClosure_le fun ℓ hℓ z hz => ?_
      have h1 := Subgroup.mem_centralizer_iff.mp (hZL hz) ℓ hℓ
      have e : ℓ * z * ℓ⁻¹ = z := by rw [h1]; group
      rw [e]
      exact hZL hz
    exact Subgroup.le_centralizer_iff.mp hVc
  obtain ⟨u₀, hu₀, hu₀Z⟩ := Set.not_subset.mp hnot
  have hu₀1 : β ⟨u₀, hu₀.2⟩ ≠ 1 := by
    intro h1
    apply hu₀Z
    have h2 : (⟨u₀, hu₀.2⟩ : ↥(blockU L)) = 1 := β.injective (h1.trans (map_one β).symm)
    rw [show u₀ = 1 from congrArg Subtype.val h2]
    exact (blockZ L).one_mem
  have hθb : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u : ↥(blockU L)),
      β ⟨g * u * g⁻¹, Mod32.conj_mem_blockU g.2 u⟩ = ρ g (β u) :=
    fun g u => hβe g u ⟨g * u * g⁻¹, Mod32.conj_mem_blockU g.2 u⟩ rfl
  have hTZ : T ≤ Subgroup.centralizer (Z : Set G) :=
    CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T
  have hfixZ : ∀ u : ↥(blockU L), (u : G) ∈ Z →
      β u = 1 ∨ β u = w0 ∨ β u = hom w0 ∨ β u = hom (hom w0) := by
    intro u huZ
    apply hfix
    intro t ht
    rw [← hθb ⟨t, hTL ht⟩ u]
    congr 1
    apply Subtype.ext
    show t * u * t⁻¹ = u
    have h1 := Subgroup.mem_centralizer_iff.mp (hTZ ht) u huZ
    rw [← h1]
    group
  have hle : L ⊓ Subgroup.centralizer (Z : Set G) ≤ pre ρ hLTN P0 := by
    intro y ⟨hyL, hyZ⟩
    refine (mem_pre ρ hLTN).mpr ⟨Subgroup.mem_sup_left hyL, ?_⟩
    have hfy : ρ ⟨y, hLTN (Subgroup.mem_sup_left hyL)⟩ (β ⟨u₀, hu₀.2⟩) = β ⟨u₀, hu₀.2⟩ := by
      rw [← hθb ⟨y, hLTN (Subgroup.mem_sup_left hyL)⟩ ⟨u₀, hu₀.2⟩]
      congr 1
      apply Subtype.ext
      show y * u₀ * y⁻¹ = u₀
      have h1 := Subgroup.mem_centralizer_iff.mp hyZ u₀ hu₀.1
      rw [← h1]
      group
    have hyG : ρ ⟨y, hLTN (Subgroup.mem_sup_left hyL)⟩ ∈ Gam0 := hρL y hyL
    have hw : ρ ⟨y, hLTN (Subgroup.mem_sup_left hyL)⟩ w0 = w0 := by
      rcases hfixZ ⟨u₀, hu₀.2⟩ hu₀.1 with h0 | h0 | h0 | h0
      · exact absurd h0 hu₀1
      · rwa [h0] at hfy
      · refine fix_w0_of_fix hyG (k := 1) ?_
        rw [pow_one]
        rwa [h0] at hfy
      · refine fix_w0_of_fix hyG (k := 2) ?_
        rw [pow_two, MulAut.mul_apply]
        rwa [h0] at hfy
    rw [← inf_stab0_eq hG]
    exact ⟨hρN _, hw⟩
  have hodd : ∀ y ∈ pre ρ hLTN P0, Odd (orderOf y) →
      y ∈ L ⊓ Subgroup.centralizer (Z : Set G) := by
    intro y hy ho
    obtain ⟨hyLT, hyp⟩ := (mem_pre ρ hLTN).mp hy
    have hyL : y ∈ L := CZCore.mem_of_odd hTL hT2 hyLT ho
    refine ⟨hyL, hcentZ y hyL fun u hu => ?_⟩
    have hyG : ρ ⟨y, hLTN hyLT⟩ ∈ Gam0 := hρL y hyL
    have hyw : ρ ⟨y, hLTN hyLT⟩ w0 = w0 := P0_le_stab0 hyp
    have hfixw : ρ ⟨y, hLTN hyLT⟩ (β ⟨u, hu.2⟩) = β ⟨u, hu.2⟩ := by
      rcases hfixZ ⟨u, hu.2⟩ hu.1 with h0 | h0 | h0 | h0 <;> rw [h0]
      · exact map_one _
      · exact hyw
      · have h1 := fix_line hyG hyw 1
        rwa [pow_one] at h1
      · have h1 := fix_line hyG hyw 2
        rwa [pow_two, MulAut.mul_apply] at h1
    have hβeq : β ⟨y * u * y⁻¹, Mod32.conj_mem_blockU (hLTN hyLT) ⟨u, hu.2⟩⟩ = β ⟨u, hu.2⟩ :=
      (hθb ⟨y, hLTN hyLT⟩ ⟨u, hu.2⟩).trans hfixw
    have h1 : y * u * y⁻¹ = u := congrArg Subtype.val (β.injective hβeq)
    calc u * y = (y * u * y⁻¹) * y := by rw [h1]
      _ = y * u := by group
  refine le_antisymm (oTwoUpper_mono hle) ?_
  rw [oTwoUpper, Subgroup.closure_le]
  rintro x ⟨hx, ho⟩
  exact mem_oTwoUpper_of_odd (hodd x hx ho) ho

theorem parabolic_of_rho [Finite G] {T M L D : Subgroup G} (h : Hyp331 G T M L D)
    (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* MulAut W6) (hρN : ∀ g, ρ g ∈ Nor0)
    (hρL' : ∀ x ∈ Gam0, ∃ ℓ, ∃ hℓ : ℓ ∈ L, ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = x)
    (hρT : ∀ t (ht : t ∈ T), ρ ⟨t, hTL ht⟩ ∈ S0)
    (hK : ∀ g, g ∈ L ⊔ T → ∀ hgN : g ∈ Subgroup.normalizer (L : Set G), ρ ⟨g, hgN⟩ = 1 →
      g ∈ qL L T) :
    oTwoUpper (pre ρ (sup_le Subgroup.le_normalizer hTL) P0) ⊔ T =
        pre ρ (sup_le Subgroup.le_normalizer hTL) P0 ∧
      Nonempty (↥(pre ρ (sup_le Subgroup.le_normalizer hTL) P0) ⧸
        CFSG.pCore 2 ↥(pre ρ (sup_le Subgroup.le_normalizer hTL) P0) ≃* Equiv.Perm (Fin 3)) ∧
      pCoreOf 2 (pre ρ (sup_le Subgroup.le_normalizer hTL) P0) =
        pre ρ (sup_le Subgroup.le_normalizer hTL) R0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := h.toSetup331.isSylowTwoOf.2.1
  have hTidx : ¬ 2 ∣ T.index := h.sylow.2
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have : Finite (MulAut W6) :=
    Finite.of_injective (fun f : MulAut W6 => (f : W6 → W6)) DFunLike.coe_injective
  set R := (ρ.comp (Subgroup.inclusion hLTN)).range with hR
  have hGR : Gam0 ≤ R := by
    intro x hx
    obtain ⟨ℓ, hℓ, e⟩ := hρL' x hx
    exact ⟨⟨ℓ, Subgroup.mem_sup_left hℓ⟩, e⟩
  have hRN : R ≤ Nor0 := by
    rintro _ ⟨g, rfl⟩
    exact hρN _
  have h6 := card_inf_P0 (eq_or_eq_of_le hGR hRN)
  obtain ⟨x, hxG, y, hyG, hxP, hyP, hxy⟩ := exists_pair
  obtain ⟨ℓa, hℓa, ea⟩ := hρL' x hxG
  obtain ⟨ℓb, hℓb, eb⟩ := hρL' y hyG
  exact G2XS3.parabolic_gen' ρ hLTN hT2 hTidx (fun g hg h1 => hK g hg (hLTN hg) h1)
    (p := P0) (r := R0) (fun t ht => S0_le_P0 (hρT t ht)) R0_le_P0 P0_le_normalizer
    isPGroup_R0 (Or.inl h6) hℓa hℓb
    (by
      show ρ ⟨ℓa, Subgroup.le_normalizer hℓa⟩ ∈ P0
      rw [ea]
      exact hxP)
    (by
      show ρ ⟨ℓb, Subgroup.le_normalizer hℓb⟩ ∈ P0
      rw [eb]
      exact hyP)
    (by
      show (ρ ⟨ℓb, Subgroup.le_normalizer hℓb⟩ * ρ ⟨ℓa, Subgroup.le_normalizer hℓa⟩)⁻¹ *
        (ρ ⟨ℓa, Subgroup.le_normalizer hℓa⟩ * ρ ⟨ℓb, Subgroup.le_normalizer hℓb⟩) ∉ R0
      rw [ea, eb]
      exact hxy)

theorem fact3_3_25XS3Hat_of
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (hE : HatA6Embed) (hN : HatA6Normalizer) :
    CZA6.Fact3_3_25XS3Hat := by
  intro G _ _ T M L D h hTL hH
  obtain ⟨hG, ρ, β, hβe, hρN, hρL, hρL', hρT, -, hK⟩ := HatR.exists_rho hE hN h hTL hH
  have hX := cZ_eq h38 h39 h hTL hH hG ρ β hβe hρN hρL hρL' hρT
  obtain ⟨hXT, ⟨e⟩, -⟩ := parabolic_of_rho h hTL ρ hρN hρL' hρT hK
  exact nonempty_quot_pCore_congr (by rw [hX, hXT]) ⟨e⟩

end HatX

end CFSG.Quasithin.H13
