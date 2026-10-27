module

public import CFSG.Quasithin.H13.U3S13472D
public import CFSG.Quasithin.Background.B5Part3

public section

namespace CFSG.Quasithin.H13.U3.P2

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
variable {S : A6.Setting134 G T L V} {H₁ H₂ : Subgroup G}

@[expose] def g4 : SL3.S := ⟨!![1, 1, 0; 0, 1, 1; 0, 0, 1], by decide +kernel⟩

theorem g4_pow : g4 ^ 4 = 1 ∧ g4 ^ 2 ≠ 1 := by decide +kernel

theorem ex_pow : SL3.ex ^ 2 = 1 ∧ SL3.ex ≠ 1 := by decide +kernel

theorem not_isPGroup_of_isQuasisimple {Q : Type*} [Group Q] [Finite Q]
    (hq : CFSG.IsQuasisimple Q) : ¬ IsPGroup 2 Q := by
  intro hp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial Q := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (by rw [Subsingleton.elim a b])
  have := hq.1
  exact Group.IsPerfect.not_isNilpotent Q hp.isNilpotent

omit [Finite G] in
theorem autOn_bot (W : Subgroup G) : autOn (⊥ : Subgroup G) W = ⊥ := by
  rw [autOn, Subgroup.bot_subgroupOf, Subgroup.map_bot]

omit [Finite G] in
theorem le_normalizer_bot (Y : Subgroup G) : Y ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
  intro g _
  rw [mem_normalizer_iff]
  intro h
  simp only [mem_bot]
  constructor
  · rintro rfl
    group
  · intro h1
    rw [mul_inv_eq_one, mul_eq_left] at h1
    exact h1

omit [Finite G] in
theorem conjAct_comm {W : Subgroup G} {g h : ↥(normalizer (W : Set G))}
    (hgh : (g : G) * h * (g : G)⁻¹ * (h : G)⁻¹ ∈ centralizer (W : Set G)) :
    conjAct W g * conjAct W h = conjAct W h * conjAct W g := by
  have h1 : conjAct W (g * h * g⁻¹ * h⁻¹) = 1 := by
    ext w
    rw [conjAct, MonoidHom.comp_apply, normalizerMonoidHom_apply_apply_coe, MulAut.one_apply]
    change ((g * h * g⁻¹ * h⁻¹ : ↥(normalizer (W : Set G))) : G) * w *
      ((g * h * g⁻¹ * h⁻¹ : ↥(normalizer (W : Set G))) : G)⁻¹ = w
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← mem_centralizer_iff.1 hgh w w.2, mul_inv_cancel_right]
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1

theorem false_of_not_B (h56 : AsB56) (D : Data2 S H₁ H₂) {X : Subgroup G} (hS : SettingX D X)
    {A : Subgroup G} (hA : IsElemAbelianCorank T 1 A)
    (hAC : ¬ A ≤ centralizer (v0Of T H₁ H₂ : Set G))
    (hB : ¬ (A ⊓ centralizer (v0Of T H₁ H₂ : Set G)) ⊔ v0Of T H₁ H₂ ≤
      centralizer (conjClosure (quasithinOmegaOneCenter T) X : Set G)) : False := by
  have hWc := hS.isMulCommutative
  have hred := hS.reduced
  set W := conjClosure (quasithinOmegaOneCenter T) X with hWdef
  have hWe : IsElemAbelian 2 W := hred.2.2.1
  have hW2 : ∀ w ∈ W, w ^ 2 = 1 := hWe.2
  have hV2 : ∀ v : ↥W, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hW2 v v.2)
  have hXW : X ≤ normalizer (W : Set G) := hred.2.1
  have hKW : D.K₀ ≤ normalizer (W : Set G) := hS.KX.trans hXW
  obtain ⟨e⟩ := hS.nonempty_equiv
  have hKs : IsSimpleGroup ↥(autOn D.K₀ W) := by
    have := HSType.isSimpleGroup_SL_three_two
    exact e.isSimpleGroup
  have hKcard : Nat.card ↥(autOn D.K₀ W) = 168 := by
    rw [Nat.card_congr e.toEquiv, SL3.card_S]
  obtain ⟨t, het⟩ : ∃ t, e t = SL3.ex := ⟨e.symm _, e.apply_symm_apply _⟩
  obtain ⟨t4, het4⟩ : ∃ t, e t = g4 := ⟨e.symm _, e.apply_symm_apply _⟩
  have hcoe : ∀ (k : ↥(autOn D.K₀ W)) (n : ℕ), (k : MulAut ↥W) ^ n = ((k ^ n : ↥(autOn D.K₀ W)) :
      MulAut ↥W) := fun k n => rfl
  have ht1 : (t : MulAut ↥W) ≠ 1 := fun h => ex_pow.2 (by
    rw [← het, show t = 1 from Subtype.ext h, map_one])
  have ht2 : (t : MulAut ↥W) ^ 2 = 1 := by
    rw [hcoe, show t ^ 2 = 1 from e.injective (by rw [map_pow, het, ex_pow.1, map_one])]
    rfl
  have ht44 : (t4 : MulAut ↥W) ^ 4 = 1 := by
    rw [hcoe, show t4 ^ 4 = 1 from e.injective (by rw [map_pow, het4, g4_pow.1, map_one])]
    rfl
  have ht42 : (t4 : MulAut ↥W) ^ 2 ≠ 1 := fun h => g4_pow.2 (by
    rw [← het4, ← map_pow, show t4 ^ 2 = 1 from Subtype.ext (by rw [← hcoe]; exact h), map_one])
  set Cent : Subgroup (MulAut ↥W) := centralizer ((autOn D.K₀ W : Subgroup (MulAut ↥W)) :
    Set (MulAut ↥W)) with hCent
  set Y : Subgroup G := X ⊓ (Cent.comap (conjAct W)).map (normalizer (W : Set G)).subtype
    with hYdef
  have hmemY : ∀ (g : G) (hgX : g ∈ X), conjAct W ⟨g, hXW hgX⟩ ∈ Cent → g ∈ Y :=
    fun g hgX hgC => ⟨hgX, ⟨⟨g, hXW hgX⟩, hgC, rfl⟩⟩
  have hYX : Y ≤ X := inf_le_left
  have hYW : Y ≤ normalizer (W : Set G) := hYX.trans hXW
  have hYC : autOn Y W ≤ Cent := by
    intro r hr
    obtain ⟨g, hgY, rfl⟩ := Setup.mem_autOn_iff.1 hr
    obtain ⟨-, g', hg', hgg'⟩ := hgY
    have : g' = g := Subtype.ext hgg'
    rw [← this]
    exact hg'
  have hKn := InternalSec.autOn_normal_of (U := W) hS.hNX
  have hconjC : ∀ a ∈ autOn X W, ∀ c ∈ Cent, a * c * a⁻¹ ∈ Cent := by
    intro a ha c hc
    rw [mem_centralizer_iff] at hc ⊢
    intro k hk
    have hk' : a⁻¹ * k * a⁻¹⁻¹ ∈ autOn D.K₀ W := hKn _ (inv_mem ha) k hk
    rw [inv_inv] at hk'
    have h1 := hc _ hk'
    calc k * (a * c * a⁻¹) = a * ((a⁻¹ * k * a) * c) * a⁻¹ := by group
      _ = a * (c * (a⁻¹ * k * a)) * a⁻¹ := by rw [h1]
      _ = a * c * a⁻¹ * k := by group
  have hYeq : ∀ r, r ∈ autOn Y W ↔ r ∈ autOn X W ∧ r ∈ Cent := by
    intro r
    refine ⟨fun hr => ⟨InternalSec.autOn_le_autOn_of_le hYX hr, hYC hr⟩, fun ⟨hr, hrC⟩ => ?_⟩
    obtain ⟨g, hgX, rfl⟩ := Setup.mem_autOn_iff.1 hr
    exact Setup.mem_autOn_iff.2 ⟨g, hmemY g hgX hrC, rfl⟩
  have hn : ((autOn Y W).subgroupOf (autOn X W)).Normal := by
    refine ⟨fun r hr a => ?_⟩
    rw [mem_subgroupOf] at hr ⊢
    have hr' := (hYeq _).1 hr
    rw [hYeq]
    exact ⟨mul_mem (mul_mem a.2 hr'.1) (inv_mem a.2), hconjC _ a.2 _ hr'.2⟩
  have hO2 : pCoreOf 2 (autOn Y W) = ⊥ := by
    have := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 _ _
      (InternalSec.autOn_le_autOn_of_le hYX) hn
    rw [Setup.pCoreOf_autOn_eq_bot hred] at this
    exact le_bot_iff.1 this
  have hO2Y : pCoreOf 2 X ≤ Y := by
    intro g hg
    have hgX := pCoreOf_le 2 X hg
    refine hmemY g hgX ?_
    have h1 : SettingX.conjOn X W hXW ⟨g, hgX⟩ = 1 :=
      MonoidHom.mem_ker.1 ((SettingX.mem_ker_conjOn hXW ⟨g, hgX⟩).2
        (hS.pCoreOf_le_centralizer hg))
    change SettingX.conjOn X W hXW ⟨g, hgX⟩ ∈ Cent
    rw [h1]
    exact one_mem _
  have hO2le : pCoreOf 2 X ≤ pCoreOf 2 Y :=
    QuasithinUnique.le_pCoreOf_of_le_normalizer hO2Y (hYX.trans (le_normalizer_pCoreOf 2 X))
      (pCoreOf_isPGroup 2 X)
  have hSY : SQTKGroup ↥Y :=
    sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian fun h =>
      hS.hX.2 (le_bot_iff.1 (h ▸ hO2le))
  have hQ0 : T ⊓ centralizer (v0Of T H₁ H₂ : Set G) = pCoreOf 2 (H₁ ⊔ H₂) :=
    s1347_T_inf_centralizer S D.hyp D.hH₀
  have hV0C : v0Of T H₁ H₂ ≤ centralizer (v0Of T H₁ H₂ : Set G) := fun v hv =>
    mem_centralizer_iff.2 fun w hw => congrArg Subtype.val
      (D.isMulCommutative.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)
  have hBQ : (A ⊓ centralizer (v0Of T H₁ H₂ : Set G)) ⊔ v0Of T H₁ H₂ ≤
      pCoreOf 2 (H₁ ⊔ H₂) :=
    hQ0 ▸ sup_le (inf_le_inf_right _ hA.1) (le_inf (s1347_V0_le_T S D.hH₀) hV0C)
  have hKQ : pCoreOf 2 (H₁ ⊔ H₂) ⊓ D.K₀ ≤ pCoreOf 2 D.K₀ :=
    QuasithinUnique.le_pCoreOf_of_le_normalizer inf_le_right
      (fun k hk => mem_normalizer_inf_of (le_normalizer_pCoreOf 2 (H₁ ⊔ H₂) (D.KH hk))
        (Subgroup.le_normalizer hk))
      ((pCoreOf_isPGroup 2 (H₁ ⊔ H₂)).to_le inf_le_left)
  have hQY : pCoreOf 2 (H₁ ⊔ H₂) ≤ Y := by
    intro q hq
    have hqX : q ∈ X := hS.hX.1 (pCoreOf_le 2 _ hq)
    refine hmemY q hqX ?_
    rw [mem_centralizer_iff]
    intro r hr
    obtain ⟨k, hk, rfl⟩ := Setup.mem_autOn_iff.1 hr
    refine (conjAct_comm (g := k) (h := ⟨q, hXW hqX⟩) ?_)
    have hc : (k : G) * q * (k : G)⁻¹ * q⁻¹ ∈ pCoreOf 2 (H₁ ⊔ H₂) ⊓ D.K₀ := by
      refine ⟨(pCoreOf 2 (H₁ ⊔ H₂)).mul_mem ((mem_normalizer_iff.1 (le_normalizer_pCoreOf 2
        (H₁ ⊔ H₂) (D.KH hk)) q).1 hq) ((pCoreOf 2 (H₁ ⊔ H₂)).inv_mem hq), ?_⟩
      have h1 := (mem_normalizer_iff.1 (D.hN (pCoreOf_le 2 _ hq)) (k : G)⁻¹).1 (inv_mem hk)
      have e : (k : G) * q * (k : G)⁻¹ * q⁻¹ = k * (q * (k : G)⁻¹ * q⁻¹) := by group
      rw [e]
      exact mul_mem hk h1
    exact hS.pCoreOf_le_centralizer ((pCoreOf_le_pCoreOf hS.KX hS.hNX) (hKQ hc))
  have hBY := hBQ.trans hQY
  have hBmax := isMaxElemAbelian_B D hA hAC
  have hoffX : IsFFStarOffender (autOn X W)
      (autOn ((A ⊓ centralizer (v0Of T H₁ H₂ : Set G)) ⊔ v0Of T H₁ H₂) W) :=
    offenderImages_isFFStarOffender hWe hred.1 hred.2.1
      ⟨_, ⟨isMaxElemAbelian_of_isSylowTwoOf hS.sylow hBmax, hB⟩, rfl⟩
  have hoff : IsFFStarOffender (autOn Y W)
      (autOn ((A ⊓ centralizer (v0Of T H₁ H₂ : Set G)) ⊔ v0Of T H₁ H₂) W) :=
    ⟨InternalSec.autOn_le_autOn_of_le hBY, hoffX.2⟩
  obtain ⟨-, -, hQ, hAJ, hcases⟩ := InternalSec.b56Cases_ffJ_autOn h56 hW2 hYW bot_le
    (le_normalizer_bot Y) hSY hO2 hoff (by rw [autOn_bot, commutator_bot_left])
  have hJY : ffJ (autOn Y W) ≤ autOn Y W := B6.ffJ_le _
  have hJX : ffJ (autOn Y W) ≤ autOn X W := hJY.trans (InternalSec.autOn_le_autOn_of_le hYX)
  have hJC : ∀ r ∈ ffJ (autOn Y W), ∀ k ∈ autOn D.K₀ W, r * k = k * r := fun r hr k hk =>
    (mem_centralizer_iff.1 (hYC (hJY hr)) k hk).symm
  have hBne := hoff.2.1
  have hfin : ∀ R ≤ ffJ (autOn Y W), (∀ k ∈ autOn D.K₀ W, ∀ u ∈ commV R, k u = u) →
      IsPGroup 2 ↥R := fun R hRJ htriv =>
    hS.isPGroup_of_fix (hRJ.trans hJX) fun r hr z hz =>
      fix_commV_of_triv (fun r hr k hk => hJC r (hRJ hr) k hk) htriv hr (hS.Z_mem_commV hz)
  rcases hcases with h1 | h2 | h3 | h4 | h5
  ·
    obtain ⟨hq, hB51, -⟩ := h1
    have hFJ : quasithinGenFitting (ffJ (autOn Y W)) ≤ ffJ (autOn Y W) :=
      quasithinGenFitting_le _
    have hFK : ∀ f ∈ quasithinGenFitting (ffJ (autOn Y W)), ∀ k ∈ autOn D.K₀ W,
        f * k = k * f := fun f hf => hJC f (hFJ hf)
    have hFX := hFJ.trans hJX
    have hcontr : (∀ k ∈ autOn D.K₀ W, ∀ u ∈ commV (quasithinGenFitting (ffJ (autOn Y W))),
        k u = u) → False := fun htriv =>
      not_isPGroup_of_isQuasisimple hq (hfin _ hFJ htriv)
    obtain ⟨-, hcase⟩ := hB51.1
    rcases hcase with hi | hii | ⟨n, hiii⟩ | hiv
    · exact hcontr (triv_of_irrPlus hV2 hFK hKs t.2 ht1 ht2 hi.1)
    · obtain ⟨-, n, K, hKf, hKfin, -, I, π, -, hsup, hreal, -, -⟩ := hii
      have hsup' : I 0 ⊔ I 1 = commV (quasithinGenFitting (ffJ (autOn Y W))) := by
        rw [← hsup]
        refine le_antisymm (sup_le (le_iSup I 0) (le_iSup I 1)) (iSup_le fun i => ?_)
        fin_cases i
        · exact le_sup_left
        · exact le_sup_right
      exact hcontr (triv_of_sum_two_irr hV2 hFK hKs t4.2 ht44 ht42 hsup'
        (B5.isIrr_of_realizes (by norm_num) (hreal 0))
        (B5.isIrr_of_realizes (by norm_num) (hreal 1)))
    · obtain ⟨-, hn, π, U₁, U₂, -, hreal, -⟩ := hiii
      have hinj := FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hreal
      exact hS.false_of_threeRank2 hFX hFK
        (FFC.ThreeRank2.of_injective π hinj (FFC.threeRank2_statedSL (by omega)))
    · obtain ⟨-, n, hn, k, hk1, -, I, π, -, -, -, hreal⟩ := hiv
      have hinj := FFC.injective_of_faithful_sec (FFModel.nat_faithful _) (hreal ⟨0, by omega⟩)
      exact hS.false_of_threeRank2 hFX hFK
        (FFC.ThreeRank2.of_injective π hinj (FFC.threeRank2_statedSL (by omega)))
  ·
    obtain ⟨-, -, hcard⟩ := h2
    have htriv := triv_of_card hJC hKs (by rw [hcard, hKcard]; decide)
    have hJle : ffJ (autOn Y W) ≤ pCoreOf 2 (ffJ (autOn Y W)) :=
      LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_rfl (Subgroup.le_normalizer)
        (hfin _ le_rfl htriv)
    rw [hQ] at hJle
    exact hBne (le_bot_iff.1 (hAJ.trans hJle))
  · exact hS.false_of_threeRank2 hJX hJC (FFC.threeRank2_of_case3 h3)
  · exact hS.false_of_threeRank2 hJX hJC (FFC.threeRank2_of_case4 h4)
  · exact hS.false_of_threeRank2 hJX hJC (FFC.threeRank2_of_case5 h5)

end CFSG.Quasithin.H13.U3.P2
