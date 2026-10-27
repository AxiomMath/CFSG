module

public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSpNsFrame
public import CFSG.LocalAnalysis.StandardType.GGNsFrameCompRest
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrame

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21 CFSG.LieType.Universal.Symplectic
  Matrix Polynomial CFSG.RankThree.PartOne CFSG.RankThree.Classical
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

namespace SevSpNs

section Frame

variable {F : Type} [Field F] {n e s r p : ℕ}
  {A₀ : GL (Fin n ⊕ Fin n) F} {ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r}
  {C : Matrix (Fin e) (Fin e) F}

theorem spBlockMat_one : RootPlaneSp.SpBlockMat A₀ ε C (1 : StatedSp n F) 0 := by
  have h : mat n F (1 : StatedSp n F) =
      SpNonsplitComp.frameRing A₀ ε (SLNS.nsCore (r := r) C 0) := by
    rw [map_one, SLNS.nsCore_zero, map_one]
  exact h

theorem spBlockMat_mul {X Y : StatedSp n F} {k k' : Fin s → ℕ}
    (hX : RootPlaneSp.SpBlockMat A₀ ε C X k) (hY : RootPlaneSp.SpBlockMat A₀ ε C Y k') :
    RootPlaneSp.SpBlockMat A₀ ε C (X * Y) (k + k') := by
  have h : mat n F (X * Y) = SpNonsplitComp.frameRing A₀ ε (SLNS.nsCore C (k + k')) := by
    rw [map_mul, SpNonsplitComp.mat_eq_of_spBlockMat hX, SpNonsplitComp.mat_eq_of_spBlockMat hY,
      ← map_mul, SLNS.nsCore_mul]
  exact h

theorem spBlockMat_pow {X : StatedSp n F} {k : Fin s → ℕ}
    (hX : RootPlaneSp.SpBlockMat A₀ ε C X k) (m : ℕ) :
    RootPlaneSp.SpBlockMat A₀ ε C (X ^ m) (m • k) := by
  induction m with
  | zero =>
    rw [pow_zero, zero_smul]
    exact spBlockMat_one
  | succ m ih =>
    rw [pow_succ, succ_nsmul]
    exact spBlockMat_mul ih hX

theorem eq_one_of_spBlockMat (hCp : C ^ p = 1) {X : StatedSp n F} {k : Fin s → ℕ}
    (hX : RootPlaneSp.SpBlockMat A₀ ε C X k) (hk : ∀ i, p ∣ k i) : X = 1 := by
  apply mat_injective
  rw [SpNonsplitComp.mat_eq_of_spBlockMat hX,
    NoOffPSLRest.nsCore_congr hCp (k' := 0) fun i => by
      rw [Pi.zero_apply, Nat.zero_mod]
      exact Nat.mod_eq_zero_of_dvd (hk i),
    SLNS.nsCore_zero, map_one, map_one]

end Frame

section Witness

theorem witness_psp_nonsplit {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {n f : ℕ} {ψ : StatedSp n (GaloisField 2 f) →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (Symplectic.rootDatum n (GaloisField 2 f)) .PSp n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hns : ¬ p ∣ 2 ^ f - 1) {b : G} (hb : b ∈ Bs)
    (hb1 : b ≠ 1) {L₁ : Subgroup G}
    (hL₁ : IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}))
    (hpL : p ∣ Nat.card L₁) :
    ∃ e ∈ L₁, GGSixSeventeenDirect p Bs D (ggG0 p B x L D J) e := by
  classical
  have hrk : 2 ≤ n := hctx.2.2.2.1.2
  have : NeZero n := ⟨by omega⟩
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hker : ψ.ker ≤ Subgroup.center (StatedSp n (GaloisField 2 f)) := hctx.2.2.2.2.1.2
  have hpp := hctx.prime
  have hp2 := hctx.ne_two
  have : NeZero p := ⟨hpp.ne_zero⟩
  have : Fact p.Prime := ⟨hpp⟩
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hz : a ∈ Subgroup.center (StatedSp n (GaloisField 2 f)) := hker ha
    rw [AutPSp.center_eq_bot] at hz
    exact Subgroup.mem_bot.mp hz
  have hG₀ : ψ.range = ggG0 p B x L D J := hctx.range_eq
  have hBs := hctx.bstar
  have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.sstar.1.2.1
  have hBBs : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hBs.1
  have hr4 : 4 ≤ LargeEvenTwoLocalRank p G := hctx.beta.2.2.2
  have hcard : p ^ 4 ≤ Nat.card Bs :=
    calc p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hpp.pos hr4
      _ = Nat.card B := hBcard.symm
      _ ≤ Nat.card Bs := hBBs
  obtain ⟨e, s, r, C, ε, A₀, hCp, hcunit, hreal, hframe⟩ :=
    ggSpNonsplitFrameInput_holds G p B Bs x L D J n f ψ hctx s1.1 hns
  have hcongr : ∀ {b : G} {k k' : Fin s → ℕ}, NoOffPSLRest.SpFrameRep ψ A₀ ε C b k →
      (∀ i, k i % p = k' i % p) → NoOffPSLRest.SpFrameRep ψ A₀ ε C b k' := by
    rintro b k k' ⟨X, hX1, hX2⟩ hkk
    exact ⟨X, hX1, by rw [hX2, NoOffPSLRest.nsCore_congr hCp hkk]⟩
  have he0 : e ≠ 0 := by
    intro he0
    have hsub : Bs ≤ ⊥ := fun b hb => by
      obtain ⟨k, X, rfl, hX⟩ := hframe b hb
      have hX1 : X = 1 := by
        apply Subtype.ext
        apply Units.ext
        rw [hX, NoOffPSLRest.nsCore_eq_one_of_e_zero he0, Matrix.submatrix_one_equiv,
          Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
        rfl
      rw [hX1, map_one]
      exact Subgroup.one_mem _
    have h1 : Nat.card Bs ≤ 1 := by
      have := Subgroup.card_le_of_le hsub
      rwa [Subgroup.card_bot] at this
    have := Nat.one_lt_pow (by norm_num : 4 ≠ 0) hpp.one_lt
    omega
  have he2 : 2 ≤ e := by
    by_contra he
    obtain rfl : e = 1 := by omega
    have hu := hcunit 1 (Nat.Prime.not_dvd_one hpp) (C 0 0)
    have h0 : C ^ 1 - C 0 0 • (1 : Matrix (Fin 1) (Fin 1) (GaloisField 2 f)) = 0 := by
      ext a b
      rw [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]
      simp
    rw [h0] at hu
    exact not_isUnit_zero hu
  have hinjBs : Function.Injective (fun b : Bs => fun i : Fin s =>
      ((NoOffPSLRest.spExp ψ A₀ ε C b i : ℕ) : ZMod p)) := by
    intro b b' hbb
    have hb := NoOffPSLRest.spExp_spec (hframe b b.2)
    have hb' := NoOffPSLRest.spExp_spec (hframe b' b'.2)
    have hmod : ∀ i, NoOffPSLRest.spExp ψ A₀ ε C b' i % p =
        NoOffPSLRest.spExp ψ A₀ ε C b i % p := by
      intro i
      have := congrFun hbb i
      simp only at this
      rw [ZMod.natCast_eq_natCast_iff'] at this
      exact this.symm
    exact Subtype.ext (hb.eq (hcongr hb' hmod))
  have hBsle : Nat.card Bs ≤ p ^ s := by
    calc Nat.card Bs ≤ Nat.card (Fin s → ZMod p) := Nat.card_le_card_of_injective _ hinjBs
      _ = p ^ s := by rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin s),
          Fintype.card_fin]
  have hs4 : 4 ≤ s := (Nat.pow_le_pow_iff_right hpp.one_lt).mp (hcard.trans hBsle)
  have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hnsF : ¬ p ∣ Nat.card (GaloisField 2 f) - 1 := by
    rw [hcardF]
    exact hns
  have hrealX : ∀ k : Fin s → ℕ, ∃ X : StatedSp n (GaloisField 2 f),
      RootPlaneSp.SpBlockMat A₀ ε C X k := by
    intro k
    obtain ⟨b, -, X, -, hX⟩ := hreal k
    exact ⟨X, hX⟩
  have hmemBs : ∀ {X : StatedSp n (GaloisField 2 f)} {k : Fin s → ℕ},
      RootPlaneSp.SpBlockMat A₀ ε C X k → ψ X ∈ Bs := by
    intro X k hX
    obtain ⟨b', hb', hb'k⟩ := hreal k
    rw [hb'k.eq ⟨X, rfl, hX⟩] at hb'
    exact hb'
  have hfin : ∀ {z : StatedSp n (GaloisField 2 f)} {k : Fin s → ℕ},
      RootPlaneSp.SpBlockMat A₀ ε C z k → z ≠ 1 → ψ z ∈ L₁ → ∀ {j j' : Fin s}, j ≠ j' →
        (∀ i, i ≠ j → i ≠ j' → p ∣ k i) →
        ∃ e ∈ L₁, GGSixSeventeenDirect p Bs D (ggG0 p B x L D J) e := by
    intro z k hz hz1 hzL j j' hjj hk
    obtain ⟨L₂, hL₂, hL₂c⟩ := direct_of_two_supp hpp hp2 hnsF he2 hs4 hCp hcunit hrealX hψ
      (fun b hb => hframe b hb) hz hz1 hjj hk
    refine ⟨ψ z, hzL, hmemBs hz, fun h => hz1 (hψ (h.trans (map_one ψ).symm)), Or.inr ⟨L₂, ?_,
      hL₂c⟩⟩
    rwa [← hG₀]
  obtain ⟨β, x₀, hbx, hx₀⟩ := hframe b hb
  subst hbx
  have hx₀p : x₀ ^ p = 1 := SpNonsplitComp.pow_p_eq_one hCp hx₀
  have hx₀1 : x₀ ≠ 1 := fun h => hb1 (by rw [h, map_one])
  have hx₀o : orderOf x₀ = p := orderOf_eq_prime hx₀p hx₀1
  have hinj : Function.Injective (proj n (GaloisField 2 f)) := by
    rw [← MonoidHom.ker_eq_bot_iff, CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.ker_proj]
    exact le_antisymm
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars_le_center.trans
        AutPSp.center_eq_bot.le) bot_le
  have hxop : orderOf (proj n (GaloisField 2 f) x₀) = p := by
    rw [orderOf_injective _ hinj x₀, hx₀o]
  have blocks := ((symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two hf hcardF hpp
    hp2 hp2 (by omega) _ hxop).2) x₀ rfl hx₀o
  have hmapC : (Subgroup.centralizer ({x₀} : Set (StatedSp n (GaloisField 2 f)))).map ψ =
      ggG0 p B x L D J ⊓ Subgroup.centralizer {ψ x₀} := by
    rw [← hG₀]
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_inf, MonoidHom.mem_range,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, rfl⟩, by rw [← map_mul, ← map_mul, hy]⟩
    · rintro ⟨⟨y, rfl⟩, hy⟩
      exact ⟨y, hψ (by rw [map_mul, map_mul]; exact hy), rfl⟩
  rw [← hmapC] at hL₁
  obtain ⟨hL₁', hmapL⟩ := isComponentOf_comap_of_injective ψ hψ hL₁
  obtain ⟨hn, O, hLO, hab⟩ :=
    exists_spSupported_of_isComponentOf hcardF hf hpp hp2 hx₀p blocks hL₁'
  have hAp : IsPGroup p (Bs.comap ψ) := fun a => ⟨1, Subtype.ext (hψ (by
      rw [pow_one, Subgroup.coe_pow, map_pow, Subgroup.coe_one, map_one]
      exact hBs.2.1.2 _ a.2))⟩
  have hAC : ∀ a ∈ Bs.comap ψ,
      a ∈ Subgroup.centralizer ({x₀} : Set (StatedSp n (GaloisField 2 f))) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hψ
    rw [map_mul, map_mul]
    exact TableB.IsElemAbelian.comm hBs.2.1 ha hb
  have hpL' : p ∣ Nat.card (L₁.comap ψ) := by
    rwa [← hmapL, Subgroup.card_map_of_injective hψ] at hpL
  obtain ⟨w, hwL, hw1, hwp, hwc⟩ := exists_mem_inf_centralizer hpp hAp
    (fun a ha l hl => hn a (hAC a ha) l hl) hpL'
  have hwB : ψ w ∈ Bs := by
    refine hBs.2.2.2 _ (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
      (by rw [← map_pow, hwp, map_one])
    obtain ⟨k, Y, hyY, -⟩ := hframe y hy
    subst hyY
    rw [← map_mul, ← map_mul, hwc Y hy]
  obtain ⟨κ, W, hW1, hW⟩ := hframe _ hwB
  obtain rfl : W = w := hψ hW1.symm
  obtain ⟨j, hj⟩ : ∃ j, ¬ p ∣ κ j := by
    by_contra hall
    push Not at hall
    exact hw1 (eq_one_of_spBlockMat hCp hW hall)
  have hwL₁ : ψ W ∈ L₁ := hmapL ▸ Subgroup.mem_map_of_mem ψ hwL
  by_cases hj' : ∃ j', j' ≠ j ∧ ¬ p ∣ κ j'
  · obtain ⟨j', hjj', hj'⟩ := hj'
    obtain ⟨u, hu⟩ := hrealX (Pi.single j 1)
    obtain ⟨v, hv⟩ := hrealX (Pi.single j' 1)
    have hfac : ∀ {X : StatedSp n (GaloisField 2 f)} {i₀ : Fin s}, ¬ p ∣ κ i₀ →
        RootPlaneSp.SpBlockMat A₀ ε C X (Pi.single i₀ 1) → X ∈ spSupported x₀ O := by
      intro X i₀ hi₀ hX
      refine mem_spSupported_of_fix (hLO hwL) (SpNonsplitComp.commute_of_spBlockMat hX hx₀)
        fun v hv => fix_of_supp hpp hp2 hCp hcunit hW hX (fun i hi => ?_) hv
      by_cases hii : i = i₀
      · subst hii
        exact absurd hi hi₀
      · rw [Pi.single_eq_of_ne hii]
        exact dvd_zero p
    obtain ⟨a, c, ha, hc, hac, hmem⟩ := hab u (hfac hj hu) v (hfac hj' hv)
      (SpNonsplitComp.pow_p_eq_one hCp hu) (SpNonsplitComp.pow_p_eq_one hCp hv)
    have hz := spBlockMat_mul (spBlockMat_pow hu a) (spBlockMat_pow hv c)
    refine hfin hz (fun h1 => ?_) (hmapL ▸ Subgroup.mem_map_of_mem ψ hmem) hjj'.symm
      fun i hi hi' => ?_
    · have hmod := fun i => NoOffPSLRest.SpFrameRep.mod_eq hψ he0 hpp.pos hCp hcunit
        ⟨_, rfl, hz⟩ ⟨1, by rw [h1], spBlockMat_one⟩ i
      have h1j := hmod j
      have h1j' := hmod j'
      simp [hjj', Ne.symm hjj'] at h1j h1j'
      rw [Nat.mod_eq_of_lt ha] at h1j
      rw [Nat.mod_eq_of_lt hc] at h1j'
      omega
    · simp [hi, hi']
  · push Not at hj'
    have : Nontrivial (Fin s) := Fin.nontrivial_iff_two_le.mpr (by omega)
    obtain ⟨j'', hj''⟩ := exists_ne j
    exact hfin hW hw1 hwL₁ (Ne.symm hj'') fun i hi _ => hj' i hi

end Witness

end SevSpNs

section Inputs

theorem ggSixSeventeenWitnessDvdOn_PSpNonsplit : GGSixSeventeenWitnessDvdOn GGPSpNonsplit := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx s1 b L₁ hpair hpL
  obtain ⟨rfl, hns⟩ := hP
  obtain ⟨hb, hb1, hcomp, -⟩ := hpair
  obtain ⟨e, he, hdir⟩ := SevSpNs.witness_psp_nonsplit (ψ := ψ) hctx s1 hns hb hb1 hcomp hpL
  exact Or.inr ⟨e, he, Or.inl hdir⟩

@[expose] def GGSixSeventeenWitnessRest10 : Prop :=
  GGSixSeventeenWitnessDvdOn (fun t _ _ _ => t = .POmegaPlus) ∧
    GGSixSeventeenWitnessDvdOn (fun t _ _ _ => t = .POmegaMinus) ∧
    GGSixSeventeenE8SevenInput ∧ GGSixSeventeenRootWitnessInputFor GGExceptionalTag

theorem ggSixSeventeenWitnessRest10_of_rest9 (h : GGSixSeventeenWitnessRest9) :
    GGSixSeventeenWitnessRest10 :=
  h.2

theorem ggSixSeventeenWitnessRest9_of_rest10 (h : GGSixSeventeenWitnessRest10) :
    GGSixSeventeenWitnessRest9 :=
  ⟨ggSixSeventeenWitnessDvdOn_PSpNonsplit, h⟩

end Inputs

section Wiring

theorem ggSixSeventeenWitnessOn_PSpNonsplit : GGSixSeventeenWitnessOn GGPSpNonsplit :=
  ggSixSeventeenWitnessOn_of_dvdOn (by
    rintro t n f p ⟨rfl, -⟩
    exact ⟨ggNonsplitTag_PSp_holds, ggLayerPDivTag_PSp⟩) ggSixSeventeenWitnessDvdOn_PSpNonsplit

theorem ggSixSeventeenWitnessRest7_of_rest10 (hPl : GGNonsplitTag .POmegaPlus)
    (hMi : GGNonsplitTag .POmegaMinus) (h : GGSixSeventeenWitnessRest10) :
    GGSixSeventeenWitnessRest7 :=
  ggSixSeventeenWitnessRest7_of_rest9 hPl hMi (ggSixSeventeenWitnessRest9_of_rest10 h)

theorem ggSixSeventeenWitnessInput_of_rest10 (hPl : GGNonsplitTag .POmegaPlus)
    (hMi : GGNonsplitTag .POmegaMinus) (h : GGSixSeventeenWitnessRest10) :
    GGSixSeventeenWitnessInputFor fun _ => True :=
  ggSixSeventeenWitnessInput_of_rest9 hPl hMi (ggSixSeventeenWitnessRest9_of_rest10 h)

end Wiring

end CFSG.StandardType
