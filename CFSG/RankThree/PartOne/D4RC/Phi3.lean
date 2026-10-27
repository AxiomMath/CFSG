module

public import CFSG.RankThree.PartOne.D4RC.RootLong
public import CFSG.RankThree.PartOne.D4RC.CenterZ
public import CFSG.RankThree.PartOne.D4RC.Pencil
public import CFSG.RankThree.PartOne.D4RC.Gamma
public import CFSG.RankThree.PartOne.D4RC.Hyp
public import CFSG.RankThree.PartOne.D4RC.Dichotomy
public import CFSG.RankThree.PartOne.D4RC.Output
public import CFSG.RankThree.PartOne.D4RC.OutputARS
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.Sporadic.Th.Max3.Involutions
public import CFSG.Timmesfeld.ARSInputThm
public import Certificates.Certificate10089Base
public import Certificates.Certificate10091Base

public noncomputable section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley.TrialityFold CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.TwistedD4 CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ7
  CFSG.Timmesfeld.ARS CFSG.Open
open CFSG.RankThree.Classical2 (fixSubgroup unitarySet)

open CFSG.RankThree.PartOne.Census3 (IsoLie)

open scoped Matrix MatrixGroups Pointwise

set_option linter.unusedSectionVars false

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

section Card

variable {L k : Type} [Field L] [Field k] [Algebra k L]

theorem rc3_transvection_01 (c : L) :
    (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c :
      Matrix (Fin 3) (Fin 3) L) 0 1 = c := by
  simp [Matrix.SpecialLinearGroup.transvection, Matrix.transvection]

theorem rc3_rcaT12_injective (H' : SL(3, L)) : Function.Injective (rcaT12 (k := k) H') := by
  intro s t h
  change H' * _ * H'⁻¹ = H' * _ * H'⁻¹ at h
  have h1 := mul_left_cancel (mul_right_cancel h)
  have h2 := congrArg (fun X : SL(3, L) => (X : Matrix (Fin 3) (Fin 3) L) 0 1) h1
  simp only [rc3_transvection_01] at h2
  exact Multiplicative.toAdd.injective ((algebraMap k L).injective h2)

end Card

section Phi3

variable {ℓ f : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {ε : ℤ}
  {p : ℕ} {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

theorem rc3_card_rcaA0 {F : RclFrame ℓ f K σ ε p L} {x : 𝒞[K, σ]} {i : Fin 4}
    (sp : RclSpecial F x i) (D : RclAlgData F i) :
    Nat.card (rcaA0 sp D) = Nat.card (fixSubfield σ) := by
  rw [rcq_rcaA0_eq_map, Subgroup.card_map_of_injective (rcqTheta_injective sp D),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (rcq_le_fix D)).toEquiv, rclA0AlgOf_eq_range,
    ← Nat.card_congr
      (MonoidHom.ofInjective (rc3_rcaT12_injective (k := fixSubfield σ) D.H')).toEquiv]
  exact Nat.card_congr Multiplicative.toAdd

end Phi3

section Gamma

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {p : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2]

theorem rc3_gamma_eq_top (hσ3 : ∀ c, σ (σ (σ c)) = c)
    [Finite (twistedGroup σ.toRingHom)] [IsSimpleGroup (twistedGroup σ.toRingHom)]
    (hT : Nat.card (twistedGroup σ.toRingHom) = ordTrialityD4 (2 ^ f))
    (e : 𝒞[K, σ] ≃* twistedGroup σ.toRingHom)
    (hcompat : ∀ k, (((e k : twistedGroup σ.toRingHom) : adjointGroup d4 K) : ModGL d4 K) =
      ((k : 𝒞[K, σ]) : ModGL d4 K))
    {F : RclFrame 2 f K σ 1 p L} {S : Sylow p 𝒞[K, σ]} {c : 𝒞[K, σ]} {E : Subgroup 𝒞[K, σ]}
    (Ln : RceLines F S c E) : rcgGamma Ln = ⊤ := by
  classical
  have hp : p.Prime := F.hp
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    have h3 := F.hp3
    by_contra h
    have h4 : p = 4 := by omega
    rw [h4] at hp
    exact absurd hp (by decide)
  obtain ⟨D₀⟩ := rcl_exists_algData F 0
  have hσ' : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c := hσ3
  have hHyp := rcg_hyp (σ := σ.toRingHom) hσ'
  have hR := hHyp.root
  have hH := rcg_sigmaEqLambda (σ := σ.toRingHom) hσ'
  set Γ := rcgGamma Ln with hΓ
  set A₀ := rcaA0 (Ln.sp 0) D₀ with hA₀
  set ΓT := Γ.map e.toMonoidHom with hΓT
  set A₀T := A₀.map e.toMonoidHom with hA₀T
  have hA₀R : A₀T ∈ longClass σ.toRingHom := rcb_map_mem_longClass hσ3 e hcompat (Ln.sp 0) D₀
  have hA₀Γ : A₀T ≤ ΓT := Subgroup.map_mono ((rcaA0_le _ D₀).trans (rcg_le_gamma Ln 0))
  obtain ⟨g₁, hg₁, g₂, hg₂, hc1, hc2, hnc⟩ := rcq_pencil (Ln.sp 0) D₀ rfl
  have hconjT : ∀ g, conjSub A₀T (e g) = (conjSub A₀ g).map e.toMonoidHom := fun g =>
    rcm_conjSub_map e.toMonoidHom A₀ g
  set A₁T := conjSub A₀T (e g₁) with hA₁T
  set A₂T := conjSub A₀T (e g₂) with hA₂T
  have hA₁ : A₁T ∈ rccOrbit ΓT A₀T :=
    ⟨e g₁, Subgroup.mem_map_of_mem _ (rcg_le_gamma Ln 0 hg₁), rfl⟩
  have hA₂ : A₂T ∈ rccOrbit ΓT A₀T :=
    ⟨e g₂, Subgroup.mem_map_of_mem _ (rcg_le_gamma Ln 0 hg₂), rfl⟩
  have hA₁R : A₁T ∈ longClass σ.toRingHom := rcg_conjSub_mem hA₀R _
  have hA₂R : A₂T ∈ longClass σ.toRingHom := rcg_conjSub_mem hA₀R _
  have hc1T : Commuting A₀T A₁T := by
    rw [hA₁T, hconjT]
    exact rcm_commuting_map _ hc1
  have hc2T : Commuting A₀T A₂T := by
    rw [hA₂T, hconjT]
    exact rcm_commuting_map _ hc2
  have hncT : ¬ Commuting A₁T A₂T := by
    rw [hA₁T, hA₂T, hconjT, hconjT, rcm_commuting_map_iff e.injective]
    exact hnc
  have hsymm : ∀ {A B : Subgroup (twistedGroup σ.toRingHom)}, Commuting A B → Commuting B A :=
    fun h a ha b hb => (h b hb a ha).symm
  have hne₁ : A₁T ≠ A₀T := fun h => hncT (h ▸ hc2T)
  have hne₂ : A₂T ≠ A₀T := fun h => hncT (hsymm (h ▸ hc1T))
  have h₁ := CaseH.mem_lambdaSet_of_commuting hH hA₀R hA₁R hne₁ hc1T
  have h₂ := CaseH.mem_lambdaSet_of_commuting hH hA₀R hA₂R hne₂ hc2T
  have hab : ∀ A ∈ longClass σ.toRingHom, ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a :=
    fun A hA => rcm_comm_of_mul_self (rcg_mul_self hσ' hA)
  have hnot : ¬ A₂T ≤ A₀T ⊔ A₁T := fun hle => hncT fun a ha b hb =>
    rcm_comm_sup (hab _ hA₀R) (hab _ hA₁R) hc1T a (le_sup_right (a := A₀T) ha) b (hle hb)
  have hsub : rccOrbit ΓT A₀T ⊆ longClass σ.toRingHom := rccOrbit_subset hR hA₀R
  have hgen : ⨆ A ∈ rccOrbit ΓT A₀T, A = ΓT := by
    rw [rcm_iSup_orbit_map, rcg_iSup_orbit]
  have hcenter : Subgroup.center ↥ΓT = ⊥ :=
    rcm_center_map e (rcz_center Ln (j := 1) (by decide) (rcg_E_le Ln) (rcg_le_gamma Ln 0)
      (rcg_le_gamma Ln 1))
  have htwo := rcm_twoCore_map e (rcr_hyp_twoCore F Ln.hEp Ln.hEc Ln.x Ln.hx Ln.hcover
    (rcg_E_le Ln) fun j => ⟨Ln.sp j, rcg_le_gamma Ln j⟩)
  have hHypΓ := rcs_hyp_of_subgroup (𝒳 := longClass σ.toRingHom) hA₀Γ (rcg_ne_bot hσ' hA₀R)
    (rcg_mul_self hσ' hA₀R) (rccOrbit_eq_range ΓT A₀T)
    (fun A hA B hB hAB => hR.rel A (hsub hA) B (hsub hB) hAB)
    (fun A hA B hB hs => rcc_closure_of_two hHyp hH hA₀R hA₀Γ hA₁ hA₂ h₁ h₂ hnot hA hB hs)
    hgen ⟨A₁T, hA₁, A₂T, hA₂,
      (CaseH.special_of_mem_lambdaSet_of_mem_lambdaSet hHyp hA₀R h₁ h₂ hncT).1⟩ hcenter htwo
  have hkc : Nat.card (fixSubfield σ) = 2 ^ f :=
    card_fixSubfield_cube Nat.prime_two F.hf F.hK σ F.hσ
  have hCT : Nat.card 𝒞[K, σ] = ordTrialityD4 (2 ^ f) := by rw [Nat.card_congr e.toEquiv, hT]
  have hcardΓ : Nat.card ↥ΓT = Nat.card ↥Γ := Subgroup.card_map_of_injective e.injective
  have hE : ∀ E' ∈ rcsSub ΓT (rccOrbit ΓT A₀T), Nat.card E' = 2 ^ f := by
    rintro _ ⟨A, hA, rfl⟩
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (rccOrbit_le hA₀Γ hA)).toEquiv]
    obtain ⟨g, -, rfl⟩ := hA
    calc Nat.card ↥(conjSub A₀T g) = Nat.card ↥A₀T :=
          Subgroup.card_map_of_injective (MulAut.conj g).injective
      _ = Nat.card ↥A₀ := Subgroup.card_map_of_injective e.injective
      _ = 2 ^ f := by rw [hA₀, rc3_card_rcaA0, hkc]
  have hmM : Nat.card ↥ΓT ∣ ordTrialityD4 (2 ^ f) := hT ▸ Subgroup.card_subgroup_dvd_card ΓT
  have hRm : rOrd 3 f ∣ Nat.card ↥ΓT := by
    rw [hcardΓ]
    have h1 : Nat.card (rclPx (Ln.sp 0)) ∣ Nat.card Γ :=
      Subgroup.card_dvd_of_le (rcg_le_gamma Ln 0)
    rw [card_rclPx, (rcl_card_rclQ F 0).1 rfl] at h1
    simp only [rOrd, ↓reduceIte]
    exact h1
  have hpm : p ^ padicValNat p (ordTrialityD4 (2 ^ f)) ∣ Nat.card ↥ΓT := by
    rw [hcardΓ, ← hCT, ← Nat.factorization_def _ hp, ← Sylow.card_eq_multiplicity S]
    exact Subgroup.card_dvd_of_le (rcg_sylow_le Ln)
  have hpΦ : p ∣ phiOrd 3 (2 ^ f) := by
    simp only [phiOrd, ↓reduceIte]
    have h := F.hpd
    have h' : ((2 ^ f : ℕ) : ℤ) ^ 2 + 1 * ((2 ^ f : ℕ) : ℤ) + 1 =
        (((2 ^ f) ^ 2 + 2 ^ f + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h'] at h
    exact Int.natCast_dvd_natCast.mp h
  have hcard := rcs_output_card hHypΓ (rcs_arsOutput hHypΓ) (c := 3) (Or.inl rfl)
    (by have := F.hf; omega) hp hp5 hpΦ hE hmM hRm hpm
  have htop : ΓT = ⊤ := Subgroup.eq_top_of_card_eq ΓT (hcard.trans hT.symm)
  rw [← Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective Γ, ← hΓT, htop,
    Subgroup.comap_top]

theorem rc3_eq_top_of_le (hσ3 : ∀ c, σ (σ (σ c)) = c)
    [Finite (twistedGroup σ.toRingHom)] [IsSimpleGroup (twistedGroup σ.toRingHom)]
    (hT : Nat.card (twistedGroup σ.toRingHom) = ordTrialityD4 (2 ^ f))
    (e : 𝒞[K, σ] ≃* twistedGroup σ.toRingHom)
    (hcompat : ∀ k, (((e k : twistedGroup σ.toRingHom) : adjointGroup d4 K) : ModGL d4 K) =
      ((k : 𝒞[K, σ]) : ModGL d4 K))
    {F : RclFrame 2 f K σ 1 p L} {S : Sylow p 𝒞[K, σ]} {c : 𝒞[K, σ]} {E : Subgroup 𝒞[K, σ]}
    (Ln : RceLines F S c E) {N : Subgroup 𝒞[K, σ]}
    (hC : Subgroup.centralizer ({Ln.x 0} : Set 𝒞[K, σ]) ≤ N)
    (hN : Subgroup.normalizer ((S : Subgroup 𝒞[K, σ]) : Set 𝒞[K, σ]) ≤ N) : N = ⊤ := by
  have : Fact p.Prime := ⟨F.hp⟩
  have hΓN : rcgGamma Ln ≤ N := iSup_le fun j => by
    obtain ⟨n, -, hnN, hPj⟩ := rcg_factor_conj Ln j
    rw [hPj]
    exact rca_map_conj_le ((rclPx_le_centralizer (Ln.sp 0)).trans hC) (hN hnN)
  rw [rc3_gamma_eq_top hσ3 hT e hcompat Ln] at hΓN
  exact eq_top_iff.2 hΓN

end Gamma

section Final


theorem rc3_centN_phi3 {q : TauCeti.PrimePower} (hq : q.p = 2) {K : Type} [Group K] [Finite K]
    [IsSimpleGroup K] (hiso : IsoLie K (.trialityD4 q)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpd : p ∣ q.card ^ 2 + q.card + 1) (S : Sylow p K) (E : Subgroup K) (hES : E ≤ S)
    (hE : CFSG.IsElementaryAbelian p E) (hEc : Nat.card E = p ^ 2) :
    ∃ x ∈ E, x ≠ 1 ∧ ∀ N : Subgroup K, IsCoatom N → Subgroup.centralizer {x} ≤ N →
      ¬ Subgroup.normalizer ((S : Subgroup K) : Set K) ≤ N := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨X, _, _, σ, _, e₀, e, hσ3, hσq, hX, -, hcompat, hord⟩ := rcg_exists_model_equiv hq hiso
  have hQ : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq]
  set f := q.exponent with hfdef
  have hf : 1 ≤ f := q.exponent_pos
  let L := AlgebraicClosure X
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap X L).injective 2
  have hK : Nat.card X = (2 ^ f) ^ 3 := by rw [hX, hQ]
  have hσ : ∀ c, σ c = c ^ (2 ^ f) := fun c => by rw [hσq, hQ]
  have hpd' : (p : ℤ) ∣ ((2 ^ f : ℕ) : ℤ) ^ 2 + 1 * ((2 ^ f : ℕ) : ℤ) + 1 := by
    rw [hQ] at hpd
    have h' : ((2 ^ f : ℕ) : ℤ) ^ 2 + 1 * ((2 ^ f : ℕ) : ℤ) + 1 =
        (((2 ^ f) ^ 2 + 2 ^ f + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h']
    exact Int.natCast_dvd_natCast.mpr hpd
  obtain ⟨F⟩ := rcl_exists_frame (ℓ := 2) (L := L) rfl hf hK hσ (Or.inl rfl) hp (by omega) hpd'
  have : Finite (twistedGroup σ.toRingHom) := Finite.of_equiv K e.toEquiv
  have : IsSimpleGroup (twistedGroup σ.toRingHom) := e.symm.isSimpleGroup
  have hT : Nat.card (twistedGroup σ.toRingHom) = ordTrialityD4 (2 ^ f) := by
    rw [hord]
    unfold d4Order ordTrialityD4
    ring
  set e' := e₀.symm.trans e with he'
  have hcompat' : ∀ k, (((e' k : twistedGroup σ.toRingHom) : adjointGroup d4 X) : ModGL d4 X) =
      ((k : 𝒞[X, σ]) : ModGL d4 X) := fun k => by
    have := hcompat (e₀.symm k)
    rw [MulEquiv.apply_symm_apply] at this
    exact this
  set S' : Sylow p 𝒞[X, σ] := S.mapSurjective (f := e₀.toMonoidHom) e₀.surjective with hS'
  set E' := E.map e₀.toMonoidHom with hE'
  have hS'c : (S' : Subgroup 𝒞[X, σ]) = (S : Subgroup K).map e₀.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  have hE'S : E' ≤ S' := by
    rw [hS'c]
    exact Subgroup.map_mono hES
  have hE'p : ∀ y ∈ E', y ^ p = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, CFSG.elemPow_eq_one_of_isElementaryAbelian y hy, map_one]
  have hE'c : Nat.card E' = p ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective e₀.injective, hEc]
  obtain ⟨c, hc⟩ := F.hconj (S' : Subgroup 𝒞[X, σ]) S'.isPGroup'
  obtain ⟨Ln⟩ := rce_exists_lines F S' (c := c) hc hE'S hE'p hE'c
  obtain ⟨y, hyE, hy⟩ := (Ln.hx 0).1
  refine ⟨y, hyE, fun h1 => (Ln.hx 0).2 (by rw [← hy, h1, map_one]), ?_⟩
  intro N hNc hCN hNN
  apply hNc.1
  have htop : N.map e₀.toMonoidHom = ⊤ := by
    refine rc3_eq_top_of_le hσ3 hT e' hcompat' Ln ?_ ?_
    · intro z hz
      refine ⟨e₀.symm z, hCN ?_, e₀.apply_symm_apply z⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
      apply e₀.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      have hy' : e₀.toMonoidHom y = Ln.x 0 := hy
      rw [MulEquiv.coe_toMonoidHom] at hy'
      rw [hy']
      exact hz
    · rw [hS'c, ← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.map_mono hNN
  rw [← Subgroup.comap_map_eq_self_of_injective (f := e₀.toMonoidHom) e₀.injective N, htop,
    Subgroup.comap_top]

end Final

end CFSG.RankThree.PartOne.D4RC
