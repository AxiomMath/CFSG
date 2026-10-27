module

public import CFSG.RankThree.PartOne.D4RC.Cross6
public import CFSG.RankThree.PartOne.D4RC.NoFix6
public import CFSG.RankThree.PartOne.D4RC.CentN

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

theorem rc6_conjSub_of_le_centralizer {G : Type*} [Group G] {B : Subgroup G} {x : G}
    (h : B ≤ Subgroup.centralizer ({x} : Set G)) : conjSub B x = B := by
  have hc : ∀ b ∈ B, x * b = b * x := fun b hb =>
    Subgroup.mem_centralizer_iff.1 (h hb) x rfl
  ext a
  rw [mem_conjSub]
  constructor
  · intro ha
    have h1 := hc _ ha
    have e1 : a = x⁻¹ * a * x := by
      calc a = x * (x⁻¹ * a * x) * x⁻¹ := by group
        _ = x⁻¹ * a * x := by rw [h1]; group
    rw [e1]
    exact ha
  · intro ha
    have h1 := hc _ ha
    have e1 : x⁻¹ * a * x = a := by
      calc x⁻¹ * a * x = x⁻¹ * (a * x) := by group
        _ = x⁻¹ * (x * a) := by rw [h1]
        _ = a := by group
    rw [e1]
    exact ha

section Gamma

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {p : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2]

theorem rc6_dvd (F : RclFrame 2 f K σ (-1) p L) : p ∣ (2 ^ f) ^ 2 - 2 ^ f + 1 := by
  have h := F.hpd
  have hle : 2 ^ f ≤ (2 ^ f) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h' : ((2 ^ f : ℕ) : ℤ) ^ 2 + -1 * ((2 ^ f : ℕ) : ℤ) + 1 =
      (((2 ^ f) ^ 2 - 2 ^ f + 1 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hle]
    ring
  rw [h'] at h
  exact Int.natCast_dvd_natCast.mp h

theorem rc6_gamma_eq_top (hσ3 : ∀ c, σ (σ (σ c)) = c)
    [Finite (twistedGroup σ.toRingHom)] [IsSimpleGroup (twistedGroup σ.toRingHom)]
    (hT : Nat.card (twistedGroup σ.toRingHom) = ordTrialityD4 (2 ^ f))
    (e : 𝒞[K, σ] ≃* twistedGroup σ.toRingHom)
    (hcompat : ∀ k, (((e k : twistedGroup σ.toRingHom) : adjointGroup d4 K) : ModGL d4 K) =
      ((k : 𝒞[K, σ]) : ModGL d4 K))
    {F : RclFrame 2 f K σ (-1) p L} {S : Sylow p 𝒞[K, σ]} {c : 𝒞[K, σ]} {E : Subgroup 𝒞[K, σ]}
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
  have hconjM : ∀ (M : Subgroup 𝒞[K, σ]) g, conjSub (M.map e.toMonoidHom) (e g) =
      (conjSub M g).map e.toMonoidHom := fun M g => rcm_conjSub_map e.toMonoidHom M g
  have hconjT : ∀ g, conjSub A₀T (e g) = (conjSub A₀ g).map e.toMonoidHom := fun g =>
    hconjM A₀ g
  obtain ⟨n, hnΓ, -, hP1⟩ := rcg_factor_conj Ln 1
  obtain ⟨y, hyP, hno⟩ := rcx_exists_not_opposite hσ3 e hcompat (Ln.sp 0) D₀ n
  set A₁ := conjSub A₀ (n * y) with hA₁def
  set A₁T := conjSub A₀T (e (n * y)) with hA₁T
  have hA₁e : A₁T = A₁.map e.toMonoidHom := hconjT _
  have hA₁ : A₁T ∈ rccOrbit ΓT A₀T :=
    ⟨e (n * y), Subgroup.mem_map_of_mem _ (Γ.mul_mem hnΓ (rcg_le_gamma Ln 0 hyP)), rfl⟩
  have hA₁R : A₁T ∈ longClass σ.toRingHom := rcg_conjSub_mem hA₀R _
  have hno' : ¬ Opposite A₀T A₁T := by rw [hA₁e]; exact hno
  have hq : Nat.card K = (2 ^ f) ^ 3 := F.hK
  have hpq := rc6_dvd F
  have hx0 : orderOf (e (Ln.x 0)) = p := by rw [MulEquiv.orderOf_eq, (Ln.sp 0).hx]
  have hx1 : orderOf (e (Ln.x 1)) = p := by rw [MulEquiv.orderOf_eq, (Ln.sp 1).hx]
  have hcomm : Commute (e (Ln.x 0)) (e (Ln.x 1)) := by
    have h := (IsPGroup.isMulCommutative_of_card_eq_prime_sq Ln.hEc).is_comm.comm
      (⟨_, (Ln.hx 0).1⟩ : E) ⟨_, (Ln.hx 1).1⟩
    have h' : Ln.x 0 * Ln.x 1 = Ln.x 1 * Ln.x 0 := congrArg Subtype.val h
    exact (Commute.map h' e)
  have hA₀C : A₀ ≤ Subgroup.centralizer ({Ln.x 0} : Set 𝒞[K, σ]) :=
    (rcaA0_le (Ln.sp 0) D₀).trans (rclPx_le_centralizer (Ln.sp 0))
  have hfix0' : conjSub A₀ (Ln.x 0) = A₀ := rc6_conjSub_of_le_centralizer hA₀C
  have hfix0 : conjSub A₀T (e (Ln.x 0)) = A₀T := by rw [hconjT, hfix0']
  have hA₁P : A₁ ≤ rclPx (Ln.sp 1) := by
    rw [hA₁def, conjSub_mul, hP1]
    exact Subgroup.map_mono (rca_map_conj_le (rcaA0_le (Ln.sp 0) D₀) hyP)
  have hfix1' : conjSub A₁ (Ln.x 1) = A₁ :=
    rc6_conjSub_of_le_centralizer (hA₁P.trans (rclPx_le_centralizer (Ln.sp 1)))
  have hfix1 : conjSub A₁T (e (Ln.x 1)) = A₁T := by
    rw [hA₁e, hconjM, hfix1']
  have hne : A₀T ≠ A₁T := by
    intro h
    rw [hA₁e] at h
    have h' : A₀ = A₁ := Subgroup.map_injective e.injective h
    apply rcn_not_normalizes Ln D₀ (j := 1) (by decide)
    rw [← hA₀, h']
    exact hfix1'
  have hsp : Special (longClass σ.toRingHom) A₀T A₁T :=
    rcf_special_of_not_opposite hσ' hq hp hpq hx0 hx1 hcomm hA₀R hA₁R hne hfix0 hfix1 hno'
  have hy0 : e (Ln.x 0) ∈ ΓT := Subgroup.mem_map_of_mem _ (rcg_E_le Ln (Ln.hx 0).1)
  have hyL : conjSub (A₀T ⊔ ⁅A₁T, A₀T⁆) (e (Ln.x 0)) ≠ A₀T ⊔ ⁅A₁T, A₀T⁆ := by
    rw [Subgroup.commutator_comm]
    exact rcg_lfpf hσ' hq hp hpq hx0 hA₀R hfix0
      (CaseH.commutator_mem_lambdaSet hHyp hA₀R hA₁R hsp).1
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
    (fun A hA B hB hs => rcc_closure_of_special hHyp hH hA₀R hA₀Γ hA₁ hsp.symm hy0 hfix0 hyL
      hA hB hs)
    hgen ⟨A₀T, rccOrbit_self A₀T, A₁T, hA₁, hsp⟩ hcenter htwo
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
  have hRm : rOrd 6 f ∣ Nat.card ↥ΓT := by
    rw [hcardΓ]
    have h1 : Nat.card (rclPx (Ln.sp 0)) ∣ Nat.card Γ :=
      Subgroup.card_dvd_of_le (rcg_le_gamma Ln 0)
    rw [card_rclPx, (rcl_card_rclQ F 0).2 rfl] at h1
    simp only [rOrd, show (6 : ℕ) ≠ 3 by decide, ↓reduceIte]
    exact h1
  have hpm : p ^ padicValNat p (ordTrialityD4 (2 ^ f)) ∣ Nat.card ↥ΓT := by
    rw [hcardΓ, ← hCT, ← Nat.factorization_def _ hp, ← Sylow.card_eq_multiplicity S]
    exact Subgroup.card_dvd_of_le (rcg_sylow_le Ln)
  have hpΦ : p ∣ phiOrd 6 (2 ^ f) := by
    simp only [phiOrd, show (6 : ℕ) ≠ 3 by decide, ↓reduceIte]
    exact hpq
  have hcard := rcs_output_card hHypΓ (rcs_arsOutput hHypΓ) (c := 6) (Or.inr rfl)
    (by have := F.hf; omega) hp hp5 hpΦ hE hmM hRm hpm
  have htop : ΓT = ⊤ := Subgroup.eq_top_of_card_eq ΓT (hcard.trans hT.symm)
  rw [← Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective Γ, ← hΓT, htop,
    Subgroup.comap_top]

theorem rc6_eq_top_of_le (hσ3 : ∀ c, σ (σ (σ c)) = c)
    [Finite (twistedGroup σ.toRingHom)] [IsSimpleGroup (twistedGroup σ.toRingHom)]
    (hT : Nat.card (twistedGroup σ.toRingHom) = ordTrialityD4 (2 ^ f))
    (e : 𝒞[K, σ] ≃* twistedGroup σ.toRingHom)
    (hcompat : ∀ k, (((e k : twistedGroup σ.toRingHom) : adjointGroup d4 K) : ModGL d4 K) =
      ((k : 𝒞[K, σ]) : ModGL d4 K))
    {F : RclFrame 2 f K σ (-1) p L} {S : Sylow p 𝒞[K, σ]} {c : 𝒞[K, σ]} {E : Subgroup 𝒞[K, σ]}
    (Ln : RceLines F S c E) {N : Subgroup 𝒞[K, σ]}
    (hC : Subgroup.centralizer ({Ln.x 0} : Set 𝒞[K, σ]) ≤ N)
    (hN : Subgroup.normalizer ((S : Subgroup 𝒞[K, σ]) : Set 𝒞[K, σ]) ≤ N) : N = ⊤ := by
  have : Fact p.Prime := ⟨F.hp⟩
  have hΓN : rcgGamma Ln ≤ N := iSup_le fun j => by
    obtain ⟨n, -, hnN, hPj⟩ := rcg_factor_conj Ln j
    rw [hPj]
    exact rca_map_conj_le ((rclPx_le_centralizer (Ln.sp 0)).trans hC) (hN hnN)
  rw [rc6_gamma_eq_top hσ3 hT e hcompat Ln] at hΓN
  exact eq_top_iff.2 hΓN

end Gamma

section Final


theorem rc6_centN_phi6 {q : TauCeti.PrimePower} (hq : q.p = 2) {K : Type} [Group K] [Finite K]
    [IsSimpleGroup K] (hiso : IsoLie K (.trialityD4 q)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpd : p ∣ q.card ^ 2 - q.card + 1) (S : Sylow p K) (E : Subgroup K) (hES : E ≤ S)
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
  have hpd' : (p : ℤ) ∣ ((2 ^ f : ℕ) : ℤ) ^ 2 + -1 * ((2 ^ f : ℕ) : ℤ) + 1 := by
    rw [hQ] at hpd
    have hle : 2 ^ f ≤ (2 ^ f) ^ 2 := Nat.le_self_pow (by norm_num) _
    have h' : ((2 ^ f : ℕ) : ℤ) ^ 2 + -1 * ((2 ^ f : ℕ) : ℤ) + 1 =
        (((2 ^ f) ^ 2 - 2 ^ f + 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hle]
      ring
    rw [h']
    exact Int.natCast_dvd_natCast.mpr hpd
  obtain ⟨F⟩ := rcl_exists_frame (ℓ := 2) (L := L) rfl hf hK hσ (Or.inr rfl) hp (by omega) hpd'
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
    refine rc6_eq_top_of_le hσ3 hT e' hcompat' Ln ?_ ?_
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

theorem rc6_max3D4CentN6 : Max3D4CentN6 :=
  fun _ hq _ _ _ _ hiso _ hp hp5 hpd S E hES hE hEc =>
    rc6_centN_phi6 hq hiso hp hp5 hpd S E hES hE hEc

theorem rc6_max3D4CentN : Max3D4CentN := max3D4CentN_of_phi6 rc6_max3D4CentN6

end Final

end CFSG.RankThree.PartOne.D4RC
