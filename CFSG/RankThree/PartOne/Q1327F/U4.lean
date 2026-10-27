module

public import CFSG.RankThree.PartOne.Q1327F.Common
public import CFSG.RankThree.PartOne.Q1327F.PGroup
public import CFSG.RankThree.PartOne.Q1327F.Unip
public import CFSG.RankThree.PartOne.Q1327F.Orders
public import CFSG.RankThree.PartOne.Q1327T.Item7UBasic
public import CFSG.RankThree.PartOne.K133.MaxItems
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.GroupTheory.PRankCoprimeQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.RankThree.PartOne.K133.Moving
public import CFSG.RankThree.PartOne.K133.SylowKill
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
public import CFSG.RankThree.PartOne.KF.R7Final
public import CFSG.RankThree.PartOne.KF.SUGram
public import CFSG.RankThree.PartOne.KFOUT3.KtySUQuot
public import CFSG.RankThree.PartOne.KLAY.Core
public import CFSG.RankThree.PartOne.Q1327T.Item7Inv
public import CFSG.RankThree.PartOne.S12.InputsSec15
public import CFSG.RankThree.PartOne.S12.Sec136Pair
public import CFSG.RankThree.PartOne.S12.Sec136Setup
public import CFSG.RankThree.PartOne.S12.Sec141Row
public import CFSG.RankThree.PartOne.S12.Sec15FA
public import CFSG.RankThree.PartOne.S12.Sec15Items
public import CFSG.RankThree.PartOne.S15K.PSylowOrth
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorNormalizer

public section

namespace CFSG.RankThree.PartOne.Q1327F

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.Q1327T CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K133

section Diag

variable {Q : Type} [Group Q] [Finite Q] {K : Type} [Field K] {p f n : ℕ}

theorem false_of_unitary_diag' {ℓ : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (hn : 4 ≤ n)
    (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (hpq : p ∣ ℓ ^ f + 1)
    (π : unitarySU ℓ f K n →* Q)
    (hπ : Function.Surjective π) (hker : ¬ p ∣ Nat.card π.ker) (hZ : Subgroup.center Q = ⊥)
    {Ē : Subgroup Q} (hE : IsElementaryAbelian p Ē) (hcard : Nat.card Ē = p ^ 2)
    (hmax : ∀ F : Subgroup Q, IsElementaryAbelian p F → F ≤ Subgroup.centralizer (Ē : Set Q) →
      Ē ≤ F → F ≤ Ē ⊔ Subgroup.center Q) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hU : UnitaryFieldData ℓ f K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hfinK : Finite K := hU.finite
  obtain ⟨E₀, hE₀, hE₀card, hE₀map⟩ := exists_lift_elementaryAbelian π hp hker Ē
    (fun y _ => hπ y) hcard
  have hE₀exp : ∀ x ∈ E₀, x ^ p = 1 := fun x hx =>
    elemPow_eq_one_of_isElementaryAbelian (A := E₀) x hx
  have hE₀comm : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x := fun x hx y hy => by
    have := congrArg Subtype.val ((IsMulCommutative.is_comm (M := E₀)).comm ⟨x, hx⟩ ⟨y, hy⟩)
    simpa using this
  obtain ⟨ψ, hψ⟩ := exists_diag_iso_le_of_iso hU hp hpq (MulEquiv.refl _) E₀ hE₀exp hE₀comm
  have hrK : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    have h1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
    have hfac : (ℓ ^ f) ^ 2 - 1 = (ℓ ^ f + 1) * (ℓ ^ f - 1) := by
      zify [Nat.one_le_pow 2 (ℓ ^ f) (by omega), h1]
      ring
    rw [hfac]
    exact Dvd.dvd.mul_right hpq _
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hTle : torusSU p (m + 1) K ≤ unitarySU ℓ f K (m + 1) := torusSU_le_unitarySU hU hpq
  let T : Subgroup (unitarySU ℓ f K (m + 1)) := (torusSU p (m + 1) K).subgroupOf _
  have hTmem : ∀ g : unitarySU ℓ f K (m + 1), g ∈ T ↔ (g : GL (Fin (m + 1)) K) ∈ torusSU p _ K :=
    fun g => Iff.rfl
  have hTcard : p ^ m ≤ Nat.card T := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTle).toEquiv]
    exact pow_le_card_torusSU hp hrK m
  have hTel : IsElementaryAbelian p T := isElementaryAbelian_torusSU_subgroupOf _
  let Eplus : Subgroup (unitarySU ℓ f K (m + 1)) := T.map ψ.toMonoidHom
  have hEel : IsElementaryAbelian p Eplus := IsElementaryAbelian.map ψ.toMonoidHom
  have hE₀le : E₀ ≤ Eplus := by
    intro x hx
    exact ⟨ψ.symm x, (hTmem _).2 (hψ _ (by simpa using hx)), by simp⟩
  have hEcard : p ^ m ≤ Nat.card Eplus := by
    rw [Subgroup.card_map_of_injective ψ.injective]
    exact hTcard
  let P' : Subgroup Q := Eplus.map π
  have hP'el : IsElementaryAbelian p P' := IsElementaryAbelian.map π
  have hEP : Ē ≤ P' := by
    rw [← hE₀map]
    exact Subgroup.map_mono hE₀le
  have hP'card : Nat.card P' = Nat.card Eplus := by
    have hdis := N143.disjoint_ker_of_isPGroup π hp (IsElementaryAbelian.isPGroup p Eplus) hker
    exact N143.card_map_of_disjoint_ker π hdis
  have hC : P' ≤ Subgroup.centralizer (Ē : Set Q) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have := congrArg Subtype.val ((IsMulCommutative.is_comm (M := P')).comm ⟨a, hEP ha⟩ ⟨y, hy⟩)
    simpa using this
  have hle := hmax P' hP'el hC hEP
  rw [hZ, sup_bot_eq] at hle
  have h1 : Nat.card P' ≤ Nat.card Ē := Subgroup.card_le_of_le hle
  rw [hP'card, hcard] at h1
  have h2 : p ^ 2 < p ^ m := by
    have := hEcard
    have : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    have h3 : p ^ 3 ≤ p ^ m := Nat.pow_le_pow_right hp.pos (by omega)
    omega
  omega

end Diag

section Hermitian

open CFSG.RankThree.PartOne.N143X

variable {ℓ : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
  (L : Type) [Field L] [Algebra K L] (E : Subgroup (GL ι K))

local notation "φ" => iterateFrobenius L ℓ

theorem hermitian_pairing' [CharP L ℓ] (f : ℕ) {A : Matrix ι ι L}
    (hA : (A.map (φ f))ᵀ * A = 1) (v w : ι → L) :
    ((φ f) ∘ (A *ᵥ v)) ⬝ᵥ (A *ᵥ w) = ((φ f) ∘ v) ⬝ᵥ w := by
  have h1 : ((φ f) ∘ (A *ᵥ v)) = (A.map (φ f)) *ᵥ ((φ f) ∘ v) :=
    funext fun i => RingHom.map_mulVec (φ f) A v i
  rw [h1]
  calc ((A.map (φ f)) *ᵥ ((φ f) ∘ v)) ⬝ᵥ (A *ᵥ w)
      = ((φ f) ∘ v) ⬝ᵥ ((A.map (φ f))ᵀ *ᵥ (A *ᵥ w)) := by
        rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
          dotProduct_comm]
    _ = ((φ f) ∘ v) ⬝ᵥ (((A.map (φ f))ᵀ * A) *ᵥ w) := by rw [Matrix.mulVec_mulVec]
    _ = ((φ f) ∘ v) ⬝ᵥ w := by rw [hA, Matrix.one_mulVec]

theorem joint_qinv_ne_bot_herm' [IsAlgClosed L] [CharP L ℓ] {p : ℕ} (f : ℕ) (hp : (p : L) ≠ 0)
    (hexp : ∀ e : E, (e : GL ι K) ^ p = 1) (hcomm : ∀ e e' : E, (e : GL ι K) * e' = e' * e)
    (hEL : ∀ e : E, ((mapL L (e : GL ι K)).map (φ f))ᵀ * mapL L (e : GL ι K) = 1)
    {χ : E → L} (h : joint L E χ ≠ ⊥) : joint L E (fun e => (φ f (χ e))⁻¹) ≠ ⊥ := by
  by_contra hbot
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h
  have hvanish : ∀ (ψ : E → L), ∀ w ∈ joint L E ψ, ((φ f) ∘ v) ⬝ᵥ w = 0 := by
    intro ψ w hw
    by_cases hψ : ψ = fun e => (φ f (χ e))⁻¹
    · subst hψ
      rw [hbot, Submodule.mem_bot] at hw
      subst hw
      simp
    · obtain ⟨g, hg⟩ := Function.ne_iff.1 hψ
      have h1 := hermitian_pairing' L f (hEL g) v w
      rw [(mem_joint L E).1 hv g, (mem_joint L E).1 hw g] at h1
      have h2 : (φ f) ∘ (χ g • v) = (φ f (χ g)) • ((φ f) ∘ v) := by
        funext i
        simp [map_mul]
      rw [h2] at h1
      simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul] at h1
      have hne : φ f (χ g) * ψ g ≠ 1 := fun h1' => hg (eq_inv_of_mul_eq_one_right h1')
      have h3 : (φ f (χ g) * ψ g - 1) * (((φ f) ∘ v) ⬝ᵥ w) = 0 := by linear_combination h1
      rcases mul_eq_zero.1 h3 with h0 | h0
      · exact absurd (sub_eq_zero.1 h0) hne
      · exact h0
  have htop := iSup_joint_eq_top L E hp hexp hcomm
  have hall : ∀ w : ι → L, ((φ f) ∘ v) ⬝ᵥ w = 0 := by
    intro w
    have hw : w ∈ ⨆ χ : E → L, joint L E χ := by rw [htop]; exact Submodule.mem_top
    refine Submodule.iSup_induction _ (motive := fun w => ((φ f) ∘ v) ⬝ᵥ w = 0) hw
      (fun ψ w hw => hvanish ψ w hw) (by simp) fun x y hx hy => ?_
    rw [dotProduct_add, hx, hy, add_zero]
  apply hv0
  funext i
  have := hall (Pi.single i 1)
  simp only [dotProduct_single, mul_one] at this
  exact (map_eq_zero (φ f)).1 this

theorem nuStable_of_hermitian' [IsAlgClosed L] [CharP L ℓ] {p : ℕ} (f : ℕ) (hp : (p : L) ≠ 0)
    (hpq : p ∣ ℓ ^ f - 1) (hexp : ∀ e : E, (e : GL ι K) ^ p = 1)
    (hcomm : ∀ e e' : E, (e : GL ι K) * e' = e' * e)
    (hEL : ∀ e : E, ((mapL L (e : GL ι K)).map (φ f))ᵀ * mapL L (e : GL ι K) = 1) :
    NuStable L E := by
  intro χ h
  have h1 := joint_qinv_ne_bot_herm' L E f hp hexp hcomm hEL h
  have h2 : (fun e : E => (φ f (χ e))⁻¹) = fun e => (χ e)⁻¹ := by
    funext e
    have hχ := weight_pow_eq_one L E hexp h e
    obtain ⟨m, hm⟩ := hpq
    have hq : ℓ ^ f = p * m + 1 := by
      have : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ (Fact.out : ℓ.Prime).pos
      omega
    have hx : φ f (χ e) = χ e := by
      rw [iterateFrobenius_def, hq, pow_succ, pow_mul, hχ, one_pow, one_mul]
    rw [hx]
  rwa [h2] at h1

variable {L E}

theorem faithfulSmallSym_normalizer_range_herm' [CharP K ℓ] {p : ℕ} (f : ℕ) (hp : (p : K) ≠ 0)
    (hp2 : p % 2 = 1) (hpq : p ∣ ℓ ^ f - 1) [IsElementaryAbelian p E]
    (hEK : ∀ e ∈ E, (((e : GL ι K) : Matrix ι ι K).map (· ^ ℓ ^ f))ᵀ *
      ((e : GL ι K) : Matrix ι ι K) = 1) :
    FaithfulSmallSym E.normalizerMonoidHom.range (Fintype.card ι) := by
  let L := AlgebraicClosure K
  have hpL : (p : L) ≠ 0 := by
    intro h0
    apply hp
    apply (algebraMap K L).injective
    rw [map_natCast, map_zero]
    exact h0
  have hexp : ∀ e : E, (e : GL ι K) ^ p = 1 := fun e =>
    elemPow_eq_one_of_isElementaryAbelian (A := E) e e.2
  have hcomm : ∀ e e' : E, (e : GL ι K) * e' = e' * e := fun e e' =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm e e')
  obtain ⟨hfin, hcard⟩ := nat_card_wts_le L E hpL hexp hcomm
  have hEL : ∀ e : E, ((mapL L (e : GL ι K)).map (iterateFrobenius L ℓ f))ᵀ *
      mapL L (e : GL ι K) = 1 := by
    intro e
    have hmap : (mapL L (e : GL ι K)).map (iterateFrobenius L ℓ f) =
        (((e : GL ι K) : Matrix ι ι K).map (· ^ ℓ ^ f)).map (algebraMap K L) := by
      ext i j
      simp [mapL, Matrix.map_apply, iterateFrobenius_def, map_pow]
    rw [hmap, ← Matrix.transpose_map, mapL, ← Matrix.map_mul, hEK e e.2,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hν : NuStable L E := nuStable_of_hermitian' L E f hpL hpq hexp hcomm hEL
  exact ⟨Wts L E, hfin, weightAction, hcard, weightAction_injective hpL hexp hcomm, nuPerm hν,
    nuPerm_sq hν, fun x y hx hy => nuPerm_fixed hp2 hexp hν x y hx hy,
    fun β => weightAction_comm_nuPerm hν β⟩

end Hermitian

section Unitary

variable {K : Type} [Field K] [Finite K] {p f n : ℕ}

theorem not_dvd_add_one_of_dvd_sub_one' {q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 1 ≤ q)
    (h : p ∣ q - 1) : ¬ p ∣ q + 1 := by
  intro h'
  have h2 : p ∣ (q + 1) - (q - 1) := Nat.dvd_sub h' h
  have h3 : (q + 1) - (q - 1) = 2 := by omega
  rw [h3] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)

theorem card_dvd_eight_of_unitary' {ℓ : ℕ} (hℓ : ℓ.Prime) {Y : Type} [Group Y] (hp : p.Prime)
    (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hn1 : 1 ≤ n) (hn : n ≤ 5) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hpq : p ∣ ℓ ^ f - 1)
    (e : Y ≃* StatedProj (StatedSU n (ℓ ^ f) K)) {E : Subgroup Y} (hE : IsElementaryAbelian p E) :
    Nat.card E.normalizerMonoidHom.range ∣ 8 := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hU : UnitaryFieldData ℓ f K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hchar : CharP K ℓ := hU.charP
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  have hpd : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1) := fun hd =>
    not_dvd_add_one_of_dvd_sub_one' hp hp2 hq1 hpq (hd.trans (Nat.gcd_dvd_right _ _))
  have hpK : (p : K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff K ℓ p).1 h0
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 this).symm
  obtain ⟨F, hF, hFM, -, hdvd⟩ := N143X.exists_cover_of_matrix_model (StatedSU n (ℓ ^ f) K) e hp
    (d := Nat.gcd n (ℓ ^ f + 1)) (fun c hc => by
      obtain ⟨h1, h2⟩ := ((CFSG.LinearGroups.unitary_scalar_kernel hℓ hK hn1).2.1 c).1 hc
      exact pow_gcd_eq_one.2 ⟨h1, h2⟩) hpd hE
  have hEK : ∀ x ∈ F, (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map (· ^ ℓ ^ f))ᵀ *
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := fun x hx => by
    have := hFM hx
    have hset := (CFSG.LinearGroups.unitary_scalar_kernel hℓ hK hn1).1
    have hx' : x ∈ ({A : GL (Fin n) K | (A : Matrix (Fin n) (Fin n) K).det = 1 ∧
      ((A : Matrix (Fin n) (Fin n) K).map (· ^ ℓ ^ f))ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1} :
        Set (GL (Fin n) K)) := by
      rw [← hset]
      exact this
    exact hx'.2
  exact hdvd.trans (FaithfulSmallSym.card_dvd_eight
    (faithfulSmallSym_normalizer_range_herm' f hpK (hp.eq_two_or_odd.resolve_left hp2) hpq hEK)
    (by rw [Fintype.card_fin]; exact hn))

theorem pRank_statedProj_statedSU_le_one' {ℓ : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpℓ : p ≠ ℓ) (hn1 : 1 ≤ n) (hK : Nat.card K = (ℓ ^ f) ^ 2) (hpq : ¬ p ∣ ℓ ^ f + 1)
    (h : n / orderOf (-((ℓ ^ f : ℕ) : ZMod p)) ≤ 1) :
    CFSG.pRank p (StatedProj (StatedSU n (ℓ ^ f) K)) ≤ 1 := by
  have hpQ : ¬ p ∣ ℓ ^ f := fun hd =>
    hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow hd))
  have hN : ¬ p ∣ Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (ℓ ^ f) K)) := by
    rw [(CFSG.LinearGroups.unitary_scalar_kernel hℓ hK hn1).2.2]
    exact fun hd => hpq (hd.trans (Nat.gcd_dvd_right _ _))
  rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp _ hN]
  exact pRank_statedSU_le_one hp hp2 hK hpQ hn1 h

end Unitary

section Leaf

theorem psu4_core {Q : Type} [Group Q] [Finite Q] {p g ℓ : ℕ} {Ē : Subgroup Q}
    (h : Row8Conf p g Q Ē) (hℓ : ℓ.Prime) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ 1) ^ 2) (hZ : Subgroup.center Q = ⊥)
    (e : (Q ⧸ Subgroup.center Q) ≃* StatedProj (StatedSU 4 (ℓ ^ 1) K))
    (hW : Nonempty (torusImage Ē ⊤ ≃* Equiv.Perm (Fin 3))) : False := by
  have hp := h.prime
  have hp5 := h.five_le
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hU : UnitaryFieldData ℓ 1 K := ⟨hℓ, le_rfl, by rw [hK, ← pow_mul, mul_comm]⟩
  have hchar : CharP K ℓ := hU.charP
  let ce : Q ≃* (Q ⧸ Subgroup.center Q) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  by_cases hpr : p = ℓ
  · have hcharp : CharP K p := by rw [hpr]; exact hchar
    refine false_of_pGroup_plane hp5 hZ ?_ ?_ h.elem h.card
      (fun F hF hFc hEF => by simpa [hZ] using h.max F hF hFc hEF) hW
    · intro y ⟨k, hk⟩
      have h1 : ((ce.trans e) y) ^ p ^ k = 1 := by rw [← map_pow, hk, map_one]
      have h2 := statedProj_pow_p_eq_one (ι := Fin 4) (by simp; omega) (StatedSU 4 (ℓ ^ 1) K) _
        ⟨k, h1⟩
      exact (map_eq_one_iff _ (ce.trans e).injective).1 (by rw [map_pow]; exact h2)
    · rw [Nat.card_congr (ce.trans e).toEquiv, hpr]
      exact p_cube_dvd_card_psu_four hℓ hK
  · have hq1 : 1 ≤ ℓ ^ 1 := Nat.one_le_pow _ _ hℓ.pos
    by_cases hpq1 : p ∣ ℓ ^ 1 + 1
    · obtain ⟨π, hπ, hπk⟩ := exists_cover_unitary hZ e
      have hker : ¬ p ∣ Nat.card π.ker := by
        rw [hπk, (CFSG.LinearGroups.unitary_scalar_kernel hℓ hK (by norm_num : 1 ≤ 4)).2.2]
        intro hd
        have := Nat.le_of_dvd (by norm_num) (hd.trans (Nat.gcd_dvd_left 4 _))
        omega
      exact false_of_unitary_diag' hℓ hp (by norm_num : 4 ≤ 4) le_rfl hK hpq1 π hπ hker hZ
        h.elem h.card h.max
    · by_cases hpq2 : p ∣ ℓ ^ 1 - 1
      · have hdvd := card_dvd_eight_of_unitary' hℓ hp hp2 hpr (n := 4) (by norm_num) (by norm_num)
          le_rfl hK hpq2 (ce.trans e) h.elem
        obtain ⟨φ⟩ := hW
        have h6 : Nat.card Ē.normalizerMonoidHom.range = 6 := by
          rw [← torusImage_top_eq_range]
          exact (Nat.card_congr φ.toEquiv).trans
            (by simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial])
        rw [h6] at hdvd
        omega
      · have hpQ : ¬ p ∣ ℓ ^ 1 := fun hd =>
          hpr ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow hd))
        have hd3 := three_le_orderOf_neg_of_not_dvd hp hpQ hpq2 hpq1 hq1
        have hrk := pRank_statedProj_statedSU_le_one' hℓ hp hp2 hpr (n := 4) (by norm_num) hK hpq1
          (Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)))
        have h2 := h.two_le_pRank
        rw [pRank_eq_of_mulEquiv_of_one_lt hp.one_lt e] at h2
        omega

theorem row8U3At_leaf4_two
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    Row8U3At (K133.leaf4 2) := by
  intro Q _ _ p g Ē hX h
  obtain ⟨q, hq2, hq1, hv, ⟨e0⟩⟩ := hX
  have hp := h.prime
  have hp5 := h.five_le
  have : Fact p.Prime := ⟨hp⟩
  have hmod : StatedClassicalModel (Q ⧸ Subgroup.center Q) .PSU 4 q.p q.exponent :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e0
  have hZ : Subgroup.center Q = ⊥ :=
    center_eq_bot_of_multiplier' hp hGA h.quasisimple h.center_p (t := .PSU) (n := 4)
      (f := q.exponent) (ℓ := q.p) ⟨hmod.1, Or.inl hmod⟩ fun hd =>
        not_dvd_thirtySix hp hp5 (hd.trans (card_multiplier_psu_four_dvd hq2))
  refine ⟨hZ, fun hW => ?_⟩
  exfalso
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hK1 : Nat.card K = (q.p ^ 1) ^ 2 := by rw [hK, hq1]
  have e1 : (Q ⧸ Subgroup.center Q) ≃* StatedProj (StatedSU 4 (q.p ^ 1) K) := hq1 ▸ e
  exact psu4_core h q.prime_p hK1 hZ e1 hW

end Leaf

end CFSG.RankThree.PartOne.Q1327F
