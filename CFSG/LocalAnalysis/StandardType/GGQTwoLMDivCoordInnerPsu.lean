module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerTor
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerLift
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerTlift
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerTid
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerTker
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerTcl
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerW
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerWf
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerQuot

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary Matrix

variable {G : Type} [Group G] [Finite G]

theorem qTwoLMDivCoordInner_psu_assembly {B Bs L : Subgroup G} {x : G} (hG : GGThmIHyp 3 B x L)
    (hBs : GGBstar 3 B Bs) (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {m : ℕ} (hm : 6 ≤ m)
    (h3 : 3 ∣ m) {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {L0 : Type} [Group L0]
    {c : ↥L →* L0} {π : Su F0 2 1 m →* L0} {ρ : ↥Bs →* MulAut L0}
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) (hk : QTwoDivKind.facts .psuInner m Bs L) :
    ∃ C : QTwoDivCoords m (QTwoHm m h3) (QTwoHm m h3) Bs L x hN,
      IsHmModel m h3 (QTwoHm m h3) C.permV ∧ IsHmModel m h3 (QTwoHm m h3) C.permVT := by
  obtain ⟨h1, h2⟩ := hk
  obtain ⟨δ, hδ⟩ := qTwoLMDivCoordInner_torus hU.card h3
  obtain ⟨τ, hτ⟩ := qTwoLMDivCoordInner_tlift hBs hN hU hδ
  have h_Tker1 : ∀ f, τ f = 1 ↔ f ∈ Subgroup.zpowers (qTwoOneVec m h3) :=
    (qTwoLMDivCoordInner_tker hG hN hm h3 hU hδ hτ).2.1 h1
  obtain ⟨hrange, hsplit⟩ := qTwoLMDivCoordInner_tident hG hBs hN hm h3 hU hδ hτ h2

  have hx3 : x ^ 3 = 1 := hBs.2.1.2 x (hBs.1 hG.2.2.2.2.2.2.1.2.1)
  have hxne : x ≠ 1 := hG.2.2.2.2.2.2.1.2.2.1
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hxne

  have hxL : x ∉ L := by
    intro hxL
    have hxmem : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      have hc : x * (l : G) = (l : G) * x :=
        Subgroup.mem_centralizer_iff.mp (qTwoLMFrameC_le_centralizer hG l.2) x
          (Set.mem_singleton x)
      exact Subtype.ext hc.symm
    have hxordL : orderOf (⟨x, hxL⟩ : ↥L) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact hxord
    have hdvd : 3 ∣ Nat.card (Subgroup.center ↥L) := by
      have h := Subgroup.orderOf_dvd_natCard (Subgroup.center ↥L) hxmem
      rwa [hxordL] at h
    exact h1 hdvd

  have hinter : Subgroup.zpowers x ⊓ L = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨hy_zp, hy_L⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy_zp
    have hkL : x ^ k ∈ L := by rwa [← hk] at hy_L
    let r := (k % 3 : ℤ).toNat
    have hkmod : x ^ (r : ℤ) = x ^ k := by
      have h1z : (r : ℤ) = k % 3 := Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))
      have h3z : (3 : ℤ) = (orderOf x : ℤ) := by exact_mod_cast hxord.symm
      rw [h1z, h3z, zpow_mod_orderOf]
    have hkLmod : x ^ (r : ℤ) ∈ L := by
      rw [hkmod]
      exact hkL
    have hcases : r = 0 ∨ r = 1 ∨ r = 2 := by
      have hrlt : r < 3 := by
        have h1z : (r : ℤ) = k % 3 := Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))
        have h2z : (k % 3 : ℤ) < 3 := Int.emod_lt_of_pos k (by norm_num)
        rw [← h1z] at h2z
        exact_mod_cast h2z
      interval_cases r <;> simp
    rcases hcases with h0 | h1z | h2z
    · have hk1 : x ^ k = 1 := by
        rw [← hkmod, h0]
        simp
      rw [← hk, hk1]
    · have hxL' : x ∈ L := by
        simpa [h1z] using hkLmod
      exact absurd hxL' hxL
    · have hx2L : x ^ 2 ∈ L := by
        simpa [h2z] using hkLmod
      have h4 : (x ^ 2) ^ 2 = x := by
        rw [← pow_mul]
        norm_num
        rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, hx3, one_mul]
      have h5 : (x ^ 2) ^ 2 ∈ L := pow_mem hx2L 2
      rw [h4] at h5
      exact absurd h5 hxL

  have hker' : ∀ f, ((τ f : ↥L) : G) ∈ Subgroup.zpowers x ↔
      f ∈ Subgroup.zpowers (qTwoOneVec m h3) := by
    intro f
    constructor
    · intro hx_mem
      have hx_L : ((τ f : ↥L) : G) ∈ L := (τ f).2
      have hx_bot : ((τ f : ↥L) : G) ∈ Subgroup.zpowers x ⊓ L := ⟨hx_mem, hx_L⟩
      rw [hinter] at hx_bot
      have h_eq_one : ((τ f : ↥L) : G) = 1 := by
        rwa [Subgroup.mem_bot] at hx_bot
      have h_tau_one : τ f = 1 := Subtype.ext h_eq_one
      exact (h_Tker1 f).mp h_tau_one
    · intro hf
      have h_tau_one : τ f = 1 := (h_Tker1 f).mpr hf
      rw [h_tau_one]
      exact Subgroup.one_mem _

  let φT : ↥(sumZero m 3) →* ↥(Bs ⊓ L) :=
    { toFun := fun f => ⟨((τ f : ↥L) : G), hτ.mem f, (τ f).2⟩
      map_one' := by
        apply Subtype.ext
        simp only [Subgroup.coe_one, map_one]
      map_mul' := fun f g => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, map_mul] }

  have hφT_surj : Function.Surjective φT := by
    intro x
    obtain ⟨f, hf⟩ := hrange ⟨x.val, x.2.2⟩ x.2.1
    refine ⟨f, ?_⟩
    apply Subtype.ext
    exact congrArg (fun y : ↥L => (y : G)) hf

  have hφT_ker : φT.ker = Subgroup.zpowers (qTwoOneVec m h3) := by
    ext f
    rw [MonoidHom.mem_ker]
    constructor
    · intro hf
      have h_eq : τ f = 1 := by
        apply Subtype.ext
        have h := congrArg (fun x : ↥(Bs ⊓ L) => (x : G)) hf
        simpa [φT] using h
      exact (h_Tker1 f).mp h_eq
    · intro hf
      have h_tau_one : τ f = 1 := (h_Tker1 f).mpr hf
      apply Subtype.ext
      show ((τ f : ↥L) : G) = 1
      simp [h_tau_one]

  obtain ⟨thetaT, hthetaT⟩ := qTwoLMDivCoordInner_quot h3 φT hφT_surj hφT_ker

  obtain ⟨ρ, hρ_IsHm, hρ⟩ := qTwoLMDivCoordInner_permHm m h3

  obtain ⟨θ, hθ⟩ := qTwoLMDivCoordInner_wtheta hG hBs hN h3 τ hτ.mem hrange hsplit hker'

  have hwn : ∀ n : ↥L, MulAut.conj n ∈
      Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L)) →
      (n : G) ∈ Subgroup.normalizer (Bs : Set G) :=
    fun n hn => qTwoLMDivCoordInner_wnorm hG hBs hN (by omega : 4 ≤ m) hU hsplit n hn

  have hcl := qTwoLMDivCoordInner_tclauses hG hBs hN hm h3 hU hδ hτ hrange hsplit
  have hcl1 := hcl.1
  have hcl2 := hcl.2

  have hfields := qTwoLMDivCoordInner_wfields hN h3 τ hτ.mem θ hθ ρ hρ hwn hcl1 hcl2
  obtain ⟨hnorm_perm, hperm_ind⟩ := hfields

  have normT : ∀ n : ↥L, (n : G) ∈ Subgroup.normalizer (Bs : Set G) →
      ∃ π : Equiv.Perm (Fin m), ∀ v : QTwoHm m h3,
        (n : G) * ((thetaT v : ↥(Bs ⊓ L)) : G) * (n : G)⁻¹ =
          ((thetaT (ρ π v) : ↥(Bs ⊓ L)) : G) := by
    intro n hn
    obtain ⟨π', hπ'⟩ := hcl1 n hn
    refine ⟨π', fun v => ?_⟩
    refine QuotientGroup.induction_on v fun f => ?_
    have h1 : ((thetaT (QuotientGroup.mk f) : ↥(Bs ⊓ L)) : G) = ((τ f : ↥L) : G) := by
      rw [hthetaT]
      rfl
    have h2 : ((thetaT (ρ π' (QuotientGroup.mk f)) : ↥(Bs ⊓ L)) : G) =
        ((τ (permAutV π' f) : ↥L) : G) := by
      rw [hρ, hthetaT]
      rfl
    rw [h1, h2]
    exact hπ' f

  have indT : ∀ σ : Equiv.Perm (Fin m), ∃ n : ↥L,
      (n : G) ∈ Subgroup.normalizer (Bs : Set G) ∧ ∀ v : QTwoHm m h3,
        (n : G) * ((thetaT v : ↥(Bs ⊓ L)) : G) * (n : G)⁻¹ =
          ((thetaT (ρ σ v) : ↥(Bs ⊓ L)) : G) := by
    intro σ
    obtain ⟨n, hn, hπ⟩ := hcl2 σ
    refine ⟨n, hn, fun v => ?_⟩
    refine QuotientGroup.induction_on v fun f => ?_
    have h1 : ((thetaT (QuotientGroup.mk f) : ↥(Bs ⊓ L)) : G) = ((τ f : ↥L) : G) := by
      rw [hthetaT]
      rfl
    have h2 : ((thetaT (ρ σ (QuotientGroup.mk f)) : ↥(Bs ⊓ L)) : G) =
        ((τ (permAutV σ f) : ↥L) : G) := by
      rw [hρ, hthetaT]
      rfl
    rw [h1, h2]
    exact hπ f

  refine ⟨{
    permV := ρ
    permVT := ρ
    theta := θ
    norm_perm := hnorm_perm
    perm_ind := hperm_ind
    thetaT := thetaT
    normT := normT
    indT := indT
  }, hρ_IsHm, hρ_IsHm⟩

end CFSG.StandardType.QTwo

end
