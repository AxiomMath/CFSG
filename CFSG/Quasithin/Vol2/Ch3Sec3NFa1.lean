module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFStmt
public import CFSG.Quasithin.Vol2.Ch3Sec3NFFacts
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321FC

public section

namespace CFSG.Quasithin.H13.L3321

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.QuasithinUnique.Setup.Lift CFSG.Quasithin.S152N
open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin
open scoped IsMulCommutative

@[expose] def Rm : SL2F2 := ⟨!![0, 1; 1, 1], by decide⟩

@[expose] def ga : SL4 := diagSL Rm 1

@[expose] def gb : SL4 := diagSL 1 Rm

theorem ga_pow : ga ^ 3 = 1 := by decide +kernel

theorem gb_pow : gb ^ 3 = 1 := by decide +kernel

theorem ga_mem : ga ∈ P2 := diagSL_mem _ _

theorem gb_mem : gb ∈ P2 := diagSL_mem _ _

theorem fix_nat : ∀ w : Multiplicative (FLc.Vt 4), FLc.actM ga w = w → FLc.actM gb w = w →
    w = 1 := by
  decide +kernel

theorem fix_dual : ∀ w : Multiplicative (FLc.Vt 4), FLc.actDl ga w = w → FLc.actDl gb w = w →
    w = 1 := by
  decide +kernel

theorem fix_eq_one_of_sum {V : Type} [CommGroup V] {ρ : FLc.SLt 4 →* MulAut V}
    {U₁ U₂ : Subgroup V} (hdirect : IsIntDirect U₁ U₂ ⊤)
    (D₁ : FLc.VModel 4 ρ U₁ ⊥ (Multiplicative (FLc.Vt 4)) (fun g a => FLc.actM g a))
    (D₂ : FLc.VModel 4 ρ U₂ ⊥ (Multiplicative (FLc.Vt 4)) FLc.actDl) {v : V}
    (hfa : ρ ga v = v) (hfb : ρ gb v = v) : v = 1 := by
  have hv : v ∈ U₁ ⊔ U₂ := by rw [hdirect.1]; exact Subgroup.mem_top v
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Subgroup.mem_sup.mp hv
  have split : ∀ g : FLc.SLt 4, ρ g (u₁ * u₂) = u₁ * u₂ → ρ g u₁ = u₁ ∧ ρ g u₂ = u₂ := by
    intro g hg
    have h1 : ρ g u₁ ∈ U₁ := D₁.inv g u₁ hu₁
    have h2 : ρ g u₂ ∈ U₂ := D₂.inv g u₂ hu₂
    rw [map_mul] at hg
    have h3 : ρ g u₁ * u₁⁻¹ ∈ U₁ ⊓ U₂ := by
      refine ⟨U₁.mul_mem h1 (U₁.inv_mem hu₁), ?_⟩
      have : ρ g u₁ * u₁⁻¹ = u₂ * (ρ g u₂)⁻¹ := by
        have e : ρ g u₁ = u₁ * u₂ * (ρ g u₂)⁻¹ := by
          rw [← hg]; group
        rw [e, mul_assoc u₁ u₂]
        exact mul_inv_cancel_comm _ _
      rw [this]
      exact U₂.mul_mem hu₂ (U₂.inv_mem h2)
    rw [hdirect.2, Subgroup.mem_bot, mul_inv_eq_one] at h3
    refine ⟨h3, ?_⟩
    rw [h3] at hg
    exact mul_left_cancel hg
  obtain ⟨ha₁, ha₂⟩ := split ga hfa
  obtain ⟨hb₁, hb₂⟩ := split gb hfb
  have key₁ : u₁ = 1 := by
    have e : ∀ g : FLc.SLt 4, ρ g u₁ = u₁ →
        FLc.actM g (D₁.β ⟨u₁, hu₁⟩) = D₁.β ⟨u₁, hu₁⟩ := by
      intro g hg
      have hu : ρ g u₁ ∈ U₁ := D₁.inv g u₁ hu₁
      have := D₁.equiv g ⟨u₁, hu₁⟩ hu
      have e2 : (⟨ρ g u₁, hu⟩ : ↥U₁) = ⟨u₁, hu₁⟩ := Subtype.ext hg
      rw [e2] at this
      exact this.symm
    have h1 := fix_nat _ (e ga ha₁) (e gb hb₁)
    have := D₁.ker ⟨u₁, hu₁⟩ h1
    simpa using this
  have key₂ : u₂ = 1 := by
    have e : ∀ g : FLc.SLt 4, ρ g u₂ = u₂ →
        FLc.actDl g (D₂.β ⟨u₂, hu₂⟩) = D₂.β ⟨u₂, hu₂⟩ := by
      intro g hg
      have hu : ρ g u₂ ∈ U₂ := D₂.inv g u₂ hu₂
      have := D₂.equiv g ⟨u₂, hu₂⟩ hu
      have e2 : (⟨ρ g u₂, hu⟩ : ↥U₂) = ⟨u₂, hu₂⟩ := Subtype.ext hg
      rw [e2] at this
      exact this.symm
    have h1 := fix_dual _ (e ga ha₂) (e gb hb₂)
    have := D₂.ker ⟨u₂, hu₂⟩ h1
    simpa using this
  rw [key₁, key₂, one_mul]

theorem exists_odd_lift {G : Type} [Group G] [Finite G] {L : Subgroup G} (α : ↥L →* SL4)
    (hα : Function.Surjective α) {g : SL4} (hg : g ^ 3 = 1) :
    ∃ y : ↥L, Odd (orderOf (y : G)) ∧ α y = g := by
  obtain ⟨l, rfl⟩ := hα g
  have hn : orderOf l ≠ 0 := (orderOf_pos l).ne'
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  obtain ⟨q, hq⟩ : ∃ q : ℕ, 4 ^ k = 3 * q + 1 := by
    have : 4 ^ k % 3 = 1 := by
      rw [Nat.pow_mod]; norm_num
    exact ⟨4 ^ k / 3, by omega⟩
  refine ⟨l ^ (4 ^ k), ?_, ?_⟩
  · have hpow : (l ^ 4 ^ k) ^ m = 1 := by
      rw [← pow_mul]
      have : 4 ^ k * m = orderOf l * 2 ^ k := by
        rw [hkm, show (4 : ℕ) = 2 * 2 from rfl, mul_pow]; ring
      rw [this, pow_mul, pow_orderOf_eq_one, one_pow]
    have hdvd : orderOf (l ^ 4 ^ k) ∣ m := orderOf_dvd_of_pow_eq_one hpow
    rw [Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat hm hdvd
  · rw [map_pow, hq, pow_add, pow_mul, hg, one_pow, one_mul, pow_one]

theorem obl3_3_13D12NF_a1_of (h36 : A36ForSQTK) (h7 : Stmt3_3_7) (h14 : Stmt3_3_14)
    (he : Step3_3_21e) : Obl3_3_13D12NF_a1 := by
  intro G _ _ T M L D H K h hP hH hHLT hwr hO hK hKq hYK hTK hKf _ hq
  obtain ⟨hTL, ⟨e⟩, hc, hmod, hout, α, ρ, U₁, U₂, hαs, hαk, hαU, hαv, hdirect, ⟨D₁⟩, ⟨D₂⟩,
    rfl⟩ := hP
  have hmod' : Mod3321 T L := ⟨hc, Or.inr hmod⟩
  rw [commV_eq_top h7 h14 he h ⟨e⟩ hmod'] at hdirect
  have hYC : oTwoUpper (L3316.liftPre α P2 ⊔ T) ≤
      Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    hYK.trans (nf_conjClosure_le_centralizer_Z h36 h ⟨hH.1.trans le_sup_left, hO⟩ hK hKf)
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (quasithinOmegaOneCenter_ne_bot h.sylow.1 h.toSetup331.T_ne_bot)
  have hzZ : (a : G) ∈ quasithinOmegaOneCenter T := a.2
  have hz1 : (a : G) ≠ 1 := fun h1 => ha (Subtype.ext h1)
  have hzV : (a : G) ∈ vPlus L T := le_conjClosure _ _ hzZ
  have hlift : ∀ g : SL4, g ^ 3 = 1 → g ∈ P2 → ∃ y : ↥L, α y = g ∧
      (y : G) ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    intro g hg3 hgP
    obtain ⟨y, hyo, hyg⟩ := exists_odd_lift α hαs hg3
    have hyH : (y : G) ∈ L3316.liftPre α P2 ⊔ T :=
      Subgroup.mem_sup_left ⟨y, show α y ∈ P2 by rw [hyg]; exact hgP, rfl⟩
    exact ⟨y, hyg, hYC (mem_oTwoUpper_of_odd hyH hyo)⟩
  obtain ⟨y₁, hy₁, hy₁C⟩ := hlift ga ga_pow ga_mem
  obtain ⟨y₂, hy₂, hy₂C⟩ := hlift gb gb_pow gb_mem
  have hfix : ∀ (y : ↥L) (g : SL4), α y = g →
      (y : G) ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
      ρ g ⟨a, hzV⟩ = ⟨a, hzV⟩ := by
    intro y g hyg hyC
    have hyN : (y : G) ∈ Subgroup.normalizer (vPlus L T : Set G) :=
      L3317.le_normalizer_vPlus h y.2
    rw [← hyg, hαv y hyN]
    apply Subtype.ext
    rw [FLc.conjAct_coe hyN]
    have h1 : (a : G) * (y : G) = (y : G) * (a : G) := Subgroup.mem_centralizer_iff.mp hyC a hzZ
    rw [← h1, mul_assoc, mul_inv_cancel, mul_one]
  have hv1 : (⟨a, hzV⟩ : ↥(vPlus L T)) = 1 :=
    fix_eq_one_of_sum hdirect D₁ D₂ (hfix y₁ ga hy₁ hy₁C) (hfix y₂ gb hy₂ hy₂C)
  exact hz1 (congrArg Subtype.val hv1)

end CFSG.Quasithin.H13.L3321
