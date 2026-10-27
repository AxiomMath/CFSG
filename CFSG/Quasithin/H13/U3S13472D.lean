module

public import CFSG.Quasithin.H13.U3S13472C
public import CFSG.Quasithin.Vol2.Ch10SecV1SI

public section

namespace CFSG.Quasithin.H13.U3.P2

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
variable {S : A6.Setting134 G T L V} {H₁ H₂ : Subgroup G}

namespace SettingX

variable {D : Data2 S H₁ H₂} {X : Subgroup G}

theorem X_le_normalizer (hS : SettingX D X) :
    X ≤ normalizer (conjClosure (quasithinOmegaOneCenter T) X : Set G) := hS.reduced.2.1

theorem isMulCommutative (hS : SettingX D X) :
    IsMulCommutative ↥(conjClosure (quasithinOmegaOneCenter T) X) := hS.reduced.2.2.1.1

theorem inf_centralizer (hS : SettingX D X) :
    D.K₀ ⊓ centralizer (conjClosure (quasithinOmegaOneCenter T) X : Set G) = pCoreOf 2 D.K₀ := by
  apply le_antisymm
  · refine QuasithinUnique.le_pCoreOf_of_le_normalizer inf_le_left (fun k hk => ?_) ?_
    · exact mem_normalizer_inf_of (Subgroup.le_normalizer hk)
        (mem_normalizer_centralizer_of_mem (hS.X_le_normalizer (hS.KX hk)))
    · exact S.h13.sylow.1.to_le ((inf_le_inf_right _ hS.KX).trans hS.inf_centralizer_le_T)
  · exact le_inf (pCoreOf_le 2 _)
      ((pCoreOf_le_pCoreOf hS.KX hS.hNX).trans hS.pCoreOf_le_centralizer)

@[expose] noncomputable def conjOn (Y W : Subgroup G) (hY : Y ≤ normalizer (W : Set G)) :
    ↥Y →* MulAut ↥W :=
  (conjAct W).comp (Subgroup.inclusion hY)

omit [Finite G] in
theorem range_conjOn {Y W : Subgroup G} (hY : Y ≤ normalizer (W : Set G)) :
    (conjOn Y W hY).range = autOn Y W := by
  rw [conjOn, MonoidHom.range_comp, Subgroup.inclusion_range]
  rfl

omit [Finite G] in
theorem mem_ker_conjOn {Y W : Subgroup G} (hY : Y ≤ normalizer (W : Set G)) (y : ↥Y) :
    y ∈ (conjOn Y W hY).ker ↔ (y : G) ∈ centralizer (W : Set G) := by
  rw [MonoidHom.mem_ker, mem_centralizer_iff]
  constructor
  · intro h w hw
    have h1 := congrArg (fun φ : MulAut ↥W => ((φ ⟨w, hw⟩ : ↥W) : G)) h
    simp only [conjOn, MonoidHom.comp_apply, MulAut.one_apply] at h1
    rw [conjAct, MonoidHom.comp_apply, normalizerMonoidHom_apply_apply_coe] at h1
    change (y : G) * w * (y : G)⁻¹ = w at h1
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  · intro h
    ext w
    simp only [conjOn, MonoidHom.comp_apply, MulAut.one_apply]
    rw [conjAct, MonoidHom.comp_apply, normalizerMonoidHom_apply_apply_coe]
    change (y : G) * w * (y : G)⁻¹ = w
    rw [← h w w.2, mul_inv_cancel_right]

theorem nonempty_equiv (hS : SettingX D X) :
    Nonempty (↥(autOn D.K₀ (conjClosure (quasithinOmegaOneCenter T) X)) ≃* SL3.S) := by
  set W := conjClosure (quasithinOmegaOneCenter T) X with hW
  have hKN : D.K₀ ≤ normalizer (W : Set G) := hS.KX.trans hS.X_le_normalizer
  have hker : (conjOn D.K₀ W hKN).ker = CFSG.Open.pCore 2 ↥D.K₀ := by
    ext k
    rw [mem_ker_conjOn, ← pCoreOf_subgroupOf_eq_pCore, mem_subgroupOf,
      ← hS.inf_centralizer]
    exact ⟨fun h => ⟨k.2, h⟩, fun h => h.2⟩
  obtain ⟨φ, hφ, hφker⟩ := D.hK
  exact ⟨(MulEquiv.subgroupCongr (range_conjOn hKN)).symm.trans
    ((QuotientGroup.quotientKerEquivRange _).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (hker.trans hφker.symm)).trans
        (QuotientGroup.quotientKerEquivOfSurjective φ hφ)))⟩

theorem Z_mem_commV (hS : SettingX D X) {z : G} (hz : z ∈ quasithinOmegaOneCenter T) :
    haveI := hS.isMulCommutative
    (⟨z, le_conjClosure _ _ hz⟩ : ↥(conjClosure (quasithinOmegaOneCenter T) X)) ∈
      commV (autOn D.K₀ (conjClosure (quasithinOmegaOneCenter T) X)) := by
  have := hS.isMulCommutative
  set W := conjClosure (quasithinOmegaOneCenter T) X with hW
  have hKN : D.K₀ ≤ normalizer (W : Set G) := hS.KX.trans hS.X_le_normalizer
  have hle : ⁅D.K₀, W⁆ ≤ (commV (autOn D.K₀ W)).map W.subtype := by
    rw [commutator_le]
    intro k hk w hw
    refine ⟨conjAct W ⟨k, hKN hk⟩ ⟨w, hw⟩ * (⟨w, hw⟩ : ↥W)⁻¹,
      Subgroup.subset_closure ⟨_, Setup.mem_autOn_iff.2 ⟨⟨k, hKN hk⟩, hk, rfl⟩, ⟨w, hw⟩, rfl⟩,
      ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [conjAct, MonoidHom.comp_apply, normalizerMonoidHom_apply_apply_coe]
    rfl
  have hz' : z ∈ ⁅D.K₀, W⁆ := commutator_mono le_rfl hS.V0_le (D.Z_le_commutator hz)
  obtain ⟨u, hu, hu'⟩ := hle hz'
  have : u = ⟨z, le_conjClosure _ _ hz⟩ := Subtype.ext hu'
  rw [← this]
  exact hu

theorem isPGroup_of_fix (hS : SettingX D X)
    {R : Subgroup (MulAut ↥(conjClosure (quasithinOmegaOneCenter T) X))}
    (hRX : R ≤ autOn X (conjClosure (quasithinOmegaOneCenter T) X))
    (hfix : ∀ r ∈ R, ∀ (z : G) (hz : z ∈ quasithinOmegaOneCenter T),
      r ⟨z, le_conjClosure _ _ hz⟩ = ⟨z, le_conjClosure _ _ hz⟩) : IsPGroup 2 ↥R := by
  rintro ⟨r, hr⟩
  obtain ⟨g, hgX, rfl⟩ := Setup.mem_autOn_iff.1 (hRX hr)
  have hgZ : (g : G) ∈ X ⊓ centralizer (quasithinOmegaOneCenter T : Set G) := by
    refine ⟨hgX, mem_centralizer_iff.2 fun z hz => ?_⟩
    have h1 := congrArg Subtype.val (hfix _ hr z hz)
    rw [conjAct, MonoidHom.comp_apply, normalizerMonoidHom_apply_apply_coe] at h1
    change (g : G) * z * (g : G)⁻¹ = z at h1
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  rw [hS.hXZ] at hgZ
  obtain ⟨n, hn⟩ := S.h13.sylow.1 ⟨_, hgZ⟩
  refine ⟨n, Subtype.ext ?_⟩
  have hg1 : g ^ 2 ^ n = 1 := Subtype.ext (by simpa using congrArg Subtype.val hn)
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← map_pow, hg1, map_one]

theorem pRank_le (hS : SettingX D X) :
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥(autOn X (conjClosure (quasithinOmegaOneCenter T) X))) ≤
      2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set W := conjClosure (quasithinOmegaOneCenter T) X with hW
  have hSQ : SQTKGroup ↥X :=
    sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian hS.hX.2
  have h2 := hSQ.1 3 Nat.prime_three (by norm_num)
  set c := conjOn X W hS.X_le_normalizer with hc
  have hker2 : IsPGroup 2 ↥c.ker := by
    rintro ⟨k, hk⟩
    have hkT : (k : G) ∈ T := hS.inf_centralizer_le_T ⟨k.2, (mem_ker_conjOn _ k).1 hk⟩
    obtain ⟨n, hn⟩ := S.h13.sylow.1 ⟨_, hkT⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hn
  have hN : ¬ 3 ∣ Nat.card ↥c.ker := by
    obtain ⟨m, hm⟩ := hker2.exists_card_eq
    rw [hm]
    intro h
    have := (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  have e1 := (QuotientGroup.quotientKerEquivRange c).trans
    (MulEquiv.subgroupCongr (range_conjOn hS.X_le_normalizer))
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e1,
    CFSG.SectionRank.pRank_quotient_eq c.ker hN]
  exact h2

theorem false_of_threeRank2 (hS : SettingX D X)
    {R : Subgroup (MulAut ↥(conjClosure (quasithinOmegaOneCenter T) X))}
    (hRX : R ≤ autOn X (conjClosure (quasithinOmegaOneCenter T) X))
    (hRC : ∀ r ∈ R, ∀ k ∈ autOn D.K₀ (conjClosure (quasithinOmegaOneCenter T) X),
      r * k = k * r) (h3 : FFC.ThreeRank2 ↥R) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hS.nonempty_equiv
  have hKX : autOn D.K₀ (conjClosure (quasithinOmegaOneCenter T) X) ≤
      autOn X (conjClosure (quasithinOmegaOneCenter T) X) :=
    InternalSec.autOn_le_autOn_of_le hS.KX
  obtain ⟨k, hek⟩ : ∃ k, e k = SL3.w3 := ⟨e.symm SL3.w3, e.apply_symm_apply _⟩
  have hk3 : k ^ 3 = 1 := e.injective (by
    rw [map_pow, hek, map_one]
    decide +kernel)
  have hk1 : k ≠ 1 := fun h => by
    have h1 := congrArg e h
    rw [hek, map_one] at h1
    revert h1
    decide +kernel
  have hkc : ¬ ∀ l ∈ autOn D.K₀ (conjClosure (quasithinOmegaOneCenter T) X),
      ((k : ↥(autOn D.K₀ (conjClosure (quasithinOmegaOneCenter T) X))) :
        MulAut ↥(conjClosure (quasithinOmegaOneCenter T) X)) * l = l * k := by
    intro h
    apply hk1
    have hcen : e k ∈ Subgroup.center SL3.S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h2 : k * e.symm g = e.symm g * k := Subtype.ext (h _ (e.symm g).2)
      have h3 := congrArg e h2
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h3
      exact h3.symm
    rw [Data2.center_SL3, mem_bot] at hcen
    exact e.injective (hcen.trans (map_one e).symm)
  obtain ⟨x, y, hx1, hx3, hy3, hxy, hyx⟩ := h3
  let ι : ↥R → ↥(autOn X (conjClosure (quasithinOmegaOneCenter T) X)) := fun r => ⟨r, hRX r.2⟩
  let k' : ↥(autOn X (conjClosure (quasithinOmegaOneCenter T) X)) := ⟨k, hKX k.2⟩
  have hιmul : ∀ r r' : ↥R, ι (r * r') = ι r * ι r' := fun r r' => Subtype.ext rfl
  have hιpow : ∀ (r : ↥R) (n : ℕ), (ι r) ^ n = ι (r ^ n) := fun r n => Subtype.ext rfl
  have hι1 : ι 1 = 1 := Subtype.ext rfl
  have hιinj : ∀ r r' : ↥R, ι r = ι r' → r = r' := fun r r' h =>
    Subtype.ext (congrArg
      (fun z : ↥(autOn X (conjClosure (quasithinOmegaOneCenter T) X)) =>
        (z : MulAut ↥(conjClosure (quasithinOmegaOneCenter T) X))) h)
  have hcomm : ∀ r : ↥R, Commute (ι r) k' := fun r => Subtype.ext (hRC r r.2 k k.2)
  have h3le := Vol2.Ch10.V1C.A319.three_le_pRank_of_gens (p := 3) (x := ι x) (z := ι y) (c := k')
    (by rw [hιpow, hx3, hι1]) (by rw [hιpow, hy3, hι1])
    (Subtype.ext (by simpa using congrArg Subtype.val hk3))
    (by rw [Commute, SemiconjBy, ← hιmul, ← hιmul, hxy]) (hcomm x) (hcomm y)
    (fun h => hx1 (hιinj x 1 (h.trans hι1.symm)))
    (fun n h => hyx (Subgroup.mem_zpowers_iff.2 ⟨n, by
      rw [zpow_natCast]
      exact hιinj _ _ ((hιpow x n).symm.trans h)⟩))
    (fun m n h => hkc fun l hl => by
      rw [hιpow, hιpow, ← hιmul] at h
      have h1 : ((k : ↥(autOn D.K₀ (conjClosure (quasithinOmegaOneCenter T) X))) :
          MulAut ↥(conjClosure (quasithinOmegaOneCenter T) X)) =
          ((x ^ m * y ^ n : ↥R) : MulAut ↥(conjClosure (quasithinOmegaOneCenter T) X)) :=
        (congrArg Subtype.val h).symm
      rw [h1]
      exact hRC _ (x ^ m * y ^ n).2 l hl)
  have := hS.pRank_le
  omega

end SettingX

end CFSG.Quasithin.H13.U3.P2
