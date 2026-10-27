module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch4Sec3L4313
public import CFSG.Quasithin.Vol2.Ch4Sec3L4314R

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank Vol2.KGNat
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uMat uSL coe_uSL)
open scoped MatrixGroups Matrix Pointwise

namespace SL3Pt

theorem eq_one_of_pow_two_pow_eq_one {F : Type} [Field F] [CharP F 2] {c : F} {k : ℕ}
    (h : c ^ 2 ^ k = 1) : c = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := sub_pow_char_pow (p := 2) c 1 k
  rw [h, one_pow, sub_self] at h1
  exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero k two_ne_zero)).mp h1)

end SL3Pt

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem L4314.comm_of_injective {V : Subgroup G} {A : Type} [CommGroup A] {f : ↥V →* A}
    (hf : Function.Injective f) : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
  intro a ha b hb
  have h := hf (show f (⟨a, ha⟩ * ⟨b, hb⟩) = f (⟨b, hb⟩ * ⟨a, ha⟩) by
    rw [map_mul, map_mul, mul_comm])
  exact congrArg Subtype.val h

namespace Setting4311

variable {T M L : Subgroup G} {n : ℕ} {I H K : Subgroup G} {t : G} {m : ℕ} {F : Type} [Field F]
  [Fintype F] {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)}
  {W' : Submodule F (Fin 3 → F)} {ZS K₂ R₂ : Subgroup G} {μ : Fˣ} {y : G}
variable (s : Setting4311 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y)
include s

theorem S_inf_K_le_centralizer_ZS : T ⊓ H ⊓ K ≤ Subgroup.centralizer (ZS : Set G) := by
  have : CharP F 2 := s.charP
  intro x hx
  have hxK : x ∈ K := hx.2
  rw [s.mem_centralizer_ZS_iff hxK, mem_stE0]
  obtain ⟨z₀, hz₀⟩ := s.β_bij.2 (Multiplicative.ofAdd ![1, 0, 0])
  have hz₀Z : (z₀ : G) ∈ ZS := (s.ZS_iff z₀).mpr ⟨1, by rw [hz₀, toAdd_ofAdd, one_smul]⟩
  have hxN : x ∈ Subgroup.normalizer (ZS : Set G) := s.T_le_normalizer_ZS hx.1.1
  have hv : x * z₀ * x⁻¹ ∈ ZS := (Subgroup.mem_normalizer_iff.mp hxN z₀).mp hz₀Z
  let v : ↥(u4311 I K) := ⟨x * z₀ * x⁻¹, s.ZS_le_U hv⟩
  obtain ⟨c, hc⟩ := (s.ZS_iff v).mp hv
  have h1 := s.β_act ⟨x, hxK⟩ z₀ v rfl
  rw [hz₀, toAdd_ofAdd, hc] at h1
  set A := ((α ⟨x, hxK⟩ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hA
  have hpow : ∀ j : ℕ, (A ^ j) *ᵥ ![1, 0, 0] = c ^ j • ![(1 : F), 0, 0] := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, ← h1, smul_smul, pow_succ,
        mul_comm]
  obtain ⟨a, ha⟩ := s.sk.base.hyp.sylow.1 ⟨x, hx.1.1⟩
  have hxa : (⟨x, hxK⟩ : ↥K) ^ 2 ^ a = 1 := Subtype.ext (by simpa using congrArg Subtype.val ha)
  have hAa : A ^ 2 ^ a = 1 := by
    have h2 : α (⟨x, hxK⟩ ^ 2 ^ a) = 1 := by rw [hxa, map_one]
    rw [map_pow] at h2
    have h3 := congrArg (fun g : ↥(StatedSL 3 F) => ((g : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F)) h2
    simpa [hA] using h3
  have hc1 : c ^ 2 ^ a = 1 := by
    have h4 := hpow (2 ^ a)
    rw [hAa, Matrix.one_mulVec] at h4
    have h5 := congrFun h4 0
    simpa using h5.symm
  rw [← h1, SL3Pt.eq_one_of_pow_two_pow_eq_one hc1, one_smul]

theorem isSylowTwoOf_S_inf_K (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) : IsSylowTwoOf (T ⊓ H ⊓ K) K :=
  A4.isSylowTwoOf_inf_normal (s.isSylowTwoOf_S_sup hR hC h37 h38 h39) le_sup_left
    (_root_.sup_le (fun _ hx => Subgroup.le_normalizer hx) s.sk.S_le_normalizer)

theorem R₂_le_S_inf_K (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) : R₂ ≤ T ⊓ H ⊓ K := by
  refine le_inf ?_ ?_
  · have hSsylH := s.sk.base.isSylowTwoOf_S_H hR hC h37 h38 h39
    have hKSH : K₂ ⊔ T ⊓ H ≤ H :=
      _root_.sup_le (s.K₂_le_K.trans (le_of_mem_cComp s.sk.cComp)) inf_le_right
    have hS : IsSylowTwoOf (T ⊓ H) (K₂ ⊔ T ⊓ H) := by
      refine ⟨le_sup_right, hSsylH.2.1, fun h2 => hSsylH.2.2 ?_⟩
      have h1 := Subgroup.relIndex_mul_relIndex (T ⊓ H) (K₂ ⊔ T ⊓ H) H le_sup_right hKSH
      exact h2.trans (Dvd.intro _ h1)
    rw [s.R₂_eq]
    exact pCoreOf_two_le_of_isSylowTwoOf hS
  · rw [s.R₂_eq_P₀ h135 hR hC h37 h38 h39]
    exact s.P₀_le.trans inf_le_left

theorem centerOf_eq_ZS (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) {X : Subgroup G} (hRX : R₂ ≤ X)
    (hXK : X ≤ K) (hXC : X ≤ Subgroup.centralizer (ZS : Set G)) : centerOf X = ZS := by
  have hQK := s.pCoreOf_K_eq h135 hR hC h37 h38 h39
  have hP₀ := s.R₂_eq_P₀ h135 hR hC h37 h38 h39
  have hQX : q4311 I K ≤ X := by
    rw [← hQK]
    exact (s.pCoreOf_K_le_P₀.trans hP₀.ge).trans hRX
  have hUQ : u4311 I K ≤ q4311 I K := inf_le_left
  apply le_antisymm
  · intro z hz
    have hzK : z ∈ K := hXK hz.1
    have hzCQ : z ∈ Subgroup.centralizer ((q4311 I K : Subgroup G) : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hQX) hz.2
    have hzQ : z ∈ q4311 I K := by
      rw [← hQK]
      refine s.charTwo ⟨hzK, ?_⟩
      rw [hQK]
      exact hzCQ
    have hzU : z ∈ u4311 I K := ⟨hzQ, hzCQ⟩
    refine (s.ZS_iff ⟨z, hzU⟩).mpr ?_
    have hfix : ∀ a b : F, uMat a b 0 *ᵥ Multiplicative.toAdd (β ⟨z, hzU⟩) =
        Multiplicative.toAdd (β ⟨z, hzU⟩) := by
      intro a b
      obtain ⟨r, hr⟩ := s.modO2.1 (specialLinearGroupEquivStatedSL 3 F (uSL a b 0))
      have hrm : ((α r : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = uMat a b 0 := by
        rw [hr, specialLinearGroupEquivStatedSL_coe, coe_uSL]
      have hrR : (r : G) ∈ R₂ := by
        rw [hP₀]
        exact mem_P₀.mpr ⟨r.2, show α r ∈ radE0 F from SL3Pt.mem_radE0.mpr ⟨a, b, hrm⟩⟩
      have hcomm : (r : G) * z = z * r := Subgroup.mem_centralizer_iff.mp hz.2 _ (hRX hrR)
      have h1 := s.β_act r ⟨z, hzU⟩ ⟨z, hzU⟩ (by
        show z = r * z * (r : G)⁻¹
        rw [hcomm, mul_inv_cancel_right])
      rw [hrm] at h1
      exact h1.symm
    have hv1 : Multiplicative.toAdd (β ⟨z, hzU⟩) 1 = 0 := by
      have h0 := congrFun (hfix 1 0) 0
      rw [SL3Pt.uMat_mulVec] at h0
      simp only [Matrix.cons_val_zero, one_mul, zero_mul, add_zero] at h0
      linear_combination h0
    have hv2 : Multiplicative.toAdd (β ⟨z, hzU⟩) 2 = 0 := by
      have h0 := congrFun (hfix 0 1) 0
      rw [SL3Pt.uMat_mulVec] at h0
      simp only [Matrix.cons_val_zero, one_mul, zero_mul, add_zero] at h0
      linear_combination h0
    exact ⟨_, SL3Pt.eq_smul_e0 hv1 hv2⟩
  · intro z hz
    refine ⟨hQX (hUQ (s.ZS_le_U hz)), Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp (hXC hx) z hz).symm

theorem sq_eq_one_of_mem_U {u : G} (hu : u ∈ u4311 I K) : u ^ 2 = 1 := by
  have : CharP F 2 := s.charP
  have h1 : β (⟨u, hu⟩ ^ 2) = 1 := by
    rw [map_pow]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, two_nsmul, CharTwo.add_self_eq_zero]
  have h2 : (⟨u, hu⟩ : ↥(u4311 I K)) ^ 2 = 1 := s.β_bij.1 (h1.trans (map_one β).symm)
  simpa using congrArg Subtype.val h2

theorem omegaOneCenterOf_S_inf_K (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    omegaOneCenterOf (T ⊓ H ⊓ K) = ZS := by
  rw [omegaOneCenterOf, s.centerOf_eq_ZS h135 hR hC h37 h38 h39
    (s.R₂_le_S_inf_K h135 hR hC h37 h38 h39) inf_le_right s.S_inf_K_le_centralizer_ZS, omegaOneOf]
  apply le_antisymm
  · exact (Subgroup.closure_le _).mpr fun x hx => hx.1
  · intro z hz
    exact Subgroup.subset_closure ⟨hz, s.sq_eq_one_of_mem_U (s.ZS_le_U hz)⟩

theorem c134Q_K_eq (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) : c134Q K K = q4311 I K := by
  rw [c134Q, s.pCoreOf_K_eq h135 hR hC h37 h38 h39]
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha k hk
    have h2 : k * a⁻¹ * k⁻¹ ∈ q4311 I K :=
      (Subgroup.mem_normalizer_iff.mp (s.dualQ.1 hk) a⁻¹).mp (Subgroup.inv_mem _ ha)
    rw [commutatorElement_def]
    have h3 := Subgroup.mul_mem _ ha h2
    simpa [mul_assoc] using h3
  · calc q4311 I K = ⁅q4311 I K, Subgroup.zpowers y⁆ := s.q4311_eq_commutator
      _ ≤ ⁅q4311 I K, K⁆ := Subgroup.commutator_mono le_rfl s.Y_le_K

theorem q4311_not_comm : ¬ ∀ a ∈ q4311 I K, ∀ b ∈ q4311 I K, a * b = b * a := by
  intro hab
  obtain ⟨-, -, β₂, hβ₂s, hβ₂k, -⟩ := s.dualQ
  have htriv : ∀ q : ↥(q4311 I K), β₂ q = 1 := by
    intro q
    rw [← MonoidHom.mem_ker, hβ₂k, Subgroup.mem_subgroupOf]
    exact ⟨q.2, Subgroup.mem_centralizer_iff.mpr fun y hy => hab y hy q q.2⟩
  obtain ⟨q, hq⟩ := hβ₂s (Multiplicative.ofAdd (fun _ _ => 1))
  rw [htriv q] at hq
  have := congrFun (congrFun (congrArg Multiplicative.toAdd hq) 0) 0
  simp at this

end Setting4311

end CFSG.Quasithin.H13.Ch4
