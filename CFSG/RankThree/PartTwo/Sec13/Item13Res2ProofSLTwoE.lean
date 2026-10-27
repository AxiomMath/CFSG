module

public import CFSG.RankThree.PartTwo.Sec13.Item13Res2ProofSLTwo
public import CFSG.RankThree.PartTwo.Sec13.Item13Res2ProofCube
import CFSG.RankThree.PartTwo.Sec13.Item13Res2ProofCubeLift
public import CFSG.RankThree.PartTwo.Sec13.Item131bProofE
import CFSG.RankThree.PartTwo.Sec13.Item13ResProofTypes
import CFSG.RankThree.PartTwo.Sec13.Item131Facts

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Step131bSLTwoInEU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L → Sec4.IsSLThreePiTwo (lBarA c L A) →
    (∃ (f : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ f) ^ 2 ∧
      2 ^ f % 3 = 2 ∧
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ f) K)) →
    ∀ E : Subgroup G, E ≤ (L ⊔ A) ⊓ Subgroup.normalizer (A : Set G) →
      CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
      ¬ IsCyclic (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) →
      ¬ IsCyclic (E ⊓ L : Subgroup G) → E ∈ partTwoE G

namespace Res2Proof

open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial
open Matrix

section Root

variable {K : Type} [Field K]

@[expose] def rootU (r : K) : GL (Fin 3) K :=
  ⟨!![1, r, 0; 0, 1, 0; 0, 0, 1], !![1, -r, 0; 0, 1, 0; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]⟩

theorem coe_rootU (r : K) :
    ((rootU r : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![1, r, 0; 0, 1, 0; 0, 0, 1] :=
  rfl

theorem rootU_mul (r s : K) : rootU r * rootU s = rootU (r + s) := by
  apply Units.ext
  rw [Units.val_mul, coe_rootU, coe_rootU, coe_rootU]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, add_comm]

theorem rootU_zero : rootU (0 : K) = 1 := by
  apply Units.ext
  rw [coe_rootU, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [one_apply]

@[expose] def rootUHom : Multiplicative K →* GL (Fin 3) K where
  toFun r := rootU (Multiplicative.toAdd r)
  map_one' := rootU_zero
  map_mul' r s := by rw [rootU_mul]; rfl

theorem rootUHom_apply (r : Multiplicative K) : rootUHom r = rootU (Multiplicative.toAdd r) :=
  rfl

theorem det_rootU (r : K) : ((rootU r : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [coe_rootU, det_fin_three]
  simp

theorem diagUnits_conj_rootU (a b c : Kˣ) (r : K) :
    diagUnits a b c * rootU r * (diagUnits a b c)⁻¹ = rootU ((a : K) * (b⁻¹ : Kˣ) * r) := by
  have hinv : (diagUnits a b c)⁻¹ = diagUnits a⁻¹ b⁻¹ c⁻¹ := by
    rw [inv_eq_iff_mul_eq_one, diagUnits_mul, mul_inv_cancel, mul_inv_cancel, mul_inv_cancel,
      diagUnits_self_eq_scalar, map_one]
  rw [hinv]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagUnits, coe_diagUnits, coe_rootU, coe_rootU]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, diagonal, mul_comm, mul_left_comm]

end Root

section TwoSubgroup

variable {X : Type} [Group X] {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem sLTwoData_exists_two_subgroup [Finite X] (D : SLTwoData X π p f K) {z : X}
    (hz : z ∈ D.L₀)
    (hz3 : z ^ 3 = 1) (hzC : z ∉ Subgroup.centralizer (D.L₀ : Set X)) (hpπ : p ≠ 2 ∨ π = true) :
    ∃ R : Subgroup X, R ≤ D.L₀ ∧ R ≠ ⊥ ∧ IsPGroup 2 R ∧
      z ∈ Subgroup.normalizer (R : Set X) := by
  have hK := D.piField
  have hq := D.modThree
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  set zL : D.L₀ := ⟨z, hz⟩ with hzL
  have hεL : ((D.e zL : slPi π 3 (p ^ f) K) : GL (Fin 3) K) ∈ slPi π 3 (p ^ f) K := (D.e zL).2
  have hzL3 : zL ^ 3 = 1 := Subtype.ext (by simp [hzL, hz3])
  have hε3 : ((D.e zL : slPi π 3 (p ^ f) K) : GL (Fin 3) K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, hzL3, map_one, Subgroup.coe_one]
  have hεZ : ((D.e zL : slPi π 3 (p ^ f) K) : GL (Fin 3) K) ∉ zPi π 3 (p ^ f) K := by
    intro hεZ
    apply hzC
    have hS := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hεZ
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have h1 : D.e ⟨w, hw⟩ * D.e zL = D.e zL * D.e ⟨w, hw⟩ :=
      Subtype.ext (commute_of_mem_statedScalars hS _)
    have h2 : (⟨w, hw⟩ : D.L₀) * zL = zL * ⟨w, hw⟩ :=
      D.e.injective (by rw [map_mul, map_mul, h1])
    exact congrArg Subtype.val h2
  have hε1 : ((D.e zL : slPi π 3 (p ^ f) K) : GL (Fin 3) K) ≠ 1 :=
    fun h => hεZ (h ▸ one_mem _)
  obtain ⟨g, hgH, hgD⟩ := rank3II_4_10_three hK hq hτ hτ1 hεL hεZ (orderOf_eq_prime hε3 hε1)
  have hlift : ∀ s ∈ slPi π 3 (p ^ f) K, ∃ w : D.L₀,
      g⁻¹ * (D.e w : GL (Fin 3) K) * g = s := by
    intro s hs
    refine ⟨D.e.symm ⟨g * s * g⁻¹, mul_mul_inv_mem_slPi hπ hgH hs⟩, ?_⟩
    rw [MulEquiv.apply_symm_apply]
    group
  have hinj : ∀ w w' : D.L₀, g⁻¹ * (D.e w : GL (Fin 3) K) * g =
      g⁻¹ * (D.e w' : GL (Fin 3) K) * g → w = w' := by
    intro w w' h
    have h1 : ((D.e w : slPi π 3 (p ^ f) K) : GL (Fin 3) K) = D.e w' := by
      have := congrArg (fun m => g * m * g⁻¹) h
      simpa [mul_assoc] using this
    exact D.e.injective (Subtype.ext h1)
  have hmapmul : ∀ w w' : D.L₀, g⁻¹ * (D.e (w * w') : GL (Fin 3) K) * g =
      (g⁻¹ * (D.e w : GL (Fin 3) K) * g) * (g⁻¹ * (D.e w' : GL (Fin 3) K) * g) := by
    intro w w'
    rw [map_mul, Subgroup.coe_mul]
    group
  by_cases hp2 : p ≠ 2
  ·
    have hchar := Sec4.PiField.charP hK
    have hm1 : (-1 : K) ≠ 1 := by
      intro h
      have h2 : ((2 : ℕ) : K) = 0 := by
        have : (2 : K) = 1 - (-1) := by ring
        rw [Nat.cast_ofNat, this, h, sub_self]
      have := (CharP.cast_eq_zero_iff K p 2).mp h2
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hK.prime Nat.prime_two).mp this)
    set m : Kˣ := -1 with hm
    have hmμ : m ∈ rootsOfUnity (qSubPi π (p ^ f)) K := by
      rw [mem_rootsOfUnity]
      have hodd : Odd (p ^ f) := (hK.prime.eq_two_or_odd'.resolve_left hp2).pow
      obtain ⟨k, hk⟩ := hodd
      cases π
      · change m ^ (p ^ f + 1) = 1
        rw [hk, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul, hm, neg_one_sq, one_pow]
      · change m ^ (p ^ f - 1) = 1
        rw [hk, show 2 * k + 1 - 1 = 2 * k by omega, pow_mul, hm, neg_one_sq, one_pow]
    have h1μ : (1 : Kˣ) ∈ rootsOfUnity (qSubPi π (p ^ f)) K := one_mem _
    set s := diagUnits m m 1 with hs
    have hsL : s ∈ slPi π 3 (p ^ f) K := by
      refine (mem_slPi_iff hπ).mpr ⟨diagUnits_mem_glPi hK hmμ hmμ h1μ, ?_⟩
      rw [hs, det_diagUnits, hm]
      simp
    obtain ⟨w, hw⟩ := hlift s hsL
    have hs1 : s ≠ 1 := by
      intro h1
      apply hm1
      have := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 0 0) h1
      simpa [hs, coe_diagUnits, hm] using this
    have hs2 : s ^ 2 = 1 := by
      rw [hs, diagUnits_pow, hm, neg_one_sq, one_pow]
      have := diagUnits_self_eq_scalar (1 : Kˣ)
      rw [this, map_one]
    refine ⟨Subgroup.zpowers (w : X), Subgroup.zpowers_le.mpr w.2, ?_, ?_, ?_⟩
    · intro hbot
      apply hs1
      have hw1 : (w : X) = 1 := by
        have := Subgroup.mem_zpowers (w : X)
        rw [hbot, Subgroup.mem_bot] at this
        exact this
      have : w = 1 := Subtype.ext hw1
      rw [← hw, this, map_one, Subgroup.coe_one, mul_one, inv_mul_cancel]
    · have hw2 : w ^ 2 = 1 := hinj _ _ (by
        rw [map_pow, Subgroup.coe_pow, show g⁻¹ * (D.e w : GL (Fin 3) K) ^ 2 * g =
          (g⁻¹ * (D.e w : GL (Fin 3) K) * g) ^ 2 by simp only [sq]; group, hw, hs2, map_one,
          Subgroup.coe_one]
        group)
      intro r
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp r.2
      refine ⟨1, Subtype.ext ?_⟩
      simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
      rw [← hn, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast]
      have : (w : X) ^ 2 = 1 := by simpa using congrArg Subtype.val hw2
      rw [this, _root_.one_zpow]
    ·
      have hzw : zL * w = w * zL := hinj _ _ (by
        rw [hmapmul, hmapmul, hgD, hw, hs]
        exact (diagUnits_commute_diagTau hτ m m 1).symm)
      have hzw' : z * (w : X) = (w : X) * z := congrArg Subtype.val hzw
      refine Subgroup.mem_normalizer_fintype fun r hr => ?_
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hr
      rw [show z * (w : X) ^ n * z⁻¹ = (w : X) ^ n by
        rw [(Commute.zpow_right hzw' n).eq, mul_inv_cancel_right]]
      exact Subgroup.zpow_mem_zpowers _ n
  ·
    push Not at hp2
    have hπt : π = true := hpπ.resolve_left (by simp [hp2])
    subst hπt
    · subst hp2
      have hchar := Sec4.PiField.charP hK
      have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
      set Rm : Subgroup (GL (Fin 3) K) := rootUHom.range with hRm
      have hRmL : Rm ≤ slPi true 3 (2 ^ f) K := by
        rintro _ ⟨r, rfl⟩
        exact (mem_slPi_true _).mpr (det_rootU _)
      set RL : Subgroup D.L₀ :=
        { carrier := {w | g⁻¹ * (D.e w : GL (Fin 3) K) * g ∈ Rm}
          mul_mem' := fun {w w'} hw hw' => by
            simp only [Set.mem_ofPred_eq] at hw hw' ⊢
            rw [hmapmul]
            exact mul_mem hw hw'
          one_mem' := by
            simp only [Set.mem_ofPred_eq, map_one, Subgroup.coe_one, mul_one, inv_mul_cancel]
            exact one_mem _
          inv_mem' := fun {w} hw => by
            simp only [Set.mem_ofPred_eq] at hw ⊢
            rw [map_inv, Subgroup.coe_inv, show g⁻¹ * (D.e w : GL (Fin 3) K)⁻¹ * g =
              (g⁻¹ * (D.e w : GL (Fin 3) K) * g)⁻¹ by group]
            exact inv_mem hw } with hRL
      have hmemRL : ∀ w : D.L₀, w ∈ RL ↔ g⁻¹ * (D.e w : GL (Fin 3) K) * g ∈ Rm :=
        fun w => Iff.rfl
      obtain ⟨w₁, hw₁⟩ := hlift (rootU 1) ((mem_slPi_true _).mpr (det_rootU _))
      refine ⟨RL.map D.L₀.subtype, ?_, ?_, ?_, ?_⟩
      · rintro _ ⟨w, -, rfl⟩
        exact w.2
      · intro hbot
        have hw₁R : (w₁ : X) ∈ RL.map D.L₀.subtype :=
          ⟨w₁, (hmemRL w₁).mpr (hw₁ ▸ ⟨Multiplicative.ofAdd 1, rfl⟩), rfl⟩
        rw [hbot, Subgroup.mem_bot] at hw₁R
        have : w₁ = 1 := Subtype.ext hw₁R
        rw [this, map_one, Subgroup.coe_one, mul_one, inv_mul_cancel] at hw₁
        have := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 0 1) hw₁
        simp [coe_rootU] at this
      · rintro ⟨_, ⟨w, hw, rfl⟩⟩
        refine ⟨1, Subtype.ext ?_⟩
        simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
        obtain ⟨r, hr⟩ := (hmemRL w).mp hw
        have hw2 : w ^ 2 = 1 := hinj _ _ (by
          rw [map_pow, Subgroup.coe_pow, show g⁻¹ * (D.e w : GL (Fin 3) K) ^ 2 * g =
            (g⁻¹ * (D.e w : GL (Fin 3) K) * g) ^ 2 by simp only [sq]; group, ← hr,
            rootUHom_apply, sq, rootU_mul, ← two_mul, h2, zero_mul, rootU_zero, map_one,
            Subgroup.coe_one]
          group)
        simpa using congrArg Subtype.val hw2
      · refine Subgroup.mem_normalizer_fintype fun r hr => ?_
        obtain ⟨w, hw, rfl⟩ := hr
        obtain ⟨t, ht⟩ := (hmemRL w).mp hw
        refine ⟨zL * w * zL⁻¹, (hmemRL _).mpr ?_, by simp [hzL]⟩
        rw [hmapmul, hmapmul, map_inv, Subgroup.coe_inv,
          show g⁻¹ * (D.e zL : GL (Fin 3) K)⁻¹ * g = (g⁻¹ * (D.e zL : GL (Fin 3) K) * g)⁻¹ by
            group, hgD, ← ht, rootUHom_apply]
        have hτ0 : τ ≠ 0 := by
          rintro rfl
          simp at hτ
        rw [diagTau_eq_diagUnits hτ hτ0, diagUnits_conj_rootU]
        exact ⟨Multiplicative.ofAdd _, rfl⟩

end TwoSubgroup

section G

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem mk_commute_of_mem_thetaQuotCentralizer (hL : L ∈ thetaComponentsAt 3 c)
    {x l : Subgroup.normalizer (Subgroup.zpowers c : Set G)}
    (hx : (x : G) ∈ Sec4.thetaQuotCentralizer L) (hl : (l : G) ∈ L) :
    QuotientGroup.mk' (aschbacherSolvableCore 3
        (Subgroup.normalizer (Subgroup.zpowers c : Set G))) x *
      QuotientGroup.mk' _ l = QuotientGroup.mk' _ l * QuotientGroup.mk' _ x := by
  have h1 := (Sec6.mem_thetaQuotCentralizer_iff.mp hx).2 l hl
  rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt hL, Sec13.inSubgroup_theta_centralizer] at h1
  obtain ⟨t, ht, hte⟩ := h1.2.2
  have htv : t = l⁻¹ * (x * l * x⁻¹) := Subtype.ext (by simpa using hte)
  have h2 : QuotientGroup.mk' (aschbacherSolvableCore 3
      (Subgroup.normalizer (Subgroup.zpowers c : Set G))) (l⁻¹ * (x * l * x⁻¹)) = 1 := by
    rw [← htv]
    exact (QuotientGroup.eq_one_iff _).mpr ht
  simp only [map_mul, map_inv] at h2
  calc QuotientGroup.mk' _ x * QuotientGroup.mk' _ l =
      QuotientGroup.mk' _ l * ((QuotientGroup.mk' _ l)⁻¹ * (QuotientGroup.mk' _ x *
        QuotientGroup.mk' _ l * (QuotientGroup.mk' _ x)⁻¹)) * QuotientGroup.mk' _ x := by group
    _ = QuotientGroup.mk' _ l * QuotientGroup.mk' _ x := by rw [h2, mul_one]

theorem mem_partTwoE_of_isSLThreePiTwo (hD : Sec13Data G A c L)
    (hSL2 : Sec4.IsSLThreePiTwo (lBarA c L A))
    (hnU : ¬ ∃ (f : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ f) ^ 2 ∧
      2 ^ f % 3 = 2 ∧
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ f) K))
    {E : Subgroup G} (hEle : E ≤ (L ⊔ A) ⊓ Subgroup.normalizer (A : Set G))
    (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27)
    (hEC : ¬ IsCyclic (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G))
    (hEL : ¬ IsCyclic (E ⊓ L : Subgroup G)) : E ∈ partTwoE G := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨π, p, f, K, _, ⟨D⟩⟩ := exists_sLTwoData hSL2
  have hK := D.piField
  have hcL : c ∈ L := mem_of_isSLThreePiTwo slTwoCenter hD hSL2
  have hL := hD.mem_thetaComponentsAt
  have hSL : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) :=
    ResProof.isSLThreePi_of_isSLThreePiTwo hD hSL2
  have hty : Item131bProof.HeisType (L ⧸ aschbacherSolvableCore 3 L) := Or.inl hSL
  obtain ⟨hcE, -, hEL9, hsup⟩ :=
    Item131bProof.e_facts hD hty hcL (hEle.trans inf_le_left) hEe hE27 hEC hEL
  have hΛ := subgroupOf_lBar_eq_L₀ hD D
  have hpπ : p ≠ 2 ∨ π = true := by
    by_contra h
    push Not at h
    obtain ⟨hp2, hπ⟩ := h
    have hπ' : π = false := by simpa using hπ
    subst hp2
    subst hπ'
    apply hnU
    obtain ⟨η, -⟩ := exists_lBarEquiv hL
    refine ⟨f, K, inferInstance, hK.finite, by simpa [piCard] using hK.card, D.modThree, ⟨?_⟩⟩
    exact η.trans ((Subgroup.subgroupOfEquivOfLe lBar_le_lBarA).symm.trans
      ((MulEquiv.subgroupCongr hΛ).trans D.e))
  obtain ⟨e, ⟨heE, heL⟩, hecz⟩ : ∃ e ∈ E ⊓ L, e ∉ Subgroup.zpowers c := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show E ⊓ L ≤ Subgroup.zpowers c from h)
    rw [hEL9, Nat.card_zpowers, hD.orderOf_eq] at this
    norm_num at this
  have he3 : e ^ 3 = 1 := hEe.2 e heE
  have hec : e * c = c * e := congrArg Subtype.val (hEe.1.is_comm.comm ⟨e, heE⟩ ⟨c, hcE⟩)
  set Hc := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hHc
  set Θ := aschbacherSolvableCore 3 Hc with hΘ
  have hLH : L ≤ Hc := le_normalizer_zpowers_of_mem hL
  have hLAH : L ⊔ A ≤ Hc := sup_le hLH hD.A_le_normalizer_zpowers
  have hEH : E ≤ Hc := (hEle.trans inf_le_left).trans hLAH
  set eH : Hc := ⟨e, hLH heL⟩ with heH
  have heY : eH ∈ (L ⊔ A).subgroupOf Hc := Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left heL)
  set eb : lBarA c L A := ⟨QuotientGroup.mk' Θ eH, Subgroup.mem_map_of_mem _ heY⟩ with heb
  obtain ⟨hebL₀, heb3, hebC⟩ :=
    bar_mem_not_mem_centralizer hD D hcL heL he3 hec hecz (eb := eb) rfl
  obtain ⟨R, hRL₀, hR1, hR2, hebR⟩ := sLTwoData_exists_two_subgroup D hebL₀ heb3 hebC hpπ
  set Rb : Subgroup (Hc ⧸ Θ) := R.map (lBarA c L A).subtype with hRb
  have hRb1 : Rb ≠ ⊥ := by
    intro h
    apply hR1
    rw [eq_bot_iff]
    intro r hr
    have : ((r : lBarA c L A) : Hc ⧸ Θ) ∈ Rb := ⟨r, hr, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact Subtype.ext this
  have hRb2 : IsPGroup 2 Rb := hR2.map _
  have hRbL : ∀ r ∈ Rb, ∃ l : Hc, (l : G) ∈ L ∧ QuotientGroup.mk' Θ l = r := by
    rintro _ ⟨r, hr, rfl⟩
    have hrΛ : r ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A) := hΛ ▸ hRL₀ hr
    obtain ⟨l, hl, hlr⟩ := Subgroup.mem_subgroupOf.mp hrΛ
    exact ⟨l, Subgroup.mem_subgroupOf.mp hl, hlr⟩
  set Nn : Subgroup G := ((Subgroup.normalizer (Rb : Set (Hc ⧸ Θ))).comap
    (QuotientGroup.mk' Θ)).map Hc.subtype with hNn
  have hmemNn : ∀ x : Hc, QuotientGroup.mk' Θ x ∈ Subgroup.normalizer (Rb : Set (Hc ⧸ Θ)) →
      (x : G) ∈ Nn := fun x hx => ⟨x, hx, rfl⟩
  have hCN : E ⊓ Sec4.thetaQuotCentralizer L ≤ Nn := by
    intro y hy
    refine hmemNn ⟨y, hEH hy.1⟩ (Subgroup.mem_normalizer_fintype fun r hr => ?_)
    obtain ⟨l, hl, rfl⟩ := hRbL r hr
    rw [mk_commute_of_mem_thetaQuotCentralizer hL hy.2 hl, mul_inv_cancel_right]
    exact hr
  have heN : e ∈ Nn := by
    refine hmemNn eH (Subgroup.mem_normalizer_fintype fun r hr => ?_)
    obtain ⟨r', hr', rfl⟩ := hr
    exact ⟨eb * r' * eb⁻¹, (Subgroup.mem_normalizer_iff.mp hebR r').mp hr', rfl⟩
  have hcN : c ∈ Nn := by
    refine hmemNn ⟨c, Subgroup.le_normalizer (Subgroup.mem_zpowers c)⟩
      (Subgroup.mem_normalizer_fintype fun r hr => ?_)
    obtain ⟨r', hr', rfl⟩ := hr
    have hcZ := Subgroup.mem_center_iff.mp (mkC_mem_center hD) r'
    have : QuotientGroup.mk' Θ ⟨c, Subgroup.le_normalizer (Subgroup.mem_zpowers c)⟩ *
        ((r' : lBarA c L A) : Hc ⧸ Θ) *
        (QuotientGroup.mk' Θ ⟨c, Subgroup.le_normalizer (Subgroup.mem_zpowers c)⟩)⁻¹ =
        ((r' : lBarA c L A) : Hc ⧸ Θ) := by
      have h1 := congrArg Subtype.val hcZ
      simp only [Subgroup.coe_mul, mkC] at h1
      rw [← h1, mul_inv_cancel_right]
    change _ * ((r' : lBarA c L A) : Hc ⧸ Θ) * _ ∈ Rb
    rw [this]
    exact ⟨r', hr', rfl⟩
  have hELN : E ⊓ L ≤ Nn := by
    have hle : Subgroup.zpowers e ⊔ Subgroup.zpowers c ≤ E ⊓ L :=
      sup_le (Subgroup.zpowers_le.mpr ⟨heE, heL⟩) (Subgroup.zpowers_le.mpr ⟨hcE, hcL⟩)
    have heq : Subgroup.zpowers e ⊔ Subgroup.zpowers c = E ⊓ L := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [hEL9]
      have hcomm : ∀ x ∈ Subgroup.zpowers e, ∀ y ∈ Subgroup.zpowers c, x * y = y * x :=
        fun x hx y hy => congrArg Subtype.val (hEe.1.is_comm.comm
          ⟨x, (Subgroup.zpowers_le.mpr heE) hx⟩ ⟨y, (Subgroup.zpowers_le.mpr hcE) hy⟩)
      have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
      have hbot : Subgroup.zpowers e ⊓ Subgroup.zpowers c = ⊥ := by
        refine Subgroup.eq_bot_of_card_eq _ ?_
        have hdvd : Nat.card (Subgroup.zpowers e ⊓ Subgroup.zpowers c : Subgroup G) ∣ 3 := by
          rw [← hD.card_zpowers]
          exact Subgroup.card_dvd_of_le inf_le_right
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
        · exact h1
        · exfalso
          apply hecz
          have heq : Subgroup.zpowers e ⊓ Subgroup.zpowers c = Subgroup.zpowers c :=
            Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hD.card_zpowers])
          have : Subgroup.zpowers e = Subgroup.zpowers c := by
            refine (Subgroup.eq_of_le_of_card_ge (heq ▸ inf_le_left) ?_).symm
            rw [hD.card_zpowers, Nat.card_zpowers, orderOf_eq_prime he3 (by
              rintro rfl
              exact hecz (one_mem _))]
          rw [← this]
          exact Subgroup.mem_zpowers e
      rw [hbot, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers,
        hD.orderOf_eq, orderOf_eq_prime he3 (by rintro rfl; exact hecz (one_mem _))] at hcard
      rw [hcard]
    rw [← heq]
    exact sup_le (Subgroup.zpowers_le.mpr heN) (Subgroup.zpowers_le.mpr hcN)
  have hEN : E ≤ Nn := hsup ▸ sup_le hCN hELN
  have hP : IsPGroup 3 (E.subgroupOf Hc) := fun x =>
    ⟨1, Subtype.ext (Subtype.ext (by simpa using hEe.2 _ (Subgroup.mem_subgroupOf.mp x.2)))⟩
  have hPR : ∀ x ∈ E.subgroupOf Hc,
      QuotientGroup.mk' Θ x ∈ Subgroup.normalizer (Rb : Set (Hc ⧸ Θ)) := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hEN (Subgroup.mem_subgroupOf.mp hx)
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  obtain ⟨U, hU1, hU2, hUN⟩ := Item131bProof.exists_two_subgroup_of_mk hP hRb1 hRb2 hPR
  refine ⟨hEe, hE27, U.map Hc.subtype, ?_, hU2.map _, fun x hx => ?_⟩
  · intro h
    apply hU1
    rw [eq_bot_iff]
    intro u hu
    have : (u : G) ∈ U.map Hc.subtype := ⟨u, hu, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact Subtype.ext this
  · exact (Sec13.coe_mem_normalizer_map_iff Hc (h := ⟨x, hEH hx⟩)).mpr
      (hUN (Subgroup.mem_subgroupOf.mpr hx))

end G

end Res2Proof

open Res2Proof in
theorem step131bSLTwoInE_of_U (hU : Step131bSLTwoInEU) : Step131bSLTwoInE := by
  intro G _ _ A c L hD hSL E hEle hEe hE27 hEC hEL
  by_cases hSU : ∃ (f : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ f) ^ 2 ∧
      2 ^ f % 3 = 2 ∧
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ f) K)
  · exact hU G A c L hD hSL hSU E hEle hEe hE27 hEC hEL
  · exact mem_partTwoE_of_isSLThreePiTwo hD hSL hSU hEle hEe hE27 hEC hEL

theorem step131bSLTwo_of_U
    (h128 : Sec12.Item128BarAt) (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5)
    (h415 : Sec4.Item4_15) (hU : Step131bSLTwoInEU) : Step131bSLTwo :=
  step131bSLTwo_of_inE h128 h422 h45 h415 (step131bSLTwoInE_of_U hU)

end CFSG.RankThree.PartTwo.Sec13
