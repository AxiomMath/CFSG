module

public import CFSG.RankThree.PartTwo.Sec21.Item228InspProofStatements
public import CFSG.RankThree.PartTwo.Sec21.Item223PrintProof
import CFSG.RankThree.PartTwo.Sec21.Item228InspProofRefl
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.Models.PGLOrders
public import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofOne
public import CFSG.RankThree.PartTwo.Sec6.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly (IsElemAbelian)

variable {G : Type} [Group G]

@[expose] noncomputable def perfCent (X ℓ : Subgroup G) : Subgroup G :=
  inSubgroup perfectResidual (X ⊓ Subgroup.centralizer (ℓ : Set G))

@[expose] def U4EvenTorus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T : Subgroup G) (k : ℕ), 0 < k → Even k →
    Nonempty (X ≃* projSU 4 2 k) → T ≤ X → IsElemAbelian 3 T → Nat.card T = 3 ^ 2 →
      Nonempty (starOf T X ≃* DihedralGroup 4) ∧
      (∀ ℓ : Subgroup G, ℓ ≤ T → Nat.card ℓ = 3 →
        Nonempty (perfCent X ℓ ≃* projSL 2 (GaloisField 2 k)) ∨
          Nonempty (perfCent X ℓ ≃* projSL 2 (GaloisField 2 (2 * k)))) ∧
      ∀ ℓ₁ ℓ₂ c₁ c₂ : Subgroup G, ℓ₁ ≤ T → ℓ₂ ≤ T → c₁ ≤ T → c₂ ≤ T →
        Nat.card ℓ₁ = 3 → Nat.card ℓ₂ = 3 → Nat.card c₁ = 3 → Nat.card c₂ = 3 → ℓ₁ ≠ ℓ₂ →
        c₁ ≤ perfCent X ℓ₁ → c₂ ≤ perfCent X ℓ₂ →
          (c₁ = ℓ₂ → c₂ = ℓ₁ ∧
            (⁅perfCent X ℓ₁, perfCent X ℓ₂⁆ = ⊥ ∨
              (perfCent X ℓ₁ ⊔ perfCent X ℓ₂ = X ∧
                Nonempty (perfCent X ℓ₁ ≃* projSL 2 (GaloisField 2 (2 * k))) ∧
                Nonempty (perfCent X ℓ₂ ≃* projSL 2 (GaloisField 2 (2 * k))) ∧
                ∃ g ∈ X, g ∈ Subgroup.normalizer (T : Set G) ∧
                  ℓ₁.map (MulAut.conj g).toMonoidHom = ℓ₂ ∧
                  ℓ₂.map (MulAut.conj g).toMonoidHom = ℓ₁))) ∧
          (c₁ ≠ ℓ₂ → perfCent X ℓ₁ ⊔ perfCent X ℓ₂ = X)

namespace Item228InspProof

structure InnerData (A X : Subgroup G) : Prop where
  le_normalizer : A ≤ Subgroup.normalizer (X : Set G)
  center_eq_bot : Subgroup.center X = ⊥
  decomp : ∀ b ∈ A, ∃ y ∈ A ⊓ X, y⁻¹ * b ∈ Subgroup.centralizer (X : Set G)
  card_inf : Nat.card (A ⊓ X : Subgroup G) = 3 ^ 2
  exists_center : ∃ a ∈ A, a ≠ 1 ∧ X ∈ thetaComponentsAt 3 a

theorem innerData_of_inner [Finite G] (h66 : Sec6.Item6_6) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hA27 : Nat.card A = 3 ^ 3) {X : Subgroup G}
    (hX : X ∈ lStar A) {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) (hXa : X ∈ thetaComponentsAt 3 a)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hZ : Subgroup.center X = ⊥)
    (hθ : aschbacherSolvableCore 3 X = ⊥) (hinner : ∀ x ∈ A, ¬ Sec4.InducesOuterTheta x X) :
    InnerData A X := by
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hAmax : Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A :=
    ⟨hAe, fun B hB hAB => (hpair.mem_S.1.2.1 B hB hAB).le⟩
  have ha3 : a ^ 3 = 1 := hAe.2 a haA
  have hXC := Sec6.le_centralizer_of_mem_thetaComponentsAt hXa
  have hdecomp : ∀ b ∈ A, ∃ y ∈ A ⊓ X, y⁻¹ * b ∈ Subgroup.centralizer (X : Set G) := by
    intro b hb
    obtain ⟨y, hyX, hby⟩ :=
      Item223PrintProof.exists_conj_eq_of_not_inducesOuterTheta hθ (hAX hb) (hinner b hb)
    refine ⟨y, ⟨Item223PrintProof.mem_of_conj_eq hAmax hAX hZ hb hyX hby, hyX⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := hby l hl
    calc l * (y⁻¹ * b) = y⁻¹ * (y * l * y⁻¹) * b := by group
      _ = y⁻¹ * (b * l * b⁻¹) * b := by rw [h1]
      _ = y⁻¹ * b * l := by group
  have hcardC : Nat.card (A ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) = 3 := by
    have hcyc := h66 G hpair.standing A hpair.mem_S X hX
    have hle : A ⊓ Subgroup.centralizer (X : Set G) ≤ A ⊓ Sec4.thetaQuotCentralizer X := by
      rintro d ⟨hdA, hdC⟩
      refine ⟨hdA, Sec6.mem_thetaQuotCentralizer_iff.mpr
        ⟨Subgroup.centralizer_le_normalizer _ hdC, fun l hl => ?_⟩⟩
      have h1 : l * d = d * l := Subgroup.mem_centralizer_iff.mp hdC l hl
      rw [show l⁻¹ * (d * l * d⁻¹) = 1 by rw [← h1]; group]
      exact Subgroup.one_mem _
    have hle3 : Nat.card (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) ≤ 3 := by
      obtain ⟨g, hg⟩ := hcyc.exists_generator
      rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
      have : g ^ 3 = 1 := Subtype.ext (by simpa using hAe.2 _ g.2.1)
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one this)
    have haC : a ∈ A ⊓ Subgroup.centralizer (X : Set G) :=
      ⟨haA, Subgroup.mem_centralizer_iff.mpr fun l hl =>
        Subgroup.mem_centralizer_singleton_iff.mp (hXC hl)⟩
    have hge : 3 ≤ Nat.card (A ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) := by
      have h := Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr haC)
      rwa [Nat.card_zpowers, orderOf_eq_prime ha3 ha1] at h
    have := (Subgroup.card_le_of_le hle).trans hle3
    omega
  have hbij : Function.Bijective (fun p : (A ⊓ X : Subgroup G) ×
      (A ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) =>
        (⟨(p.1 : G) * p.2, A.mul_mem p.1.2.1 p.2.2.1⟩ : A)) := by
    constructor
    · rintro ⟨y, z⟩ ⟨y', z'⟩ h
      have h1 : (y : G) * z = y' * z' := congrArg Subtype.val h
      have h2 : (y' : G)⁻¹ * y = z' * (z : G)⁻¹ := by
        calc (y' : G)⁻¹ * y = (y' : G)⁻¹ * (y * z) * (z : G)⁻¹ := by group
          _ = (y' : G)⁻¹ * (y' * z') * (z : G)⁻¹ := by rw [h1]
          _ = z' * (z : G)⁻¹ := by group
      have hm : (y' : G)⁻¹ * y ∈ X := X.mul_mem (X.inv_mem y'.2.2) y.2.2
      have hc : ∀ l ∈ X, ((y' : G)⁻¹ * y) * l * ((y' : G)⁻¹ * y)⁻¹ = l := by
        intro l hl
        rw [h2]
        have hz : (z' : G) * (z : G)⁻¹ ∈ Subgroup.centralizer (X : Set G) :=
          Subgroup.mul_mem _ z'.2.2 (Subgroup.inv_mem _ z.2.2)
        rw [(Subgroup.mem_centralizer_iff.mp hz l hl).symm, mul_inv_cancel_right]
      have h3 := Item223PrintProof.eq_one_of_forall_conj_eq hZ hm hc
      have hyy : (y : G) = y' := by
        rw [inv_mul_eq_one] at h3
        exact h3.symm
      have hzz : (z : G) = z' := by
        rw [hyy] at h1
        exact mul_left_cancel h1
      exact Prod.ext (Subtype.ext hyy) (Subtype.ext hzz)
    · rintro ⟨b, hb⟩
      obtain ⟨y, hy, hyb⟩ := hdecomp b hb
      exact ⟨(⟨y, hy⟩, ⟨y⁻¹ * b, A.mul_mem (A.inv_mem hy.1) hb, hyb⟩),
        Subtype.ext (by simp)⟩
  have hcardA := Nat.card_eq_of_bijective _ hbij
  rw [Nat.card_prod, hcardC, hA27] at hcardA
  exact ⟨hAX, hZ, hdecomp, by omega, ⟨a, haA, ha1, hXa⟩⟩

theorem innerData_of_U4 [Finite G] (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (hA27 : Nat.card A = 3 ^ 3)
    {X : Subgroup G} (hX : X ∈ lStar A) {k : ℕ} (hk : 1 ≤ k) (eX : X ≃* projSU 4 2 k) :
    InnerData A X := by
  have hG := hpair.standing.toTheoremFourHyp
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  obtain ⟨a, haA, ha1, hXa⟩ := mem_thetaComponentFamily_iff.mp hX.1
  have ha3 : a ^ 3 = 1 := hAe.2 a haA
  have hAX := Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe haA ha1 X hXa
  have : IsSimpleGroup (projSU 4 2 k) := isSimpleGroup_projSU le_rfl hk
  have : IsSimpleGroup X := eX.isSimpleGroup
  have hperf : Group.IsPerfect X := isPerfect_of_mem_thetaComponentFamily hX.1
  have hZ := Item223PrintProof.center_eq_bot_of_isSimpleGroup_of_isPerfect hperf
  have hθ := inSubgroup_theta_eq_bot_of_mulEquiv hperf eX
  have hθ' : aschbacherSolvableCore 3 X = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp hθ
  have eθ : X ⧸ aschbacherSolvableCore 3 X ≃* projSU 4 2 k :=
    (mulEquiv_lBar_of_theta_eq_bot hθ).symm.trans eX
  have hinner : ∀ x ∈ A, ¬ Sec4.InducesOuterTheta x X := fun x hxA =>
    Item223PrintProof.not_inducesOuterTheta_of_mem_thetaComponentsAt hG ha3 ha1 hXa hk eθ
      (congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hxA⟩ ⟨a, haA⟩)) (hAe.2 x hxA)
  exact innerData_of_inner h66 hpair hA27 hX haA ha1 hXa hAX hZ hθ' hinner

theorem root_facts [Finite G] (h222 : Item222) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hK : KOfWellDefined A) {X : Subgroup G}
    (hD : InnerData A X) {φ : MulAut A} (hφ : φ ∈ dStar A) (hKX : kOf A φ ≤ X)
    (hS : ∀ ℓ : Subgroup G, ℓ ≤ A ⊓ X → Nat.card ℓ = 3 → ∃ n : ℕ, 2 ≤ n ∧
      Nonempty (perfCent X ℓ ≃* projSL 2 (GaloisField 2 n))) :
    Nat.card (A ⊓ X ⊓ fixedInG A φ : Subgroup G) = 3 ∧
      A ⊓ Subgroup.centralizer (X : Set G) ≤ fixedInG A φ ∧
      kOf A φ = perfCent X (A ⊓ X ⊓ fixedInG A φ) ∧
      (commOf φ).map A.subtype ≤ A ⊓ X ∧
      ∃ j : Subgroup.normalizer (A : Set G), (j : G) ∈ X ∧ wConj A j = φ := by
  have hAF := hpair.mem_S.1
  have hAe : IsElemAbelian 3 A := hAF.1
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  have hA3 : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hAe.2 a a.2)
  obtain ⟨a, haA, -, hXa⟩ := hD.exists_center
  obtain ⟨j, hjK, -, hj⟩ := exists_involution_kOf_wConj_eq h222 hpair hK hφ
  have hjX : (j : G) ∈ X := hKX hjK
  set T := A ⊓ X with hTdef
  have hcA : (commOf φ).map A.subtype ≤ T :=
    le_inf (Subgroup.map_subtype_le _) ((map_commOf_le_kOf h222 hpair hK hφ).trans hKX)
  have hfix : A ⊓ Subgroup.centralizer (X : Set G) ≤ fixedInG A φ := by
    rintro z ⟨hzA, hzC⟩
    refine ⟨⟨z, hzA⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_fixedSubgroupOf, ← hj]
    apply Subtype.ext
    rw [wConj_apply]
    change (j : G) * z * (j : G)⁻¹ = z
    rw [Subgroup.mem_centralizer_iff.mp hzC j hjX, mul_inv_cancel_right]
  have hjT : (j : G) ∈ Subgroup.normalizer (T : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨j.2, Subgroup.le_normalizer hjX⟩
  have hjφ : wConj A ⟨(j : G), j.2⟩ = φ := hj
  obtain ⟨hρ, -, hfixT⟩ := Item223PrintProof.restrict_reflection inf_le_left hAc hA3 j.2 hjT
    (by rw [hjφ]; exact hφ.1) (by rw [hjφ]; exact hcA)
  rw [hjφ] at hfixT
  have hTc : ∀ a b : T, a * b = b * a :=
    (Sec5.isElemAbelian_of_le hAe inf_le_left).1.is_comm.comm
  have hℓ3 : Nat.card (T ⊓ fixedInG A φ : Subgroup G) = 3 := by
    rw [← hfixT, fixedInG, Subgroup.card_map_of_injective T.subtype_injective]
    have h := card_eq_three_mul_card_fixed hTc hρ
    rw [hD.card_inf] at h
    omega
  have hcentEq : X ⊓ Subgroup.centralizer (fixedInG A φ : Set G) =
      X ⊓ Subgroup.centralizer ((T ⊓ fixedInG A φ : Subgroup G) : Set G) := by
    apply le_antisymm
    · exact inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_right))
    · rintro g ⟨hgX, hg⟩
      exact ⟨hgX, Item223PrintProof.mem_centralizer_of_mem_centralizer_inf hD.decomp
        (Subgroup.map_subtype_le _) hfix hgX hg⟩
  obtain ⟨n, hn2, ⟨e⟩⟩ := hS (T ⊓ fixedInG A φ) inf_le_left hℓ3
  have hφX : φ ∈ starOf A X := ⟨j, Subgroup.mem_subgroupOf.mpr hjX, hj⟩
  have e' : inSubgroup perfectResidual (X ⊓ Subgroup.centralizer (fixedInG A φ : Set G)) ≃*
      projSL 2 (GaloisField 2 n) :=
    (MulEquiv.subgroupCongr (congrArg (inSubgroup perfectResidual) hcentEq)).trans e
  have := isSimpleGroup_projSL_two hn2
  have hK0 := Item222Proof.kZero_eq_perfectResidual hAF haA hXa hφX hφ.1.1 e'.isSimpleGroup
    (exists_not_commute_of_mulEquiv_projSL e') (three_dvd_card_of_mulEquiv_projSL e')
  have hU : ¬ CFSG.Assembly.LowTwoRank.StatedClassicalModel (kZero A φ) .PSU 3 2 2 := by
    rw [hK0]
    exact Item222Proof.not_statedClassicalModel_U34_of_mulEquiv (by omega) e'
  have hKeq : kOf A φ = perfCent X (T ⊓ fixedInG A φ) := by
    rw [kOf_eq_kZero hU, hK0, hcentEq]
    rfl
  exact ⟨hℓ3, hfix, hKeq, hcA, j, hjX, hj⟩

theorem conj_mem_of_mem_normalizer_inf {A X : Subgroup G}
    (hdec : ∀ b ∈ A, ∃ y ∈ A ⊓ X, y⁻¹ * b ∈ Subgroup.centralizer (X : Set G)) {g : G}
    (hgX : g ∈ X) (hgT : g ∈ Subgroup.normalizer ((A ⊓ X : Subgroup G) : Set G)) {b : G}
    (hb : b ∈ A) : g * b * g⁻¹ ∈ A := by
  obtain ⟨y, hy, hyb⟩ := hdec b hb
  have hz : g * (y⁻¹ * b) * g⁻¹ = y⁻¹ * b := by
    rw [Subgroup.mem_centralizer_iff.mp hyb g hgX, mul_inv_cancel_right]
  have hgy : g * y * g⁻¹ ∈ A ⊓ X := (Subgroup.mem_normalizer_iff.mp hgT y).mp hy
  have : g * b * g⁻¹ = (g * y * g⁻¹) * (g * (y⁻¹ * b) * g⁻¹) := by group
  rw [this, hz]
  exact A.mul_mem hgy.1 (A.mul_mem (A.inv_mem hy.1) hb)

theorem mem_normalizer_of_mem_normalizer_inf {A X : Subgroup G}
    (hdec : ∀ b ∈ A, ∃ y ∈ A ⊓ X, y⁻¹ * b ∈ Subgroup.centralizer (X : Set G)) {g : G}
    (hgX : g ∈ X) (hgT : g ∈ Subgroup.normalizer ((A ⊓ X : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · exact conj_mem_of_mem_normalizer_inf hdec hgX hgT
  · intro hb
    have h := conj_mem_of_mem_normalizer_inf hdec (X.inv_mem hgX) (Subgroup.inv_mem _ hgT) hb
    rwa [inv_inv, show g⁻¹ * (g * b * g⁻¹) * g = b by group] at h

theorem exists_wStar_conj_of_swap {A X : Subgroup G} (hD : InnerData A X)
    (hAe : IsElemAbelian 3 A) {φ ψ : MulAut A} (hφ : IsReflectionOn φ) (hψ : IsReflectionOn ψ)
    (hfix₁ : A ⊓ Subgroup.centralizer (X : Set G) ≤ fixedInG A φ)
    (hfix₂ : A ⊓ Subgroup.centralizer (X : Set G) ≤ fixedInG A ψ) {g : G} (hgX : g ∈ X)
    (hgT : g ∈ Subgroup.normalizer ((A ⊓ X : Subgroup G) : Set G))
    (hg₁ : (A ⊓ X ⊓ fixedInG A φ).map (MulAut.conj g).toMonoidHom = A ⊓ X ⊓ fixedInG A ψ)
    (hg₂ : ((commOf φ).map A.subtype).map (MulAut.conj g).toMonoidHom =
      (commOf ψ).map A.subtype) :
    ∃ w ∈ wStar A, w * φ * w⁻¹ = ψ := by
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  have hA3 : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hAe.2 a a.2)
  have hgA := mem_normalizer_of_mem_normalizer_inf hD.decomp hgX hgT
  set w := wConj A ⟨g, hgA⟩ with hwdef
  refine ⟨w, wConj_mem_wStar A _, ?_⟩
  have hmapA : A.map (MulAut.conj g).toMonoidHom = A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hgA y).mp hy
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgA) x).mp hx
      simpa [mul_assoc] using this
  have hmapT : (A ⊓ X).map (MulAut.conj g).toMonoidHom = A ⊓ X := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hgT y).mp hy
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgT) x).mp hx
      simpa [mul_assoc] using this
  have hfixEq : fixedInG A (w * φ * w⁻¹) = fixedInG A ψ := by
    rw [hwdef, fixedInG_conj]
    refine Item223PrintProof.fixedInG_eq_of_inf_eq hD.decomp ?_ (Subgroup.map_subtype_le _) ?_
      hfix₂ ?_
    · exact (Subgroup.map_mono (Subgroup.map_subtype_le _)).trans hmapA.le
    · intro z hz
      refine ⟨z, hfix₁ hz, ?_⟩
      change g * z * g⁻¹ = z
      rw [Subgroup.mem_centralizer_iff.mp hz.2 g hgX, mul_inv_cancel_right]
    · rw [← hg₁, Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective, hmapT]
  have hfix : fixedSubgroupOf (w * φ * w⁻¹) = fixedSubgroupOf ψ :=
    Subgroup.map_injective A.subtype_injective hfixEq
  have hcomm : commOf (w * φ * w⁻¹) = commOf ψ := by
    apply Subgroup.map_injective A.subtype_injective
    rw [commOf_conj, Subgroup.map_map, ← hg₂, Subgroup.map_map]
    rfl
  exact eq_of_fixed_eq_of_commOf_eq hAc hA3 (hφ.conj w).1 hψ.1 hfix hcomm

theorem nonempty_starOf_mulEquiv_inf {A X : Subgroup G} (hD : InnerData A X) :
    Nonempty (starOf A X ≃* starOf (A ⊓ X) X) := by
  set T := A ⊓ X with hTdef
  set H : Subgroup (Subgroup.normalizer (A : Set G)) := X.subgroupOf _ with hHdef
  have hHT : ∀ x : H, ((x : Subgroup.normalizer (A : Set G)) : G) ∈
      Subgroup.normalizer (T : Set G) := fun x =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨(x : Subgroup.normalizer (A : Set G)).2,
      Subgroup.le_normalizer (Subgroup.mem_subgroupOf.mp x.2)⟩
  set f₁ : H →* MulAut A := A.normalizerMonoidHom.comp H.subtype with hf₁
  set g₀ : H →* Subgroup.normalizer (T : Set G) :=
    ((Subgroup.normalizer (A : Set G)).subtype.comp H.subtype).codRestrict _ hHT with hg₀
  set f₂ : H →* MulAut T := T.normalizerMonoidHom.comp g₀ with hf₂
  have hr₁ : f₁.range = starOf A X := by
    rw [hf₁, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hr₂ : f₂.range = starOf T X := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact ⟨g₀ x, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp x.2), rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      have hyX : (y : G) ∈ X := Subgroup.mem_subgroupOf.mp hy
      have hyA := mem_normalizer_of_mem_normalizer_inf hD.decomp hyX y.2
      exact ⟨⟨⟨y, hyA⟩, Subgroup.mem_subgroupOf.mpr hyX⟩, rfl⟩
  have hker : f₁.ker = f₂.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    have hf₁x : ∀ a : A, ((f₁ x a : A) : G) = ((x : Subgroup.normalizer (A : Set G)) : G) * a *
        ((x : Subgroup.normalizer (A : Set G)) : G)⁻¹ := fun a => rfl
    have hf₂x : ∀ t : T, ((f₂ x t : T) : G) = ((x : Subgroup.normalizer (A : Set G)) : G) * t *
        ((x : Subgroup.normalizer (A : Set G)) : G)⁻¹ := fun t => rfl
    constructor
    · intro h
      ext t
      rw [hf₂x, MulAut.one_apply]
      have := congrArg (fun σ : MulAut A => ((σ ⟨t, t.2.1⟩ : A) : G)) h
      simpa [hf₁x] using this
    · intro h
      have h1 : ∀ t ∈ T, ((x : Subgroup.normalizer (A : Set G)) : G) * t *
          ((x : Subgroup.normalizer (A : Set G)) : G)⁻¹ = t := by
        intro t ht
        have := congrArg (fun σ : MulAut T => ((σ ⟨t, ht⟩ : T) : G)) h
        simpa [hf₂x] using this
      ext a
      rw [hf₁x, MulAut.one_apply]
      exact Item223PrintProof.conj_eq_of_conj_eq_on_inf hD.decomp
        (Subgroup.mem_subgroupOf.mp x.2) h1 a a.2
  obtain ⟨e⟩ := Item223PrintProof.nonempty_range_mulEquiv_of_ker_eq f₁ f₂ hker
  exact ⟨(MulEquiv.subgroupCongr hr₁).symm.trans (e.trans (MulEquiv.subgroupCongr hr₂))⟩

theorem card_projSU_five_two_two : Nat.card (projSU 5 2 2) = 2 ^ 20 * 50968125 :=
  CFSG.PGLModel.card_projSU_five_four.trans (by norm_num)

theorem isEmpty_mulEquiv_projSU_five {X : Type*} [Group X] {k : ℕ} (hk : 1 ≤ k)
    (eX : X ≃* projSU 4 2 k) : IsEmpty (X ≃* projSU 5 2 2) := by
  refine ⟨fun f => ?_⟩
  have h := Nat.card_congr (eX.symm.trans f).toEquiv
  rw [card_projSU le_rfl hk, ordTwistedA_three_eq hk, card_projSU_five_two_two] at h
  have hv := congrArg (padicValNat 2) h
  rw [padicValNat_pow_two_pow_mul_odd (odd_ordTwistedA_three_part hk),
    padicValNat_two_pow_mul_odd (by decide)] at hv
  omega

theorem insp228_of_U4 [Finite G] (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (h222 : Item222)
    (hKW : KOfWellDefinedAll) (hU4 : U4EvenTorus) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hA27 : Nat.card A = 3 ^ 3) {φ ψ : MulAut A}
    (hφ : φ ∈ dStar A) (hψ : ψ ∈ dStar A) (hne : ψ ≠ φ) {X : Subgroup G} (hX : X ∈ lStar A)
    (hKX : kOf A φ ≤ X) (hJX : kOf A ψ ≤ X) {k : ℕ} (hk0 : 0 < k) (hke : Even k)
    (eX : X ≃* projSU 4 2 k) : Insp228Comm A φ ψ ∧ Insp228NonComm A φ ψ := by
  have hK := hKW G A E U c L hpair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  have hA3 : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hAe.2 a a.2)
  have hne' : φ ≠ ψ := fun h => hne h.symm
  have hD := innerData_of_U4 h45 h66 hpair hA27 hX hk0 eX
  set T := A ⊓ X with hTdef
  have hTe : IsElemAbelian 3 T := Sec5.isElemAbelian_of_le hAe inf_le_left
  obtain ⟨hD8, hlines, hpairs⟩ := hU4 G X T k hk0 hke ⟨eX⟩ inf_le_right hTe hD.card_inf
  have hS : ∀ ℓ : Subgroup G, ℓ ≤ T → Nat.card ℓ = 3 → ∃ n : ℕ, 2 ≤ n ∧
      Nonempty (perfCent X ℓ ≃* projSL 2 (GaloisField 2 n)) := by
    intro ℓ hℓ h3
    rcases hlines ℓ hℓ h3 with h | h
    · exact ⟨k, by obtain ⟨r, hr⟩ := hke; omega, h⟩
    · exact ⟨2 * k, by omega, h⟩
  obtain ⟨hℓ₁3, hfix₁, hK₁, hc₁T, -⟩ := root_facts h222 hpair hK hD hφ hKX hS
  obtain ⟨hℓ₂3, hfix₂, hK₂, hc₂T, -⟩ := root_facts h222 hpair hK hD hψ hJX hS
  have hc₁3 : Nat.card ((commOf φ).map A.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective A.subtype_injective]
    exact hφ.1.2
  have hc₂3 : Nat.card ((commOf ψ).map A.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective A.subtype_injective]
    exact hψ.1.2
  have hℓne : T ⊓ fixedInG A φ ≠ T ⊓ fixedInG A ψ := fun h =>
    fixedSubgroupOf_ne_of_ne h222 hpair hK hφ hψ hne' (Subgroup.map_injective
      A.subtype_injective (Item223PrintProof.fixedInG_eq_of_inf_eq hD.decomp
        (Subgroup.map_subtype_le _) (Subgroup.map_subtype_le _) hfix₁ hfix₂ h))
  have hc₁S : (commOf φ).map A.subtype ≤ perfCent X (T ⊓ fixedInG A φ) :=
    hK₁ ▸ map_commOf_le_kOf h222 hpair hK hφ
  have hc₂S : (commOf ψ).map A.subtype ≤ perfCent X (T ⊓ fixedInG A ψ) :=
    hK₂ ▸ map_commOf_le_kOf h222 hpair hK hψ
  obtain ⟨hL1, hL2⟩ := hpairs _ _ _ _ inf_le_left inf_le_left hc₁T hc₂T hℓ₁3 hℓ₂3 hc₁3 hc₂3
    hℓne hc₁S hc₂S
  have hcℓ : ∀ {χ χ' : MulAut A}, (commOf χ).map A.subtype = T ⊓ fixedInG A χ' →
      commOf χ ≤ fixedSubgroupOf χ' := fun h =>
    (Subgroup.map_le_map_iff_of_injective A.subtype_injective).mp (h.le.trans inf_le_right)
  unfold Insp228Comm Insp228NonComm
  rw [hK₁, hK₂]
  refine ⟨fun hc => ?_, fun hnc => ?_⟩
  ·
    have h₂ : commOf φ ≤ fixedSubgroupOf ψ :=
      commOf_le_fixedSubgroupOf_of_commute hAc hA3 hψ.1 hφ.1 hc.symm hne
    have hc₁ℓ₂ : (commOf φ).map A.subtype = T ⊓ fixedInG A ψ :=
      Subgroup.eq_of_le_of_card_ge (le_inf hc₁T (Subgroup.map_mono h₂)) (by rw [hℓ₂3, hc₁3])
    obtain ⟨hc₂ℓ₁, h | ⟨hY, eK, eJ, g, hgX, hgT, hg₁, hg₂⟩⟩ := hL1 hc₁ℓ₂
    · exact Or.inl h
    · refine Or.inr (Or.inl ⟨by rw [hY]; exact hX, 2 * k, by omega, ?_, eK, eJ, ?_, ?_⟩)
      · obtain ⟨r, rfl⟩ := hke
        omega
      · rw [hY, show 2 * k / 2 = k by omega]
        exact ⟨eX⟩
      · refine exists_wStar_conj_of_swap hD hAe hφ.1 hψ.1 hfix₁ hfix₂ hgX hgT hg₁ ?_
        rw [hc₁ℓ₂, hg₂, hc₂ℓ₁]
  ·
    have hc₁ne : (commOf φ).map A.subtype ≠ T ⊓ fixedInG A ψ := by
      intro h
      obtain ⟨hc₂ℓ₁, -⟩ := hL1 h
      exact hnc (commute_of_commOf_le hAc hA3 hφ.1.1 (hcℓ h) (hcℓ hc₂ℓ₁))
    have hY := hL2 hc₁ne
    refine Or.inl ⟨by rw [hY]; exact hX, ?_, ?_⟩
    · refine Or.inr (Or.inr (Or.inl ⟨hA27, k, hk0, hke, ?_, hlines _ inf_le_left hℓ₁3, ?_⟩))
      · rw [hY]
        exact ⟨eX⟩
      · rw [hY]
        obtain ⟨e₁⟩ := nonempty_starOf_mulEquiv_inf hD
        obtain ⟨e₂⟩ := hD8
        exact ⟨e₁.trans e₂⟩
    · rw [hY]
      exact isEmpty_mulEquiv_projSU_five hk0 eX

end Item228InspProof

open Item228InspProof

theorem insp228U4_of (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (h222 : Item222)
    (hKW : KOfWellDefinedAll) (hU4 : U4EvenTorus) : Insp228U4 := by
  intro G _ _ A E U c L hpair hA27 φ hφ ψ hψ hne X hX hKX hJX hfam _
  obtain ⟨m, hm0, hme, -, ⟨eX⟩⟩ := hfam
  exact insp228_of_U4 h45 h66 h222 hKW hU4 hpair hA27 hφ hψ hne hX hKX hJX hm0 hme eX

theorem insp228U4Half_of (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (h222 : Item222)
    (hKW : KOfWellDefinedAll) (hU4 : U4EvenTorus) : Insp228U4Half := by
  intro G _ _ A E U c L hpair hA27 φ hφ ψ hψ hne X hX hKX hJX hfam _
  obtain ⟨m, hm0, -, -, hm4, ⟨eX⟩⟩ := hfam
  exact insp228_of_U4 h45 h66 h222 hKW hU4 hpair hA27 hφ hψ hne hX hKX hJX (k := m / 2)
    (by omega) ⟨m / 4, by omega⟩ eX

end CFSG.RankThree.PartTwo.Sec21
