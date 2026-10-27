module

public import CFSG.RankThree.PartOne.D4RC.TwoLocal

public noncomputable section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley.TrialityFold CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups Pointwise

set_option linter.unusedSectionVars false

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

section Group

variable {G : Type*} [Group G]

theorem rcr_centralizer_eq {p : ℕ} (hp : p.Prime) {x e : G} (hx : x ^ p = 1) (hx1 : x ≠ 1)
    (he : e ∈ Subgroup.zpowers x) (he1 : e ≠ 1) :
    Subgroup.centralizer ({e} : Set G) = Subgroup.centralizer ({x} : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have hox : orderOf x = p := orderOf_eq_prime hx hx1
  have hcard : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hox]
  have : Finite (Subgroup.zpowers x) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  have hle : Subgroup.zpowers e ≤ Subgroup.zpowers x := Subgroup.zpowers_le.2 he
  have hxe : x ∈ Subgroup.zpowers e := by
    have hne : Subgroup.zpowers e ≠ ⊥ := fun h => he1 (by
      have : e ∈ Subgroup.zpowers e := Subgroup.mem_zpowers e
      rw [h, Subgroup.mem_bot] at this
      exact this)
    have hdvd : Nat.card (Subgroup.zpowers e) ∣ p := hcard ▸ Subgroup.card_dvd_of_le hle
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | hp'
    · exact absurd (Subgroup.card_eq_one.1 h1) hne
    · have : Subgroup.zpowers e = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hp'])
      rw [this]
      exact Subgroup.mem_zpowers x
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hxe
  ext z
  simp only [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    rw [← hn]
    exact ((Commute.zpow_left (h.symm) n).symm)
  · intro h
    exact ((Commute.zpow_left h.symm m).symm)

end Group

section Regular

variable {ℓ f : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {ε : ℤ}
  {p : ℕ} {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

@[expose] def rcrPsi (F : RclFrame ℓ f K σ ε p L) (c : 𝒞[K, σ]) :
    𝒞[K, σ] →* ModGL TwistTag.D4.tag L :=
  (MulAut.conj F.g0⁻¹).toMonoidHom.comp ((triEmb K σ L).comp (MulAut.conj c).toMonoidHom)

theorem rcrPsi_apply (F : RclFrame ℓ f K σ ε p L) (c y : 𝒞[K, σ]) :
    rcrPsi F c y = F.g0⁻¹ * triEmb K σ L (c * y * c⁻¹) * F.g0 := by
  change (MulAut.conj F.g0⁻¹ : MulAut (ModGL TwistTag.D4.tag L))
    (triEmb K σ L ((MulAut.conj c : MulAut 𝒞[K, σ]) y)) = _
  rw [MulAut.conj_apply, MulAut.conj_apply, inv_inv]

theorem rcrPsi_injective (F : RclFrame ℓ f K σ ε p L) (c : 𝒞[K, σ]) :
    Function.Injective (rcrPsi F c) := by
  intro y y' h
  rw [rcrPsi_apply, rcrPsi_apply] at h
  have h2 := triEmb_injective (mul_left_cancel (mul_right_cancel h))
  exact mul_left_cancel (mul_right_cancel h2)

theorem rcrPsi_mem_adjointGroup (F : RclFrame ℓ f K σ ε p L) (c y : 𝒞[K, σ]) :
    rcrPsi F c y ∈ adjointGroup TwistTag.D4.tag L := by
  rw [rcrPsi_apply]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ F.hg0C)
    (triEmb_mem_adjointGroup _)) F.hg0C

theorem rcrPsi_fixed (F : RclFrame ℓ f K σ ε p L) (c y : 𝒞[K, σ]) :
    F.n * twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) (rcrPsi F c y) * F.n⁻¹ =
      rcrPsi F c y := by
  have hcomm := d4Q_hcomm K σ F.hσ L
  have hι := triEmb_fixed (K := K) (σ := σ) (L := L) (iterateFrobenius L ℓ f) hcomm
    (c * y * c⁻¹)
  rw [rcrPsi_apply, map_mul, map_mul, map_inv, F.hg0, hι]
  group

theorem rcr_odd_card_centralizer (F : RclFrame ℓ f K σ ε p L) {y c : 𝒞[K, σ]}
    (hy : orderOf y = p) {b : Fin TwistTag.D4.tag.rank → Lˣ}
    (hb : rootDiagUnit TwistTag.D4.tag b = F.g0⁻¹ * triEmb K σ L (c * y * c⁻¹) * F.g0)
    (hker : rootCharKernel b = ∅) :
    Odd (Nat.card (Subgroup.centralizer ({y} : Set 𝒞[K, σ]))) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hbψ : rootDiagUnit TwistTag.D4.tag b = rcrPsi F c y := by rw [hb, rcrPsi_apply]
  have hd : orderOf (rootDiagUnit TwistTag.D4.tag b) = p := by
    rw [hbψ, orderOf_injective _ (rcrPsi_injective F c), hy]
  have hreg : ∀ α : Fin TwistTag.D4.tag.rank → ℤ, IsRoot TwistTag.D4.tag α →
      rootChar b α ≠ 1 := fun α hα h1 => by
    have : α ∈ rootCharKernel b := ⟨hα, h1⟩
    rw [hker] at this
    exact this
  have hp2 : p ≠ 2 := by have := F.hp3; omega
  have hpL : ringChar L ≠ p := by
    rw [ringChar.eq L ℓ, F.hℓ2]
    exact hp2.symm
  have hthm := (D4_odd_prime_regular_root_character_centralizer L p F.hp hp2 hpL b hd hreg).2
  have hT : ∀ z : Subgroup.centralizer ({y} : Set 𝒞[K, σ]), rcrPsi F c z ∈
      twistedTorusOf F.n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) := by
    intro z
    have hzy : (z : 𝒞[K, σ]) * y = y * z :=
      (Subgroup.mem_centralizer_iff.1 z.2 y rfl).symm
    have hcomm : rootDiagUnit TwistTag.D4.tag b * rcrPsi F c z *
        (rootDiagUnit TwistTag.D4.tag b)⁻¹ = rcrPsi F c z := by
      rw [hbψ, ← map_mul, ← map_inv, ← map_mul, show y * (z : 𝒞[K, σ]) * y⁻¹ = z by
        rw [← hzy]; group]
    have hmem := (hthm (rcrPsi F c z)).1 ⟨rcrPsi_mem_adjointGroup F c z, hcomm⟩
    exact ⟨hmem, rcrPsi_fixed F c z⟩
  let φ : Subgroup.centralizer ({y} : Set 𝒞[K, σ]) →*
      twistedTorusOf F.n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) :=
    ((rcrPsi F c).comp (Subgroup.centralizer ({y} : Set 𝒞[K, σ])).subtype).codRestrict _ hT
  have hφ : Function.Injective φ := fun z z' h =>
    Subtype.ext (rcrPsi_injective F c (congrArg Subtype.val h))
  have hodd := d4T36_torus_card_odd F.hf F.hε F.hn F.w F.hnw F.hw
  have hfin : Finite (twistedTorusOf F.n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f))) :=
    Nat.finite_of_card_ne_zero hodd.pos.ne'
  exact Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_injective φ hφ)

theorem rcr_twoCoreLocal_regular (F : RclFrame ℓ f K σ ε p L) {y c : 𝒞[K, σ]}
    (hy : orderOf y = p) {b : Fin TwistTag.D4.tag.rank → Lˣ}
    (hb : rootDiagUnit TwistTag.D4.tag b = F.g0⁻¹ * triEmb K σ L (c * y * c⁻¹) * F.g0)
    (hker : rootCharKernel b = ∅) (Γ : Subgroup 𝒞[K, σ]) : TwoCoreLocal Γ y :=
  Or.inl (rcr_odd_card_centralizer F hy hb hker)

theorem rcr_even_card_centralizer (F : RclFrame ℓ f K σ ε p L) {x : 𝒞[K, σ]} {i : Fin 4}
    (sp : RclSpecial F x i) : Even (Nat.card (Subgroup.centralizer ({x} : Set 𝒞[K, σ]))) := by
  have hdvd : Nat.card (rclPx sp) ∣ Nat.card (Subgroup.centralizer ({x} : Set 𝒞[K, σ])) :=
    Subgroup.card_dvd_of_le (rclPx_le_centralizer sp)
  rw [card_rclPx] at hdvd
  have h2 : 2 ∣ Nat.card (rclQ F i) := by
    have h8 : 2 ∣ ℓ ^ f := by rw [F.hℓ2]; exact dvd_pow_self 2 (by have := F.hf; omega)
    have h9 : 2 ∣ (ℓ ^ f) ^ 3 := dvd_pow h8 (by norm_num)
    obtain ⟨hc1, hc2⟩ := rcl_card_rclQ F i
    rcases F.hε with h | h
    · rw [hc1 h]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h9 _) _
    · rw [hc2 h]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h9 _) _
  exact even_iff_two_dvd.2 (h2.trans hdvd)

theorem rcr_hyp_twoCore (F : RclFrame ℓ f K σ ε p L) {E : Subgroup 𝒞[K, σ]}
    (hEp : ∀ y ∈ E, y ^ p = 1) (hEc : Nat.card E = p ^ 2) {c : 𝒞[K, σ]} (x : Fin 4 → 𝒞[K, σ])
    (hx1 : ∀ j, x j ∈ E ∧ x j ≠ 1)
    (hcover : ∀ y ∈ E, y ≠ 1 → (∃ j, y ∈ Subgroup.zpowers (x j)) ∨
      ∃ b : Fin TwistTag.D4.tag.rank → Lˣ,
        rootDiagUnit TwistTag.D4.tag b = F.g0⁻¹ * triEmb K σ L (c * y * c⁻¹) * F.g0 ∧
        rootCharKernel b = ∅)
    {Γ : Subgroup 𝒞[K, σ]} (hEΓ : E ≤ Γ) (hPΓ : ∀ j, ∃ sp : RclSpecial F (x j) j, rclPx sp ≤ Γ) :
    ∀ N : Subgroup ↥Γ, N.Normal → IsPGroup 2 N → N = ⊥ := by
  have hp := F.hp
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by have := F.hp3; omega
  have hEp' : ∀ y : E, y ^ p = 1 := fun y =>
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hEp y y.2)
  refine rcs_hyp_twoCore hp hp2 hEΓ hEp' hEc fun e he he1 => ?_
  rcases hcover e he he1 with ⟨j, hj⟩ | ⟨b, hb, hker⟩
  · obtain ⟨sp, hsp⟩ := hPΓ j
    have hloc := rct_twoCoreLocal F sp hsp
    have hC := rcr_centralizer_eq hp (hEp _ (hx1 j).1) (hx1 j).2 hj he1
    unfold TwoCoreLocal at hloc ⊢
    rw [hC]
    exact hloc
  · exact rcr_twoCoreLocal_regular F (orderOf_eq_prime (hEp e he) he1) hb hker Γ

end Regular

end CFSG.RankThree.PartOne.D4RC
