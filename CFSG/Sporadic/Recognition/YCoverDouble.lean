module

public import CFSG.Sporadic.Recognition.YCoverLift
public import CFSG.Monster.Schur.CentralEps
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.Sporadic.Recognition.YCover

open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons evalWord_append)
open CFSG.Monster.GMS.R433Cover (IsZ cm evalWord_mul_central map_evalWord_of_forall
  commute_of_sq evalWord_reverse_inv)
open CFSG.YGroups (yRels yEdges ngen spiderWord pairExp pairWord yGen YGroup yModelHom
  yModelHom_yGen)
open scoped commutatorElement

variable {p q r : ℕ} {E G : Type*} [Group E] [Group G]

theorem commutatorElement_mul_central {x y k : E} (hk : ∀ g : E, g * k = k * g) :
    ⁅x * k, y⁆ = ⁅x, y⁆ ∧ ⁅x, y * k⁆ = ⁅x, y⁆ := by
  constructor
  · calc ⁅x * k, y⁆ = x * (k * y) * (k⁻¹ * x⁻¹) * y⁻¹ := by
          rw [commutatorElement_def]; group
      _ = x * (y * k) * (k⁻¹ * x⁻¹) * y⁻¹ := by rw [← hk y]
      _ = ⁅x, y⁆ := by rw [commutatorElement_def]; group
  · calc ⁅x, y * k⁆ = x * y * (k * x⁻¹) * k⁻¹ * y⁻¹ := by
          rw [commutatorElement_def]; group
      _ = x * y * (x⁻¹ * k) * k⁻¹ * y⁻¹ := by rw [← hk x⁻¹]
      _ = ⁅x, y⁆ := by rw [commutatorElement_def]; group

theorem surj_of_perfect {π : E →* G} {z : E} (hz : CentralKernel π z) {Q : Type*} [Group Q]
    {ρ : Q →* G} {θ : Q →* E} (hπθ : π.comp θ = ρ) (hρ : Function.Surjective ρ)
    (hperf : commutator E = ⊤) : Function.Surjective θ := by
  obtain ⟨hzc, hz2, -, hker⟩ := hz
  have hdecomp : ∀ e : E, ∃ s : E, s ∈ θ.range ∧ ∃ k, IsZ z k ∧ e = s * k := by
    intro e
    obtain ⟨r, hr⟩ := hρ (π e)
    have hπr : π (θ r) = π e := by
      have := congrArg (fun f => f r) hπθ
      simpa [hr] using this
    have h1 : π ((θ r)⁻¹ * e) = 1 := by
      rw [map_mul, map_inv, hπr, inv_mul_cancel]
    exact ⟨θ r, ⟨r, rfl⟩, (θ r)⁻¹ * e, hker _ h1, by group⟩
  have hcomm : commutator E ≤ θ.range := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨s₁, hs₁, k₁, hk₁, rfl⟩ := hdecomp a
    obtain ⟨s₂, hs₂, k₂, hk₂, rfl⟩ := hdecomp b
    have c₁ := CFSG.Monster.GMS.R433Cover.IsZ.comm hzc hz2 hk₁
    have c₂ := CFSG.Monster.GMS.R433Cover.IsZ.comm hzc hz2 hk₂
    rw [(commutatorElement_mul_central c₁).1, (commutatorElement_mul_central c₂).2,
      commutatorElement_def]
    exact θ.range.mul_mem (θ.range.mul_mem (θ.range.mul_mem hs₁ hs₂) (θ.range.inv_mem hs₁))
      (θ.range.inv_mem hs₂)
  intro e
  have h := hcomm
  rw [hperf] at h
  exact h (Subgroup.mem_top e)

theorem nonempty_mulEquiv_of_cover (D : FlagData p q r) {F : YGroup p q r}
    (hFdef : F = evalWord (yGen p q r) D.Fw ^ 9) [Finite (QuotY p q r F)] {π : E →* G} {z : E}
    (hz : CentralKernel π z) (hπ : Function.Surjective π) {ρ : QuotY p q r F →* G}
    (hρ : Function.Surjective ρ) {Y : List ℕ} (hYlt : ∀ c ∈ Y, c < ngen p q r)
    (hY : ConjIdentity D (marked F ρ) Y) (h1 : SpiderIdentity p q (marked F ρ))
    (hperf : commutator E = ⊤) (hcard : Nat.card (QuotY p q r F) ≤ Nat.card E) :
    Nonempty (E ≃* QuotY p q r F) := by
  obtain ⟨θ, hθ⟩ := exists_hom_quot D hFdef hz hπ ρ hYlt hY h1
  have hsurj := surj_of_perfect hz hθ hρ hperf
  have hbij := hsurj.bijective_of_nat_card_le hcard
  exact ⟨(MulEquiv.ofBijective θ hbij).symm⟩

theorem exists_centralKernel_of_card_ker {π : E →* G} (hk : Nat.card π.ker = 2) :
    ∃ z : E, CentralKernel π z := by
  obtain ⟨z, hzK, -, hzall⟩ := CFSG.Monster.Schur.exists_ker_elem π hk
  refine ⟨z, ?_, ?_, by simpa using hzK, hzall⟩
  · exact fun x => Subgroup.mem_center_iff.mp
      (CFSG.Monster.Schur.mem_center_of_mem_ker π hk hzK) x
  · rw [← sq]; exact CFSG.Monster.Schur.sq_eq_one_of_mem_ker π hk hzK

theorem identities_of_Y (D : FlagData p q r) {F : YGroup p q r}
    (hFdef : F = evalWord (yGen p q r) D.Fw ^ 9) (ρ : QuotY p q r F →* G) (Y : List ℕ)
    (hid2 : evalWord (yGen p q r) (Y.reverse ++ [D.t₁, D.t₂, D.t₃] ++ Y) =
      evalWord (yGen p q r) ([D.q₁, D.q₂, D.q₃, D.q₄] ++ (List.replicate 9 D.Fw).flatten))
    (hid1 : evalWord (yGen p q r)
      (List.replicate 3 ((List.replicate 5 (spiderWord p q)).flatten ++ [0])).flatten = 1) :
    ConjIdentity D (marked F ρ) Y ∧ SpiderIdentity p q (marked F ρ) := by
  have hinv := marked_mul_self F ρ
  constructor
  · apply conjIdentity_of_eq D hinv Y
    have e1 : evalWord (yGen p q r) ([D.q₁, D.q₂, D.q₃, D.q₄] ++ (List.replicate 9 D.Fw).flatten) =
        evalWord (yGen p q r) [D.q₁, D.q₂, D.q₃, D.q₄] * F := by
      rw [evalWord_append, evalWord_replicate_flatten', hFdef]
    rw [e1] at hid2
    have h3 := congrArg (ρ.comp (quotMk F)) hid2
    have h4 : (ρ.comp (quotMk F)) F = 1 := by simp [quotMk_self]
    rw [map_mul, h4, mul_one] at h3
    simpa only [← marked_evalWord] using h3
  · apply spiderIdentity_of_eq
    rw [marked_evalWord, hid1, map_one]

theorem noPerfectDoubleCover_quot (D : FlagData p q r) {F : YGroup p q r}
    (hFdef : F = evalWord (yGen p q r) D.Fw ^ 9) {Y : List ℕ} (hYlt : ∀ c ∈ Y, c < ngen p q r)
    (hY : ConjIdentity D (marked F (MonoidHom.id (QuotY p q r F))) Y)
    (h1 : SpiderIdentity p q (marked F (MonoidHom.id (QuotY p q r F)))) :
    CFSG.Monster.Schur.NoPerfectDoubleCover (QuotY p q r F) := by
  intro E _ π hπ hperf hk
  obtain ⟨z, hz⟩ := exists_centralKernel_of_card_ker hk
  obtain ⟨θ, hθ⟩ := exists_hom_quot D hFdef hz hπ (MonoidHom.id _) hYlt hY h1
  have hsurj := surj_of_perfect hz hθ Function.surjective_id (Group.isPerfect_def.1 hperf)
  have hπθ : ∀ x, π (θ x) = x := fun x => by
    have := congrArg (fun f => f x) hθ
    simpa using this
  have hker : π.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := hsurj x
    have hy : y = 1 := by rw [← hπθ y]; exact hx
    rw [hy, map_one]
    exact one_mem _
  rw [hker, Subgroup.card_bot] at hk
  exact absurd hk (by norm_num)

theorem nonempty_mulEquiv_quot_of_doubleCover (D : FlagData p q r) {F : YGroup p q r}
    (hFdef : F = evalWord (yGen p q r) D.Fw ^ 9) [Finite (QuotY p q r F)] {X : Type*} [Group X]
    {ρ : QuotY p q r F →* X} (hρ : Function.Surjective ρ) {Y : List ℕ}
    (hYlt : ∀ c ∈ Y, c < ngen p q r) (hY : ConjIdentity D (marked F ρ) Y)
    (h1 : SpiderIdentity p q (marked F ρ)) (hcard : Nat.card (QuotY p q r F) ≤ 2 * Nat.card X)
    {E : Type*} [Group E] (φ : E →* X) (hφ : Function.Surjective φ) (hperf : Group.IsPerfect E)
    (hk : Nat.card φ.ker = 2) : Nonempty (E ≃* QuotY p q r F) := by
  obtain ⟨z, hz⟩ := exists_centralKernel_of_card_ker hk
  have hcardE : Nat.card (QuotY p q r F) ≤ Nat.card E := by
    rw [CFSG.Monster.Schur.card_eq_mul_card_ker φ hφ, hk, mul_comm]
    exact hcard
  exact nonempty_mulEquiv_of_cover D hFdef hz hφ hρ hYlt hY h1 (Group.isPerfect_def.1 hperf)
    hcardE

end CFSG.Sporadic.Recognition.YCover
