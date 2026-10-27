module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512WrStep
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512WrGen
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512WrCnt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace X1512

variable {G : Type} [Group G] [Finite G] {n : ℕ} {H U L N K F₁ F₂ X₁ X₂ : Subgroup G}

namespace WrStep

variable (P : WrStep H U L N K F₁ F₂ X₁ X₂)

include P

omit [Finite G] in
theorem exists_mem_not_mem_K {T : Subgroup G} (hT : IsSylowTwoOf T H) : ∃ t ∈ T, t ∉ K := by
  by_contra h
  have hTK : T ≤ K := fun t ht => by
    by_contra hn
    exact h ⟨t, ht, hn⟩
  have h1 := Subgroup.relIndex_mul_relIndex T K H hTK P.K_le
  rw [P.K_idx] at h1
  apply hT.2.2
  show 2 ∣ T.relIndex H
  rw [← h1]
  exact Dvd.intro_left _ rfl

theorem datum_one (hn : n = 3 ∨ n = 5) [(L.subgroupOf X₁).Normal] [(L.subgroupOf X₂).Normal]
    {Ψ₁ Ψ₂ : ↥K →* Equiv.Perm (Fin n)} {β₁ : ↥(G6.coreMod n) →* ↥X₁ ⧸ L.subgroupOf X₁}
    {β₂ : ↥(G6.coreMod n) →* ↥X₂ ⧸ L.subgroupOf X₂}
    (W : WrAll n P.F₁_le_K P.F₂_le_K Ψ₁ Ψ₂ β₁ β₂) {T Pm A : Subgroup G}
    (hmp : MinParabolic H T Pm) (hCP : cSecIn H L N ≤ Pm) (hAT : A ≤ T) (hAK : A ≤ K)
    (hAe : IsElemAbelian 2 A)
    (hcount : Nat.card A * Nat.card (fixSecIn A L N) =
      Nat.card ↥(A ⊓ cSecIn H L N) * Nat.card N)
    (hB : (A.subgroupOf K).map Ψ₁ ≠ ⊥) : ShapeDatum H Pm (cSecIn H L N) A := by
  have := P.normal_sub (Y := N) le_rfl
  obtain ⟨c₁, -, hprod⟩ := P.count_wr hn W.M₁ W.M₂ hAK hAe hcount
  have hker := P.ker_prod hn W.M₁ W.M₂
  obtain ⟨t, htT, htK⟩ := P.exists_mem_not_mem_K hmp.isSylow
  have hD := P.sylow_img hn W hmp.isSylow
  have hDcard := card_sylow_perm hn hD
  have hBD : (A.subgroupOf K).map Ψ₁ ≤
      (((T ⊓ K) ⊓ kerSub Ψ₂).subgroupOf K).map Ψ₁ := by
    rintro _ ⟨a, ha, rfl⟩
    have hmem : (Ψ₁ a, (1 : Equiv.Perm (Fin n))) ∈
        ((A.subgroupOf K).map Ψ₁).prod ((A.subgroupOf K).map Ψ₂) :=
      ⟨⟨a, ha, rfl⟩, Subgroup.one_mem _⟩
    rw [← hprod] at hmem
    obtain ⟨a', ha', hρ⟩ := hmem
    have h1 : Ψ₁ a' = Ψ₁ a := congrArg Prod.fst hρ
    have h2 : Ψ₂ a' = 1 := congrArg Prod.snd hρ
    have ha'A : (a' : G) ∈ A := Subgroup.mem_subgroupOf.mp ha'
    exact ⟨a', Subgroup.mem_subgroupOf.mpr ⟨⟨hAT ha'A, a'.2⟩, mem_kerSub.mpr ⟨a'.2, h2⟩⟩, h1⟩
  have hBe := isElemAbelian_map_subgroupOf Ψ₁ hAe
  obtain ⟨ξ, hξ3, -, hξnorm, hξinv, hξcl⟩ := (fin_main hn hDcard hBD hBe).2 c₁ hB
  obtain ⟨x, hxF, hxξ⟩ := W.onto₁ ξ
  have hxK : x ∈ K := P.F₁_le_K hxF
  have hρx : (Ψ₁.prod Ψ₂) ⟨x, hxK⟩ = (ξ, 1) := by
    rw [MonoidHom.prod_apply, hxξ, P.ψ₂_eq_one_of_mem_F₁ hn W.M₂ hxF]
  have hx3 : (Ψ₁.prod Ψ₂) ⟨x, hxK⟩ ^ 3 = 1 := by
    rw [hρx]
    exact Prod.ext (by simpa using hξ3) (by simp)
  have hnorm : ∀ g ∈ (A.subgroupOf K).map (Ψ₁.prod Ψ₂),
      g * (Ψ₁.prod Ψ₂) ⟨x, hxK⟩ * g⁻¹ = (Ψ₁.prod Ψ₂) ⟨x, hxK⟩ ∨
        g * (Ψ₁.prod Ψ₂) ⟨x, hxK⟩ * g⁻¹ = ((Ψ₁.prod Ψ₂) ⟨x, hxK⟩)⁻¹ := by
    intro g hg
    rw [hρx]
    rw [hprod, Subgroup.mem_prod] at hg
    rcases hξnorm g.1 hg.1 with h | h
    · left
      exact Prod.ext (by simpa using h) (by simp)
    · right
      exact Prod.ext (by simpa using h) (by simp)
  have hinv : ∃ g ∈ (A.subgroupOf K).map (Ψ₁.prod Ψ₂),
      g * (Ψ₁.prod Ψ₂) ⟨x, hxK⟩ * g⁻¹ = ((Ψ₁.prod Ψ₂) ⟨x, hxK⟩)⁻¹ := by
    obtain ⟨g₁, hg₁, hg₁ξ⟩ := hξinv
    refine ⟨(g₁, 1), ?_, ?_⟩
    · rw [hprod]
      exact ⟨hg₁, Subgroup.one_mem _⟩
    · rw [hρx]
      exact Prod.ext (by simpa using hg₁ξ) (by simp)
  obtain ⟨hx3', hxA, hxinv⟩ := datum_conditions hker hAK ⟨x, hxK⟩ hx3 hnorm hinv
  refine ⟨x, P.F₁_le hxF, ?_, hx3', hxA, hxinv⟩
  exact P.not_mem_of_closure hn W hker hmp hCP htT htK hxF (by rw [hxξ]; exact hξcl)

end WrStep

theorem shapeDatum_wr (hn : n = 3 ∨ n = 5) {T Pm A : Subgroup G} [(L.subgroupOf N).Normal]
    (c : ShapeCtx T Pm H U L N A) (hK : ¬ oTwoUpper H ≤ cSecIn H L N)
    (hφ : QuotIsoWith H (cSecIn H L N) (thompsonJ H)
      (Equiv.Perm (Fin n) ≀ᵣ Multiplicative (ZMod 2)) (Equiv.Perm (Fin n) × Equiv.Perm (Fin n)))
    (hpair : NaturalSnPair n H L N) : ShapeDatum H Pm (cSecIn H L N) A := by
  obtain ⟨F₁, F₂, X₁, X₂, hn₁, hn₂, h₁, h₂, P, hFF⟩ := exists_wrStep hn c hφ hpair
  have := hn₁
  have := hn₂
  obtain ⟨Ψ₁, Ψ₂, β₁, β₂, W⟩ := P.exists_wrAll hn h₁ h₂
  obtain ⟨hCP, -⟩ := le_and_isSylow c.mp (S152Fin.cSecIn_le_left H L N) c.normalizes c.pCoreOf_le hK
  have hAK : A ≤ F₁ ⊔ F₂ := by
    rw [hFF]
    exact c.leJ.trans le_sup_left
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_forall c.step.2.1.2
  have hAC : A ⊓ cSecIn H L N = A ⊓ pCoreOf 2 H :=
    (inf_cSecIn_eq (c.le.trans c.mp.isSylow.1) hHL).trans c.count.1
  have hcount : Nat.card A * Nat.card (fixSecIn A L N) =
      Nat.card ↥(A ⊓ cSecIn H L N) * Nat.card N := by
    rw [hAC]
    exact c.count.2
  have := P.normal_sub (Y := N) le_rfl
  by_cases hB₁ : (A.subgroupOf (F₁ ⊔ F₂)).map Ψ₁ = ⊥
  · by_cases hB₂ : (A.subgroupOf (F₁ ⊔ F₂)).map Ψ₂ = ⊥
    · exfalso
      obtain ⟨-, -, hprod⟩ := P.count_wr hn W.M₁ W.M₂ hAK c.abelian hcount
      have hker := P.ker_prod hn W.M₁ W.M₂
      apply c.offender
      intro a ha
      have h1 : (Ψ₁.prod Ψ₂) ⟨a, hAK ha⟩ ∈ (A.subgroupOf (F₁ ⊔ F₂)).map (Ψ₁.prod Ψ₂) :=
        ⟨⟨a, hAK ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
      rw [hprod, hB₁, hB₂, Subgroup.mem_prod] at h1
      have h2 : (⟨a, hAK ha⟩ : ↥(F₁ ⊔ F₂)) ∈ (Ψ₁.prod Ψ₂).ker := by
        rw [MonoidHom.mem_ker]
        exact Prod.ext (Subgroup.mem_bot.mp h1.1) (Subgroup.mem_bot.mp h1.2)
      rw [hker] at h2
      have h3 : a ∈ A ⊓ cSecIn H L N := ⟨ha, Subgroup.mem_subgroupOf.mp h2⟩
      rw [hAC] at h3
      exact h3.2
    · exact P.symm.datum_one hn W.symm c.mp hCP c.le hAK c.abelian hcount hB₂
  · exact P.datum_one hn W c.mp hCP c.le hAK c.abelian hcount hB₁

end X1512

end CFSG.Quasithin
