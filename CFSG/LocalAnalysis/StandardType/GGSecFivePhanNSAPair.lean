module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSADefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSAPairAux
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSAPairAux2

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

private theorem ggPhanNSAPairAux_refl_eq_swap
    {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs) {n : ℕ}
    (ε : Equiv.Perm (Fin n) ≃* ↥(ggAutomizer X Bs))
    (hεrefl : ∀ a b : Fin n, a ≠ b →
      GGIsReflection p ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs))
    {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs) (hr : GGIsReflection p r) :
    ∃ a b : Fin n, a ≠ b ∧ r = ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨V, hVadd, hVmod, ⟨ι⟩⟩ := exists_ggLinData (p := p) hBs
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod p) V := hVmod
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  let T : Equiv.Perm (Fin n) →* (V ≃ₗ[ZMod p] V) :=
    (ggLin (p := p) ι).comp ((Subgroup.subtype (ggAutomizer X Bs)).comp ε.toMonoidHom)
  have hT : ∀ π : Equiv.Perm (Fin n),
      T π = ggLin (p := p) ι (((ε π : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)) := fun _ => rfl
  have hlin : ∀ {φ : MulAut ↥Bs}, GGIsReflection p φ → IsLinRefl (ggLin (p := p) ι φ) := by
    intro φ hφ
    obtain ⟨x, f, hfx, hrepr⟩ := exists_of_ggIsReflection (p := p) ι hφ
    rw [ggLin_eq_reflection ι hfx hrepr]
    exact ⟨x, f, hfx, fun v => Module.reflection_apply v hfx⟩
  have hinj : Function.Injective T := by
    intro x y hxy
    exact ε.injective (Subtype.ext (ggLin_injective ι hxy))
  have hsw : ∀ a b : Fin n, a ≠ b → IsLinRefl (T (Equiv.swap a b)) := by
    intro a b hab
    rw [hT]
    exact hlin (hεrefl a b hab)
  let π : Equiv.Perm (Fin n) := ε.symm ⟨r, hrA⟩
  have hπ : IsLinRefl (T π) := by
    rw [hT]
    have hval : ((ε π : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) = r := by
      change ((ε (ε.symm ⟨r, hrA⟩) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) = r
      simp
    rw [hval]
    exact hlin hr
  obtain ⟨a, b, hab, hswap⟩ := isSwap_of_isLinRefl hp2 T hinj hsw hπ
  refine ⟨a, b, hab, ?_⟩
  have hval : ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) = r := by
    rw [← hswap]
    change ((ε π : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) = r
    change ((ε (ε.symm ⟨r, hrA⟩) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) = r
    simp
  exact hval.symm

private lemma ggPhanNSAPairAux_swap_disjoint {n : ℕ} {a b c d : Fin n}
    (hab : a ≠ b) (hcd : c ≠ d)
    (hcomm : Equiv.swap a b * Equiv.swap c d = Equiv.swap c d * Equiv.swap a b)
    (hne : Equiv.swap a b ≠ Equiv.swap c d) :
    Equiv.Perm.Disjoint (Equiv.swap a b) (Equiv.swap c d) := by
  rw [Equiv.Perm.disjoint_iff_eq_or_eq]
  intro x
  by_contra h
  push Not at h
  obtain ⟨hx1, hx2⟩ := h
  have hxt : x ∈ (Equiv.swap c d).support := by
    rw [Equiv.Perm.mem_support]; exact hx2
  have hxs : x ∈ (Equiv.swap a b).support := by
    rw [Equiv.Perm.mem_support]; exact hx1
  have hfx_t : Equiv.swap a b x ∈ (Equiv.swap c d).support :=
    (Equiv.Perm.mem_support_iff_of_commute hcomm x).mpr hxt
  have hb_or : x = a ∨ x = b := by
    have := hxs
    rwa [Equiv.Perm.support_swap hab, Finset.mem_insert, Finset.mem_singleton] at this
  have hsx : Equiv.swap a b x = a ∨ Equiv.swap a b x = b := by
    rcases hb_or with hx | hx
    · exact Or.inr (by rw [hx, Equiv.swap_apply_left])
    · exact Or.inl (by rw [hx, Equiv.swap_apply_right])
  have ha_t : a ∈ (Equiv.swap c d).support := by
    rcases hb_or with hx | hx
    · exact hx ▸ hxt
    · rcases hsx with h | h
      · rw [← h]; exact hfx_t
      · exact absurd (h.trans hx.symm) hx1
  have hb_t : b ∈ (Equiv.swap c d).support := by
    rcases hb_or with hx | hx
    · rcases hsx with h | h
      · exact absurd (h.trans hx.symm) hx1
      · rw [← h]; exact hfx_t
    · exact hx ▸ hxt
  have ha_cd : a = c ∨ a = d := by
    have := ha_t
    rwa [Equiv.Perm.support_swap hcd, Finset.mem_insert, Finset.mem_singleton] at this
  have hb_cd : b = c ∨ b = d := by
    have := hb_t
    rwa [Equiv.Perm.support_swap hcd, Finset.mem_insert, Finset.mem_singleton] at this
  rcases ha_cd with hac | had
  · rcases hb_cd with hbc | hbd
    · exact hab (by rw [hac, hbc])
    · exact hne (by rw [hac, hbd])
  · rcases hb_cd with hbc | hbd
    · exact hne (by rw [had, hbc, Equiv.swap_comm])
    · exact hab (by rw [had, hbd])

private theorem ggPhanNSAPairAux_suPairBlock_comm
    {K : Type} [Field K] [Finite K] {p f n : ℕ} [Fact p.Prime] [CharP K p]
    {a b c d : Fin n} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    ∀ A ∈ ggSuPairBlock K p f n a b, ∀ B ∈ ggSuPairBlock K p f n c d, A * B = B * A := by
  classical
  intro A hA B hB
  let P : Matrix (Fin n) (Fin n) K := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1
  let Q : Matrix (Fin n) (Fin n) K := ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1
  have hP : ∀ i j : Fin n, ¬ ((i = a ∨ i = b) ∧ (j = a ∨ j = b)) → P i j = 0 := by
    intro i j hij
    simp only [P, Matrix.sub_apply]
    rw [hA i j (by tauto), sub_self]
  have hQ : ∀ i j : Fin n, ¬ ((i = c ∨ i = d) ∧ (j = c ∨ j = d)) → Q i j = 0 := by
    intro i j hij
    simp only [Q, Matrix.sub_apply]
    rw [hB i j (by tauto), sub_self]
  have hPQ : P * Q = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = a ∨ k = b
    · have hkc : k ≠ c := by
        intro hkc
        rcases hk with h | h
        · exact hac (h.symm.trans hkc)
        · exact hbc (h.symm.trans hkc)
      have hkd : k ≠ d := by
        intro hkd
        rcases hk with h | h
        · exact had (h.symm.trans hkd)
        · exact hbd (h.symm.trans hkd)
      have hk' : ¬ ((k = c ∨ k = d) ∧ (j = c ∨ j = d)) := by
        rintro ⟨h1, -⟩
        exact h1.elim hkc hkd
      rw [hQ k j hk', mul_zero]
    · have hk' : ¬ ((i = a ∨ i = b) ∧ (k = a ∨ k = b)) := by
        rintro ⟨-, h2⟩
        exact hk h2
      rw [hP i k hk', zero_mul]
  have hQP : Q * P = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = c ∨ k = d
    · have hka : k ≠ a := by
        intro hka'
        rcases hk with h | h
        · exact hac (hka'.symm.trans h)
        · exact had (hka'.symm.trans h)
      have hkb : k ≠ b := by
        intro hkb'
        rcases hk with h | h
        · exact hbc (hkb'.symm.trans h)
        · exact hbd (hkb'.symm.trans h)
      have hk' : ¬ ((k = a ∨ k = b) ∧ (j = a ∨ j = b)) := by
        rintro ⟨h1, -⟩
        exact h1.elim hka hkb
      rw [hP k j hk', mul_zero]
    · have hk' : ¬ ((i = c ∨ i = d) ∧ (k = c ∨ k = d)) := by
        rintro ⟨-, h2⟩
        exact hk h2
      rw [hQ i k hk', zero_mul]
  have hAm : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + P := by
    dsimp only [P]; abel
  have hBm : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + Q := by
    dsimp only [Q]; abel
  have hkey : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [hAm, hBm]
    have hdiff : (1 + P) * (1 + Q) - (1 + Q) * (1 + P) = P * Q - Q * P := by
      noncomm_ring
    rw [hPQ, hQP, sub_zero] at hdiff
    exact sub_eq_zero.mp hdiff
  apply Subtype.ext
  apply Units.ext
  exact hkey

private lemma ggPhanNSAPairAux_swap_overlap {n : ℕ} {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    (hcomm : Equiv.swap a b * Equiv.swap c d ≠ Equiv.swap c d * Equiv.swap a b) :
    a = c ∨ a = d ∨ b = c ∨ b = d := by
  by_contra h
  push Not at h
  obtain ⟨hac, had, hbc, hbd⟩ := h
  apply hcomm
  apply Equiv.Perm.Disjoint.commute
  rw [Equiv.Perm.disjoint_iff_eq_or_eq]
  intro x
  by_cases hxa : x = a
  · subst hxa
    exact Or.inr (Equiv.swap_apply_of_ne_of_ne hac had)
  by_cases hxb : x = b
  · subst hxb
    exact Or.inr (Equiv.swap_apply_of_ne_of_ne hbc hbd)
  by_cases hxc : x = c
  · subst hxc
    exact Or.inl (Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm)
  by_cases hxd : x = d
  · subst hxd
    exact Or.inl (Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm)
  exact Or.inl (Equiv.swap_apply_of_ne_of_ne hxa hxb)

private lemma ggPhanNSAPairAux_share3 {n : ℕ} {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    (hcomm : Equiv.swap a b * Equiv.swap c d ≠ Equiv.swap c d * Equiv.swap a b) :
    ∃ x y z : Fin n, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      ({a, b} : Finset (Fin n)) = {x, y} ∧ ({c, d} : Finset (Fin n)) = {y, z} := by
  have hne : Equiv.swap a b ≠ Equiv.swap c d := fun h => hcomm (by rw [h])
  rcases ggPhanNSAPairAux_swap_overlap hab hcd hcomm with hac | had | hbc | hbd
  · refine ⟨b, a, d, hab.symm, ?_, ?_, Finset.pair_comm a b, ?_⟩
    · intro h; exact hcd (hac.symm.trans h)
    · intro h; exact hne (by rw [hac, h])
    · rw [hac]
  · refine ⟨b, a, c, hab.symm, ?_, ?_, Finset.pair_comm a b, ?_⟩
    · intro h; exact hcd (h.symm.trans had)
    · intro h; exact hne (by rw [had, h, Equiv.swap_comm])
    · rw [had, Finset.pair_comm]
  · refine ⟨a, b, d, hab, ?_, ?_, rfl, ?_⟩
    · intro h; exact hcd (hbc.symm.trans h)
    · intro h; exact hne (by rw [hbc, h, Equiv.swap_comm])
    · rw [hbc, Finset.pair_comm]
  · refine ⟨a, b, c, hab, ?_, ?_, rfl, ?_⟩
    · intro h; exact hcd (h.symm.trans hbd)
    · intro h; exact hne (by rw [hbd, h])
    · rw [hbd, Finset.pair_comm]

private lemma ggPhanNSAPairAux_suPairBlock_congr {K : Type} [Field K] [Finite K] {p f n : ℕ}
    [Fact p.Prime] [CharP K p] {a b c d : Fin n}
    (h : ({a, b} : Finset (Fin n)) = {c, d}) :
    ggSuPairBlock K p f n a b = ggSuPairBlock K p f n c d := by
  have hiff : ∀ i : Fin n, (i ≠ a ∧ i ≠ b) ↔ (i ≠ c ∧ i ≠ d) := by
    intro i
    constructor
    · rintro ⟨hi1, hi2⟩
      have h1 : i ∉ ({a, b} : Finset (Fin n)) := by simp [hi1, hi2]
      rw [h] at h1
      simpa using h1
    · rintro ⟨hi1, hi2⟩
      have h1 : i ∉ ({c, d} : Finset (Fin n)) := by simp [hi1, hi2]
      rw [← h] at h1
      simpa using h1
  apply Subgroup.ext
  intro M
  simp only [ggSuPairBlock]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  exact imp_congr (or_congr (hiff i) (hiff j)) Iff.rfl
theorem ggSecFivePhanPairAInput_of_nsKGPos
    (hNS : GGSecFiveNSKGPosAInput) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
        ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
          GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∃ (m : ℕ) (σ : Fin m ≃ ι), 5 ≤ m ∧ M = (CoxeterMatrix.A m).reindex σ) →
          (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) →
          ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → ¬ GGSplitLie p X →
            ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e →
            ∀ r' ∈ ggAutomizer X Bs, r' ∈ ggCoxRefl M e → r ≠ r' →
              (r * r' = r' * r →
                ∀ a ∈ ggRankOneIn X Bs r, ∀ b ∈ ggRankOneIn X Bs r', a * b = b * a) ∧
              (r * r' ≠ r' * r →
                ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (f : ℕ),
                  Nat.card K = (2 ^ f) ^ 2 →
                  Nat.card (ggRankOneIn X Bs r) = 2 ^ f * ((2 ^ f) ^ 2 - 1) →
                  ∃ W : Subgroup G, UnitaryBlockStandardPair K 2 f W
                    (ggRankOneIn X Bs r) (ggRankOneIn X Bs r')) := by
  classical
  intro G _ _ p B Bs x L D J 𝒦 hcfg hL ι M e hpres hAtype h6 X hX hXns r hrA hrC r' hrA' hrC' hne
  obtain ⟨K, hKfield, hKfin, hKchar, f, n, ψ, hKcard, hn4, hker, hrange, hpq, hpos, -⟩ :=
    hNS G p B Bs x L D J 𝒦 hcfg hL ι M e hpres hAtype h6 X hX hXns
  letI : Field K := hKfield
  letI : Finite K := hKfin
  letI : CharP K 2 := hKchar
  obtain ⟨ε, hεrefl, hεlevi⟩ := hpos
  refine ⟨?_, ?_⟩
  ·
    intro hcomm a ha b hb
    have hp : p.Prime := (ggRouteCfg_prime hcfg).1
    have hp2 : p ≠ 2 := (ggRouteCfg_prime hcfg).2
    have hBs : IsElemAbelian p Bs := ggRouteCfg_isElemAbelian hcfg
    have hrefl : GGIsReflection p r := ggCoxRefl_isReflection hpres.2 hrC
    have hrefl' : GGIsReflection p r' := ggCoxRefl_isReflection hpres.2 hrC'
    obtain ⟨a₁, b₁, hab₁, hr_eq⟩ :=
      ggPhanNSAPairAux_refl_eq_swap hp hp2 hBs ε hεrefl hrA hrefl
    obtain ⟨c₁, d₁, hcd₁, hr'_eq⟩ :=
      ggPhanNSAPairAux_refl_eq_swap hp hp2 hBs ε hεrefl hrA' hrefl'
    have hcomm_swap : Equiv.swap a₁ b₁ * Equiv.swap c₁ d₁ =
        Equiv.swap c₁ d₁ * Equiv.swap a₁ b₁ := by
      apply ε.injective
      apply Subtype.ext
      simp only [map_mul, Subgroup.coe_mul]
      rw [← hr_eq, ← hr'_eq]
      exact hcomm
    have hne_swap : Equiv.swap a₁ b₁ ≠ Equiv.swap c₁ d₁ := by
      intro h
      apply hne
      rw [hr_eq, hr'_eq, h]
    have hdisj : ∀ x : Fin n,
        Equiv.swap a₁ b₁ x = x ∨ Equiv.swap c₁ d₁ x = x :=
      Equiv.Perm.disjoint_iff_eq_or_eq.mp
        (ggPhanNSAPairAux_swap_disjoint hab₁ hcd₁ hcomm_swap hne_swap)
    have hac : a₁ ≠ c₁ := by
      intro h
      rcases hdisj a₁ with h1 | h2
      · rw [Equiv.swap_apply_left] at h1
        exact hab₁ h1.symm
      · rw [h, Equiv.swap_apply_left] at h2
        exact hcd₁ h2.symm
    have had : a₁ ≠ d₁ := by
      intro h
      rcases hdisj a₁ with h1 | h2
      · rw [Equiv.swap_apply_left] at h1
        exact hab₁ h1.symm
      · rw [h, Equiv.swap_apply_right] at h2
        exact hcd₁ h2
    have hbc : b₁ ≠ c₁ := by
      intro h
      rcases hdisj b₁ with h1 | h2
      · rw [Equiv.swap_apply_right] at h1
        exact hab₁ h1
      · rw [h, Equiv.swap_apply_left] at h2
        exact hcd₁ h2.symm
    have hbd : b₁ ≠ d₁ := by
      intro h
      rcases hdisj b₁ with h1 | h2
      · rw [Equiv.swap_apply_right] at h1
        exact hab₁ h1
      · rw [h, Equiv.swap_apply_right] at h2
        exact hcd₁ h2
    have hrS : ggRankOneIn X Bs r = (ggSuPairBlock K 2 f n a₁ b₁).map ψ := by
      rw [hr_eq]; exact hεlevi a₁ b₁ hab₁
    have hr'S : ggRankOneIn X Bs r' = (ggSuPairBlock K 2 f n c₁ d₁).map ψ := by
      rw [hr'_eq]; exact hεlevi c₁ d₁ hcd₁
    rw [hrS] at ha
    rw [hr'S] at hb
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hb
    simpa only [map_mul] using
      congrArg ψ (ggPhanNSAPairAux_suPairBlock_comm hac had hbc hbd u hu v hv)
  ·
    intro hnc K' _ _ _ f' hK' hS
    have hp : p.Prime := (ggRouteCfg_prime hcfg).1
    have hp2 : p ≠ 2 := (ggRouteCfg_prime hcfg).2
    have hBs : IsElemAbelian p Bs := ggRouteCfg_isElemAbelian hcfg
    have hrefl : GGIsReflection p r := ggCoxRefl_isReflection hpres.2 hrC
    have hrefl' : GGIsReflection p r' := ggCoxRefl_isReflection hpres.2 hrC'
    obtain ⟨a₁, b₁, hab₁, hr_eq⟩ :=
      ggPhanNSAPairAux_refl_eq_swap hp hp2 hBs ε hεrefl hrA hrefl
    obtain ⟨c₁, d₁, hcd₁, hr'_eq⟩ :=
      ggPhanNSAPairAux_refl_eq_swap hp hp2 hBs ε hεrefl hrA' hrefl'
    have hrS : ggRankOneIn X Bs r = (ggSuPairBlock K 2 f n a₁ b₁).map ψ := by
      rw [hr_eq]; exact hεlevi a₁ b₁ hab₁
    have hr'S : ggRankOneIn X Bs r' = (ggSuPairBlock K 2 f n c₁ d₁).map ψ := by
      rw [hr'_eq]; exact hεlevi c₁ d₁ hcd₁
    have hnc_swap : Equiv.swap a₁ b₁ * Equiv.swap c₁ d₁ ≠
        Equiv.swap c₁ d₁ * Equiv.swap a₁ b₁ := by
      intro hswap
      apply hnc
      have h3 := congrArg (fun π : Equiv.Perm (Fin n) =>
        ((ε π : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)) hswap
      simp only [map_mul, Subgroup.coe_mul] at h3
      rw [← hr_eq, ← hr'_eq] at h3
      exact h3
    obtain ⟨x, y, z, hxy, hyz, hxz, hxy_eq, hyz_eq⟩ :=
      ggPhanNSAPairAux_share3 hab₁ hcd₁ hnc_swap
    obtain ⟨W, hW⟩ := ggPhanNSAPairAux_stdPair (K := K) (f := f) (n := n) ψ hker
      (by omega) hxy hyz hxz
    have e1 : (ggSuPairBlock K 2 f n x y).map ψ = ggRankOneIn X Bs r := by
      rw [ggPhanNSAPairAux_suPairBlock_congr (K := K) (p := 2) (f := f) (n := n)
        (a := x) (b := y) (c := a₁) (d := b₁) hxy_eq.symm, ← hrS]
    have e2 : (ggSuPairBlock K 2 f n y z).map ψ = ggRankOneIn X Bs r' := by
      rw [ggPhanNSAPairAux_suPairBlock_congr (K := K) (p := 2) (f := f) (n := n)
        (a := y) (b := z) (c := c₁) (d := d₁) hyz_eq.symm, ← hr'S]
    rw [e1, e2] at hW
    exact ⟨W, ggPhanNSAPairAux_stdPair_of_card hKcard hK' hW hS⟩

end CFSG.StandardType

end
