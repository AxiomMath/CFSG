module

public import CFSG.LocalAnalysis.StandardType.GGQTwoChartDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoChartTwoThreeCent
public import CFSG.LocalAnalysis.StandardType.GGQTwoChartTwoThreeBlk
import CFSG.LocalAnalysis.StandardType.GGQTwoChartTwoThreeSym

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open scoped Pointwise Matrix
variable {G : Type} [Group G] [Finite G]
variable {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {m n : ℕ}
variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]

private theorem qTwoChartTwoThree_diag_coe (c : Fin m → F0ˣ) :
    ((qTwoChartTwoThree_diag c : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      Matrix.diagonal fun i => ((c i : F0ˣ) : F0) := rfl

private theorem qTwoChartTwoThree_diag_inv_coe (c : Fin m → F0ˣ) :
    (((qTwoChartTwoThree_diag c)⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      Matrix.diagonal fun i => (((c i)⁻¹ : F0ˣ) : F0) := rfl

private theorem qTwoChartTwoThree_diag_mulVec_single (c : Fin m → F0ˣ) (k : Fin m) :
    ((qTwoChartTwoThree_diag c : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ
      Pi.single k 1 = Pi.single k ((c k : F0ˣ) : F0) := by
  rw [qTwoChartTwoThree_diag_coe, Matrix.diagonal_mulVec_single, mul_one]

private theorem qTwoChartTwoThree_diag_inv_mulVec_single (c : Fin m → F0ˣ) (k : Fin m) :
    (((qTwoChartTwoThree_diag c)⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ
      Pi.single k 1 = Pi.single k ((((c k)⁻¹ : F0ˣ)) : F0) := by
  rw [qTwoChartTwoThree_diag_inv_coe, Matrix.diagonal_mulVec_single, mul_one]

private theorem qTwoChartTwoThree_extendDomain_swap (ε0 : Fin m ↪ Fin (n + 1))
    (i j : Fin m) :
    (Equiv.swap i j).extendDomain (Equiv.ofInjective ε0 ε0.injective) =
      Equiv.swap (ε0 i) (ε0 j) := by
  classical
  apply Equiv.ext
  intro y
  by_cases hy : y ∈ Set.range ε0
  · obtain ⟨k, hk⟩ := hy
    rw [← hk]
    change (Equiv.swap i j).extendDomain (Equiv.ofInjective ε0 ε0.injective)
        (Equiv.ofInjective ε0 ε0.injective k) = Equiv.swap (ε0 i) (ε0 j) (ε0 k)
    rw [Equiv.Perm.extendDomain_apply_image]
    change ε0 (Equiv.swap i j k) = Equiv.swap (ε0 i) (ε0 j) (ε0 k)
    rcases eq_or_ne k i with h | h
    · subst h
      rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
    rcases eq_or_ne k j with h' | h'
    · subst h'
      rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
    · rw [Equiv.swap_apply_of_ne_of_ne h h', Equiv.swap_apply_of_ne_of_ne]
      · intro hx
        exact h (ε0.injective hx)
      · intro hx
        exact h' (ε0.injective hx)
  · rw [Equiv.Perm.extendDomain_apply_not_subtype _ _ hy]
    exact (Equiv.swap_apply_of_ne_of_ne (fun h => hy ⟨i, h.symm⟩)
      (fun h => hy ⟨j, h.symm⟩)).symm

private theorem qTwoChartTwoThree_swap_fix
    (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    {ψ : Su F0 2 1 m →* G} {ε0 : Fin m ↪ Fin (n + 1)} (hε0 : QTwoFrameMatch S ψ ε0)
    {T : Finset (Fin m)} {b : ↥Bs} {c : Fin m → F0ˣ}
    (hb : qTwoChartTwoThree_induces ψ (b : G) c) (hc : ∀ i ∈ T, ∀ j ∈ T, c i = c j)
    {i j : Fin m} (hi : i ∈ T) (hj : j ∈ T) :
    ((S.ρA (Equiv.swap (ε0 i) (ε0 j)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) b = b := by
  by_cases hij : i = j
  · subst hij
    rw [Equiv.swap_self]
    change ((S.ρA (1 : Equiv.Perm (Fin (n + 1))) : ↥(ggAutomizerJoin L Bs 𝒦)) :
      MulAut ↥Bs) b = b
    rw [map_one]
    rfl
  obtain ⟨u, hu1, hu2⟩ := hε0 (Equiv.swap i j)
  have hσt : (Equiv.swap i j).extendDomain (Equiv.ofInjective ε0 ε0.injective) =
      Equiv.swap (ε0 i) (ε0 j) := qTwoChartTwoThree_extendDomain_swap ε0 i j
  rw [hσt] at hu2
  let β : MulAut ↥Bs :=
    ((S.ρA (Equiv.swap (ε0 i) (ε0 j)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)
  let b₁ : G := ψ u * (b : G) * (ψ u)⁻¹
  have hformula : ∀ b' : ↥Bs, ((β b' : ↥Bs) : G) = ψ u * (b' : G) * (ψ u)⁻¹ := by
    intro b'
    exact hu2.2.2 b'
  have hceq : (fun k => c ((Equiv.swap i j).symm k)) = c := by
    funext k
    have hsym : (Equiv.swap i j).symm = (Equiv.swap i j) := Equiv.swap_inv i j
    rw [hsym]
    rcases eq_or_ne k i with hki | hki
    · rw [hki, Equiv.swap_apply_left]
      exact (hc i hi j hj).symm
    rcases eq_or_ne k j with hkj | hkj
    · rw [hkj, Equiv.swap_apply_right]
      exact hc i hi j hj
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hb1 : qTwoChartTwoThree_induces ψ b₁ c := by
    have h := qTwoChartTwoThree_induces_conj hb hu1
    rwa [hceq] at h
  have hconj : ψ u = ((b : G)⁻¹ * b₁) * ψ u * ((b : G)⁻¹ * b₁)⁻¹ := by
    calc ψ u = (b : G)⁻¹ * ((b : G) * ψ u * (b : G)⁻¹) * (b : G) := by group
    _ = (b : G)⁻¹ * (b₁ * ψ u * b₁⁻¹) * (b : G) := by
          rw [qTwoChartTwoThree_induces_unique hb hb1 u]
    _ = ((b : G)⁻¹ * b₁) * ψ u * ((b : G)⁻¹ * b₁)⁻¹ := by group
  have hw : ((b : G)⁻¹ * b₁) * ψ u = ψ u * ((b : G)⁻¹ * b₁) := by
    have h := congrArg (fun x : G => x * ((b : G)⁻¹ * b₁)) hconj
    rw [show (((b : G)⁻¹ * b₁) * ψ u * ((b : G)⁻¹ * b₁)⁻¹) * ((b : G)⁻¹ * b₁)
        = ((b : G)⁻¹ * b₁) * ψ u by group] at h
    exact h.symm
  let w : ↥Bs := b⁻¹ * β b
  have hwval : (w : G) = (b : G)⁻¹ * b₁ := by
    show ((b⁻¹ * β b : ↥Bs) : G) = (b : G)⁻¹ * b₁
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hformula b]
  have hww : (w : G) * ψ u = ψ u * (w : G) := by
    rw [hwval]
    exact hw
  have hββ : β * β = 1 := by
    change ((S.ρA (Equiv.swap (ε0 i) (ε0 j)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
        ((S.ρA (Equiv.swap (ε0 i) (ε0 j)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) = 1
    rw [← Subgroup.coe_mul, ← map_mul, Equiv.swap_mul_self, map_one, Subgroup.coe_one]
  have hββb : β (β b) = b := by
    calc β (β b) = (β * β) b := rfl
    _ = (1 : MulAut ↥Bs) b := by rw [hββ]
    _ = b := rfl
  have hβw : β w = w := by
    apply Subtype.ext
    have hbβw : ((β w : ↥Bs) : G) = (w : G) := by
      rw [hformula w]
      calc ψ u * (w : G) * (ψ u)⁻¹ = ((w : G) * ψ u) * (ψ u)⁻¹ := by rw [← hww]
      _ = (w : G) := by group
    exact hbβw
  have hβwinv : β w = w⁻¹ := by
    calc β w = β (b⁻¹ * β b) := rfl
    _ = (β b)⁻¹ * β (β b) := by rw [map_mul, map_inv]
    _ = (β b)⁻¹ * b := by rw [hββb]
    _ = w⁻¹ := by
          change ((β b)⁻¹ * b : ↥Bs) = (b⁻¹ * β b : ↥Bs)⁻¹
          rw [mul_inv_rev, inv_inv]
  have hwinv : w = w⁻¹ := hβw.symm.trans hβwinv
  have hww2 : w * w = 1 := by
    have h := congrArg (fun x => w * x) hwinv
    rwa [mul_inv_cancel] at h
  have hw2 : w ^ 2 = 1 := by rw [sq]; exact hww2
  have hw3 : w ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, S.hLocal.elemAb.2 (w : G) w.2]
  have hw1 : w = 1 := by
    have h3 : w ^ 3 = w := by
      rw [show w ^ 3 = w ^ 2 * w by rw [pow_succ], hw2, one_mul]
    rw [← h3, hw3]
  have hβb_eq : β b = b := by
    have h1 : b⁻¹ * β b = 1 := hw1
    exact (inv_mul_eq_one.mp h1).symm
  exact hβb_eq

private theorem qTwoChartTwoThree_apply_eq_of_supported
    (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    {ψ : Su F0 2 1 m →* G} {ε0 : Fin m ↪ Fin (n + 1)} (hε0 : QTwoFrameMatch S ψ ε0)
    {T : Finset (Fin m)} {b : ↥Bs} {c : Fin m → F0ˣ}
    (hb : qTwoChartTwoThree_induces ψ (b : G) c) (hc : ∀ i ∈ T, ∀ j ∈ T, c i = c j) :
    ∀ σ : Equiv.Perm (Fin (n + 1)), (∀ y, y ∉ T.map ε0 → σ y = y) →
      ((S.ρA σ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) b = b := by
  let Stab : Subgroup (Equiv.Perm (Fin (n + 1))) :=
    { carrier := {σ | ((S.ρA σ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) b = b}
      one_mem' := by
        show ((S.ρA 1 : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) b = b
        simp
      mul_mem' := by
        intro σ τ hσ hτ
        show ((S.ρA (σ * τ) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) b = b
        rw [map_mul]
        show (((S.ρA σ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
          ((S.ρA τ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) b = b
        rw [MulAut.coe_mul, Function.comp_apply, hτ, hσ]
      inv_mem' := by
        intro σ hσ
        show ((S.ρA σ⁻¹ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) b = b
        rw [map_inv]
        simp only [Subgroup.coe_inv, MulAut.coe_inv]
        exact (MulEquiv.symm_apply_eq _).mpr hσ.symm }
  have hS : ∀ τ : Equiv.Perm (Fin (n + 1)), τ.IsSwap → (∀ y, y ∉ T.map ε0 → τ y = y) →
      τ ∈ Stab := by
    rintro τ ⟨a, a', hne, rfl⟩ hsup
    have ha : a ∈ T.map ε0 := by
      by_contra h
      have hfix := hsup a h
      rw [Equiv.swap_apply_left] at hfix
      exact hne hfix.symm
    have ha' : a' ∈ T.map ε0 := by
      by_contra h
      have hfix := hsup a' h
      rw [Equiv.swap_apply_right] at hfix
      exact hne hfix
    obtain ⟨i, hiT, hia⟩ := Finset.mem_map.mp ha
    obtain ⟨j, hjT, hja⟩ := Finset.mem_map.mp ha'
    subst hia
    subst hja
    exact qTwoChartTwoThree_swap_fix S hε0 hb hc hiT hjT
  have hclosure : Subgroup.closure {τ : Equiv.Perm (Fin (n + 1)) |
      τ.IsSwap ∧ ∀ y, y ∉ T.map ε0 → τ y = y} ≤ Stab :=
    (Subgroup.closure_le Stab).mpr fun τ hτ => hS τ hτ.1 hτ.2
  intro σ hσ
  have hσS : σ ∈ Subgroup.closure {τ : Equiv.Perm (Fin (n + 1)) |
      τ.IsSwap ∧ ∀ y, y ∉ T.map ε0 → τ y = y} :=
    qTwoChartTwoThree_mem_closure_swaps_of_supported hσ
  exact hclosure hσS

theorem qTwoChartTwoThree_mem_fixI (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    {ψ : Su F0 2 1 m →* G} {ε0 : Fin m ↪ Fin (n + 1)} (hε0 : QTwoFrameMatch S ψ ε0)
    {T : Finset (Fin m)} {b : ↥Bs} {c : Fin m → F0ˣ}
    (hb : qTwoChartTwoThree_induces ψ (b : G) c) (hc : ∀ i ∈ T, ∀ j ∈ T, c i = c j) :
    (b : G) ∈ qTwoFixI S.ρA (T.map ε0) := by
  rw [qTwoChartTwoThree_mem_fixI_iff]
  intro s
  obtain ⟨σ, hσsup, hσeq⟩ :=
    (qTwoChartTwoThree_mem_symI (ρA := S.ρA) (I := T.map ε0)).mp s.2
  rw [← hσeq]
  exact qTwoChartTwoThree_apply_eq_of_supported S hε0 hb hc σ hσsup

theorem qTwoChartTwoThree_const_of_mem_fixI (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    {ψ : Su F0 2 1 m →* G} (hψ : QTwoOrdModel Bs L ψ) {ε0 : Fin m ↪ Fin (n + 1)}
    (hε0 : QTwoFrameMatch S ψ ε0) {T : Finset (Fin m)} {b : ↥Bs} {c : Fin m → F0ˣ}
    (hb : qTwoChartTwoThree_induces ψ (b : G) c) (hbF : (b : G) ∈ qTwoFixI S.ρA (T.map ε0)) :
    ∀ i ∈ T, ∀ j ∈ T, c i = c j := by
  intro i hi j hj
  by_cases hij : i = j
  · subst hij
    rfl
  classical
  have hbF' : ∀ s : qTwoSymI S.ρA (T.map ε0), (s : MulAut ↥Bs) b = b :=
    (qTwoChartTwoThree_mem_fixI_iff S.ρA (T.map ε0) b).mp hbF
  have hmem : ((S.ρA (Equiv.swap (ε0 i) (ε0 j)) : ↥(ggAutomizerJoin L Bs 𝒦)) :
      MulAut ↥Bs) ∈ qTwoSymI S.ρA (T.map ε0) := by
    rw [qTwoChartTwoThree_mem_symI]
    refine ⟨Equiv.swap (ε0 i) (ε0 j), ?_, rfl⟩
    intro y hy
    exact Equiv.swap_apply_of_ne_of_ne
      (fun h => hy (h ▸ Finset.mem_map.mpr ⟨i, hi, rfl⟩))
      (fun h => hy (h ▸ Finset.mem_map.mpr ⟨j, hj, rfl⟩))
  have hβb : ((S.ρA (Equiv.swap (ε0 i) (ε0 j)) : ↥(ggAutomizerJoin L Bs 𝒦)) :
      MulAut ↥Bs) b = b := hbF' ⟨_, hmem⟩
  obtain ⟨u, hu1, hu2⟩ := hε0 (Equiv.swap i j)
  have hσt : (Equiv.swap i j).extendDomain (Equiv.ofInjective ε0 ε0.injective) =
      Equiv.swap (ε0 i) (ε0 j) := qTwoChartTwoThree_extendDomain_swap ε0 i j
  rw [hσt] at hu2
  let β : MulAut ↥Bs :=
    ((S.ρA (Equiv.swap (ε0 i) (ε0 j)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)
  have hformula : ∀ b' : ↥Bs, ((β b' : ↥Bs) : G) = ψ u * (b' : G) * (ψ u)⁻¹ := by
    intro b'
    exact hu2.2.2 b'
  have hbβ : ((β b : ↥Bs) : G) = (b : G) := congrArg (fun x : ↥Bs => (x : G)) hβb
  have hbψ : ψ u * (b : G) * (ψ u)⁻¹ = (b : G) := by rw [← hformula b, hbβ]
  have hcomm : (b : G) * ψ u = ψ u * (b : G) := by
    have h := congrArg (fun x : G => x * ψ u) hbψ
    rw [show (ψ u * (b : G) * (ψ u)⁻¹) * ψ u = ψ u * (b : G) by group] at h
    exact h.symm
  obtain ⟨u', hu', hψu'⟩ := hb u
  have hψu_eq : ψ u' = ψ u := by
    rw [hψu', hcomm]
    group
  have hker : u' * u⁻¹ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψu_eq, mul_inv_cancel]
  have hz : u' * u⁻¹ ∈ Subgroup.center (Su F0 2 1 m) := hψ.2.1 hker
  have hperm : ∀ σ : Equiv.Perm (Fin m), ∃ u : Su F0 2 1 m, ∀ i : Fin m,
      ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single i 1 =
        Pi.single (σ i) 1 :=
    fun σ => (hε0 σ).imp fun u hu => hu.1
  have hcard : ({i, j} : Finset (Fin m)).card < (Finset.univ : Finset (Fin m)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    have hm : 5 ≤ m := S.hm
    have h2 : ({i, j} : Finset (Fin m)).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hki : k ≠ i := fun h => hk (by rw [h]; simp)
  have hkj : k ≠ j := fun h => hk (by rw [h]; simp)
  have hσk : Equiv.swap i j k = k := Equiv.swap_apply_of_ne_of_ne hki hkj
  have hu1k : ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single k 1 =
      Pi.single k 1 := by
    rw [hu1 k, hσk]
  have huinvk : (((u : GL (Fin m) F0)⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ
      Pi.single k 1 = Pi.single k 1 := by
    have hmul : (((u : GL (Fin m) F0)⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
        ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (((u : GL (Fin m) F0)⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ
          Pi.single k 1
        = (((u : GL (Fin m) F0)⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ
            (((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single k 1) := by
          rw [hu1k]
    _ = ((((u : GL (Fin m) F0)⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
            ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)) *ᵥ Pi.single k 1 := by
          rw [Matrix.mulVec_mulVec]
    _ = (1 : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single k 1 := by rw [hmul]
    _ = Pi.single k 1 := by rw [Matrix.one_mulVec]
  have hab : ((((c k)⁻¹ : F0ˣ)) : F0) * ((c k : F0ˣ) : F0) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hDuD : (((qTwoChartTwoThree_diag c * (u : GL (Fin m) F0) *
      (qTwoChartTwoThree_diag c)⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)) *ᵥ
      Pi.single k 1 = Pi.single k 1 := by
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [qTwoChartTwoThree_diag_inv_mulVec_single]
    rw [show Pi.single k ((((c k)⁻¹ : F0ˣ)) : F0) =
        ((((c k)⁻¹ : F0ˣ)) : F0) • Pi.single k (1 : F0) by
      rw [← Pi.single_smul', smul_eq_mul, mul_one]]
    rw [Matrix.mulVec_smul, hu1k, Matrix.mulVec_smul, qTwoChartTwoThree_diag_mulVec_single]
    rw [← Pi.single_smul', smul_eq_mul, hab]
  have hzmat : (((u' * u⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      (((qTwoChartTwoThree_diag c * (u : GL (Fin m) F0) *
        (qTwoChartTwoThree_diag c)⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)) *
        (((u : GL (Fin m) F0)⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) := by
    rw [show (((u' * u⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) :
        Matrix (Fin m) (Fin m) F0) =
        ((u' : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
          (((u : GL (Fin m) F0)⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) by rfl]
    rw [hu']
  have hz_k : (((u' * u⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ
      Pi.single k 1 = Pi.single k 1 := by
    rw [hzmat, ← Matrix.mulVec_mulVec, huinvk, hDuD]
  have hz1 : u' * u⁻¹ = 1 := qTwoChartTwoThree_central_eq_one hperm hz hz_k
  have huu : u' = u := mul_inv_eq_one.mp hz1
  have huD : (u : GL (Fin m) F0) = qTwoChartTwoThree_diag c * (u : GL (Fin m) F0) *
      (qTwoChartTwoThree_diag c)⁻¹ := by
    rw [huu] at hu'
    exact hu'
  have hmat : ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      ((qTwoChartTwoThree_diag c * (u : GL (Fin m) F0) *
        (qTwoChartTwoThree_diag c)⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) :=
    congrArg (fun g : GL (Fin m) F0 => ((g : GL (Fin m) F0) :
      Matrix (Fin m) (Fin m) F0)) huD
  have hL : ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single i 1 =
      Pi.single j 1 := by
    rw [hu1 i, Equiv.swap_apply_left]
  have hR : (((qTwoChartTwoThree_diag c * (u : GL (Fin m) F0) *
      (qTwoChartTwoThree_diag c)⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)) *ᵥ
      Pi.single i 1 = Pi.single j (((((c i)⁻¹ : F0ˣ)) : F0) * ((c j : F0ˣ) : F0)) := by
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [qTwoChartTwoThree_diag_inv_mulVec_single]
    rw [show Pi.single i ((((c i)⁻¹ : F0ˣ)) : F0) =
        ((((c i)⁻¹ : F0ˣ)) : F0) • Pi.single i (1 : F0) by
      rw [← Pi.single_smul', smul_eq_mul, mul_one]]
    rw [Matrix.mulVec_smul, hu1 i, Equiv.swap_apply_left]
    rw [Matrix.mulVec_smul, qTwoChartTwoThree_diag_mulVec_single, ← Pi.single_smul',
      smul_eq_mul]
  have hEq : (Pi.single j (((((c i)⁻¹ : F0ˣ)) : F0) * ((c j : F0ˣ) : F0)) :
      Fin m → F0) = (Pi.single j (1 : F0) : Fin m → F0) := by
    rw [← hR, ← hL, hmat]
  have hcoord : (((((c i)⁻¹ : F0ˣ)) : F0) * ((c j : F0ˣ) : F0)) = 1 := by
    have := congrFun hEq j
    simpa using this
  have hprod : (c i)⁻¹ * c j = 1 := by
    apply Units.ext
    simpa [Units.val_mul, Units.val_one] using hcoord
  exact inv_mul_eq_one.mp hprod

theorem qTwoChartTwoThree_block_le_centralizer (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    {ψ : Su F0 2 1 m →* G} (hψ : QTwoOrdModel Bs L ψ) {ε0 : Fin m ↪ Fin (n + 1)}
    (hε0 : QTwoFrameMatch S ψ ε0) (T : Finset (Fin m)) :
    (coordBlockSU F0 2 1 T).map ψ ≤
      Subgroup.centralizer ((qTwoFixI S.ρA (T.map ε0) : Subgroup G) : Set G) := by
  intro y hy
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  obtain ⟨b, hbF, hbf⟩ := Subgroup.mem_map.mp hf
  rw [← hbf]
  have hbF' : (b : G) ∈ qTwoFixI S.ρA (T.map ε0) := Subgroup.mem_map.mpr ⟨b, hbF, rfl⟩
  obtain ⟨c, hbc⟩ := qTwoChartTwoThree_induces_of_ordModel hψ b
  have hcconst : ∀ i ∈ T, ∀ j ∈ T, c i = c j :=
    qTwoChartTwoThree_const_of_mem_fixI S hψ hε0 hbc hbF'
  have hcomm_diag : qTwoChartTwoThree_diag c * (u : GL (Fin m) F0) *
      (qTwoChartTwoThree_diag c)⁻¹ = (u : GL (Fin m) F0) :=
    qTwoChartTwoThree_block_comm_diag hcconst hu
  obtain ⟨u', hu', hψu'⟩ := hbc u
  have hu'u : (u' : GL (Fin m) F0) = (u : GL (Fin m) F0) := by rw [hu', hcomm_diag]
  have huueq : u' = u := Subtype.ext hu'u
  have hconj : (b : G) * ψ u * (b : G)⁻¹ = ψ u := by
    rw [← hψu', huueq]
  have hgoal : (b : G) * ψ u = ψ u * (b : G) := by
    calc (b : G) * ψ u = (b : G) * ψ u * (b : G)⁻¹ * (b : G) := by group
    _ = ψ u * (b : G) := by rw [hconj]
  exact hgoal

end CFSG.StandardType.QTwo

end
