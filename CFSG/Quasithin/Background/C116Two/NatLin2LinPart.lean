module

public import CFSG.Quasithin.Background.C116Two.NatLin2Defs

public section

namespace CFSG.Quasithin.C116Two

open CFSG.QuasithinUnique CFSG.Open

private def nlpLmap {F : Type} [Field F] (b : MulAut (Multiplicative (Fin 2 → F)))
    (hb : IsSemilinear (RingEquiv.refl F) b) : (Fin 2 → F) →ₗ[F] (Fin 2 → F) where
  toFun := addMap b
  map_add' := addMap_add b
  map_smul' c x := hb c x

private def nlpNmap {F : Type} [Field F] (b : MulAut (Multiplicative (Fin 2 → F)))
    (hb : IsSemilinear (RingEquiv.refl F) b) : (Fin 2 → F) →ₗ[F] (Fin 2 → F) :=
  nlpLmap b hb - LinearMap.id

private theorem nlpNmap_apply {F : Type} [Field F] (b : MulAut (Multiplicative (Fin 2 → F)))
    (hb : IsSemilinear (RingEquiv.refl F) b) (x : Fin 2 → F) :
    nlpNmap b hb x = addMap b x - x := rfl

private theorem nlpAddMap_sub {F : Type} [Field F] (b : MulAut (Multiplicative (Fin 2 → F)))
    (hb : IsSemilinear (RingEquiv.refl F) b) (u v : Fin 2 → F) :
    addMap b (u - v) = addMap b u - addMap b v :=
  (nlpLmap b hb).map_sub u v

private theorem nlpInvol {F : Type} [Field F] (b : MulAut (Multiplicative (Fin 2 → F)))
    (hb2 : b ^ 2 = 1) (x : Fin 2 → F) : addMap b (addMap b x) = x := by
  rw [← addMap_mul, ← pow_two, hb2, addMap_one]

private theorem nlpTwo {F : Type} [Field F] [CharP F 2] (v : Fin 2 → F) : v + v = 0 := by
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  rw [← two_smul F v, h2, zero_smul]

private theorem nlpNmap_sq {F : Type} [Field F] [CharP F 2]
    (b : MulAut (Multiplicative (Fin 2 → F))) (hb : IsSemilinear (RingEquiv.refl F) b)
    (hb2 : b ^ 2 = 1) (x : Fin 2 → F) : nlpNmap b hb (nlpNmap b hb x) = 0 := by
  simp only [nlpNmap_apply]
  rw [nlpAddMap_sub b hb, nlpInvol b hb2]
  have h : x - addMap b x - (addMap b x - x) = (x + x) - (addMap b x + addMap b x) := by abel
  rw [h, nlpTwo x, nlpTwo (addMap b x), sub_self]

private theorem nlpNmap_ne_zero {F : Type} [Field F] (b : MulAut (Multiplicative (Fin 2 → F)))
    (hb : IsSemilinear (RingEquiv.refl F) b) (hb1 : b ≠ 1) : nlpNmap b hb ≠ 0 := by
  intro h0
  apply hb1
  refine MulEquiv.ext fun y => ?_
  have hv : addMap b (Multiplicative.toAdd y) = Multiplicative.toAdd y := by
    have h := LinearMap.congr_fun h0 (Multiplicative.toAdd y)
    rw [nlpNmap_apply, LinearMap.zero_apply, sub_eq_zero] at h
    exact h
  exact congrArg Multiplicative.ofAdd hv

private theorem nlpFinrank {F : Type} [Field F] (N : (Fin 2 → F) →ₗ[F] (Fin 2 → F))
    (hN2 : ∀ x, N (N x) = 0) (hN : N ≠ 0) : Module.finrank F (LinearMap.ker N) = 1 := by
  have hle : LinearMap.range N ≤ LinearMap.ker N := by
    rintro _ ⟨x, rfl⟩
    exact LinearMap.mem_ker.mpr (hN2 x)
  have hrk := LinearMap.finrank_range_add_finrank_ker N
  rw [Module.finrank_fin_fun] at hrk
  have h1 : 1 ≤ Module.finrank F (LinearMap.range N) := by
    rw [Submodule.one_le_finrank_iff]
    intro h
    exact hN (LinearMap.range_eq_bot.mp h)
  have h2 : Module.finrank F (LinearMap.range N) ≤ Module.finrank F (LinearMap.ker N) :=
    Submodule.finrank_mono hle
  have h3 : Module.finrank F (LinearMap.ker N) < Module.finrank F (Fin 2 → F) :=
    Submodule.finrank_lt (fun h => hN (LinearMap.ker_eq_top.mp h))
  rw [Module.finrank_fin_fun] at h3
  omega

private theorem nlpKerLe {F : Type} [Field F] (N M : (Fin 2 → F) →ₗ[F] (Fin 2 → F))
    (hN2 : ∀ x, N (N x) = 0) (hM2 : ∀ x, M (M x) = 0) (hNM : ∀ x, N (M x) = M (N x))
    (hN : N ≠ 0) : LinearMap.ker N ≤ LinearMap.ker M := by
  have hfin := nlpFinrank N hN2 hN
  have hpos : 0 < Module.finrank F (LinearMap.ker N) := by omega
  obtain ⟨⟨w, hw⟩, hw0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hw0' : w ≠ 0 := fun h => hw0 (Subtype.ext h)
  have hspan : ∀ y ∈ LinearMap.ker N, ∃ c : F, c • w = y := by
    intro y hy
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨w, hw⟩ : LinearMap.ker N)
      (fun h => hw0' (congrArg Subtype.val h))).mp hfin ⟨y, hy⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  have hNw : N w = 0 := LinearMap.mem_ker.mp hw
  have hMw : M w ∈ LinearMap.ker N := LinearMap.mem_ker.mpr (by rw [hNM, hNw, map_zero])
  obtain ⟨c, hc⟩ := hspan (M w) hMw
  have hMM : M (M w) = (c * c) • w := by
    rw [← hc, map_smul, ← hc, smul_smul]
  have hc0 : c = 0 := by
    have h0 : (c * c) • w = 0 := by rw [← hMM]; exact hM2 w
    rcases smul_eq_zero.mp h0 with h | h
    · exact mul_self_eq_zero.mp h
    · exact absurd h hw0'
  have hMw0 : M w = 0 := by rw [← hc, hc0, zero_smul]
  intro x hx
  obtain ⟨d, rfl⟩ := hspan x hx
  rw [LinearMap.mem_ker, map_smul, hMw0, smul_zero]

private theorem nlpCard {F : Type} [Field F] [Fintype F] (N : (Fin 2 → F) →ₗ[F] (Fin 2 → F))
    (hN2 : ∀ x, N (N x) = 0) (hN : N ≠ 0) : Nat.card (LinearMap.ker N) = Fintype.card F := by
  rw [Module.natCard_eq_pow_finrank (K := F), nlpFinrank N hN2 hN, pow_one, Nat.card_eq_fintype_card]

private theorem nlpNmap_comm {F : Type} [Field F] (b b' : MulAut (Multiplicative (Fin 2 → F)))
    (hb : IsSemilinear (RingEquiv.refl F) b) (hb' : IsSemilinear (RingEquiv.refl F) b')
    (hbb' : b * b' = b' * b) (x : Fin 2 → F) :
    nlpNmap b hb (nlpNmap b' hb' x) = nlpNmap b' hb' (nlpNmap b hb x) := by
  have hc : addMap b (addMap b' x) = addMap b' (addMap b x) := by
    rw [← addMap_mul, ← addMap_mul, hbb']
  simp only [nlpNmap_apply]
  rw [nlpAddMap_sub b hb, nlpAddMap_sub b' hb', hc]
  abel

private theorem nlpNmap_mul {F : Type} [Field F] (b b' : MulAut (Multiplicative (Fin 2 → F)))
    (hb : IsSemilinear (RingEquiv.refl F) b) (hb' : IsSemilinear (RingEquiv.refl F) b')
    (x : Fin 2 → F) :
    addMap (b * b') x - x = nlpNmap b hb (nlpNmap b' hb' x) + nlpNmap b' hb' x + nlpNmap b hb x := by
  rw [addMap_mul]
  simp only [nlpNmap_apply]
  rw [nlpAddMap_sub b hb]
  abel

theorem linear_part_card {F : Type} [Field F] [Fintype F] [CharP F 2]
    (B₁ : Subgroup (MulAut (Multiplicative (Fin 2 → F)))) (hB₁ : IsElemAbelian 2 B₁)
    (hlin : ∀ b ∈ B₁, IsSemilinear (RingEquiv.refl F) b) (hne : B₁ ≠ ⊥) :
    Nat.card B₁ ≤ Fintype.card F ∧ ∃ ℓ : Submodule F (Fin 2 → F), Nat.card ℓ = Fintype.card F ∧
      ∀ x : Fin 2 → F, (∀ b ∈ B₁, addMap b x = x) ↔ x ∈ ℓ := by
  obtain ⟨b₀, hb₀, hb₀1⟩ : ∃ b₀ ∈ B₁, b₀ ≠ 1 := by
    by_contra h
    push Not at h
    apply hne
    rw [eq_bot_iff]
    intro b hb
    exact (Subgroup.mem_bot).mpr (h b hb)
  have hsq : ∀ b ∈ B₁, b ^ 2 = 1 := fun b hb => hB₁.2 b hb
  have hcomm : ∀ b ∈ B₁, ∀ b' ∈ B₁, b * b' = b' * b := by
    intro b hb b' hb'
    exact congrArg Subtype.val (hB₁.1.is_comm.comm ⟨b, hb⟩ ⟨b', hb'⟩)
  have hN₀0 : nlpNmap b₀ (hlin b₀ hb₀) ≠ 0 := nlpNmap_ne_zero b₀ (hlin b₀ hb₀) hb₀1
  have hN₀2 : ∀ x, nlpNmap b₀ (hlin b₀ hb₀) (nlpNmap b₀ (hlin b₀ hb₀) x) = 0 :=
    nlpNmap_sq b₀ (hlin b₀ hb₀) (hsq b₀ hb₀)
  have hℓ : ∀ b (hb : b ∈ B₁), LinearMap.ker (nlpNmap b₀ (hlin b₀ hb₀)) ≤
      LinearMap.ker (nlpNmap b (hlin b hb)) :=
    fun b hb => nlpKerLe _ _ hN₀2 (nlpNmap_sq b (hlin b hb) (hsq b hb))
      (fun x => nlpNmap_comm b₀ b (hlin b₀ hb₀) (hlin b hb) (hcomm b₀ hb₀ b hb) x) hN₀0
  have hℓeq : ∀ b (hb : b ∈ B₁), b ≠ 1 →
      LinearMap.ker (nlpNmap b (hlin b hb)) = LinearMap.ker (nlpNmap b₀ (hlin b₀ hb₀)) := by
    intro b hb hb1
    apply le_antisymm
    · exact nlpKerLe (nlpNmap b (hlin b hb)) (nlpNmap b₀ (hlin b₀ hb₀))
        (nlpNmap_sq b (hlin b hb) (hsq b hb)) hN₀2
        (fun x => nlpNmap_comm b b₀ (hlin b hb) (hlin b₀ hb₀) (hcomm b hb b₀ hb₀) x)
        (nlpNmap_ne_zero b (hlin b hb) hb1)
    · exact hℓ b hb
  have hfix : ∀ x : Fin 2 → F, (∀ b ∈ B₁, addMap b x = x) ↔
      x ∈ LinearMap.ker (nlpNmap b₀ (hlin b₀ hb₀)) := by
    intro x
    constructor
    · intro h
      exact LinearMap.mem_ker.mpr (by rw [nlpNmap_apply, h b₀ hb₀, sub_self])
    · intro hx b hb
      have h1 := LinearMap.mem_ker.mp (hℓ b hb hx)
      rw [nlpNmap_apply] at h1
      exact sub_eq_zero.mp h1
  obtain ⟨e, he⟩ : ∃ e : Fin 2 → F, nlpNmap b₀ (hlin b₀ hb₀) e ≠ 0 := by
    by_contra h
    push Not at h
    exact hN₀0 (LinearMap.ext fun x => h x)
  have hmem : ∀ b (hb : b ∈ B₁),
      nlpNmap b (hlin b hb) e ∈ LinearMap.ker (nlpNmap b₀ (hlin b₀ hb₀)) := by
    intro b hb
    by_cases hb1 : b = 1
    · subst hb1
      have h0 : nlpNmap 1 (hlin 1 hb) e = 0 := by
        rw [nlpNmap_apply, addMap_one, sub_self]
      rw [LinearMap.mem_ker, h0, map_zero]
    · have h1 : nlpNmap b (hlin b hb) e ∈ LinearMap.ker (nlpNmap b (hlin b hb)) :=
        LinearMap.mem_ker.mpr (nlpNmap_sq b (hlin b hb) (hsq b hb) e)
      rw [hℓeq b hb hb1] at h1
      exact h1
  let f : B₁ → LinearMap.ker (nlpNmap b₀ (hlin b₀ hb₀)) :=
    fun b => ⟨nlpNmap b.1 (hlin b.1 b.2) e, hmem b.1 b.2⟩
  have hinj : Function.Injective f := by
    intro b b' hbb
    have hval : nlpNmap b.1 (hlin b.1 b.2) e = nlpNmap b'.1 (hlin b'.1 b'.2) e :=
      congrArg Subtype.val hbb
    have hc : b.1 * b'.1 ∈ B₁ := B₁.mul_mem b.2 b'.2
    have hcz : nlpNmap (b.1 * b'.1) (hlin (b.1 * b'.1) hc) e = 0 := by
      rw [nlpNmap_apply, nlpNmap_mul b.1 b'.1 (hlin b.1 b.2) (hlin b'.1 b'.2) e, ← hval,
        nlpNmap_sq b.1 (hlin b.1 b.2) (hsq b.1 b.2) e, zero_add, nlpTwo]
    have hc1 : b.1 * b'.1 = 1 := by
      by_contra hne1
      have hek : e ∈ LinearMap.ker (nlpNmap (b.1 * b'.1) (hlin (b.1 * b'.1) hc)) :=
        LinearMap.mem_ker.mpr hcz
      rw [hℓeq (b.1 * b'.1) hc hne1] at hek
      exact he (LinearMap.mem_ker.mp hek)
    have hsq' : b'.1 * b'.1 = 1 := by rw [← pow_two]; exact hsq b'.1 b'.2
    have hval2 : b.1 = b'.1 := by
      calc b.1 = b.1 * (b'.1 * b'.1) := by rw [hsq', mul_one]
        _ = (b.1 * b'.1) * b'.1 := by rw [mul_assoc]
        _ = b'.1 := by rw [hc1, one_mul]
    exact Subtype.ext hval2
  refine ⟨?_, LinearMap.ker (nlpNmap b₀ (hlin b₀ hb₀)),
    nlpCard (nlpNmap b₀ (hlin b₀ hb₀)) hN₀2 hN₀0, hfix⟩
  calc Nat.card B₁ ≤ Nat.card (LinearMap.ker (nlpNmap b₀ (hlin b₀ hb₀))) :=
        Nat.card_le_card_of_injective f hinj
    _ = Fintype.card F := nlpCard (nlpNmap b₀ (hlin b₀ hb₀)) hN₀2 hN₀0

end CFSG.Quasithin.C116Two
