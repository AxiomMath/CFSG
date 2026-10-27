module

public import CFSG.Quasithin.Background.B1MoreIrr
public import CFSG.Quasithin.Background.F918H3
public import CFSG.Quasithin.EmptyFaithful.S153ZJ
public import CFSG.Quasithin.EmptyFaithful.S153ZM

public section

namespace CFSG.Quasithin

open scoped Pointwise

section

variable {Q : Type} [CommGroup Q] [Finite Q]

theorem sxc_exists_isIrr {Λ : Subgroup (MulAut Q)} {T : Subgroup Q} (hT : Λ ≤ stabSub T)
    (hne : T ≠ ⊥) : ∃ L : Subgroup Q, XMod.IsIrr ↥Λ L := by
  obtain ⟨L, ⟨hLinv, hLne⟩, hmin⟩ := (wellFounded_lt (α := Subgroup Q)).has_min
    {L : Subgroup Q | Λ ≤ stabSub L ∧ L ≠ ⊥} ⟨T, hT, hne⟩
  refine ⟨L, (isInv_iff Λ L).2 fun x hx w hw => (hLinv hx w).2 hw,
    bot_lt_iff_ne_bot.2 hLne, fun J hJ _ hJL => ?_⟩
  by_cases hJb : J = ⊥
  · exact Or.inl hJb
  · right
    by_contra hJL'
    exact hmin J ⟨le_stabSub_of_forall_mem ((isInv_iff Λ J).1 hJ), hJb⟩ (lt_of_le_of_ne hJL hJL')

omit [Finite Q] in
theorem sxc_smul_eq_iff {a : MulAut Q} {L : Subgroup Q} : a • L = L ↔ a ∈ stabSub L := by
  constructor
  · intro h u
    have e : a u ∈ a • L ↔ u ∈ L := by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simp
    rwa [h] at e
  · intro h
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simpa using (h (a⁻¹ • x)).symm

theorem sxc_cliff_mod (hQ : ∀ q : Q, q ^ 2 = 1) {Λ A : Subgroup (MulAut Q)}
    (hAel : IsElemAbelian2 A) (hAΛ : ∀ a ∈ A, ∀ l ∈ Λ, a * l * a⁻¹ ∈ Λ) {τ : MulAut Q}
    (hτΛ : ∀ l ∈ Λ, τ * l = l * τ)
    (hirr : ∀ T : Subgroup Q, Λ ≤ stabSub T → A ≤ stabSub T → (∀ s ∈ T, τ s ∈ T) →
      T = ⊥ ∨ T = ⊤)
    (hnot : ∃ T : Subgroup Q, Λ ≤ stabSub T ∧ T ≠ ⊥ ∧ T ≠ ⊤) :
    ∃ L : Subgroup Q, XMod.IsIrr ↥Λ L ∧ L ≠ ⊤ ∧
      ((A ⊓ stabSub L = A ∧ 2 * Z391.nB A L ≤ Z391.nB A (⊤ : Subgroup Q)) ∨
        (A ⊓ stabSub L < A ∧
          (2 ^ (rk A - rk ↥(A ⊓ stabSub L)) - 1) * rk L + Z391.nB (A ⊓ stabSub L) L ≤
            Z391.nB A (⊤ : Subgroup Q))) := by
  classical
  obtain ⟨T₀, hT₀Λ, hT₀b, hT₀t⟩ := hnot
  obtain ⟨L₀, hL₀⟩ := sxc_exists_isIrr hT₀Λ hT₀b
  have hN : XMod.Normalizes ↥Λ ↥A Q := Z391.normalizes_of_conj Λ A hAΛ
  have hp : IsPGroup 2 ↥A :=
    isPGroup_two_of_sq_eq_one fun x : ↥A => Subtype.ext (by simpa using hAel.2 _ x.2)
  obtain ⟨L, -, hL, -, hHC⟩ := XMod.exists_isHomComp_of_isIrr hQ hN hp hL₀
  have hind : sSupIndep (Set.range fun t : ↥A => (t : MulAut Q) • L) :=
    XMod.sSupIndep_smul_of_isHomComp hN hL hHC
  have hΛL : Λ ≤ stabSub L := le_stabSub_of_forall_mem ((isInv_iff Λ L).1 hL.1)
  have hLtop : L ≠ ⊤ := by
    intro h
    rcases hL.2.2 T₀ ((isInv_iff Λ T₀).2 fun x hx w hw => (hT₀Λ hx w).2 hw) bot_le
      (h ▸ le_top) with h' | h'
    · exact hT₀b h'
    · exact hT₀t (h'.trans h)
  refine ⟨L, hL, hLtop, ?_⟩
  by_cases hA₁ : A ⊓ stabSub L = A
  · left
    refine ⟨hA₁, ?_⟩
    have hAL : A ≤ stabSub L := inf_eq_left.1 hA₁
    have hVinv : ∀ g : ↥(stabSub L), ∀ v ∈ L, g • v ∈ L := fun g v hv => (g.2 v).2 hv
    have hVirr : XMod.IsIrr ↥(Λ.subgroupOf (stabSub L)) L := Z391.isIrr_subgroupOf hΛL hL
    have hAp : IsPGroup 2 ↥(A.subgroupOf (stabSub L)) := A4.isPGroup_subgroupOf_of_le hAL hp
    have hAΛ' : ∀ a ∈ A.subgroupOf (stabSub L), ∀ l ∈ Λ.subgroupOf (stabSub L),
        a * l * a⁻¹ ∈ Λ.subgroupOf (stabSub L) := fun a ha l hl => hAΛ _ ha _ hl
    let ψ₀ : ↥L →* Z391.QuotMod L hVinv :=
      (Z391.QuotMod.mk L hVinv).comp ((τ : Q ≃* Q).toMonoidHom.comp L.subtype)
    have hψ₀ : ∀ l ∈ Λ.subgroupOf (stabSub L), ∀ v : ↥L,
        ψ₀ ⟨l • (v : Q), hVinv l v v.2⟩ = l • ψ₀ v := by
      intro l hl v
      show Z391.QuotMod.mk L hVinv (τ (l • (v : Q))) =
        l • Z391.QuotMod.mk L hVinv (τ (v : Q))
      rw [Z391.quotMod_smul_mk]
      exact congrArg (Z391.QuotMod.mk L hVinv)
        (congrArg (fun f : MulAut Q => f (v : Q)) (hτΛ (l : MulAut Q) hl))
    have hne : ψ₀ ≠ 1 := by
      intro h1
      have hτL : ∀ s ∈ L, τ s ∈ L := by
        intro s hs
        have h2 : ψ₀ ⟨s, hs⟩ = 1 := by rw [h1]; rfl
        have h3 : τ s ∈ (Z391.QuotMod.mk L hVinv).ker := h2
        rwa [Z391.QuotMod.ker_mk] at h3
      rcases hirr L hΛL hAL hτL with h | h
      · exact hL.2.1.ne' h
      · exact hLtop h
    have key := Z391.two_nB_le (Γ := ↥(stabSub L)) hQ hAp hAΛ' hVinv hVirr ψ₀ hψ₀ hne
    rwa [Z391.nB_subgroupOf hAL, Z391.nB_subgroupOf hAL] at key
  · right
    have hA₁A : A ⊓ stabSub L ≤ A := inf_le_left
    refine ⟨lt_of_le_of_ne hA₁A hA₁, ?_⟩
    have hrk : rk ↥A = rk ↥(A ⊓ stabSub L) + (rk A - rk ↥(A ⊓ stabSub L)) := by
      have := rk_mono hA₁A
      omega
    obtain ⟨hb1, -⟩ := Z391.nB_block (Γ := MulAut Q) L (rk A - rk ↥(A ⊓ stabSub L)) A
      (A ⊓ stabSub L) hAel.1 hAel.2 hA₁A hrk (fun a ha => sxc_smul_eq_iff.2 ha.2)
      (fun a ha h => ⟨ha, sxc_smul_eq_iff.1 h⟩) hind
    have h2 := hb1.trans (Z391.nB_mono A (le_top : (⨆ t : ↥A, (t : MulAut Q) • L) ≤ ⊤))
    omega

end

end CFSG.Quasithin
