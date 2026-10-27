module

public import CFSG.Quasithin.EmptyFaithful.S153ZF
public import CFSG.Quasithin.EmptyFaithful.S153ZE

public section

namespace CFSG.Quasithin.Z391

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem two_nB_le [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ A : Subgroup Γ} (hA : IsPGroup 2 A)
    (hAΛ : ∀ a ∈ A, ∀ l ∈ Λ, a * l * a⁻¹ ∈ Λ) {V : Subgroup Q}
    (hVinv : ∀ g : Γ, ∀ v ∈ V, g • v ∈ V) (hV : XMod.IsIrr ↥Λ V)
    (ψ₀ : ↥(V : Subgroup Q) →* QuotMod V hVinv)
    (hψ₀ : ∀ l ∈ Λ, ∀ v : ↥V, ψ₀ ⟨l • (v : Q), hVinv l v v.2⟩ = l • ψ₀ v) (hne : ψ₀ ≠ 1) :
    2 * nB A V ≤ nB A (⊤ : Subgroup Q) := by
  classical
  let _ : MulDistribMulAction Γ ↥V := subAct V hVinv
  have hq2 : ∀ p : QuotMod V hVinv, p ^ 2 = 1 := by
    intro p
    obtain ⟨x, rfl⟩ := QuotMod.mk_surjective V hVinv p
    rw [← map_pow, hQ x, map_one]
  obtain ⟨φ, hφne, hφΛ, hφA⟩ := exists_fixed_hom hq2 Λ A hA hAΛ ψ₀ (fun l hl p => hψ₀ l hl p) hne
  have hker : φ.ker = ⊥ := by
    set K : Subgroup Q := (φ.ker).map V.subtype with hK
    have hKΛ : XMod.IsInv ↥Λ K := by
      rintro ⟨l, hl⟩ k hk
      obtain ⟨k', hk', rfl⟩ := hk
      refine ⟨l • k', ?_, rfl⟩
      have hk'' : φ k' = 1 := hk'
      show φ (l • k') = 1
      rw [hφΛ l hl k', hk'', smul_one]
    rcases hV.2.2 K hKΛ bot_le (Subgroup.map_subtype_le _) with h | h
    · refine (Subgroup.eq_bot_iff_forall _).2 fun k hk => ?_
      have hk' : (k : Q) ∈ K := ⟨k, hk, rfl⟩
      rw [h, Subgroup.mem_bot] at hk'
      exact Subtype.ext hk'
    · exfalso
      apply hφne
      refine MonoidHom.ext fun v => ?_
      have hv : (v : Q) ∈ K := by rw [h]; exact v.2
      obtain ⟨v', hv', hvv'⟩ := hv
      have : v' = v := Subtype.ext hvv'
      rw [← this]
      exact hv'
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hker
  set S : Subgroup (QuotMod V hVinv) := φ.range with hS
  have hnS : nB A S = nB A V := by
    unfold nB
    set F := XMod.fixed ↥A (⊤ : Subgroup Q) with hF
    set F' := XMod.fixed ↥A (⊤ : Subgroup (QuotMod V hVinv)) with hF'
    have hrk1 : rk ↥S = rk ↥V := by
      unfold rk
      exact congrArg (padicValNat 2) (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm)
    have key : ∀ (a : Γ) (v : ↥V), a • v = v ↔ a • (v : Q) = (v : Q) :=
      fun a v => ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    have hmap : S ⊓ F' = ((V ⊓ F).subgroupOf V).map φ := by
      ext y
      constructor
      · rintro ⟨⟨v, rfl⟩, hy⟩
        refine ⟨v, ?_, rfl⟩
        refine ⟨v.2, XMod.mem_fixed.2 ⟨trivial, fun a => ?_⟩⟩
        have h1 := (XMod.mem_fixed.1 hy).2 a
        change (a : Γ) • φ v = φ v at h1
        rw [← hφA (a : Γ) a.2 v] at h1
        exact (key a v).1 (hinj h1)
      · rintro ⟨v, hv, rfl⟩
        refine ⟨⟨v, rfl⟩, XMod.mem_fixed.2 ⟨trivial, fun a => ?_⟩⟩
        have h1 := (XMod.mem_fixed.1 hv.2).2 a
        change (a : Γ) • (v : Q) = v at h1
        change (a : Γ) • φ v = φ v
        rw [← hφA (a : Γ) a.2 v, (key a v).2 h1]
    have hrk2 : rk ↥(S ⊓ F') = rk ↥(V ⊓ F) := by
      rw [hmap]
      unfold rk
      rw [Nat.card_congr (Subgroup.equivMapOfInjective _ φ hinj).toEquiv.symm]
      exact congrArg _ (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv)
    rw [hrk1, hrk2]
  have h1 := nB_chain A V hVinv
  have h2 := nB_mono A (le_top : S ≤ (⊤ : Subgroup (QuotMod V hVinv)))
  omega

end CFSG.Quasithin.Z391
