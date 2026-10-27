module

public import CFSG.LocalAnalysis.WeakClosure81.W16PLemmaQSzBB
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.Bridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open Matrix CFSG.CGT.PushingUpLit.SolKNA CFSG.RankThree.GF2n.SzExplicit
  CFSG.RepresentationTheory.SzMartineau
open CFSG.RankThree.S4Free.SzNatural
open scoped Pointwise

private theorem torusSz_injective (a : ℕ) : Function.Injective (torusSz a) := by
  intro x y hxy
  have hm : torusMat a x = torusMat a y := by
    have h := congrArg (fun g : ↥(Sz a) =>
      ((g : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a))) hxy
    simpa only [torusSz, coe_torusGL] using h
  have h1 : (x : F a) ^ (1 + 2 ^ a) = (y : F a) ^ (1 + 2 ^ a) := by
    simpa [torusMat] using congrArg (fun M : Matrix (Fin 4) (Fin 4) (F a) => M 0 0) hm
  have h2 : (x : F a) ^ (2 ^ a) = (y : F a) ^ (2 ^ a) := by
    simpa [torusMat] using congrArg (fun M : Matrix (Fin 4) (Fin 4) (F a) => M 1 1) hm
  have h1u : x ^ (1 + 2 ^ a) = y ^ (1 + 2 ^ a) := Units.ext (by simpa using h1)
  have h2u : x ^ (2 ^ a) = y ^ (2 ^ a) := Units.ext (by simpa using h2)
  have h3 : x * y ^ (2 ^ a) = y * y ^ (2 ^ a) := by
    calc x * y ^ (2 ^ a) = x * x ^ (2 ^ a) := by rw [h2u]
      _ = x ^ (1 + 2 ^ a) := by group
      _ = y ^ (1 + 2 ^ a) := h1u
      _ = y * y ^ (2 ^ a) := by group
  calc x = x * y ^ (2 ^ a) * (y ^ (2 ^ a))⁻¹ := by group
    _ = y * y ^ (2 ^ a) * (y ^ (2 ^ a))⁻¹ := by rw [h3]
    _ = y := by group

private theorem card_torusSzHom_range (a : ℕ) :
    Nat.card (torusSzHom a).range = 2 ^ (2 * a + 1) - 1 := by
  have h := (Nat.card_congr (MonoidHom.ofInjective (f := torusSzHom a)
    (torusSz_injective a)).symm.toEquiv).trans
    (by rw [Nat.card_units, card_F a])
  exact h

private theorem rootSub_inf_torusSzHom_range (a : ℕ) :
    rootSub a ⊓ (torusSzHom a).range = ⊥ := by
  refine Subgroup.inf_eq_bot_of_coprime ?_
  rw [card_rootSub, card_torusSzHom_range]
  have hodd : Odd (2 ^ (2 * a + 1) - 1) := by
    refine ⟨2 ^ (2 * a) - 1, ?_⟩
    rw [pow_succ']
    have h1 : 0 < 2 ^ (2 * a) := by positivity
    omega
  have hcop : Nat.Coprime 2 (2 ^ (2 * a + 1) - 1) := Nat.coprime_two_left.mpr hodd
  exact (hcop.pow_left (2 * a + 1)).pow_left 2

private theorem card_sup_rootSub_torusSzHom_range (a : ℕ) :
    Nat.card ↥(rootSub a ⊔ (torusSzHom a).range) =
      (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) := by
  have hprod : ((rootSub a ⊔ (torusSzHom a).range : Subgroup ↥(Sz a)) : Set ↥(Sz a)) =
      (rootSub a : Set ↥(Sz a)) * ((torusSzHom a).range : Set ↥(Sz a)) :=
    Subgroup.coe_mul_of_right_le_normalizer_left (rootSub a) (torusSzHom a).range
      (torusSzHom_range_le_normalizer a)
  let f : ↥(rootSub a) × ↥((torusSzHom a).range) →
      ↥(rootSub a ⊔ (torusSzHom a).range) :=
    fun p => ⟨(p.1 : ↥(Sz a)) * (p.2 : ↥(Sz a)), by
      have hmem : ((p.1 : ↥(Sz a)) * (p.2 : ↥(Sz a))) ∈
          (rootSub a : Set ↥(Sz a)) * ((torusSzHom a).range : Set ↥(Sz a)) :=
        Set.mul_mem_mul p.1.2 p.2.2
      rw [← hprod] at hmem
      exact hmem⟩
  have hf : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · rintro ⟨s, t⟩ ⟨s', t'⟩ hpq
      have h : (s : ↥(Sz a)) * (t : ↥(Sz a)) = (s' : ↥(Sz a)) * (t' : ↥(Sz a)) :=
        Subtype.ext_iff.mp hpq
      have h' : (s' : ↥(Sz a))⁻¹ * (s : ↥(Sz a)) =
          (t' : ↥(Sz a)) * (t : ↥(Sz a))⁻¹ := by
        calc (s' : ↥(Sz a))⁻¹ * (s : ↥(Sz a))
            = (s' : ↥(Sz a))⁻¹ * ((s : ↥(Sz a)) * (t : ↥(Sz a))) *
                (t : ↥(Sz a))⁻¹ := by group
          _ = (s' : ↥(Sz a))⁻¹ * ((s' : ↥(Sz a)) * (t' : ↥(Sz a))) *
                (t : ↥(Sz a))⁻¹ := by rw [h]
          _ = (t' : ↥(Sz a)) * (t : ↥(Sz a))⁻¹ := by group
      have hmem : (s' : ↥(Sz a))⁻¹ * (s : ↥(Sz a)) ∈
          rootSub a ⊓ (torusSzHom a).range :=
        ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ s'.2) s.2,
          h'.symm ▸ Subgroup.mul_mem _ t'.2 (Subgroup.inv_mem _ t.2)⟩
      rw [rootSub_inf_torusSzHom_range a] at hmem
      have hs : (s' : ↥(Sz a))⁻¹ * (s : ↥(Sz a)) = 1 := Subgroup.mem_bot.mp hmem
      have ht : (t' : ↥(Sz a)) * (t : ↥(Sz a))⁻¹ = 1 := by rw [← h']; exact hs
      exact Prod.ext (Subtype.ext (inv_mul_eq_one.mp hs).symm)
        (Subtype.ext (mul_inv_eq_one.mp ht).symm)
    · intro x
      have hx : (x : ↥(Sz a)) ∈
          (rootSub a : Set ↥(Sz a)) * ((torusSzHom a).range : Set ↥(Sz a)) := by
        rw [← hprod]
        exact x.2
      obtain ⟨s, hs, t, ht, hst⟩ := Set.mem_mul.mp hx
      exact ⟨(⟨s, hs⟩, ⟨t, ht⟩), Subtype.ext hst⟩
  have hcard := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_prod, card_rootSub, card_torusSzHom_range] at hcard
  exact hcard.symm

theorem normalizer_rootSub_eq_sup {a : ℕ} (ha : 1 ≤ a) :
    Subgroup.normalizer (rootSub a : Set ↥(Sz a)) = rootSub a ⊔ (torusSzHom a).range := by
  have hsup_le : rootSub a ⊔ (torusSzHom a).range ≤
      Subgroup.normalizer (rootSub a : Set ↥(Sz a)) :=
    sup_le Subgroup.le_normalizer (torusSzHom_range_le_normalizer a)
  have hcard : Nat.card (Subgroup.normalizer (rootSub a : Set ↥(Sz a))) =
      Nat.card ↥(rootSub a ⊔ (torusSzHom a).range) := by
    obtain ⟨e⟩ :=
      CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup a
    have h := CFSG.RankThree.S4Free.Suzuki.card_normalizer_sylow (a := a) (K := F a)
      (X := ↥(Sz a)) (card_F a) e (rootSylow a)
    rw [coe_rootSylow] at h
    rw [h, card_sup_rootSub_torusSzHom_range]
  exact (Subgroup.eq_of_le_of_card_ge hsup_le hcard.le).symm

theorem exists_eq_rootSz_mul_torusSz_of_mem_normalizer {a : ℕ}
    (ha : 1 ≤ a) {x : ↥(Sz a)} (hx : x ∈ Subgroup.normalizer (rootSub a : Set ↥(Sz a))) :
    ∃ (u w : F a) (y : (F a)ˣ), x = rootSz a u w * torusSz a y := by
  have hx' : x ∈ (rootSub a : Set ↥(Sz a)) * ((torusSzHom a).range : Set ↥(Sz a)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left (rootSub a) (torusSzHom a).range
      (torusSzHom_range_le_normalizer a), ← normalizer_rootSub_eq_sup ha]
    exact hx
  obtain ⟨s, hs, t, ht, hst⟩ := Set.mem_mul.mp hx'
  obtain ⟨u, w, rfl⟩ := (mem_rootSub a).mp hs
  obtain ⟨y, rfl⟩ := ht
  exact ⟨u, w, y, hst.symm⟩

end CFSG.LocalAnalysis.WeakClosure81

end
