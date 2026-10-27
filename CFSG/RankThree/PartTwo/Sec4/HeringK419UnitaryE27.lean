module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringUnitary

theorem exists_E27 {U Y : Type} [Group U] [Group Y] [Finite U] [Finite Y]
    (hZ : Subgroup.center U = ⊥) (ι : U →* Y) (hι : Function.Injective ι) (α : MulAut Y)
    (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1) (hfix : ∀ u, α (ι u) = ι u)
    (E : Subgroup U) (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) :
    ∃ F : Subgroup (MulAut Y), CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card F = 27 ∧
      F ≤ (MulAut.conj : Y →* MulAut Y).range ⊔ Subgroup.zpowers α := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hEc, hEe⟩ := hE
  haveI := hEc
  have hord : orderOf α = 3 := orderOf_eq_prime hα3 hα1
  have hcomm_α : ∀ e : U, Commute (MulAut.conj (ι e)) α := by
    intro e
    show MulAut.conj (ι e) * α = α * MulAut.conj (ι e)
    ext y
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hfix]
  have hcentral : ∀ z : U, (∀ u : U, MulAut.conj (ι z) (ι u) = ι u) → z = 1 := by
    intro z hz
    have hzc : z ∈ Subgroup.center U := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply hι
      have h := hz g
      rw [MulAut.conj_apply] at h
      rw [map_mul, map_mul]
      exact (mul_inv_eq_iff_eq_mul.mp h).symm
    rw [hZ] at hzc
    exact Subgroup.mem_bot.mp hzc
  have hnot : ∀ z : U, MulAut.conj (ι z) ≠ α := by
    intro z hz
    have hz1 : z = 1 := hcentral z (fun u => by rw [hz]; exact hfix u)
    apply hα1
    rw [← hz, hz1, map_one, map_one]
  let φ1 : E →* MulAut Y := (MulAut.conj : Y →* MulAut Y).comp (ι.comp E.subtype)
  let φ2 : Subgroup.zpowers α →* MulAut Y := (Subgroup.zpowers α).subtype
  have hcomm : ∀ (x : E) (y : Subgroup.zpowers α), Commute (φ1 x) (φ2 y) := by
    intro x y
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp y.2
    show Commute (MulAut.conj (ι (x : U))) (y : MulAut Y)
    rw [← hk]
    exact (hcomm_α (x : U)).zpow_right k
  let Φ : ↥E × ↥(Subgroup.zpowers α) →* MulAut Y := MonoidHom.noncommCoprod φ1 φ2 hcomm
  have hΦ_apply : ∀ p, Φ p = MulAut.conj (ι (p.1 : U)) * (p.2 : MulAut Y) := fun p => rfl
  have hpow3 : ∀ b ∈ Subgroup.zpowers α, b ^ 3 = 1 := by
    intro b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hα3, one_zpow]
  have hzcomm : ∀ a ∈ Subgroup.zpowers α, ∀ b ∈ Subgroup.zpowers α, Commute a b := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.refl α).zpow_zpow k l
  have hEpow : ∀ x : E, x ^ 3 = 1 := by
    intro x
    apply Subtype.ext
    simpa using hEe (x : U) x.2
  have hΦpow : ∀ p : ↥E × ↥(Subgroup.zpowers α), p ^ 3 = 1 := by
    intro p
    refine Prod.ext ?_ ?_
    · exact hEpow p.1
    · exact Subtype.ext (hpow3 _ p.2.2)
  have hcommP : ∀ p q : ↥E × ↥(Subgroup.zpowers α), p * q = q * p := by
    intro p q
    refine Prod.ext ?_ ?_
    · exact mul_comm' p.1 q.1
    · exact Subtype.ext (hzcomm _ p.2.2 _ q.2.2).eq
  have hFc : IsMulCommutative Φ.range := by
    refine IsMulCommutative.of_comm fun x y => Subtype.ext ?_
    obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp x.2
    obtain ⟨q, hq⟩ := MonoidHom.mem_range.mp y.2
    show (x : MulAut Y) * (y : MulAut Y) = (y : MulAut Y) * (x : MulAut Y)
    rw [← hp, ← hq, ← map_mul, ← map_mul, hcommP p q]
  have hFexp : ∀ x ∈ Φ.range, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨p, rfl⟩ := MonoidHom.mem_range.mp hx
    rw [← map_pow, hΦpow p, map_one]
  have hEA : IsMulCommutative Φ.range ∧ ∀ x ∈ Φ.range, x ^ 3 = 1 := ⟨hFc, hFexp⟩
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_one Φ).mpr fun p hp => ?_
    have hp' : MulAut.conj (ι (p.1 : U)) * (p.2 : MulAut Y) = 1 :=
      (hΦ_apply p).symm.trans hp
    by_cases hβ : (p.2 : MulAut Y) = 1
    · have hc : MulAut.conj (ι (p.1 : U)) = 1 := by
        rw [hβ, mul_one] at hp'
        exact hp'
      have he : (p.1 : U) = 1 := by
        apply hcentral
        intro u
        rw [hc, MulAut.one_apply]
      exact Prod.ext (Subtype.ext he) (Subtype.ext hβ)
    · exfalso
      have hβ3 : (p.2 : MulAut Y) ^ 3 = 1 := hpow3 _ p.2.2
      have hord_β : orderOf (p.2 : MulAut Y) = 3 := orderOf_eq_prime hβ3 hβ
      have hle : Subgroup.zpowers (p.2 : MulAut Y) ≤ Subgroup.zpowers α :=
        Subgroup.zpowers_le.mpr p.2.2
      have heq : Subgroup.zpowers (p.2 : MulAut Y) = Subgroup.zpowers α :=
        Subgroup.eq_of_le_of_card_ge hle
          (le_of_eq (by rw [Nat.card_zpowers, Nat.card_zpowers, hord_β, hord]))
      have hαmem : α ∈ Subgroup.zpowers (p.2 : MulAut Y) := by
        rw [heq]
        exact Subgroup.mem_zpowers α
      have hc_eq : MulAut.conj (ι (p.1 : U)) = (p.2 : MulAut Y)⁻¹ :=
        eq_inv_of_mul_eq_one_left hp'
      have hαmem' : α ∈ Subgroup.zpowers (MulAut.conj (ι (p.1 : U))) := by
        rw [hc_eq, Subgroup.zpowers_inv]
        exact hαmem
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hαmem'
      have hn' : MulAut.conj (ι ((p.1 : U) ^ n)) = α := by
        rw [map_zpow ι, map_zpow (MulAut.conj : Y →* MulAut Y)]
        exact hn
      exact hnot _ hn'
  have hcard : Nat.card Φ.range = 27 := by
    have h1 := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [Nat.card_prod, hE9, Nat.card_zpowers, hord] at h1
    omega
  refine ⟨Φ.range, hEA, hcard, ?_⟩
  intro x hx
  obtain ⟨p, rfl⟩ := MonoidHom.mem_range.mp hx
  rw [hΦ_apply]
  exact mul_mem (Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨ι (p.1 : U), rfl⟩))
    (Subgroup.mem_sup_right p.2.2)

end CFSG.RankThree.PartTwo.Sec4.HeringUnitary
