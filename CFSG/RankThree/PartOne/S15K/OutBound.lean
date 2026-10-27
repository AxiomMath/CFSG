module

public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG CFSG.RankThree.PartOne

theorem card_le_of_outPNice {P : Type} [Group P] [Finite P] {p : ℕ} (hp : p.Prime)
    (hOut : OutStructure.OutPNice p P) {E : Type*} [Group E] [Finite E]
    [hEel : IsElementaryAbelian p E] (ρ : E →* MulAut P)
    (hρ : ∀ e : E, ρ e ∈ OutStructure.Inn P → e = 1) : Nat.card E ≤ p := by
  classical
  by_contra hlt
  push Not at hlt
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup p E).exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra h
    push Not at h
    have hp2 := hp.two_le
    interval_cases k
    · rw [pow_zero] at hk
      omega
    · rw [pow_one] at hk
      omega
  obtain ⟨E', hE'⟩ := Sylow.exists_subgroup_card_pow_prime p (n := 2)
    (by rw [hk]; exact pow_dvd_pow p hk2)
  have hEpow : ∀ e : E, e ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (IsElementaryAbelian.exponent_dvd_p p E)
  have hEcomm : ∀ a b : E, a * b = b * a := fun a b => hEel.is_comm.comm a b
  let f : ↥E' →* MulAut P := ρ.comp E'.subtype
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro e he
    have h1 : ρ (e : E) = 1 := he
    exact Subtype.ext (hρ _ (by rw [h1]; exact (OutStructure.Inn P).one_mem))
  let Eim : Subgroup (MulAut P) := f.range
  have hEimel : IsElementaryAbelian p ↥Eim :=
    { toIsMulCommutative := ⟨⟨fun a b => by
        obtain ⟨a', ha'⟩ := a.2
        obtain ⟨b', hb'⟩ := b.2
        apply Subtype.ext
        show (a : MulAut P) * b = b * a
        rw [← ha', ← hb', ← map_mul, ← map_mul]
        exact congrArg f (Subtype.ext (hEcomm a' b'))⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun a => by
        obtain ⟨a', ha'⟩ := a.2
        apply Subtype.ext
        show (a : MulAut P) ^ p = 1
        rw [← ha', ← map_pow]
        have : (a' : E) ^ p = 1 := hEpow a'
        have h2 : a' ^ p = 1 := Subtype.ext this
        rw [h2, map_one] }
  have hEimcard : Nat.card Eim = p ^ 2 := by
    rw [← hE']
    exact (Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv).symm
  have hEimbot : Eim ⊓ Sec66T.innerAut P = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨⟨a', rfl⟩, hy⟩
    have : a' = 1 := Subtype.ext (hρ (a' : E) hy)
    rw [Subgroup.mem_bot, this, map_one]
  exact Sec66T.no_plane_of_outPNice hp hOut Eim hEimel hEimcard hEimbot

end CFSG.RankThree.PartOne.S15K
