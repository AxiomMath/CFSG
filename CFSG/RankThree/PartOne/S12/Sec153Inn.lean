module

public import CFSG.RankThree.PartOne.S12.Sec153Weyl

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

namespace Sec153

theorem E_le_of_ne_five (hMod : KFU5Mod) (hAt : KFU5At) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
      Sec15Hyp G p A c L E → Sec12Facts G p A c L E →
      Outcome152Five p E A (lieGenerated p E) → p ≠ 5 → E ≤ lieGenerated p E := by
  intro G _ _ p A c L E h15 hF hout h5
  classical
  have h := h15.h12
  have hp := h.prime
  have hEel : IsElementaryAbelian p ↥E := h.E_elem
  have hEc : ∀ a b : ↥E, a * b = b * a := fun a b => hEel.is_comm.comm a b
  have hE : ∀ e : ↥E, e ^ p = 1 := fun e =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (IsElementaryAbelian.exponent_dvd_p p ↥E) e
  obtain ⟨M⟩ := nonempty_modData hMod h15 hF hout
  obtain ⟨f₀, hf₀, hpf₀, ⟨e₀⟩, -⟩ := id hout
  let D' : Subgroup ↥E := (lieGenerated p E).comap E.subtype
  have hdiff : ∀ i j : Fin 5, M.v j * (M.v i)⁻¹ ∈ D' := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [mul_inv_cancel]
      exact D'.one_mem
    · obtain ⟨t, ht, hθ⟩ := exists_reflection_swap hp M.θ M.refl i j hij
      obtain ⟨hne, hmod, hcent, hmoved, k, hk, hkK, hkt⟩ :=
        hAt G p A c L E f₀ h15 hF hout hf₀ hpf₀ ⟨e₀⟩ t ht
      have hKI : kZero p E t ≤ lieGenerated p E :=
        le_sSup ⟨t, ht, (isKt_iff_of_nonexceptional hne).2 rfl⟩
      have h1 : t (M.v i) = M.v j := by
        have := M.perm ⟨t, Subgroup.subset_closure ht⟩ i
        rw [hθ, Equiv.swap_apply_left] at this
        exact this
      have h2 : ((t (M.v i) * (M.v i)⁻¹ : ↥E) : G) ∈ kZero p E t :=
        hmoved ⟨t (M.v i) * (M.v i)⁻¹, Subgroup.subset_closure ⟨M.v i, rfl⟩, rfl⟩
      rw [h1] at h2
      exact hKI h2
  have hnorm : D'.Normal := ⟨fun n hn g => by rw [hEc g n, mul_inv_cancel_right]; exact hn⟩
  have h1 : M.v 0 * M.v 1 * M.v 2 * M.v 3 * M.v 4 = 1 := by
    have := (M.rel (fun _ => 1)).2 ⟨1, fun i => by simp⟩
    simpa using this
  have hq : ∀ i, (QuotientGroup.mk (M.v i) : ↥E ⧸ D') = QuotientGroup.mk (M.v 0) := by
    intro i
    rw [QuotientGroup.eq]
    have := hdiff i 0
    rwa [hEc (M.v 0) (M.v i)⁻¹] at this
  have hq5 : (QuotientGroup.mk (M.v 0) : ↥E ⧸ D') ^ 5 = 1 := by
    have h2 : (QuotientGroup.mk (M.v 0 * M.v 1 * M.v 2 * M.v 3 * M.v 4) : ↥E ⧸ D') = 1 := by
      rw [h1]
      exact QuotientGroup.mk_one _
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      hq 1, hq 2, hq 3, hq 4] at h2
    simpa [pow_succ, mul_assoc] using h2
  have hqp : (QuotientGroup.mk (M.v 0) : ↥E ⧸ D') ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hE, QuotientGroup.mk_one]
  have hq1 : (QuotientGroup.mk (M.v 0) : ↥E ⧸ D') = 1 := by
    have hcop : Nat.Coprime 5 p := (Nat.coprime_primes (by norm_num) hp).2 (Ne.symm h5)
    have h3 := orderOf_dvd_of_pow_eq_one hq5
    have h4 := orderOf_dvd_of_pow_eq_one hqp
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h3 h4)
  have hv : ∀ i, M.v i ∈ D' := fun i => by
    have h2 := hq i
    rw [hq1] at h2
    exact (QuotientGroup.eq_one_iff _).1 h2
  intro x hx
  obtain ⟨a, ha⟩ := M.gen ⟨x, hx⟩
  have hmem : (⟨x, hx⟩ : ↥E) ∈ D' := by
    rw [ha]
    exact D'.mul_mem (D'.mul_mem (D'.mul_mem (D'.mul_mem (D'.zpow_mem (hv 0) _)
      (D'.zpow_mem (hv 1) _)) (D'.zpow_mem (hv 2) _)) (D'.zpow_mem (hv 3) _))
      (D'.zpow_mem (hv 4) _)
  exact hmem

theorem u5_act_inner_of_ne_five (hMod : KFU5Mod) (hAt : KFU5At) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
      Sec15Hyp G p A c L E → Sec12Facts G p A c L E →
      Outcome152Five p E A (lieGenerated p E) → p ≠ 5 →
      ∀ (f : ℕ) (e : ↥(lieGenerated p E) ⧸ Subgroup.center ↥(lieGenerated p E) ≃* projSU 5 2 f)
        (x : G) (hx : x ∈ lieNormalizer p E), x ∈ E →
          ∃ z : projSU 5 2 f, U5K.U5Act (lieGenerated p E) e ⟨x, hx⟩ = MulAut.conj z := by
  intro G _ _ p A c L E h15 hF hout h5 f e x hx hxE
  have hxI : x ∈ lieGenerated p E := E_le_of_ne_five hMod hAt G p A c L E h15 hF hout h5 hxE
  exact ⟨e (⟨x, hxI⟩ : ↥(lieGenerated p E)), U5K.U5Act_of_mem (lieGenerated p E) e ⟨x, hxI⟩⟩

end Sec153

end CFSG.RankThree.PartOne
