module

public import CFSG.LocalAnalysis.StandardType.GGStdPosRootKerForm

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem CFSG.Timmesfeld.ARS

private theorem ggRootKer_weylAction_conj {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A) (hsymm : ∀ i j, A i j = A j i)
    (u : (coxeterMatrix hA).Group) (i : I) (β : I → ℤ) :
    weylAction hA (u * (coxeterMatrix hA).simple i * u⁻¹) β =
      β - cartanPair A β (weylAction hA u (Pi.single i 1)) • weylAction hA u (Pi.single i 1) := by
  rw [weylAction_mul_apply, weylAction_mul_apply, ← CoxeterMatrix.toCoxeterSystem_simple,
    weylAction_simple, reflection_apply_coroot, map_sub, map_zsmul, weylAction_apply_inv_apply,
    ← cartanPair_single, ← cartanPair_weylAction hA hsymm u (weylAction hA u⁻¹ β) (Pi.single i 1),
    weylAction_apply_inv_apply]

theorem ggRootKer_eq_or_reflect {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℤ}
    (hA : TauCeti.IsFiniteType A) (hpd : (A.map (Int.cast : ℤ → ℚ)).PosDef)
    (hconn : GGSimplyLacedConnected (coxeterMatrix hA)) (h3 : 3 ≤ Fintype.card I) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {β β' γ : I → ℤ} (hβ : β ∈ roots hA ∅) (hβ' : β' ∈ roots hA ∅)
    (hγ : γ ∈ roots hA ∅)
    (h : ∀ e : I → ℤ, (p : ℤ) ∣ cartanPair A γ e → (p : ℤ) ∣ cartanPair A (β' - β) e) :
    β' = β ∨ β' = β - cartanPair A β γ • γ := by
  have hsymm := cartan_symm_of_posDef hpd
  have hqγ : cartanPair A γ γ = 2 := cartanForm_eq_two hA hsymm hγ
  have hqβ : cartanPair A β β = 2 := cartanForm_eq_two hA hsymm hβ
  have hqβ' : cartanPair A β' β' = 2 := cartanForm_eq_two hA hsymm hβ'
  obtain ⟨m, hm⟩ : ∃ m : ℤ, 2 * m = p + 1 := by
    obtain ⟨r, hr⟩ := (hp.eq_two_or_odd').resolve_left hp2
    exact ⟨r + 1, by rw [hr]; push_cast; ring⟩
  set c := cartanPair A β γ with hcdef
  set c' := cartanPair A β' γ with hc'def
  set lam := cartanPair A (β' - β) γ * m with hlam
  have hrad : ∀ k, (p : ℤ) ∣ coroot A k (β' - β - lam • γ) := by
    intro k
    have he := h ((2 : ℤ) • Pi.single k 1 - coroot A k γ • γ) (by
      rw [ggRootKer_cartanPair_sub_right, ggRootKer_cartanPair_smul_right,
        ggRootKer_cartanPair_smul_right, cartanPair_single, hqγ, mul_comm, sub_self]
      exact dvd_zero _)
    rw [ggRootKer_cartanPair_sub_right, ggRootKer_cartanPair_smul_right,
      ggRootKer_cartanPair_smul_right, cartanPair_single] at he
    have e : coroot A k (β' - β - lam • γ) = m * (2 * coroot A k (β' - β) -
        coroot A k γ * cartanPair A (β' - β) γ) - p * coroot A k (β' - β) := by
      rw [map_sub _ (β' - β), map_zsmul, smul_eq_mul, hlam]
      linear_combination (-coroot A k (β' - β)) * hm
    rw [e]
    exact dvd_sub (dvd_mul_of_dvd_right he _) (dvd_mul_right _ _)
  have hradB : ∀ v, (p : ℤ) ∣ cartanPair A (β' - β - lam • γ) v := fun v =>
    Finset.dvd_sum fun k _ => dvd_mul_of_dvd_right (hrad k) _
  have h1 : (p : ℤ) ∣ lam * (c + c') := by
    have := hradB (β' + β)
    rw [show cartanPair A (β' - β - lam • γ) (β' + β) = -(lam * (c + c')) by
      simp only [ggRootKer_cartanPair_sub_left, ggRootKer_cartanPair_add_right,
        ggRootKer_cartanPair_smul_left, hqβ, hqβ', hcdef, hc'def, cartanPair_comm hsymm γ,
        cartanPair_comm hsymm β β']
      ring] at this
    exact (dvd_neg).mp this
  have h2 : (p : ℤ) ∣ c' - c - 2 * lam := by
    have := hradB γ
    rwa [ggRootKer_cartanPair_sub_left, ggRootKer_cartanPair_sub_left,
      ggRootKer_cartanPair_smul_left, hqγ, ← hcdef, ← hc'def, mul_comm lam] at this
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hpZ.dvd_or_dvd h1 with hl | hl
  ·
    left
    refine ggRootKer_eq_of_rad hA hpd hconn h3 hp hp2 hβ hβ' fun k => ?_
    have := dvd_add (hrad k) (dvd_mul_of_dvd_left hl (coroot A k γ))
    rwa [map_sub, map_zsmul, smul_eq_mul, sub_add_cancel] at this
  ·
    right
    have hl2 : (p : ℤ) ∣ lam + c := by
      have h22 : (p : ℤ) ∣ 2 * (lam + c) := by
        have := dvd_sub hl h2
        rw [show c + c' - (c' - c - 2 * lam) = 2 * (lam + c) by ring] at this
        exact this
      rcases hpZ.dvd_or_dvd h22 with h22 | h22
      · exfalso
        have : p ∣ 2 := by exact_mod_cast h22
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
      · exact h22
    obtain ⟨u, i, rfl⟩ | ⟨u, i, hi, -⟩ := hγ
    swap
    · exact absurd hi (Set.notMem_empty i)
    have hs := ggRootKer_weylAction_conj hA hsymm u i β
    have hsβ : β - c • weylAction hA u (Pi.single i 1) ∈ roots hA ∅ :=
      hs ▸ weylAction_mem_roots hA _ hβ
    refine ggRootKer_eq_of_rad hA hpd hconn h3 hp hp2 hsβ hβ' fun k => ?_
    have := dvd_add (hrad k)
      (dvd_mul_of_dvd_left hl2 (coroot A k (weylAction hA u (Pi.single i 1))))
    rw [map_sub, map_zsmul, smul_eq_mul] at this
    rw [show β' - (β - c • weylAction hA u (Pi.single i 1)) =
      β' - β + c • weylAction hA u (Pi.single i 1) by abel, map_add, map_zsmul, smul_eq_mul]
    convert this using 1
    ring

theorem ggRootKer_eq_one_or_conj {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℤ}
    (hA : TauCeti.IsFiniteType A) (hsymm : ∀ i j, A i j = A j i) (u : (coxeterMatrix hA).Group)
    (i : I) (v : (coxeterMatrix hA).Group)
    (h : ∀ β ∈ roots hA ∅, weylAction hA v β = β ∨
      weylAction hA v β = β - cartanPair A β (weylAction hA u (Pi.single i 1)) •
        weylAction hA u (Pi.single i 1)) :
    v = 1 ∨ v = u * (coxeterMatrix hA).simple i * u⁻¹ := by
  set γ := weylAction hA u (Pi.single i 1)
  have hγ : γ ∈ roots hA ∅ := Or.inl ⟨u, i, rfl⟩
  have hqγ : cartanPair A γ γ = 2 := cartanForm_eq_two hA hsymm hγ
  have hsingle : ∀ j : I, (Pi.single j 1 : I → ℤ) ∈ roots hA ∅ := fun j =>
    Or.inl ⟨1, j, by rw [map_one, Module.End.one_apply]⟩
  have hext : ∀ w : (coxeterMatrix hA).Group,
      (∀ j, weylAction hA v (Pi.single j 1) = weylAction hA w (Pi.single j 1)) → v = w :=
    fun w hw => weylAction_injective hA ((Pi.basisFun ℤ I).ext fun j => by
      rw [Pi.basisFun_apply]
      exact hw j)
  have hinv := fun β => cartanPair_weylAction hA hsymm v β γ
  rcases h γ hγ with hv | hv
  · left
    refine hext 1 fun j => ?_
    rw [map_one, Module.End.one_apply]
    rcases h _ (hsingle j) with h1 | h1
    · exact h1
    · have := hinv (Pi.single j 1)
      rw [h1, hv, ggRootKer_cartanPair_sub_left, ggRootKer_cartanPair_smul_left, hqγ] at this
      have hc0 : cartanPair A (Pi.single j 1) γ = 0 := by linarith
      rw [h1, hc0, zero_smul, sub_zero]
  · right
    refine hext _ fun j => ?_
    rw [ggRootKer_weylAction_conj hA hsymm u i]
    rcases h _ (hsingle j) with h1 | h1
    · have := hinv (Pi.single j 1)
      rw [h1, hv, hqγ, ggRootKer_cartanPair_sub_right, ggRootKer_cartanPair_smul_right] at this
      have hc0 : cartanPair A (Pi.single j 1) γ = 0 := by linarith
      rw [h1, hc0, zero_smul, sub_zero]
    · exact h1

end CFSG.StandardType

end
