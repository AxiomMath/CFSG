module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySuzukiModule
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LieType.Ree.SuzukiSplitTorusCentralizers

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open CFSG.Blueprint CFSG.LieType.Ree

variable {a : ℕ} {K : Type} [Field K] [Finite K]

private theorem involutions_conjugate (hK : Nat.card K = 2 ^ (2 * a + 1))
    {x y : ↥(suzukiGroup a K)} (hx : x * x = 1) (hx1 : x ≠ 1)
    (hy : y * y = 1) (hy1 : y ≠ 1) :
    ∃ g : ↥(suzukiGroup a K), g * y * g⁻¹ = x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx) hx1
  have hyo : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy) hy1
  obtain ⟨g, hg⟩ := isConj_iff.1
    (CFSG.QuasithinUnique.Setup.Family.suzuki_involutions_conjugate (a := a) (K := K)
      hK y x hyo hxo)
  exact ⟨g, hg⟩

theorem exists_closure_three_conj_eq_top_of_closure (hK : Nat.card K = 2 ^ (2 * a + 1))
    {u₁ u₂ u₃ : ↥(suzukiGroup a K)} (h₁ : u₁ * u₁ = 1) (h₁' : u₁ ≠ 1)
    (h₂ : u₂ * u₂ = 1) (h₂' : u₂ ≠ 1) (h₃ : u₃ * u₃ = 1) (h₃' : u₃ ≠ 1)
    (hgen : Subgroup.closure ({u₁, u₂, u₃} : Set ↥(suzukiGroup a K)) = ⊤)
    {x : ↥(suzukiGroup a K)} (hx : x * x = 1) (hx1 : x ≠ 1) :
    ∃ g₁ g₂ : ↥(suzukiGroup a K),
      Subgroup.closure ({x, g₁ * x * g₁⁻¹, g₂ * x * g₂⁻¹} : Set ↥(suzukiGroup a K)) = ⊤ := by
  obtain ⟨c, hc⟩ := involutions_conjugate hK h₁ h₁' hx hx1
  have hux : c⁻¹ * u₁ * c = x := by rw [← hc]; group
  have hconj₂ : (c⁻¹ * u₂ * c) * (c⁻¹ * u₂ * c) = 1 := by
    rw [show c⁻¹ * u₂ * c * (c⁻¹ * u₂ * c) = c⁻¹ * (u₂ * u₂) * c by group, h₂]; group
  have hconj₂' : c⁻¹ * u₂ * c ≠ 1 := by
    intro h
    apply h₂'
    have := congrArg (fun z => c * z * c⁻¹) h
    simpa [mul_assoc] using this
  have hconj₃ : (c⁻¹ * u₃ * c) * (c⁻¹ * u₃ * c) = 1 := by
    rw [show c⁻¹ * u₃ * c * (c⁻¹ * u₃ * c) = c⁻¹ * (u₃ * u₃) * c by group, h₃]; group
  have hconj₃' : c⁻¹ * u₃ * c ≠ 1 := by
    intro h
    apply h₃'
    have := congrArg (fun z => c * z * c⁻¹) h
    simpa [mul_assoc] using this
  obtain ⟨g₁, hg₁⟩ := involutions_conjugate hK hconj₂ hconj₂' hx hx1
  obtain ⟨g₂, hg₂⟩ := involutions_conjugate hK hconj₃ hconj₃' hx hx1
  refine ⟨g₁, g₂, ?_⟩
  rw [hg₁, hg₂]
  have hmap := MonoidHom.map_closure (MulAut.conj c⁻¹).toMonoidHom
    ({u₁, u₂, u₃} : Set ↥(suzukiGroup a K))
  rw [hgen, Subgroup.map_top_of_surjective _ (MulAut.conj c⁻¹).surjective] at hmap
  rw [hmap]
  congr 1
  ext y
  simp [MulAut.conj_apply, hux]

private theorem suzukiSElt_zero_one_sq (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    suzukiSElt a K 0 1 * suzukiSElt a K 0 1 = 1 := by
  rw [suzukiSElt_mul hK, ← suzukiSElt_zero_zero hK]
  congr 1
  · simp
  · linear_combination (suzuki_frob_data a hK).1

private theorem suzukiSElt_zero_one_ne_one (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    suzukiSElt a K 0 1 ≠ 1 := by
  intro h
  rw [← suzukiSElt_zero_zero hK, suzukiSElt_inj] at h
  exact one_ne_zero h.2

private theorem suzuki_exists_div_suzukiN (hK : Nat.card K = 2 ^ (2 * a + 1))
    {c : K} (hc : c ≠ 0) : ∃ v : K, v ≠ 0 ∧ v / suzukiN a 0 v = c := by
  have hunits : ((Nat.card Kˣ : ℕ) : ℤ) = (2 : ℤ) ^ (2 * a + 1) - 1 := by
    rw [Nat.card_units, hK, Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_one]
  have hcop : IsCoprime ((2 : ℤ) ^ (a + 1) - 1) ((Nat.card Kˣ : ℕ) : ℤ) := by
    rw [hunits]
    exact ⟨(2 : ℤ) ^ (a + 1) + 1, -2, by ring⟩
  have hbij : Function.Bijective (fun s : Kˣ => s ^ ((2 : ℤ) ^ (a + 1) - 1 : ℤ)) :=
    zpow_bijective_of_isCoprime hcop
  obtain ⟨w, hw⟩ := hbij.2 (Units.mk0 (c⁻¹) (inv_ne_zero hc))
  refine ⟨(w : K), w.ne_zero, ?_⟩
  have hwK : ((w : K) ^ ((2 : ℤ) ^ (a + 1) - 1 : ℤ)) = c⁻¹ := by
    have h := congrArg Units.val hw
    rwa [Units.val_zpow_eq_zpow_val] at h
  have hneg : ((w : K) ^ (1 - (2 : ℤ) ^ (a + 1) : ℤ)) = c := by
    have h1 : (1 - (2 : ℤ) ^ (a + 1) : ℤ) = -((2 : ℤ) ^ (a + 1) - 1) := by ring
    rw [h1, zpow_neg, hwK, inv_inv]
  have hN : suzukiN a 0 (w : K) = (w : K) ^ (2 ^ (a + 1)) := by
    simp [suzukiN, zero_pow (by positivity : 2 ^ (a + 1) + 2 ≠ 0)]
  have hdiv : (w : K) / (w : K) ^ (2 ^ (a + 1)) = ((w : K) ^ (1 - (2 : ℤ) ^ (a + 1) : ℤ)) := by
    have h1 : (w : K) ^ (1 - (2 : ℤ) ^ (a + 1) : ℤ) =
        (w : K) * ((w : K) ^ (2 ^ (a + 1)))⁻¹ := by
      have hexp : (1 - (2 : ℤ) ^ (a + 1) : ℤ) = 1 + -(((2 ^ (a + 1) : ℕ) : ℤ)) := by
        push_cast
        ring
      rw [hexp, zpow_add₀ w.ne_zero, zpow_one, zpow_neg, zpow_natCast]
    rw [h1, div_eq_mul_inv]
  rw [hN, hdiv, hneg]

private theorem suzuki_conj_mem_suzukiZ0 (hK : Nat.card K = 2 ^ (2 * a + 1))
    {b z : ↥(suzukiGroup a K)} (hb : b ∈ suzukiB a K) (hz : z ∈ suzukiZ0 a K) :
    b * z * b⁻¹ ∈ suzukiZ0 a K := by
  obtain ⟨u, v, l, rfl⟩ := (mem_suzukiB_iff hK).1 hb
  obtain ⟨w, rfl⟩ := (mem_suzukiZ0_iff hK).1 hz
  have h1 : suzukiDElt a K l * suzukiSElt a K 0 w * (suzukiDElt a K l)⁻¹ =
      suzukiSElt a K 0 (((l⁻¹ : Kˣ) : K) ^ (2 ^ (a + 1) + 1) * w) := by
    simpa using suzukiDElt_conj' hK l 0 w
  have h2 : suzukiSElt a K u v *
      suzukiSElt a K 0 (((l⁻¹ : Kˣ) : K) ^ (2 ^ (a + 1) + 1) * w) * (suzukiSElt a K u v)⁻¹ =
      suzukiSElt a K 0 (((l⁻¹ : Kˣ) : K) ^ (2 ^ (a + 1) + 1) * w) := by
    rw [← suzukiSElt_zero_commute hK _ u v]
    group
  rw [mul_inv_rev,
    show suzukiSElt a K u v * suzukiDElt a K l * suzukiSElt a K 0 w *
        ((suzukiDElt a K l)⁻¹ * (suzukiSElt a K u v)⁻¹) =
        suzukiSElt a K u v * (suzukiDElt a K l * suzukiSElt a K 0 w *
          (suzukiDElt a K l)⁻¹) * (suzukiSElt a K u v)⁻¹ by group,
    h1, h2]
  exact (mem_suzukiZ0_iff hK).2 ⟨_, rfl⟩

private theorem suzukiSElt_mul_WElt_mem_suzukiB (hK : Nat.card K = 2 ^ (2 * a + 1))
    (H : Subgroup ↥(suzukiGroup a K)) (hW : suzukiWElt a K ∈ H)
    (hZ0 : suzukiZ0 a K ≤ H) (c : K) :
    ∃ h ∈ H, ∃ b ∈ suzukiB a K, suzukiSElt a K c 0 * suzukiWElt a K = h * b := by
  by_cases hc : c = 0
  · exact ⟨suzukiWElt a K, hW, 1, one_mem _, by
      rw [hc, suzukiSElt_zero_zero hK, one_mul, mul_one]⟩
  · obtain ⟨v, hv0, hvc⟩ := suzuki_exists_div_suzukiN hK hc
    obtain ⟨hN, hfac⟩ := suzuki_bruhat_factorization hK (0 : K) v (by simp [hv0])
    set t : Kˣ := Units.mk0 (suzukiN a 0 v) hN with ht_def
    have ht : (t : K) = suzukiN a 0 v := rfl
    have e : suzukiWElt a K * suzukiSElt a K 0 v * suzukiWElt a K =
        suzukiSElt a K (v / (t : K)) ((0 : K) / (t : K)) *
          suzukiDElt a K (t ^ (2 - 2 ^ (a + 1) : ℤ)) * suzukiWElt a K *
          suzukiSElt a K ((0 ^ (2 ^ (a + 1) + 1) + v) / (t : K))
            (v / (t : K) ^ 2 ^ (a + 1)) :=
      suzukiSElt_ext (hfac t ht)
    rw [zero_div, zero_pow (by positivity : 2 ^ (a + 1) + 1 ≠ 0), zero_add] at e
    have hvc' : v / (t : K) = c := by rw [ht, hvc]
    rw [hvc'] at e
    set μ : Kˣ := t ^ (2 - 2 ^ (a + 1) : ℤ) with hμ_def
    have hWD : suzukiDElt a K μ * suzukiWElt a K = suzukiWElt a K * suzukiDElt a K μ⁻¹ := by
      calc suzukiDElt a K μ * suzukiWElt a K
          = (suzukiWElt a K * suzukiWElt a K) * suzukiDElt a K μ * suzukiWElt a K := by
            rw [suzukiWElt_mul_self]
            group
        _ = suzukiWElt a K * (suzukiWElt a K * suzukiDElt a K μ * suzukiWElt a K) := by group
        _ = suzukiWElt a K * suzukiDElt a K μ⁻¹ := by rw [suzukiWElt_D_W hK μ]
    have hDWD : suzukiDElt a K μ * suzukiWElt a K * suzukiDElt a K μ = suzukiWElt a K := by
      rw [hWD, mul_assoc, ← suzukiDElt_inv, inv_mul_cancel, mul_one]
    have hSDW : suzukiSElt a K c 0 * suzukiDElt a K μ * suzukiWElt a K =
        (suzukiWElt a K * suzukiSElt a K 0 v * suzukiWElt a K) *
          (suzukiSElt a K c (v / (t : K) ^ 2 ^ (a + 1)))⁻¹ := by
      rw [e]
      group
    refine ⟨suzukiWElt a K * suzukiSElt a K 0 v * suzukiWElt a K,
      H.mul_mem (H.mul_mem hW (hZ0 ((mem_suzukiZ0_iff hK).2 ⟨v, rfl⟩))) hW,
      (suzukiSElt a K c (v / (t : K) ^ 2 ^ (a + 1)))⁻¹ * suzukiDElt a K μ, ?_, ?_⟩
    · exact (suzukiB a K).mul_mem
        ((suzukiB a K).inv_mem
          (suzukiU_le_suzukiB a K (suzukiSElt_mem_suzukiU a K _ _)))
        (suzukiT_le_suzukiB a K (suzukiDElt_mem_suzukiT a K μ))
    · calc suzukiSElt a K c 0 * suzukiWElt a K
          = (suzukiSElt a K c 0 * suzukiDElt a K μ * suzukiWElt a K) * suzukiDElt a K μ := by
            rw [show (suzukiSElt a K c 0 * suzukiDElt a K μ * suzukiWElt a K) * suzukiDElt a K μ =
                suzukiSElt a K c 0 * (suzukiDElt a K μ * suzukiWElt a K * suzukiDElt a K μ) by
              group,
              hDWD]
        _ = ((suzukiWElt a K * suzukiSElt a K 0 v * suzukiWElt a K) *
              (suzukiSElt a K c (v / (t : K) ^ 2 ^ (a + 1)))⁻¹) * suzukiDElt a K μ := by
            rw [hSDW]
        _ = (suzukiWElt a K * suzukiSElt a K 0 v * suzukiWElt a K) *
              ((suzukiSElt a K c (v / (t : K) ^ 2 ^ (a + 1)))⁻¹ * suzukiDElt a K μ) := by
            group

private theorem suzuki_closure_involutions_eq_top (hK : Nat.card K = 2 ^ (2 * a + 1))
    (ha : 1 ≤ a) :
    Subgroup.closure {z : ↥(suzukiGroup a K) | z * z = 1 ∧ z ≠ 1} = ⊤ := by
  classical
  set S : Set ↥(suzukiGroup a K) := {z | z * z = 1 ∧ z ≠ 1} with hS
  have himg : ∀ (g z : ↥(suzukiGroup a K)), z ∈ S → MulAut.conj g z ∈ S := by
    intro g z hz
    refine ⟨?_, ?_⟩
    · have h := map_mul (MulAut.conj g) z z
      rw [← h, hz.1, map_one]
    · intro h1
      apply hz.2
      have h2 : MulAut.conj g z = MulAut.conj g 1 := by simpa using h1
      exact (MulAut.conj g).injective h2
  have hnorm : (Subgroup.closure S).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hset : ⇑(MulAut.conj g).toMonoidHom '' S = S := by
      refine Set.Subset.antisymm (by rintro _ ⟨z, hz, rfl⟩; exact himg g z hz) ?_
      intro y hy
      exact ⟨MulAut.conj g⁻¹ y, himg g⁻¹ y hy, by
        show MulAut.conj g (MulAut.conj g⁻¹ y) = y
        rw [MulAut.conj_apply, MulAut.conj_apply]
        group⟩
    have hmap := MonoidHom.map_closure (MulAut.conj g).toMonoidHom S
    rw [hset] at hmap
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hn
  have hne : Subgroup.closure S ≠ ⊥ := by
    intro h
    have hx : suzukiSElt a K 0 1 ∈ Subgroup.closure S :=
      Subgroup.subset_closure ⟨suzukiSElt_zero_one_sq hK, suzukiSElt_zero_one_ne_one hK⟩
    rw [h] at hx
    exact suzukiSElt_zero_one_ne_one hK (by simpa using hx)
  haveI : IsSimpleGroup ↥(suzukiGroup a K) := (suzuki_simple ha hK).2.2
  haveI := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.closure S) with h | h
  · exact absurd h hne
  · exact h

theorem suzuki_eq_top_of_suzukiZ0_le_of_W_mem (hK : Nat.card K = 2 ^ (2 * a + 1)) (ha : 1 ≤ a)
    {H : Subgroup ↥(suzukiGroup a K)} (hZ0 : suzukiZ0 a K ≤ H)
    (hW : suzukiWElt a K ∈ H) : H = ⊤ := by
  have hθ0 : 2 ^ (a + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hHB : ∀ g : ↥(suzukiGroup a K), ∃ h ∈ H, ∃ b ∈ suzukiB a K, g = h * b := by
    intro g
    rcases suzukiGroup_mem_cells hK g with hg | hg
    · exact ⟨1, H.one_mem, g, hg, (one_mul g).symm⟩
    · obtain ⟨u, v, l, c, d, rfl⟩ := (mem_suzukiBigCell_iff hK).1 hg
      obtain ⟨h1, hh1, b1, hb1, hb1eq⟩ :=
        suzukiSElt_mul_WElt_mem_suzukiB hK H hW hZ0 u
      have hDW : suzukiDElt a K l * suzukiWElt a K =
          suzukiWElt a K * suzukiDElt a K l⁻¹ := by
        calc suzukiDElt a K l * suzukiWElt a K
            = (suzukiWElt a K * suzukiWElt a K) * suzukiDElt a K l *
                suzukiWElt a K := by rw [suzukiWElt_mul_self]; group
          _ = suzukiWElt a K * (suzukiWElt a K * suzukiDElt a K l * suzukiWElt a K) := by group
          _ = suzukiWElt a K * suzukiDElt a K l⁻¹ := by rw [suzukiWElt_D_W hK l]
      have hsplit : suzukiSElt a K u v = suzukiSElt a K 0 v * suzukiSElt a K u 0 := by
        rw [suzukiSElt_mul hK]
        congr 1
        · simp
        · simp [zero_pow hθ0]
      have hmain : suzukiSElt a K u v * suzukiDElt a K l * suzukiWElt a K *
          suzukiSElt a K c d =
          (suzukiSElt a K 0 v * h1) *
            (b1 * suzukiDElt a K l⁻¹ * suzukiSElt a K c d) := by
        calc suzukiSElt a K u v * suzukiDElt a K l * suzukiWElt a K * suzukiSElt a K c d
            = suzukiSElt a K u v * (suzukiDElt a K l * suzukiWElt a K) *
                suzukiSElt a K c d := by group
          _ = suzukiSElt a K u v * (suzukiWElt a K * suzukiDElt a K l⁻¹) *
                suzukiSElt a K c d := by rw [hDW]
          _ = suzukiSElt a K 0 v * suzukiSElt a K u 0 *
                (suzukiWElt a K * suzukiDElt a K l⁻¹) * suzukiSElt a K c d := by rw [hsplit]
          _ = suzukiSElt a K 0 v * (suzukiSElt a K u 0 * suzukiWElt a K) *
                (suzukiDElt a K l⁻¹ * suzukiSElt a K c d) := by group
          _ = suzukiSElt a K 0 v * (h1 * b1) *
                (suzukiDElt a K l⁻¹ * suzukiSElt a K c d) := by rw [hb1eq]
          _ = (suzukiSElt a K 0 v * h1) *
                (b1 * suzukiDElt a K l⁻¹ * suzukiSElt a K c d) := by group
      refine ⟨suzukiSElt a K 0 v * h1,
        H.mul_mem (hZ0 ((mem_suzukiZ0_iff hK).2 ⟨v, rfl⟩)) hh1,
        b1 * suzukiDElt a K l⁻¹ * suzukiSElt a K c d, ?_, hmain⟩
      refine (suzukiB a K).mul_mem ((suzukiB a K).mul_mem hb1
        (suzukiT_le_suzukiB a K (suzukiDElt_mem_suzukiT a K l⁻¹)))
        (suzukiU_le_suzukiB a K (suzukiSElt_mem_suzukiU a K c d))
  have hInv : ∀ z : ↥(suzukiGroup a K), z * z = 1 → z ≠ 1 → z ∈ H := by
    intro z hz hz1
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz) hz1
    have hx0o : orderOf (suzukiSElt a K 0 1) = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact suzukiSElt_zero_one_sq hK)
        (suzukiSElt_zero_one_ne_one hK)
    obtain ⟨g, hg⟩ := isConj_iff.1
      (CFSG.QuasithinUnique.Setup.Family.suzuki_involutions_conjugate (a := a) (K := K) hK
        z (suzukiSElt a K 0 1) hzo hx0o)
    obtain ⟨h, hhH, b, hbB, hb⟩ := hHB g⁻¹
    have hg' : g = b⁻¹ * h⁻¹ := by
      have h2 : (h * b)⁻¹ = b⁻¹ * h⁻¹ := mul_inv_rev h b
      rw [← hb] at h2
      simpa using h2
    have hz_eq : z = h * (b * suzukiSElt a K 0 1 * b⁻¹) * h⁻¹ := by
      have h1 : z = g⁻¹ * suzukiSElt a K 0 1 * g := by rw [← hg]; group
      rw [h1, hb, hg']
      group
    rw [hz_eq]
    have hbZ : b * suzukiSElt a K 0 1 * b⁻¹ ∈ suzukiZ0 a K :=
      suzuki_conj_mem_suzukiZ0 hK hbB ((mem_suzukiZ0_iff hK).2 ⟨1, rfl⟩)
    exact H.mul_mem (H.mul_mem hhH (hZ0 hbZ)) (H.inv_mem hhH)
  have hle : Subgroup.closure {z : ↥(suzukiGroup a K) | z * z = 1 ∧ z ≠ 1} ≤ H :=
    (Subgroup.closure_le H).2 (fun z hz => hInv z hz.1 hz.2)
  rw [suzuki_closure_involutions_eq_top hK ha] at hle
  exact le_antisymm le_top hle

private theorem suzukiT_le_of_mem_suzukiDElt_sq_inv (hK : Nat.card K = 2 ^ (2 * a + 1))
    {H : Subgroup ↥(suzukiGroup a K)} {l : Kˣ}
    (hl : ∀ m : Kˣ, m ∈ Subgroup.zpowers l)
    (hD : suzukiDElt a K (l⁻¹ * l⁻¹) ∈ H) : suzukiT a K ≤ H := by
  rw [suzukiT]
  refine (Subgroup.closure_le H).2 ?_
  rintro _ ⟨m, rfl⟩
  have hodd : Odd (Nat.card Kˣ) := odd_card_units hK
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.card Kˣ = 2 * k + 1 := hodd
  have hcop2 : IsCoprime (2 : ℤ) ((Nat.card Kˣ : ℕ) : ℤ) := by
    refine ⟨-(k : ℤ), 1, ?_⟩
    rw [hk]
    push_cast
    ring
  have hz2 : ∀ m : Kˣ, m ∈ Subgroup.zpowers (l⁻¹ * l⁻¹) := by
    intro m
    obtain ⟨y, hy⟩ := (zpow_bijective_of_isCoprime hcop2).2 l
    have hy' : y * y = l := by
      have h : (y : Kˣ) ^ (2 : ℤ) = l := hy
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two] at h
      exact h
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hl y)
    have hl2 : l ∈ Subgroup.zpowers (l ^ 2) := by
      refine Subgroup.mem_zpowers_iff.2 ⟨j, ?_⟩
      have h2 : (l ^ 2 : Kˣ) ^ j = y * y := by
        rw [show ((l : Kˣ) ^ 2) = l ^ (((2 : ℕ) : ℤ)) from (zpow_natCast l 2).symm,
          ← zpow_mul l (((2 : ℕ) : ℤ)) j,
          show (((2 : ℕ) : ℤ)) * j = j + j by ring, zpow_add l j j, hj]
      rw [h2, hy']
    have htop_l : Subgroup.zpowers l = ⊤ := (Subgroup.eq_top_iff' _).2 hl
    have htop2 : Subgroup.zpowers (l ^ 2) = ⊤ := by
      refine le_antisymm le_top ?_
      intro m' _
      exact Subgroup.zpowers_le.2 hl2 (by rw [htop_l]; exact Subgroup.mem_top m')
    have hfin : Subgroup.zpowers (l⁻¹ * l⁻¹) = Subgroup.zpowers (l ^ 2) := by
      rw [show l⁻¹ * l⁻¹ = (l ^ 2)⁻¹ by group, Subgroup.zpowers_inv]
    rw [hfin, htop2]
    exact Subgroup.mem_top m
  have hT : ∀ m : Kˣ, suzukiDElt a K m ∈ H := by
    intro m
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hz2 m)
    let Dh : Kˣ →* ↥(suzukiGroup a K) :=
      { toFun := suzukiDElt a K
        map_one' := suzukiDElt_one
        map_mul' := fun a b => (suzukiDElt_mul a b).symm }
    have hDh : Dh (l⁻¹ * l⁻¹) ∈ H := hD
    have hm : suzukiDElt a K m = Dh (l⁻¹ * l⁻¹) ^ j := by
      have h1 : Dh ((l⁻¹ * l⁻¹) ^ j) = Dh (l⁻¹ * l⁻¹) ^ j := map_zpow Dh _ j
      rw [hj] at h1
      exact h1
    rw [hm]
    exact H.zpow_mem hDh j
  exact hT m

theorem suzuki_closure_three_involutions_eq_top (hK : Nat.card K = 2 ^ (2 * a + 1)) (ha : 1 ≤ a)
    {l : Kˣ} (hl : ∀ m : Kˣ, m ∈ Subgroup.zpowers l) :
    Subgroup.closure ({suzukiSElt a K 0 1, suzukiWElt a K,
      suzukiDElt a K l * suzukiWElt a K * (suzukiDElt a K l)⁻¹} :
        Set ↥(suzukiGroup a K)) = ⊤ := by
  classical
  set H : Subgroup ↥(suzukiGroup a K) := Subgroup.closure
    ({suzukiSElt a K 0 1, suzukiWElt a K,
      suzukiDElt a K l * suzukiWElt a K * (suzukiDElt a K l)⁻¹} :
        Set ↥(suzukiGroup a K)) with hH
  have hx0 : suzukiSElt a K 0 1 ∈ H := Subgroup.subset_closure (by simp)
  have hW : suzukiWElt a K ∈ H := Subgroup.subset_closure (by simp)
  have hDc : suzukiDElt a K l * suzukiWElt a K * (suzukiDElt a K l)⁻¹ ∈ H :=
    Subgroup.subset_closure (by simp)
  have hD : suzukiDElt a K (l⁻¹ * l⁻¹) ∈ H := by
    have h1 : suzukiWElt a K * (suzukiDElt a K l * suzukiWElt a K * (suzukiDElt a K l)⁻¹) =
        suzukiDElt a K (l⁻¹ * l⁻¹) := by
      calc suzukiWElt a K * (suzukiDElt a K l * suzukiWElt a K * (suzukiDElt a K l)⁻¹)
          = (suzukiWElt a K * suzukiDElt a K l * suzukiWElt a K) *
              (suzukiDElt a K l)⁻¹ := by group
        _ = suzukiDElt a K l⁻¹ * (suzukiDElt a K l)⁻¹ := by rw [suzukiWElt_D_W hK l]
        _ = suzukiDElt a K (l⁻¹ * l⁻¹) := by rw [suzukiDElt_inv, suzukiDElt_mul]
    rw [← h1]
    exact H.mul_mem hW hDc
  have hT : suzukiT a K ≤ H :=
    suzukiT_le_of_mem_suzukiDElt_sq_inv hK hl hD
  have hTm : ∀ m : Kˣ, suzukiDElt a K m ∈ H := fun m =>
    hT (suzukiDElt_mem_suzukiT a K m)
  have hZ0 : suzukiZ0 a K ≤ H := by
    intro z hz
    obtain ⟨w, rfl⟩ := (mem_suzukiZ0_iff hK).1 hz
    by_cases hw : w = 0
    · rw [hw, suzukiSElt_zero_zero hK]
      exact H.one_mem
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, hbij, -⟩ :=
        suzuki_frobenius_exponents a K hK
      obtain ⟨μ, hμ⟩ := hbij.2 (Units.mk0 w hw)
      have hμK : (μ : K) ^ (2 ^ (a + 1) + 1) = w := by
        have h2 := congrArg Units.val hμ
        rw [Units.val_zpow_eq_zpow_val, Units.val_mk0] at h2
        have h3 : ((2 : ℤ) ^ (a + 1) + 1) = ((2 ^ (a + 1) + 1 : ℕ) : ℤ) := by
          push_cast
          ring
        rw [h3, zpow_natCast] at h2
        exact h2
      have hconj : suzukiDElt a K μ⁻¹ * suzukiSElt a K 0 1 * (suzukiDElt a K μ⁻¹)⁻¹ =
          suzukiSElt a K 0 w := by
        rw [suzukiDElt_conj' hK (μ⁻¹) 0 1, inv_inv, mul_zero, mul_one, hμK]
      rw [← hconj]
      exact H.mul_mem (H.mul_mem (hTm _) hx0) (H.inv_mem (hTm _))
  exact suzuki_eq_top_of_suzukiZ0_le_of_W_mem hK ha hZ0 hW

theorem exists_closure_three_conj_eq_top (hK : Nat.card K = 2 ^ (2 * a + 1)) (ha : 1 ≤ a)
    (x : ↥(suzukiGroup a K)) (hx : x * x = 1) (hx1 : x ≠ 1) :
    ∃ g₁ g₂ : ↥(suzukiGroup a K),
      Subgroup.closure ({x, g₁ * x * g₁⁻¹, g₂ * x * g₂⁻¹} :
        Set ↥(suzukiGroup a K)) = ⊤ := by
  obtain ⟨l, hl⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hD2 : (suzukiDElt a K l * suzukiWElt a K * (suzukiDElt a K l)⁻¹) *
      (suzukiDElt a K l * suzukiWElt a K * (suzukiDElt a K l)⁻¹) = 1 := by
    have e : (suzukiDElt a K l * suzukiWElt a K * (suzukiDElt a K l)⁻¹) *
        (suzukiDElt a K l * suzukiWElt a K * (suzukiDElt a K l)⁻¹) =
        suzukiDElt a K l * (suzukiWElt a K * suzukiWElt a K) *
          (suzukiDElt a K l)⁻¹ := by group
    rw [e, suzukiWElt_mul_self]
    group
  have hD1 : suzukiDElt a K l * suzukiWElt a K * (suzukiDElt a K l)⁻¹ ≠ 1 := by
    intro h
    apply suzukiWElt_ne_one (a := a) (K := K)
    have h2 := congrArg (fun z => (suzukiDElt a K l)⁻¹ * z * suzukiDElt a K l) h
    rw [show (suzukiDElt a K l)⁻¹ * (suzukiDElt a K l * suzukiWElt a K *
        (suzukiDElt a K l)⁻¹) * suzukiDElt a K l = suzukiWElt a K by group,
      show (suzukiDElt a K l)⁻¹ * 1 * suzukiDElt a K l = 1 by group] at h2
    exact h2
  exact exists_closure_three_conj_eq_top_of_closure hK
    (suzukiSElt_zero_one_sq hK) (suzukiSElt_zero_one_ne_one hK)
    (suzukiWElt_mul_self) (suzukiWElt_ne_one) hD2 hD1
    (suzuki_closure_three_involutions_eq_top hK ha hl) hx hx1

end CFSG.RankThree.GF2n.Tim81.Sec2
