module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res4ProofHeis

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank (StatedScalars)

namespace Res423Four

section Gen

variable {H : Type} [Group H]

theorem normalizerMonoidHom_eq_of_closure {A : Subgroup H} {S : Set H}
    (hA : A = Subgroup.closure S) {g w : H} (hg : g ∈ Subgroup.normalizer (A : Set H))
    (hw : w ∈ Subgroup.normalizer (A : Set H)) (h : ∀ x ∈ S, g * x * g⁻¹ = w * x * w⁻¹) :
    A.normalizerMonoidHom ⟨g, hg⟩ = A.normalizerMonoidHom ⟨w, hw⟩ := by
  have hle : A ≤ Subgroup.centralizer ({w⁻¹ * g} : Set H) := by
    rw [hA, Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have h1 := h x hx
    calc x * (w⁻¹ * g) = w⁻¹ * (w * x * w⁻¹) * g := by group
      _ = w⁻¹ * (g * x * g⁻¹) * g := by rw [h1]
      _ = w⁻¹ * g * x := by group
  refine MulEquiv.ext fun x => Subtype.ext ?_
  change g * (x : H) * g⁻¹ = w * x * w⁻¹
  have h2 := Subgroup.mem_centralizer_singleton_iff.mp (hle x.2)
  calc g * (x : H) * g⁻¹ = w * ((w⁻¹ * g) * x) * g⁻¹ := by group
    _ = w * (x * (w⁻¹ * g)) * g⁻¹ := by rw [← h2]
    _ = w * x * w⁻¹ := by group

end Gen

section Lifts

variable {H : Type} [Group H] {L : Subgroup H} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem lift_conj_eq {e : L ≃* slPi π 3 (p ^ f) K} {a b : H} (hbL : b ∈ L)
    {y : GL (Fin 3) K} (hy : IsPGLAt e a y) :
    y * (e ⟨b, hbL⟩ : GL (Fin 3) K) * y⁻¹ = e ⟨a * b * a⁻¹, hLn.conj_mem _ hbL a⟩ := by
  have h1 := hy.2 (e ⟨b, hbL⟩)
  rw [coe_slAct_eq] at h1
  simp only [MulEquiv.symm_apply_apply] at h1
  exact h1.symm

theorem mem_sup_centralizer_of_heis (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {e : L ≃* slPi π 3 (p ^ f) K} {v a h : H} (hvL : v ∈ L) {Y W : GL (Fin 3) K}
    (hY : IsPGLAt e a Y) (hW : IsPGLAt e h W) {ζ : Kˣ} (hζ1 : ζ ≠ 1)
    (hζ : Y * (e ⟨v, hvL⟩ : GL (Fin 3) K) * Y⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * (e ⟨v, hvL⟩ : GL (Fin 3) K))
    (hhv : h * v = v * h) (hha : h * a * h⁻¹ * a⁻¹ ∈ Subgroup.centralizer (L : Set H)) :
    h ∈ L ⊔ Subgroup.centralizer (L : Set H) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have h3 := hK.three_ne_zero hq
  set V := (e ⟨v, hvL⟩ : GL (Fin 3) K) with hVdef
  have hV : IsPGLAt e v V := isPGLAt_of_mem e hπ hvL
  have hWV : W * V = V * W := isPGLAt_commute_of_mem hvL hhv hW
  have hk : IsPGLAt e (h * a * h⁻¹ * a⁻¹) (W * Y * W⁻¹ * Y⁻¹) :=
    isPGLAt_mul e (isPGLAt_mul e (isPGLAt_mul e hW hY) (isPGLAt_inv hπ hW)) (isPGLAt_inv hπ hY)
  have hks := isPGLAt_inv_mul_mem hK hq (isPGLAt_of_mem_centralizer e hha) hk
  rw [inv_one, one_mul] at hks
  obtain ⟨ℓ, hℓ⟩ := hks
  have hWY : W * Y * W⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) ℓ * Y := by
    rw [hℓ]; group
  have hℓ3 : ℓ ^ 3 = 1 := pow_three_eq_one_of_conj_eq_scalar_mul hWY
  have hζ3 : ζ ^ 3 = 1 := pow_three_eq_one_of_conj_eq_scalar_mul hζ
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, ℓ = ζ ^ m := by
    have hζK : (ζ : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hζ3, Units.val_one]
    have hζK1 : (ζ : K) ≠ 1 := fun h => hζ1 (Units.ext h)
    have hℓK : (ℓ : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hℓ3, Units.val_one]
    rcases eq_one_or_eq_tau_or_eq_tau_sq hζK hζK1 hℓK with h | h | h
    · exact ⟨0, Units.ext (by rw [h, pow_zero, Units.val_one])⟩
    · exact ⟨1, Units.ext (by rw [h, pow_one])⟩
    · exact ⟨2, Units.ext (by rw [h, Units.val_pow_eq_pow_val])⟩
  set s := Matrix.GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ with hs
  have hsc : ∀ g : GL (Fin 3) K, g * s = s * g := fun g =>
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ⁻¹ g).eq
  have hVY : V * Y = s * Y * V := by
    have h1 : Y * V = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * V * Y := by
      rw [← hζ]; group
    have h2 : s * Matrix.GeneralLinearGroup.scalar (Fin 3) ζ = 1 := by
      rw [hs, ← map_mul, inv_mul_cancel, map_one]
    calc V * Y = s * (Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * V * Y) := by
          rw [← mul_assoc, ← mul_assoc, h2, one_mul]
      _ = s * Y * V := by rw [← h1, mul_assoc]
  have hVmY : V ^ m * Y = s ^ m * Y * V ^ m := by
    simpa using pow_mul_pow_heis hsc hVY m 1
  have hsm : s ^ m * Matrix.GeneralLinearGroup.scalar (Fin 3) (ζ ^ m) = 1 := by
    rw [hs, ← map_pow, ← map_mul, inv_pow, inv_mul_cancel, map_one]
  have hWY' : W * Y = Matrix.GeneralLinearGroup.scalar (Fin 3) (ζ ^ m) * Y * W := by
    rw [← hWY]; group
  have hsW : W * s ^ m = s ^ m * W := (Commute.pow_right (show Commute W s from hsc W) m).eq
  have hr1 : (W * V ^ m) * Y = Y * (W * V ^ m) := by
    calc (W * V ^ m) * Y = W * (V ^ m * Y) := by rw [mul_assoc]
      _ = W * (s ^ m * Y * V ^ m) := by rw [hVmY]
      _ = (W * s ^ m) * Y * V ^ m := by simp only [mul_assoc]
      _ = s ^ m * (W * Y) * V ^ m := by rw [hsW]; simp only [mul_assoc]
      _ = s ^ m * (Matrix.GeneralLinearGroup.scalar (Fin 3) (ζ ^ m) * Y * W) * V ^ m := by
          rw [hWY']
      _ = (s ^ m * Matrix.GeneralLinearGroup.scalar (Fin 3) (ζ ^ m)) * Y * (W * V ^ m) := by
          simp only [mul_assoc]
      _ = Y * (W * V ^ m) := by rw [hsm, one_mul]
  have hr2 : (W * V ^ m) * V = V * (W * V ^ m) := by
    calc (W * V ^ m) * V = W * (V * V ^ m) := by rw [mul_assoc, (Commute.self_pow V m).eq]
      _ = (W * V) * V ^ m := by rw [mul_assoc]
      _ = V * (W * V ^ m) := by rw [hWV, mul_assoc]
  have hsc' := mem_statedScalars_of_commute_heis h3 hζ1 hζ3 hζ hr1 hr2
  have hC := mem_centralizer_of_isPGLAt_scalar (isPGLAt_mul e hW (isPGLAt_pow hV m)) hsc'
  have hmem := mul_mem (Subgroup.mem_sup_right (S := L) hC)
    (Subgroup.mem_sup_left (T := Subgroup.centralizer (L : Set H)) (inv_mem (pow_mem hvL m)))
  rwa [mul_inv_cancel_right] at hmem

end Lifts

end Res423Four

open Res423Four

theorem k423SL3TypeThreeFrame_holds : K423SL3TypeThreeFrame := by
  intro H _ _ L hLn π p f K _ _ hK hq _ e A c hA hA27 hc3 hAc hpgl _ hdata
  obtain ⟨a, haA, -, u, v, huC, huL, hvL, hvC, -, hv3, hAinf, -, huac⟩ := hdata
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨hcL, -⟩ := mem_and_inf_centralizer_eq hK hq e hA hc3 hAc
  have hAe := hA.prop
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcAC : c ∈ A ⊓ Subgroup.centralizer (L : Set H) := hAc ▸ Subgroup.mem_zpowers c
  have hcA : c ∈ A := hcAC.1
  have hcC : c ∈ Subgroup.centralizer (L : Set H) := hcAC.2
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc3
    norm_num at hc3
  have hv3' : v ^ 3 = 1 := by rw [← hv3]; exact pow_orderOf_eq_one v
  have hLu : ∀ l ∈ L, l * u = u * l := fun l hl => Subgroup.mem_centralizer_iff.mp huC l hl
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl => Subgroup.mem_centralizer_iff.mp hcC l hl
  have huvA : u * v ∈ A := by
    have h1 : u * v ∈ Subgroup.closure ({c, u * v} : Set H) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    rw [← hAinf] at h1
    exact h1.1
  have hcu : c * u = u * c := hLu c hcL
  have hvu : v * u = u * v := hLu v hvL
  have hac : a * c = c * a := hAcomm a haA c hcA
  have hcv : v * c = c * v := hLc v hvL
  have hava : a * v * a⁻¹ = c * v := by
    have h1 : a * u⁻¹ * a⁻¹ = u⁻¹ * c := by rw [← huac]; group
    have h2 : a * (u * v) * a⁻¹ = u * v := by
      rw [hAcomm a haA _ huvA, mul_inv_cancel_right]
    calc a * v * a⁻¹ = (a * u⁻¹ * a⁻¹) * (a * (u * v) * a⁻¹) := by group
      _ = u⁻¹ * (c * u) * v := by rw [h1, h2]; group
      _ = c * v := by rw [hcu]; group
  have hav : a * v = c * v * a := by
    calc a * v = (a * v * a⁻¹) * a := by group
      _ = c * v * a := by rw [hava]
  have hvav : v * a * v⁻¹ = c⁻¹ * a := by
    have h1 : a * v * a⁻¹ * v⁻¹ = c := by rw [hava]; group
    calc v * a * v⁻¹ = (a * v * a⁻¹ * v⁻¹)⁻¹ * a := by group
      _ = c⁻¹ * a := by rw [h1]
  have hvav' : v⁻¹ * a * v⁻¹⁻¹ = c * a := by
    calc v⁻¹ * a * v⁻¹⁻¹ = v⁻¹ * (c * (c⁻¹ * a)) * v := by group
      _ = v⁻¹ * (c * (v * a * v⁻¹)) * v := by rw [hvav]
      _ = v⁻¹ * (c * v) * a := by group
      _ = v⁻¹ * (v * c) * a := by rw [hcv]
      _ = c * a := by group
  obtain ⟨Y, hY⟩ := hpgl a haA
  obtain ⟨ζ, hζC⟩ : (e ⟨c, hcL⟩ : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := by
    refine mem_statedScalars_of_commute hπ hq' hτ hτ1 fun x hx => ?_
    obtain ⟨l, hl⟩ := e.surjective ⟨x, hx⟩
    have h1 : (⟨c, hcL⟩ : L) * l = l * ⟨c, hcL⟩ := Subtype.ext (hLc l l.2).symm
    have h2 := congrArg (fun t : L => ((e t : slPi π 3 (p ^ f) K) : GL (Fin 3) K)) h1
    simp only [map_mul, Subgroup.coe_mul, hl] at h2
    exact h2
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    apply hc1
    have h1 : e ⟨c, hcL⟩ = 1 := Subtype.ext (by rw [← hζC, map_one, Subgroup.coe_one])
    exact congrArg Subtype.val (e.injective (h1.trans (map_one e).symm))
  have hYV : Y * (e ⟨v, hvL⟩ : GL (Fin 3) K) * Y⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * (e ⟨v, hvL⟩ : GL (Fin 3) K) := by
    rw [lift_conj_eq hvL hY]
    have h2 : (⟨a * v * a⁻¹, hLn.conj_mem _ hvL a⟩ : L) = ⟨c, hcL⟩ * ⟨v, hvL⟩ :=
      Subtype.ext hava
    rw [h2, map_mul, Subgroup.coe_mul, ← hζC]
  have hcentu : Subgroup.closure ({c, u * v} : Set H) ≤
      Subgroup.centralizer ({u} : Set H) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · rw [hx, SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact hcu
    · rw [Set.mem_singleton_iff.mp hx, SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      calc u * v * u = u * (v * u) := by rw [mul_assoc]
        _ = u * (u * v) := by rw [hvu]
  have haclos : a ∉ Subgroup.closure ({c, u * v} : Set H) := by
    intro h
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hcentu h)
    apply hc1
    rw [← huac, ← h1]
    group
  have haLC : a ∉ L ⊔ Subgroup.centralizer (L : Set H) := by
    intro h
    apply haclos
    rw [← hAinf]
    exact ⟨haA, h⟩
  have huvc : u * v ∉ Subgroup.zpowers c := by
    intro h
    apply hvC
    have h1 : u * v ∈ Subgroup.centralizer (L : Set H) := Subgroup.zpowers_le.mpr hcC h
    have h2 := mul_mem (inv_mem huC) h1
    rwa [inv_mul_cancel_left] at h2
  have h9 : Nat.card (Subgroup.closure ({c, u * v} : Set H)) = 9 :=
    Item424Proof.card_closure_pair_eq_nine hAe hA27 hcA huvA hc1 huvc
  have hAeq : A = Subgroup.closure ({c, u * v, a} : Set H) :=
    Item424Proof.eq_closure_triple hA27 hcA huvA haA h9 haclos
  have hAL : A ⊓ L = Subgroup.zpowers c := by
    have hle : Subgroup.zpowers c ≤ A ⊓ L := Subgroup.zpowers_le.mpr ⟨hcA, hcL⟩
    have hle2 : A ⊓ L ≤ Subgroup.closure ({c, u * v} : Set H) := by
      rw [← hAinf]
      exact inf_le_inf_left _ le_sup_left
    have hne : u * v ∉ A ⊓ L := by
      intro h
      apply huL
      have h1 := L.mul_mem (Subgroup.mem_inf.mp h).2 (L.inv_mem hvL)
      rwa [mul_inv_cancel_right] at h1
    have hd1 : Nat.card (A ⊓ L : Subgroup H) ∣ 9 := h9 ▸ Subgroup.card_dvd_of_le hle2
    have hd2 : 3 ∣ Nat.card (A ⊓ L : Subgroup H) := by
      have h1 := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_zpowers, hc3] at h1
    have hne9 : Nat.card (A ⊓ L : Subgroup H) ≠ 9 := by
      intro h
      apply hne
      rw [Subgroup.eq_of_le_of_card_ge hle2 (h9.trans h.symm).le]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have h3 : Nat.card (A ⊓ L : Subgroup H) = 3 := by
      obtain ⟨k, hk⟩ := hd2
      have hk3 : k ∣ 3 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3)
        (show 3 * k ∣ 3 * 3 by rw [← hk]; exact hd1)
      rcases (Nat.dvd_prime Nat.prime_three).mp hk3 with rfl | rfl
      · exact hk.trans (by norm_num)
      · exact absurd (hk.trans (by norm_num)) hne9
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h3, Nat.card_zpowers, hc3])).symm
  have hvN : v ∈ Subgroup.normalizer (A : Set H) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have hle : A ≤ A.comap (MulAut.conj v).toMonoidHom := by
      conv_lhs => rw [hAeq]
      rw [Subgroup.closure_le]
      intro y hy
      change v * y * v⁻¹ ∈ A
      rcases hy with hy | hy | hy
      · rw [hy, hcv, mul_inv_cancel_right]
        exact hcA
      · rw [hy]
        have h1 : v * (u * v) * v⁻¹ = u * v := by
          calc v * (u * v) * v⁻¹ = v * u := by group
            _ = u * v := hvu
        rw [h1]
        exact huvA
      · rw [Set.mem_singleton_iff.mp hy, hvav]
        exact mul_mem (inv_mem hcA) haA
    exact hle hx
  set σv : MulAut A := A.normalizerMonoidHom ⟨v, hvN⟩ with hσv
  have hσvIn : σv ∈ autIn L A := mem_autIn_iff.mpr ⟨v, hvN, hvL, rfl⟩
  have hσv3 : σv ^ 3 = 1 := by
    rw [hσv, ← map_pow]
    have h1 : (⟨v, hvN⟩ : Subgroup.normalizer (A : Set H)) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hv3')
    rw [h1, map_one]
  have hσv1 : σv ≠ 1 := by
    intro h
    have h1 := congrArg (fun φ : MulAut A => ((φ ⟨a, haA⟩ : A) : H)) h
    change v * a * v⁻¹ = a at h1
    rw [hvav] at h1
    apply hc1
    exact inv_eq_one.mp (mul_right_cancel (h1.trans (one_mul a).symm))
  have hσvord : orderOf σv = 3 := orderOf_eq_prime hσv3 hσv1
  have hsub : autIn L A ≤ Subgroup.zpowers σv := by
    intro σ hσ
    obtain ⟨g, hgN, hgL, rfl⟩ := mem_autIn_iff.mp hσ
    have hgA : ∀ x ∈ A, g * x * g⁻¹ ∈ A := fun x hx =>
      (Subgroup.mem_normalizer_iff.mp hgN x).mp hx
    have hgu : g * u = u * g := hLu g hgL
    have hgc : g * c = c * g := hLc g hgL
    have hga : g * a * g⁻¹ * a⁻¹ ∈ Subgroup.zpowers c := by
      rw [← hAL]
      refine Subgroup.mem_inf.mpr ⟨A.mul_mem (hgA a haA) (A.inv_mem haA), ?_⟩
      have e1 : g * a * g⁻¹ * a⁻¹ = g * (a * g⁻¹ * a⁻¹) := by group
      rw [e1]
      exact mul_mem hgL (hLn.conj_mem _ (inv_mem hgL) a)
    have hgv : g * v * g⁻¹ * v⁻¹ ∈ Subgroup.zpowers c := by
      rw [← hAL]
      have hwL : g * v * g⁻¹ * v⁻¹ ∈ L :=
        mul_mem (mul_mem (mul_mem hgL hvL) (inv_mem hgL)) (inv_mem hvL)
      refine Subgroup.mem_inf.mpr ⟨?_, hwL⟩
      have hwu := hLu _ hwL
      have e1 : g * v * g⁻¹ * v⁻¹ = (g * (u * v) * g⁻¹) * (u * v)⁻¹ := by
        calc g * v * g⁻¹ * v⁻¹ = (g * v * g⁻¹ * v⁻¹) * u * u⁻¹ := by group
          _ = u * (g * v * g⁻¹ * v⁻¹) * u⁻¹ := by rw [hwu]
          _ = (u * g) * v * g⁻¹ * v⁻¹ * u⁻¹ := by group
          _ = (g * u) * v * g⁻¹ * v⁻¹ * u⁻¹ := by rw [hgu]
          _ = (g * (u * v) * g⁻¹) * (u * v)⁻¹ := by group
      rw [e1]
      exact A.mul_mem (hgA _ huvA) (A.inv_mem huvA)
    have hcom : g * a * g⁻¹ * a⁻¹ ∈ Subgroup.centralizer (L : Set H) :=
      Subgroup.zpowers_le.mpr hcC hga
    have hgLC : ∀ x : H, g * x ∈ L ⊔ Subgroup.centralizer (L : Set H) →
        x ∈ L ⊔ Subgroup.centralizer (L : Set H) := fun x hx => by
      have h1 := mul_mem (Subgroup.mem_sup_left (inv_mem hgL)) hx
      rwa [inv_mul_cancel_left] at h1
    have hgW : IsPGLAt e g (e ⟨g, hgL⟩ : GL (Fin 3) K) := isPGLAt_of_mem e hπ hgL
    have hgv1 : g * v * g⁻¹ * v⁻¹ = 1 := by
      by_contra hne
      rcases eq_or_eq_inv_of_mem_zpowers hc3 hgv hne with h | h
      ·
        have hgv' : g * v = c * v * g := by
          calc g * v = (g * v * g⁻¹ * v⁻¹) * v * g := by group
            _ = c * v * g := by rw [h]
        have hca' : a⁻¹ * c = c * a⁻¹ := (Commute.inv_left (show Commute a c from hac)).eq
        have hgc' : g * c⁻¹ = c⁻¹ * g := (Commute.inv_right (show Commute g c from hgc)).eq
        have hav1 : a⁻¹ * v = c⁻¹ * v * a⁻¹ := by
          have h1 : v * a⁻¹ = c * a⁻¹ * v := by
            calc v * a⁻¹ = a⁻¹ * (a * v) * a⁻¹ := by group
              _ = a⁻¹ * (c * v * a) * a⁻¹ := by rw [hav]
              _ = (a⁻¹ * c) * v := by group
              _ = c * a⁻¹ * v := by rw [hca']
          calc a⁻¹ * v = c⁻¹ * (c * a⁻¹ * v) := by group
            _ = c⁻¹ * (v * a⁻¹) := by rw [h1]
            _ = c⁻¹ * v * a⁻¹ := by group
        have h1 : (g * a⁻¹) * v = v * (g * a⁻¹) := by
          calc g * a⁻¹ * v = g * (a⁻¹ * v) := by group
            _ = g * (c⁻¹ * v * a⁻¹) := by rw [hav1]
            _ = (g * c⁻¹) * v * a⁻¹ := by group
            _ = (c⁻¹ * g) * v * a⁻¹ := by rw [hgc']
            _ = c⁻¹ * (g * v) * a⁻¹ := by group
            _ = c⁻¹ * (c * v * g) * a⁻¹ := by rw [hgv']
            _ = v * (g * a⁻¹) := by group
        have h2 : (g * a⁻¹) * a * (g * a⁻¹)⁻¹ * a⁻¹ ∈ Subgroup.centralizer (L : Set H) := by
          have e1 : (g * a⁻¹) * a * (g * a⁻¹)⁻¹ * a⁻¹ = g * a * g⁻¹ * a⁻¹ := by group
          rw [e1]
          exact hcom
        have hk := mem_sup_centralizer_of_heis hK hq hvL hY
          (isPGLAt_mul e hgW (isPGLAt_inv hπ hY)) hζ1 hYV h1 h2
        have h3 := inv_mem (hgLC _ hk)
        rw [inv_inv] at h3
        exact haLC h3
      ·
        have hgv' : g * v = c⁻¹ * v * g := by
          calc g * v = (g * v * g⁻¹ * v⁻¹) * v * g := by group
            _ = c⁻¹ * v * g := by rw [h]
        have h1 : (g * a) * v = v * (g * a) := by
          calc g * a * v = g * (a * v) := by group
            _ = g * (c * v * a) := by rw [hav]
            _ = (g * c) * v * a := by group
            _ = (c * g) * v * a := by rw [hgc]
            _ = c * (g * v) * a := by group
            _ = c * (c⁻¹ * v * g) * a := by rw [hgv']
            _ = v * (g * a) := by group
        have h2 : (g * a) * a * (g * a)⁻¹ * a⁻¹ ∈ Subgroup.centralizer (L : Set H) := by
          have e1 : (g * a) * a * (g * a)⁻¹ * a⁻¹ = g * a * g⁻¹ * a⁻¹ := by group
          rw [e1]
          exact hcom
        have hk := mem_sup_centralizer_of_heis hK hq hvL hY (isPGLAt_mul e hgW hY) hζ1 hYV h1 h2
        exact haLC (hgLC _ hk)
    have hgvc : g * v = v * g := by
      calc g * v = (g * v * g⁻¹ * v⁻¹) * v * g := by group
        _ = v * g := by rw [hgv1, one_mul]
    have hfix : ∀ w ∈ L, w * v = v * w → w * c * w⁻¹ = c ∧ w * (u * v) * w⁻¹ = u * v := by
      intro w hwL hwv
      refine ⟨by rw [hLc w hwL, mul_inv_cancel_right], ?_⟩
      have hwu := hLu w hwL
      calc w * (u * v) * w⁻¹ = (w * u) * v * w⁻¹ := by group
        _ = u * (w * v) * w⁻¹ := by rw [hwu]; group
        _ = u * (v * w) * w⁻¹ := by rw [hwv]
        _ = u * v := by group
    have key : ∀ (w : H) (hw : w ∈ Subgroup.normalizer (A : Set H)), w ∈ L → w * v = v * w →
        g * a * g⁻¹ = w * a * w⁻¹ →
        A.normalizerMonoidHom ⟨g, hgN⟩ = A.normalizerMonoidHom ⟨w, hw⟩ := by
      intro w hw hwL hwv hgaw
      refine normalizerMonoidHom_eq_of_closure hAeq hgN hw fun x hx => ?_
      rcases hx with hx | hx | hx
      · rw [hx, (hfix g hgL hgvc).1, (hfix w hwL hwv).1]
      · rw [hx, (hfix g hgL hgvc).2, (hfix w hwL hwv).2]
      · rw [Set.mem_singleton_iff.mp hx]
        exact hgaw
    have hga' : ∀ k : H, g * a * g⁻¹ * a⁻¹ = k → g * a * g⁻¹ = k * a := fun k hk => by
      rw [← hk]; group
    by_cases h1 : g * a * g⁻¹ * a⁻¹ = 1
    · have h2 := key 1 (Subgroup.one_mem _) (Subgroup.one_mem _) (by rw [one_mul, mul_one])
        (by rw [hga' 1 h1]; group)
      rw [h2]
      change A.normalizerMonoidHom 1 ∈ _
      rw [map_one]
      exact Subgroup.one_mem _
    · rcases eq_or_eq_inv_of_mem_zpowers hc3 hga h1 with h | h
      · have h2 := key v⁻¹ (inv_mem hvN) (inv_mem hvL)
          (by rw [inv_mul_cancel, mul_inv_cancel]) (by rw [hga' c h, hvav'])
        rw [h2]
        change A.normalizerMonoidHom (⟨v, hvN⟩⁻¹) ∈ _
        rw [map_inv]
        exact inv_mem (Subgroup.mem_zpowers σv)
      · have h2 := key v hvN hvL rfl (by rw [hga' c⁻¹ h, hvav])
        rw [h2]
        exact Subgroup.mem_zpowers σv
  have hAut : autIn L A = Subgroup.zpowers σv :=
    le_antisymm hsub (Subgroup.zpowers_le.mpr hσvIn)
  have hcard : Nat.card (autIn L A) = 3 := by rw [hAut, Nat.card_zpowers, hσvord]
  have hZ3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  exact ⟨mulEquivOfPrimeCardEq hcard hZ3⟩

end CFSG.RankThree.PartTwo.Sec4
