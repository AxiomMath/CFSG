module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourCount
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A4Block
public import CFSG.Quasithin.EmptyFaithful.S14113Case
public import CFSG.Quasithin.EmptyFaithful.S146P2
public import CFSG.Quasithin.EmptyFaithful.S146P5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

theorem a3ConjCount_of_charTwo {G : Type} [Group G] [Finite G] {H X : Subgroup G}
    (hS : IsSQTKIn H) (hch : CharTwo H) (hX : IsBlock2 H X) (h3 : IsAltType X 3)
    {a b c : G} (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) :
    conjSub a X = conjSub b X ∨ conjSub a X = conjSub c X ∨ conjSub b X = conjSub c X := by
  by_contra hcon
  rw [not_or, not_or] at hcon
  obtain ⟨hAB, hAC, hBC⟩ := hcon
  have hblk : ∀ g ∈ H, IsBlock2 H (conjSub g X) := fun g hg => IsBlock2.conjByElt_of_mem hX hg
  have halt : ∀ g : G, IsAltType (conjSub g X) 3 := fun g =>
    L238.IsAltType.map_equiv h3 (MulAut.conj g)
  have hchi : ∀ g ∈ H, IsChiBlock H (conjSub g X) := fun g hg =>
    ⟨hblk g hg, Or.inr ⟨3, by decide, le_rfl, halt g⟩⟩
  exact L238.not_three_alt3 hch (hS.1 3 Nat.prime_three (by norm_num)) (hchi a ha) (hchi b hb)
    (hchi c hc) (halt a) (halt b) (halt c) hAB hAC hBC

theorem a3AutFive_proved : A3AutFive := by
  intro G _ _ X hs ha k hkN hk5
  have hA := DoubleA3.IsA4Block.of_alt3 hs ha
  obtain ⟨c, hcX, hc3, hcN, hcfp, hXc⟩ := hA.exists_c
  have hk5' : k ^ 5 = 1 := by rw [← hk5]; exact pow_orderOf_eq_one k
  have hkU : ∀ u ∈ blockU X, k * u * k⁻¹ ∈ blockU X := by
    intro u hu
    exact (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU hkN) u).mp hu
  have hkfix : ∀ u ∈ blockU X, k * u * k⁻¹ = u := by
    intro u hu
    let f : blockU X → blockU X := fun x => ⟨k * x * k⁻¹, hkU x x.2⟩
    have hf : ∀ n : ℕ, ∀ x : blockU X, ((f^[n] x : blockU X) : G) = k ^ n * x * (k ^ n)⁻¹ := by
      intro n
      induction n with
      | zero => intro x; simp
      | succ n ih =>
        intro x
        rw [Function.iterate_succ_apply']
        show k * ((f^[n] x : blockU X) : G) * k⁻¹ = _
        rw [ih x]
        simp only [pow_succ']
        group
    have hper : Function.IsPeriodicPt f 5 ⟨u, hu⟩ := by
      apply Subtype.ext
      show ((f^[5] ⟨u, hu⟩ : blockU X) : G) = u
      rw [hf, hk5']
      simp
    rcases (Nat.dvd_prime (by norm_num)).mp hper.minimalPeriod_dvd with h1 | h5
    · exact congrArg Subtype.val (Function.minimalPeriod_eq_one_iff_isFixedPt.mp h1)
    · exfalso
      have hinj : Set.InjOn (fun n => f^[n] ⟨u, hu⟩)
          (Set.Iio (Function.minimalPeriod f ⟨u, hu⟩)) :=
        Function.iterate_injOn_Iio_minimalPeriod
      rw [h5] at hinj
      have hcard : Nat.card (Fin 5) ≤ Nat.card (blockU X) := by
        refine Nat.card_le_card_of_injective (fun i : Fin 5 => f^[i.val] ⟨u, hu⟩) ?_
        intro i j hij
        exact Fin.ext (hinj i.2 j.2 hij)
      rw [Nat.card_fin, hA.card_U] at hcard
      omega
  have hkcentU : ∀ u ∈ blockU X, k * u = u * k := fun u hu =>
    mul_inv_eq_iff_eq_mul.mp (hkfix u hu)
  have hc'X : k * c * k⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hkN c).mp hcX
  have hdX : c⁻¹ * (k * c * k⁻¹) ∈ X := X.mul_mem (X.inv_mem hcX) hc'X
  have hdU : ∀ v ∈ blockU X, (c⁻¹ * (k * c * k⁻¹)) * v * (c⁻¹ * (k * c * k⁻¹))⁻¹ = v := by
    intro v hv
    have hv' : c * v * c⁻¹ ∈ blockU X := (Subgroup.mem_normalizer_iff.mp hcN v).mp hv
    have e1 : k⁻¹ * v * k = v := by
      have := hkcentU v hv
      calc k⁻¹ * v * k = k⁻¹ * (v * k) := by group
        _ = k⁻¹ * (k * v) := by rw [this]
        _ = v := by group
    calc (c⁻¹ * (k * c * k⁻¹)) * v * (c⁻¹ * (k * c * k⁻¹))⁻¹
        = c⁻¹ * (k * (c * (k⁻¹ * v * k) * c⁻¹) * k⁻¹) * c := by group
      _ = c⁻¹ * (k * (c * v * c⁻¹) * k⁻¹) * c := by rw [e1]
      _ = c⁻¹ * (c * v * c⁻¹) * c := by rw [hkfix _ hv']
      _ = v := by group
  have hUX : blockU X ≤ X := hA.le
  have hUcomm : ∀ u ∈ blockU X, ∀ v ∈ blockU X, u * v = v * u := hA.comm_U
  have hCU : X ⊓ Subgroup.centralizer (blockU X : Set G) = blockU X := by
    set Cx := X ⊓ Subgroup.centralizer (blockU X : Set G) with hCx
    have hUle : blockU X ≤ Cx := fun u hu =>
      ⟨hUX hu, Subgroup.mem_centralizer_iff.mpr fun v hv => hUcomm v hv u hu⟩
    have hd1 : Nat.card (blockU X) ∣ Nat.card Cx := Subgroup.card_dvd_of_le hUle
    have hd2 : Nat.card Cx ∣ Nat.card X := Subgroup.card_dvd_of_le inf_le_left
    rw [hA.card_U] at hd1
    rw [hA.card_L] at hd2
    have hle12 : Nat.card Cx ≤ 12 := Nat.le_of_dvd (by norm_num) hd2
    have hn : Nat.card Cx = 4 ∨ Nat.card Cx = 12 := by
      generalize Nat.card Cx = n at *
      interval_cases n <;> omega
    rcases hn with h4 | h12
    · exact (Subgroup.eq_of_le_of_card_ge hUle (by rw [h4, hA.card_U])).symm
    · exfalso
      have hCxX : Cx = X := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h12, hA.card_L])
      have hcC : c ∈ Cx := hCxX ▸ hcX
      have hcc := Subgroup.mem_centralizer_iff.mp hcC.2
      obtain ⟨v, hvU, hv1⟩ : ∃ v ∈ blockU X, v ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have : blockU X = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
        have h1 : Nat.card (blockU X) = 1 := by rw [this]; exact Subgroup.card_bot
        have h4 := hA.card_U
        omega
      apply hcfp v hvU hv1
      have := hcc v hvU
      calc c * v * c⁻¹ = (v * c) * c⁻¹ := by rw [← this]
        _ = v := by group
  have hdmem : c⁻¹ * (k * c * k⁻¹) ∈ blockU X := by
    rw [← hCU]
    refine ⟨hdX, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have := hdU v hv
    exact (mul_inv_eq_iff_eq_mul.mp this).symm
  have hc' : k * c * k⁻¹ = c * (c⁻¹ * (k * c * k⁻¹)) := by group
  have hkd : k * (c⁻¹ * (k * c * k⁻¹)) * k⁻¹ = c⁻¹ * (k * c * k⁻¹) := hkfix _ hdmem
  have hd2 : (c⁻¹ * (k * c * k⁻¹)) * (c⁻¹ * (k * c * k⁻¹)) = 1 := by
    have := hA.sq_U _ hdmem
    simpa [pow_two] using this
  have hkk : k * (k * c * k⁻¹) * k⁻¹ = c := by
    calc k * (k * c * k⁻¹) * k⁻¹
        = k * (c * (c⁻¹ * (k * c * k⁻¹))) * k⁻¹ := by rw [← hc']
      _ = (k * c * k⁻¹) * (k * (c⁻¹ * (k * c * k⁻¹)) * k⁻¹) := by group
      _ = (c * (c⁻¹ * (k * c * k⁻¹))) * (c⁻¹ * (k * c * k⁻¹)) := by rw [← hc', hkd]
      _ = c * ((c⁻¹ * (k * c * k⁻¹)) * (c⁻¹ * (k * c * k⁻¹))) := by group
      _ = c := by rw [hd2, mul_one]
  have hk2c : Commute (k * k) c := by
    have : k * k * c * (k * k)⁻¹ = c := by
      calc k * k * c * (k * k)⁻¹ = k * (k * c * k⁻¹) * k⁻¹ := by group
        _ = c := hkk
    exact (mul_inv_eq_iff_eq_mul.mp this)
  have hkc : Commute k c := by
    have hk : (k * k) ^ 3 = k := by
      calc (k * k) ^ 3 = k ^ 6 := by rw [← pow_two, ← pow_mul]
        _ = k ^ 5 * k := by rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ]
        _ = k := by rw [hk5', one_mul]
    have := hk2c.pow_left 3
    rwa [hk] at this
  have hXle : X ≤ Subgroup.centralizer ({k} : Set G) := by
    rw [hXc]
    refine sup_le (fun u hu => ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hkcentU u hu).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hkc.symm.eq
  exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hXle hx)

section Steps

variable {G : Type} [Group G] [Finite G] {H X Kz : Subgroup G}

theorem le_centralizer_of_a3_PC (hch : CharTwo H) (hA : A3AutFive)
    (hH : IsSQTKIn H) (hX : IsBlock2 H X) (h3 : IsAltType X 3) (hKH : Kz ≤ H)
    (hKz5 : Kz ≤ Subgroup.closure {x | x ∈ Kz ∧ orderOf x = 5}) :
    Kz ≤ Subgroup.centralizer (X : Set G) := by
  refine hKz5.trans ((Subgroup.closure_le _).mpr fun g hg => ?_)
  obtain ⟨hgK, hg5⟩ := hg
  have hgH : g ∈ H := hKH hgK
  have hg2H : g * g ∈ H := H.mul_mem hgH hgH
  have hnorm : g ∈ Subgroup.normalizer (X : Set G) := by
    by_contra hnn
    have hne : conjSub g X ≠ X := fun he => hnn (CosetGeom.mem_normalizer_of_conjSub_eq he)
    have h1 : conjSub (1 : G) X = X := conjSub_eq_of_mem_normalizer (Subgroup.one_mem _)
    have hmul : conjSub (g * g) X = conjSub g (conjSub g X) := conjSub_mul g g X
    rcases a3ConjCount_of_charTwo hH hch hX h3 H.one_mem hgH hg2H with hc | hc | hc
    · exact hne (by rw [h1] at hc; exact hc.symm)
    ·
      rw [h1, hmul] at hc
      apply hne
      have hg2 : g * g ∈ Subgroup.normalizer (X : Set G) := by
        have e : conjSub (g * g) X = X := by rw [hmul]; exact hc.symm
        exact CosetGeom.mem_normalizer_of_conjSub_eq e
      have hg6 : g = (g * g) ^ 3 := by
        have h5 : g ^ 5 = 1 := by rw [← hg5]; exact pow_orderOf_eq_one g
        calc g = g ^ 6 := by rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ', h5, mul_one]
          _ = (g * g) ^ 3 := by rw [← pow_two, ← pow_mul]
      have hgN : g ∈ Subgroup.normalizer (X : Set G) := by
        rw [hg6]
        exact (Subgroup.normalizer (X : Set G)).pow_mem hg2 3
      exact conjSub_eq_of_mem_normalizer hgN
    ·
      rw [hmul] at hc
      apply hne
      have key : ∀ Y : Subgroup G, conjSub g⁻¹ (conjSub g Y) = Y := fun Y =>
        conjSub_conjSub_inv g Y
      have := congrArg (conjSub g⁻¹) hc
      rw [key X, key (conjSub g X)] at this
      exact this.symm
  exact hA G X hX.1 h3 g hnorm hg5

end Steps

theorem input14615A3P_proved (iH : Input14615HypP) (iKz : Input14615KzP) : Input14615A3P := by
  intro G _ _ T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂ X hX h3
  obtain ⟨hHyp, hchar, -⟩ := iH G T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂
  obtain ⟨hKzG₂, hKz5, hNorm⟩ :=
    iKz G T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂
  have hXG₂ : IsBlock2 (g2_14615 K₂) X := isBlock2_of_oTwoFIn hX
  have hcent : conjClosure (oTwoUpper H) (mcOf T) ≤ Subgroup.centralizer (X : Set G) :=
    le_centralizer_of_a3_PC hchar a3AutFive_proved hHyp.sqtk hXG₂ h3 hKzG₂ hKz5
  intro x hx
  have hxG₂ : x ∈ g2_14615 K₂ := hXG₂.2.1 hx
  have hxC : x ∈ Subgroup.centralizer
      ((conjClosure (oTwoUpper H) (mcOf T) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp (hcent hk) x hx).symm
  exact ⟨hNorm (Subgroup.centralizer_le_normalizer _ hxC), hxG₂⟩

end CFSG.Quasithin
