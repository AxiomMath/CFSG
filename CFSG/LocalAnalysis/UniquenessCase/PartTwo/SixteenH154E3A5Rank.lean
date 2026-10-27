module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Frame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3A5RankA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightFix
public import CFSG.Quasithin.Background.F918Z8b
public import CFSG.Quasithin.Background.StabSubBasics

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem s16h_e3_altNat_map {T : Type} [CommGroup T] (x : MulAut T)
    {H : Subgroup (MulAut T)} {U : Subgroup T} {n : ℕ}
    (h : AlternatingNatural H U ⊥ n) :
    AlternatingNatural (H.map (MulAut.conj x).toMonoidHom) (U.map x.toMonoidHom) ⊥ n := by
  obtain ⟨π, hπ⟩ := h
  exact ⟨_, by
    simpa only [conjAutSub, Subgroup.map_bot] using d321b_realizes_map x hπ⟩

private theorem s16h_e3_sumOfNat_map {T : Type} [CommGroup T] (x : MulAut T)
    {N : Subgroup (MulAut T) → Subgroup T → Subgroup T → Prop}
    (hN : ∀ H U, N H U ⊥ →
      N (H.map (MulAut.conj x).toMonoidHom) (U.map x.toMonoidHom) ⊥)
    {H : Subgroup (MulAut T)} {U : Subgroup T} {k : ℕ}
    (h : SumOfNat N H U ⊥ k) :
    SumOfNat N (H.map (MulAut.conj x).toMonoidHom) (U.map x.toMonoidHom) ⊥ k := by
  obtain ⟨I, -, hind, hsup, hnat⟩ := h
  refine ⟨fun i => (I i).map x.toMonoidHom, fun i => bot_le, ?_, ?_,
    fun i => hN _ _ (hnat i)⟩
  · intro i
    have hle := Subgroup.map_mono (f := x.toMonoidHom) (hind i)
    rw [Subgroup.map_inf_eq _ _ x.toMonoidHom x.injective, Subgroup.map_sup,
      Subgroup.map_bot] at hle
    simp only [Subgroup.map_iSup x.toMonoidHom] at hle
    simpa using hle
  · have h := congrArg (fun V : Subgroup T => V.map x.toMonoidHom) hsup
    rwa [Subgroup.map_sup, Subgroup.map_bot, Subgroup.map_iSup x.toMonoidHom] at h

private theorem s16h_e3_card_sup_le_mul {W : Type} [CommGroup W] [Finite W] {A B : Subgroup W} :
    Nat.card ↥(A ⊔ B) ≤ Nat.card ↥A * Nat.card ↥B := by
  have h := card_sup_mul_card_inf A B
  calc Nat.card ↥(A ⊔ B) ≤ Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) :=
        Nat.le_mul_of_pos_right _ Nat.card_pos
    _ = Nat.card ↥A * Nat.card ↥B := h

private theorem s16h_e3_card_commSub_mono {W : Type} [CommGroup W] [Finite W]
    {A B : Subgroup W} {X : Subgroup (MulAut W)}
    (h : A ≤ B) : Nat.card ↥(commSub A X) ≤ Nat.card ↥(commSub B X) :=
  Nat.card_le_card_of_injective (Subgroup.inclusion (commSub_mono h le_rfl))
    (Subgroup.inclusion_injective _)

theorem s16h_e3_commSub_ge_eight_of_stab {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} {U : Subgroup W}
    {τ : MulAut W} (hL : IsAlt ↥L 5) (hexp : ∀ w : W, w ^ 2 = 1)
    (hsum : SumOfNat (fun H V Z => AlternatingNatural H V Z 5) L U ⊥ 3)
    (hLstabU : L ≤ stabSub U)
    (hstabU : τ ∈ stabSub U) (hstabL : ∀ l ∈ L, τ * l * τ⁻¹ ∈ L)
    (hnt : τ ∉ centSub U) :
    8 ≤ Nat.card ↥(commSub U (Subgroup.zpowers τ)) := by
  classical
  have hUL : U ⊓ fixV L = ⊥ :=
    s16e_inf_fixV_eq_bot_sumOfNat_alt (H := L) (U := U) (n := 5) (k := 3)
      (by norm_num) (by decide) hsum
  obtain ⟨I, -, hind, hUeq, hnat⟩ := hsum
  let S : Subgroup W := commSub U (Subgroup.zpowers τ)
  have hSU : S ≤ U := s16h_e3_commSub_zpowers_le_of_stab hstabU
  have hSne : S ≠ ⊥ := by
    intro hbot
    apply hnt
    rw [mem_centSub]
    intro u hu
    exact (mem_fixV.1 ((commSub_eq_bot_iff.1 hbot) hu)) τ (Subgroup.mem_zpowers τ)
  by_contra h8
  have hSle4 : Nat.card ↥S ≤ 4 := by
    have hpow : Nat.card ↥S = 2 ^ rk ↥S := card_eq_two_pow hexp S
    have hlt : 2 ^ rk ↥S < 8 := by rw [← hpow]; exact lt_of_not_ge h8
    have hrk : rk ↥S ≤ 2 := by
      by_contra hge
      have hge2 : 2 < rk ↥S := not_le.1 hge
      have hge3 : 3 ≤ rk ↥S := by omega
      have h1 : 2 ^ 3 ≤ 2 ^ rk ↥S := Nat.pow_le_pow_right (by norm_num) hge3
      norm_num at h1
      omega
    rw [hpow]
    calc 2 ^ rk ↥S ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hrk
      _ = 4 := by norm_num
  have hcomm : ∀ l ∈ L, τ * l = l * τ := by
    intro l hl
    let b : MulAut W := l * τ⁻¹ * l⁻¹
    let c : MulAut W := τ * l * τ⁻¹ * l⁻¹
    have hcL : c ∈ L := L.mul_mem (hstabL l hl) (L.inv_mem hl)
    have hbstab : b ∈ stabSub U :=
      (stabSub U).mul_mem ((stabSub U).mul_mem (hLstabU hl) ((stabSub U).inv_mem hstabU))
        ((stabSub U).inv_mem (hLstabU hl))
    have hceq : c = τ * b := by simp only [b, c]; group
    have hle : commSub U (Subgroup.zpowers c) ≤
        commSub U (Subgroup.zpowers τ) ⊔ commSub U (Subgroup.zpowers b) := by
      rw [hceq]
      exact s16h_e3_commSub_zpowers_mul_le hstabU hbstab
    have hbmap : commSub U (Subgroup.zpowers b) = S.map l.toMonoidHom := by
      have h1 : (commSub U (Subgroup.zpowers τ⁻¹)).map l.toMonoidHom =
          commSub U (Subgroup.zpowers b) := by
        rw [CFSG.RankThree.S4Free.Stell.map_commSub l U (Subgroup.zpowers τ⁻¹),
          MonoidHom.map_zpowers,
          CFSG.RankThree.S4Free.Stell.map_eq_self_of_mem_stabSub (hLstabU hl)]
        rfl
      rw [← h1, show S = commSub U (Subgroup.zpowers τ) from rfl, Subgroup.zpowers_inv]
    have hcardb : Nat.card ↥(commSub U (Subgroup.zpowers b)) = Nat.card ↥S := by
      rw [hbmap, Subgroup.card_map_of_injective (f := l.toMonoidHom) l.injective]
    have hbound : Nat.card ↥(commSub U (Subgroup.zpowers c)) ≤ 16 := by
      calc Nat.card ↥(commSub U (Subgroup.zpowers c))
          ≤ Nat.card ↥(commSub U (Subgroup.zpowers τ) ⊔
              commSub U (Subgroup.zpowers b)) :=
            Nat.card_le_card_of_injective (Subgroup.inclusion hle)
              (Subgroup.inclusion_injective hle)
        _ ≤ Nat.card ↥(commSub U (Subgroup.zpowers τ)) *
              Nat.card ↥(commSub U (Subgroup.zpowers b)) := s16h_e3_card_sup_le_mul
        _ = Nat.card ↥S * Nat.card ↥S := by rw [hcardb]
        _ ≤ 4 * 4 := Nat.mul_le_mul hSle4 hSle4
        _ = 16 := by norm_num
    have hc1 : c = 1 := by
      by_contra hcne
      have h64 := s16h_e3_commSub_sum_three_ge hind hnat hUeq hcL hcne
      omega
    have h1 : τ * l * τ⁻¹ = l := mul_inv_eq_one.mp hc1
    exact mul_inv_eq_iff_eq_mul.mp h1
  have hSinv : ∀ l ∈ L, ∀ s ∈ S, l s ∈ S := by
    intro l hl s hs
    have hs' : s ∈ U.map (CFSG.RankThree.S4Free.Stell.commMulHom τ) := by
      change s ∈ commSub U (Subgroup.zpowers τ) at hs
      rwa [show commSub U (Subgroup.zpowers τ) =
          U.map (CFSG.RankThree.S4Free.Stell.commMulHom τ) from
        CFSG.RankThree.S4Free.Stell.commSub_zpowers_eq_map_commMulHom hstabU] at hs
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hs'
    show l (CFSG.RankThree.S4Free.Stell.commMulHom τ u) ∈
      commSub U (Subgroup.zpowers τ)
    rw [show commSub U (Subgroup.zpowers τ) =
        U.map (CFSG.RankThree.S4Free.Stell.commMulHom τ) from
      CFSG.RankThree.S4Free.Stell.commSub_zpowers_eq_map_commMulHom hstabU]
    refine Subgroup.mem_map.mpr ⟨l u, (mem_stabSub.mp (hLstabU hl) u).mpr hu, ?_⟩
    show CFSG.RankThree.S4Free.Stell.commMulHom τ (l u) =
      l (CFSG.RankThree.S4Free.Stell.commMulHom τ u)
    rw [CFSG.RankThree.S4Free.Stell.commMulHom_apply,
      CFSG.RankThree.S4Free.Stell.commMulHom_apply, map_mul, map_inv]
    congr 1
    exact congrArg (fun f : MulAut W => f u) (hcomm l hl)
  have h8' := s16h_e3_invariant_ge_eight hL hexp hUL hSU hSne hSinv
  omega

theorem s16h_e3_a5_involution_rank {W : Type} [CommGroup W] [Finite W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W} (F : s16h_E3Frame X L L' T U U')
    (hL : IsAlt ↥L 5)
    (hsum : SumOfNat (fun H V Z => AlternatingNatural H V Z 5) L U ⊥ 3)
    {τ : MulAut W} (hτ : τ ∈ X) (h2 : τ ^ 2 = 1) (h1 : τ ≠ 1) :
    8 ≤ Nat.card ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers τ)) := by
  classical
  have hexp : ∀ w : W, w ^ 2 = 1 := F.exp2
  have hLstabU : L ≤ stabSub U := by
    rw [F.u_eq]
    intro l hl
    exact StabLat.mem_stabSub_commSub (by intro u; simp) (Subgroup.le_normalizer hl)
  have hL'stabU' : L' ≤ stabSub U' := by
    rw [F.u'_eq]
    intro l hl
    exact StabLat.mem_stabSub_commSub (by intro u; simp) (Subgroup.le_normalizer hl)
  rcases F.perm τ hτ with hfix | hswap
  · obtain ⟨hLfix, hL'fix, hUfix, hU'fix⟩ := hfix
    have hstabU : τ ∈ stabSub U := StabLat.mem_stabSub_of_map_eq hUfix
    have hstabU' : τ ∈ stabSub U' := StabLat.mem_stabSub_of_map_eq hU'fix
    have hstabL : ∀ l ∈ L, τ * l * τ⁻¹ ∈ L := by
      intro l hl
      have hmem : MulAut.conj τ l ∈ L := by
        rw [← hLfix]; exact Subgroup.mem_map_of_mem _ hl
      rwa [MulAut.conj_apply] at hmem
    have hstabL' : ∀ l ∈ L', τ * l * τ⁻¹ ∈ L' := by
      intro l hl
      have hmem : MulAut.conj τ l ∈ L' := by
        rw [← hL'fix]; exact Subgroup.mem_map_of_mem _ hl
      rwa [MulAut.conj_apply] at hmem
    by_cases hnt : τ ∈ centSub U
    · have hnt' : τ ∉ centSub U' := by
        intro hc'
        have hτ1 : τ = 1 := by
          ext w
          obtain ⟨u, hu, u', hu', rfl⟩ :=
            Subgroup.mem_sup.mp (by rw [F.sup_eq]; exact Subgroup.mem_top w)
          rw [map_mul, (mem_centSub.1 hnt) u hu, (mem_centSub.1 hc') u' hu']
          rfl
        exact h1 hτ1
      obtain ⟨t, htT, htL, htU⟩ := F.swap
      have hsum' : SumOfNat (fun H V Z => AlternatingNatural H V Z 5) L' U' ⊥ 3 := by
        have h := s16h_e3_sumOfNat_map t (fun _ _ hh => s16h_e3_altNat_map t hh) hsum
        rwa [htL, htU] at h
      have hL' : IsAlt ↥L' 5 := by
        have hm : IsAlt ↥(L.map (MulAut.conj t).toMonoidHom) 5 := by
          obtain ⟨e⟩ := hL
          exact ⟨(Subgroup.equivMapOfInjective L (MulAut.conj t).toMonoidHom
            (MulAut.conj t).injective).symm.trans e⟩
        rwa [htL] at hm
      have h8 := s16h_e3_commSub_ge_eight_of_stab hL' hexp hsum' hL'stabU'
        hstabU' hstabL' hnt'
      exact le_trans h8 (s16h_e3_card_commSub_mono (le_top : U' ≤ (⊤ : Subgroup W)))
    · have h8 := s16h_e3_commSub_ge_eight_of_stab hL hexp hsum hLstabU hstabU hstabL hnt
      exact le_trans h8 (s16h_e3_card_commSub_mono (le_top : U ≤ (⊤ : Subgroup W)))
  · obtain ⟨-, -, hUsw, -⟩ := hswap
    let φ : ↥U →* W := (CFSG.RankThree.S4Free.Stell.commMulHom τ).comp U.subtype
    have hφinj : Function.Injective φ := by
      rw [← MonoidHom.ker_eq_bot_iff φ, Subgroup.eq_bot_iff_forall]
      intro u hu
      have hu' : CFSG.RankThree.S4Free.Stell.commMulHom τ (u : W) = 1 :=
        MonoidHom.mem_ker.mp hu
      have htu : τ (u : W) = (u : W) := by
        rw [CFSG.RankThree.S4Free.Stell.commMulHom_apply] at hu'
        exact mul_inv_eq_one.mp hu'
      have hmemU' : (u : W) ∈ U' := by
        have h1 : τ (u : W) ∈ U' := by
          have h2 := Subgroup.mem_map_of_mem τ.toMonoidHom u.2
          rwa [hUsw] at h2
        rwa [htu] at h1
      have hbot : (u : W) ∈ (⊥ : Subgroup W) := by
        rw [← F.inf_eq]
        exact ⟨u.2, hmemU'⟩
      exact Subtype.ext (Subgroup.mem_bot.mp hbot)
    have hφmem : ∀ u : ↥U, φ u ∈ commSub ⊤ (Subgroup.zpowers τ) := by
      intro u
      exact Subgroup.subset_closure
        ⟨τ, Subgroup.mem_zpowers τ, (u : W), Subgroup.mem_top _, rfl⟩
    let ψ : ↥U →* ↥(commSub ⊤ (Subgroup.zpowers τ)) := φ.codRestrict _ hφmem
    have hψinj : Function.Injective ψ := by
      intro a b hab
      exact hφinj (congrArg Subtype.val hab)
    have hcard : Nat.card ↥U ≤ Nat.card ↥(commSub ⊤ (Subgroup.zpowers τ)) :=
      Nat.card_le_card_of_injective ψ hψinj
    obtain ⟨I, -, -, hUeq, hnat⟩ := hsum
    have hU8 : 8 ≤ Nat.card ↥U := by
      have hI0 : Nat.card ↥(I 0) = 16 := by
        have h := s16c1610_card_alternatingNatural_odd (H := L) (U := I 0) (n := 5)
          (by decide : Odd 5) (hnat 0)
        norm_num at h
        exact h
      have hle : I 0 ≤ U := by
        rw [← hUeq, bot_sup_eq]
        exact le_iSup I 0
      calc 8 ≤ Nat.card ↥(I 0) := by omega
        _ ≤ Nat.card ↥U := Nat.card_le_card_of_injective (Subgroup.inclusion hle)
            (Subgroup.inclusion_injective hle)
    exact le_trans hU8 hcard

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
