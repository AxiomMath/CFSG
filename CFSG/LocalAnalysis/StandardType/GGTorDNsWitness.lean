module

public import CFSG.LocalAnalysis.StandardType.GGTorDNsTorus
public import CFSG.LocalAnalysis.StandardType.GGTorDNsFrame
public import CFSG.LocalAnalysis.StandardType.GGTorusDWeyl
public import CFSG.LocalAnalysis.StandardType.GGRealKGOmegaFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddLayer
public import CFSG.RankThree.PartOne.S11d.OrthCaseH

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.TorDNs

open QuadraticMap CFSG.Open CFSG.RankThree.Classical2 CFSG.LocalAnalysis.GLTheoremA.S172C.Cent
  CFSG.StandardType.OmNsRootGen CFSG.StandardType.SpJoin CFSG.StandardType.TorC
  CFSG.StandardType.DScalarTorus CFSG.GroupTheory.WeirSylow Multiplicative

theorem simpleReflection_apply_of_lt {m N : ℕ} (hN : 4 ≤ N) {i : Fin N} (hi : i.val + 1 < N)
    (f : Fin N → Multiplicative (ZMod m)) :
    simpleReflection hN i f = fun j => f (Equiv.swap i ⟨i.val + 1, hi⟩ j) := by
  rw [simpleReflection, dite_eq_left hi, SpCoord.permAut_apply, Equiv.swap_inv]
  rfl

theorem simpleReflection_apply_of_not_lt {m N : ℕ} (hN : 4 ≤ N) {i : Fin N}
    (hi : ¬ i.val + 1 < N) (f : Fin N → Multiplicative (ZMod m)) :
    simpleReflection hN i f = fun j =>
      if j = ⟨N - 2, by omega⟩ then (f ⟨N - 1, by omega⟩)⁻¹
      else if j = ⟨N - 1, by omega⟩ then (f ⟨N - 2, by omega⟩)⁻¹ else f j := by
  have hab : (⟨N - 2, by omega⟩ : Fin N) ≠ ⟨N - 1, by omega⟩ :=
    Fin.ne_of_val_ne (by simp only; omega)
  funext j
  rw [simpleReflection, dite_eq_right hi]
  simp only [MulAut.mul_apply, SpCoord.sgnAut_apply, SpCoord.permAut_apply, Function.comp_apply,
    Equiv.swap_inv, Function.update_apply]
  by_cases h1 : j = ⟨N - 2, by omega⟩
  · subst j
    simp only [ite_true, ite_eq_right hab, Equiv.swap_apply_left]
  · by_cases h2 : j = ⟨N - 1, by omega⟩
    · subst j
      simp only [ite_true, ite_eq_right hab.symm, Equiv.swap_apply_right]
    · simp only [ite_eq_right h1, ite_eq_right h2, Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem simpleReflection_compLeft {m m' N : ℕ} (hN : 4 ≤ N)
    (h : Multiplicative (ZMod m) →* Multiplicative (ZMod m')) (i : Fin N)
    (f : Fin N → Multiplicative (ZMod m)) :
    h.compLeft (Fin N) (simpleReflection hN i f) =
      simpleReflection hN i (h.compLeft (Fin N) f) := by
  funext j
  by_cases hi : i.val + 1 < N
  · rw [simpleReflection_apply_of_lt hN hi, simpleReflection_apply_of_lt hN hi]
    rfl
  · rw [simpleReflection_apply_of_not_lt hN hi, simpleReflection_apply_of_not_lt hN hi]
    simp only [MonoidHom.compLeft_apply, Function.comp_apply]
    split_ifs <;> simp only [map_inv]

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

theorem exists_ggTorusTorWit_omega (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) {N : ℕ} (hdim : Module.finrank F V = 2 * N)
    (hN : 4 ≤ N) (htype : IsPlusType Q ↔ Even N) {E : Subgroup ↥(orthDerived Q)}
    (hE : IsElemAbelian p E)
    (hsc : ∀ g : ↥(orthDerived Q), (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) :
    ∃ w : GGTorusTorWit (Nat.card F + 1) N ↥(orthDerived Q) (scalarA E),
      w.Holds (CartanMatrix.D N) (ggCoxeterMatrixD N) ∧
      (∀ τ ∈ w.T, ∃ s ∈ w.Tsc, τ = MulAut.conj s) ∧ Odd (Nat.card w.Tsc) := by
  classical
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have h2q : 2 ∣ Nat.card F := by
    have := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact (CharP.cast_eq_zero_iff F 2 _).mp (FiniteField.cast_card_eq_zero F)
  have hm : Odd (Nat.card F + 1) := (even_iff_two_dvd.mpr h2q).add_one
  have : NeZero (Nat.card F + 1) := ⟨by omega⟩
  have hq1 : 1 ≤ Nat.card F := Nat.card_pos
  have hpq' : ¬ p ∣ Nat.card F - 1 := by
    intro h1
    have h3 : p ∣ (Nat.card F + 1) - (Nat.card F - 1) := Nat.dvd_sub hpq h1
    rw [show (Nat.card F + 1) - (Nat.card F - 1) = 2 by omega] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)
  have hcenter : Subgroup.center ↥(orthDerived Q) = ⊥ :=
    (CFSG.StandardType.OrthRestOdd.orthDerived_facts Q hQ (by omega)).2.1
  have hT3 := CFSG.RankThree.PartOne.exists_threeSingular_of_dim Q hQ hN hdim
  obtain ⟨U, e, u, c, t, hF, htop⟩ :=
    exists_spanningCoherentFrame hQ hp hp2 hpq hdim hN htype hE hsc
  have hirr := framePoly_irreducible hF hp hpq' ⟨0, by omega⟩
  have hgd := framePoly_dvd_cyclotomic hF hp hpq' ⟨0, by omega⟩
  obtain ⟨D, hD⟩ := exists_spTorusData_companion hp hp2 hpq hirr hgd
  have hDp : D.ζp (ofAdd 1) = spCompanion t := by
    rw [hD, spPlaneZetaCompanion, TableBSymp.zmodPowHom_apply, toAdd_ofAdd, ZMod.val_one,
      pow_one]
  obtain ⟨T, hTU⟩ := exists_fullTorus hQ hT3 hF hp hp2 hpq D hDp
  have hTinj : Function.Injective T := fullTorus_injective hF hp hpq' hTU
  obtain ⟨b₀, hb₀⟩ := D.mem_m (ofAdd 1)
  rw [hDp] at hb₀
  have hTe : ∀ a, T (Pi.mulSingle a b₀) = e a := fullTorus_mulSingle hF htop hTU hb₀
  have hb₀p : b₀ ^ p = 1 := by
    have h1 : T (Pi.mulSingle ⟨0, by omega⟩ (b₀ ^ p)) = 1 := by
      rw [Pi.mulSingle_pow, map_pow, hTe, ← hF.orderOf_eq ⟨0, by omega⟩, pow_orderOf_eq_one]
    have h2 := congrFun (hTinj (h1.trans (map_one T).symm)) ⟨0, by omega⟩
    simpa using h2
  obtain ⟨τ, hτinj, hτE, hτe, -⟩ := exists_frameTorus hF.toIsPlaneFrame hp
  subst hτE
  set ι : (Fin N → Multiplicative (ZMod p)) →*
      (Fin N → Multiplicative (ZMod (Nat.card F + 1))) :=
    (TableBSymp.zmodPowHom hb₀p).compLeft (Fin N) with hιdef
  have hτT : τ = T.comp ι := by
    refine SpCoord.hom_ext_mulSingle fun j => ?_
    have hι : ι (Pi.mulSingle j (ofAdd 1)) = Pi.mulSingle j b₀ := by
      funext i
      rw [hιdef, MonoidHom.compLeft_apply, Function.comp_apply]
      by_cases hij : i = j
      · subst hij
        rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same, TableBSymp.zmodPowHom_apply, toAdd_ofAdd,
          ZMod.val_one, pow_one]
      · rw [Pi.mulSingle_eq_of_ne hij, Pi.mulSingle_eq_of_ne hij, map_one]
    rw [hτe, MonoidHom.comp_apply, hι, hTe]
  obtain ⟨n, hnlt, hnfork⟩ : ∃ n : Fin N → ↥(orthDerived Q),
      (∀ i (hi : i.val + 1 < N), n i =
        ⟨frameSwap Q e u c t i ⟨i.val + 1, hi⟩, frameSwap_mem_orthDerived hQ hdim (by omega)⟩) ∧
      (∀ i, ¬ i.val + 1 < N → n i =
        ⟨signedSwap Q e u c t ⟨N - 2, by omega⟩ ⟨N - 1, by omega⟩,
          signedSwap_mem_orthDerived hQ hdim (by omega) hF⟩) :=
    ⟨fun i => if hi : i.val + 1 < N then
        ⟨frameSwap Q e u c t i ⟨i.val + 1, hi⟩, frameSwap_mem_orthDerived hQ hdim (by omega)⟩
      else ⟨signedSwap Q e u c t ⟨N - 2, by omega⟩ ⟨N - 1, by omega⟩,
          signedSwap_mem_orthDerived hQ hdim (by omega) hF⟩,
      fun i hi => dite_eq_left hi, fun i hi => dite_eq_right hi⟩
  have hnT : ∀ i f, n i * T f * (n i)⁻¹ = T (simpleReflection hN i f) := by
    intro i f
    by_cases hi : i.val + 1 < N
    · have hne : i ≠ ⟨i.val + 1, hi⟩ := Fin.ne_of_val_ne (by simp)
      rw [hnlt i hi, frameSwap_conj_torus hQ hdim (by omega) hF hp hpq' htop hTU hne f,
        simpleReflection_apply_of_lt hN hi]
    · have hne : (⟨N - 2, by omega⟩ : Fin N) ≠ ⟨N - 1, by omega⟩ :=
        Fin.ne_of_val_ne (by simp only; omega)
      rw [hnfork i hi, signedSwap_conj_torus hQ hdim (by omega) hF hp hpq' htop hTU hDp hne f,
        simpleReflection_apply_of_not_lt hN hi]
  have hnτ : ∀ i f, n i * τ f * (n i)⁻¹ = τ (simpleReflection hN i f) := by
    intro i f
    rw [hτT, MonoidHom.comp_apply, MonoidHom.comp_apply, hnT, hιdef, simpleReflection_compLeft]
  have hEτ : ∀ g, g ∈ τ.range ↔ g ^ p = 1 ∧ g ∈ T.range :=
    mem_iff_pow_eq_one_and_mem_range hF hp hpq' htop hTU hDp
  have hcentE : Subgroup.centralizer (τ.range : Set ↥(orthDerived Q)) ≤ T.range := by
    intro g hg
    refine mem_range_of_commute hF hp hpq' htop hTU hDp g fun j => ?_
    exact (Subgroup.mem_centralizer_iff.mp hg _ ⟨_, hτe j⟩).symm
  have hb01 : b₀ ≠ 1 := by
    intro h1
    have he1 : e (⟨0, by omega⟩ : Fin N) = 1 := by
      rw [← hTe, h1, Pi.mulSingle_one, map_one]
    have h := hF.orderOf_eq (⟨0, by omega⟩ : Fin N)
    rw [he1, orderOf_one] at h
    exact hp.ne_one h.symm
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨w, hw, -, -, -, hT, hTsc⟩ := exists_ggTorusTorWit_of_planeCoordinates
    hp2 hm hN (MulEquiv.refl _) T hTinj τ hτinj hEτ b₀ hb₀p hb01 n
    (fun i a => by rw [← simpleReflection_eq_mul_corTuple]; exact hnT i a) hnτ
    hcenter hcentE
    (fun _ _ _ hu => RealKGOmega.isSignedPerm_of_normalizer hQ hp hp2 hpq hT3 hF
      (by omega) hsc hτinj rfl hτe hu)
    (fun g i hi => RealKGOmega.not_induces_sgnAut hQ hp hpq' hF.toIsPlaneFrame htop hτe
      (hF.mem i) (by rw [hF.quad_eq i]; exact hF.c_ne_zero) g hi)
  exact ⟨w, hw, hT, hTsc⟩

end CFSG.StandardType.TorDNs

end
