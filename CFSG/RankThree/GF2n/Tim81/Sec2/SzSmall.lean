module

public import CFSG.Quasithin.Background.SmithB45SzNat

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open CFSG.Quasithin.B45Sz CFSG.QuasithinUnique.Setup.X7 CFSG.Blueprint Matrix
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.X7b

variable {a : ℕ} {K : Type} [Field K] [CharP K 2] [Fintype K]
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

@[expose] def IsSzNatural
    (ρ : Representation (ZMod 2) ↥(suzukiGroup a K) W) : Prop :=
  ∃ (c : ℕ) (φ : W ≃+ (Fin 4 → K)), ∀ g w,
    φ (ρ g w) =
      (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c)) *ᵥ φ w

theorem isSzNatural_of_finrank_eq_four
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (ρ : Representation (ZMod 2) ↥(suzukiGroup a K) W) [Fact ρ.IsIrreducible]
    (hnt : ∃ g, ρ g ≠ 1) (hdim : Module.finrank (EndRing ρ) W = 4) :
    IsSzNatural ρ := by
  classical
  let π : ↥(suzukiGroup a K) →* (W ≃ₗ[ZMod 2] W) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).toMonoidHom.comp ρ.toHomUnits
  have hπ : repOfG π = ρ := rfl
  haveI : Fact (repOfG π).IsIrreducible := ⟨by rw [hπ]; exact Fact.out⟩
  have hnt' : ∃ g, repOfG π g ≠ 1 := by simpa [hπ] using hnt
  obtain ⟨c, φ, hφ⟩ := sz_exists_natural_of_four hK π hnt' (by rw [hπ]; exact hdim)
  refine ⟨c, φ, fun g w => ?_⟩
  have hρ : (π g) w = ρ g w := by
    change repOfG π g w = ρ g w
    rw [hπ]
  rw [← hρ]
  exact hφ g w

private theorem dvd_of_shiftSet_card_two {f d : ℕ} (hfo : Odd f) {A : Finset ℕ}
    (hA : A ⊆ Finset.range (2 * f)) (hA2 : A.card = 2)
    (hshift : shiftSet f (2 * d) A = A) : f ∣ d := by
  classical
  have hfpos : 0 < f := hfo.pos
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hA2
  have hx : x ∈ ({x, y} : Finset ℕ) := by simp
  have hy : y ∈ ({x, y} : Finset ℕ) := by simp
  have hxlt : x < 2 * f := Finset.mem_range.mp (hA hx)
  have hylt : y < 2 * f := Finset.mem_range.mp (hA hy)
  have hmx : (x + 2 * d) % (2 * f) ∈ ({x, y} : Finset ℕ) := by
    rw [← hshift]
    exact Finset.mem_image_of_mem _ hx
  have hmy : (y + 2 * d) % (2 * f) ∈ ({x, y} : Finset ℕ) := by
    rw [← hshift]
    exact Finset.mem_image_of_mem _ hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmx hmy
  have hdvd : ∀ u : ℕ, u < 2 * f → (u + 2 * d) % (2 * f) = u → 2 * f ∣ 2 * d := by
    intro u hu hmod
    have hcong : u + 2 * d ≡ u + 0 [MOD 2 * f] := by
      unfold Nat.ModEq
      rw [hmod, add_zero, Nat.mod_eq_of_lt hu]
    exact Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_left_cancel' u hcong)
  have h4 : 2 * f ∣ 4 * d := by
    rcases hmx with hmid | hmid
    · exact (show 2 * d * 2 = 4 * d by ring) ▸ dvd_mul_of_dvd_left (hdvd x hxlt hmid) 2
    · rcases hmy with hmyx | hmyy
      · have hxy1 : x + 2 * d ≡ y [MOD 2 * f] := by
          unfold Nat.ModEq
          rw [hmid, Nat.mod_eq_of_lt hylt]
        have hyx1 : y + 2 * d ≡ x [MOD 2 * f] := by
          unfold Nat.ModEq
          rw [hmyx, Nat.mod_eq_of_lt hxlt]
        have hsum := hxy1.add hyx1
        have hsum' : x + y + 4 * d ≡ x + y [MOD 2 * f] := by
          rwa [show (x + 2 * d) + (y + 2 * d) = x + y + 4 * d by ring,
            show y + x = x + y by ring] at hsum
        exact Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_left_cancel' (x + y) hsum')
      · exact (show 2 * d * 2 = 4 * d by ring) ▸ dvd_mul_of_dvd_left (hdvd y hylt hmyy) 2
  have h2d : f ∣ 2 * d := by
    apply Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2)
    simpa [mul_assoc, mul_comm, mul_left_comm] using h4
  exact hfo.coprime_two_right.dvd_of_dvd_mul_right (by simpa [mul_comm] using h2d)

private theorem sixteen_mul_le_four_pow {m : ℕ} (hm : 3 ≤ m) : 16 * m ≤ 4 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have h64 : 64 ≤ 4 ^ m := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    rw [pow_succ]
    nlinarith

theorem isSzNatural_or_le_card
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (ρ : Representation (ZMod 2) ↥(suzukiGroup a K) W) [Fact ρ.IsIrreducible]
    (hnt : ∃ g, ρ g ≠ 1) :
    IsSzNatural ρ ∨ 2 ^ (16 * (2 * a + 1)) ≤ Nat.card W := by
  classical
  obtain ⟨d, hd1, hDcard, hdesc⟩ := sz_descent hK hnt
  obtain ⟨E, hEfield, hEfin, hEchar, ιK, ιD, A, hAne, hA, ⟨Φ⟩, hshift, hdimW⟩ :=
    hdesc (Module.finBasis (EndRing ρ) W)
  let _ : Field E := hEfield
  let _ : Finite E := hEfin
  have hWcard : Nat.card W = 2 ^ (d * 4 ^ A.card) := by
    rw [natCard_eq_pow_finrank (ρ := ρ), hDcard, hdimW, ← pow_mul]
  have hfin : Finite (EndRing ρ) := finite_endRing ρ
  have hApos : 0 < A.card := Finset.card_pos.mpr hAne
  have hm2 : A.card = 2 → 16 * (2 * a + 1) ≤ d * 4 ^ A.card := by
    intro h2
    have hfd : 2 * a + 1 ∣ d :=
      dvd_of_shiftSet_card_two ⟨a, by ring⟩
        (fun i hi => szOmega_subset (hA hi)) h2 hshift
    have hfle : 2 * a + 1 ≤ d := Nat.le_of_dvd hd1 hfd
    rw [h2]
    norm_num
    calc 16 * (2 * a + 1) ≤ 16 * d := Nat.mul_le_mul_left 16 hfle
      _ = d * 16 := by ring
  have hm3 : 3 ≤ A.card → 16 * (2 * a + 1) ≤ d * 4 ^ A.card := by
    intro hge
    have hfmd : 2 * a + 1 ≤ A.card * d :=
      le_card_mul_of_shiftSet hA hAne hd1 hshift
    have h4m : 16 * A.card ≤ 4 ^ A.card := sixteen_mul_le_four_pow hge
    calc 16 * (2 * a + 1) ≤ 16 * (A.card * d) := Nat.mul_le_mul_left 16 hfmd
      _ = d * (16 * A.card) := by ring
      _ ≤ d * 4 ^ A.card := Nat.mul_le_mul_left d h4m
  rcases lt_or_ge A.card 3 with hlt | hge
  · have h12 : A.card = 1 ∨ A.card = 2 := by omega
    rcases h12 with h1 | h2
    · left
      apply isSzNatural_of_finrank_eq_four hK ρ hnt
      rw [hdimW, h1]
      norm_num
    · right
      calc 2 ^ (16 * (2 * a + 1)) ≤ 2 ^ (d * 4 ^ A.card) :=
            Nat.pow_le_pow_right (by norm_num) (hm2 h2)
        _ = Nat.card W := hWcard.symm
  · right
    calc 2 ^ (16 * (2 * a + 1)) ≤ 2 ^ (d * 4 ^ A.card) :=
          Nat.pow_le_pow_right (by norm_num) (hm3 hge)
      _ = Nat.card W := hWcard.symm

section Generic

variable {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  {ρ : Representation (ZMod 2) G W} [Fact ρ.IsIrreducible]

theorem natCard_fix_pow_gen_subgroup {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W)
    {E : Type} [Field E] [Finite E] (ιD : EndRing ρ →+* E) {κ : Type} [Fintype κ]
    [DecidableEq κ] (R : G →* Matrix κ κ E)
    (Φ : (CFSG.QuasithinUnique.Setup.X7.matRep R).Equiv (matRepE b ιD)) (Z : Subgroup G) :
    Nat.card {w : W // ∀ z ∈ Z, ρ z w = w} ^
        (letI := ιD.toAlgebra; Module.finrank (EndRing ρ) E) =
      Nat.card {y : κ → E // ∀ z ∈ Z, (R z).mulVec y = y} := by
  classical
  let _ := ιD.toAlgebra
  have hcoord : ∀ (g : G) (w : W),
      (matRep b g).mulVec (b.equivFun.toEquiv w) = b.equivFun.toEquiv (ρ g w) := by
    intro g w
    change (matRep b g).mulVec (b.equivFun w) = b.equivFun (ρ g w)
    exact LinearMap.toMatrix_mulVec_repr b b (repD ρ g) w
  have h1 : {w : W // ∀ z ∈ Z, ρ z w = w} ≃
      {x : Fin m → EndRing ρ //
        ∀ z : Z, (matRep b (z : G) - 1).mulVec x = 0} :=
    Equiv.subtypeEquiv b.equivFun.toEquiv (fun w => by
      constructor
      · intro h z
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, hcoord, h (z : G) z.2, sub_self]
      · intro h z hz
        have := h ⟨z, hz⟩
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, hcoord, sub_eq_zero] at this
        exact b.equivFun.injective this)
  have h2 := natCard_common_ker_map ιD (fun z : Z => matRep b (z : G) - 1)
  have h3 : {x : Fin m → E // ∀ z : Z,
      ((matRep b (z : G) - 1).map ιD).mulVec x = 0} ≃
      {y : κ → E // ∀ z : Z, (R (z : G)).mulVec y = y} :=
    Equiv.subtypeEquiv Φ.symm.toLinearEquiv.toEquiv (fun x => by
      have hsub : ∀ z : Z,
          ((matRep b (z : G) - 1).map ιD).mulVec x =
            matRepE b ιD (z : G) x - x := by
        intro z
        rw [matRepE_apply, Matrix.map_sub _ (fun a b => map_sub ιD a b),
          Matrix.map_one ιD (map_zero ιD) (map_one ιD), Matrix.sub_mulVec, Matrix.one_mulVec]
      have hint : ∀ z : Z, Φ.symm (matRepE b ιD (z : G) x) =
          (R (z : G)).mulVec (Φ.symm x) := fun z => equiv_apply Φ.symm (z : G) x
      change (∀ z : Z, ((matRep b (z : G) - 1).map ιD).mulVec x = 0) ↔
        ∀ z : Z, (R (z : G)).mulVec (Φ.symm x) = Φ.symm x
      refine forall_congr' fun z => ?_
      rw [hsub z, ← hint z]
      constructor
      · intro h
        rw [sub_eq_zero.mp h]
      · intro h
        rw [sub_eq_zero]
        exact Φ.symm.toLinearEquiv.injective h)
  have h1' : Nat.card {w : W // ∀ z ∈ Z, ρ z w = w} =
      Nat.card {x : Fin m → EndRing ρ //
        ∀ z : Z, (matRep b (z : G) - 1).mulVec x = 0} :=
    Nat.card_congr h1
  have h3' : Nat.card {x : Fin m → E // ∀ z : Z,
      ((matRep b (z : G) - 1).map ιD).mulVec x = 0} =
      Nat.card {y : κ → E // ∀ z : Z, (R (z : G)).mulVec y = y} :=
    Nat.card_congr h3
  have hY : Nat.card {y : κ → E // ∀ z ∈ Z, (R z).mulVec y = y} =
      Nat.card {y : κ → E // ∀ z : Z, (R (z : G)).mulVec y = y} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun y => by
      constructor
      · intro h z
        exact h (z : G) z.2
      · intro h z hz
        exact h ⟨z, hz⟩)
  rw [h1', hY]
  rw [h3'] at h2
  exact h2.symm

theorem natCard_fixedSub_eq_pow_finrank {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W)
    {E : Type} [Field E] [Finite E] (ιD : EndRing ρ →+* E) {κ : Type} [Fintype κ]
    [DecidableEq κ] (R : G →* Matrix κ κ E)
    (Φ : (CFSG.QuasithinUnique.Setup.X7.matRep R).Equiv (matRepE b ιD)) (Z : Subgroup G) :
    Nat.card (fixedSub ρ Z) =
      Nat.card (EndRing ρ) ^ Module.finrank E (fixedSub (CFSG.QuasithinUnique.Setup.X7.matRep R) Z) := by
  classical
  let _ := ιD.toAlgebra
  let e : {y : κ → E // ∀ z ∈ Z, (R z).mulVec y = y} ≃
      ↥(fixedSub (CFSG.QuasithinUnique.Setup.X7.matRep R) Z) :=
    Equiv.subtypeEquivRight fun y => by
      constructor
      · intro h
        rw [mem_fixedSub]
        intro z hz
        rw [CFSG.QuasithinUnique.Setup.X7.matRep_apply, h z hz]
      · intro h z hz
        have := (mem_fixedSub.mp h) z hz
        rwa [CFSG.QuasithinUnique.Setup.X7.matRep_apply] at this
  have hE : Nat.card {y : κ → E // ∀ z ∈ Z, (R z).mulVec y = y} =
      Nat.card E ^ Module.finrank E
        (fixedSub (CFSG.QuasithinUnique.Setup.X7.matRep R) Z) := by
    rw [Nat.card_congr e]
    exact Module.natCard_eq_pow_finrank
  have he0 : 0 < Module.finrank (EndRing ρ) E := Module.finrank_pos
  have hcount := natCard_fix_pow_gen_subgroup b ιD R Φ Z
  have hD : Nat.card E = Nat.card (EndRing ρ) ^
      Module.finrank (EndRing ρ) E := natCard_E_eq ιD
  have hmain : Nat.card {w : W // ∀ z ∈ Z, ρ z w = w} ^
      Module.finrank (EndRing ρ) E =
      (Nat.card (EndRing ρ) ^ Module.finrank E
        (fixedSub (CFSG.QuasithinUnique.Setup.X7.matRep R) Z)) ^
        Module.finrank (EndRing ρ) E := by
    rw [hcount, hE, hD, ← pow_mul, ← pow_mul, mul_comm]
  have hfix : Nat.card (fixedSub ρ Z) =
      Nat.card {w : W // ∀ z ∈ Z, ρ z w = w} := rfl
  rw [hfix]
  exact Nat.pow_left_injective he0.ne' hmain

end Generic

section SzCount

variable {ρ : Representation (ZMod 2) ↥(suzukiGroup a K) W} [Fact ρ.IsIrreducible]

theorem natCard_fixedSub_sz_eq_pow_finrank
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (k : Type) [Field k] [Algebra K k] [Finite k]
    {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W) (ιD : EndRing ρ →+* k)
    {A : Finset ℕ}
    (Φ : (CFSG.QuasithinUnique.Setup.X7.matRep (szT k hK A)).Equiv (matRepE b ιD))
    (Z : Subgroup ↥(suzukiGroup a K)) :
    Nat.card (fixedSub ρ Z) =
      Nat.card (EndRing ρ) ^ Module.finrank k
        (fixedSub (CFSG.QuasithinUnique.Setup.X7.matRep (szT k hK A)) Z) :=
  natCard_fixedSub_eq_pow_finrank b ιD (szT k hK A) Φ Z

end SzCount

end CFSG.RankThree.GF2n.Tim81.Sec2
