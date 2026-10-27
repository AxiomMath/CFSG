module

public import CFSG.RankThree.PartOne.K133Spor.Perm11
public import CFSG.RankThree.PartOne.K133Spor.Bridge
public import CFSG.RankThree.PartOne.KS.Arith
public import CFSG.RankThree.PartOne.SPOR.OuterLy
public import CFSG.RankThree.PartTwo.Census.Sporadic.LyBridge

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms TauCeti
  CFSG.RankThree.PartOne.S13K
open CFSG.Sporadic.LySchreier (involution_centralizers_quasisimple)

theorem not_sq_dvd_card_Ly_aux {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hp5 : p ≠ 5) :
    ¬ p ^ 2 ∣ 51765179004000000 := by
  have hs : Nat.Coprime p (2 ^ 8 * 3 ^ 7 * 5 ^ 6) :=
    CFSG.RankThree.PartOne.coprime_two_three_five_pow hp hp3 hp5 8 7 6
  have hN : (51765179004000000 : ℕ) = (2 ^ 8 * 3 ^ 7 * 5 ^ 6) * 5917373 := by norm_num
  rw [hN]
  exact CFSG.RankThree.PartOne.not_sq_dvd_mul_of_coprime hp hs (B := 2432) (by norm_num)
    (by decide +kernel) (by norm_num)

theorem ly_not_four_dvd_card_centralizer_plane
    {T : Type} [Group T] [Finite T]
    (hT : Nonempty (T ≃* NativeSporadic.Ly)) {D : Subgroup T} (hD5 : ∀ g ∈ D, g ^ 5 = 1)
    (hDc : Nat.card D = 25) : ¬ 4 ∣ Nat.card (Subgroup.centralizer (D : Set T)) := by
  classical
  intro h4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨R0, hR0⟩ := Sylow.exists_subgroup_card_pow_prime (G := Subgroup.centralizer (D : Set T))
    2 (n := 2) (by simpa using h4)
  set R : Subgroup T := R0.map (Subgroup.centralizer (D : Set T)).subtype with hRdef
  have hRcard : Nat.card R = 2 ^ 2 := by
    rw [hRdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hR0]
  have hR2 : IsPGroup 2 R := IsPGroup.of_card hRcard
  have hRD : ∀ r ∈ R, ∀ d ∈ D, r * d = d * r := by
    rintro _ ⟨r, -, rfl⟩ d hd
    exact (Subgroup.mem_centralizer_iff.1 r.2 d hd).symm
  have hRnt : Nontrivial R := Finite.one_lt_card_iff_nontrivial.mp (by rw [hRcard]; norm_num)
  have hZnt : Nontrivial (Subgroup.center R) := hR2.center_nontrivial
  have hZ2 : IsPGroup 2 (Subgroup.center R) :=
    hR2.of_injective (Subgroup.center R).subtype (Subgroup.center R).subtype_injective
  have h2dvd : 2 ∣ Nat.card (Subgroup.center R) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hZ2
    have hn0 : n ≠ 0 := by
      rintro rfl
      have := Finite.one_lt_card_iff_nontrivial.mpr hZnt
      rw [hn] at this
      omega
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center R) 2 h2dvd
  set w : T := (((z : Subgroup.center R) : R) : T) with hwdef
  have hwR : w ∈ R := ((z : Subgroup.center R) : R).2
  have hw2 : orderOf w = 2 := by
    rw [hwdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hz
  have hwcomm : ∀ r ∈ R, r * w = w * r := by
    intro r hr
    have := Subgroup.mem_center_iff.mp z.2 ⟨r, hr⟩
    exact congrArg Subtype.val this
  set C : Subgroup T := Subgroup.centralizer ({w} : Set T) with hC
  have hRC : R ≤ C := fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (hwcomm r hr)
  have hDC : D ≤ C := fun d hd => Subgroup.mem_centralizer_singleton_iff.mpr (hRD w hwR d hd).symm
  obtain ⟨-, hcard2, ⟨φ⟩⟩ := involution_centralizers_quasisimple hT w hw2
  let ψ : ↥C →* ↥(alternatingGroup (Fin 11)) :=
    (φ : ↥C ⧸ Subgroup.center ↥C →* ↥(alternatingGroup (Fin 11))).comp
      (QuotientGroup.mk' (Subgroup.center ↥C))
  have hψker : ∀ x : ↥C, ψ x = 1 ↔ x ∈ Subgroup.center ↥C := by
    intro x
    change φ (x : ↥C ⧸ Subgroup.center ↥C) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  let θR : ↥R →* Equiv.Perm (Fin 11) :=
    (alternatingGroup (Fin 11)).subtype.comp (ψ.comp (Subgroup.inclusion hRC))
  let θD : ↥D →* Equiv.Perm (Fin 11) :=
    (alternatingGroup (Fin 11)).subtype.comp (ψ.comp (Subgroup.inclusion hDC))
  have hθDinj : Function.Injective θD := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have h1 : ψ (Subgroup.inclusion hDC d) = 1 := Subtype.ext hd
    have hcen : Subgroup.inclusion hDC d ∈ Subgroup.center ↥C := (hψker _).mp h1
    have h2 : (Subgroup.inclusion hDC d) ^ 2 = 1 := by
      have := pow_card_eq_one' (G := Subgroup.center ↥C) (x := ⟨_, hcen⟩)
      rw [hcard2] at this
      exact congrArg Subtype.val this
    have h2' : (d : T) ^ 2 = 1 := congrArg Subtype.val h2
    have h5 : (d : T) ^ 5 = 1 := hD5 d d.2
    have hd1 : (d : T) = 1 := by
      have e : (d : T) = (d : T) ^ 5 * ((d : T) ^ 2)⁻¹ ^ 2 := by
        have : ((d : T) ^ 2)⁻¹ ^ 2 = ((d : T) ^ 4)⁻¹ := by group
        rw [this]; group
      rw [e, h5, h2']; group
    exact Subtype.ext hd1
  have hDbarcard : Nat.card θD.range = 25 := by
    rw [← hDc]
    exact Nat.card_congr (MonoidHom.ofInjective hθDinj).symm.toEquiv
  have hDbar5 : ∀ g ∈ θD.range, g ^ 5 = 1 := by
    rintro _ ⟨d, rfl⟩
    rw [← map_pow]
    have : d ^ 5 = 1 := Subtype.ext (by simpa using hD5 d d.2)
    rw [this, map_one]
  have hkercard : Nat.card θR.ker ≤ 2 := by
    rw [← hcard2]
    refine Nat.card_le_card_of_injective
      (fun x => (⟨Subgroup.inclusion hRC (x : ↥R), (hψker _).mp (Subtype.ext (by
        have h1 : θR (x : ↥R) = 1 := x.2
        exact h1))⟩ : Subgroup.center ↥C)) ?_
    intro x y hxy
    apply Subtype.ext
    apply Subgroup.inclusion_injective hRC
    exact congrArg Subtype.val hxy
  have hrangecard : 2 ≤ Nat.card θR.range := by
    have hkr := Subgroup.card_ker_mul_card_range θR
    have hpos : 0 < Nat.card θR.ker := Nat.card_pos
    rw [hRcard] at hkr
    have hrpos : 0 < Nat.card θR.range := Nat.card_pos
    by_contra hlt
    have : Nat.card θR.range = 1 := by omega
    rw [this] at hkr
    omega
  have hRange2 : IsPGroup 2 θR.range :=
    hR2.of_surjective θR.rangeRestrict θR.rangeRestrict_surjective
  have h2range : 2 ∣ Nat.card θR.range := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hRange2
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      omega
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := θR.range) 2 h2range
  have hu2 : (u : Equiv.Perm (Fin 11)) ^ 2 = 1 := by
    have := pow_orderOf_eq_one u
    rw [hu] at this
    exact congrArg Subtype.val this
  have hu1 : (u : Equiv.Perm (Fin 11)) ≠ 1 := by
    intro h1
    have : u = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hu
    omega
  have huA : Equiv.Perm.sign (u : Equiv.Perm (Fin 11)) = 1 := by
    obtain ⟨_, ⟨r, rfl⟩⟩ := u
    exact Equiv.Perm.mem_alternatingGroup.mp (ψ (Subgroup.inclusion hRC r)).2
  have hcomm : ∀ g ∈ θD.range, (u : Equiv.Perm (Fin 11)) * g = g * (u : Equiv.Perm (Fin 11)) := by
    rintro _ ⟨d, rfl⟩
    obtain ⟨_, ⟨r, rfl⟩⟩ := u
    have hrd := hRD r r.2 d d.2
    have h1 : Subgroup.inclusion hRC r * Subgroup.inclusion hDC d =
        Subgroup.inclusion hDC d * Subgroup.inclusion hRC r := Subtype.ext hrd
    have h2 : ψ (Subgroup.inclusion hRC r) * ψ (Subgroup.inclusion hDC d) =
        ψ (Subgroup.inclusion hDC d) * ψ (Subgroup.inclusion hRC r) := by
      rw [← map_mul, ← map_mul, h1]
    exact congrArg Subtype.val h2
  exact CFSG.RankThree.PartOne.K133Spor.not_commute_plane hDbar5 hDbarcard hu2 hu1 huA hcomm

theorem goodRes_ly
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) (e : X ≃* NativeSporadic.Ly) {p : ℕ} (hp : p.Prime)
    (h5 : 5 ≤ p) : GoodRes p X := by
  have hout2 : Nat.card (Outer X) ∣ 2 :=
    (CFSG.RankThree.PartOne.SPOR.outer_order_divides_two' (T := X) ⟨e⟩).1
  by_cases hp5 : p = 5
  · subst hp5
    have hnd : ¬ 5 ∣ Nat.card (Outer X) := fun h => by
      have := Nat.le_of_dvd (by norm_num) (h.trans hout2)
      omega
    exact goodRes_of_centralizer_not_four_dvd hp hnab hnd fun D hD hDc =>
      ly_not_four_dvd_card_centralizer_plane ⟨e⟩ hD (by rw [hDc]; norm_num)
  · refine goodRes_of_not_sq_dvd ?_
    have hcardX : Nat.card X = 51765179004000000 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.Ly.card_Ly'
    exact CFSG.RankThree.PartOne.not_sq_dvd_card_mulAut_of_outer_le hnab (MulEquiv.refl X)
      (N := 51765179004000000) (k := 2) hcardX (Nat.le_of_dvd (by norm_num) hout2) hp
      (by omega) (not_sq_dvd_card_Ly_aux hp (by omega) hp5)

theorem kf133ResMaxAt_leaf6_ly
    (hTypes : ∀ r, 9 ≤ r → r ≤ 12 → KF132Types r) : KF133ResMaxAt (leaf6 .Ly) := by
  refine KF133ResMaxAt.of_goodRes hTypes fun X _ _ _ hne hX p hp h5 => ?_
  obtain ⟨e0⟩ := hX
  have : IsSimpleGroup SporadicName.Ly.Group := e0.symm.isSimpleGroup
  obtain ⟨e1⟩ := CFSG.RankThree.PartTwo.Census.nonempty_mulEquiv_Ly
  exact goodRes_ly hne (e0.trans e1) hp h5

end CFSG.RankThree.PartOne.K133
