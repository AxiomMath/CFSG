module

public import CFSG.RankThree.PartTwo.Sec13.K135SFComponent
public import CFSG.RankThree.PartTwo.Sec13.K135SFCritical
public import CFSG.RankThree.PartTwo.Sec13.K135SFLift
public import CFSG.RankThree.PartTwo.Sec13.K135SFHH
public import CFSG.GroupTheory.BaerSuzuki.Helpers

public section

namespace CFSG.RankThree.PartTwo.Sec13.K135SF

open CFSG
open CFSG.Assembly.RankThreeEven (localRank)
open scoped commutatorElement

private theorem orderOf_map_eq_two_of_odd_ker {G H : Type*} [Group G] [Finite G] [Group H]
    (φ : G →* H) (hker : Odd (Nat.card φ.ker)) {x : G} (hx : orderOf x = 2) : orderOf (φ x) = 2 := by
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have h1 : φ x ≠ 1 := by
    intro h
    have hmem : x ∈ φ.ker := h
    have : orderOf (⟨x, hmem⟩ : φ.ker) ∣ Nat.card φ.ker := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hx] at this
    exact (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hker this)) even_two
  exact orderOf_eq_prime (by rw [← map_pow, hx2, map_one]) h1

theorem sf2_holds : SF2Statement := by
  intro M _ _ hloc R _ hRodd X _ S _ _ hS hSn π hπ hodd hnot
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N₀ : Subgroup M := (CFSG.pPrimeCore 3 R).map R.subtype with hN₀def
  haveI hN₀n : N₀.Normal := normal_map_pPrimeCore R 3
  have hN₀R : N₀ ≤ R := Subgroup.map_subtype_le _
  have hN₀3 : ¬ 3 ∣ Nat.card N₀ := by
    rw [hN₀def, Subgroup.card_map_of_injective R.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hN₀odd : Odd (Nat.card N₀) := Odd.of_dvd_nat hRodd (Subgroup.card_dvd_of_le hN₀R)
  have hN₀2 : ¬ 2 ∣ Nat.card N₀ := fun h =>
    (Nat.not_even_iff_odd.mpr hN₀odd) (even_iff_two_dvd.mpr h)
  let q : M →* M ⧸ N₀ := QuotientGroup.mk' N₀
  have hqker : q.ker = N₀ := QuotientGroup.ker_mk' N₀
  set R₁ : Subgroup (M ⧸ N₀) := R.map q with hR₁def
  haveI hR₁n : R₁.Normal := Subgroup.Normal.map ‹R.Normal› q (QuotientGroup.mk'_surjective N₀)
  have hcore : CFSG.pPrimeCore 3 R₁ = ⊥ := pPrimeCore_map_quotient_eq_bot R N₀ rfl
  have hRsolv : Group.IsSolvable R := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hRodd
  have hsolv : Group.IsSolvable R₁ :=
    Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective q R)
  set Q : Subgroup (M ⧸ N₀) := (CFSG.pCore 3 R₁).map R₁.subtype with hQdef
  haveI hQchar : (CFSG.pCore 3 R₁).Characteristic := CFSG.BaerSuzuki.Helpers.pCore_characteristic 3
  haveI hQn : Q.Normal := normal_map_of_characteristic R₁ (CFSG.pCore 3 R₁)
  have hQp : IsPGroup 3 Q := (CFSG.BaerSuzuki.Helpers.pCore_isPGroup (G := R₁) 3).map R₁.subtype
  have hQR : Q ≤ R₁ := Subgroup.map_subtype_le _
  set Xb : Subgroup (M ⧸ N₀) := X.map q with hXbdef
  haveI : Group.IsPerfect Xb := Group.IsPerfect.map q
  let φ : X →* Xb := q.subgroupMap X
  have hφs : Function.Surjective φ := MonoidHom.subgroupMap_surjective q X
  have hφker : Odd (Nat.card φ.ker) := by
    let ι : φ.ker →* N₀ := (X.subtype.comp φ.ker.subtype).codRestrict N₀ (fun y => by
      have hy : φ y.1 = 1 := y.2
      have : q (y.1 : M) = 1 := congrArg Subtype.val hy
      exact (QuotientGroup.eq_one_iff _).mp this)
    have hι : Function.Injective ι := fun a b hab => by
      have h1 : ((ι a : N₀) : M) = ((ι b : N₀) : M) := congrArg Subtype.val hab
      have h2 : (((a : φ.ker) : X) : M) = (((b : φ.ker) : X) : M) := h1
      exact Subtype.ext (Subtype.ext h2)
    exact Odd.of_dvd_nat hN₀odd (Subgroup.card_dvd_of_injective ι hι)
  have hact : ¬ Xb ≤ Subgroup.centralizer (Q : Set (M ⧸ N₀)) := by
    intro hle
    have h1 : ⁅R₁, Xb⁆ = ⊥ := commutator_eq_bot_of_centralizes_pCore R₁ hsolv hcore Xb hle
    apply hnot
    have h2 : (⁅R, X⁆).map q = ⊥ := by
      rw [Subgroup.map_commutator]
      exact h1
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h2
  have hrank : ∀ t ∈ Xb, orderOf t = 2 →
      CFSG.Open.pRank 3 (Q ⊓ Subgroup.centralizer {t}) ≤ 3 := by
    intro t ht ht2
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ht
    have hker : Odd (Nat.card q.ker) := by rw [hqker]; exact hN₀odd
    obtain ⟨g, hg, hg2⟩ := exists_involution_lift_of_odd_ker q hker (x := x) ht2
    have h1 := pRank_fixed_quotient_le N₀ hN₀3 hN₀2 R hN₀R g hg2 hloc
    rw [hg] at h1
    exact (CFSG.SectionRank.pRank_mono (by norm_num) (inf_le_inf_right _ hQR)).trans h1
  obtain ⟨a, b, ha2, hb2, hab, hne⟩ :=
    exists_commuting_involutions_of_surjective hS hSn π hπ hodd
  have hφa : orderOf (φ a) = 2 := orderOf_map_eq_two_of_odd_ker φ hφker ha2
  have hφb : orderOf (φ b) = 2 := orderOf_map_eq_two_of_odd_ker φ hφker hb2
  have hφne : φ a ≠ φ b := by
    intro h
    have hab' : a * b ≠ 1 := fun h1 => hne (by
      have ha1 : a * a = 1 := by rw [← sq]; rw [← ha2]; exact pow_orderOf_eq_one a
      calc a = a * (b * b) := by
            rw [show b * b = 1 by rw [← sq]; rw [← hb2]; exact pow_orderOf_eq_one b, mul_one]
        _ = (a * b) * b := by rw [mul_assoc]
        _ = b := by rw [h1, one_mul])
    have hord : orderOf (a * b) = 2 := by
      refine orderOf_eq_prime ?_ hab'
      have hx : Commute a b := hab
      have ha1 : a ^ 2 = 1 := by rw [← ha2]; exact pow_orderOf_eq_one a
      have hb1 : b ^ 2 = 1 := by rw [← hb2]; exact pow_orderOf_eq_one b
      rw [hx.mul_pow, ha1, hb1, one_mul]
    have hmem : a⁻¹ * b ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    have hainv : a⁻¹ = a := by
      have ha1 : a * a = 1 := by rw [← sq, ← ha2]; exact pow_orderOf_eq_one a
      exact inv_eq_of_mul_eq_one_right ha1
    rw [hainv] at hmem
    have : orderOf (⟨a * b, hmem⟩ : φ.ker) ∣ Nat.card φ.ker := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hord] at this
    exact (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hφker this)) even_two
  obtain ⟨n, ρ, hn12, hρ1, hρfix⟩ := sf2_core Q hQp Xb hact hrank
    ((φ a : Xb) : M ⧸ N₀) ((φ b : Xb) : M ⧸ N₀) (φ a).2 (φ b).2
    (by rw [Subgroup.orderOf_coe]; exact hφa) (by rw [Subgroup.orderOf_coe]; exact hφb)
    (by rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hab])
    (fun h => hφne (Subtype.ext h))
  set ρX : X →* Matrix.GeneralLinearGroup (Fin n) (ZMod 3) := ρ.comp φ with hρX
  have hρX1 : ρX ≠ 1 := by
    intro h
    refine hρ1 (MonoidHom.ext fun y => ?_)
    obtain ⟨x, rfl⟩ := hφs y
    have := DFunLike.congr_fun h x
    simpa [hρX] using this
  haveI hπsolv : Group.IsSolvable π.ker := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hkerle : ρX.ker ≤ π.ker := ker_le_of_perfect_solvable_kernel hS π hπ hπsolv ρX hρX1
  refine ⟨n, X, inferInstance, inferInstance, ρX, π.ker, inferInstance, hn12, inferInstance, hρX1,
    hkerle, hodd, ⟨QuotientGroup.quotientKerEquivOfSurjective π hπ⟩, ?_⟩
  intro t ht
  have := hρfix (φ t) (orderOf_map_eq_two_of_odd_ker φ hφker ht |>.symm ▸ rfl)
  simpa [hρX] using this

end CFSG.RankThree.PartTwo.Sec13.K135SF
