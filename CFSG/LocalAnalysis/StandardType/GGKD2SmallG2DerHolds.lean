module

public import CFSG.LocalAnalysis.StandardType.GGKD2SmallPieces1615
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestSmall
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoLayer
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestG2
public import CFSG.LocalAnalysis.StandardType.GGLayerCycModelOmegaInnerSU33
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineGroups

public section

namespace CFSG.StandardType.KD2Pieces1615

open CFSG CFSG.Assembly CFSG.StandardType S2MathAs3_1615

open CFSG.Quasithin.G2U

open CFSG.StandardType.LayerCyc

private theorem ltrke3_perfect_commutative_bot {G : Type*} [Group G]
    (hperf : commutator G = ⊤) (hcomm : ∀ x y : G, x * y = y * x) : Subsingleton G := by
  have hbot : commutator G = ⊥ := by
    rw [commutator_def]
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun x _ => ?_
    rw [Subgroup.mem_centralizer_iff]
    exact fun y _ => (hcomm x y).symm
  have htopbot : (⊤ : Subgroup G) = ⊥ := by rw [← hperf]; exact hbot
  refine ⟨fun a b => ?_⟩
  have ha : a ∈ (⊥ : Subgroup G) := htopbot ▸ Subgroup.mem_top a
  have hb : b ∈ (⊥ : Subgroup G) := htopbot ▸ Subgroup.mem_top b
  rw [Subgroup.mem_bot] at ha hb
  rw [ha, hb]

private theorem ltrke3_su3_centralizer_solvable {u : CFSG.Open.StatedSU 3 3 F9}
    (hu1 : u ≠ 1) (hu3 : u ^ 3 = 1) :
    Group.IsSolvable (Subgroup.centralizer ({u} : Set (CFSG.Open.StatedSU 3 3 F9))) := by
  have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  refine isSolvable_centralizer_of_forall_not_commute fun x hxp hx3 => ?_
  exact ggSU33ThreeCentInput_holds u x hord hxp hx3

private theorem ltrke3_conj_eq_one_iff {R : Type*} [Group R] (hZ : Subgroup.center R = ⊥)
    {u : R} (hu : MulAut.conj u = 1) : u = 1 := by
  have hmem : u ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h := congrArg (fun f : MulAut R => f x) hu
    rw [MulAut.conj_apply] at h
    have h2 : u * x = x * u := by
      have := congrArg (fun z : R => z * u) h
      simpa [mul_assoc] using this
    exact h2.symm
  rwa [hZ, Subgroup.mem_bot] at hmem

private theorem ltrke3_g2der_nonabelian
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    ∃ x y : LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true), x * y ≠ y * x := by
  obtain ⟨e⟩ := TableBExcSmallRest.nonempty_g2der_equiv_su3 K hK
  refine ⟨e.symm ⟨TableBExcSmallRest.su3X, TableBExcSmallRest.su3X_mem⟩,
    e.symm ⟨TableBExcSmallRest.su3Y, TableBExcSmallRest.su3Y_mem⟩, ?_⟩
  intro h
  refine TableBExcSmallRest.su3X_mul_su3Y_ne ?_
  have h' : ((⟨TableBExcSmallRest.su3X, TableBExcSmallRest.su3X_mem⟩ :
        CFSG.Open.StatedSU 3 3 F9) *
      ⟨TableBExcSmallRest.su3Y, TableBExcSmallRest.su3Y_mem⟩) =
      (⟨TableBExcSmallRest.su3Y, TableBExcSmallRest.su3Y_mem⟩ *
      ⟨TableBExcSmallRest.su3X, TableBExcSmallRest.su3X_mem⟩) := by
    have hh := congrArg e h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using hh
  simpa using congrArg (fun z : CFSG.Open.StatedSU 3 3 F9 => (z : GL (Fin 3) F9)) h'

theorem smallG2Der_holds :
    SmallG2Der := by
  intro lab hlab htag
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeG2Derived] at hQ ⊢
  obtain ⟨K, hF, hFin, hK, hQ'⟩ := hQ
  refine ⟨K, hF, hFin, hK, hQ', ?_⟩
  rw [SetupFalse]
  intro L' _ _ ψ hψ hker hcomm e J a hsetup
  rcases hsetup with
    ⟨hp, hp2, he1, he3, hφI, hJcomp, h2n, hJlabel, hae, haI, haJ, hanon⟩
  obtain ⟨φ, hφI, hφeq⟩ := hφI
  have hφne : φ ≠ 1 := by
    intro hφ1
    apply he1
    apply MulEquiv.ext
    intro x
    have hmem : ∀ y ∈ (⊤ : Subgroup L'), e y * y⁻¹ ∈ ψ.ker := by
      intro y _
      rw [MonoidHom.mem_ker]
      have h1 : ψ (e y * y⁻¹) = φ (ψ y) * (ψ y)⁻¹ := by
        rw [map_mul, map_inv, ← hφeq]
      rw [h1, hφ1]
      simp
    exact CFSG.StandardType.USixTwo.fix_of_perfect (π := ψ) hker
      (show ⁅(⊤ : Subgroup L'), ⊤⁆ = ⊤ from hcomm) hmem x (Subgroup.mem_top x)
  have hφ3 : φ ^ 3 = 1 := by
    apply MulEquiv.ext
    intro r
    obtain ⟨y, rfl⟩ := hψ r
    have hpow : ∀ k : ℕ, ∀ y : L', (φ ^ k) (ψ y) = ψ ((e ^ k) y) := by
      intro k
      induction k with
      | zero => intro y; simp
      | succ k ih =>
        intro y
        rw [pow_succ, MulAut.mul_apply, hφeq, ih, pow_succ, MulAut.mul_apply]
    rw [hpow 3 y, he3]
    simp
  have hR : ∃ x y : LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true),
      x * y ≠ y * x := ltrke3_g2der_nonabelian hK
  have hφinner : φ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true)) :=
    RawAutSmall.mem_inner_g2der hK hR (m := 3) (by decide) hφ3
  obtain ⟨u, rfl⟩ := hφinner
  have hu1 : u ≠ 1 := by
    intro hu
    exact hφne (by rw [hu]; exact map_one _)
  obtain ⟨eR⟩ := TableBExcSmallRest.nonempty_g2der_equiv_su3 K hK
  have hZ : Subgroup.center (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true)) = ⊥ :=
    TableBExcSmallRest.center_eq_bot_of_mulEquiv eR TableBExcSmallRest.center_su3_eq_bot
  have hu3 : u ^ 3 = 1 := by
    refine ltrke3_conj_eq_one_iff hZ ?_
    simpa only [map_pow] using hφ3
  have hu'1 : eR u ≠ 1 := fun h => hu1 (eR.injective (by rw [h, map_one]))
  have hu'3 : (eR u) ^ 3 = 1 := by rw [← map_pow, hu3, map_one]
  haveI hsol : Group.IsSolvable
      (Subgroup.centralizer ({eR u} : Set (CFSG.Open.StatedSU 3 3 F9))) :=
    ltrke3_su3_centralizer_solvable hu'1 hu'3
  have hle : (J.map ψ).map eR.toMonoidHom ≤
      Subgroup.centralizer ({eR u} : Set (CFSG.Open.StatedSU 3 3 F9)) := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨j, hj, rfl⟩ := hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hfix : e j = j := (mem_ggFixSub.mp (hJcomp.1 hj))
    have hconj : MulAut.conj u (ψ j) = ψ j := by rw [hφeq, hfix]
    rw [MulAut.conj_apply] at hconj
    have hcommu : u * ψ j = ψ j * u := by
      calc u * ψ j = u * ψ j * u⁻¹ * u := by group
        _ = ψ j * u := by rw [hconj]
    show eR (ψ j) * eR u = eR u * eR (ψ j)
    have hh : eR (ψ j * u) = eR (u * ψ j) := by rw [hcommu]
    simpa only [map_mul] using hh
  have hJmap_ne : J.map ψ ≠ ⊥ := by
    intro hbot
    have hJle : J ≤ ψ.ker := by
      rwa [Subgroup.map_eq_bot_iff] at hbot
    have hJcenter : J ≤ Subgroup.center L' := hJle.trans hker
    have hJcomm : ∀ x y : ↥J, x * y = y * x := by
      intro x y
      apply Subtype.ext
      change (x : L') * (y : L') = (y : L') * (x : L')
      exact (Subgroup.mem_center_iff.mp (hJcenter x.2) (y : L')).symm
    haveI : Subsingleton ↥J :=
      ltrke3_perfect_commutative_bot hJcomp.2.2.1 hJcomm
    exact hanon ⟨1, fun j j' _ => Subsingleton.elim _ _⟩
  haveI hJnt : Nontrivial ↥(J.map ψ) := (Subgroup.nontrivial_iff_ne_bot _).2 hJmap_ne
  haveI hJnt' : Nontrivial ↥((J.map ψ).map eR.toMonoidHom) := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hbot
    have hle' := (Subgroup.map_eq_bot_iff _).mp hbot
    have hker_le : eR.toMonoidHom.ker ≤ ⊥ := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      rw [Subgroup.mem_bot]
      exact eR.injective (by simpa using hx)
    exact hJmap_ne (le_bot_iff.mp (hle'.trans hker_le))
  haveI hJperf : Group.IsPerfect ↥J := Group.IsPerfect.mk hJcomp.2.2.1
  haveI hperf1 : Group.IsPerfect ↥(J.map ψ) := Group.IsPerfect.map ψ
  haveI hperf : Group.IsPerfect ↥((J.map ψ).map eR.toMonoidHom) :=
    Group.IsPerfect.map eR.toMonoidHom
  haveI hsolmap : Group.IsSolvable ↥((J.map ψ).map eR.toMonoidHom) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  exact Group.IsPerfect.not_isSolvable ↥((J.map ψ).map eR.toMonoidHom) hsolmap

end CFSG.StandardType.KD2Pieces1615

end
