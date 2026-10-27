module

public import CFSG.RankThree.PartOne.S11c.CentralWitness
public import CFSG.RankThree.CentralCover.SteinbergBNCoverPairingCore
public import CFSG.RankThree.PartOne.KF.ClsBasic

public section

namespace CFSG.RankThree.PartOne.HNRed

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne
open CFSG.Assembly.RankThreeEven (localRank)

theorem exists_elemAbelian_rank_four_in_preimage {Y X : Type*} [Group Y] [Finite Y] [Group X]
    (φ : Y →* X) (hφ : Function.Surjective φ) (hZ : φ.ker ≤ Subgroup.center Y) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {U : Subgroup X} {k : ℕ} (hU : IsElementaryAbelian p U)
    (hUcard : Nat.card U = p ^ k) (hk : 6 ≤ k) :
    ∃ A : Subgroup Y, A ≤ U.comap φ ∧ IsElementaryAbelian p A ∧ ∃ r : ℕ, 4 ≤ r ∧
      Nat.card A = p ^ r := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hUp : IsPGroup p U := IsElementaryAbelian.isPGroup p U
  have : Finite U := Nat.finite_of_card_ne_zero (by rw [hUcard]; exact (pow_pos hp.pos k).ne')
  set F : Subgroup Y := U.comap φ with hF
  have hnil : Group.IsNilpotent F := by
    let f : F →* U := (φ.comp F.subtype).codRestrict U fun x => x.2
    have : Group.IsNilpotent U := hUp.isNilpotent
    refine Subgroup.isNilpotent_of_ker_le_center f ?_
    intro x hx
    have hxk : (x : Y) ∈ φ.ker := congrArg Subtype.val hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hZ hxk) y)
  obtain ⟨P⟩ : Nonempty (Sylow p F) := inferInstance
  set S : Subgroup Y := (P : Subgroup F).map F.subtype with hS
  have hSU : S.map φ = U := map_sylow_comap φ hφ hUp P
  have hSF : S ≤ F := fun x hx => by
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  let ψ : S →* U := (φ.comp S.subtype).codRestrict U fun x => hSU ▸ Subgroup.mem_map_of_mem φ x.2
  have hψs : Function.Surjective ψ := fun u => by
    have hu : (u : X) ∈ S.map φ := by rw [hSU]; exact u.2
    obtain ⟨x, hx, hxu⟩ := hu
    exact ⟨⟨x, hx⟩, Subtype.ext hxu⟩
  have hker' : ψ.ker ≤ Subgroup.center S := fun x hx => by
    have hxk : ((x : S) : Y) ∈ φ.ker := congrArg Subtype.val hx
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hZ hxk) w)
  have e := QuotientGroup.quotientKerEquivOfSurjective ψ hψs
  have hel : IsElementaryAbelian p (S ⧸ ψ.ker) :=
    isElementaryAbelian_of_mulEquiv_lift e.symm hU
  have hcard : Nat.card (S ⧸ ψ.ker) = p ^ k := by rw [Nat.card_congr e.toEquiv]; exact hUcard
  have hrank4 : 4 ≤ pRank p S := by
    by_contra hlt
    have h5 := central_elementary_odd_quotient_rank_three_bound hp hp2 (F := S)
      (by omega) ψ.ker hker' k hel hcard
    omega
  obtain ⟨A, hA, hAcard⟩ := exists_isElementaryAbelian_card_pRank (p := p) hp.one_lt (H := S)
  refine ⟨A.map S.subtype, ?_, IsElementaryAbelian.map_subtype (H := A), pRank p S, hrank4, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact hSF x.2
  · rw [Subgroup.card_map_of_injective S.subtype_injective, hAcard]

theorem four_le_localRank_of_cover {H : Type} [Group H] [Finite H] {X : Subgroup H} {T : Type}
    [Group T] [Finite T] (φ : X →* T) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center X) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h6 : 6 ≤ localRank p T) : 4 ≤ localRank p H := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, hU2, hU1, E, hEN, hE, hEcard⟩ :=
    exists_elemAbelian_of_le_localRank hp (by norm_num) h6
  obtain ⟨A, hAF, hAel, r, hr, hAcard⟩ :=
    exists_elemAbelian_rank_four_in_preimage φ hφ hker hp hp2 hE hEcard le_rfl
  obtain ⟨R, hR1, hR2, hFR⟩ := CFSG.RankThree.CentralCover.exists_two_subgroup_normalized_of_cover
    hφ hker hU1 hU2 (S := E.comap φ) (fun x hx u hu =>
      ((Subgroup.mem_normalizer_iff.1 (hEN hx)) u).1 hu)
  have hR1' : R.map X.subtype ≠ ⊥ := fun h =>
    hR1 ((Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).1 h)
  have hAN : A.map X.subtype ≤ Subgroup.normalizer ((R.map X.subtype : Subgroup H) : Set H) :=
    (Subgroup.map_mono (hAF.trans hFR)).trans (Subgroup.le_normalizer_map X.subtype)
  have hAab : CFSG.Open.IsElemAbelian p (A.map X.subtype) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1
      (IsElementaryAbelian.map_subtype (H := A))
  have hAcard' : Nat.card (A.map X.subtype) = p ^ r := by
    rw [Subgroup.card_map_of_injective X.subtype_injective, hAcard]
  have hloc : CFSG.Open.IsTwoLocal (Subgroup.normalizer ((R.map X.subtype : Subgroup H) : Set H)) :=
    ⟨_, hR1', hR2.map X.subtype, rfl⟩
  exact hr.trans ((CFSG.SectionRank.le_pRank hp.one_lt hAN hAab hAcard').trans
    (le_csSup (CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_bddAbove p hp H)
      ⟨_, hloc, rfl⟩))

theorem isElementaryAbelian_range_cube {T : Type} [Group T]
    (θ : Multiplicative (Fin 6 → ZMod 3) →* T) (hθ : Function.Injective θ) :
    IsElementaryAbelian 3 θ.range ∧ Nat.card θ.range = 3 ^ 6 := by
  refine ⟨?_, ?_⟩
  · refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
    · obtain ⟨_, a, rfl⟩ := a
      obtain ⟨_, b, rfl⟩ := b
      apply Subtype.ext
      change θ a * θ b = θ b * θ a
      rw [← map_mul, ← map_mul, mul_comm]
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
      obtain ⟨_, a, rfl⟩ := x
      apply Subtype.ext
      change θ a ^ 3 = 1
      rw [← map_pow]
      have : a ^ 3 = 1 := by
        apply Multiplicative.toAdd.injective
        ext j
        simp [toAdd_pow]
        exact Or.inl (by decide)
      rw [this, map_one]
  · rw [Nat.card_congr (MonoidHom.ofInjective hθ).toEquiv.symm]
    rw [Nat.card_eq_fintype_card]
    simp [Fintype.card_pi, ZMod.card]

theorem four_le_localRank_of_rank_six_witness {H : Type} [Group H] [Finite H] {X : Subgroup H}
    {T : Type} [Group T] (η : X →* T) (hη : Function.Surjective η)
    (hker : η.ker ≤ Subgroup.center X) (θ : Multiplicative (Fin 6 → ZMod 3) →* T)
    (hθ : Function.Injective θ) {s : T} (hs1 : s ≠ 1) (hs2 : s ^ 2 = 1)
    (hsθ : ∀ a, s * θ a = θ a * s) : 4 ≤ localRank 3 H := by
  obtain ⟨hel, hcard⟩ := isElementaryAbelian_range_cube θ hθ
  obtain ⟨z, hz2, hz1, V, hV, hVel, r, hr, hVcard⟩ :=
    exists_rank_four_of_central_witness η hη hker Nat.prime_three (by norm_num) hel hcard
      (le_refl 6) hs1 hs2 (fun u hu => by
        obtain ⟨a, rfl⟩ := hu
        exact hsθ a)
  exact le_localRank_of_rank_four_witness (G := H) (Y := X) Nat.prime_three.one_lt
    ⟨z, hz2, hz1, V, hV, hVel, r, hr, hVcard⟩

end CFSG.RankThree.PartOne.HNRed
