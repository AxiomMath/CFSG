module

public import CFSG.Quasithin.EmptyFaithful.S146zTOrbit
public import CFSG.Quasithin.EmptyFaithful.S146zRImg
public import CFSG.Quasithin.EmptyFaithful.S146zMSol
public import CFSG.Quasithin.EmptyFaithful.S146zQLists

public section

namespace CFSG.Quasithin.S146zT

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7

theorem input14614NoSz_proved :
    Input14614NoSz := by
  intro G _ _ T M S H PQ p hred hmax J hJ n hn hne
  obtain ⟨e⟩ := hne
  classical
  have hp35 : p = 3 ∨ p = 5 := S.p_eq_three_or_five_of_isRedCE hred
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hTG : T ≤ mcOf T := hTH.trans hHG
  set X : Subgroup G := mcOf T with hXdef
  set R : Subgroup ↥X := CFSG.Open.pCore 2 ↥X with hRdef
  have hRp : IsPGroup 2 R := CFSG.LieType.BorelTits.pCore_isPGroup 2
  let π : ↥X →* ↥X ⧸ R := QuotientGroup.mk' R
  have hJc : imageOTwoQuot X J ∈ cComp (⊤ : Subgroup (OTwoQuot X)) := q_image_mem_cComp hJ
  obtain ⟨eJ⟩ := q_oTwoQuot_equiv_image (subnormal_of_mem_cComp hJ)
  have hSz : IsSzSub (imageOTwoQuot X J) := ⟨n, hn, ⟨eJ.symm.trans e⟩⟩
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hTi : ¬ 2 ∣ T.index := S.hyp.sylow.2
  have hT'p : IsPGroup 2 (T.subgroupOf X) :=
    hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTG).symm
  have hT'i : ¬ 2 ∣ (T.subgroupOf X).index := by
    intro hd
    apply hTi
    have h1 : T.relIndex X * X.index = T.index := Subgroup.relIndex_mul_index hTG
    rw [← h1]
    exact hd.trans (dvd_mul_right _ _)
  have hTb : IsSylowTwoOf ((T.subgroupOf X).map π) ⊤ := isSylowTwoOf_map_quotient R hT'p hT'i
  set Hb : Subgroup (↥X ⧸ R) := (H.subgroupOf X).map π with hHbdef
  have hTbH : (T.subgroupOf X).map π ≤ Hb :=
    Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hTH (Subgroup.mem_subgroupOf.mp hx))
  have hHs : Group.IsSolvable ↥H := hred.isSolvable S
  have hHbs : Group.IsSolvable ↥Hb := by
    have hH's : Group.IsSolvable ↥(H.subgroupOf X) :=
      Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hHG).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hHG).symm.surjective
    exact Group.isSolvable_of_surjective (f := π.subgroupMap (H.subgroupOf X))
      (π.subgroupMap_surjective _)
  obtain ⟨B, hBs, hHbB, ℓ, hℓ, h7, hd⟩ :=
    exists_solvable_normalized_of_suzuki_orbit hTb hTbH hHbs hJc hSz
  set Y : Subgroup (↥X ⧸ R) := Hb ⊔ B with hYdef
  have hYs : Group.IsSolvable ↥Y := isSolvable_sup_of_normalizes hHbB hHbs hBs
  set Hp : Subgroup G := (Y.comap π).map X.subtype with hHpdef
  have hCs : Group.IsSolvable ↥(Y.comap π) := isSolvable_comap_quotient R hRp hYs
  have hHpsolv : Group.IsSolvable ↥Hp :=
    Group.isSolvable_of_surjective
      (f := ((Y.comap π).equivMapOfInjective X.subtype X.subtype_injective).toMonoidHom)
      ((Y.comap π).equivMapOfInjective X.subtype X.subtype_injective).surjective
  have hHHp : H ≤ Hp := by
    intro h hh
    refine ⟨⟨h, hHG hh⟩, ?_, rfl⟩
    show π ⟨h, hHG hh⟩ ∈ Y
    exact (le_sup_left : Hb ≤ Y) ⟨⟨h, hHG hh⟩, Subgroup.mem_subgroupOf.mpr hh, rfl⟩
  have hHpM : Hp ≤ mcOf T := Subgroup.map_subtype_le _
  have hdvdHp : ℓ ∣ Nat.card ↥Hp := by
    have h1 : Nat.card B ∣ Nat.card Y := Subgroup.card_dvd_of_le le_sup_right
    have h2' : Nat.card Y ∣ Nat.card ↥(Y.comap π) := card_dvd_comap_quotient R Y
    have h3' : Nat.card ↥(Y.comap π) = Nat.card ↥Hp :=
      Nat.card_congr ((Y.comap π).equivMapOfInjective X.subtype X.subtype_injective).toEquiv
    rw [← h3']
    exact hd.trans (h1.trans h2')
  have hsolv := input14614Solv_proved G T M S H PQ p hred hmax Hp hHHp hHpM hHpsolv
  rcases hp35 with rfl | rfl
  · rcases hsolv.1 rfl ℓ hℓ hdvdHp with h | h <;> omega
  · rcases hsolv.2 rfl ℓ hℓ hdvdHp with h | h | h <;> omega

end CFSG.Quasithin.S146zT
