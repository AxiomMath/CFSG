module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CWrI
public import CFSG.Quasithin.Vol2.Ch10SecQ34LH
public import CFSG.Quasithin.Vol2.Ch10SecQ3CWrG
public import CFSG.Quasithin.Vol2.Ch10SecQ3CWrH

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem card_autOn_le_index_of {H T X B : Subgroup G} (hTH : T ≤ H)
    {Y : Subgroup (E2.StarQuot X H)} [Y.Normal]
    (hker : ∀ x (hx : x ∈ T), x ∈ Subgroup.normalizer (B : Set G) →
      starMk X H ⟨x, hTH hx⟩ ∈ Y → x ∈ Subgroup.centralizer (B : Set G)) :
    Nat.card (autOn T B) ≤ Y.index := by
  set D := T.subgroupOf (Subgroup.normalizer (B : Set G))
  let ι : ↥D →* ↥H :=
    { toFun := fun d => ⟨((d : Subgroup.normalizer (B : Set G)) : G),
        hTH (Subgroup.mem_subgroupOf.mp d.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  set f₂ := (QuotientGroup.mk' Y).comp ((starMk X H).comp ι)
  have hk : f₂.ker ≤ (autOnHom' T B).ker := by
    intro d hd
    rw [MonoidHom.mem_ker] at hd ⊢
    exact autOnHom'_eq_one _ (hker _ (Subgroup.mem_subgroupOf.mp d.2)
      (d : Subgroup.normalizer (B : Set G)).2 ((QuotientGroup.eq_one_iff _).mp hd))
  calc Nat.card (autOn T B) = Nat.card (autOnHom' T B).range := by rw [range_autOnHom']
    _ ≤ Nat.card f₂.range := card_range_le_of_ker_le _ _ hk
    _ ≤ Nat.card (E2.StarQuot X H ⧸ Y) := Subgroup.card_le_card_group _
    _ = Y.index := rfl

theorem card_autOn_le_index {H T X B : Subgroup G} (hXH : X ≤ H) (hTH : T ≤ H)
    (hT2 : IsPGroup 2 T) (hJ2 : IsPGroup 2 (kerIn X H)) (hBX : B ≤ X) (hBo : Odd (Nat.card B))
    {Y : Subgroup (E2.StarQuot X H)} [Y.Normal]
    (hR : E2.star X H X ≤ Subgroup.normalizer ((E2.star X H T ⊓ Y : Subgroup _) : Set _)) :
    Nat.card (autOn T B) ≤ Y.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2R : IsPGroup 2 ↥(E2.star X H T ⊓ Y) := by
    have hT2' : IsPGroup 2 ↥(T.subgroupOf H) :=
      hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
    exact (hT2'.map (starMk X H)).to_le inf_le_left
  refine card_autOn_le_index_of hTH fun x hxT hxN hdY => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hbH : b ∈ H := hXH (hBX hb)
  have hzB : x * b * x⁻¹ * b⁻¹ ∈ B :=
    B.mul_mem ((Subgroup.mem_normalizer_iff.mp hxN b).mp hb) (B.inv_mem hb)
  set x' : ↥H := ⟨x, hTH hxT⟩
  set b' : ↥H := ⟨b, hbH⟩
  have hx'R : starMk X H x' ∈ E2.star X H T ⊓ Y :=
    ⟨⟨x', Subgroup.mem_subgroupOf.mpr hxT, rfl⟩, hdY⟩
  have hb'X : starMk X H b' ∈ E2.star X H X := ⟨b', Subgroup.mem_subgroupOf.mpr (hBX hb), rfl⟩
  have hconj : starMk X H b' * (starMk X H x')⁻¹ * (starMk X H b')⁻¹ ∈
      E2.star X H T ⊓ Y :=
    (Subgroup.mem_normalizer_iff.mp (hR hb'X) _).mp (Subgroup.inv_mem _ hx'R)
  have hzR : starMk X H (x' * b' * x'⁻¹ * b'⁻¹) ∈ E2.star X H T ⊓ Y := by
    have : starMk X H (x' * b' * x'⁻¹ * b'⁻¹) =
        starMk X H x' * (starMk X H b' * (starMk X H x')⁻¹ * (starMk X H b')⁻¹) := by
      simp only [map_mul, map_inv]
      group
    rw [this]
    exact Subgroup.mul_mem _ hx'R hconj
  have hodd : Odd (orderOf (starMk X H (x' * b' * x'⁻¹ * b'⁻¹))) := by
    refine Odd.of_dvd_nat (Odd.of_dvd_nat hBo ?_) (orderOf_map_dvd _ _)
    rw [← Subgroup.orderOf_coe]
    exact Subgroup.orderOf_dvd_natCard B hzB
  have h1 := eq_one_of_mem_of_odd h2R hzR hodd
  have hzJ : x * b * x⁻¹ * b⁻¹ ∈ kerIn X H := by
    have := (QuotientGroup.eq_one_iff _).mp h1
    exact Subgroup.mem_subgroupOf.mp this
  have hz1 := eq_one_of_mem_of_odd hJ2 hzJ
    (Odd.of_dvd_nat hBo (Subgroup.orderOf_dvd_natCard B hzB))
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hz1
  exact hz1.symm

omit [Finite G] in
theorem subgroupOf_kerIn_eq_pCore {H X : Subgroup G} (hJ : kerIn X H = pCoreOf 2 H) :
    (kerIn X H).subgroupOf H = CFSG.pCore 2 ↥H := by
  ext ⟨x, hx⟩
  rw [Subgroup.mem_subgroupOf, hJ]
  exact C10P34.mem_pCoreOf_iff hx

theorem case1a (hBC : FactBorelCartan) {H T X K B : Subgroup G}
    (hmin : MinParabolic H T X) (hXH : X ≤ H) (hTX : T ≤ X) (hTXs : IsSylowTwoOf T X)
    (hns : ¬ Group.IsSolvable ↥H) (hKc : K ∈ cComp H) (hHK : H = K ⊔ T)
    (hJ : kerIn X H = pCoreOf 2 H) {t : G} (ht : t ∈ T) (hne : cjSub t K ≠ K)
    (hMeq : X = (X ⊓ K) ⊔ cjSub t (X ⊓ K) ⊔ T) (hK4 : IsPSL 2 2 2 ↥(E2.star X H K))
    (hBor : E2.IsBorelIn (E2.star X H K) (E2.star X H (X ⊓ K)))
    (hB : Lin2.IsHallTwoPrimeOf B X) (hB9 : Nat.card B = 9) (hA : 8 ≤ Nat.card (autOn T B)) :
    Nonempty (↥H ⧸ CFSG.pCore 2 ↥H ≃* SymFiveWrTwo) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hTX.trans hXH
  have hT2 : IsPGroup 2 T := hTXs.2.1
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hJR := kerIn_eq_solvRad hmin.uniqueMax hT2 hns hJ
  have hsubJ := subgroupOf_kerIn_eq hJR
  have hrad := solvableRadical_star_eq_bot hsubJ
  have hker : Group.IsSolvable ↥((kerIn X H).subgroupOf H) := by
    rw [hsubJ]
    exact A3.solvableRadical_isSolvable
  have hcK : ∀ s ∈ T, E2.star X H (cjSub s K) ∈ cComp (⊤ : Subgroup (E2.StarQuot X H)) :=
    fun s hs => mem_cComp_star hker (cjSub_mem_cComp' hKc (hTH hs))
  have hK1 : E2.star X H K ∈ cComp (⊤ : Subgroup (E2.StarQuot X H)) := mem_cComp_star hker hKc
  obtain ⟨S, hS, hBorEq⟩ := hBor
  set τ := starMk X H ⟨t, hTH ht⟩ with hτdef
  have hstarT : ∀ s ∈ E2.star X H T, ∃ s₀ ∈ T, ∃ hs₀ : s₀ ∈ H, s = starMk X H ⟨s₀, hs₀⟩ := by
    rintro _ ⟨⟨s₀, hs₀H⟩, hs₀, rfl⟩
    exact ⟨s₀, Subgroup.mem_subgroupOf.mp hs₀, hs₀H, rfl⟩
  have hXK : X ⊓ K ≤ H := inf_le_left.trans hXH
  have hcjXK : cjSub t (X ⊓ K) ≤ H := by
    rw [← Ch11.SecB.map_conj_eq_self_of_mem_normalizer (Subgroup.le_normalizer (hTH ht))]
    exact Subgroup.map_mono hXK
  obtain ⟨d, hd, hdo⟩ := exists_borel_elt hBC (le_refl 2) (Or.inl ⟨le_rfl, Or.inl hK4⟩)
    ⟨S, hS, hBorEq⟩
  have c : WrCore (E2.star X H T) (E2.star X H K) (E2.star X H X) S τ :=
    { hO := eq_bot_of_normal_star hmin
      hT := isSylowTwoOf_star hmin
      hA5 := nonempty_equiv_aFive hK4
      hsub := fun s hs => by
        obtain ⟨s₀, hs₀, hs₀H, rfl⟩ := hstarT s hs
        rw [← star_cjSub hs₀H]
        exact subnormal_of_mem_cComp (hcK s₀ hs₀)
      hτ := ⟨⟨t, hTH ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
      hne := by
        rw [← star_cjSub (hTH ht)]
        exact star_ne hker (cjSub_mem_cComp' hKc (hTH ht)) hKc hne
      hcomm := fun s hs => by
        obtain ⟨s₀, hs₀, hs₀H, rfl⟩ := hstarT s hs
        rw [← star_cjSub hs₀H]
        rcases CFSG.LocalCores.distinct_components_commute
          (isComponent_of_mem_cComp_top hrad hK1) (isComponent_of_mem_cComp_top hrad
            (hcK s₀ hs₀)) with h | h
        · exact Or.inl h.symm
        · exact Or.inr h
      hgen := by rw [← star_sup hKH hTH, ← hHK, star_self]
      h27 := not_dvd_card_star hXH hTXs hB hB9
      hS := hS
      hMX := hBorEq ▸ star_mono (inf_le_left : X ⊓ K ≤ X)
      hX₀ := by
        rw [← hBorEq]
        have h1 : E2.star X H X = E2.star X H ((X ⊓ K) ⊔ cjSub t (X ⊓ K) ⊔ T) :=
          congrArg (fun Y => E2.star X H Y) hMeq
        rw [h1, star_sup (sup_le hXK hcjXK) hTH, star_sup hXK hcjXK, star_cjSub (hTH ht)]
      hTX := star_mono hTX
      hTK := by
        rw [← hBorEq]
        exact (star_inf_le (hJ ▸ B6.pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow)).trans
          (star_mono (inf_le_inf_right _ hTX))
      hd := ⟨d, hBorEq ▸ hd, by rw [hdo]; norm_num⟩ }
  have hJ2 : IsPGroup 2 (kerIn X H) := hJ ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hY := c.normal_Y
  have h8 : 8 ≤ (E2.star X H K ⊔ cjSub τ (E2.star X H K)).index :=
    hA.trans (card_autOn_le_index hXH hTH hT2 hJ2 hB.1 hB.2.1 (by
      have := c.le_normalizer_R
      exact this))
  obtain ⟨φ⟩ := c.nonempty_equiv h8
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (subgroupOf_kerIn_eq_pCore hJ).symm).trans φ⟩

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
