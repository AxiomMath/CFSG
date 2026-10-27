module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Set
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3NatIrr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3NatEnd
public import TauCeti.Algebra.Group.Subgroup.TwoTorsionClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {V : Type} [CommGroup V]

theorem s16t3_inv_map_fixV_normalizer {E : Subgroup (MulAut V)} {x : MulAut V}
    (hx : x ∈ Subgroup.normalizer (E : Set (MulAut V))) :
    (fixV E).map x.toMonoidHom = fixV E := by
  ext v
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [mem_fixV] at hu ⊢
    intro l hl
    have hlinv : x⁻¹ * l * x ∈ E := by
      have h := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (E : Set (MulAut V))).inv_mem hx) l).mp hl
      simpa using h
    have h1 : (x⁻¹ * l * x) u = u := hu _ hlinv
    have h2 : x ((x⁻¹ * l * x) u) = x u := by rw [h1]
    simpa [MulAut.mul_apply, MulAut.apply_inv_self] using h2
  · intro hv
    refine ⟨x⁻¹ v, ?_, by simp⟩
    rw [mem_fixV] at hv ⊢
    intro l hl
    have hlinv : x * l * x⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hx l).mp hl
    have h1 : (x * l * x⁻¹) v = v := hv _ hlinv
    have h2 : x (l (x⁻¹ v)) = v := by simpa [MulAut.mul_apply] using h1
    have h3 : x⁻¹ (x (l (x⁻¹ v))) = x⁻¹ v := by rw [h2]
    simpa [MulAut.apply_inv_self] using h3

theorem s16t3_inv_sumOfNat_const
    {N : Subgroup (MulAut V) → Subgroup V → Subgroup V → Prop}
    {L : Subgroup (MulAut V)} {I Z : Subgroup V} (hZI : Z ≤ I) (hNI : N L I Z) :
    SumOfNat N L I Z 1 := by
  refine ⟨fun _ => I, fun _ => hZI, ?_, ?_, fun _ => hNI⟩
  · intro i
    have hbot : (⨆ (j : Fin 1) (_ : j ≠ i), I) = ⊥ := by
      apply iSup_eq_bot.2
      intro j
      apply iSup_eq_bot.2
      intro hj
      exact absurd (Subsingleton.elim j i) hj
    rw [hbot, sup_bot_eq]
    exact inf_le_right
  · rw [iSup_const, sup_eq_right.2 hZI]

theorem s16t3_inv_exists_family {L : Subgroup (MulAut V)} {Z : Subgroup V}
    (h : SumOfNatShape L ⊤ Z 3) :
    ∃ I : Fin 3 → Subgroup V, (∀ i, Z ≤ I i) ∧
      (∀ i, I i ⊓ (Z ⊔ ⨆ (j : Fin 3) (_ : j ≠ i), I j) ≤ Z) ∧
      (Z ⊔ ⨆ i, I i = ⊤) ∧ ∀ i, SumOfNatShape L (I i) Z 1 := by
  obtain ⟨n, hcases⟩ := h
  rcases hcases with ⟨hSL, hsum⟩ | ⟨hSp, hsum⟩ | ⟨hOP, hsum⟩ | ⟨hOM, hsum⟩ | ⟨hAl, hsum⟩
  · obtain ⟨I, hZI, hind, hsup, hNI⟩ := hsum
    exact ⟨I, hZI, hind, hsup,
      fun i => ⟨n, Or.inl ⟨hSL, s16t3_inv_sumOfNat_const (hZI i) (hNI i)⟩⟩⟩
  · obtain ⟨I, hZI, hind, hsup, hNI⟩ := hsum
    exact ⟨I, hZI, hind, hsup,
      fun i => ⟨n, Or.inr (Or.inl ⟨hSp, s16t3_inv_sumOfNat_const (hZI i) (hNI i)⟩)⟩⟩
  · obtain ⟨I, hZI, hind, hsup, hNI⟩ := hsum
    exact ⟨I, hZI, hind, hsup,
      fun i => ⟨n, Or.inr (Or.inr (Or.inl
        ⟨hOP, s16t3_inv_sumOfNat_const (hZI i) (hNI i)⟩))⟩⟩
  · obtain ⟨I, hZI, hind, hsup, hNI⟩ := hsum
    exact ⟨I, hZI, hind, hsup,
      fun i => ⟨n, Or.inr (Or.inr (Or.inr (Or.inl
        ⟨hOM, s16t3_inv_sumOfNat_const (hZI i) (hNI i)⟩)))⟩⟩
  · obtain ⟨I, hZI, hind, hsup, hNI⟩ := hsum
    exact ⟨I, hZI, hind, hsup,
      fun i => ⟨n, Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hAl, s16t3_inv_sumOfNat_const (hZI i) (hNI i)⟩)))⟩⟩

theorem s16t3_inv_card_closure_eq_eight {V : Type} [CommGroup V]
    {Z : Subgroup V} {I : Fin 3 → Subgroup V} {c : Fin 3 → V}
    (hW : ∀ w : V, w * w = 1)
    (hind : ∀ i, I i ⊓ (Z ⊔ ⨆ (j : Fin 3) (_ : j ≠ i), I j) ≤ Z)
    (hcI : ∀ i, c i ∈ I i) (hcZ : ∀ i, c i ∉ Z) :
    Nat.card (Subgroup.closure (Set.range c)) = 8 := by
  have hsq : ∀ i ∈ (Finset.univ : Finset (Fin 3)), c i ^ 2 = 1 := by
    intro i _
    rw [pow_two]
    exact hW (c i)
  have hinj : Set.InjOn (fun S : Finset (Fin 3) => ∏ i ∈ S, c i)
      ↑(Finset.univ : Finset (Fin 3)).powerset := by
    intro S _hS D _hD hSD
    have hSD' : (∏ i ∈ S, c i) = ∏ i ∈ D, c i := hSD
    have hsym : ∏ i ∈ S \ D ∪ D \ S, c i = 1 := by
      have hpp : (∏ i ∈ S, c i) * (∏ i ∈ S, c i) = 1 := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_eq_one (fun i _ => hW (c i))
      rw [TauCeti.prod_sdiff_union_sdiff (S := S) (D := D) c
        (fun i _ => hsq i (Finset.mem_univ i))]
      rw [← hSD']
      exact hpp
    have hstep : ∀ j, j ∈ S \ D ∪ D \ S → False := by
      intro j hjΔ
      have hmul : c j * (∏ i ∈ (S \ D ∪ D \ S).erase j, c i) = 1 := by
        rw [Finset.mul_prod_erase _ _ hjΔ, hsym]
      have hrest : (∏ i ∈ (S \ D ∪ D \ S).erase j, c i) ∈
          Z ⊔ ⨆ (i : Fin 3) (_ : i ≠ j), I i := by
        apply (Z ⊔ ⨆ (i : Fin 3) (_ : i ≠ j), I i).prod_mem
        intro i hi
        rw [Finset.mem_erase] at hi
        exact Subgroup.mem_sup_right
          (le_iSup₂ (f := fun i (_ : i ≠ j) => I i) i hi.1 (hcI i))
      have hcj : c j ∈ Z ⊔ ⨆ (i : Fin 3) (_ : i ≠ j), I i := by
        rw [eq_inv_of_mul_eq_one_left hmul]
        exact (Z ⊔ ⨆ (i : Fin 3) (_ : i ≠ j), I i).inv_mem hrest
      exact hcZ j (hind j (Subgroup.mem_inf.2 ⟨hcI j, hcj⟩))
    apply Finset.Subset.antisymm
    · intro j hjS
      by_contra hjD
      exact hstep j (Finset.mem_union.2 (Or.inl (Finset.mem_sdiff.2 ⟨hjS, hjD⟩)))
    · intro j hjD
      by_contra hjS
      exact hstep j (Finset.mem_union.2 (Or.inr (Finset.mem_sdiff.2 ⟨hjD, hjS⟩)))
  have h := TauCeti.natCard_closure_image_eq_two_pow
    (Finset.univ : Finset (Fin 3)) c hsq hinj
  simpa using h

theorem s16t3_inv_eight_le_range_of_move [Finite V]
    {L : Subgroup (MulAut V)} {I Z : Subgroup V} {t : MulAut V}
    (hq : CFSG.Open.IsQuasisimple ↥L) (hnat : SumOfNatShape L I Z 1)
    (htN : t ∈ Subgroup.normalizer (L : Set (MulAut V)))
    (hZt : Z.map t.toMonoidHom = Z)
    (hnot : ¬ I ≤ I.map t.toMonoidHom) :
    8 ≤ Nat.card (commHom t).range := by
  have hIirr : IsIrrOn L I Z := SumOfNatShape.isIrrOn hq hnat
  have hIr : StableUnder L I := hIirr.2.1
  have hZleI : Z ≤ I := le_of_lt hIirr.1
  have hZleI' : Z ≤ I.map t.toMonoidHom := by
    rw [← hZt]
    exact Subgroup.map_mono hZleI
  have hI'stab : StableUnder L (I.map t.toMonoidHom) := by
    intro l hl u' hu'
    obtain ⟨u, hu, rfl⟩ := hu'
    have hconj : t⁻¹ * l * t ∈ L := by
      have h := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (L : Set (MulAut V))).inv_mem htN) l).mp hl
      simpa using h
    exact ⟨(t⁻¹ * l * t) u, hIr _ hconj u hu, by simp [MulAut.mul_apply]⟩
  have hInfStab : StableUnder L (I ⊓ I.map t.toMonoidHom) :=
    fun l hl u hu => ⟨hIr l hl u hu.1, hI'stab l hl u hu.2⟩
  have hZleInf : Z ≤ I ⊓ I.map t.toMonoidHom := le_inf hZleI hZleI'
  have hInf : I ⊓ I.map t.toMonoidHom = Z := by
    rcases hIirr.2.2.2 (I ⊓ I.map t.toMonoidHom) hInfStab hZleInf inf_le_left with h | h
    · exact h
    · exact absurd (le_of_eq_of_le h.symm inf_le_right) hnot
  let f : ↥I →* V := (commHom t).comp I.subtype
  have hfker : ∀ u : ↥I, f u = 1 → ((u : I) : V) ∈ Z := by
    intro u hu
    have hcomm : commHom t (u : V) = 1 := hu
    have htu : t (u : V) = (u : V) := by
      rw [commHom_apply] at hcomm
      exact mul_inv_eq_one.1 hcomm
    rw [← hInf]
    exact ⟨u.2, ⟨(u : V), u.2, by simpa using htu⟩⟩
  have hker_le : Nat.card f.ker ≤ Nat.card ↥Z := by
    let inj : ↥f.ker → ↥Z := fun u => ⟨(((u : f.ker) : ↥I) : V), hfker _ u.2⟩
    refine Nat.card_le_card_of_injective inj (fun a b hab => ?_)
    have h1 : (((a : f.ker) : ↥I) : V) = (((b : f.ker) : ↥I) : V) :=
      congrArg (fun z : ↥Z => (z : V)) hab
    exact Subtype.ext (Subtype.ext h1)
  have hI8 : 8 * Nat.card ↥Z ≤ Nat.card ↥I := SumOfNatShape.eight_mul_card_le hq hnat
  have hcard := Subgroup.card_ker_mul_card_range f
  haveI : Nonempty ↥f.ker := ⟨1⟩
  have hpos : 0 < Nat.card f.ker := Nat.card_pos
  have h8ker : 8 * Nat.card f.ker ≤ Nat.card f.ker * Nat.card f.range := by
    calc 8 * Nat.card f.ker ≤ 8 * Nat.card ↥Z := Nat.mul_le_mul_left 8 hker_le
      _ ≤ Nat.card ↥I := hI8
      _ = Nat.card f.ker * Nat.card f.range := hcard.symm
  have h8 : 8 ≤ Nat.card f.range := by
    have hcomm : 8 * Nat.card f.ker ≤ Nat.card f.range * Nat.card f.ker := by
      rw [mul_comm (Nat.card f.range) (Nat.card f.ker)]
      exact h8ker
    exact Nat.le_of_mul_le_mul_right hcomm hpos
  calc 8 ≤ Nat.card f.range := h8
    _ ≤ Nat.card (commHom t).range := Subgroup.card_le_of_le (by
        rintro x ⟨u, rfl⟩
        exact ⟨(u : V), rfl⟩)

theorem s16t3_inv_eq_one_of_trivial_on_summand [Finite V]
    {A L T : Subgroup (MulAut V)} (h : ThreeNat A L T) {t : MulAut V} (ht : t ∈ A)
    (ht2 : t * t = 1)
    {I : Fin 3 → Subgroup V}
    (hsup : fixV L ⊔ ⨆ i, I i = ⊤)
    (hnat : ∀ i, SumOfNatShape L (I i) (fixV L) 1)
    (hstab : ∀ i, I i = (I i).map t.toMonoidHom)
    {j : Fin 3} (htriv : ∀ u ∈ I j, t u * u⁻¹ ∈ fixV L) : t = 1 := by
  have htN : t ∈ Subgroup.normalizer (L : Set (MulAut V)) := h.normal ht
  have htZ : (fixV L).map t.toMonoidHom = fixV L := s16t3_inv_map_fixV_normalizer htN
  have htZmem : ∀ z ∈ fixV L, t z ∈ fixV L := by
    intro z hz
    have : t z ∈ (fixV L).map t.toMonoidHom := ⟨z, hz, rfl⟩
    rwa [htZ] at this
  have htI : ∀ i, ∀ x ∈ I i, t x ∈ I i := by
    intro i x hx
    have : t x ∈ (I i).map t.toMonoidHom := ⟨x, hx, rfl⟩
    rwa [← hstab i] at this
  have hlZ : ∀ l ∈ L, ∀ z ∈ fixV L, l z = z := fun l hl z hz => (mem_fixV.1 hz) l hl
  have hIirrj : IsIrrOn L (I j) (fixV L) := SumOfNatShape.isIrrOn h.quasi (hnat j)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hcomm : ∀ l ∈ L, t * l = l * t := by
    intro l hl
    have hcl : t * l * t⁻¹ * l⁻¹ ∈ L := by
      have h1 : t * l * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp htN l).mp hl
      exact mul_mem h1 (L.inv_mem hl)
    have hctriv : ∀ u ∈ I j, (t * l * t⁻¹ * l⁻¹) u * u⁻¹ ∈ fixV L := by
      intro u hu
      have ha : l⁻¹ u ∈ I j := hIirrj.2.1 l⁻¹ (L.inv_mem hl) u hu
      have htaZ : t (l⁻¹ u) * (l⁻¹ u)⁻¹ ∈ fixV L := htriv _ ha
      have huZ : t u * u⁻¹ ∈ fixV L := htriv u hu
      have hta : t (l⁻¹ u) = (t (l⁻¹ u) * (l⁻¹ u)⁻¹) * (l⁻¹ u) :=
        (inv_mul_cancel_right _ _).symm
      have hlt : l (t (l⁻¹ u)) = (t (l⁻¹ u) * (l⁻¹ u)⁻¹) * u := by
        calc l (t (l⁻¹ u))
            = l ((t (l⁻¹ u) * (l⁻¹ u)⁻¹) * (l⁻¹ u)) := congrArg l hta
          _ = l (t (l⁻¹ u) * (l⁻¹ u)⁻¹) * l (l⁻¹ u) := by rw [map_mul]
          _ = (t (l⁻¹ u) * (l⁻¹ u)⁻¹) * u := by
              rw [hlZ l hl _ htaZ, MulAut.apply_inv_self]
      have hkey : (t * l * t⁻¹ * l⁻¹) u = t (t (l⁻¹ u) * (l⁻¹ u)⁻¹) * t u := by
        rw [htinv]
        calc (t * l * t * l⁻¹) u = t (l (t (l⁻¹ u))) := by simp [MulAut.mul_apply]
          _ = t ((t (l⁻¹ u) * (l⁻¹ u)⁻¹) * u) := by rw [hlt]
          _ = t (t (l⁻¹ u) * (l⁻¹ u)⁻¹) * t u := by rw [map_mul]
      have hfin : (t * l * t⁻¹ * l⁻¹) u * u⁻¹
          = t (t (l⁻¹ u) * (l⁻¹ u)⁻¹) * (t u * u⁻¹) := by
        rw [hkey]
        ac_rfl
      rw [hfin]
      exact Subgroup.mul_mem _ (htZmem _ htaZ) huZ
    have hc1 : t * l * t⁻¹ * l⁻¹ = 1 :=
      SumOfNatShape.eq_one_of_trivial h.quasi (hnat j) hcl hctriv
    calc t * l = (t * l * t⁻¹ * l⁻¹) * (l * t) := by group
      _ = l * t := by rw [hc1, one_mul]
  have htrivI : ∀ i, ∀ u : ↥(I i), t (u : V) * (u : V)⁻¹ ∈ fixV L := by
    intro i
    let φ : MulAut ↥(I i) :=
      { toFun := fun u => ⟨t (u : V), htI i _ u.2⟩
        invFun := fun u => ⟨t (u : V), htI i _ u.2⟩
        left_inv := fun u => Subtype.ext (by
          have h : (t * t) (u : V) = (u : V) := by rw [ht2]; rfl
          rwa [MulAut.mul_apply] at h)
        right_inv := fun u => Subtype.ext (by
          have h : (t * t) (u : V) = (u : V) := by rw [ht2]; rfl
          rwa [MulAut.mul_apply] at h)
        map_mul' := fun u w => Subtype.ext (by
          show t ((u : V) * (w : V)) = t (u : V) * t (w : V)
          rw [map_mul]) }
    have hZc : ∀ u : ↥(I i), ((φ u : ↥(I i)) : V) ∈ fixV L ↔ (u : V) ∈ fixV L := by
      intro u
      change t (u : V) ∈ fixV L ↔ (u : V) ∈ fixV L
      constructor
      · intro htu
        have h2 := htZmem (t (u : V)) htu
        have h3 : t (t (u : V)) = (u : V) := by
          have h : (t * t) (u : V) = (u : V) := by rw [ht2]; rfl
          rwa [MulAut.mul_apply] at h
        rwa [h3] at h2
      · exact htZmem (u : V)
    have hφc : ∀ l ∈ L, ∀ u : ↥(I i), ∀ hu : l (u : V) ∈ I i,
        ((φ ⟨l (u : V), hu⟩ : ↥(I i)) : V) * (l ((φ u : ↥(I i)) : V))⁻¹ ∈ fixV L := by
      intro l hl u _hu
      change t (l (u : V)) * (l (t (u : V)))⁻¹ ∈ fixV L
      have hthis : t (l (u : V)) = l (t (u : V)) := by
        have := congrArg (fun m : MulAut V => m (u : V)) (hcomm l hl)
        simpa [MulAut.mul_apply] using this
      rw [hthis, mul_inv_cancel]
      exact Subgroup.one_mem _
    exact SumOfNatShape.eq_of_equivariant h.quasi (hnat i) φ hZc hφc
  have htop : (⊤ : Subgroup V) ≤ (fixV L).comap (commHom t) := by
    rw [← hsup]
    refine sup_le ?_ ?_
    · intro z hz
      rw [Subgroup.mem_comap]
      exact Subgroup.mul_mem _ (htZmem z hz) (Subgroup.inv_mem _ hz)
    · refine iSup_le fun i => ?_
      intro u hu
      rw [Subgroup.mem_comap]
      exact htrivI i ⟨u, hu⟩
  apply h.faithful t ht
  intro w
  have hw : w ∈ (fixV L).comap (commHom t) := htop (Subgroup.mem_top w)
  rwa [Subgroup.mem_comap] at hw

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
