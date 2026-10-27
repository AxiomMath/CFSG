module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
public import CFSG.LocalAnalysis.SolvableSignalizer.CoprimeAction
public import CFSG.Quasithin.Background.Asc81cTenFourA
public import CFSG.HardMathSupport.Lang.Proving.FixedOrderCongruence
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.SolvableSignalizer

variable {W : Type} [CommGroup W]

private noncomputable instance s16e_e9_mulAutFintype [Finite W] : Fintype (MulAut W) := by
  classical
  haveI : Fintype W := Fintype.ofFinite W
  exact Fintype.ofInjective (fun f : MulAut W => (f : W → W))
    (fun f g h => MulEquiv.ext (congrFun h))

private noncomputable instance s16e_e9_subgroupFintype [Finite W] :
    Fintype (Subgroup (MulAut W)) := by
  classical
  haveI : Fintype (MulAut W) := s16e_e9_mulAutFintype
  exact Fintype.ofInjective (fun X : Subgroup (MulAut W) => (X : Set (MulAut W)))
    SetLike.coe_injective

private abbrev s16e_e9_idx (L : Subgroup (MulAut W)) : Type :=
  {H : Subgroup (MulAut W) // H ≤ L ∧ Nat.card H = 3}

private noncomputable instance s16e_e9_idxFintype [Finite W] (L : Subgroup (MulAut W)) :
    Fintype (s16e_e9_idx L) := by
  classical
  haveI : Fintype (Subgroup (MulAut W)) := s16e_e9_subgroupFintype
  exact Fintype.ofInjective (fun H : s16e_e9_idx L => H.1) (fun _ _ h => Subtype.ext h)

private lemma s16e_e9_card_L {L : Subgroup (MulAut W)} (hL : IsElemAbelianOfRank 3 2 ↥L) :
    Nat.card ↥L = 9 := by
  obtain ⟨e⟩ := hL
  rw [Nat.card_congr e.toEquiv,
    Nat.card_congr (Multiplicative.toAdd (α := Fin 2 → ZMod 3)), Nat.card_pi]
  simp [ZMod.card]

private lemma s16e_e9_pow_three {L : Subgroup (MulAut W)}
    (hL : IsElemAbelianOfRank 3 2 ↥L) (x : ↥L) : x ^ 3 = 1 := by
  obtain ⟨e⟩ := hL
  refine e.injective ?_
  rw [map_pow, map_one]
  have h : ∀ y : Multiplicative (Fin 2 → ZMod 3), y ^ 3 = 1 := by
    intro y
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    have h3 : (3 : ZMod 3) = 0 := by decide
    funext i
    simp [nsmul_eq_mul, h3]
  exact h (e x)

private lemma s16e_e9_isElementaryAbelian {L : Subgroup (MulAut W)}
    (hL : IsElemAbelianOfRank 3 2 ↥L) : CFSG.IsElementaryAbelian 3 ↥L := by
  obtain ⟨e⟩ := hL
  exact CFSG.IsElementaryAbelian.of_mulEquiv e.symm
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := by
        rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
        intro x
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow, toAdd_one]
        have h3 : (3 : ZMod 3) = 0 := by decide
        funext i
        simp [nsmul_eq_mul, h3] }

private lemma s16e_e9_mul_comm {L : Subgroup (MulAut W)}
    (hL : IsElemAbelianOfRank 3 2 ↥L) (x y : ↥L) : x * y = y * x := by
  obtain ⟨e⟩ := hL
  exact e.injective (by rw [map_mul, map_mul, mul_comm])

private lemma s16e_e9_mul_comm_coe {L : Subgroup (MulAut W)}
    (hL : IsElemAbelianOfRank 3 2 ↥L) {x y : MulAut W} (hx : x ∈ L) (hy : y ∈ L) :
    x * y = y * x :=
  congrArg Subtype.val (s16e_e9_mul_comm hL ⟨x, hx⟩ ⟨y, hy⟩)

private lemma s16e_e9_fixV_eq_bot [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} (hL : IsElemAbelianOfRank 3 2 ↥L)
    (hWL : commSub ⊤ L = ⊤) : fixV L = ⊥ := by
  have hodd : Odd (Nat.card L) := by
    rw [s16e_e9_card_L hL]
    norm_num
  have h := CFSG.Quasithin.Asc81c.fixV_inf_commSub_eq_bot' hW hodd (Y := L)
  rw [hWL, inf_top_eq] at h
  exact h

private lemma s16e_e9_fixedSubgroup_eq_fixV_zpowers {L : Subgroup (MulAut W)}
    (a : ↥L) : fixedSubgroup L.subtype a = fixV (Subgroup.zpowers (a : MulAut W)) := by
  ext w
  rw [mem_fixedSubgroup, mem_fixV, Subgroup.forall_mem_zpowers]
  constructor
  · intro h m
    have h' : (a : MulAut W) w = w := h
    have ha_inv : (a : MulAut W)⁻¹ w = w := by
      calc (a : MulAut W)⁻¹ w = (a : MulAut W)⁻¹ ((a : MulAut W) w) := by rw [h']
        _ = w := by simp
    exact zpow_induction_right (g := (a : MulAut W)) (P := fun g => g w = w)
      (by rw [MulAut.one_apply])
      (fun x hx => by rw [MulAut.mul_apply, h', hx])
      (fun x hx => by rw [MulAut.mul_apply, ha_inv, hx]) m
  · intro h
    simpa using h 1

private lemma s16e_e9_iSup_fixV_eq_top [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} (hL : IsElemAbelianOfRank 3 2 ↥L) :
    (⨆ H : s16e_e9_idx L, fixV H.1) = ⊤ := by
  haveI hEA : CFSG.IsElementaryAbelian 3 ↥L := s16e_e9_isElementaryAbelian hL
  letI : CommGroup ↥L := IsMulCommutative.instCommGroup
  have hcardL : Nat.card ↥L = 9 := s16e_e9_card_L hL
  have hcop : ¬ 3 ∣ Nat.card W := by
    have h2 : IsPGroup 2 W := isPGroup_two_of_sq_eq_one hW
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp h2
    rw [hn]
    intro h
    exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) h) (by norm_num)
  have hcard : 3 ^ 2 ≤ Nat.card ↥L := by rw [hcardL]; norm_num
  have h := CFSG.SolvableSignalizer.iSup_fixedSubgroup_eq_top (A := ↥L) 3 Nat.prime_three
    L.subtype hcard hcop
  rw [eq_top_iff] at h ⊢
  refine le_trans h ?_
  refine iSup₂_le ?_
  intro a ha
  rw [s16e_e9_fixedSubgroup_eq_fixV_zpowers a]
  refine le_iSup (fun H : s16e_e9_idx L => fixV H.1)
    ⟨Subgroup.zpowers (a : MulAut W), Subgroup.zpowers_le.mpr a.2, ?_⟩
  rw [Nat.card_zpowers, Subgroup.orderOf_coe]
  have hdvd : orderOf a ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr (s16e_e9_pow_three hL a)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h1 | h3
  · exact absurd (orderOf_eq_one_iff.mp h1) ha
  · exact h3

private lemma s16e_e9_stableUnder_fixV {L : Subgroup (MulAut W)}
    (hL : IsElemAbelianOfRank 3 2 ↥L) (H : Subgroup (MulAut W)) (hHL : H ≤ L) :
    StableUnder L (fixV H) := by
  intro x hxL w hw
  rw [mem_fixV] at hw ⊢
  intro h hh
  have hcomm : h * x = x * h := s16e_e9_mul_comm_coe hL (hHL hh) hxL
  calc h (x w) = (h * x) w := by rw [MulAut.mul_apply]
    _ = (x * h) w := by rw [hcomm]
    _ = x (h w) := by rw [MulAut.mul_apply]
    _ = x w := by rw [hw h hh]

private lemma s16e_e9_mem_fixV_iff (Z : Subgroup (MulAut W)) (w : W) :
    w ∈ fixV Z ↔ Z ≤ centSub (Subgroup.zpowers w) := by
  rw [mem_fixV]
  constructor
  · intro h z hz
    rw [mem_centSub]
    intro u hu
    rw [Subgroup.mem_zpowers_iff] at hu
    obtain ⟨n, rfl⟩ := hu
    calc z (w ^ n) = (z w) ^ n := map_zpow z w n
      _ = w ^ n := by rw [h z hz]
  · intro h z hz
    exact (mem_centSub.mp (h hz)) w (Subgroup.mem_zpowers w)

private lemma s16e_e9_fixV_sup (X Y : Subgroup (MulAut W)) :
    fixV (X ⊔ Y) = fixV X ⊓ fixV Y := by
  ext w
  rw [s16e_e9_mem_fixV_iff, Subgroup.mem_inf, s16e_e9_mem_fixV_iff, s16e_e9_mem_fixV_iff,
    sup_le_iff]

private lemma s16e_e9_sup_eq_L [Finite W] {L H H' : Subgroup (MulAut W)}
    (hHL : H ≤ L) (hH'L : H' ≤ L) (hHc : Nat.card H = 3) (hH'c : Nat.card H' = 3)
    (hLcard : Nat.card ↥L = 9) (hne : H ≠ H') : H ⊔ H' = L := by
  have hle : H ⊔ H' ≤ L := sup_le hHL hH'L
  have hdvd : Nat.card ↥(H ⊔ H') ∣ Nat.card ↥L := Subgroup.card_dvd_of_le hle
  rw [hLcard] at hdvd
  have hHdvd : Nat.card H ∣ Nat.card ↥(H ⊔ H') := Subgroup.card_dvd_of_le le_sup_left
  rw [hHc] at hHdvd
  have hle9 : Nat.card ↥(H ⊔ H') ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd
  have hge3 : 3 ≤ Nat.card ↥(H ⊔ H') := Nat.le_of_dvd (by norm_num) hHdvd
  have hcard : Nat.card ↥(H ⊔ H') = 9 := by
    interval_cases h : Nat.card ↥(H ⊔ H')
    · exfalso
      have h3 : Nat.card ↥(H ⊔ H') = 3 := h
      have hHeq : H ⊔ H' = H :=
        (Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hHc, h3])).symm
      have hH'le : H' ≤ H := by rw [← hHeq]; exact le_sup_right
      exact hne (Subgroup.eq_of_le_of_card_ge hH'le (by rw [hHc, hH'c])).symm
    · norm_num [h] at hdvd
    · norm_num [h] at hdvd
    · norm_num [h] at hdvd
    · norm_num [h] at hdvd
    · norm_num [h] at hdvd
    · rfl
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hLcard])

private lemma s16e_e9_iSupIndep_fixV [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} (hL : IsElemAbelianOfRank 3 2 ↥L)
    (hfixL : fixV L = ⊥) :
    iSupIndep (fun H : s16e_e9_idx L => fixV H.1) := by
  classical
  haveI : Fintype W := Fintype.ofFinite W
  have hLcard : Nat.card ↥L = 9 := s16e_e9_card_L hL
  intro H
  rw [disjoint_iff]
  apply le_antisymm _ bot_le
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxH, hxSup⟩ := hx
  let N : W →* W :=
    { toFun := fun w => ∏ h : ↥H.1, (h : MulAut W) w
      map_one' := by simp
      map_mul' := by
        intro a b
        change (∏ h : ↥H.1, (h : MulAut W) (a * b)) =
          (∏ h : ↥H.1, (h : MulAut W) a) * (∏ h : ↥H.1, (h : MulAut W) b)
        simp only [map_mul]
        rw [Finset.prod_mul_distrib] }
  have hNx : N x = x := by
    change (∏ h : ↥H.1, (h : MulAut W) x) = x
    have hfix : ∀ h : ↥H.1, (h : MulAut W) x = x := fun h => (mem_fixV.mp hxH) h.1 h.2
    rw [Finset.prod_congr rfl (fun h _ => hfix h), Finset.prod_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, H.2.2]
    rw [show x ^ 3 = x ^ 2 * x by rw [pow_succ], hW x, one_mul]
  have hker : (⨆ (H' : s16e_e9_idx L) (_ : H' ≠ H), fixV H'.1) ≤ N.ker := by
    refine iSup₂_le ?_
    intro H' hH'
    intro w hw
    rw [MonoidHom.mem_ker]
    have hwH' : ∀ h : ↥H.1, (h : MulAut W) w ∈ fixV H'.1 := by
      intro h
      rw [mem_fixV]
      intro k hk
      have hkL : k ∈ L := H'.2.1 hk
      have hhL : (h : MulAut W) ∈ L := H.2.1 h.2
      have hcomm : k * (h : MulAut W) = (h : MulAut W) * k :=
        s16e_e9_mul_comm_coe hL hkL hhL
      calc k ((h : MulAut W) w) = (k * (h : MulAut W)) w := by rw [MulAut.mul_apply]
        _ = ((h : MulAut W) * k) w := by rw [hcomm]
        _ = (h : MulAut W) (k w) := by rw [MulAut.mul_apply]
        _ = (h : MulAut W) w := by rw [mem_fixV.mp hw k hk]
    have hNmem : N w = ∏ h : ↥H.1, (h : MulAut W) w := rfl
    have hNfixH' : N w ∈ fixV H'.1 := by
      rw [hNmem]
      exact Subgroup.prod_mem (fixV H'.1) (fun h _ => hwH' h)
    have hNfixH : N w ∈ fixV H.1 := by
      rw [mem_fixV]
      intro k hk
      have hthis : k (N w) = ∏ h : ↥H.1, (((⟨k, hk⟩ : ↥H.1) * h : ↥H.1) : MulAut W) w := by
        rw [hNmem]
        rw [show k (∏ h : ↥H.1, (h : MulAut W) w) =
          ∏ h : ↥H.1, k ((h : MulAut W) w) from map_prod k.toMonoidHom _ _]
        refine Finset.prod_congr rfl (fun h _ => ?_)
        change k ((h : MulAut W) w) = (k * (h : MulAut W)) w
        rw [MulAut.mul_apply]
      rw [hthis]
      refine Fintype.prod_bijective (fun h : ↥H.1 => (⟨k, hk⟩ : ↥H.1) * h)
        (Group.mulLeft_bijective (⟨k, hk⟩ : ↥H.1)) _ _ (fun h => rfl)
    have hbot : fixV H.1 ⊓ fixV H'.1 = ⊥ := by
      rw [← s16e_e9_fixV_sup,
        s16e_e9_sup_eq_L H.2.1 H'.2.1 H.2.2 H'.2.2 hLcard
          (fun h => hH' (Subtype.ext h).symm), hfixL]
    have : N w ∈ (⊥ : Subgroup W) := by
      rw [← hbot]
      exact Subgroup.mem_inf.mpr ⟨hNfixH, hNfixH'⟩
    exact Subgroup.mem_bot.mp this
  have hxker : x ∈ N.ker := hker hxSup
  rw [MonoidHom.mem_ker, hNx] at hxker
  exact Subgroup.mem_bot.mpr hxker

private lemma s16e_e9_exists_irr_le [Finite W] {L : Subgroup (MulAut W)}
    (hL : IsElemAbelianOfRank 3 2 ↥L) (hfixL : fixV L = ⊥) {X : Subgroup W}
    (hXst : StableUnder L X) (hXne : X ≠ ⊥) :
    ∃ I : Subgroup W, I ∈ irrSet L ∧ I ≤ X := by
  classical
  haveI : Fintype W := Fintype.ofFinite W
  let T : Set (Subgroup W) := {I | I ≤ X ∧ I ≠ ⊥ ∧ StableUnder L I}
  have hT : T.Nonempty := ⟨X, le_rfl, hXne, hXst⟩
  have hex : ∃ m, ∃ I : Subgroup W, I ∈ T ∧ Nat.card I = m := by
    obtain ⟨I, hI⟩ := hT
    exact ⟨Nat.card I, I, hI, rfl⟩
  obtain ⟨I, hIT, hIcard⟩ := Nat.find_spec hex
  have hIle : I ≤ X := hIT.1
  have hIne : I ≠ ⊥ := hIT.2.1
  have hIst : StableUnder L I := hIT.2.2
  have hmin : ∀ J : Subgroup W, J ∈ T → Nat.card I ≤ Nat.card J := by
    intro J hJ
    have h := Nat.find_min' hex ⟨J, hJ, rfl⟩
    rwa [← hIcard] at h
  have hcomm_st : StableUnder L (commSub I L) := by
    intro x hxL
    have hxS : ∀ d ∈ {c | ∃ l ∈ L, ∃ w ∈ I, l w * w⁻¹ = c}, x d ∈ commSub I L := by
      rintro d ⟨l, hlL, w, hwI, rfl⟩
      refine Subgroup.subset_closure ⟨l, hlL, x w, hIst x hxL w hwI, ?_⟩
      have h1 : x (l w) = l (x w) := by
        have hcomm : x * l = l * x := s16e_e9_mul_comm_coe hL hxL hlL
        rw [← MulAut.mul_apply, hcomm, MulAut.mul_apply]
      rw [map_mul, map_inv, h1]
    have hmap_le : (commSub I L).map x.toMonoidHom ≤ commSub I L := by
      rw [commSub, MonoidHom.map_closure, Subgroup.closure_le]
      rintro d ⟨c, hcS, rfl⟩
      exact hxS c hcS
    intro c hc
    exact hmap_le ⟨c, hc, rfl⟩
  have hcomm_le : commSub I L ≤ I := commSub_le_of_invariant hIst
  have hcomm_ne : commSub I L ≠ ⊥ := by
    intro h
    have : I ≤ fixV L := commSub_eq_bot_iff.mp h
    rw [hfixL] at this
    exact hIne (le_bot_iff.mp this)
  have hcomm_eq : commSub I L = I := by
    refine Subgroup.eq_of_le_of_card_ge hcomm_le ?_
    exact hmin (commSub I L) ⟨hcomm_le.trans hIle, hcomm_ne, hcomm_st⟩
  have hIrr : IsIrrOn L I (I ⊓ fixV L) := by
    refine ⟨?_, hIst, ?_, ?_⟩
    · rw [hfixL, inf_bot_eq]
      exact bot_lt_iff_ne_bot.mpr hIne
    · rw [hfixL, inf_bot_eq]
      intro x _ u hu
      rw [Subgroup.mem_bot] at hu ⊢
      rw [hu, map_one]
    · intro J hJst _ hJI
      by_cases hJ : J = ⊥
      · exact Or.inl (by rw [hJ, hfixL, inf_bot_eq])
      · refine Or.inr ?_
        have hJmem : J ∈ T := ⟨hJI.trans hIle, hJ, hJst⟩
        exact Subgroup.eq_of_le_of_card_ge hJI (hmin J hJmem)
  exact ⟨I, ⟨hcomm_eq, hIrr⟩, hIle⟩

private lemma s16e_e9_centSub_map_conj (I : Subgroup W) (g : MulAut W) :
    centSub (I.map g.toMonoidHom) = (centSub I).map (MulAut.conj g).toMonoidHom := by
  ext x
  constructor
  · intro hx
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, ?_, ?_⟩
    · intro y hy
      have h1 : x (g y) = g y := (mem_centSub.mp hx) (g y)
        (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
      show (g⁻¹ * x * g) y = y
      calc (g⁻¹ * x * g) y = g⁻¹ (x (g y)) := by rw [MulAut.mul_apply, MulAut.mul_apply]
        _ = g⁻¹ (g y) := by rw [h1]
        _ = y := by simp
    · show (MulAut.conj g) (g⁻¹ * x * g) = x
      change g * (g⁻¹ * x * g) * g⁻¹ = x
      group
  · rintro ⟨y, hy, rfl⟩
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    have hyw : y w = w := (mem_centSub.mp hy) w hw
    show (MulAut.conj g) y (g w) = g w
    calc (MulAut.conj g) y (g w) = g (y (g⁻¹ (g w))) := by
          rw [MulAut.conj_apply, MulAut.mul_apply, MulAut.mul_apply]
      _ = g (y w) := by rw [show g⁻¹ (g w) = w by simp]
      _ = g w := by rw [hyw]

private lemma s16e_e9_ptStab_eq_of_secIsoOn {L : Subgroup (MulAut W)} {I J : Subgroup W}
    (h : SecIsoOn L I ⊥ J ⊥) : L ⊓ centSub I = L ⊓ centSub J := by
  rcases h with ⟨-, -, hstabI, -, hstabJ, -, β, hβJ, hβker, hβsurj, hβint⟩
  have hβinj : Function.Injective β := by
    intro a b hab
    have h1 : a * b⁻¹ = 1 := by
      have hb : β (a * b⁻¹) ∈ (⊥ : Subgroup W) := by
        rw [Subgroup.mem_bot, map_mul, map_inv, hab, mul_inv_cancel]
      exact Subtype.ext (Subgroup.mem_bot.mp ((hβker (a * b⁻¹)).mp hb))
    exact mul_inv_eq_one.mp h1
  ext x
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  constructor
  · rintro ⟨hxL, hxI⟩
    refine ⟨hxL, ?_⟩
    rw [mem_centSub] at hxI ⊢
    intro y hy
    obtain ⟨a, ha⟩ := hβsurj y hy
    rw [Subgroup.mem_bot, mul_inv_eq_one] at ha
    rw [← ha]
    have hxa : x a ∈ I := hstabI x hxL a a.2
    have hkey := hβint x hxL a ⟨x a, hxa⟩ rfl
    rw [Subgroup.mem_bot, mul_inv_eq_one] at hkey
    rw [← hkey]
    congr 1
    exact Subtype.ext (hxI a a.2)
  · rintro ⟨hxL, hxJ⟩
    refine ⟨hxL, ?_⟩
    rw [mem_centSub] at hxJ ⊢
    intro a ha
    have hxa : x a ∈ I := hstabI x hxL a ha
    have hkey := hβint x hxL ⟨a, ha⟩ ⟨x a, hxa⟩ rfl
    rw [Subgroup.mem_bot, mul_inv_eq_one] at hkey
    have h1 : β ⟨x a, hxa⟩ = β ⟨a, ha⟩ := by
      rw [hkey, hxJ (β ⟨a, ha⟩) (hβJ ⟨a, ha⟩)]
    exact congrArg Subtype.val (hβinj h1)

private lemma s16e_e9_eq_of_card_three_le [Finite W] {L C H : Subgroup (MulAut W)}
    (hHL : H ≤ L) (hHc : Nat.card H = 3) (hHC : H ≤ C) (hCL : C ≤ L) (hLcard : Nat.card ↥L = 9)
    (hCne : C ≠ L) : C = H := by
  have hHdvd : Nat.card H ∣ Nat.card C := Subgroup.card_dvd_of_le hHC
  rw [hHc] at hHdvd
  have hCdvd : Nat.card C ∣ Nat.card ↥L := Subgroup.card_dvd_of_le hCL
  rw [hLcard] at hCdvd
  have hle9 : Nat.card C ≤ 9 := Nat.le_of_dvd (by norm_num) hCdvd
  have hge3 : 3 ≤ Nat.card C := Nat.le_of_dvd (by norm_num) hHdvd
  have hcard : Nat.card C = 3 := by
    interval_cases h : Nat.card C
    · rfl
    · norm_num [h] at hCdvd
    · norm_num [h] at hCdvd
    · norm_num [h] at hCdvd
    · norm_num [h] at hCdvd
    · norm_num [h] at hCdvd
    · exfalso
      exact hCne (Subgroup.eq_of_le_of_card_ge hCL (by rw [h, hLcard]))
  exact (Subgroup.eq_of_le_of_card_ge hHC (by rw [hcard, hHc])).symm

private lemma s16e_e9_conj_of_ne_bot [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L A : Subgroup (MulAut W)} (hLA : L ≤ A)
    (hLn : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L)
    (hL : IsElemAbelianOfRank 3 2 ↥L) (hfixL : fixV L = ⊥) (htr : IrrSpanTrans A L)
    {H H' : Subgroup (MulAut W)} (hHL : H ≤ L) (hHc : Nat.card H = 3)
    (hHne : fixV H ≠ ⊥) (hH'L : H' ≤ L) (hH'c : Nat.card H' = 3) (hH'ne : fixV H' ≠ ⊥) :
    ∃ g ∈ A, H.map (MulAut.conj g).toMonoidHom = H' := by
  have hLcard : Nat.card ↥L = 9 := s16e_e9_card_L hL
  obtain ⟨I, hIirr, hIle⟩ := s16e_e9_exists_irr_le hL hfixL
    (s16e_e9_stableUnder_fixV hL H hHL) hHne
  obtain ⟨J, hJirr, hJle⟩ := s16e_e9_exists_irr_le hL hfixL
    (s16e_e9_stableUnder_fixV hL H' hH'L) hH'ne
  obtain ⟨g, hgA, hsec⟩ := htr.2 I hIirr J hJirr
  rw [hfixL, sup_bot_eq, sup_bot_eq] at hsec
  have hpt := s16e_e9_ptStab_eq_of_secIsoOn hsec
  have hIne : I ≠ ⊥ := by
    intro h
    have hlt := hIirr.2.1
    rw [h, bot_inf_eq] at hlt
    exact absurd hlt (lt_irrefl (⊥ : Subgroup W))
  have hHcent : H ≤ centSub I := by
    intro h hh
    rw [mem_centSub]
    intro y hy
    exact mem_fixV.mp (hIle hy) h hh
  have hCne : L ⊓ centSub I ≠ L := by
    intro h
    have hLI : L ≤ centSub I := h ▸ inf_le_right
    have hIbot : I ≤ fixV L := by
      intro y hy
      rw [mem_fixV]
      intro x hx
      exact mem_centSub.mp (hLI hx) y hy
    rw [hfixL] at hIbot
    exact hIne (le_bot_iff.mp hIbot)
  have hIH : L ⊓ centSub I = H :=
    s16e_e9_eq_of_card_three_le hHL hHc (le_inf hHL hHcent) inf_le_left hLcard hCne
  have hH'cent : H' ≤ centSub J := by
    intro h hh
    rw [mem_centSub]
    intro y hy
    exact mem_fixV.mp (hJle hy) h hh
  have hCne' : L ⊓ centSub J ≠ L := by
    intro h
    have hLJ : L ≤ centSub J := h ▸ inf_le_right
    have hJbot : J ≤ fixV L := by
      intro y hy
      rw [mem_fixV]
      intro x hx
      exact mem_centSub.mp (hLJ hx) y hy
    rw [hfixL] at hJbot
    have hJne : J ≠ ⊥ := by
      intro h
      have hlt := hJirr.2.1
      rw [h, bot_inf_eq] at hlt
      exact absurd hlt (lt_irrefl (⊥ : Subgroup W))
    exact hJne (le_bot_iff.mp hJbot)
  have hJH : L ⊓ centSub J = H' :=
    s16e_e9_eq_of_card_three_le hH'L hH'c (le_inf hH'L hH'cent) inf_le_left hLcard hCne'
  have hmap : (L ⊓ centSub I).map (MulAut.conj g).toMonoidHom =
      L ⊓ centSub (I.map g.toMonoidHom) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hLn g hgA,
      s16e_e9_centSub_map_conj]
  refine ⟨g, hgA, ?_⟩
  rw [← hIH, hmap, hpt, hJH]

private lemma s16e_e9_rk_eq_of_ne_bot [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L A : Subgroup (MulAut W)} (hLA : L ≤ A)
    (hLn : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L)
    (hL : IsElemAbelianOfRank 3 2 ↥L) (hfixL : fixV L = ⊥) (htr : IrrSpanTrans A L)
    {H H' : Subgroup (MulAut W)} (hHL : H ≤ L) (hHc : Nat.card H = 3)
    (hHne : fixV H ≠ ⊥) (hH'L : H' ≤ L) (hH'c : Nat.card H' = 3) (hH'ne : fixV H' ≠ ⊥) :
    rk ↥(fixV H) = rk ↥(fixV H') := by
  obtain ⟨g, -, hg⟩ :=
    s16e_e9_conj_of_ne_bot hW hLA hLn hL hfixL htr hHL hHc hHne hH'L hH'c hH'ne
  have hcard : Nat.card ↥(fixV H) = Nat.card ↥(fixV H') := by
    rw [← hg, Asc81c.fixV_map_conj H g,
      Subgroup.card_map_of_injective g.injective]
  rw [card_eq_two_pow hW (fixV H), card_eq_two_pow hW (fixV H')] at hcard
  exact Nat.pow_right_injective (by norm_num : 1 < 2) hcard

private lemma s16e_e9_two_pow_even (k : ℕ) : (2 : ℕ) ^ (2 * k) ≡ 1 [MOD 3] := by
  induction k with
  | zero => exact Nat.ModEq.refl 1
  | succ k ih =>
    have h : (2 : ℕ) ^ (2 * (k + 1)) = 2 ^ (2 * k) * 4 := by
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]
      norm_num
    rw [h]
    have h4 : (4 : ℕ) ≡ 1 [MOD 3] := by decide
    exact ih.mul h4

private lemma s16e_e9_two_pow_odd (k : ℕ) : (2 : ℕ) ^ (2 * k + 1) ≡ 2 [MOD 3] := by
  have h : (2 : ℕ) ^ (2 * k + 1) = 2 ^ (2 * k) * 2 := by rw [pow_succ]
  rw [h]
  simpa using (s16e_e9_two_pow_even k).mul (Nat.ModEq.refl 2)

private lemma s16e_e9_even_of_two_pow_modeq_one {n : ℕ} (h : (2 : ℕ) ^ n ≡ 1 [MOD 3]) :
    Even n := by
  rcases Nat.even_or_odd n with he | ho
  · exact he
  · exfalso
    obtain ⟨k, rfl⟩ := ho
    have h2 := s16e_e9_two_pow_odd k
    have : (1 : ℕ) ≡ 2 [MOD 3] := h.symm.trans h2
    norm_num [Nat.ModEq] at this

private lemma s16e_e9_even_rk_fixV [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hcardW : Nat.card W = 2 ^ 6) {L : Subgroup (MulAut W)}
    (hL : IsElemAbelianOfRank 3 2 ↥L) {H : Subgroup (MulAut W)}
    (hHL : H ≤ L) (hHc : Nat.card H = 3) : Even (rk ↥(fixV H)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hHne : H ≠ ⊥ := by intro h; rw [h, Subgroup.card_bot] at hHc; norm_num at hHc
  obtain ⟨h, hhne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hHne
  set hA : MulAut W := (h : MulAut W) with hhA
  have hhH : hA ∈ H := h.2
  have hhne' : hA ≠ 1 := fun h1 => hhne (Subtype.ext h1)
  have hh3 : hA ^ 3 = 1 := by
    have h' := s16e_e9_pow_three hL ⟨hA, hHL hhH⟩
    simpa using congrArg Subtype.val h'
  have hord : orderOf hA = 3 := by
    have hdvd : orderOf hA ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hh3
    have hle : orderOf hA ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    have hne1 : orderOf hA ≠ 1 := fun h1 => hhne' (orderOf_eq_one_iff.mp h1)
    have hne2 : orderOf hA ≠ 2 := by intro h2; rw [h2] at hdvd; norm_num at hdvd
    have hpos : 1 ≤ orderOf hA := orderOf_pos hA
    omega
  have hzpH : Subgroup.zpowers hA = H := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hhH)
    rw [Nat.card_zpowers, hord, hHc]
  have hset : ∀ x : W, x ∈ fixV (Subgroup.zpowers hA) ↔ hA x = x := by
    intro x
    rw [mem_fixV]
    constructor
    · intro hx; exact hx hA (Subgroup.mem_zpowers hA)
    · intro hx y hy
      rw [Subgroup.mem_zpowers_iff] at hy
      obtain ⟨n, rfl⟩ := hy
      have ha_inv : hA⁻¹ x = x := by
        calc hA⁻¹ x = hA⁻¹ (hA x) := by rw [hx]
          _ = x := by simp
      exact zpow_induction_right (g := hA) (P := fun g => g x = x)
        (by rw [MulAut.one_apply])
        (fun g hg => by rw [MulAut.mul_apply, hx, hg])
        (fun g hg => by rw [MulAut.mul_apply, ha_inv, hg]) n
  have hcardfix : Nat.card (fixV H) = Nat.card {x : W // hA x = x} := by
    rw [← hzpH]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun x => hset x))
  have hmod := CFSG.HardMathSupport.Lang.Proving.card_modEq_card_fixedPoints_of_pow_prime
    (K := W) hA (p := 3) hh3
  rw [hcardW] at hmod
  have h64 : (64 : ℕ) ≡ 1 [MOD 3] := by decide
  have hfix1 : Nat.card {x : W // hA x = x} ≡ 1 [MOD 3] := hmod.symm.trans h64
  rw [← hcardfix, card_eq_two_pow hW (fixV H)] at hfix1
  exact s16e_e9_even_of_two_pow_modeq_one hfix1

private lemma s16e_e9_card_iSup_finset [Finite W] {ι : Type*} (s : Finset ι)
    {f : ι → Subgroup W} (h : iSupIndep f) :
    Nat.card ↥(⨆ i ∈ s, f i) = ∏ i ∈ s, Nat.card ↥(f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.iSup_insert, Finset.prod_insert ha]
    have hdisj : Disjoint (f a) (⨆ i ∈ s, f i) := by
      rw [iSupIndep_def] at h
      exact Disjoint.mono_right (iSup₂_le fun i hi => le_iSup₂_of_le i (by
        rintro rfl; exact ha hi) le_rfl) (h a)
    have hcard := card_sup_mul_card_inf (f a) (⨆ i ∈ s, f i)
    rw [hdisj.eq_bot, Subgroup.card_bot, mul_one] at hcard
    rw [hcard, ih]

private lemma s16e_e9_count {ι : Type*} [Fintype ι] (f : ι → ℕ)
    (hsum : ∑ i, f i = 6) (heven : ∀ i, Even (f i))
    (hconst : ∀ i j, f i ≠ 0 → f j ≠ 0 → f i = f j) (hne6 : ∀ i, f i ≠ 6) :
    (Finset.univ.filter (fun i => f i ≠ 0)).card = 3 ∧ ∀ i, f i ≠ 0 → f i = 2 := by
  classical
  set S := Finset.univ.filter (fun i => f i ≠ 0) with hS
  have hsumS : ∑ i ∈ S, f i = 6 := by
    rw [← hsum]
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro i _ hi
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact not_not.mp hi
  have hSne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hsumS
    exact absurd hsumS (by norm_num)
  obtain ⟨i₀, hi₀⟩ := hSne
  have hfi₀ : f i₀ ≠ 0 := by simpa [hS] using hi₀
  set c := f i₀ with hc
  have hc0 : c ≠ 0 := hfi₀
  have hconstS : ∀ i ∈ S, f i = c := by
    intro i hi
    exact hconst i i₀ (by simpa [hS] using hi) hfi₀
  have hSsumc : S.card * c = 6 := by
    rw [← hsumS, Finset.sum_congr rfl hconstS, Finset.sum_const, smul_eq_mul]
  have hcdvd : c ∣ 6 := ⟨S.card, by rw [mul_comm]; exact hSsumc.symm⟩
  have hc2 : c = 2 := by
    obtain ⟨k, hk⟩ := heven i₀
    rw [← hc] at hk
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hc0 (by omega)
    have hk1 : k ≤ 3 := by
      have hle : k + k ≤ 6 := Nat.le_of_dvd (by norm_num) (by rwa [hk] at hcdvd)
      omega
    have hk2 : k ≠ 2 := by
      rintro rfl
      rw [show c = 2 + 2 from hk] at hcdvd
      norm_num at hcdvd
    have hk3 : k ≠ 3 := by
      rintro rfl
      exact hne6 i₀ (by rw [← hc, hk])
    omega
  have hScard : S.card = 3 := by
    rw [hc2] at hSsumc
    omega
  refine ⟨hScard, ?_⟩
  intro i hi
  rw [hconst i i₀ hi hfi₀]
  exact hc.symm.trans hc2

theorem s16e_symSum_two_of_E9 [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hcard : Nat.card W = 2 ^ 6) {A L : Subgroup (MulAut W)} (hLA : L ≤ A)
    (hLn : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L)
    (hL : IsElemAbelianOfRank 3 2 ↥L) (hWL : commSub ⊤ L = ⊤) (htr : IrrSpanTrans A L)
    (hO3 : ∀ N : Subgroup ↥A, N.Normal → N.index ≠ 3) : SymSumOfConj A ⊤ 2 2 := by
  classical
  haveI : Fintype W := Fintype.ofFinite W
  have hfixL : fixV L = ⊥ := s16e_e9_fixV_eq_bot hW hL hWL
  have hLcard : Nat.card ↥L = 9 := s16e_e9_card_L hL
  have hsup : (⨆ H : s16e_e9_idx L, fixV H.1) = ⊤ := s16e_e9_iSup_fixV_eq_top hW hL
  have hind : iSupIndep (fun H : s16e_e9_idx L => fixV H.1) :=
    s16e_e9_iSupIndep_fixV hW hL hfixL
  have hprod : Nat.card W = ∏ H : s16e_e9_idx L, Nat.card ↥(fixV H.1) := by
    have key := s16e_e9_card_iSup_finset (Finset.univ) hind
    simp only [Finset.mem_univ, iSup_true] at key
    rw [show Nat.card W = Nat.card ↥(⊤ : Subgroup W) by rw [Subgroup.card_top], ← hsup]
    exact key
  have hsum : ∑ H : s16e_e9_idx L, rk ↥(fixV H.1) = 6 := by
    have h1 : Nat.card W = 2 ^ (∑ H : s16e_e9_idx L, rk ↥(fixV H.1)) := by
      rw [hprod]
      rw [show (∏ H : s16e_e9_idx L, Nat.card ↥(fixV H.1)) =
        ∏ H : s16e_e9_idx L, 2 ^ rk ↥(fixV H.1) from
        Finset.prod_congr rfl (fun H _ => card_eq_two_pow hW _)]
      rw [Finset.prod_pow_eq_pow_sum]
    rw [hcard] at h1
    exact Nat.pow_right_injective (by norm_num : 1 < 2) h1.symm
  have heven : ∀ H : s16e_e9_idx L, Even (rk ↥(fixV H.1)) :=
    fun H => s16e_e9_even_rk_fixV hW hcard hL H.2.1 H.2.2
  have hconst : ∀ H H' : s16e_e9_idx L, rk ↥(fixV H.1) ≠ 0 → rk ↥(fixV H'.1) ≠ 0 →
      rk ↥(fixV H.1) = rk ↥(fixV H'.1) := by
    intro H H' hH hH'
    refine s16e_e9_rk_eq_of_ne_bot hW hLA hLn hL hfixL htr
      H.2.1 H.2.2 ?_ H'.2.1 H'.2.2 ?_
    · exact fun h => hH ((rk_eq_zero_iff hW).mpr h)
    · exact fun h => hH' ((rk_eq_zero_iff hW).mpr h)
  have hne6 : ∀ H : s16e_e9_idx L, rk ↥(fixV H.1) ≠ 6 := by
    intro H hrk
    have htop : fixV H.1 = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [card_eq_two_pow hW (fixV H.1), hrk, hcard]
    have hHbot : H.1 = ⊥ := by
      rw [eq_bot_iff]
      intro h hh
      rw [Subgroup.mem_bot]
      ext x
      exact mem_fixV.mp (htop ▸ Subgroup.mem_top x) h hh
    have hc3 := H.2.2
    rw [hHbot, Subgroup.card_bot] at hc3
    norm_num at hc3
  obtain ⟨hScard, hSval⟩ := s16e_e9_count (fun H : s16e_e9_idx L => rk ↥(fixV H.1))
    hsum heven hconst hne6
  set S : Finset (s16e_e9_idx L) :=
    Finset.univ.filter (fun H : s16e_e9_idx L => rk ↥(fixV H.1) ≠ 0) with hS
  have hScard' : S.card = 3 := by simpa [hS] using hScard
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨H₀, hH₀⟩ := hSne
  have hH₀ne : fixV H₀.1 ≠ ⊥ := by
    have hk : rk ↥(fixV H₀.1) ≠ 0 := by simpa [hS] using hH₀
    exact fun h => hk ((rk_eq_zero_iff hW).mpr h)
  have hH₀rk : rk ↥(fixV H₀.1) = 2 :=
    hSval H₀ (fun h => hH₀ne ((rk_eq_zero_iff hW).mp h))
  let Z : Subgroup W := fixV H₀.1
  have hfixV_Z : ∀ g : MulAut W,
      Z.map g.toMonoidHom = fixV (H₀.1.map (MulAut.conj g).toMonoidHom) := by
    intro g
    show (fixV H₀.1).map g.toMonoidHom = fixV (H₀.1.map (MulAut.conj g).toMonoidHom)
    rw [← Asc81c.fixV_map_conj H₀.1 g]
  have hnotbot : ∀ g : MulAut W, Z.map g.toMonoidHom ≠ ⊥ := by
    intro g h
    have hcardZ : Nat.card ↥Z = 2 ^ 2 := by
      show Nat.card ↥(fixV H₀.1) = 2 ^ 2
      rw [card_eq_two_pow hW (fixV H₀.1), hH₀rk]
    have h1 : Nat.card ↥(Z.map g.toMonoidHom) = 1 := by rw [h]; exact Subgroup.card_bot
    rw [Subgroup.card_map_of_injective g.injective, hcardZ] at h1
    norm_num at h1
  have hZFix : ∀ {H : s16e_e9_idx L}, H ∈ S → fixV H.1 ≠ ⊥ := by
    intro H hH
    have hk : rk ↥(fixV H.1) ≠ 0 := by simpa [hS] using hH
    exact fun h => hk ((rk_eq_zero_iff hW).mpr h)
  have hconj_eq : conjSubs A Z = (fun H : s16e_e9_idx L => fixV H.1) '' (S : Set _) := by
    ext X
    constructor
    · rintro ⟨g, hgA, rfl⟩
      refine ⟨⟨H₀.1.map (MulAut.conj g).toMonoidHom, ?_, ?_⟩, ?_, ?_⟩
      · exact (Subgroup.map_mono H₀.2.1).trans (le_of_eq (hLn g hgA))
      · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]; exact H₀.2.2
      · rw [Finset.mem_coe, hS]
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        intro hzero
        rw [rk_eq_zero_iff hW, ← hfixV_Z g] at hzero
        exact absurd hzero (hnotbot g)
      · show fixV (H₀.1.map (MulAut.conj g).toMonoidHom) = Z.map (g : MulAut W).toMonoidHom
        rw [hfixV_Z g]
    · rintro ⟨H, hH, rfl⟩
      obtain ⟨g, hgA, hg⟩ := s16e_e9_conj_of_ne_bot hW hLA hLn hL hfixL htr
        H₀.2.1 H₀.2.2 hH₀ne H.2.1 H.2.2 (hZFix hH)
      refine ⟨g, hgA, ?_⟩
      rw [hfixV_Z g, hg]
  have hInjS : Set.InjOn (fun H : s16e_e9_idx L => fixV H.1) (S : Set (s16e_e9_idx L)) :=
    fun H hH H' hH' heq => hind.injOn (hZFix hH) (hZFix hH') heq
  have hindS : iSupIndep (fun H : (S : Set (s16e_e9_idx L)) => fixV H.1.1) := by
    intro H
    refine (hind H.1).mono_right ?_
    refine iSup_le fun H' => iSup_le fun hH' => ?_
    refine le_iSup₂_of_le H'.1 (fun h => hH' (Subtype.ext h)) le_rfl
  have hZsInd : sSupIndep (conjSubs A Z) := by
    rw [hconj_eq, Set.image_eq_range]
    exact hindS.sSupIndep_range
  have hZssup : sSup (conjSubs A Z) = ⊤ := by
    rw [hconj_eq]
    refine le_antisymm le_top ?_
    rw [← hsup]
    refine iSup_le fun H => ?_
    by_cases hH : H ∈ S
    · exact le_sSup ⟨H, hH, rfl⟩
    · have hz : rk ↥(fixV H.1) = 0 := by
        by_contra hz
        exact hH (by simpa [hS] using hz)
      have hHz : fixV H.1 = ⊥ := (rk_eq_zero_iff hW).mp hz
      rw [hHz]; exact bot_le
  have hZncard : (conjSubs A Z).ncard = 3 := by
    rw [hconj_eq, hInjS.ncard_image, Set.ncard_coe_finset, hScard']
  haveI : Finite ↥(conjSubs A Z) := by
    haveI : Finite (Subgroup W) := by
      haveI : Fintype (Subgroup W) :=
        Fintype.ofInjective (fun X : Subgroup W => (X : Set W)) SetLike.coe_injective
      exact Finite.of_fintype _
    exact Subtype.finite
  have hcardXs : Nat.card ↥(conjSubs A Z) = 3 := by
    rw [Nat.card_coe_set_eq]; exact hZncard
  have hmemAct : ∀ (a : ↥A) (Y : ↥(conjSubs A Z)),
      ((Y : Subgroup W).map (a : MulAut W).toMonoidHom) ∈ conjSubs A Z := by
    intro a Y
    obtain ⟨g, hg, hgY⟩ := Y.2
    refine ⟨(a : MulAut W) * g, A.mul_mem a.2 hg, ?_⟩
    rw [hgY, Subgroup.map_map]; rfl
  letI : MulAction ↥A ↥(conjSubs A Z) :=
    { smul := fun a Y => ⟨(Y : Subgroup W).map (a : MulAut W).toMonoidHom, hmemAct a Y⟩
      one_smul := by
        intro Y; apply Subtype.ext
        show (Y : Subgroup W).map (MonoidHom.id W) = (Y : Subgroup W)
        rw [Subgroup.map_id]
      mul_smul := by
        intro a b Y; apply Subtype.ext
        show (Y : Subgroup W).map (((a * b : ↥A) : MulAut W)).toMonoidHom =
          ((Y : Subgroup W).map (b : MulAut W).toMonoidHom).map (a : MulAut W).toMonoidHom
        rw [Subgroup.map_map]; rfl }
  have hHof : ∀ Y : ↥(conjSubs A Z), ∃ H : s16e_e9_idx L, (Y : Subgroup W) = fixV H.1 := by
    intro Y
    obtain ⟨g, hgA, hgY⟩ := Y.2
    refine ⟨⟨H₀.1.map (MulAut.conj g).toMonoidHom, ?_, ?_⟩, ?_⟩
    · exact (Subgroup.map_mono H₀.2.1).trans (le_of_eq (hLn g hgA))
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]; exact H₀.2.2
    · rw [hgY, hfixV_Z g]
  let Hof : ↥(conjSubs A Z) → s16e_e9_idx L := fun Y => Classical.choose (hHof Y)
  have Hof_spec : ∀ Y : ↥(conjSubs A Z), (Y : Subgroup W) = fixV (Hof Y).1 :=
    fun Y => Classical.choose_spec (hHof Y)
  have Hof_ne : ∀ Y, fixV (Hof Y).1 ≠ ⊥ := by
    intro Y h
    obtain ⟨g, hg, hgY⟩ := Y.2
    have h1 : Z.map (g : MulAut W).toMonoidHom = ⊥ := by
      rw [← hgY, Hof_spec Y, h]
    exact absurd h1 (hnotbot g)
  have htrans : ∀ Y Y' : ↥(conjSubs A Z), ∃ a : ↥A, a • Y = Y' := by
    intro Y Y'
    obtain ⟨g, hgA, hg⟩ := s16e_e9_conj_of_ne_bot hW hLA hLn hL hfixL htr
      (Hof Y).2.1 (Hof Y).2.2 (Hof_ne Y) (Hof Y').2.1 (Hof Y').2.2 (Hof_ne Y')
    refine ⟨⟨g, hgA⟩, Subtype.ext ?_⟩
    show (Y : Subgroup W).map g = (Y' : Subgroup W)
    rw [Hof_spec Y]
    change (fixV (Hof Y).1).map g.toMonoidHom = (Y' : Subgroup W)
    rw [← Asc81c.fixV_map_conj (Hof Y).1 g, hg, Hof_spec Y']
  let Y₀ : ↥(conjSubs A Z) := ⟨Z, 1, A.one_mem, by
    show Z = Z.map (1 : MulAut W).toMonoidHom
    rw [show (1 : MulAut W).toMonoidHom = MonoidHom.id W from rfl, Subgroup.map_id]⟩
  let ρ : ↥A →* Equiv.Perm ↥(conjSubs A Z) := MulAction.toPermHom ↥A ↥(conjSubs A Z)
  have hsurj : Function.Surjective
      (fun σ : ↥(ρ.range) => (σ : Equiv.Perm ↥(conjSubs A Z)) • Y₀) := by
    intro Y'
    obtain ⟨a, ha⟩ := htrans Y₀ Y'
    refine ⟨⟨ρ a, ⟨a, rfl⟩⟩, ?_⟩
    change (a • Y₀ : ↥(conjSubs A Z)) = Y'
    exact ha
  have hge3 : 3 ≤ Nat.card ↥(ρ.range) := by
    have hle := Nat.card_le_card_of_surjective _ hsurj
    rwa [hcardXs] at hle
  have hdvd : Nat.card ↥(ρ.range) ∣ 6 := by
    have h1 := Subgroup.card_subgroup_dvd_card ρ.range
    have hperm : Nat.card (Equiv.Perm ↥(conjSubs A Z)) = 6 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card, hcardXs]
      norm_num
    rwa [hperm] at h1
  have hcard6 : Nat.card ↥(ρ.range) = 6 := by
    have hle6 : Nat.card ↥(ρ.range) ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    have hn4 : Nat.card ↥(ρ.range) ≠ 4 := by
      intro h; rw [h] at hdvd; norm_num at hdvd
    have hn5 : Nat.card ↥(ρ.range) ≠ 5 := by
      intro h; rw [h] at hdvd; norm_num at hdvd
    have hcases : Nat.card ↥(ρ.range) = 3 ∨ Nat.card ↥(ρ.range) = 6 := by omega
    rcases hcases with h3 | h6
    · exfalso
      have hker : ρ.ker.index = 3 := by rw [Subgroup.index_ker]; exact h3
      exact hO3 ρ.ker inferInstance hker
    · exact h6
  have htop : ρ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hcard6]
    exact (show Nat.card (Equiv.Perm ↥(conjSubs A Z)) = 6 from by
      rw [Nat.card_perm, hcardXs]; norm_num).symm
  refine ⟨Z, hH₀rk, hZsInd, hZssup, hZncard, ?_⟩
  intro π
  have hπ : π ∈ ρ.range := htop ▸ Subgroup.mem_top π
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hπ
  refine ⟨a, a.2, fun Y => ?_⟩
  have h1 : ((ρ a) Y : Subgroup W) = (π Y : Subgroup W) :=
    congrArg (fun σ : Equiv.Perm ↥(conjSubs A Z) =>
      ((σ Y : ↥(conjSubs A Z)) : Subgroup W)) ha
  have h2 : ((ρ a) Y : Subgroup W) = (Y : Subgroup W).map (a : MulAut W).toMonoidHom := by
    change (((a • Y : ↥(conjSubs A Z)) : Subgroup W)) =
      (Y : Subgroup W).map (a : MulAut W).toMonoidHom
    rfl
  rw [← h2]
  exact h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
