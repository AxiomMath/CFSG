module

public import CFSG.Quasithin.Vol2.Ch9Sec4Model
public import CFSG.Quasithin.Vol2.Ch9Lem935

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix

theorem commutator_eq_self_of_oTwoUpper {A B : Type*} [Group A] [Group B] [Finite A]
    {H : Subgroup A} (hH : oTwoUpper H = H) (f : ↥H →* B)
    (hperf : ⁅f.range, f.range⁆ = f.range) (h2 : IsPGroup 2 ↥f.ker) : ⁅H, H⁆ = H := by
  have hle : ⁅H, H⁆ ≤ H := Subgroup.commutator_le.mpr fun a ha b hb =>
    H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
  have hcomm : ⁅H, H⁆ = (commutator ↥H).map H.subtype := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  refine le_antisymm hle ?_
  conv_lhs => rw [← hH]
  rw [oTwoUpper, Subgroup.closure_le]
  rintro x ⟨hxH, hxo⟩
  have hfx : f ⟨x, hxH⟩ ∈ (commutator ↥H).map f := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, hperf]
    exact ⟨_, rfl⟩
  obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp hfx
  have hy : c⁻¹ * ⟨x, hxH⟩ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcx, inv_mul_cancel]
  obtain ⟨k, hk⟩ := h2 ⟨_, hy⟩
  have hk' : (c⁻¹ * ⟨x, hxH⟩) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hof : Abelianization.of c = 1 := by
    rw [← MonoidHom.mem_ker, Abelianization.ker_of]
    exact hc
  set a : Abelianization ↥H := Abelianization.of ⟨x, hxH⟩ with ha
  have hax : a = Abelianization.of (c⁻¹ * ⟨x, hxH⟩) := by
    rw [map_mul, map_inv, hof, inv_one, one_mul]
  have ha2 : a ^ 2 ^ k = 1 := by rw [hax, ← map_pow, hk', map_one]
  have hao : a ^ orderOf x = 1 := by
    rw [ha, ← map_pow]
    have : (⟨x, hxH⟩ : ↥H) ^ orderOf x = 1 := Subtype.ext (by simp [pow_orderOf_eq_one])
    rw [this, map_one]
  have hcop : Nat.Coprime (2 ^ k) (orderOf x) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hxo)
  have ha1 : a = 1 := by
    have h1 := orderOf_dvd_of_pow_eq_one ha2
    have h2' := orderOf_dvd_of_pow_eq_one hao
    have h3 : orderOf a ∣ 1 := by
      rw [← Nat.Coprime.gcd_eq_one hcop]
      exact Nat.dvd_gcd h1 h2'
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  have hmem : (⟨x, hxH⟩ : ↥H) ∈ commutator ↥H := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    exact ha1
  rw [hcomm]
  exact ⟨_, hmem, rfl⟩

theorem mem_cComp_self_of_hom {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    {H : Subgroup A} (hH : ⁅H, H⁆ = H) (f : ↥H →* B) (hq : CFSG.IsQuasisimple ↥f.range)
    (hN : Group.IsSolvable ↥f.ker) : H ∈ cComp H := by
  have hJ : (⊤ : Subgroup ↥f.range) ∈ cComp (⊤ : Subgroup ↥f.range) := by
    refine mem_cComp_top_of_isComponent ⟨?_, Subgroup.IsSubnormal.top⟩
    exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr Subgroup.topEquiv).mpr hq
  let e : (↥H ⧸ f.ker) ≃* ↥f.range := QuotientGroup.quotientKerEquivRange f
  have hQ : (⊤ : Subgroup (↥H ⧸ f.ker)) ∈ cComp (⊤ : Subgroup (↥H ⧸ f.ker)) := by
    have h := cComp_map_mulEquiv e.symm hJ
    have hsurj : Function.Surjective e.symm.toMonoidHom := e.symm.surjective
    rwa [Subgroup.map_top_of_surjective _ hsurj] at h
  obtain ⟨L₁, hL₁, hL₁π⟩ := (cComp_quotient_bijOn f.ker hN).surjOn hQ
  have h1 : L₁ ⊔ f.ker = ⊤ := by
    have h := congrArg (Subgroup.comap (QuotientGroup.mk' f.ker)) hL₁π
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at h
  have hperf : ⁅(⊤ : Subgroup ↥H), ⊤⁆ = ⊤ :=
    (Subgroup.isPerfect_iff.mpr hH).commutator_eq_top
  have h2 := (cComp_commutator_perfectCore hL₁ le_top hN Subgroup.le_normalizer_of_normal).2
  rw [h1, perfectCore_eq_self_of_perfect hperf] at h2
  rw [← h2] at hL₁
  have h3 := map_subtype_mem_cComp hL₁
  rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h3

theorem isQuasisimple_of_isSimpleGroup {Q : Type*} [Group Q] [hs : IsSimpleGroup Q]
    (hnab : ∃ a b : Q, a * b ≠ b * a) (hperf : Group.IsPerfect Q) : CFSG.IsQuasisimple Q := by
  have hZ : Subgroup.center Q = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have hb : b ∈ Subgroup.center Q := h ▸ Subgroup.mem_top b
      exact Subgroup.mem_center_iff.mp hb a
  let e : Q ⧸ Subgroup.center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have : Nontrivial (Q ⧸ Subgroup.center Q) := e.toEquiv.nontrivial
  refine ⟨hperf, IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective,
    ?_⟩
  obtain ⟨a, b, hab⟩ := hnab
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

namespace Om4Pt

variable {K : Type} [Field K]

theorem isQuasisimple_dgM [CharP K 2] [Finite K] (h4 : 4 ≤ Nat.card K)
    {X₀ : Matrix (Fin 2) (Fin 2) K} (hX : X₀.det ≠ 0) : CFSG.IsQuasisimple ↥(dgM X₀) := by
  have hs := Om4.sl2_isSimple h4
  have hperf : Group.IsPerfect (SpecialLinearGroup (Fin 2) K) :=
    ⟨(Om4.sl2_commutator_eq_top h4)⟩
  have hnab : ∃ a b : SpecialLinearGroup (Fin 2) K, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have : ⁅(⊤ : Subgroup (SpecialLinearGroup (Fin 2) K)), ⊤⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun a _ b _ => (h b a)
    rw [Om4.sl2_commutator_eq_top h4] at this
    exact hs.toNontrivial.exists_pair_ne.elim fun a ha => ha.elim fun b hb => hb (by
      have h1 : a ∈ (⊤ : Subgroup (SpecialLinearGroup (Fin 2) K)) := Subgroup.mem_top a
      have h2 : b ∈ (⊤ : Subgroup (SpecialLinearGroup (Fin 2) K)) := Subgroup.mem_top b
      rw [this] at h1 h2
      rw [Subgroup.mem_bot] at h1 h2
      rw [h1, h2])
  exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr (dgMEquiv hX)).mpr
    (isQuasisimple_of_isSimpleGroup hnab hperf)

theorem oTwoUpper_dgM [CharP K 2] [Fintype K] (hK4 : Fintype.card K = 4)
    {X₀ : Matrix (Fin 2) (Fin 2) K} (hX : X₀.det ≠ 0) : oTwoUpper (dgM X₀) = dgM X₀ := by
  have h4 : 4 ≤ Nat.card K := by rw [Nat.card_eq_fintype_card, hK4]
  have hs := Om4.sl2_isSimple h4
  have : Nontrivial ↥(dgM X₀) := (dgMEquiv hX).toEquiv.nontrivial
  have hsd : IsSimpleGroup ↥(dgM X₀) :=
    IsSimpleGroup.isSimpleGroup_of_surjective (dgMEquiv hX).symm.toMonoidHom
      (dgMEquiv hX).symm.surjective
  refine le_antisymm (oTwoUpper_le _) ?_
  have hn : ((oTwoUpper (dgM X₀)).subgroupOf (dgM X₀)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le _)).mpr
      (le_normalizer_oTwoUpper _)
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsd _ hn with h | h
  · exfalso
    classical
    have hU : Fintype.card Kˣ = 3 := by rw [Fintype.card_units, hK4]
    have : Nontrivial Kˣ := Fintype.one_lt_card_iff_nontrivial.mp (by rw [hU]; norm_num)
    obtain ⟨a, ha⟩ := exists_ne (1 : Kˣ)
    have ha3 : a ^ 3 = 1 := by rw [← hU]; exact pow_card_eq_one
    set d : ↥(dgM X₀) := (dgMEquiv hX).symm (diagOf a) with hd
    have hd3 : d ^ 3 = 1 := by
      have e : diagOf a ^ 3 = 1 := by
        apply Subtype.ext
        rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two, Matrix.SpecialLinearGroup.coe_mul,
          Matrix.SpecialLinearGroup.coe_mul, coe_diagOf, Matrix.SpecialLinearGroup.coe_one]
        have ha3' : (a : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, ha3, Units.val_one]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
        · linear_combination ha3'
        · calc ((a : K))⁻¹ * ((a : K))⁻¹ * ((a : K))⁻¹ = ((a : K) ^ 3)⁻¹ := by ring
            _ = 1 := by rw [ha3', inv_one]
      rw [hd, ← map_pow, e, map_one]
    have hdo : Odd (orderOf (d : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K)) := by
      rw [Subgroup.orderOf_coe]
      exact Odd.of_dvd_nat (by norm_num) (orderOf_dvd_of_pow_eq_one hd3)
    have hdmem : (d : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K) ∈
        oTwoUpper (dgM X₀) := mem_oTwoUpper_of_odd d.2 hdo
    have hd1 : d = 1 := by
      have : d ∈ (oTwoUpper (dgM X₀)).subgroupOf (dgM X₀) := Subgroup.mem_subgroupOf.mpr hdmem
      rwa [h, Subgroup.mem_bot] at this
    apply ha
    have h1 : diagOf a = 1 := by
      have := congrArg (dgMEquiv hX) hd1
      rwa [hd, MulEquiv.apply_symm_apply, map_one] at this
    have h2 := congrArg (fun g : SpecialLinearGroup (Fin 2) K =>
      (g : Matrix (Fin 2) (Fin 2) K) 0 0) h1
    simp [coe_diagOf] at h2
    exact h2
  · intro x hx
    have : (⟨x, hx⟩ : ↥(dgM X₀)) ∈ (oTwoUpper (dgM X₀)).subgroupOf (dgM X₀) := by
      rw [h]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this

theorem commutator_dgM [CharP K 2] [Finite K] (h4 : 4 ≤ Nat.card K)
    {X₀ : Matrix (Fin 2) (Fin 2) K} (hX : X₀.det ≠ 0) : ⁅dgM X₀, dgM X₀⁆ = dgM X₀ := by
  have hsl := Om4.sl2_commutator_eq_top h4
  have h1 : ⁅(⊤ : Subgroup ↥(dgM X₀)), (⊤ : Subgroup ↥(dgM X₀))⁆ = (⊤ : Subgroup ↥(dgM X₀)) := by
    have h := congrArg (Subgroup.map (dgMEquiv hX).symm.toMonoidHom) hsl
    rwa [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ (dgMEquiv hX).symm.surjective]
      at h
  have h2 := congrArg (Subgroup.map (dgM X₀).subtype) h1
  rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2

end Om4Pt

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

@[expose] def inV {K : Type} [Field K] (e : ↥(fsuV T I) ≃* Om4.VM K) (Y : Subgroup (Om4.VM K)) :
    Subgroup G :=
  (Y.comap e.toMonoidHom).map (fsuV T I).subtype

omit [Finite G] in
theorem mem_inV {K : Type} [Field K] {e : ↥(fsuV T I) ≃* Om4.VM K} {Y : Subgroup (Om4.VM K)}
    {x : G} : x ∈ inV e Y ↔ ∃ hx : x ∈ fsuV T I, e ⟨x, hx⟩ ∈ Y := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.2, hv⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

omit [Finite G] in
theorem inV_le {K : Type} [Field K] (e : ↥(fsuV T I) ≃* Om4.VM K) (Y : Subgroup (Om4.VM K)) :
    inV e Y ≤ fsuV T I := fun _ hx => (mem_inV.mp hx).1

@[expose] def lPt (T L W : Subgroup G) : Subgroup G :=
  oTwoUpper (fsuL0 T L ⊓ Subgroup.normalizer (W : Set G))

omit [Finite G] in
theorem lPt_le_L0 (T L W : Subgroup G) : lPt T L W ≤ fsuL0 T L :=
  (oTwoUpper_le _).trans inf_le_left

namespace Setup

namespace IsCoord

variable {S : Setup T L I n} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)
include hc

variable {X₀ : Matrix (Fin 2) (Fin 2) K}

theorem mem_centralizer_of_mem_dgM (k : ↥(fsuL0 T L)) (hk : ψ k ∈ Om4Pt.dgM X₀) :
    (k : G) ∈ Subgroup.centralizer (inV e (Om4Pt.lineM X₀) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨hwV, hwe⟩ := mem_inV.mp hw
  have hkw : (k : G) * w * (k : G)⁻¹ ∈ fsuV T I :=
    (Subgroup.mem_normalizer_iff.mp (S.L0_le_normalizer_V k.2) w).mp hwV
  have h1 := hc.e_conj k ⟨w, hwV⟩ hkw
  rw [Om4Pt.rho_eq_of_mem_lineM hk hwe] at h1
  have h2 : (k : G) * w * (k : G)⁻¹ = w := congrArg Subtype.val (e.injective h1)
  calc w * k = ((k : G) * w * (k : G)⁻¹) * k := by rw [h2]
    _ = k * w := by group

theorem mem_dgM_of_mem_normalizer (hX : X₀.det ≠ 0) (k : ↥(fsuL0 T L))
    (hk : (k : G) ∈ Subgroup.normalizer (inV e (Om4Pt.lineM X₀) : Set G)) :
    ψ k ∈ Om4Pt.dgM X₀ := by
  set w₀ : ↥(fsuV T I) := e.symm (Multiplicative.ofAdd X₀) with hw₀def
  have hw₀ : (w₀ : G) ∈ inV e (Om4Pt.lineM X₀) :=
    mem_inV.mpr ⟨w₀.2, by
      show e w₀ ∈ Om4Pt.lineM X₀
      rw [hw₀def, MulEquiv.apply_symm_apply]
      exact ⟨1, by rw [toAdd_ofAdd, one_smul]⟩⟩
  have h1 := (Subgroup.mem_normalizer_iff.mp hk _).mp hw₀
  obtain ⟨hkw, hkwe⟩ := mem_inV.mp h1
  rw [hc.e_conj k w₀ hkw, hw₀def, MulEquiv.apply_symm_apply] at hkwe
  exact Om4Pt.mem_dgM_of_mem_lineM hX hkwe

theorem mem_normalizer_iff_mem_dgM (hX : X₀.det ≠ 0) (k : ↥(fsuL0 T L)) :
    (k : G) ∈ Subgroup.normalizer (inV e (Om4Pt.lineM X₀) : Set G) ↔ ψ k ∈ Om4Pt.dgM X₀ :=
  ⟨hc.mem_dgM_of_mem_normalizer hX k, fun h =>
    Subgroup.centralizer_le_normalizer _ (hc.mem_centralizer_of_mem_dgM k h)⟩

theorem subgroupOf_inf_normalizer (hX : X₀.det ≠ 0) :
    (fsuL0 T L ⊓ Subgroup.normalizer (inV e (Om4Pt.lineM X₀) : Set G)).subgroupOf (fsuL0 T L) =
      (Om4Pt.dgM X₀).comap ψ := by
  ext k
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, ← hc.mem_normalizer_iff_mem_dgM hX]
  exact ⟨fun h => h.2, fun h => ⟨k.2, h⟩⟩

theorem subgroupOf_lPt (hX : X₀.det ≠ 0) :
    (lPt T L (inV e (Om4Pt.lineM X₀))).subgroupOf (fsuL0 T L) =
      oTwoUpper ((Om4Pt.dgM X₀).comap ψ) := by
  set N := fsuL0 T L ⊓ Subgroup.normalizer (inV e (Om4Pt.lineM X₀) : Set G) with hNdef
  have hN : N = (N.subgroupOf (fsuL0 T L)).map (fsuL0 T L).subtype := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left]
  have h1 : lPt T L (inV e (Om4Pt.lineM X₀)) =
      (oTwoUpper (N.subgroupOf (fsuL0 T L))).map (fsuL0 T L).subtype := by
    rw [← oTwoUpper_map, ← hN]
    rfl
  rw [h1]
  show Subgroup.comap (fsuL0 T L).subtype (Subgroup.map (fsuL0 T L).subtype _) = _
  rw [Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _), hNdef,
    hc.subgroupOf_inf_normalizer hX]

theorem map_lPt (hK4 : Fintype.card K = 4) (hX : X₀.det ≠ 0) :
    ((lPt T L (inV e (Om4Pt.lineM X₀))).subgroupOf (fsuL0 T L)).map ψ = Om4Pt.dgM X₀ := by
  rw [hc.subgroupOf_lPt hX, ← oTwoUpper_map, Subgroup.map_comap_eq_self_of_surjective hc.surj,
    Om4Pt.oTwoUpper_dgM hK4 hX]

noncomputable abbrev lPtHom
    (ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K)
    (W : Subgroup G) :
    ↥(lPt T L W) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K :=
  ψ.comp (Subgroup.inclusion (lPt_le_L0 T L W))

theorem range_lPtHom (hK4 : Fintype.card K = 4) (hX : X₀.det ≠ 0) :
    (lPtHom ψ (inV e (Om4Pt.lineM X₀))).range = Om4Pt.dgM X₀ := by
  rw [MonoidHom.range_comp, Subgroup.inclusion_range, hc.map_lPt hK4 hX]

theorem isPGroup_ker_lPtHom (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (W : Subgroup G) :
    IsPGroup 2 ↥(lPtHom ψ W).ker := by
  rintro ⟨x, hx⟩
  have hq := hc.mem_Q_of_psi_eq_one h37c h38c (Subgroup.inclusion (lPt_le_L0 T L W) x) hx
  obtain ⟨k, hk⟩ := S.isPGroup_Q ⟨_, hq⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  simpa using congrArg Subtype.val hk

theorem perfect_lPt (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (hK4 : Fintype.card K = 4) (hX : X₀.det ≠ 0) :
    ⁅lPt T L (inV e (Om4Pt.lineM X₀)), lPt T L (inV e (Om4Pt.lineM X₀))⁆ =
      lPt T L (inV e (Om4Pt.lineM X₀)) := by
  have h4 : 4 ≤ Nat.card K := by rw [Nat.card_eq_fintype_card, hK4]
  have hidem : oTwoUpper (lPt T L (inV e (Om4Pt.lineM X₀))) = lPt T L (inV e (Om4Pt.lineM X₀)) :=
    le_antisymm (oTwoUpper_le _) ((Subgroup.closure_le _).mpr fun x hx =>
      mem_oTwoUpper_of_odd (Subgroup.subset_closure hx) hx.2)
  refine commutator_eq_self_of_oTwoUpper hidem (lPtHom ψ _) ?_
    (hc.isPGroup_ker_lPtHom h37c h38c _)
  rw [hc.range_lPtHom hK4 hX]
  exact Om4Pt.commutator_dgM h4 hX

theorem mem_cComp_lPt (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (hK4 : Fintype.card K = 4) (hX : X₀.det ≠ 0) :
    lPt T L (inV e (Om4Pt.lineM X₀)) ∈ cComp (lPt T L (inV e (Om4Pt.lineM X₀))) := by
  have h4 : 4 ≤ Nat.card K := by rw [Nat.card_eq_fintype_card, hK4]
  refine mem_cComp_self_of_hom (hc.perfect_lPt h37c h38c hK4 hX) (lPtHom ψ _) ?_ ?_
  · rw [hc.range_lPtHom hK4 hX]
    exact Om4Pt.isQuasisimple_dgM h4 hX
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := (hc.isPGroup_ker_lPtHom h37c h38c (inV e (Om4Pt.lineM X₀))).isNilpotent
    infer_instance

theorem mem_lFamily_lPt (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (hK4 : Fintype.card K = 4) (hX : X₀.det ≠ 0)
    {R : Subgroup G} (hR : R ≤ Subgroup.normalizer (lPt T L (inV e (Om4Pt.lineM X₀)) : Set G)) :
    lPt T L (inV e (Om4Pt.lineM X₀)) ∈ lFamily R := by
  have hA := hc.mem_cComp_lPt h37c h38c hK4 hX
  refine ⟨hA.1, hA.2.1, A4.subnormal_of_normal le_sup_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hR)), fun K' hK' hK'1 hK'p hK'sub => ?_⟩
  exact hA.2.2.2 K' hK' hK'1 hK'p (A4.subnormal_of_le_of_le hK'sub hK'.le le_sup_left)

theorem lPt_quot (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (hK4 : Fintype.card K = 4) (hX : X₀.det ≠ 0) :
    Nonempty (↥(lPt T L (inV e (Om4Pt.lineM X₀))) ⧸
      CFSG.pCore 2 ↥(lPt T L (inV e (Om4Pt.lineM X₀))) ≃* alternatingGroup (Fin 5)) ∧
    CFSG.pCore 2 ↥(lPt T L (inV e (Om4Pt.lineM X₀))) = (lPtHom ψ (inV e (Om4Pt.lineM X₀))).ker := by
  obtain ⟨e5⟩ := sl2_four_equiv_alt_five (K := K) (by rw [Nat.card_eq_fintype_card, hK4])
  set f := lPtHom ψ (inV e (Om4Pt.lineM X₀)) with hf
  let g : ↥(lPt T L (inV e (Om4Pt.lineM X₀))) →* alternatingGroup (Fin 5) :=
    ((Om4Pt.dgMEquiv hX).trans e5).toMonoidHom.comp
      (f.codRestrict (Om4Pt.dgM X₀) fun x => (hc.range_lPtHom hK4 hX) ▸ ⟨x, rfl⟩)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨⟨z, hz0⟩, rfl⟩ := ((Om4Pt.dgMEquiv hX).trans e5).surjective y
    have hz : z ∈ f.range := (hc.range_lPtHom hK4 hX).symm ▸ hz0
    obtain ⟨x, hx⟩ := hz
    have hxz : f.codRestrict (Om4Pt.dgM X₀) (fun x => (hc.range_lPtHom hK4 hX) ▸ ⟨x, rfl⟩) x =
        ⟨z, hz0⟩ := Subtype.ext hx
    exact ⟨x, by
      show ((Om4Pt.dgMEquiv hX).trans e5) (f.codRestrict (Om4Pt.dgM X₀)
        (fun x => (hc.range_lPtHom hK4 hX) ▸ ⟨x, rfl⟩) x) = _
      rw [hxz]⟩
  have hgk : g.ker = f.ker := by
    ext x
    simp only [MonoidHom.mem_ker, g, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hker : IsPGroup 2 ↥g.ker := hgk ▸ hc.isPGroup_ker_lPtHom h37c h38c _
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  exact ⟨⟨Vol2Native.A312L.modO2EquivOfHom Vol2Native.A312L.Seven.alt5_nonabelian g hg hker⟩,
    (Vol2Native.A312L.pCore_two_eq_ker Vol2Native.A312L.Seven.alt5_nonabelian g hg hker).trans
      hgk⟩

theorem lPt_le_centralizer (hK4 : Fintype.card K = 4) (hX : X₀.det ≠ 0) :
    lPt T L (inV e (Om4Pt.lineM X₀)) ≤
      Subgroup.centralizer (inV e (Om4Pt.lineM X₀) : Set G) := by
  intro x hx
  have hxL : x ∈ fsuL0 T L := lPt_le_L0 T L _ hx
  have h1 : ψ ⟨x, hxL⟩ ∈ Om4Pt.dgM X₀ := by
    rw [← hc.map_lPt hK4 hX]
    exact ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  exact hc.mem_centralizer_of_mem_dgM ⟨x, hxL⟩ h1

theorem mem_inV_of_centralizes (hK4 : Fintype.card K = 4) (hX : X₀.det ≠ 0) {v : G}
    (hv : v ∈ fsuV T I) (h : ∀ l ∈ lPt T L (inV e (Om4Pt.lineM X₀)), l * v * l⁻¹ = v) :
    v ∈ inV e (Om4Pt.lineM X₀) := by
  refine mem_inV.mpr ⟨hv, Om4Pt.mem_lineM_of_forall_rho_eq hX fun γ hγ => ?_⟩
  rw [← hc.map_lPt hK4 hX] at hγ
  obtain ⟨k, hk, rfl⟩ := hγ
  have hkl := Subgroup.mem_subgroupOf.mp hk
  have hkv : (k : G) * v * (k : G)⁻¹ ∈ fsuV T I :=
    (Subgroup.mem_normalizer_iff.mp (S.L0_le_normalizer_V k.2) v).mp hv
  rw [← hc.e_conj k ⟨v, hv⟩ hkv]
  exact congrArg e (Subtype.ext (h _ hkl))

theorem mem_normalizer_inV_of_fix {x : G} (hx : x ∈ fsuM T L) {w : G}
    (hw : w ∈ inV e (Om4Pt.lineM X₀)) (hw1 : w ≠ 1) (hxw : x * w * x⁻¹ = w) :
    x ∈ Subgroup.normalizer (inV e (Om4Pt.lineM X₀) : Set G) := by
  have key : ∀ y : G, y ∈ fsuM T L → y * w * y⁻¹ = w → ∀ h ∈ inV e (Om4Pt.lineM X₀),
      y * h * y⁻¹ ∈ inV e (Om4Pt.lineM X₀) := by
    intro y hy hyw h hh
    obtain ⟨hwV, c, hc'⟩ := mem_inV.mp hw
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hw1
      rw [zero_smul] at hc'
      have : e ⟨w, hwV⟩ = 1 := Multiplicative.toAdd.injective (by rw [hc']; rfl)
      exact congrArg Subtype.val ((map_eq_one_iff e e.injective).mp this)
    obtain ⟨hhV, hhe⟩ := mem_inV.mp hh
    have hyh : y * h * y⁻¹ ∈ fsuV T I :=
      (Subgroup.mem_normalizer_iff.mp (S.hMN hy) h).mp hhV
    refine mem_inV.mpr ⟨hyh, ?_⟩
    have hbar : ∀ (u : G) (hu : u ∈ fsuV T I) (hu' : y * u * y⁻¹ ∈ fsuV T I),
        e ⟨y * u * y⁻¹, hu'⟩ = bar e ⟨y, S.hMN hy⟩ (e ⟨u, hu⟩) := by
      intro u hu hu'
      rw [bar_apply]
    obtain ⟨A, B, τ, hform | hform⟩ := hc.exists_form hy
    · have hσ := Om4Pt.toAdd_lr_frM_smul A B τ
      rw [hbar h hhV hyh, hform]
      refine Om4Pt.mem_lineM_of_fix (σ := τ) (fun d Y => hσ d Y) hc0 ?_ hhe
      have h1 := hbar w hwV (by rw [hyw]; exact hwV)
      rw [hform] at h1
      have hew : e ⟨w, hwV⟩ = Multiplicative.ofAdd (c • X₀) := by
        rw [← hc']; rfl
      rw [← hew, ← h1]
      exact congrArg e (Subtype.ext hyw)
    · have hσ := Om4Pt.toAdd_lr_frM_trM_smul A B τ
      rw [hbar h hhV hyh, hform]
      refine Om4Pt.mem_lineM_of_fix (σ := τ) (fun d Y => hσ d Y) hc0 ?_ hhe
      have h1 := hbar w hwV (by rw [hyw]; exact hwV)
      rw [hform] at h1
      have hew : e ⟨w, hwV⟩ = Multiplicative.ofAdd (c • X₀) := by
        rw [← hc']; rfl
      rw [← hew, ← h1]
      exact congrArg e (Subtype.ext hyw)
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key x hx hxw h, fun hh => ?_⟩
  have hxi : x⁻¹ * w * x⁻¹⁻¹ = w := by
    rw [inv_inv]
    calc x⁻¹ * w * x = x⁻¹ * (x * w * x⁻¹) * x := by rw [hxw]
      _ = w := by group
  have := key x⁻¹ ((fsuM T L).inv_mem hx) hxi _ hh
  rwa [show x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h by group] at this

theorem mem_normalizer_lPt {x : G} (hx : x ∈ fsuM T L) {w : G}
    (hw : w ∈ inV e (Om4Pt.lineM X₀)) (hw1 : w ≠ 1) (hxw : x * w * x⁻¹ = w) :
    x ∈ Subgroup.normalizer (lPt T L (inV e (Om4Pt.lineM X₀)) : Set G) := by
  have h1 := hc.mem_normalizer_inV_of_fix hx hw hw1 hxw
  refine normalizer_le_normalizer_oTwoUpper _ (Subgroup.inf_normalizer_le_normalizer_inf
    ⟨hx, Subgroup.le_normalizer h1⟩)

end IsCoord

end Setup

end CFSG.Quasithin.H13.Ch9
