module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3A5VecA
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Frame
public import CFSG.Quasithin.EmptyFaithful.S151bModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

private theorem s16h_finite_mulAut : Finite (MulAut W) := by
  classical
  exact Finite.of_injective (fun f : MulAut W => (f : W → W))
    (fun f g h => MulEquiv.ext (congrFun h))

private theorem s16h_normalizer_le_stabSub_commSub {L : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ normalizer (L : Set (MulAut W))) : g ∈ stabSub (commSub ⊤ L) := by
  rw [mem_stabSub]
  have hnorm : ∀ x ∈ L, g * x * g⁻¹ ∈ L :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have hgNinv : g⁻¹ ∈ normalizer (L : Set (MulAut W)) :=
    (normalizer (L : Set (MulAut W))).inv_mem hg
  have hnorminv : ∀ x ∈ L, g⁻¹ * x * (g⁻¹)⁻¹ ∈ L :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp hgNinv x).mp hx
  intro u
  constructor
  · intro hu
    have hmem : g⁻¹ (g u) ∈ commSub (⊤ : Subgroup W) L :=
      commSub_top_stable151b hnorminv (g u) hu
    simpa using hmem
  · intro hu
    exact commSub_top_stable151b hnorm u hu

private lemma s16h_card_isAlt5 {L : Subgroup (MulAut W)} (hL : IsAlt ↥L 5) :
    Nat.card ↥L = 60 := by
  obtain ⟨e⟩ := hL
  rw [Nat.card_congr e.toEquiv, CFSG.ComponentClassification.RankTwoAltFive.card_A5]

private lemma s16h_card_sylow_four {P H : Subgroup (MulAut W)}
    (hP : CFSG.QuasithinUnique.IsSylowTwoOf P H) (hH : Nat.card ↥H = 60) :
    Nat.card ↥P = 4 := by
  haveI := s16h_finite_mulAut (W := W)
  haveI : Finite ↥P := Subtype.finite
  haveI : Finite ↥H := Subtype.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hP.2.1
  have h1 := Subgroup.relIndex_mul_card P H
  rw [inf_eq_left.mpr hP.1, hk, hH] at h1
  have hodd : ¬ 2 ∣ P.relIndex H := hP.2.2
  rcases k with _ | _ | _ | k
  · exfalso
    apply hodd
    have : P.relIndex H = 60 := by simpa using h1
    rw [this]; norm_num
  · exfalso
    apply hodd
    have : P.relIndex H = 30 := by omega
    rw [this]; norm_num
  · simpa using hk
  · exfalso
    have : 8 ∣ 60 := ⟨P.relIndex H * 2 ^ k, by rw [← h1]; ring⟩
    omega

private theorem s16h_eq_of_mul_eq_mul_of_inf_bot {A B : Subgroup W} (h : A ⊓ B = ⊥)
    {u u' v v' : W} (hu : u ∈ A) (hu' : u' ∈ B) (hv : v ∈ A) (hv' : v' ∈ B)
    (hmul : u * u' = v * v') : u = v ∧ u' = v' := by
  have h1 : v⁻¹ * u = v' * u'⁻¹ := by
    calc v⁻¹ * u = v⁻¹ * (u * u') * u'⁻¹ := by group
      _ = v⁻¹ * (v * v') * u'⁻¹ := by rw [hmul]
      _ = v' * u'⁻¹ := by group
  have hmem : v⁻¹ * u ∈ A ⊓ B :=
    ⟨A.mul_mem (A.inv_mem hv) hu, by rw [h1]; exact B.mul_mem hv' (B.inv_mem hu')⟩
  rw [h, Subgroup.mem_bot] at hmem
  have huv : u = v := (inv_mul_eq_one.mp hmem).symm
  subst huv
  exact ⟨rfl, mul_left_cancel hmul⟩

private theorem s16h_eq_three {A B C : Subgroup W} (hA : A ⊓ (B ⊔ C) = ⊥)
    (hB : B ⊓ C = ⊥) {a0 a1 a2 b0 b1 b2 : W}
    (ha0 : a0 ∈ A) (ha1 : a1 ∈ B) (ha2 : a2 ∈ C)
    (hb0 : b0 ∈ A) (hb1 : b1 ∈ B) (hb2 : b2 ∈ C)
    (h : a0 * a1 * a2 = b0 * b1 * b2) : a0 = b0 ∧ a1 = b1 ∧ a2 = b2 := by
  have h1 : a0 * (a1 * a2) = b0 * (b1 * b2) := by
    rw [← mul_assoc, ← mul_assoc, h]
  obtain ⟨h0, h12⟩ := s16h_eq_of_mul_eq_mul_of_inf_bot hA ha0 (mul_mem_sup ha1 ha2)
    hb0 (mul_mem_sup hb1 hb2) h1
  obtain ⟨h1', h2'⟩ := s16h_eq_of_mul_eq_mul_of_inf_bot hB ha1 ha2 hb1 hb2 h12
  exact ⟨h0, h1', h2'⟩

private theorem s16h_nat_card {L : Subgroup (MulAut W)} {J : Subgroup W}
    (hJ : AlternatingNatural L J ⊥ 5) : Nat.card ↥J = 16 := by
  obtain ⟨π, hπ⟩ := hJ
  obtain ⟨f, hfs, hfk, -⟩ := CFSG.Quasithin.FFC.RealizesVia.secMap
    (D := FFModel.altDn 5) CFSG.Quasithin.FFC.altDn_ker_five hπ
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hfk u).1 hu))
  have hcard : Nat.card ↥J = Nat.card ↥(FFModel.altDn 5).sec :=
    Nat.card_congr (Equiv.ofBijective f ⟨hinj, hfs⟩)
  rw [hcard]
  exact CFSG.Quasithin.FFC.card_coreMod_five

private lemma s16h_iSup_fin_three (I : Fin 3 → Subgroup W) :
    (I 0 ⊔ I 1 ⊔ I 2) = ⨆ i, I i := by
  refine le_antisymm ?_ ?_
  · refine sup_le (sup_le ?_ ?_) ?_
    · exact le_iSup I 0
    · exact le_iSup I 1
    · exact le_iSup I 2
  · refine iSup_le fun i => ?_
    fin_cases i
    · exact le_trans le_sup_left le_sup_left
    · exact le_trans le_sup_right le_sup_left
    · exact le_sup_right

private lemma s16h_iSup_ne_zero (I : Fin 3 → Subgroup W) :
    (⨆ (j : Fin 3) (_ : j ≠ 0), I j) = I 1 ⊔ I 2 := by
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun j hj => ?_
    fin_cases j
    · exact absurd rfl hj
    · exact le_sup_left
    · exact le_sup_right
  · exact sup_le (le_iSup₂ (f := fun j (_ : j ≠ 0) => I j) 1 (by decide))
      (le_iSup₂ (f := fun j (_ : j ≠ 0) => I j) 2 (by decide))

private lemma s16h_zpow_fix {g z : MulAut W} {v : W} (hg : orderOf g = 3) (hgv : g v = v)
    (hz : z ∈ zpowers g) : z v = v := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf] at hz
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
  rw [Finset.mem_range] at hi
  have hi3 : i < 3 := by simpa [hg] using hi
  interval_cases i
  · rfl
  · simpa [pow_one] using hgv
  · simp [pow_two, MulAut.mul_apply, hgv]

theorem s16h_e3_a5_good_vector {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W}
    (F : s16h_E3Frame X L L' T U U') (hL : IsAlt ↥L 5)
    (hsum : SumOfNat (fun H V Z => AlternatingNatural H V Z 5) L U ⊥ 3) :
    ∃ w : W, w ≠ 1 ∧ (∀ τ ∈ T, τ w = w) ∧
      ∃ E : Subgroup (MulAut W), E ≤ X ∧ IsElemAbelian 3 E ∧ 9 ≤ Nat.card ↥E ∧
        ∀ e ∈ E, e w = w := by
  classical
  have hL5 : IsAlt ↥L 5 := hL
  obtain ⟨t, htT, htL, htU⟩ := F.swap
  have htX : t ∈ X := F.t_le htT
  have ht2T : t ^ 2 ∈ T := T.pow_mem htT 2
  have ht2X : t ^ 2 ∈ X := X.pow_mem htX 2
  let X₀ : Subgroup (MulAut W) := X ⊓ normalizer (L : Set (MulAut W))
  let T₀ : Subgroup (MulAut W) := T ⊓ X₀
  let T_L : Subgroup (MulAut W) := T₀ ⊓ L
  obtain ⟨I, -, hind, hsupI, hnat⟩ := hsum
  have hI0ne : I 0 ≠ ⊥ := by
    intro hbot
    have hc := s16h_nat_card (hnat 0)
    rw [hbot, Subgroup.card_bot] at hc
    norm_num at hc
  have hUne : U ≠ ⊥ := by
    intro hbot
    have hle : I 0 ≤ U := by
      have h1 : I 0 ≤ ⨆ i, I i := le_iSup I 0
      exact h1.trans ((le_sup_right : (⨆ i, I i) ≤ ⊥ ⊔ ⨆ i, I i).trans (le_of_eq hsupI))
    have : I 0 ≤ ⊥ := hbot ▸ hle
    exact hI0ne (le_bot_iff.mp this)

  have htX₀ : t ∈ X ∧ t ∉ normalizer (L : Set (MulAut W)) := by
    refine ⟨htX, fun hN => ?_⟩
    have h1 : L.map (MulAut.conj t).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hN
    rw [htL] at h1
    have hU' : U' = U := by
      rw [F.u'_eq, F.u_eq, h1]
    have hbot : U = ⊥ := by
      have h := F.inf_eq
      rw [hU'] at h
      rwa [inf_idem] at h
    exact hUne hbot
  have ht_swap : L.map (MulAut.conj t).toMonoidHom = L' ∧
      L'.map (MulAut.conj t).toMonoidHom = L := by
    rcases F.perm t htX with hf | hs
    · exfalso
      exact htX₀.2 (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hf.1)
    · exact ⟨hs.1, hs.2.1⟩
  have ht2_norm : t ^ 2 ∈ normalizer (L : Set (MulAut W)) := by
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    change L.map (MulAut.conj (t ^ 2)).toMonoidHom = L
    have hcomp : L.map (MulAut.conj (t ^ 2)).toMonoidHom =
        (L.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
    rw [hcomp, htL, ht_swap.2]
  have ht2T₀ : t ^ 2 ∈ T₀ := ⟨ht2T, ht2X, ht2_norm⟩
  have hX₀_rel : X₀.relIndex X = 2 := by
    rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
    refine ⟨t, htX, ?_, ?_⟩
    · intro h; exact htX₀.2 h.2
    intro b hbX
    rcases F.perm b hbX with hf | hs
    · right
      exact ⟨hbX, Subgroup.mem_normalizer_iff_map_conj_eq.mpr hf.1⟩
    · left
      refine ⟨X.mul_mem hbX htX, ?_⟩
      refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
      change L.map (MulAut.conj (b * t)).toMonoidHom = L
      have hcomp : L.map (MulAut.conj (b * t)).toMonoidHom =
          (L.map (MulAut.conj t).toMonoidHom).map (MulAut.conj b).toMonoidHom := by
        rw [Subgroup.map_map]
        congr 1
      rw [hcomp, htL, hs.2.1]
  have hX₀_norm : X ≤ normalizer (X₀ : Set (MulAut W)) := by
    haveI : (X₀.subgroupOf X).Normal := Subgroup.normal_of_index_eq_two hX₀_rel
    exact Subgroup.le_normalizer_of_normal_subgroupOf (H := X₀) (K := X) inf_le_left
  have hT₀_rel : T₀.relIndex T = 2 := by
    rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
    refine ⟨t, htT, ?_, ?_⟩
    · intro h; exact htX₀.2 h.2.2
    intro b hbT
    have hbX : b ∈ X := F.t_le hbT
    rcases F.perm b hbX with hf | hs
    · right
      exact ⟨hbT, hbX, Subgroup.mem_normalizer_iff_map_conj_eq.mpr hf.1⟩
    · left
      refine ⟨T.mul_mem hbT htT, X.mul_mem hbX htX, ?_⟩
      refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
      change L.map (MulAut.conj (b * t)).toMonoidHom = L
      have hcomp : L.map (MulAut.conj (b * t)).toMonoidHom =
          (L.map (MulAut.conj t).toMonoidHom).map (MulAut.conj b).toMonoidHom := by
        rw [Subgroup.map_map]
        congr 1
      rw [hcomp, htL, hs.2.1]
  have hT₀_norm : T ≤ normalizer (T₀ : Set (MulAut W)) := by
    haveI : (T₀.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two hT₀_rel
    exact Subgroup.le_normalizer_of_normal_subgroupOf (H := T₀) (K := T) inf_le_left
  have hSylX : CFSG.QuasithinUnique.IsSylowTwoOf T X := ⟨F.t_le, F.t_two, F.t_syl⟩
  have hX₀leX : X₀ ≤ X := inf_le_left
  have hSylX₀ : CFSG.QuasithinUnique.IsSylowTwoOf T₀ X₀ :=
    CFSG.Quasithin.A4.isSylowTwoOf_inf_normal hSylX hX₀leX hX₀_norm
  have hLleX₀ : L ≤ X₀ :=
    le_inf F.le_x (Subgroup.le_normalizer)
  have hX₀leN : X₀ ≤ normalizer (L : Set (MulAut W)) := inf_le_right
  have hSylTL : CFSG.QuasithinUnique.IsSylowTwoOf T_L L :=
    CFSG.Quasithin.A4.isSylowTwoOf_inf_normal hSylX₀ hLleX₀ hX₀leN
  have hTLcard : Nat.card ↥T_L = 4 :=
    s16h_card_sylow_four hSylTL (s16h_card_isAlt5 hL)
  obtain ⟨eL⟩ := hL
  obtain ⟨y, hyL, hyN, hy3, -, -⟩ :=
    CFSG.ComponentClassification.RankTwoAltFive.exists_klein_three eL inf_le_right hTLcard
  have hT₀_stab : T₀ ≤ stabSub U := by
    intro g hg
    have hgX₀ : g ∈ X₀ := (Subgroup.mem_inf.mp hg).2
    have hgN : g ∈ normalizer (L : Set (MulAut W)) := (Subgroup.mem_inf.mp hgX₀).2
    rw [F.u_eq]
    exact s16h_normalizer_le_stabSub_commSub hgN
  let actU : ↥T₀ →* MulAut ↥U :=
    (CFSG.Quasithin.resHom U).comp (Subgroup.inclusion hT₀_stab)
  letI : MulAction ↥T₀ ↥U := MulAction.compHom ↥U actU
  have hT₀p : IsPGroup 2 ↥T₀ := F.t_two.to_le (inf_le_left : T₀ ≤ T)
  have hU2 : IsPGroup 2 ↥U := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro u
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa [pow_two] using F.exp2 (u : W)
  haveI : Finite ↥U := Subtype.finite
  have hUeven : 2 ∣ Nat.card ↥U := by
    rcases hU2.card_eq_or_dvd with h1 | h2
    · exfalso
      have hnt : Nontrivial ↥U := by
        obtain ⟨u, hu⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUne
        exact ⟨u, 1, hu⟩
      have hcard := Finite.one_lt_card (α := ↥U)
      omega
    · exact h2
  have hmod := hT₀p.card_modEq_card_fixedPoints ↥U
  have hfix2 : 2 ∣ Nat.card (MulAction.fixedPoints ↥T₀ ↥U) := by
    have hU0 : Nat.card ↥U ≡ 0 [MOD 2] := Nat.modEq_zero_iff_dvd.mpr hUeven
    exact Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans hU0)
  let oneF : MulAction.fixedPoints ↥T₀ ↥U := ⟨1, fun m => by
    change actU m 1 = 1
    exact map_one (actU m)⟩
  haveI : Nonempty (MulAction.fixedPoints ↥T₀ ↥U) := ⟨oneF⟩
  have hfixnt : Nontrivial (MulAction.fixedPoints ↥T₀ ↥U) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have hpos : 0 < Nat.card (MulAction.fixedPoints ↥T₀ ↥U) := Nat.card_pos
    omega
  obtain ⟨uF, huF⟩ := exists_ne oneF
  let a : W := (uF : ↥U).1
  have haU : a ∈ U := (uF : ↥U).2
  have ha1 : a ≠ 1 := by
    intro h
    apply huF
    ext
    exact h
  have haT₀ : ∀ τ ∈ T₀, τ a = a := by
    intro τ hτ
    have h := (MulAction.mem_fixedPoints.mp uF.2) ⟨τ, hτ⟩
    change actU ⟨τ, hτ⟩ uF = uF at h
    have h' := congrArg (fun v : ↥U => (v : W)) h
    simpa [a, actU, CFSG.Quasithin.resHom_apply] using h'
  have haT_L : ∀ τ ∈ T_L, τ a = a := fun τ hτ => haT₀ τ ((inf_le_left : T_L ≤ T₀) hτ)
  have ha_iSup : a ∈ ⨆ i, I i := by
    have h : a ∈ ⊥ ⊔ ⨆ i, I i := by rw [hsupI]; exact haU
    simpa using h
  have ha_sup3 : a ∈ I 0 ⊔ I 1 ⊔ I 2 := by
    rw [s16h_iSup_fin_three]; exact ha_iSup
  obtain ⟨a01, ha01, b2, hb2, ha01a2⟩ := Subgroup.mem_sup.mp ha_sup3
  obtain ⟨b0, hb0, b1, hb1, hb0b1⟩ := Subgroup.mem_sup.mp ha01
  have ha_eq : b0 * b1 * b2 = a := by
    rw [hb0b1, ha01a2]
  have hA : I 0 ⊓ (I 1 ⊔ I 2) = ⊥ := by
    rw [← s16h_iSup_ne_zero I]
    exact le_bot_iff.mp (by simpa [bot_sup_eq] using hind 0)
  have hB : I 1 ⊓ I 2 = ⊥ := by
    have hle : I 2 ≤ ⊥ ⊔ ⨆ (j : Fin 3) (_ : j ≠ 1), I j := by
      rw [bot_sup_eq]
      exact le_iSup₂ (f := fun j (_ : j ≠ 1) => I j) 2 (by decide)
    exact le_bot_iff.mp (le_trans (inf_le_inf le_rfl hle) (hind 1))
  let af : Fin 3 → W := fun i => if i = 0 then b0 else if i = 1 then b1 else b2
  have haf0 : af 0 = b0 := by simp [af]
  have haf1 : af 1 = b1 := by simp [af]
  have haf2 : af 2 = b2 := by simp [af]
  have haf_eq : af 0 * af 1 * af 2 = a := by
    rw [haf0, haf1, haf2]; exact ha_eq
  have haf_mem : ∀ i : Fin 3, af i ∈ I i := by
    intro i
    fin_cases i
    · simpa [haf0] using hb0
    · simpa [haf1] using hb1
    · simpa [haf2] using hb2
  have hstable : ∀ i : Fin 3, ∀ τ ∈ T_L, ∀ u ∈ I i, τ u ∈ I i := by
    intro i τ hτ u hu
    have hτL : τ ∈ L := (Subgroup.mem_inf.mp hτ).2
    obtain ⟨π, hπ⟩ := hnat i
    exact hπ.2.2.2.1 ⟨τ, hτL⟩ u hu
  have haf_fixed : ∀ i : Fin 3, ∀ p ∈ T_L, p (af i) = af i := by
    intro i p hp
    have hp_eq : p (af 0) * p (af 1) * p (af 2) = af 0 * af 1 * af 2 := by
      rw [← map_mul, ← map_mul, haf_eq, haT_L p hp]
    have hres := s16h_eq_three hA hB
      (hstable 0 p hp (af 0) (haf_mem 0))
      (hstable 1 p hp (af 1) (haf_mem 1))
      (hstable 2 p hp (af 2) (haf_mem 2))
      (haf_mem 0) (haf_mem 1) (haf_mem 2) hp_eq
    fin_cases i
    · exact hres.1
    · exact hres.2.1
    · exact hres.2.2
  have hfix_af : ∀ i : Fin 3, y (af i) = af i := by
    intro i
    by_cases h : af i = 1
    · rw [h, map_one]
    · exact s16h_nat_fix_of_mem_normalizer hL5 (hnat i) inf_le_right hTLcard
        (haf_mem i) h (fun p hp => haf_fixed i p hp) hyL hyN hy3
  have hya : y a = a := by
    rw [← haf_eq]
    simp only [map_mul]
    rw [hfix_af 0, hfix_af 1, hfix_af 2]
  have hy'L' : t * y * t⁻¹ ∈ L' := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom hyL
    rw [htL] at h
    simpa [MulAut.conj_apply] using h
  have hy'3 : orderOf (t * y * t⁻¹) = 3 := by
    have h := orderOf_injective (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective y
    rw [hy3] at h
    simpa [MulAut.conj_apply] using h
  have hy'y : y * (t * y * t⁻¹) = (t * y * t⁻¹) * y :=
    F.comm y hyL (t * y * t⁻¹) hy'L'
  let y' : MulAut W := t * y * t⁻¹
  have hy'def : y' = t * y * t⁻¹ := rfl
  have htaU' : t a ∈ U' := by
    have h := Subgroup.mem_map_of_mem t.toMonoidHom haU
    rw [htU] at h
    exact h
  let w : W := a * t a
  have hwne : w ≠ 1 := by
    intro hw
    have ha2 : a * a = 1 := by
      simpa [pow_two] using F.exp2 a
    have hta : t a = a := by
      calc t a = a * a * (t a) := by rw [ha2, one_mul]
        _ = a * (a * (t a)) := by group
        _ = a := by rw [show a * (t a) = 1 from hw, mul_one]
    have hmem : a ∈ U ⊓ U' := ⟨haU, hta ▸ htaU'⟩
    rw [F.inf_eq, Subgroup.mem_bot] at hmem
    exact ha1 hmem
  have hT₀_fix_ta : ∀ τ ∈ T₀, τ (t a) = t a := by
    intro τ hτ
    have hconj : t⁻¹ * τ * t ∈ T₀ :=
      (Subgroup.mem_set_normalizer_iff''.mp (hT₀_norm htT) τ).mp hτ
    calc τ (t a) = (τ * t) a := rfl
      _ = (t * (t⁻¹ * τ * t)) a := by
          rw [show τ * t = t * (t⁻¹ * τ * t) by group]
      _ = t ((t⁻¹ * τ * t) a) := rfl
      _ = t a := by rw [haT₀ _ hconj]
  have hT₀_coset : ∀ τ ∈ T, τ ∈ T₀ ∨ ∃ σ ∈ T₀, τ = t * σ := by
    intro τ hτ
    by_cases hτ₀ : τ ∈ T₀
    · exact Or.inl hτ₀
    · right
      have hτX : τ ∈ X := F.t_le hτ
      have hnotN : τ ∉ normalizer (L : Set (MulAut W)) := fun hN => hτ₀ ⟨hτ, hτX, hN⟩
      rcases F.perm τ hτX with hf | hs
      · exfalso
        exact hnotN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hf.1)
      · have htτ : t * τ ∈ T₀ := by
          refine ⟨T.mul_mem htT hτ, X.mul_mem htX hτX, ?_⟩
          refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
          change L.map (MulAut.conj (t * τ)).toMonoidHom = L
          have hcomp : L.map (MulAut.conj (t * τ)).toMonoidHom =
              (L.map (MulAut.conj τ).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
            rw [Subgroup.map_map]
            congr 1
          rw [hcomp, hs.1, ht_swap.2]
        refine ⟨(t ^ 2)⁻¹ * (t * τ), T₀.mul_mem (T₀.inv_mem ht2T₀) htτ, ?_⟩
        show τ = t * ((t ^ 2)⁻¹ * (t * τ))
        group
  have hTw : ∀ τ ∈ T, τ w = w := by
    intro τ hτ
    rcases hT₀_coset τ hτ with hτ₀ | ⟨σ, hσ, rfl⟩
    · have h1 : τ a = a := haT₀ τ hτ₀
      have h2 : τ (t a) = t a := hT₀_fix_ta τ hτ₀
      show τ (a * t a) = a * t a
      rw [map_mul, h1, h2]
    · have hσ' : t⁻¹ * σ * t ∈ T₀ :=
        (Subgroup.mem_set_normalizer_iff''.mp (hT₀_norm htT) σ).mp hσ
      have h1 : (t * σ) a = t a := by
        rw [MulAut.mul_apply, haT₀ σ hσ]
      have h2 : (t * σ) (t a) = a := by
        calc (t * σ) (t a) = t (σ (t a)) := rfl
          _ = t ((σ * t) a) := rfl
          _ = t ((t * (t⁻¹ * σ * t)) a) := by
              rw [show σ * t = t * (t⁻¹ * σ * t) by group]
          _ = t (t ((t⁻¹ * σ * t) a)) := rfl
          _ = t (t a) := by rw [haT₀ _ hσ']
          _ = a := by rw [show t (t a) = (t ^ 2) a by rfl, haT₀ _ ht2T₀]
      show (t * σ) (a * t a) = a * t a
      rw [map_mul, h1, h2, mul_comm]
  have hy'L'' : y' ∈ L' := hy'def ▸ hy'L'
  have hy'3' : orderOf y' = 3 := hy'def ▸ hy'3
  have hy'y' : y * y' = y' * y := hy'def ▸ hy'y
  have hLL' : L ⊓ L' = ⊥ := by
    refine le_bot_iff.mp ?_
    intro z hz
    obtain ⟨hzL, hzL'⟩ := Subgroup.mem_inf.mp hz
    have hz1 : z = 1 := by
      ext x
      obtain ⟨u, hu, u', hu', rfl⟩ := Subgroup.mem_sup.mp (by
        rw [F.sup_eq]; exact Subgroup.mem_top x)
      rw [show z (u * u') = z u * z u' from map_mul z u u',
        F.fix_u z hzL' u hu, F.fix_u' z hzL u' hu']
      simp
    exact Subgroup.mem_bot.mpr hz1
  have hyy'_pow3 : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  have hy''_pow3 : y' ^ 3 = 1 := by rw [← hy'3']; exact pow_orderOf_eq_one y'
  have hcommE : ∀ a ∈ zpowers y, ∀ b ∈ zpowers y', a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((show Commute y y' from hy'y').zpow_zpow m n).eq
  have hEel : IsElemAbelian 3 (zpowers y ⊔ zpowers y') :=
    (CFSG.Open.IsElemAbelian.sup_of_commute
      (CFSG.Open.isElemAbelian_zpowers (p := 3) hyy'_pow3)
      (CFSG.Open.isElemAbelian_zpowers (p := 3) hy''_pow3) hcommE)
  have hinfE : zpowers y ⊓ zpowers y' = ⊥ := by
    refine le_bot_iff.mp ?_
    intro z hz
    obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.mp hz
    have hzL : z ∈ L := Subgroup.zpowers_le.mpr hyL hz1
    have hzL' : z ∈ L' := Subgroup.zpowers_le.mpr hy'L'' hz2
    have hbot : z ∈ L ⊓ L' := ⟨hzL, hzL'⟩
    rw [hLL', Subgroup.mem_bot] at hbot
    exact Subgroup.mem_bot.mpr hbot
  have hEcard : Nat.card ↥(zpowers y ⊔ zpowers y') = 9 := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (zpowers y) (zpowers y') hcommE).1
    rw [hinfE] at h
    simp only [Subgroup.card_bot, mul_one, Nat.card_zpowers, hy3, hy'3'] at h
    omega
  have hE_X : zpowers y ⊔ zpowers y' ≤ X :=
    sup_le (Subgroup.zpowers_le.mpr (F.le_x hyL))
      (Subgroup.zpowers_le.mpr (F.le_x' hy'L''))
  have hyta : y (t a) = t a := by
    rw [F.fix_u' y hyL (t a) htaU']
  have hyw : y w = w := by
    show y (a * t a) = a * t a
    rw [map_mul, hya, hyta]
  have hy'ta : y' (t a) = t a := by
    calc y' (t a) = (t * y * t⁻¹) (t a) := rfl
      _ = t (y a) := by simp [mul_assoc]
      _ = t a := by rw [hya]
  have hy'a : y' a = a := by
    rw [F.fix_u y' hy'L'' a haU]
  have hy'w : y' w = w := by
    show y' (a * t a) = a * t a
    rw [map_mul, hy'a, hy'ta]
  have hEw : ∀ e ∈ zpowers y ⊔ zpowers y', e w = w := by
    intro e he
    obtain ⟨e1, he1, e2, he2, rfl⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcommE he
    have h1a : e1 a = a := s16h_zpow_fix hy3 hya he1
    have h1ta : e1 (t a) = t a := s16h_zpow_fix hy3 hyta he1
    have h2a : e2 a = a := s16h_zpow_fix hy'3' hy'a he2
    have h2ta : e2 (t a) = t a := s16h_zpow_fix hy'3' hy'ta he2
    calc (e1 * e2) (a * t a) = e1 (e2 (a * t a)) := rfl
      _ = e1 (e2 a * e2 (t a)) := by rw [map_mul]
      _ = e1 (a * t a) := by rw [h2a, h2ta]
      _ = e1 a * e1 (t a) := by rw [map_mul]
      _ = a * t a := by rw [h1a, h1ta]
  refine ⟨w, hwne, hTw, zpowers y ⊔ zpowers y', hE_X, hEel, ?_, hEw⟩
  rw [hEcard]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
