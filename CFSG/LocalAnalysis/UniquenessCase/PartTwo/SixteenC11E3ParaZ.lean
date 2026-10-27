module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3Para
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem s1611e3_mem_centSub_zpowers_iff {W : Type} [CommGroup W] (l : MulAut W) (w : W) :
    l ∈ centSub (Subgroup.zpowers w) ↔ l w = w := by
  constructor
  · intro h
    exact h w (Subgroup.mem_zpowers w)
  · intro h u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    rw [map_zpow, h]

private theorem s1611e3_zpowers_commute {A : Type*} [Group A] {z a : A} (h : Commute z a)
    {k : A} (hk : k ∈ Subgroup.zpowers z) : Commute k a := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
  exact h.zpow_left m

private theorem s1611e3_inf_fixV_iSup {W : Type} [CommGroup W] {ι : Type} [Fintype ι]
    [DecidableEq ι] {I : ι → Subgroup W} (hind : iSupIndep I) {X : Subgroup (MulAut W)}
    (hXI : ∀ i, ∀ x ∈ X, ∀ w ∈ I i, x w ∈ I i) :
    (⨆ i, I i) ⊓ fixV X = ⨆ i, (I i ⊓ fixV X) := by
  refine le_antisymm ?_ ?_
  · intro w hw
    obtain ⟨hwJ, hwfix⟩ := Subgroup.mem_inf.1 hw
    let hcomm : Pairwise fun i j => ∀ x y : W, x ∈ I i → y ∈ I j → Commute x y :=
      fun _ _ _ _ _ _ _ => Commute.all _ _
    let Φ : (∀ i, I i) →* W := Subgroup.noncommPiCoprod hcomm
    have hΦinj : Function.Injective Φ := Subgroup.injective_noncommPiCoprod_of_iSupIndep hind
    have hΦrange : Φ.range = ⨆ i, I i := Subgroup.noncommPiCoprod_range
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.1 (by rw [hΦrange]; exact hwJ)
    have hΦeq : ∀ v : ∀ i, I i, Φ v = ∏ i, (v i : W) := by
      intro v
      rw [Subgroup.noncommPiCoprod_apply]
      exact Finset.noncommProd_eq_prod _ _
    have hufix : ∀ i, (u i : W) ∈ fixV X := by
      intro i
      rw [mem_fixV]
      intro x hx
      let u' : ∀ j, I j := fun j => ⟨x (u j), hXI j x hx (u j) (u j).2⟩
      have hΦu' : Φ u' = x (Φ u) := by
        rw [hΦeq u', hΦeq u, map_prod]
      have hEq : u' = u := by
        apply hΦinj
        rw [hΦu', hu]
        exact (mem_fixV.1 hwfix) x hx
      exact congrArg Subtype.val (congrFun hEq i)
    rw [← hu, hΦeq u]
    exact Subgroup.prod_mem (⨆ i, (I i ⊓ fixV X)) (t := Finset.univ)
      (fun i _ => Subgroup.mem_iSup_of_mem i (Subgroup.mem_inf.2 ⟨(u i).2, hufix i⟩))
  · refine iSup_le fun i => le_inf ?_ ?_
    · exact le_trans inf_le_left (le_iSup I i)
    · exact inf_le_right

private theorem s1611e3_card_iSup_of_iSupIndep {W : Type} [CommGroup W] [Finite W]
    {ι : Type} [Fintype ι] [DecidableEq ι] {I : ι → Subgroup W} (hind : iSupIndep I) :
    Nat.card ↥(⨆ i, I i) = ∏ i, Nat.card (I i) := by
  let hcomm : Pairwise fun i j => ∀ x y : W, x ∈ I i → y ∈ I j → Commute x y :=
    fun _ _ _ _ _ _ _ => Commute.all _ _
  let Φ : (∀ i, I i) →* W := Subgroup.noncommPiCoprod hcomm
  have hΦinj : Function.Injective Φ := Subgroup.injective_noncommPiCoprod_of_iSupIndep hind
  have hΦrange : Φ.range = ⨆ i, I i := Subgroup.noncommPiCoprod_range
  have hker : Φ.ker = ⊥ := (MonoidHom.ker_eq_bot_iff Φ).mpr hΦinj
  have h1 := Subgroup.card_ker_mul_card_range Φ
  rw [hker, Subgroup.card_bot, one_mul] at h1
  rw [← hΦrange, h1, Nat.card_pi]

private lemma s1611e3_isIrr_of_binaryNatSummand {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {I : Subgroup W} (h : BinaryNaturalSL L I ⊥ 3 1) : XMod.IsIrr ↥L I := by
  obtain ⟨K, _, _, _, _, hπ⟩ := h
  exact CFSG.Quasithin.B5.isIrr_of_realizes (n := 3) (by norm_num) hπ

theorem s1611e3_para_stab {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} (hL : IsL3 ↥L 1) {J : Subgroup W} {n p : ℕ}
    (hnp : (p = 3 ∧ n = 2) ∨ (p = 7 ∧ n = 3))
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) L J ⊥ n)
    {T₁ : Subgroup (MulAut W)} (hT₁L : T₁ ≤ L) (hT₁ : IsSylowIn 2 T₁ L)
    {Z : Subgroup (MulAut W)} (hZ : Nat.card ↥Z = p)
    (hZJ : ∀ z ∈ Z, ∀ w ∈ J, z w ∈ J) (hZL : ∀ z ∈ Z, ∀ l ∈ L, z * l = l * z)
    (hZf : ∀ z ∈ Z, z ≠ 1 → ∃ w ∈ J, z w ≠ w) :
    ∀ w ∈ J ⊓ fixV T₁, w ≠ 1 → Nat.card ↥(L ⊓ centSub (Subgroup.zpowers w)) = 24 := by
  classical
  haveI : Fintype W := Fintype.ofFinite W
  have hp : p.Prime := by rcases hnp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  obtain ⟨I, -, hind, hsup, hnat⟩ := hsum
  have hJ : J = ⨆ i, I i := by rw [← hsup, bot_sup_eq]
  have hindep : iSupIndep I := by
    rw [iSupIndep_def]
    intro i
    rw [disjoint_iff]
    exact le_bot_iff.mp (by simpa [bot_sup_eq] using hind i)
  have hIirr : ∀ i, XMod.IsIrr ↥L (I i) := fun i => s1611e3_isIrr_of_binaryNatSummand (hnat i)
  have hIinv : ∀ i, XMod.IsInv ↥L (I i) := fun i => (hIirr i).1
  have hstableL : ∀ i, ∀ x ∈ L, ∀ w ∈ I i, x w ∈ I i := by
    intro i x hx w hw
    have h := hIinv i ⟨x, hx⟩ w hw
    simpa [MulAut.smul_def] using h
  have hstable : ∀ i, ∀ x ∈ T₁, ∀ w ∈ I i, x w ∈ I i :=
    fun i x hx => hstableL i x (hT₁L hx)
  have hnatStab : ∀ i, Nat.card ↥(I i ⊓ fixV T₁) = 2 :=
    fun i => (s1611e3_natural_stab hL (hnat i) hT₁L hT₁).1
  have hnatCent : ∀ i, ∀ w ∈ I i, w ≠ 1 →
      Nat.card ↥(L ⊓ centSub (Subgroup.zpowers w)) = 24 :=
    fun i => (s1611e3_natural_stab hL (hnat i) hT₁L hT₁).2
  have hCeq : J ⊓ fixV T₁ = ⨆ i, (I i ⊓ fixV T₁) := by
    rw [hJ]
    exact s1611e3_inf_fixV_iSup hindep hstable
  have hCind : iSupIndep (fun i => I i ⊓ fixV T₁) :=
    hindep.mono (fun i => inf_le_left)
  have hCcard : Nat.card ↥(J ⊓ fixV T₁) = 2 ^ n := by
    rw [hCeq, s1611e3_card_iSup_of_iSupIndep hCind]
    rw [Finset.prod_congr rfl (fun i _ => hnatStab i)]
    simp [Finset.prod_const, Fintype.card_fin]
  have hp1C : Nat.card ↥(J ⊓ fixV T₁) = p + 1 := by
    rcases hnp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simpa using hCcard
  have hn0 : n ≠ 0 := by rcases hnp with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> norm_num
  haveI : NeZero n := ⟨hn0⟩
  have hcard0 : Nat.card ↥(I (0 : Fin n) ⊓ fixV T₁) = 2 := hnatStab 0
  haveI : Nontrivial ↥(I (0 : Fin n) ⊓ fixV T₁) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard0]; norm_num)
  obtain ⟨e, he1⟩ := exists_ne (1 : ↥(I (0 : Fin n) ⊓ fixV T₁))
  have heI : (e : W) ∈ I (0 : Fin n) := (Subgroup.mem_inf.1 e.2).1
  have hefix : (e : W) ∈ fixV T₁ := (Subgroup.mem_inf.1 e.2).2
  have heC : (e : W) ∈ J ⊓ fixV T₁ := by
    rw [hJ]
    exact Subgroup.mem_inf.2 ⟨le_iSup I 0 heI, hefix⟩
  have hene : (e : W) ≠ 1 := fun h => he1 (Subtype.ext h)
  have heCent : Nat.card ↥(L ⊓ centSub (Subgroup.zpowers (e : W))) = 24 :=
    hnatCent 0 (e : W) heI hene
  obtain ⟨z, hzZ, hz1⟩ : ∃ z : MulAut W, z ∈ Z ∧ z ≠ 1 := by
    have hnt : Nontrivial ↥Z :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hZ]; exact hp.one_lt)
    obtain ⟨z, hz1⟩ := exists_ne (1 : ↥Z)
    exact ⟨z, z.2, fun h => hz1 (Subtype.ext h)⟩
  let H : Subgroup (MulAut W) := Subgroup.zpowers z
  have hHZ : H ≤ Z := Subgroup.zpowers_le.mpr hzZ
  have hHcard : Nat.card ↥H = p := by
    have hdvd : Nat.card ↥H ∣ p := by
      rw [← hZ]
      exact Subgroup.card_dvd_of_le hHZ
    have hne1 : Nat.card ↥H ≠ 1 := by
      intro h
      have hbot : H = ⊥ := Subgroup.card_eq_one.mp h
      have : z ∈ (⊥ : Subgroup (MulAut W)) := hbot ▸ Subgroup.mem_zpowers z
      exact hz1 (Subgroup.mem_bot.mp this)
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
    · exact absurd h hne1
    · exact h
  let C : Subgroup W := J ⊓ fixV T₁
  have hZC : ∀ h ∈ Z, ∀ c ∈ C, h c ∈ C := by
    intro h hh c hc
    obtain ⟨hcJ, hcfix⟩ := Subgroup.mem_inf.1 hc
    refine Subgroup.mem_inf.2 ⟨hZJ h hh c hcJ, ?_⟩
    rw [mem_fixV]
    intro t ht
    have hcomm : h * t = t * h := hZL h hh t (hT₁L ht)
    have h1 : h (t c) = t (h c) := by
      have hc' := congrArg (fun f : MulAut W => f c) hcomm
      simpa [MulAut.mul_apply] using hc'
    rw [hcfix t ht] at h1
    exact h1.symm
  letI : MulAction ↥H ↥C :=
    { smul := fun h c => ⟨(h : MulAut W) (c : W), hZC (h : MulAut W) (hHZ h.2) (c : W) c.2⟩
      one_smul := fun c => Subtype.ext rfl
      mul_smul := fun h1 h2 c => Subtype.ext rfl }
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hHp : IsPGroup p ↥H := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hHcard)
  have hcardCfin : Fintype.card ↥C = p + 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact hp1C
  have hmod0 : Nat.card ↥C ≡ Nat.card (MulAction.fixedPoints ↥H ↥C) [MOD p] :=
    IsPGroup.card_modEq_card_fixedPoints hHp ↥C
  have hfixcard : Nat.card (MulAction.fixedPoints ↥H ↥C) = Nat.card ↥(C ⊓ fixV H) := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun c => ⟨c.1.1, Subgroup.mem_inf.2 ⟨c.1.2, ?_⟩⟩
        invFun := fun c => ⟨⟨c.1, (Subgroup.mem_inf.1 c.2).1⟩, ?_⟩
        left_inv := fun c => Subtype.ext rfl
        right_inv := fun c => Subtype.ext rfl }
    · rw [mem_fixV]
      intro h hh
      exact congrArg Subtype.val (c.2 ⟨h, hh⟩)
    · intro h
      apply Subtype.ext
      exact (mem_fixV.1 (Subgroup.mem_inf.1 c.2).2) h h.2
  set count : ℕ := Nat.card (MulAction.fixedPoints ↥H ↥C) with hcount_def
  haveI : Nonempty ↥C := ⟨1⟩
  haveI : Nonempty (MulAction.fixedPoints ↥H ↥C) :=
    ⟨⟨1, MulAction.mem_fixedPoints.mpr fun h => Subtype.ext (map_one (h : MulAut W))⟩⟩
  have hcount_ge : 1 ≤ count := by rw [hcount_def]; exact Nat.card_pos
  have hcount_le : count ≤ p + 1 := by
    rw [hfixcard, ← hp1C]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le inf_le_left)
  have hcount_ne : count ≠ p + 1 := by
    intro hcount
    have hcardC : Nat.card ↥(C ⊓ fixV H) = Nat.card ↥C := by
      rw [← hfixcard, hcount, hp1C]
    have heq : C ⊓ fixV H = C :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq hcardC.symm)
    have hCle : C ≤ fixV H := by rw [← heq]; exact inf_le_right
    have hJfix : J ≤ fixV H := by
      rw [hJ]
      refine iSup_le fun i => ?_
      let S : Subgroup W := fixV H ⊓ I i
      have hSle : S ≤ I i := inf_le_right
      have hSinv : XMod.IsInv ↥L S := by
        intro a v hv
        obtain ⟨hvfix, hvI⟩ := Subgroup.mem_inf.1 hv
        refine Subgroup.mem_inf.2 ⟨?_, hstableL i (a : MulAut W) a.2 v hvI⟩
        rw [mem_fixV] at hvfix ⊢
        intro k hk
        have hcomm : Commute k (a : MulAut W) :=
          s1611e3_zpowers_commute (hZL z hzZ (a : MulAut W) a.2) hk
        have h1 : k ((a : MulAut W) v) = (a : MulAut W) (k v) := by
          have hk' := congrArg (fun f : MulAut W => f v) hcomm.eq
          simpa [MulAut.mul_apply] using hk'
        change k ((a : MulAut W) v) = (a : MulAut W) v
        rw [h1, hvfix k hk]
      obtain ⟨e', he'1⟩ : ∃ e' : ↥(I i ⊓ fixV T₁), e' ≠ 1 := by
        haveI : Nontrivial ↥(I i ⊓ fixV T₁) :=
          Finite.one_lt_card_iff_nontrivial.mp (by rw [hnatStab i]; norm_num)
        exact exists_ne 1
      have he'S : (e' : W) ∈ S := by
        refine Subgroup.mem_inf.2 ⟨?_, (Subgroup.mem_inf.1 e'.2).1⟩
        apply hCle
        refine Subgroup.mem_inf.2 ⟨?_, (Subgroup.mem_inf.1 e'.2).2⟩
        rw [hJ]
        exact le_iSup I i (Subgroup.mem_inf.1 e'.2).1
      have hSne : S ≠ ⊥ := by
        intro hbot
        have : (e' : W) ∈ (⊥ : Subgroup W) := hbot ▸ he'S
        exact he'1 (Subtype.ext (Subgroup.mem_bot.mp this))
      rcases (hIirr i).2.2 S hSinv bot_le hSle with h | h
      · exact absurd h hSne
      · rw [← h]; exact inf_le_left
    obtain ⟨w, hwJ, hwmoved⟩ := hZf z hzZ hz1
    exact hwmoved (mem_fixV.1 (hJfix hwJ) z (Subgroup.mem_zpowers z))
  have hcount_eq : count = 1 := by
    have hmod' : (p + 1) % p = count % p := by
      rw [← hp1C]
      exact hmod0
    have hpmod : (p + 1) % p = 1 := by
      rw [Nat.add_mod_left]
      exact Nat.mod_eq_of_lt hp.one_lt
    have hmod'' : count % p = 1 := by rw [← hmod', hpmod]
    rcases Nat.lt_or_ge count p with hlt | hge
    · rwa [Nat.mod_eq_of_lt hlt] at hmod''
    · have : count = p ∨ count = p + 1 := by omega
      rcases this with h | h
      · rw [h, Nat.mod_self] at hmod''
        exact absurd hmod'' (by norm_num)
      · exact absurd h hcount_ne
  have hfixbot : C ⊓ fixV H = ⊥ := by
    have h : Nat.card ↥(C ⊓ fixV H) = 1 := by rw [← hfixcard, hcount_eq]
    exact Subgroup.card_eq_one.mp h
  let e0 : ↥C := ⟨(e : W), heC⟩
  have he0ne : e0 ≠ 1 := fun h => hene (congrArg Subtype.val h)
  have he0notfix : e0 ∉ MulAction.fixedPoints ↥H ↥C := by
    intro hfix
    have hmem : (e : W) ∈ C ⊓ fixV H :=
      Subgroup.mem_inf.2 ⟨heC, by
        rw [mem_fixV]
        intro h hh
        exact congrArg Subtype.val (hfix ⟨h, hh⟩)⟩
    have hbot : (e : W) ∈ (⊥ : Subgroup W) := hfixbot ▸ hmem
    exact hene (Subgroup.mem_bot.mp hbot)
  let O : Set ↥C := MulAction.orbit ↥H e0
  let T : Set ↥C := {c | c ≠ 1}
  have hOsub : O ⊆ T := by
    rintro c hc hc1
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hc
    exact he0ne (by
      calc e0 = (g⁻¹ * g) • e0 := by rw [inv_mul_cancel, one_smul]
        _ = g⁻¹ • (g • e0) := by rw [mul_smul]
        _ = g⁻¹ • c := by rw [hg]
        _ = g⁻¹ • (1 : ↥C) := by rw [hc1]
        _ = 1 := Subtype.ext (map_one ((g⁻¹ : ↥H) : MulAut W)))
  have hcardT : Nat.card T = p := by
    rw [Nat.card_eq_fintype_card, Set.card_ne_eq, hcardCfin]
    omega
  have hcardH : Fintype.card ↥H = p := by
    rw [← Nat.card_eq_fintype_card]
    exact hHcard
  have hcardO : Nat.card O = p := by
    have hne : Fintype.card O ≠ 1 := by
      intro h
      exact he0notfix (MulAction.mem_fixedPoints_iff_card_orbit_eq_one.mpr h)
    have hdvd : Fintype.card O ∣ p := by
      rw [← hcardH]
      exact ⟨Fintype.card (MulAction.stabilizer ↥H e0),
        (MulAction.card_orbit_mul_card_stabilizer_eq_card_group ↥H e0).symm⟩
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
    · exact absurd h hne
    · rw [Nat.card_eq_fintype_card]; exact h
  have hOT : O = T := by
    refine Set.eq_of_subset_of_ncard_le hOsub ?_ (Set.toFinite T)
    show Nat.card T ≤ Nat.card O
    rw [hcardT, hcardO]
  intro w hwC hwne
  have hc : (⟨w, hwC⟩ : ↥C) ≠ 1 := fun h => hwne (congrArg Subtype.val h)
  have hcO : (⟨w, hwC⟩ : ↥C) ∈ O := by rw [hOT]; exact hc
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hcO
  have hge : (g : MulAut W) (e : W) = w := congrArg Subtype.val hg
  have hgZ : (g : MulAut W) ∈ Z := hHZ g.2
  have hstab_eq : L ⊓ centSub (Subgroup.zpowers w) =
      L ⊓ centSub (Subgroup.zpowers (e : W)) := by
    ext l
    rw [Subgroup.mem_inf, Subgroup.mem_inf, s1611e3_mem_centSub_zpowers_iff,
      s1611e3_mem_centSub_zpowers_iff]
    constructor
    · rintro ⟨hlL, hlw⟩
      refine ⟨hlL, ?_⟩
      have hcomm : Commute (g : MulAut W) l := hZL (g : MulAut W) hgZ l hlL
      have h1 : l ((g : MulAut W) (e : W)) = (g : MulAut W) (l (e : W)) := by
        have h := congrArg (fun f : MulAut W => f (e : W)) hcomm.eq
        simpa [MulAut.mul_apply] using h.symm
      have h2 : (g : MulAut W) (l (e : W)) = (g : MulAut W) (e : W) := by
        calc (g : MulAut W) (l (e : W)) = l ((g : MulAut W) (e : W)) := h1.symm
          _ = l w := by rw [hge]
          _ = w := hlw
          _ = (g : MulAut W) (e : W) := hge.symm
      exact (g : MulAut W).injective h2
    · rintro ⟨hlL, hle⟩
      refine ⟨hlL, ?_⟩
      have hcomm : Commute (g : MulAut W) l := hZL (g : MulAut W) hgZ l hlL
      have h1 : l ((g : MulAut W) (e : W)) = (g : MulAut W) (l (e : W)) := by
        have h := congrArg (fun f : MulAut W => f (e : W)) hcomm.eq
        simpa [MulAut.mul_apply] using h.symm
      rw [← hge, h1, hle]
  rw [hstab_eq]
  exact heCent

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
