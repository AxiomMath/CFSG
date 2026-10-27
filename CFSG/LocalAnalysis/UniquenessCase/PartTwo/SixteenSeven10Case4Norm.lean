module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case4Sym
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Norm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

private theorem s16c1610_comm_of_isElemAbelianOfRank {X : Type*} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) : ∀ a b : X, a * b = b * a := by
  obtain ⟨e⟩ := h
  intro a b
  exact e.injective (by rw [map_mul, map_mul, mul_comm])

private theorem s16c1610_false_of_isQuasisimple_of_comm {X : Type*} [Group X]
    (hcomm : ∀ a b : X, a * b = b * a) (h : CFSG.Open.IsQuasisimple X) : False := by
  have hcenter : Subgroup.center X = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    exact hcomm y x
  have hbot : commutator X = ⊥ := (commutator_eq_bot_iff_center_eq_top X).mpr hcenter
  have hperf : commutator X = ⊤ := h.1
  have htopbot : (⊤ : Subgroup X) = ⊥ := hperf ▸ hbot
  haveI : Subsingleton X := by
    rw [Subgroup.eq_bot_iff_forall] at htopbot
    exact ⟨fun a b => (htopbot a trivial).trans (htopbot b trivial).symm⟩
  haveI : Nontrivial (X ⧸ Subgroup.center X) := h.2.toNontrivial
  obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial (X ⧸ Subgroup.center X)).exists_pair_ne
  exact hab (Subsingleton.elim a b)

private theorem s16c1610_rk_commSub_eq_six_of_conc4133 {W : Type} [CommGroup W] [Finite W]
    {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hcardL : Nat.card ↥L = 9) (hrkW : rk W = 6) (h : Conc4_133 A t L) :
    rk ↥(commSub ⊤ L) = 6 := by
  obtain ⟨p, hpp, _, _, _, halt⟩ := h
  have hrk_le : rk ↥(commSub ⊤ L) ≤ 6 := by
    have h := rk_mono (H := commSub ⊤ L) (K := ⊤) le_top
    rw [rk_top, hrkW] at h
    exact h
  rcases halt with ⟨hcyc, h | h | h⟩ | ⟨hcyc, h⟩ | ⟨h1p2, h⟩ | ⟨hEA, h8, _⟩ |
    ⟨hcyc, h | h⟩ | ⟨r, m, hpm, hr2, hEAr, hrk, _⟩ | ⟨hEA, h6, _⟩
  · exfalso; have := hcyc.2; omega
  · exfalso; have := hcyc.2; omega
  · exact h
  · exfalso; have := hcyc.2; omega
  · exact h
  · exfalso; omega
  · exfalso; have := hcyc.2; omega
  · exfalso; have := hcyc.2; omega
  · rcases hpm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hp3 : 3 ^ r = 9 := by
        rw [← hcardL]
        exact (A38.card_eq_of_isElemAbelianOfRank (by norm_num : Nat.Prime 3) hEAr).symm
      have hp32 : 3 ^ r = 3 ^ 2 := by rw [hp3]; norm_num
      have hr : r = 2 := Nat.pow_right_injective (by norm_num : 2 ≤ 3) hp32
      rw [hr] at hrk
      rw [hrk]
    · exfalso
      have hp7 : 7 ^ r = 9 := by
        rw [← hcardL]
        exact (A38.card_eq_of_isElemAbelianOfRank (by norm_num : Nat.Prime 7) hEAr).symm
      have h7 : 7 ^ 2 ≤ 7 ^ r := Nat.pow_le_pow_right (by norm_num) hr2
      rw [hp7] at h7
      norm_num at h7
  · exact h6

theorem s16c1610_lBar_normal_of_case4_two (D : Data G) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV)
    (h4 : Case168_4At D V₀ V hV L 3 2) :
    ∀ m ∈ Mbar D.M V₀ V hV, ∀ x ∈ lBar V₀ V hV L,
      m * x * m⁻¹ ∈ lBar V₀ V hV L := by
  classical
  obtain ⟨t, htA, ht2, ht1, htrk, hW136⟩ := hc.conc
  obtain ⟨hsupW, hnormW, hthird⟩ := hW136
  have hcardL : Nat.card ↥(lBar V₀ V hV L) = 9 := by
    have h := A38.card_eq_of_isElemAbelianOfRank (q := 3) (n := 2) (by norm_num) h4.1
    simpa using h
  have hcommL : ∀ a b : ↥(lBar V₀ V hV L), a * b = b * a :=
    s16c1610_comm_of_isElemAbelianOfRank h4.1
  have hrkW : rk (Vtil V₀ V hV) = 6 := (s16c1610_case4_two_card D hV h4).1
  have hrk6 : rk ↥(commSub ⊤ (lBar V₀ V hV L)) = 6 := by
    rcases hthird with h133 | ⟨K, hKmem, g, hgA, hKg, hLK, htens⟩ |
      ⟨hcomp3, _, _⟩ | ⟨_, _, hcomp4, _⟩
    · exact s16c1610_rk_commSub_eq_six_of_conc4133 hcardL hrkW h133
    · exfalso
      have hKL : K ≤ lBar V₀ V hV L := by rw [hLK]; exact le_sup_left
      have hcommK : ∀ a b : ↥K, a * b = b * a := by
        intro a b
        apply Subtype.ext
        simpa using congrArg Subtype.val (hcommL ⟨(a : MulAut (Vtil V₀ V hV)), hKL a.2⟩
          ⟨(b : MulAut (Vtil V₀ V hV)), hKL b.2⟩)
      exact s16c1610_false_of_isQuasisimple_of_comm hcommK hKmem.2.2
    · exfalso
      exact s16c1610_false_of_isQuasisimple_of_comm hcommL hcomp3.2.2
    · exfalso
      exact s16c1610_false_of_isQuasisimple_of_comm hcommL hcomp4.2.2
  have hcommSubTop : commSub ⊤ (lBar V₀ V hV L) = ⊤ := by
    refine eq_of_le_of_rk_le (Vtil_pow_two hV) le_top ?_
    rw [rk_top, hrkW, hrk6]
  intro m hm x hx
  by_cases hmN : m ∈ normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV)))
  · exact (Subgroup.mem_normalizer_iff.mp hmN x).mp hx
  · exfalso
    have hbot := (hnormW m hm hmN).2
    rw [hcommSubTop] at hbot
    have hmapbot : (lBar V₀ V hV L).map (MulAut.conj m).toMonoidHom = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro φ hφ
      apply MulEquiv.ext
      intro v
      exact (mem_fixV.mp (commSub_eq_bot_iff.mp hbot (Subgroup.mem_top v))) φ hφ
    have hcardmap : Nat.card ↥((lBar V₀ V hV L).map (MulAut.conj m).toMonoidHom) = 9 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj m).injective, hcardL]
    rw [hmapbot, Subgroup.card_bot] at hcardmap
    omega


private def s16c1610_pointStab {X : Type*} [Group X] (Y : Subgroup X) : Subgroup (MulAut X) where
  carrier := {l : MulAut X | ∀ y ∈ Y, l y = y}
  mul_mem' := by intro a b ha hb y hy; rw [MulAut.mul_apply, hb y hy, ha y hy]
  one_mem' := by intro y _; rfl
  inv_mem' := by
    intro a ha y hy
    have h1 : a⁻¹ y = a⁻¹ (a y) := congrArg (fun t => a⁻¹ t) (ha y hy).symm
    have h2 : a⁻¹ (a y) = y := by
      have := congrArg (fun f : MulAut X => f y) (inv_mul_cancel a)
      simpa [MulAut.mul_apply] using this
    exact h1.trans h2

private noncomputable def s16c1610_restrictAut {X : Type*} [Group X] (α : MulAut X)
    (P : Subgroup X) (hP : P.map (α : X →* X) = P) : MulAut P :=
  (α.subgroupMap P).trans (MulEquiv.subgroupCongr hP)

private theorem s16c1610_coe_restrictAut {X : Type*} [Group X] (α : MulAut X) {P : Subgroup X}
    (hP : P.map (α : X →* X) = P) (x : P) :
    ((s16c1610_restrictAut α P hP x : P) : X) = α x :=
  rfl

private noncomputable def s16c1610_restrictAutHom {X : Type*} [Group X]
    (L : Subgroup (MulAut X)) (Y : Subgroup X)
    (h : ∀ l ∈ L, Y.map (l : X →* X) = Y) : ↥L →* MulAut ↥Y where
  toFun l := s16c1610_restrictAut (l : MulAut X) Y (h l l.2)
  map_one' := by
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    rw [s16c1610_coe_restrictAut]
    rfl
  map_mul' a b := by
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    rw [s16c1610_coe_restrictAut, MulAut.mul_apply, s16c1610_coe_restrictAut,
      s16c1610_coe_restrictAut]
    rfl

private theorem s16c1610_ker_restrictAutHom {X : Type*} [Group X]
    (L : Subgroup (MulAut X)) (Y : Subgroup X)
    (h : ∀ l ∈ L, Y.map (l : X →* X) = Y) :
    (s16c1610_restrictAutHom L Y h).ker.map L.subtype = L ⊓ s16c1610_pointStab Y := by
  ext l
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k.2, ?_⟩
    intro y hy
    have h1 : s16c1610_restrictAut (k : MulAut X) Y (h k k.2) = 1 := hk
    have h2 := congrArg (fun f : MulAut ↥Y => ((f ⟨y, hy⟩ : ↥Y) : X)) h1
    rw [s16c1610_coe_restrictAut] at h2
    simpa using h2
  · rintro ⟨hlL, hlY⟩
    refine ⟨⟨l, hlL⟩, ?_, rfl⟩
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    show ((s16c1610_restrictAut (l : MulAut X) Y (h l hlL)) y : X) = ((1 : MulAut ↥Y) y : X)
    rw [s16c1610_coe_restrictAut, MulAut.one_apply]
    exact hlY y y.2

private theorem s16c1610_map_inf {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Injective f) (H K : Subgroup X) :
    (H ⊓ K).map f = H.map f ⊓ K.map f := by
  apply le_antisymm (Subgroup.map_inf_le H K f)
  intro x hx
  obtain ⟨hxH, hxK⟩ := hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxH
  obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hxK
  have hyz : y = z := hf (hyx.trans hzx.symm)
  subst hyz
  exact Subgroup.mem_map.mpr ⟨y, ⟨hy, hz⟩, hyx⟩

private theorem s16c1610_zpowers_subgroupOf {W : Type} [Group W] (L : Subgroup W) (x : ↥L) :
    (Subgroup.zpowers (x : W)).subgroupOf L = Subgroup.zpowers x := by
  ext y
  constructor
  · intro hy
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff] at hy
    obtain ⟨n, hn⟩ := hy
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext (by simpa using hn)⟩
  · intro hy
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ⟨n, congrArg Subtype.val hn⟩

private theorem s16c1610_ncard_orderThree_subgroups {W : Type} [Group W] [Finite W]
    (L : Subgroup W) (hcard : Nat.card ↥L = 9) (hexp : ∀ x : ↥L, x ^ 3 = 1) :
    (Set.ncard {X : Subgroup W | X ≤ L ∧ Nat.card X = 3}) = 4 := by
  classical
  haveI : Fintype W := Fintype.ofFinite W
  haveI : Fintype ↥L := Fintype.ofFinite ↥L
  haveI : Fintype (Subgroup W) :=
    Fintype.ofInjective (fun X : Subgroup W => (X : Set W)) SetLike.coe_injective
  have hOrder : ∀ x : ↥L, x ≠ 1 → orderOf x = 3 := by
    intro x hx
    have hdvd : orderOf x ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr (hexp x)
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx
    · exact h
  let S : Finset ↥L := Finset.univ.filter (fun x => x ≠ 1)
  have hS_eq : S = Finset.univ.erase (1 : ↥L) := by
    ext x; simp [S]
  have hcardL : Fintype.card ↥L = 9 := by rw [← Nat.card_eq_fintype_card, hcard]
  have hScard : S.card = 8 := by
    rw [hS_eq, Finset.card_erase_of_mem (Finset.mem_univ (1 : ↥L)), Finset.card_univ, hcardL]
  let g : ↥L → Subgroup W := fun x => Subgroup.zpowers (x : W)
  have himg : S.image g = Finset.univ.filter (fun X : Subgroup W => X ≤ L ∧ Nat.card X = 3) := by
    ext X
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hxS, rfl⟩
      have hxne : x ≠ 1 := by simpa [S] using hxS
      exact ⟨Subgroup.zpowers_le.mpr x.2,
        by rw [Nat.card_zpowers, Subgroup.orderOf_coe]; exact hOrder x hxne⟩
    · rintro ⟨hXL, hXc⟩
      have hXne : X ≠ ⊥ := by
        intro h; rw [h, Subgroup.card_bot] at hXc; norm_num at hXc
      obtain ⟨x0, hx0ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hXne
      have hx0ne' : (x0 : W) ≠ 1 := fun h => hx0ne (Subtype.ext h)
      refine ⟨⟨(x0 : W), hXL x0.2⟩, ?_, ?_⟩
      · have hx0neL : (⟨(x0 : W), hXL x0.2⟩ : ↥L) ≠ 1 := by
          rw [ne_eq, Subtype.ext_iff]; exact hx0ne'
        simp [S, hx0neL]
      · have hx0ord : orderOf (x0 : W) = 3 := by
          have hdvd : orderOf (x0 : W) ∣ 3 :=
            orderOf_dvd_iff_pow_eq_one.mpr (by
              have := hexp ⟨(x0 : W), hXL x0.2⟩
              simpa using this)
          rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
          · exact absurd (orderOf_eq_one_iff.mp h) hx0ne'
          · exact h
        apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr x0.2)
        rw [Nat.card_zpowers, hx0ord, hXc]
  have hfiber : ∀ X ∈ S.image g, (S.filter (fun x => g x = X)).card = 2 := by
    intro X hX
    obtain ⟨x0, hx0S, rfl⟩ := Finset.mem_image.mp hX
    have hx0ne : x0 ≠ 1 := by simpa [S] using hx0S
    have hx0ord : orderOf x0 = 3 := hOrder x0 hx0ne
    let H : Subgroup ↥L := Subgroup.zpowers x0
    let HF : Finset ↥L := Finset.univ.filter (fun x => x ∈ H)
    have hHFcard : HF.card = 3 := by
      have h1 : HF.card = Nat.card ↥(Subgroup.zpowers x0) := by
        rw [Nat.card_eq_fintype_card,
          ← Fintype.card_subtype (fun x : ↥L => x ∈ Subgroup.zpowers x0)]
      rw [h1, Nat.card_zpowers, hx0ord]
    have h1mem : (1 : ↥L) ∈ HF := by simp [HF, H]
    have hset : S.filter (fun x => g x = Subgroup.zpowers (x0 : W)) = HF.erase 1 := by
      ext x
      simp only [Finset.mem_filter, S, Finset.mem_univ, true_and, Finset.mem_erase, HF, H]
      constructor
      · rintro ⟨hxne, hgx⟩
        have hmem : (x : W) ∈ Subgroup.zpowers (x0 : W) :=
          hgx ▸ Subgroup.mem_zpowers (x : W)
        rw [← Subgroup.mem_subgroupOf, s16c1610_zpowers_subgroupOf L x0] at hmem
        exact ⟨hxne, hmem⟩
      · rintro ⟨hxne, hxmem⟩
        refine ⟨hxne, ?_⟩
        have hzp : Subgroup.zpowers x = Subgroup.zpowers x0 := by
          apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxmem)
          rw [Nat.card_zpowers, Nat.card_zpowers, hOrder x hxne, hx0ord]
        have hmap := congrArg (Subgroup.map L.subtype) hzp
        rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at hmap
        simpa using hmap
    rw [hset, Finset.card_erase_of_mem h1mem, hHFcard]
  have hsum := Finset.card_eq_sum_card_image g S
  rw [hScard, Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul] at hsum
  have hTcard : (S.image g).card = 4 := by omega
  have hsetT : ({X : Subgroup W | X ≤ L ∧ Nat.card X = 3} : Set (Subgroup W)) =
      (↑(S.image g) : Set (Subgroup W)) := by
    rw [himg]; ext X; simp
  rw [hsetT, Set.ncard_coe_finset, hTcard]

theorem s16c1610_exists_normal_three_of_symSum_two {W : Type} [CommGroup W] [Finite W]
    (h2 : ∀ w : W, w ^ 2 = 1) {A Lb : Subgroup (MulAut W)} (hLA : Lb ≤ A)
    (hLn : ∀ m ∈ A, ∀ x ∈ Lb, m * x * m⁻¹ ∈ Lb) (hL : IsElemAbelianOfRank 3 2 ↥Lb)
    (hS : SymSumOfConj A (⊤ : Subgroup W) 2 2) :
    ∃ X : Subgroup (MulAut W), X ≤ A ∧ Nat.card X = 3 ∧
      ∀ m ∈ A, ∀ x ∈ X, m * x * m⁻¹ ∈ X := by
  classical
  haveI : Fintype W := Fintype.ofFinite W
  haveI : Fintype (Subgroup W) :=
    Fintype.ofInjective (fun X : Subgroup W => (X : Set W)) SetLike.coe_injective
  obtain ⟨Z, hZrk, hZind, hZsup, hZcard, hZperm⟩ := hS
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W))
      (fun f g h => MulEquiv.ext (congrFun h))
  have hcardLb : Nat.card ↥Lb = 9 := by
    have h := A38.card_eq_of_isElemAbelianOfRank (q := 3) (n := 2) (by norm_num) hL
    simpa using h
  have hexpLb : ∀ x : ↥Lb, x ^ 3 = 1 := by
    obtain ⟨e⟩ := hL
    intro x
    apply e.injective
    rw [map_pow, map_one]
    ext i
    simp
    exact Or.inl (by decide)
  let Xs : Set (Subgroup W) := conjSubs A Z
  haveI hfinXs : Finite ↥Xs := by
    refine Finite.of_surjective
      (fun g : ↥A => (⟨Z.map (g : MulAut W).toMonoidHom,
        ⟨(g : MulAut W), g.2, rfl⟩⟩ : ↥Xs)) ?_
    rintro ⟨Y, hY⟩
    obtain ⟨g, hg, rfl⟩ := hY
    exact ⟨⟨g, hg⟩, rfl⟩
  have hcardXs : Nat.card ↥Xs = 3 := by
    rw [Nat.card_coe_set_eq]
    show (conjSubs A Z).ncard = 3
    omega
  have hmemAct : ∀ (a : ↥A) (Y : ↥Xs),
      ((Y : Subgroup W).map (a : MulAut W).toMonoidHom) ∈ Xs := by
    intro a Y
    obtain ⟨g, hg, hgY⟩ := Y.2
    refine ⟨(a : MulAut W) * g, A.mul_mem a.2 hg, ?_⟩
    rw [hgY, Subgroup.map_map]; rfl
  letI : MulAction ↥A ↥Xs :=
    { smul := fun a Y =>
        ⟨(Y : Subgroup W).map (a : MulAut W).toMonoidHom, hmemAct a Y⟩
      one_smul := by
        intro Y
        apply Subtype.ext
        show (Y : Subgroup W).map (MonoidHom.id W) = (Y : Subgroup W)
        rw [Subgroup.map_id]
      mul_smul := by
        intro a b Y
        apply Subtype.ext
        show (Y : Subgroup W).map (((a * b : ↥A) : MulAut W)).toMonoidHom
            = ((Y : Subgroup W).map (b : MulAut W).toMonoidHom).map
                (a : MulAut W).toMonoidHom
        rw [Subgroup.map_map]
        rfl }
  let ρ : ↥A →* Equiv.Perm ↥Xs := MulAction.toPermHom ↥A ↥Xs
  have hρsurj : Function.Surjective ρ := by
    intro π
    obtain ⟨g, hg, hgπ⟩ := hZperm π
    refine ⟨⟨g, hg⟩, ?_⟩
    apply Equiv.ext
    intro Y
    exact Subtype.ext (hgπ Y)
  let K : Subgroup ↥A := Lb.subgroupOf A ⊓ ρ.ker
  have hKnormal : K.Normal := by
    have h1 : (Lb.subgroupOf A).Normal :=
      (Subgroup.normal_subgroupOf_iff hLA).mpr (fun h k hh hk => hLn k hk h hh)
    show (Lb.subgroupOf A ⊓ ρ.ker).Normal
    infer_instance
  let ρ' : ↥(Lb.subgroupOf A) →* Equiv.Perm ↥Xs := ρ.comp (Lb.subgroupOf A).subtype
  have hcardLbA : Nat.card ↥(Lb.subgroupOf A) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLA).toEquiv, hcardLb]
  have hKmap : K = ρ'.ker.map (Lb.subgroupOf A).subtype := by
    ext a
    constructor
    · intro ha
      have haL : a ∈ Lb.subgroupOf A := ha.1
      have hak : ρ a = 1 := ha.2
      refine Subgroup.mem_map.mpr ⟨⟨a, haL⟩, ?_, rfl⟩
      show ρ' ⟨a, haL⟩ = 1
      show ρ ((Lb.subgroupOf A).subtype ⟨a, haL⟩) = 1
      exact hak
    · rintro ⟨k, hk, rfl⟩
      refine ⟨k.2, ?_⟩
      show (Lb.subgroupOf A).subtype k ∈ ρ.ker
      show ρ ((Lb.subgroupOf A).subtype k) = 1
      exact hk
  have hker : Nat.card ↥K = Nat.card ↥ρ'.ker := by
    rw [hKmap, Subgroup.card_map_of_injective (Lb.subgroupOf A).subtype_injective]
  have hcardK_mul : Nat.card ↥K * Nat.card ↥ρ'.range = 9 := by
    rw [hker, Subgroup.card_ker_mul_card_range ρ', hcardLbA]
  have hrange_dvd : Nat.card ↥ρ'.range ∣ 3 := by
    have h1 : Nat.card ↥ρ'.range ∣ Nat.card (Equiv.Perm ↥Xs) :=
      Subgroup.card_subgroup_dvd_card ρ'.range
    have h2 : Nat.card ↥ρ'.range ∣ Nat.card ↥(Lb.subgroupOf A) := Subgroup.card_range_dvd ρ'
    rw [Nat.card_perm, hcardXs] at h1
    rw [hcardLbA] at h2
    have hg := Nat.dvd_gcd h2 h1
    have hgcd : Nat.gcd 9 (Nat.factorial 3) = 3 := by decide
    rwa [hgcd] at hg
  have hKcases : Nat.card ↥K = 3 ∨ Nat.card ↥K = 9 := by
    have h1 : Nat.card ↥ρ'.range = 1 ∨ Nat.card ↥ρ'.range = 3 :=
      (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hrange_dvd
    rcases h1 with h | h
    · right
      rw [h, mul_one] at hcardK_mul
      exact hcardK_mul
    · left
      rw [h] at hcardK_mul
      omega
  rcases hKcases with hK3 | hK9
  · refine ⟨K.map A.subtype, Subgroup.map_subtype_le K, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective (K := K) (f := A.subtype) A.subtype_injective, hK3]
    · intro m hm x hx
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
      refine Subgroup.mem_map.mpr ⟨⟨m, hm⟩ * k * ⟨m, hm⟩⁻¹,
        hKnormal.conj_mem k hk ⟨m, hm⟩, ?_⟩
      rfl
  · have hKL : K = Lb.subgroupOf A := by
      apply Subgroup.eq_of_le_of_card_ge inf_le_left
      rw [hcardLbA, hK9]
    have hLbA_ker : Lb.subgroupOf A ≤ ρ.ker := by rw [← hKL]; exact inf_le_right
    have hfix : ∀ l ∈ Lb, ∀ Y : ↥Xs,
        (Y : Subgroup W).map (l : MulAut W).toMonoidHom = Y := by
      intro l hl Y
      have h1 : ρ ⟨l, hLA hl⟩ = 1 := hLbA_ker hl
      have h2 : ρ ⟨l, hLA hl⟩ Y = Y := by rw [h1]; rfl
      rw [show ρ ⟨l, hLA hl⟩ = MulAction.toPerm (⟨l, hLA hl⟩ : ↥A) from rfl,
        MulAction.toPerm_apply] at h2
      exact congrArg Subtype.val h2
    let Ki : ↥Xs → Subgroup (MulAut W) :=
      fun Y => Lb ⊓ s16c1610_pointStab (Y : Subgroup W)
    have hKi_equiv : ∀ (a : ↥A) (Z : ↥Xs),
        Ki (a • Z) = (Ki Z).map (MulAut.conj (a : MulAut W)).toMonoidHom := by
      intro a Z
      show Lb ⊓ s16c1610_pointStab ((a • Z : ↥Xs) : Subgroup W)
          = (Ki Z).map (MulAut.conj (a : MulAut W)).toMonoidHom
      have hLbconj : Lb.map (MulAut.conj (a : MulAut W)).toMonoidHom = Lb := by
        apply le_antisymm
        · intro x hx
          obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
          exact hLn (a : MulAut W) a.2 y hy
        · intro x hx
          have h1 : (a : MulAut W)⁻¹ * x * (a : MulAut W) ∈ Lb :=
            hLn _ (A.inv_mem a.2) x hx
          refine Subgroup.mem_map.mpr ⟨(a : MulAut W)⁻¹ * x * (a : MulAut W), h1, ?_⟩
          show (MulAut.conj (a : MulAut W)) ((a : MulAut W)⁻¹ * x * (a : MulAut W)) = x
          rw [MulAut.conj_apply]; group
      have hPS : s16c1610_pointStab ((Z : Subgroup W).map (a : MulAut W).toMonoidHom)
          = (s16c1610_pointStab (Z : Subgroup W)).map
              (MulAut.conj (a : MulAut W)).toMonoidHom := by
        ext x
        constructor
        · intro hx
          refine Subgroup.mem_map.mpr ⟨(a : MulAut W)⁻¹ * x * (a : MulAut W), ?_, ?_⟩
          · intro y hy
            have h1 : x ((a : MulAut W) y) = (a : MulAut W) y :=
              hx ((a : MulAut W) y) (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
            calc ((a : MulAut W)⁻¹ * x * (a : MulAut W)) y
                = (a : MulAut W)⁻¹ (x ((a : MulAut W) y)) := by
                  rw [MulAut.mul_apply, MulAut.mul_apply]
              _ = (a : MulAut W)⁻¹ ((a : MulAut W) y) := by rw [h1]
              _ = y := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
          · show (MulAut.conj (a : MulAut W)) ((a : MulAut W)⁻¹ * x * (a : MulAut W)) = x
            rw [MulAut.conj_apply]; group
        · rintro ⟨y, hy, rfl⟩
          intro z hz
          obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
          show (MulAut.conj (a : MulAut W)) y ((a : MulAut W) w) = (a : MulAut W) w
          rw [MulAut.conj_apply]
          calc ((a : MulAut W) * y * (a : MulAut W)⁻¹) ((a : MulAut W) w)
              = (a : MulAut W) (y ((a : MulAut W)⁻¹ ((a : MulAut W) w))) := by
                rw [MulAut.mul_apply, MulAut.mul_apply]
            _ = (a : MulAut W) (y w) := by
                rw [show (a : MulAut W)⁻¹ ((a : MulAut W) w) = w by
                  rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]]
            _ = (a : MulAut W) w := by rw [hy w hw]
      rw [show ((a • Z : ↥Xs) : Subgroup W)
          = (Z : Subgroup W).map (a : MulAut W).toMonoidHom from rfl, hPS,
        ← hLbconj, ← s16c1610_map_inf (MulAut.conj (a : MulAut W)).toMonoidHom
          (MulAut.conj (a : MulAut W)).injective]
    have hKi_card : ∀ Y : ↥Xs, Nat.card ↥(Ki Y) = 3 := by
      intro Y
      let φ : ↥Lb →* MulAut ↥(Y : Subgroup W) :=
        s16c1610_restrictAutHom Lb (Y : Subgroup W) (fun l hl => hfix l hl Y)
      have hKiφ : Ki Y = φ.ker.map Lb.subtype :=
        (s16c1610_ker_restrictAutHom Lb (Y : Subgroup W) (fun l hl => hfix l hl Y)).symm
      have hcardker : Nat.card ↥φ.ker = Nat.card ↥(Ki Y) := by
        rw [hKiφ, Subgroup.card_map_of_injective Lb.subtype_injective]
      have hker_mul : Nat.card ↥φ.ker * Nat.card ↥φ.range = 9 := by
        rw [Subgroup.card_ker_mul_card_range φ, hcardLb]
      have hcardAut : Nat.card (MulAut ↥(Y : Subgroup W)) = 6 := by
        have hrkY : rk ↥(Y : Subgroup W) = 2 := by
          obtain ⟨g, hg, hgY⟩ := Y.2
          rw [hgY, rk, Subgroup.card_map_of_injective (f := g.toMonoidHom) g.injective]
          exact hZrk
        have hcomm : ∀ a b : ↥(Y : Subgroup W), a * b = b * a := fun a b => mul_comm a b
        have hpow : ∀ a : ↥(Y : Subgroup W), a ^ 2 = 1 := fun a => by
          apply Subtype.ext
          simpa using h2 (a : W)
        have hcardY : Nat.card ↥(Y : Subgroup W) = 2 ^ 2 := by
          rw [card_eq_two_pow h2 (Y : Subgroup W), hrkY]
        have := CFSG.Sporadic.RuSchreier.ru_card_mulAut_elementary (p := 2) hcomm hpow
          (n := 2) hcardY
        simpa using this
      have hrange_dvd3 : Nat.card ↥φ.range ∣ 3 := by
        have h1 : Nat.card ↥φ.range ∣ Nat.card (MulAut ↥(Y : Subgroup W)) :=
          Subgroup.card_subgroup_dvd_card φ.range
        have h2 : Nat.card ↥φ.range ∣ Nat.card ↥Lb := Subgroup.card_range_dvd φ
        rw [hcardAut] at h1
        rw [hcardLb] at h2
        have hg := Nat.dvd_gcd h2 h1
        have hgcd : Nat.gcd 9 6 = 3 := by decide
        rwa [hgcd] at hg
      have hrange := (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hrange_dvd3
      rw [hcardker] at hker_mul
      rcases hrange with hh | hh
      · exfalso
        rw [hh, mul_one] at hker_mul
        have hKiLb : Ki Y = Lb := by
          have h9 : Nat.card ↥(Ki Y) = 9 := by simpa using hker_mul
          apply Subgroup.eq_of_le_of_card_ge inf_le_left
          rw [hcardLb, h9]
        have hle : Lb ≤ s16c1610_pointStab (Y : Subgroup W) := hKiLb.symm ▸ inf_le_right
        have hfixAny : ∀ Z : ↥Xs, Lb ≤ s16c1610_pointStab (Z : Subgroup W) := by
          intro Z
          obtain ⟨g, hg, hgσ⟩ := hZperm (Equiv.swap Y Z)
          have haZ : (⟨g, hg⟩ : ↥A) • Y = Z := by
            apply Subtype.ext
            show (Y : Subgroup W).map g.toMonoidHom = (Z : Subgroup W)
            rw [hgσ Y, Equiv.swap_apply_left]
          have heq : Ki Z = (Ki Y).map (MulAut.conj g).toMonoidHom := by
            have h0 := hKi_equiv ⟨g, hg⟩ Y
            rw [haZ] at h0
            exact h0
          have hLbconj : Lb.map (MulAut.conj g).toMonoidHom = Lb := by
            apply le_antisymm
            · intro x hx
              obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
              exact hLn g hg y hy
            · intro x hx
              have h1 : g⁻¹ * x * g ∈ Lb := hLn _ (A.inv_mem hg) x hx
              refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, h1, ?_⟩
              show (MulAut.conj g) (g⁻¹ * x * g) = x
              rw [MulAut.conj_apply]; group
          rw [hKiLb, hLbconj] at heq
          rw [← heq]
          exact inf_le_right
        have hK0bot : Lb = ⊥ := by
          rw [Subgroup.eq_bot_iff_forall]
          intro l hl
          apply MulEquiv.ext
          intro w
          have hleFix : sSup Xs ≤ (l : MulAut W).toMonoidHom.eqLocus (MonoidHom.id W) := by
            rw [sSup_le_iff]
            intro Z hZ y hy
            change l y = y
            exact hfixAny ⟨Z, hZ⟩ hl y hy
          exact (hZsup ▸ hleFix) (Subgroup.mem_top w)
        rw [hK0bot, Subgroup.card_bot] at hcardLb
        norm_num at hcardLb
      · rw [hh] at hker_mul
        omega
    have hKi_inj : Function.Injective Ki := by
      intro Y Y' hEq
      by_contra hne
      have hcardXsF : Fintype.card ↥Xs = 3 := by rw [← Nat.card_eq_fintype_card]; exact hcardXs
      haveI : DecidableEq ↥Xs := Classical.decEq _
      have hlt : ({Y, Y'} : Finset ↥Xs).card < (Finset.univ : Finset ↥Xs).card := by
        rw [Finset.card_pair hne, Finset.card_univ, hcardXsF]; norm_num
      obtain ⟨Y'', -, hY''⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      have hY''Y : Y'' ≠ Y := fun h => hY'' (by rw [h]; simp)
      have hY''Y' : Y'' ≠ Y' := fun h => hY'' (by rw [h]; simp)
      let σ : Equiv.Perm ↥Xs := Equiv.swap Y Y' * Equiv.swap Y' Y''
      have hσY : σ Y = Y' := by
        show (Equiv.swap Y Y' * Equiv.swap Y' Y'') Y = Y'
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hne hY''Y.symm,
          Equiv.swap_apply_left]
      have hσY' : σ Y' = Y'' := by
        show (Equiv.swap Y Y' * Equiv.swap Y' Y'') Y' = Y''
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hY''Y hY''Y']
      obtain ⟨g, hg, hgσ⟩ := hZperm σ
      have haσ : ∀ Z : ↥Xs, (⟨g, hg⟩ : ↥A) • Z = σ Z := by
        intro Z
        apply Subtype.ext
        show (Z : Subgroup W).map g.toMonoidHom = (σ Z : Subgroup W)
        exact hgσ Z
      have h1 : Ki Y' = (Ki Y).map (MulAut.conj g).toMonoidHom := by
        rw [← hσY, ← haσ Y, hKi_equiv ⟨g, hg⟩ Y]
      have h2 : Ki Y'' = (Ki Y').map (MulAut.conj g).toMonoidHom := by
        rw [← hσY', ← haσ Y', hKi_equiv ⟨g, hg⟩ Y']
      have h3 : Ki Y'' = Ki Y := calc
        Ki Y'' = (Ki Y').map (MulAut.conj g).toMonoidHom := h2
        _ = (Ki Y).map (MulAut.conj g).toMonoidHom := by rw [hEq]
        _ = Ki Y' := h1.symm
        _ = Ki Y := hEq.symm
      have hK0le : ∀ Z : ↥Xs, Ki Y ≤ s16c1610_pointStab (Z : Subgroup W) := by
        intro Z
        have hZmem : Z ∈ ({Y, Y', Y''} : Finset ↥Xs) := by
          have hcard3 : ({Y, Y', Y''} : Finset ↥Xs).card = 3 := by
            rw [Finset.card_insert_of_notMem (by simp [hne, hY''Y.symm]),
              Finset.card_insert_of_notMem (by simp [hY''Y'.symm]), Finset.card_singleton]
          have heq : ({Y, Y', Y''} : Finset ↥Xs) = Finset.univ := by
            apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
            rw [hcard3, Finset.card_univ, hcardXsF]
          rw [heq]; exact Finset.mem_univ Z
        simp only [Finset.mem_insert, Finset.mem_singleton] at hZmem
        rcases hZmem with rfl | rfl | rfl
        · exact inf_le_right
        · exact hEq.symm ▸ inf_le_right
        · exact h3 ▸ inf_le_right
      have hK0bot : Ki Y = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro l hl
        apply MulEquiv.ext
        intro w
        have hleFix : sSup Xs ≤ (l : MulAut W).toMonoidHom.eqLocus (MonoidHom.id W) := by
          rw [sSup_le_iff]
          intro Z hZ y hy
          change l y = y
          exact hK0le ⟨Z, hZ⟩ hl y hy
        exact (hZsup ▸ hleFix) (Subgroup.mem_top w)
      have hc := hKi_card Y
      rw [hK0bot, Subgroup.card_bot] at hc
      norm_num at hc
    let S : Set (Subgroup (MulAut W)) := Set.range Ki
    have hScard : S.ncard = 3 := by
      rw [show S = Ki '' Set.univ from by ext X; simp [S]]
      rw [Set.ncard_image_of_injective _ hKi_inj, Set.ncard_univ, hcardXs]
    have hSsub : S ⊆ {X : Subgroup (MulAut W) | X ≤ Lb ∧ Nat.card X = 3} := by
      rintro X ⟨Y, rfl⟩
      exact ⟨inf_le_left, hKi_card Y⟩
    have hTcard : (Set.ncard {X : Subgroup (MulAut W) | X ≤ Lb ∧ Nat.card X = 3}) = 4 :=
      s16c1610_ncard_orderThree_subgroups Lb hcardLb hexpLb
    have hSinv : ∀ (a : ↥A) (X : Subgroup (MulAut W)), X ∈ S →
        X.map (MulAut.conj (a : MulAut W)).toMonoidHom ∈ S := by
      rintro a X ⟨Y, rfl⟩
      exact ⟨a • Y, hKi_equiv a Y⟩
    have hcompcard : (Set.ncard ({X : Subgroup (MulAut W) | X ≤ Lb ∧ Nat.card X = 3} \ S)) = 1 := by
      rw [Set.ncard_sdiff' hSsub, hTcard, hScard]
    obtain ⟨X, hX⟩ := Set.ncard_eq_one.mp hcompcard
    have hXT : X ∈ {X : Subgroup (MulAut W) | X ≤ Lb ∧ Nat.card X = 3} := by
      have : X ∈ ({X : Subgroup (MulAut W) | X ≤ Lb ∧ Nat.card X = 3} \ S) := by
        rw [hX]; exact Set.mem_singleton X
      exact this.1
    have hXnS : X ∉ S := by
      have : X ∈ ({X : Subgroup (MulAut W) | X ≤ Lb ∧ Nat.card X = 3} \ S) := by
        rw [hX]; exact Set.mem_singleton X
      exact this.2
    refine ⟨X, hXT.1.trans hLA, hXT.2, ?_⟩
    intro m hm x hx
    have hconjT : X.map (MulAut.conj m).toMonoidHom ∈
        {X : Subgroup (MulAut W) | X ≤ Lb ∧ Nat.card X = 3} := by
      refine ⟨?_, ?_⟩
      · rintro y ⟨z, hz, rfl⟩
        exact hLn m hm z (hXT.1 hz)
      · rw [Subgroup.card_map_of_injective (MulAut.conj m).injective]; exact hXT.2
    have hconjS : X.map (MulAut.conj m).toMonoidHom ∉ S := by
      intro hmem
      have hcomp : (MulAut.conj (m⁻¹ : MulAut W)).toMonoidHom.comp
          (MulAut.conj m).toMonoidHom = MonoidHom.id (MulAut W) := by
        ext t
        simp [MulAut.conj_apply]
      have hmem' := hSinv ⟨m, hm⟩⁻¹ (X.map (MulAut.conj m).toMonoidHom) hmem
      rw [Subgroup.map_map] at hmem'
      rw [show (↑(⟨m, hm⟩⁻¹ : ↥A) : MulAut W) = m⁻¹ from rfl] at hmem'
      rw [hcomp, Subgroup.map_id] at hmem'
      exact hXnS hmem'
    have hXmap : X.map (MulAut.conj m).toMonoidHom = X := by
      have : X.map (MulAut.conj m).toMonoidHom ∈ ({X} : Set (Subgroup (MulAut W))) := by
        rw [← hX]; exact ⟨hconjT, hconjS⟩
      exact Set.mem_singleton_iff.mp this
    have : m * x * m⁻¹ ∈ X.map (MulAut.conj m).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj_apply]⟩
    rwa [hXmap] at this



section Certified


theorem s16c1610_out10_of_case4_two_three (D : Data G) (hin : In10 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV)
    (h4 : Case168_4At D V₀ V hV L 3 2) : Out10 D V₀ V hV := by
  have h125 : Hyp125 D V₀ V := hc.setting.hyp16.hyp125
  obtain ⟨hrk6, h5, h7⟩ := s16c1610_case4_two_card D hV h4
  have hd : dParam 3 = 2 := s16c1610_dParam_three
  have hLM : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := by
    unfold lBar Mbar
    exact barSub_mono V₀ V hV hc.setting.hyp151.le
  have hS : SymSumOfConj (Mbar D.M V₀ V hV) (⊤ : Subgroup (Vtil V₀ V hV)) 2 2 := by
    have := h4.2.1
    rwa [hd] at this
  obtain ⟨X, hXM, hXcard, hXnorm⟩ := s16c1610_exists_normal_three_of_symSum_two
    (Vtil_pow_two hV) hLM (s16c1610_lBar_normal_of_case4_two D hc h4) h4.1 hS
  exact s16c1610_out10_of_normal_prime D hin.hx hin.h61 hin.h127 hin.h1114 hin.h1214 hin.h162
    hin.h139 h125 (Or.inl rfl) (s16c1610_k_lt_dParam_three D hin.hSg hin.h1219 h4.2.2) hXM hXcard
    hXnorm (by rw [hd, hrk6]; norm_num) (s16c1610_not_concl614_of_five_seven hXM hrk6 h5 h7)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
