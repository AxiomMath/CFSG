module

public import CFSG.LocalAnalysis.WeakClosure81.SixTen
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

theorem s16c167_exists_hyperplane_of_fixed_card_two {W : Type*} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {X : Subgroup (MulAut W)} (hX : IsElemAbelian2 X)
    {I : Subgroup W} (hI : StableUnder X I) (hcard : Nat.card ↥(I ⊓ fixV X) = 2)
    (hbig : 2 < Nat.card ↥I) :
    ∃ C : Subgroup (MulAut W), C ≤ X ∧ E3.mQuot X C = 1 ∧ fixV C ≠ fixV X := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z : Subgroup W := I ⊓ fixV X with hZ
  have hZI : Z ≤ I := by rw [hZ]; exact inf_le_left
  have hZX : Z ≤ fixV X := by rw [hZ]; exact inf_le_right
  have hZcard : Nat.card ↥Z = 2 := hcard
  have hX2 : IsPGroup 2 ↥X :=
    isPGroup_two_of_sq_eq_one (fun x : ↥X => Subtype.ext (by simpa using hX.2 x x.2))
  have hex : ∃ w : W, w ∈ I ∧ w ∉ Z := by
    by_contra h
    have hle : I ≤ Z := by
      intro w hw
      by_contra hwZ
      exact h ⟨w, hw, hwZ⟩
    have h2 : Nat.card ↥I = 2 := by rw [le_antisymm hle hZI]; exact hZcard
    omega
  obtain ⟨w₀, hw₀I, hw₀Z⟩ := hex
  let N : Subgroup ↥I := Z.subgroupOf I
  let Q : Type _ := ↥I ⧸ N
  let fx (x : ↥X) : ↥I →* ↥I :=
    { toFun := fun z => ⟨(x : MulAut W) z, hI x x.2 z z.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
  have hfxZ : ∀ (x : ↥X) (z : ↥I), (z : W) ∈ Z → (x : MulAut W) (z : W) ∈ Z := by
    intro x z hz
    rw [hZ] at hz ⊢
    rw [Subgroup.mem_inf] at hz ⊢
    refine ⟨hI x x.2 z hz.1, ?_⟩
    rw [mem_fixV] at hz ⊢
    intro y hy
    calc y ((x : MulAut W) z) = (y * x) z := (MulAut.mul_apply W y (x : MulAut W) z).symm
      _ = (x * y) z := by rw [hX.1 y hy x x.2]
      _ = (x : MulAut W) (y z) := MulAut.mul_apply W (x : MulAut W) y z
      _ = (x : MulAut W) z := by rw [hz.2 y hy]
  have hfxN (x : ↥X) : N ≤ N.comap (fx x) := fun z hz => hfxZ x z hz
  letI : MulAction ↥X Q :=
    { smul := fun x => QuotientGroup.map N N (fx x) (hfxN x)
      one_smul := by
        intro q
        induction q using QuotientGroup.induction_on with
        | H z =>
          show QuotientGroup.map N N (fx 1) (hfxN 1) (QuotientGroup.mk z) = QuotientGroup.mk z
          rw [QuotientGroup.map_mk]
          simp [fx]
      mul_smul := by
        intro x y q
        induction q using QuotientGroup.induction_on with
        | H z =>
          show QuotientGroup.map N N (fx (x * y)) (hfxN (x * y)) (QuotientGroup.mk z) =
            QuotientGroup.map N N (fx x) (hfxN x)
              (QuotientGroup.map N N (fx y) (hfxN y) (QuotientGroup.mk z))
          rw [QuotientGroup.map_mk, QuotientGroup.map_mk, QuotientGroup.map_mk]
          congr 1 }
  have hI2 : IsPGroup 2 ↥I := (isPGroup_two_of_sq_eq_one hW).to_subgroup I
  have hQ2 : IsPGroup 2 Q := hI2.to_quotient N
  have hdvd : 2 ∣ Nat.card Q := by
    have hnt : Nontrivial Q := by
      refine ⟨QuotientGroup.mk (⟨w₀, hw₀I⟩ : ↥I), 1, fun h => hw₀Z ?_⟩
      have hmem : (⟨w₀, hw₀I⟩ : ↥I) ∈ N := (QuotientGroup.eq_one_iff (N := N) _).1 h
      rw [Subgroup.mem_subgroupOf] at hmem
      exact hmem
    obtain ⟨n, hn0, hn⟩ := hQ2.nontrivial_iff_card.1 hnt
    rw [hn]
    exact dvd_pow_self 2 (ne_of_gt hn0)
  have hfix1 : (1 : Q) ∈ MulAction.fixedPoints ↥X Q := by
    intro x
    show QuotientGroup.map N N (fx x) (hfxN x) (1 : Q) = 1
    exact map_one _
  obtain ⟨q, hqfix, hqne⟩ :=
    hX2.exists_fixed_point_of_prime_dvd_card_of_fixed_point Q hdvd hfix1
  obtain ⟨w, hwq⟩ := QuotientGroup.mk_surjective q
  have hwZ : (w : W) ∉ Z := by
    intro hwZ'
    have hmem : w ∈ N := hwZ'
    have h1 : (QuotientGroup.mk w : Q) = 1 := (QuotientGroup.eq_one_iff (N := N) w).2 hmem
    exact hqne (by rw [← hwq, h1])
  have hfixw : ∀ x ∈ X, (x : MulAut W) w * (w : W)⁻¹ ∈ Z := by
    intro x hx
    have hxq := hqfix ⟨x, hx⟩
    rw [← hwq] at hxq
    change QuotientGroup.map N N (fx ⟨x, hx⟩) (hfxN ⟨x, hx⟩) (QuotientGroup.mk w) =
      QuotientGroup.mk w at hxq
    rw [QuotientGroup.map_mk] at hxq
    have hdiv : ((fx ⟨x, hx⟩) w) / w ∈ N := (QuotientGroup.eq_iff_div_mem).1 hxq
    rw [Subgroup.mem_subgroupOf] at hdiv
    simpa [fx, div_eq_mul_inv] using hdiv
  let ψ : ↥X →* ↥Z :=
    { toFun := fun x => ⟨(x : MulAut W) w * (w : W)⁻¹, hfixw x x.2⟩
      map_one' := by
        refine Subtype.ext ?_
        simp
      map_mul' := by
        intro x y
        refine Subtype.ext ?_
        change ((x * y : ↥X) : MulAut W) (w : W) * (w : W)⁻¹
          = ((x : MulAut W) (w : W) * (w : W)⁻¹) * ((y : MulAut W) (w : W) * (w : W)⁻¹)
        rw [Subgroup.coe_mul, MulAut.mul_apply W]
        have h1 : (x : MulAut W) ((y : MulAut W) w * (w : W)⁻¹)
            = (y : MulAut W) w * (w : W)⁻¹ :=
          mem_fixV.1 (hZX (hfixw y y.2)) x x.2
        have hy : (y : MulAut W) w = ((y : MulAut W) w * (w : W)⁻¹) * w := by
          rw [mul_assoc, inv_mul_cancel, mul_one]
        conv_lhs => rw [hy, map_mul, h1]
        calc ((y : MulAut W) w * (w : W)⁻¹) * (x : MulAut W) w * (w : W)⁻¹
            = ((y : MulAut W) w * (w : W)⁻¹) * ((x : MulAut W) w * (w : W)⁻¹) := by
              rw [mul_assoc]
          _ = ((x : MulAut W) w * (w : W)⁻¹) * ((y : MulAut W) w * (w : W)⁻¹) := by
              rw [mul_comm] }
  have hψne : ψ ≠ 1 := by
    intro h
    apply hwZ
    rw [hZ, Subgroup.mem_inf]
    refine ⟨w.2, ?_⟩
    rw [mem_fixV]
    intro x hx
    have hx1 : ψ ⟨x, hx⟩ = 1 := by rw [h]; simp
    have h1 : (x : MulAut W) w * (w : W)⁻¹ = 1 := congrArg Subtype.val hx1
    exact mul_inv_eq_one.1 h1
  have hrange : ψ.range = ⊤ := by
    have h1 : ψ.range ≠ ⊥ := fun hb => hψne (MonoidHom.range_eq_bot_iff.1 hb)
    have h2 : 1 < Nat.card ↥ψ.range := (Subgroup.one_lt_card_iff_ne_bot ψ.range).2 h1
    have h3 : Nat.card ↥ψ.range ≤ 2 := by
      simpa [hZcard] using Subgroup.card_le_card_group (H := ψ.range)
    have hcardψ : Nat.card ↥ψ.range = Nat.card ↥Z := by omega
    exact Subgroup.eq_top_of_card_eq (H := ψ.range) hcardψ
  let C : Subgroup (MulAut W) := ψ.ker.map X.subtype
  refine ⟨C, ?_, ?_, ?_⟩
  · intro c hc
    have hc' : c ∈ ψ.ker.map X.subtype := hc
    obtain ⟨x, -, rfl⟩ := (Subgroup.mem_map).1 hc'
    exact x.2
  · show padicValNat 2 (C.relIndex X) = 1
    have hsub : C.subgroupOf X = ψ.ker := by
      change (ψ.ker.map X.subtype).comap X.subtype = ψ.ker
      exact Subgroup.comap_map_eq_self_of_injective X.subtype_injective ψ.ker
    have hrel : C.relIndex X = 2 := by
      change (C.subgroupOf X).index = 2
      rw [hsub, Subgroup.index_ker, hrange, Subgroup.card_top, hZcard]
    rw [hrel]
    exact padicValNat_self
  · intro h
    have hwC : (w : W) ∈ fixV C := by
      rw [mem_fixV]
      intro c hc
      have hc' : c ∈ ψ.ker.map X.subtype := hc
      obtain ⟨x, hxker, rfl⟩ := (Subgroup.mem_map).1 hc'
      have hx1 : ψ x = 1 := MonoidHom.mem_ker.2 hxker
      have h1 : (x : MulAut W) w * (w : W)⁻¹ = 1 := congrArg Subtype.val hx1
      exact mul_inv_eq_one.1 h1
    apply hwZ
    rw [hZ, Subgroup.mem_inf]
    exact ⟨w.2, h ▸ hwC⟩

theorem s16c167_aSet_two_not_fixed_pair {W : Type*} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {X Y : Subgroup (MulAut W)} (hX : X ∈ E3.aSet 2 Y)
    {I : Subgroup W} (hI : StableUnder X I) (hcard : Nat.card ↥(I ⊓ fixV X) = 2)
    (hbig : 2 < Nat.card ↥I) : False := by
  obtain ⟨C, hCX, hm, hne⟩ :=
    s16c167_exists_hyperplane_of_fixed_card_two hW hX.2.2.1 hI hcard hbig
  exact hne (hX.2.2.2 C hCX (by omega))

variable {G : Type} [Group G] [Finite G]

theorem s16c167_two_lt_card_of_mem_irrSet {W : Type*} [CommGroup W] [Finite W]
    {X : Subgroup (MulAut W)} {I : Subgroup W} (hI : I ∈ irrSet X) : 2 < Nat.card ↥I := by
  have hIrr : IsIrrOn X I (I ⊓ fixV X) := hI.2
  have hlt : I ⊓ fixV X < I := hIrr.1
  have hne : I ≠ ⊥ := by
    intro hbot
    have heq : I ⊓ fixV X = I := by rw [hbot]; simp
    exact (ne_of_lt hlt) heq
  have h1 : 1 < Nat.card ↥I := (Subgroup.one_lt_card_iff_ne_bot I).2 hne
  by_contra hcon
  have hI2 : Nat.card ↥I = 2 := by omega
  have hle : I ≤ fixV X := by
    intro u hu
    rw [mem_fixV]
    intro x hx
    obtain ⟨a, ha1, hauniq⟩ := (Nat.card_eq_two_iff' (1 : ↥I)).1 hI2
    by_cases hu1 : u = 1
    · rw [hu1, map_one]
    · have hua : (⟨u, hu⟩ : ↥I) = a := hauniq ⟨u, hu⟩ (by simpa using hu1)
      have hxaI : (x : MulAut W) a ∈ I := hIrr.2.1 x hx a a.2
      have hxane : (⟨(x : MulAut W) a, hxaI⟩ : ↥I) ≠ 1 := by
        intro hh
        apply ha1
        have hval : (x : MulAut W) a = 1 := congrArg Subtype.val hh
        apply Subtype.ext
        have hx1 : (x : MulAut W) (a : W) = (x : MulAut W) (1 : W) := by rw [hval, map_one]
        exact (x : MulAut W).injective hx1
      have hxa : (x : MulAut W) a = a :=
        congrArg Subtype.val (hauniq ⟨(x : MulAut W) a, hxaI⟩ hxane)
      rw [show u = (a : W) from congrArg Subtype.val hua]
      exact hxa
  rw [inf_eq_left.2 hle] at hlt
  exact (lt_irrefl I) hlt

private theorem mkTil_bot_injective {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    Function.Injective (mkTil ⊥ V hV) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_bot]
  constructor
  · intro h
    have hx : x ∈ modNull ⊥ V hV := (QuotientGroup.eq_one_iff (N := modNull ⊥ V hV) x).1 h
    rw [mem_modNull] at hx
    exact IntMod.val_injective (by simpa using hx)
  · rintro rfl
    exact map_one _

theorem s16c167_card_imgTil_bot {V U : Subgroup G} (hV : IsElemAbelian 2 V) (hU : U ≤ V) :
    Nat.card ↥(imgTil ⊥ V hV U) = Nat.card ↥U := by
  have hinj := mkTil_bot_injective hV
  unfold imgTil
  rw [Subgroup.card_map_of_injective hinj]
  change Nat.card ↥(U.subgroupOf V) = Nat.card ↥U
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU).toEquiv

theorem s16c167_imgTil_inf_bot {V U U' : Subgroup G} (hV : IsElemAbelian 2 V) :
    imgTil ⊥ V hV (U ⊓ U') = imgTil ⊥ V hV U ⊓ imgTil ⊥ V hV U' := by
  have hinj := mkTil_bot_injective hV
  have hsub : intSub V hV (U ⊓ U') = intSub V hV U ⊓ intSub V hV U' := by
    simp only [intSub, Subgroup.subgroupOf]
    exact Subgroup.comap_inf U U' V.subtype
  unfold imgTil
  rw [hsub, Subgroup.map_inf _ _ _ hinj]

theorem sixteen_seven2_final {M V₀ V L B I : Subgroup G} (hV : IsElemAbelian 2 V)
    (h0 : V₀ = ⊥) (hIV : I ≤ V) (hBst : B ≤ stabTil V₀ V)
    (hirr : imgTil V₀ V hV I ∈ irrBar L V₀ V hV)
    (hfix : ∀ b ∈ B, conjSubgroup I b = I)
    (hcard : Nat.card ↥(I ⊓ centralizer (B : Set G)) = 2)
    (hB2 : barSub V₀ V hV B ∈ calABar 2 M V₀ V hV) : False := by
  subst h0
  have hBst' : B ≤ stabTil ⊥ V := hBst
  have hstable : StableUnder (barSub ⊥ V hV B) (imgTil ⊥ V hV I) := by
    intro φ hφ u hu
    obtain ⟨g, hgB, rfl⟩ := (mem_barSub ⊥ V hV B φ).1 hφ
    obtain ⟨x, hxI, rfl⟩ := (mem_imgTil ⊥ V hV I u).1 hu
    rw [actTil_mk]
    refine (mem_imgTil ⊥ V hV I _).2 ⟨actStab ⊥ V hV g x, ?_, rfl⟩
    rw [actStab_apply_val]
    have hxconj : x.val ∈ conjSubgroup I (g : G) := by
      rw [hfix (g : G) hgB]
      exact hxI
    exact (mem_conjSubgroup_iff).1 hxconj
  have hfixV : fixV (barSub ⊥ V hV B) = imgTil ⊥ V hV (V ⊓ centralizer (B : Set G)) := by
    rw [← imgTil_preTil ⊥ V hV (fixV (barSub ⊥ V hV B)), ← preCTilde_bot_eq hV hBst']
    rfl
  have hcard2 : Nat.card ↥(imgTil ⊥ V hV I ⊓ fixV (barSub ⊥ V hV B)) = 2 := by
    rw [hfixV, ← s16c167_imgTil_inf_bot (U := I) (U' := V ⊓ centralizer (B : Set G)) hV]
    rw [s16c167_card_imgTil_bot hV (le_trans inf_le_right inf_le_left)]
    rw [← inf_assoc, inf_eq_left.2 hIV]
    exact hcard
  have hbig : 2 < Nat.card ↥(imgTil ⊥ V hV I) := s16c167_two_lt_card_of_mem_irrSet hirr
  have hW : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := by
    intro w
    obtain ⟨x, rfl⟩ := mkTil_surjective ⊥ V hV w
    rw [← map_pow, IntMod.sq_eq_one x, map_one]
  exact s16c167_aSet_two_not_fixed_pair hW hB2 hstable hcard2 hbig

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
