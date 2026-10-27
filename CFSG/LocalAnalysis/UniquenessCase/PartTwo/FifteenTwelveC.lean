module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwelveB
public import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s15_Twelve_mQuot_preTil {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (S : Subgroup (Vtil V₀ V hV)) :
    E3.mQuot V (preTil V₀ V hV S) = rkIdx S := by
  change rkIdx (intSub V hV (preTil V₀ V hV S)) = rkIdx S
  have h : intSub V hV (preTil V₀ V hV S) = S.comap (mkTil V₀ V hV) := by
    ext x
    rw [mem_intSub, mem_preTil]
    constructor
    · rintro ⟨y, hy, hyS⟩
      have : y = x := IntMod.val_injective hy
      rwa [this] at hyS
    · intro hx
      exact ⟨x, rfl, hx⟩
  rw [h]
  unfold rkIdx
  rw [Subgroup.index_comap_of_surjective S (mkTil_surjective V₀ V hV)]

private theorem s15_Twelve_mQuot_imgTil {V₀ V F K : Subgroup G} (hV : IsElemAbelian 2 V)
    (hV₀K : V₀ ≤ K) (hKF : K ≤ F) (hFV : F ≤ V) :
    E3.mQuot (imgTil V₀ V hV F) (imgTil V₀ V hV K) = E3.mQuot F K := by
  have hK : K ≤ V := hKF.trans hFV
  have hV₀F : V₀ ≤ F := hV₀K.trans hKF
  unfold E3.mQuot
  have hK' : imgTil V₀ V hV K = (intSub V hV K).map (mkTil V₀ V hV) := rfl
  have hF' : imgTil V₀ V hV F = (intSub V hV F).map (mkTil V₀ V hV) := rfl
  rw [hK', hF', Subgroup.relIndex_map_map]
  have hker : (mkTil V₀ V hV).ker = intSub V hV V₀ := by
    rw [show (mkTil V₀ V hV).ker = modNull V₀ V hV from QuotientGroup.ker_mk' _]
    rfl
  rw [hker]
  have h1 : intSub V hV K ⊔ intSub V hV V₀ = intSub V hV K := by
    refine le_antisymm (sup_le le_rfl ?_) le_sup_left
    intro x hx
    exact (mem_intSub V hV K x).2 (hV₀K ((mem_intSub V hV V₀ x).1 hx))
  have h2 : intSub V hV F ⊔ intSub V hV V₀ = intSub V hV F := by
    refine le_antisymm (sup_le le_rfl ?_) le_sup_left
    intro x hx
    exact (mem_intSub V hV F x).2 (hV₀F ((mem_intSub V hV V₀ x).1 hx))
  rw [h1, h2]
  exact congrArg (padicValNat 2) (by
    dsimp only [intSub]
    exact Subgroup.relIndex_subgroupOf (H := K) (K := F) (L := V) hFV)

private theorem s15_Twelve_mQuot_inf_add_rk {W : Type*} [Group W] [Finite W]
    {Y : Subgroup W} (hY : IsPGroup 2 Y) (C : Subgroup W) :
    E3.mQuot Y (Y ⊓ C) + rk ↥(Y ⊓ C) = rk ↥Y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := E3.card_eq_two_pow_mul (V := Y) (U := Y ⊓ C) hY inf_le_left
  have h' := congrArg (padicValNat 2) h
  rw [padicValNat.mul (p := 2) (a := 2 ^ E3.mQuot Y (Y ⊓ C))
      (b := Nat.card ↥(Y ⊓ C)) (by positivity) (Nat.card_pos.ne'),
    padicValNat.prime_pow] at h'
  unfold rk
  exact h'.symm

private theorem s15_Twelve_imgTil_inf_preTil {V₀ V U : Subgroup G} (hV : IsElemAbelian 2 V)
    (S : Subgroup (Vtil V₀ V hV)) :
    imgTil V₀ V hV (U ⊓ preTil V₀ V hV S) = imgTil V₀ V hV U ⊓ S := by
  ext q
  rw [Subgroup.mem_inf, mem_imgTil, mem_imgTil]
  constructor
  · rintro ⟨x, ⟨hxU, hxS⟩, rfl⟩
    obtain ⟨y, hy, hyS⟩ := (mem_preTil V₀ V hV S).1 hxS
    rw [IntMod.val_injective hy] at hyS
    exact ⟨⟨x, hxU, rfl⟩, hyS⟩
  · rintro ⟨⟨x, hxU, hxq⟩, hqS⟩
    refine ⟨x, ⟨hxU, (mem_preTil V₀ V hV S).2 ⟨x, rfl, ?_⟩⟩, hxq⟩
    rw [hxq]
    exact hqS

private theorem s15_Twelve_fixV_iSupIndep_le {W : Type*} [CommGroup W] {ι : Type*}
    [Fintype ι] (U : ι → Subgroup W) (Y : Subgroup (MulAut W)) (hind : iSupIndep U)
    (hstab : ∀ i, Y ≤ stabSub (U i)) :
    fixV Y ⊓ (⨆ i, U i) ≤ ⨆ i, (U i ⊓ fixV Y) := by
  intro v hv
  rw [Subgroup.mem_inf] at hv
  obtain ⟨hvfix, hvsup⟩ := hv
  classical
  let hcomm : Pairwise fun i j : ι => ∀ x y : W, x ∈ U i → y ∈ U j → Commute x y :=
    fun _ _ _ x y _ _ => mul_comm x y
  let φ : (∀ i, U i) →* W := Subgroup.noncommPiCoprod hcomm
  have hφinj : Function.Injective φ := Subgroup.injective_noncommPiCoprod_of_iSupIndep hind
  have hrange : φ.range = ⨆ i, U i := by
    change (Subgroup.noncommPiCoprod hcomm).range = ⨆ i, U i
    rw [Subgroup.noncommPiCoprod_range]
  have hvran : v ∈ φ.range := by rw [hrange]; exact hvsup
  obtain ⟨f, hf⟩ := hvran
  have hfix : ∀ y ∈ Y, ∀ i, y (f i : W) = (f i : W) := by
    intro y hy i
    let f' : ∀ j, U j := fun j =>
      ⟨y (f j : W), ((mem_stabSub.mp (hstab j hy)) (f j : W)).mpr (f j).property⟩
    have hφf' : φ f' = y (φ f) := by
      change (Subgroup.noncommPiCoprod hcomm) f' = y ((Subgroup.noncommPiCoprod hcomm) f)
      rw [Subgroup.noncommPiCoprod_apply, Subgroup.noncommPiCoprod_apply]
      simp only [f']
      exact (Finset.map_noncommProd Finset.univ (fun j => (f j : W)) _ y).symm
    have hyv : y v = v := (mem_fixV.mp hvfix) y hy
    have heq : f' = f := hφinj (by rw [hφf', hf, hyv])
    exact congrArg Subtype.val (congrFun heq i)
  have hmem : ∀ i, (f i : W) ∈ U i ⊓ fixV Y :=
    fun i => Subgroup.mem_inf.mpr ⟨(f i).property, fun y hy => hfix y hy i⟩
  have hvsum : v ∈ ⨆ i, (U i ⊓ fixV Y) := by
    rw [← hf]
    change (Subgroup.noncommPiCoprod hcomm) f ∈ ⨆ i, (U i ⊓ fixV Y)
    rw [Subgroup.noncommPiCoprod_apply]
    exact Subgroup.noncommProd_mem _ _
      (fun i _ => le_iSup (fun i => U i ⊓ fixV Y) i (hmem i))
  exact hvsum

private theorem s15_Twelve_star_inj (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) {Z Z' : Subgroup G}
    (hZ : Z ∈ wConj D.M V₀ V hV L) (hZ' : Z' ∈ wConj D.M V₀ V hV L)
    (heq : imgTil (v1Sub D.M V₀ V hV L) V hV Z =
      imgTil (v1Sub D.M V₀ V hV L) V hV Z') : Z = Z' := by
  obtain ⟨m, hm, rfl⟩ := hZ
  obtain ⟨m', hm', rfl⟩ := hZ'
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hbar := (s15_Core_imgTil_wSub_conj_eq_iff h hL hm hm').1 heq
  have hwTil := (s15_Core_wTil_conj_eq_iff h hL hm hm').2 hbar
  rw [← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hm),
      ← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hm')]
  unfold wSub
  rw [hwTil]

theorem s15_Twelve_count (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    {Y : Subgroup G} (hY : Y ≤ D.M)
    (hnorm : ∀ Z ∈ wConj D.M V₀ V hV L, Y ≤ normalizer (fSub15 D.M V₀ V hV L Z : Set G))
    (S : Finset (Subgroup G)) (hS : ∀ Z ∈ S, Z ∈ wConj D.M V₀ V hV L) :
    ∑ Z ∈ S, E3.mQuot (fSub15 D.M V₀ V hV L Z) (kSub15 D.M V₀ V hV L Y Z) ≤
      E3.mQuot V (centralizer (Y : Set G)) := by
  classical
  have hV₁V : v1Sub D.M V₀ V hV L ≤ V := s15_Infra_v1Sub_le h.hyp125 hV
  have hYV : Y ≤ normalizer (V : Set G) :=
    fun y hy => h.hyp125.pairFacts.le_normalizer (hY hy)
  have hYV₁ : Y ≤ normalizer (v1Sub D.M V₀ V hV L : Set G) :=
    fun y hy => s15_Infra_le_normalizer_v1Sub h.hyp125 hV (hY hy)
  have hYstab : Y ≤ stabTil (v1Sub D.M V₀ V hV L) V := le_stabTil hYV hYV₁
  obtain ⟨hind_set, hspan⟩ := fifteen_two_directSum D h1217 h hV hL
  let 𝓤 : Set (Subgroup (vStar D.M V₀ V hV L)) := wStarConj D.M V₀ V hV L
  haveI : Fintype 𝓤 := (Set.toFinite 𝓤).fintype
  have hind : iSupIndep (fun i : 𝓤 => (i : Subgroup (vStar D.M V₀ V hV L))) :=
    (sSupIndep_iff 𝓤).mp (show sSupIndep 𝓤 from hind_set)
  have hsup : (⨆ i : 𝓤, (i : Subgroup (vStar D.M V₀ V hV L))) = ⊤ := by
    rw [← sSup_eq_iSup']
    exact show sSup 𝓤 = ⊤ from hspan
  let Ch : Subgroup (vStar D.M V₀ V hV L) := fixV (barSub (v1Sub D.M V₀ V hV L) V hV Y)
  let Kh : Subgroup G := preTil (v1Sub D.M V₀ V hV L) V hV Ch
  let b : Subgroup (vStar D.M V₀ V hV L) → ℕ := fun U => E3.mQuot U (U ⊓ Ch)
  have hstab : ∀ i : 𝓤,
      barSub (v1Sub D.M V₀ V hV L) V hV Y ≤
        stabSub (i : Subgroup (vStar D.M V₀ V hV L)) := by
    intro i
    obtain ⟨m, hm, hXeq⟩ := (show (i : Subgroup (vStar D.M V₀ V hV L)) ∈
      wStarConj D.M V₀ V hV L from i.2)
    rw [hXeq]
    have hnormZ : Y ≤ normalizer
        (fSub15 D.M V₀ V hV L (conjSubgroup (wSub V₀ V hV L) m) : Set G) :=
      hnorm _ ⟨m, hm, rfl⟩
    have hle := s15_LP_barSub_le_stabSub_imgTil (V₀ := v1Sub D.M V₀ V hV L) hV hYstab hnormZ
    have himg : imgTil (v1Sub D.M V₀ V hV L) V hV
        (fSub15 D.M V₀ V hV L (conjSubgroup (wSub V₀ V hV L) m)) =
        imgTil (v1Sub D.M V₀ V hV L) V hV (conjSubgroup (wSub V₀ V hV L) m) :=
      s15_Infra_imgTil_sup_left hV (s15_Tools_conj_wSub_le D h.hyp125 hV hm) hV₁V
    rwa [himg] at hle
  have hfix : Ch = ⨆ i : 𝓤, ((i : Subgroup (vStar D.M V₀ V hV L)) ⊓ Ch) := by
    refine le_antisymm ?_ (iSup_le fun i => inf_le_right)
    have hle := s15_Twelve_fixV_iSupIndep_le
      (fun i : 𝓤 => (i : Subgroup (vStar D.M V₀ V hV L)))
      (barSub (v1Sub D.M V₀ V hV L) V hV Y) hind hstab
    rw [hsup, inf_top_eq] at hle
    exact hle
  have hPtop : IsPGroup 2 (⊤ : Subgroup (vStar D.M V₀ V hV L)) :=
    isPGroup_two_of_sq_eq_one fun g =>
      Subtype.ext (s15_Infra_vtil_sq_eq_one (v1Sub D.M V₀ V hV L) V hV
        (g : vStar D.M V₀ V hV L))
  have hper : ∀ i : 𝓤, b (i : Subgroup (vStar D.M V₀ V hV L)) +
      rk ↥((i : Subgroup (vStar D.M V₀ V hV L)) ⊓ Ch) =
      rk ↥(i : Subgroup (vStar D.M V₀ V hV L)) :=
    fun i => s15_Twelve_mQuot_inf_add_rk (hPtop.to_le le_top) Ch
  have hsum2 : ∑ i : 𝓤, rk ↥(i : Subgroup (vStar D.M V₀ V hV L)) =
      rk ↥(⊤ : Subgroup (vStar D.M V₀ V hV L)) := by
    have key : (⨆ i ∈ (Finset.univ : Finset 𝓤),
        (i : Subgroup (vStar D.M V₀ V hV L))) =
        ⨆ i : 𝓤, (i : Subgroup (vStar D.M V₀ V hV L)) := by
      rw [← Finset.iSup_coe, Finset.coe_univ, iSup_univ]
    have hh := rk_iSup_biSup_eq_sum
      (fun i : 𝓤 => (i : Subgroup (vStar D.M V₀ V hV L))) hind Finset.univ
    rw [key, hsup] at hh
    exact hh.symm
  have hind' : iSupIndep (fun i : 𝓤 => (i : Subgroup (vStar D.M V₀ V hV L)) ⊓ Ch) :=
    hind.mono fun i => inf_le_left
  have hsum3 : ∑ i : 𝓤, rk ↥((i : Subgroup (vStar D.M V₀ V hV L)) ⊓ Ch) = rk ↥Ch := by
    have key : (⨆ i ∈ (Finset.univ : Finset 𝓤),
        ((i : Subgroup (vStar D.M V₀ V hV L)) ⊓ Ch)) =
        ⨆ i : 𝓤, ((i : Subgroup (vStar D.M V₀ V hV L)) ⊓ Ch) := by
      rw [← Finset.iSup_coe, Finset.coe_univ, iSup_univ]
    have hh := rk_iSup_biSup_eq_sum
      (fun i : 𝓤 => (i : Subgroup (vStar D.M V₀ V hV L)) ⊓ Ch) hind' Finset.univ
    rw [key, ← hfix] at hh
    exact hh.symm
  have hsumB : ∑ i : 𝓤, b (i : Subgroup (vStar D.M V₀ V hV L)) = E3.mQuot V Kh := by
    have h1 : ∑ i : 𝓤, (b (i : Subgroup (vStar D.M V₀ V hV L)) +
        rk ↥((i : Subgroup (vStar D.M V₀ V hV L)) ⊓ Ch)) =
        (∑ i : 𝓤, b (i : Subgroup (vStar D.M V₀ V hV L))) +
          ∑ i : 𝓤, rk ↥((i : Subgroup (vStar D.M V₀ V hV L)) ⊓ Ch) :=
      Finset.sum_add_distrib
    have h2 : ∑ i : 𝓤, (b (i : Subgroup (vStar D.M V₀ V hV L)) +
        rk ↥((i : Subgroup (vStar D.M V₀ V hV L)) ⊓ Ch)) =
        ∑ i : 𝓤, rk ↥(i : Subgroup (vStar D.M V₀ V hV L)) :=
      Finset.sum_congr rfl fun i _ => hper i
    have h3 : (∑ i : 𝓤, b (i : Subgroup (vStar D.M V₀ V hV L))) + rk ↥Ch =
        rk ↥(⊤ : Subgroup (vStar D.M V₀ V hV L)) := by
      rw [← hsum3, ← h1, h2, hsum2]
    have h4 : rk ↥(⊤ : Subgroup (vStar D.M V₀ V hV L)) =
        rk (vStar D.M V₀ V hV L) := rk_top
    have h5 : E3.mQuot V Kh = rkIdx Ch :=
      s15_Twelve_mQuot_preTil (V₀ := v1Sub D.M V₀ V hV L) hV Ch
    have h6 : rk ↥Ch + rkIdx Ch = rk (vStar D.M V₀ V hV L) := rk_add_rkIdx Ch
    have hthis := h3
    rw [h4, ← h6, ← h5] at hthis
    refine Nat.add_left_cancel (n := rk ↥Ch) ?_
    rw [add_comm (rk ↥Ch) (∑ i : 𝓤, b (i : Subgroup (vStar D.M V₀ V hV L)))]
    exact hthis
  have hZV : ∀ Z ∈ wConj D.M V₀ V hV L, Z ≤ V := by
    intro Z hZ
    obtain ⟨m, hm, rfl⟩ := hZ
    exact s15_Tools_conj_wSub_le D h.hyp125 hV hm
  have hV₁Kh : v1Sub D.M V₀ V hV L ≤ Kh := by
    have hbot : (⊥ : Subgroup (vStar D.M V₀ V hV L)) ≤ Ch := bot_le
    have hmono := s15_LP_preTil_mono (V₀ := v1Sub D.M V₀ V hV L) (V := V) hV hbot
    rw [show Kh = preTil (v1Sub D.M V₀ V hV L) V hV Ch from rfl]
    refine le_trans ?_ hmono
    rw [preTil_bot]
    exact le_inf hV₁V le_rfl
  have hterm : ∀ Z ∈ S, E3.mQuot (fSub15 D.M V₀ V hV L Z) (kSub15 D.M V₀ V hV L Y Z) =
      b (imgTil (v1Sub D.M V₀ V hV L) V hV Z) := by
    intro Z hZmem
    have hZ := hS Z hZmem
    have hzV := hZV Z hZ
    have hFZ : fSub15 D.M V₀ V hV L Z ≤ V := sup_le hzV hV₁V
    have hV₁FZ : v1Sub D.M V₀ V hV L ≤ fSub15 D.M V₀ V hV L Z := le_sup_right
    have hV₁K : v1Sub D.M V₀ V hV L ≤ kSub15 D.M V₀ V hV L Y Z :=
      le_inf hV₁FZ hV₁Kh
    have hq := s15_Twelve_mQuot_imgTil (V₀ := v1Sub D.M V₀ V hV L)
      (F := fSub15 D.M V₀ V hV L Z) (K := kSub15 D.M V₀ V hV L Y Z) hV hV₁K inf_le_left hFZ
    have h1 : imgTil (v1Sub D.M V₀ V hV L) V hV (fSub15 D.M V₀ V hV L Z) =
        imgTil (v1Sub D.M V₀ V hV L) V hV Z :=
      s15_Infra_imgTil_sup_left hV hzV hV₁V
    have h2 : imgTil (v1Sub D.M V₀ V hV L) V hV (kSub15 D.M V₀ V hV L Y Z) =
        imgTil (v1Sub D.M V₀ V hV L) V hV Z ⊓ Ch := by
      rw [show kSub15 D.M V₀ V hV L Y Z = fSub15 D.M V₀ V hV L Z ⊓
          preTil (v1Sub D.M V₀ V hV L) V hV Ch from rfl,
        s15_Twelve_imgTil_inf_preTil hV Ch, h1]
    rw [← hq, h1, h2]
  let starmap : Subgroup G → Subgroup (vStar D.M V₀ V hV L) :=
    fun Z => imgTil (v1Sub D.M V₀ V hV L) V hV Z
  have hinj : ∀ Z ∈ S, ∀ Z' ∈ S, starmap Z = starmap Z' → Z = Z' := by
    intro Z hZ Z' hZ' heq
    exact s15_Twelve_star_inj D h hV hL (hS Z hZ) (hS Z' hZ') heq
  have himage_sub : S.image starmap ⊆ (Set.toFinite 𝓤).toFinset := by
    intro T hT
    obtain ⟨Z, hZ, rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨m, hm, hZm⟩ := hS Z hZ
    exact (Set.Finite.mem_toFinset _).2 ⟨m, hm, by rw [hZm]⟩
  have hconv : ∑ T ∈ (Set.toFinite 𝓤).toFinset, b T =
      ∑ i : 𝓤, b (i : Subgroup (vStar D.M V₀ V hV L)) := by
    rw [Set.Finite.toFinset_eq_toFinset, Set.toFinset, Finset.sum_map]
    rfl
  have hfinal : E3.mQuot V Kh ≤ E3.mQuot V (centralizer (Y : Set G)) := by
    have hCV : V ⊓ centralizer (Y : Set G) ≤ Kh := by
      intro w hw
      have hwV : w ∈ V := hw.1
      rw [show Kh = preTil (v1Sub D.M V₀ V hV L) V hV Ch from rfl]
      rw [s15_Glue_mem_preTil_fixV_iff (v1Sub D.M V₀ V hV L) V Y hV hYstab hwV]
      intro e he
      have hcomm : e * w = w * e := Subgroup.mem_centralizer_iff.mp hw.2 e he
      rw [show e * w * e⁻¹ * w⁻¹ = 1 by rw [hcomm]; group]
      exact (v1Sub D.M V₀ V hV L).one_mem
    have hinfC : E3.mQuot V (V ⊓ centralizer (Y : Set G)) =
        E3.mQuot V (centralizer (Y : Set G)) := by
      have hsub : (V ⊓ centralizer (Y : Set G)).subgroupOf V =
          (centralizer (Y : Set G)).subgroupOf V := by
        ext x
        simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        constructor
        · rintro ⟨-, hx⟩
          exact hx
        · intro hx
          exact ⟨x.2, hx⟩
      unfold E3.mQuot
      rw [show (V ⊓ centralizer (Y : Set G)).relIndex V =
          (centralizer (Y : Set G)).relIndex V from congrArg Subgroup.index hsub]
    have hmono := E3.mQuot_mono (V := V) hCV
    rwa [hinfC] at hmono
  calc ∑ Z ∈ S, E3.mQuot (fSub15 D.M V₀ V hV L Z) (kSub15 D.M V₀ V hV L Y Z)
      = ∑ Z ∈ S, b (starmap Z) := Finset.sum_congr rfl fun Z hZ => hterm Z hZ
    _ = ∑ T ∈ S.image starmap, b T := (Finset.sum_image hinj).symm
    _ ≤ ∑ T ∈ (Set.toFinite 𝓤).toFinset, b T :=
        Finset.sum_le_sum_of_subset_of_nonneg himage_sub (fun _ _ _ => Nat.zero_le _)
    _ = ∑ i : 𝓤, b (i : Subgroup (vStar D.M V₀ V hV L)) := hconv
    _ = E3.mQuot V Kh := hsumB
    _ ≤ E3.mQuot V (centralizer (Y : Set G)) := hfinal

theorem s15_Twelve_card_le (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) {n : ℕ} {k : G}
    (hk : Cond1512 n D.M V k) (hn : n < gamma15 D.M V₀ V hV L) {X : Subgroup G}
    (hX : X ∈ wConj D.M V₀ V hV L)
    (hc : E3.mQuot V (centralizer (ySub15 D.M V₀ V hV L X k : Set G)) < gamma15 D.M V₀ V hV L) :
    {Z : Subgroup G | Z ∈ wConj D.M V₀ V hV L ∧
        ¬ fSub15 D.M V₀ V hV L Z ≤ conjSubgroup D.M k}.ncard ≤
      E3.mQuot V (centralizer (ySub15 D.M V₀ V hV L X k : Set G)) := by
  classical
  let Y : Subgroup G := ySub15 D.M V₀ V hV L X k
  have hYM : Y ≤ D.M := inf_le_right
  have hnorm : ∀ Z ∈ wConj D.M V₀ V hV L, Y ≤ normalizer (fSub15 D.M V₀ V hV L Z : Set G) :=
    fun Z hZ => (s15_Twelve_fixes D h1217 h.hyp151 hV hL hYM hc hZ).1
  let T : Set (Subgroup G) := {Z : Subgroup G | Z ∈ wConj D.M V₀ V hV L ∧
    ¬ fSub15 D.M V₀ V hV L Z ≤ conjSubgroup D.M k}
  let S : Finset (Subgroup G) := (Set.toFinite T).toFinset
  have hS : ∀ Z ∈ S, Z ∈ wConj D.M V₀ V hV L := by
    intro Z hZ
    have hZ' : Z ∈ T := (Set.Finite.mem_toFinset _).1 hZ
    exact hZ'.1
  have hbound := s15_Twelve_count D h1217 h.hyp151 hV hL hYM hnorm S hS
  have hpos : ∀ Z ∈ S, 1 ≤ E3.mQuot (fSub15 D.M V₀ V hV L Z)
      (kSub15 D.M V₀ V hV L Y Z) := by
    intro Z hZ
    have hZ' : Z ∈ T := (Set.Finite.mem_toFinset _).1 hZ
    exact s15_Twelve_axis_pos D h hV hk hn hX hZ'.1 hZ'.2
  have hcard : S.card ≤ ∑ Z ∈ S, E3.mQuot (fSub15 D.M V₀ V hV L Z)
      (kSub15 D.M V₀ V hV L Y Z) := by
    calc S.card = ∑ Z ∈ S, 1 := Finset.card_eq_sum_ones S
      _ ≤ ∑ Z ∈ S, E3.mQuot (fSub15 D.M V₀ V hV L Z) (kSub15 D.M V₀ V hV L Y Z) :=
          Finset.sum_le_sum hpos
  calc {Z : Subgroup G | Z ∈ wConj D.M V₀ V hV L ∧
        ¬ fSub15 D.M V₀ V hV L Z ≤ conjSubgroup D.M k}.ncard = S.card := by
        rw [show {Z : Subgroup G | Z ∈ wConj D.M V₀ V hV L ∧
              ¬ fSub15 D.M V₀ V hV L Z ≤ conjSubgroup D.M k} = T from rfl]
        exact Set.ncard_eq_toFinset_card T (Set.toFinite T)
    _ ≤ E3.mQuot V (centralizer (ySub15 D.M V₀ V hV L X k : Set G)) :=
        le_trans hcard hbound

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
