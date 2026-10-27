module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SwapL3InF
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SwapSp4InF
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsF
import CFSG.LocalAnalysis.WeakClosure81.OrbitClosureCentreQuot
import CFSG.LocalAnalysis.WeakClosure81.CFAutAlmostSimple
import CFSG.LocalAnalysis.WeakClosure81.InFGroupOfInFTop
import CFSG.LocalAnalysis.WeakClosure81.FiveFiveFstar
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bridge13
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.Adapters.StatedPSLTwoSeven
import CFSG.GroupTheory.PCoreOfSubnormal
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22a
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Bar
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Shape
public import CFSG.Quasithin.Vol2.Ch11SecE3L0

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.SignalizerFunctorTheorem.McBride
open CFSG.Blueprint (LieModel)

private def SwapData {A : Type} [Group A] (S X : Subgroup A) : Prop :=
  IsPGroup 2 S ∧ S ≤ normalizer (X : Set A) ∧ IsSylowIn 2 (S ⊓ X) X ∧
    S17.SwapsParabolics S X

private theorem inf_eq_of_isSylowIn_le {A : Type} [Group A] [Finite A] {U S X : Subgroup A}
    (hU : IsSylowIn 2 U X) (hS : IsPGroup 2 S) (hUS : U ≤ S) : S ⊓ X = U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (isSylowOf_two_iff_isSylowIn.mpr hU).eq_of_le (le_inf hUS hU.1) inf_le_right
    (hS.to_le inf_le_left)

private theorem isSylowIn_map_of_isSylowIn {A B : Type} [Group A] [Group B] [Finite A]
    [Finite B] (φ : A →* B) {U L : Subgroup A} (hU : IsSylowIn 2 U L) :
    IsSylowIn 2 (U.map φ) (L.map φ) :=
  isSylowOf_two_iff_isSylowIn.mp (CFSG.QuasithinUnique.Setup.Layer.isSylowOf_map Nat.prime_two
    φ (isSylowOf_two_iff_isSylowIn.mpr hU))

private theorem isSylowIn_of_le_of_le {A : Type} [Group A] {U W X : Subgroup A}
    (hU : IsSylowIn 2 U X) (hUW : U ≤ W) (hWX : W ≤ X) : IsSylowIn 2 U W := by
  refine ⟨hUW, hU.isPGroup, fun hdvd => hU.not_dvd_relIndex ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex U W X hUW hWX]
  exact hdvd.mul_right _

private theorem not_le_of_swapsParabolics {A : Type} [Group A] {T X : Subgroup A}
    (h : S17.SwapsParabolics T X) : ¬ T ≤ X := by
  intro hTX
  obtain ⟨t, htT, P, ⟨-, hPN, -, -⟩, hmove⟩ := h
  have htP : t ∈ P := hPN ⟨hTX htT, le_normalizer (⟨htT, hTX htT⟩ : t ∈ T ⊓ X)⟩
  exact hmove (mem_normalizer_iff_map_conj_eq.mp (le_normalizer htP))

private theorem map_center_le_normalizer {A : Type} [Group A] {K U : Subgroup A} (hUK : U ≤ K) :
    (center ↥K).map K.subtype ≤ normalizer (U : Set A) := by
  intro z hz
  rw [CFSG.LocalCores.mem_map_center_iff] at hz
  rw [mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    have hc : u * z = z * u := mem_centralizer_iff.mp hz.2 u (hUK hu)
    have : z * u * z⁻¹ = u := by rw [← hc, mul_inv_cancel_right]
    rwa [this]
  · intro hu
    have hw : z * u * z⁻¹ * z = z * (z * u * z⁻¹) := mem_centralizer_iff.mp hz.2 _ (hUK hu)
    have : u = z * u * z⁻¹ := by
      have h2 : z * u = z * (z * u * z⁻¹) := by
        calc z * u = z * u * z⁻¹ * z := by group
          _ = z * (z * u * z⁻¹) := hw
      exact mul_left_cancel h2
    rwa [this]

private theorem SwapData.map {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (φ : A →* B) {S X : Subgroup A} (h : SwapData S X)
    (hker : X ⊓ φ.ker ≤ normalizer ((S ⊓ X : Subgroup A) : Set A)) :
    SwapData (S.map φ) (X.map φ) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hS2, hSN, hU, t, htS, P, ⟨hPX, hPN, hPne, hPmax⟩, hmove⟩ := h
  have hUmap : S.map φ ⊓ X.map φ = (S ⊓ X).map φ :=
    inf_eq_of_isSylowIn_le (isSylowIn_map_of_isSylowIn φ hU) (hS2.map φ)
      (map_mono inf_le_left)
  have hZP : X ⊓ φ.ker ≤ P := fun x hx => hPN ⟨hx.1, hker hx⟩
  have hpull : ∀ Q : Subgroup A, Q ≤ X → X ⊓ φ.ker ≤ Q → ∀ x ∈ X, φ x ∈ Q.map φ → x ∈ Q := by
    intro Q hQX hZQ x hx hxQ
    obtain ⟨q, hq, hqx⟩ := mem_map.mp hxQ
    have hz : q⁻¹ * x ∈ X ⊓ φ.ker :=
      ⟨X.mul_mem (X.inv_mem (hQX hq)) hx,
        MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hqx, inv_mul_cancel])⟩
    have hmem := Q.mul_mem hq (hZQ hz)
    rwa [mul_inv_cancel_left] at hmem
  refine ⟨hS2.map φ, (map_mono hSN).trans (le_normalizer_map φ),
    hUmap ▸ isSylowIn_map_of_isSylowIn φ hU, φ t, mem_map_of_mem φ htS, P.map φ,
    ⟨map_mono hPX, ?_, ?_, ?_⟩, ?_⟩
  · rw [hUmap]
    rintro y ⟨hyX, hyN⟩
    obtain ⟨x, hxX, rfl⟩ := mem_map.mp hyX
    refine mem_map_of_mem φ (hPN ⟨hxX, ?_⟩)
    set U : Subgroup A := S ⊓ X with hUdef
    let W : Subgroup A := (U.map φ).comap φ ⊓ X
    have hUW : U ≤ W := fun u hu => ⟨mem_map_of_mem φ hu, hu.2⟩
    have hWX : W ≤ X := inf_le_right
    have hWN : W ≤ normalizer (U : Set A) := by
      rintro w ⟨hwU, hwX⟩
      obtain ⟨u, hu, huw⟩ := mem_map.mp (mem_comap.mp hwU)
      have hz : u⁻¹ * w ∈ X ⊓ φ.ker :=
        ⟨X.mul_mem (X.inv_mem hu.2) hwX,
          MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, huw, inv_mul_cancel])⟩
      have hmem := (normalizer (U : Set A)).mul_mem (le_normalizer hu) (hker hz)
      rwa [mul_inv_cancel_left] at hmem
    have hUxW : U.map (MulAut.conj x).toMonoidHom ≤ W := by
      rintro _ ⟨u, hu, rfl⟩
      refine ⟨?_, X.mul_mem (X.mul_mem hxX hu.2) (X.inv_mem hxX)⟩
      show φ (x * u * x⁻¹) ∈ U.map φ
      rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.mp hyN (φ u)).mp (mem_map_of_mem φ hu)
    have hUxX : IsSylowIn 2 (U.map (MulAut.conj x).toMonoidHom) X :=
      CFSG.Quasithin.Ch1Sec3.isSylowIn_map_conj hU (le_normalizer hxX)
    obtain ⟨w, hwW, hw⟩ := CFSG.Quasithin.Ch1Sec3.exists_conj_of_isSylowIn
      (isSylowIn_of_le_of_le hU hUW hWX) (isSylowIn_of_le_of_le hUxX hUxW hWX)
    have hwN : w⁻¹ ∈ normalizer (U : Set A) := inv_mem (hWN hwW)
    refine mem_normalizer_iff_map_conj_eq.mpr (le_antisymm ?_ ?_)
    · intro y hy
      have h1 := (hw y).mp hy
      have h2 := (mem_normalizer_iff.mp hwN y).mpr
      simpa [mul_assoc] using h2 (by simpa [mul_assoc] using h1)
    · intro y hy
      refine (hw y).mpr ?_
      have h2 := (mem_normalizer_iff.mp hwN y).mp hy
      simpa [mul_assoc] using h2
  · intro heq
    exact hPne (le_antisymm hPX fun x hx => hpull P hPX hZP x hx (heq ▸ mem_map_of_mem φ hx))
  · intro Q' hPQ' hQ'X
    have hQmap : (Q'.comap φ ⊓ X).map φ = Q' := by
      refine le_antisymm (map_le_iff_le_comap.mpr inf_le_left) fun y hy => ?_
      obtain ⟨x, hxX, rfl⟩ := mem_map.mp (hQ'X hy)
      exact mem_map_of_mem φ ⟨hy, hxX⟩
    rcases hPmax (Q'.comap φ ⊓ X) (fun x hx => ⟨hPQ' (mem_map_of_mem φ hx), hPX hx⟩)
        inf_le_right with h | h
    · left
      rw [← hQmap, h]
    · right
      rw [← hQmap, h]
  · intro heq
    rw [← CFSG.LieType.Steinberg.map_map_conj] at heq
    have htX : X.map (MulAut.conj t).toMonoidHom = X :=
      mem_normalizer_iff_map_conj_eq.mp (hSN htS)
    have hPtX : P.map (MulAut.conj t).toMonoidHom ≤ X := htX ▸ map_mono hPX
    have hZPt : X ⊓ φ.ker ≤ P.map (MulAut.conj t).toMonoidHom := by
      intro z hz
      refine mem_map.mpr ⟨t⁻¹ * z * t, hZP ⟨?_, ?_⟩, ?_⟩
      · have ht' : t⁻¹ ∈ normalizer (X : Set A) := inv_mem (hSN htS)
        simpa using (mem_normalizer_iff.mp ht' z).mp hz.1
      · exact MonoidHom.mem_ker.mpr (by
          rw [map_mul, map_mul, map_inv, MonoidHom.mem_ker.mp hz.2, mul_one, inv_mul_cancel])
      · simp [MulAut.conj_apply, mul_assoc]
    apply hmove
    exact le_antisymm (fun x hx => hpull P hPX hZP x (hPtX hx) (heq ▸ mem_map_of_mem φ hx))
      (fun x hx => hpull _ hPtX hZPt x (hPX hx) (heq.symm ▸ mem_map_of_mem φ hx))

private theorem SwapData.mono {A : Type} [Group A] [Finite A] {S S' X : Subgroup A}
    (h : SwapData S X) (hle : S ≤ S') (hS' : IsPGroup 2 S')
    (hS'N : S' ≤ normalizer (X : Set A)) : SwapData S' X := by
  obtain ⟨-, -, hU, t, htS, P, hP, hmove⟩ := h
  have heq : S' ⊓ X = S ⊓ X := inf_eq_of_isSylowIn_le hU hS' (inf_le_left.trans hle)
  refine ⟨hS', hS'N, heq ▸ hU, t, hle htS, P, ?_, hmove⟩
  rw [heq]
  exact hP

private theorem SwapData.subgroupOf {A : Type} [Group A] [Finite A] {H S X : Subgroup A}
    (hSH : S ≤ H) (hXH : X ≤ H) (h : SwapData S X) :
    SwapData (S.subgroupOf H) (X.subgroupOf H) := by
  obtain ⟨hS2, hSN, hU, t, htS, P, ⟨hPX, hPN, hPne, hPmax⟩, hmove⟩ := h
  have hPH : P ≤ H := hPX.trans hXH
  have hinf : S.subgroupOf H ⊓ X.subgroupOf H = (S ⊓ X).subgroupOf H := by
    ext x
    simp [mem_subgroupOf]
  have hN : ∀ {K : Subgroup A}, K ≤ H → ∀ x : ↥H,
      x ∈ normalizer ((K.subgroupOf H : Subgroup ↥H) : Set ↥H) ↔
        (x : A) ∈ normalizer (K : Set A) := by
    intro K hKH x
    rw [← subgroupOf_normalizer_eq hKH, mem_subgroupOf]
  refine ⟨hS2.of_equiv (subgroupOfEquivOfLe hSH).symm,
    fun x hx => (hN hXH x).mpr (hSN (mem_subgroupOf.mp hx)), ?_, ⟨t, hSH htS⟩,
    mem_subgroupOf.mpr htS, P.subgroupOf H, ⟨subgroupOf_mono _ hPX, ?_, ?_, ?_⟩, ?_⟩
  · rw [hinf]
    exact (E1.isSylowIn_subgroupOf_iff (inf_le_left.trans hSH) hXH).mpr hU
  · rw [hinf]
    rintro x ⟨hxX, hxN⟩
    exact mem_subgroupOf.mpr
      (hPN ⟨mem_subgroupOf.mp hxX, (hN (inf_le_left.trans hSH) x).mp hxN⟩)
  · intro heq
    apply hPne
    have h1 := congrArg (Subgroup.map H.subtype) heq
    rwa [map_subgroupOf_eq_of_le hPH, map_subgroupOf_eq_of_le hXH] at h1
  · intro Q' hPQ' hQ'X
    have hPQ : P ≤ Q'.map H.subtype := fun p hp =>
      ⟨⟨p, hPH hp⟩, hPQ' (mem_subgroupOf.mpr hp), rfl⟩
    have hQX : Q'.map H.subtype ≤ X := by
      rintro _ ⟨q, hq, rfl⟩
      exact mem_subgroupOf.mp (hQ'X hq)
    have hQ' : (Q'.map H.subtype).subgroupOf H = Q' := by
      rw [← comap_subtype, comap_map_eq_self_of_injective H.subtype_injective]
    rcases hPmax _ hPQ hQX with h | h
    · left
      rw [← hQ', h]
    · right
      rw [← hQ', h]
  · intro heq
    apply hmove
    have h1 := congrArg (Subgroup.map H.subtype) heq
    rwa [CFSG.LieType.Steinberg.map_map_conj, map_subgroupOf_eq_of_le hPH] at h1

private theorem inFGroup_autQuot_of_swap (hSp : K_SwapSp4InF) (hL3 : K_SwapL3InF)
    (h410 : W4Lem4_10) {Q : Type} [Group Q] [Finite Q] {S L : Subgroup Q} {n : ℕ}
    (hsimple : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a)
    (hshape : IsL3 ↥L n ∨ IsSp4 ↥L n) (hsw : SwapData (S ⊓ normalizer (L : Set Q)) L) :
    ∃ h : ((F12.autC S L).subgroupOf (F12.autNL S L)).Normal,
      haveI := h
      InFGroup n (↥(F12.autNL S L) ⧸ (F12.autC S L).subgroupOf (F12.autNL S L)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup Q := F12.autNL S L
  let Lq : Subgroup ↥N := L.subgroupOf N
  let Kq : Subgroup ↥N := (S ⊓ normalizer (L : Set Q)).subgroupOf N
  have hKN : S ⊓ normalizer (L : Set Q) ≤ N := by
    show _ ≤ (S ⊓ normalizer (L : Set Q)) ⊔ L
    exact le_sup_left
  have hLN : L ≤ N := by
    show _ ≤ (S ⊓ normalizer (L : Set Q)) ⊔ L
    exact le_sup_right
  have hNL : N ≤ normalizer (L : Set Q) := by
    show (S ⊓ normalizer (L : Set Q)) ⊔ L ≤ _
    exact sup_le inf_le_right le_normalizer
  have hLq : Lq.Normal := (normal_subgroupOf_iff_le_normalizer hLN).mpr hNL
  have : Lq.Normal := hLq
  have hsup : Lq ⊔ Kq = ⊤ := by
    have hN : L ⊔ (S ⊓ normalizer (L : Set Q)) = N := by
      show L ⊔ (S ⊓ normalizer (L : Set Q)) = (S ⊓ normalizer (L : Set Q)) ⊔ L
      exact sup_comm ..
    have h1 : (L ⊔ (S ⊓ normalizer (L : Set Q))).subgroupOf N = Lq ⊔ Kq :=
      subgroupOf_sup (A := L) (A' := S ⊓ normalizer (L : Set Q)) (B := N) hLN hKN
    rw [hN] at h1
    rw [← h1, subgroupOf_self]
  have hCeq : (F12.autC S L).subgroupOf N = centralizer (Lq : Set ↥N) := by
    ext x
    show (x : Q) ∈ F12.autC S L ↔ x ∈ centralizer (Lq : Set ↥N)
    simp only [F12.autC, F12.autNL, mem_inf, mem_centralizer_iff]
    constructor
    · rintro ⟨-, hc⟩ y hy
      exact Subtype.ext (hc (y : Q) hy)
    · intro hc
      refine ⟨x.2, fun y hy => ?_⟩
      let yN : ↥N := ⟨y, hLN hy⟩
      have hyLq : yN ∈ Lq := mem_subgroupOf.mpr hy
      exact congrArg Subtype.val (hc yN hyLq)
  have hCn : ((F12.autC S L).subgroupOf N).Normal := hCeq ▸ normal_centralizer
  have : ((F12.autC S L).subgroupOf N).Normal := hCn
  refine ⟨hCn, ?_⟩
  set C : Subgroup ↥N := (F12.autC S L).subgroupOf N with hCdef
  have hswq : SwapData Kq Lq := SwapData.subgroupOf hKN hLN hsw
  let eLq : ↥Lq ≃* ↥L := subgroupOfEquivOfLe hLN
  have hsimpleq : IsSimpleGroup ↥Lq := eLq.isSimpleGroup_congr.mpr hsimple
  have hnabq : ∃ a b : ↥Lq, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨eLq.symm a, eLq.symm b, fun h => hab (by simpa using congrArg eLq h)⟩
  have hcenter : center ↥Lq = ⊥ := Vol2.Ch11.SecE3.center_eq_bot_of_simple hnabq
  have hLC : Lq ⊓ C = ⊥ := by
    rw [hCeq]
    refine le_bot_iff.mp ?_
    rintro x ⟨hxL, hxC⟩
    have hx' : (⟨x, hxL⟩ : ↥Lq) ∈ center ↥Lq := by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (mem_centralizer_iff.mp hxC (y : ↥N) y.2)
    rw [hcenter] at hx'
    exact congrArg Subtype.val (mem_bot.mp hx')
  let mk : ↥N →* ↥N ⧸ C := QuotientGroup.mk' C
  let Lbar : Subgroup (↥N ⧸ C) := Lq.map mk
  let Tbar : Subgroup (↥N ⧸ C) := Kq.map mk
  have hswbar : SwapData Tbar Lbar := SwapData.map mk hswq (by
    rw [QuotientGroup.ker_mk', hLC]
    exact bot_le)
  let f : ↥Lq →* ↥Lbar :=
    (mk.comp Lq.subtype).codRestrict Lbar (fun x => mem_map.mpr ⟨(x : ↥N), x.2, rfl⟩)
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have h1 : mk ((x : ↥N)⁻¹ * (y : ↥N)) = 1 := by
      have h2 : mk (x : ↥N) = mk (y : ↥N) :=
        congrArg (fun z : ↥Lbar => (z : ↥N ⧸ C)) hxy
      rw [map_mul, map_inv, h2, inv_mul_cancel]
    have h2 : (x : ↥N)⁻¹ * (y : ↥N) ∈ C := (QuotientGroup.eq_one_iff _).mp h1
    have h3 : (x : ↥N)⁻¹ * (y : ↥N) ∈ Lq := Lq.mul_mem (Lq.inv_mem x.2) y.2
    have h4 : (x : ↥N)⁻¹ * (y : ↥N) = 1 := by
      have h5 : (x : ↥N)⁻¹ * (y : ↥N) ∈ Lq ⊓ C := ⟨h3, h2⟩
      rw [hLC] at h5
      exact mem_bot.mp h5
    exact Subtype.ext (inv_mul_eq_one.mp h4)
  have hf_surj : Function.Surjective f := by
    intro y
    obtain ⟨x, hxL, hxy⟩ := mem_map.mp y.2
    exact ⟨⟨x, hxL⟩, Subtype.ext hxy⟩
  let e : ↥Lq ≃* ↥Lbar := MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hLbarN : Lbar.Normal := hLq.map mk (QuotientGroup.mk'_surjective C)
  have : Lbar.Normal := hLbarN
  have hsimplebar : IsSimpleGroup ↥Lbar := e.isSimpleGroup_congr.mp hsimpleq
  have hCbar : centralizer (Lbar : Set (↥N ⧸ C)) = ⊥ := by
    rw [eq_bot_iff_forall]
    intro a ha
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective a
    have hm : m ∈ C := by
      rw [hCeq, mem_centralizer_iff]
      intro l hl
      have hmem : mk l ∈ Lbar := mem_map.mpr ⟨l, hl, rfl⟩
      have hcomm' : mk m * mk l = mk l * mk m := (mem_centralizer_iff.mp ha (mk l) hmem).symm
      have h1 : mk (m * l * m⁻¹ * l⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm']
        group
      have h2 : m * l * m⁻¹ * l⁻¹ ∈ C := (QuotientGroup.eq_one_iff _).mp h1
      have h3 : m * l * m⁻¹ * l⁻¹ ∈ Lq := Lq.mul_mem (hLq.conj_mem l hl m) (Lq.inv_mem hl)
      have h4 : m * l * m⁻¹ * l⁻¹ = 1 := by
        have h5 : m * l * m⁻¹ * l⁻¹ ∈ Lq ⊓ C := ⟨h3, h2⟩
        rw [hLC] at h5
        exact mem_bot.mp h5
      have h5 : m * l * m⁻¹ = l := mul_inv_eq_one.mp h4
      have h6 : m * l = l * m := by
        calc m * l = (m * l * m⁻¹) * m := by group
          _ = l * m := by rw [h5]
      exact h6.symm
    exact (QuotientGroup.eq_one_iff m).mpr hm
  have hnabbar : ¬ ∀ x ∈ Lbar, ∀ y ∈ Lbar, x * y = y * x := by
    intro h
    obtain ⟨a, b, hab⟩ := hnabq
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact Subtype.ext (h _ (e a).2 _ (e b).2)
  have hFstar : Fstar (⊤ : Subgroup (↥N ⧸ C)) = Lbar :=
    fstar_eq_of_isSimpleGroup_of_centralizer_eq_bot le_top (hLbarN.subgroupOf ⊤) hsimplebar
      hnabbar (by rw [top_inf_eq]; exact hCbar)
  have hsupbar : Lbar ⊔ Tbar = ⊤ := by
    rw [← Subgroup.map_sup, hsup, map_top_of_surjective mk (QuotientGroup.mk'_surjective C)]
  have hTsyl : IsSylowIn 2 Tbar ⊤ := by
    refine ⟨le_top, hswbar.1, ?_⟩
    rw [← hsupbar, CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal,
      ← inf_relIndex_right]
    exact hswbar.2.2.1.not_dvd_relIndex
  let eLbar : ↥L ≃* ↥Lbar := eLq.symm.trans e
  rcases hshape with h3 | h4
  · have h3' : IsL3 ↥Lbar n := LieModel.of_mulEquiv eLbar h3
    rcases Nat.lt_or_ge n 2 with hn | hn
    · have hn1 : n = 1 := by
        have := (LieModel.admissible h3').2.1
        omega
      subst hn1
      have hmodel : StatedClassicalModel ↥Lbar .PSL 3 2 1 :=
        LieModel.statedClassicalModel_of_ne_zero (by norm_num) h3'
      have hF6 : F6.IsL2 7 1 ↥Lbar :=
        CFSG.Open.StatedAPI.statedClassicalModel_psl_two_seven_of_psl_three_two hmodel
      have hLcard : Nat.card ↥Lbar = 168 := by
        have := two_mul_card_isL2_odd (p := 7) (e := 1) (by norm_num) (by norm_num) hF6
        omega
      have hdvd : 168 ∣ Nat.card (↥N ⧸ C) := hLcard ▸ Subgroup.card_subgroup_dvd_card Lbar
      have hne : Nat.card (↥N ⧸ C) ≠ 168 := by
        intro hc
        have htop : Lbar = ⊤ := Subgroup.eq_top_of_card_eq Lbar (hLcard.trans hc.symm)
        exact not_le_of_swapsParabolics hswbar.2.2.2 (htop ▸ le_top)
      rcases h410 (↥N ⧸ C) Lbar Tbar 7 hLbarN hFstar
          ⟨7, 1, by norm_num, by norm_num, by norm_num, hF6⟩ (by norm_num) (by norm_num)
          hTsyl hsupbar with hF | hAlt | ⟨hsmall, -⟩
      · exact hF
      · exact absurd hAlt (not_isAlt_five_of_isL2_odd (p := 7) (e := 1) (by norm_num)
          (by norm_num) (by norm_num) hF6)
      · exfalso
        rcases hsmall with h7 | h9 | hS6
        · have := two_mul_card_isL2_odd (p := 7) (e := 1) (by norm_num) (by norm_num) h7
          omega
        · have := two_mul_card_isL2_odd (p := 3) (e := 2) (by norm_num) (by norm_num) h9
          omega
        · obtain ⟨eS⟩ := hS6
          have h720 : Nat.card (↥N ⧸ C) = 720 := by
            rw [Nat.card_congr eS.toEquiv, Nat.card_perm, Nat.card_fin]
            norm_num
          omega
    · exact inFGroup_of_inF_top n
        (hL3 (↥N ⧸ C) Lbar Tbar n hFstar hsimplebar h3' hn hTsyl hsupbar hswbar.2.2.2)
  · have h4' : IsSp4 ↥Lbar n := LieModel.of_mulEquiv eLbar h4
    exact inFGroup_of_inF_top n (hSp (↥N ⧸ C) Lbar Tbar n hFstar hsimplebar h4'
      (uc22p22a_two_le_of_isSp4 h4') hTsyl hsupbar hswbar.2.2.2)

private theorem cfAutInFGroup_of_component_swap (hSp : K_SwapSp4InF) (hL3 : K_SwapL3InF)
    (h410 : W4Lem4_10) {Q : Type} [Group Q] [Finite Q] {K S : Subgroup Q}
    (hK : CFSG.IsComponent K) (hS2 : IsPGroup 2 S) (hKT : orbitClosure K S ⊔ S = ⊤) {n : ℕ}
    (hsimple : IsSimpleGroup ↥K) (hshape : IsL3 ↥K n ∨ IsSp4 ↥K n)
    (hsw : SwapData (S ⊓ normalizer (K : Set Q)) K) :
    CFAutInFGroup n Q S := by
  classical
  intro X hXn hXne hXmin hXnc L hL
  let F : Subgroup Q := orbitClosure K S
  have hFnorm : F.Normal := orbitClosure_normal hKT
  have hQF2 : IsPGroup 2 (Q ⧸ F) := by
    have : F.Normal := hFnorm
    have : (F.subgroupOf (⊤ : Subgroup Q)).Normal := hFnorm.subgroupOf ⊤
    have htop : IsPGroup 2 ((⊤ : Subgroup Q) ⧸ F.subgroupOf ⊤) :=
      CFSG.Quasithin.F112R.isPGroup_quotient_of_sup_eq (p := 2) (G := Q)
        (L := F) (Q := S) (K := ⊤) hS2 le_top
        (by rw [normalizer_eq_top_iff.mpr hFnorm]; exact le_top) hKT
    have he : (F.subgroupOf (⊤ : Subgroup Q)).map
        (Subgroup.topEquiv (G := Q)).toMonoidHom = F := by
      ext x
      simp [mem_map, mem_subgroupOf]
    exact IsPGroup.of_equiv htop
      (QuotientGroup.congr (F.subgroupOf ⊤) F Subgroup.topEquiv he)
  have hLcomp : CFSG.IsComponent L := by
    have hsub : CFSG.Open.IsSubnormal L ⊤ :=
      CFSG.Open.IsSubnormal.trans hL.2.1
        (CFSG.Open.IsSubnormal.of_mathlib (Subgroup.Normal.isSubnormal hXn))
    exact ⟨CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hL.2.2,
      CFSG.Quasithin.A3.subnormal_top_iff.mp hsub⟩
  have hLleF : L ≤ F := by
    by_contra hnot
    let π : Q →* Q ⧸ F := QuotientGroup.mk' F
    have hmapne : L.map π ≠ ⊥ := fun hbot =>
      hnot (by simpa [π, QuotientGroup.ker_mk'] using (map_eq_bot_iff L).mp hbot)
    have : Nontrivial ↥(L.map π) := (nontrivial_iff_ne_bot _).mpr hmapne
    have hsol : Group.IsSolvable ↥(L.map π) :=
      @IsNilpotent.to_isSolvable _ _ (hQF2.to_subgroup (L.map π)).isNilpotent
    have hperf : Group.IsPerfect ↥(L.map π) := by
      have : Group.IsPerfect ↥L := hLcomp.1.1
      exact Group.IsPerfect.map π
    exact Group.IsPerfect.not_isSolvable ↥(L.map π) hsol
  have hconj : ∃ s ∈ S, L = K.map (MulAut.conj s).toMonoidHom := by
    by_contra hnot
    push Not at hnot
    have hcomm : ∀ s ∈ S, ⁅K.map (MulAut.conj s).toMonoidHom, L⁆ = ⊥ := by
      intro s hs
      rcases CFSG.LocalCores.distinct_components_commute (isComponent_map_conjAut hK s)
        hLcomp with h | h
      · exact absurd h.symm (hnot s hs)
      · exact h
    have hFleC : F ≤ centralizer (L : Set Q) :=
      orbitClosure_le fun s hs => commutator_eq_bot_iff_le_centralizer.mp (hcomm s hs)
    have hLleCF : L ≤ centralizer (F : Set Q) := by
      rw [le_centralizer_iff]
      exact hFleC
    have hLcomm : IsMulCommutative ↥L :=
      ⟨⟨fun a b => Subtype.ext
        ((mem_centralizer_iff.mp (hLleCF a.2) (b : Q) (hLleF b.2)).symm)⟩⟩
    have : Group.IsPerfect ↥L := hLcomp.1.1
    have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hLcomp.1
    exact Group.IsPerfect.not_isMulCommutative L hLcomm
  obtain ⟨s, hs, rfl⟩ := hconj
  let es : ↥K ≃* ↥(K.map (MulAut.conj s).toMonoidHom) :=
    equivMapOfInjective K (MulAut.conj s).toMonoidHom (MulAut.conj s).injective
  have hnabK : ∃ a b : ↥K, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have : Group.IsPerfect ↥K := hK.1.1
    have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
    exact Group.IsPerfect.not_isMulCommutative ↥K ⟨⟨fun a b => h a b⟩⟩
  have hnabL : ∃ a b : ↥(K.map (MulAut.conj s).toMonoidHom), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnabK
    exact ⟨es a, es b, fun h => hab (es.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hswL : SwapData (S ⊓ normalizer ((K.map (MulAut.conj s).toMonoidHom : Subgroup Q) :
      Set Q)) (K.map (MulAut.conj s).toMonoidHom) := by
    have h1 := SwapData.map (MulAut.conj s).toMonoidHom hsw (by
      rw [(MonoidHom.ker_eq_bot_iff _).mpr (MulAut.conj s).injective, inf_bot_eq]
      exact bot_le)
    have hSs : S.map (MulAut.conj s).toMonoidHom = S :=
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer hs)
    rwa [map_inf _ _ _ (MulAut.conj s).injective, hSs, map_equiv_normalizer_eq] at h1
  exact inFGroup_autQuot_of_swap hSp hL3 h410 (es.isSimpleGroup_congr.mp hsimple) hnabL
    (hshape.imp (LieModel.of_mulEquiv es) (LieModel.of_mulEquiv es)) hswL

private theorem compFactorAutInF_of_orbitClosure_swap (hSp : K_SwapSp4InF) (hL3 : K_SwapL3InF)
    (h410 : W4Lem4_10) {Q : Type} [Group Q] [Finite Q]
    (hO2 : pCoreOf 2 (⊤ : Subgroup Q) = ⊥) {K T : Subgroup Q} (hK : CFSG.IsComponent K)
    (hT : IsSylowIn 2 T ⊤) (hKT : orbitClosure K T ⊔ T = ⊤) {n : ℕ}
    (hshape : IsL3 (↥K ⧸ center ↥K) n ∨ IsSp4 (↥K ⧸ center ↥K) n)
    (hsw : SwapData (T ⊓ normalizer (K : Set Q)) K) :
    ∀ T' : Subgroup Q, CFSG.ABGLocalTools.IsSylowOf 2 T' ⊤ → CompFactorAutInF n ⊤ T' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have hFnorm : (orbitClosure K T).Normal := orbitClosure_normal hKT
  have hQF2 : IsPGroup 2 (Q ⧸ orbitClosure K T) := by
    have : (orbitClosure K T).Normal := hFnorm
    have : ((orbitClosure K T).subgroupOf (⊤ : Subgroup Q)).Normal :=
      hFnorm.subgroupOf ⊤
    have htop : IsPGroup 2 ((⊤ : Subgroup Q) ⧸ (orbitClosure K T).subgroupOf ⊤) :=
      CFSG.Quasithin.F112R.isPGroup_quotient_of_sup_eq (p := 2) (G := Q)
        (L := orbitClosure K T) (Q := T) (K := ⊤) hT2 le_top
        (by rw [normalizer_eq_top_iff.mpr hFnorm]; exact le_top) hKT
    have he : ((orbitClosure K T).subgroupOf (⊤ : Subgroup Q)).map
        (Subgroup.topEquiv (G := Q)).toMonoidHom = orbitClosure K T := by
      ext x
      simp [mem_map, mem_subgroupOf]
    exact IsPGroup.of_equiv htop
      (QuotientGroup.congr ((orbitClosure K T).subgroupOf ⊤) (orbitClosure K T)
        Subgroup.topEquiv he)
  intro T' hT'
  have hT'in : IsSylowIn 2 T' ⊤ := CFSG.ABGLocalTools.isSylowOf_iff.mp hT'
  obtain ⟨q, -, hq⟩ := CFSG.Quasithin.Ch1Sec3.exists_conj_of_isSylowIn hT hT'in
  have hT'eq : T' = T.map (MulAut.conj q).toMonoidHom := by
    ext x
    rw [mem_map]
    constructor
    · intro hx
      exact ⟨q⁻¹ * x * q, (hq x).mp hx, by simp [MulAut.conj_apply]; group⟩
    · rintro ⟨y, hy, rfl⟩
      exact (hq (q * y * q⁻¹)).mpr (by
        rw [show q⁻¹ * (q * y * q⁻¹) * q = y from by group]
        exact hy)
  set K' : Subgroup Q := K.map (MulAut.conj q).toMonoidHom with hK'def
  have hK' : CFSG.IsComponent K' := isComponent_map_conjAut hK q
  have hFconj : orbitClosure K' T' = orbitClosure K T := by
    rw [hK'def, hT'eq]
    exact (orbitClosure_map (MulAut.conj q).toMonoidHom K T).symm.trans
      (Subgroup.Normal.map_conj_eq (orbitClosure K T) q)
  have hFT' : orbitClosure K T ⊔ T' = ⊤ := by
    have : (orbitClosure K T).Normal := hFnorm
    let P : Sylow 2 Q := hT'in.isPGroup.toSylow (by simpa using hT'in.not_dvd_relIndex)
    have h := CFSG.section10_sylow_sup_normal_of_p_quotient_eq_top
      (N := orbitClosure K T) hQF2 P
    rw [IsPGroup.toSylow_coe] at h
    rw [sup_comm]
    exact h
  let eq' : ↥K ≃* ↥K' :=
    equivMapOfInjective K (MulAut.conj q).toMonoidHom (MulAut.conj q).injective
  let eZ : (↥K ⧸ center ↥K) ≃* (↥K' ⧸ center ↥K') :=
    QuotientGroup.congr (center ↥K) (center ↥K') eq' (map_center_eq _)
  have hshape' : IsL3 (↥K' ⧸ center ↥K') n ∨ IsSp4 (↥K' ⧸ center ↥K') n :=
    hshape.imp (LieModel.of_mulEquiv eZ) (LieModel.of_mulEquiv eZ)
  have hsw' : SwapData (T' ⊓ normalizer (K' : Set Q)) K' := by
    have h1 := SwapData.map (MulAut.conj q).toMonoidHom hsw (by
      rw [(MonoidHom.ker_eq_bot_iff _).mpr (MulAut.conj q).injective, inf_bot_eq]
      exact bot_le)
    rwa [map_inf _ _ _ (MulAut.conj q).injective, ← hT'eq, map_equiv_normalizer_eq] at h1
  intro Y hY hYn
  have hYnorm : Y.Normal := by
    have h := (normal_subgroupOf_iff_le_normalizer (le_top : Y ≤ ⊤)).mp hYn
    exact normalizer_eq_top_iff.mp (le_antisymm le_top h)
  let NQ := ↥(⊤ : Subgroup Q) ⧸ Y.subgroupOf ⊤
  let π : Q →* NQ :=
    (QuotientGroup.mk' (Y.subgroupOf ⊤)).comp (Subgroup.topEquiv (G := Q)).symm.toMonoidHom
  have hπsurj : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp (Subgroup.topEquiv (G := Q)).symm.surjective
  have hπker : π.ker = Y := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hx' : (Subgroup.topEquiv (G := Q)).symm x ∈ Y.subgroupOf ⊤ :=
        (QuotientGroup.eq_one_iff _).mp hx
      simpa [mem_subgroupOf] using hx'
    · intro hx
      exact (QuotientGroup.eq_one_iff _).mpr (by
        simpa [mem_subgroupOf] using hx)
  by_cases hFY : orbitClosure K T ≤ Y
  · have hN2 : IsPGroup 2 NQ := by
      have hFYker : orbitClosure K T ≤ π.ker := by rw [hπker]; exact hFY
      refine IsPGroup.of_surjective hQF2
        (QuotientGroup.lift (orbitClosure K T) π hFYker) ?_
      exact QuotientGroup.lift_surjective_of_surjective _ π hπsurj hFYker
    exact cfAutInFGroup_of_isPGroup Nat.prime_two hN2 n _
  · have hYleZ : Y ≤ orbitClosure K T ⊓ centralizer (orbitClosure K T : Set Q) :=
      (orbitClosure_le_or_le_inf_centralizer hO2 hK hT2 hKT hYnorm).resolve_left hFY
    by_cases hZY : orbitClosure K T ⊓ centralizer (orbitClosure K T : Set Q) ≤ Y
    · have hYZ : Y = orbitClosure K T ⊓ centralizer (orbitClosure K T : Set Q) :=
        le_antisymm hYleZ hZY
      have hZeq : (orbitClosure K T ⊓ centralizer (orbitClosure K T : Set Q)) =
          (center ↥(CFSG.layer Q)).map (CFSG.layer Q).subtype := by
        have hFeq : orbitClosure K T = CFSG.layer Q :=
          le_antisymm (orbitClosure_le_layer hK) (layer_le_orbitClosure hO2 hT2 hKT)
        rw [hFeq]
        ext x
        rw [mem_inf, CFSG.LocalCores.mem_map_center_iff]
      have hK'Z : K' ⊓ Y = (center ↥K').map K'.subtype := by
        rw [hYZ, hZeq]
        exact (CFSG.LocalCores.layer_center (G := Q)).2 K' hK'
      obtain ⟨hKbar, ⟨eKbar⟩⟩ :=
        isComponent_map_of_inf_eq_center π hπsurj hK' hπker hK'Z
      have hshapeBar : IsL3 ↥(K'.map π) n ∨ IsSp4 ↥(K'.map π) n :=
        hshape'.imp (LieModel.of_mulEquiv eKbar.symm) (LieModel.of_mulEquiv eKbar.symm)
      have hsimpleBar : IsSimpleGroup ↥(K'.map π) := by
        rcases hshapeBar with h | h
        · exact LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
        · exact LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
      have hS2bar : IsPGroup 2 (T'.map π) := IsPGroup.map hT'in.isPGroup π
      have hKTbar : orbitClosure (K'.map π) (T'.map π) ⊔ T'.map π = ⊤ := by
        have h1 : orbitClosure (K'.map π) (T'.map π) = (orbitClosure K' T').map π :=
          (orbitClosure_map π K' T').symm
        rw [h1, hFconj, ← Subgroup.map_sup, hFT', map_top_of_surjective π hπsurj]
      have hswBar : SwapData (T'.map π ⊓ normalizer ((K'.map π : Subgroup NQ) : Set NQ))
          (K'.map π) := by
        have h1 := SwapData.map π hsw' (by
          rw [hπker, hK'Z]
          exact map_center_le_normalizer inf_le_right)
        exact SwapData.mono h1 (le_inf (map_mono inf_le_left)
          ((map_mono inf_le_right).trans (le_normalizer_map π))) (hS2bar.to_le inf_le_left)
          inf_le_right
      have hres := cfAutInFGroup_of_component_swap hSp hL3 h410 hKbar hS2bar hKTbar
        hsimpleBar hshapeBar hswBar
      have hSbarEq : T'.map π =
          (T'.subgroupOf ⊤).map (QuotientGroup.mk' (Y.subgroupOf ⊤)) := by
        rw [show π = (QuotientGroup.mk' (Y.subgroupOf ⊤)).comp
          (Subgroup.topEquiv (G := Q)).symm.toMonoidHom from rfl, ← map_map]
        congr 1
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          simpa [mem_subgroupOf] using hy
        · intro hx
          exact ⟨(x : Q), hx, Subtype.ext rfl⟩
      rwa [hSbarEq] at hres
    · intro X hXn hXne hXmin hXnc L hL
      exfalso
      have hXtil_norm : (X.comap π).Normal := hXn.comap π
      have hZcomm : IsMulCommutative ↥(orbitClosure K T ⊓
          centralizer (orbitClosure K T : Set Q)) := by
        refine ⟨⟨fun a b => ?_⟩⟩
        exact Subtype.ext (mem_centralizer_iff.mp a.2.2 (b : Q) b.2.1).symm
      have hZmap_comm : IsMulCommutative ↥((orbitClosure K T ⊓
          centralizer (orbitClosure K T : Set Q)).map π) := by
        refine ⟨⟨fun a b => ?_⟩⟩
        obtain ⟨x, hx, hxa⟩ := mem_map.mp a.2
        obtain ⟨y, hy, hyb⟩ := mem_map.mp b.2
        have h := congrArg (fun z : ↥(orbitClosure K T ⊓
            centralizer (orbitClosure K T : Set Q)) => π (z : Q))
          (hZcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
        apply Subtype.ext
        show (a : NQ) * (b : NQ) = (b : NQ) * (a : NQ)
        rw [← hxa, ← hyb]
        simpa using h
      rcases orbitClosure_le_or_le_inf_centralizer hO2 hK hT2 hKT hXtil_norm with
        hFX | hXZ
      · have hZle : orbitClosure K T ⊓
            centralizer (orbitClosure K T : Set Q) ≤ X.comap π :=
          inf_le_left.trans hFX
        have hZmap_le : (orbitClosure K T ⊓
            centralizer (orbitClosure K T : Set Q)).map π ≤ X := by
          rw [← map_comap_eq_self_of_surjective hπsurj X]
          exact map_mono hZle
        have hZmap_ne : (orbitClosure K T ⊓
            centralizer (orbitClosure K T : Set Q)).map π ≠ ⊥ := by
          intro hbot
          apply hZY
          intro z hz
          have hzπ : π z ∈ (orbitClosure K T ⊓
              centralizer (orbitClosure K T : Set Q)).map π :=
            mem_map_of_mem π hz
          rw [hbot] at hzπ
          rw [← hπker, MonoidHom.mem_ker]
          exact mem_bot.mp hzπ
        have hZmap_norm : ((orbitClosure K T ⊓
            centralizer (orbitClosure K T : Set Q)).map π).Normal := by
          have : (orbitClosure K T).Normal := hFnorm
          exact (normal_inf_normal _ _).map π hπsurj
        rcases hXmin _ hZmap_norm hZmap_le with hbot | htop
        · exact hZmap_ne hbot
        · exact hXnc (htop ▸ hZmap_comm)
      · have hXle : X ≤ (orbitClosure K T ⊓
            centralizer (orbitClosure K T : Set Q)).map π := by
          rw [← map_comap_eq_self_of_surjective hπsurj X]
          exact map_mono hXZ
        refine hXnc ⟨⟨fun a b => ?_⟩⟩
        have hcomm := congrArg Subtype.val (hZmap_comm.is_comm.comm
          ⟨a, hXle a.2⟩ ⟨b, hXle b.2⟩)
        exact Subtype.ext (by simpa using hcomm)

theorem inFSq_sup_of_swap (h43c : W3Lem45_2Chief) (hSp : K_SwapSp4InF) (hL3 : K_SwapL3InF)
    (h410 : W4Lem4_10) {G : Type} [Group G] [Finite G] {H L T : Subgroup G} {n : ℕ}
    (hcomp : IsComponentOf L H) (hL2 : CFSG.pCore 2 ↥L = ⊥) (hsyl : IsSylowIn 2 T H)
    (hLT : L ⊔ T = H) (hshape : UC22.IsSL3 ↥L n ∨ IsSp4 ↥L n)
    (hsw : S17.SwapsParabolics (T ⊓ Subgroup.normalizer (L : Set G)) L) :
    WeakClosure81.InFSq n H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hLH, hsub, hq⟩ := hcomp
  have hTH : T ≤ H := hsyl.1
  let e0 : Bar2 L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hL2).trans QuotientGroup.quotientBot
  have hperf : ⁅L, L⁆ = L := by
    rw [← map_subtype_commutator, hq.1, ← MonoidHom.range_eq_map, range_subtype]
  have hcalC : L ∈ calC H := ⟨hsub, hperf, CFSG.Open.IsQuasisimple.of_mulEquiv e0 hq⟩
  let Kbar : Subgroup (Bar2 H) := (L.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
  let Tbar : Subgroup (Bar2 H) := (T.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
  have hKbar : CFSG.IsComponent Kbar := s13_barImage_isComponent hcalC
  have hTbar : IsSylowIn 2 Tbar ⊤ := isSylowIn_barImage hsyl
  have hgen : Kbar ⊔ Tbar = ⊤ := by
    have h := s13_barImage_sup (M := H) (A := L) (B := T) hLH hTH
    rw [hLT, s13_barImage_self] at h
    exact h.symm
  have hKT : orbitClosure Kbar Tbar ⊔ Tbar = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact sup_le ((le_orbitClosure Kbar Tbar).trans le_sup_left) le_sup_right
  have hO2 : pCoreOf 2 (⊤ : Subgroup (Bar2 H)) = ⊥ := by
    rw [CFSG.CGT.PushingUpLit.Glue.pCoreOf_top_eq, pCore_two_bar2_eq_bot]
  obtain ⟨e1, -⟩ := uc22p20d_bar2Equiv hLH hsub
  let eK : ↥L ≃* ↥Kbar := e0.symm.trans e1
  let eZ : (↥L ⧸ center ↥L) ≃* (↥Kbar ⧸ center ↥Kbar) :=
    QuotientGroup.congr (center ↥L) (center ↥Kbar) eK (map_center_eq _)
  have hshapeK : IsL3 (↥Kbar ⧸ center ↥Kbar) n ∨ IsSp4 (↥Kbar ⧸ center ↥Kbar) n := by
    rcases hshape with h | h
    · exact Or.inl (LieModel.of_mulEquiv eZ h.2)
    · right
      have hsimpleL : IsSimpleGroup ↥L :=
        LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
      have hnab : ∃ a b : ↥L, a * b ≠ b * a := by
        by_contra hc
        push Not at hc
        have : Group.IsPerfect ↥L := (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hq).1
        exact Group.IsPerfect.not_isMulCommutative ↥L ⟨⟨fun a b => hc a b⟩⟩
      have hZ : center ↥L = ⊥ := Vol2.Ch11.SecE3.center_eq_bot_of_simple hnab
      let e2 : ↥L ≃* (↥L ⧸ center ↥L) :=
        QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
      exact LieModel.of_mulEquiv (e2.trans eZ) h
  have hswG : SwapData (T ⊓ normalizer (L : Set G)) L := by
    have hTeq : (T ⊓ normalizer (L : Set G)) ⊓ L = T ⊓ L := by
      rw [inf_assoc, inf_eq_right.mpr le_normalizer]
    refine ⟨hsyl.isPGroup.to_le inf_le_left, inf_le_right, ?_, hsw⟩
    rw [hTeq]
    exact F6.isSylowIn_inf_of_isSubnormal hsub hsyl
  have hswH := SwapData.subgroupOf (H := H) (inf_le_left.trans hTH) hLH hswG
  have hOL : pCoreOf 2 L = ⊥ := by
    rw [CFSG.openPCoreOf_eq_map_pCore, hL2, Subgroup.map_bot]
  have hkerH : L.subgroupOf H ⊓ (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).ker ≤
      normalizer ((((T ⊓ normalizer (L : Set G)).subgroupOf H) ⊓ L.subgroupOf H :
        Subgroup ↥H) : Set ↥H) := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    have hxL : (x : G) ∈ L := mem_subgroupOf.mp hx.1
    have hxO : (x : G) ∈ pCoreOf 2 H := by
      have h1 := hx.2
      rw [← CFSG.openPCoreOf_subgroupOf 2 H] at h1
      exact mem_subgroupOf.mp h1
    have hxOL : (x : G) ∈ pCoreOf 2 L := by
      rw [CFSG.pCoreOf_eq_inf_pCoreOf_of_isSubnormal hsub]
      exact ⟨hxL, hxO⟩
    rw [hOL] at hxOL
    have hx1 : x = 1 := Subtype.ext (mem_bot.mp hxOL)
    rw [hx1]
    exact one_mem _
  have hswBar0 := SwapData.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) hswH hkerH
  have hswK : SwapData (Tbar ⊓ normalizer (Kbar : Set (Bar2 H))) Kbar :=
    SwapData.mono hswBar0 (le_inf (map_mono (subgroupOf_mono _ inf_le_left)) hswBar0.2.1)
      (hTbar.isPGroup.to_le inf_le_left) inf_le_right
  have hcf := compFactorAutInF_of_orbitClosure_swap hSp hL3 h410 hO2 hKbar hTbar hKT hshapeK
    hswK
  have hn : 1 ≤ n := by
    rcases hshape with h | h
    · exact (LieModel.admissible h.2).2.1
    · exact (LieModel.admissible h).2.1
  exact inFSq_of_components h43c hn hKbar hTbar hKT hcf

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
