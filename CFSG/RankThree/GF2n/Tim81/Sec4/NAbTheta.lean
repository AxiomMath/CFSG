module

public import CFSG.RankThree.GF2n.Tim81.Sec4.NAbZPK
public import CFSG.RankThree.GF2n.Tim81.Sec4.NAbTrivInter
public import CFSG.RankThree.GF2n.Tim81.Sec4.Sec45Shape
public import CFSG.RankThree.GF2n.Tim81.Sec2.NatSumRecog
public import CFSG.RankThree.GF2n.Tim81.Sec4.NAbZeta
public import CFSG.RankThree.GF2n.Tim81.Sec4.SecRepFixed

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open CFSG.QuasithinUnique.Setup.X7 CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.QuotMod
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G}

namespace RootHyp

variable {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
variable [Module (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))]

private theorem xOf_ne_bot' (h : RootHyp M V) : Tim79a.xOf V H ≠ ⊥ := fun hbot =>
  h.toHyp.ne_bot (le_bot_iff.mp (hbot ▸ le_xOf_self V H))

theorem commutator_kOf_eq_xOf
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x) (hL : IsL2OrSz V H)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ (le_refl (Tim79a.xOf V H))
      (Tim79a.H_le_normalizer_xOf V H)))
    (hWK' : Tim79a.xOf V H ≤ ⁅kOf V H, kOf V H⁆) :
    ⁅kOf V H, kOf V H⁆ = Tim79a.xOf V H := by
  refine le_antisymm ?_ hWK'
  have hD : Pc M V ⊓ conjSubgroup h₀ (Pc M V) ≤ Tim79a.xOf V H :=
    inf_conj_Pc_le_W0 (hW := hW) (W₀ := Tim79a.xOf V H) h hPH hVH hH hnM hK hnab hL
      le_rfl (Tim79a.H_le_normalizer_xOf V H) (xOf_ne_bot' (H := H) h) ψ hl horth
  obtain ⟨y, hyH, -, hVy, -⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  refine (commutator_kOf_le_sup h hPH hH hnM hK).trans ?_
  refine sup_le (sup_le (le_xOf_self V H) hD) ?_
  rw [hVy]
  exact conjSubgroup_le_xOf_of_mem (V := V) (H := H) hyH

private theorem sq_mem_xOf_of_mem_kOf_aux
    (h : RootHyp M V) (hPH : Pc M V ≤ H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V))
    (hK : KFactorization M V H h₀)
    (hcomm : ⁅kOf V H, kOf V H⁆ ≤ Tim79a.xOf V H) :
    ∀ k ∈ kOf V H, k * k ∈ Tim79a.xOf V H := by
  let D : Subgroup G :=
    { carrier := {x : G | x ∈ kOf V H ∧ x * x ∈ Tim79a.xOf V H}
      one_mem' := ⟨(kOf V H).one_mem, by rw [one_mul]; exact (Tim79a.xOf V H).one_mem⟩
      mul_mem' := by
        rintro x y ⟨hxK, hxW⟩ ⟨hyK, hyW⟩
        refine ⟨(kOf V H).mul_mem hxK hyK, ?_⟩
        have hc : ⁅x⁻¹, y⁆ ∈ Tim79a.xOf V H :=
          hcomm (Subgroup.commutator_mem_commutator ((kOf V H).inv_mem hxK) hyK)
        have hsq : (x * y) * (x * y) = (x * x) * ⁅x⁻¹, y⁆ * (y * y) := by
          rw [commutatorElement_def]; group
        rw [hsq]
        exact (Tim79a.xOf V H).mul_mem ((Tim79a.xOf V H).mul_mem hxW hc) hyW
      inv_mem' := by
        rintro x ⟨hxK, hxW⟩
        refine ⟨(kOf V H).inv_mem hxK, ?_⟩
        have hsq : x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
        rw [hsq]
        exact (Tim79a.xOf V H).inv_mem hxW }
  have hKD : kOf V H ≤ D := by
    obtain ⟨y, hyH, hPy, hVy, hHy⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
    have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
    have hP2y : IsPGroup 2 (conjSubgroup y (Pc M V)) :=
      hP2.map (MulAut.conj y).toMonoidHom
    have hA : Pc M V ⊓ kOf V H ≤ D := by
      rintro a ⟨haP, haK⟩
      exact ⟨haK, le_xOf_self V H (h.toHyp.frattini_Pc_le
        (by simpa [pow_two] using sq_mem_inSubgroup_frattini hP2 haP))⟩
    have hB : conjSubgroup h₀ (Pc M V) ⊓ kOf V H ≤ D := by
      rw [hPy]
      rintro b ⟨hbP, hbK⟩
      refine ⟨hbK, ?_⟩
      refine (conjSubgroup_le_xOf_of_mem (V := V) (H := H) hyH) ?_
      have hPhi : inSubgroup frattini (conjSubgroup y (Pc M V)) ≤ conjSubgroup y V :=
        frattini_conj_le hP2 h.toHyp.frattini_Pc_le y
      exact hPhi (by simpa [pow_two] using sq_mem_inSubgroup_frattini hP2y hbP)
    rw [hK]
    exact sup_le hA hB
  intro k hk
  exact (hKD hk).2

theorem sq_mem_xOf_of_mem_kOf
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x) (hL : IsL2OrSz V H)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ (le_refl (Tim79a.xOf V H))
      (Tim79a.H_le_normalizer_xOf V H)))
    (hWK' : Tim79a.xOf V H ≤ ⁅kOf V H, kOf V H⁆) :
    ∀ k ∈ kOf V H, k * k ∈ Tim79a.xOf V H :=
  sq_mem_xOf_of_mem_kOf_aux h hPH hH hK
    (commutator_kOf_eq_xOf (hW := hW) h hPH hVH hH hnM hK hnab hL ψ hl horth hWK').le

theorem frattini_kOf_eq_xOf
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x) (hL : IsL2OrSz V H)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ (le_refl (Tim79a.xOf V H))
      (Tim79a.H_le_normalizer_xOf V H)))
    (hWK' : Tim79a.xOf V H ≤ ⁅kOf V H, kOf V H⁆) :
    inSubgroup frattini (kOf V H) = Tim79a.xOf V H := by
  have hK' := commutator_kOf_eq_xOf (hW := hW) h hPH hVH hH hnM hK hnab hL ψ hl horth hWK'
  have hsq := sq_mem_xOf_of_mem_kOf (hW := hW) h hPH hVH hH hnM hK hnab hL ψ hl horth hWK'
  have hK2 : IsPGroup 2 (kOf V H) := isPGroup_kOf_of_factorization h hK
  have hcomm_le : ⁅kOf V H, kOf V H⁆ ≤ inSubgroup frattini (kOf V H) := by
    haveI : Fact (IsPGroup 2 ↥(kOf V H)) := ⟨hK2⟩
    have h := Subgroup.map_mono (f := (kOf V H).subtype)
      (commutator_le_frattini_of_isPGroup (p := 2) (R := ↥(kOf V H)))
    rw [Subgroup.map_subtype_commutator] at h
    simpa only [inSubgroup] using h
  have hWleK : Tim79a.xOf V H ≤ kOf V H := xOf_le_kOf h hPH hVH
  have hWnormal : ((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hWleK).mpr ?_
    exact fun k hk => Subgroup.centralizer_le_normalizer _ ((mem_kOf_iff.mp hk).2)
  have hPhi_le : inSubgroup frattini (kOf V H) ≤ Tim79a.xOf V H := by
    have h := CFSG.SectionRank.Ccomm.frattini_le_of_commutator_pow_mem
      (p := 2) (G := ↥(kOf V H)) ((Tim79a.xOf V H).subgroupOf (kOf V H))
      (fun a b => ?_) (fun a => ?_)
    · have hmap := Subgroup.map_mono (f := (kOf V H).subtype) h
      rw [Subgroup.map_subgroupOf_eq_of_le hWleK] at hmap
      simpa only [inSubgroup] using hmap
    · have := hK' ▸ Subgroup.commutator_mem_commutator a.2 b.2
      exact (Subgroup.mem_subgroupOf).mpr (hK'.symm ▸ this)
    · exact (Subgroup.mem_subgroupOf).mpr (by simpa [pow_two] using hsq a a.2)
  refine le_antisymm hPhi_le ?_
  rw [← hK']
  exact hcomm_le


section C22

variable {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
variable [Module (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))]
variable [((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal]

theorem kMod_subSec_sup_eq_top {h₀ : G}
    (hK : KFactorization M V H h₀) (hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H))
    [Module (ZMod 2) (SecMod hs)] :
    subSec hs (Pc M V ⊓ kOf V H) ⊔
      subSec hs (conjSubgroup h₀ (Pc M V) ⊓ kOf V H) = ⊤ := by
  have hsup := subSec_sup (N := kOf V H) (N₀ := Tim79a.xOf V H) hs
    (inf_le_right : Pc M V ⊓ kOf V H ≤ kOf V H)
    (inf_le_right : conjSubgroup h₀ (Pc M V) ⊓ kOf V H ≤ kOf V H)
  rw [← hsup, ← hK, subSec_self]

theorem kMod_subSec_inf_Pc_le_fixedSub
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    (hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H))
    [Module (ZMod 2) (SecMod hs)] :
    subSec hs (Pc M V ⊓ kOf V H) ≤
      fixedSub (repSec hs hs.comm SL(2, F) ψ) ((imgK V H (Pc M V)).map ψ) := by
  intro v hv
  obtain ⟨n, hn⟩ := (mem_subSec_iff hs).1 hv
  rw [← hn, CFSG.QuasithinUnique.Setup.X7.mem_fixedSub]
  rintro a ha
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨y, hyP, rfl⟩ := (mem_imgK_iff).mp hz
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hc : ⁅(n : G), (y : G)⁆ ∈ Tim79a.xOf V H :=
    le_xOf_self V H (h.toHyp.frattini_Pc_le
      (commutatorElement_mem_inSubgroup_frattini hP2 (Subgroup.mem_inf.mp n.2.1).1 hyP))
  exact (SecRepFixed.fixed_iff_commutator_mem (N := kOf V H) (N₀ := Tim79a.xOf V H)
    (hs := hs) (ψ := ψ) (hKsec := hs.comm) (z := ⟨y, hPH hyP⟩)
    (n := Subgroup.inclusion inf_le_right n)).mpr hc

theorem kMod_subSec_conj_inf_Pc_le_fixedSub
    (h : RootHyp M V) (hPH : Pc M V ≤ H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V))
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    (hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H))
    [Module (ZMod 2) (SecMod hs)] :
    subSec hs (conjSubgroup h₀ (Pc M V) ⊓ kOf V H) ≤
      fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V H (conjSubgroup h₀ (Pc M V))).map ψ) := by
  obtain ⟨y, hyH, hPy, hVy, hHy⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  intro v hv
  obtain ⟨n, hn⟩ := (mem_subSec_iff hs).1 hv
  rw [← hn, CFSG.QuasithinUnique.Setup.X7.mem_fixedSub]
  rintro a ha
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨y', hyP, rfl⟩ := (mem_imgK_iff).mp hz
  have hy'Py : (y' : G) ∈ conjSubgroup y (Pc M V) := by
    rw [hPy] at hyP
    exact hyP
  have hy'H : (y' : G) ∈ H := y'.2
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hP2h : IsPGroup 2 (conjSubgroup h₀ (Pc M V)) :=
    hP2.map (MulAut.conj h₀).toMonoidHom
  have hPhi : inSubgroup frattini (conjSubgroup h₀ (Pc M V)) ≤ Tim79a.xOf V H :=
    (frattini_conj_le hP2 h.toHyp.frattini_Pc_le h₀).trans (by
      rw [hVy]
      exact conjSubgroup_le_xOf_of_mem (V := V) (H := H) hyH)
  have hc : ⁅(n : G), (y' : G)⁆ ∈ Tim79a.xOf V H :=
    hPhi (commutatorElement_mem_inSubgroup_frattini hP2h
      (Subgroup.mem_inf.mp n.2.1).1 hyP)
  exact (SecRepFixed.fixed_iff_commutator_mem (N := kOf V H) (N₀ := Tim79a.xOf V H)
    (hs := hs) (ψ := ψ) (hKsec := hs.comm) (z := ⟨y', hy'H⟩)
    (n := Subgroup.inclusion inf_le_right n)).mpr hc

private theorem imgK_conj_inv_mul_ne_of_sl2
    (h : RootHyp M V) (hPH : Pc M V ≤ H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {x y : G} (hxP : x ∈ Pc M V) (hxK : x ∉ kOf V H)
    (hPy : conjSubgroup h₀ (Pc M V) = conjSubgroup y (Pc M V)) :
    imgK V H (conjSubgroup (x⁻¹ * y) (Pc M V)) ≠
      imgK V H (conjSubgroup y (Pc M V)) := by
  intro heq
  have hxH : x ∈ H := hPH hxP
  have hPyH : conjSubgroup y (Pc M V) ≤ H := by
    rw [← hPy, hH]
    exact le_sup_right
  have hleft : imgK V H (conjSubgroup (x⁻¹ * y) (Pc M V)) =
      conjSubgroup (piK V H ⟨x⁻¹, H.inv_mem hxH⟩)
        (imgK V H (conjSubgroup y (Pc M V))) := by
    rw [show conjSubgroup (x⁻¹ * y) (Pc M V) =
        conjSubgroup x⁻¹ (conjSubgroup y (Pc M V)) from by
      rw [CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup]]
    exact imgK_conjSubgroup (H.inv_mem hxH) hPyH
  have hfix : conjSubgroup (piK V H ⟨x⁻¹, H.inv_mem hxH⟩)
      (imgK V H (conjSubgroup y (Pc M V))) = imgK V H (conjSubgroup y (Pc M V)) := by
    rw [← hleft]
    exact heq
  have hnorm_inv : piK V H ⟨x⁻¹, H.inv_mem hxH⟩ ∈
      Subgroup.normalizer (imgK V H (conjSubgroup y (Pc M V)) : Set (HBar V H)) :=
    conjSubgroup_eq_self_iff.mp hfix
  have hxinv : piK V H ⟨x, hxH⟩ = (piK V H ⟨x⁻¹, H.inv_mem hxH⟩)⁻¹ := by
    rw [← map_inv]
    congr 1
    ext
    simp
  have hnorm : piK V H ⟨x, hxH⟩ ∈
      Subgroup.normalizer (imgK V H (conjSubgroup y (Pc M V)) : Set (HBar V H)) := by
    rw [hxinv]
    exact (Subgroup.normalizer _).inv_mem hnorm_inv
  have hmemP : piK V H ⟨x, hxH⟩ ∈ imgK V H (Pc M V) :=
    (mem_imgK_iff).mpr ⟨⟨x, hxH⟩, hxP, rfl⟩
  have himg : imgK V H (conjSubgroup h₀ (Pc M V)) =
      imgK V H (conjSubgroup y (Pc M V)) := congrArg (imgK V H) hPy
  have hbot : imgK V H (Pc M V) ⊓
      Subgroup.normalizer (imgK V H (conjSubgroup y (Pc M V)) : Set (HBar V H)) = ⊥ := by
    rw [← himg]
    exact inf_imgK_normalizer_eq_bot_of_sl2 h hPH hH hnM ψ
  have hmem : piK V H ⟨x, hxH⟩ ∈ (⊥ : Subgroup (HBar V H)) := by
    rw [← hbot]
    exact Subgroup.mem_inf.mpr ⟨hmemP, hnorm⟩
  exact hxK ((piK_eq_one_iff _).mp (Subgroup.mem_bot.mp hmem))

private theorem imgK_conj_inv_ne_of_sl2
    (h : RootHyp M V) (hPH : Pc M V ≤ H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {y' : G} (hy' : y' ∈ conjSubgroup h₀ (Pc M V)) (hy'K : y' ∉ kOf V H) :
    imgK V H (conjSubgroup y'⁻¹ (Pc M V)) ≠ imgK V H (Pc M V) := by
  intro heq
  have hy'H : y' ∈ H := by
    rw [hH]
    exact Subgroup.mem_sup_right hy'
  have hleft : imgK V H (conjSubgroup y'⁻¹ (Pc M V)) =
      conjSubgroup (piK V H ⟨y'⁻¹, H.inv_mem hy'H⟩) (imgK V H (Pc M V)) :=
    imgK_conjSubgroup (H.inv_mem hy'H) hPH
  have hfix : conjSubgroup (piK V H ⟨y'⁻¹, H.inv_mem hy'H⟩) (imgK V H (Pc M V)) =
      imgK V H (Pc M V) := by
    rw [← hleft]
    exact heq
  have hnorm_inv : piK V H ⟨y'⁻¹, H.inv_mem hy'H⟩ ∈
      Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H)) :=
    conjSubgroup_eq_self_iff.mp hfix
  have hy'inv : piK V H ⟨y', hy'H⟩ = (piK V H ⟨y'⁻¹, H.inv_mem hy'H⟩)⁻¹ := by
    rw [← map_inv]
    congr 1
    ext
    simp
  have hnorm : piK V H ⟨y', hy'H⟩ ∈
      Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H)) := by
    rw [hy'inv]
    exact (Subgroup.normalizer _).inv_mem hnorm_inv
  have hmemP' : piK V H ⟨y', hy'H⟩ ∈ imgK V H (conjSubgroup h₀ (Pc M V)) :=
    (mem_imgK_iff).mpr ⟨⟨y', hy'H⟩, hy', rfl⟩
  have hbot := imgK_conj_inf_normalizer_eq_bot_of_sl2 h hPH hH hnM ψ
  have hmem : piK V H ⟨y', hy'H⟩ ∈ (⊥ : Subgroup (HBar V H)) := by
    rw [← hbot]
    exact Subgroup.mem_inf.mpr ⟨hmemP', hnorm⟩
  exact hy'K ((piK_eq_one_iff _).mp (Subgroup.mem_bot.mp hmem))

private theorem mem_xOf_of_mem_conj_inf_kOf_of_commutator_mem
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ (le_refl (Tim79a.xOf V H))
      (Tim79a.H_le_normalizer_xOf V H)))
    {b x : G} (hb : b ∈ conjSubgroup h₀ (Pc M V) ⊓ kOf V H)
    (hxP : x ∈ Pc M V) (hxK : x ∉ kOf V H) (hbx : ⁅b, x⁆ ∈ Tim79a.xOf V H) :
    b ∈ Tim79a.xOf V H := by
  obtain ⟨y, hyH, hPy, -, hHy⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  have hbPy : b ∈ conjSubgroup y (Pc M V) := by
    have h := hb.1
    rwa [hPy] at h
  have hxH : x ∈ H := hPH hxP
  have hxb : x * b * x⁻¹ ∈ Tim79a.xOf V H ⊔ conjSubgroup y (Pc M V) := by
    have he : x * b * x⁻¹ = ⁅b, x⁆⁻¹ * b := by
      rw [commutatorElement_def]; group
    rw [he]
    exact Subgroup.mul_mem_sup ((Tim79a.xOf V H).inv_mem hbx) hbPy
  have hbconj : b ∈ conjSubgroup x⁻¹ (Tim79a.xOf V H ⊔ conjSubgroup y (Pc M V)) :=
    mem_conjSubgroup.mpr (by simpa using hxb)
  rw [conjSubgroup_sup,
    conjSubgroup_eq_self_iff.mpr (Tim79a.H_le_normalizer_xOf V H (H.inv_mem hxH)),
    CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup] at hbconj
  have hne := imgK_conj_inv_mul_ne_of_sl2 (h := h) (hPH := hPH) (hH := hH)
    (hnM := hnM) (ψ := ψ) hxP hxK hPy
  have hmain := inf_conj_Pc_sup_conjSubgroup_le_xOf_of_ne h hPH hVH hH hnM hK ψ hl
    (hW := hW) horth (g := x⁻¹ * y) (H.mul_mem (H.inv_mem hxH) hyH) (by
      simpa [hPy] using hne)
  exact hmain (Subgroup.mem_inf.mpr ⟨hb.1, hbconj⟩)

private theorem mem_xOf_of_mem_inf_kOf_of_commutator_mem
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ (le_refl (Tim79a.xOf V H))
      (Tim79a.H_le_normalizer_xOf V H)))
    {a y' : G} (ha : a ∈ Pc M V ⊓ kOf V H)
    (hy' : y' ∈ conjSubgroup h₀ (Pc M V)) (hy'K : y' ∉ kOf V H)
    (hay : ⁅a, y'⁆ ∈ Tim79a.xOf V H) : a ∈ Tim79a.xOf V H := by
  have hy'H : y' ∈ H := by
    rw [hH]
    exact Subgroup.mem_sup_right hy'
  have hya : y' * a * y'⁻¹ ∈ Tim79a.xOf V H ⊔ Pc M V := by
    have he : y' * a * y'⁻¹ = ⁅a, y'⁆⁻¹ * a := by
      rw [commutatorElement_def]; group
    rw [he]
    exact Subgroup.mul_mem_sup ((Tim79a.xOf V H).inv_mem hay) ha.1
  have ha' : a ∈ conjSubgroup y'⁻¹ (Tim79a.xOf V H ⊔ Pc M V) :=
    mem_conjSubgroup.mpr (by simpa using hya)
  rw [conjSubgroup_sup,
    conjSubgroup_eq_self_iff.mpr (Tim79a.H_le_normalizer_xOf V H (H.inv_mem hy'H))] at ha'
  have hne := imgK_conj_inv_ne_of_sl2 (h := h) (hPH := hPH) (hH := hH)
    (hnM := hnM) (ψ := ψ) hy' hy'K
  have hmain := inf_Pc_sup_conjSubgroup_le_xOf_of_ne h hPH hVH hH hnM hK ψ hl
    (hW := hW) horth (g := y'⁻¹) (H.inv_mem hy'H) hne
  exact hmain (Subgroup.mem_inf.mpr ⟨ha.1, ha'⟩)

theorem kMod_subSec_conj_inf_fixedSub_eq_bot
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ (le_refl (Tim79a.xOf V H))
      (Tim79a.H_le_normalizer_xOf V H)))
    (hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H))
    [Module (ZMod 2) (SecMod hs)] :
    subSec hs (conjSubgroup h₀ (Pc M V) ⊓ kOf V H) ⊓
      fixedSub (repSec hs hs.comm SL(2, F) ψ) ((imgK V H (Pc M V)).map ψ) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro v hv
  obtain ⟨hvB, hvfix⟩ := Submodule.mem_inf.mp hv
  obtain ⟨n, hn⟩ := (mem_subSec_iff hs).1 hvB
  obtain ⟨x, hxP, hxK⟩ := exists_mem_Pc_not_mem_kOf h hPH hH hnM
  have hxH : x ∈ H := hPH hxP
  have ha : ψ (piK V H ⟨x, hxH⟩) ∈ (imgK V H (Pc M V)).map ψ :=
    Subgroup.mem_map.mpr ⟨piK V H ⟨x, hxH⟩,
      (mem_imgK_iff).mpr ⟨⟨x, hxH⟩, hxP, rfl⟩, rfl⟩
  have hfix := mem_fixedSub.mp hvfix _ ha
  rw [← hn] at hfix
  have hbx : ⁅(n : G), x⁆ ∈ Tim79a.xOf V H :=
    (SecRepFixed.fixed_iff_commutator_mem (N := kOf V H) (N₀ := Tim79a.xOf V H)
      (hs := hs) (ψ := ψ) (hKsec := hs.comm) (z := ⟨x, hxH⟩)
      (n := Subgroup.inclusion inf_le_right n)).mp hfix
  have hbW := mem_xOf_of_mem_conj_inf_kOf_of_commutator_mem (hW := hW) h hPH hVH hH hnM
    hK ψ hl horth n.2.1 hxP hxK hbx
  rw [← hn, (SecMod.mk_eq_zero_iff hs _).mpr hbW]
  exact Submodule.zero_mem _

theorem kMod_subSec_inf_inf_fixedSub_eq_bot
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ (le_refl (Tim79a.xOf V H))
      (Tim79a.H_le_normalizer_xOf V H)))
    (hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H))
    [Module (ZMod 2) (SecMod hs)] :
    subSec hs (Pc M V ⊓ kOf V H) ⊓
      fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V H (conjSubgroup h₀ (Pc M V))).map ψ) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro v hv
  obtain ⟨hvA, hvfix⟩ := Submodule.mem_inf.mp hv
  obtain ⟨n, hn⟩ := (mem_subSec_iff hs).1 hvA
  obtain ⟨y', hy', hy'K⟩ := exists_mem_conj_not_mem_kOf h hH hnM
  have hy'H : y' ∈ H := by
    rw [hH]
    exact Subgroup.mem_sup_right hy'
  have ha : ψ (piK V H ⟨y', hy'H⟩) ∈
      (imgK V H (conjSubgroup h₀ (Pc M V))).map ψ :=
    Subgroup.mem_map.mpr ⟨piK V H ⟨y', hy'H⟩,
      (mem_imgK_iff).mpr ⟨⟨y', hy'H⟩, hy', rfl⟩, rfl⟩
  have hfix := mem_fixedSub.mp hvfix _ ha
  rw [← hn] at hfix
  have hay : ⁅(n : G), y'⁆ ∈ Tim79a.xOf V H :=
    (SecRepFixed.fixed_iff_commutator_mem (N := kOf V H) (N₀ := Tim79a.xOf V H)
      (hs := hs) (ψ := ψ) (hKsec := hs.comm) (z := ⟨y', hy'H⟩)
      (n := Subgroup.inclusion inf_le_right n)).mp hfix
  have haW := mem_xOf_of_mem_inf_kOf_of_commutator_mem (hW := hW) h hPH hVH hH hnM
    hK ψ hl horth n.2.1 hy' hy'K hay
  rw [← hn, (SecMod.mk_eq_zero_iff hs _).mpr haW]
  exact Submodule.zero_mem _

theorem fixedSub_repSec_kOf
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ (le_refl (Tim79a.xOf V H))
      (Tim79a.H_le_normalizer_xOf V H)))
    (hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H))
    [Module (ZMod 2) (SecMod hs)] :
    fixedSub (repSec hs hs.comm SL(2, F) ψ) ((imgK V H (Pc M V)).map ψ) =
      subSec hs (Pc M V ⊓ kOf V H) := by
  refine le_antisymm ?_ (kMod_subSec_inf_Pc_le_fixedSub h hPH ψ hs)
  intro v hv
  have hsup := kMod_subSec_sup_eq_top hK hs
  have hvsup : v ∈ subSec hs (Pc M V ⊓ kOf V H) ⊔
      subSec hs (conjSubgroup h₀ (Pc M V) ⊓ kOf V H) := by
    rw [hsup]
    exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hvsup
  have huFix : u ∈ fixedSub (repSec hs hs.comm SL(2, F) ψ)
      ((imgK V H (Pc M V)).map ψ) :=
    kMod_subSec_inf_Pc_le_fixedSub h hPH ψ hs hu
  have hwFix : w ∈ fixedSub (repSec hs hs.comm SL(2, F) ψ)
      ((imgK V H (Pc M V)).map ψ) := by
    have h := (fixedSub (repSec hs hs.comm SL(2, F) ψ)
      ((imgK V H (Pc M V)).map ψ)).sub_mem hv huFix
    have hw_eq : v - u = w := by rw [← huw]; abel
    rwa [hw_eq] at h
  have hwBot : w = 0 := by
    have hmem : w ∈ subSec hs (conjSubgroup h₀ (Pc M V) ⊓ kOf V H) ⊓
        fixedSub (repSec hs hs.comm SL(2, F) ψ) ((imgK V H (Pc M V)).map ψ) :=
      Submodule.mem_inf.mpr ⟨hw, hwFix⟩
    rw [kMod_subSec_conj_inf_fixedSub_eq_bot (hW := hW) h hPH hVH hH hnM hK ψ hl horth
      hs] at hmem
    simpa using hmem
  rw [← huw, hwBot, add_zero]
  exact hu

theorem fixedSub_conj_repSec_kOf
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ (le_refl (Tim79a.xOf V H))
      (Tim79a.H_le_normalizer_xOf V H)))
    (hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H))
    [Module (ZMod 2) (SecMod hs)] :
    fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V H (conjSubgroup h₀ (Pc M V))).map ψ) =
      subSec hs (conjSubgroup h₀ (Pc M V) ⊓ kOf V H) := by
  refine le_antisymm ?_ (kMod_subSec_conj_inf_Pc_le_fixedSub h hPH hH ψ hs)
  intro v hv
  have hsup := kMod_subSec_sup_eq_top hK hs
  have hvsup : v ∈ subSec hs (Pc M V ⊓ kOf V H) ⊔
      subSec hs (conjSubgroup h₀ (Pc M V) ⊓ kOf V H) := by
    rw [hsup]
    exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hvsup
  have hwFix : w ∈ fixedSub (repSec hs hs.comm SL(2, F) ψ)
      ((imgK V H (conjSubgroup h₀ (Pc M V))).map ψ) :=
    kMod_subSec_conj_inf_Pc_le_fixedSub h hPH hH ψ hs hw
  have huFix : u ∈ fixedSub (repSec hs hs.comm SL(2, F) ψ)
      ((imgK V H (conjSubgroup h₀ (Pc M V))).map ψ) := by
    have h := (fixedSub (repSec hs hs.comm SL(2, F) ψ)
      ((imgK V H (conjSubgroup h₀ (Pc M V))).map ψ)).sub_mem hv hwFix
    have hu_eq : v - w = u := by rw [← huw]; abel
    rwa [hu_eq] at h
  have huBot : u = 0 := by
    have hmem : u ∈ subSec hs (Pc M V ⊓ kOf V H) ⊓
        fixedSub (repSec hs hs.comm SL(2, F) ψ)
          ((imgK V H (conjSubgroup h₀ (Pc M V))).map ψ) :=
      Submodule.mem_inf.mpr ⟨hu, huFix⟩
    rw [kMod_subSec_inf_inf_fixedSub_eq_bot (hW := hW) h hPH hVH hH hnM hK ψ hl horth
      hs] at hmem
    simpa using hmem
  rw [← huw, huBot, zero_add]
  exact hw

theorem kMod_fixedSub_top_eq_bot
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ (le_refl (Tim79a.xOf V H))
      (Tim79a.H_le_normalizer_xOf V H)))
    (hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H))
    [Module (ZMod 2) (SecMod hs)] :
    fixedSub (repSec hs hs.comm SL(2, F) ψ) (⊤ : Subgroup SL(2, F)) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro v hv
  have hvA : v ∈ fixedSub (repSec hs hs.comm SL(2, F) ψ) ((imgK V H (Pc M V)).map ψ) :=
    fun a _ => hv a (Subgroup.mem_top a)
  have hvB : v ∈ fixedSub (repSec hs hs.comm SL(2, F) ψ)
      ((imgK V H (conjSubgroup h₀ (Pc M V))).map ψ) :=
    fun a _ => hv a (Subgroup.mem_top a)
  have hsup := kMod_subSec_sup_eq_top hK hs
  have hvsup : v ∈ subSec hs (Pc M V ⊓ kOf V H) ⊔
      subSec hs (conjSubgroup h₀ (Pc M V) ⊓ kOf V H) := by
    rw [hsup]
    exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hvsup
  have huFixA : u ∈ fixedSub (repSec hs hs.comm SL(2, F) ψ)
      ((imgK V H (Pc M V)).map ψ) :=
    kMod_subSec_inf_Pc_le_fixedSub h hPH ψ hs hu
  have hwFixA : w ∈ fixedSub (repSec hs hs.comm SL(2, F) ψ)
      ((imgK V H (Pc M V)).map ψ) := by
    have h := (fixedSub (repSec hs hs.comm SL(2, F) ψ)
      ((imgK V H (Pc M V)).map ψ)).sub_mem hvA huFixA
    have hw_eq : v - u = w := by rw [← huw]; abel
    rwa [hw_eq] at h
  have hwBot : w = 0 := by
    have hmem : w ∈ subSec hs (conjSubgroup h₀ (Pc M V) ⊓ kOf V H) ⊓
        fixedSub (repSec hs hs.comm SL(2, F) ψ) ((imgK V H (Pc M V)).map ψ) :=
      Submodule.mem_inf.mpr ⟨hw, hwFixA⟩
    rw [kMod_subSec_conj_inf_fixedSub_eq_bot (hW := hW) h hPH hVH hH hnM hK ψ hl horth
      hs] at hmem
    simpa using hmem
  have hvA' : v ∈ subSec hs (Pc M V ⊓ kOf V H) := by
    rw [← huw, hwBot, add_zero]
    exact hu
  have hmem : v ∈ subSec hs (Pc M V ⊓ kOf V H) ⊓
      fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V H (conjSubgroup h₀ (Pc M V))).map ψ) :=
    Submodule.mem_inf.mpr ⟨hvA', hvB⟩
  rw [kMod_subSec_inf_inf_fixedSub_eq_bot (hW := hW) h hPH hVH hH hnM hK ψ hl horth
    hs] at hmem
  simpa using hmem

theorem kMod_quad_repSec
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    (hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H))
    [Module (ZMod 2) (SecMod hs)] :
    ∀ a ∈ (imgK V H (Pc M V)).map ψ, ∀ b ∈ (imgK V H (Pc M V)).map ψ,
      (repSec hs hs.comm SL(2, F) ψ a - 1) ∘ₗ
        (repSec hs hs.comm SL(2, F) ψ b - 1) = 0 := by
  have hK_le_NP : kOf V H ≤ Subgroup.normalizer (Pc M V : Set G) :=
    (kOf_le_M h).trans h.toHyp.le_normalizer_Pc
  have hKP_le_P : ⁅kOf V H, Pc M V⁆ ≤ Pc M V :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hK_le_NP
  have hP_le_NK : Pc M V ≤ Subgroup.normalizer (kOf V H : Set G) :=
    hPH.trans (le_normalizer_kOf V H)
  have hPK_le_K : ⁅Pc M V, kOf V H⁆ ≤ kOf V H :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hP_le_NK
  have hKP : ⁅kOf V H, Pc M V⁆ ≤ Pc M V ⊓ kOf V H := by
    refine le_inf hKP_le_P ?_
    rw [Subgroup.commutator_comm]
    exact hPK_le_K
  intro a ha b hb
  obtain ⟨b', hb', hb''⟩ := Subgroup.mem_map.mp hb
  obtain ⟨z, hzP, hzy⟩ := (mem_imgK_iff).mp hb'
  rw [← hb'', ← hzy]
  refine LinearMap.ext fun w => ?_
  obtain ⟨n, rfl⟩ := SecMod.mk_surjective hs w
  have hd := SecRepFixed.repSec_sub_eq_mk (N := kOf V H) (N₀ := Tim79a.xOf V H)
    (hs := hs) (ψ := ψ) (hKsec := hs.comm) (z := z) (n := n)
  have hmem : repSec hs hs.comm SL(2, F) ψ (ψ (piK V H z)) (SecMod.mk hs n) -
      SecMod.mk hs n ∈ subSec hs (Pc M V ⊓ kOf V H) := by
    rw [hd]
    have hc : ⁅(n : G), (z : G)⁆ ∈ Pc M V ⊓ kOf V H :=
      hKP (Subgroup.commutator_mem_commutator n.2 hzP)
    exact SecRepFixed.mk_mem_subSec_of_mem (N := kOf V H) (N₀ := Tim79a.xOf V H)
      (hs := hs) (n := ⟨_, _⟩)
      (Subgroup.mem_inf.mpr ⟨(Pc M V).inv_mem hc.1, (kOf V H).inv_mem hc.2⟩)
  have hfix := kMod_subSec_inf_Pc_le_fixedSub h hPH ψ hs hmem
  rw [LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply]
  exact sub_eq_zero.mpr (mem_fixedSub.mp hfix a ha)

theorem kMod_fixedSub_sup_eq_top
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ (le_refl (Tim79a.xOf V H))
      (Tim79a.H_le_normalizer_xOf V H)))
    (hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H))
    [Module (ZMod 2) (SecMod hs)] :
    fixedSub (repSec hs hs.comm SL(2, F) ψ) ((imgK V H (Pc M V)).map ψ) ⊔
      fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V H (conjSubgroup h₀ (Pc M V))).map ψ) = ⊤ := by
  rw [fixedSub_repSec_kOf h hPH hVH hH hnM hK ψ hl horth hs,
    fixedSub_conj_repSec_kOf h hPH hVH hH hnM hK ψ hl horth hs,
    kMod_subSec_sup_eq_top hK hs]

theorem isNatSumModule_repSec_kOf
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ (le_refl (Tim79a.xOf V H))
      (Tim79a.H_le_normalizer_xOf V H))) :
    KModWNatSum V H ψ := by
  intro hs hmod
  letI := hmod
  obtain ⟨-, -, a, b, ha, hb, hne⟩ := imgK_map_sl2 h hPH hVH hH hnM ψ
  refine Sec2.isNatSumModule_of_fixedSub_conj (repSec hs hs.comm SL(2, F) ψ)
    (kMod_fixedSub_top_eq_bot (hW := hW) h hPH hVH hH hnM hK ψ hl horth hs) hne ?_ ?_
  · rw [← ha]
    exact kMod_quad_repSec h hPH ψ hs
  · rw [← ha, ← hb]
    exact kMod_fixedSub_sup_eq_top (hW := hW) h hPH hVH hH hnM hK ψ hl horth hs

end C22

private theorem xOf_le_inf_centralizer_kOf (h : RootHyp M V)
    (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) :
    Tim79a.xOf V H ≤ kOf V H ⊓ Subgroup.centralizer (kOf V H : Set G) := by
  refine le_inf (xOf_le_kOf h hPH hVH) ?_
  intro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact (Subgroup.mem_centralizer_iff.mp ((mem_kOf_iff.mp hk).2) w hw).symm

private theorem subSec_centralizer_invariant
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    (hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H))
    [hWnormal : ((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal]
    [hmod : Module (ZMod 2) (SecMod hs)]
    (Z : Subgroup G)
    (hZ : Z = kOf V H ⊓ Subgroup.centralizer (kOf V H : Set G)) :
    ∀ a : SL(2, F), ∀ v ∈ subSec hs Z,
      repSec hs hs.comm SL(2, F) ψ a v ∈ subSec hs Z := by
  intro a v hv
  subst hZ
  obtain ⟨w, hw⟩ := (mem_subSec_iff hs).mp hv
  let wK : ↥(kOf V H) := Subgroup.inclusion inf_le_right w
  have hw' : SecMod.mk hs wK = v := hw
  obtain ⟨g, hg⟩ := piK_surjective V H (ψ.symm a)
  have hag : a = ψ (piK V H g) := by
    rw [hg, MulEquiv.apply_symm_apply]
  rw [← hw', hag, repSec_apply_piK_mk hs hs.comm SL(2, F) ψ g wK]
  have hwZ : (w : G) ∈ kOf V H ⊓ Subgroup.centralizer (kOf V H : Set G) := w.2.1
  have hwK : (w : G) ∈ kOf V H := wK.2
  have hgK : g * (w : G) * g⁻¹ ∈ kOf V H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_kOf V H g.2) (w : G)).mp hwK
  have hgZ : g * (w : G) * g⁻¹ ∈
      kOf V H ⊓ Subgroup.centralizer (kOf V H : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨hgK, ?_⟩
    have hwC : (w : G) ∈ Subgroup.centralizer (kOf V H : Set G) :=
      (Subgroup.mem_inf.mp hwZ).2
    have hxconj : g * (w : G) * g⁻¹ ∈
        conjSubgroup (g : G) (Subgroup.centralizer (kOf V H : Set G)) := by
      rw [mem_conjSubgroup]
      simpa [show (g : G)⁻¹ * ((g : G) * (w : G) * (g : G)⁻¹) * (g : G) = (w : G)
        by group] using hwC
    have hcent := centralizer_conjSubgroup_eq (g : G) (kOf V H)
    rw [conjSubgroup_eq_self_iff.mpr (le_normalizer_kOf V H g.2)] at hcent
    rwa [← hcent] at hxconj
  refine (mem_subSec_iff hs).2 ⟨⟨g * (w : G) * g⁻¹, ?_⟩, ?_⟩
  · exact Subgroup.mem_inf.mpr ⟨hgZ, hgK⟩
  · exact congrArg (SecMod.mk hs) (Subtype.ext rfl)

private theorem exists_fixed_subSec_inf_Pc
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ (le_refl (Tim79a.xOf V H))
      (Tim79a.H_le_normalizer_xOf V H)))
    (hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H))
    [hWnormal : ((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal]
    [hmod : Module (ZMod 2) (SecMod hs)]
    (Z : Subgroup G)
    (hZne : subSec hs Z ≠ ⊥)
    (hZinv : ∀ a : SL(2, F), ∀ v ∈ subSec hs Z,
      repSec hs hs.comm SL(2, F) ψ a v ∈ subSec hs Z) :
    ∃ b ∈ subSec hs Z, b ≠ 0 ∧ b ∈ subSec hs (Pc M V ⊓ kOf V H) := by
  let X : Subgroup (SL(2, F)) := (imgK V H (Pc M V)).map ψ
  have hX2 : IsPGroup 2 X := by
    have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
    exact ((hP2.comap_subtype (K := H)).map (piK V H)).map ψ.toMonoidHom
  let U : Submodule (ZMod 2) (SecMod hs) := subSec hs Z
  haveI hUfd : FiniteDimensional (ZMod 2) U := by
    change Module.Finite (ZMod 2) U
    rw [Module.finite_def, ← Submodule.span_univ (R := ZMod 2) (M := U)]
    exact Submodule.fg_span (Set.finite_univ)
  haveI hUnt : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hZne
  letI : MulAction X U :=
    { smul := fun x v => (⟨repSec hs hs.comm SL(2, F) ψ x v.1, hZinv x v.1 v.2⟩ : U)
      one_smul := fun v => by
        apply Subtype.ext
        change repSec hs hs.comm SL(2, F) ψ 1 v.1 = v.1
        rw [map_one]
        rfl
      mul_smul := fun x y v => by
        apply Subtype.ext
        change repSec hs hs.comm SL(2, F) ψ (x * y) v.1 =
          repSec hs hs.comm SL(2, F) ψ x (repSec hs hs.comm SL(2, F) ψ y v.1)
        rw [map_mul]
        rfl }
  have hcard : 2 ∣ Nat.card U := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact dvd_pow_self 2 Module.finrank_pos.ne'
  obtain ⟨b, hbfix, hbne⟩ :=
    hX2.exists_fixed_point_of_prime_dvd_card_of_fixed_point U hcard (a := 0) (by
      rw [MulAction.mem_fixedPoints]
      intro x
      apply Subtype.ext
      change repSec hs hs.comm SL(2, F) ψ x 0 = 0
      rw [map_zero])
  have hb0 : b ≠ 0 := fun h => hbne h.symm
  have hbPc : b.1 ∈ fixedSub (repSec hs hs.comm SL(2, F) ψ)
      ((imgK V H (Pc M V)).map ψ) := by
    intro a ha
    have h : ((⟨a, ha⟩ : X) • b : U) = b := hbfix ⟨a, ha⟩
    exact congrArg Subtype.val h
  have hbA : b.1 ∈ subSec hs (Pc M V ⊓ kOf V H) := by
    rw [← fixedSub_repSec_kOf (hW := hW) h hPH hVH hH hnM hK ψ hl horth hs]
    exact hbPc
  exact ⟨b.1, b.2, fun hb => hb0 (Subtype.ext hb), hbA⟩

private theorem false_of_fixed_subSec_centralizer
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ (le_refl (Tim79a.xOf V H))
      (Tim79a.H_le_normalizer_xOf V H)))
    (hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H))
    [hWnormal : ((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal]
    [hmod : Module (ZMod 2) (SecMod hs)]
    (Z : Subgroup G)
    (hZ : Z = kOf V H ⊓ Subgroup.centralizer (kOf V H : Set G))
    (hWZ : Tim79a.xOf V H ≤ Z)
    {b : SecMod hs} (hbZ : b ∈ subSec hs Z) (hb0 : b ≠ 0)
    (hbA : b ∈ subSec hs (Pc M V ⊓ kOf V H)) :
    False := by
  subst hZ
  obtain ⟨a, ha⟩ := (mem_subSec_iff hs).mp hbA
  obtain ⟨n, hn⟩ := (mem_subSec_iff hs).mp hbZ
  have hna : (Subgroup.inclusion inf_le_right n : ↥(kOf V H)).val⁻¹ *
      (Subgroup.inclusion inf_le_right a : ↥(kOf V H)).val ∈ Tim79a.xOf V H := by
    refine (QuotMod.mk_eq_mk_iff (N := kOf V H) (N₀ := Tim79a.xOf V H) _ _).mp ?_
    exact hn.trans ha.symm
  have hWa : (n : G)⁻¹ * (a : G) ∈ Tim79a.xOf V H := by
    simpa using hna
  have hZmul : ∀ x ∈ kOf V H ⊓ Subgroup.centralizer (kOf V H : Set G),
      ∀ y ∈ kOf V H ⊓ Subgroup.centralizer (kOf V H : Set G),
      x * y ∈ kOf V H ⊓ Subgroup.centralizer (kOf V H : Set G) :=
    fun x hx y hy => Subgroup.mul_mem _ hx hy
  have haZ : (a : G) ∈ kOf V H ⊓ Subgroup.centralizer (kOf V H : Set G) := by
    have hnZ : (n : G) ∈ kOf V H ⊓ Subgroup.centralizer (kOf V H : Set G) := n.2.1
    have hwZ : (n : G)⁻¹ * (a : G) ∈
        kOf V H ⊓ Subgroup.centralizer (kOf V H : Set G) := hWZ hWa
    rw [show (a : G) = (n : G) * ((n : G)⁻¹ * (a : G)) by group]
    exact hZmul _ hnZ _ hwZ
  have haC : (a : G) ∈ Subgroup.centralizer ((Pc M V ⊓ kOf V H : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp haZ).2 x
      (Subgroup.mem_inf.mp hx).2
  have haPW : (a : G) ∈ Pc M V ⊓ Tim79a.xOf V H := by
    rw [← inf_kOf_inf_centralizer_eq_inf_xOf (hW := hW) h hPH hVH hH hnM hK hnab ψ hl horth]
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_inf.mp a.2.1).1, (Subgroup.mem_inf.mp a.2.1).2⟩, haC⟩
  have hnW : (n : G) ∈ Tim79a.xOf V H := by
    rw [show (n : G) = (a : G) * ((n : G)⁻¹ * (a : G))⁻¹ by group]
    exact (Tim79a.xOf V H).mul_mem haPW.2 ((Tim79a.xOf V H).inv_mem hWa)
  have hbzero : b = 0 := by
    rw [← hn, (SecMod.mk_eq_zero_iff hs _).mpr hnW]
  exact hb0 hbzero

private theorem inf_kOf_centralizer_eq_xOf_aux
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ (le_refl (Tim79a.xOf V H))
      (Tim79a.H_le_normalizer_xOf V H)))
    (hWK' : Tim79a.xOf V H ≤ ⁅kOf V H, kOf V H⁆)
    (hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H))
    [hWnormal : ((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal]
    [hmod : Module (ZMod 2) (SecMod hs)] :
    kOf V H ⊓ Subgroup.centralizer (kOf V H : Set G) = Tim79a.xOf V H := by
  have hcomm : ⁅kOf V H, kOf V H⁆ = Tim79a.xOf V H :=
    le_antisymm (Subgroup.commutator_le.mpr hs.comm) hWK'
  let Z : Subgroup G := kOf V H ⊓ Subgroup.centralizer (kOf V H : Set G)
  have hWZ : Tim79a.xOf V H ≤ Z := xOf_le_inf_centralizer_kOf h hPH hVH
  refine le_antisymm ?_ hWZ
  intro z hz
  by_contra hzW
  have hzK : z ∈ kOf V H := hz.1
  have hZne : subSec hs Z ≠ (⊥ : Submodule (ZMod 2) (SecMod hs)) := by
    intro hbot
    have hb : SecMod.mk hs ⟨z, hzK⟩ ∈ subSec hs Z :=
      SecRepFixed.mk_mem_subSec_of_mem (N := kOf V H) (N₀ := Tim79a.xOf V H)
        (hs := hs) (n := ⟨z, hzK⟩) hz
    rw [hbot] at hb
    have hb0 : SecMod.mk hs ⟨z, hzK⟩ = 0 := by simpa using hb
    exact hzW ((SecMod.mk_eq_zero_iff hs _).mp hb0)
  have hZinv : ∀ a : SL(2, F), ∀ v ∈ subSec hs Z,
      repSec hs hs.comm SL(2, F) ψ a v ∈ subSec hs Z :=
    subSec_centralizer_invariant (V := V) (H := H) ψ hs Z rfl
  obtain ⟨b, hbZ, hb0, hbA⟩ :=
    exists_fixed_subSec_inf_Pc (hW := hW) h hPH hVH hH hnM hK ψ hl horth hs Z hZne hZinv
  exact false_of_fixed_subSec_centralizer (hW := hW) h hPH hVH hH hnM hK hnab ψ hl horth hs
    Z rfl hWZ hbZ hb0 hbA

theorem inf_kOf_centralizer_eq_xOf
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x) (hL : IsL2OrSz V H)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ (le_refl (Tim79a.xOf V H))
      (Tim79a.H_le_normalizer_xOf V H)))
    (hWK' : Tim79a.xOf V H ≤ ⁅kOf V H, kOf V H⁆) :
    kOf V H ⊓ Subgroup.centralizer (kOf V H : Set G) = Tim79a.xOf V H := by
  have hsq : ∀ k ∈ kOf V H, k * k ∈ Tim79a.xOf V H :=
    sq_mem_xOf_of_mem_kOf (hW := hW) h hPH hVH hH hnM hK hnab hL ψ hl horth hWK'
  let hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H) :=
    { le := xOf_le_kOf h hPH hVH
      comm := by
        intro n hn n' hn'
        rw [show n * n' * n⁻¹ * n'⁻¹ = ⁅n, n'⁆ from rfl, ←
          commutator_kOf_eq_xOf (hW := hW) h hPH hVH hH hnM hK hnab hL ψ hl horth hWK']
        exact Subgroup.commutator_mem_commutator hn hn'
      conj := by
        intro g hg n hn
        exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_kOf V H hg) n).mp hn
      conj₀ := by
        intro g hg n hn
        exact (Subgroup.mem_normalizer_iff.mp (Tim79a.H_le_normalizer_xOf V H hg) n).mp hn }
  haveI hWnormal : ((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal := hs.normal
  exact inf_kOf_centralizer_eq_xOf_aux (hW := hW) h hPH hVH hH hnM hK hnab ψ hl horth
    hWK' hs (hWnormal := hs.normal) (hmod := SecMod.module hs hsq)

end RootHyp

end CFSG.RankThree.GF2n.Tim81
