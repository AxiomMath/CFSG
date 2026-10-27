module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma7_2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14
public import Mathlib.GroupTheory.Complement

import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem4_1

namespace CFSG
end CFSG
open CFSG

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

/-!
# Glauberman Lemma 6.3, step 7: identifying the centralizer

This module formalizes paper step 7 (equations (6.6) and the deduction
`C_Q(H) = H`) under the action-compatible `SL₂(p)` model supplied by step 6.
The public endpoint deliberately retains the original quotient representation,
its evaluation as conjugation, a coordinate equivalence, the quotient
isomorphism with `SL₂(p)`, and their intertwining equation.  This compatibility
is what identifies the central element `-I` with inversion on `H`.
-/

noncomputable section

namespace CFSG.Glauberman

universe u

open scoped Pointwise commutatorElement IsMulCommutative

private def sl2NegOne (p : ℕ) [Fact p.Prime] : qdSL p :=
  -(1 : qdSL p)

private theorem zmod_neg_one_ne_one {p : ℕ} [Fact p.Prime]
    (hpodd : p ≠ 2) : (-1 : ZMod p) ≠ 1 := by
  have htwo : (2 : ZMod p) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (ZMod p) Nat.prime_two hpodd
  intro h
  apply htwo
  calc
    (2 : ZMod p) = 1 + 1 := by norm_num
    _ = 1 + -1 := by rw [h]
    _ = 0 := add_neg_cancel 1

private theorem sl2NegOne_mem_center {p : ℕ} [Fact p.Prime] :
    sl2NegOne p ∈ Subgroup.center (qdSL p) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨-1, by simp, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2NegOne, Matrix.scalar_apply]

private theorem sl2NegOne_ne_one {p : ℕ} [Fact p.Prime]
    (hpodd : p ≠ 2) : sl2NegOne p ≠ 1 := by
  intro h
  have h00 := congrArg
    (fun A : qdSL p => (A : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0) h
  apply zmod_neg_one_ne_one hpodd
  simpa [sl2NegOne] using h00

private theorem sl2NegOne_sq {p : ℕ} [Fact p.Prime] :
    sl2NegOne p ^ 2 = 1 := by
  simp [sl2NegOne, pow_two]

private theorem sl2NegOne_toLin_apply {p : ℕ} [Fact p.Prime]
    (v : Fin 2 → ZMod p) :
    Matrix.SpecialLinearGroup.toLin' (sl2NegOne p) v = -v := by
  ext i
  fin_cases i <;>
    simp [sl2NegOne, Matrix.SpecialLinearGroup.toLin']

/-! Front half of step 7: pull the central `-I` subgroup back from the
natural `SL₂(p)` quotient, choose a Sylow `2`-subgroup in its preimage, and
apply Frattini. -/

set_option maxHeartbeats 800000 in
private theorem step7_exists_inverting_sylow
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {Q : Type u} [Group Q] [Finite Q]
    (H : Subgroup Q) (hHnormal : H.Normal)
    [IsMulCommutative H] [Module (ZMod p) (Additive H)]
    (coord : Additive H ≃ₗ[ZMod p] qdSpace p)
    (e : (Q ⧸ Subgroup.centralizer (H : Set Q)) ≃* qdSL p)
    (haction : ∀ (g : Q) (h : H),
      coord (Additive.ofMul (MulAut.conjNormal (H := H) g h)) =
        Matrix.SpecialLinearGroup.toLin'
          (e (QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) g))
          (coord (Additive.ofMul h))) :
    ∃ (T2 : Subgroup Q), IsPGroup 2 T2 ∧
      ∃ t : Q, t ∈ T2 ∧
        (∀ h : Q, h ∈ H → t * h * t⁻¹ = h⁻¹) ∧
        Subgroup.centralizer (H : Set Q) ⊔
          Subgroup.normalizer (T2 : Set Q) = ⊤ := by
  classical
  let : H.Normal := hHnormal
  let C : Subgroup Q := Subgroup.centralizer (H : Set Q)
  have hCnormal : C.Normal := by
    dsimp [C]
    exact Subgroup.normal_centralizer (H := H)
  let : C.Normal := hCnormal
  let q : Q →* Q ⧸ C := QuotientGroup.mk' C
  let qe : Q →* qdSL p := e.toMonoidHom.comp q
  let Z : Subgroup (qdSL p) := Subgroup.center (qdSL p)
  let T : Subgroup Q := Z.comap qe
  have hTnormal : T.Normal := by
    dsimp [T]
    exact Subgroup.Normal.comap (inferInstance : Z.Normal) qe
  let : T.Normal := hTnormal
  have hCleT : C ≤ T := by
    intro c hc
    change e (q c) ∈ Z
    have hqc : q c = 1 := (QuotientGroup.eq_one_iff c).2 hc
    rw [hqc, map_one]
    exact Z.one_mem
  let f : T →* Z :=
    (qe.comp T.subtype).codRestrict Z (by
      intro t
      exact t.2)
  have hfsurj : Function.Surjective f := by
    intro z
    rcases QuotientGroup.mk'_surjective C (e.symm (z : qdSL p)) with ⟨g, hg⟩
    have hgT : g ∈ T := by
      change e (q g) ∈ Z
      rw [hg, e.apply_symm_apply]
      exact z.2
    refine ⟨⟨g, hgT⟩, ?_⟩
    apply Subtype.ext
    change e (q g) = z
    rw [hg, e.apply_symm_apply]
  let S : Sylow 2 T := Classical.choice Sylow.nonempty
  let Smap : Sylow 2 Z := S.mapSurjective hfsurj
  have hneg : (-1 : ZMod p) ≠ 1 := zmod_neg_one_ne_one hpodd
  have hZcard : Nat.card Z = 2 := by
    simpa [Z] using
      (BenderSuzuki.External.huppert614_card_center_of_neg_one_ne_one hneg)
  have hZgroup : IsPGroup 2 Z := by
    apply IsPGroup.of_card (p := 2) (G := Z) (n := 1)
    simpa using hZcard
  have hZp : IsPGroup 2 (⊤ : Subgroup Z) :=
    hZgroup.of_equiv (Subgroup.topEquiv (G := Z)).symm
  have hSmapTop : (Smap : Subgroup Z) = ⊤ := by
    exact (Smap.3 hZp le_top).symm
  let z : Z := ⟨sl2NegOne p, sl2NegOne_mem_center⟩
  have hzSmap : z ∈ (S : Subgroup T).map f := by
    have hz : z ∈ (Smap : Subgroup Z) := by
      rw [hSmapTop]
      trivial
    simpa [Smap] using hz
  rcases Subgroup.mem_map.mp hzSmap with ⟨s, hsS, hfs⟩
  let T2 : Subgroup Q := (S : Subgroup T).map T.subtype
  have hT2p : IsPGroup 2 T2 := IsPGroup.map S.isPGroup' T.subtype
  let t : Q := ((s : T) : Q)
  have htT2 : t ∈ T2 :=
    Subgroup.mem_map.mpr ⟨s, hsS, rfl⟩
  have htImage : e (q t) = sl2NegOne p := by
    have hsval := congrArg Subtype.val hfs
    simpa [f, qe, t, z] using hsval
  have htInverts : ∀ h : Q, h ∈ H → t * h * t⁻¹ = h⁻¹ := by
    intro h hh
    let hH : H := ⟨h, hh⟩
    have hcoord := haction t hH
    rw [show QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) t = q t by rfl,
      htImage, sl2NegOne_toLin_apply] at hcoord
    have hadd :
        Additive.ofMul (MulAut.conjNormal (H := H) t hH) =
          -(Additive.ofMul hH) := by
      exact coord.injective (by simpa using hcoord)
    have hmul := congrArg (fun a : Additive H => (Additive.toMul a : H)) hadd
    have hsub : MulAut.conjNormal (H := H) t hH = hH⁻¹ := by
      simpa using hmul
    exact congrArg Subtype.val hsub
  have hT_eq : T = C ⊔ T2 := by
    apply le_antisymm
    · intro a haT
      let aT : T := ⟨a, haT⟩
      have hfa : f aT ∈ (Smap : Subgroup Z) := by
        rw [hSmapTop]
        trivial
      have hfaMap : f aT ∈ (S : Subgroup T).map f := by
        simpa [Smap] using hfa
      rcases Subgroup.mem_map.mp hfaMap with ⟨b, hbS, hfb⟩
      have habC : ((aT * b⁻¹ : T) : Q) ∈ C := by
        apply (QuotientGroup.eq_one_iff ((aT * b⁻¹ : T) : Q)).1
        have hfEq : f aT = f b := hfb.symm
        have hqEq : q (aT : Q) = q (b : Q) := by
          simpa [f, qe] using congrArg (fun z : Z => (z : qdSL p)) hfEq
        change q ((aT : Q) * (b : Q)⁻¹) = 1
        rw [map_mul, map_inv, hqEq, mul_inv_cancel]
      have hbT2 : ((b : T) : Q) ∈ T2 :=
        Subgroup.mem_map.mpr ⟨b, hbS, rfl⟩
      have habSup : ((aT * b⁻¹ : T) : Q) * ((b : T) : Q) ∈ C ⊔ T2 :=
        (C ⊔ T2).mul_mem
          ((le_sup_left : C ≤ C ⊔ T2) habC)
          ((le_sup_right : T2 ≤ C ⊔ T2) hbT2)
      simpa [aT] using habSup
    · exact sup_le hCleT (Subgroup.map_subtype_le (S : Subgroup T))
  have hFr : Subgroup.normalizer (T2 : Set Q) ⊔ T = ⊤ := by
    simpa [T2] using (Sylow.normalizer_sup_eq_top (N := T) S)
  have hCNtop : C ⊔ Subgroup.normalizer (T2 : Set Q) = ⊤ := by
    have hFr' := hFr
    rw [hT_eq] at hFr'
    have hT2leN : T2 ≤ Subgroup.normalizer (T2 : Set Q) := T2.le_normalizer
    have hFr'' :
        (Subgroup.normalizer (T2 : Set Q) ⊔ T2) ⊔ C = ⊤ := by
      calc
        (Subgroup.normalizer (T2 : Set Q) ⊔ T2) ⊔ C =
            Subgroup.normalizer (T2 : Set Q) ⊔ (T2 ⊔ C) := sup_assoc _ _ _
        _ = Subgroup.normalizer (T2 : Set Q) ⊔ (C ⊔ T2) := by
          rw [sup_comm T2 C]
        _ = ⊤ := hFr'
    rw [sup_eq_left.mpr hT2leN] at hFr''
    simpa [sup_comm] using hFr''
  exact ⟨T2, hT2p, t, htT2, htInverts, hCNtop⟩

/-! This is the exact strengthening needed from step 6 in the representation
language already used by `minimal_bad_witness_lemma6_2_data_probe`: retain the
evaluation theorem and return an `SL₂(p)` equivalence induced by the same
representation, not an unrelated abstract group equivalence. -/

private theorem step7_exists_inverting_sylow_of_compatible_rep
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {Q : Type u} [Group Q] [Finite Q]
    (H : Subgroup Q) (hHnormal : H.Normal)
    [IsMulCommutative H] [Module (ZMod p) (Additive H)]
    (rho : Q ⧸ Subgroup.centralizer (H : Set Q) →*
      LinearMap.GeneralLinearGroup (ZMod p) (Additive H))
    (hrho_eval : ∀ (g : Q) (v : Additive H),
      Additive.toMul
          (((rho (QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) g) :
            Additive H →ₗ[ZMod p] Additive H) v)) =
        MulAut.conjNormal (H := H) g (Additive.toMul v))
    (coord : Additive H ≃ₗ[ZMod p] qdSpace p)
    (e : (Q ⧸ Subgroup.centralizer (H : Set Q)) ≃* qdSL p)
    (hintertwine :
      ∀ (g : Q ⧸ Subgroup.centralizer (H : Set Q)) (v : Additive H),
        coord (((rho g : Additive H →ₗ[ZMod p] Additive H) v)) =
          Matrix.SpecialLinearGroup.toLin' (e g) (coord v)) :
    ∃ (T2 : Subgroup Q), IsPGroup 2 T2 ∧
      ∃ t : Q, t ∈ T2 ∧
        (∀ h : Q, h ∈ H → t * h * t⁻¹ = h⁻¹) ∧
        Subgroup.centralizer (H : Set Q) ⊔
          Subgroup.normalizer (T2 : Set Q) = ⊤ := by
  apply step7_exists_inverting_sylow hpodd H hHnormal coord e
  intro g h
  have heval := hrho_eval g (Additive.ofMul h)
  have heval' :
      Additive.ofMul (MulAut.conjNormal (H := H) g h) =
        ((rho (QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) g) :
          Additive H →ₗ[ZMod p] Additive H) (Additive.ofMul h)) := by
    have := congrArg Additive.ofMul heval.symm
    simpa using this
  rw [heval']
  exact hintertwine _ _

/-! The purely group-theoretic back half of paper step 7.  The preceding
`SL₂`/Frattini work is summarized by `N(T₂) ⋁ H = Q` and by a chosen
element of `T₂` acting as inversion on `H`. -/

private theorem step7_internal_decomposition
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {Q : Type u} [Group Q] [Finite Q]
    (H : Subgroup Q) (hHnormal : H.Normal) (hHp : IsPGroup p H)
    (hHleC : H ≤ Subgroup.centralizer (H : Set Q))
    (hCp : IsPGroup p (Subgroup.centralizer (H : Set Q)))
    (T2 : Subgroup Q) (hT2p : IsPGroup 2 T2)
    (t : Q) (htT2 : t ∈ T2)
    (hinverts : ∀ h : Q, h ∈ H → t * h * t⁻¹ = h⁻¹)
    (htop : Subgroup.normalizer (T2 : Set Q) ⊔ H = ⊤) :
    let C : Subgroup Q := Subgroup.centralizer (H : Set Q)
    let N : Subgroup Q := Subgroup.normalizer (T2 : Set Q)
    let E : Subgroup Q := C ⊓ N
    E.Normal ∧ E ⊓ H = ⊥ ∧ C = E ⊔ H := by
  classical
  let C : Subgroup Q := Subgroup.centralizer (H : Set Q)
  let N : Subgroup Q := Subgroup.normalizer (T2 : Set Q)
  let E : Subgroup Q := C ⊓ N
  have hCnormal : C.Normal := by
    dsimp [C]
    exact Subgroup.normal_centralizer (H := H)
  let : C.Normal := hCnormal
  have hN_norm_E : N ≤ Subgroup.normalizer (E : Set Q) := by
    have hN_norm_C : N ≤ Subgroup.normalizer (C : Set Q) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hCnormal]
      exact le_top
    exact (le_inf hN_norm_C N.le_normalizer).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := C) (K := N))
  have hH_cent_E : H ≤ Subgroup.centralizer (E : Set Q) := by
    intro h hh
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have heC : e ∈ C := he.1
    exact (Subgroup.mem_centralizer_iff.mp heC h hh).symm
  have hH_norm_E : H ≤ Subgroup.normalizer (E : Set Q) :=
    hH_cent_E.trans (Subgroup.centralizer_le_normalizer (E : Set Q))
  have hE_normalizer_top : Subgroup.normalizer (E : Set Q) = ⊤ := by
    apply top_unique
    rw [← htop]
    exact sup_le hN_norm_E hH_norm_E
  have hEnormal : E.Normal :=
    Subgroup.normalizer_eq_top_iff.mp hE_normalizer_top
  have hcomm_le_C : ⁅E, T2⁆ ≤ C := by
    have hT2_norm_C : T2 ≤ Subgroup.normalizer (C : Set Q) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hCnormal]
      exact le_top
    exact (Subgroup.commutator_mono (inf_le_left : E ≤ C) le_rfl).trans
      ((Subgroup.le_normalizer_iff_commutator_le_left
        (H := T2) (K := C)).mp hT2_norm_C)
  have hcomm_le_T2 : ⁅E, T2⁆ ≤ T2 :=
    (Subgroup.le_normalizer_iff_commutator_le_right
      (H := E) (K := T2)).mp (inf_le_right : E ≤ N)
  have hCT2 : C ⊓ T2 = ⊥ := by
    exact (IsPGroup.disjoint_of_ne p 2 hpodd C T2 hCp hT2p).eq_bot
  have hcomm_bot : ⁅E, T2⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact le_inf hcomm_le_C hcomm_le_T2 |>.trans (le_of_eq hCT2)
  have hEinfH : E ⊓ H = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro h hh
    rw [Subgroup.mem_bot]
    have hhE : h ∈ E := hh.1
    have hhH : h ∈ H := hh.2
    have hhcent : h ∈ Subgroup.centralizer (T2 : Set Q) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm_bot) hhE
    have hcommute : t * h = h * t :=
      Subgroup.mem_centralizer_iff.mp hhcent t htT2
    have hconj : t * h * t⁻¹ = h := by
      rw [hcommute]
      group
    have hhinv : h = h⁻¹ := hconj.symm.trans (hinverts h hhH)
    have hhsq : h ^ 2 = 1 := by
      calc
        h ^ 2 = h * h := pow_two h
        _ = h⁻¹ * h := congrArg (fun z : Q => z * h) hhinv
        _ = 1 := by simp
    exact eq_one_of_mem_pGroup_sq_eq_one hpodd H hHp hhH hhsq
  have hCeq : C = E ⊔ H := by
    apply le_antisymm
    · intro c hc
      have hcTop : c ∈ N ⊔ H := by rw [htop]; trivial
      rcases (Subgroup.mem_sup_of_normal_right (s := N) (t := H)).mp hcTop with
        ⟨n, hnN, h, hhH, hnh⟩
      have hnC : n ∈ C := by
        have hn : n = c * h⁻¹ := by
          calc
            n = (n * h) * h⁻¹ := by group
            _ = c * h⁻¹ := by rw [hnh]
        rw [hn]
        exact C.mul_mem hc (C.inv_mem (hHleC hhH))
      rw [← hnh]
      exact (E ⊔ H).mul_mem
        ((le_sup_left : E ≤ E ⊔ H) ⟨hnC, hnN⟩)
        ((le_sup_right : H ≤ E ⊔ H) hhH)
    · exact sup_le inf_le_left hHleC
  exact ⟨hEnormal, hEinfH, hCeq⟩

private theorem quotient_centralizer_comap_eq_of_disjoint
    {Q : Type u} [Group Q]
    (H : Subgroup Q) (hHnormal : H.Normal)
    (E : Subgroup Q) (hEnormal : E.Normal)
    (hEH : E ⊓ H = ⊥) :
    let q : Q →* Q ⧸ E := QuotientGroup.mk' E
    (Subgroup.centralizer ((H.map q : Subgroup (Q ⧸ E)) : Set (Q ⧸ E))).comap q =
      Subgroup.centralizer (H : Set Q) := by
  classical
  let : H.Normal := hHnormal
  let : E.Normal := hEnormal
  let q : Q →* Q ⧸ E := QuotientGroup.mk' E
  let Hbar : Subgroup (Q ⧸ E) := H.map q
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hqh : q h ∈ Hbar := Subgroup.mem_map.mpr ⟨h, hh, rfl⟩
    have hqcomm : q h * q g = q g * q h :=
      Subgroup.mem_centralizer_iff.mp hg (q h) hqh
    have hqeq : q (h * g) = q (g * h) := by simpa using hqcomm
    have hdE : (h * g) / (g * h) ∈ E :=
      QuotientGroup.eq_iff_div_mem.mp hqeq
    have hdH : (h * g) / (g * h) ∈ H := by
      have hmem : ⁅h, g⁆ ∈ ⁅H, Subgroup.zpowers g⁆ :=
        Subgroup.commutator_mem_commutator hh (Subgroup.mem_zpowers g)
      have hle : ⁅H, Subgroup.zpowers g⁆ ≤ H :=
        Subgroup.commutator_le_left (H₁ := H) (H₂ := Subgroup.zpowers g)
      simpa [div_eq_mul_inv, commutatorElement_def, mul_assoc] using hle hmem
    have hdOne : (h * g) / (g * h) = 1 := by
      have hd : (h * g) / (g * h) ∈ E ⊓ H := ⟨hdE, hdH⟩
      rw [hEH] at hd
      simpa using hd
    exact div_eq_one.mp hdOne
  · intro g hg
    change q g ∈ Subgroup.centralizer (Hbar : Set (Q ⧸ E))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨h, hh, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp hg h hh
    simpa using congrArg q hcomm

private theorem normal_ambient_quotient_core_membership
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (H : Subgroup Q) (hHnormal : H.Normal)
    (x : Q) (hx : x ∈ Subgroup.normalizer (H : Set Q)) :
    QuotientGroup.mk'
          ((Subgroup.centralizer (H : Set Q)).subgroupOf
            (Subgroup.normalizer (H : Set Q))) ⟨x, hx⟩ ∈
        pCore p ((Subgroup.normalizer (H : Set Q)) ⧸
          (Subgroup.centralizer (H : Set Q)).subgroupOf
            (Subgroup.normalizer (H : Set Q))) ↔
      QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) x ∈
        pCore p (Q ⧸ Subgroup.centralizer (H : Set Q)) := by
  classical
  let N : Subgroup Q := Subgroup.normalizer (H : Set Q)
  let C : Subgroup Q := Subgroup.centralizer (H : Set Q)
  have hNtop : N = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hHnormal
  let eN : N ≃* Q :=
    (MulEquiv.subgroupCongr hNtop).trans
      (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q)
  have hCmap : (C.subgroupOf N).map eN.toMonoidHom = C := by
    ext z
    constructor
    · rintro ⟨n, hn, rfl⟩
      have hnC : ((n : N) : Q) ∈ C := Subgroup.mem_subgroupOf.mp hn
      simpa [eN, MulEquiv.subgroupCongr_apply] using hnC
    · intro hz
      have hzN : z ∈ N := by rw [hNtop]; simp
      let n : N := ⟨z, hzN⟩
      refine ⟨n, Subgroup.mem_subgroupOf.mpr hz, ?_⟩
      simp [eN, n, MulEquiv.subgroupCongr_apply]
  let e : N ⧸ C.subgroupOf N ≃* Q ⧸ C :=
    QuotientGroup.congr
      (G := N) (H := Q) (G' := C.subgroupOf N) (H' := C) eN hCmap
  have he_mk :
      e (QuotientGroup.mk' (C.subgroupOf N) ⟨x, hx⟩) =
        QuotientGroup.mk' C x := by
    rfl
  have hcoreMap : (pCore p (N ⧸ C.subgroupOf N)).map e.toMonoidHom =
      pCore p (Q ⧸ C) :=
    pCore_map_iso (G := N ⧸ C.subgroupOf N) (G' := Q ⧸ C) (p := p) e
  constructor
  · intro hlocal
    have hmap : e (QuotientGroup.mk' (C.subgroupOf N) ⟨x, hx⟩) ∈
        (pCore p (N ⧸ C.subgroupOf N)).map e.toMonoidHom :=
      Subgroup.mem_map_of_mem e.toMonoidHom hlocal
    rw [hcoreMap, he_mk] at hmap
    simpa [N, C] using hmap
  · intro hambient
    have hambient' : QuotientGroup.mk' C x ∈ pCore p (Q ⧸ C) := by
      simpa [C] using hambient
    rw [← hcoreMap] at hambient'
    rcases Subgroup.mem_map.mp hambient' with ⟨z, hz, hzeq⟩
    have hzorig : z = QuotientGroup.mk' (C.subgroupOf N) ⟨x, hx⟩ := by
      apply e.injective
      exact hzeq.trans he_mk.symm
    simpa [N, C, hzorig] using hz

private theorem quotient_core_ne_and_not_pStableLocal_of_disjoint_central_factor
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (H : Subgroup Q) (hHnormal : H.Normal) (hHp : IsPGroup p H)
    (hHne : H ≠ ⊥)
    (E : Subgroup Q) (hEnormal : E.Normal)
    (hEH : E ⊓ H = ⊥)
    (x : Q)
    (hcomm : ⁅⁅H, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥)
    (hxout :
      QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) x ∉
        pCore p (Q ⧸ Subgroup.centralizer (H : Set Q))) :
    pCore p (Q ⧸ E) ≠ ⊥ ∧ ¬ pStableLocal p (Q ⧸ E) := by
  classical
  let : H.Normal := hHnormal
  let : E.Normal := hEnormal
  let C : Subgroup Q := Subgroup.centralizer (H : Set Q)
  let q : Q →* Q ⧸ E := QuotientGroup.mk' E
  let Hbar : Subgroup (Q ⧸ E) := H.map q
  let Cbar : Subgroup (Q ⧸ E) :=
    Subgroup.centralizer (Hbar : Set (Q ⧸ E))
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective E
  have hHbarNormal : Hbar.Normal :=
    Subgroup.Normal.map hHnormal q hqsurj
  let : Hbar.Normal := hHbarNormal
  have hHbarp : IsPGroup p Hbar := IsPGroup.map hHp q
  have hHbarne : Hbar ≠ ⊥ := by
    intro hbarbot
    have hleE : H ≤ E := by
      simpa [Hbar, q, QuotientGroup.ker_mk'] using
        (Subgroup.map_eq_bot_iff (f := q) (H := H)).mp hbarbot
    have hHE : H ⊓ E = H := inf_eq_left.mpr hleE
    have hHEbot : H ⊓ E = ⊥ := by simpa [inf_comm] using hEH
    apply hHne
    exact hHE.symm.trans hHEbot
  have hcoreNe : pCore p (Q ⧸ E) ≠ ⊥ := by
    intro hcorebot
    apply hHbarne
    apply le_antisymm ?_ bot_le
    have hle : Hbar ≤ pCore p (Q ⧸ E) := le_sSup ⟨hHbarNormal, hHbarp⟩
    rw [hcorebot] at hle
    exact hle
  have hcommbar :
      ⁅⁅Hbar, Subgroup.zpowers (q x)⁆, Subgroup.zpowers (q x)⁆ = ⊥ := by
    have hmap := congrArg (fun K : Subgroup Q => K.map q) hcomm
    simpa [Hbar, Subgroup.map_commutator, MonoidHom.map_zpowers] using hmap
  have hcomap : Cbar.comap q = C := by
    simpa [Cbar, Hbar, C, q] using
      quotient_centralizer_comap_eq_of_disjoint H hHnormal E hEnormal hEH
  let theta : Q →* (Q ⧸ E) ⧸ Cbar :=
    (QuotientGroup.mk' Cbar).comp q
  have hthetaSurj : Function.Surjective theta :=
    (QuotientGroup.mk'_surjective Cbar).comp hqsurj
  have hker : C = theta.ker := by
    ext g
    change g ∈ C ↔ QuotientGroup.mk' Cbar (q g) = 1
    constructor
    · intro hgC
      apply (QuotientGroup.eq_one_iff (N := Cbar) (x := q g)).2
      have hgComap : g ∈ Cbar.comap q := by simpa [hcomap] using hgC
      exact hgComap
    · intro hgOne
      have hgCbar : q g ∈ Cbar :=
        (QuotientGroup.eq_one_iff (N := Cbar) (x := q g)).1 hgOne
      have hgComap : g ∈ Cbar.comap q := hgCbar
      simpa [hcomap] using hgComap
  let e : Q ⧸ C ≃* (Q ⧸ E) ⧸ Cbar :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective theta hthetaSurj)
  have he_mk :
      e (QuotientGroup.mk' C x) = QuotientGroup.mk' Cbar (q x) := by
    rfl
  refine ⟨hcoreNe, ?_⟩
  intro hstableLocal
  have hxNorm : q x ∈ Subgroup.normalizer (Hbar : Set (Q ⧸ E)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hHbarNormal]
    trivial
  have hcondition : (pPrimeCore p (Q ⧸ E) ⊔ Hbar).Normal :=
    Subgroup.sup_normal (pPrimeCore p (Q ⧸ E)) Hbar
  have htargetLocal :=
    hstableLocal Hbar hHbarp hcondition (q x) hxNorm hcommbar
  have htarget : QuotientGroup.mk' Cbar (q x) ∈
      pCore p ((Q ⧸ E) ⧸ Cbar) := by
    simpa [Cbar] using
      (normal_ambient_quotient_core_membership
        Hbar hHbarNormal (q x) hxNorm).mp htargetLocal
  have hcoreMap :
      (pCore p (Q ⧸ C)).map e.toMonoidHom =
        pCore p ((Q ⧸ E) ⧸ Cbar) :=
    pCore_map_iso (G := Q ⧸ C) (G' := (Q ⧸ E) ⧸ Cbar) (p := p) e
  rw [← hcoreMap] at htarget
  rcases Subgroup.mem_map.mp htarget with ⟨z, hz, hzeq⟩
  have hzorig : z = QuotientGroup.mk' C x := by
    apply e.injective
    exact hzeq.trans he_mk.symm
  apply hxout
  simpa [C, hzorig] using hz

private theorem double_commutator_zpowers_of_central_factor
    {Q : Type u} [Group Q]
    (H : Subgroup Q) (hHnormal : H.Normal)
    {c x y : Q}
    (hc : c ∈ Subgroup.centralizer (H : Set Q))
    (hcy : c * y = x)
    (hcommX :
      ⁅⁅H, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥) :
    ⁅⁅H, Subgroup.zpowers y⁆, Subgroup.zpowers y⁆ = ⊥ := by
  let : H.Normal := hHnormal
  have hphi :
      MulAut.conjNormal (H := H) x = MulAut.conjNormal (H := H) y := by
    ext h
    have hyh : y * (h : Q) * y⁻¹ ∈ H :=
      hHnormal.conj_mem (h : Q) h.2 y
    have hccomm : (y * (h : Q) * y⁻¹) * c =
        c * (y * (h : Q) * y⁻¹) :=
      Subgroup.mem_centralizer_iff.mp hc _ hyh
    simp only [MulAut.conjNormal_apply]
    calc
      x * (h : Q) * x⁻¹ =
          c * (y * (h : Q) * y⁻¹) * c⁻¹ := by rw [← hcy]; group
      _ = y * (h : Q) * y⁻¹ := by rw [← hccomm]; group
  have hphiZpow (n : ℤ) :
      MulAut.conjNormal (H := H) (x ^ n) =
        MulAut.conjNormal (H := H) (y ^ n) := by
    simpa using congrArg (fun a : MulAut H => a ^ n) hphi
  have hconj (n : ℤ) (h : Q) (hh : h ∈ H) :
      x ^ n * h * (x ^ n)⁻¹ = y ^ n * h * (y ^ n)⁻¹ := by
    have heval := congrArg
      (fun a : MulAut H => a ⟨h, hh⟩) (hphiZpow n)
    exact congrArg Subtype.val heval
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  rw [Subgroup.commutator_le]
  intro h hh ym hym
  rw [Subgroup.mem_centralizer_iff]
  intro yn hyn
  rcases Subgroup.mem_zpowers_iff.mp hym with ⟨m, rfl⟩
  rcases Subgroup.mem_zpowers_iff.mp hyn with ⟨n, rfl⟩
  have hcommEq : ⁅h, y ^ m⁆ = ⁅h, x ^ m⁆ := by
    have hcj := hconj m h⁻¹ (H.inv_mem hh)
    calc
      ⁅h, y ^ m⁆ = h * (y ^ m * h⁻¹ * (y ^ m)⁻¹) := by
        simp [commutatorElement_def, mul_assoc]
      _ = h * (x ^ m * h⁻¹ * (x ^ m)⁻¹) := by rw [← hcj]
      _ = ⁅h, x ^ m⁆ := by
        simp [commutatorElement_def, mul_assoc]
  let z : Q := ⁅h, x ^ m⁆
  have hzH : z ∈ H := by
    apply (Subgroup.commutator_le_left H (Subgroup.zpowers x))
    exact Subgroup.commutator_mem_commutator hh
      (Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩)
  have hzcent : z ∈ Subgroup.centralizer (Subgroup.zpowers x : Set Q) := by
    apply (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommX)
    exact Subgroup.commutator_mem_commutator hh
      (Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩)
  have hxmul : x ^ n * z = z * x ^ n :=
    Subgroup.mem_centralizer_iff.mp hzcent (x ^ n)
      (Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩)
  have hxconj : x ^ n * z * (x ^ n)⁻¹ = z := by
    rw [hxmul]
    group
  have hyconj : y ^ n * z * (y ^ n)⁻¹ = z := by
    rw [← hconj n z hzH]
    exact hxconj
  have hymul : y ^ n * z = z * y ^ n := by
    calc
      y ^ n * z = (y ^ n * z * (y ^ n)⁻¹) * y ^ n := by group
      _ = z * y ^ n := by rw [hyconj]
  rw [hcommEq]
  exact hymul

private theorem subgroup_local_instability_of_ambient_failure
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (H : Subgroup Q) (hHp : IsPGroup p H) (hHnormal : H.Normal)
    (K : Subgroup Q) (hHK : H ≤ K)
    (hCK : Subgroup.centralizer (H : Set Q) ⊔ K = ⊤)
    (y : K)
    (hcommY :
      ⁅⁅H, Subgroup.zpowers (y : Q)⁆, Subgroup.zpowers (y : Q)⁆ = ⊥)
    (hyout :
      QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) (y : Q) ∉
        pCore p (Q ⧸ Subgroup.centralizer (H : Set Q))) :
    ¬ pStableLocal p K := by
  classical
  let C : Subgroup Q := Subgroup.centralizer (H : Set Q)
  have hCnormal : C.Normal := by
    dsimp [C]
    infer_instance
  let : C.Normal := hCnormal
  let P : Subgroup K := H.subgroupOf K
  have hPnormal : P.Normal := by
    dsimp [P]
    exact Subgroup.Normal.subgroupOf hHnormal K
  let : P.Normal := hPnormal
  have hPp : IsPGroup p P :=
    hHp.of_equiv (Subgroup.subgroupOfEquivOfLe hHK).symm
  have hPcondition : (pPrimeCore p K ⊔ P).Normal := by infer_instance
  let Nloc : Subgroup K := Subgroup.normalizer (P : Set K)
  let Cloc : Subgroup K := Subgroup.centralizer (P : Set K)
  have hNtop : Nloc = ⊤ := by
    exact Subgroup.normalizer_eq_top_iff.mpr hPnormal
  have hCloc : Cloc = C.subgroupOf K := by
    ext k
    constructor
    · intro hk
      apply Subgroup.mem_subgroupOf.mpr
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      let hK : K := ⟨h, hHK hh⟩
      have hhP : hK ∈ P := Subgroup.mem_subgroupOf.mpr hh
      exact congrArg Subtype.val
        (Subgroup.mem_centralizer_iff.mp hk hK hhP)
    · intro hk
      rw [Subgroup.mem_centralizer_iff]
      intro hK hhP
      apply Subtype.ext
      have hhH : (hK : Q) ∈ H := Subgroup.mem_subgroupOf.mp hhP
      exact Subgroup.mem_centralizer_iff.mp
        (Subgroup.mem_subgroupOf.mp hk) (hK : Q) hhH
  have hyN : y ∈ Nloc := by rw [hNtop]; simp
  have hcommLocal :
      ⁅⁅P, Subgroup.zpowers y⁆, Subgroup.zpowers y⁆ = ⊥ := by
    apply Subgroup.map_injective (f := K.subtype) K.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_commutator]
    rw [Subgroup.map_subgroupOf_eq_of_le hHK]
    simpa using hcommY
  let qC : Q →* Q ⧸ C := QuotientGroup.mk' C
  let theta : Nloc →* Q ⧸ C :=
    qC.comp (K.subtype.comp Nloc.subtype)
  have hthetaSurj : Function.Surjective theta := by
    intro z
    refine Quotient.inductionOn' z ?_
    intro g
    have hg : g ∈ C ⊔ K := by
      rw [show C ⊔ K = ⊤ by simpa [C] using hCK]
      simp
    rcases (Subgroup.mem_sup_of_normal_left
      (s := C) (t := K) (x := g)).mp hg with ⟨c, hc, k, hk, hck⟩
    let kK : K := ⟨k, hk⟩
    have hkN : kK ∈ Nloc := by rw [hNtop]; simp
    refine ⟨⟨kK, hkN⟩, ?_⟩
    change qC k = qC g
    rw [← hck, map_mul]
    have hqc : qC c = 1 :=
      (QuotientGroup.eq_one_iff (N := C) (x := c)).2 hc
    rw [hqc, one_mul]
  let ClocN : Subgroup Nloc := Cloc.subgroupOf Nloc
  have hker : ClocN = theta.ker := by
    ext n
    constructor
    · intro hn
      change theta n = 1
      apply (QuotientGroup.eq_one_iff
        (N := C) (x := ((n : Nloc) : K))).2
      have hnCloc : ((n : Nloc) : K) ∈ Cloc :=
        Subgroup.mem_subgroupOf.mp hn
      rw [hCloc] at hnCloc
      exact Subgroup.mem_subgroupOf.mp hnCloc
    · intro hn
      apply Subgroup.mem_subgroupOf.mpr
      rw [hCloc]
      apply Subgroup.mem_subgroupOf.mpr
      apply (QuotientGroup.eq_one_iff
        (N := C) (x := (((n : Nloc) : K) : Q))).1
      exact hn
  let e : Nloc ⧸ ClocN ≃* Q ⧸ C :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective theta hthetaSurj)
  have he_mk :
      e (QuotientGroup.mk' ClocN ⟨y, hyN⟩) =
        QuotientGroup.mk' C (y : Q) := by
    rfl
  intro hlocal
  have htarget := hlocal P hPp hPcondition y hyN hcommLocal
  have htarget' : QuotientGroup.mk' ClocN ⟨y, hyN⟩ ∈
      pCore p (Nloc ⧸ ClocN) := by
    simpa [Nloc, Cloc, ClocN] using htarget
  have hmapmem : e (QuotientGroup.mk' ClocN ⟨y, hyN⟩) ∈
      (pCore p (Nloc ⧸ ClocN)).map e.toMonoidHom :=
    Subgroup.mem_map_of_mem e.toMonoidHom htarget'
  have hcoreMap : (pCore p (Nloc ⧸ ClocN)).map e.toMonoidHom =
      pCore p (Q ⧸ C) :=
    pCore_map_iso (G := Nloc ⧸ ClocN) (G' := Q ⧸ C) (p := p) e
  rw [hcoreMap, he_mk] at hmapmem
  exact hyout (by simpa [C] using hmapmem)

private def topQuotientCongrStep7
    {Q : Type u} [Group Q] (E : Subgroup Q) [E.Normal] :
    (↥(⊤ : Subgroup Q) ⧸ E.subgroupOf (⊤ : Subgroup Q)) ≃* (Q ⧸ E) := by
  let e : ↥(⊤ : Subgroup Q) ≃* Q := Subgroup.topEquiv
  have he : (E.subgroupOf (⊤ : Subgroup Q)).map e.toMonoidHom = E := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.mp hy
    · intro hx
      exact Subgroup.mem_map.mpr
        ⟨⟨x, by simp⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  exact QuotientGroup.congr
    (G := ↥(⊤ : Subgroup Q)) (H := Q)
    (G' := E.subgroupOf (⊤ : Subgroup Q)) (H' := E) e he

private theorem normal_eq_bot_of_minimal_quotient_bad
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (hmin : ∀ (A : Subgroup Q) (B : Subgroup A) [B.Normal],
      Nat.card (A ⧸ B) < Nat.card Q → pStable p (A ⧸ B))
    (E : Subgroup Q) (hEnormal : E.Normal)
    (hcoreNe : pCore p (Q ⧸ E) ≠ ⊥)
    (hbad : ¬ pStableLocal p (Q ⧸ E)) :
    E = ⊥ := by
  classical
  let : E.Normal := hEnormal
  by_contra hEne
  have hlt : Nat.card (Q ⧸ E) < Nat.card Q :=
    natCard_quotient_lt_natCard_of_ne_bot E hEne
  have htoplt :
      Nat.card ((⊤ : Subgroup Q) ⧸ E.subgroupOf (⊤ : Subgroup Q)) < Nat.card Q := by
    calc
      Nat.card ((⊤ : Subgroup Q) ⧸ E.subgroupOf (⊤ : Subgroup Q)) =
          Nat.card (Q ⧸ E) :=
        Nat.card_congr (topQuotientCongrStep7 E).toEquiv
      _ < Nat.card Q := hlt
  have hstableTop :
      pStable p ((⊤ : Subgroup Q) ⧸ E.subgroupOf (⊤ : Subgroup Q)) :=
    hmin (⊤ : Subgroup Q) (E.subgroupOf (⊤ : Subgroup Q)) htoplt
  let e := topQuotientCongrStep7 E
  have hcoreMap :
      (pCore p ((⊤ : Subgroup Q) ⧸ E.subgroupOf (⊤ : Subgroup Q))).map
          e.toMonoidHom = pCore p (Q ⧸ E) :=
    pCore_map_iso (p := p) e
  have hcoreTopNe :
      pCore p ((⊤ : Subgroup Q) ⧸ E.subgroupOf (⊤ : Subgroup Q)) ≠ ⊥ := by
    intro hbot
    apply hcoreNe
    have hmapBot :
        (pCore p ((⊤ : Subgroup Q) ⧸ E.subgroupOf (⊤ : Subgroup Q))).map
            e.toMonoidHom = ⊥ := by
      rw [hbot]
      exact Subgroup.map_bot e.toMonoidHom
    exact hcoreMap.symm.trans hmapBot
  have hlocalTop :
      pStableLocal p ((⊤ : Subgroup Q) ⧸ E.subgroupOf (⊤ : Subgroup Q)) :=
    pStableLocal_of_core_ne_bot p hstableTop hcoreTopNe
  have hlocal : pStableLocal p (Q ⧸ E) :=
    (pStableLocal_congr (p := p) e).mp hlocalTop
  exact hbad hlocal

private theorem subgroup_eq_top_of_minimal_local_instability
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (hmin : ∀ (A : Subgroup Q) (B : Subgroup A) [B.Normal],
      Nat.card (A ⧸ B) < Nat.card Q → pStable p (A ⧸ B))
    (H K : Subgroup Q) (hHK : H ≤ K)
    (hHnormal : H.Normal) (hHp : IsPGroup p H) (hHne : H ≠ ⊥)
    (hnotLocal : ¬ pStableLocal p K) :
    K = ⊤ := by
  classical
  let Hloc : Subgroup K := H.subgroupOf K
  have hHlocNormal : Hloc.Normal :=
    Subgroup.Normal.subgroupOf hHnormal K
  have hHlocp : IsPGroup p Hloc :=
    hHp.of_equiv (Subgroup.subgroupOfEquivOfLe hHK).symm
  have hHlocne : Hloc ≠ ⊥ := by
    intro hbot
    apply hHne
    apply le_antisymm ?_ bot_le
    intro h hh
    let hK : K := ⟨h, hHK hh⟩
    have hhLoc : hK ∈ Hloc := hh
    rw [hbot] at hhLoc
    simpa [hK] using congrArg Subtype.val (show hK = 1 by simpa using hhLoc)
  have hcoreNe : pCore p K ≠ ⊥ := by
    intro hcorebot
    apply hHlocne
    apply le_antisymm ?_ bot_le
    have hle : Hloc ≤ pCore p K := le_sSup ⟨hHlocNormal, hHlocp⟩
    rw [hcorebot] at hle
    exact hle
  by_contra hKtop
  have hKlt : K < (⊤ : Subgroup Q) := lt_top_iff_ne_top.mpr hKtop
  have hKcard : Nat.card K < Nat.card Q := by
    simpa using natCard_lt_of_subgroup_lt hKlt
  have hquotCard : Nat.card (K ⧸ (⊥ : Subgroup K)) < Nat.card Q := by
    calc
      Nat.card (K ⧸ (⊥ : Subgroup K)) = Nat.card K :=
        Nat.card_congr (QuotientGroup.quotientBot (G := K)).toEquiv
      _ < Nat.card Q := hKcard
  have hstableQuot : pStable p (K ⧸ (⊥ : Subgroup K)) :=
    hmin K (⊥ : Subgroup K) hquotCard
  let e : K ⧸ (⊥ : Subgroup K) ≃* K := QuotientGroup.quotientBot
  have hcoreMap :
      (pCore p (K ⧸ (⊥ : Subgroup K))).map e.toMonoidHom = pCore p K :=
    pCore_map_iso (p := p) e
  have hcoreQuotNe : pCore p (K ⧸ (⊥ : Subgroup K)) ≠ ⊥ := by
    intro hbot
    apply hcoreNe
    have hmapBot : (pCore p (K ⧸ (⊥ : Subgroup K))).map e.toMonoidHom = ⊥ := by
      rw [hbot]
      exact Subgroup.map_bot e.toMonoidHom
    exact hcoreMap.symm.trans hmapBot
  have hlocalQuot : pStableLocal p (K ⧸ (⊥ : Subgroup K)) :=
    pStableLocal_of_core_ne_bot p hstableQuot hcoreQuotNe
  have hlocalK : pStableLocal p K :=
    (pStableLocal_congr (p := p) e).mp hlocalQuot
  exact hnotLocal hlocalK

private theorem step7_normalizer_sup_H_eq_top
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (hmin : ∀ (A : Subgroup Q) (B : Subgroup A) [B.Normal],
      Nat.card (A ⧸ B) < Nat.card Q → pStable p (A ⧸ B))
    (H : Subgroup Q) (hHnormal : H.Normal) (hHp : IsPGroup p H)
    (hHne : H ≠ ⊥)
    (x : Q)
    (hcomm : ⁅⁅H, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥)
    (hxout :
      QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) x ∉
        pCore p (Q ⧸ Subgroup.centralizer (H : Set Q)))
    (T2 : Subgroup Q)
    (hCNtop : Subgroup.centralizer (H : Set Q) ⊔
      Subgroup.normalizer (T2 : Set Q) = ⊤) :
    Subgroup.normalizer (T2 : Set Q) ⊔ H = ⊤ := by
  classical
  let C : Subgroup Q := Subgroup.centralizer (H : Set Q)
  let N : Subgroup Q := Subgroup.normalizer (T2 : Set Q)
  let K : Subgroup Q := N ⊔ H
  have hCnormal : C.Normal := by
    dsimp [C]
    exact Subgroup.normal_centralizer (H := H)
  let : C.Normal := hCnormal
  have hCNtop' : C ⊔ N = ⊤ := by simpa [C, N] using hCNtop
  have hHK : H ≤ K := by
    dsimp [K]
    exact le_sup_right
  have hCK : C ⊔ K = ⊤ := by
    calc
      C ⊔ K = (C ⊔ N) ⊔ H := by simp [K, sup_assoc]
      _ = ⊤ := by rw [hCNtop', top_sup_eq]
  have hxCN : x ∈ C ⊔ N := by
    rw [hCNtop']
    trivial
  rcases (Subgroup.mem_sup_of_normal_left
    (s := C) (t := N) (x := x)).mp hxCN with ⟨c, hc, y, hy, hcy⟩
  let yK : K := ⟨y, (le_sup_left : N ≤ N ⊔ H) hy⟩
  have hcommY :
      ⁅⁅H, Subgroup.zpowers (yK : Q)⁆,
          Subgroup.zpowers (yK : Q)⁆ = ⊥ := by
    simpa [yK] using
      (double_commutator_zpowers_of_central_factor
        H hHnormal hc hcy hcomm)
  have hyout :
      QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) (yK : Q) ∉
        pCore p (Q ⧸ Subgroup.centralizer (H : Set Q)) := by
    intro hycore
    apply hxout
    let q : Q →* Q ⧸ C := QuotientGroup.mk' C
    have hqc : q c = 1 :=
      (QuotientGroup.eq_one_iff (N := C) (x := c)).2 hc
    have hqxy : q x = q y := by
      rw [← hcy, map_mul, hqc, one_mul]
    simpa [C, q, yK, hqxy] using hycore
  have hnotLocal : ¬ pStableLocal p K :=
    subgroup_local_instability_of_ambient_failure
      H hHp hHnormal K hHK hCK yK hcommY hyout
  have hKtop : K = ⊤ :=
    subgroup_eq_top_of_minimal_local_instability
      hmin H K hHK hHnormal hHp hHne hnotLocal
  simpa [K, N] using hKtop

private theorem step7_centralizer_eq
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {Q : Type u} [Group Q] [Finite Q]
    (hmin : ∀ (A : Subgroup Q) (B : Subgroup A) [B.Normal],
      Nat.card (A ⧸ B) < Nat.card Q → pStable p (A ⧸ B))
    (H : Subgroup Q) (hHnormal : H.Normal) (hHp : IsPGroup p H)
    (hHne : H ≠ ⊥)
    (hHleC : H ≤ Subgroup.centralizer (H : Set Q))
    (hCp : IsPGroup p (Subgroup.centralizer (H : Set Q)))
    (x : Q)
    (hcomm : ⁅⁅H, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥)
    (hxout :
      QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) x ∉
        pCore p (Q ⧸ Subgroup.centralizer (H : Set Q)))
    (T2 : Subgroup Q) (hT2p : IsPGroup 2 T2)
    (t : Q) (htT2 : t ∈ T2)
    (hinverts : ∀ h : Q, h ∈ H → t * h * t⁻¹ = h⁻¹)
    (htop : Subgroup.normalizer (T2 : Set Q) ⊔ H = ⊤) :
    Subgroup.centralizer (H : Set Q) ⊓
          Subgroup.normalizer (T2 : Set Q) = ⊥ ∧
      Subgroup.centralizer (H : Set Q) = H := by
  classical
  let C : Subgroup Q := Subgroup.centralizer (H : Set Q)
  let N : Subgroup Q := Subgroup.normalizer (T2 : Set Q)
  let E : Subgroup Q := C ⊓ N
  obtain ⟨hEnormal, hEH, hCeq⟩ :=
    step7_internal_decomposition hpodd H hHnormal hHp hHleC hCp
      T2 hT2p t htT2 hinverts htop
  obtain ⟨hcoreEne, hbadE⟩ :=
    quotient_core_ne_and_not_pStableLocal_of_disjoint_central_factor
      H hHnormal hHp hHne E hEnormal hEH x hcomm hxout
  have hEbot : E = ⊥ :=
    normal_eq_bot_of_minimal_quotient_bad
      hmin E hEnormal hcoreEne hbadE
  have hCeq' : C = E ⊔ H := hCeq
  rw [hEbot, bot_sup_eq] at hCeq'
  exact ⟨by simpa [E, C, N] using hEbot, by simpa [C] using hCeq'⟩

/-- Paper step 7 of Glauberman Lemma 6.3: an action-compatible identification
of `Q / C_Q(H)` with the natural `SL₂(p)` action produces a Sylow-normalizer
complement to `H` and forces `C_Q(H) = H`. -/
public theorem lemma6_3_step7_centralizer_eq
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {Q : Type u} [Group Q] [Finite Q]
    (hmin : ∀ (A : Subgroup Q) (B : Subgroup A) [B.Normal],
      Nat.card (A ⧸ B) < Nat.card Q → pStable p (A ⧸ B))
    (H : Subgroup Q) (hHnormal : H.Normal) (hHp : IsPGroup p H)
    (hHne : H ≠ ⊥)
    (hHleC : H ≤ Subgroup.centralizer (H : Set Q))
    (hCp : IsPGroup p (Subgroup.centralizer (H : Set Q)))
    [IsMulCommutative H] [Module (ZMod p) (Additive H)]
    (x : Q)
    (hcomm : ⁅⁅H, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥)
    (hxout :
      QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) x ∉
        pCore p (Q ⧸ Subgroup.centralizer (H : Set Q)))
    (rho : Q ⧸ Subgroup.centralizer (H : Set Q) →*
      LinearMap.GeneralLinearGroup (ZMod p) (Additive H))
    (hrho_eval : ∀ (g : Q) (v : Additive H),
      Additive.toMul
          (((rho (QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) g) :
            Additive H →ₗ[ZMod p] Additive H) v)) =
        MulAut.conjNormal (H := H) g (Additive.toMul v))
    (coord : Additive H ≃ₗ[ZMod p] qdSpace p)
    (e : (Q ⧸ Subgroup.centralizer (H : Set Q)) ≃* qdSL p)
    (hintertwine :
      ∀ (g : Q ⧸ Subgroup.centralizer (H : Set Q)) (v : Additive H),
        coord (((rho g : Additive H →ₗ[ZMod p] Additive H) v)) =
          Matrix.SpecialLinearGroup.toLin' (e g) (coord v)) :
    ∃ T2 : Subgroup Q, IsPGroup 2 T2 ∧
      Subgroup.centralizer (H : Set Q) ⊔
          Subgroup.normalizer (T2 : Set Q) = ⊤ ∧
        Subgroup.normalizer (T2 : Set Q) ⊔ H = ⊤ ∧
          Subgroup.centralizer (H : Set Q) ⊓
              Subgroup.normalizer (T2 : Set Q) = ⊥ ∧
            Subgroup.centralizer (H : Set Q) = H ∧
              H.IsComplement' (Subgroup.normalizer (T2 : Set Q)) := by
  classical
  let : H.Normal := hHnormal
  obtain ⟨T2, hT2p, t, htT2, hinverts, hCNtop⟩ :=
    step7_exists_inverting_sylow_of_compatible_rep
      hpodd H hHnormal rho hrho_eval coord e hintertwine
  have htop : Subgroup.normalizer (T2 : Set Q) ⊔ H = ⊤ :=
    step7_normalizer_sup_H_eq_top
      hmin H hHnormal hHp hHne x hcomm hxout T2 hCNtop
  obtain ⟨hEbot, hCeq⟩ :=
    step7_centralizer_eq hpodd hmin H hHnormal hHp hHne
      hHleC hCp x hcomm hxout T2 hT2p t htT2 hinverts htop
  let N : Subgroup Q := Subgroup.normalizer (T2 : Set Q)
  have hHNbot : H ⊓ N = ⊥ := by
    simpa [N, hCeq] using hEbot
  have hdisj : Disjoint H N := disjoint_iff_inf_le.mpr hHNbot.le
  have hHNtop : H ⊔ N = ⊤ := by
    simpa [N, sup_comm] using htop
  have hmul : (H : Set Q) * (N : Set Q) = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro g
    have hg : g ∈ H ⊔ N := by rw [hHNtop]; trivial
    rcases (Subgroup.mem_sup_of_normal_left
      (s := H) (t := N) (x := g)).mp hg with ⟨h, hh, n, hn, hhn⟩
    rw [Set.mem_mul]
    exact ⟨h, hh, n, hn, hhn⟩
  have hcomp : H.IsComplement' N :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul
  exact ⟨T2, hT2p, hCNtop, htop, hEbot, hCeq, by simpa [N] using hcomp⟩

end CFSG.Glauberman
