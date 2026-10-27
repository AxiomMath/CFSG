module

public import CFSG.LocalAnalysis.WeakClosure81.FourElevenLeviL3
public import CFSG.LocalAnalysis.WeakClosure81.FourElevenLeviU3
public import CFSG.Quasithin.Vol2.Ch11SecU1U3R
public import CFSG.Quasithin.H13.NQCatA314SL25
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3Main
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81.FourEleven

open Subgroup CFSG.Quasithin.E2P.Asc80
open CFSG.Quasithin.Vol2.Ch11.SecU1.L3I CFSG.Quasithin.Vol2.Ch11.SecU1.U3
open CFSG.Blueprint (LieModel)

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem exists_leviData {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {L : Subgroup Q} [L.Normal]
    (hL : LieModel ↥L .PSL 3 p 1 ∨ LieModel ↥L .PSU 3 p 1) {y : Q} (hyL : y ∈ L)
    (hy2 : orderOf y = 2) : ∃ Y : Subgroup Q, LeviData L p y Y := by
  let _ : Fact p.Prime := ⟨hp⟩
  rcases hL with h | h
  · have hm : CFSG.Open.StatedClassicalModel ↥L .PSL 3 p 1 :=
      h.statedClassicalModel (by decide)
    obtain ⟨e⟩ := CFSG.Quasithin.E2P.Asc80.exists_equiv_psl3 (p := p) hm
    exact exists_leviData_psl3 hp5 e hyL hy2
  · have hm : CFSG.Open.StatedClassicalModel ↥L .PSU 3 p 1 :=
      h.statedClassicalModel (by decide)
    obtain ⟨F, hFld, hFin, hF, ⟨e⟩⟩ :=
      CFSG.Quasithin.E2P.Asc80.exists_equiv_psu3 (p := p) hm
    let _ : Field F := hFld
    let _ : Finite F := hFin
    exact exists_leviData_psu3 hp5 hF e.symm hyL hy2

open CFSG.Quasithin.Vol2.Ch11.SecU1.L3I in
theorem leviPsi_pow_four_mem_leviY {A : GL (Fin 2) (ZMod 5)} :
    leviPsi 5 (A ^ 4) ∈ leviY 5 := by
  have hdet : ((A ^ 4 : GL (Fin 2) (ZMod 5)) : Matrix (Fin 2) (Fin 2) (ZMod 5)).det = 1 := by
    change (Matrix.GeneralLinearGroup.det (A ^ 4) : ZMod 5) = 1
    let _ : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have h4 : (Matrix.GeneralLinearGroup.det A) ^ 4 = 1 := by
      have h := ZMod.units_pow_card_sub_one_eq_one 5 (Matrix.GeneralLinearGroup.det A)
      norm_num at h
      exact h
    rw [map_pow, h4, Units.val_one]
  let S : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨(A ^ 4 : GL (Fin 2) (ZMod 5)), hdet⟩
  refine ⟨S, ?_⟩
  rw [ofSL2_eq_leviPsi]
  congr 1
  exact Units.ext rfl

open CFSG.Quasithin.Vol2.Ch11.SecU1.L3I in
theorem isPGroup_two_centralizer_leviY_five :
    IsPGroup 2 ↥(Subgroup.centralizer (leviY 5 : Set (PSL3 5))) := by
  intro x
  refine ⟨2, Subtype.ext ?_⟩
  obtain ⟨u, hu⟩ := mem_centralizer_leviY (p := 5) (by norm_num) x.2
  change (x : PSL3 5) ^ 4 = 1
  rw [hu, ← map_pow]
  let _ : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hu4 : u ^ 4 = 1 := by
    have h := ZMod.units_pow_card_sub_one_eq_one 5 u
    norm_num at h
    exact h
  have hsc : (Matrix.GeneralLinearGroup.scalar (Fin 2) u) ^ 4 = 1 := by
    rw [← map_pow, hu4, map_one]
  rw [hsc, map_one]

open CFSG.Quasithin.Vol2.Ch11.SecU1.U3 in
theorem isPGroup_two_centralizer_leviSL_five {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 5 ^ 2) :
    IsPGroup 2 ↥(Subgroup.centralizer (leviSL hF : Set (PSU3F 5 F))) := by
  intro x
  rcases eq_one_or_eq_zcU_of_mem_centralizer_leviSL (p := 5) (F := F) rfl hF x.2 with hx | hx
  · exact ⟨0, Subtype.ext (by simpa using hx)⟩
  · refine ⟨1, Subtype.ext ?_⟩
    have hz2 : zcU hF ^ 2 = 1 := by
      rw [← orderOf_zcU (p := 5) (by norm_num) hF, pow_orderOf_eq_one]
    exact (by simpa [hx] using hz2 : (x : PSU3F 5 F) ^ 2 = 1)

open CFSG.Quasithin.Vol2.Ch11.SecU1.U3 in
theorem sq_mem_leviSL_five {F : Type} [Field F] [Finite F] (hF : Nat.card F = 5 ^ 2)
    (hcardP : Nat.card (PSU3F 5 F) = 126000) {a : PSU3F 5 F} (ha : a ∈ leviCU hF) :
    a ^ 2 ∈ leviSL hF := by
  have hcardSL : Nat.card ↥(leviSL hF) = 120 := by
    rw [← Nat.card_congr (leviSLEquiv hF).toEquiv]
    rw [Matrix.card_SL_field]
    norm_num
  have hcardCU : Nat.card ↥(leviCU hF) = 240 := by
    have h := Subgroup.card_mul_index (leviCU hF)
    have hidx : (leviCU hF).index = 525 := by
      rw [index_leviCU (p := 5) (by norm_num) hF, index_leviU hF]
      norm_num
    rw [hidx, hcardP] at h
    omega
  have hsub : Nat.card ↥((leviSL hF).subgroupOf (leviCU hF)) = 120 := by
    rw [← hcardSL]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (leviSL_le_leviCU hF)).toEquiv
  have hrel : ((leviSL hF).subgroupOf (leviCU hF)).index = 2 := by
    have h := Subgroup.card_mul_index ((leviSL hF).subgroupOf (leviCU hF))
    rw [hsub, hcardCU] at h
    omega
  have _ : ((leviSL hF).subgroupOf (leviCU hF)).Normal :=
    Subgroup.normal_of_index_eq_two hrel
  have h := Subgroup.pow_relIndex_mem ((leviSL hF).subgroupOf (leviCU hF))
    (K := ⊤) (g := (⟨a, ha⟩ : ↥(leviCU hF))) (Subgroup.mem_top _)
  rw [Subgroup.relIndex_top_right, hrel] at h
  have hmem : (⟨a, ha⟩ : ↥(leviCU hF)) ^ 2 ∈ (leviSL hF).subgroupOf (leviCU hF) := h
  simpa [Subgroup.mem_subgroupOf] using hmem

omit [Finite Q] in
theorem LeviData.five {L : Subgroup Q} [L.Normal]
    (hL : LieModel ↥L .PSL 3 5 1 ∨ LieModel ↥L .PSU 3 5 1) {y : Q} {Y : Subgroup Q}
    (hY : LeviData L 5 y Y) :
    IsPGroup 2 ↥(L ⊓ centralizer (Y : Set Q)) ∧
      ∀ x ∈ L ⊓ centralizer ({y} : Set Q), ∃ k : ℕ, x ^ 2 ^ k ∈ Y := by
  obtain ⟨eY⟩ := hY.sl2
  obtain ⟨z, hz2, hzB, hBcen⟩ := CFSG.Quasithin.H13.NQCat.A314D.sl25_core eY
  have hYcomm_le : ⁅L ⊓ centralizer ({y} : Set Q), L ⊓ centralizer ({y} : Set Q)⁆ ≤
      L ⊓ centralizer ({y} : Set Q) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact (L ⊓ centralizer ({y} : Set Q)).mul_mem
      ((L ⊓ centralizer ({y} : Set Q)).mul_mem
        ((L ⊓ centralizer ({y} : Set Q)).mul_mem ha hb)
        ((L ⊓ centralizer ({y} : Set Q)).inv_mem ha))
      ((L ⊓ centralizer ({y} : Set Q)).inv_mem hb)
  have hYL : Y ≤ L := hY.eq_commutator.trans_le (hYcomm_le.trans inf_le_left)
  have hzY : z ∈ Y := Subgroup.map_subtype_le (CFSG.pCore 2 ↥Y) hzB
  have hzC : z ∈ centralizer (Y : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (Subgroup.mem_centralizer_iff.mp (hBcen hs) z hzB).symm
  have hzy : z = y := hY.involution_eq z ⟨hYL hzY, hzC⟩ hz2
  have hyL : y ∈ L := hYL hY.mem
  have hy2 : orderOf y = 2 := by rw [← hzy]; exact hz2
  rcases hL with hL3 | hLU
  ·
    have hm : CFSG.Open.StatedClassicalModel ↥L .PSL 3 5 1 :=
      hL3.statedClassicalModel (by decide)
    obtain ⟨e⟩ := CFSG.Quasithin.E2P.Asc80.exists_equiv_psl3 (p := 5) hm
    obtain ⟨e', he'⟩ := exists_equiv_zc (p := 5) (by norm_num) e hyL hy2
    let f : PSL3 5 →* Q := L.subtype.comp e'.symm.toMonoidHom
    have hfinj : Function.Injective f := L.subtype_injective.comp e'.symm.injective
    have hfL : ∀ c, f c ∈ L := fun c => (e'.symm c).2
    have hfe : ∀ (x : Q) (hx : x ∈ L), f (e' ⟨x, hx⟩) = x := fun x hx => by
      simp [f]
    have hfz : f (zc 5) = y := by
      change L.subtype (e'.symm (zc 5)) = y
      rw [← he', MulEquiv.symm_apply_apply]
      rfl
    have hcomm_f : ∀ (x : Q) (hx : x ∈ L) (c : PSL3 5),
        x * f c = f c * x ↔ e' ⟨x, hx⟩ * c = c * e' ⟨x, hx⟩ := by
      intro x hx c
      constructor
      · intro h
        apply hfinj
        rw [map_mul, map_mul, hfe x hx]
        exact h
      · intro h
        have h1 := congrArg f h
        rwa [map_mul, map_mul, hfe x hx] at h1
    have hCL : L ⊓ centralizer ({y} : Set Q) = (leviC 5).map f := by
      simpa [f] using inf_centralizer_eq_map_leviC (p := 5) (by norm_num) e' hyL he'
    have hY0 : (leviY 5).map f = ⁅L ⊓ centralizer ({y} : Set Q),
        L ⊓ centralizer ({y} : Set Q)⁆ := by
      rw [hCL, ← Subgroup.map_commutator, commutator_leviC (p := 5) (by norm_num)]
    have hYeq : Y = (leviY 5).map f := hY.eq_commutator.trans hY0.symm
    have hCY : L ⊓ centralizer (Y : Set Q) =
        (Subgroup.centralizer (leviY 5 : Set (PSL3 5))).map f := by
      rw [hYeq]
      ext x
      constructor
      · rintro ⟨hxL, hxY⟩
        refine ⟨e' ⟨x, hxL⟩, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_, hfe x hxL⟩
        have h1 := Subgroup.mem_centralizer_iff.mp hxY (f s) ⟨s, hs, rfl⟩
        exact ((hcomm_f x hxL s).mp h1.symm).symm
      · rintro ⟨c, hc, rfl⟩
        refine ⟨hfL c, Subgroup.mem_centralizer_iff.mpr ?_⟩
        rintro _ ⟨s, hs, rfl⟩
        rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hc s hs]
    refine ⟨?_, ?_⟩
    · rw [hCY]
      refine (isPGroup_two_centralizer_leviY_five).of_equiv
        ((Subgroup.centralizer (leviY 5 : Set (PSL3 5))).equivMapOfInjective f hfinj)
    · rintro x hx
      rw [hCL] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      refine ⟨2, ?_⟩
      have ha4 : a ^ 4 ∈ leviY 5 := by
        rw [← leviPsi_range] at ha
        obtain ⟨A, rfl⟩ := ha
        rw [← map_pow]
        exact leviPsi_pow_four_mem_leviY
      rw [hYeq]
      change (f a) ^ 4 ∈ (leviY 5).map f
      rw [show (f a) ^ 4 = f (a ^ 4) by rw [map_pow]]
      exact ⟨a ^ 4, ha4, rfl⟩
  ·
    have hm : CFSG.Open.StatedClassicalModel ↥L .PSU 3 5 1 :=
      hLU.statedClassicalModel (by decide)
    obtain ⟨F, hFld, hFin, hF, ⟨e⟩⟩ :=
      CFSG.Quasithin.E2P.Asc80.exists_equiv_psu3 (p := 5) hm
    let _ : Field F := hFld
    let _ : Finite F := hFin
    let ψ : PSU3F 5 F ≃* ↥L := e.symm
    obtain ⟨ψ', hψ'⟩ := exists_equiv_zcU (p := 5) (F := F) (y := y)
      (by norm_num) hF ψ hyL hy2
    let f : PSU3F 5 F →* Q := embU ψ'
    have hfinj : Function.Injective f := embU_injective ψ'
    have hCL : L ⊓ centralizer ({y} : Set Q) = (leviCU hF).map f := by
      rw [← hψ', inf_centralizer_embU,
        centralizer_zcU (p := 5) (F := F) (by norm_num) hF]
    have hY0 : (leviSL hF).map f = ⁅L ⊓ centralizer ({y} : Set Q),
        L ⊓ centralizer ({y} : Set Q)⁆ := by
      rw [hCL, ← Subgroup.map_commutator, commutator_leviCU (p := 5) (by norm_num) hF]
    have hYeq : Y = (leviSL hF).map f := hY.eq_commutator.trans hY0.symm
    have hCY : L ⊓ centralizer (Y : Set Q) =
        (Subgroup.centralizer (leviSL hF : Set (PSU3F 5 F))).map f := by
      rw [hYeq]
      exact inf_centralizer_map_embU ψ' (leviSL hF)
    have hcardP : Nat.card (PSU3F 5 F) = 126000 := by
      rw [← Nat.card_congr e.toEquiv]
      exact (CFSG.RankThree.Classical.unitary_three_five_model ↥L hm).1
    refine ⟨?_, ?_⟩
    · rw [hCY]
      refine (isPGroup_two_centralizer_leviSL_five hF).of_equiv
        ((Subgroup.centralizer (leviSL hF : Set (PSU3F 5 F))).equivMapOfInjective f hfinj)
    · rintro x hx
      rw [hCL] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      refine ⟨1, ?_⟩
      have ha2 : a ^ 2 ∈ leviSL hF := sq_mem_leviSL_five hF hcardP ha
      rw [hYeq]
      change (f a) ^ 2 ∈ (leviSL hF).map f
      rw [show (f a) ^ 2 = f (a ^ 2) by rw [map_pow]]
      exact ⟨a ^ 2, ha2, rfl⟩

end CFSG.LocalAnalysis.WeakClosure81.FourEleven
