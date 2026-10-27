module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerToralMat
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerLeafDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.Triality
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.KFacts (unitaryIsom3 mem_unitaryIsom3)
open CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner (sc scal mem_sc_iff scal_mem_sc
  coe_scal sc_mem_center scal_pow scal_one diagGL diagGL_mul diagGL_inv torusThree)

namespace D4Inner

section Pull

variable {G R U : Type*} [Group G] [Group R] [Group U] {C : Subgroup G}

@[expose] def pbSub (Ψ : ↥C ≃* R × U) (X : Subgroup (R × U)) : Subgroup G :=
  (X.comap Ψ.toMonoidHom).map C.subtype

theorem coe_mem_pbSub (Ψ : ↥C ≃* R × U) (X : Subgroup (R × U)) (y : C) :
    (y : G) ∈ pbSub Ψ X ↔ Ψ y ∈ X := by
  constructor
  · rintro ⟨z, hz, hzy⟩
    have : z = y := Subtype.ext hzy
    rw [← this]
    exact hz
  · intro h
    exact ⟨y, h, rfl⟩

theorem pbSub_le (Ψ : ↥C ≃* R × U) (X : Subgroup (R × U)) : pbSub Ψ X ≤ C := by
  rintro _ ⟨z, -, rfl⟩
  exact z.2

theorem pow_three_eq_one_iff_of_mulEquiv (Ψ : ↥C ≃* R × U) (y : C) :
    (y : G) ^ 3 = 1 ↔ (Ψ y).1 ^ 3 = 1 ∧ (Ψ y).2 ^ 3 = 1 := by
  rw [← SubgroupClass.coe_pow, OneMemClass.coe_eq_one, ← Ψ.injective.eq_iff, map_pow, map_one,
    Prod.ext_iff, Prod.pow_fst, Prod.pow_snd, Prod.fst_one, Prod.snd_one]

@[expose] def torsion3 (H : Subgroup G) (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) : Subgroup G where
  carrier := {x | x ∈ H ∧ x ^ 3 = 1}
  mul_mem' := by
    rintro a b ⟨ha, ha3⟩ ⟨hb, hb3⟩
    exact ⟨mul_mem ha hb, by
      rw [Commute.mul_pow (show Commute a b from hH a ha b hb), ha3, hb3, one_mul]⟩
  one_mem' := ⟨one_mem _, one_pow _⟩
  inv_mem' := by
    rintro a ⟨ha, ha3⟩
    exact ⟨inv_mem ha, by rw [inv_pow, ha3, inv_one]⟩

theorem mem_torsion3 {H : Subgroup G} {hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a} {x : G} :
    x ∈ torsion3 H hH ↔ x ∈ H ∧ x ^ 3 = 1 := Iff.rfl

end Pull

section Frame

variable {n : ℕ} {E : Type} [Field E] (hU : UnitaryFieldData 2 n E)

@[expose] def diagSub (E : Type) [Field E] : Subgroup (GL (Fin 3) E) where
  carrier := {M | IsDiagGL M}
  mul_mem' := fun ha hb => IsDiagGL.mul ha hb
  one_mem' := isDiagGL_one
  inv_mem' := fun ha => IsDiagGL.inv ha

@[expose] def diagU (g : GL (Fin 3) E) : Subgroup ↥(unitaryIsom3 hU) :=
  (diagSub E).comap ((MulAut.conj g).toMonoidHom.comp (unitaryIsom3 hU).subtype)

theorem mem_diagU {g : GL (Fin 3) E} {u : ↥(unitaryIsom3 hU)} :
    u ∈ diagU hU g ↔ IsDiagGL (g * (u : GL (Fin 3) E) * g⁻¹) := Iff.rfl

@[expose] def detOneU : Subgroup ↥(unitaryIsom3 hU) :=
  (Matrix.GeneralLinearGroup.det.comp (unitaryIsom3 hU).subtype).ker

theorem mem_detOneU {u : ↥(unitaryIsom3 hU)} :
    u ∈ detOneU hU ↔ (((u : ↥(unitaryIsom3 hU)) : GL (Fin 3) E) :
      Matrix (Fin 3) (Fin 3) E).det = 1 := by
  rw [detOneU, MonoidHom.mem_ker, MonoidHom.comp_apply, ← Units.val_eq_one,
    Matrix.GeneralLinearGroup.val_det_apply]
  rfl

theorem scal_mem_diagU {g : GL (Fin 3) E} {u : ↥(unitaryIsom3 hU)}
    (hu : ((u : ↥(unitaryIsom3 hU)) : GL (Fin 3) E) ∈ sc E) : u ∈ diagU hU g := by
  rw [mem_diagU]
  obtain ⟨c, hc⟩ := mem_sc_iff.mp hu
  have hcomm := (Subgroup.mem_center_iff.mp (sc_mem_center (scal_mem_sc c)) g).symm
  rw [hc, ← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  exact isDiagGL_scal c

theorem diagU_commute {g : GL (Fin 3) E} {u w : ↥(unitaryIsom3 hU)} (hu : u ∈ diagU hU g)
    (hw : w ∈ diagU hU g) : u * w = w * u := by
  have hc := ((mem_diagU hU).mp hu).commute ((mem_diagU hU).mp hw)
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  calc (u : GL (Fin 3) E) * (w : GL (Fin 3) E) =
      g⁻¹ * ((g * (u : GL (Fin 3) E) * g⁻¹) * (g * (w : GL (Fin 3) E) * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * (w : GL (Fin 3) E) * g⁻¹) * (g * (u : GL (Fin 3) E) * g⁻¹)) * g := by
        rw [hc]
    _ = (w : GL (Fin 3) E) * (u : GL (Fin 3) E) := by group

theorem mem_diagU_iff_commute (h3 : 3 ∣ 2 ^ n + 1) {ω : Eˣ} (hω : IsPrimitiveRoot (ω : E) 3)
    {g : GL (Fin 3) E} (hg : g ∈ unitaryIsom3 hU) (w : ↥(unitaryIsom3 hU)) :
    (∀ u : ↥(unitaryIsom3 hU), u ∈ diagU hU g ⊓ detOneU hU → u * w = w * u) ↔ w ∈ diagU hU g := by
  have hω3 : ω ^ 3 = 1 := Units.ext (by simpa using hω.pow_eq_one)
  have hω23 : (ω ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
  constructor
  · intro h
    set u₀ : ↥(unitaryIsom3 hU) := ⟨g⁻¹ * diagGL E 1 ω (ω ^ 2) * g,
      conj_diagGL_mem hU h3 hg (one_pow 3) hω3 hω23⟩ with hu₀
    have hu₀D : u₀ ∈ diagU hU g ⊓ detOneU hU := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [mem_diagU]
        exact ⟨1, ω, ω ^ 2, by rw [hu₀]; group⟩
      · rw [mem_detOneU, hu₀]
        change ((g⁻¹ * diagGL E 1 ω (ω ^ 2) * g : GL (Fin 3) E) :
          Matrix (Fin 3) (Fin 3) E).det = 1
        rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, det_diagGL, mul_comm,
          ← mul_assoc, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.det_one, one_mul, Units.val_one, one_mul, ← Units.val_mul,
          show ω * ω ^ 2 = ω ^ 3 from (pow_succ' ω 2).symm, hω3, Units.val_one]
    have h1 := congrArg Subtype.val (h u₀ hu₀D)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hu₀] at h1
    rw [mem_diagU]
    refine isDiagGL_of_commute hω ?_
    calc g * (w : GL (Fin 3) E) * g⁻¹ * diagGL E 1 ω (ω ^ 2) =
        g * ((w : GL (Fin 3) E) * (g⁻¹ * diagGL E 1 ω (ω ^ 2) * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * diagGL E 1 ω (ω ^ 2) * g) * (w : GL (Fin 3) E)) * g⁻¹ := by rw [h1]
      _ = diagGL E 1 ω (ω ^ 2) * (g * (w : GL (Fin 3) E) * g⁻¹) := by group
  · intro hw u hu
    have hu' := (mem_diagU hU).mp (Subgroup.mem_inf.mp hu).1
    have hw' := (mem_diagU hU).mp hw
    have hc := hu'.commute hw'
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    calc (u : GL (Fin 3) E) * (w : GL (Fin 3) E) =
        g⁻¹ * ((g * (u : GL (Fin 3) E) * g⁻¹) * (g * (w : GL (Fin 3) E) * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * (w : GL (Fin 3) E) * g⁻¹) * (g * (u : GL (Fin 3) E) * g⁻¹)) * g := by
          rw [hc]
      _ = (w : GL (Fin 3) E) * (u : GL (Fin 3) E) := by group

end Frame

section Toral

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem natCard_subtype_eq_self {α : Type*} (a : α) : Nat.card {x : α // x = a} = 1 :=
  Nat.card_eq_one_iff_unique.mpr ⟨⟨fun x y => Subtype.ext (x.2.trans y.2.symm)⟩, ⟨⟨a, rfl⟩⟩⟩

omit [Finite K] [CharP K 2] in
theorem exists_toral_of_model {n : ℕ} (hn3 : 3 ≤ n) (h3 : 3 ∣ 2 ^ n + 1) {s : Om8 K}
    (hs3 : s ^ 3 = 1) {E : Type} [Field E] {hU : UnitaryFieldData 2 n E} {R : Type} [Group R]
    (Ψ : ↥(Subgroup.centralizer ({s} : Set (Om8 K))) ≃* R × ↥(unitaryIsom3 hU)) {ω : Eˣ}
    (hRc : ∀ a b : R, a * b = b * a) (hR3 : Nat.card {r : R // r ^ 3 = 1} = 3)
    (hω : IsPrimitiveRoot (ω : E) 3)
    (hJ : ∀ y : ↥(Subgroup.centralizer ({s} : Set (Om8 K))), (y : Om8 K) ∈ centDer s ↔
      (Ψ y).1 = 1 ∧ (((Ψ y).2 : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E).det = 1)
    (hs1 : (Ψ ⟨s, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩).1 = 1)
    (hs2 : ((Ψ ⟨s, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩).2 : GL (Fin 3) E) = scal ω)
    {g : GL (Fin 3) E} (hg : g ∈ unitaryIsom3 hU) :
    ∃ D V : Subgroup (Om8 K), D ≤ centDer s ∧
      (∀ x ∈ Subgroup.centralizer (D : Set (Om8 K)),
        ∀ y ∈ Subgroup.centralizer (D : Set (Om8 K)), x * y = y * x) ∧
      (∀ x : Om8 K, x ∈ V ↔ x ∈ Subgroup.centralizer (D : Set (Om8 K)) ∧ x ^ 3 = 1) ∧
      Nat.card V = 3 ^ 4 ∧ Nat.card ↥(V ⊓ D) = 3 ^ 2 ∧
      Nat.card ↥(V ⊓ Subgroup.centralizer (centDer s : Set (Om8 K))) = 3 ^ 2 ∧
      V ⊓ D ⊓ Subgroup.centralizer (centDer s : Set (Om8 K)) = Subgroup.zpowers s ∧
      ∀ u : ↥(Subgroup.centralizer ({s} : Set (Om8 K))),
        g * ((Ψ u).2 : GL (Fin 3) E) * g⁻¹ ∈ torusThree E →
          ∃ v ∈ V, ∀ j ∈ centDer s, (u : Om8 K) * j * (u : Om8 K)⁻¹ = v * j * v⁻¹ := by
  classical
  set s' : ↥(Subgroup.centralizer ({s} : Set (Om8 K))) :=
    ⟨s, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ with hs'
  have hω3 : ω ^ 3 = 1 := Units.ext (by simpa using hω.pow_eq_one)
  have hsU : ((Ψ s').2 : GL (Fin 3) E) ∈ sc E := by
    rw [hs2]
    exact scal_mem_sc ω
  have hsdet : (Ψ s').2 ∈ detOneU hU := by
    rw [mem_detOneU, hs2, ← diagGL_self, det_diagGL, ← Units.val_mul, ← Units.val_mul,
      ← pow_three', hω3, Units.val_one]
  set D : Subgroup (Om8 K) := pbSub Ψ ((⊥ : Subgroup R).prod (diagU hU g ⊓ detOneU hU))
    with hDdef
  have hDC : D ≤ Subgroup.centralizer ({s} : Set (Om8 K)) := pbSub_le _ _
  have hDmem : ∀ y : ↥(Subgroup.centralizer ({s} : Set (Om8 K))),
      (y : Om8 K) ∈ D ↔ (Ψ y).1 = 1 ∧ (Ψ y).2 ∈ diagU hU g ⊓ detOneU hU :=
    fun y => by rw [hDdef, coe_mem_pbSub, Subgroup.mem_prod, Subgroup.mem_bot]
  have hsD : s ∈ D := (hDmem s').mpr ⟨hs1, Subgroup.mem_inf.mpr ⟨scal_mem_diagU hU hsU, hsdet⟩⟩
  have hsJ : s ∈ centDer s := (hJ s').mpr ⟨hs1, (mem_detOneU hU).mp hsdet⟩
  have hJC : Subgroup.centralizer (centDer s : Set (Om8 K)) ≤
      Subgroup.centralizer ({s} : Set (Om8 K)) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hy s hsJ).symm
  have hCJ := mem_centralizer_centDer_iff_of_model hn3 Ψ hJ
  have hDJ : D ≤ centDer s := fun y hy => by
    obtain ⟨h1, h2⟩ := (hDmem ⟨y, hDC hy⟩).mp hy
    exact (hJ ⟨y, hDC hy⟩).mpr ⟨h1, (mem_detOneU hU).mp (Subgroup.mem_inf.mp h2).2⟩
  have hCDC : Subgroup.centralizer (D : Set (Om8 K)) ≤
      Subgroup.centralizer ({s} : Set (Om8 K)) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hy s hsD).symm
  have hCD : ∀ y : ↥(Subgroup.centralizer ({s} : Set (Om8 K))),
      (y : Om8 K) ∈ Subgroup.centralizer (D : Set (Om8 K)) ↔
      (Ψ y).2 ∈ diagU hU g := fun y => by
    rw [mem_centralizer_iff_of_mulEquiv Ψ (J := (D : Set (Om8 K)))
      (T := fun u => u ∈ diagU hU g ⊓ detOneU hU) (fun _ hz => hDC hz)
      (fun z => by rw [SetLike.mem_coe]; exact hDmem z) y]
    exact mem_diagU_iff_commute hU h3 hω hg (Ψ y).2
  have habel : ∀ a ∈ Subgroup.centralizer (D : Set (Om8 K)),
      ∀ b ∈ Subgroup.centralizer (D : Set (Om8 K)), a * b = b * a := by
    intro a ha b hb
    have ha' := (hCD ⟨a, hCDC ha⟩).mp ha
    have hb' := (hCD ⟨b, hCDC hb⟩).mp hb
    have : (⟨a, hCDC ha⟩ : ↥(Subgroup.centralizer ({s} : Set (Om8 K)))) * ⟨b, hCDC hb⟩ =
        ⟨b, hCDC hb⟩ * ⟨a, hCDC ha⟩ := by
      apply Ψ.injective
      rw [map_mul, map_mul]
      exact Prod.ext (hRc _ _) (diagU_commute hU ha' hb')
    exact congrArg Subtype.val this
  set V := torsion3 (Subgroup.centralizer (D : Set (Om8 K))) habel with hVdef
  have hVmem : ∀ x, x ∈ V ↔ x ∈ Subgroup.centralizer (D : Set (Om8 K)) ∧ x ^ 3 = 1 :=
    fun x => mem_torsion3
  have hVC : V ≤ Subgroup.centralizer ({s} : Set (Om8 K)) := fun x hx => hCDC hx.1
  have hVchar : ∀ y : ↥(Subgroup.centralizer ({s} : Set (Om8 K))), (y : Om8 K) ∈ V ↔
      (Ψ y).1 ^ 3 = 1 ∧ ((Ψ y).2 ∈ diagU hU g ∧ (Ψ y).2 ^ 3 = 1) := fun y => by
    rw [hVmem, hCD y, pow_three_eq_one_iff_of_mulEquiv Ψ y]
    tauto
  have hsV : s ∈ V := (hVmem s).mpr ⟨(hCD s').mpr (scal_mem_diagU hU hsU), hs3⟩
  have hsJ' : s ∈ Subgroup.centralizer (centDer s : Set (Om8 K)) := (hCJ s').mpr hsU
  refine ⟨D, V, hDJ, habel, hVmem, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hc := natCard_eq_mul_of_mulEquiv Ψ (S := (V : Set (Om8 K))) (fun _ hx => hVC hx)
      (P := fun r => r ^ 3 = 1)
      (P' := fun u => IsDiagGL (g * ((u : ↥(unitaryIsom3 hU)) : GL (Fin 3) E) * g⁻¹) ∧ u ^ 3 = 1)
      (fun y => by rw [SetLike.mem_coe, hVchar y, mem_diagU])
    rw [hR3, card_isDiagGL_conj_pow_three hU h3 hω hg] at hc
    rw [show Nat.card V = Nat.card (V : Set (Om8 K)) from rfl, hc]
    norm_num
  ·
    have hc := natCard_eq_mul_of_mulEquiv Ψ (S := ((V ⊓ D : Subgroup (Om8 K)) : Set (Om8 K)))
      (fun _ hx => hDC (Subgroup.mem_inf.mp hx).2) (P := fun r => r = 1)
      (P' := fun u => (IsDiagGL (g * ((u : ↥(unitaryIsom3 hU)) : GL (Fin 3) E) * g⁻¹) ∧
        (((u : ↥(unitaryIsom3 hU)) : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E).det = 1) ∧
          u ^ 3 = 1)
      (fun y => by
        rw [SetLike.mem_coe, Subgroup.mem_inf, hVchar y, hDmem y, Subgroup.mem_inf, mem_diagU,
          mem_detOneU]
        constructor
        · rintro ⟨⟨-, -, h3'⟩, h1, hd, hdet⟩
          exact ⟨h1, ⟨hd, hdet⟩, h3'⟩
        · rintro ⟨h1, ⟨hd, hdet⟩, h3'⟩
          exact ⟨⟨by rw [h1, one_pow], hd, h3'⟩, h1, hd, hdet⟩)
    rw [natCard_subtype_eq_self, card_isDiagGL_conj_det_pow_three hU h3 hω hg, one_mul] at hc
    exact hc
  ·
    have hc := natCard_eq_mul_of_mulEquiv Ψ
      (S := ((V ⊓ Subgroup.centralizer (centDer s : Set (Om8 K)) : Subgroup (Om8 K)) :
        Set (Om8 K)))
      (fun _ hx => hJC (Subgroup.mem_inf.mp hx).2) (P := fun r => r ^ 3 = 1)
      (P' := fun u => ((u : ↥(unitaryIsom3 hU)) : GL (Fin 3) E) ∈ sc E ∧ u ^ 3 = 1)
      (fun y => by
        rw [SetLike.mem_coe, Subgroup.mem_inf, hVchar y, hCJ y]
        constructor
        · rintro ⟨⟨h1, -, h3'⟩, hsc⟩
          exact ⟨h1, hsc, h3'⟩
        · rintro ⟨h1, hsc, h3'⟩
          exact ⟨⟨h1, scal_mem_diagU hU hsc, h3'⟩, hsc⟩)
    rw [hR3, card_scal_mem_unitaryIsom3_pow_three hU h3 hω] at hc
    exact hc
  ·
    apply le_antisymm
    · intro y hy
      obtain ⟨⟨hyV, hyD⟩, hyJ⟩ := Subgroup.mem_inf.mp hy |>.imp_left Subgroup.mem_inf.mp
      set z : ↥(Subgroup.centralizer ({s} : Set (Om8 K))) := ⟨y, hDC hyD⟩ with hz
      obtain ⟨h1, -⟩ := (hDmem z).mp hyD
      have hsc := (hCJ z).mp hyJ
      have h3' := ((hVchar z).mp hyV).2.2
      obtain ⟨c, hc⟩ := mem_sc_iff.mp hsc
      have hc3 : c ^ 3 = 1 := by
        apply scal_injective
        rw [scal_pow, scal_one, ← hc]
        have := congrArg Subtype.val h3'
        rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
      obtain ⟨i, -, hi⟩ := hω.eq_pow_of_pow_eq_one
        (show (c : E) ^ 3 = 1 by rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one])
      have hzi : z = s' ^ i := by
        apply Ψ.injective
        rw [map_pow]
        refine Prod.ext ?_ (Subtype.ext ?_)
        · rw [Prod.pow_fst, hs1, one_pow, h1]
        · rw [Prod.pow_snd, SubgroupClass.coe_pow, hs2, ← scal_pow, hc]
          congr 1
          exact Units.ext (by rw [Units.val_pow_eq_pow_val, hi])
      have : y = s ^ i := congrArg Subtype.val hzi
      rw [this]
      exact Subgroup.npow_mem_zpowers s i
    · exact Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hsV, hsD⟩, hsJ'⟩)
  ·
    intro u hu
    obtain ⟨a, b, c, hab, hbc, habc⟩ := hu
    have hb3 : (b * a⁻¹) ^ 3 = 1 := by rw [mul_pow, inv_pow, hab, mul_inv_cancel]
    have hc3 : (c * a⁻¹) ^ 3 = 1 := by rw [mul_pow, inv_pow, ← hbc, hab, mul_inv_cancel]
    set M₀ : ↥(unitaryIsom3 hU) := ⟨g⁻¹ * diagGL E 1 (b * a⁻¹) (c * a⁻¹) * g,
      conj_diagGL_mem hU h3 hg (one_pow 3) hb3 hc3⟩ with hM₀
    set v : ↥(Subgroup.centralizer ({s} : Set (Om8 K))) := Ψ.symm (1, M₀) with hv
    have hΨv : Ψ v = (1, M₀) := MulEquiv.apply_symm_apply _ _
    refine ⟨v, (hVchar v).mpr ?_, fun j hj => ?_⟩
    · rw [hΨv]
      refine ⟨one_pow 3, (mem_diagU hU).mpr ⟨1, b * a⁻¹, c * a⁻¹, by rw [hM₀]; group⟩,
        Subtype.ext ?_⟩
      rw [SubgroupClass.coe_pow, hM₀]
      change (g⁻¹ * diagGL E 1 (b * a⁻¹) (c * a⁻¹) * g) ^ 3 = 1
      rw [conj_diagGL_pow, one_pow, hb3, hc3, diagGL_one, mul_one, inv_mul_cancel]
    · have hu2 : ((Ψ u).2 : GL (Fin 3) E) = g⁻¹ * diagGL E a b c * g := by
        rw [← habc]
        group
      have hvu : ((v⁻¹ * u : ↥(Subgroup.centralizer ({s} : Set (Om8 K)))) : Om8 K) ∈
          Subgroup.centralizer (centDer s : Set (Om8 K)) := by
        rw [hCJ, map_mul, map_inv, hΨv, Prod.snd_mul, Prod.snd_inv, Subgroup.coe_mul,
          Subgroup.coe_inv, hu2, hM₀]
        change (g⁻¹ * diagGL E 1 (b * a⁻¹) (c * a⁻¹) * g)⁻¹ * (g⁻¹ * diagGL E a b c * g) ∈ sc E
        have e1 : (g⁻¹ * diagGL E 1 (b * a⁻¹) (c * a⁻¹) * g)⁻¹ * (g⁻¹ * diagGL E a b c * g) =
            g⁻¹ * ((diagGL E 1 (b * a⁻¹) (c * a⁻¹))⁻¹ * diagGL E a b c) * g := by group
        have e2 : (diagGL E 1 (b * a⁻¹) (c * a⁻¹))⁻¹ * diagGL E a b c = scal a := by
          rw [diagGL_inv, diagGL_mul, ← diagGL_self]
          congr 1 <;> group
        rw [e1, e2, (Subgroup.mem_center_iff.mp (sc_mem_center (scal_mem_sc a)) g⁻¹), mul_assoc,
          inv_mul_cancel, mul_one]
        exact scal_mem_sc a
      have hc := Subgroup.mem_centralizer_iff.mp hvu j hj
      rw [Subgroup.coe_mul, Subgroup.coe_inv] at hc
      calc (u : Om8 K) * j * (u : Om8 K)⁻¹ =
          v * (((v : Om8 K)⁻¹ * u) * j) * ((v : Om8 K)⁻¹ * u)⁻¹ * (v : Om8 K)⁻¹ := by group
        _ = v * (j * ((v : Om8 K)⁻¹ * u)) * ((v : Om8 K)⁻¹ * u)⁻¹ * (v : Om8 K)⁻¹ := by rw [← hc]
        _ = v * j * (v : Om8 K)⁻¹ := by group

end Toral

end D4Inner

end CFSG.StandardType

end
