module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SULCoordSplit
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestUnitaryCenter
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CoprimeSplit

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C
open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7SULCoordAux_twA_rawLegacy {lab : LargeEvenLabel} (htag : lab.tag = .twA)
    {Q : LargeEvenRawCont} (h : LargeEvenRawDatumLegacy lab Q) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ lab.n) ^ 2 ∧
      Q (LargeEvenProj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)))
        (LargeEvenMatConjImage
          (LargeEvenProjMk (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)))
          (LargeEvenGUSet (Fin (lab.rank + 1)) K (2 ^ lab.n)))
        (LargeEvenMatFieldImage
          (LargeEvenProjMk (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)))) := by
  simp only [LargeEvenRawDatumLegacy, htag] at h
  exact h

theorem hdRo7SULCoordAux_twA_rawLegacy_one {lab : LargeEvenLabel} (htag : lab.tag = .twA)
    (hn : lab.n = 1) {Q : LargeEvenRawCont} (h : LargeEvenRawDatumLegacy lab Q) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
      Q (LargeEvenProj (LargeEvenSUGroup (Fin (lab.rank + 1)) K 2))
        (LargeEvenMatConjImage
          (LargeEvenProjMk (LargeEvenSUGroup (Fin (lab.rank + 1)) K 2))
          (LargeEvenGUSet (Fin (lab.rank + 1)) K 2))
        (LargeEvenMatFieldImage
          (LargeEvenProjMk (LargeEvenSUGroup (Fin (lab.rank + 1)) K 2))) := by
  obtain ⟨K, hK, hKfin, hKcard, hQ⟩ := hdRo7SULCoordAux_twA_rawLegacy htag h
  have hq : 2 ^ lab.n = 2 := by rw [hn, pow_one]
  exact ⟨K, hK, hKfin, by rw [hKcard, hq]; norm_num, hq ▸ hQ⟩

theorem hdRo7SULCoordAux_markingDataCfg {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hH : GGHdRo7SULCoordHyp p B Bs x L D J) (hRig : GGLabelRigidInput)
    (hrow : GGHdRo7SULabL p L) :
    ∃ (m : ℕ) (F : Type) (_ : Field F) (_ : Finite F)
      (θ : (↥L ⧸ Subgroup.center ↥L) ≃* LargeEvenProj (LargeEvenSUGroup (Fin m) F 2))
      (I : Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin m) F 2)))),
      Nat.card F = 4 ∧ 7 ≤ m ∧ ¬ 3 ∣ m ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
      (∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) ∧
      I ⊆ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin m) F 2)) (LargeEvenGUSet (Fin m) F 2) := by
  obtain ⟨labL, hlabL, hLlab, -, hLtag, hLn, hrank6, h3m⟩ := hrow
  have hmark := ggInnerDiagOn_relabel hRig hH.2.2.1.1 hlabL hLlab
  obtain ⟨-, lab', hlab', hraw⟩ := hmark
  obtain ⟨R₀, iR₀, I₀, F₀, -, -, θ₀, hP₀⟩ := largeEvenRawDatum_exists hraw
  have hEq : lab' = labL := hP₀.1
  rw [hEq] at hraw hP₀
  obtain ⟨Fld, hFld, hFldfin, hFldcard, hQ⟩ :=
    hdRo7SULCoordAux_twA_rawLegacy_one hLtag hLn hraw
  obtain ⟨-, -, θ, hP⟩ := hQ
  exact ⟨labL.rank + 1, Fld, hFld, hFldfin, θ,
    LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin (labL.rank + 1)) Fld 2))
      (LargeEvenGUSet (Fin (labL.rank + 1)) Fld 2), hFldcard, by omega, h3m, hP.2.1, hP.2.2,
    (fun _ hx => hx)⟩

theorem hdRo7SULCoordAux_centerPrime_equiv {p : ℕ} {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') (h : GGCenterPrime p R) : GGCenterPrime p R' := by
  intro L' _ _ ψ hψ hker hperf
  refine h L' (e.symm.toMonoidHom.comp ψ) (e.symm.surjective.comp hψ) ?_ hperf
  intro z hz
  exact hker (by
    have h1 : e.symm (ψ z) = 1 := hz
    exact e.symm.injective (by rw [h1, map_one]))

theorem hdRo7SULCoordAux_centerCoprimeCfg
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hH : GGHdRo7SULCoordHyp p B Bs x L D J) (hRig : GGLabelRigidInput)
    (hrow : GGHdRo7SULabL p L) :
    Nat.Coprime 3 (Nat.card (Subgroup.center ↥L)) := by
  obtain ⟨m, F, hF, hFfin, θ, I, hFcard, hm3, hm3d, -, -, -⟩ := hdRo7SULCoordAux_markingDataCfg hH hRig hrow
  have hperf : commutator ↥L = ⊤ := hH.2.2.1.1.1
  have hdq : (m, 2 ^ 1) ≠ (3, 2) := by
    rintro ⟨hm, -⟩
    omega
  have hK : Nat.card F = (2 ^ 1) ^ 2 := by rw [hFcard]; norm_num
  have hcp : GGCenterPrime 3 (LargeEvenProj (LargeEvenSUGroup (Fin m) F (2 ^ 1))) :=
    StdSubRestU.ggCenterPrime_unitary hK le_rfl (by omega) hdq Nat.prime_three (by norm_num) hm3d
  have hcpL : GGCenterPrime 3 (↥L ⧸ Subgroup.center ↥L) :=
    hdRo7SULCoordAux_centerPrime_equiv θ.symm hcp
  have hnot : ¬ 3 ∣ Nat.card (Subgroup.center ↥L) :=
    hcpL ↥L (QuotientGroup.mk' (Subgroup.center ↥L)) (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']) hperf
  exact (Nat.prime_three.coprime_iff_not_dvd).mpr hnot

theorem hdRo7SULCoordAux_inf_center_eq_botCfg
    {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hH : GGHdRo7SULCoordHyp p B Bs x L D J) (hRig : GGLabelRigidInput)
    (hrow : GGHdRo7SULabL p L) :
    ∀ z ∈ Bs, z ∈ L → z ∈ Subgroup.centralizer (L : Set G) → z = 1 := by
  obtain ⟨-, -, hp3, -, -⟩ := hdRo7SULCoordAux_rowDataCfg hH hrow
  have hp : Nat.Prime p := by rw [hp3]; exact Nat.prime_three
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) := by
    rw [hp3]; exact hdRo7SULCoordAux_centerCoprimeCfg hH hRig hrow
  have hCeq := hdRo7SULCoordAux_centralizerCfg hH hp3
  obtain ⟨-, -, -, -, -, -, hSStar, -⟩ := hH.1.1
  have hxne : x ≠ 1 := hSStar.2.2.1
  have hxBs : x ∈ Bs := hH.1.2.1.1 hSStar.2.1
  have hxp : x ^ p = 1 := hH.1.2.1.2.1.2 x hxBs
  have hordx : orderOf x = p := orderOf_eq_prime hxp hxne
  intro z hzB hzL hzC
  have hzx : z ∈ Subgroup.zpowers x := by
    rw [← hCeq]; exact ⟨hzB, hzC⟩
  have hordp : orderOf z ∣ p := by
    have h1 : orderOf (⟨z, hzx⟩ : Subgroup.zpowers x) ∣ Nat.card ↥(Subgroup.zpowers x) :=
      orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk, Nat.card_zpowers, hordx] at h1
  have hzcen : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hzC (w : G) w.2
  have hordZ : orderOf z ∣ Nat.card (Subgroup.center ↥L) := by
    have h1 : orderOf (⟨⟨z, hzL⟩, hzcen⟩ : Subgroup.center ↥L) ∣
        Nat.card ↥(Subgroup.center ↥L) := orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at h1
  have hg1 : orderOf z = 1 := by
    have h2 : orderOf z ∣ p.gcd (Nat.card (Subgroup.center ↥L)) := Nat.dvd_gcd hordp hordZ
    rw [hcop.gcd_eq_one] at h2
    exact Nat.dvd_one.mp h2
  exact orderOf_eq_one_iff.mp hg1

theorem hdRo7SULCoordAux_modCenter_eq_one {L : Type} [Group L]
    (hperf : commutator L = ⊤) (g : MulAut L)
    (hg : ∀ y : L, g y * y⁻¹ ∈ Subgroup.center L) : g = 1 := by
  let k : L →* L := MonoidHom.mk' (fun y => g y * y⁻¹) (fun y z => by
    have hc : g z * z⁻¹ ∈ Subgroup.center L := hg z
    rw [map_mul]
    calc g y * g z * (y * z)⁻¹ = g y * (g z * z⁻¹) * y⁻¹ := by group
      _ = g y * ((g z * z⁻¹) * y⁻¹) := by rw [mul_assoc]
      _ = g y * (y⁻¹ * (g z * z⁻¹)) := by
            rw [show (g z * z⁻¹) * y⁻¹ = y⁻¹ * (g z * z⁻¹) from
              (Subgroup.mem_center_iff.mp hc y⁻¹).symm]
      _ = g y * y⁻¹ * (g z * z⁻¹) := by rw [mul_assoc])
  have hkker : k.ker = ⊤ := by
    rw [eq_top_iff]
    have hle : commutator L ≤ k.ker := by
      unfold commutator
      rw [Subgroup.commutator_le]
      intro x _ z _
      rw [MonoidHom.mem_ker]
      have hx : k x ∈ Subgroup.center L := hg x
      have hz : k z ∈ Subgroup.center L := hg z
      have hcomm : k x * k z = k z * k x := (Subgroup.mem_center_iff.mp hx (k z)).symm
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.mpr hcomm
    rwa [hperf] at hle
  ext y
  have hy : y ∈ k.ker := by rw [hkker]; trivial
  have h1 : k y = 1 := MonoidHom.mem_ker.mp hy
  show g y = y
  have h2 := h1
  simp only [k, MonoidHom.mk'_apply] at h2
  exact mul_inv_eq_one.mp h2

noncomputable def hdRo7SULCoordAux_conjAut {G : Type} [Group G] (L : Subgroup G)
    (g : G) (hg : g ∈ Subgroup.normalizer (L : Set G)) : MulAut ↥L where
  toFun y := ⟨g * (y : G) * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg (y : G)).mp y.2⟩
  invFun y := ⟨g⁻¹ * (y : G) * g, by
    simpa only [inv_inv] using
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (L : Set G)).inv_mem hg) (y : G)).mp y.2⟩
  left_inv y := Subtype.ext (by simp only [inv_inv]; group)
  right_inv y := Subtype.ext (by group)
  map_mul' y z := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem hdRo7SULCoordAux_innerActionCfg {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hH : GGHdRo7SULCoordHyp p B Bs x L D J) (hRig : GGLabelRigidInput)
    (hrow : GGHdRo7SULabL p L) :
    ∀ b ∈ Bs, ∃ x ∈ L, ∀ y ∈ L, b * y * b⁻¹ = x * y * x⁻¹ := by
  obtain ⟨labL, hlabL, hLlab, -, hLtag, hLn, hrank6, h3m⟩ := hrow
  have hmark := ggInnerDiagOn_relabel hRig hH.2.2.1.1 hlabL hLlab
  obtain ⟨-, lab', hlab', hraw⟩ := hmark
  obtain ⟨R₀, iR₀, I₀, F₀, -, -, θ₀, hP₀⟩ := largeEvenRawDatum_exists hraw
  have hEq : lab' = labL := hP₀.1
  rw [hEq] at hraw hP₀
  obtain ⟨Fld, hFld, hFldfin, hFldcard, hQ⟩ :=
    hdRo7SULCoordAux_twA_rawLegacy_one hLtag hLn hraw
  obtain ⟨-, -, θ, hP⟩ := hQ
  have hperf : commutator ↥L = ⊤ := hH.2.2.1.1.1
  have hF2 : Nat.card Fld = (2 ^ 1) ^ 2 := by rw [hFldcard]; norm_num
  have hcop : (2 ^ 1 + 1).Coprime (labL.rank + 1) := by
    rw [pow_one]
    exact (Nat.prime_three.coprime_iff_not_dvd).mpr h3m
  have hIinn := TableB.matConjImage_gu_subset_inn hF2 hcop
  intro b hb
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := hP.2.1 hb
  have hbNin : b⁻¹ ∈ Subgroup.normalizer (L : Set G) := (Subgroup.normalizer (L : Set G)).inv_mem hbN
  obtain ⟨φ, hφI, hφ⟩ := hP.2.2 b hb
  obtain ⟨w, hw⟩ := hIinn hφI
  obtain ⟨lq, hlq⟩ := θ.surjective w
  obtain ⟨l₀, hl₀⟩ := QuotientGroup.mk_surjective lq
  have hlqw : θ (QuotientGroup.mk l₀) = w := by rw [hl₀, hlq]
  have hcong : ∀ z : ↥L,
      (QuotientGroup.mk (l₀ * z * l₀⁻¹) : ↥L ⧸ Subgroup.center ↥L) =
      (QuotientGroup.mk (⟨b⁻¹ * (z : G) * b,
        by simpa only [inv_inv] using
          (Subgroup.mem_normalizer_iff.mp hbNin (z : G)).mp z.2⟩ : ↥L) :
        ↥L ⧸ Subgroup.center ↥L) := by
    intro z
    refine θ.injective ?_
    have h1 := hφ z ⟨b⁻¹ * (z : G) * b,
      by simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp hbNin (z : G)).mp z.2⟩ rfl
    rw [← hw] at h1
    rw [← h1, MulAut.conj_apply, ← hlqw]
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
  refine ⟨(l₀ : G)⁻¹, L.inv_mem l₀.2, ?_⟩
  intro y hy
  let yL : ↥L := ⟨y, hy⟩
  have hmem : (l₀ : G) * b ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ (Subgroup.le_normalizer l₀.2) hbN
  have hZ : ∀ z : ↥L, hdRo7SULCoordAux_conjAut L ((l₀ : G) * b) hmem z * z⁻¹ ∈
      Subgroup.center ↥L := by
    intro z
    let a : ↥L := ⟨(l₀ : G) * b * (z : G) * ((l₀ : G) * b)⁻¹,
      (Subgroup.mem_normalizer_iff.mp hmem (z : G)).mp z.2⟩
    have hbz : b * (z : G) * b⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hbN (z : G)).mp z.2
    have hc := hcong ⟨b * (z : G) * b⁻¹, hbz⟩
    rw [QuotientGroup.eq] at hc
    have hc' : a⁻¹ * z ∈ Subgroup.center ↥L := by
      convert hc using 1
      apply Subtype.ext
      simp only [a, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have h1 : a * z⁻¹ = (a⁻¹ * z)⁻¹ := by
      rw [show a * z⁻¹ = (z * a⁻¹)⁻¹ by group]
      congr 1
      have h := Subgroup.mem_center_iff.mp hc' a⁻¹
      rw [mul_assoc] at h
      exact (mul_left_cancel h).symm
    show hdRo7SULCoordAux_conjAut L ((l₀ : G) * b) hmem z * z⁻¹ ∈ Subgroup.center ↥L
    rw [show hdRo7SULCoordAux_conjAut L ((l₀ : G) * b) hmem z = a from rfl, h1]
    exact (Subgroup.center ↥L).inv_mem hc'
  have hg1 := hdRo7SULCoordAux_modCenter_eq_one hperf _ hZ
  have hy1 : (l₀ : G) * b * y * ((l₀ : G) * b)⁻¹ = y := by
    have h := congrArg (fun f : MulAut ↥L => (f yL : G)) hg1
    simp only [MulAut.one_apply] at h
    rwa [show (↑(hdRo7SULCoordAux_conjAut L ((l₀ : G) * b) hmem yL) : G) =
        (l₀ : G) * b * y * ((l₀ : G) * b)⁻¹ from rfl] at h
  calc b * y * b⁻¹
      = (l₀ : G)⁻¹ * ((l₀ : G) * b * y * ((l₀ : G) * b)⁻¹) * l₀ := by group
    _ = (l₀ : G)⁻¹ * y * l₀ := by rw [hy1]
    _ = (l₀ : G)⁻¹ * y * ((l₀ : G)⁻¹)⁻¹ := by group

theorem hdRo7SULCoordAux_splitCfg
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hH : GGHdRo7SULCoordHyp p B Bs x L D J) (hRig : GGLabelRigidInput)
    (hrow : GGHdRo7SULabL p L) :
    ∀ b ∈ Bs, ∃ t ∈ Bs ⊓ L,
      ∃ c ∈ Bs ⊓ Subgroup.centralizer (L : Set G), b = t * c := by
  have hinner := hdRo7SULCoordAux_innerActionCfg hH hRig hrow
  obtain ⟨-, -, -, -, -, -, -, -, -, hnorm, -, -⟩ := hdRo7SULCoordAux_markingDataCfg hH hRig hrow
  have hcop0 := hdRo7SULCoordAux_centerCoprimeCfg hH hRig hrow
  obtain ⟨-, -, hp3, -, -⟩ := hdRo7SULCoordAux_rowDataCfg hH hrow
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) := by
    rw [hp3]
    exact hcop0
  exact ggBstar_split_of_inner_coprime (GGConfig.tableB_facts hH.1).1
    hH.1.2.1 hcop hnorm hinner

end CFSG.StandardType.HdRo7SU
