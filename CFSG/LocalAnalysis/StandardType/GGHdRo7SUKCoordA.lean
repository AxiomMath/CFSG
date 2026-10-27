module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SULCoordModelA
import CFSG.LocalAnalysis.StandardType.GGHdRo7CoprimeSplit

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C
open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def hdRo7SUKCoordAux_rowRank {G : Type} [Group G] {p : ℕ} {J K : Subgroup G}
    (hrow : GGResRowAt ggRowSUCorank2 p J K) : ℕ :=
  (Classical.choose (Classical.choose_spec hrow)).rank + 1

theorem hdRo7SUKCoordAux_rowRank_spec {G : Type} [Group G] {p : ℕ} {J K : Subgroup G}
    (hrow : GGResRowAt ggRowSUCorank2 p J K) :
    p = 3 ∧ 7 ≤ hdRo7SUKCoordAux_rowRank hrow ∧
      ¬ 3 ∣ hdRo7SUKCoordAux_rowRank hrow := by
  have h := (Classical.choose_spec (Classical.choose_spec hrow)).2.2.2.2
  obtain ⟨hp, -, -, -, -, -, h6, h3⟩ := h
  exact ⟨hp, by
    show 7 ≤ (Classical.choose (Classical.choose_spec hrow)).rank + 1
    omega, h3⟩

theorem hdRo7SUKCoordAux_rowRank_eq {G : Type} [Group G] {p : ℕ} {J K : Subgroup G}
    (hrow : GGResRowAt ggRowSUCorank2 p J K) :
    hdRo7SUKCoordAux_rowRank hrow = (Classical.choose (Classical.choose_spec hrow)).rank + 1 :=
  rfl

theorem hdRo7SUKCoordAux_markingData {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hrow : GGResRowAt ggRowSUCorank2 p J K) :
    ∃ (m : ℕ) (F : Type) (_ : Field F) (_ : Finite F)
      (θ : (↥K ⧸ Subgroup.center ↥K) ≃* LargeEvenProj (LargeEvenSUGroup (Fin m) F 2))
      (I : Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin m) F 2)))),
      Nat.card F = 4 ∧ 3 ≤ m ∧ ¬ 3 ∣ m ∧ Bs ≤ Subgroup.normalizer (K : Set G) ∧
      (∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) := by
  let labK := Classical.choose (Classical.choose_spec hrow)
  have hspec := Classical.choose_spec (Classical.choose_spec hrow)
  have hlabK : LargeEvenInLambda2 labK := hspec.2.1
  have hKlab : GGHasLabel labK (↥K ⧸ Subgroup.center ↥K) := hspec.2.2.2.1
  have hrowData : ggRowSUCorank2 p (Classical.choose hrow) labK := hspec.2.2.2.2
  obtain ⟨-, -, -, hKtag, hKn, -, hrank6, h3m⟩ := hrowData
  have hnbr : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hmark := ggInnerDiagOn_relabel hRig (hH.2.2.1.2 y K hnbr) hlabK hKlab
  obtain ⟨-, lab', hlab', hraw⟩ := hmark
  obtain ⟨R₀, iR₀, I₀, F₀, -, -, θ₀, hP₀⟩ := largeEvenRawDatum_exists hraw
  have hEq : lab' = labK := hP₀.1
  rw [hEq] at hraw hP₀
  obtain ⟨Fld, hFld, hFldfin, hFldcard, hQ⟩ :=
    hdRo7SULCoordAux_twA_rawLegacy_one hKtag hKn hraw
  obtain ⟨-, -, θ, hP⟩ := hQ
  exact ⟨hdRo7SUKCoordAux_rowRank hrow, Fld, hFld, hFldfin, θ,
    LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin (hdRo7SUKCoordAux_rowRank hrow)) Fld 2))
      (LargeEvenGUSet (Fin (hdRo7SUKCoordAux_rowRank hrow)) Fld 2), hFldcard,
    by rw [show hdRo7SUKCoordAux_rowRank hrow = labK.rank + 1 from rfl]; omega,
    h3m, hP.2.1, hP.2.2⟩

theorem hdRo7SUKCoordAux_markingData_rowRank {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hrow : GGResRowAt ggRowSUCorank2 p J K) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F)
      (θ : (↥K ⧸ Subgroup.center ↥K) ≃*
        LargeEvenProj (LargeEvenSUGroup (Fin (hdRo7SUKCoordAux_rowRank hrow)) F 2))
      (I : Set (MulAut (LargeEvenProj
        (LargeEvenSUGroup (Fin (hdRo7SUKCoordAux_rowRank hrow)) F 2)))),
      Nat.card F = 4 ∧ 3 ≤ hdRo7SUKCoordAux_rowRank hrow ∧
        ¬ 3 ∣ hdRo7SUKCoordAux_rowRank hrow ∧ Bs ≤ Subgroup.normalizer (K : Set G) ∧
        (∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) := by
  let labK := Classical.choose (Classical.choose_spec hrow)
  have hspec := Classical.choose_spec (Classical.choose_spec hrow)
  have hlabK : LargeEvenInLambda2 labK := hspec.2.1
  have hKlab : GGHasLabel labK (↥K ⧸ Subgroup.center ↥K) := hspec.2.2.2.1
  have hrowData : ggRowSUCorank2 p (Classical.choose hrow) labK := hspec.2.2.2.2
  obtain ⟨-, -, -, hKtag, hKn, -, hrank6, h3m⟩ := hrowData
  have hnbr : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hmark := ggInnerDiagOn_relabel hRig (hH.2.2.1.2 y K hnbr) hlabK hKlab
  obtain ⟨-, lab', hlab', hraw⟩ := hmark
  obtain ⟨R₀, iR₀, I₀, F₀, -, -, θ₀, hP₀⟩ := largeEvenRawDatum_exists hraw
  have hEq : lab' = labK := hP₀.1
  rw [hEq] at hraw hP₀
  obtain ⟨Fld, hFld, hFldfin, hFldcard, hQ⟩ :=
    hdRo7SULCoordAux_twA_rawLegacy_one hKtag hKn hraw
  obtain ⟨-, -, θ, hP⟩ := hQ
  exact ⟨Fld, hFld, hFldfin, θ,
    LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin (hdRo7SUKCoordAux_rowRank hrow)) Fld 2))
      (LargeEvenGUSet (Fin (hdRo7SUKCoordAux_rowRank hrow)) Fld 2), hFldcard,
    by rw [show hdRo7SUKCoordAux_rowRank hrow = labK.rank + 1 from rfl]; omega,
    h3m, hP.2.1, hP.2.2⟩

theorem hdRo7SUKCoordAux_centerCoprime
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hrow : GGResRowAt ggRowSUCorank2 p J K) :
    Nat.Coprime 3 (Nat.card (Subgroup.center ↥K)) := by
  obtain ⟨m, F, hF, hFfin, θ, I, hFcard, hm3, hm3d, -, -⟩ :=
    hdRo7SUKCoordAux_markingData hH hRig hrow
  have hperf : commutator ↥K = ⊤ := (hH.2.2.1.2 y K hH.2.2.2.2.1).1
  have hdq : (m, 2 ^ 1) ≠ (3, 2) := by
    rintro ⟨hm, -⟩
    omega
  have hK : Nat.card F = (2 ^ 1) ^ 2 := by rw [hFcard]; norm_num
  have hcp : GGCenterPrime 3 (LargeEvenProj (LargeEvenSUGroup (Fin m) F (2 ^ 1))) :=
    StdSubRestU.ggCenterPrime_unitary hK le_rfl hm3 hdq Nat.prime_three (by norm_num) hm3d
  have hcpK : GGCenterPrime 3 (↥K ⧸ Subgroup.center ↥K) :=
    hdRo7SULCoordAux_centerPrime_equiv θ.symm hcp
  have hnot : ¬ 3 ∣ Nat.card (Subgroup.center ↥K) :=
    hcpK ↥K (QuotientGroup.mk' (Subgroup.center ↥K)) (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']) hperf
  exact (Nat.prime_three.coprime_iff_not_dvd).mpr hnot

theorem hdRo7SUKCoordAux_axisCentral {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) :
    y ∈ Bs ⊓ Subgroup.centralizer (K : Set G) := by
  have hSHat : LargeEvenSHat p B y K := hH.2.2.2.2.1.1
  have hyBs : y ∈ Bs := hH.1.2.1.1 hSHat.2.1
  have hKC : K ≤ Subgroup.centralizer ({y} : Set G) := hSHat.2.2.2.1
  refine ⟨hyBs, ?_⟩
  change y ∈ Subgroup.centralizer (K : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact (Subgroup.mem_centralizer_iff.mp (hKC hk) y (Set.mem_singleton y)).symm

private noncomputable def hdRo7SUKCoordAux_conjAut {G : Type} [Group G] (K : Subgroup G)
    (g : G) (hg : g ∈ Subgroup.normalizer (K : Set G)) : MulAut ↥K where
  toFun y := ⟨g * (y : G) * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg (y : G)).mp y.2⟩
  invFun y := ⟨g⁻¹ * (y : G) * g, by
    simpa only [inv_inv] using
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (K : Set G)).inv_mem hg) (y : G)).mp y.2⟩
  left_inv y := Subtype.ext (by simp only [inv_inv]; group)
  right_inv y := Subtype.ext (by group)
  map_mul' y z := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem hdRo7SUKCoordAux_innerAction {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hrow : GGResRowAt ggRowSUCorank2 p J K) :
    ∀ b ∈ Bs, ∃ x ∈ K, ∀ y ∈ K, b * y * b⁻¹ = x * y * x⁻¹ := by
  obtain ⟨labJ, labK, -, hlabK, -, hKlab, hrowData⟩ := hrow
  obtain ⟨-, -, -, hKtag, hKn, -, hrank6, h3m⟩ := hrowData
  have hnbr : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hmark := ggInnerDiagOn_relabel hRig (hH.2.2.1.2 y K hnbr) hlabK hKlab
  obtain ⟨-, lab', hlab', hraw⟩ := hmark
  obtain ⟨R₀, iR₀, I₀, F₀, -, -, θ₀, hP₀⟩ := largeEvenRawDatum_exists hraw
  have hEq : lab' = labK := hP₀.1
  rw [hEq] at hraw hP₀
  obtain ⟨Fld, hFld, hFldfin, hFldcard, hQ⟩ :=
    hdRo7SULCoordAux_twA_rawLegacy_one hKtag hKn hraw
  obtain ⟨-, -, θ, hP⟩ := hQ
  have hperf : commutator ↥K = ⊤ := (hH.2.2.1.2 y K hnbr).1
  have hF2 : Nat.card Fld = (2 ^ 1) ^ 2 := by rw [hFldcard]; norm_num
  have hcop : (2 ^ 1 + 1).Coprime (labK.rank + 1) := by
    rw [pow_one]
    exact (Nat.prime_three.coprime_iff_not_dvd).mpr h3m
  have hIinn := TableB.matConjImage_gu_subset_inn hF2 hcop
  intro b hb
  have hbN : b ∈ Subgroup.normalizer (K : Set G) := hP.2.1 hb
  have hbNin : b⁻¹ ∈ Subgroup.normalizer (K : Set G) := (Subgroup.normalizer (K : Set G)).inv_mem hbN
  obtain ⟨φ, hφI, hφ⟩ := hP.2.2 b hb
  obtain ⟨w, hw⟩ := hIinn hφI
  obtain ⟨kq, hkq⟩ := θ.surjective w
  obtain ⟨k₀, hk₀⟩ := QuotientGroup.mk_surjective kq
  have hkqw : θ (QuotientGroup.mk k₀) = w := by rw [hk₀, hkq]
  have hcong : ∀ z : ↥K,
      (QuotientGroup.mk (k₀ * z * k₀⁻¹) : ↥K ⧸ Subgroup.center ↥K) =
      (QuotientGroup.mk (⟨b⁻¹ * (z : G) * b,
        by simpa only [inv_inv] using
          (Subgroup.mem_normalizer_iff.mp hbNin (z : G)).mp z.2⟩ : ↥K) :
        ↥K ⧸ Subgroup.center ↥K) := by
    intro z
    refine θ.injective ?_
    have h1 := hφ z ⟨b⁻¹ * (z : G) * b,
      by simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp hbNin (z : G)).mp z.2⟩ rfl
    rw [← hw] at h1
    rw [← h1, MulAut.conj_apply, ← hkqw]
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
  refine ⟨(k₀ : G)⁻¹, K.inv_mem k₀.2, ?_⟩
  intro y' hy'
  let yK : ↥K := ⟨y', hy'⟩
  have hmem : (k₀ : G) * b ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.mul_mem _ (Subgroup.le_normalizer k₀.2) hbN
  have hZ : ∀ z : ↥K, hdRo7SUKCoordAux_conjAut K ((k₀ : G) * b) hmem z * z⁻¹ ∈
      Subgroup.center ↥K := by
    intro z
    let a : ↥K := ⟨(k₀ : G) * b * (z : G) * ((k₀ : G) * b)⁻¹,
      (Subgroup.mem_normalizer_iff.mp hmem (z : G)).mp z.2⟩
    have hbz : b * (z : G) * b⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hbN (z : G)).mp z.2
    have hc := hcong ⟨b * (z : G) * b⁻¹, hbz⟩
    rw [QuotientGroup.eq] at hc
    have hc' : a⁻¹ * z ∈ Subgroup.center ↥K := by
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
    show hdRo7SUKCoordAux_conjAut K ((k₀ : G) * b) hmem z * z⁻¹ ∈ Subgroup.center ↥K
    rw [show hdRo7SUKCoordAux_conjAut K ((k₀ : G) * b) hmem z = a from rfl, h1]
    exact (Subgroup.center ↥K).inv_mem hc'
  have hg1 := hdRo7SULCoordAux_modCenter_eq_one hperf _ hZ
  have hy1 : (k₀ : G) * b * y' * ((k₀ : G) * b)⁻¹ = y' := by
    have h := congrArg (fun f : MulAut ↥K => (f yK : G)) hg1
    simp only [MulAut.one_apply] at h
    rwa [show (↑(hdRo7SUKCoordAux_conjAut K ((k₀ : G) * b) hmem yK) : G) =
        (k₀ : G) * b * y' * ((k₀ : G) * b)⁻¹ from rfl] at h
  calc b * y' * b⁻¹
      = (k₀ : G)⁻¹ * ((k₀ : G) * b * y' * ((k₀ : G) * b)⁻¹) * k₀ := by group
    _ = (k₀ : G)⁻¹ * y' * k₀ := by rw [hy1]
    _ = (k₀ : G)⁻¹ * y' * ((k₀ : G)⁻¹)⁻¹ := by group

theorem hdRo7SUKCoordAux_split
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hrow : GGResRowAt ggRowSUCorank2 p J K) :
    ∀ b ∈ Bs, ∃ t ∈ Bs ⊓ K,
      ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = t * c := by
  have hrowc := hrow
  obtain ⟨labJ, labK, -, -, -, -, hrowData⟩ := hrowc
  have hp3 : p = 3 := hrowData.1
  have hp : p.Prime := by rw [hp3]; exact Nat.prime_three
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥K)) := by
    rw [hp3]
    exact hdRo7SUKCoordAux_centerCoprime hH hRig hrow
  obtain ⟨-, -, -, -, -, -, -, -, -, hnorm, -⟩ := hdRo7SUKCoordAux_markingData hH hRig hrow
  exact ggBstar_split_of_inner_coprime hp hH.1.2.1 hcop hnorm
    (hdRo7SUKCoordAux_innerAction hH hRig hrow)

end CFSG.StandardType.HdRo7SU