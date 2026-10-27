module

public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrameLDefs
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerRigid
public import CFSG.GroupTheory.CoprimeConjNormalizer
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.ClassicalInvolution.Phan

variable {G : Type} [Group G] {Bs L : Subgroup G}

theorem exists_bstar_conj_eq_commutator (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {n : ↥L}
    (hn : MulAut.conj n ∈ Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L)))
    {b : G} (hb : b ∈ Bs) :
    (n : G) * b * (n : G)⁻¹ * b⁻¹ ∈ L ∧ ∃ β ∈ Bs, ∀ l ∈ L,
      β * l * β⁻¹ = ((n : G) * b * (n : G)⁻¹ * b⁻¹) * l * ((n : G) * b * (n : G)⁻¹ * b⁻¹)⁻¹ := by
  classical
  have hmem : MulAut.conj n * ggGamma L hN ⟨b, hb⟩ * (MulAut.conj n)⁻¹ ∈
      (ggGamma L hN).range :=
    (Subgroup.mem_normalizer_iff.mp hn (ggGamma L hN ⟨b, hb⟩)).mp
      (MonoidHom.mem_range.mpr ⟨⟨b, hb⟩, rfl⟩)
  obtain ⟨β, hβ⟩ := MonoidHom.mem_range.mp hmem
  have hkey : ∀ x : ↥L,
      (β : G) * (x : G) * (β : G)⁻¹ =
        ((n : G) * b * (n : G)⁻¹) * (x : G) * ((n : G) * b * (n : G)⁻¹)⁻¹ := by
    intro x
    have hx := congrArg (fun y : ↥L => (y : G)) (DFunLike.congr_fun hβ x)
    rw [ggGamma_coe L hN β x] at hx
    refine hx.trans ?_
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, ggGamma_coe,
      MulEquiv.coe_toMonoidHom, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hbnL : b * (n : G)⁻¹ * b⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (hN hb) (n : G)⁻¹).mp (L.inv_mem n.2)
  have hl0 : (n : G) * b * (n : G)⁻¹ * b⁻¹ ∈ L := by
    have h := L.mul_mem n.2 hbnL
    simpa only [mul_assoc] using h
  refine ⟨hl0, (β : G) * b⁻¹, Bs.mul_mem β.2 (Bs.inv_mem hb), fun l hl => ?_⟩
  have hbLl : b⁻¹ * l * b ∈ L := by
    have h :=
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (L : Set G)).inv_mem (hN hb)) l).mp hl
    simpa only [inv_inv] using h
  calc
    ((β : G) * b⁻¹) * l * ((β : G) * b⁻¹)⁻¹
        = (β : G) * (b⁻¹ * l * b) * (β : G)⁻¹ := by group
    _ = ((n : G) * b * (n : G)⁻¹) * (b⁻¹ * l * b) *
          ((n : G) * b * (n : G)⁻¹)⁻¹ := hkey ⟨b⁻¹ * l * b, hbLl⟩
    _ = ((n : G) * b * (n : G)⁻¹ * b⁻¹) * l *
          ((n : G) * b * (n : G)⁻¹ * b⁻¹)⁻¹ := by group

section FrameKernel

variable {p : ℕ} {B Bs L D J : Subgroup G} {x : G}
variable [Finite G] (F : QTwoFrameL p B Bs x L D J)

local instance : Field F.F0 := F.fieldF0
local instance : Finite F.F0 := F.finiteF0
local instance : CharP F.F0 2 := F.charF0
local instance : Group F.L0 := F.groupL0
local instance : Finite F.L0 := F.finiteL0

theorem qTwoFrameL_kernel_commute :
    ∀ k ∈ F.c.ker.map L.subtype, ∀ l ∈ L, k * l = l * k := by
  intro k hk l hl
  obtain ⟨x, hx, rfl⟩ := hk
  have hcenter : x ∈ Subgroup.center ↥L := F.hc_ker hx
  have hcomm : (⟨l, hl⟩ : ↥L) * x = x * ⟨l, hl⟩ :=
    Subgroup.mem_center_iff.mp hcenter ⟨l, hl⟩
  exact (congrArg Subtype.val hcomm).symm

theorem qTwoFrameL_kernel_le_normalizer :
    Bs ≤ Subgroup.normalizer ((F.c.ker.map L.subtype : Subgroup G) : Set G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hmaple : (F.c.ker.map L.subtype).map (MulAut.conj b).toMonoidHom ≤
      F.c.ker.map L.subtype := by
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hk
    let y : ↥L :=
      ⟨b * (x : G) * b⁻¹, (Subgroup.mem_normalizer_iff.mp (F.hBsN hb) x).mp x.2⟩
    refine ⟨y, ?_, rfl⟩
    have h1 := F.hρ_induced ⟨b, hb⟩ x
    have hx1 : F.c x = 1 := MonoidHom.mem_ker.mp hx
    simpa [y, hx1] using h1
  have hcard : Nat.card ↥((F.c.ker.map L.subtype).map (MulAut.conj b).toMonoidHom) =
      Nat.card (F.c.ker.map L.subtype) :=
    Subgroup.card_map_of_injective (MulAut.conj b).injective
  exact Subgroup.eq_of_le_of_card_ge hmaple (le_of_eq hcard.symm)

theorem qTwoFrameL_kernel_coprime (hBs : GGBstar 3 B Bs) :
    Nat.Coprime (Nat.card (F.c.ker.map L.subtype)) (Nat.card Bs) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKcard : Nat.card (F.c.ker.map L.subtype) = Nat.card F.c.ker :=
    Subgroup.card_map_of_injective L.subtype_injective
  rw [hKcard]
  have hBsp : IsPGroup 3 ↥Bs := CFSG.Open.IsElemAbelian.isPGroup hBs.2.1
  exact IsPGroup.coprime_card_of_ne 2 3 (by norm_num) F.c.ker Bs F.hc_two hBsp


private theorem qTwoFrameL_rho_eq_c {β : G} (hβ : β ∈ Bs) {l : G} (hl : l ∈ L)
    (hconj : ∀ l₁ ∈ L, β * l₁ * β⁻¹ = l * l₁ * l⁻¹) :
    ∀ y : F.L0, F.ρ ⟨β, hβ⟩ y = F.c ⟨l, hl⟩ * y * (F.c ⟨l, hl⟩)⁻¹ := by
  intro y
  obtain ⟨l₁, rfl⟩ := F.hc_surj y
  let yβ : ↥L := ⟨(β : G) * (l₁ : G) * (β : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (F.hBsN hβ) l₁).mp l₁.2⟩
  let yl : ↥L := ⟨(l : G) * (l₁ : G) * (l : G)⁻¹,
    L.mul_mem (L.mul_mem hl l₁.2) (L.inv_mem hl)⟩
  have h1 := F.hρ_induced ⟨β, hβ⟩ l₁
  have h2 : F.c yβ = F.c yl := congrArg F.c (Subtype.ext (hconj l₁ l₁.2))
  calc
    F.ρ ⟨β, hβ⟩ (F.c l₁) = F.c yβ := h1.symm
    _ = F.c yl := h2
    _ = F.c (⟨l, hl⟩ * l₁ * ⟨l, hl⟩⁻¹) := by
          apply congrArg F.c
          exact Subtype.ext rfl
    _ = F.c ⟨l, hl⟩ * F.c l₁ * (F.c ⟨l, hl⟩)⁻¹ := by simp [map_mul]

theorem qTwoFrameL_exists_diag_of_conj_eq {β : G} (hβ : β ∈ Bs) {l : G} (hl : l ∈ L)
    (hconj : ∀ l₁ ∈ L, β * l₁ * β⁻¹ = l * l₁ * l⁻¹) :
    ∃ w : Su F.F0 2 1 F.m, ggIsDiagMat (w : GL (Fin F.m) F.F0) ∧
      F.c ⟨l, hl⟩ = F.πSU w := by
  classical
  obtain ⟨w, hw⟩ := F.hπ_surj (F.c ⟨l, hl⟩)
  obtain ⟨g, hgdiag, hgact⟩ := F.hdiag ⟨β, hβ⟩
  let k : GL (Fin F.m) F.F0 := (w : GL (Fin F.m) F.F0)⁻¹ * g
  have hk : ∀ s : Su F.F0 2 1 F.m, ∃ s' : Su F.F0 2 1 F.m,
      (s' : GL (Fin F.m) F.F0) = k * (s : GL (Fin F.m) F.F0) * k⁻¹ ∧
        F.πSU s' = F.πSU s := by
    intro s
    obtain ⟨u', hu'GL, hu'ρ⟩ := hgact s
    refine ⟨(w : Su F.F0 2 1 F.m)⁻¹ * u' * w, ?_, ?_⟩
    · simp only [k, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hu'GL]; group
    · rw [map_mul, map_mul, map_inv, ← hu'ρ,
        qTwoFrameL_rho_eq_c F hβ hl hconj (F.πSU s), hw]
      group
  obtain ⟨c, hkmat⟩ :=
    qTwoLMDivCoordInner_rigid (F0 := F.F0) (m := F.m) F.hcardF0
      (by have := F.hm; omega) F.πSU F.hπ_ker (k := k) hk
  have hc0 : c ≠ 0 := by
    have hdet : ((k : GL (Fin F.m) F.F0) : Matrix (Fin F.m) (Fin F.m) F.F0).det ≠ 0 :=
      Matrix.GeneralLinearGroup.det_ne_zero k
    rw [hkmat, Matrix.det_diagonal, Finset.prod_const] at hdet
    have hm0 : (Finset.univ : Finset (Fin F.m)).card ≠ 0 := by
      rw [Finset.card_univ, Fintype.card_fin]; have := F.hm; omega
    intro hc
    rw [hc, zero_pow hm0] at hdet
    exact hdet rfl
  have hgk : g = (w : GL (Fin F.m) F.F0) * k := by
    simp only [k]; group
  have hgmat : (g : Matrix (Fin F.m) (Fin F.m) F.F0) =
      ((w : GL (Fin F.m) F.F0) : Matrix (Fin F.m) (Fin F.m) F.F0) *
        Matrix.diagonal (fun _ => c) := by
    rw [hgk, Matrix.GeneralLinearGroup.coe_mul, hkmat]
  obtain ⟨d, hd⟩ := hgdiag
  refine ⟨w, ⟨fun i => d i * c⁻¹, ?_⟩, hw.symm⟩
  let D : Matrix (Fin F.m) (Fin F.m) F.F0 := Matrix.diagonal (fun _ => c⁻¹)
  have hwmat : ((w : GL (Fin F.m) F.F0) : Matrix (Fin F.m) (Fin F.m) F.F0) =
      (g : Matrix (Fin F.m) (Fin F.m) F.F0) * D := by
    have h := congrArg (fun M : Matrix (Fin F.m) (Fin F.m) F.F0 => M * D) hgmat
    rw [Matrix.mul_assoc, Matrix.diagonal_mul_diagonal] at h
    simp only [D] at h ⊢
    rw [show (fun _ : Fin F.m => c * c⁻¹) = fun _ => (1 : F.F0) by
      funext i; exact mul_inv_cancel₀ hc0] at h
    simpa using h.symm
  rw [hwmat, hd]
  simp only [D, Matrix.diagonal_mul_diagonal]

private theorem qTwoFrameL_conj_mem_sup (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlift : ∀ u : Su F.F0 2 1 F.m, ggIsDiagMat (u : GL (Fin F.m) F.F0) →
      ∃ ℓ : ↥L, F.c ℓ = F.πSU u ∧ (ℓ : G) ∈ Bs)
    (n : ↥L) (hn : MulAut.conj n ∈
      Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L)))
    {b : G} (hb : b ∈ Bs) :
    (n : G) * b * (n : G)⁻¹ ∈ F.c.ker.map L.subtype ⊔ Bs := by
  classical
  obtain ⟨hl0, β, hβBs, hβconj⟩ := exists_bstar_conj_eq_commutator hN hn hb
  obtain ⟨w, hwdiag, hwc⟩ := qTwoFrameL_exists_diag_of_conj_eq F hβBs hl0 hβconj
  obtain ⟨ℓ, hℓc, hℓBs⟩ := hlift w hwdiag
  have hc_eq : F.c ⟨(n : G) * b * (n : G)⁻¹ * b⁻¹, hl0⟩ = F.c ℓ :=
    hwc.trans hℓc.symm
  let y : ↥L := ⟨(n : G) * b * (n : G)⁻¹ * b⁻¹, hl0⟩ * ℓ⁻¹
  have hyker : y ∈ F.c.ker := by
    rw [MonoidHom.mem_ker]
    change F.c (⟨(n : G) * b * (n : G)⁻¹ * b⁻¹, hl0⟩ * ℓ⁻¹) = 1
    rw [map_mul, hc_eq, map_inv]
    simp
  let k : G := (y : G)
  have hkK : k ∈ F.c.ker.map L.subtype := ⟨y, hyker, rfl⟩
  have hℓbBs : (ℓ : G) * b ∈ Bs := Bs.mul_mem hℓBs hb
  have hdecomp : (n : G) * b * (n : G)⁻¹ = k * ((ℓ : G) * b) := by
    show (n : G) * b * (n : G)⁻¹ = (y : G) * ((ℓ : G) * b)
    simp only [y, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [hdecomp]
  exact Subgroup.mul_mem_sup hkK hℓbBs

theorem qTwoFrameL_link_of_lift (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlift : ∀ u : Su F.F0 2 1 F.m, ggIsDiagMat (u : GL (Fin F.m) F.F0) →
      ∃ ℓ : ↥L, F.c ℓ = F.πSU u ∧ (ℓ : G) ∈ Bs)
    (n : ↥L) (hn : MulAut.conj n ∈
      Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L))) :
    ∃ n' : ↥L, (n' : G) ∈ Subgroup.normalizer (Bs : Set G) ∧
      MulAut.conj n' = MulAut.conj n := by
  classical
  let K : Subgroup G := F.c.ker.map L.subtype
  have hKc : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k := qTwoFrameL_kernel_commute F
  have hBsK : Bs ≤ Subgroup.normalizer (K : Set G) := qTwoFrameL_kernel_le_normalizer F
  have hcop : Nat.Coprime (Nat.card K) (Nat.card Bs) := qTwoFrameL_kernel_coprime F hBs
  have hle : ∀ b ∈ Bs, (n : G) * b * (n : G)⁻¹ ∈ K ⊔ Bs := by
    intro b hb
    exact qTwoFrameL_conj_mem_sup F hN hlift n hn hb
  obtain ⟨k, hkK, hkn⟩ :=
    CFSG.GroupTheory.exists_mul_mem_normalizer_of_conj_le_sup
      (K := K) (Bs := Bs) (L := L) hKc hBsK hcop n.2 hle
  have hkL : k ∈ L := by
    obtain ⟨y, -, hyk⟩ := hkK
    rw [← hyk]
    exact y.2
  let n' : ↥L := ⟨k * (n : G), L.mul_mem hkL n.2⟩
  refine ⟨n', hkn, ?_⟩
  ext l
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  have hkl : k * (l : G) = (l : G) * k := hKc k hkK l l.2
  have hkn' : k * (n : G) = (n : G) * k := hKc k hkK n n.2
  have hkn_inv : k * (n : G)⁻¹ = (n : G)⁻¹ * k :=
    (Commute.inv_right (show Commute k (n : G) from hkn')).eq
  show (k * (n : G)) * (l : G) * (k * (n : G))⁻¹ =
    (n : G) * (l : G) * (n : G)⁻¹
  calc
    (k * (n : G)) * (l : G) * (k * (n : G))⁻¹
        = k * (n : G) * (l : G) * (n : G)⁻¹ * k⁻¹ := by group
    _ = (n : G) * k * (l : G) * (n : G)⁻¹ * k⁻¹ := by rw [hkn']
    _ = (n : G) * (k * (l : G)) * (n : G)⁻¹ * k⁻¹ := by group
    _ = (n : G) * ((l : G) * k) * (n : G)⁻¹ * k⁻¹ := by rw [hkl]
    _ = (n : G) * (l : G) * (k * (n : G)⁻¹) * k⁻¹ := by group
    _ = (n : G) * (l : G) * ((n : G)⁻¹ * k) * k⁻¹ := by rw [hkn_inv]
    _ = (n : G) * (l : G) * (n : G)⁻¹ := by group

end FrameKernel

end CFSG.StandardType.QTwo

end
