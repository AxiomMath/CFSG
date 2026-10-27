module

public import CFSG.RankThree.PartTwo.Sec14.Item1413Res2ProofM12R
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res2ProofSimple
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig
public import CFSG.RankThree.PartTwo.Toolkit.M12Facts
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJM12
import CFSG.RankThree.PartTwo.Sec13.Item13Plane
import CFSG.RankThree.PartTwo.Sec13.Item133
import CFSG.RankThree.Asc83Table.Automizer
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
public import CFSG.RankThree.GroupTheory.SteinbergBYAlphaTransport
import CFSG.RankThree.PartTwo.Sec4.Census.Interface

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open CFSG.GH74.M12.Hyp (G12)
open scoped commutatorElement

namespace Proof1413Res2

variable {G : Type} [Group G] [Finite G]

section Transport

variable {L : Subgroup G} {M : Type*} [Group M] (χ : ↥L ≃* M)

@[expose] def preM (V : Subgroup M) : Subgroup G :=
  (V.map χ.symm.toMonoidHom).map L.subtype

omit [Finite G] in
theorem preM_le (V : Subgroup M) : preM χ V ≤ L := Subgroup.map_subtype_le _

omit [Finite G] in
theorem mem_preM {V : Subgroup M} {g : G} (hg : g ∈ L) :
    g ∈ preM χ V ↔ χ ⟨g, hg⟩ ∈ V := by
  constructor
  · rintro ⟨h, ⟨v, hv, rfl⟩, hvg⟩
    have : (⟨g, hg⟩ : ↥L) = χ.symm v := Subtype.ext hvg.symm
    rw [this, MulEquiv.apply_symm_apply]
    exact hv
  · intro hv
    exact ⟨⟨g, hg⟩, ⟨χ ⟨g, hg⟩, hv, by simp⟩, rfl⟩

omit [Finite G] in
theorem card_preM (V : Subgroup M) : Nat.card (preM χ V) = Nat.card V := by
  rw [preM, Subgroup.card_map_of_injective L.subtype_injective,
    Subgroup.card_map_of_injective χ.symm.injective]

omit [Finite G] in
theorem preM_mono {V W : Subgroup M} (h : V ≤ W) : preM χ V ≤ preM χ W :=
  Subgroup.map_mono (Subgroup.map_mono h)

@[expose] def imgM (R : Subgroup G) : Subgroup M := (R.subgroupOf L).map χ.toMonoidHom

omit [Finite G] in
theorem mem_imgM {R : Subgroup G} {g : G} (hg : g ∈ L) : χ ⟨g, hg⟩ ∈ imgM χ R ↔ g ∈ R := by
  constructor
  · rintro ⟨h, hh, hhg⟩
    have : h = ⟨g, hg⟩ := χ.injective hhg
    rw [this] at hh
    exact Subgroup.mem_subgroupOf.mp hh
  · intro hgR
    exact ⟨⟨g, hg⟩, Subgroup.mem_subgroupOf.mpr hgR, rfl⟩

omit [Finite G] in
theorem preM_imgM {R : Subgroup G} (hRL : R ≤ L) : preM χ (imgM χ R) = R := by
  ext g
  constructor
  · intro hg
    exact (mem_imgM χ (preM_le χ _ hg)).mp ((mem_preM χ (preM_le χ _ hg)).mp hg)
  · intro hg
    exact (mem_preM χ (hRL hg)).mpr ((mem_imgM χ (hRL hg)).mpr hg)

omit [Finite G] in
theorem imgM_le_iff {R : Subgroup G} (hRL : R ≤ L) {V : Subgroup M} :
    imgM χ R ≤ V ↔ R ≤ preM χ V := by
  constructor
  · intro h
    rw [← preM_imgM χ hRL]
    exact preM_mono χ h
  · rintro h _ ⟨r, hr, rfl⟩
    have hr' : (r : G) ∈ R := Subgroup.mem_subgroupOf.mp hr
    exact (mem_preM χ r.2).mp (h hr')

omit [Finite G] in
theorem card_imgM {R : Subgroup G} (hRL : R ≤ L) : Nat.card (imgM χ R) = Nat.card R := by
  conv_rhs => rw [← preM_imgM χ hRL]
  rw [card_preM]

omit [Finite G] in
theorem mem_centralizer_preM_iff {V : Subgroup M} {b : G} (hb : b ∈ L) :
    b ∈ Subgroup.centralizer (preM χ V : Set G) ↔
      χ ⟨b, hb⟩ ∈ Subgroup.centralizer (V : Set M) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h w hw
    have hv : ((χ.symm w : ↥L) : G) ∈ preM χ V := ⟨χ.symm w, ⟨w, hw, rfl⟩, rfl⟩
    have h1 := h _ hv
    have h2 : χ.symm w * ⟨b, hb⟩ = ⟨b, hb⟩ * χ.symm w := Subtype.ext h1
    have h3 := congrArg χ h2
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h3
  · intro h g hg
    have hgL := preM_le χ V hg
    have h1 := h _ ((mem_preM χ hgL).mp hg)
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (χ.injective h1)

omit [Finite G] in
theorem mem_normalizer_preM_iff {V : Subgroup M} {b : G} (hb : b ∈ L) :
    b ∈ Subgroup.normalizer (preM χ V : Set G) ↔
      χ ⟨b, hb⟩ ∈ Subgroup.normalizer (V : Set M) := by
  have hconj : ∀ (g : G) (hg : g ∈ L), χ ⟨b * g * b⁻¹, mul_mem (mul_mem hb hg) (inv_mem hb)⟩ =
      χ ⟨b, hb⟩ * χ ⟨g, hg⟩ * (χ ⟨b, hb⟩)⁻¹ := by
    intro g hg
    rw [← map_mul, ← map_inv, ← map_mul]
    rfl
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h w
    have hwL := (χ.symm w).2
    have hw : χ ⟨((χ.symm w : ↥L) : G), hwL⟩ = w := by simp
    have h1 := h ((χ.symm w : ↥L) : G)
    rw [mem_preM χ hwL, mem_preM χ (mul_mem (mul_mem hb hwL) (inv_mem hb)), hconj _ hwL,
      hw] at h1
    exact h1
  · intro h g
    by_cases hg : g ∈ L
    · rw [mem_preM χ hg, mem_preM χ (mul_mem (mul_mem hb hg) (inv_mem hb)), hconj _ hg]
      exact h _
    · constructor
      · intro hg'
        exact absurd (preM_le χ V hg') hg
      · intro hg'
        exfalso
        apply hg
        have h1 := preM_le χ V hg'
        have h2 : b⁻¹ * (b * g * b⁻¹) * b ∈ L := mul_mem (mul_mem (inv_mem hb) h1) hb
        simpa [mul_assoc] using h2

omit [Finite G] in
theorem imgM_preM (V : Subgroup M) :
    imgM χ (preM χ V) = V := by
  ext t
  have ht : χ ⟨((χ.symm t : ↥L) : G), (χ.symm t).2⟩ = t := by simp
  constructor
  · intro h
    rw [← ht] at h ⊢
    exact (mem_preM χ _).mp ((mem_imgM χ _).mp h)
  · intro h
    rw [← ht] at h ⊢
    exact (mem_imgM χ _).mpr ((mem_preM χ _).mpr h)

end Transport

section Concrete

open CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig (V ai card_V V_ne V_le_C A_le_normalizer_V
  le_V_of_mem_invariant z_mem_A f_mem_A)

theorem ai_mem_centralizer_V (i : Fin 3) :
    ai i ∈ Subgroup.centralizer (V i : Set G12) :=
  Subgroup.mem_centralizer_iff.mpr fun _ hv =>
    Subgroup.mem_centralizer_singleton_iff.mp (V_le_C i hv)

theorem z_not_mem_centralizer_V
    (i : Fin 3) :
    ⁅Toolkit.M12.x, Toolkit.M12.y⁆ ∉ Subgroup.centralizer (V i : Set G12) := by
  intro hz
  have hle : V i ≤ ⊥ := by
    intro v hv
    have hvz : Commute v ⁅Toolkit.M12.x, Toolkit.M12.y⁆ := Subgroup.mem_centralizer_iff.mp hz v hv
    have hva : Commute v (ai i) := Subgroup.mem_centralizer_singleton_iff.mp (V_le_C i hv)
    have hvA := mem_centralizer_A_of_commute hvz hva
    rw [centralizer_basisA] at hvA
    exact Subgroup.mem_bot.mpr (eq_one_of_mem_basisA (U := V i) (by rw [card_V]; norm_num) hvA hv)
  have h4 := card_V i
  rw [le_bot_iff.mp hle, Subgroup.card_bot] at h4
  norm_num at h4

theorem ai_not_mem_centralizer_V
    {i j : Fin 3} (hij : i ≠ j) :
    ai i ∉ Subgroup.centralizer (V j : Set G12) := by
  intro hi
  apply z_not_mem_centralizer_V j
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact commute_z_of_commute_ai hij (Subgroup.mem_centralizer_iff.mp hi v hv)
    (Subgroup.mem_centralizer_iff.mp (ai_mem_centralizer_V j) v hv)

theorem ai_mem_A (i : Fin 3) : ai i ∈ Toolkit.M12.basisA.sub := by
  have h := f_mem_A i.val 1
  rwa [pow_one] at h

end Concrete

theorem false_of_conj_order {A L : Subgroup G} {c : G}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hAel : CFSG.Assembly.IsElemAbelian 3 A)
    (hcA : c ∈ A) (hAa : A = Subgroup.zpowers c ⊔ (A ⊓ L))
    (hS3 : Nonempty (↥(Sec4.autIn L A) ≃* Equiv.Perm (Fin 3))) (χ : ↥L ≃* G12) {g t₀ : G12}
    (hg : ∀ t ∈ (A.subgroupOf L).map χ.toMonoidHom,
      g * t * g⁻¹ ∈ (A.subgroupOf L).map χ.toMonoidHom)
    (ht₀ : t₀ ∈ (A.subgroupOf L).map χ.toMonoidHom)
    (h2 : g ^ 2 * t₀ * (g ^ 2)⁻¹ ≠ t₀) (h3 : g ^ 3 * t₀ * (g ^ 3)⁻¹ ≠ t₀) : False := by
  set l : ↥L := χ.symm g with hl
  have hlc : ∀ k : ℕ, (l : G) * c ^ k * (l : G)⁻¹ = c ^ k := by
    intro k
    have h1 : Commute (l : G) c := Subgroup.mem_centralizer_singleton_iff.mp (hLc l.2)
    rw [(h1.pow_right k).eq, mul_inv_cancel_right]
  have hlA : ∀ a ∈ A, (l : G) * a * (l : G)⁻¹ ∈ A := by
    intro a ha
    obtain ⟨k, -, b, hb, rfl⟩ := exists_pow_mul_of_mem hAel hcA hAa ha
    have hbB : χ ⟨b, hb.2⟩ ∈ (A.subgroupOf L).map χ.toMonoidHom :=
      ⟨⟨b, hb.2⟩, Subgroup.mem_subgroupOf.mpr hb.1, rfl⟩
    obtain ⟨m, hm, hm'⟩ := hg _ hbB
    have hml : m = l * ⟨b, hb.2⟩ * l⁻¹ := by
      apply χ.injective
      rw [show χ.toMonoidHom m = χ m from rfl] at hm'
      rw [hm', map_mul, map_mul, map_inv, hl, MulEquiv.apply_symm_apply]
    rw [hml] at hm
    have hlb : (l : G) * b * (l : G)⁻¹ ∈ A := Subgroup.mem_subgroupOf.mp hm
    rw [show (l : G) * (c ^ k * b) * (l : G)⁻¹ =
      ((l : G) * c ^ k * (l : G)⁻¹) * ((l : G) * b * (l : G)⁻¹) by group, hlc k]
    exact mul_mem (pow_mem hcA k) hlb
  have hlN : (l : G) ∈ Subgroup.normalizer (A : Set G) := Subgroup.mem_normalizer_fintype hlA
  set τ := A.normalizerMonoidHom ⟨(l : G), hlN⟩ with hτdef
  have hτ : τ ∈ Sec4.autIn L A := Sec4.mem_autIn_iff.mpr ⟨l, hlN, l.2, rfl⟩
  obtain ⟨m₀, hm₀, rfl⟩ := ht₀
  have hm₀A : (m₀ : G) ∈ A := Subgroup.mem_subgroupOf.mp hm₀
  have hpow : ∀ n : ℕ, g ^ n * χ m₀ * (g ^ n)⁻¹ ≠ χ m₀ → τ ^ n ≠ 1 := by
    intro n hn hτn
    apply hn
    have h1 := congrArg (fun σ : MulAut ↥A => ((σ ⟨(m₀ : G), hm₀A⟩ : ↥A) : G)) hτn
    simp only [MulAut.one_apply] at h1
    rw [normalizerMonoidHom_pow_apply_val] at h1
    have h4 : l ^ n * m₀ * (l ^ n)⁻¹ = m₀ := Subtype.ext (by simpa using h1)
    have h5 := congrArg χ h4
    rwa [map_mul, map_mul, map_inv, map_pow, hl, MulEquiv.apply_symm_apply] at h5
  obtain ⟨e⟩ := hS3
  have hS3o : ∀ σ : Equiv.Perm (Fin 3), σ ^ 2 = 1 ∨ σ ^ 3 = 1 := by decide
  have hlift : ∀ n : ℕ, e ⟨τ, hτ⟩ ^ n = 1 → τ ^ n = 1 := by
    intro n hn
    have h1 : (⟨τ, hτ⟩ : Sec4.autIn L A) ^ n = 1 := e.injective (by rw [map_pow, hn, map_one])
    exact congrArg Subtype.val h1
  rcases hS3o (e ⟨τ, hτ⟩) with h | h
  · exact hpow 2 h2 (hlift 2 h)
  · exact hpow 3 h3 (hlift 3 h)

theorem x_sq_ne_z : Toolkit.M12.x ^ 2 ≠ ⁅Toolkit.M12.x, Toolkit.M12.y⁆ := by
  rw [Ne, Toolkit.M12.eq_iff_tbl, Toolkit.M12.tblG_pow, Toolkit.M12.tbl_x, Toolkit.M12.tbl_z]
  decide +kernel

theorem y_sq_ne_z : Toolkit.M12.y ^ 2 ≠ ⁅Toolkit.M12.x, Toolkit.M12.y⁆ := by
  rw [Ne, Toolkit.M12.eq_iff_tbl, Toolkit.M12.tblG_pow, Toolkit.M12.tbl_y, Toolkit.M12.tbl_z]
  decide +kernel

theorem z_sq_ne_z : ⁅Toolkit.M12.x, Toolkit.M12.y⁆ ^ 2 ≠ ⁅Toolkit.M12.x, Toolkit.M12.y⁆ := by
  intro h
  apply Toolkit.M12.z_ne_one
  rw [pow_two] at h
  exact mul_left_cancel (h.trans (mul_one _).symm)

theorem exists_conj_E : ∃ g : G12,
    g * ⁅Toolkit.M12.x, Toolkit.M12.y⁆ * g⁻¹ = Toolkit.M12.x ∧
      g * Toolkit.M12.x * g⁻¹ = ⁅Toolkit.M12.x, Toolkit.M12.y⁆ ^ 2 := by
  obtain ⟨-, -, h3, h4, h5, h6, -⟩ := Toolkit.M12.gl_tables
  have hSz := Toolkit.M12.conj_eq_of_tbl (Toolkit.M12.tbl_wE _) Toolkit.M12.tbl_z
    Toolkit.M12.tbl_z Toolkit.M12.tbl_x h3
  have hSx := Toolkit.M12.conj_eq_of_tbl (Toolkit.M12.tbl_wE _) Toolkit.M12.tbl_x
    Toolkit.M12.tbl_z Toolkit.M12.tbl_x h4
  have hWz := Toolkit.M12.conj_eq_of_tbl (Toolkit.M12.tbl_wE _) Toolkit.M12.tbl_z
    Toolkit.M12.tbl_z Toolkit.M12.tbl_x h5
  have hWx := Toolkit.M12.conj_eq_of_tbl (Toolkit.M12.tbl_wE _) Toolkit.M12.tbl_x
    Toolkit.M12.tbl_z Toolkit.M12.tbl_x h6
  refine ⟨Toolkit.M12.wE Toolkit.M12.wES * Toolkit.M12.wE Toolkit.M12.wEW, ?_, ?_⟩
  · rw [show Toolkit.M12.wE Toolkit.M12.wES * Toolkit.M12.wE Toolkit.M12.wEW *
        ⁅Toolkit.M12.x, Toolkit.M12.y⁆ * (Toolkit.M12.wE Toolkit.M12.wES *
          Toolkit.M12.wE Toolkit.M12.wEW)⁻¹ =
        Toolkit.M12.wE Toolkit.M12.wES * (Toolkit.M12.wE Toolkit.M12.wEW *
          ⁅Toolkit.M12.x, Toolkit.M12.y⁆ * (Toolkit.M12.wE Toolkit.M12.wEW)⁻¹) *
          (Toolkit.M12.wE Toolkit.M12.wES)⁻¹ by group, hWz, pow_zero, one_mul, pow_one, hSx,
      pow_zero, one_mul, pow_one]
  · rw [show Toolkit.M12.wE Toolkit.M12.wES * Toolkit.M12.wE Toolkit.M12.wEW *
        Toolkit.M12.x * (Toolkit.M12.wE Toolkit.M12.wES * Toolkit.M12.wE Toolkit.M12.wEW)⁻¹ =
        Toolkit.M12.wE Toolkit.M12.wES * (Toolkit.M12.wE Toolkit.M12.wEW *
          Toolkit.M12.x * (Toolkit.M12.wE Toolkit.M12.wEW)⁻¹) *
          (Toolkit.M12.wE Toolkit.M12.wES)⁻¹ by group, hWx, pow_zero, mul_one, pow_one, hSz,
      pow_zero, mul_one]

theorem exists_conj_F : ∃ g : G12,
    g * ⁅Toolkit.M12.x, Toolkit.M12.y⁆ * g⁻¹ = Toolkit.M12.y ∧
      g * Toolkit.M12.y * g⁻¹ = ⁅Toolkit.M12.x, Toolkit.M12.y⁆ ^ 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, h3, h4, h5, h6⟩ := Toolkit.M12.gl_tables
  have hSz := Toolkit.M12.conj_eq_of_tbl (Toolkit.M12.tbl_wE _) Toolkit.M12.tbl_z
    Toolkit.M12.tbl_z Toolkit.M12.tbl_y h3
  have hSy := Toolkit.M12.conj_eq_of_tbl (Toolkit.M12.tbl_wE _) Toolkit.M12.tbl_y
    Toolkit.M12.tbl_z Toolkit.M12.tbl_y h4
  have hWz := Toolkit.M12.conj_eq_of_tbl (Toolkit.M12.tbl_wE _) Toolkit.M12.tbl_z
    Toolkit.M12.tbl_z Toolkit.M12.tbl_y h5
  have hWy := Toolkit.M12.conj_eq_of_tbl (Toolkit.M12.tbl_wE _) Toolkit.M12.tbl_y
    Toolkit.M12.tbl_z Toolkit.M12.tbl_y h6
  refine ⟨Toolkit.M12.wE Toolkit.M12.wFS * Toolkit.M12.wE Toolkit.M12.wFW, ?_, ?_⟩
  · rw [show Toolkit.M12.wE Toolkit.M12.wFS * Toolkit.M12.wE Toolkit.M12.wFW *
        ⁅Toolkit.M12.x, Toolkit.M12.y⁆ * (Toolkit.M12.wE Toolkit.M12.wFS *
          Toolkit.M12.wE Toolkit.M12.wFW)⁻¹ =
        Toolkit.M12.wE Toolkit.M12.wFS * (Toolkit.M12.wE Toolkit.M12.wFW *
          ⁅Toolkit.M12.x, Toolkit.M12.y⁆ * (Toolkit.M12.wE Toolkit.M12.wFW)⁻¹) *
          (Toolkit.M12.wE Toolkit.M12.wFS)⁻¹ by group, hWz, pow_zero, one_mul, pow_one, hSy,
      pow_zero, one_mul, pow_one]
  · rw [show Toolkit.M12.wE Toolkit.M12.wFS * Toolkit.M12.wE Toolkit.M12.wFW *
        Toolkit.M12.y * (Toolkit.M12.wE Toolkit.M12.wFS * Toolkit.M12.wE Toolkit.M12.wFW)⁻¹ =
        Toolkit.M12.wE Toolkit.M12.wFS * (Toolkit.M12.wE Toolkit.M12.wFW *
          Toolkit.M12.y * (Toolkit.M12.wE Toolkit.M12.wFW)⁻¹) *
          (Toolkit.M12.wE Toolkit.M12.wFS)⁻¹ by group, hWy, pow_zero, mul_one, pow_one, hSz,
      pow_zero, mul_one]

theorem false_of_conj_pair {A L : Subgroup G} {c : G}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hAel : CFSG.Assembly.IsElemAbelian 3 A)
    (hcA : c ∈ A) (hAa : A = Subgroup.zpowers c ⊔ (A ⊓ L))
    (hS3 : Nonempty (↥(Sec4.autIn L A) ≃* Equiv.Perm (Fin 3))) (χ : ↥L ≃* G12) {u g : G12}
    (hB : (A.subgroupOf L).map χ.toMonoidHom =
      Subgroup.closure ({⁅Toolkit.M12.x, Toolkit.M12.y⁆, u} : Set G12))
    (hgz : g * ⁅Toolkit.M12.x, Toolkit.M12.y⁆ * g⁻¹ = u)
    (hgu : g * u * g⁻¹ = ⁅Toolkit.M12.x, Toolkit.M12.y⁆ ^ 2)
    (hu2 : u ^ 2 ≠ ⁅Toolkit.M12.x, Toolkit.M12.y⁆) : False := by
  set z := ⁅Toolkit.M12.x, Toolkit.M12.y⁆ with hzdef
  have hzB : z ∈ Subgroup.closure ({z, u} : Set G12) := Subgroup.subset_closure (Set.mem_insert _ _)
  have huB : u ∈ Subgroup.closure ({z, u} : Set G12) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton u))
  have hgN : g ∈ Subgroup.normalizer (Subgroup.closure ({z, u} : Set G12) : Set G12) := by
    refine Asc83Table.mem_normalizer_closure_of_conj_mem ?_
    rintro s (rfl | rfl)
    · rw [hgz]
      exact huB
    · rw [hgu]
      exact pow_mem hzB 2
  refine false_of_conj_order hLc hAel hcA hAa hS3 χ (g := g) (t₀ := z) ?_ (hB ▸ hzB) ?_ ?_
  · rw [hB]
    intro t ht
    exact (Subgroup.mem_normalizer_iff.mp hgN t).mp ht
  · rw [show g ^ 2 * z * (g ^ 2)⁻¹ = g * (g * z * g⁻¹) * g⁻¹ by rw [pow_two]; group, hgz,
      hgu]
    exact z_sq_ne_z
  · rw [show g ^ 3 * z * (g ^ 3)⁻¹ = g * (g * (g * z * g⁻¹) * g⁻¹) * g⁻¹ by
        rw [pow_succ, pow_two]; group, hgz, hgu,
      show g * z ^ 2 * g⁻¹ = (g * z * g⁻¹) ^ 2 by rw [pow_two, pow_two]; group, hgz]
    exact hu2

theorem exists_equiv_basisA
    {A L : Subgroup G} {c : G} (hLc : L ≤ Subgroup.centralizer ({c} : Set G))
    (hAel : CFSG.Assembly.IsElemAbelian 3 A) (hcA : c ∈ A)
    (hAa : A = Subgroup.zpowers c ⊔ (A ⊓ L)) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hS3 : Nonempty (↥(Sec4.autIn L A) ≃* Equiv.Perm (Fin 3))) (ψ : ↥L ≃* G12) :
    ∃ χ : ↥L ≃* G12, (A.subgroupOf L).map χ.toMonoidHom = Toolkit.M12.basisA.sub := by
  have hc9 : Nat.card (A.subgroupOf L) = 9 := by
    rw [← h9, ← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective L.subtype_injective]
  set T := (A.subgroupOf L).map ψ.toMonoidHom with hT
  have hT9 : Nat.card T = 9 := by rw [hT, Subgroup.card_map_of_injective ψ.injective, hc9]
  have hT3 : IsPGroup 3 T := IsPGroup.of_card (n := 2) (by rw [hT9]; norm_num)
  obtain ⟨g, hg⟩ := exists_conj_le_P0_m12 hT3
  set χ₀ : ↥L ≃* G12 := ψ.trans (MulAut.conj g) with hχ₀
  have hχ₀T : (A.subgroupOf L).map χ₀.toMonoidHom = T.map (MulAut.conj g).toMonoidHom := by
    rw [hT, Subgroup.map_map]
    rfl
  have hmem : T.map (MulAut.conj g).toMonoidHom ∈
      ({Toolkit.M12.E, Toolkit.M12.F, Toolkit.M12.A, Toolkit.M12.A'} : Set (Subgroup G12)) := by
    rw [← Toolkit.M12.nine_eq]
    exact ⟨hg, by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hT9]⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with hE | hF | hA | hA'
  · exfalso
    obtain ⟨g', hgz, hgx⟩ := exists_conj_E
    exact false_of_conj_pair hLc hAel hcA hAa hS3 χ₀ (hχ₀T.trans hE) hgz hgx x_sq_ne_z
  · exfalso
    obtain ⟨g', hgz, hgy⟩ := exists_conj_F
    exact false_of_conj_pair hLc hAel hcA hAa hS3 χ₀ (hχ₀T.trans hF) hgz hgy y_sq_ne_z
  · exact ⟨χ₀, hχ₀T.trans hA⟩
  · refine ⟨χ₀.trans (MulAut.conj Toolkit.M12.g0), ?_⟩
    have h1 : (A.subgroupOf L).map (χ₀.trans (MulAut.conj Toolkit.M12.g0)).toMonoidHom =
        ((A.subgroupOf L).map χ₀.toMonoidHom).map (MulAut.conj Toolkit.M12.g0).toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    rw [h1, hχ₀T, hA', Toolkit.M12.map_g0_A']

section Conclusion

theorem realize_of_family {M : Type} [Group M] [Finite M] {A L : Subgroup G} {c : G}
    (hAel : CFSG.Assembly.IsElemAbelian 3 A) (hcA : c ∈ A) (hcL : c ∉ L) (h27 : Nat.card A = 27)
    (hAa : A = Subgroup.zpowers c ⊔ (A ⊓ L)) (χ : ↥L ≃* M) {T : Subgroup M}
    {W : Fin 3 → Subgroup M} {z : M} {d : G}
    (hAχ : ∀ b (hb : b ∈ A ⊓ L), χ ⟨b, hb.2⟩ ∈ T)
    (hcC : ∀ S : Subgroup G, S ≤ L → c ∈ Subgroup.centralizer (S : Set G))
    (hd : d = ((χ.symm z : ↥L) : G))
    (hRmax : ∀ i, preM χ (W i) ∈ scriptQPiStar A (lB A) L (piOf 2))
    (hcard9 : ∀ i,
      Nat.card (A ⊓ Subgroup.centralizer (preM χ (W i) : Set G) : Subgroup G) ≤ 9)
    (hcases : ∀ t ∈ T, t ≠ 1 → (t = z ∨ t = z ^ 2) ∨
      ∃ i, W i ≤ Subgroup.centralizer ({t} : Set M))
    {u : G} (hu : u ∈ A) (hud : u ∉ Subgroup.closure ({c, d} : Set G)) :
    ∃ R ∈ scriptQPiStar A (lB A) L (piOf 2),
      A ⊓ Subgroup.centralizer (R : Set G) = Subgroup.closure {c, u} := by
  obtain ⟨k, -, b, hb, rfl⟩ := exists_pow_mul_of_mem hAel hcA hAa hu
  have hbt : χ ⟨b, hb.2⟩ ∈ T := hAχ b hb
  have hcd : ∀ y ∈ Subgroup.closure ({d} : Set G),
      c ^ k * y ∈ Subgroup.closure ({c, d} : Set G) := by
    intro y hy
    refine mul_mem (pow_mem (Subgroup.subset_closure (Set.mem_insert c {d})) k) ?_
    exact Subgroup.closure_mono (Set.singleton_subset_iff.mpr
      (Set.mem_insert_of_mem c (Set.mem_singleton d))) hy
  have hbt1 : χ ⟨b, hb.2⟩ ≠ 1 := by
    intro h1
    apply hud
    have hb1 : b = 1 := by
      have h2 : (⟨b, hb.2⟩ : ↥L) = 1 := χ.injective (h1.trans (map_one χ).symm)
      exact congrArg Subtype.val h2
    rw [hb1]
    exact hcd 1 (one_mem _)
  rcases hcases _ hbt hbt1 with hz | ⟨i, hi⟩
  · exfalso
    apply hud
    have hdmem : d ∈ Subgroup.closure ({d} : Set G) := Subgroup.subset_closure (Set.mem_singleton d)
    rcases hz with hz | hz
    · have h2 : (⟨b, hb.2⟩ : ↥L) = χ.symm z := by rw [← hz, MulEquiv.symm_apply_apply]
      have hbd : b = d := by rw [hd, ← h2]
      rw [hbd]
      exact hcd d hdmem
    · have h2 : (⟨b, hb.2⟩ : ↥L) = (χ.symm z) ^ 2 := by
        rw [← map_pow, ← hz, MulEquiv.symm_apply_apply]
      have hbd : b = d ^ 2 := by rw [hd, ← Subgroup.coe_pow, ← h2]
      rw [hbd]
      exact hcd _ (pow_mem hdmem 2)
  · refine ⟨preM χ (W i), hRmax i, ?_⟩
    have hRL := preM_le χ (W i)
    have hbC : b ∈ Subgroup.centralizer (preM χ (W i) : Set G) := by
      refine (mem_centralizer_preM_iff χ hb.2).mpr (Subgroup.mem_centralizer_iff.mpr ?_)
      intro v hv
      exact Subgroup.mem_centralizer_singleton_iff.mp (hi hv)
    have hle1 : Subgroup.closure ({c, c ^ k * b} : Set G) ≤
        A ⊓ Subgroup.centralizer (preM χ (W i) : Set G) := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact ⟨hcA, hcC _ hRL⟩
      · exact ⟨hu, mul_mem (pow_mem (hcC _ hRL) k) hbC⟩
    have hc1 : c ≠ 1 := fun h => hcL (h ▸ one_mem L)
    have hco : orderOf c = 3 := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact orderOf_eq_prime (hAel.2 c hcA) hc1
    have hgt : 3 < Nat.card (Subgroup.closure ({c, c ^ k * b} : Set G)) := by
      have hlt : Subgroup.zpowers c < Subgroup.closure ({c, c ^ k * b} : Set G) := by
        refine lt_of_le_of_ne (Subgroup.zpowers_le.mpr (Subgroup.subset_closure
          (Set.mem_insert c _))) fun h => ?_
        have hu' : c ^ k * b ∈ Subgroup.zpowers c := h ▸ Subgroup.subset_closure
          (Set.mem_insert_of_mem c (Set.mem_singleton _))
        have hbc : b ∈ L ⊓ Subgroup.zpowers c := by
          refine ⟨hb.2, ?_⟩
          have h1 := mul_mem (inv_mem (pow_mem (Subgroup.mem_zpowers c) k)) hu'
          rwa [inv_mul_cancel_left] at h1
        rw [Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hco hcL,
          Subgroup.mem_bot] at hbc
        apply hbt1
        have h2 : (⟨b, hb.2⟩ : ↥L) = 1 := Subtype.ext hbc
        rw [h2, map_one]
      have h3 : Nat.card (Subgroup.zpowers c) = 3 := by rw [Nat.card_zpowers, hco]
      rw [← h3]
      exact Subgroup.card_lt_of_lt hlt
    have hdvd1 : Nat.card (Subgroup.closure ({c, c ^ k * b} : Set G)) ∣
        Nat.card (A ⊓ Subgroup.centralizer (preM χ (W i) : Set G) : Subgroup G) :=
      Subgroup.card_dvd_of_le hle1
    have hdvd2 : Nat.card (A ⊓ Subgroup.centralizer (preM χ (W i) : Set G) : Subgroup G) ∣
        3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← h27]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨k₁, hk₁, hk₁'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (hdvd1.trans hdvd2)
    obtain ⟨k₂, hk₂, hk₂'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd2
    have h9a := hcard9 i
    have hle2 := Nat.le_of_dvd (by rw [hk₂']; positivity) hdvd1
    rw [hk₁'] at hgt hle2
    rw [hk₂'] at h9a hle2
    have hk₂le : k₂ ≤ 2 := by
      by_contra h
      have : 3 ^ 3 ≤ 3 ^ k₂ := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hk₁ge : 2 ≤ k₁ := by
      by_contra h
      have : 3 ^ k₁ ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hk₁le : k₁ ≤ k₂ := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle2
    have hcardeq : Nat.card (A ⊓ Subgroup.centralizer (preM χ (W i) : Set G) : Subgroup G) ≤
        Nat.card (Subgroup.closure ({c, c ^ k * b} : Set G)) := by
      rw [hk₁', hk₂']
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact (Subgroup.eq_of_le_of_card_ge hle1 hcardeq).symm

theorem conclusion_of_family {M : Type} [Group M] [Finite M] {A L : Subgroup G} {c : G}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hAel : CFSG.Assembly.IsElemAbelian 3 A)
    (hcA : c ∈ A) (hcL : c ∉ L) (h27 : Nat.card A = 27)
    (hAa : A = Subgroup.zpowers c ⊔ (A ⊓ L)) (χ : ↥L ≃* M) {T : Subgroup M}
    (hχ : (A.subgroupOf L).map χ.toMonoidHom = T) (W : Fin 3 → Subgroup M) (z : M)
    (a : Fin 3 → M) (hW4 : ∀ i, Nat.card (W i) = 4) (hWinj : ∀ i j, W i = W j → i = j)
    (hTW : ∀ i, T ≤ Subgroup.normalizer (W i : Set M))
    (hWmax : ∀ Y ∈ invariantPiSubgroups ⊤ T (piOf 2), Y ≠ ⊥ → ∃ i, Y ≤ W i)
    (haW : ∀ i, a i ∈ Subgroup.centralizer (W i : Set M))
    (hzW : ∀ i, z ∉ Subgroup.centralizer (W i : Set M))
    (haW' : ∀ i j, i ≠ j → a i ∉ Subgroup.centralizer (W j : Set M)) (haT : ∀ i, a i ∈ T)
    (hzT : z ∈ T) (hz1 : z ≠ 1)
    (hcases : ∀ t ∈ T, t ≠ 1 → (t = z ∨ t = z ^ 2) ∨
      ∃ i, W i ≤ Subgroup.centralizer ({t} : Set M))
    (hQ : ∀ R : Subgroup G, R ≤ L → A ≤ Subgroup.normalizer (R : Set G) → IsPGroup 2 R →
      R ∈ scriptQPi A (lB A) L (piOf 2)) :
    ∃ d ∈ A ⊓ L, d ≠ 1 ∧
      (∀ u ∈ A, u ∉ Subgroup.closure ({c, d} : Set G) →
        ∃ R ∈ scriptQPiStar A (lB A) L (piOf 2),
          A ⊓ Subgroup.centralizer (R : Set G) = Subgroup.closure {c, u}) ∧
      ∀ R₁ ∈ scriptQPiStar A (lB A) L (piOf 2), ∀ R₂ ∈ scriptQPiStar A (lB A) L (piOf 2),
        A ⊓ Subgroup.centralizer (R₁ : Set G) = A ⊓ Subgroup.centralizer (R₂ : Set G) →
          R₁ = R₂ := by
  have hAχ : ∀ b (hb : b ∈ A ⊓ L), χ ⟨b, hb.2⟩ ∈ T := fun b hb =>
    hχ ▸ ⟨⟨b, hb.2⟩, Subgroup.mem_subgroupOf.mpr hb.1, rfl⟩
  have hχA : ∀ t ∈ T, ((χ.symm t : ↥L) : G) ∈ A := by
    intro t ht
    rw [← hχ] at ht
    obtain ⟨m, hm, rfl⟩ := ht
    have h1 : ((χ.symm (χ.toMonoidHom m) : ↥L) : G) = (m : G) := by simp
    rw [h1]
    exact Subgroup.mem_subgroupOf.mp hm
  have hcC : ∀ S : Subgroup G, S ≤ L → c ∈ Subgroup.centralizer (S : Set G) :=
    fun S hS => Subgroup.mem_centralizer_iff.mpr fun s hs =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLc (hS hs))
  have hAN : ∀ V : Subgroup M, T ≤ Subgroup.normalizer (V : Set M) →
      A ≤ Subgroup.normalizer (preM χ V : Set G) := by
    intro V hV x hx
    obtain ⟨k, -, b, hb, rfl⟩ := exists_pow_mul_of_mem hAel hcA hAa hx
    exact mul_mem (pow_mem (Subgroup.centralizer_le_normalizer _ (hcC _ (preM_le χ V))) k)
      ((mem_normalizer_preM_iff χ hb.2).mpr (hV (hAχ b hb)))
  have hR4 : ∀ i, Nat.card (preM χ (W i)) = 4 := fun i => by rw [card_preM, hW4]
  have hR2 : ∀ i, IsPGroup 2 (preM χ (W i)) := fun i =>
    IsPGroup.of_card (n := 2) (by rw [hR4 i]; norm_num)
  have hRQ : ∀ i, preM χ (W i) ∈ scriptQPi A (lB A) L (piOf 2) := fun i =>
    hQ _ (preM_le χ _) (hAN _ (hTW i)) (hR2 i)
  have hR0 : ∀ i, preM χ (W i) ≠ ⊥ := by
    intro i h0
    have h4 := hR4 i
    rw [h0, Subgroup.card_bot] at h4
    norm_num at h4
  have hle : ∀ S ∈ scriptQPi A (lB A) L (piOf 2), S ≠ ⊥ → ∃ i, S ≤ preM χ (W i) := by
    intro S hS hS0
    have hSL : S ≤ L := hS.1.2
    have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS
    have hAS : A ≤ Subgroup.normalizer (S : Set G) := hS.1.1.1.2.2
    have hinv : imgM χ S ∈ invariantPiSubgroups ⊤ T (piOf 2) := by
      refine ⟨le_top, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr ?_, ?_⟩
      · obtain ⟨k, hk⟩ := hS2.exists_card_eq
        exact IsPGroup.of_card (n := k) (by rw [card_imgM χ hSL, hk])
      · intro t ht
        have hbL := (χ.symm t).2
        have h1 : ((χ.symm t : ↥L) : G) ∈ Subgroup.normalizer (preM χ (imgM χ S) : Set G) := by
          rw [preM_imgM χ hSL]
          exact hAS (hχA t ht)
        have h2 := (mem_normalizer_preM_iff χ hbL).mp h1
        simpa using h2
    have hne : imgM χ S ≠ ⊥ := by
      intro h0
      apply hS0
      have h1 := card_imgM χ hSL
      rw [h0, Subgroup.card_bot] at h1
      exact Subgroup.eq_bot_of_card_eq S h1.symm
    obtain ⟨i, hi⟩ := hWmax _ hinv hne
    exact ⟨i, (imgM_le_iff χ hSL).mp hi⟩
  have hRmax : ∀ i, preM χ (W i) ∈ scriptQPiStar A (lB A) L (piOf 2) := by
    intro i
    refine ⟨hRQ i, fun S hS hiS => ?_⟩
    have hS0 : S ≠ ⊥ := fun h => hR0 i (le_bot_iff.mp (h ▸ hiS))
    obtain ⟨j, hj⟩ := hle S hS hS0
    have hij : W i ≤ W j := by
      have h1 := (imgM_le_iff χ (preM_le χ (W i))).mpr (hiS.trans hj)
      rwa [imgM_preM] at h1
    have heq : W i = W j := Subgroup.eq_of_le_of_card_ge hij (by rw [hW4, hW4])
    rw [← hWinj i j heq] at hj
    exact hj
  have hRstar : ∀ S ∈ scriptQPiStar A (lB A) L (piOf 2), ∃ i, S = preM χ (W i) := by
    intro S hS
    have hS0 : S ≠ ⊥ := by
      intro h0
      have h1 := hS.2 (hRQ 0) (by rw [h0]; exact bot_le)
      rw [h0] at h1
      exact hR0 0 (le_bot_iff.mp h1)
    obtain ⟨i, hi⟩ := hle S hS.prop hS0
    exact ⟨i, hS.eq_of_le (hRQ i) hi⟩
  obtain ⟨d, hd⟩ : ∃ d : G, d = ((χ.symm z : ↥L) : G) := ⟨_, rfl⟩
  have hdAL : d ∈ A ⊓ L := by
    rw [hd]
    exact ⟨hχA _ hzT, (χ.symm _).2⟩
  have hdχ : χ ⟨d, hdAL.2⟩ = z := by
    have h1 : (⟨d, hdAL.2⟩ : ↥L) = χ.symm z := Subtype.ext hd
    rw [h1, MulEquiv.apply_symm_apply]
  have hd1 : d ≠ 1 := by
    intro h1
    apply hz1
    rw [← hdχ]
    have h2 : (⟨d, hdAL.2⟩ : ↥L) = 1 := Subtype.ext h1
    rw [h2, map_one]
  have hdR : ∀ i, d ∉ Subgroup.centralizer (preM χ (W i) : Set G) := fun i h =>
    hzW i (by rw [← hdχ]; exact (mem_centralizer_preM_iff χ hdAL.2).mp h)
  have hcard9 : ∀ i,
      Nat.card (A ⊓ Subgroup.centralizer (preM χ (W i) : Set G) : Subgroup G) ≤ 9 := by
    intro i
    have hdvd : Nat.card (A ⊓ Subgroup.centralizer (preM χ (W i) : Set G) : Subgroup G) ∣
        3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← h27]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hk2 : k ≠ 3 := by
      rintro rfl
      apply hdR i
      have h1 : A ⊓ Subgroup.centralizer (preM χ (W i) : Set G) = A :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk', h27]; norm_num)
      have h2 : d ∈ A ⊓ Subgroup.centralizer (preM χ (W i) : Set G) := by
        rw [h1]
        exact hdAL.1
      exact h2.2
    have hk3 : k ≤ 2 := by omega
    rw [hk']
    calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk3
      _ = 9 := by norm_num
  refine ⟨d, hdAL, hd1, fun u hu hud => ?_, fun R₁ hR₁ R₂ hR₂ hC => ?_⟩
  ·
    exact realize_of_family hAel hcA hcL h27 hAa χ hAχ hcC hd hRmax hcard9 hcases hu hud
  ·
    obtain ⟨i, rfl⟩ := hRstar R₁ hR₁
    obtain ⟨j, rfl⟩ := hRstar R₂ hR₂
    by_contra hne
    have hij : i ≠ j := fun h => hne (h ▸ rfl)
    have haL : ((χ.symm (a i) : ↥L) : G) ∈ A ⊓ L := ⟨hχA _ (haT i), (χ.symm _).2⟩
    have haχ : χ ⟨((χ.symm (a i) : ↥L) : G), haL.2⟩ = a i := by simp
    have h1 : ((χ.symm (a i) : ↥L) : G) ∈
        A ⊓ Subgroup.centralizer (preM χ (W i) : Set G) :=
      ⟨haL.1, (mem_centralizer_preM_iff χ haL.2).mpr (by rw [haχ]; exact haW i)⟩
    rw [hC] at h1
    have h2 := (mem_centralizer_preM_iff χ haL.2).mp h1.2
    rw [haχ] at h2
    exact haW' i j hij h2

end Conclusion

section Concrete

open CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig (V ai card_V V_ne V_le_C A_le_normalizer_V
  le_V_of_mem_invariant z_mem_A)

theorem m12_conclusion
    {A L : Subgroup G} {c : G}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hAel : CFSG.Assembly.IsElemAbelian 3 A)
    (hcA : c ∈ A) (hcL : c ∉ L) (h27 : Nat.card A = 27)
    (hAa : A = Subgroup.zpowers c ⊔ (A ⊓ L)) (χ : ↥L ≃* G12)
    (hχ : (A.subgroupOf L).map χ.toMonoidHom = Toolkit.M12.basisA.sub)
    (hQ : ∀ R : Subgroup G, R ≤ L → A ≤ Subgroup.normalizer (R : Set G) → IsPGroup 2 R →
      R ∈ scriptQPi A (lB A) L (piOf 2)) :
    ∃ d ∈ A ⊓ L, d ≠ 1 ∧
      (∀ u ∈ A, u ∉ Subgroup.closure ({c, d} : Set G) →
        ∃ R ∈ scriptQPiStar A (lB A) L (piOf 2),
          A ⊓ Subgroup.centralizer (R : Set G) = Subgroup.closure {c, u}) ∧
      ∀ R₁ ∈ scriptQPiStar A (lB A) L (piOf 2), ∀ R₂ ∈ scriptQPiStar A (lB A) L (piOf 2),
        A ⊓ Subgroup.centralizer (R₁ : Set G) = A ⊓ Subgroup.centralizer (R₂ : Set G) →
          R₁ = R₂ :=
  conclusion_of_family hLc hAel hcA hcL h27 hAa χ hχ V ⁅Toolkit.M12.x, Toolkit.M12.y⁆ ai card_V
    V_ne A_le_normalizer_V (fun _ hY hne => le_V_of_mem_invariant hY hne) ai_mem_centralizer_V
    z_not_mem_centralizer_V (fun _ _ hij => ai_not_mem_centralizer_V hij) ai_mem_A z_mem_A
    Toolkit.M12.z_ne_one (fun _ ht ht1 => (basisA_point_cases ht ht1).imp id
      fun ⟨i, hi⟩ => ⟨i, by rw [hi]; exact V_le_C i⟩) hQ

end Concrete

end Proof1413Res2

end CFSG.RankThree.PartTwo.Sec14
