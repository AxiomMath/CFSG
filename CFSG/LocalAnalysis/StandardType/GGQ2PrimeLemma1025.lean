module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeLemma1025Basic
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeLemma1025Coords
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeLemma1025Torus
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeLemma1025Count
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeO1ppModels
import CFSG.LocalAnalysis.StandardType.GGQ2PrimeU52Torus
import CFSG.LocalAnalysis.StandardType.GGQ2PrimeU52TorusU42

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models CFSG.Assembly CFSG.StandardType

private theorem lem1025_exists_t {G : Type} [Group G] {Bs X : Subgroup G} {zk : G}
    (hX : LieModel X .PSU 5 2 1) (hBab : IsElemAbelian 3 Bs) (hBX : Bs ≤ normalizer (X : Set G))
    (hzk : zk ∈ Bs) (hcard : Nat.card (Bs ⊓ X : Subgroup G) = 3 ^ 4) :
    ∃ t ∈ Bs ⊓ X, ∀ y ∈ X, zk * y * zk⁻¹ = t * y * t⁻¹ := by
  obtain ⟨t, htX, ht⟩ := inner_of_U52 hX (hBX hzk) (hBab.2 zk hzk)
  refine ⟨t, centralizer_torus_le_of_U52 hX (lem1025_elemAbelian_of_le hBab inf_le_left)
    inf_le_right hcard (mem_inf.2 ⟨htX, mem_centralizer_iff.2 ?_⟩), ht⟩
  intro s hs
  have e : t * s * t⁻¹ = s := by
    rw [← ht s hs.2, elemAbelian_comm' hBab hzk hs.1]
    group
  rw [mul_inv_eq_iff_eq_mul] at e
  exact e.symm

theorem lemma1025Input_of_lemma101cInput (hc : Lemma101cInput) : Lemma1025Input := by
  intro G _ _ B Bs x L A κ m n k g g' X hctx hnm hkm hkn hg hgl hg' hgl' hX hXle hXL hXB
  have hS := hctx.setting
  have hW := hctx.coords
  have hBab : IsElemAbelian 3 Bs := hS.bstar.2.1
  have hx : x ∈ Bs := hW.x_mem
  have hznB : g * x * g⁻¹ ∈ Bs := (mem_normalizer_iff.1 hg x).1 hx
  have hzkB : g' * x * g'⁻¹ ∈ Bs := (mem_normalizer_iff.1 hg' x).1 hx
  have hcn := lem1025_coord_conj hW hgl hznB
  have hck := lem1025_coord_conj hW hgl' hzkB
  have hXL' : X ≤ L := hXle.trans inf_le_left
  obtain ⟨X', hX'm, hX'le, hX'split, hX'L, -⟩ := hc G B Bs x L A κ m n g hctx hnm hg hgl
  obtain ⟨hHH, -⟩ := lem1025_eq_comm_of_split hX hX'm hXle (hX'le.trans inf_le_left) hX'split
  have hBX : Bs ≤ normalizer (X : Set G) := fun b hb => by
    rw [← hHH]
    exact lem1025_mem_normalizer_comm
      (lem1025_mem_normalizer_cent (hS.Bs_norm hb) (elemAbelian_comm' hBab hb hznB))
  have hXU : X ≤ normalizer (O2Z L : Set G) :=
    (hXL'.trans (L_le_cent_O2Z L)).trans (centralizer_le_normalizer _)
  obtain ⟨hTcard, hdec⟩ := lem1025_torus_data hX hBab hBX (O2Z_ne_bot hctx.even) (O2Z_two L)
    (hS.Bs_norm.trans (norm_le_norm_O2Z L)) hXU (cor_9_5 hS hctx.even).2.le hS.Bs_card
    (by rw [hXB]; exact lem1025_card_closure_pair hW hnm hBab hznB hcn)
  have hTab : IsElemAbelian 3 (Bs ⊓ X : Subgroup G) := lem1025_elemAbelian_of_le hBab inf_le_left
  obtain ⟨t, htT, ht⟩ := lem1025_exists_t hX hBab hBX hzkB hTcard
  have hxcl : x ∈ closure ({x, x * (g * x * g⁻¹)⁻¹} : Set G) := subset_closure (Or.inl rfl)
  have hbcl : x * (g * x * g⁻¹)⁻¹ ∈ closure ({x, x * (g * x * g⁻¹)⁻¹} : Set G) :=
    subset_closure (Or.inr rfl)
  have ht1 : t ≠ 1 := by
    intro h1
    obtain ⟨p, hpm, hpn, hpk⟩ : ∃ p : Fin 7, p ≠ m ∧ p ≠ n ∧ p ≠ k :=
      (by decide : ∀ m n k : Fin 7, ∃ p : Fin 7, p ≠ m ∧ p ≠ n ∧ p ≠ k) m n k
    refine lem1025_not_mem_closure hW hkm hkn hpm hpn hpk hznB hcn hzkB hck ?_
    rw [← hXB]
    refine ⟨hzkB, mem_centralizer_iff.2 fun y hy => ?_⟩
    have h2 := ht y hy
    rw [h1, one_mul, inv_one, mul_one] at h2
    exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  have hzkt : ∀ y ∈ X, y * (g' * x * g'⁻¹) = (g' * x * g'⁻¹) * y → y * t = t * y := by
    intro y hy hyz
    have e : t * y * t⁻¹ = y := by
      rw [← ht y hy]
      exact mul_inv_eq_iff_eq_mul.2 hyz.symm
    rw [mul_inv_eq_iff_eq_mul] at e
    exact e.symm
  have hznmem : g * x * g⁻¹ ∈ closure ({x, x * (g * x * g⁻¹)⁻¹} : Set G) := by
    have := mul_mem (inv_mem hbcl) hxcl
    rwa [show (x * (g * x * g⁻¹)⁻¹)⁻¹ * x = g * x * g⁻¹ by group] at this
  have hxC : x ∈ centralizer (X : Set G) := by
    have : x ∈ Bs ⊓ centralizer (X : Set G) := by rw [hXB]; exact hxcl
    exact this.2
  have hznC : g * x * g⁻¹ ∈ centralizer (X : Set G) := by
    have : g * x * g⁻¹ ∈ Bs ⊓ centralizer (X : Set G) := by rw [hXB]; exact hznmem
    exact this.2
  have hcount := lem1025_count hW hctx.AL_le hnm.symm hkm.symm hkn.symm hXL' inf_le_left hdec
    hxC hznC hznB hcn hzkB hck hzkt
    (le_ncard_conj_torus_of_U52 hX hTab inf_le_right hTcard)
  obtain ⟨Y, hYm, hYle⟩ := exists_U42_of_U52_torus hX hTab inf_le_right hTcard htT ht1 hcount
  have hYz : Y ≤ X ⊓ centralizer ({g' * x * g'⁻¹} : Set G) := fun y hy =>
    mem_inf.2 ⟨(hYle hy).1, mem_centralizer_singleton_iff.2 (by
      have h1 := mem_centralizer_singleton_iff.1 (hYle hy).2
      have h2 := ht y (hYle hy).1
      rw [mul_inv_eq_iff_eq_mul.2 h1.symm] at h2
      exact (mul_inv_eq_iff_eq_mul.1 h2).symm)⟩
  obtain ⟨X'', -, hX''le, hX''split, hX''L, -⟩ := hc G B Bs x L A κ m k g' hctx hkm hg' hgl'
  have hYH : Y ≤ L ⊓ centralizer ({g' * x * g'⁻¹} : Set G) := fun y hy =>
    ⟨hXL' (hYz hy).1, (hYz hy).2⟩
  exact ⟨Y, hYm, hYz, (lem1025_le_comm_U42 hYm).trans ((commutator_mono hYH hYH).trans
    (lem1025_comm_le_of_split (hX''le.trans inf_le_left) hX''split)) |>.trans hX''L⟩

end CFSG.GGQ2Prime
