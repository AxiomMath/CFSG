module

public import CFSG.OddTranspositions.PartThree.Eleven.Statements
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Hyp
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Pair
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Quandle
public import CFSG.OddTranspositions.PartThree.EightFive.KBarSetup
public import Certificates.Certificate2326
public import Certificates.Certificate1383011
public import CFSG.Certificates.CosetTableShort

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native

private theorem minusQuandleT_lt (i j : Fin 65) :
    minusQuandleT (i : ℕ) (j : ℕ) < 65 := by
  rw [minusQuandleT, ← minusRefl_apply i j]
  exact (minusRefl i j).isLt

private theorem minusQuandleTf_val' (i j : Fin 65) :
    ((minusQuandleTf i j : Fin 65) : ℕ) = minusQuandleT (i : ℕ) (j : ℕ) := by
  show minusQuandleT (i : ℕ) (j : ℕ) % 65 = minusQuandleT (i : ℕ) (j : ℕ)
  rw [Nat.mod_eq_of_lt (minusQuandleT_lt i j)]

private theorem autQuandleTf_eq (i j : Fin 65) :
    minusQuandleTf i j = minusRefl i j := by
  apply Fin.ext
  rw [minusQuandleTf_val', minusRefl_apply]
  rfl

private noncomputable def autF (k : Fin 65) : minusPerm :=
  ⟨minusRefl k, minusRefl_mem k⟩

private theorem autF_injective : Function.Injective autF := by
  intro i j h
  exact minusRefl_injective (Subtype.ext_iff.mp h)

private theorem autF_range : Set.range autF = minusClass := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, rfl⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext hk.symm⟩

private theorem autF_conj (i j : Fin 65) :
    autF i * autF j * (autF i)⁻¹ = autF (minusQuandleTf i j) := by
  apply Subtype.ext
  simp only [autF, Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
  rw [autQuandleTf_eq]
  exact minusRefl_conj i j

private theorem autF_closure_top :
    Subgroup.closure (Set.range autF) = ⊤ := by
  have hset : (Subgroup.subtype minusPerm) '' Set.range autF = Set.range minusRefl := by
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨autF i, ⟨i, rfl⟩, rfl⟩
  have hmap : (Subgroup.closure (Set.range autF)).map (Subgroup.subtype minusPerm) =
      minusPerm := by
    rw [MonoidHom.map_closure, hset, minusPerm]
  rw [eq_top_iff]
  intro x _
  have hx : (x : Equiv.Perm (Fin 65)) ∈
      (Subgroup.closure (Set.range autF)).map (Subgroup.subtype minusPerm) := by
    rw [hmap]
    exact x.2
  rw [Subgroup.mem_map] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have hyx' : y = x := Subtype.ext hyx
  rwa [← hyx']

private theorem conj_autF (g : minusPerm) (k : Fin 65) :
    g * autF k * g⁻¹ = autF ((g : Equiv.Perm (Fin 65)) k) := by
  apply Subtype.ext
  simp only [autF, Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
  exact conj_minusRefl g.2 k

private theorem conj_action_hom (g : minusPerm) (i j : Fin 65) :
    (g : Equiv.Perm (Fin 65)) (minusQuandleTf i j) =
      minusQuandleTf ((g : Equiv.Perm (Fin 65)) i) ((g : Equiv.Perm (Fin 65)) j) := by
  apply minusRefl_injective
  rw [← conj_minusRefl g.2 (minusQuandleTf i j), autQuandleTf_eq i j, ← minusRefl_conj i j]
  calc (g : Equiv.Perm (Fin 65)) * (minusRefl i * minusRefl j * (minusRefl i)⁻¹) *
        (g : Equiv.Perm (Fin 65))⁻¹
      = ((g : Equiv.Perm (Fin 65)) * minusRefl i * (g : Equiv.Perm (Fin 65))⁻¹) *
        ((g : Equiv.Perm (Fin 65)) * minusRefl j * (g : Equiv.Perm (Fin 65))⁻¹) *
        (((g : Equiv.Perm (Fin 65)) * minusRefl i * (g : Equiv.Perm (Fin 65))⁻¹))⁻¹ := by
        group
    _ = minusRefl ((g : Equiv.Perm (Fin 65)) i) * minusRefl ((g : Equiv.Perm (Fin 65)) j) *
        (minusRefl ((g : Equiv.Perm (Fin 65)) i))⁻¹ := by
        rw [conj_minusRefl g.2 i, conj_minusRefl g.2 j]
    _ = minusRefl (minusQuandleTf ((g : Equiv.Perm (Fin 65)) i)
        ((g : Equiv.Perm (Fin 65)) j)) := by
        rw [autQuandleTf_eq]
        exact minusRefl_conj _ _

private theorem exists_mem_minusPerm_word (w : List (Fin 65)) :
    ∃ g : minusPerm, ∀ k : Fin 65, (g : Equiv.Perm (Fin 65)) k = w.foldr minusQuandleTf k := by
  induction w with
  | nil => exact ⟨1, fun k => rfl⟩
  | cons i w ih =>
    obtain ⟨g, hg⟩ := ih
    refine ⟨autF i * g, fun k => ?_⟩
    rw [Subgroup.coe_mul, Equiv.Perm.mul_apply, hg, List.foldr_cons, autQuandleTf_eq]
    rfl

private theorem exists_mem_minusPerm_mul_zero
    (i : Fin 65) :
    ∃ g : minusPerm, (g : Equiv.Perm (Fin 65)) 0 = i := by
  obtain ⟨w, hw⟩ := Certificates.certificate1383011.1 i
  obtain ⟨g, hg⟩ := exists_mem_minusPerm_word w
  exact ⟨g, by rw [hg, hw]⟩

private theorem quandleHom_fixes_zero_mem
    {σ : Fin 65 → Fin 65} (hinj : Function.Injective σ)
    (hhom : ∀ i j : Fin 65, σ (minusQuandleTf i j) = minusQuandleTf (σ i) (σ j))
    (h0 : σ 0 = 0) :
    ∃ g : minusPerm, ∀ k : Fin 65, (g : Equiv.Perm (Fin 65)) k = σ k := by
  obtain ⟨w, hw⟩ := Certificates.certificate1383011.2 σ hinj hhom h0
  obtain ⟨g, hg⟩ := exists_mem_minusPerm_word w
  exact ⟨g, fun k => by rw [hg, hw]⟩

theorem minusClass_aut : ∀ φ : minusPerm ≃* minusPerm, φ '' minusClass = minusClass →
    ∃ g : minusPerm, ∀ x, φ x = g * x * g⁻¹ := by
  intro φ hφ
  have hex : ∀ k : Fin 65, ∃ i : Fin 65, φ (autF k) = autF i := by
    intro k
    have hmem : φ (autF k) ∈ minusClass := by
      rw [← hφ]
      exact Set.mem_image_of_mem φ ⟨k, rfl⟩
    rw [← autF_range] at hmem
    obtain ⟨i, hi⟩ := hmem
    exact ⟨i, hi.symm⟩
  let σ : Fin 65 → Fin 65 := fun k => Classical.choose (hex k)
  have hσ : ∀ k, φ (autF k) = autF (σ k) := fun k => Classical.choose_spec (hex k)
  have hσinj : Function.Injective σ := by
    intro i j hij
    have h : φ (autF i) = φ (autF j) := by rw [hσ i, hσ j, hij]
    exact autF_injective (φ.injective h)
  have hσhom : ∀ i j : Fin 65, σ (minusQuandleTf i j) = minusQuandleTf (σ i) (σ j) := by
    intro i j
    apply autF_injective
    calc autF (σ (minusQuandleTf i j)) = φ (autF (minusQuandleTf i j)) := (hσ _).symm
      _ = φ (autF i * autF j * (autF i)⁻¹) := by rw [← autF_conj i j]
      _ = φ (autF i) * φ (autF j) * (φ (autF i))⁻¹ := by simp only [map_mul, map_inv]
      _ = autF (σ i) * autF (σ j) * (autF (σ i))⁻¹ := by rw [hσ i, hσ j]
      _ = autF (minusQuandleTf (σ i) (σ j)) := autF_conj (σ i) (σ j)
  obtain ⟨g0, hg0⟩ := exists_mem_minusPerm_mul_zero (σ 0)
  let σ' : Fin 65 → Fin 65 := fun k => (g0⁻¹ : Equiv.Perm (Fin 65)) (σ k)
  have hσ'inj : Function.Injective σ' :=
    (g0⁻¹ : Equiv.Perm (Fin 65)).injective.comp hσinj
  have hσ'hom : ∀ i j : Fin 65, σ' (minusQuandleTf i j) = minusQuandleTf (σ' i) (σ' j) := by
    intro i j
    show (g0⁻¹ : Equiv.Perm (Fin 65)) (σ (minusQuandleTf i j)) =
      minusQuandleTf ((g0⁻¹ : Equiv.Perm (Fin 65)) (σ i))
        ((g0⁻¹ : Equiv.Perm (Fin 65)) (σ j))
    rw [hσhom i j]
    exact conj_action_hom g0⁻¹ (σ i) (σ j)
  have hσ'0 : σ' 0 = 0 := by
    show (g0⁻¹ : Equiv.Perm (Fin 65)) (σ 0) = 0
    rw [← hg0]
    simp
  obtain ⟨g, hg⟩ := quandleHom_fixes_zero_mem hσ'inj hσ'hom hσ'0
  refine ⟨g0 * g, ?_⟩
  have hσk : ∀ k : Fin 65, σ k = ((g0 * g : minusPerm) : Equiv.Perm (Fin 65)) k := by
    intro k
    have hgk : (g : Equiv.Perm (Fin 65)) k = σ' k := hg k
    rw [Subgroup.coe_mul, Equiv.Perm.mul_apply, hgk]
    exact (Equiv.apply_symm_apply (g0 : Equiv.Perm (Fin 65)) (σ k)).symm
  have hconj : φ.toMonoidHom = (MulAut.conj (g0 * g)).toMonoidHom := by
    apply MonoidHom.eq_of_eqOn_dense autF_closure_top
    intro x hx
    obtain ⟨k, rfl⟩ := hx
    show φ (autF k) = (MulAut.conj (g0 * g)) (autF k)
    rw [MulAut.conj_apply, hσ k, hσk k]
    exact (conj_autF (g0 * g) k).symm
  intro x
  have hx := DFunLike.congr_fun hconj x
  show φ.toMonoidHom x = (g0 * g) * x * (g0 * g)⁻¹
  rw [hx]
  rfl

end CFSG.OddTranspositions.PartThree
