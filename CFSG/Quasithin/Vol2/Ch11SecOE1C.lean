module

public import CFSG.Quasithin.Vol2.Ch11SecOE1B
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs


public section

namespace CFSG.Quasithin.Vol2.Ch11

open Subgroup CFSG.Quasithin CFSG.Quasithin.H13

namespace OE1

variable {G : Type} [Group G]

theorem conjClosure_conjClosure_of_le {I T M : Subgroup G} (hTM : T ≤ M) :
    conjClosure (conjClosure I T) M = conjClosure I M := by
  apply le_antisymm
  · refine conjClosure_le fun m hm v hv => ?_
    induction hv using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨t, ht, i, hi, rfl⟩ := hx
      have e : m * (t * i * t⁻¹) * m⁻¹ = (m * t) * i * (m * t)⁻¹ := by group
      rw [e]
      exact mem_conjClosure (M.mul_mem hm (hTM ht)) hi
    | one =>
      rw [mul_one, mul_inv_cancel]
      exact one_mem _
    | mul x y _ _ hx hy =>
      have e : m * (x * y) * m⁻¹ = (m * x * m⁻¹) * (m * y * m⁻¹) := by group
      rw [e]
      exact mul_mem hx hy
    | inv x _ hx =>
      have e : m * x⁻¹ * m⁻¹ = (m * x * m⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem hx
  · exact conjClosure_mono (le_conjClosure I T) le_rfl

theorem conj_mem_centralizer {X : Subgroup G} {m z : G} (hm : m ∈ normalizer (X : Set G))
    (hz : z ∈ centralizer (X : Set G)) : m * z * m⁻¹ ∈ centralizer (X : Set G) :=
  (mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer X hm) z).mp hz

end OE1

theorem tmpL6_3_2_2_four_of (h322 : Ch10.TmpL6_3_2_2_two) : TmpL6_3_2_2_four := by
  intro G _ _ T L I hfsu
  have hTM : T ≤ fsuM T L := le_normalizer_conjClosure L T
  have hL0M : fsuL0 T L ≤ fsuM T L := le_normalizer
  have hVM : fsuVM T L I = conjClosure I (fsuM T L) := OE1.conjClosure_conjClosure_of_le hTM
  obtain ⟨-, -, hL0I, hIL0, hlt, hirr, -⟩ := hfsu.irrPlus
  have hab : ∀ a ∈ conjClosure I (fsuM T L), ∀ b ∈ conjClosure I (fsuM T L),
      a * b = b * a := by
    obtain ⟨hle, ⟨-, hel, -⟩⟩ := h322 G T L I hfsu
    intro a ha b hb
    rw [← hVM] at ha hb
    have h := hel.toIsMulCommutative.is_comm.comm
      (⟨⟨a, hle ha⟩, mem_subgroupOf.mpr ha⟩ : ↥((fsuVM T L I).subgroupOf (fsuM T L)))
      ⟨⟨b, hle hb⟩, mem_subgroupOf.mpr hb⟩
    exact congrArg (fun x : ↥((fsuVM T L I).subgroupOf (fsuM T L)) =>
      ((x : ↥(fsuM T L)) : G)) h
  have hkey : fsuCVM T L I ≤ conjClosure (I ⊓ centralizer (fsuL0 T L : Set G)) (fsuM T L) := by
    show fsuVM T L I ⊓ centralizer (fsuL0 T L : Set G) ≤ _
    rw [hVM]
    exact OE1.conjClosure_inf_centralizer_le hab hL0M le_rfl hL0I hIL0 hlt hirr
  have hcl : ∀ Y : Subgroup G, Y ≤ fsuVM T L I →
      conjClosure (Y ⊓ centralizer (fsuL0 T L : Set G)) (fsuM T L) ≤ fsuCVM T L I := by
    intro Y hY
    refine conjClosure_le fun m hm z hz => ⟨?_, OE1.conj_mem_centralizer hm hz.2⟩
    exact (mem_normalizer_iff.mp (le_normalizer_conjClosure (fsuV T I) (fsuM T L) hm) z).mp
      (hY hz.1)
  have hIV : I ≤ fsuV T I := le_conjClosure I T
  have hVVM : fsuV T I ≤ fsuVM T L I := le_conjClosure _ _
  have h12 : conjClosure (I ⊓ centralizer (fsuL0 T L : Set G)) (fsuM T L) ≤
      conjClosure (fsuV T I ⊓ centralizer (fsuL0 T L : Set G)) (fsuM T L) :=
    conjClosure_mono (inf_le_inf_right _ hIV) le_rfl
  exact ⟨le_antisymm hkey (hcl I (hIV.trans hVVM)),
    le_antisymm (hkey.trans h12) (hcl (fsuV T I) hVVM)⟩

end CFSG.Quasithin.Vol2.Ch11
