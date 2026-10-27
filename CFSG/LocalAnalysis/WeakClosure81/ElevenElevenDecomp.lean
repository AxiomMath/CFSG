module

public import CFSG.LocalAnalysis.WeakClosure81.ElevenTenHyp

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit Subgroup
open scoped commutatorElement Pointwise
open CFSG.QuasithinUnique.Lin2 (IsHallTwoPrimeOf ActsRegularlyOn nonIdentity)

variable {G : Type} [Group G] [Finite G]

private theorem inf_centralizer_le_of_autI_le {M V X X' : Subgroup G}
    (hV : IsElemAbelian 2 V) (hMV : M ≤ Subgroup.normalizer (V : Set G)) (hX'M : X' ≤ M)
    (hle : autI hV X' ≤ autI hV X) :
    V ⊓ Subgroup.centralizer (X : Set G) ≤ V ⊓ Subgroup.centralizer (X' : Set G) := by
  intro v hv
  obtain ⟨hvV, hvC⟩ := Subgroup.mem_inf.1 hv
  refine Subgroup.mem_inf.2 ⟨hvV, ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hvC ⊢
  intro x' hx'
  have hx'N : x' ∈ Subgroup.normalizer (V : Set G) := hMV (hX'M hx')
  have hmem : convI hV ⟨x', hx'N⟩ ∈ autI hV X := hle (convI_mem_autI hV hx' hx'N)
  obtain ⟨x, hxX, hxconv⟩ := (mem_autI hV).1 hmem
  have h1 : convI hV x (IntMod.mk hV ⟨v, hvV⟩) =
      convI hV ⟨x', hx'N⟩ (IntMod.mk hV ⟨v, hvV⟩) := by rw [hxconv]
  have h2 := congrArg IntMod.val h1
  rw [convI_apply_val, convI_apply_val] at h2
  change (x : G) * v * (x : G)⁻¹ = x' * v * x'⁻¹ at h2
  have h3 : (x : G) * v * (x : G)⁻¹ = v := by
    rw [hvC (x : G) hxX]; group
  rw [h3] at h2
  exact (mul_inv_eq_iff_eq_mul).1 h2.symm

theorem eleven11_exists_mul_cent
    {M V Q U L X U' L' X' : Subgroup G} (hd : Eleven11Data M V Q U L X)
    (hd' : Eleven11Data M V Q U' L' X')
    (h21 : Nat.card (autI hd.setting.isElemAbelian M) = 21)
    (h3 : Nat.card (autI hd.setting.isElemAbelian X) = 3)
    (h3' : Nat.card (autI hd.setting.isElemAbelian X') = 3) (hne : U ≠ U') :
    ∀ m ∈ M, ∃ g ∈ X ⊔ X', ∃ c ∈ M ⊓ Subgroup.centralizer (V : Set G), m = g * c := by
  have hV := hd.setting.isElemAbelian
  have hXM : X ≤ M := hd.isHall.1.trans inf_le_right
  have hX'M : X' ≤ M := hd'.isHall.1.trans inf_le_right
  have hXU : V ⊓ Subgroup.centralizer (X : Set G) = U := by
    obtain ⟨n, hn, h78, hr, huniq, hD⟩ := hd.ten
    exact (hD X hd.isHall).2.2.1
  have hX'U' : V ⊓ Subgroup.centralizer (X' : Set G) = U' := by
    obtain ⟨n, hn, h78, hr, huniq, hD⟩ := hd'.ten
    exact (hD X' hd'.isHall).2.2.1
  have haut_ne : autI hV X ≠ autI hV X' := by
    intro heq
    apply hne
    rw [← hXU, ← hX'U']
    exact le_antisymm (inf_centralizer_le_of_autI_le hV hd.setting.normal hX'M heq.ge)
      (inf_centralizer_le_of_autI_le hV hd.setting.normal hXM heq.le)
  have hsup : autI hV X ⊔ autI hV X' = autI hV M := by
    have hle : autI hV X ⊔ autI hV X' ≤ autI hV M :=
      sup_le (autI_mono hV hXM) (autI_mono hV hX'M)
    have hdvd : Nat.card ↥(autI hV X ⊔ autI hV X') ∣ 21 := by
      rw [← h21]
      exact Subgroup.card_dvd_of_le hle
    have h3dvd : 3 ∣ Nat.card ↥(autI hV X ⊔ autI hV X') := by
      rw [← h3]
      exact Subgroup.card_dvd_of_le le_sup_left
    have hne3 : Nat.card ↥(autI hV X ⊔ autI hV X') ≠ 3 := by
      intro hc
      apply haut_ne
      have h1 : autI hV X = autI hV X ⊔ autI hV X' :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (le_of_eq (by rw [h3, hc]))
      have h2 : autI hV X' ≤ autI hV X := by rw [h1]; exact le_sup_right
      exact (Subgroup.eq_of_le_of_card_ge h2 (le_of_eq (by rw [h3, h3']))).symm
    have hcard21 : Nat.card ↥(autI hV X ⊔ autI hV X') = 21 := by
      obtain ⟨k, hk⟩ := h3dvd
      have hk7 : k ∣ 7 := by
        have h : 3 * k ∣ 3 * 7 := by rw [← hk]; simpa using hdvd
        exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 3)).1 h
      rcases (Nat.dvd_prime Nat.prime_seven).1 hk7 with hk1 | hk7
      · exact absurd (by rw [hk, hk1, mul_one]) hne3
      · rw [hk, hk7]
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hcard21, h21]))
  intro m hmM
  have hmN : m ∈ Subgroup.normalizer (V : Set G) := hd.setting.normal hmM
  have hXsupM : X ⊔ X' ≤ M := sup_le hXM hX'M
  have hmemM : convI hV ⟨m, hmN⟩ ∈ autI hV (X ⊔ X') := by
    have h1 : convI hV ⟨m, hmN⟩ ∈ autI hV M := convI_mem_autI hV hmM hmN
    rw [← hsup] at h1
    exact (sup_le (autI_mono hV le_sup_left) (autI_mono hV le_sup_right)) h1
  obtain ⟨g, hgX, hgconv⟩ := (mem_autI hV).1 hmemM
  have hgM : (g : G) ∈ M := hXsupM hgX
  let c : G := (g : G)⁻¹ * m
  have hcM : c ∈ M := M.mul_mem (M.inv_mem hgM) hmM
  have hcN : c ∈ Subgroup.normalizer (V : Set G) :=
    (Subgroup.normalizer (V : Set G)).mul_mem
      ((Subgroup.normalizer (V : Set G)).inv_mem g.2) hmN
  have hcCent : c ∈ Subgroup.centralizer (V : Set G) := by
    refine (convI_eq_one_iff hV ⟨c, hcN⟩).1 ?_
    have hsub : (⟨c, hcN⟩ : Subgroup.normalizer (V : Set G)) =
        g⁻¹ * ⟨m, hmN⟩ := by ext; rfl
    rw [hsub, map_mul, map_inv, hgconv, inv_mul_cancel]
  refine ⟨(g : G), hgX, c, Subgroup.mem_inf.2 ⟨hcM, hcCent⟩, ?_⟩
  show m = (g : G) * ((g : G)⁻¹ * m)
  group

theorem eleven11_false_of_normalized_join
    {M V Q U L X U' L' X' E : Subgroup G} (hd : Eleven11Data M V Q U L X)
    (hd' : Eleven11Data M V Q U' L' X')
    (h21 : Nat.card (autI hd.setting.isElemAbelian M) = 21)
    (h3 : Nat.card (autI hd.setting.isElemAbelian X) = 3)
    (h3' : Nat.card (autI hd.setting.isElemAbelian X') = 3) (hne : U ≠ U')
    (hE : E ≠ ⊥) (hE2 : IsPGroup 2 E) (hL : L ≤ Subgroup.normalizer (E : Set G))
    (hL' : L' ≤ Subgroup.normalizer (E : Set G))
    (hC : M ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (E : Set G)) : False := by
  have hXL : X ≤ L := hd.isHall.1.trans inf_le_left
  have hX'L' : X' ≤ L' := hd'.isHall.1.trans inf_le_left
  have hMN : M ≤ Subgroup.normalizer (E : Set G) := by
    intro m hm
    obtain ⟨g, hg, c, hc, rfl⟩ := eleven11_exists_mul_cent hd hd' h21 h3 h3' hne m hm
    have hgN : g ∈ Subgroup.normalizer (E : Set G) :=
      (sup_le (hXL.trans hL) (hX'L'.trans hL')) hg
    exact (Subgroup.normalizer (E : Set G)).mul_mem hgN (hC hc)
  have hNM : Subgroup.normalizer (E : Set G) ≤ M :=
    eleven_b hd.setting.uniqueMax hE hE2 (inf_le_right.trans hMN)
  exact (mem_elevenBlocksB_iff.1 hd.mem_blocks).2 (hL.trans hNM)

end CFSG.LocalAnalysis.WeakClosure81
