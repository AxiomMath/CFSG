module

public import CFSG.Quasithin.Vol2.Ch10SecC10
public import CFSG.Quasithin.Vol2.Ch10SecABasicV

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G]

theorem inf_conjSubgroup_eq_bot_of_mem {T L I B A : Subgroup G} (hyp : Hyp10 G T L I)
    (hsimp : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)) (hBA : fsuL0 T L = B ⊔ A)
    (hBn : fsuL0 T L ≤ Subgroup.normalizer (B : Set G))
    (hAn : fsuL0 T L ≤ Subgroup.normalizer (A : Set G))
    (hB : ∃ s, B = CFSG.conjugate L s) (hA : ∃ s, A = CFSG.conjugate L s)
    (hOA : pCoreOf 2 A ≤ Subgroup.centralizer (fsuVM T L I : Set G)) {W : Subgroup G}
    (hW : fsuVM T L I ⊓ Subgroup.centralizer (B : Set G) = W)
    (hnc : ∀ x ∈ fsuVM T L I, x ≠ 1 → x ∉ Subgroup.centralizer (fsuL0 T L : Set G))
    {g : G} (hgM : g ∈ fsuM T L) (hgn : g ∉ Subgroup.normalizer (W : Set G)) :
    W ⊓ conjSubgroup W g = ⊥ := by
  have hLperf : ⁅L, L⁆ = L := commutator_self_of_local hyp.fsu.faithful.1
  have hMV : fsuM T L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    le_normalizer_conjClosure (fsuV T I) (fsuM T L)
  rw [eq_bot_iff]
  rintro x ⟨hxW, hxg⟩
  rw [Subgroup.mem_bot]
  by_contra hx1
  rw [← hW] at hxW hxg
  have hgx : g * x * g⁻¹ ∈ fsuVM T L I ⊓ Subgroup.centralizer (B : Set G) :=
    mem_conjSubgroup_iff.mp hxg
  have hxA : x ∉ Subgroup.centralizer (A : Set G) := fun h =>
    hnc x hxW.1 hx1 (hBA ▸ mem_centralizer_sup hxW.2 h)
  have hBx : B ≤ Subgroup.centralizer ({x} : Set G) := mem_centralizer_iff_le.mp hxW.2
  have hBgx : CFSG.conjugate B g ≤ Subgroup.centralizer ({x} : Set G) :=
    conjugate_le_centralizer (mem_centralizer_iff_le.mp hgx.2)
  have hBgL0 : CFSG.conjugate B g ≤ fsuL0 T L := by
    rintro _ ⟨y, hy, rfl⟩
    have hyL0 : y ∈ fsuL0 T L := hBA ▸ Subgroup.mem_sup_left hy
    simpa [MulAut.conj_apply] using
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgM) y).mp hyL0
  have hKc : ∃ s, CFSG.conjugate B g = CFSG.conjugate L s := by
    obtain ⟨s, rfl⟩ := hB
    exact ⟨s * g, SecA.conjugate_conjugate L s g⟩
  have hle := le_of_le_fsuL0_of_le_centralizer hLperf hsimp hBA hBn hAn hA hKc hOA hxW.1 hBx hxA
    hBgL0 hBgx
  have heq : CFSG.conjugate B g = B := Subgroup.eq_of_le_of_card_ge hle (card_conjugate B g).ge
  apply hgn
  rw [← hW]
  exact mem_normalizer_inf_centralizer (hMV hgM) (SecA.conjugate_eq_self_iff.mp heq)

theorem isTISetIn_of_cvm_eq_bot {T L I : Subgroup G} (hyp : Hyp10 G T L I)
    (h1011 : Stmt10_1_1) (h1013 : Stmt10_1_3) (h1026 : Stmt10_2_6) (h1029 : Stmt10_2_9)
    (hsimp : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) (hL0 : fsuL0 T L = L ⊔ CFSG.conjugate L t)
    (hn : fsuL0 T L ≤ Subgroup.normalizer (L : Set G))
    (hnt : fsuL0 T L ≤ Subgroup.normalizer (CFSG.conjugate L t : Set G))
    (hcv : fsuCVM T L I = ⊥) {K : Subgroup G} (hK : K = L ∨ K = CFSG.conjugate L t) :
    IsTISetIn ⁅fsuVM T L I, K⁆ ⊤ := by
  set V := fsuVM T L I with hV
  set Lt := CFSG.conjugate L t with hLt
  obtain ⟨hVM, hR, hdec, -⟩ := h1011 G T L I hyp
  obtain ⟨hVeq, hV1Lt, hV2L, -⟩ := hdec t ht htn
  obtain ⟨hVc, -⟩ := hyp.three
  have hMV : fsuM T L ≤ Subgroup.normalizer (V : Set G) :=
    le_normalizer_conjClosure (fsuV T I) (fsuM T L)
  have hTM : T ≤ fsuM T L := le_normalizer_conjClosure L T
  have hLL0 : L ≤ fsuL0 T L := le_conjClosure L T
  have hLtL0 : Lt ≤ fsuL0 T L := SecA.conjugate_le_fsuL0 ht
  have hV1V : ⁅V, L⁆ ≤ V :=
    commutator_le_left_of_le_normalizer (hLL0.trans (Subgroup.le_normalizer.trans hMV))
  have hV2V : ⁅V, Lt⁆ ≤ V :=
    commutator_le_left_of_le_normalizer (hLtL0.trans (Subgroup.le_normalizer.trans hMV))
  have hOL : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) :=
    pCoreOf_le_centralizer_of_subnormal hR hVM (subnormal_of_le_normalizer hLL0 hn)
  have hOLt : pCoreOf 2 Lt ≤ Subgroup.centralizer (V : Set G) :=
    pCoreOf_le_centralizer_of_subnormal hR hVM (subnormal_of_le_normalizer hLtL0 hnt)
  have hnc : ∀ x ∈ V, x ≠ 1 → x ∉ Subgroup.centralizer (fsuL0 T L : Set G) := by
    intro x hx hx1 hxc
    have : x ∈ fsuCVM T L I := ⟨hx, hxc⟩
    rw [hcv, Subgroup.mem_bot] at this
    exact hx1 this
  have hL0' : fsuL0 T L = Lt ⊔ L := by rw [hL0, sup_comm]
  rcases hK with hK | hK <;> rw [hK] <;> refine ⟨le_top, fun g _ hgn => ?_⟩
  · have hW : V ⊓ Subgroup.centralizer (Lt : Set G) = ⁅V, L⁆ :=
      inf_centralizer_eq_of_cvm_eq_bot hVc hcv hL0' hVeq hV1Lt hV2L hV1V hV2V
    by_cases hgM : g ∈ fsuM T L
    · exact inf_conjSubgroup_eq_bot_of_mem hyp hsimp hL0' hnt hn ⟨t, rfl⟩
        ⟨1, (SecA.conjugate_one L).symm⟩ hOL hW hnc hgM hgn
    ·
      have hg' : t⁻¹ * g * t ∉ fsuM T L := by
        intro h
        apply hgM
        have : g = t * (t⁻¹ * g * t) * t⁻¹ := by group
        rw [this]
        exact (fsuM T L).mul_mem ((fsuM T L).mul_mem (hTM ht) h) ((fsuM T L).inv_mem (hTM ht))
      have h1 := inf_conjSubgroup_eq_bot hyp h1011 h1013 h1026 h1029 hsimp ht htn hL0 hn hnt hg'
      have hconj : CFSG.conjugate ⁅V, L⁆ t = ⁅V, Lt⁆ := SecA.conjugate_commutator_fsuVM (hTM ht)
      rw [eq_bot_iff]
      rintro x ⟨hx1, hxg⟩
      have hy1 : t⁻¹ * x * t ∈ ⁅V, Lt⁆ := by
        rw [← hconj, SecA.mem_conjugate_iff]
        have : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
        rw [this]
        exact hx1
      have hy2 : t⁻¹ * x * t ∈ conjSubgroup ⁅V, Lt⁆ (t⁻¹ * g * t) := by
        rw [mem_conjSubgroup_iff, ← hconj, SecA.mem_conjugate_iff]
        have : t * (t⁻¹ * g * t * (t⁻¹ * x * t) * (t⁻¹ * g * t)⁻¹) * t⁻¹ = g * x * g⁻¹ := by
          group
        rw [this]
        exact mem_conjSubgroup_iff.mp hxg
      have hy : t⁻¹ * x * t ∈ ⁅V, Lt⁆ ⊓ conjSubgroup ⁅V, Lt⁆ (t⁻¹ * g * t) := ⟨hy1, hy2⟩
      rw [h1, Subgroup.mem_bot] at hy
      rw [Subgroup.mem_bot]
      have : x = t * (t⁻¹ * x * t) * t⁻¹ := by group
      rw [this, hy]
      group
  · have hW : V ⊓ Subgroup.centralizer (L : Set G) = ⁅V, Lt⁆ :=
      inf_centralizer_eq_of_cvm_eq_bot hVc hcv hL0 (by rw [sup_comm]; exact hVeq) hV2L hV1Lt hV2V
        hV1V
    by_cases hgM : g ∈ fsuM T L
    · exact inf_conjSubgroup_eq_bot_of_mem hyp hsimp hL0 hn hnt ⟨1, (SecA.conjugate_one L).symm⟩
        ⟨t, rfl⟩ hOLt hW hnc hgM hgn
    · exact inf_conjSubgroup_eq_bot hyp h1011 h1013 h1026 h1029 hsimp ht htn hL0 hn hnt hgM

end CFSG.Quasithin.Vol2.Ch10.SecC
