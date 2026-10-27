module

public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch10SecC9S3

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem mem_centralizer_of_mem_fsuL0
    (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {x : G}
    (hxL0 : x ∈ fsuL0 T L) (hxL : ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L) :
    x ∈ Subgroup.centralizer (fsuUL T L I : Set G) := by
  obtain ⟨-, -, hdec, -⟩ := h1011 G T L I hyp
  obtain ⟨-, hV1, -, -⟩ := hdec t ht htn
  have hsimp : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    SecA.isSimpleGroup_of_not_normal h37 h38 hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
      hyp.fsu.faithful hyp.not_normal
  have hLN : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  have hV1V : fsuUL T L I ≤ fsuVM T L I := commutator_le_left_of_le_normalizer hLN
  have hx' : x ∈ (↑(L ⊔ CFSG.conjugate L t) : Set G) := by
    rw [← SecA.fsuL0_eq_sup h37 h38 hyp ht htn]
    exact hxL0
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (conjugate_le_normalizer hyp ht)] at hx'
  obtain ⟨l, hl, l', hl', hll'⟩ := hx'
  have hll'' : l * l' = x := hll'
  have hlc : ∀ y ∈ L, ⁅l, y⁆ ∈ pCoreOf 2 L := by
    intro y hy
    have h1 := hxL y hy
    have h2 : l' * y * l'⁻¹ * y⁻¹ ∈ pCoreOf 2 L := by
      have := (SecA.commutator_conjugate_le h37 hyp ht htn
        (Subgroup.commutator_mem_commutator hy hl')).1
      have h3 := (pCoreOf 2 L).inv_mem this
      rwa [commutatorElement_inv, commutatorElement_def] at h3
    have e : ⁅l, y⁆ = (l * (l' * y * l'⁻¹ * y⁻¹) * l⁻¹)⁻¹ * (x * y * x⁻¹ * y⁻¹) := by
      rw [← hll'', commutatorElement_def]
      group
    rw [e]
    refine (pCoreOf 2 L).mul_mem ((pCoreOf 2 L).inv_mem ?_) h1
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hl) _).mp h2
  have hlO := mem_pCoreOf_of_commutator_mem hl hsimp
    (nonabelian_of_isQuasisimple hyp.fsu.quasisimple) hlc
  have hlV := pCoreOf_L_le_centralizer hyp h1011 hlO
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  rw [← hll'']
  have h4 : l * v = v * l := (Subgroup.mem_centralizer_iff.mp hlV v (hV1V hv)).symm
  have h5 : l' * v = v * l' := Subgroup.mem_centralizer_iff.mp (hV1 hv) l' hl'
  calc v * (l * l') = l * v * l' := by rw [← mul_assoc, ← h4]
    _ = l * l' * v := by rw [mul_assoc, ← h5, ← mul_assoc]

theorem false_of_torus (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h1013 : Stmt10_1_3) (h1026 : Stmt10_2_6) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {n : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n)
    (eL : ↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F) {x : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hodd : Odd (orderOf x))
    (hp : ∀ p : ℕ, p.Prime → p ∣ orderOf x → p ∣ 2 ^ n - 1)
    (hxL : ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L)
    (hxC : x ∉ Subgroup.centralizer (fsuUL T L I : Set G)) : False := by
  have hXM : Subgroup.zpowers x ≤ fsuM T L :=
    (Subgroup.zpowers_le).mpr ((h1026 G T L I hyp).2.2 hxN)
  have hXL0 : Subgroup.zpowers x ≤ fsuL0 T L := by
    refine le_fsuL0_of_dvd hyp h1013 hXM (by rw [Nat.card_zpowers]) fun p hpp hpN => ⟨?_, ?_⟩
    · rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpN)
    · rw [Nat.card_congr eL.toEquiv]
      exact (hp p hpp hpN).trans (hF ▸ card_sub_one_dvd_card_SL F)
  exact hxC (mem_centralizer_of_mem_fsuL0 h37 h38 hyp h1011 ht htn
    (hXL0 (Subgroup.mem_zpowers x)) hxL)

end CFSG.Quasithin.Vol2.Ch10.SecC
