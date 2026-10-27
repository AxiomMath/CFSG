module

public import CFSG.Quasithin.Vol2.Ch10SecB3Wr

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique
open scoped Pointwise

namespace L32

theorem pa_inv_three : ∀ g : Γ, IsPa g → g ^ 3 = 1 → g ≠ 1 →
    ∃ u : Γ, IsU u ∧ u * g * u⁻¹ = g⁻¹ := by
  unfold IsPa IsU ent; decide +kernel

theorem pb_inv_three : ∀ g : Γ, IsPb g → g ^ 3 = 1 → g ≠ 1 →
    ∃ u : Γ, IsU u ∧ u * g * u⁻¹ = g⁻¹ := by
  unfold IsPb IsU ent; decide +kernel

theorem pa_three : ∃ g : Γ, IsPa g ∧ g ^ 3 = 1 ∧ g ≠ 1 := by
  unfold IsPa ent; decide +kernel

theorem pb_three : ∃ g : Γ, IsPb g ∧ g ^ 3 = 1 ∧ g ≠ 1 := by
  unfold IsPb ent; decide +kernel

end L32

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

namespace Ctx3

variable {H B : Subgroup G} {t : G} {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ} {α : MulAut L32.Γ}
  {ψ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* L32.Γ}

theorem le_fsuL0 (c : Ctx3 T L I H B t Ψ α ψ) : B ≤ fsuL0 T L := fun _ hb => (c.le_Y hb).2

theorem exists_normalizer (c : Ctx3 T L I H B t Ψ α ψ) (hB1 : B ≠ ⊥) {u v : L32.Γ}
    (hu : L32.IsU u) (hv : L32.IsU v)
    (huv : ∀ p ∈ imgIn Ψ B, (u, v) * p * (u, v)⁻¹ ∈ imgIn Ψ B) :
    ∃ (x : G) (hx0 : x ∈ fsuL0 T L), x ∈ T0 T L ∧
      x ∈ Subgroup.normalizer (B : Set G) ∧ Ψ ⟨x, hx0⟩ = (u, v) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨A, hA, hY, -, -⟩ := c.img_eq_prod hB1
  have huv' : (u, v) ∈ ((T0 T L).subgroupOf (fsuL0 T L)).map Ψ := by
    rw [c.hC.T0]
    exact ⟨hu, hv⟩
  obtain ⟨⟨x₀, hx₀0⟩, hx₀T, hx₀⟩ := huv'
  have hx₀T0 : x₀ ∈ T0 T L := Subgroup.mem_subgroupOf.mp hx₀T
  set BO := preIn Ψ (imgIn Ψ B) with hBO
  have hBBO : B ≤ BO := fun b hb => mem_preIn.mpr ⟨c.le_fsuL0 hb,
    mem_imgIn.mpr ⟨b, c.le_fsuL0 hb, hb, rfl⟩⟩
  have hBOX : BO ≤ H ⊓ fsuM T L := by
    have hBA : imgIn Ψ B ≤ A.prod A := by
      rw [← imgIn_preIn c.hC.surj (A.prod A), ← hY]
      exact imgIn_mono Ψ c.le_Y
    exact (preIn_mono Ψ hBA).trans (hY ▸ inf_le_left)
  obtain ⟨j, hj⟩ := c.relIndex_two_pow hBBO hBOX
  have hHall : QuasithinUnique.Lin2.IsHallTwoPrimeOf B BO := ⟨hBBO, c.hB.2.1, j, hj⟩
  set f : G →* G := (MulAut.conj x₀).toMonoidHom with hf
  have hle : B.map f ≤ BO := by
    rintro _ ⟨b, hb, rfl⟩
    have hb0 := c.le_fsuL0 hb
    have hm : x₀ * b * x₀⁻¹ ∈ fsuL0 T L :=
      (fsuL0 T L).mul_mem ((fsuL0 T L).mul_mem hx₀0 hb0) ((fsuL0 T L).inv_mem hx₀0)
    refine mem_preIn.mpr ⟨by simpa [hf, MulAut.conj_apply] using hm, ?_⟩
    have e : (⟨x₀ * b * x₀⁻¹, hm⟩ : ↥(fsuL0 T L)) = ⟨x₀, hx₀0⟩ * ⟨b, hb0⟩ * ⟨x₀, hx₀0⟩⁻¹ := rfl
    have h1 := huv _ (mem_imgIn.mpr ⟨b, hb0, hb, rfl⟩)
    rw [← hx₀, ← map_inv, ← map_mul, ← map_mul, ← e] at h1
    simpa [hf, MulAut.conj_apply] using h1
  have hP : IsPGroup 3 (B.map f) :=
    (IsPGroup.of_card (n := 2) (by rw [c.card_eq_nine hB1]; norm_num)).map f
  obtain ⟨y, hyBO, hy⟩ := Ch11.SecB.exists_conj_le_hall (by norm_num) hHall hle hP
  obtain ⟨hy0, hyB⟩ := mem_preIn.mp hyBO
  obtain ⟨b, hb0, hbB, hb⟩ := mem_imgIn.mp hyB
  set k := y * b⁻¹ with hk
  have hk0 : k ∈ fsuL0 T L := (fsuL0 T L).mul_mem hy0 ((fsuL0 T L).inv_mem hb0)
  have hkO : k ∈ pCoreOf 2 (fsuL0 T L) := by
    apply (c.hC.ker ⟨k, hk0⟩).mp
    have e : (⟨k, hk0⟩ : ↥(fsuL0 T L)) = ⟨y, hy0⟩ * ⟨b, hb0⟩⁻¹ := rfl
    rw [e, map_mul, map_inv, hb, mul_inv_cancel]
  have hkT0 : k ∈ T0 T L := SecA.pCoreOf_fsuL0_le_T0 c.hyp.fsu.sylow hkO
  set x := k⁻¹ * x₀ with hx
  have hx0 : x ∈ fsuL0 T L := (fsuL0 T L).mul_mem ((fsuL0 T L).inv_mem hk0) hx₀0
  have hxB : B.map (MulAut.conj x).toMonoidHom ≤ B := by
    rintro _ ⟨z, hz, rfl⟩
    have h1 : x₀ * z * x₀⁻¹ ∈ conjSub y B := hy ⟨z, hz, rfl⟩
    rw [mem_conjSub] at h1
    have e : x * z * x⁻¹ = b * (y⁻¹ * (x₀ * z * x₀⁻¹) * y) * b⁻¹ := by
      rw [hx, hk]; group
    simpa [MulAut.conj_apply, e] using B.mul_mem (B.mul_mem hbB h1) (B.inv_mem hbB)
  have hxN : x ∈ Subgroup.normalizer (B : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe]
    refine Subgroup.eq_of_le_of_card_ge hxB ?_
    rw [← Nat.card_congr (B.equivMapOfInjective _ (MulAut.conj x).injective).toEquiv]
  refine ⟨x, hx0, (T0 T L).mul_mem ((T0 T L).inv_mem hkT0) hx₀T0, hxN, ?_⟩
  have e : (⟨x, hx0⟩ : ↥(fsuL0 T L)) = ⟨k, hk0⟩⁻¹ * ⟨x₀, hx₀0⟩ := rfl
  rw [e, map_mul, map_inv, (c.hC.ker ⟨k, hk0⟩).mpr hkO, inv_one, one_mul, hx₀]

theorem pCoreOf_le_T1 (c : Ctx3 T L I H B t Ψ α ψ) (hB1 : B ≠ ⊥) :
    pCoreOf 2 (H ⊓ fsuM T L) ≤ T1 T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hA, hY, -⟩ := c.classify' hB1
  have hTS : QuasithinUnique.IsSylowTwoOf T (H ⊓ fsuM T L) :=
    isSylowTwoOf_of_quasithinIsSylowTwo c.hyp.fsu.sylow c.T_le
  have hOT : pCoreOf 2 (H ⊓ fsuM T L) ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hTS
  intro o ho
  refine ⟨hOT ho, ?_⟩
  by_contra hon
  obtain ⟨g, hgA, hg3, hg1⟩ : ∃ g : L32.Γ, g ∈ A ∧ g ^ 3 = 1 ∧ g ≠ 1 := by
    rcases hA with rfl | rfl
    · obtain ⟨g, h1, h2, h3⟩ := L32.pa_three
      exact ⟨g, h1, h2, h3⟩
    · obtain ⟨g, h1, h2, h3⟩ := L32.pb_three
      exact ⟨g, h1, h2, h3⟩
  obtain ⟨⟨l, hl⟩, hq⟩ := QuotientGroup.mk_surjective (ψ.symm g)
  have hl0 : l ∈ fsuL0 T L := SecA.le_fsuL0 T L hl
  have hΨl : Ψ ⟨l, hl0⟩ = (g, 1) := by
    rw [c.hC.onL l hl0 hl, mkO2, hq, MulEquiv.apply_symm_apply]
  have hlX : l ∈ H ⊓ fsuM T L := by
    have : l ∈ (H ⊓ fsuM T L) ⊓ fsuL0 T L := by
      rw [hY]
      exact mem_preIn.mpr ⟨hl0, by rw [hΨl]; exact ⟨hgA, A.one_mem⟩⟩
    exact this.1
  have hoT : o ∈ T := hOT ho
  have hoLt : o * l * o⁻¹ ∈ CFSG.conjugate L t := by
    have hon' : o⁻¹ ∉ Subgroup.normalizer (L : Set G) := fun h =>
      hon (by simpa using (Subgroup.normalizer _).inv_mem h)
    rw [← SecA.conjugate_eq_of_not_mem c.h37 c.h38 c.hyp c.ht c.htn (T.inv_mem hoT) hon',
      SecA.mem_conjugate_iff]
    simpa [mul_assoc] using hl
  set z := o * l * o⁻¹ * l⁻¹ with hz
  have hzO : z ∈ pCoreOf 2 (H ⊓ fsuM T L) := by
    have hN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ fsuM T L) hlX
    have h1 : l * o⁻¹ * l⁻¹ ∈ pCoreOf 2 (H ⊓ fsuM T L) :=
      (Subgroup.mem_normalizer_iff.mp hN _).mp (Subgroup.inv_mem _ ho)
    have := Subgroup.mul_mem _ ho h1
    simpa [hz, mul_assoc] using this
  have hoL0 : o * l * o⁻¹ ∈ fsuL0 T L := SecA.conjugate_le_fsuL0 c.ht hoLt
  have hz0 : z ∈ fsuL0 T L := (fsuL0 T L).mul_mem hoL0 ((fsuL0 T L).inv_mem hl0)
  have hΨz : (Ψ ⟨z, hz0⟩).1 = g⁻¹ := by
    have e : (⟨z, hz0⟩ : ↥(fsuL0 T L)) = ⟨o * l * o⁻¹, hoL0⟩ * ⟨l, hl0⟩⁻¹ := rfl
    rw [e, map_mul, map_inv, hΨl, Prod.fst_mul, Prod.fst_inv, c.hC.onLt _ hoL0 hoLt, one_mul]
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (H ⊓ fsuM T L)) ⟨z, hzO⟩
  have hzk : (⟨z, hz0⟩ : ↥(fsuL0 T L)) ^ 2 ^ k = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val hk)
  have h2 : g⁻¹ ^ 2 ^ k = 1 := by
    rw [← hΨz, ← Prod.pow_fst, ← map_pow, hzk, map_one, Prod.fst_one]
  have hgo : orderOf g = 3 := orderOf_eq_prime hg3 hg1
  have h3 : 3 ∣ 2 ^ k := by
    rw [← hgo, ← orderOf_inv]
    exact orderOf_dvd_of_pow_eq_one h2
  exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)

theorem exists_swap (c : Ctx3 T L I H B t Ψ α ψ) (hB1 : B ≠ ⊥)
    (hTB : T ≤ pCoreOf 2 (H ⊓ fsuM T L) ⊔ (T ⊓ Subgroup.normalizer (B : Set G))) :
    ∃ x ∈ T, x ∈ Subgroup.normalizer (B : Set G) ∧ x ∉ Subgroup.normalizer (L : Set G) := by
  have hNO : T ⊓ Subgroup.normalizer (B : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 (H ⊓ fsuM T L) : Set G) := fun x hx =>
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (c.T_le hx.1)
  have ht := hTB c.ht
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hNO] at ht
  obtain ⟨o, ho, n, hn, hon⟩ := ht
  refine ⟨n, hn.1, hn.2, fun h => c.htn ?_⟩
  rw [← hon]
  exact Subgroup.mul_mem _ (c.pCoreOf_le_T1 hB1 ho).2 h

end Ctx3

end CFSG.Quasithin.Vol2.Ch10.SecB
