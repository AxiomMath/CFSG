module

public import CFSG.Quasithin.Vol2.Ch10SecB3Wr2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem exists_gen_of_card_three {P : Subgroup L32.Γ} (h : Nat.card P = 3) :
    ∃ g ∈ P, g ^ 3 = 1 ∧ g ≠ 1 ∧ P = Subgroup.zpowers g := by
  have hP1 : P ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at h
    omega
  obtain ⟨⟨g, hg⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP1
  have hg1' : g ≠ 1 := fun h' => hg1 (Subtype.ext h')
  have hg3 : g ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥P) (x := ⟨g, hg⟩)
    rw [h] at this
    simpa using congrArg Subtype.val this
  refine ⟨g, hg, hg3, hg1', ?_⟩
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hg) ?_).symm
  rw [h, Nat.card_zpowers, orderOf_eq_prime hg3 hg1']

theorem conj_mem_zpowers {g u a : L32.Γ} (hu : u * g * u⁻¹ = g⁻¹) (ha : a ∈ Subgroup.zpowers g) :
    u * a * u⁻¹ ∈ Subgroup.zpowers g := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  rw [← conj_zpow, hu]
  exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers g)) k

theorem ne_inv_of_three {g : L32.Γ} (h3 : g ^ 3 = 1) (h1 : g ≠ 1) : g ≠ g⁻¹ := by
  intro h
  apply h1
  have h2 : g * g = 1 := by
    calc g * g = g * g⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel g
  calc g = g ^ 3 * (g * g)⁻¹ := by rw [pow_succ, pow_two]; group
    _ = 1 := by rw [h3, h2]; group

namespace Ctx3

variable {H B : Subgroup G} {t : G} {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ} {α : MulAut L32.Γ}
  {ψ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* L32.Γ}

theorem Ψ_conjAct (c : Ctx3 T L I H B t Ψ α ψ) {x : G}
    (hxN : x ∈ Subgroup.normalizer (B : Set G)) (hx0 : x ∈ fsuL0 T L) (b : ↥B)
    (h : ((conjAct B ⟨x, hxN⟩ b : ↥B) : G) ∈ fsuL0 T L) :
    Ψ ⟨_, h⟩ = Ψ ⟨x, hx0⟩ * Ψ ⟨b, c.le_fsuL0 b.2⟩ * (Ψ ⟨x, hx0⟩)⁻¹ := by
  have e : (⟨_, h⟩ : ↥(fsuL0 T L)) = ⟨x, hx0⟩ * ⟨b, c.le_fsuL0 b.2⟩ * ⟨x, hx0⟩⁻¹ :=
    Subtype.ext (conjAct_apply_coe B ⟨x, hxN⟩ b)
  rw [e, map_mul, map_mul, map_inv]

theorem fst_conjAct_eq_one (c : Ctx3 T L I H B t Ψ α ψ) {x : G} (hxT : x ∈ T)
    (hxN : x ∈ Subgroup.normalizer (B : Set G)) (hxn : x ∉ Subgroup.normalizer (L : Set G))
    (b : ↥B) (hb : (Ψ ⟨b, c.le_fsuL0 b.2⟩).2 = 1)
    (h : ((conjAct B ⟨x, hxN⟩ b : ↥B) : G) ∈ fsuL0 T L) : (Ψ ⟨_, h⟩).1 = 1 := by
  have hxM : x ∈ fsuM T L := SecA.le_fsuM T L hxT
  obtain ⟨⟨l, hl⟩, hq⟩ := QuotientGroup.mk_surjective (ψ.symm (Ψ ⟨b, c.le_fsuL0 b.2⟩).1)
  have hl0 : l ∈ fsuL0 T L := SecA.le_fsuL0 T L hl
  have hΨl : Ψ ⟨l, hl0⟩ = Ψ ⟨b, c.le_fsuL0 b.2⟩ := by
    rw [c.hC.onL l hl0 hl, mkO2, hq, MulEquiv.apply_symm_apply]
    exact Prod.ext rfl hb.symm
  set k := l⁻¹ * b with hk
  have hk0 : k ∈ fsuL0 T L := (fsuL0 T L).mul_mem ((fsuL0 T L).inv_mem hl0) (c.le_fsuL0 b.2)
  have hkO : k ∈ pCoreOf 2 (fsuL0 T L) := by
    apply (c.hC.ker ⟨k, hk0⟩).mp
    have e : (⟨k, hk0⟩ : ↥(fsuL0 T L)) = ⟨l, hl0⟩⁻¹ * ⟨b, c.le_fsuL0 b.2⟩ := rfl
    rw [e, map_mul, map_inv, hΨl, inv_mul_cancel]
  have hxLt : x * l * x⁻¹ ∈ CFSG.conjugate L t := by
    have hxn' : x⁻¹ ∉ Subgroup.normalizer (L : Set G) := fun h' =>
      hxn (by simpa using (Subgroup.normalizer _).inv_mem h')
    rw [← SecA.conjugate_eq_of_not_mem c.h37 c.h38 c.hyp c.ht c.htn (T.inv_mem hxT) hxn',
      SecA.mem_conjugate_iff]
    simpa [mul_assoc] using hl
  have hxk : x * k * x⁻¹ ∈ pCoreOf 2 (fsuL0 T L) :=
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hxM) k).mp hkO
  have h1 : x * l * x⁻¹ ∈ fsuL0 T L := SecA.conjugate_le_fsuL0 c.ht hxLt
  have h2 : x * k * x⁻¹ ∈ fsuL0 T L := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hxk
  have e : (⟨_, h⟩ : ↥(fsuL0 T L)) = ⟨x * l * x⁻¹, h1⟩ * ⟨x * k * x⁻¹, h2⟩ := by
    apply Subtype.ext
    rw [conjAct_apply_coe]
    show x * (b : G) * x⁻¹ = x * l * x⁻¹ * (x * (l⁻¹ * b) * x⁻¹)
    group
  rw [e, map_mul, (c.hC.ker ⟨x * k * x⁻¹, h2⟩).mpr hxk, mul_one, c.hC.onLt _ h1 hxLt]

theorem eight_le (c : Ctx3 T L I H B t Ψ α ψ) (hB1 : B ≠ ⊥)
    (hTB : T ≤ pCoreOf 2 (H ⊓ fsuM T L) ⊔ (T ⊓ Subgroup.normalizer (B : Set G))) :
    8 ≤ Nat.card (autOn T B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hA, -, -, P₁, P₂, himg, hc₁, hc₂, hP₁, hP₂⟩ := c.img_eq_prod hB1
  obtain ⟨g₁, hg₁, hg₁3, hg₁1, hP₁g⟩ := exists_gen_of_card_three hc₁
  obtain ⟨g₂, hg₂, hg₂3, hg₂1, hP₂g⟩ := exists_gen_of_card_three hc₂
  have hinv : ∀ g ∈ A, g ^ 3 = 1 → g ≠ 1 → ∃ u, L32.IsU u ∧ u * g * u⁻¹ = g⁻¹ := by
    intro g hg h3 h1
    rcases hA with rfl | rfl
    · exact L32.pa_inv_three g hg h3 h1
    · exact L32.pb_inv_three g hg h3 h1
  obtain ⟨u₁, hu₁, hu₁g⟩ := hinv g₁ (hP₁ hg₁) hg₁3 hg₁1
  obtain ⟨u₂, hu₂, hu₂g⟩ := hinv g₂ (hP₂ hg₂) hg₂3 hg₂1
  have hU1 : L32.IsU (1 : L32.Γ) := L32.U3.one_mem
  obtain ⟨x₁, hx₁0, hx₁T0, hx₁N, hΨx₁⟩ := c.exists_normalizer hB1 hu₁ hU1 (by
    rintro ⟨a, b⟩ hab
    rw [himg] at hab ⊢
    obtain ⟨ha, hb⟩ := hab
    exact ⟨by simpa using hP₁g ▸ conj_mem_zpowers hu₁g (hP₁g ▸ ha), by simpa using hb⟩)
  obtain ⟨x₂, hx₂0, hx₂T0, hx₂N, hΨx₂⟩ := c.exists_normalizer hB1 hU1 hu₂ (by
    rintro ⟨a, b⟩ hab
    rw [himg] at hab ⊢
    obtain ⟨ha, hb⟩ := hab
    exact ⟨by simpa using ha, by simpa using hP₂g ▸ conj_mem_zpowers hu₂g (hP₂g ▸ hb)⟩)
  obtain ⟨x₃, hx₃T, hx₃N, hx₃n⟩ := c.exists_swap hB1 hTB
  obtain ⟨b₁, hb₁0, hb₁B, hΨb₁⟩ := mem_imgIn.mp
    (show (g₁, (1 : L32.Γ)) ∈ imgIn Ψ B from himg ▸ ⟨hg₁, P₂.one_mem⟩)
  obtain ⟨b₂, hb₂0, hb₂B, hΨb₂⟩ := mem_imgIn.mp
    (show ((1 : L32.Γ), g₂) ∈ imgIn Ψ B from himg ▸ ⟨P₁.one_mem, hg₂⟩)
  have hT0T : T0 T L ≤ T := inf_le_left
  set σ₁ : MulAut ↥B := conjAct B ⟨x₁, hx₁N⟩ with hσ₁
  set σ₂ : MulAut ↥B := conjAct B ⟨x₂, hx₂N⟩ with hσ₂
  set σ₃ : MulAut ↥B := conjAct B ⟨x₃, hx₃N⟩ with hσ₃
  have hm₁ : σ₁ ∈ autOn T B := SecB.mem_autOn_iff.mpr ⟨⟨x₁, hx₁N⟩, hT0T hx₁T0, rfl⟩
  have hm₂ : σ₂ ∈ autOn T B := SecB.mem_autOn_iff.mpr ⟨⟨x₂, hx₂N⟩, hT0T hx₂T0, rfl⟩
  have hm₃ : σ₃ ∈ autOn T B := SecB.mem_autOn_iff.mpr ⟨⟨x₃, hx₃N⟩, hx₃T, rfl⟩
  let ι₁ : MulAut ↥B → L32.Γ := fun φ =>
    (Ψ ⟨((φ ⟨b₁, hb₁B⟩ : ↥B) : G), c.le_fsuL0 (φ ⟨b₁, hb₁B⟩).2⟩).1
  let ι₂ : MulAut ↥B → L32.Γ := fun φ =>
    (Ψ ⟨((φ ⟨b₂, hb₂B⟩ : ↥B) : G), c.le_fsuL0 (φ ⟨b₂, hb₂B⟩).2⟩).2
  have hb₁ : Ψ ⟨((⟨b₁, hb₁B⟩ : ↥B) : G), c.le_fsuL0 hb₁B⟩ = (g₁, 1) := hΨb₁
  have hb₂ : Ψ ⟨((⟨b₂, hb₂B⟩ : ↥B) : G), c.le_fsuL0 hb₂B⟩ = (1, g₂) := hΨb₂
  have hs₁ : ∀ b : ↥B, Ψ ⟨((σ₁ b : ↥B) : G), c.le_fsuL0 (σ₁ b).2⟩ =
      (u₁, 1) * Ψ ⟨b, c.le_fsuL0 b.2⟩ * (u₁, 1)⁻¹ := fun b => by
    rw [c.Ψ_conjAct hx₁N hx₁0 b, hΨx₁]
  have hs₂ : ∀ b : ↥B, Ψ ⟨((σ₂ b : ↥B) : G), c.le_fsuL0 (σ₂ b).2⟩ =
      (1, u₂) * Ψ ⟨b, c.le_fsuL0 b.2⟩ * (1, u₂)⁻¹ := fun b => by
    rw [c.Ψ_conjAct hx₂N hx₂0 b, hΨx₂]
  have v₀₁ : ι₁ 1 = g₁ := by simp only [ι₁, MulAut.one_apply, hb₁]
  have v₀₂ : ι₂ 1 = g₂ := by simp only [ι₂, MulAut.one_apply, hb₂]
  have v₁₁ : ι₁ σ₁ = g₁⁻¹ := by
    simp only [ι₁]
    rw [hs₁, hb₁]
    simp [hu₁g]
  have v₁₂ : ι₂ σ₁ = g₂ := by
    simp only [ι₂]
    rw [hs₁, hb₂]
    simp
  have v₂₁ : ι₁ σ₂ = g₁ := by
    simp only [ι₁]
    rw [hs₂, hb₁]
    simp
  have v₂₂ : ι₂ σ₂ = g₂⁻¹ := by
    simp only [ι₂]
    rw [hs₂, hb₂]
    simp [hu₂g]
  have v₃₁ : ι₁ (σ₁ * σ₂) = g₁⁻¹ := by
    simp only [ι₁, MulAut.mul_apply]
    rw [hs₁, hs₂, hb₁]
    simp [hu₁g]
  have v₃₂ : ι₂ (σ₁ * σ₂) = g₂⁻¹ := by
    simp only [ι₂, MulAut.mul_apply]
    rw [hs₁, hs₂, hb₂]
    simp [hu₂g]
  have v₄₁ : ι₁ σ₃ = 1 :=
    c.fst_conjAct_eq_one hx₃T hx₃N hx₃n ⟨b₁, hb₁B⟩ (by rw [hb₁]) _
  have hn₁ := ne_inv_of_three hg₁3 hg₁1
  have hn₂ := ne_inv_of_three hg₂3 hg₂1
  have hn₃ : g₁⁻¹ ≠ 1 := inv_ne_one.mpr hg₁1
  set E₀ : ↥(autOn T B) := 1
  set E₁ : ↥(autOn T B) := ⟨σ₁, hm₁⟩
  set E₂ : ↥(autOn T B) := ⟨σ₂, hm₂⟩
  set E₃ : ↥(autOn T B) := ⟨σ₁ * σ₂, mul_mem hm₁ hm₂⟩
  set E₄ : ↥(autOn T B) := ⟨σ₃, hm₃⟩
  have k₁ : ∀ {E E' : ↥(autOn T B)}, E = E' → ι₁ E = ι₁ E' := fun h => by rw [h]
  have k₂ : ∀ {E E' : ↥(autOn T B)}, E = E' → ι₂ E = ι₂ E' := fun h => by rw [h]
  have d01 : E₀ ≠ E₁ := fun h => hn₁ (by have := k₁ h; rwa [Subgroup.coe_one, v₀₁, v₁₁] at this)
  have d02 : E₀ ≠ E₂ := fun h => hn₂ (by have := k₂ h; rwa [Subgroup.coe_one, v₀₂, v₂₂] at this)
  have d03 : E₀ ≠ E₃ := fun h => hn₁ (by have := k₁ h; rwa [Subgroup.coe_one, v₀₁, v₃₁] at this)
  have d04 : E₀ ≠ E₄ := fun h => hg₁1 (by have := k₁ h; rwa [Subgroup.coe_one, v₀₁, v₄₁] at this)
  have d12 : E₁ ≠ E₂ := fun h => hn₁ (by have := k₁ h; exact (v₁₁.symm.trans (this.trans v₂₁)).symm)
  have d13 : E₁ ≠ E₃ := fun h => hn₂ (by have := k₂ h; exact v₁₂.symm.trans (this.trans v₃₂))
  have d14 : E₁ ≠ E₄ := fun h => hn₃ (by have := k₁ h; exact v₁₁.symm.trans (this.trans v₄₁))
  have d23 : E₂ ≠ E₃ := fun h => hn₁ (by have := k₁ h; exact v₂₁.symm.trans (this.trans v₃₁))
  have d24 : E₂ ≠ E₄ := fun h => hg₁1 (by have := k₁ h; exact v₂₁.symm.trans (this.trans v₄₁))
  have d34 : E₃ ≠ E₄ := fun h => hn₃ (by have := k₁ h; exact v₃₁.symm.trans (this.trans v₄₁))
  classical
  let := Fintype.ofFinite ↥(autOn T B)
  have h5 : 5 ≤ Nat.card (autOn T B) := by
    have hS : ({E₀, E₁, E₂, E₃, E₄} : Finset ↥(autOn T B)).card = 5 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_pair_eq_two_iff.mpr d34]
      · simp [d23, d24]
      · simp [d12, d13, d14]
      · simp [d01, d02, d03, d04]
    rw [Nat.card_eq_fintype_card, ← hS]
    exact Finset.card_le_univ _
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp
    (isPGroup_autOn (U := B) (c.hyp.fsu.sylow.1 : IsPGroup 2 T))
  rw [he] at h5 ⊢
  rcases e with _ | _ | _ | e
  · norm_num at h5
  · norm_num at h5
  · norm_num at h5
  · calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (e + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)

end Ctx3

end CFSG.Quasithin.Vol2.Ch10.SecB
