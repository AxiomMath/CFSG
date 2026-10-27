module

public import CFSG.Quasithin.Background.SmithB45ExcRuClass
public import CFSG.Quasithin.Background.SmithB45ExcRuCent
public import CFSG.Quasithin.Background.SmithB45ExcRuSyl
public import CFSG.Quasithin.Background.SmithB45ExcHSRuDisp

public section

namespace CFSG.Quasithin.B45Exc

open CFSG.Quasithin.B45Exc.Tab CFSG.Quasithin.B45Exc.HSRu CFSG.Quasithin.B45Exc.Ru
  CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family
  CFSG.QuasithinUnique.Bridge.RuExcl CFSG.Sporadic.RuSchreier CFSG.Blueprint

theorem Ru.card_ruS_eq :
    Nat.card ruS = 2 ^ (Nat.card ruP).factorization 2 := by
  rw [card_ruS, factorization_ruP]
  norm_num

theorem sporadicExclusion2F_Ru :
    SporadicExclusion2F .Ru := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hE hEne hEel
  have hcent : Subgroup.center ↥L = ⊥ :=
    center_eq_bot_of_cover hW hq.1 hirr e fun E _ _ _ π hπ hC hodd => ru_cover E π hπ hC hodd
  set ψ : Lift L E ruP ruP :=
    Lift.ofAut hW hq.1 hirr hE hEel e hcent le_rfl ruAutEquiv ruEquivC fun s => ruAutEquiv_apply s
  obtain ⟨l, hl, hlU⟩ := ψ.exists_conj_mem hEel ruS_le Ru.card_ruS_eq
    fun r hr => ⟨1, ruS.one_mem, r, hr, (one_mul r).symm⟩
  set E' : Subgroup (MulAut W) := E.map (MulAut.conj l).toMonoidHom with hE'
  have hlN : l ∈ Subgroup.normalizer (L : Set (MulAut W)) := Subgroup.le_normalizer hl
  have hE'N : E' ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem hlN (hE hx))
      ((Subgroup.normalizer _).inv_mem hlN)
  have hE'el : IsElemAbelian2 E' := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show l * x * l⁻¹ * (l * y * l⁻¹) = l * (x * y) * l⁻¹ by group, hEel.1 x hx y hy]
      group
    · rintro _ ⟨x, hx, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, conj_pow, hEel.2 x hx]
      group
  have hidx : (fixV E').index = (fixV E).index := index_fixV_map_conj E l
  have hcardE' : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj l).injective
  have hE'LE : ∀ x ∈ E', x ∈ L ⊔ E := by
    rintro _ ⟨x, hx, rfl⟩
    exact conj_mem_sup hl hx
  set B : Subgroup (Equiv.Perm (Fin 4060)) := (E'.subgroupOf (L ⊔ E)).map ψ.toG with hB
  have hBmem : ∀ y, y ∈ B ↔ ∃ x : ↥(L ⊔ E), (x : MulAut W) ∈ E' ∧ ψ.toG x = y := by
    intro y
    simp [hB, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  have hBS : B ≤ ruS := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (hBmem y).1 hy
    obtain ⟨z, hz, hzx⟩ := hx
    have : x = ⟨l * z * l⁻¹, conj_mem_sup hl hz⟩ := Subtype.ext hzx.symm
    rw [this]
    exact hlU z hz
  have hBP : ∀ x ∈ B, x ∈ ruP := fun x hx => ruS_le (hBS hx)
  have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := (hBmem x).1 hx
    obtain ⟨b, hb, rfl⟩ := (hBmem y).1 hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hE'el.1 _ ha _ hb)
  have hsq' : ∀ x : ↥(L ⊔ E), (x : MulAut W) ∈ E' → x * x = 1 := fun x hx =>
    Subtype.ext (by simpa [sq] using hE'el.2 _ hx)
  have hBsq : ∀ x ∈ B, x * x = 1 := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := (hBmem x).1 hx
    rw [← map_mul, hsq' a ha, map_one]
  have hBcard : Nat.card B = Nat.card E := by
    rw [hB, Subgroup.card_map_of_injective ψ.toG_injective, ← hcardE']
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'LE).toEquiv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpE : IsPGroup 2 E := by
    intro x
    exact ⟨1, Subtype.ext (by simpa [pow_one] using hEel.2 x x.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hpE
  have hBk : Nat.card B = 2 ^ k := hBcard.trans hk
  refine weight2_lt_of_lt_index E ?_
  rw [← hidx, hk, ← pow_mul]
  by_cases h2B : ∃ x ∈ B, x ≠ 1 ∧ (fixFinset x).card = 0
  ·
    obtain ⟨x, hxB, hx1, hx0⟩ := h2B
    rcases ru_inv_class (hBP x hxB) (hBsq x hxB) hx1 with ⟨-, h92⟩ | ⟨⟨g, hg, hxg⟩, -⟩
    · omega
    have hB5 := ru_card_le_of_2B B (fun y hy => hBP y hy) hBcomm hBsq hg (hxg ▸ hxB)
    rw [hBk] at hB5
    have hk5 : k ≤ 5 := (Nat.pow_le_pow_iff_right (by norm_num)).1 hB5
    obtain ⟨b, hbE', rfl⟩ := (hBmem x).1 hxB
    calc 2 ^ (k * 2) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ < 2 ^ 14 := by norm_num
      _ ≤ (fixV (Subgroup.zpowers (b : MulAut W))).index := ru_disp_2B hW ψ b hg hxg
      _ ≤ (fixV E').index := index_zpowers_le_index E' hbE'
  push Not at h2B
  have h2A : ∀ x ∈ B, x ≠ 1 → (fixFinset x).card = 92 := by
    intro x hx hx1
    rcases ru_inv_class (hBP x hx) (hBsq x hx) hx1 with ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    · exact absurd h (h2B x hx hx1)
  have hk6 : k ≤ 6 := by
    have := ru_syl_card_le B hBS hBcomm hBsq h2A
    rw [hBk] at this
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  by_cases hk4 : k ≤ 4
  ·
    have hne : E' ≠ ⊥ := by
      intro h
      apply hEne
      have h1 : Nat.card E' = 1 := by rw [h, Subgroup.card_bot]
      rw [hcardE'] at h1
      exact Subgroup.card_eq_one.1 h1
    obtain ⟨⟨b, hbE⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    calc 2 ^ (k * 2) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ < 2 ^ 9 := by norm_num
      _ < (fixV (Subgroup.zpowers b)).index :=
        ru_disp_all hW hq.1 hirr hE'N hE'el e hcent hbE fun h => hb1 (Subtype.ext h)
      _ ≤ (fixV E').index := index_zpowers_le_index E' hbE
  obtain ⟨x₁, hx₁, x₂, hx₂, x₃, hx₃, x₄, hx₄, G, hG, h29, h1⟩ :=
    ru_syl_dbl B hBS hBcomm hBsq h2A (by
      rw [hBk]
      rcases (show k = 5 ∨ k = 6 by omega) with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl)
  obtain ⟨e₁, he₁, rfl⟩ := (hBmem x₁).1 hx₁
  obtain ⟨e₂, he₂, rfl⟩ := (hBmem x₂).1 hx₂
  obtain ⟨e₃, he₃, rfl⟩ := (hBmem x₃).1 hx₃
  obtain ⟨e₄, he₄, rfl⟩ := (hBmem x₄).1 hx₄
  obtain ⟨g', -, hg'G⟩ := ψ.surj G hG
  have hg'G' : ψ.toG g' = G := hg'G
  set y : ↥(L ⊔ E) := e₁ * (g' * e₂ * g'⁻¹) * e₃ * (g' * e₄ * g'⁻¹) with hy
  have hyG : ψ.toG y =
      ψ.toG e₁ * (G * ψ.toG e₂ * G⁻¹) * ψ.toG e₃ * (G * ψ.toG e₄ * G⁻¹) := by
    rw [hy]
    simp only [map_mul, map_inv, hg'G']
  have hy29 : (y : MulAut W) ^ 29 = 1 := by
    have : y ^ 29 = 1 := ψ.toG_injective (by rw [map_pow, hyG, h29, map_one])
    rw [← Subgroup.coe_pow, this, Subgroup.coe_one]
  have hy1 : (y : MulAut W) ≠ 1 := by
    intro h
    apply h1
    rw [← hyG, show y = 1 from Subtype.ext h, map_one]
  have hymem : (y : MulAut W) ∈ E' ⊔ E'.map (MulAut.conj (g' : MulAut W)).toMonoidHom := by
    have hyW : (y : MulAut W) = (e₁ : MulAut W) * ((g' : MulAut W) * e₂ * (g' : MulAut W)⁻¹) *
        e₃ * ((g' : MulAut W) * e₄ * (g' : MulAut W)⁻¹) := by
      simp [hy]
    rw [hyW]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) ?_
    · exact Subgroup.mem_sup_left he₁
    · exact Subgroup.mem_sup_right (conj_mem_map_conj _ he₂)
    · exact Subgroup.mem_sup_left he₃
    · exact Subgroup.mem_sup_right (conj_mem_map_conj _ he₄)
  have h14 : 2 ^ 14 ≤ (fixV E').index := by
    have h := (two_pow_le_index_of_pow_29 hW hy29 hy1).trans (index_fixV_zpowers_le_sq hymem)
    rw [show (2 : ℕ) ^ 28 = (2 ^ 14) ^ 2 by norm_num] at h
    exact (Nat.pow_le_pow_iff_left (by norm_num)).1 h
  calc 2 ^ (k * 2) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ < 2 ^ 14 := by norm_num
    _ ≤ (fixV E').index := h14

end CFSG.Quasithin.B45Exc
