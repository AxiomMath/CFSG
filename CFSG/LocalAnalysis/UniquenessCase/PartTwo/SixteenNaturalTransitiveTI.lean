module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem exists_noncyclic_pSubgroup_fixing_of_quotient_transitive
    {M W : Type*} [Group M] [Finite M] [CommGroup W] [Finite W]
    {p : ℕ} (hp : p.Prime) (hpW : ¬ p ∣ Nat.card W)
    (φ : M →* MulAut W) (Z : Subgroup W)
    (hZ : ∀ (m : M) (z : W), z ∈ Z → φ m z ∈ Z)
    (E : Subgroup M) (hE : IsElemAbelian p E)
    (hEcard : Nat.card E = p ^ 3)
    (hEfix : ∀ e ∈ E, ∀ z ∈ Z, φ e z = z)
    (htr : ∀ x y : W, x ∉ Z → y ∉ Z →
      ∃ m : M, φ m x * y⁻¹ ∈ Z) :
    ∀ x : W, ∃ B : Subgroup M, IsPGroup p B ∧ ¬ IsCyclic ↥B ∧
      ∀ b ∈ B, φ b x = x := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hEea : IsElementaryAbelian p E := hE.isElementaryAbelian
  have hEpg : IsPGroup p E := hE.isPGroup
  have hE1 : 1 < Nat.card E := by
    rw [hEcard]
    calc 1 < 2 ^ 3 := by norm_num
      _ ≤ p ^ 3 := Nat.pow_le_pow_left hp.two_le 3
  have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp hE1
  have hEnc : ¬ IsCyclic ↥E := by
    intro hcyc
    have hdiv : p ^ 3 ∣ p := by
      rw [← hEcard, ← hcyc.exponent_eq_card]
      exact IsElementaryAbelian.exponent_dvd_p p ↥E
    have hle : p ^ 3 ≤ p := Nat.le_of_dvd hp.pos hdiv
    have hle' : p ^ 3 ≤ p ^ 1 := by simpa using hle
    have h31 : 3 ≤ 1 := (Nat.pow_le_pow_iff_right hp.one_lt).mp hle'
    omega
  let ρ : E →* MulAut W := φ.comp E.subtype
  let : MulDistribMulAction E W := MulDistribMulAction.compHom W ρ
  intro x
  by_cases hxZ : x ∈ Z
  · refine ⟨E, hEpg, hEnc, ?_⟩
    intro b hb
    exact hEfix b hb x hxZ
  · have hZne : Z ≠ ⊤ := fun h => hxZ (h ▸ Subgroup.mem_top x)
    have hgen : (⨆ (B : Subgroup E) (_ : B.index = p), fixedPointSubgroup B W) = ⊤ :=
      CFSG.SolvableHall.abelian_hyperplane_generation (p := p) (A := E) (H := W) hpW
    have hex : ∃ B : Subgroup E, B.index = p ∧ ¬ fixedPointSubgroup B W ≤ Z := by
      by_contra h
      push Not at h
      have hle : (⨆ (B : Subgroup E) (_ : B.index = p), fixedPointSubgroup B W) ≤ Z :=
        iSup_le fun B => iSup_le fun hB => h B hB
      rw [hgen] at hle
      exact hZne (top_le_iff.mp hle)
    obtain ⟨B, hBindex, hBnotle⟩ := hex
    obtain ⟨w, hwmem, hwZ⟩ := Set.not_subset.mp hBnotle
    have hEtop : IsElemAbelian p (⊤ : Subgroup E) := by
      simpa using hE.subgroupOf E
    have hBea : IsElemAbelian p B := hEtop.mono (le_top : B ≤ ⊤)
    have hBcard : Nat.card B = p ^ 2 := by
      have h1 : Nat.card E = Nat.card (E ⧸ B) * Nat.card B :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup B
      rw [hEcard, ← Subgroup.index_eq_card, hBindex] at h1
      have h2 : p * p ^ 2 = p * Nat.card B := by rw [← h1]; ring
      exact (Nat.mul_left_cancel hp.pos h2).symm
    have hBp : IsPGroup p B := hBea.isPGroup
    have hBea' : IsElementaryAbelian p B := hBea.isElementaryAbelian
    have hBnc : ¬ IsCyclic ↥B :=
      IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hBcard
    have hwfix : ∀ b : B, b • w = w :=
      (FixedPoints.mem_subgroup (M := B) (α := W) w).1 hwmem
    obtain ⟨m, hm⟩ := htr w x hwZ hxZ
    let y : W := φ m w
    let z : W := y * x⁻¹
    have hzZ : z ∈ Z := hm
    let g : E →* M := (MulAut.conj m).toMonoidHom.comp E.subtype
    have hg : Function.Injective g :=
      (MulAut.conj m).injective.comp E.subtype_injective
    let Bx : Subgroup M := B.map g
    have hBxcard : Nat.card Bx = p ^ 2 := by
      change Nat.card (B.map g) = p ^ 2
      rw [Subgroup.card_map_of_injective hg, hBcard]
    have hBxp : IsPGroup p Bx := hBp.map g
    have hBxnc : ¬ IsCyclic ↥Bx := by
      intro hcyc
      have := hcyc
      have eB : ↥B ≃* ↥Bx := Subgroup.equivMapOfInjective B g hg
      exact hBnc (isCyclic_of_surjective eB.symm.toMonoidHom eB.symm.surjective)
    refine ⟨Bx, hBxp, hBxnc, ?_⟩
    intro b hb
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.1 hb
    have hgapply : g b₀ = m * (b₀ : M) * m⁻¹ := by
      simp [g, MulAut.conj_apply]
    have hφg : φ (g b₀) = φ m * φ (b₀ : M) * (φ m)⁻¹ := by
      rw [hgapply, map_mul, map_mul, map_inv]
    have hbw : φ (b₀ : M) w = w := by
      have h := hwfix ⟨b₀, hb₀⟩
      rw [Subgroup.smul_def] at h
      change ρ b₀ w = w at h
      change φ (b₀ : M) w = w
      exact h
    have hyfix : φ (g b₀) y = y := by
      rw [hφg]
      simp only [MulAut.mul_apply]
      rw [MulAut.inv_apply_self, hbw]
    have hfixZ : ∀ z' ∈ Z, φ (g b₀) z' = z' := by
      intro z' hz'
      rw [hφg]
      simp only [MulAut.mul_apply]
      have hz'' : (φ m)⁻¹ z' ∈ Z := by
        have h := hZ (m⁻¹) z' hz'
        rwa [map_inv] at h
      have hfixe : φ (b₀ : M) ((φ m)⁻¹ z') = (φ m)⁻¹ z' :=
        hEfix (b₀ : M) b₀.property ((φ m)⁻¹ z') hz''
      change φ m (φ (b₀ : M) ((φ m)⁻¹ z')) = z'
      rw [hfixe, MulAut.apply_inv_self]
    have hzfix : φ (g b₀) z = z := hfixZ z hzZ
    have hxz : x = z⁻¹ * y := by
      change x = (y * x⁻¹)⁻¹ * y
      group
    rw [hxz, map_mul, map_inv, hzfix, hyfix]

theorem s168e3_false_of_transitive
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (htr : ∀ x y : Vtil V₀ V hV, x ≠ 1 → y ≠ 1 →
      ∃ a ∈ Mbar D.M V₀ V hV, a x = y) : False := by
  classical
  obtain ⟨p, hpσ⟩ := c.std.hx.sig_nonempty
  have hp : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hEM, hEel, hEcard⟩ :=
    c23_exists_elemAbelian_card_pow (p := p) (M := D.M) (k := 3) hp (by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top p ↥D.M,
        ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) D.M,
        c.std.pRank_eq_three hpσ])
  let W := Vtil V₀ V hV
  let φ : ↥D.M →* MulAut W := barHom V₀ V hV c.m_le_stabTil
  have hW2 : ∀ w : W, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hpW : ¬ p ∣ Nat.card W := by
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hx2 : x ^ 2 = 1 := hW2 x
    have hp2dvd : p ∣ 2 := hx ▸ orderOf_dvd_iff_pow_eq_one.mpr hx2
    rcases (Nat.dvd_prime Nat.prime_two).mp hp2dvd with h | h
    · exact hp.ne_one h
    · exact hp2 h
  have hZ : ∀ (m : ↥D.M) (z : W), z ∈ (⊥ : Subgroup W) → φ m z ∈ (⊥ : Subgroup W) := by
    intro m z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  have hEfix : ∀ e ∈ (E.subgroupOf D.M), ∀ z ∈ (⊥ : Subgroup W), φ e z = z := by
    intro e he z hz
    rw [Subgroup.mem_bot] at hz
    rw [hz, map_one]
  have htr' : ∀ x y : W, x ∉ (⊥ : Subgroup W) → y ∉ (⊥ : Subgroup W) →
      ∃ m : ↥D.M, φ m x * y⁻¹ ∈ (⊥ : Subgroup W) := by
    intro x y hx hy
    have hx1 : x ≠ 1 := by simpa using hx
    have hy1 : y ≠ 1 := by simpa using hy
    obtain ⟨a, haM, haw⟩ := htr x y hx1 hy1
    have ha : a ∈ φ.range := by
      change a ∈ (barHom V₀ V hV c.m_le_stabTil).range
      rw [range_barHom]
      exact haM
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.1 ha
    refine ⟨m, ?_⟩
    rw [Subgroup.mem_bot, hm, haw, mul_inv_cancel]
  have hE'el : IsElemAbelian p (E.subgroupOf D.M) := hEel.subgroupOf D.M
  have hE'card : Nat.card (E.subgroupOf D.M) = p ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv, hEcard]
  have hfixM : ∀ x : W, x ≠ 1 → ∃ B : Subgroup ↥D.M, IsPGroup p B ∧ ¬ IsCyclic ↥B ∧
      ∀ b ∈ B, φ b x = x := by
    intro x hx
    exact exists_noncyclic_pSubgroup_fixing_of_quotient_transitive
      (M := ↥D.M) (W := W) hp hpW φ ⊥ hZ (E.subgroupOf D.M) hE'el hE'card hEfix htr' x
  exact s168e3_false_of_fix_M c hp hpσ hfixM
end CFSG.LocalAnalysis.UniquenessCase.PartTwo
