module

public import CFSG.RankThree.PartOne.SRC.RankOneNoncentral

public section

namespace CFSG.RankThree.PartOne.SLB4B

open Subgroup CFSG CFSG.RankThree.PartOne.SRC

theorem exists_central_cover_of_rank_le_three {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Q : Type}
    [Group Q] [Finite Q] (hQ : CFSG.IsQuasisimple Q) (hZ : Nat.Coprime p (Nat.card (center Q)))
    (h : Q) (hhc : h ∉ center Q) (hho : Nat.Coprime (orderOf h) p) (hQp : p ^ 4 ∣ Nat.card Q)
    {W : Type} [Group W] [Finite W] (ρ : W →* Q) (hρ : Function.Surjective ρ)
    (hker : IsPGroup p ρ.ker)
    (hrank : ∀ E : Subgroup W, IsElementaryAbelian p E → Nat.card E ≤ p ^ 3) :
    ∃ W₀ : Subgroup W, Function.Surjective (ρ.comp W₀.subtype) ∧
      (ρ.comp W₀.subtype).ker ≤ center W₀ ∧ IsPGroup p (ρ.comp W₀.subtype).ker := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨W₀, -, hW₀min⟩ := Finite.exists_le_minimal (p := fun K : Subgroup W => K.map ρ = ⊤)
    (a := ⊤) (by rw [Subgroup.map_top_of_surjective ρ hρ])
  set ρ₀ : W₀ →* Q := ρ.comp W₀.subtype with hρ₀
  have hρ₀s : Function.Surjective ρ₀ := by
    intro x
    have hx : x ∈ W₀.map ρ := by
      rw [hW₀min.prop]
      exact mem_top x
    obtain ⟨k, hk, rfl⟩ := hx
    exact ⟨⟨k, hk⟩, rfl⟩
  have hmin₀ : ∀ M : Subgroup W₀, M.map ρ₀ = ⊤ → M = ⊤ := by
    intro M hM
    have h1 : (M.map W₀.subtype).map ρ = ⊤ := by
      rw [Subgroup.map_map]
      exact hM
    have h2 := hW₀min.le_of_le h1 (Subgroup.map_subtype_le M)
    rw [eq_top_iff]
    intro y _
    obtain ⟨y', hy', hyy⟩ := h2 y.2
    rwa [show y' = y from Subtype.ext hyy] at hy'
  have hker₀ : IsPGroup p ρ₀.ker := by
    intro x
    have hx1 : ρ ((x : W₀) : W) = 1 := MonoidHom.mem_ker.mp x.2
    obtain ⟨k, hk⟩ := hker ⟨((x : W₀) : W), hx1⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg (fun z : ρ.ker => (z : W)) hk))⟩
  have hperf : Group.IsPerfect W₀ := by
    rw [Group.isPerfect_def]
    apply hmin₀
    have h1 := hQ.1.commutator_eq_top
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ hρ₀s]
    rwa [_root_.commutator_def] at h1
  have hrank₀ : ∀ E : Subgroup W₀, IsElementaryAbelian p E → Nat.card E ≤ p ^ 3 := by
    intro E hE
    have := hrank _ (isElementaryAbelian_map' W₀.subtype hE)
    rwa [Subgroup.card_map_of_injective W₀.subtype_injective] at this
  exact ⟨W₀, hρ₀s,
    central_of_rank_le_three hp hp2 le_rfl hQ ρ₀ hρ₀s hker₀ hmin₀ hQp hZ h hhc hho hrank₀, hker₀⟩

theorem exists_section_of_rank_le_three {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Q : Type} [Group Q]
    [Finite Q] (hQ : CFSG.IsQuasisimple Q) (hZ : Nat.Coprime p (Nat.card (center Q))) (h : Q)
    (hhc : h ∉ center Q) (hho : Nat.Coprime (orderOf h) p) (hQp : p ^ 4 ∣ Nat.card Q)
    (hclosed : ∀ (W : Type) [Group W] [Finite W] (π : W →* Q), Function.Surjective π →
      π.ker ≤ center W → IsPGroup p π.ker → ∃ s : Q →* W, ∀ g, π (s g) = g)
    {W : Type} [Group W] [Finite W] (ρ : W →* Q) (hρ : Function.Surjective ρ)
    (hker : IsPGroup p ρ.ker)
    (hrank : ∀ E : Subgroup W, IsElementaryAbelian p E → Nat.card E ≤ p ^ 3) :
    ∃ σ : Q →* W, ∀ g, ρ (σ g) = g := by
  obtain ⟨W₀, hs, hcen, hker₀⟩ :=
    exists_central_cover_of_rank_le_three hp2 hQ hZ h hhc hho hQp ρ hρ hker hrank
  obtain ⟨σ, hσ⟩ := hclosed W₀ (ρ.comp W₀.subtype) hs hcen hker₀
  exact ⟨W₀.subtype.comp σ, hσ⟩

theorem card_le_pow_three_of_not_rank_four {p : ℕ} [Fact p.Prime] {W : Type} [Group W] [Finite W]
    (hno : ¬ ∃ (E : Subgroup W) (k : ℕ), 4 ≤ k ∧ IsElementaryAbelian p E ∧
      Nat.card E = p ^ k) :
    ∀ E : Subgroup W, IsElementaryAbelian p E → Nat.card E ≤ p ^ 3 := by
  intro E hE
  have hp : p.Prime := Fact.out
  have hEp : IsPGroup p E := IsElementaryAbelian.isPGroup p E
  obtain ⟨k', hk'⟩ := hEp.exists_card_eq
  rw [hk']
  by_contra hlt
  have hk4 : 4 ≤ k' := by
    by_contra h4
    push Not at h4
    exact hlt (Nat.pow_le_pow_right hp.pos (by omega))
  exact hno ⟨E, k', hk4, hE, hk'⟩

section Omega

variable {G : Type} [Group G]

@[expose] def omegaOneCenter (p : ℕ) (X : Subgroup G) : Subgroup G where
  carrier := {z | z ∈ X ∧ z ∈ Subgroup.centralizer (X : Set G) ∧ z ^ p = 1}
  mul_mem' := by
    rintro a b ⟨haX, haC, hap⟩ ⟨hbX, hbC, hbp⟩
    refine ⟨X.mul_mem haX hbX, Subgroup.mul_mem _ haC hbC, ?_⟩
    have hcomm : Commute a b := (Subgroup.mem_centralizer_iff.mp hbC) a haX
    rw [hcomm.mul_pow, hap, hbp, one_mul]
  one_mem' := ⟨X.one_mem, Subgroup.one_mem _, one_pow p⟩
  inv_mem' := by
    rintro a ⟨haX, haC, hap⟩
    exact ⟨X.inv_mem haX, Subgroup.inv_mem _ haC, by rw [inv_pow, hap, inv_one]⟩

theorem omegaOneCenter_le (p : ℕ) (X : Subgroup G) : omegaOneCenter p X ≤ X :=
  fun _ h => h.1

theorem isElementaryAbelian_omegaOneCenter (p : ℕ) (X : Subgroup G) :
    IsElementaryAbelian p (omegaOneCenter p X) := by
  refine { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext ?_⟩⟩, exponent_dvd_p := ?_ }
  · exact Subgroup.mem_centralizer_iff.mp b.2.2.1 a a.2.1
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => Subtype.ext ?_
    exact x.2.2.2

theorem omegaOneCenter_ne_bot [Finite G] {p : ℕ} [Fact p.Prime] {X : Subgroup G}
    (hX : IsPGroup p X) (hX1 : X ≠ ⊥) : omegaOneCenter p X ≠ ⊥ := by
  have : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).mpr hX1
  have hZ : Nontrivial (Subgroup.center X) := hX.center_nontrivial
  have hdvd : p ∣ Nat.card (Subgroup.center X) := by
    obtain ⟨k, hk⟩ := (hX.to_subgroup (Subgroup.center X)).exists_card_eq
    have h1 : 1 < Nat.card (Subgroup.center X) := Finite.one_lt_card_iff_nontrivial.mpr hZ
    rw [hk] at h1 ⊢
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at h1
      exact lt_irrefl 1 h1
    exact dvd_pow_self p hk0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center X) p hdvd
  intro h
  have hmem : (((z : Subgroup.center X) : X) : G) ∈ omegaOneCenter p X := by
    refine ⟨(z : X).2, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩)
    · have h1 := pow_orderOf_eq_one z
      rw [hz] at h1
      have h2 := congrArg (fun w : Subgroup.center X => ((w : X) : G)) h1
      simpa using h2
  rw [h, Subgroup.mem_bot] at hmem
  have hz1 : z = 1 := Subtype.ext (Subtype.ext hmem)
  rw [hz1, orderOf_one] at hz
  exact (Fact.out : p.Prime).one_lt.ne hz

theorem normal_omegaOneCenter (p : ℕ) (X : Subgroup G) [X.Normal] :
    (omegaOneCenter p X).Normal := by
  refine ⟨fun z hz g => ?_⟩
  obtain ⟨hzX, hzC, hzp⟩ := hz
  refine ⟨(inferInstance : X.Normal).conj_mem z hzX g, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff] at hzC ⊢
    intro y hy
    have hy' : g⁻¹ * y * g ∈ X := by
      have := (inferInstance : X.Normal).conj_mem y hy g⁻¹
      simpa using this
    have := hzC _ hy'
    calc y * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
      _ = g * z * g⁻¹ * y := by group
  · rw [conj_pow, hzp, mul_one, mul_inv_cancel]

end Omega

theorem exists_rank_four_of_section_ker {p : ℕ} [Fact p.Prime] {Q : Type}
    [Group Q] [Finite Q] (hQ : CFSG.IsQuasisimple Q)
    (hZ : Nat.Coprime p (Nat.card (center Q))) (hQp : p ^ 4 ∣ Nat.card Q)
    {E₀ : Subgroup Q} (hE₀ : IsElementaryAbelian p E₀) (hcard : Nat.card E₀ = p ^ 3)
    {W : Type} [Group W] [Finite W] (π : W →* Q)
    (hker : IsPGroup p π.ker) (hker1 : π.ker ≠ ⊥)
    (hrank : ∀ E : Subgroup W, IsElementaryAbelian p E → Nat.card E ≤ p ^ 3)
    (σ : Q →* W) (hσ : ∀ g, π (σ g) = g) :
    ∃ (E : Subgroup W) (k : ℕ), 4 ≤ k ∧ IsElementaryAbelian p E ∧ Nat.card E = p ^ k := by
  classical
  have hp : p.Prime := Fact.out
  have hσinj : Function.Injective σ := fun a b hab => by
    have := congrArg π hab
    rwa [hσ, hσ] at this
  have hkn : π.ker.Normal := inferInstance
  set A : Subgroup W := omegaOneCenter p π.ker with hAdef
  have hAne : A ≠ ⊥ := omegaOneCenter_ne_bot hker hker1
  have hAel : IsElementaryAbelian p A := isElementaryAbelian_omegaOneCenter p π.ker
  have hAn : A.Normal := normal_omegaOneCenter p π.ker
  have hAker : A ≤ π.ker := omegaOneCenter_le p π.ker
  have hcentr : ∀ (g : Q) (x : W), x ∈ A → σ g * x * (σ g)⁻¹ = x := by
    let ψ : Q →* MulAut ↥A := (MulAut.conjNormal (H := A)).comp σ
    have hψ : ψ.ker = ⊤ := by
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ (inferInstance : ψ.ker.Normal) with
        htop | hle
      · exact htop
      · exfalso
        have hAp : IsPGroup p A := IsElementaryAbelian.isPGroup p A
        obtain ⟨a, ha⟩ := hAp.exists_card_eq
        have ha3 : a ≤ 3 := by
          have := hrank A hAel
          rw [ha] at this
          exact (Nat.pow_le_pow_iff_right hp.one_lt).mp this
        have hcomm : ∀ x y : ↥A, x * y = y * x := fun x y =>
          (IsMulCommutative.is_comm (M := A)).comm x y
        have hpow : ∀ x : ↥A, x ^ p = 1 := fun x =>
          Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (x : W) x.2)
        obtain ⟨ecoord⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := p) hcomm
          hpow ha
        have h4 := CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL ecoord
        have hN : Nat.card ψ.ker ∣ Nat.card (center Q) := Subgroup.card_dvd_of_le hle
        have hQN := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
        have h2 : Nat.card (Q ⧸ ψ.ker) ∣ Nat.card (MulAut ↥A) := by
          rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
          exact Subgroup.card_subgroup_dvd_card _
        have hcop : Nat.Coprime (p ^ 4) (Nat.card ψ.ker) :=
          Nat.Coprime.pow_left 4 (Nat.Coprime.coprime_dvd_right hN hZ)
        have h5 : p ^ 4 ∣ Nat.card (Q ⧸ ψ.ker) := by
          have : p ^ 4 ∣ Nat.card (Q ⧸ ψ.ker) * Nat.card ψ.ker := hQN ▸ hQp
          exact hcop.dvd_of_dvd_mul_right this
        exact not_pow_four_dvd_card_GL ha3 (h4 ▸ h5.trans h2)
    intro g x hx
    have := MonoidHom.mem_ker.mp (hψ ▸ Subgroup.mem_top g)
    have h1 := congrArg (fun τ : MulAut ↥A => ((τ ⟨x, hx⟩ : ↥A) : W)) this
    simpa [ψ, MulAut.conjNormal_apply] using h1
  obtain ⟨u, huA, hu1⟩ : ∃ u ∈ A, u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hAne (Subgroup.eq_bot_iff_forall _ |>.mpr hcon)
  have hupow : u ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian u huA
  have hu : orderOf u = p := orderOf_eq_prime hupow hu1
  have hcu : ∀ g : Q, Commute (σ g) u := fun g => mul_inv_eq_iff_eq_mul.mp (hcentr g u huA)
  set S₁ : Subgroup W := E₀.map σ with hS₁
  set S₂ : Subgroup W := Subgroup.zpowers u with hS₂
  have hS₁el : IsElementaryAbelian p S₁ := isElementaryAbelian_map' σ hE₀
  have hcomm : ∀ (x : ↥S₁) (y : ↥S₂), Commute (S₁.subtype x) (S₂.subtype y) := by
    intro x y
    obtain ⟨g, -, hgx⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp y.2
    change Commute (x : W) (y : W)
    rw [← hgx, ← hn]
    exact (hcu g).zpow_right n
  let φ : ↥S₁ × ↥S₂ →* W := MonoidHom.noncommCoprod S₁.subtype S₂.subtype hcomm
  have hφ : ∀ x y, φ (x, y) = (x : W) * (y : W) := fun x y => rfl
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, y⟩ hxy
    rw [hφ] at hxy
    obtain ⟨g, hg, hgx⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp y.2
    have hy : (y : W) ∈ π.ker := by
      rw [← hn]
      exact Subgroup.zpow_mem _ (hAker huA) n
    have hπy : π (y : W) = 1 := hy
    have hπx : π (x : W) = 1 := by
      have : (x : W) = ((y : W))⁻¹ := eq_inv_of_mul_eq_one_left hxy
      rw [this, map_inv, hπy, inv_one]
    have hg1 : g = 1 := by
      have := hσ g
      rw [hgx, hπx] at this
      exact this.symm
    have hx1 : x = 1 := Subtype.ext (by rw [← hgx, hg1, map_one]; rfl)
    have hy1 : y = 1 := by
      have : (y : W) = 1 := by
        rw [hx1] at hxy
        simpa using hxy
      exact Subtype.ext this
    rw [hx1, hy1]
    rfl
  have hEel : IsElementaryAbelian p φ.range := by
    have hS₂comm : ∀ a b : ↥S₂, a * b = b * a := fun a b =>
      (IsMulCommutative.is_comm (M := S₂)).comm a b
    have hS₁comm : ∀ a b : ↥S₁, a * b = b * a := fun a b =>
      (IsMulCommutative.is_comm (M := S₁)).comm a b
    refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
    · obtain ⟨⟨x₁, x₂⟩, ha⟩ := a.2
      obtain ⟨⟨y₁, y₂⟩, hb⟩ := b.2
      apply Subtype.ext
      change (a : W) * b = b * a
      rw [← ha, ← hb, ← map_mul, ← map_mul]
      congr 1
      exact Prod.ext (hS₁comm x₁ y₁) (hS₂comm x₂ y₂)
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun z => Subtype.ext ?_
      obtain ⟨⟨x₁, x₂⟩, hz⟩ := z.2
      rw [Subgroup.coe_pow, ← hz, ← map_pow]
      have h1 : x₁ ^ p = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (x₁ : W) x₁.2)
      have h2 : x₂ ^ p = 1 := by
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp x₂.2
        apply Subtype.ext
        rw [Subgroup.coe_pow, ← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
          hupow, one_zpow]
        rfl
      rw [Prod.pow_mk, h1, h2]
      exact map_one φ
  have hcardE : Nat.card φ.range = p ^ 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv, Nat.card_prod]
    have h1 : Nat.card ↥S₁ = p ^ 3 := by
      rw [hS₁, Subgroup.card_map_of_injective hσinj, hcard]
    have h2 : Nat.card ↥S₂ = p := by rw [hS₂, Nat.card_zpowers, hu]
    rw [h1, h2]
    ring
  exact ⟨φ.range, 4, le_rfl, hEel, hcardE⟩

theorem rank_four_of_cover_quasisimple_ker {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Q : Type}
    [Group Q] [Finite Q] (hQ : CFSG.IsQuasisimple Q)
    (hZ : Nat.Coprime p (Nat.card (center Q))) (h : Q) (hhc : h ∉ center Q)
    (hho : Nat.Coprime (orderOf h) p) (hQp : p ^ 4 ∣ Nat.card Q)
    (hclosed : ∀ (W : Type) [Group W] [Finite W] (π : W →* Q), Function.Surjective π →
      π.ker ≤ center W → IsPGroup p π.ker → ∃ s : Q →* W, ∀ g, π (s g) = g)
    {E₀ : Subgroup Q} (hE₀ : IsElementaryAbelian p E₀) (hcard : Nat.card E₀ = p ^ 3)
    {W : Type} [Group W] [Finite W] (π : W →* Q) (hπ : Function.Surjective π)
    (hker : IsPGroup p π.ker) (hker1 : π.ker ≠ ⊥) :
    ∃ (E : Subgroup W) (k : ℕ), 4 ≤ k ∧ IsElementaryAbelian p E ∧ Nat.card E = p ^ k := by
  by_contra hno
  have hrank := card_le_pow_three_of_not_rank_four hno
  obtain ⟨σ, hσ⟩ :=
    exists_section_of_rank_le_three hp2 hQ hZ h hhc hho hQp hclosed π hπ hker hrank
  exact hno (exists_rank_four_of_section_ker hQ hZ hQp hE₀ hcard π hker hker1 hrank σ hσ)

end CFSG.RankThree.PartOne.SLB4B
