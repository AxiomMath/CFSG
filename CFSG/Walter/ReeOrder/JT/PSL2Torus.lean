module

public import CFSG.Walter.ReeOrder.JT.PSL2Unipotent

public section

namespace CFSG.Walter.JT

open scoped MatrixGroups Pointwise

theorem TorusData.conj {X : Type*} [Group X] {L U : Subgroup X} {w : X} (hU : TorusData L U w)
    {g : X} (hg : g ∈ L) :
    TorusData L (U.map (MulAut.conj g).toMonoidHom) (g * w * g⁻¹) := by
  have hLg : L.map (MulAut.conj g).toMonoidHom = L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact L.mul_mem (L.mul_mem hg hy) (L.inv_mem hg)
    · intro hx
      exact ⟨g⁻¹ * x * g, L.mul_mem (L.mul_mem (L.inv_mem hg) hx) hg, by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
  refine ⟨?_, ?_, L.mul_mem (L.mul_mem hg hU.w_mem) (L.inv_mem hg), ?_, ?_, ?_, ?_⟩
  · rw [← hLg]
    exact Subgroup.map_mono hU.le
  · have := hU.cyclic
    exact isCyclic_of_surjective (U.equivMapOfInjective _ (MulAut.conj g).injective)
      (MulEquiv.surjective _)
  · rintro ⟨y, hy, hyw⟩
    apply hU.w_not_mem
    have : y = w := by
      have := congrArg (fun z => g⁻¹ * z * g) hyw
      simpa [mul_assoc] using this
    exact this ▸ hy
  · rw [show g * w * g⁻¹ * (g * w * g⁻¹) = g * (w * w) * g⁻¹ by group, hU.w_mul_self]
    group
  · rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show g * w * g⁻¹ * (g * y * g⁻¹) * (g * w * g⁻¹)⁻¹ = g * (w * y * w⁻¹) * g⁻¹ by group,
      hU.inv y hy]
    group
  · intro R hRU hR
    set R₀ := R.map (MulAut.conj g⁻¹).toMonoidHom with hR₀
    have hRR₀ : R = R₀.map (MulAut.conj g).toMonoidHom := by
      ext x
      constructor
      · intro hx
        refine ⟨(MulAut.conj g⁻¹).toMonoidHom x, ⟨x, hx, rfl⟩, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rwa [show g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y by group]
    have hR₀U : R₀ ≤ U := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨u, hu, rfl⟩ := hRU hy
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rwa [show g⁻¹ * (g * u * g⁻¹) * g⁻¹⁻¹ = u by group]
    have hR₀ne : R₀ ≠ ⊥ := by
      intro h0
      apply hR
      rw [hRR₀, h0, Subgroup.map_bot]
    have h := hU.normalizer R₀ hR₀U hR₀ne
    have h2 := congrArg (fun H => H.map (MulAut.conj g).toMonoidHom) h
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hLg,
      Subgroup.map_equiv_normalizer_eq, ← hRR₀, Subgroup.map_sup, MonoidHom.map_zpowers] at h2
    exact h2

section PSL2

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]

theorem psl2_exists_conj_of_cyclic (hK : Nat.card K = p ^ f) (hp : p ≠ 2) (hf : f ≠ 0)
    (hq : 5 ≤ p ^ f) {C₁ C₂ : Subgroup PSL(2, K)} (hC₁ : IsCyclic C₁) (hC₂ : IsCyclic C₂)
    (h₁ : 2 * Nat.card C₁ + 1 = p ^ f) (h₂ : 2 * Nat.card C₂ + 1 = p ^ f) :
    ∃ g : PSL(2, K), C₂ = C₁.map (MulAut.conj g).toMonoidHom := by
  classical
  let P : Sylow p PSL(2, K) := default
  obtain ⟨U, S, -, hU, -, hS, hpart⟩ :=
    Glauberman.Dickson.huppert_II_8_5_a_psl2_cover (F := K) hK P
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  have hqodd : Odd (p ^ f) := hpodd.pow
  have hgcd : Nat.gcd (Nat.card K - 1) 2 = 2 := by
    apply Nat.gcd_eq_right
    rw [hK]
    obtain ⟨k, hk⟩ := hqodd
    exact ⟨k, by omega⟩
  rw [hgcd, hK] at hU hS
  have hconj : ∀ C : Subgroup PSL(2, K), IsCyclic C → 2 * Nat.card C + 1 = p ^ f →
      ∃ g : PSL(2, K), C = U.map (MulAut.conj g).toMonoidHom := by
    intro C hC hCcard
    obtain ⟨c, hc⟩ := hC.exists_generator
    have hco : orderOf (c : PSL(2, K)) = Nat.card C := by
      rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hc]
    have hCz : C = Subgroup.zpowers (c : PSL(2, K)) := by
      refine (Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr c.2) ?_).symm
      rw [Nat.card_zpowers, hco]
    have hc1 : (c : PSL(2, K)) ≠ 1 := by
      intro h0
      rw [h0, orderOf_one] at hco
      omega
    obtain ⟨T, ⟨hcT, hT⟩, -⟩ := hpart c hc1
    rcases hT with ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩
    ·
      exfalso
      have h1 : orderOf (c : PSL(2, K)) ∣ p ^ f := by
        have := Subgroup.orderOf_dvd_natCard _ hcT
        rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective,
          psl2_card_sylow_p hK hp hf P] at this
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp h1
      rcases j with _ | j
      · rw [pow_zero] at hj
        omega
      · have hpd : p ∣ Nat.card C := by
          rw [← hco, hj]
          exact dvd_pow_self p (Nat.succ_ne_zero j)
        have hpq : p ∣ p ^ f := dvd_pow_self p hf
        have : p ∣ 1 := by
          have h2 : p ∣ 2 * Nat.card C := dvd_mul_of_dvd_right hpd 2
          have h3 : p ∣ 2 * Nat.card C + 1 := hCcard ▸ hpq
          exact (Nat.dvd_add_right h2).mp h3
        exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp this)
    · refine ⟨g, ?_⟩
      rw [hCz]
      refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hcT) ?_
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hU, Nat.card_zpowers, hco]
      omega
    ·
      exfalso
      have h1 : orderOf (c : PSL(2, K)) ∣ (p ^ f + 1) / 2 := by
        have := Subgroup.orderOf_dvd_natCard _ hcT
        rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective, hS] at this
      rw [hco, show (p ^ f + 1) / 2 = Nat.card C + 1 by omega] at h1
      have := (Nat.dvd_add_right (dvd_refl _)).mp h1
      rw [Nat.dvd_one] at this
      omega
  obtain ⟨g₁, hg₁⟩ := hconj C₁ hC₁ h₁
  obtain ⟨g₂, hg₂⟩ := hconj C₂ hC₂ h₂
  refine ⟨g₂ * g₁⁻¹, ?_⟩
  rw [hg₁, hg₂, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulAut.conj_apply]
  group

end PSL2

theorem exists_torusData_of_isCyclic
    {G : Type*} [Group G] {p f : ℕ} [Fact p.Prime]
    (F : Subgroup G) (e : F ≃* PSL(2, GaloisField p f)) (hp : p ≠ 2) (hq : 5 < p ^ f)
    (hq4 : p ^ f % 4 = 3) {C : Subgroup G} (hCF : C ≤ F) (hC : IsCyclic C)
    (hCcard : 2 * Nat.card C + 1 = p ^ f) : ∃ w : G, TorusData F C w := by
  classical
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hF := psl2Facts F e hp hq
  obtain ⟨U₀, w₀, hU₀, hU₀card⟩ := hF.odd_torus
  have hU₀card' : 2 * Nat.card U₀ + 1 = p ^ f := by
    rcases hU₀card with ⟨-, h1⟩ | ⟨h1, -⟩
    · exact h1
    · omega
  set K := GaloisField p f
  have hKcard : Nat.card K = p ^ f := GaloisField.card p f hf
  let ι : PSL(2, K) →* G := F.subtype.comp e.symm.toMonoidHom
  have hι : Function.Injective ι := F.subtype_injective.comp e.symm.injective
  have hrange : ι.range = F := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (e.symm y).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [ι]⟩
  have hmapcomap : ∀ X : Subgroup G, X ≤ F → (X.comap ι).map ι = X := fun X hX =>
    Subgroup.map_comap_eq_self (hrange ▸ hX)
  have hcyc : ∀ X : Subgroup G, X ≤ F → IsCyclic X → IsCyclic (X.comap ι) := by
    intro X hX hXc
    exact isCyclic_of_surjective (((X.comap ι).equivMapOfInjective ι hι).trans
      (MulEquiv.subgroupCongr (hmapcomap X hX))).symm (MulEquiv.surjective _)
  have hcard : ∀ X : Subgroup G, X ≤ F → Nat.card (X.comap ι) = Nat.card X := fun X hX => by
    rw [← Subgroup.card_map_of_injective hι, hmapcomap X hX]
  obtain ⟨g, hg⟩ := psl2_exists_conj_of_cyclic hKcard hp hf hq.le (hcyc U₀ hU₀.le hU₀.cyclic)
    (hcyc C hCF hC) (by rw [hcard U₀ hU₀.le]; exact hU₀card') (by rw [hcard C hCF]; exact hCcard)
  have hcomm : ι.comp (MulAut.conj g).toMonoidHom = (MulAut.conj (ι g)).toMonoidHom.comp ι := by
    ext x
    simp [map_mul, map_inv]
  have hCU : C = U₀.map (MulAut.conj (ι g)).toMonoidHom := by
    rw [← hmapcomap C hCF, hg, Subgroup.map_map, hcomm, ← Subgroup.map_map,
      hmapcomap U₀ hU₀.le]
  have hιg : ι g ∈ F := hrange ▸ ⟨g, rfl⟩
  exact ⟨ι g * w₀ * (ι g)⁻¹, hCU ▸ hU₀.conj hιg⟩

theorem exists_cyclic_of_coprime {G : Type*} [Group G] {p f : ℕ} [Fact p.Prime]
    (F : Subgroup G) (e : F ≃* PSL(2, GaloisField p f)) (hp : p ≠ 2) (hq : 5 < p ^ f)
    {x : G} (hxF : x ∈ F) (hx1 : x ≠ 1) (hcop : Nat.Coprime (orderOf x) p) :
    ∃ C : Subgroup G, C ≤ F ∧ IsCyclic C ∧ x ∈ C ∧
      (2 * Nat.card C + 1 = p ^ f ∨ 2 * Nat.card C = p ^ f + 1) := by
  classical
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  set K := GaloisField p f
  have hKcard : Nat.card K = p ^ f := GaloisField.card p f hf
  let ι : PSL(2, K) →* G := F.subtype.comp e.symm.toMonoidHom
  have hι : Function.Injective ι := F.subtype_injective.comp e.symm.injective
  have hιe : ∀ y : F, ι (e y) = y := fun y => by simp [ι]
  have hrange : ι.range = F := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact (e.symm z).2
    · intro hy
      exact ⟨e ⟨y, hy⟩, hιe ⟨y, hy⟩⟩
  set x₀ := e ⟨x, hxF⟩ with hx₀
  have hx₀x : ι x₀ = x := hιe ⟨x, hxF⟩
  have hx₀1 : x₀ ≠ 1 := fun h0 => hx1 (by rw [← hx₀x, h0, map_one])
  have hx₀o : orderOf x₀ = orderOf x := by
    rw [hx₀, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  have hqodd : Odd (p ^ f) := hpodd.pow
  have hgcd : Nat.gcd (Nat.card K - 1) 2 = 2 := by
    apply Nat.gcd_eq_right
    rw [hKcard]
    obtain ⟨k, hk⟩ := hqodd
    exact ⟨k, by omega⟩
  let P : Sylow p PSL(2, K) := default
  obtain ⟨U, S, hUc, hU, hSc, hS, hpart⟩ :=
    Glauberman.Dickson.huppert_II_8_5_a_psl2_cover (F := K) hKcard P
  rw [hgcd, hKcard] at hU hS
  obtain ⟨T, ⟨hxT, hT⟩, -⟩ := hpart x₀ hx₀1
  have hmapC : ∀ (C₀ : Subgroup PSL(2, K)) (g : PSL(2, K)), IsCyclic C₀ →
      x₀ ∈ C₀.map (MulAut.conj g).toMonoidHom →
      ∃ C : Subgroup G, C ≤ F ∧ IsCyclic C ∧ x ∈ C ∧
        Nat.card C = Nat.card C₀ := by
    intro C₀ g hC₀ hxC₀
    refine ⟨(C₀.map (MulAut.conj g).toMonoidHom).map ι, ?_, ?_, ⟨x₀, hxC₀, hx₀x⟩, ?_⟩
    · rw [← hrange]
      exact Subgroup.map_le_range ι _
    · have : IsCyclic (C₀.map (MulAut.conj g).toMonoidHom) :=
        isCyclic_of_surjective (C₀.equivMapOfInjective _ (MulAut.conj g).injective)
          (MulEquiv.surjective _)
      exact isCyclic_of_surjective ((C₀.map (MulAut.conj g).toMonoidHom).equivMapOfInjective
        ι hι) (MulEquiv.surjective _)
    · rw [Subgroup.card_map_of_injective hι,
        Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rcases hT with ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩
  ·
    exfalso
    have h1 : orderOf x₀ ∣ p ^ f := by
      have := Subgroup.orderOf_dvd_natCard _ hxT
      rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective,
        psl2_card_sylow_p hKcard hp hf P] at this
    have h2 : Nat.Coprime (orderOf x₀) (p ^ f) := by
      rw [hx₀o]
      exact Nat.Coprime.pow_right _ hcop
    apply hx₀1
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h2 h1)
  · obtain ⟨C, hCF, hCc, hxC, hCcard⟩ := hmapC U g hUc hxT
    refine ⟨C, hCF, hCc, hxC, Or.inl ?_⟩
    rw [hCcard, hU]
    obtain ⟨k, hk⟩ := hqodd
    omega
  · obtain ⟨C, hCF, hCc, hxC, hCcard⟩ := hmapC S g hSc hxT
    refine ⟨C, hCF, hCc, hxC, Or.inr ?_⟩
    rw [hCcard, hS]
    obtain ⟨k, hk⟩ := hqodd
    omega

end CFSG.Walter.JT
