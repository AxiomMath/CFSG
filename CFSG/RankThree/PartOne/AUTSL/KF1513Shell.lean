module

public import CFSG.RankThree.PartOne.S12.Sec1514Defs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.RankThree.PartOne.AUTSL

open CFSG.ComponentClassification CFSG.RankThree.PartOne

section Act

variable {G : Type} [Group G]

@[expose] def conjOn (I : Subgroup G) (h : G) (hh : h ∈ Subgroup.normalizer (I : Set G)) :
    MulAut I where
  toFun i := ⟨h * i * h⁻¹, (Subgroup.mem_normalizer_iff.1 hh i).1 i.2⟩
  invFun i := ⟨h⁻¹ * i * h⁻¹⁻¹, (Subgroup.mem_normalizer_iff.1 (inv_mem hh) i).1 i.2⟩
  left_inv i := Subtype.ext (by group)
  right_inv i := Subtype.ext (by group)
  map_mul' a b := Subtype.ext (by
    change h * ((a : G) * b) * h⁻¹ = h * a * h⁻¹ * (h * b * h⁻¹)
    group)

theorem conjOn_apply (I : Subgroup G) (h : G) (hh : h ∈ Subgroup.normalizer (I : Set G))
    (i : I) : ((conjOn I h hh i : I) : G) = h * i * h⁻¹ := rfl

@[expose] def actHom (I H : Subgroup G) (hHN : H ≤ Subgroup.normalizer (I : Set G)) :
    H →* MulAut I where
  toFun h := conjOn I h.1 (hHN h.2)
  map_one' := by
    refine MulEquiv.ext fun i => Subtype.ext ?_
    change (1 : G) * i * (1 : G)⁻¹ = i
    group
  map_mul' g h := by
    refine MulEquiv.ext fun i => Subtype.ext ?_
    change (g.1 * h.1) * i * (g.1 * h.1)⁻¹ = g.1 * (h.1 * i * h.1⁻¹) * g.1⁻¹
    group

theorem actHom_apply (I H : Subgroup G) (hHN : H ≤ Subgroup.normalizer (I : Set G)) (h : H)
    (i : I) : ((actHom I H hHN h i : I) : G) = h * i * (h : G)⁻¹ := rfl

end Act

section Shell

variable {G : Type} [Group G] [Finite G] {p : ℕ} {I H T A₀ : Subgroup G}

theorem exists_conj_mem_sylow_two {K T : Subgroup G} (hT : ABGLocalTools.IsSylowOf 2 T K) {y : G}
    (hy : y ∈ K) (hy2 : y ^ 2 = 1) : ∃ h ∈ K, h * y * h⁻¹ ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, rfl⟩ := hT
  have hZ : IsPGroup 2 (Subgroup.zpowers (⟨y, hy⟩ : K)) := by
    have hd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hy2
    obtain ⟨k, -, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show orderOf y ∣ 2 ^ 1 from hd)
    refine IsPGroup.of_card (n := k) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hk']
  obtain ⟨S', hS'⟩ := hZ.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq K S' S
  have hmem : n * ⟨y, hy⟩ * n⁻¹ ∈ (S : Subgroup K) := by
    rw [← hn, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hS' (Subgroup.mem_zpowers _))
  exact ⟨n, n.2, ⟨_, hmem, rfl⟩⟩

theorem kf1513_shell (hcfg : Config1514 p I H T A₀) (hTI : ¬ T ≤ I)
    {Γ : Type} [Group Γ] (Ψ : I ≃* Γ) (β : MulAut Γ) (hβ2 : β * β = 1)
    (hβI : β ∉ OuterAutomorphisms.inner Γ)
    (hout : ∀ Hb : Subgroup (MulAut Γ), OuterAutomorphisms.inner Γ ≤ Hb → ∀ x ∈ Hb,
      x ∉ OuterAutomorphisms.inner Γ → (∃ a : ℕ, x ^ 2 ^ a = 1) → β ∈ Hb)
    (hO2 : ∀ R : Subgroup Γ, (∀ r ∈ R, β r = r) →
      (∀ s : Γ, β s = s → ∀ r ∈ R, s * r * s⁻¹ ∈ R) → IsPGroup 2 R → R = ⊥)
    (hA : ∀ (a : G) (ha : a ∈ A₀), β (Ψ ⟨a, hcfg.A_le ha⟩) = Ψ ⟨a, hcfg.A_le ha⟩) :
    ∃ t ∈ T, t ^ 2 = 1 ∧ t ∉ I ∧ I ⊓ Subgroup.centralizer ({t} : Set G) ≠ ⊥ ∧
      (∀ Q : Subgroup G, Q ≤ I ⊓ Subgroup.centralizer ({t} : Set G) →
        I ⊓ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (Q : Set G) →
        IsPGroup 2 Q → Q = ⊥) ∧
      ∃ h ∈ H, ∃ B : Subgroup G, B ≤ A₀ ∧ Nat.card ↥A₀ ≤ p * Nat.card ↥B ∧
        B.map (MulAut.conj h).toMonoidHom ≤ I ⊓ Subgroup.centralizer ({t} : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHN := hcfg.H_le_N
  let ρ : H →* MulAut Γ := (MulAut.congr Ψ).toMonoidHom.comp (actHom I H hHN)
  have hρapp : ∀ (h : H) (i : I), ρ h (Ψ i) = Ψ (actHom I H hHN h i) := by
    intro h i
    change (MulAut.congr Ψ) (actHom I H hHN h) (Ψ i) = _
    rw [MulAut.congr_apply]
    simp
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro h hh
    have hc : (h : G) ∈ Subgroup.centralizer (I : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro i hi
      have h1 := hρapp h ⟨i, hi⟩
      rw [hh, MulAut.one_apply] at h1
      have h2 := Ψ.injective h1
      have h3 : (h : G) * i * (h : G)⁻¹ = i := congrArg Subtype.val h2.symm
      have h4 : (h : G) * i = i * h := by
        calc (h : G) * i = (h : G) * i * (h : G)⁻¹ * h := by group
          _ = i * h := by rw [h3]
      exact h4.symm
    have : (h : G) ∈ H ⊓ Subgroup.centralizer (I : Set G) := ⟨h.2, hc⟩
    rw [hcfg.faithful, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hρI : ∀ i : I, ρ ⟨i, hcfg.le_H i.2⟩ = MulAut.conj (Ψ i) := by
    intro i
    refine MulEquiv.ext fun x => ?_
    obtain ⟨j, rfl⟩ := Ψ.surjective x
    rw [hρapp, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hinner : OuterAutomorphisms.inner Γ ≤ ρ.range := by
    rintro _ ⟨γ, rfl⟩
    refine ⟨⟨(Ψ.symm γ : G), hcfg.le_H (Ψ.symm γ).2⟩, ?_⟩
    rw [hρI (Ψ.symm γ), MulEquiv.apply_symm_apply]
  have hρmemI : ∀ h : H, (h : G) ∈ I → ρ h ∈ OuterAutomorphisms.inner Γ := by
    intro h hI
    have : h = ⟨(⟨h, hI⟩ : I), hcfg.le_H hI⟩ := rfl
    rw [this, hρI]
    exact ⟨_, rfl⟩
  obtain ⟨x₀, hx₀T, hx₀I⟩ := Set.not_subset.1 hTI
  have hx₀H : x₀ ∈ H := hcfg.sylow.1 hx₀T
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (⟨x₀, hx₀H⟩ : H) ^ 2 ^ a = 1 := by
    obtain ⟨k, hk⟩ := hcfg.sylow.2.1 (⟨x₀, hx₀T⟩ : T)
    have h : x₀ ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact ⟨k, Subtype.ext (by simpa using h)⟩
  have hxnot : ρ ⟨x₀, hx₀H⟩ ∉ OuterAutomorphisms.inner Γ := by
    intro hmem
    obtain ⟨γ, hγ⟩ := hmem
    have h1 : ρ ⟨(Ψ.symm γ : G), hcfg.le_H (Ψ.symm γ).2⟩ = MulAut.conj γ := by
      rw [hρI (Ψ.symm γ), MulEquiv.apply_symm_apply]
    have h2 := hρinj (h1.trans hγ)
    have h3 : ((Ψ.symm γ : I) : G) = x₀ := congrArg Subtype.val h2
    exact hx₀I (by rw [← h3]; exact (Ψ.symm γ).2)
  obtain ⟨h₁, hh₁⟩ := hout ρ.range hinner (ρ ⟨x₀, hx₀H⟩) ⟨_, rfl⟩ hxnot
    ⟨a, by rw [← map_pow, ha, map_one]⟩
  have hh₁2 : h₁ * h₁ = 1 := hρinj (by rw [map_mul, map_one, hh₁, hβ2])
  have hh₁I : (h₁ : G) ∉ I := fun hI => hβI (hh₁ ▸ hρmemI h₁ hI)
  have hTabg : ABGLocalTools.IsSylowOf 2 T H := (ABGLocalTools.isSylowOf_iff (p := 2)).2 hcfg.sylow
  have hh₁G : (h₁ : G) ^ 2 = 1 := by
    have := congrArg Subtype.val hh₁2
    simpa [sq] using this
  obtain ⟨g, hgH, hgT⟩ := exists_conj_mem_sylow_two hTabg h₁.2 hh₁G
  have hgN : g ∈ Subgroup.normalizer (I : Set G) := hHN hgH
  have hginvN : g⁻¹ ∈ Subgroup.normalizer (I : Set G) := inv_mem hgN
  have ht2 : (g * h₁ * g⁻¹) ^ 2 = 1 := by
    calc (g * h₁ * g⁻¹) ^ 2 = g * (h₁ : G) ^ 2 * g⁻¹ := by rw [sq, sq]; group
      _ = 1 := by rw [hh₁G]; group
  have htI : g * h₁ * g⁻¹ ∉ I := by
    intro htI
    apply hh₁I
    have := (Subgroup.mem_normalizer_iff.1 hginvN _).1 htI
    rwa [show g⁻¹ * (g * (h₁ : G) * g⁻¹) * g⁻¹⁻¹ = h₁ by group] at this
  have hconj : ∀ x : G, x * (g * h₁ * g⁻¹) = (g * h₁ * g⁻¹) * x ↔
      (g⁻¹ * x * g⁻¹⁻¹) * h₁ = h₁ * (g⁻¹ * x * g⁻¹⁻¹) := by
    intro x
    constructor
    · intro h
      have := congrArg (fun y => g⁻¹ * y * g) h
      calc g⁻¹ * x * g⁻¹⁻¹ * (h₁ : G) = g⁻¹ * (x * (g * h₁ * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * h₁ * g⁻¹ * x) * g := this
        _ = h₁ * (g⁻¹ * x * g⁻¹⁻¹) := by group
    · intro h
      calc x * (g * h₁ * g⁻¹) = g * ((g⁻¹ * x * g⁻¹⁻¹) * h₁) * g⁻¹ := by group
        _ = g * (h₁ * (g⁻¹ * x * g⁻¹⁻¹)) * g⁻¹ := by rw [h]
        _ = g * h₁ * g⁻¹ * x := by group
  have hkey : ∀ i : I, ((i : G) ∈ Subgroup.centralizer ({g * h₁ * g⁻¹} : Set G)) ↔
      β (Ψ (conjOn I g⁻¹ hginvN i)) = Ψ (conjOn I g⁻¹ hginvN i) := by
    intro i
    rw [Subgroup.mem_centralizer_singleton_iff, ← hh₁, hρapp, Ψ.injective.eq_iff, Subtype.ext_iff,
      actHom_apply, hconj]
    constructor
    · intro h
      change (h₁ : G) * (g⁻¹ * i * g⁻¹⁻¹) * (h₁ : G)⁻¹ = g⁻¹ * i * g⁻¹⁻¹
      rw [← h]
      group
    · intro h
      change (h₁ : G) * (g⁻¹ * i * g⁻¹⁻¹) * (h₁ : G)⁻¹ = g⁻¹ * i * g⁻¹⁻¹ at h
      calc (g⁻¹ * i * g⁻¹⁻¹) * (h₁ : G)
          = ((h₁ : G) * (g⁻¹ * i * g⁻¹⁻¹) * (h₁ : G)⁻¹) * h₁ := by rw [h]
        _ = h₁ * (g⁻¹ * i * g⁻¹⁻¹) := by group
  have hfixA : ∀ a ∈ A₀, g * a * g⁻¹ ∈ I ⊓ Subgroup.centralizer ({g * h₁ * g⁻¹} : Set G) := by
    intro a ha
    have haI : a ∈ I := hcfg.A_le ha
    have hi₀I : g * a * g⁻¹ ∈ I := (Subgroup.mem_normalizer_iff.1 hgN a).1 haI
    refine ⟨hi₀I, (hkey ⟨g * a * g⁻¹, hi₀I⟩).2 ?_⟩
    have e : conjOn I g⁻¹ hginvN ⟨g * a * g⁻¹, hi₀I⟩ = ⟨a, haI⟩ :=
      Subtype.ext (by rw [conjOn_apply]; group)
    rw [e]
    exact hA a ha
  refine ⟨g * h₁ * g⁻¹, hgT, ht2, htI, ?_, ?_, ?_⟩
  ·
    intro hbot
    obtain ⟨a, ha, ha1⟩ : ∃ a ∈ A₀, a ≠ 1 := by
      by_contra hall
      push Not at hall
      have hA0 : A₀ = ⊥ := (Subgroup.eq_bot_iff_forall A₀).2 hall
      have hcard := hcfg.A_card
      rw [hA0, Subgroup.card_bot] at hcard
      have h5 := hcfg.five_le
      have : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) (by omega)
      omega
    have := hfixA a ha
    rw [hbot, Subgroup.mem_bot] at this
    apply ha1
    calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = 1 := by rw [this]; group
  ·
    intro Q hQC hCN hQ2
    let θ : I ≃* Γ := (conjOn I g⁻¹ hginvN).trans Ψ
    have hθ : ∀ i : I, θ i = Ψ (conjOn I g⁻¹ hginvN i) := fun i => rfl
    let R : Subgroup Γ := (Q.subgroupOf I).map θ.toMonoidHom
    have hR2 : IsPGroup 2 R := (hQ2.comap_subtype (K := I)).map θ.toMonoidHom
    have hRfix : ∀ r ∈ R, β r = r := by
      rintro _ ⟨q, hq, rfl⟩
      have hqC : (q : G) ∈ I ⊓ Subgroup.centralizer ({g * h₁ * g⁻¹} : Set G) := hQC hq
      exact (hkey q).1 hqC.2
    have hRnorm : ∀ s : Γ, β s = s → ∀ r ∈ R, s * r * s⁻¹ ∈ R := by
      intro s hs r hr
      obtain ⟨q, hq, rfl⟩ := hr
      let c : I := θ.symm s
      have hcs : θ c = s := θ.apply_symm_apply s
      have hcC : (c : G) ∈ I ⊓ Subgroup.centralizer ({g * h₁ * g⁻¹} : Set G) :=
        ⟨c.2, (hkey c).2 (by rw [← hθ, hcs]; exact hs)⟩
      have hcN := hCN hcC
      refine ⟨c * q * c⁻¹, ?_, ?_⟩
      · show c * q * c⁻¹ ∈ Q.subgroupOf I
        rw [Subgroup.mem_subgroupOf]
        have := (Subgroup.mem_normalizer_iff.1 hcN (q : G)).1 hq
        simpa using this
      · simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, hcs]
    have hRbot := hO2 R hRfix hRnorm hR2
    refine (Subgroup.eq_bot_iff_forall Q).2 fun q hq => ?_
    have hqI : q ∈ I := (hQC hq).1
    have hmem : θ ⟨q, hqI⟩ ∈ R := ⟨⟨q, hqI⟩, hq, rfl⟩
    rw [hRbot, Subgroup.mem_bot] at hmem
    have h1 : (⟨q, hqI⟩ : I) = 1 := θ.injective (by rw [hmem, map_one])
    exact congrArg Subtype.val h1
  · refine ⟨g, hgH, A₀, le_rfl, ?_, ?_⟩
    · exact Nat.le_mul_of_pos_left _ (by have := hcfg.five_le; omega)
    · rintro _ ⟨a, ha, rfl⟩
      exact hfixA a ha

end Shell

end CFSG.RankThree.PartOne.AUTSL
