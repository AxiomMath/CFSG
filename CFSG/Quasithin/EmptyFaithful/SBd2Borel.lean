module

public import CFSG.Quasithin.EmptyFaithful.S153DGen3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5

public section

namespace CFSG.Quasithin

namespace SBd2

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_of_borel {L U M : Subgroup G} (hLU : L ≤ Subgroup.normalizer (U : Set G))
    (α : ↥L →* Alt5) (hαs : Function.Surjective α)
    (hαU : ∀ ℓ : ↥L, α ℓ = 1 → (ℓ : G) ∈ Subgroup.centralizer (U : Set G))
    (hcent : ∀ ℓ : ↥L, (ℓ : G) ∈ Subgroup.centralizer (U : Set G) → (ℓ : G) ∈ M)
    (hLM : ¬ L ≤ M) {P : Subgroup (MulAut ↥U)} (hP : IsSylowTwoOf P (autOn L U))
    (hB : autOn (M ⊓ L) U = autOn L U ⊓ Subgroup.normalizer (P : Set (MulAut ↥U))) :
    ∃ Q : Subgroup Alt5, Nat.card Q = 4 ∧
      ∀ σ : Alt5, (∀ q ∈ Q, σ * q * σ⁻¹ ∈ Q) → ∃ ℓ : ↥L, (ℓ : G) ∈ M ∧ α ℓ = σ := by
  set π : ↥L →* ↥(autOn L U) := S153D.autOnHom hLU with hπ
  have hπs : Function.Surjective π := S153D.autOnHom_surjective hLU
  have hπ1 : ∀ ℓ : ↥L, π ℓ = 1 ↔ (ℓ : G) ∈ Subgroup.centralizer (U : Set G) :=
    S153D.autOnHom_eq_one_iff hLU
  have hkerπα : π.ker ≤ α.ker := by
    have hsimple : IsSimpleGroup Alt5 := alternatingGroup.isSimpleGroup (by simp)
    have hn : ((π.ker).map α).Normal := Subgroup.Normal.map inferInstance α hαs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((π.ker).map α) with hbot | htop
    · intro x hx
      have : α x ∈ (π.ker).map α := ⟨x, hx, rfl⟩
      rw [hbot] at this
      exact Subgroup.mem_bot.mp this
    · exfalso
      apply hLM
      intro g hg
      have hgL : (⟨g, hg⟩ : ↥L) ∈ π.ker := by
        have : α ⟨g, hg⟩ ∈ (π.ker).map α := by rw [htop]; trivial
        obtain ⟨k, hk, hkα⟩ := this
        have h1 : α (k⁻¹ * ⟨g, hg⟩) = 1 := by rw [map_mul, map_inv, hkα, inv_mul_cancel]
        have h2 : π (k⁻¹ * ⟨g, hg⟩) = 1 := (hπ1 _).mpr (hαU _ h1)
        have hk1 : π k = 1 := hk
        rw [map_mul, map_inv, hk1, inv_one, one_mul] at h2
        exact h2
      exact hcent _ ((hπ1 _).mp hgL)
  let ε₀ : ↥(autOn L U) →* Alt5 := (MonoidHom.liftOfSurjective π hπs) ⟨α, hkerπα⟩
  have hε₀ : ∀ ℓ : ↥L, ε₀ (π ℓ) = α ℓ := fun ℓ =>
    MonoidHom.liftOfRightInverse_comp_apply π _ (Function.rightInverse_surjInv hπs) ⟨α, hkerπα⟩ ℓ
  have hε₀inj : Function.Injective ε₀ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    obtain ⟨ℓ, rfl⟩ := hπs y
    rw [hε₀] at hy
    exact (hπ1 ℓ).mpr (hαU ℓ hy)
  have hε₀surj : Function.Surjective ε₀ := by
    intro a
    obtain ⟨ℓ, rfl⟩ := hαs a
    exact ⟨π ℓ, hε₀ ℓ⟩
  let ε : ↥(autOn L U) ≃* Alt5 := MulEquiv.ofBijective ε₀ ⟨hε₀inj, hε₀surj⟩
  have hε : ∀ ℓ : ↥L, ε (π ℓ) = α ℓ := hε₀
  have hε60 : Nat.card ↥(autOn L U) = 60 := by
    rw [Nat.card_congr ε.toEquiv, a5_card]
  set P' : Subgroup ↥(autOn L U) := P.subgroupOf (autOn L U) with hP'
  have hP'2 : IsPGroup 2 ↥P' := hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm
  have hP'idx : ¬ 2 ∣ P'.index := hP.2.2
  have hP'card : Nat.card P' = 4 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hP'2.exists_card_eq
    have h60 : 2 ^ k * P'.index = 60 := by
      rw [← hk, Subgroup.card_mul_index, hε60]
    have hk2 : k = 2 := by
      rcases k with _ | _ | _ | k
      · exfalso; apply hP'idx; rw [pow_zero, one_mul] at h60; omega
      · exfalso; apply hP'idx; rw [pow_one] at h60; omega
      · rfl
      · exfalso
        have h8 : (8 : ℕ) ∣ 60 := ⟨P'.index * 2 ^ k, by rw [← h60]; ring⟩
        omega
    rw [hk, hk2]
    norm_num
  refine ⟨P'.map ε.toMonoidHom, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (f := ε.toMonoidHom) ε.injective, hP'card]
  · intro σ hσ
    obtain ⟨g, rfl⟩ := ε.surjective σ
    have hgP : ∀ p ∈ P', g * p * g⁻¹ ∈ P' := by
      intro p hp
      have h1 := hσ (ε p) ⟨p, hp, rfl⟩
      obtain ⟨p', hp', hpp'⟩ := h1
      have : g * p * g⁻¹ = p' := ε.injective (by rw [map_mul, map_mul, map_inv]; exact hpp'.symm)
      rw [this]
      exact hp'
    have hgN : ((g : ↥(autOn L U)) : MulAut ↥U) ∈ Subgroup.normalizer (P : Set (MulAut ↥U)) := by
      refine A4.mem_normalizer_of_conj_mem fun k hk => ?_
      have hkL : k ∈ autOn L U := hP.1 hk
      have := hgP ⟨k, hkL⟩ (by exact hk)
      exact this
    have hgM : ((g : ↥(autOn L U)) : MulAut ↥U) ∈ autOn (M ⊓ L) U := by
      rw [hB]
      exact ⟨g.2, hgN⟩
    obtain ⟨m, hmN, hmML, hmg⟩ := mem_autOn_iff_exists.mp hgM
    obtain ⟨ℓ', hℓ'⟩ := hπs g
    have hmL : m ∈ L := hmML.2
    refine ⟨ℓ', ?_, ?_⟩
    ·
      have hπm : π ⟨m, hmL⟩ = π ℓ' := by
        apply Subtype.ext
        rw [hℓ']
        exact (S153D.autOnHom_coe hLU ⟨m, hmL⟩).trans hmg
      have hk : π ((⟨m, hmL⟩ : ↥L)⁻¹ * ℓ') = 1 := by
        rw [map_mul, map_inv, hπm, inv_mul_cancel]
      have hkM := hcent _ ((hπ1 _).mp hk)
      have hmM : m ∈ M := hmML.1
      have : (ℓ' : G) = m * (m⁻¹ * (ℓ' : G)) := by group
      rw [this]
      exact M.mul_mem hmM (by simpa using hkM)
    · rw [← hε, hℓ']

end SBd2

end CFSG.Quasithin
