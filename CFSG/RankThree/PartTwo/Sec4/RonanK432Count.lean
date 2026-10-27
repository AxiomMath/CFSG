module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Defs
import CFSG.RankThree.PartTwo.Sec4.RonanK432RowTools
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

@[expose] def conjAsPerm (G : Type) [Group G] (g : G) : Equiv.Perm G :=
  MulAut.toPerm G (MulAut.conj g)

theorem conjAsPerm_apply {G : Type} [Group G] (g y : G) : conjAsPerm G g y = g * y * g⁻¹ :=
  rfl

theorem conjAsPerm_pow_three {G : Type} [Group G] {g : G} (hg : g ^ 3 = 1) :
    conjAsPerm G g ^ 3 = 1 := by
  unfold conjAsPerm
  rw [← map_pow, ← map_pow, hg, map_one, map_one]

theorem zpow_eq_zpow_mod_three_of_pow_three {G : Type} [Group G] {g : G} (hg : g ^ 3 = 1)
    (n : ℤ) : g ^ n = g ^ (n % 3) := by
  have h3 : g ^ (3 : ℤ) = 1 := by exact_mod_cast hg
  conv_lhs => rw [← Int.mul_ediv_add_emod n 3]
  rw [zpow_add, zpow_mul, h3, one_zpow, one_mul]

theorem mem_zpowers_of_pow_three {G : Type} [Group G] {g y : G} (hg : g ^ 3 = 1)
    (hy : y ∈ Subgroup.zpowers g) : y = 1 ∨ y = g ∨ y = g ^ 2 := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [zpow_eq_zpow_mod_three_of_pow_three hg n]
  obtain h | h | h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  · exact Or.inl (by simp [h])
  · exact Or.inr (Or.inl (by simp [h]))
  · exact Or.inr (Or.inr (by simp [h]))

theorem natCard_modEq_three_of_perm {α : Type} [Finite α] (P : Equiv.Perm α) (hP : P ^ 3 = 1) :
    Nat.card α ≡ Nat.card {x : α // P x = x} [MOD 3] := by
  classical
  haveI := Fintype.ofFinite α
  have h := Equiv.Perm.card_compl_support_modEq (p := 3) (n := 1) (σ := P)
    (by simpa using hP)
  have hcard : Nat.card {x : α // P x = x} = P.supportᶜ.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp
  rw [hcard, Nat.card_eq_fintype_card]
  exact h.symm

theorem ncard_modEq_three_of_perm {α : Type} (X : Set α) (hX : X.Finite) (e : Equiv.Perm α)
    (he : e ^ 3 = 1) (hXe : ∀ x ∈ X, e x ∈ X) :
    X.ncard ≡ Nat.card {x : X // e x = x} [MOD 3] := by
  haveI : Finite X := hX.to_subtype
  have h3 : ∀ x, e (e (e x)) = x := by
    intro x
    have := congrArg (fun g : Equiv.Perm α => g x) he
    simpa [pow_three', Equiv.Perm.mul_apply] using this
  have hiff : ∀ x, e x ∈ X ↔ x ∈ X := by
    intro x
    refine ⟨fun hx => ?_, hXe x⟩
    have h2 := hXe _ (hXe _ hx)
    rwa [h3 x] at h2
  let P : Equiv.Perm X := e.subtypePerm (p := fun x => x ∈ X) hiff
  have hP : P ^ 3 = 1 := by
    refine Equiv.ext fun x => Subtype.ext ?_
    simp only [pow_three', Equiv.Perm.mul_apply, Equiv.Perm.one_apply, P,
      Equiv.Perm.subtypePerm_apply]
    exact h3 x
  have hcongr : Nat.card {x : X // P x = x} = Nat.card {x : X // e x = x} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => Subtype.ext_iff)
  have hmod := natCard_modEq_three_of_perm P hP
  rw [Nat.card_coe_set_eq, hcongr] at hmod
  exact hmod

theorem mem_zpowers_of_conj_commute {S : Type} [Group S] {z y : S}
    (h : WeaklyClosed (Subgroup.zpowers z)) (hy : y ∈ conjugatesOf z) (hc : z * y = y * z) :
    y ∈ Subgroup.zpowers z := by
  by_contra hnot
  obtain ⟨c, hcy⟩ := isConj_iff.mp (show IsConj z y from hy)
  refine not_weaklyClosed_of_commute_conj (z := z) (g := c) ?_ ?_ h
  · rw [hcy]
    exact hc.symm
  · rw [hcy]
    exact hnot

theorem three_not_dvd_index_centralizer_of_weaklyClosed {S : Type} [Group S] [Finite S] {z : S}
    (hz : orderOf z = 3) (h : WeaklyClosed (Subgroup.zpowers z)) :
    ¬ 3 ∣ (Subgroup.centralizer ({z} : Set S)).index := by
  rw [Subgroup.index_centralizer_eq_ncard]
  intro h3
  have hz3 : z ^ 3 = 1 := by
    rw [← hz]
    exact pow_orderOf_eq_one z
  have hX : ∀ y ∈ conjugatesOf z, conjAsPerm S z y ∈ conjugatesOf z := by
    intro y hy
    obtain ⟨c, hc⟩ := isConj_iff.mp (show IsConj z y from hy)
    show IsConj z (z * y * z⁻¹)
    rw [isConj_iff]
    exact ⟨z * c, by rw [← hc]; group⟩
  have hmod := ncard_modEq_three_of_perm (conjugatesOf z) (Set.toFinite _) (conjAsPerm S z)
    (conjAsPerm_pow_three hz3) hX
  have hfix : ∀ x : {x : conjugatesOf z // conjAsPerm S z x = x},
      (x.1 : S) ∈ ({z, z ^ 2} : Set S) := by
    intro x
    have hcomm : z * (x.1 : S) = (x.1 : S) * z := by
      have hx : z * (x.1 : S) * z⁻¹ = x.1 := x.2
      exact mul_inv_eq_iff_eq_mul.mp hx
    rcases mem_zpowers_of_pow_three hz3
        (mem_zpowers_of_conj_commute h x.1.2 hcomm) with h1 | h1 | h1
    · exfalso
      have h2 : IsConj z (x.1 : S) := x.1.2
      rw [h1, isConj_one_left] at h2
      rw [h2, orderOf_one] at hz
      exact absurd hz (by norm_num)
    · simp [h1]
    · simp [h1]
  have hle : Nat.card {x : conjugatesOf z // conjAsPerm S z x = x} ≤ 2 := by
    have hinj : Function.Injective (fun x : {x : conjugatesOf z // conjAsPerm S z x = x} =>
        (⟨x.1.1, hfix x⟩ : ({z, z ^ 2} : Set S))) := by
      intro x y hxy
      have hval := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext hval)
    calc Nat.card {x : conjugatesOf z // conjAsPerm S z x = x}
        ≤ Nat.card ({z, z ^ 2} : Set S) := Nat.card_le_card_of_injective _ hinj
      _ = ({z, z ^ 2} : Set S).ncard := Nat.card_coe_set_eq _
      _ ≤ ({z ^ 2} : Set S).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]
  have hpos : 0 < Nat.card {x : conjugatesOf z // conjAsPerm S z x = x} := by
    haveI : Nonempty {x : conjugatesOf z // conjAsPerm S z x = x} :=
      ⟨⟨⟨z, mem_conjugatesOf_self⟩, by simp [conjAsPerm_apply]⟩⟩
    exact Nat.card_pos
  unfold Nat.ModEq at hmod
  omega

theorem not_weaklyClosed_of_three_dvd_index {S : Type} [Group S] [Finite S] {z : S}
    (hz : orderOf z = 3) (h3 : 3 ∣ (Subgroup.centralizer ({z} : Set S)).index) :
    ¬ WeaklyClosed (Subgroup.zpowers z) :=
  fun h => three_not_dvd_index_centralizer_of_weaklyClosed hz h h3

@[expose, instance_reducible] def innerMulAct (S : Type) [Group S] : MulAction S (MulAut S) where
  smul x τ := MulAut.conj x * τ * (MulAut.conj x)⁻¹
  one_smul τ := by
    show MulAut.conj 1 * τ * (MulAut.conj 1)⁻¹ = τ
    simp
  mul_smul x y τ := by
    show MulAut.conj (x * y) * τ * (MulAut.conj (x * y))⁻¹ =
      MulAut.conj x * (MulAut.conj y * τ * (MulAut.conj y)⁻¹) * (MulAut.conj x)⁻¹
    simp [mul_assoc]

theorem mul_conj_eq_conj_mul_aut {S : Type} [Group S] (σ : MulAut S) (x : S) :
    σ * MulAut.conj x = MulAut.conj (σ x) * σ := by
  ext y
  show σ (x * y * x⁻¹) = σ x * σ y * (σ x)⁻¹
  simp [map_mul, map_inv]

theorem conj_conj_eq_aut {S : Type} [Group S] (σ : MulAut S) (x : S) :
    σ * (MulAut.conj x * σ * (MulAut.conj x)⁻¹) * σ⁻¹ =
      MulAut.conj (σ x) * σ * (MulAut.conj (σ x))⁻¹ := by
  have h := mul_conj_eq_conj_mul_aut σ x
  calc σ * (MulAut.conj x * σ * (MulAut.conj x)⁻¹) * σ⁻¹
      = (σ * MulAut.conj x) * σ * (σ * MulAut.conj x)⁻¹ := by group
    _ = (MulAut.conj (σ x) * σ) * σ * (MulAut.conj (σ x) * σ)⁻¹ := by rw [h]
    _ = MulAut.conj (σ x) * σ * (MulAut.conj (σ x))⁻¹ := by group

theorem conj_mul_inv_eq_aut {S : Type} [Group S] (σ : MulAut S) (x : S) :
    (MulAut.conj x * σ * (MulAut.conj x)⁻¹) * σ⁻¹ = MulAut.conj (x * σ x⁻¹) := by
  have h := mul_conj_eq_conj_mul_aut σ x⁻¹
  rw [← map_inv (MulAut.conj : S →* MulAut S) x, map_mul]
  calc MulAut.conj x * σ * MulAut.conj x⁻¹ * σ⁻¹
      = MulAut.conj x * (σ * MulAut.conj x⁻¹ * σ⁻¹) := by group
    _ = MulAut.conj x * (MulAut.conj (σ x⁻¹) * σ * σ⁻¹) := by rw [h]
    _ = MulAut.conj x * MulAut.conj (σ x⁻¹) := by group

theorem three_not_dvd_index_of_autWeaklyClosed {S : Type} [Group S] [Finite S] {σ : MulAut S}
    (hσ : σ ^ 3 = 1) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range)
    (h : AutWeaklyClosed σ) :
    ¬ 3 ∣ (Subgroup.comap (MulAut.conj : S →* MulAut S)
      (Subgroup.centralizer ({σ} : Set (MulAut S)))).index := by
  letI : MulAction S (MulAut S) := innerMulAct S
  have hstab : Subgroup.comap (MulAut.conj : S →* MulAut S)
      (Subgroup.centralizer ({σ} : Set (MulAut S))) = MulAction.stabilizer S σ := by
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
      MulAction.mem_stabilizer_iff]
    show MulAut.conj x * σ = σ * MulAut.conj x ↔ MulAut.conj x * σ * (MulAut.conj x)⁻¹ = σ
    rw [mul_inv_eq_iff_eq_mul]
  rw [hstab, MulAction.index_stabilizer]
  intro h3
  have hXe : ∀ τ ∈ MulAction.orbit S σ, conjAsPerm (MulAut S) σ τ ∈ MulAction.orbit S σ := by
    intro τ hτ
    obtain ⟨x, rfl⟩ := MulAction.mem_orbit_iff.mp hτ
    rw [MulAction.mem_orbit_iff]
    exact ⟨σ x, (conj_conj_eq_aut σ x).symm⟩
  have hfix : ∀ τ ∈ MulAction.orbit S σ, conjAsPerm (MulAut S) σ τ = τ → τ = σ := by
    intro τ hτ hfx
    obtain ⟨x, rfl⟩ := MulAction.mem_orbit_iff.mp hτ
    have hfx' : σ * (x • σ) * σ⁻¹ = x • σ := hfx
    have hcomm : (x • σ) * σ = σ * (x • σ) := (mul_inv_eq_iff_eq_mul.mp hfx').symm
    have hzp : x • σ ∈ Subgroup.zpowers σ := h x (mem_normalizer_zpowers_of_commute hcomm)
    have hrange : (x • σ) * σ⁻¹ ∈ (MulAut.conj : S →* MulAut S).range := by
      show (MulAut.conj x * σ * (MulAut.conj x)⁻¹) * σ⁻¹ ∈ _
      rw [conj_mul_inv_eq_aut σ x]
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    rcases mem_zpowers_of_pow_three hσ hzp with h1 | h1 | h1
    · exfalso
      rw [h1, one_mul] at hrange
      exact hout (by simpa using Subgroup.inv_mem _ hrange)
    · exact h1
    · exfalso
      rw [h1, show σ ^ 2 * σ⁻¹ = σ by group] at hrange
      exact hout hrange
  have hσmem : σ ∈ MulAction.orbit S σ := MulAction.mem_orbit_self σ
  have hσfix : conjAsPerm (MulAut S) σ σ = σ := by
    rw [conjAsPerm_apply]
    group
  have hmod := ncard_modEq_three_of_perm (MulAction.orbit S σ)
    (Set.finite_range (fun x : S => x • σ)) (conjAsPerm (MulAut S) σ)
    (conjAsPerm_pow_three hσ) hXe
  have hone : Nat.card {x : MulAction.orbit S σ // conjAsPerm (MulAut S) σ x = x} = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    exact ⟨⟨⟨σ, hσmem⟩, hσfix⟩, fun y => Subtype.ext (Subtype.ext (hfix y.1.1 y.1.2 y.2))⟩
  unfold Nat.ModEq at hmod
  rw [hone] at hmod
  omega

theorem not_autWeaklyClosed_of_three_dvd_index {S : Type} [Group S] [Finite S] {σ : MulAut S}
    (hσ : σ ^ 3 = 1) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range)
    (h3 : 3 ∣ (Subgroup.comap (MulAut.conj : S →* MulAut S)
      (Subgroup.centralizer ({σ} : Set (MulAut S)))).index) :
    ¬ AutWeaklyClosed σ :=
  fun h => three_not_dvd_index_of_autWeaklyClosed hσ hout h h3

end CFSG.RankThree.PartTwo.Sec4.RonanK432
