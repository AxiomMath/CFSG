module

import CFSG.Quasithin.EmptyFaithful.SBc11List
import CFSG.Quasithin.EmptyFaithful.S146F3
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Fixed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeKVocab
public import CFSG.Quasithin.Background.B5Part3
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge

theorem d321r_eq_of_conj_eq {G : Type*} [Group G] {L : Subgroup G}
    (hcen : Subgroup.center ↥L = ⊥) {x y : G} (hx : x ∈ L) (hy : y ∈ L)
    (h : ∀ l ∈ L, x * l * x⁻¹ = y * l * y⁻¹) : x = y := by
  have hz : (⟨x⁻¹ * y, L.mul_mem (L.inv_mem hx) hy⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    calc (l : G) * (x⁻¹ * y) = x⁻¹ * (x * l * x⁻¹) * y := by group
      _ = x⁻¹ * (y * l * y⁻¹) * y := by rw [h l l.2]
      _ = x⁻¹ * y * l := by group
  rw [hcen, Subgroup.mem_bot] at hz
  exact inv_mul_eq_one.1 (congrArg Subtype.val hz)

theorem d321r_card_elemAbelian {X : Type} [Group X] (hX : IsPSL 3 2 1 X) (B : Subgroup X)
    (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hsq : ∀ a ∈ B, a ^ 2 = 1) :
    Nat.card B = 1 ∨ Nat.card B = 2 ∨ Nat.card B = 4 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_slThree_of_isPSL hX
  let f : X →* CFSG.QuasithinUnique.Setup.Family.GL32 :=
    Matrix.SpecialLinearGroup.toGL.comp e.toMonoidHom
  have hf : Function.Injective f := Matrix.SpecialLinearGroup.toGL_injective.comp e.injective
  by_cases hB : B = ⊥
  · subst hB
    exact Or.inl Subgroup.card_bot
  · refine Or.inr ?_
    have hB' : B.map f ≠ ⊥ := by
      rw [Ne, Subgroup.map_eq_bot_iff_of_injective B hf]
      exact hB
    have hBc : ∀ a ∈ B.map f, ∀ b ∈ B.map f, a * b = b * a := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hcomm a ha b hb]
    have hBs : ∀ a ∈ B.map f, a ^ 2 = 1 := by
      rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hsq a ha, map_one]
    have hfix := CFSG.QuasithinUnique.Setup.Family.GL3_elementary_abelian_fixed_codimensions
      hB' hBc hBs
    rw [← Subgroup.card_map_of_injective hf]
    rcases hfix with ⟨h2, -⟩ | ⟨h4, -⟩
    · exact Or.inl h2
    · exact Or.inr h4

theorem d321x_rank_cent {W : Type} [CommGroup W] [Finite W] {L A : Subgroup (MulAut W)}
    (hpsl : IsPSL 3 2 1 ↥L) (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hA : IsElemAbelian2 A)
    (hinn : ∀ a ∈ A, ∃ b ∈ L, ∀ l ∈ L, a * l * a⁻¹ = b * l * b⁻¹) :
    rk ↥A ≤ rk ↥(A ⊓ Subgroup.centralizer (L : Set (MulAut W))) + 2 := by
  have hcen : Subgroup.center ↥L = ⊥ := SBc11.center_eq_bot_of_list (Or.inl hpsl)
  have : Finite (MulAut W) :=
    Finite.of_injective (fun σ : MulAut W => (σ : W → W)) DFunLike.coe_injective
  choose! b hbL hb using hinn
  have hmul : ∀ a₁ ∈ A, ∀ a₂ ∈ A, b (a₁ * a₂) = b a₁ * b a₂ := by
    intro a₁ ha₁ a₂ ha₂
    refine d321r_eq_of_conj_eq hcen (hbL _ (A.mul_mem ha₁ ha₂))
      (L.mul_mem (hbL _ ha₁) (hbL _ ha₂)) fun l hl => ?_
    have hl' : a₂ * l * a₂⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hAN ha₂) l).1 hl
    calc b (a₁ * a₂) * l * (b (a₁ * a₂))⁻¹ = a₁ * a₂ * l * (a₁ * a₂)⁻¹ :=
          (hb _ (A.mul_mem ha₁ ha₂) l hl).symm
      _ = a₁ * (a₂ * l * a₂⁻¹) * a₁⁻¹ := by group
      _ = b a₁ * (a₂ * l * a₂⁻¹) * (b a₁)⁻¹ := hb _ ha₁ _ hl'
      _ = b a₁ * (b a₂ * l * (b a₂)⁻¹) * (b a₁)⁻¹ := by rw [hb _ ha₂ l hl]
      _ = b a₁ * b a₂ * l * (b a₁ * b a₂)⁻¹ := by group
  let ψ : ↥A →* ↥L :=
    MonoidHom.mk' (fun a => ⟨b a, hbL a a.2⟩) fun a₁ a₂ => Subtype.ext (hmul a₁ a₁.2 a₂ a₂.2)
  have hker : ψ.ker = (A ⊓ Subgroup.centralizer (L : Set (MulAut W))).subgroupOf A := by
    ext ⟨x, hx⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro h1
      have h2 : b x = 1 := congrArg Subtype.val h1
      refine ⟨hx, fun l hl => ?_⟩
      have h3 := hb x hx l hl
      rw [h2] at h3
      calc l * x = (x * l * x⁻¹) * x := by rw [h3]; group
        _ = x * l := by group
    · rintro ⟨-, h1⟩
      apply Subtype.ext
      change b x = 1
      refine d321r_eq_of_conj_eq hcen (hbL x hx) L.one_mem fun l hl => ?_
      rw [← hb x hx l hl]
      calc x * l * x⁻¹ = l * x * x⁻¹ := by rw [h1 l hl]
        _ = 1 * l * (1 : MulAut W)⁻¹ := by group
  have hcomm : ∀ y ∈ ψ.range, ∀ z ∈ ψ.range, y * z = z * y := by
    rintro _ ⟨a₁, rfl⟩ _ ⟨a₂, rfl⟩
    have h : a₁ * a₂ = a₂ * a₁ := Subtype.ext (hA.1 _ a₁.2 _ a₂.2)
    rw [← map_mul, ← map_mul, h]
  have hsq : ∀ y ∈ ψ.range, y ^ 2 = 1 := by
    rintro _ ⟨a, rfl⟩
    have h : a ^ 2 = 1 := Subtype.ext (hA.2 _ a.2)
    rw [← map_pow, h, map_one]
  have hrange := d321r_card_elemAbelian hpsl ψ.range hcomm hsq
  have hcard := Subgroup.card_ker_mul_card_range ψ
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at hcard
  have hpos1 : Nat.card ↥(A ⊓ Subgroup.centralizer (L : Set (MulAut W))) ≠ 0 :=
    Nat.card_pos.ne'
  have hpos2 : Nat.card ψ.range ≠ 0 := Nat.card_pos.ne'
  have hv2 : padicValNat 2 (Nat.card ψ.range) ≤ 2 := by
    rcases hrange with h | h | h <;> rw [h]
    · simp
    · simp
    · have : padicValNat 2 (2 ^ 2) = 2 := padicValNat.prime_pow 2
      norm_num at this
      omega
  unfold rk
  rw [← hcard, padicValNat.mul hpos1 hpos2]
  omega

theorem d321r_relIndex_realizesVia {W : Type} [CommGroup W] {D : FFModel}
    {L : Subgroup (MulAut W)} {V Z : Subgroup W} {π : D.Gam →* ↥L}
    (h : D.RealizesVia L V Z π) :
    Z.relIndex V = Nat.card (↥D.sec ⧸ D.ker.subgroupOf D.sec) := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  have hker : β.ker = Z.subgroupOf V := by
    ext u
    rw [MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
  unfold Subgroup.relIndex
  rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hβs, Subgroup.card_top]

theorem d321r_card_natural_section {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) :
    Nat.card (↥(FFModel.nat Γ).sec ⧸ (FFModel.nat Γ).ker.subgroupOf (FFModel.nat Γ).sec) =
      Nat.card (ι → K) := by
  change Nat.card (↥(⊤ : Subgroup (Multiplicative (ι → K))) ⧸
    (⊥ : Subgroup (Multiplicative (ι → K))).subgroupOf ⊤) = Nat.card (ι → K)
  exact Nat.card_congr (B5.natQuotEquiv (Multiplicative (ι → K))).toEquiv

theorem d321r_relIndex_sup_family {W : Type} [CommGroup W] {ι : Type} [DecidableEq ι]
    {I : ι → Subgroup W} {Z : Subgroup W} {c : ℕ} (hZ : ∀ i, Z ≤ I i)
    (hc : ∀ i, Z.relIndex (I i) = c)
    (hind : ∀ i, I i ⊓ (Z ⊔ ⨆ (j : ι) (_ : j ≠ i), I j) = Z) (s : Finset ι) :
    Z.relIndex (Z ⊔ ⨆ i ∈ s, I i) = c ^ s.card := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hS : Z ⊔ ⨆ i ∈ insert a s, I i = (Z ⊔ ⨆ i ∈ s, I i) ⊔ I a := by
      rw [Finset.iSup_insert, sup_left_comm, sup_comm (I a)]
    have hZS : Z ≤ Z ⊔ ⨆ i ∈ s, I i := le_sup_left
    have hSle : (Z ⊔ ⨆ i ∈ s, I i) ≤ Z ⊔ ⨆ (j : ι) (_ : j ≠ a), I j := by
      refine sup_le_sup_left (iSup₂_le fun i hi => ?_) Z
      exact le_iSup₂_of_le i (fun h => ha (by rw [← h]; exact hi)) le_rfl
    have hinf : (Z ⊔ ⨆ i ∈ s, I i) ⊓ I a = Z := by
      refine le_antisymm ?_ (le_inf hZS (hZ a))
      calc (Z ⊔ ⨆ i ∈ s, I i) ⊓ I a = I a ⊓ (Z ⊔ ⨆ i ∈ s, I i) := inf_comm _ _
        _ ≤ I a ⊓ (Z ⊔ ⨆ (j : ι) (_ : j ≠ a), I j) := inf_le_inf_left _ hSle
        _ = Z := hind a
    rw [hS, ← Subgroup.relIndex_mul_relIndex Z (Z ⊔ ⨆ i ∈ s, I i) _ hZS le_sup_left, ih,
      Subgroup.relIndex_sup_left, ← Subgroup.inf_relIndex_right, hinf, hc a,
      Finset.card_insert_of_notMem ha, pow_succ]

theorem d321x_rk_sec {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hds : DirectSumOfCopies L U Z
      (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))) 4) :
    rk (Sec U Z) = 12 := by
  obtain ⟨I, π, hZI, hind, hU, hreal⟩ := hds
  have hc : ∀ i, Z.relIndex (I i) = 8 := fun i => by
    rw [d321r_relIndex_realizesVia (hreal i), d321r_card_natural_section, Nat.card_fun,
      Nat.card_fin, Nat.card_zmod]
    norm_num
  have key := d321r_relIndex_sup_family hZI hc hind Finset.univ
  simp only [Finset.mem_univ, iSup_pos, Finset.card_univ, Fintype.card_fin] at key
  have h : Nat.card (Sec U Z) = 8 ^ 4 := by
    rw [← hU]
    exact key
  have h2 : (8 : ℕ) ^ 4 = 2 ^ 12 := by norm_num
  unfold rk
  rw [h, h2, padicValNat.prime_pow]

end CFSG.Quasithin
