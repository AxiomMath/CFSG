module

public import CFSG.Quasithin.Vol2.Ch9KGFFG24Lang
public import CFSG.Quasithin.Background.KGRankG24
public import CFSG.LieType.Chevalley.ChevalleySplitBN
public import CFSG.LieType.Ree.Endo

public section

namespace CFSG.Quasithin.H13.Ch9.KGFF.G24

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open scoped IsMulCommutative

section Semidirect

variable {N G : Type*} [Group N] [Group G] {φ : G →* MulAut N}

@[expose] def semidirectSub (S : Subgroup N) (hS : ∀ g, ∀ x ∈ S, φ g x ∈ S) :
    Subgroup (SemidirectProduct N G φ) where
  carrier := {a | a.left ∈ S}
  mul_mem' ha hb := S.mul_mem ha (hS _ _ hb)
  one_mem' := S.one_mem
  inv_mem' ha := hS _ _ (S.inv_mem ha)

theorem mem_semidirectSub {S : Subgroup N} {hS : ∀ g, ∀ x ∈ S, φ g x ∈ S}
    {a : SemidirectProduct N G φ} : a ∈ semidirectSub S hS ↔ a.left ∈ S :=
  Iff.rfl

theorem card_semidirectSub (S : Subgroup N) (hS : ∀ g, ∀ x ∈ S, φ g x ∈ S) :
    Nat.card (semidirectSub S hS) = Nat.card S * Nat.card G := by
  rw [← Nat.card_prod]
  exact Nat.card_congr
    { toFun := fun a => (⟨a.1.left, a.2⟩, a.1.right)
      invFun := fun p => ⟨⟨p.1.1, p.2⟩, p.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_semidirectProduct :
    Nat.card (SemidirectProduct N G φ) = Nat.card N * Nat.card G := by
  rw [← Nat.card_prod]
  exact Nat.card_congr SemidirectProduct.equivProd

end Semidirect

section Sylow

variable {X : Type*} [Group X] [Finite X]

theorem exists_conj_le_of_semidirect (β : MulAut X) (hββ : β * β = 1) {U E : Subgroup X}
    (hU : IsPGroup 2 U) (hUi : ¬ 2 ∣ U.index) (hβU : ∀ x ∈ U, β x ∈ U)
    (hE : ∀ x ∈ E, x * x = 1) (hβE : ∀ x ∈ E, β x = x) :
    ∃ k : X, (∀ x ∈ E, k * x * k⁻¹ ∈ U) ∧ k * (β k)⁻¹ ∈ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB : ∀ b ∈ Subgroup.zpowers β, b = 1 ∨ b = β := by
    intro b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · exact Or.inl (by rw [zpow_mul, zpow_two, hββ, one_zpow])
    · exact Or.inr (by rw [zpow_add_one, zpow_mul, zpow_two, hββ, one_zpow, one_mul])
  let φ : ↥(Subgroup.zpowers β) →* MulAut X := (Subgroup.zpowers β).subtype
  have hφ : ∀ b x, φ b x = x ∨ φ b x = β x := by
    intro b x
    rcases hB b b.2 with h | h
    · left
      change (b : MulAut X) x = x
      rw [h]
      rfl
    · right
      change (b : MulAut X) x = β x
      rw [h]
  have hφE : ∀ b, ∀ x ∈ E, φ b x = x := fun b x hx =>
    (hφ b x).elim id fun h => h.trans (hβE x hx)
  have hUS : ∀ b, ∀ x ∈ U, φ b x ∈ U := by
    intro b x hx
    rcases hφ b x with h | h
    · rw [h]
      exact hx
    · rw [h]
      exact hβU x hx
  have hES : ∀ b, ∀ x ∈ E, φ b x ∈ E := fun b x hx => by
    rw [hφE b x hx]
    exact hx
  let UU := semidirectSub (φ := φ) U hUS
  let EE := semidirectSub (φ := φ) E hES
  have : Finite (MulAut X) :=
    Finite.of_injective (fun α : MulAut X => (α : X → X)) DFunLike.coe_injective
  have : Finite (SemidirectProduct _ _ φ) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  have hBc : Nat.card ↥(Subgroup.zpowers β) = 1 ∨ Nat.card ↥(Subgroup.zpowers β) = 2 := by
    rw [Nat.card_zpowers]
    exact (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hββ))
  have hUUc : Nat.card UU = Nat.card U * Nat.card ↥(Subgroup.zpowers β) :=
    card_semidirectSub _ _
  obtain ⟨n, hn⟩ := hU.exists_card_eq
  have hUUp : IsPGroup 2 UU := by
    rcases hBc with h | h
    · exact IsPGroup.of_card (n := n) (by rw [hUUc, hn, h, mul_one])
    · exact IsPGroup.of_card (n := n + 1) (by rw [hUUc, hn, h, pow_succ])
  have hUUi : ¬ 2 ∣ UU.index := by
    have h1 := UU.index_mul_card
    have h2 := U.index_mul_card
    rw [hUUc, card_semidirectProduct] at h1
    have hpos : 0 < Nat.card U * Nat.card ↥(Subgroup.zpowers β) :=
      Nat.mul_pos Nat.card_pos Nat.card_pos
    have he : UU.index = U.index := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      rw [h1, ← h2, mul_assoc]
    rw [he]
    exact hUi
  have hEEp : IsPGroup 2 EE := by
    intro y
    refine ⟨1, Subtype.ext ?_⟩
    have hyl : (y : SemidirectProduct _ _ φ).left ∈ E := y.2
    rw [pow_one, sq, Subgroup.coe_mul, Subgroup.coe_one]
    apply SemidirectProduct.ext
    · rw [SemidirectProduct.mul_left, hφE _ _ hyl, SemidirectProduct.one_left]
      exact hE _ hyl
    · rw [SemidirectProduct.mul_right, SemidirectProduct.one_right]
      apply Subtype.ext
      rcases hB _ (y : SemidirectProduct _ _ φ).right.2 with h | h
      · rw [Subgroup.coe_mul, h, mul_one, Subgroup.coe_one]
      · rw [Subgroup.coe_mul, h, hββ, Subgroup.coe_one]
  set P0 : Sylow 2 (SemidirectProduct _ _ φ) := hUUp.toSylow hUUi with hP0
  obtain ⟨Q, hQ⟩ := hEEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SemidirectProduct _ _ φ) Q P0
  have hconj : ∀ y ∈ EE, g * y * g⁻¹ ∈ UU := by
    intro y hy
    have hmem : MulAut.conj g • y ∈ (P0 : Subgroup (SemidirectProduct _ _ φ)) := by
      rw [← hg, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ (hQ hy)
    rw [hP0, IsPGroup.toSylow_coe, MulAut.smul_def, MulAut.conj_apply] at hmem
    exact hmem
  have hgk : g * (SemidirectProduct.inr g.right)⁻¹ = SemidirectProduct.inl g.left := by
    ext <;> simp
  have hinrE : ∀ r, (SemidirectProduct.inr r : SemidirectProduct _ _ φ) ∈ EE := fun r =>
    mem_semidirectSub.2 (by rw [SemidirectProduct.left_inr]; exact E.one_mem)
  have hconj' : ∀ y ∈ EE, SemidirectProduct.inl g.left * y *
      (SemidirectProduct.inl g.left)⁻¹ ∈ UU := by
    intro y hy
    rw [← hgk]
    have h := hconj _ (EE.mul_mem (EE.mul_mem (EE.inv_mem (hinrE g.right)) hy) (hinrE g.right))
    convert h using 1
    group
  refine ⟨g.left, fun x hx => ?_, ?_⟩
  · have h : (SemidirectProduct.inl g.left * SemidirectProduct.inl x *
        (SemidirectProduct.inl g.left)⁻¹ : SemidirectProduct _ _ φ).left ∈ U :=
      hconj' _ (mem_semidirectSub.2 (by rw [SemidirectProduct.left_inl]; exact hx))
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      SemidirectProduct.inv_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      inv_one, map_one, MulAut.one_apply, mul_one] at h
    exact h
  · have hβB : β ∈ Subgroup.zpowers β := Subgroup.mem_zpowers β
    have h : (SemidirectProduct.inl g.left * SemidirectProduct.inr ⟨β, hβB⟩ *
        (SemidirectProduct.inl g.left)⁻¹ : SemidirectProduct _ _ φ).left ∈ U :=
      hconj' _ (hinrE ⟨β, hβB⟩)
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      SemidirectProduct.inv_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      SemidirectProduct.left_inr, SemidirectProduct.right_inr, inv_one, map_one,
      MulAut.one_apply, mul_one, one_mul] at h
    rw [← map_inv]
    exact h

end Sylow

section Frob

variable {K : Type} [Field K]

theorem card_le_of_conj_fixed
    (hK : Nat.card K = 4) (δ : K →+* K) (hδ : ∀ c, δ c = c ^ 2)
    {E : Subgroup ↥(adjointGroup .G2 K)} (hE : CFSG.Open.IsElemAbelian 2 E) {k : ModGL .G2 K}
    (hk : ∀ x ∈ E, k * (x : ModGL .G2 K) * k⁻¹ ∈ posUnipotent .G2 K ∧
      Units.map (entrywiseHom δ) (k * (x : ModGL .G2 K) * k⁻¹) = k * (x : ModGL .G2 K) * k⁻¹) :
    Nat.card E ≤ 2 ^ 3 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : CharP K 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  set E'' : Subgroup (ModGL .G2 K) :=
    (E.map (adjointGroup .G2 K).subtype).map (MulAut.conj k).toMonoidHom with hE''
  have hE''U : E'' ≤ posUnipotent .G2 K := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact (hk x hx).1
  have hcomm : ∀ x ∈ E'', ∀ y ∈ E'', x * y = y * x := by
    have := hE.1
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩ _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hxy : x * y = y * x := (congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥E) ⟨y, hy⟩) :)
    simp only [MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype, ← Subgroup.coe_mul, ← map_mul,
      hxy]
  have hsq : ∀ x ∈ E'', x * x = 1 := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hx2 : x * x = 1 := by rw [← sq]; exact hE.2 x hx
    simp only [MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype, ← Subgroup.coe_mul, ← map_mul, hx2,
      map_one, Subgroup.coe_one]
  have hS : ∀ A B C D E' F : K, g2N A B C D E' F ∈ E'' →
      A ∈ {c : K | c ^ 2 = c} ∧ B ∈ {c : K | c ^ 2 = c} ∧ C ∈ {c : K | c ^ 2 = c} ∧
        D ∈ {c : K | c ^ 2 = c} ∧ E' ∈ {c : K | c ^ 2 = c} ∧ F ∈ {c : K | c ^ 2 = c} := by
    rintro A B C D E' F ⟨_, ⟨x, hx, rfl⟩, hxe⟩
    have hfix : Units.map (entrywiseHom δ) (g2N A B C D E' F) = g2N A B C D E' F := by
      rw [← hxe]
      exact (hk x hx).2
    rw [units_map_entrywiseHom_g2N] at hfix
    simp only [hδ] at hfix
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := g2N_injective hfix
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  have h := card_le_cube (S := {c : K | c ^ 2 = c}) hE''U hcomm hsq hS
  have hcard : Nat.card E'' = Nat.card E := by
    rw [hE'', Subgroup.card_map_of_injective (MulAut.conj k).injective,
      Subgroup.card_map_of_injective (adjointGroup .G2 K).subtype_injective]
  have hS2 : Nat.card ↥{c : K | c ^ 2 = c} = 2 := card_sq_eq_self hK
  rw [hcard, hS2] at h
  exact h

theorem card_le_of_entrywise_fixed
    (hK : Nat.card K = 4) (δ : K →+* K) (hδ : ∀ c, δ c = c ^ 2)
    {E : Subgroup ↥(adjointGroup .G2 K)} (hE : CFSG.Open.IsElemAbelian 2 E)
    (hσE : ∀ x ∈ E, Units.map (entrywiseHom δ) (x : ModGL .G2 K) = (x : ModGL .G2 K)) :
    Nat.card E ≤ 2 ^ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  have := finite_modGL (τ := .G2) (K := K)
  set σ : ModGL .G2 K →* ModGL .G2 K := Units.map (entrywiseHom δ) with hσdef
  have hσσ : ∀ x, σ (σ x) = x := units_map_entrywiseHom_sq_involutive hK δ hδ
  have hσX : ∀ x ∈ adjointGroup .G2 K, σ x ∈ adjointGroup .G2 K := fun x hx =>
    CFSG.LieType.Ree.entrywiseGL_mem δ hx
  have hσU : ∀ x ∈ posUnipotent .G2 K, σ x ∈ posUnipotent .G2 K := by
    intro x hx
    obtain ⟨A, B, C, D, E', F, rfl⟩ := exists_g2N_of_mem_posUnipotent hx
    rw [hσdef, units_map_entrywiseHom_g2N]
    exact g2N_mem_posUnipotent _ _ _ _ _ _
  let β : MulAut ↥(adjointGroup .G2 K) :=
    { toFun := fun x => ⟨σ x, hσX x x.2⟩
      invFun := fun x => ⟨σ x, hσX x x.2⟩
      left_inv := fun x => Subtype.ext (hσσ x)
      right_inv := fun x => Subtype.ext (hσσ x)
      map_mul' := fun x y => Subtype.ext (map_mul σ (x : ModGL .G2 K) (y : ModGL .G2 K)) }
  have hβ : ∀ x, ((β x : ↥(adjointGroup .G2 K)) : ModGL .G2 K) = σ x := fun _ => rfl
  have hββ : β * β = 1 := MulEquiv.ext fun x => Subtype.ext (hσσ x)
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index 2
    (posUnipotent_le_adjointGroup (τ := .G2) (K := K)) card_posUnipotent
  obtain ⟨k, hkE, hkU⟩ := exists_conj_le_of_semidirect β hββ hUp hUi
    (fun x hx => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      rw [hβ]
      exact hσU _ hx)
    (fun x hx => by rw [← sq]; exact hE.2 x hx)
    (fun x hx => Subtype.ext ((hβ x).trans (hσE x hx)))
  have hu : (k : ModGL .G2 K) * (σ k)⁻¹ ∈ posUnipotent .G2 K := by
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, hβ] at hkU
    exact hkU
  have hu1 : (k : ModGL .G2 K) * (σ k)⁻¹ * σ ((k : ModGL .G2 K) * (σ k)⁻¹) = 1 := by
    rw [map_mul, map_inv, hσσ]
    group
  obtain ⟨v, hvU, hv⟩ := exists_eq_mul_inv_of_mul_entrywise_eq_one hK δ hδ hu hu1
  rw [← hσdef] at hv
  have hk'σ : σ (v⁻¹ * k) = v⁻¹ * k := by
    rw [map_mul, map_inv]
    calc (σ v)⁻¹ * σ ↑k = v⁻¹ * (v * (σ v)⁻¹) * σ ↑k := by group
      _ = v⁻¹ * (↑k * (σ ↑k)⁻¹) * σ ↑k := by rw [← hv]
      _ = v⁻¹ * ↑k := by group
  refine card_le_of_conj_fixed hK δ hδ hE (k := v⁻¹ * k) fun x hx => ⟨?_, ?_⟩
  · have h := hkE x hx
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at h
    have he : v⁻¹ * ↑k * ↑x * (v⁻¹ * ↑k)⁻¹ = v⁻¹ * (↑k * ↑x * (↑k)⁻¹) * v := by group
    rw [he]
    exact (posUnipotent .G2 K).mul_mem
      ((posUnipotent .G2 K).mul_mem ((posUnipotent .G2 K).inv_mem hvU) h) hvU
  · change σ (v⁻¹ * ↑k * ↑x * (v⁻¹ * ↑k)⁻¹) = v⁻¹ * ↑k * ↑x * (v⁻¹ * ↑k)⁻¹
    rw [map_mul, map_mul, map_inv, hk'σ, hσE x hx]

end Frob

end CFSG.Quasithin.H13.Ch9.KGFF.G24

namespace CFSG.Quasithin

theorem rankG24FrobCentFact_holds :
    RankG24FrobCentFact := fun _ _ hK δ hδ _ hE hσE =>
  H13.Ch9.KGFF.G24.card_le_of_entrywise_fixed hK δ hδ hE hσE

end CFSG.Quasithin
