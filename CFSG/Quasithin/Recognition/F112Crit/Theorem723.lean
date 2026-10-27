module

public import CFSG.Quasithin.Recognition.F112Crit.Lemma715
public import CFSG.Quasithin.Recognition.F112Crit.PermBound
public import CFSG.Quasithin.Recognition.F112Crit.PermBound.Fixed
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Quasithin.Background.F1Lemma10
public import CFSG.Quasithin.Background.F2Equiv

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

open CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)

variable {G₀ G₁ G₂ T Z : Subgroup G}

structure BenderLocal (μ : CosetGeom G₀ G₁ G₂) (L : Subgroup G) : Prop where
  le_stab : L ≤ stab μ
  normal : stab μ ≤ Subgroup.normalizer (L : Set G)
  odd_gen : L ≤ Subgroup.closure {h : G | h ∈ L ∧ Odd (orderOf h)}
  trans : ∀ δ ∈ nbrs μ, ∀ δ' ∈ nbrs μ, ∃ g : ↥G₀, (g : G) ∈ L ∧ g • δ = δ'
  unipotent : ∀ δ ∈ nbrs μ, ∃ U : Subgroup G, U ≤ L ∧ IsPGroup 2 U ∧ U ≤ stab δ ∧
    (∀ ε ∈ nbrs μ, ∀ ε' ∈ nbrs μ, ε ≠ δ → ε' ≠ δ → ∃ g : ↥G₀, (g : G) ∈ U ∧ g • ε = ε') ∧
    (∀ g : ↥G₀, (g : G) ∈ U → ∀ ε ∈ nbrs μ, ε ≠ δ → g • ε = ε → (g : G) ∈ ballStab 1 μ) ∧
    stab μ ⊓ stab δ ≤ Subgroup.normalizer ((U ⊔ ballStab 1 μ : Subgroup G) : Set G)

theorem BenderLocal.smul {μ : CosetGeom G₀ G₁ G₂} {L : Subgroup G} (hL : BenderLocal μ L)
    (g : ↥G₀) : BenderLocal (g • μ) (conjSub (g : G) L) where
  le_stab := by
    rw [CosetGeom.stab_smul]
    exact conjSub_mono _ hL.le_stab
  normal := by
    rw [CosetGeom.stab_smul]
    exact conjSub_le_normalizer hL.normal
  odd_gen := by
    refine (conjSub_mono (g : G) hL.odd_gen).trans ?_
    rw [conjSub_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨x, ⟨hxL, hxodd⟩, rfl⟩
    refine ⟨mul_mem_conjSub hxL, ?_⟩
    have h := orderOf_injective (MulAut.conj (g : G)).toMonoidHom
      (MulAut.conj (g : G)).injective x
    have e : (MulAut.conj (g : G)).toMonoidHom x = (g : G) * x * (g : G)⁻¹ := rfl
    rw [e] at h
    rw [h]
    exact hxodd
  trans := by
    intro δ hδ δ' hδ'
    obtain ⟨a, rfl⟩ : ∃ a, δ = g • a := ⟨g⁻¹ • δ, by simp⟩
    obtain ⟨b, rfl⟩ : ∃ b, δ' = g • b := ⟨g⁻¹ • δ', by simp⟩
    have ha : a ∈ nbrs μ := (CosetGeom.smul_adj g).mp hδ
    have hb : b ∈ nbrs μ := (CosetGeom.smul_adj g).mp hδ'
    obtain ⟨k, hkL, hk⟩ := hL.trans a ha b hb
    refine ⟨g * k * g⁻¹, ?_, ?_⟩
    · show (g : G) * (k : G) * (g : G)⁻¹ ∈ conjSub (g : G) L
      exact mul_mem_conjSub hkL
    · rw [mul_smul, mul_smul, inv_smul_smul, hk]
  unipotent := by
    intro δ hδ
    obtain ⟨a, rfl⟩ : ∃ a, δ = g • a := ⟨g⁻¹ • δ, by simp⟩
    have ha : a ∈ nbrs μ := (CosetGeom.smul_adj g).mp hδ
    obtain ⟨U, hUL, hU2, hUδ, hUtr, hUreg, hUn⟩ := hL.unipotent a ha
    refine ⟨conjSub (g : G) U, conjSub_mono _ hUL, F7.isPGroup_conjSub hU2, ?_, ?_, ?_, ?_⟩
    · rw [CosetGeom.stab_smul]
      exact conjSub_mono _ hUδ
    · intro ε hε ε' hε' hne hne'
      obtain ⟨e, rfl⟩ : ∃ e, ε = g • e := ⟨g⁻¹ • ε, by simp⟩
      obtain ⟨e', rfl⟩ : ∃ e', ε' = g • e' := ⟨g⁻¹ • ε', by simp⟩
      have he : e ∈ nbrs μ := (CosetGeom.smul_adj g).mp hε
      have he' : e' ∈ nbrs μ := (CosetGeom.smul_adj g).mp hε'
      obtain ⟨k, hkU, hk⟩ :=
        hUtr e he e' he' (fun h => hne (by rw [h])) (fun h => hne' (by rw [h]))
      refine ⟨g * k * g⁻¹, ?_, ?_⟩
      · show (g : G) * (k : G) * (g : G)⁻¹ ∈ conjSub (g : G) U
        exact mul_mem_conjSub hkU
      · rw [mul_smul, mul_smul, inv_smul_smul, hk]
    · intro k hk ε hε hne hfix
      obtain ⟨e, rfl⟩ : ∃ e, ε = g • e := ⟨g⁻¹ • ε, by simp⟩
      have he : e ∈ nbrs μ := (CosetGeom.smul_adj g).mp hε
      rw [CosetGeom.ballStab_smul, mem_conjSub]
      have hk' : ((g⁻¹ * k * g : ↥G₀) : G) ∈ U := mem_conjSub.mp hk
      refine hUreg (g⁻¹ * k * g) hk' e he (fun h => hne (by rw [h])) ?_
      have h1 : k • g • e = g • e := hfix
      calc (g⁻¹ * k * g) • e = g⁻¹ • (k • (g • e)) := by simp [mul_smul]
        _ = g⁻¹ • (g • e) := by rw [h1]
        _ = e := inv_smul_smul g e
    · rw [CosetGeom.stab_smul, CosetGeom.stab_smul, ← conjSub_inf, CosetGeom.ballStab_smul,
        ← conjSub_sup]
      exact conjSub_le_normalizer hUn

variable [Finite G]

namespace T723

@[expose] def stabToG₀ (α : CosetGeom G₀ G₁ G₂) : ↥(stab α) →* ↥G₀ :=
  Subgroup.inclusion (CosetGeom.stab_le α)

theorem stabToG₀_smul_mem (α : CosetGeom G₀ G₁ G₂) (h : ↥(stab α)) {δ : CosetGeom G₀ G₁ G₂}
    (hδ : δ ∈ nbrs α) : stabToG₀ α h • δ ∈ nbrs α :=
  IsLocalReg.smul_mem_nbrs (g := stabToG₀ α h) hδ h.2

scoped instance instMulActionNbrs (α : CosetGeom G₀ G₁ G₂) : MulAction ↥(stab α) ↥(nbrs α) where
  smul h δ := ⟨stabToG₀ α h • (δ : CosetGeom G₀ G₁ G₂), stabToG₀_smul_mem α h δ.2⟩
  one_smul δ := Subtype.ext (by
    show stabToG₀ α 1 • (δ : CosetGeom G₀ G₁ G₂) = δ
    rw [map_one, one_smul])
  mul_smul h k δ := Subtype.ext (by
    show stabToG₀ α (h * k) • (δ : CosetGeom G₀ G₁ G₂) =
      stabToG₀ α h • (stabToG₀ α k • (δ : CosetGeom G₀ G₁ G₂))
    rw [map_mul, mul_smul])

scoped instance instDistribMulActionAdditive (α : CosetGeom G₀ G₁ G₂) (W : Subgroup G)
    [hW : Fact (stab α ≤ Subgroup.normalizer (W : Set G))] :
    DistribMulAction ↥(stab α) (Additive ↥W) where
  smul h m := ConjAut.conjAut W (h : G) (hW.out h.2) m
  one_smul m := by
    apply (ConjAut.eq_iff_val W).mpr
    show ((1 : ↥(stab α)) : G) * _ * ((1 : ↥(stab α)) : G)⁻¹ = _
    simp
  mul_smul h k m := by
    apply (ConjAut.eq_iff_val W).mpr
    show ((h * k : ↥(stab α)) : G) * _ * ((h * k : ↥(stab α)) : G)⁻¹ =
      (h : G) * ((k : G) * _ * (k : G)⁻¹) * (h : G)⁻¹
    simp [mul_assoc]
  smul_zero h := map_zero _
  smul_add h m n := map_add _ m n

theorem smul_eq_of_mem_ballStab (α : CosetGeom G₀ G₁ G₂) {h : ↥(stab α)}
    (hh : (h : G) ∈ ballStab 1 α) (ω : ↥(nbrs α)) : h • ω = ω :=
  Subtype.ext (CosetGeom.smul_eq_of_mem_stab (g := stabToG₀ α h)
    (CosetGeom.mem_ballStab.mp hh ω.1 (CosetGeom.dist_eq_one_iff_adj.mpr ω.2).le))

theorem mem_ballStab_of_forall_smul_eq (hG : G₀ = G₁ ⊔ G₂) (α : CosetGeom G₀ G₁ G₂)
    {h : ↥(stab α)} (hfix : ∀ ω : ↥(nbrs α), h • ω = ω) : (h : G) ∈ ballStab 1 α := by
  refine CosetGeom.mem_ballStab.mpr fun δ hδ => ?_
  rcases (CosetGeom.dist_le_one_iff hG).mp hδ with rfl | hadj
  · exact h.2
  · exact CosetGeom.mem_stab_of_smul_eq (g := stabToG₀ α h)
      (congrArg Subtype.val (hfix ⟨δ, hadj⟩))

theorem exists_unipotentH {α : CosetGeom G₀ G₁ G₂} {L : Subgroup G} (hL : BenderLocal α L)
    {β : CosetGeom G₀ G₁ G₂} (hβ : β ∈ nbrs α) :
    ∃ U : Subgroup ↥(stab α), U ≤ L.subgroupOf (stab α) ∧ IsPGroup 2 U ∧
      (∀ u ∈ U, u • (⟨β, hβ⟩ : ↥(nbrs α)) = ⟨β, hβ⟩) ∧
      (∀ μ ν : ↥(nbrs α), μ ≠ ⟨β, hβ⟩ → ν ≠ ⟨β, hβ⟩ → ∃ u ∈ U, u • μ = ν) ∧
      (∀ u ∈ U, ∀ μ : ↥(nbrs α), μ ≠ ⟨β, hβ⟩ → u • μ = μ → ∀ ω : ↥(nbrs α), u • ω = ω) ∧
      (∀ z : ↥(stab α), (z : G) ∈ stab β → ∀ u ∈ U,
        ∃ u' ∈ U, ∀ ω : ↥(nbrs α), (z * u * z⁻¹) • ω = u' • ω) := by
  obtain ⟨U, hUL, hU2, hUβ, htr, hreg, hnorm⟩ := hL.unipotent β hβ
  have hUα : U ≤ stab α := hUL.trans hL.le_stab
  refine ⟨U.subgroupOf (stab α), fun u hu => hUL hu, hU2.comap_subtype, ?_, ?_, ?_, ?_⟩
  · intro u hu
    exact Subtype.ext (CosetGeom.smul_eq_of_mem_stab (g := stabToG₀ α u) (hUβ hu))
  · intro μ ν hμ hν
    obtain ⟨g, hgU, hg⟩ := htr μ.1 μ.2 ν.1 ν.2 (fun h => hμ (Subtype.ext h))
      (fun h => hν (Subtype.ext h))
    exact ⟨⟨(g : G), hUα hgU⟩, hgU, Subtype.ext hg⟩
  · intro u hu μ hμ hfix ω
    have h1 := hreg (stabToG₀ α u) hu μ.1 μ.2 (fun h => hμ (Subtype.ext h))
      (congrArg Subtype.val hfix)
    exact smul_eq_of_mem_ballStab α h1 ω
  · intro z hz u hu
    have hzn : (z : G) ∈ Subgroup.normalizer ((U ⊔ ballStab 1 α : Subgroup G) : Set G) :=
      hnorm ⟨z.2, hz⟩
    have hmem : (z : G) * u * (z : G)⁻¹ ∈ U ⊔ ballStab 1 α :=
      (Subgroup.mem_normalizer_iff.mp hzn (u : G)).mp (Subgroup.mem_sup_left hu)
    rw [sup_comm] at hmem
    obtain ⟨n, hn, y, hy, hny⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
      (hUα.trans (CosetGeom.le_normalizer_ballStab 1 α))).mp hmem
    refine ⟨⟨y, hUα hy⟩, hy, fun ω => ?_⟩
    have e : z * u * z⁻¹ =
        (⟨n, CosetGeom.ballStab_le_stab 1 α hn⟩ : ↥(stab α)) * ⟨y, hUα hy⟩ :=
      Subtype.ext hny
    rw [e, mul_smul, smul_eq_of_mem_ballStab α hn]

theorem exists_mem_smul_eq {α : CosetGeom G₀ G₁ G₂} {L : Subgroup G} (hL : BenderLocal α L)
    (μ ν : ↥(nbrs α)) : ∃ l ∈ L.subgroupOf (stab α), l • μ = ν := by
  obtain ⟨g, hgL, hg⟩ := hL.trans μ.1 μ.2 ν.1 ν.2
  exact ⟨⟨(g : G), hL.le_stab hgL⟩, hgL, Subtype.ext hg⟩

theorem card_fixedBy_nbrs (α : CosetGeom G₀ G₁ G₂) (z : ↥(stab α)) :
    Nat.card (MulAction.fixedBy ↥(nbrs α) z) =
      Nat.card {δ | δ ∈ nbrs α ∧ (z : G) ∈ stab δ} := by
  refine Nat.card_congr
    { toFun := fun x => ⟨x.1.1, x.1.2, CosetGeom.mem_stab_of_smul_eq (g := stabToG₀ α z)
        (congrArg Subtype.val (MulAction.mem_fixedBy.mp x.2))⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, MulAction.mem_fixedBy.mpr
        (Subtype.ext (CosetGeom.smul_eq_of_mem_stab (g := stabToG₀ α z) y.2.2))⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

theorem fixed_bound (hG : G₀ = G₁ ⊔ G₂) {α : CosetGeom G₀ G₁ G₂} {L : Subgroup G}
    (hL : BenderLocal α L) {β : CosetGeom G₀ G₁ G₂} (hβ : β ∈ nbrs α) {z : G} (hzα : z ∈ stab α)
    (hzβ : z ∈ stab β) (hzn : z ∉ ballStab 1 α) :
    2 * (Nat.card {δ | δ ∈ nbrs α ∧ z ∈ stab δ} - 1) ≤ Nat.card (nbrs α) - 1 := by
  obtain ⟨U, -, -, hUfix, hUtrans, hUreg, hUnorm⟩ := exists_unipotentH hL hβ
  rw [← card_fixedBy_nbrs α ⟨z, hzα⟩]
  refine PermBound.two_mul_card_fixedBy_le (ω₀ := (⟨β, hβ⟩ : ↥(nbrs α))) (U := U) hUfix hUtrans
    hUreg ?_ (hUnorm ⟨z, hzα⟩ hzβ) ?_
  · exact Subtype.ext (CosetGeom.smul_eq_of_mem_stab (g := stabToG₀ α ⟨z, hzα⟩) hzβ)
  · by_contra hcon
    push Not at hcon
    exact hzn (mem_ballStab_of_forall_smul_eq hG α (h := ⟨z, hzα⟩) hcon)

theorem card_form {α : CosetGeom G₀ G₁ G₂} {L : Subgroup G} (hL : BenderLocal α L)
    {β : CosetGeom G₀ G₁ G₂} (hβ : β ∈ nbrs α) (hne : 1 < Nat.card (nbrs α)) :
    ∃ u : ℕ, Nat.card (nbrs α) = 2 ^ u + 1 := by
  obtain ⟨U, -, hU2, hUfix, hUtrans, -, -⟩ := exists_unipotentH hL hβ
  haveI : Nontrivial ↥(nbrs α) := Finite.one_lt_card_iff_nontrivial.mp hne
  obtain ⟨μ, hμ⟩ := exists_ne (⟨β, hβ⟩ : ↥(nbrs α))
  exact PermBound.exists_card_eq_two_pow_add_one hU2 hUfix hUtrans ⟨μ, hμ⟩

theorem subgroupOf_odd_gen {K L : Subgroup G} (hLK : L ≤ K)
    (h : L ≤ Subgroup.closure {x : G | x ∈ L ∧ Odd (orderOf x)}) :
    L.subgroupOf K ≤ Subgroup.closure {x : ↥K | x ∈ L.subgroupOf K ∧ Odd (orderOf x)} := by
  intro x hx
  have hx1 : (x : G) ∈ Subgroup.closure {x : G | x ∈ L ∧ Odd (orderOf x)} := h hx
  have e : K.subtype '' {x : ↥K | x ∈ L.subgroupOf K ∧ Odd (orderOf x)} =
      {x : G | x ∈ L ∧ Odd (orderOf x)} := by
    ext y
    constructor
    · rintro ⟨k, ⟨hkL, hodd⟩, rfl⟩
      exact ⟨hkL, by rwa [Subgroup.coe_subtype, Subgroup.orderOf_coe]⟩
    · rintro ⟨hyL, hodd⟩
      exact ⟨⟨y, hLK hyL⟩, ⟨hyL, by rwa [Subgroup.orderOf_mk]⟩, rfl⟩
  rw [← e, ← MonoidHom.map_closure] at hx1
  obtain ⟨y, hy, hyx⟩ := hx1
  have hyx' : y = x := Subtype.ext hyx
  rwa [hyx'] at hy

section Module

open scoped IsMulCommutative

@[expose] noncomputable def Vmod (Z W : Subgroup G) (μ : CosetGeom G₀ G₁ G₂) :
    AddSubgroup (Additive ↥W) :=
  Subgroup.toAddSubgroup ((Vv Z μ).subgroupOf W)

theorem mem_Vmod {Z W : Subgroup G} {μ : CosetGeom G₀ G₁ G₂} {v : Additive ↥W} :
    v ∈ Vmod Z W μ ↔ ((Additive.toMul v : ↥W) : G) ∈ Vv Z μ := Iff.rfl

theorem iSup_Vmod_eq_top (α : CosetGeom G₀ G₁ G₂) :
    ⨆ μ : ↥(nbrs α), Vmod Z (Wv Z α) μ.1 = ⊤ := by
  have h1 : ⨆ μ : ↥(nbrs α), (Vv Z μ.1).subgroupOf (Wv Z α) = ⊤ := by
    apply Subgroup.map_injective (Wv Z α).subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have h2 : ∀ μ : ↥(nbrs α),
        ((Vv Z μ.1).subgroupOf (Wv Z α)).map (Wv Z α).subtype = Vv Z μ.1 :=
      fun μ => Subgroup.map_subgroupOf_eq_of_le (Vv_le_Wv μ.2)
    simp only [h2]
    have e : Wv Z α = ⨆ x : {δ : CosetGeom G₀ G₁ G₂ // δ ∈ nbrs α}, Vv Z x.1 := by
      unfold Wv; exact iSup_subtype'
    exact e.symm
  have h3 : ⨆ μ : ↥(nbrs α), Vmod Z (Wv Z α) μ.1 =
      Subgroup.toAddSubgroup (⨆ μ : ↥(nbrs α), (Vv Z μ.1).subgroupOf (Wv Z α)) :=
    (OrderIso.map_iSup Subgroup.toAddSubgroup _).symm
  rw [h3, h1]
  exact OrderIso.map_top _

theorem card_commSub_toAddEquiv (α : CosetGeom G₀ G₁ G₂) (W : Subgroup G) [IsMulCommutative ↥W]
    [Fact (stab α ≤ Subgroup.normalizer (W : Set G))] (z : ↥(stab α)) :
    Nat.card (GaloisDescent.commSub (DistribMulAction.toAddEquiv (Additive ↥W) z)) =
      Nat.card (ConjAut.commSubgroup W (z : G)) := by
  have hW : stab α ≤ Subgroup.normalizer (W : Set G) := Fact.out
  have hz : (z : G) ∈ Subgroup.normalizer (W : Set G) := hW z.2
  rw [ConjAut.card_commSubgroup W (z : G) hz]
  have e : DistribMulAction.toAddEquiv (Additive ↥W) z = ConjAut.conjAut W (z : G) hz :=
    AddEquiv.ext fun m => rfl
  rw [e]

theorem avg_inputs (hc : CritAmalgam G₀ G₁ G₂ T Z) {p : ℕ} {X₀ : Subgroup G}
    (hloc : IsLocalReg (γ₁ G₀ G₁ G₂) p X₀) (hp : p = 3 ∨ p = 5) {α : CosetGeom G₀ G₁ G₂}
    (hα : vtype α = false) {L : Subgroup G} (hL : BenderLocal α L) [IsMulCommutative ↥(Wv Z α)]
    [Fact (stab α ≤ Subgroup.normalizer (Wv Z α : Set G))] :
    (∀ l ∈ L.subgroupOf (stab α), ∀ μ : ↥(nbrs α), ∀ v ∈ Vmod Z (Wv Z α) μ.1,
      l • v ∈ Vmod Z (Wv Z α) (l • μ).1) ∧
    (∀ μ : ↥(nbrs α), ∀ l ∈ L.subgroupOf (stab α), l • μ = μ →
      ∃ k : ℕ, ∀ v ∈ Vmod Z (Wv Z α) μ.1, (l ^ 2 ^ k) • v = v) ∧
    PermBound.commL (Additive ↥(Wv Z α)) (L.subgroupOf (stab α)) ≠ ⊥ := by
  have hG := hc.amalgam.gen
  refine ⟨?_, ?_, ?_⟩
  · intro l _ μ v hv
    rw [mem_Vmod] at hv ⊢
    show (l : G) * _ * (l : G)⁻¹ ∈ Vv Z (stabToG₀ α l • μ.1)
    rw [CosetGeom.Vv_smul hc.normalizes]
    exact mul_mem_conjSub hv
  · intro μ l _ hlμ
    have hμt : vtype μ.1 = true := vtype_eq_true_of_mem_nbrs hα μ.2
    obtain ⟨X, hX⟩ := exists_isLocalReg_of_vtype hloc hμt
    have hlμ' : (l : G) ∈ stab μ.1 :=
      CosetGeom.mem_stab_of_smul_eq (g := stabToG₀ α l) (congrArg Subtype.val hlμ)
    have hpow : (l : G) ^ (p - 1) ∈ ballStab 1 μ.1 :=
      hX.pow_pred_mem hG (CosetGeom.mem_nbrs_symm μ.2) ⟨hlμ', l.2⟩
    have hcent := ballStab_le_centralizer_Vv hc hμt hpow
    obtain ⟨k, hk⟩ : ∃ k : ℕ, p - 1 = 2 ^ k := by
      rcases hp with rfl | rfl
      · exact ⟨1, by norm_num⟩
      · exact ⟨2, by norm_num⟩
    refine ⟨k, fun v hv => ?_⟩
    apply (ConjAut.eq_iff_val _).mpr
    show ((l ^ 2 ^ k : ↥(stab α)) : G) * _ * ((l ^ 2 ^ k : ↥(stab α)) : G)⁻¹ = _
    rw [Subgroup.coe_pow, ← hk]
    exact mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_iff.mp hcent _ hv).symm
  · intro hbot
    refine not_le_centralizer_Wv hc hα hL.le_stab hL.trans fun l hl => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have h1 := PermBound.sub_mem_commL (M := Additive ↥(Wv Z α))
      (show (⟨l, hL.le_stab hl⟩ : ↥(stab α)) ∈ L.subgroupOf (stab α) from hl)
      (Additive.ofMul (⟨w, hw⟩ : ↥(Wv Z α)))
    rw [hbot, AddSubgroup.mem_bot, sub_eq_zero, ConjAut.eq_iff_val] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm

theorem lower_bound (hc : CritAmalgam G₀ G₁ G₂ T Z) {p : ℕ} {X₀ : Subgroup G}
    (hloc : IsLocalReg (γ₁ G₀ G₁ G₂) p X₀) (hp : p = 3 ∨ p = 5) (hb : 4 ≤ critB G₀ G₁ G₂ Z)
    {α : CosetGeom G₀ G₁ G₂} (hα : vtype α = false) {L : Subgroup G} (hL : BenderLocal α L)
    {β : CosetGeom G₀ G₁ G₂} (hβ : β ∈ nbrs α) {z : G} (hzZ : z ∈ Z) (hzα : z ∈ stab α) :
    2 ^ ((Nat.card (nbrs α) - Nat.card {δ | δ ∈ nbrs α ∧ z ∈ stab δ}) / 2) ≤
      Nat.card (ConjAut.commSubgroup (Wv Z α) z) := by
  have hWab : IsElemAbelian 2 (Wv Z α) := isElemAbelian_Wv hc hb hα
  haveI : IsMulCommutative ↥(Wv Z α) := hWab.1
  haveI : Fact (stab α ≤ Subgroup.normalizer (Wv Z α : Set G)) := ⟨stab_le_normalizer_Wv hc α⟩
  have hsq : ∀ v ∈ Wv Z α, v * v = 1 := fun v hv => by rw [← pow_two]; exact hWab.2 v hv
  obtain ⟨U, hUL, hU2, hUfix, hUtrans, -, -⟩ := exists_unipotentH hL hβ
  obtain ⟨hV, hstab, hK⟩ := avg_inputs hc hloc hp hα hL
  have hz : (⟨z, hzα⟩ : ↥(stab α)) * ⟨z, hzα⟩ = 1 :=
    Subtype.ext (by show z * z = 1; rw [← pow_two]; exact hc.isElemAbelian.2 z hzZ)
  have hzL : ∀ l ∈ L.subgroupOf (stab α),
      (⟨z, hzα⟩ : ↥(stab α)) * l * (⟨z, hzα⟩ : ↥(stab α))⁻¹ ∈ L.subgroupOf (stab α) := by
    intro l hl
    exact (Subgroup.mem_normalizer_iff.mp (hL.normal hzα) (l : G)).mp hl
  have key := PermBound.two_pow_le_card_commSub (H := ↥(stab α)) (Ω := ↥(nbrs α))
    (M := Additive ↥(Wv Z α)) (ConjAut.add_self_eq_zero (Wv Z α) hsq)
    (subgroupOf_odd_gen hL.le_stab hL.odd_gen) (exists_mem_smul_eq hL) (odd_card_nbrs hc hα)
    hUL hU2 hUfix hUtrans (fun μ => Vmod Z (Wv Z α) μ.1) hV (iSup_Vmod_eq_top α) hstab hz hzL
    hK
  rw [card_fixedBy_nbrs, card_commSub_toAddEquiv] at key
  exact key

end Module

end T723

theorem theorem723_bound (hc : CritAmalgam G₀ G₁ G₂ T Z) {p : ℕ} {X₀ : Subgroup G}
    (hloc : IsLocalReg (γ₁ G₀ G₁ G₂) p X₀) (hp : p = 3 ∨ p = 5) {L : Subgroup G}
    (hL : BenderLocal (γ₀ G₀ G₁ G₂) L) (hb : Even (critB G₀ G₁ G₂ Z))
    (hb4 : 4 ≤ critB G₀ G₁ G₂ Z) :
    ∃ (α' : CosetGeom G₀ G₁ G₂) (z : G), vtype α' = false ∧ z ∈ Z ∧ z ∈ stab α' ∧
      z ∉ ballStab 1 α' ∧
      2 ^ ((Nat.card (nbrs α') - Nat.card {δ | δ ∈ nbrs α' ∧ z ∈ stab δ}) / 2) ≤
        2 * (Nat.card (nbrs α') - 1) ∧
      2 * (Nat.card {δ | δ ∈ nbrs α' ∧ z ∈ stab δ} - 1) ≤ Nat.card (nbrs α') - 1 ∧
      ∃ u : ℕ, Nat.card (nbrs α') = 2 ^ u + 1 := by
  have hG := hc.amalgam.gen
  obtain ⟨α', hdist, hnZ⟩ := exists_dist_eq_critB hc
  have hα' : vtype α' = false := CosetGeom.vtype_eq_false_of_even hG (by rw [hdist]; exact hb)
  obtain ⟨z, hzZ, hzn⟩ := SetLike.not_le_iff_exists.mp hnZ
  set b := critB G₀ G₁ G₂ Z with hbdef
  obtain ⟨β, hβ, hβd⟩ := CosetGeom.exists_adj_dist_eq hG (α := γ₀ G₀ G₁ G₂) (δ := α')
    (d := b - 1) (by rw [hdist]; omega)
  have hzβ : z ∈ ballStab 1 β := lt_critB_imp hc (by rw [hβd]; omega) hzZ
  have hzβ' : z ∈ stab β := CosetGeom.ballStab_le_stab 1 β hzβ
  have hzα' : z ∈ stab α' :=
    CosetGeom.mem_ballStab.mp hzβ α'
      (by rw [CosetGeom.dist_comm]; exact (CosetGeom.dist_eq_one_iff_adj.mpr hβ).le)
  obtain ⟨α₁, hα₁, hα₁d⟩ := CosetGeom.exists_adj_dist_eq hG (α := α') (δ := γ₀ G₀ G₁ G₂)
    (d := b - 1) (by rw [CosetGeom.dist_comm, hdist]; omega)
  obtain ⟨α₂, hα₂, hα₂d⟩ := CosetGeom.exists_adj_dist_eq hG (α := α') (δ := α₁) (d := b - 2)
    (by rw [hα₁d]; omega)
  obtain ⟨α₃, hα₃, hα₃d⟩ := CosetGeom.exists_adj_dist_eq hG (α := α') (δ := α₂) (d := b - 3)
    (by rw [hα₂d]; omega)
  have hα₁α₂ : α₁ ∈ nbrs α₂ := CosetGeom.mem_nbrs_symm hα₂
  have hne13 : α₁ ≠ α₃ := fun h => by
    have := hα₁d.symm.trans ((congrArg (CosetGeom.dist α') h).trans hα₃d)
    omega
  have hvα₂ : vtype α₂ = false := by
    have h := (CosetGeom.vtype_eq_iff_even_dist hG α' α₂).mpr
      (by rw [hα₂d]; obtain ⟨k, hk⟩ := hb; exact ⟨k - 1, by omega⟩)
    rw [hα'] at h
    exact h.symm
  have hcard : Nat.card (nbrs α₂) = Nat.card (nbrs α') :=
    (card_nbrs_eq hc hvα₂).trans (card_nbrs_eq hc hα').symm
  have hne : 1 < Nat.card (nbrs α₂) := by
    haveI : Nontrivial ↥(nbrs α₂) :=
      ⟨⟨⟨α₁, hα₁α₂⟩, ⟨α₃, hα₃⟩, fun h => hne13 (congrArg Subtype.val h)⟩⟩
    exact Finite.one_lt_card
  have hW : Wv Z α' ≤ stab α₂ :=
    Wv_le_stab hc hα' (by rw [CosetGeom.dist_comm, hα₂d]; omega)
      (by rw [CosetGeom.dist_comm, hα₂d]; omega)
  have hup := card_commSubgroup_Wv_le hc hloc hb4 hα₁ hα₂ hα' hW (odd_card_nbrs hc hvα₂) hne hzZ
    hzα'
  obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₀ hα'
  have hL' : BenderLocal α' (conjSub (g : G) L) := by
    rw [hg]
    exact hL.smul g
  refine ⟨α', z, hα', hzZ, hzα', hzn, ?_, ?_, ?_⟩
  · calc 2 ^ ((Nat.card (nbrs α') - Nat.card {δ | δ ∈ nbrs α' ∧ z ∈ stab δ}) / 2)
        ≤ Nat.card (ConjAut.commSubgroup (Wv Z α') z) :=
          T723.lower_bound hc hloc hp hb4 hα' hL' hβ hzZ hzα'
      _ ≤ 2 * (Nat.card (nbrs α₂) - 1) := hup
      _ = 2 * (Nat.card (nbrs α') - 1) := by rw [hcard]
  · exact T723.fixed_bound hG hL' hβ hzα' hzβ' hzn
  · exact T723.card_form hL' hβ (by rw [← hcard]; exact hne)

theorem theorem723 (hc : CritAmalgam G₀ G₁ G₂ T Z) {p : ℕ} {X₀ : Subgroup G}
    (hloc : IsLocalReg (γ₁ G₀ G₁ G₂) p X₀) (hp : p = 3 ∨ p = 5) {L : Subgroup G}
    (hL : BenderLocal (γ₀ G₀ G₁ G₂) L) (hb : Even (critB G₀ G₁ G₂ Z))
    (hb4 : 4 ≤ critB G₀ G₁ G₂ Z) : Nat.card (nbrs (γ₀ G₀ G₁ G₂)) ≤ 17 := by
  obtain ⟨α', z, hα', -, -, -, hlow, hf, u, hN⟩ := theorem723_bound hc hloc hp hL hb hb4
  have hu := PermBound.le_four_of_bounds hN hf hlow
  have h16 : 2 ^ u ≤ 16 := (Nat.pow_le_pow_right (by norm_num) hu).trans (by norm_num)
  rw [← card_nbrs_eq hc hα', hN]
  omega

end CFSG.Quasithin.F112Crit

end
