module

public import CFSG.Quasithin.MS93.S36SpFaith
public import CFSG.Quasithin.MS93.S36SpAct
public import CFSG.Quasithin.MS93.MSPBridge
public import CFSG.Quasithin.MS93.S33LamOm

public section

namespace CFSG.Quasithin.MS93.S36SP

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93.MSP
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement IsMulCommutative Matrix

section Model

variable {F : Type} [Field F] [CharP F 2]

theorem rad_mem_closure_transv (hF : 2 < Nat.card F) {v : V4 F} (hv : v ≠ 0) (s : F) :
    Multiplicative.ofAdd ((0 : V4 F), s) ∈ Subgroup.closure
      {m | ∃ (c : F) (y : Multiplicative (V4 F × F)), m = omega5Act F (transv v c) y * y⁻¹} := by
  set X := {m | ∃ (c : F) (y : Multiplicative (V4 F × F)), m = omega5Act F (transv v c) y * y⁻¹}
    with hX
  obtain ⟨w, hw⟩ := exists_form_eq_one hv
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have key : ∀ β : F, β ≠ 0 →
      Multiplicative.ofAdd (v, quad₀ v + β) ∈ Subgroup.closure X := by
    intro β hβ
    refine Subgroup.subset_closure ⟨β⁻¹, Multiplicative.ofAdd (β • w, 0), ?_⟩
    have h1 : mat (transv v β⁻¹) *ᵥ (β • w) = β • w + v := by
      rw [transv_mulVec, map_smul, smul_eq_mul, hw, mul_one, inv_mul_cancel₀ hβ, one_smul]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, toAdd_omega5Act, toAdd_ofAdd, toAdd_ofAdd, h1]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.fst_neg]
      abel
    · simp only [Prod.snd_add, Prod.snd_neg]
      rw [isQuadOf_quad₀.map_add (β • w) v, map_smul, LinearMap.smul_apply, smul_eq_mul,
        form_swap v w, hw]
      linear_combination (-(quad₀ (β • w)) + β) * h2
  by_cases hs : s = 0
  · rw [hs]
    exact Subgroup.one_mem _
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨β, hβ0, hβs⟩ : ∃ β : F, β ≠ 0 ∧ β ≠ s := by
    by_contra hcon
    push Not at hcon
    have hsub : (Set.univ : Set F) ⊆ {0, s} := fun β _ => by
      by_cases h0 : β = 0
      · exact Or.inl h0
      · exact Or.inr (hcon β h0)
    have hle : Nat.card F ≤ 2 := by
      calc Nat.card F = (Set.univ : Set F).ncard := Set.ncard_univ F |>.symm
        _ ≤ ({0, s} : Set F).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    omega
  have hβ' : β - s ≠ 0 := sub_ne_zero.2 hβs
  have e : Multiplicative.ofAdd ((0 : V4 F), s) = Multiplicative.ofAdd (v, quad₀ v + β) *
      (Multiplicative.ofAdd (v, quad₀ v + (β - s)))⁻¹ := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, toAdd_ofAdd, toAdd_ofAdd, toAdd_ofAdd]
    refine Prod.ext ?_ ?_
    · simp
    · simp only [Prod.snd_add, Prod.snd_neg]
      ring
  rw [e]
  exact Subgroup.mul_mem _ (key β hβ0) (Subgroup.inv_mem _ (key _ hβ'))

end Model

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

structure SpFrame (h : PUHyp M T L) where
  F : Type
  [fld : Field F]
  [fty : Fintype F]
  [chr : CharP F 2]
  k : ℕ
  card : Fintype.card F = 2 ^ k
  one_le : 1 ≤ k
  vec : ↥(Uq M T L) →* Multiplicative (V4 F)
  surj : Function.Surjective vec
  ker : ∀ u : ↥(Uq M T L), vec u = 1 ↔ (u : G) ∈ Zq M L
  gen : ∀ g : Sp4 F, ∃ x ∈ M, ActsMat vec x g ∧ ∀ m ∈ M, ∃ g', ActsMat vec (m * x * m⁻¹) g'
  lmat : ∀ l ∈ L, ∃ g, ActsMat vec l g
  lift : ∀ t ∈ M, ∀ g, ActsMat vec t g → ∀ u : ↥(Uq M T L),
    t * u * t⁻¹ * (u : G)⁻¹ ∈ Zq M L → t * u * t⁻¹ = u
  card_C : Nat.card ↥(Uq M T L ⊓ Zq M L) ≤ 2 ^ k
  key : 2 ≤ k → ∀ t ∈ M, (∃ e : ℕ, t ^ 2 ^ e = 1) → ∀ g, ActsMat vec t g →
    ∃ l ∈ L, ActsLike M t l
  rad : 2 ≤ k → ∀ v : V4 F, v ≠ 0 → ∀ S : Subgroup G, S ≤ M →
    (∀ c : F, ∃ x ∈ S, ActsMat vec x (transv v c)) → Uq M T L ⊓ Zq M L ≤ ⁅S, Uq M T L⁆

attribute [instance] SpFrame.fld SpFrame.fty SpFrame.chr

section LiftL

variable {F : Type} [Field F] {α : ↥L →* ↥(StatedSp 2 F)}

theorem mem_trivW_of_alpha_eq_one (h : PUHyp M T L)
    (hnat : IsSumOfNaturalModulesVia L (Uq M T L) (Uq M T L ⊓ Zq M L) α false 1)
    {l : ↥L} (hl : α l = 1) : (l : G) ∈ trivW h := by
  obtain ⟨hLU, -, β, -, hβk, hβeq⟩ := hnat
  refine ⟨h.L_le l.2, fun u hu => ?_⟩
  have hlu : (l : G) * u * (l : G)⁻¹ ∈ Uq M T L :=
    (Subgroup.mem_normalizer_iff.1 (hLU l.2) u).1 hu
  have h1 := hβeq l ⟨u, hu⟩ ⟨_, hlu⟩ rfl
  have h2 : β ⟨_, hlu⟩ = β ⟨u, hu⟩ := by
    apply Multiplicative.toAdd.injective
    funext i
    rw [h1 i, hl]
    simp [moduleAct]
  have h3 : (⟨_, hlu⟩ : ↥(Uq M T L)) * (⟨u, hu⟩ : ↥(Uq M T L))⁻¹ ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h2, mul_inv_cancel]
  rw [hβk, Subgroup.mem_subgroupOf] at h3
  exact h3.2

theorem exists_piL (h : PUHyp M T L)
    (hnat : IsSumOfNaturalModulesVia L (Uq M T L) (Uq M T L ⊓ Zq M L) α false 1)
    (hsurj : Function.Surjective α) :
    ∃ π : ↥(StatedSp 2 F) →* ↥(autOn L (Uq M T L)), Function.Surjective π ∧
    ∀ l : ↥L, ((π (α l) : ↥(autOn L (Uq M T L))) : MulAut ↥(Uq M T L)) =
      conjAct (Uq M T L) ⟨l, le_normalizer_Uq h.le_normalizer (h.L_le l.2)⟩ := by
  have hLU : L ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    h.L_le.trans (le_normalizer_Uq h.le_normalizer)
  let χ : ↥L →* ↥(autOn L (Uq M T L)) :=
    ((conjAct (Uq M T L)).comp (Subgroup.inclusion hLU)).codRestrict (autOn L (Uq M T L))
      (fun l => Setup.mem_autOn_iff.2 ⟨Subgroup.inclusion hLU l, l.2, rfl⟩)
  have hker : α.ker ≤ χ.ker := by
    intro l hl
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show conjAct (Uq M T L) (Subgroup.inclusion hLU l) = 1
    apply InternalSec.conjAct_eq_one_of_mem_centralizer
    exact mem_centralizer_of_mem_trivW h (mem_trivW_of_alpha_eq_one h hnat hl)
  let π := (QuotientGroup.lift α.ker χ hker).comp
    (QuotientGroup.quotientKerEquivOfSurjective α hsurj).symm.toMonoidHom
  have hπa : ∀ l, π (α l) = χ l := by
    intro l
    have e : (QuotientGroup.quotientKerEquivOfSurjective α hsurj).symm (α l) =
        QuotientGroup.mk l := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift α.ker χ hker
      ((QuotientGroup.quotientKerEquivOfSurjective α hsurj).symm (α l)) = χ l
    rw [e, QuotientGroup.lift_mk]
  refine ⟨π, fun x => ?_, fun l => by rw [hπa]; rfl⟩
  obtain ⟨g, hgL, hgx⟩ := Setup.mem_autOn_iff.1 x.2
  refine ⟨α ⟨g, hgL⟩, ?_⟩
  rw [hπa]
  apply Subtype.ext
  rw [← hgx]
  rfl

theorem realizesVia_natL (h : PUHyp M T L)
    (hnat : IsSumOfNaturalModulesVia L (Uq M T L) (Uq M T L ⊓ Zq M L) α false 1)
    (hsurj : Function.Surjective α) [IsMulCommutative ↥(Uq M T L)]
    {π : ↥(StatedSp 2 F) →* ↥(autOn L (Uq M T L))} (hπs : Function.Surjective π)
    (hπa : ∀ l : ↥L, ((π (α l) : ↥(autOn L (Uq M T L))) : MulAut ↥(Uq M T L)) =
      conjAct (Uq M T L) ⟨l, le_normalizer_Uq h.le_normalizer (h.L_le l.2)⟩) :
    (FFModel.nat (StatedSp 2 F)).RealizesVia (autOn L (Uq M T L)) ⊤
      ((Zq M L).subgroupOf (Uq M T L)) π := by
  obtain ⟨-, -, β₀, hβ₀s, hβ₀k, hβ₀e⟩ := hnat
  let β₁ : ↥(Uq M T L) →* Multiplicative (Fin 2 ⊕ Fin 2 → F) :=
    { toFun := fun u => Multiplicative.ofAdd (Multiplicative.toAdd (β₀ u) 0)
      map_one' := by simp
      map_mul' := fun u v => by simp }
  have hβ₁ : ∀ u, β₁ u = Multiplicative.ofAdd (Multiplicative.toAdd (β₀ u) 0) := fun _ => rfl
  have hβ₁s : Function.Surjective β₁ := by
    intro x
    obtain ⟨u, hu⟩ := hβ₀s (Multiplicative.ofAdd fun _ => Multiplicative.toAdd x)
    exact ⟨u, by rw [hβ₁, hu]; rfl⟩
  have hβ₁k : ∀ u, β₁ u = 1 ↔ (u : G) ∈ Zq M L := by
    intro u
    have e1 : β₁ u = 1 ↔ β₀ u = 1 := by
      constructor
      · intro h1
        apply Multiplicative.toAdd.injective
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        exact congrArg Multiplicative.toAdd h1
      · intro h1
        rw [hβ₁, h1]
        rfl
    rw [e1, ← MonoidHom.mem_ker, hβ₀k, Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.2, fun h => ⟨u.2, h⟩⟩
  have hβ₁e : ∀ (l : ↥L) (u v : ↥(Uq M T L)), (v : G) = l * u * l⁻¹ →
      β₁ v = Multiplicative.ofAdd ((((α l : ↥(StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ Multiplicative.toAdd (β₁ u)) := by
    intro l u v huv
    have := hβ₀e l u v huv 0
    rw [hβ₁, hβ₁, this]
    simp [moduleAct]
  have hY : L ≤ Subgroup.normalizer ((Uq M T L ⊓ Zq M L : Subgroup G) : Set G) :=
    h.L_le.trans (le_normalizer_inf (le_normalizer_Uq h.le_normalizer)
      (le_normalizer_Zq h.le_normalizer))
  have hstab := InternalSec.autOn_le_stabSub hY
  refine ⟨hπs, le_top, bot_le, fun _ _ _ => Subgroup.mem_top _, fun x z hz => (hstab x.2 z).2 hz,
    (FFModel.nat_isActionModel _).sec_inv, (FFModel.nat_isActionModel _).ker_inv, ?_⟩
  let β : ↥(⊤ : Subgroup ↥(Uq M T L)) →* (FFModel.nat (StatedSp 2 F)).Sec :=
    (QuotientGroup.mk' _).comp
      (Subgroup.topEquiv.symm.toMonoidHom.comp (β₁.comp (⊤ : Subgroup ↥(Uq M T L)).subtype))
  have hβ : ∀ u : ↥(⊤ : Subgroup ↥(Uq M T L)),
      β u = QuotientGroup.mk ⟨β₁ u, Subgroup.mem_top _⟩ := fun _ => rfl
  refine ⟨β, fun q => ?_, fun u => ?_, fun γ u m hu hm hum => ?_⟩
  · obtain ⟨⟨x, -⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨u, hu⟩ := hβ₁s x
    exact ⟨⟨u, Subgroup.mem_top _⟩, by rw [hβ]; congr 1; exact Subtype.ext hu⟩
  · rw [hβ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    show β₁ u ∈ (⊥ : Subgroup (Multiplicative (Fin 2 ⊕ Fin 2 → F))) ↔ _
    rw [Subgroup.mem_bot, hβ₁k, Subgroup.mem_subgroupOf]
  · rw [hβ] at hum ⊢
    have h3 : (⟨β₁ u, Subgroup.mem_top _⟩ : ↥(FFModel.nat (StatedSp 2 F)).sec) = m := by
      have h1 := QuotientGroup.eq.1 hum
      exact inv_mul_eq_one.1 (Subtype.ext (Subgroup.mem_bot.1 (Subgroup.mem_subgroupOf.1 h1)))
    subst h3
    congr 1
    apply Subtype.ext
    obtain ⟨l₀, rfl⟩ := hsurj γ
    have hval : ((((π (α l₀) : ↥(autOn L (Uq M T L))) : MulAut ↥(Uq M T L))
        (u : ↥(Uq M T L)) : ↥(Uq M T L)) : G) =
          (l₀ : G) * ((u : ↥(Uq M T L)) : G) * (l₀ : G)⁻¹ := by
      rw [hπa]
      exact InternalSec.coe_conjAct_apply _ _
    exact hβ₁e l₀ (u : ↥(Uq M T L)) _ hval

end LiftL

section Construct

omit [Finite G] in
theorem card_inf_Zq_eq (U Z : Subgroup G) :
    Nat.card ↥(Z.subgroupOf U) = Nat.card ↥(U ⊓ Z) := by
  rw [inf_comm, ← Subgroup.subgroupOf_map_subtype,
    Subgroup.card_map_of_injective U.subtype_injective]

theorem mem_trivW_of_actsMat_one (h : PUHyp M T L) {F : Type} [Field F]
    {vec : ↥(Uq M T L) →* Multiplicative (V4 F)}
    (hker : ∀ u : ↥(Uq M T L), vec u = 1 ↔ (u : G) ∈ Zq M L) {t : G} (htM : t ∈ M)
    (ht : ActsMat vec t 1) : t ∈ trivW h := by
  have hUn := le_normalizer_Uq (T := T) h.le_normalizer
  refine ⟨htM, fun u hu => ?_⟩
  have hv := conj_mem (hUn htM) ⟨u, hu⟩
  have h1 := ht ⟨u, hu⟩ ⟨_, hv⟩ rfl
  rw [mat_one, Matrix.one_mulVec] at h1
  have h2 : vec (⟨_, hv⟩ * (⟨u, hu⟩ : ↥(Uq M T L))⁻¹) = 1 := by
    rw [map_mul, map_inv]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, h1, add_neg_cancel]
    rfl
  exact (hker _).1 h2

theorem exists_two_elem_preimage {F : Type} [Field F] {α : ↥L →* ↥(StatedSp 2 F)}
    (hsurj : Function.Surjective α) {g : ↥(StatedSp 2 F)} {e : ℕ} (hg : g ^ 2 ^ e = 1) :
    ∃ l : ↥L, α l = g ∧ ∃ a : ℕ, l ^ 2 ^ a = 1 := by
  obtain ⟨l₀, rfl⟩ := hsurj g
  obtain ⟨a, m₀, hm₀, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos l₀).ne'
  have hcop : Nat.Coprime m₀ (2 ^ (e + 1)) := Nat.Coprime.pow_right _ hm₀.coprime_two_right
  obtain ⟨m₁, -, hm₁⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop
    (Nat.one_lt_two_pow (Nat.succ_ne_zero e))
  refine ⟨l₀ ^ (m₀ * m₁), ?_, a, ?_⟩
  · have hg' : α l₀ ^ 2 ^ (e + 1) = 1 := by rw [pow_succ, pow_mul, hg, one_pow]
    rw [map_pow, ← Nat.mod_add_div (m₀ * m₁) (2 ^ (e + 1)), pow_add, pow_mul, hg', one_pow,
      mul_one, hm₁, pow_one]
  · rw [← pow_mul, mul_comm, ← mul_assoc, pow_mul, ← hord, pow_orderOf_eq_one, one_pow]

theorem exists_spFrame_of_sp4 (h : PUHyp M T L) {k : ℕ} (hk : 2 ≤ k) {F : Type} [Field F]
    [Fintype F] (hF : Fintype.card F = 2 ^ k) {α : ↥L →* ↥(StatedSp 2 F)}
    (hsurj : Function.Surjective α)
    (hnat : IsSumOfNaturalModulesVia L (Uq M T L) (Uq M T L ⊓ Zq M L) α false 1) :
    ∃ d : SpFrame h, d.k = k := by
  have : CharP F 2 := charP_of_card_eq_prime_pow hF
  have hFn : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hF]
  obtain ⟨c⟩ := MSP.nonempty_natCoord hnat
  have := Sp4L.isMulCommutative_uq h
  have hUn := le_normalizer_Uq (T := T) h.le_normalizer
  have hLU : L ≤ Subgroup.normalizer (Uq M T L : Set G) := h.L_le.trans hUn
  obtain ⟨π, hπs, hπa⟩ := exists_piL h hnat hsurj
  have hreal := realizesVia_natL h hnat hsurj hπs hπa
  have hV : ∀ w : ↥(Uq M T L), w ^ 2 = 1 := fun w => Subtype.ext (by simpa using Sp4L.uq_sq h w.2)
  have hcomm : commV (autOn L (Uq M T L)) = ⊤ :=
    InternalSec.commV_autOn_eq_top hLU h.commutator_uq
  have hZ : (Zq M L).subgroupOf (Uq M T L) ≤ fixV (autOn L (Uq M T L)) :=
    InternalSec.le_fixV_autOn (inf_le_right.trans inf_le_right)
  obtain ⟨hcardC, hlift⟩ := Sp4L.lift_of_realizes hFn (by omega) hV hZ hcomm hreal
  have hker : ∀ u : ↥(Uq M T L), c.toVec u = 1 ↔ (u : G) ∈ Zq M L := by
    intro u
    rw [← MonoidHom.mem_ker, c.ker_eq, Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.2, fun h => ⟨u.2, h⟩⟩
  have hLact : ∀ l : ↥L, ActsMat c.toVec (l : G) (α l) := fun l u v huv => c.equiv l u v huv
  have hagree : ∀ t ∈ M, ∀ g, ActsMat c.toVec t g → ∀ l : ↥L, α l = g →
      t * (l : G)⁻¹ ∈ Subgroup.centralizer (Uq M T L : Set G) := by
    intro t htM g hg l hl
    have h1 : ActsMat c.toVec (t * (l : G)⁻¹) (g * g⁻¹) :=
      actsMat_mul (inv_mem (hLU l.2)) hg (actsMat_inv (hl ▸ hLact l))
    rw [mul_inv_cancel] at h1
    exact mem_centralizer_of_mem_trivW h
      (mem_trivW_of_actsMat_one h hker (M.mul_mem htM (M.inv_mem (h.L_le l.2))) h1)
  refine ⟨SpFrame.mk F k hF (by omega) c.toVec c.surj hker ?_ ?_ ?_ ?_ ?_ ?_, rfl⟩
  · intro g
    obtain ⟨l, rfl⟩ := hsurj g
    refine ⟨l, h.L_le l.2, hLact l, fun m hm => ?_⟩
    have hml : m * (l : G) * m⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (h.le_normalizer hm) _).1 l.2
    exact ⟨α ⟨_, hml⟩, hLact ⟨_, hml⟩⟩
  · intro l hl
    exact ⟨α ⟨l, hl⟩, hLact ⟨l, hl⟩⟩
  · intro t htM g hg u hu
    obtain ⟨l, rfl⟩ := hsurj g
    have hc := hagree t htM _ hg l rfl
    have hlu : (l : G) * u * (l : G)⁻¹ ∈ Uq M T L := conj_mem (hLU l.2) u
    have e : t * u * t⁻¹ = (l : G) * u * (l : G)⁻¹ := by
      have := Subgroup.mem_centralizer_iff.1 hc _ hlu
      calc t * u * t⁻¹ = (t * (l : G)⁻¹) * ((l : G) * u * (l : G)⁻¹) * (t * (l : G)⁻¹)⁻¹ := by
            group
        _ = (l : G) * u * (l : G)⁻¹ := by rw [← this]; group
    rw [e] at hu ⊢
    have hx : conjAct (Uq M T L) ⟨l, hLU l.2⟩ ∈ autOn L (Uq M T L) :=
      Setup.mem_autOn_iff.2 ⟨⟨l, hLU l.2⟩, l.2, rfl⟩
    have hval : ((conjAct (Uq M T L) ⟨l, hLU l.2⟩ u : ↥(Uq M T L)) : G) =
        (l : G) * u * (l : G)⁻¹ := InternalSec.coe_conjAct_apply _ _
    have hxw : conjAct (Uq M T L) ⟨l, hLU l.2⟩ u * u⁻¹ ∈ (Zq M L).subgroupOf (Uq M T L) := by
      rw [Subgroup.mem_subgroupOf]
      show ((conjAct (Uq M T L) ⟨l, hLU l.2⟩ u : ↥(Uq M T L)) : G) * (u : G)⁻¹ ∈ _
      rw [hval]
      exact hu
    have := hlift _ hx u hxw
    rw [← hval, this]
  · rw [← card_inf_Zq_eq]
    exact hcardC
  · intro _ t htM ht2 g hg
    obtain ⟨e, he⟩ := ht2
    have hge : g ^ 2 ^ e = 1 := by
      have h1 := actsMat_pow (hUn htM) hg (2 ^ e)
      rw [he] at h1
      exact actsMat_unique c.surj (one_mem _) h1 actsMat_one
    obtain ⟨l, hl, hl2⟩ := exists_two_elem_preimage hsurj hge
    refine ⟨l, l.2, actsLike_of_mem_centralizer h htM l.2 ⟨e, he⟩ ?_ (hagree t htM g hg l hl)⟩
    obtain ⟨a, ha⟩ := hl2
    exact ⟨a, by simpa using congrArg Subtype.val ha⟩
  · intro _ v hv S hSM hS z hz
    obtain ⟨ψ, hψs, hψe, hψZ⟩ := S33.exists_omega5_quotient hFn (by omega) hV hZ hcomm hreal
    have hq2 : 2 < Nat.card F := by
      rw [hFn]
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have hgen : Subgroup.closure {m | ∃ (c : F) (y : Multiplicative (V4 F × F)),
        m = omega5Act F (transv v c) y * y⁻¹} ≤
          ⁅S, Uq M T L⁆.comap ((Uq M T L).subtype.comp ψ) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨c, y, rfl⟩
      obtain ⟨x, hxS, hx⟩ := hS c
      obtain ⟨l, hl⟩ := hsurj (transv v c)
      have hc := hagree x (hSM hxS) _ hx l hl
      set u : ↥(Uq M T L) := ψ y with hu
      have hlu : (l : G) * u * (l : G)⁻¹ ∈ Uq M T L := conj_mem (hLU l.2) u
      have exl : x * u * x⁻¹ = (l : G) * u * (l : G)⁻¹ := by
        have := Subgroup.mem_centralizer_iff.1 hc _ hlu
        calc x * u * x⁻¹ = (x * (l : G)⁻¹) * ((l : G) * u * (l : G)⁻¹) * (x * (l : G)⁻¹)⁻¹ := by
              group
          _ = (l : G) * u * (l : G)⁻¹ := by rw [← this]; group
      have hval : ((((π (transv v c) : ↥(autOn L (Uq M T L))) : MulAut ↥(Uq M T L)) u :
          ↥(Uq M T L)) : G) = x * u * x⁻¹ := by
        rw [← hl, hπa, exl]
        exact InternalSec.coe_conjAct_apply _ _
      rw [SetLike.mem_coe, Subgroup.mem_comap, MonoidHom.comp_apply, map_mul, map_inv, hψe,
        Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hval]
      have := Subgroup.commutator_mem_commutator hxS u.2
      rwa [commutatorElement_def] at this
    obtain ⟨y, hy⟩ := hψs ⟨z, hz.1⟩
    have hyR : y ∈ omega5Rad F := hψZ y (by rw [hy]; exact hz.2)
    have hy' : y = Multiplicative.ofAdd ((0 : V4 F), (Multiplicative.toAdd y).2) := by
      apply Multiplicative.toAdd.injective
      exact Prod.ext hyR rfl
    have := hgen (hy' ▸ rad_mem_closure_transv hq2 hv _)
    rw [Subgroup.mem_comap, MonoidHom.comp_apply, hy] at this
    exact this

theorem exists_spFrame_of_two (h : PUHyp M T L) {α : ↥M →* ↥(StatedSp 2 (ZMod 2))}
    (hsurj : Function.Surjective α)
    (hnat : IsSumOfNaturalModulesVia M (Uq M T L) (Uq M T L ⊓ Zq M L) α false 1) :
    ∃ d : SpFrame h, d.k = 1 := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hnat
  have hnat' : IsSumOfNaturalModulesVia M (Uq M T L)
      (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) α false 1 := by
    rw [← h.Uq_inf_Zq]
    exact hnat
  obtain ⟨hcard, -, hlift⟩ := sp4Lift_holds G M T L h 1 (ZMod 2) inferInstance inferInstance α
    ⟨le_rfl, by simp, hsurj, hnat'⟩
  have hker : ∀ u : ↥(Uq M T L), c.toVec u = 1 ↔ (u : G) ∈ Zq M L := by
    intro u
    rw [← MonoidHom.mem_ker, c.ker_eq, Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.2, fun h => ⟨u.2, h⟩⟩
  have hMact : ∀ m : ↥M, ActsMat c.toVec (m : G) (α m) := fun m u v huv => c.equiv m u v huv
  refine ⟨SpFrame.mk (ZMod 2) 1 (by simp) le_rfl c.toVec c.surj hker ?_ ?_ ?_ ?_
    (fun hk => absurd hk (by norm_num)) (fun hk => absurd hk (by norm_num)), rfl⟩
  · intro g
    obtain ⟨m, rfl⟩ := hsurj g
    refine ⟨m, m.2, hMact m, fun m' hm' => ?_⟩
    have hmm : m' * (m : G) * m'⁻¹ ∈ M := M.mul_mem (M.mul_mem hm' m.2) (M.inv_mem hm')
    exact ⟨α ⟨_, hmm⟩, hMact ⟨_, hmm⟩⟩
  · intro l hl
    exact ⟨α ⟨l, h.L_le hl⟩, hMact ⟨l, h.L_le hl⟩⟩
  · intro t htM _ _ u hu
    exact hlift t htM u u.2 hu.2
  · rw [h.Uq_inf_Zq]
    simpa using hcard

end Construct

end CFSG.Quasithin.MS93.S36SP
