module

public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.CoprimeCentralizer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Normalizer
public import CFSG.Quasithin.Background.G9Stmts
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Bridge
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Toolkit

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.QuasithinUnique.Setup.Family

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem m_le_of_autRank {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    {S : Type} [Group S] (e : ↥L ≃* S) {r : ℕ}
    (hr : ∀ B : Subgroup (MulAut S), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ r) : m ≤ r := by
  have hLΓ : L ≤ Γ := h.L_comp.1
  have hLn : (L.subgroupOf Γ).Normal :=
    (Subgroup.normal_subgroupOf_iff hLΓ).2 fun l γ hl hγ => h.H_normal γ hγ l hl
  let ψ : ↥A →* MulAut ↥L :=
    { toFun := fun a => conjAutL hLΓ hLn (Subgroup.inclusion h.A_le a)
      map_one' := MulEquiv.ext fun l => Subtype.ext (by simp [conjAutL_apply])
      map_mul' := fun a b => MulEquiv.ext fun l => Subtype.ext (by
        simp [conjAutL_apply, mul_assoc]) }
  have hψ : ∀ a : ↥A, ∀ l : ↥L, (((ψ a) l : ↥L) : GLV V) = (a : GLV V) * l * (a : GLV V)⁻¹ :=
    fun a l => rfl
  have hA2 : IsPGroup 2 ↥A := OrdinaryProofs.isPGroup_two_of_isElemAbelian h.A_elem
  have hbot := OrdinaryProofs.inf_centralizer_eq_bot_of_two_group h.H_irr Γ hA2
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hc : (a : GLV V) ∈ A ⊓ (Γ ⊓ Subgroup.centralizer (L : Set (GLV V))) := by
      refine ⟨a.2, h.A_le a.2, ?_⟩
      show (a : GLV V) ∈ Subgroup.centralizer (L : Set (GLV V))
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have := hψ a ⟨l, hl⟩
      rw [ha] at this
      have h2 : l = (a : GLV V) * l * (a : GLV V)⁻¹ := this
      calc l * (a : GLV V) = ((a : GLV V) * l * (a : GLV V)⁻¹) * (a : GLV V) :=
            congrArg (· * (a : GLV V)) h2
        _ = (a : GLV V) * l := by simp [mul_assoc]
    rw [hbot, Subgroup.mem_bot] at hc
    exact Subtype.ext hc
  let ψ' : ↥A →* MulAut S := (MulAut.congr e).toMonoidHom.comp ψ
  have hinj' : Function.Injective ψ' := (MulAut.congr e).injective.comp hinj
  have hcard : Nat.card ψ'.range = 2 ^ m := by
    rw [← h.A_card]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv).symm
  have hcomm : ∀ x ∈ ψ'.range, ∀ y ∈ ψ'.range, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact h.A_elem.1.is_comm.comm a b
  have hsq : ∀ x ∈ ψ'.range, x * x = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_mul]
    have := h.A_elem.2 (a : GLV V) a.2
    have h3 : a * a = 1 := Subtype.ext (by simpa [sq] using this)
    rw [h3, map_one]
  have := hr _ hcomm hsq
  rw [hcard] at this
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this

theorem exists_mulEquiv_of_cover {L : Subgroup (GLV V)} (hq : CFSG.Open.IsQuasisimple ↥L)
    (hirr : IsIrr L ⊤) {S : Type} [Group S] (e : (↥L ⧸ Subgroup.center ↥L) ≃* S)
    (hCover : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* S),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) → π.ker = ⊥) :
    ∃ f : ↥L ≃* S, ∀ l : ↥L, f l = e (QuotientGroup.mk l) := by
  have hfin : Finite (GLV V) := OrdinaryProofs.finite_GLV_of_finite (V := V)
  have hW : ∀ w : Multiplicative V, w * w = 1 := mul_self_eq_one_multiplicative
  let ρ : ↥L →* S := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hρsurj : Function.Surjective ρ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ρ.ker = Subgroup.center ↥L := by
    ext x
    rw [MonoidHom.mem_ker]
    show e (QuotientGroup.mk x) = 1 ↔ _
    rw [← map_one e, e.injective.eq_iff, ← QuotientGroup.eq_one_iff]
  have hZodd : Odd (Nat.card (Subgroup.center ↥L)) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have h2 : 2 ∣ Nat.card (Subgroup.center ↥L) := even_iff_two_dvd.1 hev
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hxL : orderOf ((x : ↥L) : GLV V) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
    have hc : ∀ l ∈ toMulSub L, l * linEquivMulAut ((x : ↥L) : GLV V) =
        linEquivMulAut ((x : ↥L) : GLV V) * l := by
      intro l hl
      obtain ⟨g, rfl⟩ := linEquivMulAut.surjective l
      have hg : g ∈ L := linEquivMulAut_mem_toMulSub.1 hl
      have := Subgroup.mem_center_iff.1 x.2 ⟨g, hg⟩
      have h3 := congrArg (fun y : ↥L => linEquivMulAut (y : GLV V)) this
      simpa using h3
    have hodd := CFSG.QuasithinUnique.Setup.X1.odd_orderOf_of_commutes hW
      (isIrrOn_toMulSub hirr) hc
    rw [MulEquiv.orderOf_eq, hxL] at hodd
    exact absurd hodd (by decide)
  have : Group.IsPerfect ↥L := ⟨hq.1⟩
  have hker1 : ρ.ker = ⊥ := hCover ↥L ρ hρsurj (by rw [hker]) (by rw [hker]; exact hZodd)
  have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff _).1 hker1
  exact ⟨MulEquiv.ofBijective ρ ⟨hinj, hρsurj⟩, fun l => rfl⟩

theorem false_of_cover_rank_dim {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    {S : Type} [Group S] (e : (↥L ⧸ Subgroup.center ↥L) ≃* S)
    (hCover : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* S),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) → π.ker = ⊥)
    {r : ℕ}
    (hr : ∀ B : Subgroup (MulAut S), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ r)
    {ρ : ℕ}
    (hDim : ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
      ∀ σ : S →* MulAut W, Function.Injective σ → 2 ^ ρ ≤ Nat.card W)
    (hlt : 2 * (r + 1) < ρ) : False := by
  obtain ⟨f, -⟩ := exists_mulEquiv_of_cover h.L_comp.2.2 h.H_irr e hCover
  have hm := m_le_of_autRank h f hr
  let σ : S →* MulAut (Multiplicative V) :=
    (toMulSub L).subtype.comp ((toMulSubEquiv L).toMonoidHom.comp f.symm.toMonoidHom)
  have hσ : Function.Injective σ :=
    Subtype.val_injective.comp ((toMulSubEquiv L).injective.comp f.symm.injective)
  have hd := hDim (Multiplicative V) mul_self_eq_one_multiplicative σ hσ
  rw [natCard_multiplicative] at hd
  have hd' : ρ ≤ Module.finrank (ZMod 2) V := (Nat.pow_le_pow_iff_right (by norm_num)).1 hd
  have hb := h.bound
  omega

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
