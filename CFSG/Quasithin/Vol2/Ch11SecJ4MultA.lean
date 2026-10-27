module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.J4Mult

@[expose] def NoPerfectTripleCover (G : Type*) [Group G] : Prop :=
  ∀ (E : Type) [Group E] (π : E →* G), Function.Surjective π → Group.IsPerfect E →
    Nat.card π.ker ≠ 3

@[expose] def NoPerfectCentralCover (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ (E : Type) [Group E] (π : E →* G), Function.Surjective π → Group.IsPerfect E →
    π.ker ≤ Subgroup.center E → Nat.card π.ker ≠ p

theorem NoPerfectTripleCover.noPerfectCentralCover {G : Type*} [Group G]
    (h : NoPerfectTripleCover G) : NoPerfectCentralCover 3 G :=
  fun E _ π hπ hE _ => h E π hπ hE

open scoped commutatorElement IsMulCommutative

private theorem commutatorElement_mul_central {G : Type*} [Group G] (x y : G) {c d : G}
    (hc : c ∈ Subgroup.center G) (hd : d ∈ Subgroup.center G) : ⁅x * c, y * d⁆ = ⁅x, y⁆ := by
  have hc' : ∀ g : G, c * g * c⁻¹ = g := fun g => by
    rw [← Subgroup.mem_center_iff.1 hc g, mul_inv_cancel_right]
  have hd' : ∀ g : G, d * g * d⁻¹ = g := fun g => by
    rw [← Subgroup.mem_center_iff.1 hd g, mul_inv_cancel_right]
  calc ⁅x * c, y * d⁆ = x * (c * (y * d) * c⁻¹) * x⁻¹ * d⁻¹ * y⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = x * y * (d * x⁻¹ * d⁻¹) * y⁻¹ := by rw [hc']; group
    _ = ⁅x, y⁆ := by rw [hd', commutatorElement_def]

theorem ker_inf_commutator_eq_bot {X : Type} {Q : Type*} [Group X] [Group Q]
    [Group.IsPerfect Q] {p : ℕ} (hp : p.Prime) (hQ : NoPerfectCentralCover p Q) (ψ : X →* Q)
    (hψ : Function.Surjective ψ) (hc : ψ.ker ≤ Subgroup.center X) (hcard : Nat.card ψ.ker = p) :
    ψ.ker ⊓ commutator X = ⊥ := by
  have : Finite ψ.ker := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  by_contra hne
  have hle : ψ.ker ≤ commutator X := by
    have h1 : Nat.card ↥(ψ.ker ⊓ commutator X) ∣ p :=
      hcard ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hp).1 h1 with h | h
    · exact absurd (Subgroup.card_eq_one.1 h) hne
    · have he : ψ.ker ⊓ commutator X = ψ.ker :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hcard])
      rw [← he]
      exact inf_le_right
  have hmap : (commutator X).map ψ = ⊤ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective ψ hψ,
      ← _root_.commutator_def]
    exact Group.IsPerfect.commutator_eq_top
  have hdec : ∀ x : X, ∃ y ∈ commutator X, y⁻¹ * x ∈ ψ.ker := by
    intro x
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (hmap ▸ Subgroup.mem_top (ψ x))
    exact ⟨y, hy, by rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]⟩
  have hYY : ⁅commutator X, commutator X⁆ = commutator X := by
    refine le_antisymm (Subgroup.commutator_le_left _ _) ?_
    conv_lhs => rw [_root_.commutator_def]
    rw [Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨y, hy, hya⟩ := hdec a
    obtain ⟨y', hy', hyb⟩ := hdec b
    have e := commutatorElement_mul_central y y' (hc hya) (hc hyb)
    rw [mul_inv_cancel_left, mul_inv_cancel_left] at e
    rw [e]
    exact Subgroup.commutator_mem_commutator hy hy'
  have : Group.IsPerfect (commutator X) := Subgroup.isPerfect_iff.2 hYY
  let ψ' : commutator X →* Q := ψ.comp (commutator X).subtype
  have hψ' : Function.Surjective ψ' := by
    intro q
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 (hmap ▸ Subgroup.mem_top q)
    exact ⟨⟨y, hy⟩, rfl⟩
  have hker' : ψ'.ker = ψ.ker.subgroupOf (commutator X) := by
    ext y
    simp [ψ', MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  refine hQ (commutator X) ψ' hψ' this ?_ ?_
  · rw [hker']
    intro y hy
    rw [Subgroup.mem_subgroupOf] at hy
    exact Subgroup.mem_center_iff.2 fun g => Subtype.ext (Subgroup.mem_center_iff.1 (hc hy) g)
  · rw [hker', ← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv

theorem inf_commutator_eq_bot {X : Type} {Q : Type*} [Group X] [Group Q] [Group.IsPerfect Q]
    {p : ℕ} (hp : p.Prime) (hQ : NoPerfectCentralCover p Q) (ψ : X →* Q)
    (hψ : Function.Surjective ψ) {Z : Subgroup X} (hZc : Z ≤ Subgroup.center X)
    (hZp : Nat.card Z = p) (hZψ : Z ≤ ψ.ker)
    (hcop : Nat.Coprime (Z.subgroupOf ψ.ker).index p) : Z ⊓ commutator X = ⊥ := by
  classical
  set m := (Z.subgroupOf ψ.ker).index with hm
  have hZ'c : Z.subgroupOf ψ.ker ≤ Subgroup.center ψ.ker := fun x hx =>
    Subgroup.mem_center_iff.2 fun g => Subtype.ext (Subgroup.mem_center_iff.1 (hZc hx) g)
  have : (Z.subgroupOf ψ.ker).Normal := Subgroup.normal_of_le_center hZ'c
  have hm0 : m ≠ 0 := by
    intro h
    rw [h, Nat.coprime_zero_left] at hcop
    exact hp.one_lt.ne' hcop
  have : (Z.subgroupOf ψ.ker).FiniteIndex := ⟨hm0⟩
  let τ := MonoidHom.transfer (G := ψ.ker) (A := Subgroup.center ψ.ker) (Subgroup.inclusion hZ'c)
  have hτ : ∀ x : ψ.ker, ((τ x : ψ.ker) : X) = (x : X) ^ m := by
    intro x
    have key : ∀ (k : ℕ) (g₀ : ψ.ker), g₀⁻¹ * x ^ k * g₀ ∈ Z.subgroupOf ψ.ker →
        g₀⁻¹ * x ^ k * g₀ = x ^ k := by
      intro k g₀ hk
      have hcen := Subgroup.mem_center_iff.1 (hZ'c hk) g₀
      have e : g₀ * (g₀⁻¹ * x ^ k * g₀) * g₀⁻¹ = x ^ k := by group
      conv_rhs => rw [← e]
      rw [hcen, mul_inv_cancel_right]
    simp only [τ, MonoidHom.transfer_eq_pow _ x key]
    rfl
  let E₁ : Subgroup X := τ.ker.map ψ.ker.subtype
  have hmemE₁ : ∀ x : X, x ∈ E₁ ↔ x ∈ ψ.ker ∧ x ^ m = 1 := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      have h1 := hτ y
      rw [MonoidHom.mem_ker.1 hy] at h1
      exact h1.symm
    · rintro ⟨hx, hxm⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      apply Subtype.ext
      apply Subtype.ext
      rw [hτ]
      exact hxm
  have hE₁ : E₁ ≤ ψ.ker := fun x hx => ((hmemE₁ x).1 hx).1
  have hE₁n : E₁.Normal := ⟨fun n hn g => by
    rw [hmemE₁] at hn ⊢
    exact ⟨ψ.normal_ker.conj_mem n hn.1 g, by rw [conj_pow, hn.2, mul_one, mul_inv_cancel]⟩⟩
  have hZE₁ : ∀ z ∈ Z, z ∈ E₁ → z = 1 := by
    intro z hz hzE
    have h1 : z ^ m = 1 := ((hmemE₁ z).1 hzE).2
    have h2 : z ^ p = 1 := by
      have h : (⟨z, hz⟩ : Z) ^ Nat.card Z = 1 := pow_card_eq_one'
      rw [hZp] at h
      simpa using congrArg Subtype.val h
    exact (pow_eq_one_iff_of_coprime hcop).1 ⟨h1, h2⟩
  have hdec : ∀ x ∈ ψ.ker, ∃ z ∈ Z, z⁻¹ * x ∈ E₁ := by
    intro x hx
    have hxm : x ^ m ∈ Z := Subgroup.pow_index_mem (Z.subgroupOf ψ.ker) (⟨x, hx⟩ : ψ.ker)
    have hcop' : (Nat.card Z).Coprime m := hZp ▸ hcop.symm
    obtain ⟨z, hz⟩ := (powCoprime hcop').surjective ⟨x ^ m, hxm⟩
    refine ⟨z, z.2, (hmemE₁ _).2 ⟨ψ.ker.mul_mem (ψ.ker.inv_mem (hZψ z.2)) hx, ?_⟩⟩
    have hzm : (z : X) ^ m = x ^ m := congrArg Subtype.val hz
    have hcomm : Commute (z : X)⁻¹ x :=
      (Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ (hZc z.2)) x).symm
    rw [hcomm.mul_pow, inv_pow, hzm, inv_mul_cancel]
  let ψ' : X ⧸ E₁ →* Q := QuotientGroup.lift E₁ ψ hE₁
  have hψ' : Function.Surjective ψ' := by
    intro q
    obtain ⟨x, rfl⟩ := hψ q
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hker' : ψ'.ker = Z.map (QuotientGroup.mk' E₁) := by
    rw [QuotientGroup.ker_lift]
    refine le_antisymm ?_ (Subgroup.map_mono hZψ)
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hzx⟩ := hdec x hx
    refine ⟨z, hz, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    exact hzx
  have hc' : ψ'.ker ≤ Subgroup.center (X ⧸ E₁) := by
    rw [hker']
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    induction g using QuotientGroup.induction_on with
    | H g =>
      have h := congrArg (QuotientGroup.mk' E₁) (Subgroup.mem_center_iff.1 (hZc hz) g)
      simpa using h
  have hcard' : Nat.card ψ'.ker = p := by
    rw [hker', ← hZp]
    have hinj : Function.Injective ((QuotientGroup.mk' E₁).comp Z.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro z hz
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hz
      exact Subtype.ext (hZE₁ z z.2 hz)
    have hr : Z.map (QuotientGroup.mk' E₁) = ((QuotientGroup.mk' E₁).comp Z.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hr]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have hY := ker_inf_commutator_eq_bot hp hQ ψ' hψ' hc' hcard'
  rw [hker'] at hY
  rw [eq_bot_iff]
  rintro z ⟨hz, hzc⟩
  have hmap : (commutator X).map (QuotientGroup.mk' E₁) ≤ commutator (X ⧸ E₁) := by
    simp only [_root_.commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have h1 : QuotientGroup.mk' E₁ z ∈ Z.map (QuotientGroup.mk' E₁) ⊓ commutator (X ⧸ E₁) :=
    ⟨⟨z, hz, rfl⟩, hmap ⟨z, hzc, rfl⟩⟩
  rw [hY, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact Subgroup.mem_bot.2 (hZE₁ z hz h1)

end CFSG.Quasithin.Vol2.Ch11.SecS.J4Mult
