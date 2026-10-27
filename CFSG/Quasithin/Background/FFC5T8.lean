module

public import CFSG.Quasithin.Background.FFC5T6
public import CFSG.Quasithin.Background.FFC5T7
public import CFSG.Quasithin.Background.FFC5T3

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.JonesParshall Matrix

section T8

variable {V : Type} [CommGroup V]

theorem NatQuot3.nonempty_equiv {L : Subgroup (MulAut V)} {U Z : Subgroup V} (D : NatQuot3 L U Z) :
    Nonempty (↥L ≃* ↥(StatedSL 3 (ZMod 2))) :=
  ⟨(MulEquiv.ofBijective D.ρ ⟨D.inj, D.surj⟩).symm.trans (specialLinearGroupEquivStatedSL 3 (ZMod 2))⟩

theorem NatQuot3.card_eq {L : Subgroup (MulAut V)} {U Z : Subgroup V} (D : NatQuot3 L U Z) (hZU : Z ≤ U) :
    Nat.card ↥U = 2 ^ 3 * Nat.card ↥Z := by
  have h1 := Subgroup.card_ker_mul_card_range D.θ
  have hker : D.θ.ker = Z.subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, D.θ_ker]
    rfl
  have hrange : Nat.card D.θ.range = 2 ^ 3 := by
    rw [MonoidHom.range_eq_top.2 D.θ_surj, Subgroup.card_top,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 3 → ZMod 2) ≃ (Fin 3 → ZMod 2))]
    simp [Nat.card_eq_fintype_card, ZMod.card]
  have hZ : Nat.card ↥(Z.subgroupOf U) = Nat.card ↥Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv
  rw [hker, hZ, hrange] at h1
  rw [← h1, mul_comm]

theorem perfect_of_equiv_sl3 {X : Subgroup (MulAut V)} (e : ↥X ≃* ↥(StatedSL 3 (ZMod 2))) :
    ⁅X, X⁆ = X := by
  have hp : Group.IsPerfect SL3F2 :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := ZMod 2) (n := 3) (le_refl 3)
  have h1 : Group.IsPerfect ↥(StatedSL 3 (ZMod 2)) :=
    Group.IsPerfect.ofSurjective (f := (specialLinearGroupEquivStatedSL 3 (ZMod 2)).toMonoidHom)
      (specialLinearGroupEquivStatedSL 3 (ZMod 2)).surjective
  have h2 : Group.IsPerfect ↥X := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Subgroup.isPerfect_iff.mp h2

end T8

section Direct

variable {V : Type} [CommGroup V]

theorem DirectSumOfCopies.one {D : FFModel} {L : Subgroup (MulAut V)} {U : Subgroup V} {π : D.Gam →* ↥L}
    (h : D.RealizesVia L U ⊥ π) : DirectSumOfCopies L U ⊥ D 1 := by
  refine ⟨fun _ => U, π, fun _ => bot_le, fun i => ?_, ?_, fun _ => h⟩
  · have h1 : (⨆ (j : Fin 1) (_ : j ≠ i), U) = ⊥ :=
      iSup₂_eq_bot.2 fun j hj => absurd (Subsingleton.elim j i) hj
    show U ⊓ (⊥ ⊔ ⨆ (j : Fin 1) (_ : j ≠ i), U) = ⊥
    rw [h1, bot_sup_eq, inf_bot_eq]
  · show ⊥ ⊔ ⨆ _ : Fin 1, U = U
    rw [iSup_const, bot_sup_eq]

theorem DirectSumOfCopies.zmod {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {n k : ℕ}
    {L : Subgroup (MulAut V)} {U Z : Subgroup V}
    (h : DirectSumOfCopies L U Z (FFModel.nat (StatedSL n K)) k) :
    DirectSumOfCopies L U Z (FFModel.nat (StatedSL n (ZMod 2))) k := by
  obtain ⟨I, π, h1, h2, h3, h4⟩ := h
  exact ⟨I, π.comp (slOfZMod (ringEquivZModTwo K hK) n), h1, h2, h3,
    fun i => realizesVia_zmod hK (h4 i)⟩

theorem DirectSumOfCopies.restrict_exact {D : FFModel} {L : Subgroup (MulAut V)} {U Z U₀ : Subgroup V}
    {k : ℕ} (h : DirectSumOfCopies L U Z D k) (hU : U = U₀ ⊔ Z)
    (hinv : ∀ g : ↥L, ∀ u ∈ U₀, (g : MulAut V) u ∈ U₀) (hbot : U₀ ⊓ Z = ⊥) :
    DirectSumOfCopies L U₀ ⊥ D k := by
  obtain ⟨I, π, hZI, hind, hsup, hreal⟩ := h
  set I' : Fin k → Subgroup V := fun i => I i ⊓ U₀ with hI'
  have hIU : ∀ i, I i ≤ U := fun i => hsup ▸ (le_iSup I i).trans le_sup_right
  have hIsplit : ∀ i, I i ≤ I' i ⊔ Z := by
    intro i y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 (hU ▸ hIU i hy)
    have : a ∈ I i := by
      have := (I i).mul_mem hy ((I i).inv_mem (hZI i hb))
      simpa using this
    exact Subgroup.mul_mem_sup ⟨this, ha⟩ hb
  have hsupI : ∀ i, I' i ⊔ Z = I i := fun i =>
    le_antisymm (sup_le inf_le_left (hZI i)) (hIsplit i)
  refine ⟨I', π, fun _ => bot_le, fun i => ?_, ?_, fun i => ?_⟩
  · have hmono : (⨆ (j : Fin k) (_ : j ≠ i), I' j) ≤ ⨆ (j : Fin k) (_ : j ≠ i), I j :=
      iSup₂_mono fun j _ => inf_le_left
    show I' i ⊓ (⊥ ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I' j) = ⊥
    rw [bot_sup_eq, eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have h1 : x ∈ I i ⊓ (Z ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j) :=
      ⟨hx1.1, Subgroup.mem_sup_right (hmono hx2)⟩
    rw [hind i] at h1
    have h2 : x ∈ U₀ ⊓ Z := ⟨hx1.2, h1⟩
    rw [hbot] at h2
    exact h2
  · apply le_antisymm
    · exact sup_le bot_le (iSup_le fun i => inf_le_right)
    · have h2 : ⨆ i, I i ≤ (⨆ i, I' i) ⊔ Z :=
        iSup_le fun i => (hIsplit i).trans (sup_le_sup_right (le_iSup I' i) Z)
      have h3 : U₀ ≤ (⨆ i, I' i) ⊔ Z := by
        calc U₀ ≤ U := by rw [hU]; exact le_sup_left
          _ = Z ⊔ ⨆ i, I i := hsup.symm
          _ ≤ (⨆ i, I' i) ⊔ Z := sup_le le_sup_right h2
      have hle : (⨆ i, I' i) ≤ U₀ := iSup_le fun i => inf_le_right
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 (h3 hx)
      have hb' : b ∈ U₀ := by
        have := U₀.mul_mem (U₀.inv_mem (hle ha)) hx
        simpa using this
      have hb0 : b ∈ U₀ ⊓ Z := ⟨hb', hb⟩
      rw [hbot, Subgroup.mem_bot] at hb0
      rw [hb0, mul_one]
      exact Subgroup.mem_sup_right ha
  · have hres := realizesVia_restrict (hreal i) (hsupI i)
      (fun g u hu => ⟨(hreal i).2.2.2.1 g u hu.1, hinv g u hu.2⟩)
    have hZ : Z ⊓ I' i = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hx1, hx2⟩
      have : x ∈ U₀ ⊓ Z := ⟨hx2.2, hx1⟩
      rw [hbot] at this
      exact this
    rwa [hZ] at hres

end Direct

section Pieces

variable {V : Type} [CommGroup V]

namespace B510Fa

variable {G G₁ G₂ : Subgroup (MulAut V)} (h : B510Fa G G₁ G₂)

include h in
theorem hu_of_one {u : V} (hu : u ∉ commV G₁ ⊔ fixV G₁)
    (hvan : ∃ m : Additive ↥(fixV G₁), ∀ g : ↥G₂,
      ((Additive.toMul (cocyF h.hc₂ u g - (muW h.hLW₂ g m - m)) : ↥(fixV G₁)) : V) ∈ fixV G) :
    ∃ u : V, u ∉ commV G₁ ⊔ fixV G₁ ∧ ∀ g ∈ G₂, g u * u⁻¹ ∈ fixV G := by
  obtain ⟨m, hm⟩ := hvan
  refine ⟨u * (((Additive.toMul m : ↥(fixV G₁)) : V))⁻¹, ?_, fun g hg => ?_⟩
  · intro hmem
    apply hu
    have h1 : u = (u * (((Additive.toMul m : ↥(fixV G₁)) : V))⁻¹) *
        ((Additive.toMul m : ↥(fixV G₁)) : V) := by simp
    rw [h1]
    exact (commV G₁ ⊔ fixV G₁).mul_mem hmem
      (Subgroup.mem_sup_right ((Additive.toMul m : ↥(fixV G₁)).2))
  · have h1 := hm ⟨g, hg⟩
    have h2 : ((Additive.toMul (cocyF h.hc₂ u ⟨g, hg⟩ - (muW h.hLW₂ ⟨g, hg⟩ m - m)) : ↥(fixV G₁)) : V) =
        g (u * (((Additive.toMul m : ↥(fixV G₁)) : V))⁻¹) *
          (u * (((Additive.toMul m : ↥(fixV G₁)) : V))⁻¹)⁻¹ := by
      rw [toMul_sub, Subgroup.coe_div, muW_sub_apply]
      show g u * u⁻¹ / (g ((Additive.toMul m : ↥(fixV G₁)) : V) * ((Additive.toMul m : ↥(fixV G₁)) : V)⁻¹) = _
      rw [map_mul, map_inv, div_eq_mul_inv]
      simp [mul_comm, mul_left_comm, mul_assoc]
    rw [h2] at h1
    exact h1

include h in
theorem hT_of_top
    (hT₀ : (⊤ : Subgroup ↥(fixV G₁)) =
      commV (autSub G₂ (fixV G₁)) ⊔ fixV (autSub G₂ (fixV G₁))) :
    fixV G₁ = commV G₂ ⊔ fixV G := by
  have := congrArg (Subgroup.map (fixV G₁).subtype) hT₀
  rw [map_top_eq, Subgroup.map_sup, map_fixV_eq h] at this
  refine le_antisymm ?_ (sup_le h.commV_le (B1.fixV_le_fixV h.G₁_le))
  rw [this]
  exact sup_le_sup_right (map_commV_le h) _

include h in
theorem case_a3_one
    [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hnat : BinaryNaturalSL G₁ (commV G₁) ⊥ 3 1)
    (hidx : (commV G₁ ⊔ fixV G₁).index = 2) (hgood : GoodFactor (autSub G₂ (fixV G₁)))
    (hV₂ : fixV G₁ = commV G₂ ⊔ fixV G) (hS : BinaryNaturalSL G₂ (fixV G₁) (fixV G) 3 1) :
    B56Case3 G ∨ B56Case5 G := by
  obtain ⟨D⟩ := exists_natQuot3 hS
  have hCW : fixV G ≤ fixV G₁ := B1.fixV_le_fixV h.G₁_le
  have hcard : Nat.card ↥(fixV G₁) = 8 * Nat.card ↥(fixV G) := by
    rw [D.card_eq hCW]
    norm_num
  obtain ⟨u, hu⟩ : ∃ u : V, u ∉ commV G₁ ⊔ fixV G₁ := by
    by_contra hcon
    push Not at hcon
    have : commV G₁ ⊔ fixV G₁ = ⊤ := eq_top_iff.2 fun x _ => hcon x
    rw [← Subgroup.index_eq_one] at this
    omega
  rcases h.l3_dichotomy hV D hV₂ hcard u with hvan | hz
  · exact Or.inl (h.case3_of hV hnat hidx hgood (h.hu_of_one hu hvan))
  · right
    have hiso := D.nonempty_equiv
    refine h.case5_of hnat hidx hV₂ (Or.inl ⟨hiso, 1, by norm_num, ?_⟩)
    obtain ⟨π, hπ⟩ := BinaryNaturalSL.exists_zmod hS
    have hres := realizesVia_restrict hπ (U' := commV G₂) hV₂.symm (commV_invariant_coe G₂)
    rw [inf_comm, hz] at hres
    exact DirectSumOfCopies.one hres

include h in
theorem case_b_one [Finite V] (hnat : BinaryNaturalSL G₁ (commV G₁) ⊥ 3 1)
    (hidx : (commV G₁ ⊔ fixV G₁).index = 2) (hV₂ : fixV G₁ = commV G₂ ⊔ fixV G)
    (hex : commV G₂ ⊓ fixV G = ⊥) (hiso : Nonempty (↥G₂ ≃* ↥(StatedSL 3 (ZMod 2))))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (hd : DirectSumOfCopies G₂ (fixV G₁) (fixV G) (FFModel.nat (StatedSL 3 K)) 2) : B56Case5 G :=
  h.case5_of hnat hidx hV₂ (Or.inl ⟨hiso, 2, le_rfl,
    DirectSumOfCopies.restrict_exact (DirectSumOfCopies.zmod hK hd) hV₂ (commV_invariant_coe G₂) hex⟩)

end B510Fa

end Pieces

end FFC

end CFSG.Quasithin
