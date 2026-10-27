module

public import CFSG.Quasithin.MS93.S46FFSec
public import CFSG.Quasithin.MS93.S46FF

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin

section General

variable {G : Type*} [Group G] {V : Type} [CommGroup V] (ρ : G →* MulAut V)

theorem commV_inv (g : G) {x : V} (hx : x ∈ commV ρ.range) : ρ g x ∈ commV ρ.range := by
  have h1 : ρ g x * x⁻¹ ∈ commV ρ.range :=
    Subgroup.subset_closure ⟨ρ g, mem_range_apply ρ g, x, rfl⟩
  have e : ρ g x = (ρ g x * x⁻¹) * x := by rw [inv_mul_cancel_right]
  rw [e]
  exact (commV ρ.range).mul_mem h1 hx

theorem commV_le_of_isPerfect [hG : Group.IsPerfect G] {W : Subgroup V}
    (hW : ∀ g, ∀ x ∈ commV ρ.range, ρ g x * x⁻¹ ∈ W) : commV ρ.range ≤ W := by
  set C : Subgroup V :=
    Subgroup.closure {w | ∃ g, ∃ x ∈ commV ρ.range, ρ g x * x⁻¹ = w} with hC
  have hCW : C ≤ W := by
    rw [Subgroup.closure_le]
    rintro _ ⟨g, x, hx, rfl⟩
    exact hW g x hx
  refine le_trans ?_ hCW
  let d : G → (V →* V ⧸ C) := fun g =>
    { toFun := fun v => QuotientGroup.mk (ρ g v * v⁻¹)
      map_one' := by simp
      map_mul' := fun a b => by
        rw [map_mul, mul_inv, mul_mul_mul_comm, QuotientGroup.mk_mul] }
  have hd : ∀ g v, d g v = QuotientGroup.mk (ρ g v * v⁻¹) := fun _ _ => rfl
  let D : G →* (V →* V ⧸ C) := MonoidHom.mk' d (fun g h => by
    ext v
    rw [MonoidHom.mul_apply, hd, hd, hd]
    set y := ρ h v * v⁻¹ with hy
    have hyX : y ∈ commV ρ.range := Subgroup.subset_closure ⟨ρ h, mem_range_apply ρ h, v, rfl⟩
    have hmem : ρ g y * y⁻¹ ∈ C := Subgroup.subset_closure ⟨g, y, hyX, rfl⟩
    have hyv : ρ h v = y * v := by rw [hy, inv_mul_cancel_right]
    have hgy : (QuotientGroup.mk (ρ g y) : V ⧸ C) = QuotientGroup.mk y :=
      QuotientGroup.eq_iff_div_mem.mpr (by rwa [div_eq_mul_inv])
    calc (QuotientGroup.mk (ρ (g * h) v * v⁻¹) : V ⧸ C)
        = QuotientGroup.mk (ρ g y * (ρ g v * v⁻¹)) := by
          rw [map_mul, MulAut.mul_apply, hyv, map_mul, mul_assoc]
      _ = QuotientGroup.mk (ρ g y) * QuotientGroup.mk (ρ g v * v⁻¹) := QuotientGroup.mk_mul _ _ _
      _ = QuotientGroup.mk (ρ g v * v⁻¹) * QuotientGroup.mk y := by rw [hgy, mul_comm])
  have : IsMulCommutative (V →* V ⧸ C) := ⟨⟨mul_comm⟩⟩
  have hker : D.ker = ⊤ := by
    rw [eq_top_iff, ← hG.commutator_eq_top]
    exact Abelianization.commutator_subset_ker D
  rw [commV, Subgroup.closure_le]
  rintro _ ⟨_, ⟨g, rfl⟩, v, rfl⟩
  have h1 : D g = 1 := MonoidHom.mem_ker.mp (hker ▸ Subgroup.mem_top g)
  have h2 := DFunLike.congr_fun h1 v
  rw [show D g v = d g v from rfl, hd, MonoidHom.one_apply, QuotientGroup.eq_one_iff] at h2
  exact h2

theorem mul_eq_one_of_alt {M : Type*} [CommGroup M] (ω : V →* V →* M) (halt : ∀ v, ω v v = 1)
    (v w : V) : ω v w * ω w v = 1 := by
  have e : ω (v * w) (v * w) = (ω v v * ω v w) * (ω w v * ω w w) := by
    rw [map_mul ω v w, MonoidHom.mul_apply, map_mul (ω v), map_mul (ω w)]
  rw [halt (v * w), halt v, halt w, one_mul, mul_one] at e
  exact e.symm

theorem exists_form_ne_one [Group.IsPerfect G] {M : Type*} [CommGroup M] (ω : V →* V →* M)
    (hinv : ∀ g v w, ω (ρ g v) (ρ g w) = ω v w) (hnd : ∀ v, (∀ w, ω v w = 1) → v = 1)
    (hskew : ∀ v w, ω v w = 1 → ω w v = 1) (hX : commV ρ.range ≠ ⊥) :
    ∃ x ∈ commV ρ.range, ∃ x' ∈ commV ρ.range, ω x x' ≠ 1 := by
  by_contra h
  push Not at h
  have key : ∀ v, ∀ x ∈ commV ρ.range, ω v x = 1 := by
    intro v
    have hle : commV ρ.range ≤ (ω v).ker := commV_le_of_isPerfect ρ fun g x hx => by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      have e1 : ω (ρ g v) (ρ g x) = ω v x := hinv g v x
      have hd : ρ g v * v⁻¹ ∈ commV ρ.range :=
        Subgroup.subset_closure ⟨ρ g, mem_range_apply ρ g, v, rfl⟩
      have e2 : ω (ρ g v * v⁻¹) (ρ g x) = 1 := h _ hd _ (commV_inv ρ g hx)
      have e3 : ω (ρ g v) (ρ g x) = ω (ρ g v * v⁻¹) (ρ g x) * ω v (ρ g x) := by
        rw [← MonoidHom.mul_apply, ← map_mul, inv_mul_cancel_right]
      rw [e3, e2, one_mul] at e1
      rw [e1, mul_inv_cancel]
    exact fun x hx => hle hx
  apply hX
  rw [eq_bot_iff]
  intro x hx
  exact hnd x fun w => hskew _ _ (key w x hx)

theorem exists_units_form [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) {Y : Type*} [CommGroup Y]
    (ω : V →* V →* Y) {x x' : V} (h : ω x x' ≠ 1) :
    ∃ f : V →* V →* ℂˣ, f x x' ≠ 1 ∧ ∀ v w v' w', ω v w = ω v' w' → f v w = f v' w' := by
  set S : Set Y := Set.range fun p : V × V => ω p.1 p.2 with hS
  set Y₀ : Subgroup Y := Subgroup.closure S with hY₀
  have hmem : ∀ v w, ω v w ∈ Y₀ := fun v w => Subgroup.subset_closure ⟨(v, w), rfl⟩
  have hS2 : ∀ y ∈ Y₀, y ^ 2 = 1 := by
    intro y hy
    have hle : Y₀ ≤ (powMonoidHom 2 : Y →* Y).ker := by
      rw [hY₀, Subgroup.closure_le]
      rintro _ ⟨⟨v, w⟩, rfl⟩
      show (ω v w) ^ 2 = 1
      rw [← map_pow, hV2, map_one]
    exact hle hy
  have hfg : Y₀.FG := (Subgroup.fg_iff Y₀).mpr ⟨S, hY₀.symm, Set.toFinite S⟩
  have : Group.FG ↥Y₀ := (Group.fg_iff_subgroup_fg Y₀).mpr hfg
  have : Finite ↥Y₀ := CommGroup.finite_of_fg_isMulTorsion ↥Y₀ fun y =>
    isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, Subtype.ext (by simpa using hS2 y y.2)⟩
  have : NeZero (Monoid.exponent ↥Y₀) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨χ, hχ⟩ : ∃ χ : ↥Y₀ →* ℂˣ, χ ⟨ω x x', hmem x x'⟩ ≠ χ 1 := by
    by_contra hcon
    push Not at hcon
    have := (CommGroup.forall_apply_eq_apply_iff ↥Y₀ (M := ℂ)).mp hcon
    exact h (congrArg Subtype.val this)
  let f : V →* V →* ℂˣ :=
    { toFun := fun v => χ.comp ((ω v).codRestrict Y₀ (hmem v))
      map_one' := by
        ext w
        have e : (⟨ω 1 w, hmem 1 w⟩ : ↥Y₀) = 1 := Subtype.ext (by simp)
        simp only [MonoidHom.comp_apply, MonoidHom.codRestrict_apply, MonoidHom.one_apply]
        rw [e, map_one]
      map_mul' := fun v v' => by
        ext w
        have e : (⟨ω (v * v') w, hmem (v * v') w⟩ : ↥Y₀) =
            ⟨ω v w, hmem v w⟩ * ⟨ω v' w, hmem v' w⟩ := Subtype.ext (by simp)
        simp only [MonoidHom.comp_apply, MonoidHom.codRestrict_apply, MonoidHom.mul_apply]
        rw [e, map_mul] }
  have hf : ∀ v w, f v w = χ ⟨ω v w, hmem v w⟩ := fun _ _ => rfl
  refine ⟨f, ?_, fun v w v' w' hvw => ?_⟩
  · rw [hf, ← map_one χ]
    exact hχ
  · rw [hf, hf]
    congr 1
    exact Subtype.ext hvw

theorem perpIn_inv {M : Type*} [CommGroup M] (f : V →* V →* M)
    (hf : ∀ g v w, f (ρ g v) (ρ g w) = f v w) {X U : Subgroup V}
    (hX : ∀ g, ∀ x ∈ X, ρ g x ∈ X) (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) :
    ∀ g, ∀ x ∈ perpIn f X U, ρ g x ∈ perpIn f X U := by
  intro g x hx
  refine ⟨hX g x hx.1, fun u hu => ?_⟩
  have e : ρ g (ρ g⁻¹ u) = u := by rw [map_inv, MulAut.apply_inv_self]
  have := hf g x (ρ g⁻¹ u)
  rw [e] at this
  rw [this]
  exact hx.2 _ (hU g⁻¹ u hu)

theorem exists_maximal_inv [Finite V] {R X : Subgroup V} (hRinv : ∀ g, ∀ u ∈ R, ρ g u ∈ R)
    (hRX : R ≤ X) (hRne : R ≠ X) :
    ∃ M₀ : Subgroup V, (∀ g, ∀ u ∈ M₀, ρ g u ∈ M₀) ∧ R ≤ M₀ ∧ M₀ ≤ X ∧ M₀ ≠ X ∧
      ∀ J : Subgroup V, (∀ g, ∀ u ∈ J, ρ g u ∈ J) → M₀ ≤ J → J ≤ X → J = M₀ ∨ J = X := by
  set 𝒮 : Set (Subgroup V) := {U | (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧ R ≤ U ∧ U ≤ X ∧ U ≠ X}
  obtain ⟨M₀, ⟨hinv, hR, hX, hne⟩, hmax⟩ := Set.exists_max_image 𝒮 (fun U => Nat.card U)
    (Set.toFinite 𝒮) ⟨R, hRinv, le_rfl, hRX, hRne⟩
  refine ⟨M₀, hinv, hR, hX, hne, fun J hJ hMJ hJX => ?_⟩
  by_cases hJX' : J = X
  · exact Or.inr hJX'
  · left
    exact (Subgroup.eq_of_le_of_card_ge hMJ (hmax J ⟨hJ, hR.trans hMJ, hJX, hJX'⟩)).symm

theorem form_eq_one_of_mem_secPre {M : Type*} [CommGroup M] {A : Subgroup (MulAut V)}
    {W U T : Subgroup V} (f : V →* V →* M) (hfA : ∀ a ∈ A, ∀ v w, f (a v) (a w) = f v w)
    (hTU : ∀ t ∈ T, ∀ u ∈ U, f t u = 1) {c : V} (hcT : c ∈ T) (hcA : c ∈ fixV A) {q : V}
    (hq : q ∈ secPre W U (commV (autSec A W U))) : f c q = 1 := by
  refine MonoidHom.mem_ker.mp (secPre_commV_le (Z := (f c).ker)
    (fun u hu => MonoidHom.mem_ker.mpr (hTU c hcT u hu)) (fun a ha w _ => ?_) hq)
  rw [MonoidHom.mem_ker, map_mul, map_inv]
  have := hfA a ha c w
  rw [hcA a ha] at this
  rw [this, mul_inv_cancel]

end General

section SL3Sec

variable {F : Type} [Field F] [Finite F] {V : Type} [CommGroup V] (ρ : SL3 F →* MulAut V)
  {W U : Subgroup V} (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U)

theorem inf_centSec_eq_bot (hnt : ∃ g s, secRho ρ hW hU g s ≠ s) {A : Subgroup (MulAut V)}
    (hAK : A ≤ ρ.range) (hA2 : ∀ a ∈ A, a ^ 2 = 1) : A ⊓ centSec W U = ⊥ := by
  rw [eq_bot_iff]
  rintro a ⟨haA, hac⟩
  rw [Subgroup.mem_bot]
  obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp (hAK haA)
  have hker : g ∈ (secRho ρ hW hU).ker :=
    MonoidHom.mem_ker.mpr ((secRho_eq_one_iff ρ hW hU g).mpr hac)
  have hc := ker_le_center (secRho ρ hW hU) hnt hker
  have h3 : ρ g ^ 3 = 1 := by rw [← map_pow, pow_three_eq_one_of_mem_center hc, map_one]
  exact eq_one_of_pow_three h3 (e := 1) (by simpa using hA2 _ haA)

end SL3Sec

theorem sd_trivial {F : Type} [Field F] [Fintype F] {n : ℕ} {V : Type} [CommGroup V] [Finite V]
    (h14 : MS14AS) (hSQ : SQTKQuot) (hsq : SQTKGroup (SL3 F))
    (hF : Fintype.card F = 2 ^ n) (hV2 : ∀ v : V, v ^ 2 = 1) (ρ : SL3 F →* MulAut V)
    {Y : Type} [CommGroup Y] (ω : V →* V →* Y) (halt : ∀ v, ω v v = 1)
    (hinv : ∀ g v w, ω (ρ g v) (ρ g w) = ω v w) (hnd : ∀ v, (∀ w, ω v w = 1) → v = 1)
    (hff : IsFFModule ρ.range) : ∀ g v, ρ g v = v := by
  have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have : Group.IsPerfect (SL3 F) := isPerfect_SL3
  by_contra hcon
  push Not at hcon
  obtain ⟨g₀, v₀, hv₀⟩ := hcon
  set X := commV ρ.range with hXdef
  have hXinv : ∀ g, ∀ x ∈ X, ρ g x ∈ X := fun g x hx => commV_inv ρ g hx
  have hXne : X ≠ ⊥ := by
    intro h
    have : ρ g₀ v₀ * v₀⁻¹ ∈ X := Subgroup.subset_closure ⟨ρ g₀, mem_range_apply ρ g₀, v₀, rfl⟩
    rw [h, Subgroup.mem_bot, mul_inv_eq_one] at this
    exact hv₀ this
  have hωskew : ∀ v w, ω v w = 1 → ω w v = 1 := fun v w h => by
    have := mul_eq_one_of_alt ω halt v w
    rwa [h, one_mul] at this
  obtain ⟨x₀, hx₀, x₀', hx₀', hω₀⟩ := exists_form_ne_one ρ ω hinv hnd hωskew hXne
  obtain ⟨f, hf₀, hfω⟩ := exists_units_form hV2 ω hω₀
  have hf1 : ∀ v w, ω v w = 1 → f v w = 1 := fun v w h => by
    rw [hfω v w 1 1 (by rw [h]; simp)]
    simp
  have hfinv : ∀ g v w, f (ρ g v) (ρ g w) = f v w := fun g v w => hfω _ _ _ _ (hinv g v w)
  have hfalt : ∀ v, f v v = 1 := fun v => hf1 v v (halt v)
  have hfskew : ∀ v w, f v w = 1 → f w v = 1 := fun v w h => by
    have := mul_eq_one_of_alt f hfalt v w
    rwa [h, one_mul] at this
  have hRinv := perpIn_inv ρ f hfinv hXinv hXinv
  have hRne : perpIn f X X ≠ X := fun h => by
    have hx : x₀ ∈ perpIn f X X := by rw [h]; exact hx₀
    exact hf₀ (hx.2 x₀' hx₀')
  obtain ⟨M₀, hM₀inv, hRM₀, hM₀X, hM₀ne, hM₀max⟩ :=
    exists_maximal_inv ρ hRinv (perpIn_le f X X) hRne
  obtain ⟨g₁, x₁, hx₁, hg₁⟩ : ∃ g, ∃ x ∈ X, ρ g x * x⁻¹ ∉ M₀ := by
    by_contra h
    push Not at h
    exact hM₀ne (le_antisymm hM₀X (commV_le_of_isPerfect ρ h))
  have hTinv := perpIn_inv ρ f hfinv hXinv hM₀inv
  have hTT : perpIn f X (perpIn f X M₀) = M₀ := perpIn_perpIn f hfskew hRM₀ hM₀X
  obtain ⟨A, hAK, hA1, hAe, hAcard⟩ := hff
  by_cases hTM : perpIn f X M₀ ≤ M₀
  ·
    have hntS := sec_nt ρ hXinv hM₀inv hx₁ hg₁
    have hirrS := sec_irr ρ hXinv hM₀inv hM₀X hM₀max
    have hfaith := inf_centSec_eq_bot ρ hXinv hM₀inv hntS hAK hAe.2
    have hffS := sec_ff ρ hXinv hM₀inv hM₀X hAK hA1 hAe hAcard hfaith
    obtain ⟨F', iF', fF', hFF', σ, θ, hθ⟩ := exists_natCoord (secRho ρ hXinv hM₀inv) h14 hSQ
      hsq hF' (sec_sq hV2) hirrS hntS hffS
    have : CharP F' 2 := FFC.charP_two_of_card_pow (hFF'.trans hF')
    have hAX : A ≤ stabSub X := hAK.trans (range_le_stabSub ρ hXinv)
    have hAM : A ≤ stabSub M₀ := hAK.trans (range_le_stabSub ρ hM₀inv)
    have hcĀ : Nat.card (autSec A X M₀) = Nat.card A := by
      have := card_autSec_mul hAX hAM
      rwa [hfaith, Subgroup.card_bot, mul_one] at this
    have hĀK : autSec A X M₀ ≤ (secRho ρ hXinv hM₀inv).range := by
      rw [range_secRho]
      exact autSec_mono hAK X M₀
    have hĀ1 : autSec A X M₀ ≠ ⊥ := by
      intro hbot
      apply hA1
      have h1 : Nat.card A = 1 := by rw [← hcĀ, hbot, Subgroup.card_bot]
      exact Subgroup.eq_bot_of_card_eq A h1
    have hlt := card_lt_of_coord hθ hĀK hĀ1 (isElemAbelian2_autSec ρ hXinv hM₀inv hAK hAe)
    rw [hcĀ] at hlt
    have hidx := (fixV (autSec A X M₀)).index_mul_card
    have hsec := card_sec_mul hM₀X
    have hfixX := card_inf_fixV_le_autSec hM₀X hAX (A := A)
    have hX' : Nat.card X ≤ Nat.card A * Nat.card ↥(X ⊓ fixV A) := by
      have h1 := card_sup_mul_card_inf X (fixV A)
      have h2 : Nat.card ↥(X ⊔ fixV A) ≤ Nat.card V := Subgroup.card_le_card_group _
      refine Nat.le_of_mul_le_mul_right ?_ (Nat.card_pos : 0 < Nat.card (fixV A))
      calc Nat.card X * Nat.card (fixV A) = Nat.card ↥(X ⊔ fixV A) * Nat.card ↥(X ⊓ fixV A) :=
            h1.symm
        _ ≤ Nat.card V * Nat.card ↥(X ⊓ fixV A) := Nat.mul_le_mul_right _ h2
        _ ≤ (Nat.card A * Nat.card (fixV A)) * Nat.card ↥(X ⊓ fixV A) :=
            Nat.mul_le_mul_right _ hAcard
        _ = Nat.card A * Nat.card ↥(X ⊓ fixV A) * Nat.card (fixV A) := by ring
    have hTM' : Nat.card (perpIn f X M₀) * Nat.card ↥(M₀ ⊓ fixV A) ≤
        Nat.card M₀ * Nat.card ↥(perpIn f X M₀ ⊓ fixV A) := by
      have h1 := card_sup_mul_card_inf (perpIn f X M₀) (M₀ ⊓ fixV A)
      have h2 : perpIn f X M₀ ⊔ M₀ ⊓ fixV A ≤ M₀ := sup_le hTM inf_le_left
      have h3 : perpIn f X M₀ ⊓ (M₀ ⊓ fixV A) = perpIn f X M₀ ⊓ fixV A := by
        rw [← inf_assoc, inf_eq_left.mpr hTM]
      rw [← h1, h3]
      exact Nat.mul_le_mul_right _ (Subgroup.card_le_of_le h2)
    have hpair := card_mul_le_of_pairing f (P₀ := perpIn f X M₀ ⊓ fixV A)
      (P := perpIn f X M₀) (Q₀ := M₀) (Q := secPre X M₀ (commV (autSec A X M₀))) inf_le_left
      (le_secPre hM₀X _)
      (fun p hp q hq => form_eq_one_of_mem_secPre (T := perpIn f X M₀) f
        (fun a ha v w => by
          obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp (hAK ha)
          exact hfinv g v w)
        (fun t ht u hu => ht.2 u hu) hp.1 hp.2 hq)
      (fun q hq h => by
        rw [← hTT]
        exact ⟨secPre_le _ _ _ hq, fun t ht => hfskew _ _ (h t ht)⟩)
    rw [← card_secPre hM₀X] at hpair
    set a := Nat.card A
    set cS := Nat.card (fixV (autSec A X M₀))
    set k := Nat.card (commV (autSec A X M₀))
    set idx := (fixV (autSec A X M₀)).index
    set cM := Nat.card ↥(M₀ ⊓ fixV A)
    set cT := Nat.card ↥(perpIn f X M₀ ⊓ fixV A)
    set t := Nat.card (perpIn f X M₀)
    set m := Nat.card M₀
    have hm : 0 < m := Nat.card_pos
    have hcT : 0 < cT := Nat.card_pos
    have hcM : 0 < cM := Nat.card_pos
    have hcS : 0 < cS := Nat.card_pos
    have hk1 : k * cT ≤ t := by
      refine Nat.le_of_mul_le_mul_right ?_ hm
      calc k * cT * m = k * m * cT := by ring
        _ ≤ t * m := hpair
    have hk2 : k * cM ≤ m := by
      refine Nat.le_of_mul_le_mul_right ?_ hcT
      calc k * cM * cT = k * cT * cM := by ring
        _ ≤ t * cM := Nat.mul_le_mul_right _ hk1
        _ ≤ m * cT := hTM'
    have hk3 : Nat.card (Sec X M₀) * k ≤ a * cS := by
      refine Nat.le_of_mul_le_mul_right ?_ hcM
      calc Nat.card (Sec X M₀) * k * cM = Nat.card (Sec X M₀) * (k * cM) := by ring
        _ ≤ Nat.card (Sec X M₀) * m := Nat.mul_le_mul_left _ hk2
        _ = Nat.card X := hsec
        _ ≤ a * Nat.card ↥(X ⊓ fixV A) := hX'
        _ ≤ a * (cS * cM) := Nat.mul_le_mul_left _ hfixX
        _ = a * cS * cM := by ring
    have hk4 : idx * k ≤ a := by
      refine Nat.le_of_mul_le_mul_right ?_ hcS
      calc idx * k * cS = idx * cS * k := by ring
        _ = Nat.card (Sec X M₀) * k := by rw [hidx]
        _ ≤ a * cS := hk3
    omega
  ·
    have hsupinv : ∀ {J : Subgroup V}, (∀ g, ∀ u ∈ J, ρ g u ∈ J) →
        ∀ g, ∀ u ∈ J ⊔ M₀, ρ g u ∈ J ⊔ M₀ := by
      intro J hJ g u hu
      obtain ⟨j, hj, m, hm, rfl⟩ := Subgroup.mem_sup.mp hu
      rw [map_mul]
      exact Subgroup.mul_mem_sup (hJ g j hj) (hM₀inv g m hm)
    have hsup : perpIn f X M₀ ⊔ M₀ = X := by
      rcases hM₀max _ (hsupinv hTinv) le_sup_right (sup_le (perpIn_le f X M₀) hM₀X) with h | h
      · exact absurd (le_sup_left.trans h.le) hTM
      · exact h
    have hU'inv : ∀ g, ∀ u ∈ perpIn f X M₀ ⊓ M₀, ρ g u ∈ perpIn f X M₀ ⊓ M₀ :=
      fun g u hu => ⟨hTinv g u hu.1, hM₀inv g u hu.2⟩
    have hirr' : ∀ J : Subgroup V, (∀ g, ∀ w ∈ J, ρ g w ∈ J) → perpIn f X M₀ ⊓ M₀ ≤ J →
        J ≤ perpIn f X M₀ → J = perpIn f X M₀ ⊓ M₀ ∨ J = perpIn f X M₀ := by
      intro J hJ hUJ hJT
      rcases hM₀max (J ⊔ M₀) (hsupinv hJ) le_sup_right
          (sup_le (hJT.trans (perpIn_le f X M₀)) hM₀X) with h | h
      · left
        exact le_antisymm (le_inf hJT (le_sup_left.trans h.le)) hUJ
      · right
        refine le_antisymm hJT fun t ht => ?_
        have htJ : t ∈ J ⊔ M₀ := by rw [h]; exact perpIn_le f X M₀ ht
        obtain ⟨j, hj, m, hm, rfl⟩ := Subgroup.mem_sup.mp htJ
        have hmT : m ∈ perpIn f X M₀ := by
          have := (perpIn f X M₀).mul_mem ((perpIn f X M₀).inv_mem (hJT hj)) ht
          rwa [inv_mul_cancel_left] at this
        exact J.mul_mem hj (hUJ ⟨hmT, hm⟩)
    obtain ⟨g₂, t₂, ht₂, hg₂⟩ : ∃ g, ∃ t ∈ perpIn f X M₀, ρ g t * t⁻¹ ∉ perpIn f X M₀ ⊓ M₀ := by
      by_contra h
      push Not at h
      apply hg₁
      have hx₁' : x₁ ∈ perpIn f X M₀ ⊔ M₀ := by rw [hsup]; exact hx₁
      obtain ⟨t, ht, m, hm, rfl⟩ := Subgroup.mem_sup.mp hx₁'
      have e : ρ g₁ (t * m) * (t * m)⁻¹ = (ρ g₁ t * t⁻¹) * (ρ g₁ m * m⁻¹) := by
        rw [map_mul, mul_inv, mul_mul_mul_comm]
      rw [e]
      exact M₀.mul_mem (h g₁ t ht).2 (M₀.mul_mem (hM₀inv g₁ m hm) (M₀.inv_mem hm))
    have hntS' := sec_nt ρ hTinv hU'inv ht₂ hg₂
    have hirrS' := sec_irr ρ hTinv hU'inv inf_le_left hirr'
    have hfaith' := inf_centSec_eq_bot ρ hTinv hU'inv hntS' hAK hAe.2
    have hffS' := sec_ff ρ hTinv hU'inv inf_le_left hAK hA1 hAe hAcard hfaith'
    obtain ⟨F', iF', fF', -, σ, θ, hθ⟩ := exists_natCoord (secRho ρ hTinv hU'inv) h14 hSQ hsq
      hF' (sec_sq hV2) hirrS' hntS' hffS'
    have h1 : ∀ u ∈ perpIn f X M₀ ⊓ M₀, ∀ w ∈ perpIn f X M₀, f u w = 1 :=
      fun u hu w hw => hfskew _ _ (hw.2 u hu.2)
    have h2 : ∀ w ∈ perpIn f X M₀, ∀ u ∈ perpIn f X M₀ ⊓ M₀, f w u = 1 :=
      fun w hw u hu => hw.2 u hu.2
    have hg := form_eq_one_of_coord hθ (secForm f h1 h2) fun k hk s s' => by
      obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hk
      exact secForm_inv ρ hTinv hU'inv f h1 h2 hfinv g s s'
    refine hTM (le_trans ?_ hTT.le)
    intro t ht
    exact ⟨perpIn_le f X M₀ ht, fun t' ht' => eq_one_of_secForm_eq_one hg ht ht'⟩

end CFSG.Quasithin.MS93.S46
