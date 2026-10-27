module

public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcRootsB
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcWeylTypes

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


private theorem ggKGEc_rootChar_zetaPow_eq_one_iff_charVal {τ : Tag} {p : ℕ} [NeZero p]
    {L : Type} [Field L] {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p)
    (z : Fin τ.rank → ZMod p) (v : Fin τ.rank → ℤ) :
    rootChar (fun i => ζ ^ (z i).val) v = 1 ↔ CFSG.RankThree.E6.charVal z v = 0 := by
  have h : rootChar (fun i => ζ ^ (z i).val) v = ζ ^ (∑ i, v i * ((z i).val : ℤ)) := by
    rw [rootChar, ← Finset.prod_zpow_eq_zpow_sum Finset.univ ζ (fun i => v i * ((z i).val : ℤ))]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
  rw [h, hζ.zpow_eq_one_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd, CFSG.RankThree.E6.charVal]
  push_cast
  simp only [ZMod.natCast_zmod_val]

private theorem ggKGEc_redMod_add {τ : Tag} {p : ℕ} (v v' : Fin τ.rank → ℤ) :
    TableBExc.redMod τ p (v + v') = TableBExc.redMod τ p v + TableBExc.redMod τ p v' := by
  funext i
  simp [TableBExc.redMod, Pi.add_apply]

private theorem ggKGEc_torusAct_add {τ : Tag} {p : ℕ} [NeZero p] (w : WeylGroup τ)
    (x y : Fin τ.rank → ZMod p) :
    TableBExc.torusAct τ p w (x + y) =
      TableBExc.torusAct τ p w x + TableBExc.torusAct τ p w y := by
  rw [TableBExc.torusAct, TableBExc.torusAct, TableBExc.torusAct]
  have h : TableBExc.redMod τ p (TableBExc.liftMod τ p (x + y)) =
      TableBExc.redMod τ p (TableBExc.liftMod τ p x + TableBExc.liftMod τ p y) := by
    rw [TableBExc.redMod_liftMod, ggKGEc_redMod_add, TableBExc.redMod_liftMod,
      TableBExc.redMod_liftMod]
  have h2 := TableBExc.redMod_smul_eq (τ := τ) (p := p) w h
  rw [smul_add, ggKGEc_redMod_add] at h2
  exact h2

private theorem ggKGEc_isElemAbelian_zpowers {τ : Tag} {p : ℕ} {v : WeylGroup τ}
    (hv : orderOf v = p) : CFSG.Open.IsElemAbelian p (Subgroup.zpowers v) := by
  constructor
  · refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
  · intro x hx
    have hdvd : orderOf x ∣ orderOf v := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← hk, orderOf_zpow]
      exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
    rw [hv] at hdvd
    exact (orderOf_dvd_iff_pow_eq_one).1 hdvd

theorem ggKGExc_no_transvection
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 ≤ p) (hτ6 : τ = .E6 → 5 ≤ p) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    {v : WeylGroup τ}
    (hv : orderOf v = p) :
    ¬ ∀ x : Fin τ.rank → ℤ, ∃ c : ℤ, ∀ i, (p : ℤ) ∣ (v • x - x) i - c * γ i := by
  intro h
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hrank : 1 ≤ τ.rank := by rcases hτ with rfl | rfl | rfl | rfl <;> decide
  have hoff : GGWeylNoOffender τ p := by
    rcases hτ with rfl | rfl | rfl | rfl
    · have := hτ6 rfl
      exact NoOffExc.ggWeylNoOffender_E6 hp (by omega) (by omega)
    · exact NoOffExc.ggWeylNoOffender_E7 hp (by omega)
    · exact NoOffExc.ggWeylNoOffender_E8 hp (by omega)
    · exact NoOffExc.ggWeylNoOffender_F4 hp (by omega)
  let f : (Fin τ.rank → ZMod p) →+ (Fin τ.rank → ZMod p) :=
    { toFun := fun x => TableBExc.torusAct τ p v x - x
      map_zero' := by
        have h0 : TableBExc.liftMod τ p (0 : Fin τ.rank → ZMod p) = 0 := by
          funext i; simp [TableBExc.liftMod]
        show TableBExc.redMod τ p (v • TableBExc.liftMod τ p 0) - 0 = 0
        rw [h0, smul_zero]
        funext i
        simp [TableBExc.redMod]
      map_add' := fun x y => by rw [ggKGEc_torusAct_add]; abel }
  have hM : Module (ZMod p) (Fin τ.rank → ZMod p) := inferInstance
  have hVcard : Nat.card (Fin τ.rank → ZMod p) = p ^ τ.rank := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hrange : f.range ≤ AddSubgroup.zmultiples (TableBExc.redMod τ p γ) := by
    rintro y ⟨x, rfl⟩
    obtain ⟨c, hc⟩ := h (TableBExc.liftMod τ p x)
    have hred : TableBExc.redMod τ p
        (v • TableBExc.liftMod τ p x - TableBExc.liftMod τ p x) =
        (c : ZMod p) • TableBExc.redMod τ p γ := by
      funext i
      have hci := hc i
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hci
      simp only [TableBExc.redMod, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sub,
        Int.cast_mul] at hci ⊢
      linear_combination hci
    have hsub : TableBExc.redMod τ p (v • TableBExc.liftMod τ p x - TableBExc.liftMod τ p x)
        = TableBExc.redMod τ p (v • TableBExc.liftMod τ p x) - x := by
      rw [TableBExc.redMod_sub, TableBExc.redMod_liftMod]
    change TableBExc.redMod τ p (v • TableBExc.liftMod τ p x) - x ∈
      AddSubgroup.zmultiples (TableBExc.redMod τ p γ)
    rw [← hsub, hred]
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨c, ?_⟩
    funext i
    simp only [Pi.smul_apply, zsmul_eq_mul, smul_eq_mul]
  have hg : p • TableBExc.redMod τ p γ = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod p) p (TableBExc.redMod τ p γ), ZMod.natCast_self]
    simp
  have hcardg : Nat.card (AddSubgroup.zmultiples (TableBExc.redMod τ p γ)) ≤ p := by
    rw [Nat.card_zmultiples]
    exact Nat.le_of_dvd hp.pos (addOrderOf_dvd_of_nsmul_eq_zero hg)
  have hlerange : Nat.card f.range ≤ p := by
    have hinj : Function.Injective
        (fun x : f.range => (⟨x.1, hrange x.2⟩ : AddSubgroup.zmultiples (TableBExc.redMod τ p γ))) :=
      fun a b hab => Subtype.ext (congrArg (fun z : AddSubgroup.zmultiples (TableBExc.redMod τ p γ) => (z : Fin τ.rank → ZMod p)) hab)
    exact (Nat.card_le_card_of_injective _ hinj).trans hcardg
  have hfix : Nat.card {x : Fin τ.rank → ZMod p // TableBExc.torusAct τ p v x = x}
      = Nat.card f.ker := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun x => ?_
    rw [AddMonoidHom.mem_ker]
    rw [show f x = TableBExc.torusAct τ p v x - x from rfl]
    exact sub_eq_zero.symm
  have hker : p ^ (τ.rank - 1) ≤ Nat.card f.ker := by
    have h := AddSubgroup.card_ker_mul_card_range f
    rw [hVcard] at h
    have hpos : 0 < Nat.card f.range := Nat.card_pos
    have : p ^ (τ.rank - 1) * Nat.card f.range ≤ Nat.card f.ker * Nat.card f.range := by
      rw [h]
      calc p ^ (τ.rank - 1) * Nat.card f.range ≤ p ^ (τ.rank - 1) * p :=
            Nat.mul_le_mul_left _ hlerange
        _ = p ^ τ.rank := by rw [mul_comm, ← pow_succ', Nat.sub_add_cancel hrank]
    exact Nat.le_of_mul_le_mul_right this hpos
  have hcard : p ^ (τ.rank - 1) ≤
      Nat.card {x : Fin τ.rank → ZMod p // TableBExc.torusAct τ p v x = x} := by
    rw [hfix]; exact hker
  have hA : CFSG.Open.IsElemAbelian p (Subgroup.zpowers v) := ggKGEc_isElemAbelian_zpowers hv
  have hA1 : Subgroup.zpowers v ≠ ⊥ := by
    intro hbot
    have hv1 : v = 1 := by
      have : v ∈ (⊥ : Subgroup (WeylGroup τ)) := hbot ▸ Subgroup.mem_zpowers v
      simpa using this
    rw [hv1] at hv
    simp at hv
    omega
  have hoffv := hoff (Subgroup.zpowers v) hA hA1
  have hcardA : Nat.card (Subgroup.zpowers v) = p := by rw [Nat.card_zpowers, hv]
  have hfixA : Nat.card {x : Fin τ.rank → ZMod p //
      ∀ a ∈ Subgroup.zpowers v, TableBExc.torusAct τ p a x = x}
      = Nat.card {x : Fin τ.rank → ZMod p // TableBExc.torusAct τ p v x = x} := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun x => ?_
    constructor
    · intro hx; exact hx v (Subgroup.mem_zpowers v)
    · intro hx a ha
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
      rw [← hk]
      have hperm : TableBExc.torusPerm τ p v x = x := by
        rw [TableBExc.torusPerm_apply]; exact hx
      have hpt := Function.IsFixedPt.perm_zpow hperm k
      rw [← map_zpow] at hpt
      exact hpt
  rw [hcardA, hfixA] at hoffv
  have hlow : p ^ τ.rank ≤
      p * Nat.card {x : Fin τ.rank → ZMod p // TableBExc.torusAct τ p v x = x} := by
    calc p ^ τ.rank = p * p ^ (τ.rank - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel hrank]
      _ ≤ p * _ := Nat.mul_le_mul_left p hcard
  omega

private theorem ggKGEc_redMod_mem_span {τ : Tag} {p : ℕ} [Fact p.Prime] {γ y : Fin τ.rank → ℤ}
    (h : ∀ z : Fin τ.rank → ZMod p, CFSG.RankThree.E6.charVal z γ = 0 →
      CFSG.RankThree.E6.charVal z y = 0) :
    ∃ c : ZMod p, TableBExc.redMod τ p y = c • TableBExc.redMod τ p γ := by
  let f : (Fin τ.rank → ZMod p) →ₗ[ZMod p] ZMod p :=
    ∑ i, (γ i : ZMod p) • (LinearMap.proj i : (Fin τ.rank → ZMod p) →ₗ[ZMod p] ZMod p)
  have hf : ∀ z, f z = CFSG.RankThree.E6.charVal z γ := by
    intro z
    simp only [f, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
      CFSG.RankThree.E6.charVal, smul_eq_mul]
  let g : (Fin τ.rank → ZMod p) →ₗ[ZMod p] ZMod p :=
    ∑ i, (y i : ZMod p) • (LinearMap.proj i : (Fin τ.rank → ZMod p) →ₗ[ZMod p] ZMod p)
  have hgfun : ∀ z, g z = CFSG.RankThree.E6.charVal z y := by
    intro z
    simp only [g, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
      CFSG.RankThree.E6.charVal, smul_eq_mul]
  have hle : (⨅ _ : Fin 1, LinearMap.ker f) ≤ LinearMap.ker g := by
    intro z hz
    have hz1 : z ∈ f.ker := by simpa using hz
    rw [LinearMap.mem_ker, hf] at hz1
    rw [LinearMap.mem_ker, hgfun]
    exact h z hz1
  have hg : g ∈ Submodule.span (ZMod p) (Set.range (fun _ : Fin 1 => f)) :=
    @mem_span_of_iInf_ker_le_ker (Fin 1) (ZMod p) (Fin τ.rank → ZMod p) _ _
      (Pi.module (Fin τ.rank) (fun _ => ZMod p) (ZMod p)) _ (fun _ => f) g hle
  have hg' : g ∈ Submodule.span (ZMod p) ({f} : Set ((Fin τ.rank → ZMod p) →ₗ[ZMod p] ZMod p)) := by
    simpa using hg
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hg'
  refine ⟨c, ?_⟩
  funext i
  have hci := congrFun (congrArg DFunLike.coe hc) (Pi.single i 1 : Fin τ.rank → ZMod p)
  change c * f (Pi.single i 1 : Fin τ.rank → ZMod p) = g (Pi.single i 1) at hci
  rw [hf, hgfun] at hci
  have h1 : CFSG.RankThree.E6.charVal (Pi.single i 1 : Fin τ.rank → ZMod p) y =
      (y i : ZMod p) := by
    rw [CFSG.RankThree.E6.charVal, Finset.sum_eq_single i]
    · simp
    · intro j _ hj; rw [Pi.single_eq_of_ne (M := fun _ => ZMod p) hj, mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have h2 : CFSG.RankThree.E6.charVal (Pi.single i 1 : Fin τ.rank → ZMod p) γ =
      (γ i : ZMod p) := by
    rw [CFSG.RankThree.E6.charVal, Finset.sum_eq_single i]
    · simp
    · intro j _ hj; rw [Pi.single_eq_of_ne (M := fun _ => ZMod p) hj, mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [h1, h2] at hci
  simpa [TableBExc.redMod] using hci.symm

private theorem ggKGEc_rootReflection_mem_familyStabilizer {τ : Tag} {k : Type} [Field k]
    {ι : Type} (a : ι → Fin τ.rank → kˣ) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hker : ∀ i, rootChar (a i) γ = 1) :
    rootReflection γ ∈ familyStabilizer a := by
  intro i v
  rw [rootReflection]
  rw [dif_pos hγ]
  obtain ⟨c, hc⟩ := exists_conj_simple_smul
    (Classical.choose (isRoot_iff_exists_smul_single.1 hγ))
    (Classical.choose (Classical.choose_spec (isRoot_iff_exists_smul_single.1 hγ))) v
  have hspec := Classical.choose_spec (Classical.choose_spec (isRoot_iff_exists_smul_single.1 hγ))
  rw [hc, hspec, rootChar_sub, rootChar_zsmul, hker i, one_zpow, inv_one, mul_one]

private theorem ggKGEc_eq_one_of_fixRoot
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    {k : Type} [Field k] {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hτ6 : τ = .E6 → 5 ≤ p) {ζ : k}
    (hζ : IsPrimitiveRoot ζ p) {ι : Type} (a : ι → Fin τ.rank → kˣ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hall : ∀ b : Fin τ.rank → kˣ, (∀ j, b j ^ p = 1) → rootChar b γ = 1 → ∃ i, a i = b)
    {w : WeylGroup τ} (hw : w ∈ familyStabilizer a) (hwγ : w • γ = γ) : w = 1 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  let ζ' : kˣ := (hζ.isUnit hp.ne_zero).unit
  have hζ'coe : (ζ' : k) = ζ := (hζ.isUnit hp.ne_zero).unit_spec
  have hζ' : IsPrimitiveRoot ζ' p := by
    apply IsPrimitiveRoot.mk
    · apply Units.ext
      rw [Units.val_pow_eq_pow_val, hζ'coe, hζ.pow_eq_one, Units.val_one]
    · intro l hl
      have h1 : ζ ^ l = 1 := by
        have := congrArg (fun u : kˣ => (u : k)) hl
        simpa [hζ'coe] using this
      exact (hζ.pow_eq_one_iff_dvd l).1 h1
  have hP : ∀ x : Fin τ.rank → ℤ, ∃ c : ℤ, ∀ i, (p : ℤ) ∣ (w • x - x) i - c * γ i := by
    intro x
    have hsep : ∀ z : Fin τ.rank → ZMod p, CFSG.RankThree.E6.charVal z γ = 0 →
        CFSG.RankThree.E6.charVal z (w • x - x) = 0 := by
      intro z hz
      let b : Fin τ.rank → kˣ := fun j => ζ' ^ (z j).val
      have hbp : ∀ j, b j ^ p = 1 := by
        intro j
        show (ζ' ^ (z j).val) ^ p = 1
        rw [← pow_mul, mul_comm, pow_mul, hζ'.pow_eq_one, one_pow]
      have hbγ : rootChar b γ = 1 := by
        rw [ggKGEc_rootChar_zetaPow_eq_one_iff_charVal hζ' z γ]
        exact hz
      obtain ⟨i, hi⟩ := hall b hbp hbγ
      have hwi := hw i x
      rw [hi] at hwi
      have h1 : rootChar b (w • x - x) = 1 := by
        rw [rootChar_sub, hwi, mul_inv_cancel]
      rwa [ggKGEc_rootChar_zetaPow_eq_one_iff_charVal hζ' z (w • x - x)] at h1
    obtain ⟨c, hc⟩ := ggKGEc_redMod_mem_span (τ := τ) (p := p) hsep
    refine ⟨c.val, ?_⟩
    intro i
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hci := congrFun hc i
    simp only [TableBExc.redMod, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sub,
      Int.cast_mul] at hci
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val,
      Pi.sub_apply]
    rw [hci]
    ring
  let T : (Fin τ.rank → ZMod p) →+ (Fin τ.rank → ZMod p) :=
    { toFun := fun x => TableBExc.torusAct τ p w x
      map_zero' := by
        have h0 : TableBExc.liftMod τ p (0 : Fin τ.rank → ZMod p) = 0 := by
          funext i; simp [TableBExc.liftMod]
        show TableBExc.redMod τ p (w • TableBExc.liftMod τ p 0) = 0
        rw [h0, smul_zero]; funext i; simp [TableBExc.redMod]
      map_add' := fun x y => ggKGEc_torusAct_add w x y }
  let f : (Fin τ.rank → ZMod p) →+ (Fin τ.rank → ZMod p) :=
    { toFun := fun x => T x - x
      map_zero' := by simp
      map_add' := fun x y => by rw [map_add]; abel }
  have hT : ∀ x, T x = x + f x := fun x => by show T x = x + (T x - x); abel
  have hfg : f (TableBExc.redMod τ p γ) = 0 := by
    have h1 : TableBExc.torusAct τ p w (TableBExc.redMod τ p γ) = TableBExc.redMod τ p γ := by
      rw [TableBExc.torusAct]
      rw [TableBExc.redMod_smul_eq w (TableBExc.redMod_liftMod _), hwγ]
    show TableBExc.torusAct τ p w (TableBExc.redMod τ p γ) - TableBExc.redMod τ p γ = 0
    rw [h1, sub_self]
  have hfx : ∀ x, f x ∈ AddSubgroup.zmultiples (TableBExc.redMod τ p γ) := by
    intro x
    obtain ⟨c, hc⟩ := hP (TableBExc.liftMod τ p x)
    have hred : TableBExc.redMod τ p
        (w • TableBExc.liftMod τ p x - TableBExc.liftMod τ p x) = c • TableBExc.redMod τ p γ := by
      funext i
      have hci := hc i
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hci
      simp only [TableBExc.redMod, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sub,
        Int.cast_mul] at hci ⊢
      linear_combination hci
    have hsub : TableBExc.redMod τ p (w • TableBExc.liftMod τ p x - TableBExc.liftMod τ p x)
        = TableBExc.redMod τ p (w • TableBExc.liftMod τ p x) - x := by
      rw [TableBExc.redMod_sub, TableBExc.redMod_liftMod]
    have hthis : f x = (c : ZMod p) • TableBExc.redMod τ p γ := by
      change TableBExc.redMod τ p (w • TableBExc.liftMod τ p x) - x = _
      rw [← hsub, hred]
      funext i
      simp [zsmul_eq_mul, smul_eq_mul]
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨c, ?_⟩
    rw [hthis]
    funext i
    simp [zsmul_eq_mul, smul_eq_mul]
  have hf2 : ∀ x, f (f x) = 0 := by
    intro x
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp (hfx x)
    rw [← hn, map_zsmul, hfg]
    exact zsmul_zero n
  have hTk : ∀ k : ℕ, ∀ x, (T^[k]) x = x + k • f x := by
    intro k
    induction k with
    | zero => intro x; rw [Function.iterate_zero_apply, zero_nsmul, add_zero]
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply', ih x, map_add, map_nsmul, hT x,
        show T (f x) = f x from by rw [hT (f x), hf2 x, add_zero]]
      rw [succ_nsmul]; abel
  have hpf : ∀ x, p • f x = 0 := by
    intro x
    rw [← Nat.cast_smul_eq_nsmul (ZMod p) p (f x), ZMod.natCast_self]
    exact zero_smul (ZMod p) (f x)
  have hTtorus : ∀ k : ℕ, ∀ x, (T^[k]) x = TableBExc.torusAct τ p (w ^ k) x := by
    intro k
    induction k with
    | zero => intro x; rw [Function.iterate_zero_apply, pow_zero, TableBExc.torusAct_one]
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply', ih x, pow_succ', TableBExc.torusAct_mul]
      rfl
  have hwp : w ^ p = 1 := by
    apply NoOffExc.eq_one_of_torusAct (τ := τ) (p := p) (by omega)
    intro x
    rw [← hTtorus p x, hTk p x, hpf x, add_zero]
  by_contra hw1
  have hord : orderOf w = p := orderOf_eq_prime hwp hw1
  exact (ggKGExc_no_transvection hτ hp hp3 hτ6 hγ hord) hP

theorem ggKGExc_familyStabilizer_killRoot
    {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {k : Type} [Field k] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 ≤ p) (hτ6 : τ = .E6 → 5 ≤ p) {ζ : k} (hζ : IsPrimitiveRoot ζ p) {ι : Type}
    (a : ι → Fin τ.rank → kˣ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hker : ∀ i, rootChar (a i) γ = 1)
    (hall : ∀ b : Fin τ.rank → kˣ, (∀ j, b j ^ p = 1) → rootChar b γ = 1 → ∃ i, a i = b) :
    familyStabilizer a = {1, rootReflection γ} := by
  apply Set.Subset.antisymm
  · intro w hw
    have hker_eq : familyKernel a = {γ, -γ} :=
      ggKGExc_familyKernel_killRoot hτ hp hp3 hζ a hγ hker hall
    have himg := image_familyKernel (a := a) hw
    have hwγ : w • γ = γ ∨ w • γ = -γ := by
      have hmem : w • γ ∈ familyKernel a := by
        rw [← himg]
        exact ⟨γ, by rw [hker_eq]; exact Or.inl rfl, rfl⟩
      rw [hker_eq] at hmem
      simpa using hmem
    rcases hwγ with h | h
    · left
      exact ggKGEc_eq_one_of_fixRoot hτ hp hp3 hτ6 hζ a hγ hall hw h
    · right
      have hw' : w * rootReflection γ ∈ familyStabilizer a := fun i =>
        (rootCharStabilizerSubgroup (a i)).mul_mem (hw i)
          (ggKGEc_rootReflection_mem_familyStabilizer a hγ hker i)
      have hfix : (w * rootReflection γ) • γ = γ := by
        rw [mul_smul, rootReflection_smul_self hγ, smul_neg, h, neg_neg]
      have h1 := ggKGEc_eq_one_of_fixRoot hτ hp hp3 hτ6 hζ a hγ hall hw' hfix
      have hrr := rootReflection_mul_self hγ
      calc w = w * 1 := (mul_one w).symm
        _ = w * (rootReflection γ * rootReflection γ) := by rw [hrr, mul_one]
        _ = (w * rootReflection γ) * rootReflection γ := by rw [mul_assoc]
        _ = 1 * rootReflection γ := by rw [h1]
        _ = rootReflection γ := one_mul _
  · intro w hw
    rcases hw with rfl | rfl
    · intro i v; simp
    · exact ggKGEc_rootReflection_mem_familyStabilizer a hγ hker

end CFSG.StandardType
