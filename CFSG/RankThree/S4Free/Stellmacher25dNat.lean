module

public import CFSG.RankThree.S4Free.Stellmacher25d
public import CFSG.RankThree.S4Free.Stellmacher24Diag
public import CFSG.RankThree.S4Free.Stellmacher34Defs
import CFSG.RepresentationTheory.SzMartineau.MartineauInput

public section

namespace CFSG.RankThree.S4Free.Stell

open Subgroup CFSG.Quasithin CFSG.Blueprint Suzuki

variable {V : Type*} [CommGroup V] [Finite V]

theorem forall_mem_of_odd (hV : ∀ v : V, v ^ 2 = 1) {y : MulAut V} {m : ℕ} (hm : Odd m)
    (hy : y ^ m = 1) {C U₁ U₂ W : Subgroup V} (hCU : C ≤ U₂) (h1W : U₁ ≤ W)
    (hyU₁ : y ∈ stabSub U₁) (hyU₂ : y ∈ stabSub U₂)
    (hfpf : ∀ w ∈ W, y w * w⁻¹ ∈ C → w ∈ C) : ∀ w ∈ U₁, y w * w⁻¹ ∈ U₂ → w ∈ U₂ := by
  intro w hw hyw
  set N : V := ∏ i ∈ Finset.range m, (y ^ i) w with hN
  have hNy : y N = N := by
    have e1 : y N = ∏ i ∈ Finset.range m, (y ^ (i + 1)) w := by
      rw [hN, map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [pow_succ', MulAut.mul_apply]
    have e2 := Finset.prod_range_succ' (fun i => (y ^ i) w) m
    have e3 := Finset.prod_range_succ (fun i => (y ^ i) w) m
    simp only [pow_zero, MulAut.one_apply, hy] at e2 e3
    rw [e1, hN]
    exact mul_right_cancel (e2.symm.trans e3)
  have hyiU₁ : ∀ i : ℕ, (y ^ i) w ∈ U₁ := fun i => by
    induction i with
    | zero => simpa using hw
    | succ i ih =>
      rw [pow_succ', MulAut.mul_apply]
      exact (hyU₁ _).mpr ih
  have hNC : N ∈ C := hfpf N (h1W (U₁.prod_mem fun i _ => hyiU₁ i))
    (by rw [hNy, mul_inv_cancel]; exact C.one_mem)
  have hyi : ∀ i : ℕ, (y ^ i) w * w⁻¹ ∈ U₂ := fun i => by
    induction i with
    | zero => simp [U₂.one_mem]
    | succ i ih =>
      have e : (y ^ (i + 1)) w * w⁻¹ = y ((y ^ i) w * w⁻¹) * (y w * w⁻¹) := by
        rw [pow_succ', MulAut.mul_apply, map_mul, map_inv]
        group
      rw [e]
      exact U₂.mul_mem ((hyU₂ _).mpr ih) hyw
  have hNw : N * (w ^ m)⁻¹ ∈ U₂ := by
    have e : N * (w ^ m)⁻¹ = ∏ i ∈ Finset.range m, ((y ^ i) w * w⁻¹) := by
      rw [hN, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, inv_pow]
    rw [e]
    exact U₂.prod_mem fun i _ => hyi i
  have hwm : w ^ m = w := by
    obtain ⟨k, rfl⟩ := hm
    rw [pow_succ, pow_mul, hV, one_pow, one_mul]
  have := U₂.mul_mem (U₂.inv_mem hNw) (hCU hNC)
  rwa [mul_inv_rev, inv_inv, hwm, mul_assoc, inv_mul_cancel, mul_one] at this

open Matrix in
theorem isNatSzProduct_of_fpf {G : Type*} [Group G]
    {Y : Type*} [CommGroup Y] [Finite Y] (hY : ∀ y : Y, y ^ 2 = 1) {a : ℕ} (ha : 1 ≤ a)
    (ψ : G →* CFSG.Open.Sz a) (hψ : Function.Surjective ψ) (ρ : G →* MulAut Y)
    (hker : ψ.ker ≤ ρ.ker) {g₀ : G} (hg₀ : orderOf (ψ g₀) = 5)
    (hfpf : ∀ y, ρ g₀ y = y → y = 1) : IsNatSzProduct a ψ ρ := by
  classical
  set ρ₀ : ↥(CFSG.Open.Sz a) →* MulAut Y := (QuotientGroup.lift ψ.ker ρ hker).comp
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.toMonoidHom with hρ₀def
  have hρ₀ : ∀ g, ρ₀ (ψ g) = ρ g := by
    intro g
    rw [hρ₀def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      show (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm (ψ g) = (g : G ⧸ ψ.ker) from
        (MulEquiv.symm_apply_eq _).mpr rfl, QuotientGroup.lift_mk]
  set N := Nat.card Y with hN
  let ε : {i : ℕ // i < N} ≃ Y := Fin.equivSubtype.symm.trans (Finite.equivFin Y).symm
  letI : CommGroup {i : ℕ // i < N} := ε.commGroup
  let eY : {i : ℕ // i < N} ≃* Y := ε.mulEquiv
  have hT2 : ∀ t : Additive {i : ℕ // i < N}, (2 : ℕ) • t = 0 := by
    intro t
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    apply eY.injective
    rw [map_pow, hY, map_one]
  letI : Module (ZMod 2) (Additive {i : ℕ // i < N}) := AddCommGroup.zmodModule hT2
  let ρT : Representation (ZMod 2) ↥(CFSG.Open.Sz a) (Additive {i : ℕ // i < N}) :=
    { toFun := fun g => AddMonoidHom.toZModLinearMap 2
        { toFun := fun t => Additive.ofMul (eY.symm (ρ₀ g (eY (Additive.toMul t))))
          map_zero' := by simp
          map_add' := fun s t => by simp }
      map_one' := by
        ext t
        simp
      map_mul' := fun g h => by
        ext t
        simp }
  have hρT : ∀ g t, ρT g t = Additive.ofMul (eY.symm (ρ₀ g (eY (Additive.toMul t)))) :=
    fun _ _ => rfl
  obtain ⟨s, hsI, hstop, hsnat⟩ := CFSG.RepresentationTheory.SzMartineau.martineauSzInput_holds a ha
    (Additive {i : ℕ // i < N}) ρT ⟨ψ g₀, hg₀, fun t ht => by
      rw [hρT, hρ₀] at ht
      have h1 : ρ g₀ (eY (Additive.toMul t)) = eY (Additive.toMul t) := by
        have := congrArg (fun u => eY (Additive.toMul u)) ht
        simpa using this
      apply Additive.toMul.injective
      rw [toMul_zero]
      exact eY.injective ((hfpf _ h1).trans (map_one eY).symm)⟩
  choose θ hθinj hθrange hθeq using hsnat
  set k := s.card with hk
  let idx : Fin k ≃ ↥s := s.equivFin.symm
  let θi : Fin k → ((Fin 4 → GaloisField 2 (2 * a + 1)) →+ Additive {i : ℕ // i < N}) :=
    fun j => θ (idx j) (idx j).2
  have hθmem : ∀ j v, θi j v ∈ ((idx j : ↥s) : Submodule (ZMod 2) (Additive {i : ℕ // i < N})) := by
    intro j v
    rw [← Submodule.mem_toAddSubgroup, ← hθrange (idx j) (idx j).2]
    exact ⟨v, rfl⟩
  let Φ : (Fin k → Fin 4 → GaloisField 2 (2 * a + 1)) →+ Additive {i : ℕ // i < N} :=
    ∑ j, (θi j).comp (Pi.evalAddMonoidHom _ j)
  have hΦ : ∀ f, Φ f = ∑ j, θi j (f j) := fun f => by
    simp only [Φ, AddMonoidHom.finset_sum_apply, AddMonoidHom.comp_apply,
      Pi.evalAddMonoidHom_apply]
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    funext j
    have hW := (Finset.supIndep_iff_disjoint_erase.mp hsI) (idx j) (idx j).2
    have hrest : ∑ i ∈ Finset.univ.erase j, θi i (f i) ∈
        (s.erase (idx j : Submodule (ZMod 2) (Additive {i : ℕ // i < N}))).sup id := by
      refine Submodule.sum_mem _ fun i hi => ?_
      have hij : (idx i : Submodule (ZMod 2) (Additive {i : ℕ // i < N})) ≠ idx j := fun h' =>
        (Finset.mem_erase.mp hi).1 (idx.injective (Subtype.ext h'))
      exact Finset.le_sup (f := id) (Finset.mem_erase.mpr ⟨hij, (idx i).2⟩) (hθmem i (f i))
    have hsplit : θi j (f j) + ∑ i ∈ Finset.univ.erase j, θi i (f i) = 0 := by
      rw [Finset.add_sum_erase _ (fun i => θi i (f i)) (Finset.mem_univ j), ← hΦ, hf]
    have hj' : θi j (f j) ∈
        (s.erase (idx j : Submodule (ZMod 2) (Additive {i : ℕ // i < N}))).sup id := by
      rw [eq_neg_of_add_eq_zero_left hsplit]
      exact Submodule.neg_mem _ hrest
    have h0 : θi j (f j) = 0 := (Submodule.disjoint_def.mp hW) _ (hθmem j (f j)) hj'
    exact hθinj (idx j) (idx j).2 (h0.trans (map_zero _).symm)
  have hΦsurj : Function.Surjective Φ := by
    intro t
    have hle : s.sup id ≤ (AddMonoidHom.toZModLinearMap 2 Φ).range := by
      refine Finset.sup_le fun W hW => ?_
      intro w hw
      have hw' : w ∈ (θ W hW).range := by
        rw [hθrange]
        exact hw
      obtain ⟨v, rfl⟩ := hw'
      have hij : idx (idx.symm ⟨W, hW⟩) = ⟨W, hW⟩ := idx.apply_symm_apply _
      refine ⟨Pi.single (idx.symm ⟨W, hW⟩) v, ?_⟩
      show Φ (Pi.single (idx.symm ⟨W, hW⟩) v) = θ W hW v
      rw [hΦ, Finset.sum_eq_single (idx.symm ⟨W, hW⟩)
        (fun i _ hi => by rw [Pi.single_eq_of_ne hi, map_zero])
        (fun h' => absurd (Finset.mem_univ _) h'), Pi.single_eq_same]
      simp only [θi, hij]
    have ht : t ∈ s.sup id := by
      rw [hstop]
      exact Submodule.mem_top
    obtain ⟨f, hf⟩ := hle ht
    exact ⟨f, hf⟩
  set ΦE := AddEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩ with hΦE
  refine ⟨k, eY.symm.trans (AddEquiv.toMultiplicativeLeft ΦE).symm, fun g y => ?_⟩
  set f := ΦE.symm (Additive.ofMul (eY.symm y)) with hf
  have hΦf : Φ f = Additive.ofMul (eY.symm y) := ΦE.apply_symm_apply _
  have key : Φ (fun j => (((ψ g : CFSG.Open.Sz a) : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
      Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ f j) =
      Additive.ofMul (eY.symm (ρ g y)) := by
    rw [hΦ]
    calc ∑ j, θi j ((((ψ g : CFSG.Open.Sz a) : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ f j) =
        ∑ j, ρT (ψ g) (θi j (f j)) :=
          Finset.sum_congr rfl fun j _ => hθeq (idx j) (idx j).2 (ψ g) (f j)
      _ = ρT (ψ g) (∑ j, θi j (f j)) := (map_sum _ _ _).symm
      _ = Additive.ofMul (eY.symm (ρ g y)) := by
        rw [← hΦ, hΦf, hρT, toMul_ofMul, MulEquiv.apply_symm_apply, hρ₀]
  apply Multiplicative.toAdd.injective
  change ΦE.symm (Additive.ofMul (eY.symm (ρ g y))) =
    fun j => (((ψ g : CFSG.Open.Sz a) : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
      Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ f j
  rw [ΦE.symm_apply_eq]
  exact key.symm

open Matrix in
theorem card_eq_of_isNatSzProduct {G Y : Type*} [Group G] [CommGroup Y] [Nontrivial Y] {n : ℕ}
    {ψ : G →* CFSG.Open.Sz n} {ρ : G →* MulAut Y} (h : IsNatSzProduct n ψ ρ)
    (hirr : ∀ X : Subgroup Y, (∀ g, ∀ y ∈ X, ρ g y ∈ X) → X = ⊥ ∨ X = ⊤) :
    Nat.card Y = 2 ^ (4 * (2 * n + 1)) := by
  classical
  obtain ⟨k, θ, hθ⟩ := h
  have hk : k ≠ 0 := by
    rintro rfl
    obtain ⟨y, hy⟩ := exists_ne (1 : Y)
    apply hy
    apply θ.injective
    rw [map_one]
    apply Multiplicative.toAdd.injective
    funext j
    exact j.elim0
  set j₀ : Fin k := ⟨0, Nat.pos_of_ne_zero hk⟩ with hj₀
  set X : Subgroup Y := Subgroup.comap θ.toMonoidHom
    { carrier := {f | ∀ j ≠ j₀, Multiplicative.toAdd f j = 0}
      mul_mem' := fun {f g} hf hg j hj => by
        simp only [Set.mem_setOf_eq, toAdd_mul, Pi.add_apply] at hf hg ⊢
        rw [hf j hj, hg j hj, add_zero]
      one_mem' := fun j _ => by simp
      inv_mem' := fun {f} hf j hj => by
        simp only [Set.mem_setOf_eq, toAdd_inv, Pi.neg_apply] at hf ⊢
        rw [hf j hj, neg_zero] } with hX
  have hmemX : ∀ y, y ∈ X ↔ ∀ j ≠ j₀, Multiplicative.toAdd (θ y) j = 0 := fun y => Iff.rfl
  have hXinv : ∀ g, ∀ y ∈ X, ρ g y ∈ X := by
    intro g y hy
    rw [hmemX] at hy ⊢
    intro j hj
    rw [hθ, toAdd_ofAdd, hy j hj, Matrix.mulVec_zero]
  set v : Fin 4 → GaloisField 2 (2 * n + 1) := Pi.single 0 1 with hv
  have hv0 : v ≠ 0 := fun h0 => by simpa [hv] using congrFun h0 0
  have hsingle : ∀ j, θ.symm (Multiplicative.ofAdd (Pi.single j v)) ∈ X ↔ j = j₀ := by
    intro j
    rw [hmemX, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    constructor
    · intro hj
      by_contra hne
      have := hj j hne
      rw [Pi.single_eq_same] at this
      exact hv0 this
    · rintro rfl i hi
      exact Pi.single_eq_of_ne hi _
  have hX1 : X ≠ ⊥ := by
    intro hX0
    have hmem := (hsingle j₀).mpr rfl
    rw [hX0, mem_bot, MulEquiv.symm_apply_eq, map_one] at hmem
    have := congrArg
      (fun f : Multiplicative (Fin k → Fin 4 → GaloisField 2 (2 * n + 1)) =>
        Multiplicative.toAdd f j₀) hmem
    simp only [toAdd_ofAdd, Pi.single_eq_same, toAdd_one, Pi.zero_apply] at this
    exact hv0 this
  have hXtop : X = ⊤ := (hirr X hXinv).resolve_left hX1
  have hk1 : k = 1 := by
    by_contra hk1
    have hne : (⟨1, by omega⟩ : Fin k) ≠ j₀ := by
      rw [hj₀]
      exact fun h' => absurd (congrArg Fin.val h') (by norm_num)
    exact hne ((hsingle _).mp (hXtop ▸ mem_top _))
  subst hk1
  have hF : Nat.card (GaloisField 2 (2 * n + 1)) = 2 ^ (2 * n + 1) :=
    GaloisField.card 2 (2 * n + 1) (by omega)
  rw [Nat.card_congr θ.toEquiv]
  change Nat.card (Fin 1 → Fin 4 → GaloisField 2 (2 * n + 1)) = _
  rw [Nat.card_fun, Nat.card_fun, hF, Nat.card_eq_fintype_card, Fintype.card_fin,
    Nat.card_eq_fintype_card, Fintype.card_fin, pow_one, ← pow_mul, mul_comm]

theorem sec_irred {L : Subgroup (MulAut V)} {U₁ U₂ : Subgroup V} (h21 : U₂ ≤ U₁)
    (hU₁ : L ≤ stabSub U₁) (hU₂ : L ≤ stabSub U₂)
    (hirr : ∀ X : Subgroup V, U₂ ≤ X → X ≤ U₁ → L ≤ stabSub X → X = U₂ ∨ X = U₁)
    (J : Subgroup (Sec U₁ U₂)) (hJ : ∀ l, ∀ z ∈ J, secAct hU₁ hU₂ l z ∈ J) : J = ⊥ ∨ J = ⊤ := by
  set X : Subgroup V := (J.comap (QuotientGroup.mk' (U₂.subgroupOf U₁))).map U₁.subtype with hX
  have hmemX : ∀ y : ↥U₁, (y : V) ∈ X ↔ (QuotientGroup.mk y : Sec U₁ U₂) ∈ J := by
    intro y
    constructor
    · rintro ⟨z, hz, hzy⟩
      rw [← Subtype.ext hzy]
      exact hz
    · intro h
      exact ⟨y, h, rfl⟩
  have hLX : L ≤ stabSub X := le_stabSub_of_forall_apply_mem fun l hl w hw => by
    obtain ⟨z, hz, rfl⟩ := hw
    have h1 := hJ ⟨l, hl⟩ _ (show (QuotientGroup.mk z : Sec U₁ U₂) ∈ J from hz)
    rw [secAct_mk] at h1
    exact (hmemX ⟨l z, (hU₁ hl z).2 z.2⟩).2 h1
  have h2X : U₂ ≤ X := fun y hy => (hmemX ⟨y, h21 hy⟩).2
    (by rw [(sec_mk_eq_one_iff _).2 hy]; exact J.one_mem)
  rcases hirr X h2X (map_subtype_le _) hLX with h | h
  · left
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    have h1 := (hmemX y).2 hz
    rw [h] at h1
    exact mem_bot.2 ((sec_mk_eq_one_iff _).2 h1)
  · right
    rw [eq_top_iff]
    intro z _
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    exact (hmemX y).1 (by rw [h]; exact y.2)

namespace Hyp25Sz

variable {S M A L : Subgroup (MulAut V)} {Z₀ W : Subgroup V}

theorem le_M_of_le (h : Hyp25Sz S M A L Z₀ W) : A ≤ M := fun b hb =>
  h.normalizer_le b (h.isL24Sz.le hb) (map_eq_self_of_le_fixV h.le_fixV hb)

theorem exists_fpf_five (hV : ∀ v : V, v ^ 2 = 1)
    (h : Hyp25Sz S M A L Z₀ W) (R : Subgroup ↥L) [R.Normal] (hodd : ¬ 2 ∣ (oTwo ↥L).relIndex R)
    {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : ↥L ⧸ R ≃* suzukiGroup a K) :
    ∃ y : ↥L, orderOf (QuotientGroup.mk y : ↥L ⧸ R) = 5 ∧ Odd (orderOf y) ∧
      ∀ w ∈ W, (y : MulAut V) w * w⁻¹ ∈ W ⊓ fixV L → w ∈ W ⊓ fixV L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hbA, hbO⟩ := h.isL24Sz.exists_mem_not_mem_oTwo h.elemAb
  have hbL : b ∈ L := h.isL24Sz.le hbA
  set b' : ↥L := ⟨b, hbL⟩ with hb'
  have hb'2 : b' ^ 2 = 1 := Subtype.ext (by simpa using h.elemAb.2 b hbA)
  have hb'R : b' ∉ R := fun hR => hbO ⟨b', inf_le_oTwo_of_odd h.elemAb hodd ⟨hR, hbA⟩, rfl⟩
  set π := QuotientGroup.mk' R with hπ
  set ab : ↥L ⧸ R := π b' with hab
  have hab2 : orderOf ab = 2 := by
    refine orderOf_eq_prime (by rw [hab, ← map_pow, hb'2, map_one]) fun h1 => hb'R ?_
    rwa [hab, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have habi : ab⁻¹ = ab :=
    inv_eq_of_mul_eq_one_right (by rw [← sq, ← hab2, pow_orderOf_eq_one])
  obtain ⟨f, hf5, hfi⟩ := Suzuki.exists_orderOf_eq_five_inv hK e hab2
  set t := ab * f with ht
  have ht2 : orderOf t = 2 := by
    refine orderOf_eq_prime ?_ fun h1 => ?_
    · rw [sq, ht]
      calc ab * f * (ab * f) = (ab * f * ab⁻¹) * f := by rw [habi]; group
        _ = 1 := by rw [hfi, inv_mul_cancel]
    · have hf : f = ab⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [hf, orderOf_inv, hab2] at hf5
      norm_num at hf5
  obtain ⟨c₀, hc₀⟩ := isConj_iff.mp
    (CFSG.QuasithinUnique.Setup.Family.suzuki_involutions_conjugate hK (e ab) (e t)
      (by rw [MulEquiv.orderOf_eq]; exact hab2) (by rw [MulEquiv.orderOf_eq]; exact ht2))
  obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective R (e.symm c₀)
  have hct : π c * ab * (π c)⁻¹ = t := by
    apply e.injective
    rw [hπ, hc, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hc₀]
  have hcM : (c : MulAut V) ∉ M := by
    intro hcM
    set Mb := (M.subgroupOf L).map π with hMb
    have hRM : R ≤ M.subgroupOf L := fun r hr =>
      mem_subgroupOf.mpr (h.isL24Sz.le_of_suzuki ha hK e h.elemAb ⟨r, hr, rfl⟩)
    have hMbtop : Mb ≠ ⊤ := by
      intro htop
      apply h.isL24Sz.not_le
      intro l hl
      have h1 : (⟨l, hl⟩ : ↥L) ∈ Mb.comap π := by
        rw [htop, comap_top]
        exact mem_top _
      rw [hMb, comap_map_eq, hπ, QuotientGroup.ker_mk', sup_eq_left.mpr hRM] at h1
      exact mem_subgroupOf.mp h1
    have hP : IsPGroup 2 ((S.subgroupOf L).map π) :=
      (h.isPGroup.comap_subtype (K := L)).map π
    have hPi : ¬ 2 ∣ ((S.subgroupOf L).map π).index := fun h2 =>
      h.isL24Sz.not_dvd_relIndex (h2.trans (index_map_dvd _ (QuotientGroup.mk'_surjective R)))
    have hTM : ((hP.toSylow hPi : Sylow 2 (↥L ⧸ R)) : Subgroup (↥L ⧸ R)) ≤ Mb :=
      map_mono fun s hs => mem_subgroupOf.mpr (h.le_M (mem_subgroupOf.mp hs))
    have hMN := le_normalizer_of_sylow_le ha hK e (hP.toSylow hPi) hTM hMbtop
    have habM : ab ∈ Mb := ⟨b', mem_subgroupOf.mpr (h.le_M_of_le hbA), rfl⟩
    have hcMb : π c ∈ Mb := ⟨c, mem_subgroupOf.mpr hcM, rfl⟩
    have hfM : f ∈ Mb := by
      have hf : f = ab⁻¹ * (π c * ab * (π c)⁻¹) := by rw [hct, ht, inv_mul_cancel_left]
      rw [hf]
      exact Mb.mul_mem (Mb.inv_mem habM) (Mb.mul_mem (Mb.mul_mem hcMb habM) (Mb.inv_mem hcMb))
    have h5 := (normalizer (((hP.toSylow hPi : Sylow 2 (↥L ⧸ R)) : Subgroup (↥L ⧸ R)) :
      Set (↥L ⧸ R))).orderOf_dvd_natCard (hMN hfM)
    rw [hf5] at h5
    exact Suzuki.not_five_dvd_card_normalizer hK e _ h5
  set y₀ : ↥L := b' * (c * b' * c⁻¹) with hy₀
  have hy₀f : π y₀ = f := by
    rw [hy₀, map_mul, map_mul, map_mul, map_inv, ← hab, hct, ht, ← mul_assoc, ← sq, ← hab2,
      pow_orderOf_eq_one, one_mul]
  have hy₀fpf : ∀ w ∈ W, (y₀ : MulAut V) w * w⁻¹ ∈ W ⊓ fixV L → w ∈ W ⊓ fixV L :=
    fun w hw hc' => h.mem_of_comm_mem hV hbA hbO c.2 hcM hw hc'
  obtain ⟨k, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y₀).ne'
  refine ⟨y₀ ^ 2 ^ k, ?_, ?_, ?_⟩
  · show orderOf (π (y₀ ^ 2 ^ k)) = 5
    have hcop : (orderOf f).Coprime (2 ^ k) := by
      rw [hf5]
      exact Nat.Coprime.pow_right _ (by norm_num)
    rw [map_pow, hy₀f, hcop.orderOf_pow, hf5]
  · rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (hord ▸ dvd_mul_right _ _), hord,
      Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
    exact hm
  · have hstab : (y₀ : MulAut V) ∈ stabSub W := h.le_stabSub y₀.2
    have hCfix : ∀ c' ∈ W ⊓ fixV L, (y₀ : MulAut V) c' = c' := fun c' hc' =>
      (mem_inf.mp hc').2 _ y₀.2
    have := forall_mem_of_pow_two_pow hV hstab inf_le_left hCfix hy₀fpf hm
      (by rw [Subgroup.orderOf_coe, hord])
    simpa using this

end Hyp25Sz

theorem exists_hom_open_sz {L : Subgroup (MulAut V)} (R : Subgroup ↥L) [R.Normal] {a : ℕ}
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : ↥L ⧸ R ≃* suzukiGroup a K) :
    ∃ ψ : ↥L →* CFSG.Open.Sz a, Function.Surjective ψ ∧ ψ.ker = R ∧
      ∀ l, orderOf (ψ l) = orderOf (QuotientGroup.mk l : ↥L ⧸ R) := by
  obtain ⟨σ⟩ := nonempty_mulEquiv_open_sz hK
  refine ⟨(σ.toMonoidHom.comp e.toMonoidHom).comp (QuotientGroup.mk' R),
    (σ.surjective.comp e.surjective).comp (QuotientGroup.mk'_surjective R), ?_, fun l => ?_⟩
  · ext g
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq,
      QuotientGroup.mk'_apply]

namespace Hyp25Sz

variable {S M A L : Subgroup (MulAut V)} {Z₀ W : Subgroup V}

theorem isNatSzProduct_chief
    (hV : ∀ v : V, v ^ 2 = 1) (h : Hyp25Sz S M A L Z₀ W) (R : Subgroup ↥L) [R.Normal]
    (hOR : oTwo ↥L ≤ R) (hodd : ¬ 2 ∣ (oTwo ↥L).relIndex R) {a : ℕ} (ha : 1 ≤ a) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (e : ↥L ⧸ R ≃* suzukiGroup a K)
    {U₁ U₂ : Subgroup V} (hCU : W ⊓ fixV L ≤ U₂) (h21 : U₂ < U₁) (h1W : U₁ ≤ W)
    (hU₁ : L ≤ stabSub U₁) (hU₂ : L ≤ stabSub U₂)
    (hirr : ∀ X : Subgroup V, U₂ ≤ X → X ≤ U₁ → L ≤ stabSub X → X = U₂ ∨ X = U₁) :
    ∃ ψ : ↥L →* CFSG.Open.Sz a, Function.Surjective ψ ∧ ψ.ker = R ∧
      IsNatSzProduct a ψ (secAct hU₁ hU₂) := by
  have hker := h.ker_secAct_eq hV R hOR hodd ha hK e hCU h21 h1W hU₁ hU₂ hirr
  obtain ⟨ψ, hψs, hψk, hψo⟩ := exists_hom_open_sz R hK e
  obtain ⟨y, hy5, hyodd, hyfpf⟩ := h.exists_fpf_five hV R hodd ha hK e
  have hym : (y : MulAut V) ^ orderOf y = 1 := by
    rw [← Subgroup.coe_pow, pow_orderOf_eq_one, Subgroup.coe_one]
  refine ⟨ψ, hψs, hψk, isNatSzProduct_of_fpf (sec_sq_eq_one hV) ha ψ hψs (secAct hU₁ hU₂)
    (by rw [hψk, hker]) (g₀ := y) (by rw [hψo, hy5]) fun z hz => ?_⟩
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective z
  rw [secAct_mk] at hz
  exact (sec_mk_eq_one_iff w).mpr (forall_mem_of_odd hV hyodd hym hCU h1W (hU₁ y.2)
    (hU₂ y.2) hyfpf w w.2 ((sec_mk_eq_mk_iff _ _).mp hz))

theorem chief
    (hV : ∀ v : V, v ^ 2 = 1) (h : Hyp25Sz S M A L Z₀ W) (R : Subgroup ↥L) [R.Normal]
    (hOR : oTwo ↥L ≤ R) (hodd : ¬ 2 ∣ (oTwo ↥L).relIndex R) {a : ℕ} (ha : 1 ≤ a) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (e : ↥L ⧸ R ≃* suzukiGroup a K) :
    ∀ U₁ U₂ : Subgroup V, W ⊓ fixV L ≤ U₂ → U₂ ≤ U₁ → U₁ ≤ W → L ≤ stabSub U₁ →
      L ≤ stabSub U₂ → U₂ < U₁ →
      (∀ X : Subgroup V, U₂ ≤ X → X ≤ U₁ → L ≤ stabSub X → X = U₂ ∨ X = U₁) →
      U₂.relIndex U₁ = 2 ^ (4 * (2 * a + 1)) ∧
        ∀ l ∈ L, (∀ w ∈ U₁, l w * w⁻¹ ∈ U₂) → l ∈ R.map L.subtype := by
  intro U₁ U₂ hCU h21 h1W hU₁ hU₂ hlt hirr
  have hker := h.ker_secAct_eq hV R hOR hodd ha hK e hCU hlt h1W hU₁ hU₂ hirr
  refine ⟨?_, fun l hl hlw => ⟨⟨l, hl⟩, ?_, rfl⟩⟩
  swap
  · show (⟨l, hl⟩ : ↥L) ∈ R
    rw [← hker, MonoidHom.mem_ker, secAct_eq_one_iff]
    exact hlw
  obtain ⟨ψ, -, -, hnat⟩ := h.isNatSzProduct_chief hV R hOR hodd ha hK e hCU hlt h1W hU₁ hU₂ hirr
  obtain ⟨y₁, hy₁, hy₀⟩ := Set.not_subset.mp (not_le_of_gt hlt)
  have : Nontrivial (Sec U₁ U₂) :=
    ⟨⟨QuotientGroup.mk ⟨y₁, hy₁⟩, 1, fun h0 => hy₀ ((sec_mk_eq_one_iff ⟨y₁, hy₁⟩).mp h0)⟩⟩
  exact card_eq_of_isNatSzProduct hnat (sec_irred h21 hU₁ hU₂ hirr)

end Hyp25Sz

end CFSG.RankThree.S4Free.Stell

namespace CFSG.RankThree.S4Free.Stell34

open Subgroup CFSG.Quasithin

universe u

theorem hyp24Sz_holds
    (hSub : CFSG.LocalAnalysis.WeakClosure81.SuzukiSubgroupInput) : Hyp24Sz.{u} :=
  fun _ _ _ hH _ _ _ h => Stell.exists_isL24_or_isL24Sz_of_szSections hSub hH h

theorem hyp25dSz_holds :
    Hyp25dSz.{u} := by
  intro V _ _ hV S M A L Z₀ hL hS hSM hA hq hZA hLM hgen hC hO
  have h : Stell.Hyp25Sz S M A L Z₀ ⊤ :=
    { isL24Sz := hL
      isPGroup := hS
      le_M := hSM
      elemAb := hA
      quadratic := hq
      le_fixV := hZA
      le_W := le_top
      le_stabSub := fun _ _ => mem_stabSub.mpr fun _ => by simp
      gen := fun U hU => by rw [hgen U hU]
      normalizer_le := fun l hl hZ => hLM (mem_inf.mpr ⟨hl, mem_stabSub.mpr fun u =>
        ⟨fun hu => by
          have hu' : l u ∈ Z₀.map l.toMonoidHom := hZ.symm ▸ hu
          obtain ⟨z, hz, hzu⟩ := hu'
          rwa [l.injective hzu] at hz,
        fun hu => hZ ▸ ⟨u, hu, rfl⟩⟩⟩) }
  obtain ⟨R, hRn, hOR, hodd, a, ha, K, _, _, hK, ⟨e⟩⟩ := hL.suzuki
  have hR := h.eq_bot_of_oTwo_eq_bot hV hO R hodd ha hK e
  obtain ⟨ψ, hψs, hψk, hψo⟩ := Stell.exists_hom_open_sz R hK e
  obtain ⟨y, hy5, -, hyfpf⟩ := h.exists_fpf_five hV R hodd ha hK e
  refine ⟨a, ha, ψ, hψs, Stell.isNatSzProduct_of_fpf hV ha ψ hψs L.subtype
    (by rw [hψk, hR]; exact bot_le) (g₀ := y) (by rw [hψo, hy5]) fun v hv => ?_⟩
  have h1 := hyfpf v (mem_top v) (by
    rw [show (y : MulAut V) v = v from hv, mul_inv_cancel]
    exact one_mem _)
  rwa [hC, inf_bot_eq, mem_bot] at h1

end CFSG.RankThree.S4Free.Stell34
