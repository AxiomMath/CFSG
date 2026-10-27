module

public import CFSG.Quasithin.Background.G64SymCase
public import CFSG.Quasithin.Background.G64ExtSq

public section

namespace CFSG.Quasithin.G64

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank Equiv Equiv.Perm

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [CommGroup V]

@[expose] def RedPiece (Gi : Subgroup (MulAut V)) (Wi C : Subgroup V) : Prop :=
  (∃ π : ↥(StatedSL 2 (ZMod 2)) →* ↥Gi,
      (FFModel.nat (StatedSL 2 (ZMod 2))).RealizesVia Gi Wi C π) ∨
    (∃ π : ↥(StatedSL 3 (ZMod 2)) →* ↥Gi,
      (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia Gi Wi C π) ∨
    SymmetricNatural Gi Wi C 5

theorem modComm_le_of_inv {Gi : Subgroup (MulAut V)} {Wi : Subgroup V}
    (hinv : ∀ g ∈ Gi, ∀ w ∈ Wi, g w ∈ Wi) : modComm Gi Wi ≤ Wi :=
  XMod.commOf_le_of_isInv (A := ↥Gi) fun g w hw => hinv g g.2 w hw

theorem B56Piece.commV_le {Gi : Subgroup (MulAut V)} {Wi C : Subgroup V}
    (hp : B56Piece Gi Wi C) : commV Gi ≤ Wi := by
  rcases hp with ⟨hW, -⟩ | ⟨hW, -⟩ | ⟨-, hle, -⟩
  · rw [hW]; exact le_sup_left
  · rw [hW]; exact le_sup_left
  · exact hle

theorem B56Piece.faithful {Gi : Subgroup (MulAut V)} {Wi C : Subgroup V} (hp : B56Piece Gi Wi C)
    (hinv : ∀ g ∈ Gi, ∀ w ∈ Wi, g w ∈ Wi) (hCW : C ≤ Wi) {g : MulAut V} (hg : g ∈ Gi)
    (htriv : ∀ w ∈ Wi, g w * w⁻¹ ∈ C) : g = 1 := by
  rcases hp with ⟨-, ⟨n, F, _, _, -, π, hπ⟩ | ⟨π, hπ⟩ | ⟨m, F, _, _, -, π, hπ⟩⟩ |
    ⟨-, m, F, _, _, -, I, π, -, -, hsup, hreal⟩ | ⟨-, -, -, -, F, _, _, -, π, hπ⟩
  · exact RealizesVia.eq_one_of_trivial (FFModel.nat_faithful _) hπ hg htriv
  · exact RealizesVia.eq_one_of_trivial (symDn_faithful le_rfl) hπ hg htriv
  · exact RealizesVia.eq_one_of_trivial (FFModel.nat_faithful _) hπ hg htriv
  · have hI : I 0 ≤ Wi := by
      rw [← hsup]
      exact le_sup_of_le_right (le_iSup I 0)
    exact RealizesVia.eq_one_of_trivial (FFModel.nat_faithful _) (hreal 0) hg
      fun w hw => htriv w (hI hw)
  · have hM : modComm Gi Wi ⊔ C ≤ Wi := sup_le (modComm_le_of_inv hinv) hCW
    exact RealizesVia.eq_one_of_trivial (FFModel.nat_faithful _) hπ hg
      fun w hw => htriv w (hM hw)

theorem two_le_card_field (F : Type) [Field F] [Finite F] : 2 ≤ Nat.card F := by
  have : Nontrivial F := inferInstance
  exact Finite.one_lt_card_iff_nontrivial.2 this

theorem exists_zmod_of_transvection (hV2 : ∀ v : V, v ^ 2 = 1) {H : Subgroup (MulAut V)}
    {U Z : Subgroup V} {d n : ℕ} (h : BinaryNaturalSL H U Z d n) {x : MulAut V} (hx : x ∈ H)
    (hx1 : x ≠ 1) (htr : Nat.card (commV (Subgroup.zpowers x)) = 2) :
    ∃ π : ↥(StatedSL d (ZMod 2)) →* ↥H,
      (FFModel.nat (StatedSL d (ZMod 2))).RealizesVia H U Z π := by
  obtain ⟨F, _, _, -, π, hπ⟩ := h
  obtain ⟨γ, hγ⟩ := exists_preimage hπ hx
  have hγ1 : γ ≠ 1 := by
    rintro rfl
    rw [map_one] at hγ
    exact hx1 (by rw [← hγ]; rfl)
  have hmove := RealizesVia.exists_moved (FFModel.nat_faithful _) hπ hγ1
  have ht := isTransvecSec_of_card_two (by rw [hγ]; exact htr) hmove
  have hF2 : Nat.card F ≤ 2 := card_le_two_of_rankOne hV2 hπ ht.1 ht.2
  have hF : Nat.card F = 2 := le_antisymm hF2 (two_le_card_field F)
  exact ⟨_, realizesVia_zmod hF hπ⟩

theorem B56Piece.not_c {Gi : Subgroup (MulAut V)} {Wi C : Subgroup V} [Finite V]
    (hle : Wi ≤ modComm Gi Wi ⊔ C) (hcard : Nat.card ↥Wi = 2 ^ 4 * Nat.card ↥C)
    (hπ : BinaryNaturalSL Gi (modComm Gi Wi ⊔ C) C 3 1) : False := by
  obtain ⟨π, hπ⟩ := BinaryNaturalSL.exists_zmod hπ
  have h1 := RealizesVia.card_eq hπ
  rw [card_natMod, Nat.card_zmod] at h1
  have h2 : Nat.card ↥Wi ≤ Nat.card ↥(modComm Gi Wi ⊔ C) := Subgroup.card_le_of_le hle
  rw [hcard, h1] at h2
  have hC : 0 < Nat.card ↥C := Nat.card_pos
  have : 2 ^ 4 * Nat.card ↥C ≤ 2 ^ 3 * Nat.card ↥C := h2
  nlinarith

theorem B56Piece.reduce [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) {Gi : Subgroup (MulAut V)}
    {Wi C : Subgroup V} (hp : B56Piece Gi Wi C) (hle : Wi ≤ modComm Gi Wi ⊔ C) {d : MulAut V}
    (hd : d ∈ Gi) (hd1 : d ≠ 1) (htr : Nat.card (commV (Subgroup.zpowers d)) = 2) :
    Wi = commV Gi ⊔ C ∧ RedPiece Gi Wi C := by
  rcases hp with ⟨hW, ⟨n, h2⟩ | h5 | ⟨m, h3⟩⟩ | ⟨-, m, F, _, _, -, I, π, hZI, hind, hsup, hreal⟩ |
    ⟨-, -, hcard, -, hπ⟩
  · obtain ⟨π, hπ⟩ := exists_zmod_of_transvection hV2 h2 hd hd1 htr
    exact ⟨hW, Or.inl ⟨π, hπ⟩⟩
  · exact ⟨hW, Or.inr (Or.inr h5)⟩
  · obtain ⟨π, hπ⟩ := exists_zmod_of_transvection hV2 h3 hd hd1 htr
    exact ⟨hW, Or.inr (Or.inl ⟨π, hπ⟩)⟩
  ·
    exfalso
    obtain ⟨γ, hγ⟩ := exists_preimage (hreal 0) hd
    have hγ1 : γ ≠ 1 := by
      rintro rfl
      rw [map_one] at hγ
      exact hd1 (by rw [← hγ]; rfl)
    obtain ⟨u₀, hu₀, hm₀⟩ := RealizesVia.exists_moved (FFModel.nat_faithful _) (hreal 0) hγ1
    obtain ⟨u₁, hu₁, hm₁⟩ := RealizesVia.exists_moved (FFModel.nat_faithful _) (hreal 1) hγ1
    rw [hγ] at hm₀ hm₁
    have h01 : I 0 ⊓ I 1 ≤ C := by
      rw [← hind 0]
      refine inf_le_inf_left _ (le_sup_of_le_right ?_)
      exact le_iSup₂_of_le (f := fun (j : Fin 2) (_ : j ≠ 0) => I j) 1 (by decide) le_rfl
    exact false_of_two_moved htr (fun u hu => (hreal 0).2.2.2.1 ⟨d, hd⟩ u hu)
      (fun u hu => (hreal 1).2.2.2.1 ⟨d, hd⟩ u hu) h01 hu₀ hu₁ hm₀ hm₁
  · exact absurd (B56Piece.not_c hle hcard hπ) not_false

theorem RedPiece.card_commV_mul_le [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1)
    {Gi : Subgroup (MulAut V)} {Wi C : Subgroup V} (hp : RedPiece Gi Wi C) {d : MulAut V}
    (hd : d ∈ Gi) (hd1 : d ≠ 1) (htr : Nat.card (commV (Subgroup.zpowers d)) = 2) :
    Nat.card (commV Gi) * Nat.card C ≤ Nat.card Wi := by
  rcases hp with ⟨π, hπ⟩ | ⟨π, hπ⟩ | ⟨π, hπ⟩
  · have h1 := card_commV_le_of_natSL le_rfl hπ hd hd1 htr
    rw [RealizesVia.card_eq hπ, card_natMod, Nat.card_zmod]
    exact Nat.mul_le_mul_right _ h1
  · have h1 := card_commV_le_of_natSL (by norm_num) hπ hd hd1 htr
    rw [RealizesVia.card_eq hπ, card_natMod, Nat.card_zmod]
    exact Nat.mul_le_mul_right _ h1
  · set π' : Perm (Fin 5) →* ↥Gi := π with hπ'def
    have hπ' : (FFModel.symDn 5).RealizesVia Gi Wi C π' := hπ
    have hinj : Function.Injective π' :=
      RealizesVia.injective_of_faithful' (symDn_faithful le_rfl) hπ'
    set θ : ↥Gi ≃* Perm (Fin (4 + 1)) := (MulEquiv.ofBijective π' ⟨hinj, hπ'.1⟩).symm with hθ
    have hπθ : π' (θ ⟨d, hd⟩) = ⟨d, hd⟩ :=
      (MulEquiv.ofBijective π' ⟨hinj, hπ'.1⟩).apply_symm_apply _
    have hsw : (θ ⟨d, hd⟩).IsSwap := by
      refine isSwap_of_symNat hV2 le_rfl hπ' ?_
      rw [hπθ]
      exact htr
    have h1 := card_commV_le_of_swap θ hd hsw htr
    rw [RealizesVia.card_eq hπ, card_symDn_mod (by norm_num), ite_eq_right (by decide)]
    exact Nat.mul_le_mul_right _ h1

theorem mem_closure_pairVec {n : ℕ} (i : Fin n) {x : G6.PermMod n} (hx : x ∈ G6.coreMod n) :
    x ∈ Subgroup.closure (Set.range (pairVec i)) := by
  classical
  have hx' : x = ∏ l, pairVec i l ^ (Multiplicative.toAdd x l).val := by
    apply Multiplicative.toAdd.injective
    funext m
    rw [toAdd_prod, Finset.sum_apply]
    simp only [toAdd_pow, pairVec, toAdd_ofAdd, Pi.smul_apply, Pi.add_apply, smul_add,
      Finset.sum_add_distrib]
    have h1 : ∑ l, (Multiplicative.toAdd x l).val • (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) m =
        (∑ l, Multiplicative.toAdd x l) * (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) m := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id', id]
    have h2 : ∑ l, (Multiplicative.toAdd x l).val • (Pi.single l (1 : ZMod 2) : Fin n → ZMod 2) m =
        Multiplicative.toAdd x m := by
      rw [Finset.sum_eq_single m]
      · rw [Pi.single_eq_same, nsmul_eq_mul, mul_one, ZMod.natCast_val, ZMod.cast_id', id]
      · intro l _ hl
        rw [Pi.single_eq_of_ne (Ne.symm hl), smul_zero]
      · simp
    rw [h1, h2, G6.mem_coreMod.1 hx, zero_mul, zero_add]
  rw [hx']
  exact Subgroup.prod_mem _ fun l _ =>
    Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self l)) _

@[expose] def invSub [Finite V] (Y : Subgroup V) : Subgroup (MulAut V) where
  carrier := {x | ∀ y ∈ Y, x y ∈ Y}
  one_mem' := fun y hy => hy
  mul_mem' := fun {x z} hx hz y hy => hx _ (hz y hy)
  inv_mem' := by
    intro x hx y hy
    let f : ↥Y → ↥Y := fun w => ⟨x w, hx w w.2⟩
    have hf : Function.Injective f := fun w w' h =>
      Subtype.ext (x.injective (congrArg Subtype.val h))
    obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.1 hf) ⟨y, hy⟩
    have : x⁻¹ y = w := by
      rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
      exact (congrArg Subtype.val hw).symm
    rw [this]
    exact w.2

theorem le_of_inv_natSL [Finite V] {n : ℕ} {Gi : Subgroup (MulAut V)} {Wi : Subgroup V}
    {π : ↥(StatedSL n (ZMod 2)) →* ↥Gi}
    (hπ : (FFModel.nat (StatedSL n (ZMod 2))).RealizesVia Gi Wi ⊥ π) {Y : Subgroup V}
    (hYW : Y ≤ Wi) (hYinv : ∀ g ∈ Gi, ∀ y ∈ Y, g y ∈ Y) {y₀ : V} (hy₀ : y₀ ∈ Y)
    (hy₀1 : y₀ ≠ 1) : Wi ≤ Y := by
  obtain ⟨f, hfs, hfk, hfe⟩ := exists_natMap hπ
  have hfi : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu'
    exact Subtype.ext (Subgroup.mem_bot.1 ((hfk u).1 hu'))
  intro w hw
  by_cases hw1 : w = 1
  · rw [hw1]; exact Y.one_mem
  have hv : Multiplicative.toAdd (f ⟨y₀, hYW hy₀⟩) ≠ 0 := by
    intro h0
    apply hy₀1
    have : f ⟨y₀, hYW hy₀⟩ = 1 := Multiplicative.toAdd.injective h0
    exact Subgroup.mem_bot.1 ((hfk _).1 this)
  have hv' : Multiplicative.toAdd (f ⟨w, hw⟩) ≠ 0 := by
    intro h0
    apply hw1
    have : f ⟨w, hw⟩ = 1 := Multiplicative.toAdd.injective h0
    exact Subgroup.mem_bot.1 ((hfk _).1 this)
  obtain ⟨φ, d, hφd, hg⟩ := CFSG.GroupTheory.GLnTwoSplitting.exists_transvection_apply_eq hv hv'
  set γ := (glLin n).symm (LinearEquiv.transvection hφd) with hγ
  have hγm := mem_statedSL_zmod γ
  have hu : ((π ⟨γ, hγm⟩ : ↥Gi) : MulAut V) y₀ ∈ Wi := hπ.2.2.2.1 _ y₀ (hYW hy₀)
  have h1 := hfe ⟨γ, hγm⟩ ⟨y₀, hYW hy₀⟩ hu
  have h2 : f ⟨_, hu⟩ = f ⟨w, hw⟩ := by
    rw [h1]
    apply Multiplicative.toAdd.injective
    show (γ : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (Multiplicative.toAdd (f ⟨y₀, hYW hy₀⟩)) = _
    rw [← glLin_apply, hγ, MulEquiv.apply_symm_apply, hg]
  have h3 : ((π ⟨γ, hγm⟩ : ↥Gi) : MulAut V) y₀ = w := congrArg Subtype.val (hfi h2)
  rw [← h3]
  exact hYinv _ (π _).2 y₀ hy₀

theorem le_of_inv_symDn5 [Finite V] {Gi : Subgroup (MulAut V)} {Wi : Subgroup V}
    (hp : SymmetricNatural Gi Wi ⊥ 5) {Y : Subgroup V}
    (hYW : Y ≤ Wi) (hYinv : ∀ g ∈ Gi, ∀ y ∈ Y, g y ∈ Y) {y₀ : V} (hy₀ : y₀ ∈ Y)
    (hy₀1 : y₀ ≠ 1) : Wi ≤ Y := by
  classical
  obtain ⟨π₀, hπ₀⟩ := hp
  set π : Perm (Fin 5) →* ↥Gi := π₀ with hπdef
  have hπ : (FFModel.symDn 5).RealizesVia Gi Wi ⊥ π := hπ₀
  have hker : (FFModel.symDn 5).ker = ⊥ := by
    have := Explicit.card_dnZ (n := 5) (by norm_num)
    rw [ite_eq_right (by decide)] at this
    exact Subgroup.card_eq_one.1 this
  obtain ⟨f, hfs, hfk, hfe⟩ := RealizesVia.exists_secMap hker hπ
  have hfi : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu'
    exact Subtype.ext (Subgroup.mem_bot.1 ((hfk u).1 hu'))
  set Yc : Subgroup ↥(G6.coreMod 5) := (Y.subgroupOf Wi).map f with hYc
  have hYcinv : ∀ (σ : Perm (Fin 5)) (x : ↥(G6.coreMod 5)), x ∈ Yc →
      (⟨G6.permAct 5 σ x, G6.permAct_mem_coreMod σ x.2⟩ : ↥(G6.coreMod 5)) ∈ Yc := by
    rintro σ _ ⟨u, hu, rfl⟩
    have hu' : ((π σ : ↥Gi) : MulAut V) u ∈ Wi := hπ.2.2.2.1 _ u u.2
    refine ⟨⟨_, hu'⟩, ?_, ?_⟩
    · exact hYinv _ (π σ).2 u hu
    · apply Subtype.ext
      exact hfe σ u hu'
  set x₀ : ↥(G6.coreMod 5) := f ⟨y₀, hYW hy₀⟩ with hx₀
  have hx₀Y : x₀ ∈ Yc := ⟨⟨y₀, hYW hy₀⟩, hy₀, rfl⟩
  have hx₀1 : (x₀ : G6.PermMod 5) ≠ 1 := by
    intro h0
    apply hy₀1
    have : f ⟨y₀, hYW hy₀⟩ = 1 := Subtype.ext h0
    exact Subgroup.mem_bot.1 ((hfk _).1 this)
  obtain ⟨i, hi⟩ : ∃ i, Multiplicative.toAdd (x₀ : G6.PermMod 5) i = 1 := by
    by_contra hcon
    push Not at hcon
    apply hx₀1
    apply Multiplicative.toAdd.injective
    funext l
    have := hcon l
    rcases CFSG.GroupTheory.GLnTwoSplitting.zmod_two_eq_zero_or_one
      (Multiplicative.toAdd (x₀ : G6.PermMod 5) l) with h | h
    · exact h
    · exact absurd h this
  obtain ⟨j, hj⟩ : ∃ j, Multiplicative.toAdd (x₀ : G6.PermMod 5) j = 0 := by
    by_contra hcon
    push Not at hcon
    have hall : (x₀ : G6.PermMod 5) = G6.allOnes 5 := by
      apply Multiplicative.toAdd.injective
      funext l
      exact CFSG.GroupTheory.GLnTwoSplitting.zmod_two_eq_one_of_ne_zero (hcon l)
    have := x₀.2
    rw [hall, Explicit.allOnes_mem_coreMod_iff] at this
    exact absurd this (by decide)
  have hij : i ≠ j := by
    rintro rfl
    rw [hi] at hj
    exact one_ne_zero hj
  have hpair : (⟨pairVec i j, pairVec_mem_coreMod i j⟩ : ↥(G6.coreMod 5)) ∈ Yc := by
    have h1 := Yc.mul_mem (hYcinv (swap i j) x₀ hx₀Y) hx₀Y
    convert h1 using 1
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext l
    simp only [Subgroup.coe_mul, toAdd_mul, G6.permAct_apply, pairVec, toAdd_ofAdd,
      Pi.add_apply, swap_inv]
    by_cases hli : l = i
    · subst hli
      rw [swap_apply_left, hj, hi, Pi.single_eq_same, Pi.single_eq_of_ne hij]
      rfl
    · by_cases hlj : l = j
      · subst hlj
        rw [swap_apply_right, hj, hi, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij)]
        rfl
      · rw [swap_apply_of_ne_of_ne hli hlj, Pi.single_eq_of_ne hli, Pi.single_eq_of_ne hlj,
          add_zero, CFSG.GroupTheory.GLnTwoSplitting.zmod_two_add_self]
  have hpairs : ∀ l, (⟨pairVec i l, pairVec_mem_coreMod i l⟩ : ↥(G6.coreMod 5)) ∈ Yc := by
    intro l
    by_cases hli : l = i
    · subst hli
      have : (⟨pairVec l l, pairVec_mem_coreMod l l⟩ : ↥(G6.coreMod 5)) = 1 := by
        apply Subtype.ext
        apply Multiplicative.toAdd.injective
        funext m
        simp [pairVec, CFSG.GroupTheory.GLnTwoSplitting.zmod_two_add_self]
      rw [this]
      exact Yc.one_mem
    · have h1 := hYcinv (swap j l) _ hpair
      convert h1 using 1
      apply Subtype.ext
      show pairVec i l = G6.permAct 5 (swap j l) (pairVec i j)
      rw [permAct_pairVec, swap_apply_of_ne_of_ne hij (Ne.symm hli), swap_apply_left]
  have hall : Yc = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    have hx := mem_closure_pairVec i x.2
    have hle : Subgroup.closure (Set.range (pairVec i)) ≤ Yc.map (G6.coreMod 5).subtype := by
      rw [Subgroup.closure_le]
      rintro _ ⟨l, rfl⟩
      exact ⟨_, hpairs l, rfl⟩
    obtain ⟨x', hx', hxx'⟩ := hle hx
    rw [show x = x' from Subtype.ext hxx'.symm]
    exact hx'
  intro w hw
  have hfw : f ⟨w, hw⟩ ∈ Yc := by rw [hall]; trivial
  obtain ⟨u, hu, hfu⟩ := hfw
  rw [show w = u from congrArg Subtype.val (hfi hfu).symm]
  exact hu

theorem RedPiece.eq_of_inv [Finite V] {Gi : Subgroup (MulAut V)} {Wi : Subgroup V}
    (hp : RedPiece Gi Wi ⊥) {Y : Subgroup V} (hYW : Y ≤ Wi)
    (hYinv : ∀ g ∈ Gi, ∀ y ∈ Y, g y ∈ Y) (hY : Y ≠ ⊥) : Y = Wi := by
  obtain ⟨y₀, hy₀, hy₀1⟩ : ∃ y ∈ Y, y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hY (eq_bot_iff.2 fun y hy => hcon y hy)
  refine le_antisymm hYW ?_
  rcases hp with ⟨π, hπ⟩ | ⟨π, hπ⟩ | h5
  · exact le_of_inv_natSL hπ hYW hYinv hy₀ hy₀1
  · exact le_of_inv_natSL hπ hYW hYinv hy₀ hy₀1
  · exact le_of_inv_symDn5 h5 hYW hYinv hy₀ hy₀1

end CFSG.Quasithin.G64
