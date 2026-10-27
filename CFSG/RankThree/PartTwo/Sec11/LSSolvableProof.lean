module

public import CFSG.RankThree.PartTwo.Sec11.LSSolvableProofHeis
public import CFSG.RankThree.SteinbergR3ELargeEvenLinearTwoCover
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.RankThree.PartTwo.Sec11.LSSolvableProofKlein

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG.Assembly.RankThreeEven (projSL)

namespace LSSolvableProof

open Module

theorem card_projSL_two_even (f : ℕ) (hf : 1 ≤ f) :
    Nat.card (projSL 2 (GaloisField 2 f)) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  rw [← Nat.card_congr (CFSG.RankThree.PartTwo.KFacts.KS116Proof.projSLEquiv
      (GaloisField 2 f)).toEquiv,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, GaloisField.card 2 f (by omega)]

theorem le_card_projSL_two_even {f : ℕ} (hf : 6 ≤ f) :
    262080 ≤ Nat.card (projSL 2 (GaloisField 2 f)) := by
  rw [card_projSL_two_even f (by omega)]
  have h64 : 64 ≤ 2 ^ f := by
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h1 : 4096 ≤ (2 ^ f) ^ 2 := by
    calc 4096 = 64 ^ 2 := by norm_num
      _ ≤ (2 ^ f) ^ 2 := Nat.pow_le_pow_left h64 2
  calc 262080 = 64 * (4096 - 1) := by norm_num
    _ ≤ 2 ^ f * ((2 ^ f) ^ 2 - 1) := Nat.mul_le_mul h64 (by omega)

theorem index_lt_eq_top {X : Type*} [Group X] [Finite X] [Group.IsPerfect X] {N : Subgroup X}
    [N.Normal] (hN : Group.IsSolvable N) {f : ℕ} (hf : 6 ≤ f)
    (e : X ⧸ N ≃* projSL 2 (GaloisField 2 f)) :
    ∀ J : Subgroup X, J.Normal → J.index < 262080 → J = ⊤ := by
  intro J _ hidx
  by_contra hJ
  have : IsSimpleGroup (projSL 2 (GaloisField 2 f)) := isSimpleGroup_projSL (by omega)
  have hsimple : IsSimpleGroup (X ⧸ N) := MulEquiv.isSimpleGroup e
  obtain ⟨x, hx⟩ : ∃ x, x ∉ J := by
    by_contra hall
    push Not at hall
    exact hJ (eq_top_iff.mpr fun x _ => hall x)
  have hρ : ∃ x, QuotientGroup.mk' J x ≠ 1 := ⟨x, by
    rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]; exact hx⟩
  have hJN : (QuotientGroup.mk' J).ker ≤ N := ker_le_of_perfect hN hsimple _ hρ
  rw [QuotientGroup.ker_mk'] at hJN
  have hdvd := Subgroup.index_dvd_of_le hJN
  have hpos : 0 < J.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hle := Nat.le_of_dvd hpos hdvd
  have hN' : N.index = Nat.card (projSL 2 (GaloisField 2 f)) := by
    rw [Subgroup.index_eq_card, Nat.card_congr e.toEquiv]
  have := le_card_projSL_two_even hf
  omega

theorem seven_le_finrank_of_irreducible
    {f : ℕ} (hf : 6 ≤ f) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {Y : Type} [Group Y] [Finite Y] [Group.IsPerfect Y]
    (M : Subgroup Y) [M.Normal] (hM : Group.IsSolvable M)
    (e : Y ⧸ M ≃* projSL 2 (GaloisField 2 f))
    (hsmall : ∀ J : Subgroup Y, J.Normal → J.index < 262080 → J = ⊤)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V] [Nontrivial V]
    (ρ : Y →* (V →ₗ[ZMod p] V)) (hρ : Function.Injective ρ) (hirr : IsIrreducibleRep ρ) :
    7 ≤ Module.finrank (ZMod p) V := by
  by_contra hlt
  push Not at hlt
  have hdim : Module.finrank (ZMod p) V ≤ 6 := by omega
  have : IsSimpleGroup (projSL 2 (GaloisField 2 f)) := isSimpleGroup_projSL (by omega)
  have hsimple : IsSimpleGroup (Y ⧸ M) := MulEquiv.isSimpleGroup e
  have hZM : Subgroup.center Y ≤ M := by
    have hcen : Subgroup.center (Y ⧸ M) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (Y ⧸ M)) with h | h
      · exact h
      · exfalso
        have h1 : ⁅(⊤ : Subgroup (Y ⧸ M)), (⊤ : Subgroup (Y ⧸ M))⁆ = ⊥ := by
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.coe_top,
            Subgroup.centralizer_univ, h]
        have h2 : ⁅(⊤ : Subgroup (Y ⧸ M)), (⊤ : Subgroup (Y ⧸ M))⁆ = ⊤ := by
          rw [← commutator_def]
          exact Group.IsPerfect.commutator_eq_top
        obtain ⟨a, b, hab⟩ := exists_pair_ne (Y ⧸ M)
        have h3 : (⊤ : Subgroup (Y ⧸ M)) = ⊥ := h2.symm.trans h1
        have ha : a ∈ (⊥ : Subgroup (Y ⧸ M)) := h3 ▸ Subgroup.mem_top a
        have hb : b ∈ (⊥ : Subgroup (Y ⧸ M)) := h3 ▸ Subgroup.mem_top b
        rw [Subgroup.mem_bot] at ha hb
        exact hab (ha.trans hb.symm)
    intro z hz
    have hz' : QuotientGroup.mk' M z ∈ Subgroup.center (Y ⧸ M) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective M q
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
    rw [hcen, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hz'
    exact hz'
  by_cases hMZ : M ≤ Subgroup.center Y
  ·
    set π : Y →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f) :=
      (Sec4.projSLEquivPSL (GaloisField 2 f)).toMonoidHom.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' M)) with hπ
    have hπs : Function.Surjective π :=
      (Sec4.projSLEquivPSL _).surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective M))
    have hker : π.ker = M := by
      ext x
      rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
        MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    obtain ⟨hbot, -⟩ := CFSG.RankThree.large_even_linear_two_perfect_full_central_cover_trivial
      (f := f) (by omega) (GaloisField.card 2 f (by omega)) π hπs (hker ▸ hMZ)
    rw [hker] at hbot
    have hinj : Function.Injective (QuotientGroup.mk' M) := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']; exact hbot
    set E : Y ≃* projSL 2 (GaloisField 2 f) :=
      (MulEquiv.ofBijective (QuotientGroup.mk' M) ⟨hinj, QuotientGroup.mk'_surjective M⟩).trans e
    have hρ' : Function.Injective (ρ.comp E.symm.toMonoidHom) := hρ.comp E.symm.injective
    have hLS := (CFSG.RankThree.PartTwo.KFacts.landazuriSeitzL2Even f (by omega) p hp2 V
      (ρ.comp E.symm.toMonoidHom) hρ').1
    have h64 : 64 ≤ 2 ^ f := by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  · obtain ⟨R, hRn, hZR, hRZ, hRR, s, hs, hpow, hact⟩ := exists_noncentral_normal M hM hMZ
    have : R.Normal := hRn
    exact false_of_noncentral_normal hρ hirr hdim hsmall R hZR hRZ hRR hs hpow hact

end LSSolvableProof

open LSSolvableProof in
theorem l2EvenSolvableMinDegree :
    L2EvenSolvableMinDegree := by
  intro f hf p _ hp5 X _ _ hperf N _ hN _ hiso
  obtain ⟨e⟩ := hiso
  have hp2 : p ≠ 2 := by omega
  have : IsSimpleGroup (projSL 2 (GaloisField 2 f)) := isSimpleGroup_projSL (by omega)
  have hsimple : IsSimpleGroup (X ⧸ N) := MulEquiv.isSimpleGroup e
  have hsmallX := @index_lt_eq_top X _ _ hperf N _ hN f hf e
  suffices H : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V]
      [Module.Finite (ZMod p) V] (ρ : X →* (V →ₗ[ZMod p] V)),
      Module.finrank (ZMod p) V = n → (∃ x, ρ x ≠ 1) → 7 ≤ n by
    intro V _ _ _ ρ hρ
    exact H _ V ρ rfl hρ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ ρ hn hρ
  have hVnt : Nontrivial V := by
    by_contra hsub
    rw [not_nontrivial_iff_subsingleton] at hsub
    obtain ⟨x, hx⟩ := hρ
    exact hx (LinearMap.ext fun v => Subsingleton.elim _ _)
  by_cases hirr : IsIrreducibleRep ρ
  ·
    have hKN : ρ.ker ≤ N := @ker_le_of_perfect X _ hperf N _ hN hsimple _ _ ρ hρ
    have : Group.IsPerfect X := hperf
    set ρbar : X ⧸ ρ.ker →* (V →ₗ[ZMod p] V) := QuotientGroup.lift ρ.ker ρ (fun _ hx => hx)
      with hρbar
    have hinj : Function.Injective ρbar := liftKer_injective ρ
    set M : Subgroup (X ⧸ ρ.ker) := N.map (QuotientGroup.mk' ρ.ker) with hM
    have hMsolv : Group.IsSolvable M := by
      have : Group.IsSolvable N := hN
      refine Group.isSolvable_of_surjective
        (f := ((QuotientGroup.mk' ρ.ker).comp N.subtype).codRestrict M (fun x => ⟨x, x.2, rfl⟩))
        ?_
      rintro ⟨_, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    set e' : (X ⧸ ρ.ker) ⧸ M ≃* projSL 2 (GaloisField 2 f) :=
      (QuotientGroup.quotientQuotientEquivQuotient ρ.ker N hKN).trans e with he'
    have hsmallY : ∀ J : Subgroup (X ⧸ ρ.ker), J.Normal → J.index < 262080 → J = ⊤ := by
      intro J hJ hidx
      have h1 : (J.comap (QuotientGroup.mk' ρ.ker)).index = J.index :=
        Subgroup.index_comap_of_surjective J (QuotientGroup.mk'_surjective ρ.ker)
      have h2 := hsmallX (J.comap (QuotientGroup.mk' ρ.ker)) (hJ.comap _) (h1 ▸ hidx)
      rw [eq_top_iff]
      intro q _
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ρ.ker q
      have : x ∈ J.comap (QuotientGroup.mk' ρ.ker) := by rw [h2]; exact Subgroup.mem_top x
      exact this
    have hirr' : IsIrreducibleRep ρbar := by
      intro W hW
      apply hirr W
      intro x v hv
      have := hW (QuotientGroup.mk' ρ.ker x) v hv
      rwa [hρbar, QuotientGroup.mk'_apply, QuotientGroup.lift_mk] at this
    rw [← hn]
    exact seven_le_finrank_of_irreducible hf hp2 M hMsolv e' hsmallY ρbar hinj hirr'
  ·
    obtain ⟨W, hW, hW0, hWt⟩ : ∃ W : Submodule (ZMod p) V, (∀ x, ∀ v ∈ W, ρ x v ∈ W) ∧
        W ≠ ⊥ ∧ W ≠ ⊤ := by
      by_contra hall
      push Not at hall
      exact hirr fun W hW => by
        by_cases h0 : W = ⊥
        · exact Or.inl h0
        · exact Or.inr (hall W hW h0)
    let ρW : X →* (W →ₗ[ZMod p] W) :=
      { toFun := fun x => (ρ x).restrict (p := W) (q := W) (hW x)
        map_one' := by
          apply LinearMap.ext
          intro w
          apply Subtype.ext
          simp
        map_mul' := fun x y => by
          apply LinearMap.ext
          intro w
          apply Subtype.ext
          simp }
    let ρQ : X →* ((V ⧸ W) →ₗ[ZMod p] (V ⧸ W)) :=
      { toFun := fun x => W.mapQ W (ρ x) (fun v hv => hW x v hv)
        map_one' := by
          apply Submodule.linearMap_qext
          apply LinearMap.ext
          intro v
          simp
        map_mul' := fun x y => by
          apply Submodule.linearMap_qext
          apply LinearMap.ext
          intro v
          simp }
    have hWlt : Module.finrank (ZMod p) W < n := hn ▸ Submodule.finrank_lt hWt
    have hQlt : Module.finrank (ZMod p) (V ⧸ W) < n := by
      have h1 := W.finrank_quotient_add_finrank
      have h2 : 0 < Module.finrank (ZMod p) W := by
        rw [Module.finrank_pos_iff]
        exact Submodule.nontrivial_iff_ne_bot.mpr hW0
      omega
    by_cases hρW : ∃ x, ρW x ≠ 1
    · have h1 := ih _ hWlt W ρW rfl hρW
      have h2 : Module.finrank (ZMod p) W ≤ n := hn ▸ Submodule.finrank_le W
      omega
    by_cases hρQ : ∃ x, ρQ x ≠ 1
    · have h1 := ih _ hQlt (V ⧸ W) ρQ rfl hρQ
      omega
    exfalso
    push Not at hρW hρQ
    have hfixW : ∀ x, ∀ w ∈ W, ρ x w = w := by
      intro x w hw
      have := congrArg (fun φ : W →ₗ[ZMod p] W => ((φ ⟨w, hw⟩ : W) : V)) (hρW x)
      simpa [ρW] using this
    have hfixQ : ∀ x v, ρ x v - v ∈ W := by
      intro x v
      have := congrArg (fun φ : (V ⧸ W) →ₗ[ZMod p] (V ⧸ W) => φ (Submodule.Quotient.mk v))
        (hρQ x)
      simp only [ρQ, MonoidHom.coe_mk, OneHom.coe_mk, Submodule.mapQ_apply,
        Module.End.one_apply] at this
      exact (Submodule.Quotient.eq W).mp this
    have hcomm : ∀ x y, ρ x * ρ y = ρ y * ρ x := by
      intro x y
      apply LinearMap.ext
      intro v
      rw [Module.End.mul_apply, Module.End.mul_apply]
      have ha := hfixQ x v
      have hb := hfixQ y v
      have e1 : ρ y v = v + (ρ y v - v) := by abel
      have e2 : ρ x v = v + (ρ x v - v) := by abel
      rw [e1, map_add, hfixW x _ hb, e2, map_add, hfixW y _ ha]
      abel
    have hker : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ ≤ ρ.ker := by
      rw [Subgroup.commutator_le]
      intro x _ y _
      rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, hcomm x y,
        mul_assoc (ρ y), ← map_mul, mul_inv_cancel, map_one, mul_one, ← map_mul,
        mul_inv_cancel, map_one]
    have htop : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ := by
      rw [← commutator_def]
      exact Group.IsPerfect.commutator_eq_top
    rw [htop] at hker
    obtain ⟨x, hx⟩ := hρ
    exact hx (hker (Subgroup.mem_top x))

open LSSolvableProof in
theorem landazuriSeitzL2EvenSolvable :
    LandazuriSeitzL2EvenSolvable :=
  landazuriSeitzL2EvenSolvable_of_minDegree l2EvenSolvableMinDegree

end CFSG.RankThree.PartTwo.Sec11
