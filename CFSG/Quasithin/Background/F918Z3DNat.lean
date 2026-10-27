module

public import CFSG.Quasithin.Background.F918Z3D
public import CFSG.Quasithin.Background.F918Z3A1Irr
public import CFSG.Quasithin.Background.F918Z5A3
public import CFSG.Quasithin.Background.F918Z6Symm
public import CFSG.Quasithin.Background.F918J3
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.EmptyFaithful.SzN15Nat

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank
open scoped Matrix

namespace Z3D

section Unpack

variable {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}

theorem exists_column_of_nat_realizes {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {π : ↥Γ →* ↥H}
    (h : (FFModel.nat Γ).RealizesVia H ⊤ ⊥ π) :
    ∃ b : W ≃* Multiplicative (ι → K), ∀ (γ : ↥Γ) (w : W),
      b ((π γ : MulAut W) w) = Multiplicative.ofAdd
        (((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd (b w)) := by
  have R := SzN15.NatReal.of_realizesVia h
  obtain ⟨β, hβs, hβk, hβe⟩ := R.exists_β
  let b0 : W →* Multiplicative (ι → K) := β.comp (Subgroup.topEquiv (G := W)).symm.toMonoidHom
  have hb0 : ∀ w : W, b0 w = β ⟨w, trivial⟩ := fun w => rfl
  have hinj : Function.Injective b0 := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have := (hβk ⟨w, trivial⟩).1 (by rw [← hb0]; exact hw)
    exact Subgroup.mem_bot.1 this
  have hsurj : Function.Surjective b0 := by
    intro m'
    obtain ⟨u, hu⟩ := hβs m'
    exact ⟨(u : W), by rw [hb0]; exact hu⟩
  exact ⟨MulEquiv.ofBijective b0 ⟨hinj, hsurj⟩, fun γ w => hβe γ ⟨w, trivial⟩ trivial⟩

theorem exists_column_of_binaryNaturalSL {m a : ℕ} (h : BinaryNaturalSL H ⊤ ⊥ m a) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ a ∧
      ∃ (π : ↥(StatedSL m K) →* ↥H) (b : W ≃* Multiplicative (Fin m → K)),
        Function.Surjective π ∧ ∀ (γ : ↥(StatedSL m K)) (w : W),
          b ((π γ : MulAut W) w) = Multiplicative.ofAdd
            (((γ : Matrix.GeneralLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ
              Multiplicative.toAdd (b w)) := by
  obtain ⟨K, hK, hf, hc, π, hπ⟩ := h
  obtain ⟨b, hb⟩ := exists_column_of_nat_realizes hπ
  exact ⟨K, hK, hf, hc, π, b, hπ.1, hb⟩

end Unpack

section Alternatives

variable {V : Type} [CommGroup V] {D X : Subgroup (MulAut V)} {F : Type} [Field F] {d r : ℕ}
  {β : V ≃* Multiplicative (Matrix (Fin d) (Fin r) F)}
  {ρ : ↥D →* Matrix.GeneralLinearGroup (Fin d) F}
  {σ : ↥X →* Matrix.GeneralLinearGroup (Fin r) F}

theorem exists_ringHom_of_natural (hM : IsMatModel D X β ρ σ) {I : Subgroup V} (hI0 : I ≠ ⊥)
    (hIinv : ∀ y ∈ D, ∀ v ∈ I, y v ∈ I)
    (hImin : ∀ U ≤ I, (∀ y ∈ D, ∀ v ∈ U, y v ∈ U) → U = ⊥ ∨ U = I) {ι : Type} [Fintype ι]
    [DecidableEq ι] {K : Type} [Field K] {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)}
    {π : ↥Γ →* ↥(autSub D I)} (hπs : Function.Surjective π) (b : ↥I ≃* Multiplicative (ι → K))
    (hb : ∀ (γ : ↥Γ) (w : ↥I), b ((π γ : MulAut ↥I) w) = Multiplicative.ofAdd
      (((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd (b w))) :
    ∃ f : K →+* F, Function.Injective f := by
  obtain ⟨v₀, hv₀, i₀, j₀, hij⟩ := exists_entry_ne_zero (β := β) hI0
  obtain ⟨e, he⟩ := exists_equiv_column hM hI0 hIinv hImin
  let E : (ι → K) ≃+ (Fin d → F) :=
    { toFun := fun x => Multiplicative.toAdd (e (b.symm (Multiplicative.ofAdd x)))
      invFun := fun w => Multiplicative.toAdd (b (e.symm (Multiplicative.ofAdd w)))
      left_inv := fun x => by simp
      right_inv := fun w => by simp
      map_add' := fun x y => by simp }
  have hstab := le_stabSub_of_invariant hIinv
  have hact : ∀ g : ↥D, ∃ γ : ↥Γ, ∀ x : ι → K,
      E.symm ((ρ g : Matrix (Fin d) (Fin d) F) *ᵥ E x) =
        ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ x := by
    intro g
    have hmem : resHom I ⟨(g : MulAut V), hstab g.2⟩ ∈ autSub D I :=
      mem_autSub.2 ⟨⟨g, hstab g.2⟩, g.2, rfl⟩
    obtain ⟨γ, hγ⟩ := hπs ⟨_, hmem⟩
    refine ⟨γ, fun x => ?_⟩
    have hbu : b (b.symm (Multiplicative.ofAdd x)) = Multiplicative.ofAdd x :=
      b.apply_symm_apply _
    have hv : (g : MulAut V) ((b.symm (Multiplicative.ofAdd x) : ↥I) : V) ∈ I :=
      hIinv g g.2 _ (b.symm (Multiplicative.ofAdd x)).2
    have h1 := he g (b.symm (Multiplicative.ofAdd x)) hv
    have hπu : ((π γ : ↥(autSub D I)) : MulAut ↥I) (b.symm (Multiplicative.ofAdd x)) =
        ⟨(g : MulAut V) ((b.symm (Multiplicative.ofAdd x) : ↥I) : V), hv⟩ := by
      rw [hγ]
      rfl
    have h2 := hb γ (b.symm (Multiplicative.ofAdd x))
    rw [hπu, hbu] at h2
    change Multiplicative.toAdd (b (e.symm (Multiplicative.ofAdd
      ((ρ g : Matrix (Fin d) (Fin d) F) *ᵥ
        Multiplicative.toAdd (e (b.symm (Multiplicative.ofAdd x))))))) = _
    rw [← h1, MulEquiv.symm_apply_apply, h2]
    rfl
  obtain ⟨f, -⟩ := exists_ringHom_of_commuting_scalars (K := K) hM (Fin.pos i₀) E fun g c x => by
    obtain ⟨γ, hγ⟩ := hact g
    rw [hγ, hγ, Matrix.mulVec_smul]
  exact ⟨f, f.injective⟩

theorem false_of_binaryNaturalSL_two [Finite F] (hM : IsMatModel D X β ρ σ) (hd : 3 ≤ d)
    {I : Subgroup V} (hI0 : I ≠ ⊥) (hIinv : ∀ y ∈ D, ∀ v ∈ I, y v ∈ I)
    (hImin : ∀ U ≤ I, (∀ y ∈ D, ∀ v ∈ U, y v ∈ U) → U = ⊥ ∨ U = I) {n : ℕ} (hn : 2 ≤ n)
    (h : BinaryNaturalSL (autSub D I) ⊤ ⊥ 2 n) : False := by
  obtain ⟨K, hKf, hKfin, hKc, π, b, hπs, hb⟩ := exists_column_of_binaryNaturalSL h
  obtain ⟨f, hf⟩ := exists_ringHom_of_natural hM hI0 hIinv hImin hπs b hb
  have hle : Nat.card K ≤ Nat.card F := Nat.card_le_card_of_injective f hf
  have hcK : Nat.card ↥I = Nat.card K ^ 2 := card_eq_pow_of_equiv b
  have hcF : Nat.card ↥I = Nat.card F ^ d := card_eq_pow hM hI0 hIinv hImin
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKc]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h1 : Nat.card K ^ 2 = Nat.card F ^ d := hcK.symm.trans hcF
  have h2 : Nat.card K ^ d ≤ Nat.card F ^ d := Nat.pow_le_pow_left hle d
  have h3 : Nat.card K ^ 3 ≤ Nat.card K ^ d := Nat.pow_le_pow_right (by omega) hd
  have h4 : Nat.card K ^ 2 < Nat.card K ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

theorem card_of_binaryNaturalSL_three [Finite F] (hM : IsMatModel D X β ρ σ) (hd : 3 ≤ d)
    {I : Subgroup V} (hI0 : I ≠ ⊥) (hIinv : ∀ y ∈ D, ∀ v ∈ I, y v ∈ I)
    (hImin : ∀ U ≤ I, (∀ y ∈ D, ∀ v ∈ U, y v ∈ U) → U = ⊥ ∨ U = I)
    (h : BinaryNaturalSL (autSub D I) ⊤ ⊥ 3 1) : d = 3 ∧ Nat.card F = 2 := by
  obtain ⟨K, hKf, hKfin, hKc, π, b, hπs, hb⟩ := exists_column_of_binaryNaturalSL h
  have hcK : Nat.card ↥I = Nat.card K ^ 3 := card_eq_pow_of_equiv b
  have hcF : Nat.card ↥I = Nat.card F ^ d := card_eq_pow hM hI0 hIinv hImin
  have hF2 : 2 ≤ Nat.card F := Finite.one_lt_card
  have h8 : Nat.card F ^ d = 8 := by
    rw [← hcF, hcK, hKc]
    norm_num
  have hq : Nat.card F = 2 := by
    by_contra hne
    have h3 : 3 ≤ Nat.card F := by omega
    have h27 : 27 ≤ Nat.card F ^ d :=
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ Nat.card F ^ 3 := Nat.pow_le_pow_left h3 3
        _ ≤ Nat.card F ^ d := Nat.pow_le_pow_right (by omega) hd
    omega
  refine ⟨?_, hq⟩
  rw [hq] at h8
  exact Nat.pow_right_injective (le_refl 2) (h8.trans (by norm_num : (8 : ℕ) = 2 ^ 3))

end Alternatives

section Three

theorem isPSL_three_two_of_equiv {G : Type} [Group G] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (e : G ≃* ↥(StatedSL 3 K)) : IsPSL 3 2 1 G := by
  have hu := subsingleton_units_of_card_two hK
  have hsc : StatedScalars (Fin 3) K = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro _ ⟨c, rfl⟩
    rw [Subsingleton.elim c 1, map_one]
  have hN : (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K) = ⊥ := by
    rw [hsc, Subgroup.bot_subgroupOf]
  refine ⟨⟨Nat.prime_two, le_refl 1, by norm_num, by decide, by decide⟩, K, inferInstance,
    inferInstance, by simpa using hK, ⟨?_⟩⟩
  exact e.trans ((QuotientGroup.quotientBot (G := ↥(StatedSL 3 K))).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hN.symm))

variable {V : Type} [CommGroup V] [Finite V] {D X G T' : Subgroup (MulAut V)} {s : MulAut V}

theorem natural_case (hZ : Z37 D X G T' s) {F : Type} [Field F] [Finite F] [CharP F 2] {d : ℕ}
    (hd : 3 ≤ d) (β : V ≃* Multiplicative (Matrix (Fin d) (Fin d) F))
    (ρ : ↥D →* Matrix.GeneralLinearGroup (Fin d) F)
    (σ : ↥X →* Matrix.GeneralLinearGroup (Fin d) F) (hM : IsMatModel D X β ρ σ)
    {I : Subgroup V} (hI0 : I ≠ ⊥) (hIinv : ∀ y ∈ D, ∀ v ∈ I, y v ∈ I)
    (hImin : ∀ U ≤ I, (∀ y ∈ D, ∀ v ∈ U, y v ∈ U) → U = ⊥ ∨ U = I)
    (hnat : (∃ n, 2 ≤ n ∧ BinaryNaturalSL (autSub D I) ⊤ ⊥ 2 n) ∨
      BinaryNaturalSL (autSub D I) ⊤ ⊥ 3 1) : Z37Concl D X := by
  rcases hnat with ⟨n, hn, h2⟩ | h3
  · exact (false_of_binaryNaturalSL_two hM hd hI0 hIinv hImin hn h2).elim
  · obtain ⟨hd3, hF2⟩ := card_of_binaryNaturalSL_three hM hd hI0 hIinv hImin h3
    have hfaith : D ⊓ centSub I = ⊥ :=
      eq_bot_iff.2 fun g hg => Subgroup.mem_bot.2 (Z3A1.faithful hZ hI0 hIinv g hg.1 hg.2)
    obtain ⟨K, hKf, hKfin, hKc, ⟨eSL⟩⟩ := BinaryNaturalSL.exists_equiv h3
    have hK2 : Nat.card K = 2 := by simpa using hKc
    let eD : ↥D ≃* ↥(StatedSL 3 K) :=
      (autSubEquivOfFaithful (le_stabSub_of_invariant hIinv) hfaith).trans eSL.symm
    have hDpsl : IsPSL 3 2 1 ↥D := isPSL_three_two_of_equiv hK2 eD
    have hXpsl : IsPSL 3 2 1 ↥X :=
      isPSL_three_two_of_equiv hK2 ((conjEquivOfEq hZ.swapDX).symm.trans eD)
    subst hd3
    exact Or.inr ⟨hDpsl, tensorNatL32_of_sqModel_three hZ.comm hF2 β ρ σ hM hDpsl hXpsl⟩

end Three

end Z3D

end CFSG.Quasithin
