module

public import CFSG.Quasithin.EmptyFaithful.T1515dB
public import CFSG.Quasithin.Background.HL42Aut
public import CFSG.Quasithin.Background.B5FinS8
public import CFSG.Quasithin.Background.F918F1
import CFSG.Open.StatedZModTwo

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.JonesParshall CFSG.QuasithinUnique Matrix
open scoped commutatorElement

namespace LRed4


theorem transv_sq : ∀ i j : Fin 4, i ≠ j →
    ((1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) + Matrix.single i j 1) *
      (1 + Matrix.single i j 1) = 1 := by
  decide +kernel

@[expose] def transv4 (i j : Fin 4) (hij : i ≠ j) : GL (Fin 4) (ZMod 2) :=
  ⟨1 + Matrix.single i j 1, 1 + Matrix.single i j 1, transv_sq i j hij, transv_sq i j hij⟩

theorem lam2_fixed_zero (w : Fin 6 → ZMod 2)
    (h : ∀ γ : ↥(StatedSL 4 (ZMod 2)), wedgeRep4 γ w = w) : w = 0 := by
  have key : ∀ w : Fin 6 → ZMod 2, (∀ i j : Fin 4, i ≠ j →
      wedgeMat4 ((1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) + Matrix.single i j 1) *ᵥ w = w) →
      w = 0 := by decide +kernel
  apply key
  intro i j hij
  have h1 := h (B5FinS8.slEquiv.symm (transv4 i j hij))
  rw [wedgeRep4_apply] at h1
  have h2 := B5FinS8.slEquiv_apply (B5FinS8.slEquiv.symm (transv4 i j hij))
  rw [MulEquiv.apply_symm_apply] at h2
  rw [← h2] at h1
  exact h1

theorem no_epi_sl5 {K : Type} [Group K] [Finite K] (hK : Nat.card K = 20160)
    (π : ↥(StatedSL 5 (ZMod 2)) →* K) (hπ : Function.Surjective π) : False := by
  have hs : IsSimpleGroup ↥(StatedSL 5 (ZMod 2)) :=
    CFSG.Quasithin.B69.isSimpleGroup_statedSL_two (by simp) (by norm_num)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with hbot | htop
  · have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 hbot
    have h1 : Nat.card ↥(StatedSL 5 (ZMod 2)) = Nat.card K :=
      Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ⟩)
    rw [card_statedSL_five_zmod1527d] at h1
    omega
  · have hsub : Subsingleton K := ⟨fun a b => by
      obtain ⟨x, rfl⟩ := hπ a
      obtain ⟨y, rfl⟩ := hπ b
      have hx : x ∈ π.ker := by rw [htop]; trivial
      have hy : y ∈ π.ker := by rw [htop]; trivial
      rw [MonoidHom.mem_ker.1 hx, MonoidHom.mem_ker.1 hy]⟩
    have := Nat.card_of_subsingleton (1 : K)
    omega

@[expose] noncomputable def commEquivAlt8 {V : Type} [CommGroup V] {X : Subgroup (MulAut V)}
    (θ : ↥X ≃* Equiv.Perm (Fin 8)) : ↥⁅X, X⁆ ≃* ↥(alternatingGroup (Fin 8)) := by
  have hA : commutator (Equiv.Perm (Fin 8)) = alternatingGroup (Fin 8) :=
    alternatingGroup.commutator_perm_eq (by simp)
  have h1 : (commutator ↥X).map X.subtype = ⁅X, X⁆ := Subgroup.map_subtype_commutator X
  have h2 : (commutator ↥X).map θ.toMonoidHom = alternatingGroup (Fin 8) := by
    rw [← hA, commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top.2 θ.surjective, ← commutator_def]
  exact (MulEquiv.subgroupCongr h1.symm).trans
    ((Subgroup.equivMapOfInjective (commutator ↥X) X.subtype X.subtype_injective).symm.trans
      ((Subgroup.equivMapOfInjective (commutator ↥X) θ.toMonoidHom θ.injective).trans
        (MulEquiv.subgroupCongr h2)))

@[expose] noncomputable def commEquivSL4 {V : Type} [CommGroup V] {X : Subgroup (MulAut V)}
    (θ : ↥X ≃* Equiv.Perm (Fin 8)) : ↥⁅X, X⁆ ≃* ↥(StatedSL 4 (ZMod 2)) :=
  (commEquivAlt8 θ).trans (H.L4.alpha8.trans B5FinS8.slEquiv.symm)

theorem card_comm_s8 {V : Type} [CommGroup V] {X : Subgroup (MulAut V)}
    (θ : ↥X ≃* Equiv.Perm (Fin 8)) : Nat.card ↥⁅X, X⁆ = 20160 := by
  rw [Nat.card_congr (commEquivSL4 θ).toEquiv]
  exact card_statedSL_four_zmod1527d


section Alt

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem comm_conj_mem {X : Subgroup (MulAut V)} {x k : MulAut V} (hx : x ∈ X) (hk : k ∈ ⁅X, X⁆) :
    x * k * x⁻¹ ∈ ⁅X, X⁆ := by
  have hn := Subgroup.normalizer_commutator_ge_left X X hx
  exact (Subgroup.mem_normalizer_iff.mp hn k).mp hk

omit [Finite V] in
theorem fixV_comm_invariant {X : Subgroup (MulAut V)} {x : MulAut V} (hx : x ∈ X) {z : V}
    (hz : z ∈ fixV ⁅X, X⁆) : x z ∈ fixV ⁅X, X⁆ := by
  intro k hk
  have hk' : x⁻¹ * k * x ∈ ⁅X, X⁆ := by
    have := comm_conj_mem (X := X) (X.inv_mem hx) hk
    simpa using this
  have h1 := hz _ hk'
  calc k (x z) = (x * (x⁻¹ * k * x)) z := by simp [mul_assoc]
    _ = x ((x⁻¹ * k * x) z) := rfl
    _ = x z := by rw [h1]

omit [Finite V] in
theorem fixV_le_of_extTwo {K : Subgroup (MulAut V)} {U Z : Subgroup V}
    (h : SLExteriorTwo K U Z 4) (hU : U = ⊤) : fixV K ≤ Z := by
  subst hU
  obtain ⟨π, β, hπs, -, -, hβs, hβk, hβe⟩ := sl4ExteriorTwo_coord h
  intro u hu
  have h0 : Multiplicative.toAdd (β ⟨u, trivial⟩) = 0 := by
    apply lam2_fixed_zero
    intro γ
    have h1 := hβe γ ⟨u, trivial⟩ trivial
    have h2 : ((π γ : ↥K) : MulAut V) u = u := hu _ (π γ).2
    have h3 : (⟨((π γ : ↥K) : MulAut V) u, trivial⟩ : ↥(⊤ : Subgroup V)) = ⟨u, trivial⟩ :=
      Subtype.ext h2
    rw [h3] at h1
    exact (Multiplicative.toAdd.injective (by simpa using h1.symm)).symm ▸ rfl
  have : β ⟨u, trivial⟩ = 1 := by
    apply Multiplicative.toAdd.injective
    simpa using h0
  exact (hβk _).1 this


theorem sym_of_alt {X : Subgroup (MulAut V)} (θ : ↥X ≃* Equiv.Perm (Fin 8))
    (hcomm : commV ⁅X, X⁆ = ⊤) (halt : Alt15127 ⁅X, X⁆ (commV ⁅X, X⁆))
    (h4 : ¬ SumNatDual ⁅X, X⁆ ⊤ 4)
    (h4' : ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ 3 ∧
      DirectSumOfCopies ⁅X, X⁆ ⊤ ⊥ (FFModel.nat (StatedSL 4 (ZMod 2))) k) :
    ∃ Z : Subgroup V, Z ≤ fixV ⁅X, X⁆ ∧ Nat.card Z ≤ 2 ∧ SymmetricNatural X ⊤ Z 8 := by
  rw [hcomm] at halt
  have hcard := card_comm_s8 θ
  rcases halt with ⟨Z, hZ, hZc, hex⟩ | h5 | ⟨n, hn⟩ | ⟨n, hn45, k, hk1, hk2, hdir⟩
  · refine ⟨Z, fun z hz => (hZ hz).1, hZc, ?_⟩
    have hfix : fixV ⁅X, X⁆ ≤ Z := fixV_le_of_extTwo hex rfl
    have hZinv : ∀ x ∈ X, ∀ z ∈ Z, x z ∈ Z := fun x hx z hz =>
      hfix (fixV_comm_invariant hx (hZ hz).1)
    exact B5FinS8.symmetricNatural_eight_of_exteriorTwo θ hex (fun _ _ _ _ => trivial) hZinv
  · obtain ⟨π, hπ⟩ := h5
    exact (no_epi_sl5 hcard π hπ.1).elim
  · obtain ⟨hn45, π, U₁, U₂, hdirect, h1, h2⟩ := hn
    rcases hn45 with rfl | rfl
    · exact (h4 ⟨Or.inl rfl, π, U₁, U₂, hdirect, h1, h2⟩).elim
    · exact (no_epi_sl5 hcard π h1.1).elim
  · obtain ⟨I, π, hI1, hI2, hI3, hreal⟩ := hdir
    rcases hn45 with rfl | rfl
    · exact (h4' ⟨k, hk1, by omega, ⟨I, π, hI1, hI2, hI3, hreal⟩⟩).elim
    · exact (no_epi_sl5 hcard π (hreal ⟨0, by omega⟩).1).elim


end Alt

theorem isPSL_two_of_statedSL' {n : ℕ} (hn : 3 ≤ n) {X : Type} [Group X]
    (e : X ≃* ↥(StatedSL n (ZMod 2))) : IsPSL n 2 1 X :=
  CFSG.Open.StatedAPI.statedClassicalModel_psl_of_mulEquiv_statedSL_zmod_two hn e

theorem isPSL_comm_s8 {V : Type} [CommGroup V] {X : Subgroup (MulAut V)}
    (θ : ↥X ≃* Equiv.Perm (Fin 8)) : IsPSL 4 2 1 ↥⁅X, X⁆ :=
  isPSL_two_of_statedSL' (by norm_num) (commEquivSL4 θ)

end LRed4

end CFSG.Quasithin
