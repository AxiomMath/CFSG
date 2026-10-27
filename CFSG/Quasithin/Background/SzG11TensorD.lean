module

public import CFSG.Quasithin.Background.SzG11TensorB
public import CFSG.Quasithin.Background.E11End

public section

namespace CFSG.Quasithin

namespace G11

namespace SzG11S

namespace Tensor

section Alt

variable {G : Type*} [Group G]

theorem isPerfect_of_alt_five (e : G ≃* ↥(alternatingGroup (Fin 5))) : Group.IsPerfect G := by
  have h : Group.IsPerfect ↥(alternatingGroup (Fin 5)) :=
    Group.isPerfect_def.2 (commutator_alternatingGroup_eq_top (by simp))
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem commutator_eq_top_of_alt_five (e : G ≃* ↥(alternatingGroup (Fin 5))) :
    commutator G = ⊤ :=
  Group.isPerfect_def.1 (isPerfect_of_alt_five e)

theorem natCard_of_alt_five (e : G ≃* ↥(alternatingGroup (Fin 5))) : Nat.card G = 60 := by
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  simp [Nat.factorial]

end Alt

section Kappa

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {H : Subgroup (GLV V)}
  {I : Submodule (ZMod 2) V}

theorem exists_kappa (D : E11Data H I) (hF : Nat.card D.F = 4) :
    ∃ κ : GaloisField 2 2 →ₐ[ZMod 2] Module.End (ZMod 2) ↥I,
      (∀ k, κ k ∈ endOn H I) ∧ ∀ f ∈ endOn H I, ∃ k, κ k = f := by
  have hK4 : Nat.card D.F = 2 ^ 2 := by rw [hF]; norm_num
  let eF : D.F ≃ₐ[ZMod 2] GaloisField 2 2 := GaloisField.algEquivGaloisField 2 2 hK4
  let κ : GaloisField 2 2 →ₐ[ZMod 2] Module.End (ZMod 2) ↥I :=
    ((endOn H I).val.comp D.endEquiv.symm.toAlgHom).comp eF.symm.toAlgHom
  refine ⟨κ, fun k => (D.endEquiv.symm (eF.symm k)).2, fun f hf => ⟨eF (D.endEquiv ⟨f, hf⟩), ?_⟩⟩
  show ((D.endEquiv.symm (eF.symm (eF (D.endEquiv ⟨f, hf⟩))) : endOn H I) :
    Module.End (ZMod 2) ↥I) = f
  rw [AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply]

theorem kappa_comm {K : Type} [Field K] [Algebra (ZMod 2) K]
    (κ : K →ₐ[ZMod 2] Module.End (ZMod 2) ↥I) (hκ : ∀ k, κ k ∈ endOn H I)
    (hI : Invariant H I) (k : K) (h : ↥H) (x : ↥I) :
    κ k (restrictHom H I hI h x) = restrictHom H I hI h (κ k x) := by
  have h1 := (E11.mem_endOn_iff (κ k) hI).1 (hκ k) (h : GLV V) h.2 x
  refine Subtype.ext ?_
  rw [coe_restrictHom]
  exact h1.symm

theorem restrictHom_injective (hI : Invariant H I) (hfaith : FaithfulOn H I) :
    Function.Injective (restrictHom H I hI) := by
  rw [injective_iff_map_eq_one]
  intro k hk
  have h1 := faithfulOn_iff.1 hfaith (k : GLV V) k.2 (restrictHom_eq_one_iff.1 hk)
  exact Subtype.ext h1

end Kappa

section Decomposition

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {H C : Subgroup (GLV V)}
  {I : Submodule (ZMod 2) V}

omit [Finite V] in
theorem exists_endOn_of_centralizer (hI : Invariant H I) (htop : I = ⊤) {c : GLV V}
    (hc : c ∈ Subgroup.centralizer (H : Set (GLV V))) :
    ∃ f ∈ endOn H I, ∀ i : ↥I, ((f i : ↥I) : V) = c (i : V) := by
  let f : Module.End (ZMod 2) ↥I :=
    LinearMap.restrict (c : V →ₗ[ZMod 2] V) (p := I) (q := I) (fun x _ => by rw [htop]; trivial)
  refine ⟨f, (E11.mem_endOn_iff f hI).2 fun h hh i => ?_, fun i => rfl⟩
  have := Subgroup.mem_centralizer_iff.1 hc h hh
  exact congrArg (fun g : GLV V => g (i : V)) this

theorem exists_complement_hiso (hhom : Homogeneous H) (hI : IrrPlus H I) (hfix : fixedSpace H = ⊥)
    (hsum : sSup {J : Submodule (ZMod 2) V | IsIrr H J} = ⊤)
    (hd : Module.finrank (ZMod 2) V = 8) (hfaith : FaithfulOn H I)
    (hHperf : commutator ↥H = ⊤) (hHcard : Nat.card ↥H = 60)
    (hCperf : commutator ↥C = ⊤) (hCcard : Nat.card ↥C = 60)
    (hcent : C ≤ Subgroup.centralizer (H : Set (GLV V)))
    (κ : GaloisField 2 2 →ₐ[ZMod 2] Module.End (ZMod 2) ↥I)
    (hκsurj : ∀ f ∈ endOn H I, ∃ k, κ k = f) :
    ∃ (J : Submodule (ZMod 2) V) (φ : ↥I ≃ₗ[ZMod 2] ↥J), IsCompl I J ∧
      (∀ k ∈ H, ∀ i j : ↥I, k (i : V) = (j : V) → k ((φ i : ↥J) : V) = ((φ j : ↥J) : V)) ∧
      Module.finrank (ZMod 2) ↥I = 4 := by
  classical
  obtain ⟨J, hJinv, hIJ⟩ := exists_invariant_compl hsum hI.1
  have hn : Module.finrank (ZMod 2) ↥I + Module.finrank (ZMod 2) ↥J = 8 := by
    rw [Submodule.finrank_add_eq_of_isCompl hIJ, hd]
  have hI0 : I ≠ ⊥ := (hI.isIrr hfix).ne_bot
  have hpos : 0 < Module.finrank (ZMod 2) ↥I :=
    Nat.pos_of_ne_zero fun h => hI0 (Submodule.finrank_eq_zero.1 h)
  by_cases hJ0 : J = ⊥
  · exfalso
    have htop : I = ⊤ := by
      have := hIJ.codisjoint.eq_top
      rwa [hJ0, sup_bot_eq] at this
    have hcomm : ∀ a b : ↥C, a * b = b * a := by
      intro a b
      obtain ⟨f, hf, hfa⟩ := exists_endOn_of_centralizer hI.1 htop (hcent a.2)
      obtain ⟨g, hg, hgb⟩ := exists_endOn_of_centralizer hI.1 htop (hcent b.2)
      obtain ⟨k, rfl⟩ := hκsurj f hf
      obtain ⟨l, rfl⟩ := hκsurj g hg
      have hkl : κ k * κ l = κ l * κ k := by
        rw [← map_mul, ← map_mul, mul_comm]
      refine Subtype.ext (LinearEquiv.ext fun v => ?_)
      have hv : v ∈ I := by rw [htop]; trivial
      have h1 := congrArg (fun T : Module.End (ZMod 2) ↥I => ((T ⟨v, hv⟩ : ↥I) : V)) hkl
      simp only [Module.End.mul_apply] at h1
      have e1 : ((κ k (κ l ⟨v, hv⟩) : ↥I) : V) = (a : GLV V) ((b : GLV V) v) := by
        rw [hfa, hgb]
      have e2 : ((κ l (κ k ⟨v, hv⟩) : ↥I) : V) = (b : GLV V) ((a : GLV V) v) := by
        rw [hgb, hfa]
      exact (e1.symm.trans h1).trans e2
    have hbot : commutator ↥C = ⊥ := by
      rw [commutator_def, eq_bot_iff, Subgroup.commutator_le]
      intro a _ b _
      exact Subgroup.mem_bot.2 (commutatorElement_eq_one_iff_mul_comm.2 (hcomm a b))
    have h1 : Nat.card ↥C = 1 := by
      rw [← Subgroup.card_top (G := ↥C), ← hCperf, hbot, Subgroup.card_bot]
    omega
  · obtain ⟨J₀, hJ₀J, hJ₀irr⟩ := exists_isIrr_le hJinv hJ0
    have hJ₀plus : IrrPlus H J₀ := hJ₀irr.irrPlus hfix
    obtain ⟨φ₀, hφ₀⟩ := hhom I J₀ hI hJ₀plus
    have h1 : Module.finrank (ZMod 2) ↥I = Module.finrank (ZMod 2) ↥J₀ :=
      LinearEquiv.finrank_eq φ₀
    have h2 : Module.finrank (ZMod 2) ↥J₀ ≤ Module.finrank (ZMod 2) ↥J :=
      Submodule.finrank_mono hJ₀J
    have heven : Even (Module.finrank (ZMod 2) ↥I) :=
      even_finrank_of_algHom (by rw [GaloisField.card 2 2 (by norm_num)]; norm_num) κ
    have hn2 : ¬ Module.finrank (ZMod 2) ↥I ≤ 2 := by
      intro hle
      have hsolv : Group.IsSolvable (↥I ≃ₗ[ZMod 2] ↥I) :=
        isSolvable_linearEquiv_of_finrank_le_two I hle
      have hsolvH : Group.IsSolvable ↥H :=
        Group.isSolvable_of_isSolvable_injective (restrictHom_injective hI.1 hfaith)
      have hfin : Finite ↥H := Nat.finite_of_card_ne_zero (by omega)
      have hnt : Nontrivial ↥H := Finite.one_lt_card_iff_nontrivial.1 (by omega)
      have hperfH : Group.IsPerfect ↥H := Group.isPerfect_def.2 hHperf
      exact Group.IsPerfect.not_isSolvable ↥H hsolvH
    obtain ⟨m, hm⟩ := heven
    have hn4 : Module.finrank (ZMod 2) ↥I = 4 := by omega
    obtain rfl : J₀ = J :=
      Submodule.eq_of_le_of_finrank_eq hJ₀J (by omega)
    exact ⟨J₀, φ₀, hIJ, hφ₀, hn4⟩

end Decomposition

end Tensor

end SzG11S

end G11

end CFSG.Quasithin
