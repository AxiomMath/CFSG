module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S22c
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22t
public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge4
public import CFSG.Quasithin.Background.A1bKrullSchmidt
public import CFSG.LocalAnalysis.GLTheoremB.Prop95L97Sigma3Dec
public import CFSG.Adapters.ProjectiveSpecialLinear
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
import all CFSG.Quasithin.Background.A1bKrullSchmidt
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.LocalAnalysis.UniquenessCase.UC22P22d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext (IsInternalDirect)
open CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Sigma3 (Sigma3Dec.isIndecomposableGroup_of_mulEquiv
  Sigma3Dec.center_eq_bot_of_mulEquiv Sigma3Dec.isIndexedDirectProduct_range_mulSingle)

namespace P22y

section Remak

variable {X : Type} [Group X] {m : ℕ} {H : Subgroup X} {Nb : Fin m → Subgroup X}

theorem pairwise_commute (hd : IsInternalDirect H Nb) :
    Pairwise fun i j => ∀ x y : X, x ∈ Nb i → y ∈ Nb j → Commute x y :=
  fun i j hij x y hx hy => hd.2.1 i j hij x hx y hy

theorem iSupIndep_of (hd : IsInternalDirect H Nb) : iSupIndep Nb := fun i =>
  disjoint_iff.2 (hd.2.2 i)

@[expose] def piMul (hd : IsInternalDirect H Nb) : (∀ i, ↥(Nb i)) →* X :=
  Subgroup.noncommPiCoprod (pairwise_commute hd)

theorem piMul_mulSingle (hd : IsInternalDirect H Nb) (i : Fin m) (a : ↥(Nb i)) :
    piMul hd (Pi.mulSingle i a) = (a : X) :=
  Subgroup.noncommPiCoprod_mulSingle i a

theorem piMul_injective (hd : IsInternalDirect H Nb) : Function.Injective (piMul hd) :=
  Subgroup.injective_noncommPiCoprod_of_iSupIndep (iSupIndep_of hd)

theorem piMul_range (hd : IsInternalDirect H Nb) : (piMul hd).range = H := by
  rw [piMul, Subgroup.noncommPiCoprod_range]
  exact hd.1

theorem exists_aut_conj [Finite X] (hd : IsInternalDirect H Nb) {g : X}
    (hg : g ∈ normalizer (H : Set X)) :
    ∃ α : MulAut (∀ i, ↥(Nb i)), ∀ x, piMul hd (α x) = g * piMul hd x * g⁻¹ := by
  have hmem : ∀ x : ∀ i, ↥(Nb i), ∃ y : ∀ i, ↥(Nb i), piMul hd y = g * piMul hd x * g⁻¹ := by
    intro x
    have hr := Subgroup.ext_iff.1 (piMul_range hd)
    have h1 : piMul hd x ∈ H := (hr _).1 ⟨x, rfl⟩
    exact (hr _).2 ((Subgroup.mem_normalizer_iff.1 hg _).1 h1)
  choose f hf using hmem
  have hinj := piMul_injective hd
  have hmul : ∀ x y, f (x * y) = f x * f y := by
    intro x y
    apply hinj
    simp only [hf, map_mul]
    group
  have hfinj : Function.Injective f := by
    intro x y hxy
    apply hinj
    have := congrArg (piMul hd) hxy
    rw [hf, hf] at this
    simpa using this
  let F : (∀ i, ↥(Nb i)) →* (∀ i, ↥(Nb i)) := MonoidHom.mk' f hmul
  exact ⟨MulEquiv.ofBijective F (Finite.injective_iff_bijective.1 hfinj), hf⟩

theorem exists_perm [Finite X] (hd : IsInternalDirect H Nb)
    (hind : ∀ i, CFSG.Quasithin.IsIndecomposableGroup ↥(Nb i))
    (hZ : ∀ i, Subgroup.center ↥(Nb i) = ⊥) {g : X} (hg : g ∈ normalizer (H : Set X)) :
    ∃ τ : Equiv.Perm (Fin m), ∀ i, (Nb i).map (MulAut.conj g).toMonoidHom = Nb (τ i) := by
  classical
  obtain ⟨α, hα⟩ := exists_aut_conj hd hg
  have hind' : ∀ i, CFSG.Quasithin.IsIndecomposableGroup
      ↥((MonoidHom.mulSingle (fun j : Fin m => ↥(Nb j)) i).range) := fun i =>
    Sigma3Dec.isIndecomposableGroup_of_mulEquiv
      (MonoidHom.ofInjective (f := MonoidHom.mulSingle (fun j : Fin m => ↥(Nb j)) i)
        (Pi.mulSingle_injective (M := fun j : Fin m => ↥(Nb j)) i)).symm (hind i)
  obtain ⟨τ, hτ⟩ := CFSG.Quasithin.krull_schmidt_aut_permutes
    (Sigma3Dec.isIndexedDirectProduct_range_mulSingle (F := fun j : Fin m => ↥(Nb j))) hind' α
  have hcenter : Subgroup.center (∀ i, ↥(Nb i)) = ⊥ := by
    rw [Subgroup.center_pi, Subgroup.pi_eq_bot_iff]
    exact hZ
  have hmap : ∀ i, ((MonoidHom.mulSingle (fun j : Fin m => ↥(Nb j)) i).range).map α.toMonoidHom =
      (MonoidHom.mulSingle (fun j : Fin m => ↥(Nb j)) (τ i)).range := by
    intro i
    have := hτ i
    rwa [hcenter, sup_bot_eq, sup_bot_eq] at this
  refine ⟨τ, fun i => ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h1 : α (Pi.mulSingle i (⟨y, hy⟩ : ↥(Nb i))) ∈
        (MonoidHom.mulSingle (fun j : Fin m => ↥(Nb j)) (τ i)).range := by
      rw [← hmap i]
      exact ⟨_, ⟨⟨y, hy⟩, rfl⟩, rfl⟩
    obtain ⟨b, hb⟩ := h1
    have h2 := hα (Pi.mulSingle i (⟨y, hy⟩ : ↥(Nb i)))
    have hb' : Pi.mulSingle (τ i) b = α (Pi.mulSingle i (⟨y, hy⟩ : ↥(Nb i))) := hb
    rw [← hb', piMul_mulSingle, piMul_mulSingle] at h2
    change (MulAut.conj g) y ∈ Nb (τ i)
    rw [MulAut.conj_apply, ← h2]
    exact b.2
  · intro hx
    have h1 : (Pi.mulSingle (τ i) (⟨x, hx⟩ : ↥(Nb (τ i))) : ∀ j, ↥(Nb j)) ∈
        ((MonoidHom.mulSingle (fun j : Fin m => ↥(Nb j)) i).range).map α.toMonoidHom := by
      rw [hmap i]
      exact ⟨⟨x, hx⟩, rfl⟩
    obtain ⟨y, ⟨a, rfl⟩, hay⟩ := h1
    have hay' : α (Pi.mulSingle i a) = Pi.mulSingle (τ i) (⟨x, hx⟩ : ↥(Nb (τ i))) := hay
    have h2 := hα (Pi.mulSingle i a)
    rw [hay', piMul_mulSingle, piMul_mulSingle] at h2
    refine ⟨(a : X), a.2, ?_⟩
    change (MulAut.conj g) (a : X) = x
    rw [MulAut.conj_apply]
    exact h2.symm

end Remak

section L2

theorem one_le_of_card {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) : 1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · have h1 : 1 < Nat.card F := Finite.one_lt_card
    rw [hF, h, pow_zero] at h1
    omega
  · exact h

theorem charP_two_of_card {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    CharP F 2 :=
  uc22p22d_charP_two (one_le_of_card hF) hF

theorem center_sl2_eq_bot {F : Type} [Field F] [CharP F 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hsq : (r - 1) ^ 2 = 0 := by linear_combination hr + (1 - r) * h2
  have hr1 : r = 1 := sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 hsq)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1, map_one]
  rfl

theorem center_eq_bot_of_isL2Ev {X : Type} [Group X] {n : ℕ} (h : IsL2Ev X n) : Subgroup.center X = ⊥ := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  haveI := charP_two_of_card hF
  refine Sigma3Dec.center_eq_bot_of_mulEquiv
    (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm) fun y hy => ?_
  have hyc : y ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Subgroup.mem_center_iff.2 fun z => (hy z).symm
  rw [center_sl2_eq_bot, Subgroup.mem_bot] at hyc
  exact hyc

theorem isSimpleGroup_sl2 {F : Type} [Field F] [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) := by
  haveI := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have e : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientMulEquivOfEq center_sl2_eq_bot).trans QuotientGroup.quotientBot
  haveI : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) F) := e.symm.toEquiv.nontrivial
  exact IsSimpleGroup.isSimpleGroup_of_surjective e.toMonoidHom e.surjective

theorem card_of_isL2Ev_one {X : Type} [Group X] (h : IsL2Ev X 1) : Nat.card X = 6 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two, hF]
  norm_num

theorem isIndecomposable_of_card_six {X : Type} [Group X] [Finite X] (h6 : Nat.card X = 6)
    (hZ : Subgroup.center X = ⊥) : CFSG.Quasithin.IsIndecomposableGroup X := by
  haveI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  refine ⟨inferInstance, fun B C hB hC hBC hsup => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hB1, hC1⟩ := hcon
  have hcomm : ∀ x ∈ B, ∀ y ∈ C, x * y = y * x := fun x hx y hy =>
    Subgroup.commute_of_normal_of_disjoint B C hB hC (disjoint_iff.2 hBC) x y hx hy
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute B C hcomm).1
  rw [hsup, hBC, Subgroup.card_bot, mul_one, Subgroup.card_top, h6] at hcard
  have hB2 : 1 < Nat.card B := by
    have := (Subgroup.one_lt_card_iff_ne_bot B).2 hB1
    exact this
  have hC2 : 1 < Nat.card C := (Subgroup.one_lt_card_iff_ne_bot C).2 hC1
  have hprime : ∀ a b : ℕ, a * b = 6 → 1 < a → 1 < b → a.Prime := by
    intro a b hab ha hb
    have hale : a ≤ 6 := Nat.le_of_dvd (by norm_num) ⟨b, hab.symm⟩
    have h23 : a = 2 ∨ a = 3 := by
      interval_cases a <;> omega
    rcases h23 with rfl | rfl <;> norm_num
  have hBp : (Nat.card B).Prime := hprime _ _ hcard.symm hB2 hC2
  have hab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    haveI : Fact (Nat.card B).Prime := ⟨hBp⟩
    haveI := isCyclic_of_prime_card (α := ↥B) rfl
    letI : CommGroup ↥B := IsCyclic.commGroup
    have := mul_comm (⟨x, hx⟩ : ↥B) ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hBc : B ⊔ C ≤ Subgroup.centralizer (B : Set X) := sup_le
    (fun y hy => Subgroup.mem_centralizer_iff.2 fun x hx => hab x hx y hy)
    (fun y hy => Subgroup.mem_centralizer_iff.2 fun x hx => hcomm x hx y hy)
  have hBZ : B ≤ Subgroup.center X := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro z
    have hz : z ∈ Subgroup.centralizer (B : Set X) := hBc (by rw [hsup]; trivial)
    exact (Subgroup.mem_centralizer_iff.1 hz x hx).symm
  rw [hZ, le_bot_iff] at hBZ
  exact hB1 hBZ

theorem isIndecomposable_of_isSimpleGroup {X : Type} [Group X] [IsSimpleGroup X] :
    CFSG.Quasithin.IsIndecomposableGroup X := by
  refine ⟨inferInstance, fun B C hB _ hBC _ => ?_⟩
  rcases hB.eq_bot_or_eq_top with h | h
  · exact Or.inl h
  · rw [h, top_inf_eq] at hBC
    exact Or.inr hBC

theorem isIndecomposable_of_isL2Ev {X : Type} [Group X] [Finite X] {n : ℕ} (h : IsL2Ev X n) :
    CFSG.Quasithin.IsIndecomposableGroup X := by
  have hZ := center_eq_bot_of_isL2Ev h
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  have hn := one_le_of_card hF
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · have hn1 : n = 1 := by omega
    subst hn1
    exact isIndecomposable_of_card_six (card_of_isL2Ev_one ⟨F, inferInstance, inferInstance, hF, ⟨e⟩⟩) hZ
  · haveI := charP_two_of_card hF
    have h4 : 4 ≤ Nat.card F := by
      rw [hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    haveI := isSimpleGroup_sl2 h4
    let e' : X ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
      e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm
    haveI : Nontrivial X := e'.toEquiv.nontrivial
    haveI : IsSimpleGroup X :=
      IsSimpleGroup.isSimpleGroup_of_surjective e'.symm.toMonoidHom e'.symm.surjective
    exact isIndecomposable_of_isSimpleGroup

end L2

end P22y

open P22y

variable {G : Type} [Group G] [Finite G]

theorem uc22p22ya_nbar_normal (D : Data G) : (mbarImage D.M D.U (proofN D)).Normal :=
  uc22br4_mbarImage_normal D.M D.U (proofN D) (uc22p22e_jOf_le_self D.M) (uc22p22t_M_le_normalizer_jOf D)

theorem uc22p22ya_exists_perm (D : Data G) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (hNb : NbarSplit D Nb) (h51 : Cl22_5_1 D Nb) (g : MBar D.M D.U) :
    ∃ τ : Equiv.Perm (Fin m), ∀ i, (Nb i).map (MulAut.conj g).toMonoidHom = Nb (τ i) := by
  have hn := uc22p22ya_nbar_normal D
  refine exists_perm hNb.1 (fun i => ?_) (fun i => ?_) ?_
  · obtain ⟨n, hn', _⟩ := h51 i
    exact isIndecomposable_of_isL2Ev hn'
  · obtain ⟨n, hn', _⟩ := h51 i
    exact center_eq_bot_of_isL2Ev hn'
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hn.conj_mem h hh g, fun hh => ?_⟩
    have := hn.conj_mem _ hh g⁻¹
    simpa [mul_assoc] using this

end CFSG.LocalAnalysis.UniquenessCase.UC22
