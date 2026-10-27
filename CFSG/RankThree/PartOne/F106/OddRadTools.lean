module

public import CFSG.RankThree.PartOne.F106.OddRadAt
public import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.GroupTheory.ABGLocalTools.Constraint

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG
open scoped commutatorElement

theorem eqLocus_conj_eq_centralizer {T : Type*} [Group T] (t : T) :
    ((MulAut.conj t : MulAut T) : T →* T).eqLocus (MonoidHom.id T) = Subgroup.centralizer {t} := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff]
  show (MulAut.conj t) x = x ↔ _
  rw [MulAut.conj_apply]
  constructor
  · intro h
    exact ((mul_inv_eq_iff_eq_mul.1 h).symm)
  · intro h
    rw [← h, mul_inv_cancel_right]

theorem card_radical_residual_of_embedding {T M : Type*} [Group T] [Group M] (ι : T →* M)
    (hι : Function.Injective ι) (t : T) :
    Nat.card ↥(solvableRadical ↥(perfectResidual ↥(Subgroup.centralizer {t}))) =
      Nat.card ↥(solvableRadical ↥(perfectResidual ↥(ι.range ⊓ Subgroup.centralizer {ι t}))) := by
  have hmap : (Subgroup.centralizer {t}).map ι = ι.range ⊓ Subgroup.centralizer {ι t} := by
    ext y
    rw [Subgroup.mem_map, Subgroup.mem_inf, MonoidHom.mem_range]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
      rw [← map_mul, ← map_mul, hx]
    · rintro ⟨⟨x, rfl⟩, hy⟩
      refine ⟨x, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      exact hι (by rw [map_mul, map_mul, hy])
  exact card_solvableRadical_perfectResidual_eq
    (((Subgroup.centralizer {t}).equivMapOfInjective ι hι).trans (MulEquiv.subgroupCongr hmap))

theorem card_radical_residual_conj {M : Type*} [Group M] (Y : Subgroup M) {γ : M} (hγ : γ ∈ Y)
    (x : M) :
    Nat.card ↥(solvableRadical ↥(perfectResidual ↥(Y ⊓ Subgroup.centralizer {γ * x * γ⁻¹}))) =
      Nat.card ↥(solvableRadical ↥(perfectResidual ↥(Y ⊓ Subgroup.centralizer {x}))) := by
  have hmap : (Y ⊓ Subgroup.centralizer {x}).map (MulAut.conj γ).toMonoidHom =
      Y ⊓ Subgroup.centralizer {γ * x * γ⁻¹} := by
    ext y
    rw [Subgroup.mem_map, Subgroup.mem_inf]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨hzY, hz'⟩ := Subgroup.mem_inf.1 hz
      refine ⟨?_, ?_⟩
      · exact Y.mul_mem (Y.mul_mem hγ hzY) (Y.inv_mem hγ)
      · rw [Subgroup.mem_centralizer_singleton_iff] at hz' ⊢
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        calc γ * z * γ⁻¹ * (γ * x * γ⁻¹) = γ * (z * x) * γ⁻¹ := by group
          _ = γ * (x * z) * γ⁻¹ := by rw [hz']
          _ = γ * x * γ⁻¹ * (γ * z * γ⁻¹) := by group
    · rintro ⟨hyY, hy⟩
      refine ⟨γ⁻¹ * y * γ, Subgroup.mem_inf.2 ⟨Y.mul_mem (Y.mul_mem (Y.inv_mem hγ) hyY) hγ, ?_⟩,
        ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
        have h1 : y * (γ * x * γ⁻¹) = γ * x * γ⁻¹ * y := hy
        calc γ⁻¹ * y * γ * x = γ⁻¹ * (y * (γ * x * γ⁻¹)) * γ := by group
          _ = γ⁻¹ * (γ * x * γ⁻¹ * y) * γ := by rw [h1]
          _ = x * (γ⁻¹ * y * γ) := by group
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
  exact (card_solvableRadical_perfectResidual_eq
    (((Y ⊓ Subgroup.centralizer {x}).equivMapOfInjective (MulAut.conj γ).toMonoidHom
      (MulAut.conj γ).injective).trans (MulEquiv.subgroupCongr hmap))).symm

theorem card_radical_residual_of_comm {D : Type*} [Group D] (hD : ∀ x y : D, x * y = y * x) :
    Nat.card ↥(solvableRadical ↥(perfectResidual D)) = 1 := by
  have hbot : perfectResidual D = ⊥ := by
    have h1 : ⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆ = ⊥ :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := (⊤ : Subgroup D))
        (H₂ := (⊤ : Subgroup D))).2 fun x _ => Subgroup.mem_centralizer_iff.2 fun h _ => hD h x
    refine le_bot_iff.1 ((iInf_le _ 1).trans ?_)
    rw [derivedSeries_one, commutator_def, h1]
  have : Subsingleton ↥(perfectResidual D) := by
    rw [hbot]
    infer_instance
  rw [Subgroup.eq_bot_of_subsingleton (solvableRadical ↥(perfectResidual D)), Subgroup.card_bot]

theorem card_radical_residual_of_simple_commutator {Y : Type*} [Group Y] [Finite Y]
    (hs : IsSimpleGroup ↥(commutator Y)) (hp : Group.IsPerfect ↥(commutator Y)) :
    Nat.card ↥(solvableRadical ↥(perfectResidual Y)) = 1 := by
  have hcc : ⁅commutator Y, commutator Y⁆ = commutator Y := Subgroup.isPerfect_iff.1 hp
  have hres : perfectResidual Y = commutator Y := by
    refine le_antisymm ((iInf_le _ 1).trans (by rw [derivedSeries_one])) (le_iInf fun n => ?_)
    induction n with
    | zero => exact le_top
    | succ n ih =>
      rw [derivedSeries_succ]
      exact hcc ▸ Subgroup.commutator_mono ih ih
  let e : ↥(perfectResidual Y) ≃* ↥(commutator Y) := MulEquiv.subgroupCongr hres
  have : IsSimpleGroup ↥(perfectResidual Y) := e.isSimpleGroup
  have hnsol : ¬ Group.IsSolvable ↥(perfectResidual Y) := fun hsol =>
    CFSG.LieType.SteinbergBR.not_isSolvable_of_isPerfect (G := ↥(commutator Y))
      (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  have hnorm : (solvableRadical ↥(perfectResidual Y)).Normal := inferInstance
  have hsol : Group.IsSolvable ↥(solvableRadical ↥(perfectResidual Y)) :=
    CFSG.ABGLocalTools.solvableRadical_isSolvable
  rcases hnorm.eq_bot_or_eq_top with h | h
  · rw [h, Subgroup.card_bot]
  · exfalso
    rw [h] at hsol
    exact hnsol (Group.isSolvable_of_surjective
      (f := (Subgroup.topEquiv : (⊤ : Subgroup ↥(perfectResidual Y)) ≃* _).toMonoidHom)
      (MulEquiv.surjective _))

theorem card_radical_residual_of_commutator_eq {M : Type*} [Group M] [Finite M]
    (D R : Subgroup M) (hDR : ⁅D, D⁆ = R) (hs : IsSimpleGroup ↥R) (hp : Group.IsPerfect ↥R) :
    Nat.card ↥(solvableRadical ↥(perfectResidual ↥D)) = 1 := by
  have hmap : (commutator ↥D).map D.subtype = R := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    exact hDR
  have e : ↥(commutator ↥D) ≃* ↥R :=
    ((commutator ↥D).equivMapOfInjective D.subtype D.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  have := hs
  refine card_radical_residual_of_simple_commutator e.isSimpleGroup ?_
  have hRR : ⁅R, R⁆ = R := Subgroup.isPerfect_iff.1 hp
  refine Subgroup.isPerfect_iff.2 (Subgroup.map_injective D.subtype_injective ?_)
  rw [Subgroup.map_commutator, hmap, hRR]

theorem odd_card_radical_residual_of_dichotomy {M : Type*} [Group M] [Finite M] (D : Subgroup M)
    (h : (∀ x ∈ D, ∀ y ∈ D, x * y = y * x) ∨
      ∃ R : Subgroup M, ⁅D, D⁆ = R ∧ IsSimpleGroup ↥R ∧ Group.IsPerfect ↥R) :
    Odd (Nat.card ↥(solvableRadical ↥(perfectResidual ↥D))) := by
  rcases h with h | ⟨R, hDR, hs, hp⟩
  · rw [card_radical_residual_of_comm (D := ↥D) fun x y => Subtype.ext (h x x.2 y y.2)]
    exact odd_one
  · rw [card_radical_residual_of_commutator_eq D R hDR hs hp]
    exact odd_one

theorem factorization_eq_of_sylow_le {M : Type*} [Group M] [Finite M] {p : ℕ} [hp : Fact p.Prime]
    {Y H : Subgroup M} (hHY : H ≤ Y) (S : Sylow p ↥Y) (hS : (S : Subgroup ↥Y) ≤ H.subgroupOf Y) :
    (Nat.card ↥Y).factorization p = (Nat.card ↥H).factorization p := by
  have h1 : Nat.card ↥S = p ^ (Nat.card ↥Y).factorization p := Sylow.card_eq_multiplicity S
  have h2 : Nat.card ↥S ∣ Nat.card ↥(H.subgroupOf Y) := Subgroup.card_dvd_of_le hS
  have h3 : Nat.card ↥(H.subgroupOf Y) = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHY).toEquiv
  have h4 : Nat.card ↥H ∣ Nat.card ↥Y := Subgroup.card_dvd_of_le hHY
  refine le_antisymm ?_ ((Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 h4 p)
  exact (hp.out.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 (h1 ▸ h3 ▸ h2)

theorem isPerfect_of_simple_nonabelian {G : Type*} [Group G] [IsSimpleGroup G]
    (h : ∃ a b : G, a * b ≠ b * a) : Group.IsPerfect G := by
  refine ⟨?_⟩
  rcases (inferInstance : (commutator G).Normal).eq_bot_or_eq_top with hb | ht
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    apply hab
    have hmem : ⁅a, b⁆ ∈ commutator G :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [hb, Subgroup.mem_bot, commutatorElement_def] at hmem
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [hmem, one_mul]
  · exact ht

theorem card_radical_residual_of_simple_perfect {Y : Type*} [Group Y] [Finite Y]
    [IsSimpleGroup Y] (hp : Group.IsPerfect Y) :
    Nat.card ↥(solvableRadical ↥(perfectResidual Y)) = 1 := by
  have hc : commutator Y = ⊤ := hp.commutator_eq_top
  let e : ↥(commutator Y) ≃* Y := (MulEquiv.subgroupCongr hc).trans Subgroup.topEquiv
  refine card_radical_residual_of_simple_commutator e.isSimpleGroup ?_
  refine Subgroup.isPerfect_iff.2 ?_
  rw [hc, ← commutator_def]
  exact hc

theorem card_radical_residual_of_simple_nonabelian {Y : Type*} [Group Y] [Finite Y]
    [IsSimpleGroup Y] (h : ∃ a b : Y, a * b ≠ b * a) :
    Nat.card ↥(solvableRadical ↥(perfectResidual Y)) = 1 :=
  card_radical_residual_of_simple_perfect (isPerfect_of_simple_nonabelian h)

theorem exists_noncomm_of_perfect {T : Type*} [Group T] [Nontrivial T] (hp : Group.IsPerfect T) :
    ∃ a b : T, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨g, hg⟩ := exists_ne (1 : T)
  have hc : commutator T = ⊤ := hp.commutator_eq_top
  have hb : commutator T ≤ ⊥ := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_bot, commutatorElement_def, hcon a b]
    group
  have hg' : g ∈ commutator T := by
    rw [hc]
    exact Subgroup.mem_top g
  exact hg (Subgroup.mem_bot.1 (hb hg'))

theorem center_eq_bot_of_simple_nonabelian {T : Type*} [Group T] [IsSimpleGroup T]
    (h : ∃ a b : T, a * b ≠ b * a) : Subgroup.center T = ⊥ := by
  rcases (inferInstance : (Subgroup.center T).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    have ha : a ∈ Subgroup.center T := by
      rw [ht]
      exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.1 ha b).symm

theorem orderOf_conj_eq {T : Type*} [Group T] (hc : Subgroup.center T = ⊥) (t : T) :
    orderOf (MulAut.conj t) = orderOf t := by
  have hinj : Function.Injective (MulAut.conj : T →* MulAut T) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro t ht
    have h1 : ∀ g : T, g * t = t * g := fun g => by
      have h2 : (MulAut.conj t) g = g := by rw [MonoidHom.mem_ker.1 ht]; rfl
      rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    have h3 : t ∈ Subgroup.center T := Subgroup.mem_center_iff.2 h1
    rw [hc] at h3
    exact h3
  exact orderOf_injective _ hinj t

end CFSG.RankThree.PartOne.F106
