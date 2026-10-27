module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.FusionRep
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.FusionGL
import CFSG.OddTranspositions.PartThree.Eleven.Wong.OddCore

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Subgroup

namespace SwapData

variable {G : Type} [Group G] (D : SwapData G)

private theorem map_conj_centralizer_singleton_aux {X : Type*} [Group X] (g t : X) :
    (Subgroup.centralizer ({t} : Set X)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * t * g⁻¹} : Set X) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    change (g * y * g⁻¹) ∈ Subgroup.centralizer ({g * t * g⁻¹} : Set X)
    have hy' : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc g * y * g⁻¹ * (g * t * g⁻¹) = g * (y * t) * g⁻¹ := by group
        _ = g * (t * y) * g⁻¹ := by rw [hy']
        _ = (g * t * g⁻¹) * (g * y * g⁻¹) := by group)
  · intro x hx
    have hx' : x * (g * t * g⁻¹) = (g * t * g⁻¹) * x :=
      Subgroup.mem_centralizer_singleton_iff.mp hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · change (g⁻¹ * x * g) ∈ Subgroup.centralizer ({t} : Set X)
      exact Subgroup.mem_centralizer_singleton_iff.mpr (by
        calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [hx']
          _ = t * (g⁻¹ * x * g) := by group)
    · change g * (g⁻¹ * x * g) * g⁻¹ = x
      group

private theorem two_pow_factorization_14400 : 2 ^ (14400 : ℕ).factorization 2 = 64 := by
  rw [Nat.factorization_def 14400 Nat.prime_two]
  have h1 : (14400 : ℕ) = 2 ^ 6 * 225 := by norm_num
  rw [h1, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ (2 : ℕ) ∣ 225)]
  norm_num

private theorem w13d_h1_sq : D.h1 ^ 2 = D.t := by
  rw [show D.h1 = D.i1 hM from rfl, ← map_pow, hM_sq, ← D.t_eq_i1]

private theorem w13d_E_le [Finite G] :
    D.E ≤ centralizer {D.t} ⊓ centralizer {D.v} := by
  refine (closure_le _).mpr ?_
  rintro g (rfl | rfl | rfl | rfl)
  · exact mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr rfl, D.t_mem_centralizer_v⟩
  · exact mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr D.t_commute_u.eq.symm,
      D.u_mem_centralizer_v⟩
  · exact mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr D.commute_t_v.eq.symm,
      mem_centralizer_singleton_iff.mpr rfl⟩
  · exact mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr D.commute_t_w.eq.symm,
      mem_centralizer_singleton_iff.mpr D.commute_v_w.eq.symm⟩

private theorem w13d_h1_mem [Finite G] :
    D.h1 ∈ centralizer {D.t} ⊓ centralizer {D.v} := by
  have h : D.h1 ∈ closure {D.r, D.h1, D.h2, D.w} := subset_closure (by simp)
  rwa [← D.centralizer_t_inf_centralizer_v] at h

private theorem w13d_h1_not_mem_E : D.h1 ∉ D.E := by
  intro h
  have h2 : D.h1 ^ 2 = 1 := D.sq_eq_one_of_mem_E h
  rw [w13d_h1_sq D] at h2
  have ht := D.orderOf_t
  rw [h2, orderOf_one] at ht
  exact absurd ht (by norm_num)

private theorem w13d_relIndex_E [Finite G] :
    D.E.relIndex (centralizer {D.t} ⊓ centralizer {D.v}) = 2 := by
  have hET := w13d_E_le D
  have h := Subgroup.relIndex_mul_card D.E (centralizer {D.t} ⊓ centralizer {D.v})
  rw [inf_eq_left.mpr hET, D.card_E, D.card_centralizer_t_inf_centralizer_v] at h
  omega

private theorem w13d_relIndex_T_V [Finite G] {V : Subgroup G}
    (hTV : centralizer {D.t} ⊓ centralizer {D.v} ≤ V) (hV : Nat.card V = 64) :
    (centralizer {D.t} ⊓ centralizer {D.v}).relIndex V = 2 := by
  have h := Subgroup.relIndex_mul_card (centralizer {D.t} ⊓ centralizer {D.v}) V
  rw [inf_eq_left.mpr hTV, D.card_centralizer_t_inf_centralizer_v, hV] at h
  omega

private theorem w13d_commute_gens {a b : G} (ha : a ∈ ({D.t, D.u, D.v, D.w} : Set G))
    (hb : b ∈ ({D.t, D.u, D.v, D.w} : Set G)) : Commute a b := by
  have h : Commute D.t b ∧ Commute D.u b ∧ Commute D.v b ∧ Commute D.w b := by
    rcases hb with rfl | rfl | rfl | rfl
    · exact ⟨Commute.refl _, D.t_commute_u.symm, D.d_commute_t hM, D.d_commute_t cM⟩
    · exact ⟨D.t_commute_u, Commute.refl _, D.d_commute_u hM, D.d_commute_u cM⟩
    · exact ⟨(D.d_commute_t hM).symm, (D.d_commute_u hM).symm, Commute.refl _,
        D.commute_v_w.symm⟩
    · exact ⟨(D.d_commute_t cM).symm, (D.d_commute_u cM).symm, D.commute_v_w, Commute.refl _⟩
  obtain ⟨h1, h2, h3, h4⟩ := h
  rcases ha with rfl | rfl | rfl | rfl
  exacts [h1, h2, h3, h4]

private theorem w13d_commute_of_mem_E {x y : G} (hx : x ∈ D.E) (hy : y ∈ D.E) :
    Commute x y := by
  have hc : D.E ≤ centralizer (D.E : Set G) := by
    show closure {D.t, D.u, D.v, D.w} ≤ centralizer (closure {D.t, D.u, D.v, D.w} : Set G)
    rw [centralizer_closure]
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem a ha => exact mem_centralizer_iff.mpr fun b hb => (w13d_commute_gens D ha hb).eq.symm
    | one => exact one_mem _
    | mul a b _ _ ha hb => exact mul_mem ha hb
    | inv a _ ha => exact inv_mem ha
  exact mem_centralizer_iff.mp (hc hy) x hx

private theorem w13d_mem_closure_t_v_of_mem_E_of_commute [Finite G] {x : G}
    (hx : x ∈ D.E) (hc : Commute x D.h1) : x ∈ closure {D.t, D.v} := by
  obtain ⟨ρ, hρ⟩ := D.exists_isBasisRep
  obtain ⟨a, rfl⟩ := D.mem_E_iff.mp hx
  have hconj : D.h1⁻¹ * D.vecE a * D.h1 = D.vecE a := by
    calc D.h1⁻¹ * D.vecE a * D.h1 = D.h1⁻¹ * (D.vecE a * D.h1) := by group
      _ = D.h1⁻¹ * (D.h1 * D.vecE a) := by rw [hc.eq]
      _ = D.vecE a := by group
  have hrep := IsBasisRep.conj_vecE hρ ⟨D.h1, D.h1_mem_normalizer_E⟩ a
  rw [IsBasisRep.apply_h1 hρ] at hrep
  simp only [val_fusionUnitA] at hrep
  have heq : D.vecE (Matrix.vecMul a fusionA) = D.vecE a := by rw [← hrep, hconj]
  have hmat : Matrix.vecMul a fusionA = a := D.vecE_injective heq
  have key : ∀ a : Fin 4 → ZMod 2, Matrix.vecMul a fusionA = a → a 1 = 0 ∧ a 3 = 0 := by
    decide
  obtain ⟨ha1, ha3⟩ := key a hmat
  have hvec : D.vecE a = D.t ^ (a 0).val * D.v ^ (a 2).val := by
    simp [SwapData.vecE, ha1, ha3]
  rw [hvec]
  have ht : D.t ∈ closure ({D.t, D.v} : Set G) := subset_closure (by simp)
  have hv : D.v ∈ closure ({D.t, D.v} : Set G) := subset_closure (by simp)
  exact mul_mem (Subgroup.pow_mem (closure ({D.t, D.v} : Set G)) ht _)
    (Subgroup.pow_mem (closure ({D.t, D.v} : Set G)) hv _)

private theorem w13d_relIndex_of_card_sixteen [Finite G] {A : Subgroup G}
    (hAT : A ≤ centralizer {D.t} ⊓ centralizer {D.v}) (hAcard : Nat.card A = 16) :
    A.relIndex (centralizer {D.t} ⊓ centralizer {D.v}) = 2 := by
  have h := Subgroup.relIndex_mul_card A (centralizer {D.t} ⊓ centralizer {D.v})
  rw [inf_eq_left.mpr hAT, hAcard, D.card_centralizer_t_inf_centralizer_v] at h
  omega

private theorem w13d_eq_E_of_abelian [Finite G] {A : Subgroup G}
    (hAT : A ≤ centralizer {D.t} ⊓ centralizer {D.v})
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hAcard : Nat.card A = 16) :
    A = D.E := by
  by_contra hne
  have hAE : ¬ A ≤ D.E := fun h =>
    hne (Subgroup.eq_of_le_of_card_ge h (by rw [hAcard, D.card_E]))
  obtain ⟨y, hyA, hyE⟩ := Set.not_subset.mp hAE
  let T : Subgroup G := centralizer {D.t} ⊓ centralizer {D.v}
  have hyT : y ∈ T := hAT hyA
  have h1T : D.h1 ∈ T := w13d_h1_mem D
  have hyinvT : y⁻¹ ∈ T := T.inv_mem hyT
  have hyinvE : y⁻¹ ∉ D.E := fun h => hyE (by simpa using D.E.inv_mem h)
  have hidx : (D.E.subgroupOf T).index = 2 := w13d_relIndex_E D
  have hmem : (⟨y⁻¹, hyinvT⟩ : ↥T) * ⟨D.h1, h1T⟩ ∈ D.E.subgroupOf T := by
    have ha : (⟨y⁻¹, hyinvT⟩ : ↥T) ∉ D.E.subgroupOf T :=
      fun h => hyinvE ((Subgroup.mem_subgroupOf (H := D.E) (K := T)).mp h)
    have hb : (⟨D.h1, h1T⟩ : ↥T) ∉ D.E.subgroupOf T :=
      fun h => w13d_h1_not_mem_E D ((Subgroup.mem_subgroupOf (H := D.E) (K := T)).mp h)
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
    exact ⟨fun h => absurd h ha, fun h => absurd h hb⟩
  have hzE : y⁻¹ * D.h1 ∈ D.E := (Subgroup.mem_subgroupOf (H := D.E) (K := T)).mp hmem
  have hcardle : Nat.card ↥(A ⊓ D.E) ≤ 4 := by
    have hle : A ⊓ D.E ≤ closure ({D.t, D.v} : Set G) := by
      intro x hx
      obtain ⟨hxA, hxE⟩ := Subgroup.mem_inf.mp hx
      have hxy : Commute x y := hAab x hxA y hyA
      have hxz : Commute x (y⁻¹ * D.h1) := w13d_commute_of_mem_E D hxE hzE
      have hxh1 : Commute x D.h1 := by
        have hyz : y * (y⁻¹ * D.h1) = D.h1 := by group
        rw [← hyz]
        exact hxy.mul_right hxz
      exact w13d_mem_closure_t_v_of_mem_E_of_commute D hxE hxh1
    have h := Subgroup.card_le_of_le hle
    have hcv : Nat.card (closure ({D.t, D.v} : Set G)) = 4 :=
      card_closure_pair D.orderOf_t D.orderOf_v D.commute_t_v (by
        intro h
        rw [D.v_eq_d] at h
        exact D.t_ne_d hM h.symm)
    rwa [hcv] at h
  have hcardge : 8 ≤ Nat.card ↥(A ⊓ D.E) := by
    have hidxA : (A.subgroupOf T).index = 2 := w13d_relIndex_of_card_sixteen D hAT hAcard
    have hidxE : (D.E.subgroupOf T).index = 2 := w13d_relIndex_E D
    have hinf : A.subgroupOf T ⊓ D.E.subgroupOf T = (A ⊓ D.E).subgroupOf T := by
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    have hidxle : (A.subgroupOf T ⊓ D.E.subgroupOf T).index ≤ 4 := by
      have h := Subgroup.index_inf_le (H := A.subgroupOf T) (K := D.E.subgroupOf T)
      rwa [hidxA, hidxE] at h
    rw [hinf] at hidxle
    have hcard := Subgroup.card_mul_index (A.subgroupOf T ⊓ D.E.subgroupOf T)
    rw [hinf] at hcard
    have hsub : Nat.card ((A ⊓ D.E).subgroupOf T) = Nat.card ↥(A ⊓ D.E) := by
      have h := Subgroup.card_subtype T ((A ⊓ D.E).subgroupOf T)
      rw [Subgroup.subgroupOf_map_subtype (A ⊓ D.E) T,
        inf_eq_left.mpr (le_trans (inf_le_left : A ⊓ D.E ≤ A) hAT)] at h
      exact h.symm
    rw [hsub] at hcard
    have hTcard : Nat.card ↥T = 32 := by
      simpa only [T] using D.card_centralizer_t_inf_centralizer_v
    rw [hTcard] at hcard
    have hidxpos : ((A ⊓ D.E).subgroupOf T).index ≠ 0 := by
      rw [← hinf]
      exact Subgroup.index_ne_zero_of_finite
    have h1 : 32 ≤ Nat.card ↥(A ⊓ D.E) * 4 := by
      rw [← hcard]
      exact Nat.mul_le_mul_left _ hidxle
    omega
  omega

private theorem w13d_mem_normalizer_of_mem [Finite G] {V : Subgroup G}
    (hTV : centralizer {D.t} ⊓ centralizer {D.v} ≤ V) (hV : Nat.card V = 64) {g : G}
    (hg : g ∈ V) : g ∈ normalizer (D.E : Set G) := by
  have hidxTV : (centralizer {D.t} ⊓ centralizer {D.v}).relIndex V = 2 :=
    w13d_relIndex_T_V D hTV hV
  have hE'T : D.E.map (MulAut.conj g).toMonoidHom ≤
      centralizer {D.t} ⊓ centralizer {D.v} := by
    rintro _ ⟨e, he, rfl⟩
    exact conj_mem_of_relIndex_eq_two hTV hidxTV hg ((w13d_E_le D) he)
  have hcard : Nat.card (D.E.map (MulAut.conj g).toMonoidHom) = 16 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, D.card_E]
  have hab : ∀ x ∈ D.E.map (MulAut.conj g).toMonoidHom,
      ∀ y ∈ D.E.map (MulAut.conj g).toMonoidHom, x * y = y * x := by
    rintro _ ⟨e1, he1, rfl⟩ _ ⟨e2, he2, rfl⟩
    have h := congrArg (MulAut.conj g) (w13d_commute_of_mem_E D he1 he2).eq
    simpa [map_mul] using h
  have hEeq := w13d_eq_E_of_abelian D hE'T hab hcard
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  simpa using hEeq

theorem le_normalizer_E_of_le [Finite G] {V : Subgroup G}
    (hTV : centralizer {D.t} ⊓ centralizer {D.v} ≤ V) (hV : Nat.card V = 64) :
    V ≤ normalizer (D.E : Set G) := by
  exact fun g hg => w13d_mem_normalizer_of_mem D hTV hV hg

theorem exists_card_eq_sixtyFour_of_isConj [Finite G] (h : IsConj D.t D.v) :
    ∃ V : Subgroup G, centralizer {D.t} ⊓ centralizer {D.v} ≤ V ∧ V ≤ centralizer {D.v} ∧
      Nat.card V = 64 := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have hcardCv : Nat.card (centralizer {D.v}) = 14400 := by
    have hmap : centralizer {D.v} = (centralizer {D.t}).map (MulAut.conj c) := by
      rw [← hc]
      exact (map_conj_centralizer_singleton_aux c D.t).symm
    rw [hmap, Subgroup.card_map_of_injective (MulAut.conj c).injective,
      D.hyp.card_centralizer]
  let T : Subgroup G := centralizer {D.t} ⊓ centralizer {D.v}
  have hTle : T ≤ centralizer {D.v} := inf_le_right
  have hcardT : Nat.card T = 32 := by
    simpa only [T] using D.card_centralizer_t_inf_centralizer_v
  have hP : IsPGroup 2 (T.subgroupOf (centralizer {D.v})) := by
    refine IsPGroup.of_card (n := 5) ?_
    have h := Subgroup.card_subtype (centralizer {D.v}) (T.subgroupOf (centralizer {D.v}))
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTle] at h
    rw [← h, hcardT]
    norm_num
  obtain ⟨Q, hTQ⟩ := hP.exists_le_sylow
  have hcardQ : Nat.card Q = 64 := by
    rw [Sylow.card_eq_multiplicity, hcardCv, two_pow_factorization_14400]
  refine ⟨(Q : Subgroup ↥(centralizer {D.v})).map (centralizer {D.v}).subtype, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : (⟨x, hTle hx⟩ : ↥(centralizer {D.v})) ∈ T.subgroupOf (centralizer {D.v}) :=
      Subgroup.mem_subgroupOf.mpr hx
    exact Subgroup.mem_map_of_mem (centralizer {D.v}).subtype (hTQ hx')
  · exact Subgroup.map_subtype_le _
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hcardQ]

theorem not_isConj_t_v [Finite G] : ¬ IsConj D.t D.v := by
  intro h
  obtain ⟨V, hTV, hVCv, hVcard⟩ := exists_card_eq_sixtyFour_of_isConj D h
  obtain ⟨ρ, hρ⟩ := D.exists_isBasisRep
  let N : Subgroup G := normalizer (D.E : Set G)
  have hVN : V ≤ N := le_normalizer_E_of_le D hTV hVcard
  have hSN : D.S ≤ N := D.S_le_normalizer_E
  have hEV : D.E ≤ V := (w13d_E_le D).trans hTV
  have hES : D.E ≤ D.S := D.E_le_S
  have hh1V : D.h1 ∈ V := hTV (w13d_h1_mem D)
  have hh1S : D.h1 ∈ D.S := subset_closure (by simp)
  let ψV : ↥V →* GL (Fin 4) (ZMod 2) := ρ.comp (Subgroup.inclusion hVN)
  let ψS : ↥D.S →* GL (Fin 4) (ZMod 2) := ρ.comp (Subgroup.inclusion hSN)
  have hψVrange : ψV.range = (V.subgroupOf N).map ρ := by
    change (ρ.comp (Subgroup.inclusion hVN)).range = (V.subgroupOf N).map ρ
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hψSrange : ψS.range = (D.S.subgroupOf N).map ρ := by
    change (ρ.comp (Subgroup.inclusion hSN)).range = (D.S.subgroupOf N).map ρ
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hkerV : ψV.ker = D.E.subgroupOf V := by
    change (ρ.comp (Subgroup.inclusion hVN)).ker = D.E.subgroupOf V
    rw [← MonoidHom.comap_ker, IsBasisRep.ker_eq hρ, Subgroup.comap_inclusion_subgroupOf]
  have hkerS : ψS.ker = D.E.subgroupOf D.S := by
    change (ρ.comp (Subgroup.inclusion hSN)).ker = D.E.subgroupOf D.S
    rw [← MonoidHom.comap_ker, IsBasisRep.ker_eq hρ, Subgroup.comap_inclusion_subgroupOf]
  have hcardEsubV : Nat.card (D.E.subgroupOf V) = 16 := by
    have h := Subgroup.card_subtype V (D.E.subgroupOf V)
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hEV] at h
    exact h.symm.trans D.card_E
  have hcardEsubS : Nat.card (D.E.subgroupOf D.S) = 16 := by
    have h := Subgroup.card_subtype D.S (D.E.subgroupOf D.S)
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hES] at h
    exact h.symm.trans D.card_E
  have hcardPV : Nat.card ((V.subgroupOf N).map ρ) = 4 := by
    have hcard := Subgroup.card_ker_mul_card_range ψV
    rw [hkerV, hcardEsubV, hψVrange, hVcard] at hcard
    omega
  have hcardPS : Nat.card ((D.S.subgroupOf N).map ρ) = 4 := by
    have hcard := Subgroup.card_ker_mul_card_range ψS
    rw [hkerS, hcardEsubS, hψSrange, D.card_S] at hcard
    omega
  have hA : fusionUnitA ∈ ρ.range := ⟨⟨D.h1, D.h1_mem_normalizer_E⟩, IsBasisRep.apply_h1 hρ⟩
  have hB : fusionUnitB ∈ ρ.range := ⟨⟨D.c1, D.c1_mem_normalizer_E⟩, IsBasisRep.apply_c1 hρ⟩
  have hF : fusionUnitF ∈ ρ.range := ⟨⟨D.f12, D.f12_mem_normalizer_E⟩, IsBasisRep.apply_f12 hρ⟩
  have hAPV : fusionUnitA ∈ (V.subgroupOf N).map ρ := by
    have hx : (⟨D.h1, D.h1_mem_normalizer_E⟩ : ↥N) ∈ V.subgroupOf N :=
      Subgroup.mem_subgroupOf.mpr hh1V
    have := Subgroup.mem_map_of_mem ρ hx
    rwa [IsBasisRep.apply_h1 hρ] at this
  have hAPS : fusionUnitA ∈ (D.S.subgroupOf N).map ρ := by
    have hx : (⟨D.h1, D.h1_mem_normalizer_E⟩ : ↥N) ∈ D.S.subgroupOf N :=
      Subgroup.mem_subgroupOf.mpr hh1S
    have := Subgroup.mem_map_of_mem ρ hx
    rwa [IsBasisRep.apply_h1 hρ] at this
  have hPVeq : (V.subgroupOf N).map ρ = Subgroup.closure {fusionUnitA, fusionUnitB} :=
    eq_closure_fusionUnitA_fusionUnitB hA hB hF (IsBasisRep.not_eight_dvd hρ)
      (Subgroup.map_le_range ρ (V.subgroupOf N)) hAPV hcardPV
  have hPSeq : (D.S.subgroupOf N).map ρ = Subgroup.closure {fusionUnitA, fusionUnitB} :=
    eq_closure_fusionUnitA_fusionUnitB hA hB hF (IsBasisRep.not_eight_dvd hρ)
      (Subgroup.map_le_range ρ (D.S.subgroupOf N)) hAPS hcardPS
  have hP_eq : (V.subgroupOf N).map ρ = (D.S.subgroupOf N).map ρ := hPVeq.trans hPSeq.symm
  have hkerN : ρ.ker ≤ V.subgroupOf N := by
    rw [IsBasisRep.ker_eq hρ]
    exact Subgroup.subgroupOf_mono N hEV
  have hkerNS : ρ.ker ≤ D.S.subgroupOf N := by
    rw [IsBasisRep.ker_eq hρ]
    exact Subgroup.subgroupOf_mono N hES
  have hVeqS : V.subgroupOf N = D.S.subgroupOf N := by
    calc V.subgroupOf N = ((V.subgroupOf N).map ρ).comap ρ :=
          (Subgroup.comap_map_eq_self hkerN).symm
      _ = ((D.S.subgroupOf N).map ρ).comap ρ := by rw [hP_eq]
      _ = D.S.subgroupOf N := Subgroup.comap_map_eq_self hkerNS
  have hVS : V = D.S := by
    have hin : V ⊓ N = D.S ⊓ N := Subgroup.subgroupOf_inj.mp hVeqS
    rwa [inf_eq_left.mpr hVN, inf_eq_left.mpr hSN] at hin
  have hvS : D.v ∈ D.S := hES (subset_closure (by simp))
  have hcenter : (⟨D.v, hvS⟩ : ↥D.S) ∈ center D.S := by
    rw [Subgroup.mem_center_iff]
    intro s
    refine Subtype.ext ?_
    have hsV : (s : G) ∈ V := hVS ▸ s.2
    exact Subgroup.mem_centralizer_singleton_iff.mp (hVCv hsV)
  rw [D.center_S] at hcenter
  have hvzp : D.v ∈ zpowers D.t :=
    (Subgroup.mem_subgroupOf (H := zpowers D.t) (K := D.S)).mp hcenter
  rcases (mem_zpowers_of_orderOf_eq_two D.orderOf_t).mp hvzp with hv1 | hvt
  · have hv := D.orderOf_v
    rw [hv1, orderOf_one] at hv
    exact absurd hv (by norm_num)
  · exact D.t_ne_d hM (by rw [D.v_eq_d] at hvt; exact hvt.symm)

end SwapData

end CFSG.OddTranspositions.PartThree.Wong
