module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.A1cRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

private theorem s16h_cx_isElemAbelian_of_card_eq_prime {A : Type*} [Group A] {p : ℕ}
    (hp : p.Prime) {H : Subgroup A} (hH : Nat.card ↥H = p) : IsElemAbelian p H := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic ↥H := isCyclic_of_prime_card hH
  refine ⟨inferInstance, ?_⟩
  intro x hx
  have h := pow_card_eq_one' (G := ↥H) (x := ⟨x, hx⟩)
  rw [hH] at h
  simpa using Subtype.ext_iff.mp h

theorem s16h_closure_of_le_commutator {A : Type*} [Group A] [Finite A] {Mb Lb : Subgroup A}
    {p : ℕ} (hp : p.Prime) (hLb : Nat.card ↥Lb = p) (hLd : Lb ≤ ⁅Mb, Mb⁆)
    (hcomm : ∀ q ∈ Mb, ∀ q' ∈ Mb,
      Lb.map (MulAut.conj q).toMonoidHom ≠ Lb.map (MulAut.conj q').toMonoidHom →
        ⁅Lb.map (MulAut.conj q).toMonoidHom, Lb.map (MulAut.conj q').toMonoidHom⁆ = ⊥)
    (hind : sSupIndep {X : Subgroup A | ∃ q ∈ Mb, X = Lb.map (MulAut.conj q).toMonoidHom}) :
    ∃ X : Subgroup A, X ≤ ⁅Mb, Mb⁆ ∧ (∀ q ∈ Mb, ∀ x ∈ X, q * x * q⁻¹ ∈ X) ∧
      IsElemAbelian p X ∧ Nat.card ↥X =
        p ^ Set.ncard {X : Subgroup A | ∃ q ∈ Mb, X = Lb.map (MulAut.conj q).toMonoidHom} := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let S : Set (Subgroup A) := {X : Subgroup A | ∃ q ∈ Mb, X = Lb.map (MulAut.conj q).toMonoidHom}
  let X0 : Subgroup A := sSup S
  let Hm : Subgroup A := ⁅Mb, Mb⁆
  have hS_range : S = Set.range (fun q : Mb => Lb.map (MulAut.conj (q : A)).toMonoidHom) := by
    ext U
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨q, q.2, rfl⟩
  have hSfin : S.Finite := by
    rw [hS_range]
    exact Set.finite_range (fun q : Mb => Lb.map (MulAut.conj (q : A)).toMonoidHom)
  haveI : Fintype ↥S := hSfin.fintype
  have hcard_mem : ∀ ω : ↥S, Nat.card ↥(ω : Subgroup A) = p := by
    intro ω
    obtain ⟨q, hq, hqeq⟩ := ω.2
    rw [hqeq, Subgroup.card_map_of_injective (MulAut.conj q).injective, hLb]
  let Hsub : ↥S → Subgroup A := fun ω => (ω : Subgroup A)
  have hcommS : Pairwise fun i j : ↥S => ∀ x y : A, x ∈ Hsub i → y ∈ Hsub j → Commute x y := by
    rintro i j hij x y hx hy
    obtain ⟨q, hq, hqeq⟩ := i.2
    obtain ⟨q', hq', hq'eq⟩ := j.2
    have hne : Lb.map (MulAut.conj q).toMonoidHom ≠ Lb.map (MulAut.conj q').toMonoidHom := by
      intro heq
      exact hij (Subtype.ext (by rw [hqeq, hq'eq, heq]))
    have hx' : x ∈ Lb.map (MulAut.conj q).toMonoidHom := hqeq ▸ hx
    have hy' : y ∈ Lb.map (MulAut.conj q').toMonoidHom := hq'eq ▸ hy
    have hmem := Subgroup.commutator_mem_commutator hx' hy'
    rw [hcomm q hq q' hq' hne, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_commute.mp hmem
  have hφinj : Function.Injective (Subgroup.noncommPiCoprod (H := Hsub) hcommS) :=
    Subgroup.injective_noncommPiCoprod_of_iSupIndep ((sSupIndep_iff S).1 hind)
  have hX0eq : X0 = ⨆ ω : ↥S, (ω : Subgroup A) := sSup_eq_iSup' S
  have hφrange : (Subgroup.noncommPiCoprod (H := Hsub) hcommS).range = X0 := by
    rw [Subgroup.noncommPiCoprod_range]
    change (⨆ i : ↥S, (i : Subgroup A)) = X0
    rw [← sSup_eq_iSup']
  have hcardX0 : Nat.card ↥X0 = p ^ Set.ncard S := by
    have hker : (Subgroup.noncommPiCoprod (H := Hsub) hcommS).ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff _).2 hφinj
    have hcard := Subgroup.card_ker_mul_card_range (Subgroup.noncommPiCoprod (H := Hsub) hcommS)
    rw [hker, Subgroup.card_bot, one_mul, hφrange] at hcard
    calc Nat.card ↥X0
        = Nat.card (∀ ω : ↥S, ↥(Hsub ω)) := hcard
      _ = ∏ ω : ↥S, Nat.card ↥(Hsub ω) := Nat.card_pi
      _ = ∏ _ω : ↥S, p := Finset.prod_congr rfl (fun ω _ => hcard_mem ω)
      _ = p ^ Set.ncard S := by
            rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
              Nat.card_coe_set_eq]
  have hmemEA : ∀ ω : ↥S, IsElemAbelian p (ω : Subgroup A) :=
    fun ω => s16h_cx_isElemAbelian_of_card_eq_prime hp (hcard_mem ω)
  have hcomm_pair : ∀ ω ω' : ↥S, ω ≠ ω' →
      ∀ x y : A, x ∈ (ω : Subgroup A) → y ∈ (ω' : Subgroup A) → x * y = y * x :=
    fun ω ω' hne x y hx hy => (hcommS hne x y hx hy).eq
  have hcomm_same : ∀ ω : ↥S, ∀ x ∈ (ω : Subgroup A), ∀ y ∈ (ω : Subgroup A),
      x * y = y * x := by
    intro ω x hx y hy
    haveI := (hmemEA ω).1
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥(ω : Subgroup A)) ⟨y, hy⟩)
  have hX0comm : ∀ x ∈ X0, ∀ y ∈ X0, x * y = y * x := by
    intro x hx
    have hx' : x ∈ ⨆ ω : ↥S, (ω : Subgroup A) := hX0eq ▸ hx
    refine Subgroup.iSup_induction (C := fun v => ∀ y ∈ X0, v * y = y * v)
      (fun ω : ↥S => (ω : Subgroup A)) hx' ?_ ?_ ?_
    · intro ω z hzω
      intro y hy
      have hy' : y ∈ ⨆ ω' : ↥S, (ω' : Subgroup A) := hX0eq ▸ hy
      refine Subgroup.iSup_induction (C := fun w => z * w = w * z)
        (fun ω' : ↥S => (ω' : Subgroup A)) hy' ?_ ?_ ?_
      · intro ω' w hwω'
        by_cases hω : ω = ω'
        · subst hω
          exact hcomm_same ω z hzω w hwω'
        · exact hcomm_pair ω ω' hω z w hzω hwω'
      · simp
      · intro a b iha ihb
        rw [← mul_assoc, iha, mul_assoc, ihb, ← mul_assoc]
    · intro y hy
      simp
    · intro a b iha ihb y hy
      rw [mul_assoc, ihb y hy, ← mul_assoc, iha y hy, mul_assoc]
  have hX0exp : ∀ x ∈ X0, x ^ p = 1 := by
    intro x hx
    have hx' : x ∈ ⨆ ω : ↥S, (ω : Subgroup A) := hX0eq ▸ hx
    refine (Subgroup.iSup_induction (C := fun v => v ∈ X0 ∧ v ^ p = 1)
      (fun ω : ↥S => (ω : Subgroup A)) hx' ?_ ?_ ?_).2
    · intro ω v hv
      refine ⟨?_, (hmemEA ω).2 v hv⟩
      rw [hX0eq]
      exact le_iSup (fun ω : ↥S => (ω : Subgroup A)) ω hv
    · exact ⟨X0.one_mem, one_pow p⟩
    · intro a b ha hb
      refine ⟨X0.mul_mem ha.1 hb.1, ?_⟩
      have hc : Commute a b := hX0comm a ha.1 b hb.1
      rw [hc.mul_pow p, ha.2, hb.2, mul_one]
  have hEA0 : IsElemAbelian p X0 :=
    ⟨IsMulCommutative.of_comm
        (fun a b : X0 => Subtype.ext (hX0comm (a : A) a.2 (b : A) b.2)), hX0exp⟩
  have hX0norm : ∀ q ∈ Mb, ∀ x ∈ X0, q * x * q⁻¹ ∈ X0 := by
    intro q hq x hx
    have hx' : x ∈ ⨆ ω : ↥S, (ω : Subgroup A) := hX0eq ▸ hx
    refine Subgroup.iSup_induction (C := fun v => q * v * q⁻¹ ∈ X0)
      (fun ω : ↥S => (ω : Subgroup A)) hx' ?_ ?_ ?_
    · intro ω z hzω
      obtain ⟨m, hm, hmeq⟩ := ω.2
      have hzL : z ∈ Lb.map (MulAut.conj m).toMonoidHom := hmeq ▸ hzω
      obtain ⟨l, hl, hl_eq⟩ := Subgroup.mem_map.mp hzL
      have hzmem : q * z * q⁻¹ ∈ Lb.map (MulAut.conj (q * m)).toMonoidHom := by
        have heq : q * z * q⁻¹ = (MulAut.conj (q * m)).toMonoidHom l := by
          rw [← hl_eq]
          change q * MulAut.conj m l * q⁻¹ = MulAut.conj (q * m) l
          rw [MulAut.conj_apply, MulAut.conj_apply]
          group
        rw [heq]
        exact Subgroup.mem_map_of_mem _ hl
      rw [hX0eq]
      exact le_iSup (fun ω : ↥S => (ω : Subgroup A))
        ⟨Lb.map (MulAut.conj (q * m)).toMonoidHom, q * m, Mb.mul_mem hq hm, rfl⟩ hzmem
    · simpa using X0.one_mem
    · intro a b iha ihb
      rw [show q * (a * b) * q⁻¹ = (q * a * q⁻¹) * (q * b * q⁻¹) from by group]
      exact X0.mul_mem iha ihb
  have hHmNorm : Mb ≤ Subgroup.normalizer (Hm : Set A) :=
    Subgroup.normalizer_commutator_ge_left Mb Mb
  have hX0Hm : X0 ≤ Hm := by
    rw [hX0eq]
    apply iSup_le
    intro ω
    obtain ⟨q, hq, hqeq⟩ := ω.2
    rw [hqeq]
    rintro x ⟨l, hl, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hHmNorm hq) l).mp (hLd hl)
  exact ⟨X0, hX0Hm, hX0norm, hEA0, hcardX0⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
