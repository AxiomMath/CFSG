module

public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin.AppendixH.H11

open CFSG.Quasithin
open scoped symmDiff

variable {V : Type*} [CommGroup V] [Finite V]

private theorem card_closure_finset_le (hV : ∀ v : V, v ^ 2 = 1) (s : Finset V) :
    Nat.card (Subgroup.closure (s : Set V)) ≤ 2 ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.coe_empty, Subgroup.closure_empty, Subgroup.card_bot, Finset.card_empty]
    norm_num
  | insert a s ha ih =>
    have hcoe : ((insert a s : Finset V) : Set V) = ({a} : Set V) ∪ (s : Set V) := by
      ext x
      simp [Finset.mem_insert]
    rw [hcoe, Finset.card_insert_of_notMem ha, Subgroup.closure_union]
    have hcard_a : Nat.card (Subgroup.closure ({a} : Set V)) ≤ 2 := by
      rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.mpr (hV a))
    have hpos : 0 < Nat.card ↥(Subgroup.closure ({a} : Set V) ⊓
        Subgroup.closure (s : Set V)) := Nat.card_pos
    calc Nat.card ↥(Subgroup.closure ({a} : Set V) ⊔ Subgroup.closure (s : Set V))
        ≤ Nat.card ↥(Subgroup.closure ({a} : Set V) ⊔ Subgroup.closure (s : Set V)) *
            Nat.card ↥(Subgroup.closure ({a} : Set V) ⊓ Subgroup.closure (s : Set V)) :=
          Nat.le_mul_of_pos_right _ hpos
      _ = Nat.card ↥(Subgroup.closure ({a} : Set V)) *
            Nat.card ↥(Subgroup.closure (s : Set V)) :=
          card_sup_mul_card_inf _ _
      _ ≤ 2 * 2 ^ s.card := Nat.mul_le_mul hcard_a ih
      _ = 2 ^ (s.card + 1) := by rw [pow_succ]; ring

theorem le_rkIdx_of_independent_commutators (hV : ∀ v : V, v ^ 2 = 1) (t : MulAut V) {k : ℕ}
    (v : Fin k → V)
    (h : ∀ S : Finset (Fin k), S.Nonempty → ∏ s ∈ S, (t (v s) * (v s)⁻¹) ≠ 1) :
    k ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  classical
  have hΦinj : Function.Injective (fun S : Finset (Fin k) => ∏ s ∈ S, commHom t (v s)) := by
    intro S T hST
    by_contra hne
    simp_rw [commHom_apply] at hST
    have hSD : ∏ s ∈ S \ T, (t (v s) * (v s)⁻¹) =
        ∏ s ∈ T \ S, (t (v s) * (v s)⁻¹) :=
      (Finset.prod_sdiff_eq_prod_sdiff_iff).2 hST
    have hdisj : Disjoint (S \ T) (T \ S) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hx').1
    have hprod : ∏ s ∈ S ∆ T, (t (v s) * (v s)⁻¹) = 1 := by
      rw [Finset.symmDiff_def, Finset.prod_union hdisj, hSD, ← pow_two, hV]
    exact h (S ∆ T) (Finset.symmDiff_nonempty.mpr hne) hprod
  have hmem : ∀ S : Finset (Fin k), (∏ s ∈ S, commHom t (v s)) ∈ (commHom t).range :=
    fun S => ⟨∏ s ∈ S, v s, map_prod (commHom t) v S⟩
  have hfinj : Function.Injective
      (fun S : Finset (Fin k) =>
        (⟨∏ s ∈ S, commHom t (v s), hmem S⟩ : (commHom t).range)) := by
    intro S T hST
    exact hΦinj (Subtype.ext_iff.mp hST)
  have hleR : Nat.card (Finset (Fin k)) ≤ Nat.card (commHom t).range :=
    Nat.card_le_card_of_injective _ hfinj
  have hcardfin : Nat.card (Finset (Fin k)) = 2 ^ k := by
    rw [Nat.card_eq_fintype_card, Fintype.card_finset, Fintype.card_fin]
  have hrk : k ≤ rk (commHom t).range := by
    apply (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp
    calc 2 ^ k = Nat.card (Finset (Fin k)) := hcardfin.symm
      _ ≤ Nat.card (commHom t).range := hleR
      _ = 2 ^ rk (commHom t).range := card_eq_two_pow hV (commHom t).range
  rw [rkIdx_fixV_zpowers t, commV_zpowers_eq_map t, ← MonoidHom.range_eq_map]
  exact hrk

theorem rkIdx_le_of_commutators_mem (hV : ∀ v : V, v ^ 2 = 1) (t : MulAut V) (K : Subgroup V)
    {k : ℕ} (hK : Nat.card K ≤ 2 ^ k) (h : ∀ v : V, t v * v⁻¹ ∈ K) :
    rkIdx (fixV (Subgroup.zpowers t)) ≤ k := by
  have hrange : (commHom t).range ≤ K := by
    rintro x ⟨y, rfl⟩
    simpa [commHom_apply] using h y
  have hmain : rk (commHom t).range ≤ k := by
    have hcardK : Nat.card K = 2 ^ rk K := card_eq_two_pow hV K
    have hle : 2 ^ rk K ≤ 2 ^ k := by rw [← hcardK]; exact hK
    calc rk (commHom t).range ≤ rk K := rk_mono hrange
      _ ≤ k := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
  rw [rkIdx_fixV_zpowers t, commV_zpowers_eq_map t, ← MonoidHom.range_eq_map]
  exact hmain

theorem card_closure_range_le (hV : ∀ v : V, v ^ 2 = 1) {k : ℕ} (c : Fin k → V) :
    Nat.card (Subgroup.closure (Set.range c)) ≤ 2 ^ k := by
  classical
  have h1 := card_closure_finset_le hV (Finset.univ.image c)
  have hcoe : ((Finset.univ.image c : Finset V) : Set V) = Set.range c := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [hcoe] at h1
  have hcard : (Finset.univ.image c).card ≤ k := by
    calc (Finset.univ.image c).card ≤ Finset.univ.card := Finset.card_image_le
      _ = k := Finset.card_fin k
  calc Nat.card (Subgroup.closure (Set.range c)) ≤ 2 ^ (Finset.univ.image c).card := h1
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hcard

theorem five_le_rkIdx_of_inverts (hV : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 2 ^ 10)
    (t l : MulAut V) (ht : t * t = 1) (htl : t * l * t⁻¹ = l⁻¹)
    (hl : ∀ v : V, (l * l) v = v → v = 1) :
    5 ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  classical
  set C := fixV (Subgroup.zpowers t)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hclaim : ∀ w : V, w ∈ C → l w ∈ C → w = 1 := by
    intro w hw hlw
    have hw' : t w = w := mem_fixV_zpowers_iff.mp hw
    have hlw' : t (l w) = l w := mem_fixV_zpowers_iff.mp hlw
    have h1 : (t * l * t⁻¹) w = l⁻¹ w := by rw [htl]
    rw [MulAut.mul_apply, MulAut.mul_apply, htinv, hw', hlw'] at h1
    have hll : (l * l) w = w := by
      rw [MulAut.mul_apply, h1]
      simp
    exact hl w hll
  have hinf : C ⊓ C.map (l : V →* V) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr ?_
    rintro v ⟨hvC, hvmap⟩
    obtain ⟨w, hwC, hwl⟩ := hvmap
    have hw1 : w = 1 := hclaim w hwC (hwl.symm ▸ hvC)
    rw [← hwl, hw1]
    simp
  have hrkV : rk V = 10 := by
    unfold rk
    rw [hcard, padicValNat.prime_pow]
  have hrkmap : rk ↥(C.map (l : V →* V)) = rk C := by
    unfold rk
    rw [Subgroup.card_map_of_injective (f := (l : V →* V)) l.injective]
  have hsup : rk ↥(C ⊔ C.map (l : V →* V)) = 2 * rk C := by
    have h := rk_sup_add_rk_inf C (C.map (l : V →* V))
    rw [hinf, rk_bot, hrkmap] at h
    omega
  have hle : 2 * rk C ≤ 10 := by
    rw [← hsup]
    calc rk ↥(C ⊔ C.map (l : V →* V)) ≤ rk (⊤ : Subgroup V) := rk_mono le_top
      _ = rk V := rk_top
      _ = 10 := hrkV
  have hrkC : rk C ≤ 5 := by omega
  have hsum := rk_add_rkIdx C
  omega

theorem isElemAbelian2_of_isQuadratic (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)}
    (hA : IsQuadratic A) : IsElemAbelian2 A := by
  refine ⟨?_, ?_⟩
  · intro a ha b hb
    ext v
    have hbva : b v * v⁻¹ ∈ fixV A :=
      hA (Subgroup.subset_closure ⟨b, hb, v, rfl⟩)
    have hava : a v * v⁻¹ ∈ fixV A :=
      hA (Subgroup.subset_closure ⟨a, ha, v, rfl⟩)
    have haw : a (b v * v⁻¹) = b v * v⁻¹ := hbva a ha
    have hbw : b (a v * v⁻¹) = a v * v⁻¹ := hava b hb
    calc (a * b) v = a (b v) := rfl
      _ = a ((b v * v⁻¹) * v) := by rw [show (b v * v⁻¹) * v = b v by group]
      _ = a (b v * v⁻¹) * a v := by rw [map_mul]
      _ = (b v * v⁻¹) * a v := by rw [haw]
      _ = (a v * v⁻¹) * b v := by ac_rfl
      _ = b (a v * v⁻¹) * b v := by rw [hbw]
      _ = b ((a v * v⁻¹) * v) := by rw [← map_mul]
      _ = b (a v) := by rw [show (a v * v⁻¹) * v = a v by group]
      _ = (b * a) v := rfl
  · intro a ha
    rw [pow_two]
    ext v
    have hava : a v * v⁻¹ ∈ fixV A :=
      hA (Subgroup.subset_closure ⟨a, ha, v, rfl⟩)
    have haw : a (a v * v⁻¹) = a v * v⁻¹ := hava a ha
    calc (a * a) v = a (a v) := rfl
      _ = a ((a v * v⁻¹) * v) := by rw [show (a v * v⁻¹) * v = a v by group]
      _ = a (a v * v⁻¹) * a v := by rw [map_mul]
      _ = (a v * v⁻¹) * a v := by rw [haw]
      _ = (a v * v⁻¹) * (a v * v⁻¹) * v := by group
      _ = v := by rw [← pow_two, hV, one_mul]

theorem rkIdx_zpowers_le_rk_fixV_of_isQuadratic (hV : ∀ v : V, v ^ 2 = 1)
    {A : Subgroup (MulAut V)} (hA : IsQuadratic A) {a : MulAut V} (ha : a ∈ A) :
    rkIdx (fixV (Subgroup.zpowers a)) ≤ rk ↥(fixV A) := by
  have hmono : commV (Subgroup.zpowers a) ≤ commV A :=
    Subgroup.closure_mono fun _ ⟨x, hx, v, hv⟩ =>
      ⟨x, (Subgroup.zpowers_le.mpr ha) hx, v, hv⟩
  calc rkIdx (fixV (Subgroup.zpowers a)) = rk (commV (Subgroup.zpowers a)) :=
        rkIdx_fixV_zpowers a
    _ ≤ rk (commV A) := rk_mono hmono
    _ ≤ rk ↥(fixV A) := rk_mono hA

theorem card_eq_two_pow_rk (hV : ∀ v : V, v ^ 2 = 1) (H : Subgroup V) :
    Nat.card H = 2 ^ rk ↥H :=
  card_eq_two_pow hV H

end CFSG.Quasithin.AppendixH.H11
