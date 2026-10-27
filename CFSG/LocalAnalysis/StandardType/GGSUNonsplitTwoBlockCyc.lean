module

public import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlockForm

public section

namespace CFSG.StandardType

namespace SUTB

open Module Polynomial CFSG.RankThree.PartOne.OddIso

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

theorem aeval_mem_of_inv {U : Submodule K V} {X : Module.End K V} (hU : ∀ u ∈ U, X u ∈ U)
    (P : K[X]) {u : V} (hu : u ∈ U) : aeval X P u ∈ U := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, LinearMap.add_apply]; exact U.add_mem hP hQ
  | monomial k c =>
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact U.smul_mem c (invariant_pow hU k u hu)

theorem eq_cyc_of_le {X : Module.End K V} {g : K[X]} (hg : Irreducible g) {w : V}
    (hw : aeval X g w = 0) {S : Submodule K V} (hS : S ≤ cyc X w) (hSX : ∀ s ∈ S, X s ∈ S)
    (hS0 : S ≠ ⊥) : S = cyc X w := by
  refine le_antisymm hS (cyc_le hSX ?_)
  obtain ⟨s, hsS, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  obtain ⟨t, rfl⟩ := (mem_cyc_iff X w s).mp (hS hsS)
  have hgt : ¬ g ∣ t := by
    rintro ⟨q, rfl⟩
    apply hs0
    rw [mul_comm, map_mul, Module.End.mul_apply, hw, map_zero]
  obtain ⟨a, b, hab⟩ := (hg.coprime_iff_not_dvd.mpr hgt).symm
  have h1 : aeval X (a * t + b * g) w = w := by rw [hab, map_one, Module.End.one_apply]
  rw [map_add, map_mul, map_mul, LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply,
    hw, map_zero, add_zero] at h1
  rw [← h1]
  exact aeval_mem_of_inv hSX a hsS

theorem span_pow_eq_cyc {X : Module.End K V} {p : ℕ} (hp : 0 < p) (hXp : X ^ p = 1) (w : V) :
    Submodule.span K (Set.range fun k : Fin p => (X ^ (k : ℕ)) w) = cyc X w := by
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro _ ⟨k, rfl⟩
    exact pow_mem_cyc X w k
  · rintro _ ⟨i, rfl⟩
    refine Submodule.subset_span ⟨⟨i % p, Nat.mod_lt _ hp⟩, ?_⟩
    change (X ^ (i % p)) w = (X ^ i) w
    conv_rhs => rw [← Nat.mod_add_div i p, pow_add, pow_mul, hXp, one_pow, mul_one]

theorem pow_succ_mod_apply {X : Module.End K V} {p : ℕ} (hXp : X ^ p = 1) (w : V) (k : ℕ) :
    X ((X ^ k) w) = (X ^ ((k + 1) % p)) w := by
  rw [← Module.End.mul_apply, ← pow_succ']
  conv_lhs => rw [← Nat.mod_add_div (k + 1) p, pow_add, pow_mul, hXp, one_pow, mul_one]

variable {σ : K →+* K} {B : V →ₛₗ[σ] V →ₗ[K] K}

theorem apply_left_eq {X : Module.End K V} (hXB : ∀ v w, B (X v) (X w) = B v w) {p : ℕ}
    (hp : 1 ≤ p) (hXp : X ^ p = 1) (v w : V) : B (X v) w = B v ((X ^ (p - 1)) w) := by
  have h1 : X ((X ^ (p - 1)) w) = w := by
    rw [← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel hp, hXp, Module.End.one_apply]
  rw [← hXB v ((X ^ (p - 1)) w), h1]

theorem nondegOn_cyc_sup (hB : B.IsSymm) {X : Module.End K V}
    (hXB : ∀ v w, B (X v) (X w) = B v w) {p : ℕ} (hp : 1 ≤ p) (hXp : X ^ p = 1) {g g' : K[X]}
    (hg : Irreducible g) (hg' : Irreducible g') {w w' : V} (hw : aeval X g w = 0)
    (hw' : aeval X g' w' = 0) (hww' : B w w' ≠ 0)
    (hiso : ∀ a ∈ cyc X w, ∀ b ∈ cyc X w, B a b = 0)
    (hiso' : ∀ a ∈ cyc X w', ∀ b ∈ cyc X w', B a b = 0) :
    NondegOn B (cyc X w ⊔ cyc X w') := by
  have hinv : ∀ u : V, ∀ v ∈ cyc X u, (X ^ (p - 1)) v ∈ cyc X u := fun u v hv =>
    invariant_pow (cyc_invariant X u) (p - 1) v hv
  let R : Submodule K V :=
    { carrier := {v | v ∈ cyc X w ∧ ∀ v' ∈ cyc X w', B v v' = 0}
      add_mem' := fun ha hb => ⟨(cyc X w).add_mem ha.1 hb.1, fun v' hv' => by
        rw [map_add, LinearMap.add_apply, ha.2 v' hv', hb.2 v' hv', add_zero]⟩
      zero_mem' := ⟨(cyc X w).zero_mem, fun v' _ => by rw [map_zero, LinearMap.zero_apply]⟩
      smul_mem' := fun c v hv => ⟨(cyc X w).smul_mem c hv.1, fun v' hv' => by
        rw [map_smulₛₗ, LinearMap.smul_apply, hv.2 v' hv', smul_zero]⟩ }
  have hmemR : ∀ s, s ∈ R ↔ s ∈ cyc X w ∧ ∀ v' ∈ cyc X w', B s v' = 0 := fun s => Iff.rfl
  have hR : R = ⊥ := by
    by_contra hR0
    have hRX : ∀ s ∈ R, X s ∈ R := fun s hs => by
      obtain ⟨hs1, hs2⟩ := (hmemR s).mp hs
      refine (hmemR _).mpr ⟨cyc_invariant X w s hs1, fun v' hv' => ?_⟩
      rw [apply_left_eq hXB hp hXp, hs2 _ (hinv w' v' hv')]
    have hRZ := eq_cyc_of_le hg hw (fun s hs => ((hmemR s).mp hs).1) hRX hR0
    have hwR : w ∈ R := hRZ ▸ pow_mem_cyc X w 0
    exact hww' (((hmemR w).mp hwR).2 w' (by simpa using pow_mem_cyc X w' 0))
  let R' : Submodule K V :=
    { carrier := {v' | v' ∈ cyc X w' ∧ ∀ v ∈ cyc X w, B v v' = 0}
      add_mem' := fun ha hb => ⟨(cyc X w').add_mem ha.1 hb.1, fun v hv => by
        rw [map_add, ha.2 v hv, hb.2 v hv, add_zero]⟩
      zero_mem' := ⟨(cyc X w').zero_mem, fun v _ => by rw [map_zero]⟩
      smul_mem' := fun c v' hv' => ⟨(cyc X w').smul_mem c hv'.1, fun v hv => by
        rw [map_smul, hv'.2 v hv, smul_zero]⟩ }
  have hmemR' : ∀ s, s ∈ R' ↔ s ∈ cyc X w' ∧ ∀ v ∈ cyc X w, B v s = 0 := fun s => Iff.rfl
  have hR' : R' = ⊥ := by
    by_contra hR0
    have hRX : ∀ s ∈ R', X s ∈ R' := fun s hs => by
      obtain ⟨hs1, hs2⟩ := (hmemR' s).mp hs
      refine (hmemR' _).mpr ⟨cyc_invariant X w' s hs1, fun v hv => ?_⟩
      have h2 : X ((X ^ (p - 1)) v) = v := by
        rw [← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel hp, hXp, Module.End.one_apply]
      calc B v (X s) = B (X ((X ^ (p - 1)) v)) (X s) := by rw [h2]
        _ = B ((X ^ (p - 1)) v) s := hXB _ _
        _ = 0 := hs2 _ (hinv w v hv)
    have hRZ := eq_cyc_of_le hg' hw' (fun s hs => ((hmemR' s).mp hs).1) hRX hR0
    have hwR : w' ∈ R' := hRZ ▸ pow_mem_cyc X w' 0
    exact hww' (((hmemR' w').mp hwR).2 w (by simpa using pow_mem_cyc X w 0))
  intro m hm hn
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hm
  have hb0 : b = 0 := by
    have : b ∈ R' := (hmemR' b).mpr ⟨hb, fun v hv => by
      have h1 := hn v (Submodule.mem_sup_left hv)
      rwa [map_add, hiso v hv a ha, zero_add] at h1⟩
    rw [hR'] at this
    exact (Submodule.mem_bot K).mp this
  have ha0 : a = 0 := by
    have : a ∈ R := (hmemR a).mpr ⟨ha, fun v' hv' => by
      have h1 := hn v' (Submodule.mem_sup_right hv')
      rw [map_add, hiso' v' hv' b hb, add_zero] at h1
      rw [← hB.eq v' a, h1, map_zero]⟩
    rw [hR] at this
    exact (Submodule.mem_bot K).mp this
  rw [ha0, hb0, add_zero]

end SUTB

end CFSG.StandardType
