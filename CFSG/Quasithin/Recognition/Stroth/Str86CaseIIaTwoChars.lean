module

public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaTwoTorus
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaTwoModel
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaTwoCoords

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open scoped Pointwise commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]

theorem str86_torus_chars_of_model
    {N S Kb L1 : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {k : ℕ}
    (hk : 2 ≤ k) (hKcard : Nat.card K = (2 ^ k) ^ 2)
    (Φ : Additive ↥N ≃+ (Fin 3 → K))
    (hLN : L1 ⊔ S ≤ Subgroup.normalizer (N : Set G))
    (hNL : Kb ≤ Subgroup.normalizer ((L1 ⊔ S : Subgroup G) : Set G))
    (hNS : Kb ≤ Subgroup.normalizer (S : Set G))
    (hNN : Kb ≤ Subgroup.normalizer (N : Set G))
    (hL1 : ∀ h ∈ L1 ⊔ S, ∃ x ∈ su3Anti K k, ∀ n n' : ↥N, (n' : G) = h * n * h⁻¹ →
      Φ (Additive.ofMul n') = (x : Matrix (Fin 3) (Fin 3) K) *ᵥ Φ (Additive.ofMul n))
    (hL2 : ∀ x ∈ su3Anti K k, ∃ h ∈ L1 ⊔ S, ∀ n n' : ↥N, (n' : G) = h * n * h⁻¹ →
      Φ (Additive.ofMul n') = (x : Matrix (Fin 3) (Fin 3) K) *ᵥ Φ (Additive.ofMul n))
    (hS1 : ∀ s ∈ S, ∃ x ∈ CFSG.Quasithin.H.SU3.ujSub k K, ∀ n n' : ↥N,
      (n' : G) = s * n * s⁻¹ →
      Φ (Additive.ofMul n') = (x : Matrix (Fin 3) (Fin 3) K) *ᵥ Φ (Additive.ofMul n))
    (hS2 : ∀ x ∈ CFSG.Quasithin.H.SU3.ujSub k K, ∃ s ∈ S, ∀ n n' : ↥N,
      (n' : G) = s * n * s⁻¹ →
      Φ (Additive.ofMul n') = (x : Matrix (Fin 3) (Fin 3) K) *ᵥ Φ (Additive.ofMul n))
    (hfix : ∀ (d : ↥Kb) (n : ↥N), (Φ (Additive.ofMul n)) 1 = 0 →
      (Φ (Additive.ofMul n)) 2 = 0 → (d : G) * (n : G) * (d : G)⁻¹ = (n : G)) :
    ∃ χ₂ χ₃ : ↥Kb →* Kˣ,
      (∀ d : ↥Kb, (χ₃ d : K) = (χ₂ d : K) ^ (2 ^ k + 1)) ∧
      (∀ d : ↥Kb, (χ₃ d : K) ^ (2 ^ k) = (χ₃ d : K)) ∧
      (∀ (d : ↥Kb) (n n' : ↥N), (n' : G) = (d : G) * n * (d : G)⁻¹ →
        Φ (Additive.ofMul n') 2 = Φ (Additive.ofMul n) 2 * (χ₃ d : K) ∧
        (Φ (Additive.ofMul n) 2 = 0 →
          Φ (Additive.ofMul n') 1 = Φ (Additive.ofMul n) 1 * (χ₂ d : K)) ∧
        (Φ (Additive.ofMul n) 1 = 0 → Φ (Additive.ofMul n) 2 = 0 →
          Φ (Additive.ofMul n') = Φ (Additive.ofMul n))) := by
  classical
  let conjEquiv (d : ↥Kb) : ↥N ≃* ↥N :=
    ((MulAut.conj (d : G)).subgroupMap N).trans
      (MulEquiv.subgroupCongr (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNN d.2)))
  let conjMem (d : ↥Kb) (n : ↥N) : (d : G) * (n : G) * (d : G)⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp (hNN d.2) (n : G)).mp n.2
  let memOfConjL (h : G) (hh : h ∈ L1 ⊔ S) (n : ↥N) : h * (n : G) * h⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp (hLN hh) (n : G)).mp n.2
  let memOfConjS (s : G) (hs : s ∈ S) (n : ↥N) : s * (n : G) * s⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp (((le_sup_right : S ≤ L1 ⊔ S).trans hLN) hs) (n : G)).mp n.2
  let g : ↥Kb → ((Fin 3 → K) ≃+ (Fin 3 → K)) := fun d =>
    Φ.symm.trans ((conjEquiv d).toAdditive.trans Φ)
  have hg_apply : ∀ (d : ↥Kb) (n : ↥N),
      g d (Φ (Additive.ofMul n)) =
        Φ (Additive.ofMul (⟨(d : G) * (n : G) * (d : G)⁻¹, conjMem d n⟩ : ↥N)) := by
    intro d n
    simp only [g, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
    congr 1
  have hg_apply_sub : ∀ (d : ↥Kb) (n : ↥N) (h : (d : G) * (n : G) * (d : G)⁻¹ ∈ N),
      g d (Φ (Additive.ofMul n)) =
        Φ (Additive.ofMul (⟨(d : G) * (n : G) * (d : G)⁻¹, h⟩ : ↥N)) := by
    intro d n h
    rw [hg_apply d n]
  have hg_mul_apply : ∀ (d d' : ↥Kb) (n : ↥N),
      g (d * d') (Φ (Additive.ofMul n)) = g d (g d' (Φ (Additive.ofMul n))) := by
    intro d d' n
    have hm1 : (d' : G) * (n : G) * (d' : G)⁻¹ ∈ N := conjMem d' n
    have hm2 : (d : G) * ((d' : G) * (n : G) * (d' : G)⁻¹) * (d : G)⁻¹ ∈ N :=
      conjMem d ⟨_, hm1⟩
    have hm3 : ((d * d' : ↥Kb) : G) * (n : G) * ((d * d' : ↥Kb) : G)⁻¹ ∈ N :=
      conjMem (d * d') n
    calc
      g (d * d') (Φ (Additive.ofMul n)) =
          Φ (Additive.ofMul (⟨((d * d' : ↥Kb) : G) * (n : G) *
            ((d * d' : ↥Kb) : G)⁻¹, hm3⟩ : ↥N)) := hg_apply_sub (d * d') n hm3
      _ = Φ (Additive.ofMul (⟨(d : G) * ((d' : G) * (n : G) * (d' : G)⁻¹) *
            (d : G)⁻¹, hm2⟩ : ↥N)) := by
          congr 1
          apply Subtype.ext
          simp only [Subgroup.coe_mul]
          group
      _ = g d (Φ (Additive.ofMul (⟨(d' : G) * (n : G) * (d' : G)⁻¹, hm1⟩ : ↥N))) :=
          (hg_apply_sub d ⟨_, hm1⟩ hm2).symm
      _ = g d (g d' (Φ (Additive.ofMul n))) := by rw [hg_apply d' n]
  have hg_mul : ∀ (d d' : ↥Kb) (v : Fin 3 → K), g (d * d') v = g d (g d' v) := by
    intro d d' v
    obtain ⟨n, rfl⟩ : ∃ n : ↥N, Φ (Additive.ofMul n) = v :=
      ⟨Additive.toMul (Φ.symm v), by simp⟩
    exact hg_mul_apply d d' n
  have hg_one_apply : ∀ n : ↥N, g 1 (Φ (Additive.ofMul n)) = Φ (Additive.ofMul n) := by
    intro n
    rw [hg_apply 1 n]
    congr 1
    apply Subtype.ext
    simp
  have hg_one : ∀ v : Fin 3 → K, g 1 v = v := by
    intro v
    obtain ⟨n, rfl⟩ : ∃ n : ↥N, Φ (Additive.ofMul n) = v :=
      ⟨Additive.toMul (Φ.symm v), by simp⟩
    exact hg_one_apply n
  have hgL : ∀ d : ↥Kb, ∀ x ∈ su3Anti K k, ∃ x' ∈ su3Anti K k, ∀ v,
      g d ((x : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
        (x' : Matrix (Fin 3) (Fin 3) K) *ᵥ g d v := by
    intro d x hx
    obtain ⟨h, hh, hhx⟩ := hL2 x hx
    have hdh : (d : G) * h * (d : G)⁻¹ ∈ L1 ⊔ S :=
      (Subgroup.mem_normalizer_iff.mp (hNL d.2) h).mp hh
    obtain ⟨x', hx', hx'x⟩ := hL1 _ hdh
    refine ⟨x', hx', ?_⟩
    intro v
    obtain ⟨n, rfl⟩ : ∃ n : ↥N, Φ (Additive.ofMul n) = v :=
      ⟨Additive.toMul (Φ.symm v), by simp⟩
    have hm1 : h * (n : G) * h⁻¹ ∈ N := memOfConjL h hh n
    have hm2 : (d : G) * (h * (n : G) * h⁻¹) * (d : G)⁻¹ ∈ N := conjMem d ⟨_, hm1⟩
    have hm3 : (d : G) * (n : G) * (d : G)⁻¹ ∈ N := conjMem d n
    have hm4 : ((d : G) * h * (d : G)⁻¹) * ((d : G) * (n : G) * (d : G)⁻¹) *
        ((d : G) * h * (d : G)⁻¹)⁻¹ ∈ N := memOfConjL _ hdh ⟨_, hm3⟩
    have hnx : Φ (Additive.ofMul (⟨h * (n : G) * h⁻¹, hm1⟩ : ↥N)) =
        (x : Matrix (Fin 3) (Fin 3) K) *ᵥ Φ (Additive.ofMul n) := hhx n ⟨_, hm1⟩ rfl
    have hdhx : Φ (Additive.ofMul (⟨((d : G) * h * (d : G)⁻¹) *
          ((d : G) * (n : G) * (d : G)⁻¹) * ((d : G) * h * (d : G)⁻¹)⁻¹, hm4⟩ : ↥N)) =
        (x' : Matrix (Fin 3) (Fin 3) K) *ᵥ
          Φ (Additive.ofMul (⟨(d : G) * (n : G) * (d : G)⁻¹, hm3⟩ : ↥N)) :=
      hx'x ⟨_, hm3⟩ ⟨_, hm4⟩ rfl
    calc
      g d ((x : Matrix (Fin 3) (Fin 3) K) *ᵥ Φ (Additive.ofMul n)) =
          g d (Φ (Additive.ofMul (⟨h * (n : G) * h⁻¹, hm1⟩ : ↥N))) := by rw [hnx]
      _ = Φ (Additive.ofMul (⟨(d : G) * (h * (n : G) * h⁻¹) * (d : G)⁻¹, hm2⟩ : ↥N)) :=
          hg_apply_sub d ⟨_, hm1⟩ hm2
      _ = Φ (Additive.ofMul (⟨((d : G) * h * (d : G)⁻¹) *
            ((d : G) * (n : G) * (d : G)⁻¹) * ((d : G) * h * (d : G)⁻¹)⁻¹, hm4⟩ : ↥N)) := by
          congr 1
          apply Subtype.ext
          group
      _ = (x' : Matrix (Fin 3) (Fin 3) K) *ᵥ
            Φ (Additive.ofMul (⟨(d : G) * (n : G) * (d : G)⁻¹, hm3⟩ : ↥N)) := hdhx
      _ = (x' : Matrix (Fin 3) (Fin 3) K) *ᵥ g d (Φ (Additive.ofMul n)) := by
          rw [hg_apply_sub d n hm3]
  have hgT : ∀ d : ↥Kb, ∀ x ∈ CFSG.Quasithin.H.SU3.ujSub k K, ∃ x' ∈
      CFSG.Quasithin.H.SU3.ujSub k K, ∀ v,
      g d ((x : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
        (x' : Matrix (Fin 3) (Fin 3) K) *ᵥ g d v := by
    intro d x hx
    obtain ⟨s, hs, hsx⟩ := hS2 x hx
    have hds : (d : G) * s * (d : G)⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp (hNS d.2) s).mp hs
    obtain ⟨x', hx', hx'x⟩ := hS1 _ hds
    refine ⟨x', hx', ?_⟩
    intro v
    obtain ⟨n, rfl⟩ : ∃ n : ↥N, Φ (Additive.ofMul n) = v :=
      ⟨Additive.toMul (Φ.symm v), by simp⟩
    have hm1 : s * (n : G) * s⁻¹ ∈ N := memOfConjS s hs n
    have hm2 : (d : G) * (s * (n : G) * s⁻¹) * (d : G)⁻¹ ∈ N := conjMem d ⟨_, hm1⟩
    have hm3 : (d : G) * (n : G) * (d : G)⁻¹ ∈ N := conjMem d n
    have hm4 : ((d : G) * s * (d : G)⁻¹) * ((d : G) * (n : G) * (d : G)⁻¹) *
        ((d : G) * s * (d : G)⁻¹)⁻¹ ∈ N := memOfConjS _ hds ⟨_, hm3⟩
    have hnx : Φ (Additive.ofMul (⟨s * (n : G) * s⁻¹, hm1⟩ : ↥N)) =
        (x : Matrix (Fin 3) (Fin 3) K) *ᵥ Φ (Additive.ofMul n) := hsx n ⟨_, hm1⟩ rfl
    have hdsx : Φ (Additive.ofMul (⟨((d : G) * s * (d : G)⁻¹) *
          ((d : G) * (n : G) * (d : G)⁻¹) * ((d : G) * s * (d : G)⁻¹)⁻¹, hm4⟩ : ↥N)) =
        (x' : Matrix (Fin 3) (Fin 3) K) *ᵥ
          Φ (Additive.ofMul (⟨(d : G) * (n : G) * (d : G)⁻¹, hm3⟩ : ↥N)) :=
      hx'x ⟨_, hm3⟩ ⟨_, hm4⟩ rfl
    calc
      g d ((x : Matrix (Fin 3) (Fin 3) K) *ᵥ Φ (Additive.ofMul n)) =
          g d (Φ (Additive.ofMul (⟨s * (n : G) * s⁻¹, hm1⟩ : ↥N))) := by rw [hnx]
      _ = Φ (Additive.ofMul (⟨(d : G) * (s * (n : G) * s⁻¹) * (d : G)⁻¹, hm2⟩ : ↥N)) :=
          hg_apply_sub d ⟨_, hm1⟩ hm2
      _ = Φ (Additive.ofMul (⟨((d : G) * s * (d : G)⁻¹) *
            ((d : G) * (n : G) * (d : G)⁻¹) * ((d : G) * s * (d : G)⁻¹)⁻¹, hm4⟩ : ↥N)) := by
          congr 1
          apply Subtype.ext
          group
      _ = (x' : Matrix (Fin 3) (Fin 3) K) *ᵥ
            Φ (Additive.ofMul (⟨(d : G) * (n : G) * (d : G)⁻¹, hm3⟩ : ↥N)) := hdsx
      _ = (x' : Matrix (Fin 3) (Fin 3) K) *ᵥ g d (Φ (Additive.ofMul n)) := by
          rw [hg_apply_sub d n hm3]
  have hg0 : ∀ d : ↥Kb, ∀ c : K, g d (Pi.single 0 c) = Pi.single 0 c := by
    intro d c
    obtain ⟨n, hn⟩ : ∃ n : ↥N, Φ (Additive.ofMul n) = Pi.single 0 c :=
      ⟨Additive.toMul (Φ.symm (Pi.single 0 c)), by simp⟩
    have h1 : (Φ (Additive.ofMul n)) 1 = 0 := by rw [hn]; simp
    have h2 : (Φ (Additive.ofMul n)) 2 = 0 := by rw [hn]; simp
    have hfixn : (d : G) * (n : G) * (d : G)⁻¹ = (n : G) := hfix d n h1 h2
    have hm : (d : G) * (n : G) * (d : G)⁻¹ ∈ N := conjMem d n
    calc
      g d (Pi.single 0 c) = g d (Φ (Additive.ofMul n)) := by rw [hn]
      _ = Φ (Additive.ofMul (⟨(d : G) * (n : G) * (d : G)⁻¹, hm⟩ : ↥N)) :=
          hg_apply_sub d n hm
      _ = Φ (Additive.ofMul n) := by
          rw [show (⟨(d : G) * (n : G) * (d : G)⁻¹, hm⟩ : ↥N) = n from Subtype.ext hfixn]
      _ = Pi.single 0 c := hn
  have hweight : ∀ d : ↥Kb, ∃ u₂ u₃ : Kˣ, (u₃ : K) = (u₂ : K) ^ (2 ^ k + 1) ∧
      (u₃ : K) ^ (2 ^ k) = (u₃ : K) ∧
      (∀ v : Fin 3 → K, v 2 = 0 → (g d v) 2 = 0) ∧
      (∀ v : Fin 3 → K, v 2 = 0 → (g d v) 1 = v 1 * (u₂ : K)) ∧
      (∀ v : Fin 3 → K, (g d v) 2 = v 2 * (u₃ : K)) := by
    intro d
    obtain ⟨u₂, u₃, hrel, hpow, hv2, hv1, hv3, -, -, -, -⟩ :=
      u3_similitude_weight_fpf (F := K) hk hKcard (g d) (hgL d) (hgT d) (hg0 d)
    exact ⟨u₂, u₃, hrel, hpow, hv2, hv1, hv3⟩
  choose u₂ u₃ hprops using hweight
  have hrel : ∀ d : ↥Kb, (u₃ d : K) = (u₂ d : K) ^ (2 ^ k + 1) := fun d => (hprops d).1
  have hpow : ∀ d : ↥Kb, (u₃ d : K) ^ (2 ^ k) = (u₃ d : K) := fun d => (hprops d).2.1
  have hv2 : ∀ (d : ↥Kb) (v : Fin 3 → K), v 2 = 0 → (g d v) 2 = 0 :=
    fun d => (hprops d).2.2.1
  have hv1 : ∀ (d : ↥Kb) (v : Fin 3 → K), v 2 = 0 → (g d v) 1 = v 1 * (u₂ d : K) :=
    fun d => (hprops d).2.2.2.1
  have hv3 : ∀ (d : ↥Kb) (v : Fin 3 → K), (g d v) 2 = v 2 * (u₃ d : K) :=
    fun d => (hprops d).2.2.2.2
  let χ₂ : ↥Kb →* Kˣ :=
    { toFun := u₂
      map_one' := by
        apply Units.ext
        have h := hv1 1 (Pi.single 1 (1 : K)) (by simp)
        rw [hg_one] at h
        simpa using h.symm
      map_mul' := by
        intro d d'
        apply Units.ext
        have h2 : (g d' (Pi.single 1 (1 : K))) 2 = 0 := by
          rw [hv3 d']
          simp
        calc
          (u₂ (d * d') : K) = (g (d * d') (Pi.single 1 (1 : K))) 1 := by
            rw [hv1 (d * d') (Pi.single 1 (1 : K)) (by simp)]
            simp
          _ = (g d (g d' (Pi.single 1 (1 : K)))) 1 := by rw [hg_mul]
          _ = (g d' (Pi.single 1 (1 : K))) 1 * (u₂ d : K) := hv1 d _ h2
          _ = ((Pi.single (1 : Fin 3) (1 : K) : Fin 3 → K) 1 * (u₂ d' : K)) * (u₂ d : K) := by
            rw [hv1 d' (Pi.single (1 : Fin 3) (1 : K) : Fin 3 → K) (by simp)]
          _ = (u₂ d' : K) * (u₂ d : K) := by simp
          _ = (u₂ d : K) * (u₂ d' : K) := mul_comm _ _ }
  let χ₃ : ↥Kb →* Kˣ :=
    { toFun := u₃
      map_one' := by
        apply Units.ext
        have h := hv3 1 (Pi.single 2 (1 : K))
        rw [hg_one] at h
        simpa using h.symm
      map_mul' := by
        intro d d'
        apply Units.ext
        calc
          (u₃ (d * d') : K) = (g (d * d') (Pi.single 2 (1 : K))) 2 := by
            rw [hv3 (d * d') (Pi.single 2 (1 : K))]
            simp
          _ = (g d (g d' (Pi.single 2 (1 : K)))) 2 := by rw [hg_mul]
          _ = (g d' (Pi.single 2 (1 : K))) 2 * (u₃ d : K) := hv3 d _
          _ = ((Pi.single (2 : Fin 3) (1 : K) : Fin 3 → K) 2 * (u₃ d' : K)) * (u₃ d : K) := by
            rw [hv3 d' (Pi.single (2 : Fin 3) (1 : K) : Fin 3 → K)]
          _ = (u₃ d' : K) * (u₃ d : K) := by simp
          _ = (u₃ d : K) * (u₃ d' : K) := mul_comm _ _ }
  have hχ₂_val : ∀ d : ↥Kb, (χ₂ d : K) = (u₂ d : K) := fun d => rfl
  have hχ₃_val : ∀ d : ↥Kb, (χ₃ d : K) = (u₃ d : K) := fun d => rfl
  refine ⟨χ₂, χ₃, fun d => hrel d, fun d => hpow d, ?_⟩
  intro d n n' hn
  have hm : (d : G) * (n : G) * (d : G)⁻¹ ∈ N := conjMem d n
  have hn'_eq : (⟨(d : G) * (n : G) * (d : G)⁻¹, hm⟩ : ↥N) = n' := Subtype.ext hn.symm
  have hΦ : Φ (Additive.ofMul n') = g d (Φ (Additive.ofMul n)) := by
    rw [← hn'_eq, hg_apply_sub d n hm]
  have h2 : Φ (Additive.ofMul n') 2 =
      Φ (Additive.ofMul n) 2 * (χ₃ d : K) := by
    rw [hΦ, hv3, hχ₃_val d]
  refine ⟨h2, ?_, ?_⟩
  · intro h0
    rw [hΦ, hv1 d _ h0, hχ₂_val d]
  · intro h1 h0
    have hfixn : (d : G) * (n : G) * (d : G)⁻¹ = (n : G) := hfix d n h1 h0
    rw [← hn'_eq]
    congr 1
    apply Subtype.ext
    exact hfixn

theorem str86_caseIIa_two_chars
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hm : IsL2Quot m (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hIIa : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G))
    (hZ : Z1 L1 L2 S ≤ Q2 L1 L2 S)
    (hc : IsChiefSeriesFrom (L2 ⊔ S) (str86U L1 L2 S) (str86U L1 L2 S) 2)
    {N : Subgroup G} (hN : IsElemAbelian 2 N)
    (hNZ : N ≤ Z1 L1 L2 S) (hNne : N ≠ ⊥)
    (hNP1 : P1 L1 L2 S ≤ Subgroup.normalizer (N : Set G))
    (hNS : S ⊓ Subgroup.centralizer (N : Set G) = Q1 L1 L2 S)
    (hNat : @BinaryNaturalSU3 ↥N (commGroupOfElemAbelian hN) (autOn (L1 ⊔ S) N) ⊤ ⊥ k)
    {Kb : Subgroup G} (hKb : Kb ≤ (L2 ⊔ S) ⊓ Subgroup.normalizer (S : Set G))
    (hKbB : Kb ≤ bigB L1 L2 S) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = (2 ^ k) ^ 2 ∧
      ∃ (Φ : Additive ↥N ≃+ (Fin 3 → K)) (χ₂ χ₃ : ↥Kb →* Kˣ),
        (∀ s ∈ S, ∃ x ∈ CFSG.Quasithin.H.SU3.ujSub k K, ∀ n n' : ↥N,
          (n' : G) = s * n * s⁻¹ →
          Φ (Additive.ofMul n') =
            (x : Matrix (Fin 3) (Fin 3) K).mulVec (Φ (Additive.ofMul n))) ∧
        (∀ x ∈ CFSG.Quasithin.H.SU3.ujSub k K, ∃ s ∈ S, ∀ n n' : ↥N,
          (n' : G) = s * n * s⁻¹ →
          Φ (Additive.ofMul n') =
            (x : Matrix (Fin 3) (Fin 3) K).mulVec (Φ (Additive.ofMul n))) ∧
        (∀ d : ↥Kb, (χ₃ d : K) = (χ₂ d : K) ^ (2 ^ k + 1)) ∧
        (∀ d : ↥Kb, (χ₃ d : K) ^ (2 ^ k) = (χ₃ d : K)) ∧
        (∀ (d : ↥Kb) (n n' : ↥N), (n' : G) = (d : G) * n * (d : G)⁻¹ →
          Φ (Additive.ofMul n') 2 = Φ (Additive.ofMul n) 2 * (χ₃ d : K) ∧
          (Φ (Additive.ofMul n) 2 = 0 →
            Φ (Additive.ofMul n') 1 = Φ (Additive.ofMul n) 1 * (χ₂ d : K)) ∧
          (Φ (Additive.ofMul n) 1 = 0 → Φ (Additive.ofMul n) 2 = 0 →
            Φ (Additive.ofMul n') = Φ (Additive.ofMul n)))  := by
  classical

  have hm2 : 2 ≤ m :=
    CFSG.Quasithin.F112R.two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hm
  have hS2eq : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hSB (Or.inr (Or.inr ⟨m, hm2, hm⟩))
  have hQ2S : Q2 L1 L2 S ≤ S := by
    calc
      Q2 L1 L2 S ≤ (S ⊓ L2) ⊔ Q2 L1 L2 S := le_sup_right
      _ = S := hS2eq.symm
  have hSle : S ≤ L2 ⊔ Q2 L1 L2 S := by
    calc
      S = (S ⊓ L2) ⊔ Q2 L1 L2 S := hS2eq
      _ ≤ L2 ⊔ Q2 L1 L2 S := sup_le (inf_le_right.trans le_sup_left) le_sup_right
  have hKbL2S : Kb ≤ L2 ⊔ S := fun x hx => (hKb hx).1
  have hKbS : Kb ≤ Subgroup.normalizer (S : Set G) := fun x hx => (hKb hx).2
  have hKbZ2 : Kb ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    (hKbL2S.trans (sup_le le_sup_left hSle)).trans hIIa
  have hLN : L1 ⊔ S ≤ Subgroup.normalizer (N : Set G) :=
    sup_le ((le_sup_left : L1 ≤ P1 L1 L2 S).trans hNP1)
      (((le_sup_right : S ≤ bigB L1 L2 S).trans
        (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S)).trans hNP1)
  have hSN : S ≤ Subgroup.normalizer (N : Set G) := le_sup_right.trans hLN
  have hNL : Kb ≤ Subgroup.normalizer ((L1 ⊔ S : Subgroup G) : Set G) :=
    (le_inf (hKbB.trans (bigB_le_normalizer_of_hyp111 hF.1)) hKbS).trans
      (Subgroup.inf_normalizer_le_normalizer_sup L1 S)
  have hNN : Kb ≤ Subgroup.normalizer (N : Set G) :=
    hKbB.trans ((le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S).trans hNP1)
  obtain ⟨K, hK, hKfin, hKchar, hKcard, Φ, hL1, hL2, hS1, hS2⟩ :=
    str86_caseIIa_two_model hF hSB hk hFc hU3 hB2 hm hII hIIa hZ hc hN hNZ hNne hNP1 hNS hNat
  letI : Field K := hK
  letI : Finite K := hKfin
  letI : CharP K 2 := hKchar
  have hflag := str86_flag_coords_of_ujSub hN hSN hk hKcard Φ hS1 hS2
  have hfix : ∀ (d : ↥Kb) (n : ↥N), (Φ (Additive.ofMul n)) 1 = 0 →
      (Φ (Additive.ofMul n)) 2 = 0 → (d : G) * (n : G) * (d : G)⁻¹ = (n : G) := by
    intro d n h1 h2
    have hcenS : (n : G) ∈ Subgroup.centralizer (S : Set G) := (hflag.1 n).mpr ⟨h1, h2⟩
    have hnQ2 : (n : G) ∈ Q2 L1 L2 S := hZ (hNZ n.2)
    have hn2 : (n : G) * (n : G) = 1 := by
      have := hN.2 (n : G) n.2
      simpa [pow_two] using this
    have hcenQ2 : (n : G) ∈ Subgroup.centralizer (Q2 L1 L2 S : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact Subgroup.mem_centralizer_iff.mp hcenS z (hQ2S hz)
    have hnZ2 : (n : G) ∈ Z2 L1 L2 S :=
      mem_omegaOneCenterOf hnQ2 (Subgroup.mem_centralizer_iff.mp hcenQ2)
        (by rw [pow_two]; exact hn2)
    have hcomm : (n : G) * (d : G) = (d : G) * (n : G) :=
      Subgroup.mem_centralizer_iff.mp (hKbZ2 d.2) (n : G) hnZ2
    rw [← hcomm]
    group
  obtain ⟨χ₂, χ₃, hrel, hpow, hcoord⟩ :=
    str86_torus_chars_of_model (N := N) (S := S) (Kb := Kb) (L1 := L1) hk hKcard Φ
      hLN hNL hKbS hNN hL1 hL2 hS1 hS2 hfix
  refine ⟨K, hK, hKfin, hKchar, hKcard, Φ, χ₂, χ₃, ?_, ?_, ?_, ?_, ?_⟩
  · exact hS1
  · exact hS2
  · exact hrel
  · exact hpow
  · exact hcoord

end CFSG.Quasithin.Stroth
