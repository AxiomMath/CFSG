module

public import CFSG.Quasithin.Vol2.Ch3Sec3S6Sylow
public import CFSG.Quasithin.Vol2.Ch3Sec3A6Inputs
public import CFSG.Quasithin.Vol2.Ch3Sec3Par32S6Pack

public section

namespace CFSG.Quasithin.H13.Par32

open CFSG.Quasithin.H13.A6Coc

@[expose] def code (σ : Equiv.Perm (Fin 6)) : ℕ :=
  (σ 0 : ℕ) + 6 * ((σ 1 : ℕ) + 6 * ((σ 2 : ℕ) + 6 * ((σ 3 : ℕ) + 6 * ((σ 4 : ℕ) +
    6 * (σ 5 : ℕ)))))

theorem code_injective : Function.Injective code := by
  intro σ τ h
  simp only [code] at h
  have h0 := (σ 0).isLt
  have h1 := (σ 1).isLt
  have h2 := (σ 2).isLt
  have h3 := (σ 3).isLt
  have h4 := (σ 4).isLt
  have h5 := (σ 5).isLt
  have k0 := (τ 0).isLt
  have k1 := (τ 1).isLt
  have k2 := (τ 2).isLt
  have k3 := (τ 3).isLt
  have k4 := (τ 4).isLt
  have k5 := (τ 5).isLt
  have e0 : (σ 0 : ℕ) = τ 0 := by omega
  have e1 : (σ 1 : ℕ) = τ 1 := by omega
  have e2 : (σ 2 : ℕ) = τ 2 := by omega
  have e3 : (σ 3 : ℕ) = τ 3 := by omega
  have e4 : (σ 4 : ℕ) = τ 4 := by omega
  have e5 : (σ 5 : ℕ) = τ 5 := by omega
  refine Equiv.ext fun i => Fin.ext ?_
  fin_cases i
  exacts [e0, e1, e2, e3, e4, e5]

theorem mem_of_code_mem {E : List (Equiv.Perm (Fin 6))} {x : Equiv.Perm (Fin 6)}
    (h : code x ∈ E.map code) : x ∈ E := by
  obtain ⟨y, hy, hxy⟩ := List.mem_map.mp h
  rwa [code_injective hxy] at hy

theorem closure_subset {S E : List (Equiv.Perm (Fin 6))} (hS : ∀ s ∈ S, s * s = 1)
    (h1 : (1 : Equiv.Perm (Fin 6)) ∈ E) (hE : ∀ x ∈ E, ∀ s ∈ S, x * s ∈ E) :
    ∀ x ∈ Subgroup.closure {x | x ∈ S}, x ∈ E := by
  intro x hx
  induction hx using Subgroup.closure_induction_right with
  | one => exact h1
  | mul_right x _ s hs ih => exact hE x ih s hs
  | mul_inv_cancel x _ s hs ih =>
    rw [inv_eq_of_mul_eq_one_right (hS s hs)]
    exact hE x ih s hs

theorem card_eq_length {H : Subgroup (Equiv.Perm (Fin 6))} {E : List (Equiv.Perm (Fin 6))}
    (hE : (E.map code).Nodup) (h : ∀ x, x ∈ H ↔ x ∈ E) : Nat.card H = E.length := by
  have e : Nat.card H = E.toFinset.card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [h])
  rw [e, List.toFinset_card_of_nodup (List.Nodup.of_map code hE)]

theorem two_mul_card_inf_alternatingGroup {K : Subgroup (Equiv.Perm (Fin 6))}
    {x : Equiv.Perm (Fin 6)} (hx : x ∈ K) (hsx : Equiv.Perm.sign x = -1) :
    2 * Nat.card ↥(K ⊓ alternatingGroup (Fin 6)) = Nat.card K := by
  let f : ↥K →* ℤˣ := Equiv.Perm.sign.comp K.subtype
  have hker : f.ker = (alternatingGroup (Fin 6)).subgroupOf K := by
    ext k
    simp [f, Subgroup.mem_subgroupOf, Equiv.Perm.mem_alternatingGroup]
  have hrange : Nat.card f.range = 2 := by
    have : f.range = ⊤ := by
      refine MonoidHom.range_eq_top.mpr fun u => ?_
      rcases Int.units_eq_one_or u with rfl | rfl
      · exact ⟨1, map_one f⟩
      · exact ⟨⟨x, hx⟩, hsx⟩
    rw [this, Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_units_int]
  have h1 := Subgroup.index_ker f
  rw [hker, hrange] at h1
  have h2 := Subgroup.relIndex_mul_card (H := alternatingGroup (Fin 6)) (K := K)
  rw [Subgroup.relIndex, h1, inf_comm] at h2
  exact h2

@[expose] def a1 : Equiv.Perm (Fin 6) :=
  ⟨![1, 0, 3, 2, 4, 5], ![1, 0, 3, 2, 4, 5], by decide, by decide⟩
@[expose] def b1 : Equiv.Perm (Fin 6) :=
  ⟨![2, 3, 0, 1, 4, 5], ![2, 3, 0, 1, 4, 5], by decide, by decide⟩
@[expose] def c45 : Equiv.Perm (Fin 6) :=
  ⟨![0, 1, 2, 3, 5, 4], ![0, 1, 2, 3, 5, 4], by decide, by decide⟩
@[expose] def s1 : Equiv.Perm (Fin 6) :=
  ⟨![1, 0, 2, 3, 5, 4], ![1, 0, 2, 3, 5, 4], by decide, by decide⟩
@[expose] def t1 : Equiv.Perm (Fin 6) :=
  ⟨![0, 2, 1, 3, 5, 4], ![0, 2, 1, 3, 5, 4], by decide, by decide⟩
@[expose] def x01 : Equiv.Perm (Fin 6) :=
  ⟨![1, 0, 2, 3, 4, 5], ![1, 0, 2, 3, 4, 5], by decide, by decide⟩
@[expose] def x23 : Equiv.Perm (Fin 6) :=
  ⟨![0, 1, 3, 2, 4, 5], ![0, 1, 3, 2, 4, 5], by decide, by decide⟩
@[expose] def w2 : Equiv.Perm (Fin 6) :=
  ⟨![0, 1, 4, 5, 2, 3], ![0, 1, 4, 5, 2, 3], by decide, by decide⟩

theorem a1_eq : a1 = Equiv.swap 0 1 * Equiv.swap 2 3 := by decide
theorem b1_eq : b1 = Equiv.swap 0 2 * Equiv.swap 1 3 := by decide
theorem c45_eq : c45 = Equiv.swap 4 5 := by decide
theorem s1_eq : s1 = Equiv.swap 0 1 * Equiv.swap 4 5 := by decide
theorem t1_eq : t1 = Equiv.swap 1 2 * Equiv.swap 4 5 := by decide
theorem x01_eq : x01 = Equiv.swap 0 1 := by decide
theorem w2_eq : w2 = Equiv.swap 2 4 * Equiv.swap 3 5 := by decide

theorem sign_c45 : Equiv.Perm.sign c45 = -1 := by
  rw [c45_eq, Equiv.Perm.sign_swap (by decide)]

theorem sign_pair {i j k l : Fin 6} (hij : i ≠ j) (hkl : k ≠ l) :
    Equiv.Perm.sign (Equiv.swap i j * Equiv.swap k l) = 1 := by
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij, Equiv.Perm.sign_swap hkl]
  rfl

theorem a1_mem_alt : a1 ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup, a1_eq]
  exact sign_pair (by decide) (by decide)

theorem b1_mem_alt : b1 ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup, b1_eq]
  exact sign_pair (by decide) (by decide)

theorem s1_mem_alt : s1 ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup, s1_eq]
  exact sign_pair (by decide) (by decide)

theorem t1_mem_alt : t1 ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup, t1_eq]
  exact sign_pair (by decide) (by decide)

theorem w2_mem_alt : w2 ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup, w2_eq]
  exact sign_pair (by decide) (by decide)

@[expose] def gensR1 : List (Equiv.Perm (Fin 6)) := [a1, b1, c45]

@[expose] def r1 : Subgroup (Equiv.Perm (Fin 6)) := Subgroup.closure {x | x ∈ gensR1}

@[expose] def elemsR1 : List (Equiv.Perm (Fin 6)) :=
  [1, a1, b1, c45, a1 * b1, a1 * c45, b1 * c45, a1 * b1 * c45]

@[expose] def codesR1 : List ℕ :=
  [44790, 44605, 44300, 38310, 44115, 38125, 37820, 37635]

@[expose] def gens1 : List (Equiv.Perm (Fin 6)) := [a1, b1, c45, s1, t1]

@[expose] def p1 : Subgroup (Equiv.Perm (Fin 6)) := Subgroup.closure {x | x ∈ gens1}

@[expose] def elemsK1 : List (Equiv.Perm (Fin 6)) := [1, s1, t1, s1 * t1, t1 * s1, s1 * t1 * s1]

@[expose] def elemsP1 : List (Equiv.Perm (Fin 6)) :=
  [⟨![0, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5], by decide, by decide⟩,
    ⟨![1, 0, 2, 3, 5, 4], ![1, 0, 2, 3, 5, 4], by decide, by decide⟩,
    ⟨![0, 2, 1, 3, 5, 4], ![0, 2, 1, 3, 5, 4], by decide, by decide⟩,
    ⟨![1, 2, 0, 3, 4, 5], ![2, 0, 1, 3, 4, 5], by decide, by decide⟩,
    ⟨![2, 0, 1, 3, 4, 5], ![1, 2, 0, 3, 4, 5], by decide, by decide⟩,
    ⟨![2, 1, 0, 3, 5, 4], ![2, 1, 0, 3, 5, 4], by decide, by decide⟩,
    ⟨![1, 0, 3, 2, 4, 5], ![1, 0, 3, 2, 4, 5], by decide, by decide⟩,
    ⟨![0, 1, 3, 2, 5, 4], ![0, 1, 3, 2, 5, 4], by decide, by decide⟩,
    ⟨![1, 3, 0, 2, 5, 4], ![2, 0, 3, 1, 5, 4], by decide, by decide⟩,
    ⟨![0, 3, 1, 2, 4, 5], ![0, 2, 3, 1, 4, 5], by decide, by decide⟩,
    ⟨![3, 1, 0, 2, 4, 5], ![2, 1, 3, 0, 4, 5], by decide, by decide⟩,
    ⟨![3, 0, 1, 2, 5, 4], ![1, 2, 3, 0, 5, 4], by decide, by decide⟩,
    ⟨![2, 3, 0, 1, 4, 5], ![2, 3, 0, 1, 4, 5], by decide, by decide⟩,
    ⟨![3, 2, 0, 1, 5, 4], ![2, 3, 1, 0, 5, 4], by decide, by decide⟩,
    ⟨![2, 0, 3, 1, 5, 4], ![1, 3, 0, 2, 5, 4], by decide, by decide⟩,
    ⟨![3, 0, 2, 1, 4, 5], ![1, 3, 2, 0, 4, 5], by decide, by decide⟩,
    ⟨![0, 2, 3, 1, 4, 5], ![0, 3, 1, 2, 4, 5], by decide, by decide⟩,
    ⟨![0, 3, 2, 1, 5, 4], ![0, 3, 2, 1, 5, 4], by decide, by decide⟩,
    ⟨![0, 1, 2, 3, 5, 4], ![0, 1, 2, 3, 5, 4], by decide, by decide⟩,
    ⟨![1, 0, 2, 3, 4, 5], ![1, 0, 2, 3, 4, 5], by decide, by decide⟩,
    ⟨![0, 2, 1, 3, 4, 5], ![0, 2, 1, 3, 4, 5], by decide, by decide⟩,
    ⟨![1, 2, 0, 3, 5, 4], ![2, 0, 1, 3, 5, 4], by decide, by decide⟩,
    ⟨![2, 0, 1, 3, 5, 4], ![1, 2, 0, 3, 5, 4], by decide, by decide⟩,
    ⟨![2, 1, 0, 3, 4, 5], ![2, 1, 0, 3, 4, 5], by decide, by decide⟩,
    ⟨![3, 2, 1, 0, 4, 5], ![3, 2, 1, 0, 4, 5], by decide, by decide⟩,
    ⟨![2, 3, 1, 0, 5, 4], ![3, 2, 0, 1, 5, 4], by decide, by decide⟩,
    ⟨![3, 1, 2, 0, 5, 4], ![3, 1, 2, 0, 5, 4], by decide, by decide⟩,
    ⟨![2, 1, 3, 0, 4, 5], ![3, 1, 0, 2, 4, 5], by decide, by decide⟩,
    ⟨![1, 3, 2, 0, 4, 5], ![3, 0, 2, 1, 4, 5], by decide, by decide⟩,
    ⟨![1, 2, 3, 0, 5, 4], ![3, 0, 1, 2, 5, 4], by decide, by decide⟩,
    ⟨![1, 0, 3, 2, 5, 4], ![1, 0, 3, 2, 5, 4], by decide, by decide⟩,
    ⟨![0, 1, 3, 2, 4, 5], ![0, 1, 3, 2, 4, 5], by decide, by decide⟩,
    ⟨![1, 3, 0, 2, 4, 5], ![2, 0, 3, 1, 4, 5], by decide, by decide⟩,
    ⟨![0, 3, 1, 2, 5, 4], ![0, 2, 3, 1, 5, 4], by decide, by decide⟩,
    ⟨![3, 1, 0, 2, 5, 4], ![2, 1, 3, 0, 5, 4], by decide, by decide⟩,
    ⟨![3, 0, 1, 2, 4, 5], ![1, 2, 3, 0, 4, 5], by decide, by decide⟩,
    ⟨![2, 3, 0, 1, 5, 4], ![2, 3, 0, 1, 5, 4], by decide, by decide⟩,
    ⟨![3, 2, 0, 1, 4, 5], ![2, 3, 1, 0, 4, 5], by decide, by decide⟩,
    ⟨![2, 0, 3, 1, 4, 5], ![1, 3, 0, 2, 4, 5], by decide, by decide⟩,
    ⟨![3, 0, 2, 1, 5, 4], ![1, 3, 2, 0, 5, 4], by decide, by decide⟩,
    ⟨![0, 2, 3, 1, 5, 4], ![0, 3, 1, 2, 5, 4], by decide, by decide⟩,
    ⟨![0, 3, 2, 1, 4, 5], ![0, 3, 2, 1, 4, 5], by decide, by decide⟩,
    ⟨![3, 2, 1, 0, 5, 4], ![3, 2, 1, 0, 5, 4], by decide, by decide⟩,
    ⟨![2, 3, 1, 0, 4, 5], ![3, 2, 0, 1, 4, 5], by decide, by decide⟩,
    ⟨![3, 1, 2, 0, 4, 5], ![3, 1, 2, 0, 4, 5], by decide, by decide⟩,
    ⟨![2, 1, 3, 0, 5, 4], ![3, 1, 0, 2, 5, 4], by decide, by decide⟩,
    ⟨![1, 3, 2, 0, 5, 4], ![3, 0, 2, 1, 5, 4], by decide, by decide⟩,
    ⟨![1, 2, 3, 0, 4, 5], ![3, 0, 1, 2, 4, 5], by decide, by decide⟩]

@[expose] def codesP1 : List ℕ :=
  [44790, 38305, 38280, 44725, 44750, 38240, 44605, 38130, 38035, 44550, 44505, 38055, 44300,
    37815, 37910, 44355, 44400, 37890, 38310, 44785, 44760, 38245, 38270, 44720, 44115, 37640,
    37665, 44180, 44155, 37705, 38125, 44610, 44515, 38070, 38025, 44535, 37820, 44295, 44390,
    37875, 37920, 44370, 37635, 44120, 44145, 37700, 37675, 44185]

theorem codes_R1 : elemsR1.map code = codesR1 := by decide +kernel
theorem nodup_R1 : codesR1.Nodup := by decide
theorem invol_R1 : ∀ s ∈ gensR1, s * s = 1 :=
  CFSG.Permutation.FinPack.sq_of_KL Par32Pack.h16 _ Par32Pack.cGR1 _ (by decide +kernel)
    Par32Pack.enc_one (by decide +kernel)
theorem rmul_R1 : ∀ x ∈ elemsR1, ∀ s ∈ gensR1, code (x * s) ∈ codesR1 := by
  intro x hx s hs
  rw [← codes_R1]
  exact List.mem_map.2 ⟨_, CFSG.Permutation.FinPack.mul_mem_of_K Par32Pack.h16 _ _ Par32Pack.cR1
    Par32Pack.cGR1 (by decide +kernel) (by decide +kernel) (by decide +kernel) x hx s hs, rfl⟩
theorem sq_R1 : ∀ x ∈ elemsR1, x * x = 1 :=
  CFSG.Permutation.FinPack.sq_of_KL Par32Pack.h16 _ Par32Pack.cR1 _ (by decide +kernel)
    Par32Pack.enc_one (by decide +kernel)
theorem elemsP1_eq : elemsP1 = elemsR1.flatMap fun r => elemsK1.map (r * ·) := by
  decide +kernel
theorem codes_P1 : elemsP1.map code = codesP1 := by decide +kernel
theorem nodup_P1 : codesP1.Nodup := by decide
theorem invol_1 : ∀ s ∈ gens1, s * s = 1 :=
  CFSG.Permutation.FinPack.sq_of_KL Par32Pack.h16 _ Par32Pack.cG1 _ (by decide +kernel)
    Par32Pack.enc_one (by decide +kernel)
theorem rmul_P1 : ∀ x ∈ elemsP1, ∀ s ∈ gens1, code (x * s) ∈ codesP1 := by
  intro x hx s hs
  rw [← codes_P1]
  exact List.mem_map.2 ⟨_, CFSG.Permutation.FinPack.mul_mem_of_K Par32Pack.h16 _ _ Par32Pack.cP1
    Par32Pack.cG1 (by decide +kernel) (by decide +kernel) (by decide +kernel) x hx s hs, rfl⟩
theorem conj_R1 : ∀ g ∈ gens1, ∀ r ∈ elemsR1, code (g * r * g) ∈ codesR1 := by
  intro g hg r hr
  rw [← codes_R1]
  exact List.mem_map.2 ⟨_, CFSG.Permutation.FinPack.conj_mem_of_K Par32Pack.h16 _ _ Par32Pack.cG1
    Par32Pack.cR1 (by decide +kernel) (by decide +kernel) (by decide +kernel) g hg r hr, rfl⟩

theorem mem_r1_iff (x : Equiv.Perm (Fin 6)) : x ∈ r1 ↔ x ∈ elemsR1 := by
  constructor
  · refine closure_subset invol_R1 (by simp [elemsR1]) (fun y hy s hs => ?_) x
    exact mem_of_code_mem (by rw [codes_R1]; exact rmul_R1 y hy s hs)
  · intro hx
    have ha : a1 ∈ r1 := Subgroup.subset_closure (by simp [gensR1])
    have hb : b1 ∈ r1 := Subgroup.subset_closure (by simp [gensR1])
    have hc : c45 ∈ r1 := Subgroup.subset_closure (by simp [gensR1])
    simp only [elemsR1, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [r1.one_mem, ha, hb, hc, r1.mul_mem ha hb, r1.mul_mem ha hc, r1.mul_mem hb hc,
      r1.mul_mem (r1.mul_mem ha hb) hc]

theorem r1_le_p1 : r1 ≤ p1 :=
  Subgroup.closure_mono fun x hx => by
    change x ∈ gensR1 at hx
    change x ∈ gens1
    simp only [gensR1, gens1, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    tauto

theorem s1_mem_p1 : s1 ∈ p1 := Subgroup.subset_closure (by simp [gens1])

theorem t1_mem_p1 : t1 ∈ p1 := Subgroup.subset_closure (by simp [gens1])

theorem mem_p1_iff (x : Equiv.Perm (Fin 6)) : x ∈ p1 ↔ x ∈ elemsP1 := by
  constructor
  · refine closure_subset invol_1 (by decide +kernel) (fun y hy s hs => ?_) x
    exact mem_of_code_mem (by rw [codes_P1]; exact rmul_P1 y hy s hs)
  · intro hx
    rw [elemsP1_eq] at hx
    obtain ⟨r, hr, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    refine p1.mul_mem (r1_le_p1 ((mem_r1_iff r).mpr hr)) ?_
    simp only [elemsK1, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [p1.one_mem, s1_mem_p1, t1_mem_p1, p1.mul_mem s1_mem_p1 t1_mem_p1,
      p1.mul_mem t1_mem_p1 s1_mem_p1, p1.mul_mem (p1.mul_mem s1_mem_p1 t1_mem_p1) s1_mem_p1]

theorem card_r1 : Nat.card r1 = 8 := by
  rw [card_eq_length (by rw [codes_R1]; exact nodup_R1) mem_r1_iff]
  rfl

theorem card_p1 : Nat.card p1 = 48 := by
  rw [card_eq_length (by rw [codes_P1]; exact nodup_P1) mem_p1_iff]
  rfl

theorem sq_eq_one_of_mem_r1 {x : Equiv.Perm (Fin 6)} (hx : x ∈ r1) : x * x = 1 :=
  sq_R1 x ((mem_r1_iff x).mp hx)

theorem p1_le_normalizer : p1 ≤ Subgroup.normalizer (r1 : Set (Equiv.Perm (Fin 6))) := by
  have key : ∀ g ∈ gens1, ∀ r ∈ r1, g * r * g ∈ r1 := by
    intro g hg r hr
    have h1 := conj_R1 g hg r ((mem_r1_iff r).mp hr)
    rw [← codes_R1] at h1
    exact (mem_r1_iff _).mpr (mem_of_code_mem h1)
  rw [p1, Subgroup.closure_le]
  intro g hg
  have hg2 : g⁻¹ = g := inv_eq_of_mul_eq_one_right (invol_1 g hg)
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  intro r
  rw [hg2]
  refine ⟨key g hg r, fun h => ?_⟩
  have := key g hg _ h
  rwa [show g * (g * r * g) * g = (g * g) * r * (g * g) by group, invol_1 g hg, one_mul,
    mul_one] at this

theorem sylowS6_le_p1 : sylowS6 ≤ p1 := by
  rw [sylowS6, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · rw [show Equiv.swap (0 : Fin 6) 1 = s1 * c45 by decide]
    exact p1.mul_mem s1_mem_p1 (r1_le_p1 (Subgroup.subset_closure (by simp [gensR1])))
  · rw [← b1_eq]
    exact r1_le_p1 (Subgroup.subset_closure (by simp [gensR1]))
  · rw [← c45_eq]
    exact r1_le_p1 (Subgroup.subset_closure (by simp [gensR1]))

theorem c45_mem_r1 : c45 ∈ r1 := Subgroup.subset_closure (by simp [gensR1])

theorem a1_mem_r1 : a1 ∈ r1 := Subgroup.subset_closure (by simp [gensR1])

theorem comm_not_mem_r1 : (t1 * s1)⁻¹ * (s1 * t1) ∉ r1 := by
  rw [mem_r1_iff]
  decide +kernel

@[expose] def gensR2 : List (Equiv.Perm (Fin 6)) := [x01, x23, c45]

@[expose] def r2 : Subgroup (Equiv.Perm (Fin 6)) := Subgroup.closure {x | x ∈ gensR2}

@[expose] def elemsR2 : List (Equiv.Perm (Fin 6)) :=
  [1, x01, x23, c45, x01 * x23, x01 * c45, x23 * c45, x01 * x23 * c45]

@[expose] def codesR2 : List ℕ :=
  [44790, 44785, 44610, 38310, 44605, 38305, 38130, 38125]

@[expose] def gens2 : List (Equiv.Perm (Fin 6)) := [x01, x23, c45, b1, w2]

@[expose] def p2 : Subgroup (Equiv.Perm (Fin 6)) := Subgroup.closure {x | x ∈ gens2}

@[expose] def elemsK2 : List (Equiv.Perm (Fin 6)) := [1, b1, w2, b1 * w2, w2 * b1, b1 * w2 * b1]

@[expose] def elemsP2 : List (Equiv.Perm (Fin 6)) :=
  [⟨![0, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5], by decide, by decide⟩,
    ⟨![2, 3, 0, 1, 4, 5], ![2, 3, 0, 1, 4, 5], by decide, by decide⟩,
    ⟨![0, 1, 4, 5, 2, 3], ![0, 1, 4, 5, 2, 3], by decide, by decide⟩,
    ⟨![2, 3, 4, 5, 0, 1], ![4, 5, 0, 1, 2, 3], by decide, by decide⟩,
    ⟨![4, 5, 0, 1, 2, 3], ![2, 3, 4, 5, 0, 1], by decide, by decide⟩,
    ⟨![4, 5, 2, 3, 0, 1], ![4, 5, 2, 3, 0, 1], by decide, by decide⟩,
    ⟨![1, 0, 2, 3, 4, 5], ![1, 0, 2, 3, 4, 5], by decide, by decide⟩,
    ⟨![2, 3, 1, 0, 4, 5], ![3, 2, 0, 1, 4, 5], by decide, by decide⟩,
    ⟨![1, 0, 4, 5, 2, 3], ![1, 0, 4, 5, 2, 3], by decide, by decide⟩,
    ⟨![2, 3, 4, 5, 1, 0], ![5, 4, 0, 1, 2, 3], by decide, by decide⟩,
    ⟨![4, 5, 1, 0, 2, 3], ![3, 2, 4, 5, 0, 1], by decide, by decide⟩,
    ⟨![4, 5, 2, 3, 1, 0], ![5, 4, 2, 3, 0, 1], by decide, by decide⟩,
    ⟨![0, 1, 3, 2, 4, 5], ![0, 1, 3, 2, 4, 5], by decide, by decide⟩,
    ⟨![3, 2, 0, 1, 4, 5], ![2, 3, 1, 0, 4, 5], by decide, by decide⟩,
    ⟨![0, 1, 4, 5, 3, 2], ![0, 1, 5, 4, 2, 3], by decide, by decide⟩,
    ⟨![3, 2, 4, 5, 0, 1], ![4, 5, 1, 0, 2, 3], by decide, by decide⟩,
    ⟨![4, 5, 0, 1, 3, 2], ![2, 3, 5, 4, 0, 1], by decide, by decide⟩,
    ⟨![4, 5, 3, 2, 0, 1], ![4, 5, 3, 2, 0, 1], by decide, by decide⟩,
    ⟨![0, 1, 2, 3, 5, 4], ![0, 1, 2, 3, 5, 4], by decide, by decide⟩,
    ⟨![2, 3, 0, 1, 5, 4], ![2, 3, 0, 1, 5, 4], by decide, by decide⟩,
    ⟨![0, 1, 5, 4, 2, 3], ![0, 1, 4, 5, 3, 2], by decide, by decide⟩,
    ⟨![2, 3, 5, 4, 0, 1], ![4, 5, 0, 1, 3, 2], by decide, by decide⟩,
    ⟨![5, 4, 0, 1, 2, 3], ![2, 3, 4, 5, 1, 0], by decide, by decide⟩,
    ⟨![5, 4, 2, 3, 0, 1], ![4, 5, 2, 3, 1, 0], by decide, by decide⟩,
    ⟨![1, 0, 3, 2, 4, 5], ![1, 0, 3, 2, 4, 5], by decide, by decide⟩,
    ⟨![3, 2, 1, 0, 4, 5], ![3, 2, 1, 0, 4, 5], by decide, by decide⟩,
    ⟨![1, 0, 4, 5, 3, 2], ![1, 0, 5, 4, 2, 3], by decide, by decide⟩,
    ⟨![3, 2, 4, 5, 1, 0], ![5, 4, 1, 0, 2, 3], by decide, by decide⟩,
    ⟨![4, 5, 1, 0, 3, 2], ![3, 2, 5, 4, 0, 1], by decide, by decide⟩,
    ⟨![4, 5, 3, 2, 1, 0], ![5, 4, 3, 2, 0, 1], by decide, by decide⟩,
    ⟨![1, 0, 2, 3, 5, 4], ![1, 0, 2, 3, 5, 4], by decide, by decide⟩,
    ⟨![2, 3, 1, 0, 5, 4], ![3, 2, 0, 1, 5, 4], by decide, by decide⟩,
    ⟨![1, 0, 5, 4, 2, 3], ![1, 0, 4, 5, 3, 2], by decide, by decide⟩,
    ⟨![2, 3, 5, 4, 1, 0], ![5, 4, 0, 1, 3, 2], by decide, by decide⟩,
    ⟨![5, 4, 1, 0, 2, 3], ![3, 2, 4, 5, 1, 0], by decide, by decide⟩,
    ⟨![5, 4, 2, 3, 1, 0], ![5, 4, 2, 3, 1, 0], by decide, by decide⟩,
    ⟨![0, 1, 3, 2, 5, 4], ![0, 1, 3, 2, 5, 4], by decide, by decide⟩,
    ⟨![3, 2, 0, 1, 5, 4], ![2, 3, 1, 0, 5, 4], by decide, by decide⟩,
    ⟨![0, 1, 5, 4, 3, 2], ![0, 1, 5, 4, 3, 2], by decide, by decide⟩,
    ⟨![3, 2, 5, 4, 0, 1], ![4, 5, 1, 0, 3, 2], by decide, by decide⟩,
    ⟨![5, 4, 0, 1, 3, 2], ![2, 3, 5, 4, 1, 0], by decide, by decide⟩,
    ⟨![5, 4, 3, 2, 0, 1], ![4, 5, 3, 2, 1, 0], by decide, by decide⟩,
    ⟨![1, 0, 3, 2, 5, 4], ![1, 0, 3, 2, 5, 4], by decide, by decide⟩,
    ⟨![3, 2, 1, 0, 5, 4], ![3, 2, 1, 0, 5, 4], by decide, by decide⟩,
    ⟨![1, 0, 5, 4, 3, 2], ![1, 0, 5, 4, 3, 2], by decide, by decide⟩,
    ⟨![3, 2, 5, 4, 1, 0], ![5, 4, 1, 0, 3, 2], by decide, by decide⟩,
    ⟨![5, 4, 1, 0, 3, 2], ![3, 2, 5, 4, 1, 0], by decide, by decide⟩,
    ⟨![5, 4, 3, 2, 1, 0], ![5, 4, 3, 2, 1, 0], by decide, by decide⟩]

@[expose] def codesP2 : List ℕ :=
  [44790, 44300, 27150, 9020, 26170, 8530, 44785, 44120, 27145, 2540, 25990, 2050, 44610, 44295,
    20670, 9015, 19690, 8350, 38310, 37820, 26970, 8840, 26165, 8525, 44605, 44115, 20665, 2535,
    19510, 1870, 38305, 37640, 26965, 2360, 25985, 2045, 38130, 37815, 20490, 8835, 19685, 8345,
    38125, 37635, 20485, 2355, 19505, 1865]

theorem codes_R2 : elemsR2.map code = codesR2 := by decide +kernel
theorem nodup_R2 : codesR2.Nodup := by decide
theorem invol_R2 : ∀ s ∈ gensR2, s * s = 1 :=
  CFSG.Permutation.FinPack.sq_of_KL Par32Pack.h16 _ Par32Pack.cGR2 _ (by decide +kernel)
    Par32Pack.enc_one (by decide +kernel)
theorem rmul_R2 : ∀ x ∈ elemsR2, ∀ s ∈ gensR2, code (x * s) ∈ codesR2 := by
  intro x hx s hs
  rw [← codes_R2]
  exact List.mem_map.2 ⟨_, CFSG.Permutation.FinPack.mul_mem_of_K Par32Pack.h16 _ _ Par32Pack.cR2
    Par32Pack.cGR2 (by decide +kernel) (by decide +kernel) (by decide +kernel) x hx s hs, rfl⟩
theorem sq_R2 : ∀ x ∈ elemsR2, x * x = 1 :=
  CFSG.Permutation.FinPack.sq_of_KL Par32Pack.h16 _ Par32Pack.cR2 _ (by decide +kernel)
    Par32Pack.enc_one (by decide +kernel)
theorem elemsP2_eq : elemsP2 = elemsR2.flatMap fun r => elemsK2.map (r * ·) := by
  decide +kernel
theorem codes_P2 : elemsP2.map code = codesP2 := by decide +kernel
theorem nodup_P2 : codesP2.Nodup := by decide
theorem invol_2 : ∀ s ∈ gens2, s * s = 1 :=
  CFSG.Permutation.FinPack.sq_of_KL Par32Pack.h16 _ Par32Pack.cG2 _ (by decide +kernel)
    Par32Pack.enc_one (by decide +kernel)
theorem rmul_P2 : ∀ x ∈ elemsP2, ∀ s ∈ gens2, code (x * s) ∈ codesP2 := by
  intro x hx s hs
  rw [← codes_P2]
  exact List.mem_map.2 ⟨_, CFSG.Permutation.FinPack.mul_mem_of_K Par32Pack.h16 _ _ Par32Pack.cP2
    Par32Pack.cG2 (by decide +kernel) (by decide +kernel) (by decide +kernel) x hx s hs, rfl⟩
theorem conj_R2 : ∀ g ∈ gens2, ∀ r ∈ elemsR2, code (g * r * g) ∈ codesR2 := by
  intro g hg r hr
  rw [← codes_R2]
  exact List.mem_map.2 ⟨_, CFSG.Permutation.FinPack.conj_mem_of_K Par32Pack.h16 _ _ Par32Pack.cG2
    Par32Pack.cR2 (by decide +kernel) (by decide +kernel) (by decide +kernel) g hg r hr, rfl⟩

theorem mem_r2_iff (x : Equiv.Perm (Fin 6)) : x ∈ r2 ↔ x ∈ elemsR2 := by
  constructor
  · refine closure_subset invol_R2 (by simp [elemsR2]) (fun y hy s hs => ?_) x
    exact mem_of_code_mem (by rw [codes_R2]; exact rmul_R2 y hy s hs)
  · intro hx
    have ha : x01 ∈ r2 := Subgroup.subset_closure (by simp [gensR2])
    have hb : x23 ∈ r2 := Subgroup.subset_closure (by simp [gensR2])
    have hc : c45 ∈ r2 := Subgroup.subset_closure (by simp [gensR2])
    simp only [elemsR2, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [r2.one_mem, ha, hb, hc, r2.mul_mem ha hb, r2.mul_mem ha hc, r2.mul_mem hb hc,
      r2.mul_mem (r2.mul_mem ha hb) hc]

theorem r2_le_p2 : r2 ≤ p2 :=
  Subgroup.closure_mono fun x hx => by
    change x ∈ gensR2 at hx
    change x ∈ gens2
    simp only [gensR2, gens2, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    tauto

theorem b1_mem_p2 : b1 ∈ p2 := Subgroup.subset_closure (by simp [gens2])

theorem w2_mem_p2 : w2 ∈ p2 := Subgroup.subset_closure (by simp [gens2])

theorem mem_p2_iff (x : Equiv.Perm (Fin 6)) : x ∈ p2 ↔ x ∈ elemsP2 := by
  constructor
  · refine closure_subset invol_2 (by decide +kernel) (fun y hy s hs => ?_) x
    exact mem_of_code_mem (by rw [codes_P2]; exact rmul_P2 y hy s hs)
  · intro hx
    rw [elemsP2_eq] at hx
    obtain ⟨r, hr, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    refine p2.mul_mem (r2_le_p2 ((mem_r2_iff r).mpr hr)) ?_
    simp only [elemsK2, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [p2.one_mem, b1_mem_p2, w2_mem_p2, p2.mul_mem b1_mem_p2 w2_mem_p2,
      p2.mul_mem w2_mem_p2 b1_mem_p2, p2.mul_mem (p2.mul_mem b1_mem_p2 w2_mem_p2) b1_mem_p2]

theorem card_r2 : Nat.card r2 = 8 := by
  rw [card_eq_length (by rw [codes_R2]; exact nodup_R2) mem_r2_iff]
  rfl

theorem card_p2 : Nat.card p2 = 48 := by
  rw [card_eq_length (by rw [codes_P2]; exact nodup_P2) mem_p2_iff]
  rfl

theorem sq_eq_one_of_mem_r2 {x : Equiv.Perm (Fin 6)} (hx : x ∈ r2) : x * x = 1 :=
  sq_R2 x ((mem_r2_iff x).mp hx)

theorem p2_le_normalizer : p2 ≤ Subgroup.normalizer (r2 : Set (Equiv.Perm (Fin 6))) := by
  have key : ∀ g ∈ gens2, ∀ r ∈ r2, g * r * g ∈ r2 := by
    intro g hg r hr
    have h1 := conj_R2 g hg r ((mem_r2_iff r).mp hr)
    rw [← codes_R2] at h1
    exact (mem_r2_iff _).mpr (mem_of_code_mem h1)
  rw [p2, Subgroup.closure_le]
  intro g hg
  have hg2 : g⁻¹ = g := inv_eq_of_mul_eq_one_right (invol_2 g hg)
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  intro r
  rw [hg2]
  refine ⟨key g hg r, fun h => ?_⟩
  have := key g hg _ h
  rwa [show g * (g * r * g) * g = (g * g) * r * (g * g) by group, invol_2 g hg, one_mul,
    mul_one] at this

theorem sylowS6_le_p2 : sylowS6 ≤ p2 := by
  rw [sylowS6, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · rw [← x01_eq]
    exact r2_le_p2 (Subgroup.subset_closure (by simp [gensR2]))
  · rw [← b1_eq]
    exact b1_mem_p2
  · rw [← c45_eq]
    exact r2_le_p2 (Subgroup.subset_closure (by simp [gensR2]))

theorem c45_mem_r2 : c45 ∈ r2 := Subgroup.subset_closure (by simp [gensR2])

theorem comm_not_mem_r2 : (w2 * b1)⁻¹ * (b1 * w2) ∉ r2 := by
  rw [mem_r2_iff]
  decide +kernel

theorem inter_check : ∀ x ∈ elemsR1, x ∈ elemsR2 → x ∈ S6Syl.elemsA :=
  CFSG.Permutation.FinPack.inter_of_K Par32Pack.h16 _ _ _ Par32Pack.cR1 Par32Pack.cR2
    Par32Pack.cA (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem inter_check' : ∀ x ∈ S6Syl.elemsA, x ∈ elemsR1 ∧ x ∈ elemsR2 := by
  have hA : (S6Syl.elemsA.map CFSG.Permutation.FinPack.enc == Par32Pack.cA) = true := by
    decide +kernel
  intro x hx
  exact ⟨CFSG.Permutation.FinPack.sub_of_KL Par32Pack.h16 _ _ Par32Pack.cA Par32Pack.cR1 hA
      (by decide +kernel) (by decide +kernel) x hx,
    CFSG.Permutation.FinPack.sub_of_KL Par32Pack.h16 _ _ Par32Pack.cA Par32Pack.cR2 hA
      (by decide +kernel) (by decide +kernel) x hx⟩

theorem r1_inf_r2 : r1 ⊓ r2 = aBar2 := by
  ext x
  rw [Subgroup.mem_inf, mem_r1_iff, mem_r2_iff, S6Syl.aBar2_eq]
  exact ⟨fun h => inter_check x h.1 h.2, fun h => inter_check' x h⟩

theorem eq_of_mem_r1_inf_r2 {x : Equiv.Perm (Fin 6)} (hx : x ∈ r1 ⊓ r2)
    (hxA : x ∈ alternatingGroup (Fin 6)) : x = 1 ∨ x = a1 := by
  rw [r1_inf_r2, S6Syl.aBar2_eq] at hx
  rw [Equiv.Perm.mem_alternatingGroup] at hxA
  simp only [S6Syl.elemsA, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr a1_eq.symm
  · rw [Equiv.Perm.sign_swap (by decide)] at hxA
    exact absurd hxA (by decide)
  · rw [Equiv.Perm.sign_mul, sign_pair (by decide) (by decide), Equiv.Perm.sign_swap (by decide)]
      at hxA
    exact absurd hxA (by decide)

theorem card_fix_a1 : (Finset.univ.filter fun v : Vec4 => act a1 v = v).card = 4 := by
  decide +kernel

theorem eq_alternatingGroup_or_eq_top {H : Subgroup (Equiv.Perm (Fin 6))}
    (hH : alternatingGroup (Fin 6) ≤ H) : H = alternatingGroup (Fin 6) ∨ H = ⊤ := by
  have hdvd := Subgroup.index_dvd_of_le hH
  rw [alternatingGroup.index_eq_two] at hdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact Or.inr (Subgroup.index_eq_one.mp h1)
  · left
    have e1 := Subgroup.card_mul_index H
    have e2 := Subgroup.card_mul_index (alternatingGroup (Fin 6))
    rw [h2] at e1
    rw [alternatingGroup.index_eq_two] at e2
    exact (Subgroup.eq_of_le_of_card_ge hH (by omega)).symm

end CFSG.Quasithin.H13.Par32
