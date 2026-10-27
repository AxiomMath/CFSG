module

public import CFSG.Sporadic.Bridge.BRels9201
public import CFSG.Monster.B.Pinned.Primes.SeedGL
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.Sporadic.Bridge.B.R9201

open CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.Pinned CFSG.Monster.B.Primes.Native
  CFSG.KC.BM.B9201

@[expose] def isIv : Ins → Bool
  | .iv _ _ => true
  | _ => false

theorem bProg_noIv : (bProg.all fun ins => !isIv ins) = true := by decide

theorem map_insStep {G N : Type*} [Group G] [Monoid N] (f : G →* N) (ρ : ℕ → G) (ins : Ins)
    (h : isIv ins = false) :
    (fun i => f (insStepG ρ ins i)) = insStepM (fun i => f (ρ i)) ins := by
  funext i
  cases ins with
  | mu a b k =>
    simp only [insStepG, insStepM]
    by_cases e : i = k
    · subst e
      rw [Function.update_self, Function.update_self, map_mul]
    · rw [Function.update_of_ne e, Function.update_of_ne e]
  | iv a k => simp [isIv] at h
  | pwr e a k =>
    simp only [insStepG, insStepM]
    by_cases e' : i = k
    · subst e'
      rw [Function.update_self, Function.update_self, map_pow]
    · rw [Function.update_of_ne e', Function.update_of_ne e']

theorem map_foldl_insStep {G N : Type*} [Group G] [Monoid N] (f : G →* N) :
    ∀ (prog : List Ins), (prog.all fun ins => !isIv ins) = true → ∀ (ρ : ℕ → G) (r : ℕ),
      f (prog.foldl insStepG ρ r) = prog.foldl insStepM (fun i => f (ρ i)) r
  | [], _, _, _ => rfl
  | ins :: p, hp, ρ, r => by
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at hp
    rw [List.foldl_cons, List.foldl_cons, map_foldl_insStep f p hp.2, map_insStep f ρ ins hp.1]

theorem map_runG {G N : Type*} [Group G] [Monoid N] (f : G →* N) (prog : List Ins)
    (hp : (prog.all fun ins => !isIv ins) = true) (a b : G) (r : ℕ) :
    f (runG prog a b r) = runM prog (f a) (f b) r := by
  unfold runG runM
  rw [map_foldl_insStep f prog hp]
  have e : (fun i => f (progInit a b i)) = fun i => if i = 1 then f a else if i = 2 then f b else 1 := by
    funext i
    unfold progInit
    split_ifs <;> simp
  rw [e]

theorem bMat_runG (k : ℕ) :
    bMat (runG bProg bA₁ bA₂ (bTreg k)) = tM genA₁ genA₂ k :=
  map_runG bMat bProg bProg_noIv bA₁ bA₂ (bTreg k)

section Map

variable {G N : Type*} [Group G] [Monoid N] (f : G →* N) {T : ℕ → G} {t : ℕ → N}

theorem lp_map (he : ∀ k < 11, f (T k) = t k) (l : List ℕ) (hl : ∀ k ∈ l, k < 11) :
    f (CFSG.KC.BM.B9201.lp T l) = CFSG.KC.BM.B9201.lp t l := by
  rw [CFSG.KC.BM.B9201.lp, CFSG.KC.BM.B9201.lp, MonoidHom.map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun k hk => he k (hl k hk)

variable {f}

theorem relsT_map (hf : Function.Injective f) (he : ∀ k < 11, f (T k) = t k) (h : RelsT t) :
    RelsT T := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  have hr : f (rT T) = rT t := lp_map f he _ (by decide)
  have hrq : f (rqT T) = rqT t := lp_map f he _ (by decide)
  have e : ∀ k, k < 11 → f (T k) = t k := he
  refine ⟨hf ?_, hf ?_, fun j hj => hf ?_, fun i hi => hf ?_, fun i hi => hf ?_, hf ?_, hf ?_,
    hf ?_, hf ?_, hf ?_, hf ?_, hf ?_⟩
  · rw [map_mul, map_one, e 0 (by norm_num)]
    exact h1
  · rw [map_pow, map_mul, map_one, e 0 (by norm_num), e 1 (by norm_num)]
    exact h2
  · have hj' : j < 11 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
      omega
    rw [map_mul, map_mul, e 0 (by norm_num), e j hj']
    exact h3 j hj
  · rw [map_mul, map_mul, hr, e i (by omega), e (i + 1) (by omega)]
    exact h4 i hi
  · have hc : chain2.getD i 0 < 11 ∧ chain2.getD (i + 1) 0 < 11 := by
      interval_cases i <;> decide
    rw [map_mul, map_mul, hrq, e _ hc.1, e _ hc.2]
    exact h5 i hi
  · rw [map_mul, map_mul, e 5 (by norm_num), e 8 (by norm_num)]
    exact h6
  · simp only [map_mul]
    rw [e 5 (by norm_num), e 9 (by norm_num), e 10 (by norm_num)]
    exact h7
  · simp only [map_mul]
    rw [e 6 (by norm_num), e 7 (by norm_num), e 8 (by norm_num)]
    exact h8
  · simp only [map_mul]
    rw [e 6 (by norm_num), e 7 (by norm_num), e 9 (by norm_num), e 10 (by norm_num)]
    exact h9
  · rw [map_pow, map_one, lp_map f he _ (by decide)]
    exact h10
  · rw [map_pow, map_one, lp_map f he _ (by decide)]
    exact h11
  · rw [map_pow, map_one, lp_map f he _ (by decide)]
    exact h12

theorem hT_map (he : ∀ k < 11, f (T k) = t k) :
    f (CFSG.KC.BM.B9201.hT T) = CFSG.KC.BM.B9201.hT t := by
  rw [CFSG.KC.BM.B9201.hT, CFSG.KC.BM.B9201.hT, map_pow, map_mul, sT, sT, rT, rT,
    lp_map f he _ (by decide), lp_map f he _ (by decide)]

theorem apT_map (he : ∀ k < 11, f (T k) = t k) : f (apT T) = apT t := by
  rw [apT, apT, map_pow, map_mul, map_pow, sT, sT, rT, rT, lp_map f he _ (by decide),
    lp_map f he _ (by decide)]

end Map

theorem conj_units {M : Type*} [Monoid M] [IsDedekindFiniteMonoid M] {g₁ g₂ u w p : Mˣ}
    {G Gi : M} (hi : G * Gi = 1) (hb : (g₂ : M) * G = G * p) (ha : (g₁ : M) * (G * u) = G * u * w) :
    ∃ Gu : Mˣ, g₁ * Gu = Gu * w ∧ g₂ * Gu = Gu * (u⁻¹ * p * u) := by
  let G0 : Mˣ := ⟨G, Gi, hi, mul_eq_one_comm.1 hi⟩
  have e2 : g₂ * G0 = G0 * p := Units.ext hb
  refine ⟨G0 * u, Units.ext ?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, Units.val_mul]
    exact ha
  · rw [← mul_assoc, e2]
    group

theorem bridge_gen {T : ℕ → NativeSporadic.B}
    (hT' : ∀ k < 11, bMat (T k) = tM genA₁ genA₂ k) (h : B9201Facts genA₁ genA₂) :
    (∀ i < 11, T i * T i = 1) ∧ (∀ v ∈ pres.relatorLetters, wordProd T v = 1) ∧
      ∃ Gu : GL (Fin 4370) (ZMod 2), glA₁ * Gu = Gu * bGL (apT T) ∧
        glA₂ * Gu = Gu * bGL ((CFSG.KC.BM.B9201.hT T)⁻¹ * (T 0 * T 1) * CFSG.KC.BM.B9201.hT T) := by
  obtain ⟨t, ht, hR, G, Gi, hb, ha, hi⟩ := h
  have hTt : ∀ k < 11, bMat (T k) = t k := fun k hk => (hT' k hk).trans (ht k hk)
  have hRT : RelsT T := relsT_map bMat_injective hTt hR
  refine ⟨(cox_of_relsT hRT).1, rels_of_relsT hRT, ?_⟩
  rw [map_mul, map_mul, map_inv]
  refine conj_units hi ?_ ?_
  · rw [coe_bGL, map_mul, hTt 0 (by norm_num), hTt 1 (by norm_num)]
    exact hb
  · rw [coe_bGL, coe_bGL, hT_map hTt, apT_map hTt]
    exact ha

end CFSG.Sporadic.Bridge.B.R9201

end
