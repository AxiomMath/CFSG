
module

public import CFSG.LocalAnalysis.StandardType.L34SylowKFacts
public import Certificates.Data.Kernel.L34Syl.TabEq

public section

namespace CFSG.StandardType.L34Sylow

open CFSG.KC.L34Syl CFSG.KC.Enum CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open scoped Pointwise

theorem tabEqB_sound {t : Tab} {x : ℕ} (h : tabEqB t x = true) :
    t.size = 42 ∧ ∀ i < 42, t[i]! = pg 6 63 x i := by
  simp only [tabEqB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1, fun i hi => h.2 i hi⟩

theorem tabRep_pp {t : Tab} {x : ℕ} (hx : PermN 42 6 63 x) (h : tabEqB t x = true) :
    TabRep t (pp 42 6 63 x) := by
  obtain ⟨hs, he⟩ := tabEqB_sound h
  refine ⟨hs, fun i => ?_⟩
  rw [he i i.2]
  exact (CFSG.KS.PK.permOf_apply hx i).symm

theorem closureTabs_eq_closure {gens : Array Tab} {ng : ℕ} {F : ℕ → Equiv.Perm (Fin 42)}
    (hsz : gens.size = ng) (h : ∀ j < ng, TabRep gens[j]! (F j)) :
    closureTabs gens = Subgroup.closure {g | ∃ j < ng, F j = g} := by
  unfold closureTabs
  congr 1
  ext g
  constructor
  · rintro ⟨j, hj, hr⟩
    exact ⟨j, by omega, (h j (by omega)).perm_eq hr⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, by omega, h j hj⟩

theorem mem_gen {n w m : ℕ} {L : ℕ → ℕ} {ng j : ℕ} (hj : j < ng) :
    pp n w m (L (2 * j)) ∈ gen n w m L ng :=
  Subgroup.subset_closure ⟨j, hj, rfl⟩

theorem gen_le {n w m : ℕ} {L : ℕ → ℕ} {ng : ℕ} {H : Subgroup (Equiv.Perm (Fin n))}
    (h : ∀ j < ng, pp n w m (L (2 * j)) ∈ H) : gen n w m L ng ≤ H := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨j, hj, rfl⟩
  exact h j hj

theorem lane_lt {n om T k : ℕ} (hom : om = 2 ^ n - 1) : lane n om T k < 2 ^ n := by
  have e : lane n om T k = (T >>> (n * k)) &&& om := rfl
  rw [e, hom]
  exact Nat.and_lt_two_pow _ (by have := Nat.one_le_two_pow (n := n); omega)

theorem mset_inj {n s t : ℕ} (hs : s < 2 ^ n) (ht : t < 2 ^ n) (h : mset n s = mset n t) :
    s = t := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · have := congrArg (fun A : Set (Fin n) => (⟨i, hi⟩ : Fin n) ∈ A) h
    simp only [mset, Set.mem_setOf_eq, eq_iff_iff] at this
    exact Bool.eq_iff_iff.mpr this
  · have h2 : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

theorem pairwise_zpowers_ne {p : ℕ} {L : List ℕ} (hL : L.Pairwise (· < ·))
    (h : ∀ x ∈ L, PermN 42 6 63 x ∧ x < 2 ^ 252 ∧ CanonGen p (pp 42 6 63 x) ∧
      orderOf (pp 42 6 63 x) = p) :
    (L.map (pp 42 6 63)).Pairwise fun X Y => Subgroup.zpowers X ≠ Subgroup.zpowers Y := by
  rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem (fun {x y} hx hy hxy he => ?_) hL
  obtain ⟨hxP, hxl, hxc, hxo⟩ := h x hx
  obtain ⟨hyP, hyl, hyc, hyo⟩ := h y hy
  have e := canonGen_unique hxo hyo hxc hyc he
  have := pp_inj (by norm_num) (by rfl) hxP hyP hxl hyl e
  omega

theorem ne_one_of_canonGen {p : ℕ} {x : Equiv.Perm (Fin 42)} (h : CanonGen p x) : x ≠ 1 := by
  rintro rfl
  obtain ⟨a, -, ha, -⟩ := h
  exact ha rfl

theorem image_eq_of_mem_closure {α : Type*} {A : Set α} {X : Set (Equiv.Perm α)}
    (hX : ∀ g ∈ X, ⇑g '' A = A) {m : Equiv.Perm α} (hm : m ∈ Subgroup.closure X) :
    ⇑m '' A = A := by
  have hle : Subgroup.closure X ≤ MulAction.stabilizer (Equiv.Perm α) A :=
    (Subgroup.closure_le _).2 fun g hg => by
      rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
      exact hX g hg
  have := hle hm
  rw [MulAction.mem_stabilizer_iff] at this
  exact this

theorem image_trans {α : Type*} {R y z : Set α} {g₁ g₂ : Equiv.Perm α} (h₁ : ⇑g₁ '' R = y)
    (h₂ : ⇑g₂ '' R = z) : ⇑(g₂ * g₁⁻¹) '' y = z := by
  subst h₁ h₂
  rw [Set.image_image]
  congr 1
  funext a
  exact congrArg g₂ (g₁.symm_apply_apply a)

theorem aSixData_of_checks {S M : Subgroup (Equiv.Perm (Fin 42))} {LS LM SX HP H OM OD R CN ST SD : ℕ}
    {CW : List (List ℕ × List ℕ)}
    (hSg : S = gen 42 6 63 (lane 252 pm252 LS) 3) (hMg : M = gen 42 6 63 (lane 252 pm252 LM) 3)
    (hMS : M ≤ S)
    (hLSok : lettersOK 42 6 63 252 (lane 252 pm252 LS) 3 = true)
    (hLMok : lettersOK 42 6 63 252 (lane 252 pm252 LM) 3 = true)
    (horb : orbK 42 6 63 4398046511103 (lane 252 pm252 LS) 3 H OM OD 56 = true)
    (hsub : subK 42 6 63 4398046511103 (lane 252 pm252 LM) 3 R CN H OM OD 56 = true)
    (hres : restrK 42 6 63 (lane 252 pm252 LM) (lane 18 262143 SX) HP H = true)
    (hsx : lettersOK 6 3 7 18 (lane 18 262143 SX) 3 = true)
    (hst : grpK 6 3 7 18 262143 9 511 (lane 18 262143 SX) 3 ST SD 360 = true)
    (hcw : commsK 42 6 63 6 (lane 252 pm252 LM) (fun i => lane 252 pm252 LM (Nat.mul 2 i)) CW 0 =
      true) (hcwl : CW.length = 3)
    (hH0 : H = hOf 42 4398046511103 OM R)
    (hCN0 : CN % 256 = 1 ∧ (((CN / 256) % 256 = 10 ∧ (CN / 65536) % 256 = 45) ∨
      ((CN / 256) % 256 = 45 ∧ (CN / 65536) % 256 = 10))) :
    ASixData S M := by
  have hom : (4398046511103 : ℕ) = 2 ^ 42 - 1 := by norm_num
  have hH : H = lane 42 4398046511103 OM ((R / 2 ^ (6 * 0)) % 64) := by
    rw [hH0, hOf, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
    congr 1
    have e : (R >>> 0) &&& 63 = R % 64 := by
      rw [Nat.shiftRight_zero, show (63 : ℕ) = 2 ^ 6 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    exact e
  have hCN : (CN / 2 ^ (8 * 0)) % 256 = 1 ∧ (((CN / 2 ^ (8 * 1)) % 256 = 10 ∧
      (CN / 2 ^ (8 * 2)) % 256 = 45) ∨ ((CN / 2 ^ (8 * 1)) % 256 = 45 ∧
      (CN / 2 ^ (8 * 2)) % 256 = 10)) := by
    norm_num
    exact hCN0
  have hLS := lettersOK_sound hLSok
  have hLM := lettersOK_sound hLMok
  obtain ⟨hOimg, hOcov, hOinc⟩ := orbK_sound hom (by norm_num) (fun j hj => (hLS j hj).1) horb
  obtain ⟨hfixH, hlab, hcnt⟩ := subK_sound hom (fun j hj => (hLM j hj).1) hsub
  obtain ⟨hHP1, hHP2, hHP3, hHP4⟩ := restrK_sound (fun j hj => (hLM j hj).1) hres
  have hSX := lettersOK_sound hsx
  obtain ⟨-, hSTinj, hSTmem⟩ := grpK_sound (by norm_num) (by norm_num) (by norm_num) hSX hst
  have hcomm := commsK_sound hLM hcw
  rw [← hSg] at hOimg hOcov
  rw [← hMg] at hlab
  set mk : ℕ → Set (Fin 42) := fun k => mset 42 (lane 42 4398046511103 OM k) with hmk
  have hmk_inj : ∀ k < 56, ∀ k' < 56, mk k = mk k' → k = k' := by
    intro k hk k' hk' h
    have := mset_inj (lane_lt hom) (lane_lt hom) h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact absurd this (Nat.ne_of_lt (hOinc k hk k' hk' hlt))
    · exact absurd this (Nat.ne_of_gt (hOinc k' hk' k hk hlt))
  let o : Fin 6 → Fin 42 := fun a => ⟨pg 6 63 HP a, hHP1 a a.2⟩
  have ho : Function.Injective o := fun a b h =>
    Fin.ext (hHP2 a a.2 b b.2 (congrArg Fin.val h))
  have hrange : Set.range o = mset 42 H := by
    ext i
    rw [hHP3 i]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, rfl⟩
    · rintro ⟨a, ha, he⟩
      exact ⟨⟨a, ha⟩, Fin.ext he⟩
  have hMH : ∀ m ∈ M, ⇑m '' Set.range o = Set.range o := by
    intro m hm
    rw [hrange]
    rw [hMg] at hm
    exact image_eq_of_mem_closure (by rintro _ ⟨j, hj, rfl⟩; exact hfixH j hj) hm
  set Q := gen 6 3 7 (lane 18 262143 SX) 3 with hQ
  have hQcard : Nat.card Q = 360 := card_gen_eq hSTinj hSTmem
  let Rl : Subgroup (Equiv.Perm (Fin 6)) :=
    { carrier := {τ | ∃ m ∈ M, ∀ i, m (o i) = o (τ i)}
      mul_mem' := by
        rintro τ σ ⟨m, hm, hmτ⟩ ⟨m', hm', hm'σ⟩
        exact ⟨m * m', mul_mem hm hm', fun i => by
          rw [Equiv.Perm.mul_apply, hm'σ, hmτ, Equiv.Perm.mul_apply]⟩
      one_mem' := ⟨1, one_mem _, fun i => rfl⟩
      inv_mem' := by
        rintro τ ⟨m, hm, hmτ⟩
        refine ⟨m⁻¹, inv_mem hm, fun i => ?_⟩
        have h := hmτ (τ⁻¹ i)
        rw [show τ (τ⁻¹ i) = i from τ.apply_symm_apply i] at h
        rw [← h]
        exact m.symm_apply_apply _ }
  have hQR : Q ≤ Rl := by
    refine gen_le fun j hj => ⟨pp 42 6 63 (lane 252 pm252 LM (2 * j)), ?_, fun i => ?_⟩
    · rw [hMg]
      exact mem_gen hj
    · apply Fin.ext
      have h1 := hHP4 j hj i i.2 (o i) rfl
      rw [h1]
      have h2 := CFSG.KS.PK.permOf_apply (hSX j hj).1 i
      change pg 6 63 HP (pg 3 7 (lane 18 262143 SX (2 * j)) i) =
        pg 6 63 HP ((pp 6 3 7 (lane 18 262143 SX (2 * j)) i : Fin 6) : ℕ)
      rw [show ((pp 6 3 7 (lane 18 262143 SX (2 * j)) i : Fin 6) : ℕ) =
        pg 3 7 (lane 18 262143 SX (2 * j)) i from h2]
  set lab : ℕ → ℕ := subLab OD with hlabd
  let B : Fin 3 → Set (Set (Fin 42)) := fun c => {y | ∃ k < 56, lab k = c ∧ mk k = y}
  have hroot : ∀ c : Fin 3, ∀ k < 56, lab k = c → ∃ g ∈ M,
      ⇑g '' mk ((R / 2 ^ (6 * (c : ℕ))) % 64) = mk k := by
    intro c k hk hc
    obtain ⟨-, g, hg, he⟩ := hlab k hk
    rw [hc] at he
    exact ⟨g, hg, he⟩
  have hH' : mk ((R / 2 ^ (6 * 0)) % 64) = Set.range o := by
    rw [hrange, hH]
  have hncard : ∀ c : Fin 3, (B c).ncard = (CN / 2 ^ (8 * (c : ℕ))) % 256 := by
    intro c
    rw [← hcnt c c.2]
    have e : B c = ↑((Finset.filter (fun k => lab k = c) (Finset.range 56)).image mk) := by
      ext y
      simp only [B, Set.mem_setOf_eq, Finset.coe_image, Finset.coe_filter, Finset.mem_range,
        Set.mem_image]
      constructor
      · rintro ⟨k, hk, hc, rfl⟩
        exact ⟨k, ⟨hk, hc⟩, rfl⟩
      · rintro ⟨k, ⟨hk, hc⟩, rfl⟩
        exact ⟨k, hk, hc, rfl⟩
    rw [e, Set.ncard_coe_finset, Finset.card_image_of_injOn]
    intro k hk k' hk' h
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hk hk'
    exact hmk_inj k hk.1 k' hk'.1 h
  refine ⟨hMS, ?_, o, ho, hMH, ⟨Q, hQcard.ge, fun τ hτ => hQR hτ⟩, B, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [hMg]
    refine gen_le fun j hj => ?_
    have := (hcomm j (by omega)).2
    simpa using this
  ·
    have h1 : (B 0).ncard = 1 := by rw [hncard]; exact hCN.1
    obtain ⟨y, hy⟩ := Set.ncard_eq_one.mp h1
    have hHB : Set.range o ∈ B 0 := by
      obtain ⟨k, hk, hk0, rfl⟩ : ∃ k < 56, lab k = 0 ∧ mk k = y := by
        have : y ∈ B 0 := by rw [hy]; exact Set.mem_singleton y
        exact this
      obtain ⟨g, hg, he⟩ := hroot 0 k hk hk0
      rw [Fin.val_zero, hH'] at he
      rw [hMH g hg] at he
      exact ⟨k, hk, hk0, he.symm⟩
    rw [hy] at hHB ⊢
    rw [Set.mem_singleton_iff.mp hHB]
  · intro c y hy
    obtain ⟨k, hk, -, rfl⟩ := hy
    obtain ⟨g, hg, he⟩ := hOimg k hk
    exact ⟨g, hg, by rw [← hrange] at he; exact he⟩
  · intro g hg
    obtain ⟨k, hk, he⟩ := hOcov g hg
    obtain ⟨hl, -⟩ := hlab k hk
    refine ⟨⟨lab k, hl⟩, k, hk, rfl, ?_⟩
    rw [hrange]
    exact he.symm
  · intro c d hcd
    rw [Set.disjoint_left]
    rintro y ⟨k, hk, hkc, rfl⟩ ⟨k', hk', hkd, he⟩
    have := hmk_inj k' hk' k hk he
    subst this
    exact hcd (Fin.ext (hkc.symm.trans hkd))
  · intro c y hy z hz
    obtain ⟨k, hk, hkc, rfl⟩ := hy
    obtain ⟨k', hk', hkc', rfl⟩ := hz
    obtain ⟨g₁, hg₁, he₁⟩ := hroot c k hk hkc
    obtain ⟨g₂, hg₂, he₂⟩ := hroot c k' hk' hkc'
    exact ⟨g₂ * g₁⁻¹, mul_mem hg₂ (inv_mem hg₁), image_trans he₁ he₂⟩
  · rw [hncard 1, hncard 2]
    exact hCN.2

theorem recFacts {p : ℕ} [Fact p.Prime] {S P : Subgroup (Equiv.Perm (Fin 42))} {PT RT cnt hi lo : ℕ}
    {L : List (ℕ × ℕ)} (hp2 : 2 ≤ p) (hPS : P ≤ S)
    (hPT : ∀ c < 9, PermN 42 6 63 (lane 252 pm252 PT c) ∧ pp 42 6 63 (lane 252 pm252 PT c) ∈ P)
    (hpow : ∀ i < cnt, (∀ k < p - 1, PermN 42 6 63 (lane 252 pm252 RT ((p - 1) * i + k)) ∧
        pp 42 6 63 (lane 252 pm252 RT ((p - 1) * i + k)) =
          pp 42 6 63 (lane 252 pm252 RT ((p - 1) * i)) ^ (k + 1)) ∧
      pp 42 6 63 (lane 252 pm252 RT ((p - 1) * i)) ^ p = 1 ∧
      pp 42 6 63 (lane 252 pm252 RT ((p - 1) * i)) ≠ 1)
    (hrepS : ∀ i < cnt, pp 42 6 63 (lane 252 pm252 RT ((p - 1) * i)) ∈ S)
    (h : recsK 42 6 63 252 pm252 p 9 ((p - 1) * cnt) PT RT hi L lo = true) :
    (L.map Prod.fst).Pairwise (· < ·) ∧ ∀ e ∈ L, lo < e.1 ∧ e.1 ≤ hi ∧
      PermN 42 6 63 e.1 ∧ e.1 < 2 ^ 252 ∧ CanonGen p (pp 42 6 63 e.1) ∧
      orderOf (pp 42 6 63 e.1) = p ∧ pp 42 6 63 e.1 ∈ S ∧ pp 42 6 63 e.1 ≠ 1 ∧
      pp 42 6 63 e.1 ^ p = 1 ∧ ∃ c ∈ P, ∃ i < cnt,
        c⁻¹ * pp 42 6 63 e.1 * c ∈ Subgroup.zpowers (pp 42 6 63 (lane 252 pm252 RT ((p - 1) * i))) := by
  have hRT : ∀ t < (p - 1) * cnt, PermN 42 6 63 (lane 252 pm252 RT t) := by
    intro t ht
    have hp1 : 0 < p - 1 := by omega
    have hi : t / (p - 1) < cnt := by
      rw [Nat.div_lt_iff_lt_mul hp1]
      rw [Nat.mul_comm] at ht
      exact ht
    have e : t = (p - 1) * (t / (p - 1)) + t % (p - 1) := (Nat.div_add_mod t (p - 1)).symm
    have := ((hpow _ hi).1 (t % (p - 1)) (Nat.mod_lt _ hp1)).1
    rwa [← e] at this
  obtain ⟨hpw, hall⟩ := recsK_sound (fun c hc => (hPT c hc).1) hRT h
  refine ⟨hpw, fun e he => ?_⟩
  obtain ⟨hlo, hhi, hlt, hperm, hcan, c, hc, t, ht, hX⟩ := hall e he
  have hp1 : 0 < p - 1 := by omega
  set i := t / (p - 1) with hi
  set k := t % (p - 1) with hk
  have hicnt : i < cnt := by
    rw [hi, Nat.div_lt_iff_lt_mul hp1]
    rw [Nat.mul_comm] at ht
    exact ht
  have hkp : k < p - 1 := Nat.mod_lt _ hp1
  have et : t = (p - 1) * i + k := (Nat.div_add_mod t (p - 1)).symm
  set r := pp 42 6 63 (lane 252 pm252 RT ((p - 1) * i)) with hr
  obtain ⟨hpowi, hrp, hr1⟩ := hpow i hicnt
  have hR : pp 42 6 63 (lane 252 pm252 RT t) = r ^ (k + 1) := by
    rw [et]
    exact (hpowi k hkp).2
  set C := pp 42 6 63 (lane 252 pm252 PT c) with hC
  set X := pp 42 6 63 e.1 with hXd
  have hCX : C⁻¹ * X * C = r ^ (k + 1) := by
    rw [hX, ← hR]
    group
  have hX1 : X ≠ 1 := ne_one_of_canonGen hcan
  have hXp : X ^ p = 1 := by
    have e1 : X = C * r ^ (k + 1) * C⁻¹ := by rw [← hCX]; group
    rw [e1, conj_pow, ← pow_mul, mul_comm, pow_mul, hrp, one_pow]
    group
  have hCP : C ∈ P := (hPT c hc).2
  have hXS : X ∈ S := by
    rw [hX]
    exact mul_mem (mul_mem (hPS hCP) (hR ▸ pow_mem (hrepS i hicnt) _)) (inv_mem (hPS hCP))
  refine ⟨hlo, hhi, hperm, hlt, hcan, orderOf_eq_prime hXp hX1, hXS, hX1, hXp, C, hCP, i, hicnt,
    ?_⟩
  rw [hCX]
  exact Subgroup.npow_mem_zpowers r (k + 1)

end CFSG.StandardType.L34Sylow
