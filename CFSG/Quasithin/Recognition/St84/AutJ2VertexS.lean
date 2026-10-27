module

public import CFSG.Quasithin.Recognition.St84.J2VertexS
public import CFSG.GroupTheory.PCore.PCoreOfIndex
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open
open CFSG.GroupTheory
open CFSG.LieType.BorelTits
open CFSG.Quasithin.F112R.St84.Heis
open CFSG.QuasithinUnique

variable {G : Type*} [Group G]

private theorem relIndex_subgroupOf_pCore_le_two [Finite G] {P Q : Subgroup G} (hQP : Q ≤ P)
    (hO : Q.relIndex (pCoreOf 2 P) ≤ 2) :
    (Q.subgroupOf P).relIndex (pCore 2 ↥P) ≤ 2 := by
  have hpcore : (pCoreOf 2 P).subgroupOf P = pCore 2 ↥P := by
    rw [show pCoreOf 2 P = (pCore 2 ↥P).map P.subtype from rfl,
      ← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
  rw [← hpcore, Subgroup.relIndex_subgroupOf (H := Q) (K := pCoreOf 2 P) (L := P)
    (pCoreOf_le 2 P)]
  exact hO

private theorem mem_centralizer_subgroupOf_of_mem_ker [Finite G] {P Q : Subgroup G}
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) (χ : ↥Q ≃* Q1M) {x : ↥P}
    (hx : x ∈ (parAct hPQ χ).ker) :
    x ∈ Subgroup.centralizer ((Q.subgroupOf P : Subgroup ↥P) : Set ↥P) := by
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hxQ : (x : G) ∈ Subgroup.centralizer (Q : Set G) :=
    (parAct_eq_one_iff (P := P) (Q := Q) (hPQ := hPQ) (χ := χ) x).mp hx
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.mp hxQ (q : G) hq

private theorem centralInvolution_mem_subgroupOf [Finite G] {P Q : Subgroup G}
    (hZ : ∀ c ∈ P, (∀ g ∈ P, g * c = c * g) → c ^ 2 = 1 → c ∈ Q) :
    ∀ c : ↥P, c ∈ Subgroup.center ↥P → c ^ 2 = 1 → c ∈ Q.subgroupOf P := by
  intro c hcen hc2
  have hcen' : ∀ g : ↥P, g * c = c * g := Subgroup.mem_center_iff.mp hcen
  have hcenG : ∀ g ∈ P, g * (c : G) = (c : G) * g := by
    intro g hg
    have h := congrArg Subtype.val (hcen' ⟨g, hg⟩)
    simpa using h
  have hc2G : (c : G) ^ 2 = 1 := by simpa using congrArg Subtype.val hc2
  exact hZ (c : G) c.2 hcenG hc2G

private theorem card_inf_ker_le_two {X : Type*} [Group X] [Finite X] {Q K N : Subgroup X}
    (hKnormal : K.Normal) (hK2 : IsPGroup 2 K)
    (hQindex : Q.relIndex (pCore 2 X) ≤ 2) (hNQ : N ⊓ Q = ⊥) :
    Nat.card ↥(N ⊓ K) ≤ 2 := by
  have hKcore : K ≤ pCore 2 X := le_pCore (r := 2) (G := X) hKnormal hK2
  have hNKQ : N ⊓ K ⊓ Q = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxNK, hxQ⟩ := Subgroup.mem_inf.mp hx
    have hxN : x ∈ N := (Subgroup.mem_inf.mp hxNK).1
    have hmem : x ∈ N ⊓ Q := ⟨hxN, hxQ⟩
    rwa [hNQ] at hmem
  have hVsub : (K ⊓ Q).subgroupOf (N ⊓ K) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx
    obtain ⟨hxK, hxQ⟩ := hx
    have hxNK : (x : X) ∈ N ⊓ K := x.2
    have hmem : (x : X) ∈ N ⊓ K ⊓ Q := ⟨hxNK, hxQ⟩
    rw [hNKQ] at hmem
    simpa using hmem
  have hindex : (K ⊓ Q).relIndex (N ⊓ K) = Nat.card ↥(N ⊓ K) := by
    rw [Subgroup.relIndex, hVsub, Subgroup.index_bot]
  have hfin1 : (K ⊓ Q).relIndex K ≠ 0 :=
    (Subgroup.finiteIndex_of_finite (H := (K ⊓ Q).subgroupOf K)).index_ne_zero
  have hfin2 : Q.relIndex (pCore 2 X) ≠ 0 :=
    (Subgroup.finiteIndex_of_finite (H := Q.subgroupOf (pCore 2 X))).index_ne_zero
  have h1 : (K ⊓ Q).relIndex (N ⊓ K) ≤ (K ⊓ Q).relIndex K :=
    Subgroup.relIndex_le_of_le_right (H := K ⊓ Q) (K := N ⊓ K) (L := K) inf_le_right hfin1
  have h2 : (K ⊓ Q).relIndex K = Q.relIndex K := by
    rw [inf_comm]
    exact Subgroup.inf_relIndex_right (H := Q) (K := K)
  have h3 : Q.relIndex K ≤ Q.relIndex (pCore 2 X) :=
    Subgroup.relIndex_le_of_le_right hKcore hfin2
  calc Nat.card ↥(N ⊓ K) = (K ⊓ Q).relIndex (N ⊓ K) := hindex.symm
    _ ≤ (K ⊓ Q).relIndex K := h1
    _ = Q.relIndex K := h2
    _ ≤ Q.relIndex (pCore 2 X) := h3
    _ ≤ 2 := hQindex

private theorem card_eq_36_of_card_map {X : Type*} [Group X] [Finite X] {N : Subgroup X}
    {T : Sylow 3 X} (hN : N = Subgroup.normalizer (T : Set X)) (hXcard : Nat.card X = 2304)
    {m t : ℕ} (hm : m = 18 ∨ m = 36) (ht : t = 1 ∨ t = 2)
    (hcard : Nat.card N = m * t) : Nat.card N = 36 := by
  have hmul : Nat.card N * N.index = 2304 := by
    rw [Subgroup.card_mul_index, hXcard]
  have hsyl : Nat.card (Sylow 3 X) = N.index := by
    rw [hN]
    exact Sylow.card_eq_index_normalizer T
  have hsylmod : Nat.card (Sylow 3 X) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 X
  rcases hm with hm | hm <;> rcases ht with ht | ht
  · exfalso
    have hi : N.index = 128 := by
      rw [hm, ht, mul_one] at hcard
      rw [hcard] at hmul
      refine Nat.mul_left_cancel (by norm_num : (0:ℕ) < 18) ?_
      rw [hmul]
    rw [hsyl, hi] at hsylmod
    norm_num at hsylmod
  · rw [hm, ht] at hcard
    omega
  · rw [hm, ht, mul_one] at hcard
    exact hcard
  · exfalso
    have hi : N.index = 32 := by
      rw [hm, ht] at hcard
      rw [hcard] at hmul
      refine Nat.mul_left_cancel (by norm_num : (0:ℕ) < 36 * 2) ?_
      rw [hmul]
    rw [hsyl, hi] at hsylmod
    norm_num at hsylmod

theorem map_normalizer_le_AJ' {X : Type*} [Group X] {T : Subgroup X}
    (ψ : X →* MulAut Q1M) (hψT : T.map ψ = AJ3) :
    (Subgroup.normalizer (T : Set X)).map ψ ≤ AJ' := by
  have h := Subgroup.le_normalizer_map (H := T) (f := ψ)
  rw [hψT] at h
  exact h.trans normalizer_AJ3_le

private theorem card_eq_card_map_mul_card_inf_ker {X : Type*} [Group X]
    {N : Subgroup X} (ψ : X →* MulAut Q1M) :
    Nat.card N = Nat.card (N.map ψ) * Nat.card ↥(N ⊓ ψ.ker) := by
  classical
  let ψN : ↥N →* MulAut Q1M := ψ.comp N.subtype
  have hrangeN : ψN.range = N.map ψ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hkerN : ψN.ker = ψ.ker.subgroupOf N := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    rfl
  have h1 := Subgroup.card_ker_mul_card_range ψN
  rw [hkerN, hrangeN] at h1
  have h2 : Nat.card (ψ.ker.subgroupOf N) = Nat.card ↥(N ⊓ ψ.ker) := by
    have hsub : ψ.ker.subgroupOf N = (N ⊓ ψ.ker).subgroupOf N := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
    rw [hsub]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h2, mul_comm] at h1
  exact h1.symm

theorem card_normalizer_eq_36_and_inf_ker_eq_bot {X : Type*} [Group X] [Finite X]
    {Q : Subgroup X} (ψ : X →* MulAut Q1M)
    (hK2 : IsPGroup 2 ψ.ker)
    (hKQ : ψ.ker ≤ Subgroup.centralizer (Q : Set X))
    (hQcard : Nat.card Q = 64) (hQindex : Q.relIndex (pCore 2 X) ≤ 2)
    {T : Sylow 3 X} (hψT : (T : Subgroup X).map ψ = AJ3)
    (hAJN : AJ ≤ (Subgroup.normalizer (T : Set X)).map ψ)
    (hNQ : Subgroup.normalizer (T : Set X) ⊓ Q = ⊥)
    (hZ : ∀ c ∈ Subgroup.center X, c ^ 2 = 1 → c ∈ Q)
    (hXcard : Nat.card X = 2304) :
    Nat.card (Subgroup.normalizer (T : Set X)) = 36 ∧
      Subgroup.normalizer (T : Set X) ⊓ ψ.ker = ⊥ := by
  classical
  let N : Subgroup X := Subgroup.normalizer (T : Set X)
  have hKnormal : ψ.ker.Normal := MonoidHom.normal_ker ψ
  have hNAJ' : N.map ψ ≤ AJ' := map_normalizer_le_AJ' ψ hψT
  have hNmap_card : Nat.card (N.map ψ) = 18 ∨ Nat.card (N.map ψ) = 36 := by
    have hdvd : Nat.card (N.map ψ) ∣ 36 := by
      rw [← card_AJ']
      exact Subgroup.card_dvd_of_le hNAJ'
    have hle : 18 ≤ Nat.card (N.map ψ) := by
      rw [← card_AJ]
      exact Subgroup.card_le_of_le hAJN
    have hmem : Nat.card (N.map ψ) ∈ Nat.divisors 36 :=
      Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hdiv : Nat.divisors 36 = {1, 2, 3, 4, 6, 9, 12, 18, 36} := by decide
    rw [hdiv] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  have hbound : Nat.card ↥(N ⊓ ψ.ker) ≤ 2 := card_inf_ker_le_two hKnormal hK2 hQindex hNQ
  have hNcard : Nat.card N = Nat.card (N.map ψ) * Nat.card ↥(N ⊓ ψ.ker) :=
    card_eq_card_map_mul_card_inf_ker ψ
  have hk : Nat.card ↥(N ⊓ ψ.ker) = 1 ∨ Nat.card ↥(N ⊓ ψ.ker) = 2 := by
    have hpos : 0 < Nat.card ↥(N ⊓ ψ.ker) := Nat.card_pos
    omega
  have hN36 : Nat.card N = 36 :=
    card_eq_36_of_card_map (N := N) (T := T) rfl hXcard hNmap_card hk hNcard
  refine ⟨hN36, ?_⟩
  rcases hk with hk1 | hk2
  · exact Subgroup.eq_bot_of_card_eq (H := N ⊓ ψ.ker) hk1
  · exact absurd hk2 (card_inf_ne_two_of_le_centralizer hKnormal hKQ hNQ
      (by rw [hQcard, hN36, hXcard]) hZ)

private theorem normalizer_sylow_inf_subgroupOf_eq_bot [Finite G] {P Q R A : Subgroup G}
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) (χ : ↥Q ≃* Q1M)
    (hAP : A ≤ P) (hRA : R ≤ A) (hAR : A ≤ Subgroup.normalizer (R : Set G))
    {T : Sylow 3 ↥P} (hTcoe : (T : Subgroup ↥P) = R.subgroupOf P)
    {r0 : G} (hr0R : r0 ∈ R)
    (hρ : parAct hPQ χ ⟨r0, hAP (hRA hr0R)⟩ = ρM) (hRQ : R ⊓ Q = ⊥) :
    Subgroup.normalizer (T : Set ↥P) ⊓ Q.subgroupOf P = ⊥ := by
  classical
  let N' : Subgroup ↥P := Subgroup.normalizer (T : Set ↥P)
  let NG : Subgroup G := N'.map P.subtype
  have hNGnorm : NG ≤ Subgroup.normalizer (R : Set G) := by
    have h := Subgroup.le_normalizer_map (H := (T : Subgroup ↥P)) (f := P.subtype)
    have hTR : (T : Subgroup ↥P).map P.subtype = R := by
      rw [hTcoe, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hRA.trans hAP)]
    rwa [hTR] at h
  have hNGQ : NG ⊓ Q = ⊥ :=
    inf_eq_bot_of_le_normalizer_of_parAct_eq_ρM hPQ χ hr0R (hRA.trans hAP) hρ hRQ hNGnorm
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxN, hxQ⟩ := Subgroup.mem_inf.mp hx
  have hxNG : (x : G) ∈ NG := Subgroup.mem_map.mpr ⟨x, hxN, rfl⟩
  have hxQG : (x : G) ∈ Q := hxQ
  have hmem : (x : G) ∈ NG ⊓ Q := ⟨hxNG, hxQG⟩
  rw [hNGQ] at hmem
  have hx1 : (x : G) = 1 := by simpa using hmem
  exact Subtype.ext hx1

private theorem nonempty_mulEquiv_of_normalizer {Y : Type*} [Group Y] [Finite Y]
    {Q N : Subgroup Y} (hNQ : N ⊓ Q = ⊥)
    (hcard : Nat.card Q * Nat.card N = Nat.card (⊤ : Subgroup Y))
    (hPQ : ⊤ ≤ Subgroup.normalizer (Q : Set Y)) {ψ : Y →* MulAut Q1M}
    (hψAJ : N.map ψ ≤ AJ') (hψker : N ⊓ ψ.ker = ⊥) (hNcard : Nat.card N = 36)
    (χ : ↥Q ≃* Q1M)
    (hψχ : ∀ n : ↥N, ψ (n : Y) = parAct hPQ χ (Subgroup.inclusion le_top n)) :
    Nonempty (Y ≃* Q1M ⋊[AJ'.subtype] ↥AJ') := by
  classical
  let ψN : ↥N →* MulAut Q1M := ψ.comp N.subtype
  have hkerN : ψN.ker = ψ.ker.subgroupOf N := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    rfl
  have hkerNbot : ψN.ker = ⊥ := by
    rw [hkerN, eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have hmem : (x : Y) ∈ N ⊓ ψ.ker := ⟨x.2, hx⟩
    rw [hψker] at hmem
    simpa using hmem
  have hinjN : Function.Injective ψN := (MonoidHom.ker_eq_bot_iff ψN).mp hkerNbot
  have hrangeN : ψN.range = N.map ψ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hle : ψN.range ≤ AJ' := by
    rw [hrangeN]
    exact hψAJ
  have hcardrange : Nat.card ψN.range = Nat.card AJ' := by
    have h1 : Nat.card ψN.range = Nat.card ↥N :=
      (Nat.card_congr (MonoidHom.ofInjective hinjN).toEquiv).symm
    rw [h1, hNcard, card_AJ']
  have hrangeAJ' : ψN.range = AJ' :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcardrange.symm)
  let e : ↥N ≃* ↥AJ' := (MonoidHom.ofInjective hinjN).trans (MulEquiv.subgroupCongr hrangeAJ')
  have he : ∀ n : ↥N, (e n : MulAut Q1M) = parAct hPQ χ (Subgroup.inclusion le_top n) := by
    intro n
    rw [show (e n : MulAut Q1M) = ψ (n : Y) from rfl, hψχ n]
  exact (nonempty_mulEquiv_semidirect (G := Y) (P := ⊤) (Q := Q) (A := N) le_top hPQ
    le_top hNQ hcard χ e he).map (fun f => Subgroup.topEquiv.symm.trans f)

private theorem exists_normalizer_sylow_inf_eq_bot [Finite G] {P Q R A : Subgroup G}
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) (χ : ↥Q ≃* Q1M)
    (hAP : A ≤ P) (hRA : R ≤ A) (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hRcard : Nat.card R = 9) (hQ2 : IsPGroup 2 Q)
    {T : Sylow 3 ↥P} (hTcoe : (T : Subgroup ↥P) = R.subgroupOf P)
    (hRsubmap : (R.subgroupOf P).map (parAct hPQ χ) = AJ3)
    (hrange : ((parAct hPQ χ).comp (Subgroup.inclusion hAP)).range = AJ) :
    ∃ N' : Subgroup ↥P, N' = Subgroup.normalizer (T : Set ↥P) ∧
      AJ ≤ N'.map (parAct hPQ χ) ∧ N' ⊓ Q.subgroupOf P = ⊥ := by
  classical
  let ψ : ↥P →* MulAut Q1M := parAct hPQ χ
  let A' : Subgroup ↥P := A.subgroupOf P
  have hA'map : A'.map ψ = AJ := by
    rw [← hrange]
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p.1, hp⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨⟨(a : G), hAP a.2⟩, a.2, rfl⟩
  have hA'N : A' ≤ Subgroup.normalizer (T : Set ↥P) := by
    have hN'eq : Subgroup.normalizer (T : Set ↥P) =
        (Subgroup.normalizer (R : Set G)).subgroupOf P := by
      change Subgroup.normalizer ((T : Subgroup ↥P) : Set ↥P) =
        (Subgroup.normalizer (R : Set G)).subgroupOf P
      rw [hTcoe]
      exact (Subgroup.subgroupOf_normalizer_eq (hRA.trans hAP)).symm
    rw [hN'eq]
    intro a ha
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    exact hAR ha
  have hAJN : AJ ≤ (Subgroup.normalizer (T : Set ↥P)).map ψ := by
    rw [← hA'map]
    exact Subgroup.map_mono hA'N
  have hRP : R ≤ P := hRA.trans hAP
  have hρMmem : ρM ∈ (R.subgroupOf P).map ψ := by
    rw [hRsubmap]
    exact ρM_mem_AJ3
  obtain ⟨r0, hr0R, hr0ψ⟩ := Subgroup.mem_map.mp hρMmem
  have hr0RG : (r0 : G) ∈ R := hr0R
  have hρ : parAct hPQ χ ⟨(r0 : G), hRP hr0RG⟩ = ρM := by
    have hsub : (⟨(r0 : G), hRP hr0RG⟩ : ↥P) = r0 := Subtype.ext rfl
    calc parAct hPQ χ ⟨(r0 : G), hRP hr0RG⟩ = ψ ⟨(r0 : G), hRP hr0RG⟩ := rfl
      _ = ψ r0 := by rw [hsub]
      _ = ρM := hr0ψ
  have hRQ : R ⊓ Q = ⊥ := by
    have hR3 : IsPGroup 3 R :=
      IsPGroup.of_card (p := 3) (n := 2) (by rw [hRcard]; norm_num)
    exact disjoint_iff.mp
      (IsPGroup.disjoint_of_coprime hR3 hQ2 (by norm_num : Nat.Coprime 3 2))
  exact ⟨Subgroup.normalizer (T : Set ↥P), rfl, hAJN,
    normalizer_sylow_inf_subgroupOf_eq_bot hPQ χ hAP hRA hAR hTcoe hr0RG hρ hRQ⟩

theorem nonempty_mulEquiv_heisModelAut [Finite G] {P Q : Subgroup G} (hQP : Q ≤ P)
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) (hP : Nat.card P = 2304) (hchar : CharTwo P)
    (hO : Q.relIndex (pCoreOf 2 P) ≤ 2) (χ : ↥Q ≃* Q1M)
    {β t : G} (hβP : β ∈ P) (hβ3 : β ^ 3 = 1) (hχβ : parAct hPQ χ ⟨β, hβP⟩ = βM)
    (htP : t ∈ P) (hχt : parAct hPQ χ ⟨t, htP⟩ = τM)
    (hZ : ∀ c ∈ P, (∀ g ∈ P, g * c = c * g) → c ^ 2 = 1 → c ∈ Q) :
    Nonempty (↥P ≃* Q1M ⋊[AJ'.subtype] ↥AJ') := by
  classical
  have hQcard : Nat.card Q = 64 := by
    rw [Nat.card_congr χ.toEquiv, card_Q1M]
  have hQ2 : IsPGroup 2 Q :=
    IsPGroup.of_card (p := 2) (n := 6) (by rw [hQcard]; norm_num)
  have hker : IsPGroup 2 ↥(P ⊓ Subgroup.centralizer (Q : Set G)) :=
    isPGroup_inf_centralizer_of_relIndex_le_two hQ2 hchar hO
  have h3 : Nat.factorization (Nat.card P) 3 = 2 := by
    rw [hP]
    decide +kernel
  obtain ⟨R, A, hAP, hβR, hRA, hRcard, hAR, _, hrange⟩ :=
    exists_heisComplement hPQ h3 hker χ hβP hβ3 hχβ htP hχt
  have hRP : R ≤ P := hRA.trans hAP
  let ψ : ↥P →* MulAut Q1M := parAct hPQ χ
  let Q' : Subgroup ↥P := Q.subgroupOf P
  let K : Subgroup ↥P := ψ.ker
  let Rsub : Subgroup ↥P := R.subgroupOf P
  have hQ'normal : Q'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mpr hPQ
  have hQ'card : Nat.card Q' = 64 := by
    rw [show Nat.card Q' = Nat.card Q from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP)]
    exact hQcard
  have hQ'index : Q'.relIndex (pCore 2 ↥P) ≤ 2 :=
    relIndex_subgroupOf_pCore_le_two hQP hO
  have hKeq : K = (P ⊓ Subgroup.centralizer (Q : Set G)).subgroupOf P := ker_parAct hPQ χ
  have hK2 : IsPGroup 2 K := by
    rw [hKeq]
    exact hker.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left).symm
  have hKQ : K ≤ Subgroup.centralizer (Q' : Set ↥P) :=
    fun x hx => mem_centralizer_subgroupOf_of_mem_ker hPQ χ hx
  have hRsubcard : Nat.card Rsub = 9 := by
    rw [show Nat.card Rsub = Nat.card R from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRP)]
    exact hRcard
  have hψR : Rsub.map ψ = AJ3 :=
    map_eq_AJ3_of_card_eq_nine hPQ hker χ hRsubcard hβR hχβ
  have hRsubcard' : Nat.card Rsub = 3 ^ (Nat.card ↥P).factorization 3 := by
    rw [show Nat.card ↥P = Nat.card P from rfl, h3, hRsubcard]
    norm_num
  let T : Sylow 3 ↥P := Sylow.ofCard Rsub hRsubcard'
  have hTcoe : (T : Subgroup ↥P) = Rsub := Sylow.coe_ofCard Rsub hRsubcard'
  have hψT : (T : Subgroup ↥P).map ψ = AJ3 := by
    rw [hTcoe]
    exact hψR
  obtain ⟨N', hN'def, hAJN, hNQ'⟩ :=
    exists_normalizer_sylow_inf_eq_bot hPQ χ hAP hRA hAR hRcard hQ2 hTcoe hψR hrange
  subst N'
  let N' : Subgroup ↥P := Subgroup.normalizer (T : Set ↥P)
  have hZ' : ∀ c : ↥P, c ∈ Subgroup.center ↥P → c ^ 2 = 1 → c ∈ Q' :=
    centralInvolution_mem_subgroupOf hZ
  have hPcard : Nat.card ↥P = 2304 := by
    rw [show Nat.card ↥P = Nat.card P from rfl, hP]
  obtain ⟨hNcard, hNK⟩ :=
    card_normalizer_eq_36_and_inf_ker_eq_bot ψ hK2 hKQ hQ'card hQ'index hψT hAJN hNQ' hZ'
      hPcard
  let χ' : ↥Q' ≃* Q1M := (Subgroup.subgroupOfEquivOfLe hQP).trans χ
  have hcardQN : Nat.card Q' * Nat.card N' = Nat.card (⊤ : Subgroup ↥P) := by
    rw [Subgroup.card_top, hQ'card, hNcard, hPcard]
  have hNAJ' : N'.map ψ ≤ AJ' := map_normalizer_le_AJ' ψ hψT
  have hPQtop : ⊤ ≤ Subgroup.normalizer (Q' : Set ↥P) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hQ'normal]
  have hψχ : ∀ n : ↥N', ψ (n : ↥P) =
      parAct hPQtop χ' (Subgroup.inclusion le_top n) := by
    intro n
    refine MulEquiv.ext fun m => ?_
    rw [parAct_apply]
    rfl
  exact nonempty_mulEquiv_of_normalizer hNQ' hcardQN hPQtop hNAJ' hNK hNcard χ' hψχ

end CFSG.Quasithin.F112R.St84
