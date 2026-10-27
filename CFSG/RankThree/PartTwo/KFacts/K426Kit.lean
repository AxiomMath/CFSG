module

public import Certificates.Data.K426Checks

public section

namespace CFSG.RankThree.PartTwo.KFacts.K426

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.RankThree.PartOne
open scoped commutatorElement

variable {n : ℕ}

section Lines

variable {p N r : ℕ} {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert} {xs : Array (Array ℕ)}

theorem linesOK3_parts (h : linesOK3 p N r n gs ps c xs = true) :
    enumOK n gs ps c = true ∧ c.pts.size = N ∧
    allLt N (fun k => !(eqA n (powArr n c.pts[k]! p) (idA n)) || eqA n c.pts[k]! (idA n) ||
      (List.range r).any fun j => (List.range p).any fun e =>
        eqA n c.pts[k]! (powArr n xs[j]! e)) = true ∧
    allLt r (fun j => validA n xs[j]! && eqA n (powArr n xs[j]! p) (idA n)) = true := by
  simp only [linesOK3, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem linesOK3_line (h : linesOK3 p N r n gs ps c xs = true) {j : ℕ} (hj : j < r) :
    validA n xs[j]! = true ∧ permOfArr n xs[j]! ^ p = 1 := by
  have hl := allLt_spec (linesOK3_parts h).2.2.2 hj
  simp only [Bool.and_eq_true] at hl
  exact ⟨hl.1, (eqA_iff (rep_powArr (rep_of_validA hl.1) p) rep_idA).1 hl.2⟩

theorem linesOK3_card (hps : ∀ q ∈ ps, q < n) (h : linesOK3 p N r n gs ps c xs = true) :
    Nat.card (closure (permsA n gs)) = N :=
  (enumOK_spec hps (linesOK3_parts h).1).2.1.trans (linesOK3_parts h).2.1

theorem linesOK3_spec (hps : ∀ q ∈ ps, q < n) (h : linesOK3 p N r n gs ps c xs = true)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ closure (permsA n gs)) (hgp : g ^ p = 1) :
    g = 1 ∨ ∃ j < r, ∃ e < p, g = permOfArr n xs[j]! ^ e := by
  obtain ⟨hE, hN, hk, -⟩ := linesOK3_parts h
  obtain ⟨k, hkc, hkg⟩ := enumOK_exists_rep hps hE hg
  rw [hN] at hkc
  have hc := allLt_spec hk hkc
  have hpow : eqA n (powArr n c.pts[k]! p) (idA n) = true :=
    (eqA_iff (rep_powArr hkg p) rep_idA).2 hgp
  rw [hpow, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hc
  rcases hc with hc | hc
  · exact Or.inl ((eqA_iff hkg rep_idA).1 hc)
  · simp only [List.any_eq_true, List.mem_range] at hc
    obtain ⟨j, hj, e, he, hje⟩ := hc
    exact Or.inr ⟨j, hj, e, he,
      (eqA_iff hkg (rep_powArr (rep_of_validA (linesOK3_line h hj).1) e)).1 hje⟩

end Lines

theorem transOK2_spec {r : ℕ} {H X L : Array (Array ℕ)} {rec : List ℕ} {RL : Array Level}
    {Rb : Array ℕ} {R' : Subgroup (Equiv.Perm (Fin n))}
    (hmemR : ∀ {g : Array ℕ} {G : Equiv.Perm (Fin n)}, Rep n g G → siftA n RL Rb 0 g = true →
      G ∈ R')
    (hX : ∀ j < r, validA n X[rec.getD j 0]! = true) (hL : ∀ j < r, validA n L[j]! = true)
    (h : transOK2 r n H X L rec RL Rb = true) {j : ℕ} (hj : j < r) :
    permOfArr n H[j]! ∈ R' ∧
      permOfArr n H[j]! * permOfArr n X[rec.getD j 0]! * (permOfArr n H[j]!)⁻¹ =
        permOfArr n L[j]! := by
  have h' := allLt_spec h hj
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨hv, hs⟩, he⟩ := h'
  exact ⟨hmemR (rep_of_validA hv) hs,
    eq_of_eqA (rep_conjA hv (rep_of_validA (hX j hj))) (rep_of_validA (hL j hj)) he⟩

theorem centralizer_eq_of_ptailOK' {p chunks : ℕ} {Q : RawSchreierDatum n}
    {O S : Array (Array ℕ)} {base : Array ℕ} {W : Array (List ℤ)} (hA : ChainArrays Q O S base W)
    (hc0 : 0 < chunks) (hc : rawChainOK n O S base W chunks = true) {x : Array ℕ}
    {X : Equiv.Perm (Fin n)} (hx : Rep n x X) {rels : List (ℕ × ℕ × ℕ)}
    {gs : Array (Array ℕ)} {ps : List ℕ} {cC : ArrCert} {N : ℕ} (hps : ∀ q ∈ ps, q < n)
    (hcent : centOKP p n S base x rels gs ps cC N = true) :
    closure (permsA n gs) = centralizer {X} ⊓ Q.originalSubgroup ∧
      Nat.card (closure (permsA n gs)) = N := by
  simp only [centOKP, Bool.and_eq_true, beq_iff_eq] at hcent
  obtain ⟨⟨⟨⟨⟨hrels, hC⟩, hsize⟩, hcomm⟩, hsift⟩, htail⟩ := hcent
  refine ⟨le_antisymm ?_ ?_, (enumOK_spec hps hC).2.1.trans hsize⟩
  · rw [closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hrep := rep_of_validA (enumOK_gens_valid hC hk)
    refine mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_, ?_⟩
    · exact (commA_iff hrep hx).1 (allLt_spec hcomm hk)
    · exact (siftA_iff_mem_originalSubgroup hA hc0 hc hrep).1 (allLt_spec hsift hk)
  · intro g hg
    have htail' : ptailOK n (rawLevels n S base) base x (powPA p n x) rels cC.pts.toList
        Q.baseCount 0 (idA n) = true := by
      rw [← hA.base_size]
      exact htail
    obtain ⟨e, he, hre⟩ := centralizer_subset_of_ptailOK hA (chainCheckFacts hc)
      (validSchreier_of_chainOK hA hc0 hc).1 hx (rep_powPA hx) (relsOKP_spec hrels) htail' hg
    exact enumOK_mem_of_mem hps hC hre he

theorem commutator_le_of_derivedLeOK {gC gD : Array (Array ℕ)} {ps : List ℕ} {cD : ArrCert}
    {M : ℕ} (hps : ∀ q ∈ ps, q < n) (hval : ∀ k < gC.size, validA n gC[k]! = true)
    (h : derivedLeOK n gC gD ps cD M = true) :
    ⁅closure (permsA n gC), closure (permsA n gC)⁆ ≤ closure (permsA n gD) ∧
      Nat.card (closure (permsA n gD)) = M := by
  simp only [derivedLeOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hDe, hDs⟩, hnorm⟩, hcomm⟩ := h
  refine ⟨?_, (enumOK_spec hps hDe).2.1.trans hDs⟩
  set D := closure (permsA n gD)
  have hconjgen : ∀ k < gC.size, ∀ l < gD.size,
      permOfArr n gC[k]! * permOfArr n gD[l]! * (permOfArr n gC[k]!)⁻¹ ∈ D := fun k hk l hl =>
    enumOK_mem_of_any hps hDe (rep_conjA (hval k hk) (rep_of_validA (enumOK_gens_valid hDe hl)))
      (allLt_spec (allLt_spec hnorm hk) hl)
  have hcommgen : ∀ k < gC.size, ∀ l < gC.size,
      ⁅permOfArr n gC[k]!, permOfArr n gC[l]!⁆ ∈ D := fun k hk l hl =>
    enumOK_mem_of_any hps hDe (rep_commutatorA (hval k hk) (hval l hl))
      (allLt_spec (allLt_spec hcomm hk) hl)
  have hCN : closure (permsA n gC) ≤ normalizer (D : Set (Equiv.Perm (Fin n))) :=
    closure_le_normalizer_closure (by
      rintro _ ⟨k, hk, rfl⟩ _ ⟨l, hl, rfl⟩
      exact hconjgen k hk l hl)
  have hconj : ∀ g ∈ closure (permsA n gC), ∀ m ∈ D, g * m * g⁻¹ ∈ D := fun g hg m hm =>
    (mem_normalizer_iff.1 (hCN hg) m).1 hm
  have hgenC : ∀ k < gC.size, ∀ h ∈ closure (permsA n gC), ⁅permOfArr n gC[k]!, h⁆ ∈ D := by
    intro k hk h hh
    induction hh using closure_induction with
    | mem s hs =>
      obtain ⟨l, hl, rfl⟩ := hs
      exact hcommgen k hk l hl
    | one => simp
    | mul a b ha hb iha ihb =>
      have e : ⁅permOfArr n gC[k]!, a * b⁆ =
          ⁅permOfArr n gC[k]!, a⁆ * (a * ⁅permOfArr n gC[k]!, b⁆ * a⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact D.mul_mem iha (hconj a ha _ ihb)
    | inv a ha iha =>
      have e : ⁅permOfArr n gC[k]!, a⁻¹⁆ = a⁻¹ * ⁅permOfArr n gC[k]!, a⁆⁻¹ * a⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hconj a⁻¹ ((closure (permsA n gC)).inv_mem ha) _ (D.inv_mem iha)
  rw [commutator_le]
  intro g hg h hh
  induction hg using closure_induction with
  | mem s hs =>
    obtain ⟨k, hk, rfl⟩ := hs
    exact hgenC k hk h hh
  | one => simp
  | mul a b ha hb iha ihb =>
    have e : ⁅a * b, h⁆ = a * ⁅b, h⁆ * a⁻¹ * ⁅a, h⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact D.mul_mem (hconj a ha _ ihb) iha
  | inv a ha iha =>
    have e : ⁅a⁻¹, h⁆ = a⁻¹ * ⁅a, h⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hconj a⁻¹ ((closure (permsA n gC)).inv_mem ha) _ (D.inv_mem iha)

theorem rep_evalWA {m : ℕ} {gs : Array (Array ℕ)} (hval : ∀ k < gs.size, validA n gs[k]! = true)
    (hm : m ≤ gs.size) :
    ∀ w : List (Fin m × Bool),
      Rep n (evalWA n gs w)
        (CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest.evalW
          (fun i => permOfArr n gs[i.val]!) w)
  | [] => rep_idA
  | x :: w => by
    rw [CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest.evalW_cons, evalWA]
    have hv := hval x.1.val (lt_of_lt_of_le x.1.2 hm)
    obtain ⟨i, b⟩ := x
    cases b
    · exact rep_compA (rep_inv_of_validA hv) (rep_evalWA hval hm w)
    · exact rep_compA (rep_of_validA hv) (rep_evalWA hval hm w)

theorem card_A6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

@[expose] def NoA6 {G : Type*} [Group G] (C : Subgroup G) : Prop :=
  ∀ H : Subgroup G, H ≤ C → ∀ f : H →* alternatingGroup (Fin 6), ¬ Function.Surjective f

theorem NoA6.mono {G : Type*} [Group G] {C C' : Subgroup G} (h : NoA6 C) (hle : C' ≤ C) :
    NoA6 C' := fun H hH f hf => h H (hH.trans hle) f hf

theorem NoA6.of_map {G G' : Type*} [Group G] [Group G'] (ψ : G →* G')
    (hψ : Function.Injective ψ) {C : Subgroup G} (h : NoA6 (C.map ψ)) : NoA6 C := by
  intro H hH f hf
  let e : H ≃* H.map ψ := H.equivMapOfInjective ψ hψ
  exact h (H.map ψ) (map_mono hH) (f.comp e.symm.toMonoidHom)
    (hf.comp e.symm.surjective)

theorem noA6_of_normal_pGroup {G : Type*} [Group G] {C A : Subgroup G} [Finite C] (hAC : A ≤ C)
    (hAn : (A.subgroupOf C).Normal) (hA3 : IsPGroup 3 A) {m : ℕ}
    (hm : Nat.card C = Nat.card A * m) (h360 : ¬ 360 ∣ m) : NoA6 C := by
  intro H hHC f hf
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite H := Finite.of_injective _ (Subgroup.inclusion_injective hHC)
  have : Finite A := Finite.of_injective _ (Subgroup.inclusion_injective hAC)
  set N := A.subgroupOf C
  let φ : H →* C ⧸ N := (QuotientGroup.mk' N).comp (Subgroup.inclusion hHC)
  have hmemA : ∀ k : φ.ker, ((k : H) : G) ∈ A := by
    intro k
    have hk : (QuotientGroup.mk (Subgroup.inclusion hHC (k : H)) : C ⧸ N) = 1 := k.2
    exact Subgroup.mem_subgroupOf.1
      ((QuotientGroup.eq_one_iff (N := N) (Subgroup.inclusion hHC (k : H))).1 hk)
  have hK3 : IsPGroup 3 φ.ker := by
    let ψ : φ.ker →* A :=
      { toFun := fun k => ⟨((k : H) : G), hmemA k⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine hA3.of_injective ψ fun a b hab => ?_
    have h' := congrArg (fun z : A => (z : G)) hab
    exact Subtype.ext (Subtype.ext h')
  have hKf : φ.ker ≤ f.ker := by
    have hnorm : (φ.ker.map f).Normal := (MonoidHom.normal_ker φ).map f hf
    have hsimple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (φ.ker.map f) with hb | ht
    · exact (Subgroup.map_eq_bot_iff _).1 hb
    · exfalso
      have h3 : IsPGroup 3 (φ.ker.map f) := hK3.map f
      rw [ht] at h3
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card.1 h3)
      rw [Subgroup.card_top, card_A6] at hk
      have h5 : 5 ∣ 3 ^ k := hk ▸ (by norm_num : 5 ∣ 360)
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_five h5) (by norm_num)
  have hH1 : Nat.card H = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have hH2 : Nat.card H = 360 * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv, card_A6]
  obtain ⟨t, ht⟩ := Subgroup.card_dvd_of_le hKf
  have hpos : 0 < Nat.card φ.ker := Nat.card_pos
  have hrange : Nat.card φ.range = 360 * t := by
    have : Nat.card φ.range * Nat.card φ.ker = 360 * t * Nat.card φ.ker := by
      rw [← hH1, hH2, ht]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hQ : Nat.card (C ⧸ N) = m := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv, hm] at h1
    have hApos : 0 < Nat.card A := Nat.card_pos
    have : Nat.card (C ⧸ N) * Nat.card A = m * Nat.card A := by rw [← h1]; ring
    exact Nat.eq_of_mul_eq_mul_right hApos this
  apply h360
  rw [← hQ]
  exact (Dvd.intro t hrange.symm).trans (Subgroup.card_subgroup_dvd_card φ.range)

theorem exists_conj_mem_of_card {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] {P Q : Subgroup G}
    [Finite P] (hQP : Q ≤ P) (hQ : Nat.card Q = p ^ (Nat.card P).factorization p) {x : G}
    (hx : x ∈ P) (hxo : orderOf x = p) : ∃ g ∈ P, g⁻¹ * x * g ∈ Q := by
  let S0 : Sylow p P := Sylow.ofCard (Q.subgroupOf P)
    (by rw [Nat.card_congr (subgroupOfEquivOfLe hQP).toEquiv, hQ])
  let x' : P := ⟨x, hx⟩
  have hx'o : orderOf x' = p := by rw [Subgroup.orderOf_mk]; exact hxo
  have hpg : IsPGroup p (zpowers x') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx'o, pow_one])
  obtain ⟨S, hS⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P S0 S
  have hmem : x' ∈ ((g • S0 : Sylow p P) : Subgroup P) := by
    rw [hg]
    exact hS (mem_zpowers x')
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv] at hmem
  refine ⟨g, g.2, ?_⟩
  have : ((g⁻¹ * x' * g : P) : G) ∈ Q := hmem
  simpa using this

theorem eq_bot_of_isPerfect_of_isPGroup {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {P : Subgroup G} [Finite P] (hP : IsPGroup p P) [Group.IsPerfect P] : P = ⊥ := by
  by_contra h
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).2 h
  exact Group.IsPerfect.not_isNilpotent P hP.isNilpotent

theorem le_commutator_of_isPerfect {G : Type*} [Group G] {P C : Subgroup G} (hPC : P ≤ C)
    [Group.IsPerfect P] : P ≤ ⁅C, C⁆ := by
  rw [← Subgroup.commutator_eq_self (H := P)]
  exact Subgroup.commutator_mono hPC hPC

theorem centralizer_pow_two_le {G : Type*} [Group G] {y : G} (hy : y ^ 3 = 1) :
    centralizer {y ^ 2} ≤ centralizer {y} := by
  intro z hz
  have hz' : z * y ^ 2 = y ^ 2 * z := mem_centralizer_singleton_iff.1 hz
  have hy4 : y = (y ^ 2) ^ 2 := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hy, one_mul, pow_one]
  rw [mem_centralizer_singleton_iff, hy4]
  exact ((Commute.pow_right hz' 2))

theorem exists_conj_rep {G : Type*} [Group G] {P Q : Subgroup G} [Finite P] (hQP : Q ≤ P)
    (hQ : Nat.card Q = 3 ^ (Nat.card P).factorization 3) {r : ℕ} (Lf Xf Hf : ℕ → G)
    (rec : ℕ → ℕ) (hlines : ∀ g ∈ Q, g ^ 3 = 1 → g = 1 ∨ ∃ j < r, ∃ e < 3, g = Lf j ^ e)
    (htrans : ∀ j < r, Hf j ∈ P ∧ Hf j * Xf (rec j) * (Hf j)⁻¹ = Lf j)
    {x : G} (hx : x ∈ P) (hxo : orderOf x = 3) :
    ∃ k ∈ P, ∃ j < r, ∃ e, (e = 1 ∨ e = 2) ∧ x = k * Xf (rec j) ^ e * k⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hgP, hgQ⟩ := exists_conj_mem_of_card hQP hQ hx hxo
  have hx3 : x ^ 3 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h; rw [h, orderOf_one] at hxo; norm_num at hxo
  have hy3 : (g⁻¹ * x * g) ^ 3 = 1 := by
    rw [show g⁻¹ * x * g = MulAut.conj g⁻¹ x by simp, ← map_pow, hx3,
      map_one]
  rcases hlines _ hgQ hy3 with h1 | ⟨j, hj, e, he, hje⟩
  · exfalso
    apply hx1
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this, h1]; group
  · obtain ⟨hHP, hHe⟩ := htrans j hj
    refine ⟨g * Hf j, P.mul_mem hgP hHP, j, hj, e, ?_, ?_⟩
    · interval_cases e
      · exfalso; rw [pow_zero] at hje; apply hx1
        have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        rw [this, hje]; group
      · exact Or.inl rfl
      · exact Or.inr rfl
    · have hL : Lf j ^ e = Hf j * Xf (rec j) ^ e * (Hf j)⁻¹ := by
        rw [← hHe, ← MulAut.conj_apply, ← MulAut.conj_apply, map_pow]
      have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      rw [this, hje, hL]; group

theorem noA6_conj {G : Type*} [Group G] {P : Subgroup G} {y k : G} (hk : k ∈ P) (hy : y ^ 3 = 1)
    (h : NoA6 (centralizer {y} ⊓ P)) {e : ℕ} (he : e = 1 ∨ e = 2) :
    NoA6 (centralizer {k * y ^ e * k⁻¹} ⊓ P) := by
  apply NoA6.of_map (MulAut.conj k⁻¹).toMonoidHom (MulAut.conj k⁻¹).injective
  apply h.mono
  rintro _ ⟨z, ⟨hzc, hzP⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · have hzc' : z * (k * y ^ e * k⁻¹) = (k * y ^ e * k⁻¹) * z :=
      mem_centralizer_singleton_iff.1 hzc
    have hc : (k⁻¹ * z * k) * y ^ e = y ^ e * (k⁻¹ * z * k) := by
      calc (k⁻¹ * z * k) * y ^ e = k⁻¹ * (z * (k * y ^ e * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * y ^ e * k⁻¹) * z) * k := by rw [hzc']
        _ = y ^ e * (k⁻¹ * z * k) := by group
    have hmem : k⁻¹ * z * k ∈ centralizer {y ^ e} := mem_centralizer_singleton_iff.2 hc
    show (MulAut.conj k⁻¹) z ∈ centralizer {y}
    rw [MulAut.conj_apply, inv_inv]
    rcases he with rfl | rfl
    · simpa using hmem
    · exact centralizer_pow_two_le hy hmem
  · show (MulAut.conj k⁻¹) z ∈ P
    rw [MulAut.conj_apply, inv_inv]
    exact P.mul_mem (P.mul_mem (P.inv_mem hk) hzP) hk

theorem noA6_centralizer_of_mulEquiv {G G' : Type*} [Group G] [Group G'] {P : Subgroup G'}
    (e : G ≃* P) {x : G} (h : NoA6 (centralizer {(e x : G')} ⊓ P)) :
    NoA6 (centralizer {x}) := by
  refine NoA6.of_map (P.subtype.comp e.toMonoidHom) (Subtype.val_injective.comp e.injective)
    (h.mono ?_)
  intro w hw
  obtain ⟨z, hz, rfl⟩ := mem_map.1 hw
  refine mem_inf.2 ⟨?_, (e z).2⟩
  rw [mem_centralizer_singleton_iff] at hz ⊢
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    Subgroup.coe_subtype]
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hz]

theorem noA6_all_of_mulEquiv {G G' : Type*} [Group G] [Group G'] {P : Subgroup G'}
    (e : G ≃* P) (h : ∀ x ∈ P, orderOf x = 3 → NoA6 (centralizer {x} ⊓ P)) :
    ∀ x : G, orderOf x = 3 → ∀ H : Subgroup G, H ≤ centralizer {x} →
      ∀ f : H →* alternatingGroup (Fin 6), ¬ Function.Surjective f := by
  intro x hx
  have hXo : orderOf ((e x : P) : G') = 3 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hx
  exact noA6_centralizer_of_mulEquiv e (h _ (e x).2 hXo)

end CFSG.RankThree.PartTwo.KFacts.K426
