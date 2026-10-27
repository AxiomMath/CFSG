module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitSUDim
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitSUMove
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalUInner
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLNonsplitGroup

public section

namespace CFSG.StandardType

namespace OrdPNsU

open Matrix Module CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups SUTB NoOffOm CFSG.RankThree.PartOne.KCUnitaryPlane

section Order

variable {f n : ℕ} {K : Type} [Field K] {p : ℕ} {A : Subgroup ↥(unitarySU 2 f K n)}

theorem card_le_pow_ordNegQ (h : UnitaryFieldData 2 f K) (hA : MaxElemAb p A) :
    Nat.card A ≤ p ^ (n / ordNegQ 2 f p) := by
  have : Finite K := h.finite
  obtain ⟨S, hS, hterm⟩ := exists_terminal_pieceSet (h := h) hA
  rw [card_eq_pow_of_terminal h hA hS hterm]
  refine Nat.pow_le_pow_right hA.prime.pos ?_
  have he := ordNegQ_pos (f := f) hA.prime hA.ne_two
  rw [Nat.le_div_iff_mul_le he]
  have hle : ∀ y ∈ S, ordNegQ 2 f p ≤ finrank K (rng y) := by
    intro y hy
    refine Nat.le_of_dvd ?_ (ordNegQ_dvd_finrank_rng h hA.prime hA.ne_two
      (hA.pow y (hS.mem y hy)))
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact rng_ne_bot (hS.ne_one y hy)
  calc S.card * ordNegQ 2 f p = ∑ _y ∈ S, ordNegQ 2 f p := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ y ∈ S, finrank K (rng y) := Finset.sum_le_sum hle
    _ = finrank K (pieceSpan S) := (finrank_pieceSpan h hA hS).symm
    _ ≤ finrank K (Fin n → K) := Submodule.finrank_le _
    _ = n := Module.finrank_fin_fun K

theorem pow_ordNegQ_le_card (h : UnitaryFieldData 2 f K) (hA : MaxElemAb p A)
    (hne : ∃ c ∈ A, c ≠ 1) : p ^ (n / ordNegQ 2 f p) ≤ Nat.card A := by
  classical
  have : Finite K := h.finite
  have hp := hA.prime
  have hp2 := hA.ne_two
  obtain ⟨S, hS, hterm⟩ := exists_terminal_pieceSet (h := h) hA
  rw [card_eq_pow_of_terminal h hA hS hterm]
  refine Nat.pow_le_pow_right hp.pos ?_
  have he := ordNegQ_pos (f := f) hp hp2
  obtain ⟨y₀, hy₀⟩ : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    obtain ⟨c, hc, hc1⟩ := hne
    exact hc1 (hterm c hc fun v hv => by
      have : v = 0 := by simpa [pieceSpan] using hv
      rw [this, map_zero])
  have hdim : ∀ y ∈ S, finrank K (rng y) = ordNegQ 2 f p := by
    intro y hy
    have hyA := hS.mem y hy
    have hne0 : rng y ≠ ⊥ := rng_ne_bot (hS.ne_one y hy)
    refine le_antisymm (finrank_le_ordNegQ_of_minimal h hp hp2 (hA.pow y hyA) le_rfl hne0
      (nondegOn_rng hA hyA) (rng_inv hA hyA hyA) fun W hWle hW0 hWnd hWy =>
        OrdPNsU.IsPieceSet.minimal h hA hS hy hWle hW0 hWnd hWy) ?_
    refine Nat.le_of_dvd ?_ (ordNegQ_dvd_finrank_rng h hp hp2 (hA.pow y hyA))
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact hne0
  have hX : finrank K (pieceSpan S) = S.card * ordNegQ 2 f p := by
    rw [finrank_pieceSpan h hA hS, Finset.sum_congr rfl hdim, Finset.sum_const, smul_eq_mul]
  have hW := finrank_orth_pieceSpan_lt h hA hS hterm hy₀
  rw [hdim y₀ hy₀] at hW
  have hcompl := CFSG.RankThree.PartOne.OddIso.isCompl_orthogonalBilin_of_sep
    (B := stdHermForm h n) (hS.nondegOn_card hA).1
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  rw [Module.finrank_fin_fun, hX] at hsum
  have hlt : n < (S.card + 1) * ordNegQ 2 f p := by
    rw [Nat.succ_mul]
    omega
  exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul he).mpr hlt)

end Order

section Exists

variable {f n : ℕ} {K : Type} [Field K] {p : ℕ}

theorem closure_comm_pow {G : Type*} [Group G] {S : Set G}
    (hc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hp : ∀ x ∈ S, x ^ p = 1) :
    (∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a) ∧
      ∀ a ∈ Subgroup.closure S, a ^ p = 1 := by
  have hcomm : IsMulCommutative (Subgroup.closure S) :=
    Subgroup.isMulCommutative_closure fun x hx y hy _ => hc x hx y hy
  have hc' : ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  refine ⟨hc', fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hp x hx
  | one => exact one_pow p
  | mul x y hx hy ihx ihy =>
    rw [(show Commute x y from hc' x hx y hy).mul_pow, ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

theorem exists_maxElemAb_containing {ι : Type*} (h : UnitaryFieldData 2 f K) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : ¬ p ∣ 2 ^ f + 1)
    (U : ι → ↥(unitarySU 2 f K n)) (hpow : ∀ i, U i ^ p = 1)
    (hcomm : ∀ i j, U i * U j = U j * U i) :
    ∃ P : Subgroup ↥(unitarySU 2 f K n), MaxElemAb p P ∧ ∀ i, U i ∈ P := by
  classical
  have : Finite K := h.finite
  set S : Set ↥(unitarySU 2 f K n) := Set.range U with hS
  have hScomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hcomm i j
  have hSpow : ∀ a ∈ S, a ^ p = 1 := by
    rintro _ ⟨i, rfl⟩
    exact hpow i
  set Q : Subgroup ↥(unitarySU 2 f K n) → Prop := fun E =>
    S ⊆ E ∧ (∀ a ∈ E, a ^ p = 1) ∧ ∀ a ∈ E, ∀ b ∈ E, a * b = b * a with hQ
  set Pq : ℕ → Prop := fun k => ∃ E, Q E ∧ Nat.card E = k with hPq
  have hQ0 : Q (Subgroup.closure S) := by
    have h1 := closure_comm_pow (p := p) hScomm hSpow
    exact ⟨Subgroup.subset_closure, h1.2, h1.1⟩
  have hbound : ∀ k, Pq k → k ≤ Nat.card ↥(unitarySU 2 f K n) := by
    rintro k ⟨E, -, rfl⟩
    exact Subgroup.card_le_card_group E
  have hPq0 : Pq (Nat.card (Subgroup.closure S)) := ⟨_, hQ0, rfl⟩
  set N := Nat.findGreatest Pq (Nat.card ↥(unitarySU 2 f K n)) with hN
  obtain ⟨E, hE, hEN⟩ : Pq N := Nat.findGreatest_spec (hbound _ hPq0) hPq0
  refine ⟨E, ⟨hp, hp2, hpq, hE.2.1, hE.2.2, fun g hg hgE => ?_⟩, fun i => hE.1 ⟨i, rfl⟩⟩
  set E' := Subgroup.closure ((E : Set ↥(unitarySU 2 f K n)) ∪ {g}) with hE'
  have h1 := closure_comm_pow (S := (E : Set ↥(unitarySU 2 f K n)) ∪ {g}) (p := p)
    (by
      rintro x (hx | hx) y (hy | hy)
      · exact hE.2.2 x hx y hy
      · rw [Set.mem_singleton_iff.mp hy]; exact (hgE x hx).symm
      · rw [Set.mem_singleton_iff.mp hx]; exact hgE y hy
      · rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy])
    (by
      rintro x (hx | hx)
      · exact hE.2.1 x hx
      · rw [Set.mem_singleton_iff.mp hx]; exact hg)
  have hEE' : E ≤ E' := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hSE' : S ⊆ E' := fun x hx => hEE' (hE.1 hx)
  have hQ' : Q E' := ⟨hSE', h1.2, h1.1⟩
  have hcard : Nat.card E' ≤ Nat.card E := by
    rw [hEN]
    exact Nat.le_findGreatest (hbound _ ⟨E', hQ', rfl⟩) ⟨E', hQ', rfl⟩
  have heq : E = E' := Subgroup.eq_of_le_of_card_ge hEE' hcard
  rw [heq]
  exact Subgroup.subset_closure (Or.inr rfl)

theorem exists_maxElemAb_mem (h : UnitaryFieldData 2 f K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ 2 ^ f + 1) {u : ↥(unitarySU 2 f K n)} (hu : u ^ p = 1) :
    ∃ E : Subgroup ↥(unitarySU 2 f K n), MaxElemAb p E ∧ u ∈ E := by
  obtain ⟨E, hE, huE⟩ := exists_maxElemAb_containing h hp hp2 hpq
    (fun _ : Unit => u) (fun _ => hu) (fun _ _ => rfl)
  exact ⟨E, hE, huE ()⟩
end Exists

section Setting

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)

include hF in
theorem exists_conj_mem_centralizer_nonsplit {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs G₀ : Subgroup G} (hf : 1 ≤ f) {ψ : SU (unitaryInvolution F 2 f) n →* G}
    (hS : GGSixFusionSetting p Bs G₀ (Unitary.rootDatum hF n) .PSU n f ψ)
    (hpq : ¬ p ∣ 2 ^ f + 1) {y : G} (hyp : y ^ p = 1)
    (hy : GGPsiInnerDiag (Unitary.rootDatum hF n) ψ y) :
    ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : UnitaryFieldData 2 f F := ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨⟨-, hrank⟩, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  have hrk : 2 ≤ n / 2 := hrank
  have hn : 4 ≤ n := by omega
  have hpp := hS.prime
  have hp2 := hS.ne_two
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hS.centralizer_eq_bot
  have hcop : Nat.Coprime p (Nat.gcd n (2 ^ f + 1)) :=
    (Nat.Prime.coprime_iff_not_dvd hpp).mpr fun hd => hpq (hd.trans (Nat.gcd_dvd_right _ _))
  obtain ⟨P₀, hP₀⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hF n
  set φ := SURep.ggFrameU hF ψ P₀ hP₀ with hφ
  have hrφ : φ.range = G₀ := (SURep.range_ggFrameU hF ψ P₀ hP₀).trans hrange
  have hker₁ : φ.ker ≤ Subgroup.center ↥(unitarySU 2 f F n) :=
    SURep.ker_ggFrameU_le hF ψ P₀ hP₀ hker
  have hn3 : 3 ≤ n := by omega
  have hnq : (n, 2 ^ f) ≠ (3, 2) := fun h' => by
    have := congrArg Prod.fst h'
    simp only at this
    omega
  obtain ⟨u, hu, hup⟩ :=
    OrdPInnerSU.exists_eq_frame_of_innerDiag hF hf hn hker hC hP₀ hcop hy hyp
  rw [← hφ] at hu
  by_cases hu1 : u = 1
  · refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [← hu, hu1, map_one, inv_one, one_mul, one_mul]
    exact Subgroup.one_mem _
  have hnp : ∀ z : ↥(unitarySU 2 f F n), φ z = 1 → z ^ p = 1 → z = 1 := by
    intro z hz hzp
    obtain ⟨e, he⟩ := SURep.ggFrameKer_of_ker_le_center hF hn3 hnq hker₁ z hz
    obtain ⟨-, huni⟩ := (mem_unitarySU_iff h).mp z.2
    rw [he, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one] at huni
    have hbar := congrFun (Matrix.diagonal_injective huni) ⟨0, by omega⟩
    simp only [UnitaryFieldData.bar_apply] at hbar
    have heq : e ^ (2 ^ f + 1) = 1 := by rw [pow_succ]; exact hbar
    have hep : e ^ p = 1 := by
      have h1 := congrArg (fun g : ↥(unitarySU 2 f F n) =>
        ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) hzp
      simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, he, ← map_pow, OneMemClass.coe_one,
        Units.val_one] at h1
      have h2 := congrFun (congrFun h1 ⟨0, by omega⟩) ⟨0, by omega⟩
      simpa [Matrix.scalar_apply] using h2
    have he1 : e = 1 := by
      have h1 := pow_gcd_eq_one.mpr ⟨hep, heq⟩
      rwa [((Nat.Prime.coprime_iff_not_dvd hpp).mpr hpq).gcd_eq_one, pow_one] at h1
    apply Subtype.ext
    apply Units.ext
    rw [he, he1, map_one]
    rfl
  have hBsφ : Bs ≤ φ.range := fun b hb => by
    obtain ⟨s, hs, -⟩ := OrdPInnerSU.exists_eq_frame_of_innerDiag hF hf hn hker hC hP₀ hcop
      (hS.innerDiag b hb) (hS.elem.2 b hb)
    exact ⟨s, hs⟩
  have hAb : IsElemAbelian p (Bs.subgroupOf φ.range) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun a ha => Subtype.ext ?_⟩
    · exact TableB.IsElemAbelian.comm hS.elem (Subgroup.mem_subgroupOf.mp a.2)
        (Subgroup.mem_subgroupOf.mp b.2)
    · simpa using hS.elem.2 _ (Subgroup.mem_subgroupOf.mp ha)
  have hnp' : ∀ z ∈ φ.rangeRestrict.ker, z ^ p = 1 → z = 1 := fun z hz hzp => by
    rw [MonoidHom.ker_rangeRestrict] at hz
    exact hnp z hz hzp
  obtain ⟨A, hAmap, -, hA, hAcard⟩ := TableBUE.exists_lift_of_noTorsion φ.rangeRestrict
    φ.rangeRestrict_surjective hpp hnp' hAb
  have hlift : ∀ b ∈ Bs, ∃ a ∈ A, φ a = b := by
    intro b hb
    have hb' : (⟨b, hBsφ hb⟩ : φ.range) ∈ Bs.subgroupOf φ.range := Subgroup.mem_subgroupOf.mpr hb
    rw [← hAmap] at hb'
    obtain ⟨a, ha, hae⟩ := hb'
    exact ⟨a, ha, congrArg Subtype.val hae⟩
  have hAφ : ∀ a ∈ A, φ a ∈ Bs := by
    intro a ha
    have h1 : φ.rangeRestrict a ∈ Bs.subgroupOf φ.range := by
      rw [← hAmap]
      exact ⟨a, ha, rfl⟩
    exact Subgroup.mem_subgroupOf.mp h1
  have hAmax : MaxElemAb p A := by
    refine ⟨hpp, hp2, hpq, fun a ha => hA.2 a ha,
      fun a ha b hb => TableB.IsElemAbelian.comm hA ha hb, fun g hgp hgA => ?_⟩
    have hgc : φ g ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨a, haA, rfl⟩ := hlift b hb
      rw [← map_mul, ← map_mul, hgA a haA]
    have hgB : φ g ∈ Bs := hS.omega _ hgc (by rw [← map_pow, hgp, map_one])
    obtain ⟨a, haA, hag⟩ := hlift _ hgB
    have h1 : a⁻¹ * g = 1 := by
      refine hnp _ (by rw [map_mul, map_inv, hag, inv_mul_cancel]) ?_
      have hcomm : Commute a⁻¹ g := (show Commute g a from hgA a haA).symm.inv_left
      rw [hcomm.mul_pow, inv_pow, hA.2 a haA, hgp, inv_one, one_mul]
    rw [← inv_mul_eq_one.mp h1]
    exact haA
  have hAcard' : Nat.card A = Nat.card Bs := by
    rw [hAcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBsφ).toEquiv
  obtain ⟨E, hE, huE⟩ := exists_maxElemAb_mem h hpp hp2 hpq hup
  have hcardE : Nat.card A ≤ Nat.card E :=
    (card_le_pow_ordNegQ h hAmax).trans (pow_ordNegQ_le_card h hE ⟨u, huE, hu1⟩)
  have hEel : IsElemAbelian p E :=
    ⟨⟨⟨fun a b => Subtype.ext (hE.comm _ a.2 _ b.2)⟩⟩, hE.pow⟩
  have hinj : Function.Injective (φ.comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hnp x hx (hE.pow x x.2))
  have hEcard : Nat.card (E.map φ) = Nat.card E := by
    have hr : (φ.comp E.subtype).range = E.map φ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hr]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hEM : E.map φ ≤ Subgroup.normalizer (G₀ : Set G) := by
    rintro _ ⟨x, -, rfl⟩
    exact Subgroup.le_normalizer (hrφ ▸ ⟨x, rfl⟩)
  have hEφ : IsElemAbelian p (E.map φ) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, x, hx, rfl⟩ := a
      obtain ⟨_, z, hz, rfl⟩ := b
      apply Subtype.ext
      change φ x * φ z = φ z * φ x
      rw [← map_mul, ← map_mul, TableB.IsElemAbelian.comm hEel hx hz]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hEel.2 x hx, map_one]
  refine OrdPNS.exists_conj_mem_centralizer_of_card hS hEM hEφ
    (by rw [hEcard, ← hAcard']; exact hcardE) ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [← hu, ← map_mul, ← map_mul, hE.comm u huE x hx]

end Setting

end OrdPNsU

section Family

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

theorem ggOrdPInnerConjPSUNonsplit_holds : GGOrdPInnerConjPSUNonsplit := by
  intro G _ _ p Bs G₀ n f ψ hS _ hpq y _ hyo hy
  have hyp : y ^ p = 1 := hyo ▸ pow_orderOf_eq_one y
  have hf : 1 ≤ f := hS.presents.1.1.2.1
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  exact OrdPNsU.exists_conj_mem_centralizer_nonsplit
    (F := GaloisField 2 (2 * (f + 1))) (card_galoisField_two_mul 2 (f + 1) (by omega)) (by omega)
    hS hpq hyp hy

theorem ggOrdPInnerConjAt_PSU : GGOrdPInnerConjAt .PSU :=
  ggOrdPInnerConjAt_PSU_of_nonsplit ggOrdPInnerConjPSUNonsplit_holds

end Family

end CFSG.StandardType
