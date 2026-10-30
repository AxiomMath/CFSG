module

public import CFSG.RankThree.PartTwo.Sec15.F153L3C2Quot
public import CFSG.RankThree.PartTwo.Sec15.F153L3C2Defs
public import CFSG.RankThree.PartTwo.Sec15.Item152ExclSL2
public import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
public import CFSG.RankThree.PartTwo.Sec13.Item13Res5ProofTools
import CFSG.RankThree.PartTwo.Sec15.Item15No135
import CFSG.GroupTheory.CyclicSylowNormalOddComplement
import CFSG.GroupTheory.PCore.SubgroupCore
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.KFacts.KS14PGL
import CFSG.RankThree.PartTwo.Sec4.Item462AltProofCases

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153L3C2

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15

section Generic

theorem quasi_normal_eq_top_of_nonabelian {Q : Type*} [Group Q] (hq : CFSG.IsQuasisimple Q)
    (N : Subgroup Q) [N.Normal] (hN : ∃ a b : ↥N, a * b ≠ b * a) : N = ⊤ := by
  rcases quasi_normal_le_center_or_eq_top hq N with h | h
  · obtain ⟨a, b, hab⟩ := hN
    exact (hab (Subtype.ext (Subgroup.mem_center_iff.mp (h b.2) (a : Q)))).elim
  · exact h

theorem false_of_quasi_nonabelian_pair {Q : Type*} [Group Q] (hq : CFSG.IsQuasisimple Q)
    (U V : Subgroup Q) [U.Normal] [V.Normal] (hU : ∃ a b : ↥U, a * b ≠ b * a)
    (hV : ∃ a b : ↥V, a * b ≠ b * a) (hUV : U ⊓ V = ⊥) : False := by
  have hU' := quasi_normal_eq_top_of_nonabelian hq U hU
  have hV' := quasi_normal_eq_top_of_nonabelian hq V hV
  rw [hU', hV', inf_top_eq] at hUV
  have hall : ∀ x : Q, x = 1 := by
    intro x
    have hx : x ∈ (⊤ : Subgroup Q) := Subgroup.mem_top x
    rw [hUV, Subgroup.mem_bot] at hx
    exact hx
  obtain ⟨a, b, hab⟩ := hU
  exact hab (Subtype.ext ((hall _).trans (hall _).symm))

theorem exists_noncomm_of_mulEquiv {H K : Type*} [Group H] [Group K] (e : H ≃* K)
    (hH : ∃ a b : H, a * b ≠ b * a) : ∃ a b : K, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := hH
  refine ⟨e a, e b, fun h => hab (e.injective ?_)⟩
  simpa using h

theorem nonempty_centerQuotient_equiv_of_simple' {Q T : Type*} [Group Q] [Group T]
    (hq : CFSG.IsQuasisimple Q) (hT : IsSimpleGroup T) (e : Q ≃* T) :
    Nonempty (Q ⧸ Subgroup.center Q ≃* T) := by
  haveI := hT
  have hQs : IsSimpleGroup Q := e.isSimpleGroup
  have hnab : ∃ a b : Q, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
  have hc : Subgroup.center Q = ⊥ :=
    CFSG.RankThree.PartTwo.Sec15.center_eq_bot_of_isSimpleGroup hQs hnab
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans e⟩

theorem equiv_of_quasi_of_simple {X S' T : Type*} [Group X] [Group S'] [Group T]
    (hXq : CFSG.IsQuasisimple X) (hS : IsSimpleGroup S') (e : X ≃* S')
    (hXT : Nonempty (X ⧸ Subgroup.center X ≃* T)) : Nonempty (T ≃* S') := by
  obtain ⟨f⟩ := hXT
  obtain ⟨g⟩ := nonempty_centerQuotient_equiv_of_simple' hXq hS e
  exact ⟨f.symm.trans g⟩

theorem isEmpty_mulEquiv_prod_of_quasi {X H₁ H₂ : Type*} [Group X] [Group H₁] [Group H₂]
    (hXq : CFSG.IsQuasisimple X) (h₁ : ∃ a b : H₁, a * b ≠ b * a)
    (h₂ : ∃ a b : H₂, a * b ≠ b * a) : IsEmpty (X ≃* H₁ × H₂) := by
  refine ⟨fun e => ?_⟩
  obtain ⟨a, b, hab⟩ := h₁
  obtain ⟨c, d, hcd⟩ := h₂
  obtain ⟨fU, hfU⟩ : ∃ f : X →* H₂, ∀ x, f x = (e x).2 :=
    ⟨(MonoidHom.snd H₁ H₂).comp e.toMonoidHom, fun x => rfl⟩
  obtain ⟨fV, hfV⟩ : ∃ f : X →* H₁, ∀ x, f x = (e x).1 :=
    ⟨(MonoidHom.fst H₁ H₂).comp e.toMonoidHom, fun x => rfl⟩
  have hmemU : ∀ x : X, x ∈ fU.ker ↔ (e x).2 = 1 := fun x => by
    rw [MonoidHom.mem_ker, hfU]
  have hmemV : ∀ x : X, x ∈ fV.ker ↔ (e x).1 = 1 := fun x => by
    rw [MonoidHom.mem_ker, hfV]
  have hU : ∃ x y : ↥fU.ker, x * y ≠ y * x := by
    refine ⟨⟨e.symm (a, 1), (hmemU _).mpr (by simp)⟩,
      ⟨e.symm (b, 1), (hmemU _).mpr (by simp)⟩, fun h => hab ?_⟩
    have h2 := congrArg (fun z : ↥fU.ker => e (z : X)) h
    simpa using h2
  have hV : ∃ x y : ↥fV.ker, x * y ≠ y * x := by
    refine ⟨⟨e.symm (1, c), (hmemV _).mpr (by simp)⟩,
      ⟨e.symm (1, d), (hmemV _).mpr (by simp)⟩, fun h => hcd ?_⟩
    have h2 := congrArg (fun z : ↥fV.ker => e (z : X)) h
    simpa using h2
  have hUV : fU.ker ⊓ fV.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [hmemU] at hx1
    rw [hmemV] at hx2
    rw [Subgroup.mem_bot]
    apply e.injective
    rw [map_one]
    exact Prod.ext hx2 hx1
  exact false_of_quasi_nonabelian_pair hXq fU.ker fV.ker hU hV hUV

theorem exists_noncomm_alternatingGroup {n : ℕ} (hn : 4 ≤ n) :
    ∃ a b : alternatingGroup (Fin n), a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  have hcomm : IsMulCommutative (alternatingGroup (Fin n)) := ⟨⟨fun a b => hc a b⟩⟩
  have h3 := alternatingGroup.isMulCommutative_iff_card_le_three.mp hcomm
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h3
  omega

theorem exists_noncomm_of_isTripleCover_A6 {W : Type*} [Group W]
    (hW : Sec4.IsTripleCover W (alternatingGroup (Fin 6))) : ∃ a b : W, a * b ≠ b * a := by
  obtain ⟨-, ⟨φ⟩⟩ := hW
  obtain ⟨a, b, hab⟩ := exists_noncomm_of_mulEquiv φ.symm
    (exists_noncomm_alternatingGroup (n := 6) (by norm_num))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨x, y, fun hxy => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxy]

theorem commutator_top_ne_bot_of_quasi {Q : Type*} [Group Q] (hq : CFSG.IsQuasisimple Q) :
    ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ≠ ⊥ := by
  intro h
  obtain ⟨hperf, -, ⟨a, b, hab⟩⟩ := hq
  have htop : (⊤ : Subgroup Q) = ⊥ := by
    rw [← hperf.commutator_eq_top]
    exact h
  have hall : ∀ x : Q, x = 1 := by
    intro x
    have hx : x ∈ (⊤ : Subgroup Q) := Subgroup.mem_top x
    rw [htop, Subgroup.mem_bot] at hx
    exact hx
  apply hab
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  rw [hall x, hall y]

theorem not_isCentralProductA6Covers_of_quasi {X : Type*} [Group X] (hXq : CFSG.IsQuasisimple X) :
    ¬ IsCentralProductA6Covers X := by
  rintro ⟨U, V, hU, hV, -, hcomm, -, hU6, hV6⟩
  have hUt : U = ⊤ :=
    quasi_normal_eq_top_of_nonabelian hXq U (exists_noncomm_of_isTripleCover_A6 hU6)
  have hVt : V = ⊤ :=
    quasi_normal_eq_top_of_nonabelian hXq V (exists_noncomm_of_isTripleCover_A6 hV6)
  rw [hUt, hVt] at hcomm
  exact commutator_top_ne_bot_of_quasi hXq hcomm

theorem not_isA6CoverTimesA5_of_quasi {X : Type*} [Group X] (hXq : CFSG.IsQuasisimple X) :
    ¬ IsA6CoverTimesA5 X := by
  rintro ⟨U, V, hU, hV, hUV, -, hU6, ⟨eV⟩⟩
  exact false_of_quasi_nonabelian_pair hXq U V (exists_noncomm_of_isTripleCover_A6 hU6)
    (exists_noncomm_of_mulEquiv eV.symm (exists_noncomm_alternatingGroup (n := 5) (by norm_num)))
    hUV

theorem quasi_quotient_of_central_ker {Q Q' : Type*} [Group Q] [Group Q']
    (hq : CFSG.IsQuasisimple Q) (φ : Q →* Q') (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Q) :
    CFSG.IsQuasisimple Q' ∧ Nonempty (Q' ⧸ Subgroup.center Q' ≃* Q ⧸ Subgroup.center Q) := by
  haveI : Group.IsPerfect Q := hq.1
  haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hq.2.1
  have hcenterQ : Subgroup.center (Q ⧸ Subgroup.center Q) = ⊥ :=
    CFSG.RankThree.PartTwo.Sec15.center_eq_bot_of_isSimpleGroup hq.2.1 hq.2.2
  have hkey : ∀ x : Q, φ x ∈ Subgroup.center Q' → x ∈ Subgroup.center Q := by
    intro x hx
    have hcentral : (QuotientGroup.mk x : Q ⧸ Subgroup.center Q) ∈
        Subgroup.center (Q ⧸ Subgroup.center Q) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective g
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      refine hker ?_
      rw [MonoidHom.mem_ker]
      have hc : φ q * φ x = φ x * φ q := Subgroup.mem_center_iff.mp hx (φ q)
      simp only [map_mul, map_inv]
      rw [hc, inv_mul_cancel]
    rw [hcenterQ, Subgroup.mem_bot] at hcentral
    exact (QuotientGroup.eq_one_iff x).mp hcentral
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Q →* Q' ⧸ Subgroup.center Q',
      ∀ x, ψ x = (φ x : Q' ⧸ Subgroup.center Q') :=
    ⟨(QuotientGroup.mk' (Subgroup.center Q')).comp φ, fun x => rfl⟩
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨x, rfl⟩ := hφ y'
    exact ⟨x, hψ x⟩
  have hψker : ψ.ker = Subgroup.center Q := by
    ext x
    rw [MonoidHom.mem_ker, hψ, QuotientGroup.eq_one_iff]
    constructor
    · exact hkey x
    · intro hx
      refine Subgroup.mem_center_iff.mpr (fun g' => ?_)
      obtain ⟨g, rfl⟩ := hφ g'
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx g]
  have hperf' : Group.IsPerfect Q' := Group.IsPerfect.ofSurjective hφ
  have he : Q ⧸ Subgroup.center Q ≃* Q' ⧸ Subgroup.center Q' :=
    (QuotientGroup.quotientMulEquivOfEq hψker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj)
  have hsimp' : IsSimpleGroup (Q' ⧸ Subgroup.center Q') := he.symm.isSimpleGroup
  have hnab' : ∃ a b : Q' ⧸ Subgroup.center Q', a * b ≠ b * a :=
    exists_noncomm_of_mulEquiv he hq.2.2
  have hQ' : CFSG.IsQuasisimple Q' := by
    unfold CFSG.IsQuasisimple
    exact ⟨hperf', hsimp', hnab'⟩
  exact ⟨hQ', ⟨he.symm⟩⟩

theorem three_dvd_card_of_isLThreeEpsAt {T : Type} [Group T] {f : ℕ} (hf : 1 ≤ f)
    (hT : IsLThreeEpsAt T 2 f) : 3 ∣ Nat.card T := by
  rcases hT with h1 | ⟨-, h2⟩
  · exact CFSG.RankThree.PartTwo.KFacts.three_dvd_card_of_mulEquiv_projSL h1.some
  · exact CFSG.RankThree.PartTwo.KFacts.three_dvd_card_of_mulEquiv_projSU (by omega) h2.some

theorem three_dvd_card_of_centerQuot {X T : Type*} [Group X] [Group T] [Finite X]
    (hXT : Nonempty (X ⧸ Subgroup.center X ≃* T)) (h3 : 3 ∣ Nat.card T) : 3 ∣ Nat.card X := by
  obtain ⟨e⟩ := hXT
  have hidx : (Subgroup.center X).index = Nat.card T := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr e.toEquiv
  have hdvd : (Subgroup.center X).index ∣ Nat.card X := Subgroup.index_dvd_card _
  rw [hidx] at hdvd
  exact dvd_trans h3 hdvd

end Generic

section Helpers

theorem three_dvd_card_of_isLThreeEpsAt_all {T : Type} [Group T] {f : ℕ}
    (hT : IsLThreeEpsAt T 2 f) : 3 ∣ Nat.card T := by
  have cyc : (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2) ^ 3 = 1 ∧
      Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 ≠ 1 ∧
      Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2) = 1 := by
    refine ⟨?_, ?_, ?_⟩ <;> decide
  rcases hT with hT1 | ⟨-, hT2⟩
  · obtain ⟨φ⟩ := hT1
    exact CFSG.RankThree.PartTwo.Sec13.Res5Proof.three_dvd_card_of_mulEquiv φ
      (CFSG.RankThree.PartTwo.Sec13.Res5Proof.three_dvd_card_projSL_of_perm
        (GaloisField 2 f) cyc.1 cyc.2.1 cyc.2.2)
  · obtain ⟨φ⟩ := hT2
    exact CFSG.RankThree.PartTwo.Sec13.Res5Proof.three_dvd_card_of_mulEquiv φ
      (CFSG.RankThree.PartTwo.Sec13.Res5Proof.three_dvd_card_projSU_of_perm
        (p := 2) (f := f) cyc.1 cyc.2.1 cyc.2.2)

end Helpers

section Helpers

theorem hj_nonabelian_alt5 : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := by
  refine ⟨⟨Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2, ?_⟩,
    ⟨Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 3, ?_⟩, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (show (0 : Fin 5) ≠ 1 by decide),
      Equiv.Perm.sign_swap (show (1 : Fin 5) ≠ 2 by decide)]
    rfl
  · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (show (0 : Fin 5) ≠ 1 by decide),
      Equiv.Perm.sign_swap (show (1 : Fin 5) ≠ 3 by decide)]
    rfl
  · intro h
    have h0 := congrArg (fun g : alternatingGroup (Fin 5) => (g : Equiv.Perm (Fin 5)) 0) h
    exact absurd h0 (by decide)

theorem hj_nonab_of_center_bot {H : Type*} [Group H] [Nontrivial H]
    (hc : Subgroup.center H = ⊥) : ∃ a b : H, a * b ≠ b * a := by
  by_contra hcon
  simp only [not_exists, ne_eq, not_not] at hcon
  have htop : Subgroup.center H = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact Subgroup.mem_center_iff.mpr (fun g => hcon g x)
  have htb : (⊤ : Subgroup H) = ⊥ := htop.symm.trans hc
  obtain ⟨x, hx⟩ := exists_ne (1 : H)
  have hxtop : x ∈ (⊤ : Subgroup H) := Subgroup.mem_top x
  rw [htb, Subgroup.mem_bot] at hxtop
  exact hx hxtop

theorem hj_exists_mul_of_mem_sup {Q : Type*} [Group Q] (U V : Subgroup Q)
    (hc : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) {x : Q} (hx : x ∈ U ⊔ V) :
    ∃ u ∈ U, ∃ v ∈ V, u * v = x := by
  let M : Subgroup Q :=
    { carrier := {y | ∃ u ∈ U, ∃ v ∈ V, u * v = y}
      mul_mem' := by
        rintro _ _ ⟨u, hu, v, hv, rfl⟩ ⟨u', hu', v', hv', rfl⟩
        show ∃ u₁ ∈ U, ∃ v₁ ∈ V, u₁ * v₁ = u * v * (u' * v')
        refine ⟨u * u', U.mul_mem hu hu', v * v', V.mul_mem hv hv', ?_⟩
        calc u * u' * (v * v') = u * (u' * v) * v' := by simp only [mul_assoc]
          _ = u * (v * u') * v' := by rw [hc u' hu' v hv]
          _ = u * v * (u' * v') := by simp only [mul_assoc]
      one_mem' := by
        show ∃ u₁ ∈ U, ∃ v₁ ∈ V, u₁ * v₁ = 1
        exact ⟨1, U.one_mem, 1, V.one_mem, mul_one 1⟩
      inv_mem' := by
        rintro _ ⟨u, hu, v, hv, rfl⟩
        show ∃ u₁ ∈ U, ∃ v₁ ∈ V, u₁ * v₁ = (u * v)⁻¹
        refine ⟨u⁻¹, U.inv_mem hu, v⁻¹, V.inv_mem hv, ?_⟩
        calc u⁻¹ * v⁻¹ = (v * u)⁻¹ := by group
          _ = (u * v)⁻¹ := by rw [hc u hu v hv] }
  have hmemM : ∀ y, y ∈ M ↔ ∃ u ∈ U, ∃ v ∈ V, u * v = y := fun y => Iff.rfl
  have hle : U ⊔ V ≤ M :=
    sup_le (fun u hu => (hmemM u).mpr ⟨u, hu, 1, V.one_mem, mul_one u⟩)
      (fun v hv => (hmemM v).mpr ⟨1, U.one_mem, v, hv, one_mul v⟩)
  obtain ⟨u, hu, v, hv, h⟩ := (hmemM x).mp (hle hx)
  exact ⟨u, hu, v, hv, h⟩

theorem hj_quasi_factor_eq_bot {Q : Type*} [Group Q] (X : Subgroup Q)
    (hXq : CFSG.IsQuasisimple X) (hXnab : ∃ a b : ↥X, a * b ≠ b * a)
    (U V : Subgroup Q) (hU : U ≤ X) (hV : V ≤ X) (hsup : U ⊔ V = X) (hinf : U ⊓ V = ⊥)
    (hc : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) : U = ⊥ ∨ V = ⊥ := by
  have hUC : U ≤ Subgroup.centralizer (V : Set Q) :=
    fun u hu => Subgroup.mem_centralizer_iff.mpr (fun v hv => (hc u hu v hv).symm)
  have hVC : V ≤ Subgroup.centralizer (U : Set Q) :=
    fun v hv => Subgroup.mem_centralizer_iff.mpr (fun u hu => hc u hu v hv)
  have hNU : (U.subgroupOf X).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hU).mpr ?_
    rw [← hsup]
    exact sup_le Subgroup.le_normalizer (hVC.trans (Subgroup.centralizer_le_normalizer _))
  have hNV : (V.subgroupOf X).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hV).mpr ?_
    rw [← hsup]
    exact sup_le (hUC.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  have hinfN : U.subgroupOf X ⊓ V.subgroupOf X = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have h0 : x.1 ∈ U ⊓ V := ⟨Subgroup.mem_subgroupOf.mp hx1, Subgroup.mem_subgroupOf.mp hx2⟩
    rw [hinf, Subgroup.mem_bot] at h0
    rw [Subgroup.mem_bot]
    exact Subtype.ext h0
  have hsupN : U.subgroupOf X ⊔ V.subgroupOf X = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    obtain ⟨u, hu, v, hv, huv⟩ :=
      hj_exists_mul_of_mem_sup U V hc (by rw [hsup]; exact hx)
    have hxeq : (⟨x, hx⟩ : ↥X) = (⟨u, hU hu⟩ : ↥X) * ⟨v, hV hv⟩ := Subtype.ext huv.symm
    rw [hxeq]
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr hu))
      (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mpr hv))
  have key2 : ∀ (N₁ N₂ : Subgroup ↥X) [N₁.Normal] [N₂.Normal],
      N₁ ⊓ N₂ = ⊥ → N₁ ⊔ N₂ = ⊤ → N₁ = ⊥ ∨ N₂ = ⊥ := by
    intro N₁ N₂ _ _ h1 h2
    rcases quasi_normal_le_center_or_eq_top hXq N₁ with hc1 | hT1
    · rcases quasi_normal_le_center_or_eq_top hXq N₂ with hc2 | hT2
      · exfalso
        have hall : (⊤ : Subgroup ↥X) ≤ Subgroup.center ↥X := by
          rw [← h2]
          exact sup_le hc1 hc2
        obtain ⟨a, b, hab⟩ := hXnab
        exact hab (Subgroup.mem_center_iff.mp (hall (Subgroup.mem_top a)) b).symm
      · left
        rw [hT2, inf_top_eq] at h1
        exact h1
    · right
      rw [hT1, top_inf_eq] at h1
      exact h1
  rcases key2 (U.subgroupOf X) (V.subgroupOf X) hinfN hsupN with h0 | h0
  · left
    rw [Subgroup.subgroupOf_eq_bot] at h0
    exact disjoint_self.mp (h0.mono_right hU)
  · right
    rw [Subgroup.subgroupOf_eq_bot] at h0
    exact disjoint_self.mp (h0.mono_right hV)

end Helpers


variable {G : Type} [Group G] [Finite G]

section HJ


theorem false_of_img148_l3char2 {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (h148 : Item148 A LB) {Y : Subgroup G} (hY : Y ∈ scriptY A) (hAab : IsMulCommutative A)
    (hHJ : AllPointsHJ A) (hch : Chosen136 A) (hList : KL3Char2NotList148)
    {T : Type} [Group T] {f : ℕ} (hf : 1 ≤ f) (hT : IsLThreeEpsAt T 2 f)
    (hXq : letI := ker148_normal hY.2
      CFSG.IsQuasisimple ↥(img148 A Y (deltaZero A LB Y)))
    (hXT : letI := ker148_normal hY.2
      Nonempty (↥(img148 A Y (deltaZero A LB Y)) ⧸ Subgroup.center ↥(img148 A Y (deltaZero A LB Y))
        ≃* T)) : False := by
  let := ker148_normal hY.2
  have hXq' : CFSG.IsQuasisimple ↥(img148 A Y (deltaZero A LB Y)) := hXq
  have hXT' : Nonempty (↥(img148 A Y (deltaZero A LB Y)) ⧸
      Subgroup.center ↥(img148 A Y (deltaZero A LB Y)) ≃* T) := hXT
  set X := img148 A Y (deltaZero A LB Y) with hX
  obtain ⟨hNA5, hNA6, hNA7, hNA10, hNON, hNJ2, hNL37⟩ := hList T f hf hT
  have hS5 : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  have hS7 : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  have hS10 : IsSimpleGroup (alternatingGroup (Fin 10)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hSJ2 : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 :=
    CFSG.Sporadic.J2.isSimpleGroup_J2
  have hnab5 : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := hj_nonabelian_alt5
  haveI : Nontrivial CFSG.Blueprint.NativeSporadic.J2 := hSJ2.toNontrivial
  have hnabJ2 := hj_nonab_of_center_bot (H := CFSG.Blueprint.NativeSporadic.J2)
    (KFacts.KS14.center_nativeJ2_eq_bot Sec4.Sporadic.rank3II_4_15)
  have hXnab : ∃ a b : ↥X, a * b ≠ b * a := by
    obtain ⟨-, -, a', b', hab⟩ := hXq'
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥X) a'
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥X) b'
    exact ⟨a, b, fun h => hab (by rw [← map_mul, ← map_mul, h])⟩
  have h3X : 3 ∣ Nat.card ↥X :=
    three_dvd_card_of_centerQuot hXT' (three_dvd_card_of_isLThreeEpsAt hf hT)
  have hLHJ : ∀ c' : G, Subgroup.zpowers c' ∈ omegaA A → ∀ L' ∈ lA A c', 3 ∣ Nat.card L' →
      Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) := by
    intro c' hc' L' hL' h3
    obtain ⟨Le, hLe, hJe⟩ := hHJ c' hc'
    rw [(hch.2 c' hc' Le hLe).2 L' hL'.1 h3]
    exact hJe
  have hAle : A ≤ Y ⊔ A := le_sup_right
  have key : ∀ J : Subgroup G, J ≤ Y → img148 A Y J = ⊥ →
      ∀ p f : ℕ, IsZ3PGLThreeAt ↥(img148 A Y (J ⊔ A)) p f → False := by
    intro J hJY hJ p f hZ
    rw [img148_sup (hJY.trans le_sup_left) hAle, hJ, bot_sup_eq] at hZ
    obtain ⟨a, b, hab⟩ := KFacts.KS14.ks15Z3PGLNonabelian _ p f hZ
    exact hab (img148_comm hAab a b)
  rcases (h148 Y hY).2 with h1 | h2 | h3 | h4 | h5 | h6 | h7
  ·
    have hX1 : X = ⊥ := img148_eq_bot_of_le h1
    obtain ⟨a, b, hab⟩ := hXnab
    have ha : a = 1 := Subtype.ext (Subgroup.mem_bot.mp (hX1 ▸ a.2))
    have hb : b = 1 := Subtype.ext (Subgroup.mem_bot.mp (hX1 ▸ b.2))
    exact hab (by rw [ha, hb])
  ·
    obtain ⟨c', hc', -, L', hL', hcases⟩ := h2
    rcases hcases with hφ | ⟨-, hφ⟩ | ⟨p', f', e', hp', hf', he', hiso', -⟩ | ⟨-, h3A6 | hφ⟩
    ·
      obtain ⟨φ⟩ := hφ
      have h3L : 3 ∣ Nat.card L' := by
        refine h3X.trans ?_
        rw [Nat.card_congr φ.toEquiv]
        exact Subgroup.card_quotient_dvd_card _
      obtain ⟨ψ⟩ := hLHJ c' hc' L' hL' h3L
      obtain ⟨θ⟩ := equiv_of_quasi_of_simple hXq' hSJ2 (φ.trans ψ) hXT'
      exact hNJ2.false θ
    ·
      obtain ⟨φ⟩ := hφ
      obtain ⟨θ⟩ := equiv_of_quasi_of_simple hXq' hS7 φ hXT'
      exact hNA7.false θ
    ·
      have hfe : f' * e' ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
      have h3L : 3 ∣ Nat.card L' :=
        (three_dvd_card_of_isoLThreePi' hfe hiso').trans (Subgroup.card_quotient_dvd_card _)
      obtain ⟨ψ⟩ := hLHJ c' hc' L' hL' h3L
      exact KFacts.KS14.ks17J2NotList.1 p' (f' * e') (isoLThreePi_of_mulEquiv' ψ hiso')
    ·
      obtain ⟨φ⟩ := hXT'
      obtain ⟨-, ⟨ψ⟩⟩ := h3A6
      exact hNA6.false (φ.symm.trans ψ)
    ·
      obtain ⟨φ⟩ := hφ
      obtain ⟨θ⟩ := equiv_of_quasi_of_simple hXq' hS5 φ hXT'
      exact hNA5.false θ
  ·
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h⟩ := h3
    rcases h with hON' | hCP | hA6A5 | hφ | hφ | ⟨_, hφ⟩
    ·
      obtain ⟨φ⟩ := hXT'
      obtain ⟨-, ⟨ψ⟩⟩ := hON'
      exact hNON.false (φ.symm.trans ψ)
    · exact not_isCentralProductA6Covers_of_quasi hXq' hCP
    · exact not_isA6CoverTimesA5_of_quasi hXq' hA6A5
    · obtain ⟨φ⟩ := hφ
      exact (isEmpty_mulEquiv_prod_of_quasi hXq' hj_nonabelian_alt5
        hj_nonabelian_alt5).false φ
    · obtain ⟨φ⟩ := hφ
      obtain ⟨θ⟩ := equiv_of_quasi_of_simple hXq' hS7 φ hXT'
      exact hNA7.false θ
    · obtain ⟨φ⟩ := hφ
      obtain ⟨θ⟩ := equiv_of_quasi_of_simple hXq'
        (CFSG.RankThree.PartTwo.Sec4.Item462AltProof.isSimpleGroup_projSL_three (GaloisField 7 1))
        φ hXT'
      exact (hNL37 _).false θ
  ·
    obtain ⟨⟨φ⟩, -⟩ := h4
    obtain ⟨θ⟩ := equiv_of_quasi_of_simple hXq' hS10 φ hXT'
    exact hNA10.false θ
  ·
    obtain ⟨c, hcA, L, n, m, hzc, hL, hn, hm, -, -, -, -, hLε, -, -⟩ := h5
    have hnm : 1 ≤ n * m := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have h3L : 3 ∣ Nat.card L :=
      (three_dvd_card_of_isLThreeEpsAt hnm hLε).trans (Subgroup.card_quotient_dvd_card _)
    obtain ⟨ψ⟩ := hLHJ c hzc L hL h3L
    exact (hList _ (n * m) hnm hLε).2.2.2.2.2.1.false ψ
  ·
    obtain ⟨⟨φ⟩, -⟩ := h6
    exact (isEmpty_mulEquiv_prod_of_quasi hXq' hnab5 hnabJ2).false φ
  ·
    obtain ⟨-, -, L₁, L₂, J₁, J₂, p₁, f₁, -, p₂, f₂, -, -, -, -, -, -, -, hJ₁, hJ₂, hsup, hinf,
      hcomm, -, -, -, -, hZ₁, hZ₂, -, -⟩ := h7
    rw [← hX] at hsup
    have hJ₁le : img148 A Y J₁ ≤ X := hsup ▸ le_sup_left
    have hJ₂le : img148 A Y J₂ ≤ X := hsup ▸ le_sup_right
    have hc : ∀ u ∈ img148 A Y J₁, ∀ v ∈ img148 A Y J₂, u * v = v * u := by
      intro u hu v hv
      have h0 := Subgroup.commutator_mem_commutator hu hv
      rw [hcomm, Subgroup.mem_bot] at h0
      exact commutatorElement_eq_one_iff_mul_comm.mp h0
    rcases hj_quasi_factor_eq_bot X hXq' hXnab (img148 A Y J₁) (img148 A Y J₂) hJ₁le hJ₂le
      hsup hinf hc with h0 | h0
    · exact key J₁ (hJ₁.trans inf_le_right) h0 p₁ f₁ hZ₁
    · exact key J₂ (hJ₂.trans inf_le_right) h0 p₂ f₂ hZ₂

theorem img148_quasisimple_of_scriptY0 (h134 : Item134) (h48 : Sec4.Item4_8)
    {A L : Subgroup G} {c : G} (h : Sec15R G A c L) {Y : Subgroup G}
    (hY : Y ∈ scriptY0 A (lB A)) {T : Type} [Group T] {f : ℕ} (hT : IsLThreeEpsAt T 2 f)
    (e : (↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) ≃* T) :
    letI := ker148_normal hY.1.1.2
    CFSG.IsQuasisimple ↥(img148 A Y (deltaZero A (lB A) Y)) ∧
      Nonempty (↥(img148 A Y (deltaZero A (lB A) Y)) ⧸
        Subgroup.center ↥(img148 A Y (deltaZero A (lB A) Y)) ≃* T) := by
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.1.1.2
  have hY3 : Y = oPrimeResidualOf 3 Y := hY.1.2.1
  have hYdelta : Y = delta A (lB A) Y := hY.1.2.2.1
  have hYq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := hY.1.2.2.2
  have hΔ0 : Y = deltaZero A (lB A) Y :=
    eq_deltaZero_of_eq_delta' h134 CFSG.Sporadic.J2.isSimpleGroup_J2 h48
      Sec4.Sporadic.rank3II_4_15 (KFacts.KS14.center_nativeJ2_eq_bot Sec4.Sporadic.rank3II_4_15)
      h.toSec14Std hAY hY3 hYdelta
  rw [← hΔ0]
  have hpc2 : CFSG.pCore 2 ↥Y ≤ CFSG.pPrimeCore 3 ↥Y := by
    have hN : (CFSG.pCore 2 ↥Y).Normal := CFSG.pCore_normal (p := 2) (G := ↥Y)
    have hcop : Nat.Coprime 3 (Nat.card (CFSG.pCore 2 ↥Y)) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥Y))
      rw [hn]
      exact Nat.Coprime.pow_right n (by norm_num)
    exact CFSG.le_pPrimeCore_of_normal_coprime (p := 3) (G := ↥Y) hN hcop
  let φ' : (↥Y ⧸ CFSG.pCore 2 ↥Y) →* (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) :=
    QuotientGroup.map (CFSG.pCore 2 ↥Y) (CFSG.pPrimeCore 3 ↥Y) (MonoidHom.id ↥Y)
      (fun x hx => hpc2 hx)
  have hsurj : Function.Surjective φ' := by
    intro y
    obtain ⟨y0, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥Y) y
    exact ⟨(QuotientGroup.mk y0 : ↥Y ⧸ CFSG.pCore 2 ↥Y), rfl⟩
  obtain ⟨φ⟩ := nonempty_img148_equiv hAY
  rcases quasi_normal_le_center_or_eq_top hYq φ'.ker with hker | htop
  · obtain ⟨hqY, ⟨eY⟩⟩ := quasi_quotient_of_central_ker hYq φ' hsurj hker
    refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv φ.symm hqY, ⟨?_⟩⟩
    exact (QuotientGroup.congr (Subgroup.center _) (Subgroup.center _) φ
      (Subgroup.map_center_eq φ)).trans (eY.trans e)
  · exfalso
    have hpc : CFSG.pPrimeCore 3 ↥Y = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have hy : (QuotientGroup.mk y : ↥Y ⧸ CFSG.pCore 2 ↥Y) ∈ φ'.ker := by
        rw [htop]
        exact Subgroup.mem_top _
      rw [MonoidHom.mem_ker] at hy
      exact (QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 3 ↥Y) y).mp hy
    have hc := CFSG.coprime_card_pPrimeCore 3 ↥Y
    rw [hpc, Subgroup.card_top] at hc
    have h3T : 3 ∣ Nat.card T := three_dvd_card_of_isLThreeEpsAt_all hT
    have hcZ : Nat.card T ∣ Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
      rw [← Nat.card_congr e.toEquiv]
      exact Subgroup.card_dvd_of_surjective
        (f := QuotientGroup.mk' (Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)))
        (QuotientGroup.mk'_surjective _)
    have hdvd : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) ∣ Nat.card ↥Y :=
      Subgroup.card_dvd_of_surjective (f := QuotientGroup.mk' (CFSG.pCore 2 ↥Y))
        (QuotientGroup.mk'_surjective _)
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hc ((h3T.trans hcZ).trans hdvd)


theorem false_of_hj_stage (h134 : Item134) (h48 : Sec4.Item4_8) (h148 : Item148HJS14)
    (hList : KL3Char2NotList148) {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (hHJ : AllPointsHJ A) {Y : Subgroup G} (hY : Y ∈ scriptY0 A (lB A)) {f : ℕ} (hf : 1 ≤ f)
    (hε : IsLThreeEpsAt ((↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) 2 f) :
    False := by
  obtain ⟨hXq, hXT⟩ := img148_quasisimple_of_scriptY0 h134 h48 h hY hε (MulEquiv.refl _)
  exact false_of_img148_l3char2 (h148 G A c L h.toSec14Std hHJ) hY.1.1 h.isElemAbelian.1 hHJ
    h.chosen136 hList hf hε hXq hXT

end HJ

end CFSG.RankThree.PartTwo.Sec15.F153L3C2
