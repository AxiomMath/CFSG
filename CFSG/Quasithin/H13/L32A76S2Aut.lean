module

public import CFSG.Quasithin.Background.A3StructureDefs
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin.H13.L32A.S2

open CFSG.Open CFSG.Quasithin

theorem not_comm_of_card {X : Type*} [Group X] [IsSimpleGroup X]
    (h168 : Nat.card X = 168) : ¬ ∀ a b : X, a * b = b * a := by
  intro hc
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [h168]; norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 2 (by rw [h168]; norm_num)
  have hN : (Subgroup.zpowers x).Normal := ⟨fun n hn g => by
    rw [hc g n, mul_inv_cancel_right]
    exact hn⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x) with h | h
  · rw [Subgroup.zpowers_eq_bot] at h
    rw [h, orderOf_one] at hx
    norm_num at hx
  · have h1 := Nat.card_zpowers x
    rw [h, Subgroup.card_top, h168, hx] at h1
    norm_num at h1

theorem le_of_nilpotent_of_card {X : Type*} [Group X] {F N : Subgroup X} [F.Normal] [N.Normal]
    [IsSimpleGroup (X ⧸ N)] (hnil : Group.IsNilpotent F) (h168 : Nat.card (X ⧸ N) = 168) :
    F ≤ N := by
  have hn : (F.map (QuotientGroup.mk' N)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective N)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (F.map (QuotientGroup.mk' N)) with h | h
  · intro f hf
    have : QuotientGroup.mk' N f ∈ F.map (QuotientGroup.mk' N) := ⟨f, hf, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff f).mp this
  · exfalso
    have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp F.subtype) := by
      rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype]
      exact h
    have : Group.IsNilpotent (X ⧸ N) := Group.nilpotent_of_surjective _ hsurj
    have hc : Subgroup.center (X ⧸ N) ≠ ⊥ := Group.IsNilpotent.center_ne_bot (X ⧸ N)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (X ⧸ N)) with h' | h'
    · exact hc h'
    · apply not_comm_of_card h168
      intro a b
      have ha : a ∈ Subgroup.center (X ⧸ N) := h' ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm

theorem card_SL_two_zmod (p : ℕ) [Fact p.Prime] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) = (p ^ 2 - 1) * p := by
  rw [Matrix.card_SL_field, ZMod.card, Fin.prod_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  have hp1 : 0 < p - 1 := by have := (Fact.out : p.Prime).two_le; omega
  have e : p ^ 2 - p = p * (p - 1) := by rw [Nat.mul_sub_one, sq]
  rw [e, ← mul_assoc, Nat.mul_div_cancel _ hp1]

theorem eq_seven_of_card {p k : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hk1 : 1 ≤ k) (hk2 : k ≤ 2)
    (h : k * 168 = (p ^ 2 - 1) * p) : p = 7 := by
  have hp8 : p < 8 := by
    by_contra hcon
    have hcon : 8 ≤ p := by omega
    have h1 : 64 ≤ p ^ 2 := by nlinarith
    have h2 : 63 ≤ p ^ 2 - 1 := by omega
    have h3 : 63 * 8 ≤ (p ^ 2 - 1) * p := Nat.mul_le_mul h2 hcon
    omega
  interval_cases p
  all_goals first
    | rfl
    | (exfalso; norm_num at hp; done)
    | (exfalso; norm_num at h; try omega)

theorem card_center_SL_two_le (p : ℕ) [Fact p.Prime] :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) ≤ 2 := by
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity).toEquiv]
  have : NeZero (max (Fintype.card (Fin 2)) 1) := ⟨by simp⟩
  exact (card_rootsOfUnity _ _).trans (by simp)

theorem aut_eq_one_of_case3 {X : Type} [Group X] [Finite X] (h3 : A36Case3 X) (N : Subgroup X)
    [N.Normal] (hs : IsSimpleGroup (X ⧸ N)) (h168 : Nat.card (X ⧸ N) = 168) (α : MulAut X)
    (hα5 : α ^ 5 = 1) (hα : ∀ x : X, α x * x⁻¹ ∈ N) : α = 1 := by
  classical
  have := hs
  obtain ⟨p, hp, hp3, -, -, e, ψ, hψs, hψk, -⟩ := h3
  have : Fact p.Prime := ⟨hp⟩
  have hFN : CFSG.fittingSubgroup X ≤ N := le_of_nilpotent_of_card inferInstance h168
  have hcardF : Nat.card ↥(CFSG.fittingSubgroup X) = p ^ 2 := by
    rw [Nat.card_congr (e.toEquiv.trans Multiplicative.toAdd)]
    simp
  have hexpF : ∀ f : ↥(CFSG.fittingSubgroup X), f ^ p = 1 := by
    intro f
    apply e.injective
    rw [map_pow, map_one]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    ext i
    simp
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have h4 : (2 : ZMod p) ^ 2 ≠ 1 := by
    intro h
    have h' : ((3 : ℕ) : ZMod p) = 0 := by
      have : (2 : ZMod p) ^ 2 - 1 = 0 := by rw [h, sub_self]
      have e3 : (2 : ZMod p) ^ 2 - 1 = ((3 : ℕ) : ZMod p) := by push_cast; ring
      rw [← e3, this]
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have hperf : commutator (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) = ⊤ :=
    Matrix.SL2.commutator_eq_top h2 h4
  have hcard4 : 4 ≤ Nat.card (ZMod p) := by rw [Nat.card_zmod]; omega
  have hPSL : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p) ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcard4
  have hNψn : (N.map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψs
  have hNψ : N.map ψ ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
    set Z := Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) with hZ
    have hn : ((N.map ψ).map (QuotientGroup.mk' Z)).Normal :=
      Subgroup.Normal.map hNψn _ (QuotientGroup.mk'_surjective Z)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.map ψ).map (QuotientGroup.mk' Z)) with
      h | h
    · intro s hs
      have : QuotientGroup.mk' Z s ∈ (N.map ψ).map (QuotientGroup.mk' Z) := ⟨s, hs, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff s).mp this
    · exfalso
      apply not_comm_of_card h168
      intro a' b'
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N a'
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective N b'
      have hmem : QuotientGroup.mk' Z (ψ a) ∈ (N.map ψ).map (QuotientGroup.mk' Z) :=
        h ▸ Subgroup.mem_top _
      obtain ⟨n, hn, hns⟩ := Subgroup.mem_map.mp hmem
      have hz : n⁻¹ * ψ a ∈ Z := QuotientGroup.eq.mp hns
      have hcz : n⁻¹ * ψ a * ψ b * (n⁻¹ * ψ a)⁻¹ = ψ b := by
        rw [← Subgroup.mem_center_iff.mp hz (ψ b)]
        group
      have hc : ψ (a * b * a⁻¹ * b⁻¹) ∈ N.map ψ := by
        have e1 : ψ (a * b * a⁻¹ * b⁻¹) =
            n * (n⁻¹ * ψ a * ψ b * (n⁻¹ * ψ a)⁻¹) * n⁻¹ * (ψ b)⁻¹ := by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv]
          group
        have e2 : n * ψ b * n⁻¹ * (ψ b)⁻¹ = n * (ψ b * n⁻¹ * (ψ b)⁻¹) := by group
        rw [e1, hcz, e2]
        exact mul_mem hn (hNψn.conj_mem _ (inv_mem hn) (ψ b))
      obtain ⟨y, hy, hyc⟩ := Subgroup.mem_map.mp hc
      have hk : y⁻¹ * (a * b * a⁻¹ * b⁻¹) ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hyc, inv_mul_cancel]
      rw [hψk] at hk
      have hab : a * b * a⁻¹ * b⁻¹ ∈ N := by
        have := N.mul_mem hy (hFN hk)
        rwa [mul_inv_cancel_left] at this
      have h1 : QuotientGroup.mk' N (a * b * a⁻¹ * b⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hab
      simp only [map_mul, map_inv] at h1
      calc QuotientGroup.mk' N a * QuotientGroup.mk' N b =
            (QuotientGroup.mk' N a * QuotientGroup.mk' N b * (QuotientGroup.mk' N a)⁻¹ *
              (QuotientGroup.mk' N b)⁻¹) * (QuotientGroup.mk' N b * QuotientGroup.mk' N a) := by
            group
        _ = QuotientGroup.mk' N b * QuotientGroup.mk' N a := by rw [h1, one_mul]
  have hp7 : p = 7 := by
    have hidx : (N.map ψ).index = 168 := by
      rw [Subgroup.index_map_eq N hψs (hψk.symm ▸ hFN), Subgroup.index_eq_card, h168]
    have h1 := Subgroup.card_mul_index (N.map ψ)
    rw [hidx, card_SL_two_zmod p] at h1
    exact eq_seven_of_card hp hp3 Nat.card_pos
      ((Subgroup.card_le_of_le hNψ).trans (card_center_SL_two_le p)) h1
  subst hp7
  have hαF : (CFSG.fittingSubgroup X).map α.toMonoidHom = CFSG.fittingSubgroup X :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance α
  let β : MulAut ↥(CFSG.fittingSubgroup X) :=
    (α.subgroupMap (CFSG.fittingSubgroup X)).trans (MulEquiv.subgroupCongr hαF)
  have hβpow : ∀ (n : ℕ) (f : ↥(CFSG.fittingSubgroup X)),
      (((β ^ n) f : ↥(CFSG.fittingSubgroup X)) : X) = (α ^ n) f := by
    intro n
    induction n with
    | zero => intro f; rfl
    | succ n ih =>
      intro f
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ih]
      rfl
  have hβ5 : β ^ 5 = 1 := MulEquiv.ext fun f => Subtype.ext (by rw [hβpow, hα5]; rfl)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hP : IsPGroup 5 (Subgroup.zpowers β) := by
    intro g
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← hn, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hβ5, one_zpow]
  let K : Subgroup ↥(CFSG.fittingSubgroup X) :=
    { carrier := {f | β f = f}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_mul] at ha hb ⊢
        rw [ha, hb]
      one_mem' := map_one β
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq, map_inv] at ha ⊢
        rw [ha] }
  have hfix : ∀ f, f ∈ MulAction.fixedPoints (Subgroup.zpowers β) ↥(CFSG.fittingSubgroup X) ↔
      f ∈ K := by
    intro f
    constructor
    · intro hf
      exact hf ⟨β, Subgroup.mem_zpowers β⟩
    · intro hf g
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
      have hf' : β f = f := hf
      rw [Subgroup.smul_def, ← hn, MulAut.smul_def]
      have h2 : ∀ m : ℕ, (β ^ m) f = f := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih => rw [pow_succ, MulAut.mul_apply, hf', ih]
      rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
      · rw [zpow_natCast, h2]
      · rw [zpow_neg, zpow_natCast]
        conv_lhs => rw [← h2 m]
        rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  have hmod := hP.card_modEq_card_fixedPoints ↥(CFSG.fittingSubgroup X)
  rw [Nat.card_congr (Equiv.subtypeEquivRight hfix), hcardF] at hmod
  have hKtop : K = ⊤ := by
    obtain ⟨i, hi, hiK⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 7)).mp
      (hcardF ▸ Subgroup.card_subgroup_dvd_card K)
    have hK : Nat.card ↥K = 7 ^ 2 := by
      have hmod' : 7 ^ 2 ≡ 7 ^ i [MOD 5] := hiK ▸ hmod
      interval_cases i <;> simp_all [Nat.ModEq]
    exact (Subgroup.card_eq_iff_eq_top K).mp (hK.trans hcardF.symm)
  have hαfix : ∀ f ∈ CFSG.fittingSubgroup X, α f = f := by
    intro f hf
    have h1 : (⟨f, hf⟩ : ↥(CFSG.fittingSubgroup X)) ∈ K := hKtop ▸ Subgroup.mem_top _
    exact congrArg Subtype.val h1
  have hcen : ∀ x : X,
      ψ (α x * x⁻¹) ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)) :=
    fun x => hNψ ⟨_, hα x, rfl⟩
  let ε : X →* ↥(Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 7))) :=
    { toFun := fun x => ⟨ψ (α x * x⁻¹), hcen x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        show ψ (α (x * y) * (x * y)⁻¹) = ψ (α x * x⁻¹) * ψ (α y * y⁻¹)
        have h1 : (ψ x)⁻¹ * ψ (α y * y⁻¹) = ψ (α y * y⁻¹) * (ψ x)⁻¹ :=
          Subgroup.mem_center_iff.mp (hcen y) (ψ x)⁻¹
        calc ψ (α (x * y) * (x * y)⁻¹) = ψ (α x) * (ψ (α y * y⁻¹) * (ψ x)⁻¹) := by
              simp only [map_mul, map_inv, mul_inv_rev]
              group
          _ = ψ (α x * x⁻¹) * ψ (α y * y⁻¹) := by
              rw [← h1, map_mul ψ (α x), map_inv]
              group) }
  have hker : commutator X ≤ ε.ker := Abelianization.commutator_subset_ker ε
  have hd : ∀ x : X, α x * x⁻¹ ∈ CFSG.fittingSubgroup X := by
    intro x
    have hx : ψ x ∈ (commutator X).map ψ := by
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective ψ hψs,
        ← commutator_def, hperf]
      exact Subgroup.mem_top _
    obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp hx
    have hcF : c⁻¹ * x ∈ CFSG.fittingSubgroup X := by
      rw [← hψk, MonoidHom.mem_ker, map_mul, map_inv, hcx, inv_mul_cancel]
    have hεx : ε x = 1 := by
      have e1 : x = c * (c⁻¹ * x) := by group
      rw [e1, map_mul, hker hc, one_mul]
      apply Subtype.ext
      show ψ (α (c⁻¹ * x) * (c⁻¹ * x)⁻¹) = 1
      rw [hαfix _ hcF, mul_inv_cancel, map_one]
    have h1 : ψ (α x * x⁻¹) = 1 := congrArg Subtype.val hεx
    rw [← hψk]
    exact h1
  refine MulEquiv.ext fun x => ?_
  set d := α x * x⁻¹ with hddef
  have hdF := hd x
  have hpow : ∀ n : ℕ, (α ^ n) x = d ^ n * x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hαfix d hdF, pow_succ, mul_assoc,
        hddef, inv_mul_cancel_right]
  have h5 : d ^ 5 = 1 := by
    have := hpow 5
    rw [hα5, MulAut.one_apply] at this
    exact (mul_eq_right.mp this.symm)
  have h7 : d ^ 7 = 1 := by
    have := congrArg Subtype.val (hexpF ⟨d, hdF⟩)
    simpa using this
  have hd1 : d = 1 := by
    have hd5 : orderOf d ∣ 5 := orderOf_dvd_of_pow_eq_one h5
    have hd7 : orderOf d ∣ 7 := orderOf_dvd_of_pow_eq_one h7
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (by norm_num) hd5 hd7)
  rw [MulAut.one_apply]
  exact mul_inv_eq_one.mp hd1

end CFSG.Quasithin.H13.L32A.S2

end
