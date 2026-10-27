module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoNComp
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoNCmp
public import CFSG.LieType.SeitzGeneration.HyperCoverUnitary
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoNPerm7
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoNMono
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.StandardType.E6QTwo

open CFSG CFSG.Assembly E6QTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.SectionRank.OddCover (diagHom coe_diagHom)

theorem ggQ2s08rN_exists_perm_four {N : ℕ} (hN : 5 ≤ N) (w : Fin N) :
    ∃ τ : Equiv.Perm (Fin N), τ w = w ∧ ¬ τ ^ 2 ^ 1 = 1 ∧ τ ^ 2 ^ (1 + 1) = 1 := by
  classical
  have hcard : 4 ≤ (Finset.univ.erase w).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ w), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq hcard
  set l := t.toList with hl
  have hnd : l.Nodup := Finset.nodup_toList t
  have hlen : l.length = 4 := by rw [hl, Finset.length_toList, htc]
  have hcyc : (List.formPerm l).IsCycle := List.isCycle_formPerm hnd (by omega)
  have hsupp : (List.formPerm l).support = l.toFinset :=
    List.support_formPerm_of_nodup l hnd (fun x h => by rw [h] at hlen; simp at hlen)
  have hord : orderOf (List.formPerm l) = 4 := by
    rw [hcyc.orderOf, hsupp, List.toFinset_card_of_nodup hnd, hlen]
  refine ⟨List.formPerm l, ?_, ?_, ?_⟩
  · apply List.formPerm_apply_of_notMem
    intro hw
    have : w ∈ t := by rwa [hl, Finset.mem_toList] at hw
    exact (Finset.mem_erase.mp (ht this)).1 rfl
  · intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hord] at this
    norm_num at this
  · rw [show 2 ^ (1 + 1) = 4 by norm_num, ← hord]
    exact pow_orderOf_eq_one _

namespace GGQ2S08RoN

variable {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G} {n : ℕ}

omit [Finite G]
  in
theorem eq_one_of_mem_center_of_pow_three (hZ : Nat.Coprime 3 (Nat.card (Subgroup.center ↥L)))
    {y : ↥L} (hy : y ∈ Subgroup.center ↥L) (h3 : y ^ 3 = 1) : y = 1 := by
  have h1 : orderOf (⟨y, hy⟩ : ↥(Subgroup.center ↥L)) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h3))
  have h2 : orderOf (⟨y, hy⟩ : ↥(Subgroup.center ↥L)) ∣ Nat.card ↥(Subgroup.center ↥L) :=
    orderOf_dvd_natCard _
  have h := Nat.dvd_gcd h1 h2
  rw [hZ.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h
  exact congrArg Subtype.val h

theorem eq_one_of_mem_center_of_even (c : GGQ2S08RoN n Bs L x)
    (hZ : Nat.Coprime 3 (Nat.card (Subgroup.center ↥L))) (heven : Even n) {q : ↥L}
    (hq : q ∈ Subgroup.center ↥L) : q = 1 := by
  have hKc : Nat.card c.K = (2 ^ 1) ^ 2 := by rw [c.hK]; norm_num
  have hU := USixTwo.fieldDataFour c.hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP c.K 2 := hU.charP
  have : Group.IsPerfect ↥L := Group.isPerfect_def.mpr c.hperf
  let ρ : ↥L →* CFSG.Open.StatedProj (CFSG.Open.StatedSU (n + 1) (2 ^ 1) c.K) := c.piL
  have hker : ρ.ker ≤ Subgroup.center ↥L := by
    intro l hl
    rw [← c.piL_ker]
    exact hl
  obtain ⟨φ, hφ, hφρ⟩ := CFSG.LieType.SeitzGeneration.exists_su_cover_hom hKc le_rfl
    (by have := c.hn; omega : 4 ≤ n + 1) ρ c.piL_surjective hker
    (fun he => absurd he (Nat.not_even_iff_odd.mpr heven.add_one))
  obtain ⟨g, hg⟩ := hφ q
  have hρq : ρ q = 1 := by
    change c.piL q = 1
    rw [← MonoidHom.mem_ker, c.piL_ker]
    exact hq
  rw [← hg, hφρ] at hρq
  have hg3 : g ^ 3 = 1 := by
    obtain ⟨μ, hμ⟩ := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hρq)
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hμ, ← map_pow, c.cube μ, map_one, Subgroup.coe_one]
  have hq3 : q ^ 3 = 1 := by rw [← hg, ← map_pow, hg3, map_one]
  exact eq_one_of_mem_center_of_pow_three hZ hq hq3

theorem eq_one_of_piL_eq_one_of_odd (c : GGQ2S08RoN n Bs L x)
    (hZ : Nat.Coprime 3 (Nat.card (Subgroup.center ↥L))) (hodd : Odd n) (w : Fin (n + 1))
    {q : ↥L} (hq : q ∈ c.compL w) (h1 : c.piL q = 1) : q = 1 := by
  have hKc : Nat.card c.K = (2 ^ 1) ^ 2 := by rw [c.hK]; norm_num
  have hU := USixTwo.fieldDataFour c.hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP c.K 2 := hU.charP
  have hperf : Group.IsPerfect ↥(c.compL w) := Group.isPerfect_def.mpr (c.compL_quasisimple w).1
  let ρ₀ : ↥(c.compL w) →* ↥(c.stabImg w) :=
    (c.piL.comp (c.compL w).subtype).codRestrict (c.stabImg w)
      (fun q' => c.compL_le_stabPre w q'.2)
  let e : ↥(c.stabImg w) ≃* ↥(CFSG.Open.StatedSU n (2 ^ 1) c.K) :=
    (c.stabEquiv w).symm.trans (ggQ2s08rN_stabSUEquiv c.hK w)
  let Zs : Subgroup ↥(CFSG.Open.StatedSU n (2 ^ 1) c.K) :=
    (CFSG.Open.StatedScalars (Fin n) c.K).subgroupOf (CFSG.Open.StatedSU n (2 ^ 1) c.K)
  let mk := QuotientGroup.mk' Zs
  let ρ : ↥(c.compL w) →* CFSG.Open.StatedProj (CFSG.Open.StatedSU n (2 ^ 1) c.K) :=
    mk.comp (e.toMonoidHom.comp ρ₀)
  have hρ₀ : Function.Surjective ρ₀ := by
    rintro ⟨r, hr⟩
    have hmap := ggQ2s08r6_map_comm_comap c.piL_surjective (c.stabImg w) (c.stabImg_perfect w)
    rw [← hmap] at hr
    obtain ⟨q', hq', hq'r⟩ := hr
    exact ⟨⟨q', hq'⟩, Subtype.ext hq'r⟩
  have hρ : Function.Surjective ρ :=
    (QuotientGroup.mk'_surjective _).comp (e.surjective.comp hρ₀)
  have hker₀ : ρ₀.ker ≤ Subgroup.center ↥(c.compL w) := by
    intro q' hq'
    have h : c.piL q' = 1 := congrArg Subtype.val hq'
    have hz : (q' : ↥L) ∈ Subgroup.center ↥L := by rw [← c.piL_ker]; exact h
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro r
    exact Subtype.ext (hz r)
  have hcen : (Subgroup.center ↥(c.stabImg w)).comap ρ₀ = Subgroup.center ↥(c.compL w) :=
    CFSG.LocalCores.comap_center_eq_of_perfect hperf ρ₀ hρ₀ hker₀
  have hker : ρ.ker ≤ Subgroup.center ↥(c.compL w) := by
    intro q' hq'
    rw [← hcen, Subgroup.mem_comap]
    have h2 : e (ρ₀ q') ∈ Zs := (QuotientGroup.eq_one_iff _).mp hq'
    obtain ⟨μ, hμ⟩ := Subgroup.mem_subgroupOf.mp h2
    rw [Subgroup.mem_center_iff]
    intro r
    apply e.injective
    rw [map_mul, map_mul]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hμ]
    exact (TypeA.PGLTor.scalar_mul_comm μ _).symm
  obtain ⟨φ, hφ, hφρ⟩ := CFSG.LieType.SeitzGeneration.exists_su_cover_hom hKc le_rfl
    (by have := c.hn; omega : 4 ≤ n) ρ hρ hker
    (fun he => absurd he (Nat.not_even_iff_odd.mpr hodd))
  obtain ⟨g, hg⟩ := hφ ⟨q, hq⟩
  have hρq : ρ ⟨q, hq⟩ = 1 := by
    have h0 : ρ₀ ⟨q, hq⟩ = 1 := Subtype.ext h1
    change mk (e (ρ₀ ⟨q, hq⟩)) = 1
    rw [h0, map_one, map_one]
  rw [← hg, hφρ] at hρq
  have hg3 : g ^ 3 = 1 := by
    obtain ⟨μ, hμ⟩ := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hρq)
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hμ, ← map_pow, c.cube μ, map_one, Subgroup.coe_one]
  have hq3 : q ^ 3 = 1 := by
    have h3 : (⟨q, hq⟩ : ↥(c.compL w)) ^ 3 = 1 := by rw [← hg, ← map_pow, hg3, map_one]
    exact congrArg Subtype.val h3
  have hqZ : q ∈ Subgroup.center ↥L := by rw [← c.piL_ker]; exact h1
  exact eq_one_of_mem_center_of_pow_three hZ hqZ hq3

theorem eq_one_of_piL_eq_one (c : GGQ2S08RoN n Bs L x)
    (hZ : Nat.Coprime 3 (Nat.card (Subgroup.center ↥L))) (w : Fin (n + 1)) {q : ↥L}
    (hq : q ∈ c.compL w) (h1 : c.piL q = 1) : q = 1 := by
  rcases Nat.even_or_odd n with heven | hodd
  · exact c.eq_one_of_mem_center_of_even hZ heven (by rw [← c.piL_ker]; exact h1)
  · exact c.eq_one_of_piL_eq_one_of_odd hZ hodd w hq h1

theorem conjB_mem_center (c : GGQ2S08RoN n Bs L x) (b : Bs) {y : ↥L}
    (hy : y ∈ Subgroup.center ↥L) : c.conjB b y ∈ Subgroup.center ↥L := by
  rw [Subgroup.mem_center_iff] at hy ⊢
  intro l
  have h := hy ((c.conjB b).symm l)
  have h2 := congrArg (c.conjB b) h
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
  exact h2

theorem conj_mem_of_mem_compL (c : GGQ2S08RoN n Bs L x)
    (hZ : Nat.Coprime 3 (Nat.card (Subgroup.center ↥L))) (w : Fin (n + 1))
    {q : ↥L} (hq : q ∈ c.compL w) (b : Bs) {b' : G} (hb' : b' ∈ Bs) (y : ↥L)
    (hy : y ∈ Subgroup.center ↥L) (h : (q : G) * b * (q : G)⁻¹ = b' * y) :
    (q : G) * b * (q : G)⁻¹ ∈ Bs := by
  have hu : q * c.conjB b q⁻¹ ∈ c.compL w :=
    (c.compL w).mul_mem hq (c.conjB_mem_compL w b ((c.compL w).inv_mem hq))
  set u := q * c.conjB b q⁻¹ with hudef
  set y' := c.conjB b y with hy'def
  have hy'c : y' ∈ Subgroup.center ↥L := c.conjB_mem_center b hy
  have hy'G : (y' : G) = (b : G) * y * (b : G)⁻¹ := e6QTwoBstarConjAction_apply c.hNL b y
  have huG : (u : G) = (q : G) * b * (q : G)⁻¹ * (b : G)⁻¹ := by
    rw [hudef, Subgroup.coe_mul, e6QTwoBstarConjAction_apply, Subgroup.coe_inv]
    group
  have hc'eq : (u : G) = (b' * (b : G)⁻¹) * y' := by
    rw [huG, h, hy'G]
    group
  have hc'Bs : b' * (b : G)⁻¹ ∈ Bs := Bs.mul_mem hb' (Bs.inv_mem b.2)
  have hc'L : b' * (b : G)⁻¹ ∈ L := by
    have : b' * (b : G)⁻¹ = (u : G) * (y' : G)⁻¹ := by rw [hc'eq]; group
    rw [this]
    exact L.mul_mem u.2 (L.inv_mem y'.2)
  set c' : ↥L := ⟨b' * (b : G)⁻¹, hc'L⟩ with hc'def
  have huL : u = c' * y' := Subtype.ext hc'eq
  have hc'3 : c' ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact c.hBs.2 _ hc'Bs)
  have hu3 : u ^ 3 = y' ^ 3 := by
    have hcomm : Commute c' y' := Subgroup.mem_center_iff.mp hy'c c'
    rw [huL, hcomm.mul_pow, hc'3, one_mul]
  have hpi : c.piL (u ^ 3) = 1 := by
    rw [hu3, map_pow]
    have : c.piL y' = 1 := by rw [← MonoidHom.mem_ker, c.piL_ker]; exact hy'c
    rw [this, one_pow]
  have hu31 : u ^ 3 = 1 := c.eq_one_of_piL_eq_one hZ w ((c.compL w).pow_mem hu 3) hpi
  have hy'1 : y' = 1 := eq_one_of_mem_center_of_pow_three hZ hy'c (by rw [← hu3, hu31])
  have huBs : (u : G) ∈ Bs := by
    rw [hc'eq, hy'1, Subgroup.coe_one, mul_one]
    exact hc'Bs
  have : (q : G) * b * (q : G)⁻¹ = (u : G) * b := by rw [huG]; group
  rw [this]
  exact Bs.mul_mem huBs b.2

omit [Finite G]
  in
theorem mulAut_mul_conj_mul_inv {H : Type} [Group H] (φ : MulAut H) (a : H) :
    φ * MulAut.conj a * φ⁻¹ = MulAut.conj (φ a) := by
  ext r
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.inv_apply,
    MulEquiv.apply_symm_apply]

theorem mem_stabPre_of_normAction (c : GGQ2S08RoN n Bs L x) {w : Fin (n + 1)}
    {τ : Equiv.Perm (Fin (n + 1))} (hτw : τ w = w) {ν : G} (hνL : ν ∈ L) {b₀ : Bs}
    (hact : e6QTwoNNormAction c.θ ⟨ν, Subgroup.le_normalizer hνL⟩ =
      c.act b₀ * e6QTwoNFramePerm c.hK c.hQ τ * (c.act b₀)⁻¹) :
    (⟨ν, hνL⟩ : ↥L) ∈ c.stabPre w := by
  set u : ↥(LargeEvenSUGroup (Fin (n + 1)) c.K 2) :=
    (suCongrN c.K).symm (e6QTwoNPermGLSU c.hK τ) with hudef
  have hfru : c.fr u = InndiagSU.frameMk (USixTwo.fieldDataFour c.hK) c.Q c.hQ
      (e6QTwoNPermGLSU c.hK τ) := by
    rw [fr_apply, hudef, MulEquiv.apply_symm_apply]
  have hconj : MulAut.conj (c.piL ⟨ν, hνL⟩) =
      MulAut.conj (c.fr (c.diagConj (c.diag b₀) u)) := by
    have h1 : MulAut.conj (c.piL ⟨ν, hνL⟩) =
        e6QTwoNNormAction c.θ ⟨ν, Subgroup.le_normalizer hνL⟩ := by
      rw [e6QTwoNNormAction_of_mem_L c.θ ⟨ν, hνL⟩, conjOnQuot_eq]
      rfl
    rw [h1, hact, e6QTwoNFramePerm, ← hfru, mulAut_mul_conj_mul_inv, act_fr]
  have hcen := TableBUE.center_proj_eq_bot (K := c.K) (n := 1) (d := n + 1)
    (by rw [c.hK]; norm_num) (by have := c.hn; omega)
    (fun h => by have h1 : n + 1 = 3 := congrArg Prod.fst h; have := c.hn; omega)
  have heq : c.piL ⟨ν, hνL⟩ = c.fr (c.diagConj (c.diag b₀) u) := by
    have hz : (c.fr (c.diagConj (c.diag b₀) u))⁻¹ * c.piL ⟨ν, hνL⟩ ∈
        Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) c.K (2 ^ 1))) := by
      rw [Subgroup.mem_center_iff]
      intro r
      have h := congrArg (fun φ : MulAut _ => φ r) hconj
      simp only [MulAut.conj_apply] at h
      calc r * ((c.fr (c.diagConj (c.diag b₀) u))⁻¹ * c.piL ⟨ν, hνL⟩)
          = (c.fr (c.diagConj (c.diag b₀) u))⁻¹ *
              (c.fr (c.diagConj (c.diag b₀) u) * r * (c.fr (c.diagConj (c.diag b₀) u))⁻¹) *
              c.piL ⟨ν, hνL⟩ := by group
        _ = (c.fr (c.diagConj (c.diag b₀) u))⁻¹ *
              (c.piL ⟨ν, hνL⟩ * r * (c.piL ⟨ν, hνL⟩)⁻¹) * c.piL ⟨ν, hνL⟩ := by rw [← h]
        _ = (c.fr (c.diagConj (c.diag b₀) u))⁻¹ * c.piL ⟨ν, hνL⟩ * r := by group
    rw [hcen, Subgroup.mem_bot, inv_mul_eq_one] at hz
    exact hz.symm
  have hu : u ∈ ggQ2s08rNStab c.K w := by
    refine ggQ2s08rN_permGL_mem_stab hτw u ?_
    change (e6QTwoNPermGLSU c.hK τ : GL (Fin (n + 1)) c.K) = _
    rw [e6QTwoNCoePermGLSU]
    ext i j
    simp [TauCeti.permutationGL_coe, Matrix.permMatrixHom_apply]
  change c.piL ⟨ν, hνL⟩ ∈ c.stabImg w
  rw [heq]
  exact ⟨_, ggQ2s08rN_diag_conj_mem_stab (c.diag b₀) hu (c.coe_diagConj _ u), rfl⟩

theorem four_dvd_card_automizer_of_mem (c : GGQ2S08RoN n Bs L x) {w : Fin (n + 1)}
    {τ : Equiv.Perm (Fin (n + 1))} (hτord : orderOf τ = 2 ^ (1 + 1)) {q : ↥L}
    (hq : q ∈ c.compL w) (hqconj : ∀ b : Bs, (q : G) * b * (q : G)⁻¹ ∈ Bs)
    (hrelq : ∀ b : Bs, ∃ μ : c.Kˣ, ∀ k,
      c.diag ⟨(q : G) * b * (q : G)⁻¹, hqconj b⟩ k = μ * c.diag b (τ.symm k)) :
    4 ∣ Nat.card ↥(ggAutomizer (c.comp w) Bs) := by
  classical
  have hqN : (q : G) ∈ Subgroup.normalizer (Bs : Set G) := by
    have hmap : Bs.map (MulAut.conj (q : G)).toMonoidHom ≤ Bs := by
      rintro _ ⟨b, hb, rfl⟩
      exact hqconj ⟨b, hb⟩
    have hcard : Nat.card ↥(Bs.map (MulAut.conj (q : G)).toMonoidHom) = Nat.card ↥Bs :=
      Subgroup.card_map_of_injective (MulAut.conj (q : G)).injective
    exact mem_normalizer_iff_map_conj.mpr (Subgroup.eq_of_le_of_card_ge hmap hcard.ge)
  set α : MulAut ↥Bs := Bs.normalizerMonoidHom ⟨(q : G), hqN⟩ with hαdef
  have hαapply : ∀ b : Bs, α b = ⟨(q : G) * b * (q : G)⁻¹, hqconj b⟩ := fun b =>
    Subtype.ext (Bs.normalizerMonoidHom_apply_apply_coe ⟨(q : G), hqN⟩ b)
  have hαmem : α ∈ ggAutomizer (c.comp w) Bs := by
    refine Subgroup.subset_closure (show α ∈ ggInduced (c.comp w) Bs from
      ⟨(q : G), ⟨q, hq, rfl⟩, hqN, fun b => ?_⟩)
    rw [hαapply]
  have hαpow : ∀ (m : ℕ) (b : Bs), ∃ μ : c.Kˣ, ∀ k,
      c.diag ((α ^ m) b) k = μ * c.diag b ((τ ^ m).symm k) := by
    intro m
    induction m with
    | zero =>
      intro b
      refine ⟨1, fun k => ?_⟩
      rw [pow_zero, pow_zero, one_mul]
      rfl
    | succ m ih =>
      intro b
      obtain ⟨μ, hμ⟩ := ih b
      obtain ⟨μ', hμ'⟩ := hrelq ((α ^ m) b)
      refine ⟨μ' * μ, fun k => ?_⟩
      rw [pow_succ', MulAut.mul_apply, hαapply, hμ' k, hμ, pow_succ', Equiv.Perm.mul_def,
        Equiv.symm_trans_apply, mul_assoc]
  have h4 : 4 ∣ orderOf α := by
    have hτm : τ ^ orderOf α = 1 := by
      apply ggQ2s08rN_perm_eq_of_forall c.card_units (by have := c.hn; omega)
      intro σ
      obtain ⟨b, hb⟩ := c.exists_diag_eq (fun k => (σ (0 : Fin (n + 1)))⁻¹ * σ k) (by simp)
      obtain ⟨μ, hμ⟩ := hαpow (orderOf α) b
      rw [pow_orderOf_eq_one, MulAut.one_apply] at hμ
      have hσ : ∀ k, σ k = σ (0 : Fin (n + 1)) * c.diag b k := fun k => by
        rw [hb, mul_inv_cancel_left]
      refine ⟨μ⁻¹, fun i => ?_⟩
      rw [Equiv.Perm.one_symm, Equiv.Perm.coe_one, id, hσ ((τ ^ orderOf α).symm i), hσ i,
        hμ i, mul_left_comm μ⁻¹, inv_mul_cancel_left]
    have h := orderOf_dvd_of_pow_eq_one hτm
    rw [hτord] at h
    exact h
  exact h4.trans (Subgroup.orderOf_dvd_natCard _ hαmem)

theorem four_dvd_card_automizer_of (c : GGQ2S08RoN n Bs L x)
    (hZ : Nat.Coprime 3 (Nat.card (Subgroup.center ↥L))) {w : Fin (n + 1)}
    {τ : Equiv.Perm (Fin (n + 1))} (hτw : τ w = w) (hτord : orderOf τ = 2 ^ (1 + 1))
    {ν : G} (hνL : ν ∈ L) (hνN : ν ∈ Subgroup.normalizer (Bs : Set G)) {b₀ : Bs}
    (hact : e6QTwoNNormAction c.θ ⟨ν, Subgroup.le_normalizer hνL⟩ =
      c.act b₀ * e6QTwoNFramePerm c.hK c.hQ τ * (c.act b₀)⁻¹)
    (hνact : ∀ (b : ↥Bs) (σ : Fin (n + 1) → c.Kˣ), (∀ k, σ k ^ 3 = 1) →
      c.FrameDiag b σ → c.FrameDiag ⟨ν * (b : G) * ν⁻¹,
        (Subgroup.mem_normalizer_iff.mp hνN (b : G)).mp b.2⟩ (σ ∘ ⇑τ.symm)) :
    4 ∣ Nat.card ↥(ggAutomizer (c.comp w) Bs) := by
  classical
  have hconjBs : ∀ b : Bs, ν * (b : G) * ν⁻¹ ∈ Bs := fun b =>
    (Subgroup.mem_normalizer_iff.mp hνN (b : G)).mp b.2
  have hrel : ∀ b : Bs, ∃ μ : c.Kˣ, ∀ k,
      c.diag ⟨ν * (b : G) * ν⁻¹, hconjBs b⟩ k = μ * c.diag b (τ.symm k) := by
    intro b
    have h := hνact b (c.diag b) (fun k => c.cube _) (c.frameDiag_diag b)
    obtain ⟨μ, hμ⟩ := c.exists_eq_smul_diag h
    refine ⟨μ⁻¹, fun k => ?_⟩
    have := hμ k
    simp only [Function.comp_apply] at this
    rw [this, inv_mul_cancel_left]
  have hνP := c.mem_stabPre_of_normAction hτw hνL hact
  have hsup := ggQ2s08r6_comap_eq_sup c.piL_surjective (c.stabImg w) (c.stabImg_perfect w)
  have hνP' : (⟨ν, hνL⟩ : ↥L) ∈ c.compL w ⊔ c.piL.ker := by
    have h : (⟨ν, hνL⟩ : ↥L) ∈ Subgroup.comap c.piL (c.stabImg w) := hνP
    rw [hsup] at h
    exact h
  have : (c.piL.ker).Normal := MonoidHom.normal_ker _
  obtain ⟨q, hq, z, hz, hqz⟩ := Subgroup.mem_sup_of_normal_right.mp hνP'
  have hzc : z ∈ Subgroup.center ↥L := by rw [← c.piL_ker]; exact hz
  have hqG : (q : G) = ν * (z : G)⁻¹ := by
    have h : (q : G) * z = ν := congrArg Subtype.val hqz
    rw [← h]
    group
  have hk : ∀ b : Bs, ∃ k : ↥L, k ∈ Subgroup.center ↥L ∧
      (q : G) * b * (q : G)⁻¹ = (ν * (b : G) * ν⁻¹) * k := by
    intro b
    have hkc : c.conjB b⁻¹ z⁻¹ * z ∈ Subgroup.center ↥L := (Subgroup.center ↥L).mul_mem
      (c.conjB_mem_center b⁻¹ ((Subgroup.center ↥L).inv_mem hzc)) hzc
    refine ⟨c.conjB b⁻¹ z⁻¹ * z, hkc, ?_⟩
    have hkG : ((c.conjB b⁻¹ z⁻¹ * z : ↥L) : G) = (b : G)⁻¹ * (z : G)⁻¹ * b * z := by
      rw [Subgroup.coe_mul, e6QTwoBstarConjAction_apply]
      simp only [Subgroup.coe_inv, inv_inv]
    have hcomm : ν⁻¹ * ((c.conjB b⁻¹ z⁻¹ * z : ↥L) : G) =
        ((c.conjB b⁻¹ z⁻¹ * z : ↥L) : G) * ν⁻¹ :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hkc ⟨ν⁻¹, L.inv_mem hνL⟩)
    rw [mul_assoc (ν * (b : G)), hcomm, hkG, hqG]
    group
  have hqconj : ∀ b : Bs, (q : G) * b * (q : G)⁻¹ ∈ Bs := by
    intro b
    obtain ⟨k, hkc, hkeq⟩ := hk b
    exact c.conj_mem_of_mem_compL hZ w hq b (hconjBs b) k hkc hkeq
  have hrelq : ∀ b : Bs, ∃ μ : c.Kˣ, ∀ k,
      c.diag ⟨(q : G) * b * (q : G)⁻¹, hqconj b⟩ k = μ * c.diag b (τ.symm k) := by
    intro b
    obtain ⟨k₁, hk₁c, hk₁eq⟩ := hk b
    have hk₁Bs : (k₁ : G) ∈ Bs := by
      have : (k₁ : G) = (ν * (b : G) * ν⁻¹)⁻¹ * ((q : G) * b * (q : G)⁻¹) := by
        rw [hk₁eq]
        group
      rw [this]
      exact Bs.mul_mem (Bs.inv_mem (hconjBs b)) (hqconj b)
    have hk₁x : (k₁ : G) ∈ Subgroup.zpowers x := by
      rw [← c.hBL]
      refine ⟨hk₁Bs, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hk₁c ⟨l, hl⟩)
    have hsplit : (⟨(q : G) * b * (q : G)⁻¹, hqconj b⟩ : ↥Bs) =
        ⟨ν * (b : G) * ν⁻¹, hconjBs b⟩ * ⟨(k₁ : G), hk₁Bs⟩ := Subtype.ext hk₁eq
    have hdk : c.diag ⟨(k₁ : G), hk₁Bs⟩ = 1 := (c.diag_eq_one_iff _).mpr hk₁x
    obtain ⟨μ, hμ⟩ := hrel b
    refine ⟨μ, fun k => ?_⟩
    rw [hsplit, c.diag_mul, hdk, mul_one]
    exact hμ k
  exact c.four_dvd_card_automizer_of_mem hτord hq hqconj hrelq

theorem four_dvd_card_automizer_of_coprime (c : GGQ2S08RoN n Bs L x)
    (hZ : Nat.Coprime 3 (Nat.card (Subgroup.center ↥L))) (w : Fin (n + 1)) :
    4 ∣ Nat.card ↥(ggAutomizer (c.comp w) Bs) := by
  obtain ⟨τ, hτw, hτ2, hτ4⟩ := ggQ2s08rN_exists_perm_four (by have := c.hn; omega) w
  have hτord : orderOf τ = 2 ^ (1 + 1) := orderOf_eq_prime_pow hτ2 hτ4
  obtain ⟨ν, hνL, hνN, ⟨b₀, hact⟩, hνact⟩ := e6QTwoN_exists_mem_normalizer_frameAct_perm c.hK
    (by have := c.hn; omega) hZ c.θ c.hNL c.hfull c.hrange c.hperf c.hBs c.hx c.hBL c.hstar τ
  exact c.four_dvd_card_automizer_of hZ hτw hτord hνL hνN hact hνact

end GGQ2S08RoN

end CFSG.StandardType.E6QTwo

end
