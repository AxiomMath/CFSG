module

public import CFSG.Quasithin.Recognition.St84.Hyp
public import CFSG.Quasithin.Recognition.St84.L2Group
public import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionAutomorphismsSupport

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open
open scoped MatrixGroups

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {v : V} {n : ℕ}
  {N : Subgroup G}


private theorem eq_of_ne_one_of_card_eq_two {H : Type*} [Group H] (hcard : Nat.card H = 2)
    {x y : H} (hx : x ≠ 1) (hy : y ≠ 1) : x = y := by
  obtain ⟨z, hz, hzuniq⟩ := (Nat.card_eq_two_iff' (1 : H)).mp hcard
  exact (hzuniq x hx).trans (hzuniq y hy).symm

namespace IsLocL2

@[expose] noncomputable def phi (hN : IsLocL2 Γ G v n N) :
    N →* PSL(2, GaloisField 2 n) :=
  hN.quot.some.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥N))

theorem pCoreOf_eq (hN : IsLocL2 Γ G v n N) :
    pCoreOf 2 N = pCoreOf 2 (MulAction.stabilizer G v) := by
  classical
  let Gv := MulAction.stabilizer G v
  have hGvN : Gv ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN.le).mp hN.normal
  refine le_antisymm ?_ ?_
  ·
    have hGvCore : Gv ≤ Subgroup.normalizer (pCoreOf 2 N : Set G) := by
      have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (H := N) (K := CFSG.pCore 2 N)
      simpa [pCoreOf] using hGvN.trans h
    have hnormal : ((pCoreOf 2 N).subgroupOf Gv).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hGvCore
    have hp : IsPGroup 2 (pCoreOf 2 N) :=
      (CFSG.pCore_isPGroup (G := N) (p := 2)).map N.subtype
    exact CFSG.LieType.BorelTits.le_pCoreOf (r := 2)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 N).trans hN.le) hnormal hp
  ·
    have hQnormal : ((pCoreOf 2 Gv).subgroupOf N).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer
        (hN.le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Gv))
    have hQp : IsPGroup 2 (pCoreOf 2 Gv) :=
      (CFSG.pCore_isPGroup (G := Gv) (p := 2)).map Gv.subtype
    exact CFSG.LieType.BorelTits.le_pCoreOf (r := 2) hN.oTwo_le hQnormal hQp

theorem phi_ker (hN : IsLocL2 Γ G v n N) (x : N) :
    hN.phi x = 1 ↔ (x : G) ∈ pCoreOf 2 (MulAction.stabilizer G v) := by
  classical
  have hmap : hN.phi x = 1 ↔ QuotientGroup.mk' (CFSG.pCore 2 ↥N) x = 1 := by
    constructor
    · intro h
      have h' : hN.quot.some (QuotientGroup.mk' (CFSG.pCore 2 ↥N) x) =
          hN.quot.some 1 := by
        simpa [phi] using h
      exact hN.quot.some.injective h'
    · intro h
      show hN.quot.some (QuotientGroup.mk' (CFSG.pCore 2 ↥N) x) = 1
      rw [h]
      exact map_one hN.quot.some
  rw [hmap]
  constructor
  · intro hx
    have hx' : x ∈ CFSG.pCore 2 ↥N :=
      (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥N) x).mp hx
    rw [← pCoreOf_eq (Γ := Γ) (G := G) (v := v) (n := n) (N := N) hN]
    exact Subgroup.mem_map_of_mem N.subtype hx'
  · intro hx
    have hmem : (x : G) ∈ pCoreOf 2 N := by
      rw [pCoreOf_eq (Γ := Γ) (G := G) (v := v) (n := n) (N := N) hN]
      exact hx
    have hx' : x ∈ CFSG.pCore 2 ↥N :=
      (Subgroup.mem_map_iff_mem N.subtype_injective).mp hmem
    exact (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥N) x).mpr hx'

@[expose] def neighborAction (hN : IsLocL2 Γ G v n N)
    (hadj : ∀ (g : G) (u w : V), Γ.Adj (g • u) (g • w) ↔ Γ.Adj u w) :
    SubMulAction N V :=
  { carrier := Γ.neighborSet v
    smul_mem' := by
      intro g a ha
      rw [SimpleGraph.mem_neighborSet] at ha ⊢
      have hv : (g : G) • v = v := MulAction.mem_stabilizer_iff.mp (hN.le g.2)
      rw [MulAction.subgroup_smul_def, ← hv]
      exact (hadj (g : G) v a).mpr ha }

theorem neighborAction_isPretransitive (hN : IsLocL2 Γ G v n N)
    (hadj : ∀ (g : G) (u w : V), Γ.Adj (g • u) (g • w) ↔ Γ.Adj u w) :
    MulAction.IsPretransitive N (hN.neighborAction hadj) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨g, hgN, hg⟩ := hN.trans x.1 y.1 x.2 y.2
  exact ⟨⟨g, hgN⟩, Subtype.ext hg⟩

theorem Q_fixes_neighbors (hN : IsLocL2 Γ G v n N)
    (hadj : ∀ (g : G) (u w : V), Γ.Adj (g • u) (g • w) ↔ Γ.Adj u w)
    (hfin : Finite (MulAction.stabilizer G v))
    (hcard : Nat.card (Γ.neighborSet v) = 2 ^ n + 1) (hn : 1 ≤ n) :
    ∀ a : V, Γ.Adj v a →
      ∀ q : G, q ∈ pCoreOf 2 (MulAction.stabilizer G v) → q • a = a := by
  classical
  let Gv := MulAction.stabilizer G v
  haveI : Finite N :=
    Finite.of_injective
      (fun x : N => (⟨(x : G), hN.le x.2⟩ : Gv))
      (fun a b h => Subtype.ext
        (congrArg (fun z : Gv => (z : G)) h))
  let Δ : SubMulAction N V := hN.neighborAction hadj
  have htrans : MulAction.IsPretransitive N Δ := hN.neighborAction_isPretransitive hadj
  haveI := htrans
  have hQeq : (pCoreOf 2 (MulAction.stabilizer G v)).subgroupOf N = CFSG.pCore 2 ↥N := by
    rw [← pCoreOf_eq (Γ := Γ) (G := G) (v := v) (n := n) (N := N) hN]
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      exact (Subgroup.mem_map_iff_mem N.subtype_injective).mp hx
    · intro hx
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_map_of_mem N.subtype hx
  let QN : Subgroup N := (pCoreOf 2 (MulAction.stabilizer G v)).subgroupOf N
  have hQNnormal : QN.Normal := by
    rw [show QN = CFSG.pCore 2 ↥N from hQeq]
    infer_instance
  haveI : QN.Normal := hQNnormal
  have hQNp : IsPGroup 2 QN := by
    rw [show QN = CFSG.pCore 2 ↥N from hQeq]
    exact CFSG.pCore_isPGroup (G := ↥N) (p := 2)
  intro a ha q hq
  let aΔ : Δ := ⟨a, by
    show a ∈ Δ.carrier
    rw [show a ∈ Δ.carrier ↔ Γ.Adj v a from SimpleGraph.mem_neighborSet (G := Γ) v a]
    exact ha⟩
  have hqNmem : q ∈ N :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 N)
      (by rwa [← pCoreOf_eq (Γ := Γ) (G := G) (v := v) (n := n) (N := N) hN] at hq)
  let qN : QN := ⟨⟨q, hqNmem⟩, hq⟩
  let O : Set Δ := MulAction.orbit QN aΔ
  have hblock : MulAction.IsBlock N O :=
    MulAction.IsBlock.orbit_of_normal (G := N) (N := QN) aΔ
  have hOnonempty : O.Nonempty := ⟨aΔ, MulAction.mem_orbit_self aΔ⟩
  have hdvdΔ : Set.ncard O ∣ Nat.card Δ :=
    hblock.ncard_dvd_card hOnonempty
  haveI hΔfinite : Finite (Γ.neighborSet v) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; have := Nat.two_pow_pos n; omega)
  haveI : Finite Δ :=
    Finite.of_injective (fun x : Δ => (⟨x.1, x.2⟩ : Γ.neighborSet v))
      (fun a b h => Subtype.ext (congrArg Subtype.val h))
  have hΔcard : Nat.card Δ = 2 ^ n + 1 := by
    rw [← hcard]
    exact Nat.card_congr
      { toFun := fun x : Δ => (⟨x.1, x.2⟩ : Γ.neighborSet v)
        invFun := fun x => (⟨x.1, x.2⟩ : Δ)
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
  have hdvdOdd : Set.ncard O ∣ 2 ^ n + 1 := by
    rwa [hΔcard] at hdvdΔ
  obtain ⟨k, hk⟩ := hQNp.exists_card_eq
  haveI : Fintype QN := Fintype.ofFinite _
  haveI : Fintype (MulAction.orbit QN aΔ) := Fintype.ofFinite _
  have horbit_dvd : Set.ncard O ∣ 2 ^ k := by
    have hmul := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := QN) aΔ
    have hcardO : Fintype.card (MulAction.orbit QN aΔ) = Set.ncard O := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    have hcardQ : Fintype.card QN = 2 ^ k := by
      rw [← Nat.card_eq_fintype_card]; exact hk
    rw [hcardO, hcardQ] at hmul
    exact ⟨Fintype.card (MulAction.stabilizer QN aΔ), hmul.symm⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp horbit_dvd
  have hOdd : Odd (2 ^ n + 1) := by
    have heven : Even (2 ^ n) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    exact heven.add_odd odd_one
  have hOddO : Odd (Set.ncard O) := Odd.of_dvd_nat hOdd hdvdOdd
  have hj0 : j = 0 := by
    cases j with
    | zero => rfl
    | succ j =>
        exfalso
        have heven : Even (2 ^ (j + 1)) := by
          rw [pow_succ]
          exact even_two.mul_left _
        exact (Nat.not_even_iff_odd.mpr (hj ▸ hOddO)) heven
  have hOcard : Set.ncard O = 1 := by
    rw [hj, hj0, pow_zero]
  haveI : Subsingleton (MulAction.orbit QN aΔ) := by
    have h1 : Nat.card (MulAction.orbit QN aΔ) = 1 := by
      rw [Nat.card_coe_set_eq]
      simpa [O] using hOcard
    exact (Nat.card_eq_one_iff_unique.mp h1).1
  have hqfix : qN • aΔ = aΔ := by
    have hsingle : (⟨qN • aΔ, MulAction.mem_orbit aΔ qN⟩ : MulAction.orbit QN aΔ) =
        ⟨aΔ, MulAction.mem_orbit_self aΔ⟩ := Subsingleton.elim _ _
    exact congrArg Subtype.val hsingle
  have hqfixV : (qN : N) • a = a := congrArg Subtype.val hqfix
  simpa [qN, MulAction.subgroup_smul_def] using hqfixV

theorem N_fixes_neighbors_mem_Q (hN : IsLocL2 Γ G v n N)
    (hadj : ∀ (g : G) (u w : V), Γ.Adj (g • u) (g • w) ↔ Γ.Adj u w)
    (hfin : Finite (MulAction.stabilizer G v))
    (hcard : Nat.card (Γ.neighborSet v) = 2 ^ n + 1) (hn : 1 ≤ n)
    {x : N} (hx : ∀ a : V, Γ.Adj v a → (x : G) • a = a) :
    (x : G) ∈ pCoreOf 2 (MulAction.stabilizer G v) := by
  classical
  let Gv := MulAction.stabilizer G v
  let L := PSL(2, GaloisField 2 n)
  haveI : Finite N :=
    Finite.of_injective
      (fun x : N => (⟨(x : G), hN.le x.2⟩ : Gv))
      (fun a b h => Subtype.ext
        (congrArg (fun z : Gv => (z : G)) h))
  let Δ : SubMulAction N V := hN.neighborAction hadj
  have htrans : MulAction.IsPretransitive N Δ := hN.neighborAction_isPretransitive hadj
  haveI := htrans
  haveI hΔfinite : Finite (Γ.neighborSet v) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; have := Nat.two_pow_pos n; omega)
  haveI : Finite Δ :=
    Finite.of_injective (fun x : Δ => (⟨x.1, x.2⟩ : Γ.neighborSet v))
      (fun a b h => Subtype.ext (congrArg Subtype.val h))
  have hΔcard : Nat.card Δ = 2 ^ n + 1 := by
    rw [← hcard]
    exact Nat.card_congr
      { toFun := fun x : Δ => (⟨x.1, x.2⟩ : Γ.neighborSet v)
        invFun := fun x => (⟨x.1, x.2⟩ : Δ)
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
  let ρ : N →* Equiv.Perm Δ := MulAction.toPermHom N Δ
  let C : Subgroup N := MonoidHom.ker ρ
  have hCmem : ∀ y : N, y ∈ C ↔ ∀ a : Δ, y • a = a := by
    intro y
    rw [show y ∈ C ↔ ρ y = 1 from MonoidHom.mem_ker, MulAction.toPermHom_apply]
    constructor
    · intro h a
      simpa [MulAction.toPermHom_apply] using
        congrArg (fun e : Equiv.Perm Δ => e a) h
    · intro h
      ext a
      exact congrArg Subtype.val (h a)
  let QN : Subgroup N := (pCoreOf 2 (MulAction.stabilizer G v)).subgroupOf N
  have hker : MonoidHom.ker hN.phi = QN := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hN.phi_ker y
  have hQNleC : QN ≤ C := by
    intro q hq
    rw [hCmem]
    intro a
    apply Subtype.ext
    have hqQ : (q : G) ∈ pCoreOf 2 (MulAction.stabilizer G v) :=
      Subgroup.mem_subgroupOf.mp hq
    exact hN.Q_fixes_neighbors hadj hfin hcard hn a.1 a.2 (q : G) hqQ
  have hCnormal : C.Normal := inferInstance
  have hφsurj : Function.Surjective hN.phi := by
    intro y
    obtain ⟨q, rfl⟩ := hN.quot.some.surjective y
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥N) q
    exact ⟨m, rfl⟩
  let B : Subgroup L := C.map hN.phi
  have hBnormal : B.Normal := hCnormal.map hN.phi hφsurj
  have hker_le_C : MonoidHom.ker hN.phi ≤ C := by
    rw [hker]
    exact hQNleC
  have hBne : B ≠ ⊤ := by
    intro hBtop
    have hCtop : C = ⊤ := by
      apply top_unique
      intro y _
      have hyB : hN.phi y ∈ B := by
        rw [hBtop]
        exact Subgroup.mem_top _
      obtain ⟨c, hcC, hcφ⟩ := Subgroup.mem_map.mp hyB
      have hcy : c⁻¹ * y ∈ C := by
        have h1 : hN.phi (c⁻¹ * y) = 1 := by
          rw [map_mul, map_inv, hcφ]
          simp
        have h1' : c⁻¹ * y ∈ MonoidHom.ker hN.phi := by
          simpa [MonoidHom.mem_ker] using h1
        have h2 : c⁻¹ * y ∈ QN := by rwa [← hker]
        exact hQNleC h2
      have hy : y = c * (c⁻¹ * y) := by group
      rw [hy]
      exact C.mul_mem hcC hcy
    have htriv : ∀ y : N, ∀ a : Δ, y • a = a := by
      intro y a
      have hyC : y ∈ C := by rw [hCtop]; exact Subgroup.mem_top _
      exact (hCmem y).mp hyC a
    have hne : Nontrivial Δ :=
      Finite.one_lt_card_iff_nontrivial.mp (by
        rw [hΔcard]
        have : 2 ≤ 2 ^ n := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
        omega)
    obtain ⟨a, b, hab⟩ := exists_pair_ne Δ
    obtain ⟨g, hg⟩ := htrans.exists_smul_eq a b
    have hga : g • a = a := htriv g a
    exact hab (by rw [← hg, hga])
  by_cases hn2 : 2 ≤ n
  ·
    haveI : IsSimpleGroup L := by
      refine Matrix.ProjectiveSpecialLinearGroup.rank_two_simple ?_
      rw [GaloisField.card 2 n (by omega)]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    have hBbot : B = ⊥ := by
      rcases hBnormal.eq_bot_or_eq_top with h | h
      · exact h
      · exact absurd h hBne
    have hCleQN : C ≤ QN := by
      intro c hc
      have hφc : hN.phi c = 1 := by
        have hcB : hN.phi c ∈ B := ⟨c, hc, rfl⟩
        rw [hBbot] at hcB
        simpa using hcB
      rw [Subgroup.mem_subgroupOf]
      exact (hN.phi_ker c).mp hφc
    have hxC : x ∈ C := by
      rw [hCmem]
      intro a
      apply Subtype.ext
      exact hx a.1 a.2
    have hxQN : x ∈ QN := hCleQN hxC
    exact Subgroup.mem_subgroupOf.mp hxQN
  ·
    have hn1 : n = 1 := by omega
    have hΔcard3 : Nat.card Δ = 3 := by
      rw [hΔcard, hn1]
      norm_num
    have hLcard : Nat.card L = 6 := by
      change Nat.card (PSL(2, GaloisField 2 n)) = 6
      rw [hn1]
      have h := CFSG.Walter.psl2_even_card (f := 1) (by omega)
      norm_num at h
      exact h
    have hPermCard : Nat.card (Equiv.Perm Δ) = 6 := by
      rw [Nat.card_perm, hΔcard3]
      norm_num
    have hCindex_eq : C.index = Nat.card (N ⧸ C) := Subgroup.index_eq_card (H := C)
    have hCindex_dvd6 : C.index ∣ 6 := by
      have hcardq : Nat.card (N ⧸ C) = Nat.card ρ.range :=
        Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv
      have hrange : Nat.card ρ.range ∣ 6 := by
        have h := Subgroup.card_subgroup_dvd_card ρ.range
        rwa [hPermCard] at h
      rw [hCindex_eq, hcardq]
      exact hrange
    have hCindex_dvd3 : 3 ∣ C.index := by
      have hΔne : Nonempty Δ :=
        (Nat.card_pos_iff.mp (by rw [hΔcard3]; norm_num)).1
      obtain ⟨aΔ⟩ := hΔne
      let Na : Subgroup N := MulAction.stabilizer N aΔ
      have hC_le_Na : C ≤ Na := by
        intro c hc
        rw [MulAction.mem_stabilizer_iff]
        exact (hCmem c).mp hc aΔ
      have hNa_index : Na.index = 3 := by
        rw [MulAction.index_stabilizer_of_transitive N aΔ, hΔcard3]
      have hmul := Subgroup.relIndex_mul_index hC_le_Na
      rw [hNa_index] at hmul
      refine ⟨C.relIndex Na, ?_⟩
      rw [mul_comm]
      exact hmul.symm
    have hBindex_eq : B.index = C.index := by
      exact Subgroup.index_map_eq (f := hN.phi) (H := C) hφsurj hker_le_C
    have hBindex_dvd6 : B.index ∣ 6 := by
      rw [hBindex_eq]; exact hCindex_dvd6
    have hBindex_dvd3 : 3 ∣ B.index := by
      rw [hBindex_eq]; exact hCindex_dvd3
    have hBindex_ne1 : B.index ≠ 1 := fun h => hBne (Subgroup.index_eq_one.mp h)
    have hBindex_le : B.index ≤ 6 := Nat.le_of_dvd (by norm_num) hBindex_dvd6
    have hBindex_ge : 1 ≤ B.index := by
      rw [Nat.one_le_iff_ne_zero]
      exact Subgroup.index_ne_zero_of_finite
    have hBbot : B = ⊥ := by
      interval_cases hBidx : B.index
      · exfalso
        exact hBindex_ne1 rfl
      · norm_num at hBindex_dvd3
      · have hmul := Subgroup.card_mul_index B
        rw [show B.index = 3 from hBidx, hLcard] at hmul
        have hBcard : Nat.card B = 2 := by omega
        have hcenter := CFSG.Semidihedral.Local.le_center_of_normal_card_two hBnormal hBcard
        have hbot : Subgroup.center L = ⊥ := by
          change Subgroup.center (PSL(2, GaloisField 2 n)) = ⊥
          rw [hn1]
          exact psl2_center_eq_bot
        rw [hbot] at hcenter
        exact le_bot_iff.mp hcenter
      · norm_num at hBindex_dvd3
      · norm_num at hBindex_dvd3
      · have hmul := Subgroup.card_mul_index B
        rw [show B.index = 6 from hBidx, hLcard] at hmul
        have hBcard : Nat.card B = 1 := by omega
        exact Subgroup.eq_bot_of_card_eq B hBcard
    have hCleQN : C ≤ QN := by
      intro c hc
      have hφc : hN.phi c = 1 := by
        have hcB : hN.phi c ∈ B := ⟨c, hc, rfl⟩
        rw [hBbot] at hcB
        simpa using hcB
      rw [Subgroup.mem_subgroupOf]
      exact (hN.phi_ker c).mp hφc
    have hxC : x ∈ C := by
      rw [hCmem]
      intro a
      apply Subtype.ext
      exact hx a.1 a.2
    have hxQN : x ∈ QN := hCleQN hxC
    exact Subgroup.mem_subgroupOf.mp hxQN

@[expose] def pointSubgroup (hN : IsLocL2 Γ G v n N) (a : V) : Subgroup N :=
  (N ⊓ MulAction.stabilizer G a).subgroupOf N

@[expose] noncomputable def pointBorel (hN : IsLocL2 Γ G v n N) (a : V) :
    Subgroup (PSL(2, GaloisField 2 n)) :=
  (hN.pointSubgroup a).map hN.phi

theorem card_pointBorel (hN : IsLocL2 Γ G v n N)
    (hadj : ∀ (g : G) (u w : V), Γ.Adj (g • u) (g • w) ↔ Γ.Adj u w)
    (hfin : Finite (MulAction.stabilizer G v))
    (hcard : Nat.card (Γ.neighborSet v) = 2 ^ n + 1) (hn : 1 ≤ n)
    {a : V} (ha : Γ.Adj v a) :
    Nat.card (hN.pointBorel a) = 2 ^ n * (2 ^ n - 1) := by
  classical
  let Gv := MulAction.stabilizer G v
  let L := PSL(2, GaloisField 2 n)
  haveI : Finite N :=
    Finite.of_injective
      (fun x : N => (⟨(x : G), hN.le x.2⟩ : Gv))
      (fun a b h => Subtype.ext
        (congrArg (fun z : Gv => (z : G)) h))
  let Δ : SubMulAction N V := hN.neighborAction hadj
  have htrans : MulAction.IsPretransitive N Δ := hN.neighborAction_isPretransitive hadj
  haveI := htrans
  haveI hΔfinite : Finite (Γ.neighborSet v) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; have := Nat.two_pow_pos n; omega)
  haveI : Finite Δ :=
    Finite.of_injective (fun x : Δ => (⟨x.1, x.2⟩ : Γ.neighborSet v))
      (fun a b h => Subtype.ext (congrArg Subtype.val h))
  have hΔcard : Nat.card Δ = 2 ^ n + 1 := by
    rw [← hcard]
    exact Nat.card_congr
      { toFun := fun x : Δ => (⟨x.1, x.2⟩ : Γ.neighborSet v)
        invFun := fun x => (⟨x.1, x.2⟩ : Δ)
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
  let aΔ : Δ := ⟨a, by
    show a ∈ Δ.carrier
    rw [show a ∈ Δ.carrier ↔ Γ.Adj v a from SimpleGraph.mem_neighborSet (G := Γ) v a]
    exact ha⟩
  have hNa : hN.pointSubgroup a = MulAction.stabilizer N aΔ := by
    ext x
    change ((x : G) ∈ N ∧ (x : G) • a = a) ↔ x • aΔ = aΔ
    constructor
    · intro h
      apply Subtype.ext
      rw [SubMulAction.val_smul, MulAction.subgroup_smul_def]
      exact h.2
    · intro h
      refine ⟨x.2, ?_⟩
      have hval : ((x • aΔ : Δ) : V) = (x : G) • a := by
        rw [SubMulAction.val_smul, MulAction.subgroup_smul_def]
      rw [← hval]
      exact congrArg (fun z : Δ => (z : V)) h
  let QN : Subgroup N := (pCoreOf 2 Gv).subgroupOf N
  have hker : MonoidHom.ker hN.phi = QN := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hN.phi_ker y
  have hQlePoint : QN ≤ hN.pointSubgroup a := by
    intro q hq
    rw [hNa, MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    have hqQ : (q : G) ∈ pCoreOf 2 Gv := Subgroup.mem_subgroupOf.mp hq
    exact hN.Q_fixes_neighbors hadj hfin hcard hn a ha (q : G) hqQ
  have hφsurj : Function.Surjective hN.phi := by
    intro y
    obtain ⟨q, rfl⟩ := hN.quot.some.surjective y
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥N) q
    exact ⟨m, rfl⟩
  have hBindex : (hN.pointBorel a).index = 2 ^ n + 1 := by
    have hindex_map : (hN.pointBorel a).index = (hN.pointSubgroup a).index := by
      exact Subgroup.index_map_eq (f := hN.phi) (H := hN.pointSubgroup a) hφsurj
        (by rw [hker]; exact hQlePoint)
    rw [hindex_map, hNa, MulAction.index_stabilizer_of_transitive N aΔ, hΔcard]
  have hBcard_mul : Nat.card (hN.pointBorel a) * (2 ^ n + 1) = Nat.card L := by
    have h := Subgroup.card_mul_index (hN.pointBorel a)
    rwa [hBindex] at h
  have hLfac : Nat.card L = (2 ^ n * (2 ^ n - 1)) * (2 ^ n + 1) := by
    rw [show L = PSL(2, GaloisField 2 n) from rfl, CFSG.Walter.psl2_even_card (f := n) (by omega)]
    have hsq : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
      rw [show (1 : ℕ) = 1 ^ 2 by norm_num, Nat.sq_sub_sq, one_pow, mul_comm]
    rw [hsq]
    ring
  rw [hLfac] at hBcard_mul
  exact Nat.eq_of_mul_eq_mul_right (by positivity) hBcard_mul

theorem exists_pointSylow (hN : IsLocL2 Γ G v n N)
    (hadj : ∀ (g : G) (u w : V), Γ.Adj (g • u) (g • w) ↔ Γ.Adj u w)
    (hfin : Finite (MulAction.stabilizer G v))
    (hcard : Nat.card (Γ.neighborSet v) = 2 ^ n + 1) (hn : 1 ≤ n)
    {a : V} (ha : Γ.Adj v a) :
    ∃ U : Sylow 2 (PSL(2, GaloisField 2 n)),
      (U : Subgroup (PSL(2, GaloisField 2 n))) ≤ hN.pointBorel a ∧
        hN.pointBorel a = Subgroup.normalizer
          (U : Set (PSL(2, GaloisField 2 n))) :=
  psl2_borel_of_card hn (hN.card_pointBorel hadj hfin hcard hn ha)

@[expose] noncomputable def pointSylow (hN : IsLocL2 Γ G v n N)
    (hadj : ∀ (g : G) (u w : V), Γ.Adj (g • u) (g • w) ↔ Γ.Adj u w)
    (hfin : Finite (MulAction.stabilizer G v))
    (hcard : Nat.card (Γ.neighborSet v) = 2 ^ n + 1) (hn : 1 ≤ n) (a : V) :
    Sylow 2 (PSL(2, GaloisField 2 n)) := by
  classical
  exact if ha : Γ.Adj v a then
    Classical.choose (hN.exists_pointSylow hadj hfin hcard hn ha)
  else default

theorem pointSylow_spec (hN : IsLocL2 Γ G v n N)
    (hadj : ∀ (g : G) (u w : V), Γ.Adj (g • u) (g • w) ↔ Γ.Adj u w)
    (hfin : Finite (MulAction.stabilizer G v))
    (hcard : Nat.card (Γ.neighborSet v) = 2 ^ n + 1) (hn : 1 ≤ n)
    {a : V} (ha : Γ.Adj v a) :
    (hN.pointSylow hadj hfin hcard hn a :
        Subgroup (PSL(2, GaloisField 2 n))) ≤ hN.pointBorel a ∧
      hN.pointBorel a = Subgroup.normalizer
        (hN.pointSylow hadj hfin hcard hn a :
          Set (PSL(2, GaloisField 2 n))) := by
  rw [pointSylow, dif_pos ha]
  exact Classical.choose_spec (hN.exists_pointSylow hadj hfin hcard hn ha)

theorem sylow_eq_of_le_normalizer (hn : 1 ≤ n)
    {U V : Sylow 2 (PSL(2, GaloisField 2 n))}
    (hV : (V : Subgroup (PSL(2, GaloisField 2 n))) ≤
      Subgroup.normalizer (U : Set (PSL(2, GaloisField 2 n)))) :
    V = U := by
  classical
  have hUcard : Nat.card (U : Subgroup (PSL(2, GaloisField 2 n))) = 2 ^ n :=
    psl2_sylow_two_card hn U
  have hVcard : Nat.card (V : Subgroup (PSL(2, GaloisField 2 n))) = 2 ^ n :=
    psl2_sylow_two_card hn V
  have hq2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  haveI : Nontrivial (V : Subgroup (PSL(2, GaloisField 2 n))) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hVcard]; omega)
  obtain ⟨x, hx1⟩ := exists_ne (1 : (V : Subgroup (PSL(2, GaloisField 2 n))))
  have hxV' : (x : PSL(2, GaloisField 2 n)) ∈
      (V : Subgroup (PSL(2, GaloisField 2 n))) := x.2
  have hx1' : (x : PSL(2, GaloisField 2 n)) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hxN : (x : PSL(2, GaloisField 2 n)) ∈
      Subgroup.normalizer (U : Set (PSL(2, GaloisField 2 n))) := hV hxV'
  exact ((psl2_sylow_two_normalizes_iff hn (U := V) (V := U) hxV' hx1').mp hxN).symm

theorem pointSubgroup_eq_stabilizer (hN : IsLocL2 Γ G v n N)
    (hadj : ∀ (g : G) (u w : V), Γ.Adj (g • u) (g • w) ↔ Γ.Adj u w)
    {a : V} (ha : Γ.Adj v a) :
    hN.pointSubgroup a = MulAction.stabilizer N
      (⟨a, by
        show a ∈ (hN.neighborAction hadj).carrier
        rw [show a ∈ (hN.neighborAction hadj).carrier ↔ Γ.Adj v a from
          SimpleGraph.mem_neighborSet (G := Γ) v a]
        exact ha⟩ : hN.neighborAction hadj) := by
  classical
  let Δ : SubMulAction N V := hN.neighborAction hadj
  let aΔ : Δ := ⟨a, by
    show a ∈ Δ.carrier
    rw [show a ∈ Δ.carrier ↔ Γ.Adj v a from SimpleGraph.mem_neighborSet (G := Γ) v a]
    exact ha⟩
  change hN.pointSubgroup a = MulAction.stabilizer N aΔ
  ext x
  change ((x : G) ∈ N ∧ (x : G) • a = a) ↔ x • aΔ = aΔ
  constructor
  · intro h
    apply Subtype.ext
    rw [SubMulAction.val_smul, MulAction.subgroup_smul_def]
    exact h.2
  · intro h
    refine ⟨x.2, ?_⟩
    have hval : ((x • aΔ : Δ) : V) = (x : G) • a := by
      rw [SubMulAction.val_smul, MulAction.subgroup_smul_def]
    rw [← hval]
    exact congrArg (fun z : Δ => (z : V)) h

theorem pointSubgroup_smul (hN : IsLocL2 Γ G v n N)
    (hadj : ∀ (g : G) (u w : V), Γ.Adj (g • u) (g • w) ↔ Γ.Adj u w)
    {a : V} (ha : Γ.Adj v a) (n : N) :
    hN.pointSubgroup ((n : G) • a) =
      (hN.pointSubgroup a).map (MulAut.conj n).toMonoidHom := by
  classical
  let Δ : SubMulAction N V := hN.neighborAction hadj
  let aΔ : Δ := ⟨a, by
    show a ∈ Δ.carrier
    rw [show a ∈ Δ.carrier ↔ Γ.Adj v a from SimpleGraph.mem_neighborSet (G := Γ) v a]
    exact ha⟩
  have hmem : (n : G) • a ∈ (hN.neighborAction hadj).carrier :=
    (hN.neighborAction hadj).smul_mem n (by
      change Γ.Adj v a
      exact ha)
  have hna : (⟨(n : G) • a, hmem⟩ : Δ) = n • aΔ := rfl
  rw [pointSubgroup_eq_stabilizer hN hadj ha,
    pointSubgroup_eq_stabilizer hN hadj (by
      change Γ.Adj v ((n : G) • a)
      exact hmem)]
  rw [hna]
  exact MulAction.stabilizer_smul_eq_stabilizer_map_conj n aΔ

theorem pointBorel_smul (hN : IsLocL2 Γ G v n N)
    (hadj : ∀ (g : G) (u w : V), Γ.Adj (g • u) (g • w) ↔ Γ.Adj u w)
    {a : V} (ha : Γ.Adj v a) (n : N) :
    hN.pointBorel ((n : G) • a) =
      (hN.pointBorel a).map (MulAut.conj (hN.phi n)).toMonoidHom := by
  classical
  rw [pointBorel, pointBorel, pointSubgroup_smul hN hadj ha n, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, map_mul, map_inv]

theorem phi_surjective (hN : IsLocL2 Γ G v n N) : Function.Surjective hN.phi := by
  intro y
  obtain ⟨q, rfl⟩ := hN.quot.some.surjective y
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥N) q
  exact ⟨m, rfl⟩

theorem phi_ker_isPGroup (hN : IsLocL2 Γ G v n N) :
    IsPGroup 2 (MonoidHom.ker hN.phi) := by
  classical
  let Gv := MulAction.stabilizer G v
  let QN : Subgroup N := (pCoreOf 2 Gv).subgroupOf N
  have hQleN : pCoreOf 2 Gv ≤ N := by
    rw [← pCoreOf_eq (Γ := Γ) (G := G) (v := v) (n := n) (N := N) hN]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 N
  have hQp : IsPGroup 2 (pCoreOf 2 Gv) :=
    (CFSG.pCore_isPGroup (G := Gv) (p := 2)).map Gv.subtype
  have hQNp : IsPGroup 2 QN :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQleN).symm
  have hker : MonoidHom.ker hN.phi = QN := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hN.phi_ker y
  rwa [hker]

@[expose] noncomputable def pointSylowN (hN : IsLocL2 Γ G v n N)
    (hadj : ∀ (g : G) (u w : V), Γ.Adj (g • u) (g • w) ↔ Γ.Adj u w)
    (hfin : Finite (MulAction.stabilizer G v))
    (hcard : Nat.card (Γ.neighborSet v) = 2 ^ n + 1) (hn : 1 ≤ n) (a : V) :
    Sylow 2 N :=
  (hN.pointSylow hadj hfin hcard hn a).comapOfKerIsPGroup hN.phi
    (hN.phi_ker_isPGroup) (by
      rw [MonoidHom.range_eq_top.mpr hN.phi_surjective]
      exact le_top)

theorem pointBorel_eq_normalizer (hN : IsLocL2 Γ G v n N)
    (hadj : ∀ (g : G) (u w : V), Γ.Adj (g • u) (g • w) ↔ Γ.Adj u w)
    (hfin : Finite (MulAction.stabilizer G v))
    (hcard : Nat.card (Γ.neighborSet v) = 2 ^ n + 1) (hn : 1 ≤ n)
    {a : V} (ha : Γ.Adj v a) :
    hN.pointBorel a = Subgroup.normalizer
      (hN.pointSylow hadj hfin hcard hn a :
        Set (PSL(2, GaloisField 2 n))) :=
  (hN.pointSylow_spec hadj hfin hcard hn ha).2

theorem pointSubgroup_eq_comap_pointBorel (hN : IsLocL2 Γ G v n N)
    (hadj : ∀ (g : G) (u w : V), Γ.Adj (g • u) (g • w) ↔ Γ.Adj u w)
    (hfin : Finite (MulAction.stabilizer G v))
    (hcard : Nat.card (Γ.neighborSet v) = 2 ^ n + 1) (hn : 1 ≤ n)
    {a : V} (ha : Γ.Adj v a) :
    hN.pointSubgroup a = (hN.pointBorel a).comap hN.phi := by
  classical
  let Gv := MulAction.stabilizer G v
  let QN : Subgroup N := (pCoreOf 2 Gv).subgroupOf N
  have hQlePoint : QN ≤ hN.pointSubgroup a := by
    intro q hq
    rw [pointSubgroup_eq_stabilizer hN hadj ha, MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    have hqQ : (q : G) ∈ pCoreOf 2 Gv := Subgroup.mem_subgroupOf.mp hq
    exact hN.Q_fixes_neighbors hadj hfin hcard hn a ha (q : G) hqQ
  have hker : MonoidHom.ker hN.phi ≤ hN.pointSubgroup a := by
    have hkereq : MonoidHom.ker hN.phi = QN := by
      ext y
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact hN.phi_ker y
    rwa [hkereq]
  have h := Subgroup.comap_map_eq_self (f := hN.phi) (H := hN.pointSubgroup a) hker
  rw [← h]
  rfl

theorem pointSubgroup_eq_normalizer_pointSylowN (hN : IsLocL2 Γ G v n N)
    (hadj : ∀ (g : G) (u w : V), Γ.Adj (g • u) (g • w) ↔ Γ.Adj u w)
    (hfin : Finite (MulAction.stabilizer G v))
    (hcard : Nat.card (Γ.neighborSet v) = 2 ^ n + 1) (hn : 1 ≤ n)
    {a : V} (ha : Γ.Adj v a) :
    hN.pointSubgroup a = Subgroup.normalizer
      ((hN.pointSylowN hadj hfin hcard hn a : Sylow 2 N) : Subgroup N) := by
  classical
  rw [pointSubgroup_eq_comap_pointBorel hN hadj hfin hcard hn ha]
  rw [pointBorel_eq_normalizer hN hadj hfin hcard hn ha]
  have hL : Subgroup.comap hN.phi
      (Subgroup.normalizer ((hN.pointSylow hadj hfin hcard hn a :
        Subgroup (PSL(2, GaloisField 2 n))))) =
      Subgroup.normalizer (Subgroup.comap hN.phi
        ((hN.pointSylow hadj hfin hcard hn a :
          Subgroup (PSL(2, GaloisField 2 n))))) :=
    Subgroup.comap_normalizer_eq_of_surjective
      (H := (hN.pointSylow hadj hfin hcard hn a :
        Subgroup (PSL(2, GaloisField 2 n)))) (f := hN.phi) hN.phi_surjective
  have hR : ((hN.pointSylowN hadj hfin hcard hn a : Sylow 2 N) : Subgroup N) =
      Subgroup.comap hN.phi
        ((hN.pointSylow hadj hfin hcard hn a :
          Subgroup (PSL(2, GaloisField 2 n)))) :=
    Sylow.coe_comapOfKerIsPGroup (hN.pointSylow hadj hfin hcard hn a) hN.phi
      (hN.phi_ker_isPGroup) _
  exact hL

theorem pointSylow_surjective (hN : IsLocL2 Γ G v n N)
    (hadj : ∀ (g : G) (u w : V), Γ.Adj (g • u) (g • w) ↔ Γ.Adj u w)
    (hfin : Finite (MulAction.stabilizer G v))
    (hcard : Nat.card (Γ.neighborSet v) = 2 ^ n + 1) (hn : 1 ≤ n) :
    Function.Surjective (fun a : (hN.neighborAction hadj) =>
      hN.pointSylow hadj hfin hcard hn a.1) := by
  classical
  let L := PSL(2, GaloisField 2 n)
  let Δ : SubMulAction N V := hN.neighborAction hadj
  have hΔne : Nonempty Δ := by
    have hcard3 : 3 ≤ Nat.card Δ := by
      rw [show Nat.card Δ = 2 ^ n + 1 from by
        rw [show Nat.card Δ = Nat.card (Γ.neighborSet v) from by
          exact Nat.card_congr
            { toFun := fun x : Δ => (⟨x.1, x.2⟩ : Γ.neighborSet v)
              invFun := fun x => (⟨x.1, x.2⟩ : Δ)
              left_inv := by intro x; rfl
              right_inv := by intro x; rfl }]
        exact hcard]
      have h2 : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    exact (Nat.card_pos_iff.mp (by omega)).1
  obtain ⟨a0⟩ := hΔne
  let U0 : Sylow 2 L := hN.pointSylow hadj hfin hcard hn a0.1
  intro U
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L U0 U
  obtain ⟨n, hnφ⟩ := hN.phi_surjective g
  have hmem : (n : G) • a0.1 ∈ Δ.carrier :=
    Δ.smul_mem n a0.2
  let a1 : Δ := ⟨(n : G) • a0.1, hmem⟩
  refine ⟨a1, ?_⟩
  have hUeq : (U : Subgroup L) = (U0 : Subgroup L).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  have hUle : (U : Subgroup L) ≤ hN.pointBorel a1.1 := by
    rw [hUeq, ← hnφ]
    rw [show a1.1 = (n : G) • a0.1 from rfl,
      pointBorel_smul hN hadj (show Γ.Adj v a0.1 from a0.2) n]
    exact Subgroup.map_mono (hN.pointSylow_spec hadj hfin hcard hn (show Γ.Adj v a0.1 from a0.2)).1
  have hUnorm : (U : Subgroup L) ≤ Subgroup.normalizer
      ((hN.pointSylow hadj hfin hcard hn a1.1 : Sylow 2 L) :
        Set L) := by
    rwa [← pointBorel_eq_normalizer hN hadj hfin hcard hn
      (show Γ.Adj v a1.1 from a1.2)]
  have hEq : U = hN.pointSylow hadj hfin hcard hn a1.1 :=
    sylow_eq_of_le_normalizer hn hUnorm
  exact hEq.symm

theorem pointSylow_bijective (hN : IsLocL2 Γ G v n N)
    (hadj : ∀ (g : G) (u w : V), Γ.Adj (g • u) (g • w) ↔ Γ.Adj u w)
    (hfin : Finite (MulAction.stabilizer G v))
    (hcard : Nat.card (Γ.neighborSet v) = 2 ^ n + 1) (hn : 1 ≤ n) :
    Function.Bijective (fun a : (hN.neighborAction hadj) =>
      hN.pointSylow hadj hfin hcard hn a.1) := by
  classical
  let Δ : SubMulAction N V := hN.neighborAction hadj
  have hΔcard : Nat.card Δ = 2 ^ n + 1 := by
    rw [show Nat.card Δ = Nat.card (Γ.neighborSet v) from by
      exact Nat.card_congr
        { toFun := fun x : Δ => (⟨x.1, x.2⟩ : Γ.neighborSet v)
          invFun := fun x => (⟨x.1, x.2⟩ : Δ)
          left_inv := by intro x; rfl
          right_inv := by intro x; rfl }]
    exact hcard
  haveI : Finite Δ :=
    Nat.finite_of_card_ne_zero (by rw [hΔcard]; have := Nat.two_pow_pos n; omega)
  refine (hN.pointSylow_surjective hadj hfin hcard hn).bijective_of_nat_card_le ?_
  rw [hΔcard, CFSG.Walter.psl2_even_card_sylow (f := n) (by omega)]

theorem sylow_fixes_unique (hN : IsLocL2 Γ G v n N)
    (hadj : ∀ (g : G) (u w : V), Γ.Adj (g • u) (g • w) ↔ Γ.Adj u w)
    (hfin : Finite (MulAction.stabilizer G v))
    (hcard : Nat.card (Γ.neighborSet v) = 2 ^ n + 1) (hn : 1 ≤ n)
    (S : Sylow 2 N) :
    ∃! a : V, Γ.Adj v a ∧ ∀ x : N, x ∈ (S : Subgroup N) → (x : G) • a = a := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let L := PSL(2, GaloisField 2 n)
  let Δ : SubMulAction N V := hN.neighborAction hadj
  haveI : Finite N :=
    Finite.of_injective
      (fun x : N => (⟨(x : G), hN.le x.2⟩ : MulAction.stabilizer G v))
      (fun a b h => Subtype.ext
        (congrArg (fun z : MulAction.stabilizer G v => (z : G)) h))
  have hbij := hN.pointSylow_bijective hadj hfin hcard hn
  let U : Sylow 2 L := S.mapSurjective hN.phi_surjective
  obtain ⟨a0, ha0⟩ := hbij.2 U
  refine ⟨a0.1, ?_, ?_⟩
  · constructor
    · exact a0.2
    · intro x hx
      have hxU : hN.phi x ∈ (U : Subgroup L) := by
        rw [show (U : Subgroup L) = (S : Subgroup N).map hN.phi from
          rfl]
        exact Subgroup.mem_map_of_mem hN.phi hx
      have hxU' : hN.phi x ∈ (hN.pointSylow hadj hfin hcard hn a0.1 :
          Subgroup L) := by
        rwa [← ha0] at hxU
      have hxle : hN.phi x ∈ hN.pointBorel a0.1 :=
        (hN.pointSylow_spec hadj hfin hcard hn a0.2).1 hxU'
      have hxcomap : x ∈ (hN.pointBorel a0.1).comap hN.phi := hxle
      have hxpoint : x ∈ hN.pointSubgroup a0.1 := by
        rwa [← pointSubgroup_eq_comap_pointBorel hN hadj hfin hcard hn a0.2] at hxcomap
      have hxstab : x ∈ MulAction.stabilizer N a0 := by
        rwa [← pointSubgroup_eq_stabilizer hN hadj a0.2]
      exact congrArg (fun z : Δ => (z : V)) (MulAction.mem_stabilizer_iff.mp hxstab)
  · intro b hb
    have hbAdj : Γ.Adj v b := hb.1
    have hbfix : ∀ x : N, x ∈ (S : Subgroup N) → (x : G) • b = b := hb.2
    have hUle : (U : Subgroup L) ≤ hN.pointBorel b := by
      intro y hy
      rw [show (U : Subgroup L) = (S : Subgroup N).map hN.phi from rfl] at hy
      obtain ⟨x, hxS, hxy⟩ := Subgroup.mem_map.mp hy
      rw [← hxy]
      have hxpoint : x ∈ hN.pointSubgroup b := by
        rw [pointSubgroup_eq_stabilizer hN hadj hbAdj, MulAction.mem_stabilizer_iff]
        apply Subtype.ext
        exact hbfix x hxS
      have hxcomap : x ∈ (hN.pointBorel b).comap hN.phi := by
        rwa [← pointSubgroup_eq_comap_pointBorel hN hadj hfin hcard hn hbAdj]
      exact hxcomap
    have hUnorm : (U : Subgroup L) ≤ Subgroup.normalizer
        ((hN.pointSylow hadj hfin hcard hn b : Sylow 2 L) : Set L) := by
      rwa [← pointBorel_eq_normalizer hN hadj hfin hcard hn hbAdj]
    have hUeq : U = hN.pointSylow hadj hfin hcard hn b :=
      sylow_eq_of_le_normalizer hn hUnorm
    have hpointEq : hN.pointSylow hadj hfin hcard hn a0.1 =
        hN.pointSylow hadj hfin hcard hn b := ha0.trans hUeq
    have hab : a0 = (⟨b, hbAdj⟩ : Δ) := hbij.1 hpointEq
    exact (congrArg Subtype.val hab).symm

theorem fixes_unique_of_mem_sylow_not_pcore (hN : IsLocL2 Γ G v n N)
    (hadj : ∀ (g : G) (u w : V), Γ.Adj (g • u) (g • w) ↔ Γ.Adj u w)
    (hfin : Finite (MulAction.stabilizer G v))
    (hcard : Nat.card (Γ.neighborSet v) = 2 ^ n + 1) (hn : 1 ≤ n)
    (S : Sylow 2 N) {x : N} (hxS : x ∈ (S : Subgroup N))
    (hxQ : (x : G) ∉ pCoreOf 2 (MulAction.stabilizer G v)) :
    ∃! a : V, Γ.Adj v a ∧ (x : G) • a = a := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let L := PSL(2, GaloisField 2 n)
  let Δ : SubMulAction N V := hN.neighborAction hadj
  haveI : Finite N :=
    Finite.of_injective
      (fun x : N => (⟨(x : G), hN.le x.2⟩ : MulAction.stabilizer G v))
      (fun a b h => Subtype.ext
        (congrArg (fun z : MulAction.stabilizer G v => (z : G)) h))
  have hbij := hN.pointSylow_bijective hadj hfin hcard hn
  let U : Sylow 2 L := S.mapSurjective hN.phi_surjective
  have hUcoe : (U : Subgroup L) = (S : Subgroup N).map hN.phi := rfl
  obtain ⟨a0, ha0, huniq⟩ := hN.sylow_fixes_unique hadj hfin hcard hn S
  have hphi_ne : hN.phi x ≠ 1 := fun h => hxQ ((hN.phi_ker x).mp h)
  have hxU : hN.phi x ∈ (U : Subgroup L) := by
    rw [hUcoe]
    exact Subgroup.mem_map_of_mem hN.phi hxS
  have hUa0 : U = hN.pointSylow hadj hfin hcard hn a0 := by
    apply sylow_eq_of_le_normalizer hn
    rw [← pointBorel_eq_normalizer hN hadj hfin hcard hn ha0.1]
    intro y hy
    rw [hUcoe] at hy
    obtain ⟨s, hsS, hsy⟩ := Subgroup.mem_map.mp hy
    rw [← hsy]
    have hspoint : s ∈ hN.pointSubgroup a0 := by
      rw [pointSubgroup_eq_stabilizer hN hadj ha0.1, MulAction.mem_stabilizer_iff]
      apply Subtype.ext
      exact ha0.2 s hsS
    have hscomap : s ∈ (hN.pointBorel a0).comap hN.phi := by
      rwa [← pointSubgroup_eq_comap_pointBorel hN hadj hfin hcard hn ha0.1]
    exact hscomap
  refine ⟨a0, ⟨ha0.1, ha0.2 x hxS⟩, ?_⟩
  intro b hb
  have hbAdj : Γ.Adj v b := hb.1
  have hxfix : (x : G) • b = b := hb.2
  have hxpoint : x ∈ hN.pointSubgroup b := by
    rw [pointSubgroup_eq_stabilizer hN hadj hbAdj, MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    exact hxfix
  have hxB : hN.phi x ∈ hN.pointBorel b := by
    have hxcomap : x ∈ (hN.pointBorel b).comap hN.phi := by
      rwa [← pointSubgroup_eq_comap_pointBorel hN hadj hfin hcard hn hbAdj]
    exact hxcomap
  have hxnorm : hN.phi x ∈ Subgroup.normalizer
      ((hN.pointSylow hadj hfin hcard hn b : Sylow 2 L) : Set L) := by
    rwa [← pointBorel_eq_normalizer hN hadj hfin hcard hn hbAdj]
  have hVeq : hN.pointSylow hadj hfin hcard hn b = U :=
    ((psl2_sylow_two_normalizes_iff hn (U := U)
      (V := hN.pointSylow hadj hfin hcard hn b) hxU hphi_ne).mp hxnorm)
  have hpointEq : hN.pointSylow hadj hfin hcard hn a0 =
      hN.pointSylow hadj hfin hcard hn b := by
    calc
      hN.pointSylow hadj hfin hcard hn a0 = U := hUa0.symm
      _ = hN.pointSylow hadj hfin hcard hn b := hVeq.symm
  have hab : (⟨a0, ha0.1⟩ : Δ) = (⟨b, hbAdj⟩ : Δ) := hbij.1 (by simpa using hpointEq)
  exact (congrArg Subtype.val hab).symm

theorem pCoreOf_subgroupOf_le_sylow (hN : IsLocL2 Γ G v n N) (S : Sylow 2 N) :
    (pCoreOf 2 (MulAction.stabilizer G v)).subgroupOf N ≤ (S : Subgroup N) := by
  classical
  let Gv := MulAction.stabilizer G v
  let QN : Subgroup N := (pCoreOf 2 Gv).subgroupOf N
  have hQNnormal : QN.Normal := by
    have hQeq : QN = CFSG.pCore 2 ↥N := by
      dsimp [QN]
      rw [← pCoreOf_eq (Γ := Γ) (G := G) (v := v) (n := n) (N := N) hN]
      ext x
      constructor
      · intro hx
        rw [Subgroup.mem_subgroupOf] at hx
        exact (Subgroup.mem_map_iff_mem N.subtype_injective).mp hx
      · intro hx
        rw [Subgroup.mem_subgroupOf]
        exact Subgroup.mem_map_of_mem N.subtype hx
    rw [hQeq]
    infer_instance
  have hQNp : IsPGroup 2 QN := by
    have hQeq : QN = CFSG.pCore 2 ↥N := by
      dsimp [QN]
      rw [← pCoreOf_eq (Γ := Γ) (G := G) (v := v) (n := n) (N := N) hN]
      ext x
      constructor
      · intro hx
        rw [Subgroup.mem_subgroupOf] at hx
        exact (Subgroup.mem_map_iff_mem N.subtype_injective).mp hx
      · intro hx
        rw [Subgroup.mem_subgroupOf]
        exact Subgroup.mem_map_of_mem N.subtype hx
    rw [hQeq]
    exact CFSG.pCore_isPGroup (G := ↥N) (p := 2)
  exact hQNp.le_sylow_of_normal S

private theorem torus_cyclic_of_ne_bot (hN : IsLocL2 Γ G v n N)
    (hadj : ∀ (g : G) (u w : V), Γ.Adj (g • u) (g • w) ↔ Γ.Adj u w)
    (hfin : Finite (MulAction.stabilizer G v))
    (hcard : Nat.card (Γ.neighborSet v) = 2 ^ n + 1) (hn : 1 ≤ n)
    (S : Sylow 2 N) (K : Subgroup N)
    (hKS : K ⊓ (S : Subgroup N) = ⊥)
    (hsup : K ⊔ (S : Subgroup N) =
      Subgroup.normalizer ((S : Subgroup N) : Set N))
    (hKne : K ≠ ⊥) :
    IsCyclic K ∧ Nat.card K = 2 ^ n - 1 := by
  classical
  let L := PSL(2, GaloisField 2 n)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite N :=
    Finite.of_injective
      (fun x : N => (⟨(x : G), hN.le x.2⟩ : MulAction.stabilizer G v))
      (fun a b h => Subtype.ext
        (congrArg (fun z : MulAction.stabilizer G v => (z : G)) h))
  let U : Sylow 2 L := S.mapSurjective hN.phi_surjective
  let D : Subgroup L := K.map hN.phi
  have hker_le_S : MonoidHom.ker hN.phi ≤ (S : Subgroup N) := by
    have h := hN.pCoreOf_subgroupOf_le_sylow S
    have hker : MonoidHom.ker hN.phi = (pCoreOf 2 (MulAction.stabilizer G v)).subgroupOf N := by
      ext y
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact hN.phi_ker y
    rwa [hker]
  have hDinf : D ⊓ (U : Subgroup L) = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyD, hyU⟩
    obtain ⟨k, hkK, rfl⟩ := Subgroup.mem_map.mp hyD
    have hkU : hN.phi k ∈ (U : Subgroup L) := hyU
    rw [show (U : Subgroup L) = (S : Subgroup N).map hN.phi from rfl] at hkU
    obtain ⟨s, hsS, hsk⟩ := Subgroup.mem_map.mp hkU
    have hker : s⁻¹ * k ∈ MonoidHom.ker hN.phi := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hsk, inv_mul_cancel]
    have hkerS : s⁻¹ * k ∈ (S : Subgroup N) := hker_le_S hker
    have hkS : k ∈ (S : Subgroup N) := by
      have : k = s * (s⁻¹ * k) := by group
      rw [this]
      exact (S : Subgroup N).mul_mem hsS hkerS
    have hkbot : k ∈ (⊥ : Subgroup N) := by
      rw [← hKS]
      exact ⟨hkK, hkS⟩
    rw [Subgroup.mem_bot] at hkbot
    simp [hkbot]
  have hDsup : D ⊔ (U : Subgroup L) =
      Subgroup.normalizer ((U : Subgroup L) : Set L) := by
    have hmapnorm : (Subgroup.normalizer ((S : Subgroup N) : Set N)).map hN.phi =
        Subgroup.normalizer ((U : Subgroup L) : Set L) := by
      have hUcomap : (U : Subgroup L).comap hN.phi = (S : Subgroup N) := by
        rw [show (U : Subgroup L) = (S : Subgroup N).map hN.phi from rfl]
        exact Subgroup.comap_map_eq_self (f := hN.phi) hker_le_S
      have hcomap : (Subgroup.normalizer ((U : Subgroup L) : Set L)).comap hN.phi =
          Subgroup.normalizer ((S : Subgroup N) : Set N) := by
        rw [Subgroup.comap_normalizer_eq_of_surjective
          (H := (U : Subgroup L)) (f := hN.phi) hN.phi_surjective]
        rw [hUcomap]
      rw [← hcomap]
      exact Subgroup.map_comap_eq_self_of_surjective hN.phi_surjective _
    calc
      D ⊔ (U : Subgroup L) = (K ⊔ (S : Subgroup N)).map hN.phi := by
        simp [D, U, Subgroup.map_sup]
      _ = (Subgroup.normalizer ((S : Subgroup N) : Set N)).map hN.phi := by rw [hsup]
      _ = _ := hmapnorm
  have hDcyc : IsCyclic D := psl2_torus_cyclic hn hDinf hDsup
  have hDcard : Nat.card D = 2 ^ n - 1 := psl2_torus_card hn hDinf hDsup
  let psi : K →* D :=
    { toFun := fun k => ⟨hN.phi k, Subgroup.mem_map_of_mem hN.phi k.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hpsi_inj : Function.Injective psi := by
    intro a b hab
    have hφ : hN.phi a = hN.phi b := congrArg Subtype.val hab
    have hker : (a : N) * (b : N)⁻¹ ∈ MonoidHom.ker hN.phi := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, mul_inv_cancel]
    have hkerS : (a : N) * (b : N)⁻¹ ∈ (S : Subgroup N) := hker_le_S hker
    have habS : (a : N) * (b : N)⁻¹ ∈ K ⊓ (S : Subgroup N) := ⟨K.mul_mem a.2 (K.inv_mem b.2), hkerS⟩
    rw [hKS] at habS
    rw [Subgroup.mem_bot] at habS
    have : a = b := by
      have := congrArg (fun z : N => z * b) habS
      simpa [mul_assoc] using this
    exact this
  have hpsi_surj : Function.Surjective psi := by
    intro d
    obtain ⟨k, hkK, hkd⟩ := Subgroup.mem_map.mp d.2
    exact ⟨⟨k, hkK⟩, Subtype.ext hkd⟩
  let e : K ≃* D := MulEquiv.ofBijective psi ⟨hpsi_inj, hpsi_surj⟩
  have hKcyc : IsCyclic K := isCyclic_of_injective psi hpsi_inj
  have hKcard : Nat.card K = 2 ^ n - 1 := by
    rw [show Nat.card K = Nat.card D from Nat.card_congr e.toEquiv, hDcard]
  exact ⟨hKcyc, hKcard⟩

theorem sylow_sup_zpowers_eq (hN : IsLocL2 Γ G v n N)
    (hadj : ∀ (g : G) (u w : V), Γ.Adj (g • u) (g • w) ↔ Γ.Adj u w)
    (hfin : Finite (MulAction.stabilizer G v))
    (hcard : Nat.card (Γ.neighborSet v) = 2 ^ n + 1) (hn : 1 ≤ n)
    (S : Sylow 2 N) {g : N}
    (hg : g ∉ Subgroup.normalizer ((S : Subgroup N) : Set N)) :
    (S : Subgroup N) ⊔ Subgroup.zpowers g = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let L := PSL(2, GaloisField 2 n)
  haveI : Finite N :=
    Finite.of_injective
      (fun x : N => (⟨(x : G), hN.le x.2⟩ : MulAction.stabilizer G v))
      (fun a b h => Subtype.ext
        (congrArg (fun z : MulAction.stabilizer G v => (z : G)) h))
  let U : Sylow 2 L := S.mapSurjective hN.phi_surjective
  let t : L := hN.phi g
  have hker_le_S : MonoidHom.ker hN.phi ≤ (S : Subgroup N) := by
    have h := hN.pCoreOf_subgroupOf_le_sylow S
    have hker : MonoidHom.ker hN.phi = (pCoreOf 2 (MulAction.stabilizer G v)).subgroupOf N := by
      ext y
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact hN.phi_ker y
    rwa [hker]
  have hUcomap : (U : Subgroup L).comap hN.phi = (S : Subgroup N) := by
    rw [show (U : Subgroup L) = (S : Subgroup N).map hN.phi from rfl]
    exact Subgroup.comap_map_eq_self (f := hN.phi) hker_le_S
  have hpre : (Subgroup.normalizer ((U : Subgroup L) : Set L)).comap hN.phi =
      Subgroup.normalizer ((S : Subgroup N) : Set N) := by
    rw [Subgroup.comap_normalizer_eq_of_surjective
      (H := (U : Subgroup L)) (f := hN.phi) hN.phi_surjective]
    rw [hUcomap]
  have ht_not : t ∉ Subgroup.normalizer ((U : Subgroup L) : Set L) := by
    intro ht
    apply hg
    have hgcomap : g ∈ (Subgroup.normalizer ((U : Subgroup L) : Set L)).comap hN.phi := ht
    rwa [hpre] at hgcomap
  let tU : Sylow 2 L := t • U
  have htU_ne : U ≠ tU := by
    intro h
    apply ht_not
    have : t • U = U := h.symm
    exact (Sylow.smul_eq_iff_mem_normalizer).mp this
  have hsupU : (U : Subgroup L) ⊔ (tU : Subgroup L) = ⊤ :=
    psl2_sylow_two_sup_eq_top hn htU_ne
  have htU_coe : (tU : Subgroup L) = (U : Subgroup L).map (MulAut.conj t).toMonoidHom := by
    dsimp [tU]
    rw [Sylow.coe_subgroup_smul]
    rfl
  have htU_le : (tU : Subgroup L) ≤ (U : Subgroup L) ⊔ Subgroup.zpowers t := by
    rw [htU_coe]
    intro y hy
    obtain ⟨u, huU, rfl⟩ := Subgroup.mem_map.mp hy
    have hu : u ∈ (U : Subgroup L) ⊔ Subgroup.zpowers t := Subgroup.mem_sup_left huU
    have htmem : t ∈ (U : Subgroup L) ⊔ Subgroup.zpowers t :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    have htinv : t⁻¹ ∈ (U : Subgroup L) ⊔ Subgroup.zpowers t :=
      Subgroup.inv_mem _ htmem
    simpa [mul_assoc] using
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ htmem hu) htinv)
  have hU_top : (U : Subgroup L) ⊔ Subgroup.zpowers t = ⊤ := by
    apply top_unique
    rw [← hsupU]
    exact sup_le le_sup_left htU_le
  have hmap : ((S : Subgroup N) ⊔ Subgroup.zpowers g).map hN.phi =
      (U : Subgroup L) ⊔ Subgroup.zpowers t := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  have hmap_top : ((S : Subgroup N) ⊔ Subgroup.zpowers g).map hN.phi = ⊤ := by
    rw [hmap, hU_top]
  apply top_unique
  intro y hy
  have hy_map : hN.phi y ∈ ((S : Subgroup N) ⊔ Subgroup.zpowers g).map hN.phi := by
    rw [hmap_top]
    exact Subgroup.mem_top _
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy_map
  have hker : y * z⁻¹ ∈ MonoidHom.ker hN.phi := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hzy, mul_inv_cancel]
  have hkerH : y * z⁻¹ ∈ (S : Subgroup N) ⊔ Subgroup.zpowers g :=
    (show (S : Subgroup N) ≤ (S : Subgroup N) ⊔ Subgroup.zpowers g from le_sup_left)
      (hker_le_S hker)
  have hyz : y = (y * z⁻¹) * z := by group
  rw [hyz]
  exact Subgroup.mul_mem _ hkerH hz

private theorem torus_transitive_on_sylow_of_ne_bot (hN : IsLocL2 Γ G v n N)
    (hadj : ∀ (g : G) (u w : V), Γ.Adj (g • u) (g • w) ↔ Γ.Adj u w)
    (hfin : Finite (MulAction.stabilizer G v))
    (hcard : Nat.card (Γ.neighborSet v) = 2 ^ n + 1) (hn : 1 ≤ n)
    (S : Sylow 2 N) (K : Subgroup N)
    (hKS : K ⊓ (S : Subgroup N) = ⊥)
    (hsup : K ⊔ (S : Subgroup N) =
      Subgroup.normalizer ((S : Subgroup N) : Set N))
    (hKne : K ≠ ⊥) {x y : N}
    (hxS : x ∈ (S : Subgroup N)) (hyS : y ∈ (S : Subgroup N))
    (hxQ : (x : G) ∉ pCoreOf 2 (MulAction.stabilizer G v))
    (hyQ : (y : G) ∉ pCoreOf 2 (MulAction.stabilizer G v)) :
    ∃ k : K, (k : N) * x * (k : N)⁻¹ * y⁻¹ ∈
      (pCoreOf 2 (MulAction.stabilizer G v)).subgroupOf N := by
  classical
  let L := PSL(2, GaloisField 2 n)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite N :=
    Finite.of_injective
      (fun x : N => (⟨(x : G), hN.le x.2⟩ : MulAction.stabilizer G v))
      (fun a b h => Subtype.ext
        (congrArg (fun z : MulAction.stabilizer G v => (z : G)) h))
  let U : Sylow 2 L := S.mapSurjective hN.phi_surjective
  let D : Subgroup L := K.map hN.phi
  have hker_le_S : MonoidHom.ker hN.phi ≤ (S : Subgroup N) := by
    have h := hN.pCoreOf_subgroupOf_le_sylow S
    have hker : MonoidHom.ker hN.phi = (pCoreOf 2 (MulAction.stabilizer G v)).subgroupOf N := by
      ext y
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact hN.phi_ker y
    rwa [hker]
  have hDinf : D ⊓ (U : Subgroup L) = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyD, hyU⟩
    obtain ⟨k, hkK, rfl⟩ := Subgroup.mem_map.mp hyD
    have hkU : hN.phi k ∈ (U : Subgroup L) := hyU
    rw [show (U : Subgroup L) = (S : Subgroup N).map hN.phi from rfl] at hkU
    obtain ⟨s, hsS, hsk⟩ := Subgroup.mem_map.mp hkU
    have hker : s⁻¹ * k ∈ MonoidHom.ker hN.phi := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hsk, inv_mul_cancel]
    have hkerS : s⁻¹ * k ∈ (S : Subgroup N) := hker_le_S hker
    have hkS : k ∈ (S : Subgroup N) := by
      have : k = s * (s⁻¹ * k) := by group
      rw [this]
      exact (S : Subgroup N).mul_mem hsS hkerS
    have hkbot : k ∈ (⊥ : Subgroup N) := by
      rw [← hKS]
      exact ⟨hkK, hkS⟩
    rw [Subgroup.mem_bot] at hkbot
    simp [hkbot]
  have hDsup : D ⊔ (U : Subgroup L) =
      Subgroup.normalizer ((U : Subgroup L) : Set L) := by
    have hUcomap : (U : Subgroup L).comap hN.phi = (S : Subgroup N) := by
      rw [show (U : Subgroup L) = (S : Subgroup N).map hN.phi from rfl]
      exact Subgroup.comap_map_eq_self (f := hN.phi) hker_le_S
    have hcomap : (Subgroup.normalizer ((U : Subgroup L) : Set L)).comap hN.phi =
        Subgroup.normalizer ((S : Subgroup N) : Set N) := by
      rw [Subgroup.comap_normalizer_eq_of_surjective
        (H := (U : Subgroup L)) (f := hN.phi) hN.phi_surjective]
      rw [hUcomap]
    have hmapnorm : (Subgroup.normalizer ((S : Subgroup N) : Set N)).map hN.phi =
        Subgroup.normalizer ((U : Subgroup L) : Set L) := by
      rw [← hcomap]
      exact Subgroup.map_comap_eq_self_of_surjective hN.phi_surjective _
    calc
      D ⊔ (U : Subgroup L) = (K ⊔ (S : Subgroup N)).map hN.phi := by
        simp [D, U, Subgroup.map_sup]
      _ = (Subgroup.normalizer ((S : Subgroup N) : Set N)).map hN.phi := by rw [hsup]
      _ = _ := hmapnorm
  have hKcard := (hN.torus_cyclic_of_ne_bot hadj hfin hcard hn S K hKS hsup hKne).2
  have hn2 : 2 ≤ n := by
    by_contra h
    have hn1 : n = 1 := by omega
    have hcard1 : Nat.card K = 1 := by
      rw [hKcard, hn1]
      norm_num
    exact hKne (Subgroup.eq_bot_of_card_eq K hcard1)
  have hreg := psl2_torus_regular_on_sylow hn2 hDinf hDsup
  have hxU : hN.phi x ∈ (U : Subgroup L) := by
    rw [show (U : Subgroup L) = (S : Subgroup N).map hN.phi from rfl]
    exact Subgroup.mem_map_of_mem hN.phi hxS
  have hyU : hN.phi y ∈ (U : Subgroup L) := by
    rw [show (U : Subgroup L) = (S : Subgroup N).map hN.phi from rfl]
    exact Subgroup.mem_map_of_mem hN.phi hyS
  have hx1 : hN.phi x ≠ 1 := fun h => hxQ ((hN.phi_ker x).mp h)
  have hy1 : hN.phi y ≠ 1 := fun h => hyQ ((hN.phi_ker y).mp h)
  obtain ⟨d, hdD, hduv⟩ := hreg (hN.phi x) hxU hx1 (hN.phi y) hyU hy1
  obtain ⟨k, hkK, hkd⟩ := Subgroup.mem_map.mp hdD
  refine ⟨⟨k, hkK⟩, ?_⟩
  have hker : k * x * k⁻¹ * y⁻¹ ∈ MonoidHom.ker hN.phi := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hkd, hduv, mul_inv_cancel]
  have hker_eq : MonoidHom.ker hN.phi =
      (pCoreOf 2 (MulAction.stabilizer G v)).subgroupOf N := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hN.phi_ker y
  rwa [hker_eq] at hker

theorem torus_map_inf (hN : IsLocL2 Γ G v n N) [Finite N]
    (hfin : Finite (MulAction.stabilizer G v))
    (S : Sylow 2 N) (K : Subgroup N)
    (hKS : K ⊓ (S : Subgroup N) = ⊥) :
    (K.map hN.phi) ⊓
      ((S.mapSurjective (p := 2) hN.phi_surjective : Sylow 2
        (PSL(2, GaloisField 2 n))) : Subgroup (PSL(2, GaloisField 2 n))) = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite N :=
    Finite.of_injective
      (fun x : N => (⟨(x : G), hN.le x.2⟩ : MulAction.stabilizer G v))
      (fun a b h => Subtype.ext
        (congrArg (fun z : MulAction.stabilizer G v => (z : G)) h))
  have hker_le_S : MonoidHom.ker hN.phi ≤ (S : Subgroup N) :=
    (by
      have h := hN.pCoreOf_subgroupOf_le_sylow S
      have hker : MonoidHom.ker hN.phi =
          (pCoreOf 2 (MulAction.stabilizer G v)).subgroupOf N := by
        ext y
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
        exact hN.phi_ker y
      rwa [hker])
  rw [eq_bot_iff]
  rintro y ⟨hyD, hyU⟩
  obtain ⟨k, hkK, rfl⟩ := Subgroup.mem_map.mp hyD
  have hkU : hN.phi k ∈
      ((S.mapSurjective (p := 2) hN.phi_surjective : Sylow 2
        (PSL(2, GaloisField 2 n))) : Subgroup (PSL(2, GaloisField 2 n))) := hyU
  rw [show ((S.mapSurjective (p := 2) hN.phi_surjective : Sylow 2
        (PSL(2, GaloisField 2 n))) : Subgroup (PSL(2, GaloisField 2 n))) =
      (S : Subgroup N).map hN.phi from rfl] at hkU
  obtain ⟨s, hsS, hsk⟩ := Subgroup.mem_map.mp hkU
  have hker : s⁻¹ * k ∈ MonoidHom.ker hN.phi := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hsk, inv_mul_cancel]
  have hkerS : s⁻¹ * k ∈ (S : Subgroup N) := hker_le_S hker
  have hkS : k ∈ (S : Subgroup N) := by
    have : k = s * (s⁻¹ * k) := by group
    rw [this]
    exact (S : Subgroup N).mul_mem hsS hkerS
  have hkbot : k ∈ (⊥ : Subgroup N) := by
    rw [← hKS]
    exact ⟨hkK, hkS⟩
  rw [Subgroup.mem_bot] at hkbot
  simp [hkbot]

theorem torus_map_sup (hN : IsLocL2 Γ G v n N) [Finite N]
    (hfin : Finite (MulAction.stabilizer G v))
    (S : Sylow 2 N) (K : Subgroup N)
    (hsup : K ⊔ (S : Subgroup N) =
      Subgroup.normalizer ((S : Subgroup N) : Set N)) :
    (K.map hN.phi) ⊔
      ((S.mapSurjective (p := 2) hN.phi_surjective : Sylow 2
        (PSL(2, GaloisField 2 n))) : Subgroup (PSL(2, GaloisField 2 n))) =
      Subgroup.normalizer
        (((S.mapSurjective (p := 2) hN.phi_surjective : Sylow 2
          (PSL(2, GaloisField 2 n))) : Subgroup (PSL(2, GaloisField 2 n))) : Set
            (PSL(2, GaloisField 2 n))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite N :=
    Finite.of_injective
      (fun x : N => (⟨(x : G), hN.le x.2⟩ : MulAction.stabilizer G v))
      (fun a b h => Subtype.ext
        (congrArg (fun z : MulAction.stabilizer G v => (z : G)) h))
  have hker_le_S : MonoidHom.ker hN.phi ≤ (S : Subgroup N) :=
    (by
      have h := hN.pCoreOf_subgroupOf_le_sylow S
      have hker : MonoidHom.ker hN.phi =
          (pCoreOf 2 (MulAction.stabilizer G v)).subgroupOf N := by
        ext y
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
        exact hN.phi_ker y
      rwa [hker])
  let U : Sylow 2 (PSL(2, GaloisField 2 n)) :=
    S.mapSurjective (p := 2) hN.phi_surjective
  have hUcomap : (U : Subgroup (PSL(2, GaloisField 2 n))).comap hN.phi =
      (S : Subgroup N) := by
    rw [show (U : Subgroup (PSL(2, GaloisField 2 n))) =
        (S : Subgroup N).map hN.phi from rfl]
    exact Subgroup.comap_map_eq_self (f := hN.phi) hker_le_S
  have hcomap : (Subgroup.normalizer
        ((U : Subgroup (PSL(2, GaloisField 2 n))) : Set
          (PSL(2, GaloisField 2 n)))).comap hN.phi =
      Subgroup.normalizer ((S : Subgroup N) : Set N) := by
    rw [Subgroup.comap_normalizer_eq_of_surjective
      (H := (U : Subgroup (PSL(2, GaloisField 2 n)))) (f := hN.phi)
      hN.phi_surjective]
    rw [hUcomap]
  have hmapnorm : (Subgroup.normalizer ((S : Subgroup N) : Set N)).map hN.phi =
      Subgroup.normalizer ((U : Subgroup (PSL(2, GaloisField 2 n))) : Set
        (PSL(2, GaloisField 2 n))) := by
    rw [← hcomap]
    exact Subgroup.map_comap_eq_self_of_surjective hN.phi_surjective _
  calc
    (K.map hN.phi) ⊔ (U : Subgroup (PSL(2, GaloisField 2 n))) =
        (K ⊔ (S : Subgroup N)).map hN.phi := by
      simp [U, Subgroup.map_sup]
    _ = (Subgroup.normalizer ((S : Subgroup N) : Set N)).map hN.phi := by rw [hsup]
    _ = _ := hmapnorm

private theorem torus_fixes_two_of_ne_bot (hN : IsLocL2 Γ G v n N)
    (hadj : ∀ (g : G) (u w : V), Γ.Adj (g • u) (g • w) ↔ Γ.Adj u w)
    (hfin : Finite (MulAction.stabilizer G v))
    (hcard : Nat.card (Γ.neighborSet v) = 2 ^ n + 1) (hn : 1 ≤ n)
    (S : Sylow 2 N) (K : Subgroup N)
    (hKS : K ⊓ (S : Subgroup N) = ⊥)
    (hsup : K ⊔ (S : Subgroup N) =
      Subgroup.normalizer ((S : Subgroup N) : Set N))
    (hKne : K ≠ ⊥) {k : K} (hk : k ≠ 1) :
    Set.ncard {a : V | Γ.Adj v a ∧ ((k : N) : G) • a = a} = 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite N :=
    Finite.of_injective
      (fun x : N => (⟨(x : G), hN.le x.2⟩ : MulAction.stabilizer G v))
      (fun a b h => Subtype.ext
        (congrArg (fun z : MulAction.stabilizer G v => (z : G)) h))
  let L := PSL(2, GaloisField 2 n)
  let U : Sylow 2 L := S.mapSurjective (p := 2) hN.phi_surjective
  let D : Subgroup L := K.map hN.phi
  have hDinf : D ⊓ (U : Subgroup L) = ⊥ := hN.torus_map_inf hfin (S := S) (K := K) hKS
  have hDsup : D ⊔ (U : Subgroup L) = Subgroup.normalizer ((U : Subgroup L) : Set L) :=
    hN.torus_map_sup hfin (S := S) (K := K) hsup
  have hKcard := (hN.torus_cyclic_of_ne_bot hadj hfin hcard hn S K hKS hsup hKne).2
  have hn2 : 2 ≤ n := by
    by_contra h
    have hn1 : n = 1 := by omega
    have hcard1 : Nat.card K = 1 := by
      rw [hKcard, hn1]
      norm_num
    exact hKne (Subgroup.eq_bot_of_card_eq K hcard1)
  obtain ⟨W, hWU, hWle, hWiff⟩ := psl2_torus_fixed_sylow hn2 hDinf hDsup
  have hbij := hN.pointSylow_bijective hadj hfin hcard hn
  obtain ⟨aU, haU⟩ := hbij.2 U
  obtain ⟨aV, haV⟩ := hbij.2 W
  have hUV : aU ≠ aV := by
    intro h
    apply hWU
    rw [← haU, ← haV, h]
  let d : D := ⟨hN.phi (k : N), Subgroup.mem_map_of_mem hN.phi k.2⟩
  have hd1 : d ≠ 1 := by
    intro hd
    have hφk : hN.phi (k : N) = 1 := congrArg Subtype.val hd
    have hkker : (k : N) ∈ MonoidHom.ker hN.phi := by
      simpa [MonoidHom.mem_ker] using hφk
    have hker_le_S : MonoidHom.ker hN.phi ≤ (S : Subgroup N) := by
      have h := hN.pCoreOf_subgroupOf_le_sylow S
      have hker : MonoidHom.ker hN.phi =
          (pCoreOf 2 (MulAction.stabilizer G v)).subgroupOf N := by
        ext y
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
        exact hN.phi_ker y
      rwa [hker]
    have hkS : (k : N) ∈ (S : Subgroup N) := hker_le_S hkker
    have hkbot : (k : N) ∈ (⊥ : Subgroup N) := by
      rw [← hKS]
      exact ⟨k.2, hkS⟩
    rw [Subgroup.mem_bot] at hkbot
    exact hk (Subtype.ext hkbot)
  have hdleU : D ≤ Subgroup.normalizer ((U : Subgroup L) : Set L) := by
    rw [← hDsup]
    exact le_sup_left
  have hfixU : ((k : N) : G) • aU.1 = aU.1 := by
    have hdNU : (d : L) ∈ Subgroup.normalizer ((U : Subgroup L) : Set L) := hdleU d.2
    have hkcomap : (k : N) ∈ (hN.pointBorel aU.1).comap hN.phi := by
      rw [pointBorel_eq_normalizer hN hadj hfin hcard hn aU.2]
      simpa [haU] using hdNU
    have hkpoint : (k : N) ∈ hN.pointSubgroup aU.1 := by
      rwa [← pointSubgroup_eq_comap_pointBorel hN hadj hfin hcard hn aU.2] at hkcomap
    have hkstab : (k : N) ∈ MulAction.stabilizer N aU := by
      rwa [← pointSubgroup_eq_stabilizer hN hadj aU.2]
    exact congrArg (fun z : (hN.neighborAction hadj) => (z : V))
      (MulAction.mem_stabilizer_iff.mp hkstab)
  have hfixV : ((k : N) : G) • aV.1 = aV.1 := by
    have hdNV : (d : L) ∈ Subgroup.normalizer ((W : Subgroup L) : Set L) := hWle d.2
    have hkcomap : (k : N) ∈ (hN.pointBorel aV.1).comap hN.phi := by
      rw [pointBorel_eq_normalizer hN hadj hfin hcard hn aV.2]
      simpa [haV] using hdNV
    have hkpoint : (k : N) ∈ hN.pointSubgroup aV.1 := by
      rwa [← pointSubgroup_eq_comap_pointBorel hN hadj hfin hcard hn aV.2] at hkcomap
    have hkstab : (k : N) ∈ MulAction.stabilizer N aV := by
      rwa [← pointSubgroup_eq_stabilizer hN hadj aV.2]
    exact congrArg (fun z : (hN.neighborAction hadj) => (z : V))
      (MulAction.mem_stabilizer_iff.mp hkstab)
  have hset : {a : V | Γ.Adj v a ∧ ((k : N) : G) • a = a} = {aU.1, aV.1} := by
    ext b
    constructor
    · intro hb
      have hbAdj : Γ.Adj v b := hb.1
      have hbk : ((k : N) : G) • b = b := hb.2
      have hbpoint : (k : N) ∈ hN.pointSubgroup b := by
        rw [pointSubgroup_eq_stabilizer hN hadj hbAdj]
        exact MulAction.mem_stabilizer_iff.mpr (by
          apply Subtype.ext
          rw [SubMulAction.val_smul, MulAction.subgroup_smul_def]
          exact hbk)
      have hdB : hN.phi (k : N) ∈ hN.pointBorel b := by
        have hkcomap : (k : N) ∈ (hN.pointBorel b).comap hN.phi := by
          rwa [← pointSubgroup_eq_comap_pointBorel hN hadj hfin hcard hn hbAdj]
        exact hkcomap
      have hdN : (d : L) ∈ Subgroup.normalizer
          ((hN.pointSylow hadj hfin hcard hn b : Sylow 2 L) : Set L) := by
        rw [← pointBorel_eq_normalizer hN hadj hfin hcard hn hbAdj]
        exact hdB
      have hbor := (hWiff d hd1 (hN.pointSylow hadj hfin hcard hn b)).mp hdN
      rcases hbor with h | h
      · left
        have : (⟨b, hbAdj⟩ : (hN.neighborAction hadj)) = aU :=
          hbij.1 (h.trans haU.symm)
        exact congrArg Subtype.val this
      · right
        have : (⟨b, hbAdj⟩ : (hN.neighborAction hadj)) = aV :=
          hbij.1 (h.trans haV.symm)
        exact congrArg Subtype.val this
    · intro hb
      rcases hb with h | h
      · rw [h]
        exact ⟨aU.2, hfixU⟩
      · rw [h]
        exact ⟨aV.2, hfixV⟩
  rw [hset, Set.ncard_pair]
  exact fun h => hUV (Subtype.ext h)

theorem torus_centralizer (hN : IsLocL2 Γ G v n N)
    (hadj : ∀ (g : G) (u w : V), Γ.Adj (g • u) (g • w) ↔ Γ.Adj u w)
    (hfin : Finite (MulAction.stabilizer G v))
    (hcard : Nat.card (Γ.neighborSet v) = 2 ^ n + 1) (hn : 1 ≤ n)
    (S : Sylow 2 N) (K : Subgroup N)
    (hKS : K ⊓ (S : Subgroup N) = ⊥)
    (hsup : K ⊔ (S : Subgroup N) =
      Subgroup.normalizer ((S : Subgroup N) : Set N))
    (hKne : K ≠ ⊥) :
    Subgroup.centralizer (K : Set N) ≤
      K ⊔ (pCoreOf 2 (MulAction.stabilizer G v)).subgroupOf N := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite N :=
    Finite.of_injective
      (fun x : N => (⟨(x : G), hN.le x.2⟩ : MulAction.stabilizer G v))
      (fun a b h => Subtype.ext
        (congrArg (fun z : MulAction.stabilizer G v => (z : G)) h))
  let L := PSL(2, GaloisField 2 n)
  let U : Sylow 2 L := S.mapSurjective (p := 2) hN.phi_surjective
  let D : Subgroup L := K.map hN.phi
  have hDinf : D ⊓ (U : Subgroup L) = ⊥ := hN.torus_map_inf hfin (S := S) (K := K) hKS
  have hDsup : D ⊔ (U : Subgroup L) = Subgroup.normalizer ((U : Subgroup L) : Set L) :=
    hN.torus_map_sup hfin (S := S) (K := K) hsup
  have hKcard := (hN.torus_cyclic_of_ne_bot hadj hfin hcard hn S K hKS hsup hKne).2
  have hn2 : 2 ≤ n := by
    by_contra h
    have hn1 : n = 1 := by omega
    have hcard1 : Nat.card K = 1 := by
      rw [hKcard, hn1]
      norm_num
    exact hKne (Subgroup.eq_bot_of_card_eq K hcard1)
  have hcent := psl2_torus_centralizer hn2 hDinf hDsup
  intro x hx
  have hxcentD : hN.phi x ∈ Subgroup.centralizer (D : Set L) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    obtain ⟨k, hkK, hkd⟩ := Subgroup.mem_map.mp hd
    have hkx : (k : N) * x = x * (k : N) :=
      (Subgroup.mem_centralizer_iff.mp hx) k hkK
    rw [← hkd]
    simpa [map_mul] using congrArg hN.phi hkx
  rw [hcent] at hxcentD
  obtain ⟨k, hkK, hkd⟩ := Subgroup.mem_map.mp hxcentD
  have hker : x * (k : N)⁻¹ ∈ MonoidHom.ker hN.phi := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hkd, mul_inv_cancel]
  have hker_eq : MonoidHom.ker hN.phi =
      (pCoreOf 2 (MulAction.stabilizer G v)).subgroupOf N := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hN.phi_ker y
  have hkerQ : x * (k : N)⁻¹ ∈
      (pCoreOf 2 (MulAction.stabilizer G v)).subgroupOf N := by
    rwa [← hker_eq]
  have hxKQ : x ∈ (pCoreOf 2 (MulAction.stabilizer G v)).subgroupOf N ⊔ K := by
    have hx' : x = (x * (k : N)⁻¹) * k := by group
    rw [hx']
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left hkerQ) (Subgroup.mem_sup_right hkK)
  rwa [sup_comm] at hxKQ

theorem inf_stabilizer_eq_inf_normalizer_pointSylowN (hN : IsLocL2 Γ G v n N)
    (hadj : ∀ (g : G) (u w : V), Γ.Adj (g • u) (g • w) ↔ Γ.Adj u w)
    (hfin : Finite (MulAction.stabilizer G v))
    (hcard : Nat.card (Γ.neighborSet v) = 2 ^ n + 1) (hn : 1 ≤ n)
    {a : V} (ha : Γ.Adj v a) :
    N ⊓ MulAction.stabilizer G a =
      N ⊓ Subgroup.normalizer
        ((Subgroup.map N.subtype
          ((hN.pointSylowN hadj hfin hcard hn a : Sylow 2 N) : Subgroup N) :
            Subgroup G) : Set G) := by
  classical
  let S : Subgroup N := (hN.pointSylowN hadj hfin hcard hn a : Sylow 2 N)
  let Sg : Subgroup G := S.map N.subtype
  have hSgle : Sg ≤ N := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  have hSgsub : Sg.subgroupOf N = S := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      have : y = x := Subtype.ext hyx
      simpa [this] using hy
    · intro hx
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_map_of_mem N.subtype hx
  have hnorm : (Subgroup.normalizer (Sg : Set G)).subgroupOf N =
      Subgroup.normalizer (S : Set N) := by
    rw [Subgroup.subgroupOf_normalizer_eq (H := Sg) (N := N) hSgle, hSgsub]
  ext x
  constructor
  · rintro ⟨hxN, hxa⟩
    refine ⟨hxN, ?_⟩
    have hxpoint : (⟨x, hxN⟩ : N) ∈ hN.pointSubgroup a := by
      rw [pointSubgroup_eq_stabilizer hN hadj ha]
      exact MulAction.mem_stabilizer_iff.mpr (by
        apply Subtype.ext
        rw [SubMulAction.val_smul, MulAction.subgroup_smul_def]
        exact hxa)
    have hxnormS : (⟨x, hxN⟩ : N) ∈ Subgroup.normalizer (S : Set N) := by
      rwa [← pointSubgroup_eq_normalizer_pointSylowN hN hadj hfin hcard hn ha]
    have hxsub : (⟨x, hxN⟩ : N) ∈ (Subgroup.normalizer (Sg : Set G)).subgroupOf N := by
      rwa [hnorm]
    exact Subgroup.mem_subgroupOf.mp hxsub
  · rintro ⟨hxN, hxnormG⟩
    refine ⟨hxN, ?_⟩
    have hxsub : (⟨x, hxN⟩ : N) ∈ (Subgroup.normalizer (Sg : Set G)).subgroupOf N :=
      Subgroup.mem_subgroupOf.mpr hxnormG
    have hxnormS : (⟨x, hxN⟩ : N) ∈ Subgroup.normalizer (S : Set N) := by
      rwa [hnorm] at hxsub
    have hxpoint : (⟨x, hxN⟩ : N) ∈ hN.pointSubgroup a := by
      rwa [pointSubgroup_eq_normalizer_pointSylowN hN hadj hfin hcard hn ha]
    have hxstab : (⟨x, hxN⟩ : N) ∈ MulAction.stabilizer N
        (⟨a, by
          show a ∈ (hN.neighborAction hadj).carrier
          rw [show a ∈ (hN.neighborAction hadj).carrier ↔ Γ.Adj v a from
            SimpleGraph.mem_neighborSet (G := Γ) v a]
          exact ha⟩ : hN.neighborAction hadj) := by
      rwa [← pointSubgroup_eq_stabilizer hN hadj ha]
    exact congrArg (fun z : hN.neighborAction hadj => (z : V))
      (MulAction.mem_stabilizer_iff.mp hxstab)

theorem torus_fixes_two (hN : IsLocL2 Γ G v n N)
    (hadj : ∀ (g : G) (u w : V), Γ.Adj (g • u) (g • w) ↔ Γ.Adj u w)
    (hfin : Finite (MulAction.stabilizer G v))
    (hcard : Nat.card (Γ.neighborSet v) = 2 ^ n + 1) (hn : 1 ≤ n)
    (S : Sylow 2 N) (K : Subgroup N)
    (hKS : K ⊓ (S : Subgroup N) = ⊥)
    (hsup : K ⊔ (S : Subgroup N) =
      Subgroup.normalizer ((S : Subgroup N) : Set N)) :
    ∀ k : K, k ≠ 1 →
      Set.ncard {a : V | Γ.Adj v a ∧ ((k : N) : G) • a = a} = 2 := by
  by_cases hKne : K = ⊥
  · subst K
    intro k hk
    exact absurd (Subsingleton.elim k 1) hk
  · exact fun k hk => hN.torus_fixes_two_of_ne_bot hadj hfin hcard hn S K hKS hsup hKne hk


theorem torus_transitive_on_sylow (hN : IsLocL2 Γ G v n N)
    (hadj : ∀ (g : G) (u w : V), Γ.Adj (g • u) (g • w) ↔ Γ.Adj u w)
    (hfin : Finite (MulAction.stabilizer G v))
    (hcard : Nat.card (Γ.neighborSet v) = 2 ^ n + 1) (hn : 1 ≤ n)
    (S : Sylow 2 N) (K : Subgroup N)
    (hKS : K ⊓ (S : Subgroup N) = ⊥)
    (hsup : K ⊔ (S : Subgroup N) =
      Subgroup.normalizer ((S : Subgroup N) : Set N))
    {x y : N} (hxS : x ∈ (S : Subgroup N)) (hyS : y ∈ (S : Subgroup N))
    (hxQ : (x : G) ∉ pCoreOf 2 (MulAction.stabilizer G v))
    (hyQ : (y : G) ∉ pCoreOf 2 (MulAction.stabilizer G v)) :
    ∃ k : K, (k : N) * x * (k : N)⁻¹ * y⁻¹ ∈
      (pCoreOf 2 (MulAction.stabilizer G v)).subgroupOf N := by
  by_cases hKne : K = ⊥
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Finite N :=
      Finite.of_injective
        (fun x : N => (⟨(x : G), hN.le x.2⟩ : MulAction.stabilizer G v))
        (fun a b h => Subtype.ext
          (congrArg (fun z : MulAction.stabilizer G v => (z : G)) h))
    let L := PSL(2, GaloisField 2 n)
    let U : Sylow 2 L := S.mapSurjective (p := 2) hN.phi_surjective
    let D : Subgroup L := K.map hN.phi
    have hDinf : D ⊓ (U : Subgroup L) = ⊥ := hN.torus_map_inf hfin (S := S) (K := K) hKS
    have hDsup : D ⊔ (U : Subgroup L) = Subgroup.normalizer ((U : Subgroup L) : Set L) :=
      hN.torus_map_sup hfin (S := S) (K := K) hsup
    have hDcard : Nat.card D = 2 ^ n - 1 := psl2_torus_card hn hDinf hDsup
    have hDbot : D = ⊥ := by
      dsimp [D]
      rw [hKne]
      simp
    have hD1 : Nat.card D = 1 := by rw [hDbot]; simp
    rw [hD1] at hDcard
    have hpowle : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have hpow2 : 2 ^ n = 2 := by omega
    have hn1 : n = 1 := by
      by_contra h
      have h2 : 2 ≤ n := by omega
      have h4 : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2
      omega
    let f : (S : Subgroup N) →* L := hN.phi.comp (S : Subgroup N).subtype
    let QNS : Subgroup (S : Subgroup N) := MonoidHom.ker f
    have hQNSnormal : QNS.Normal := inferInstance
    haveI : QNS.Normal := hQNSnormal
    have hQNS : QNS = ((pCoreOf 2 (MulAction.stabilizer G v)).subgroupOf N).subgroupOf
        (S : Subgroup N) := by
      ext z
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact hN.phi_ker (z : N)
    have hqcard : Nat.card ((S : Subgroup N) ⧸ QNS) = 2 := by
      have e := QuotientGroup.quotientKerEquivRange f
      have hcardrange : Nat.card ((S : Subgroup N) ⧸ QNS) = Nat.card f.range :=
        Nat.card_congr e.toEquiv
      rw [hcardrange]
      have hrange : f.range = (U : Subgroup L) := by
        rw [show (U : Subgroup L) = (S : Subgroup N).map hN.phi from rfl]
        change (hN.phi.comp (S : Subgroup N).subtype).range =
          (S : Subgroup N).map hN.phi
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rw [hrange]
      have := psl2_sylow_two_card hn U
      have h2 : (2 : ℕ) ^ n = 2 := by rw [hn1]; norm_num
      rwa [h2] at this
    let xS : (S : Subgroup N) := ⟨x, hxS⟩
    let yS : (S : Subgroup N) := ⟨y, hyS⟩
    have hxq : (QuotientGroup.mk xS : (S : Subgroup N) ⧸ QNS) ≠ 1 := by
      intro h
      apply hxQ
      have hxQNS : xS ∈ QNS := (QuotientGroup.eq_one_iff (N := QNS) xS).mp h
      rw [hQNS] at hxQNS
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hxQNS
      simpa [xS] using hxQNS
    have hyq : (QuotientGroup.mk yS : (S : Subgroup N) ⧸ QNS) ≠ 1 := by
      intro h
      apply hyQ
      have hyQNS : yS ∈ QNS := (QuotientGroup.eq_one_iff (N := QNS) yS).mp h
      rw [hQNS] at hyQNS
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hyQNS
      simpa [yS] using hyQNS
    have hxyq : (QuotientGroup.mk xS : (S : Subgroup N) ⧸ QNS) = QuotientGroup.mk yS :=
      eq_of_ne_one_of_card_eq_two hqcard hxq hyq
    have hdiv : xS / yS ∈ QNS := (QuotientGroup.eq_iff_div_mem.mp hxyq)
    rw [hQNS, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hdiv
    refine ⟨1, ?_⟩
    rw [Subgroup.mem_subgroupOf]
    simpa [xS, yS, div_eq_mul_inv] using hdiv
  · exact hN.torus_transitive_on_sylow_of_ne_bot hadj hfin hcard hn S K hKS hsup hKne hxS hyS
      hxQ hyQ

theorem sylow_sup_zpowers_eq_G (hN : IsLocL2 Γ G v n N)
    (hadj : ∀ (g : G) (u w : V), Γ.Adj (g • u) (g • w) ↔ Γ.Adj u w)
    (hfin : Finite (MulAction.stabilizer G v))
    (hcard : Nat.card (Γ.neighborSet v) = 2 ^ n + 1) (hn : 1 ≤ n)
    (S : Sylow 2 N) {g : G} (hgN : g ∈ N)
    (hg : g ∉ Subgroup.normalizer
      (((S : Subgroup N).map N.subtype : Subgroup G) : Set G)) :
    (S : Subgroup N).map N.subtype ⊔ Subgroup.zpowers g = N := by
  classical
  let gN : N := ⟨g, hgN⟩
  let Sg : Subgroup G := (S : Subgroup N).map N.subtype
  have hSgle : Sg ≤ N := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  have hSgsub : Sg.subgroupOf N = (S : Subgroup N) := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      have : y = x := Subtype.ext hyx
      simpa [this] using hy
    · intro hx
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_map_of_mem N.subtype hx
  have hnorm : (Subgroup.normalizer (Sg : Set G)).subgroupOf N =
      Subgroup.normalizer ((S : Subgroup N) : Set N) := by
    rw [Subgroup.subgroupOf_normalizer_eq (H := Sg) (N := N) hSgle, hSgsub]
  have hgN_norm : gN ∉ Subgroup.normalizer ((S : Subgroup N) : Set N) := by
    intro h
    apply hg
    have hgsub : gN ∈ (Subgroup.normalizer (Sg : Set G)).subgroupOf N := by
      rw [hnorm]
      exact h
    have hgnorm : (gN : G) ∈ Subgroup.normalizer (Sg : Set G) :=
      Subgroup.mem_subgroupOf.mp hgsub
    simpa [gN, Sg] using hgnorm
  have hsup := hN.sylow_sup_zpowers_eq hadj hfin hcard hn S (g := gN) hgN_norm
  have hmap := congrArg (Subgroup.map N.subtype) hsup
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.map_top,
    Subgroup.range_subtype] at hmap
  simpa [Sg] using hmap

theorem torus_cyclic (hN : IsLocL2 Γ G v n N)
    (hadj : ∀ (g : G) (u w : V), Γ.Adj (g • u) (g • w) ↔ Γ.Adj u w)
    (hfin : Finite (MulAction.stabilizer G v))
    (hcard : Nat.card (Γ.neighborSet v) = 2 ^ n + 1) (hn : 1 ≤ n)
    (S : Sylow 2 N) (K : Subgroup N)
    (hKS : K ⊓ (S : Subgroup N) = ⊥)
    (hsup : K ⊔ (S : Subgroup N) =
      Subgroup.normalizer ((S : Subgroup N) : Set N)) :
    IsCyclic K ∧ Nat.card K = 2 ^ n - 1 := by
  by_cases hKne : K = ⊥
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Finite N :=
      Finite.of_injective
        (fun x : N => (⟨(x : G), hN.le x.2⟩ : MulAction.stabilizer G v))
        (fun a b h => Subtype.ext
          (congrArg (fun z : MulAction.stabilizer G v => (z : G)) h))
    let L := PSL(2, GaloisField 2 n)
    let U : Sylow 2 L := S.mapSurjective (p := 2) hN.phi_surjective
    let D : Subgroup L := K.map hN.phi
    have hDinf : D ⊓ (U : Subgroup L) = ⊥ := hN.torus_map_inf hfin (S := S) (K := K) hKS
    have hDsup : D ⊔ (U : Subgroup L) = Subgroup.normalizer ((U : Subgroup L) : Set L) :=
      hN.torus_map_sup hfin (S := S) (K := K) hsup
    have hDcard : Nat.card D = 2 ^ n - 1 := psl2_torus_card hn hDinf hDsup
    have hDbot : D = ⊥ := by
      dsimp [D]
      rw [hKne]
      simp
    have hD1 : Nat.card D = 1 := by rw [hDbot]; simp
    rw [hD1] at hDcard
    have hpowle : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have hpow2 : 2 ^ n = 2 := by omega
    have hn1 : n = 1 := by
      by_contra h
      have h2 : 2 ≤ n := by omega
      have h4 : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2
      omega
    constructor
    · rw [hKne]
      infer_instance
    · rw [hKne, hn1]
      simp
  · exact hN.torus_cyclic_of_ne_bot hadj hfin hcard hn S K hKS hsup hKne

end IsLocL2

end CFSG.Quasithin.St84
