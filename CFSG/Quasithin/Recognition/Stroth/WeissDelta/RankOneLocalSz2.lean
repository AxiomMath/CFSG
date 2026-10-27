module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RankOneLocalSz
public import CFSG.LieType.Ree.SuzukiSplitTorusCentralizers

public section

open scoped Pointwise LinearAlgebra.Projectivization

namespace CFSG.Quasithin.Stroth.WeissDelta

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.LieType.Ree
  CFSG.ShultStronglyClosedTI.SuzukiModel CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartOne.CTP

theorem exists_root_at {X Ω : Type*} [Group X] [Finite X] [MulAction X Ω]
    {N : Subgroup X} [N.Normal] {q : ℕ} {ω β : Ω} {Q T : Subgroup N}
    (P : SuzukiPointAction N Ω q ω β Q T) :
    ∃ R : Subgroup X, R ≤ MulAction.stabilizer X ω ∧
      (R.subgroupOf (MulAction.stabilizer X ω)).Normal ∧ IsPGroup 2 R ∧
      ∀ a b : Ω, a ≠ ω → b ≠ ω → ∃! r : R, (r : X) • a = b := by
  classical
  obtain ⟨S, hS⟩ := P.exists_sylow
  have hQ2 : IsPGroup 2 Q := by rw [← hS]; exact S.isPGroup'
  have hQle : Q ≤ MulAction.stabilizer N ω := by
    rw [← P.sup_eq_stabilizer]
    exact le_sup_left
  let R : Subgroup X := Q.map N.subtype
  have hRle : R ≤ MulAction.stabilizer X ω := by
    intro r hr
    rcases hr with ⟨q, hq, rfl⟩
    exact hQle hq
  have hRnorm : MulAction.stabilizer X ω ≤ Subgroup.normalizer (R : Set X) :=
    root_normal_in_pointStabilizer hQ2 ⟨S, hS⟩ hQle P.stabilizer_le_normalizer
  have hRnormal : (R.subgroupOf (MulAction.stabilizer X ω)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRle).mpr hRnorm
  refine ⟨R, hRle, hRnormal, hQ2.map _, ?_⟩
  intro a b ha hb
  obtain ⟨r, hr, huniq⟩ := P.regular a b ha hb
  refine ⟨⟨(r : N), Subgroup.mem_map_of_mem N.subtype r.2⟩, ?_, ?_⟩
  · change ((r : N) : X) • a = b
    exact hr
  · intro s hs
    rcases s.2 with ⟨r', hr', hval⟩
    have hact : ((r' : N) : X) • a = b := by
      have hs' : (s : X) • a = b := hs
      rw [← hval] at hs'
      exact hs'
    have hr'eq : r' = (r : N) := congrArg Subtype.val (huniq ⟨r', hr'⟩ hact)
    apply Subtype.ext
    change (s : X) = ((r : N) : X)
    rw [← hval, hr'eq]
    rfl

theorem exists_root_arbitrary {X Ω : Type*} [Group X] [Finite X] [MulAction X Ω]
    {N : Subgroup X} [N.Normal] {q : ℕ} {ω β : Ω} {Q T : Subgroup N}
    (P : SuzukiPointAction N Ω q ω β Q T) (x : Ω) :
    ∃ R : Subgroup X, R ≤ MulAction.stabilizer X x ∧
      (R.subgroupOf (MulAction.stabilizer X x)).Normal ∧ IsPGroup 2 R ∧
      ∀ a b : Ω, a ≠ x → b ≠ x → ∃! r : R, (r : X) • a = b := by
  classical
  haveI : MulAction.IsPretransitive N Ω :=
    MulAction.isPretransitive_of_is_two_pretransitive
      (h2 := P.isMultiplyPretransitive)
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N ω x
  subst hn
  exact exists_root_at (N := N) (P := P.conj n)

end CFSG.Quasithin.Stroth.WeissDelta

namespace CFSG.Quasithin.Stroth.WeissDelta

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.LieType.Ree
  CFSG.ShultStronglyClosedTI.SuzukiModel CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartOne.CTP

theorem outer_sz_cyclic_odd (a : ℕ) (ha : 1 ≤ a)
    {N : Type} [Group N] (e : N ≃* Sz a) :
    IsCyclic (Outer N) ∧ Odd (Nat.card (Outer N)) := by
  classical
  let K := GaloisField 2 (2 * a + 1)
  have hK : Nat.card K = 2 ^ (2 * a + 1) := GaloisField.card 2 _ (by omega)
  let φ : N ≃* suzukiGroup a K := e.trans (szToSuzukiGroup a)
  have hG := (CFSG.RankThree.Automorphisms.Suzuki_full_field_automorphism_splitting
    a ha K hK).2.2.2.2
  have hcyc : IsCyclic (Outer (suzukiGroup a K)) := hG.1
  have hodd : Odd (Nat.card (Outer (suzukiGroup a K))) := hG.2.2
  have ε := equivalence φ
  have hcard : Nat.card (Outer N) = Nat.card (Outer (suzukiGroup a K)) :=
    Nat.card_congr ε.toEquiv
  exact ⟨isCyclic_of_surjective ε.symm.toMonoidHom ε.symm.surjective,
    hcard ▸ hodd⟩

theorem perfectResidual_eq_of_normal_perfect_outer {X : Type} [Group X] [Finite X]
    {N : Subgroup X} [N.Normal]
    (hperf : Group.IsPerfect N) (hOut : Group.IsSolvable (Outer N))
    (hC : Subgroup.centralizer (N : Set X) = ⊥) :
    CFSG.perfectResidual X = N := by
  have hsolv : Group.IsSolvable (X ⧸ N) :=
    solvable_quotient_of_outer N hC (h := hOut)
  have hresle : CFSG.perfectResidual X ≤ N :=
    ((CFSG.perfect_residual_characterization (G := X)).2.2.2.2.1 N).mp hsolv
  refine le_antisymm hresle ?_
  exact (perfect_residual_transport (MonoidHom.id X)).2.2 N hperf

theorem odd_of_odd_inf_normal_outer {X : Type} [Group X] [Finite X]
    {N H T : Subgroup X} [N.Normal] (hC : Subgroup.centralizer (N : Set X) = ⊥)
    (hTH : T ≤ H) (hTn : (T.subgroupOf H).Normal)
    (hT : T = H ⊓ N) (hTodd : Odd (Nat.card T))
    (hOut : Odd (Nat.card (Outer N))) : Odd (Nat.card H) := by
  classical
  letI : (T.subgroupOf H).Normal := hTn
  let f : H →* Outer N := (outerHom N).comp H.subtype
  have hker : f.ker = T.subgroupOf H := by
    ext x
    constructor
    · intro hx
      have hxX : (x : X) ∈ (outerHom N).ker := hx
      rw [ker_outerHom N hC] at hxX
      rw [hT]
      exact ⟨x.2, hxX⟩
    · intro hx
      rw [hT] at hx
      change outerHom N (x : X) = 1
      rw [← MonoidHom.mem_ker, ker_outerHom N hC]
      exact hx.2
  let g : H ⧸ T.subgroupOf H →* Outer N :=
    QuotientGroup.lift (T.subgroupOf H) f (by
      intro x hx
      rw [MonoidHom.mem_ker]
      have : x ∈ f.ker := by simpa [hker]
      exact this)
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    have hy : f y = 1 := hx
    have : y ∈ f.ker := hy
    rw [hker] at this
    exact (QuotientGroup.eq_one_iff y).mpr this
  have hquot : Odd (Nat.card (H ⧸ T.subgroupOf H)) :=
    Odd.of_dvd_nat hOut (Subgroup.card_dvd_of_injective g hg)
  have hcardT : Nat.card (T.subgroupOf H) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv
  have hprod : Nat.card H = Nat.card (T.subgroupOf H) * Nat.card (H ⧸ T.subgroupOf H) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (T.subgroupOf H), Nat.mul_comm]
  rw [hprod, hcardT]
  exact hTodd.mul hquot

end CFSG.Quasithin.Stroth.WeissDelta

namespace CFSG.Quasithin.Stroth.WeissDelta

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.LieType.Ree
  CFSG.ShultStronglyClosedTI.SuzukiModel CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartOne.CTP

theorem exists_conj_torus {N Ω : Type*} [Group N] [MulAction N Ω] {q : ℕ} {ω β : Ω}
    {Q T : Subgroup N} (P : SuzukiPointAction N Ω q ω β Q T) {x y : Ω} (hxy : x ≠ y) :
    ∃ n : N, n • ω = x ∧ n • β = y ∧
      MulAction.stabilizer N x ⊓ MulAction.stabilizer N y =
        T.map (MulAut.conj n).toMonoidHom := by
  have h2' : ∀ {a b c d : Ω}, a ≠ b → c ≠ d →
      ∃ g : N, g • a = c ∧ g • b = d :=
    MulAction.is_two_pretransitive_iff.mp P.isMultiplyPretransitive
  obtain ⟨n, hx, hy⟩ := h2' (a := ω) (b := β) (c := x) (d := y) P.ne hxy
  refine ⟨n, hx, hy, ?_⟩
  rw [← hx, ← hy, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    ← Subgroup.map_inf_eq _ _ _ (MulAut.conj n).injective,
    P.stabilizer_inf_stabilizer]

theorem inf_stabilizer_eq_map_subtype {X Ω : Type*} [Group X] [MulAction X Ω] {N : Subgroup X}
    {H : Subgroup N} {x y : Ω}
    (hH : MulAction.stabilizer N x ⊓ MulAction.stabilizer N y = H) :
    N ⊓ MulAction.stabilizer X x ⊓ MulAction.stabilizer X y = H.map N.subtype := by
  rw [← hH]
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.coe_subtype]
  constructor
  · rintro ⟨⟨hgN, hgx⟩, hgy⟩
    exact ⟨⟨g, hgN⟩, ⟨hgx, hgy⟩, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h.2, hh.1⟩, hh.2⟩

theorem fix_two_conj {N Ω : Type*} [Group N] [MulAction N Ω] {q : ℕ} {ω β : Ω}
    {Q T : Subgroup N} (P : SuzukiPointAction N Ω q ω β Q T)
    (hfix : ∀ t ∈ T, t ≠ 1 → ∀ z : Ω, t • z = z → z = ω ∨ z = β)
    {x y : Ω} (n : N) (hx : n • ω = x) (hy : n • β = y) :
    ∀ t ∈ T.map (MulAut.conj n).toMonoidHom, t ≠ 1 →
      ∀ z : Ω, t • z = z → z = x ∨ z = y := by
  intro t ht ht1 z hz
  rcases ht with ⟨s, hs, rfl⟩
  have hs1 : s ≠ 1 := by
    intro h
    apply ht1
    rw [h, map_one]
  have hz' : s • (n⁻¹ • z) = n⁻¹ • z := by
    have h := hz
    change (n * s * n⁻¹) • z = z at h
    apply smul_left_cancel n
    calc n • (s • (n⁻¹ • z)) = (n * s * n⁻¹) • z := by
          simp only [mul_smul]
      _ = z := h
      _ = n • (n⁻¹ • z) := (smul_inv_smul n z).symm
  rcases hfix s hs hs1 _ hz' with h | h
  · left
    have : n • (n⁻¹ • z) = n • ω := by rw [h]
    simpa [hx] using this
  · right
    have : n • (n⁻¹ • z) = n • β := by rw [h]
    simpa [hy] using this

end CFSG.Quasithin.Stroth.WeissDelta

namespace CFSG.Quasithin.Stroth.WeissDelta

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.LieType.Ree
  CFSG.ShultStronglyClosedTI.SuzukiModel CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartOne.CTP

theorem rankOneLocal_sz {X Ω : Type} [Group X] [Finite X]
    [Fintype Ω] [MulAction X Ω] [FaithfulSMul X Ω]
    (h2 : MulAction.IsMultiplyPretransitive X Ω 2) (a : ℕ) (ha : 1 ≤ a)
    (N : Subgroup X) (hN : N.Normal) (e : ↥N ≃* Sz a)
    (hΩ : Fintype.card Ω = 2 ^ (2 * (2 * a + 1)) + 1) :
    RankOneLocal X Ω N := by
  classical
  let K := GaloisField 2 (2 * a + 1)
  have hK : Nat.card K = 2 ^ (2 * a + 1) := GaloisField.card 2 _ (by omega)
  obtain ⟨ω, β, Q, T, ψ, P, hψT, hψQ, hψB⟩ :=
    exists_szPointAction (X := X) (Ω := Ω) h2 ha N hN e hΩ
  haveI : MulAction.IsMultiplyPretransitive N Ω 2 := P.isMultiplyPretransitive
  haveI : MulAction.IsPretransitive N Ω :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have hTcard : Nat.card T = 2 ^ (2 * a + 1) - 1 := P.card_T
  have hTodd : Odd (Nat.card T) := by
    rw [hTcard]
    exact mersenne_odd.mpr (by omega)
  have hcent := (suzuki_split_torus_odd_prime_centralizers (a := a) (K := K) hK).1
  have hdisj := suzukiU_inf_suzukiT (a := a) (K := K) hK
  have hCQ : ∀ t ∈ T, t ≠ 1 → ∀ q ∈ Q, q * t = t * q → q = 1 :=
    centralizer_trivial_on_root ψ hψT hψQ hcent hdisj
  have hfix : ∀ t ∈ T, t ≠ 1 → ∀ z : Ω, t • z = z → z = ω ∨ z = β :=
    fix_two_of_pointAction P hCQ
  have hperfG : Group.IsPerfect (suzukiGroup a K) :=
    (suzuki_perfect (a := a) (K := K) ha hK).2
  have hperfN : Group.IsPerfect N :=
    Group.IsPerfect.ofSurjective (f := ψ.symm.toMonoidHom) ψ.symm.surjective
  have hQbot : Q ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card Q = 1 := by rw [hbot, Subgroup.card_bot]
    rw [P.card_U] at h1
    have hq : 1 < (2 ^ (2 * a + 1)) ^ 2 := by
      calc 1 < 2 ^ (2 * a + 1) := by
            calc 1 < 2 := by norm_num
              _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (n := 2) (i := 1)
                  (j := 2 * a + 1) (by norm_num) (by omega)
        _ ≤ (2 ^ (2 * a + 1)) ^ 2 := by
            calc 2 ^ (2 * a + 1) = 2 ^ (2 * a + 1) * 1 := by ring
              _ ≤ 2 ^ (2 * a + 1) * 2 ^ (2 * a + 1) :=
                  Nat.mul_le_mul_left _ Nat.one_le_two_pow
              _ = (2 ^ (2 * a + 1)) ^ 2 := by ring
    exact (ne_of_gt hq) h1
  haveI : Nontrivial N := by
    obtain ⟨q, hq⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQbot
    exact ⟨q, 1, fun h => hq (Subtype.ext h)⟩
  have hNnonab : ¬ IsMulCommutative N := hperfN.not_isMulCommutative
  have hCbot : Subgroup.centralizer (N : Set X) = ⊥ :=
    centralizer_eq_bot_of_isMultiplyPretransitive hNnonab h2
  have hOut := outer_sz_cyclic_odd a ha e
  haveI : IsMulCommutative (Outer N) := hOut.1.isMulCommutative
  have hOutSolv : Group.IsSolvable (Outer N) :=
    Group.isSolvable_of_comm fun x y => mul_comm' x y
  have hOutOdd : Odd (Nat.card (Outer N)) := hOut.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun x => exists_root_arbitrary (N := N) P x
  · intro x y hxy
    obtain ⟨n, -, -, hTxy⟩ := exists_conj_torus P hxy
    let Tsub : Subgroup X := (T.map (MulAut.conj n).toMonoidHom).map N.subtype
    have hfield : N ⊓ MulAction.stabilizer X x ⊓ MulAction.stabilizer X y = Tsub :=
      inf_stabilizer_eq_map_subtype hTxy
    rw [hfield]
    rw [show Nat.card Tsub = Nat.card (T.map (MulAut.conj n).toMonoidHom) from
      Subgroup.card_map_of_injective (Subtype.coe_injective)]
    rw [Subgroup.card_map_of_injective (MulAut.conj n).injective]
    exact hTodd
  · intro x y z hxy hfixall
    obtain ⟨n, hx, hy, hTxy⟩ := exists_conj_torus P hxy
    let Tsub : Subgroup X := (T.map (MulAut.conj n).toMonoidHom).map N.subtype
    have hfield : N ⊓ MulAction.stabilizer X x ⊓ MulAction.stabilizer X y = Tsub :=
      inf_stabilizer_eq_map_subtype hTxy
    have hcard : Nat.card (T.map (MulAut.conj n).toMonoidHom) =
        2 ^ (2 * a + 1) - 1 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, hTcard]
    have hTne : T.map (MulAut.conj n).toMonoidHom ≠ ⊥ := by
      intro hbot
      have h1 : Nat.card (T.map (MulAut.conj n).toMonoidHom) = 1 := by
        rw [hbot, Subgroup.card_bot]
      rw [hcard] at h1
      have hq : 8 ≤ 2 ^ (2 * a + 1) := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨t, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hTne
    have htfield : ((t : N) : X) ∈
        N ⊓ MulAction.stabilizer X x ⊓ MulAction.stabilizer X y := by
      rw [hfield]
      exact ⟨t, t.2, rfl⟩
    exact fix_two_conj P hfix n hx hy (t : N) t.2 (by simpa using ht1) z
      (hfixall ((t : N) : X) htfield)
  · intro x y hxy
    obtain ⟨n, -, -, hTxy⟩ := exists_conj_torus P hxy
    let Tsub : Subgroup X := (T.map (MulAut.conj n).toMonoidHom).map N.subtype
    have hfield : N ⊓ MulAction.stabilizer X x ⊓ MulAction.stabilizer X y = Tsub :=
      inf_stabilizer_eq_map_subtype hTxy
    have hTcyc : IsCyclic T := P.isCyclic
    letI : IsCyclic T := hTcyc
    rw [hfield]
    have hcyc : IsCyclic (T.map (MulAut.conj n).toMonoidHom) :=
      isCyclic_of_surjective
        (Subgroup.equivMapOfInjective T (MulAut.conj n).toMonoidHom
          (MulAut.conj n).injective).toMonoidHom (Equiv.surjective _)
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective (T.map (MulAut.conj n).toMonoidHom) N.subtype
        N.subtype_injective).toMonoidHom (Equiv.surjective _)
  · intro x y hxy S hS hSodd
    obtain ⟨n, -, -, hTxy⟩ := exists_conj_torus P hxy
    let H : Subgroup X := MulAction.stabilizer X x ⊓ MulAction.stabilizer X y
    let Tsub : Subgroup X := (T.map (MulAut.conj n).toMonoidHom).map N.subtype
    have hTsub : Tsub = H ⊓ N := by
      rw [show Tsub = (T.map (MulAut.conj n).toMonoidHom).map N.subtype from rfl]
      rw [← hTxy]
      ext g
      simp [H, Subgroup.mem_inf, and_assoc]
    have hTH : Tsub ≤ H := by
      rw [hTsub]
      exact inf_le_left
    have hTn : (Tsub.subgroupOf H).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hTH]
      rw [hTsub]
      have hHN : H ≤ Subgroup.normalizer (N : Set X) := by
        haveI : N.Normal := hN
        rw [Subgroup.normalizer_eq_top]
        exact le_top
      refine le_trans (le_inf Subgroup.le_normalizer hHN) ?_
      exact Subgroup.inf_normalizer_le_normalizer_inf
    have hTsubOdd : Odd (Nat.card Tsub) := by
      have h1 : Nat.card Tsub = Nat.card (T.map (MulAut.conj n).toMonoidHom) :=
        Subgroup.card_map_of_injective (Subtype.coe_injective)
      have h2 : Nat.card (T.map (MulAut.conj n).toMonoidHom) = Nat.card T :=
        Subgroup.card_map_of_injective (MulAut.conj n).injective
      rw [h1, h2]
      exact hTodd
    have hHodd : Odd (Nat.card H) :=
      odd_of_odd_inf_normal_outer hCbot hTH hTn hTsub hTsubOdd hOutOdd
    exact Odd.of_dvd_nat hHodd
      (Subgroup.card_dvd_of_le ((Subgroup.closure_le _).mpr hS))
  · exact perfectResidual_eq_of_normal_perfect_outer hperfN hOutSolv hCbot

end CFSG.Quasithin.Stroth.WeissDelta

namespace CFSG.Quasithin.Stroth.WeissDelta

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.LieType.Ree
  CFSG.ShultStronglyClosedTI.SuzukiModel CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartOne.CTP

theorem fix_two_arbitrary {X Ω : Type*} [Group X] [Finite X] [MulAction X Ω]
    {N : Subgroup X} [N.Normal] {q : ℕ} {ω β : Ω} {Q T : Subgroup N}
    (P : SuzukiPointAction N Ω q ω β Q T)
    (hfix : ∀ t ∈ T, t ≠ 1 → ∀ z : Ω, t • z = z → z = ω ∨ z = β)
    {x y : Ω} (hxy : x ≠ y) :
    ∀ t ∈ N ⊓ MulAction.stabilizer X x ⊓ MulAction.stabilizer X y, t ≠ 1 →
      ∀ z : Ω, t • z = z → z = x ∨ z = y := by
  obtain ⟨n, hx, hy, hTxy⟩ := exists_conj_torus P hxy
  let Tsub : Subgroup X := (T.map (MulAut.conj n).toMonoidHom).map N.subtype
  have hfield : N ⊓ MulAction.stabilizer X x ⊓ MulAction.stabilizer X y = Tsub :=
    inf_stabilizer_eq_map_subtype hTxy
  intro t ht ht1 z hz
  have ht' : t ∈ Tsub := by rwa [hfield] at ht
  rcases ht' with ⟨s, hs, hst⟩
  have hs1 : s ≠ 1 := by
    intro h
    apply ht1
    rw [← hst, h, map_one]
  have hz' : s • z = z := by
    rwa [← hst] at hz
  exact fix_two_conj P hfix n hx hy s hs hs1 z hz'

@[expose] def SzCentralizerLe (X Ω : Type*) [Group X] [MulAction X Ω] (N : Subgroup X) : Prop :=
  ∀ (x y : Ω), x ≠ y → ∀ g ∈ MulAction.stabilizer X x ⊓ MulAction.stabilizer X y,
    (∀ t ∈ N ⊓ MulAction.stabilizer X x ⊓ MulAction.stabilizer X y, g * t = t * g) → g ∈ N

theorem rankOneZassenhaus_sz_of_centralizer
    {X Ω : Type} [Group X] [Finite X] [Fintype Ω] [MulAction X Ω] [FaithfulSMul X Ω]
    (h2 : MulAction.IsMultiplyPretransitive X Ω 2) (a : ℕ) (ha : 1 ≤ a)
    (N : Subgroup X) (hN : N.Normal) (e : ↥N ≃* Sz a)
    (hΩ : Fintype.card Ω = 2 ^ (2 * (2 * a + 1)) + 1)
    (hA4 : SzCentralizerLe X Ω N) :
    RankOneZassenhaus X Ω N := by
  classical
  let K := GaloisField 2 (2 * a + 1)
  have hK : Nat.card K = 2 ^ (2 * a + 1) := GaloisField.card 2 _ (by omega)
  obtain ⟨ω, β, Q, T, ψ, P, hψT, hψQ, hψB⟩ :=
    exists_szPointAction (X := X) (Ω := Ω) h2 ha N hN e hΩ
  haveI : MulAction.IsMultiplyPretransitive N Ω 2 := P.isMultiplyPretransitive
  have hcent := (suzuki_split_torus_odd_prime_centralizers (a := a) (K := K) hK).1
  have hdisj := suzukiU_inf_suzukiT (a := a) (K := K) hK
  have hCQ : ∀ t ∈ T, t ≠ 1 → ∀ q ∈ Q, q * t = t * q → q = 1 :=
    centralizer_trivial_on_root ψ hψT hψQ hcent hdisj
  have hfix : ∀ t ∈ T, t ≠ 1 → ∀ z : Ω, t • z = z → z = ω ∨ z = β :=
    fix_two_of_pointAction P hCQ
  refine ⟨?_, ?_⟩
  · intro x y hxy t ht ht1 z hz
    exact fix_two_arbitrary P hfix hxy t ht ht1 z hz
  · exact hA4

end CFSG.Quasithin.Stroth.WeissDelta
