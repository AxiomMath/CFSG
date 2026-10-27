module

public import CFSG.RankThree.PartTwo.Sec8.HeringU3nBender
public import CFSG.RankThree.PartTwo.KFacts.AutPSU
import CFSG.RankThree.PartTwo.Sec4.StepsBender
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AAE7
import CFSG.RankThree.PartTwo.Sec6.Item611FixProofG2
import CFSG.LocalAnalysis.RankFourTheoremC.PPointMaxPair
import CFSG.RankThree.PartTwo.Sec19.Step196KFact

public section

namespace CFSG.RankThree.PartTwo.Sec8.HeringU3n

open CFSG.GH74.Uniqueness.Bender
open CFSG.RankThreeEvenClassification.Helpers
  (exists_centralizer_preimage_of_pGroup_prime_complement_kernel)

variable {X : Type} [Group X] [Finite X]

theorem sylow_eq_of_map_eq {N : Subgroup X} [N.Normal] (hNc : N ≤ Subgroup.center X)
    (hNodd : Odd (Nat.card N)) {Q P : Sylow 2 X}
    (h : (Q : Subgroup X).map (QuotientGroup.mk' N) = (P : Subgroup X).map (QuotientGroup.mk' N)) :
    Q = P :=
  Sylow.ext (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.AAE7.eq_of_map_eq_central
    hNc hNodd Q.isPGroup' P.isPGroup' h)

theorem mk_invol {N : Subgroup X} [N.Normal] (hNodd : Odd (Nat.card N)) {s : X} (hs1 : s ≠ 1)
    (hs2 : s ^ 2 = 1) : QuotientGroup.mk' N s ≠ 1 ∧ (QuotientGroup.mk' N s) ^ 2 = 1 := by
  have hN2 : ¬ 2 ∣ Nat.card N := by
    have := Nat.odd_iff.mp hNodd
    omega
  refine ⟨fun h1 => hs1 ?_, by rw [← map_pow, hs2, map_one]⟩
  exact CFSG.RankThree.PartTwo.Sec4.eq_one_of_pow_prime_pow_eq_one Nat.prime_two hN2
    ((QuotientGroup.eq_one_iff s).mp h1) (a := 1) (by simpa using hs2)

theorem cover_sylow_data {N : Subgroup X} [N.Normal]
    (hNc : N ≤ Subgroup.center X) (hNodd : Odd (Nat.card N)) {m e : ℕ}
    (h : BenderType (X ⧸ N) m 3 e) {s : X} (hs1 : s ≠ 1) (hs2 : s ^ 2 = 1) :
    ∃ P : Sylow 2 X, (∀ Q : Sylow 2 X, s ∈ (Q : Subgroup X) → Q = P) ∧ s ∈ (P : Subgroup X) ∧
      qOf s = (P : Subgroup X) ∧
      (P : Subgroup X).map (QuotientGroup.mk' N) = qOf (QuotientGroup.mk' N s) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' N with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  obtain ⟨hs1', hs2'⟩ := mk_invol hNodd hs1 hs2
  obtain ⟨Pb, huniq, hsPb, hszb, hqb, -, -, -, -⟩ := bender_sylow_data h hs1' hs2'
  obtain ⟨P, hsP⟩ := CFSG.GH74.Uniqueness.Sec128B.exists_sylow_mem_of_orderOf_eq_two
    (orderOf_eq_prime hs2 hs1)
  have hmapS : ∀ Q : Sylow 2 X, s ∈ (Q : Subgroup X) →
      (Q : Subgroup X).map π = (Pb : Subgroup (X ⧸ N)) := by
    intro Q hsQ
    have hQ : Q.mapSurjective (f := π) hsurj = Pb :=
      huniq _ (by rw [Sylow.coe_mapSurjective]; exact ⟨s, hsQ, rfl⟩)
    have := congrArg (fun R : Sylow 2 (X ⧸ N) => (R : Subgroup (X ⧸ N))) hQ
    simpa using this
  have hPmap := hmapS P hsP
  have hscent : ∀ y ∈ (P : Subgroup X), y * s = s * y := by
    intro y hy
    have hyb : π y ∈ (Pb : Subgroup (X ⧸ N)) := hPmap ▸ ⟨y, hy, rfl⟩
    have hc : π y * π s = π s * π y := (mem_rootCenter_iff.mp hszb).2 _ hyb
    have hcP : y * s * y⁻¹ * s⁻¹ ∈ (P : Subgroup X) :=
      (P : Subgroup X).mul_mem ((P : Subgroup X).mul_mem ((P : Subgroup X).mul_mem hy hsP)
        ((P : Subgroup X).inv_mem hy)) ((P : Subgroup X).inv_mem hsP)
    have hπc : π (y * s * y⁻¹ * s⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hc]
      group
    have hc1 := CFSG.ComponentClassification.AschbacherTheorem3.mk_eq_one_of_odd hNodd
      P.isPGroup' hcP hπc
    calc y * s = (y * s * y⁻¹ * s⁻¹) * (s * y) := by group
      _ = s * y := by rw [hc1, one_mul]
  have hPC : (P : Subgroup X) ≤ Subgroup.centralizer ({s} : Set X) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hscent y hy)
  have hCnorm : Subgroup.centralizer ({s} : Set X) ≤
      Subgroup.normalizer ((P : Subgroup X) : Set X) := by
    intro g hg
    have hgs : g * s = s * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    have hsg : s ∈ ((g • P : Sylow 2 X) : Subgroup X) := by
      rw [mem_sylow_smul_iff]
      have : g⁻¹ * s * g = s := by
        calc g⁻¹ * s * g = g⁻¹ * (s * g) := by group
          _ = g⁻¹ * (g * s) := by rw [hgs]
          _ = s := by group
      rw [this]
      exact hsP
    have hgP : g • P = P :=
      sylow_eq_of_map_eq hNc hNodd (by rw [hmapS _ hsg, hPmap])
    exact Sylow.smul_eq_iff_mem_normalizer.mp hgP
  refine ⟨P, fun Q hsQ => sylow_eq_of_map_eq hNc hNodd (by rw [hmapS Q hsQ, hPmap]), hsP, ?_,
    by rw [hqb]; exact hPmap⟩
  apply le_antisymm
  · have hQ2 : IsPGroup 2 (qOf s) := isPGroup_qOf s
    have hPn : (P : Subgroup X) ≤ Subgroup.normalizer (qOf s : Set X) :=
      hPC.trans (centralizer_le_normalizer_qOf s)
    have hsup : IsPGroup 2 ↥(qOf s ⊔ (P : Subgroup X)) :=
      CFSG.LocalAnalysis.RankFourTheoremC.isPGroup_sup_of_le_normalizer hQ2 P.isPGroup' hPn
    exact (P.is_maximal' hsup le_sup_right ▸ le_sup_left)
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPC hCnorm P.isPGroup'

theorem cover_root {N : Subgroup X} [N.Normal]
    (hNc : N ≤ Subgroup.center X) (hNodd : Odd (Nat.card N)) {m e : ℕ}
    (h : BenderType (X ⧸ N) m 3 e) {s : X} (hs1 : s ≠ 1) (hs2 : s ^ 2 = 1)
    {E : Subgroup X} (hE : CFSG.Assembly.IsElemAbelian 2 E) (hEc : Nat.card E = 2 ^ m)
    (hsE : s ∈ E) :
    (∀ u ∈ qOf s, ∀ x ∈ E, u * x = x * u) ∧ (∀ u ∈ qOf s, u ^ 2 = 1 → u ∈ E) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' N with hπ
  obtain ⟨P, huniq, hsP, hq, hmap⟩ := cover_sylow_data hNc hNodd h hs1 hs2
  obtain ⟨hs1', hs2'⟩ := mk_invol hNodd hs1 hs2
  obtain ⟨Pb, -, -, -, hqb, -, hinvb, -, hEb⟩ := bender_sylow_data h hs1' hs2'
  have hPb : (P : Subgroup X).map π = (Pb : Subgroup (X ⧸ N)) := by rw [hmap, hqb]
  have hE2 : IsPGroup 2 E := IsPGroup.of_card hEc
  obtain ⟨Q, hEQ⟩ := hE2.exists_le_sylow
  have hEP : E ≤ (P : Subgroup X) := (huniq Q (hEQ hsE)) ▸ hEQ
  have hinjE : ∀ x ∈ E, π x = 1 → x = 1 := fun x hx h1 =>
    CFSG.ComponentClassification.AschbacherTheorem3.mk_eq_one_of_odd hNodd hE2 hx h1
  have hEcardb : Nat.card (E.map π) = 2 ^ m := by
    rw [CFSG.RankThree.PartTwo.Sec6.Res611Fix.card_map_of_inf_ker_eq_bot π
      (H := E) (by
        rw [eq_bot_iff]
        intro x hx
        exact Subgroup.mem_bot.mpr (hinjE x hx.1 (MonoidHom.mem_ker.mp hx.2)))]
    exact hEc
  have hEmap : E.map π = rootCenter (Pb : Subgroup (X ⧸ N)) :=
    hEb (E.map π) (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 2 π E hE) hEcardb
      ⟨s, hsE, rfl⟩
  have hinjP : ∀ x ∈ (P : Subgroup X), π x = 1 → x = 1 := fun x hx h1 =>
    CFSG.ComponentClassification.AschbacherTheorem3.mk_eq_one_of_odd hNodd P.isPGroup' hx h1
  rw [hq]
  refine ⟨fun u hu x hx => ?_, fun u hu hu2 => ?_⟩
  · have hxb : π x ∈ rootCenter (Pb : Subgroup (X ⧸ N)) := hEmap ▸ ⟨x, hx, rfl⟩
    have hub : π u ∈ (Pb : Subgroup (X ⧸ N)) := hPb ▸ ⟨u, hu, rfl⟩
    have hc : π u * π x = π x * π u := (mem_rootCenter_iff.mp hxb).2 _ hub
    have hxP : x ∈ (P : Subgroup X) := hEP hx
    have hcP : u * x * u⁻¹ * x⁻¹ ∈ (P : Subgroup X) :=
      (P : Subgroup X).mul_mem ((P : Subgroup X).mul_mem ((P : Subgroup X).mul_mem hu hxP)
        ((P : Subgroup X).inv_mem hu)) ((P : Subgroup X).inv_mem hxP)
    have hπc : π (u * x * u⁻¹ * x⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hc]
      group
    have hc1 := hinjP _ hcP hπc
    calc u * x = (u * x * u⁻¹ * x⁻¹) * (x * u) := by group
      _ = x * u := by rw [hc1, one_mul]
  · have hub : π u ∈ (Pb : Subgroup (X ⧸ N)) := hPb ▸ ⟨u, hu, rfl⟩
    have hz : π u ∈ rootCenter (Pb : Subgroup (X ⧸ N)) :=
      hinvb (π u) hub (by rw [← map_pow, hu2, map_one])
    rw [← hEmap] at hz
    obtain ⟨x, hx, hxu⟩ := hz
    have hxP : x ∈ (P : Subgroup X) := hEP hx
    have hmem : u * x⁻¹ ∈ (P : Subgroup X) :=
      (P : Subgroup X).mul_mem hu ((P : Subgroup X).inv_mem hxP)
    have h1 : u * x⁻¹ = 1 := hinjP _ hmem (by simp only [map_mul, map_inv, hxu, mul_inv_cancel])
    have : u = x := mul_inv_eq_one.mp h1
    rw [this]
    exact hx

theorem cover_aut [Group.IsPerfect X]
    (hodd : Odd (Nat.card (Subgroup.center X))) {m e : ℕ} (hm : Odd m)
    (h : BenderType (X ⧸ Subgroup.center X) m 3 e) {s : X} (hs1 : s ≠ 1) (hs2 : s ^ 2 = 1)
    {F : Subgroup (MulAut X)} (hF : IsPGroup 2 F) (hFs : ∀ f ∈ F, f s = s)
    (hFn : ∀ x ∈ Subgroup.centralizer ({s} : Set X), ∀ f ∈ F,
      MulAut.conj x * f * (MulAut.conj x)⁻¹ ∈ F) :
    ∀ f ∈ F, ∃ u ∈ qOf s, f = MulAut.conj u := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.center X with hN
  set π := QuotientGroup.mk' N with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  obtain ⟨P, -, hsP, hq, hmap⟩ := cover_sylow_data (le_refl N) hodd h hs1 hs2
  obtain ⟨hs1', hs2'⟩ := mk_invol hodd hs1 hs2
  set d := CFSG.RankThree.PartTwo.KFacts.centerDescend X with hd
  have hdmk : ∀ (σ : MulAut X) (y : X), d σ (π y) = π (σ y) := fun σ y =>
    CFSG.RankThree.PartTwo.KFacts.centerDescend_mk X σ y
  set F' : Subgroup (MulAut (X ⧸ N)) := F.map d with hF'
  have hF'2 : IsPGroup 2 F' := hF.map d
  have hF's : ∀ f ∈ F', f (π s) = π s := by
    rintro _ ⟨f, hf, rfl⟩
    rw [hdmk, hFs f hf]
  have hkerY : ¬ 2 ∣ Nat.card π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    have := Nat.odd_iff.mp hodd
    omega
  have hzY : IsPGroup 2 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hs2 hs1, pow_one])
  have hF'n : ∀ xb ∈ Subgroup.centralizer ({π s} : Set (X ⧸ N)), ∀ f' ∈ F',
      MulAut.conj xb * f' * (MulAut.conj xb)⁻¹ ∈ F' := by
    intro xb hxb f' hf'
    have hcomm' : Commute (π s) xb := (Subgroup.mem_centralizer_singleton_iff.mp hxb).symm
    have hxbY : xb ∈ Subgroup.centralizer (((Subgroup.zpowers s).map π : Subgroup _) : Set _) := by
      rw [MonoidHom.map_zpowers, Subgroup.mem_centralizer_iff]
      rintro _ ⟨k, rfl⟩
      exact (hcomm'.zpow_left k).eq
    obtain ⟨x, hxc, rfl⟩ := exists_centralizer_preimage_of_pGroup_prime_complement_kernel 2
      Nat.prime_two π hsurj hkerY _ hzY xb hxbY
    have hxs : x ∈ Subgroup.centralizer ({s} : Set X) := by
      rw [Subgroup.mem_centralizer_iff] at hxc ⊢
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hxc s (Subgroup.mem_zpowers s)
    obtain ⟨f, hf, rfl⟩ := hf'
    have : MulAut.conj (π x) * d f * (MulAut.conj (π x))⁻¹ =
        d (MulAut.conj x * f * (MulAut.conj x)⁻¹) := by
      rw [map_mul, map_mul, map_inv, CFSG.RankThree.PartTwo.Sec19.Step196Proof.centerDescend_conj]
      rfl
    rw [this]
    exact ⟨_, hFn x hxs f hf, rfl⟩
  have hbar := bender_aut_pgroup hm h hs1' hs2' hF'2 hF's hF'n
  intro f hf
  obtain ⟨ub, hub, hfub⟩ := hbar (d f) ⟨f, hf, rfl⟩
  rw [← hmap] at hub
  obtain ⟨u, hu, rfl⟩ := hub
  refine ⟨u, hq ▸ hu, ?_⟩
  refine CFSG.RankThree.PartTwo.Sec4.mulAut_eq_of_inv_mul_mem_center (fun y => ?_)
  have hy := congrArg (fun σ : MulAut (X ⧸ N) => σ (π y)) hfub
  simp only [hdmk, MulAut.conj_apply, ← hπ] at hy
  have h1 : π ((MulAut.conj u y)⁻¹ * f y) = 1 := by
    simp only [map_mul, map_inv, MulAut.conj_apply]
    rw [hy]
    group
  exact (QuotientGroup.eq_one_iff _).mp h1

end CFSG.RankThree.PartTwo.Sec8.HeringU3n
