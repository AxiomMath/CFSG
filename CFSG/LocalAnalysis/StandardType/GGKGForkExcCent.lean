module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcFrame
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcRootsB
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcRootsD

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootOps CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE

private theorem ggKGEx_units_map_fr_eq_pow
    {K : Type} [Field K] (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (u : (AlgebraicClosure K)ˣ) :
    Units.map Fr.toMonoidHom u = u ^ Nat.card K := by
  apply Units.ext
  rw [Units.coe_map]
  change Fr ↑u = ↑u ^ Nat.card K
  rw [hFr]

private theorem ggKGEx_units_map_fr_inv_eq_self
    {K : Type} [Field K] {p : ℕ} (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) {b : (AlgebraicClosure K)ˣ} (hb : b ^ p = 1)
    {k : ℕ} (hq : Nat.card K = p * k - 1) (hpk : 1 ≤ p * k) :
    (Units.map Fr.toMonoidHom b)⁻¹ = b := by
  rw [ggKGEx_units_map_fr_eq_pow Fr hFr b, hq]
  have h1 : b ^ (p * k) = 1 := by rw [pow_mul, hb, one_pow]
  have h2 : b ^ (p * k - 1) = b⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel hpk, h1]
  rw [h2, inv_inv]

private noncomputable def ggKGEx_w0 (τ : Tag) : WeylGroup τ :=
  (coxeterSystem τ).wordProd ((RootOps.longestWord τ).map τ.idx)

private theorem ggKGEx_w0_smul_E7
    (i : Fin Tag.E7.rank) :
    ggKGEx_w0 .E7 • (Pi.single i 1 : Fin Tag.E7.rank → ℤ) = -Pi.single i 1 := by
  fin_cases i <;> (rw [ggKGEx_w0, wordProd_smul] <;> decide +kernel)

private theorem ggKGEx_w0_smul_E8
    (i : Fin Tag.E8.rank) :
    ggKGEx_w0 .E8 • (Pi.single i 1 : Fin Tag.E8.rank → ℤ) = -Pi.single i 1 := by
  fin_cases i <;> (rw [ggKGEx_w0, wordProd_smul] <;> decide +kernel)

private theorem ggKGEx_w0_smul_F4
    (i : Fin Tag.F4.rank) :
    ggKGEx_w0 .F4 • (Pi.single i 1 : Fin Tag.F4.rank → ℤ) = -Pi.single i 1 := by
  fin_cases i <;> (rw [ggKGEx_w0, wordProd_smul] <;> decide +kernel)

def ggKGEx_phi : Equiv.Perm (Fin Tag.E6.rank) :=
  Equiv.swap ⟨0, by decide⟩ ⟨5, by decide⟩ * Equiv.swap ⟨2, by decide⟩ ⟨4, by decide⟩

private theorem ggKGEx_w0_smul_E6
    (i : Fin Tag.E6.rank) :
    ggKGEx_w0 .E6 • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) = -Pi.single (ggKGEx_phi i) 1 := by
  fin_cases i <;>
    (rw [ggKGEx_w0, wordProd_smul] <;> decide +kernel)

private theorem ggKGEx_w0_reversesSigns
    (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) :
    ReversesSigns (ggKGEx_w0 τ) := by
  have hsingle : ∀ i : Fin τ.rank,
      height (ggKGEx_w0 τ • (Pi.single i 1 : Fin τ.rank → ℤ)) < 0 := by
    intro i
    rcases hτ with rfl | rfl | rfl | rfl
    · rw [ggKGEx_w0_smul_E6 i]
      simp [height]
    · rw [ggKGEx_w0_smul_E7 i]
      simp [height]
    · rw [ggKGEx_w0_smul_E8 i]
      simp [height]
    · rw [ggKGEx_w0_smul_F4 i]
      simp [height]
  intro α hα hpos
  exact height_smul_neg_of_forall_single hsingle hα hpos

private theorem ggKGEx_w0_inv
    (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) :
    (ggKGEx_w0 τ)⁻¹ = ggKGEx_w0 τ :=
  (ReversesSigns.eq (ggKGEx_w0_reversesSigns τ hτ)
    (ReversesSigns.inv (ggKGEx_w0_reversesSigns τ hτ))).symm

private theorem ggKGEx_eq_w0
    (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {w : WeylGroup τ}
    (hw : ExcIsLongest τ w) : w = ggKGEx_w0 τ := by
  refine ReversesSigns.eq ?_ (ggKGEx_w0_reversesSigns τ hτ)
  refine fun α hα hpos => (IsRoot.height_neg_iff (IsRoot.smul hα w)).2 fun j =>
    hw α hα ((IsRoot.height_pos_iff hα).1 hpos) j

private theorem ggKGEx_weylTuple_w0_neg
    (τ : Tag) (hτ : τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    {K : Type} [Field K] (c : Fin τ.rank → Kˣ) :
    weylTuple (ggKGEx_w0 τ) c = c⁻¹ := by
  have h : ∀ j, ggKGEx_w0 τ • (Pi.single j 1 : Fin τ.rank → ℤ) = -Pi.single j 1 := by
    rcases hτ with rfl | rfl | rfl
    · exact ggKGEx_w0_smul_E7
    · exact ggKGEx_w0_smul_E8
    · exact ggKGEx_w0_smul_F4
  funext i
  rw [weylTuple, ggKGEx_w0_inv τ (by rcases hτ with rfl | rfl | rfl <;> simp), h i,
    show (-Pi.single i 1 : Fin τ.rank → ℤ) = 0 - Pi.single i 1 by simp, rootChar_sub,
    rootChar_zero, one_mul]
  rw [show rootChar c (Pi.single i 1) = c i from by simpa using rootChar_nsmul_single c i 1]
  rfl

private theorem ggKGEx_weylTuple_w0_phi
    {K : Type} [Field K] (c : Fin Tag.E6.rank → Kˣ) :
    weylTuple (ggKGEx_w0 .E6) c = fun i => (c (ggKGEx_phi i))⁻¹ := by
  funext i
  rw [weylTuple, ggKGEx_w0_inv .E6 (Or.inl rfl), ggKGEx_w0_smul_E6 i,
    show (-Pi.single (ggKGEx_phi i) 1 : Fin Tag.E6.rank → ℤ) = 0 - Pi.single (ggKGEx_phi i) 1 by
      simp,
    rootChar_sub, rootChar_zero, one_mul]
  rw [show rootChar c (Pi.single (ggKGEx_phi i) 1) = c (ggKGEx_phi i) from by
    simpa using rootChar_nsmul_single c (ggKGEx_phi i) 1]

private theorem ggKGEx_le_of_relIndex_dvd {G : Type*} [Group G] {p d : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {H X : Subgroup G} [Finite X] (hX : IsPGroup p X) (hd : d = 1 ∨ d = 2)
    (h : H.relIndex X ∣ d) : X ≤ H := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← Subgroup.relIndex_eq_one]
  obtain ⟨n, hn⟩ := hX.exists_card_eq
  have hdvd : H.relIndex X ∣ p ^ n := by
    rw [← hn]
    exact Subgroup.index_dvd_card (H.subgroupOf X)
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  rw [hm] at h ⊢
  rcases m with _ | m
  · simp
  · exfalso
    have hpd : p ∣ d := (dvd_pow_self p (Nat.succ_ne_zero m)).trans h
    rcases hd with rfl | rfl
    · exact hp.one_lt.ne' (Nat.dvd_one.1 hpd)
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hpd)

private theorem ggKGEx_mem_image_of_fixed_pow
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hτ6 : τ = .E6 → 5 ≤ p)
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {r : ModGL τ (AlgebraicClosure K)}
    (hr : r ∈ adjointGroup τ (AlgebraicClosure K))
    (hrF : Units.map (entrywiseHom Fr) r = r) (hrp : r ^ p = 1) :
    r ∈ (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) := by
  rcases hτ with rfl | rfl | rfl | rfl
  ·
    let X : Subgroup (ModGL Tag.E6 (AlgebraicClosure K)) := Subgroup.zpowers r
    have hXC : X ≤ adjointGroup Tag.E6 (AlgebraicClosure K) := Subgroup.zpowers_le.2 hr
    have hXF : ∀ x ∈ X, Units.map (entrywiseHom Fr) x = x := by
      intro x hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [map_zpow, hrF]
    have hXfin : Finite X :=
      Nat.finite_of_card_ne_zero (by
        rw [Nat.card_zpowers]
        exact (Nat.pos_of_dvd_of_pos (orderOf_dvd_of_pow_eq_one hrp) hp.pos).ne')
    have hXp : IsPGroup p X := by
      rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hrp) with h | h
      · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
      · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
    haveI : Finite X := hXfin
    obtain ⟨-, hgrp⟩ := finite_fixed_subgroup_rational 3 (Or.inl ⟨rfl, rfl⟩) Fr hFr X hXC hXF
    have := hτ6 rfl
    exact hgrp p hp (by omega) X le_rfl hXp (Subgroup.mem_zpowers r)
  ·
    let X : Subgroup (ModGL Tag.E7 (AlgebraicClosure K)) := Subgroup.zpowers r
    have hXC : X ≤ adjointGroup Tag.E7 (AlgebraicClosure K) := Subgroup.zpowers_le.2 hr
    have hXF : ∀ x ∈ X, Units.map (entrywiseHom Fr) x = x := by
      intro x hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [map_zpow, hrF]
    have hXfin : Finite X :=
      Nat.finite_of_card_ne_zero (by
        rw [Nat.card_zpowers]
        exact (Nat.pos_of_dvd_of_pos (orderOf_dvd_of_pow_eq_one hrp) hp.pos).ne')
    have hXp : IsPGroup p X := by
      rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hrp) with h | h
      · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
      · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
    haveI : Finite X := hXfin
    obtain ⟨hidx, -⟩ :=
      finite_fixed_subgroup_rational 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) Fr hFr X hXC hXF
    exact ggKGEx_le_of_relIndex_dvd hp (by omega) hXp (Or.inr rfl) hidx (Subgroup.mem_zpowers r)
  ·
    let X : Subgroup (ModGL Tag.E8 (AlgebraicClosure K)) := Subgroup.zpowers r
    have hXC : X ≤ adjointGroup Tag.E8 (AlgebraicClosure K) := Subgroup.zpowers_le.2 hr
    have hXF : ∀ x ∈ X, Units.map (entrywiseHom Fr) x = x := by
      intro x hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [map_zpow, hrF]
    have hXfin : Finite X :=
      Nat.finite_of_card_ne_zero (by
        rw [Nat.card_zpowers]
        exact (Nat.pos_of_dvd_of_pos (orderOf_dvd_of_pow_eq_one hrp) hp.pos).ne')
    have hXp : IsPGroup p X := by
      rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hrp) with h | h
      · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
      · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
    haveI : Finite X := hXfin
    obtain ⟨hidx, -⟩ :=
      finite_fixed_subgroup_rational 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) Fr hFr X hXC hXF
    exact ggKGEx_le_of_relIndex_dvd hp (by omega) hXp (Or.inl rfl) hidx (Subgroup.mem_zpowers r)
  ·
    have hM : r ∈ adjointGroup Tag.F4 (AlgebraicClosure K) ⊓
        (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := ⟨hr, hrF⟩
    rwa [F4_frobenius_fixed_eq_map Fr hFr] at hM

private theorem ggKGEx_torus_pow_eq_image
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ} {E : Subgroup (adjointGroup τ K)}
    (hp : p.Prime) (hp3 : 3 ≤ p) (hτ6 : τ = .E6 → 5 ≤ p)
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) (F : ExcFrame τ K p E) :
    ∀ d ∈ F.D.torus, d ^ p = 1 →
      ∃ x ∈ E, d = F.D.g0⁻¹ *
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * F.D.g0 := by
  obtain ⟨Fr, hFr, hΦ⟩ := F.frob
  intro d hd hdp
  have hg0 : F.D.g0 ∈ adjointGroup τ (AlgebraicClosure K) := F.D.g0_mem
  have hdT : d ∈ torusGroup τ (AlgebraicClosure K) := (mem_twistedTorusOf.1 hd).1
  have hdG : d ∈ adjointGroup τ (AlgebraicClosure K) := torusGroup_le_adjointGroup' hdT
  set r : ModGL τ (AlgebraicClosure K) := F.D.g0 * d * F.D.g0⁻¹ with hrdef
  have hrG : r ∈ adjointGroup τ (AlgebraicClosure K) := mul_mem (mul_mem hg0 hdG) (inv_mem hg0)
  have hrF : Units.map (entrywiseHom Fr) r = r := by
    have hg0' : Units.map (entrywiseHom Fr) F.D.g0 = F.D.g0 * F.D.n := by
      rw [← hΦ, F.D.lang]
    have hd' : Units.map (entrywiseHom Fr) d = F.D.n⁻¹ * d * F.D.n := by
      have h2 : F.D.Φ d = F.D.n⁻¹ * d * F.D.n := by
        have h := (mem_twistedTorusOf.1 hd).2
        calc F.D.Φ d = F.D.n⁻¹ * (F.D.n * F.D.Φ d * F.D.n⁻¹) * F.D.n := by group
          _ = F.D.n⁻¹ * d * F.D.n := by rw [h]
      rwa [hΦ d] at h2
    calc Units.map (entrywiseHom Fr) r
        = Units.map (entrywiseHom Fr) (F.D.g0 * d * F.D.g0⁻¹) := by rw [hrdef]
      _ = Units.map (entrywiseHom Fr) F.D.g0 * Units.map (entrywiseHom Fr) d *
            (Units.map (entrywiseHom Fr) F.D.g0)⁻¹ := by rw [map_mul, map_mul, map_inv]
      _ = (F.D.g0 * F.D.n) * (F.D.n⁻¹ * d * F.D.n) * (F.D.g0 * F.D.n)⁻¹ := by rw [hg0', hd']
      _ = F.D.g0 * d * F.D.g0⁻¹ := by group
      _ = r := by rw [hrdef]
  have hrp : r ^ p = 1 := by rw [hrdef, conj_pow, hdp, mul_one, mul_inv_cancel]
  obtain ⟨x, hxG, hxr⟩ :=
    Subgroup.mem_map.1 (ggKGEx_mem_image_of_fixed_pow hp hp3 hτ6 hτ Fr hFr hrG hrF hrp)
  let x' : adjointGroup τ K := ⟨x, hxG⟩
  have hx'r : baseChangeGL (algebraMap K (AlgebraicClosure K)) (x' : ModGL τ K) = r := hxr
  refine ⟨x', ?_, ?_⟩
  · rw [F.mem_iff]
    refine ⟨?_, ?_⟩
    · apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
      rw [map_pow, map_one, hx'r, hrp]
    · rw [hx'r, hrdef]
      convert hd using 1
      group
  · rw [hx'r, hrdef]
    group

private theorem ggKGEx_mem_torus_of_weylTuple
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ} {E : Subgroup (adjointGroup τ K)}
    (F : ExcFrame τ K p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    {b : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (hact : weylTuple F.w (fun i => Units.map Fr.toMonoidHom (b i)) = b) :
    rootDiagUnit τ b ∈ F.D.torus := by
  refine (mem_twistedTorusOf.2 ⟨?_, ?_⟩)
  · obtain ⟨-, t, ht⟩ := exceptional_Lang_adjoint_diagonal_lift τ (AlgebraicClosure K) b
    rw [ht]
    refine Subgroup.list_prod_mem _ fun g hg => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg
    exact torusElt_mem_torusGroup j _
  · have h1 : Units.map (entrywiseHom Fr) (rootDiagUnit τ b) =
        rootDiagUnit τ (fun i => Units.map Fr.toMonoidHom (b i)) :=
      Units.ext (entrywise_rootDiag Fr b)
    rw [F.n_eq, hΦ (rootDiagUnit τ b), h1, canonicalRep_conj_rootDiagUnit, hact]

theorem ggKGEx_hact_w_one
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ} {E : Subgroup (adjointGroup τ K)}
    (F : ExcFrame τ K p E) {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (hwn : F.w = 1) (hpq : p ∣ Nat.card K - 1)
    {b : Fin τ.rank → (AlgebraicClosure K)ˣ} (hb : ∀ i, b i ^ p = 1) :
    weylTuple F.w (fun i => Units.map Fr.toMonoidHom (b i)) = b := by
  rw [hwn, weylTuple_one]
  funext i
  obtain ⟨k, hk⟩ := hpq
  have hpos : 0 < Nat.card K := by
    haveI : Nonempty K := ⟨0⟩
    exact Nat.card_pos
  have hq : Nat.card K = p * k + 1 := by omega
  rw [ggKGEx_units_map_fr_eq_pow Fr hFr (b i), hq, pow_add, pow_mul, hb i, one_pow, one_mul,
    pow_one]

theorem ggKGEx_hact_w_neg
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ} {E : Subgroup (adjointGroup τ K)}
    (F : ExcFrame τ K p E) {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (hτ : τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    (hlong : ExcIsLongest τ F.w) (hpq : p ∣ Nat.card K + 1)
    {b : Fin τ.rank → (AlgebraicClosure K)ˣ} (hb : ∀ i, b i ^ p = 1) :
    weylTuple F.w (fun i => Units.map Fr.toMonoidHom (b i)) = b := by
  rw [ggKGEx_eq_w0 τ (Or.inr hτ) hlong]
  rw [ggKGEx_weylTuple_w0_neg τ hτ]
  funext i
  obtain ⟨k, hk⟩ := hpq
  have hpos : 0 < Nat.card K := by
    haveI : Nonempty K := ⟨0⟩
    exact Nat.card_pos
  have hq : Nat.card K = p * k - 1 := by omega
  have hpk : 1 ≤ p * k := by omega
  rw [Pi.inv_apply, ggKGEx_units_map_fr_inv_eq_self Fr hFr (hb i) hq hpk]

theorem ggKGEx_hact_w_phi
    {K : Type} [Field K] [Finite K] {p : ℕ} {E : Subgroup (adjointGroup Tag.E6 K)}
    (F : ExcFrame Tag.E6 K p E) {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (hlong : ExcIsLongest Tag.E6 F.w)
    (hpq : p ∣ Nat.card K + 1) {b : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ}
    (hb : ∀ i, b i ^ p = 1) (hfix : ∀ i, b (ggKGEx_phi i) = b i) :
    weylTuple F.w (fun i => Units.map Fr.toMonoidHom (b i)) = b := by
  rw [ggKGEx_eq_w0 Tag.E6 (Or.inl rfl) hlong, ggKGEx_weylTuple_w0_phi]
  funext i
  obtain ⟨k, hk⟩ := hpq
  have hpos : 0 < Nat.card K := by
    haveI : Nonempty K := ⟨0⟩
    exact Nat.card_pos
  have hq : Nat.card K = p * k - 1 := by omega
  have hpk : 1 ≤ p * k := by omega
  rw [ggKGEx_units_map_fr_inv_eq_self Fr hFr (hb (ggKGEx_phi i)) hq hpk, hfix i]

theorem ggKGEx_familyCentralizer_le_torus
    {τ : Tag} {L : Type} [Field L] {ι : Type} (a : ι → Fin τ.rank → Lˣ)
    (hker : familyKernel a = ∅) (hstab : familyStabilizer a = {1}) :
    familyCentralizer τ L a ≤ torusGroup τ L := by
  intro g hg
  obtain ⟨w, hw, m, hm, rfl⟩ := familyCentralizer_le_mul τ L a hg
  rw [hstab] at hw
  rw [Set.mem_singleton_iff] at hw
  subst hw
  have hfg : familyGroup (K := L) a = torusGroup τ L := by
    rw [familyGroup, hker, rootSpan]
    simp
  rw [hfg] at hm
  rwa [canonicalRep_one, mul_one]

theorem ggKGEx_phi_fix
    {L : Type} [Field L] {b : Fin Tag.E6.rank → Lˣ}
    (h05 : b ⟨0, by decide⟩ = b ⟨5, by decide⟩)
    (h24 : b ⟨2, by decide⟩ = b ⟨4, by decide⟩) :
    ∀ i, b (ggKGEx_phi i) = b i := by
  have h0 : ggKGEx_phi (⟨0, by decide⟩ : Fin Tag.E6.rank) = ⟨5, by decide⟩ := by decide
  have h1 : ggKGEx_phi (⟨1, by decide⟩ : Fin Tag.E6.rank) = ⟨1, by decide⟩ := by decide
  have h2 : ggKGEx_phi (⟨2, by decide⟩ : Fin Tag.E6.rank) = ⟨4, by decide⟩ := by decide
  have h3 : ggKGEx_phi (⟨3, by decide⟩ : Fin Tag.E6.rank) = ⟨3, by decide⟩ := by decide
  have h4 : ggKGEx_phi (⟨4, by decide⟩ : Fin Tag.E6.rank) = ⟨2, by decide⟩ := by decide
  have h5 : ggKGEx_phi (⟨5, by decide⟩ : Fin Tag.E6.rank) = ⟨0, by decide⟩ := by decide
  intro i
  fin_cases i
  · rw [h0]; exact h05.symm
  · rw [h1]
  · rw [h2]; exact h24.symm
  · rw [h3]
  · rw [h4]; exact h24
  · rw [h5]; exact h05

theorem ggKGEx_exists_conj_of_hact
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)}
    (hp : p.Prime) (hp3 : 3 ≤ p) (hτ6 : τ = .E6 → 5 ≤ p)
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    (F : ExcFrame τ K p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    {b : Fin τ.rank → (AlgebraicClosure K)ˣ} (hb : ∀ j, b j ^ p = 1)
    (hact : weylTuple F.w (fun i => Units.map Fr.toMonoidHom (b i)) = b) :
    ∃ e ∈ E, rootDiagUnit τ b =
      F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) * F.D.g0 := by
  have hd : rootDiagUnit τ b ∈ F.D.torus :=
    ggKGEx_mem_torus_of_weylTuple F hΦ hact
  have hdp : (rootDiagUnit τ b) ^ p = 1 := by
    rw [rootDiagUnit_pow]
    have hbp : b ^ p = 1 := by
      funext j
      simp [Pi.pow_apply, hb j]
    rw [hbp, rootDiagUnit_one]
  exact ggKGEx_torus_pow_eq_image hp hp3 hτ6 hτ F (rootDiagUnit τ b) hd hdp

theorem ggKGExc_centralizer_eq
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) (hp : p.Prime)
    (hp3 : 3 ≤ p) (hτ6 : τ = .E6 → 5 ≤ p) (F : ExcFrame τ K p E)
    (hw : (p ∣ Nat.card K - 1 ∧ F.w = 1) ∨ (p ∣ Nat.card K + 1 ∧ ExcIsLongest τ F.w))
    (x : adjointGroup τ K) :
    x ∈ Subgroup.centralizer (E : Set (adjointGroup τ K)) ↔
      F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * F.D.g0 ∈
        F.D.torus := by
  obtain ⟨Fr, hFr, hΦ⟩ := F.frob
  have hBx_fix : Units.map (entrywiseHom Fr)
      (baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K)) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) :=
    units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr (x : ModGL τ K)
  constructor
  swap
  · intro hx
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hye : F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) *
        F.D.g0 ∈ F.D.torus := ((F.mem_iff e).1 he).2
    have hxT : F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) *
        F.D.g0 ∈ torusGroup τ (AlgebraicClosure K) := (mem_twistedTorusOf.1 hx).1
    have heT : F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) *
        F.D.g0 ∈ torusGroup τ (AlgebraicClosure K) := (mem_twistedTorusOf.1 hye).1
    have hcomm : (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) *
          F.D.g0) * (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) *
          F.D.g0) =
        (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) *
          F.D.g0) * (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) *
          F.D.g0) :=
      mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hxT)
        (torusGroup_le_diagonalGroup heT)
    apply Subtype.ext
    apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    have h3 : baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) *
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) *
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) := by
      calc baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) *
            baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K)
          = F.D.g0 * ((F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) *
              F.D.g0) * (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) *
              F.D.g0)) * F.D.g0⁻¹ := by group
        _ = F.D.g0 * ((F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) *
              F.D.g0) * (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) *
              F.D.g0)) * F.D.g0⁻¹ := by rw [hcomm]
        _ = baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) *
            baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) := by group
    exact h3.symm
  · intro hxcent
    rw [Subgroup.mem_centralizer_iff] at hxcent
    refine (mem_twistedTorusOf.2 ⟨?_, ?_⟩)
    · have hxG : F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) *
          F.D.g0 ∈ adjointGroup τ (AlgebraicClosure K) :=
        mul_mem (mul_mem (inv_mem F.D.g0_mem)
          (CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup (algebraMap K (AlgebraicClosure K))
            x.property)) F.D.g0_mem
      haveI : CharP (AlgebraicClosure K) 2 :=
        charP_of_injective_ringHom (algebraMap K (AlgebraicClosure K)).injective 2
      obtain ⟨ζu, hζu⟩ :=
        CFSG.LieType.SeitzGeneration.exists_primitiveRoot_units (L := AlgebraicClosure K) (ℓ := 2)
          (by norm_num) hp (by omega)
      let ζ : AlgebraicClosure K := ζu
      have hζ : IsPrimitiveRoot ζ p := IsPrimitiveRoot.coe_units_iff.2 hζu
      have hmem_of : ∀ {ι : Type} (a : ι → Fin τ.rank → (AlgebraicClosure K)ˣ),
          (∀ i, ∃ e ∈ E, rootDiagUnit τ (a i) =
            F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) * F.D.g0) →
          F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * F.D.g0 ∈
            familyCentralizer τ (AlgebraicClosure K) a := by
        intro ι a hroot
        rw [mem_familyCentralizer]
        refine ⟨hxG, fun i => ?_⟩
        obtain ⟨e, heE, heq⟩ := hroot i
        have hxe : e * x = x * e := hxcent e heE
        have hcomm : (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) *
              F.D.g0) * (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) *
              F.D.g0) =
            (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) *
              F.D.g0) * (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) *
              F.D.g0) := by
          calc (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) * F.D.g0) *
                (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * F.D.g0)
              = F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
                  ((e * x : adjointGroup τ K) : ModGL τ K) * F.D.g0 := by
                rw [Subgroup.coe_mul, map_mul]; group
            _ = F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
                  ((x * e : adjointGroup τ K) : ModGL τ K) * F.D.g0 := by rw [hxe]
            _ = (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * F.D.g0) *
                (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) * F.D.g0) := by
                rw [Subgroup.coe_mul, map_mul]; group
        rw [heq, hcomm]
        group
      rcases hw with ⟨hpq, hwn⟩ | ⟨hpq, hlong⟩
      · let a : {b : Fin τ.rank → (AlgebraicClosure K)ˣ // ∀ j, b j ^ p = 1} →
            Fin τ.rank → (AlgebraicClosure K)ˣ := Subtype.val
        have hall : ∀ b : Fin τ.rank → (AlgebraicClosure K)ˣ, (∀ j, b j ^ p = 1) →
            ∃ i, a i = b := fun b hb => ⟨⟨b, hb⟩, rfl⟩
        have hker : familyKernel a = ∅ :=
          ggKGExc_familyKernel_allPTorsion (ζ := ζ) hp hp3 hζ a hall
        have hstab : familyStabilizer a = {1} :=
          ggKGExc_familyStabilizer_allPTorsion (ζ := ζ) hτ hp hp3 hζ a hall
        exact ggKGEx_familyCentralizer_le_torus a hker hstab
          (hmem_of a fun i => ggKGEx_exists_conj_of_hact hp hp3 hτ6 hτ F hΦ i.property
            (ggKGEx_hact_w_one F hFr hwn hpq i.property))
      · by_cases hE6 : τ = .E6
        · subst hE6
          let a : {b : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ //
              (∀ j, b j ^ p = 1) ∧ ∀ i, b (ggKGEx_phi i) = b i} →
              Fin Tag.E6.rank → (AlgebraicClosure K)ˣ := Subtype.val
          have hall : ∀ b : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ, (∀ j, b j ^ p = 1) →
              b ⟨0, by decide⟩ = b ⟨5, by decide⟩ →
              b ⟨2, by decide⟩ = b ⟨4, by decide⟩ → ∃ i, a i = b := by
            intro b hb h05 h24
            exact ⟨⟨b, hb, ggKGEx_phi_fix h05 h24⟩, rfl⟩
          have hker : familyKernel a = ∅ := ggKGExc_familyKernel_phi (ζ := ζ) hp (hτ6 rfl) hζ a hall
          have hstab : familyStabilizer a = {1} :=
            ggKGExc_familyStabilizer_phi (ζ := ζ) hp (hτ6 rfl) hζ a hall
          exact ggKGEx_familyCentralizer_le_torus a hker hstab
            (hmem_of a fun i =>
              ggKGEx_exists_conj_of_hact hp hp3 hτ6 hτ F hΦ i.property.1
                (ggKGEx_hact_w_phi F hFr hlong hpq i.property.1 i.property.2))
        · have hτ' : τ = .E7 ∨ τ = .E8 ∨ τ = .F4 := by
            rcases hτ with h | h | h | h
            · exact absurd h hE6
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
          let a : {b : Fin τ.rank → (AlgebraicClosure K)ˣ // ∀ j, b j ^ p = 1} →
              Fin τ.rank → (AlgebraicClosure K)ˣ := Subtype.val
          have hall : ∀ b : Fin τ.rank → (AlgebraicClosure K)ˣ, (∀ j, b j ^ p = 1) →
              ∃ i, a i = b := fun b hb => ⟨⟨b, hb⟩, rfl⟩
          have hker : familyKernel a = ∅ :=
            ggKGExc_familyKernel_allPTorsion (ζ := ζ) hp hp3 hζ a hall
          have hstab : familyStabilizer a = {1} :=
            ggKGExc_familyStabilizer_allPTorsion (ζ := ζ) hτ hp hp3 hζ a hall
          exact ggKGEx_familyCentralizer_le_torus a hker hstab
            (hmem_of a fun i => ggKGEx_exists_conj_of_hact hp hp3 hτ6 hτ F hΦ i.property
              (ggKGEx_hact_w_neg F hFr hτ' hlong hpq i.property))
    · have hΦBx : F.D.Φ (baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K)) =
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) := by
        rw [hΦ, hBx_fix]
      rw [show F.D.Φ (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) *
              F.D.g0) =
            (F.D.Φ F.D.g0)⁻¹ *
              F.D.Φ (baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K)) *
              F.D.Φ F.D.g0 from by simp only [map_mul, map_inv]]
      rw [F.D.lang, hΦBx]
      group

end CFSG.StandardType
