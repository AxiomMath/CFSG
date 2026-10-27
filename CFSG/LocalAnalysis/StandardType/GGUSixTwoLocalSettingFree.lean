module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoLocalSetting

public section

namespace CFSG.StandardType.USixTwo

open CFSG.Assembly CFSG.Open
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

variable {G : Type*} [Group G] {K : Type} [Field K]

namespace LocalSetting

variable {ω : K} {hω : ω ^ 2 + ω + 1 = 0} {b : G} {L : Subgroup G}
  {φ : L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))} {Bs : Subgroup G}

theorem normal_and_index_dvd_six [Finite G] [Finite K] (hS : LocalSetting hω b L φ Bs) :
    (((Subgroup.centralizer {b} ⊓ Subgroup.centralizer (L : Set G)) ⊔ L).subgroupOf
      (Subgroup.centralizer {b})).Normal ∧
    (((Subgroup.centralizer {b} ⊓ Subgroup.centralizer (L : Set G)) ⊔ L).subgroupOf
      (Subgroup.centralizer {b})).index ∣ 6 := by
  classical
  let Cb : Subgroup G := Subgroup.centralizer ({b} : Set G)
  let U := LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
  let Inn : Subgroup (MulAut U) := (MulAut.conj : U →* MulAut U).range
  let ψ : ↥Cb →* MulAut U :=
    (MulAut.congr φ).toMonoidHom.comp
      ((Subgroup.normalizerMonoidHom L).comp
        (Subgroup.inclusion (centralizer_b_le_normalizer_L hS)))
  have hψ : ∀ g : ↥Cb, ψ g = inducedAut hS g.1 (centralizer_b_le_normalizer_L hS g.2) := by
    intro g
    ext u
    obtain ⟨x, rfl⟩ := φ.surjective u
    rw [inducedAut_apply]
    change ((MulAut.congr φ) (Subgroup.normalizerMonoidHom L
      ((Subgroup.inclusion (centralizer_b_le_normalizer_L hS)) g))) (φ ⟨x, x.2⟩) =
      φ ⟨g.1 * x.1 * g.1⁻¹, _⟩
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    congr 1
  haveI hInn : Inn.Normal :=
    ⟨fun _ ⟨u, hu⟩ σ => ⟨σ u, by
      rw [← hu]
      ext v
      simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]⟩⟩
  have heq : ((Subgroup.centralizer {b} ⊓ Subgroup.centralizer (L : Set G)) ⊔ L).subgroupOf Cb =
      Inn.comap ψ := by
    apply le_antisymm
    · rw [Subgroup.subgroupOf_sup (inf_le_left : Cb ⊓ Subgroup.centralizer (L : Set G) ≤ Cb)
        hS.le_centralizer]
      refine sup_le ?_ ?_
      · intro g hg
        have hgL : (g : G) ∈ Subgroup.centralizer (L : Set G) :=
          (Subgroup.mem_subgroupOf.mp hg).2
        refine ⟨1, ?_⟩
        rw [map_one, hψ]
        ext u
        obtain ⟨x, rfl⟩ := φ.surjective u
        rw [inducedAut_apply, MulAut.one_apply]
        congr 1
        apply Subtype.ext
        change (x : G) = g * x * (g : G)⁻¹
        rw [← Subgroup.mem_centralizer_iff.mp hgL x x.2]
        group
      · intro g hg
        have hgL : (g : G) ∈ L := Subgroup.mem_subgroupOf.mp hg
        refine ⟨φ ⟨g, hgL⟩, ?_⟩
        rw [hψ, inducedAut_of_mem_L hS hgL]
    · intro g hg
      obtain ⟨u, hu⟩ := hg
      let l : L := φ.symm u
      have hlL : (l : G) ∈ L := l.2
      have hlu : φ l = u := φ.apply_symm_apply u
      have hact : ∀ x ∈ L, (g : G) * x * (g : G)⁻¹ = (l : G) * x * (l : G)⁻¹ := by
        intro x hx
        have h1 := congrArg (fun α : MulAut U => α (φ ⟨x, hx⟩)) hu
        rw [hψ, inducedAut_apply, MulAut.conj_apply, ← hlu, ← map_inv, ← map_mul,
          ← map_mul] at h1
        have h2 := congrArg Subtype.val (φ.injective h1)
        simpa using h2.symm
      have hglCL : (g : G) * (l : G)⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hlyL : (l : G)⁻¹ * y * l ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hlL) hy) hlL
        have hgy : (g : G) * ((l : G)⁻¹ * y * l) * (g : G)⁻¹ = y := by
          rw [hact _ hlyL]
          group
        calc y * ((g : G) * (l : G)⁻¹) =
            ((g : G) * ((l : G)⁻¹ * y * l) * (g : G)⁻¹) * ((g : G) * (l : G)⁻¹) := by
              rw [hgy]
          _ = (g : G) * (l : G)⁻¹ * y := by group
      have hglR : (g : G) * (l : G)⁻¹ ∈
          Subgroup.centralizer {b} ⊓ Subgroup.centralizer (L : Set G) :=
        ⟨Subgroup.mul_mem _ g.2 (hS.le_centralizer (L.inv_mem hlL)), hglCL⟩
      rw [Subgroup.mem_subgroupOf, show (g : G) = ((g : G) * (l : G)⁻¹) * l by group]
      exact Subgroup.mul_mem_sup hglR hlL
  rw [heq]
  refine ⟨hInn.comap ψ, ?_⟩
  rw [Subgroup.index_comap]
  exact (Subgroup.relIndex_dvd_index_of_normal Inn ψ.range).trans
    (index_range_conj_dvd_six hS.card_K)

theorem relPPrimeCore_le_centralizer_and_odd_index [Finite G] [Finite K]
    (hS : LocalSetting hω b L φ Bs) :
    relPPrimeCore 3 (Subgroup.centralizer {b}) ≤ Subgroup.centralizer (Bs : Set G) ∧
      ¬ 2 ∣ ((relPPrimeCore 3 (Subgroup.centralizer {b})).subgroupOf
        (Subgroup.centralizer (Bs : Set G))).index := by
  classical
  let Cb : Subgroup G := Subgroup.centralizer ({b} : Set G)
  let CL : Subgroup G := Subgroup.centralizer (L : Set G)
  let R : Subgroup G := Cb ⊓ CL
  let O : Subgroup G := relPPrimeCore 3 Cb
  let P : Subgroup G := Subgroup.zpowers b
  let Cbs : Subgroup G := Subgroup.centralizer (Bs : Set G)
  have hOleCb : O ≤ Cb := relPPrimeCore_le Cb
  have hOleR : O ≤ R := le_inf hOleCb (relPPrimeCore_le_centralizer hS)
  have hPR : P ≤ R :=
    Subgroup.zpowers_le.mpr ⟨b_mem_centralizer_b hS, b_mem_centralizer_L hS⟩
  have hRsup : R = O ⊔ P := centralizer_inf_eq hS
  refine ⟨hOleR.trans (centralizer_b_inf_le_centralizer_Bs hS), ?_⟩
  let X : Sylow 2 ↥Cbs := Classical.choice (inferInstance : Nonempty (Sylow 2 ↥Cbs))
  have hXle : (X : Subgroup ↥Cbs) ≤ O.subgroupOf Cbs := by
    intro t ht
    have hX2 : IsPGroup 2 ↥(X : Subgroup ↥Cbs) := X.isPGroup'
    obtain ⟨n, hn⟩ := hX2 ⟨t, ht⟩
    have ht_ord : orderOf (t : ↥Cbs) ∣ 2 ^ n := by
      have h := (orderOf_dvd_iff_pow_eq_one).mpr hn
      rwa [Subgroup.orderOf_mk] at h
    have ht3 : (t : G) ^ 3 ∈ R := pow_three_mem_centralizer_b_inf hS t.2
    have htR : (t : G) ∈ R := by
      have hcop : Nat.Coprime (orderOf (t : ↥Cbs)) 3 :=
        (((by norm_num : Nat.Coprime 3 2).pow_right n).coprime_dvd_right ht_ord).symm
      have hcop' : Nat.Coprime (orderOf (t : G)) 3 := by
        simpa using hcop
      have hle : Subgroup.zpowers ((t : G) ^ 3) ≤ Subgroup.zpowers (t : G) :=
        Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩) 3)
      have hzeq : Subgroup.zpowers ((t : G) ^ 3) = Subgroup.zpowers (t : G) :=
        Subgroup.eq_of_le_of_card_ge hle (by
          rw [Nat.card_zpowers, Nat.card_zpowers, Nat.Coprime.orderOf_pow hcop'])
      have hmem : (t : G) ∈ Subgroup.zpowers ((t : G) ^ 3) := by
        rw [hzeq]
        exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
      exact Subgroup.zpowers_le.mpr ht3 hmem
    haveI : (O.subgroupOf R).Normal := by
      refine ⟨fun x hx g => ?_⟩
      have hxO : (x : G) ∈ O := Subgroup.mem_subgroupOf.mp hx
      refine Subgroup.mem_subgroupOf.mpr ?_
      have hconj : (⟨(g : G), g.2.1⟩ : ↥Cb) * ⟨x, x.2.1⟩ * (⟨(g : G), g.2.1⟩ : ↥Cb)⁻¹ ∈
          O.subgroupOf Cb :=
        (relPPrimeCore_normal Nat.prime_three Cb).conj_mem ⟨x, x.2.1⟩ hxO ⟨(g : G), g.2.1⟩
      exact Subgroup.mem_subgroupOf.mp hconj
    have ht_sup' : (⟨(t : G), htR⟩ : ↥R) ∈ O.subgroupOf R ⊔ P.subgroupOf R := by
      rw [← Subgroup.subgroupOf_sup hOleR hPR]
      exact Subgroup.mem_subgroupOf.mpr (hRsup ▸ htR)
    obtain ⟨o, hoO, p, hpP, hop⟩ := Subgroup.mem_sup_of_normal_left.mp ht_sup'
    let q : ↥R →* (↥R ⧸ O.subgroupOf R) := QuotientGroup.mk' (O.subgroupOf R)
    have hq : q ⟨(t : G), htR⟩ = q p := by
      rw [← hop, map_mul, show q o = 1 from (QuotientGroup.eq_one_iff o).mpr hoO, one_mul]
    have hp3 : ((p : ↥R) : G) ∈ P := Subgroup.mem_subgroupOf.mp hpP
    obtain ⟨m, hm⟩ := isPGroup_zpowers_b hS ⟨(p : G), hp3⟩
    have hp_ord : orderOf (p : ↥R) ∣ 3 ^ m := by
      have h : orderOf (⟨(p : G), hp3⟩ : ↥P) ∣ 3 ^ m :=
        (orderOf_dvd_iff_pow_eq_one).mpr hm
      rw [Subgroup.orderOf_mk] at h
      simpa using h
    have h2n : orderOf (q ⟨(t : G), htR⟩) ∣ 2 ^ n := by
      have h1 : orderOf (q ⟨(t : G), htR⟩) ∣ orderOf (⟨(t : G), htR⟩ : ↥R) :=
        orderOf_map_dvd q _
      rw [Subgroup.orderOf_mk] at h1
      exact h1.trans (by simpa using ht_ord)
    have h3m : orderOf (q ⟨(t : G), htR⟩) ∣ 3 ^ m := by
      rw [hq]
      exact (orderOf_map_dvd q p).trans hp_ord
    have hcop : Nat.Coprime (2 ^ n) (3 ^ m) :=
      Nat.coprime_pow_primes n m Nat.prime_two Nat.prime_three (by norm_num)
    have h1 : orderOf (q ⟨(t : G), htR⟩) = 1 := Nat.eq_one_of_dvd_coprimes hcop h2n h3m
    have hq1 : q ⟨(t : G), htR⟩ = 1 := orderOf_eq_one_iff.mp h1
    have htO : (t : G) ∈ O := by
      have hmem : (⟨(t : G), htR⟩ : ↥R) ∈ O.subgroupOf R := (QuotientGroup.eq_one_iff _).mp hq1
      exact Subgroup.mem_subgroupOf.mp hmem
    exact Subgroup.mem_subgroupOf.mpr htO
  intro h2
  exact X.not_dvd_index (h2.trans (Subgroup.index_dvd_of_le hXle))

open scoped Pointwise in
theorem mem_sup_of_mem_sup_centralizer_of_sq_eq_one [Finite G] [Finite K]
    (hS : LocalSetting hω b L φ Bs) {y : G}
    (hy : y ∈ (L ⊓ Subgroup.normalizer (Bs : Set G)) ⊔ Subgroup.centralizer (Bs : Set G))
    (hy2 : y ^ 2 = 1) :
    y ∈ L ⊔ (Subgroup.centralizer {b} ⊓ Subgroup.centralizer (L : Set G)) := by
  have hle : Subgroup.centralizer (Bs : Set G) ≤
      Subgroup.normalizer ((L ⊓ Subgroup.normalizer (Bs : Set G) : Subgroup G) : Set G) := by
    intro c hc
    have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
      centralizer_b_le_normalizer_L hS (centralizer_Bs_le_centralizer_b hS hc)
    have hcB : c ∈ Subgroup.normalizer (Bs : Set G) :=
      Subgroup.centralizer_le_normalizer (Bs : Set G) hc
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨hzL, hzN⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hcN z).mp hzL,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hcB hzN) (Subgroup.inv_mem _ hcB)⟩
    · rintro ⟨hzL, hzN⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp hcN z).mpr hzL, ?_⟩
      have h := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hcB) hzN) hcB
      simpa [mul_assoc] using h
  have hy' : y ∈ ((L ⊓ Subgroup.normalizer (Bs : Set G) : Subgroup G) : Set G) *
      (Subgroup.centralizer (Bs : Set G) : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hle]
    exact hy
  obtain ⟨l, hl, c, hc, rfl⟩ := hy'
  beta_reduce at hy2 ⊢
  have hlL : l ∈ L := (Subgroup.mem_inf.mp hl).1
  have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
    centralizer_b_le_normalizer_L hS (centralizer_Bs_le_centralizer_b hS hc)
  have hc2N : c ^ 2 ∈ Subgroup.normalizer (L : Set G) := Subgroup.pow_mem _ hcN 2
  have hy3 : l * c = (l * (c * l * c⁻¹) * (c ^ 2 * l * (c ^ 2)⁻¹)) * c ^ 3 := by
    calc l * c = (l * c) ^ 3 := by rw [pow_succ, hy2, one_mul]
      _ = (l * c) * (l * c) * (l * c) := by rw [pow_succ, pow_two]
      _ = _ := by group
  rw [hy3]
  refine Subgroup.mul_mem_sup (L.mul_mem (L.mul_mem hlL ?_) ?_)
    (pow_three_mem_centralizer_b_inf hS hc)
  · exact (Subgroup.mem_normalizer_iff.mp hcN l).mp hlL
  · exact (Subgroup.mem_normalizer_iff.mp hc2N l).mp hlL

end LocalSetting

end CFSG.StandardType.USixTwo

end
