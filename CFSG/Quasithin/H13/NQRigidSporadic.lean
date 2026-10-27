module

public import CFSG.Quasithin.H13.NQRigidInputs
public import CFSG.Quasithin.H13.NQCatExcludesJ4
public import CFSG.Quasithin.SteinbergBTTitsPermutableSylowCyclic
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj exists_conj_eq_of_isSylowOf)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Blueprint
open scoped Pointwise

theorem map_mul_comm_of_mul_comm {K S : Type*} [Group K] [Group S] (σ : K →* S)
    {P B : Subgroup K} (hPB : (P : Set K) * (B : Set K) = (B : Set K) * (P : Set K)) :
    ((P.map σ : Subgroup S) : Set S) * ((B.map σ : Subgroup S) : Set S) =
      ((B.map σ : Subgroup S) : Set S) * ((P.map σ : Subgroup S) : Set S) := by
  rw [coe_map, coe_map, ← Set.image_mul, hPB, Set.image_mul]

theorem injective_of_not_dvd_card_ker {K S : Type*} [Group K] [Group S] [Finite K] {p : ℕ}
    (hp : p.Prime) (σ : K →* S) (hker : ¬ p ∣ Nat.card σ.ker) {P : Subgroup K}
    (hP : IsPGroup p P) : Function.Injective (σ.comp P.subtype) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [injective_iff_map_eq_one]
  intro y hy
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) y
  have hy' : (y : K) ∈ σ.ker := hy
  have hk' : orderOf (y : K) = p ^ k := by rw [Subgroup.orderOf_coe, hk]
  exact Subtype.ext (NQTerm.eq_one_of_orderOf_dvd_prime_pow hp hker hy' hk'.dvd)

theorem noncyclic_prime_Sylow_product_excludes_Tits_quotient
    {K S : Type} [Group K] [Group S] [Finite K] [Finite S] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (σ : K →* S) (hσ : Function.Surjective σ) (hker : ¬ p ∣ Nat.card σ.ker) (P : Subgroup K)
    (hPp : IsPGroup p P) (hPc : ¬ IsCyclic P) (B : Sylow 2 K)
    (hPB : (P : Set K) * ((B : Subgroup K) : Set K) = ((B : Subgroup K) : Set K) * (P : Set K)) :
    ¬ ReeTitsModel S .Tits 2 1 := by
  classical
  intro hT
  obtain ⟨ψ⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv S 2 1 hT
  set φ : K →* CFSG.Sporadic.Schreier.Tits.titsD := ψ.toMonoidHom.comp σ with hφ
  have hφs : Function.Surjective φ := ψ.surjective.comp hσ
  have hUc : ((B.mapSurjective hφs : Sylow 2 CFSG.Sporadic.Schreier.Tits.titsD) :
      Subgroup CFSG.Sporadic.Schreier.Tits.titsD) = (B : Subgroup K).map φ :=
    Sylow.coe_mapSurjective _ _
  have hAU : ((P.map φ : Subgroup CFSG.Sporadic.Schreier.Tits.titsD) :
      Set CFSG.Sporadic.Schreier.Tits.titsD) *
      (((B.mapSurjective hφs : Sylow 2 CFSG.Sporadic.Schreier.Tits.titsD) :
        Subgroup CFSG.Sporadic.Schreier.Tits.titsD) : Set CFSG.Sporadic.Schreier.Tits.titsD) =
      (((B.mapSurjective hφs : Sylow 2 CFSG.Sporadic.Schreier.Tits.titsD) :
        Subgroup CFSG.Sporadic.Schreier.Tits.titsD) : Set CFSG.Sporadic.Schreier.Tits.titsD) *
        ((P.map φ : Subgroup CFSG.Sporadic.Schreier.Tits.titsD) :
          Set CFSG.Sporadic.Schreier.Tits.titsD) := by
    rw [hUc]
    exact map_mul_comm_of_mul_comm φ hPB
  have hcyc := (SteinbergBT.tits_common_sylow_and_prime_subgroup_normalizer_action_is_cyclic hp
    hp2 (B.mapSurjective hφs) (P.map φ) (hPp.map φ) hAU).2.2.1
  have hkerφ : φ.ker = σ.ker := by
    ext k
    simp only [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have hinj : Function.Injective (φ.comp P.subtype) :=
    injective_of_not_dvd_card_ker hp φ (by rw [hkerφ]; exact hker) hPp
  have hrange : (φ.comp P.subtype).range = P.map φ := by
    rw [MonoidHom.range_comp, range_subtype]
  let e : P ≃* P.map φ := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  exact hPc (isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective)

theorem stmtTitsSylowProduct_holds :
    StmtTitsSylowProduct :=
  fun _ _ _ _ _ _ _ hp hp2 σ hσ hker P hPp hPc B hPB =>
    noncyclic_prime_Sylow_product_excludes_Tits_quotient hp hp2 σ hσ hker P hPp hPc B hPB

theorem irreducible_original_prime_witness_excludes_J4_single_component_quotient
    {H : Type} [Group H] [Finite H] {D K X : Subgroup H} (hDK : D ≤ normalizer (K : Set H))
    (hXD : X ≤ D) (hXn : (X.subgroupOf D).Normal) (hXK : X ≤ K) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hW : p ^ 2 ≤ Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)))
    (hirr : IsFrattiniIrreducible X D) (hZ : ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K)))
    {P B : Subgroup H} (hP : IsSylowOf p P X) (hB : IsSylowOf 2 B K)
    (hPB : (P : Set H) * (B : Set H) = (B : Set H) * (P : Set H)) :
    IsEmpty ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K) ≃* NativeSporadic.J4) := by
  refine ⟨fun ψ₀ => ?_⟩
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  have hPX : P ≤ X := hP.le
  have hPK : P ≤ K := hPX.trans hXK
  have hBK : B ≤ K := hB.le
  have hDX : D ≤ normalizer (X : Set H) := (normal_subgroupOf_iff_le_normalizer hXD).mp hXn
  set S := (K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K) with hSdef
  set σ : K →* S := (QuotientGroup.mk' (center (K ⧸ CFSG.pCore 2 K))).comp
    (QuotientGroup.mk' (CFSG.pCore 2 K)) with hσ
  have hσs : Function.Surjective σ := fun z => by
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (center (K ⧸ CFSG.pCore 2 K)) z
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 K) j
    exact ⟨k, rfl⟩
  have hP'p : IsPGroup p (P.subgroupOf K) := by
    rw [← comap_subtype]
    exact hP.isPGroup.comap_subtype
  have hσinj : Function.Injective (σ.comp (P.subgroupOf K).subtype) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP'p) y
    have hk' : orderOf (y : K) ∣ p ^ k := (by rw [Subgroup.orderOf_coe, hk] :
      orderOf (y : K) = p ^ k).dvd
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 K) (y : K) ∈ center (K ⧸ CFSG.pCore 2 K) :=
      (QuotientGroup.eq_one_iff _).mp hy
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 K) (y : K) = 1 :=
      NQTerm.eq_one_of_orderOf_dvd_prime_pow hp hZ h1 ((orderOf_map_dvd _ _).trans hk')
    have h3 : (y : K) ∈ CFSG.pCore 2 K := (QuotientGroup.eq_one_iff _).mp h2
    have h4 : ¬ p ∣ Nat.card (CFSG.pCore 2 K) := by
      obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 K)).exists_card_eq
      rw [hm]
      intro hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
    exact Subtype.ext (NQTerm.eq_one_of_orderOf_dvd_prime_pow hp h4 h3 hk')
  set A := (P.subgroupOf K).map σ with hA
  have hrange : (σ.comp (P.subgroupOf K).subtype).range = A := by
    rw [MonoidHom.range_comp, range_subtype]
  let eA : P.subgroupOf K ≃* A :=
    (MonoidHom.ofInjective hσinj).trans (MulEquiv.subgroupCongr hrange)
  have hAp : IsPGroup p A := hP'p.map σ
  obtain ⟨B₁, hB₁⟩ := hB.exists_sylow_eq_subgroupOf
  have hUc : ((B₁.mapSurjective hσs : Sylow 2 S) : Subgroup S) = (B.subgroupOf K).map σ := by
    rw [Sylow.coe_mapSurjective, hB₁]
  have hPBK : ((P.subgroupOf K : Subgroup K) : Set K) * ((B.subgroupOf K : Subgroup K) : Set K) =
      ((B.subgroupOf K : Subgroup K) : Set K) * ((P.subgroupOf K : Subgroup K) : Set K) := by
    apply Set.image_injective.mpr K.subtype_injective
    rw [Set.image_mul, Set.image_mul, ← coe_map, ← coe_map, subgroupOf_map_subtype,
      subgroupOf_map_subtype, inf_of_le_left hPK, inf_of_le_left hBK, hPB]
  have hAU : (A : Set S) * (((B₁.mapSurjective hσs : Sylow 2 S) : Subgroup S) : Set S) =
      (((B₁.mapSurjective hσs : Sylow 2 S) : Subgroup S) : Set S) * (A : Set S) := by
    rw [hUc]
    exact map_mul_comm_of_mul_comm σ hPBK
  set W := (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X) with hWdef
  set ι : X →* W := (QuotientGroup.mk' (frattini (X ⧸ CFSG.pCore 2 X))).comp
    (QuotientGroup.mk' (CFSG.pCore 2 X)) with hι
  have hWsurj : Function.Surjective (ι.comp (P.subgroupOf X).subtype) :=
    NQCat.surjective_frattiniQuotient_of_isSylowOf hXA hP
  obtain ⟨-, -, hWpow, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hXA
  have hpp : p < p ^ 2 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  have ePX : P.subgroupOf K ≃* P.subgroupOf X :=
    (subgroupOfEquivOfLe hPK).trans (subgroupOfEquivOfLe hPX).symm
  have hPnc : ¬ IsCyclic (P.subgroupOf X) := by
    intro hc
    have hWc : IsCyclic W := isCyclic_of_surjective _ hWsurj
    obtain ⟨w, hw⟩ := hWc.exists_generator
    have h1 : Nat.card W ≤ p := by
      rw [← orderOf_eq_card_of_forall_mem_zpowers hw]
      exact orderOf_le_of_pow_eq_one hp.pos (hWpow w)
    exact absurd (hW.trans h1) (not_le.mpr hpp)
  have hAnc : ¬ IsCyclic A := by
    intro hc
    apply hPnc
    have : IsCyclic (P.subgroupOf K) :=
      isCyclic_of_surjective eA.symm.toMonoidHom eA.symm.surjective
    exact isCyclic_of_surjective ePX.toMonoidHom ePX.surjective
  obtain ⟨hp11, hAcard, C, hCA, hCcard, hCinv⟩ :=
    NQCat.J4_line_of_mulEquiv ψ₀ hp hp5 A hAp hAnc (B₁.mapSurjective hσs) hAU
  let τ : normalizer (K : Set H) →* MulAut S :=
    (CFSG.SectionRank.Ccomm.autQuotient (center (K ⧸ CFSG.pCore 2 K))).comp
      ((CFSG.SectionRank.Ccomm.autQuotient (CFSG.pCore 2 K)).comp K.normalizerMonoidHom)
  have hτ : ∀ (n : normalizer (K : Set H)) (k : K), τ n (σ k) = σ (K.normalizerMonoidHom n k) :=
    fun _ _ => rfl
  have hCn : ∀ n : normalizer (K : Set H), (n : H) ∈ normalizer (P : Set H) →
      C.map (τ n).toMonoidHom = C := by
    intro n hnP
    apply hCinv
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      refine ⟨K.normalizerMonoidHom n k, ?_, (hτ n k).symm⟩
      exact mem_subgroupOf.mpr ((mem_normalizer_iff.mp hnP k).mp (mem_subgroupOf.mp hk))
    · exact (card_map_of_injective (f := (τ n).toMonoidHom) (τ n).injective).symm.le
  set PC : Subgroup H := ((C.comap σ) ⊓ P.subgroupOf K).map K.subtype with hPC
  have hPCP : PC ≤ P := by
    rintro _ ⟨k, hk, rfl⟩
    exact mem_subgroupOf.mp (mem_inf.mp hk).2
  have hPCn : ∀ n : normalizer (K : Set H), (n : H) ∈ normalizer (P : Set H) →
      ∀ z ∈ PC, (n : H) * z * (n : H)⁻¹ ∈ PC := by
    intro n hnP z hz
    obtain ⟨k, hk, rfl⟩ := hz
    obtain ⟨hkC, hkP⟩ := mem_inf.mp hk
    refine ⟨K.normalizerMonoidHom n k, mem_inf.mpr ⟨?_, ?_⟩, rfl⟩
    · rw [mem_comap, ← hτ]
      have h1 : τ n (σ k) ∈ C.map (τ n).toMonoidHom := ⟨σ k, hkC, rfl⟩
      rwa [hCn n hnP] at h1
    · exact mem_subgroupOf.mpr ((mem_normalizer_iff.mp hnP k).mp (mem_subgroupOf.mp hkP))
  have hPCcard : Nat.card PC ≤ p := by
    have h1 : Nat.card PC = Nat.card ((C.comap σ) ⊓ P.subgroupOf K : Subgroup K) :=
      card_map_of_injective K.subtype_injective
    have h2 : Nat.card ((C.comap σ) ⊓ P.subgroupOf K : Subgroup K) ≤ Nat.card C := by
      refine Nat.card_le_card_of_injective
        (fun k : ((C.comap σ) ⊓ P.subgroupOf K : Subgroup K) => (⟨σ k, (mem_inf.mp k.2).1⟩ : C))
        fun a b hab => ?_
      have hab' : σ (a : K) = σ (b : K) := congrArg Subtype.val hab
      have h3 := hσinj (a₁ := ⟨a, (mem_inf.mp a.2).2⟩) (a₂ := ⟨b, (mem_inf.mp b.2).2⟩) hab'
      have h4 := congrArg (fun x : (P.subgroupOf K) => (x : K)) h3
      exact Subtype.ext h4
    rw [h1]
    omega
  have hPC1 : PC ≠ ⊥ := by
    have hCnt : Nontrivial C := by
      rw [← Finite.one_lt_card_iff_nontrivial, hCcard]
      norm_num
    obtain ⟨c, hc1⟩ := exists_ne (1 : C)
    obtain ⟨k, hkP, hkc⟩ := hCA c.2
    intro hbot
    have hk : (k : H) ∈ PC := ⟨k, mem_inf.mpr ⟨by rw [mem_comap, hkc]; exact c.2, hkP⟩, rfl⟩
    rw [hbot, mem_bot] at hk
    apply hc1
    apply Subtype.ext
    rw [← hkc, show k = 1 from Subtype.ext hk, map_one]
    rfl
  have hcardP : Nat.card (P.subgroupOf X) = p ^ 2 := by
    rw [← Nat.card_congr ePX.toEquiv, Nat.card_congr eA.toEquiv, hAcard, hp11]
  have hιbij : Function.Bijective (ι.comp (P.subgroupOf X).subtype) :=
    hWsurj.bijective_of_nat_card_le (by rw [hcardP]; exact hW)
  set Y : Subgroup W := ((PC.subgroupOf X).map ι) with hY
  have hYW : ∀ z : X, (z : H) ∈ PC → ι z ∈ Y := fun z hz => ⟨z, mem_subgroupOf.mpr hz, rfl⟩
  have hY1 : Y ≠ ⊥ := by
    intro hbot
    apply hPC1
    rw [eq_bot_iff]
    intro z hz
    have hzX : z ∈ X := hPX (hPCP hz)
    have h1 : ι ⟨z, hzX⟩ ∈ Y := hYW ⟨z, hzX⟩ hz
    rw [hbot, mem_bot] at h1
    have h2 : (ι.comp (P.subgroupOf X).subtype) ⟨⟨z, hzX⟩, mem_subgroupOf.mpr (hPCP hz)⟩ =
        (ι.comp (P.subgroupOf X).subtype) 1 := by
      rw [map_one]
      exact h1
    have h3 := hιbij.1 h2
    exact (mem_bot).mpr (congrArg (fun w : P.subgroupOf X => ((w : X) : H)) h3)
  have hYtop : Y ≠ ⊤ := by
    intro htop
    have h1 : Nat.card Y ≤ Nat.card PC := by
      rw [hY]
      refine (Nat.le_of_dvd Nat.card_pos
        (Subgroup.card_map_dvd (H := PC.subgroupOf X) ι)).trans ?_
      exact (Nat.card_congr (subgroupOfEquivOfLe ((hPCP.trans hPX))).toEquiv).le
    rw [htop, card_top] at h1
    exact absurd (hW.trans (h1.trans hPCcard)) (not_le.mpr hpp)
  have hYinv : ∀ h : normalizer (X : Set H), (h : H) ∈ D → ∀ y ∈ Y,
      normalizerFrattiniConj X h y ∈ Y := by
    intro h hhD y hy
    obtain ⟨x, hxX, hxP⟩ := exists_conj_eq_of_isSylowOf hP (isSylowOf_map_conj hP h.2)
    set n : H := x⁻¹ * h with hn
    have hnD : n ∈ D := D.mul_mem (D.inv_mem (hXD hxX)) hhD
    have hnPeq : P.map (MulAut.conj n).toMonoidHom = P := by
      have h1 := congrArg (fun K' : Subgroup H => K'.map (MulAut.conj x⁻¹).toMonoidHom) hxP
      simp only [map_map] at h1
      have e1 : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
          MonoidHom.id H := by
        ext y
        change x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y
        group
      have e2 : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj (h : H)).toMonoidHom =
          (MulAut.conj n).toMonoidHom := by
        ext y
        simp [MulAut.conj_apply, hn, mul_assoc]
      rw [e1, e2, map_id] at h1
      exact h1.symm
    have hnP : n ∈ normalizer (P : Set H) := by
      rw [mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        rw [← hnPeq]
        exact ⟨y, hy, rfl⟩
      · intro hy
        rw [← hnPeq] at hy
        obtain ⟨y', hy', hyy⟩ := hy
        have : y' = y := by
          have h1 : n * y' * n⁻¹ = n * y * n⁻¹ := hyy
          simpa using h1
        rwa [← this]
    have hxN : x ∈ normalizer (X : Set H) := hDX (hXD hxX)
    have hnN : n ∈ normalizer (X : Set H) := mul_mem (inv_mem hxN) h.2
    have hsplit : normalizerFrattiniConj X h = normalizerFrattiniConj X ⟨n, hnN⟩ := by
      have : h = ⟨x, hxN⟩ * ⟨n, hnN⟩ := Subtype.ext (by simp [hn])
      rw [this, map_mul, normalizerFrattiniConj_eq_one_of_mem hXA _ hxX, one_mul]
    rw [hsplit]
    obtain ⟨z, hz, rfl⟩ := hy
    have hzPC : (z : H) ∈ PC := mem_subgroupOf.mp hz
    have hnK : n ∈ normalizer (K : Set H) := hDK hnD
    have hmem := hPCn ⟨n, hnK⟩ hnP (z : H) hzPC
    have hconj : normalizerFrattiniConj X ⟨n, hnN⟩ (ι z) = ι (X.normalizerMonoidHom ⟨n, hnN⟩ z) :=
      rfl
    rw [hconj]
    exact hYW _ hmem
  rcases hirr Y hYinv with h0 | ht
  · exact hY1 h0
  · exact hYtop ht

theorem stmtJ4SingleComponent_holds :
    StmtJ4SingleComponent :=
  fun _ _ _ _ _ _ hDK hXD hXn hXK _ hp hp5 hXA hW hirr hZ _ _ hP hB hPB =>
    irreducible_original_prime_witness_excludes_J4_single_component_quotient hDK hXD hXn hXK hp
      hp5 hXA hW hirr hZ hP hB hPB

end CFSG.Quasithin.H13.NQRigid
