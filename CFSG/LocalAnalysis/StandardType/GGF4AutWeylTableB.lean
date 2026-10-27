module

public import CFSG.LocalAnalysis.StandardType.GGF4AutWeyl
public import CFSG.LocalAnalysis.StandardType.GGNbrTableBExcInduced
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylGenRefl
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerF4
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley CFSG.Assembly
  CFSG.LieType.SeitzGeneration CFSG.RankThree.CentralCover Multiplicative
open CFSG.Open (IsElemAbelian)

namespace F4AutWeyl

theorem exists_descent_F4
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 4) :
    ∃ ψ : adjointGroup .F4 K →* adjointGroup .F4 (FiniteField.Extension K 2 2),
      Function.Injective ψ ∧ E.map ψ = TableBF4.torusPow (FiniteField.Extension K 2 2) p ∧
      ∀ w : WeylGroup .F4, ∃ k : adjointGroup .F4 K,
        ∃ t ∈ torusGroup .F4 (FiniteField.Extension K 2 2),
          ((ψ k : adjointGroup .F4 (FiniteField.Extension K 2 2)) :
              ModGL .F4 (FiniteField.Extension K 2 2)) =
            t * canonicalRep (coxeterSystem .F4) (FiniteField.Extension K 2 2) w := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq2 : p ∣ Nat.card K ^ 2 - 1 := dvd_card_sq_sub_one_of_card_F4 hp hp2 hE hcard
  let L := FiniteField.Extension K 2 2
  have hLK : Nat.card L = Nat.card K ^ 2 := FiniteField.natCard_extension K 2 2
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have hpL : p ∣ Nat.card L - 1 := hLK ▸ hq2
  let Fr : L →+* L := (FiniteField.Extension.frob K 2 2).toRingEquiv.toRingHom
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => FiniteField.Extension.frob_apply K 2 2
  have hFr2 : ∀ c, Fr (Fr c) = c := by
    intro c
    haveI := Fintype.ofFinite L
    rw [hFr, hFr, ← pow_mul, ← sq, ← hLK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hbij : Function.Bijective Fr := (FiniteField.Extension.frob K 2 2).toRingEquiv.bijective
  have hfix := frobenius_fixed_eq_map_of_bijective (τ := .F4) (Or.inr rfl) Fr hFr hbij
  let σ : adjointGroup .F4 L →* adjointGroup .F4 L := TableBF4Two.adjointMap Fr
  have hσ : ∀ x : adjointGroup .F4 L, ((σ x : adjointGroup .F4 L) : ModGL .F4 L) =
      Units.map (entrywiseHom Fr) (x : ModGL .F4 L) := fun x => Units.ext rfl
  have hσ2 : ∀ x, σ (σ x) = x := by
    intro x
    refine Subtype.ext (Units.ext ?_)
    rw [hσ, hσ]
    change entrywise Fr (entrywise Fr _) = _
    rw [entrywise_entrywise, show Fr.comp Fr = RingHom.id L from RingHom.ext hFr2, entrywise_id]
  set φ := TableBF4Two.adjointMap (algebraMap K L) with hφ
  have hφinj : Function.Injective φ := TableBF4Two.adjointMap_injective _
  have hφfix : ∀ k, σ (φ k) = φ k := by
    intro k
    have hk : ((φ k : adjointGroup .F4 L) : ModGL .F4 L) ∈
        adjointGroup .F4 L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) :=
      hfix ▸ ⟨(k : ModGL .F4 K), k.2, rfl⟩
    exact Subtype.ext ((hσ _).trans hk.2)
  have hσfix : ∀ x, σ x = x → ∃ k, φ k = x := by
    intro x hx
    have hx' : (x : ModGL .F4 L) ∈
        adjointGroup .F4 L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) :=
      ⟨x.2, (hσ x).symm.trans (congrArg Subtype.val hx)⟩
    rw [hfix] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
  have hE' : IsElemAbelian p (E.map φ) := TableB.isElemAbelian_map hE φ
  have hcard' : Nat.card (E.map φ) = p ^ 4 := by
    rw [Subgroup.card_map_of_injective hφinj, hcard]
  obtain ⟨g, hg⟩ := ggF4ToralRankInput_of_three hp hp2 hpL (fun _ => ggF4ThreeRankInput_holds)
    (E.map φ) hE' hcard'.ge
  set V := TableBF4.torusPow L p with hV
  have hmemV : ∀ y, y ∈ V ↔ g⁻¹ * y * g ∈ E.map φ := by
    intro y
    rw [← hg, Subgroup.mem_map_equiv]
    rfl
  have hCV := F4_adjointGroup_inf_centralizer_torusPow_of_ne_two (k := L) hp hp2
    (by rw [Nat.card_units]; exact hpL)
  have hcent : ∀ x ∈ Subgroup.centralizer ((E.map φ : Subgroup (adjointGroup .F4 L)) :
      Set (adjointGroup .F4 L)), ((g * x * g⁻¹ : adjointGroup .F4 L) : ModGL .F4 L) ∈
        torusGroup .F4 L := by
    intro x hx
    rw [← hCV]
    refine ⟨(g * x * g⁻¹).2, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    have hhV : (⟨h, torusGroup_le_adjointGroup_F4 hh.1⟩ : adjointGroup .F4 L) ∈ V :=
      ⟨hh.1, Subtype.ext (by rw [Subgroup.coe_pow, hh.2, OneMemClass.coe_one])⟩
    have h1 := Subgroup.mem_centralizer_iff.1 hx _ ((hmemV _).1 hhV)
    have h2 : (⟨h, torusGroup_le_adjointGroup_F4 hh.1⟩ : adjointGroup .F4 L) * (g * x * g⁻¹) =
        (g * x * g⁻¹) * ⟨h, torusGroup_le_adjointGroup_F4 hh.1⟩ := by
      calc _ = g * ((g⁻¹ * ⟨h, torusGroup_le_adjointGroup_F4 hh.1⟩ * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * ⟨h, torusGroup_le_adjointGroup_F4 hh.1⟩ * g)) * g⁻¹ := by rw [h1]
        _ = _ := by group
    exact congrArg Subtype.val h2
  obtain ⟨N, hN⟩ : ∃ N, Nat.card L - 1 = 2 * N + 1 := by
    haveI := Fintype.ofFinite K
    obtain ⟨f, -, hf⟩ := FiniteField.card K 2
    have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
    have hf1 : 1 ≤ (f : ℕ) := f.pos
    have h4 : 4 ≤ Nat.card L := by
      rw [hLK, hK, ← pow_mul]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ ((f : ℕ) * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ∣ Nat.card L := by
      rw [hLK, hK]
      exact dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
    obtain ⟨m, hm⟩ := h2
    exact ⟨m - 1, by omega⟩
  have hodd : ∀ c ∈ Subgroup.centralizer ((E.map φ : Subgroup (adjointGroup .F4 L)) :
      Set (adjointGroup .F4 L)), c ^ (2 * N + 1) = 1 := by
    intro c hc
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hcent c hc)
    have h1 : (g * c * g⁻¹) ^ (Nat.card L - 1) = 1 := by
      refine Subtype.ext ?_
      rw [Subgroup.coe_pow, ha, OneMemClass.coe_one, rootDiagUnit_pow]
      convert rootDiagUnit_one (τ := .F4) (K := L)
      funext i
      rw [Pi.pow_apply, Pi.one_apply, ← Nat.card_units, pow_card_eq_one']
    rw [conj_pow, conj_eq_one_iff, hN] at h1
    exact h1
  set ψ := (MulAut.conj g).toMonoidHom.comp φ with hψ
  have hψinj : Function.Injective ψ := (MulAut.conj g).injective.comp hφinj
  have hEV : E.map ψ = V := by rw [hψ, ← Subgroup.map_map]; exact hg
  have hW : ∀ w : WeylGroup .F4, ∃ h ∈ (⊤ : Subgroup (adjointGroup .F4 K)).map ψ,
      ∃ t ∈ torusGroup .F4 L, (h : ModGL .F4 L) = t * canonicalRep (coxeterSystem .F4) L w := by
    intro w
    set nw : adjointGroup .F4 L :=
      ⟨canonicalRep (coxeterSystem .F4) L w, canonicalRep_mem_adjointGroup _ L w⟩ with hnw
    have hnwV := canonicalRep_mem_normalizer_torusPow_F4 L p w
    have hn : g⁻¹ * nw * g ∈ Subgroup.normalizer ((E.map φ : Subgroup (adjointGroup .F4 L)) :
        Set (adjointGroup .F4 L)) := by
      refine Subgroup.mem_normalizer_iff.2 fun x => ?_
      have e1 : x ∈ E.map φ ↔ g * x * g⁻¹ ∈ V := by
        rw [hmemV, show g⁻¹ * (g * x * g⁻¹) * g = x by group]
      have e2 : g⁻¹ * (nw * (g * x * g⁻¹) * nw⁻¹) * g =
          g⁻¹ * nw * g * x * (g⁻¹ * nw * g)⁻¹ := by group
      rw [e1, Subgroup.mem_normalizer_iff.1 hnwV (g * x * g⁻¹),
        hmemV (nw * (g * x * g⁻¹) * nw⁻¹), e2]
    obtain ⟨z, hz, hσz⟩ := exists_fixed_mul_inv σ hσ2
      (fun e he => by obtain ⟨k, -, rfl⟩ := he; exact hφfix k) hodd hn
    obtain ⟨k, hk⟩ := hσfix _ hσz
    have htz := hcent _ (Subgroup.inv_mem _ hz)
    refine ⟨ψ k, ⟨k, Subgroup.mem_top k, rfl⟩, canonicalRep (coxeterSystem .F4) L w *
        ((g * z⁻¹ * g⁻¹ : adjointGroup .F4 L) : ModGL .F4 L) *
        (canonicalRep (coxeterSystem .F4) L w)⁻¹,
      (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer (R := L) w) _).1 htz, ?_⟩
    have h1 : ψ k = nw * (g * z⁻¹ * g⁻¹) := by
      change g * φ k * g⁻¹ = _
      rw [hk]
      group
    rw [h1]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hnw]
    group
  refine ⟨ψ, hψinj, hEV, fun w => ?_⟩
  obtain ⟨h, ⟨k, -, rfl⟩, t, ht, hkt⟩ := hW w
  exact ⟨k, t, ht, hkt⟩

theorem card_eq_pow_four_of_le
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian p E) (hr : p ^ 4 ≤ Nat.card E) :
    Nat.card E = p ^ 4 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 (TableB.isPGroup_of_isElemAbelian hE)
  have h4m : 4 ≤ m := (Nat.pow_le_pow_iff_right hp.one_lt).1 (hm ▸ hr)
  obtain ⟨E₀, hE₀card, -, hE₀E⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp
    (H := ⊥) (L := E) (n := 4) (by rw [Subgroup.card_bot]; exact one_dvd _)
    (by rw [hm]; exact pow_dvd_pow p h4m) bot_le
  have hq2 := dvd_card_sq_sub_one_of_card_F4 hp hp2 (TableB.isElemAbelian_mono hE hE₀E) hE₀card
  exact le_antisymm (ExcFieldAutCentRankF4.card_le_pow_four hp hp2 hq2 hE) hr

private theorem coordCongr_apply {M N : Type} [Group M] [Group N] (θ : M ≃* N) (φ : MulAut N)
    (f : M) : MulAut.congr θ.symm φ f = θ.symm (φ (θ f)) :=
  rfl

theorem congr_symm_of_isReflection {R : Type} [Group R] {p k : ℕ}
    (τ : Multiplicative (Fin k → ZMod p) →* R) {E : Subgroup R}
    (θ : Multiplicative (Fin k → ZMod p) ≃* ↥E) (hθ : ∀ f, (θ f : R) = τ f)
    {φ : MulAut ↥E} (hφA : φ ∈ ggAutomizer ⊤ E) (hφr : GGIsReflection p φ) :
    MulAut.congr θ.symm φ ^ 2 = 1 ∧
      Nat.card {f : Multiplicative (Fin k → ZMod p) // MulAut.congr θ.symm φ f = f} * p =
        Nat.card (Multiplicative (Fin k → ZMod p)) ∧
      ∃ w : R, ∀ f, w * τ f * w⁻¹ = τ (MulAut.congr θ.symm φ f) := by
  obtain ⟨g, -, -, hφg⟩ := mem_ggAutomizer_iff.1 hφA
  refine ⟨by rw [← map_pow, hφr.1, map_one], ?_, g, fun f => ?_⟩
  · have hfix : Nat.card {f : Multiplicative (Fin k → ZMod p) // MulAut.congr θ.symm φ f = f} =
        Nat.card {b : ↥E // φ b = b} := by
      refine Nat.card_congr (Equiv.subtypeEquiv θ.toEquiv fun f => ?_)
      simp only [coordCongr_apply, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
      constructor
      · intro h
        have h1 := congrArg θ h
        rwa [MulEquiv.apply_symm_apply] at h1
      · intro h
        rw [h, MulEquiv.symm_apply_apply]
    rw [hfix, hφr.2]
    exact Nat.card_congr θ.toEquiv.symm
  · rw [← hθ, ← hθ, coordCongr_apply, MulEquiv.apply_symm_apply, hφg]

theorem congr_symm_mem_closure {R : Type} [Group R] {p k : ℕ}
    (τ : Multiplicative (Fin k → ZMod p) →* R) {E : Subgroup R}
    (θ : Multiplicative (Fin k → ZMod p) ≃* ↥E) (hθ : ∀ f, (θ f : R) = τ f)
    (hrefl : GGReflGenerated p (ggAutomizer ⊤ E))
    (S : Set (MulAut (Multiplicative (Fin k → ZMod p))))
    (hS : ∀ φ ∈ ggAutomizer ⊤ E, GGIsReflection p φ → MulAut.congr θ.symm φ ∈ S) {g : R}
    (hg : g ∈ Subgroup.normalizer (E : Set R)) :
    ∃ u ∈ Subgroup.closure S, ∀ f, g * τ f * g⁻¹ = τ (u f) := by
  have hφ : ggConjAut E hg ∈ ggAutomizer ⊤ E := ggConjAut_mem_ggAutomizer (Subgroup.mem_top g) hg
  rw [hrefl] at hφ
  have hmap : (Subgroup.closure {φ | φ ∈ ggAutomizer ⊤ E ∧ GGIsReflection p φ}).map
      (MulAut.congr θ.symm).toMonoidHom ≤ Subgroup.closure S := by
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨φ, ⟨hφA, hφr⟩, rfl⟩
    exact hS φ hφA hφr
  refine ⟨MulAut.congr θ.symm (ggConjAut E hg), hmap ⟨_, hφ, rfl⟩, fun f => ?_⟩
  rw [← hθ, ← hθ, coordCongr_apply, MulEquiv.apply_symm_apply, ggConjAut_apply]

end F4AutWeyl

namespace NbrTableBExc

theorem ggTorusInducedReflElt_adjointF4_all
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    GGTorusInducedReflElt p 4 (adjointGroup .F4 K) := by
  intro E hE hr _ k τ hτ hτE
  have hcard := F4AutWeyl.card_eq_pow_four_of_le hp hp2 hE hr
  obtain ⟨-, hrefl, -⟩ := ggAutomizer_adjointF4_of_card hp hp2 hE hcard
  set θ : Multiplicative (Fin k → ZMod p) ≃* ↥E :=
    (MonoidHom.ofInjective hτ).trans (MulEquiv.subgroupCongr hτE) with hθdef
  have hθ : ∀ f, (θ f : adjointGroup .F4 K) = τ f := fun f => rfl
  intro u hu
  obtain ⟨g, hg⟩ := mem_ggTorusInduced.1 hu
  have hgN : g ∈ Subgroup.normalizer (E : Set (adjointGroup .F4 K)) := by
    refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · rw [← hτE] at hx ⊢
      obtain ⟨f, rfl⟩ := hx
      exact ⟨u f, (hg f).symm⟩
    · rw [← hτE] at hx ⊢
      obtain ⟨f', hf'⟩ := hx
      refine ⟨u⁻¹ f', ?_⟩
      have h1 := hg (u⁻¹ f')
      rw [MulAut.apply_inv_self] at h1
      exact mul_left_cancel (mul_right_cancel (h1.trans hf'))
  obtain ⟨u', hu', hgu'⟩ := F4AutWeyl.congr_symm_mem_closure τ θ hθ hrefl
    (ggTorusInvolSet p τ) (fun φ hφA hφr => F4AutWeyl.congr_symm_of_isReflection τ θ hθ hφA hφr)
    hgN
  have huu : u = u' := MulEquiv.ext fun f => hτ ((hg f).symm.trans (hgu' f))
  exact huu ▸ hu'

end NbrTableBExc

namespace ExcWeylGen

theorem ggTorusWeylGenElt_adjointF4_all
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    GGTorusWeylGenElt p 4 (adjointGroup .F4 K) := by
  intro E hE hr _
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hcard := F4AutWeyl.card_eq_pow_four_of_le hp hp2 hE hr
  obtain ⟨-, hrefl, -⟩ := ggAutomizer_adjointF4_of_card hp hp2 hE hcard
  obtain ⟨ψ, hψ, hEV, hW⟩ := F4AutWeyl.exists_descent_F4 hp hp2 hE hcard
  set L := FiniteField.Extension K 2 2
  have hLK : Nat.card L = Nat.card K ^ 2 := FiniteField.natCard_extension K 2 2
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have hpL : p ∣ Nat.card L - 1 := hLK ▸ F4AutWeyl.dvd_card_sq_sub_one_of_card_F4 hp hp2 hE hcard
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := L) hpL
  have hζ : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  have hdet : IsUnit ((Tag.F4.cartan.det : ℤ) : ZMod p) := by
    rw [det_cartan_F4, Int.cast_one]
    exact isUnit_one
  set χ := chevTorus .F4 ζ hζ with hχdef
  have hχinj : Function.Injective χ := chevTorus_injective hζo hζ hdet
  have hχr : χ.range = TableBF4.torusPow L p := range_chevTorus_eq_torusPow_of_prime hp hpL hζo hζ
  have hχE : ∀ f, χ f ∈ E.map ψ := fun f => hEV ▸ hχr ▸ ⟨f, rfl⟩
  set e : Multiplicative (Fin Tag.F4.rank → ZMod p) →* adjointGroup .F4 K :=
    E.subtype.comp ((E.equivMapOfInjective ψ hψ).symm.toMonoidHom.comp
      (χ.codRestrict (E.map ψ) hχE)) with hedef
  have he : ∀ f, ψ (e f) = χ f := fun f => by
    have h1 := (E.equivMapOfInjective ψ hψ).apply_symm_apply ⟨χ f, hχE f⟩
    exact congrArg Subtype.val h1
  have heE : ∀ f, e f ∈ E := fun f => ((E.equivMapOfInjective ψ hψ).symm _).2
  have heinj : Function.Injective e := fun f f' h => hχinj (by rw [← he, ← he, h])
  have herange : e.range = E := by
    refine le_antisymm (by rintro _ ⟨f, rfl⟩; exact heE f) fun x hx => ?_
    obtain ⟨f, hf⟩ : ψ x ∈ χ.range := hχr ▸ hEV ▸ ⟨x, hx, rfl⟩
    exact ⟨f, hψ (by rw [he, hf])⟩
  choose kk tt htt hkt using hW
  set n : Fin Tag.F4.rank → adjointGroup .F4 K := fun i => kk (simple .F4 i) with hndef
  have hTcomm := (triangular_borel_structure.{0, 0} .F4 L).1
  have hrefl' : ∀ i v, n i * e (ofAdd v) * (n i)⁻¹ =
      e (ofAdd (v - cartanFunctional .F4 p i v • Pi.single i 1)) := by
    intro i v
    apply hψ
    rw [map_mul, map_mul, map_inv, he, he]
    have hw := weylElt_conj_chevTorus (K := L) ζ hζ i v
    have hcan : canonicalRep (coxeterSystem .F4) L (simple .F4 i) = weylElt .F4 L i 1 := by
      rw [show simple .F4 i = (coxeterSystem .F4).wordProd [i] from
          (CoxeterSystem.wordProd_singleton _ i).symm,
        EvenF4QPlus.canonicalRep_wordProd_of_charTwo, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one]
    apply Subtype.ext
    have hψn : ((ψ (n i) : adjointGroup .F4 L) : ModGL .F4 L) =
        tt (simple .F4 i) * weylElt .F4 L i 1 := by rw [hndef, hkt, hcan]
    have hχv : ((χ (ofAdd (v - cartanFunctional .F4 p i v • Pi.single i 1)) :
        adjointGroup .F4 L) : ModGL .F4 L) ∈ torusGroup .F4 L := by
      have h1 : χ (ofAdd (v - cartanFunctional .F4 p i v • Pi.single i 1)) ∈
          TableBF4.torusPow L p := hχr ▸ ⟨_, rfl⟩
      exact h1.1
    have hw' := congrArg Subtype.val hw
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hw' ⊢
    rw [hψn, ← hw']
    have hc := hTcomm _ (htt (simple .F4 i)) _ (hw' ▸ hχv)
    calc tt (simple .F4 i) * weylElt .F4 L i 1 * ((χ (ofAdd v) : adjointGroup .F4 L) :
          ModGL .F4 L) * (tt (simple .F4 i) * weylElt .F4 L i 1)⁻¹ =
        tt (simple .F4 i) * (weylElt .F4 L i 1 * ((χ (ofAdd v) : adjointGroup .F4 L) :
          ModGL .F4 L) * (weylElt .F4 L i 1)⁻¹) * (tt (simple .F4 i))⁻¹ := by group
      _ = _ := by rw [hc]; group
  set θ : Multiplicative (Fin Tag.F4.rank → ZMod p) ≃* ↥E :=
    (MonoidHom.ofInjective heinj).trans (MulEquiv.subgroupCongr herange) with hθdef
  have hθ : ∀ f, (θ f : adjointGroup .F4 K) = e f := fun f => rfl
  refine ⟨Tag.F4.rank, e, heinj, herange, fun L' _ φ' hφ' hker =>
    exists_torus_section_of_reflections hp hp2 e (cartanFunctional .F4 p)
      (fun i => cartanFunctional_single i) n hrefl' hφ' hker, fun g hg => ?_⟩
  exact F4AutWeyl.congr_symm_mem_closure e θ hθ hrefl (ggTorusInducedReflSet p e)
    (fun φ hφA hφr => by
      obtain ⟨h2, hfix, w, hw⟩ := F4AutWeyl.congr_symm_of_isReflection e θ hθ hφA hφr
      exact ⟨SpCoord.pow_sub_one_eq_one_of_sq hp hp2 h2, hfix, w, hw⟩) hg

end ExcWeylGen

namespace NbrTableBExc

theorem ggTorusReflGenW_F4_all
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    GGTorusReflGenW p 4 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K) :=
  ggTorusReflGenW_of_inducedReflElt hp hp2 (TableBF4.idImage_subset_inn K)
    (TableBF4.center_recipeGroup_eq_bot K)
    (ggTorusWeylGenElt_of_mulEquiv (TableBF4.recipeEquiv K)
      (ExcWeylGen.ggTorusWeylGenElt_adjointF4_all hp hp2))
    (ggTorusInducedReflElt_of_mulEquiv (TableBF4.recipeEquiv K)
      (ggTorusInducedReflElt_adjointF4_all hp hp2))

theorem largeEvenLabelAll_reflGenW_F4_all
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .F4) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusReflGenW p 4 R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ, ggTorusReflGenW_F4_all hp hp2⟩

end NbrTableBExc

end CFSG.StandardType
