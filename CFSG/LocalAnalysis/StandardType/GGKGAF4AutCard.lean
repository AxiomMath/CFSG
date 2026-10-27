module

public import CFSG.LocalAnalysis.StandardType.GGKGAF4Defs
public import CFSG.LocalAnalysis.StandardType.GGF4AutWeyl
public import CFSG.LocalAnalysis.StandardType.GGF4AutWeylTorus
public import CFSG.LocalAnalysis.StandardType.GGF4AutWeylTableB
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Basic
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixPerfect
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflInner
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.LieType.SeitzGeneration

namespace KGA

private theorem f4t_exists_hW
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 4) :
    ∃ ψ : adjointGroup .F4 K →* adjointGroup .F4 (FiniteField.Extension K 2 2),
      Function.Injective ψ ∧ E.map ψ = TableBF4.torusPow (FiniteField.Extension K 2 2) p ∧
      p ∣ Nat.card (FiniteField.Extension K 2 2) - 1 ∧
      (∀ w : WeylGroup .F4, ∃ h ∈ (⊤ : Subgroup (adjointGroup .F4 K)).map ψ,
        ∃ t ∈ torusGroup .F4 (FiniteField.Extension K 2 2),
          (h : ModGL .F4 (FiniteField.Extension K 2 2)) =
            t * canonicalRep (coxeterSystem .F4) (FiniteField.Extension K 2 2) w) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq2 : p ∣ Nat.card K ^ 2 - 1 := F4AutWeyl.dvd_card_sq_sub_one_of_card_F4 hp hp2 hE hcard
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
  have hCV := F4AutWeyl.F4_adjointGroup_inf_centralizer_torusPow_of_ne_two (k := L) hp hp2
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
    have hnwV := F4AutWeyl.canonicalRep_mem_normalizer_torusPow_F4 L p w
    have hn : g⁻¹ * nw * g ∈ Subgroup.normalizer ((E.map φ : Subgroup (adjointGroup .F4 L)) :
        Set (adjointGroup .F4 L)) := by
      refine Subgroup.mem_normalizer_iff.2 fun x => ?_
      have e1 : x ∈ E.map φ ↔ g * x * g⁻¹ ∈ V := by
        rw [hmemV, show g⁻¹ * (g * x * g⁻¹) * g = x by group]
      have e2 : g⁻¹ * (nw * (g * x * g⁻¹) * nw⁻¹) * g =
          g⁻¹ * nw * g * x * (g⁻¹ * nw * g)⁻¹ := by group
      rw [e1, Subgroup.mem_normalizer_iff.1 hnwV (g * x * g⁻¹),
        hmemV (nw * (g * x * g⁻¹) * nw⁻¹), e2]
    obtain ⟨z, hz, hσz⟩ := F4AutWeyl.exists_fixed_mul_inv σ hσ2
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
  exact ⟨ψ, hψinj, hEV.trans hV, hpL, hW⟩

theorem ggAutomizer_adjointF4_card_eq_of_card
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 4) :
    Nat.card (ggAutomizer ⊤ E) = 1152 := by
  obtain ⟨ψ, hψinj, hEV, hpL, hW⟩ := f4t_exists_hW hp hp2 hE hcard
  have hcard_range : Nat.card (F4AutWeyl.weylTorusAut (FiniteField.Extension K 2 2) p).range =
      1152 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective
      (F4AutWeyl.weylTorusAut_injective hp hp2 hpL)).toEquiv,
      CFSG.RankThree.PartOne.K133H.card_weylGroup_F4]
  have h1 : Nat.card (ggAutomizer ((⊤ : Subgroup (adjointGroup .F4 K)).map ψ)
      (TableBF4.torusPow (FiniteField.Extension K 2 2) p)) = 1152 := by
    rw [F4AutWeyl.ggAutomizer_torusPow_eq_range hp hp2 hpL hW, hcard_range]
  have h2 := F4AutWeyl.ggAutomizer_map_eq hψinj ⊤ E hEV
  rw [h2] at h1
  rwa [Subgroup.card_map_of_injective (MulAut.congr _).injective] at h1

theorem ggF4_transport {p : ℕ} {R : Type} [Group R]
    (hZ : Subgroup.center R = ⊥) {I : Set (MulAut R)}
    (hI : ∀ φ ∈ I, ∃ r : R, φ = MulAut.conj r) (hAO : GGF4AutOrderAt p R)
    {L' : Type} [Group L'] (ψ : L' →* R) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (A : Subgroup (MulAut L')) (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) (h4 : p ^ 4 ≤ Nat.card A) :
    Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) = 1152 := by
  classical
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap⟩ : ∃ Λ : R →* MulAut L',
      (∀ {e : R} {x : L'}, ψ x = e → Λ e = MulAut.conj x) ∧ Function.Injective Λ ∧
      (∀ e l, ψ (Λ e l) = e * ψ l * e⁻¹) :=
    ⟨ReflInner.liftConj ψ hψ hker, fun hx => ReflInner.liftConj_eq hψ hker hx,
      ReflInner.liftConj_injective hψ hker hZ, ReflInner.map_liftConj_apply hψ hker⟩
  have hAΛ : ∀ a ∈ A, ∃ e, Λ e = a := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    obtain ⟨e, rfl⟩ := hI φ hφI
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
    rw [hΛmap, ← hφ l, MulAut.conj_apply]
  set E : Subgroup R := A.comap Λ
  have hΦbij : Function.Bijective (fun e : E => (⟨Λ e, e.2⟩ : A)) := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from he ▸ a.2⟩, Subtype.ext he⟩
  have hcardE : Nat.card E = Nat.card A := Nat.card_congr (Equiv.ofBijective _ hΦbij)
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hA e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hA.2 _ he
  have h4E : p ^ 4 ≤ Nat.card E := by rw [hcardE]; exact h4
  have hauto : Nat.card (ggAutomizer ⊤ E) = 1152 := (hAO E hEab h4E).2
  have hEA : E.map Λ = A := by
    apply le_antisymm
    · rintro _ ⟨e, he, rfl⟩
      exact he
    · intro a ha
      obtain ⟨e, he⟩ := hAΛ a ha
      exact ⟨e, show Λ e ∈ A from he ▸ ha, he⟩
  have hH : (⊤ : Subgroup R).map Λ = (MulAut.conj : L' →* MulAut L').range := by
    rw [Subgroup.map_top]
    ext φ
    rw [MonoidHom.mem_range, MonoidHom.mem_range]
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨Function.surjInv hψ r, (hΛeq (Function.surjInv_eq hψ r)).symm⟩
    · rintro ⟨n, rfl⟩
      exact ⟨ψ n, hΛeq rfl⟩
  have hB := F4AutWeyl.ggAutomizer_map_eq hΛinj ⊤ E hEA
  rw [hH] at hB
  have hcard : Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) = 1152 := by
    rw [hB, Subgroup.card_map_of_injective (MulAut.congr _).injective]
    exact hauto
  exact hcard

end KGA

end CFSG.StandardType

end
