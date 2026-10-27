module

public import CFSG.LocalAnalysis.StandardType.GGStdSubExistAdmissible

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

section Reduction

variable {G : Type} [Group G] [Finite G]

theorem ggGamma_range_props {p r : ℕ} (hp : p.Prime) {B : Subgroup G} {x : G} {L : Subgroup G}
    (hS : LargeEvenSStar p B x L) (h4 : 4 ≤ LargeEvenTwoLocalRank p G) (hL : commutator L = ⊤)
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hlift : GGTorusLift p r R) :
    IsElemAbelian p (ggGamma L hBN).range ∧
      (∀ a ∈ (ggGamma L hBN).range, ∃ φ ∈ I, ∀ l : L, φ (ggQuotHom θ l) = ggQuotHom θ (a l)) ∧
      p ^ r ≤ Nat.card (ggGamma L hBN).range ∧ p ^ 3 ≤ Nat.card (ggGamma L hBN).range := by
  have hBp : ∀ b : B, b ^ p = 1 := fun b => Subtype.ext (by simpa using hS.1.1.2 b b.2)
  have hBc : ∀ a b : B, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hS.1.1 a.2 b.2)
  have hcA := card_range_ggGamma_mul L hBN hp hS
  have hcβ := card_range_ggBeta_mul L θ hp hS hL hBN
  have hAβ : Nat.card (ggGamma L hBN).range = Nat.card (ggBeta L θ hBN).range :=
    Nat.eq_of_mul_eq_mul_right hp.pos (hcA.trans hcβ.symm)
  refine ⟨isElemAbelian_range hBc hBp _, ?_, ?_, ?_⟩
  · rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta L θ hBN b, ggBeta_mem L θ hBN h3 b, fun l => ggBeta_ggQuotHom L hBN θ b l⟩
  · rw [hAβ]
    exact pow_le_card_range_ggBeta hp hS hL θ hBN hlift
  · have h4' := pow_four_le_card_of_bmax hp hS.1 h4
    rw [← hcA, pow_succ] at h4'
    exact Nat.le_of_mul_le_mul_right h4' hp.pos

theorem exists_stdSubPre_of_endNode {p : ℕ} (hp : p.Prime) {B : Subgroup G} {x : G}
    {L : Subgroup G} (hS : LargeEvenSStar p B x L) (hBN : B ≤ Subgroup.normalizer (L : Set G))
    {a : MulAut L} (haA : a ∈ (ggGamma L hBN).range) (ha1 : a ≠ 1)
    (hcomp : IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a))
    (hcent : ∀ a' ∈ (ggGamma L hBN).range,
      ((∀ j ∈ LargeEvenLayer (ggFix a), a' j = j) ↔ a' ∈ Subgroup.zpowers a)) :
    ∃ D J : Subgroup G, LargeEvenStdSubPre p B x L D J := by
  have := Fact.mk hp
  set γ := ggGamma L hBN with hγ
  obtain ⟨d, rfl⟩ := haA
  have hxB : x ∈ B := hS.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  have hdx : (d : G) ∉ Subgroup.zpowers x := by
    intro hd
    apply ha1
    rw [ggGamma_eq_one_iff]
    rw [← inf_centralizer_eq_zpowers_of_sstar hp hS] at hd
    exact hd.2
  have hdp : (d : G) ^ p = 1 := hS.1.1.2 d d.2
  have hxp : x ^ p = 1 := hS.1.1.2 x hxB
  have hd1 : (d : G) ≠ 1 := fun h => hdx (h ▸ one_mem _)
  set D : Subgroup G := Subgroup.zpowers x ⊔ Subgroup.zpowers (d : G) with hD
  set J' := LargeEvenLayer (ggFix (γ d)) with hJ'
  have hJ'fix : J' ≤ ggFix (γ d) := sSup_le fun K hK => hK.1
  have hfix : (ggFix (γ d)).map L.subtype = L ⊓ Subgroup.centralizer (D : Set G) := by
    rw [hD, inf_centralizer_sup_zpowers hLx]
    exact map_ggFix_ggGamma L hBN d
  have hDB : D ≤ B := sup_le (Subgroup.zpowers_le.mpr hxB) (Subgroup.zpowers_le.mpr d.2)
  refine ⟨D, J'.map L.subtype, hDB, isElemAbelian_mono hS.1.1 hDB, ?_,
    Subgroup.mem_sup_left (Subgroup.mem_zpowers x), ?_, ?_, ?_⟩
  · have hN : Subgroup.zpowers (d : G) ≤
        Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
      intro y hy
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact IsElemAbelian.comm hS.1.1 (Subgroup.zpowers_le.mpr hxB hz)
        (Subgroup.zpowers_le.mpr d.2 hy)
    have hdisj : Disjoint (Subgroup.zpowers x) (Subgroup.zpowers (d : G)) := by
      rw [Subgroup.disjoint_def]
      intro g hgx hgd
      by_contra hg1
      have h1 := mem_of_mem_zpowers_of_ne_one hp hdp hd1 hgd hgx hg1
      exact hdx h1
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hN hdisj,
      Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hxp hS.2.2.1,
      orderOf_eq_prime hdp hd1, sq]
  · rw [← hfix, largeEvenLayer_map_of_injective _ L.subtype_injective]
  · rw [← hfix]
    exact isComponentOf_map_of_injective _ L.subtype_injective hcomp
  · apply le_antisymm
    · refine le_inf hDB (sup_le ?_ ?_)
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        rintro _ ⟨j, -, rfl⟩
        exact Subgroup.mem_centralizer_singleton_iff.mp (hLx j.2)
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        rintro _ ⟨j, hj, rfl⟩
        have h1 := congrArg Subtype.val (mem_ggFix.mp (hJ'fix hj))
        rw [ggGamma_coe] at h1
        calc (j : G) * d = d * j * (d : G)⁻¹ * d := by rw [h1]
          _ = d * j := by group
    · rintro b ⟨hbB, hbJ⟩
      have hγb : ∀ j ∈ J', γ ⟨b, hbB⟩ j = j := by
        intro j hj
        apply Subtype.ext
        rw [ggGamma_coe]
        have := Subgroup.mem_centralizer_iff.mp hbJ j ⟨j, hj, rfl⟩
        calc b * j * b⁻¹ = j * b * b⁻¹ := by rw [this]
          _ = j := by group
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ((hcent _ ⟨⟨b, hbB⟩, rfl⟩).mp hγb)
      have hker : ((⟨b, hbB⟩ : B) * d ^ (-k)) ∈ γ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_zpow, ← hk, ← zpow_add, add_neg_cancel, zpow_zero]
      rw [ker_ggGamma L hBN hp hS, Subgroup.mem_subgroupOf] at hker
      have hb : b = (((⟨b, hbB⟩ : B) * d ^ (-k) : B) : G) * (d : G) ^ k := by
        rw [Subgroup.coe_mul, Subgroup.coe_zpow, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero,
          mul_one]
      rw [hb]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hker)
        (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ _))

theorem ggStdSubPreInput_of_labels_adm (ha₀ : GGLNoncyclicInput)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGEndNodeAdm p r R I) :
    GGStdSubPreInput := by
  intro G _ _ p B x L hT
  have hnc := ha₀ G p B x L hT
  obtain ⟨-, -, -, -, -, hβ, hS, hst⟩ := hT
  have hp : p.Prime := hβ.1
  have hM := largeEvenMarking_and_labelAll (S := fun lab => LargeEvenSplit p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hst.1
  obtain ⟨hL, lab, -, hraw⟩ := hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBN, h3⟩, r, hlift, hend⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hA, hAI, hr, h3'⟩ := ggGamma_range_props hp hS hβ.2.2.2 hL θ hBN h3 hlift
  have hadm := ggAdmissible_of_clauseFour hp hS hnc hBN hst.2.1
  obtain ⟨a, haA, ha1, hcomp, hcent⟩ := hend L (ggQuotHom θ) (ggQuotHom_surjective θ)
    (by rw [ker_ggQuotHom]) hL _ hA hAI hr h3' hadm
  exact exists_stdSubPre_of_endNode hp hS hBN haA ha1 hcomp hcent

theorem card_range_ggGamma_mul_of {p : ℕ} (hp : p.Prime) {E : Subgroup G} {x : G}
    {L : Subgroup G} (hE : IsElemAbelian p E) (hxE : x ∈ E) (hx1 : x ≠ 1)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S → IsCyclic S)
    (hEN : E ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card (ggGamma L hEN).range * p = Nat.card E := by
  have := Fact.mk hp
  have h1 := card_range_mul_card_ker (ggGamma L hEN)
  have hker : (ggGamma L hEN).ker = (Subgroup.zpowers x).subgroupOf E := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ggGamma_eq_one_iff,
      ← inf_centralizer_eq_zpowers_of_elemAbelian hp hE hxE hx1 hLx hcyc]
    exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩
  rw [hker] at h1
  have h2 : Nat.card ((Subgroup.zpowers x).subgroupOf E) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hxE)).toEquiv,
      Nat.card_zpowers, orderOf_eq_prime (hE.2 x hxE) hx1]
  rwa [h2] at h1

theorem card_le_of_bstarBoundInn {p r : ℕ} (hp : p.Prime) {B : Subgroup G} {x : G}
    {L : Subgroup G} (hS : LargeEvenSStar p B x L) (h4 : 4 ≤ LargeEvenTwoLocalRank p G)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S) (hL : commutator L = ⊤)
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hinn : ∃ U : Subgroup G, U ≤ L ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      B ≤ Subgroup.normalizer (U : Set G))
    (hlift : GGTorusLift p r R) (hbound : GGBstarBoundInn p r R I) {E : Subgroup G}
    (hE : IsElemAbelian p E) (hBE : B ≤ E) : Nat.card E ≤ p * Nat.card B := by
  have := Fact.mk hp
  have hEC : E ≤ Subgroup.centralizer ({x} : Set G) := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mpr (IsElemAbelian.comm hE he (hBE hS.2.1))
  have hEN : E ≤ Subgroup.normalizer (L : Set G) := fun e he =>
    mem_normalizer_of_sstar hS hnc (hEC he)
  obtain ⟨hA, hAI, hr, h3'⟩ := ggGamma_range_props hp hS h4 hL θ hBN h3 hlift
  set γB := ggGamma L hBN with hγB
  set γE := ggGamma L hEN with hγE
  have hloc : ∃ U' : Subgroup L, U' ≠ ⊥ ∧ IsPGroup 2 U' ∧ ∀ a ∈ γB.range, ∀ u ∈ U', a u ∈ U' := by
    obtain ⟨U, hUL, hU1, hU2, hBU⟩ := hinn
    refine ⟨U.subgroupOf L, ?_, hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUL).symm, ?_⟩
    · intro hbot
      apply hU1
      rw [eq_bot_iff]
      intro u hu
      have h1 : (⟨u, hUL hu⟩ : L) ∈ U.subgroupOf L := hu
      rw [hbot, Subgroup.mem_bot] at h1
      exact congrArg Subtype.val h1
    · rintro _ ⟨b, rfl⟩ u hu
      show ((γB b u : L) : G) ∈ U
      rw [hγB, ggGamma_coe]
      exact (Subgroup.mem_normalizer_iff.mp (hBU b.2) u).mp hu
  have hAAh : γB.range ≤ γE.range := by
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, hBE b.2⟩, rfl⟩
  have hcB := card_range_ggGamma_mul L hBN hp hS
  have hcE := card_range_ggGamma_mul_of hp hE (hBE hS.2.1) hS.2.2.1 hS.2.2.2.1.1 hS.2.2.2.2 hEN
  have hAh : IsElemAbelian p γE.range := isElemAbelian_range
    (fun a b => Subtype.ext (IsElemAbelian.comm hE a.2 b.2))
    (fun a => Subtype.ext (by simpa using hE.2 a a.2)) γE
  by_contra hcon'
  have hcon := not_le.mp hcon'
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp (isPGroup_of_isElemAbelian hE)
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (isPGroup_of_isElemAbelian hS.1.1)
  have hp2 : p ^ 2 * Nat.card γB.range ≤ Nat.card γE.range := by
    have h1 : p ^ (m + 1) < p ^ e := by
      rw [← he, pow_succ, ← hm, mul_comm]
      exact hcon
    have hme : m + 2 ≤ e := by
      have := (Nat.pow_lt_pow_iff_right hp.one_lt).mp h1
      omega
    have h5 : p ^ 2 * Nat.card B ≤ Nat.card E := by
      rw [hm, he, ← pow_add]
      exact Nat.pow_le_pow_right hp.pos (by omega)
    rw [← hcB, ← hcE] at h5
    have h6 : p ^ 2 * Nat.card γB.range * p ≤ Nat.card γE.range * p := by
      calc p ^ 2 * Nat.card γB.range * p = p ^ 2 * (Nat.card γB.range * p) := by ring
        _ ≤ _ := h5
    exact Nat.le_of_mul_le_mul_right h6 hp.pos
  obtain ⟨A', hlt, hle, U, hU, hU2, hAU⟩ := hbound L (ggQuotHom θ) (ggQuotHom_surjective θ)
    (by rw [ker_ggQuotHom]) hL γB.range γE.range hA hAI hr h3' hloc hAAh hAh hp2
  set E₂ : Subgroup G := (A'.comap γE).map E.subtype with hE₂
  have hE₂E : E₂ ≤ E := Subgroup.map_subtype_le _
  have hBE₂ : B ≤ E₂ := by
    intro b hb
    exact ⟨⟨b, hBE hb⟩, hlt.le ⟨⟨b, hb⟩, rfl⟩, rfl⟩
  have hBlt : B ≠ E₂ := by
    intro heq
    obtain ⟨φ, hφA', hφB⟩ := IsConcreteLE.exists_of_lt hlt
    obtain ⟨e₀, rfl⟩ := hle hφA'
    apply hφB
    have he₂ : (e₀ : G) ∈ E₂ := ⟨e₀, hφA', rfl⟩
    rw [← heq] at he₂
    exact ⟨⟨e₀, he₂⟩, rfl⟩
  have hE₂A : IsElemAbelian p E₂ := isElemAbelian_mono hE hE₂E
  have hUG : U.map L.subtype ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective]
    exact hU
  have hE₂N : E₂ ≤ Subgroup.normalizer ((U.map L.subtype : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    rintro _ ⟨e₁, he₁, rfl⟩ _ ⟨u, hu, rfl⟩
    exact ⟨γE e₁ u, hAU _ he₁ u hu, ggGamma_coe L hEN e₁ u⟩
  have hcard := card_le_of_twoLocal hp ⟨U.map L.subtype, hUG, hU2.map _, rfl⟩ hE₂N hE₂A
  rw [← hS.1.2.1] at hcard
  exact hBlt (Subgroup.eq_of_le_of_card_ge hBE₂ hcard)

theorem ggBstarInput_of_labels_inn (ha₀ : GGLNoncyclicInput) (hinn : GGInnLocalInput)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGBstarBoundInn p r R I) :
    GGBstarInput := by
  intro G _ _ p B x L hT
  have hnc := ha₀ G p B x L hT
  have hU := hinn G p B x L hT
  obtain ⟨-, -, -, -, -, hβ, hS, hst⟩ := hT
  have hp : p.Prime := hβ.1
  have hM := largeEvenMarking_and_labelAll (S := fun lab => LargeEvenSplit p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hst.1
  obtain ⟨hL, lab, -, hraw⟩ := hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBN, h3⟩, r, hlift, hbound⟩ := largeEvenRawDatum_exists hraw
  exact exists_ggBstar_of_card_le hS.1.1 fun E hE hBE =>
    card_le_of_bstarBoundInn hp hS hβ.2.2.2 hnc hL θ hBN h3 hU hlift hbound hE hBE

end Reduction

end CFSG.StandardType
