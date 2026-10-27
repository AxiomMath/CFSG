module

public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGTableB

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB TypeA CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem TypeA.prime_ne_two_of_dvd_two_pow_sub_one {p m : ℕ} (hm : 1 ≤ m) (h : p ∣ 2 ^ m - 1) :
    p ≠ 2 := by
  rintro rfl
  have h1 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  have h2 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  omega

theorem recipeLinear_tableB {d N p : ℕ} (hp : p.Prime) (hpN : p ∣ N - 1) (hN : ∃ m, N = 2 ^ m)
    (hd : 2 ≤ d) (hpd : ¬ p ∣ d) {Q : LargeEvenRawCont} (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  obtain ⟨m, rfl⟩ := hN
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpN
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero] at hK
      omega
    · exact h0
  have hp2 : p ≠ 2 := prime_ne_two_of_dvd_two_pow_sub_one hm (hK ▸ hpK)
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have h4 : 4 ≤ Nat.card K := by
    have h1 := Nat.le_of_dvd (by omega) hpK
    omega
  have hpd' : Nat.Coprime p d := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpd
  have hI : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
      MulAut.congr (recipeEquiv d K) φ ∈ Set.range (conjAut d K) := fun _ hφ =>
    congr_recipeEquiv_mem hφ
  rcases (show d ≤ 3 ∨ 4 ≤ d by omega) with hd3 | hd4
  · exact ⟨0, ggTorusLift_of_mulEquiv (recipeEquiv d K)
        (ggTorusLift_zero (two_dvd_card_projectiveSL hd)),
      ggBstarBound_of_mulEquiv (recipeEquiv d K) hI
        (ggBstarBound_small hp hpK (by omega) hd3 hpd'),
      ggEndNode_of_mulEquiv (recipeEquiv d K) hI (ggEndNode_small hp hpK (by omega) hd3 hpd')⟩
  · have hsec : SLHasSections d K :=
      slHasSections_of_card (by omega) (by omega) (by omega) (by omega)
    exact ⟨d - 1, ggTorusLift_of_mulEquiv (recipeEquiv d K)
        (ggTorusLift_coprime hp hpK hd hpd' hsec),
      ggBstarBound_of_mulEquiv (recipeEquiv d K) hI
        (ggBstarBound_coprime hp hp2 hpK (by omega) hpd'),
      ggEndNode_of_mulEquiv (recipeEquiv d K) hI (ggEndNode_coprime hp hpK hd4 hpd' h4 hsec)⟩

@[expose] def GGTypeALabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1 ∧ ¬ p ∣ lab.rank + 1) ∨
    (lab.tag = .D ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1) ∨
    (lab.tag = .twD ∧ lab.rank = 2 ∧ p ∣ (2 ^ lab.n) ^ 2 - 1)

theorem GGTypeALabel.pilot {p : ℕ} {lab : LargeEvenLabel} (h : GGTypeALabel p lab) :
    GGOutdiagPilotLabel lab := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, hl, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, by omega⟩))))

theorem largeEvenLabelAll_typeA {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGTypeALabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I := by
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  rcases h with ⟨h, hpn, hpl⟩ | ⟨h, hl, hpn⟩ | ⟨h, hl, hpn⟩
  · dsimp only at h hpn hpl
    subst h
    have hl1 : 1 ≤ l := hlab.2.1
    exact recipeLinear_tableB hp hpn ⟨n, rfl⟩ (by omega) hpl hQ
  · dsimp only at h hl hpn
    subst h hl
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_left rfl] at hQ ⊢
    have hp2 := prime_ne_two_of_dvd_two_pow_sub_one hn hpn
    refine recipeLinear_tableB hp hpn ⟨n, rfl⟩ (by norm_num) (fun h4 => hp2 ?_) hQ
    have h1 : p ∣ 2 ^ 2 := by norm_num; exact h4
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1)
  · dsimp only at h hl hpn
    subst h hl
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_left rfl] at hQ ⊢
    have hpn' : p ∣ 2 ^ (2 * n) - 1 := by rw [mul_comm, pow_mul]; exact hpn
    have hp2 := prime_ne_two_of_dvd_two_pow_sub_one (by omega) hpn'
    refine recipeLinear_tableB hp hpn ⟨2 * n, by rw [mul_comm, pow_mul]⟩ le_rfl
      (fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)) hQ

section On

variable {G : Type} [Group G] [Finite G]

@[expose] def GGBstarInputOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G),
    GGThmIHyp p B x L →
    LargeEvenMarking L (fun lab _ _ I _ θ => S p lab ∧ LargeEvenSplit p lab ∧
      B ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) →
    ∃ Bs : Subgroup G, GGBstar p B Bs

@[expose] def GGStdSubPreInputOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G),
    GGThmIHyp p B x L →
    LargeEvenMarking L (fun lab _ _ I _ θ => S p lab ∧ LargeEvenSplit p lab ∧
      B ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) →
    ∃ D J : Subgroup G, LargeEvenStdSubPre p B x L D J

theorem exists_ggBstar_of_marking {p : ℕ} {B : Subgroup G} {x : G} {L : Subgroup G}
    (hT : GGThmIHyp p B x L) (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hM : LargeEvenMarking L fun _ R _ I _ θ => (B ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) ∧
      ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I) :
    ∃ Bs : Subgroup G, GGBstar p B Bs := by
  obtain ⟨-, -, -, -, -, hβ, hS, -⟩ := hT
  have hp : p.Prime := hβ.1
  obtain ⟨hL, lab, -, hraw⟩ := hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨hBN, h3⟩, r, hlift, hbound⟩ := largeEvenRawDatum_exists hraw
  exact exists_ggBstar_of_card_le hS.1.1 fun E hE hBE =>
    card_le_of_bstarBound hp hS hβ.2.2.2 hnc hL θ hBN h3 hlift hbound hE hBE

theorem ggBstarInputOn_of_labels {S : ℕ → LargeEvenLabel → Prop}
    (hpilot : ∀ p lab, S p lab → GGOutdiagPilotLabel lab)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I) :
    GGBstarInputOn S := by
  intro G _ _ p B x L hT hM
  have hp : p.Prime := hT.2.2.2.2.2.1.1
  have hnc := ggLNoncyclicInputOn_pilot G p B x L hT
    (largeEvenMarking_mono (fun lab _ _ _ _ _ hP => ⟨hpilot p lab hP.1, hP.2⟩) hM)
  have hM' := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  exact exists_ggBstar_of_marking hT hnc
    (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨⟨hP.1.2.2.1, hP.1.2.2.2⟩, hP.2⟩) hM')

theorem exists_stdSubPre_of_marking {p : ℕ} {B : Subgroup G} {x : G} {L : Subgroup G}
    (hT : GGThmIHyp p B x L)
    (hM : LargeEvenMarking L fun _ R _ I _ θ => (B ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) ∧
      ∃ r, GGTorusLift p r R ∧ GGEndNode p r R I) :
    ∃ D J : Subgroup G, LargeEvenStdSubPre p B x L D J := by
  obtain ⟨-, -, -, -, -, hβ, hS, -⟩ := hT
  have hp : p.Prime := hβ.1
  have := Fact.mk hp
  obtain ⟨hL, lab, -, hraw⟩ := hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨hBN, h3⟩, r, hlift, hend⟩ := largeEvenRawDatum_exists hraw
  set γ := ggGamma L hBN with hγ
  have hBp : ∀ b : B, b ^ p = 1 := fun b => Subtype.ext (by simpa using hS.1.1.2 b b.2)
  have hBc : ∀ a b : B, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hS.1.1 a.2 b.2)
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ I, ∀ l : L, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta L θ hBN b, ggBeta_mem L θ hBN h3 b, fun l => ggBeta_ggQuotHom L hBN θ b l⟩
  have hcA := card_range_ggGamma_mul L hBN hp hS
  have hcβ := card_range_ggBeta_mul L θ hp hS hL hBN
  have hAβ : Nat.card γ.range = Nat.card (ggBeta L θ hBN).range :=
    Nat.eq_of_mul_eq_mul_right hp.pos (hcA.trans hcβ.symm)
  have hr : p ^ r ≤ Nat.card γ.range := by
    rw [hAβ]
    exact pow_le_card_range_ggBeta hp hS hL θ hBN hlift
  have h3' : p ^ 3 ≤ Nat.card γ.range := by
    have h4 := pow_four_le_card_of_bmax hp hS.1 hβ.2.2.2
    rw [← hcA, pow_succ] at h4
    exact Nat.le_of_mul_le_mul_right h4 hp.pos
  obtain ⟨a, haA, ha1, hcomp, hcent⟩ := hend L (ggQuotHom θ) (ggQuotHom_surjective θ)
    (by rw [ker_ggQuotHom]) hL γ.range hA hAI hr h3'
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
  ·
    have hN : Subgroup.zpowers (d : G) ≤
        Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
      intro y hy
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact IsElemAbelian.comm hS.1.1 (Subgroup.zpowers_le.mpr hxB hz)
        (Subgroup.zpowers_le.mpr d.2 hy)
    have hdisj : Disjoint (Subgroup.zpowers x) (Subgroup.zpowers (d : G)) := by
      have hdvd : Nat.card (Subgroup.zpowers x ⊓ Subgroup.zpowers (d : G) : Subgroup G) ∣ p := by
        have := Subgroup.card_dvd_of_le
          (inf_le_right : Subgroup.zpowers x ⊓ Subgroup.zpowers (d : G) ≤ _)
        rwa [Nat.card_zpowers, orderOf_eq_prime hdp hd1] at this
      rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
      · rw [disjoint_iff]
        exact Subgroup.eq_bot_of_card_eq _ h1
      · exfalso
        apply hdx
        have heq : Subgroup.zpowers x ⊓ Subgroup.zpowers (d : G) = Subgroup.zpowers (d : G) :=
          Subgroup.eq_of_le_of_card_ge inf_le_right
            (by rw [h1, Nat.card_zpowers, orderOf_eq_prime hdp hd1])
        have hmem : (d : G) ∈ Subgroup.zpowers x ⊓ Subgroup.zpowers (d : G) := by
          rw [heq]
          exact Subgroup.mem_zpowers _
        exact hmem.1
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hN hdisj,
      Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hxp hS.2.2.1,
      orderOf_eq_prime hdp hd1, sq]
  ·
    rw [← hfix, largeEvenLayer_map_of_injective _ L.subtype_injective]
  ·
    rw [← hfix]
    exact isComponentOf_map_of_injective _ L.subtype_injective hcomp
  ·
    apply le_antisymm
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


theorem ggStdSubPreInputOn_of_labels {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGEndNode p r R I) :
    GGStdSubPreInputOn S := by
  intro G _ _ p B x L hT hM
  have hp : p.Prime := hT.2.2.2.2.2.1.1
  have hM' := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  exact exists_stdSubPre_of_marking hT
    (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨⟨hP.1.2.2.1, hP.1.2.2.2⟩, hP.2⟩) hM')

end On

theorem ggBstarInputOn_typeA : GGBstarInputOn GGTypeALabel :=
  ggBstarInputOn_of_labels (fun _ _ h => h.pilot) fun _ _ hp hlab h =>
    (largeEvenLabelAll_typeA hp hlab h).mono fun _ _ _ _ ⟨r, h1, h2, _⟩ => ⟨r, h1, h2⟩

theorem ggStdSubPreInputOn_typeA : GGStdSubPreInputOn GGTypeALabel :=
  ggStdSubPreInputOn_of_labels fun _ _ hp hlab h =>
    (largeEvenLabelAll_typeA hp hlab h).mono fun _ _ _ _ ⟨r, h1, _, h3⟩ => ⟨r, h1, h3⟩

end CFSG.StandardType
