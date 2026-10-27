module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res5ProofFaith
import CFSG.RankThree.PartTwo.Sec19.Item194Proof
import CFSG.RankThree.PartTwo.Sec19.Step199Proof

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13

@[expose] def TrialityE27Gen : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ), 2 ≤ n →
    CFSG.Blueprint.ChevalleyExceptionalModel Y .trialityD4 2 n →
    ∀ (B : Subgroup (MulAut Y)), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x ^ 3 = 1) →
      Nat.card B = 27 → ∀ c ∈ B, c ∉ (MulAut.conj : Y →* MulAut Y).range →
        Subgroup.closure ({y | c y = y} ∪ ⋃ (F : Subgroup (MulAut Y)) (_ : F ≤ B ∧ Nat.card F = 9),
          {y | ∀ φ ∈ F, φ y = y}) = ⊤

namespace Item19Res6Proof

variable {G : Type} [Group G] [Finite G]

theorem le_sup_of_closure_fix_iUnion_eq_top {X E : Subgroup G}
    (hEX : E ≤ Subgroup.normalizer (X : Set G)) (hE3 : IsPGroup 3 E) {c : G} (hcE : c ∈ E)
    (hgen : Subgroup.closure ({y | Step1910Proof.quotAct hEX ⟨c, hcE⟩ y = y} ∪
      ⋃ F : {F : Subgroup G // F ≤ E ∧ Nat.card F = 9},
        {y | ∀ b : E, (b : G) ∈ (F : Subgroup G) → Step1910Proof.quotAct hEX b y = y}) = ⊤) :
    X ≤ (X ⊓ Subgroup.centralizer ({c} : Set G)) ⊔
      (⨆ F : {F : Subgroup G // F ≤ E ∧ Nat.card F = 9},
        X ⊓ Subgroup.centralizer ((F : Subgroup G) : Set G)) ⊔ CFSG.Open.pCoreOf 2 X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ρ := Step1910Proof.quotAct hEX with hρ
  set O := CFSG.Open.pCoreOf 2 X with hO
  set S := (X ⊓ Subgroup.centralizer ({c} : Set G)) ⊔
    (⨆ F : {F : Subgroup G // F ≤ E ∧ Nat.card F = 9},
      X ⊓ Subgroup.centralizer ((F : Subgroup G) : Set G)) ⊔ O with hS
  have hOX : O ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hO3 : ¬ 3 ∣ Nat.card O := by
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).exists_card_eq
    rw [hk]
    intro h
    have := Nat.prime_three.dvd_of_dvd_pow h
    norm_num at this
  have hEO : E ≤ Subgroup.normalizer (O : Set G) :=
    hEX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
  set T : Subgroup (X ⧸ CFSG.pCore 2 X) := (S.subgroupOf X).map (QuotientGroup.mk' _) with hT
  have hlift : ∀ (B : Subgroup G), B ≤ E → (S' : Subgroup G) → (∀ y : G, y ∈ X →
      (∀ b ∈ B, b * y = y * b) → y ∈ S') → S' ≤ S → ∀ x : X,
      (∀ b : E, (b : G) ∈ B → ρ b (x : X ⧸ CFSG.pCore 2 X) = x) →
      ((x : X) : X ⧸ CFSG.pCore 2 X) ∈ T := by
    intro B hBE S' hS' hS'S x hx
    have hkx : ∀ b ∈ B, (x : G)⁻¹ * (b * x * b⁻¹) ∈ O := by
      intro b hb
      exact (Item19Res4Proof.quotAct_mk_eq_iff hEX ⟨b, hBE hb⟩ x).mp (hx ⟨b, hBE hb⟩ hb)
    obtain ⟨y₁, hy₁, hy₁F⟩ :=
      Step199Proof.exists_fixed_mem_coset (hE3.to_le hBE) hO3 (hBE.trans hEO) hkx
    have hy₁X : y₁ ∈ X := by
      have := X.mul_mem x.2 (hOX hy₁)
      simpa using this
    refine ⟨⟨y₁, hy₁X⟩, Subgroup.mem_subgroupOf.mpr (hS'S (hS' y₁ hy₁X hy₁F)), ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq, Item194Proof.mem_pCore_iff, Subgroup.coe_mul,
      Subgroup.coe_inv]
    have := O.inv_mem hy₁
    simpa using this
  have hgenT : ({y | ρ ⟨c, hcE⟩ y = y} ∪ ⋃ F : {F : Subgroup G // F ≤ E ∧ Nat.card F = 9},
      {y | ∀ b : E, (b : G) ∈ (F : Subgroup G) → ρ b y = y}) ⊆
      (T : Set (X ⧸ CFSG.pCore 2 X)) := by
    rintro y (hy | hy)
    · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      refine hlift (Subgroup.zpowers c) (Subgroup.zpowers_le.2 hcE)
        (X ⊓ Subgroup.centralizer ({c} : Set G)) ?_ (le_sup_left.trans le_sup_left) x ?_
      · intro y hyX hyc
        refine ⟨hyX, Subgroup.mem_centralizer_iff.2 ?_⟩
        intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact hyc c (Subgroup.mem_zpowers c)
      · rintro ⟨b, hbE⟩ ⟨m, rfl⟩
        have hb : (⟨c ^ m, hbE⟩ : E) = ⟨c, hcE⟩ ^ m := Subtype.ext (by simp)
        rw [hb, map_zpow]
        exact Item19Res4Proof.zpow_apply_eq_self hy m
    · obtain ⟨F, hyF⟩ := Set.mem_iUnion.1 hy
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      have hFS : X ⊓ Subgroup.centralizer ((F : Subgroup G) : Set G) ≤ S := by
        rw [hS]
        exact le_sup_of_le_left (le_sup_of_le_right (le_iSup_of_le F le_rfl))
      refine hlift F.1 F.2.1 (X ⊓ Subgroup.centralizer ((F : Subgroup G) : Set G)) ?_ hFS x ?_
      · intro y hyX hyF
        exact ⟨hyX, Subgroup.mem_centralizer_iff.2 hyF⟩
      · intro b hb
        exact hyF b hb
  have hTtop : T = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    exact hgenT
  intro x hx
  have hxT : ((⟨x, hx⟩ : X) : X ⧸ CFSG.pCore 2 X) ∈ T := by rw [hTtop]; trivial
  obtain ⟨s, hs, hsx⟩ := hxT
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq, Item194Proof.mem_pCore_iff, Subgroup.coe_mul,
    Subgroup.coe_inv] at hsx
  have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
  have hOS : O ≤ S := le_sup_right
  have e : x = (s : G) * ((s : G)⁻¹ * x) := by group
  rw [e]
  exact S.mul_mem hsS (hOS hsx)

end Item19Res6Proof

open Item19Res4Proof Item19Res6Proof in
theorem ks1917XGenFaithfulD4_of
    (hT : TrialityE27Gen) :
    KS1917XGenFaithfulD4 := by
  intro G _ _ X E c hXp hXq hEX hEab hE27 hcE hfaith htype
  obtain ⟨n, hn, hmodel, hout⟩ := htype
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ρ := Step1910Proof.quotAct hEX with hρ
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 := (quotAct_eq_one_iff hEX a).mp ha
    have h2 := hfaith a a.2 (fun x hx => (commutator_mem_pCoreOf_iff hx).mpr (h1 x hx))
    exact Subtype.ext h2
  have hR := isElemAbelian_range_quotAct hEX hEab
  have hRab : ∀ x ∈ ρ.range, ∀ y ∈ ρ.range, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hR.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hR27 : Nat.card ρ.range = 27 := by
    rw [← hE27]
    exact Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv.symm
  have hcout := quotAct_not_mem_range_conj hEX hcE hout
  have hgen := hT (X ⧸ CFSG.pCore 2 X) n hn hmodel ρ.range hRab hR.2 hR27 (ρ ⟨c, hcE⟩) ⟨_, rfl⟩
    hcout
  have hE3 : IsPGroup 3 E := IsPGroup.of_card (n := 3) (by rw [hE27]; norm_num)
  refine le_sup_of_closure_fix_iUnion_eq_top hEX hE3 hcE ?_
  rw [eq_top_iff, ← hgen]
  refine Subgroup.closure_mono ?_
  rintro y (hy | hy)
  · exact Or.inl hy
  · simp only [Set.mem_iUnion] at hy
    obtain ⟨F', ⟨hF'R, hF'9⟩, hyF'⟩ := hy
    set FE : Subgroup E := F'.comap ρ with hFE
    have hFE9 : Nat.card FE = 9 := by
      have h1 : FE.map ρ = F' := by
        rw [hFE, Subgroup.map_comap_eq, inf_eq_right.2 hF'R]
      rw [← hF'9, ← h1, Subgroup.card_map_of_injective hρinj]
    have hF9 : Nat.card (FE.map E.subtype) = 9 := by
      rw [Subgroup.card_map_of_injective E.subtype_injective, hFE9]
    refine Or.inr (Set.mem_iUnion.2 ⟨⟨FE.map E.subtype, Subgroup.map_subtype_le FE, hF9⟩, ?_⟩)
    intro b hb
    obtain ⟨b', hb', hbb'⟩ := hb
    have : b' = b := Subtype.ext hbb'
    subst this
    exact hyF' _ hb'

end CFSG.RankThree.PartTwo.Sec19
