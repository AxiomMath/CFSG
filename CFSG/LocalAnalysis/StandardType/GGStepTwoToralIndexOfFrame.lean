module

public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralLatIndex
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoToralRestTagsWeyl
public import CFSG.LocalAnalysis.StandardType.GGExcKnownGroups

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType

namespace StepTwoToralIndex

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank
open CFSG.LinearAlgebra.CoprimeActions.PermutationFunctionFixedDimension (fixedSpace)

section Orbit

variable {N p : ℕ}

theorem latLinked_latPerm {S : Matrix (Fin N) (Fin N) ℤ} {π : Equiv.Perm (Fin N)}
    (hGram : ∀ α β, latGram S (latPerm π α) (latPerm π β) = latGram S α β)
    {Φ : Set (Fin N → ℤ)} (hΦ : ∀ γ ∈ Φ, latPerm π γ ∈ Φ) {a b : Fin N → ℤ}
    (h : latLinked S Φ a b) : latLinked S Φ (latPerm π a) (latPerm π b) := by
  induction h with
  | rel x y hxy =>
    refine Relation.EqvGen.rel _ _ ⟨hΦ x hxy.1, hΦ y hxy.2.1, ?_⟩
    rw [hGram]
    exact hxy.2.2
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

theorem latLinked_mem_iff {S : Matrix (Fin N) (Fin N) ℤ} {Φ : Set (Fin N → ℤ)}
    {a b : Fin N → ℤ} (h : latLinked S Φ a b) : a ∈ Φ ↔ b ∈ Φ := by
  induction h with
  | rel x y hxy => exact ⟨fun _ => hxy.2.1, fun _ => hxy.1⟩
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

theorem latChar_latPerm {π : Equiv.Perm (Fin N)} {g : Fin N → ZMod p}
    (hg : ∀ i, g (π i) = g i) (α : Fin N → ℤ) :
    latChar p g (latPerm π α) = latChar p g α := by
  simp only [latChar, latPerm]
  rw [← Equiv.sum_comp π (fun i => (α (π.symm i) : ZMod p) * g i)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Equiv.symm_apply_apply, hg j]

theorem isCompOrbit_stable {S : Matrix (Fin N) (Fin N) ℤ} {π : Equiv.Perm (Fin N)}
    (hGram : ∀ α β, latGram S (latPerm π α) (latPerm π β) = latGram S α β)
    {R : Set (Fin N → ℤ)} (hR : ∀ β ∈ R, latPerm π β ∈ R) {g : Fin N → ZMod p}
    (hg : ∀ i, g (π i) = g i) {O : Set (Fin N → ℤ)}
    (h : IsCompOrbit S π (latPhi R p g) O) : O ⊆ R ∧ ∀ β ∈ O, latPerm π β ∈ O := by
  have hΦ : ∀ γ ∈ latPhi R p g, latPerm π γ ∈ latPhi R p g := fun γ hγ =>
    ⟨hR γ hγ.1, by rw [latChar_latPerm hg]; exact hγ.2⟩
  obtain ⟨α, hα, rfl⟩ := h
  have hiter : ∀ k : ℕ, (latPerm π)^[k] α ∈ latPhi R p g := by
    intro k
    induction k with
    | zero => exact hα
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact hΦ _ ih
  refine ⟨?_, ?_⟩
  · rintro β ⟨k, hk⟩
    exact ((latLinked_mem_iff hk).mp (hiter k)).1
  · rintro β ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    rw [Function.iterate_succ_apply']
    exact latLinked_latPerm hGram hΦ hk

end Orbit

section Frame

variable {G : Type} [Group G] {U' : Type} [Group U'] {p : ℕ} {Bs G₀ : Subgroup G}
  {Δ : UniversalRootDatum U'} {S : Matrix (Fin Δ.rank) (Fin Δ.rank) ℤ}
  {π : Equiv.Perm (Fin Δ.rank)} {f : ℕ}

theorem card_coord_preimage [Fact p.Prime] (F : GGStdForm p Bs G₀ Δ S π f)
    (hspan : ∀ g : Fin Δ.rank → ZMod p, g ∈ LatCorootSpan Δ p)
    (X : Submodule (ZMod p) (Fin Δ.rank → ZMod p)) (hX : X ≤ fixedSpace (ZMod p) π) :
    Nat.card {b : Bs // Multiplicative.toAdd (F.coord b) ∈ X} =
      p ^ Module.finrank (ZMod p) X := by
  have e : {b : Bs // Multiplicative.toAdd (F.coord b) ∈ X} ≃ X := by
    refine Equiv.ofBijective (fun b => ⟨Multiplicative.toAdd (F.coord b.1), b.2⟩) ⟨?_, ?_⟩
    · intro a b hab
      have h := congrArg Subtype.val hab
      exact Subtype.ext (F.coord_inj (Multiplicative.toAdd.injective h))
    · rintro ⟨x, hx⟩
      obtain ⟨b, hb⟩ := F.coord_surj x (hspan x) (hX hx)
      exact ⟨⟨b, hb ▸ hx⟩, Subtype.ext hb⟩
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]

theorem card_inf_centralizer_stdForm [Fact p.Prime] (F : GGStdForm p Bs G₀ Δ S π f)
    (hspan : ∀ g : Fin Δ.rank → ZMod p, g ∈ LatCorootSpan Δ p) {L : Subgroup G}
    {O : Set (Fin Δ.rank → ℤ)}
    (hcent : ∀ b' : Bs, (b' : G) ∈ Subgroup.centralizer (L : Set G) ↔
      ∀ α ∈ O, latChar p (Multiplicative.toAdd (F.coord b')) α = 0) :
    Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) =
      p ^ Module.finrank (ZMod p) ↥(fixedSpace (ZMod p) π ⊓ rootAnnihilator p O) := by
  rw [← card_coord_preimage F hspan (fixedSpace (ZMod p) π ⊓ rootAnnihilator p O) inf_le_left]
  refine Nat.card_congr
    { toFun := fun x => ⟨⟨x, x.2.1⟩, F.coord_fixed _, (hcent ⟨x, x.2.1⟩).mp x.2.2⟩
      invFun := fun y => ⟨y.1.1, y.1.2, (hcent y.1).mpr y.2.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

theorem mem_sup_of_coord_mem [Fact p.Prime] (F : GGStdForm p Bs G₀ Δ S π f)
    (hspan : ∀ g : Fin Δ.rank → ZMod p, g ∈ LatCorootSpan Δ p) {L₁ : Subgroup G} {b : G}
    (hb : b ∈ Bs) {A : Submodule (ZMod p) (Fin Δ.rank → ZMod p)} (hAV : A ≤ fixedSpace (ZMod p) π)
    (hAL : ∀ b' : Bs, Multiplicative.toAdd (F.coord b') ∈ A → (b' : G) ∈ L₁) (x : Bs)
    (hx : Multiplicative.toAdd (F.coord x) ∈
      Submodule.span (ZMod p) {Multiplicative.toAdd (F.coord ⟨b, hb⟩)} ⊔ A) :
    (x : G) ∈ Subgroup.zpowers b ⊔ L₁ := by
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
  obtain ⟨bz, hbz⟩ := F.coord_surj z (hspan z) (hAV hz)
  have hbzL : (bz : G) ∈ L₁ := hAL bz (hbz ▸ hz)
  have hxe : x = (⟨b, hb⟩ : Bs) ^ a.val * bz := by
    apply F.coord_inj
    apply Multiplicative.toAdd.injective
    rw [map_mul, map_pow, toAdd_mul, toAdd_pow, hbz, ← hyz, ← ZMod.natCast_zmod_val a,
      Nat.cast_smul_eq_nsmul]
    simp
  rw [hxe]
  exact Subgroup.mul_mem_sup ((Subgroup.zpowers b).pow_mem (Subgroup.mem_zpowers b) _) hbzL

end Frame

section Config

theorem not_dvd_det_cartan_exc {t : StatedLieTag} (ht : GGExcFive t) (f : ℕ) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hW : ¬ p ∣ ggExcWeylOrder t) :
    ¬ (p : ℤ) ∣ (ggU (absTag t) 6 f).D.cartan.det := by
  have hone : ¬ (p : ℤ) ∣ 1 := by
    intro h
    have h' : p ∣ 1 := by exact_mod_cast h
    exact hp.one_lt.ne' (Nat.dvd_one.mp h')
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · rw [show (ggU (absTag .F4) 6 f).D.cartan.det = 1 from det_cartan_F4]
    exact hone
  · rw [show (ggU (absTag .E6) 6 f).D.cartan.det = 3 from det_cartan_E6]
    intro h
    have h' : p ∣ 3 := by exact_mod_cast h
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h'
    exact hW (by norm_num [ggExcWeylOrder])
  · rw [show (ggU (absTag .E7) 6 f).D.cartan.det = 2 from det_cartan_E7]
    intro h
    have h' : p ∣ 2 := by exact_mod_cast h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
  · rw [show (ggU (absTag .E8) 6 f).D.cartan.det = 1 from det_cartan_E8]
    exact hone
  · rw [show (ggU (absTag .twistedE6) 6 f).D.cartan.det = 3 from det_cartan_E6]
    intro h
    have h' : p ∣ 3 := by exact_mod_cast h
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h'
    exact hW (by norm_num [ggExcWeylOrder])

theorem four_le_card_B {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {Δ : UniversalRootDatum U}
    {t : StatedLieTag} {n f : ℕ} {ψ : U →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) : p ^ 4 ≤ Nat.card B := by
  have hB : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.sstar.1.2.1
  have h4 : 4 ≤ LargeEvenTwoLocalRank p G := hctx.beta.2.2.2
  rw [hB]
  exact Nat.pow_le_pow_right hctx.prime.pos h4

end Config

section Index

open scoped Matrix in
theorem index_of_frame (hF : GGExcKGToralFrame) (hR0 : GGExcRegimeInput) {t : StatedLieTag}
    (ht : GGExcFive t) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ}
    {ψ : (ggU t n f).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ) (s1 : GGSixStepOne p B Bs x L D J)
    (hW : ¬ p ∣ ggExcWeylOrder t) {b : G} {L₁ : Subgroup G}
    (hpair : GGStepTwoPair p B Bs x L D J b L₁) :
    Nat.card Bs ≤ p * Nat.card ↥(Bs ⊓ (Subgroup.zpowers b ⊔ L₁)) := by
  classical
  have hp : p.Prime := hctx.prime
  have hp2 : p ≠ 2 := hctx.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  have hks : GGKnownSetting t n f ψ := ggKnownSetting_of_ctx hctx s1
  have hreg : GGExcRegime p f := hR0 G p B Bs x L D J t n f ψ ht hctx s1
  have hcard : p ^ 4 ≤ Nat.card Bs :=
    (four_le_card_B hctx).trans (Subgroup.card_le_of_le hctx.bstar.1)
  have hBsN : Bs ≤ Subgroup.normalizer (ψ.range : Set G) := by
    rw [hctx.range_eq]; exact hctx.bstar_le_normalizer
  have hinn : ∀ b ∈ (Bs : Subgroup G), GGPsiInnerDiag (ggU t n f).D ψ b :=
    hctx.2.2.2.2.2.2.1.2
  have hsyl : ∃ P : Sylow p (Subgroup.normalizer (ψ.range : Set G)),
      Bs ≤ (P : Subgroup (Subgroup.normalizer (ψ.range : Set G))).map
        (Subgroup.normalizer (ψ.range : Set G)).subtype ∧
      ∀ E : Subgroup G, E ≤ (P : Subgroup (Subgroup.normalizer (ψ.range : Set G))).map
        (Subgroup.normalizer (ψ.range : Set G)).subtype →
        IsElemAbelian p E → Nat.card E = Nat.card Bs → E = Bs := by
    have hnorm : Subgroup.normalizer (ψ.range : Set G) =
        Subgroup.normalizer (ggG0 p B x L D J : Set G) := by rw [hctx.range_eq]
    exact hnorm.symm ▸ s1.2.2.2.1
  obtain ⟨S, π, F, ⟨hRG, hDA, -, -, -, -, -⟩, -, hA, -⟩ :=
    hF t n f ht G ψ hks p hp hp2 hreg Bs hctx.bstar.2.1 hcard hBsN hinn hsyl
  obtain ⟨hbBs, hb1, hcomp, hcardC⟩ := hpair
  have hb1' : (⟨b, hbBs⟩ : Bs) ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  have hcomp' : IsComponentOf L₁ (ψ.range ⊓ Subgroup.centralizer {((⟨b, hbBs⟩ : Bs) : G)}) := by
    rw [hctx.range_eq]; exact hcomp
  obtain ⟨O, hOorb, hOcent, hOeig⟩ := hA ⟨b, hbBs⟩ hb1' L₁ hcomp'
  have hdet := not_dvd_det_cartan_exc ht f hp hp2 hW
  have hspan : ∀ g : Fin (ggU (absTag t) 6 f).D.rank → ZMod p,
      g ∈ LatCorootSpan (ggU (absTag t) 6 f).D p := fun g =>
    latCorootSpan_eq_top (ggU (absTag t) 6 f).D p hp hdet g
  have hGram := latGram_latPerm_exc t f ht S hRG π hDA
  obtain ⟨hOR, hπO⟩ := isCompOrbit_stable hGram
    (fun β hβ => latPerm_mem_roots_exc t f ht π hDA hβ) (F.coord_fixed ⟨b, hbBs⟩) hOorb
  obtain ⟨A, hAV, hAeig, hAP, hdim⟩ :=
    exists_complement_exc ht f hp2 hW S hRG π hDA O hOR hπO
  have hAL : ∀ b' : Bs, Multiplicative.toAdd (F.coord b') ∈ A → (b' : G) ∈ L₁ := fun b' hb' =>
    hOeig b' (hAeig hb')
  have hVP : Module.finrank (ZMod p) ↥(fixedSpace (ZMod p) π ⊓ rootAnnihilator p O) ≤ 2 := by
    have h1 := card_inf_centralizer_stdForm F hspan hOcent
    have h2 : p ^ Module.finrank (ZMod p) ↥(fixedSpace (ZMod p) π ⊓ rootAnnihilator p O) ≤ p ^ 2 :=
      h1 ▸ hcardC
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h2
  have hcV : Multiplicative.toAdd (F.coord ⟨b, hbBs⟩) ∈ fixedSpace (ZMod p) π :=
    F.coord_fixed ⟨b, hbBs⟩
  have hbC : ((⟨b, hbBs⟩ : Bs) : G) ∈ Subgroup.centralizer (L₁ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcomp.1 hl).2
  have hcP : Multiplicative.toAdd (F.coord ⟨b, hbBs⟩) ∈ rootAnnihilator p O :=
    (hOcent ⟨b, hbBs⟩).mp hbC
  have hc0 : Multiplicative.toAdd (F.coord ⟨b, hbBs⟩) ≠ 0 := by
    intro h0
    apply hb1'
    apply F.coord_inj
    apply Multiplicative.toAdd.injective
    simpa using h0
  have hTV : Submodule.span (ZMod p) {Multiplicative.toAdd (F.coord ⟨b, hbBs⟩)} ⊔ A ≤
      fixedSpace (ZMod p) π :=
    sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hcV) hAV
  have hcA : Submodule.span (ZMod p) {Multiplicative.toAdd (F.coord ⟨b, hbBs⟩)} ⊓ A = ⊥ := by
    refine eq_bot_iff.mpr fun y hy => ?_
    obtain ⟨hy1, hy2⟩ := hy
    have hyP : y ∈ rootAnnihilator p O := by
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy1
      exact (rootAnnihilator p O).smul_mem a hcP
    have hy' : y ∈ A ⊓ rootAnnihilator p O := ⟨hy2, hyP⟩
    rwa [hAP] at hy'
  have hdimT : Module.finrank (ZMod p)
      ↥(Submodule.span (ZMod p) {Multiplicative.toAdd (F.coord ⟨b, hbBs⟩)} ⊔ A) =
        Module.finrank (ZMod p) A + 1 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq
      (Submodule.span (ZMod p) {Multiplicative.toAdd (F.coord ⟨b, hbBs⟩)}) A
    rw [hcA, finrank_bot, finrank_span_singleton hc0] at h1
    omega
  have hcardBs : Nat.card Bs = p ^ Module.finrank (ZMod p) (fixedSpace (ZMod p) π) := by
    rw [← card_coord_preimage F hspan (fixedSpace (ZMod p) π) le_rfl]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv fun b => F.coord_fixed b).symm
  have hcardT := card_coord_preimage F hspan _ hTV
  have hle : Nat.card {x : Bs // Multiplicative.toAdd (F.coord x) ∈
        Submodule.span (ZMod p) {Multiplicative.toAdd (F.coord ⟨b, hbBs⟩)} ⊔ A} ≤
      Nat.card ↥(Bs ⊓ (Subgroup.zpowers b ⊔ L₁)) := by
    refine Nat.card_le_card_of_injective
      (fun x => ⟨x.1.1, x.1.2, mem_sup_of_coord_mem F hspan hbBs hAV hAL x.1 x.2⟩) ?_
    intro x y hxy
    have h := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h)
  calc Nat.card Bs = p ^ Module.finrank (ZMod p) (fixedSpace (ZMod p) π) := hcardBs
    _ ≤ p ^ (Module.finrank (ZMod p)
        ↥(Submodule.span (ZMod p) {Multiplicative.toAdd (F.coord ⟨b, hbBs⟩)} ⊔ A) + 1) :=
      Nat.pow_le_pow_right hp.pos (by omega)
    _ = p * p ^ Module.finrank (ZMod p)
        ↥(Submodule.span (ZMod p) {Multiplicative.toAdd (F.coord ⟨b, hbBs⟩)} ⊔ A) := by ring
    _ = p * Nat.card {x : Bs // Multiplicative.toAdd (F.coord x) ∈
        Submodule.span (ZMod p) {Multiplicative.toAdd (F.coord ⟨b, hbBs⟩)} ⊔ A} := by
      rw [hcardT]
    _ ≤ p * Nat.card ↥(Bs ⊓ (Subgroup.zpowers b ⊔ L₁)) := Nat.mul_le_mul_left p hle

end Index

end StepTwoToralIndex

section Main

open StepTwoToralIndex CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

theorem ggStepTwoExcIndexNonsplitOn_of_frame (hF : GGExcKGToralFrame) (hR0 : GGExcRegimeInput)
    {t : StatedLieTag} (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) :
    GGStepTwoExcIndexNonsplitOn t := by
  have hexc : GGExcFive t := by
    rcases ht with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  intro G _ _ p B Bs x L D J n f ψ hctx s1 hW _ b L₁ hpair
  exact index_of_frame hF hR0 hexc hctx s1 hW hpair

theorem ggStepTwoExcIndexOn_twistedE6_of_frame (hF : GGExcKGToralFrame) (hR0 : GGExcRegimeInput) :
    GGStepTwoExcIndexOn .twistedE6 := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 hW b L₁ hpair
  exact index_of_frame hF hR0 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hctx s1 hW hpair

end Main

end CFSG.StandardType
