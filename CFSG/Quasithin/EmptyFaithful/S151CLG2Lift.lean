module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporLift
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParDef
public import CFSG.Quasithin.EmptyFaithful.SBc6Sl2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtL2BlockData
public import CFSG.Fischer.Classification.Recognition.Main
public import CFSG.RankThree.PartOne.S11d.Common
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2

public section

namespace CFSG.Quasithin.CLG2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin
open CFSG.QuasithinUnique.Vol2Native.L239

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G]

@[expose] def liftQ (L : Subgroup G) (A : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) : Subgroup G :=
  (A.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).map L.subtype

theorem mem_liftQ {L : Subgroup G} {A : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)} {g : G} :
    g ∈ liftQ L A ↔ ∃ hg : g ∈ L, (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ⟨g, hg⟩ ∈ A := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l.2, hl⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem liftQ_le (L : Subgroup G) (A : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) : liftQ L A ≤ L := by
  rintro _ ⟨l, -, rfl⟩
  exact l.2

theorem exists_induced_aut {L R : Subgroup G} (hRN : R ≤ Subgroup.normalizer (L : Set G))
    {r : G} (hr : r ∈ R) :
    ∃ cbar : MulAut (↥L ⧸ CFSG.pCore 2 ↥L),
      (((R ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).map cbar.toMonoidHom =
        ((R ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ∧
      ∀ l : ↥L, cbar (QuotientGroup.mk' (CFSG.pCore 2 ↥L) l) =
        QuotientGroup.mk' (CFSG.pCore 2 ↥L) (L.normalizerMonoidHom ⟨r, hRN hr⟩ l) := by
  set θ := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hθ
  have hθs : Function.Surjective θ := QuotientGroup.mk'_surjective _
  set c : MulAut ↥L := L.normalizerMonoidHom ⟨r, hRN hr⟩ with hc
  have hkerc : θ.ker.comap c.toMonoidHom = θ.ker := by
    rw [hθ, QuotientGroup.ker_mk']
    exact Subgroup.Characteristic.fixed (H := CFSG.pCore 2 ↥L) inferInstance c
  obtain ⟨cbar, hcbar⟩ := exists_induced_mulAut θ hθs c hkerc
  refine ⟨cbar, ?_, hcbar⟩
  set SL : Subgroup ↥L := (R ⊓ L).subgroupOf L with hSL
  have hSc : SL.map c.toMonoidHom = SL := by
    ext y
    constructor
    · rintro ⟨l, hl, rfl⟩
      have hl' : (l : G) ∈ R ⊓ L := hl
      have : ((c l : ↥L) : G) ∈ R ⊓ L :=
        ⟨(conj_mem_sylow_iff hRN hr l).2 hl'.1, (c l).2⟩
      exact this
    · intro hy
      have hy' : (y : G) ∈ R ⊓ L := hy
      refine ⟨c.symm y, ?_, by simp⟩
      have h1 : ((c (c.symm y) : ↥L) : G) ∈ R := by simpa using hy'.1
      show ((c.symm y : ↥L) : G) ∈ R ⊓ L
      exact ⟨(conj_mem_sylow_iff hRN hr (c.symm y)).1 h1, (c.symm y).2⟩
  have : cbar.toMonoidHom.comp θ = θ.comp c.toMonoidHom := by
    ext l
    exact hcbar l
  rw [Subgroup.map_map, this, ← Subgroup.map_map, hSc]

theorem normalizes_liftQ {L R : Subgroup G} (hRN : R ≤ Subgroup.normalizer (L : Set G))
    {A : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)}
    (hinv : ∀ α : MulAut (↥L ⧸ CFSG.pCore 2 ↥L),
      (((R ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).map α.toMonoidHom =
        ((R ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) →
        A.map α.toMonoidHom = A) :
    R ≤ Subgroup.normalizer (liftQ L A : Set G) := by
  set θ := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hθ
  have hkey : ∀ r ∈ R, ∀ g ∈ liftQ L A, r * g * r⁻¹ ∈ liftQ L A := by
    intro r hr g hg
    obtain ⟨hgL, hgA⟩ := mem_liftQ.1 hg
    obtain ⟨cbar, hS, hcbar⟩ := exists_induced_aut hRN hr
    have hAc := hinv cbar hS
    have hgL' : r * g * r⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hRN hr) g).1 hgL
    refine mem_liftQ.2 ⟨hgL', ?_⟩
    have h1 : θ ⟨r * g * r⁻¹, hgL'⟩ = cbar (θ ⟨g, hgL⟩) := by
      rw [hcbar]
      rfl
    have h2 : cbar (θ ⟨g, hgL⟩) ∈ A.map cbar.toMonoidHom := ⟨θ ⟨g, hgL⟩, hgA, rfl⟩
    rw [hAc] at h2
    rw [h1]
    exact h2
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨hkey r hr g, fun hg => ?_⟩
  have := hkey r⁻¹ (R.inv_mem hr) _ hg
  simpa [mul_assoc] using this

theorem goodLocal_liftQ {L : Subgroup G} {A : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)}
    (hA : GoodLocal A) : CharTwo (liftQ L A) ∧ ¬ HasChi0Block (liftQ L A) := by
  set θ := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hθ
  have hθs : Function.Surjective θ := QuotientGroup.mk'_surjective _
  have hNker2 : IsPGroup 2 θ.ker := by
    rw [hθ, QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  let φ : ↥(liftQ L A) →* ↥A :=
    { toFun := fun g => ⟨θ ⟨g.1, (mem_liftQ.1 g.2).1⟩, (mem_liftQ.1 g.2).2⟩
      map_one' := Subtype.ext (map_one θ)
      map_mul' := fun a b => Subtype.ext (map_mul θ ⟨a.1, (mem_liftQ.1 a.2).1⟩
        ⟨b.1, (mem_liftQ.1 b.2).1⟩) }
  have hφs : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨l, rfl⟩ := hθs y
    have hlK : (l : G) ∈ liftQ L A := mem_liftQ.2 ⟨l.2, hy⟩
    exact ⟨⟨l, hlK⟩, rfl⟩
  have hφk : IsPGroup 2 φ.ker := by
    intro k
    have hk : θ ⟨(k : ↥(liftQ L A)).1, (mem_liftQ.1 (k : ↥(liftQ L A)).2).1⟩ = 1 := by
      have := k.2
      rw [MonoidHom.mem_ker] at this
      exact congrArg Subtype.val this
    have hmemker : (⟨(k : ↥(liftQ L A)).1, (mem_liftQ.1 (k : ↥(liftQ L A)).2).1⟩ : ↥L) ∈
        θ.ker := hk
    obtain ⟨n, hn⟩ := hNker2 ⟨_, hmemker⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun y : ↥θ.ker => ((y : ↥L) : G)) hn
    simpa using this
  exact hA G _ φ hφs hφk

theorem four_le_pow_two {m : ℕ} (hm : 2 ≤ m) : 4 ≤ 2 ^ m :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm

theorem ker_eq_pCore_of_sl2 {H : Type} [Group H] [Finite H] {F : Type} [Field F] [Finite F]
    [CharP F 2] (h4 : 4 ≤ Nat.card F) (ψ : H →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hs : Function.Surjective ψ) (hk : IsPGroup 2 ψ.ker) : ψ.ker = CFSG.pCore 2 H := by
  have hsimple : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.QuasithinUnique.Vol2Native.A312L.sl2_isSimple
      (CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four h4)
  apply le_antisymm
  · exact le_sSup ⟨ψ.normal_ker, hk⟩
  · have hnorm : ((CFSG.pCore 2 H).map ψ).Normal :=
      (CFSG.pCore_normal (G := H) (p := 2)).map ψ hs
    have := hnorm
    rcases hsimple.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 H).map ψ) with h | h
    · intro x hx
      rw [MonoidHom.mem_ker]
      have : ψ x ∈ (CFSG.pCore 2 H).map ψ := ⟨x, hx, rfl⟩
      rw [h] at this
      exact Subgroup.mem_bot.mp this
    · exfalso
      apply S151S4.sl2_not_isPGroup F h4
      have hp : IsPGroup 2 ↥((CFSG.pCore 2 H).map ψ) :=
        (CFSG.pCore_isPGroup (G := H) (p := 2)).map ψ
      rw [h] at hp
      exact hp.of_equiv Subgroup.topEquiv

theorem isPSL_of_equiv_sl2 {X : Type} [Group X] {F : Type} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hF : Nat.card F = 2 ^ m) (hm : 2 ≤ m)
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 2) F) : IsPSL 2 2 m X := by
  have h4 := four_le_pow_two hm
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, F, inferInstance, inferInstance, hF,
    ⟨e.trans (((QuotientGroup.quotientMulEquivOfEq (S151S4.center_sl2_eq_bot F)).trans
      QuotientGroup.quotientBot).symm.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F))⟩⟩
  · intro h
    have h2 : 2 ^ m = 2 := congrArg Prod.snd h
    exact absurd (h2 ▸ h4) (by norm_num)
  · intro h
    have h2 : 2 ^ m = 3 := congrArg Prod.snd h
    exact absurd (h2 ▸ h4) (by norm_num)

theorem isQuasisimple_of_isPSL_two_two {X : Type} [Group X] [Finite X] {m : ℕ} (hm : 2 ≤ m)
    (h : IsPSL 2 2 m X) : CFSG.IsQuasisimple X := by
  have hs : IsSimpleGroup X := SBc6.isSimpleGroup_of_psl (by omega) h
  have hnc := L246.nonab_of_isPSL h
  have hq := CFSG.Fischer.Classification.Recognition.isQuasisimple_of_isSimpleGroup hnc
  exact CFSG.RankThree.PartOne.S11d.isQuasisimple_of_perfect_of_simple ⟨hq.1⟩ hq.2

theorem sl2_quotient {H : Type} [Group H] [Finite H] {F : Type} [Field F] [Finite F]
    [CharP F 2] {m : ℕ} (hF : Nat.card F = 2 ^ m) (hm : 2 ≤ m)
    (ψ : H →* Matrix.SpecialLinearGroup (Fin 2) F) (hs : Function.Surjective ψ)
    (hk : IsPGroup 2 ψ.ker) :
    IsPSL 2 2 m (H ⧸ CFSG.pCore 2 H) ∧ CFSG.IsQuasisimple (H ⧸ CFSG.pCore 2 H) := by
  have h4 : 4 ≤ Nat.card F := hF ▸ four_le_pow_two hm
  have hker := ker_eq_pCore_of_sl2 h4 ψ hs hk
  have e : (H ⧸ CFSG.pCore 2 H) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hs)
  have hpsl := isPSL_of_equiv_sl2 hF hm e
  exact ⟨hpsl, isQuasisimple_of_isPSL_two_two hm hpsl⟩


section PerfectCore

variable {L : Subgroup G}

theorem map_perfectCore_comap (A : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) :
    (perfectCore (A.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥L)))).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = perfectCore A := by
  rw [map_perfectCore, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]

theorem perfectCore_liftQ (A : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) :
    perfectCore (liftQ L A) =
      (perfectCore (A.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥L)))).map L.subtype :=
  (map_perfectCore L.subtype _).symm

theorem exists_hom_perfectCore (A : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) :
    ∃ ρ : ↥(perfectCore (liftQ L A)) →* ↥(perfectCore A),
      Function.Surjective ρ ∧ IsPGroup 2 ρ.ker := by
  set θ := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hθ
  have hxL : ∀ x : ↥(perfectCore (liftQ L A)), (x : G) ∈ L := fun x =>
    liftQ_le L A (perfectCore_le _ x.2)
  have hxA : ∀ x : ↥(perfectCore (liftQ L A)), θ ⟨x, hxL x⟩ ∈ perfectCore A := by
    rintro ⟨x, hx⟩
    rw [perfectCore_liftQ] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have : θ y ∈ (perfectCore (A.comap θ)).map θ := ⟨y, hy, rfl⟩
    rw [hθ, map_perfectCore_comap] at this
    exact this
  let ρ : ↥(perfectCore (liftQ L A)) →* ↥(perfectCore A) :=
    { toFun := fun x => ⟨θ ⟨x.1, hxL x⟩, hxA x⟩
      map_one' := Subtype.ext (map_one θ)
      map_mul' := fun a b => Subtype.ext (map_mul θ ⟨a.1, hxL a⟩ ⟨b.1, hxL b⟩) }
  have hρs : Function.Surjective ρ := by
    rintro ⟨z, hz⟩
    rw [← map_perfectCore_comap] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    refine ⟨⟨(y : G), ?_⟩, rfl⟩
    rw [perfectCore_liftQ]
    exact ⟨y, hy, rfl⟩
  have hNker2 : IsPGroup 2 θ.ker := by
    rw [hθ, QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  refine ⟨ρ, hρs, fun k => ?_⟩
  have hk : θ ⟨(k : ↥(perfectCore (liftQ L A))).1, hxL k⟩ = 1 := by
    have := k.2
    rw [MonoidHom.mem_ker] at this
    exact congrArg Subtype.val this
  have hmemker : (⟨(k : ↥(perfectCore (liftQ L A))).1, hxL k⟩ : ↥L) ∈ θ.ker := hk
  obtain ⟨n, hn⟩ := hNker2 ⟨_, hmemker⟩
  refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg (fun y : ↥θ.ker => ((y : ↥L) : G)) hn
  simpa using this

theorem perfectCore_liftQ_levi {A : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)} (hA : Rk2.Rank2Levi A) :
    ∃ m : ℕ, 2 ≤ m ∧
      IsPSL 2 2 m (↥(perfectCore (liftQ L A)) ⧸ CFSG.pCore 2 ↥(perfectCore (liftQ L A))) ∧
      CFSG.IsQuasisimple
        (↥(perfectCore (liftQ L A)) ⧸ CFSG.pCore 2 ↥(perfectCore (liftQ L A))) := by
  obtain ⟨F, hF, hFin, hCh, m, hFm, hm, g, hg, hker⟩ := hA
  obtain ⟨ρ, hρs, hρk⟩ := exists_hom_perfectCore (L := L) A
  have hk : IsPGroup 2 (g.comp ρ).ker := by
    rw [← MonoidHom.comap_ker]
    exact hker.comap_of_ker_isPGroup ρ hρk
  exact ⟨m, hm, sl2_quotient hFm hm (g.comp ρ) (hg.comp hρs) hk⟩

theorem map_pCore_subtype (L : Subgroup G) :
    (CFSG.pCore 2 ↥L).map L.subtype = pCoreOf 2 L := by
  rfl

theorem le_sup_perfectCore_liftQ {R : Subgroup G} {A₀ A₁ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)}
    (hsup : perfectCore A₀ ⊔ perfectCore A₁ ⊔
      ((R ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = ⊤)
    (hR : pCoreOf 2 L ≤ R) :
    L ≤ perfectCore (liftQ L A₀) ⊔ perfectCore (liftQ L A₁) ⊔ (R ⊓ L) := by
  set θ := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hθ
  set W : Subgroup ↥L := perfectCore (A₀.comap θ) ⊔ perfectCore (A₁.comap θ) ⊔
    (R ⊓ L).subgroupOf L with hW
  have hWm : W.map θ = ⊤ := by
    rw [hW, Subgroup.map_sup, Subgroup.map_sup, hθ, map_perfectCore_comap, map_perfectCore_comap]
    exact hsup
  have hWk : W ⊔ θ.ker = ⊤ := by
    have := Subgroup.comap_map_eq θ W
    rw [hWm, Subgroup.comap_top] at this
    exact this.symm
  intro x hx
  have hx' : (⟨x, hx⟩ : ↥L) ∈ W ⊔ θ.ker := hWk ▸ Subgroup.mem_top _
  have hmap : (W ⊔ θ.ker).map L.subtype ≤
      perfectCore (liftQ L A₀) ⊔ perfectCore (liftQ L A₁) ⊔ (R ⊓ L) := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [hW, Subgroup.map_sup, Subgroup.map_sup, ← perfectCore_liftQ, ← perfectCore_liftQ,
        Subgroup.map_subgroupOf_eq_of_le inf_le_right]
    · rw [hθ, QuotientGroup.ker_mk', map_pCore_subtype]
      exact (le_inf hR (CFSG.LieType.BorelTits.pCoreOf_le 2 L)).trans le_sup_right
  exact hmap ⟨⟨x, hx⟩, hx', rfl⟩

end PerfectCore

end CFSG.Quasithin.CLG2
