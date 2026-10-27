module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenWeylLift
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenKernel
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerCore
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenLift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

variable {G : Type} [Group G] [Finite G]

theorem exists_overGamma_of_weylReflSet {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs K : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hW : ggAutomizer (MulAut.conj : ↥K →* MulAut ↥K).range (ggGamma K hN).range ≤
      Subgroup.closure (ggTorusReflSet p (ggGamma K hN).range)) :
    ∀ a ∈ ggAutomizer (MulAut.conj : ↥K →* MulAut ↥K).range (ggGamma K hN).range,
      ∃ c ∈ Subgroup.closure {φ : MulAut ↥Bs | φ ∈ ggAutomizer K Bs ∧ GGIsReflection p φ},
        GGOverGamma hN c a := by
  classical
  let A : Subgroup (MulAut ↥K) := (ggGamma K hN).range
  let S : Set (MulAut ↥Bs) := {φ | φ ∈ ggAutomizer K Bs ∧ GGIsReflection p φ}
  let Cl : Subgroup (MulAut ↥Bs) := Subgroup.closure S
  let Sig : Subgroup (MulAut ↥A) :=
  { carrier := {a | ∃ c ∈ Cl, GGOverGamma hN c a}
    one_mem' := ⟨1, Cl.one_mem, GGOverGamma.one⟩
    mul_mem' := by
      rintro a b ⟨c, hc, h⟩ ⟨d, hd, h'⟩
      exact ⟨c * d, Cl.mul_mem hc hd, h.mul h'⟩
    inv_mem' := by
      rintro a ⟨c, hc, h⟩
      exact ⟨c⁻¹, Cl.inv_mem hc, h.inv⟩ }
  have hstep1 : Subgroup.closure (ggTorusReflSet p A) ≤ Sig := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro φ ⟨n, hn, hnW, rfl, hrefl⟩
    obtain ⟨g, hgK, hg, hrefl', hover⟩ :=
      exists_isReflection_overGamma_of_weylElt hp hp2 hBs hSC hN hnW hn hrefl
    exact ⟨ggConjAut Bs hg,
      Subgroup.subset_closure ⟨ggConjAut_mem_ggAutomizer hgK hg, hrefl'⟩, hover⟩
  intro a ha
  obtain ⟨c, hccl, hcover⟩ := (hW.trans hstep1) ha
  exact ⟨c, hccl, hcover⟩

theorem ggReflGenerated_of_weylReflSet {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs K : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hNoTr : GGNoTransvection p Bs) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hZ : Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ p)
    (hW : ggAutomizer (MulAut.conj : ↥K →* MulAut ↥K).range (ggGamma K hN).range ≤
      Subgroup.closure (ggTorusReflSet p (ggGamma K hN).range)) :
    GGReflGenerated p (ggAutomizer K Bs) := by
  classical
  let A : Subgroup (MulAut ↥K) := (ggGamma K hN).range
  let H : Subgroup (MulAut ↥K) := (MulAut.conj : ↥K →* MulAut ↥K).range
  let S : Set (MulAut ↥Bs) := {φ | φ ∈ ggAutomizer K Bs ∧ GGIsReflection p φ}
  let Cl : Subgroup (MulAut ↥Bs) := Subgroup.closure S
  change ggAutomizer K Bs = Cl
  apply le_antisymm
  ·
    intro φ hφ
    obtain ⟨g, hgK, hg, hφg⟩ := mem_ggAutomizer_iff.mp hφ
    have hφeq : φ = ggConjAut Bs hg := by
      apply MulEquiv.ext
      intro b
      apply Subtype.ext
      rw [ggConjAut_apply]
      exact hφg b
    let a : MulAut ↥A := ggConjAut A (conj_mem_normalizer_range_ggGamma hN hgK hg)
    have ha : a ∈ ggAutomizer H A :=
      ggConjAut_mem_ggAutomizer (H := H) (Bs := A)
        (g := MulAut.conj (⟨g, hgK⟩ : ↥K))
        (MonoidHom.mem_range.mpr ⟨⟨g, hgK⟩, rfl⟩)
        (conj_mem_normalizer_range_ggGamma hN hgK hg)
    obtain ⟨c, hccl, hcover⟩ := exists_overGamma_of_weylReflSet hp hp2 hBs hSC hN hW a ha
    have hoverφ : GGOverGamma hN φ a := by
      rw [hφeq]
      exact ggOverGamma_conjAut (hN := hN) hgK hg
    have hCle : Cl ≤ ggAutomizer K Bs :=
      (Subgroup.closure_le _).mpr (fun x hx => hx.1)
    have hκ : φ⁻¹ * c ∈ ggAutomizer K Bs :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hφ) (hCle hccl)
    have h1 : GGOverGamma hN (φ⁻¹ * c) 1 := by
      have h := hoverφ.inv.mul hcover
      rwa [inv_mul_cancel] at h
    have hκ1 : φ⁻¹ * c = 1 :=
      eq_one_of_ggOverGamma_one hp hBs hNoTr hN hZ hκ h1
    have hφc : φ = c := by
      have h' : φ * (φ⁻¹ * c) = φ := by rw [hκ1, mul_one]
      rw [← mul_assoc, mul_inv_cancel, one_mul] at h'
      exact h'.symm
    simpa [hφc] using hccl
  ·
    exact (Subgroup.closure_le _).mpr (fun φ hφ => hφ.1)

theorem ggTorusTBGroup_of_nbr {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K) (hK : commutator K = ⊤)
    {R : Type} [Group R] (θ : K ⧸ Subgroup.center K ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I)
    (hlift : GGTorusLift p r R) :
    GGTorusTBGroup p r R I K (ggQuotHom θ) (ggGamma K hN).range := by
  classical
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have := Fact.mk hp
  have hS : LargeEvenSHat p B y K := hnb.1
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := hBBs.trans hN
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hS.2.2.2.1
  set γ := ggGamma K hN with hγ
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ I, ∀ l : K, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta K θ hN b, hBsI b b.2, fun l => ggBeta_ggQuotHom K hN θ b l⟩
  have hcA := card_range_ggGamma_mul_of_sHat hp hS hBN
  have hle : Nat.card (ggGamma K hBN).range ≤ Nat.card γ.range := by
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, hBBs b.2⟩, rfl⟩
  have hr : p ^ r ≤ Nat.card γ.range := by
    have h1 := succ_le_twoLocalRank_of_torusLift hp hKy (hS.1.1.2 y hS.2.1) hS.2.2.1 hK θ hlift
    have h2 : p ^ (r + 1) ≤ Nat.card (ggGamma K hBN).range * p := by
      rw [hcA, hS.1.2.1]
      exact Nat.pow_le_pow_right hp.pos h1
    rw [pow_succ] at h2
    exact (Nat.le_of_mul_le_mul_right h2 hp.pos).trans hle
  have h3 : p ^ 3 ≤ Nat.card γ.range := by
    have h4 := pow_four_le_card_of_bmax hp hS.1 hcfg.1.2.2.2.2.2.1.2.2.2
    rw [← hcA, pow_succ] at h4
    exact (Nat.le_of_mul_le_mul_right h4 hp.pos).trans hle
  exact ⟨ggQuotHom_surjective θ, by rw [ker_ggQuotHom], hK, hA, hAI, hr, h3,
    ggTorusSelfCent_ggGamma hN hSC⟩

theorem exists_overGamma_of_ggTorusReflGenW {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K) (hK : commutator K = ⊤)
    {R : Type} [Group R] (θ : K ⧸ Subgroup.center K ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I)
    (hlift : GGTorusLift p r R) (hT : GGTorusReflGenW p r R I) :
    ∀ a ∈ ggAutomizer (MulAut.conj : ↥K →* MulAut ↥K).range (ggGamma K hN).range,
      ∃ c ∈ Subgroup.closure {φ : MulAut ↥Bs | φ ∈ ggAutomizer K Bs ∧ GGIsReflection p φ},
        GGOverGamma hN c a := by
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  exact exists_overGamma_of_weylReflSet hp hp2 hBs hSC hN
    (hT K (ggQuotHom θ) (ggGamma K hN).range
      (ggTorusTBGroup_of_nbr hcfg hnb hK θ hN hBsI hlift))

theorem existsUnique_overGamma_of_ggTorusReflGenW {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hNoTr : GGNoTransvection p Bs)
    {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K) (hK : commutator K = ⊤)
    {R : Type} [Group R] (θ : K ⧸ Subgroup.center K ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I)
    (hlift : GGTorusLift p r R) (hT : GGTorusReflGenW p r R I)
    (hZ : Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ p) :
    ∀ a ∈ ggAutomizer (MulAut.conj : ↥K →* MulAut ↥K).range (ggGamma K hN).range,
      ∃! c : MulAut ↥Bs, c ∈ ggAutomizer K Bs ∧ GGOverGamma hN c a := by
  intro a ha
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  obtain ⟨c, hcl, hover⟩ :=
    exists_overGamma_of_ggTorusReflGenW hcfg hnb hK θ hN hBsI hlift hT a ha
  have hCle : Subgroup.closure {φ : MulAut ↥Bs | φ ∈ ggAutomizer K Bs ∧ GGIsReflection p φ} ≤
      ggAutomizer K Bs := (Subgroup.closure_le _).mpr (fun φ hφ => hφ.1)
  refine ⟨c, ⟨hCle hcl, hover⟩, ?_⟩
  rintro d ⟨hd, hdover⟩
  have h1 : GGOverGamma hN (c⁻¹ * d) 1 := by
    have h := hover.inv.mul hdover
    rwa [inv_mul_cancel] at h
  have hκ : c⁻¹ * d ∈ ggAutomizer K Bs :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (hCle hcl)) hd
  exact (inv_mul_eq_one.mp (eq_one_of_ggOverGamma_one hp hBs hNoTr hN hZ hκ h1)).symm

theorem ggReflGenerated_of_ggTorusReflGenW {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hNoTr : GGNoTransvection p Bs)
    {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K) (hK : commutator K = ⊤)
    {R : Type} [Group R] (θ : K ⧸ Subgroup.center K ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I)
    (hlift : GGTorusLift p r R) (hT : GGTorusReflGenW p r R I)
    (hZ : Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ p) :
    GGReflGenerated p (ggAutomizer K Bs) := by
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  exact ggReflGenerated_of_weylReflSet hp hp2 hBs hSC hNoTr hN hZ
    (hT K (ggQuotHom θ) (ggGamma K hN).range
      (ggTorusTBGroup_of_nbr hcfg hnb hK θ hN hBsI hlift))

section Over

omit [Finite G] in
theorem exists_overGamma_of_mem_ggAutomizer {Bs X : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) {c : MulAut ↥Bs} (hc : c ∈ ggAutomizer X Bs) :
    ∃ a ∈ ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range (ggGamma X hN).range,
      GGOverGamma hN c a := by
  obtain ⟨g, hgX, hgN, hcg⟩ := mem_ggAutomizer_iff.mp hc
  have hc_eq : c = ggConjAut Bs hgN := MulEquiv.ext fun b => Subtype.ext (hcg b)
  subst hc_eq
  exact ⟨_, ggConjAut_mem_ggAutomizer (g := MulAut.conj (⟨g, hgX⟩ : ↥X))
    (MonoidHom.mem_range.mpr ⟨⟨g, hgX⟩, rfl⟩) (conj_mem_normalizer_range_ggGamma hN hgX hgN),
    ggOverGamma_conjAut hgX hgN⟩

private noncomputable def ggAutomizerGammaChoice {Bs X : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (c : ggAutomizer X Bs) :
    MulAut ↥(ggGamma X hN).range :=
  Classical.choose (exists_overGamma_of_mem_ggAutomizer hN c.2)

private theorem ggAutomizerGammaChoice_overGamma {Bs X : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (c : ggAutomizer X Bs) :
    GGOverGamma hN (c : MulAut ↥Bs) (ggAutomizerGammaChoice hN c) :=
  (Classical.choose_spec (exists_overGamma_of_mem_ggAutomizer hN c.2)).2

noncomputable def ggAutomizerGammaHom {Bs X : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) :
    ggAutomizer X Bs →*
      ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range (ggGamma X hN).range :=
  { toFun := fun c =>
      ⟨ggAutomizerGammaChoice hN c,
        (Classical.choose_spec (exists_overGamma_of_mem_ggAutomizer hN c.2)).1⟩
    map_one' := by
      apply Subtype.ext
      exact GGOverGamma.unique (ggAutomizerGammaChoice_overGamma hN 1) GGOverGamma.one
    map_mul' := fun c d => by
      apply Subtype.ext
      exact GGOverGamma.unique (ggAutomizerGammaChoice_overGamma hN (c * d))
        ((ggAutomizerGammaChoice_overGamma hN c).mul
          (ggAutomizerGammaChoice_overGamma hN d)) }

theorem ggAutomizerGammaHom_overGamma {Bs X : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (c : ggAutomizer X Bs) :
    GGOverGamma hN (c : MulAut ↥Bs)
      (((ggAutomizerGammaHom hN c :
          ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range (ggGamma X hN).range) :
        MulAut ↥(ggGamma X hN).range)) :=
  ggAutomizerGammaChoice_overGamma hN c

theorem ggAutomizerGammaHom_ker_isPGroup {p : ℕ} {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hN : Bs ≤ Subgroup.normalizer (X : Set G)) :
    IsPGroup p (ggAutomizerGammaHom hN).ker := by
  intro a
  refine ⟨1, ?_⟩
  simp only [pow_one]
  apply Subtype.ext
  apply Subtype.ext
  apply pow_eq_one_of_ggOverGamma_one hBs hN a.1.2
  have hov := ggAutomizerGammaHom_overGamma hN a.1
  have h0 : ((ggAutomizerGammaHom hN a.1) : MulAut (ggGamma X hN).range) = 1 :=
    congrArg Subtype.val a.2
  rwa [h0] at hov

theorem ggAutomizerGammaHom_injective {p : ℕ} (hp : p.Prime) {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hNoTr : GGNoTransvection p Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hZ : Nat.card ↥(Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G)) ≤ p) :
    Function.Injective (ggAutomizerGammaHom hN) := by
  intro c d hcd
  have h1 : ((ggAutomizerGammaHom hN c :
        ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range (ggGamma X hN).range) :
        MulAut ↥(ggGamma X hN).range) =
      ((ggAutomizerGammaHom hN d :
        ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range (ggGamma X hN).range) :
        MulAut ↥(ggGamma X hN).range) := congrArg Subtype.val hcd
  have hov : GGOverGamma hN ((c : MulAut ↥Bs)⁻¹ * d) 1 := by
    have h2 := (ggAutomizerGammaHom_overGamma hN c).inv.mul
      (ggAutomizerGammaHom_overGamma hN d)
    rwa [h1, inv_mul_cancel] at h2
  have hmem : (c : MulAut ↥Bs)⁻¹ * d ∈ ggAutomizer X Bs :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ c.2) d.2
  exact Subtype.ext (inv_mul_eq_one.mp
    (eq_one_of_ggOverGamma_one hp hBs hNoTr hN hZ hmem hov))

theorem ggAutomizerGammaHom_range {p : ℕ} {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) :
    (((ggAutomizerGammaHom hN).range.map
        (ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range
          (ggGamma X hN).range).subtype) : Set (MulAut ↥(ggGamma X hN).range)) =
      ggTorusWeylAut p (ggGamma X hN).range := by
  ext a
  constructor
  · intro ha
    change a ∈ Subgroup.map
      (ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range (ggGamma X hN).range).subtype
      (ggAutomizerGammaHom hN).range at ha
    rw [Subgroup.mem_map] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    rw [MonoidHom.mem_range] at hb
    obtain ⟨c, rfl⟩ := hb
    obtain ⟨g, hgX, hgN, hcg⟩ := mem_ggAutomizer_iff.mp c.2
    have hceq : (c : MulAut ↥Bs) = ggConjAut Bs hgN :=
      MulEquiv.ext fun b => Subtype.ext (hcg b)
    have hn := conj_mem_normalizer_range_ggGamma hN hgX hgN
    have hweyl : GGTorusWeylElt p (ggGamma X hN).range ⟨g, hgX⟩ :=
      ggTorusWeylElt_of_mem_normalizer hBs hN hgX hgN
    have hov : GGOverGamma hN (c : MulAut ↥Bs)
        (ggConjAut (ggGamma X hN).range hn) := by
      rw [hceq]
      exact ggOverGamma_conjAut hgX hgN
    have heq : ((ggAutomizerGammaHom hN c :
          ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range (ggGamma X hN).range) :
          MulAut ↥(ggGamma X hN).range) =
        ggConjAut (ggGamma X hN).range hn :=
      GGOverGamma.unique (ggAutomizerGammaHom_overGamma hN c) hov
    change ((ggAutomizerGammaHom hN c :
      ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range (ggGamma X hN).range) :
      MulAut ↥(ggGamma X hN).range) ∈ ggTorusWeylAut p (ggGamma X hN).range
    rw [heq]
    exact ⟨⟨g, hgX⟩, hn, hweyl, rfl⟩
  · rintro ⟨n, hn, hnW, rfl⟩
    have hnN : (n : G) ∈ Subgroup.normalizer (Bs : Set G) :=
      mem_normalizer_of_ggTorusWeylElt hN hSC hnW
    have hc_mem : ggConjAut Bs hnN ∈ ggAutomizer X Bs :=
      ggConjAut_mem_ggAutomizer n.2 hnN
    have hov' := ggOverGamma_conjAut (hN := hN) n.2 hnN
    have heq : ggConjAut (ggGamma X hN).range
        (conj_mem_normalizer_range_ggGamma hN n.2 hnN) =
        ggConjAut (ggGamma X hN).range hn := by
      apply MulEquiv.ext
      intro b
      apply Subtype.ext
      rfl
    rw [heq] at hov'
    have hEq : ((ggAutomizerGammaHom hN ⟨ggConjAut Bs hnN, hc_mem⟩ :
          ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range (ggGamma X hN).range) :
          MulAut ↥(ggGamma X hN).range) =
        ggConjAut (ggGamma X hN).range hn :=
      GGOverGamma.unique
        (ggAutomizerGammaHom_overGamma hN ⟨ggConjAut Bs hnN, hc_mem⟩) hov'
    change ggConjAut (ggGamma X hN).range hn ∈ Subgroup.map
      (ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range (ggGamma X hN).range).subtype
      (ggAutomizerGammaHom hN).range
    rw [Subgroup.mem_map]
    exact ⟨ggAutomizerGammaHom hN ⟨ggConjAut Bs hnN, hc_mem⟩,
      ⟨⟨ggConjAut Bs hnN, hc_mem⟩, rfl⟩, hEq⟩

theorem card_ggAutomizer_dvd_gamma {p : ℕ} (hp : p.Prime) {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hNoTr : GGNoTransvection p Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hZ : Nat.card ↥(Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G)) ≤ p) :
    Nat.card (ggAutomizer X Bs) ∣
      Nat.card (ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range (ggGamma X hN).range) :=
  Subgroup.card_dvd_of_injective (ggAutomizerGammaHom hN)
    (ggAutomizerGammaHom_injective hp hBs hNoTr hN hZ)

end Over

theorem ggAutomizerGammaHom_surjective_of_weyl_normalizers {p : ℕ}
    {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hW : ∀ n : X, MulAut.conj n ∈ Subgroup.normalizer
      ((ggGamma X hN).range : Set (MulAut X)) → GGTorusWeylElt p (ggGamma X hN).range n) :
    Function.Surjective (ggAutomizerGammaHom hN) := by
  intro a
  obtain ⟨_, ⟨n, rfl⟩, hn, han⟩ := mem_ggAutomizer_iff.mp a.2
  have hnBs := mem_normalizer_of_ggTorusWeylElt hN hSC (hW n hn)
  have hc : ggConjAut Bs hnBs ∈ ggAutomizer X Bs := ggConjAut_mem_ggAutomizer n.2 hnBs
  refine ⟨⟨ggConjAut Bs hnBs, hc⟩, ?_⟩
  have ha : (a : MulAut (ggGamma X hN).range) = ggConjAut (ggGamma X hN).range hn :=
    MulEquiv.ext fun b => Subtype.ext (han b)
  apply Subtype.ext
  rw [ha]
  exact GGOverGamma.unique (ggAutomizerGammaHom_overGamma hN ⟨_, hc⟩)
    (ggOverGamma_conjAut n.2 hnBs)

theorem map_ggAutomizerGammaHom_subgroup_of_weyl_normalizers
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X J : Subgroup G}
    (hJK : J ≤ X) (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hW : ∀ n : X, MulAut.conj n ∈ Subgroup.normalizer
      ((ggGamma X hN).range : Set (MulAut X)) → GGTorusWeylElt p (ggGamma X hN).range n) :
    (((ggAutomizer J Bs).subgroupOf (ggAutomizer X Bs)).map (ggAutomizerGammaHom hN)).map
      (ggAutomizer (MulAut.conj : X →* MulAut X).range (ggGamma X hN).range).subtype =
        ggAutomizer (((J.subgroupOf X).map (MulAut.conj : X →* MulAut X))) (ggGamma X hN).range := by
  classical
  let Φ := ggAutomizerGammaHom hN
  let SJ := (ggAutomizer J Bs).subgroupOf (ggAutomizer X Bs)
  apply le_antisymm
  · rintro a ⟨a₀, ⟨c, hc, rfl⟩, rfl⟩
    have hcJ : (c : MulAut Bs) ∈ ggAutomizer J Bs := hc
    obtain ⟨g, hgJ, hgN, hgact⟩ := mem_ggAutomizer_iff.mp hcJ
    let n : X := ⟨g, hJK hgJ⟩
    have hn : MulAut.conj n ∈ Subgroup.normalizer
        ((ggGamma X hN).range : Set (MulAut X)) := conj_mem_normalizer_range_ggGamma hN n.2 hgN
    have hceq : (c : MulAut Bs) = ggConjAut Bs hgN := by
      apply MulEquiv.ext
      intro b
      apply Subtype.ext
      rw [ggConjAut_apply]
      exact hgact b
    have hover : GGOverGamma hN (c : MulAut Bs) (ggConjAut (ggGamma X hN).range hn) := by
      rw [hceq]
      exact ggOverGamma_conjAut n.2 hgN
    have heq : (Φ c : MulAut (ggGamma X hN).range) = ggConjAut (ggGamma X hN).range hn :=
      (ggAutomizerGammaHom_overGamma hN c).unique hover
    change (Φ c : MulAut (ggGamma X hN).range) ∈
      ggAutomizer ((J.subgroupOf X).map (MulAut.conj : X →* MulAut X)) (ggGamma X hN).range
    rw [heq]
    refine ggConjAut_mem_ggAutomizer ?_ hn
    change MulAut.conj n ∈ (J.subgroupOf X).map (MulAut.conj : X →* MulAut X)
    exact ⟨n, hgJ, rfl⟩
  · intro a ha
    obtain ⟨u, hu, hn, hau⟩ := mem_ggAutomizer_iff.mp ha
    obtain ⟨n, hnJ, rfl⟩ := Subgroup.mem_map.mp hu
    have hnG : (n : G) ∈ J := hnJ
    have hnBs := mem_normalizer_of_ggTorusWeylElt hN hSC (hW n hn)
    have hcX : ggConjAut Bs hnBs ∈ ggAutomizer X Bs := ggConjAut_mem_ggAutomizer n.2 hnBs
    let c : ggAutomizer X Bs := ⟨ggConjAut Bs hnBs, hcX⟩
    have hc : c ∈ SJ := ggConjAut_mem_ggAutomizer hnG hnBs
    refine ⟨Φ c, ⟨c, hc, rfl⟩, ?_⟩
    have haeq : a = ggConjAut (ggGamma X hN).range hn :=
      MulEquiv.ext fun b => Subtype.ext (hau b)
    rw [haeq]
    exact GGOverGamma.unique (ggAutomizerGammaHom_overGamma hN c)
      (ggOverGamma_conjAut n.2 hnBs)


end CFSG.StandardType

end
