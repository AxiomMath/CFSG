module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinRMDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylBranchOfInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveCaseZeroOfInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxStep6
import CFSG.LocalAnalysis.StandardType.GGSecFiveCoxProdHolds
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeAAssembly
import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
import CFSG.LocalAnalysis.StandardType.GGForkJrPumpDichotomy
import CFSG.LocalAnalysis.StandardType.GGSecFiveCR3OfPump
import CFSG.LocalAnalysis.StandardType.GGSecFiveCROfInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace NSJoin

section Helpers

private theorem nsRM_eps_zpowers_eq {G : Type} [Group G] [Finite G] {x b : G} {p : ℕ}
    (hp : p.Prime) (hox : orderOf x = p) (hbx : b ∈ Subgroup.zpowers x) (hb1 : b ≠ 1) :
    x ∈ Subgroup.zpowers b := by
  have hdvd : orderOf b ∣ p := by rw [← hox]; exact orderOf_dvd_of_mem_zpowers hbx
  have hordb : orderOf b = p :=
    ((Nat.dvd_prime hp).mp hdvd).resolve_left (fun h => hb1 (orderOf_eq_one_iff.mp h))
  have hle : Subgroup.zpowers b ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hbx
  have hcardx : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hox]
  have hcardb : Nat.card (Subgroup.zpowers b) = p := by rw [Nat.card_zpowers, hordb]
  have heq : Subgroup.zpowers b = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardx, hcardb])
  exact heq.symm ▸ Subgroup.mem_zpowers x

private theorem nsCR_pair_order_le_four
    (hRR : GGSecFiveRootReflInput) (hCP : GGSecFiveCoxProdInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs : Subgroup G}
    (hp : p.Prime) (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    (A : Subgroup (MulAut ↥Bs)) (hA : A ≤ ggInduced ⊤ Bs)
    (hW : GGWeylReflectionGroup p A) (hnotG2 : ¬ GGWeylOfType p CoxeterMatrix.G₂ A)
    {a b : MulAut ↥Bs} (ha : a ∈ A) (hb : b ∈ A)
    (har : GGIsReflection p a) (hbr : GGIsReflection p b) : orderOf (a * b) ≤ 4 := by
  obtain ⟨ι, M, hM, f, hf⟩ := hW
  have hM2 : ¬ ∃ e : Fin 2 ≃ ι, M = CoxeterMatrix.G₂.reindex e := by
    rintro ⟨e, rfl⟩
    exact hnotG2 (GGWeylOfType.of_reindex (p := p) (A := A) (e := e) ⟨f, hf⟩)
  obtain ⟨i, g, hag⟩ := hRR G p Bs hp hp2 hBs hNT A hA ι M hM hM2 f hf ⟨a, ha⟩ har
  obtain ⟨j, h, hbh⟩ := hRR G p Bs hp hp2 hBs hNT A hA ι M hM hM2 f hf ⟨b, hb⟩ hbr
  have hz : (⟨a, ha⟩ * ⟨b, hb⟩ : ↥A) =
      f ((g * M.simple i * g⁻¹) * (h * M.simple j * h⁻¹)) := by
    rw [hag, hbh, ← map_mul]
  calc orderOf (a * b) = orderOf (⟨a, ha⟩ * ⟨b, hb⟩ : ↥A) := by
        rw [show a * b = ((⟨a, ha⟩ * ⟨b, hb⟩ : ↥A) : MulAut ↥Bs) from rfl, Subgroup.orderOf_coe]
      _ = orderOf (f ((g * M.simple i * g⁻¹) * (h * M.simple j * h⁻¹))) := by rw [hz]
      _ = orderOf ((g * M.simple i * g⁻¹) * (h * M.simple j * h⁻¹)) :=
        MulEquiv.orderOf_eq f _
      _ ≤ 4 := hCP ι M hM hM2 i j g h

end Helpers


@[expose] def NSBaseFrameInputOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), NSRegularCfgOf T p B Bs x L D J 𝒦 →
      ∃ (ιL : Type) (_ : Fintype ιL) (ML : CoxeterMatrix ιL),
        (GGIsWeylMatrixAD ML ∨ GGIsWeylMatrixE ML) ∧ GGWeylOfType p ML (ggAutomizer L Bs) ∧
          Nat.card ↥Bs ≤ p ^ (Fintype.card ιL + 1) ∧ 3 ≤ Fintype.card ιL

@[expose] def NSBaseFrameInput : Prop :=
  NSBaseFrameInputOf NSTypeAD

@[expose] def NSJrInputOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), NSRegularCfgOf T p B Bs x L D J 𝒦 →
      ∀ r ∈ ggAutomizer J Bs, GGIsReflection p r → GGRealized p Bs r

@[expose] def NSCRInputOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), NSRegularCfgOf T p B Bs x L D J 𝒦 →
      ∀ t t' : MulAut ↥Bs,
        (∃ r ∈ ggAutomizer J Bs, GGIsReflection p r ∧ ∃ g ∈ ggInduced ⊤ Bs, t = g * r * g⁻¹) →
        GGIsReflection p t' → GGRealized p Bs t' → orderOf (t * t') ≤ 4

@[expose] def NSCR3InputOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), NSRegularCfgOf T p B Bs x L D J 𝒦 →
      ∀ r₁ ∈ ggAutomizer J Bs, ∀ r₂ ∈ ggAutomizer J Bs, GGIsReflection p r₁ →
        GGIsReflection p r₂ → orderOf (r₁ * r₂) = 3 →
        ∀ g ∈ ggInduced ⊤ Bs, ∀ t' : MulAut ↥Bs, GGIsReflection p t' → GGRealized p Bs t' →
          ¬ (Commute t' (g * r₁ * g⁻¹) ∧ Commute t' (g * r₂ * g⁻¹)) →
            Nat.card (Subgroup.closure ({g * r₁ * g⁻¹, g * r₂ * g⁻¹, t'} : Set (MulAut ↥Bs))) ∣ 48

@[expose] def NSWeylBranchInputOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), NSRegularCfgOf T p B Bs x L D J 𝒦 →
      (∀ b : ↥Bs, (∀ φ ∈ ggAInf p B Bs x L D J, φ b = b) → b = 1) →
        GGWeylReflectionGroup p (ggAInf p B Bs x L D J)

@[expose] def NSCaseZeroInputOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), NSRegularCfgOf T p B Bs x L D J 𝒦 →
      ∀ hxBs : x ∈ Bs, (∀ φ ∈ ggAInf p B Bs x L D J, φ ⟨x, hxBs⟩ = ⟨x, hxBs⟩) →
        (∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
          ∃ t ∈ ggAutomizer K Bs, GGIsReflection p t ∧ ¬ GGRealized p Bs t) →
          GGSecFiveInfWitness p B Bs x L D J

theorem nsCRInput_of_pump {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hPumpL : NSPumpLInputOf T) (hPumpNbr : NSPumpNbrInputOf T) : NSCRInputOf T := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg0 t t' ht ht'refl ht'real
  have hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦 := ggSecFiveRouteCfg'_of_routeCfg hcfg0.1
  obtain ⟨r, hrJ, hrrefl, g, hgInd, ht_eq⟩ := ht
  obtain ⟨g0, -, hg0N, hg0eq⟩ := hgInd
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  have hInn : GGInnerDiagAll p B Bs x L D J := hcfg.1.2.2.1
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  obtain ⟨hp, hBs_ea, -, -, -⟩ := hconf.tableB_facts
  have hp2 : p ≠ 2 := hconf.1.2.2.2.2.2.1.2.1
  have : Fact p.Prime := ⟨hp⟩
  have hRR : GGSecFiveRootReflInput := SecFiveRootRefl.ggSecFiveRootReflInput_holds
  have hCP : GGSecFiveCoxProdInput := ggSecFiveCoxProdInput_holds
  let φ : MulAut ↥Bs := ggConjAut Bs hg0N
  have hg_eq : g = φ := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [hg0eq b, ggConjAut_apply]
  have ht_eq' : t = φ * r * φ⁻¹ := by rw [ht_eq, hg_eq]
  let φinv : MulAut ↥Bs := ggConjAut Bs (Subgroup.inv_mem _ hg0N)
  have hφinv : φinv = φ⁻¹ := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [ggConjAut_apply, inv_inv]
    exact (inv_apply_of_forall (fun b => ggConjAut_apply Bs hg0N b) b).symm
  let s : MulAut ↥Bs := φinv * t' * φinv⁻¹
  have hs_real : GGRealized p Bs s := ht'real.conj hp (Subgroup.inv_mem _ hg0N)
  have hs_refl : GGIsReflection p s := ht'refl.conj' φinv
  obtain ⟨Jt, hs_ind, hs_fix, hs_pc⟩ := hs_real
  have hdich := ggDichotomy_refined hL hP hconf hInn hs_refl hs_ind hs_fix hs_pc
  have hconj : (MulAut.conj φinv) (t * t') = r * s := by
    change φinv * (t * t') * φinv⁻¹ = r * (φinv * t' * φinv⁻¹)
    rw [ht_eq', hφinv]
    group
  have horder : orderOf (t * t') = orderOf (r * s) := by
    rw [← MulEquiv.orderOf_eq (MulAut.conj φinv) (t * t'), hconj]
  rw [horder]
  rcases hdich with hJLt | ⟨d, K, hnb, hJK, hJtK⟩ | hcomm
  ·
    have hpJ : p ∣ Nat.card J := hP G p B x L D J hconf.1 hconf.2.2
    obtain ⟨hJL, -, -⟩ := eq_of_le_of_stdSub hconf.1 hconf.2.2 hpJ
    obtain ⟨hWeyl, hnotG2⟩ := hPumpL G p B Bs x L D J 𝒦 hcfg0
    have hJle : ggAutomizer J Bs ≤ ggAutomizer L Bs := ggAutomizer_mono Bs hJL
    have hrA : r ∈ ggAutomizer L Bs := hJle hrJ
    have hsA : s ∈ ggAutomizer L Bs := by
      obtain ⟨a, ha, haN, has⟩ := hs_ind
      exact Subgroup.subset_closure ⟨a, hJLt ha, haN, has⟩
    have hAind : ggAutomizer L Bs ≤ ggInduced ⊤ Bs := by
      intro w hw
      have h1 : w ∈ ggAutomizer ⊤ Bs := ggAutomizer_mono Bs le_top hw
      rwa [ggAutomizer_eq] at h1
    exact nsCR_pair_order_le_four hRR hCP hp hp2 hBs_ea hNT (ggAutomizer L Bs) hAind
      hWeyl hnotG2 hrA hsA hrrefl hs_refl
  ·
    obtain ⟨hWeyl, hnotG2⟩ := hPumpNbr G p B Bs x L D J 𝒦 hcfg0 d K hnb
    have hJKle : ggAutomizer J Bs ≤ ggAutomizer K Bs := ggAutomizer_mono Bs hJK
    have hrA : r ∈ ggAutomizer K Bs := hJKle hrJ
    have hsA : s ∈ ggAutomizer K Bs := by
      obtain ⟨a, ha, haN, has⟩ := hs_ind
      exact Subgroup.subset_closure ⟨a, hJtK ha, haN, has⟩
    have hAind : ggAutomizer K Bs ≤ ggInduced ⊤ Bs := by
      intro w hw
      have h1 : w ∈ ggAutomizer ⊤ Bs := ggAutomizer_mono Bs le_top hw
      rwa [ggAutomizer_eq] at h1
    exact nsCR_pair_order_le_four hRR hCP hp hp2 hBs_ea hNT (ggAutomizer K Bs) hAind
      hWeyl hnotG2 hrA hsA hrrefl hs_refl
  ·
    have hsr : s * r = r * s := by
      have hsub : ggInduced J Bs ⊆ (Subgroup.centralizer ({s} : Set (MulAut ↥Bs))) := by
        intro a ha
        exact Subgroup.mem_centralizer_iff.mpr (by
          intro h hh
          rw [Set.mem_singleton_iff] at hh
          subst hh
          exact hcomm a ha)
      have hcl : ggAutomizer J Bs ≤ Subgroup.centralizer ({s} : Set (MulAut ↥Bs)) :=
        (Subgroup.closure_le (Subgroup.centralizer ({s} : Set (MulAut ↥Bs)))).mpr hsub
      have hmem := hcl hrJ
      exact (Subgroup.mem_centralizer_iff.mp hmem) s rfl
    have h2 : (r * s) ^ 2 = 1 := by
      have hcr : Commute r s := hsr.symm
      rw [hcr.mul_pow, hrrefl.1, hs_refl.1, mul_one]
    have hle2 : orderOf (r * s) ≤ 2 :=
      Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h2)
    omega

theorem nsCR3Input_of_pump {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hPumpL : NSPumpLInputOf T) (hPumpNbr : NSPumpNbrInputOf T) (hRT : GGWeylReflTripleInput) :
    NSCR3InputOf T := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg0 r₁ hr₁J r₂ hr₂J hr₁ hr₂ hord g hg t' ht'r ht'R hnc
  have hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦 := ggSecFiveRouteCfg'_of_routeCfg hcfg0.1
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  have hInn : GGInnerDiagAll p B Bs x L D J := hcfg.1.2.2.1
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  obtain ⟨hp, -, -, -, -⟩ := hconf.tableB_facts
  have hp2 : p ≠ 2 := hconf.1.2.2.2.2.2.1.2.1
  have hBsab : IsElemAbelian p Bs := hconf.2.1.2.1
  have : Fact p.Prime := ⟨hp⟩
  have hNoTv : ∀ X : Subgroup G, ∀ a ∈ ggAutomizer X Bs, ¬ GGIsTransvection p a := by
    intro X a ha
    obtain ⟨m, -, hmN, hm⟩ := mem_ggAutomizer_iff.mp ha
    exact hNT a ⟨m, Subgroup.mem_top m, hmN, hm⟩
  obtain ⟨n, -, hnN, hn⟩ := hg
  have hgn : g = ggConjAut Bs hnN := MulEquiv.ext fun b => Subtype.ext (hn b)
  have hninv : n⁻¹ ∈ Subgroup.normalizer (Bs : Set G) := Subgroup.inv_mem _ hnN
  have hinv : ggConjAut Bs hninv = g⁻¹ := by
    rw [hgn]
    refine eq_inv_of_mul_eq_one_left (MulEquiv.ext fun b => Subtype.ext ?_)
    show n⁻¹ * (n * (b : G) * n⁻¹) * n⁻¹⁻¹ = b
    group
  have hsR : GGRealized p Bs (ggConjAut Bs hninv * t' * (ggConjAut Bs hninv)⁻¹) :=
    GGRealized.conj hp ht'R hninv
  rw [hinv, inv_inv] at hsR
  have hsr : GGIsReflection p (g⁻¹ * t' * g) := by
    simpa using ht'r.conj g⁻¹
  set s := g⁻¹ * t' * g with hs
  have hcard : Nat.card (Subgroup.closure ({g * r₁ * g⁻¹, g * r₂ * g⁻¹, t'} : Set (MulAut ↥Bs))) =
      Nat.card (Subgroup.closure ({r₁, r₂, s} : Set (MulAut ↥Bs))) := by
    have himg : (MulAut.conj g).toMonoidHom '' ({r₁, r₂, s} : Set (MulAut ↥Bs)) =
        {g * r₁ * g⁻¹, g * r₂ * g⁻¹, t'} := by
      simp only [Set.image_insert_eq, Set.image_singleton, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, hs]
      congr 2
      group
    rw [← himg, ← MonoidHom.map_closure]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  rw [hcard]
  obtain ⟨Js, hind, hJC, hpc⟩ := hsR
  have hpJ : p ∣ Nat.card J := hP G p B x L D J hconf.1 hconf.2.2
  rcases ggDichotomy_refined hL hP hconf hInn hsr hind hJC hpc with hJsL | ⟨d, K, hnb, hJK, hJsK⟩ |
    hcomm
  ·
    obtain ⟨hJL, -, -⟩ := eq_of_le_of_stdSub hconf.1 hconf.2.2 hpJ
    obtain ⟨m, hm, hmN, hm'⟩ := hind
    obtain ⟨hW, hG2⟩ := hPumpL G p B Bs x L D J 𝒦 hcfg0
    exact hRT G p Bs (ggAutomizer L Bs) hp hp2 hBsab (hNoTv L) hW hG2 r₁
      (ggAutomizer_mono Bs hJL hr₁J) r₂ (ggAutomizer_mono Bs hJL hr₂J) s
      (Subgroup.subset_closure ⟨m, hJsL hm, hmN, hm'⟩) hr₁ hr₂ hsr hord
  ·
    obtain ⟨m, hm, hmN, hm'⟩ := hind
    obtain ⟨hW, hG2⟩ := hPumpNbr G p B Bs x L D J 𝒦 hcfg0 d K hnb
    exact hRT G p Bs (ggAutomizer K Bs) hp hp2 hBsab (hNoTv K) hW hG2 r₁
      (ggAutomizer_mono Bs hJK hr₁J) r₂ (ggAutomizer_mono Bs hJK hr₂J) s
      (Subgroup.subset_closure ⟨m, hJsK hm, hmN, hm'⟩) hr₁ hr₂ hsr hord
  ·
    exfalso
    apply hnc
    have hc₁ : Commute s r₁ := hcomm r₁ (mem_ggAutomizer_iff.mp hr₁J)
    have hc₂ : Commute s r₂ := hcomm r₂ (mem_ggAutomizer_iff.mp hr₂J)
    have ht' : t' = g * s * g⁻¹ := by rw [hs]; group
    rw [ht']
    exact ⟨(hc₁.conj g), (hc₂.conj g)⟩

theorem nsJrInput_of_rootGenL {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hRootGenL : NSRootGenLInputOf T) : NSJrInputOf T := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg r hr hrefl
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1.1
  have hstdpre : LargeEvenStdSubPre p B x L D J := hconf.2.2.1
  have hJL : J ≤ L := hstdpre.2.2.2.2.2.1.1.trans inf_le_left
  obtain ⟨g, hg, hgN, hgφ⟩ := mem_ggAutomizer_iff.mp hr
  exact hRootGenL G p B Bs x L D J 𝒦 hcfg r
    (mem_ggAutomizer_iff.mpr ⟨g, hJL hg, hgN, hgφ⟩) hrefl

theorem nsRM_zero_fixes_x {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop} (hFix : NSFixInputOf T)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : NSRegularCfgOf T p B Bs x L D J 𝒦) (hxBs : x ∈ Bs)
    (hC : ¬ ∀ b : ↥Bs, (∀ φ ∈ ggAInf p B Bs x L D J, φ b = b) → b = 1) :
    ∀ φ ∈ ggAInf p B Bs x L D J, φ ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := by
  have hcfg' : GGSecFiveRouteCfg' p B Bs x L D J 𝒦 := ggSecFiveRouteCfg'_of_routeCfg hcfg.1
  have hconf : GGConfig p B Bs x L D J := hcfg'.1.1
  obtain ⟨hp, hBs_ea, -, -, -⟩ := hconf.tableB_facts
  have : Fact p.Prime := ⟨hp⟩
  have hle : ggAutomizer L Bs ≤ ggAInf p B Bs x L D J := le_sup_left
  push Not at hC
  obtain ⟨b, hb, hb1⟩ := hC
  have hbmem : (b : G) ∈ Subgroup.zpowers x :=
    hFix G p B Bs x L D J 𝒦 hcfg b fun φ hφ => hb φ (hle hφ)
  have hbG1 : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hx1 : x ≠ 1 := by
    intro hx
    apply hbG1
    have hbot : Subgroup.zpowers x = ⊥ := by rw [hx, Subgroup.zpowers_one_eq_bot]
    rw [hbot] at hbmem
    simpa using hbmem
  have hxpow : x ^ p = 1 := hBs_ea.2 x hxBs
  have hox : orderOf x = p := orderOf_eq_prime hxpow hx1
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (nsRM_eps_zpowers_eq hp hox hbmem hbG1)
  intro φ hφ
  have hφb : φ b = b := hb φ hφ
  have hbn : b ^ n = (⟨x, hxBs⟩ : ↥Bs) := by
    apply Subtype.ext
    rw [Subgroup.coe_zpow]
    exact hn
  calc φ ⟨x, hxBs⟩ = φ (b ^ n) := by rw [← hbn]
    _ = (φ b) ^ n := map_zpow φ b n
    _ = b ^ n := by rw [hφb]
    _ = ⟨x, hxBs⟩ := hbn

theorem nsRM_saturated {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hRootGenL : NSRootGenLInputOf T)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : NSRegularCfgOf T p B Bs x L D J 𝒦)
    (hxBs : x ∈ Bs) :
    ∀ a ∈ ggAInf p B Bs x L D J, GGIsReflection p a → a ⟨x, hxBs⟩ = ⟨x, hxBs⟩ →
      (∃ g ∈ ggAInf p B Bs x L D J, ∃ r ∈ ggAutomizer L Bs, GGIsReflection p r ∧ a = g * r * g⁻¹) →
        a ∈ ggAutomizer L Bs := by
  have hcfg' : GGSecFiveRouteCfg' p B Bs x L D J 𝒦 := ggSecFiveRouteCfg'_of_routeCfg hcfg.1
  have hconf : GGConfig p B Bs x L D J := hcfg'.1.1
  obtain ⟨hp, -, -, -, -⟩ := hconf.tableB_facts
  have hAInf_le : ggAInf p B Bs x L D J ≤ ggAutomizer ⊤ Bs := by
    rw [ggAInf]
    refine sup_le (ggAutomizer_mono Bs le_top) ?_
    refine iSup_le fun y => iSup_le fun K => iSup_le fun _ =>
      ggAutomizer_mono Bs le_top
  have hInn : GGInnerDiagOn Bs L := hcfg'.1.2.2.1.1
  have hP3 : GGFixedRealizedInL p Bs L x :=
    ggFixedRealizedInL_of_config hL hP hconf hInn
  rintro a haAInf haRefl haFixx ⟨g, hgAInf, r, hrL, hrRefl, haeq⟩
  have hrR : GGRealized p Bs r := hRootGenL G p B Bs x L D J 𝒦 hcfg r hrL hrRefl
  obtain ⟨g₀, -, hg₀N, hg₀eq⟩ :=
    eq_ggConjAut_of_mem_ggAutomizer (hAInf_le hgAInf)
  have haR : GGRealized p Bs a := by
    rw [haeq, hg₀eq]
    exact hrR.conj hp hg₀N
  have haInd : a ∈ ggInduced ⊤ Bs := haR.mem_ggInduced_top
  have haFix : x ∈ ggFixG Bs a :=
    Subgroup.mem_map.mpr ⟨⟨x, hxBs⟩, haFixx, rfl⟩
  exact hP3 a haRefl haInd haFix haR

theorem nsRM_witness_zero_realized {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hBase : NSBaseFrameInputOf T)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : NSRegularCfgOf T p B Bs x L D J 𝒦)
    (hxBs : x ∈ Bs) (hfix : ∀ φ ∈ ggAInf p B Bs x L D J, φ ⟨x, hxBs⟩ = ⟨x, hxBs⟩)
    (hreal : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → ∀ t ∈ ggAutomizer K Bs,
      GGIsReflection p t → GGRealized p Bs t) :
    GGSecFiveInfWitness p B Bs x L D J := by
  have hcfg' : GGSecFiveRouteCfg' p B Bs x L D J 𝒦 := ggSecFiveRouteCfg'_of_routeCfg hcfg.1
  have hP3 : GGFixedRealizedInL p Bs L x :=
    ggFixedRealizedInL_of_config hL hP hcfg'.1.1 hcfg'.1.2.2.1.1
  have hle : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizer L Bs := by
    intro y K hnbr
    rw [hcfg'.2.1 y K hnbr]
    refine (Subgroup.closure_le (K := ggAutomizer L Bs)).mpr ?_
    rintro t ⟨htK, htr⟩
    have htA : t ∈ ggAInf p B Bs x L D J := by
      rw [ggAInf]
      refine Subgroup.mem_sup_right ?_
      exact Subgroup.mem_iSup_of_mem (S := fun y : G =>
          ⨆ (K : Subgroup G) (_ : GGNbr p B x D J y K), ggAutomizer K Bs) y
        (Subgroup.mem_iSup_of_mem (S := fun K : Subgroup G =>
            ⨆ (_ : GGNbr p B x D J y K), ggAutomizer K Bs) K
          (Subgroup.mem_iSup_of_mem (S := fun _ : GGNbr p B x D J y K =>
              ggAutomizer K Bs) hnbr htK))
    have htx : t ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := hfix t htA
    have htxE : x ∈ ggFixG Bs t := Subgroup.mem_map.mpr ⟨⟨x, hxBs⟩, htx, rfl⟩
    have htR : GGRealized p Bs t := hreal y K hnbr t htK htr
    exact hP3 t htr htR.mem_ggInduced_top htxE htR
  have hAeq : ggAInf p B Bs x L D J = ggAutomizer L Bs := by
    rw [ggAInf]
    refine le_antisymm (sup_le le_rfl ?_) le_sup_left
    exact iSup_le fun y => iSup_le fun K => iSup_le fun hnbr => hle y K hnbr
  have hweylL : GGWeylReflectionGroup p (ggAutomizer L Bs) := by
    obtain ⟨ιL, -, ML, hADE, hW, -, -⟩ := hBase G p B Bs x L D J 𝒦 hcfg
    rcases hADE with hAD | hE
    · exact ⟨ιL, ML, hAD.isWeylMatrix, hW⟩
    · exact ⟨ιL, ML, hE.isWeylMatrix, hW⟩
  refine ⟨?_, ⟨∅, ?_, ?_⟩⟩
  · rw [hAeq]; exact hweylL
  · constructor
    · simp
    · intro K hK; simp at hK
  · rw [hAeq, ggAutomizerJoin]
    simp

theorem nsCaseZeroInput_of_inputs {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hFix : NSFixInputOf T) (hRootGenL : NSRootGenLInputOf T) (hBase : NSBaseFrameInputOf T) :
    NSCaseZeroInputOf T := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hxBs hfix _
  have hcfg' : GGSecFiveRouteCfg' p B Bs x L D J 𝒦 := ggSecFiveRouteCfg'_of_routeCfg hcfg.1
  obtain ⟨ιL, instL, ML, hML, hAL, -, -⟩ := hBase G p B Bs x L D J 𝒦 hcfg
  exact (⟨hcfg', hxBs, hfix, nsRM_saturated hL hP hRootGenL hcfg hxBs,
    ⟨ιL, instL, ML, hML, hAL⟩, hFix G p B Bs x L D J 𝒦 hcfg⟩ :
      GGCaseZeroData p B Bs x L D J 𝒦).witness

theorem nsRM_witness_main {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hRootGenL : NSRootGenLInputOf T) (hBase : NSBaseFrameInputOf T)
    (hLev2 : GGSecFiveLevTwoInput') (hWeyl : NSWeylBranchInputOf T)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : NSRegularCfgOf T p B Bs x L D J 𝒦)
    (hC : ∀ b : ↥Bs, (∀ φ ∈ ggAInf p B Bs x L D J, φ b = b) → b = 1) :
    GGSecFiveInfWitness p B Bs x L D J := by
  have hcfg' : GGSecFiveRouteCfg' p B Bs x L D J 𝒦 := ggSecFiveRouteCfg'_of_routeCfg hcfg.1
  have hconf : GGConfig p B Bs x L D J := hcfg'.1.1
  obtain ⟨hp, hBs_ea, hxBs, hLx, -⟩ := hconf.tableB_facts
  have hp2 : p ≠ 2 := hconf.1.2.2.2.2.2.1.2.1
  have hNT : GGNoTransvection p Bs := hcfg'.1.2.2.2.1
  have hW : GGWeylReflectionGroup p (ggAInf p B Bs x L D J) :=
    hWeyl G p B Bs x L D J 𝒦 hcfg hC
  refine ⟨hW, ?_⟩
  obtain ⟨ι, M, hM, f, hf⟩ := hW
  obtain ⟨ιL, instL, ML, hML, hWeylL, hcardBs, -⟩ := hBase G p B Bs x L D J 𝒦 hcfg
  obtain ⟨𝒮', h𝒮'sub, hcard', heq⟩ :=
    hLev2 G p Bs hp hp2 hBs_ea hNT (ggAInf p B Bs x L D J) (ggRM_ainf_le_induced)
      ι M hM (ggRM_not_G2 hML hWeylL le_sup_left f) f hf
      ⟨x, hxBs⟩ (ggAutomizer L Bs) ιL ML le_sup_left (ggRM_AL_fixes_x hcfg' hxBs)
      hML hWeylL hcardBs (nsRM_saturated hL hP hRootGenL hcfg hxBs)
      (GGSecFiveNbrAutFamily p B Bs x D J) (by
        intro K hK
        obtain ⟨y, K₀, hNK, rfl⟩ := hK
        refine ⟨?_, ?_⟩
        · exact (le_iSup_of_le y (le_iSup_of_le K₀ (le_iSup_of_le hNK
            (le_rfl : ggAutomizer K₀ Bs ≤ ggAutomizer K₀ Bs)))).trans le_sup_right
        · exact hcfg'.2.1 y K₀ hNK)
  obtain ⟨𝒦', h𝒦', hjoin'⟩ := ggRM_nbrs_of_family 𝒮' h𝒮'sub hcard'
  refine ⟨𝒦', h𝒦', ?_⟩
  calc ggAutomizerJoin L Bs 𝒦'
      = ggAutomizer L Bs ⊔ ⨆ S ∈ 𝒮', S := hjoin'
    _ = ggAutomizer L Bs ⊔ ⨆ S ∈ GGSecFiveNbrAutFamily p B Bs x D J, S := heq.symm
    _ = ggAInf p B Bs x L D J := ggRM_ainf_eq_sup.symm

theorem nsReflMaxInput_of_weylBranch {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hFix : NSFixInputOf T) (hRootGenL : NSRootGenLInputOf T) (hBase : NSBaseFrameInputOf T)
    (hLev2 : GGSecFiveLevTwoInput') (hWeyl : NSWeylBranchInputOf T) : NSReflMaxInputOf T := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg0 hns hguard y K' hnbr
  have hcfg : NSRegularCfgOf T p B Bs x L D J 𝒦 := ⟨hcfg0, hns, hguard⟩
  have hcfg' : GGSecFiveRouteCfg' p B Bs x L D J 𝒦 := ggSecFiveRouteCfg'_of_routeCfg hcfg0
  have hxBs : x ∈ Bs := hcfg'.1.1.tableB_facts.2.2.1
  by_cases hC : ∀ b : ↥Bs, (∀ φ ∈ ggAInf p B Bs x L D J, φ b = b) → b = 1
  · exact ggRM_of_witness hcfg'.2.2.2
      (nsRM_witness_main hL hP hRootGenL hBase hLev2 hWeyl hcfg hC) y K' hnbr
  · have hfix := nsRM_zero_fixes_x hFix hcfg hxBs hC
    by_cases hun : ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
        ∃ t ∈ ggAutomizer K Bs, GGIsReflection p t ∧ ¬ GGRealized p Bs t
    · exact ggRM_of_witness hcfg'.2.2.2
        (nsCaseZeroInput_of_inputs hL hP hFix hRootGenL hBase G p B Bs x L D J 𝒦 hcfg hxBs hfix
          hun) y K' hnbr
    · refine ggRM_of_witness hcfg'.2.2.2
        (nsRM_witness_zero_realized hL hP hBase hcfg hxBs hfix ?_) y K' hnbr
      intro y K hK t ht hrefl
      by_contra hnr
      exact hun ⟨y, K, hK, t, ht, hrefl, hnr⟩

theorem nsFixInput_of_tbFix {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop} (hT : GGTBFixInput) :
    NSFixInputOf T := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg0
  have hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦 := ggSecFiveRouteCfg'_of_routeCfg hcfg0.1
  have hR := hcfg.1
  obtain ⟨y, K, hnbr⟩ := exists_ggNbr hR.1.1.2.2.2.2.2.2.2 hR.1.2.2
  exact hT G p B Bs x L D J hR.1 hR.2.1 hR.2.2.1 hR.2.2.2.1 y K hnbr (hcfg.2.1 y K hnbr)
    (Or.inr hcfg.2.1)

theorem nsPumpLInput_of_baseFrame {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hBase : NSBaseFrameInputOf T) : NSPumpLInputOf T := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg
  obtain ⟨ιL, instL, ML, hML, hWeylL, -, -⟩ := hBase G p B Bs x L D J 𝒦 hcfg
  have hWM : GGIsWeylMatrix ML := by
    rcases hML with h | h
    · exact h.isWeylMatrix
    · exact h.isWeylMatrix
  refine ⟨GGWeylOfType.weylReflectionGroup hWM hWeylL, ?_⟩
  rintro ⟨f, -⟩
  exact ggRM_not_G2_of_le hML hWeylL le_rfl f ⟨Equiv.refl (Fin 2), (ggCoxeterMatrix_reindex_refl _).symm⟩

end NSJoin

end CFSG.StandardType

end
