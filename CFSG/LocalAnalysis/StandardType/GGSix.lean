module

public import CFSG.LocalAnalysis.StandardType.GGSkeleton
public import CFSG.LocalAnalysis.StandardType.GGSixFusion

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.RankThree.PartTwo.Sec21

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] def GGSixCtx (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) : Prop :=
  IsSimpleGroup G ∧ (∃ a b : G, a * b ≠ b * a) ∧ KProper InCatalog G ∧ IsCharTwoType G ∧
    4 ≤ evenRank G ∧ p ∈ LargeEvenBeta 4 G ∧ LargeEvenSStar p B x L ∧
    LargeEvenStandardType p B x L ∧ GGSixHyp p B Bs x L D J

noncomputable abbrev ggM (p : ℕ) (B : Subgroup G) (x : G) (L D J : Subgroup G) :
    Subgroup G :=
  Subgroup.normalizer (ggG0 p B x L D J : Set G)

@[expose] def GGTransvection (p : ℕ) (Bs : Subgroup G) (a : G) : Prop :=
  Nat.card (⁅Bs, Subgroup.zpowers a⁆ : Subgroup G) = p ∧
    ⁅Bs, Subgroup.zpowers a⁆ ≤ Subgroup.centralizer {a}

@[expose] def GGSixStepOne (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) : Prop :=
  Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ ∧
    GGControlsStrongFusion (ggM p B x L D J) D ∧
    (∀ Q : Subgroup G, D ≤ Subgroup.normalizer (Q : Set G) → Nat.Coprime p (Nat.card Q) →
      Q ≤ ggM p B x L D J) ∧
    (∃ P : Sylow p (ggM p B x L D J),
      Bs ≤ (P : Subgroup (ggM p B x L D J)).map (ggM p B x L D J).subtype ∧
      ∀ E : Subgroup G, E ≤ (P : Subgroup (ggM p B x L D J)).map (ggM p B x L D J).subtype →
        IsElemAbelian p E → Nat.card E = Nat.card Bs → E = Bs) ∧
    ∀ a ∈ Subgroup.normalizer (Bs : Set G), ¬ GGTransvection p Bs a

@[expose] def GGSixStepTwo (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) : Prop :=
  ∀ b ∈ Bs, b ≠ 1 → ∀ L₁ : Subgroup G,
    IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) →
    Nat.card (Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤ p ^ 2 →
      IsSubnormal L₁ (Subgroup.centralizer {b}) ∧
        GGControlsStrongFusion (ggM p B x L D J) (Subgroup.zpowers b)

@[expose] def GGSixStepThree (p : ℕ) (B : Subgroup G) (x : G) (L D J : Subgroup G) : Prop :=
  Odd ((ggG0 p B x L D J).relIndex (ggM p B x L D J)) ∧
    ∃ r : G, r ∈ ggG0 p B x L D J ∧ orderOf r = 2 ∧
      (∃ T : Sylow 2 (ggG0 p B x L D J),
        r ∈ (T : Subgroup (ggG0 p B x L D J)).map (ggG0 p B x L D J).subtype ∧
        (T : Subgroup (ggG0 p B x L D J)).map (ggG0 p B x L D J).subtype ≤
          Subgroup.centralizer {r}) ∧
      Subgroup.centralizer {r} ≤ ggM p B x L D J ∧
      GGControlsStrongFusion (ggM p B x L D J) (Subgroup.zpowers r)

end Defs

@[expose] def GGSixStepOneInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSixCtx p B Bs x L D J → GGSixStepOne p B Bs x L D J

@[expose] def GGSixStepTwoInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSixCtx p B Bs x L D J → GGSixStepOne p B Bs x L D J → GGSixStepTwo p B Bs x L D J

@[expose] def GGSixStepThreeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSixCtx p B Bs x L D J → GGSixStepOne p B Bs x L D J → GGSixStepTwo p B Bs x L D J →
      GGSixStepThree p B x L D J

theorem ggHoltAt_of_strongFusion {G : Type} [Group G] [Finite G] {G₀ M : Subgroup G}
    (hle : G₀ ≤ M) (hne : M ≠ ⊤) (hodd : Odd (G₀.relIndex M)) {r : G} (hrG₀ : r ∈ G₀)
    (hr : orderOf r = 2)
    (hT : ∃ T : Sylow 2 G₀, r ∈ (T : Subgroup G₀).map G₀.subtype ∧
      (T : Subgroup G₀).map G₀.subtype ≤ Subgroup.centralizer {r})
    (hfus : GGControlsStrongFusion M (Subgroup.zpowers r)) : GGHoltAt M := by
  have hprime : (orderOf r).Prime := hr ▸ Nat.prime_two
  obtain ⟨-, hfus'⟩ := (ggControlsStrongFusion_zpowers_iff hprime).mp hfus
  obtain ⟨T, hrT, hTc⟩ := hT
  obtain ⟨T', hT'⟩ := exists_sylow_two_map_eq_of_odd_relIndex hle hodd T
  refine ⟨hne, r, hr, fun q => ?_, T', by rw [hT']; exact hrT, by rw [hT']; exact hTc⟩
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [smul_mk_eq_iff, mk_eq_mk_one_iff]
    exact ⟨hfus' g, fun hg => M.mul_mem (M.mul_mem (M.inv_mem hg) (hle hrG₀)) hg⟩

theorem ggSix_holt_of_stepThree {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G}
    {x : G} {L D J : Subgroup G} (h3 : GGSixStepThree p B x L D J) :
    Subgroup.normalizer (ggG0 p B x L D J : Set G) = ⊤ ∨
      GGHoltAt (Subgroup.normalizer (ggG0 p B x L D J : Set G)) := by
  by_cases hM : Subgroup.normalizer (ggG0 p B x L D J : Set G) = ⊤
  · exact Or.inl hM
  · obtain ⟨hodd, r, hrG₀, hr, hT, -, hfus⟩ := h3
    exact Or.inr (ggHoltAt_of_strongFusion Subgroup.le_normalizer hM hodd hrG₀ hr hT hfus)

theorem ggSecSixInput_of_inputs (h1 : GGSixStepOneInput) (h2 : GGSixStepTwoInput)
    (h3 : GGSixStepThreeInput) : GGSecSixInput := by
  intro G _ _ _ hnonab hK hchar he p hp B x L hS hst Bs D J hsix
  have hctx : GGSixCtx p B Bs x L D J :=
    ⟨inferInstance, hnonab, hK, hchar, he, hp, hS, hst, hsix⟩
  have s1 := h1 G p B Bs x L D J hctx
  exact ggSix_holt_of_stepThree (h3 G p B Bs x L D J hctx s1 (h2 G p B Bs x L D J hctx s1))

section StepOne

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}

theorem le_ggG0_of_neighbor {y : G} {K : Subgroup G}
    (h : LargeEvenSHat p B y K ∧ LargeEvenNeighbor p x y K D J) : K ≤ ggG0 p B x L D J :=
  le_sup_of_le_right (le_iSup_of_le y (le_iSup_of_le K (le_iSup_of_le h le_rfl)))

theorem mem_normalizer_ggG0 {g : G} (hL : g ∈ Subgroup.normalizer (L : Set G))
    (hK : ∀ (y : G) (K : Subgroup G), LargeEvenSHat p B y K ∧ LargeEvenNeighbor p x y K D J →
      g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G) := by
  have key : ∀ c : G, c ∈ Subgroup.normalizer (L : Set G) →
      (∀ (y : G) (K : Subgroup G), LargeEvenSHat p B y K ∧ LargeEvenNeighbor p x y K D J →
        c ∈ Subgroup.normalizer (K : Set G)) →
      ∀ h ∈ ggG0 p B x L D J, c * h * c⁻¹ ∈ ggG0 p B x L D J := by
    intro c hcL hcK
    have hle : ggG0 p B x L D J ≤
        (ggG0 p B x L D J).comap (MulAut.conj c).toMonoidHom := by
      refine sup_le (fun l hl => ?_) (iSup_le fun y => iSup_le fun K => iSup_le fun hP => ?_)
      · exact le_sup_left (a := L) ((Subgroup.mem_normalizer_iff.mp hcL l).mp hl)
      · intro k hk
        exact le_ggG0_of_neighbor hP ((Subgroup.mem_normalizer_iff.mp (hcK y K hP) k).mp hk)
    intro h hh
    simpa using hle hh
  refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨key g hL hK h, fun hh => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hL) (fun y K hP => Subgroup.inv_mem _ (hK y K hP)) _ hh
  simpa [mul_assoc] using this

theorem centralizer_subcomp_le_normalizer_ggG0
    (h : ∀ g ∈ Subgroup.centralizer (D : Set G), g ∈ Subgroup.normalizer (L : Set G) ∧
      ∀ (y : G) (K : Subgroup G), LargeEvenSHat p B y K ∧ LargeEvenNeighbor p x y K D J →
        g ∈ Subgroup.normalizer (K : Set G)) :
    Subgroup.centralizer (D : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) :=
  fun g hg => mem_normalizer_ggG0 (h g hg).1 (h g hg).2

end StepOne

@[expose] def GGSixNeighborNormalInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSixCtx p B Bs x L D J → ∀ g ∈ Subgroup.centralizer (D : Set G),
      g ∈ Subgroup.normalizer (L : Set G) ∧
        ∀ (y : G) (K : Subgroup G), LargeEvenSHat p B y K ∧ LargeEvenNeighbor p x y K D J →
          g ∈ Subgroup.normalizer (K : Set G)

theorem centralizer_le_ggM_of_input (h : GGSixNeighborNormalInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hctx : GGSixCtx p B Bs x L D J) :
    Subgroup.centralizer (D : Set G) ≤ ggM p B x L D J :=
  centralizer_subcomp_le_normalizer_ggG0 (h G p B Bs x L D J hctx)

theorem mem_of_conj_mem_bstar {G : Type} [Group G] {M Bs : Subgroup G}
    (hfus : ∀ b ∈ Bs, ∀ g : G, g⁻¹ * b * g ∈ Bs →
      ∃ n ∈ Subgroup.normalizer (Bs : Set G), g⁻¹ * b * g = n⁻¹ * b * n)
    (hN : Subgroup.normalizer (Bs : Set G) ≤ M) {b g m : G} (hb : b ∈ Bs)
    (hC : Subgroup.centralizer {b} ≤ M) (hm : m ∈ M) (hy : m⁻¹ * (g⁻¹ * b * g) * m ∈ Bs) :
    g ∈ M := by
  have hy' : (g * m)⁻¹ * b * (g * m) ∈ Bs := by
    simpa [mul_assoc] using hy
  obtain ⟨n, hn, heq⟩ := hfus b hb (g * m) hy'
  have := M.mul_mem (mem_of_conj_eq_conj hC (hN hn) heq) (M.inv_mem hm)
  rwa [mul_inv_cancel_right] at this

theorem GGSixStepOne.exists_sylow {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (h1 : GGSixStepOne p B Bs x L D J)
    (hctx : GGSixCtx p B Bs x L D J) :
    ∃ P : Sylow p G, Bs ≤ (P : Subgroup G) ∧ (P : Subgroup G) ≤ ggM p B x L D J ∧
      ∀ E : Subgroup G, E ≤ (P : Subgroup G) → IsElemAbelian p E → Nat.card E = Nat.card Bs →
        E = Bs := by
  have : Fact p.Prime := ⟨hctx.2.2.2.2.2.1.1⟩
  obtain ⟨P, hBsP, huniq⟩ := h1.2.2.2.1
  have hBsEl : IsElemAbelian p Bs := hctx.2.2.2.2.2.2.2.2.1.2.1
  have hNM : Subgroup.normalizer (Bs : Set G) ≤ ggM p B x L D J := hctx.2.2.2.2.2.2.2.2.2.2.2.2
  have hN : Subgroup.normalizer (((P : Subgroup (ggM p B x L D J)).map
      (ggM p B x L D J).subtype : Subgroup G) : Set G) ≤ ggM p B x L D J := by
    intro n hn
    apply hNM
    apply mem_normalizer_of_map_conj_eq
    refine huniq _ ?_ (isElemAbelian_map_hom hBsEl _)
      (Subgroup.card_map_of_injective (MulAut.conj n).injective)
    rintro _ ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.mp hn a).mp (hBsP ha)
  obtain ⟨Q, hQ⟩ := exists_sylow_eq_map_of_normalizer_le P hN
  refine ⟨Q, by rw [hQ]; exact hBsP, by rw [hQ]; exact Subgroup.map_subtype_le _, ?_⟩
  rw [hQ]
  exact huniq

theorem GGSixStepOne.exists_mem_normalizer_conj_eq {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hctx : GGSixCtx p B Bs x L D J)
    (h1 : GGSixStepOne p B Bs x L D J) {b g : G} (hb : b ∈ Bs) (hg : g⁻¹ * b * g ∈ Bs) :
    ∃ n ∈ Subgroup.normalizer (Bs : Set G), g⁻¹ * b * g = n⁻¹ * b * n := by
  have : Fact p.Prime := ⟨hctx.2.2.2.2.2.1.1⟩
  obtain ⟨P, -, -, huniq⟩ := h1.exists_sylow hctx
  exact CFSG.StandardType.exists_mem_normalizer_conj_eq hctx.2.2.2.2.2.2.2.2.1.2.1 P huniq hb hg

theorem GGSixStepOne.mem_of_conj_mem_bstar {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hctx : GGSixCtx p B Bs x L D J)
    (h1 : GGSixStepOne p B Bs x L D J) {b g m : G} (hb : b ∈ Bs)
    (hC : Subgroup.centralizer {b} ≤ ggM p B x L D J) (hm : m ∈ ggM p B x L D J)
    (hy : m⁻¹ * (g⁻¹ * b * g) * m ∈ Bs) : g ∈ ggM p B x L D J :=
  CFSG.StandardType.mem_of_conj_mem_bstar
    (fun _ hb' _ hg' => h1.exists_mem_normalizer_conj_eq hctx hb' hg')
    hctx.2.2.2.2.2.2.2.2.2.2.2.2 hb hC hm hy

theorem GGSixHyp.card_le_card_bstar {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hp : p.Prime)
    (hsix : GGSixHyp p B Bs x L D J) {E : Subgroup G} (hE : IsElemAbelian p E) :
    Nat.card E ≤ Nat.card Bs := by
  have : Fact p.Prime := ⟨hp⟩
  have hEp : IsPGroup p E := fun y => ⟨1, Subtype.ext (by simpa using hE.2 y y.2)⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  set A : Subgroup (⊤ : Subgroup G) := E.subgroupOf ⊤ with hA
  have hAE : Nat.card A = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_top : E ≤ ⊤)).toEquiv
  have hAel : IsElementaryAbelian p A := by
    have := hE.1
    refine { is_comm := ⟨fun a b => ?_⟩, exponent_dvd_p := ?_ }
    · apply Subtype.ext
      apply Subtype.ext
      have h := congrArg Subtype.val (mul_comm' (⟨(a : G), a.2⟩ : E) ⟨(b : G), b.2⟩)
      simpa using h
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
      apply Subtype.ext
      apply Subtype.ext
      simpa using hE.2 (a : G) a.2
  have hle : k ≤ CFSG.pRank p (⊤ : Subgroup G) := by
    refine le_csSup ⟨Nat.card (⊤ : Subgroup G), ?_⟩ ⟨A, hAel, by rw [hAE, hk]⟩
    rintro r ⟨A', -, hA'⟩
    calc r ≤ p ^ r := (Nat.lt_pow_self hp.one_lt).le
      _ = Nat.card A' := hA'.symm
      _ ≤ Nat.card (⊤ : Subgroup G) := Subgroup.card_le_card_group A'
  rw [hk, hsix.1.2.2]
  exact Nat.pow_le_pow_right hp.pos hle

theorem GGSixHyp.mem_of_mem_centralizer {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hp : p.Prime)
    (hsix : GGSixHyp p B Bs x L D J) {e : G} (he : e ∈ Subgroup.centralizer (Bs : Set G))
    (hep : e ^ p = 1) : e ∈ Bs :=
  mem_of_mem_centralizer_of_maximal hsix.1.2.1 (fun _ hE => hsix.card_le_card_bstar hp hE) he hep

end CFSG.StandardType
