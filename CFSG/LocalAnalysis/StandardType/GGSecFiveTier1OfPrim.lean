module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePrimDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneWeyl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneCard
public import CFSG.LocalAnalysis.StandardType.GGSimplyLacedTits
public import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl
public import CFSG.LocalAnalysis.StandardType.GGHalfCentGroup

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT Matrix

open scoped MatrixGroups

section Helpers

variable {G : Type} [Group G] [Finite G]

theorem ggAutomizerJoin_le_ggAutomizer (L Bs : Subgroup G) (𝒦 : Finset (Subgroup G)) :
    ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer (L ⊔ ⨆ K ∈ 𝒦, K) Bs := by
  unfold ggAutomizerJoin
  refine sup_le (ggAutomizer_mono Bs le_sup_left) (iSup₂_le fun K hK => ggAutomizer_mono Bs ?_)
  exact (le_iSup₂ (f := fun K (_ : K ∈ 𝒦) => K) K hK).trans le_sup_right

theorem ggRouteCfg_prime {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (h : GGSecFiveRouteCfg p B Bs x L D J 𝒦) :
    p.Prime ∧ p ≠ 2 := by
  obtain ⟨⟨⟨⟨_, _, _, _, _, hβ, _⟩, _⟩, _⟩, _⟩ := h
  obtain ⟨hp, hp2, _⟩ := hβ
  exact ⟨hp, hp2⟩

theorem ggRouteCfg_ne_bot {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (h : GGSecFiveRouteCfg p B Bs x L D J 𝒦) : L ≠ ⊥ := by
  obtain ⟨⟨⟨⟨_, _, _, _, _, _, hS, _⟩, _⟩, _⟩, _⟩ := h
  obtain ⟨_, _, _, hC, _⟩ := hS
  exact GGHalf.ne_bot_of_isComponentOf hC

private lemma coe_presentation_mul {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {ι : Type}
    {M : CoxeterMatrix ι} (e : M.Group ≃* ↥A) (x y : M.Group) :
    ((e (x * y) : ↥A) : MulAut ↥Bs) = ((e x : ↥A) : MulAut ↥Bs) * ((e y : ↥A) : MulAut ↥Bs) := by
  rw [map_mul, Subgroup.coe_mul]

theorem ggSimple_eq_conj_of_mem_ggCoxRefl {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {ι : Type}
    {M : CoxeterMatrix ι} (e : M.Group ≃* ↥A) (hM : GGSimplyLacedConnected M)
    {r₀ : MulAut ↥Bs} (hr₀ : r₀ ∈ ggCoxRefl M e) (i : ι) :
    ∃ a ∈ A, ((e (M.simple i) : ↥A) : MulAut ↥Bs) = a * r₀ * a⁻¹ := by
  obtain ⟨w, k, rfl⟩ := hr₀
  obtain ⟨u, hu⟩ := ggSimplyLaced_simple_conj hM k i
  refine ⟨((e (u * w⁻¹) : ↥A) : MulAut ↥Bs), (e (u * w⁻¹)).2, ?_⟩
  rw [hu]
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem ggCoxRefl_conj_of_connected {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {ι : Type}
    {M : CoxeterMatrix ι} (e : M.Group ≃* ↥A) (hM : GGSimplyLacedConnected M)
    {r₀ r : MulAut ↥Bs} (hr₀ : r₀ ∈ ggCoxRefl M e) (hr : r ∈ ggCoxRefl M e) :
    ∃ a ∈ A, r = a * r₀ * a⁻¹ := by
  obtain ⟨w, i, rfl⟩ := hr
  obtain ⟨a, haA, hai⟩ := ggSimple_eq_conj_of_mem_ggCoxRefl e hM hr₀ i
  refine ⟨((e w : ↥A) : MulAut ↥Bs) * a, A.mul_mem (e w).2 haA, ?_⟩
  have h1 : ((e (w * M.simple i * w⁻¹) : ↥A) : MulAut ↥Bs) =
      ((e w : ↥A) : MulAut ↥Bs) * ((e (M.simple i) : ↥A) : MulAut ↥Bs) *
        ((e w : ↥A) : MulAut ↥Bs)⁻¹ := by
    simp [map_mul, map_inv]
  rw [h1, hai]
  group

theorem ggCoxConj_ne {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {ι : Type}
    {M : CoxeterMatrix ι} (e : M.Group ≃* ↥A) (hinj : Function.Injective M.simple) (w : M.Group)
    {i j : ι} (hij : i ≠ j) :
    ((e (w * M.simple i * w⁻¹) : ↥A) : MulAut ↥Bs) ≠
      ((e (w * M.simple j * w⁻¹) : ↥A) : MulAut ↥Bs) := by
  intro h
  apply hij
  apply hinj
  have h1 : e (w * M.simple i * w⁻¹) = e (w * M.simple j * w⁻¹) := Subtype.val_injective h
  have h2 : w * M.simple i * w⁻¹ = w * M.simple j * w⁻¹ := e.injective h1
  rw [mul_assoc, mul_assoc] at h2
  exact mul_right_cancel (mul_left_cancel h2)

theorem ggCoxConj_comm {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {ι : Type}
    {M : CoxeterMatrix ι} (e : M.Group ≃* ↥A) (w : M.Group) {i j : ι}
    (h : M.simple i * M.simple j = M.simple j * M.simple i) :
    ((e (w * M.simple i * w⁻¹) : ↥A) : MulAut ↥Bs) *
        ((e (w * M.simple j * w⁻¹) : ↥A) : MulAut ↥Bs) =
      ((e (w * M.simple j * w⁻¹) : ↥A) : MulAut ↥Bs) *
        ((e (w * M.simple i * w⁻¹) : ↥A) : MulAut ↥Bs) := by
  have hXY : (w * M.simple i * w⁻¹) * (w * M.simple j * w⁻¹) =
      (w * M.simple j * w⁻¹) * (w * M.simple i * w⁻¹) := by
    calc (w * M.simple i * w⁻¹) * (w * M.simple j * w⁻¹)
        = w * (M.simple i * M.simple j) * w⁻¹ := by group
      _ = w * (M.simple j * M.simple i) * w⁻¹ := by rw [h]
      _ = (w * M.simple j * w⁻¹) * (w * M.simple i * w⁻¹) := by group
  rw [← coe_presentation_mul e (w * M.simple i * w⁻¹) (w * M.simple j * w⁻¹),
    ← coe_presentation_mul e (w * M.simple j * w⁻¹) (w * M.simple i * w⁻¹)]
  rw [hXY]

theorem ggCoxConj_ne_comm {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {ι : Type}
    {M : CoxeterMatrix ι} (e : M.Group ≃* ↥A) (w : M.Group) {i j : ι}
    (h : M.simple i * M.simple j ≠ M.simple j * M.simple i) :
    ((e (w * M.simple i * w⁻¹) : ↥A) : MulAut ↥Bs) *
        ((e (w * M.simple j * w⁻¹) : ↥A) : MulAut ↥Bs) ≠
      ((e (w * M.simple j * w⁻¹) : ↥A) : MulAut ↥Bs) *
        ((e (w * M.simple i * w⁻¹) : ↥A) : MulAut ↥Bs) := by
  intro hc
  apply h
  have hc' : ((e ((w * M.simple i * w⁻¹) * (w * M.simple j * w⁻¹)) : ↥A) : MulAut ↥Bs) =
      ((e ((w * M.simple j * w⁻¹) * (w * M.simple i * w⁻¹)) : ↥A) : MulAut ↥Bs) :=
    (coe_presentation_mul e (w * M.simple i * w⁻¹) (w * M.simple j * w⁻¹)).trans
      (hc.trans (coe_presentation_mul e (w * M.simple j * w⁻¹) (w * M.simple i * w⁻¹)).symm)
  have h1 : e ((w * M.simple i * w⁻¹) * (w * M.simple j * w⁻¹)) =
      e ((w * M.simple j * w⁻¹) * (w * M.simple i * w⁻¹)) := Subtype.val_injective hc'
  have hXY : (w * M.simple i * w⁻¹) * (w * M.simple j * w⁻¹) =
      (w * M.simple j * w⁻¹) * (w * M.simple i * w⁻¹) := e.injective h1
  have hXY' : w * (M.simple i * M.simple j) * w⁻¹ =
      w * (M.simple j * M.simple i) * w⁻¹ := by
    convert hXY using 1 <;> group
  exact mul_left_cancel (mul_right_cancel hXY')

theorem ggRankOnePerf_conj_card_le {Bs H : Subgroup G} {a : MulAut ↥Bs} (ha : a ∈ ggAutomizer H Bs)
    (r : MulAut ↥Bs) :
    Nat.card (ggRankOnePerf Bs (a * r * a⁻¹)) = Nat.card (ggRankOnePerf Bs r) ∧
      (ggRankOnePerf Bs r ≤ H → ggRankOnePerf Bs (a * r * a⁻¹) ≤ H) := by
  obtain ⟨g, hgH, -, hg⟩ := mem_ggAutomizer_iff.mp ha
  have hmap : (ggRankOnePerf Bs r).map (MulAut.conj g).toMonoidHom =
      ggRankOnePerf Bs (a * r * a⁻¹) := ggRankOnePerf_map_conj hg r
  constructor
  · rw [← hmap]
    exact Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective
  · intro hle z hz
    rw [← hmap] at hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact H.mul_mem (H.mul_mem hgH (hle hy)) (H.inv_mem hgH)

private theorem conj_presentation_simple {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)}
    {ι : Type} {M : CoxeterMatrix ι} (e : M.Group ≃* ↥A) (w s : M.Group) :
    ((e w⁻¹ : ↥A) : MulAut ↥Bs) * ((e (w * s * w⁻¹) : ↥A) : MulAut ↥Bs) *
      ((e w⁻¹ : ↥A) : MulAut ↥Bs)⁻¹ = ((e s : ↥A) : MulAut ↥Bs) := by
  rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul]
  congr 1
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  group

theorem ggRankOnePerf_comm_of_conj_pair {Bs H : Subgroup G} {A : Subgroup (MulAut ↥Bs)}
    (hA : A ≤ ggAutomizer H Bs) {ι : Type} {M : CoxeterMatrix ι} (e : M.Group ≃* ↥A)
    (w : M.Group) (i j : ι)
    (h : ∀ x ∈ ggRankOnePerf Bs ((e (w * M.simple i * w⁻¹) : ↥A) : MulAut ↥Bs),
         ∀ y ∈ ggRankOnePerf Bs ((e (w * M.simple j * w⁻¹) : ↥A) : MulAut ↥Bs), x * y = y * x) :
    ∀ x ∈ ggRankOnePerf Bs ((e (M.simple i) : ↥A) : MulAut ↥Bs),
    ∀ y ∈ ggRankOnePerf Bs ((e (M.simple j) : ↥A) : MulAut ↥Bs), x * y = y * x := by
  have h' := ggRankOnePerf_commute_transport
    (a := ((e w⁻¹ : ↥A) : MulAut ↥Bs))
    (r := ((e (w * M.simple i * w⁻¹) : ↥A) : MulAut ↥Bs))
    (r' := ((e (w * M.simple j * w⁻¹) : ↥A) : MulAut ↥Bs))
    (hA (e w⁻¹).2) h
  rwa [conj_presentation_simple e w (M.simple i), conj_presentation_simple e w (M.simple j)] at h'

theorem ggLinearBlockPair_of_conj_pair {Bs H : Subgroup G} {A : Subgroup (MulAut ↥Bs)}
    (hA : A ≤ ggAutomizer H Bs) {ι : Type} {M : CoxeterMatrix ι} (e : M.Group ≃* ↥A)
    (w : M.Group) (i j : ι) {F' : Type} [Field F'] [Finite F'] {W : Subgroup G}
    (hpair : LinearBlockStandardPair F' W
      (ggRankOnePerf Bs ((e (w * M.simple i * w⁻¹) : ↥A) : MulAut ↥Bs))
      (ggRankOnePerf Bs ((e (w * M.simple j * w⁻¹) : ↥A) : MulAut ↥Bs)))
    {F : Type} [Field F] [Finite F]
    (hcard : Nat.card (ggRankOnePerf Bs ((e (M.simple i) : ↥A) : MulAut ↥Bs)) = Nat.card SL(2, F)) :
    ∃ W' : Subgroup G, LinearBlockStandardPair F W'
      (ggRankOnePerf Bs ((e (M.simple i) : ↥A) : MulAut ↥Bs))
      (ggRankOnePerf Bs ((e (M.simple j) : ↥A) : MulAut ↥Bs)) := by
  obtain ⟨g, -, -, hg⟩ := mem_ggAutomizer_iff.mp (hA (e w⁻¹).2)
  have hthis := ggLinearBlockPair_map_conj hpair g
  rw [ggRankOnePerf_map_conj (g := g) (a := ((e w⁻¹ : ↥A) : MulAut ↥Bs)) hg
        ((e (w * M.simple i * w⁻¹) : ↥A) : MulAut ↥Bs),
      conj_presentation_simple e w (M.simple i)] at hthis
  rw [ggRankOnePerf_map_conj (g := g) (a := ((e w⁻¹ : ↥A) : MulAut ↥Bs)) hg
        ((e (w * M.simple j * w⁻¹) : ↥A) : MulAut ↥Bs),
      conj_presentation_simple e w (M.simple j)] at hthis
  exact ggLinearBlockPair_exists_of_card_eq hthis hcard

theorem ggLe_iSup_ggRankOnePerf_of_gen {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {ι : Type}
    {M : CoxeterMatrix ι} (e : M.Group ≃* ↥A)
    (hN : ∀ i : ι, ∃ n ∈ ggRankOnePerf Bs ((e (M.simple i) : ↥A) : MulAut ↥Bs),
      n ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ b : ↥Bs, ((((e (M.simple i) : ↥A) : MulAut ↥Bs) b : ↥Bs) : G) = n * b * n⁻¹)
    {X : Subgroup G}
    (hgen : X = ⨆ r ∈ {r : MulAut ↥Bs | r ∈ ggAutomizer X Bs ∧ r ∈ ggCoxRefl M e},
      ggRankOneIn X Bs r)
    (hL1 : ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → ggRankOnePerf Bs r = ggRankOneIn X Bs r) :
    X ≤ ⨆ i : ι, ggRankOnePerf Bs ((e (M.simple i) : ↥A) : MulAut ↥Bs) := by
  let N : Subgroup G := ⨆ i : ι, ggRankOnePerf Bs ((e (M.simple i) : ↥A) : MulAut ↥Bs)
  calc X = ⨆ r ∈ {r : MulAut ↥Bs | r ∈ ggAutomizer X Bs ∧ r ∈ ggCoxRefl M e},
        ggRankOneIn X Bs r := hgen
    _ ≤ N := by
      refine iSup₂_le fun r hr => ?_
      rw [(hL1 r hr.1 hr.2).symm]
      obtain ⟨w, i, rfl⟩ := hr.2
      exact ggRankOnePerf_conj_le_iSup e hN w i

theorem ggFin_four_le_card {F : Type} [Field F] [Finite F] (hc : CharP F 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ Nat.card F - 1) : 4 ≤ Nat.card F := by
  haveI := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  have hcard : Nat.card F = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hn]
  rw [hcard] at h ⊢
  have hpos : 0 < 2 ^ (n : ℕ) - 1 := by
    have h1 : 1 < 2 ^ (n : ℕ) := Nat.one_lt_two_pow n.pos.ne'
    omega
  have hp_le : p ≤ 2 ^ (n : ℕ) - 1 := Nat.le_of_dvd hpos h
  have h2p : 2 ≤ p := hp.two_le
  generalize hq : 2 ^ (n : ℕ) = q at *
  omega

end Helpers

section Main

theorem ggSplitLie_of_prim_refl (hL1 : GGSecFiveL1CoxInput) (hRk1 : GGSecFiveRk1Input)
    (hGen : GGSecFiveGenCoxInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hsplit : GGSplitLie p L) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦) {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs)
    (hrC : r ∈ ggCoxRefl M e) : GGSplitLie p X := by
  by_contra hns
  haveI : Finite ι := ggIsWeylMatrix_finite hpres.1
  have hconn : GGSimplyLacedConnected M := ggSimplyLacedConnected_of_weyl hpres.1 hle3
  have hAH : ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer (L ⊔ ⨆ K ∈ 𝒦, K) Bs :=
    ggAutomizerJoin_le_ggAutomizer L Bs 𝒦
  obtain ⟨hpp, hp2⟩ := ggRouteCfg_prime hcfg
  obtain ⟨r₀, hr₀A, hr₀C⟩ : ∃ r₀ : MulAut ↥Bs, r₀ ∈ ggAutomizer L Bs ∧ r₀ ∈ ggCoxRefl M e := by
    by_contra hne
    refine ggRouteCfg_ne_bot hcfg (le_bot_iff.mp ?_)
    calc L = ⨆ r ∈ {r : MulAut ↥Bs | r ∈ ggAutomizer L Bs ∧ r ∈ ggCoxRefl M e},
          ggRankOneIn L Bs r :=
          hGen G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 L (Or.inl rfl) hsplit
      _ ≤ ⊥ := iSup₂_le fun r hr => absurd ⟨r, hr.1, hr.2⟩ hne
  obtain ⟨F, hF, hFfin, θ, -, hθinj, hθrange, -, hpF, -⟩ :=
    hRk1 G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 L (Or.inl rfl) r₀ hr₀A hr₀C
  obtain ⟨F', hF', hF'fin, θ', -, hθ'inj, hθ'range, -, -, hpF'⟩ :=
    hRk1 G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 X hX r hrA hrC
  obtain ⟨a, haA, hra⟩ := ggCoxRefl_conj_of_connected e hconn hr₀C hrC
  have hL1r₀ : ggRankOnePerf Bs r₀ = ggRankOneIn L Bs r₀ :=
    hL1 G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 L (Or.inl rfl) r₀ hr₀A hr₀C
  have hL1r : ggRankOnePerf Bs r = ggRankOneIn X Bs r :=
    hL1 G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 X hX r hrA hrC
  have hc₀ : Nat.card (ggRankOnePerf Bs r₀) = Nat.card SL(2, F) := by
    rw [hL1r₀, ← hθrange]
    exact Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv.symm
  have hc : Nat.card (ggRankOnePerf Bs r) = Nat.card SL(2, F') := by
    rw [hL1r, ← hθ'range]
    exact Nat.card_congr (MonoidHom.ofInjective hθ'inj).toEquiv.symm
  have hcr : Nat.card (ggRankOnePerf Bs r) = Nat.card (ggRankOnePerf Bs r₀) := by
    rw [hra]
    exact (ggRankOnePerf_conj_card_le (hAH haA) r₀).1
  have hFF : Nat.card F = Nat.card F' := ggSL2_card_inj (by rw [← hc₀, ← hc, hcr])
  have hq : 1 ≤ Nat.card F := le_of_lt Finite.one_lt_card
  have h1 : p ∣ Nat.card F - 1 := hpF hsplit
  have h2 : p ∣ Nat.card F + 1 := hFF ▸ hpF' hns
  have h3 : p ∣ 2 := by
    have h4 : p ∣ (Nat.card F + 1) - (Nat.card F - 1) := Nat.dvd_sub h2 h1
    have h5 : (Nat.card F + 1) - (Nat.card F - 1) = 2 := by omega
    rwa [h5] at h4
  have h6 : p ≤ 2 := Nat.le_of_dvd (by norm_num) h3
  have h7 : 2 ≤ p := hpp.two_le
  omega

theorem ggSecFiveTier1Input_of_prim (hL1 : GGSecFiveL1CoxInput) (hRk1 : GGSecFiveRk1Input)
    (hGen : GGSecFiveGenCoxInput) (hOrb : GGSecFiveOrbInput) (hL2 : GGSecFiveL2SplitInput)
    (hRk2 : GGSecFiveRk2Input) (hNbr : GGSecFiveSplitNbrInput) : GGSecFiveTier1Input := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3
  have hAH : ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer (L ⊔ ⨆ K ∈ 𝒦, K) Bs :=
    ggAutomizerJoin_le_ggAutomizer L Bs 𝒦
  obtain ⟨hpp, hp2⟩ := ggRouteCfg_prime hcfg
  haveI : Finite ι := ggIsWeylMatrix_finite hpres.1
  have hconn : GGSimplyLacedConnected M := ggSimplyLacedConnected_of_weyl hpres.1 hle3
  have hsl : GGSimplyLaced M := hconn.1
  have hsplitX : ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → GGSplitLie p X := by
    intro X hX
    rcases hX with hXL | hK
    · rw [hXL]
      exact hsplit
    · exact hNbr G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 X hK
  have hgenX : ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) →
      X = ⨆ r ∈ {r : MulAut ↥Bs | r ∈ ggAutomizer X Bs ∧ r ∈ ggCoxRefl M e},
        ggRankOneIn X Bs r :=
    fun X hX => hGen G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 X hX (hsplitX X hX)
  have hL1X : ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e →
      ggRankOnePerf Bs r = ggRankOneIn X Bs r :=
    fun X hX => hL1 G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 X hX
  obtain ⟨r₀, hr₀A, hr₀C⟩ : ∃ r₀ : MulAut ↥Bs, r₀ ∈ ggAutomizer L Bs ∧ r₀ ∈ ggCoxRefl M e := by
    by_contra hne
    refine ggRouteCfg_ne_bot hcfg (le_bot_iff.mp ?_)
    calc L = ⨆ r ∈ {r : MulAut ↥Bs | r ∈ ggAutomizer L Bs ∧ r ∈ ggCoxRefl M e},
          ggRankOneIn L Bs r := hgenX L (Or.inl rfl)
      _ ≤ ⊥ := iSup₂_le fun r hr => absurd ⟨r, hr.1, hr.2⟩ hne
  obtain ⟨F, hF, hFfin, θ, hchar, hθinj, hθrange, ⟨n₀, hn₀L, hn₀N, hn₀r⟩, hpF, -⟩ :=
    hRk1 G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 L (Or.inl rfl) r₀ hr₀A hr₀C
  have hL1r₀ : ggRankOnePerf Bs r₀ = ggRankOneIn L Bs r₀ := hL1X L (Or.inl rfl) r₀ hr₀A hr₀C
  have hn₀S : n₀ ∈ ggRankOnePerf Bs r₀ := hL1r₀ ▸ hn₀L
  have hcard₀ : Nat.card (ggRankOnePerf Bs r₀) = Nat.card SL(2, F) := by
    rw [hL1r₀, ← hθrange]
    exact Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv.symm
  have hsimple : ∀ i : ι, ∃ a ∈ ggAutomizerJoin L Bs 𝒦,
      ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) = a * r₀ * a⁻¹ :=
    fun i => ggSimple_eq_conj_of_mem_ggCoxRefl e hconn hr₀C i
  have hN : ∀ i : ι, ∃ n ∈ ggRankOnePerf Bs
      ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs),
      n ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ b : ↥Bs, ((((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) b : ↥Bs) : G) =
        n * b * n⁻¹ := by
    intro i
    obtain ⟨a, haA, hai⟩ := hsimple i
    obtain ⟨g, -, -, -, hnS, hnN, hnr⟩ := ggWeylElt_conj (hAH haA) hn₀S hn₀N hn₀r
    exact ⟨g * n₀ * g⁻¹, by rw [hai]; exact hnS, hnN, by rw [hai]; exact hnr⟩
  have hcard : ∀ i : ι, Nat.card (ggRankOnePerf Bs
      ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) = Nat.card SL(2, F) := by
    intro i
    obtain ⟨a, haA, hai⟩ := hsimple i
    rw [hai, (ggRankOnePerf_conj_card_le (hAH haA) r₀).1, hcard₀]
  refine ⟨F, hF, hFfin, hchar, ggFin_four_le_card hchar hpp hp2 (hpF hsplit), ?_, ?_, ?_⟩
  · intro i j hij hM2
    by_cases hO : GGOrbPair L Bs 𝒦 M e i j
    · obtain ⟨w, X, hX, hrX, hr'X⟩ := hO
      have hrC : ((e (w * M.simple i * w⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈
          ggCoxRefl M e := ⟨w, i, rfl⟩
      have hr'C : ((e (w * M.simple j * w⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈
          ggCoxRefl M e := ⟨w, j, rfl⟩
      have hne := ggCoxConj_ne e (ggSimplyLaced_simple_injective hsl) w hij
      have hcomm := ggCoxConj_comm e w (ggSimplyLaced_simple_comm hM2)
      have h1 := (hRk2 G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 X hX _ hrX hrC _ hr'X hr'C
        hne).1 hcomm
      refine ggRankOnePerf_comm_of_conj_pair hAH e w i j ?_
      intro a ha b hb
      rw [hL1X X hX _ hrX hrC] at ha
      rw [hL1X X hX _ hr'X hr'C] at hb
      exact h1 a ha b hb
    · exact hL2 G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 i j hij hM2 hO
  · intro i j hM3
    have hij : i ≠ j := by
      rintro rfl
      have h1 := M.diagonal i
      omega
    obtain ⟨w, X, hX, hrX, hr'X⟩ :=
      hOrb G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 i j hM3
    have hrC : ((e (w * M.simple i * w⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈
        ggCoxRefl M e := ⟨w, i, rfl⟩
    have hr'C : ((e (w * M.simple j * w⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈
        ggCoxRefl M e := ⟨w, j, rfl⟩
    have hne := ggCoxConj_ne e (ggSimplyLaced_simple_injective hsl) w hij
    have hnc := ggCoxConj_ne_comm e w (ggSimplyLaced_simple_noncomm hsl hM3)
    obtain ⟨F', hF', hF'fin, W', -, hpair⟩ :=
      (hRk2 G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 X hX _ hrX hrC _ hr'X hr'C hne).2
        (hsplitX X hX) hnc
    rw [← hL1X X hX _ hrX hrC, ← hL1X X hX _ hr'X hr'C] at hpair
    exact ggLinearBlockPair_of_conj_pair hAH e w i j hpair (hcard i)
  · apply le_antisymm
    · refine iSup_le fun i => ?_
      obtain ⟨a, haA, hai⟩ := hsimple i
      rw [hai]
      refine (ggRankOnePerf_conj_card_le (hAH haA) r₀).2 ?_
      rw [hL1r₀]
      exact (ggRankOneIn_le L Bs r₀).trans le_sup_left
    · refine sup_le ?_ (iSup₂_le fun K hK => ?_)
      · exact ggLe_iSup_ggRankOnePerf_of_gen e hN (hgenX L (Or.inl rfl)) (hL1X L (Or.inl rfl))
      · exact ggLe_iSup_ggRankOnePerf_of_gen e hN (hgenX K (Or.inr hK)) (hL1X K (Or.inr hK))

end Main

end CFSG.StandardType
