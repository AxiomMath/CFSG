module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoBridge
public import CFSG.LocalAnalysis.StandardType.GGOneFiveInputs
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Automizer

variable {G : Type} [Group G]

theorem mem_ggInduced_iff {H Bs : Subgroup G} {φ : MulAut ↥Bs} :
    φ ∈ ggInduced H Bs ↔ ∃ g : Subgroup.normalizer (Bs : Set G), (g : G) ∈ H ∧
      Bs.normalizerMonoidHom g = φ := by
  constructor
  · rintro ⟨g, hgH, hgN, hφ⟩
    exact ⟨⟨g, hgN⟩, hgH, MulEquiv.ext fun b => Subtype.ext (hφ b).symm⟩
  · rintro ⟨⟨g, hgN⟩, hgH, rfl⟩
    exact ⟨g, hgH, hgN, fun b => rfl⟩

theorem mem_ggInduced_top_iff {Bs : Subgroup G} {φ : MulAut ↥Bs} :
    φ ∈ ggInduced ⊤ Bs ↔ φ ∈ Bs.normalizerMonoidHom.range := by
  rw [mem_ggInduced_iff]
  exact ⟨fun ⟨g, _, hg⟩ => ⟨g, hg⟩, fun ⟨g, hg⟩ => ⟨g, Subgroup.mem_top _, hg⟩⟩

theorem noNormalP_of_ggOpAutTrivial {p : ℕ} {Bs : Subgroup G} (hO : GGOpAutTrivial p Bs) :
    ∀ N : Subgroup (MulAut ↥Bs), N ≤ Bs.normalizerMonoidHom.range →
      (∀ a ∈ Bs.normalizerMonoidHom.range, ∀ n ∈ N, a * n * a⁻¹ ∈ N) → IsPGroup p N →
        N = ⊥ := by
  intro N hNr hNn hNp
  set κ := Bs.normalizerMonoidHom with hκ
  set X : Subgroup G := (N.comap κ).map (Subgroup.normalizer (Bs : Set G)).subtype with hX
  have hmemX : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (Bs : Set G)),
      g ∈ X ↔ κ ⟨g, hg⟩ ∈ N := by
    intro g hg
    constructor
    · rintro ⟨m, hm, hmg⟩
      have : m = ⟨g, hg⟩ := Subtype.ext hmg
      rw [← this]
      exact hm
    · intro h
      exact ⟨⟨g, hg⟩, h, rfl⟩
  have hXN : X ≤ Subgroup.normalizer (Bs : Set G) := Subgroup.map_subtype_le _
  have hCX : Subgroup.centralizer (Bs : Set G) ≤ X := by
    intro g hg
    have hgN : g ∈ Subgroup.normalizer (Bs : Set G) := Subgroup.centralizer_le_normalizer _ hg
    rw [hmemX g hgN]
    have h1 : κ ⟨g, hgN⟩ = 1 := by
      ext b
      show g * b * g⁻¹ = b
      rw [← (Subgroup.mem_centralizer_iff.mp hg) b b.2, mul_inv_cancel_right]
    rw [h1]
    exact N.one_mem
  have hXn : (X.subgroupOf (Subgroup.normalizer (Bs : Set G))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    rw [hmemX _ n.2] at hn
    rw [hmemX _ (g * n * g⁻¹).2]
    have : κ (g * n * g⁻¹) = κ g * κ n * (κ g)⁻¹ := by rw [map_mul, map_mul, map_inv]
    rw [show (⟨((g * n * g⁻¹ : Subgroup.normalizer (Bs : Set G)) : G), (g * n * g⁻¹).2⟩ :
        Subgroup.normalizer (Bs : Set G)) = g * n * g⁻¹ from rfl, this]
    exact hNn _ ⟨g, rfl⟩ _ hn
  have hXp : ∀ g ∈ X, ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (Bs : Set G) := by
    rintro g ⟨m, hm, rfl⟩
    obtain ⟨k, hk⟩ := hNp ⟨κ m, hm⟩
    refine ⟨k, ?_⟩
    have h1 : κ (m ^ p ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    have h2 : m ^ p ^ k ∈ κ.ker := h1
    rw [hκ, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h2
    simpa using h2
  have hXC := hO X hXN hCX hXn hXp
  rw [eq_bot_iff]
  intro n hn
  obtain ⟨m, rfl⟩ := hNr hn
  have hm : (m : G) ∈ X := (hmemX m m.2).mpr hn
  have h2 : m ∈ κ.ker := by
    rw [hκ, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
    exact hXC hm
  rw [MonoidHom.mem_ker] at h2
  rw [h2]
  exact Subgroup.one_mem _

end Automizer

@[expose] def GGBstarInnerDiagLInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagOn Bs L

@[expose] def GGLTransvectionCenterInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
      ∀ φ ∈ ggInduced (Subgroup.centralizer ({x} : Set G)) Bs, GGIsTransvection p φ →
        ∀ b : ↥Bs, ((b⁻¹ * φ b : ↥Bs) : G) ∈ Subgroup.zpowers x

@[expose] def GGLNoInvariantLineInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
      ∀ E : Subgroup G, E ≤ Bs → x ∈ E → Nat.card E = p ^ 2 →
        ¬ Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (E : Set G)

section NoTransvection

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_zpowers_mk_of_coe_mem {Bs : Subgroup G} {x : G} (hx : x ∈ Bs) {b : ↥Bs}
    (hb : (b : G) ∈ Subgroup.zpowers x) : b ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩

theorem ggNoTransvection_of (hK : GGKantorReductionInput) (hcen : GGLTransvectionCenterInput)
    (hline : GGLNoInvariantLineInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig p B Bs x L D J) (hO : GGOpAutTrivial p Bs) (hL : GGInnerDiagOn Bs L) :
    GGNoTransvection p Bs := by
  intro φ hφ htv
  obtain ⟨hT, hBs, hstd⟩ := hC
  have hp : p.Prime := hT.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hT.2.2.2.2.2.1.2.1
  have hxBs : x ∈ Bs := hBs.1 hT.2.2.2.2.2.2.1.2.1
  have hcomm : ∀ a b : ↥Bs, a * b = b * a := fun a b => hBs.2.1.1.is_comm.comm a b
  have hexp : ∀ a : ↥Bs, a ^ p = 1 := fun a => Subtype.ext (by simpa using hBs.2.1.2 a a.2)
  rcases exists_transvection_fix_or_plane_mul hK hp hp2 hcomm hexp Bs.normalizerMonoidHom.range
      (noNormalP_of_ggOpAutTrivial hO) ⟨φ, mem_ggInduced_top_iff.mp hφ, htv⟩ ⟨x, hxBs⟩ with
    ⟨ψ, ⟨g, rfl⟩, hψtv, hψx, b, hb⟩ | ⟨E, hEcard, hxE, hEinv⟩
  · have hgx : (g : G) ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : (g : G) * x * (g : G)⁻¹ = x := congrArg Subtype.val hψx
      calc (g : G) * x = (g : G) * x * (g : G)⁻¹ * (g : G) := by group
        _ = x * (g : G) := by rw [h1]
    have hmem : Bs.normalizerMonoidHom g ∈ ggInduced (Subgroup.centralizer ({x} : Set G)) Bs :=
      mem_ggInduced_iff.mpr ⟨g, hgx, rfl⟩
    exact hb (mem_zpowers_mk_of_coe_mem hxBs
      (hcen G p B Bs x L D J ⟨hT, hBs, hstd⟩ hL _ hmem hψtv b))
  · refine hline G p B Bs x L D J ⟨hT, hBs, hstd⟩ hL (E.map Bs.subtype)
      (Subgroup.map_subtype_le E) ⟨⟨x, hxBs⟩, hxE, rfl⟩
      (by rw [Subgroup.card_map_of_injective Bs.subtype_injective, hEcard]) ?_
    refine CFSG.StandardType.le_normalizer_of_map_conj_le fun g hg => ?_
    rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
    have hge := hEinv (Bs.normalizerMonoidHom ⟨g, hg⟩) ⟨⟨g, hg⟩, rfl⟩ e he
    exact ⟨_, hge, rfl⟩

end NoTransvection

@[expose] def GGMarkingAll {K : Type*} [Group K] (Q : LargeEvenMarkProp K) : Prop :=
  ∀ P : LargeEvenMarkProp K, LargeEvenMarking K P →
    LargeEvenMarking K fun lab R _ I F θ => P lab R I F θ ∧ Q lab R I F θ

@[expose] def GGBstarNbrNormalInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      Bs ≤ Subgroup.normalizer (K : Set G)

@[expose] def GGNbrGraphInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
        GGMarkingAll (K := ↥K) fun _ _ _ I F θ => ∀ (b : G) (hb : b ∈ Bs),
          ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, ggLAut K θ ⟨b, hN hb⟩ = u * f

@[expose] def GGNbrFieldTransvectionInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
        GGMarkingAll (K := ↥K) fun _ _ _ I F θ =>
          (∀ (b : G) (hb : b ∈ Bs), ∃ u ∈ I, ∃ f ∈ Subgroup.closure F,
            ggLAut K θ ⟨b, hN hb⟩ = u * f) →
          (∃ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∉ I) →
            ∃ φ ∈ ggInduced ⊤ Bs, GGIsTransvection p φ

section Induces

variable {G : Type} [Group G] (K : Subgroup G) {R : Type} [Group R]
  (θ : K ⧸ Subgroup.center K ≃* R)

theorem largeEvenInduces_ggLAut_inv {b : G} (hb : b⁻¹ ∈ Subgroup.normalizer (K : Set G)) :
    LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) (ggLAut K θ ⟨b⁻¹, hb⟩) := by
  intro l l' hll'
  rw [ggLAut_apply]
  congr 2
  apply Subtype.ext
  rw [normalizerMonoidHom_coe, hll', inv_inv]

end Induces

theorem ggCor42Input_of (hK : GGKantorReductionInput) (hLID : GGBstarInnerDiagLInput)
    (hcen : GGLTransvectionCenterInput) (hline : GGLNoInvariantLineInput)
    (hnorm : GGBstarNbrNormalInput) (hgraph : GGNbrGraphInput)
    (hfield : GGNbrFieldTransvectionInput) : GGCor42Input := by
  intro G _ _ p B Bs x L D J hC hO
  have hL := hLID G p B Bs x L D J hC
  have hNT := ggNoTransvection_of hK hcen hline hC hO hL
  refine ⟨hL, fun y K hK' => ?_⟩
  have hN := hnorm G p B Bs x L D J hC y K hK'
  have h5 := (hC.1.2.2.2.2.2.2.2.2.2.1 y K (isNeighborOf_of_ggNbr hC.2.2 hK')).2
  have hM := hfield G p B Bs x L D J hC y K hK' hN _ (hgraph G p B Bs x L D J hC y K hK' hN _ h5)
  refine largeEvenMarking_mono ?_ hM
  rintro lab R _ I F θ ⟨⟨-, hall⟩, himp⟩
  refine ⟨hN, fun b hb => ⟨_, ?_, largeEvenInduces_ggLAut_inv K θ (hN (Bs.inv_mem hb))⟩⟩
  by_contra hnot
  obtain ⟨φ, hφ, htv⟩ := himp hall ⟨b⁻¹, Bs.inv_mem hb, hnot⟩
  exact hNT φ hφ htv

theorem ggNoTransvectionInput_of (hK : GGKantorReductionInput) (hcen : GGLTransvectionCenterInput)
    (hline : GGLNoInvariantLineInput) : GGNoTransvectionInput := by
  intro G _ _ p B Bs x L D J hC hO hD
  exact ggNoTransvection_of hK hcen hline hC hO hD.1

end CFSG.StandardType
