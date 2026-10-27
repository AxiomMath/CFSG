module

public import CFSG.Quasithin.Background.AutOnBasics
public import CFSG.Quasithin.H13.A6Realize
public import CFSG.Quasithin.Background.C124BlkQuot
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.H13.StatementsL6

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G]

theorem le_normalizer_blockU (L : Subgroup G) : L ≤ normalizer (blockU L : Set G) := by
  have hQ : ∀ g ∈ L, ∀ q ∈ blockQ L, g * q * g⁻¹ ∈ blockQ L := fun g hg q hq =>
    (Subgroup.mem_normalizer_iff.1
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hg) q).1 hq
  have key : ∀ g ∈ L, ∀ x ∈ blockU L, g * x * g⁻¹ ∈ blockU L := by
    intro g hg x hx
    unfold blockU at hx ⊢
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨q, hq, l, hl, rfl⟩ := hx
      have : g * ⁅q, l⁆ * g⁻¹ = ⁅g * q * g⁻¹, g * l * g⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      rw [this]
      exact Subgroup.commutator_mem_commutator (hQ g hg q hq) (L.mul_mem (L.mul_mem hg hl)
        (L.inv_mem hg))
    | one => simp
    | mul x y _ _ hx hy =>
      have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ hx
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key g hg h hh, fun hh => ?_⟩
  have := key g⁻¹ (L.inv_mem hg) _ hh
  simpa [mul_assoc] using this

theorem conjAct_val (V : Subgroup G) (g : ↥(normalizer (V : Set G))) (x : ↥V) :
    ((conjAct V g x : ↥V) : G) = g * x * (g : G)⁻¹ :=
  CFSG.Quasithin.AutOn.coe_conjAct_apply V g x

theorem permAct_allOnes_eq (σ : Equiv.Perm (Fin 6)) :
    G6.permAct 6 σ (G6.allOnes 6) = G6.allOnes 6 := rfl

theorem mem_pCoreOf_iff_gc (L : Subgroup G) (x : ↥L) :
    (x : G) ∈ pCoreOf 2 L ↔ x ∈ CFSG.pCore 2 ↥L := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rwa [← this]
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem isA6Block_of_isAltBlockType {L : Subgroup G} (h : IsAltBlockType L 6) :
    H13.IsA6Block L := by
  obtain ⟨hshort, α, hα, hker, β, hβs, hβk, hβe⟩ := h
  have hLN := le_normalizer_blockU L
  have hU : blockU L ≤ blockQ L ⊓ centralizer (blockQ L : Set G) := hshort.2.2.1.1
  have hcomm : IsMulCommutative ↥(blockU L) := ⟨⟨fun a b => Subtype.ext
    ((Subgroup.mem_centralizer_iff.1 (hU a.2).2 b (hU b.2).1).symm)⟩⟩
  refine ⟨hshort, ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)⟩, hcomm, ?_⟩
  let φ : ↥L →* ↥(autOn L (blockU L)) := A6.autOnHom hLN
  have hφs : Function.Surjective φ := A6.autOnHom_surjective hLN
  have hφv : ∀ (l : ↥L) (u : ↥(blockU L)),
      (((φ l : ↥(autOn L (blockU L))) : MulAut ↥(blockU L)) u : G) = l * u * (l : G)⁻¹ :=
    fun l u => conjAct_val _ _ _
  have hφk : α.ker ≤ φ.ker := by
    intro l hl
    rw [hker] at hl
    rw [MonoidHom.mem_ker]
    refine Subtype.ext (MulEquiv.ext fun u => Subtype.ext ?_)
    show (((φ l : ↥(autOn L (blockU L))) : MulAut ↥(blockU L)) u : G) = (u : G)
    rw [hφv]
    have hlQ : (l : G) ∈ blockQ L := (mem_pCoreOf_iff_gc L l).2 hl
    have h1 := Subgroup.mem_centralizer_iff.1 (hU u.2).2 l hlQ
    calc (l : G) * u * (l : G)⁻¹ = u * l * (l : G)⁻¹ := by rw [h1]
      _ = u := by group
  let e : (↥L ⧸ α.ker) ≃* ↥(alternatingGroup (Fin 6)) :=
    QuotientGroup.quotientKerEquivOfSurjective α hα
  let π : ↥(alternatingGroup (Fin 6)) →* ↥(autOn L (blockU L)) :=
    (QuotientGroup.lift α.ker φ hφk).comp e.symm.toMonoidHom
  have hπ : ∀ l : ↥L, π (α l) = φ l := fun l => by
    have h1 : e (QuotientGroup.mk l) = α l := rfl
    simp only [π, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← h1, MulEquiv.symm_apply_apply]
    rfl
  have hπs : Function.Surjective π := fun y => by
    obtain ⟨l, rfl⟩ := hφs y
    exact ⟨α l, hπ l⟩
  have hmain : ∀ (γ : ↥(alternatingGroup (Fin 6))) (u : ↥(blockU L)) (m : ↥(G6.coreMod 6)),
      β u = C124.altHeartHom 6 m →
      β (((π γ : ↥(autOn L (blockU L))) : MulAut ↥(blockU L)) u) = C124.altHeartHom 6
        ⟨G6.permAct 6 (γ : Equiv.Perm (Fin 6)) m, G6.permAct_mem_coreMod _ m.2⟩ := by
    intro γ u m hum
    obtain ⟨l, rfl⟩ := hα γ
    rw [hπ]
    have hv := hφv l u
    have hx : (QuotientAddGroup.mk (Multiplicative.toAdd (C124.coreEvenEquiv 6 m)) :
        AltHeart 6) = Multiplicative.toAdd (β u) := by
      rw [hum, C124.altHeartHom_apply]
    have hβe' := hβe l u (((φ l : ↥(autOn L (blockU L))) : MulAut ↥(blockU L)) u) hv _ hx
    apply Multiplicative.toAdd.injective
    rw [C124.altHeartHom_apply, ← hβe']
    rfl
  refine ⟨π, hπs, le_top, inf_le_right, fun _ _ _ => Subgroup.mem_top _, ?_, ?_, ?_, ?_⟩
  · intro h z hz
    obtain ⟨l, rfl⟩ := hφs h
    have hzc : (z : G) ∈ centralizer (L : Set G) :=
      (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hz)).2
    have h1 := Subgroup.mem_centralizer_iff.1 hzc l l.2
    have h2 : (φ l : MulAut ↥(blockU L)) z = z := Subtype.ext (by
      rw [hφv]
      calc (l : G) * z * (l : G)⁻¹ = z * l * (l : G)⁻¹ := by rw [h1]
        _ = z := by group)
    rw [h2]
    exact hz
  · intro γ m hm
    exact G6.permAct_mem_coreMod (Subtype.val γ) hm
  · intro γ m hm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hm.1
    refine ⟨?_, G6.permAct_mem_coreMod (Subtype.val γ) hm.2⟩
    rw [← hk]
    show G6.permAct 6 (Subtype.val γ) (G6.allOnes 6 ^ k) ∈ _
    rw [map_zpow, permAct_allOnes_eq]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
  · refine ⟨(C124.altQuotEquiv 6 (by norm_num)).symm.toMonoidHom.comp
      (β.comp Subgroup.topEquiv.toMonoidHom), ?_, ?_, ?_⟩
    · exact (C124.altQuotEquiv 6 (by norm_num)).symm.surjective.comp
        (hβs.comp Subgroup.topEquiv.surjective)
    · intro u
      show (C124.altQuotEquiv 6 (by norm_num)).symm (β (Subgroup.topEquiv u)) = 1 ↔ _
      rw [MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, hβk]
      rfl
    · intro γ u m hu hm hum
      have h1 : β (Subgroup.topEquiv u) = C124.altHeartHom 6 (show ↥(G6.coreMod 6) from m) :=
        (MulEquiv.symm_apply_eq (C124.altQuotEquiv 6 (by norm_num))).1 hum
      show (C124.altQuotEquiv 6 (by norm_num)).symm (β (Subgroup.topEquiv
        ⟨((π γ : ↥(autOn L (blockU L))) : MulAut ↥(blockU L)) (u : ↥(blockU L)), hu⟩)) = _
      apply (MulEquiv.symm_apply_eq _).2
      exact hmain γ u m h1

theorem isHatA6Block_of {L : Subgroup G} (h : CFSG.Quasithin.IsHatA6Block L) :
    H13.IsHatA6Block L :=
  ⟨h.1, ⟨h.2.1.1.1, h.2.1.2.1, h.2.1.2.2⟩, h.2.2.1, h.2.2.2⟩

end CFSG.Quasithin.H13.U3.GC137
