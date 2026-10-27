module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.Item47Kinds

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

variable {G : Type*} [Group G]

private theorem rh2_central_eq_one {H : Type*} [Group H] {L : Subgroup H}
    (hZ : Subgroup.center L = ⊥) {x : H} (hx : x ∈ L) (hc : ∀ g ∈ L, g * x = x * g) :
    x = 1 := by
  have hmem : (⟨x, hx⟩ : L) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g.1 g.2)
  rw [hZ, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

private theorem rh2_conj_injective {H : Type*} [Group H] {L : Subgroup H}
    (hZ : Subgroup.center L = ⊥) : Function.Injective (MulAut.conj : L →* MulAut L) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  refine Subtype.ext (rh2_central_eq_one hZ x.2 (fun g hg => ?_))
  have h := congrArg (fun τ : MulAut L => τ ⟨g, hg⟩) hx
  have h' : (x : H) * g * (x : H)⁻¹ = g := congrArg Subtype.val h
  exact (mul_inv_eq_iff_eq_mul.mp h').symm

private theorem rh2_isElemAbelian_range {H K : Type*} [Group H] [Group K] {E : Subgroup H}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (f : E →* K) :
    CFSG.Assembly.IsElemAbelian 3 f.range := by
  have hc : ∀ x ∈ f.range, ∀ y ∈ f.range, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hy
    rw [← map_mul, ← map_mul, hE.1.is_comm.comm a b]
  refine ⟨⟨⟨fun p q => Subtype.ext (hc p.1 p.2 q.1 q.2)⟩⟩, fun x hx => ?_⟩
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
  have ha3 : a ^ 3 = 1 := Subtype.ext (by simpa using hE.2 a a.2)
  rw [← map_pow, ha3, map_one]

theorem exists_inner_rep {L : Subgroup G} (hZ : Subgroup.center L = ⊥) (hcube : CubeInner L)
    {d : G} (hdN : d ∈ Subgroup.normalizer (L : Set G)) (hd3 : d ^ 3 = 1) :
    ∃ dL ∈ L, dL ^ 3 = 1 ∧ ∀ l ∈ L, d * l * d⁻¹ = dL * l * dL⁻¹ := by
  obtain ⟨τ, hτdef⟩ : ∃ τ : MulAut L,
      τ = L.normalizerMonoidHom (⟨d, hdN⟩ : Subgroup.normalizer (L : Set G)) := ⟨_, rfl⟩
  have hd3' : (⟨d, hdN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
    Subtype.ext (by simpa using hd3)
  have hτ3 : τ ^ 3 = 1 := by
    rw [hτdef, ← map_pow, hd3', map_one]
  have hin : τ ∈ (MulAut.conj : L →* MulAut L).range := hcube τ hτ3
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hin
  have hy3 : y ^ 3 = 1 := by
    refine (map_eq_one_iff (MulAut.conj : L →* MulAut L) (rh2_conj_injective hZ)).mp ?_
    rw [map_pow, hy, hτ3]
  refine ⟨(y : G), y.2, ?_, ?_⟩
  · simpa using congrArg Subtype.val hy3
  · intro l hl
    calc d * l * d⁻¹ = ((τ ⟨l, hl⟩ : L) : G) := by subst hτdef; rfl
      _ = ((MulAut.conj y ⟨l, hl⟩ : L) : G) := by rw [hy]
      _ = (y : G) * l * (y : G)⁻¹ := rfl

theorem card_le_nine_mul_of_inner [Finite G] {L E : Subgroup G} (hZ : Subgroup.center L = ⊥)
    (hcube : CubeInner L) (hEN : E ≤ Subgroup.normalizer (L : Set G))
    (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (h9 : ∀ F : Subgroup L, CFSG.Assembly.IsElemAbelian 3 F → Nat.card F ≤ 9) :
    Nat.card E ≤ 9 * Nat.card (E ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) := by
  have hE3 : ∀ a : E, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hE.2 a a.2)
  obtain ⟨act, hact⟩ : ∃ act : E →* MulAut L,
      ∀ (a : E) (x : L), ((act a x : L) : G) = (a : G) * (x : G) * (a : G)⁻¹ :=
    ⟨L.normalizerMonoidHom.comp (Subgroup.inclusion hEN), fun _ _ => rfl⟩
  have hact3 : ∀ a : E, act a ^ 3 = 1 := fun a => by
    rw [← map_pow, hE3 a, map_one]
  have hcinj := rh2_conj_injective hZ
  have hrange : ∀ a : E, act a ∈ (MulAut.conj : L →* MulAut L).range :=
    fun a => hcube (act a) (hact3 a)
  obtain ⟨phi, hphi⟩ : ∃ phi : E →* L, ∀ a : E, MulAut.conj (phi a) = act a :=
    ⟨(MonoidHom.ofInjective hcinj).symm.toMonoidHom.comp (act.codRestrict _ hrange),
      fun a => MonoidHom.apply_ofInjective_symm hcinj ⟨act a, hrange a⟩⟩
  have hact1 : ∀ a : E, act a = 1 ↔ (a : G) ∈ Subgroup.centralizer (L : Set G) := by
    intro a
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h g hg
      have h1 : ((act a ⟨g, hg⟩ : L) : G) = g := by simp [h]
      rw [hact a ⟨g, hg⟩] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
    · intro h
      refine MulEquiv.ext fun x => Subtype.ext ?_
      rw [hact a x, MulAut.one_apply, ← h x x.2, mul_inv_cancel_right]
  have hphi1 : ∀ a : E, phi a = 1 ↔ act a = 1 := fun a => by
    rw [← hphi a, map_eq_one_iff _ hcinj]
  have hphiC : ∀ a : E, phi a = 1 ↔ (a : G) ∈ Subgroup.centralizer (L : Set G) :=
    fun a => (hphi1 a).trans (hact1 a)
  have hidx : Nat.card phi.ker * Nat.card phi.range = Nat.card E := by
    have h := Subgroup.card_mul_index phi.ker
    rw [Subgroup.index_ker] at h
    exact h
  have hmapK : phi.ker.map E.subtype = E ⊓ Subgroup.centralizer (L : Set G) := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
      exact Subgroup.mem_inf.mpr ⟨a.2, (hphiC a).mp (MonoidHom.mem_ker.mp ha)⟩
    · intro hx
      obtain ⟨hxE, hxC⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_map.mpr
        ⟨⟨x, hxE⟩, MonoidHom.mem_ker.mpr ((hphiC ⟨x, hxE⟩).mpr hxC), rfl⟩
  have hKcard : Nat.card (E ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) =
      Nat.card phi.ker := by
    rw [← hmapK]
    exact Subgroup.card_map_of_injective E.subtype_injective
  have hPle : Nat.card phi.range ≤ 9 := h9 _ (rh2_isElemAbelian_range hE phi)
  rw [hKcard, ← hidx]
  exact (Nat.mul_le_mul le_rfl hPle).trans_eq (Nat.mul_comm _ _)

end CFSG.RankThree.PartTwo.Sec14.Ronan148R

end
