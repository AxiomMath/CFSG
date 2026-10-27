module

public import CFSG.RankThree.PartTwo.Sec4.Item47Kinds
public import CFSG.RankThree.PartTwo.Sec13.Item136PGL
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

private theorem split148_eq_one {G : Type} [Group G] {L : Subgroup G}
    (hZ : Subgroup.center L = ⊥) {x : G} (hx : x ∈ L) (hc : ∀ g ∈ L, g * x = x * g) :
    x = 1 := by
  have hmem : (⟨x, hx⟩ : L) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g.1 g.2)
  rw [hZ, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

private theorem split148_isElemAbelian_of_le {G : Type} [Group G] {A : Subgroup G}
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA3 : ∀ a ∈ A, a ^ 3 = 1) (H : Subgroup G)
    (hH : H ≤ A) : CFSG.Assembly.IsElemAbelian 3 H :=
  ⟨⟨⟨fun p q => Subtype.ext (hAc p.1 (hH p.2) q.1 (hH q.2))⟩⟩, fun x hx => hA3 x (hH hx)⟩

theorem inner_split {G : Type} [Group G] [Finite G] {L A : Subgroup G}
    (hZ : Subgroup.center L = ⊥) (hcube : CubeInner L)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hA : Late.IsE27 A)
    (hG3 : ∀ E : Subgroup G, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 27)
    (hL9 : ∀ E : Subgroup G, E ≤ L → CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 9)
    (hLE : ∃ E : Subgroup G, E ≤ L ∧ CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9) :
    Nat.card (A ⊓ L : Subgroup G) = 9 ∧
      Nat.card (A ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) = 3 ∧
      (A ⊓ L) ⊔ (A ⊓ Subgroup.centralizer (L : Set G)) = A := by
  obtain ⟨E, hEL, hE, hE9⟩ := hLE
  have hAel : CFSG.Assembly.IsElemAbelian 3 A := hA.1
  have hA27 : Nat.card A = 27 := hA.2
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    haveI := hAel.1
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) ⟨b, hb⟩)
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := fun a ha => hAel.2 a ha
  have hAc' : ∀ a b : A, a * b = b * a := fun a b => Subtype.ext (hAc a a.2 b b.2)
  have hpow3 : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hA3 a a.2)
  have hLC : ∀ x : G, x ∈ L → x ∈ Subgroup.centralizer (L : Set G) → x = 1 :=
    fun x hxL hxC =>
      split148_eq_one hZ hxL (fun g hg => (Subgroup.mem_centralizer_iff.mp hxC) g hg)
  have hinf_bot : ∀ H K : Subgroup G, H ≤ L → K ≤ Subgroup.centralizer (L : Set G) →
      H ⊓ K = ⊥ := by
    intro H K hHL hKC
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxH, hxK⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_bot]
    exact hLC x (hHL hxH) (hKC hxK)
  have hcomm : ∀ x : G, x ∈ L → ∀ y ∈ Subgroup.centralizer (L : Set G),
      x * y = y * x :=
    fun x hx y hy => (Subgroup.mem_centralizer_iff.mp hy) x hx
  obtain ⟨act, hact⟩ : ∃ act : A →* MulAut L,
      ∀ (a : A) (x : L), ((act a x : L) : G) = (a : G) * (x : G) * (a : G)⁻¹ :=
    ⟨L.normalizerMonoidHom.comp (Subgroup.inclusion hAN), fun _ _ => rfl⟩
  have hact3 : ∀ a : A, act a ^ 3 = 1 := fun a => by
    rw [← map_pow, hpow3 a, map_one]
  have hcinj : Function.Injective (MulAut.conj : L →* MulAut L) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    refine Subtype.ext (split148_eq_one hZ x.2 (fun g hg => ?_))
    have h := congrArg (fun τ : MulAut L => τ ⟨g, hg⟩) hx
    have h' : (x : G) * g * (x : G)⁻¹ = g := congrArg Subtype.val h
    exact (mul_inv_eq_iff_eq_mul.mp h').symm
  have hrange : ∀ a : A, act a ∈ (MulAut.conj : L →* MulAut L).range :=
    fun a => hcube (act a) (hact3 a)
  obtain ⟨phi, hphi⟩ : ∃ phi : A →* L, ∀ a : A, MulAut.conj (phi a) = act a :=
    ⟨(MonoidHom.ofInjective hcinj).symm.toMonoidHom.comp (act.codRestrict _ hrange),
      fun a => MonoidHom.apply_ofInjective_symm hcinj ⟨act a, hrange a⟩⟩
  obtain ⟨rho, hrho⟩ : ∃ rho : A →* G, ∀ a : A, rho a = ((phi a : L) : G) :=
    ⟨L.subtype.comp phi, fun _ => rfl⟩
  have hrhoL : ∀ a : A, rho a ∈ L := fun a => by
    rw [hrho a]
    exact (phi a).2
  have hrhoc : ∀ a b : A, rho a * rho b = rho b * rho a := fun a b => by
    rw [← map_mul, ← map_mul, hAc' a b]
  have hrho3 : ∀ a : A, rho a ^ 3 = 1 := fun a => by
    rw [← map_pow, hpow3 a, map_one]
  have hphic : ∀ a b : A, phi a * phi b = phi b * phi a := fun a b => by
    rw [← map_mul, ← map_mul, hAc' a b]
  have hkey : ∀ (a : A) (x : L), (a : G) * (x : G) * (a : G)⁻¹ =
      ((phi a : L) : G) * (x : G) * ((phi a : L) : G)⁻¹ := by
    intro a x
    rw [← hact a x, ← hphi a]
    exact congrArg Subtype.val (MulAut.conj_apply (phi a) x)
  have hact1 : ∀ a : A, act a = 1 ↔ (a : G) ∈ Subgroup.centralizer (L : Set G) := by
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
  have hrho1 : ∀ a : A, rho a = 1 ↔ act a = 1 := by
    intro a
    rw [← hphi a, map_eq_one_iff _ hcinj, hrho a]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hrhoA : ∀ a : A, rho a = 1 ↔ (a : G) ∈ Subgroup.centralizer (L : Set G) :=
    fun a => (hrho1 a).trans (hact1 a)
  have hidx : Nat.card rho.ker * Nat.card rho.range = 27 := by
    have h := Subgroup.card_mul_index rho.ker
    rw [Subgroup.index_ker, hA27] at h
    exact h
  have hmapK : rho.ker.map A.subtype = A ⊓ Subgroup.centralizer (L : Set G) := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
      exact Subgroup.mem_inf.mpr ⟨a.2, (hrhoA a).mp (MonoidHom.mem_ker.mp ha)⟩
    · intro hx
      obtain ⟨hxA, hxC⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_map.mpr
        ⟨⟨x, hxA⟩, MonoidHom.mem_ker.mpr ((hrhoA ⟨x, hxA⟩).mpr hxC), rfl⟩
  have hBcard : Nat.card (A ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) =
      Nat.card rho.ker := by
    rw [← hmapK]
    exact Subgroup.card_map_of_injective A.subtype_injective
  have hBP : Nat.card (A ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) *
      Nat.card rho.range = 27 := by
    rw [hBcard]
    exact hidx
  have hPL : rho.range ≤ L := by
    intro p hp
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hp
    exact hrhoL a
  have hPcomm : ∀ p ∈ rho.range, ∀ q ∈ rho.range, p * q = q * p := by
    intro p hp q hq
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hp
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hq
    exact hrhoc a b
  have hPel : CFSG.Assembly.IsElemAbelian 3 rho.range := by
    refine ⟨⟨⟨fun p q => Subtype.ext (hPcomm p.1 p.2 q.1 q.2)⟩⟩, fun x hx => ?_⟩
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
    exact hrho3 a
  have hPA : ∀ p ∈ rho.range, ∀ b ∈ A, p * b = b * p := by
    intro p hp b hb
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hp
    have hk : (b : G) * ((phi a : L) : G) * (b : G)⁻¹ =
        ((phi ⟨b, hb⟩ : L) : G) * ((phi a : L) : G) * ((phi ⟨b, hb⟩ : L) : G)⁻¹ :=
      hkey ⟨b, hb⟩ (phi a)
    have hc : ((phi ⟨b, hb⟩ : L) : G) * ((phi a : L) : G) =
        ((phi a : L) : G) * ((phi ⟨b, hb⟩ : L) : G) :=
      congrArg Subtype.val (hphic ⟨b, hb⟩ a)
    have h2 : ((phi a : L) : G) =
        ((phi ⟨b, hb⟩ : L) : G) * ((phi a : L) : G) * ((phi ⟨b, hb⟩ : L) : G)⁻¹ := by
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    have h3 : (b : G) * ((phi a : L) : G) * (b : G)⁻¹ = ((phi a : L) : G) :=
      hk.trans h2.symm
    rw [hrho a]
    exact (mul_inv_eq_iff_eq_mul.mp h3).symm
  have hAP : CFSG.Assembly.IsElemAbelian 3 (rho.range ⊔ A) :=
    CFSG.RankThree.PartTwo.Sec13.isElemAbelian_sup hPel hAel hPA
  have hPAeq : A = rho.range ⊔ A :=
    Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hA27]; exact hG3 _ hAP)
  have hPA_le : rho.range ≤ A := le_sup_left.trans hPAeq.symm.le
  have hBel : CFSG.Assembly.IsElemAbelian 3 (A ⊓ Subgroup.centralizer (L : Set G)) :=
    split148_isElemAbelian_of_le hAc hA3 (A ⊓ Subgroup.centralizer (L : Set G)) inf_le_left
  have hEBsup : CFSG.Assembly.IsElemAbelian 3 (E ⊔ (A ⊓ Subgroup.centralizer (L : Set G))) :=
    CFSG.RankThree.PartTwo.Sec13.isElemAbelian_sup hE hBel
      (fun x hx y hy => hcomm x (hEL hx) y (Subgroup.mem_inf.mp hy).2)
  have hEBcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E
    (A ⊓ Subgroup.centralizer (L : Set G))
    (fun x hx y hy => hcomm x (hEL hx) y (Subgroup.mem_inf.mp hy).2)).1
  rw [hinf_bot E (A ⊓ Subgroup.centralizer (L : Set G)) hEL inf_le_right, Subgroup.card_bot,
    mul_one, hE9] at hEBcard
  have hB_le : Nat.card (A ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) ≤ 3 := by
    have := hG3 _ hEBsup
    omega
  have hPle : Nat.card rho.range ≤ 9 := hL9 _ hPL hPel
  have hB_ge : 3 ≤ Nat.card (A ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) := by
    have h27 : 27 ≤ Nat.card (A ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) * 9 := by
      rw [← hBP]
      exact Nat.mul_le_mul le_rfl hPle
    omega
  have hB3 : Nat.card (A ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) = 3 :=
    le_antisymm hB_le hB_ge
  have hP9 : Nat.card rho.range = 9 := by
    rw [hB3] at hBP
    omega
  have hD_ge : 9 ≤ Nat.card (A ⊓ L : Subgroup G) := by
    have := Subgroup.card_le_of_le (le_inf hPA_le hPL)
    omega
  have hD_le : Nat.card (A ⊓ L : Subgroup G) ≤ 9 :=
    hL9 (A ⊓ L) inf_le_right (split148_isElemAbelian_of_le hAc hA3 (A ⊓ L) inf_le_left)
  have hD9 : Nat.card (A ⊓ L : Subgroup G) = 9 := le_antisymm hD_le hD_ge
  have hDB_card := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (A ⊓ L)
    (A ⊓ Subgroup.centralizer (L : Set G))
    (fun x hx y hy => hcomm x (Subgroup.mem_inf.mp hx).2 y (Subgroup.mem_inf.mp hy).2)).1
  rw [hinf_bot (A ⊓ L) (A ⊓ Subgroup.centralizer (L : Set G)) inf_le_right inf_le_right,
    Subgroup.card_bot, mul_one, hD9, hB3] at hDB_card
  have hsup_le : (A ⊓ L) ⊔ (A ⊓ Subgroup.centralizer (L : Set G)) ≤ A :=
    sup_le inf_le_left inf_le_left
  have hsup_eq : (A ⊓ L) ⊔ (A ⊓ Subgroup.centralizer (L : Set G)) = A :=
    Subgroup.eq_of_le_of_card_ge hsup_le (by rw [hA27]; omega)
  exact ⟨hD9, hB3, hsup_eq⟩

end CFSG.RankThree.PartTwo.Sec4.Ronan148S
