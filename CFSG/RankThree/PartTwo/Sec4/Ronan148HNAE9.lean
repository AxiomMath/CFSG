module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148HNAOuter

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.RankThree.PartTwo.KFacts (IsInnerAut isInnerAut_congr mul_mulAutConj_mul_inv)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (NoThreeCover)
open scoped Pointwise

section Split

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_mem_of_commute {L : Subgroup G} (hZ : Subgroup.center L = ⊥) {x : G}
    (hx : x ∈ L) (hc : ∀ g ∈ L, g * x = x * g) : x = 1 := by
  have hmem : (⟨x, hx⟩ : L) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g.1 g.2)
  rw [hZ, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

theorem inner_split_of_inner {L A : Subgroup G} (hZ : Subgroup.center L = ⊥)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hA : Late.IsE27 A)
    (hin : ∀ a : A, IsInnerAut (L.normalizerMonoidHom (Subgroup.inclusion hAN a)))
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
  have hsubEl : ∀ H : Subgroup G, H ≤ A → CFSG.Assembly.IsElemAbelian 3 H := fun H hH =>
    ⟨⟨⟨fun p q => Subtype.ext (hAc p.1 (hH p.2) q.1 (hH q.2))⟩⟩, fun x hx => hA3 x (hH hx)⟩
  have hLC : ∀ x : G, x ∈ L → x ∈ Subgroup.centralizer (L : Set G) → x = 1 :=
    fun x hxL hxC =>
      eq_one_of_mem_of_commute hZ hxL (fun g hg => (Subgroup.mem_centralizer_iff.mp hxC) g hg)
  have hinf_bot : ∀ H K : Subgroup G, H ≤ L → K ≤ Subgroup.centralizer (L : Set G) →
      H ⊓ K = ⊥ := by
    intro H K hHL hKC
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxH, hxK⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_bot]
    exact hLC x (hHL hxH) (hKC hxK)
  have hcomm : ∀ x : G, x ∈ L → ∀ y ∈ Subgroup.centralizer (L : Set G), x * y = y * x :=
    fun x hx y hy => (Subgroup.mem_centralizer_iff.mp hy) x hx
  obtain ⟨act, hact, hactdef⟩ : ∃ act : A →* MulAut L,
      (∀ (a : A) (x : L), ((act a x : L) : G) = (a : G) * (x : G) * (a : G)⁻¹) ∧
        act = L.normalizerMonoidHom.comp (Subgroup.inclusion hAN) :=
    ⟨L.normalizerMonoidHom.comp (Subgroup.inclusion hAN), fun _ _ => rfl, rfl⟩
  have hcinj := conj_injective_of_center_eq_bot hZ
  have hrange : ∀ a : A, act a ∈ (MulAut.conj : L →* MulAut L).range := by
    intro a
    rw [hactdef]
    exact hin a
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
    hsubEl (A ⊓ Subgroup.centralizer (L : Set G)) inf_le_left
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
    hL9 (A ⊓ L) inf_le_right (hsubEl (A ⊓ L) inf_le_left)
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

end Split

section Row

variable {G : Type} [Group G] [Finite G]

theorem mem_of_isInnerAut {L A : Subgroup G} (hZ : Subgroup.center L = ⊥)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 3)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hA : CFSG.Assembly.IsElemAbelian 3 A)
    {a₀ : A} (ha₀ : ¬ IsInnerAut (L.normalizerMonoidHom (Subgroup.inclusion hAN a₀)))
    {E₀ : Subgroup L} (hE₀ : CFSG.Assembly.IsElemAbelian 3 E₀) (hE₀9 : Nat.card E₀ = 9)
    (hE₀fix : ∀ e ∈ E₀, L.normalizerMonoidHom (Subgroup.inclusion hAN a₀) e = e)
    (x : A) (hx : IsInnerAut (L.normalizerMonoidHom (Subgroup.inclusion hAN x))) :
    (x : G) ∈ L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set act : A →* MulAut L := L.normalizerMonoidHom.comp (Subgroup.inclusion hAN) with hactdef
  have hact : ∀ (a : A) (l : L), ((act a l : L) : G) = (a : G) * (l : G) * (a : G)⁻¹ :=
    fun _ _ => rfl
  have hAc : ∀ a b : A, a * b = b * a := fun a b => by
    haveI := hA.1
    exact mul_comm' a b
  have hpow3 : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hA.2 a a.2)
  have hcinj := conj_injective_of_center_eq_bot hZ
  obtain ⟨y, hy⟩ := hx
  change MulAut.conj y = act x at hy
  have hy3 : y ^ 3 = 1 := by
    refine (map_eq_one_iff _ hcinj).mp ?_
    rw [map_pow, hy, ← map_pow, hpow3 x, map_one]
  have hrep : ∀ l ∈ L, (x : G) * l * (x : G)⁻¹ = (y : G) * l * (y : G)⁻¹ := by
    intro l hl
    have h1 : ((MulAut.conj y ⟨l, hl⟩ : L) : G) = ((act x ⟨l, hl⟩ : L) : G) := by rw [hy]
    rw [hact] at h1
    exact h1.symm
  have hwC : (y : G)⁻¹ * x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := hrep l hl
    calc l * ((y : G)⁻¹ * x) = (y : G)⁻¹ * ((y : G) * l * (y : G)⁻¹) * x := by group
      _ = (y : G)⁻¹ * ((x : G) * l * (x : G)⁻¹) * x := by rw [h1]
      _ = (y : G)⁻¹ * x * l := by group
  have hxy : (x : G) * y = y * x := by
    have h1 := hrep y y.2
    calc (x : G) * y = x * y * (x : G)⁻¹ * x := by group
      _ = y * y * (y : G)⁻¹ * x := by rw [h1]
      _ = y * x := by group
  have hy3' : (y : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hy3
  have hx3 : (x : G) ^ 3 = 1 := by simpa using congrArg Subtype.val (hpow3 x)
  have hw3 : ((y : G)⁻¹ * x) ^ 3 = 1 := by
    have hc : Commute (y : G)⁻¹ x := Commute.inv_left (show Commute (y : G) x from hxy.symm)
    rw [hc.mul_pow, inv_pow, hy3', hx3, inv_one, one_mul]
  have hα := act a₀
  have hya : act a₀ y = y := by
    apply hcinj
    rw [← mul_mulAutConj_mul_inv, hy, ← map_inv, ← map_mul, ← map_mul, hAc a₀ x, mul_assoc,
      mul_inv_cancel, mul_one]
  have hay : (a₀ : G) * y = y * a₀ := by
    have h1 : (a₀ : G) * y * (a₀ : G)⁻¹ = y := by
      rw [← hact]
      exact congrArg Subtype.val hya
    calc (a₀ : G) * y = a₀ * y * (a₀ : G)⁻¹ * a₀ := by group
      _ = y * a₀ := by rw [h1]
  have hax : (a₀ : G) * x = x * a₀ := congrArg Subtype.val (hAc a₀ x)
  set w : G := (y : G)⁻¹ * x with hw
  have haw : (a₀ : G) * w = w * a₀ := by
    rw [hw]
    calc (a₀ : G) * ((y : G)⁻¹ * x) = (a₀ * (y : G)⁻¹) * x := by group
      _ = ((y : G)⁻¹ * a₀) * x := by
        rw [(Commute.inv_right (show Commute (a₀ : G) y from hay)).eq]
      _ = (y : G)⁻¹ * (a₀ * x) := by group
      _ = (y : G)⁻¹ * (x * a₀) := by rw [hax]
      _ = (y : G)⁻¹ * x * a₀ := by group
  by_contra hxL
  have hw1 : w ≠ 1 := by
    intro h
    apply hxL
    have : (x : G) = y := by
      calc (x : G) = y * w := by rw [hw]; group
        _ = y := by rw [h, mul_one]
    rw [this]
    exact y.2
  set E₁ : Subgroup G := E₀.map L.subtype with hE₁
  have hE₁L : E₁ ≤ L := Subgroup.map_subtype_le _
  have hE₁e : CFSG.Assembly.IsElemAbelian 3 E₁ := isElemAbelian_map _ hE₀
  have hE₁9 : Nat.card E₁ = 9 := by
    rw [hE₁, Subgroup.card_map_of_injective L.subtype_injective, hE₀9]
  have hE₁a : ∀ e ∈ E₁, (a₀ : G) * e = e * a₀ := by
    rintro _ ⟨e, he, rfl⟩
    have h1 : (a₀ : G) * e * (a₀ : G)⁻¹ = e := by
      rw [← hact]
      exact congrArg Subtype.val (hE₀fix e he)
    calc (a₀ : G) * e = a₀ * e * (a₀ : G)⁻¹ * a₀ := by group
      _ = e * a₀ := by rw [h1]
  have hLC : ∀ z ∈ L, z ∈ Subgroup.centralizer (L : Set G) → z = 1 := fun z hz hzC =>
    eq_one_of_mem_of_commute hZ hz (fun g hg => Subgroup.mem_centralizer_iff.mp hzC g hg)
  have hW : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers w) :=
    CFSG.RankThree.PartTwo.Sec13.isElemAbelian_zpowers hw3
  have hWc : Nat.card (Subgroup.zpowers w) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hw3 hw1]
  have hWC : Subgroup.zpowers w ≤ Subgroup.centralizer (L : Set G) := Subgroup.zpowers_le.mpr hwC
  have hcEW : ∀ e ∈ E₁, ∀ v ∈ Subgroup.zpowers w, e * v = v * e := fun e he v hv =>
    Subgroup.mem_centralizer_iff.mp (hWC hv) e (hE₁L he)
  have hinfEW : E₁ ⊓ Subgroup.zpowers w = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzE, hzW⟩
    exact Subgroup.mem_bot.mpr (hLC z (hE₁L hzE) (hWC hzW))
  set F := E₁ ⊔ Subgroup.zpowers w with hF
  have hFe : CFSG.Assembly.IsElemAbelian 3 F :=
    CFSG.RankThree.PartTwo.Sec13.isElemAbelian_sup hE₁e hW hcEW
  have hFc : Nat.card F = 27 := by
    rw [hF, Ronan148R.card_sup_of_commute_of_inf hcEW hinfEW, hE₁9, hWc]
  have hFa : ∀ f ∈ F, f * a₀ = a₀ * f := by
    intro f hf
    have hcF : F ≤ Subgroup.centralizer ({(a₀ : G)} : Set G) := by
      refine sup_le (fun e he => ?_) (Subgroup.zpowers_le.mpr ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hE₁a e he).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr haw.symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcF hf)
  have ha₀F : (a₀ : G) ∉ F := by
    intro haF
    have hnorm : E₁ ≤ Subgroup.normalizer ((Subgroup.zpowers w : Subgroup G) : Set G) := by
      intro e he
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
      intro v hv
      exact (hcEW e he v hv).symm
    have hset : ((E₁ ⊔ Subgroup.zpowers w : Subgroup G) : Set G) =
        (E₁ : Set G) * (Subgroup.zpowers w : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right E₁ (Subgroup.zpowers w) hnorm
    have haF' : (a₀ : G) ∈ ((E₁ ⊔ Subgroup.zpowers w : Subgroup G) : Set G) := haF
    rw [hset] at haF'
    obtain ⟨e, he, v, hv, hev⟩ := haF'
    apply ha₀
    refine ⟨⟨e, hE₁L he⟩, ?_⟩
    ext l
    change (e : G) * l * e⁻¹ = (a₀ : G) * l * (a₀ : G)⁻¹
    have hvl : v * l = l * v := (Subgroup.mem_centralizer_iff.mp (hWC hv) l l.2).symm
    rw [← hev]
    calc (e : G) * l * e⁻¹ = e * (v * l * v⁻¹) * e⁻¹ := by rw [hvl, mul_inv_cancel_right]
      _ = e * v * l * (e * v)⁻¹ := by group
  have hA0 : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers (a₀ : G)) :=
    CFSG.RankThree.PartTwo.Sec13.isElemAbelian_zpowers (by simpa using congrArg Subtype.val (hpow3 a₀))
  have ha₀1 : (a₀ : G) ≠ 1 := fun h => ha₀F (h ▸ F.one_mem)
  have hA0c : Nat.card (Subgroup.zpowers (a₀ : G)) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (by simpa using congrArg Subtype.val (hpow3 a₀)) ha₀1]
  have hcFA : ∀ f ∈ F, ∀ v ∈ Subgroup.zpowers (a₀ : G), f * v = v * f := by
    intro f hf v hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact (Commute.zpow_right (show Commute f a₀ from hFa f hf) k).eq
  have hinfFA : F ⊓ Subgroup.zpowers (a₀ : G) = ⊥ := by
    have hd : Nat.card (F ⊓ Subgroup.zpowers (a₀ : G) : Subgroup G) ∣ 3 :=
      hA0c ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : F ⊓ Subgroup.zpowers (a₀ : G) = Subgroup.zpowers (a₀ : G) :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hA0c])
      have hmem : (a₀ : G) ∈ F ⊓ Subgroup.zpowers (a₀ : G) := by
        rw [heq]
        exact Subgroup.mem_zpowers _
      exact ha₀F (Subgroup.mem_inf.mp hmem).1
  have hB := CFSG.RankThree.PartTwo.Sec13.isElemAbelian_sup hFe hA0 hcFA
  have hBc := Ronan148R.card_sup_of_commute_of_inf hcFA hinfFA
  rw [hFc, hA0c] at hBc
  have hle := card_le_of_pRank_le hrk hB
  rw [hBc] at hle
  norm_num at hle

theorem row425_of_e9Move_outer {S : Type} [Group S] (h3 : NoThreeCover S)
    (hmove : E9Move S)
    (h9 : ∀ E : Subgroup S, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 9)
    (hE9 : ∃ E : Subgroup S, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9)
    (hout : ∀ α β : MulAut S, α ^ 3 = 1 → β ^ 3 = 1 → ¬ IsInnerAut α →
      ∃ k : ℕ, IsInnerAut (α ^ k * β))
    (hfix : ∀ α : MulAut S, α ^ 3 = 1 → ¬ IsInnerAut α →
      (∃ E : Subgroup (autFix α), CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9) ∧
        E9Move (autFix α)) :
    Row425 S := by
  intro G _ _ _ A hA hrk hθ L hL ⟨eL⟩ c hLc K _ K' hK' _ hAZ hN
  exfalso
  have hcmem : c ∈ A ⊓ (K' ⊓ Subgroup.centralizer (K' : Set G)) :=
    hAZ ▸ Subgroup.mem_zpowers c
  have hcA : c ∈ A := hcmem.1
  have hK'L : K' ≤ L := (hK' ▸ Subgroup.map_subtype_le K).trans inf_le_left
  have hcL : c ∈ L := hK'L hcmem.2.1
  have hc1 : c ≠ 1 := by
    rintro rfl
    exact hLc fun x _ => Subgroup.mem_centralizer_singleton_iff.mpr (by simp)
  have hZ : Subgroup.center L = ⊥ := Ronan148L.center_eq_bot_of_noThreeCover h3 hθ hL eL
  let φ : L ≃* S := (RonanK429.quotCenterEquivOfEqBot hZ).trans eL
  have hAc : ∀ a ∈ A, a * c = c * a := fun a ha =>
    congrArg Subtype.val (hA.1.1.is_comm.comm (⟨a, ha⟩ : A) ⟨c, hcA⟩)
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rcases CFSG.LocalCores.distinct_components_commute
        (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj a) hL) hL with h | h
    · exact h
    · exfalso
      have hcLa : c ∈ L.map (MulAut.conj a).toMonoidHom := by
        refine ⟨c, hcL, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [hAc a ha, mul_inv_cancel_right]
      have hcC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hcLa
      exact hLc fun x hx =>
        Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hcC x hx)
  have hmoveL : E9Move L := hmove.of_mulEquiv φ
  have h9L : ∀ E : Subgroup L, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 9 := by
    intro E hE
    have := h9 (E.map φ.toMonoidHom) (isElemAbelian_map _ hE)
    rwa [Subgroup.card_map_of_injective φ.injective] at this
  have hE9L : ∃ E : Subgroup L, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
    obtain ⟨E, hE, hE9⟩ := hE9
    exact ⟨E.map φ.symm.toMonoidHom, isElemAbelian_map _ hE, by
      rw [Subgroup.card_map_of_injective φ.symm.injective, hE9]⟩
  have houtL : ∀ α β : MulAut L, α ^ 3 = 1 → β ^ 3 = 1 → ¬ IsInnerAut α →
      ∃ k : ℕ, IsInnerAut (α ^ k * β) := by
    intro α β hα hβ hαo
    obtain ⟨k, hk⟩ := hout (MulAut.congr φ α) (MulAut.congr φ β)
      (by rw [← map_pow, hα, map_one]) (by rw [← map_pow, hβ, map_one])
      (fun h => hαo ((isInnerAut_congr φ α).mp h))
    refine ⟨k, (isInnerAut_congr φ _).mp ?_⟩
    rwa [map_mul, map_pow]
  have hfixL : ∀ α : MulAut L, α ^ 3 = 1 → ¬ IsInnerAut α →
      (∃ E : Subgroup (autFix α), CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9) ∧
        E9Move (autFix α) := by
    intro α hα hαo
    obtain ⟨⟨E, hE, hE9'⟩, hmv⟩ := hfix (MulAut.congr φ α) (by rw [← map_pow, hα, map_one])
      (fun h => hαo ((isInnerAut_congr φ α).mp h))
    let eF : autFix (MulAut.congr φ α) ≃* autFix α := autFixCongrEquiv φ α
    exact ⟨⟨E.map eF.toMonoidHom, isElemAbelian_map _ hE, by
      rw [Subgroup.card_map_of_injective eF.injective, hE9']⟩, hmv.of_mulEquiv eF.symm⟩
  set act : A →* MulAut L := L.normalizerMonoidHom.comp (Subgroup.inclusion hAN) with hactdef
  have hact : ∀ (a : A) (x : L), ((act a x : L) : G) = (a : G) * (x : G) * (a : G)⁻¹ :=
    fun _ _ => rfl
  have hpow3 : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hA.1.2 a a.2)
  have hcL' : (⟨c, hcL⟩ : L) ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  by_cases hall : ∀ a : A, IsInnerAut (act a)
  ·
    have hG3 : ∀ E : Subgroup G, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 27 :=
      fun E hE => card_le_of_pRank_le hrk.le hE
    have hL9 : ∀ E : Subgroup G, E ≤ L → CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 9 := by
      intro E hEL hE
      have := h9L (E.subgroupOf L) (isElemAbelian_comap L.subtype L.subtype_injective hE)
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv] at this
    have hLE : ∃ E : Subgroup G, E ≤ L ∧ CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
      obtain ⟨E, hE, hE9'⟩ := hE9L
      exact ⟨E.map L.subtype, Subgroup.map_subtype_le E, isElemAbelian_map _ hE, by
        rw [Subgroup.card_map_of_injective L.subtype_injective, hE9']⟩
    obtain ⟨hAL9, -, hsplit⟩ := inner_split_of_inner hZ hAN hA hall hG3 hL9 hLE
    set E : Subgroup L := (A ⊓ L).subgroupOf L with hE
    have hEab : CFSG.Assembly.IsElemAbelian 3 E :=
      isElemAbelian_comap L.subtype L.subtype_injective (isElemAbelian_mono inf_le_left hA.1)
    have hEcard : Nat.card E = 9 := by
      rw [hE, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ L ≤ L)).toEquiv,
        hAL9]
    have hsE : (⟨c, hcL⟩ : L) ∈ E := ⟨hcA, hcL⟩
    obtain ⟨n, hn, hns⟩ := hmoveL E hEab hEcard _ hsE hcL'
    have hnA : (n : G) ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) :=
      mem_normalizer_of_subgroupOf inf_le_right hn
    have hnAA := mem_normalizer_of_split hsplit n.2 hnA
    apply hns
    rw [← zpowers_subgroupOf hcL]
    exact mem_normalizer_subgroupOf (Subgroup.zpowers_le.mpr hcL) (hN hnAA)
  ·
    push Not at hall
    obtain ⟨a₀, ha₀⟩ := hall
    set α := act a₀ with hαdef
    have hα3 : α ^ 3 = 1 := by rw [hαdef, ← map_pow, hpow3 a₀, map_one]
    obtain ⟨⟨E₀, hE₀, hE₀9⟩, hmvα⟩ := hfixL α hα3 ha₀
    set E₀' : Subgroup L := E₀.map (autFix α).subtype with hE₀'
    have hE₀'e : CFSG.Assembly.IsElemAbelian 3 E₀' := isElemAbelian_map _ hE₀
    have hE₀'9 : Nat.card E₀' = 9 := by
      rw [hE₀', Subgroup.card_map_of_injective (autFix α).subtype_injective, hE₀9]
    have hE₀'fix : ∀ e ∈ E₀', α e = e := by
      rintro _ ⟨e, -, rfl⟩
      exact e.2
    have hinL : ∀ x : A, IsInnerAut (act x) → (x : G) ∈ L := fun x hx =>
      mem_of_isInnerAut hZ hrk.le hAN hA.1 ha₀ hE₀'e hE₀'9 hE₀'fix x hx
    set H : Subgroup G := A ⊓ L with hH
    have hHA : H ≤ A := inf_le_left
    have hHL : H ≤ L := inf_le_right
    have hA0 : Subgroup.zpowers (a₀ : G) ≤ A := Subgroup.zpowers_le.mpr a₀.2
    have hAeq : H ⊔ Subgroup.zpowers (a₀ : G) = A := by
      refine le_antisymm (sup_le hHA hA0) fun x hx => ?_
      obtain ⟨k, hk⟩ := houtL α (act ⟨x, hx⟩) hα3 (by rw [← map_pow, hpow3, map_one]) ha₀
      have hk' : IsInnerAut (act (a₀ ^ k * ⟨x, hx⟩)) := by rwa [map_mul, map_pow]
      have hmem := hinL _ hk'
      have hxe : x = (a₀ : G)⁻¹ ^ k * (((a₀ ^ k * ⟨x, hx⟩ : A)) : G) := by
        simp only [Subgroup.coe_mul, SubgroupClass.coe_pow, inv_pow]
        group
      rw [hxe]
      refine mul_mem (Subgroup.mem_sup_right (Subgroup.pow_mem _
        (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)) k)) (Subgroup.mem_sup_left ⟨?_, hmem⟩)
      exact (a₀ ^ k * ⟨x, hx⟩ : A).2
    have hHcomm : ∀ h ∈ H, ∀ v ∈ Subgroup.zpowers (a₀ : G), h * v = v * h := by
      intro h hh v hv
      exact congrArg Subtype.val (hA.1.1.is_comm.comm (⟨h, hHA hh⟩ : A) ⟨v, hA0 hv⟩)
    have hHel : CFSG.Assembly.IsElemAbelian 3 H := isElemAbelian_mono hHA hA.1
    have hH9 : Nat.card H = 9 := by
      have hle : Nat.card H ≤ 9 := by
        have := h9L (H.subgroupOf L) (isElemAbelian_comap L.subtype L.subtype_injective hHel)
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv] at this
      have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute H
        (Subgroup.zpowers (a₀ : G)) hHcomm).1
      rw [hAeq, hA.2] at hcard
      have h3' : Nat.card (Subgroup.zpowers (a₀ : G)) ≤ 3 := by
        rw [Nat.card_zpowers]
        exact orderOf_le_of_pow_eq_one (by norm_num)
          (by simpa using congrArg Subtype.val (hpow3 a₀))
      have hpos : 0 < Nat.card (H ⊓ Subgroup.zpowers (a₀ : G) : Subgroup G) := Nat.card_pos
      have : 27 ≤ Nat.card H * 3 := by
        calc 27 ≤ 27 * Nat.card (H ⊓ Subgroup.zpowers (a₀ : G) : Subgroup G) :=
              Nat.le_mul_of_pos_right _ hpos
          _ = Nat.card H * Nat.card (Subgroup.zpowers (a₀ : G)) := hcard
          _ ≤ Nat.card H * 3 := Nat.mul_le_mul le_rfl h3'
      omega
    set M : Subgroup G := (autFix α).map L.subtype with hM
    have hHM : H ≤ M := by
      intro h hh
      refine ⟨⟨h, hHL hh⟩, ?_, rfl⟩
      change α ⟨h, hHL hh⟩ = ⟨h, hHL hh⟩
      apply Subtype.ext
      rw [hact]
      have hc' : (a₀ : G) * h = h * a₀ := (hHcomm h hh a₀ (Subgroup.mem_zpowers _)).symm
      rw [hc', mul_inv_cancel_right]
    let eM : autFix α ≃* M := (autFix α).equivMapOfInjective L.subtype L.subtype_injective
    have hmvM : E9Move M := hmvα.of_mulEquiv eM.symm
    have hcM : c ∈ M := hHM ⟨hcA, hcL⟩
    have hHMe : CFSG.Assembly.IsElemAbelian 3 (H.subgroupOf M) :=
      isElemAbelian_comap M.subtype M.subtype_injective hHel
    have hHM9 : Nat.card (H.subgroupOf M) = 9 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHM).toEquiv, hH9]
    have hcM1 : (⟨c, hcM⟩ : M) ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
    obtain ⟨n, hn, hns⟩ := hmvM (H.subgroupOf M) hHMe hHM9 ⟨c, hcM⟩ ⟨hcA, hcL⟩ hcM1
    have hnH : (n : G) ∈ Subgroup.normalizer (H : Set G) := mem_normalizer_of_subgroupOf hHM hn
    have hna : (n : G) * a₀ = a₀ * n := by
      obtain ⟨m, hm, hmn⟩ := n.2
      have hm' : α m = m := hm
      have h1 : (a₀ : G) * m * (a₀ : G)⁻¹ = m := by
        rw [← hact]
        exact congrArg Subtype.val hm'
      rw [← hmn]
      change (m : G) * a₀ = a₀ * m
      calc (m : G) * a₀ = a₀ * m * (a₀ : G)⁻¹ * a₀ := by rw [h1]
        _ = a₀ * m := by group
    have hnZ : (n : G) ∈ Subgroup.normalizer ((Subgroup.zpowers (a₀ : G) : Subgroup G) : Set G) := by
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
      intro v hv
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (SetLike.mem_coe.mp hv)
      exact (Commute.zpow_left (show Commute (a₀ : G) n from hna.symm) k).eq
    have hnA : (n : G) ∈ Subgroup.normalizer (A : Set G) := by
      rw [← hAeq]
      exact mem_normalizer_sup hnH hnZ
    apply hns
    rw [← zpowers_subgroupOf hcM]
    exact mem_normalizer_subgroupOf (Subgroup.zpowers_le.mpr hcM) (hN hnA)

theorem row425_of_e9Move_outer_of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (h3 : NoThreeCover S) (hmove : E9Move T)
    (h9 : ∀ E : Subgroup T, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 9)
    (hE9 : ∃ E : Subgroup T, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9)
    (hout : ∀ α β : MulAut T, α ^ 3 = 1 → β ^ 3 = 1 → ¬ IsInnerAut α →
      ∃ k : ℕ, IsInnerAut (α ^ k * β))
    (hfix : ∀ α : MulAut T, α ^ 3 = 1 → ¬ IsInnerAut α →
      (∃ E : Subgroup (autFix α), CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9) ∧
        E9Move (autFix α)) :
    Row425 S := by
  refine row425_of_e9Move_outer h3 (hmove.of_mulEquiv e) (fun E hE => ?_) ?_ ?_ ?_
  · have := h9 (E.map e.toMonoidHom) (isElemAbelian_map _ hE)
    rwa [Subgroup.card_map_of_injective e.injective] at this
  · obtain ⟨E, hE, hE9'⟩ := hE9
    exact ⟨E.map e.symm.toMonoidHom, isElemAbelian_map _ hE, by
      rw [Subgroup.card_map_of_injective e.symm.injective, hE9']⟩
  · intro α β hα hβ hαo
    obtain ⟨k, hk⟩ := hout (MulAut.congr e α) (MulAut.congr e β)
      (by rw [← map_pow, hα, map_one]) (by rw [← map_pow, hβ, map_one])
      (fun h => hαo ((isInnerAut_congr e α).mp h))
    refine ⟨k, (isInnerAut_congr e _).mp ?_⟩
    rwa [map_mul, map_pow]
  · intro α hα hαo
    obtain ⟨⟨E, hE, hE9'⟩, hmv⟩ := hfix (MulAut.congr e α) (by rw [← map_pow, hα, map_one])
      (fun h => hαo ((isInnerAut_congr e α).mp h))
    let eF : autFix (MulAut.congr e α) ≃* autFix α := autFixCongrEquiv e α
    exact ⟨⟨E.map eF.toMonoidHom, isElemAbelian_map _ hE, by
      rw [Subgroup.card_map_of_injective eF.injective, hE9']⟩, hmv.of_mulEquiv eF.symm⟩

end Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148H
