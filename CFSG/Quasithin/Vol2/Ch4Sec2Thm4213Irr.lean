module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Typ
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213C2
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213IrrG

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative Matrix Pointwise

variable {G : Type} [Group G] [Finite G]

namespace T4213N

omit [Finite G] in
theorem eq_bot_or_eq_of_slExteriorTwo {L V : Subgroup G} [IsMulCommutative ↥V]
    (h : SLExteriorTwo (V := ↥V) (autOn L V) ⊤ ⊥ 4) {W : Subgroup G} (hWV : W ≤ V)
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) : W = ⊥ ∨ W = V := by
  obtain ⟨π, -, -, -, -, -, -, -, β, -, hβk, hβe⟩ := h
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    have h1 := (hβk u).mp hu
    rw [Subgroup.mem_bot] at h1 ⊢
    exact Subtype.ext h1
  let q : Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2)) →* ↥(FFModel.extSq (ZMod 2) 4).sec ⧸
      (FFModel.extSq (ZMod 2) 4).ker.subgroupOf (FFModel.extSq (ZMod 2) 4).sec :=
    (QuotientGroup.mk' _).comp ((MonoidHom.id _).codRestrict _ fun _ => trivial)
  let Y : Subgroup (Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) :=
    (((W.subgroupOf V).comap (⊤ : Subgroup ↥V).subtype).map β).comap q
  let X : AddSubgroup (AltHeart 8) := (Subgroup.toAddSubgroup' Y).comap heartEquiv.toAddMonoidHom
  have hmemX : ∀ x : AltHeart 8, x ∈ X ↔ ∃ u : ↥(⊤ : Subgroup ↥V), ((u : ↥V) : G) ∈ W ∧
      β u = q (Multiplicative.ofAdd (heartEquiv x)) := fun x => Iff.rfl
  have hinv : ∀ σ : alternatingGroup (Fin 8), ∀ x : ↥(evenWeight 8),
      (QuotientAddGroup.mk x : AltHeart 8) ∈ X →
        (QuotientAddGroup.mk (permWeight 8 (σ : Equiv.Perm (Fin 8)) x) : AltHeart 8) ∈ X := by
    intro σ x hx
    obtain ⟨u, huW, hu⟩ := (hmemX _).mp hx
    obtain ⟨g, hgL, hg⟩ := Setup.mem_autOn_iff.mp (π (B5FinS8.alpha σ)).2
    have hact : ∀ v : ↥V, ((((π (B5FinS8.alpha σ) : ↥(autOn L V)) : MulAut ↥V) v : ↥V) : G) =
        g * v * (g : G)⁻¹ := by
      intro v
      rw [← hg, Setup.coe_conjAct_apply]
    have h1 := hβe (B5FinS8.alpha σ) u
      ⟨Multiplicative.ofAdd (heartEquiv (QuotientAddGroup.mk x)), trivial⟩ trivial trivial hu
    have h2 : (⟨(FFModel.extSq (ZMod 2) 4).act (B5FinS8.alpha σ)
          (Multiplicative.ofAdd (heartEquiv (QuotientAddGroup.mk x))), trivial⟩ :
          ↥(FFModel.extSq (ZMod 2) 4).sec) =
        ⟨Multiplicative.ofAdd (heartEquiv (QuotientAddGroup.mk
          (permWeight 8 (σ : Equiv.Perm (Fin 8)) x))), trivial⟩ := by
      apply Subtype.ext
      show extSqAct (ZMod 2) 4 (B5FinS8.alpha σ)
          (Multiplicative.ofAdd (heartEquiv (QuotientAddGroup.mk x))) =
        Multiplicative.ofAdd (heartEquiv (QuotientAddGroup.mk
          (permWeight 8 (σ : Equiv.Perm (Fin 8)) x)))
      rw [heartEquiv_perm]
      rfl
    refine (hmemX _).mpr ⟨⟨((π (B5FinS8.alpha σ) : ↥(autOn L V)) : MulAut ↥V) (u : ↥V), trivial⟩,
      ?_, h1.trans (congrArg QuotientGroup.mk h2)⟩
    show ((((π (B5FinS8.alpha σ) : ↥(autOn L V)) : MulAut ↥V) (u : ↥V) : ↥V) : G) ∈ W
    rw [hact]
    exact (Subgroup.mem_normalizer_iff.mp (hLW hgL) _).mp huW
  rcases heart_eq_bot_or_top X hinv with hX | hX
  ·
    left
    rw [eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_bot]
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨⟨w, hWV hw⟩, trivial⟩)
    have hxX : heartEquiv.symm (Multiplicative.toAdd
        (m.1 : Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2)))) ∈ X := by
      refine (hmemX _).mpr ⟨⟨⟨w, hWV hw⟩, trivial⟩, hw, ?_⟩
      rw [AddEquiv.apply_symm_apply, ← hm]
      rfl
    rw [hX, AddSubgroup.mem_bot, AddEquiv.map_eq_zero_iff] at hxX
    have hm1 : m = 1 := by
      apply Subtype.ext
      show (m.1 : Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) = 1
      exact Multiplicative.toAdd.injective (hxX.trans toAdd_one.symm)
    have h1 : β ⟨⟨w, hWV hw⟩, trivial⟩ = 1 := by
      rw [← hm, hm1, QuotientGroup.mk_one]
    have h2 := (hβk _).mp h1
    rw [Subgroup.mem_bot] at h2
    exact congrArg Subtype.val h2
  ·
    right
    refine le_antisymm hWV fun v hv => ?_
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨⟨v, hv⟩, trivial⟩)
    have hxX : heartEquiv.symm (Multiplicative.toAdd
        (m.1 : Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2)))) ∈ X := by
      rw [hX]
      exact AddSubgroup.mem_top _
    obtain ⟨u, huW, hu⟩ := (hmemX _).mp hxX
    rw [AddEquiv.apply_symm_apply] at hu
    have h1 : u = ⟨⟨v, hv⟩, trivial⟩ := hβi (hu.trans (by rw [← hm]; rfl))
    rw [h1] at huW
    exact huW

omit [Finite G] in
theorem irr_of_slExteriorTwo {L V : Subgroup G} [IsMulCommutative ↥V]
    (h : SLExteriorTwo (V := ↥V) (autOn L V) ⊤ ⊥ 4) {W : Subgroup G}
    (hCW : V ⊓ Subgroup.centralizer (L : Set G) ≤ W) (hWV : W ≤ V)
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) :
    W = V ⊓ Subgroup.centralizer (L : Set G) ∨ W = V := by
  rcases eq_bot_or_eq_of_slExteriorTwo h hWV hLW with hW | hW
  · left
    rw [hW]
    exact (le_bot_iff.mp (hW ▸ hCW)).symm
  · exact Or.inr hW

omit [Finite G] in
theorem pCore_le_subgroupOf {X N : Subgroup G} (hQN : pCoreOf 2 X ≤ N) :
    CFSG.pCore 2 ↥X ≤ N.subgroupOf X := by
  intro x hx
  exact hQN ⟨x, hx, rfl⟩

omit [Finite G] in
theorem subgroupOf_map_normal {X N : Subgroup G} (hXN : X ≤ Subgroup.normalizer (N : Set G)) :
    ((N.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))).Normal := by
  have hn : (N.subgroupOf X).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hXN g.2) n).mp hn⟩
  exact hn.map _ (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem mem_of_mk_mem {X N : Subgroup G} (hQN : pCoreOf 2 X ≤ N) {x : ↥X}
    (hx : (QuotientGroup.mk x : ModO2 X) ∈
      (N.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))) :
    (x : G) ∈ N := by
  obtain ⟨y, hy, hyx⟩ := hx
  have h1 : y⁻¹ * x ∈ CFSG.pCore 2 ↥X := by
    rw [← QuotientGroup.eq]
    exact hyx
  have h2 := (N.subgroupOf X).mul_mem hy (pCore_le_subgroupOf hQN h1)
  rw [mul_inv_cancel_left] at h2
  exact h2

omit [Finite G] in
theorem relIndex_eq_index_map {X N : Subgroup G} (hQN : pCoreOf 2 X ≤ N) :
    N.relIndex X = ((N.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))).index := by
  have hker : (QuotientGroup.mk' (CFSG.pCore 2 ↥X)).ker ≤ N.subgroupOf X := by
    rw [QuotientGroup.ker_mk']
    exact pCore_le_subgroupOf hQN
  exact (Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _) hker).symm

theorem mem_of_isHat {X N : Subgroup G} (hX : IsHat (ModO2 X) (alternatingGroup (Fin 6)))
    {x : ↥X} (hxc : (QuotientGroup.mk x : ModO2 X) ∈ Subgroup.center (ModO2 X))
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) (hQN : pCoreOf 2 X ≤ N)
    (h27 : ¬ 27 ∣ N.relIndex X) : (x : G) ∈ N := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hX.1 (subgroupOf_map_normal hXN) with
    htop | hcen
  · refine mem_of_mk_mem hQN ?_
    rw [htop]
    exact Subgroup.mem_top _
  · have hdvd : Nat.card ((N.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))) ∣ 3 := by
      rw [← hX.2.1]
      exact Subgroup.card_dvd_of_le hcen
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h1 | h3
    · exfalso
      apply h27
      rw [relIndex_eq_index_map hQN, Subgroup.eq_bot_of_card_eq _ h1, Subgroup.index_bot,
        C489.card_of_isHat_alt6 hX]
      norm_num
    · have heq : (N.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) =
          Subgroup.center (ModO2 X) :=
        Subgroup.eq_of_le_of_card_ge hcen (le_of_eq (by rw [h3, hX.2.1]))
      refine mem_of_mk_mem hQN ?_
      rw [heq]
      exact hxc

omit [Finite G] in
theorem eq_of_isSimpleGroup {X N : Subgroup G} (hs : IsSimpleGroup (ModO2 X))
    (h27X : 27 ∣ Nat.card (ModO2 X)) (hNX : N ≤ X) (hXN : X ≤ Subgroup.normalizer (N : Set G))
    (hQN : pCoreOf 2 X ≤ N) (h27 : ¬ 27 ∣ N.relIndex X) : N = X := by
  have := hs
  have := subgroupOf_map_normal (N := N) hXN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((N.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))) with hbot | htop
  · exfalso
    apply h27
    rw [relIndex_eq_index_map hQN, hbot, Subgroup.index_bot]
    exact h27X
  · refine le_antisymm hNX fun x hx => ?_
    refine mem_of_mk_mem (x := ⟨x, hx⟩) hQN ?_
    rw [htop]
    exact Subgroup.mem_top _

theorem eq_bot_or_eq_blockU_of_isHatA6Block {B : Subgroup G} (h : CFSG.Quasithin.IsHatA6Block B)
    {W : Subgroup G} (hWU : W ≤ blockU B) (hBW : B ≤ Subgroup.normalizer (W : Set G)) :
    W = ⊥ ∨ W = blockU B := by
  obtain ⟨hsh, hhat, hcard, hcent⟩ := h
  obtain ⟨-, -, ⟨hUQ, hU2⟩, -, -⟩ := hsh
  have hUc : ∀ a ∈ blockU B, ∀ b ∈ blockU B, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hUQ ha)).2 b
      (Subgroup.mem_inf.mp (hUQ hb)).1).symm
  have hXU : B ≤ Subgroup.normalizer (blockU B : Set G) :=
    Subgroup.normalizer_commutator_ge_right _ _
  have hmemQ : ∀ x : ↥B, (x : G) ∈ pCoreOf 2 B ↔ (QuotientGroup.mk x : ModO2 B) = 1 := by
    intro x
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.mem_map_iff_mem B.subtype_injective
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : ↥(Subgroup.center (ModO2 B)), z₀ ≠ 1 := by
    by_contra hne
    push Not at hne
    have h1 : Nat.card (Subgroup.center (ModO2 B)) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (hne a).trans (hne b).symm⟩, ⟨1⟩⟩
    have h2 : Nat.card (Subgroup.center (ModO2 B)) = 3 := hhat.2.1
    omega
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (z₀ : ModO2 B)
  have hz3 : (z₀ : ModO2 B) ^ 3 = 1 := by
    have h1 : z₀ ^ Nat.card (Subgroup.center (ModO2 B)) = 1 := pow_card_eq_one'
    rw [hhat.2.1] at h1
    simpa using congrArg Subtype.val h1
  have hy3 : (y : G) ^ 3 ∈ Subgroup.centralizer (blockU B : Set G) := by
    have h1 : ((y ^ 3 : ↥B) : G) ∈ pCoreOf 2 B := by
      rw [hmemQ, QuotientGroup.mk_pow, hy, hz3]
    rw [← hcent] at h1
    simpa using (Subgroup.mem_inf.mp h1).2
  have hyU : (y : G) ∉ Subgroup.centralizer (blockU B : Set G) := by
    intro hyU
    have h1 : (y : G) ∈ pCoreOf 2 B := by
      rw [← hcent]
      exact Subgroup.mem_inf.mpr ⟨y.2, hyU⟩
    rw [hmemQ, hy] at h1
    exact hz₀ (Subtype.ext h1)
  have hnorm : ∀ N : Subgroup G, N ≤ B → B ≤ Subgroup.normalizer (N : Set G) →
      B ⊓ Subgroup.centralizer (blockU B : Set G) ≤ N → ¬ 27 ∣ N.relIndex B →
        (y : G) ∈ N := by
    intro N _ hXN hCN h27
    refine mem_of_isHat (x := y) hhat ?_ hXN ?_ h27
    · rw [hy]
      exact z₀.2
    · rw [← hcent]
      exact hCN
  exact eq_bot_or_eq_of_order_three hXU hUc hU2 (hcard.le.trans (by norm_num)) y.2 hy3 hyU hnorm
    hWU hBW

end T4213N

namespace Conf4212

variable {T M L I H K : Subgroup G} (c : Conf4212 G T M L I H K)
include c

theorem LH_le_normalizer_V :
    perfectCore (L ⊓ H) ≤
      Subgroup.normalizer ((⁅reducedAggregate (L ⊔ T), L⁆ : Subgroup G) : Set G) := by
  have h1 := c.hypC28.V_comm
  rw [conjClosure_eq_self c.LH_normal] at h1
  rw [← h1]
  exact Subgroup.normalizer_commutator_ge_right _ _

theorem V_le_LH : ⁅reducedAggregate (L ⊔ T), L⁆ ≤ perfectCore (L ⊓ H) := by
  have h := c.hypC28.V_le
  rwa [conjClosure_eq_self c.LH_normal] at h

theorem V_le_pCoreOf_LH : ⁅reducedAggregate (L ⊔ T), L⁆ ≤ pCoreOf 2 (perfectCore (L ⊓ H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_pCoreOf_of_le_normalizer 2 c.V_le_LH c.LH_le_normalizer_V fun x => ⟨1, ?_⟩
  exact Subtype.ext (by simpa using c.hypC28.V_elem.2 _ x.2)

theorem V_le_blockU : ⁅reducedAggregate (L ⊔ T), L⁆ ≤ blockU (perfectCore (L ⊓ H)) := by
  have h1 := c.hypC28.V_comm
  rw [conjClosure_eq_self c.LH_normal] at h1
  rw [← h1]
  exact Subgroup.commutator_mono c.V_le_pCoreOf_LH le_rfl

theorem inf_centralizer_eq :
    ⁅reducedAggregate (L ⊔ T), L⁆ ⊓ Subgroup.centralizer (L : Set G) =
      ⁅reducedAggregate (L ⊔ T), L⁆ ⊓ Subgroup.centralizer (perfectCore (L ⊓ H) : Set G) := by
  have hVC : ⁅reducedAggregate (L ⊔ T), L⁆ ≤ Subgroup.centralizer (pCoreOf 2 L : Set G) :=
    Subgroup.le_centralizer_iff.mp (c.pCoreOf_le_centralizer_V c.pCoreOf_L_le)
  apply le_antisymm
  · exact inf_le_inf_left _ (Subgroup.centralizer_le ((perfectCore_le _).trans inf_le_left))
  · refine le_inf inf_le_left ?_
    rw [← Subgroup.le_centralizer_iff]
    refine c.L_le.trans (_root_.sup_le ?_ ?_)
    · rw [Subgroup.le_centralizer_iff]
      exact inf_le_right
    · rw [Subgroup.le_centralizer_iff]
      exact inf_le_left.trans hVC

theorem V_eq_blockU_of_isHatA6Block (h : CFSG.Quasithin.IsHatA6Block (perfectCore (L ⊓ H))) :
    ⁅reducedAggregate (L ⊔ T), L⁆ = blockU (perfectCore (L ⊓ H)) :=
  (T4213N.eq_bot_or_eq_blockU_of_isHatA6Block h c.V_le_blockU c.LH_le_normalizer_V).resolve_left
    c.hypC28.V_ne

theorem irr_of_isHatA6Block (h : CFSG.Quasithin.IsHatA6Block (perfectCore (L ⊓ H)))
    {W : Subgroup G}
    (hCW : ⁅reducedAggregate (L ⊔ T), L⁆ ⊓ Subgroup.centralizer (L : Set G) ≤ W)
    (hWV : W ≤ ⁅reducedAggregate (L ⊔ T), L⁆) (hLW : L ≤ Subgroup.normalizer (W : Set G)) :
    W = ⁅reducedAggregate (L ⊔ T), L⁆ ⊓ Subgroup.centralizer (L : Set G) ∨
      W = ⁅reducedAggregate (L ⊔ T), L⁆ := by
  have hLHL : perfectCore (L ⊓ H) ≤ L := (perfectCore_le _).trans inf_le_left
  rcases T4213N.eq_bot_or_eq_blockU_of_isHatA6Block h (hWV.trans c.V_le_blockU)
      (hLHL.trans hLW) with hW | hW
  · left
    rw [hW]
    exact (le_bot_iff.mp (hW ▸ hCW)).symm
  · right
    exact le_antisymm hWV (c.V_le_blockU.trans hW.ge)

theorem irr_of_isG2Block (h : CFSG.Quasithin.IsG2Block (perfectCore (L ⊓ H)))
    {W : Subgroup G}
    (hCW : ⁅reducedAggregate (L ⊔ T), L⁆ ⊓ Subgroup.centralizer (L : Set G) ≤ W)
    (hWV : W ≤ ⁅reducedAggregate (L ⊔ T), L⁆) (hLW : L ≤ Subgroup.normalizer (W : Set G)) :
    W = ⁅reducedAggregate (L ⊔ T), L⁆ ⊓ Subgroup.centralizer (L : Set G) ∨
      W = ⁅reducedAggregate (L ⊔ T), L⁆ := by
  set LH := perfectCore (L ⊓ H) with hLHdef
  obtain ⟨hsh, hU, hidx, hnatural⟩ := h
  obtain ⟨-, -, ⟨hUQ, -⟩, -, -⟩ := hsh
  have hLHL : LH ≤ L := (perfectCore_le _).trans inf_le_left
  rw [c.inf_centralizer_eq] at hCW ⊢
  have hne : ¬ LH ≤ Subgroup.centralizer
      ((⁅reducedAggregate (L ⊔ T), L⁆ : Subgroup G) : Set G) := by
    intro hle
    apply c.hypC28.V_ne
    have h1 := c.hypC28.V_comm
    rw [conjClosure_eq_self c.LH_normal] at h1
    rw [← h1, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.le_centralizer_iff.mp hle
  have hidx' : (⁅reducedAggregate (L ⊔ T), L⁆ ⊓ Subgroup.centralizer (LH : Set G)).relIndex
      ⁅reducedAggregate (L ⊔ T), L⁆ ≤ 64 := by
    have h1 : (Subgroup.centralizer (LH : Set G)).relIndex (blockU LH) = 2 ^ 6 := by
      rw [← Subgroup.inf_relIndex_left]
      exact hidx
    rw [Subgroup.inf_relIndex_left]
    calc (Subgroup.centralizer (LH : Set G)).relIndex ⁅reducedAggregate (L ⊔ T), L⁆
        ≤ (Subgroup.centralizer (LH : Set G)).relIndex (blockU LH) :=
          Subgroup.relIndex_le_of_le_right c.V_le_blockU (by rw [h1]; norm_num)
      _ = 64 := by rw [h1]; norm_num
  have hQV : pCoreOf 2 LH ≤
      LH ⊓ Subgroup.centralizer ((⁅reducedAggregate (L ⊔ T), L⁆ : Subgroup G) : Set G) := by
    refine le_inf (pCoreOf_le 2 LH) ?_
    rw [Subgroup.le_centralizer_iff]
    intro v hv
    exact (Subgroup.mem_inf.mp (hUQ (c.V_le_blockU hv))).2
  have hs : IsSimpleGroup (ModO2 LH) :=
    CFSG.Quasithin.SBc11.isSimpleGroup_of_list (Or.inr (Or.inr hU))
  have h27 : 27 ∣ Nat.card (ModO2 LH) := by
    rw [CFSG.Quasithin.SBc11.card_of_isPSU_three_three hU]
    norm_num
  exact T4213N.eq_or_eq_of_index_le c.LH_le_normalizer_V c.V_comm c.hypC28.V_elem.2
    (perfect_of_mem_cComp c.LH_mem) hne hidx'
    (fun N hNX hXN hCN h27N => T4213N.eq_of_isSimpleGroup hs h27 hNX hXN (hQV.trans hCN) h27N)
    hCW hWV (hLHL.trans hLW)

theorem card_ne_of_cases
    (hcase : C48Case1 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
        K ∨
      C48Case2 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case3 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case4 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case8 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K) :
    Nat.card (ModO2 L) ≠ 1080 ∧ Nat.card (ModO2 L) ≠ 6048 := by
  rcases hcase with h1 | h2 | h3 | h4 | h8
  · obtain ⟨n, -, -, hn⟩ := c.type_of_case1 h1
    have h := T4213.psl2_card_ne n
    rw [hn]
    exact ⟨h.2.2.1, h.2.2.2⟩
  · rcases c.type_of_case2 h2 with ⟨-, hc⟩ | ⟨-, hc⟩ <;> rw [hc] <;> norm_num
  · obtain ⟨e⟩ := c.equiv_alt_of_isAltBlockType h3.2
    rw [Nat.card_congr e.toEquiv, C489.card_alt6]
    norm_num
  · obtain ⟨e⟩ := c.equiv_alt7_of_isExcA7Block h4.2
    rw [Nat.card_congr e.toEquiv, C489.card_alt7]
    norm_num
  · obtain ⟨e⟩ := c.equiv_alt_of_isAltBlockType h8.2
    rw [Nat.card_congr e.toEquiv, C489.card_alt6]
    norm_num

theorem irrCase4213
    (hcase : C48Case1 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
        K ∨
      C48Case2 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case3 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case4 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case5 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case7 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case8 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K) :
    IrrCase4213 G L ⁅reducedAggregate (L ⊔ T), L⁆ := by
  intro hyp W hCW hWV hLW
  have hgen : (C48Case1 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H))
        ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case2 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case3 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case4 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case8 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K) →
      W = ⁅reducedAggregate (L ⊔ T), L⁆ ⊓ Subgroup.centralizer (L : Set G) ∨
        W = ⁅reducedAggregate (L ⊔ T), L⁆ := by
    intro h
    obtain ⟨hne1, hne2⟩ := c.card_ne_of_cases h
    rcases hyp with hhat | hpsu | ⟨-, _, hext⟩
    · exact absurd (T4213.card_of_hatA6 hhat) hne1
    · exact absurd (T4213.card_of_lieModel_psu331 hpsu) hne2
    · exact T4213N.irr_of_slExteriorTwo hext hCW hWV hLW
  rcases hcase with h | h | h | h | h5 | h7 | h
  · exact hgen (Or.inl h)
  · exact hgen (Or.inr (Or.inl h))
  · exact hgen (Or.inr (Or.inr (Or.inl h)))
  · exact hgen (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases hyp with - | hpsu | ⟨-, _, hext⟩
    · exact c.irr_of_isHatA6Block h5.2 hCW hWV hLW
    · exact absurd ((T4213.card_of_hatA6 (c.hat_of_isHatA6Block h5.2)).symm.trans
        (T4213.card_of_lieModel_psu331 hpsu)) (by norm_num)
    · exact T4213N.irr_of_slExteriorTwo hext hCW hWV hLW
  · rcases hyp with hhat | - | ⟨-, _, hext⟩
    · exact absurd ((T4213.card_of_hatA6 hhat).symm.trans
        (T4213.card_of_lieModel_psu331 (c.lieModel_of_isG2Block h7.2))) (by norm_num)
    · exact c.irr_of_isG2Block h7.2 hCW hWV hLW
    · exact T4213N.irr_of_slExteriorTwo hext hCW hWV hLW
  · exact hgen (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Conf4212

end CFSG.Quasithin.H13.Ch4
