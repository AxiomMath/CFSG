module

public import CFSG.Quasithin.MS93.S32Cent
public import CFSG.Quasithin.MS93.SkTypes
public import CFSG.Quasithin.MS93.S5Stmt

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S5

variable {G : Type} [Group G]

section KerIm

variable {M : Subgroup G} {H : Type*} [Group H] (a : ↥M →* H)

@[expose] def kerG : Subgroup G := a.ker.map M.subtype

@[expose] def imSp (E : Subgroup G) : Subgroup H := (E.subgroupOf M).map a

theorem kerG_le : kerG a ≤ M := Subgroup.map_subtype_le _

theorem mem_kerG {g : G} : g ∈ kerG a ↔ ∃ hg : g ∈ M, a ⟨g, hg⟩ = 1 := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m.2, hm⟩
  · rintro ⟨hg, h1⟩
    exact ⟨⟨g, hg⟩, h1, rfl⟩

theorem le_normalizer_kerG : M ≤ Subgroup.normalizer (kerG a : Set G) := by
  have key : ∀ m ∈ M, ∀ x ∈ kerG a, m * x * m⁻¹ ∈ kerG a := by
    intro m hm x hx
    obtain ⟨hxM, hx1⟩ := (mem_kerG a).1 hx
    refine (mem_kerG a).2 ⟨M.mul_mem (M.mul_mem hm hxM) (M.inv_mem hm), ?_⟩
    have e : (⟨m * x * m⁻¹, M.mul_mem (M.mul_mem hm hxM) (M.inv_mem hm)⟩ : ↥M) =
        ⟨m, hm⟩ * ⟨x, hxM⟩ * (⟨m, hm⟩ : ↥M)⁻¹ := rfl
    rw [e, map_mul, map_mul, hx1, mul_one, map_inv, mul_inv_cancel]
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key m hm x, fun hx => ?_⟩
  have := key m⁻¹ (M.inv_mem hm) _ hx
  simpa [mul_assoc] using this

theorem imSp_mono {E E' : Subgroup G} (h : E ≤ E') : imSp a E ≤ imSp a E' :=
  Subgroup.map_mono fun _ hx => h hx

theorem card_imSp_eq_relIndex {E : Subgroup G} (hE : E ≤ M) :
    Nat.card (imSp a E) = (kerG a).relIndex E := by
  rw [imSp, ← Subgroup.relIndex_ker, kerG]
  have h1 := Subgroup.relIndex_map_map_of_injective a.ker (E.subgroupOf M) M.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hE] at h1
  exact h1.symm

theorem card_subgroupOf (K L' : Subgroup G) : Nat.card (K.subgroupOf L') = Nat.card ↥(K ⊓ L') := by
  rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective L'.subtype_injective]

end KerIm

variable {M T L : Subgroup G} {k : ℕ} {F : Type} [Field F] [Fintype F]
  {a : ↥M →* ↥(StatedSp 2 F)}

namespace IsSp4Data

variable (hd : IsSp4Data M T L k F a)
include hd

theorem one_le : 1 ≤ k := hd.1

theorem card_eq : Fintype.card F = 2 ^ k := hd.2.1

theorem nat_card_eq : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.card_eq]

theorem surj : Function.Surjective a := hd.2.2.1

theorem nat : IsSumOfNaturalModulesVia M (Uq M T L)
    (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) a false 1 := hd.2.2.2

theorem charP : CharP F 2 := charP_of_card_eq_prime_pow hd.card_eq

theorem commutator_mem_of_mem_kerG {l : G} (hl : l ∈ kerG a) {u : G} (hu : u ∈ Uq M T L) :
    l * u * l⁻¹ * u⁻¹ ∈ Uq M T L ⊓ Subgroup.centralizer (L : Set G) := by
  obtain ⟨hlM, hl1⟩ := (mem_kerG a).1 hl
  obtain ⟨hMU, hCU, β, hβs, hβk, hβeq⟩ := hd.nat
  have hlu : l * u * l⁻¹ ∈ Uq M T L :=
    (Subgroup.mem_normalizer_iff.1 (hMU hlM) u).1 hu
  have h1 := hβeq ⟨l, hlM⟩ ⟨u, hu⟩ ⟨l * u * l⁻¹, hlu⟩ rfl
  have h2 : β ⟨l * u * l⁻¹, hlu⟩ = β ⟨u, hu⟩ := by
    apply Multiplicative.toAdd.injective
    funext i
    rw [h1 i, hl1]
    simp [moduleAct]
  have h3 : (⟨l * u * l⁻¹, hlu⟩ : ↥(Uq M T L)) * (⟨u, hu⟩ : ↥(Uq M T L))⁻¹ ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h2, mul_inv_cancel]
  rw [hβk, Subgroup.mem_subgroupOf] at h3
  exact h3

variable [Finite G] (h : PUHyp M T L)
include h

theorem pCoreOf_le_kerG : pCoreOf 2 M ≤ kerG a := by
  intro x hx
  refine (mem_kerG a).2 ⟨pCoreOf_le' M hx, eq_one_of_isSumOfNaturalModulesVia hd.nat ?_⟩
  intro v hv
  have hvX : v ∈ Xq M := h.Uq_le_Xq hv
  have hvZ := PU.omegaOneCenterOf_le_centerOf (pCoreOf 2 M) hvX
  have hc := Subgroup.mem_centralizer_iff.1 hvZ.2 x hx
  show x * v * x⁻¹ = v
  rw [hc, mul_inv_cancel_right]

omit [Fintype F] hd in
theorem commute_of_mem_Uq {u v : G} (hu : u ∈ Uq M T L) (hv : v ∈ Uq M T L) : u * v = v * u :=
  by
  have hu' := PU.omegaOneCenterOf_le_centerOf (pCoreOf 2 M) (h.Uq_le_Xq hu)
  have hv' := PU.omegaOneCenterOf_le_centerOf (pCoreOf 2 M) (h.Uq_le_Xq hv)
  exact (Subgroup.mem_centralizer_iff.1 hu'.2 v hv'.1).symm

theorem not_le_kerG : ¬ L ≤ kerG a := by
  intro hL
  have hUL : ⁅Uq M T L, L⁆ ≤ Uq M T L ⊓ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.commutator_le]
    intro u hu l hl
    have hw : u⁻¹ ∈ Uq M T L := inv_mem hu
    have h1 := hd.commutator_mem_of_mem_kerG (hL hl) hw
    have hlw : l * u⁻¹ * l⁻¹ ∈ Uq M T L :=
      (Subgroup.mem_normalizer_iff.1 (h.L_le.trans (le_normalizer_Uq h.le_normalizer) hl) _).1 hw
    have hc : l * u⁻¹ * l⁻¹ * u⁻¹⁻¹ ∈ Uq M T L := h1.1
    have e : ⁅u, l⁆ = u * (l * u⁻¹ * l⁻¹ * u⁻¹⁻¹) * u⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e, commute_of_mem_Uq h hu hc, mul_inv_cancel_right]
    exact h1
  have hUL1 : ⁅⁅Uq M T L, L⁆, L⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx l hl
    have hx' := hUL hx
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.1 hx'.2 l hl).symm
  have hU := commutator_eq_commutator_commutator (Uq_le (T := T) h.L_le) h.L_le
    (le_normalizer_Uq (T := T) h.le_normalizer) h.le_normalizer h.perfect
  have hZ := commutator_eq_commutator_commutator (Z0q_le M T) h.L_le (le_normalizer_Z0q M T)
    h.le_normalizer h.perfect
  rw [hUL1] at hU
  have hU0 : Uq M T L = ⊥ := by rw [Uq, hZ, ← Uq, hU]
  apply h.not_le_centralizer_Z0q
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
  exact hU0

theorem inf_kerG : T ⊓ kerG a = pCoreOf 2 M := by
  refine le_antisymm ?_ (le_inf h.pCore_le (hd.pCoreOf_le_kerG h))
  set P := T ⊓ kerG a with hP
  have hPM : P ≤ M := inf_le_left.trans h.le
  have hcomm : ⁅kerG a, L⁆ ≤ pCoreOf 2 M :=
    h.commutator_le_pCoreOf_M (kerG_le a) (le_normalizer_kerG a) (hd.not_le_kerG h)
  have hTn : T ≤ Subgroup.normalizer (P : Set G) :=
    le_normalizer_inf Subgroup.le_normalizer (h.le.trans (le_normalizer_kerG a))
  have hLn : L ≤ Subgroup.normalizer (P : Set G) := by
    have key : ∀ l ∈ L, ∀ p ∈ P, l * p * l⁻¹ ∈ P := by
      intro l hl p hp
      have hlp : l * p * l⁻¹ * p⁻¹ ∈ pCoreOf 2 M := by
        have := Subgroup.commutator_mem_commutator hp.2 hl
        have h' := (pCoreOf 2 M).inv_mem (hcomm this)
        simpa [commutatorElement_def, mul_assoc] using h'
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (le_normalizer_kerG a (h.L_le hl)) p).mp hp.2⟩
      have e : l * p * l⁻¹ = (l * p * l⁻¹ * p⁻¹) * p := by group
      rw [e]
      exact T.mul_mem (h.pCore_le hlp) hp.1
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro p
    refine ⟨key l hl p, fun hp => ?_⟩
    have := key l⁻¹ (L.inv_mem hl) _ hp
    simpa [mul_assoc] using this
  have hMn : M ≤ Subgroup.normalizer (P : Set G) := by
    rw [h.eq_sup]
    exact sup_le hLn hTn
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPM hMn
    (h.isPGroup.to_le inf_le_left)

theorem card_imSp {E : Subgroup G} (hE : E ≤ T) :
    Nat.card (imSp a E) = (pCoreOf 2 M).relIndex E := by
  rw [card_imSp_eq_relIndex a (hE.trans h.le), ← Subgroup.inf_relIndex_right,
    ← inf_eq_right.2 hE, ← inf_assoc, inf_comm (kerG a), hd.inf_kerG h, inf_eq_right.2 hE,
    Subgroup.inf_relIndex_right]

end IsSp4Data

structure NatVec (M T L : Subgroup G) {F : Type} [Field F] (a : ↥M →* ↥(StatedSp 2 F)) where
  toVec : ↥(Uq M T L) →* Multiplicative (MSP.V4 F)
  surj : Function.Surjective toVec
  ker_iff : ∀ u, toVec u = 1 ↔ (u : G) ∈ Uq M T L ⊓ Subgroup.centralizer (L : Set G)
  equiv : ∀ (m : ↥M) (u v : ↥(Uq M T L)), (v : G) = m * u * m⁻¹ →
    Multiplicative.toAdd (toVec v) = MSP.mat (a m) *ᵥ Multiplicative.toAdd (toVec u)

theorem IsSp4Data.nonempty_natVec (hd : IsSp4Data M T L k F a) : Nonempty (NatVec M T L a) := by
  obtain ⟨-, -, β, hβs, hβk, hβeq⟩ := hd.nat
  let π : Multiplicative (Fin 1 → MSP.V4 F) →* Multiplicative (MSP.V4 F) :=
    { toFun := fun x => Multiplicative.ofAdd (Multiplicative.toAdd x 0)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hπinj : Function.Injective π := by
    intro x y hxy
    apply Multiplicative.toAdd.injective
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    exact congrArg Multiplicative.toAdd hxy
  refine ⟨⟨π.comp β, ?_, fun u => ?_, fun m u v huv => ?_⟩⟩
  · intro y
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd fun _ => Multiplicative.toAdd y)
    exact ⟨u, by rw [MonoidHom.comp_apply, hu]; rfl⟩
  · rw [MonoidHom.comp_apply, ← map_one π, hπinj.eq_iff, ← MonoidHom.mem_ker, hβk,
      Subgroup.mem_subgroupOf]
  · have := hβeq m u v huv 0
    simpa [π, moduleAct] using this

namespace NatVec

variable (nv : NatVec M T L a)

@[expose] def vec (u : ↥(Uq M T L)) : MSP.V4 F := Multiplicative.toAdd (nv.toVec u)

omit [Fintype F] in
theorem vec_conj (m : ↥M) (u : ↥(Uq M T L)) (hu : (m : G) * u * (m : G)⁻¹ ∈ Uq M T L) :
    nv.vec ⟨_, hu⟩ = MSP.mat (a m) *ᵥ nv.vec u :=
  nv.equiv m u ⟨_, hu⟩ rfl

omit [Fintype F] in
theorem mat_mulVec_vec_of_commute (m : ↥M) (u : ↥(Uq M T L))
    (hmu : (m : G) * u = u * (m : G)) : MSP.mat (a m) *ᵥ nv.vec u = nv.vec u := by
  have hu : (m : G) * u * (m : G)⁻¹ ∈ Uq M T L := by
    rw [hmu, mul_inv_cancel_right]
    exact u.2
  rw [← nv.vec_conj m u hu]
  congr 2
  rw [hmu, mul_inv_cancel_right]

omit [Fintype F] in
theorem vec_mem_fixSp {E : Subgroup G} (u : ↥(Uq M T L))
    (hu : (u : G) ∈ Subgroup.centralizer (E : Set G)) : nv.vec u ∈ MSP.fixSp (imSp a E) := by
  rw [MSP.mem_fixSp]
  rintro _ ⟨e, he, rfl⟩
  have hc := Subgroup.mem_centralizer_iff.1 hu (e : G) he
  exact nv.mat_mulVec_vec_of_commute (e : ↥M) u hc

omit [Fintype F] in
include nv in
theorem card_Uq :
    Nat.card ↥(Uq M T L) = Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) *
      Nat.card (MSP.V4 F) := by
  have hker : nv.toVec.ker = (Subgroup.centralizer (L : Set G)).subgroupOf (Uq M T L) := by
    ext u
    rw [MonoidHom.mem_ker, nv.ker_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨u.2, h⟩⟩
  have h1 := Subgroup.card_mul_index nv.toVec.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 nv.surj, Subgroup.card_top, hker,
    card_subgroupOf, inf_comm] at h1
  rw [← h1]
  rfl

omit [Fintype F] in
include nv in
theorem card_inf_centralizer_le [Finite G] [Finite F] (E : Subgroup G) :
    Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (E : Set G)) ≤
      Nat.card (MSP.fixSp (imSp a E)) *
        Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) := by
  set CE : Subgroup ↥(Uq M T L) := (Subgroup.centralizer (E : Set G)).subgroupOf (Uq M T L)
  have h1 := Subgroup.relIndex_mul_card (H := nv.toVec.ker) (K := CE)
  rw [Subgroup.relIndex_ker] at h1
  have hCE : Nat.card CE = Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (E : Set G)) := by
    rw [card_subgroupOf, inf_comm]
  have hmap : Nat.card (CE.map nv.toVec) ≤ Nat.card (MSP.fixSp (imSp a E)) := by
    let f : ↥(CE.map nv.toVec) → ↥(MSP.fixSp (imSp a E)) := fun x =>
      ⟨Multiplicative.toAdd (x : Multiplicative (MSP.V4 F)), by
        obtain ⟨_, ⟨u, hu, rfl⟩⟩ := x
        exact nv.vec_mem_fixSp u (Subgroup.mem_subgroupOf.1 hu)⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      have hv := congrArg Subtype.val hxy
      exact Multiplicative.toAdd.injective hv
    exact Nat.card_le_card_of_injective f hf
  have hker : Nat.card ↥(nv.toVec.ker ⊓ CE) ≤
      Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) := by
    have hle : nv.toVec.ker ⊓ CE ≤
        (Subgroup.centralizer (L : Set G)).subgroupOf (Uq M T L) := by
      intro u hu
      have := (nv.ker_iff u).1 hu.1
      exact Subgroup.mem_subgroupOf.2 this.2
    calc Nat.card ↥(nv.toVec.ker ⊓ CE) ≤
        Nat.card ((Subgroup.centralizer (L : Set G)).subgroupOf (Uq M T L)) :=
          Subgroup.card_le_of_le hle
      _ = _ := by rw [card_subgroupOf, inf_comm]
  rw [← hCE, ← h1]
  exact Nat.mul_le_mul hmap hker

omit [Fintype F] in
include nv in
theorem card_le_relIndex [Finite G] [Finite F] (E : Subgroup G) :
    Nat.card (MSP.V4 F) ≤ Nat.card (MSP.fixSp (imSp a E)) *
      (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) := by
  have h1 := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (E : Set G))
    (K := Uq M T L)
  rw [inf_comm] at h1
  have h2 := nv.card_inf_centralizer_le E
  have h3 := nv.card_Uq
  have hC : 0 < Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) := Nat.card_pos
  rw [h3] at h1
  have key : Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) * Nat.card (MSP.V4 F) ≤
      Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) *
        (Nat.card (MSP.fixSp (imSp a E)) *
          (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L)) := by
    calc _ = _ := h1.symm
      _ ≤ (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) *
          (Nat.card (MSP.fixSp (imSp a E)) *
            Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G))) :=
          Nat.mul_le_mul_left _ h2
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left key hC

end NatVec

namespace NatVec

variable (nv : NatVec M T L a)

omit [Fintype F] in
theorem mem_centralizer_iff_vec_mem_fixSp
    (hMU : M ≤ Subgroup.normalizer (Uq M T L : Set G))
    (hlift : ∀ m ∈ M, ∀ u ∈ Uq M T L, m * u * m⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G) →
      m * u * m⁻¹ = u)
    {E : Subgroup G} (hE : E ≤ M) (u : ↥(Uq M T L)) :
    (u : G) ∈ Subgroup.centralizer (E : Set G) ↔ nv.vec u ∈ MSP.fixSp (imSp a E) := by
  refine ⟨nv.vec_mem_fixSp u, fun hu => ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have heM : e ∈ M := hE he
  have hfix := (MSP.mem_fixSp.1 hu) (a ⟨e, heM⟩) ⟨⟨e, heM⟩, he, rfl⟩
  have heu : e * u * e⁻¹ ∈ Uq M T L :=
    (Subgroup.mem_normalizer_iff.1 (hMU heM) u).1 u.2
  have h1 := nv.vec_conj ⟨e, heM⟩ u heu
  have h2 : nv.vec ⟨e * u * e⁻¹, heu⟩ = nv.vec u := by rw [h1]; exact hfix
  have h3 : nv.toVec (⟨e * u * e⁻¹, heu⟩ * u⁻¹) = 1 := by
    rw [map_mul, map_inv]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, toAdd_one]
    have : Multiplicative.toAdd (nv.toVec ⟨e * u * e⁻¹, heu⟩) =
        Multiplicative.toAdd (nv.toVec u) := h2
    rw [this, add_neg_cancel]
  have h4 := ((nv.ker_iff _).1 h3).2
  have h5 := hlift e heM u u.2 h4
  calc e * (u : G) = e * u * e⁻¹ * e := by group
    _ = u * e := by rw [h5]

end NatVec

end S5

end CFSG.Quasithin.MS93
