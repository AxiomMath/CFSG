module

public import CFSG.Quasithin.MS93.S310MI
public import CFSG.Quasithin.MS93.S36SpESec

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S512N

section Perfect

variable {Γ : Type*} [Group Γ]

theorem commutator_mem_of_perfect {L B Z : Subgroup Γ} (hL : ⁅L, L⁆ = L)
    (hLZ : L ≤ Subgroup.normalizer (Z : Set Γ))
    (hBL : ⁅B, L⁆ ≤ Z) {x : Γ} (hxB : x ∈ Subgroup.normalizer (B : Set Γ))
    (hxZ : x ∈ Subgroup.normalizer (Z : Set Γ)) (hx : ∀ l ∈ L, ⁅x, l⁆ ∈ B) :
    ∀ l ∈ L, ⁅x, l⁆ ∈ Z := by
  let S : Subgroup Γ :=
    { carrier := {y | y ∈ Subgroup.normalizer (B : Set Γ) ∧ y ∈ Subgroup.normalizer (Z : Set Γ) ∧
        ∀ l ∈ L, ⁅y, l⁆ ∈ B}
      one_mem' := ⟨one_mem _, one_mem _, fun l _ => by simp⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨h₁B, h₁Z, h₁⟩ ⟨h₂B, h₂Z, h₂⟩
        refine ⟨mul_mem h₁B h₂B, mul_mem h₁Z h₂Z, fun l hl => ?_⟩
        have e : ⁅y₁ * y₂, l⁆ = (y₁ * ⁅y₂, l⁆ * y₁⁻¹) * ⁅y₁, l⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact mul_mem ((Subgroup.mem_normalizer_iff.1 h₁B _).1 (h₂ l hl)) (h₁ l hl)
      inv_mem' := by
        rintro y ⟨hB, hZ, hy⟩
        refine ⟨inv_mem hB, inv_mem hZ, fun l hl => ?_⟩
        have e : ⁅y⁻¹, l⁆ = y⁻¹ * ⁅y, l⁆⁻¹ * y := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hB) _).1 (inv_mem (hy l hl))
        simpa using this }
  have hW : Subgroup.zpowers x ≤ S := (Subgroup.zpowers_le).2 ⟨hxB, hxZ, hx⟩
  have hWL : ⁅Subgroup.zpowers x, L⁆ ≤ B := by
    rw [Subgroup.commutator_le]
    intro w hw l hl
    exact (hW hw).2.2 l hl
  have hWZ : Subgroup.zpowers x ≤ Subgroup.normalizer (Z : Set Γ) := fun w hw => (hW hw).2.1
  have key := S5B.commutator_le_of_perfect hL hWZ hLZ hWL hBL
  intro l hl
  exact key (Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers x) hl)

end Perfect

section Hyp

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem perfect_puTrans (h : PUHyp M T L) :
    ⁅puTrans h.le L (baseA _), puTrans h.le L (baseA (puAmalgam h.le))⁆ =
      puTrans h.le L (baseA (puAmalgam h.le)) := by
  rw [S5B.puTrans_L_baseA h, ← imM_commutator h.le h.L_le h.L_le, h.perfect]

structure SecHyp (h : PUHyp M T L) (V : Subgroup (puAmalgam h.le).Universal) : Prop where
  b : 2 < critDist (puAmalgam h.le)
  vv : V ≤ Vv _ (baseA (puAmalgam h.le))
  vn : stab _ (baseA (puAmalgam h.le)) ≤ Subgroup.normalizer (V : Set (puAmalgam h.le).Universal)
  comm : ⁅V, V⁆ ≤ S5.bSub h.le L (baseA _)
  sq : ∀ v ∈ V, v ^ 2 ∈ S5.bSub h.le L (baseA _)
  ne : ¬ V ≤ S5.bSub h.le L (baseA _)

structure NatHyp (h : PUHyp M T L) (k : ℕ) (V E Z Y : Subgroup (puAmalgam h.le).Universal) :
    Prop extends SecHyp h V where
  qv : ⁅V, Qv _ (baseA (puAmalgam h.le))⁆ ≤ S5.bSub h.le L (baseA _)
  es : E ≤ stab _ (baseA (puAmalgam h.le))
  ee : CFSG.Open.IsElemAbelian 2 E
  eq : (Qv _ (baseA (puAmalgam h.le))).relIndex E = 2 ^ k
  eu : (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
    (S5.uSub h.le L (baseA _)) ≤ 2 ^ k
  zv : Z ≤ V
  yv : Y ≤ V
  zy : ∀ x ∈ V, ∃ z ∈ Z, z⁻¹ * x ∈ Y
  zi : (S5.bSub h.le L (baseA _)).relIndex Z ≤ 2 ^ k
  ye : ⁅Y, E⁆ ≤ S5.bSub h.le L (baseA _)
  gen : V ≤ Z ⊔ ⁅V, puTrans h.le L (baseA _)⁆
  zt : k = 1 → ⁅Z, Qv _ (baseB (puAmalgam h.le))⁆ ≤ S5.bSub h.le L (baseA _)

namespace SecHyp

variable {h : PUHyp M T L} {V : Subgroup (puAmalgam h.le).Universal}
  (hn : SecHyp h V)
include hn

theorem le_normalizer_inf : stab _ (baseA (puAmalgam h.le)) ≤
    Subgroup.normalizer ((V ⊓ S5.bSub h.le L (baseA _) : Subgroup _) :
      Set (puAmalgam h.le).Universal) :=
  S310.le_normalizer_inf hn.vn (S310.stab_le_normalizer_bSub h _)

theorem exists_secMod : ∃ (S : Type) (_ : CommGroup S) (p : ↥V →* S)
    (ρ : ↥(stab (puAmalgam h.le) (baseA _)) →* MulAut S),
    S36E.SecData (stab _ (baseA (puAmalgam h.le))) V (V ⊓ S5.bSub h.le L (baseA _)) S p ρ :=
  S36E.exists_secMod inf_le_left hn.vn hn.le_normalizer_inf fun a ha a' ha' =>
    ⟨by
      rw [commutatorElement_def]
      exact V.mul_mem (V.mul_mem (V.mul_mem ha ha') (V.inv_mem ha)) (V.inv_mem ha'),
      hn.comm (Subgroup.commutator_mem_commutator ha ha')⟩

theorem le_qv : V ≤ Qv _ (baseA (puAmalgam h.le)) := hn.vv.trans (S310.vv_le_qv_baseA h hn.b)

theorem le_stab : V ≤ stab _ (baseA (puAmalgam h.le)) := hn.le_qv.trans (qv_le_stab _ _)

theorem finite_V : Finite ↥V :=
  have := S310.finite_stab_of_isMVtx h (isMVtx_baseA (puAmalgam h.le))
  Finite.of_injective _ (Subgroup.inclusion_injective hn.le_stab)

theorem exists_not_mem : ∃ v ∈ V, v ∉ S5.bSub h.le L (baseA _) := by
  by_contra hcon
  push Not at hcon
  exact hn.ne hcon

variable {S : Type} [CommGroup S] {p : ↥V →* S}
  {ρ : ↥(stab (puAmalgam h.le) (baseA _)) →* MulAut S}
  (hs : S36E.SecData (stab _ (baseA (puAmalgam h.le))) V (V ⊓ S5.bSub h.le L (baseA _)) S p ρ)
include hs

theorem sq_eq_one (s : S) : s ^ 2 = 1 := by
  obtain ⟨v, rfl⟩ := hs.surj s
  rw [← map_pow, hs.ker]
  exact ⟨by simpa using pow_mem v.2 2, by simpa using hn.sq v v.2⟩

theorem finite_S : Finite S :=
  have := hn.finite_V
  Finite.of_surjective _ hs.surj

theorem nontrivial_S : Nontrivial S := by
  obtain ⟨v, hv, hvB⟩ := hn.exists_not_mem
  refine ⟨⟨p ⟨v, hv⟩, 1, fun h1 => hvB ?_⟩⟩
  exact ((hs.ker ⟨v, hv⟩).1 h1).2

theorem eq_one_of_fixed (s : S) (hfix : ∀ l : ↥(stab (puAmalgam h.le) (baseA _)),
    (l : (puAmalgam h.le).Universal) ∈ puTrans h.le L (baseA _) → ρ l s = s) : s = 1 := by
  obtain ⟨v, rfl⟩ := hs.surj s
  have hvst : (v : (puAmalgam h.le).Universal) ∈ stab _ (baseA (puAmalgam h.le)) := hn.le_stab v.2
  have hB : ∀ l ∈ puTrans h.le L (baseA _), ⁅(v : (puAmalgam h.le).Universal), l⁆ ∈
      S5.bSub h.le L (baseA _) := by
    intro l hl
    have hlst : l ∈ stab _ (baseA (puAmalgam h.le)) := puTrans_le_stab h.le L _ hl
    have h1 := hfix ⟨l, hlst⟩ hl
    rw [hs.conj ⟨l, hlst⟩ v (S36E.conj_mem hn.vn hlst v.2), hs.eq_iff] at h1
    have h2 : ⁅l, (v : (puAmalgam h.le).Universal)⁆ ∈ S5.bSub h.le L (baseA _) := by
      rw [commutatorElement_def]
      exact h1.2
    rw [← commutatorElement_inv]
    exact inv_mem h2
  have hZ := commutator_mem_of_perfect (perfect_puTrans h)
    ((puTrans_le_stab h.le L _).trans (stab_le_normalizer_zm _ _))
    (Subgroup.commutator_le.2 fun x hx l hl =>
      S5B.commutator_mem_zm_of_mem_bSub h hn.b (isMVtx_baseA _) hx hl)
    (S310.stab_le_normalizer_bSub h _ hvst) (stab_le_normalizer_zm _ _ hvst) hB
  have hvB : (v : (puAmalgam h.le).Universal) ∈ S5.bSub h.le L (baseA _) :=
    Subgroup.subset_closure ⟨hn.vv v.2, hZ⟩
  exact (hs.ker v).2 ⟨v.2, hvB⟩

end SecHyp

namespace NatHyp

variable {h : PUHyp M T L} {k : ℕ} {V E Z Y : Subgroup (puAmalgam h.le).Universal}
  (hn : NatHyp h k V E Z Y)
  {S : Type} [CommGroup S] {p : ↥V →* S}
  {ρ : ↥(stab (puAmalgam h.le) (baseA _)) →* MulAut S}
  (hs : S36E.SecData (stab _ (baseA (puAmalgam h.le))) V (V ⊓ S5.bSub h.le L (baseA _)) S p ρ)
include hn hs

theorem rho_eq_one_of_mem_qv (g : ↥(stab (puAmalgam h.le) (baseA _)))
    (hg : (g : (puAmalgam h.le).Universal) ∈ Qv _ (baseA (puAmalgam h.le))) : ρ g = 1 := by
  refine (hs.rho_eq_one_iff g).2 fun v hv => ⟨?_, ?_⟩
  · exact V.mul_mem (S36E.conj_mem hn.vn g.2 hv) (V.inv_mem hv)
  · have h1 := Subgroup.commutator_mem_commutator hg hv
    rw [Subgroup.commutator_comm] at h1
    have h2 := hn.qv h1
    rwa [commutatorElement_def] at h2

theorem map_Y_le_fixV : (Y.subgroupOf V).map p ≤
    fixV ((E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map ρ) := by
  rintro _ ⟨y, hy, rfl⟩ _ ⟨e, he, rfl⟩
  have heY : (e : (puAmalgam h.le).Universal) ∈ E := Subgroup.mem_subgroupOf.1 he
  have hyY : (y : (puAmalgam h.le).Universal) ∈ Y := Subgroup.mem_subgroupOf.1 hy
  rw [hs.conj e y (S36E.conj_mem hn.vn e.2 y.2), hs.eq_iff]
  refine ⟨V.mul_mem (S36E.conj_mem hn.vn e.2 y.2) (V.inv_mem y.2), ?_⟩
  have h1 := Subgroup.commutator_mem_commutator heY hyY
  rw [Subgroup.commutator_comm] at h1
  have h2 := hn.ye h1
  rwa [commutatorElement_def] at h2

theorem map_Z_sup_map_Y : (Z.subgroupOf V).map p ⊔ (Y.subgroupOf V).map p = ⊤ := by
  rw [eq_top_iff]
  intro s _
  obtain ⟨x, rfl⟩ := hs.surj s
  obtain ⟨z, hz, hzy⟩ := hn.zy x x.2
  have hzV : z ∈ V := hn.zv hz
  have e : x = (⟨z, hzV⟩ : ↥V) * ⟨z⁻¹ * x, hn.yv hzy⟩ := Subtype.ext (by simp)
  rw [e, map_mul]
  exact Subgroup.mul_mem_sup ⟨_, Subgroup.mem_subgroupOf.2 hz, rfl⟩
    ⟨_, Subgroup.mem_subgroupOf.2 hzy, rfl⟩

theorem card_map_Z : Nat.card ((Z.subgroupOf V).map p) =
    (S5.bSub h.le L (baseA _)).relIndex Z := by
  have hker : p.ker = (V ⊓ S5.bSub h.le L (baseA _)).subgroupOf V := by
    ext a
    rw [MonoidHom.mem_ker, hs.ker, Subgroup.mem_subgroupOf]
  rw [← Subgroup.relIndex_ker, hker, Subgroup.relIndex_subgroupOf hn.zv,
    ← Subgroup.inf_relIndex_right, inf_assoc, inf_comm _ Z, ← inf_assoc,
    inf_eq_right.2 hn.zv, Subgroup.inf_relIndex_left]

theorem index_fixV_le :
    (fixV ((E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map ρ)).index ≤ 2 ^ k := by
  have := hn.toSecHyp.finite_S hs
  set PY := (Y.subgroupOf V).map p
  set PZ := (Z.subgroupOf V).map p
  have h1 : (fixV ((E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map ρ)).index ≤ PY.index :=
    Subgroup.index_antitone (hn.map_Y_le_fixV hs)
  have h2 : PY.index = PY.relIndex PZ := by
    rw [← Subgroup.relIndex_sup_left, sup_comm, hn.map_Z_sup_map_Y hs,
      Subgroup.relIndex_top_right]
  have h3 : PY.relIndex PZ ≤ Nat.card PZ := by
    have := Subgroup.relIndex_mul_card PY PZ
    have hpos : 0 < Nat.card ↥(PY ⊓ PZ) := Nat.card_pos
    calc PY.relIndex PZ ≤ PY.relIndex PZ * Nat.card ↥(PY ⊓ PZ) := Nat.le_mul_of_pos_right _ hpos
      _ = Nat.card PZ := this
  calc _ ≤ PY.index := h1
    _ = PY.relIndex PZ := h2
    _ ≤ Nat.card PZ := h3
    _ = (S5.bSub h.le L (baseA _)).relIndex Z := hn.card_map_Z hs
    _ ≤ 2 ^ k := hn.zi

end NatHyp

end Hyp

end S512N

end CFSG.Quasithin.MS93
