module

public import CFSG.Quasithin.Recognition.GoldschmidtBasic

public section

open Monoid

universe u v

namespace CFSG.Quasithin

namespace GoldAmalgam

variable {A C B : Type*} [Group A] [Group C] [Group B]

@[expose] def commonNormalCore (X : GoldAmalgam A C B) : Subgroup C :=
  ⨆ K : {K : Subgroup C // (K.map X.toA).Normal ∧ (K.map X.toB).Normal}, K.1

theorem le_commonNormalCore {X : GoldAmalgam A C B} {K : Subgroup C}
    (hA : (K.map X.toA).Normal) (hB : (K.map X.toB).Normal) : K ≤ X.commonNormalCore :=
  le_iSup (fun K : {K : Subgroup C // (K.map X.toA).Normal ∧ (K.map X.toB).Normal} => K.1)
    ⟨K, hA, hB⟩

theorem commonNormalCore_map_toA_normal (X : GoldAmalgam A C B) :
    (X.commonNormalCore.map X.toA).Normal := by
  unfold commonNormalCore
  rw [Subgroup.map_iSup]
  have : ∀ K : {K : Subgroup C // (K.map X.toA).Normal ∧ (K.map X.toB).Normal},
      (K.1.map X.toA).Normal := fun K => K.2.1
  infer_instance

theorem commonNormalCore_map_toB_normal (X : GoldAmalgam A C B) :
    (X.commonNormalCore.map X.toB).Normal := by
  unfold commonNormalCore
  rw [Subgroup.map_iSup]
  have : ∀ K : {K : Subgroup C // (K.map X.toA).Normal ∧ (K.map X.toB).Normal},
      (K.1.map X.toB).Normal := fun K => K.2.2
  infer_instance

theorem isFaithful_iff_commonNormalCore_eq_bot (X : GoldAmalgam A C B) :
    X.IsFaithful ↔ X.commonNormalCore = ⊥ := by
  constructor
  · intro h
    exact h _ X.commonNormalCore_map_toA_normal X.commonNormalCore_map_toB_normal
  · intro h K hA hB
    exact le_bot_iff.mp (h ▸ X.le_commonNormalCore hA hB)

structure GoldCompletion (X : GoldAmalgam A C B) (D : Type*) [Group D] where
  ψA : A →* D
  ψB : B →* D
  ψA_injective : Function.Injective ψA
  ψB_injective : Function.Injective ψB
  comm : ∀ c, ψA (X.toA c) = ψB (X.toB c)
  gen : ψA.range ⊔ ψB.range = ⊤
  inter : ψA.range ⊓ ψB.range ≤ (ψA.comp X.toA).range

namespace GoldCompletion

variable {X : GoldAmalgam A C B} {D : Type*} [Group D] (Φ : GoldCompletion X D)

@[expose] def edge : Subgroup D := (Φ.ψA.comp X.toA).range

theorem edge_eq_inf : Φ.edge = Φ.ψA.range ⊓ Φ.ψB.range := by
  refine le_antisymm (le_inf ?_ ?_) Φ.inter
  · rintro _ ⟨c, rfl⟩
    exact ⟨X.toA c, rfl⟩
  · rintro _ ⟨c, rfl⟩
    exact ⟨X.toB c, (Φ.comm c).symm⟩

theorem relIndex_range_eq_edgeA_index : Φ.ψB.range.relIndex Φ.ψA.range = X.edgeA.index := by
  rw [← Subgroup.inf_relIndex_left (H := Φ.ψA.range) (K := Φ.ψB.range), ← Φ.edge_eq_inf]
  have hmap : Φ.edge = X.edgeA.map Φ.ψA := by
    unfold GoldCompletion.edge GoldAmalgam.edgeA
    rw [MonoidHom.range_comp]
  have := Subgroup.relIndex_map_map_of_injective X.edgeA ⊤ Φ.ψA_injective
  rw [Subgroup.map_top, Subgroup.relIndex_top_right] at this
  rw [hmap]
  exact this

theorem relIndex_range_eq_edgeB_index : Φ.ψA.range.relIndex Φ.ψB.range = X.edgeB.index := by
  rw [← Subgroup.inf_relIndex_left (H := Φ.ψB.range) (K := Φ.ψA.range), inf_comm, ← Φ.edge_eq_inf]
  have hmap : Φ.edge = X.edgeB.map Φ.ψB := by
    unfold GoldCompletion.edge GoldAmalgam.edgeB
    have : Φ.ψA.comp X.toA = Φ.ψB.comp X.toB := MonoidHom.ext Φ.comm
    rw [this, MonoidHom.range_comp]
  have := Subgroup.relIndex_map_map_of_injective X.edgeB ⊤ Φ.ψB_injective
  rw [Subgroup.map_top, Subgroup.relIndex_top_right] at this
  rw [hmap]
  exact this

theorem card_edge : Nat.card Φ.edge = Nat.card C := by
  have hinj : Function.Injective (Φ.ψA.comp X.toA) := Φ.ψA_injective.comp X.toA_injective
  exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm

theorem range_le_normalizer_map {A' D' : Type*} [Group A'] [Group D'] (f : A' →* D')
    (M : Subgroup A') [hM : M.Normal] :
    f.range ≤ Subgroup.normalizer ((M.map f : Subgroup D') : Set D') := by
  rintro _ ⟨a, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨a * m * a⁻¹, hM.conj_mem m hm a, by simp⟩
  · rintro ⟨m, hm, hmh⟩
    refine ⟨a⁻¹ * m * a, by simpa using hM.conj_mem m hm a⁻¹, ?_⟩
    have : f m = f a * h * (f a)⁻¹ := hmh
    simp [this, mul_assoc]

theorem map_comp_toA_eq_map_comp_toB (K : Subgroup C) :
    K.map (Φ.ψA.comp X.toA) = K.map (Φ.ψB.comp X.toB) := by
  have : Φ.ψA.comp X.toA = Φ.ψB.comp X.toB := MonoidHom.ext Φ.comm
  rw [this]

theorem normal_map_iff (K : Subgroup C) :
    ((K.map X.toA).Normal ∧ (K.map X.toB).Normal) ↔ (K.map (Φ.ψA.comp X.toA)).Normal := by
  have hN : K.map (Φ.ψA.comp X.toA) = (K.map X.toA).map Φ.ψA := by
    rw [Subgroup.map_map]
  have hNB : K.map (Φ.ψA.comp X.toA) = (K.map X.toB).map Φ.ψB := by
    rw [Φ.map_comp_toA_eq_map_comp_toB, Subgroup.map_map]
  constructor
  · rintro ⟨hA, hB⟩
    refine Subgroup.normalizer_eq_top_iff.mp ?_
    rw [eq_top_iff, ← Φ.gen]
    refine sup_le ?_ ?_
    · rw [hN]
      exact range_le_normalizer_map Φ.ψA _
    · rw [hNB]
      exact range_le_normalizer_map Φ.ψB _
  · intro h
    refine ⟨?_, ?_⟩
    · have : K.map X.toA = (K.map (Φ.ψA.comp X.toA)).comap Φ.ψA := by
        rw [hN]
        exact (Subgroup.comap_map_eq_self_of_injective Φ.ψA_injective _).symm
      rw [this]
      exact h.comap _
    · have : K.map X.toB = (K.map (Φ.ψA.comp X.toA)).comap Φ.ψB := by
        rw [hNB]
        exact (Subgroup.comap_map_eq_self_of_injective Φ.ψB_injective _).symm
      rw [this]
      exact h.comap _

theorem isFaithful_iff :
    X.IsFaithful ↔ ∀ N : Subgroup D, N.Normal → N ≤ Φ.edge → N = ⊥ := by
  constructor
  · intro hf N hN hle
    have hmap : (N.comap (Φ.ψA.comp X.toA)).map (Φ.ψA.comp X.toA) = N :=
      Subgroup.map_comap_eq_self hle
    have hnorm : ((N.comap (Φ.ψA.comp X.toA)).map X.toA).Normal ∧
        ((N.comap (Φ.ψA.comp X.toA)).map X.toB).Normal := by
      rw [Φ.normal_map_iff, hmap]
      exact hN
    have hbot := hf _ hnorm.1 hnorm.2
    rw [← hmap, hbot, Subgroup.map_bot]
  · intro h K hA hB
    have hnorm : (K.map (Φ.ψA.comp X.toA)).Normal := (Φ.normal_map_iff K).mp ⟨hA, hB⟩
    have hle : K.map (Φ.ψA.comp X.toA) ≤ Φ.edge := Subgroup.map_le_range _ _
    have hbot := h _ hnorm hle
    have hinj : Function.Injective (Φ.ψA.comp X.toA) := Φ.ψA_injective.comp X.toA_injective
    exact Subgroup.map_injective hinj (by rw [hbot, Subgroup.map_bot])

end GoldCompletion

section Kernel

variable {X : GoldAmalgam A C B} {D : Type*} [Group D] (Φ : GoldCompletion X D)

namespace GoldCompletion

theorem normalCore_inf_eq (H K : Subgroup D) :
    (H ⊓ K).normalCore = H.normalCore ⊓ K.normalCore := by
  refine le_antisymm (le_inf (Subgroup.normalCore_mono inf_le_left)
    (Subgroup.normalCore_mono inf_le_right)) ?_
  have : (H.normalCore ⊓ K.normalCore).Normal := inferInstance
  exact Subgroup.normal_le_normalCore.mpr (inf_le_inf H.normalCore_le K.normalCore_le)

theorem ker_inf_ker_eq_normalCore_edge :
    (MulAction.toPermHom D (D ⧸ Φ.ψA.range)).ker ⊓ (MulAction.toPermHom D (D ⧸ Φ.ψB.range)).ker =
      Φ.edge.normalCore := by
  rw [← Subgroup.normalCore_eq_ker, ← Subgroup.normalCore_eq_ker, ← normalCore_inf_eq,
    Φ.edge_eq_inf]

theorem commonNormalCore_eq_comap_normalCore :
    X.commonNormalCore = Φ.edge.normalCore.comap (Φ.ψA.comp X.toA) := by
  apply le_antisymm
  · have hnorm := (Φ.normal_map_iff _).mp
      ⟨X.commonNormalCore_map_toA_normal, X.commonNormalCore_map_toB_normal⟩
    have hle : X.commonNormalCore.map (Φ.ψA.comp X.toA) ≤ Φ.edge.normalCore := by
      rw [Subgroup.normal_le_normalCore]
      exact Subgroup.map_le_range _ _
    exact Subgroup.map_le_iff_le_comap.mp hle
  · have hmap : (Φ.edge.normalCore.comap (Φ.ψA.comp X.toA)).map (Φ.ψA.comp X.toA) =
        Φ.edge.normalCore := Subgroup.map_comap_eq_self Φ.edge.normalCore_le
    have hnorm : ((Φ.edge.normalCore.comap (Φ.ψA.comp X.toA)).map X.toA).Normal ∧
        ((Φ.edge.normalCore.comap (Φ.ψA.comp X.toA)).map X.toB).Normal := by
      rw [Φ.normal_map_iff, hmap]
      exact Subgroup.normalCore_normal _
    exact X.le_commonNormalCore hnorm.1 hnorm.2

theorem isFaithful_iff_ker_inf_ker_eq_bot :
    X.IsFaithful ↔
      (MulAction.toPermHom D (D ⧸ Φ.ψA.range)).ker ⊓
        (MulAction.toPermHom D (D ⧸ Φ.ψB.range)).ker = ⊥ := by
  rw [Φ.ker_inf_ker_eq_normalCore_edge, X.isFaithful_iff_commonNormalCore_eq_bot,
    Φ.commonNormalCore_eq_comap_normalCore]
  constructor
  · intro h
    have hmap : (Φ.edge.normalCore.comap (Φ.ψA.comp X.toA)).map (Φ.ψA.comp X.toA) =
        Φ.edge.normalCore := Subgroup.map_comap_eq_self Φ.edge.normalCore_le
    rw [← hmap, h, Subgroup.map_bot]
  · intro h
    have hinj : Function.Injective (Φ.ψA.comp X.toA) := Φ.ψA_injective.comp X.toA_injective
    rw [h, MonoidHom.comap_bot, (MonoidHom.ker_eq_bot_iff _).mpr hinj]

end GoldCompletion

end Kernel

end GoldAmalgam

section Universal

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B]

abbrev goldVertexGroup (A B : Type u) : Bool → Type u := fun b => cond b A B

instance goldVertexGroup.instGroup : ∀ b : Bool, Group (goldVertexGroup A B b)
  | true => ‹Group A›
  | false => ‹Group B›

namespace GoldAmalgam

@[expose] def diagram (X : GoldAmalgam A C B) : ∀ b : Bool, C →* goldVertexGroup A B b
  | true => X.toA
  | false => X.toB

theorem diagram_injective (X : GoldAmalgam A C B) : ∀ b, Function.Injective (X.diagram b)
  | true => X.toA_injective
  | false => X.toB_injective

abbrev Universal (X : GoldAmalgam A C B) : Type max u v := PushoutI X.diagram

@[expose] def ofA (X : GoldAmalgam A C B) : A →* X.Universal :=
  PushoutI.of (φ := X.diagram) true

@[expose] def ofB (X : GoldAmalgam A C B) : B →* X.Universal :=
  PushoutI.of (φ := X.diagram) false

theorem ofA_injective (X : GoldAmalgam A C B) : Function.Injective X.ofA :=
  PushoutI.of_injective X.diagram_injective true

theorem ofB_injective (X : GoldAmalgam A C B) : Function.Injective X.ofB :=
  PushoutI.of_injective X.diagram_injective false

theorem ofA_toA (X : GoldAmalgam A C B) (c : C) :
    X.ofA (X.toA c) = PushoutI.base X.diagram c :=
  PushoutI.of_apply_eq_base X.diagram true c

theorem ofB_toB (X : GoldAmalgam A C B) (c : C) :
    X.ofB (X.toB c) = PushoutI.base X.diagram c :=
  PushoutI.of_apply_eq_base X.diagram false c

theorem ofA_range_inf_ofB_range (X : GoldAmalgam A C B) :
    X.ofA.range ⊓ X.ofB.range = (PushoutI.base X.diagram).range :=
  PushoutI.inf_of_range_eq_base_range X.diagram_injective (by decide : (true : Bool) ≠ false)

theorem ofA_range_sup_ofB_range (X : GoldAmalgam A C B) : X.ofA.range ⊔ X.ofB.range = ⊤ := by
  rw [eq_top_iff]
  intro x _
  induction x using PushoutI.induction_on with
  | of i g =>
    cases i
    · exact Subgroup.mem_sup_right ⟨g, rfl⟩
    · exact Subgroup.mem_sup_left ⟨g, rfl⟩
  | base h =>
    exact Subgroup.mem_sup_left ⟨X.toA h, X.ofA_toA h⟩
  | mul x y hx hy => exact mul_mem (hx trivial) (hy trivial)

@[expose] def universalCompletion (X : GoldAmalgam A C B) : GoldCompletion X X.Universal where
  ψA := X.ofA
  ψB := X.ofB
  ψA_injective := X.ofA_injective
  ψB_injective := X.ofB_injective
  comm c := by rw [X.ofA_toA, X.ofB_toB]
  gen := X.ofA_range_sup_ofB_range
  inter := by
    rw [X.ofA_range_inf_ofB_range]
    rintro _ ⟨c, rfl⟩
    exact ⟨c, X.ofA_toA c⟩

end GoldAmalgam

end Universal

end CFSG.Quasithin
