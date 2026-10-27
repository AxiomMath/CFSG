module

public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.GF2n

open CFSG.CGT.Timmesfeld75
open scoped Pointwise

variable {G : Type*} [Group G]

theorem card_conjSubgroup (g : G) (T : Subgroup G) :
    Nat.card (conjSubgroup g T) = Nat.card T :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem conjSubgroup_mul (g h : G) (T : Subgroup G) :
    conjSubgroup (g * h) T = conjSubgroup g (conjSubgroup h T) := by
  ext x
  simp only [mem_conjSubgroup]
  rw [show (g * h)⁻¹ * x * (g * h) = h⁻¹ * (g⁻¹ * x * g) * h by group]

theorem conjSubgroup_one (T : Subgroup G) : conjSubgroup 1 T = T := by
  ext x
  simp [mem_conjSubgroup]

theorem conjSubgroup_inf (g : G) (U V : Subgroup G) :
    conjSubgroup g (U ⊓ V) = conjSubgroup g U ⊓ conjSubgroup g V :=
  Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective

theorem conjSubgroup_eq_self_iff {g : G} {T : Subgroup G} :
    conjSubgroup g T = T ↔ g ∈ Subgroup.normalizer (T : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rfl

theorem isTI_conjSubgroup {T : Subgroup G} (h : IsTI T) (g : G) : IsTI (conjSubgroup g T) := by
  intro k
  have e : conjSubgroup k (conjSubgroup g T) =
      conjSubgroup g (conjSubgroup (g⁻¹ * k * g) T) := by
    rw [← conjSubgroup_mul, ← conjSubgroup_mul]
    congr 1
    group
  rw [e, ← conjSubgroup_inf]
  rcases h (g⁻¹ * k * g) with hk | hk
  · left
    rw [hk]
    exact Subgroup.map_bot _
  · right
    rw [hk]

theorem conjSubgroup_eq_of_isTI [Finite G] {T : Subgroup G} (h : IsTI T) {g : G}
    (hne : T ⊓ conjSubgroup g T ≠ ⊥) : conjSubgroup g T = T := by
  rcases h g with h' | h'
  · exact absurd h' hne
  · have hle : T ≤ conjSubgroup g T := calc
      T = T ⊓ conjSubgroup g T := h'.symm
      _ ≤ conjSubgroup g T := inf_le_right
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])).symm

theorem inf_conjSubgroup_eq_bot_of_isTI [Finite G] {T : Subgroup G} (h : IsTI T) {g : G}
    (hne : conjSubgroup g T ≠ T) : T ⊓ conjSubgroup g T = ⊥ := by
  by_contra h'
  exact hne (conjSubgroup_eq_of_isTI h h')

theorem le_normalizer_map_subtype (H : Subgroup G) (N : Subgroup H) [N.Normal] :
    H ≤ Subgroup.normalizer ((N.map H.subtype : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨h, hh⟩ * y * ⟨h, hh⟩⁻¹, Subgroup.Normal.conj_mem inferInstance y hy _, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    refine ⟨⟨h, hh⟩⁻¹ * y * ⟨h, hh⟩, ?_, ?_⟩
    · simpa using Subgroup.Normal.conj_mem inferInstance y hy (⟨h, hh⟩⁻¹ : H)
    · have : (y : G) = h * x * h⁻¹ := hyx
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, this]
      group

theorem mem_normalizer_map_subtype_of_characteristic {Q : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) (A : Subgroup Q) [hA : A.Characteristic] :
    g ∈ Subgroup.normalizer ((A.map Q.subtype : Subgroup G) : Set G) := by
  have key : ∀ c : G, c ∈ Subgroup.normalizer (Q : Set G) →
      ∀ x ∈ A.map Q.subtype, c * x * c⁻¹ ∈ A.map Q.subtype := by
    intro c hc x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    let φ : MulAut Q := Q.normalizerMonoidHom ⟨c, hc⟩
    have hφ : φ y ∈ A := by
      have h := hA.fixed φ
      have : y ∈ A.comap φ.toMonoidHom := by rw [h]; exact hy
      exact this
    exact Subgroup.mem_map.mpr ⟨φ y, hφ, rfl⟩
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hx
  simpa [mul_assoc] using this

theorem mem_normalizer_inSubgroup_frattini {P : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G)) :
    g ∈ Subgroup.normalizer ((inSubgroup frattini P : Subgroup G) : Set G) :=
  mem_normalizer_map_subtype_of_characteristic hg (frattini P)

theorem mem_normalizer_sup {E F : Subgroup G} {g : G}
    (hE : g ∈ Subgroup.normalizer (E : Set G)) (hF : g ∈ Subgroup.normalizer (F : Set G)) :
    g ∈ Subgroup.normalizer ((E ⊔ F : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hE hF ⊢
  rw [Subgroup.map_sup, hE, hF]

theorem mem_normalizer_inf {E F : Subgroup G} {g : G}
    (hE : g ∈ Subgroup.normalizer (E : Set G)) (hF : g ∈ Subgroup.normalizer (F : Set G)) :
    g ∈ Subgroup.normalizer ((E ⊓ F : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hE hF ⊢
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective, hE, hF]

theorem mem_normalizer_centralizer {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (H : Set G) : Set G) := by
  have key : ∀ c : G, c ∈ Subgroup.normalizer (H : Set G) →
      ∀ x ∈ Subgroup.centralizer (H : Set G), c * x * c⁻¹ ∈ Subgroup.centralizer (H : Set G) := by
    intro c hc x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro h hh
    have hh' : c⁻¹ * h * c ∈ H := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hc) h).mp hh
      simpa using this
    have := hx _ hh'
    calc h * (c * x * c⁻¹) = c * ((c⁻¹ * h * c) * x) * c⁻¹ := by group
      _ = c * (x * (c⁻¹ * h * c)) * c⁻¹ := by rw [this]
      _ = c * x * c⁻¹ * h := by group
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hx
  simpa [mul_assoc] using this

theorem le_normalizer_of_comm {X N : Subgroup G} (h : ∀ x ∈ X, ∀ y ∈ N, x * y = y * x) :
    X ≤ Subgroup.normalizer (N : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [h x hx y hy, mul_inv_cancel_right]
    exact hy
  · intro hy
    have h1 := h x hx _ hy
    have : y = x * y * x⁻¹ := by
      calc y = x⁻¹ * ((x * y * x⁻¹) * x) := by group
        _ = x⁻¹ * (x * (x * y * x⁻¹)) := by rw [← h1]
        _ = x * y * x⁻¹ := by group
    rw [this]
    exact hy

theorem exists_mul_of_mem_sup {V U : Subgroup G} (hUV : U ≤ Subgroup.normalizer (V : Set G))
    {x : G} (hx : x ∈ V ⊔ U) : ∃ v ∈ V, ∃ u ∈ U, x = v * u := by
  have hx' : x ∈ (V : Set G) * (U : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left V U hUV]
    exact hx
  obtain ⟨v, hv, u, hu, rfl⟩ := hx'
  exact ⟨v, hv, u, hu, rfl⟩

theorem inSubgroup_pCore_two (M : Subgroup G) :
    IsPGroup 2 (inSubgroup (pCore 2) M) ∧ inSubgroup (pCore 2) M ≤ M ∧
      M ≤ Subgroup.normalizer ((inSubgroup (pCore 2) M : Subgroup G) : Set G) :=
  ⟨IsPGroup.map (pCore_isPGroup (p := 2) (G := M)) M.subtype, Subgroup.map_subtype_le _,
    le_normalizer_map_subtype M (pCore 2 M)⟩

end CFSG.RankThree.GF2n
