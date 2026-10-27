module

public import CFSG.Quasithin.EmptyFaithful.E111RDiag
public import CFSG.Quasithin.EmptyFaithful.E111RComp
public import CFSG.Quasithin.EmptyFaithful.E111RFam
public import CFSG.Quasithin.Vol2.Ch11SecE3L0

public section

namespace CFSG.Quasithin.E2.E22N.E111R

open CFSG.Open CFSG.Quasithin.A1b CFSG.Quasithin.Vol2.Ch11.SecB

variable {G : Type} [Group G]

@[expose] noncomputable def diagSub (S C : Subgroup G) [Fintype ↥C] (hC : DiagComm S C) :
    Subgroup G :=
  (diagHom S C hC).range

theorem card_conjSub (g : G) (H : Subgroup G) : Nat.card ↥(A1b.conjSub g H) = Nat.card ↥H := by
  unfold A1b.conjSub
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

@[expose] def diagFam (T A S C : Subgroup G) [Fintype ↥C] (hC : DiagComm S C) :
    Set (Subgroup G) :=
  Set.range fun g : ↥(T ⊓ Subgroup.centralizer (A : Set G)) =>
    A1b.conjSub (g : G) (diagSub S C hC)

structure DiagSetting (X T A S C : Subgroup G) : Prop where
  red : E111Reduced G X T
  AT : A ≤ T
  elem : IsElemAbelian 2 A
  comp : IsComp X S
  CA : C ≤ A
  CV : C ⊓ (A ⊓ Subgroup.normalizer (S : Set G)) = ⊥

namespace DiagSetting

variable {X T A S C : Subgroup G} (h : DiagSetting X T A S C)
include h

theorem comm {a b : G} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a :=
  congrArg Subtype.val (h.elem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem conj_ne {c c' : G} (hc : c ∈ C) (hc' : c' ∈ C) (hne : c ≠ c') :
    A1b.conjSub c S ≠ A1b.conjSub c' S := by
  intro heq
  apply hne
  have hn : c'⁻¹ * c ∈ Subgroup.normalizer (S : Set G) := by
    apply mem_normalizer_of_conjSub_eq
    rw [A1b.conjSub_mul, heq, ← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one]
  have hCv : c'⁻¹ * c ∈ C ⊓ (A ⊓ Subgroup.normalizer (S : Set G)) :=
    ⟨C.mul_mem (C.inv_mem hc') hc, A.mul_mem (A.inv_mem (h.CA hc')) (h.CA hc), hn⟩
  rw [h.CV, Subgroup.mem_bot] at hCv
  calc c = c' * (c'⁻¹ * c) := (mul_inv_cancel_left c' c).symm
    _ = c' := by rw [hCv, mul_one]

theorem diagComm : DiagComm S C := by
  intro c hc c' hc' hne x hx y hy
  rcases (h.comp.conj h.red.1 c).eq_or_commute (h.comp.conj h.red.1 c') with heq | hcomm
  · exact absurd heq (h.conj_ne hc hc' hne)
  · exact hcomm _ (A1b.mem_conjSub_of_mem hx) _ (A1b.mem_conjSub_of_mem hy)

theorem commute_of_ne {g : G}
    (hg : ∀ c ∈ C, ∀ c' ∈ C, A1b.conjSub (g * c) S ≠ A1b.conjSub c' S) :
    ∀ c ∈ C, ∀ c' ∈ C, ∀ x ∈ S, ∀ y ∈ S,
      Commute (g * c * x * (g * c)⁻¹) ((c' : G) * y * c'⁻¹) := by
  intro c hc c' hc' x hx y hy
  rcases (h.comp.conj h.red.1 (g * c)).eq_or_commute (h.comp.conj h.red.1 c') with heq | hcomm
  · exact absurd heq (hg c hc c' hc')
  · exact hcomm _ (A1b.mem_conjSub_of_mem hx) _ (A1b.mem_conjSub_of_mem hy)

theorem center_trivial : ∀ x ∈ S, x ∈ Subgroup.centralizer (S : Set G) → x = 1 := by
  intro x hx hxc
  have := h.comp.simple
  have hZ := Vol2.Ch11.SecE3.center_eq_bot_of_simple h.comp.nonabelian
  have hc : (⟨x, hx⟩ : ↥S) ∈ Subgroup.center ↥S :=
    Subgroup.mem_center_iff.mpr fun y => Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc y y.2)
  rw [hZ, Subgroup.mem_bot] at hc
  exact congrArg Subtype.val hc

variable [Fintype ↥C]

noncomputable def diagEquiv : ↥S ≃* ↥(diagSub S C h.diagComm) :=
  MonoidHom.ofInjective (diagHom_injective h.diagComm h.center_trivial)

theorem diag_simple : IsSimpleGroup ↥(diagSub S C h.diagComm) := by
  have := h.comp.simple
  exact (MulEquiv.isSimpleGroup_congr h.diagEquiv).mp this

theorem diag_nonabelian : ∃ a b : ↥(diagSub S C h.diagComm), a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h.comp.nonabelian
  refine ⟨h.diagEquiv a, h.diagEquiv b, fun he => hab (h.diagEquiv.injective ?_)⟩
  rw [map_mul, map_mul]
  exact he

theorem diag_le : diagSub S C h.diagComm ≤ X := by
  rintro _ ⟨x, rfl⟩
  exact diagHom_mem h.diagComm h.comp.le (fun c _ y hy => h.red.1.conj_mem y hy c) x

theorem le_centralizer_diag : C ≤ Subgroup.centralizer (diagSub S C h.diagComm : Set G) := by
  intro c hc
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨x, rfl⟩
  have := conj_diagHom_of_mem h.diagComm x hc
  calc diagHom S C h.diagComm x * c = c * diagHom S C h.diagComm x * c⁻¹ * c := by rw [this]
    _ = c * diagHom S C h.diagComm x := by group

theorem exists_diag (x : G) (hx : x ∈ S) :
    ∃ y ∈ diagSub S C h.diagComm, x⁻¹ * y ∈ Subgroup.centralizer (S : Set G) :=
  ⟨diagHom S C h.diagComm ⟨x, hx⟩, ⟨_, rfl⟩, inv_mul_diagHom_mem h.diagComm ⟨x, hx⟩⟩

theorem conjSub_diag_of_comm [Finite G] {k : G} (hkS : k ∈ Subgroup.normalizer (S : Set G))
    (hkC : ∀ c ∈ C, k * c = c * k) :
    A1b.conjSub k (diagSub S C h.diagComm) = diagSub S C h.diagComm := by
  have hle : A1b.conjSub k (diagSub S C h.diagComm) ≤ diagSub S C h.diagComm := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    have := conj_diagHom_of_comm h.diagComm x hkS hkC
    exact ⟨_, this.symm⟩
  exact Subgroup.eq_of_le_of_card_ge hle (card_conjSub k _).ge

theorem conjSub_diag_of_mem [Finite G] {c : G} (hc : c ∈ C) :
    A1b.conjSub c (diagSub S C h.diagComm) = diagSub S C h.diagComm :=
  conjSub_eq_of_mem_normalizer
    (Subgroup.centralizer_le_normalizer _ (h.le_centralizer_diag hc))

theorem eq_or_commute_conj [Finite G] {k : G} (hk : k ∈ Subgroup.centralizer (A : Set G)) :
    A1b.conjSub k (diagSub S C h.diagComm) = diagSub S C h.diagComm ∨
      ∀ x ∈ A1b.conjSub k (diagSub S C h.diagComm), ∀ y ∈ diagSub S C h.diagComm,
        x * y = y * x := by
  have hkc : ∀ c ∈ C, k * c = c * k := fun c hc =>
    (Subgroup.mem_centralizer_iff.mp hk c (h.CA hc)).symm
  by_cases hex : ∃ c ∈ C, ∃ c' ∈ C, A1b.conjSub (k * c) S = A1b.conjSub c' S
  · left
    obtain ⟨c, hc, c', hc', heq⟩ := hex
    set m := c'⁻¹ * (k * c) with hm
    have hmS : m ∈ Subgroup.normalizer (S : Set G) := by
      apply mem_normalizer_of_conjSub_eq
      rw [hm, A1b.conjSub_mul, heq, ← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one]
    have hmC : ∀ d ∈ C, m * d = d * m := by
      intro d hd
      have h1 := h.comm (h.CA (C.inv_mem hc')) (h.CA hd)
      have h2 := hkc d hd
      have h3 := h.comm (h.CA hc) (h.CA hd)
      calc m * d = c'⁻¹ * (k * (c * d)) := by rw [hm]; group
        _ = c'⁻¹ * ((k * d) * c) := by rw [h3]; group
        _ = c'⁻¹ * ((d * k) * c) := by rw [h2]
        _ = (c'⁻¹ * d) * (k * c) := by group
        _ = (d * c'⁻¹) * (k * c) := by rw [h1]
        _ = d * m := by rw [hm]; group
    have hkm : k = c' * m * c⁻¹ := by rw [hm]; group
    rw [hkm, A1b.conjSub_mul, A1b.conjSub_mul, h.conjSub_diag_of_mem (C.inv_mem hc),
      h.conjSub_diag_of_comm hmS hmC, h.conjSub_diag_of_mem hc']
  · right
    push Not at hex
    have hcomm := commute_conj_diagHom h.diagComm (h.commute_of_ne fun c hc c' hc' =>
      hex c hc c' hc')
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩ _ ⟨y, rfl⟩
    exact hcomm x y

theorem semiFam [Finite G] : SemiFam (diagFam T A S C h.diagComm) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨g, rfl⟩
    have := h.diag_simple
    exact (MulEquiv.isSimpleGroup_congr (Subgroup.equivMapOfInjective _ _
      (MulAut.conj (g : G)).injective)).mp this
  · rintro _ ⟨g, rfl⟩
    obtain ⟨a, b, hab⟩ := h.diag_nonabelian
    set e := Subgroup.equivMapOfInjective (diagSub S C h.diagComm)
      (MulAut.conj (g : G)).toMonoidHom (MulAut.conj (g : G)).injective
    refine ⟨e a, e b, fun he => hab (e.injective ?_)⟩
    rw [map_mul, map_mul]
    exact he
  · rintro _ ⟨g, rfl⟩ _ ⟨g', rfl⟩ hne
    have hk : (g' : G)⁻¹ * g ∈ Subgroup.centralizer (A : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ g'.2.2) g.2.2
    rcases h.eq_or_commute_conj hk with heq | hcomm
    · exfalso
      apply hne
      dsimp only
      rw [show (g : G) = g' * ((g' : G)⁻¹ * g) by group, A1b.conjSub_mul, heq]
    · intro x hx y hy
      dsimp only at hx hy
      rw [A1b.mem_conjSub_iff] at hx hy
      have hx' : (g' : G)⁻¹ * x * g' ∈ A1b.conjSub ((g' : G)⁻¹ * g) (diagSub S C h.diagComm) := by
        rw [A1b.mem_conjSub_iff]
        simpa [mul_assoc] using hx
      have h1 := hcomm _ hx' _ hy
      have h2 : (g' : G) * ((g' : G)⁻¹ * x * g' * ((g' : G)⁻¹ * y * g')) * (g' : G)⁻¹ =
          (g' : G) * ((g' : G)⁻¹ * y * g' * ((g' : G)⁻¹ * x * g')) * (g' : G)⁻¹ := by
        rw [h1]
      simpa [mul_assoc] using h2

end DiagSetting

end CFSG.Quasithin.E2.E22N.E111R
