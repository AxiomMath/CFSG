module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F7
public import CFSG.Quasithin.Background.Harris.R1.QbetaA

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.SzR1
  CFSG.Quasithin.F7

namespace QD

variable {G : Type*} [Group G] [Finite G] {P S Q W Z M D : Subgroup G} {g y z : G}

theorem conjSub_inv_eq (h : QD P S Q W Z M D g y z) (hSM : S ≤ Subgroup.normalizer (M : Set G)) :
    conjSub g⁻¹ M = conjSub g M := by
  have e : g⁻¹ = g * (g * g)⁻¹ := by group
  rw [e, conjSub_mul, conjSub_eq_of_mem_normalizer (hSM (S.inv_mem h.hgg))]

theorem D_inf_conjSub_inv_le_Z (h : QD P S Q W Z M D g y z)
    (hSM : S ≤ Subgroup.normalizer (M : Set G)) : D ⊓ conjSub g⁻¹ M ≤ Z := by
  rw [h.conjSub_inv_eq hSM]
  exact h.D_inf_conjSub_M_le_Z

theorem Q_le_normalizer_conjSub (h : QD P S Q W Z M D g y z) :
    Q ≤ Subgroup.normalizer ((conjSub g D : Subgroup G) : Set G) :=
  calc Q = conjSub g Q := (conjSub_eq_of_mem_normalizer (h.vh.qn h.hg)).symm
    _ ≤ conjSub g S := conjSub_mono g h.vh.qs
    _ ≤ Subgroup.normalizer ((conjSub g D : Subgroup G) : Set G) :=
      conjSub_le_normalizer h.hDS

theorem conjSub_D_le_Q (h : QD P S Q W Z M D g y z) : conjSub g D ≤ Q :=
  calc conjSub g D ≤ conjSub g Q := conjSub_mono g h.D_le_Q
    _ = Q := conjSub_eq_of_mem_normalizer (h.vh.qn h.hg)

theorem commute_D_conjSub (h : QD P S Q W Z M D g y z) (hSM : S ≤ Subgroup.normalizer (M : Set G)) :
    ∀ d ∈ D, ∀ e ∈ conjSub g D, d * e = e * d := by
  intro d hd e he
  have hdN : d ∈ Subgroup.normalizer ((conjSub g D : Subgroup G) : Set G) :=
    h.Q_le_normalizer_conjSub (h.D_le_Q hd)
  have heN : e ∈ Subgroup.normalizer (D : Set G) := h.hDS (h.vh.qs (h.conjSub_D_le_Q he))
  set c := d * e * d⁻¹ * e⁻¹ with hc
  have hcE : c ∈ conjSub g D :=
    (conjSub g D).mul_mem ((Subgroup.mem_normalizer_iff.mp hdN e).mp he) ((conjSub g D).inv_mem he)
  have hcD : c ∈ D := by
    have h1 : e * d⁻¹ * e⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp heN d⁻¹).mp (D.inv_mem hd)
    have e1 : c = d * (e * d⁻¹ * e⁻¹) := by rw [hc]; group
    rw [e1]
    exact D.mul_mem hd h1
  have hcM : c ∈ conjSub g M := conjSub_mono g h.hD hcE
  have hcZ : c ∈ Z := h.D_inf_conjSub_M_le_Z ⟨hcD, hcM⟩
  have hc' : g⁻¹ * c * g ∈ D := mem_conjSub.mp hcE
  have hc'M : g⁻¹ * c * g ∈ conjSub g M := by
    rw [mem_conjSub]
    have e2 : g⁻¹ * (g⁻¹ * c * g) * g = (g * g)⁻¹ * c * (g * g) := by group
    rw [e2]
    have hgg : g * g ∈ S := h.hgg
    have := (Subgroup.mem_normalizer_iff.mp (hSM (S.inv_mem hgg)) c).mp (h.hD hcD)
    simpa using this
  have hc'Z : g⁻¹ * c * g ∈ Z := h.D_inf_conjSub_M_le_Z ⟨hc', hc'M⟩
  have hcZg : c ∈ conjSub g Z := mem_conjSub.mpr hc'Z
  have h1 : c ∈ Z ⊓ conjSub g Z := ⟨hcZ, hcZg⟩
  rw [h.hZZ, Subgroup.mem_bot] at h1
  have e3 : d * e = e * d := by
    have : d * e * d⁻¹ * e⁻¹ = 1 := h1
    calc d * e = (d * e * d⁻¹ * e⁻¹) * (e * d) := by group
      _ = e * d := by rw [this, one_mul]
  exact e3

theorem D_le_Z_of_conjSub_le (h : QD P S Q W Z M D g y z) (hSM : S ≤ Subgroup.normalizer (M : Set G))
    (hM : conjSub g D ≤ M) : D ≤ Z := by
  intro x hx
  have hxm : x ∈ conjSub g⁻¹ M := by
    rw [mem_conjSub]
    have := hM (mul_mem_conjSub (g := g) hx)
    simpa using this
  exact h.D_inf_conjSub_inv_le_Z hSM ⟨hx, hxm⟩

end QD

end CFSG.Quasithin.Background.Harris.R1
