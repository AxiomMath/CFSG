module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aOvergroupSp
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.TwoReduced

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L14328

variable {G : Type} [Group G]

theorem mem_conj_iff {X : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate X g ↔ g * x * g⁻¹ ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by simp [mul_assoc]⟩

theorem conjugate_normalizer (X : Subgroup G) (h : G) :
    CFSG.conjugate (Subgroup.normalizer (X : Set G)) h =
      Subgroup.normalizer (CFSG.conjugate X h : Set G) := by
  ext y
  rw [mem_conj_iff, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro H m
    rw [mem_conj_iff, mem_conj_iff]
    have := H (h * m * h⁻¹)
    rw [show h * y * h⁻¹ * (h * m * h⁻¹) * (h * y * h⁻¹)⁻¹ = h * (y * m * y⁻¹) * h⁻¹ by group]
      at this
    exact this
  · intro H n
    have := H (h⁻¹ * n * h)
    rw [mem_conj_iff, mem_conj_iff,
      show h * (h⁻¹ * n * h) * h⁻¹ = n by group,
      show h * (y * (h⁻¹ * n * h) * y⁻¹) * h⁻¹ = h * y * h⁻¹ * n * (h * y * h⁻¹)⁻¹ by group]
      at this
    exact this

theorem conjugate_centralizer (X : Subgroup G) (h : G) :
    CFSG.conjugate (Subgroup.centralizer (X : Set G)) h =
      Subgroup.centralizer (CFSG.conjugate X h : Set G) := by
  ext y
  rw [mem_conj_iff, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro H m hm
    rw [SetLike.mem_coe, mem_conj_iff] at hm
    have := H _ hm
    calc m * y = h⁻¹ * ((h * m * h⁻¹) * (h * y * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * y * h⁻¹) * (h * m * h⁻¹)) * h := by rw [this]
      _ = y * m := by group
  · intro H n hn
    have hn' : h⁻¹ * n * h ∈ (CFSG.conjugate X h : Set G) := by
      rw [SetLike.mem_coe, mem_conj_iff]
      simpa [mul_assoc] using hn
    have := H _ hn'
    calc n * (h * y * h⁻¹) = h * ((h⁻¹ * n * h) * y) * h⁻¹ := by group
      _ = h * (y * (h⁻¹ * n * h)) * h⁻¹ := by rw [this]
      _ = h * y * h⁻¹ * n := by group

theorem conjugate_inf (X Y : Subgroup G) (h : G) :
    CFSG.conjugate (X ⊓ Y) h = CFSG.conjugate X h ⊓ CFSG.conjugate Y h := by
  ext y
  simp only [Subgroup.mem_inf, mem_conj_iff]

theorem conjugate_centerOf (X : Subgroup G) (h : G) :
    CFSG.conjugate (centerOf X) h = centerOf (CFSG.conjugate X h) := by
  rw [centerOf, conjugate_inf, conjugate_centralizer]
  rfl

theorem conjugate_conjClosure (X N : Subgroup G) (h : G) :
    CFSG.conjugate (conjClosure X N) h = conjClosure (CFSG.conjugate X h) (CFSG.conjugate N h) := by
  apply le_antisymm
  · intro y hy
    rw [mem_conj_iff] at hy
    have key : ∀ w ∈ conjClosure X N,
        h⁻¹ * w * h ∈ conjClosure (CFSG.conjugate X h) (CFSG.conjugate N h) := by
      intro w hw
      induction hw using Subgroup.closure_induction with
      | mem w hw =>
        obtain ⟨n, hn, x, hx, rfl⟩ := hw
        have hn' : h⁻¹ * n * h ∈ CFSG.conjugate N h := by
          rw [mem_conj_iff]
          simpa [mul_assoc] using hn
        have hx' : h⁻¹ * x * h ∈ CFSG.conjugate X h := by
          rw [mem_conj_iff]
          simpa [mul_assoc] using hx
        rw [show h⁻¹ * (n * x * n⁻¹) * h = (h⁻¹ * n * h) * (h⁻¹ * x * h) * (h⁻¹ * n * h)⁻¹ by
          group]
        exact mem_conjClosure hn' hx'
      | one => simp
      | mul w w' _ _ ih ih' =>
        rw [show h⁻¹ * (w * w') * h = (h⁻¹ * w * h) * (h⁻¹ * w' * h) by group]
        exact Subgroup.mul_mem _ ih ih'
      | inv w _ ih =>
        rw [show h⁻¹ * w⁻¹ * h = (h⁻¹ * w * h)⁻¹ by group]
        exact Subgroup.inv_mem _ ih
    have := key _ hy
    simpa [mul_assoc] using this
  · refine conjClosure_le fun n hn x hx => ?_
    rw [mem_conj_iff] at hn hx ⊢
    rw [show h * (n * x * n⁻¹) * h⁻¹ = (h * n * h⁻¹) * (h * x * h⁻¹) * (h * n * h⁻¹)⁻¹ by group]
    exact mem_conjClosure hn hx

end L14328

end CFSG.Quasithin.H13
