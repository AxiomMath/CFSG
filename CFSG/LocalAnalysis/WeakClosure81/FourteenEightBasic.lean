module

public import CFSG.LocalAnalysis.WeakClosure81.FourteenSeven
public import CFSG.LocalAnalysis.WeakClosure81.SixFourShape

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def IsFixedPointFreeTorus (M V : Subgroup G) (g : G) (Y : Subgroup G) : Prop :=
  IsRegularTorus M V g Y ∧ ∀ y ∈ Y, y ≠ 1 → ∀ v ∈ V, y * v * y⁻¹ = v → v ∈ NOf M V g

@[expose] def TorusData {Q : Type*} [Group Q] (A : Subgroup Q) (g₀ : Q) (T : Subgroup Q) :
    Prop :=
  IsCyclic ↥T ∧ Nat.card T = Nat.card A - 1 ∧ T ≤ normalizer (A : Set Q) ∧
    T ≤ normalizer (conjSubgroup A g₀ : Set Q) ∧
    (∀ a ∈ A, a ≠ 1 → ∀ b ∈ A, b ≠ 1 → ∃ t ∈ T, t * a * t⁻¹ = b) ∧
    (∀ t ∈ T, ∀ a ∈ A, a ≠ 1 → t * a * t⁻¹ = a → t = 1) ∧
    ∀ t ∈ T, t ≠ 1 → ∃ c : Q, ∃ s₁ ∈ conjSubgroup A c,
      ∃ s₂ ∈ conjSubgroup (conjSubgroup A g₀) c, s₁ ≠ 1 ∧ s₂ ≠ 1 ∧ t = s₁ * s₂

variable {n : ℕ} {M V₀ V : Subgroup G} {g : G}

theorem s148_W148Basic_conj_eq_of_mem_NOf_of_mem_L (h : Hyp64 n M V₀ V g) {x e : G}
    (hxL : x ∈ LOf V g) (he : e ∈ NOf M V g) : x * e * x⁻¹ = e := by
  have hc := NOf_le_centralizer_L h he
  have hcomm := Subgroup.mem_centralizer_iff.1 hc x hxL
  rw [hcomm]; group

theorem s148_W148Basic_sup_le_L (h : Hyp64 n M V₀ V g) :
    UOf M V g ⊔ BOf M V g ≤ LOf V g :=
  sup_le (fun _ hu => Subgroup.mem_sup_left hu.1)
    (fun _ hb => Subgroup.mem_sup_right hb.1)

theorem s148_W148Basic_L_le_normalizer (h : Hyp64 n M V₀ V g) :
    LOf V g ≤ Subgroup.normalizer ((UOf M V g ⊔ BOf M V g : Subgroup G) : Set G) := by
  obtain ⟨K, hK, hLK, -, -, -⟩ := inCalOStar_K_facts h
  rw [hK] at hLK
  exact hLK

theorem s148_W148Basic_conj_mem_sup (h : Hyp64 n M V₀ V g) {x l : G}
    (hlL : l ∈ LOf V g) (hx : x ∈ UOf M V g ⊔ BOf M V g) :
    l * x * l⁻¹ ∈ UOf M V g ⊔ BOf M V g :=
  (Subgroup.mem_normalizer_iff.1 (s148_W148Basic_L_le_normalizer h hlL) x).1 hx

theorem s148_W148Basic_S_mul (h : Hyp64 n M V₀ V g) {f x z : G}
    (hxL : x ∈ LOf V g) (hzL : z ∈ LOf V g)
    (hx : ⁅x, f⁆ ∈ NOf M V g) (hz : ⁅z, f⁆ ∈ NOf M V g) :
    ⁅x * z, f⁆ ∈ NOf M V g := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  rw [s148_W148Basic_conj_eq_of_mem_NOf_of_mem_L h hxL hz]
  exact (NOf M V g).mul_mem hz hx

theorem s148_W148Basic_S_inv (h : Hyp64 n M V₀ V g) {f x : G} (hxL : x ∈ LOf V g)
    (hx : ⁅x, f⁆ ∈ NOf M V g) : ⁅x⁻¹, f⁆ ∈ NOf M V g := by
  have hfx : ⁅f, x⁆ ∈ NOf M V g := by
    rw [← commutatorElement_inv]
    exact (NOf M V g).inv_mem hx
  rw [commutatorElement_inv_left]
  have h := s148_W148Basic_conj_eq_of_mem_NOf_of_mem_L h ((LOf V g).inv_mem hxL) hfx
  rw [inv_inv] at h
  rwa [h]

theorem s148_W148Basic_F_mul (h : Hyp64 n M V₀ V g) {y f₁ f₂ : G}
    (hf₁L : f₁ ∈ LOf V g) (hf₂L : f₂ ∈ LOf V g)
    (h₁ : ⁅y, f₁⁆ ∈ NOf M V g) (h₂ : ⁅y, f₂⁆ ∈ NOf M V g) :
    ⁅y, f₁ * f₂⁆ ∈ NOf M V g := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  rw [show ⁅y, f₁⁆ * f₁ * ⁅y, f₂⁆ * f₁⁻¹
        = ⁅y, f₁⁆ * (f₁ * ⁅y, f₂⁆ * f₁⁻¹) from by group]
  rw [s148_W148Basic_conj_eq_of_mem_NOf_of_mem_L h hf₁L h₂]
  exact (NOf M V g).mul_mem h₁ h₂

theorem s148_W148Basic_F_inv (h : Hyp64 n M V₀ V g) {y f : G} (hfL : f ∈ LOf V g)
    (hfy : ⁅y, f⁆ ∈ NOf M V g) : ⁅y, f⁻¹⁆ ∈ NOf M V g := by
  have hfy' : ⁅f, y⁆ ∈ NOf M V g := by
    rw [← commutatorElement_inv]
    exact (NOf M V g).inv_mem hfy
  rw [commutatorElement_inv_right]
  have h := s148_W148Basic_conj_eq_of_mem_NOf_of_mem_L h ((LOf V g).inv_mem hfL) hfy'
  rw [inv_inv] at h
  rwa [h]

theorem s148_W148Basic_mem_NOf_of_commutator_mem (h : Hyp64 n M V₀ V g)
    (hgen : GenHyp M V g) {t₁ t₂ f : G} (ht₁ : t₁ ∈ V) (ht₁U : t₁ ∉ UOf M V g)
    (ht₂ : t₂ ∈ conjSubgroup V g) (ht₂B : t₂ ∉ BOf M V g)
    (hfK : f ∈ UOf M V g ⊔ BOf M V g)
    (h₁ : ⁅t₁, f⁆ ∈ NOf M V g) (h₂ : ⁅t₂, f⁆ ∈ NOf M V g) :
    f ∈ NOf M V g := by
  have hU : f ∈ UOf M V g :=
    stepB h hgen ht₁ ht₁U f hfK (by
      rw [← commutatorElement_inv t₁ f]
      exact (NOf M V g).inv_mem h₁)
  have hB : f ∈ BOf M V g :=
    stepA h hgen ht₂ ht₂B f hfK (by
      rw [← commutatorElement_inv t₂ f]
      exact (NOf M V g).inv_mem h₂)
  exact Subgroup.mem_inf.2 ⟨hU, hB⟩

theorem UOf_ne (h : Hyp64 n M V₀ V g) : UOf M V g ≠ V := by
  intro hUV
  exact h.inCalOStar.1.2.1 ((le_of_eq hUV.symm).trans (by simp [UOf]))

theorem mul_self_mem_NOf (h : Hyp64 n M V₀ V g) {k : G} (hk : k ∈ UOf M V g ⊔ BOf M V g) :
    k * k ∈ NOf M V g := by
  have hUB : UOf M V g ≤ Subgroup.normalizer (BOf M V g : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    exact (commutator_U_B_le_N h).trans inf_le_right
  change k ∈ (↑(UOf M V g ⊔ BOf M V g) : Set G) at hk
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (UOf M V g) (BOf M V g) hUB] at hk
  obtain ⟨u, huU, b, hbB, rfl⟩ := hk
  have hu2 : u⁻¹ = u :=
    inv_eq_of_mul_eq_one_right (IsElemAbelian.mul_self_eq_one h.elemAbelian huU.1)
  have hb2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right
    (IsElemAbelian.mul_self_eq_one (E3.isElemAbelian_conjSubgroup h.elemAbelian g) hbB.1)
  have hkk : (u * b) * (u * b) = ⁅u, b⁆ := by
    rw [commutatorElement_def]
    rw [hu2, hb2]
    group
  rw [hkk]
  exact commutator_U_B_le_N h (Subgroup.commutator_mem_commutator huU hbB)

theorem commutatorElement_mem_NOf (h : Hyp64 n M V₀ V g) {k₁ k₂ : G}
    (hk₁ : k₁ ∈ UOf M V g ⊔ BOf M V g) (hk₂ : k₂ ∈ UOf M V g ⊔ BOf M V g) :
    ⁅k₁, k₂⁆ ∈ NOf M V g := by
  have hVgel : IsElemAbelian 2 (conjSubgroup V g) :=
    E3.isElemAbelian_conjSubgroup h.elemAbelian g
  have hUB : UOf M V g ≤ Subgroup.normalizer (BOf M V g : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    exact (commutator_U_B_le_N h).trans inf_le_right
  have hk₁' : k₁ ∈ (↑(UOf M V g) : Set G) * (↑(BOf M V g) : Set G) := by
    change k₁ ∈ (↑(UOf M V g ⊔ BOf M V g) : Set G) at hk₁
    rwa [Subgroup.coe_mul_of_left_le_normalizer_right (UOf M V g) (BOf M V g) hUB] at hk₁
  obtain ⟨u₁, hu₁, b₁, hb₁, rfl⟩ := hk₁'
  have hk₂' : k₂ ∈ (↑(UOf M V g) : Set G) * (↑(BOf M V g) : Set G) := by
    change k₂ ∈ (↑(UOf M V g ⊔ BOf M V g) : Set G) at hk₂
    rwa [Subgroup.coe_mul_of_left_le_normalizer_right (UOf M V g) (BOf M V g) hUB] at hk₂
  obtain ⟨u₂, hu₂, b₂, hb₂, rfl⟩ := hk₂'
  have hb : ⁅b₁, u₂ * b₂⁆ ∈ NOf M V g := by
    have hb₁b₂ : ⁅b₁, b₂⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 (IsElemAbelian.comm hVgel hb₁.1 hb₂.1)
    have hb₁u₂ : ⁅b₁, u₂⁆ ∈ NOf M V g := by
      have h1 : ⁅u₂, b₁⁆ ∈ NOf M V g :=
        commutator_U_B_le_N h (Subgroup.commutator_mem_commutator hu₂ hb₁)
      rw [← commutatorElement_inv] at h1
      exact (NOf M V g).inv_mem_iff.1 h1
    have heq : ⁅b₁, u₂ * b₂⁆ = ⁅b₁, u₂⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj, hb₁b₂]
      group
    rw [heq]
    exact hb₁u₂
  have hu : ⁅u₁, u₂ * b₂⁆ ∈ NOf M V g := by
    have hu₁u₂ : ⁅u₁, u₂⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 (IsElemAbelian.comm h.elemAbelian hu₁.1 hu₂.1)
    have hu₁b₂ : ⁅u₁, b₂⁆ ∈ NOf M V g :=
      commutator_U_B_le_N h (Subgroup.commutator_mem_commutator hu₁ hb₂)
    have heq : ⁅u₁, u₂ * b₂⁆ = ⁅u₁, b₂⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj, hu₁u₂, one_mul]
      exact s148_W148Basic_conj_eq_of_mem_NOf_of_mem_L h
        (Subgroup.mem_sup_left hu₂.1) hu₁b₂
    rw [heq]
    exact hu₁b₂
  rw [commutatorElement_mul_left_eq_conj_mul]
  rw [s148_W148Basic_conj_eq_of_mem_NOf_of_mem_L h (Subgroup.mem_sup_left hu₁.1) hb]
  exact (NOf M V g).mul_mem hb hu

theorem isPGroup_UOf_sup_BOf (h : Hyp64 n M V₀ V g) :
    IsPGroup 2 ↥(UOf M V g ⊔ BOf M V g) := by
  intro k
  refine ⟨2, ?_⟩
  apply Subtype.ext
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  have hkV : (k : G) * (k : G) ∈ V := by
    have h := (Subgroup.mem_inf.1 (mul_self_mem_NOf h k.2)).1
    unfold UOf at h
    exact h.1
  have h4 : (k : G) ^ (2 : ℕ) ^ 2 = 1 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, show (4 : ℕ) = 2 + 2 by norm_num, pow_add,
      pow_two]
    exact IsElemAbelian.mul_self_eq_one h.elemAbelian hkV
  exact h4

theorem mem_M_of_mem_normalizer_sup (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g) {x : G}
    (hxL : x ∈ LOf V g)
    (hx : x ∈ normalizer ((V ⊔ (UOf M V g ⊔ BOf M V g) : Subgroup G) : Set G)) :
    x ∈ M := by
  have hK : LOf V g ≤ Subgroup.normalizer ((UOf M V g ⊔ BOf M V g : Subgroup G) : Set G) :=
    s148_W148Basic_L_le_normalizer h
  have hxK : conjSubgroup (UOf M V g ⊔ BOf M V g) x = UOf M V g ⊔ BOf M V g :=
    conjSubgroup_eq_iff_mem_normalizer.2 (hK hxL)
  have hxVK : conjSubgroup (V ⊔ (UOf M V g ⊔ BOf M V g)) x
      = V ⊔ (UOf M V g ⊔ BOf M V g) :=
    conjSubgroup_eq_iff_mem_normalizer.2 hx
  rw [conjSubgroup_sup, hxK] at hxVK
  have hxV : conjSubgroup V x = V :=
    conjSubgroup_V_eq_of_sup_eq_of_ne h hgen (UOf_ne h) hxL hxVK
  rw [← h.normalizer_eq]
  exact conjSubgroup_eq_iff_mem_normalizer.1 hxV

theorem mem_conjM_of_mem_normalizer_sup (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g) {x : G}
    (hxL : x ∈ LOf V g)
    (hx : x ∈ normalizer ((conjSubgroup V g ⊔ (UOf M V g ⊔ BOf M V g) : Subgroup G) : Set G)) :
    x ∈ conjSubgroup M g := by
  have hK : LOf V g ≤ Subgroup.normalizer ((UOf M V g ⊔ BOf M V g : Subgroup G) : Set G) :=
    s148_W148Basic_L_le_normalizer h
  have hxK : conjSubgroup (UOf M V g ⊔ BOf M V g) x = UOf M V g ⊔ BOf M V g :=
    conjSubgroup_eq_iff_mem_normalizer.2 (hK hxL)
  obtain ⟨K, hK, hLK, hlK, hcomm, hKset⟩ := inCalOStar_K_facts h
  obtain ⟨l, hlL, hlV⟩ := hlK
  have hxVgK : conjSubgroup (conjSubgroup V g ⊔ (UOf M V g ⊔ BOf M V g)) x
      = conjSubgroup V g ⊔ (UOf M V g ⊔ BOf M V g) :=
    conjSubgroup_eq_iff_mem_normalizer.2 hx
  rw [conjSubgroup_sup, hxK] at hxVgK
  have hwL : l * x ∈ LOf V g := (LOf V g).mul_mem hlL hxL
  have hwV : conjSubgroup V (l * x) = conjSubgroup (conjSubgroup V g) x := by
    rw [← conjSubgroup_conjSubgroup V l x, ← hlV]
  have hwK : conjSubgroup V (l * x) ⊔ (UOf M V g ⊔ BOf M V g)
      = conjSubgroup V g ⊔ (UOf M V g ⊔ BOf M V g) := by
    rw [hwV]
    exact hxVgK
  have hVw := conjSubgroup_V_eq_conjSubgroup_V_of_sup_eq_of_ne h hgen (UOf_ne h) hwL hwK
  have hconj : conjSubgroup (conjSubgroup V g) x = conjSubgroup V g := hwV ▸ hVw
  have hxN : x ∈ Subgroup.normalizer (conjSubgroup V g : Set G) :=
    conjSubgroup_eq_iff_mem_normalizer.1 hconj
  rw [← E3.conjSubgroup_normalizer V g, h.normalizer_eq] at hxN
  exact hxN

theorem mem_NOf_of_conj_mul_inv_mem (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g)
    {t₁ t₂ y : G} (ht₁ : t₁ ∈ V) (ht₁U : t₁ ∉ UOf M V g) (ht₂ : t₂ ∈ conjSubgroup V g)
    (ht₂B : t₂ ∉ BOf M V g) (hy : (t₁ * t₂)⁻¹ * y ∈ UOf M V g ⊔ BOf M V g) {k : G}
    (hk : k ∈ UOf M V g ⊔ BOf M V g) (hyk : y * k * y⁻¹ * k⁻¹ ∈ NOf M V g) :
    k ∈ NOf M V g := by
  have hLK := s148_W148Basic_L_le_normalizer h
  have hKL := s148_W148Basic_sup_le_L h
  have ht₁L : t₁ ∈ LOf V g := Subgroup.mem_sup_left ht₁
  have ht₂L : t₂ ∈ LOf V g := Subgroup.mem_sup_right ht₂
  have ht₁2 : t₁ * t₁ = 1 := IsElemAbelian.mul_self_eq_one h.elemAbelian ht₁
  have ht₂2 : t₂ * t₂ = 1 :=
    IsElemAbelian.mul_self_eq_one (E3.isElemAbelian_conjSubgroup h.elemAbelian g) ht₂
  have ht₁inv : t₁⁻¹ = t₁ := inv_eq_of_mul_eq_one_right ht₁2
  have ht₂inv : t₂⁻¹ = t₂ := inv_eq_of_mul_eq_one_right ht₂2
  obtain ⟨k₀, hk₀, hy_eq⟩ : ∃ k₀ : G,
      k₀ ∈ UOf M V g ⊔ BOf M V g ∧ y = t₁ * t₂ * k₀ :=
    ⟨(t₁ * t₂)⁻¹ * y, hy, by group⟩
  have hk₀L : k₀ ∈ LOf V g := hKL hk₀
  have hyL : y ∈ LOf V g := by
    rw [hy_eq]
    exact (LOf V g).mul_mem ((LOf V g).mul_mem ht₁L ht₂L) hk₀L
  have hkF : ⁅y, k⁆ ∈ NOf M V g := by rw [commutatorElement_def]; exact hyk
  have hkey : t₁ * (t₁ * y * t₁⁻¹) * t₁⁻¹ = y := by
    rw [ht₁inv]
    calc t₁ * (t₁ * y * t₁) * t₁ = (t₁ * t₁) * y * (t₁ * t₁) := by group
      _ = y := by rw [ht₁2, one_mul, mul_one]
  have hconjF : ∀ f : G, f ∈ UOf M V g ⊔ BOf M V g → ⁅y, f⁆ ∈ NOf M V g →
      ⁅y, t₁ * f * t₁⁻¹⁆ ∈ NOf M V g := by
    intro f hfK hyf
    have hyy'K : y * (t₁ * y * t₁⁻¹) ∈ UOf M V g ⊔ BOf M V g := by
      have h₁ : t₂ * k₀ * t₂ ∈ UOf M V g ⊔ BOf M V g := by
        simpa only [ht₂inv] using s148_W148Basic_conj_mem_sup h ht₂L hk₀
      have h₂ : t₁ * (t₂ * k₀ * t₂) * t₁⁻¹ ∈ UOf M V g ⊔ BOf M V g :=
        s148_W148Basic_conj_mem_sup h ht₁L h₁
      have h₃ : t₁ * k₀ * t₁⁻¹ ∈ UOf M V g ⊔ BOf M V g :=
        s148_W148Basic_conj_mem_sup h ht₁L hk₀
      have hL : y * (t₁ * y * t₁⁻¹)
          = t₁ * t₂ * k₀ * t₂ * k₀ * t₁ := by
        rw [hy_eq, ht₁inv]
        calc (t₁ * t₂ * k₀) * (t₁ * (t₁ * t₂ * k₀) * t₁)
            = t₁ * t₂ * k₀ * (t₁ * t₁) * t₂ * k₀ * t₁ := by group
          _ = t₁ * t₂ * k₀ * t₂ * k₀ * t₁ := by rw [ht₁2, mul_one]
      have hR : (t₁ * (t₂ * k₀ * t₂) * t₁⁻¹) * (t₁ * k₀ * t₁⁻¹)
          = t₁ * t₂ * k₀ * t₂ * k₀ * t₁ := by
        rw [ht₁inv]
        calc (t₁ * (t₂ * k₀ * t₂) * t₁) * (t₁ * k₀ * t₁)
            = t₁ * t₂ * k₀ * t₂ * (t₁ * t₁) * k₀ * t₁ := by group
          _ = t₁ * t₂ * k₀ * t₂ * k₀ * t₁ := by rw [ht₁2, mul_one]
      rw [hL, ← hR]
      exact (UOf M V g ⊔ BOf M V g).mul_mem h₂ h₃
    have hy'L : t₁ * y * t₁⁻¹ ∈ LOf V g :=
      (LOf V g).mul_mem ((LOf V g).mul_mem ht₁L hyL) ((LOf V g).inv_mem ht₁L)
    have hy'f : ⁅t₁ * y * t₁⁻¹, f⁆ ∈ NOf M V g := by
      have h1 : ⁅y⁻¹, f⁆ ∈ NOf M V g := s148_W148Basic_S_inv h hyL hyf
      have h2 : ⁅y * (t₁ * y * t₁⁻¹), f⁆ ∈ NOf M V g :=
        commutatorElement_mem_NOf h hyy'K hfK
      have hy'eq : t₁ * y * t₁⁻¹ = y⁻¹ * (y * (t₁ * y * t₁⁻¹)) := by group
      rw [hy'eq]
      exact s148_W148Basic_S_mul h ((LOf V g).inv_mem hyL) ((LOf V g).mul_mem hyL hy'L) h1 h2
    have hident : ⁅y, t₁ * f * t₁⁻¹⁆ = t₁ * ⁅t₁ * y * t₁⁻¹, f⁆ * t₁⁻¹ := by
      conv_lhs => rw [← hkey]
      exact (conjugate_commutatorElement (t₁ * y * t₁⁻¹) f t₁).symm
    rw [hident]
    rw [s148_W148Basic_conj_eq_of_mem_NOf_of_mem_L h ht₁L hy'f]
    exact hy'f
  have hF_mul : ∀ f₁ f₂ : G, f₁ ∈ UOf M V g ⊔ BOf M V g →
      f₂ ∈ UOf M V g ⊔ BOf M V g → ⁅y, f₁⁆ ∈ NOf M V g → ⁅y, f₂⁆ ∈ NOf M V g →
      ⁅y, f₁ * f₂⁆ ∈ NOf M V g := by
    intro f₁ f₂ hf₁ hf₂ h₁ h₂
    exact s148_W148Basic_F_mul h (hKL hf₁) (hKL hf₂) h₁ h₂
  have hF_inv : ∀ f : G, f ∈ UOf M V g ⊔ BOf M V g → ⁅y, f⁆ ∈ NOf M V g →
      ⁅y, f⁻¹⁆ ∈ NOf M V g := by
    intro f hf hfy
    exact s148_W148Basic_F_inv h (hKL hf) hfy
  by_contra hkE
  by_cases hcase : ⁅t₁, k⁆ ∈ NOf M V g
  · have ht₂k : ⁅t₂, k⁆ ∈ NOf M V g := by
      have h1 : ⁅t₁⁻¹, k⁆ ∈ NOf M V g := s148_W148Basic_S_inv h ht₁L hcase
      have h3 : ⁅k₀⁻¹, k⁆ ∈ NOf M V g :=
        s148_W148Basic_S_inv h hk₀L (commutatorElement_mem_NOf h hk₀ hk)
      have h12 : ⁅t₁⁻¹ * y, k⁆ ∈ NOf M V g :=
        s148_W148Basic_S_mul h ((LOf V g).inv_mem ht₁L) hyL h1 hkF
      have ht₂eq : t₂ = t₁⁻¹ * y * k₀⁻¹ := by rw [hy_eq]; group
      rw [ht₂eq]
      exact s148_W148Basic_S_mul h ((LOf V g).mul_mem ((LOf V g).inv_mem ht₁L) hyL)
        ((LOf V g).inv_mem hk₀L) h12 h3
    exact absurd (s148_W148Basic_mem_NOf_of_commutator_mem h hgen ht₁ ht₁U ht₂ ht₂B hk
      hcase ht₂k) hkE
  · set f : G := (t₁ * k * t₁⁻¹) * k⁻¹ with hfdef
    have hfK : f ∈ UOf M V g ⊔ BOf M V g := by
      rw [hfdef]
      exact (UOf M V g ⊔ BOf M V g).mul_mem
        (s148_W148Basic_conj_mem_sup h ht₁L hk) ((UOf M V g ⊔ BOf M V g).inv_mem hk)
    have hfE : f ∉ NOf M V g := by
      rw [hfdef, ← commutatorElement_def]
      exact hcase
    have ht₁f : ⁅t₁, f⁆ ∈ NOf M V g := by
      have hc : k * (t₁ * k⁻¹ * t₁⁻¹) ∈ UOf M V g ⊔ BOf M V g :=
        (UOf M V g ⊔ BOf M V g).mul_mem hk
          (s148_W148Basic_conj_mem_sup h ht₁L ((UOf M V g ⊔ BOf M V g).inv_mem hk))
      have hcc : (k * (t₁ * k⁻¹ * t₁⁻¹)) * (k * (t₁ * k⁻¹ * t₁⁻¹)) ∈ NOf M V g :=
        mul_self_mem_NOf h hc
      have heq : ⁅t₁, f⁆
          = (k * (t₁ * k⁻¹ * t₁⁻¹)) * (k * (t₁ * k⁻¹ * t₁⁻¹)) := by
        rw [hfdef, commutatorElement_def, ht₁inv]
        rw [show ((t₁ * k * t₁) * k⁻¹)⁻¹ = k * (t₁ * k⁻¹ * t₁) from by
          simp only [mul_inv_rev, inv_inv, ht₁inv, mul_assoc]]
        calc t₁ * ((t₁ * k * t₁) * k⁻¹) * t₁ * (k * (t₁ * k⁻¹ * t₁))
            = (t₁ * t₁) * k * t₁ * k⁻¹ * t₁ * k * (t₁ * k⁻¹ * t₁) := by group
          _ = (k * (t₁ * k⁻¹ * t₁)) * (k * (t₁ * k⁻¹ * t₁)) := by
                rw [ht₁2, one_mul]; group
      rw [heq]
      exact hcc
    have hyf : ⁅y, f⁆ ∈ NOf M V g := by
      have h1 : ⁅y, t₁ * k * t₁⁻¹⁆ ∈ NOf M V g := hconjF k hk hkF
      have h2 : ⁅y, k⁻¹⁆ ∈ NOf M V g := hF_inv k hk hkF
      have h3 : ⁅y, (t₁ * k * t₁⁻¹) * k⁻¹⁆ ∈ NOf M V g :=
        hF_mul (t₁ * k * t₁⁻¹) k⁻¹ (s148_W148Basic_conj_mem_sup h ht₁L hk)
          ((UOf M V g ⊔ BOf M V g).inv_mem hk) h1 h2
      rw [hfdef]
      exact h3
    have ht₂f : ⁅t₂, f⁆ ∈ NOf M V g := by
      have h1 : ⁅t₁⁻¹, f⁆ ∈ NOf M V g := s148_W148Basic_S_inv h ht₁L ht₁f
      have h3 : ⁅k₀⁻¹, f⁆ ∈ NOf M V g :=
        s148_W148Basic_S_inv h hk₀L (commutatorElement_mem_NOf h hk₀ hfK)
      have h12 : ⁅t₁⁻¹ * y, f⁆ ∈ NOf M V g :=
        s148_W148Basic_S_mul h ((LOf V g).inv_mem ht₁L) hyL h1 hyf
      have ht₂eq : t₂ = t₁⁻¹ * y * k₀⁻¹ := by rw [hy_eq]; group
      rw [ht₂eq]
      exact s148_W148Basic_S_mul h ((LOf V g).mul_mem ((LOf V g).inv_mem ht₁L) hyL)
        ((LOf V g).inv_mem hk₀L) h12 h3
    exact absurd (s148_W148Basic_mem_NOf_of_commutator_mem h hgen ht₁ ht₁U ht₂ ht₂B hfK
      ht₁f ht₂f) hfE

theorem isFixedPointFreeTorus_bot (h2 : (UOf M V g).relIndex V = 2) :
    IsFixedPointFreeTorus M V g ⊥ := by
  constructor
  · refine ⟨bot_le, ?_, inferInstance, ?_⟩
    · rw [Subgroup.card_bot, E3.mQuot, h2, padicValNat_self]
      norm_num
    · intro v hv hvU w hw hwU
      refine ⟨1, Subgroup.mem_bot.2 rfl, ?_⟩
      simp only [one_mul, inv_one, mul_one]
      have hindex : ((UOf M V g).subgroupOf V).index = 2 := h2
      have hv' : (⟨v, hv⟩ : ↥V) ∉ (UOf M V g).subgroupOf V :=
        fun hmem => hvU (Subgroup.mem_subgroupOf.1 hmem)
      have hw' : (⟨w, hw⟩ : ↥V)⁻¹ ∉ (UOf M V g).subgroupOf V := by
        intro hmem
        exact hwU ((UOf M V g).inv_mem_iff.1 (Subgroup.mem_subgroupOf.1 hmem))
      have hmem : (⟨v, hv⟩ : ↥V) * (⟨w, hw⟩ : ↥V)⁻¹ ∈ (UOf M V g).subgroupOf V := by
        rw [Subgroup.mul_mem_iff_of_index_two hindex]
        exact ⟨fun h => absurd h hv', fun h => absurd h hw'⟩
      simpa using Subgroup.mem_subgroupOf.1 hmem
  · intro y hy hy1
    exact absurd (Subgroup.mem_bot.1 hy) hy1

end CFSG.LocalAnalysis.WeakClosure81
