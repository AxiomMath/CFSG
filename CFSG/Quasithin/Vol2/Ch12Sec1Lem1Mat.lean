module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1FF
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1Ns

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique Matrix
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut slGraphAut_matrix)
open scoped Matrix

namespace Sec1211Ns

variable {G : Type} [Group G]

@[expose] def Xv (L V₁ : Subgroup G) (v : G) : Subgroup G :=
  Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V₁ : Set G) ⊓
    Subgroup.centralizer ({v} : Set G)

structure Frame [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ} {a₀ c₀ : G}
    (S : Setting T L V V₁ V₂ n a₀ c₀) (m : ℕ) where
  h : 1 + m = n
  s : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)
  hs₁ : (s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ VecStab.e0 h = S.C₁.E a₀
  hs₂ : (slGraphAut n (ZMod 2) s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ VecStab.e0 h = S.C₂.E c₀

namespace Setting

variable [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ} {a₀ c₀ : G}
  (S : Setting T L V V₁ V₂ n a₀ c₀)
include S

theorem nonempty_frame : Nonempty (Frame S (n - 1)) := by
  obtain ⟨s, hs₁, hs₂⟩ := PairStab.exists_normal S.one_add (by have := S.three_le; omega) S.hxy
  exact ⟨⟨S.one_add, s, hs₁, hs₂⟩⟩

theorem Xv_le_normalizer₂ {a : G} (ha : a ∈ Xv L V₁ (a₀ * c₀)) :
    a ∈ Subgroup.normalizer (V₂ : Set G) := by
  rcases S.fix_or_swap ha.1.1 with ⟨-, h⟩ | ⟨h₁, -⟩
  · exact h
  · exfalso
    have h1 : a * a₀ * a⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.mp ha.1.2 a₀).mp S.ha₀
    have h3 : a * a₀ * a⁻¹ ∈ V₁ ⊓ V₂ := ⟨h1, (h₁ a₀).mp S.ha₀⟩
    rw [S.hyp.inf, Subgroup.mem_bot] at h3
    exact S.a₀_ne (by
      calc a₀ = a⁻¹ * (a * a₀ * a⁻¹) * a := by group
        _ = 1 := by rw [h3]; group)

theorem Xv_fix {a : G} (ha : a ∈ Xv L V₁ (a₀ * c₀)) :
    a * a₀ * a⁻¹ = a₀ ∧ a * c₀ * a⁻¹ = c₀ := by
  have hav := Subgroup.mem_centralizer_singleton_iff.mp ha.2
  have e : a * a₀ * a⁻¹ * (a * c₀ * a⁻¹) = a₀ * c₀ := by
    calc a * a₀ * a⁻¹ * (a * c₀ * a⁻¹) = a * (a₀ * c₀) * a⁻¹ := by group
      _ = a₀ * c₀ := by rw [hav, mul_inv_cancel_right]
  exact S.decomp_unique ((Subgroup.mem_normalizer_iff.mp ha.1.2 a₀).mp S.ha₀) S.ha₀
    ((Subgroup.mem_normalizer_iff.mp (S.Xv_le_normalizer₂ ha) c₀).mp S.hc₀) S.hc₀ e

theorem exists_pairStab {a : G} (ha : a ∈ Xv L V₁ (a₀ * c₀)) :
    ∃ g ∈ PairStab.pairStab (S.C₁.E a₀) (S.C₂.E c₀),
      (∀ x ∈ V₁, S.C₁.E (a * x * a⁻¹) = (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ S.C₁.E x) ∧
        ∀ y ∈ V₂, S.C₂.E (a * y * a⁻¹) =
          (slGraphAut n (ZMod 2) g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ S.C₂.E y := by
  obtain ⟨l, hl, hal⟩ := S.exists_eq_conj ha.1.1 ha.1.2 (S.Xv_le_normalizer₂ ha)
  have h₁ : ∀ x ∈ V₁, S.C₁.E (a * x * a⁻¹) = (S.C₁.ρ ⟨l, hl⟩ : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
      S.C₁.E x := fun x hx => by
    rw [hal x (S.le₁ hx)]
    exact S.C₁.conj ⟨l, hl⟩ x hx
  have h₂ : ∀ y ∈ V₂, S.C₂.E (a * y * a⁻¹) =
      (slGraphAut n (ZMod 2) (S.C₁.ρ ⟨l, hl⟩) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ S.C₂.E y :=
    fun y hy => by
      rw [hal y (S.le₂ hy), ← S.dual]
      exact S.C₂.conj ⟨l, hl⟩ y hy
  refine ⟨S.C₁.ρ ⟨l, hl⟩, ⟨?_, ?_⟩, h₁, h₂⟩
  · show (S.C₁.ρ ⟨l, hl⟩ : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ S.C₁.E a₀ = S.C₁.E a₀
    rw [← h₁ a₀ S.ha₀, (S.Xv_fix ha).1]
  · show (slGraphAut n (ZMod 2) (S.C₁.ρ ⟨l, hl⟩) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
      S.C₂.E c₀ = S.C₂.E c₀
    rw [← h₂ c₀ S.hc₀, (S.Xv_fix ha).2]

variable {S} {m : ℕ} (F : Frame S m)

@[expose] noncomputable def frameMat (D : Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) :
    Matrix.SpecialLinearGroup (Fin n) (ZMod 2) :=
  F.s * PairStab.levE F.h D * F.s⁻¹

theorem frameMat_mul (D D' : Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) :
    frameMat F (D * D') = frameMat F D * frameMat F D' := by
  simp only [frameMat, map_mul]
  group

theorem frameMat_injective : Function.Injective (frameMat F) := by
  intro D D' h
  apply PairStab.levE_injective F.h
  have := congrArg (fun g => F.s⁻¹ * g * F.s) h
  simpa [frameMat, mul_assoc] using this

theorem frameMat_mulVec_emb (D : Matrix.SpecialLinearGroup (Fin m) (ZMod 2))
    (ξ : Fin m → ZMod 2) :
    (frameMat F D : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
        ((F.s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ PairStab.emb F.h ξ) =
      (F.s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
        PairStab.emb F.h ((D : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ ξ) := by
  rw [frameMat, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ← mulVec_mulVec, ← mulVec_mulVec, VecStab.inv_mulVec_mulVec, PairStab.levE_mulVec_emb]

theorem graph_frameMat_mulVec_emb (D : Matrix.SpecialLinearGroup (Fin m) (ZMod 2))
    (η : Fin m → ZMod 2) :
    (slGraphAut n (ZMod 2) (frameMat F D) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
        ((slGraphAut n (ZMod 2) F.s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ PairStab.emb F.h η) =
      (slGraphAut n (ZMod 2) F.s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
        PairStab.emb F.h ((slGraphAut m (ZMod 2) D : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ η) := by
  rw [frameMat, map_mul, map_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, ← mulVec_mulVec,
    PairStab.graph_inv_mulVec_mulVec, PairStab.graph_levE_mulVec_emb]

theorem exists_frameMat {g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)}
    (hg : g ∈ PairStab.pairStab (S.C₁.E a₀) (S.C₂.E c₀)) : ∃ D, frameMat F D = g := by
  rw [PairStab.eq_map_levE F.h F.hs₁ F.hs₂] at hg
  obtain ⟨_, ⟨D, rfl⟩, rfl⟩ := hg
  exact ⟨D, rfl⟩

theorem exists_D {a : G} (ha : a ∈ Xv L V₁ (a₀ * c₀)) :
    ∃ D : Matrix.SpecialLinearGroup (Fin m) (ZMod 2),
      (∀ x ∈ V₁, S.C₁.E (a * x * a⁻¹) =
        (frameMat F D : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ S.C₁.E x) ∧
      ∀ y ∈ V₂, S.C₂.E (a * y * a⁻¹) =
        (slGraphAut n (ZMod 2) (frameMat F D) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ S.C₂.E y := by
  obtain ⟨g, hg, h₁, h₂⟩ := S.exists_pairStab ha
  obtain ⟨D, rfl⟩ := exists_frameMat F hg
  exact ⟨D, h₁, h₂⟩

theorem D_unique {a : G} {D D' : Matrix.SpecialLinearGroup (Fin m) (ZMod 2)}
    (hD : ∀ x ∈ V₁, S.C₁.E (a * x * a⁻¹) =
      (frameMat F D : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ S.C₁.E x)
    (hD' : ∀ x ∈ V₁, S.C₁.E (a * x * a⁻¹) =
      (frameMat F D' : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ S.C₁.E x) : D = D' := by
  apply frameMat_injective F
  refine PairStab.eq_of_mulVec_eq fun ξ => ?_
  have h1 := hD _ (S.C₁.inv_mem ξ)
  rw [hD' _ (S.C₁.inv_mem ξ), S.C₁.E_inv] at h1
  exact h1.symm

@[expose] noncomputable def theta :
    ↥(Xv L V₁ (a₀ * c₀)) →* Matrix.SpecialLinearGroup (Fin m) (ZMod 2) where
  toFun a := Classical.choose (exists_D F a.2)
  map_one' := by
    refine D_unique F (Classical.choose_spec (exists_D F (Xv L V₁ (a₀ * c₀)).one_mem)).1 ?_
    intro x _
    rw [show frameMat F 1 = 1 by simp [frameMat], Matrix.SpecialLinearGroup.coe_one, one_mulVec]
    simp
  map_mul' a b := by
    refine D_unique F (Classical.choose_spec (exists_D F (a * b).2)).1 ?_
    intro x hx
    have hb := (Classical.choose_spec (exists_D F b.2)).1 x hx
    have hbx : (b : G) * x * (b : G)⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.mp b.2.1.2 x).mp hx
    have ha := (Classical.choose_spec (exists_D F a.2)).1 _ hbx
    have e : ((a * b : ↥(Xv L V₁ (a₀ * c₀))) : G) * x * ((a * b : ↥(Xv L V₁ (a₀ * c₀))) : G)⁻¹ =
        (a : G) * ((b : G) * x * (b : G)⁻¹) * (a : G)⁻¹ := by
      simp only [Subgroup.coe_mul]
      group
    rw [e, ha, hb, frameMat_mul, Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec]

theorem theta_spec₁ (a : ↥(Xv L V₁ (a₀ * c₀))) {x : G} (hx : x ∈ V₁) :
    S.C₁.E ((a : G) * x * (a : G)⁻¹) =
      (frameMat F (theta F a) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ S.C₁.E x :=
  (Classical.choose_spec (exists_D F a.2)).1 x hx

theorem theta_spec₂ (a : ↥(Xv L V₁ (a₀ * c₀))) {y : G} (hy : y ∈ V₂) :
    S.C₂.E ((a : G) * y * (a : G)⁻¹) =
      (slGraphAut n (ZMod 2) (frameMat F (theta F a)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
        S.C₂.E y :=
  (Classical.choose_spec (exists_D F a.2)).2 y hy

theorem s_emb_dot (ξ : Fin m → ZMod 2) :
    ((F.s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ PairStab.emb F.h ξ) ⬝ᵥ S.C₂.E c₀ = 0 := by
  rw [← PairStab.inv_mulVec_dot F.h F.hs₂, VecStab.inv_mulVec_mulVec, PairStab.emb_dot_e0]

theorem graph_s_emb_dot (η : Fin m → ZMod 2) :
    S.C₁.E a₀ ⬝ᵥ ((slGraphAut n (ZMod 2) F.s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
      PairStab.emb F.h η) = 0 := by
  rw [dotProduct_comm, ← PairStab.graph_inv_mulVec_dot F.h F.hs₁,
    PairStab.graph_inv_mulVec_mulVec, PairStab.emb_dot_e0]

theorem exists_emb₁ {x : G} (hx : x ∈ S.W₁) :
    ∃ ξ, S.C₁.E x = (F.s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ PairStab.emb F.h ξ := by
  obtain ⟨ξ, hξ⟩ := PairStab.exists_emb_of_dot F.h
    (x := ((F.s⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ S.C₁.E x)
    (by rw [PairStab.inv_mulVec_dot F.h F.hs₂]; exact hx.2)
  refine ⟨ξ, ?_⟩
  rw [← hξ, VecStab.mulVec_inv_mulVec]

theorem exists_emb₂ {y : G} (hy : y ∈ S.W₂) :
    ∃ η, S.C₂.E y = (slGraphAut n (ZMod 2) F.s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
      PairStab.emb F.h η := by
  obtain ⟨η, hη⟩ := PairStab.exists_emb_of_dot F.h
    (x := (slGraphAut n (ZMod 2) F.s⁻¹ : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ S.C₂.E y)
    (by rw [PairStab.graph_inv_mulVec_dot F.h F.hs₁, dotProduct_comm]; exact hy.2)
  refine ⟨η, ?_⟩
  rw [← hη, map_inv]
  exact (VecStab.mulVec_inv_mulVec _ _).symm

@[expose] noncomputable def psi {Y : Subgroup G} (hY : Y ≤ Xv L V₁ (a₀ * c₀)) :
    ↥Y →* Matrix.SpecialLinearGroup (Fin m) (ZMod 2) :=
  (theta F).comp (Subgroup.inclusion hY)

theorem psi_spec₁ {Y : Subgroup G} (hY : Y ≤ Xv L V₁ (a₀ * c₀)) (a : ↥Y) {x : G}
    (hx : x ∈ V₁) : S.C₁.E ((a : G) * x * (a : G)⁻¹) =
      (frameMat F (psi F hY a) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ S.C₁.E x :=
  theta_spec₁ F (Subgroup.inclusion hY a) hx

theorem psi_spec₂ {Y : Subgroup G} (hY : Y ≤ Xv L V₁ (a₀ * c₀)) (a : ↥Y) {y : G}
    (hy : y ∈ V₂) : S.C₂.E ((a : G) * y * (a : G)⁻¹) =
      (slGraphAut n (ZMod 2) (frameMat F (psi F hY a)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
        S.C₂.E y :=
  theta_spec₂ F (Subgroup.inclusion hY a) hy

theorem conj_eq_iff₁ {a x : G} (haN : a ∈ Subgroup.normalizer (V₁ : Set G)) (hx : x ∈ V₁)
    {g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)}
    (hg : S.C₁.E (a * x * a⁻¹) = (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ S.C₁.E x) :
    a * x = x * a ↔ (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ S.C₁.E x = S.C₁.E x := by
  rw [← hg]
  constructor
  · intro h
    rw [h, mul_inv_cancel_right]
  · intro h
    have h1 := S.C₁.inj _ ((Subgroup.mem_normalizer_iff.mp haN x).mp hx) _ hx h
    calc a * x = a * x * a⁻¹ * a := by group
      _ = x * a := by rw [h1]

theorem conj_eq_iff₂ {a y : G} (haN : a ∈ Subgroup.normalizer (V₂ : Set G)) (hy : y ∈ V₂)
    {g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)}
    (hg : S.C₂.E (a * y * a⁻¹) = (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ S.C₂.E y) :
    a * y = y * a ↔ (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ S.C₂.E y = S.C₂.E y := by
  rw [← hg]
  constructor
  · intro h
    rw [h, mul_inv_cancel_right]
  · intro h
    have h1 := S.C₂.inj _ ((Subgroup.mem_normalizer_iff.mp haN y).mp hy) _ hy h
    calc a * y = a * y * a⁻¹ * a := by group
      _ = y * a := by rw [h1]

section Three

variable (F : Frame S 3)

theorem card_W₁_inf {Y : Subgroup G} (hY : Y ≤ Xv L V₁ (a₀ * c₀)) :
    Nat.card ↥(S.W₁ ⊓ Subgroup.centralizer (Y : Set G)) = Nat.card (FF3.fixS (psi F hY).range) := by
  symm
  refine Nat.card_eq_of_bijective (fun ξ => ⟨S.C₁.inv ((F.s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
    PairStab.emb F.h (ξ : Fin 3 → ZMod 2)), ⟨S.C₁.inv_mem _, by
      show S.C₁.E (S.C₁.inv _) ⬝ᵥ S.C₂.E c₀ = 0
      rw [S.C₁.E_inv]
      exact s_emb_dot F _⟩, ?_⟩) ⟨?_, ?_⟩
  · refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
    have h1 := psi_spec₁ F hY ⟨a, ha⟩ (S.C₁.inv_mem ((F.s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
      PairStab.emb F.h (ξ : Fin 3 → ZMod 2)))
    refine (conj_eq_iff₁ (hY ha).1.2 (S.C₁.inv_mem _) h1).mpr ?_
    rw [S.C₁.E_inv, frameMat_mulVec_emb, ξ.2 _ ⟨⟨a, ha⟩, rfl⟩]
  · intro ξ ξ' he
    have h1 := congrArg (fun x : ↥(S.W₁ ⊓ Subgroup.centralizer (Y : Set G)) => S.C₁.E x) he
    simp only [S.C₁.E_inv] at h1
    have h2 := congrArg (fun z => ((F.s⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ z) h1
    simp only [VecStab.inv_mulVec_mulVec] at h2
    exact Subtype.ext (PairStab.emb_injective F.h h2)
  · rintro ⟨x, hxW, hxC⟩
    obtain ⟨ξ, hξ⟩ := exists_emb₁ F hxW
    refine ⟨⟨ξ, ?_⟩, Subtype.ext ?_⟩
    · rintro _ ⟨a, rfl⟩
      have h1 := psi_spec₁ F hY a hxW.1
      have h2 := (conj_eq_iff₁ (hY a.2).1.2 hxW.1 h1).mp
        (Subgroup.mem_centralizer_iff.mp hxC a a.2)
      rw [hξ, frameMat_mulVec_emb] at h2
      have h3 := congrArg (fun z => ((F.s⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ z) h2
      simp only [VecStab.inv_mulVec_mulVec] at h3
      exact PairStab.emb_injective F.h h3
    · show S.C₁.inv _ = x
      rw [← hξ, S.C₁.inv_E hxW.1]

theorem card_W₂_inf {Y : Subgroup G} (hY : Y ≤ Xv L V₁ (a₀ * c₀)) (hY2 : ∀ a ∈ Y, a * a = 1) :
    Nat.card ↥(S.W₂ ⊓ Subgroup.centralizer (Y : Set G)) = Nat.card (FF3.fixT (psi F hY).range) := by
  have hinv : ∀ a : ↥Y, psi F hY a * psi F hY a = 1 := fun a => by
    rw [← map_mul, show a * a = 1 from Subtype.ext (hY2 a a.2), map_one]
  have hδ : ∀ a : ↥Y, (slGraphAut 3 (ZMod 2) (psi F hY a) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (psi F hY a : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ := fun a =>
    FF3.slGraphAut_eq_transpose (hinv a)
  symm
  refine Nat.card_eq_of_bijective (fun η => ⟨S.C₂.inv
    ((slGraphAut n (ZMod 2) F.s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
      PairStab.emb F.h (η : Fin 3 → ZMod 2)), ⟨S.C₂.inv_mem _, by
      show S.C₁.E a₀ ⬝ᵥ S.C₂.E (S.C₂.inv _) = 0
      rw [S.C₂.E_inv]
      exact graph_s_emb_dot F _⟩, ?_⟩) ⟨?_, ?_⟩
  · refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
    have h1 := psi_spec₂ F hY ⟨a, ha⟩ (S.C₂.inv_mem
      ((slGraphAut n (ZMod 2) F.s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
        PairStab.emb F.h (η : Fin 3 → ZMod 2)))
    refine (conj_eq_iff₂ (S.Xv_le_normalizer₂ (hY ha)) (S.C₂.inv_mem _) h1).mpr ?_
    rw [S.C₂.E_inv, graph_frameMat_mulVec_emb, hδ, η.2 _ ⟨⟨a, ha⟩, rfl⟩]
  · intro η η' he
    have h1 := congrArg (fun x : ↥(S.W₂ ⊓ Subgroup.centralizer (Y : Set G)) => S.C₂.E x) he
    simp only [S.C₂.E_inv] at h1
    have h2 := congrArg (fun z => (slGraphAut n (ZMod 2) F.s⁻¹ :
      Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ z) h1
    simp only [PairStab.graph_inv_mulVec_mulVec] at h2
    exact Subtype.ext (PairStab.emb_injective F.h h2)
  · rintro ⟨y, hyW, hyC⟩
    obtain ⟨η, hη⟩ := exists_emb₂ F hyW
    refine ⟨⟨η, ?_⟩, Subtype.ext ?_⟩
    · rintro _ ⟨a, rfl⟩
      have h1 := psi_spec₂ F hY a hyW.1
      have h2 := (conj_eq_iff₂ (S.Xv_le_normalizer₂ (hY a.2)) hyW.1 h1).mp
        (Subgroup.mem_centralizer_iff.mp hyC a a.2)
      rw [hη, graph_frameMat_mulVec_emb, hδ] at h2
      have h3 := congrArg (fun z => (slGraphAut n (ZMod 2) F.s⁻¹ :
        Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ z) h2
      simp only [PairStab.graph_inv_mulVec_mulVec] at h3
      exact PairStab.emb_injective F.h h3
    · show S.C₂.inv _ = y
      rw [← hη, S.C₂.inv_E hyW.1]

end Three

end Setting

end Sec1211Ns

end CFSG.Quasithin.H13
