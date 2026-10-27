module

public import CFSG.RankThree.GF2n.Smith81.Sec1Frobenius
import CFSG.RankThree.GF2n.Stroth80.Sec41Alg

public section

namespace CFSG.RankThree.GF2n.Smith81

variable {G : Type} [Group G]

@[expose] def KillsAbelian (P C : Subgroup G) : Prop :=
  ∀ (A : Type) [Group A], (∀ a b : A, a * b = b * a) → ∀ f : ↥P →* A,
    (∀ p : ↥P, (p : G) ∈ C → f p = 1) → ∀ p, f p = 1

theorem killsAbelian_of_surjective {R X : Type} [Group R] [Group X] (hX : Group.IsPerfect X)
    (N₀ : Subgroup R) [N₀.Normal] (e : R ⧸ N₀ ≃* X) {P C : Subgroup G} (s : R →* ↥P)
    (hs : Function.Surjective s) (hN₀ : ∀ x ∈ N₀, ((s x : ↥P) : G) ∈ C) : KillsAbelian P C := by
  intro A _ hA f hf p
  obtain ⟨x, rfl⟩ := hs p
  have hker : N₀ ≤ (f.comp s).ker := fun y hy => hf _ (hN₀ y hy)
  haveI := hX
  have h1 := Stroth80.hom_eq_one_of_perfect_of_comm hA
    ((QuotientGroup.lift N₀ (f.comp s) hker).comp e.symm.toMonoidHom) (e (QuotientGroup.mk x))
  simpa using h1

theorem centralizes_of_semilinAct_of_kills {N Y P C : Subgroup G} (hS : SemilinAct N Y)
    (hPN : P ≤ N) (hCY : ∀ c ∈ C, ∀ y ∈ Y, c * y = y * c) (hP : KillsAbelian P C) :
    ∀ p ∈ P, ∀ y ∈ Y, p * y = y * p := by
  classical
  obtain ⟨hN, K, hK, hfin, e, hact⟩ := hS
  choose a σ hasig using fun m : ↥N => hact (m : G) m.2
  have huniq : ∀ (c₁ c₂ : K) (σ₁ σ₂ : K ≃+* K), c₁ ≠ 0 →
      (∀ k, c₁ * σ₁ k = c₂ * σ₂ k) → c₁ = c₂ ∧ σ₁ = σ₂ := by
    intro c₁ c₂ σ₁ σ₂ hc h
    have h1 := h 1
    simp only [map_one, mul_one] at h1
    refine ⟨h1, RingEquiv.ext fun k => ?_⟩
    have := h k
    rw [h1] at this
    exact mul_left_cancel₀ (h1 ▸ hc) this
  have key : ∀ (m m' : ↥N) (k : K), (a (m * m') : K) * σ (m * m') k =
      (a m : K) * σ m ((a m' : K) * σ m' k) := by
    intro m m' k
    set z : ↥Y := e.symm (Multiplicative.ofAdd k) with hz
    have hzk : Multiplicative.toAdd (e z) = k := by simp [hz]
    let w' : ↥Y := ⟨(m' : G) * z * (m' : G)⁻¹, hN m' m'.2 z z.2⟩
    let w : ↥Y := ⟨(m : G) * w' * (m : G)⁻¹, hN m m.2 w' w'.2⟩
    have h1 := hasig m' z w' rfl
    have h2 := hasig m w' w rfl
    have h3 := hasig (m * m') z w (by
      show (m : G) * ((m' : G) * z * (m' : G)⁻¹) * (m : G)⁻¹ =
        (m : G) * (m' : G) * z * ((m : G) * (m' : G))⁻¹
      group)
    rw [hzk] at h1 h3
    rw [h1] at h2
    exact h3.symm.trans h2
  have hσmul : ∀ m m' : ↥N, σ (m * m') = σ m * σ m' := by
    intro m m'
    refine (huniq (a (m * m') : K) ((a m : K) * σ m (a m' : K)) (σ (m * m')) (σ m * σ m')
      (a (m * m')).ne_zero fun k => ?_).2
    rw [key, map_mul, mul_assoc]
    rfl
  have hamul : ∀ m m' : ↥N, (a (m * m') : K) = (a m : K) * σ m (a m' : K) := by
    intro m m'
    refine (huniq (a (m * m') : K) ((a m : K) * σ m (a m' : K)) (σ (m * m')) (σ m * σ m')
      (a (m * m')).ne_zero fun k => ?_).1
    rw [key, map_mul, mul_assoc]
    rfl
  have htriv : ∀ m : ↥N, (m : G) ∈ C → (a m : K) = 1 ∧ σ m = 1 := by
    intro m hmC
    refine huniq (a m : K) 1 (σ m) 1 (a m).ne_zero fun k => ?_
    set z : ↥Y := e.symm (Multiplicative.ofAdd k) with hz
    have hzk : Multiplicative.toAdd (e z) = k := by simp [hz]
    have h1 := hasig m z z (by
      rw [hCY _ hmC _ z.2]
      group)
    rw [hzk] at h1
    rw [← h1, one_mul]
    rfl
  let sgm : ↥N →* (K ≃+* K) := MonoidHom.mk' σ hσmul
  haveI : IsMulCommutative (K ≃+* K) := (Stroth80.isCyclic_ringEquiv K).isMulCommutative
  have hσ1 : ∀ (p : G) (hp : p ∈ P), σ ⟨p, hPN hp⟩ = 1 := fun p hp =>
    hP _ (fun a b => Std.Commutative.comm (op := (· * ·)) a b)
      (sgm.comp (Subgroup.inclusion hPN)) (fun p' hp' => (htriv _ hp').2) ⟨p, hp⟩
  let lam : ↥P →* Kˣ := MonoidHom.mk' (fun p : ↥P => a ⟨(p : G), hPN p.2⟩) (fun p p' => by
    apply Units.ext
    have := hamul ⟨(p : G), hPN p.2⟩ ⟨(p' : G), hPN p'.2⟩
    rw [hσ1 (p : G) p.2] at this
    exact this)
  intro p hp y hy
  have ha1 : a ⟨p, hPN hp⟩ = 1 :=
    hP _ (fun a b => mul_comm a b) lam (fun p' hp' => Units.ext (htriv _ hp').1) ⟨p, hp⟩
  let z : ↥Y := ⟨y, hy⟩
  let w : ↥Y := ⟨p * y * p⁻¹, hN p (hPN hp) y hy⟩
  have h1 := hasig ⟨p, hPN hp⟩ z w rfl
  rw [hσ1 p hp, ha1] at h1
  have h2 : Multiplicative.toAdd (e w) = Multiplicative.toAdd (e z) := by simpa using h1
  have h3 : w = z := e.injective (Multiplicative.toAdd.injective h2)
  have h4 : p * y * p⁻¹ = y := congrArg Subtype.val h3
  calc p * y = (p * y * p⁻¹) * p := by group
    _ = y * p := by rw [h4]

end CFSG.RankThree.GF2n.Smith81
