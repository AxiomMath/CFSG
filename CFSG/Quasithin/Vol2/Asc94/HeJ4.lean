module

public import CFSG.Quasithin.Vol2.Asc94.HeJ3
public import CFSG.Quasithin.Vol2.Asc94.TSGen

public section

namespace CFSG.Quasithin.A94.HeJ

open Matrix Subgroup

variable {G : Type} [Group G] [Finite G]

theorem NData.symm {A A' : Subgroup G} {u w : G → V2} {N T : Subgroup G}
    (h : NData (A := A) (A' := A') u w N T) (hsq : ∀ x ∈ A', x * x = 1) :
    NData (A := A') (A' := A) w u N T where
  norm n hn := ⟨(h.norm n hn).2, (h.norm n hn).1⟩
  JN := by rw [sup_comm]; exact h.JN
  Aab := h.A'ab
  A'ab := h.Aab
  Asq := hsq
  cent x hx := by
    rw [inf_comm]
    exact h.cent x (fun y hy => hx y (by rw [sup_comm]; exact hy))
  TN := h.TN
  Tf t ht h1 h2 := by
    rw [sup_comm]
    exact h.Tf t ht h2 h1
  card := by rw [sup_comm]; exact h.card

structure Data40 (A A' : Subgroup G) (u w : G → V2) (m : G → M2) (N T : Subgroup G) (a : G) :
    Prop where
  hT : TData A A' u w m
  hK : NData (A := A) (A' := A') u w N T
  ha : a ∈ A ⊓ A'
  ham : m a = 1
  cardJ : Nat.card ↥(A ⊔ A') = 256
  cardM : Nat.card ↥(normalizer (A : Set G)) = 138240
  cardΩ : Nat.card {y : G // ∃ l ∈ normalizer (A : Set G), y = l⁻¹ * a * l} = 18

theorem Data40.symm {A A' : Subgroup G} {u w : G → V2} {m : G → M2} {N T : Subgroup G} {a : G}
    (h : Data40 A A' u w m N T a) (hsq : ∀ x ∈ A', x * x = 1)
    (cardM : Nat.card ↥(normalizer (A' : Set G)) = 138240)
    (cardΩ : Nat.card {y : G // ∃ l ∈ normalizer (A' : Set G), y = l⁻¹ * a * l} = 18) :
    Data40 A' A w u (fun x => (m x)ᵀ) N T a where
  hT := h.hT.symm
  hK := h.hK.symm hsq
  ha := by rw [inf_comm]; exact h.ha
  ham := by simp [h.ham]
  cardJ := by rw [sup_comm]; exact h.cardJ
  cardM := cardM
  cardΩ := cardΩ

section D40

variable {A A' : Subgroup G} {u w : G → V2} {m : G → M2} {N T : Subgroup G} {a : G}
  (hD : Data40 A A' u w m N T a)

include hD

theorem Data40.cardN : Nat.card ↥N = 9216 := by
  rw [hD.hK.card, hD.cardJ]

theorem Data40.N_le_M : N ≤ normalizer (A : Set G) := by
  intro n hn
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact (hD.hK.norm n hn).1 x
  · intro hx
    have h := (hD.hK.norm n⁻¹ (N.inv_mem hn)).1 _ hx
    have e : n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x := by group
    rwa [e] at h

theorem Data40.mem_Z_conj {l : G} (hl : l ∈ N) {y : G} (hy : y ∈ A ⊓ A') : l * y * l⁻¹ ∈ A ⊓ A' :=
  ⟨(hD.hK.norm l hl).1 y hy.1, (hD.hK.norm l hl).2 y hy.2⟩

theorem Data40.card_orbit_N :
    Nat.card {y : G // ∃ l ∈ N, y = l⁻¹ * a * l} = 6 := by
  rw [← card_isUnit_M2]
  have hZ : ∀ l ∈ N, l⁻¹ * a * l ∈ A ⊓ A' := fun l hl => by
    have := hD.mem_Z_conj (N.inv_mem hl) hD.ha
    simpa using this
  have hm : ∀ (l : G) (hl : l ∈ N), m (l⁻¹ * a * l) =
      ((hD.hT.rho N hD.hK.norm ⟨l⁻¹, N.inv_mem hl⟩).1 : M2) *
        ((hD.hT.rho N hD.hK.norm ⟨l⁻¹, N.inv_mem hl⟩).2 : M2)ᵀ := by
    intro l hl
    have := hD.hT.m_conj N hD.hK.norm ⟨l⁻¹, N.inv_mem hl⟩ hD.ha
    simp only [inv_inv] at this
    rw [this, hD.ham, mul_one]
  refine Nat.card_congr (Equiv.ofBijective (fun y => ⟨m y.1, ?_⟩) ⟨?_, ?_⟩)
  · obtain ⟨y, l, hl, rfl⟩ := y
    simp only
    rw [hm l hl]
    refine IsUnit.mul (Units.isUnit _) ?_
    refine (Matrix.isUnit_iff_isUnit_det _).mpr ?_
    rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)
  · rintro ⟨y₁, l₁, hl₁, rfl⟩ ⟨y₂, l₂, hl₂, rfl⟩ h
    have h' : m (l₁⁻¹ * a * l₁) = m (l₂⁻¹ * a * l₂) := congrArg Subtype.val h
    exact Subtype.ext (hD.hT.minj _ (hZ l₁ hl₁) _ (hZ l₂ hl₂) h')
  · rintro ⟨Q, hQ⟩
    obtain ⟨n, hn⟩ := hD.hT.rho_surjective hD.hK (hQ.unit, 1)
    refine ⟨⟨(n : G) * a * (n : G)⁻¹, (n : G)⁻¹, N.inv_mem n.2, by simp⟩, ?_⟩
    apply Subtype.ext
    show m ((n : G) * a * (n : G)⁻¹) = Q
    rw [hD.hT.m_conj N hD.hK.norm n hD.ha, hD.ham, hn]
    simp

theorem Data40.cardD : Nat.card ↥(N ⊓ centralizer ({a} : Set G)) = 1536 := by
  have h := CFSG.Quasithin.A94.Gen.card_conjOrbit_mul_card_stab N a
  rw [hD.card_orbit_N, hD.cardN] at h
  omega

theorem Data40.cardI :
    Nat.card ↥(normalizer (A : Set G) ⊓ centralizer ({a} : Set G)) = 7680 := by
  have h := CFSG.Quasithin.A94.Gen.card_conjOrbit_mul_card_stab (normalizer (A : Set G)) a
  rw [hD.cardΩ, hD.cardM] at h
  omega

theorem Data40.D_le_I :
    N ⊓ centralizer ({a} : Set G) ≤ normalizer (A : Set G) ⊓ centralizer ({a} : Set G) :=
  inf_le_inf_right _ hD.N_le_M

theorem Data40.relIndex_D_I :
    (N ⊓ centralizer ({a} : Set G)).relIndex
      (normalizer (A : Set G) ⊓ centralizer ({a} : Set G)) = 5 := by
  have h := Subgroup.relIndex_mul_card (H := N ⊓ centralizer ({a} : Set G))
    (K := normalizer (A : Set G) ⊓ centralizer ({a} : Set G))
  rw [inf_eq_left.mpr hD.D_le_I, hD.cardD, hD.cardI] at h
  omega

theorem Data40.rho_D {n : N} (hn : (n : G) ∈ centralizer ({a} : Set G)) :
    ((hD.hT.rho N hD.hK.norm n).1 : M2) * ((hD.hT.rho N hD.hK.norm n).2 : M2)ᵀ = 1 := by
  have hc : (n : G) * a * (n : G)⁻¹ = a := by
    have := mem_centralizer_singleton_iff.mp hn
    rw [mul_inv_eq_iff_eq_mul]; exact this
  have := hD.hT.m_conj N hD.hK.norm n hD.ha
  rw [hc, hD.ham, mul_one] at this
  exact this.symm

theorem Data40.exists_x :
    ∃ x : G, x ∈ N ∧ x ∈ centralizer ({a} : Set G) ∧ orderOf x = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h3 : 3 ∣ Nat.card ↥(N ⊓ centralizer ({a} : Set G)) := by rw [hD.cardD]; norm_num
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(N ⊓ centralizer ({a} : Set G))) 3 h3
  exact ⟨x, x.2.1, x.2.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

theorem Data40.rho_D_inv {n : N} (hn : (n : G) ∈ centralizer ({a} : Set G)) :
    ((hD.hT.rho N hD.hK.norm n).2 : M2)ᵀ = (((hD.hT.rho N hD.hK.norm n).1)⁻¹ : GL2).val := by
  have hρ := hD.rho_D hn
  set g := (hD.hT.rho N hD.hK.norm n).1 with hg
  calc ((hD.hT.rho N hD.hK.norm n).2 : M2)ᵀ
      = ((g⁻¹ : GL2).val * (g : M2)) * ((hD.hT.rho N hD.hK.norm n).2 : M2)ᵀ := by
        rw [Units.inv_mul, one_mul]
    _ = (g⁻¹ : GL2).val * ((g : M2) * ((hD.hT.rho N hD.hK.norm n).2 : M2)ᵀ) := by
        rw [mul_assoc]
    _ = (g⁻¹ : GL2).val := by rw [hρ, mul_one]

theorem Data40.m_conj_D {n : N} (hn : (n : G) ∈ centralizer ({a} : Set G)) {v : G}
    (hv : v ∈ A ⊓ A') :
    m ((n : G) * v * (n : G)⁻¹) = ((hD.hT.rho N hD.hK.norm n).1 : M2) * m v *
      (((hD.hT.rho N hD.hK.norm n).1)⁻¹ : GL2).val := by
  rw [hD.hT.m_conj N hD.hK.norm n hv, hD.rho_D_inv hn]

section X

variable {x : G} (hxN : x ∈ N) (hxa : x ∈ centralizer ({a} : Set G)) (hx3 : orderOf x = 3)

include hxN hxa hx3

theorem Data40.g_pow_three :
    (hD.hT.rho N hD.hK.norm ⟨x, hxN⟩).1 ^ 3 = 1 := by
  have h1 : (⟨x, hxN⟩ : N) ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow]; simpa using pow_orderOf_eq_one x |> fun h => hx3 ▸ h)
  have := congrArg (fun r => r.1) (by rw [← map_pow, h1, map_one] :
    (hD.hT.rho N hD.hK.norm ⟨x, hxN⟩) ^ 3 = 1)
  simpa using this

theorem Data40.g_ne_one : (hD.hT.rho N hD.hK.norm ⟨x, hxN⟩).1 ≠ 1 := by
  intro hg
  have hρ := hD.rho_D (n := ⟨x, hxN⟩) hxa
  rw [hg] at hρ
  have h2 : ((hD.hT.rho N hD.hK.norm ⟨x, hxN⟩).2 : M2) = 1 := by
    have : ((hD.hT.rho N hD.hK.norm ⟨x, hxN⟩).2 : M2)ᵀ = 1 := by simpa using hρ
    simpa using congrArg Matrix.transpose this
  have hone : hD.hT.rho N hD.hK.norm ⟨x, hxN⟩ = 1 :=
    Prod.ext hg (Units.ext h2)
  have hker : (⟨x, hxN⟩ : N) ∈ (hD.hT.rho N hD.hK.norm).ker := hone
  rw [hD.hT.ker_rho hD.hK, Subgroup.mem_subgroupOf] at hker
  have h3 : orderOf (⟨x, hker⟩ : ↥(A ⊔ A')) ∣ Nat.card ↥(A ⊔ A') := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hx3, hD.cardJ] at h3
  omega

end X

end D40

end CFSG.Quasithin.A94.HeJ
