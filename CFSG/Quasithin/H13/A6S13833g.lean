module

public import CFSG.Quasithin.H13.A6S13833f

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

@[expose] def dPair : Fin 15 → Fin 6 × Fin 6 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5),
    (3, 4), (3, 5), (4, 5)]

@[expose] def dVec (k : Fin 15) : P6 := dv (dPair k).1 (dPair k).2

@[expose] def dIdx (w : P6) : Fin 15 := ((List.finRange 15).find? fun k => dVec k = w).getD 0

@[expose] def dPerm (σ : Perm (Fin 6)) (k : Fin 15) : Fin 15 := dIdx (act4f σ (dVec k))

theorem dVec_facts : ∀ k, InW4 (dVec k) ∧ dVec k ≠ 1 := by decide +kernel

theorem dVec_inj : ∀ k k', dVec k = dVec k' → k = k' := by decide +kernel

theorem dVec_dIdx : ∀ w : P6, InW4 w → w ≠ 1 → dVec (dIdx w) = w := by decide +kernel

theorem dVec_fourteen : dVec 14 = e0123 := by decide

theorem exists_A6_dVec : ∀ k : Fin 15, ∃ σ : Perm (Fin 6), Perm.sign σ = 1 ∧
    act4f σ e0123 = dVec k := by
  decide +kernel

theorem zmod2_cases' : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem act4f_map_one : ∀ σ : Perm (Fin 6), act4f σ 1 = 1 := by decide +kernel

theorem act4f_dVec (σ : Perm (Fin 6)) (k : Fin 15) : act4f σ (dVec k) = dVec (dPerm σ k) := by
  have hW := (dVec_facts k).1
  have hne : act4f σ (dVec k) ≠ 1 := by
    intro h
    apply (dVec_facts k).2
    have e : act4f σ⁻¹ (act4f σ (dVec k)) = dVec k := by
      rw [← act4f_mul, inv_mul_cancel, act4f_one _ hW]
    rw [← e, h, act4f_map_one]
  exact (dVec_dIdx _ (act4f_mem σ hW) hne).symm

theorem dPerm_mul (σ τ : Perm (Fin 6)) (k : Fin 15) :
    dPerm (σ * τ) k = dPerm σ (dPerm τ k) := by
  apply dVec_inj
  rw [← act4f_dVec, ← act4f_dVec, ← act4f_dVec, act4f_mul]

theorem dPerm_one (k : Fin 15) : dPerm 1 k = k := by
  apply dVec_inj
  rw [← act4f_dVec, act4f_one _ (dVec_facts k).1]

theorem dPerm_inv_dPerm (σ : Perm (Fin 6)) (k : Fin 15) : dPerm σ⁻¹ (dPerm σ k) = k := by
  rw [← dPerm_mul, inv_mul_cancel, dPerm_one]

theorem dPerm_dPerm_inv (σ : Perm (Fin 6)) (k : Fin 15) : dPerm σ (dPerm σ⁻¹ k) = k := by
  rw [← dPerm_mul, mul_inv_cancel, dPerm_one]

@[expose] def dPermE (σ : Perm (Fin 6)) : Perm (Fin 15) where
  toFun := dPerm σ
  invFun := dPerm σ⁻¹
  left_inv := dPerm_inv_dPerm σ
  right_inv := dPerm_dPerm_inv σ

@[expose] def actA (σ : Perm (Fin 6)) : (Fin 6 → ZMod 2) →+ (Fin 6 → ZMod 2) where
  toFun v := Multiplicative.toAdd (act4f σ (Multiplicative.ofAdd v))
  map_zero' := by
    show Multiplicative.toAdd (act4f σ 1) = 0
    rw [act4f_map_one]; rfl
  map_add' v w := by
    show Multiplicative.toAdd (act4f σ (Multiplicative.ofAdd v * Multiplicative.ofAdd w)) = _
    rw [act4f_mul_apply]; rfl

theorem actA_smul (σ : Perm (Fin 6)) (c : ZMod 2) (v : Fin 6 → ZMod 2) :
    actA σ (c • v) = c • actA σ v := by
  rcases zmod2_cases' c with rfl | rfl
  · rw [zero_smul, zero_smul, map_zero]
  · rw [one_smul, one_smul]

@[expose] def dA (k : Fin 15) : Fin 6 → ZMod 2 := Multiplicative.toAdd (dVec k)

theorem actA_dA (σ : Perm (Fin 6)) (k : Fin 15) : actA σ (dA k) = dA (dPerm σ k) := by
  show Multiplicative.toAdd (act4f σ (dVec k)) = _
  rw [act4f_dVec]; rfl

@[expose] def ConI (s t : Fin 15 → ZMod 2) : Prop := ∑ k, (s k * t k) • dA k = 0

instance (s t : Fin 15 → ZMod 2) : Decidable (ConI s t) := by unfold ConI; infer_instance

theorem ConI_add {s s' t : Fin 15 → ZMod 2} (h : ConI s t) (h' : ConI s' t) :
    ConI (s + s') t := by
  unfold ConI at *
  simp only [Pi.add_apply, add_mul, add_smul, Finset.sum_add_distrib, h, h', add_zero]

theorem actA_inv_actA (σ : Perm (Fin 6)) {v : Fin 6 → ZMod 2} (hv : InW4 (Multiplicative.ofAdd v)) :
    actA σ⁻¹ (actA σ v) = v := by
  show Multiplicative.toAdd (act4f σ⁻¹ (act4f σ (Multiplicative.ofAdd v))) = v
  rw [← act4f_mul, inv_mul_cancel, act4f_one _ hv]
  rfl

theorem inW4_sum_dA (c : Fin 15 → ZMod 2) : InW4 (Multiplicative.ofAdd (∑ k, c k • dA k)) := by
  have hW : ∀ v w : Fin 6 → ZMod 2, InW4 (Multiplicative.ofAdd v) →
      InW4 (Multiplicative.ofAdd w) → InW4 (Multiplicative.ofAdd (v + w)) := by
    intro v w hv hw
    exact W4.mul_mem hv hw
  have h0 : InW4 (Multiplicative.ofAdd (0 : Fin 6 → ZMod 2)) := W4.one_mem
  have hs : ∀ (a : ZMod 2) (k : Fin 15), InW4 (Multiplicative.ofAdd (a • dA k)) := by
    intro a k
    rcases zmod2_cases' a with rfl | rfl
    · rw [zero_smul]; exact h0
    · rw [one_smul]; exact (dVec_facts k).1
  induction (Finset.univ : Finset (Fin 15)) using Finset.induction_on with
  | empty => simpa using h0
  | insert k s hk ih =>
    rw [Finset.sum_insert hk]
    exact hW _ _ (hs _ _) ih

theorem ConI_comp (σ : Perm (Fin 6)) (s t : Fin 15 → ZMod 2) :
    ConI s (fun k => t (dPerm σ k)) ↔ ConI (fun k => s (dPerm σ⁻¹ k)) t := by
  unfold ConI
  have e : ∑ k, (s k * t (dPerm σ k)) • dA k =
      ∑ m, (s (dPerm σ⁻¹ m) * t m) • dA (dPerm σ⁻¹ m) := by
    refine Fintype.sum_equiv (dPermE σ) _ _ (fun k => ?_)
    show _ = (s (dPerm σ⁻¹ (dPerm σ k)) * t (dPerm σ k)) • dA (dPerm σ⁻¹ (dPerm σ k))
    rw [dPerm_inv_dPerm]
  have e2 : ∑ m, (s (dPerm σ⁻¹ m) * t m) • dA (dPerm σ⁻¹ m) =
      actA σ⁻¹ (∑ m, (s (dPerm σ⁻¹ m) * t m) • dA m) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [actA_smul, actA_dA]
  rw [e, e2]
  constructor
  · intro h
    have h1 := actA_inv_actA σ⁻¹ (inW4_sum_dA fun m => s (dPerm σ⁻¹ m) * t m)
    rw [inv_inv, h, map_zero] at h1
    exact h1.symm
  · intro h
    rw [h, map_zero]

@[expose] def rEps (ε : Fin 4 → ZMod 2) : Fin 15 → ZMod 2 :=
  ![0, 0, 0, ε 0, ε 0, 0, 0, ε 1, ε 1, 0, ε 2, ε 2, ε 3, ε 3, 0]

@[expose] def c45 : Fin 15 → ZMod 2 := rEps fun _ => 1

@[expose] def cY : Fin 15 → Fin 15 → ZMod 2 :=
  ![![0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0], ![1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0],
    ![1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0], ![1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1],
    ![1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1], ![1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0],
    ![1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0], ![1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    ![1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1], ![0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0],
    ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1], ![0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1],
    ![0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1], ![0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1],
    ![0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0]]

@[expose] def sigY : Fin 15 → Perm (Fin 6) :=
  ![swap 1 5 * swap 0 4 * swap 1 3 * swap 0 2, swap 0 5 * swap 2 4 * swap 0 3 * swap 0 1,
    swap 3 5 * swap 0 4 * swap 0 2 * swap 0 1, swap 0 5 * swap 0 3 * swap 0 2 * swap 0 1,
    swap 0 4 * swap 0 3 * swap 0 2 * swap 0 1, swap 2 1 * swap 1 5 * swap 2 4 * swap 1 3,
    swap 1 3 * swap 3 5 * swap 1 4 * swap 1 2, swap 4 1 * swap 1 5 * swap 1 3 * swap 1 2,
    swap 1 5 * swap 1 4 * swap 1 3 * swap 1 2, swap 3 5 * swap 2 4, swap 2 5 * swap 2 3,
    swap 2 4 * swap 2 3, swap 4 3 * swap 3 5, swap 3 5 * swap 3 4, 1]

theorem sigY_facts : ∀ j : Fin 15, Perm.sign (sigY j) = 1 ∧
    (fun k => c45 (dPerm (sigY j)⁻¹ k)) = cY j := by
  decide +kernel

@[expose] def certEps (ε : Fin 4 → ZMod 2) : List (Perm (Fin 6)) :=
  if ε = ![1, 0, 0, 0] then
    [1, swap 4 5 * swap 0 1, swap 1 0 * swap 0 2, swap 4 5 * swap 2 1 * swap 1 0 * swap 0 3]
  else if ε = ![0, 1, 0, 0] then
    [1, swap 4 5 * swap 1 2, swap 2 1 * swap 1 3, swap 4 5 * swap 0 1]
  else if ε = ![1, 1, 0, 0] then [1, swap 1 3 * swap 0 2]
  else if ε = ![0, 0, 1, 0] then
    [1, swap 4 5 * swap 2 3, swap 4 5 * swap 1 2, swap 0 2 * swap 0 1]
  else if ε = ![1, 0, 1, 0] then [1, swap 2 3 * swap 0 1]
  else if ε = ![0, 1, 1, 0] then [1, swap 2 3 * swap 0 1]
  else if ε = ![1, 1, 1, 0] then
    [1, swap 4 5 * swap 2 3, swap 1 3 * swap 1 2, swap 4 5 * swap 0 3 * swap 0 2 * swap 0 1]
  else if ε = ![0, 0, 0, 1] then
    [1, swap 4 5 * swap 2 3, swap 1 3 * swap 1 2, swap 4 5 * swap 0 3 * swap 0 2 * swap 0 1]
  else if ε = ![1, 0, 0, 1] then [1, swap 2 3 * swap 0 1]
  else if ε = ![0, 1, 0, 1] then [1, swap 2 3 * swap 0 1]
  else if ε = ![1, 1, 0, 1] then
    [1, swap 4 5 * swap 2 3, swap 4 5 * swap 1 2, swap 0 2 * swap 0 1]
  else if ε = ![0, 0, 1, 1] then [1, swap 1 3 * swap 0 2]
  else if ε = ![1, 0, 1, 1] then
    [1, swap 4 5 * swap 1 2, swap 2 1 * swap 1 3, swap 4 5 * swap 0 1]
  else if ε = ![0, 1, 1, 1] then
    [1, swap 4 5 * swap 0 1, swap 1 0 * swap 0 2, swap 4 5 * swap 2 1 * swap 1 0 * swap 0 3]
  else [1]

theorem certEps_facts : ∀ ε : Fin 4 → ZMod 2, ε ≠ 0 →
    (∀ σ ∈ certEps ε, Perm.sign σ = 1) ∧
      ((certEps ε).map fun σ => fun k => rEps ε (dPerm σ⁻¹ k)).sum = c45 := by
  decide +kernel

@[expose] def piC (k : Fin 15) : Fin 15 := dPerm c012⁻¹ k

@[expose] def mkT (a : Fin 8 → ZMod 2) : Fin 15 → ZMod 2 :=
  ![a 0, a 0 + a 1, a 2, a 4, a 6, a 1, a 3, a 5, a 7, a 2 + a 3, a 4 + a 5, a 6 + a 7, 0, 0, 0]

@[expose] def list4 : List (Fin 15 → ZMod 2) :=
  [0, ![0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0],
    ![1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0],
    ![1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0]]

theorem mkT_mem_list4 : ∀ a : Fin 8 → ZMod 2, (∀ j : Fin 15, ConI (cY j) (mkT a)) →
    mkT a ∈ list4 := by
  decide +kernel

theorem act4f_e0123_eq_dVec (σ : Perm (Fin 6)) : act4f σ e0123 = dVec (dPerm σ 14) := by
  rw [← dVec_fourteen, act4f_dVec]

theorem comm_mul_mem_V {G : Type} [Group G] {V : Subgroup G} {q a v : G}
    (hq : q ∈ Subgroup.centralizer (V : Set G)) (hv : v ∈ V) :
    q * (a * v) * q⁻¹ * (a * v)⁻¹ = q * a * q⁻¹ * a⁻¹ := by
  have h : v * q = q * v := Subgroup.mem_centralizer_iff.mp hq v hv
  have h' : v * q⁻¹ = q⁻¹ * v := by
    calc v * q⁻¹ = q⁻¹ * (q * v) * q⁻¹ := by group
      _ = q⁻¹ * (v * q) * q⁻¹ := by rw [h]
      _ = q⁻¹ * v := by group
  calc q * (a * v) * q⁻¹ * (a * v)⁻¹ = q * a * (v * q⁻¹) * v⁻¹ * a⁻¹ := by group
    _ = q * a * (q⁻¹ * v) * v⁻¹ * a⁻¹ := by rw [h']
    _ = q * a * q⁻¹ * a⁻¹ := by group


namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem psi_conj_z (l : ↥(Subgroup.normalizer (V : Set G))) :
    (S.frame.ψ ⟨(l : G) * S.z * (l : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp l.2 S.z).mp S.z_mem_V⟩ : P6) =
      act4f (S.frame.ρ l) e0123 := by
  rw [S.psi_conj l ⟨S.z, S.z_mem_V⟩, S.psi_z]
  rfl

theorem exists_lk (k : Fin 15) : ∃ l : ↥(Subgroup.normalizer (V : Set G)), (l : G) ∈ L ∧
    act4f (S.frame.ρ l) e0123 = dVec k := by
  obtain ⟨σ, hσ, hk⟩ := exists_A6_dVec k
  obtain ⟨l, hlL, hl⟩ := (S.frame.image_L σ).2 (Perm.mem_alternatingGroup.2 hσ)
  exact ⟨l, hlL, by rw [hl, hk]⟩

@[expose] noncomputable def lk (k : Fin 15) : ↥(Subgroup.normalizer (V : Set G)) :=
  Classical.choose (S.exists_lk k)

theorem lk_mem (k : Fin 15) : (S.lk k : G) ∈ L := (Classical.choose_spec (S.exists_lk k)).1

theorem lk_act (k : Fin 15) : act4f (S.frame.ρ (S.lk k)) e0123 = dVec k :=
  (Classical.choose_spec (S.exists_lk k)).2

theorem conj_z_eq_of_act {l l' : ↥(Subgroup.normalizer (V : Set G))}
    (h : act4f (S.frame.ρ l) e0123 = act4f (S.frame.ρ l') e0123) :
    (l : G) * S.z * (l : G)⁻¹ = (l' : G) * S.z * (l' : G)⁻¹ := by
  have h1 := S.psi_conj_z l
  have h2 := S.psi_conj_z l'
  rw [h] at h1
  have := S.frame.ψ.injective (Subtype.ext (h1.trans h2.symm))
  exact congrArg Subtype.val this

open Classical in
@[expose] noncomputable def Fq (u₁ q : G) (k : Fin 15) : ZMod 2 :=
  if q * ((S.lk k : G) * u₁ * (S.lk k : G)⁻¹) * q⁻¹ *
      ((S.lk k : G) * u₁ * (S.lk k : G)⁻¹)⁻¹ = 1 then 0 else 1

theorem Fq_eq_zero_iff {u₁ q : G} {k : Fin 15} : S.Fq u₁ q k = 0 ↔
    q * ((S.lk k : G) * u₁ * (S.lk k : G)⁻¹) * q⁻¹ *
      ((S.lk k : G) * u₁ * (S.lk k : G)⁻¹)⁻¹ = 1 := by
  unfold Fq
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h1 => absurd h1 (by decide), fun h1 => absurd h1 h⟩

theorem Fq_eq_one_iff {u₁ q : G} {k : Fin 15} : S.Fq u₁ q k = 1 ↔
    q * ((S.lk k : G) * u₁ * (S.lk k : G)⁻¹) * q⁻¹ *
      ((S.lk k : G) * u₁ * (S.lk k : G)⁻¹)⁻¹ ≠ 1 := by
  unfold Fq
  split_ifs with h
  · exact ⟨fun h1 => absurd h1 (by decide), fun h1 => absurd h h1⟩
  · exact ⟨fun _ => h, fun _ => rfl⟩

theorem UH_le_G1 : conjClosure S.V3 S.G1 ≤ S.G1 := by
  have hV3 : S.V3 ≤ S.G1 := fun v hv => by
    have : v ∈ Subgroup.centralizer ({S.z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact isElemAbelian_comm S.elemAbelian_V (S.V3_le_V hv) S.z_mem_V
    exact this
  exact conjClosure_le fun h hh v hv => S.G1.mul_mem (S.G1.mul_mem hh (hV3 hv)) (S.G1.inv_mem hh)

theorem mul_z_comm {g : G} (hg : g ∈ S.G1) : g * S.z = S.z * g := by
  have : g ∈ Subgroup.centralizer ({S.z} : Set G) := hg
  exact Subgroup.mem_centralizer_singleton_iff.mp this

theorem z_mul_z : S.z * S.z = 1 := by
  have := S.elemAbelian_V.2 S.z S.z_mem_V
  rwa [sq] at this

theorem pCoreOf_LT_le_centralizer :
    pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (V : Set G) := by
  rw [← S.cT]; exact inf_le_right

section Phi

variable {ρ : ↥S.G1 →* Perm (Fin 6)}
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative ↥(evenWeight 6)}
  (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ fsuV1 T V)
  (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
    Multiplicative.toAdd (β v) = permWeight 6 (ρ h) (Multiplicative.toAdd (β u)))
  {u₁ : G} (hu₁ : u₁ ∈ S.U1c β) (hu₁V : u₁ ∉ fsuV1 T V)
include hβk hu₁ hu₁V

theorem eq_of_mem_U1c {u : G} (hu : u ∈ S.U1c β) (huV : u ∉ fsuV1 T V) :
    u = u₁ ∨ u = u₁ * S.z := by
  obtain ⟨huU, hu'⟩ := (S.mem_U1c).1 hu
  obtain ⟨hu₁U, hu₁'⟩ := (S.mem_U1c).1 hu₁
  have hne : ∀ (w : G) (hw : w ∈ conjClosure S.V3 S.G1), w ∉ fsuV1 T V →
      Multiplicative.toAdd (β ⟨w, hw⟩) ∈ constWeight 6 →
      Multiplicative.toAdd (β ⟨w, hw⟩) = onesEv := by
    intro w hw hwV hwc
    rcases (mem_constWeight_iff _).1 hwc with h | h
    · exact absurd ((hβk ⟨w, hw⟩).1 (Multiplicative.toAdd.injective (by rw [h, toAdd_one])))
        hwV
    · exact h
  have h1 := hne u huU huV hu'
  have h2 := hne u₁ hu₁U hu₁V hu₁'
  have hm : u₁⁻¹ * u ∈ conjClosure S.V3 S.G1 :=
    (conjClosure S.V3 S.G1).mul_mem ((conjClosure S.V3 S.G1).inv_mem hu₁U) huU
  have hk : u₁⁻¹ * u ∈ fsuV1 T V := by
    refine (hβk ⟨_, hm⟩).1 ?_
    have e : (⟨u₁⁻¹ * u, hm⟩ : ↥(conjClosure S.V3 S.G1)) = (⟨u₁, hu₁U⟩)⁻¹ * ⟨u, huU⟩ := rfl
    rw [e, map_mul, map_inv]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, h1, h2, neg_add_cancel, toAdd_one]
  rcases (S.mem_V1_iff).1 hk with h | h
  · left
    calc u = u₁ * (u₁⁻¹ * u) := by group
      _ = u₁ := by rw [h, mul_one]
  · right
    calc u = u₁ * (u₁⁻¹ * u) := by group
      _ = u₁ * S.z := by rw [h]

include hβe in
theorem conj_u1_eq {m : G} (hm : m ∈ S.G1) : m * u₁ * m⁻¹ = u₁ ∨ m * u₁ * m⁻¹ = u₁ * S.z := by
  refine S.eq_of_mem_U1c hβk hu₁ hu₁V ?_ ?_
  · exact (Subgroup.mem_normalizer_iff.mp (S.G1_le_normalizer_U1c hβe hβk hm) u₁).mp hu₁
  · intro h
    apply hu₁V
    have hmV : m ∈ Subgroup.normalizer (fsuV1 T V : Set G) := by
      rw [S.normalizer_V1]; exact hm
    exact (Subgroup.mem_normalizer_iff.mp hmV u₁).mpr h

include hβe in
theorem comm_conj_u1_eq {q : G} (hq : q ∈ Subgroup.centralizer (V : Set G))
    {l l' : ↥(Subgroup.normalizer (V : Set G))}
    (h : (l : G) * S.z * (l : G)⁻¹ = (l' : G) * S.z * (l' : G)⁻¹) :
    q * ((l' : G) * u₁ * (l' : G)⁻¹) * q⁻¹ * ((l' : G) * u₁ * (l' : G)⁻¹)⁻¹ =
      q * ((l : G) * u₁ * (l : G)⁻¹) * q⁻¹ * ((l : G) * u₁ * (l : G)⁻¹)⁻¹ := by
  set m : G := (l : G)⁻¹ * l' with hm
  have hmz : m * S.z * m⁻¹ = S.z := by
    calc m * S.z * m⁻¹ = (l : G)⁻¹ * ((l' : G) * S.z * (l' : G)⁻¹) * l := by rw [hm]; group
      _ = (l : G)⁻¹ * ((l : G) * S.z * (l : G)⁻¹) * l := by rw [h]
      _ = S.z := by group
  have hmG : m ∈ S.G1 := by
    show m ∈ Subgroup.centralizer ({S.z} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc m * S.z = m * S.z * m⁻¹ * m := by group
      _ = S.z * m := by rw [hmz]
  have e : (l' : G) * u₁ * (l' : G)⁻¹ = (l : G) * (m * u₁ * m⁻¹) * (l : G)⁻¹ := by
    rw [hm]; group
  have hvV : (l : G) * S.z * (l : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp l.2 S.z).mp S.z_mem_V
  rw [e]
  rcases S.conj_u1_eq hβk hβe hu₁ hu₁V hmG with h1 | h1
  · rw [h1]
  · rw [h1]
    have e2 : (l : G) * (u₁ * S.z) * (l : G)⁻¹ =
        ((l : G) * u₁ * (l : G)⁻¹) * ((l : G) * S.z * (l : G)⁻¹) := by group
    rw [e2, comm_mul_mem_V hq hvV]

include hβe in
theorem Fq_eq_zero_iff_of_act {q : G} (hq : q ∈ Subgroup.centralizer (V : Set G))
    {l : ↥(Subgroup.normalizer (V : Set G))} {k : Fin 15}
    (hl : act4f (S.frame.ρ l) e0123 = dVec k) :
    S.Fq u₁ q k = 0 ↔
      q * ((l : G) * u₁ * (l : G)⁻¹) * q⁻¹ * ((l : G) * u₁ * (l : G)⁻¹)⁻¹ = 1 := by
  rw [S.Fq_eq_zero_iff, S.comm_conj_u1_eq hβk hβe hu₁ hu₁V hq
    (S.conj_z_eq_of_act (hl.trans (S.lk_act k).symm))]

omit hu₁V in
include hβe in
theorem comm_conj_u1_mem {q : G} (hq : q ∈ pCoreOf 2 (L ⊔ T))
    {l : G} (hl : l ∈ L) :
    q * (l * u₁ * l⁻¹) * q⁻¹ * (l * u₁ * l⁻¹)⁻¹ = 1 ∨
      q * (l * u₁ * l⁻¹) * q⁻¹ * (l * u₁ * l⁻¹)⁻¹ = l * S.z * l⁻¹ := by
  have hq' : l⁻¹ * q * l⁻¹⁻¹ ∈ pCoreOf 2 (L ⊔ T) :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (L ⊔ T)
      (Subgroup.mem_sup_left (L.inv_mem hl))) q).mp hq
  rw [inv_inv] at hq'
  have hqT : l⁻¹ * q * l ∈ T := pCoreOf_le_of_sylow S.h13.sylow le_sup_right hq'
  have hqG : l⁻¹ * q * l ∈ S.G1 := by
    have := S.T_le_NV1 hqT
    rwa [S.normalizer_V1] at this
  have hc := S.comm_mem_V1_of_U1c hβe hβk hqG hu₁
  have e : q * (l * u₁ * l⁻¹) * q⁻¹ * (l * u₁ * l⁻¹)⁻¹ =
      l * ((l⁻¹ * q * l) * u₁ * (l⁻¹ * q * l)⁻¹ * u₁⁻¹) * l⁻¹ := by group
  rw [e]
  rcases (S.mem_V1_iff).1 hc with h | h
  · left; rw [h]; group
  · right; rw [h]

omit hu₁V in
include hβe in
theorem Fq_mul {q₁ q₂ : G} (h₁ : q₁ ∈ pCoreOf 2 (L ⊔ T))
    (h₂ : q₂ ∈ pCoreOf 2 (L ⊔ T)) (k : Fin 15) :
    S.Fq u₁ (q₁ * q₂) k = S.Fq u₁ q₁ k + S.Fq u₁ q₂ k := by
  set l : G := (S.lk k : G) with hl
  set a : G := l * u₁ * l⁻¹ with ha
  set v : G := l * S.z * l⁻¹ with hv
  have hlL : l ∈ L := S.lk_mem k
  have hvV : v ∈ V := (Subgroup.mem_normalizer_iff.mp (S.lk k).2 S.z).mp S.z_mem_V
  have hv1 : v ≠ 1 := by
    intro h
    apply S.z_ne_one
    calc S.z = l⁻¹ * v * l := by rw [hv]; group
      _ = 1 := by rw [h]; group
  have hvv : v * v = 1 := by
    rw [hv]
    calc l * S.z * l⁻¹ * (l * S.z * l⁻¹) = l * (S.z * S.z) * l⁻¹ := by group
      _ = 1 := by rw [S.z_mul_z]; group
  have hQC : pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (V : Set G) := by
    rw [← S.cT]; exact inf_le_right
  have hc₁ := S.comm_conj_u1_mem hβk hβe hu₁ h₁ hlL
  have hc₂ := S.comm_conj_u1_mem hβk hβe hu₁ h₂ hlL
  rw [← ha, ← hv] at hc₁ hc₂
  have hmul : (q₁ * q₂) * a * (q₁ * q₂)⁻¹ * a⁻¹ =
      (q₂ * a * q₂⁻¹ * a⁻¹) * (q₁ * a * q₁⁻¹ * a⁻¹) := by
    have hX : q₂ * a * q₂⁻¹ * a⁻¹ ∈ V := by
      rcases hc₂ with h | h <;> rw [h]
      · exact V.one_mem
      · exact hvV
    have hcomm : (q₂ * a * q₂⁻¹ * a⁻¹) * q₁ = q₁ * (q₂ * a * q₂⁻¹ * a⁻¹) :=
      Subgroup.mem_centralizer_iff.mp (hQC h₁) _ hX
    calc (q₁ * q₂) * a * (q₁ * q₂)⁻¹ * a⁻¹ =
        q₁ * (q₂ * a * q₂⁻¹ * a⁻¹) * q₁⁻¹ * (q₁ * a * q₁⁻¹ * a⁻¹) := by group
      _ = (q₂ * a * q₂⁻¹ * a⁻¹) * q₁ * q₁⁻¹ * (q₁ * a * q₁⁻¹ * a⁻¹) := by rw [hcomm]
      _ = (q₂ * a * q₂⁻¹ * a⁻¹) * (q₁ * a * q₁⁻¹ * a⁻¹) := by group
  have hval : ∀ q : G, (q * a * q⁻¹ * a⁻¹ = 1 → S.Fq u₁ q k = 0) ∧
      (q * a * q⁻¹ * a⁻¹ ≠ 1 → S.Fq u₁ q k = 1) :=
    fun q => ⟨fun h => S.Fq_eq_zero_iff.2 h, fun h => S.Fq_eq_one_iff.2 h⟩
  rcases hc₁ with h | h <;> rcases hc₂ with h' | h'
  · rw [(hval _).1 (by rw [hmul, h, h']; group), (hval _).1 h, (hval _).1 h']; rfl
  · rw [(hval _).2 (by rw [hmul, h, h', mul_one]; exact hv1), (hval _).1 h,
      (hval _).2 (by rw [h']; exact hv1)]; rfl
  · rw [(hval _).2 (by rw [hmul, h, h', one_mul]; exact hv1), (hval _).2 (by rw [h]; exact hv1),
      (hval _).1 h']; rfl
  · rw [(hval _).1 (by rw [hmul, h, h']; exact hvv), (hval _).2 (by rw [h]; exact hv1),
      (hval _).2 (by rw [h']; exact hv1)]; rfl

include hβe in
theorem Fq_eq_zero_iff_mem_centralizer {q : G}
    (hq : q ∈ pCoreOf 2 (L ⊔ T)) :
    (∀ k, S.Fq u₁ q k = 0) ↔ q ∈ Subgroup.centralizer (S.U0c β : Set G) := by
  have hQC := S.pCoreOf_LT_le_centralizer hq
  constructor
  · intro h
    have hgen : ∀ l ∈ L, ∀ u ∈ S.U1c β, l * u * l⁻¹ ∈ Subgroup.centralizer ({q} : Set G) := by
      intro l hl u hu
      rw [Subgroup.mem_centralizer_singleton_iff]
      set lN : ↥(Subgroup.normalizer (V : Set G)) := ⟨l, S.frame.L_le hl⟩ with hlN
      have hlz : l * S.z * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (S.frame.L_le hl) S.z).mp
        S.z_mem_V
      have hcomm : q * (l * u₁ * l⁻¹) * q⁻¹ * (l * u₁ * l⁻¹)⁻¹ = 1 :=
        (S.Fq_eq_zero_iff_of_act hβk hβe hu₁ hu₁V hQC (l := lN) (act4f_e0123_eq_dVec _)).1 (h _)
      have hcomm' : (l * u₁ * l⁻¹) * q = q * (l * u₁ * l⁻¹) := by
        calc (l * u₁ * l⁻¹) * q =
            (q * (l * u₁ * l⁻¹) * q⁻¹ * (l * u₁ * l⁻¹)⁻¹)⁻¹ * q * (l * u₁ * l⁻¹) := by group
          _ = q * (l * u₁ * l⁻¹) := by rw [hcomm]; group
      by_cases huV : u ∈ fsuV1 T V
      · have hV : l * u * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (S.frame.L_le hl) u).mp
          (S.V1_le_V3.trans S.V3_le_V huV)
        exact Subgroup.mem_centralizer_iff.mp hQC _ hV
      · rcases S.eq_of_mem_U1c hβk hu₁ hu₁V hu huV with rfl | rfl
        · exact hcomm'
        · have e : l * (u₁ * S.z) * l⁻¹ = (l * u₁ * l⁻¹) * (l * S.z * l⁻¹) := by group
          rw [e]
          have hz : (l * S.z * l⁻¹) * q = q * (l * S.z * l⁻¹) :=
            Subgroup.mem_centralizer_iff.mp hQC _ hlz
          calc (l * u₁ * l⁻¹) * (l * S.z * l⁻¹) * q =
              (l * u₁ * l⁻¹) * ((l * S.z * l⁻¹) * q) := by group
            _ = (l * u₁ * l⁻¹) * q * (l * S.z * l⁻¹) := by rw [hz]; group
            _ = q * (l * u₁ * l⁻¹) * (l * S.z * l⁻¹) := by rw [hcomm']
            _ = q * ((l * u₁ * l⁻¹) * (l * S.z * l⁻¹)) := by group
    have hle : S.U0c β ≤ Subgroup.centralizer ({q} : Set G) := conjClosure_le hgen
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy))
  · intro h k
    rw [S.Fq_eq_zero_iff]
    have hmem : (S.lk k : G) * u₁ * (S.lk k : G)⁻¹ ∈ S.U0c β := mem_conjClosure (S.lk_mem k) hu₁
    have hc := Subgroup.mem_centralizer_iff.mp h _ hmem
    rw [← hc]
    group

include hβe in
theorem Fq_conj {q : G} (hq : q ∈ pCoreOf 2 (L ⊔ T))
    {l : ↥(Subgroup.normalizer (V : Set G))} (k : Fin 15) :
    S.Fq u₁ ((l : G) * q * (l : G)⁻¹) k = S.Fq u₁ q (dPerm (S.frame.ρ l)⁻¹ k) := by
  have hQC := S.pCoreOf_LT_le_centralizer hq
  set m : ↥(Subgroup.normalizer (V : Set G)) := l⁻¹ * S.lk k with hmdef
  have hm : act4f (S.frame.ρ m) e0123 = dVec (dPerm (S.frame.ρ l)⁻¹ k) := by
    rw [hmdef, map_mul, map_inv, act4f_mul, S.lk_act, act4f_dVec]
  have e2 := S.Fq_eq_zero_iff_of_act hβk hβe hu₁ hu₁V hQC hm
  have key : (l : G) * q * (l : G)⁻¹ * ((S.lk k : G) * u₁ * (S.lk k : G)⁻¹) *
      ((l : G) * q * (l : G)⁻¹)⁻¹ * ((S.lk k : G) * u₁ * (S.lk k : G)⁻¹)⁻¹ =
      (l : G) * (q * ((m : G) * u₁ * (m : G)⁻¹) * q⁻¹ * ((m : G) * u₁ * (m : G)⁻¹)⁻¹) *
        (l : G)⁻¹ := by
    rw [hmdef]; simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
  rcases zmod2_cases' (S.Fq u₁ q (dPerm (S.frame.ρ l)⁻¹ k)) with h | h
  · rw [h, S.Fq_eq_zero_iff, key, e2.1 h]; group
  · rw [h, S.Fq_eq_one_iff, key]
    intro h1
    have h2 : q * ((m : G) * u₁ * (m : G)⁻¹) * q⁻¹ * ((m : G) * u₁ * (m : G)⁻¹)⁻¹ = 1 := by
      calc _ = (l : G)⁻¹ * ((l : G) * (q * ((m : G) * u₁ * (m : G)⁻¹) * q⁻¹ *
            ((m : G) * u₁ * (m : G)⁻¹)⁻¹) * (l : G)⁻¹) * l := by group
        _ = 1 := by rw [h1]; group
    rw [e2.2 h2] at h
    exact absurd h (by decide)

omit hu₁V in
include hβe in
theorem comm_conj_u1_mem_V {q : G} (hq : q ∈ pCoreOf 2 (L ⊔ T))
    {l : ↥(Subgroup.normalizer (V : Set G))} (hl : (l : G) ∈ L) :
    q * ((l : G) * u₁ * (l : G)⁻¹) * q⁻¹ * ((l : G) * u₁ * (l : G)⁻¹)⁻¹ ∈ V := by
  rcases S.comm_conj_u1_mem hβk hβe hu₁ hq hl with h | h
  · rw [h]; exact V.one_mem
  · rw [h]; exact (Subgroup.mem_normalizer_iff.mp l.2 S.z).mp S.z_mem_V

include hβe in
theorem psi_comm_eq {q : G} (hq : q ∈ pCoreOf 2 (L ⊔ T))
    {l : ↥(Subgroup.normalizer (V : Set G))} (hl : (l : G) ∈ L) {k : Fin 15}
    (hlk : act4f (S.frame.ρ l) e0123 = dVec k)
    (hmem : q * ((l : G) * u₁ * (l : G)⁻¹) * q⁻¹ * ((l : G) * u₁ * (l : G)⁻¹)⁻¹ ∈ V) :
    Multiplicative.toAdd (S.frame.ψ ⟨_, hmem⟩ : P6) = S.Fq u₁ q k • dA k := by
  have hQC := S.pCoreOf_LT_le_centralizer hq
  have e := S.Fq_eq_zero_iff_of_act hβk hβe hu₁ hu₁V hQC hlk
  rcases S.comm_conj_u1_mem hβk hβe hu₁ hq hl with h | h
  · have h0 : S.Fq u₁ q k = 0 := e.2 h
    rw [h0, zero_smul]
    have e1 : (⟨_, hmem⟩ : ↥V) = 1 := Subtype.ext h
    rw [e1, map_one]
    rfl
  · have hV : (l : G) * S.z * (l : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp l.2 S.z).mp S.z_mem_V
    have h1 : S.Fq u₁ q k = 1 := by
      rcases zmod2_cases' (S.Fq u₁ q k) with h0 | h0
      · exfalso
        apply S.z_ne_one
        have h2 := e.1 h0
        rw [h] at h2
        calc S.z = (l : G)⁻¹ * ((l : G) * S.z * (l : G)⁻¹) * l := by group
          _ = 1 := by rw [h2]; group
      · exact h0
    rw [h1, one_smul]
    have e1 : (⟨_, hmem⟩ : ↥V) = ⟨_, hV⟩ := Subtype.ext h
    rw [e1]
    have h3 := S.psi_conj_z l
    rw [hlk] at h3
    rw [h3]
    rfl

end Phi

end Setting4

end CFSG.Quasithin.H13.A6
