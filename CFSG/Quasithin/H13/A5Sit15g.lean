module

public import CFSG.Quasithin.H13.A5Sit15f
public import CFSG.Quasithin.H13.A5SitSp4

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.A5.Orth

theorem zmod2_eq_of_iff : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b := by
  decide

theorem conj_pow_eq {G : Type} [Group G] {y q w : G} (hq : y * q * y⁻¹ = w * q)
    (hyw : y * w = w * y) (k : ℕ) : y ^ k * q * (y ^ k)⁻¹ = w ^ k * q := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hykw : y * w ^ k = w ^ k * y := (Commute.pow_right hyw k).eq
    calc y ^ (k + 1) * q * (y ^ (k + 1))⁻¹ = y * (y ^ k * q * (y ^ k)⁻¹) * y⁻¹ := by
          rw [pow_succ']
          group
      _ = y * (w ^ k * q) * y⁻¹ := by rw [ih]
      _ = (y * w ^ k) * (y⁻¹ * (y * q * y⁻¹)) := by group
      _ = (w ^ k * y) * (y⁻¹ * (w * q)) := by rw [hykw, hq]
      _ = w ^ (k + 1) * q := by
          rw [pow_succ]
          group

theorem eq_one_of_conj {G : Type} [Group G] {y q w : G} (hodd : Odd (orderOf y))
    (hq : y * q * y⁻¹ = w * q) (hyw : y * w = w * y) (hw4 : w ^ 4 = 1) : w = 1 := by
  have h := conj_pow_eq hq hyw (orderOf y)
  rw [pow_orderOf_eq_one, inv_one, one_mul, mul_one] at h
  have hwm : w ^ orderOf y = 1 := by
    have h' : w ^ orderOf y * q = 1 * q := by rw [one_mul, ← h]
    exact mul_right_cancel h'
  have hd : orderOf w ∣ Nat.gcd (orderOf y) 4 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hwm) (orderOf_dvd_of_pow_eq_one hw4)
  have hcop : Nat.Coprime (orderOf y) 4 := by
    have := hodd.coprime_two_right
    exact Nat.Coprime.pow_right 2 this
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact hd

namespace A5SitPf15

variable {G : Type} [Group G] [Finite G] {T V V₁ V₃ L₁ H : Subgroup G}
  {S : A5Sit G T V V₁ V₃ L₁ H} {SY : A5SitY S L₁} (P : A5SitPf15 S SY)
include P

theorem comm_iff_Bf (u v : ↥(conjClosure V₃ H)) :
    (u : G) * v = v * u ↔
      Bf (Multiplicative.toAdd (P.C.θ u)) (Multiplicative.toAdd (P.C.θ v)) = 0 := by
  have hvH : (v : G) ∈ H := S.U_le_Q.trans (pCoreOf_le 2 H) v.2
  set d : G := (v : G)⁻¹ * (u : G)⁻¹ * v * u with hd
  have hdU : d ∈ conjClosure V₃ H :=
    (conjClosure V₃ H).mul_mem ((conjClosure V₃ H).mul_mem ((conjClosure V₃ H).mul_mem
      ((conjClosure V₃ H).inv_mem v.2) ((conjClosure V₃ H).inv_mem u.2)) v.2) u.2
  have hdθ : P.C.θ ⟨d, hdU⟩ = 1 := by
    have e : (⟨d, hdU⟩ : ↥(conjClosure V₃ H)) = v⁻¹ * u⁻¹ * v * u := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_inv, toAdd_one]
    abel
  have hd1 : d = 1 ∨ d = P.C.z := (P.C.ker_iff ⟨d, hdU⟩).1 hdθ
  have hdv : d * v = v * d := by
    rcases hd1 with h | h <;> rw [h]
    · simp
    · exact (P.comm_z hvH).symm
  have hvu : (v : G) * u = u * v * d := by
    rw [hd]
    group
  have hsq : ((u : G) * v) ^ 2 = (u : G) ^ 2 * (v : G) ^ 2 * d := by
    calc ((u : G) * v) ^ 2 = u * (v * u) * v := by rw [pow_two]; group
      _ = u * (u * v * d) * v := by rw [hvu]
      _ = u * u * v * (d * v) := by group
      _ = u * u * v * (v * d) := by rw [hdv]
      _ = (u : G) ^ 2 * (v : G) ^ 2 * d := by rw [pow_two, pow_two]; group
  have hcomm : (u : G) * v = v * u ↔ d = 1 := by
    constructor
    · intro h
      have e : (v : G)⁻¹ * (u : G)⁻¹ * v * u = (v : G)⁻¹ * (u : G)⁻¹ * (v * u) := by group
      rw [hd, e, ← h]
      group
    · intro h
      rw [hvu, h, mul_one]
  have hθuv : Multiplicative.toAdd (P.C.θ (u * v)) =
      Multiplicative.toAdd (P.C.θ u) + Multiplicative.toAdd (P.C.θ v) := by
    rw [map_mul, toAdd_mul]
  have hzz : P.C.z * P.C.z = 1 := by
    rw [← pow_two]
    exact P.C.z_sq
  rw [hcomm, Bf_eq, ← hθuv]
  have huv2 := P.C.sq (u * v)
  rw [Subgroup.coe_mul] at huv2
  rcases P.C.sq u with ⟨ha, hu2⟩ | ⟨ha, hu2⟩ <;> rcases P.C.sq v with ⟨hb, hv2⟩ | ⟨hb, hv2⟩ <;>
    rcases huv2 with ⟨hc, hc2⟩ | ⟨hc, hc2⟩ <;> rw [ha, hb, hc] <;>
    rw [hc2, hu2, hv2] at hsq <;> rcases hd1 with h | h <;> rw [h] at hsq ⊢ <;>
    simp only [one_mul, mul_one, hzz] at hsq <;>
    first
    | exact absurd hsq P.C.z_ne
    | exact absurd hsq.symm P.C.z_ne
    | exact ⟨fun _ => by decide, fun _ => rfl⟩
    | exact ⟨fun hh => absurd hh P.C.z_ne, fun hh => absurd hh (by decide)⟩

variable (hQ : Nat.card (pCoreOf 2 H) = 64)
include hQ

theorem commQ_iff_Bf (q₁ q₂ : ↥(pCoreOf 2 H)) :
    (q₁ : G) * q₂ = q₂ * q₁ ↔
      Bf (Multiplicative.toAdd (P.thetaQ hQ q₁)) (Multiplicative.toAdd (P.thetaQ hQ q₂)) = 0 := by
  obtain ⟨u₁, hu₁, j₁, hj₁, h₁⟩ := P.decomp hQ q₁.2
  obtain ⟨u₂, hu₂, j₂, hj₂, h₂⟩ := P.decomp hQ q₂.2
  have e₁ : P.thetaQ hQ q₁ = P.C.θ ⟨u₁, hu₁⟩ := P.thetaQ_eq hQ q₁.2 hu₁ hj₁ h₁
  have e₂ : P.thetaQ hQ q₂ = P.C.θ ⟨u₂, hu₂⟩ := P.thetaQ_eq hQ q₂.2 hu₂ hj₂ h₂
  rw [e₁, e₂, ← P.comm_iff_Bf ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩, h₁, h₂]
  have c1 : j₁ * u₂ = u₂ * j₁ := (Subgroup.mem_centralizer_iff.mp hj₁.2 u₂ hu₂).symm
  have c2 : j₂ * u₁ = u₁ * j₂ := (Subgroup.mem_centralizer_iff.mp hj₂.2 u₁ hu₁).symm
  have c3 : j₂ * j₁ = j₁ * j₂ := P.Z1_comm hQ hj₂ hj₁
  have e1 : u₁ * j₁ * (u₂ * j₂) = u₁ * u₂ * (j₁ * j₂) := by
    calc u₁ * j₁ * (u₂ * j₂) = u₁ * (j₁ * u₂) * j₂ := by group
      _ = u₁ * (u₂ * j₁) * j₂ := by rw [c1]
      _ = u₁ * u₂ * (j₁ * j₂) := by group
  have e2 : u₂ * j₂ * (u₁ * j₁) = u₂ * u₁ * (j₁ * j₂) := by
    calc u₂ * j₂ * (u₁ * j₁) = u₂ * (j₂ * u₁) * j₁ := by group
      _ = u₂ * (u₁ * j₂) * j₁ := by rw [c2]
      _ = u₂ * u₁ * (j₂ * j₁) := by group
      _ = u₂ * u₁ * (j₁ * j₂) := by rw [c3]
  rw [e1, e2]
  exact ⟨fun h => mul_right_cancel h, fun h => by rw [h]⟩

theorem normalizer_le_Z1 :
    Subgroup.normalizer (pCoreOf 2 H : Set G) ≤ Subgroup.normalizer (P.Z1 : Set G) := by
  refine A5.le_normalizer_of_forall_conj_mem fun x hx j hj => ?_
  rw [P.Z1_eq_center hQ] at hj ⊢
  obtain ⟨hjQ, hjc⟩ := hj
  refine ⟨(Subgroup.mem_normalizer_iff.mp hx j).mp hjQ,
    Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩
  have hq' : x⁻¹ * q * x⁻¹⁻¹ ∈ pCoreOf 2 H :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) q).mp hq
  rw [inv_inv] at hq'
  have h := Subgroup.mem_centralizer_iff.mp hjc _ hq'
  calc q * (x * j * x⁻¹) = x * ((x⁻¹ * q * x) * j) * x⁻¹ := by group
    _ = x * (j * (x⁻¹ * q * x)) * x⁻¹ := by rw [h]
    _ = x * j * x⁻¹ * q := by group

theorem ker_le_ker_conj {x : G} (hx : x ∈ Subgroup.normalizer (pCoreOf 2 H : Set G)) :
    (P.thetaQ hQ).ker ≤ ((P.thetaQ hQ).comp (Q8Coords.conjHom hx)).ker := by
  intro q hq
  rw [MonoidHom.mem_ker, P.thetaQ_eq_one_iff] at hq
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, P.thetaQ_eq_one_iff, Q8Coords.coe_conjHom]
  exact (Subgroup.mem_normalizer_iff.mp (P.normalizer_le_Z1 hQ hx) q).mp hq

@[expose] noncomputable def actHomQ {x : G} (hx : x ∈ Subgroup.normalizer (pCoreOf 2 H : Set G)) :
    Multiplicative V4 →* Multiplicative V4 :=
  (P.thetaQ hQ).liftOfRightInverse (Function.surjInv (P.thetaQ_surj hQ))
    (Function.rightInverse_surjInv (P.thetaQ_surj hQ))
    ⟨(P.thetaQ hQ).comp (Q8Coords.conjHom hx), P.ker_le_ker_conj hQ hx⟩

theorem actHomQ_θ {x : G} (hx : x ∈ Subgroup.normalizer (pCoreOf 2 H : Set G))
    (q : ↥(pCoreOf 2 H)) :
    P.actHomQ hQ hx (P.thetaQ hQ q) = P.thetaQ hQ (Q8Coords.conjHom hx q) :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ q

theorem actHomQ_injective {x : G} (hx : x ∈ Subgroup.normalizer (pCoreOf 2 H : Set G)) :
    Function.Injective (P.actHomQ hQ hx) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  obtain ⟨q, rfl⟩ := P.thetaQ_surj hQ w
  rw [P.actHomQ_θ, P.thetaQ_eq_one_iff, Q8Coords.coe_conjHom] at hw
  rw [P.thetaQ_eq_one_iff]
  have h := (Subgroup.mem_normalizer_iff.mp
    (P.normalizer_le_Z1 hQ (Subgroup.inv_mem _ hx)) _).mp hw
  have e : x⁻¹ * (x * (q : G) * x⁻¹) * x⁻¹⁻¹ = q := by group
  rwa [e] at h

@[expose] noncomputable def actAutQ {x : G}
    (hx : x ∈ Subgroup.normalizer (pCoreOf 2 H : Set G)) : MulAut (Multiplicative V4) :=
  MulEquiv.ofBijective (P.actHomQ hQ hx)
    (Finite.injective_iff_bijective.mp (P.actHomQ_injective hQ hx))

theorem actAutQ_θ {x : G} (hx : x ∈ Subgroup.normalizer (pCoreOf 2 H : Set G))
    (q : ↥(pCoreOf 2 H)) :
    P.actAutQ hQ hx (P.thetaQ hQ q) = P.thetaQ hQ (Q8Coords.conjHom hx q) :=
  P.actHomQ_θ hQ hx q

theorem actAutQ_one (h1 : (1 : G) ∈ Subgroup.normalizer (pCoreOf 2 H : Set G)) :
    P.actAutQ hQ h1 = 1 := by
  apply MulEquiv.ext
  intro w
  obtain ⟨q, rfl⟩ := P.thetaQ_surj hQ w
  rw [P.actAutQ_θ, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  simp

theorem actAutQ_mul {x y : G} (hx : x ∈ Subgroup.normalizer (pCoreOf 2 H : Set G))
    (hy : y ∈ Subgroup.normalizer (pCoreOf 2 H : Set G))
    (hxy : x * y ∈ Subgroup.normalizer (pCoreOf 2 H : Set G)) :
    P.actAutQ hQ hxy = P.actAutQ hQ hx * P.actAutQ hQ hy := by
  apply MulEquiv.ext
  intro w
  obtain ⟨q, rfl⟩ := P.thetaQ_surj hQ w
  rw [MulAut.mul_apply, P.actAutQ_θ, P.actAutQ_θ, P.actAutQ_θ]
  congr 1
  apply Subtype.ext
  simp only [Q8Coords.coe_conjHom]
  group

@[expose] noncomputable def actQ (X : Subgroup G)
    (hX : X ≤ Subgroup.normalizer (pCoreOf 2 H : Set G)) : ↥X →* MulAut (Multiplicative V4) where
  toFun x := P.actAutQ hQ (hX x.2)
  map_one' := P.actAutQ_one hQ _
  map_mul' _ _ := P.actAutQ_mul hQ _ _ _

theorem actQ_θ (X : Subgroup G) (hX : X ≤ Subgroup.normalizer (pCoreOf 2 H : Set G))
    (x : ↥X) (q : ↥(pCoreOf 2 H)) :
    P.actQ hQ X hX x (P.thetaQ hQ q) = P.thetaQ hQ (Q8Coords.conjHom (hX x.2) q) :=
  P.actAutQ_θ hQ _ q

theorem actQ_mem_Spq (X : Subgroup G) (hX : X ≤ Subgroup.normalizer (pCoreOf 2 H : Set G))
    (x : ↥X) : P.actQ hQ X hX x ∈ Spq := by
  intro v w
  obtain ⟨q₁, hq₁⟩ := P.thetaQ_surj hQ (Multiplicative.ofAdd v)
  obtain ⟨q₂, hq₂⟩ := P.thetaQ_surj hQ (Multiplicative.ofAdd w)
  rw [← hq₁, ← hq₂, P.actQ_θ, P.actQ_θ]
  have hv : v = Multiplicative.toAdd (P.thetaQ hQ q₁) := by rw [hq₁]; rfl
  have hw : w = Multiplicative.toAdd (P.thetaQ hQ q₂) := by rw [hq₂]; rfl
  rw [hv, hw]
  apply zmod2_eq_of_iff
  rw [← P.commQ_iff_Bf hQ, ← P.commQ_iff_Bf hQ, Q8Coords.coe_conjHom, Q8Coords.coe_conjHom]
  set a : G := (x : G) with ha
  constructor
  · intro h
    have e : (q₁ : G) * q₂ = a⁻¹ * ((a * q₁ * a⁻¹) * (a * q₂ * a⁻¹)) * a := by group
    rw [e, h]
    group
  · intro h
    have e : a * q₁ * a⁻¹ * (a * q₂ * a⁻¹) = a * (q₁ * q₂) * a⁻¹ := by group
    rw [e, h]
    group

theorem actQ_H (x : ↥H) : P.actQ hQ H (le_normalizer_pCoreOf 2 H) x = P.Φ x := by
  apply MulEquiv.ext
  intro w
  obtain ⟨u, rfl⟩ := P.C.θ_surj w
  have hxu : (x : G) * u * (x : G)⁻¹ ∈ conjClosure V₃ H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V₃ H x.2) u).mp u.2
  have e1 : (Q8Coords.conjHom ((le_normalizer_pCoreOf 2 H) x.2) ⟨u, S.U_le_Q u.2⟩ :
      ↥(pCoreOf 2 H)) = ⟨(x : G) * u * (x : G)⁻¹, S.U_le_Q hxu⟩ := rfl
  have h1 : P.actQ hQ H (le_normalizer_pCoreOf 2 H) x (P.C.θ u) =
      P.C.θ ⟨(x : G) * u * (x : G)⁻¹, hxu⟩ := by
    rw [← P.thetaQ_U hQ u, P.actQ_θ, e1, P.thetaQ_U hQ ⟨_, hxu⟩]
  have h2 : P.Φ x (P.C.θ u) = P.C.θ ⟨(x : G) * u * (x : G)⁻¹, hxu⟩ := by
    unfold Φ
    rw [Q8Coords.act_θ]
    rfl
  rw [h1, h2]

theorem comm_of_odd {y : G} (hyN : y ∈ Subgroup.normalizer (pCoreOf 2 H : Set G))
    (hyz : y * P.C.z = P.C.z * y) (hodd : Odd (orderOf y))
    (htriv : ∀ q ∈ pCoreOf 2 H, y * q * y⁻¹ * q⁻¹ ∈ P.Z1) :
    ∀ q ∈ pCoreOf 2 H, y * q = q * y := by
  have hyZ : y ∈ Subgroup.normalizer (P.Z1 : Set G) := P.normalizer_le_Z1 hQ hyN
  have hyV1 : ∀ v ∈ V₁, y * v = v * y := by
    intro v hv
    rcases (P.Cz v).1 hv with rfl | rfl
    · simp
    · exact hyz
  have hconjV1 : ∀ v ∈ V₁, y * v * y⁻¹ = v := fun v hv => by
    rw [hyV1 v hv, mul_inv_cancel_right]
  have hV1Z : V₁ ≤ P.Z1 := by
    intro v hv
    have h : v ∈ conjClosure V₃ H ⊓ P.Z1 := by
      rw [P.U_inf_Z1]
      exact hv
    exact h.2
  have hidx : (V₁.subgroupOf P.Z1).index = 2 := by
    have h := Subgroup.relIndex_mul_card V₁ P.Z1
    rw [inf_eq_left.2 hV1Z, S.card_V1, P.card_Z1 hQ] at h
    show V₁.relIndex P.Z1 = 2
    omega
  have hV1c : ∀ v ∈ V₁, ∀ x ∈ H, v * x = x * v := fun v hv x hx =>
    Subgroup.mem_centralizer_iff.mp (S.hF.H_le_centralizer hx) v hv
  have hZ4 : ∀ w ∈ P.Z1, w ^ 4 = 1 := by
    intro w hw
    have h := pow_card_eq_one' (G := ↥P.Z1) (x := ⟨w, hw⟩)
    rw [P.card_Z1 hQ] at h
    exact congrArg Subtype.val h
  have hyZ1 : ∀ j ∈ P.Z1, y * j = j * y := by
    intro j hj
    have hjy : y * j * y⁻¹ ∈ P.Z1 := (Subgroup.mem_normalizer_iff.mp hyZ j).mp hj
    have hc : y * j * y⁻¹ * j⁻¹ ∈ V₁ := by
      have key := Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨y * j * y⁻¹, hjy⟩)
        (b := (⟨j, hj⟩ : ↥P.Z1)⁻¹)
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at key
      rw [key]
      constructor
      · intro h
        have e : j = y⁻¹ * (y * j * y⁻¹) * y := by group
        have h2 : j ∈ V₁ := by
          rw [e]
          have := hconjV1 _ h
          have e2 : y⁻¹ * (y * j * y⁻¹) * y = y * j * y⁻¹ := by
            calc y⁻¹ * (y * j * y⁻¹) * y = y⁻¹ * (y * (y * j * y⁻¹) * y⁻¹) * y := by rw [this]
              _ = y * j * y⁻¹ := by group
          rw [e2]
          exact h
        exact V₁.inv_mem h2
      · intro h
        have h2 : j ∈ V₁ := by simpa using V₁.inv_mem h
        rw [hconjV1 j h2]
        exact h2
    set c := y * j * y⁻¹ * j⁻¹ with hcdef
    have hjH : j ∈ H := pCoreOf_le 2 H hj.1
    have hq : y * j * y⁻¹ = c * j := by rw [hcdef]; group
    have hc4 : c ^ 4 = 1 := hZ4 c (hV1Z hc)
    have hc1 : c = 1 := eq_one_of_conj hodd hq (hyV1 c hc) hc4
    have : y * j * y⁻¹ = j := by rw [hq, hc1, one_mul]
    calc y * j = y * j * y⁻¹ * y := by group
      _ = j * y := by rw [this]
  intro q hq
  set w := y * q * y⁻¹ * q⁻¹ with hwdef
  have hwZ : w ∈ P.Z1 := htriv q hq
  have hqw : y * q * y⁻¹ = w * q := by rw [hwdef]; group
  have hw1 : w = 1 := eq_one_of_conj hodd hqw (hyZ1 w hwZ) (hZ4 w hwZ)
  have : y * q * y⁻¹ = q := by rw [hqw, hw1, one_mul]
  calc y * q = y * q * y⁻¹ * y := by group
    _ = q * y := by rw [this]

theorem isPGroup_ker_actQ (X : Subgroup G) (hX : X ≤ Subgroup.normalizer (pCoreOf 2 H : Set G))
    (hXz : ∀ x ∈ X, x * P.C.z = P.C.z * x)
    (hXC : ∀ x ∈ X, (∀ q ∈ pCoreOf 2 H, x * q = q * x) → x ∈ pCoreOf 2 H) :
    IsPGroup 2 (P.actQ hQ X hX).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro g
  set a : G := ((g : ↥X) : G) with ha
  obtain ⟨e, m', hm', hn⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos a).ne' 2 (by norm_num)
  have hmodd : Odd m' := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hm')
  set y : G := a ^ (2 ^ e) with hy
  have hyX : y ∈ X := X.pow_mem (g : ↥X).2 _
  have hy1 : y ^ m' = 1 := by
    rw [hy, ← pow_mul, ← hn, pow_orderOf_eq_one]
  have hyodd : Odd (orderOf y) := hmodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hy1)
  have hgk : (g : ↥X) ^ (2 ^ e) ∈ (P.actQ hQ X hX).ker := (P.actQ hQ X hX).ker.pow_mem g.2 _
  have htriv : ∀ q ∈ pCoreOf 2 H, y * q * y⁻¹ * q⁻¹ ∈ P.Z1 := by
    intro q hq
    have h1 := congrArg (fun φ : MulAut (Multiplicative V4) => φ (P.thetaQ hQ ⟨q, hq⟩))
      ((MonoidHom.mem_ker).1 hgk)
    simp only [MulAut.one_apply] at h1
    rw [P.actQ_θ] at h1
    have hm : y * q * y⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp (hX hyX) q).mp hq
    have e1 : (Q8Coords.conjHom (hX ((g : ↥X) ^ (2 ^ e)).2) ⟨q, hq⟩ : ↥(pCoreOf 2 H)) =
        ⟨y * q * y⁻¹, hm⟩ := Subtype.ext (by simp [Q8Coords.coe_conjHom, hy, ha])
    rw [e1] at h1
    have h2 : P.thetaQ hQ (⟨y * q * y⁻¹, hm⟩ * (⟨q, hq⟩ : ↥(pCoreOf 2 H))⁻¹) = 1 := by
      rw [map_mul, map_inv, h1]
      exact mul_inv_cancel _
    exact (P.thetaQ_eq_one_iff hQ _).1 h2
  have hyC := P.comm_of_odd hQ (hX hyX) (hXz y hyX) hyodd htriv
  have hyQ : y ∈ pCoreOf 2 H := hXC y hyX hyC
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 (pCoreOf_isPGroup 2 H) ⟨y, hyQ⟩
  rw [Subgroup.orderOf_mk] at hk
  have hy1' : y = 1 := by
    rcases k with _ | k
    · rwa [pow_zero, orderOf_eq_one_iff] at hk
    · exfalso
      rw [hk] at hyodd
      have := Nat.odd_iff.1 hyodd
      rw [pow_succ] at this
      omega
  refine ⟨e, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
  rw [← ha, ← hy]
  exact hy1'

end A5SitPf15

end CFSG.Quasithin.H13
