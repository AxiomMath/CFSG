module

public import CFSG.Quasithin.Vol2.Ch4Sec3C135V

public section

namespace CFSG.Quasithin.H13.Ch4.C135

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.Ch4 Matrix
open scoped commutatorElement

variable {G : Type} [Group G] {F : Type} [Field F]

namespace Hyp135

variable {G₀ L : Subgroup G} {α : ↥L →* ↥(StatedSL 3 F)} {H : Hyp135 G₀ L α}

namespace Adapted

variable (C : H.Adapted)

theorem e_comm [Finite G] {t : G} (ht : t ∈ pCoreOf 2 G₀) (q : ↥(c134Q G₀ L)) :
    C.e (cnj (H.pCoreOf_le_normalizer_Q ht) q * q⁻¹) =
      fun i => if i = 0 then C.lam ht • C.e q 1 else 0 := by
  rw [C.mul, C.e_inv]
  funext i
  fin_cases i
  · simp [(C.lam_spec ht q).1]
  · simp [(C.lam_spec ht q).2]

theorem le_normalizer_W_of_ne [Finite G] [CharP F 2] (hTQ : ¬ pCoreOf 2 G₀ ≤ c134Q G₀ L) :
    G₀ ≤ Subgroup.normalizer (C.W : Set G) := by
  obtain ⟨t₀, ht₀, ht₀Q⟩ := Set.not_subset.mp hTQ
  have hl₀ : C.lam ht₀ ≠ 0 := fun h => ht₀Q (C.mem_Q_of_lam ht₀ h)
  have hrep : ∀ w ∈ C.W, ∃ (q : ↥(c134Q G₀ L)) (u : G), u ∈ centerOf (c134Q G₀ L) ∧
      w = t₀ * q * t₀⁻¹ * (q : G)⁻¹ * u := by
    intro w hw
    have hwQ := C.W_le_Q hw
    obtain ⟨q, hq⟩ := C.surj (fun i => if i = 0 then 0 else (C.lam ht₀)⁻¹ • C.e ⟨w, hwQ⟩ 0)
    have h1 := C.e_comm ht₀ q
    have h2 : C.e (cnj (H.pCoreOf_le_normalizer_Q ht₀) q * q⁻¹) = C.e ⟨w, hwQ⟩ := by
      rw [h1, hq]
      funext i
      fin_cases i
      · simp [smul_smul, mul_inv_cancel₀ hl₀]
      · simp [(C.mem_W_iff ⟨w, hwQ⟩).mp hw]
    have h3 := (C.e_eq_iff _ _).mp h2
    refine ⟨q, _, h3, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_cnj]
    group
  refine le_normalizer_of_conj_mem fun g hg w hw => ?_
  obtain ⟨q, u, hu, rfl⟩ := hrep w hw
  have hgT : g * t₀ * g⁻¹ ∈ pCoreOf 2 G₀ :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 G₀ hg) t₀).mp ht₀
  have hgq : g * q * g⁻¹ ∈ c134Q G₀ L :=
    (Subgroup.mem_normalizer_iff.mp (H.le_normalizer_Q hg) q).mp q.2
  have hgu : g * u * g⁻¹ ∈ centerOf (c134Q G₀ L) :=
    (Subgroup.mem_normalizer_iff.mp (H.le_normalizer_U hg) u).mp hu
  have h1 := C.e_comm hgT ⟨_, hgq⟩
  have h2 : ((cnj (H.pCoreOf_le_normalizer_Q hgT) ⟨_, hgq⟩ * ⟨_, hgq⟩⁻¹ :
      ↥(c134Q G₀ L)) : G) ∈ C.W := (C.mem_W_iff _).mpr (by rw [h1]; simp)
  have h3 := C.W.mul_mem h2 (C.centerOf_le_Wμ _ hgu)
  convert h3 using 1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_cnj]
  group

theorem le_normalizer_V_of_ne [Finite G] [CharP F 2] (hTQ : ¬ pCoreOf 2 G₀ ≤ c134Q G₀ L) :
    G₀ ≤ Subgroup.normalizer (C.V : Set G) := fun _ hg =>
  mem_normalizer_inf (le_normalizer_pCoreOf 2 G₀ hg)
    (mem_normalizer_centralizer_of_mem (C.le_normalizer_W_of_ne hTQ hg))

theorem L_le_normalizer_V [Finite G] : L ≤ Subgroup.normalizer (C.V : Set G) := fun _ hg =>
  mem_normalizer_inf (le_normalizer_pCoreOf 2 G₀ (H.le hg))
    (mem_normalizer_centralizer_of_mem (C.le_normalizer_W hg))

theorem cm_mem_W [Finite G] [CharP F 2] {v : G} (hv : v ∈ C.V) (g : ↥L) :
    (cm hv.1 g : G) ∈ C.W := by
  refine C.mem_W_of_mem_V_Q ?_ (cm hv.1 g).2
  have hgv : (g : G) * v * (g : G)⁻¹ ∈ C.V :=
    (Subgroup.mem_normalizer_iff.mp (C.L_le_normalizer_V g.2) v).mp hv
  rw [coe_cm, show v⁻¹ * g * v * (g : G)⁻¹ = v⁻¹ * (g * v * (g : G)⁻¹) by group]
  exact C.V.mul_mem (C.V.inv_mem hv) hgv

theorem exists_conj_eq [Finite G] [CharP F 2] {v : G} (hv : v ∈ C.V) (g : ↥L) :
    ∃ w ∈ C.W, (g : G) * v * (g : G)⁻¹ = v * w :=
  ⟨_, C.cm_mem_W hv g, by rw [coe_cm]; group⟩

omit C in
include H in
theorem mem_centralizer_L_of {x : G} (hx : x ∈ G₀)
    (h : ∀ g ∈ L, g * x * g⁻¹ = x) : x = 1 := by
  have h1 : x ∈ G₀ ⊓ Subgroup.centralizer (L : Set G) := ⟨hx,
    Subgroup.mem_centralizer_iff.mpr fun g hg => by
      calc g * x = g * x * g⁻¹ * g := by group
        _ = x * g := by rw [h g hg]⟩
  rw [H.cent] at h1
  exact Subgroup.mem_bot.mp h1

theorem V_comm [Finite G] [CharP F 2] {v v' : G} (hv : v ∈ C.V) (hv' : v' ∈ C.V) :
    v * v' = v' * v := by
  have hvG : v * v' * v⁻¹ * v'⁻¹ ∈ G₀ :=
    pCoreOf_le 2 G₀ ((pCoreOf 2 G₀).mul_mem ((pCoreOf 2 G₀).mul_mem
      ((pCoreOf 2 G₀).mul_mem hv.1 hv'.1) ((pCoreOf 2 G₀).inv_mem hv.1))
        ((pCoreOf 2 G₀).inv_mem hv'.1))
  have h := mem_centralizer_L_of (H := H) hvG fun g hg => by
    obtain ⟨w, hw, hgw⟩ := C.exists_conj_eq hv ⟨g, hg⟩
    obtain ⟨w', hw', hgw'⟩ := C.exists_conj_eq hv' ⟨g, hg⟩
    simp only at hgw hgw'
    have c1 : w * v' = v' * w := Subgroup.mem_centralizer_iff.mp hv'.2 w hw
    have c2 : w' * v = v * w' := Subgroup.mem_centralizer_iff.mp hv.2 w' hw'
    have c3 : w * w' = w' * w := C.mul_comm_W hw hw'
    calc g * (v * v' * v⁻¹ * v'⁻¹) * g⁻¹ =
          (g * v * g⁻¹) * (g * v' * g⁻¹) * (g * v * g⁻¹)⁻¹ * (g * v' * g⁻¹)⁻¹ := by group
      _ = (v * w) * (v' * w') * (v * w)⁻¹ * (v' * w')⁻¹ := by rw [hgw, hgw']
      _ = v * (w * v') * w' * w⁻¹ * v⁻¹ * w'⁻¹ * v'⁻¹ := by group
      _ = v * v' * (w * w') * w⁻¹ * v⁻¹ * w'⁻¹ * v'⁻¹ := by rw [c1]; group
      _ = v * v' * w' * v⁻¹ * w'⁻¹ * v'⁻¹ := by rw [c3]; group
      _ = v * v' * v⁻¹ * v'⁻¹ := by
        have c6 : w' * v⁻¹ = v⁻¹ * w' := by
          calc w' * v⁻¹ = v⁻¹ * (v * w') * v⁻¹ := by group
            _ = v⁻¹ * (w' * v) * v⁻¹ := by rw [c2]
            _ = v⁻¹ * w' := by group
        rw [mul_assoc (v * v'), c6]
        group
  calc v * v' = (v * v' * v⁻¹ * v'⁻¹) * (v' * v) := by group
    _ = v' * v := by rw [h, one_mul]

theorem V_sq [Finite G] [CharP F 2] {v : G} (hv : v ∈ C.V) : v ^ 2 = 1 := by
  have hvG : v ^ 2 ∈ G₀ := pCoreOf_le 2 G₀ ((pCoreOf 2 G₀).pow_mem hv.1 2)
  refine mem_centralizer_L_of (H := H) hvG fun g hg => ?_
  obtain ⟨w, hw, hgw⟩ := C.exists_conj_eq hv ⟨g, hg⟩
  simp only at hgw
  have c : w * v = v * w := Subgroup.mem_centralizer_iff.mp hv.2 w hw
  have hw2 := C.sq_eq_one_of_mem_Wμ e₀_ne_zero hw
  rw [sq] at hw2 ⊢
  calc g * (v * v) * g⁻¹ = (g * v * g⁻¹) * (g * v * g⁻¹) := by group
    _ = v * w * (v * w) := by rw [hgw]
    _ = v * (w * v) * w := by group
    _ = v * (v * w) * w := by rw [c]
    _ = v * v * (w * w) := by group
    _ = v * v := by rw [hw2, mul_one]

theorem mem_V_of_commute [Finite G] [CharP F 2] {v : G} (hv : v ∈ C.V) (hvW : v ∉ C.W) {t : G}
    (ht : t ∈ pCoreOf 2 G₀) (htv : t * v = v * t) : t ∈ C.V := by
  obtain ⟨q₀, hq₀⟩ := C.exists_mul_mem_V ht
  set t₁ := t * (q₀ : G)⁻¹ with ht₁
  have hc : (q₀ : G) * v = v * q₀ := by
    have e : (q₀ : G) = t₁⁻¹ * t := by rw [ht₁]; group
    have h1 := C.V_comm hq₀ hv
    rw [e]
    calc t₁⁻¹ * t * v = t₁⁻¹ * (v * t) := by rw [mul_assoc, htv]
      _ = t₁⁻¹ * (v * t₁) * (t₁⁻¹ * t) := by group
      _ = t₁⁻¹ * (t₁ * v) * (t₁⁻¹ * t) := by rw [h1]
      _ = v * (t₁⁻¹ * t) := by group
  have hq₀W := C.mem_W_of_commute_V hv hvW hc
  have e : t = t₁ * q₀ := by rw [ht₁]; group
  rw [e]
  exact C.V.mul_mem hq₀ (C.W_le_V hq₀W)

end Adapted

end Hyp135

end CFSG.Quasithin.H13.Ch4.C135

end
