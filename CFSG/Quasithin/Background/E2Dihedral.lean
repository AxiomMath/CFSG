module

public import CFSG.Quasithin.Background.E2Thirteen
public import CFSG.Quasithin.Background.E2SolvBaumann

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F

namespace E2

variable {G : Type*} [Group G]

structure DihedralPair (H T V U : Subgroup G) (x z : G) : Prop where
  T2 : IsPGroup 2 T
  TH : T ≤ H
  QT : pCoreOf 2 H ≤ T
  char : CharTwo H
  VT : V ≤ T
  TV : T ≤ Subgroup.normalizer (V : Set G)
  elem : IsElemAbelian 2 V
  UV : U ≤ V
  VQU : V ⊓ pCoreOf 2 H ≤ U
  xV : x ∈ V
  xU : x ∉ U
  U2 : ∀ v ∈ V, v ∈ U ∨ x * v ∈ U
  zH : z ∈ H
  zodd : Odd (orderOf z)
  z1 : z ≠ 1
  xz : x * z * x⁻¹ = z⁻¹
  zU : ∀ u ∈ U, z * u * z⁻¹ * u⁻¹ ∈ pCoreOf 2 H

abbrev dpI (V : Subgroup G) (z : G) : Subgroup G := V ⊔ cjSub z V

abbrev dpR (H V U : Subgroup G) (z : G) : Subgroup G := dpI V z ⊓ (U ⊔ pCoreOf 2 H)

abbrev dpA (H V U : Subgroup G) (z : G) : Subgroup G := cjSub z V ⊓ dpR H V U z

abbrev dpZ (V : Subgroup G) (z : G) : Subgroup G := V ⊓ cjSub z V

abbrev dpP (H V U : Subgroup G) (z : G) : Subgroup G := U ⊔ dpA H V U z

namespace DihedralPair

variable {H T V U : Subgroup G} {x z : G}

theorem VH (d : DihedralPair H T V U x z) : V ≤ H := d.VT.trans d.TH

theorem HQ (_d : DihedralPair H T V U x z) :
    H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H

theorem x2 (d : DihedralPair H T V U x z) : x * x = 1 := by
  simpa [pow_two] using d.elem.2 x d.xV

theorem zN (d : DihedralPair H T V U x z) : z ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
  d.HQ d.zH

theorem zU' (d : DihedralPair H T V U x z) : ∀ u ∈ U, z⁻¹ * u * z * u⁻¹ ∈ pCoreOf 2 H := by
  intro u hu
  have h2 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ d.zN) _).mp
    ((pCoreOf 2 H).inv_mem (d.zU u hu))
  have e : z⁻¹ * u * z * u⁻¹ = z⁻¹ * (z * u * z⁻¹ * u⁻¹)⁻¹ * z⁻¹⁻¹ := by group
  rw [e]
  exact h2

theorem zQ' (d : DihedralPair H T V U x z) : ∀ q ∈ pCoreOf 2 H, z⁻¹ * q * z ∈ pCoreOf 2 H :=
  fun q hq => by simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ d.zN) q).mp hq

theorem Vzel (d : DihedralPair H T V U x z) : IsElemAbelian 2 (cjSub z V) :=
  isElemAbelian_cjSub d.elem

theorem zz [Finite G] (d : DihedralPair H T V U x z) :
    (z * z) ^ ((orderOf z + 1) / 2) = z := by
  obtain ⟨m, hm⟩ := d.zodd
  rw [show (orderOf z + 1) / 2 = m + 1 by omega, ← pow_two, ← pow_mul,
    show 2 * (m + 1) = orderOf z + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]

theorem zI [Finite G] (d : DihedralPair H T V U x z) : z ∈ dpI V z := by
  have hzx : z * x * z⁻¹ ∈ cjSub z V := by
    rw [mem_cjSub]
    simpa [mul_assoc] using d.xV
  have h1 : x * z⁻¹ * x⁻¹ = z := by
    have := congrArg (·⁻¹) d.xz
    simpa [mul_assoc] using this
  have hz2 : z * x * z⁻¹ * x⁻¹ = z * z := by
    calc z * x * z⁻¹ * x⁻¹ = z * (x * z⁻¹ * x⁻¹) := by group
      _ = z * z := by rw [h1]
  have hz2I : z * z ∈ dpI V z := by
    rw [← hz2]
    exact (dpI V z).mul_mem (Subgroup.mem_sup_right hzx)
      ((dpI V z).inv_mem (Subgroup.mem_sup_left d.xV))
  have := (dpI V z).pow_mem hz2I ((orderOf z + 1) / 2)
  rwa [d.zz] at this

theorem IH (d : DihedralPair H T V U x z) : dpI V z ≤ H := sup_le d.VH fun w hw => by
  rw [mem_cjSub] at hw
  have e : w = z * (z⁻¹ * w * z) * z⁻¹ := by group
  rw [e]
  exact H.mul_mem (H.mul_mem d.zH (d.VH hw)) (H.inv_mem d.zH)

theorem zUQ (d : DihedralPair H T V U x z) :
    z ∈ Subgroup.normalizer ((U ⊔ pCoreOf 2 H : Subgroup G) : Set G) :=
  mem_normalizer_sup_of_comm d.zN d.zU d.zU'

theorem IUQ (d : DihedralPair H T V U x z) :
    dpI V z ≤ Subgroup.normalizer ((U ⊔ pCoreOf 2 H : Subgroup G) : Set G) := by
  have hVUQ : V ≤ Subgroup.normalizer ((U ⊔ pCoreOf 2 H : Subgroup G) : Set G) := by
    intro v hv
    refine mem_normalizer_sup_of_comm (d.HQ (d.VH hv)) (fun u hu => ?_) (fun u hu => ?_)
    · have : v * u * v⁻¹ * u⁻¹ = 1 := by
        rw [isElemAbelian_comm d.elem hv (d.UV hu)]
        group
      rw [this]
      exact (pCoreOf 2 H).one_mem
    · have : v⁻¹ * u * v * u⁻¹ = 1 := by
        rw [isElemAbelian_comm d.elem (V.inv_mem hv) (d.UV hu)]
        group
      rw [this]
      exact (pCoreOf 2 H).one_mem
  refine sup_le hVUQ fun w hw => ?_
  rw [mem_cjSub] at hw
  have e : w = z * (z⁻¹ * w * z) * z⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ d.zUQ (hVUQ hw)) (Subgroup.inv_mem _ d.zUQ)

theorem IR (d : DihedralPair H T V U x z) :
    dpI V z ≤ Subgroup.normalizer (dpR H V U z : Set G) :=
  B2F.le_normalizer_inf Subgroup.le_normalizer d.IUQ

theorem RT (d : DihedralPair H T V U x z) : dpR H V U z ≤ T :=
  inf_le_right.trans (sup_le (d.UV.trans d.VT) d.QT)

theorem RV (d : DihedralPair H T V U x z) :
    dpR H V U z ≤ Subgroup.normalizer (V : Set G) := d.RT.trans d.TV

theorem zR [Finite G] (d : DihedralPair H T V U x z) :
    z ∈ Subgroup.normalizer (dpR H V U z : Set G) := d.IR d.zI

theorem RVz [Finite G] (d : DihedralPair H T V U x z) :
    dpR H V U z ≤ Subgroup.normalizer (cjSub z V : Set G) := by
  intro r hr
  have h1 : z⁻¹ * r * z ∈ dpR H V U z := by
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ d.zR) r).mp hr
  have := conj_mem_normalizer_cjSub z (d.RV h1)
  simpa [mul_assoc] using this

theorem VR (d : DihedralPair H T V U x z) : V ⊓ dpR H V U z = U := by
  apply le_antisymm
  · rintro w ⟨hwV, -, hwUQ⟩
    have hUQN : U ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := (d.UV.trans d.VH).trans d.HQ
    have hw' : w ∈ ((U ⊔ pCoreOf 2 H : Subgroup G) : Set G) := hwUQ
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hUQN] at hw'
    obtain ⟨u, hu, q, hq, rfl⟩ := hw'
    have hqV : q ∈ V := by
      have := V.mul_mem (V.inv_mem (d.UV hu)) hwV
      simpa using this
    exact U.mul_mem hu (d.VQU ⟨hqV, hq⟩)
  · exact fun u hu => ⟨d.UV hu, Subgroup.mem_sup_left (d.UV hu), Subgroup.mem_sup_left hu⟩

theorem UR (d : DihedralPair H T V U x z) : U ≤ dpR H V U z := fun u hu => by
  have : u ∈ V ⊓ dpR H V U z := by rw [d.VR]; exact hu
  exact this.2

theorem Aeq [Finite G] (d : DihedralPair H T V U x z) : dpA H V U z = cjSub z U := by
  rw [dpA, ← cjSub_eq_of_mem_normalizer d.zR, ← cjSub_inf, d.VR]

theorem AR (_d : DihedralPair H T V U x z) : dpA H V U z ≤ dpR H V U z := inf_le_right

theorem AT (d : DihedralPair H T V U x z) : dpA H V U z ≤ T := inf_le_right.trans d.RT

theorem AVz (_d : DihedralPair H T V U x z) : dpA H V U z ≤ cjSub z V := inf_le_left

theorem Ael (d : DihedralPair H T V U x z) : IsElemAbelian 2 (dpA H V U z) :=
  isElemAbelian_mono inf_le_left d.Vzel

theorem ZU [Finite G] (d : DihedralPair H T V U x z) : dpZ V z ≤ U := by
  rintro w ⟨hwV, hwVz⟩
  by_contra hwU
  have hc : x * w ∈ U := (d.U2 w hwV).resolve_left hwU
  replace hwVz : z⁻¹ * w * z ∈ V := mem_cjSub.1 hwVz
  have hw : x * (x * w) = w := by rw [← mul_assoc, d.x2, one_mul]
  have e : z⁻¹ * z⁻¹ = (z⁻¹ * w * z) * ((z⁻¹ * (x * w) * z * (x * w)⁻¹) * (x * w))⁻¹ *
      x⁻¹ := by
    calc z⁻¹ * z⁻¹ = z⁻¹ * (x * z * x⁻¹) := by rw [d.xz]
      _ = (z⁻¹ * (x * (x * w)) * z) * ((z⁻¹ * (x * w) * z * (x * w)⁻¹) * (x * w))⁻¹ *
          x⁻¹ := by group
      _ = _ := by rw [hw]
  have hT1 : z⁻¹ * z⁻¹ ∈ T := by
    rw [e]
    refine T.mul_mem (T.mul_mem (d.VT hwVz) (T.inv_mem (T.mul_mem (d.QT (d.zU' _ hc))
      (d.UV.trans d.VT hc)))) (T.inv_mem (d.VT d.xV))
  obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one d.T2 hT1
  have e2 : z⁻¹ * z⁻¹ = (z ^ 2)⁻¹ := by rw [pow_two, mul_inv_rev]
  rw [e2, inv_pow, inv_eq_one] at hk
  have hk' : z ^ 2 ^ (k + 1) = 1 := by rw [pow_succ', pow_mul, hk]
  exact d.z1 (eq_one_of_odd_orderOf_of_pow_two_pow d.zodd hk')

theorem ZA [Finite G] (d : DihedralPair H T V U x z) : dpZ V z ≤ dpA H V U z := fun _ hw =>
  ⟨hw.2, (d.UV.trans le_sup_left : U ≤ dpI V z) (d.ZU hw), Subgroup.mem_sup_left (d.ZU hw)⟩

theorem ZC (d : DihedralPair H T V U x z) :
    ∀ ζ ∈ dpZ V z, ∀ y ∈ dpI V z, y * ζ = ζ * y := by
  intro ζ hζ y hy
  have h1 : ζ ∈ Subgroup.centralizer (dpI V z : Set G) := mem_centralizer_sup
    (Subgroup.mem_centralizer_iff.2 fun v hv => isElemAbelian_comm d.elem hv hζ.1)
    (Subgroup.mem_centralizer_iff.2 fun v hv => isElemAbelian_comm d.Vzel hv hζ.2)
  exact Subgroup.mem_centralizer_iff.1 h1 y hy

theorem comm1 (d : DihedralPair H T V U x z) : ⁅V, dpA H V U z⁆ ≤ U := by
  rw [Subgroup.commutator_le]
  intro v hv a ha
  rw [commutatorElement_def, ← d.VR]
  refine ⟨?_, ?_⟩
  · have := (Subgroup.mem_normalizer_iff.mp (d.RV (d.AR ha)) v⁻¹).mp (V.inv_mem hv)
    have e : v * a * v⁻¹ * a⁻¹ = v * (a * v⁻¹ * a⁻¹) := by group
    rw [e]
    exact V.mul_mem hv this
  · have := (Subgroup.mem_normalizer_iff.mp (d.IR (Subgroup.mem_sup_left hv)) a).mp (d.AR ha)
    exact (dpR H V U z).mul_mem this ((dpR H V U z).inv_mem (d.AR ha))

theorem comm2 [Finite G] (d : DihedralPair H T V U x z) : ⁅U, dpA H V U z⁆ ≤ dpZ V z := by
  rw [Subgroup.commutator_le]
  intro u hu a ha
  rw [commutatorElement_def]
  refine ⟨?_, ?_⟩
  · have := (Subgroup.mem_normalizer_iff.mp (d.RV (d.AR ha)) u⁻¹).mp (V.inv_mem (d.UV hu))
    have e : u * a * u⁻¹ * a⁻¹ = u * (a * u⁻¹ * a⁻¹) := by group
    rw [e]
    exact V.mul_mem (d.UV hu) this
  · have := (Subgroup.mem_normalizer_iff.mp (d.RVz (d.UR hu)) a).mp (d.AVz ha)
    exact (cjSub z V).mul_mem this ((cjSub z V).inv_mem (d.AVz ha))

theorem comm3 (d : DihedralPair H T V U x z) : ⁅dpZ V z, dpA H V U z⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro w hw a ha
  rw [commutatorElement_def, Subgroup.mem_bot, isElemAbelian_comm d.Vzel hw.2 (d.AVz ha)]
  group

theorem cubic [Finite G] (d : DihedralPair H T V U x z) :
    ⁅⁅⁅V, dpA H V U z⁆, dpA H V U z⁆, dpA H V U z⁆ = ⊥ :=
  le_bot_iff.1 ((Subgroup.commutator_mono (Subgroup.commutator_mono d.comm1 le_rfl)
    le_rfl).trans ((Subgroup.commutator_mono d.comm2 le_rfl).trans d.comm3.le))

theorem ACV [Finite G] (d : DihedralPair H T V U x z) :
    dpA H V U z ⊓ Subgroup.centralizer (V : Set G) = dpZ V z := by
  set A := dpA H V U z with hA
  set Z := dpZ V z with hZ
  set C := A ⊓ commCentralizer V Z with hC
  have hCV : ∀ v ∈ V, ∀ c ∈ C, v * c * v⁻¹ ∈ C := by
    intro v hv c hc
    have hvZ : v ∈ Subgroup.normalizer (Z : Set G) := Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun w hw => isElemAbelian_comm d.elem hw.1 hv)
    refine ⟨?_, conj_mem_commCentralizer (Subgroup.le_normalizer hv) hvZ hc.2⟩
    have e : v * c * v⁻¹ = (v * c * v⁻¹ * c⁻¹) * c := by group
    rw [e]
    exact A.mul_mem (d.ZA (hc.2.2 v hv)) hc.1
  have hIC : dpI V z ≤ Subgroup.normalizer (C : Set G) := by
    refine sup_le (fun v hv => B6.mem_normalizer_of_forall_mem (hCV v hv) fun c hc => ?_)
      fun w hw => Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.2 fun c hc => isElemAbelian_comm d.Vzel (d.AVz hc.1) hw)
    simpa using hCV v⁻¹ (V.inv_mem hv) c hc
  have hCZ : C ≤ Z := by
    intro c hc
    refine ⟨?_, d.AVz hc.1⟩
    have h1 : z * c * z⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.mp (hIC d.zI) c).mp hc
    have h2 : z * c * z⁻¹ ∈ cjSub z V := d.AVz h1.1
    rw [mem_cjSub] at h2
    simpa [mul_assoc] using h2
  apply le_antisymm
  · intro a ha
    refine hCZ ⟨ha.1, Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2
      fun w hw => isElemAbelian_comm d.Vzel hw.2 (d.AVz ha.1)), fun v hv => ?_⟩
    have : v * a * v⁻¹ * a⁻¹ = 1 := by
      rw [Subgroup.mem_centralizer_iff.1 ha.2 v hv]
      group
    rw [this]
    exact Z.one_mem
  · exact fun w hw => ⟨d.ZA hw, Subgroup.mem_centralizer_iff.2 fun v hv =>
      isElemAbelian_comm d.elem hv hw.1⟩

theorem wu [Finite G] (d : DihedralPair H T V U x z) :
    ∀ w ∈ cjSub z V, ∀ u ∈ U, w * u * w⁻¹ * u⁻¹ ∈ dpA H V U z := by
  intro w hw u hu
  refine ⟨?_, ?_⟩
  · have := (Subgroup.mem_normalizer_iff.mp (d.RVz (d.UR hu)) w⁻¹).mp ((cjSub z V).inv_mem hw)
    have e : w * u * w⁻¹ * u⁻¹ = w * (u * w⁻¹ * u⁻¹) := by group
    rw [e]
    exact (cjSub z V).mul_mem hw this
  · have := (Subgroup.mem_normalizer_iff.mp (d.IR (Subgroup.mem_sup_right hw)) u).mp (d.UR hu)
    exact (dpR H V U z).mul_mem this ((dpR H V U z).inv_mem (d.UR hu))

theorem PR (d : DihedralPair H T V U x z) : dpP H V U z ≤ dpR H V U z := sup_le d.UR d.AR

theorem IP [Finite G] (d : DihedralPair H T V U x z) :
    dpI V z ≤ Subgroup.normalizer (dpP H V U z : Set G) := by
  have hVzP : ∀ w ∈ cjSub z V, cjSub w (dpP H V U z) ≤ dpP H V U z := by
    intro w hw
    have hwA : w ∈ Subgroup.normalizer (dpA H V U z : Set G) := Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun a ha => isElemAbelian_comm d.Vzel (d.AVz ha) hw)
    rw [dpP, cjSub_sup, cjSub_eq_of_mem_normalizer hwA]
    refine sup_le (fun y hy => ?_) le_sup_right
    rw [mem_cjSub] at hy
    have e : y = (w * (w⁻¹ * y * w) * w⁻¹ * (w⁻¹ * y * w)⁻¹) * (w⁻¹ * y * w) := by group
    rw [e]
    exact (dpP H V U z).mul_mem (Subgroup.mem_sup_right (d.wu w hw _ hy))
      (Subgroup.mem_sup_left hy)
  have hVP' : ∀ v ∈ V, cjSub v (dpP H V U z) ≤ dpP H V U z := by
    intro v hv
    have hvU : v ∈ Subgroup.normalizer (U : Set G) := Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun u hu => isElemAbelian_comm d.elem (d.UV hu) hv)
    rw [dpP, cjSub_sup, cjSub_eq_of_mem_normalizer hvU]
    refine sup_le le_sup_left (fun y hy => ?_)
    rw [mem_cjSub] at hy
    have hc : v * (v⁻¹ * y * v) * v⁻¹ * (v⁻¹ * y * v)⁻¹ ∈ U := by
      have := Subgroup.commutator_mem_commutator hv hy
      rw [commutatorElement_def] at this
      exact d.comm1 this
    have e : y = (v * (v⁻¹ * y * v) * v⁻¹ * (v⁻¹ * y * v)⁻¹) * (v⁻¹ * y * v) := by group
    rw [e]
    exact (dpP H V U z).mul_mem (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hy)
  exact sup_le (fun v hv => le_normalizer_of_cjSub_le (hVP' v hv) (hVP' v⁻¹ (V.inv_mem hv)))
    fun w hw => le_normalizer_of_cjSub_le (hVzP w hw) (hVzP w⁻¹ ((cjSub z V).inv_mem hw))

theorem QU (d : DihedralPair H T V U x z) :
    pCoreOf 2 H ≤ Subgroup.normalizer (U : Set G) := by
  have key : ∀ q ∈ pCoreOf 2 H, ∀ u ∈ U, q * u * q⁻¹ ∈ U := by
    intro q hq u hu
    have h1 : q * u * q⁻¹ * u⁻¹ ∈ V ⊓ pCoreOf 2 H := by
      refine ⟨?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (d.TV (d.QT hq)) u).mp (d.UV hu)
        exact V.mul_mem this (V.inv_mem (d.UV hu))
      · have := (Subgroup.mem_normalizer_iff.mp (d.HQ (d.VH (d.UV hu))) q⁻¹).mp
          ((pCoreOf 2 H).inv_mem hq)
        have e : q * u * q⁻¹ * u⁻¹ = q * (u * q⁻¹ * u⁻¹) := by group
        rw [e]
        exact (pCoreOf 2 H).mul_mem hq this
    have e : q * u * q⁻¹ = (q * u * q⁻¹ * u⁻¹) * u := by group
    rw [e]
    exact U.mul_mem (d.VQU h1) hu
  exact fun q hq => B6.mem_normalizer_of_forall_mem (key q hq)
    (fun u hu => by simpa using key q⁻¹ ((pCoreOf 2 H).inv_mem hq) u hu)

theorem QA [Finite G] (d : DihedralPair H T V U x z) :
    pCoreOf 2 H ≤ Subgroup.normalizer (dpA H V U z : Set G) := by
  intro q hq
  rw [d.Aeq]
  have := conj_mem_normalizer_cjSub z (d.QU (d.zQ' q hq))
  simpa [mul_assoc] using this

theorem QI (d : DihedralPair H T V U x z) :
    pCoreOf 2 H ≤ Subgroup.normalizer (dpI V z : Set G) := by
  refine B2F.le_normalizer_sup (d.QT.trans d.TV) fun q hq => ?_
  have := conj_mem_normalizer_cjSub z (d.TV (d.QT (d.zQ' q hq)))
  simpa [mul_assoc] using this

theorem QR (d : DihedralPair H T V U x z) :
    pCoreOf 2 H ≤ Subgroup.normalizer (dpR H V U z : Set G) :=
  B2F.le_normalizer_inf d.QI
    ((le_sup_right : pCoreOf 2 H ≤ U ⊔ pCoreOf 2 H).trans Subgroup.le_normalizer)

theorem AV [Finite G] (d : DihedralPair H T V U x z) :
    ¬ dpA H V U z ≤ Subgroup.centralizer (V : Set G) := by
  intro hAC
  set P := dpP H V U z with hP
  set R := dpR H V U z with hR
  set I := dpI V z with hI
  set Q := pCoreOf 2 H with hQ
  have hVP : V ≤ Subgroup.centralizer (P : Set G) := fun v hv =>
    mem_centralizer_sup
      (Subgroup.mem_centralizer_iff.2 fun u hu => isElemAbelian_comm d.elem (d.UV hu) hv)
      (Subgroup.mem_centralizer_iff.2 fun a ha =>
        (Subgroup.mem_centralizer_iff.1 (hAC ha) v hv).symm)
  have hQP : Q ≤ Subgroup.normalizer (P : Set G) := B2F.le_normalizer_sup d.QU d.QA
  set Y := I ⊓ Subgroup.centralizer (P : Set G) ⊓ commCentralizer R P with hY
  have hYconj : ∀ g : G, g ∈ Subgroup.normalizer (I : Set G) →
      g ∈ Subgroup.normalizer (P : Set G) → g ∈ Subgroup.normalizer (R : Set G) →
        ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := by
    intro g hgI hgP hgR y hy
    refine ⟨⟨(Subgroup.mem_normalizer_iff.mp hgI y).mp hy.1.1, ?_⟩,
      conj_mem_commCentralizer hgR hgP hy.2⟩
    exact (Subgroup.mem_normalizer_iff.mp (B2F.normalizer_le_normalizer_centralizer P hgP) y).mp
      hy.1.2
  have hVY : V ≤ Y := by
    intro v hv
    refine ⟨⟨Subgroup.mem_sup_left hv, hVP hv⟩, Subgroup.centralizer_le_normalizer _ (hVP hv),
      fun r hr => ?_⟩
    apply Subgroup.mem_sup_left
    rw [← d.VR]
    refine ⟨V.mul_mem ((Subgroup.mem_normalizer_iff.mp (d.RV hr) v).mp hv) (V.inv_mem hv), ?_⟩
    have := (Subgroup.mem_normalizer_iff.mp (d.IR (Subgroup.mem_sup_left hv)) r⁻¹).mp
      (R.inv_mem hr)
    have e : r * v * r⁻¹ * v⁻¹ = r * (v * r⁻¹ * v⁻¹) := by group
    rw [e]
    exact R.mul_mem hr this
  have hIY : I ≤ Y := by
    refine sup_le hVY fun w hw => ?_
    rw [mem_cjSub] at hw
    have := hYconj z (Subgroup.le_normalizer d.zI) (d.IP d.zI) d.zR _ (hVY hw)
    simpa [mul_assoc] using this
  have hY2 : ∀ y ∈ Y, ∃ k : ℕ, y ^ 2 ^ k = 1 := by
    intro y hy
    obtain ⟨a₂, b, rfl, -, hb, ⟨k, hk⟩, hbo⟩ := exists_two_part_odd_part y
    have hbY : b ∈ Y := Subgroup.zpowers_le.2 hy hb
    have hbH : b ∈ H := d.IH hbY.1.1
    have hbR : ∀ r ∈ R, b * r = r * b := by
      intro r hr
      have hc : b * r * b⁻¹ * r⁻¹ ∈ P := by
        have := P.inv_mem (hbY.2.2 r hr)
        simpa [mul_assoc] using this
      exact commute_of_odd_of_commutator hbo
        (Subgroup.mem_centralizer_iff.1 hbY.1.2 _ hc).symm
        (exists_pow_two_pow_eq_one d.T2 (d.RT (d.PR hc)))
    have hbQ : b ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hcQ : b * q * b⁻¹ * q⁻¹ ∈ Q :=
        Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (d.HQ hbH) q).mp hq) (Q.inv_mem hq)
      have hcY : b * q * b⁻¹ * q⁻¹ ∈ Y := by
        have h1 := hYconj q (d.QI hq) (hQP hq) (d.QR hq) b⁻¹ (Y.inv_mem hbY)
        have e : b * q * b⁻¹ * q⁻¹ = b * (q * b⁻¹ * q⁻¹) := by group
        rw [e]
        exact Y.mul_mem hbY h1
      have hcR : b * q * b⁻¹ * q⁻¹ ∈ R := ⟨hcY.1.1, Subgroup.mem_sup_right hcQ⟩
      exact (commute_of_odd_of_commutator hbo (hbR _ hcR)
        (exists_pow_two_pow_eq_one d.T2 (d.QT hcQ))).symm
    have hbQ' : b ∈ Q := d.char ⟨hbH, hbQ⟩
    obtain ⟨k', hk'⟩ := exists_pow_two_pow_eq_one d.T2 (d.QT hbQ')
    have hb1 : b = 1 := eq_one_of_odd_orderOf_of_pow_two_pow hbo hk'
    exact ⟨k, by rw [hb1, one_mul]; exact hk⟩
  obtain ⟨k, hk⟩ := hY2 z (hIY d.zI)
  exact d.z1 (eq_one_of_odd_orderOf_of_pow_two_pow d.zodd hk)

theorem cardV [Finite G] (d : DihedralPair H T V U x z) : Nat.card V = 2 * Nat.card U := by
  have hidx : (U.subgroupOf V).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨x, d.xV⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    by_cases hb : (b : G) ∈ U
    · refine Or.inr ⟨hb, fun hbx => d.xU ?_⟩
      have := U.mul_mem (U.inv_mem hb) hbx
      simpa using this
    · refine Or.inl ⟨?_, hb⟩
      rw [isElemAbelian_comm d.elem b.2 d.xV]
      exact (d.U2 b b.2).resolve_left hb
  have h1 := Subgroup.relIndex_mul_card U V
  rw [inf_eq_left.2 d.UV] at h1
  rw [← h1]
  have : U.relIndex V = 2 := hidx
  rw [this]

theorem cardA [Finite G] (d : DihedralPair H T V U x z) :
    Nat.card (dpA H V U z) = Nat.card U := by rw [d.Aeq, card_cjSub]

theorem relIndex_le_two_of_le [Finite G] (d : DihedralPair H T V U x z)
    (hUA : U ≤ Subgroup.centralizer (dpA H V U z : Set G)) :
    (V ⊓ Subgroup.centralizer (dpA H V U z : Set G)).relIndex V ≤ 2 := by
  have h1 : Nat.card U ≤ Nat.card ↥(V ⊓ Subgroup.centralizer (dpA H V U z : Set G)) :=
    Subgroup.card_le_of_le (le_inf d.UV hUA)
  have hmV := Subgroup.relIndex_mul_card (V ⊓ Subgroup.centralizer (dpA H V U z : Set G)) V
  rw [inf_eq_left.2 inf_le_left] at hmV
  have hUpos : 0 < Nat.card U := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hUpos
  calc (V ⊓ Subgroup.centralizer (dpA H V U z : Set G)).relIndex V * Nat.card U ≤
        (V ⊓ Subgroup.centralizer (dpA H V U z : Set G)).relIndex V *
          Nat.card ↥(V ⊓ Subgroup.centralizer (dpA H V U z : Set G)) :=
        Nat.mul_le_mul_left _ h1
    _ = 2 * Nat.card U := by rw [hmV, d.cardV]

theorem nZ [Finite G] (d : DihedralPair H T V U x z) :
    (dpZ V z).relIndex (dpA H V U z) * Nat.card (dpZ V z) = Nat.card (dpA H V U z) := by
  have h1 := Subgroup.relIndex_mul_card (dpZ V z) (dpA H V U z)
  rwa [inf_eq_left.2 d.ZA] at h1

theorem relIndex_ne_one [Finite G] (d : DihedralPair H T V U x z) :
    (dpZ V z).relIndex (dpA H V U z) ≠ 1 := by
  intro h1
  have h := d.nZ
  rw [h1, one_mul] at h
  apply d.AV
  have hZeqA : dpZ V z = dpA H V U z := Subgroup.eq_of_le_of_card_ge d.ZA h.symm.le
  rw [← hZeqA]
  exact fun w hw => Subgroup.mem_centralizer_iff.2 fun v hv => isElemAbelian_comm d.elem hv hw.1

theorem relIndex_ne_zero [Finite G] (d : DihedralPair H T V U x z) :
    (dpZ V z).relIndex (dpA H V U z) ≠ 0 := by
  intro h0
  have h := d.nZ
  rw [h0, zero_mul] at h
  exact (Nat.card_pos (α := dpA H V U z)).ne' h.symm

theorem relIndex_le_two_mul [Finite G] (d : DihedralPair H T V U x z) :
    (V ⊓ Subgroup.centralizer (dpA H V U z : Set G)).relIndex V ≤
      2 * (dpZ V z).relIndex (dpA H V U z) := by
  have hmV := Subgroup.relIndex_mul_card (V ⊓ Subgroup.centralizer (dpA H V U z : Set G)) V
  rw [inf_eq_left.2 inf_le_left] at hmV
  have hZVA : dpZ V z ≤ V ⊓ Subgroup.centralizer (dpA H V U z : Set G) := fun w hw =>
    ⟨hw.1, Subgroup.mem_centralizer_iff.2 fun a ha => isElemAbelian_comm d.Vzel (d.AVz ha) hw.2⟩
  have hcardZ := Subgroup.card_le_of_le hZVA
  have hZpos : 0 < Nat.card (dpZ V z) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hZpos
  calc (V ⊓ Subgroup.centralizer (dpA H V U z : Set G)).relIndex V * Nat.card (dpZ V z) ≤
        (V ⊓ Subgroup.centralizer (dpA H V U z : Set G)).relIndex V *
          Nat.card ↥(V ⊓ Subgroup.centralizer (dpA H V U z : Set G)) :=
        Nat.mul_le_mul_left _ hcardZ
    _ = Nat.card V := hmV
    _ = 2 * Nat.card (dpA H V U z) := by rw [d.cardV, d.cardA]
    _ = 2 * (dpZ V z).relIndex (dpA H V U z) * Nat.card (dpZ V z) := by rw [← d.nZ, mul_assoc]

theorem le_centralizer_of_relIndex_eq_two [Finite G] (d : DihedralPair H T V U x z)
    (hn2 : (dpZ V z).relIndex (dpA H V U z) = 2) :
    U ≤ Subgroup.centralizer (dpA H V U z : Set G) := by
  set A := dpA H V U z with hA
  set Z := dpZ V z with hZ
  set I := dpI V z with hI
  have hidxA : (Z.subgroupOf A).index = 2 := hn2
  have hidxU : (Z.subgroupOf U).index = 2 := by
    have h1 := Subgroup.relIndex_mul_card Z U
    rw [inf_eq_left.2 d.ZU] at h1
    have hZpos : 0 < Nat.card Z := Nat.card_pos
    have h2 : Z.relIndex U * Nat.card Z = 2 * Nat.card Z := by
      rw [h1, ← d.cardA, ← d.nZ, hn2]
    exact Nat.eq_of_mul_eq_mul_right hZpos h2
  have hcosetA : ∀ {a b : G}, a ∈ A → b ∈ A → b ∉ Z → a ∉ Z → a * b ∈ Z := by
    intro a b ha hb hbZ haZ
    have key := Subgroup.mul_mem_iff_of_index_two hidxA (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at key
    exact key.2 (iff_of_false haZ hbZ)
  have hcosetU : ∀ {a b : G}, a ∈ U → b ∈ U → b ∉ Z → a ∉ Z → a * b ∈ Z := by
    intro a b ha hb hbZ haZ
    have key := Subgroup.mul_mem_iff_of_index_two hidxU (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at key
    exact key.2 (iff_of_false haZ hbZ)
  have hZlt : Z < A := lt_of_le_of_ne d.ZA fun h => by
    rw [h, Subgroup.relIndex_self] at hn2
    exact absurd hn2 (by norm_num)
  obtain ⟨a, ha, haZ⟩ := IsConcreteLE.exists_of_lt hZlt
  have haVz : a ∈ cjSub z V := d.AVz ha
  have hw : z * a * z⁻¹ ∈ dpP H V U z := (Subgroup.mem_normalizer_iff.mp (d.IP d.zI) a).mp
    (Subgroup.mem_sup_right ha)
  have hUA : U ≤ Subgroup.normalizer (A : Set G) := by
    have key : ∀ u ∈ U, ∀ b ∈ A, u * b * u⁻¹ ∈ A := by
      intro u hu b hb
      have h1 : u * b * u⁻¹ * b⁻¹ ∈ Z := by
        have := Subgroup.commutator_mem_commutator hu hb
        rw [commutatorElement_def] at this
        exact d.comm2 this
      have e : u * b * u⁻¹ = (u * b * u⁻¹ * b⁻¹) * b := by group
      rw [e]
      exact A.mul_mem (d.ZA h1) hb
    exact fun u hu => B6.mem_normalizer_of_forall_mem (key u hu)
      (fun b hb => by simpa using key u⁻¹ (U.inv_mem hu) b hb)
  have hw' : z * a * z⁻¹ ∈ ((U ⊔ A : Subgroup G) : Set G) := hw
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hUA] at hw'
  obtain ⟨u₁, hu₁, a₁, ha₁, hwu₁⟩ := hw'
  have hzVz : ∀ {y : G}, z * y * z⁻¹ ∈ cjSub z V → y ∈ V := fun hy => by
    rw [mem_cjSub] at hy
    simpa [mul_assoc] using hy
  have hu₁Z : u₁ ∉ Z := by
    intro hu₁Z
    apply haZ
    refine ⟨hzVz ?_, haVz⟩
    rw [← hwu₁]
    exact d.AVz (A.mul_mem (d.ZA hu₁Z) ha₁)
  have ha₁Z : a₁ ∉ Z := by
    intro ha₁Z
    have hwU : z * a * z⁻¹ ∈ U := by
      rw [← hwu₁]
      exact U.mul_mem hu₁ (d.ZU ha₁Z)
    have hu' : z⁻¹ * a * z ∈ U := by
      have := ha
      rw [hA, d.Aeq, mem_cjSub] at this
      exact this
    have hu'Z : z⁻¹ * a * z ∉ Z := fun h => haZ (by
      have hc := d.ZC _ h z d.zI
      have e : a = z * (z⁻¹ * a * z) * z⁻¹ := by group
      rw [e, hc]
      simpa [mul_assoc] using h)
    have hZc : ∀ ζ ∈ Z, (z * z) * ζ * (z * z)⁻¹ = ζ := fun ζ hζ => by
      rw [d.ZC ζ hζ (z * z) (I.mul_mem d.zI d.zI)]
      group
    have hzzU : cjSub (z * z) U ≤ U := by
      intro y hy
      rw [mem_cjSub] at hy
      by_cases huZ : (z * z)⁻¹ * y * (z * z) ∈ Z
      · have e : y = (z * z) * ((z * z)⁻¹ * y * (z * z)) * (z * z)⁻¹ := by group
        rw [e, hZc _ huZ]
        exact d.ZU huZ
      · have h1 := hcosetU hy hu' hu'Z huZ
        have e : y = (z * z) * (((z * z)⁻¹ * y * (z * z)) * (z⁻¹ * a * z)) * (z * z)⁻¹ *
            (z * a * z⁻¹)⁻¹ := by group
        rw [e, hZc _ h1]
        exact U.mul_mem (d.ZU h1) (U.inv_mem hwU)
    have hzzN : z * z ∈ Subgroup.normalizer (U : Set G) :=
      mem_normalizer_iff_cjSub_eq.2 (Subgroup.eq_of_le_of_card_ge hzzU (by rw [card_cjSub]))
    have hzN' : z ∈ Subgroup.normalizer (U : Set G) := by
      have := Subgroup.pow_mem _ hzzN ((orderOf z + 1) / 2)
      rwa [d.zz] at this
    apply haZ
    have haU : a ∈ U := by
      have := ha
      rw [hA, d.Aeq, cjSub_eq_of_mem_normalizer hzN'] at this
      exact this
    exact ⟨d.UV haU, haVz⟩
  have ha2 : a * a = 1 := by simpa [pow_two] using d.Ael.2 a ha
  have hw2 : (u₁ * a₁) * (u₁ * a₁) = 1 := by
    have hwu₁' : u₁ * a₁ = z * a * z⁻¹ := hwu₁
    rw [hwu₁']
    calc (z * a * z⁻¹) * (z * a * z⁻¹) = z * (a * a) * z⁻¹ := by group
      _ = 1 := by rw [ha2]; group
  have hu₁2 : u₁ * u₁ = 1 := by simpa [pow_two] using d.elem.2 u₁ (d.UV hu₁)
  have ha₁2 : a₁ * a₁ = 1 := by simpa [pow_two] using d.Ael.2 a₁ ha₁
  have hc11 : Commute u₁ a₁ := by
    have h1 : u₁ * a₁ = (u₁ * a₁)⁻¹ := eq_inv_of_mul_eq_one_left hw2
    show u₁ * a₁ = a₁ * u₁
    rw [h1, mul_inv_rev, inv_eq_of_mul_eq_one_right ha₁2, inv_eq_of_mul_eq_one_right hu₁2]
  have hu₁I : u₁ ∈ I := Subgroup.mem_sup_left (d.UV hu₁)
  have ha₁I : a₁ ∈ I := Subgroup.mem_sup_right (d.AVz ha₁)
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have huI : u ∈ I := Subgroup.mem_sup_left (d.UV hu)
  have hbI : b ∈ I := Subgroup.mem_sup_right (d.AVz hb)
  by_cases huZ : u ∈ Z
  · exact d.ZC u huZ b hbI
  by_cases hbZ : b ∈ Z
  · exact (d.ZC b hbZ u huI).symm
  have hζ₁ := hcosetU hu hu₁ hu₁Z huZ
  have hζ₂ := hcosetA hb ha₁ ha₁Z hbZ
  have hu' : u = (u * u₁) * u₁ := by rw [mul_assoc, hu₁2, mul_one]
  have hb' : b = (b * a₁) * a₁ := by rw [mul_assoc, ha₁2, mul_one]
  have c1 : Commute (u * u₁) a₁ := (d.ZC _ hζ₁ a₁ ha₁I).symm
  have c2 : Commute (b * a₁) u₁ := (d.ZC _ hζ₂ u₁ hu₁I).symm
  have c3 : Commute (b * a₁) (u * u₁) := (d.ZC _ hζ₂ _ (I.mul_mem huI hu₁I)).symm
  have key : Commute ((b * a₁) * a₁) ((u * u₁) * u₁) :=
    Commute.mul_right (Commute.mul_left c3 c1.symm) (Commute.mul_left c2 hc11.symm)
  rw [← hb', ← hu'] at key
  exact key.eq

theorem relIndex_lt [Finite G] (d : DihedralPair H T V U x z) :
    (V ⊓ Subgroup.centralizer (dpA H V U z : Set G)).relIndex V <
      ((dpA H V U z ⊓ Subgroup.centralizer (V : Set G)).relIndex (dpA H V U z)) ^ 2 := by
  rw [d.ACV]
  have hn0 := d.relIndex_ne_zero
  have hn1 := d.relIndex_ne_one
  rcases Nat.lt_or_ge 2 ((dpZ V z).relIndex (dpA H V U z)) with h3 | h2
  · calc (V ⊓ Subgroup.centralizer (dpA H V U z : Set G)).relIndex V ≤
          2 * (dpZ V z).relIndex (dpA H V U z) := d.relIndex_le_two_mul
      _ < (dpZ V z).relIndex (dpA H V U z) * (dpZ V z).relIndex (dpA H V U z) :=
          Nat.mul_lt_mul_of_pos_right h3 (by omega)
      _ = (dpZ V z).relIndex (dpA H V U z) ^ 2 := (sq _).symm
  have hn2 : (dpZ V z).relIndex (dpA H V U z) = 2 := by omega
  refine lt_of_le_of_lt (d.relIndex_le_two_of_le (d.le_centralizer_of_relIndex_eq_two hn2)) ?_
  rw [hn2]
  norm_num

theorem quad [Finite G] (d : DihedralPair H T V U x z) (hZ1 : dpZ V z = ⊥) :
    ⁅⁅V, dpA H V U z⁆, dpA H V U z⁆ = ⊥ ∧
      (V ⊓ Subgroup.centralizer (dpA H V U z : Set G)).relIndex V ≤
        (dpA H V U z ⊓ Subgroup.centralizer (V : Set G)).relIndex (dpA H V U z) := by
  have hUA : ⁅U, dpA H V U z⁆ = ⊥ := le_bot_iff.1 (hZ1 ▸ d.comm2)
  refine ⟨le_bot_iff.1 ((Subgroup.commutator_mono d.comm1 le_rfl).trans hUA.le), ?_⟩
  rw [d.ACV]
  have hn0 := d.relIndex_ne_zero
  have hn1 := d.relIndex_ne_one
  refine (d.relIndex_le_two_of_le (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hUA)).trans ?_
  omega

end DihedralPair

theorem exists_cubic_of_dihedral_pair [Finite G] {H T V U : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTH : T ≤ H) (hQT : pCoreOf 2 H ≤ T) (hchar : CharTwo H) (hVT : V ≤ T)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hV : IsElemAbelian 2 V) (hUV : U ≤ V)
    (hVQU : V ⊓ pCoreOf 2 H ≤ U) {x : G} (hxV : x ∈ V) (hxU : x ∉ U)
    (hU2 : ∀ v ∈ V, v ∈ U ∨ x * v ∈ U) {z : G} (hzH : z ∈ H) (hzo : Odd (orderOf z))
    (hz1 : z ≠ 1) (hxz : x * z * x⁻¹ = z⁻¹) (hzU : ∀ u ∈ U, z * u * z⁻¹ * u⁻¹ ∈ pCoreOf 2 H) :
    ∃ A : Subgroup G, A ≤ T ∧ A ≤ cjSub z V ∧ IsElemAbelian 2 A ∧
      ⁅⁅⁅V, A⁆, A⁆, A⁆ = ⊥ ∧ ¬ A ≤ Subgroup.centralizer (V : Set G) ∧
      A ⊓ Subgroup.centralizer (V : Set G) = V ⊓ cjSub z V ∧
      (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V <
        ((A ⊓ Subgroup.centralizer (V : Set G)).relIndex A) ^ 2 ∧
      (V ⊓ cjSub z V = ⊥ → ⁅⁅V, A⁆, A⁆ = ⊥ ∧
        (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V ≤
          (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A) ∧
      A = cjSub z U ∧ z ∈ V ⊔ cjSub z V ∧
      V ⊔ cjSub z V ≤ Subgroup.normalizer ((U ⊔ A : Subgroup G) : Set G) ∧
      V ⊓ cjSub z V ≤ U ∧ ⁅U, A⁆ ≤ V ⊓ cjSub z V ∧ ⁅V, A⁆ ≤ U ∧
      (∀ ζ ∈ V ⊓ cjSub z V, ∀ y ∈ V ⊔ cjSub z V, y * ζ = ζ * y) ∧
      Nat.card V = 2 * Nat.card U := by
  have d : DihedralPair H T V U x z := ⟨hT2, hTH, hQT, hchar, hVT, hTV, hV, hUV, hVQU, hxV, hxU,
    hU2, hzH, hzo, hz1, hxz, hzU⟩
  exact ⟨dpA H V U z, d.AT, d.AVz, d.Ael, d.cubic, d.AV, d.ACV, d.relIndex_lt, d.quad, d.Aeq,
    d.zI, d.IP, d.ZU, d.comm2, d.comm1, d.ZC, d.cardV⟩

theorem DihedralPair.exists_of_isSolvable [Finite G] {H T M V : Subgroup G}
    (h : MinParabolic H T M) (hsolv : Group.IsSolvable H) (hchar : CharTwo H) (hVT : V ≤ T)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hV : IsElemAbelian 2 V)
    (hVQ : ¬ V ≤ pCoreOf 2 H) : ∃ U : Subgroup G, ∃ x z : G, DihedralPair H T V U x z := by
  have hT := h.isSylow
  obtain ⟨U, hUV, hVQU, x, hxV, hxU, hU2, z, hzH, hzo, hz1, hxz, hzU⟩ :=
    exists_dihedral_pair h hsolv hVT hTV hV hVQ
  exact ⟨U, x, z, ⟨hT.2.1, hT.1, B6.pCoreOf_two_le_of_isSylowTwoOf hT, hchar, hVT, hTV, hV, hUV,
    hVQU, hxV, hxU, hU2, hzH, hzo, hz1, hxz, hzU⟩⟩

end E2

open E2 in
theorem E2_13_two_of_isSolvable {G : Type*} [Group G] [Finite G] {H T M V : Subgroup G}
    (h : MinParabolic H T M) (hsolv : Group.IsSolvable H) (hchar : CharTwo H) (hVT : V ≤ T)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hV : IsElemAbelian 2 V)
    (hVJ : ¬ V ≤ kerIn M H) :
    ∃ g ∈ H, ∃ A : Subgroup G, A ≤ T ∧ A ≤ cjSub g V ∧ IsElemAbelian 2 A ∧
      ⁅⁅⁅V, A⁆, A⁆, A⁆ = ⊥ ∧ ¬ A ≤ Subgroup.centralizer (V : Set G) ∧
      A ⊓ Subgroup.centralizer (V : Set G) = V ⊓ cjSub g V ∧
      (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V ≤
        ((A ⊓ Subgroup.centralizer (V : Set G)).relIndex A) ^ 2 := by
  have hT := h.isSylow
  have hVQ : ¬ V ≤ pCoreOf 2 H := fun hle => hVJ (hle.trans h.pCoreOf_le_kerIn)
  obtain ⟨U, hUV, hVQU, x, hxV, hxU, hU2, z, hzH, hzo, hz1, hxz, hzU⟩ :=
    exists_dihedral_pair h hsolv hVT hTV hV hVQ
  obtain ⟨A, hAT, hAVz, hAel, hcubic, hAV, hACV, hlt, -⟩ := exists_cubic_of_dihedral_pair
    hT.2.1 hT.1 (B6.pCoreOf_two_le_of_isSylowTwoOf hT) hchar hVT hTV hV hUV hVQU hxV hxU hU2 hzH
    hzo hz1 hxz hzU
  exact ⟨z, hzH, A, hAT, hAVz, hAel, hcubic, hAV, hACV, hlt.le⟩

end CFSG.Quasithin
