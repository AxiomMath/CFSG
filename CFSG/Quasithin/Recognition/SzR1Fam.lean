module

public import CFSG.Quasithin.Recognition.F112J2FamB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped commutatorElement

namespace SzR1

variable {G : Type} [Group G] {K1 S : Subgroup G} {Ω : Type}

structure FamData (K1 S : Subgroup G) (Ω : Type) where
  act : ↥K1 →* Equiv.Perm Ω
  pt : Ω
  trans : ∀ ω, ∃ k : ↥K1, act k pt = ω
  stab : ∀ k : ↥K1, act k pt = pt ↔ (k : G) ∈ borelOf K1 S

namespace FamData

variable (D : FamData K1 S Ω)

noncomputable def kf (ω : Ω) : ↥K1 := (D.trans ω).choose

theorem kf_spec (ω : Ω) : D.act (D.kf ω) D.pt = ω := (D.trans ω).choose_spec

theorem mem_borelOf_of_pt_eq {k k' : ↥K1} (h : D.act k D.pt = D.act k' D.pt) :
    ((k⁻¹ * k' : ↥K1) : G) ∈ borelOf K1 S := by
  rw [← D.stab]
  rw [map_mul, map_inv, Equiv.Perm.mul_apply, ← h]
  exact Equiv.symm_apply_apply _ _

@[expose] noncomputable def Vf (V : Subgroup G) (ω : Ω) : Subgroup G := conjSub (D.kf ω : G) V

variable {V : Subgroup G}

theorem conjSub_V (hVn : borelOf K1 S ≤ Subgroup.normalizer (V : Set G)) (k : ↥K1) :
    conjSub (k : G) V = D.Vf V (D.act k D.pt) := by
  set j := D.act k D.pt with hj
  have h := D.mem_borelOf_of_pt_eq (k := D.kf j) (k' := k) (by rw [D.kf_spec])
  have hN : (((D.kf j)⁻¹ * k : ↥K1) : G) ∈ Subgroup.normalizer (V : Set G) := hVn h
  have e : (k : G) = (D.kf j : G) * (((D.kf j)⁻¹ * k : ↥K1) : G) := by simp
  rw [e, conjSub_mul, conjSub_eq_of_mem_normalizer hN]
  rfl

theorem conjSub_Vf (hVn : borelOf K1 S ≤ Subgroup.normalizer (V : Set G)) (k : ↥K1) (ω : Ω) :
    conjSub (k : G) (D.Vf V ω) = D.Vf V (D.act k ω) := by
  have e : (k : G) * (D.kf ω : G) = ((k * D.kf ω : ↥K1) : G) := rfl
  unfold Vf
  rw [← conjSub_mul, e, D.conjSub_V hVn (k * D.kf ω)]
  have : D.act (k * D.kf ω) D.pt = D.act k ω := by
    rw [map_mul, Equiv.Perm.mul_apply, D.kf_spec]
  rw [this]
  rfl

theorem conjClosure_eq_iSup (hSK : S ≤ Subgroup.normalizer (K1 : Set G))
    (hSV : S ≤ Subgroup.normalizer (V : Set G))
    (hVn : borelOf K1 S ≤ Subgroup.normalizer (V : Set G)) :
    conjClosure V (K1 ⊔ S) = ⨆ ω, D.Vf V ω := by
  apply le_antisymm
  · refine conjClosure_le fun c hc v hv => ?_
    obtain ⟨k, hk, s, hs, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hSK).mp hc
    have hv' : s * v * s⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hSV hs) v).mp hv
    have e : k * s * v * (k * s)⁻¹ = k * (s * v * s⁻¹) * k⁻¹ := by group
    rw [e]
    have hmem : k * (s * v * s⁻¹) * k⁻¹ ∈ conjSub k V := mul_mem_conjSub hv'
    rw [show conjSub k V = D.Vf V (D.act ⟨k, hk⟩ D.pt) from D.conjSub_V hVn ⟨k, hk⟩] at hmem
    exact (le_iSup (fun j => D.Vf V j) _) hmem
  · refine iSup_le fun j => ?_
    intro x hx
    have hx' : (D.kf j : G)⁻¹ * x * (D.kf j : G) ∈ V := mem_conjSub.mp hx
    have := mem_conjClosure (Z := V) (H := K1 ⊔ S) (h := (D.kf j : G))
      (z := (D.kf j : G)⁻¹ * x * (D.kf j : G)) (Subgroup.mem_sup_left (D.kf j).2) hx'
    simpa [mul_assoc] using this

end FamData

section Ctx

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}

structure FamCtx (K1 L2 S Zs : Subgroup G) (Ω : Type) where
  h : R1SettingLegacyBare K1 L2 S Zs
  hR : Hyp111R K1 L2 S
  D : FamData K1 S Ω
  twoTrans : ∀ {a b c d : Ω}, a ≠ b → c ≠ d → ∃ k : ↥K1, D.act k a = c ∧ D.act k b = d
  hcomm : ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ = Zs

namespace FamCtx

variable (C : FamCtx K1 L2 S Zs Ω)

include C

theorem hVn : borelOf K1 S ≤ Subgroup.normalizer (conjClosure Zs L2 : Set G) :=
  (le_sup_left.trans le_sup_left : borelOf K1 S ≤ bigB K1 L2 S).trans
    (F112J2.bigB_le_normalizer_V C.h C.hR)

theorem hSV : S ≤ Subgroup.normalizer (conjClosure Zs L2 : Set G) :=
  (le_sup_right : S ≤ bigB K1 L2 S).trans (F112J2.bigB_le_normalizer_V C.h C.hR)

theorem hSK : S ≤ Subgroup.normalizer (K1 : Set G) := C.h.hyp.h1.normalizes

theorem U_eq : vBeta K1 L2 S Zs = ⨆ j, C.D.Vf (conjClosure Zs L2) j :=
  C.D.conjClosure_eq_iSup C.hSK C.hSV C.hVn

theorem Zs_sq {z : G} (hz : z ∈ Zs) : z * z = 1 := by
  have h1 : (⟨z, hz⟩ : ↥Zs) ^ Nat.card ↥Zs = 1 := pow_card_eq_one'
  rw [C.h.card_Z] at h1
  simpa [pow_two] using congrArg Subtype.val h1

theorem Zs_eq_zpowers {z₀ : G} (hz₀ : z₀ ∈ Zs) (hne : z₀ ≠ 1) : Zs = Subgroup.zpowers z₀ := by
  have hle : Subgroup.zpowers z₀ ≤ Zs := Subgroup.zpowers_le.mpr hz₀
  have hord : orderOf z₀ = 2 := orderOf_eq_prime (by rw [pow_two]; exact C.Zs_sq hz₀) hne
  have hcard : Nat.card ↥(Subgroup.zpowers z₀) = 2 := by rw [Nat.card_zpowers, hord]
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, C.h.card_Z])).symm

theorem exists_ne_one : ∃ z₀ : G, z₀ ∈ Zs ∧ z₀ ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hbot : Zs = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact hcon x hx
  have := C.h.card_Z
  rw [hbot, Subgroup.card_bot] at this
  omega

theorem V_comm {x y : G} (hx : x ∈ conjClosure Zs L2) (hy : y ∈ conjClosure Zs L2) :
    x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : IsMulCommutative ↥(conjClosure Zs L2) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [C.h.V_card]; norm_num)
  have := hc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
  exact congrArg Subtype.val this

theorem V_sq {x : G} (hx : x ∈ conjClosure Zs L2) : x * x = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨l, hl, z, hz, rfl⟩ := hx
    calc l * z * l⁻¹ * (l * z * l⁻¹) = l * (z * z) * l⁻¹ := by group
      _ = 1 := by rw [C.Zs_sq hz]; group
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hc := C.V_comm hx hy
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hc]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x hx ih =>
    calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
      _ = 1 := by rw [ih, inv_one]

theorem Vf_card (j : Ω) : Nat.card ↥(C.D.Vf (conjClosure Zs L2) j) = 4 := by
  unfold FamData.Vf
  rw [CosetGeom.card_conjSub, C.h.V_card]

theorem Zs_le_Vf (j : Ω) : Zs ≤ C.D.Vf (conjClosure Zs L2) j := by
  intro z hz
  have hk : ((C.D.kf j : ↥K1) : G) ∈ Subgroup.centralizer (Zs : Set G) :=
    C.h.K1_cent_Z (C.D.kf j).2
  have hcomm : z * (C.D.kf j : G) = (C.D.kf j : G) * z :=
    Subgroup.mem_centralizer_iff.mp hk z hz
  have e : (C.D.kf j : G) * z * (C.D.kf j : G)⁻¹ = z := by
    rw [← hcomm]
    group
  have hm : (C.D.kf j : G) * z * (C.D.kf j : G)⁻¹ ∈
      conjSub (C.D.kf j : G) (conjClosure Zs L2) :=
    mul_mem_conjSub (le_conjClosure Zs L2 hz)
  rwa [e] at hm

theorem Vf_comm {j : Ω} {x y : G} (hx : x ∈ C.D.Vf (conjClosure Zs L2) j)
    (hy : y ∈ C.D.Vf (conjClosure Zs L2) j) : x * y = y * x := by
  have hx' := mem_conjSub.mp hx
  have hy' := mem_conjSub.mp hy
  have := C.V_comm hx' hy'
  set g : G := (C.D.kf j : G)
  have e1 : x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
  have e2 : y * x = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
  rw [e1, e2, this]

theorem Vf_sq {j : Ω} {x : G} (hx : x ∈ C.D.Vf (conjClosure Zs L2) j) : x * x = 1 := by
  have hx' := mem_conjSub.mp hx
  have := C.V_sq hx'
  set g : G := (C.D.kf j : G)
  have e1 : x * x = g * ((g⁻¹ * x * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
  rw [e1, this]
  group

theorem exists_zf (j : Ω) : ∃ x : G, x ∈ C.D.Vf (conjClosure Zs L2) j ∧ x ∉ Zs := by
  by_contra hcon
  push Not at hcon
  have hle : C.D.Vf (conjClosure Zs L2) j ≤ Zs := fun x hx => hcon x hx
  have h1 := Subgroup.card_le_of_le hle
  rw [C.Vf_card, C.h.card_Z] at h1
  omega

@[expose] noncomputable def zf (j : Ω) : G := (C.exists_zf j).choose

theorem zf_mem (j : Ω) : C.zf j ∈ C.D.Vf (conjClosure Zs L2) j :=
  (C.exists_zf j).choose_spec.1

theorem zf_not_mem (j : Ω) : C.zf j ∉ Zs := (C.exists_zf j).choose_spec.2

theorem index_Zs_Vf (j : Ω) : (Zs.subgroupOf (C.D.Vf (conjClosure Zs L2) j)).index = 2 := by
  have hZV := C.Zs_le_Vf j
  have h4 : (Zs.subgroupOf (C.D.Vf (conjClosure Zs L2) j)).index *
      Nat.card ↥(Zs.subgroupOf (C.D.Vf (conjClosure Zs L2) j)) =
      Nat.card ↥(C.D.Vf (conjClosure Zs L2) j) := Subgroup.index_mul_card _
  have h5 : Nat.card ↥(Zs.subgroupOf (C.D.Vf (conjClosure Zs L2) j)) = 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv).trans C.h.card_Z
  rw [h5, C.Vf_card] at h4
  omega

theorem Vf_eq {j : Ω} {x : G} (hx : x ∈ C.D.Vf (conjClosure Zs L2) j) :
    x ∈ Zs ∨ (C.zf j)⁻¹ * x ∈ Zs := by
  by_cases hxZ : x ∈ Zs
  · exact Or.inl hxZ
  · exact Or.inr (F112J2.inv_mul_mem_of_not_mem (C.index_Zs_Vf j) (C.zf_mem j) hx
      (C.zf_not_mem j) hxZ)

theorem Vf_le_U (j : Ω) : C.D.Vf (conjClosure Zs L2) j ≤ vBeta K1 L2 S Zs := by
  rw [C.U_eq]
  exact le_iSup (fun j => C.D.Vf (conjClosure Zs L2) j) j

theorem zf_mem_U (j : Ω) : C.zf j ∈ vBeta K1 L2 S Zs := C.Vf_le_U j (C.zf_mem j)

theorem U_le_sup : vBeta K1 L2 S Zs ≤ K1 ⊔ S := by
  refine conjClosure_le fun c hc v hv => ?_
  have hvC : v ∈ K1 ⊔ S := (pCoreOf_le 2 (K1 ⊔ S)) (C.h.V_le hv)
  exact (K1 ⊔ S).mul_mem ((K1 ⊔ S).mul_mem hc hvC) ((K1 ⊔ S).inv_mem hc)

theorem Zs_central {u z : G} (hu : u ∈ vBeta K1 L2 S Zs) (hz : z ∈ Zs) : u * z = z * u := by
  have hC : K1 ⊔ S ≤ Subgroup.centralizer (Zs : Set G) :=
    sup_le C.h.K1_cent_Z (F112J2.S_le_centralizer_Z C.h)
  have := Subgroup.mem_centralizer_iff.mp (hC (C.U_le_sup hu)) z hz
  exact this.symm

theorem U_eq_closure {z₀ : G} (hz₀ : z₀ ∈ Zs) (hne : z₀ ≠ 1) :
    vBeta K1 L2 S Zs = Subgroup.closure (insert z₀ (Set.range C.zf)) := by
  apply le_antisymm
  · rw [C.U_eq]
    refine iSup_le fun j x hx => ?_
    have hZ : Zs ≤ Subgroup.closure (insert z₀ (Set.range C.zf)) :=
      (C.Zs_eq_zpowers hz₀ hne).le.trans
        ((Subgroup.zpowers_eq_closure z₀).le.trans (Subgroup.closure_mono (by simp)))
    rcases C.Vf_eq hx with h1 | h1
    · exact hZ h1
    · have : x = C.zf j * ((C.zf j)⁻¹ * x) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr ⟨j, rfl⟩)) (hZ h1)
  · rw [Subgroup.closure_le]
    rintro x (rfl | ⟨j, rfl⟩)
    · exact F112J2.Zs_le_vBeta K1 L2 S Zs hz₀
    · exact C.zf_mem_U j

theorem U_comm_mem {x y : G} (hx : x ∈ vBeta K1 L2 S Zs) (hy : y ∈ vBeta K1 L2 S Zs) :
    x * y * x⁻¹ * y⁻¹ ∈ Zs := by
  have := Subgroup.commutator_mem_commutator hx hy
  rw [C.hcomm] at this
  exact this

@[expose] noncomputable def cm (i j : Ω) : G := C.zf i * C.zf j * (C.zf i)⁻¹ * (C.zf j)⁻¹

theorem cm_mem (i j : Ω) : C.cm i j ∈ Zs := C.U_comm_mem (C.zf_mem_U i) (C.zf_mem_U j)

theorem conj_zf (k : ↥K1) (i : Ω) :
    ∃ ε ∈ Zs, (k : G) * C.zf i * (k : G)⁻¹ = C.zf (C.D.act k i) * ε := by
  set m : G := (k : G) * C.zf i * (k : G)⁻¹ with hm
  have hmV : m ∈ C.D.Vf (conjClosure Zs L2) (C.D.act k i) := by
    have h1 : m ∈ conjSub (k : G) (C.D.Vf (conjClosure Zs L2) i) :=
      mul_mem_conjSub (C.zf_mem i)
    rwa [C.D.conjSub_Vf C.hVn k i] at h1
  have hmZ : m ∉ Zs := by
    intro hmZ
    apply C.zf_not_mem i
    have hk : ((k : ↥K1) : G) ∈ Subgroup.centralizer (Zs : Set G) := C.h.K1_cent_Z k.2
    have hcomm : m * (k : G) = (k : G) * m := Subgroup.mem_centralizer_iff.mp hk m hmZ
    have e : C.zf i = m := by
      calc C.zf i = (k : G)⁻¹ * ((k : G) * C.zf i * (k : G)⁻¹) * (k : G) := by group
        _ = (k : G)⁻¹ * (m * (k : G)) := by rw [hm]; group
        _ = (k : G)⁻¹ * ((k : G) * m) := by rw [hcomm]
        _ = m := by group
    rw [e]
    exact hmZ
  rcases C.Vf_eq hmV with h1 | h1
  · exact absurd h1 hmZ
  · exact ⟨_, h1, by group⟩

theorem cm_equivariant (k : ↥K1) (i j : Ω) :
    C.cm (C.D.act k i) (C.D.act k j) = C.cm i j := by
  obtain ⟨ε₁, hε₁, e₁⟩ := C.conj_zf k i
  obtain ⟨ε₂, hε₂, e₂⟩ := C.conj_zf k j
  set a' := C.zf (C.D.act k i) with ha'
  set b' := C.zf (C.D.act k j) with hb'
  have hkc : ((k : ↥K1) : G) ∈ Subgroup.centralizer (Zs : Set G) := C.h.K1_cent_Z k.2
  have h2 : ((k : G) * C.zf i * (k : G)⁻¹) * ((k : G) * C.zf j * (k : G)⁻¹) *
      ((k : G) * C.zf i * (k : G)⁻¹)⁻¹ * ((k : G) * C.zf j * (k : G)⁻¹)⁻¹ = C.cm i j := by
    have e : ((k : G) * C.zf i * (k : G)⁻¹) * ((k : G) * C.zf j * (k : G)⁻¹) *
        ((k : G) * C.zf i * (k : G)⁻¹)⁻¹ * ((k : G) * C.zf j * (k : G)⁻¹)⁻¹ =
        (k : G) * C.cm i j * (k : G)⁻¹ := by
      unfold FamCtx.cm
      group
    rw [e]
    have hc : C.cm i j * (k : G) = (k : G) * C.cm i j :=
      Subgroup.mem_centralizer_iff.mp hkc _ (C.cm_mem i j)
    rw [← hc]
    group
  rw [e₁, e₂] at h2
  have hεδ : ε₁ * ε₂ = ε₂ * ε₁ := by
    have := C.Zs_central (F112J2.Zs_le_vBeta K1 L2 S Zs hε₂) hε₁
    exact this.symm
  have hδa : ε₂ * a' = a' * ε₂ := (C.Zs_central (C.zf_mem_U _) hε₂).symm
  have hεb : ε₁ * b' = b' * ε₁ := (C.Zs_central (C.zf_mem_U _) hε₁).symm
  rw [F112J2.commutator_mul_central hεb hεδ hδa] at h2
  exact h2

theorem cm_const {i j i' j' : Ω} (hij : i ≠ j) (hij' : i' ≠ j') : C.cm i' j' = C.cm i j := by
  obtain ⟨k, hk1, hk2⟩ := C.twoTrans hij hij'
  have := C.cm_equivariant k i j
  rw [hk1, hk2] at this
  exact this

theorem cm_ne_one {i j : Ω} (hij : i ≠ j) : C.cm i j ≠ 1 := by
  intro hc
  obtain ⟨z₁, hz₁, hne⟩ := C.exists_ne_one
  have hall : ∀ a b : Ω, C.zf a * C.zf b = C.zf b * C.zf a := by
    intro a b
    by_cases hab : a = b
    · rw [hab]
    · have h1 : C.cm a b = 1 := by
        rw [C.cm_const hij hab, hc]
      have h2 : C.zf a * C.zf b * (C.zf a)⁻¹ * (C.zf b)⁻¹ = 1 := h1
      calc C.zf a * C.zf b
          = (C.zf a * C.zf b * (C.zf a)⁻¹ * (C.zf b)⁻¹) * (C.zf b * C.zf a) := by group
        _ = C.zf b * C.zf a := by rw [h2, one_mul]
  have hU : ∀ x ∈ Subgroup.closure (insert z₁ (Set.range C.zf)),
      ∀ y ∈ Subgroup.closure (insert z₁ (Set.range C.zf)), x * y = y * x := by
    intro x hx y hy
    refine F112J2.closure_comm (T := insert z₁ (Set.range C.zf)) ?_ hx hy
    rintro a (rfl | ⟨i, rfl⟩) b (rfl | ⟨j, rfl⟩)
    · rfl
    · exact (C.Zs_central (C.zf_mem_U j) hz₁).symm
    · exact C.Zs_central (C.zf_mem_U i) hz₁
    · exact hall i j
  have hab : ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hx' : x ∈ Subgroup.closure (insert z₁ (Set.range C.zf)) := by
      rw [← C.U_eq_closure hz₁ hne]
      exact hx
    have hy' : y ∈ Subgroup.closure (insert z₁ (Set.range C.zf)) := by
      rw [← C.U_eq_closure hz₁ hne]
      exact hy
    exact hU y hy' x hx'
  rw [C.hcomm] at hab
  have := C.h.card_Z
  rw [hab, Subgroup.card_bot] at this
  omega

end FamCtx

end Ctx

end SzR1

end CFSG.Quasithin
