module

public import CFSG.Quasithin.Recognition.F112J2FamA
public import CFSG.Quasithin.Recognition.F112J2Torus

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.A5Model
open scoped commutatorElement

namespace F112J2

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

structure FiveCtx (K1 L2 S Zs : Subgroup G) where
  h : R1SettingLegacyBare K1 L2 S Zs
  hR : Hyp111R K1 L2 S
  D : ActData K1 S
  hcomm : ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ = Zs

omit [Finite G] in
theorem Zs_le_vBeta (K1 L2 S Zs : Subgroup G) : Zs ≤ vBeta K1 L2 S Zs :=
  (le_conjClosure Zs L2).trans (le_conjClosure (conjClosure Zs L2) (K1 ⊔ S))

omit [Finite G] in
theorem commutator_mul_central {a b ε δ : G} (hεb : ε * b = b * ε) (hεδ : ε * δ = δ * ε)
    (hδa : δ * a = a * δ) :
    (a * ε) * (b * δ) * (a * ε)⁻¹ * (b * δ)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have hδa' : δ * a⁻¹ = a⁻¹ * δ := by
    calc δ * a⁻¹ = a⁻¹ * (a * δ) * a⁻¹ := by group
      _ = a⁻¹ * (δ * a) * a⁻¹ := by rw [hδa]
      _ = a⁻¹ * δ := by group
  calc (a * ε) * (b * δ) * (a * ε)⁻¹ * (b * δ)⁻¹
      = a * (ε * b) * δ * ε⁻¹ * a⁻¹ * δ⁻¹ * b⁻¹ := by group
    _ = a * (b * ε) * δ * ε⁻¹ * a⁻¹ * δ⁻¹ * b⁻¹ := by rw [hεb]
    _ = a * b * (ε * δ) * ε⁻¹ * a⁻¹ * δ⁻¹ * b⁻¹ := by group
    _ = a * b * (δ * ε) * ε⁻¹ * a⁻¹ * δ⁻¹ * b⁻¹ := by rw [hεδ]
    _ = a * b * δ * a⁻¹ * δ⁻¹ * b⁻¹ := by group
    _ = a * b * (δ * a⁻¹) * δ⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * δ) * δ⁻¹ * b⁻¹ := by rw [hδa']
    _ = a * b * a⁻¹ * b⁻¹ := by group

omit [Finite G] in
theorem closure_comm {T : Set G} (h : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) {x y : G}
    (hx : x ∈ Subgroup.closure T) (hy : y ∈ Subgroup.closure T) : x * y = y * x := by
  have h1 : Subgroup.closure T ≤ Subgroup.centralizer T := by
    rw [Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro b hb
    exact h b hb a ha
  have h2 : Subgroup.closure T ≤ Subgroup.centralizer (Subgroup.closure T : Set G) := by
    rw [Subgroup.centralizer_closure]
    exact h1
  exact (Subgroup.mem_centralizer_iff.mp (h2 hx) y hy).symm

namespace FiveCtx

variable (C : FiveCtx K1 L2 S Zs)

include C

theorem hVn : borelOf K1 S ≤ Subgroup.normalizer (conjClosure Zs L2 : Set G) :=
  (le_sup_left.trans le_sup_left : borelOf K1 S ≤ bigB K1 L2 S).trans
    (bigB_le_normalizer_V C.h C.hR)

theorem hSV : S ≤ Subgroup.normalizer (conjClosure Zs L2 : Set G) :=
  (le_sup_right : S ≤ bigB K1 L2 S).trans (bigB_le_normalizer_V C.h C.hR)

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

theorem Vf_card (j : Fin 5) : Nat.card ↥(C.D.Vf (conjClosure Zs L2) j) = 4 := by
  unfold ActData.Vf
  rw [CosetGeom.card_conjSub, C.h.V_card]

theorem Zs_le_Vf (j : Fin 5) : Zs ≤ C.D.Vf (conjClosure Zs L2) j := by
  intro z hz
  have hk : ((C.D.kf j : ↥K1) : G) ∈ Subgroup.centralizer (Zs : Set G) :=
    C.h.K1_cent_Z (C.D.kf j).2
  have hcomm : z * (C.D.kf j : G) = (C.D.kf j : G) * z :=
    Subgroup.mem_centralizer_iff.mp hk z hz
  have e : (C.D.kf j : G) * z * (C.D.kf j : G)⁻¹ = z := by
    rw [← hcomm]
    group
  have hm : (C.D.kf j : G) * z * (C.D.kf j : G)⁻¹ ∈ conjSub (C.D.kf j : G) (conjClosure Zs L2) :=
    mul_mem_conjSub (le_conjClosure Zs L2 hz)
  rwa [e] at hm

theorem Vf_sq {j : Fin 5} {x : G} (hx : x ∈ C.D.Vf (conjClosure Zs L2) j) : x * x = 1 := by
  have hx' := mem_conjSub.mp hx
  have := C.V_sq hx'
  set g : G := (C.D.kf j : G)
  have e1 : x * x = g * ((g⁻¹ * x * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
  rw [e1, this]
  group

theorem exists_zf (j : Fin 5) : ∃ x : G, x ∈ C.D.Vf (conjClosure Zs L2) j ∧ x ∉ Zs := by
  by_contra hcon
  push Not at hcon
  have hle : C.D.Vf (conjClosure Zs L2) j ≤ Zs := fun x hx => hcon x hx
  have h1 := Subgroup.card_le_of_le hle
  rw [C.Vf_card, C.h.card_Z] at h1
  omega

@[expose] noncomputable def zf (j : Fin 5) : G := (C.exists_zf j).choose

theorem zf_mem (j : Fin 5) : C.zf j ∈ C.D.Vf (conjClosure Zs L2) j :=
  (C.exists_zf j).choose_spec.1

theorem zf_not_mem (j : Fin 5) : C.zf j ∉ Zs := (C.exists_zf j).choose_spec.2

theorem index_Zs_Vf (j : Fin 5) : (Zs.subgroupOf (C.D.Vf (conjClosure Zs L2) j)).index = 2 := by
  have hZV := C.Zs_le_Vf j
  have h4 : (Zs.subgroupOf (C.D.Vf (conjClosure Zs L2) j)).index *
      Nat.card ↥(Zs.subgroupOf (C.D.Vf (conjClosure Zs L2) j)) =
      Nat.card ↥(C.D.Vf (conjClosure Zs L2) j) := Subgroup.index_mul_card _
  have h5 : Nat.card ↥(Zs.subgroupOf (C.D.Vf (conjClosure Zs L2) j)) = 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv).trans C.h.card_Z
  rw [h5, C.Vf_card] at h4
  omega

theorem Vf_eq {j : Fin 5} {x : G} (hx : x ∈ C.D.Vf (conjClosure Zs L2) j) :
    x ∈ Zs ∨ (C.zf j)⁻¹ * x ∈ Zs := by
  by_cases hxZ : x ∈ Zs
  · exact Or.inl hxZ
  · exact Or.inr (inv_mul_mem_of_not_mem (C.index_Zs_Vf j) (C.zf_mem j) hx (C.zf_not_mem j) hxZ)

theorem Vf_le_U (j : Fin 5) : C.D.Vf (conjClosure Zs L2) j ≤ vBeta K1 L2 S Zs := by
  rw [C.U_eq]
  exact le_iSup (fun j => C.D.Vf (conjClosure Zs L2) j) j

theorem zf_mem_U (j : Fin 5) : C.zf j ∈ vBeta K1 L2 S Zs := C.Vf_le_U j (C.zf_mem j)

theorem U_le_sup : vBeta K1 L2 S Zs ≤ K1 ⊔ S := by
  refine conjClosure_le fun c hc v hv => ?_
  have hvC : v ∈ K1 ⊔ S := (pCoreOf_le 2 (K1 ⊔ S)) (C.h.V_le hv)
  exact (K1 ⊔ S).mul_mem ((K1 ⊔ S).mul_mem hc hvC) ((K1 ⊔ S).inv_mem hc)

theorem Zs_central {u z : G} (hu : u ∈ vBeta K1 L2 S Zs) (hz : z ∈ Zs) : u * z = z * u := by
  have hC : K1 ⊔ S ≤ Subgroup.centralizer (Zs : Set G) :=
    sup_le C.h.K1_cent_Z (S_le_centralizer_Z C.h)
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
    · exact Zs_le_vBeta K1 L2 S Zs hz₀
    · exact C.zf_mem_U j

theorem U_comm_mem {x y : G} (hx : x ∈ vBeta K1 L2 S Zs) (hy : y ∈ vBeta K1 L2 S Zs) :
    x * y * x⁻¹ * y⁻¹ ∈ Zs := by
  have := Subgroup.commutator_mem_commutator hx hy
  rw [C.hcomm] at this
  exact this

@[expose] noncomputable def cm (i j : Fin 5) : G := C.zf i * C.zf j * (C.zf i)⁻¹ * (C.zf j)⁻¹

theorem cm_mem (i j : Fin 5) : C.cm i j ∈ Zs := C.U_comm_mem (C.zf_mem_U i) (C.zf_mem_U j)

theorem conj_zf (k : ↥K1) (i : Fin 5) :
    ∃ ε ∈ Zs, (k : G) * C.zf i * (k : G)⁻¹ = C.zf ((C.D.θ k : Equiv.Perm (Fin 5)) i) * ε := by
  set m : G := (k : G) * C.zf i * (k : G)⁻¹ with hm
  have hmV : m ∈ C.D.Vf (conjClosure Zs L2) ((C.D.θ k : Equiv.Perm (Fin 5)) i) := by
    have h1 : m ∈ conjSub (k : G) (C.D.Vf (conjClosure Zs L2) i) := mul_mem_conjSub (C.zf_mem i)
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

theorem cm_equivariant (k : ↥K1) (i j : Fin 5) :
    C.cm ((C.D.θ k : Equiv.Perm (Fin 5)) i) ((C.D.θ k : Equiv.Perm (Fin 5)) j) = C.cm i j := by
  obtain ⟨ε₁, hε₁, e₁⟩ := C.conj_zf k i
  obtain ⟨ε₂, hε₂, e₂⟩ := C.conj_zf k j
  set a' := C.zf ((C.D.θ k : Equiv.Perm (Fin 5)) i) with ha'
  set b' := C.zf ((C.D.θ k : Equiv.Perm (Fin 5)) j) with hb'
  have hkc : ((k : ↥K1) : G) ∈ Subgroup.centralizer (Zs : Set G) := C.h.K1_cent_Z k.2
  have h2 : ((k : G) * C.zf i * (k : G)⁻¹) * ((k : G) * C.zf j * (k : G)⁻¹) *
      ((k : G) * C.zf i * (k : G)⁻¹)⁻¹ * ((k : G) * C.zf j * (k : G)⁻¹)⁻¹ = C.cm i j := by
    have e : ((k : G) * C.zf i * (k : G)⁻¹) * ((k : G) * C.zf j * (k : G)⁻¹) *
        ((k : G) * C.zf i * (k : G)⁻¹)⁻¹ * ((k : G) * C.zf j * (k : G)⁻¹)⁻¹ =
        (k : G) * C.cm i j * (k : G)⁻¹ := by
      unfold FiveCtx.cm
      group
    rw [e]
    have hc : C.cm i j * (k : G) = (k : G) * C.cm i j :=
      Subgroup.mem_centralizer_iff.mp hkc _ (C.cm_mem i j)
    rw [← hc]
    group
  rw [e₁, e₂] at h2
  have hεδ : ε₁ * ε₂ = ε₂ * ε₁ := by
    have := C.Zs_central (Zs_le_vBeta K1 L2 S Zs hε₂) hε₁
    exact this.symm
  have hδa : ε₂ * a' = a' * ε₂ := (C.Zs_central (C.zf_mem_U _) hε₂).symm
  have hεb : ε₁ * b' = b' * ε₁ := (C.Zs_central (C.zf_mem_U _) hε₁).symm
  rw [commutator_mul_central hεb hεδ hδa] at h2
  exact h2

theorem cm_const {i j i' j' : Fin 5} (hij : i ≠ j) (hij' : i' ≠ j') : C.cm i' j' = C.cm i j := by
  obtain ⟨g, hg1, hg2⟩ := a5_two_trans hij hij'
  obtain ⟨k, hk⟩ := C.D.surj g
  have := C.cm_equivariant k i j
  rw [hk, hg1, hg2] at this
  exact this

theorem cm_ne_one : C.cm 0 1 ≠ 1 := by
  intro hc
  obtain ⟨z₁, hz₁, hne⟩ := C.exists_ne_one
  have hall : ∀ i j : Fin 5, C.zf i * C.zf j = C.zf j * C.zf i := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · have h1 : C.cm i j = 1 := by
        rw [C.cm_const (i := 0) (j := 1) (by decide) hij, hc]
      have h2 : C.zf i * C.zf j * (C.zf i)⁻¹ * (C.zf j)⁻¹ = 1 := h1
      calc C.zf i * C.zf j
          = (C.zf i * C.zf j * (C.zf i)⁻¹ * (C.zf j)⁻¹) * (C.zf j * C.zf i) := by group
        _ = C.zf j * C.zf i := by rw [h2, one_mul]
  have hU : ∀ x ∈ Subgroup.closure (insert z₁ (Set.range C.zf)),
      ∀ y ∈ Subgroup.closure (insert z₁ (Set.range C.zf)), x * y = y * x := by
    intro x hx y hy
    refine closure_comm (T := insert z₁ (Set.range C.zf)) ?_ hx hy
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

end FiveCtx

end F112J2

end CFSG.Quasithin
