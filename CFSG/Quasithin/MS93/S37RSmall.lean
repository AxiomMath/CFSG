module

public import CFSG.Quasithin.MS93.S37RRad

public section

namespace CFSG.Quasithin.MS93.S37R

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36 CFSG.Quasithin.Vol2
open CFSG.Quasithin.MS93.S37 CFSG.Quasithin.MS93.S37L
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]

namespace Dat

variable {C : Cfg M T L F} (D : Dat C)

theorem Ψ_rad_mem_A (s : F) :
    D.Ψ (iota (0, s)) ∈ Uq M T L ⊓ Subgroup.centralizer (L : Set G) := by
  have h := D.hβ (iota (0, s)) (D.hU _)
  have h0 : C.N.co ⟨D.Ψ (iota (0, s)), D.hU _⟩ = 0 := by
    rw [h]
    funext i
    rcases i with i | i <;> rfl
  exact (C.N.co_eq_zero_iff _).1 h0

omit [Fintype F] in
theorem iota_add (v w : (Fin 2 → F) × F) : iota (v + w) = iota v * iota w := by
  apply Multiplicative.toAdd.injective
  simp only [iota, toAdd_mul, toAdd_ofAdd, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
  congr 1
  funext i
  rcases i with i | i <;> simp

theorem exists_rad_ker
    (hA : Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) < Nat.card F) :
    ∃ k : F, k ≠ 0 ∧ D.Ψ (iota (0, k)) = 1 := by
  by_contra hne
  push Not at hne
  let f : F → ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) :=
    fun k => ⟨D.Ψ (iota (0, k)), D.Ψ_rad_mem_A k⟩
  have hf : Function.Injective f := fun k k' h => by
    have h1 : D.Ψ (iota (0, k)) = D.Ψ (iota (0, k')) := congrArg Subtype.val h
    by_contra hkk
    apply hne (k - k') (sub_ne_zero.2 hkk)
    have e : iota ((0 : Fin 2 → F), k) = iota (0, k - k') * iota (0, k') := by
      rw [← iota_add]
      congr 1
      simp
    have h2 : D.Ψ (iota (0, k - k')) * D.Ψ (iota (0, k')) = 1 * D.Ψ (iota (0, k')) := by
      rw [← map_mul, ← e, h1, one_mul]
    exact mul_right_cancel h2
  have := Nat.card_le_card_of_injective f hf
  omega

variable [CharP F 2]

theorem exists_comm_eq
    (hA : Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) < Nat.card F)
    {r : G} (hr : r ∈ C.Usub (ln₀ F)) (hrA : r ∉ Uq M T L ⊓ Subgroup.centralizer (L : Set G)) :
    ∃ x y, ⁅D.z y, D.u x⁆ = r := by
  obtain ⟨hrU, hco⟩ := (C.mem_Usub).1 hr
  set e : Fin 2 → F := fun i => C.N.co ⟨r, hrU⟩ (.inl i) with he
  have hce : C.N.co ⟨r, hrU⟩ = Sum.elim e 0 := eq_elim_of_mem_ln₀ hco
  have he0 : e ≠ 0 := fun h0 => hrA ((C.N.co_eq_zero_iff _).1 (by
    rw [hce, h0]; funext i; rcases i with i | i <;> rfl))
  obtain ⟨w, hw⟩ := D.hs r hrU
  have hw1 : (Multiplicative.toAdd w).1 = Sum.elim e 0 := by
    rw [← hce, ← D.hβ w (D.hU w)]
    exact congrArg C.N.co (Subtype.ext hw)
  have hwi : w = iota (e, (Multiplicative.toAdd w).2) := by
    apply Multiplicative.toAdd.injective
    exact Prod.ext hw1 rfl
  obtain ⟨s', hs'0, hs'⟩ : ∃ s' : F, s' ≠ 0 ∧ D.Ψ (iota (e, s')) = r := by
    by_cases hs0 : (Multiplicative.toAdd w).2 = 0
    · obtain ⟨k, hk0, hk⟩ := D.exists_rad_ker hA
      refine ⟨k, hk0, ?_⟩
      have e1 : iota (e, k) = iota (e, (Multiplicative.toAdd w).2) * iota (0, k) := by
        rw [← iota_add, hs0]
        congr 1
        simp
      rw [e1, map_mul, hk, mul_one, ← hwi, hw]
    · exact ⟨_, hs0, by rw [← hwi, hw]⟩
  obtain ⟨x, hxe, hgood⟩ := D.exists_good_x he0 hs'0
  obtain ⟨y, hy⟩ := hgood e
  refine ⟨x, y, ?_⟩
  rw [D.comm_z, ← hs']
  congr 2
  rw [lc, hy, qv_eq_dot, hy, hxe]

theorem tImage_A_le_A
    (hA : Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) < Nat.card F) :
    tImage D.θ (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) ≤
      Uq M T L ⊓ Subgroup.centralizer (L : Set G) := by
  intro r hr
  by_contra hrA
  obtain ⟨x, y, hxy⟩ := D.exists_comm_eq hA (D.tImage_A_le hr) hrA
  obtain ⟨a, haT, ha, rfl⟩ := mem_tImage.1 hr
  have e : ⁅D.z y, D.u x⁆ = ((D.θ ⁅(⟨D.u y, D.u_mem_T1 y⟩ : ↥(T1 M T L)),
      D.θ⁻¹ ⟨D.u x, D.u_mem_T1 x⟩⁆ : ↥(T1 M T L)) : G) := by
    rw [map_commutatorElement, MulAut.apply_inv_self]
    rfl
  have hinj : ⁅(⟨D.u y, D.u_mem_T1 y⟩ : ↥(T1 M T L)), D.θ⁻¹ ⟨D.u x, D.u_mem_T1 x⟩⁆ =
      ⟨a, haT⟩ := D.θ.injective (Subtype.ext (by rw [← e, hxy]))
  have hval : ⁅D.u y, D.zi x⁆ = a := congrArg Subtype.val hinj
  have haA : ⁅D.u y, D.zi x⁆ ∈ Uq M T L ⊓ Subgroup.centralizer (L : Set G) := by
    rw [hval]
    exact ha
  have hinv : ⁅D.zi x, D.u y⁆ ∈ Uq M T L ⊓ Subgroup.centralizer (L : Set G) := by
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ haA
  have h1 := eq_one_of_comm_mem_A C (T1_le_sup (D.zi_mem_T1 x)) (D.u_mem y) hinv
  apply hrA
  have h2 : a = 1 := by
    rw [← hval, ← commutatorElement_inv, h1, inv_one]
  have : (⟨a, haT⟩ : ↥(T1 M T L)) = 1 := Subtype.ext h2
  rw [this, map_one]
  exact Subgroup.one_mem _

omit [CharP F 2] in
theorem re_mem_R₀ (e : Fin 2 → F) : D.Ψ (iota (e, 0)) ∈ C.Usub (ln₀ F) := by
  refine (C.mem_Usub).2 ⟨D.hU _, ?_⟩
  rw [D.hβ]
  rw [mem_ln₀]
  exact ⟨rfl, rfl⟩

theorem θ_mem_R₀ {r : G} (hr : r ∈ C.Usub (ln₀ F)) :
    ((D.θ ⟨r, R₀_le_T1 hr⟩ : ↥(T1 M T L)) : G) ∈ C.Usub (ln₀ F) := by
  rw [← D.tImage_R₀]
  exact mem_tImage.2 ⟨r, R₀_le_T1 hr, hr, rfl⟩

@[expose] noncomputable def thb (e : Fin 2 → F) : Fin 2 → F := fun i =>
  C.N.co ⟨_, (C.Usub_le _) (D.θ_mem_R₀ (D.re_mem_R₀ e))⟩ (.inl i)

theorem tImage_A_eq
    (hA : Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) < Nat.card F) :
    tImage D.θ (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) =
      Uq M T L ⊓ Subgroup.centralizer (L : Set G) := by
  have hAT : Uq M T L ⊓ Subgroup.centralizer (L : Set G) ≤ T1 M T L :=
    inf_le_left.trans C.Uq_le_T1
  refine Subgroup.eq_of_le_of_card_ge (D.tImage_A_le_A hA) ?_
  rw [card_tImage D.θ hAT]

theorem co_θ_eq
    (hA : Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) < Nat.card F)
    {r : G} (hr : r ∈ C.Usub (ln₀ F)) {e : Fin 2 → F}
    (hco : C.N.co ⟨r, (C.Usub_le _) hr⟩ = Sum.elim e 0) :
    C.N.co ⟨_, (C.Usub_le _) (D.θ_mem_R₀ hr)⟩ = Sum.elim (D.thb e) 0 := by
  have hre := D.re_mem_R₀ e
  have ha : (D.Ψ (iota (e, 0)))⁻¹ * r ∈ Uq M T L ⊓ Subgroup.centralizer (L : Set G) := by
    have h1 : C.N.co ⟨D.Ψ (iota (e, 0)), D.hU _⟩ = C.N.co ⟨r, (C.Usub_le _) hr⟩ := by
      rw [hco]
      exact D.hβ _ _
    exact (C.N.co_eq_co_iff ⟨_, D.hU _⟩ ⟨r, (C.Usub_le _) hr⟩).1 h1
  have haT : (D.Ψ (iota (e, 0)))⁻¹ * r ∈ T1 M T L := inf_le_left.trans C.Uq_le_T1 ha
  have hθa : ((D.θ ⟨_, haT⟩ : ↥(T1 M T L)) : G) ∈ Uq M T L ⊓ Subgroup.centralizer (L : Set G) :=
    D.tImage_A_le_A hA (mem_tImage.2 ⟨_, haT, ha, rfl⟩)
  have e1 : ((D.θ ⟨r, R₀_le_T1 hr⟩ : ↥(T1 M T L)) : G) =
      ((D.θ ⟨_, R₀_le_T1 hre⟩ : ↥(T1 M T L)) : G) * ((D.θ ⟨_, haT⟩ : ↥(T1 M T L)) : G) := by
    rw [← Subgroup.coe_mul, ← map_mul]
    congr 2
    exact Subtype.ext (by simp)
  have e2 : (⟨_, (C.Usub_le _) (D.θ_mem_R₀ hr)⟩ : ↥(Uq M T L)) =
      ⟨((D.θ ⟨_, R₀_le_T1 hre⟩ : ↥(T1 M T L)) : G), (C.Usub_le _) (D.θ_mem_R₀ hre)⟩ *
        ⟨((D.θ ⟨_, haT⟩ : ↥(T1 M T L)) : G), hθa.1⟩ := Subtype.ext e1
  rw [e2, C.N.co_mul,
    (C.N.co_eq_zero_iff ⟨((D.θ ⟨_, haT⟩ : ↥(T1 M T L)) : G), hθa.1⟩).2 hθa, add_zero]
  exact eq_elim_of_mem_ln₀ ((C.mem_Usub).1 (D.θ_mem_R₀ hre)).2 |>.trans rfl

section Small

variable (hA : Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) < Nat.card F)
include hA

theorem thb_add (e e' : Fin 2 → F) : D.thb (e + e') = D.thb e + D.thb e' := by
  have hr : D.Ψ (iota (e, 0)) * D.Ψ (iota (e', 0)) ∈ C.Usub (ln₀ F) :=
    (C.Usub (ln₀ F)).mul_mem (D.re_mem_R₀ e) (D.re_mem_R₀ e')
  have hco : C.N.co ⟨_, (C.Usub_le _) hr⟩ = Sum.elim (e + e') 0 := by
    rw [show (⟨_, (C.Usub_le _) hr⟩ : ↥(Uq M T L)) = ⟨_, D.hU _⟩ * ⟨_, D.hU _⟩ from rfl,
      C.N.co_mul, D.hβ, D.hβ]
    funext i
    rcases i with i | i <;> simp [iota]
  have h := D.co_θ_eq hA hr hco
  have e1 : ((D.θ ⟨_, R₀_le_T1 hr⟩ : ↥(T1 M T L)) : G) =
      ((D.θ ⟨_, R₀_le_T1 (D.re_mem_R₀ e)⟩ : ↥(T1 M T L)) : G) *
        ((D.θ ⟨_, R₀_le_T1 (D.re_mem_R₀ e')⟩ : ↥(T1 M T L)) : G) := by
    show ((D.θ (⟨_, R₀_le_T1 (D.re_mem_R₀ e)⟩ * ⟨_, R₀_le_T1 (D.re_mem_R₀ e')⟩) :
      ↥(T1 M T L)) : G) = _
    rw [map_mul]
    rfl
  have e2 : (⟨_, (C.Usub_le _) (D.θ_mem_R₀ hr)⟩ : ↥(Uq M T L)) =
      ⟨_, (C.Usub_le _) (D.θ_mem_R₀ (D.re_mem_R₀ e))⟩ *
        ⟨_, (C.Usub_le _) (D.θ_mem_R₀ (D.re_mem_R₀ e'))⟩ := Subtype.ext e1
  rw [e2, C.N.co_mul] at h
  funext i
  have := congrFun h (.inl i)
  simp only [Pi.add_apply, Sum.elim_inl] at this
  exact this.symm

theorem thb_inj {e : Fin 2 → F} (h : D.thb e = 0) : e = 0 := by
  have hre := D.re_mem_R₀ e
  have hθA : ((D.θ ⟨_, R₀_le_T1 hre⟩ : ↥(T1 M T L)) : G) ∈
      Uq M T L ⊓ Subgroup.centralizer (L : Set G) := by
    refine (C.N.co_eq_zero_iff ⟨_, (C.Usub_le _) (D.θ_mem_R₀ hre)⟩).1 ?_
    rw [eq_elim_of_mem_ln₀ ((C.mem_Usub).1 (D.θ_mem_R₀ hre)).2]
    have h' : (fun i => C.N.co ⟨_, (C.Usub_le _) (D.θ_mem_R₀ hre)⟩ (.inl i)) = 0 := h
    rw [h']
    funext i
    rcases i with i | i <;> rfl
  have hAT : Uq M T L ⊓ Subgroup.centralizer (L : Set G) ≤ T1 M T L :=
    inf_le_left.trans C.Uq_le_T1
  have hinv := tImage_inv_eq hAT (D.tImage_A_eq hA)
  have hmem : D.Ψ (iota (e, 0)) ∈ Uq M T L ⊓ Subgroup.centralizer (L : Set G) := by
    rw [← hinv]
    refine mem_tImage.2 ⟨_, (D.θ ⟨_, R₀_le_T1 hre⟩).2, hθA, ?_⟩
    simp
  have h0 := (C.N.co_eq_zero_iff ⟨_, D.hU _⟩).2 hmem
  rw [D.hβ] at h0
  funext i
  exact congrFun h0 (.inl i)

@[expose] noncomputable def thbHom : (Fin 2 → F) →+ (Fin 2 → F) where
  toFun := D.thb
  map_zero' := by
    have := D.thb_add hA 0 0
    rw [add_zero] at this
    exact (add_eq_left.1 this.symm)
  map_add' := D.thb_add hA

@[expose] noncomputable def thbEquiv : (Fin 2 → F) ≃+ (Fin 2 → F) :=
  AddEquiv.ofBijective (D.thbHom hA) (by
    have hinj : Function.Injective (D.thbHom hA) := by
      rw [injective_iff_map_eq_zero]
      exact fun e h => D.thb_inj hA h
    exact ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩)

theorem thbEquiv_apply (e : Fin 2 → F) : D.thbEquiv hA e = D.thb e := rfl

end Small

section Small2

variable (hA : Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) < Nat.card F)
include D hA

theorem thb_mv (x y : Fin 2 → F) : D.thb (mv (D.Φ' x) y) = mv (D.Φ y) x := by
  have hr : ⁅D.zi x, D.u y⁆ ∈ C.Usub (ln₀ F) := by
    refine (C.mem_Usub).2 ⟨by rw [D.comm_zi]; exact D.hU _, ?_⟩
    rw [show (⟨⁅D.zi x, D.u y⁆, _⟩ : ↥(Uq M T L)) = ⟨D.Ψ (iota (lc (D.Φ' x) y)), D.hU _⟩ from
      Subtype.ext (D.comm_zi x y), D.hβ, mem_ln₀]
    exact ⟨rfl, rfl⟩
  have hco : C.N.co ⟨⁅D.zi x, D.u y⁆, (C.Usub_le _) hr⟩ = Sum.elim (mv (D.Φ' x) y) 0 := by
    rw [show (⟨⁅D.zi x, D.u y⁆, _⟩ : ↥(Uq M T L)) = ⟨D.Ψ (iota (lc (D.Φ' x) y)), D.hU _⟩ from
      Subtype.ext (D.comm_zi x y), D.hβ]
    rfl
  have h := D.co_θ_eq hA hr hco
  have hθ : ((D.θ ⟨⁅D.zi x, D.u y⁆, R₀_le_T1 hr⟩ : ↥(T1 M T L)) : G) =
      (D.Ψ (iota (lc (D.Φ y) x)))⁻¹ := by
    rw [← D.comm_z, commutatorElement_inv]
    exact D.θ_comm_zi x y
  have hco' : C.N.co ⟨_, (C.Usub_le _) (D.θ_mem_R₀ hr)⟩ = Sum.elim (mv (D.Φ y) x) 0 := by
    rw [show (⟨_, (C.Usub_le _) (D.θ_mem_R₀ hr)⟩ : ↥(Uq M T L)) =
      ⟨D.Ψ (iota (lc (D.Φ y) x))⁻¹, D.hU _⟩ from Subtype.ext (hθ.trans (map_inv D.Ψ _).symm), D.hβ,
      toAdd_inv]
    funext i
    rcases i with i | i <;> simp [iota, lc, CharTwo.neg_eq]
  rw [hco'] at h
  funext i
  exact (congrFun h (.inl i)).symm

theorem coc_eq_zero {x : G} (hx : x ∈ pCoreOf 2 M) {B : F}
    (hB : ∀ g, C.coc hx g = S5.cform B 0 g) : B = 0 := by
  have hq : 2 < Fintype.card F := by have := D.hq; rw [Nat.card_eq_fintype_card] at this; omega
  obtain ⟨x₁, -, -, hg₁, -⟩ := D.exists_good_pair
  have hline : ∀ w : F × F × F, ∃ y, ∀ c : F, D.ΦHom y ≠ c • w := by
    by_contra hcon
    push Not at hcon
    obtain ⟨w, hw⟩ := hcon
    choose f hf using hw
    have hinj : Function.Injective (fun t : ↥D.E₃ => f (Classical.choose t.2)) := by
      intro t t' h
      apply Subtype.ext
      rw [← Classical.choose_spec t.2, ← Classical.choose_spec t'.2, hf, hf]
      exact congrArg (· • w) h
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [D.card_E₃] at h1
    have : 1 < Nat.card F := by have := D.hq; omega
    nlinarith
  set t'' := D.θ⁻¹ ⟨x, C.pCore_le_T1 hx⟩ with ht''
  set C'' := S5.q1Coord (C.rho ⟨(t'' : G), T1_le_sup t''.2⟩)
  have hBy : ∀ y, D.thbEquiv hA (mv C'' y) = B • sd (D.ΦHom y) := by
    intro y
    have hc : ⁅D.u y, (t'' : G)⁆ ∈ Uq M T L := by
      have := C.comm_mem_Uq_of_mem (C.h.le (T1_le_T t''.2)) (D.u_mem y)
      rw [← commutatorElement_inv]
      exact (Uq M T L).inv_mem this
    have hco := D.co_comm_u_T1 y t''.2 hc
    have hr : ⁅D.u y, (t'' : G)⁆ ∈ C.Usub (ln₀ F) := (C.mem_Usub).2 ⟨hc, by
      rw [hco, mem_ln₀]; exact ⟨rfl, rfl⟩⟩
    have h := D.co_θ_eq hA hr hco
    have hθ : ((D.θ ⟨⁅D.u y, (t'' : G)⁆, R₀_le_T1 hr⟩ : ↥(T1 M T L)) : G) = ⁅D.z y, x⁆ := by
      have e : (⟨⁅D.u y, (t'' : G)⁆, R₀_le_T1 hr⟩ : ↥(T1 M T L)) =
          ⁅(⟨D.u y, D.u_mem_T1 y⟩ : ↥(T1 M T L)), t''⁆ := rfl
      rw [e, map_commutatorElement, ht'', MulAut.apply_inv_self]
      rfl
    have hco' := D.co_comm_z_pCore y hx hB
    rw [show (⟨_, (C.Usub_le _) (D.θ_mem_R₀ hr)⟩ : ↥(Uq M T L)) =
      ⟨⁅D.z y, x⁆, (C.Usub_le _) (D.comm_z_mem_R₀ y hx)⟩ from Subtype.ext hθ, hco'] at h
    rw [thbEquiv_apply, D.ΦHom_apply]
    funext i
    exact (congrFun h (.inl i)).symm
  exact eq_zero_of_semilin hq D.ΦHom D.Φ' (D.thbEquiv hA) (fun x y => D.thb_mv hA x y) hg₁
    hline hBy

theorem pCore_eq_UD : ∀ x ∈ pCoreOf 2 M, ∃ v ∈ Uq M T L, v⁻¹ * x ∈ Dq M L := by
  intro x hx
  obtain ⟨v, hv, B, hx', hB⟩ := exists_normal_coc C hx
  have hB0 := D.coc_eq_zero hA hx' hB
  refine ⟨v, hv, C.mem_Dq_of_coc_eq_zero hx' fun g => ?_⟩
  rw [hB, hB0]
  simp [S5.cform]

theorem rhoIm_eq_small : C.rhoIm (Qt M D.θ) = C.rhoIm (Ut M T L D.θ) :=
  D.rhoIm_eq_of (D.pCore_eq_UD hA) fun _ hd => D.tImage_D_le_of (D.tImage_A_le_A hA) hd

end Small2

end Dat

end CFSG.Quasithin.MS93.S37R
