module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabG112Def
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.G112A2

open Module CFSG.Open

section Perm

open Equiv

@[expose] def s7σ0 : Perm (Fin 7) := swap 0 1 * swap 2 3

@[expose] def s7ρ0 : Perm (Fin 7) := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4

theorem s7σ0_cycleType : s7σ0.cycleType = {2, 2} := by
  have hd : Perm.Disjoint (swap (0 : Fin 7) 1) (swap 2 3) := by
    intro x
    revert x
    decide
  rw [s7σ0, hd.cycleType_mul, (Perm.isCycle_swap (by decide)).cycleType,
    (Perm.isCycle_swap (by decide)).cycleType, Perm.card_support_swap (by decide),
    Perm.card_support_swap (by decide)]
  rfl

theorem sign_s7ρ0 : Perm.sign s7ρ0 = 1 := by decide

set_option maxRecDepth 20000 in
theorem s7_pow_five : (s7σ0 * (s7ρ0 * s7σ0 * s7ρ0⁻¹)) ^ 5 = 1 := by decide

theorem s7_ne_one : s7σ0 * (s7ρ0 * s7σ0 * s7ρ0⁻¹) ≠ 1 := fun h => by
  have := congrArg (fun f : Perm (Fin 7) => f 0) h
  revert this
  decide

theorem cycleType_of_involution {σ : Perm (Fin 7)} (hσ : σ ∈ alternatingGroup (Fin 7))
    (h2 : σ * σ = 1) (h1 : σ ≠ 1) : σ.cycleType = {2, 2} := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact h2) h1
  have hall : ∀ n ∈ σ.cycleType, n = 2 := fun n hn => by
    have h1 := Perm.dvd_of_mem_cycleType hn
    have h2 := Perm.two_le_of_mem_cycleType hn
    rw [hord] at h1
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  set m := Multiset.card σ.cycleType with hm
  have hrep : σ.cycleType = Multiset.replicate m 2 := Multiset.eq_replicate.mpr ⟨rfl, hall⟩
  have hsum : σ.cycleType.sum ≤ 7 := (Perm.sum_cycleType_le σ).trans (by simp)
  rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hsign := Perm.sign_of_cycleType σ
  rw [(Perm.mem_alternatingGroup).mp hσ, hrep, Multiset.sum_replicate, smul_eq_mul,
    Multiset.card_replicate] at hsign
  have hm0 : m ≠ 0 := fun h => by
    rw [h, Multiset.replicate_zero] at hrep
    exact h1 (Perm.cycleType_eq_zero.mp hrep)
  have heven : Even (m * 2 + m) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    rw [hodd.neg_one_pow] at hsign
    exact absurd hsign (by decide)
  have hm2 : m = 2 := by
    obtain ⟨k, hk⟩ := heven
    omega
  rw [hrep, hm2]
  rfl

theorem exists_conj_orderOf_five {σ : Perm (Fin 7)} (hσ : σ ∈ alternatingGroup (Fin 7))
    (h2 : σ * σ = 1) (h1 : σ ≠ 1) :
    ∃ c ∈ alternatingGroup (Fin 7), orderOf (σ * (c * σ * c⁻¹)) = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hconj : IsConj s7σ0 σ := by
    rw [Perm.isConj_iff_cycleType_eq, s7σ0_cycleType, cycleType_of_involution hσ h2 h1]
  obtain ⟨d, hd⟩ := isConj_iff.mp hconj
  refine ⟨d * s7ρ0 * d⁻¹, ?_, ?_⟩
  · rw [Perm.mem_alternatingGroup, map_mul, map_mul, map_inv, sign_s7ρ0, mul_one, mul_inv_cancel]
  · have heq : σ * (d * s7ρ0 * d⁻¹ * σ * (d * s7ρ0 * d⁻¹)⁻¹) =
        MulAut.conj d (s7σ0 * (s7ρ0 * s7σ0 * s7ρ0⁻¹)) := by
      rw [MulAut.conj_apply, ← hd]
      group
    rw [heq, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime s7_pow_five s7_ne_one

end Perm

section Linear

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem add_self_eq_zero (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem map_sub_le {I : Submodule (ZMod 2) V} {t : V ≃ₗ[ZMod 2] V} (htI : ∀ v ∈ I, t v ∈ I) :
    I.map (t.toLinearMap - LinearMap.id) ≤ I := by
  rintro _ ⟨v, hv, rfl⟩
  exact I.sub_mem (htI v hv) hv

theorem natCard_eq_two_pow (W : Type*) [AddCommGroup W] [Module (ZMod 2) W] [Finite W] :
    Nat.card W = 2 ^ finrank (ZMod 2) W := by
  classical
  letI : Fintype W := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

theorem eq_zero_or_eq_of_finrank_one {R : Submodule (ZMod 2) V} (hR : finrank (ZMod 2) R = 1)
    {n w : V} (hn : n ∈ R) (hn0 : n ≠ 0) (hw : w ∈ R) : w = 0 ∨ w = n := by
  classical
  have hc : Nat.card R = 2 := by
    rw [natCard_eq_two_pow, hR]
    norm_num
  by_contra hne
  push Not at hne
  obtain ⟨hw0, hwn⟩ := hne
  let f : Fin 3 → ↥R := ![0, ⟨n, hn⟩, ⟨w, hw⟩]
  have hf : Function.Injective f := by
    intro i j hij
    have hij' := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp [f] at hij' ⊢
    all_goals first
      | exact absurd hij'.symm hn0 | exact absurd hij' hn0 | exact absurd hij'.symm hw0
      | exact absurd hij' hw0 | exact absurd hij'.symm hwn | exact absurd hij' hwn
  have := Nat.card_le_card_of_injective f hf
  simp at this
  omega

@[simp] theorem sub_apply_eq (t : V ≃ₗ[ZMod 2] V) (v : V) :
    ((t.toLinearMap - LinearMap.id : V →ₗ[ZMod 2] V) v) = t v - v := rfl


theorem fix_sq_of_finrank_one {I : Submodule (ZMod 2) V} {t : V ≃ₗ[ZMod 2] V}
    (htI : ∀ v ∈ I, t v ∈ I) (hr : finrank (ZMod 2) (I.map (t.toLinearMap - LinearMap.id)) = 1) :
    ∀ v ∈ I, t (t v) = v := by
  set R := I.map (t.toLinearMap - LinearMap.id) with hRdef
  have hmem : ∀ v ∈ I, t v - v ∈ R := fun v hv => ⟨v, hv, rfl⟩
  have hRI : R ≤ I := map_sub_le htI
  obtain ⟨n, hnR, hn0⟩ : ∃ n ∈ R, n ≠ 0 :=
    Submodule.exists_mem_ne_zero_of_ne_bot (fun h => by
      rw [h, finrank_bot] at hr
      exact absurd hr (by norm_num))
  have hkill : ∀ w ∈ R, t w = w := by
    intro w hw
    rcases eq_zero_or_eq_of_finrank_one hr hnR hn0 (hmem w (hRI hw)) with h | h
    · exact sub_eq_zero.mp h
    · exfalso
      rcases eq_zero_or_eq_of_finrank_one hr hnR hn0 hw with h' | h'
      · rw [h', map_zero, sub_zero] at h
        exact hn0 h.symm
      · rw [h'] at h
        have htn : t n = t 0 := by
          rw [map_zero, sub_eq_iff_eq_add.mp h, add_self_eq_zero]
        exact hn0 (t.injective htn)
  intro v hv
  have h1 := hkill _ (hmem v hv)
  rw [map_sub] at h1
  calc t (t v) = t v - v + t v := by rw [← h1]; abel
    _ = (t v + t v) - v := by abel
    _ = -v := by rw [add_self_eq_zero, zero_sub]
    _ = v := neg_eq_of_add_eq_zero_left (add_self_eq_zero v)

theorem finrank_ker_domRestrict {I : Submodule (ZMod 2) V} (hI : finrank (ZMod 2) I = 4)
    {t : V ≃ₗ[ZMod 2] V} (hr : finrank (ZMod 2) (I.map (t.toLinearMap - LinearMap.id)) = 1) :
    finrank (ZMod 2) (LinearMap.ker ((t.toLinearMap - LinearMap.id).domRestrict I)) = 3 := by
  have h := LinearMap.finrank_range_add_finrank_ker ((t.toLinearMap - LinearMap.id).domRestrict I)
  rw [LinearMap.range_domRestrict, hr, hI] at h
  omega

theorem fix_of_order_five {I : Submodule (ZMod 2) V} (hI : finrank (ZMod 2) I = 4)
    {a b : V ≃ₗ[ZMod 2] V} (haI : ∀ v ∈ I, a v ∈ I) (hbI : ∀ v ∈ I, b v ∈ I)
    (ha : finrank (ZMod 2) (I.map (a.toLinearMap - LinearMap.id)) = 1)
    (hb : finrank (ZMod 2) (I.map (b.toLinearMap - LinearMap.id)) = 1)
    (h5 : (a * b) ^ 5 = 1) : ∀ v ∈ I, (a * b) v = v := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set g := a * b with hg
  have hgI : ∀ v ∈ I, g v ∈ I := fun v hv => haI _ (hbI v hv)
  have hKa := finrank_ker_domRestrict hI ha
  have hKb := finrank_ker_domRestrict hI hb
  set Ka := LinearMap.ker ((a.toLinearMap - LinearMap.id).domRestrict I)
  set Kb := LinearMap.ker ((b.toLinearMap - LinearMap.id).domRestrict I)
  set F := LinearMap.ker ((g.toLinearMap - LinearMap.id).domRestrict I) with hF
  have hC : 2 ≤ finrank (ZMod 2) ↥(Ka ⊓ Kb) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq Ka Kb
    have hle : finrank (ZMod 2) ↥(Ka ⊔ Kb) ≤ 4 := hI ▸ Submodule.finrank_le _
    omega
  have hCF : Ka ⊓ Kb ≤ F := by
    intro w hw
    obtain ⟨hwa, hwb⟩ := Submodule.mem_inf.mp hw
    simp only [Ka, Kb, F, LinearMap.mem_ker, LinearMap.domRestrict_apply, sub_apply_eq,
      sub_eq_zero] at hwa hwb ⊢
    rw [hg, LinearEquiv.mul_apply, hwb, hwa]
  have hFr : 2 ≤ finrank (ZMod 2) F := hC.trans (Submodule.finrank_mono hCF)
  have hFle : finrank (ZMod 2) F ≤ 4 := hI ▸ Submodule.finrank_le _
  letI : Fintype ↥I := Fintype.ofFinite _
  let f : Function.End ↥I := fun w => ⟨g w, hgI w w.2⟩
  have hpow : ∀ (n : ℕ) (w : ↥I), ((f ^ n) w : V) = (g ^ n) w := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [pow_succ, pow_succ]
      show (((f ^ n) (f w)) : V) = (g ^ n * g) w
      rw [ih, LinearEquiv.mul_apply]
  have hf : f ^ 5 ^ 1 = 1 := by
    funext w
    apply Subtype.ext
    rw [pow_one, hpow, h5]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 5) (n := 1) hf
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hmod
  have hfix : Nat.card (Function.fixedPoints f) = Nat.card F := by
    refine Nat.card_congr
      { toFun := fun w => ⟨w.1, ?_⟩
        invFun := fun w => ⟨w.1, ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · have hw : f w.1 = w.1 := w.2
      have hw' : g (w.1 : V) = w.1 := congrArg Subtype.val hw
      simp only [hF, LinearMap.mem_ker, LinearMap.domRestrict_apply, sub_apply_eq, sub_eq_zero]
      exact hw'
    · have hw := w.2
      simp only [hF, LinearMap.mem_ker, LinearMap.domRestrict_apply, sub_apply_eq,
        sub_eq_zero] at hw
      exact Subtype.ext hw
  rw [hfix, natCard_eq_two_pow, natCard_eq_two_pow, hI] at hmod
  have hF4 : finrank (ZMod 2) F = 4 := by
    obtain ⟨k, hk⟩ : ∃ k, finrank (ZMod 2) F = k := ⟨_, rfl⟩
    rw [hk] at hmod hFr hFle ⊢
    interval_cases k
    · exact absurd hmod (by decide)
    · exact absurd hmod (by decide)
    · rfl
  have htop : F = ⊤ := Submodule.eq_top_of_finrank_eq (hF4.trans hI.symm)
  intro v hv
  have hmem : (⟨v, hv⟩ : ↥I) ∈ F := htop ▸ Submodule.mem_top
  simpa only [hF, LinearMap.mem_ker, LinearMap.domRestrict_apply, sub_apply_eq, sub_eq_zero]
    using hmem

end Linear


section Main

open Equiv

theorem isQuasisimple_of_simple {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hnab : ∃ a b : Q, a * b ≠ b * a) : CFSG.Open.IsQuasisimple Q := by
  obtain ⟨a, b, hab⟩ := hnab
  have hc : Subgroup.center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
    · exact h
    · exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a) hab
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
    · exfalso
      apply hab
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
      exact (Subgroup.mem_centralizer_iff.mp (h (Subgroup.mem_top b)) a (Subgroup.mem_top a))
    · exact h
  · let e : Q ⧸ Subgroup.center Q ≃* Q :=
      (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
    exact e.isSimpleGroup

@[expose] def s7τ0 : Perm (Fin 7) := swap 0 1 * swap 1 2

theorem s7τ0_mem : s7τ0 ∈ alternatingGroup (Fin 7) := by
  rw [Perm.mem_alternatingGroup]; decide

theorem s7σ0_mem : s7σ0 ∈ alternatingGroup (Fin 7) := by
  rw [Perm.mem_alternatingGroup]; decide

theorem s7_noncomm : s7τ0 * s7σ0 ≠ s7σ0 * s7τ0 := fun h => by
  have := congrArg (fun f : Perm (Fin 7) => f 0) h
  revert this
  decide

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem finrank_ne_two_of_concl8 {B : LinearMap.BilinForm (ZMod 2) V}
    {Γ X : Subgroup (V ≃ₗ[ZMod 2] V)} (hXΓ : X ≤ Γ) (h8 : G112Concl8 B Γ X)
    {t : V ≃ₗ[ZMod 2] V} (htΓ : t ∈ Γ) :
    finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) ≠ 2 := by
  classical
  intro hr
  obtain ⟨-, ⟨φ⟩, I, hI4, -, hEI, x, hxX, ⟨v0, hv0I, hxv0⟩, hcompl⟩ := h8
  have hxΓ : x ∈ Γ := hXΓ hxX
  set J := I.map (x : V →ₗ[ZMod 2] V) with hJ
  set Aγ : Subgroup ↥Γ := (alternatingGroup (Fin 7)).comap φ.toMonoidHom with hAγ
  have hmemA : ∀ g : ↥Γ, g ∈ Aγ ↔ Perm.sign (φ g) = 1 := fun g => by
    rw [hAγ, Subgroup.mem_comap, Perm.mem_alternatingGroup]
    rfl
  have hAn : Aγ.Normal := Subgroup.Normal.comap inferInstance _
  have hAeq : Aγ.map φ.toMonoidHom = alternatingGroup (Fin 7) :=
    Subgroup.map_comap_eq_self_of_surjective φ.surjective _
  let eA : ↥Aγ ≃* ↥(alternatingGroup (Fin 7)) :=
    (Aγ.equivMapOfInjective φ.toMonoidHom φ.injective).trans (MulEquiv.subgroupCongr hAeq)
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup ↥Aγ := eA.isSimpleGroup
  have hnab : ∃ a b : ↥Aγ, a * b ≠ b * a := by
    refine ⟨eA.symm ⟨s7τ0, s7τ0_mem⟩, eA.symm ⟨s7σ0, s7σ0_mem⟩, fun h => s7_noncomm ?_⟩
    have := congrArg (fun g => ((eA g : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7))) h
    simpa using this
  have hcomp : IsComponentOf Aγ ⊤ :=
    ⟨le_top, IsSubnormal.step le_top (hAn.comap (⊤ : Subgroup ↥Γ).subtype)
      (IsSubnormal.refl ⊤), isQuasisimple_of_simple hnab⟩
  have hAE : Aγ ≤ genFittingLayer ↥Γ := by
    rw [genFittingLayer.eq_sSup]
    exact le_sSup hcomp
  have hAI : ∀ g : ↥Γ, g ∈ Aγ → ∀ v ∈ I, (g : V ≃ₗ[ZMod 2] V) v ∈ I :=
    fun g hg v hv => hEI _ ⟨g, hAE hg, rfl⟩ v hv
  have hinv : ∀ g : V ≃ₗ[ZMod 2] V, ∀ v, g⁻¹ (g v) = v := fun g v => by
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]
    rfl
  have hinv' : ∀ g : V ≃ₗ[ZMod 2] V, ∀ v, g (g⁻¹ v) = v := fun g v => by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  set xx : ↥Γ := ⟨x, hxΓ⟩ with hxx
  set tt : ↥Γ := ⟨t, htΓ⟩ with htt
  have hxA : xx ∉ Aγ := fun h => hxv0 (hAI xx h v0 hv0I)
  have hIJ : I ⊓ J = ⊥ := hcompl.inf_eq_bot
  have hsup : I ⊔ J = ⊤ := hcompl.sup_eq_top
  have hrange_le : ∀ P : Submodule (ZMod 2) V,
      P.map (t.toLinearMap - LinearMap.id) ≤ LinearMap.range (t.toLinearMap - LinearMap.id) :=
    fun P => LinearMap.map_le_range
  by_cases htA : tt ∈ Aγ
  ·
    have hconj : ∀ g : ↥Γ, g ∈ Aγ → xx⁻¹ * g * xx ∈ Aγ := fun g hg => by
      have := hAn.conj_mem g hg xx⁻¹
      rwa [inv_inv] at this
    have hfaith : ∀ g : ↥Γ, g ∈ Aγ → (∀ v ∈ I, (g : V ≃ₗ[ZMod 2] V) v = v) → g = 1 := by
      let K : Subgroup ↥Aγ :=
        { carrier := {g | ∀ v ∈ I, (((g : ↥Γ) : V ≃ₗ[ZMod 2] V)) v = v}
          one_mem' := fun _ _ => rfl
          mul_mem' := fun {a b} ha hb v hv => by
            show ((a : ↥Γ) : V ≃ₗ[ZMod 2] V) (((b : ↥Γ) : V ≃ₗ[ZMod 2] V) v) = v
            rw [hb v hv, ha v hv]
          inv_mem' := fun {a} ha v hv => by
            show (((a : ↥Γ) : V ≃ₗ[ZMod 2] V))⁻¹ v = v
            conv_lhs => rw [← ha v hv]
            exact hinv _ v }
      have hKn : K.Normal := by
        constructor
        intro a ha c v hv
        show ((c : ↥Γ) : V ≃ₗ[ZMod 2] V) (((a : ↥Γ) : V ≃ₗ[ZMod 2] V)
          ((((c : ↥Γ) : V ≃ₗ[ZMod 2] V))⁻¹ v)) = v
        have hcv : (((c : ↥Γ) : V ≃ₗ[ZMod 2] V))⁻¹ v ∈ I :=
          hAI ((c : ↥Γ)⁻¹) (Aγ.inv_mem c.2) v hv
        rw [ha _ hcv, hinv']
      intro g hg hgI
      haveI := hKn
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with hK | hK
      · have : (⟨g, hg⟩ : ↥Aγ) ∈ K := hgI
        rw [hK, Subgroup.mem_bot] at this
        exact congrArg Subtype.val this
      ·
        have hall : ∀ a : ↥Γ, a ∈ Aγ → ∀ v ∈ I, (a : V ≃ₗ[ZMod 2] V) v = v := fun a ha =>
          (hK.symm ▸ Subgroup.mem_top (⟨a, ha⟩ : ↥Aγ) : (⟨a, ha⟩ : ↥Aγ) ∈ K)
        have hgJ : ∀ v ∈ I, (g : V ≃ₗ[ZMod 2] V) (x v) = x v := fun v hv => by
          have h1 := hall _ (hconj g hg) v hv
          have h2 : (g : V ≃ₗ[ZMod 2] V) (x v) = x ((x⁻¹ * (g : V ≃ₗ[ZMod 2] V) * x) v) := by
            rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hinv']
          rw [h2]
          exact congrArg x h1
        apply Subtype.ext
        refine LinearEquiv.ext fun w => ?_
        have hw : w ∈ I ⊔ J := hsup ▸ Submodule.mem_top
        obtain ⟨i, hi, j, hj, rfl⟩ := Submodule.mem_sup.mp hw
        obtain ⟨u, hu, rfl⟩ := hj
        rw [map_add, hgI i hi]
        exact congrArg (i + ·) (hgJ u hu)
    have ht'A : xx⁻¹ * tt * xx ∈ Aγ := hconj tt htA
    obtain ⟨t', ht'⟩ : ∃ t' : V ≃ₗ[ZMod 2] V, t' = ((xx⁻¹ * tt * xx : ↥Γ) : V ≃ₗ[ZMod 2] V) :=
      ⟨_, rfl⟩
    have htI : ∀ v ∈ I, t v ∈ I := hAI tt htA
    have ht'I : ∀ v ∈ I, t' v ∈ I := ht' ▸ hAI _ ht'A
    have htx : ∀ v, t (x v) = x (t' v) := fun v => by
      rw [ht', Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply,
        LinearEquiv.mul_apply]
      show t (x v) = x (x⁻¹ (t (x v)))
      rw [hinv']
    have hJmap : J.map (t.toLinearMap - LinearMap.id) =
        (I.map (t'.toLinearMap - LinearMap.id)).map (x : V →ₗ[ZMod 2] V) := by
      ext w
      simp only [hJ, Submodule.mem_map, sub_apply_eq]
      constructor
      · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
        exact ⟨t' u - u, ⟨u, hu, rfl⟩, by simp [htx, map_sub]⟩
      · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
        exact ⟨x u, ⟨u, hu, rfl⟩, by simp [htx, map_sub]⟩
    have hr2 : finrank (ZMod 2) (J.map (t.toLinearMap - LinearMap.id)) =
        finrank (ZMod 2) (I.map (t'.toLinearMap - LinearMap.id)) := by
      rw [hJmap]
      exact LinearEquiv.finrank_map_eq x _
    have hPI : I.map (t.toLinearMap - LinearMap.id) ≤ I := map_sub_le htI
    have hPJ : J.map (t.toLinearMap - LinearMap.id) ≤ J := by
      rw [hJmap]
      exact Submodule.map_mono (map_sub_le ht'I)
    have hsum : finrank (ZMod 2) (I.map (t.toLinearMap - LinearMap.id)) +
        finrank (ZMod 2) (J.map (t.toLinearMap - LinearMap.id)) ≤ 2 := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq (I.map (t.toLinearMap - LinearMap.id))
        (J.map (t.toLinearMap - LinearMap.id))
      have hinf : I.map (t.toLinearMap - LinearMap.id) ⊓ J.map (t.toLinearMap - LinearMap.id) = ⊥ :=
        eq_bot_iff.mpr ((inf_le_inf hPI hPJ).trans hIJ.le)
      rw [hinf, finrank_bot, add_zero] at h
      rw [← h]
      exact (Submodule.finrank_mono (sup_le (hrange_le I) (hrange_le J))).trans hr.le
    have ht1 : tt ≠ 1 := fun h => by
      have : t = 1 := congrArg Subtype.val h
      rw [this] at hr
      have h0 : ((1 : V ≃ₗ[ZMod 2] V).toLinearMap - LinearMap.id : V →ₗ[ZMod 2] V) = 0 := by
        ext v; simp
      rw [h0, LinearMap.range_zero, finrank_bot] at hr
      exact absurd hr (by norm_num)
    have hpos : ∀ g : ↥Γ, g ∈ Aγ → g ≠ 1 →
        1 ≤ finrank (ZMod 2) (I.map ((g : V ≃ₗ[ZMod 2] V).toLinearMap - LinearMap.id)) := by
      intro g hg hg1
      by_contra h0
      push Not at h0
      have hb : I.map ((g : V ≃ₗ[ZMod 2] V).toLinearMap - LinearMap.id) = ⊥ :=
        Submodule.finrank_eq_zero.mp (by omega)
      apply hg1
      refine hfaith g hg fun v hv => ?_
      have : (g : V ≃ₗ[ZMod 2] V) v - v ∈
          I.map ((g : V ≃ₗ[ZMod 2] V).toLinearMap - LinearMap.id) := ⟨v, hv, rfl⟩
      rw [hb, Submodule.mem_bot, sub_eq_zero] at this
      exact this
    have ht'1 : xx⁻¹ * tt * xx ≠ 1 := fun h => ht1 (by
      have := congrArg (fun g => xx * g * xx⁻¹) h
      simpa [mul_assoc] using this)
    have hr1 : 1 ≤ finrank (ZMod 2) (I.map (t.toLinearMap - LinearMap.id)) := hpos tt htA ht1
    have hr2' : 1 ≤ finrank (ZMod 2) (I.map (t'.toLinearMap - LinearMap.id)) :=
      ht' ▸ hpos _ ht'A ht'1
    have hr1eq : finrank (ZMod 2) (I.map (t.toLinearMap - LinearMap.id)) = 1 := by
      have : finrank (ZMod 2) (I.map (t'.toLinearMap - LinearMap.id)) ≥ 1 := hr2'
      omega
    have htt2 : tt * tt = 1 := by
      refine hfaith _ (Aγ.mul_mem htA htA) fun v hv => ?_
      show t (t v) = v
      exact fix_sq_of_finrank_one htI hr1eq v hv
    have hσA : φ tt ∈ alternatingGroup (Fin 7) := (hmemA tt).mp htA
    have hσ2 : φ tt * φ tt = 1 := by rw [← map_mul, htt2, map_one]
    have hσ1 : φ tt ≠ 1 := fun h => ht1 (φ.injective (h.trans (map_one φ).symm))
    obtain ⟨c', hc'A, hc'⟩ := exists_conj_orderOf_five hσA hσ2 hσ1
    set cc : ↥Γ := φ.symm c' with hcc
    have hccA : cc ∈ Aγ := by
      rw [hmemA, hcc, MulEquiv.apply_symm_apply]
      exact (Perm.mem_alternatingGroup).mp hc'A
    set bb : ↥Γ := cc * tt * cc⁻¹ with hbb
    have hbbA : bb ∈ Aγ := Aγ.mul_mem (Aγ.mul_mem hccA htA) (Aγ.inv_mem hccA)
    have hord : orderOf (tt * bb) = 5 := by
      rw [← MulEquiv.orderOf_eq φ, map_mul, hbb, map_mul, map_mul, map_inv, hcc,
        MulEquiv.apply_symm_apply]
      exact hc'
    have hbI : ∀ v ∈ I, (bb : V ≃ₗ[ZMod 2] V) v ∈ I := hAI bb hbbA
    obtain ⟨c, hc⟩ : ∃ c : V ≃ₗ[ZMod 2] V, c = (cc : V ≃ₗ[ZMod 2] V) := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b : V ≃ₗ[ZMod 2] V, b = (bb : V ≃ₗ[ZMod 2] V) := ⟨_, rfl⟩
    have hcI : ∀ v ∈ I, c v ∈ I := hc ▸ hAI cc hccA
    have hciI : ∀ v ∈ I, c⁻¹ v ∈ I := by
      have h := hAI cc⁻¹ (Aγ.inv_mem hccA)
      rw [Subgroup.coe_inv, ← hc] at h
      exact h
    have hbapp : ∀ v, b v = c (t (c⁻¹ v)) := fun v => by
      rw [hb, hbb, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hc,
        LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    have hbmap : I.map (b.toLinearMap - LinearMap.id) =
        (I.map (t.toLinearMap - LinearMap.id)).map (c : V →ₗ[ZMod 2] V) := by
      ext w
      simp only [Submodule.mem_map, sub_apply_eq, LinearEquiv.coe_coe]
      constructor
      · rintro ⟨u, hu, rfl⟩
        refine ⟨t (c⁻¹ u) - c⁻¹ u, ⟨_, hciI u hu, rfl⟩, ?_⟩
        rw [map_sub, hinv' c u, hbapp]
      · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
        refine ⟨c u, hcI u hu, ?_⟩
        rw [hbapp, hinv c u, map_sub]
    have hbI' : ∀ v ∈ I, b v ∈ I := hb ▸ hbI
    have hbr : finrank (ZMod 2) (I.map (b.toLinearMap - LinearMap.id)) = 1 := by
      rw [hbmap, LinearEquiv.finrank_map_eq, hr1eq]
    have h5 : (t * b) ^ 5 = 1 := by
      have := pow_orderOf_eq_one (tt * bb)
      rw [hord] at this
      have h' := congrArg Subtype.val this
      rw [Subgroup.coe_pow, Subgroup.coe_mul, ← hb] at h'
      exact h'
    have hfix := fix_of_order_five hI4 htI hbI' hr1eq hbr h5
    have h1 : tt * bb = 1 := by
      refine hfaith _ (Aγ.mul_mem htA hbbA) fun v hv => ?_
      rw [Subgroup.coe_mul, ← hb]
      exact hfix v hv
    rw [h1, orderOf_one] at hord
    exact absurd hord (by norm_num)
  ·
    have hsgn : ∀ g : ↥Γ, g ∉ Aγ → Perm.sign (φ g) = -1 := fun g hg =>
      (Int.units_eq_one_or _).resolve_left fun h => hg ((hmemA g).mpr h)
    have haA : xx⁻¹ * tt ∈ Aγ := by
      rw [hmemA, map_mul, map_inv, map_mul, map_inv, hsgn xx hxA, hsgn tt htA]
      rfl
    have htJ : ∀ v ∈ I, t v ∈ J := fun v hv => by
      have h1 := hAI _ haA v hv
      refine ⟨_, h1, ?_⟩
      show x ((x⁻¹ * t) v) = t v
      rw [LinearEquiv.mul_apply, hinv']
    have hinj : Function.Injective ((t.toLinearMap - LinearMap.id).domRestrict I) := by
      intro u w huw
      have h1 : t ((u : V) - w) = (u : V) - w := by
        have := huw
        simp only [LinearMap.domRestrict_apply, sub_apply_eq] at this
        rw [map_sub]
        rw [sub_eq_sub_iff_sub_eq_sub] at this
        exact this
      have hmem : (u : V) - w ∈ I ⊓ J :=
        ⟨I.sub_mem u.2 w.2, h1 ▸ htJ _ (I.sub_mem u.2 w.2)⟩
      rw [hIJ, Submodule.mem_bot, sub_eq_zero] at hmem
      exact Subtype.ext hmem
    have h4 := LinearMap.finrank_range_of_inj hinj
    rw [LinearMap.range_domRestrict, hI4] at h4
    have := Submodule.finrank_mono (hrange_le I)
    omega

theorem g112ConclA2_concl8 (B : LinearMap.BilinForm (ZMod 2) V)
    (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) (v₁ : V) (W : Submodule (ZMod 2) V)
    (X X₀ : Subgroup (V ≃ₗ[ZMod 2] V)) (hH : G111Hyp B Γ v₁ W X X₀) (h8 : G112Concl8 B Γ X) :
    ∀ t ∈ X, Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 2 →
      v₁ ∈ LinearMap.range (t.toLinearMap - LinearMap.id) → (∀ v, B v (t v) = 0) →
      ∃ γ ∈ Γ, (∀ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id),
        γ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id)) ∧ γ v₁ ≠ v₁ := by
  intro t ht hr _ _
  exact absurd hr (finrank_ne_two_of_concl8 hH.X_le h8 (hH.X_le ht))

end Main

end CFSG.Quasithin.G112A2
