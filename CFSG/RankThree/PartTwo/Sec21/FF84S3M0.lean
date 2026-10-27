module

public import CFSG.RankThree.PartTwo.Sec21.FF84S3P
public import CFSG.RankThree.PartTwo.Sec21.FF84S3A2
public import CFSG.RankThree.PartTwo.Sec21.FF84S3T0
public import CFSG.RankThree.GF2n.Tim81.Sec4.ListBridges

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open Equiv Equiv.Perm Subgroup

section Model
variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ : G}

@[expose] noncomputable def M0_quotIso (hZ : Subgroup.center L = ⊥) :
    ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
  (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot

theorem M0_quotIso_mk (hZ : Subgroup.center L = ⊥) (x : ↥L) :
    M0_quotIso hZ (QuotientGroup.mk x) = x := by
  simp only [M0_quotIso, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem M0_quotIso_symm_apply (hZ : Subgroup.center L = ⊥) (x : ↥L) :
    (M0_quotIso hZ).symm x = QuotientGroup.mk x := by
  rw [MulEquiv.symm_apply_eq, M0_quotIso_mk]

@[expose] noncomputable def M0_toL (hZ : Subgroup.center L = ⊥)
    (e' : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 8)) :
    ↥L ≃* alternatingGroup (Fin 8) :=
  (M0_quotIso hZ).symm.trans e'

theorem M0_toL_apply (hZ : Subgroup.center L = ⊥)
    (e' : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 8)) (x : ↥L) :
    M0_toL hZ e' x = e' (QuotientGroup.mk x) := by
  simp [M0_toL, M0_quotIso_symm_apply]

theorem M0_conjNormal_val (σ : Equiv.Perm (Fin 8)) (h : alternatingGroup (Fin 8)) :
    ((MulAut.conjNormal σ h : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) =
      σ * (h : Equiv.Perm (Fin 8)) * σ⁻¹ := by
  simp [MulAut.conjNormal_apply]

theorem M0_orderOf3 (f : ↥L ≃* alternatingGroup (Fin 8)) {y : ↥L} (h3 : y ^ 3 = 1) (h1 : y ≠ 1) :
    orderOf ((f y : alternatingGroup (Fin 8)) : P8) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply orderOf_eq_prime
  · have h' : (f y) ^ 3 = 1 := by rw [← map_pow, h3, map_one]
    have h'' := congrArg Subtype.val h'
    simpa using h''
  · intro h
    apply h1
    apply f.injective
    apply Subtype.ext
    simpa using h

theorem M0_card_cen (f : ↥L ≃* alternatingGroup (Fin 8)) (y : ↥L) :
    Nat.card ↥(Subgroup.centralizer ({((f y : alternatingGroup (Fin 8)) : P8)} : Set P8) ⊓ A8s) =
      Nat.card ↥(L ⊓ Cen (y : G)) := by
  have hψi : Function.Injective ((alternatingGroup (Fin 8)).subtype.comp f.toMonoidHom) :=
    Subtype.val_injective.comp f.injective
  have key : (((L ⊓ Cen (y : G)).subgroupOf L).map
      ((alternatingGroup (Fin 8)).subtype.comp f.toMonoidHom)) =
      Subgroup.centralizer ({((f y : alternatingGroup (Fin 8)) : P8)} : Set P8) ⊓ A8s := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hwy : (w : G) ∈ Cen (y : G) := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hw)).2
      have hwy' : (w : G) * (y : G) = (y : G) * (w : G) := Subgroup.mem_centralizer_singleton_iff.1 hwy
      have hwy'' : w * y = y * w := Subtype.ext hwy'
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, (f w).2⟩
      have h' := congrArg (fun t => ((f t : alternatingGroup (Fin 8)) : P8)) hwy''
      simpa [map_mul] using h'
    · rintro ⟨hz2, hz1⟩
      set w : ↥L := f.symm ⟨z, hz1⟩ with hw_def
      have hzw : ((f w : alternatingGroup (Fin 8)) : P8) = z := by
        simp [hw_def]
      refine ⟨w, ?_, hzw⟩
      refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨w.2, ?_⟩)
      have hz2' := Subgroup.mem_centralizer_singleton_iff.1 hz2
      rw [← hzw] at hz2'
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      have h1 : f (w * y) = f (y * w) := by
        apply Subtype.ext
        simp only [map_mul, Subgroup.coe_mul]
        exact hz2'
      have h2 := f.injective h1
      exact congrArg Subtype.val h2
  rw [← key, Subgroup.card_map_of_injective hψi]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

theorem M0_mk_inj (hZ : Subgroup.center L = ⊥) (u v : ↥L) (h : (QuotientGroup.mk u : ↥L ⧸ Subgroup.center ↥L) = QuotientGroup.mk v) : u = v := by
  have h' := QuotientGroup.eq.1 h
  rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at h'
  exact h'

theorem M0_T0_conj (hL : ⁅L, L⁆ = L)
    (e' : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 8)) :
    ∃ θ : ↥(Nor L) →* P8,
      (∀ (g : G) (hg : g ∈ Nor L) (x y : ↥L), (y : G) = g * x * g⁻¹ →
        ((e' (QuotientGroup.mk y) : alternatingGroup (Fin 8)) : P8) =
          θ ⟨g, hg⟩ * ((e' (QuotientGroup.mk x) : alternatingGroup (Fin 8)) : P8) * (θ ⟨g, hg⟩)⁻¹) ∧
      (∀ x : ↥L, θ ⟨(x : G), Subgroup.le_normalizer x.2⟩ =
        ((e' (QuotientGroup.mk x) : alternatingGroup (Fin 8)) : P8)) ∧
      (∀ (g : G) (hg : g ∈ Nor L), θ ⟨g, hg⟩ = 1 ↔ g ∈ CenS L) := by
  obtain ⟨θ, h1, h2, h3⟩ := T0_thetaBar L hL e'
  refine ⟨θ, fun g hg x y hy => ?_, fun x => h2 x, fun g hg => h3 ⟨g, hg⟩⟩
  have hxy : L.normalizerMonoidHom ⟨g, hg⟩ x = y := Subtype.ext (by simp [hy])
  have := h1 ⟨g, hg⟩ x
  rw [hxy] at this
  exact this

theorem M0_quot (h : FF84Sec3 b L B b₁ b₂) (hZ : Subgroup.center L = ⊥) :
    ∃ e' : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 8),
      ∀ x y : ↥L, (x : G) = b₁ → (y : G) = b₂ →
        ((e' (QuotientGroup.mk x) : alternatingGroup (Fin 8)) : P8) = m₁ ∧
        ((e' (QuotientGroup.mk y) : alternatingGroup (Fin 8)) : P8) = m₂ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e₀⟩ :=
    CFSG.RankThree.GF2n.Tim81.nonempty_mulEquiv_alternating_eight_of_psl4_model h.hyp.model
  obtain ⟨e⟩ : Nonempty (↥L ≃* alternatingGroup (Fin 8)) := ⟨M0_toL hZ e₀⟩
  have hb₁L : b₁ ∈ L := (Subgroup.mem_inf.1 h.hb₁).2
  have hb₂L : b₂ ∈ L := (Subgroup.mem_inf.1 h.hb₂).2
  obtain ⟨y₁, hy₁⟩ : ∃ y : ↥L, (y : G) = b₁ := ⟨⟨b₁, hb₁L⟩, rfl⟩
  obtain ⟨y₂, hy₂⟩ : ∃ y : ↥L, (y : G) = b₂ := ⟨⟨b₂, hb₂L⟩, rfl⟩
  obtain ⟨h13, h23, hcomm, hne1, hne2, hind, -⟩ :=
    mono_facts h.hyp.ord (mem_B_b₁ h) (mem_B_b₂ h) h.mono
  have hy₁3 : y₁ ^ 3 = 1 := Subtype.ext (by simpa [hy₁] using h13)
  have hy₂3 : y₂ ^ 3 = 1 := Subtype.ext (by simpa [hy₂] using h23)
  have hy₁1 : y₁ ≠ 1 := fun h' => hne1 (by simpa [hy₁] using congrArg Subtype.val h')
  have hy₂1 : y₂ ≠ 1 := fun h' => hne2 (by simpa [hy₂] using congrArg Subtype.val h')
  have hy_comm : y₁ * y₂ = y₂ * y₁ := Subtype.ext (by simpa [hy₁, hy₂] using hcomm)
  have hy_ind : ∀ k : ℤ, y₂ ≠ y₁ ^ k := fun k h' => hind k (by
    have := congrArg Subtype.val h'
    simpa [hy₁, hy₂] using this)
  have hx₁A : ((e y₁ : alternatingGroup (Fin 8)) : P8) ∈ A8s := (e y₁).2
  have hx₂A : ((e y₂ : alternatingGroup (Fin 8)) : P8) ∈ A8s := (e y₂).2
  have ord₁ := M0_orderOf3 e hy₁3 hy₁1
  have ord₂ := M0_orderOf3 e hy₂3 hy₂1
  have hcomm' : ((e y₁ : alternatingGroup (Fin 8)) : P8) * ((e y₂ : alternatingGroup (Fin 8)) : P8) =
      ((e y₂ : alternatingGroup (Fin 8)) : P8) * ((e y₁ : alternatingGroup (Fin 8)) : P8) := by
    have h' := congrArg (fun t => ((e t : alternatingGroup (Fin 8)) : P8)) hy_comm
    simpa [map_mul] using h'
  have c18 : Nat.card ↥(Subgroup.centralizer ({((e y₁ : alternatingGroup (Fin 8)) : P8)} : Set P8) ⊓
      A8s) = 18 := by
    rw [M0_card_cen e y₁, hy₁]
    have := h.caseA
    rw [hZ, Subgroup.card_bot, mul_one] at this
    exact this
  have hct₁ := (A1_class _ hx₁A ord₁).1 c18
  have hc18₂ : Nat.card ↥(Subgroup.centralizer ({((e y₂ : alternatingGroup (Fin 8)) : P8)} : Set P8) ⊓
      A8s) = 18 := by
    rw [M0_card_cen e y₂, hy₂]
    have hcP := P_caseA₂ h
    rw [hZ, Subgroup.card_bot, mul_one] at hcP
    exact hcP
  have hct₂ := (A1_class _ hx₂A ord₂).1 hc18₂
  have hnot : ((e y₂ : alternatingGroup (Fin 8)) : P8) ∉
      Subgroup.zpowers ((e y₁ : alternatingGroup (Fin 8)) : P8) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    apply hy_ind k
    apply e.injective
    apply Subtype.ext
    rw [map_zpow]
    simpa using hk.symm
  obtain ⟨σ, hσ₁, hσ₂⟩ := A2_normalize _ _ hx₁A hx₂A hcomm' ord₁ ord₂ hct₁ hct₂ hnot
  refine ⟨(M0_quotIso hZ).trans (e.trans (MulAut.conjNormal σ)), ?_⟩
  intro x y hx hy
  have hxy : x = y₁ := Subtype.ext (hx.trans hy₁.symm)
  have hyy : y = y₂ := Subtype.ext (hy.trans hy₂.symm)
  subst hxy
  subst hyy
  have key : ∀ z : ↥L, ((((M0_quotIso hZ).trans (e.trans (MulAut.conjNormal σ)))
      (QuotientGroup.mk z) : alternatingGroup (Fin 8)) : P8) =
      σ * ((e z : alternatingGroup (Fin 8)) : P8) * σ⁻¹ := by
    intro z
    rw [MulEquiv.trans_apply, M0_quotIso_mk, MulEquiv.trans_apply, M0_conjNormal_val]
  constructor
  · rw [key]; exact hσ₁
  · rw [key]; exact hσ₂

theorem M0_model (h : FF84Sec3 b L B b₁ b₂) (hZ : Subgroup.center L = ⊥) :
    ∃ e : ↥L ≃* alternatingGroup (Fin 8), ∀ x y : ↥L, (x : G) = b₁ → (y : G) = b₂ →
      ((e x : alternatingGroup (Fin 8)) : P8) = m₁ ∧ ((e y : alternatingGroup (Fin 8)) : P8) = m₂ := by
  obtain ⟨e', he'⟩ := M0_quot h hZ
  refine ⟨M0_toL hZ e', fun x y hx hy => ?_⟩
  rw [M0_toL_apply, M0_toL_apply]
  exact he' x y hx hy

end Model

end CFSG.RankThree.PartTwo.Sec21.FF84.S3
