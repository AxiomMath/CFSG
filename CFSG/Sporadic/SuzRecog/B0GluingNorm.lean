module

public import CFSG.Sporadic.SuzRecog.B0GluingCert
public import CFSG.Sporadic.SuzRecog.C1ModelCent
public import CFSG.Sporadic.SuzRecog.LocalR

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog.B0Gluing

open Subgroup CFSG.Open CFSG.ComponentClassification.AS81.SuzB0 CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
  CFSG.Sporadic.SuzRecog.LocalR

section RhoA


theorem A40_le_invE : A40 ≤ invE 1 := fun _ hx => CT0_le_invE (mem_inf.mp (A40_le hx)).2

theorem A40_le_normalizer_R0 :
    A40 ≤ normalizer (Model.R0 : Set (Equiv.Perm (Fin 1782))) := by
  rw [A40_eq, closure_le]
  rintro g (rfl | rfl)
  · exact mem_normalizer_R0 (by rw [mul_inv_cancel_right]; exact w0_mem_R0)
      (by rw [R0_comm w0_mem_R0 r1_mem_R0, mul_inv_cancel_right]; exact r1_mem_R0)
  · exact rho1_mem_B0.2

theorem rhoA_spec {c : Equiv.Perm (Fin 1782)} (hc : c ∈ CT0) (h3 : c * (c * c) = 1) (h1 : c ≠ 1)
    (hu1 : c * Model.w0 * (c * c) * Model.w0 = Model.w0 * (c * Model.w0 * (c * c)))
    (hu2 : c * Model.w0 * (c * c) ≠ Model.w0)
    (hu3 : c * (c * Model.w0 * (c * c)) * (c * c) = Model.w0 * (c * Model.w0 * (c * c))) :
    c ∈ A40 := by
  obtain ⟨k, hk, hrep⟩ := enumerates_CT0.exists_pos hc
  have h := b0RhoA_check
  unfold rhoACheck at h
  rw [Array.all_eq_true] at h
  have hk' := h k hk
  rw [← getElem!_pos ct0Tabs k hk] at hk'
  set t := ct0Tabs[k]!
  have hc2 : TabRep (comp 1782 t t) (c * c) := hrep.comp hrep
  have hu : TabRep (conjTab 1782 t (comp 1782 t t) w0T) (c * Model.w0 * (c * c)) :=
    (hrep.comp tabRep_w0).comp hc2
  have e1 : (comp 1782 t (comp 1782 t t) == idTab 1782) = true :=
    ((hrep.comp hc2).beq_iff TabRep.idTab).mpr h3
  have e2 : (t == idTab 1782) = false := by
    rw [Bool.eq_false_iff]
    intro he
    exact h1 ((hrep.beq_iff TabRep.idTab).mp he)
  have e3 : (comp 1782 (conjTab 1782 t (comp 1782 t t) w0T) w0T ==
      comp 1782 w0T (conjTab 1782 t (comp 1782 t t) w0T)) = true :=
    ((hu.comp tabRep_w0).beq_iff (tabRep_w0.comp hu)).mpr hu1
  have e4 : (conjTab 1782 t (comp 1782 t t) w0T == w0T) = false := by
    rw [Bool.eq_false_iff]
    intro he
    exact hu2 ((hu.beq_iff tabRep_w0).mp he)
  have e5 : (conjTab 1782 t (comp 1782 t t) (conjTab 1782 t (comp 1782 t t) w0T) ==
      comp 1782 w0T (conjTab 1782 t (comp 1782 t t) w0T)) = true :=
    (((hrep.comp hu).comp hc2).beq_iff (tabRep_w0.comp hu)).mpr hu3
  simp only [e1, e2, e3, e4, e5, Bool.not_false, Bool.and_true, Bool.not_true, Bool.false_or]
    at hk'
  obtain ⟨g, hg, hgr⟩ := enumerates_closure_A4.sound _ (mem_of_found hk')
  rw [A40_eq, hrep.perm_eq hgr]
  exact hg

end RhoA

section Normal


variable {G : Type} [Group G] [Finite G] {z : G}

theorem exists_sigma_normal {σ₀ : ↥(centralizer ({z} : Set G)) ≃* ↥(invE 1)} {A R : Subgroup G}
    (L : SuzLocalR z σ₀ w0E (T0.subgroupOf (invE 1)) A R) :
    ∃ σ : ↥(centralizer ({z} : Set G)) ≃* ↥(invE 1),
      (∀ y (hy : y ∈ T0), ((σ.symm ⟨y, T0_le_invE hy⟩ : ↥(centralizer ({z} : Set G))) : G) ∈ A) ∧
      (∀ y (hy : y ∈ A40), ((σ.symm ⟨y, A40_le_invE hy⟩ : ↥(centralizer ({z} : Set G))) : G) ∈
        centralizer (A : Set G)) ∧
      ∀ x (hx : x ∈ centralizer ({z} : Set G)),
        ((σ ⟨x, hx⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈ Model.R0 ↔ x ∈ R := by
  set M := centralizer ({z} : Set G)
  have hc := L.comp
  obtain ⟨r, hr, hr1⟩ := hc.exists_ne_one
  obtain ⟨σ, hσr, -, -, hT, -⟩ := L.tau r hr hr1
  obtain ⟨ρ, hρ, hρ3, hρR, hCA, h12⟩ := L.rho
  obtain ⟨hρA, hρz⟩ := mem_inf.mp hρ
  have hRM : ∀ x ∈ R, x ∈ M := fun x hx => hc.R_le_M hx
  have hAM : ∀ x ∈ centralizer (A : Set G), x ∈ M := fun x hx =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hx z hc.z_mem).symm
  have hTA : ∀ y (hy : y ∈ T0), ((σ.symm ⟨y, T0_le_invE hy⟩ : M) : G) ∈ A := fun y hy => by
    have : (⟨y, T0_le_invE hy⟩ : ↥(invE 1)) ∈ trS σ (A ⊓ M) := by
      rw [hT]
      exact mem_subgroupOf.mpr hy
    exact (mem_inf.mp (mem_trS_iff.mp this)).1
  have hCT0 : ∀ x (hx : x ∈ centralizer (A : Set G)),
      ((σ ⟨x, hAM x hx⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈ CT0 := fun x hx => by
    refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun t ht => ?_, (σ ⟨x, hAM x hx⟩).2⟩
    have hm := hTA t ht
    have e : σ.symm ⟨t, T0_le_invE ht⟩ * ⟨x, hAM x hx⟩ =
        ⟨x, hAM x hx⟩ * σ.symm ⟨t, T0_le_invE ht⟩ :=
      Subtype.ext (mem_centralizer_iff.mp hx _ hm)
    have := congrArg (fun m => ((σ m : ↥(invE 1)) : Equiv.Perm (Fin 1782))) e
    simpa only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul] using this
  have hmove : ∀ s ∈ R, s ≠ 1 → ρ * s * ρ⁻¹ ≠ s := fun s hs hs1 hfix => by
    have hP : IsPGroup 2 (centralizer ({s} : Set G) ⊓ M : Subgroup G) :=
      IsPGroup.of_card (n := 9) (by rw [(L.sylow s hs hs1).2]; norm_num)
    have hmem : ρ ∈ centralizer ({s} : Set G) ⊓ M :=
      ⟨mem_centralizer_singleton_iff.2 (by
        calc ρ * s = ρ * s * ρ⁻¹ * ρ := by group
          _ = s * ρ := by rw [hfix]), hρz⟩
    obtain ⟨k, hk⟩ := hP ⟨ρ, hmem⟩
    have hdvd : orderOf ρ ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      have := congrArg Subtype.val hk
      simpa using this
    rw [hρ3] at hdvd
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) hdvd
    omega
  have hρ1 : ρ ^ 3 = 1 := by rw [← hρ3]; exact pow_orderOf_eq_one ρ
  have hρn : ∀ x ∈ R, ρ * x * ρ⁻¹ ∈ R := fun x hx => (mem_normalizer_iff.mp hρR x).mp hx
  obtain ⟨s, hsdef⟩ : ∃ s, s = ρ * r * ρ⁻¹ := ⟨_, rfl⟩
  have hs : s ∈ R := hsdef ▸ hρn r hr
  have hs1 : s ≠ 1 := fun e => hr1 (by
    calc r = ρ⁻¹ * (ρ * r * ρ⁻¹) * ρ := by group
      _ = 1 := by rw [← hsdef, e]; group)
  have hsr : s ≠ r := hsdef ▸ hmove r hr hr1
  have hrr : r * r = 1 := by rw [← sq]; exact hc.elem.2 r hr
  have hcyc : ρ * s * ρ⁻¹ = r * s := by
    have ht : ρ * s * ρ⁻¹ ∈ R := hρn s hs
    rcases mem_four hc.card hr hs hr1 hs1 hsr hrr ht with h | h | h | h
    · exfalso
      exact hs1 (by
        calc s = ρ⁻¹ * (ρ * s * ρ⁻¹) * ρ := by group
          _ = 1 := by rw [h]; group)
    · exfalso
      apply hsr
      calc s = ρ * r * ρ⁻¹ := hsdef
        _ = ρ * (ρ * s * ρ⁻¹) * ρ⁻¹ := by rw [h]
        _ = ρ * (ρ * (ρ * r * ρ⁻¹) * ρ⁻¹) * ρ⁻¹ := by rw [hsdef]
        _ = ρ * (ρ * ρ) * r * (ρ * (ρ * ρ))⁻¹ := by group
        _ = r := by rw [← pow_three, hρ1]; group
    · exact absurd h (hmove s hs hs1)
    · exact h
  set cE := σ ⟨ρ, hρz⟩ with hcE
  set c : Equiv.Perm (Fin 1782) := (cE : Equiv.Perm (Fin 1782))
  have hσw : ((σ ⟨r, hRM r hr⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) = Model.w0 := by
    have := hc.R_le_M hr
    rw [show (⟨r, hRM r hr⟩ : M) = ⟨r, hc.R_le_M hr⟩ from rfl, hσr]
    rfl
  have hσmul : ∀ a b (ha : a ∈ M) (hb : b ∈ M) (hab : a * b ∈ M),
      ((σ ⟨a * b, hab⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) =
        (σ ⟨a, ha⟩ : Equiv.Perm (Fin 1782)) * (σ ⟨b, hb⟩ : Equiv.Perm (Fin 1782)) := by
    intro a b ha hb hab
    rw [show (⟨a * b, hab⟩ : M) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl, map_mul, Subgroup.coe_mul]
  have hσinv : ∀ a (ha : a ∈ M) (hai : a⁻¹ ∈ M),
      ((σ ⟨a⁻¹, hai⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) =
        (σ ⟨a, ha⟩ : Equiv.Perm (Fin 1782))⁻¹ := by
    intro a ha hai
    rw [show (⟨a⁻¹, hai⟩ : M) = (⟨a, ha⟩ : M)⁻¹ from rfl, map_inv, Subgroup.coe_inv]
  have hρi : ρ⁻¹ ∈ M := inv_mem hρz
  have hconj : ∀ x (hx : x ∈ M), ((σ ⟨ρ * x * ρ⁻¹, mul_mem (mul_mem hρz hx) hρi⟩ : ↥(invE 1)) :
      Equiv.Perm (Fin 1782)) = c * (σ ⟨x, hx⟩ : Equiv.Perm (Fin 1782)) * c⁻¹ := by
    intro x hx
    rw [hσmul _ _ (mul_mem hρz hx) hρi, hσmul _ _ hρz hx, hσinv _ hρz hρi]
  have hc3 : c * (c * c) = 1 := by
    have e : ρ * (ρ * ρ) = 1 := by rw [← pow_three, hρ1]
    have := hσmul ρ (ρ * ρ) hρz (mul_mem hρz hρz) (mul_mem hρz (mul_mem hρz hρz))
    rw [hσmul ρ ρ hρz hρz] at this
    rw [← this]
    simp only [e]
    rw [show (⟨1, one_mem M⟩ : M) = 1 from rfl, map_one, Subgroup.coe_one]
  have hcc : c * c = c⁻¹ := (eq_inv_of_mul_eq_one_right hc3)
  have hc1 : c ≠ 1 := fun h => by
    have : cE = 1 := Subtype.ext h
    rw [hcE, MulEquiv.map_eq_one_iff] at this
    have hρ1' : ρ = 1 := congrArg Subtype.val this
    rw [hρ1', orderOf_one] at hρ3
    norm_num at hρ3
  have hsM : s ∈ M := hRM s hs
  have hu : c * Model.w0 * (c * c) = (σ ⟨s, hsM⟩ : Equiv.Perm (Fin 1782)) := by
    rw [hcc, ← hσw, ← hconj r (hRM r hr)]
    exact congrArg Subtype.val (congrArg σ (Subtype.ext hsdef.symm))
  have hcA : c ∈ A40 := by
    refine rhoA_spec (hCT0 ρ hρA) hc3 hc1 ?_ ?_ ?_
    · rw [hu, ← hσw, ← hσmul _ _ hsM (hRM r hr) (mul_mem hsM (hRM r hr)),
        ← hσmul _ _ (hRM r hr) hsM (mul_mem (hRM r hr) hsM)]
      congr 1
      exact congrArg _ (Subtype.ext (hc.comm hs hr))
    · rw [hu, ← hσw]
      intro h
      have := congrArg Subtype.val (σ.injective (Subtype.ext h))
      exact hsr this
    · rw [hu, hcc, ← hconj s hsM, ← hσw, ← hσmul _ _ (hRM r hr) hsM (mul_mem (hRM r hr) hsM)]
      exact congrArg _ (congrArg _ (Subtype.ext hcyc))
  have hcN := A40_le_normalizer_R0 hcA
  have huR0 : (σ ⟨s, hsM⟩ : Equiv.Perm (Fin 1782)) ∈ Model.R0 := by
    rw [← hu, hcc]
    exact (mem_normalizer_iff.mp hcN _).mp w0_mem_R0
  have hσR : ∀ x (hx : x ∈ R),
      ((σ ⟨x, hRM x hx⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈ Model.R0 := by
    intro x hx
    rcases mem_four hc.card hr hs hr1 hs1 hsr hrr hx with rfl | rfl | rfl | rfl
    · rw [show (⟨1, hRM 1 hx⟩ : M) = 1 from rfl, map_one, Subgroup.coe_one]
      exact one_mem _
    · rw [hσw]
      exact w0_mem_R0
    · exact huR0
    · rw [hσmul _ _ (hRM r hr) hsM, hσw]
      exact mul_mem w0_mem_R0 huR0
  let K : Subgroup G := (((A40.subgroupOf (invE 1)).comap σ.toMonoidHom).map M.subtype)
  have hmemK : ∀ x (hx : x ∈ M), ((σ ⟨x, hx⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈ A40 →
      x ∈ K := fun x hx h => ⟨⟨x, hx⟩, mem_subgroupOf.mpr h, rfl⟩
  have hCAK : centralizer (A : Set G) ≤ K := by
    rw [hCA]
    refine sup_le (fun x hx => hmemK x (hRM x hx) (R0_le_A40 (hσR x hx))) ?_
    rw [zpowers_le]
    exact hmemK ρ hρz hcA
  have hσCA : ∀ x (hx : x ∈ centralizer (A : Set G)),
      ((σ ⟨x, hAM x hx⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈ A40 := fun x hx => by
    obtain ⟨m, hm, hmx⟩ := hCAK hx
    have e : m = ⟨x, hAM x hx⟩ := Subtype.ext hmx
    rw [← e]
    exact mem_subgroupOf.mp hm
  refine ⟨σ, hTA, fun y hy => ?_, fun x hx => ⟨fun h => ?_, fun h => hσR x h⟩⟩
  ·
    let f : ↥(centralizer (A : Set G)) → ↥A40 := fun x => ⟨_, hσCA x x.2⟩
    have hf : Function.Injective f := fun x x' hxx' => by
      have h1 : ((f x : ↥A40) : Equiv.Perm (Fin 1782)) = f x' := congrArg Subtype.val hxx'
      have e : (⟨x, hAM x x.2⟩ : M) = ⟨x', hAM x' x'.2⟩ := σ.injective (Subtype.ext h1)
      exact Subtype.ext (show (x : G) = x' from congrArg (fun m : M => (m : G)) e)
    have hbij := hf.bijective_of_nat_card_le (by rw [h12, card_A40])
    obtain ⟨x, hx⟩ := hbij.2 ⟨y, hy⟩
    have hx' : ((f x : ↥A40) : Equiv.Perm (Fin 1782)) = y := congrArg Subtype.val hx
    have e : σ ⟨x, hAM x x.2⟩ = ⟨y, A40_le_invE hy⟩ := Subtype.ext hx'
    rw [← e, MulEquiv.symm_apply_apply]
    exact x.2
  ·
    let f : ↥R → ↥Model.R0 := fun x => ⟨_, hσR x x.2⟩
    have hf : Function.Injective f := fun x x' hxx' => by
      have h1 : ((f x : ↥Model.R0) : Equiv.Perm (Fin 1782)) = f x' := congrArg Subtype.val hxx'
      have e : (⟨x, hRM x x.2⟩ : M) = ⟨x', hRM x' x'.2⟩ := σ.injective (Subtype.ext h1)
      exact Subtype.ext (show (x : G) = x' from congrArg (fun m : M => (m : G)) e)
    have hbij := hf.bijective_of_nat_card_le (by rw [hc.card, card_R0])
    obtain ⟨y, hy⟩ := hbij.2 ⟨_, h⟩
    have hy' : ((f y : ↥Model.R0) : Equiv.Perm (Fin 1782)) = σ ⟨x, hx⟩ := congrArg Subtype.val hy
    have e : σ ⟨y, hRM y y.2⟩ = σ ⟨x, hx⟩ := Subtype.ext hy'
    have e2 : (y : G) = x := congrArg Subtype.val (σ.injective e)
    rw [← e2]
    exact y.2

end Normal

end CFSG.Sporadic.SuzRecog.B0Gluing
