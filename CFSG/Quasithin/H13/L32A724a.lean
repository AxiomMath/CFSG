module

public import CFSG.Quasithin.H13.L32A723b

public section

namespace CFSG.Quasithin.H13.S4

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.L32A CFSG.Quasithin.H13.A6 CFSG.Quasithin.H6

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} {γ γ' : F8.Geom T L H}
  {g k : ↥((L ⊔ T) ⊔ H)} {θ : ↥L →* Γ} {c : G}

theorem s_le_q (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) :
    L32A.sL T L V ≤ pCoreOf 2 (L ⊔ T) := by
  have hS := C.setting
  have hF := C.hypF98
  rw [C.eq_hz] at hS hF
  exact sL_le_pCoreOf hS hF D.mod

theorem isPGroup_s (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) :
    IsPGroup 2 ↥(L32A.sL T L V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (pCoreOf_isPGroup 2 _).to_le (s_le_q C D)

theorem t_le_h (C : Ctx722 G T L V H γ γ' g k) : T ≤ H :=
  le_sup_right.trans C.hypF98.toHypF91.L₁T_le_H

theorem s_le_h (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) : L32A.sL T L V ≤ H :=
  (s_le_q C D).trans ((pCoreOf_sup_le C.setting.hyp).trans (t_le_h C))

theorem mem_h_of_mem_normalizer (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) {x : G}
    (hx : x ∈ Subgroup.normalizer (fsuV1 T V : Set G)) : x ∈ H := by
  rw [L32A.normalizer_eq_centralizer_of_card_two D.card_v1] at hx
  rw [C.eq_hz]
  exact hx

omit [Finite G] in
theorem conj_mem_s {l s : G} (hl : l ∈ L) (hs : s ∈ L32A.sL T L V) :
    l * s * l⁻¹ ∈ L32A.sL T L V :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ L hl) s).mp hs

theorem s_inf_l1_le_p (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) :
    L32A.sL T L V ⊓ L32A.l1 T L V ≤ pCoreOf 2 (oTwoUpper H) := by
  rw [← C.o2_l1]
  exact le_pCoreOf_of_le_normalizer inf_le_right
    (F7.le_normalizer_inf (fun x hx => le_normalizer_conjClosure _ L (l1_le_l D hx))
      Subgroup.le_normalizer) ((isPGroup_s C D).to_le inf_le_left)

theorem comm_mem_p_of_mem_l1 (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) {l s : G}
    (hl : l ∈ L32A.l1 T L V) (hs : s ∈ L32A.sL T L V) :
    l * s * l⁻¹ * s⁻¹ ∈ L32A.sL T L V ⊓ pCoreOf 2 (oTwoUpper H) := by
  have hS : l * s * l⁻¹ * s⁻¹ ∈ L32A.sL T L V :=
    mul_mem (conj_mem_s (l1_le_l D hl) hs) (inv_mem hs)
  have hL : l * s * l⁻¹ * s⁻¹ ∈ L32A.l1 T L V := by
    have h1 : s * l⁻¹ * s⁻¹ ∈ L32A.l1 T L V :=
      (Subgroup.mem_normalizer_iff.mp (C.l1_normal (s_le_h C D hs)) _).mp (inv_mem hl)
    have e : l * s * l⁻¹ * s⁻¹ = l * (s * l⁻¹ * s⁻¹) := by group
    rw [e]
    exact mul_mem hl h1
  exact ⟨hS, s_inf_l1_le_p C D ⟨hS, hL⟩⟩

theorem secMod_s (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) :
    SecMod L (L32A.sL T L V) (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) θ := by
  have hVR : V ≤ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L :=
    C.v_le_e.trans (le_conjClosure _ _)
  refine SecMod.of_nontrivial (r_le_s C D) (le_normalizer_conjClosure _ L) le_normalizer_r
    (fun a ha b hb => ?_) (fun a ha => ?_) D.surj (fun l hl x hx => ?_) ?_
  · have h1 := Subgroup.commutator_mem_commutator ha hb
    rw [C.frattini.2, commutatorElement_def] at h1
    exact hVR h1
  · have h1 : a ^ 2 ∈ ⁅L32A.sL T L V, L32A.sL T L V⁆ :=
      sq_mem_commutator_closure (X := {x | ∃ h ∈ L, ∃ z ∈ fsuU T V, h * z * h⁻¹ = x})
        (fun x hx => by
          obtain ⟨h, -, z, hz, rfl⟩ := hx
          have hz2 : z ^ 2 = 1 := F7.isElemAbelian_pow_eq_one D.elem_u hz
          rw [conj_pow, hz2]
          group) ha
    rw [C.frattini.2] at h1
    exact hVR h1
  · have hlQ : (l : G) ∈ pCoreOf 2 (L ⊔ T) := D.cent_le ⟨l.2, (D.ker l).mp hl⟩
    have h1 := Subgroup.commutator_mem_commutator hlQ hx
    rw [Subgroup.commutator_comm, C.sq, commutatorElement_def] at h1
    exact h1
  · obtain ⟨u, hu, huE⟩ : ∃ u ∈ fsuU T V, u ∉ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ := by
      by_contra hall
      push Not at hall
      have h1 : ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆.relIndex (fsuU T V) = 1 :=
        Subgroup.relIndex_eq_one.mpr hall
      rw [C.relIndex_eu] at h1
      norm_num at h1
    refine ⟨⟨c, D.c_L⟩, u, u_le_s hu, fun h => huE (fpf_ue C D hu ?_)⟩
    rw [← u_inf_r C D]
    exact Subgroup.mem_inf.mpr ⟨mul_mem (conj_c_mem_u C D hu) (inv_mem hu), h⟩

theorem exists_gen_u (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) :
    ∃ m ∈ fsuU T V, m ∉ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ ∧
      ∀ l : ↥L, θ l ∈ H6.borel → (l : G) * m * (l : G)⁻¹ * m⁻¹ ∈ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ := by
  set B : Subgroup G := (H6.borel.comap θ).map L.subtype with hB
  have hBmem : ∀ {b : G}, b ∈ B → ∃ l : ↥L, θ l ∈ H6.borel ∧ (l : G) = b := by
    intro b hb
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hb
    exact ⟨l, hl, rfl⟩
  have hEU := e_le_u C D
  have hBN : ∀ {b : G}, b ∈ B → b ∈ Subgroup.normalizer (fsuV1 T V : Set G) := by
    intro b hb
    obtain ⟨l, hl, rfl⟩ := hBmem hb
    exact (D.ll l).mp (Subgroup.mem_inf.mp (show θ l ∈ Lp ⊓ Ll from hl)).2
  have hBU : B ≤ Subgroup.normalizer (fsuU T V : Set G) := fun b hb =>
    le_normalizer_u C D (mem_h_of_mem_normalizer C D (hBN hb))
  have hBE : B ≤ Subgroup.normalizer ((⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ : Subgroup G) : Set G) := by
    intro b hb
    obtain ⟨l, hl, rfl⟩ := hBmem hb
    exact le_normalizer_e ⟨l.2, (D.ll l).mp (Subgroup.mem_inf.mp (show θ l ∈ Lp ⊓ Ll from hl)).2⟩
  have hUE : fsuU T V ≤ Subgroup.normalizer ((⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ : Subgroup G) :
      Set G) := le_normalizer_of_comm hEU fun a ha b hb => u_comm C ha hb
  have hne : ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ ≠ fsuU T V := by
    intro h
    have h1 := C.relIndex_eu
    rw [h, Subgroup.relIndex_self] at h1
    norm_num at h1
  obtain ⟨m, hmU, hmE, hmB⟩ := exists_mem_fix_mod hEU hne D.borel_two (isPGroup_u D) hBU hBE hUE
  exact ⟨m, hmU, hmE, fun l hl => hmB l (Subgroup.mem_map.mpr ⟨l, hl, rfl⟩)⟩

theorem u_eq_closure (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) {m : G}
    (hm : m ∈ fsuU T V) (hmE : m ∉ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆) :
    fsuU T V = Subgroup.closure ({y | ∃ a ∈ L32A.l1 T L V, a * m * a⁻¹ = y} ∪
      ((⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ : Subgroup G) : Set G)) :=
  eq_closure_of_fpf (e_le_u C D) (le_normalizer_of_comm (e_le_u C D)
      fun _ ha _ hb => u_comm C ha hb)
    (fun _ hx => le_normalizer_u C D (l1_le_h C hx))
    (fun _ hx => le_normalizer_e (D.l1_le hx)) C.relIndex_eu
    (fun _ hw h => fpf_ue C D hw (h c D.c_mem)) hm hmE

theorem relIndex_sup_eq {A R : Subgroup G} (hAR : A ≤ Subgroup.normalizer (R : Set G)) :
    R.relIndex (A ⊔ R) = (A ⊓ R).relIndex A := by
  have h1 := card_sup_mul_card_inf' hAR
  have h2 := Subgroup.relIndex_mul_card R (A ⊔ R)
  have h3 := Subgroup.relIndex_mul_card (A ⊓ R) A
  rw [inf_eq_left.mpr le_sup_right] at h2
  rw [inf_eq_left.mpr inf_le_left] at h3
  have hR : 0 < Nat.card R := Nat.card_pos
  have hAR' : 0 < Nat.card ↥(A ⊓ R) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hR hAR')
  calc R.relIndex (A ⊔ R) * (Nat.card R * Nat.card ↥(A ⊓ R))
      = (R.relIndex (A ⊔ R) * Nat.card R) * Nat.card ↥(A ⊓ R) := by ring
    _ = Nat.card ↥(A ⊔ R) * Nat.card ↥(A ⊓ R) := by rw [h2]
    _ = Nat.card A * Nat.card R := h1
    _ = (A ⊓ R).relIndex A * Nat.card ↥(A ⊓ R) * Nat.card R := by rw [h3]
    _ = (A ⊓ R).relIndex A * (Nat.card R * Nat.card ↥(A ⊓ R)) := by ring

theorem isPGroup_r (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) :
    IsPGroup 2 ↥(conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) := fun x =>
  ⟨1, Subtype.ext (by simpa using r_sq C D x.2)⟩

omit [Finite G] in
theorem conj_c_mem_r (D : Data T L V θ c) {r : G}
    (hr : r ∈ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) :
    c * r * c⁻¹ ∈ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_r D.c_L) r).mp hr

theorem s_le_normalizer_r (C : Ctx722 G T L V H γ γ' g k) :
    L32A.sL T L V ≤
      Subgroup.normalizer ((conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L : Subgroup G) : Set G) :=
  fun _ hs => mem_normalizer_of_forall_conj (Q := L32A.sL T L V) (fun q hq r hr => by
    rw [Subgroup.mem_centralizer_iff.mp (C.r_center hr).2 q hq, mul_inv_cancel_right]
    exact hr) hs

theorem lemma14_7_24_cases (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c)
    [(Subgroup.subgroupOf (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) (L32A.sL T L V)).Normal] :
    ∃ ρ : Γ →* AddMonoid.End (Additive (↥(L32A.sL T L V) ⧸
        Subgroup.subgroupOf (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) (L32A.sL T L V))),
      (∀ (l : ↥L) (s : ↥(L32A.sL T L V)),
        ρ (θ l) (Additive.ofMul (QuotientGroup.mk s)) =
          Additive.ofMul (QuotientGroup.mk ((secMod_s C D).conjX l s))) ∧
      ((IsoMod ρ ρV ∧ (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L).relIndex (L32A.sL T L V) =
          4 * (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L).relIndex
            (cfix c (L32A.sL T L V) ⊔ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L)) ∨
        (IsoMod ρ ρCore ∧
          (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L).relIndex (L32A.sL T L V) =
          16 * (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L).relIndex
            (cfix c (L32A.sL T L V) ⊔ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L)) ∨
        (IsoMod ρ ρSt ∧
          (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L).relIndex (L32A.sL T L V) =
          64 * (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L).relIndex
            (cfix c (L32A.sL T L V) ⊔ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L)) ∨
        (IsoMod ρ (prodRep ρV ρSt) ∧
          (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L).relIndex (L32A.sL T L V) =
          256 * (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L).relIndex
            (cfix c (L32A.sL T L V) ⊔ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L)) ∨
        (IsoMod ρ (prodRep ρCore ρSt) ∧
          (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L).relIndex (L32A.sL T L V) =
          1024 * (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L).relIndex
            (cfix c (L32A.sL T L V) ⊔ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L))) := by
  have SM := secMod_s C D
  obtain ⟨m, hmU, hmE, hmT⟩ := exists_gen_u C D
  have hU₀ := u_eq_closure C D hmU hmE
  have hER : ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ ≤ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L :=
    le_conjClosure _ L
  have hUcl : fsuU T V ≤ Subgroup.closure ({y | ∃ a ∈ L32A.l1 T L V, a * m * a⁻¹ = y} ∪
      ((conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L : Subgroup G) : Set G)) := by
    exact hU₀.le.trans (Subgroup.closure_mono (Set.union_subset_union_right _ fun x hx => hER hx))
  have hgen : ∀ s ∈ L32A.sL T L V, s ∈ Subgroup.closure ({y | ∃ l : ↥L, (l : G) * m * (l : G)⁻¹ = y}
      ∪ ((conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L : Subgroup G) : Set G)) := fun s hs =>
    conjClosure_le_closure (l1_le_l D) le_normalizer_r hUcl hs
  have hW : fsuU T V ⊔ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L = Subgroup.closure
      ({y | ∃ l : ↥L, θ l ∈ Ll ∧ (l : G) * m * (l : G)⁻¹ = y} ∪
        ((conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L : Subgroup G) : Set G)) := by
    apply le_antisymm
    · refine sup_le (hU₀.le.trans ?_) fun r hr => Subgroup.subset_closure (Or.inr hr)
      rw [Subgroup.closure_le]
      rintro _ (⟨a, ha, rfl⟩ | he)
      · exact Subgroup.subset_closure (Or.inl ⟨⟨a, l1_le_l D ha⟩,
          (D.ll ⟨a, l1_le_l D ha⟩).mpr (D.l1_le ha).2, rfl⟩)
      · exact Subgroup.subset_closure (Or.inr (hER he))
    · rw [Subgroup.closure_le]
      rintro _ (⟨l, hl, rfl⟩ | hr)
      · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (le_normalizer_u C D
          (mem_h_of_mem_normalizer C D ((D.ll l).mp hl))) m).mp hmU)
      · exact Subgroup.mem_sup_right hr
  have hWY : (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L).relIndex
      (fsuU T V ⊔ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) = 4 := by
    rw [relIndex_sup_eq ((u_le_s).trans (s_le_normalizer_r C)), u_inf_r C D, C.relIndex_eu]
  have hR3 := not_three_dvd_card (isPGroup_r C D)
  have hC : ∀ s, s ∈ cfix c (L32A.sL T L V) ⊔ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L ↔
      s ∈ L32A.sL T L V ∧ c * s * c⁻¹ * s⁻¹ ∈ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L :=
    fun s => mem_cfix_sup_iff D.c3 (r_le_s C D) hR3 (fun r hr => conj_c_mem_r D hr)
      (s_le_normalizer_r C) s
  exact SM.h65_cases volI_H_6_5 (u_le_s hmU) (fun l hl => hER (hmT l hl)) hgen hW hWY
    (x := ⟨c, D.c_L⟩) D.theta_c3 D.theta_c hC

end CFSG.Quasithin.H13.S4
