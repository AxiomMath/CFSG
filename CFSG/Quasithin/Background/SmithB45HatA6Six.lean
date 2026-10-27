module

public import CFSG.Quasithin.Background.SmithB42HatA6Norm
public import CFSG.Quasithin.Background.SmithB42HatA6Dim
public import CFSG.Quasithin.Background.SmithB42Alt6Conj
public import CFSG.Quasithin.Background.SmithB45AltBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115CoverDihedral

public section

namespace CFSG.Quasithin.B45HatA6

open Equiv CFSG.CharacterTheory.SteinbergBY HatA6

section Four

theorem isElemAbelian2_closure_pair {V : Type} [CommGroup V] {a b : MulAut V} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b = b * a) :
    IsElemAbelian2 (Subgroup.closure ({a, b} : Set (MulAut V))) := by
  have hc : ∀ x ∈ ({a, b} : Set (MulAut V)), ∀ y ∈ ({a, b} : Set (MulAut V)),
      x * y = y * x := by
    rintro x (rfl | rfl) y (rfl | rfl)
    · rfl
    · exact hab
    · exact hab.symm
    · rfl
  have h1 : Subgroup.closure ({a, b} : Set (MulAut V)) ≤
      Subgroup.centralizer ({a, b} : Set (MulAut V)) :=
    (Subgroup.closure_le _).mpr fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
      hc y hy x hx
  have h2 : Subgroup.closure ({a, b} : Set (MulAut V)) ≤
      Subgroup.centralizer (Subgroup.closure ({a, b} : Set (MulAut V)) : Set (MulAut V)) :=
    (Subgroup.closure_le _).mpr fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_iff.mp (h1 hy) x hx).symm
  have hcomm : ∀ x ∈ Subgroup.closure ({a, b} : Set (MulAut V)),
      ∀ y ∈ Subgroup.closure ({a, b} : Set (MulAut V)), x * y = y * x :=
    fun x hx y hy => Subgroup.mem_centralizer_iff.mp (h2 hy) x hx
  refine ⟨hcomm, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · rw [pow_two, ha]
    · rw [pow_two, hb]
  | one => exact one_pow 2
  | mul x y hx hy ihx ihy => rw [Commute.mul_pow (hcomm x hx y hy) 2, ihx, ihy, one_mul]
  | inv x _ ih => rw [inv_pow, ih, inv_one]

theorem card_closure_pair_eq_four {X : Type*} [Group X] [Finite X] {a b : X} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    Nat.card (Subgroup.closure ({a, b} : Set X)) = 4 := by
  have hle := CFSG.QuasithinUnique.Ch1.card_closure_involutions_le ha hb
  have hab2 : (a * b) ^ 2 = 1 := by
    rw [pow_two]
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = a * a * (b * b) := by group
      _ = 1 := by rw [ha, hb, one_mul]
  have hord : orderOf (a * b) ≤ 2 := orderOf_le_of_pow_eq_one two_pos hab2
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hne
    calc a = a * (b * b) := by rw [hb, mul_one]
      _ = a * b * b := by rw [mul_assoc]
      _ = b := by rw [h, one_mul]
  have hane : a ≠ a * b := fun h => hb1 (by
    calc b = a⁻¹ * (a * b) := by group
      _ = 1 := by rw [← h, inv_mul_cancel])
  have hbne : b ≠ a * b := fun h => ha1 (by
    calc a = a * b * b⁻¹ := by group
      _ = 1 := by rw [← h, mul_inv_cancel])
  have hl : [1, a, b, a * b].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    exact ⟨⟨Ne.symm ha1, Ne.symm hb1, Ne.symm hab1⟩, ⟨hne, hane⟩, hbne, not_false⟩
  have hge := B42Alt6.length_le_card (Subgroup.closure ({a, b} : Set X)) _ hl (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
  simp only [List.length_cons, List.length_nil] at hge
  omega

theorem comm_of_commutator_mem_center {X : Type*} [Group X] {a b : X} (hb : b * b = 1)
    (hc : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center X) (h3 : (a * b * a⁻¹ * b⁻¹) ^ 3 = 1) :
    a * b = b * a := by
  obtain ⟨c, hcdef⟩ : ∃ c, c = a * b * a⁻¹ * b⁻¹ := ⟨_, rfl⟩
  rw [← hcdef] at hc h3
  have hcu : ∀ y : X, y * c = c * y := Subgroup.mem_center_iff.1 hc
  have hc2 : c * c = 1 := by
    have e1 : c * b = a * b * a⁻¹ := by rw [hcdef]; group
    have e2 : (c * b) * (c * b) = c * c := by
      calc (c * b) * (c * b) = c * (b * c) * b := by group
        _ = c * (c * b) * b := by rw [hcu b]
        _ = c * c * (b * b) := by group
        _ = c * c := by rw [hb, mul_one]
    rw [← e2, e1]
    calc a * b * a⁻¹ * (a * b * a⁻¹) = a * (b * b) * a⁻¹ := by group
      _ = 1 := by rw [hb]; group
  have hc1 : c = 1 := by
    calc c = c ^ 3 * (c * c)⁻¹ := by group
      _ = 1 := by rw [h3, hc2]; group
  calc a * b = c * (b * a) := by rw [hcdef]; group
    _ = b * a := by rw [hc1, one_mul]

theorem pow_three_of_mem_center {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {zL : ↥L}
    (hcen : Subgroup.center ↥L = Subgroup.zpowers zL) (h3 : (zL : MulAut V) ^ 3 = 1) :
    ∀ x ∈ Subgroup.center ↥L, x ^ 3 = 1 := by
  have hz3 : zL ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact h3)
  intro x hx
  rw [hcen] at hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]

end Four

section Fix

variable {V : Type} [CommGroup V] {hsq : ∀ v : V, v * v = 1} {z : MulAut V}
  {u : Fin 3 → V} (hb : Function.Bijective (coordHom hsq z u)) (hzz : ∀ w, z (z w) = w * z w)
  {L : Subgroup (MulAut V)} (hLz : ∀ x ∈ L, ∀ w, x (z w) = z (x w))

theorem linL_eq_self {l : ↥L} (hl : l * l = 1) {c : Fin 3 → FieldFour} (hc : c ≠ 0)
    (hlc : (FieldFour ∙ c).map (linL hb hzz hLz l) = (FieldFour ∙ c)) :
    linL hb hzz hLz l c = c := by
  rw [map_span_singleton] at hlc
  obtain ⟨w, hw⟩ := (span_eq_iff).1 hlc
  rw [Units.smul_def] at hw
  have h2 : linL hb hzz hLz (l * l) c = c := by rw [hl, linL_one, LinearMap.id_apply]
  rw [linL_mul, LinearMap.comp_apply, ← hw, LinearMap.map_smul, ← hw, smul_smul] at h2
  have h3 : ((w : FieldFour) * w - 1) • c = 0 := by rw [sub_smul, one_smul, h2, sub_self]
  have h4 : (w : FieldFour) * w = 1 :=
    sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right hc)
  have hw1 : (w : FieldFour) = 1 := by
    rcases ff_unit_cases w with h | h | h
    · exact h
    · rw [h] at h4
      exact absurd h4 (by decide)
    · rw [h] at h4
      exact absurd h4 (by decide)
  rw [← hw, hw1, one_smul]

end Fix

section Main

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

theorem four_facts :
    (swap (0 : Fin 6) 1 * swap 2 3) * (swap 0 1 * swap 2 3) = 1 ∧
    (swap (0 : Fin 6) 2 * swap 1 3) * (swap 0 2 * swap 1 3) = 1 ∧
    (swap (0 : Fin 6) 1 * swap 2 3) * (swap 0 2 * swap 1 3) =
      (swap 0 2 * swap 1 3) * (swap 0 1 * swap 2 3) ∧
    swap (0 : Fin 6) 1 * swap 2 3 ≠ 1 ∧ swap (0 : Fin 6) 2 * swap 1 3 ≠ 1 ∧
    swap (0 : Fin 6) 1 * swap 2 3 ≠ swap 0 2 * swap 1 3 ∧
    (swap (0 : Fin 6) 1 * swap 2 3 : Perm (Fin 6)) 4 = 4 ∧
    (swap (0 : Fin 6) 1 * swap 2 3 : Perm (Fin 6)) 5 = 5 ∧
    (swap (0 : Fin 6) 2 * swap 1 3 : Perm (Fin 6)) 4 = 4 ∧
    (swap (0 : Fin 6) 2 * swap 1 3 : Perm (Fin 6)) 5 = 5 ∧
    Perm.sign (swap (0 : Fin 6) 1 * swap 2 3) = 1 ∧ Perm.sign (swap (0 : Fin 6) 2 * swap 1 3) = 1 :=
  by decide

theorem qhatOf_le_one_of_card (hV : ∀ v : V, v ^ 2 = 1) (hHyp : B4Hyp G L)
    (hP : B42TypeHatA6 ↥L) (hcard : Nat.card V = 2 ^ 6) : qhatOf G ≤ ((1 : ℚ) : WithTop ℚ) := by
  classical
  obtain ⟨hq, hZ, ⟨e⟩⟩ := id hP
  have hperf : Group.IsPerfect ↥L := hq.1
  obtain ⟨zL, hcen, h3, -, hfp⟩ := HatA6.exists_center_gen hHyp hP
  have hsq : ∀ v : V, v * v = 1 := fun v => by rw [← pow_two]; exact hV v
  set z : MulAut V := (zL : MulAut V) with hzdef
  have hzz : ∀ w, z (z w) = w * z w := fun w =>
    H13.zz_eq_of_fpf hV h3 (W := ⊤) (fun _ _ => trivial) (fun w _ hw => hfp w hw) trivial
  obtain ⟨u, hb⟩ := exists_coord hsq hcard h3 hfp
  have hzc : zL ∈ Subgroup.center ↥L := hcen ▸ Subgroup.mem_zpowers zL
  have hLz : ∀ l ∈ L, ∀ w, l (z w) = z (l w) := by
    intro l hl w
    have h1 := Subgroup.mem_center_iff.1 hzc ⟨l, hl⟩
    exact congrArg (fun y : ↥L => (y : MulAut V) w) h1
  have hirr := HatA6.irr_of_b4Hyp hHyp
  have hz3 : zL ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact h3)
  have hcen3 := pow_three_of_mem_center hcen h3
  have hperf' : commutator ↥L = ⊤ := Group.isPerfect_def.1 hperf
  have hfpf : ∀ k ∈ Subgroup.center ↥L, k ≠ 1 → ∀ v : V, (k : MulAut V) v = v → v = 1 := by
    intro k hk hk1 v hv
    rw [hcen] at hk
    obtain ⟨n, hn0⟩ := (mem_powers_iff_mem_zpowers).2 hk
    have hn0' : zL ^ n = k := hn0
    rw [← hn0'] at hk1 hv
    have hn : zL ^ n = zL ^ (n % 3) := by
      conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, hz3, one_pow, one_mul]
    rw [hn] at hk1 hv
    have hn3 : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases (n % 3)
    · exact absurd (pow_zero zL) hk1
    · exact hfp v (by simpa using hv)
    · apply hfp v
      have h2 : z (z v) = v := by simpa [pow_two, MulAut.mul_apply] using hv
      calc z v = z (z (z v)) := by rw [h2]
        _ = v := by
          have := congrArg (fun y : MulAut V => y v) h3
          simpa [pow_succ, MulAut.mul_apply] using this
  obtain ⟨f, hf1, hf⟩ := H13.Orbit.hatA6_orbits hcard hperf' hZ e hfpf
  set O := H13.Orbit.orbitIn L f with hOdef
  have hO : ∀ l ∈ L, ∀ v ∈ O, l v ∈ O := by
    rintro l hl _ ⟨m, hm, rfl⟩
    exact ⟨l * m, L.mul_mem hl hm, rfl⟩
  have hfO : f ∈ O := ⟨1, L.one_mem, rfl⟩
  have hOcard : Nat.card O = 18 := (hf f hf1).1 hfO
  have h1O : (1 : V) ∉ O := by
    rintro ⟨m, -, hm⟩
    apply hf1
    have := congrArg (fun w => m⁻¹ w) hm
    simpa using this
  have hker : ∀ l : ↥L, ptPerm hb hzz hLz O hO l = 1 → l ∈ Subgroup.center ↥L := by
    intro l hl
    rw [ptPerm_eq_altPerm hb hzz hLz hO rfl hcen e l] at hl
    have h1 : e (QuotientGroup.mk l) = 1 :=
      altPerm_injective hb hzz hLz hO hirr hcard rfl hcen e hOcard h1O
        (hl.trans (map_one _).symm)
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hlift : ∀ σ : Perm ↥(pts hb O), σ ∈ alternatingGroup ↥(pts hb O) → σ * σ = 1 →
      ∃ l : ↥L, l * l = 1 ∧ ptPerm hb hzz hLz O hO l = σ := by
    intro σ hσ hσ2
    rw [← range_ptPerm hb hzz hLz hO hirr hcard rfl hcen e hOcard h1O] at hσ
    obtain ⟨l, hl⟩ := hσ
    have hl2 : l ^ 2 ∈ Subgroup.center ↥L := hker _ (by rw [map_pow, hl, pow_two, hσ2])
    refine ⟨l ^ 3, ?_, ?_⟩
    · rw [← pow_add, show (3 : ℕ) + 3 = 2 * 3 from rfl, pow_mul, hcen3 _ hl2]
    · rw [map_pow, hl, pow_succ, pow_two, hσ2, one_mul]
  have hP6 : Fintype.card ↥(pts hb O) = 6 := by
    rw [Fintype.card_coe]
    exact card_pts_eq hb hzz hO rfl hOcard h1O
  let φ : Fin 6 ≃ ↥(pts hb O) := (Fintype.equivFinOfCardEq hP6).symm
  obtain ⟨ha2, hb2, hab, ha1, hb1, hne, ha4, ha5, hb4, hb5, hsa, hsb⟩ := four_facts
  set a₀ : Perm (Fin 6) := swap 0 1 * swap 2 3 with ha₀
  set b₀ : Perm (Fin 6) := swap 0 2 * swap 1 3 with hb₀
  have hmemA : ∀ σ : Perm (Fin 6), Perm.sign σ = 1 →
      φ.permCongrHom σ ∈ alternatingGroup ↥(pts hb O) := by
    intro σ hσ
    rw [Perm.mem_alternatingGroup, permCongrHom_coe, Perm.sign_permCongr, hσ]
  have hsq' : ∀ σ : Perm (Fin 6), σ * σ = 1 → φ.permCongrHom σ * φ.permCongrHom σ = 1 := by
    intro σ hσ
    rw [← map_mul, hσ, map_one]
  obtain ⟨u₁, hu₁2, hu₁⟩ := hlift _ (hmemA a₀ hsa) (hsq' a₀ ha2)
  obtain ⟨u₂, hu₂2, hu₂⟩ := hlift _ (hmemA b₀ hsb) (hsq' b₀ hb2)
  have hσ : φ.permCongrHom a₀ * φ.permCongrHom b₀ = φ.permCongrHom b₀ * φ.permCongrHom a₀ := by
    rw [← map_mul, hab, map_mul]
  have hcc : u₁ * u₂ * u₁⁻¹ * u₂⁻¹ ∈ Subgroup.center ↥L := hker _ (by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hu₁, hu₂, hσ]
    group)
  have hcomm : u₁ * u₂ = u₂ * u₁ := comm_of_commutator_mem_center hu₂2 hcc (hcen3 _ hcc)
  set E : Subgroup (MulAut V) := Subgroup.closure {(u₁ : MulAut V), (u₂ : MulAut V)} with hE
  have hu₁2' : (u₁ : MulAut V) * u₁ = 1 := congrArg Subtype.val hu₁2
  have hu₂2' : (u₂ : MulAut V) * u₂ = 1 := congrArg Subtype.val hu₂2
  have hcomm' : (u₁ : MulAut V) * u₂ = u₂ * u₁ := congrArg Subtype.val hcomm
  have hne1 : ∀ (l : ↥L) (σ : Perm (Fin 6)), σ ≠ 1 → ptPerm hb hzz hLz O hO l = φ.permCongrHom σ →
      (l : MulAut V) ≠ 1 := by
    intro l σ hσ hlσ h
    have hl1 : l = 1 := Subtype.ext h
    rw [hl1, map_one] at hlσ
    exact hσ (φ.permCongrHom.injective (hlσ.symm.trans (map_one _).symm))
  have hu₁₂ : (u₁ : MulAut V) ≠ u₂ := by
    intro h
    have h1 : u₁ = u₂ := Subtype.ext h
    rw [h1, hu₂] at hu₁
    exact hne (φ.permCongrHom.injective hu₁.symm)
  have hE4 : Nat.card E = 4 :=
    card_closure_pair_eq_four hu₁2' hu₂2' hcomm' (hne1 u₁ a₀ ha1 hu₁) (hne1 u₂ b₀ hb1 hu₂) hu₁₂
  have hEe : IsElemAbelian2 E := isElemAbelian2_closure_pair hu₁2' hu₂2' hcomm'
  have hEG : E ≤ G := by
    rw [hE, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact HatA6.le_of_b4Hyp hHyp u₁.2
    · exact HatA6.le_of_b4Hyp hHyp u₂.2
  obtain ⟨c, hc, hcp⟩ := (mem_pts hb O).1 (φ 4).2
  obtain ⟨d, hd, hdq⟩ := (mem_pts hb O).1 (φ 5).2
  have hc0 := ne_zero_of_mem_okSet hb O h1O hc
  have hd0 := ne_zero_of_mem_okSet hb O h1O hd
  have hcd : (FieldFour ∙ c) ≠ (FieldFour ∙ d) := by
    rw [hcp, hdq]
    intro h
    have h45 := φ.injective (Subtype.ext h)
    exact absurd h45 (by decide)
  have hind := pair_indep hc0 hd0 hcd
  have hfix : ∀ (l : ↥L) (σ : Perm (Fin 6)), l * l = 1 →
      ptPerm hb hzz hLz O hO l = φ.permCongrHom σ → σ 4 = 4 → σ 5 = 5 → ∀ s t : FieldFour,
      (l : MulAut V) (coordEquiv hb (Multiplicative.ofAdd (s • c + t • d))) =
        coordEquiv hb (Multiplicative.ofAdd (s • c + t • d)) := by
    intro l σ hl2 hlσ h4 h5 s t
    have hp : ∀ i : Fin 6, σ i = i → ∀ x : Fin 3 → FieldFour, x ≠ 0 →
        (FieldFour ∙ x) = ((φ i : ↥(pts hb O)) : Submodule FieldFour (Fin 3 → FieldFour)) →
        linL hb hzz hLz l x = x := by
      intro i hi x hx hxp
      apply linL_eq_self hb hzz hLz hl2 hx
      have h1 := congrArg Subtype.val (show ptPerm hb hzz hLz O hO l (φ i) = φ i by
        rw [hlσ, permCongrHom_coe, permCongr_apply, symm_apply_apply, hi])
      rw [ptPerm_apply, ptAct_coe] at h1
      rw [hxp]
      exact h1
    rw [← coordEquiv_linL hb hzz hLz l, map_add, map_smul, map_smul,
      hp 4 h4 c hc0 hcp, hp 5 h5 d hd0 hdq]
  have hmem : ∀ s t : FieldFour, coordEquiv hb (Multiplicative.ofAdd (s • c + t • d)) ∈ fixV E := by
    intro s t x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · exact hfix u₁ a₀ hu₁2 hu₁ ha4 ha5 s t
      · exact hfix u₂ b₀ hu₂2 hu₂ hb4 hb5 s t
    | one => rfl
    | mul p q _ _ hp hq => rw [MulAut.mul_apply, hq, hp]
    | inv p _ hp =>
      calc p⁻¹ (coordEquiv hb (Multiplicative.ofAdd (s • c + t • d))) =
          p⁻¹ (p (coordEquiv hb (Multiplicative.ofAdd (s • c + t • d)))) := by rw [hp]
        _ = coordEquiv hb (Multiplicative.ofAdd (s • c + t • d)) := by simp
  let F : FieldFour × FieldFour → ↥(fixV E) := fun st => ⟨_, hmem st.1 st.2⟩
  have hF : Function.Injective F := by
    rintro ⟨s, t⟩ ⟨s', t'⟩ h
    have h1 := (coordEquiv hb).injective (congrArg Subtype.val h)
    have h2 : s • c + t • d = s' • c + t' • d := Multiplicative.ofAdd.injective h1
    have h3 : (s - s') • c + (t - t') • d = 0 := by
      rw [sub_smul, sub_smul, sub_add_sub_comm, h2, sub_self]
    obtain ⟨h5, h6⟩ := LinearIndependent.pair_iff.1 hind _ _ h3
    rw [sub_eq_zero] at h5 h6
    rw [h5, h6]
  have h16 : 16 ≤ Nat.card (fixV E) := by
    have h := Nat.card_le_card_of_injective F hF
    rwa [Nat.card_prod, FieldFour.natCard_eq] at h
  exact B45Alt.qhatOf_le_one_of_four hV hEG hEe hE4 (by rw [hcard]; omega)

end Main

end CFSG.Quasithin.B45HatA6
