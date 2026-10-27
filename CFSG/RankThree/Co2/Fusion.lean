module

public import CFSG.RankThree.Co2.X9
public import CFSG.RankThree.Co2.JClasses
public import CFSG.Monster.B.Recog.GenericZStar

public noncomputable section

open scoped Pointwise

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Monster.B.Short CFSG.Monster.B.TwoA.Co2Inv

@[expose, instance_reducible] def conjActG {G : Type*} [Group G] (N : Subgroup G) :
    MulAction N G where
  smul n x := (n : G) * x * (n : G)⁻¹
  one_smul x := by change (1 : G) * x * 1⁻¹ = x; group
  mul_smul k l x := by
    change ((k : G) * l) * x * ((k : G) * l)⁻¹ = k * (l * x * (l : G)⁻¹) * (k : G)⁻¹
    group

theorem map_map_conj {K L : Type*} [Group K] [Group L] (e : K ≃* L) (S : Subgroup K) (c : K) :
    (S.map (MulAut.conj c).toMonoidHom).map e.toMonoidHom =
      (S.map e.toMonoidHom).map (MulAut.conj (e c)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem map_subtype_conj {G : Type*} [Group G] (H : Subgroup G) (S : Subgroup H) (c : H) :
    (S.map (MulAut.conj c).toMonoidHom).map H.subtype =
      (S.map H.subtype).map (MulAut.conj (c : G)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem elemTwo_map {K L : Type*} [Group K] [Group L] (f : K →* L) {A : Subgroup K}
    (hA : ElemTwo A) : ElemTwo (A.map f) := by
  constructor
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hA.1 a ha, map_one]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hA.2 a ha b hb]

theorem elemTwo_comap_subtype {G : Type*} [Group G] {H A : Subgroup G} (hA : ElemTwo A) :
    ElemTwo (A.subgroupOf H) := by
  constructor
  · intro a ha
    exact Subtype.ext (hA.1 _ ha)
  · intro a ha b hb
    exact Subtype.ext (hA.2 _ ha _ hb)

namespace Co2CentHyp

variable {G : Type} [Group G] (h : Co2CentHyp G)

@[expose] def JG : Subgroup G := ((subW jWords).map h.φ.symm.toMonoidHom).map h.H.subtype

theorem mem_JG {x : G} : x ∈ h.JG ↔ ∃ y ∈ subW jWords, ((h.φ.symm y : h.H) : G) = x := by
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, rfl⟩

theorem JG_le_H : h.JG ≤ h.H := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem elemTwo_JG : ElemTwo h.JG := elemTwo_map _ (elemTwo_map _ elemTwo_J)

theorem card_JG : Nat.card h.JG = 1024 := by
  rw [JG, Subgroup.card_map_of_injective h.H.subtype_injective,
    Subgroup.card_map_of_injective h.φ.symm.injective, card_J]

theorem z_mem_JG : h.z ∈ h.JG := by
  rw [mem_JG]
  exact ⟨rCr, rCr_mem_J, by rw [h.φ_symm_rCr]; rfl⟩

theorem one_class : ∀ A : Subgroup G, A ≤ Subgroup.centralizer {h.z} → ElemTwo A →
    Nat.card A = Nat.card h.JG →
      ∃ g ∈ Subgroup.centralizer {h.z}, A = h.JG.map (MulAut.conj g).toMonoidHom := by
  intro A hAH hA hcard
  set AH : Subgroup h.H := A.subgroupOf h.H
  set A' : Subgroup Cr := AH.map h.φ.toMonoidHom
  have hA' : ElemTwo A' := elemTwo_map _ (elemTwo_comap_subtype hA)
  have hcard' : Nat.card A' = 1024 := by
    rw [Subgroup.card_map_of_injective h.φ.injective, card_subgroupOf_eq hAH, hcard, card_JG]
  obtain ⟨c, hc⟩ := exists_conj_J_of_elemTwo hA' hcard'
  refine ⟨(h.φ.symm c : G), (h.φ.symm c).2, ?_⟩
  have hAH' : AH = A'.map h.φ.symm.toMonoidHom := by
    rw [Subgroup.map_map]
    ext x
    simp [A']
  have hA_eq : A = AH.map h.H.subtype := (Subgroup.map_subgroupOf_eq_of_le hAH).symm
  rw [hA_eq, hAH', hc, map_map_conj, map_subtype_conj]
  rfl

@[expose] def Ω : Set G := {t | t ∈ h.JG ∧ IsConj h.z t}

theorem card_Ω_dvd : Nat.card h.Ω ∣ Nat.card (Subgroup.normalizer (h.JG : Set G)) := by
  letI := conjActG (Subgroup.normalizer (h.JG : Set G))
  have horb : MulAction.orbit (Subgroup.normalizer (h.JG : Set G)) h.z = h.Ω := by
    ext t
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨(Subgroup.mem_normalizer_iff.1 n.2 h.z).1 h.z_mem_JG, isConj_iff.2 ⟨n, rfl⟩⟩
    · rintro ⟨htJ, hzt⟩
      obtain ⟨n, hn, e⟩ := exists_normalizer_conj_of_class h.elemTwo_JG h.one_class htJ hzt
      exact ⟨⟨n, hn⟩, e⟩
  rw [← horb, Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
  exact Subgroup.index_dvd_card _

theorem card_Ω_eq : Nat.card h.Ω =
    Nat.card {y : subW jWords // IsConj h.z ((h.φ.symm (y : Cr) : h.H) : G)} := by
  symm
  refine Nat.card_congr
    { toFun := fun y => ⟨_, (h.mem_JG).2 ⟨(y.1 : Cr), y.1.2, rfl⟩, y.2⟩
      invFun := fun t => ⟨⟨h.φ ⟨t.1, h.JG_le_H t.2.1⟩, ?_⟩, ?_⟩
      left_inv := fun y => ?_
      right_inv := fun t => ?_ }
  · obtain ⟨y, hy, e⟩ := (h.mem_JG).1 t.2.1
    have : (⟨t.1, h.JG_le_H t.2.1⟩ : h.H) = h.φ.symm y := Subtype.ext e.symm
    rw [this, MulEquiv.apply_symm_apply]
    exact hy
  · change IsConj h.z (((h.φ.symm (h.φ ⟨t.1, h.JG_le_H t.2.1⟩)) : h.H) : G)
    rw [MulEquiv.symm_apply_apply]
    exact t.2.2
  · apply Subtype.ext; apply Subtype.ext
    change h.φ ⟨((h.φ.symm (y : Cr) : h.H) : G), _⟩ = (y : Cr)
    rw [Subtype.coe_eta, MulEquiv.apply_symm_apply]
  · apply Subtype.ext
    change ((h.φ.symm (h.φ ⟨t.1, h.JG_le_H t.2.1⟩) : h.H) : G) = t.1
    rw [MulEquiv.symm_apply_apply]

@[expose] def FusesTwo : Prop := IsConj h.z ((h.φ.symm (rep 2) : h.H) : G)

@[expose] def FusesSeven : Prop := IsConj h.z ((h.φ.symm (rep 7) : h.H) : G)

theorem isConj_z_of_mem_J {y : Cr} (hy : y ∈ subW jWords)
    (hz : IsConj h.z ((h.φ.symm y : h.H) : G)) :
    y = rCr ∨ (IsConj (rep 2) y ∧ h.FusesTwo) ∨ (IsConj (rep 7) y ∧ h.FusesSeven) := by
  have hy1 : y ≠ 1 := by
    intro e
    apply h.ne_one_of_isConj_z hz
    rw [e, map_one]
    rfl
  have hy2 : y * y = 1 := elemTwo_J.1 y hy
  obtain ⟨i, hi, hyi⟩ := exists_isConj_rep y hy2 hy1
  have ht : IsConj h.z ((h.φ.symm y : h.H) : G) := hz
  have hφ : IsConj (h.φ (h.φ.symm y)) (rep i) := by rw [MulEquiv.apply_symm_apply]; exact hyi
  have hbad : ¬ BadClass i := fun hb => h.not_isConj_rep_of_bad ht hb hφ
  have hfuse : IsConj h.z ((h.φ.symm (rep i) : h.H) : G) := hz.trans (h.isConj_φ_symm hyi)
  interval_cases i
  · left
    rw [rep_zero] at hyi
    obtain ⟨g, hg⟩ := isConj_iff.1 hyi.symm
    rw [← hg, conj_rCr]
  · exact absurd (Or.inl rfl) hbad
  · exact Or.inr (Or.inl ⟨hyi.symm, hfuse⟩)
  · exact absurd (Or.inr (Or.inl rfl)) hbad
  · exact absurd (Or.inr (Or.inr (Or.inl rfl))) hbad
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hbad
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hbad
  · exact Or.inr (Or.inr ⟨hyi.symm, hfuse⟩)
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) hbad
  · exact absurd hyi.symm (not_isConj_rep_nine_of_mem_J hy)

theorem isConj_z_of_rCr : IsConj h.z ((h.φ.symm rCr : h.H) : G) := by
  rw [h.φ_symm_rCr]
  rfl

theorem isConj_z_of_class {i : ℕ} {y : Cr} (hyi : IsConj (rep i) y)
    (hf : IsConj h.z ((h.φ.symm (rep i) : h.H) : G)) :
    IsConj h.z ((h.φ.symm y : h.H) : G) :=
  hf.trans (h.isConj_φ_symm hyi)

theorem card_H : Nat.card h.H = 743178240 := by
  rw [Nat.card_congr h.φ.toEquiv, natCard_Cr]

theorem not_mem_H_of_prime {s : G} {p : ℕ} (hs : orderOf s = p) (hp : ¬ p ∣ 743178240)
    (hsz : s * h.z = h.z * s) : False := by
  have hsH : s ∈ h.H := Subgroup.mem_centralizer_singleton_iff.2 hsz
  have := orderOf_dvd_natCard (⟨s, hsH⟩ : h.H)
  rw [Subgroup.orderOf_mk, hs, h.card_H] at this
  exact hp this

theorem not_two_only (h2 : h.FusesTwo) (h7 : ¬ h.FusesSeven) : False := by
  have := h.finite
  have hcard : Nat.card h.Ω = 61 := by
    rw [h.card_Ω_eq, ← card_J_r_two]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
    constructor
    · intro hz
      rcases h.isConj_z_of_mem_J y.2 hz with e | ⟨hc, -⟩ | ⟨-, hf⟩
      · exact Or.inl e
      · exact Or.inr hc
      · exact absurd hf h7
    · rintro (e | hc)
      · rw [e]; exact h.isConj_z_of_rCr
      · exact h.isConj_z_of_class hc h2
  have hdvd := h.card_Ω_dvd
  rw [hcard] at hdvd
  have : Fact (Nat.Prime 61) := ⟨by norm_num⟩
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 61 hdvd
  have hs' : orderOf (s : G) = 61 := by rwa [Subgroup.orderOf_coe]
  have hcent := centralizes_of_prime_order (V := h.JG) (by norm_num) hs' s.2
    (by rw [h.card_JG]; norm_num) (a := 10) (by
      intro c hc1 hc2
      interval_cases c <;> norm_num)
  exact h.not_mem_H_of_prime hs' (by norm_num) (hcent h.z h.z_mem_JG)

@[expose] def VG : Subgroup G :=
  ((Subgroup.closure omegaSeven).map h.φ.symm.toMonoidHom).map h.H.subtype

theorem not_seven_only (h2 : ¬ h.FusesTwo) (h7 : h.FusesSeven) : False := by
  have := h.finite
  have hΩ : h.Ω = (fun y : Cr => ((h.φ.symm y : h.H) : G)) '' omegaSeven := by
    ext t
    constructor
    · rintro ⟨htJ, hzt⟩
      obtain ⟨y, hy, rfl⟩ := (h.mem_JG).1 htJ
      refine ⟨y, ⟨hy, ?_⟩, rfl⟩
      rcases h.isConj_z_of_mem_J hy hzt with e | ⟨-, hf⟩ | ⟨hc, -⟩
      · exact Or.inl e
      · exact absurd hf h2
      · exact Or.inr hc
    · rintro ⟨y, ⟨hy, e | hc⟩, rfl⟩
      · exact ⟨(h.mem_JG).2 ⟨y, hy, rfl⟩, by rw [e]; exact h.isConj_z_of_rCr⟩
      · exact ⟨(h.mem_JG).2 ⟨y, hy, rfl⟩, h.isConj_z_of_class hc h7⟩
  have hV : Subgroup.closure h.Ω = h.VG := by
    rw [hΩ, VG, MonoidHom.map_closure, MonoidHom.map_closure,
      Set.image_image]
    rfl
  have hcard : Nat.card h.Ω = 17 := by
    rw [h.card_Ω_eq, ← card_J_r_seven]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
    constructor
    · intro hz
      rcases h.isConj_z_of_mem_J y.2 hz with e | ⟨-, hf⟩ | ⟨hc, -⟩
      · exact Or.inl e
      · exact absurd hf h2
      · exact Or.inr hc
    · rintro (e | hc)
      · rw [e]; exact h.isConj_z_of_rCr
      · exact h.isConj_z_of_class hc h7
  have hdvd := h.card_Ω_dvd
  rw [hcard] at hdvd
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 17 hdvd
  have hs' : orderOf (s : G) = 17 := by rwa [Subgroup.orderOf_coe]
  have hcardV : Nat.card h.VG = 2 ^ 6 := by
    rw [VG, Subgroup.card_map_of_injective h.H.subtype_injective,
      Subgroup.card_map_of_injective h.φ.symm.injective, card_V]
    norm_num
  have : Finite h.VG := inferInstance
  have hsN : (s : G) ∈ Subgroup.normalizer (h.VG : Set G) := by
    apply mem_normalizer_of_conj_mem
    rw [← hV]
    intro v hv
    have hmap : (Subgroup.closure h.Ω).map (MulAut.conj (s : G)).toMonoidHom ≤
        Subgroup.closure h.Ω := by
      rw [MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro _ ⟨t, ⟨htJ, hzt⟩, rfl⟩
      exact ⟨(Subgroup.mem_normalizer_iff.1 s.2 t).1 htJ,
        hzt.trans (isConj_iff.2 ⟨(s : G), rfl⟩)⟩
    exact hmap ⟨v, hv, rfl⟩
  have hcent := centralizes_of_prime_order (V := h.VG) (by norm_num) hs' hsN hcardV (a := 6)
    (by
      intro c hc1 hc2
      interval_cases c <;> norm_num)
  have hzV : h.z ∈ h.VG := by
    rw [← hV]
    exact Subgroup.subset_closure ⟨h.z_mem_JG, IsConj.refl _⟩
  exact h.not_mem_H_of_prime hs' (by norm_num) (hcent h.z hzV)

theorem fused_two_seven_of_some (hsome : h.FusesTwo ∨ h.FusesSeven) :
    h.FusesTwo ∧ h.FusesSeven := by
  by_cases h2 : h.FusesTwo <;> by_cases h7 : h.FusesSeven
  · exact ⟨h2, h7⟩
  · exact (h.not_two_only h2 h7).elim
  · exact (h.not_seven_only h2 h7).elim
  · rcases hsome with h' | h'
    · exact absurd h' h2
    · exact absurd h' h7

include h in
theorem nonabelian : ∃ a b : G, a * b ≠ b * a := by
  refine ⟨((h.φ.symm fSix : h.H) : G), ((h.φ.symm qOne : h.H) : G), fun e => ?_⟩
  have e' : h.φ.symm fSix * h.φ.symm qOne = h.φ.symm qOne * h.φ.symm fSix := Subtype.ext e
  have e'' : fSix * qOne = qOne * fSix := h.φ.symm.injective
    ((map_mul h.φ.symm _ _).trans (e'.trans (map_mul h.φ.symm _ _).symm))
  apply fSix_conj_qOne.1
  rw [e'', mul_inv_cancel_right]

theorem class_of_isConj_z {t : h.H} (ht : IsConj h.z (t : G)) :
    h.φ t = rCr ∨ IsConj (h.φ t) (rep 2) ∨ IsConj (h.φ t) (rep 7) := by
  obtain ⟨ht2, ht1⟩ := h.φ_invol ht
  obtain ⟨i, hi, hti⟩ := exists_isConj_rep (h.φ t) ht2 ht1
  have hbad : ¬ BadClass i := fun hb => h.not_isConj_rep_of_bad ht hb hti
  interval_cases i
  · left
    rw [rep_zero] at hti
    obtain ⟨g, hg⟩ := isConj_iff.1 hti.symm
    rw [← hg, conj_rCr]
  · exact absurd (Or.inl rfl) hbad
  · exact Or.inr (Or.inl hti)
  · exact absurd (Or.inr (Or.inl rfl)) hbad
  · exact absurd (Or.inr (Or.inr (Or.inl rfl))) hbad
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hbad
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hbad
  · exact Or.inr (Or.inr hti)
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) hbad
  · exact absurd hti (h.not_isConj_rep_nine ht)

theorem fusesTwo_and_fusesSeven : h.FusesTwo ∧ h.FusesSeven := by
  have := h.finite
  have := h.simple
  obtain ⟨g, hne, hcomm⟩ := CFSG.Monster.B.Recog.exists_conj_ne_commute h.nonabelian h.hz
  have hH : g * h.z * g⁻¹ ∈ h.H := Subgroup.mem_centralizer_singleton_iff.2 hcomm
  set t : h.H := ⟨g * h.z * g⁻¹, hH⟩
  have ht : IsConj h.z (t : G) := isConj_iff.2 ⟨g, rfl⟩
  apply h.fused_two_seven_of_some
  rcases h.class_of_isConj_z ht with e | e | e
  · exfalso
    apply hne
    have : t = h.zG := by
      apply h.φ.injective
      rw [e, h.φ_zG]
    exact congrArg Subtype.val this
  · left
    have := h.isConj_φ_symm e
    rw [MulEquiv.symm_apply_apply] at this
    exact ht.trans this
  · right
    have := h.isConj_φ_symm e
    rw [MulEquiv.symm_apply_apply] at this
    exact ht.trans this

theorem isConj_z_iff (t : h.H) : IsConj h.z (t : G) ↔
    h.φ t = rCr ∨ IsConj (h.φ t) (rep 2) ∨ IsConj (h.φ t) (rep 7) := by
  constructor
  · exact h.class_of_isConj_z
  · obtain ⟨h2, h7⟩ := h.fusesTwo_and_fusesSeven
    rintro (e | e | e)
    · have : t = h.zG := by
        apply h.φ.injective
        rw [e, h.φ_zG]
      rw [this]
      rfl
    · have := h.isConj_φ_symm e.symm
      rw [MulEquiv.symm_apply_apply] at this
      exact h2.trans this
    · have := h.isConj_φ_symm e.symm
      rw [MulEquiv.symm_apply_apply] at this
      exact h7.trans this

end Co2CentHyp

end CFSG.RankThree.Co2
