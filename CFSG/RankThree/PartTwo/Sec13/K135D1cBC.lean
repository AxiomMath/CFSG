module

public import CFSG.RankThree.PartTwo.Sec13.F135LastR4Aux
public import CFSG.RankThree.PartTwo.Sec13.F135LastAct
public import CFSG.RankThree.PartTwo.Sec13.K135G1
public import CFSG.RankThree.PartTwo.Sec13.F135LastR3Comp
public import CFSG.RankThree.PartTwo.Sec13.F135LastR3Cube
public import CFSG.RankThree.PartTwo.Sec13.K135K3Core

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open scoped commutatorElement

theorem conj_aut_apply_eq {S : Type*} [Group S] (φ : MulAut S) (s : S) :
    (MulAut.conj : S →* MulAut S) (φ s) = φ * (MulAut.conj : S →* MulAut S) s * φ⁻¹ := by
  ext x
  simp [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem mem_normalizer_sup_of_mem {N : Type} [Group N] {A B : Subgroup N} {g : N}
    (hA : g ∈ Subgroup.normalizer (A : Set N)) (hB : g ∈ Subgroup.normalizer (B : Set N)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup N) : Set N) := by
  have hmap : ∀ K : Subgroup N, g ∈ Subgroup.normalizer (K : Set N) →
      K.map (MulAut.conj g).toMonoidHom = K := by
    intro K hK
    ext y
    rw [r3e_mem_map_conj]
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hK) y)
    simpa using this.symm
  apply r3e_mem_normalizer_of_map_eq
  rw [Subgroup.map_sup, hmap A hA, hmap B hB]

theorem actS_eq_conj_of_acts {N : Type} [Group N] {J₀ : Subgroup N}
    (m : Subgroup.normalizer (J₀ : Set N)) (x : ↥J₀)
    (hx : ∀ j : ↥J₀, (m : N) * (j : N) * (m : N)⁻¹ = (x : N) * (j : N) * (x : N)⁻¹) :
    actS J₀ m = (MulAut.conj : (↥J₀ ⧸ Subgroup.center ↥J₀) →*
      MulAut (↥J₀ ⧸ Subgroup.center ↥J₀)) (QuotientGroup.mk x) := by
  ext s
  induction s using QuotientGroup.induction_on with
  | H j =>
    rw [actS_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hx j)

theorem r3_swap_false {N : Type} [Group N] [Finite N] {p : ℕ} (hp : p.Prime)
    (hno : ∀ A T : Subgroup N, CFSG.Open.IsElemAbelian p A → Nat.card A = p ^ 3 → T ≠ ⊥ →
      IsPGroup 2 T → ¬ A ≤ Subgroup.normalizer (T : Set N))
    {Y : Subgroup N} (hY : Nat.card Y = p) (hYc : Y ≤ Subgroup.center N)
    (hmult : ∀ J : Subgroup N, CFSG.IsComponent J → ¬ p ∣ Nat.card (Subgroup.center J))
    {u : N} {J₀ : Subgroup N} (hJ₀ : CFSG.IsComponent J₀)
    (hne : J₀.map (MulAut.conj u).toMonoidHom ≠ J₀)
    {F Ū : Subgroup N} (hFJ : F ≤ Subgroup.normalizer (J₀ : Set N))
    (hŪJ : Ū ≤ Subgroup.normalizer (J₀ : Set N))
    (hŪ2 : IsPGroup 2 Ū) (hŪF : F ≤ Subgroup.normalizer (Ū : Set N)) (hŪcomm : Ū ≤ ⁅Ū, F⁆)
    (hŪnc : ¬ Ū ≤ Subgroup.centralizer (J₀ : Set N))
    (ha : ∀ f ∈ F, ∃ x ∈ J₀, x ^ p = 1 ∧ ∀ j ∈ J₀, f * j * f⁻¹ = x * j * x⁻¹) : False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : CFSG.IsQuasisimple ↥J₀ := hJ₀.1
  have hperf : Group.IsPerfect ↥J₀ := hq.1
  haveI hInnN : ((MulAut.conj : (↥J₀ ⧸ Subgroup.center ↥J₀) →*
      MulAut (↥J₀ ⧸ Subgroup.center ↥J₀)).range).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  have hcen : Subgroup.center (↥J₀ ⧸ Subgroup.center ↥J₀) = ⊥ := center_quot_eq_bot hq
  have hinj : Function.Injective (MulAut.conj : (↥J₀ ⧸ Subgroup.center ↥J₀) →*
      MulAut (↥J₀ ⧸ Subgroup.center ↥J₀)) := conj_injective_of_center_eq_bot hcen
  let n₀ : Subgroup N := Subgroup.normalizer (J₀ : Set N)
  let ρ : ↥n₀ →* MulAut (↥J₀ ⧸ Subgroup.center ↥J₀) := actS J₀
  let Fn : Subgroup ↥n₀ := F.subgroupOf n₀
  let Un : Subgroup ↥n₀ := Ū.subgroupOf n₀
  let V : Subgroup (MulAut (↥J₀ ⧸ Subgroup.center ↥J₀)) := Un.map ρ
  let Fb : Subgroup (MulAut (↥J₀ ⧸ Subgroup.center ↥J₀)) := Fn.map ρ
  have hFb : Fb ≤ (MulAut.conj : (↥J₀ ⧸ Subgroup.center ↥J₀) →*
      MulAut (↥J₀ ⧸ Subgroup.center ↥J₀)).range := by
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨x, hxJ, -, hx⟩ := ha (m : N) hm
    exact ⟨_, (actS_eq_conj_of_acts m ⟨x, hxJ⟩ fun j => hx j j.2).symm⟩
  have hUnF : Un ≤ ⁅Un, Fn⁆ := by
    have h1 : Un.map n₀.subtype = Ū := Subgroup.map_subgroupOf_eq_of_le hŪJ
    have h2 : Fn.map n₀.subtype = F := Subgroup.map_subgroupOf_eq_of_le hFJ
    have h3 : (⁅Un, Fn⁆).map n₀.subtype = ⁅Ū, F⁆ := by
      rw [Subgroup.map_commutator, h1, h2]
    intro a ha'
    have ha1 : (a : N) ∈ ⁅Ū, F⁆ := hŪcomm (by
      have : (a : N) ∈ Un.map n₀.subtype := ⟨a, ha', rfl⟩
      rwa [h1] at this)
    rw [← h3] at ha1
    obtain ⟨b, hb, hba⟩ := ha1
    have : b = a := Subtype.ext hba
    rwa [this] at hb
  have hVF : V ≤ ⁅V, Fb⁆ := by
    have : (Un.map ρ) ≤ (⁅Un, Fn⁆).map ρ := Subgroup.map_mono hUnF
    rwa [Subgroup.map_commutator] at this
  have hVinn : V ≤ (MulAut.conj : (↥J₀ ⧸ Subgroup.center ↥J₀) →*
      MulAut (↥J₀ ⧸ Subgroup.center ↥J₀)).range :=
    hVF.trans ((Subgroup.commutator_mono le_top hFb).trans (Subgroup.commutator_le_right ⊤ _))
  have hUn2 : IsPGroup 2 Un := hŪ2.comap_subtype
  have hV2 : IsPGroup 2 V := hUn2.map ρ
  have hVn : ∀ g ∈ Fb, ∀ v ∈ V, g * v * g⁻¹ ∈ V := by
    rintro _ ⟨m, hm, rfl⟩ _ ⟨a, ha', rfl⟩
    refine ⟨m * a * m⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    have hm' : (m : N) ∈ F := hm
    have ha'' : (a : N) ∈ Ū := ha'
    exact (Subgroup.mem_normalizer_iff.mp (hŪF hm') (a : N)).mp ha''
  have hV1 : V ≠ ⊥ := by
    obtain ⟨a, haU, hanc⟩ := (SetLike.not_le_iff_exists.mp hŪnc)
    intro hV
    have hmem : ρ ⟨a, hŪJ haU⟩ ∈ V := ⟨⟨a, hŪJ haU⟩, haU, rfl⟩
    rw [hV, Subgroup.mem_bot] at hmem
    exact hanc ((actS_eq_one_iff hperf ⟨a, hŪJ haU⟩).mp hmem)
  have hFb1 : Fb ≠ ⊥ := by
    intro h
    apply hV1
    have := hVF
    rw [h, Subgroup.commutator_bot_right] at this
    exact le_bot_iff.mp this
  obtain ⟨⟨g, hgFb⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hFb1
  obtain ⟨m, hm, hmg⟩ := hgFb
  have hm' : (m : N) ∈ F := hm
  obtain ⟨x, hxJ, hxp, hx⟩ := ha (m : N) hm'
  let x' : ↥J₀ := ⟨x, hxJ⟩
  have hρm : ρ m = (MulAut.conj : (↥J₀ ⧸ Subgroup.center ↥J₀) →*
      MulAut (↥J₀ ⧸ Subgroup.center ↥J₀)) (QuotientGroup.mk x') :=
    actS_eq_conj_of_acts m x' fun j => hx j j.2
  have hg1' : g ≠ 1 := fun h => hg1 (Subtype.ext h)
  have hxb1 : (QuotientGroup.mk x' : ↥J₀ ⧸ Subgroup.center ↥J₀) ≠ 1 := by
    intro h
    apply hg1'
    rw [← hmg, hρm, h, map_one]
  have hx1 : x ≠ 1 := by
    intro h
    apply hxb1
    have : x' = 1 := Subtype.ext h
    rw [this, QuotientGroup.mk_one]
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  let c : (↥J₀ ⧸ Subgroup.center ↥J₀) →* MulAut (↥J₀ ⧸ Subgroup.center ↥J₀) := MulAut.conj
  let VS : Subgroup (↥J₀ ⧸ Subgroup.center ↥J₀) := V.comap c
  have hVS2 : IsPGroup 2 VS := hV2.comap_of_injective c hinj
  have hVS1 : VS ≠ ⊥ := by
    intro h
    apply hV1
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨s, rfl⟩ := hVinn hv
    have hs : s ∈ VS := hv
    rw [h, Subgroup.mem_bot] at hs
    rw [hs, map_one]
    exact Subgroup.one_mem _
  have hinv : ∀ s ∈ VS, (MulAut.conj (QuotientGroup.mk x' : ↥J₀ ⧸ Subgroup.center ↥J₀) :
      MulAut (↥J₀ ⧸ Subgroup.center ↥J₀)) s ∈ VS := by
    intro s hs
    rw [Subgroup.mem_comap] at hs ⊢
    rw [conj_aut_apply_eq]
    exact hVn _ ⟨m, hm, hρm⟩ _ hs
  obtain ⟨T₀, hT₀1, hT₀2, hT₀map⟩ := exists_invariant_two_subgroup_of_central
    (QuotientGroup.mk' (Subgroup.center ↥J₀)) (QuotientGroup.mk'_surjective _)
    (by intro z hz; rwa [QuotientGroup.ker_mk'] at hz) (MulAut.conj x')
    (MulAut.conj (QuotientGroup.mk x' : ↥J₀ ⧸ Subgroup.center ↥J₀))
    (fun j => by simp [MulAut.conj_apply]) VS hVS1 hVS2 hinv
  let T₀' : Subgroup N := T₀.map J₀.subtype
  have hxn : x ∈ Subgroup.normalizer (J₀ : Set N) := Subgroup.le_normalizer hxJ
  have hxT₀ : x ∈ Subgroup.normalizer (T₀' : Set N) := by
    refine r4_normalizer_of_map J₀ ⟨x, hxn⟩ T₀ ?_
    have e : J₀.normalizerMonoidHom ⟨x, hxn⟩ = MulAut.conj x' :=
      MulEquiv.ext fun j => Subtype.ext rfl
    rw [e]
    exact hT₀map
  let J₁ : Subgroup N := J₀.map (MulAut.conj u).toMonoidHom
  have hJ₁c : CFSG.IsComponent J₁ :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj u) hJ₀
  have hJ₀J₁ : J₀ ≠ J₁ := fun h => hne h.symm
  have hcomm : ∀ a ∈ J₀, ∀ b ∈ J₁, a * b = b * a := by
    intro a ha' b hb
    rcases CFSG.LocalCores.distinct_components_commute hJ₀ hJ₁c with he | hb'
    · exact absurd he hJ₀J₁
    · have hab : ⁅a, b⁆ ∈ ⁅J₀, J₁⁆ := Subgroup.commutator_mem_commutator ha' hb
      rw [hb', Subgroup.mem_bot] at hab
      exact commutatorElement_eq_one_iff_mul_comm.1 hab
  let x₁ : N := u * x * u⁻¹
  have hx₁J : x₁ ∈ J₁ := ⟨x, hxJ, rfl⟩
  have hx₁o : orderOf x₁ = p := by
    have h := orderOf_injective (MulAut.conj u).toMonoidHom (MulAut.conj u).injective x
    rw [hxo] at h
    exact h
  obtain ⟨F', hF'el, hF'card, hF'eq⟩ := r3_elem3 hp hY hYc hJ₀ hJ₁c hJ₀J₁ (hmult J₀ hJ₀)
    (hmult J₁ hJ₁c) hxJ hx₁J hxo hx₁o
  let T₁' : Subgroup N := T₀'.map (MulAut.conj u).toMonoidHom
  have hT₀'J : T₀' ≤ J₀ := Subgroup.map_subtype_le T₀
  have hT₁'J : T₁' ≤ J₁ := Subgroup.map_mono hT₀'J
  have hx₁T₁ : x₁ ∈ Subgroup.normalizer (T₁' : Set N) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [r3c_conj_mem_map_iff, r3c_conj_mem_map_iff]
    have e : u⁻¹ * (x₁ * y * x₁⁻¹) * u = x * (u⁻¹ * y * u) * x⁻¹ := by
      simp only [x₁]
      group
    rw [e]
    exact Subgroup.mem_normalizer_iff.mp hxT₀ (u⁻¹ * y * u)
  have hT₀'2 : IsPGroup 2 T₀' := hT₀2.map J₀.subtype
  have hT₁'2 : IsPGroup 2 T₁' := hT₀'2.map _
  have hTc : ∀ a ∈ T₀', ∀ b ∈ T₁', a * b = b * a := fun a ha' b hb =>
    hcomm a (hT₀'J ha') b (hT₁'J hb)
  have hT2 : IsPGroup 2 (T₀' ⊔ T₁' : Subgroup N) := r3c_isPGroup_sup hT₀'2 hT₁'2 hTc
  have hT0ne : T₀' ≠ ⊥ := fun h =>
    hT₀1 ((Subgroup.map_eq_bot_iff_of_injective T₀ Subtype.coe_injective).mp h)
  have hTne : (T₀' ⊔ T₁' : Subgroup N) ≠ ⊥ := fun h =>
    hT0ne (le_bot_iff.mp (le_sup_left.trans h.le))
  have hF'N : F' ≤ Subgroup.normalizer ((T₀' ⊔ T₁' : Subgroup N) : Set N) := by
    rw [hF'eq]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact (hYc.trans (Subgroup.center_le_centralizer _)).trans
        (Subgroup.centralizer_le_normalizer _)
    · refine Subgroup.zpowers_le.mpr (mem_normalizer_sup_of_mem hxT₀ ?_)
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hcomm x hxJ b (hT₁'J hb)).symm
    · refine Subgroup.zpowers_le.mpr (mem_normalizer_sup_of_mem ?_ hx₁T₁)
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact hcomm b (hT₀'J hb) x₁ hx₁J
  exact hno F' (T₀' ⊔ T₁') hF'el hF'card hTne hT2 hF'N

end CFSG.RankThree.PartTwo.Sec13.F135Last

