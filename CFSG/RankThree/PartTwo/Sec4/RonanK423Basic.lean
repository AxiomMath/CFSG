module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census423Three.GoodGroupGen

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK423

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Res423Two
open CFSG.AGLEmbeddingD2.Wilson.Census423Three
open scoped commutatorElement

variable {X : Type} [Group X]

omit [Group X] in
theorem isSimpleGroup_of_isQuasisimple_center_eq_bot {X : Type} [Group X]
    (hq : CFSG.IsQuasisimple X) (hZ : Subgroup.center X = ⊥) : IsSimpleGroup X := by
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hq.2.1
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup

theorem derived_le (C : Subgroup X) : ⁅C, C⁆ ≤ C :=
  Subgroup.commutator_le.2 fun v hv w hw => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hv hw) (inv_mem hv)) (inv_mem hw)

theorem conj_mem_derived {C : Subgroup X} {x r : X} (hx : x ∈ C) (hr : r ∈ ⁅C, C⁆) :
    x * r * x⁻¹ ∈ ⁅C, C⁆ := by
  have h1 : ⁅x, r⁆ ∈ ⁅C, ⁅C, C⁆⁆ := Subgroup.commutator_mem_commutator hx hr
  have h2 : ⁅C, ⁅C, C⁆⁆ ≤ ⁅C, C⁆ := Subgroup.commutator_mono_right (derived_le C)
  have h3 : x * r * x⁻¹ = ⁅x, r⁆ * r := by
    rw [commutatorElement_def]
    group
  rw [h3]
  exact mul_mem (h2 h1) hr

theorem qRes_eq_derived [Finite X] {b : X}
    (hP : ⁅⁅Subgroup.centralizer ({b} : Set X), Subgroup.centralizer ({b} : Set X)⁆,
      ⁅Subgroup.centralizer ({b} : Set X), Subgroup.centralizer ({b} : Set X)⁆⁆ =
      ⁅Subgroup.centralizer ({b} : Set X), Subgroup.centralizer ({b} : Set X)⁆) :
    qRes b = ⁅Subgroup.centralizer ({b} : Set X), Subgroup.centralizer ({b} : Set X)⁆ := by
  set C := Subgroup.centralizer ({b} : Set X) with hC
  apply le_antisymm
  · unfold qRes inSubgroup
    have h1 : perfectResidual ↥C ≤ derivedSeries ↥C 1 := iInf_le _ 1
    calc (perfectResidual ↥C).map C.subtype ≤ (derivedSeries ↥C 1).map C.subtype :=
          Subgroup.map_mono h1
      _ = ⁅C, C⁆ := by
          rw [derivedSeries_one]
          exact Subgroup.map_subtype_commutator C
  · have key : ∀ n : ℕ, ⁅C, C⁆ ≤ (derivedSeries ↥C n).map C.subtype := by
      intro n
      induction n with
      | zero =>
        rw [derivedSeries_zero, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
        exact derived_le C
      | succ n ih =>
        rw [derivedSeries_succ, Subgroup.map_commutator, ← hP]
        exact Subgroup.commutator_mono ih ih
    unfold qRes inSubgroup
    rw [perfectResidual, Subgroup.map_iInf _ C.subtype_injective]
    exact le_iInf key

theorem qRes_eq_derived_of_isQuasisimple [Finite X] {b : X}
    (hq : CFSG.IsQuasisimple ↥(⁅Subgroup.centralizer ({b} : Set X),
      Subgroup.centralizer ({b} : Set X)⁆)) :
    qRes b = ⁅Subgroup.centralizer ({b} : Set X), Subgroup.centralizer ({b} : Set X)⁆ := by
  haveI : Group.IsPerfect ↥(⁅Subgroup.centralizer ({b} : Set X),
      Subgroup.centralizer ({b} : Set X)⁆) := hq.1
  exact qRes_eq_derived (Subgroup.commutator_eq_self)

variable [Finite X]

theorem theta_central_of_derived (b : X)
    (hq : CFSG.IsQuasisimple ↥(⁅Subgroup.centralizer ({b} : Set X),
      Subgroup.centralizer ({b} : Set X)⁆))
    (hZ3 : ∀ z ∈ Subgroup.center ↥(⁅Subgroup.centralizer ({b} : Set X),
      Subgroup.centralizer ({b} : Set X)⁆), ∃ k : ℕ, z ^ 3 ^ k = 1) :
    ∀ x ∈ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set X)),
      ∀ c ∈ Subgroup.centralizer ({b} : Set X), x * c = c * x := by
  classical
  set C := Subgroup.centralizer ({b} : Set X) with hC
  set R : Subgroup X := ⁅C, C⁆ with hR
  set Θ := inSubgroup (aschbacherSolvableCore 3) C with hΘ
  have hΘC : Θ ≤ C := inSubgroup_theta_le C
  have hRC : R ≤ C := derived_le C
  have hΘ3 : ¬ 3 ∣ Nat.card Θ := not_three_dvd_card_inSubgroup_theta C
  have hbot : ∀ x ∈ Θ, x ∈ R → x = 1 := by
    intro x hxΘ hxR
    set N : Subgroup ↥R := (Θ ⊓ R).subgroupOf R with hN
    have hNn : N.Normal := by
      refine ⟨fun m hm g => ?_⟩
      rw [hN, Subgroup.mem_subgroupOf] at hm ⊢
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · have := conj_mem_inSubgroup_theta' (hRC g.2) (Subgroup.mem_inf.1 hm).1
        simpa using this
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2 (Subgroup.mem_inf.1 hm).2)
          (Subgroup.inv_mem _ g.2)
    have hNs : Group.IsSolvable N := by
      have : Group.IsSolvable ↥Θ := isSolvable_inSubgroup_theta C
      let f : N →* ↥Θ :=
        { toFun := fun n => ⟨((n : ↥R) : X),
            (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 n.2)).1⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      refine Group.isSolvable_of_isSolvable_injective (f := f) ?_
      intro u v huv
      exact Subtype.ext (Subtype.ext (congrArg (fun w : ↥Θ => (w : X)) huv))
    have hxN : (⟨x, hxR⟩ : ↥R) ∈ N := Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hxΘ, hxR⟩)
    have hcen : (⟨x, hxR⟩ : ↥R) ∈ Subgroup.center ↥R := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact (rad_of_isQuasisimple hq hNn hNs _ hxN g).symm
    obtain ⟨k, hk⟩ := hZ3 _ hcen
    have hx3 : x ^ 3 ^ k = 1 := congrArg Subtype.val hk
    have h1 : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hx3
    have h2 : orderOf (⟨x, hxΘ⟩ : ↥Θ) ∣ Nat.card Θ := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h2
    obtain ⟨j, hj, hjx⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0, pow_zero] at hjx
      exact orderOf_eq_one_iff.mp hjx
    · exfalso
      apply hΘ3
      refine (dvd_pow_self 3 hpos.ne').trans ?_
      rw [← hjx]
      exact h2
  intro x hx c hc
  have hxC : x ∈ C := hΘC hx
  have hcomm : ⁅x, c⁆ = 1 := by
    apply hbot
    · have h1 : c * x⁻¹ * c⁻¹ ∈ Θ := conj_mem_inSubgroup_theta' hc (inv_mem hx)
      have := Subgroup.mul_mem _ hx h1
      rwa [← mul_assoc, ← mul_assoc, ← commutatorElement_def] at this
    · exact Subgroup.commutator_mem_commutator hxC hc
  exact (commutatorElement_eq_one_iff_mul_comm.1 hcomm)

theorem thetaJ_eq_bot_of_central (hZ : Subgroup.center X = ⊥) {D : Subgroup X}
    (hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hDexp : ∀ x ∈ D, x ^ 3 = 1)
    (Hc : ∀ b ∈ D, b ≠ 1 → ∀ x ∈ inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({b} : Set X)), ∀ c ∈ Subgroup.centralizer ({b} : Set X),
        x * c = c * x)
    {Y : Subgroup (MulAut X)} (hY : (MulAut.conj : X →* MulAut X).range ≤ Y) :
    thetaJ 3 ((D.map (MulAut.conj : X →* MulAut X)).subgroupOf Y) = ⊥ := by
  have hinj := conj_injective_of_center hZ
  set B := (D.map (MulAut.conj : X →* MulAut X)).subgroupOf Y with hB
  refine eq_bot_iff.mpr (iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_)
  obtain ⟨b₀, hb₀, hbb₀⟩ := Subgroup.mem_subgroupOf.mp hb
  have hb₀1 : b₀ ≠ 1 := by
    rintro rfl
    apply hb1
    apply Subtype.ext
    rw [← hbb₀]
    simp
  rw [Subgroup.commutator_le]
  intro q hq' d hd
  obtain ⟨d₀, hd₀, hdd₀⟩ := Subgroup.mem_subgroupOf.mp hd
  have hd₀C : d₀ ∈ Subgroup.centralizer ({b₀} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hDc d₀ hd₀ b₀ hb₀)
  have hqd : (q : MulAut X) d₀ = d₀ := by
    have hz := mem_theta_of_mem_theta hZ hY hbb₀.symm hq' hd₀C
    set z := (q : MulAut X) d₀ * d₀⁻¹ with hzdef
    have hzc : z * d₀ = d₀ * z := Hc b₀ hb₀ hb₀1 z hz d₀ hd₀C
    have hzd : (q : MulAut X) d₀ = z * d₀ := by rw [hzdef]; group
    have hq3 : ((q : MulAut X) d₀) ^ 3 = 1 := by
      rw [← map_pow, hDexp d₀ hd₀, map_one]
    have hz3 : z ^ 3 = 1 := by
      rw [hzd, (show Commute z d₀ from hzc).mul_pow, hDexp d₀ hd₀, mul_one] at hq3
      exact hq3
    have hz1 : z = 1 := by
      have h1 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
      have h2 : orderOf (⟨z, hz⟩ : ↥(inSubgroup (aschbacherSolvableCore 3)
          (Subgroup.centralizer ({b₀} : Set X)))) ∣ Nat.card
          (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b₀} : Set X))) :=
        orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h2
      rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
      · exact orderOf_eq_one_iff.mp h
      · rw [h] at h2
        exact absurd h2 (not_three_dvd_card_inSubgroup_theta _)
    rw [hzd, hz1, one_mul]
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [← hdd₀]
  have h1 := mulAut_mul_conj_mul_inv (q : MulAut X) d₀
  rw [hqd] at h1
  calc (q : MulAut X) * MulAut.conj d₀ =
      (q : MulAut X) * MulAut.conj d₀ * (q : MulAut X)⁻¹ * (q : MulAut X) := by group
    _ = MulAut.conj d₀ * (q : MulAut X) := by rw [h1]

theorem alphaVanishes_of_local_central (hZ : Subgroup.center X = ⊥) {D : Subgroup X}
    (hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hDexp : ∀ x ∈ D, x ^ 3 = 1)
    (Hc : ∀ b ∈ D, b ≠ 1 → ∀ x ∈ inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({b} : Set X)), ∀ c ∈ Subgroup.centralizer ({b} : Set X),
        x * c = c * x)
    (H3 : (⊤ : Subgroup X) ≤ Subgroup.closure {x : X | ∃ b ∈ D, b ≠ 1 ∧ x ∈ qRes b}) :
    AlphaVanishes X D := by
  intro Y hY
  have hinj := conj_injective_of_center hZ
  set B := (D.map (MulAut.conj : X →* MulAut X)).subgroupOf Y with hB
  have hJ : thetaJ 3 B = ⊥ := thetaJ_eq_bot_of_central hZ hDc hDexp Hc hY
  have hT : thetaT 3 B = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    rw [Subgroup.mem_bot]
    have htfix : ∀ x : X, (∃ b ∈ D, b ≠ 1 ∧ x ∈ qRes b) → (t : MulAut X) x = x := by
      rintro x ⟨b₀, hb₀, hb₀1, hx⟩
      have hbY : MulAut.conj b₀ ∈ Y := hY ⟨b₀, rfl⟩
      set b : Y := ⟨MulAut.conj b₀, hbY⟩
      have hbB : b ∈ B := Subgroup.mem_subgroupOf.mpr ⟨b₀, hb₀, rfl⟩
      have hb1 : b ≠ 1 := by
        intro h1
        apply hb₀1
        apply hinj
        rw [map_one]
        exact congrArg Subtype.val h1
      have htb : t ∈
          inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set Y)) := by
        have h1 := Subgroup.mem_iInf.mp ht b
        have h2 := Subgroup.mem_iInf.mp h1 hbB
        exact Subgroup.mem_iInf.mp h2 hb1
      exact fixes_qRes hZ hY (b := b) (d := b₀) rfl
        (fun z hz y hy => Hc b₀ hb₀ hb₀1 z hz.1 y (qRes_le b₀ hy)) htb x hx
    have hle : Subgroup.closure {x : X | ∃ b ∈ D, b ≠ 1 ∧ x ∈ qRes b} ≤
        (t : MulAut X).toMonoidHom.eqLocus (MonoidHom.id X) := by
      rw [Subgroup.closure_le]
      intro x hx
      exact htfix x hx
    apply Subtype.ext
    ext x
    exact hle (H3 (Subgroup.mem_top x))
  rw [thetaAlpha, hJ, hT, sup_bot_eq]

theorem alphaVanishes_of_derived_quasisimple (hZ : Subgroup.center X = ⊥) {D : Subgroup X}
    (hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hDexp : ∀ x ∈ D, x ^ 3 = 1)
    (hq : ∀ b ∈ D, b ≠ 1 → CFSG.IsQuasisimple ↥(⁅Subgroup.centralizer ({b} : Set X),
      Subgroup.centralizer ({b} : Set X)⁆))
    (hZ3 : ∀ b ∈ D, b ≠ 1 → ∀ z ∈ Subgroup.center ↥(⁅Subgroup.centralizer ({b} : Set X),
      Subgroup.centralizer ({b} : Set X)⁆), ∃ k : ℕ, z ^ 3 ^ k = 1)
    (H3 : (⊤ : Subgroup X) ≤ Subgroup.closure {x : X | ∃ b ∈ D, b ≠ 1 ∧ x ∈ qRes b}) :
    AlphaVanishes X D :=
  alphaVanishes_of_local_central hZ hDc hDexp
    (fun b hb hb1 => theta_central_of_derived b (hq b hb hb1) (hZ3 b hb hb1)) H3

theorem centralizer_le_derived_sup {D : Subgroup X} {b : X} (hb : b ∈ D)
    (hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) {A : Subgroup X}
    (hA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    (hAR : ∀ a ∈ A, ∀ r ∈ ⁅Subgroup.centralizer ({b} : Set X), Subgroup.centralizer ({b} : Set X)⁆,
      a * r = r * a)
    (hC : Subgroup.centralizer ({b} : Set X) ≤
      ⁅Subgroup.centralizer ({b} : Set X), Subgroup.centralizer ({b} : Set X)⁆ ⊔ A) :
    Subgroup.centralizer ({b} : Set X) ≤
      ⁅Subgroup.centralizer ({b} : Set X), Subgroup.centralizer ({b} : Set X)⁆ ⊔
        Subgroup.centralizer (D : Set X) := by
  have hAD : A ≤ Subgroup.centralizer (D : Set X) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hdC : d ∈ Subgroup.centralizer ({b} : Set X) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hDc d hd b hb)
    have hle : ⁅Subgroup.centralizer ({b} : Set X), Subgroup.centralizer ({b} : Set X)⁆ ⊔ A ≤
        Subgroup.centralizer ({a} : Set X) :=
      sup_le (fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (hAR a ha r hr).symm)
        (fun a' ha' => Subgroup.mem_centralizer_singleton_iff.mpr (hA a ha a' ha').symm)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (hC hdC))
  exact hC.trans (sup_le_sup_left hAD _)

theorem layers_gen [IsSimpleGroup X] {D : Subgroup X}
    (hgen : (⊤ : Subgroup X) ≤ Subgroup.closure {x : X | ∃ b ∈ D, b ≠ 1 ∧ x * b = b * x})
    (hCD : ∀ b ∈ D, b ≠ 1 → Subgroup.centralizer ({b} : Set X) ≤
      ⁅Subgroup.centralizer ({b} : Set X), Subgroup.centralizer ({b} : Set X)⁆ ⊔
        Subgroup.centralizer (D : Set X))
    (hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a)
    (hne : ∃ b ∈ D, b ≠ 1 ∧ ⁅Subgroup.centralizer ({b} : Set X),
      Subgroup.centralizer ({b} : Set X)⁆ ≠ ⊥) :
    (⊤ : Subgroup X) ≤ Subgroup.closure {x : X | ∃ b ∈ D, b ≠ 1 ∧
      x ∈ ⁅Subgroup.centralizer ({b} : Set X), Subgroup.centralizer ({b} : Set X)⁆} := by
  set M : Subgroup X := Subgroup.closure {x : X | ∃ b ∈ D, b ≠ 1 ∧
      x ∈ ⁅Subgroup.centralizer ({b} : Set X), Subgroup.centralizer ({b} : Set X)⁆} with hM
  have hMgen : ∀ b ∈ D, b ≠ 1 → ∀ x ∈ ⁅Subgroup.centralizer ({b} : Set X),
      Subgroup.centralizer ({b} : Set X)⁆, x ∈ M := fun b hb hb1 x hx =>
    Subgroup.subset_closure ⟨b, hb, hb1, hx⟩
  have hCDN : Subgroup.centralizer (D : Set X) ≤ Subgroup.normalizer (M : Set X) := by
    intro z hz
    have hmap : M.map (MulAut.conj z).toMonoidHom ≤ M := by
      rw [hM, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨x, ⟨b, hb, hb1, hx⟩, rfl⟩
      have hzb : z ∈ Subgroup.centralizer ({b} : Set X) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hz b hb).symm
      exact Subgroup.subset_closure ⟨b, hb, hb1, conj_mem_derived hzb hx⟩
    refine Subgroup.mem_normalizer_fintype fun m hm => ?_
    exact hmap ⟨m, hm, rfl⟩
  have hC : ∀ b ∈ D, b ≠ 1 → ∀ c ∈ Subgroup.centralizer ({b} : Set X),
      c ∈ Subgroup.normalizer (M : Set X) := by
    intro b hb hb1 c hc
    have h1 : ⁅Subgroup.centralizer ({b} : Set X), Subgroup.centralizer ({b} : Set X)⁆ ⊔
        Subgroup.centralizer (D : Set X) ≤ Subgroup.normalizer (M : Set X) :=
      sup_le (fun x hx => Subgroup.le_normalizer (hMgen b hb hb1 x hx)) hCDN
    exact h1 (hCD b hb hb1 hc)
  have hN : (⊤ : Subgroup X) ≤ Subgroup.normalizer (M : Set X) := by
    refine hgen.trans ?_
    rw [Subgroup.closure_le]
    rintro x ⟨b, hb, hb1, hx⟩
    exact hC b hb hb1 x (Subgroup.mem_centralizer_singleton_iff.mpr hx)
  have hMn : M.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hN)
  obtain ⟨b, hb, hb1, hRne⟩ := hne
  have hMbot : M ≠ ⊥ := by
    intro h
    apply hRne
    rw [eq_bot_iff]
    intro x hx
    have := hMgen b hb hb1 x hx
    rwa [h] at this
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with h | h
  · exact absurd h hMbot
  · rw [h]

theorem alphaVanishes_of_derived (hX : CFSG.IsQuasisimple X) (hZ : Subgroup.center X = ⊥)
    {D : Subgroup X} (hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hDexp : ∀ x ∈ D, x ^ 3 = 1)
    (hD9 : Nat.card D = 9)
    (hq : ∀ b ∈ D, b ≠ 1 → CFSG.IsQuasisimple ↥(⁅Subgroup.centralizer ({b} : Set X),
      Subgroup.centralizer ({b} : Set X)⁆))
    (hZ3 : ∀ b ∈ D, b ≠ 1 → ∀ z ∈ Subgroup.center ↥(⁅Subgroup.centralizer ({b} : Set X),
      Subgroup.centralizer ({b} : Set X)⁆), ∃ k : ℕ, z ^ 3 ^ k = 1)
    (hCD : ∀ b ∈ D, b ≠ 1 → Subgroup.centralizer ({b} : Set X) ≤
      ⁅Subgroup.centralizer ({b} : Set X), Subgroup.centralizer ({b} : Set X)⁆ ⊔
        Subgroup.centralizer (D : Set X))
    (hgen : (⊤ : Subgroup X) ≤ Subgroup.closure {x : X | ∃ b ∈ D, b ≠ 1 ∧ x * b = b * x}) :
    AlphaVanishes X D := by
  haveI : IsSimpleGroup X := isSimpleGroup_of_isQuasisimple_center_eq_bot hX hZ
  obtain ⟨b, hb, hb1⟩ : ∃ b ∈ D, b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hle : D ≤ ⊥ := fun x hx => Subgroup.mem_bot.mpr (hcon x hx)
    have := Subgroup.card_le_of_le hle
    rw [Subgroup.card_bot] at this
    omega
  have hne : ∃ b ∈ D, b ≠ 1 ∧ ⁅Subgroup.centralizer ({b} : Set X),
      Subgroup.centralizer ({b} : Set X)⁆ ≠ ⊥ := by
    refine ⟨b, hb, hb1, fun h => ?_⟩
    have hq' := hq b hb hb1
    set R : Subgroup X := ⁅Subgroup.centralizer ({b} : Set X),
      Subgroup.centralizer ({b} : Set X)⁆ with hR
    haveI : IsSimpleGroup (↥R ⧸ Subgroup.center ↥R) := hq'.2.1
    haveI : Nontrivial ↥R :=
      (QuotientGroup.mk_surjective : Function.Surjective
        (QuotientGroup.mk : ↥R → ↥R ⧸ Subgroup.center ↥R)).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).mp this h
  have hlay := layers_gen hgen hCD hDc hne
  refine alphaVanishes_of_derived_quasisimple hZ hDc hDexp hq hZ3 ?_
  refine hlay.trans (Subgroup.closure_mono ?_)
  rintro x ⟨b, hb, hb1, hx⟩
  exact ⟨b, hb, hb1, by rwa [qRes_eq_derived_of_isQuasisimple (hq b hb hb1)]⟩

theorem alphaVanishes_of_derived_layers (hZ : Subgroup.center X = ⊥) {D : Subgroup X}
    (hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hDexp : ∀ x ∈ D, x ^ 3 = 1)
    (hq : ∀ b ∈ D, b ≠ 1 → CFSG.IsQuasisimple ↥(⁅Subgroup.centralizer ({b} : Set X),
      Subgroup.centralizer ({b} : Set X)⁆))
    (hZ3 : ∀ b ∈ D, b ≠ 1 → ∀ z ∈ Subgroup.center ↥(⁅Subgroup.centralizer ({b} : Set X),
      Subgroup.centralizer ({b} : Set X)⁆), ∃ k : ℕ, z ^ 3 ^ k = 1)
    (hlay : (⊤ : Subgroup X) ≤ Subgroup.closure {x : X | ∃ b ∈ D, b ≠ 1 ∧
      x ∈ ⁅Subgroup.centralizer ({b} : Set X), Subgroup.centralizer ({b} : Set X)⁆}) :
    AlphaVanishes X D := by
  refine alphaVanishes_of_derived_quasisimple hZ hDc hDexp hq hZ3 ?_
  refine hlay.trans (Subgroup.closure_mono ?_)
  rintro x ⟨b, hb, hb1, hx⟩
  exact ⟨b, hb, hb1, by rwa [qRes_eq_derived_of_isQuasisimple (hq b hb hb1)]⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK423
