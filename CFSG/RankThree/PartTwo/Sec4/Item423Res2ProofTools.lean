module

public import CFSG.RankThree.PartTwo.Sec4.Item423ResProofCensus

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Res423Two

@[expose] def AlphaVanishes (X : Type) [Group X] (D : Subgroup X) : Prop :=
  ∀ Y : Subgroup (MulAut X), (MulAut.conj : X →* MulAut X).range ≤ Y →
    thetaAlpha 3 ((D.map (MulAut.conj : X →* MulAut X)).subgroupOf Y) = ⊥

variable {X : Type} [Group X] [Finite X]

theorem census423_of_alphaVanishes
    (h : ∀ D : Subgroup X, Maximal (fun B : Subgroup X => CFSG.Assembly.IsElemAbelian 3 B) D →
      Nat.card D = 9 → AlphaVanishes X D) : Census423 X := by
  intro D hD hD9 Y hY hα
  exact absurd (h D hD hD9 Y hY) hα

omit [Finite X] in
theorem mulAut_congr_conj {X' : Type} [Group X'] (e : X ≃* X') (x : X) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem alphaVanishes_of_mulEquiv {X' : Type} [Group X'] (e : X ≃* X') {D : Subgroup X}
    (h : AlphaVanishes X' (D.map e.toMonoidHom)) : AlphaVanishes X D := by
  intro Y hY
  set Ψ : MulAut X ≃* MulAut X' := MulAut.congr e with hΨ
  have hY' : (MulAut.conj : X' →* MulAut X').range ≤ Y.map Ψ.toMonoidHom := by
    rintro _ ⟨x', rfl⟩
    refine ⟨MulAut.conj (e.symm x'), hY ⟨_, rfl⟩, ?_⟩
    change Ψ (MulAut.conj (e.symm x')) = MulAut.conj x'
    rw [hΨ, mulAut_congr_conj, MulEquiv.apply_symm_apply]
  have hD' : (D.map (MulAut.conj : X →* MulAut X)).map Ψ.toMonoidHom =
      (D.map e.toMonoidHom).map (MulAut.conj : X' →* MulAut X') := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun d => ?_
    change Ψ (MulAut.conj d) = MulAut.conj (e d)
    rw [hΨ, mulAut_congr_conj]
  have h1 := h _ hY'
  rw [← hD'] at h1
  by_contra hne
  exact (Sec13.thetaAlpha_subgroupOf_map_ne_bot_iff Ψ _ Y).mpr hne h1

theorem exists_map_conj_eq_of_card_nine {G : Type*} [Group G] [Finite G]
    (hG : (Nat.card G).factorization 3 = 2) {D E : Subgroup G} (hD : Nat.card D = 9)
    (hE : Nat.card E = 9) : ∃ g : G, D.map (MulAut.conj g).toMonoidHom = E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDp : IsPGroup 3 D := IsPGroup.of_card (n := 2) (by rw [hD]; norm_num)
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card (P₀ := E)
    (by rw [hE, hG]; norm_num) hDp
  refine ⟨g⁻¹, Subgroup.eq_of_le_of_card_ge (Item434AltPerm.map_conj_inv_le hg) ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hD, hE]

theorem factorization_card_alternatingGroup {n k m : ℕ} (hn : 2 ≤ n)
    (h : n.factorial / 2 = 3 ^ k * m) (hm : ¬ 3 ∣ m) :
    (Nat.card (alternatingGroup (Fin n))).factorization 3 = k := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [nat_card_alternatingGroup, Nat.card_fin, h,
    Item434AltPerm.factorization_three_pow_mul k hm]

theorem not_three_dvd_card_inSubgroup_theta {G : Type*} [Group G] [Finite G] (H : Subgroup G) :
    ¬ 3 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) H) := by
  rw [inSubgroup, Subgroup.card_map_of_injective H.subtype_injective]
  exact (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1

theorem isSolvable_inSubgroup_theta {G : Type*} [Group G] [Finite G] (H : Subgroup G) :
    Group.IsSolvable (inSubgroup (aschbacherSolvableCore 3) H) := by
  rw [inSubgroup]
  have := (solvable_prime_complement_core_characterization (H := H) Nat.prime_three).1
  exact Group.isSolvable_of_surjective
    (MonoidHom.subgroupMap_surjective H.subtype (aschbacherSolvableCore 3 H))

theorem inSubgroup_theta_le {G : Type*} [Group G] (H : Subgroup G) :
    inSubgroup (aschbacherSolvableCore 3) H ≤ H :=
  Subgroup.map_subtype_le _

theorem conj_mem_inSubgroup_theta' {G : Type*} [Group G] {H : Subgroup G} {l g : G}
    (hl : l ∈ H) (hg : g ∈ inSubgroup (aschbacherSolvableCore 3) H) :
    l * g * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) H := by
  obtain ⟨t, ht, rfl⟩ := hg
  exact ⟨⟨l, hl⟩ * t * (⟨l, hl⟩ : H)⁻¹,
    (inferInstance : (aschbacherSolvableCore 3 H).Normal).conj_mem t ht _, rfl⟩

theorem thetaAlpha_eq_bot_of_forall {G : Type*} [Group G] {B : Subgroup G} (hB : B ≠ ⊥)
    (h : ∀ b ∈ B, b ≠ 1 →
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set G)) = ⊥) :
    thetaAlpha 3 B = ⊥ := by
  obtain ⟨⟨b₀, hb₀⟩, hb₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB
  have hb₀1' : b₀ ≠ 1 := fun h => hb₀1 (Subtype.ext h)
  have hJ : thetaJ 3 B = ⊥ := by
    refine eq_bot_iff.mpr (iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_)
    rw [h b hb hb1, Subgroup.commutator_bot_left]
  have hT : thetaT 3 B = ⊥ := by
    refine eq_bot_iff.mpr ((iInf_le_of_le b₀ (iInf_le_of_le hb₀ (iInf_le_of_le hb₀1' le_rfl))).trans
      ?_)
    rw [h b₀ hb₀ hb₀1']
  rw [thetaAlpha, hJ, hT, sup_bot_eq]

omit [Finite X] in
theorem subgroupOf_ne_bot (hZ : Subgroup.center X = ⊥) {D : Subgroup X} (hD : D ≠ ⊥)
    {Y : Subgroup (MulAut X)} (hY : (MulAut.conj : X →* MulAut X).range ≤ Y) :
    (D.map (MulAut.conj : X →* MulAut X)).subgroupOf Y ≠ ⊥ := by
  obtain ⟨⟨d, hd⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
  intro hbot
  have hmem : (⟨MulAut.conj d, hY ⟨d, rfl⟩⟩ : Y) ∈
      (D.map (MulAut.conj : X →* MulAut X)).subgroupOf Y :=
    Subgroup.mem_subgroupOf.mpr ⟨d, hd, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  have h1 : MulAut.conj d = 1 := congrArg Subtype.val hmem
  apply hd1'
  have hc : d ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun σ : MulAut X => σ g) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * d = d * g * d⁻¹ * d := by rw [this]
      _ = d * g := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact hc

theorem alphaVanishes_of_noSignalizer (hZ : Subgroup.center X = ⊥) {D : Subgroup X}
    (hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hD : D ≠ ⊥)
    (h : ∀ Q : Subgroup (MulAut X), ¬ 3 ∣ Nat.card Q →
      D.map (MulAut.conj : X →* MulAut X) ≤ Subgroup.normalizer (Q : Set (MulAut X)) → Q = ⊥) :
    AlphaVanishes X D := by
  intro Y hY
  refine thetaAlpha_eq_bot_of_forall (subgroupOf_ne_bot hZ hD hY) fun b hb hb1 => ?_
  obtain ⟨d', hd', hbd'⟩ := Subgroup.mem_subgroupOf.mp hb
  set Q := inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set Y)) with hQ
  have hQ3 : ¬ 3 ∣ Nat.card (Q.map Y.subtype) := by
    rw [Subgroup.card_map_of_injective Y.subtype_injective]
    exact not_three_dvd_card_inSubgroup_theta _
  have hN : D.map (MulAut.conj : X →* MulAut X) ≤
      Subgroup.normalizer ((Q.map Y.subtype : Subgroup (MulAut X)) : Set (MulAut X)) := by
    rintro _ ⟨d, hd, rfl⟩
    have hdY : MulAut.conj d ∈ Y := hY ⟨d, rfl⟩
    set γ : Y := ⟨MulAut.conj d, hdY⟩ with hγ
    have hγb : γ ∈ Subgroup.centralizer ({b} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      change MulAut.conj d * (b : MulAut X) = (b : MulAut X) * MulAut.conj d
      rw [← hbd']
      rw [← map_mul, ← map_mul, hDc d hd d' hd']
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨q, hq, rfl⟩ := hx
    exact ⟨γ * q * γ⁻¹, conj_mem_inSubgroup_theta' hγb hq, rfl⟩
  have h1 := h _ hQ3 hN
  exact (Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective).mp h1

omit [Finite X] in
theorem conj_injective_of_center (hZ : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [← hZ, Subgroup.mem_center_iff]
  intro g
  have := congrArg (fun σ : MulAut X => σ g) hx
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  calc g * x = x * g * x⁻¹ * x := by rw [this]
    _ = x * g := by group

omit [Finite X] in
theorem mulAut_mul_conj_mul_inv (σ : MulAut X) (x : X) :
    σ * MulAut.conj x * σ⁻¹ = MulAut.conj (σ x) := by
  ext y
  simp [MulAut.conj_apply, MulAut.mul_apply]

theorem fix_of_mem_theta (hZ : Subgroup.center X = ⊥) {Y : Subgroup (MulAut X)}
    (hY : (MulAut.conj : X →* MulAut X).range ≤ Y) {b₀ : X}
    (hθ : aschbacherSolvableCore 3 (Subgroup.centralizer ({b₀} : Set X)) = ⊥) {b : Y}
    (hb : (b : MulAut X) = MulAut.conj b₀) {q : Y}
    (hq : q ∈ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set Y)))
    {c : X} (hc : c ∈ Subgroup.centralizer ({b₀} : Set X)) : (q : MulAut X) c = c := by
  have hinj := conj_injective_of_center hZ
  set C := Subgroup.centralizer ({b} : Set Y) with hC
  set Q := inSubgroup (aschbacherSolvableCore 3) C with hQ
  have hγ : ∀ x ∈ Subgroup.centralizer ({b₀} : Set X), (⟨MulAut.conj x, hY ⟨x, rfl⟩⟩ : Y) ∈ C := by
    intro x hx
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    change MulAut.conj x * (b : MulAut X) = (b : MulAut X) * MulAut.conj x
    rw [hb, ← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hx]
  set W : Subgroup X := ((Q.map Y.subtype).comap (MulAut.conj : X →* MulAut X)) ⊓
    Subgroup.centralizer ({b₀} : Set X) with hW
  have hWbot : W = ⊥ := by
    set C₀ := Subgroup.centralizer ({b₀} : Set X) with hC₀
    have hWC : W ≤ C₀ := inf_le_right
    set N := W.subgroupOf C₀ with hN
    have hNn : N.Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨hn1, hn2⟩ := hn
      refine ⟨?_, ?_⟩
      · obtain ⟨k, hk, hkn⟩ := hn1
        have hgC := hγ g g.2
        refine ⟨⟨MulAut.conj (g : X), hY ⟨_, rfl⟩⟩ * k * (⟨MulAut.conj (g : X), hY ⟨_, rfl⟩⟩ : Y)⁻¹,
          conj_mem_inSubgroup_theta' hgC hk, ?_⟩
        · simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype]
          rw [show ((k : MulAut X)) = MulAut.conj ((n : C₀) : X) from hkn]
          simp only [map_mul, map_inv]
      · exact (g * n * g⁻¹).2
    have hNs : Group.IsSolvable N := by
      have hQs : Group.IsSolvable (Q.map Y.subtype) := by
        have := isSolvable_inSubgroup_theta C
        exact Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective Y.subtype Q)
      let f : N →* (Q.map Y.subtype) :=
        { toFun := fun n => ⟨MulAut.conj ((n : C₀) : X), (Subgroup.mem_subgroupOf.mp n.2).1⟩
          map_one' := by ext; simp
          map_mul' := fun x y => by ext; simp }
      have hf : Function.Injective f := by
        intro x y hxy
        have h1 : MulAut.conj ((x : C₀) : X) = MulAut.conj ((y : C₀) : X) :=
          congrArg Subtype.val hxy
        exact Subtype.ext (Subtype.ext (hinj h1))
      exact Group.isSolvable_of_isSolvable_injective hf
    have hN3 : ¬ 3 ∣ Nat.card N := by
      intro h3
      apply not_three_dvd_card_inSubgroup_theta C
      have hcard : Nat.card N ∣ Nat.card (Q.map Y.subtype) := by
        let f : N →* (Q.map Y.subtype) :=
          { toFun := fun n => ⟨MulAut.conj ((n : C₀) : X), (Subgroup.mem_subgroupOf.mp n.2).1⟩
            map_one' := by ext; simp
            map_mul' := fun x y => by ext; simp }
        have hf : Function.Injective f := by
          intro x y hxy
          have h1 : MulAut.conj ((x : C₀) : X) = MulAut.conj ((y : C₀) : X) :=
            congrArg Subtype.val hxy
          exact Subtype.ext (Subtype.ext (hinj h1))
        exact Subgroup.card_dvd_of_injective f hf
      rw [Subgroup.card_map_of_injective Y.subtype_injective] at hcard
      exact h3.trans hcard
    have hle := (solvable_prime_complement_core_characterization (H := C₀)
      Nat.prime_three).2.2.2.1 N hNn hNs hN3
    rw [hθ, le_bot_iff] at hle
    rw [eq_bot_iff]
    intro w hw
    have hw' : (⟨w, hWC hw⟩ : C₀) ∈ N := Subgroup.mem_subgroupOf.mpr hw
    rw [hle, Subgroup.mem_bot] at hw'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hw')
  have hqC : q ∈ C := inSubgroup_theta_le C hq
  have hqb₀ : (q : MulAut X) b₀ = b₀ := by
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hqC
    have h2 : (q : MulAut X) * (b : MulAut X) = (b : MulAut X) * (q : MulAut X) :=
      congrArg Subtype.val h1
    rw [hb] at h2
    have h3 : MulAut.conj ((q : MulAut X) b₀) = MulAut.conj b₀ := by
      rw [← mulAut_mul_conj_mul_inv, h2, mul_inv_cancel_right]
    exact hinj h3
  set w := (q : MulAut X) c * c⁻¹ with hw
  have hwW : w ∈ W := by
    refine ⟨?_, ?_⟩
    · set γ : Y := ⟨MulAut.conj c, hY ⟨c, rfl⟩⟩ with hγdef
      have hγC : γ ∈ C := hγ c hc
      refine ⟨q * (γ * q⁻¹ * γ⁻¹), mul_mem hq (conj_mem_inSubgroup_theta' hγC (inv_mem hq)), ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
      change (q : MulAut X) * (MulAut.conj c * (q : MulAut X)⁻¹ * (MulAut.conj c)⁻¹) =
        MulAut.conj w
      rw [hw, map_mul, map_inv, ← mulAut_mul_conj_mul_inv]
      group
    · rw [Subgroup.mem_centralizer_singleton_iff] at hc
      show w ∈ Subgroup.centralizer ({b₀} : Set X)
      rw [Subgroup.mem_centralizer_singleton_iff, hw]
      have hqc : (q : MulAut X) (c * b₀) = (q : MulAut X) (b₀ * c) := by rw [hc]
      rw [map_mul, map_mul, hqb₀] at hqc
      have hc' : c⁻¹ * b₀ = b₀ * c⁻¹ := by
        calc c⁻¹ * b₀ = c⁻¹ * (b₀ * c) * c⁻¹ := by group
          _ = c⁻¹ * (c * b₀) * c⁻¹ := by rw [hc]
          _ = b₀ * c⁻¹ := by group
      calc (q : MulAut X) c * c⁻¹ * b₀ = (q : MulAut X) c * (c⁻¹ * b₀) := by rw [mul_assoc]
        _ = (q : MulAut X) c * (b₀ * c⁻¹) := by rw [hc']
        _ = ((q : MulAut X) c * b₀) * c⁻¹ := by rw [mul_assoc]
        _ = (b₀ * (q : MulAut X) c) * c⁻¹ := by rw [hqc]
        _ = b₀ * ((q : MulAut X) c * c⁻¹) := by rw [mul_assoc]
  rw [hWbot, Subgroup.mem_bot, hw, mul_inv_eq_one] at hwW
  exact hwW

theorem alphaVanishes_of_core (hZ : Subgroup.center X = ⊥) {D : Subgroup X}
    (hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a)
    (hθ : ∀ b ∈ D, b ≠ 1 → aschbacherSolvableCore 3 (Subgroup.centralizer ({b} : Set X)) = ⊥)
    (hgen : (⊤ : Subgroup X) ≤ Subgroup.closure {x : X | ∃ b ∈ D, b ≠ 1 ∧ x * b = b * x}) :
    AlphaVanishes X D := by
  intro Y hY
  have hinj := conj_injective_of_center hZ
  set B := (D.map (MulAut.conj : X →* MulAut X)).subgroupOf Y with hB
  have hfix : ∀ b ∈ B, b ≠ 1 → ∃ b₀ ∈ D, b₀ ≠ 1 ∧ (b : MulAut X) = MulAut.conj b₀ ∧
      ∀ q ∈ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set Y)),
        ∀ c ∈ Subgroup.centralizer ({b₀} : Set X), (q : MulAut X) c = c := by
    intro b hb hb1
    obtain ⟨b₀, hb₀, hbb₀⟩ := Subgroup.mem_subgroupOf.mp hb
    have hb₀1 : b₀ ≠ 1 := by
      rintro rfl
      apply hb1
      apply Subtype.ext
      rw [← hbb₀]
      simp
    exact ⟨b₀, hb₀, hb₀1, hbb₀.symm, fun q hq c hc =>
      fix_of_mem_theta hZ hY (hθ b₀ hb₀ hb₀1) hbb₀.symm hq hc⟩
  have hJ : thetaJ 3 B = ⊥ := by
    refine eq_bot_iff.mpr (iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_)
    obtain ⟨b₀, hb₀, -, -, hq⟩ := hfix b hb hb1
    rw [Subgroup.commutator_le]
    intro q hq' d hd
    obtain ⟨d₀, hd₀, hdd₀⟩ := Subgroup.mem_subgroupOf.mp hd
    have hd₀C : d₀ ∈ Subgroup.centralizer ({b₀} : Set X) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hDc d₀ hd₀ b₀ hb₀)
    have hqd : (q : MulAut X) d₀ = d₀ := hq q hq' d₀ hd₀C
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hdd₀]
    have h1 := mulAut_mul_conj_mul_inv (q : MulAut X) d₀
    rw [hqd] at h1
    calc (q : MulAut X) * MulAut.conj d₀ =
        (q : MulAut X) * MulAut.conj d₀ * (q : MulAut X)⁻¹ * (q : MulAut X) := by group
      _ = MulAut.conj d₀ * (q : MulAut X) := by rw [h1]
  have hT : thetaT 3 B = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    rw [Subgroup.mem_bot]
    have htfix : ∀ x : X, (∃ b ∈ D, b ≠ 1 ∧ x * b = b * x) → (t : MulAut X) x = x := by
      rintro x ⟨b₀, hb₀, hb₀1, hxb₀⟩
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
      exact fix_of_mem_theta hZ hY (hθ b₀ hb₀ hb₀1) rfl htb
        (Subgroup.mem_centralizer_singleton_iff.mpr hxb₀)
    have hle : Subgroup.closure {x : X | ∃ b ∈ D, b ≠ 1 ∧ x * b = b * x} ≤
        (t : MulAut X).toMonoidHom.eqLocus (MonoidHom.id X) := by
      rw [Subgroup.closure_le]
      intro x hx
      exact htfix x hx
    apply Subtype.ext
    refine MulEquiv.ext fun x => ?_
    exact hle (hgen (Subgroup.mem_top x))
  rw [thetaAlpha, hJ, hT, sup_bot_eq]

end Res423Two

end CFSG.RankThree.PartTwo.Sec4
