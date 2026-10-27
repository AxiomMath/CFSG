module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOmComp
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordShapeAlign

public section

namespace CFSG.StandardType

namespace CoordOm

open Polynomial Module Multiplicative CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2 (orthDerived)

local notation "bComp" => CFSG.RankThree.PartOne.KCOrthogonal.blockComponent
local notation "bCompApply" => CFSG.RankThree.PartOne.KCOrthogonal.blockComponent_apply_of_mem

theorem exists_unit_forall {p r : ℕ} [Fact p.Prime] {O : Subgroup (ZMod p)ˣ}
    (T : AddSubgroup (Fin r → ZMod p)) {i i' : Fin r}
    (h : ∀ t ∈ T, ∃ u ∈ O, t i' = (u : ZMod p) * t i) :
    ∃ u ∈ O, ∀ t ∈ T, t i' = (u : ZMod p) * t i := by
  classical
  by_cases h0 : ∀ t ∈ T, t i = 0
  · refine ⟨1, O.one_mem, fun t ht => ?_⟩
    obtain ⟨u, -, hu⟩ := h t ht
    rw [hu, h0 t ht, mul_zero, mul_zero]
  push Not at h0
  obtain ⟨t₀, ht₀, ha₀⟩ := h0
  obtain ⟨u₀, hu₀, hu₀t⟩ := h t₀ ht₀
  refine ⟨u₀, hu₀, fun t₁ ht₁ => ?_⟩
  by_contra hne
  have hmem : ∀ c : ZMod p, t₁ + c • t₀ ∈ T := fun c =>
    T.add_mem ht₁ (by
      have : c • t₀ = c.val • t₀ := by
        funext m
        rw [Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_zmod_val, smul_eq_mul]
      rw [this]
      exact T.nsmul_mem ht₀ _)
  choose u hu hut using fun c => h _ (hmem c)
  have hinj : Function.Injective u := by
    intro c c' hcc
    have e1 := hut c
    have e2 := hut c'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu₀t] at e1 e2
    rw [hcc] at e1
    have hdiff : (u c' : ZMod p) ≠ u₀ := by
      intro he
      apply hne
      rw [he] at e2
      linear_combination e2
    have h3 : (c - c') * t₀ i * ((u c' : ZMod p) - u₀) = 0 := by
      linear_combination e2 - e1
    rcases mul_eq_zero.mp h3 with h4 | h4
    · rcases mul_eq_zero.mp h4 with h5 | h5
      · exact sub_eq_zero.mp h5
      · exact absurd h5 ha₀
    · exact absurd (sub_eq_zero.mp h4) hdiff
  have hcard := Nat.card_le_card_of_injective u hinj
  rw [Nat.card_zmod, Nat.card_eq_fintype_card, ZMod.card_units] at hcard
  have := (Fact.out : p.Prime).one_lt
  omega

section Block

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem blockComponent_comm (hx : OddOrderIsometry Q p x)
    (g : ↥(Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)))) (h : K[X]) {y : V ≃ₗ[K] V}
    (hyc : y ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V))) (hgy : g.1 * y = y * g.1) :
    (bComp hx g h).1 * y = y * (bComp hx g h).1 := by
  classical
  apply LinearEquiv.toLinearMap_injective
  refine ext_primaryComponent hx.squarefree_minpoly fun a ha v hv => ?_
  show (bComp hx g h).1 (y v) = y ((bComp hx g h).1 v)
  have hyv : y v ∈ primaryComponent x.toLinearMap a :=
    apply_mem_primaryComponent_of_mem_centralizer hyc hv
  rw [bCompApply hx g h ha hyv, bCompApply hx g h ha hv]
  split_ifs
  · show (g.1 * y) v = (y * g.1) v
    rw [hgy]
  · rfl

variable [Finite K]

theorem exists_le_supportedBlock_of_comm (hx : OddOrderIsometry Q p x)
    {E : Subgroup (V ≃ₗ[K] V)} (hxE : x ∈ E) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    {J : Subgroup (V ≃ₗ[K] V)}
    (hJ : CFSG.Assembly.IsComponentOf J
      (orthDerived Q ⊓ Subgroup.centralizer (E : Set (V ≃ₗ[K] V)))) :
    ∃ h ∈ primaryFactors x.toLinearMap, J ≤ supportedBlock Q x h := by
  classical
  have : Finite (V ≃ₗ[K] V) := by
    have : Finite V := Module.finite_of_finite K
    exact Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
      fun _ _ he => LinearEquiv.ext (congrFun he)
  set H := TauCeti.QuadraticMap.orthogonalGroup Q ⊓ Subgroup.centralizer (E : Set (V ≃ₗ[K] V))
    with hH
  have hJH : CFSG.Assembly.IsComponentOf J H := by
    obtain ⟨hle, hsn, hq⟩ := hJ
    have hle' : orthDerived Q ⊓ Subgroup.centralizer (E : Set (V ≃ₗ[K] V)) ≤ H :=
      inf_le_inf_right _ orthDerived_le_orthogonalGroup
    refine ⟨hle.trans hle', ggIsSubnormal_trans hsn (LayerCores.ggSubnormal_of_normal hle' ?_), hq⟩
    intro u hu s hs
    exact Subgroup.mem_inf.mpr ⟨LayerPDiv.conj_mem_commutator_self _ (Subgroup.mem_inf.mp hu).1
      (Subgroup.mem_inf.mp hs).1, Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.mem_inf.mp hu).2 (Subgroup.mem_inf.mp hs).2) (Subgroup.inv_mem _
        (Subgroup.mem_inf.mp hu).2)⟩
  have hHx : ∀ g ∈ H, g ∈ isometryCentralizer Q x := fun g hg =>
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hg).1, Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hg).2 x hxE)).symm⟩
  by_contra hno
  push Not at hno
  have hcent : ∀ a ∈ primaryFactors x.toLinearMap, ∀ c ∈ supportedBlock Q x a ⊓
      Subgroup.centralizer (E : Set (V ≃ₗ[K] V)), ∀ j ∈ J, c * j = j * c := by
    intro a ha
    set N := supportedBlock Q x a ⊓ Subgroup.centralizer (E : Set (V ≃ₗ[K] V)) with hN
    have hNH : N ≤ H := inf_le_inf_right _ fun g hg =>
      (Subgroup.mem_inf.mp (mem_supportedBlock.mp hg).1).1
    have hNn : (N.subgroupOf H).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hNH]
      intro c g hc hg
      exact Subgroup.mem_inf.mpr ⟨conj_mem_supportedBlock (hHx g hg) (Subgroup.mem_inf.mp hc).1,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_inf.mp hg).2
          (Subgroup.mem_inf.mp hc).2) (Subgroup.inv_mem _ (Subgroup.mem_inf.mp hg).2)⟩
    rcases CoordSL.le_or_commutator_eq_bot_of_normal hJH hNH hNn with h1 | h1
    · exact absurd (h1.trans inf_le_left) (hno a ha)
    · intro c hc j hj
      have h2 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1 hj
      exact (Subgroup.mem_centralizer_iff.mp h2 c hc)
  apply CFSG.LocalAnalysis.ComponentInitial.not_le_centralizer_self_of_isQuasisimple hJH.2.2
  intro j hj
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have hgH : g ∈ H := hJH.1 hg
  have hjH : j ∈ H := hJH.1 hj
  have hgc : g ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) :=
    (Subgroup.mem_inf.mp (hHx g hgH)).2
  have hjc : j ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) :=
    (Subgroup.mem_inf.mp (hHx j hjH)).2
  symm
  apply LinearEquiv.toLinearMap_injective
  refine ext_primaryComponent hx.squarefree_minpoly fun a ha v hv => ?_
  show j (g v) = g (j v)
  set c := (bComp hx ⟨j, hjc⟩ a).1 with hc
  have hcB : c ∈ supportedBlock Q x a := hx.blockComponent_mem (hHx j hjH) ha
  have hcE : c ∈ Subgroup.centralizer (E : Set (V ≃ₗ[K] V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzc : z ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hEc z hz x hxE)
    have hjz : j * z = z * j :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hjH).2 z hz).symm
    exact (blockComponent_comm hx ⟨j, hjc⟩ a hzc hjz).symm
  have hcg := hcent a ha c (Subgroup.mem_inf.mpr ⟨hcB, hcE⟩) g hg
  have hva : v ∈ orbitSpace x.toLinearMap a := Submodule.mem_sup_left hv
  have hgv : g v ∈ orbitSpace x.toLinearMap a := mem_orbitSpace_of_apply hgc hva
  rw [← blockComponent_apply_orbit hx ⟨j, hjc⟩ ha hgv,
    ← blockComponent_apply_orbit hx ⟨j, hjc⟩ ha hva]
  show (c * g) v = (g * c) v
  rw [hcg]

end Block

section Count

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

theorem card_ge_of_four [Fact p.Prime] (F : SevOm.Frame Q p A r) {H : Subgroup (V ≃ₗ[K] V)}
    [Finite H] {v₁ v₂ v₃ v₄ : Fin r → ZMod p} (h₁ : F.ι (ofAdd v₁) ∈ H)
    (h₂ : F.ι (ofAdd v₂) ∈ H) (h₃ : F.ι (ofAdd v₃) ∈ H) (h₄ : F.ι (ofAdd v₄) ∈ H)
    {k₁ k₂ k₃ k₄ : Fin r} (hv₁ : v₁ k₁ ≠ 0) (hv₂ : v₂ k₂ ≠ 0) (hv₃ : v₃ k₃ ≠ 0) (hv₄ : v₄ k₄ ≠ 0)
    (h12 : v₁ k₂ = 0) (h13 : v₁ k₃ = 0) (h14 : v₁ k₄ = 0) (h23 : v₂ k₃ = 0) (h24 : v₂ k₄ = 0)
    (h34 : v₃ k₄ = 0) : p ^ 4 ≤ Nat.card H := by
  have hmem : ∀ a : ZMod p × ZMod p × ZMod p × ZMod p,
      F.ι (ofAdd (a.1 • v₁ + a.2.1 • v₂ + a.2.2.1 • v₃ + a.2.2.2 • v₄)) ∈ H := by
    intro a
    rw [ofAdd_add, ofAdd_add, ofAdd_add, map_mul, map_mul, map_mul]
    exact H.mul_mem (H.mul_mem (H.mul_mem (StepTwoToral.ofAdd_smul_mem h₁ _)
      (StepTwoToral.ofAdd_smul_mem h₂ _)) (StepTwoToral.ofAdd_smul_mem h₃ _))
      (StepTwoToral.ofAdd_smul_mem h₄ _)
  have hinj : Function.Injective
      fun a : ZMod p × ZMod p × ZMod p × ZMod p => (⟨_, hmem a⟩ : H) := by
    intro a b hab
    have h0 : a.1 • v₁ + a.2.1 • v₂ + a.2.2.1 • v₃ + a.2.2.2 • v₄ =
        b.1 • v₁ + b.2.1 • v₂ + b.2.2.1 • v₃ + b.2.2.2 • v₄ :=
      ofAdd.injective (F.inj (congrArg Subtype.val hab))
    have e4 := congrFun h0 k₄
    have e3 := congrFun h0 k₃
    have e2 := congrFun h0 k₂
    have e1 := congrFun h0 k₁
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h14, h24, h34, mul_zero,
      zero_add] at e4
    have hd : a.2.2.2 = b.2.2.2 := mul_right_cancel₀ hv₄ e4
    rw [hd] at e3
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h13, h23, mul_zero, zero_add,
      add_left_inj] at e3
    have hc : a.2.2.1 = b.2.2.1 := mul_right_cancel₀ hv₃ e3
    rw [hc, hd] at e2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h12, mul_zero, zero_add,
      add_left_inj] at e2
    have hb : a.2.1 = b.2.1 := mul_right_cancel₀ hv₂ e2
    rw [hb, hc, hd] at e1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_left_inj] at e1
    have ha : a.1 = b.1 := mul_right_cancel₀ hv₁ e1
    exact Prod.ext ha (Prod.ext hb (Prod.ext hc hd))
  have hcard : Nat.card (ZMod p × ZMod p × ZMod p × ZMod p) = p ^ 4 := by
    rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_zmod]
    ring
  have h := Nat.card_le_card_of_injective _ hinj
  rwa [hcard] at h

end Count

end CoordOm

section Shape

open Polynomial Module Multiplicative CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CoordOm

theorem ggOmFrameShapeInput_holds : GGOmFrameShapeInput := by
  intro K _ _ _ V _ _ _ p _ hp2 Q hQ hT A hAΩ hmax r F hr4 hF E J hEA hJ hcardJ
  classical
  have hp : p.Prime := Fact.out
  have : Finite (V ≃ₗ[K] V) := by
    have : Finite V := Module.finite_of_finite K
    exact Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
      fun _ _ he => LinearEquiv.ext (congrFun he)
  set O := CoordSpNs.galSigns p (Nat.card K) with hOdef
  set C := A ⊓ Subgroup.centralizer (J : Set (V ≃ₗ[K] V)) with hCdef
  set T : AddSubgroup (Fin r → ZMod p) :=
    { carrier := {t | F.ι (ofAdd t) ∈ E}
      add_mem' := fun {a b} ha hb => by
        show F.ι (ofAdd (a + b)) ∈ E
        rw [ofAdd_add, map_mul]
        exact E.mul_mem ha hb
      zero_mem' := by
        show F.ι (ofAdd 0) ∈ E
        rw [ofAdd_zero, map_one]
        exact E.one_mem
      neg_mem' := fun {a} ha => by
        show F.ι (ofAdd (-a)) ∈ E
        rw [ofAdd_neg, map_inv]
        exact E.inv_mem ha } with hTdef
  have hmemT : ∀ t, t ∈ T ↔ F.ι (ofAdd t) ∈ E := fun t => Iff.rfl
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    frame_comm F (hEA ha) (hEA hb)
  have hEC : ∀ e ∈ E, e ∈ C := fun e he => Subgroup.mem_inf.mpr ⟨hEA he,
    Subgroup.mem_centralizer_iff.mpr fun g hg =>
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hJ.1 hg)).2 e he).symm⟩
  set inY : Fin r → Prop := fun i => F.ι (ofAdd (Pi.single i 1)) ∈ C with hinY
  have hYmem : ∀ s : Fin r → ZMod p, (∀ i, s i ≠ 0 → inY i) → F.ι (ofAdd s) ∈ C := by
    intro s hs
    have hsum : s = ∑ i, s i • (Pi.single i (1 : ZMod p) : Fin r → ZMod p) := by
      funext m
      rw [Finset.sum_apply, Finset.sum_eq_single m]
      · simp
      · intro b _ hbm
        simp [Pi.single_eq_of_ne' hbm]
      · intro hm
        exact absurd (Finset.mem_univ m) hm
    rw [hsum]
    refine ofAdd_sum_mem _ _ fun i _ => ?_
    by_cases hi : s i = 0
    · rw [hi, zero_smul, ofAdd_zero, map_one]
      exact C.one_mem
    · exact StepTwoToral.ofAdd_smul_mem (hs i hi) (s i)
  have hlt : ∀ {n : ℕ}, p ^ 4 ≤ n → n ≤ p ^ 3 → False := fun h1 h2 =>
    absurd (h1.trans h2) (not_le.mpr (Nat.pow_lt_pow_right hp.one_lt (by norm_num)))
  by_cases hX0 : ∀ t ∈ T, ∀ i, ¬ inY i → t i = 0
  ·
    by_cases hXne : ∃ k, ¬ inY k
    · obtain ⟨k, hk⟩ := hXne
      exact Or.inl ⟨k, fun s hs => hX0 s ((hmemT s).mpr hs) k hk⟩
    · push Not at hXne
      exfalso
      have hk : ∀ a : ℕ, a < 4 → a < r := fun a ha => by omega
      exact hlt (card_ge_of_four F (hXne ⟨0, hk 0 (by norm_num)⟩) (hXne ⟨1, hk 1 (by norm_num)⟩)
        (hXne ⟨2, hk 2 (by norm_num)⟩) (hXne ⟨3, hk 3 (by norm_num)⟩)
        (k₁ := ⟨0, hk 0 (by norm_num)⟩) (k₂ := ⟨1, hk 1 (by norm_num)⟩)
        (k₃ := ⟨2, hk 2 (by norm_num)⟩) (k₄ := ⟨3, hk 3 (by norm_num)⟩)
        (by simp) (by simp) (by simp) (by simp) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
        (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
        (by simp [Fin.ext_iff])) hcardJ
  push Not at hX0
  obtain ⟨t₀, ht₀, i₀, hi₀Y, hti₀⟩ := hX0
  set t₀X : Fin r → ZMod p := fun i => if inY i then 0 else t₀ i with ht₀X
  have ht₀XC : F.ι (ofAdd t₀X) ∈ C := by
    have h1 : t₀X = t₀ - (t₀ - t₀X) := by abel
    rw [h1, ofAdd_sub, _root_.map_div]
    refine C.div_mem (hEC _ ht₀) (hYmem _ fun i hi => ?_)
    by_contra hiY
    apply hi
    simp only [ht₀X, Pi.sub_apply, hiY, ite_false, sub_self]
  obtain ⟨j, j', hjj⟩ : ∃ j j' : Fin r, ∀ i, inY i → i = j ∨ i = j' := by
    by_contra hno
    push Not at hno
    obtain ⟨y₁, hy₁, -, -⟩ := hno i₀ i₀
    obtain ⟨y₂, hy₂, hy₂₁, -⟩ := hno y₁ y₁
    obtain ⟨y₃, hy₃, hy₃₁, hy₃₂⟩ := hno y₁ y₂
    have hne : ∀ y, inY y → y ≠ i₀ := fun y hy e => hi₀Y (e ▸ hy)
    exact hlt (card_ge_of_four F hy₁ hy₂ hy₃ ht₀XC (k₁ := y₁) (k₂ := y₂) (k₃ := y₃) (k₄ := i₀)
      (by simp) (by simp) (by simp) (by simp [ht₀X, hi₀Y, hti₀]) (by simp [hy₂₁])
      (by simp [hy₃₁]) (by simp [Ne.symm (hne y₁ hy₁)]) (by simp [hy₃₂])
      (by simp [Ne.symm (hne y₂ hy₂)]) (by simp [Ne.symm (hne y₃ hy₃)])) hcardJ
  have hpair : ∀ i, ¬ inY i → ∀ t ∈ T, ∃ u ∈ O, t i = (u : ZMod p) * t i₀ := by
    intro i hiY t ht
    have hx : OddOrderIsometry Q p (F.ι (ofAdd t)) := F.oddOrderIsometry hQ hp2 hp hAΩ (ofAdd t)
    obtain ⟨h, hh, hJB⟩ := exists_le_supportedBlock_of_comm hx ht hEc hJ
    have horb : ∀ m, ¬ inY m → F.U m ≤ orbitSpace (F.ι (ofAdd t)).toLinearMap h := by
      intro m hmY
      rcases frame_piece_dichotomy hQ hT hp hp2 F hAΩ hmax (ofAdd t) hh m with h1 | h1
      · exact h1
      · exfalso
        apply hmY
        refine Subgroup.mem_inf.mpr ⟨F.mem _, Subgroup.mem_centralizer_iff.mpr fun g hg =>
          commute_of_triv hx hh (hJB hg) (Subgroup.mem_centralizer_singleton_iff.mpr
            (frame_comm F (F.mem _) (F.mem _))) (frame_triv_orbit F hx hh fun m' hm' => ?_)⟩
        have : m' = m := by
          by_contra hne
          exact hm' (by rw [toAdd_ofAdd, Pi.single_eq_of_ne hne])
        rw [this]
        exact h1
    by_cases hX : h = X - 1
    ·
      have hz : ∀ m, ¬ inY m → t m = 0 := by
        intro m hmY
        by_contra h0
        obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp (F.ne_bot m)
        have h1 := horb m hmY hu
        rw [hX, orbitSpace_X_sub_one] at h1
        exact hu0 (F.fpf (ofAdd t) m h0 u hu (mem_fixedSpace.mp h1))
      exact ⟨1, O.one_mem, by rw [hz i hiY, hz i₀ hi₀Y, mul_zero]⟩
    · obtain ⟨w, -, hw⟩ := hF (Equiv.swap i₀ i) 1 (fun _ => O.one_mem) (by simp)
      refine frame_align hQ hp hp2 hAΩ F t hh hX (horb i₀ hi₀Y) (horb i hiY) (w := w)
        fun s => ?_
      rw [hw s]
      simp only [Pi.one_apply, Units.val_one, one_mul]
  have hjoint : ∀ i, ∃ u ∈ O, ¬ inY i → ∀ t ∈ T, t i = (u : ZMod p) * t i₀ := by
    intro i
    by_cases hiY : inY i
    · exact ⟨1, O.one_mem, fun h => absurd hiY h⟩
    · obtain ⟨u, hu, hut⟩ := exists_unit_forall T (hpair i hiY)
      exact ⟨u, hu, fun _ => hut⟩
  choose ε hεO hε using hjoint
  refine Or.inr ⟨j, j', ε, hεO, fun s hs => ⟨s i₀, fun i hij hij' => ?_⟩⟩
  have hiY : ¬ inY i := fun h => by
    rcases hjj i h with e | e
    · exact hij e
    · exact hij' e
  exact hε i hiY s hs

end Shape

theorem ggOmCoordInput_of_move_splitFour (hmove : GGOmFrameMoveInput)
    (hsf : GGOmSplitFourCentInput) : GGOmCoordInput :=
  ggOmCoordInput_of_inputs hmove ggOmFrameShapeInput_holds hsf

section Certified

theorem ggStepTwoCoordModelOn_POmegaPlus_of_move_splitFour (hmove : GGOmFrameMoveInput)
    (hsf : GGOmSplitFourCentInput) : GGStepTwoCoordModelOn .POmegaPlus :=
  ggStepTwoCoordModelOn_POmegaPlus_of_coord (ggOmCoordInput_of_move_splitFour hmove hsf)

theorem ggStepTwoCoordModelOn_POmegaMinus_of_move_splitFour (hmove : GGOmFrameMoveInput)
    (hsf : GGOmSplitFourCentInput) : GGStepTwoCoordModelOn .POmegaMinus :=
  ggStepTwoCoordModelOn_POmegaMinus_of_coord (ggOmCoordInput_of_move_splitFour hmove hsf)

theorem ggStepTwoToralWitnessOn_POmegaPlus_of_move_splitFour (hmove : GGOmFrameMoveInput)
    (hsf : GGOmSplitFourCentInput) : GGStepTwoToralWitnessOn .POmegaPlus :=
  ggStepTwoToralWitnessOn_of_coordModel
    (ggStepTwoCoordModelOn_POmegaPlus_of_move_splitFour hmove hsf)

theorem ggStepTwoToralWitnessOn_POmegaMinus_of_move_splitFour (hmove : GGOmFrameMoveInput)
    (hsf : GGOmSplitFourCentInput) : GGStepTwoToralWitnessOn .POmegaMinus :=
  ggStepTwoToralWitnessOn_of_coordModel
    (ggStepTwoCoordModelOn_POmegaMinus_of_move_splitFour hmove hsf)

end Certified

end CFSG.StandardType
