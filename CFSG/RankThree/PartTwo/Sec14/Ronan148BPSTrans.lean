module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSInsp

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

open CFSG CFSG.GH74.GLS CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec13
open scoped commutatorElement

variable {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G']

structure SigGenHyp (P K Q D : Subgroup G) : Prop where
  perf : Group.IsPerfect K
  quasi : IsQuasisimple (↥K ⧸ aschbacherSolvableCore 3 ↥K)
  three : 3 ∣ Nat.card K
  normK : P ≤ Subgroup.normalizer (K : Set G)
  faith : ∀ p ∈ P, (∀ k ∈ K, p * k * p⁻¹ * k⁻¹ ∈ (aschbacherSolvableCore 3 ↥K).map K.subtype) →
    p = 1
  hyp : IsHyperplane P D
  cent : Q ≤ Subgroup.centralizer (D : Set G)
  inv : Q ∈ invariantPiSubgroups ⊤ P (piCompl 3)
  comm : Q = ⁅Q, P⁆
  normQ : Q ≤ Subgroup.normalizer (K : Set G)
  nontriv : ¬ ⁅K, Q⁆ ≤ (aschbacherSolvableCore 3 ↥K).map K.subtype

@[expose] def SigGenConcl (P K : Subgroup G) : Prop :=
  K ≤ sSup {V : Subgroup G | V ≤ K ∧ V ∈ invariantPiSubgroups ⊤ P (piCompl 3) ∧ V = ⁅V, P⁆}

theorem sigGen148_iff {X : Type} [Group X] [Finite X] {P : Subgroup (MulAut X)} :
    SigGen148 X P ↔ ∀ K Q D : Subgroup (MulAut X), K ≤ (MulAut.conj : X →* MulAut X).range →
      Q ≤ (MulAut.conj : X →* MulAut X).range → SigGenHyp P K Q D → SigGenConcl P K := by
  constructor
  · intro h K Q D hK hQ hh
    exact h K Q D hK hQ hh.perf hh.quasi hh.three hh.normK hh.faith hh.hyp hh.cent hh.inv hh.comm
      hh.normQ hh.nontriv
  · intro h K Q D hK hQ hperf hquasi h3 hPK hfaith hD hQD hQinv hQP hQK hnt
    exact h K Q D hK hQ ⟨hperf, hquasi, h3, hPK, hfaith, hD, hQD, hQinv, hQP, hQK, hnt⟩

section Transport

variable (f : G →* G') (hf : Function.Injective f)
include hf

theorem isElemAbelian_comap {P : Subgroup G'} (hP : P ≤ f.range)
    (h : CFSG.Assembly.IsElemAbelian 3 P) : CFSG.Assembly.IsElemAbelian 3 (P.comap f) := by
  refine ⟨⟨⟨fun u v => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩
  · have := h.1.is_comm.comm ⟨_, u.2⟩ ⟨_, v.2⟩
    have h1 := congrArg Subtype.val this
    simpa using h1
  · rw [map_pow, map_one]
    exact h.2 _ hx

theorem card_comap_of_le_range {H : Subgroup G'} (hH : H ≤ f.range) :
    Nat.card (H.comap f) = Nat.card H := by
  rw [← Subgroup.card_map_of_injective hf, Subgroup.map_comap_eq_self hH]

theorem mem_normalizer_comap_iff {H : Subgroup G'} (hH : H ≤ f.range) (x : G) :
    x ∈ Subgroup.normalizer ((H.comap f : Subgroup G) : Set G) ↔
      f x ∈ Subgroup.normalizer (H : Set G') := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    constructor
    · intro hy
      obtain ⟨z, rfl⟩ := hH hy
      have := (h z).mp hy
      rwa [Subgroup.mem_comap, map_mul, map_mul, map_inv] at this
    · intro hy
      have hyr : f x * y * (f x)⁻¹ ∈ f.range := hH hy
      obtain ⟨z, hz⟩ := hyr
      have hz' : f (x⁻¹ * z * x) = y := by
        rw [map_mul, map_mul, map_inv, hz]
        group
      rw [← hz']
      have : z ∈ H.comap f := by rw [Subgroup.mem_comap, hz]; exact hy
      have h2 := (h (x⁻¹ * z * x)).mpr (by
        have e : x * (x⁻¹ * z * x) * x⁻¹ = z := by group
        rw [e]; exact this)
      exact h2
  · intro h y
    rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact h (f y)

theorem mem_centralizer_comap_iff {H : Subgroup G'} (hH : H ≤ f.range) (x : G) :
    x ∈ Subgroup.centralizer ((H.comap f : Subgroup G) : Set G) ↔
      f x ∈ Subgroup.centralizer (H : Set G') := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    obtain ⟨z, rfl⟩ := hH hy
    have := h z hy
    rw [← map_mul, ← map_mul, this]
  · intro h y hy
    exact hf (by rw [map_mul, map_mul]; exact h (f y) hy)

theorem comap_commutator_of_le_range {A B : Subgroup G'} (hA : A ≤ f.range) (hB : B ≤ f.range) :
    (⁅A, B⁆ : Subgroup G').comap f = ⁅A.comap f, B.comap f⁆ := by
  apply Subgroup.map_injective hf
  rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self hA, Subgroup.map_comap_eq_self hB,
    Subgroup.map_comap_eq_self]
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨x, rfl⟩ := hA ha
  obtain ⟨y, rfl⟩ := hB hb
  exact ⟨⁅x, y⁆, by rw [map_commutatorElement]⟩

theorem map_theta_comap {K : Subgroup G'} (hK : K ≤ f.range) :
    ((aschbacherSolvableCore 3 ↥(K.comap f)).map (K.comap f).subtype).map f =
      (aschbacherSolvableCore 3 ↥K).map K.subtype := by
  have := PS.inSubgroup_theta_map_injective f hf (K.comap f)
  rw [Subgroup.map_comap_eq_self hK] at this
  exact this.symm

theorem SigGenHyp.comap {P K Q D : Subgroup G'} (hP : P ≤ f.range) (hK : K ≤ f.range)
    (hQ : Q ≤ f.range) (h : SigGenHyp P K Q D) :
    SigGenHyp (P.comap f) (K.comap f) (Q.comap f) (D.comap f) := by
  have hD : D ≤ f.range := h.hyp.1.trans hP
  set eK : ↥(K.comap f) ≃* ↥K :=
    ((K.comap f).equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr
      (Subgroup.map_comap_eq_self hK)) with heK
  have hθ := map_theta_comap f hf hK
  have hθmem : ∀ x : G, x ∈ (aschbacherSolvableCore 3 ↥(K.comap f)).map (K.comap f).subtype ↔
      f x ∈ (aschbacherSolvableCore 3 ↥K).map K.subtype := by
    intro x
    rw [← hθ]
    constructor
    · intro hx
      exact Subgroup.mem_map_of_mem f hx
    · rintro ⟨y, hy, hyx⟩
      rwa [← hf hyx]
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ⟨le_top, ?_, ?_⟩, ?_, ?_, ?_⟩
  · have := h.perf
    exact Group.IsPerfect.ofSurjective (f := eK.symm.toMonoidHom) eK.symm.surjective
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ eK (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv
        Nat.prime_three eK)).symm h.quasi
  · rw [card_comap_of_le_range f hf hK]; exact h.three
  · intro p hp
    exact (mem_normalizer_comap_iff f hf hK p).mpr (h.normK hp)
  · intro p hp hpK
    apply hf
    rw [map_one]
    refine h.faith (f p) hp fun k hk => ?_
    obtain ⟨k', rfl⟩ := hK hk
    have := (hθmem _).mp (hpK k' hk)
    simpa using this
  · intro x hx
    exact h.hyp.1 hx
  · rw [card_comap_of_le_range f hf hP, card_comap_of_le_range f hf hD]
    exact h.hyp.2
  · intro q hq
    exact (mem_centralizer_comap_iff f hf hD q).mpr (h.cent hq)
  · intro r hr
    apply h.inv.2.1 r
    rwa [card_comap_of_le_range f hf hQ] at hr
  · intro p hp
    exact (mem_normalizer_comap_iff f hf hQ p).mpr (h.inv.2.2 hp)
  · rw [← comap_commutator_of_le_range f hf hQ hP, ← h.comm]
  · intro q hq
    exact (mem_normalizer_comap_iff f hf hK q).mpr (h.normQ hq)
  · intro hle
    apply h.nontriv
    rw [← comap_commutator_of_le_range f hf hK hQ] at hle
    intro y hy
    have hyr : y ∈ f.range := by
      have hcr : ⁅K, Q⁆ ≤ f.range := by
        rw [Subgroup.commutator_le]
        intro a ha b hb
        obtain ⟨x, rfl⟩ := hK ha
        obtain ⟨z, rfl⟩ := hQ hb
        exact ⟨⁅x, z⁆, by rw [map_commutatorElement]⟩
      exact hcr hy
    obtain ⟨x, rfl⟩ := hyr
    exact (hθmem x).mp (hle hy)

theorem SigGenConcl.of_comap {P K : Subgroup G'} (hP : P ≤ f.range) (hK : K ≤ f.range)
    (h : SigGenConcl (P.comap f) (K.comap f)) : SigGenConcl P K := by
  intro y hy
  obtain ⟨x, rfl⟩ := hK hy
  have hx : x ∈ K.comap f := hy
  have h1 := h hx
  have hmap : ∀ V ∈ {V : Subgroup G | V ≤ K.comap f ∧
      V ∈ invariantPiSubgroups ⊤ (P.comap f) (piCompl 3) ∧ V = ⁅V, P.comap f⁆},
      V.map f ∈ {V : Subgroup G' | V ≤ K ∧ V ∈ invariantPiSubgroups ⊤ P (piCompl 3) ∧
        V = ⁅V, P⁆} := by
    rintro V ⟨hVK, hVinv, hVc⟩
    refine ⟨?_, ⟨le_top, ?_, ?_⟩, ?_⟩
    · rintro _ ⟨v, hv, rfl⟩
      exact hVK hv
    · intro r hr
      apply hVinv.2.1 r
      rwa [Subgroup.card_map_of_injective hf] at hr
    · intro p hp
      obtain ⟨p', rfl⟩ := hP hp
      have hp' : p' ∈ Subgroup.normalizer (V : Set G) := hVinv.2.2 hp
      rw [Subgroup.mem_normalizer_iff] at hp' ⊢
      intro z
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨p' * v * p'⁻¹, (hp' v).mp hv, by rw [map_mul, map_mul, map_inv]⟩
      · rintro ⟨v, hv, hve⟩
        refine ⟨p'⁻¹ * v * p', ?_, ?_⟩
        · have := (hp' (p'⁻¹ * v * p')).mpr (by
            have e : p' * (p'⁻¹ * v * p') * p'⁻¹ = v := by group
            rw [e]; exact hv)
          exact this
        · rw [map_mul, map_mul, map_inv, hve]
          group
    · conv_lhs => rw [hVc]
      rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self hP]
  have h2 : (sSup {V : Subgroup G | V ≤ K.comap f ∧
      V ∈ invariantPiSubgroups ⊤ (P.comap f) (piCompl 3) ∧ V = ⁅V, P.comap f⁆}).map f ≤
      sSup {V : Subgroup G' | V ≤ K ∧ V ∈ invariantPiSubgroups ⊤ P (piCompl 3) ∧ V = ⁅V, P⁆} := by
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun V hV => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (hmap V hV)
  exact h2 (Subgroup.mem_map_of_mem f h1)

end Transport

@[expose] def SigGenIn148 (X : Type) [Group X] [Finite X] : Prop :=
  ∀ P K Q D : Subgroup X, CFSG.Assembly.IsElemAbelian 3 P → Nat.card P = 9 →
    SigGenHyp P K Q D → SigGenConcl P K

theorem sigGen148_of_in {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    (hinn : ∀ α : MulAut X, α ^ 3 = 1 → α ∈ (MulAut.conj : X →* MulAut X).range)
    (h : SigGenIn148 X) {P : Subgroup (MulAut X)} (hP : CFSG.Assembly.IsElemAbelian 3 P)
    (hP9 : Nat.card P = 9) : SigGen148 X P := by
  rw [sigGen148_iff]
  intro K Q D hK hQ hh
  have hinj := PS.conj_injective hZ
  have hPr : P ≤ (MulAut.conj : X →* MulAut X).range := fun α hα => hinn α (hP.2 α hα)
  refine SigGenConcl.of_comap _ hinj hPr hK ?_
  refine h _ _ _ _ (isElemAbelian_comap _ hinj hPr hP) ?_ (hh.comap _ hinj hPr hK hQ)
  rw [card_comap_of_le_range _ hinj hPr, hP9]

@[expose] def ThreeSolvIn148 (X : Type) [Group X] [Finite X] : Prop :=
  ∀ P V : Subgroup X, CFSG.Assembly.IsElemAbelian 3 P → Nat.card P = 9 →
    Nat.Coprime 3 (Nat.card V) → P ≤ Subgroup.normalizer (V : Set X) → Group.IsSolvable V

theorem threeSolvInv148_of_in {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    (hinn : ∀ α : MulAut X, α ^ 3 = 1 → α ∈ (MulAut.conj : X →* MulAut X).range)
    (h : ThreeSolvIn148 X) {P : Subgroup (MulAut X)} (hP : CFSG.Assembly.IsElemAbelian 3 P)
    (hP9 : Nat.card P = 9) : ThreeSolvInv148 X P := by
  intro V hV3 hVinv
  have hinj := PS.conj_injective hZ
  have hPr : P ≤ (MulAut.conj : X →* MulAut X).range := fun α hα => hinn α (hP.2 α hα)
  refine h (P.comap (MulAut.conj : X →* MulAut X)) V (isElemAbelian_comap _ hinj hPr hP)
    (by rw [card_comap_of_le_range _ hinj hPr, hP9]) hV3 ?_
  intro p hp
  refine PS.mem_normalizer_of_conj_le fun v hv => ?_
  have := hVinv _ hp v hv
  simpa [MulAut.conj_apply] using this

@[expose] def InspIn148 (X : Type) [Group X] [Finite X] : Prop :=
  Subgroup.center X = ⊥ ∧
    (∀ α : MulAut X, α ^ 3 = 1 → α ∈ (MulAut.conj : X →* MulAut X).range) ∧
    ThreeSolvIn148 X ∧ RankTwo148 X ∧ SigGenIn148 X

theorem InspIn148.insp {X : Type} [Group X] [Finite X] (h : InspIn148 X)
    {P : Subgroup (MulAut X)} (hP : CFSG.Assembly.IsElemAbelian 3 P) (hP9 : Nat.card P = 9) :
    ThreeSolvInv148 X P ∧ RankTwo148 X ∧ SigGen148 X P :=
  ⟨threeSolvInv148_of_in h.1 h.2.1 h.2.2.1 hP hP9, h.2.2.2.1,
    sigGen148_of_in h.1 h.2.1 h.2.2.2.2 hP hP9⟩

theorem InspIn148.of_mulEquiv {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y]
    (e : X ≃* Y) (h : InspIn148 Y) : InspIn148 X := by
  obtain ⟨hZ, hinn, ha, hb, hc⟩ := h
  set f : Y →* X := e.symm.toMonoidHom with hf
  have hfi : Function.Injective f := e.symm.injective
  have hfr : ∀ H : Subgroup X, H ≤ f.range := fun H x _ => ⟨e x, by simp [hf]⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    have : e x ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := Subgroup.mem_center_iff.mp hx (e.symm y)
      have := congrArg e this
      simpa using this
    rw [hZ, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    simpa using congrArg e.symm this
  · intro α hα
    set β : MulAut Y := (e.symm.trans α).trans e with hβ
    have hβ3 : β ^ 3 = 1 := by
      ext y
      have h1 : ∀ n : ℕ, (β ^ n) y = e ((α ^ n) (e.symm y)) := by
        intro n
        induction n generalizing y with
        | zero => simp
        | succ n ih =>
          rw [pow_succ, MulAut.mul_apply, pow_succ, MulAut.mul_apply, ih]
          simp [hβ]
      rw [h1, hα]
      simp
    obtain ⟨y, hy⟩ := hinn β hβ3
    refine ⟨e.symm y, ?_⟩
    ext x
    have := congrArg (fun γ : MulAut Y => γ (e x)) hy
    simp only [MulAut.conj_apply, hβ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at this
    rw [MulAut.conj_apply]
    apply e.injective
    simpa using this
  · intro P V hP hP9 hV3 hPV
    have hP' := isElemAbelian_comap f hfi (hfr P) hP
    have hsol := ha (P.comap f) (V.comap f) hP' (by rw [card_comap_of_le_range f hfi (hfr P), hP9])
      (by rwa [card_comap_of_le_range f hfi (hfr V)])
      (fun p hp => (mem_normalizer_comap_iff f hfi (hfr V) p).mpr (hPV hp))
    have eV : ↥(V.comap f) ≃* ↥V :=
      ((V.comap f).equivMapOfInjective f hfi).trans
        (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self (hfr V)))
    exact Group.isSolvable_of_surjective (f := eV.toMonoidHom) eV.surjective
  · intro E hE hE27
    exact hb (E.comap f) (isElemAbelian_comap f hfi (hfr E) hE)
      (by rw [card_comap_of_le_range f hfi (hfr E), hE27])
  · intro P K Q D hP hP9 hh
    refine SigGenConcl.of_comap f hfi (hfr P) (hfr K) ?_
    exact hc _ _ _ _ (isElemAbelian_comap f hfi (hfr P) hP)
      (by rw [card_comap_of_le_range f hfi (hfr P), hP9]) (hh.comap f hfi (hfr P) (hfr K) (hfr Q))

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
