module

public import CFSG.RankThree.PartTwo.Sec11.Item116PRank
public import CFSG.RankThree.GroupTheory.ThetaComponents
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank

noncomputable abbrev thetaCent {G : Type} [Group G] [Finite G] (a : G) : Subgroup G :=
  inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))

@[expose] def PRankData {G : Type} [Group G] [Finite G] (p : ℕ) (a : G) (Y : Subgroup G) (e : ℕ) :
    Prop :=
  ∃ (U : Subgroup G) (ψ : U →* Multiplicative (Fin e → ZMod p)),
    U ≤ Y ⊓ Subgroup.centralizer ({a} : Set G) ∧ IsPGroup p U ∧ Function.Surjective ψ ∧
    (∀ u : U, (u : G) ∈ thetaCent a → ψ u = 1) ∧
    (∀ u : U, (∀ y ∈ Y, (u : G) * y * (u : G)⁻¹ * y⁻¹ ∈ thetaCent a) → ψ u = 1)

section Core

variable {G : Type} [Group G] [Finite G]

theorem zpowers_eq_of_orderOf_prime_local {q : ℕ} (hq : q.Prime) {x y : G}
    (hx : orderOf x = q) (hy : y ∈ Subgroup.zpowers x) (hy1 : y ≠ 1) :
    Subgroup.zpowers y = Subgroup.zpowers x := by
  have hle : Subgroup.zpowers y ≤ Subgroup.zpowers x := Subgroup.zpowers_le.2 hy
  have hdvd : orderOf y ∣ q := hx ▸ orderOf_dvd_of_mem_zpowers hy
  have hy' : orderOf y = q := by
    rcases (Nat.dvd_prime hq).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hy1
    · exact h
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, hx, hy']

theorem zpowers_conj_eq_local {a w : G} (ha3 : a ^ 3 = 1)
    (hw : w * a * w⁻¹ ∈ Subgroup.zpowers a) :
    Subgroup.zpowers (w * a * w⁻¹) = Subgroup.zpowers a := by
  by_cases ha1 : a = 1
  · subst ha1
    simp
  · have hord : orderOf a = 3 := orderOf_eq_prime ha3 ha1
    have hb1 : w * a * w⁻¹ ≠ 1 := by
      intro h
      apply ha1
      have e1 : a = w⁻¹ * (w * a * w⁻¹) * w := by group
      rw [e1, h]
      group
    exact zpowers_eq_of_orderOf_prime_local Nat.prime_three hord hw hb1

theorem centralizer_eq_of_zpowers_eq_local {x y : G}
    (h : Subgroup.zpowers x = Subgroup.zpowers y) :
    Subgroup.centralizer ({x} : Set G) = Subgroup.centralizer ({y} : Set G) := by
  have hx : x ∈ Subgroup.zpowers y := by
    rw [← h]
    exact Subgroup.mem_zpowers x
  have hy : y ∈ Subgroup.zpowers x := by
    rw [h]
    exact Subgroup.mem_zpowers y
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hg
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (show Commute g x from hg).zpow_right m
  · intro hg
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (show Commute g y from hg).zpow_right m

theorem centralizer_conj_eq_local {a w : G} (ha3 : a ^ 3 = 1)
    (hw : w * a * w⁻¹ ∈ Subgroup.zpowers a) :
    Subgroup.centralizer ({w * a * w⁻¹} : Set G) = Subgroup.centralizer ({a} : Set G) :=
  centralizer_eq_of_zpowers_eq_local (zpowers_conj_eq_local ha3 hw)

theorem not_threeGenerated_of_finrank {P V : Type*} [Group P] [AddCommGroup V] {p : ℕ}
    [Fact p.Prime] [Module (ZMod p) V] (hV : 3 < Module.finrank (ZMod p) V)
    (g : P →* Multiplicative V) (hg : Function.Surjective g) :
    ¬ ∃ s : Finset P, s.card ≤ 3 ∧ Subgroup.closure (s : Set P) = ⊤ := by
  classical
  rintro ⟨s, hs, hgen⟩
  let T : Finset V := s.image (fun x => Multiplicative.toAdd (g x))
  let W : Submodule (ZMod p) V := Submodule.span (ZMod p) (T : Set V)
  have hmem : ∀ x ∈ Subgroup.closure (s : Set P), Multiplicative.toAdd (g x) ∈ W := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      exact Submodule.subset_span (Finset.mem_coe.mpr
        (Finset.mem_image_of_mem _ (Finset.mem_coe.mp hx)))
    | one =>
      rw [map_one, toAdd_one]
      exact W.zero_mem
    | mul x y _ _ hx hy =>
      rw [map_mul, toAdd_mul]
      exact W.add_mem hx hy
    | inv x _ hx =>
      rw [map_inv, toAdd_inv]
      exact W.neg_mem hx
  have htop : W = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro v
    obtain ⟨x, hx⟩ := hg (Multiplicative.ofAdd v)
    have hxmem := hmem x (by rw [hgen]; exact Subgroup.mem_top x)
    rw [hx, toAdd_ofAdd] at hxmem
    exact hxmem
  have hfin : Module.finrank (ZMod p) W ≤ T.card := finrank_span_finset_le_card (R := ZMod p) T
  have hcardT : T.card ≤ 3 := (Finset.card_image_le).trans hs
  have hWtop : Module.finrank (ZMod p) W = Module.finrank (ZMod p) V := by
    rw [htop, finrank_top]
  omega

theorem commute_mk_of_ne_components {H : Type} [Group H] [Finite H] {L L' : Subgroup H}
    (hL : L ∈ thetaComponents 3 H) (hL' : L' ∈ thetaComponents 3 H) (hne : L ≠ L') {x x' : H}
    (hx : x ∈ L) (hx' : x' ∈ L') :
    QuotientGroup.mk' (aschbacherSolvableCore 3 H) x *
        QuotientGroup.mk' (aschbacherSolvableCore 3 H) x' =
      QuotientGroup.mk' (aschbacherSolvableCore 3 H) x' *
        QuotientGroup.mk' (aschbacherSolvableCore 3 H) x := by
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 H) with hπ
  obtain ⟨hbij, -, -⟩ := theta_component_quotient_correspondence (H := H) Nat.prime_three
  have hKne : L.map π ≠ L'.map π := fun h => hne (hbij.injOn hL hL' h)
  have hcomm := (LocalCores.distinct_components_commute
    (isComponent_map_of_mem_thetaComponents Nat.prime_three hL)
    (isComponent_map_of_mem_thetaComponents Nat.prime_three hL')).resolve_left hKne
  have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  exact (Subgroup.mem_centralizer_iff.mp (hcent (Subgroup.mem_map_of_mem π hx)) (π x')
    (Subgroup.mem_map_of_mem π hx')).symm

theorem commutator_mem_thetaCent_of_ne {a : G} {Y Y' : Subgroup G}
    (hY : Y ∈ thetaComponentsAt 3 a) (hY' : Y' ∈ thetaComponentsAt 3 a) (hne : Y ≠ Y') :
    ∀ y ∈ Y, ∀ y' ∈ Y', y * y' * y⁻¹ * y'⁻¹ ∈ thetaCent a := by
  obtain ⟨L, hL, rfl⟩ := hY
  obtain ⟨L', hL', rfl⟩ := hY'
  have hLne : L ≠ L' := fun h => hne (by rw [h])
  intro y hy y' hy'
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
  obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.mp hy'
  have hc := commute_mk_of_ne_components hL hL' hLne hu hu'
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G))) with hπ
  have hπz : π (u * u' * u⁻¹ * u'⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  have hz : u * u' * u⁻¹ * u'⁻¹ ∈ aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G)) :=
    (QuotientGroup.eq_one_iff _).mp hπz
  exact Subgroup.mem_map_of_mem (Subgroup.centralizer ({a} : Set G)).subtype hz

theorem map_conj_centralizer_singleton_local (w a : G) :
    (Subgroup.centralizer ({a} : Set G)).map (MulAut.conj w).toMonoidHom =
      Subgroup.centralizer ({w * a * w⁻¹} : Set G) := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    change w * x * w⁻¹ * (w * a * w⁻¹) = w * a * w⁻¹ * (w * x * w⁻¹)
    calc w * x * w⁻¹ * (w * a * w⁻¹) = w * (x * a) * w⁻¹ := by group
      _ = w * (a * x) * w⁻¹ := by rw [hx]
      _ = w * a * w⁻¹ * (w * x * w⁻¹) := by group
  · intro hy
    refine ⟨w⁻¹ * y * w, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have h' : y * (w * a * w⁻¹) = w * a * w⁻¹ * y := hy
      calc w⁻¹ * y * w * a = w⁻¹ * (y * (w * a * w⁻¹)) * w := by group
        _ = w⁻¹ * (w * a * w⁻¹ * y) * w := by rw [h']
        _ = a * (w⁻¹ * y * w) := by group
    · change w * (w⁻¹ * y * w) * w⁻¹ = y
      group

theorem centralizer_map_conj_local {a w : G} (ha3 : a ^ 3 = 1)
    (hw : w * a * w⁻¹ ∈ Subgroup.zpowers a) :
    (Subgroup.centralizer ({a} : Set G)).map (MulAut.conj w).toMonoidHom =
      Subgroup.centralizer ({a} : Set G) :=
  (map_conj_centralizer_singleton_local w a).trans (centralizer_conj_eq_local ha3 hw)

noncomputable def conjCentAut_local {a w : G} (ha3 : a ^ 3 = 1)
    (hw : w * a * w⁻¹ ∈ Subgroup.zpowers a) :
    Subgroup.centralizer ({a} : Set G) ≃* Subgroup.centralizer ({a} : Set G) :=
  (Subgroup.equivMapOfInjective (Subgroup.centralizer ({a} : Set G))
    (MulAut.conj w).toMonoidHom (MulAut.conj w).injective).trans
    (MulEquiv.subgroupCongr (centralizer_map_conj_local ha3 hw))

theorem thetaCent_map_conj_local {a w : G} (ha3 : a ^ 3 = 1)
    (hw : w * a * w⁻¹ ∈ Subgroup.zpowers a) :
    (thetaCent a).map (MulAut.conj w).toMonoidHom = thetaCent a := by
  have hθ := aschbacherSolvableCore_map_mulEquiv Nat.prime_three (conjCentAut_local ha3 hw)
  have hcomp : (MulAut.conj w).toMonoidHom.comp (Subgroup.centralizer ({a} : Set G)).subtype
      = (Subgroup.centralizer ({a} : Set G)).subtype.comp (conjCentAut_local ha3 hw).toMonoidHom :=
    MonoidHom.ext fun x => rfl
  unfold thetaCent inSubgroup
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hθ]

theorem map_conj_mem_thetaComponentsAt {a : G} (ha3 : a ^ 3 = 1) {Y : Subgroup G}
    (hY : Y ∈ thetaComponentsAt 3 a) {w : G} (hw : w * a * w⁻¹ ∈ Subgroup.zpowers a) :
    Y.map (MulAut.conj w).toMonoidHom ∈ thetaComponentsAt 3 a := by
  obtain ⟨L, hL, rfl⟩ := hY
  unfold thetaComponentsAt
  refine ⟨L.map (conjCentAut_local ha3 hw).toMonoidHom,
    map_mulEquiv_mem_thetaComponents Nat.prime_three (conjCentAut_local ha3 hw) hL, ?_⟩
  dsimp only
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem PRankData.conj {a : G} (ha3 : a ^ 3 = 1) {p : ℕ} {Y : Subgroup G} {e : ℕ}
    (hd : PRankData p a Y e) {w : G} (hw : w * a * w⁻¹ ∈ Subgroup.zpowers a) :
    PRankData p a (Y.map (MulAut.conj w).toMonoidHom) e := by
  unfold PRankData at hd ⊢
  obtain ⟨U, ψ, hUle, hUp, hψs, hk1, hk2⟩ := hd
  have hinv : ∀ x : G, (MulAut.conj w).toMonoidHom x ∈ thetaCent a ↔ x ∈ thetaCent a := by
    intro x
    have h : (MulAut.conj w).toMonoidHom x ∈
        (thetaCent a).map (MulAut.conj w).toMonoidHom ↔ x ∈ thetaCent a :=
      Subgroup.mem_map_iff_mem (f := (MulAut.conj w).toMonoidHom) (MulAut.conj w).injective
    rwa [thetaCent_map_conj_local ha3 hw] at h
  refine ⟨U.map (MulAut.conj w).toMonoidHom,
    ψ.comp (Subgroup.equivMapOfInjective U (MulAut.conj w).toMonoidHom
      (MulAut.conj w).injective).symm.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    have hu' := hUle hu
    rw [Subgroup.mem_inf] at hu'
    rw [Subgroup.mem_inf]
    refine ⟨Subgroup.mem_map_of_mem _ hu'.1, ?_⟩
    have hc := Subgroup.mem_map_of_mem (MulAut.conj w).toMonoidHom hu'.2
    rwa [centralizer_map_conj_local ha3 hw] at hc
  · exact hUp.map (MulAut.conj w).toMonoidHom
  · intro m
    obtain ⟨u, hu⟩ := hψs m
    refine ⟨Subgroup.equivMapOfInjective U (MulAut.conj w).toMonoidHom
      (MulAut.conj w).injective u, ?_⟩
    exact (congrArg ψ ((Subgroup.equivMapOfInjective U (MulAut.conj w).toMonoidHom
      (MulAut.conj w).injective).symm_apply_apply u)).trans hu
  · intro u'
    obtain ⟨u, rfl⟩ := (Subgroup.equivMapOfInjective U (MulAut.conj w).toMonoidHom
      (MulAut.conj w).injective).surjective u'
    intro hθ
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    apply hk1 u
    have hθ' : (MulAut.conj w).toMonoidHom (u : G) ∈ thetaCent a := hθ
    exact (hinv _).mp hθ'
  · intro u' hu'
    obtain ⟨u, rfl⟩ := (Subgroup.equivMapOfInjective U (MulAut.conj w).toMonoidHom
      (MulAut.conj w).injective).surjective u'
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    apply hk2 u
    intro y hy
    have h : (MulAut.conj w).toMonoidHom (u : G) * (MulAut.conj w).toMonoidHom y *
        ((MulAut.conj w).toMonoidHom (u : G))⁻¹ * ((MulAut.conj w).toMonoidHom y)⁻¹ ∈
          thetaCent a :=
      hu' ((MulAut.conj w).toMonoidHom y) (Subgroup.mem_map_of_mem _ hy)
    apply (hinv _).mp
    simp only [map_mul, map_inv]
    exact h

theorem mem_core_iff_mem_thetaCent_local {a : G} (w : ↥(Subgroup.centralizer ({a} : Set G))) :
    w ∈ aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G)) ↔ (w : G) ∈ thetaCent a := by
  unfold thetaCent inSubgroup
  exact (Subgroup.mem_map_iff_mem (f := (Subgroup.centralizer ({a} : Set G)).subtype)
    (Subgroup.subtype_injective _)).symm

theorem mk_commute_iff_local {Q : Type} [Group Q] (N : Subgroup Q) [N.Normal] (u v : Q) :
    QuotientGroup.mk' N u * QuotientGroup.mk' N v = QuotientGroup.mk' N v * QuotientGroup.mk' N u ↔
      QuotientGroup.mk' N (u * v * u⁻¹ * v⁻¹) = 1 := by
  have h : QuotientGroup.mk' N (u * v * u⁻¹ * v⁻¹) =
      (QuotientGroup.mk' N u * QuotientGroup.mk' N v) *
        (QuotientGroup.mk' N v * QuotientGroup.mk' N u)⁻¹ := by
    simp only [map_mul, map_inv]
    group
  rw [h, mul_inv_eq_one]

theorem commute_mk_of_ne_thetaComponentsAt_local {a : G} {Y Y' : Subgroup G}
    (hY : Y ∈ thetaComponentsAt 3 a) (hY' : Y' ∈ thetaComponentsAt 3 a) (hne : Y ≠ Y')
    {x x' : ↥(Subgroup.centralizer ({a} : Set G))} (hx : (x : G) ∈ Y) (hx' : (x' : G) ∈ Y') :
    QuotientGroup.mk' (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G))) x *
      QuotientGroup.mk' (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G))) x' =
    QuotientGroup.mk' (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G))) x' *
      QuotientGroup.mk' (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G))) x := by
  have hz : x * x' * x⁻¹ * x'⁻¹ ∈ aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G)) := by
    rw [mem_core_iff_mem_thetaCent_local]
    exact commutator_mem_thetaCent_of_ne hY hY' hne _ hx _ hx'
  have hz' : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G)))
      (x * x' * x⁻¹ * x'⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hz
  exact (mk_commute_iff_local (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G)))
    x x').mpr hz'

theorem mem_centralizer_of_mem_thetaComponentsAt_local {a : G} {Y : Subgroup G}
    (hY : Y ∈ thetaComponentsAt 3 a) : ∀ y ∈ Y, y ∈ Subgroup.centralizer ({a} : Set G) := by
  obtain ⟨L, -, rfl⟩ := hY
  intro y hy
  obtain ⟨u, -, rfl⟩ := Subgroup.mem_map.mp hy
  exact u.2

theorem commute_of_noncommProd_eq_one_local {Q : Type} [Group Q] {ι : Type} [DecidableEq ι]
    (s : Finset ι) (f : ι → Q) (comm : (s : Set ι).Pairwise fun i j => Commute (f i) (f j))
    (h : s.noncommProd f comm = 1) {i : ι} (hi : i ∈ s) (q : Q)
    (hq : ∀ j ∈ s, j ≠ i → Commute (f j) q) : Commute (f i) q := by
  have hsub : ((s.erase i : Finset ι) : Set ι).Pairwise fun a b => Commute (f a) (f b) :=
    comm.mono (Finset.coe_subset.mpr (Finset.erase_subset i s))
  have hmul : f i * (s.erase i).noncommProd f hsub = s.noncommProd f comm :=
    Finset.mul_noncommProd_erase s hi f comm
  have hfi : f i = ((s.erase i).noncommProd f hsub)⁻¹ :=
    eq_inv_of_mul_eq_one_left (hmul.trans h)
  have hmem : (s.erase i).noncommProd f hsub ∈ Subgroup.centralizer ({q} : Set Q) :=
    Subgroup.noncommProd_mem _ hsub (fun j hj => Subgroup.mem_centralizer_singleton_iff.mpr
      (hq j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)))
  have hcomm : Commute ((s.erase i).noncommProd f hsub) q :=
    Subgroup.mem_centralizer_singleton_iff.mp hmem
  rw [hfi]
  exact hcomm.inv_left

noncomputable def piOfAddHom_local {ι : Type} {W : ι → Type} [∀ i, Group (W i)] {V : ι → Type}
    [∀ i, AddCommGroup (V i)] (ψ : ∀ i, W i →* Multiplicative (V i)) :
    (∀ i, W i) →* Multiplicative (∀ i, V i) where
  toFun x := Multiplicative.ofAdd (fun i => Multiplicative.toAdd (ψ i (x i)))
  map_one' := by
    simp only [Pi.one_apply, map_one, toAdd_one] <;> rfl
  map_mul' x y := by
    simp only [Pi.mul_apply, map_mul, toAdd_mul] <;> rfl

theorem piOfAddHom_local_apply_eq_one {ι : Type} {W : ι → Type} [∀ i, Group (W i)] {V : ι → Type}
    [∀ i, AddCommGroup (V i)] (ψ : ∀ i, W i →* Multiplicative (V i)) (x : ∀ i, W i)
    (h : ∀ i, ψ i (x i) = 1) : piOfAddHom_local ψ x = 1 := by
  show Multiplicative.ofAdd (fun i => Multiplicative.toAdd (ψ i (x i))) = 1
  simp only [h, toAdd_one] <;> rfl

theorem piOfAddHom_local_surjective {ι : Type} {W : ι → Type} [∀ i, Group (W i)] {V : ι → Type}
    [∀ i, AddCommGroup (V i)] (ψ : ∀ i, W i →* Multiplicative (V i))
    (hψ : ∀ i, Function.Surjective (ψ i)) : Function.Surjective (piOfAddHom_local ψ) := by
  intro w
  choose x hx using fun i => hψ i (Multiplicative.ofAdd (Multiplicative.toAdd w i))
  refine ⟨x, ?_⟩
  show Multiplicative.ofAdd (fun i => Multiplicative.toAdd (ψ i (x i))) = w
  simp only [hx, toAdd_ofAdd, ofAdd_toAdd] <;> rfl

theorem isPGroup_pi_local {ι : Type} [Fintype ι] {V : ι → Type} [∀ i, Group (V i)] {p : ℕ}
    (hV : ∀ i, IsPGroup p (V i)) : IsPGroup p (∀ i, V i) := by
  intro g
  choose k hk using fun i => hV i (g i)
  refine ⟨∑ j, k j, ?_⟩
  funext i
  have hle : k i ≤ ∑ j, k j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i)
  obtain ⟨c, hc⟩ := pow_dvd_pow p hle
  rw [Pi.pow_apply, Pi.one_apply, hc, pow_mul, hk i, one_pow]

theorem finrank_pi_local {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι] (e : ι → ℕ) :
    Module.finrank (ZMod p) (∀ i, Fin (e i) → ZMod p) = ∑ i, e i := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_fin_fun]

theorem exists_not_threeGenerated {a : G} {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι]
    (Y : ι → Subgroup G) (hY : Function.Injective Y) (hYa : ∀ i, Y i ∈ thetaComponentsAt 3 a)
    (e : ι → ℕ) (hrank : 3 < ∑ i, e i) (hdata : ∀ i, PRankData p a (Y i) (e i)) :
    ∃ Pbar : Subgroup (↥(Subgroup.centralizer ({a} : Set G)) ⧸
        aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G))),
      IsPGroup p Pbar ∧ ¬ ∃ s : Finset Pbar, s.card ≤ 3 ∧ Subgroup.closure (s : Set Pbar) = ⊤ := by
  classical
  unfold PRankData at hdata
  choose U ψ hUle hUp hψs _hk1 hk2 using hdata
  have hUC : ∀ i, U i ≤ Subgroup.centralizer ({a} : Set G) :=
    fun i => (hUle i).trans inf_le_right
  obtain ⟨ϕ, hϕ⟩ : ∃ ϕ : ∀ i, ↥(U i) →* (↥(Subgroup.centralizer ({a} : Set G)) ⧸
      aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G))),
      ∀ i (x : ↥(U i)), ϕ i x = QuotientGroup.mk' (aschbacherSolvableCore 3
        ↥(Subgroup.centralizer ({a} : Set G))) (Subgroup.inclusion (hUC i) x) :=
    ⟨fun i => (QuotientGroup.mk' (aschbacherSolvableCore 3
      ↥(Subgroup.centralizer ({a} : Set G)))).comp (Subgroup.inclusion (hUC i)), fun i x => rfl⟩
  have hcomm : Pairwise fun i j => ∀ x y, Commute (ϕ i x) (ϕ j y) := by
    intro i j hij x y
    rw [hϕ, hϕ]
    exact commute_mk_of_ne_thetaComponentsAt_local (x := Subgroup.inclusion (hUC i) x)
      (x' := Subgroup.inclusion (hUC j) y) (hYa i) (hYa j) (fun h => hij (hY h))
      (Subgroup.mem_inf.mp (hUle i x.2)).1 (Subgroup.mem_inf.mp (hUle j y.2)).1
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (∀ i, ↥(U i)) →* (↥(Subgroup.centralizer ({a} : Set G)) ⧸
      aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G))),
      Φ = MonoidHom.noncommPiCoprod ϕ hcomm := ⟨_, rfl⟩
  have hker : Φ.ker ≤ (piOfAddHom_local ψ).ker := by
    intro x hx
    have hxΦ : Φ x = 1 := MonoidHom.mem_ker.mp hx
    rw [hΦ, MonoidHom.noncommPiCoprod_apply] at hxΦ
    apply MonoidHom.mem_ker.mpr
    apply piOfAddHom_local_apply_eq_one
    intro i
    apply hk2 i (x i)
    intro y hy
    have hyC : y ∈ Subgroup.centralizer ({a} : Set G) :=
      mem_centralizer_of_mem_thetaComponentsAt_local (hYa i) y hy
    have hc : Commute (ϕ i (x i)) (QuotientGroup.mk' (aschbacherSolvableCore 3
        ↥(Subgroup.centralizer ({a} : Set G))) ⟨y, hyC⟩) := by
      refine commute_of_noncommProd_eq_one_local Finset.univ (fun j => ϕ j (x j)) _ hxΦ
        (Finset.mem_univ i) _ ?_
      intro j _ hji
      simp only [hϕ]
      exact commute_mk_of_ne_thetaComponentsAt_local (x := Subgroup.inclusion (hUC j) (x j))
        (x' := ⟨y, hyC⟩) (hYa j) (hYa i) (fun h => hji (hY h))
        (Subgroup.mem_inf.mp (hUle j (x j).2)).1 hy
    rw [hϕ] at hc
    have h2 := (mk_commute_iff_local (aschbacherSolvableCore 3
      ↥(Subgroup.centralizer ({a} : Set G))) (Subgroup.inclusion (hUC i) (x i))
      ⟨y, hyC⟩).mp hc
    have h3 := (QuotientGroup.eq_one_iff _).mp h2
    exact (mem_core_iff_mem_thetaCent_local _).mp h3
  have hLs : Function.Surjective (QuotientGroup.lift Φ.ker (piOfAddHom_local ψ) hker) := by
    intro w
    obtain ⟨x, hx⟩ := piOfAddHom_local_surjective ψ hψs w
    exact ⟨QuotientGroup.mk x, (QuotientGroup.lift_mk Φ.ker hker x).trans hx⟩
  have hgs : Function.Surjective ((QuotientGroup.lift Φ.ker (piOfAddHom_local ψ) hker).comp
      (QuotientGroup.quotientKerEquivRange Φ).symm.toMonoidHom) := by
    intro w
    obtain ⟨q, hq⟩ := hLs w
    obtain ⟨z, hz⟩ := (QuotientGroup.quotientKerEquivRange Φ).symm.surjective q
    refine ⟨z, ?_⟩
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hz, hq]
  have hV : 3 < Module.finrank (ZMod p) (∀ i, Fin (e i) → ZMod p) := by
    rw [finrank_pi_local]
    exact hrank
  refine ⟨Φ.range, ?_, ?_⟩
  · exact (isPGroup_pi_local hUp).of_surjective Φ.rangeRestrict Φ.rangeRestrict_surjective
  ·
    refine @not_threeGenerated_of_finrank (↥Φ.range) (∀ i, Fin (e i) → ZMod p) _ _ p _
      (Pi.module ι (fun i => Fin (e i) → ZMod p) (ZMod p)) hV _ hgs

theorem odd_card_theta_of_components (hB : KFacts.BlackburnRankTwo) {a : G} {p : ℕ}
    [Fact p.Prime] (hp5 : 5 ≤ p)
    (hloc : CFSG.Assembly.RankThreeEven.localRank p G < 3) {ι : Type} [Fintype ι]
    (Y : ι → Subgroup G) (hY : Function.Injective Y) (hYa : ∀ i, Y i ∈ thetaComponentsAt 3 a)
    (e : ι → ℕ) (hrank : 3 < ∑ i, e i) (hdata : ∀ i, PRankData p a (Y i) (e i)) :
    Odd (Nat.card (thetaCent a)) := by
  by_contra hodd
  have hev : Even (Nat.card (thetaCent a)) := Nat.not_odd_iff_even.mp hodd
  have hcard : Nat.card (thetaCent a) =
      Nat.card (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G))) :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  obtain ⟨Pbar, hP, hnot⟩ := exists_not_threeGenerated Y hY hYa e hrank hdata
  exact hnot (Item116PRank.exists_three_generators_of_even_normal hB hp5 hloc
    (Subgroup.centralizer ({a} : Set G))
    (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G)))
    (by rw [← hcard]; exact hev) Pbar hP)

end Core

end CFSG.RankThree.PartTwo.Sec11
