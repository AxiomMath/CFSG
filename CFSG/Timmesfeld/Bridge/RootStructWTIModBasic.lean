module

public import CFSG.Timmesfeld.Bridge.RootStructWTIRadical
public import CFSG.Timmesfeld.Bridge.RootStructWTIModuleProps

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

theorem commutator_mem_of_mem_sup {K N₀ A B : Subgroup G} (hA : A ≤ K) (hB : B ≤ K)
    (hN₀ : ∀ k ∈ K, ∀ m ∈ N₀, k * m * k⁻¹ ∈ N₀)
    (h : ∀ u ∈ (A : Set G) ∪ B, ∀ v ∈ (A : Set G) ∪ B, u * v * u⁻¹ * v⁻¹ ∈ N₀)
    {n n' : G} (hn : n ∈ A ⊔ B) (hn' : n' ∈ A ⊔ B) : n * n' * n⁻¹ * n'⁻¹ ∈ N₀ := by
  have hcl : A ⊔ B = Subgroup.closure ((A : Set G) ∪ B) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  have hcK : Subgroup.closure ((A : Set G) ∪ B) ≤ K := hcl ▸ sup_le hA hB
  have step : ∀ u ∈ (A : Set G) ∪ B, ∀ v ∈ A ⊔ B, u * v * u⁻¹ * v⁻¹ ∈ N₀ := by
    intro u hu v hv
    rw [hcl] at hv
    induction hv using Subgroup.closure_induction with
    | mem v hv => exact h u hu v hv
    | one => simp
    | mul v w hv hw ihv ihw =>
      have e : u * (v * w) * u⁻¹ * (v * w)⁻¹ =
          (u * v * u⁻¹ * v⁻¹) * (v * (u * w * u⁻¹ * w⁻¹) * v⁻¹) := by group
      rw [e]
      exact N₀.mul_mem ihv (hN₀ v (hcK hv) _ ihw)
    | inv v hv ihv =>
      have e : u * v⁻¹ * u⁻¹ * v⁻¹⁻¹ = v⁻¹ * (u * v * u⁻¹ * v⁻¹)⁻¹ * v⁻¹⁻¹ := by group
      rw [e]
      exact hN₀ v⁻¹ (K.inv_mem (hcK hv)) _ (N₀.inv_mem ihv)
  rw [hcl] at hn
  induction hn using Subgroup.closure_induction with
  | mem u hu => exact step u hu n' hn'
  | one => simp
  | mul u w hu hw ihu ihw =>
    have e : u * w * n' * (u * w)⁻¹ * n'⁻¹ =
        u * (w * n' * w⁻¹ * n'⁻¹) * u⁻¹ * (u * n' * u⁻¹ * n'⁻¹) := by group
    rw [e]
    exact N₀.mul_mem (hN₀ u (hcK hu) _ ihw) ihu
  | inv u hu ihu =>
    have e : u⁻¹ * n' * u⁻¹⁻¹ * n'⁻¹ = u⁻¹ * (u * n' * u⁻¹ * n'⁻¹)⁻¹ * u⁻¹⁻¹ := by group
    rw [e]
    exact hN₀ u⁻¹ (K.inv_mem (hcK hu)) _ (N₀.inv_mem ihu)

theorem lineN_comm (D : Set G) (a d : G) : lineN D d a = lineN D a d := sup_comm _ _

theorem lineN₀_comm (D : Set G) (a d : G) : lineN₀ D d a = lineN₀ D a d := inf_comm _ _

theorem lineN₀_le_nCore_inf (D : Set G) (a d : G) :
    lineN₀ D a d ≤ nCore D a ⊓ Subgroup.centralizer {d} :=
  le_inf inf_le_left fun _ hk =>
    Subgroup.mem_centralizer_singleton_iff.2 (commute_of_mem_nCore hk.2)

theorem lineN₀_le_lineN (D : Set G) (a d : G) : lineN₀ D a d ≤ lineN D a d :=
  le_sup_of_le_left (lineN₀_le_nCore_inf D a d)

theorem conj_mem_lineN₀ (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {a d g : G}
    (hga : Commute g a) (hgd : Commute g d) {m : G} (hm : m ∈ lineN₀ D a d) :
    g * m * g⁻¹ ∈ lineN₀ D a d :=
  ⟨conj_mem_nCore hclass hga hm.1, conj_mem_nCore hclass hgd hm.2⟩

namespace LineSetting

variable (hL : LineSetting G D)
include hL

theorem nCore_eq_closure {p : G} (hp : p ∈ D) :
    nCore D p = Subgroup.closure {c | c ∈ D ∧ Commute p c} :=
  le_antisymm (nCore_le_closure_commute D p) (hL.closure_commute_le_nCore hp)

theorem nCore_eq_of_mem_rootSet {p p' : G} (hp : p ∈ D) (hp' : p' ∈ rootSet D p) :
    nCore D p' = nCore D p := by
  rw [hL.nCore_eq_closure hp'.1, hL.nCore_eq_closure hp]
  congr 1
  ext c
  simp only [Set.mem_ofPred_eq]
  exact ⟨fun ⟨hc, h⟩ => ⟨hc, (hp'.2 c hc).1 h⟩, fun ⟨hc, h⟩ => ⟨hc, (hp'.2 c hc).2 h⟩⟩

theorem mem_nCore_of_commute {p c : G} (hp : p ∈ D) (hc : c ∈ D) (hpc : Commute p c) :
    c ∈ nCore D p :=
  hL.closure_commute_le_nCore hp (Subgroup.subset_closure ⟨hc, hpc⟩)

theorem rootGroup_le_nCore {p x : G} (hp : p ∈ D) (hpx : Commute p x) :
    rootGroup D x ≤ nCore D p := by
  rw [rootGroup, Subgroup.closure_le]
  intro x' hx'
  exact hL.mem_nCore_of_commute hp hx'.1 ((hx'.2 p hp).2 hpx.symm).symm

section Line

variable {a d : G}

theorem line_le_lineN₀ (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d) :
    rootGroup D a ⊔ rootGroup D d ≤ lineN₀ D a d :=
  le_inf (hL.sup_rootGroup_le_nCore ha hd had)
    (by rw [sup_comm]; exact hL.sup_rootGroup_le_nCore hd ha had.symm)

theorem commute_of_mem_nCore_inf (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {k : G}
    (hk : k ∈ nCore D a ⊓ Subgroup.centralizer {d}) {t : G}
    (ht : t ∈ rootGroup D a ⊔ rootGroup D d) : Commute k t := by
  have hdaD : d * a ∈ D := by rw [← had.eq]; exact hadD
  have haT : a ∉ rootSet D d := fun h => hdT (mem_rootSet_comm hd h)
  rw [sup_comm] at ht
  exact hL.commute_of_mem_nCore_of_commute hd ha had.symm hdaD haT hk.1
    (Subgroup.mem_centralizer_singleton_iff.1 hk.2) ht

theorem commute_of_mem_nCore_inf' (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {k : G}
    (hk : k ∈ nCore D d ⊓ Subgroup.centralizer {a}) {t : G}
    (ht : t ∈ rootGroup D a ⊔ rootGroup D d) : Commute k t :=
  hL.commute_of_mem_nCore_of_commute ha hd had hadD hdT hk.1
    (Subgroup.mem_centralizer_singleton_iff.1 hk.2) ht

theorem commute_of_mem_lineN (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {n : G} (hn : n ∈ lineN D a d) {t : G}
    (ht : t ∈ rootGroup D a ⊔ rootGroup D d) : Commute n t := by
  have hle : lineN D a d ≤ Subgroup.centralizer {t} := by
    refine sup_le (fun k hk => ?_) (fun k hk => ?_) <;>
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    · exact hL.commute_of_mem_nCore_inf ha hd had hadD hdT hk ht
    · exact hL.commute_of_mem_nCore_inf' ha hd had hadD hdT hk ht
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hn)

theorem commute_of_mem_lineN₀ (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {n : G} (hn : n ∈ lineN₀ D a d) {t : G}
    (ht : t ∈ rootGroup D a ⊔ rootGroup D d) : Commute n t :=
  hL.commute_of_mem_lineN ha hd had hadD hdT (lineN₀_le_lineN D a d hn) ht

theorem commutator_mem_lineN₀ (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {n n' : G} (hn : n ∈ lineN D a d)
    (hn' : n' ∈ lineN D a d) : n * n' * n⁻¹ * n'⁻¹ ∈ lineN₀ D a d := by
  have hclass := hL.hyp.isClass
  have hcomm := nCoreCommutatorInRoot_of_hyp hL.hyp hL.closure
  have hT := hL.line_le_lineN₀ ha hd had
  set K : Subgroup G := Subgroup.centralizer {a} ⊓ Subgroup.centralizer {d} with hK
  have haT : a ∈ rootGroup D a ⊔ rootGroup D d :=
    Subgroup.mem_sup_left (rootSet_subset_rootGroup D a (mem_rootSet_self ha))
  have hdT' : d ∈ rootGroup D a ⊔ rootGroup D d :=
    Subgroup.mem_sup_right (rootSet_subset_rootGroup D d (mem_rootSet_self hd))
  have hA : nCore D a ⊓ Subgroup.centralizer {d} ≤ K := fun k hk =>
    ⟨Subgroup.mem_centralizer_singleton_iff.2
      (hL.commute_of_mem_nCore_inf ha hd had hadD hdT hk haT),
      hk.2⟩
  have hB : nCore D d ⊓ Subgroup.centralizer {a} ≤ K := fun k hk =>
    ⟨hk.2, Subgroup.mem_centralizer_singleton_iff.2
      (hL.commute_of_mem_nCore_inf' ha hd had hadD hdT hk hdT')⟩
  refine commutator_mem_of_mem_sup hA hB (fun k hk m hm => conj_mem_lineN₀ hclass
    (Subgroup.mem_centralizer_singleton_iff.1 hk.1)
    (Subgroup.mem_centralizer_singleton_iff.1 hk.2) hm) ?_ hn hn'
  rintro u (hu | hu) v (hv | hv)
  · exact hT (Subgroup.mem_sup_left (hcomm a ha u hu.1 v hv.1))
  ·
    refine ⟨?_, ?_⟩
    · have h1 : v * u⁻¹ * v⁻¹ ∈ nCore D a :=
        conj_mem_nCore hclass (Subgroup.mem_centralizer_singleton_iff.1 hv.2)
          ((nCore D a).inv_mem hu.1)
      have : u * v * u⁻¹ * v⁻¹ = u * (v * u⁻¹ * v⁻¹) := by group
      rw [this]
      exact (nCore D a).mul_mem hu.1 h1
    · have h1 : u * v * u⁻¹ ∈ nCore D d :=
        conj_mem_nCore hclass (Subgroup.mem_centralizer_singleton_iff.1 hu.2) hv.1
      exact (nCore D d).mul_mem h1 ((nCore D d).inv_mem hv.1)
  · refine ⟨?_, ?_⟩
    · have h1 : u * v * u⁻¹ ∈ nCore D a :=
        conj_mem_nCore hclass (Subgroup.mem_centralizer_singleton_iff.1 hu.2) hv.1
      exact (nCore D a).mul_mem h1 ((nCore D a).inv_mem hv.1)
    · have h1 : v * u⁻¹ * v⁻¹ ∈ nCore D d :=
        conj_mem_nCore hclass (Subgroup.mem_centralizer_singleton_iff.1 hv.2)
          ((nCore D d).inv_mem hu.1)
      have : u * v * u⁻¹ * v⁻¹ = u * (v * u⁻¹ * v⁻¹) := by group
      rw [this]
      exact (nCore D d).mul_mem hu.1 h1
  · exact hT (Subgroup.mem_sup_right (hcomm d hd u hu.1 v hv.1))

theorem orderOf_mul_eq_four_of_collinear (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {x : G} (hx : x ∈ D) (hax : Commute a x)
    (hxT : x ∉ rootGroup D a ⊔ rootGroup D d) : orderOf (d * x) = 4 := by
  rw [orderOf_mul_comm_eq]
  exact orderOf_mul_eq_four_of_not_mem_line hL.hyp.root hL.lineCentralizerEq ha hd had hadD hdT
    (hL.lineTI ha hd had hadD hdT) hx hax hxT

theorem mul_inv_mem_of_collinear (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {x : G} (hx : x ∈ D) (hax : Commute a x)
    (haxD : a * x ∈ D) (hxT : x ∉ rootGroup D a ⊔ rootGroup D d) {x' : G}
    (hx' : x' ∈ rootSet D x) {t : G} (ht : t ∈ rootGroup D a ⊔ rootGroup D d) :
    x' * t * x'⁻¹ * t⁻¹ ∈ rootGroup D a := by
  have hdaD : d * a ∈ D := by rw [← had.eq]; exact hadD
  rw [sup_comm] at ht
  exact mul_inv_mem_of_special hL.hyp.root hL.closure hL.special hL.commLambda hd ha had.symm
    hdaD hx hax haxD (hL.orderOf_mul_eq_four_of_collinear ha hd had hadD hdT hx hax hxT) hx' ht

theorem conj_mem_line_of_collinear (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {x : G} (hx : x ∈ D) (hax : Commute a x)
    (haxD : a * x ∈ D) (hxT : x ∉ rootGroup D a ⊔ rootGroup D d) {x' : G}
    (hx' : x' ∈ rootSet D x) {t : G} (ht : t ∈ rootGroup D a ⊔ rootGroup D d) :
    x' * t * x'⁻¹ ∈ rootGroup D a ⊔ rootGroup D d := by
  have h := hL.mul_inv_mem_of_collinear ha hd had hadD hdT hx hax haxD hxT hx' ht
  have e : x' * t * x'⁻¹ = (x' * t * x'⁻¹ * t⁻¹) * t := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h) ht

theorem commutator_mem_of_collinear (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {x : G} (hx : x ∈ D) (hax : Commute a x)
    (haxD : a * x ∈ D) (hxT : x ∉ rootGroup D a ⊔ rootGroup D d) {x' : G}
    (hx' : x' ∈ rootGroup D x) {w : G} (hw : w ∈ nCore D d ⊓ Subgroup.centralizer {a}) :
    x' * w * x'⁻¹ * w⁻¹ ∈ nCore D a ⊓ Subgroup.centralizer {d} := by
  have hclass := hL.hyp.isClass
  have hD := hL.hyp.root
  rcases (mem_rootGroup_iff_of_rootClosure hD hL.closure hx).1 hx' with rfl | hx'T
  · rw [one_mul, inv_one, mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hx'M : x' ∈ nCore D a := hL.rootGroup_le_nCore ha hax hx'
  have hinv : x'⁻¹ = x' := hD.inv_eq hx'T.1
  have hdt : x'⁻¹ * d * x' ∈ rootGroup D a ⊔ rootGroup D d := by
    have := hL.conj_mem_line_of_collinear ha hd had hadD hdT hx hax haxD hxT hx'T
      (right_mem_line hd)
    rw [hinv] at this ⊢
    exact this
  have hconj : ∀ {k : G}, Commute k (x'⁻¹ * d * x') → Commute (x' * k * x'⁻¹) d := fun hk => by
    have := (Commute.conj_iff x').2 hk
    rwa [show x' * (x'⁻¹ * d * x') * x'⁻¹ = d by group] at this
  have hcM : x' * w * x'⁻¹ * w⁻¹ ∈ nCore D a := by
    have h1 : w * x'⁻¹ * w⁻¹ ∈ nCore D a :=
      conj_mem_nCore hclass (Subgroup.mem_centralizer_singleton_iff.1 hw.2)
        ((nCore D a).inv_mem hx'M)
    have e : x' * w * x'⁻¹ * w⁻¹ = x' * (w * x'⁻¹ * w⁻¹) := by group
    rw [e]
    exact (nCore D a).mul_mem hx'M h1
  have hwd : Commute w d := hL.commute_of_mem_nCore_inf' ha hd had hadD hdT hw (right_mem_line hd)
  exact ⟨hcM, Subgroup.mem_centralizer_singleton_iff.2
    ((hconj (hL.commute_of_mem_nCore_inf' ha hd had hadD hdT hw hdt)).mul_left hwd.inv_left)⟩

theorem conj_mem_lineN_of_collinear (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {x : G} (hx : x ∈ D) (hax : Commute a x)
    (haxD : a * x ∈ D) (hxT : x ∉ rootGroup D a ⊔ rootGroup D d) {x' : G}
    (hx' : x' ∈ rootSet D x) {n : G} (hn : n ∈ lineN D a d) : x' * n * x'⁻¹ ∈ lineN D a d := by
  have hD := hL.hyp.root
  have hx'M : x' ∈ nCore D a :=
    hL.rootGroup_le_nCore ha hax (rootSet_subset_rootGroup D x hx')
  have hinv : x'⁻¹ = x' := hD.inv_eq hx'.1
  have hdt : x'⁻¹ * d * x' ∈ rootGroup D a ⊔ rootGroup D d := by
    have := hL.conj_mem_line_of_collinear ha hd had hadD hdT hx hax haxD hxT hx'
      (right_mem_line hd)
    rw [hinv] at this ⊢
    exact this
  have hconj : ∀ {k : G}, Commute k (x'⁻¹ * d * x') → Commute (x' * k * x'⁻¹) d := fun hk => by
    have := (Commute.conj_iff x').2 hk
    rwa [show x' * (x'⁻¹ * d * x') * x'⁻¹ = d by group] at this
  have hle : (lineN D a d).map (MulAut.conj x').toMonoidHom ≤ lineN D a d := by
    rw [lineN, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨u, hu, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      refine Subgroup.mem_sup_left ⟨(nCore D a).mul_mem ((nCore D a).mul_mem hx'M hu.1)
        ((nCore D a).inv_mem hx'M), Subgroup.mem_centralizer_singleton_iff.2 (hconj ?_)⟩
      exact hL.commute_of_mem_nCore_inf ha hd had hadD hdT hu hdt
    · rintro _ ⟨v, hv, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have e : x' * v * x'⁻¹ = (x' * v * x'⁻¹ * v⁻¹) * v := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hL.commutator_mem_of_collinear ha hd had
        hadD hdT hx hax haxD hxT (rootSet_subset_rootGroup D x hx') hv))
        (Subgroup.mem_sup_right hv)
  exact hle ⟨n, hn, rfl⟩

omit hL in
theorem mem_normalizer_of_mul_self_eq_one {g : G} (hg : g * g = 1) {H : Subgroup G}
    (hgH : ∀ n ∈ H, g * n * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  have hinv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨hgH n, fun h => ?_⟩
  have := hgH _ h
  rwa [hinv, show g * (g * n * g) * g = (g * g) * n * (g * g) by group, hg, one_mul,
    mul_one] at this

theorem rootGroup_le_normalizer_lineN (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {x : G} (hx : x ∈ D) (hax : Commute a x)
    (haxD : a * x ∈ D) (hxT : x ∉ rootGroup D a ⊔ rootGroup D d) :
    rootGroup D x ≤ Subgroup.normalizer (lineN D a d : Set G) := by
  rw [rootGroup, Subgroup.closure_le]
  intro x' hx'
  exact mem_normalizer_of_mul_self_eq_one (hL.hyp.root.mul_self_eq_one hx'.1)
    fun n hn => hL.conj_mem_lineN_of_collinear ha hd had hadD hdT hx hax haxD hxT hx' hn

theorem lineN₀_le_nCore (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {x : G} (hx : x ∈ D) (hax : Commute a x)
    (haxD : a * x ∈ D) (hxT : x ∉ rootGroup D a ⊔ rootGroup D d) {y : G} (hy : y ∈ D)
    (hdy : Commute d y) (hdyD : d * y ∈ D) (hyT : y ∉ rootGroup D a ⊔ rootGroup D d) {p : G}
    (hpT : p ∈ rootGroup D a ⊔ rootGroup D d) (hpa : p ∉ rootGroup D a) :
    lineN₀ D a d ≤ nCore D p := by
  have hclass := hL.hyp.isClass
  have hD := hL.hyp.root
  have hc := hL.closure
  have hp1 : p ≠ 1 := fun h => hpa (h ▸ (rootGroup D a).one_mem)
  have hpD : p ∈ D := mem_of_mem_sup_rootGroup hL.hyp hc hL.special ha hd had hadD hdT hpT hp1
  intro n hn
  by_cases hpd : p ∈ rootSet D d
  · rw [hL.nCore_eq_of_mem_rootSet hd hpd]
    exact hn.2
  obtain ⟨α, hα, δ, hδ, hpe⟩ := exists_mul_eq_of_mem_line hd had hpT
  have hδ1 : δ ≠ 1 := by
    rintro rfl
    rw [mul_one] at hpe
    exact hpa (hpe ▸ hα)
  have hδT : δ ∈ rootSet D d := ((mem_rootGroup_iff_of_rootClosure hD hc hd).1 hδ).resolve_left hδ1
  have hα1 : α ≠ 1 := by
    rintro rfl
    rw [one_mul] at hpe
    exact hpd (hpe ▸ hδT)
  have hαT : α ∈ rootSet D a := ((mem_rootGroup_iff_of_rootClosure hD hc ha).1 hα).resolve_left hα1
  have hδD := hδT.1
  have haδ : Commute a δ := (commute_of_mem_rootGroup_of_commute hδ ha had.symm).symm
  have hδL : δ ∈ rootGroup D a ⊔ rootGroup D d := Subgroup.mem_sup_right hδ
  have hTδ : rootGroup D a ⊔ rootGroup D δ = rootGroup D a ⊔ rootGroup D d := by
    rw [rootGroup_eq_of_mem hδT]
  have haδD : a * δ ∈ D := by
    refine mem_of_mem_sup_rootGroup hL.hyp hc hL.special ha hd had hadD hdT
      (Subgroup.mul_mem _ (left_mem_line ha) hδL) fun h => ?_
    have hδa : δ ∈ rootGroup D a := by
      rw [eq_inv_of_mul_eq_one_right h]
      exact (rootGroup D a).inv_mem (rootSet_subset_rootGroup D a (mem_rootSet_self ha))
    have hne : rootSet D a ≠ rootSet D d := fun h' => hdT (h' ▸ mem_rootSet_self hd)
    have := rootGroup_inf_eq_bot_of_rootClosure hD hc ha hd hne
    have hmem : δ ∈ rootGroup D a ⊓ rootGroup D d := ⟨hδa, hδ⟩
    rw [this, Subgroup.mem_bot] at hmem
    exact hδ1 hmem
  have h4x : orderOf (δ * x) = 4 :=
    orderOf_mul_eq_four_of_mem_rootSet hD hd hx hδT (mem_rootSet_self hx)
      (hL.orderOf_mul_eq_four_of_collinear ha hd had hadD hdT hx hax hxT)
  obtain ⟨x₁, hx₁, hx₁e⟩ := exists_mem_rootSet_conj_eq_mul hL.hyp hc hL.special hL.commLambda
    ha hδD haδ haδD hx hax haxD h4x hαT
  have hαδ : Commute α δ := commute_of_mem_sup_rootGroup ha hd had (Subgroup.mem_sup_left hα) hδL
  have hpe' : p = x₁ * δ * x₁⁻¹ := by rw [hx₁e, hpe, hαδ.eq]
  have hx₁inv : x₁⁻¹ = x₁ := hD.inv_eq hx₁.1
  have hx₁M : x₁ ∈ nCore D a :=
    hL.rootGroup_le_nCore ha hax (rootSet_subset_rootGroup D x hx₁)
  set b := x₁ * y * x₁⁻¹ with hb
  have hbD : b ∈ D := conj_mem_of_isClass hclass x₁ hy
  have hδy : Commute δ y := commute_of_mem_rootGroup_of_commute hδ hy hdy
  have hpb : Commute p b := by rw [hpe', hb]; exact (Commute.conj_iff x₁).2 hδy
  have hydT : y ∉ rootSet D d := fun h => hyT (Subgroup.mem_sup_right
    (rootSet_subset_rootGroup D d h))
  have hδyD : δ * y ∈ D := by
    refine mem_of_mem_sup_rootGroup hL.hyp hc hL.special hd hy hdy hdyD hydT
      (Subgroup.mul_mem _ (Subgroup.mem_sup_left hδ) (right_mem_line hy)) fun h => hyT ?_
    rw [eq_inv_of_mul_eq_one_right h]
    exact (rootGroup D a ⊔ rootGroup D d).inv_mem hδL
  have hpbD : p * b ∈ D := by
    rw [hpe', hb, show x₁ * δ * x₁⁻¹ * (x₁ * y * x₁⁻¹) = x₁ * (δ * y) * x₁⁻¹ by group]
    exact conj_mem_of_isClass hclass x₁ hδyD
  have hpdc : Commute p d := commute_of_mem_sup_rootGroup ha hd had hpT (right_mem_line hd)
  have hpdD : p * d ∈ D := by
    refine mem_of_mem_sup_rootGroup hL.hyp hc hL.special ha hd had hadD hdT
      (Subgroup.mul_mem _ hpT (right_mem_line hd)) fun h => hpd ?_
    rw [eq_inv_of_mul_eq_one_left h, hD.inv_eq hd]
    exact mem_rootSet_self hd
  have hdTp : d ∉ rootSet D p := fun h => hpd (mem_rootSet_comm hpD h)
  have hTp : rootGroup D p ⊔ rootGroup D d = rootGroup D a ⊔ rootGroup D d :=
    sup_rootGroup_eq_of_mem hL.hyp hc hL.special ha hd had hadD hdT hpT (right_mem_line hd) hp1
      (hD.ne_one hd) hdTp
  have hbL : b ∉ rootGroup D p ⊔ rootGroup D d := by
    rw [hTp]
    intro hbT
    apply hyT
    have := hL.conj_mem_line_of_collinear ha hd had hadD hdT hx hax haxD hxT hx₁ hbT
    rwa [hb, show x₁ * (x₁ * y * x₁⁻¹) * x₁⁻¹ = (x₁ * x₁) * y * (x₁ * x₁)⁻¹ by group,
      hD.mul_self_eq_one hx₁.1, one_mul, inv_one, mul_one] at this
  have hnp : Commute n p := hL.commute_of_mem_lineN₀ ha hd had hadD hdT hn hpT
  have hAp : rootGroup D p ⊔ rootGroup D b =
      (rootGroup D d ⊔ rootGroup D y).map (MulAut.conj x₁).toMonoidHom := by
    rw [Subgroup.map_sup, ← rootGroup_eq_of_mem hδT, ← rootGroup_conj hclass,
      ← rootGroup_conj hclass, ← hpe', ← hb]
  have hcA : n⁻¹ * x₁⁻¹ * n * x₁ ∈ rootGroup D a := by
    have := nCoreCommutatorInRoot_of_hyp hL.hyp hc a ha n⁻¹ ((nCore D a).inv_mem hn.1) x₁⁻¹
      ((nCore D a).inv_mem hx₁M)
    simpa only [inv_inv] using this
  have hydD : y * d ∈ D := by rw [← hdy.eq]; exact hdyD
  have hya4 : orderOf (y * a) = 4 :=
    orderOf_mul_eq_four_of_not_mem_line' hD hL.lineCentralizerEq ha hd had hadD hdT
      (hL.lineTI ha hd had hadD hdT) hy hdy hyT
  have hfixc : ∀ c ∈ rootGroup D a,
      (rootGroup D d ⊔ rootGroup D y).map (MulAut.conj c).toMonoidHom =
        rootGroup D d ⊔ rootGroup D y := by
    intro c hcA'
    rcases (mem_rootGroup_iff_of_rootClosure hD hc ha).1 hcA' with rfl | hcT
    · exact RankOne.map_conj_one _
    · have hN := normalizesLine_of_special hD hL.special hL.commLambda hy hd hdy.symm hydD ha
        had.symm (by rw [← had.eq]; exact hadD) hya4 hcT
      refine map_conj_eq_of_mul_self_eq_one (hD.mul_self_eq_one hcT.1) fun u hu => ?_
      rw [sup_comm] at hu ⊢
      exact hN u hu
  have hfixn : (rootGroup D d ⊔ rootGroup D y).map (MulAut.conj n).toMonoidHom =
      rootGroup D d ⊔ rootGroup D y :=
    hL.map_conj_eq_of_mem_closure hd (nCore_le_closure_commute D d hn.2)
      ⟨y, hy, hdy, hdyD, hydT, rfl⟩
  have hkL : (rootGroup D p ⊔ rootGroup D b).map (MulAut.conj n).toMonoidHom =
      rootGroup D p ⊔ rootGroup D b := by
    rw [hAp, ← RankOne.map_conj_mul,
      show n * x₁ = x₁ * n * (n⁻¹ * x₁⁻¹ * n * x₁) by group, RankOne.map_conj_mul,
      RankOne.map_conj_mul, hfixc _ hcA, hfixn]
  exact hL.mem_nCore_of_map_conj_eq hpD hd hpdc hpdD hdTp hbD hpb hpbD hbL hn.2 hnp hkL

theorem conj_mem_line_not_mem (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {x : G} (hx : x ∈ D) (hax : Commute a x)
    (haxD : a * x ∈ D) (hxT : x ∉ rootGroup D a ⊔ rootGroup D d) {x' : G}
    (hx' : x' ∈ rootSet D x) :
    x'⁻¹ * d * x' ∈ rootGroup D a ⊔ rootGroup D d ∧ x'⁻¹ * d * x' ∉ rootGroup D a ∧
      x'⁻¹ * d * x' ∉ rootSet D d := by
  have hD := hL.hyp.root
  have hc := hL.closure
  have hinv : x'⁻¹ = x' := hD.inv_eq hx'.1
  have hconj := hL.conj_mem_line_of_collinear ha hd had hadD hdT hx hax haxD hxT hx'
    (right_mem_line hd)
  refine ⟨by rw [hinv] at hconj ⊢; exact hconj, fun h => ?_, fun h => ?_⟩
  · have hx'a : Commute x' a := (hx'.2 a ha).2 hax.symm
    have hpc : Commute (x'⁻¹ * d * x') x' :=
      commute_of_mem_rootGroup_of_commute h hx'.1 hx'a.symm
    have : x'⁻¹ * d * x' = d := by
      have h3 : x' * (x'⁻¹ * d * x') * x'⁻¹ = x'⁻¹ * d * x' := by
        rw [hpc.symm.eq, mul_inv_cancel_right]
      calc x'⁻¹ * d * x' = x' * (x'⁻¹ * d * x') * x'⁻¹ := h3.symm
        _ = d := by group
    rw [this] at h
    exact hdT (((mem_rootGroup_iff_of_rootClosure hD hc ha).1 h).resolve_left (hD.ne_one hd))
  · have h1 := hL.mul_inv_mem_of_collinear ha hd had hadD hdT hx hax haxD hxT hx'
      (right_mem_line hd)
    have h2 : x' * d * x'⁻¹ * d⁻¹ ∈ rootGroup D d := by
      have h' : x' * d * x'⁻¹ ∈ rootSet D d := by
        have e : x' * d * x'⁻¹ = x'⁻¹ * d * x' := by rw [hinv]
        rw [e]
        exact h
      exact Subgroup.mul_mem _ (rootSet_subset_rootGroup D d h')
        ((rootGroup D d).inv_mem (rootSet_subset_rootGroup D d (mem_rootSet_self hd)))
    have hne : rootSet D a ≠ rootSet D d := fun h' => hdT (h' ▸ mem_rootSet_self hd)
    have hbot := rootGroup_inf_eq_bot_of_rootClosure hD hc ha hd hne
    have hmem : x' * d * x'⁻¹ * d⁻¹ ∈ rootGroup D a ⊓ rootGroup D d := ⟨h1, h2⟩
    rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    have hxd : Commute x' d := by
      show x' * d = d * x'
      calc x' * d = x' * d * x'⁻¹ * x' := by group
        _ = d * x' := by rw [hmem]
    have h4 := hL.orderOf_mul_eq_four_of_collinear ha hd had hadD hdT hx hax hxT
    exact not_commute_of_orderOf_mul_eq_four (hD.mul_self_eq_one hd) (hD.mul_self_eq_one hx) h4
      ((hx'.2 d hd).1 hxd).symm

theorem conj_mem_lineN₀_of_collinear (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {x : G} (hx : x ∈ D) (hax : Commute a x)
    (haxD : a * x ∈ D) (hxT : x ∉ rootGroup D a ⊔ rootGroup D d) {y : G} (hy : y ∈ D)
    (hdy : Commute d y) (hdyD : d * y ∈ D) (hyT : y ∉ rootGroup D a ⊔ rootGroup D d) {x' : G}
    (hx' : x' ∈ rootSet D x) {n : G} (hn : n ∈ lineN₀ D a d) : x' * n * x'⁻¹ ∈ lineN₀ D a d := by
  have hclass := hL.hyp.isClass
  have hx'M : x' ∈ nCore D a :=
    hL.rootGroup_le_nCore ha hax (rootSet_subset_rootGroup D x hx')
  obtain ⟨hpT, hpa, -⟩ := hL.conj_mem_line_not_mem ha hd had hadD hdT hx hax haxD hxT hx'
  have hnp := hL.lineN₀_le_nCore ha hd had hadD hdT hx hax haxD hxT hy hdy hdyD hyT hpT hpa hn
  refine ⟨(nCore D a).mul_mem ((nCore D a).mul_mem hx'M hn.1) ((nCore D a).inv_mem hx'M), ?_⟩
  have := conj_mem_nCore_conj hclass hnp x'
  rwa [show x' * (x'⁻¹ * d * x') * x'⁻¹ = d by group] at this

theorem rootGroup_le_normalizer_lineN₀ (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {x : G} (hx : x ∈ D) (hax : Commute a x)
    (haxD : a * x ∈ D) (hxT : x ∉ rootGroup D a ⊔ rootGroup D d) {y : G} (hy : y ∈ D)
    (hdy : Commute d y) (hdyD : d * y ∈ D) (hyT : y ∉ rootGroup D a ⊔ rootGroup D d) :
    rootGroup D x ≤ Subgroup.normalizer (lineN₀ D a d : Set G) := by
  rw [rootGroup, Subgroup.closure_le]
  intro x' hx'
  exact mem_normalizer_of_mul_self_eq_one (hL.hyp.root.mul_self_eq_one hx'.1)
    fun n hn => hL.conj_mem_lineN₀_of_collinear ha hd had hadD hdT hx hax haxD hxT hy hdy hdyD
      hyT hx' hn

theorem mem_lineN₀_of_mul_inv_mem (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {x : G} (hx : x ∈ D) (hax : Commute a x)
    (haxD : a * x ∈ D) (hxT : x ∉ rootGroup D a ⊔ rootGroup D d) {y : G} (hy : y ∈ D)
    (hdy : Commute d y) (hdyD : d * y ∈ D) (hyT : y ∉ rootGroup D a ⊔ rootGroup D d) {x' : G}
    (hx' : x' ∈ rootSet D x) {w : G} (hw : w ∈ nCore D d ⊓ Subgroup.centralizer {a})
    (hxw : x' * w * x'⁻¹ * w⁻¹ ∈ lineN₀ D a d) : w ∈ lineN₀ D a d := by
  have hclass := hL.hyp.isClass
  have hD := hL.hyp.root
  have hc := hL.closure
  obtain ⟨hpT, hpa, hpd⟩ := hL.conj_mem_line_not_mem ha hd had hadD hdT hx hax haxD hxT hx'
  set p := x'⁻¹ * d * x' with hp
  have hp1 : p ≠ 1 := fun h => hpa (h ▸ (rootGroup D a).one_mem)
  have hpD : p ∈ D := mem_of_mem_sup_rootGroup hL.hyp hc hL.special ha hd had hadD hdT hpT hp1
  have hwM : x' * w * x'⁻¹ ∈ nCore D d := by
    have e : x' * w * x'⁻¹ = (x' * w * x'⁻¹ * w⁻¹) * w := by group
    rw [e]
    exact (nCore D d).mul_mem hxw.2 hw.1
  have hwp : w ∈ nCore D p := by
    have := conj_mem_nCore_conj hclass hwM x'⁻¹
    rwa [inv_inv, show x'⁻¹ * (x' * w * x'⁻¹) * x' = w by group] at this
  have hdpc : Commute d p := commute_of_mem_sup_rootGroup ha hd had (right_mem_line hd) hpT
  have hdpD : d * p ∈ D := by
    refine mem_of_mem_sup_rootGroup hL.hyp hc hL.special ha hd had hadD hdT
      (Subgroup.mul_mem _ (right_mem_line hd) hpT) fun h => hpd ?_
    rw [eq_inv_of_mul_eq_one_right h, hD.inv_eq hd]
    exact mem_rootSet_self hd
  have hTdp : rootGroup D d ⊔ rootGroup D p = rootGroup D a ⊔ rootGroup D d :=
    sup_rootGroup_eq_of_mem hL.hyp hc hL.special ha hd had hadD hdT (right_mem_line hd) hpT
      (hD.ne_one hd) hp1 hpd
  have hinv : x'⁻¹ = x' := hD.inv_eq hx'.1
  set y₂ := x'⁻¹ * y * x' with hy₂
  have hy₂D : y₂ ∈ D := by
    have := conj_mem_of_isClass hclass x'⁻¹ hy
    rwa [inv_inv] at this
  have hpy₂ : Commute p y₂ := by
    have := (Commute.conj_iff x'⁻¹).2 hdy
    rwa [inv_inv] at this
  have hpy₂D : p * y₂ ∈ D := by
    rw [hp, hy₂, show x'⁻¹ * d * x' * (x'⁻¹ * y * x') = x'⁻¹ * (d * y) * x'⁻¹⁻¹ by group]
    exact conj_mem_of_isClass hclass x'⁻¹ hdyD
  have hyT' : y ∉ rootGroup D d ⊔ rootGroup D p := by rw [hTdp]; exact hyT
  have hy₂T : y₂ ∉ rootGroup D d ⊔ rootGroup D p := by
    rw [hTdp]
    intro h
    apply hyT
    have := hL.conj_mem_line_of_collinear ha hd had hadD hdT hx hax haxD hxT hx' h
    rwa [hy₂, show x' * (x'⁻¹ * y * x') * x'⁻¹ = y by group] at this
  have haT : a ∈ rootGroup D d ⊔ rootGroup D p := by rw [hTdp]; exact left_mem_line ha
  have had' : a ∉ rootGroup D d := fun h => hdT (mem_rootSet_comm hd
    (((mem_rootGroup_iff_of_rootClosure hD hc hd).1 h).resolve_left (hD.ne_one ha)))
  have hwa := hL.lineN₀_le_nCore hd hpD hdpc hdpD hpd hy hdy hdyD hyT' hy₂D hpy₂ hpy₂D hy₂T haT
    had' ⟨hw.1, hwp⟩
  exact ⟨hwa, hw.1⟩

theorem nCore_eq_rootGroup_sup (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {x : G} (hx : x ∈ D) (hax : Commute a x)
    (haxD : a * x ∈ D) (hxT : x ∉ rootGroup D a ⊔ rootGroup D d) :
    nCore D a = rootGroup D x ⊔ (nCore D a ⊓ Subgroup.centralizer {d}) := by
  have hD := hL.hyp.root
  have hc := hL.closure
  refine le_antisymm (fun g hg => ?_) (sup_le (hL.rootGroup_le_nCore ha hax) inf_le_left)
  have hgd : g * d * g⁻¹ * d⁻¹ ∈ rootGroup D a :=
    nCoreCommutatorInRoot_of_hyp hL.hyp hc a ha g hg d (hL.mem_nCore_of_commute ha hd had)
  rcases (mem_rootGroup_iff_of_rootClosure hD hc ha).1 hgd with h1 | hα
  · refine Subgroup.mem_sup_right ⟨hg, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have h2 := mul_inv_eq_one.1 h1
    calc g * d = g * d * g⁻¹ * g := by group
      _ = d * g := by rw [h2]
  · have h4 := hL.orderOf_mul_eq_four_of_collinear ha hd had hadD hdT hx hax hxT
    obtain ⟨x₁, hx₁, he⟩ := exists_mem_rootSet_conj_eq_mul hL.hyp hc hL.special hL.commLambda ha
      hd had hadD hx hax haxD h4 hα
    have hαd : Commute (g * d * g⁻¹ * d⁻¹) d := commute_of_mem_rootGroup_of_commute hgd hd had
    have h1 : g * d * g⁻¹ = x₁ * d * x₁⁻¹ := by
      rw [he, ← hαd.eq]
      group
    have hcomm : x₁⁻¹ * g * d = d * (x₁⁻¹ * g) := by
      calc x₁⁻¹ * g * d = x₁⁻¹ * (g * d * g⁻¹) * g := by group
        _ = x₁⁻¹ * (x₁ * d * x₁⁻¹) * g := by rw [h1]
        _ = d * (x₁⁻¹ * g) := by group
    have hx₁M : x₁ ∈ nCore D a :=
      hL.rootGroup_le_nCore ha hax (rootSet_subset_rootGroup D x hx₁)
    have e : g = x₁ * (x₁⁻¹ * g) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (rootSet_subset_rootGroup D x hx₁))
      (Subgroup.mem_sup_right ⟨(nCore D a).mul_mem ((nCore D a).inv_mem hx₁M) hg,
        Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩)

theorem rootGroup_inf_centralizer_eq_bot (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {x : G} (hx : x ∈ D) (hax : Commute a x)
    (hxT : x ∉ rootGroup D a ⊔ rootGroup D d) :
    rootGroup D x ⊓ Subgroup.centralizer {d} = ⊥ := by
  have hD := hL.hyp.root
  rw [eq_bot_iff]
  rintro g ⟨hg, hgd⟩
  rw [Subgroup.mem_bot]
  rcases (mem_rootGroup_iff_of_rootClosure hD hL.closure hx).1 hg with h | hgT
  · exact h
  · exfalso
    have h4 := hL.orderOf_mul_eq_four_of_collinear ha hd had hadD hdT hx hax hxT
    have hxd : Commute x d := (hgT.2 d hd).1 (Subgroup.mem_centralizer_singleton_iff.1 hgd)
    exact not_commute_of_orderOf_mul_eq_four (hD.mul_self_eq_one hd) (hD.mul_self_eq_one hx) h4
      hxd.symm

end Line

end LineSetting

end CFSG.Timmesfeld.Bridge
