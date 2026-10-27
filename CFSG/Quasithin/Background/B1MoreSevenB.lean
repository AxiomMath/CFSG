module

public import CFSG.Quasithin.Background.B1MoreSevenA
public import CFSG.Quasithin.Background.B1MoreIrr
public import CFSG.Quasithin.Background.B1MoreQuot
public import CFSG.Quasithin.Background.B1Restrict

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {V : Type*} [CommGroup V]

@[expose] def psiHom (a : MulAut V) : V →* V := a.toMonoidHom * (MonoidHom.id V)⁻¹

theorem psiHom_apply (a : MulAut V) (v : V) : psiHom a v = a v * v⁻¹ := rfl

@[expose] def Dsub (a : MulAut V) (I : Subgroup V) : Subgroup V := I.map (psiHom a)

theorem mem_Dsub {a : MulAut V} {I : Subgroup V} {x : V} :
    x ∈ Dsub a I ↔ ∃ i ∈ I, a i * i⁻¹ = x := by
  unfold Dsub
  simp only [Subgroup.mem_map, psiHom_apply]

theorem mem_stabSub_of_invariant {U : Subgroup V} {g : MulAut V} (h1 : ∀ u ∈ U, g u ∈ U)
    (h2 : ∀ u ∈ U, g⁻¹ u ∈ U) : g ∈ stabSub U := by
  intro u
  refine ⟨fun hu => ?_, fun hu => h1 u hu⟩
  have := h2 _ hu
  simpa using this

theorem centSec_conj {X Z : Subgroup V} {g h : MulAut V} (hg : g ∈ centSec X Z)
    (hh : h ∈ stabSub X) (hZ : ∀ z ∈ Z, h z ∈ Z) : h * g * h⁻¹ ∈ centSec X Z := by
  refine ⟨(stabSub X).mul_mem ((stabSub X).mul_mem hh hg.1) ((stabSub X).inv_mem hh),
    fun x hx => ?_⟩
  have hx' : h⁻¹ x ∈ X := ((stabSub X).inv_mem hh x).2 hx
  have e : (h * g * h⁻¹) x * x⁻¹ = h (g (h⁻¹ x) * (h⁻¹ x)⁻¹) := by
    simp [MulAut.mul_apply, map_mul, map_inv]
  rw [e]
  exact hZ _ (hg.2 _ hx')

theorem commSub_inv_H (H : Subgroup (MulAut V)) (X : Subgroup V) :
    ∀ h ∈ H, ∀ m ∈ commSub X H, h m ∈ commSub X H := by
  intro h hh m hm
  unfold commSub at hm ⊢
  refine Subgroup.closure_induction (p := fun m _ => h m ∈ Subgroup.closure
    {c | ∃ x ∈ H, ∃ w ∈ X, x w * w⁻¹ = c}) ?_ ?_ ?_ ?_ hm
  · rintro _ ⟨g, hg, x, hx, rfl⟩
    have e : h (g x * x⁻¹) = ((h * g) x * x⁻¹) * (h x * x⁻¹)⁻¹ := by
      simp [MulAut.mul_apply, map_mul, map_inv]
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨h * g, H.mul_mem hh hg, x, hx, rfl⟩)
      (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨h, hh, x, hx, rfl⟩))
  · simp
  · intro a b _ _ ha hb
    simpa using Subgroup.mul_mem _ ha hb
  · intro a _ ha
    simpa using Subgroup.inv_mem _ ha

theorem sup_commSub_inv (H : Subgroup (MulAut V)) (X : Subgroup V) :
    ∀ h ∈ H, ∀ y ∈ X ⊔ commSub X H, h y ∈ X ⊔ commSub X H := by
  intro h hh y hy
  obtain ⟨x, hx, m, hm, rfl⟩ := Subgroup.mem_sup.1 hy
  have e : h (x * m) = (h x * x⁻¹ * h m) * x := by
    rw [map_mul]; cgroup
  rw [e]
  have h1 : h x * x⁻¹ ∈ commSub X H := Subgroup.subset_closure ⟨h, hh, x, hx, rfl⟩
  have h2 : h m ∈ commSub X H := commSub_inv_H H X h hh m hm
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ((commSub X H).mul_mem h1 h2))
    (Subgroup.mem_sup_left hx)

theorem commSub_sup_le_self (H : Subgroup (MulAut V)) (X : Subgroup V) :
    commSub (X ⊔ commSub X H) H ≤ commSub X H := by
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨h, hh, y, hy, rfl⟩
  obtain ⟨x, hx, m, hm, rfl⟩ := Subgroup.mem_sup.1 hy
  have e : h (x * m) * (x * m)⁻¹ = (h x * x⁻¹) * (h m * m⁻¹) := by
    rw [map_mul]; cgroup
  rw [e]
  have h1 : h x * x⁻¹ ∈ commSub X H := Subgroup.subset_closure ⟨h, hh, x, hx, rfl⟩
  have h2 : h m * m⁻¹ ∈ commSub X H :=
    (commSub X H).mul_mem (commSub_inv_H H X h hh m hm) ((commSub X H).inv_mem hm)
  exact (commSub X H).mul_mem h1 h2

structure B72Hyp (H A : Subgroup (MulAut V)) (a : MulAut V) (I : Subgroup V) : Prop where
  hHA : ⁅H, A⁆ = H
  ha : a ∈ A
  abel : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b
  hcomm : ∀ b ∈ A, ∀ v : V, b (a v * v⁻¹) = a v * v⁻¹
  hI : I ∈ IrrPlus H (⊤ : Subgroup V)
  hne : I.map a.toMonoidHom ≠ I

namespace B72Hyp

variable {H A : Subgroup (MulAut V)} {a : MulAut V} {I : Subgroup V}

theorem conj_mem (P : B72Hyp H A a I) {b : MulAut V} (hb : b ∈ A) {y : MulAut V} (hy : y ∈ H) :
    b * y * b⁻¹ ∈ H :=
  conj_mem_of_commutator_eq P.hHA hb hy

theorem fixV_inv (P : B72Hyp H A a I) {b : MulAut V} (hb : b ∈ A) {z : V} (hz : z ∈ fixV H) :
    b z ∈ fixV H := by
  intro h hh
  have h1 : b⁻¹ * h * b ∈ H := by
    have := P.conj_mem (A.inv_mem hb) hh
    simpa using this
  have h2 : (b⁻¹ * h * b) z = z := hz _ h1
  have h3 : h (b z) = b ((b⁻¹ * h * b) z) := by
    simp [MulAut.mul_apply]
  rw [h3, h2]

theorem map_fixV (P : B72Hyp H A a I) {b : MulAut V} (hb : b ∈ A) :
    (fixV H).map b.toMonoidHom = fixV H := by
  have hst : b ∈ stabSub (fixV H) :=
    mem_stabSub_of_invariant (fun u hu => P.fixV_inv hb hu) (fun u hu => P.fixV_inv (A.inv_mem hb) hu)
  exact map_eq_of_mem_stabSub hst

theorem irr' (P : B72Hyp H A a I) : I.map a.toMonoidHom ∈ IrrPlus H (⊤ : Subgroup V) := by
  refine irrPlus_map (fun x hx => P.conj_mem P.ha hx) (fun x hx => ?_) P.hI
  have := P.conj_mem (A.inv_mem P.ha) hx
  simpa using this

theorem disj (P : B72Hyp H A a I) :
    (I ⊔ fixV H) ⊓ (I.map a.toMonoidHom ⊔ fixV H) = fixV H := by
  rcases irrPlus_sup_inf P.hI P.irr' with h | h
  · exact absurd h.symm P.hne
  · exact h

theorem not_le (P : B72Hyp H A a I) : ¬ I ≤ fixV H := by
  intro h
  obtain ⟨-, -, hlt, -⟩ := mem_irrPlus_top_iff.1 P.hI
  rw [inf_eq_left.2 h] at hlt
  exact lt_irrefl _ hlt

theorem Dsub_fixed (P : B72Hyp H A a I) {b : MulAut V} (hb : b ∈ A) {x : V} (hx : x ∈ Dsub a I) :
    b x = x := by
  obtain ⟨i, -, rfl⟩ := mem_Dsub.1 hx
  exact P.hcomm b hb i

theorem Dsub_le_W (a : MulAut V) (I : Subgroup V) : Dsub a I ≤ I ⊔ I.map a.toMonoidHom := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_Dsub.1 hx
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨i, hi, rfl⟩)
    (Subgroup.inv_mem _ (Subgroup.mem_sup_left hi))

theorem not_invariant_DZ (P : B72Hyp H A a I) :
    ¬ ∀ h ∈ H, ∀ x ∈ Dsub a I ⊔ fixV H, h x ∈ Dsub a I ⊔ fixV H := by
  intro hinv
  obtain ⟨invI, commI, -, -⟩ := mem_irrPlus_top_iff.1 P.hI
  obtain ⟨invI', -, -, -⟩ := mem_irrPlus_top_iff.1 P.irr'
  set Z := fixV H with hZ
  set D := Dsub a I with hD
  have hbc : ∀ b ∈ A, b ∈ centSec (D ⊔ Z) Z := by
    intro b hb
    have hbD : ∀ x ∈ D, b x = x := fun x hx => P.Dsub_fixed hb hx
    have hbD' : ∀ x ∈ D, b⁻¹ x = x := fun x hx => P.Dsub_fixed (A.inv_mem hb) hx
    have h1 : ∀ u ∈ D ⊔ Z, b u ∈ D ⊔ Z := by
      intro u hu
      obtain ⟨d, hd, z, hz, rfl⟩ := Subgroup.mem_sup.1 hu
      rw [map_mul, hbD d hd]
      exact Subgroup.mul_mem_sup hd (P.fixV_inv hb hz)
    have h2 : ∀ u ∈ D ⊔ Z, b⁻¹ u ∈ D ⊔ Z := by
      intro u hu
      obtain ⟨d, hd, z, hz, rfl⟩ := Subgroup.mem_sup.1 hu
      rw [map_mul, hbD' d hd]
      exact Subgroup.mul_mem_sup hd (P.fixV_inv (A.inv_mem hb) hz)
    refine ⟨mem_stabSub_of_invariant h1 h2, fun x hx => ?_⟩
    obtain ⟨d, hd, z, hz, rfl⟩ := Subgroup.mem_sup.1 hx
    have e : b (d * z) * (d * z)⁻¹ = b z * z⁻¹ := by
      rw [map_mul, hbD d hd]; cgroup
    rw [e]
    exact Z.mul_mem (P.fixV_inv hb hz) (Z.inv_mem hz)
  have hcc : ∀ h ∈ H, ∀ b ∈ A, h * b * h⁻¹ * b⁻¹ ∈ centSec (D ⊔ Z) Z := by
    intro h hh b hb
    have hhs : h ∈ stabSub (D ⊔ Z) :=
      mem_stabSub_of_invariant (fun u hu => hinv h hh u hu) (fun u hu => hinv h⁻¹ (H.inv_mem hh) u hu)
    have hZh : ∀ z ∈ Z, h z ∈ Z := fun z hz => by rw [hz h hh]; exact hz
    exact (centSec _ _).mul_mem (centSec_conj (hbc b hb) hhs hZh) ((centSec _ _).inv_mem (hbc b hb))
  have hHc : H ≤ centSec (D ⊔ Z) Z := by
    rw [← P.hHA]
    rw [Subgroup.commutator_le]
    intro h hh b hb
    exact hcc h hh b hb
  have key : ∀ i ∈ I, ∀ h ∈ H, h i * i⁻¹ ∈ Z := by
    intro i hi h hh
    have hx : a i * i⁻¹ ∈ D ⊔ Z := Subgroup.mem_sup_left (mem_Dsub.2 ⟨i, hi, rfl⟩)
    have h1 := (hHc hh).2 _ hx
    have hai : a i ∈ I.map a.toMonoidHom := ⟨i, hi, rfl⟩
    set p := h (a i) * (a i)⁻¹ with hp
    set q := h i * i⁻¹ with hq
    have hpq : p * q⁻¹ ∈ Z := by
      have e : p * q⁻¹ = h (a i * i⁻¹) * (a i * i⁻¹)⁻¹ := by
        rw [hp, hq, map_mul, map_inv]; cgroup
      rw [e]; exact h1
    have hqI : q ∈ I := I.mul_mem (invI h hh i hi) (I.inv_mem hi)
    have hpI' : p ∈ I.map a.toMonoidHom :=
      (I.map a.toMonoidHom).mul_mem (invI' h hh _ hai) ((I.map a.toMonoidHom).inv_mem hai)
    have hp1 : p ∈ I ⊔ Z := by
      have e : p = (p * q⁻¹) * q := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hpq) (Subgroup.mem_sup_left hqI)
    have hpZ : p ∈ Z := by
      have : p ∈ (I ⊔ Z) ⊓ (I.map a.toMonoidHom ⊔ Z) := ⟨hp1, Subgroup.mem_sup_left hpI'⟩
      rwa [P.disj] at this
    have hqZ : q ∈ Z := by
      have e : q = (p * q⁻¹)⁻¹ * p := by group
      rw [e]
      exact Z.mul_mem (Z.inv_mem hpq) hpZ
    exact hqZ
  apply P.not_le
  calc I = commSub I H := commI.symm
    _ ≤ Z := by
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨h, hh, i, hi, rfl⟩
      exact key i hi h hh

end B72Hyp

end CFSG.Quasithin
