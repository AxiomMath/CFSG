module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43EvenFinA
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseE

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even

namespace EvenFin

open Equiv

variable {G : Type} [Group G]

structure EndHyp (A Qa Za W C Mc Zb P Mab Q : Subgroup G) (ψ : ↥A →* Perm (Fin 5)) : Prop where
  surj : Function.Surjective ψ
  ker : ∀ x : ↥A, ψ x = 1 → (x : G) ∈ Qa
  mem_Mab : ∀ x : ↥A, (x : G) ∈ Mab ↔ ψ x 4 = 4
  Mab_le : Mab ≤ A
  max : ∀ K : Subgroup G, Mab ≤ K → K ≤ A → K = Mab ∨ K = A
  Za_le : Za ≤ W
  W_le : W ≤ Qa
  Qa_le : Qa ≤ Mab
  Qa_cent : Qa ≤ Subgroup.centralizer (Za : Set G)
  comm_mem : ∀ w ∈ W, ∀ q ∈ Qa, w * q * w⁻¹ * q⁻¹ ∈ Za
  norm_W : A ≤ Subgroup.normalizer (W : Set G)
  norm_Qa : A ≤ Subgroup.normalizer (Qa : Set G)
  C_le : C ≤ Qa
  Mc_eq : Mc = Qa ⊓ Subgroup.centralizer (W : Set G)
  Mc_le : Mc ≤ C
  not_C_le : ¬ C ≤ Mc
  P_le : P ≤ Mab
  P_two : IsPGroup 2 P
  Za_two : IsPGroup 2 Za
  P_norm_C : P ≤ Subgroup.normalizer (C : Set G)
  Mab_norm_C : Mab ≤ Subgroup.normalizer (C : Set G)
  relIndex_U : (W ⊓ Subgroup.centralizer (C : Set G)).relIndex W = 2
  Zb_eq : Za ⊓ Subgroup.centralizer (P : Set G) ≤ Zb
  card_Zb : Nat.card Zb = 2
  Zb_le : Zb ≤ Za
  Mab_cent_Zb : Mab ≤ Subgroup.centralizer (Zb : Set G)
  center : A ⊓ Subgroup.centralizer (A : Set G) = ⊥
  Q_le : Q ≤ P
  Mab_norm_Q : Mab ≤ Subgroup.normalizer (Q : Set G)
  not_Q_le : ¬ Q ≤ Qa
  comm_Q : ⁅Q ⊓ Qa, Mab⁆ ≤ C
  irred : ∀ N : Subgroup G, Za ≤ N → N ≤ W → A ≤ Subgroup.normalizer (N : Set G) →
    N = Za ∨ N = W
  relIndex_Za : Za.relIndex W ≠ 2

structure YData (W C Zb : Subgroup G) (y i : G) : Prop where
  mem_C : y ∈ C
  mem_Zb : i ∈ Zb
  ne_one : i ≠ 1
  comm_eq : ∀ w ∈ W, w ∉ W ⊓ Subgroup.centralizer (C : Set G) → w * y * w⁻¹ * y⁻¹ = i

namespace EndHyp

variable {A Qa Za W C Mc Zb P Mab Q : Subgroup G} {ψ : ↥A →* Perm (Fin 5)}

section Basic

variable (h : EndHyp A Qa Za W C Mc Zb P Mab Q ψ)
include h

theorem Qa_le_A : Qa ≤ A := h.Qa_le.trans h.Mab_le

theorem P_le_A : P ≤ A := h.P_le.trans h.Mab_le

theorem commute_Qa_Za {q z : G} (hq : q ∈ Qa) (hz : z ∈ Za) : q * z = z * q :=
  (Subgroup.mem_centralizer_iff.mp (h.Qa_cent hq) z hz).symm

theorem conj_mem_Qa {g q : G} (hg : g ∈ A) (hq : q ∈ Qa) : g * q * g⁻¹ ∈ Qa :=
  (Subgroup.mem_normalizer_iff.mp (h.norm_Qa hg) q).mp hq

theorem conj_mem_W {g w : G} (hg : g ∈ A) (hw : w ∈ W) : g * w * g⁻¹ ∈ W :=
  (Subgroup.mem_normalizer_iff.mp (h.norm_W hg) w).mp hw

theorem conj_inv_mem_W {g w : G} (hg : g ∈ A) (hw : w ∈ W) : g⁻¹ * w * g ∈ W := by
  have := h.conj_mem_W (inv_mem hg) hw
  rwa [inv_inv] at this

theorem conj_mem_Mc {g n : G} (hg : g ∈ A) (hn : n ∈ Mc) : g * n * g⁻¹ ∈ Mc := by
  rw [h.Mc_eq] at hn ⊢
  exact ⟨h.conj_mem_Qa hg hn.1, conj_mem_centralizer (h.norm_W hg) hn.2⟩

theorem conj_mem_U_iff {g : G} (hgA : g ∈ A) (hgC : g ∈ Subgroup.normalizer (C : Set G))
    (u : G) : g * u * g⁻¹ ∈ W ⊓ Subgroup.centralizer (C : Set G) ↔
      u ∈ W ⊓ Subgroup.centralizer (C : Set G) :=
  conj_mem_inf_centralizer_iff (h.norm_W hgA) hgC u

theorem inv_mul_mem_U {w w₀ : G} (hw : w ∈ W)
    (hwU : w ∉ W ⊓ Subgroup.centralizer (C : Set G)) (hw₀ : w₀ ∈ W)
    (hw₀U : w₀ ∉ W ⊓ Subgroup.centralizer (C : Set G)) :
    w₀⁻¹ * w ∈ W ⊓ Subgroup.centralizer (C : Set G) :=
  inv_mul_mem_of_relIndex_two h.relIndex_U hw₀ hw hw₀U hwU

theorem comm_eq_of_not_mem {w w₀ c : G} (hw : w ∈ W)
    (hwU : w ∉ W ⊓ Subgroup.centralizer (C : Set G)) (hw₀ : w₀ ∈ W)
    (hw₀U : w₀ ∉ W ⊓ Subgroup.centralizer (C : Set G)) (hc : c ∈ C) :
    w * c * w⁻¹ * c⁻¹ = w₀ * c * w₀⁻¹ * c⁻¹ := by
  have hu := h.inv_mul_mem_U hw hwU hw₀ hw₀U
  have hcu : (w₀⁻¹ * w) * c = c * (w₀⁻¹ * w) :=
    (Subgroup.mem_centralizer_iff.mp hu.2 c hc).symm
  calc w * c * w⁻¹ * c⁻¹ = (w₀ * (w₀⁻¹ * w)) * c * (w₀ * (w₀⁻¹ * w))⁻¹ * c⁻¹ := by group
    _ = w₀ * c * w₀⁻¹ * c⁻¹ := comm_mul_right_of_commute hcu

omit h in
theorem comm_eq_one_of_mem {u c : G} (hu : u ∈ W ⊓ Subgroup.centralizer (C : Set G))
    (hc : c ∈ C) : u * c * u⁻¹ * c⁻¹ = 1 := by
  rw [← Subgroup.mem_centralizer_iff.mp hu.2 c hc]
  group

theorem exists_not_mem_U : ∃ w₀ ∈ W, w₀ ∉ W ⊓ Subgroup.centralizer (C : Set G) := by
  by_contra hcon
  push Not at hcon
  have h1 := h.relIndex_U
  rw [Subgroup.relIndex_eq_one.mpr fun w hw => hcon w hw] at h1
  exact absurd h1 (by norm_num)

end Basic

section Steps

variable (h : EndHyp A Qa Za W C Mc Zb P Mab Q ψ)
include h

theorem exists_y [Finite G] : ∃ y ∈ C, ∃ w₀ ∈ W, w₀ ∉ W ⊓ Subgroup.centralizer (C : Set G) ∧
    w₀ * y * w₀⁻¹ * y⁻¹ ∈ Zb ∧ w₀ * y * w₀⁻¹ * y⁻¹ ≠ 1 := by
  obtain ⟨w₀, hw₀, hw₀U⟩ := h.exists_not_mem_U
  have hfZ : ∀ c ∈ C, w₀ * c * w₀⁻¹ * c⁻¹ ∈ Za := fun c hc => h.comm_mem w₀ hw₀ c (h.C_le hc)
  let f : ↥C →* G :=
    { toFun := fun c => w₀ * c * w₀⁻¹ * (c : G)⁻¹
      map_one' := by simp
      map_mul' := fun c₁ c₂ => by
        show w₀ * ((c₁ : G) * c₂) * w₀⁻¹ * ((c₁ : G) * c₂)⁻¹ = _
        exact comm_mul_left_of_commute (h.commute_Qa_Za (h.C_le c₁.2) (hfZ c₂ c₂.2)) }
  have hfC : ∀ c : ↥C, f c = w₀ * c * w₀⁻¹ * (c : G)⁻¹ := fun c => rfl
  have hIZ : f.range ≤ Za := by
    rintro _ ⟨c, rfl⟩
    exact hfZ c c.2
  have hne : f.range ≠ ⊥ := by
    obtain ⟨c, hcC, hcM⟩ := IsConcreteLE.not_le_iff_exists.mp h.not_C_le
    have hcW : c ∉ Subgroup.centralizer (W : Set G) := fun hc =>
      hcM (by rw [h.Mc_eq]; exact ⟨h.C_le hcC, hc⟩)
    rw [Subgroup.mem_centralizer_iff] at hcW
    push Not at hcW
    obtain ⟨w, hw, hwc⟩ := hcW
    have hwU : w ∉ W ⊓ Subgroup.centralizer (C : Set G) := fun hwU =>
      hwc (Subgroup.mem_centralizer_iff.mp hwU.2 c hcC).symm
    intro hbot
    have hmem : f ⟨c, hcC⟩ ∈ f.range := ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot, hfC] at hmem
    have e : w * c * w⁻¹ * c⁻¹ = 1 := (h.comm_eq_of_not_mem hw hwU hw₀ hw₀U hcC).trans hmem
    apply hwc
    calc w * c = (w * c * w⁻¹ * c⁻¹) * (c * w) := by group
      _ = c * w := by rw [e]; group
  have hPI : P ≤ Subgroup.normalizer (f.range : Set G) := by
    refine le_normalizer_of_conj_mem fun p hp i hi => ?_
    obtain ⟨c, rfl⟩ := hi
    have hpA := h.P_le_A hp
    have hc' : p * c * p⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.mp (h.P_norm_C hp) c).mp c.2
    have hw' : p * w₀ * p⁻¹ ∈ W := h.conj_mem_W hpA hw₀
    have hw'U : p * w₀ * p⁻¹ ∉ W ⊓ Subgroup.centralizer (C : Set G) := by
      rw [h.conj_mem_U_iff hpA (h.P_norm_C hp)]
      exact hw₀U
    refine ⟨⟨p * c * p⁻¹, hc'⟩, ?_⟩
    show w₀ * (p * c * p⁻¹) * w₀⁻¹ * (p * c * p⁻¹)⁻¹ = p * (w₀ * c * w₀⁻¹ * (c : G)⁻¹) * p⁻¹
    rw [conj_comm, h.comm_eq_of_not_mem hw' hw'U hw₀ hw₀U hc']
  obtain ⟨i, hiI, hi1, hiP⟩ :=
    exists_fixed_of_le_normalizer h.P_two (h.Za_two.to_le hIZ) hPI hne
  obtain ⟨y, rfl⟩ := hiI
  have hc : f y ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    calc p * f y = (p * f y * p⁻¹) * p := by group
      _ = f y * p := by rw [hiP p hp]
  exact ⟨y, y.2, w₀, hw₀, hw₀U, h.Zb_eq (Subgroup.mem_inf.mpr ⟨hIZ ⟨y, rfl⟩, hc⟩), hi1⟩

theorem exists_ydata [Finite G] : ∃ y i, YData W C Zb y i := by
  obtain ⟨y, hyC, w₀, hw₀, hw₀U, hZ, h1⟩ := h.exists_y
  exact ⟨y, _, ⟨hyC, hZ, h1, fun w hw hwU => h.comm_eq_of_not_mem hw hwU hw₀ hw₀U hyC⟩⟩

theorem mem_Mc_of_mem_Mab {y i : G} (hy : YData W C Zb y i) {m : G} (hm : m ∈ Mab) :
    y⁻¹ * (m * y * m⁻¹) ∈ Mc := by
  have hmA := h.Mab_le hm
  have hmC := h.Mab_norm_C hm
  have hyC := hy.mem_C
  have hy'C : m * y * m⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.mp hmC y).mp hyC
  have key : ∀ w ∈ W, w * y * w⁻¹ * y⁻¹ = w * (m * y * m⁻¹) * w⁻¹ * (m * y * m⁻¹)⁻¹ := by
    intro w hw
    have hw' : m⁻¹ * w * m ∈ W := h.conj_inv_mem_W hmA hw
    have hiff : m⁻¹ * w * m ∈ W ⊓ Subgroup.centralizer (C : Set G) ↔
        w ∈ W ⊓ Subgroup.centralizer (C : Set G) := by
      have := h.conj_mem_U_iff (inv_mem hmA) (inv_mem hmC) w
      rwa [inv_inv] at this
    rw [comm_conj_right w m y]
    by_cases hwU : w ∈ W ⊓ Subgroup.centralizer (C : Set G)
    · rw [comm_eq_one_of_mem hwU hyC, comm_eq_one_of_mem (hiff.mpr hwU) hyC]
      group
    · rw [hy.comm_eq w hw hwU, hy.comm_eq _ hw' (fun h' => hwU (hiff.mp h'))]
      have hc := Subgroup.mem_centralizer_iff.mp (h.Mab_cent_Zb hm) i hy.mem_Zb
      calc i = (i * m) * m⁻¹ := by group
        _ = m * i * m⁻¹ := by rw [hc]
  rw [h.Mc_eq]
  refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (h.C_le hyC)) (h.C_le hy'C), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact commute_of_comm_eq (key w hw)

theorem mem_Mc_of_apply_eq {y i : G} (hy : YData W C Zb y i) {x x' : ↥A}
    (hxx : ψ x 4 = ψ x' 4) :
    ((x : G) * y * (x : G)⁻¹)⁻¹ * ((x' : G) * y * (x' : G)⁻¹) ∈ Mc := by
  have hm4 : ψ (x⁻¹ * x') 4 = 4 := by
    rw [map_mul, map_inv, Perm.mul_apply, ← hxx]
    exact Perm.inv_eq_iff_eq.mpr rfl
  have hn := h.mem_Mc_of_mem_Mab hy ((h.mem_Mab _).mpr hm4)
  have e : ((x : G) * y * (x : G)⁻¹)⁻¹ * ((x' : G) * y * (x' : G)⁻¹) =
      (x : G) * (y⁻¹ * (((x⁻¹ * x' : ↥A) : G) * y * ((x⁻¹ * x' : ↥A) : G)⁻¹)) * (x : G)⁻¹ := by
    push_cast
    group
  rw [e]
  exact h.conj_mem_Mc x.2 hn

theorem eq_one_of_conj_eq {g z : G} (hgA : g ∈ A) (hgM : g ∉ Mab) (hz : z ∈ Zb)
    (hgz : g * z * g⁻¹ = z) : z = 1 := by
  have hle : Mab ≤ A ⊓ Subgroup.centralizer ({z} : Set G) := fun m hm =>
    ⟨h.Mab_le hm, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (h.Mab_cent_Zb hm) z hz).symm⟩
  have hgc : g * z = z * g := by
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [hgz]
  rcases h.max _ hle inf_le_left with heq | heq
  · exact absurd (heq.le ⟨hgA, Subgroup.mem_centralizer_singleton_iff.mpr hgc⟩) hgM
  · have hzA : z ∈ A := h.Qa_le_A (h.W_le (h.Za_le (h.Zb_le hz)))
    have hzc : z ∈ A ⊓ Subgroup.centralizer (A : Set G) := ⟨hzA,
      Subgroup.mem_centralizer_iff.mpr fun a ha =>
        Subgroup.mem_centralizer_singleton_iff.mp (heq.ge ha).2⟩
    rw [h.center] at hzc
    exact hzc

theorem false_of_conj_le [Finite G] {x : G} (hxA : x ∈ A) (hxM : x ∉ Mab)
    (hU : ∀ u ∈ W ⊓ Subgroup.centralizer (C : Set G),
      x⁻¹ * u * x ∈ W ⊓ Subgroup.centralizer (C : Set G)) : False := by
  have hxN : x ∈ Subgroup.normalizer ((W ⊓ Subgroup.centralizer (C : Set G) :
      Subgroup G) : Set G) := by
    have := mem_normalizer_of_conj_le (x := x⁻¹)
      (U := W ⊓ Subgroup.centralizer (C : Set G)) fun u hu => by
        rw [inv_inv]
        exact hU u hu
    simpa using inv_mem this
  have hMabN : Mab ≤ A ⊓ Subgroup.normalizer ((W ⊓ Subgroup.centralizer (C : Set G) :
      Subgroup G) : Set G) := fun m hm =>
    ⟨h.Mab_le hm, Subgroup.mem_normalizer_iff.mpr fun u =>
      (h.conj_mem_U_iff (h.Mab_le hm) (h.Mab_norm_C hm) u).symm⟩
  rcases h.max _ hMabN inf_le_left with heq | heq
  · exact hxM (heq.le ⟨hxA, hxN⟩)
  · have hAN : A ≤ Subgroup.normalizer ((W ⊓ Subgroup.centralizer (C : Set G) :
        Subgroup G) : Set G) := fun a ha => (heq.ge ha).2
    have hZU : Za ≤ W ⊓ Subgroup.centralizer (C : Set G) := fun z hz =>
      ⟨h.Za_le hz, Subgroup.mem_centralizer_iff.mpr fun c hc => h.commute_Qa_Za (h.C_le hc) hz⟩
    rcases h.irred _ hZU inf_le_left hAN with hUZ | hUW
    · exact h.relIndex_Za (by rw [← hUZ]; exact h.relIndex_U)
    · have h1 := h.relIndex_U
      rw [hUW, Subgroup.relIndex_self] at h1
      exact absurd h1 (by norm_num)

theorem conj_mem_U_of_mem_C {y i : G} (hy : YData W C Zb y i) {xb xc : ↥A}
    (hp : ((xb : G) * y * (xb : G)⁻¹) * ((xc : G) * y * (xc : G)⁻¹)⁻¹ ∈ C)
    (hbc : ψ xc 4 ≠ ψ xb 4) {u : G} (hu : u ∈ W ⊓ Subgroup.centralizer (C : Set G)) :
    (xb : G)⁻¹ * u * xb ∈ W ⊓ Subgroup.centralizer (C : Set G) := by
  by_contra hcon
  have huW : u ∈ W := (Subgroup.mem_inf.mp hu).1
  have hb' : (xb : G)⁻¹ * u * xb ∈ W := h.conj_inv_mem_W xb.2 huW
  have hc' : (xc : G)⁻¹ * u * xc ∈ W := h.conj_inv_mem_W xc.2 huW
  have hC'Qa : (xc : G) * y * (xc : G)⁻¹ ∈ Qa := h.conj_mem_Qa xc.2 (h.C_le hy.mem_C)
  have e1 : u * ((xb : G) * y * (xb : G)⁻¹) * u⁻¹ * ((xb : G) * y * (xb : G)⁻¹)⁻¹ =
      (xb : G) * i * (xb : G)⁻¹ := by
    rw [comm_conj_right, hy.comm_eq _ hb' hcon]
  have hAC : u * ((xb : G) * y * (xb : G)⁻¹) * u⁻¹ * ((xb : G) * y * (xb : G)⁻¹)⁻¹ =
      u * ((xc : G) * y * (xc : G)⁻¹) * u⁻¹ * ((xc : G) * y * (xc : G)⁻¹)⁻¹ :=
    comm_eq_of_commute (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hu).2 _ hp).symm
      (h.commute_Qa_Za (h.C_le hp) (h.comm_mem u huW _ hC'Qa))
  have hcU : (xc : G)⁻¹ * u * xc ∉ W ⊓ Subgroup.centralizer (C : Set G) := by
    intro hmem
    have e : u * ((xc : G) * y * (xc : G)⁻¹) * u⁻¹ * ((xc : G) * y * (xc : G)⁻¹)⁻¹ = 1 := by
      rw [comm_conj_right, comm_eq_one_of_mem hmem hy.mem_C]
      group
    rw [← hAC, e1] at e
    apply hy.ne_one
    calc i = (xb : G)⁻¹ * ((xb : G) * i * (xb : G)⁻¹) * xb := by group
      _ = 1 := by rw [e]; group
  have e2 : u * ((xc : G) * y * (xc : G)⁻¹) * u⁻¹ * ((xc : G) * y * (xc : G)⁻¹)⁻¹ =
      (xc : G) * i * (xc : G)⁻¹ := by
    rw [comm_conj_right, hy.comm_eq _ hc' hcU]
  have e3 : (xb : G) * i * (xb : G)⁻¹ = (xc : G) * i * (xc : G)⁻¹ := by
    rw [← e1, ← e2, hAC]
  have hg4 : ψ (xc⁻¹ * xb) 4 ≠ 4 := by
    rw [map_mul, map_inv, Perm.mul_apply]
    intro e
    have e' := congrArg (ψ xc) e
    have key : ∀ (f : Perm (Fin 5)) (x : Fin 5), f (f⁻¹ x) = x := fun f x =>
      (eq_symm_apply f).mp rfl
    rw [key] at e'
    exact hbc e'.symm
  apply hy.ne_one
  refine h.eq_one_of_conj_eq (xc⁻¹ * xb).2 (fun hmem => hg4 ((h.mem_Mab _).mp hmem))
    hy.mem_Zb ?_
  push_cast
  calc (xc : G)⁻¹ * xb * i * ((xc : G)⁻¹ * xb)⁻¹ =
      (xc : G)⁻¹ * ((xb : G) * i * (xb : G)⁻¹) * xc := by group
    _ = (xc : G)⁻¹ * ((xc : G) * i * (xc : G)⁻¹) * xc := by rw [e3]
    _ = i := by group

theorem false_of_data [Finite G] {y i : G} (hy : YData W C Zb y i) {t g m : ↥A}
    (htQ : (t : G) ∈ Q) (hmM : (m : G) ∈ Mab) (hma : ψ (m * g) 4 = ψ g 4)
    (hb : ψ (t * g) 4 ≠ 4) (hbc : ψ (m * (t * g)) 4 ≠ ψ (t * g) 4) : False := by
  have hyQa : y ∈ Qa := h.C_le hy.mem_C
  have hyaQa : (g : G) * y * (g : G)⁻¹ ∈ Qa := h.conj_mem_Qa g.2 hyQa
  have hzQ : (t : G) * ((g : G) * y * (g : G)⁻¹) * (t : G)⁻¹ * ((g : G) * y * (g : G)⁻¹)⁻¹ ∈
      Q := by
    have h1 : ((g : G) * y * (g : G)⁻¹) * (t : G)⁻¹ * ((g : G) * y * (g : G)⁻¹)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (h.Mab_norm_Q (h.Qa_le hyaQa)) _).mp (inv_mem htQ)
    have e : (t : G) * ((g : G) * y * (g : G)⁻¹) * (t : G)⁻¹ * ((g : G) * y * (g : G)⁻¹)⁻¹ =
        (t : G) * (((g : G) * y * (g : G)⁻¹) * (t : G)⁻¹ * ((g : G) * y * (g : G)⁻¹)⁻¹) := by
      group
    rw [e]
    exact mul_mem htQ h1
  have hzQa : (t : G) * ((g : G) * y * (g : G)⁻¹) * (t : G)⁻¹ * ((g : G) * y * (g : G)⁻¹)⁻¹ ∈
      Qa := mul_mem (h.conj_mem_Qa t.2 hyaQa) (inv_mem hyaQa)
  have hk := h.comm_Q (Subgroup.commutator_mem_commutator (Subgroup.mem_inf.mpr ⟨hzQ, hzQa⟩) hmM)
  rw [commutatorElement_def] at hk
  have hn := h.mem_Mc_of_apply_eq hy (x := g) (x' := m * g) hma.symm
  have hC'A : ((m * (t * g) : ↥A) : G) * y * ((m * (t * g) : ↥A) : G)⁻¹ ∈ A :=
    h.Qa_le_A (h.conj_mem_Qa (m * (t * g)).2 hyQa)
  have hC'n := h.conj_mem_Mc hC'A (inv_mem hn)
  have hp : ((t * g : ↥A) : G) * y * ((t * g : ↥A) : G)⁻¹ *
      (((m * (t * g) : ↥A) : G) * y * ((m * (t * g) : ↥A) : G)⁻¹)⁻¹ ∈ C := by
    have e : ((t * g : ↥A) : G) * y * ((t * g : ↥A) : G)⁻¹ *
        (((m * (t * g) : ↥A) : G) * y * ((m * (t * g) : ↥A) : G)⁻¹)⁻¹ =
        ((t : G) * ((g : G) * y * (g : G)⁻¹) * (t : G)⁻¹ * ((g : G) * y * (g : G)⁻¹)⁻¹) * m *
          ((t : G) * ((g : G) * y * (g : G)⁻¹) * (t : G)⁻¹ * ((g : G) * y * (g : G)⁻¹)⁻¹)⁻¹ *
          (m : G)⁻¹ *
        ((((m * (t * g) : ↥A) : G) * y * ((m * (t * g) : ↥A) : G)⁻¹) *
          (((g : G) * y * (g : G)⁻¹)⁻¹ * (((m * g : ↥A) : G) * y * ((m * g : ↥A) : G)⁻¹))⁻¹ *
          (((m * (t * g) : ↥A) : G) * y * ((m * (t * g) : ↥A) : G)⁻¹)⁻¹) := by
      push_cast
      group
    rw [e]
    exact mul_mem hk (h.Mc_le hC'n)
  exact h.false_of_conj_le (t * g).2 (fun hmem => hb ((h.mem_Mab _).mp hmem))
    fun u hu => h.conj_mem_U_of_mem_C hy hp hbc hu

theorem false [Finite G] : False := by
  obtain ⟨y, i, hy⟩ := h.exists_ydata
  obtain ⟨t, htQ, htQa⟩ := IsConcreteLE.not_le_iff_exists.mp h.not_Q_le
  have htP : t ∈ P := h.Q_le htQ
  let tA : ↥A := ⟨t, h.P_le_A htP⟩
  have ht4 : ψ tA 4 = 4 := (h.mem_Mab tA).mp (h.P_le htP)
  obtain ⟨a, ha⟩ : ∃ a, ψ tA a ≠ a := by
    by_contra hcon
    push Not at hcon
    exact htQa (h.ker tA (Equiv.ext hcon))
  have ha4 : a ≠ 4 := by
    rintro rfl
    exact ha ht4
  have hb4 : ψ tA a ≠ 4 := fun e => ha4 ((ψ tA).injective (e.trans ht4.symm))
  obtain ⟨c, hca, hcb, hc4⟩ : ∃ c : Fin 5, c ≠ a ∧ c ≠ ψ tA a ∧ c ≠ 4 := by
    have key : ∀ a b : Fin 5, ∃ c : Fin 5, c ≠ a ∧ c ≠ b ∧ c ≠ 4 := by decide
    exact key a (ψ tA a)
  obtain ⟨mA, hmA⟩ := h.surj (swap (ψ tA a) c)
  obtain ⟨gA, hgA⟩ := h.surj (swap 4 a)
  have hg4 : ψ gA 4 = a := by
    rw [hgA]
    exact swap_apply_left _ _
  have hm4 : ψ mA 4 = 4 := by
    rw [hmA]
    exact swap_apply_of_ne_of_ne hb4.symm hc4.symm
  refine h.false_of_data hy (t := tA) (g := gA) (m := mA) htQ ((h.mem_Mab mA).mpr hm4) ?_ ?_ ?_
  · rw [map_mul, Perm.mul_apply, hg4, hmA]
    exact swap_apply_of_ne_of_ne ha.symm hca.symm
  · rw [map_mul, Perm.mul_apply, hg4]
    exact hb4
  · simp only [map_mul, Perm.mul_apply, hg4, hmA, swap_apply_left]
    exact hcb

end Steps

end EndHyp

end EvenFin

end CFSG.Quasithin.F53.Stellmacher.S43.Even
