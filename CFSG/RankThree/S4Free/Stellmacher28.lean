module

public import CFSG.RankThree.S4Free.Stellmacher31
public import CFSG.RankThree.S4Free.StellmacherNatSz
public import CFSG.RankThree.S4Free.StellmacherSzModule
import CFSG.Quasithin.Background.AutOnIndex
import CFSG.RankThree.S4Free.StellmacherSzSylow
import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.Bridge

public section

namespace CFSG.RankThree.S4Free.Stell

open CFSG.Open CFSG.Quasithin CFSG.RankThree.GF2n.SzExplicit Subgroup

universe u

@[expose] def IsNatSzExt (H : Type*) [Group H] (n : ℕ) : Prop :=
  ∃ ψ : H →* Sz n, Function.Surjective ψ ∧ ψ.ker = oTwo H ∧
    ∃ (V : Type) (_ : CommGroup V) (π : oTwo H →* V) (ρ : H →* MulAut V),
      Function.Surjective π ∧ π.ker ≤ (center H).subgroupOf (oTwo H) ∧
      (∀ (h : H) (x y : oTwo H), (y : H) = h * x * h⁻¹ → ρ h (π x) = π y) ∧
      IsNatSzProduct n ψ ρ

section Offender

variable {V : Type*} [CommGroup V]

theorem ALe.mono {S S' : Subgroup (MulAut V)} {U : Subgroup V} {e : ℚ} (h : ALe S U e)
    (hSS' : S ≤ S') : ALe S' U e := by
  obtain ⟨B, ⟨hBS, hB⟩, hle⟩ := h
  exact ⟨B, ⟨hBS.trans hSS', hB⟩, hle⟩

end Offender

section Quadratic

open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G]

theorem ale_one_autOn_of_quadratic {P A B : Subgroup G} [IsMulCommutative A]
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hPA : P ≤ normalizer (A : Set G)) (hBP : B ≤ P)
    (hq : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ * a⁻¹ ∈ centralizer (B : Set G))
    (hBA : ¬ B ≤ centralizer (A : Set G))
    (hle : (A ⊓ centralizer (B : Set G)).relIndex A ≤
      (B ⊓ centralizer (A : Set G)).relIndex B) : ALe (autOn P A) ⊤ 1 := by
  have hBN : B ≤ normalizer (A : Set G) := hBP.trans hPA
  have hA2' : ∀ a : A, a ^ 2 = 1 := fun a => Subtype.ext (hA2 a a.2)
  have hcA : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ * a⁻¹ ∈ A := fun b hb a ha =>
    A.mul_mem ((mem_normalizer_iff.mp (hBN hb) a).mp ha) (A.inv_mem ha)
  have hconj : ∀ b ∈ B, ∀ b' ∈ B, ∀ a ∈ A,
      b * (b' * a * b'⁻¹) * b⁻¹ = (b' * a * b'⁻¹ * a⁻¹) * ((b * a * b⁻¹ * a⁻¹) * a) := by
    intro b hb b' hb' a ha
    have hc := mem_centralizer_iff.mp (hq b' hb' a ha) b hb
    calc b * (b' * a * b'⁻¹) * b⁻¹ = b * (b' * a * b'⁻¹ * a⁻¹) * b⁻¹ * (b * a * b⁻¹) := by
          group
      _ = (b' * a * b'⁻¹ * a⁻¹) * ((b * a * b⁻¹ * a⁻¹) * a) := by
          rw [hc]
          group
  have hswap : ∀ p q r : G, p * q = q * p → p * (q * r) = q * (p * r) := by
    intro p q r h
    calc p * (q * r) = p * q * r := (mul_assoc p q r).symm
      _ = q * p * r := by rw [h]
      _ = q * (p * r) := mul_assoc q p r
  have hsq : ∀ p r : G, p ^ 2 = 1 → p * (p * r) = r := by
    intro p r h
    rw [← mul_assoc, ← pow_two, h, one_mul]
  have hel : IsElemAbelian2 (autOn B A) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      have hxB : (x : G) ∈ B := hx
      have hyB : (y : G) ∈ B := hy
      refine MulEquiv.ext fun a => Subtype.ext ?_
      simp only [MulAut.mul_apply]
      rw [AutOn.coe_conjAct_apply, AutOn.coe_conjAct_apply, AutOn.coe_conjAct_apply,
        AutOn.coe_conjAct_apply, hconj _ hxB _ hyB _ a.2, hconj _ hyB _ hxB _ a.2]
      have hc := (inferInstance : IsMulCommutative A).is_comm.comm
        (⟨_, hcA _ hyB _ a.2⟩ : A) ⟨_, hcA _ hxB _ a.2⟩
      have hc' := congrArg (fun t : A => (t : G)) hc
      simp only [Subgroup.coe_mul] at hc'
      exact hswap _ _ _ hc'
    · rintro _ ⟨x, hx, rfl⟩
      have hxB : (x : G) ∈ B := hx
      refine MulEquiv.ext fun a => Subtype.ext ?_
      rw [pow_two, MulAut.mul_apply, AutOn.coe_conjAct_apply, AutOn.coe_conjAct_apply,
        hconj _ hxB _ hxB _ a.2, MulAut.one_apply]
      exact hsq _ _ (hA2 _ (hcA _ hxB _ a.2))
  have hfix : fixV (autOn B A) = (centralizer (B : Set G)).subgroupOf A :=
    AutOn.fixV_autOn_eq hBN
  refine ⟨autOn B A, ⟨AutOn.autOn_mono hBP, fun hle' => hBA ?_, IsElemAbelian2.elemAbOn hel ⊤⟩,
    ?_⟩
  · intro b hb
    rw [mem_centralizer_iff]
    intro a ha
    have ha' : (⟨a, ha⟩ : A) ∈ fixV (autOn B A) := hle' (Subgroup.mem_top _)
    rw [hfix, Subgroup.mem_subgroupOf] at ha'
    exact ((mem_centralizer_iff.mp ha') b hb).symm
  · rw [one_mul, dimOn_top, codimOn_top]
    have hidx : (fixV (autOn B A)).index = (A ⊓ centralizer (B : Set G)).relIndex A := by
      rw [hfix, Subgroup.inf_relIndex_left]
      rfl
    have hcard : Nat.card (autOn B A) = (B ⊓ centralizer (A : Set G)).relIndex B :=
      AutOn.card_autOn_eq_relIndex hBN
    rw [← hidx, ← hcard, B1.index_eq_two_pow hA2', B1.card_elemAbelian hel] at hle
    exact_mod_cast (Nat.pow_le_pow_iff_right (by norm_num)).mp hle

end Quadratic

section NatModule

open SzNatural

variable {n : ℕ}

private theorem mem_flag_three_of_sub_rootElt {u : F n} (hu : u ≠ 0) (w : F n)
    {x : Fin 4 → F n} (h : act n (rootElt n u w) x - x ∈ flag n 2) : x ∈ flag n 3 := by
  rw [mem_flag_two] at h
  rw [mem_flag_three]
  have e := h.1
  rw [Pi.sub_apply, act_rootElt] at e
  simp only [Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at e
  have : u * x 3 = 0 := by linear_combination e
  exact (mul_eq_zero.mp this).resolve_left hu

private theorem mem_flag_three_of_sub_rootElt_zero {w : F n} (hw : w ≠ 0) {x : Fin 4 → F n}
    (h : act n (rootElt n 0 w) x - x ∈ flag n 1) : x ∈ flag n 3 := by
  rw [mem_flag_one] at h
  rw [mem_flag_three]
  have e := h.1
  rw [Pi.sub_apply, act_rootElt] at e
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    zero_pow_theta, zero_mul, add_zero] at e
  have h0 : (0 : F n) ^ (1 + 2 ^ (n + 1)) = 0 := zero_pow (by positivity)
  rw [h0, zero_add] at e
  have : w * x 3 = 0 := by linear_combination e
  exact (mul_eq_zero.mp this).resolve_left hw

private theorem commElt_rootElt_zero_flag_three {w : F n} (hw : w ≠ 0) :
    commElt n (rootElt n 0 w) (flag n 3) = flag n 1 := by
  ext y
  rw [mem_commElt, mem_flag_one]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [mem_flag_three] at hv
    rw [act_rootElt]
    simp [hv, zero_pow_theta]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨![0, 0, y 0 / w, 0], (mem_flag_three n).mpr rfl, ?_⟩
    rw [act_rootElt]
    ext j
    fin_cases j <;> simp [h1, h2, h3, zero_pow_theta, mul_div_cancel₀ _ hw]


private theorem exists_conj_rootElt (hn : 1 ≤ n) (P : Sylow 2 (Sz n)) {s : Sz n}
    (hs : s ∈ (P : Subgroup (Sz n)))
    (hs' : s ∉ centralizer ((P : Subgroup (Sz n)) : Set (Sz n))) :
    ∃ (g : Sz n) (u w : F n), u ≠ 0 ∧ s = g * rootElt n u w * g⁻¹ ∧
      ∀ i, series n P i = (flag n i).map (act n g) := by
  obtain ⟨g, hg, hser⟩ := exists_series_eq hn P
  obtain ⟨u, w, hu⟩ := (mem_rootSub n).mp ((hg s).mp hs)
  refine ⟨g, u, w, ?_, by rw [hu]; group, hser⟩
  rintro rfl
  apply hs'
  have : g⁻¹ * s * g ∈ rootSub n ⊓ centralizer (rootSub n : Set (Sz n)) := by
    rw [rootSub_inf_centralizer n hn, ← hu]
    exact ⟨w, rfl⟩
  exact ((inf_centralizer_conj n g hg s).mpr this).2

private theorem exists_conj_rootElt_zero (hn : 1 ≤ n) (P : Sylow 2 (Sz n)) {z : Sz n}
    (hz : z ∈ (P : Subgroup (Sz n)) ⊓ centralizer ((P : Subgroup (Sz n)) : Set (Sz n)))
    (hz1 : z ≠ 1) :
    ∃ (g : Sz n) (w : F n), w ≠ 0 ∧ z = g * rootElt n 0 w * g⁻¹ ∧
      ∀ i, series n P i = (flag n i).map (act n g) := by
  obtain ⟨g, hg, hser⟩ := exists_series_eq hn P
  have hz0 := (inf_centralizer_conj n g hg z).mp hz
  rw [rootSub_inf_centralizer n hn] at hz0
  obtain ⟨w, hw⟩ := (mem_rootCenter n).mp hz0
  refine ⟨g, w, ?_, by rw [hw]; group, hser⟩
  rintro rfl
  rw [rootElt_zero_zero] at hw
  exact hz1 (by simpa [mul_assoc] using (congrArg (fun x => g * x * g⁻¹) hw).symm)

private theorem act_conj_sub (g r : Sz n) (x : Fin 4 → F n) :
    act n g⁻¹ (act n (g * r * g⁻¹) x - x) = act n r (act n g⁻¹ x) - act n g⁻¹ x := by
  rw [map_sub, act_mul, act_mul, act_inv_act]

theorem mem_series_three_of_sub_mem_series_two (hn : 1 ≤ n) (P : Sylow 2 (Sz n)) {s : Sz n}
    (hs : s ∈ (P : Subgroup (Sz n)))
    (hs' : s ∉ centralizer ((P : Subgroup (Sz n)) : Set (Sz n))) {x : Fin 4 → F n}
    (h : act n s x - x ∈ series n P 2) : x ∈ series n P 3 := by
  obtain ⟨g, u, w, hu, rfl, hser⟩ := exists_conj_rootElt hn P hs hs'
  rw [hser, mem_map_act] at h ⊢
  rw [act_conj_sub] at h
  exact mem_flag_three_of_sub_rootElt hu w h

theorem mem_series_three_of_sub_mem_series_one (hn : 1 ≤ n) (P : Sylow 2 (Sz n)) {z : Sz n}
    (hz : z ∈ (P : Subgroup (Sz n)) ⊓ centralizer ((P : Subgroup (Sz n)) : Set (Sz n)))
    (hz1 : z ≠ 1) {x : Fin 4 → F n} (h : act n z x - x ∈ series n P 1) : x ∈ series n P 3 := by
  obtain ⟨g, w, hw, rfl, hser⟩ := exists_conj_rootElt_zero hn P hz hz1
  rw [hser, mem_map_act] at h ⊢
  rw [act_conj_sub] at h
  exact mem_flag_three_of_sub_rootElt_zero hw h

theorem commElt_series_three_eq_series_one (hn : 1 ≤ n) (P : Sylow 2 (Sz n)) {z : Sz n}
    (hz : z ∈ (P : Subgroup (Sz n)) ⊓ centralizer ((P : Subgroup (Sz n)) : Set (Sz n)))
    (hz1 : z ≠ 1) : commElt n z (series n P 3) = series n P 1 := by
  obtain ⟨g, w, hw, rfl, hser⟩ := exists_conj_rootElt_zero hn P hz hz1
  rw [hser, hser, commElt_conj, commElt_rootElt_zero_flag_three hw]

theorem commElt_top_eq_series_three (hn : 1 ≤ n) (P : Sylow 2 (Sz n)) {s : Sz n}
    (hs : s ∈ (P : Subgroup (Sz n)))
    (hs' : s ∉ centralizer ((P : Subgroup (Sz n)) : Set (Sz n))) :
    commElt n s ⊤ = series n P 3 := by
  have hle : commElt n s ⊤ ≤ series n P 3 := by
    intro y hy
    obtain ⟨v, -, rfl⟩ := (mem_commElt n).mp hy
    exact sub_mem_comm n hs (AddSubgroup.mem_top v)
  refine AddSubgroup.eq_of_le_of_card_ge hle ?_
  set f := act n s - AddMonoidHom.id (Fin 4 → F n) with hf
  have hker : f.ker = series n P 1 := (fixElt_eq_series_one hn P hs hs').1
  have hrange : commElt n s ⊤ = f.range := by
    rw [commElt, AddMonoidHom.range_eq_map]
  have hV : Nat.card (Fin 4 → F n) = (2 ^ (2 * n + 1)) ^ 4 := by
    rw [← AddSubgroup.card_top]
    exact SzNatural.card_top n
  have h := AddSubgroup.card_ker_mul_card_range f
  rw [hker, ← hrange, card_series hn P (i := 1) (by norm_num), pow_one, hV] at h
  rw [card_series hn P (i := 3) (by norm_num)]
  have hq : 0 < 2 ^ (2 * n + 1) := by positivity
  have : 2 ^ (2 * n + 1) * (2 ^ (2 * n + 1)) ^ 3 =
      2 ^ (2 * n + 1) * Nat.card (commElt n s ⊤) := by
    rw [h]
    ring
  exact (Nat.eq_of_mul_eq_mul_left hq this).le

end NatModule

section Core

open SzNatural
open scoped commutatorElement IsMulCommutative

variable {n : ℕ}

@[expose] noncomputable def seriesPow (P : Subgroup (Sz n)) (k i : ℕ) :
    Subgroup (Multiplicative (Fin k → Fin 4 → F n)) where
  carrier := {v | ∀ j, Multiplicative.toAdd v j ∈ series n P i}
  mul_mem' {_ _} ha hb j := (series n P i).add_mem (ha j) (hb j)
  one_mem' _ := (series n P i).zero_mem
  inv_mem' {_} ha j := (series n P i).neg_mem (ha j)

theorem mem_seriesPow {P : Subgroup (Sz n)} {k i : ℕ}
    {v : Multiplicative (Fin k → Fin 4 → F n)} :
    v ∈ seriesPow P k i ↔ ∀ j, Multiplicative.toAdd v j ∈ series n P i :=
  Iff.rfl

theorem card_seriesPow (P : Subgroup (Sz n)) (k i : ℕ) :
    Nat.card (seriesPow P k i) = Nat.card (series n P i) ^ k := by
  have e : seriesPow P k i ≃ (Fin k → series n P i) :=
    { toFun := fun v j => ⟨Multiplicative.toAdd (v : Multiplicative (Fin k → Fin 4 → F n)) j, v.2 j⟩
      invFun := fun f => ⟨Multiplicative.ofAdd fun j => (f j : Fin 4 → F n), fun j => (f j).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin]

theorem card_eq_card_ker_inf_mul_card_map {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (A : Subgroup G) : Nat.card A = Nat.card (f.ker ⊓ A : Subgroup G) * Nat.card (A.map f) := by
  rw [card_map_eq_relIndex, mul_comm]
  exact (Subgroup.relIndex_mul_card f.ker A).symm

structure Setting28Sz {H : Type u} [Group H] {k : ℕ} (ψ : H →* Sz n)
    (c : ψ.ker →* Multiplicative (Fin k → Fin 4 → F n)) (S W : Subgroup H)
    (P : Sylow 2 (Sz n)) : Prop where
  one_le_n : 1 ≤ n
  one_le_k : 1 ≤ k
  surj : Function.Surjective c
  central : ∀ x : ψ.ker, c x = 1 → ∀ h : H, h * x = x * h
  conj : ∀ (h : H) (x y : ψ.ker), (y : H) = h * x * h⁻¹ → ∀ j,
    Multiplicative.toAdd (c y) j = act n (ψ h) (Multiplicative.toAdd (c x) j)
  map_S : S.map ψ = P
  ker_le : ψ.ker ≤ S
  elemAb : IsElemAbelian 2 W
  le : W ≤ S
  map_W : W.map ψ = (P : Subgroup (Sz n)) ⊓ centralizer ((P : Subgroup (Sz n)) : Set (Sz n))
  normalizes : S ≤ normalizer (W : Set H)
  card_P : Nat.card (P : Subgroup (Sz n)) = (2 ^ (2 * n + 1)) ^ 2
  card_Z : Nat.card ((P : Subgroup (Sz n)) ⊓ centralizer ((P : Subgroup (Sz n)) : Set (Sz n)) :
    Subgroup (Sz n)) = 2 ^ (2 * n + 1)
  sq_mem : ∀ p ∈ (P : Subgroup (Sz n)),
    p ^ 2 ∈ (P : Subgroup (Sz n)) ⊓ centralizer ((P : Subgroup (Sz n)) : Set (Sz n))

namespace Setting28Sz

variable {H : Type u} [Group H] {k : ℕ} {ψ : H →* Sz n}
  {c : ψ.ker →* Multiplicative (Fin k → Fin 4 → F n)} {S W : Subgroup H} {P : Sylow 2 (Sz n)}

@[expose] noncomputable def xSub (c : ψ.ker →* Multiplicative (Fin k → Fin 4 → F n))
    (P : Subgroup (Sz n)) (i : ℕ) : Subgroup H :=
  ((seriesPow P k i).comap c).map ψ.ker.subtype

theorem mem_xSub {P' : Subgroup (Sz n)} {i : ℕ} {g : H} :
    g ∈ xSub c P' i ↔
      ∃ x : ψ.ker, (x : H) = g ∧ ∀ j, Multiplicative.toAdd (c x) j ∈ series n P' i := by
  simp only [xSub, Subgroup.mem_map, Subgroup.mem_comap, mem_seriesPow, Subgroup.coe_subtype]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, rfl, hx⟩
  · rintro ⟨x, rfl, hx⟩
    exact ⟨x, hx, rfl⟩

@[expose] noncomputable def cSub (c : ψ.ker →* Multiplicative (Fin k → Fin 4 → F n))
    (W : Subgroup H) (P : Subgroup (Sz n)) : Subgroup H :=
  W ⊓ xSub c P 1

theorem toAdd_mul (x y : ψ.ker) :
    Multiplicative.toAdd (c (x * y)) = Multiplicative.toAdd (c x) + Multiplicative.toAdd (c y) := by
  rw [map_mul, _root_.toAdd_mul]

theorem toAdd_inv (x : ψ.ker) :
    Multiplicative.toAdd (c x⁻¹) = - Multiplicative.toAdd (c x) := by
  rw [map_inv, _root_.toAdd_inv]

theorem conj_mem_ker (h : H) (x : ψ.ker) : h * (x : H) * h⁻¹ ∈ ψ.ker :=
  (inferInstance : ψ.ker.Normal).conj_mem _ x.2 h

theorem mem_series_two (D : Setting28Sz ψ c S W P) (x : ψ.ker)
    (hx : ∀ w ∈ W, w * (x : H) = x * w) (j : Fin k) :
    Multiplicative.toAdd (c x) j ∈ series n P 2 := by
  rw [series_two, mem_fix]
  intro z hz
  rw [← D.map_W] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact (D.conj w x x (by rw [hx w hw, mul_inv_cancel_right]) j).symm

theorem two_le_q : 2 ≤ 2 ^ (2 * n + 1) :=
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (2 * n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem exists_mem_ne_one (D : Setting28Sz ψ c S W P) : ∃ w ∈ W, ψ w ≠ 1 := by
  have hne : (P : Subgroup (Sz n)) ⊓ centralizer ((P : Subgroup (Sz n)) : Set (Sz n)) ≠ ⊥ := by
    intro h
    have h1 := D.card_Z
    rw [h, Subgroup.card_bot] at h1
    have := two_le_q (n := n)
    omega
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  rw [← D.map_W] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact ⟨w, hw, fun h => hz1 (Subtype.ext h)⟩

theorem exists_mem_of_mem_series_two (D : Setting28Sz ψ c S W P)
    (v : Fin k → Fin 4 → F n) (hv : ∀ j, v j ∈ series n P 2) :
    ∃ y : ψ.ker, (y : H) ∈ W ∧ Multiplicative.toAdd (c y) = v := by
  obtain ⟨w₀, hw₀, hw₀1⟩ := D.exists_mem_ne_one
  have hz : ψ w₀ ∈ (P : Subgroup (Sz n)) ⊓ centralizer ((P : Subgroup (Sz n)) : Set (Sz n)) :=
    D.map_W ▸ ⟨w₀, hw₀, rfl⟩
  have hcomm := (fixElt_eq_series_two D.one_le_n P hz hw₀1).2
  have hu : ∀ j, ∃ u, act n (ψ w₀) u - u = v j := fun j => by
    have := hv j
    rw [← hcomm, mem_commElt] at this
    obtain ⟨u, -, hu⟩ := this
    exact ⟨u, hu⟩
  choose u hu using hu
  obtain ⟨x, hx⟩ := D.surj (Multiplicative.ofAdd u)
  set x' : ψ.ker := ⟨w₀ * x * w₀⁻¹, conj_mem_ker w₀ x⟩ with hx'
  refine ⟨x' * x⁻¹, ?_, ?_⟩
  · have hxN : (x : H) ∈ normalizer (W : Set H) := D.normalizes (D.ker_le x.2)
    have h1 : (x : H) * w₀⁻¹ * (x : H)⁻¹ ∈ W := (mem_normalizer_iff.mp hxN _).mp (W.inv_mem hw₀)
    have e : ((x' * x⁻¹ : ψ.ker) : H) = w₀ * ((x : H) * w₀⁻¹ * (x : H)⁻¹) := by
      rw [Subgroup.coe_mul, hx', Subgroup.coe_inv]
      group
    rw [e]
    exact W.mul_mem hw₀ h1
  · funext j
    have h1 : Multiplicative.toAdd (c x') j = act n (ψ w₀) (Multiplicative.toAdd (c x) j) :=
      D.conj w₀ x x' rfl j
    rw [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, h1, hx, toAdd_ofAdd, ← sub_eq_add_neg,
      hu j]

theorem map_mem_of_centralizes (D : Setting28Sz ψ c S W P)
    {g : H} (hg : g ∈ S)
    (hgW : ∀ w ∈ W, g * w = w * g) :
    ψ g ∈ (P : Subgroup (Sz n)) ⊓ centralizer ((P : Subgroup (Sz n)) : Set (Sz n)) := by
  have hgP : ψ g ∈ (P : Subgroup (Sz n)) := D.map_S ▸ ⟨g, hg, rfl⟩
  refine ⟨hgP, ?_⟩
  by_contra hgC
  have hfix := (fixElt_eq_series_one D.one_le_n P hgP hgC).1
  have hlt : ¬ series n P 2 ≤ series n P 1 := by
    intro hle
    have h1 := AddSubgroup.card_le_of_le hle
    rw [card_series D.one_le_n P (i := 2) (by norm_num),
      card_series D.one_le_n P (i := 1) (by norm_num)] at h1
    have := two_le_q (n := n)
    nlinarith
  obtain ⟨v₀, hv₀2, hv₀1⟩ := SetLike.not_le_iff_exists.mp hlt
  set j₀ : Fin k := ⟨0, D.one_le_k⟩
  obtain ⟨y, hyW, hy⟩ := D.exists_mem_of_mem_series_two (Pi.single j₀ v₀) fun j => by
    by_cases hj : j = j₀
    · subst hj
      rw [Pi.single_eq_same]
      exact hv₀2
    · rw [Pi.single_eq_of_ne hj]
      exact (series n P 2).zero_mem
  have h1 := D.conj g y y (by rw [hgW _ hyW, mul_inv_cancel_right]) j₀
  rw [hy, Pi.single_eq_same] at h1
  apply hv₀1
  rw [← hfix, mem_fixElt]
  exact h1.symm

@[expose] noncomputable def qSub (D : Setting28Sz ψ c S W P) : Subgroup H where
  carrier := {g | g ∈ S ∧ (∀ w ∈ W, g * w * g⁻¹ * w⁻¹ ∈ cSub c W P) ∧
    ∀ y ∈ cSub c W P, g * y * g⁻¹ = y}
  mul_mem' := by
    rintro g₁ g₂ ⟨h₁S, h₁W, h₁C⟩ ⟨h₂S, h₂W, h₂C⟩
    refine ⟨S.mul_mem h₁S h₂S, fun w hw => ?_, fun y hy => ?_⟩
    · have e : g₁ * g₂ * w * (g₁ * g₂)⁻¹ * w⁻¹ =
          (g₁ * (g₂ * w * g₂⁻¹ * w⁻¹) * g₁⁻¹) * (g₁ * w * g₁⁻¹ * w⁻¹) := by group
      rw [e, h₁C _ (h₂W w hw)]
      exact (cSub c W P).mul_mem (h₂W w hw) (h₁W w hw)
    · have e : g₁ * g₂ * y * (g₁ * g₂)⁻¹ = g₁ * (g₂ * y * g₂⁻¹) * g₁⁻¹ := by group
      rw [e, h₂C y hy, h₁C y hy]
  one_mem' := ⟨S.one_mem, fun w _ => by simp [(cSub c W P).one_mem], fun y _ => by simp⟩
  inv_mem' := by
    rintro g ⟨hS, hW, hC⟩
    refine ⟨S.inv_mem hS, fun w hw => ?_, fun y hy => ?_⟩
    · have hw' : g⁻¹ * w * g ∈ W := by
        have := (mem_normalizer_iff.mp (D.normalizes (S.inv_mem hS)) w).mp hw
        rwa [inv_inv] at this
      have e : g⁻¹ * w * g⁻¹⁻¹ * w⁻¹ = (g * (g⁻¹ * w * g) * g⁻¹ * (g⁻¹ * w * g)⁻¹)⁻¹ := by group
      rw [e]
      exact (cSub c W P).inv_mem (hW _ hw')
    · calc g⁻¹ * y * g⁻¹⁻¹ = g⁻¹ * (g * y * g⁻¹) * g := by rw [hC y hy, inv_inv]
        _ = y := by group

theorem mem_qSub (D : Setting28Sz ψ c S W P) {g : H} :
    g ∈ D.qSub ↔ g ∈ S ∧ (∀ w ∈ W, g * w * g⁻¹ * w⁻¹ ∈ cSub c W P) ∧
      ∀ y ∈ cSub c W P, g * y * g⁻¹ = y :=
  Iff.rfl

theorem le_qSub (D : Setting28Sz ψ c S W P) : W ≤ D.qSub := by
  intro w hw
  have hcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (D.elemAb.1.is_comm.comm (⟨a, ha⟩ : W) ⟨b, hb⟩)
  refine ⟨D.le hw, fun w' hw' => ?_, fun y hy => ?_⟩
  · rw [hcomm w hw w' hw', mul_inv_cancel_right, mul_inv_cancel]
    exact (cSub c W P).one_mem
  · rw [hcomm w hw y hy.1, mul_inv_cancel_right]

theorem central_of_toAdd_eq_zero (D : Setting28Sz ψ c S W P) (x : ψ.ker)
    (h : Multiplicative.toAdd (c x) = 0) (g : H) : g * x = x * g :=
  D.central x (by rw [← ofAdd_toAdd (c x), h, ofAdd_zero]) g

theorem toAdd_conj (D : Setting28Sz ψ c S W P) (h : H) (x : ψ.ker) :
    Multiplicative.toAdd (c ⟨h * x * h⁻¹, conj_mem_ker h x⟩) =
      fun j => act n (ψ h) (Multiplicative.toAdd (c x) j) :=
  funext (D.conj h x _ rfl)

theorem commute_of_mem (D : Setting28Sz ψ c S W P) {a b : H} (ha : a ∈ W) (hb : b ∈ W) :
    Commute a b :=
  congrArg Subtype.val (D.elemAb.1.is_comm.comm (⟨a, ha⟩ : W) ⟨b, hb⟩)

theorem inv_eq_of_mem (D : Setting28Sz ψ c S W P) {a : H} (ha : a ∈ W) : a⁻¹ = a := by
  have h := D.elemAb.2 a ha
  rw [pow_two] at h
  exact inv_eq_of_mul_eq_one_right h

theorem exists_mem_not_centralizer (D : Setting28Sz ψ c S W P) :
    ∃ s ∈ S, ψ s ∈ (P : Subgroup (Sz n)) ∧
      ψ s ∉ centralizer ((P : Subgroup (Sz n)) : Set (Sz n)) := by
  have hne : ¬ (P : Subgroup (Sz n)) ≤ centralizer ((P : Subgroup (Sz n)) : Set (Sz n)) := by
    intro hle
    have h1 := D.card_Z
    rw [inf_eq_left.mpr hle, D.card_P] at h1
    have := two_le_q (n := n)
    nlinarith
  obtain ⟨p, hp, hpC⟩ := SetLike.not_le_iff_exists.mp hne
  rw [← D.map_S] at hp
  obtain ⟨s, hs, rfl⟩ := hp
  exact ⟨s, hs, D.map_S ▸ ⟨s, hs, rfl⟩, hpC⟩

theorem commutatorElement_mul_mul_eq {a w x b : H} (haw : Commute a w)
    (hax : Commute a x) (hab : Commute a b) (hbw : Commute b w) : ⁅a * w, x * b⁆ = ⁅w, x⁆ := by
  have h1 : b * w⁻¹ * a⁻¹ * b⁻¹ = w⁻¹ * a⁻¹ :=
    calc b * w⁻¹ * a⁻¹ * b⁻¹ = w⁻¹ * (b * a⁻¹) * b⁻¹ := by rw [hbw.inv_right.eq]; group
      _ = w⁻¹ * (a⁻¹ * b) * b⁻¹ := by rw [hab.symm.inv_right.eq]
      _ = w⁻¹ * a⁻¹ := by group
  have h2 : a * (w * x * w⁻¹) * a⁻¹ = w * x * w⁻¹ := by
    rw [((haw.mul_right hax).mul_right haw.inv_right).eq, mul_inv_cancel_right]
  calc ⁅a * w, x * b⁆ = a * w * x * (b * w⁻¹ * a⁻¹ * b⁻¹) * x⁻¹ := by
        rw [commutatorElement_def]; group
    _ = a * w * x * (w⁻¹ * a⁻¹) * x⁻¹ := by rw [h1]
    _ = a * (w * x * w⁻¹) * a⁻¹ * x⁻¹ := by group
    _ = w * x * w⁻¹ * x⁻¹ := by rw [h2]
    _ = ⁅w, x⁆ := by rw [commutatorElement_def]

theorem conj_eq_of_mem_xSub_three (D : Setting28Sz ψ c S W P)
    {x : H} (hx : x ∈ xSub c P 3) {y : H} (hy : y ∈ cSub c W P) : x * y * x⁻¹ = y := by
  obtain ⟨xk, rfl, hx3⟩ := mem_xSub.mp hx
  obtain ⟨-, hy1⟩ := hy
  obtain ⟨yk, rfl, hyk⟩ := mem_xSub.mp hy1
  obtain ⟨s₀, -, hs₀P, hs₀C⟩ := D.exists_mem_not_centralizer
  have hcomm := commElt_top_eq_series_three D.one_le_n P hs₀P hs₀C
  have hu : ∀ j, ∃ u, act n (ψ s₀) u - u = Multiplicative.toAdd (c xk) j := fun j => by
    have := hx3 j
    rw [← hcomm, mem_commElt] at this
    obtain ⟨u, -, hu⟩ := this
    exact ⟨u, hu⟩
  choose u hu using hu
  obtain ⟨x', hx'⟩ := D.surj (Multiplicative.ofAdd u)
  set x'' : ψ.ker := ⟨s₀ * x' * s₀⁻¹, conj_mem_ker s₀ x'⟩ * x'⁻¹ with hx''
  have hκ := D.central_of_toAdd_eq_zero (x''⁻¹ * xk) (by
    funext j
    rw [toAdd_mul, toAdd_inv, hx'', toAdd_mul, toAdd_inv, D.toAdd_conj, hx', toAdd_ofAdd]
    simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply, ← hu j]
    abel)
  set κ₁ : ψ.ker := yk * ⟨s₀ * yk⁻¹ * s₀⁻¹, conj_mem_ker s₀ yk⁻¹⟩ with hκ₁
  have hκ₁c := D.central_of_toAdd_eq_zero κ₁ (by
    funext j
    rw [hκ₁, toAdd_mul, D.toAdd_conj, toAdd_inv]
    simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply, map_neg]
    have hfix : act n (ψ s₀) (Multiplicative.toAdd (c yk) j) = Multiplicative.toAdd (c yk) j :=
      (SzNatural.mem_fix n).mp (hyk j) _ hs₀P
    rw [hfix, add_neg_cancel])
  have hyk1 : ψ (yk : H) = 1 := yk.2
  set κ₂ : ψ.ker := ⟨(yk : H) * x' * (yk : H)⁻¹, conj_mem_ker (yk : H) x'⟩ * x'⁻¹ with hκ₂
  have hκ₂c := D.central_of_toAdd_eq_zero κ₂ (by
    funext j
    rw [hκ₂, toAdd_mul, D.toAdd_conj, toAdd_inv, hyk1]
    simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply, act_one, add_neg_cancel])
  have e1 : (yk : H) * s₀ * (yk : H)⁻¹ = s₀ * κ₁ := by
    rw [hκ₁c s₀, hκ₁]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have e2 : (yk : H) * x' * (yk : H)⁻¹ = x' * κ₂ := by
    rw [hκ₂c (x' : H), hκ₂]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have e3 : (yk : H) * (x'' : H) * (yk : H)⁻¹ = x'' := by
    have : (x'' : H) = ⁅s₀, (x' : H)⁆ := by
      rw [hx'', commutatorElement_def]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [this, ← MulAut.conj_apply, map_commutatorElement, MulAut.conj_apply, MulAut.conj_apply,
      e1, e2, commutatorElement_mul_central (fun g => (hκ₁c g).symm) (fun g => (hκ₂c g).symm)]
  have e4 : (xk : H) = x'' * (x''⁻¹ * xk : ψ.ker) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  have e5 : (yk : H) * xk * (yk : H)⁻¹ = xk := by
    rw [e4]
    calc (yk : H) * (x'' * ((x''⁻¹ * xk : ψ.ker) : H)) * (yk : H)⁻¹ =
        ((yk : H) * x'' * (yk : H)⁻¹) * ((yk : H) * ((x''⁻¹ * xk : ψ.ker) : H) * (yk : H)⁻¹) := by
          group
      _ = x'' * ((x''⁻¹ * xk : ψ.ker) : H) := by
          rw [e3, hκ (yk : H), mul_inv_cancel_right]
  have e6 : (yk : H) * xk = xk * yk := by
    calc (yk : H) * xk = (yk : H) * xk * (yk : H)⁻¹ * yk := by group
      _ = xk * yk := by rw [e5]
  rw [← e6, mul_inv_cancel_right]

theorem xSub_three_le_qSub (D : Setting28Sz ψ c S W P) :
    xSub c P 3 ≤ D.qSub := by
  intro x hx
  refine ⟨?_, fun w hw => ?_, fun y hy => D.conj_eq_of_mem_xSub_three hx hy⟩
  · obtain ⟨xk, rfl, -⟩ := mem_xSub.mp hx
    exact D.ker_le xk.2
  · obtain ⟨xk, rfl, hx3⟩ := mem_xSub.mp hx
    have hxN : (xk : H) ∈ normalizer (W : Set H) := D.normalizes (D.ker_le xk.2)
    refine ⟨W.mul_mem ((mem_normalizer_iff.mp hxN w).mp hw) (W.inv_mem hw),
      mem_xSub.mpr ⟨xk * ⟨w * ((xk⁻¹ : ψ.ker) : H) * w⁻¹, conj_mem_ker w xk⁻¹⟩, ?_, fun j => ?_⟩⟩
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    · rw [toAdd_mul, D.toAdd_conj, toAdd_inv]
      simp only [Pi.add_apply, Pi.neg_apply, map_neg]
      by_cases hw1 : ψ w = 1
      · rw [hw1, act_one, add_neg_cancel]
        exact (series n P 1).zero_mem
      · have hz : ψ w ∈ (P : Subgroup (Sz n)) ⊓
            centralizer ((P : Subgroup (Sz n)) : Set (Sz n)) := D.map_W ▸ ⟨w, hw, rfl⟩
        have h1 : act n (ψ w) (Multiplicative.toAdd (c xk) j) - Multiplicative.toAdd (c xk) j ∈
            series n P 1 := by
          rw [← commElt_series_three_eq_series_one D.one_le_n P hz hw1, mem_commElt]
          exact ⟨_, hx3 j, rfl⟩
        have h2 := (series n P 1).neg_mem h1
        rwa [neg_sub, sub_eq_add_neg] at h2

theorem mem_qSub_of_mul_self (D : Setting28Sz ψ c S W P)
    {s w κ : H} (hs : s ∈ S) (hsC : ψ s ∉ centralizer ((P : Subgroup (Sz n)) : Set (Sz n)))
    (hw : w ∈ W) (hκ : ∀ g : H, g * κ = κ * g) (hsq : s * s = w * κ) : s ∈ D.qSub := by
  have hsP : ψ s ∈ (P : Subgroup (Sz n)) := D.map_S ▸ ⟨s, hs, rfl⟩
  have hsN : s ∈ normalizer (W : Set H) := D.normalizes hs
  have hfix1 := (fixElt_eq_series_one D.one_le_n P hsP hsC).1
  have hcomW : ∀ w' ∈ W, s * w' * s⁻¹ * w'⁻¹ ∈ cSub c W P := by
    intro w' hw'
    have hw'' : s * w' * s⁻¹ ∈ W := (mem_normalizer_iff.mp hsN w').mp hw'
    have hw'Z : ψ w' ∈ (P : Subgroup (Sz n)) ⊓
        centralizer ((P : Subgroup (Sz n)) : Set (Sz n)) := D.map_W ▸ ⟨w', hw', rfl⟩
    have hdk : s * w' * s⁻¹ * w'⁻¹ ∈ ψ.ker := by
      have hcm : Commute (ψ s) (ψ w') := mem_centralizer_iff.mp hw'Z.2 (ψ s) hsP
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hcm.eq]
      group
    refine ⟨W.mul_mem hw'' (W.inv_mem hw'), mem_xSub.mpr ⟨⟨_, hdk⟩, rfl, fun j => ?_⟩⟩
    have e2 : s * s * w' * (s * s)⁻¹ = w' := by
      rw [hsq]
      calc w * κ * w' * (w * κ)⁻¹ = w * (κ * w') * κ⁻¹ * w⁻¹ := by group
        _ = w * (w' * κ) * κ⁻¹ * w⁻¹ := by rw [← hκ w']
        _ = w * w' * w⁻¹ := by group
        _ = w' := by rw [(D.commute_of_mem hw hw').eq, mul_inv_cancel_right]
    have hfixd : s * (s * w' * s⁻¹ * w'⁻¹) * s⁻¹ = s * w' * s⁻¹ * w'⁻¹ := by
      calc s * (s * w' * s⁻¹ * w'⁻¹) * s⁻¹ = (s * s * w' * (s * s)⁻¹) * (s * w' * s⁻¹)⁻¹ := by
            group
        _ = w' * (s * w' * s⁻¹)⁻¹ := by rw [e2]
        _ = s * w' * s⁻¹ * w'⁻¹ := by
          rw [D.inv_eq_of_mem hw'', D.inv_eq_of_mem hw', (D.commute_of_mem hw' hw'').eq]
    have h1 := D.conj s ⟨_, hdk⟩ ⟨_, hdk⟩ hfixd.symm j
    rw [← hfix1, mem_fixElt]
    exact h1.symm
  refine ⟨hs, hcomW, fun y hy => ?_⟩
  obtain ⟨-, hy1⟩ := hy
  obtain ⟨yk, rfl, hyk⟩ := mem_xSub.mp hy1
  obtain ⟨w₀, hw₀, hw₀1⟩ := D.exists_mem_ne_one
  have hz₀ : ψ w₀ ∈ (P : Subgroup (Sz n)) ⊓ centralizer ((P : Subgroup (Sz n)) : Set (Sz n)) :=
    D.map_W ▸ ⟨w₀, hw₀, rfl⟩
  have hcomm₀ := commElt_series_three_eq_series_one D.one_le_n P hz₀ hw₀1
  have hv : ∀ j, ∃ v ∈ series n P 3, act n (ψ w₀) v - v = Multiplicative.toAdd (c yk) j :=
    fun j => by
      have := hyk j
      rwa [← hcomm₀, mem_commElt] at this
  choose v hv3 hv using hv
  obtain ⟨x₂, hx₂⟩ := D.surj (Multiplicative.ofAdd v)
  set y' : ψ.ker := ⟨w₀ * x₂ * w₀⁻¹, conj_mem_ker w₀ x₂⟩ * x₂⁻¹ with hy'
  have hκ' := D.central_of_toAdd_eq_zero (y'⁻¹ * yk) (by
    funext j
    rw [toAdd_mul, toAdd_inv, hy', toAdd_mul, toAdd_inv, D.toAdd_conj, hx₂, toAdd_ofAdd]
    simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply, ← hv j]
    abel)
  have hx₂3 : (x₂ : H) ∈ xSub c P 3 :=
    mem_xSub.mpr ⟨x₂, rfl, fun j => by rw [hx₂, toAdd_ofAdd]; exact hv3 j⟩
  have hd₀ := hcomW w₀ hw₀
  set d₀ := s * w₀ * s⁻¹ * w₀⁻¹ with hd₀def
  set b : ψ.ker := x₂⁻¹ * ⟨s * x₂ * s⁻¹, conj_mem_ker s x₂⟩ with hbdef
  have hc32 : comm n P (series n P 3) = series n P 2 :=
    comm_series D.one_le_n P (k := 2) (by norm_num)
  have hb2 : ∀ j, Multiplicative.toAdd (c b) j ∈ series n P 2 := fun j => by
    rw [hbdef, toAdd_mul, toAdd_inv, D.toAdd_conj, hx₂, toAdd_ofAdd]
    simp only [Pi.add_apply, Pi.neg_apply]
    rw [neg_add_eq_sub, ← hc32]
    exact sub_mem_comm n hsP (hv3 j)
  obtain ⟨yb, hybW, hyb⟩ := D.exists_mem_of_mem_series_two _ hb2
  have hκb := D.central_of_toAdd_eq_zero (yb⁻¹ * b) (by
    rw [toAdd_mul, toAdd_inv, hyb, neg_add_cancel])
  have e1 : s * w₀ * s⁻¹ = d₀ * w₀ := by rw [hd₀def]; group
  have e2 : s * (x₂ : H) * s⁻¹ = (x₂ * yb) * ((yb⁻¹ * b : ψ.ker) : H) := by
    rw [hbdef]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hcx : Commute d₀ (x₂ : H) := by
    have h := D.conj_eq_of_mem_xSub_three hx₂3 hd₀
    calc d₀ * x₂ = ((x₂ : H) * d₀ * (x₂ : H)⁻¹) * x₂ := by rw [h]
      _ = x₂ * d₀ := by group
  have e3 : s * (y' : H) * s⁻¹ = y' := by
    have hy'c : (y' : H) = ⁅w₀, (x₂ : H)⁆ := by
      rw [hy', commutatorElement_def]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have h1 := commutatorElement_mul_central (x := d₀ * w₀) (y := (x₂ : H) * yb) (z := 1)
      (z' := ((yb⁻¹ * b : ψ.ker) : H)) (fun g => by simp) (fun g => (hκb g).symm)
    rw [mul_one] at h1
    rw [hy'c, ← MulAut.conj_apply, map_commutatorElement, MulAut.conj_apply, MulAut.conj_apply,
      e1, e2, h1]
    exact commutatorElement_mul_mul_eq (D.commute_of_mem hd₀.1 hw₀) hcx
      (D.commute_of_mem hd₀.1 hybW) (D.commute_of_mem hybW hw₀)
  have e4 : (yk : H) = y' * ((y'⁻¹ * yk : ψ.ker) : H) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  rw [e4]
  calc s * (y' * ((y'⁻¹ * yk : ψ.ker) : H)) * s⁻¹ =
      (s * y' * s⁻¹) * (s * ((y'⁻¹ * yk : ψ.ker) : H) * s⁻¹) := by group
    _ = y' * ((y'⁻¹ * yk : ψ.ker) : H) := by rw [e3, hκ' s, mul_inv_cancel_right]

theorem exists_mul_mem_qSub (D : Setting28Sz ψ c S W P) {s : H}
    (hs : s ∈ S) (hsC : ψ s ∉ centralizer ((P : Subgroup (Sz n)) : Set (Sz n))) :
    ∃ x ∈ ψ.ker, s * x ∈ D.qSub := by
  have hsP : ψ s ∈ (P : Subgroup (Sz n)) := D.map_S ▸ ⟨s, hs, rfl⟩
  have hsN : s ∈ normalizer (W : Set H) := D.normalizes hs
  obtain ⟨w, hw, hws⟩ : ∃ w ∈ W, ψ w = ψ (s ^ 2) := by
    have h := D.sq_mem _ hsP
    rw [← map_pow, ← D.map_W] at h
    obtain ⟨w, hw, h⟩ := h
    exact ⟨w, hw, h⟩
  have hwZ : ψ w ∈ (P : Subgroup (Sz n)) ⊓ centralizer ((P : Subgroup (Sz n)) : Set (Sz n)) :=
    D.map_W ▸ ⟨w, hw, rfl⟩
  have hx₁ : w⁻¹ * s ^ 2 ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hws, inv_mul_cancel]
  set x₁ : ψ.ker := ⟨w⁻¹ * s ^ 2, hx₁⟩ with hx₁def
  have ha : s * w⁻¹ * s⁻¹ * w ∈ ψ.ker := by
    have hcm : Commute (ψ s) (ψ w) := mem_centralizer_iff.mp hwZ.2 (ψ s) hsP
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hcm.inv_right.eq]
    group
  set a : ψ.ker := ⟨s * w⁻¹ * s⁻¹ * w, ha⟩ with hadef
  have haW : (a : H) ∈ W := W.mul_mem ((mem_normalizer_iff.mp hsN _).mp (W.inv_mem hw)) hw
  have hx₁3 : ∀ j, Multiplicative.toAdd (c x₁) j ∈ series n P 3 := fun j => by
    apply mem_series_three_of_sub_mem_series_two D.one_le_n P hsP hsC
    have h1 := D.conj s x₁ (a * x₁) (by rw [Subgroup.coe_mul, hadef, hx₁def]; group) j
    rw [toAdd_mul, Pi.add_apply] at h1
    rw [← h1, add_sub_cancel_right]
    exact D.mem_series_two a (fun w' hw' => (D.commute_of_mem hw' haW).eq) j
  have hs'P : ψ s⁻¹ ∈ (P : Subgroup (Sz n)) := by
    rw [map_inv]
    exact (P : Subgroup (Sz n)).inv_mem hsP
  have hs'C : ψ s⁻¹ ∉ centralizer ((P : Subgroup (Sz n)) : Set (Sz n)) := by
    rw [map_inv]
    intro h
    exact hsC (by simpa using (centralizer _).inv_mem h)
  have hcomm := commElt_top_eq_series_three D.one_le_n P hs'P hs'C
  have hu : ∀ j, ∃ u, act n (ψ s⁻¹) u - u = Multiplicative.toAdd (c x₁) j := fun j => by
    have := hx₁3 j
    rw [← hcomm, mem_commElt] at this
    obtain ⟨u, -, hu⟩ := this
    exact ⟨u, hu⟩
  choose u hu using hu
  obtain ⟨x, hx⟩ := D.surj (Multiplicative.ofAdd u)
  refine ⟨x, x.2, ?_⟩
  set κ : ψ.ker := x₁ * ⟨s⁻¹ * x * s⁻¹⁻¹, conj_mem_ker s⁻¹ x⟩ * x with hκdef
  have h2 : ∀ v : Fin 4 → F n, v + v = 0 := fun v => funext fun i => by
    rw [Pi.add_apply, ← two_mul, two_eq_zero n, zero_mul]
    rfl
  have hκc := D.central_of_toAdd_eq_zero κ (by
    funext j
    rw [hκdef, toAdd_mul, toAdd_mul, D.toAdd_conj, hx, toAdd_ofAdd]
    simp only [Pi.add_apply, Pi.zero_apply]
    rw [← hu j]
    calc act n (ψ s⁻¹) (u j) - u j + act n (ψ s⁻¹) (u j) + u j =
        act n (ψ s⁻¹) (u j) + act n (ψ s⁻¹) (u j) := by abel
      _ = 0 := h2 _)
  have hψx : ψ (x : H) = 1 := x.2
  refine D.mem_qSub_of_mul_self (S.mul_mem hs (D.ker_le x.2)) ?_ hw hκc ?_
  · rwa [map_mul, hψx, mul_one]
  · rw [hκdef]
    simp only [Subgroup.coe_mul, hx₁def]
    group

theorem map_qSub (D : Setting28Sz ψ c S W P) :
    D.qSub.map ψ = P := by
  refine le_antisymm ?_ fun p hp => ?_
  · rw [← D.map_S]
    exact Subgroup.map_mono fun g hg => hg.1
  · by_cases hpC : p ∈ centralizer ((P : Subgroup (Sz n)) : Set (Sz n))
    · have hpZ : p ∈ W.map ψ := by
        rw [D.map_W]
        exact ⟨hp, hpC⟩
      exact Subgroup.map_mono D.le_qSub hpZ
    · rw [← D.map_S] at hp
      obtain ⟨s, hs, rfl⟩ := hp
      obtain ⟨x, hx, hsx⟩ := D.exists_mul_mem_qSub hs hpC
      refine ⟨s * x, hsx, ?_⟩
      rw [map_mul, MonoidHom.mem_ker.mp hx, mul_one]

theorem card_xSub (D : Setting28Sz ψ c S W P) (i : ℕ) :
    Nat.card (xSub c (P : Subgroup (Sz n)) i) =
      Nat.card c.ker * Nat.card (seriesPow (P : Subgroup (Sz n)) k i) := by
  rw [xSub, Subgroup.card_map_of_injective ψ.ker.subtype_injective,
    card_eq_card_ker_inf_mul_card_map c, Subgroup.map_comap_eq_self_of_surjective D.surj,
    inf_eq_left.mpr (MonoidHom.ker_le_comap c _)]

theorem xSub_le_ker (P' : Subgroup (Sz n)) (i : ℕ) : xSub c P' i ≤ ψ.ker := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem map_subgroupOf_W (D : Setting28Sz ψ c S W P) :
    (W.subgroupOf ψ.ker).map c = seriesPow (P : Subgroup (Sz n)) k 2 := by
  refine le_antisymm ?_ fun v hv => ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact D.mem_series_two y fun w hw => (D.commute_of_mem hw hy).eq
  · obtain ⟨y, hyW, hy⟩ := D.exists_mem_of_mem_series_two (Multiplicative.toAdd v) hv
    exact ⟨y, hyW, by rw [← ofAdd_toAdd (c y), hy, ofAdd_toAdd]⟩

theorem map_subgroupOf_cSub (D : Setting28Sz ψ c S W P) :
    ((cSub c W P).subgroupOf ψ.ker).map c = seriesPow (P : Subgroup (Sz n)) k 1 := by
  refine le_antisymm ?_ fun v hv => ?_
  · rintro _ ⟨y, ⟨-, hy⟩, rfl⟩
    obtain ⟨x, hx, hx1⟩ := mem_xSub.mp hy
    rwa [Subtype.ext hx] at hx1
  · have hv2 : ∀ j, Multiplicative.toAdd v j ∈ series n P 2 := fun j =>
      series_mono D.one_le_n P (by norm_num) (hv j)
    obtain ⟨y, hyW, hy⟩ := D.exists_mem_of_mem_series_two (Multiplicative.toAdd v) hv2
    refine ⟨y, ⟨hyW, mem_xSub.mpr ⟨y, rfl, fun j => ?_⟩⟩, ?_⟩
    · rw [hy]
      exact hv j
    · rw [← ofAdd_toAdd (c y), hy, ofAdd_toAdd]

theorem ker_inf_subgroupOf_cSub (D : Setting28Sz ψ c S W P) :
    c.ker ⊓ (cSub c W P).subgroupOf ψ.ker = c.ker ⊓ W.subgroupOf ψ.ker := by
  refine le_antisymm (inf_le_inf_left _ fun y hy => hy.1) fun y ⟨hyk, hyW⟩ => ⟨hyk, hyW, ?_⟩
  refine mem_xSub.mpr ⟨y, rfl, fun j => ?_⟩
  rw [MonoidHom.mem_ker.mp hyk, toAdd_one]
  exact (series n P 1).zero_mem

theorem card_subgroupOf_ker (A : Subgroup H) :
    Nat.card (A.subgroupOf ψ.ker) = Nat.card (ψ.ker ⊓ A : Subgroup H) := by
  rw [← Subgroup.card_map_of_injective ψ.ker.subtype_injective, Subgroup.subgroupOf_map_subtype,
    inf_comm]

theorem relIndex_centralizer_le [Finite H]
    (D : Setting28Sz ψ c S W P) :
    (W ⊓ centralizer (D.qSub : Set H)).relIndex W ≤
      (D.qSub ⊓ centralizer (W : Set H)).relIndex D.qSub := by
  set q := 2 ^ (2 * n + 1) with hq
  set a := Nat.card (c.ker ⊓ W.subgroupOf ψ.ker : Subgroup ψ.ker) with ha
  set b := Nat.card c.ker with hb
  have hN : ∀ i ≤ 4, Nat.card (seriesPow (P : Subgroup (Sz n)) k i) = (q ^ i) ^ k := by
    intro i hi
    rw [card_seriesPow, card_series D.one_le_n P hi]
  have hW : Nat.card W = a * (q ^ 2) ^ k * q := by
    rw [card_eq_card_ker_inf_mul_card_map ψ W, D.map_W, D.card_Z, ← card_subgroupOf_ker,
      card_eq_card_ker_inf_mul_card_map c, map_subgroupOf_W D, hN 2 (by norm_num)]
  have hC : Nat.card (cSub c W P) = a * (q ^ 1) ^ k := by
    have hle : cSub c W P ≤ ψ.ker := inf_le_right.trans (xSub_le_ker _ 1)
    have e : Nat.card (cSub c W P) = Nat.card ((cSub c W P).subgroupOf ψ.ker) := by
      rw [card_subgroupOf_ker, inf_eq_right.mpr hle]
    rw [e, card_eq_card_ker_inf_mul_card_map c, map_subgroupOf_cSub D,
      ker_inf_subgroupOf_cSub D, hN 1 (by norm_num)]
  have hQ : b * (q ^ 3) ^ k * q ^ 2 ≤ Nat.card D.qSub := by
    rw [card_eq_card_ker_inf_mul_card_map ψ D.qSub, map_qSub D, D.card_P]
    refine Nat.mul_le_mul_right _ ?_
    rw [hb, ← hN 3 (by norm_num), ← card_xSub D 3]
    exact Subgroup.card_le_of_le (le_inf (xSub_le_ker _ 3) D.xSub_three_le_qSub)
  have hSW : Nat.card (S ⊓ centralizer (W : Set H) : Subgroup H) ≤ b * (q ^ 2) ^ k * q := by
    rw [card_eq_card_ker_inf_mul_card_map ψ]
    refine Nat.mul_le_mul ?_ ?_
    · rw [hb, ← hN 2 (by norm_num), ← card_xSub D 2]
      refine Subgroup.card_le_of_le fun g hg => mem_xSub.mpr ⟨⟨g, hg.1⟩, rfl, ?_⟩
      exact D.mem_series_two ⟨g, hg.1⟩ fun w hw => (mem_centralizer_iff.mp hg.2.2 w hw)
    · refine (Subgroup.card_le_of_le ?_).trans D.card_Z.le
      rintro _ ⟨g, ⟨hgS, hgW⟩, rfl⟩
      exact D.map_mem_of_centralizes hgS fun w hw => (mem_centralizer_iff.mp hgW w hw).symm
  have h₁ := Subgroup.relIndex_mul_card (W ⊓ centralizer (D.qSub : Set H)) W
  rw [inf_eq_left.mpr inf_le_left] at h₁
  have h₂ := Subgroup.relIndex_mul_card (D.qSub ⊓ centralizer (W : Set H)) D.qSub
  rw [inf_eq_left.mpr inf_le_left] at h₂
  have hWC : Nat.card (cSub c W P) ≤ Nat.card (W ⊓ centralizer (D.qSub : Set H) : Subgroup H) :=
    Subgroup.card_le_of_le (le_inf inf_le_left fun y hy =>
      mem_centralizer_iff.mpr fun g hg => by
        have h := hg.2.2 y hy
        calc g * y = g * y * g⁻¹ * g := by group
          _ = y * g := by rw [h])
  have hQC : Nat.card (D.qSub ⊓ centralizer (W : Set H) : Subgroup H) ≤
      Nat.card (S ⊓ centralizer (W : Set H) : Subgroup H) :=
    Subgroup.card_le_of_le (inf_le_inf_right _ fun g hg => hg.1)
  have hpos₁ : 0 < Nat.card (W ⊓ centralizer (D.qSub : Set H) : Subgroup H) := Nat.card_pos
  have hpos₂ : 0 < Nat.card (D.qSub ⊓ centralizer (W : Set H) : Subgroup H) := Nat.card_pos
  set r₁ := (W ⊓ centralizer (D.qSub : Set H)).relIndex W
  set r₂ := (D.qSub ⊓ centralizer (W : Set H)).relIndex D.qSub
  set m₁ := Nat.card (W ⊓ centralizer (D.qSub : Set H) : Subgroup H)
  set m₂ := Nat.card (D.qSub ⊓ centralizer (W : Set H) : Subgroup H)
  have key : r₁ * (m₁ * m₂) ≤ r₂ * (m₁ * m₂) :=
    calc r₁ * (m₁ * m₂) = Nat.card W * m₂ := by rw [← mul_assoc, h₁]
      _ ≤ (a * (q ^ 2) ^ k * q) * (b * (q ^ 2) ^ k * q) :=
          Nat.mul_le_mul hW.le (hQC.trans hSW)
      _ = (b * (q ^ 3) ^ k * q ^ 2) * (a * (q ^ 1) ^ k) := by
          simp only [← pow_mul]
          ring
      _ ≤ Nat.card D.qSub * m₁ := Nat.mul_le_mul hQ (hC ▸ hWC)
      _ = r₂ * (m₁ * m₂) := by rw [← h₂]; ring
  exact Nat.le_of_mul_le_mul_right key (Nat.mul_pos hpos₁ hpos₂)

theorem ale_one [Finite H] [IsMulCommutative W]
    (D : Setting28Sz ψ c S W P) : ALe (autOn S W) ⊤ 1 := by
  refine ale_one_autOn_of_quadratic (B := D.qSub) D.elemAb.2 D.normalizes (fun g hg => hg.1) ?_
    ?_ D.relIndex_centralizer_le
  · intro g hg a ha
    rw [mem_centralizer_iff]
    intro g' hg'
    have h := hg'.2.2 _ (hg.2.1 a ha)
    calc g' * (g * a * g⁻¹ * a⁻¹) = g' * (g * a * g⁻¹ * a⁻¹) * g'⁻¹ * g' := by group
      _ = g * a * g⁻¹ * a⁻¹ * g' := by rw [h]
  · intro hle
    obtain ⟨s, hs, -, hsC⟩ := D.exists_mem_not_centralizer
    obtain ⟨x, hx, hsx⟩ := D.exists_mul_mem_qSub hs hsC
    have h := D.map_mem_of_centralizes hsx.1 fun w hw =>
      (mem_centralizer_iff.mp (hle hsx) w hw).symm
    rw [map_mul, MonoidHom.mem_ker.mp hx, mul_one] at h
    exact hsC h.2

end Setting28Sz

end Core

section Main

open scoped IsMulCommutative

theorem ALe.autOn_map {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
    {f : G →* G'} (hf : Function.Injective f) {P U : Subgroup G} [IsMulCommutative U]
    (hPU : P ≤ normalizer (U : Set G)) {P' U' : Subgroup G'} [IsMulCommutative U']
    (hP' : P.map f = P') (hU' : U.map f = U') {e : ℚ} (h : ALe (autOn P U) ⊤ e) :
    ALe (autOn P' U') ⊤ e := by
  subst hP' hU'
  have hiff := agt_autOn_map_iff hf hPU le_rfl
    ((Subgroup.map_mono hPU).trans (Subgroup.le_normalizer_map f)) (e := e)
  rw [Subgroup.subgroupOf_self] at hiff
  by_contra hne
  rw [not_ale_iff] at hne
  exact not_ale_iff.mpr (hiff.mp hne) h


theorem ale_one_autOn_of_isNatSzExt_of_isPGroup {H : Type u} [Group H] [Finite H]
    {S W : Subgroup H} [IsMulCommutative W] (hS : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index)
    (hWel : IsElemAbelian 2 W) (hWS : W ≤ S)
    (hWN : normalizer (S : Set H) ≤ normalizer (W : Set H))
    (hC : centralizer (oTwo H : Set H) ≤ oTwo H) (hWO : ¬ W ≤ oTwo H) {n : ℕ} (hn : 1 ≤ n)
    (hnat : IsNatSzExt H n) : ALe (autOn S W) ⊤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ, hψ, hψk, V, _, π, ρ, hπ, hπk, hπρ, k, θ, hθ⟩ := hnat
  set ι : ψ.ker →* oTwo H := Subgroup.inclusion hψk.le with hιdef
  set c : ψ.ker →* Multiplicative (Fin k → Fin 4 → F n) :=
    θ.toMonoidHom.comp (π.comp ι) with hcdef
  have hι : Function.Surjective ι := fun x => ⟨⟨x, hψk.ge x.2⟩, rfl⟩
  have hc : Function.Surjective c := θ.surjective.comp (hπ.comp hι)
  have hcK : ∀ x : ψ.ker, c x = 1 → ∀ h : H, h * x = x * h := by
    intro x hx h
    have h1 : π (ι x) = 1 := θ.injective (by rw [map_one]; exact hx)
    have h2 := hπk h1
    rw [Subgroup.mem_subgroupOf] at h2
    exact Subgroup.mem_center_iff.mp h2 h
  have hcc : ∀ (h : H) (x y : ψ.ker), (y : H) = h * x * h⁻¹ → ∀ j,
      Multiplicative.toAdd (c y) j = SzNatural.act n (ψ h) (Multiplicative.toAdd (c x) j) := by
    intro h x y hxy j
    have h1 := hπρ h (ι x) (ι y) hxy
    show Multiplicative.toAdd (θ (π (ι y))) j = _
    rw [← h1, hθ]
    rfl
  have hXS : ψ.ker ≤ S := by
    rw [hψk]
    have := (oTwo_isPGroup H).le_sylow_of_normal (hS.toSylow hSi)
    simpa using this
  have hSψ : IsPGroup 2 (S.map ψ) := hS.map ψ
  have hSψi : ¬ 2 ∣ (S.map ψ).index := fun h => hSi (h.trans (Subgroup.index_map_dvd S hψ))
  set P : Sylow 2 (Sz n) := hSψ.toSylow hSψi with hPdef
  have hPS : S.map ψ = P := (IsPGroup.toSylow_coe hSψ hSψi).symm
  obtain ⟨e⟩ := CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup n
  obtain ⟨hPc, hZc, hsq, -⟩ :=
    CFSG.RankThree.S4Free.Suzuki.card_sylow_and_center hn (SzNatural.card_F n) e P
  have hq := Setting28Sz.two_le_q (n := n)
  have hfwd : ∀ g : H, ψ g ∈ normalizer ((P : Subgroup (Sz n)) : Set (Sz n)) →
      ∀ x ∈ S, g * x * g⁻¹ ∈ S := by
    intro g hg x hx
    have h1 : ψ (g * x * g⁻¹) ∈ (P : Subgroup (Sz n)) := by
      rw [map_mul, map_mul, map_inv]
      refine (mem_normalizer_iff.mp hg _).mp ?_
      rw [← hPS]
      exact ⟨x, hx, rfl⟩
    rw [← hPS] at h1
    obtain ⟨s, hs, hsx⟩ := h1
    have hk : s⁻¹ * (g * x * g⁻¹) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hsx, inv_mul_cancel]
    have := S.mul_mem hs (hXS hk)
    rwa [mul_inv_cancel_left] at this
  have hWψ :
      W.map ψ = (P : Subgroup (Sz n)) ⊓ centralizer ((P : Subgroup (Sz n)) : Set (Sz n)) := by
    have hWP : W.map ψ ≤ (P : Subgroup (Sz n)) := by
      rw [← hPS]
      exact Subgroup.map_mono hWS
    have hWNP : normalizer ((P : Subgroup (Sz n)) : Set (Sz n)) ≤
        normalizer ((W.map ψ : Subgroup (Sz n)) : Set (Sz n)) := by
      intro g hg
      obtain ⟨g, rfl⟩ := hψ g
      have hgS : g ∈ normalizer (S : Set H) := by
        rw [mem_normalizer_iff]
        intro x
        refine ⟨hfwd g hg x, fun hx => ?_⟩
        have hg' : ψ g⁻¹ ∈ normalizer ((P : Subgroup (Sz n)) : Set (Sz n)) := by
          rw [map_inv]
          exact Subgroup.inv_mem _ hg
        have := hfwd g⁻¹ hg' _ hx
        rwa [inv_inv, show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this
      exact Subgroup.le_normalizer_map ψ ⟨g, hWN hgS, rfl⟩
    rcases CFSG.RankThree.S4Free.Suzuki.eq_bot_or_eq_center_or_eq_sylow hn (SzNatural.card_F n) e P
      hWP hWNP with h | h | h
    · exfalso
      apply hWO
      rw [← hψk, ← Subgroup.map_eq_bot_iff]
      exact h
    · exact h
    · exfalso
      have hle : (P : Subgroup (Sz n)) ≤ centralizer ((P : Subgroup (Sz n)) : Set (Sz n)) := by
        rw [← h]
        rintro _ ⟨w, hw, rfl⟩
        rw [mem_centralizer_iff]
        rintro _ ⟨w', hw', rfl⟩
        rw [← map_mul, ← map_mul]
        exact congrArg ψ (congrArg Subtype.val
          (hWel.1.is_comm.comm (⟨w', hw'⟩ : W) ⟨w, hw⟩))
      rw [inf_eq_left.mpr hle, hPc] at hZc
      nlinarith
  have hk : 1 ≤ k := by
    by_contra hk0
    have hk0 : k = 0 := by omega
    subst hk0
    apply hWO
    refine (le_top : W ≤ ⊤).trans fun h _ => hC ?_
    rw [mem_centralizer_iff]
    intro x hx
    rw [← hψk] at hx
    exact (hcK ⟨x, hx⟩ (Subsingleton.elim _ _) h).symm
  have D : Setting28Sz ψ c S W P :=
    { one_le_n := hn
      one_le_k := hk
      surj := hc
      central := hcK
      conj := hcc
      map_S := hPS
      ker_le := hXS
      elemAb := hWel
      le := hWS
      map_W := hWψ
      normalizes := (Subgroup.le_normalizer).trans hWN
      card_P := hPc
      card_Z := hZc
      sq_mem := hsq }
  exact D.ale_one

theorem ale_one_autOn_of_isNatSzExt {G : Type u} [Group G] [Finite G] {H S W : Subgroup G}
    [IsMulCommutative W] (hSH : S ≤ H) (hS : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.relIndex H)
    (hWel : IsElemAbelian 2 W) (hWS : W ≤ S)
    (hWN : H ⊓ normalizer (S : Set G) ≤ normalizer (W : Set G))
    (hC : H ⊓ centralizer ((oTwo ↥H).map H.subtype : Set G) ≤ (oTwo ↥H).map H.subtype)
    (hWO : ¬ W ≤ (oTwo ↥H).map H.subtype) {n : ℕ} (hn : 1 ≤ n) (hnat : IsNatSzExt ↥H n) :
    ALe (autOn S W) ⊤ 1 := by
  have hWH : W ≤ H := hWS.trans hSH
  set S' := S.subgroupOf H with hS'
  set W' := W.subgroupOf H with hW'
  haveI : IsMulCommutative W' := ⟨⟨fun a b => by
    have h := congrArg (fun t : W => (t : G))
      (hWel.1.is_comm.comm (⟨(a : H), a.2⟩ : W) ⟨(b : H), b.2⟩)
    exact Subtype.ext (Subtype.ext h)⟩⟩
  have hWel' : IsElemAbelian 2 W' :=
    ⟨inferInstance, fun x hx => Subtype.ext (by simpa using hWel.2 _ hx)⟩
  have hWS' : W' ≤ S' := fun x hx => hWS hx
  have hWN' : normalizer (S' : Set H) ≤ normalizer (W' : Set H) := by
    intro h hh
    have hhS : (h : G) ∈ H ⊓ normalizer (S : Set G) := by
      refine ⟨h.2, mem_normalizer_iff.mpr fun g => ?_⟩
      by_cases hg : g ∈ H
      · exact (mem_normalizer_iff.mp hh ⟨g, hg⟩)
      · have h1 : g ∉ S := fun h' => hg (hSH h')
        have h2 : (h : G) * g * (h : G)⁻¹ ∉ S := fun h' => hg (by
          have := H.mul_mem (H.mul_mem (H.inv_mem h.2) (hSH h')) h.2
          rwa [show (h : G)⁻¹ * ((h : G) * g * (h : G)⁻¹) * h = g by group] at this)
        exact iff_of_false h1 h2
    have hhW := hWN hhS
    exact mem_normalizer_iff.mpr fun x => mem_normalizer_iff.mp hhW x
  have hC' : centralizer (oTwo ↥H : Set ↥H) ≤ oTwo ↥H := by
    intro h hh
    have hhC : (h : G) ∈ H ⊓ centralizer ((oTwo ↥H).map H.subtype : Set G) := by
      refine ⟨h.2, mem_centralizer_iff.mpr ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact congrArg Subtype.val (mem_centralizer_iff.mp hh x hx)
    obtain ⟨x, hx, hxh⟩ := hC hhC
    rwa [show x = h from Subtype.ext hxh] at hx
  have hWO' : ¬ W' ≤ oTwo ↥H := fun hle => hWO fun g hg => ⟨⟨g, hWH hg⟩, hle hg, rfl⟩
  have h := ale_one_autOn_of_isNatSzExt_of_isPGroup (S := S') (W := W')
    (hS.comap_of_injective H.subtype H.subtype_injective) hSi hWel' hWS' hWN' hC' hWO' hn hnat
  refine ALe.autOn_map H.subtype_injective (fun x hx => hWN' (Subgroup.le_normalizer hx)) ?_ ?_ h
  · rw [hS', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSH]
  · rw [hW', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hWH]

end Main

end CFSG.RankThree.S4Free.Stell
