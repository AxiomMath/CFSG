module

public import CFSG.RankThree.S4Free.StellmacherOffender
public import CFSG.RankThree.S4Free.StellmacherL24

public section

namespace CFSG.RankThree.S4Free.Stell

open CFSG.Quasithin

variable {V : Type*} [CommGroup V]

@[expose] def commMulHom (g : MulAut V) : V →* V where
  toFun v := g v * v⁻¹
  map_one' := by simp
  map_mul' u v := by
    simp only [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

theorem commMulHom_apply (g : MulAut V) (v : V) : commMulHom g v = g v * v⁻¹ := rfl

theorem mem_fixV_zpowers_iff_apply {g : MulAut V} {v : V} :
    v ∈ fixV (Subgroup.zpowers g) ↔ g v = v := by
  refine ⟨fun h => h g (Subgroup.mem_zpowers g), fun h x hx => ?_⟩
  have hg : g ∈ MulAction.stabilizer (MulAut V) v := MulAction.mem_stabilizer_iff.mpr h
  exact MulAction.mem_stabilizer_iff.mp ((Subgroup.zpowers_le.mpr hg) hx)

theorem ker_commMulHom (g : MulAut V) : (commMulHom g).ker = fixV (Subgroup.zpowers g) := by
  ext v
  rw [MonoidHom.mem_ker, commMulHom_apply, mul_inv_eq_one, mem_fixV_zpowers_iff_apply]

theorem fixV_sup_eq_inf (X Y : Subgroup (MulAut V)) : fixV (X ⊔ Y) = fixV X ⊓ fixV Y := by
  ext v
  constructor
  · intro h
    exact ⟨fun x hx => h x (Subgroup.mem_sup_left hx), fun y hy => h y (Subgroup.mem_sup_right hy)⟩
  · rintro ⟨hX, hY⟩ z hz
    have hle : X ⊔ Y ≤ MulAction.stabilizer (MulAut V) v :=
      sup_le (fun x hx => MulAction.mem_stabilizer_iff.mpr (hX x hx))
        (fun y hy => MulAction.mem_stabilizer_iff.mpr (hY y hy))
    exact MulAction.mem_stabilizer_iff.mp (hle hz)

theorem fixV_le_fixV_of_le {X Y : Subgroup (MulAut V)} (h : X ≤ Y) : fixV Y ≤ fixV X :=
  fun _ hv x hx => hv x (h hx)

theorem le_stabSub_of_forall_apply_mem {X : Subgroup (MulAut V)} {U : Subgroup V}
    (h : ∀ x ∈ X, ∀ u ∈ U, x u ∈ U) : X ≤ stabSub U := by
  intro x hx u
  refine ⟨fun hu => ?_, h x hx u⟩
  have := h x⁻¹ (X.inv_mem hx) (x u) hu
  rwa [MulAut.inv_apply_self] at this

theorem map_eq_self_of_mem_stabSub {g : MulAut V} {U : Subgroup V} (hg : g ∈ stabSub U) :
    U.map g.toMonoidHom = U := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (hg u).mpr hu
  · intro hv
    refine ⟨g⁻¹ v, (hg (g⁻¹ v)).mp (by rw [MulAut.apply_inv_self]; exact hv), ?_⟩
    simp [MulAut.apply_inv_self]

theorem map_eq_self_of_le_fixV {X : Subgroup (MulAut V)} {C : Subgroup V} (hC : C ≤ fixV X)
    {g : MulAut V} (hg : g ∈ X) : C.map g.toMonoidHom = C := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    change g u ∈ C
    rw [hC hu g hg]
    exact hu
  · intro hv
    exact ⟨v, hv, hC hv g hg⟩

theorem rk_map_mulAut [Finite V] (g : MulAut V) (U : Subgroup V) :
    rk ↥(U.map g.toMonoidHom) = rk U := by
  unfold rk
  rw [Subgroup.card_map_of_injective (f := g.toMonoidHom) g.injective]

theorem map_commSub (g : MulAut V) (W : Subgroup V) (X : Subgroup (MulAut V)) :
    (commSub W X).map g.toMonoidHom =
      commSub (W.map g.toMonoidHom) (X.map (MulAut.conj g).toMonoidHom) := by
  rw [commSub, commSub, MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨_, ⟨x, hx, w, hw, rfl⟩, rfl⟩
    refine ⟨g * x * g⁻¹, ⟨x, hx, rfl⟩, g w, ⟨w, hw, rfl⟩, ?_⟩
    simp [MulAut.mul_apply, map_mul, map_inv]
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨x w * w⁻¹, ⟨x, hx, w, hw, rfl⟩, by simp [MulAut.mul_apply, map_mul, map_inv]⟩

theorem commSub_zpowers_eq_map_commMulHom {g : MulAut V} {W : Subgroup V}
    (hg : g ∈ stabSub W) : commSub W (Subgroup.zpowers g) = W.map (commMulHom g) := by
  apply le_antisymm
  · let T : Subgroup (MulAut V) :=
      { carrier := {x | x ∈ stabSub W ∧ ∀ w ∈ W, x w * w⁻¹ ∈ W.map (commMulHom g)}
        one_mem' := ⟨Subgroup.one_mem _, fun w _ => by simp⟩
        mul_mem' := by
          rintro x y ⟨hxS, hx⟩ ⟨hyS, hy⟩
          refine ⟨Subgroup.mul_mem _ hxS hyS, fun w hw => ?_⟩
          have hyw : y w ∈ W := (hyS w).mpr hw
          have := Subgroup.mul_mem _ (hx (y w) hyw) (hy w hw)
          rwa [show x (y w) * (y w)⁻¹ * (y w * w⁻¹) = (x * y) w * w⁻¹ by
            rw [MulAut.mul_apply]; group] at this
        inv_mem' := by
          rintro x ⟨hxS, hx⟩
          refine ⟨Subgroup.inv_mem _ hxS, fun w hw => ?_⟩
          have hw' : x⁻¹ w ∈ W := ((Subgroup.inv_mem _ hxS) w).mpr hw
          have := Subgroup.inv_mem _ (hx (x⁻¹ w) hw')
          rwa [MulAut.apply_inv_self, show (w * (x⁻¹ w)⁻¹)⁻¹ = x⁻¹ w * w⁻¹ by group] at this }
    have hgT : g ∈ T := ⟨hg, fun w hw => ⟨w, hw, rfl⟩⟩
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    exact ((Subgroup.zpowers_le.mpr hgT) hx).2 w hw
  · rintro _ ⟨w, hw, rfl⟩
    exact Subgroup.subset_closure ⟨g, Subgroup.mem_zpowers g, w, hw, rfl⟩

theorem card_map_commMulHom_mul (g : MulAut V) (W : Subgroup V) :
    Nat.card ↥(W.map (commMulHom g)) * Nat.card ↥(W ⊓ fixV (Subgroup.zpowers g)) =
      Nat.card W := by
  rw [← Subgroup.relIndex_ker, ker_commMulHom, inf_comm, Subgroup.relIndex_mul_card]

theorem rk_commSub_add_rk_inf_fixV [Finite V] {g : MulAut V} {W : Subgroup V}
    (hg : g ∈ stabSub W) :
    rk ↥(commSub W (Subgroup.zpowers g)) + rk ↥(W ⊓ fixV (Subgroup.zpowers g)) = rk W := by
  rw [commSub_zpowers_eq_map_commMulHom hg]
  unfold rk
  rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', card_map_commMulHom_mul]

theorem mRel_add_rk_of_le [Finite V] {C W : Subgroup V} (h : C ≤ W) :
    mRel C W + rk C = rk W := by
  unfold mRel rk
  have h1 := Subgroup.relIndex_mul_card C W
  rw [inf_eq_left.mpr h] at h1
  rw [← padicValNat.mul (relIndex_ne_zero_of_finite C W) Nat.card_pos.ne', h1]

structure Setting25 (A L : Subgroup (MulAut V)) (Z₀ W : Subgroup V) : Prop where
  le_L : A ≤ L
  quad : commSub W A ≤ fixV A
  le_fixV : Z₀ ≤ fixV A
  le_W : Z₀ ≤ W
  le_stabSub : L ≤ stabSub W
  gen : ∀ U : Subgroup V, (∀ l ∈ L, Z₀.map l.toMonoidHom ≤ U) → W ≤ U

namespace Setting25

variable {A L : Subgroup (MulAut V)} {Z₀ W : Subgroup V}

theorem mem_stabSub (h : Setting25 A L Z₀ W) {l : MulAut V} (hl : l ∈ L) : l ∈ stabSub W :=
  h.le_stabSub hl

theorem map_W (h : Setting25 A L Z₀ W) {l : MulAut V} (hl : l ∈ L) : W.map l.toMonoidHom = W :=
  map_eq_self_of_mem_stabSub (h.mem_stabSub hl)

theorem commSub_le (h : Setting25 A L Z₀ W) {X : Subgroup (MulAut V)} (hX : X ≤ L) :
    commSub W X ≤ W :=
  commSub_le_of_invariant fun x hx w hw => ((h.mem_stabSub (hX hx)) w).mpr hw

theorem map_conj_le (h : Setting25 A L Z₀ W) {y : MulAut V} (hy : y ∈ L) :
    A.map (MulAut.conj y).toMonoidHom ≤ L := by
  rintro _ ⟨b, hb, rfl⟩
  exact L.mul_mem (L.mul_mem hy (h.le_L hb)) (L.inv_mem hy)

theorem quad_conj [Finite V] (h : Setting25 A L Z₀ W) {y : MulAut V} (hy : y ∈ L) :
    commSub W (A.map (MulAut.conj y).toMonoidHom) ≤ fixV (A.map (MulAut.conj y).toMonoidHom) := by
  rw [fixV_map_conj, ← h.map_W hy, ← map_commSub]
  exact Subgroup.map_mono h.quad

theorem map_fix (h : Setting25 A L Z₀ W) {y : MulAut V} (hy : y ∈ L) :
    (W ⊓ fixV L).map y.toMonoidHom = W ⊓ fixV L :=
  map_eq_self_of_le_fixV inf_le_right hy

theorem map_inf_fixV [Finite V] (h : Setting25 A L Z₀ W) {y : MulAut V} (hy : y ∈ L)
    (X : Subgroup (MulAut V)) :
    (W ⊓ fixV X).map y.toMonoidHom = W ⊓ fixV (X.map (MulAut.conj y).toMonoidHom) := by
  rw [Subgroup.map_inf_eq W (fixV X) y.toMonoidHom y.injective, h.map_W hy, fixV_map_conj]

theorem eq_sup (h : Setting25 A L Z₀ W) {a' : MulAut V}
    (hL : A ⊔ Subgroup.zpowers a' = L) :
    Z₀ ⊔ commSub W A ⊔ commSub W (Subgroup.zpowers a') = W := by
  have ha' : Subgroup.zpowers a' ≤ L := le_sup_right.trans hL.le
  set U := Z₀ ⊔ commSub W A ⊔ commSub W (Subgroup.zpowers a') with hU
  have hUW : U ≤ W := sup_le (sup_le h.le_W (h.commSub_le h.le_L)) (h.commSub_le ha')
  have hinv : ∀ X : Subgroup (MulAut V), commSub W X ≤ U → ∀ x ∈ X, ∀ u ∈ U, x u ∈ U := by
    intro X hX x hx u hu
    have h1 : x u * u⁻¹ ∈ U := hX (Subgroup.subset_closure ⟨x, hx, u, hUW hu, rfl⟩)
    have h2 := U.mul_mem h1 hu
    rwa [inv_mul_cancel_right] at h2
  have hA : A ≤ stabSub U :=
    le_stabSub_of_forall_apply_mem (hinv A (le_sup_right.trans le_sup_left))
  have hZ : Subgroup.zpowers a' ≤ stabSub U :=
    le_stabSub_of_forall_apply_mem (hinv _ le_sup_right)
  have hLU : L ≤ stabSub U := hL.ge.trans (sup_le hA hZ)
  refine le_antisymm hUW (h.gen U fun l hl => ?_)
  rintro _ ⟨z, hz, rfl⟩
  exact ((hLU hl) z).mpr ((le_sup_left.trans le_sup_left : Z₀ ≤ U) hz)

theorem key [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (h : Setting25 A L Z₀ W) {a y : MulAut V}
    (haA : a ∈ A) (hyL : y ∈ L) (hL : A ⊔ Subgroup.zpowers (y * a * y⁻¹) = L) :
    W ⊓ fixV A = commSub W A ⊔ (W ⊓ fixV L) ∧
      commSub W A ⊔ (W ⊓ fixV L) = commSub W (Subgroup.zpowers a) ⊔ (W ⊓ fixV L) ∧
      commSub W (Subgroup.zpowers a) ⊔ (W ⊓ fixV L) = W ⊓ fixV (Subgroup.zpowers a) ∧
      commSub W (Subgroup.zpowers a) ⊓ (W ⊓ fixV L) = ⊥ ∧
      2 * rk ↥(W ⊓ fixV A) = rk W + rk ↥(W ⊓ fixV L) := by
  set C := W ⊓ fixV L with hCdef
  set a' := y * a * y⁻¹ with ha'def
  set D := Z₀ ⊔ commSub W A ⊔ C with hDdef
  have haL : a ∈ L := h.le_L haA
  have hza : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.mpr haA
  have hconj : a' ∈ A.map (MulAut.conj y).toMonoidHom := ⟨a, haA, rfl⟩
  have hza' : Subgroup.zpowers a' ≤ A.map (MulAut.conj y).toMonoidHom :=
    Subgroup.zpowers_le.mpr hconj
  have hLsup : A ⊔ A.map (MulAut.conj y).toMonoidHom = L :=
    le_antisymm (sup_le h.le_L (h.map_conj_le hyL)) (hL.ge.trans (sup_le_sup_left hza' A))
  have hfixL : fixV L = fixV A ⊓ fixV (A.map (MulAut.conj y).toMonoidHom) := by
    rw [← hLsup, fixV_sup_eq_inf]
  have hfixL' : fixV L = fixV A ⊓ fixV (Subgroup.zpowers a') := by
    rw [← hL, fixV_sup_eq_inf]
  have hCW : C ≤ W := inf_le_left
  have hCA : C ≤ fixV A := inf_le_right.trans (fixV_le_fixV_of_le h.le_L)
  have hDA : D ≤ W ⊓ fixV A :=
    sup_le (sup_le (le_inf h.le_W h.le_fixV) (le_inf (h.commSub_le h.le_L) h.quad))
      (le_inf hCW hCA)
  set X := commSub W (Subgroup.zpowers a') with hXdef
  have hXfix : X ≤ fixV (Subgroup.zpowers a') :=
    (commSub_mono le_rfl hza').trans ((h.quad_conj hyL).trans (fixV_le_fixV_of_le hza'))
  have hXC : X ⊔ C ≤ W ⊓ fixV (Subgroup.zpowers a') :=
    sup_le (le_inf (h.commSub_le (le_sup_right.trans hL.le)) hXfix)
      (le_inf hCW (inf_le_right.trans (fixV_le_fixV_of_le (le_sup_right.trans hL.le))))
  have hsup1 : D ⊔ (X ⊔ C) = W := by
    refine le_antisymm (sup_le (hDA.trans inf_le_left) (hXC.trans inf_le_left)) ?_
    exact (h.eq_sup hL).ge.trans
      (sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right))
  have hinf1 : D ⊓ (X ⊔ C) ≤ C := by
    refine (inf_le_inf hDA hXC).trans ?_
    rw [hCdef, hfixL']
    exact le_inf (inf_le_left.trans inf_le_left) (le_inf (inf_le_left.trans inf_le_right)
      (inf_le_right.trans inf_le_right))
  have hC1 : C ≤ D ⊓ (X ⊔ C) := le_inf le_sup_right le_sup_right
  have hr1 : rk W + rk C = rk D + rk ↥(X ⊔ C) := by
    have := rk_sup_add_rk_inf D (X ⊔ C)
    rwa [hsup1, le_antisymm hinf1 hC1] at this
  have hDy : D.map y.toMonoidHom ≤ W ⊓ fixV (A.map (MulAut.conj y).toMonoidHom) := by
    rw [← h.map_inf_fixV hyL A]
    exact Subgroup.map_mono hDA
  have hinf2 : D ⊓ D.map y.toMonoidHom ≤ C := by
    refine (inf_le_inf hDA hDy).trans ?_
    rw [hCdef, hfixL]
    exact le_inf (inf_le_left.trans inf_le_left) (le_inf (inf_le_left.trans inf_le_right)
      (inf_le_right.trans inf_le_right))
  have hr2 : 2 * rk D ≤ rk W + rk C := by
    have h1 := rk_sup_add_rk_inf D (D.map y.toMonoidHom)
    have h2 : rk ↥(D ⊔ D.map y.toMonoidHom) ≤ rk W :=
      rk_mono (sup_le (hDA.trans inf_le_left) (hDy.trans inf_le_left))
    have h3 : rk ↥(D ⊓ D.map y.toMonoidHom) ≤ rk C := rk_mono hinf2
    rw [rk_map_mulAut] at h1
    omega
  have hCy : C.map y.toMonoidHom = C := h.map_fix hyL
  have hXmap : (commSub W (Subgroup.zpowers a) ⊔ C).map y.toMonoidHom = X ⊔ C := by
    rw [Subgroup.map_sup, map_commSub, h.map_W hyL, hCy, MonoidHom.map_zpowers]
    rfl
  have hEa : commSub W (Subgroup.zpowers a) ⊔ C ≤ commSub W A ⊔ C :=
    sup_le_sup_right (commSub_mono le_rfl hza) C
  have hEA : commSub W A ⊔ C ≤ D := sup_le_sup_right le_sup_right C
  have hr3 : rk ↥(X ⊔ C) ≤ rk D := by
    rw [← hXmap, rk_map_mulAut]
    exact rk_mono (hEa.trans hEA)
  have hrD : 2 * rk D = rk W + rk C := by omega
  have hrX : rk ↥(X ⊔ C) = rk D := by omega
  have hEa_eq : commSub W (Subgroup.zpowers a) ⊔ C = D := by
    refine eq_of_le_of_rk_le hV (hEa.trans hEA) ?_
    have := rk_map_mulAut y (commSub W (Subgroup.zpowers a) ⊔ C)
    rw [hXmap] at this
    omega
  have hEA_eq : commSub W A ⊔ C = D :=
    le_antisymm hEA (hEa_eq.symm.le.trans hEa)
  have hfa : D ≤ W ⊓ fixV (Subgroup.zpowers a) :=
    hDA.trans (inf_le_inf_left W (fixV_le_fixV_of_le hza))
  have hsa := rk_commSub_add_rk_inf_fixV (h.mem_stabSub haL)
  have hsupa := rk_sup_add_rk_inf (commSub W (Subgroup.zpowers a)) C
  rw [hEa_eq] at hsupa
  have hfa_eq : D = W ⊓ fixV (Subgroup.zpowers a) := by
    refine eq_of_le_of_rk_le hV hfa ?_
    omega
  have hrF : rk ↥(W ⊓ fixV (Subgroup.zpowers a)) = rk D := by rw [← hfa_eq]
  have hDfixA : W ⊓ fixV A = D :=
    le_antisymm ((inf_le_inf_left W (fixV_le_fixV_of_le hza)).trans hfa_eq.symm.le) hDA
  have hbot : commSub W (Subgroup.zpowers a) ⊓ C = ⊥ := by
    rw [← rk_eq_zero_iff hV]
    omega
  refine ⟨hDfixA.trans hEA_eq.symm, hEA_eq.trans hEa_eq.symm, hEa_eq.trans hfa_eq, hbot, ?_⟩
  rw [hDfixA]
  exact hrD

theorem inf_fixV_conj_eq [Finite V] (h : Setting25 A L Z₀ W) {a x : MulAut V} (hxL : x ∈ L)
    (hfix : W ⊓ fixV (Subgroup.zpowers a) = W ⊓ fixV A) :
    W ⊓ fixV (Subgroup.zpowers (x * a * x⁻¹)) = W ⊓ fixV (A.map (MulAut.conj x).toMonoidHom) := by
  have hza : (Subgroup.zpowers a).map (MulAut.conj x).toMonoidHom =
      Subgroup.zpowers (x * a * x⁻¹) := MonoidHom.map_zpowers _ _
  rw [← hza, ← h.map_inf_fixV hxL, hfix, h.map_inf_fixV hxL]

theorem commSub_conj_eq (h : Setting25 A L Z₀ W) {a x : MulAut V} (hxL : x ∈ L) :
    commSub W (Subgroup.zpowers (x * a * x⁻¹)) =
      (commSub W (Subgroup.zpowers a)).map x.toMonoidHom := by
  have hza : (Subgroup.zpowers a).map (MulAut.conj x).toMonoidHom =
      Subgroup.zpowers (x * a * x⁻¹) := MonoidHom.map_zpowers _ _
  rw [map_commSub, h.map_W hxL, hza]

theorem sup_fixV_conj [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (h : Setting25 A L Z₀ W)
    (h2 : 2 * rk ↥(W ⊓ fixV A) = rk W + rk ↥(W ⊓ fixV L)) {x : MulAut V} (hxL : x ∈ L)
    (hx : A ⊔ A.map (MulAut.conj x).toMonoidHom = L) :
    (W ⊓ fixV A) ⊔ (W ⊓ fixV (A.map (MulAut.conj x).toMonoidHom)) = W := by
  have hfixL : fixV L = fixV A ⊓ fixV (A.map (MulAut.conj x).toMonoidHom) := by
    rw [← hx, fixV_sup_eq_inf]
  have hinf : (W ⊓ fixV A) ⊓ (W ⊓ fixV (A.map (MulAut.conj x).toMonoidHom)) ≤ W ⊓ fixV L := by
    rw [hfixL]
    exact le_inf (inf_le_left.trans inf_le_left)
      (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))
  have hr := rk_sup_add_rk_inf (W ⊓ fixV A) (W ⊓ fixV (A.map (MulAut.conj x).toMonoidHom))
  have hr' : rk ↥(W ⊓ fixV (A.map (MulAut.conj x).toMonoidHom)) = rk ↥(W ⊓ fixV A) := by
    rw [← h.map_inf_fixV hxL, rk_map_mulAut]
  have hri := rk_mono hinf
  refine (eq_of_le_of_rk_le hV (sup_le inf_le_left inf_le_left) ?_)
  omega

theorem mem_of_comm_mem [Finite V] (h : Setting25 A L Z₀ W) {a x : MulAut V} (haA : a ∈ A)
    (hxL : x ∈ L) (hx : A ⊔ A.map (MulAut.conj x).toMonoidHom = L)
    (hfix : W ⊓ fixV (Subgroup.zpowers a) = W ⊓ fixV A)
    (hbot : commSub W (Subgroup.zpowers a) ⊓ (W ⊓ fixV L) = ⊥) {w : V} (hw : w ∈ W)
    (hc : (a * (x * a * x⁻¹)) w * w⁻¹ ∈ W ⊓ fixV L) : w ∈ W ⊓ fixV L := by
  have haL : a ∈ L := h.le_L haA
  have hfixL : fixV L = fixV A ⊓ fixV (A.map (MulAut.conj x).toMonoidHom) := by
    rw [← hx, fixV_sup_eq_inf]
  have hCA : W ⊓ fixV L ≤ W ⊓ fixV A := inf_le_inf_left W (fixV_le_fixV_of_le h.le_L)
  have hcA : commSub W (Subgroup.zpowers a) ≤ W ⊓ fixV A :=
    le_inf (h.commSub_le (Subgroup.zpowers_le.mpr haL))
      ((commSub_mono le_rfl (Subgroup.zpowers_le.mpr haA)).trans h.quad)
  have hc2 := h.commSub_conj_eq (a := a) hxL
  have hfix2 := h.inf_fixV_conj_eq hxL hfix
  have hc2A : commSub W (Subgroup.zpowers (x * a * x⁻¹)) ≤
      W ⊓ fixV (A.map (MulAut.conj x).toMonoidHom) := by
    rw [hc2, ← h.map_inf_fixV hxL A]
    exact Subgroup.map_mono hcA
  have hbot2 : commSub W (Subgroup.zpowers (x * a * x⁻¹)) ⊓ (W ⊓ fixV L) = ⊥ := by
    rw [hc2, ← h.map_fix hxL, ← Subgroup.map_inf_eq _ _ x.toMonoidHom x.injective, hbot,
      Subgroup.map_bot]
  set a2 := x * a * x⁻¹ with ha2
  set c₀ := (a * a2) w * w⁻¹ with hc₀
  have hc₀L : ∀ l ∈ L, l c₀ = c₀ := fun l hl => (Subgroup.mem_inf.mp hc).2 l hl
  have h1 : a (a2 w) = c₀ * w := by
    rw [hc₀, MulAut.mul_apply (e₁ := a) (e₂ := a2) (m := w)]
    exact (inv_mul_cancel_right _ _).symm
  have h2 : a2 w = c₀ * a⁻¹ w := by
    have := congrArg (fun v => a⁻¹ v) h1
    simp only [MulAut.inv_apply_self, map_mul] at this
    rw [this, hc₀L a⁻¹ (L.inv_mem haL)]
  have ht : a2 w * w⁻¹ ∈ commSub W (Subgroup.zpowers a2) :=
    Subgroup.subset_closure ⟨a2, Subgroup.mem_zpowers _, w, hw, rfl⟩
  have hu : a⁻¹ w * w⁻¹ ∈ commSub W (Subgroup.zpowers a) :=
    Subgroup.subset_closure ⟨a⁻¹, Subgroup.inv_mem _ (Subgroup.mem_zpowers a), w, hw, rfl⟩
  have htA : a2 w * w⁻¹ ∈ W ⊓ fixV A := by
    rw [h2, mul_assoc]
    exact Subgroup.mul_mem _ (hCA hc) (hcA hu)
  have htC : a2 w * w⁻¹ ∈ W ⊓ fixV L := by
    rw [hfixL]
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp htA).1, Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_inf.mp htA).2, (Subgroup.mem_inf.mp (hc2A ht)).2⟩⟩
  have ht1 : a2 w * w⁻¹ = 1 := by
    have : a2 w * w⁻¹ ∈ commSub W (Subgroup.zpowers a2) ⊓ (W ⊓ fixV L) :=
      Subgroup.mem_inf.mpr ⟨ht, htC⟩
    rwa [hbot2, Subgroup.mem_bot] at this
  have hw2 : a2 w = w := mul_inv_eq_one.mp ht1
  have hc₀a : c₀ = a w * w⁻¹ := by rw [hc₀, MulAut.mul_apply (e₁ := a) (e₂ := a2) (m := w), hw2]
  have hwa : a w * w⁻¹ ∈ commSub W (Subgroup.zpowers a) :=
    Subgroup.subset_closure ⟨a, Subgroup.mem_zpowers a, w, hw, rfl⟩
  have ha1 : a w * w⁻¹ = 1 := by
    have : a w * w⁻¹ ∈ commSub W (Subgroup.zpowers a) ⊓ (W ⊓ fixV L) :=
      Subgroup.mem_inf.mpr ⟨hwa, hc₀a ▸ hc⟩
    rwa [hbot, Subgroup.mem_bot] at this
  have hw1 : w ∈ W ⊓ fixV A :=
    hfix.le (Subgroup.mem_inf.mpr ⟨hw, mem_fixV_zpowers_iff_apply.mpr (mul_inv_eq_one.mp ha1)⟩)
  have hw2' : w ∈ W ⊓ fixV (A.map (MulAut.conj x).toMonoidHom) :=
    hfix2.le (Subgroup.mem_inf.mpr ⟨hw, mem_fixV_zpowers_iff_apply.mpr hw2⟩)
  rw [hfixL]
  exact Subgroup.mem_inf.mpr ⟨hw, Subgroup.mem_inf.mpr
    ⟨(Subgroup.mem_inf.mp hw1).2, (Subgroup.mem_inf.mp hw2').2⟩⟩

theorem two_mul_rk_inf_fixV [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (h : Setting25 A L Z₀ W)
    {a x : MulAut V} (haA : a ∈ A) (hxL : x ∈ L) (hx : A ⊔ A.map (MulAut.conj x).toMonoidHom = L)
    (hfix : W ⊓ fixV (Subgroup.zpowers a) = W ⊓ fixV A)
    (hbot : commSub W (Subgroup.zpowers a) ⊓ (W ⊓ fixV L) = ⊥) {U : Subgroup V}
    (hCU : W ⊓ fixV L ≤ U) (hUW : U ≤ W) (hUL : L ≤ stabSub U) :
    2 * rk ↥(U ⊓ fixV (Subgroup.zpowers a)) = rk U + rk ↥(W ⊓ fixV L) := by
  have haL : a ∈ L := h.le_L haA
  have hfixL : fixV L = fixV A ⊓ fixV (A.map (MulAut.conj x).toMonoidHom) := by
    rw [← hx, fixV_sup_eq_inf]
  have hfix2 := h.inf_fixV_conj_eq hxL hfix
  have hza : (Subgroup.zpowers a).map (MulAut.conj x).toMonoidHom =
      Subgroup.zpowers (x * a * x⁻¹) := MonoidHom.map_zpowers _ _
  have hEx : (U ⊓ fixV (Subgroup.zpowers a)).map x.toMonoidHom =
      U ⊓ fixV (Subgroup.zpowers (x * a * x⁻¹)) := by
    rw [Subgroup.map_inf_eq _ _ x.toMonoidHom x.injective,
      map_eq_self_of_mem_stabSub (hUL hxL), ← fixV_map_conj, hza]
  have hE : U ⊓ fixV (Subgroup.zpowers a) ≤ W ⊓ fixV A :=
    hfix ▸ inf_le_inf_right _ hUW
  have hE2 : U ⊓ fixV (Subgroup.zpowers (x * a * x⁻¹)) ≤
      W ⊓ fixV (A.map (MulAut.conj x).toMonoidHom) :=
    hfix2 ▸ inf_le_inf_right _ hUW
  have hinf : (U ⊓ fixV (Subgroup.zpowers a)) ⊓ (U ⊓ fixV (Subgroup.zpowers (x * a * x⁻¹))) ≤
      W ⊓ fixV L := by
    refine (inf_le_inf hE hE2).trans ?_
    rw [hfixL]
    exact le_inf (inf_le_left.trans inf_le_left)
      (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))
  have hr1 := rk_sup_add_rk_inf (U ⊓ fixV (Subgroup.zpowers a))
    (U ⊓ fixV (Subgroup.zpowers (x * a * x⁻¹)))
  have hr1' : rk ↥(U ⊓ fixV (Subgroup.zpowers (x * a * x⁻¹))) =
      rk ↥(U ⊓ fixV (Subgroup.zpowers a)) := by
    rw [← hEx, rk_map_mulAut]
  have hr2 : rk ↥((U ⊓ fixV (Subgroup.zpowers a)) ⊔
      (U ⊓ fixV (Subgroup.zpowers (x * a * x⁻¹)))) ≤ rk U :=
    rk_mono (sup_le inf_le_left inf_le_left)
  have hr3 := rk_mono hinf
  have hcU : commSub U (Subgroup.zpowers a) ≤ U :=
    commSub_le_of_invariant fun g hg u hu => ((hUL (Subgroup.zpowers_le.mpr haL hg)) u).mpr hu
  have hcW : commSub U (Subgroup.zpowers a) ≤ commSub W (Subgroup.zpowers a) :=
    commSub_mono hUW le_rfl
  have hcfix : commSub W (Subgroup.zpowers a) ≤ fixV (Subgroup.zpowers a) :=
    ((commSub_mono le_rfl (Subgroup.zpowers_le.mpr haA)).trans h.quad).trans
      (fixV_le_fixV_of_le (Subgroup.zpowers_le.mpr haA))
  have hsupE : commSub U (Subgroup.zpowers a) ⊔ (W ⊓ fixV L) ≤ U ⊓ fixV (Subgroup.zpowers a) :=
    sup_le (le_inf hcU (hcW.trans hcfix))
      (le_inf hCU (inf_le_right.trans (fixV_le_fixV_of_le (Subgroup.zpowers_le.mpr haL))))
  have hbotU : commSub U (Subgroup.zpowers a) ⊓ (W ⊓ fixV L) = ⊥ :=
    le_bot_iff.mp (hbot ▸ inf_le_inf_right _ hcW)
  have hr4 := rk_sup_add_rk_inf (commSub U (Subgroup.zpowers a)) (W ⊓ fixV L)
  rw [hbotU, rk_bot] at hr4
  have hr5 := rk_mono hsupE
  have hr6 := rk_commSub_add_rk_inf_fixV (hUL haL)
  omega

theorem eq_of_commSub_le [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (h : Setting25 A L Z₀ W)
    {a x : MulAut V} (haA : a ∈ A) (hxL : x ∈ L) (hx : A ⊔ A.map (MulAut.conj x).toMonoidHom = L)
    (hfix : W ⊓ fixV (Subgroup.zpowers a) = W ⊓ fixV A)
    (hbot : commSub W (Subgroup.zpowers a) ⊓ (W ⊓ fixV L) = ⊥) {U₁ U₂ : Subgroup V}
    (hCU : W ⊓ fixV L ≤ U₂) (h21 : U₂ ≤ U₁) (h1W : U₁ ≤ W) (hU₁ : L ≤ stabSub U₁)
    (hU₂ : L ≤ stabSub U₂) (hc : commSub U₁ (Subgroup.zpowers a) ≤ U₂) : U₁ = U₂ := by
  have haL : a ∈ L := h.le_L haA
  have hE1 := h.two_mul_rk_inf_fixV hV haA hxL hx hfix hbot (hCU.trans h21) h1W hU₁
  have hE2 := h.two_mul_rk_inf_fixV hV haA hxL hx hfix hbot hCU (h21.trans h1W) hU₂
  have hcW : commSub U₁ (Subgroup.zpowers a) ≤ commSub W (Subgroup.zpowers a) :=
    commSub_mono h1W le_rfl
  have hcfix : commSub W (Subgroup.zpowers a) ≤ fixV (Subgroup.zpowers a) :=
    ((commSub_mono le_rfl (Subgroup.zpowers_le.mpr haA)).trans h.quad).trans
      (fixV_le_fixV_of_le (Subgroup.zpowers_le.mpr haA))
  have hsup : commSub U₁ (Subgroup.zpowers a) ⊔ (W ⊓ fixV L) ≤ U₂ ⊓ fixV (Subgroup.zpowers a) :=
    sup_le (le_inf hc (hcW.trans hcfix))
      (le_inf hCU (inf_le_right.trans (fixV_le_fixV_of_le (Subgroup.zpowers_le.mpr haL))))
  have hbotU : commSub U₁ (Subgroup.zpowers a) ⊓ (W ⊓ fixV L) = ⊥ :=
    le_bot_iff.mp (hbot ▸ inf_le_inf_right _ hcW)
  have hr4 := rk_sup_add_rk_inf (commSub U₁ (Subgroup.zpowers a)) (W ⊓ fixV L)
  rw [hbotU, rk_bot] at hr4
  have hr5 := rk_mono hsup
  have hr6 := rk_commSub_add_rk_inf_fixV (hU₁ haL)
  exact (eq_of_le_of_rk_le hV h21 (by omega)).symm

end Setting25

theorem dihedral_normalClosure_eq_top {n : ℕ} (hn : Odd n) {d : DihedralGroup n} (hd1 : d ≠ 1)
    (hd2 : d ^ 2 = 1) : Subgroup.normalClosure ({d} : Set (DihedralGroup n)) = ⊤ := by
  have hcop : Nat.Coprime 2 n := Nat.coprime_two_left.mpr hn
  set u : (ZMod n)ˣ := ZMod.unitOfCoprime 2 hcop with hu_def
  have hu : (u : ZMod n) = 2 := by
    rw [hu_def, ZMod.coe_unitOfCoprime]
    norm_num
  rcases d with i | i
  · exfalso
    apply hd1
    rw [DihedralGroup.r_pow, ← DihedralGroup.r_zero] at hd2
    have hi : i * 2 = 0 := by
      have := DihedralGroup.r.inj hd2
      simpa using this
    have hi0 : i = 0 := by
      calc i = i * (u : ZMod n) * ((u⁻¹ : (ZMod n)ˣ) : ZMod n) :=
            (Units.mul_inv_cancel_right i u).symm
        _ = 0 := by rw [hu, hi, zero_mul]
    rw [hi0, DihedralGroup.r_zero]
  · set N := Subgroup.normalClosure ({DihedralGroup.sr i} : Set (DihedralGroup n))
    have hsr : ∀ k : ZMod n, DihedralGroup.sr k ∈ N := by
      intro k
      set j : ZMod n := (i - k) * ((u⁻¹ : (ZMod n)ˣ) : ZMod n) with hj
      have h2j : 2 * j = i - k := by
        calc 2 * j = (u : ZMod n) * ((i - k) * ((u⁻¹ : (ZMod n)ˣ) : ZMod n)) := by rw [hu]
          _ = (i - k) * ((u : ZMod n) * ((u⁻¹ : (ZMod n)ˣ) : ZMod n)) := by ring
          _ = i - k := by rw [Units.mul_inv, mul_one]
      have hconj : DihedralGroup.r j * DihedralGroup.sr i * (DihedralGroup.r j)⁻¹ =
          DihedralGroup.sr k := by
        rw [DihedralGroup.inv_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
        congr 1
        linear_combination (-1 : ZMod n) * h2j
      rw [← hconj]
      exact (Subgroup.normalClosure_normal).conj_mem _
        (Subgroup.subset_normalClosure (Set.mem_singleton _)) _
    rw [eq_top_iff]
    rintro (k | k) -
    · have : DihedralGroup.sr (0 : ZMod n) * DihedralGroup.sr k = DihedralGroup.r k := by
        rw [DihedralGroup.sr_mul_sr, sub_zero]
      rw [← this]
      exact N.mul_mem (hsr 0) (hsr k)
    · exact hsr k

section L24

variable [Finite V] {S M A L : Subgroup (MulAut V)}

theorem IsL24.exists_mem_not_mem_oTwo (hL : IsL24 S M A L) :
    ∃ a ∈ A, a ∉ (oTwo ↥L).map L.subtype := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hxL, hxM⟩ := Set.not_subset.mp hL.not_le
  have hAO : A ≤ (oTwo ↥L).map L.subtype := fun a ha => hcon a ha
  have hAxO : A.map (MulAut.conj x).toMonoidHom ≤ (oTwo ↥L).map L.subtype := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨b', hb', rfl⟩ := hAO hb
    exact ⟨⟨x, hxL⟩ * b' * ⟨x, hxL⟩⁻¹, (inferInstance : (oTwo ↥L).Normal).conj_mem _ hb' _, rfl⟩
  have hLO : L ≤ (oTwo ↥L).map L.subtype :=
    (hL.sup_conj x hxL hxM).ge.trans (sup_le hAO hAxO)
  have htop : oTwo ↥L = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨g', hg', hgg'⟩ := hLO g.2
    rwa [show g' = g from Subtype.ext hgg'] at hg'
  obtain ⟨r, s, hr, -, -, ⟨e⟩⟩ := hL.dihedral
  have h1 : (oTwo ↥L).index = 1 := Subgroup.index_eq_one.mpr htop
  rw [Subgroup.index, Nat.card_congr e.toEquiv, DihedralGroup.nat_card] at h1
  have : 0 < r ^ s := pow_pos hr.pos s
  omega

theorem IsL24.exists_conj_not_mem (hL : IsL24 S M A L) (hS : IsPGroup 2 S) (hSM : S ≤ M)
    (hA : CFSG.Open.IsElemAbelian 2 A) {a : MulAut V} (haA : a ∈ A)
    (haO : a ∉ (oTwo ↥L).map L.subtype) : ∃ y ∈ L, y * a * y⁻¹ ∉ M := by
  by_contra hcon
  push Not at hcon
  obtain ⟨r, s, hr, hr2, -, ⟨e⟩⟩ := hL.dihedral
  have haL : a ∈ L := hL.le haA
  set a' : ↥L := ⟨a, haL⟩ with ha'
  set φ : ↥L →* DihedralGroup (r ^ s) := e.toMonoidHom.comp (QuotientGroup.mk' (oTwo ↥L))
    with hφ
  have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = oTwo ↥L := by
    ext g
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hφa1 : φ a' ≠ 1 := by
    intro h1
    apply haO
    have : a' ∈ oTwo ↥L := hker ▸ (MonoidHom.mem_ker.mpr h1)
    exact ⟨a', this, rfl⟩
  have hφa2 : φ a' ^ 2 = 1 := by
    rw [← map_pow]
    have : a' ^ 2 = 1 := Subtype.ext (by simpa using hA.2 a haA)
    rw [this, map_one]
  have hodd : Odd (r ^ s) := (hr.odd_of_ne_two hr2).pow
  have htop := dihedral_normalClosure_eq_top hodd hφa1 hφa2
  have hN : Subgroup.normalClosure ({a'} : Set ↥L) ≤ M.subgroupOf L := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro b hb
    obtain ⟨c, hc, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hb
    rw [Set.mem_singleton_iff] at hc
    subst hc
    obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    simpa using hcon g g.2
  have hmap : (Subgroup.normalClosure ({a'} : Set ↥L)).map φ = ⊤ := by
    rw [Subgroup.map_normalClosure _ _ hφs, Set.image_singleton, htop]
  have hsup : Subgroup.normalClosure ({a'} : Set ↥L) ⊔ φ.ker = ⊤ := by
    rw [← Subgroup.comap_map_eq, hmap, Subgroup.comap_top]
  have hO : oTwo ↥L ≤ M.subgroupOf L := fun g hg =>
    Subgroup.mem_subgroupOf.mpr (hL.oTwo_le hS hSM ⟨g, hg, rfl⟩)
  have htopM : (⊤ : Subgroup ↥L) ≤ M.subgroupOf L := by
    rw [← hsup, hker]
    exact sup_le hN hO
  apply hL.not_le
  intro l hl
  exact Subgroup.mem_subgroupOf.mp (htopM (Subgroup.mem_top ⟨l, hl⟩))

theorem IsL24.exists_sup_zpowers_eq (hL : IsL24 S M A L) (hS : IsPGroup 2 S) (hSM : S ≤ M)
    (hA : CFSG.Open.IsElemAbelian 2 A) {a : MulAut V} (haA : a ∈ A)
    (haO : a ∉ (oTwo ↥L).map L.subtype) : ∃ y ∈ L, A ⊔ Subgroup.zpowers (y * a * y⁻¹) = L := by
  obtain ⟨y, hyL, hyM⟩ := hL.exists_conj_not_mem hS hSM hA haA haO
  refine ⟨y, hyL, hL.eq_of_le (sup_le hL.le ?_) le_sup_left fun hM =>
    hyM (hM (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))⟩
  exact Subgroup.zpowers_le.mpr (L.mul_mem (L.mul_mem hyL (hL.le haA)) (L.inv_mem hyL))

end L24

structure Hyp25 (S M A L : Subgroup (MulAut V)) (Z₀ W : Subgroup V) : Prop where
  isL24 : IsL24 S M A L
  isPGroup : IsPGroup 2 S
  le_M : S ≤ M
  elemAb : CFSG.Open.IsElemAbelian 2 A
  quadratic : IsQuadratic A
  le_fixV : Z₀ ≤ fixV A
  le_W : Z₀ ≤ W
  le_stabSub : L ≤ stabSub W
  gen : ∀ U : Subgroup V, (∀ l ∈ L, Z₀.map l.toMonoidHom ≤ U) → W ≤ U

namespace Hyp25

variable [Finite V] {S M A L : Subgroup (MulAut V)} {Z₀ W : Subgroup V}

theorem setting (h : Hyp25 S M A L Z₀ W) : Setting25 A L Z₀ W where
  le_L := h.isL24.le
  quad := (commSub_mono le_top le_rfl).trans ((commV_eq_commSub A).symm.le.trans h.quadratic)
  le_fixV := h.le_fixV
  le_W := h.le_W
  le_stabSub := h.le_stabSub
  gen := h.gen

theorem fixV_eq (hV : ∀ v : V, v ^ 2 = 1) (h : Hyp25 S M A L Z₀ W) {a : MulAut V} (haA : a ∈ A)
    (haO : a ∉ (oTwo ↥L).map L.subtype) :
    W ⊓ fixV A = W ⊓ fixV (Subgroup.zpowers a) ∧
      commSub W (Subgroup.zpowers a) ⊔ (W ⊓ fixV L) = W ⊓ fixV A ∧
      commSub W A ⊔ (W ⊓ fixV L) = W ⊓ fixV A ∧
      commSub W (Subgroup.zpowers a) ⊓ (W ⊓ fixV L) = ⊥ ∧
      2 * rk ↥(commSub W (Subgroup.zpowers a)) = mRel (W ⊓ fixV L) W := by
  obtain ⟨y, hyL, hy⟩ := h.isL24.exists_sup_zpowers_eq h.isPGroup h.le_M h.elemAb haA haO
  obtain ⟨k1, k2, k3, k4, k5⟩ := h.setting.key hV haA hyL hy
  have haL : a ∈ L := h.isL24.le haA
  have hs := rk_commSub_add_rk_inf_fixV (h.setting.mem_stabSub haL)
  have hm := mRel_add_rk_of_le (inf_le_left : W ⊓ fixV L ≤ W)
  have hfa : W ⊓ fixV A = W ⊓ fixV (Subgroup.zpowers a) := k1.trans (k2.trans k3)
  refine ⟨hfa, k3.trans hfa.symm, k1.symm, k4, ?_⟩
  rw [← hfa] at hs
  omega

theorem sup_fixV_conj_eq (hV : ∀ v : V, v ^ 2 = 1) (h : Hyp25 S M A L Z₀ W) {x : MulAut V}
    (hxL : x ∈ L) (hxM : x ∉ M) :
    (W ⊓ fixV A) ⊔ (W ⊓ fixV (A.map (MulAut.conj x).toMonoidHom)) = W := by
  obtain ⟨a, haA, haO⟩ := h.isL24.exists_mem_not_mem_oTwo
  obtain ⟨y, hyL, hy⟩ := h.isL24.exists_sup_zpowers_eq h.isPGroup h.le_M h.elemAb haA haO
  obtain ⟨-, -, -, -, k5⟩ := h.setting.key hV haA hyL hy
  exact h.setting.sup_fixV_conj hV k5 hxL (h.isL24.sup_conj x hxL hxM)

theorem mem_of_comm_mem (hV : ∀ v : V, v ^ 2 = 1) (h : Hyp25 S M A L Z₀ W) {a x : MulAut V}
    (haA : a ∈ A) (haO : a ∉ (oTwo ↥L).map L.subtype) (hxL : x ∈ L) (hxM : x ∉ M) {w : V}
    (hw : w ∈ W) (hc : (a * (x * a * x⁻¹)) w * w⁻¹ ∈ W ⊓ fixV L) : w ∈ W ⊓ fixV L := by
  obtain ⟨b1, -, -, b4, -⟩ := h.fixV_eq hV haA haO
  exact h.setting.mem_of_comm_mem haA hxL (h.isL24.sup_conj x hxL hxM) b1.symm b4 hw hc

end Hyp25

end CFSG.RankThree.S4Free.Stell
