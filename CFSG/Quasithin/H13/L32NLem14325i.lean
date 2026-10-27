module

public import CFSG.Quasithin.H13.L32NLem14325h

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

namespace L14325

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)}

omit [Finite G] in
theorem zU_comm {a b : G} (ha : a ∈ centerOf (fsuU T V)) (hb : b ∈ centerOf (fsuU T V)) :
    a * b = b * a :=
  (Subgroup.mem_centralizer_iff.mp ha.2 b hb.1).symm

abbrev vP (T V : Subgroup G) (c : G) : Subgroup G := conjClosure (Subgroup.zpowers c) (l32nH T V)

omit [Finite G] in
theorem conj_mem_vP {c h v : G} (hh : h ∈ l32nH T V) (hv : v ∈ vP T V c) :
    h * v * h⁻¹ ∈ vP T V c :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ hh) v).mp hv

omit [Finite G] in
theorem c_mem_vP (c : G) : c ∈ vP T V c := le_conjClosure _ _ (Subgroup.mem_zpowers c)

namespace CtxI

variable (C : CtxI G T L V V₂ g D)
include C

theorem vH_sq {v : G} (hv : v ∈ vH T L V) : v * v = 1 := by
  have := C.ctx.red.2.2.1.2 v hv
  rwa [pow_two] at this

theorem vH_comm {v w : G} (hv : v ∈ vH T L V) (hw : w ∈ vH T L V) : v * w = w * v :=
  congrArg Subtype.val (C.ctx.red.2.2.1.1.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩)

omit [Finite G] C in
theorem conj_mem_vH {h v : G} (hh : h ∈ l32nH T V) (hv : v ∈ vH T L V) : h * v * h⁻¹ ∈ vH T L V :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ hh) v).mp hv

omit [Finite G] C in
theorem conj_mem_zU {h w : G} (hh : h ∈ l32nH T V) (hw : w ∈ centerOf (fsuU T V)) :
    h * w * h⁻¹ ∈ centerOf (fsuU T V) :=
  (Subgroup.mem_normalizer_iff.mp (L14332.l32nH_le_normalizer_zU hh) w).mp hw

theorem comm_eq {x : G} (hx : x ∈ CFSG.conjugate (centerOf (fsuU T V)) g) {w w' : G}
    (hw : w ∈ centerOf (fsuU T V)) (hw' : w' ∈ centerOf (fsuU T V))
    (h1 : x * w * x⁻¹ * w⁻¹ ≠ 1) (h1' : x * w' * x⁻¹ * w'⁻¹ ≠ 1) :
    x * w * x⁻¹ * w⁻¹ = x * w' * x⁻¹ * w'⁻¹ := by
  set Z₀ := centerOf (fsuU T V) ⊓ CFSG.conjugate (fsuU T V) g with hZ₀
  have hxZ : ∀ n ∈ Z₀, x * n = n * x := fun n hn => comm_of_mem_conj hx hn
  have hnot : ∀ u ∈ centerOf (fsuU T V), x * u * x⁻¹ * u⁻¹ ≠ 1 → u ∉ Z₀ := by
    intro u _ hu hu0
    apply hu
    rw [hxZ u hu0]
    group
  have hidx : (Z₀.subgroupOf (centerOf (fsuU T V))).index = 2 := C.relIdx
  have hm := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨w⁻¹, (centerOf _).inv_mem hw⟩)
    (b := ⟨w', hw'⟩)).mpr (iff_of_false (fun h => hnot w hw h1 (by
      have := Z₀.inv_mem (Subgroup.mem_subgroupOf.mp h)
      simpa using this)) (fun h => hnot w' hw' h1' (Subgroup.mem_subgroupOf.mp h)))
  have hn : w⁻¹ * w' ∈ Z₀ := Subgroup.mem_subgroupOf.mp hm
  have hnc : x * (w⁻¹ * w') * x⁻¹ = w⁻¹ * w' := by
    rw [hxZ _ hn]
    group
  calc x * w * x⁻¹ * w⁻¹ = x * w * x⁻¹ * (x * (w⁻¹ * w') * x⁻¹) * (w⁻¹ * w')⁻¹ * w⁻¹ := by
        rw [hnc]; group
    _ = x * w' * x⁻¹ * w'⁻¹ := by group

structure TransData (C : CtxI G T L V V₂ g D) (x c : G) : Prop where
  x_mem : x ∈ CFSG.conjugate (centerOf (fsuU T V)) g
  x_ne : ∀ hxN : x ∈ Subgroup.normalizer (fsuU T V : Set G), D.ρ ⟨x, hxN⟩ ≠ 1
  c_mem : c ∈ vH T L V
  c_ne : c ≠ 1
  comm : ∀ w ∈ centerOf (fsuU T V), x * w * x⁻¹ * w⁻¹ = 1 ∨ x * w * x⁻¹ * w⁻¹ = c

theorem exists_transData : ∃ x c, TransData C x c := by
  obtain ⟨⟨γ, hγZ⟩, hγ1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp C.ctx.zUg_ne
  obtain ⟨x, hx, hxN, hxγ⟩ := (L128A.HatU.mem_img D).mp hγZ
  have hxne : ∀ hxN' : x ∈ Subgroup.normalizer (fsuU T V : Set G), D.ρ ⟨x, hxN'⟩ ≠ 1 :=
    fun _ h1 => hγ1 (Subtype.ext (by show γ = 1; rw [← hxγ]; exact h1))
  have hxH : x ∈ l32nH T V := C.ctx.zUg_le hx
  have hxc : x ∉ Subgroup.centralizer (vH T L V : Set G) := fun hxc =>
    hxne hxN ((L14332.rho_eq_one_iff_mem hxH hxN).mpr
      (C.mem_cHat_of_mem_centralizer (zUg_le_kI hx) hxc))
  obtain ⟨v₀, hv₀, hv₀x⟩ : ∃ v₀ ∈ vH T L V, x * v₀ * x⁻¹ * v₀⁻¹ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hxc
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have := hcon v hv
    calc v * x = x * v * x⁻¹ * v⁻¹ * v * x := by rw [this]; group
      _ = x * v := by group
  have hv₀Z : v₀ ∈ centerOf (fsuU T V) := C.ctx.vH_le hv₀
  refine ⟨x, x * v₀ * x⁻¹ * v₀⁻¹, ⟨hx, hxne, ?_, hv₀x, fun w hw => ?_⟩⟩
  · exact (vH T L V).mul_mem (conj_mem_vH hxH hv₀) ((vH T L V).inv_mem hv₀)
  · by_cases h1 : x * w * x⁻¹ * w⁻¹ = 1
    · exact Or.inl h1
    · exact Or.inr (C.comm_eq hx hw hv₀Z h1 hv₀x)

namespace TransData

variable {C} {x c : G} (X : TransData C x c)
include X

theorem x_H : x ∈ l32nH T V := C.ctx.zUg_le X.x_mem

theorem comm_conj {h : G} (hh : h ∈ l32nH T V) {w : G} (hw : w ∈ centerOf (fsuU T V)) :
    h * x * h⁻¹ * w * (h * x * h⁻¹)⁻¹ * w⁻¹ = 1 ∨
      h * x * h⁻¹ * w * (h * x * h⁻¹)⁻¹ * w⁻¹ = h * c * h⁻¹ := by
  have hw' : h⁻¹ * w * h ∈ centerOf (fsuU T V) := by
    simpa using conj_mem_zU ((l32nH T V).inv_mem hh) hw
  have e : h * x * h⁻¹ * w * (h * x * h⁻¹)⁻¹ * w⁻¹ =
      h * (x * (h⁻¹ * w * h) * x⁻¹ * (h⁻¹ * w * h)⁻¹) * h⁻¹ := by group
  rw [e]
  rcases X.comm _ hw' with h1 | h1 <;> rw [h1]
  · left; group
  · exact Or.inr rfl

theorem vP_le : vP T V c ≤ vH T L V :=
  conjClosure_le fun h hh z hz => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact conj_mem_vH hh ((vH T L V).zpow_mem X.c_mem k)

theorem zg_cases {z : G} (hz : z ∈ CFSG.conjugate (centerOf (fsuU T V)) g) :
    (∀ w ∈ centerOf (fsuU T V), z * w * z⁻¹ = w) ∨
      ∀ w ∈ centerOf (fsuU T V), z * w * z⁻¹ = x * w * x⁻¹ := by
  have hzH : z ∈ l32nH T V := C.ctx.zUg_le hz
  have hzN := L14332.l32nH_le_normalizer_fsuU T V hzH
  have hxN := L14332.l32nH_le_normalizer_fsuU T V X.x_H
  have hρz : D.ρ ⟨z, hzN⟩ ∈ D.img (CFSG.conjugate (centerOf (fsuU T V)) g) :=
    L128A.HatU.rho_mem_img D hz hzN
  have hρx : D.ρ ⟨x, hxN⟩ ∈ D.img (CFSG.conjugate (centerOf (fsuU T V)) g) :=
    L128A.HatU.rho_mem_img D X.x_mem hxN
  have hU : ∀ u ∈ fsuU T V, ∀ w ∈ centerOf (fsuU T V), u * w * u⁻¹ = w := fun u hu w hw => by
    rw [Subgroup.mem_centralizer_iff.mp hw.2 u hu]
    group
  have h2 : ∀ a b : ↥(D.img (CFSG.conjugate (centerOf (fsuU T V)) g)), a ≠ 1 → b ≠ 1 → a = b :=
    fun a b ha hb => by
      have : Nat.card ↥(D.img (CFSG.conjugate (centerOf (fsuU T V)) g)) = 2 := C.card_zd
      rcases (Nat.card_eq_two_iff' (1 : ↥(D.img (CFSG.conjugate (centerOf (fsuU T V)) g)))).mp
        this with ⟨q, hq1, hq⟩
      rw [hq a ha, hq b hb]
  by_cases hz1 : D.ρ ⟨z, hzN⟩ = 1
  · left
    exact hU z (C.zgU z hz ((L14332.rho_eq_one_iff_mem hzH hzN).mp hz1))
  · right
    have he : (⟨_, hρz⟩ : ↥(D.img (CFSG.conjugate (centerOf (fsuU T V)) g))) = ⟨_, hρx⟩ :=
      h2 _ _ (fun h => hz1 (congrArg Subtype.val h)) (fun h => X.x_ne hxN (congrArg Subtype.val h))
    have hzx : z * x⁻¹ ∈ CFSG.conjugate (centerOf (fsuU T V)) g :=
      Subgroup.mul_mem _ hz (Subgroup.inv_mem _ X.x_mem)
    have hzxH : z * x⁻¹ ∈ l32nH T V := C.ctx.zUg_le hzx
    have hzxN := L14332.l32nH_le_normalizer_fsuU T V hzxH
    have hρzx : D.ρ ⟨z * x⁻¹, hzxN⟩ = 1 := by
      have e : (⟨z * x⁻¹, hzxN⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) =
          ⟨z, hzN⟩ * ⟨x, hxN⟩⁻¹ := rfl
      rw [e, map_mul, map_inv]
      have := congrArg Subtype.val he
      simp only at this
      rw [this, mul_inv_cancel]
    have huU := C.zgU _ hzx ((L14332.rho_eq_one_iff_mem hzxH hzxN).mp hρzx)
    intro w hw
    have hxw : x * w * x⁻¹ ∈ centerOf (fsuU T V) := conj_mem_zU X.x_H hw
    calc z * w * z⁻¹ = (z * x⁻¹) * (x * w * x⁻¹) * (z * x⁻¹)⁻¹ := by group
      _ = x * w * x⁻¹ := hU _ huU _ hxw

theorem comm_mem_vP {k : G} (hk : k ∈ kI T V g) {w : G} (hw : w ∈ centerOf (fsuU T V)) :
    k * w * k⁻¹ * w⁻¹ ∈ vP T V c := by
  let S : Subgroup G :=
    { carrier := {k | k ∈ l32nH T V ∧
        ∀ w ∈ centerOf (fsuU T V), k * w * k⁻¹ * w⁻¹ ∈ vP T V c}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨(l32nH T V).mul_mem ha hb, fun w hw => ?_⟩
        have e : a * b * w * (a * b)⁻¹ * w⁻¹ =
            a * (b * w * b⁻¹ * w⁻¹) * a⁻¹ * (a * w * a⁻¹ * w⁻¹) := by group
        rw [e]
        exact (vP T V c).mul_mem (conj_mem_vP ha (hb' w hw)) (ha' w hw)
      one_mem' := ⟨(l32nH T V).one_mem, fun w _ => by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨(l32nH T V).inv_mem ha, fun w hw => ?_⟩
        have hw' : a⁻¹ * w * a⁻¹⁻¹ ∈ centerOf (fsuU T V) := conj_mem_zU ((l32nH T V).inv_mem ha) hw
        have h1 := ha' _ hw'
        have e : a * (a⁻¹ * w * a⁻¹⁻¹) * a⁻¹ * (a⁻¹ * w * a⁻¹⁻¹)⁻¹ = w * (a⁻¹ * w * a)⁻¹ := by
          group
        rw [e] at h1
        have h2 := (vP T V c).inv_mem h1
        have hc : a⁻¹ * w * a⁻¹⁻¹ * w⁻¹ = (w * (a⁻¹ * w * a)⁻¹)⁻¹ := by group
        rw [hc]
        exact h2 }
  have hKS : kI T V g ≤ S := conjClosure_le fun h hh z hz => by
    refine ⟨(l32nH T V).mul_mem ((l32nH T V).mul_mem hh (C.ctx.zUg_le hz))
      ((l32nH T V).inv_mem hh), fun w hw => ?_⟩
    have hw' : h⁻¹ * w * h ∈ centerOf (fsuU T V) := by
      simpa using conj_mem_zU ((l32nH T V).inv_mem hh) hw
    have e : h * z * h⁻¹ * w * (h * z * h⁻¹)⁻¹ * w⁻¹ =
        h * (z * (h⁻¹ * w * h) * z⁻¹) * h⁻¹ * w⁻¹ := by group
    rw [e]
    rcases X.zg_cases hz with h1 | h1
    · rw [h1 _ hw', show h * (h⁻¹ * w * h) * h⁻¹ * w⁻¹ = 1 by group]
      exact (vP T V c).one_mem
    · rw [h1 _ hw']
      have e2 : h * (x * (h⁻¹ * w * h) * x⁻¹) * h⁻¹ * w⁻¹ =
          h * x * h⁻¹ * w * (h * x * h⁻¹)⁻¹ * w⁻¹ := by group
      rw [e2]
      rcases X.comm_conj hh hw with h2 | h2 <;> rw [h2]
      · exact (vP T V c).one_mem
      · exact conj_mem_vP hh (c_mem_vP c)
  exact (hKS hk).2 w hw

end TransData

theorem exists_three : ∃ y ∈ kI T V g, ∃ k : ℕ, y ^ (3 ^ k) = 1 ∧
    ∃ hyN : y ∈ Subgroup.normalizer (fsuU T V : Set G), D.ρ ⟨y, hyN⟩ ^ 3 = 1 ∧
      D.ρ ⟨y, hyN⟩ ≠ 1 := by
  obtain ⟨e⟩ := C.iso
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set σ : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2 with hσ
  have hσ3 : σ ^ 3 = 1 := by decide
  have hσ1 : σ ≠ 1 := by decide
  obtain ⟨⟨γ, hγ⟩, hγe⟩ := e.surjective σ
  obtain ⟨k₀, hk₀, hk₀N, hk₀γ⟩ := (L128A.HatU.mem_img D).mp hγ
  have hγ3 : γ ^ 3 = 1 := by
    have : (⟨γ, hγ⟩ : ↥(D.img (kI T V g))) ^ 3 = 1 := e.injective (by rw [map_pow, hγe, hσ3,
      map_one])
    simpa using congrArg Subtype.val this
  have hγ1 : γ ≠ 1 := fun h => hσ1 (by
    rw [← hγe]
    have : (⟨γ, hγ⟩ : ↥(D.img (kI T V g))) = 1 := Subtype.ext h
    rw [this, map_one])
  set u : ↥(Subgroup.normalizer (fsuU T V : Set G)) := ⟨k₀, hk₀N⟩ with hu
  have ho0 : orderOf (k₀ : G) ≠ 0 := (orderOf_pos k₀).ne'
  obtain ⟨n, m, hm3, hom⟩ := Nat.exists_eq_pow_mul_and_not_dvd ho0 3 (by norm_num)
  have hγo : orderOf γ = 3 := orderOf_eq_prime hγ3 hγ1
  refine ⟨k₀ ^ m, (kI T V g).pow_mem hk₀ m, n, ?_, (Subgroup.normalizer _).pow_mem hk₀N m, ?_⟩
  · rw [← pow_mul, mul_comm, ← hom, pow_orderOf_eq_one]
  · have e1 : (⟨k₀ ^ m, (Subgroup.normalizer _).pow_mem hk₀N m⟩ :
        ↥(Subgroup.normalizer (fsuU T V : Set G))) = u ^ m := rfl
    rw [e1, map_pow, hu, hk₀γ]
    refine ⟨by rw [← pow_mul, mul_comm, pow_mul, hγ3, one_pow], fun h1 => hm3 ?_⟩
    rw [← hγo]
    exact orderOf_dvd_of_pow_eq_one h1

namespace TransData

variable {C} {x c : G} (X : TransData C x c)
include X

theorem exists_move : ∃ v ∈ vP T V c, x * v * x⁻¹ * v⁻¹ = c := by
  by_contra hcon
  push Not at hcon
  have hxP : ∀ v ∈ vP T V c, x * v * x⁻¹ = v := by
    intro v hv
    rcases X.comm v (C.ctx.vH_le (X.vP_le hv)) with h | h
    · calc x * v * x⁻¹ = x * v * x⁻¹ * v⁻¹ * v := by group
        _ = v := by rw [h, one_mul]
    · exact absurd h (hcon v hv)
  have hKP : ∀ k ∈ kI T V g, ∀ v ∈ vP T V c, k * v * k⁻¹ = v := by
    let S : Subgroup G := Subgroup.centralizer (vP T V c : Set G)
    have hKS : kI T V g ≤ S := conjClosure_le fun h hh z hz => by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv' : h⁻¹ * v * h ∈ vP T V c := by
        simpa using conj_mem_vP ((l32nH T V).inv_mem hh) hv
      have hz' : z * (h⁻¹ * v * h) * z⁻¹ = h⁻¹ * v * h := by
        rcases X.zg_cases hz with h1 | h1
        · exact h1 _ (C.ctx.vH_le (X.vP_le hv'))
        · rw [h1 _ (C.ctx.vH_le (X.vP_le hv'))]
          exact hxP _ hv'
      have hcomm : h⁻¹ * v * h * z = z * (h⁻¹ * v * h) := by
        calc h⁻¹ * v * h * z = z * (h⁻¹ * v * h) * z⁻¹ * z := by rw [hz']
          _ = z * (h⁻¹ * v * h) := by group
      calc v * (h * z * h⁻¹) = h * (h⁻¹ * v * h * z) * h⁻¹ := by group
        _ = h * (z * (h⁻¹ * v * h)) * h⁻¹ := by rw [hcomm]
        _ = h * z * h⁻¹ * v := by group
    intro k hk v hv
    have := Subgroup.mem_centralizer_iff.mp (hKS hk) v hv
    calc k * v * k⁻¹ = v * k * k⁻¹ := by rw [this]
      _ = v := by group
  obtain ⟨y, hyK, n, hyn, hyN, hy3, hy1⟩ := C.exists_three
  have hyZ : ∀ w ∈ centerOf (fsuU T V), y * w * y⁻¹ = w := by
    intro w hw
    set d := y * w * y⁻¹ * w⁻¹ with hd
    have hdP : d ∈ vP T V c := X.comm_mem_vP hyK hw
    have hyd : y * d * y⁻¹ = d := hKP y hyK d hdP
    have hpow : ∀ j : ℕ, y ^ j * w * (y ^ j)⁻¹ = d ^ j * w := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have hydj : y * d ^ j * y⁻¹ = d ^ j := by
          have := map_pow (MulAut.conj y) d j
          simp only [MulAut.conj_apply] at this
          rw [this, hyd]
        have hdw : d ^ j * w ∈ centerOf (fsuU T V) := (centerOf _).mul_mem
          ((centerOf _).pow_mem (C.ctx.vH_le (X.vP_le hdP)) j) hw
        calc y ^ (j + 1) * w * (y ^ (j + 1))⁻¹ = y * (y ^ j * w * (y ^ j)⁻¹) * y⁻¹ := by
              rw [pow_succ']; group
          _ = y * (d ^ j * w) * y⁻¹ := by rw [ih]
          _ = (y * d ^ j * y⁻¹) * (y * w * y⁻¹) := by group
          _ = d ^ j * (d * w) := by rw [hydj, hd]; group
          _ = d ^ (j + 1) * w := by rw [pow_succ]; group
    have h1 := hpow (3 ^ n)
    rw [hyn] at h1
    have hd3 : d ^ (3 ^ n) = 1 := by
      have : w = d ^ (3 ^ n) * w := by simpa using h1
      calc d ^ (3 ^ n) = d ^ (3 ^ n) * w * w⁻¹ := by group
        _ = 1 := by rw [← this]; group
    have hdd : d * d = 1 := C.vH_sq (X.vP_le hdP)
    have hd1 : d = 1 := by
      obtain ⟨j, hj⟩ : ∃ j, 3 ^ n = 2 * j + 1 := Odd.exists_bit1 (Odd.pow (by decide))
      rw [hj, pow_succ, pow_mul, _root_.sq, hdd, one_pow, one_mul] at hd3
      exact hd3
    calc y * w * y⁻¹ = d * w := by rw [hd]; group
      _ = w := by rw [hd1, one_mul]
  have hyc : y ∈ Subgroup.centralizer (vH T L V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have := hyZ v (C.ctx.vH_le hv)
    calc v * y = y * v * y⁻¹ * y := by rw [this]
      _ = y * v := by group
  exact hy1 ((L14332.rho_eq_one_iff_mem (C.kI_le hyK) hyN).mpr
    (C.mem_cHat_of_mem_centralizer hyK hyc))

end TransData

end CtxI

end L14325

end CFSG.Quasithin.H13
