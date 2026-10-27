module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenDefs
public import CFSG.Quasithin.Background.D2Involutions

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

private theorem pow_apply_mem {x : MulAut W} {Y : Subgroup W}
    (hY : ∀ y ∈ Y, x y ∈ Y) (n : ℕ) {y : W} (hy : y ∈ Y) : (x ^ n) y ∈ Y := by
  induction n generalizing y with
  | zero => simpa using hy
  | succ n ih =>
      have h := hY _ (ih hy)
      simpa [pow_succ', MulAut.mul_apply] using h

theorem fixV_zpowers_eq_commSub_and_card (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {x b : MulAut W} (hx : orderOf x = p) (hb : orderOf b = 2)
    (hxb : b * x * b⁻¹ = x⁻¹) (hfix : fixV (Subgroup.zpowers x) = ⊥) :
    fixV (Subgroup.zpowers b) = commSub ⊤ (Subgroup.zpowers b) ∧
      Nat.card W = Nat.card (fixV (Subgroup.zpowers b)) ^ 2 := by
  have hb2 : b ^ 2 = 1 := by
    rw [← hb]
    exact pow_orderOf_eq_one b
  have hcomm : fixV (Subgroup.zpowers b) = commV (Subgroup.zpowers b) :=
    fixV_eq_commV_of_inverts hW hfix hb2 hxb
  have hfixb : fixV (Subgroup.zpowers b) = commSub ⊤ (Subgroup.zpowers b) := by
    rw [hcomm, commV_eq_commSub]
  refine ⟨hfixb, ?_⟩
  have hrk := rk_eq_two_mul_of_inverts hW hfix hb2 hxb
  rw [← hcomm] at hrk
  calc Nat.card W = 2 ^ rk W := card_eq_two_pow_rk hW
    _ = 2 ^ (2 * rk ↥(fixV (Subgroup.zpowers b))) := by rw [hrk]
    _ = (2 ^ rk ↥(fixV (Subgroup.zpowers b))) ^ 2 := by
        conv_rhs => rw [← pow_mul]
        congr 1
        exact Nat.mul_comm _ _
    _ = (Nat.card (fixV (Subgroup.zpowers b))) ^ 2 := by
        rw [card_eq_two_pow hW]

theorem card_eq_card_mul_card {b : MulAut W} (hb : b * b = 1) {U A : Subgroup W}
    (hAT : A ≤ commSub ⊤ (Subgroup.zpowers b)) (hTU : fixV (Subgroup.zpowers b) ≤ U)
    (hUA : ∀ u ∈ U, b u * u⁻¹ ∈ A) (hAU : ∀ w : W, b w * w⁻¹ ∈ A → w ∈ U) :
    Nat.card U = Nat.card (fixV (Subgroup.zpowers b)) * Nat.card A := by
  set T : Subgroup W := fixV (Subgroup.zpowers b) with hT
  let ψ : W →* W := commHom b
  have hker : ψ.ker = T := ker_commHom b
  have hrange : ψ.range = commSub ⊤ (Subgroup.zpowers b) := by
    rw [MonoidHom.range_eq_map,
      ← commSub_zpowers_eq_map (W := ⊤) (g := b) (fun _ _ _ _ => Subgroup.mem_top _)]
  have hArange : A ≤ ψ.range := by
    rw [hrange]
    exact hAT
  have hcomap : A.comap ψ = U := by
    ext w
    rw [Subgroup.mem_comap]
    exact ⟨fun h => hAU w (by simpa [ψ, commHom_apply] using h),
      fun h => by simpa [ψ, commHom_apply] using hUA w h⟩
  let f : ↥U →* W := ψ.domRestrict U
  have hrangeA : f.range = A := by
    rw [show f.range = U.map ψ from MonoidHom.domRestrict_range U ψ]
    rw [← hcomap]
    exact Subgroup.map_comap_eq_self hArange
  have hkerf : f.ker = T.subgroupOf U := by
    rw [show f.ker = ψ.ker.subgroupOf U from MonoidHom.ker_domRestrict U ψ, hker]
  have hcardker : Nat.card f.ker = Nat.card T := by
    rw [hkerf]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTU).toEquiv
  have h := Subgroup.card_ker_mul_card_range f
  rw [hcardker, hrangeA] at h
  exact h.symm

theorem le_orbitClosure (x : MulAut W) (A : Subgroup W) : A ≤ orbitClosure x A := by
  intro a ha
  exact Subgroup.mem_iSup_of_mem 0
    (by simpa using Subgroup.mem_map_of_mem ((x ^ 0 : MulAut W) : W →* W) ha)

theorem apply_mem_orbitClosure (x : MulAut W) (A : Subgroup W) {z : W}
    (hz : z ∈ orbitClosure x A) : x z ∈ orbitClosure x A := by
  have hmap : (orbitClosure x A).map ((x : MulAut W) : W →* W) ≤ orbitClosure x A := by
    rw [orbitClosure, Subgroup.map_iSup]
    refine iSup_le fun i => ?_
    rw [Subgroup.map_map]
    refine le_trans ?_ (le_iSup (fun j => A.map ((x ^ j : MulAut W) : W →* W)) (i + 1))
    rintro w ⟨a, ha, rfl⟩
    simpa [MonoidHom.comp_apply, pow_succ', MulAut.mul_apply] using
      Subgroup.mem_map_of_mem ((x ^ (i + 1) : MulAut W) : W →* W) ha
  exact hmap (Subgroup.mem_map_of_mem ((x : MulAut W) : W →* W) hz)

private theorem pow_apply_mem_orbitClosure (x : MulAut W) (A : Subgroup W) (n : ℕ) {z : W}
    (hz : z ∈ orbitClosure x A) : (x ^ n) z ∈ orbitClosure x A := by
  induction n generalizing z with
  | zero => simpa using hz
  | succ n ih =>
      have h := apply_mem_orbitClosure x A (ih hz)
      simpa [pow_succ', MulAut.mul_apply] using h

theorem orbitClosure_le {x : MulAut W} {A Y : Subgroup W} (hAY : A ≤ Y)
    (hxY : ∀ y ∈ Y, x y ∈ Y) : orbitClosure x A ≤ Y := by
  rw [orbitClosure]
  refine iSup_le fun i => ?_
  induction i with
  | zero =>
      have h1 : ((x ^ 0 : MulAut W) : W →* W) = MonoidHom.id W := by
        rw [pow_zero]
        ext
        rfl
      rw [h1, Subgroup.map_id]
      exact hAY
  | succ i ih =>
      intro z hz
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hz
      have hai : (x ^ i) a ∈ Y := ih (Subgroup.mem_map_of_mem ((x ^ i : MulAut W) : W →* W) ha)
      simpa [pow_succ', MulAut.mul_apply] using hxY _ hai

theorem apply_mem_orbitClosure_of_inverts {p : ℕ} {x b : MulAut W} (hx : orderOf x = p)
    (hxb : b * x * b⁻¹ = x⁻¹) {A : Subgroup W} (hA : A ≤ fixV (Subgroup.zpowers b)) {z : W}
    (hz : z ∈ orbitClosure x A) : b z ∈ orbitClosure x A := by
  let OC := orbitClosure x A
  let Y : Subgroup W := OC.comap (b : W →* W)
  have hxY : ∀ y ∈ Y, x y ∈ Y := by
    intro y hy
    rw [Subgroup.mem_comap] at hy ⊢
    have hbx : b * x = x⁻¹ * b := by
      have := congrArg (· * b) hxb
      simpa [mul_assoc] using this
    have h1 : b (x y) = x⁻¹ (b y) := by
      have := congrArg (fun g : MulAut W => g y) hbx
      simpa [MulAut.mul_apply] using this
    have hp_pos : 0 < p := by
      rw [← hx]
      exact orderOf_pos x
    have hxp : x ^ p = 1 := by
      rw [← hx]
      exact pow_orderOf_eq_one x
    have hinv : x⁻¹ = x ^ (p - 1) := by
      have h : x ^ (p - 1) * x = 1 := by
        rw [← pow_succ, show p - 1 + 1 = p from Nat.succ_pred_eq_of_pos hp_pos, hxp]
      exact inv_eq_of_mul_eq_one_left h
    change b (x y) ∈ OC
    change b y ∈ OC at hy
    rw [h1, hinv]
    exact pow_apply_mem_orbitClosure x A (p - 1) hy
  have hAY : A ≤ Y := by
    intro a ha
    rw [Subgroup.mem_comap]
    change b a ∈ OC
    have hba : b a = a := mem_fixV_zpowers_iff.mp (hA ha)
    rw [hba]
    exact le_orbitClosure x A ha
  exact orbitClosure_le hAY hxY hz

theorem index_orbitClosure_le (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x b : MulAut W} (hx : orderOf x = p) (hb : orderOf b = 2) (hxb : b * x * b⁻¹ = x⁻¹)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) {A : Subgroup W}
    (hA : A ≤ fixV (Subgroup.zpowers b)) :
    (orbitClosure x A).index ≤ (A.relIndex (fixV (Subgroup.zpowers b))) ^ 2 := by
  set T : Subgroup W := fixV (Subgroup.zpowers b) with hT
  set OC : Subgroup W := orbitClosure x A with hOC
  set a : ℕ := Nat.card A with ha
  set r : ℕ := A.relIndex T with hr
  have hxp : x ^ p = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hxeq : x = (x ^ 2) ^ ((p + 1) / 2) := by
    obtain ⟨k, hk⟩ := hodd
    have hp1 : p = 2 * k + 1 := hk
    have h2 : 2 * ((p + 1) / 2) = p + 1 := by omega
    rw [← pow_mul, h2, pow_succ, hxp, one_mul]
  have hdisj : A ⊓ A.map ((x : MulAut W) : W →* W) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro y hy
    obtain ⟨t, htA, hyt⟩ := Subgroup.mem_map.mp hy.2
    have hyT : y ∈ T := hA hy.1
    have hby : b y = y := mem_fixV_zpowers_iff.mp hyT
    have hbt : b t = t := mem_fixV_zpowers_iff.mp (hA htA)
    have hbx : b * x = x⁻¹ * b := by
      have := congrArg (· * b) hxb
      simpa [mul_assoc] using this
    have h1 : b (x t) = x⁻¹ t := by
      rw [← MulAut.mul_apply W b x t, hbx, MulAut.mul_apply W, hbt]
    have hyt' : x t = y := hyt
    have hxt : x t = x⁻¹ t := by
      rw [← h1, hyt', hby]
    have h2 : (x ^ 2) t = t := by
      have := congrArg (fun w => x w) hxt
      simpa [pow_two, MulAut.mul_apply] using this
    have hpow : ∀ n : ℕ, ((x ^ 2) ^ n) t = t := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [pow_succ', MulAut.mul_apply, ih, h2]
    have hxt_fix : x t = t := by
      rw [hxeq]
      exact hpow _
    have htfix : t ∈ fixV (Subgroup.zpowers x) := mem_fixV_zpowers_iff.mpr hxt_fix
    rw [hfix] at htfix
    have ht1 : t = 1 := by simpa using htfix
    rw [Subgroup.mem_bot]
    rw [← hyt, ht1, map_one]
  let f : ↥A × ↥A → ↥OC := fun u =>
    ⟨(u.1 : W) * x u.2,
      OC.mul_mem (le_orbitClosure x A u.1.2)
        (apply_mem_orbitClosure x A (le_orbitClosure x A u.2.2))⟩
  have hinj : Function.Injective f := by
    rintro ⟨a1, a2⟩ ⟨a1', a2'⟩ heq
    have hval : (a1 : W) * x a2 = (a1' : W) * x a2' := congrArg Subtype.val heq
    have hdiff : (a1' : W)⁻¹ * a1 = x ((a2' : W) * (a2 : W)⁻¹) := by
      have := congrArg (fun w => (a1' : W)⁻¹ * w * (x (a2 : W))⁻¹) hval
      simpa [mul_assoc, map_mul, map_inv] using this
    have hmem : (a1' : W)⁻¹ * a1 ∈ A ⊓ A.map ((x : MulAut W) : W →* W) := by
      constructor
      · exact A.mul_mem (A.inv_mem a1'.2) a1.2
      · rw [hdiff]
        exact Subgroup.mem_map_of_mem ((x : MulAut W) : W →* W)
          (A.mul_mem a2'.2 (A.inv_mem a2.2))
    rw [hdisj] at hmem
    have hone : (a1' : W)⁻¹ * a1 = 1 := by simpa using hmem
    have ha1 : (a1 : W) = a1' := by
      have := congrArg (fun w => (a1' : W) * w) hone
      simpa [mul_assoc] using this
    have hx2 : x (a2 : W) = x a2' := by
      apply mul_left_cancel (a := (a1' : W))
      simpa [ha1] using hval
    have ha2 : (a2 : W) = a2' := x.injective hx2
    exact Prod.ext (Subtype.ext ha1) (Subtype.ext ha2)
  have hcardle : a ^ 2 ≤ Nat.card OC := by
    have := Nat.card_le_card_of_injective f hinj
    rw [Nat.card_prod] at this
    simpa [a, pow_two] using this
  have hcardW : Nat.card W = Nat.card T ^ 2 :=
    (fixV_zpowers_eq_commSub_and_card hW hp hp2 hx hb hxb hfix).2
  have hTcard : Nat.card T = r * a := by
    have := Subgroup.relIndex_mul_card A T
    rw [inf_eq_left.mpr hA] at this
    simpa [r, a] using this.symm
  have hcardOC : Nat.card OC * OC.index = Nat.card W := Subgroup.card_mul_index OC
  have hkey : OC.index * a ^ 2 ≤ r ^ 2 * a ^ 2 := by
    calc OC.index * a ^ 2 ≤ OC.index * Nat.card OC := Nat.mul_le_mul_left _ hcardle
      _ = Nat.card OC * OC.index := Nat.mul_comm _ _
      _ = Nat.card W := hcardOC
      _ = Nat.card T ^ 2 := hcardW
      _ = (r * a) ^ 2 := by rw [hTcard]
      _ = r ^ 2 * a ^ 2 := by rw [mul_pow]
  exact Nat.le_of_mul_le_mul_right hkey (pow_pos (card_subgroup_pos A) 2)

theorem even_rk_of_invariant (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x b : MulAut W} (hx : orderOf x = p) (hb : orderOf b = 2) (hxb : b * x * b⁻¹ = x⁻¹)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) {Z : Subgroup W} (hxZ : ∀ z ∈ Z, x z ∈ Z)
    (hbZ : ∀ z ∈ Z, b z ∈ Z) : Even (rk ↥Z) := by
  have hb2 : b ^ 2 = 1 := by
    rw [← hb]
    exact pow_orderOf_eq_one b
  have hxp : x ^ p = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hp_pos : 0 < p := by
    rw [← hx]
    exact orderOf_pos x
  have hinv : x⁻¹ = x ^ (p - 1) := by
    have h : x ^ (p - 1) * x = 1 := by
      rw [← pow_succ, show p - 1 + 1 = p from Nat.succ_pred_eq_of_pos hp_pos, hxp]
    exact inv_eq_of_mul_eq_one_left h
  have hxst : x ∈ stabSub Z := by
    rw [mem_stabSub]
    intro u
    constructor
    · intro hu
      have h := pow_apply_mem hxZ (p - 1) hu
      rwa [show (x ^ (p - 1)) (x u) = u by
        rw [← hinv]
        exact MulAut.inv_apply_self W x u] at h
    · exact hxZ u
  have hbst : b ∈ stabSub Z := by
    rw [mem_stabSub]
    intro u
    constructor
    · intro hu
      have hbu : b (b u) = u := by
        have := congrArg (fun g : MulAut W => g u) hb2
        simpa [pow_two, MulAut.mul_apply] using this
      have h := hbZ (b u) hu
      rwa [hbu] at h
    · exact hbZ u
  let xZ : MulAut ↥Z := resHom Z ⟨x, hxst⟩
  let bZ : MulAut ↥Z := resHom Z ⟨b, hbst⟩
  have hbZ2 : bZ ^ 2 = 1 := by
    have h2 : (⟨b, hbst⟩ : stabSub Z) ^ 2 = 1 := by
      apply Subtype.ext
      simpa using hb2
    have hthis : (resHom Z ⟨b, hbst⟩) ^ 2 = 1 := by
      rw [← map_pow, h2, map_one]
    simpa [bZ] using hthis
  have hbZxZ : bZ * xZ * bZ⁻¹ = xZ⁻¹ := by
    have hconj : (⟨b, hbst⟩ : stabSub Z) * ⟨x, hxst⟩ * (⟨b, hbst⟩ : stabSub Z)⁻¹ =
        (⟨x, hxst⟩ : stabSub Z)⁻¹ := by
      apply Subtype.ext
      simpa using hxb
    have hthis := congrArg (resHom Z) hconj
    simpa only [bZ, xZ, map_mul, map_inv] using hthis
  have hfixZ : fixV (Subgroup.zpowers xZ) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro u hu
    have hxu : xZ u = u := mem_fixV_zpowers_iff.mp hu
    have h1 : ((xZ u : ↥Z) : W) = x (u : W) := resHom_apply Z ⟨x, hxst⟩ u
    have h2 : x (u : W) = (u : W) := by rw [← h1, hxu]
    have hu' : (u : W) ∈ fixV (Subgroup.zpowers x) := mem_fixV_zpowers_iff.mpr h2
    rw [hfix] at hu'
    have h1' : (u : W) = 1 := by simpa using hu'
    exact Subgroup.mem_bot.mpr (Subtype.ext h1')
  have hVZ : ∀ u : ↥Z, u ^ 2 = 1 := fun u => by
    apply Subtype.ext
    simpa using hW (u : W)
  have hrk := rk_eq_two_mul_of_inverts hVZ hfixZ hbZ2 hbZxZ
  rw [hrk]
  exact even_two_mul _

theorem card_modEq_card_inf_fixV {p : ℕ} (hp : p.Prime) {x : MulAut W} (hx : orderOf x = p)
    {Y : Subgroup W} (hY : ∀ y ∈ Y, x y ∈ Y) :
    Nat.card Y ≡ Nat.card ↥(Y ⊓ fixV (Subgroup.zpowers x)) [MOD p] := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype ↥Y := Fintype.ofFinite ↥Y
  let σ : Function.End ↥Y := fun y => ⟨x y, hY y y.2⟩
  have hσpow : ∀ (n : ℕ) (y : ↥Y),
      (σ ^ n) y = ⟨(x ^ n) (y : W), pow_apply_mem hY n y.2⟩ := by
    intro n
    induction n with
    | zero =>
        intro y
        apply Subtype.ext
        rfl
    | succ n ih =>
        intro y
        apply Subtype.ext
        have hval := congrArg (fun z : ↥Y => (z : W)) (ih y)
        rw [pow_succ']
        change x ((σ ^ n) y : W) = (x ^ (n + 1)) (y : W)
        rw [hval, pow_succ']
        rfl
  have hxp : x ^ p = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hσ : σ ^ p ^ 1 = 1 := by
    rw [pow_one]
    funext y
    rw [hσpow p y]
    apply Subtype.ext
    change (x ^ p) (y : W) = (y : W)
    rw [hxp]
    rfl
  let e : ↥(Function.fixedPoints (σ : ↥Y → ↥Y)) ≃ ↥(Y ⊓ fixV (Subgroup.zpowers x)) :=
    { toFun := fun y => ⟨(y : ↥Y).1, ⟨(y : ↥Y).2, by
        change ((y : ↥Y) : W) ∈ fixV (Subgroup.zpowers x)
        rw [mem_fixV_zpowers_iff]
        simpa [σ] using congrArg Subtype.val y.2⟩⟩
      invFun := fun z => ⟨⟨(z : W), z.2.1⟩, by
        apply Subtype.ext
        exact mem_fixV_zpowers_iff.mp z.2.2⟩
      left_inv := fun y => by ext; rfl
      right_inv := fun z => by ext; rfl }
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := σ) (p := p) (n := 1) hσ
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hmod
  rwa [Nat.card_congr e] at hmod

theorem card_modEq_one_of_fixV_eq_bot {p : ℕ} (hp : p.Prime) {x : MulAut W} (hx : orderOf x = p)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) {Y : Subgroup W} (hY : ∀ y ∈ Y, x y ∈ Y) :
    Nat.card Y ≡ 1 [MOD p] := by
  have h := card_modEq_card_inf_fixV (W := W) hp hx hY
  rw [hfix, inf_bot_eq] at h
  simpa using h

end CFSG.LocalAnalysis.WeakClosure81
