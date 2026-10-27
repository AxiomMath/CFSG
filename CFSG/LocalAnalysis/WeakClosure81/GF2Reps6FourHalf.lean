module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6FourLift
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6OddTr
public import CFSG.Open.Defs
import CFSG.GroupTheory.ConjKerCenter

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open CFSG.Quasithin Subgroup

variable {V : Type*} [CommGroup V]

private theorem mulAut_conj_apply_eq {X : Type*} [Group X] (f : MulAut X) (x : X) :
    MulAut.conj (f x) = f * MulAut.conj x * f⁻¹ := by
  ext y
  rw [MulAut.conj_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply,
    map_mul, map_mul, map_inv, MulAut.apply_inv_self]

private theorem conj_mk_mul_conj_eq {L A : Subgroup (MulAut V)}
    (hAL : ∀ u ∈ A, ∀ l ∈ L, u * l * u⁻¹ ∈ L) {a : MulAut V} (haA : a ∈ A)
    (ha : a * a = 1) {β : MulAut (↥L ⧸ center ↥L)}
    (hβ : ∀ l : ↥L, β (QuotientGroup.mk l) =
      QuotientGroup.mk (⟨a * l * a⁻¹, hAL a haA l l.2⟩ : ↥L))
    {g : ↥L} {w : MulAut V} (hw : w = a * ((g : MulAut V) * a * (g : MulAut V)⁻¹))
    (hwL : w ∈ L) :
    MulAut.conj (QuotientGroup.mk (⟨w, hwL⟩ : ↥L) : ↥L ⧸ center ↥L) =
      β * (MulAut.conj (QuotientGroup.mk g : ↥L ⧸ center ↥L) * β *
        (MulAut.conj (QuotientGroup.mk g : ↥L ⧸ center ↥L))⁻¹) := by
  have haa : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hβ2 : β * β = 1 := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H l =>
      rw [MulAut.mul_apply, hβ l,
        hβ (⟨a * (l : MulAut V) * a⁻¹, hAL a haA _ l.2⟩ : ↥L)]
      refine congrArg QuotientGroup.mk (Subtype.ext ?_)
      have hainv : a⁻¹ * a⁻¹ = 1 := by rw [← mul_inv_rev, ha, inv_one]
      calc a * (a * (l : MulAut V) * a⁻¹) * a⁻¹
          = (a * a) * (l : MulAut V) * (a⁻¹ * a⁻¹) := by group
        _ = (l : MulAut V) := by rw [ha, hainv, one_mul, mul_one]
  have hw' : (⟨w, hwL⟩ : ↥L) = ⟨a * (g : MulAut V) * a⁻¹, hAL a haA _ g.2⟩ * g⁻¹ := by
    apply Subtype.ext
    change w = (a * (g : MulAut V) * a⁻¹) * (g : MulAut V)⁻¹
    rw [hw, haa]
    group
  have hπw : (QuotientGroup.mk (⟨w, hwL⟩ : ↥L) : ↥L ⧸ center ↥L) =
      β (QuotientGroup.mk g) * (QuotientGroup.mk g)⁻¹ := by
    conv_lhs => rw [hw']
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hβ g]
  rw [hπw, map_mul, map_inv, mulAut_conj_apply_eq β (QuotientGroup.mk g),
    inv_eq_of_mul_eq_one_right hβ2]
  group

theorem exists_odd_orderOf_mul_conj_eq [Finite V] {L A : Subgroup (MulAut V)}
    (hL : CFSG.Open.IsQuasisimple ↥L) (hZ : Odd (Nat.card (center ↥L)))
    (hAL : ∀ u ∈ A, ∀ l ∈ L, u * l * u⁻¹ ∈ L) {a : MulAut V} (haA : a ∈ A) (ha : a * a = 1)
    {β : MulAut (↥L ⧸ center ↥L)}
    (hβ : ∀ l : ↥L, β (QuotientGroup.mk l) =
      QuotientGroup.mk (⟨a * l * a⁻¹, hAL a haA l l.2⟩ : ↥L))
    (g : ↥L) :
    ∃ r : ℕ, Odd r ∧ orderOf (a * ((g : MulAut V) * a * (g : MulAut V)⁻¹)) =
      orderOf (β * (MulAut.conj (QuotientGroup.mk g : ↥L ⧸ center ↥L) * β *
        (MulAut.conj (QuotientGroup.mk g : ↥L ⧸ center ↥L))⁻¹)) * r := by
  classical
  haveI hAutFin : Finite (MulAut V) := Finite.of_injective _ DFunLike.coe_injective
  haveI hLfin : Finite ↥L := Finite.of_injective ((↑) : ↥L → MulAut V) Subtype.coe_injective
  let X := ↥L ⧸ center ↥L
  haveI hXfin : Finite X :=
    Finite.of_surjective (QuotientGroup.mk' (center ↥L)) (QuotientGroup.mk'_surjective _)
  haveI hAutXfin : Finite (MulAut X) := Finite.of_injective _ DFunLike.coe_injective
  have hperfL : Group.IsPerfect ↥L := ⟨hL.1⟩
  haveI : IsSimpleGroup X := hL.2
  have hZcenter : Subgroup.center X = ⊥ := by
    letI := hperfL
    haveI : Group.IsPerfect X :=
      Group.IsPerfect.ofSurjective (f := (QuotientGroup.mk' (center ↥L) : ↥L →* X))
        (QuotientGroup.mk'_surjective (center ↥L))
    exact TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative
      (Group.IsPerfect.not_isMulCommutative X)
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [← MonoidHom.ker_eq_bot_iff, CFSG.GroupTheory.ker_conj_eq_center]
    exact hZcenter
  set b : MulAut V := (g : MulAut V) * a * (g : MulAut V)⁻¹ with hbdef
  set w : MulAut V := a * b with hwdef
  have hwmem : w ∈ L := by
    have h1 : a * (g : MulAut V) * a⁻¹ ∈ L := hAL a haA _ g.2
    have h2 : w = (a * (g : MulAut V) * a⁻¹) * (g : MulAut V)⁻¹ := by
      rw [hwdef, hbdef, inv_eq_of_mul_eq_one_right ha]
      group
    rw [h2]
    exact L.mul_mem h1 (L.inv_mem g.2)
  let w' : ↥L := ⟨w, hwmem⟩
  set β' : MulAut X :=
    MulAut.conj (QuotientGroup.mk g) * β * (MulAut.conj (QuotientGroup.mk g))⁻¹ with hβ'def
  have hconj : MulAut.conj (QuotientGroup.mk w' : X) = β * β' := by
    rw [hβ'def]
    exact conj_mk_mul_conj_eq hAL haA ha hβ (by rw [hwdef, hbdef]) hwmem
  have horder : orderOf (QuotientGroup.mk w' : X) = orderOf (β * β') := by
    rw [← orderOf_injective (MulAut.conj : X →* MulAut X) hinj (QuotientGroup.mk w'), hconj]
  set m : ℕ := orderOf (β * β') with hmdef
  have hmpos : m ≠ 0 := (orderOf_pos _).ne'
  have hmdvd : m ∣ orderOf w' := by
    rw [← horder]
    exact orderOf_map_dvd (QuotientGroup.mk' (center ↥L) : ↥L →* X) w'
  have hxcent : w' ^ m ∈ center ↥L := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← horder]
    exact pow_orderOf_eq_one _
  set r : ℕ := orderOf (w' ^ m) with hrdef
  have hrdvd : r ∣ Nat.card (center ↥L) := by
    rw [hrdef]
    exact Subgroup.orderOf_dvd_natCard (center ↥L) hxcent
  refine ⟨r, hZ.of_dvd_nat hrdvd, ?_⟩
  have hr : r = orderOf w' / m := by
    rw [hrdef]
    exact orderOf_pow_of_dvd hmpos hmdvd
  have hworder : orderOf w' = m * r := by
    rw [hr, Nat.mul_div_cancel' hmdvd]
  rw [← hworder, ← Subgroup.orderOf_coe w']

private theorem pow_eq_self_of_mul_self_eq_one_of_odd {G : Type*} [Group G] {x : G}
    (hx : x * x = 1) {r : ℕ} (hr : Odd r) : x ^ r = x := by
  obtain ⟨k, rfl⟩ := hr
  rw [pow_add, pow_mul, pow_two, hx, one_pow, one_mul, pow_one]

private theorem conj_mk_apply {G : Type*} [Group G] {N : Subgroup G} [N.Normal] (l m : G) :
    MulAut.conj (QuotientGroup.mk l : G ⧸ N) (QuotientGroup.mk m) =
      QuotientGroup.mk (l * m * l⁻¹) := by
  rw [MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]

private theorem conj_inv_mk_apply {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (l m : G) :
    (MulAut.conj (QuotientGroup.mk l : G ⧸ N))⁻¹ (QuotientGroup.mk m) =
      QuotientGroup.mk (l⁻¹ * m * l) := by
  rw [MulAut.conj_inv_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]

private theorem map_conj_commY_eq_self {X : Type*} [Group X] (B : Subgroup (MulAut X))
    {β : MulAut X} {d : X} (hd : β d = d) :
    (commY B β).map (MulAut.conj d).toMonoidHom = commY B β := by
  have hmaps : ∀ {e : X}, β e = e →
      (commY B β).map (MulAut.conj e).toMonoidHom ≤ commY B β := by
    intro e he
    rw [commY, MonoidHom.map_closure, Subgroup.closure_le]
    rintro w ⟨g, hg, rfl⟩
    obtain ⟨y, hyβ, b, hbB, rfl⟩ := hg
    have hey : β (e * y) = e * y := by rw [map_mul, he, hyβ]
    have hdecomp : MulAut.conj e (y * (b y)⁻¹) =
        ((e * y) * (b (e * y))⁻¹) * (e * (b e)⁻¹)⁻¹ := by
      rw [MulAut.conj_apply, map_mul b e y]
      group
    change (MulAut.conj e) (y * (b y)⁻¹) ∈ commY B β
    rw [hdecomp]
    exact (commY B β).mul_mem (Subgroup.subset_closure ⟨e * y, hey, b, hbB, rfl⟩)
      ((commY B β).inv_mem (Subgroup.subset_closure ⟨e, he, b, hbB, rfl⟩))
  have hd' : β d⁻¹ = d⁻¹ := by rw [map_inv, hd]
  have hcancel : ((commY B β).map (MulAut.conj d⁻¹).toMonoidHom).map
      (MulAut.conj d).toMonoidHom = commY B β := by
    rw [Subgroup.map_map]
    have hcomp : (MulAut.conj d).toMonoidHom.comp (MulAut.conj d⁻¹).toMonoidHom =
        MonoidHom.id X := by
      ext x
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      group
    rw [hcomp, Subgroup.map_id]
  refine le_antisymm (hmaps hd) ?_
  conv_lhs => rw [← hcancel]
  exact Subgroup.map_mono (hmaps hd')

private theorem conj_mk_beta_conj_mk {L A : Subgroup (MulAut V)} {a : MulAut V}
    (hAL : ∀ u ∈ A, ∀ l ∈ L, u * l * u⁻¹ ∈ L) (haA : a ∈ A)
    {β : MulAut (↥L ⧸ center ↥L)}
    (hβ : ∀ l : ↥L, β (QuotientGroup.mk l) =
      QuotientGroup.mk (⟨a * l * a⁻¹, hAL a haA l l.2⟩ : ↥L))
    {z : MulAut V} (hzL : z ∈ L) {lam : ↥L}
    (hlam : (lam : MulAut V) * a * (lam : MulAut V)⁻¹ = a * z) :
    MulAut.conj (QuotientGroup.mk lam : ↥L ⧸ center ↥L) * β *
      (MulAut.conj (QuotientGroup.mk lam : ↥L ⧸ center ↥L))⁻¹ =
      β * MulAut.conj (QuotientGroup.mk (⟨z, hzL⟩ : ↥L) : ↥L ⧸ center ↥L) := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H m =>
    rw [MulAut.mul_apply, MulAut.mul_apply, conj_inv_mk_apply (l := lam) (m := m),
      hβ (lam⁻¹ * m * lam),
      conj_mk_apply (l := lam)
        (m := (⟨a * ((lam⁻¹ * m * lam : ↥L) : MulAut V) * a⁻¹,
          hAL a haA _ (lam⁻¹ * m * lam).2⟩ : ↥L)),
      MulAut.mul_apply, conj_mk_apply (l := (⟨z, hzL⟩ : ↥L)) (m := m), hβ]
    refine congrArg QuotientGroup.mk (Subtype.ext ?_)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hlamv : (lam : MulAut V) * a * (lam : MulAut V)⁻¹ = a * z := hlam
    calc (lam : MulAut V) * (a * ((lam⁻¹ * m * lam : ↥L) : MulAut V) * a⁻¹) *
          (lam : MulAut V)⁻¹
        = ((lam : MulAut V) * a * (lam : MulAut V)⁻¹) * (m : MulAut V) *
          ((lam : MulAut V) * a * (lam : MulAut V)⁻¹)⁻¹ := by
          rw [show ((lam⁻¹ * m * lam : ↥L) : MulAut V) =
            (lam : MulAut V)⁻¹ * (m : MulAut V) * (lam : MulAut V) from rfl]
          group
      _ = a * (((⟨z, hzL⟩ : ↥L) * m * (⟨z, hzL⟩ : ↥L)⁻¹ : ↥L) : MulAut V) * a⁻¹ := by
          rw [hlamv]
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group

private theorem commV_inf_commV_conj_lam_eq_bot [Finite V] {L A : Subgroup (MulAut V)}
    (hL : CFSG.Open.IsQuasisimple ↥L) (hZ : Odd (Nat.card (center ↥L)))
    (hAL : ∀ u ∈ A, ∀ l ∈ L, u * l * u⁻¹ ∈ L) (hA : IsQuadratic A) (hfix : fixV L = ⊥)
    {a : MulAut V} (haA : a ∈ A) (ha : a * a = 1)
    {B : Subgroup (MulAut (↥L ⧸ center ↥L))} {β : MulAut (↥L ⧸ center ↥L)}
    (hβ : ∀ l : ↥L, β (QuotientGroup.mk l) =
      QuotientGroup.mk (⟨a * l * a⁻¹, hAL a haA l l.2⟩ : ↥L))
    (hB : ∀ b ∈ B, ∃ u, ∃ hu : u ∈ A, ∀ l : ↥L, b (QuotientGroup.mk l) =
      QuotientGroup.mk (⟨u * l * u⁻¹, hAL u hu l l.2⟩ : ↥L))
    {g : ↥L} (hgen : FourGen B β (QuotientGroup.mk g))
    (hinj : Function.Injective
      (MulAut.conj : (↥L ⧸ center ↥L) →* MulAut (↥L ⧸ center ↥L)))
    {z : MulAut V} (hzL : z ∈ L)
    (hzconj : MulAut.conj (QuotientGroup.mk (⟨z, hzL⟩ : ↥L) : ↥L ⧸ center ↥L) =
      (β * (MulAut.conj (QuotientGroup.mk g) * β *
        (MulAut.conj (QuotientGroup.mk g))⁻¹)) ^
        (orderOf (β * (MulAut.conj (QuotientGroup.mk g) * β *
          (MulAut.conj (QuotientGroup.mk g))⁻¹)) / 2))
    {lam : ↥L} (hlam : (lam : MulAut V) * a * (lam : MulAut V)⁻¹ = a * z) :
    commV (zpowers a) ⊓ commV (zpowers (a * z)) = ⊥ := by
  classical
  set β' : MulAut (↥L ⧸ center ↥L) :=
    MulAut.conj (QuotientGroup.mk g) * β * (MulAut.conj (QuotientGroup.mk g))⁻¹ with hβ'def
  obtain ⟨k, hkβ, hkgen⟩ := hgen
  have hkside : MulAut.conj k * β * (MulAut.conj k)⁻¹ =
      β * (β * β') ^ (orderOf (β * β') / 2) := by
    rw [hβ'def]
    exact hkβ
  have hconjlam : MulAut.conj (QuotientGroup.mk lam) * β *
      (MulAut.conj (QuotientGroup.mk lam))⁻¹ =
      β * (β * β') ^ (orderOf (β * β') / 2) := by
    rw [hβ'def] at hzconj
    rw [← hzconj]
    exact conj_mk_beta_conj_mk hAL haA hβ hzL hlam
  have hkc : MulAut.conj k * β * (MulAut.conj k)⁻¹ =
      MulAut.conj (QuotientGroup.mk lam) * β * (MulAut.conj (QuotientGroup.mk lam))⁻¹ := by
    rw [hkside, hconjlam]
  set c : ↥L ⧸ center ↥L := k⁻¹ * (QuotientGroup.mk lam : ↥L ⧸ center ↥L) with hcdef
  have hconjc : MulAut.conj c =
      (MulAut.conj k)⁻¹ * MulAut.conj (QuotientGroup.mk lam) := by
    rw [hcdef, map_mul, map_inv]
  have hcomm : MulAut.conj c * β = β * MulAut.conj c := by
    rw [hconjc]
    have h4 : β * ((MulAut.conj k)⁻¹ * MulAut.conj (QuotientGroup.mk lam)) =
        (MulAut.conj k)⁻¹ * MulAut.conj (QuotientGroup.mk lam) * β := by
      calc β * ((MulAut.conj k)⁻¹ * MulAut.conj (QuotientGroup.mk lam))
          = (MulAut.conj k)⁻¹ * (MulAut.conj k * β * (MulAut.conj k)⁻¹) *
              MulAut.conj (QuotientGroup.mk lam) := by group
        _ = (MulAut.conj k)⁻¹ * (MulAut.conj (QuotientGroup.mk lam) * β *
              (MulAut.conj (QuotientGroup.mk lam))⁻¹) *
              MulAut.conj (QuotientGroup.mk lam) := by rw [hkc]
        _ = (MulAut.conj k)⁻¹ * MulAut.conj (QuotientGroup.mk lam) * β := by group
    exact h4.symm
  have hβc : β c = c := by
    apply hinj
    rw [mulAut_conj_apply_eq, ← hcomm]
    group
  have hmapc : (commY B β).map (MulAut.conj c).toMonoidHom = commY B β :=
    map_conj_commY_eq_self B hβc
  have hgenlam : commY B β ⊔
      (commY B β).map (MulAut.conj (QuotientGroup.mk lam)).toMonoidHom = ⊤ := by
    have hle : (commY B β).map (MulAut.conj (QuotientGroup.mk lam)).toMonoidHom =
        (commY B β).map (MulAut.conj k).toMonoidHom := by
      have hcl : (QuotientGroup.mk lam : ↥L ⧸ center ↥L) = k * c := by
        rw [hcdef]
        group
      have hconj' : MulAut.conj (QuotientGroup.mk lam : ↥L ⧸ center ↥L) =
          MulAut.conj k * MulAut.conj c := by
        rw [hcl, map_mul]
      rw [hconj']
      have hcomp : (MulAut.conj k * MulAut.conj c).toMonoidHom =
          (MulAut.conj k).toMonoidHom.comp (MulAut.conj c).toMonoidHom := by
        ext x
        simp only [MulEquiv.coe_toMonoidHom, MulAut.mul_apply, MonoidHom.comp_apply]
      rw [hcomp, ← Subgroup.map_map, hmapc]
    rw [hle]
    exact hkgen
  have hLle : L ≤ quadY L A a ⊔
      (quadY L A a).map (MulAut.conj (lam : MulAut V)).toMonoidHom :=
    le_quadY_sup_conj_of_commY hL.1 hZ hAL haA ha hβ hB hgenlam
  have hfix' : fixV (quadY L A a ⊔
      (quadY L A a).map (MulAut.conj (lam : MulAut V)).toMonoidHom) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have hvL : v ∈ fixV L := fun l hl => hv l (hLle hl)
    rwa [hfix] at hvL
  have hdisj := commV_inf_commV_conj_eq_bot (V := V) (Y := quadY L A a) (a := a)
    (h := (lam : MulAut V)) (fixes_commV_quadY hA haA) hfix'
  rwa [hlam] at hdisj

theorem commV_inf_commV_mul_pow_half_eq_bot [Finite V] {L A : Subgroup (MulAut V)}
    (hL : CFSG.Open.IsQuasisimple ↥L) (hZ : Odd (Nat.card (center ↥L)))
    (hAL : ∀ u ∈ A, ∀ l ∈ L, u * l * u⁻¹ ∈ L) (hA : IsQuadratic A) (hfix : fixV L = ⊥)
    {a : MulAut V} (haA : a ∈ A) (ha : a * a = 1)
    {B : Subgroup (MulAut (↥L ⧸ center ↥L))} {β : MulAut (↥L ⧸ center ↥L)}
    (hβ : ∀ l : ↥L, β (QuotientGroup.mk l) =
      QuotientGroup.mk (⟨a * l * a⁻¹, hAL a haA l l.2⟩ : ↥L))
    (hB : ∀ b ∈ B, ∃ u, ∃ hu : u ∈ A, ∀ l : ↥L, b (QuotientGroup.mk l) =
      QuotientGroup.mk (⟨u * l * u⁻¹, hAL u hu l l.2⟩ : ↥L))
    {g : ↥L}
    (hm : Even (orderOf (β * (MulAut.conj (QuotientGroup.mk g : ↥L ⧸ center ↥L) * β *
      (MulAut.conj (QuotientGroup.mk g : ↥L ⧸ center ↥L))⁻¹))))
    (hgen : FourGen B β (QuotientGroup.mk g)) :
    commV (zpowers a) ⊓ commV (zpowers (a * (a * ((g : MulAut V) * a * (g : MulAut V)⁻¹)) ^
      (orderOf (a * ((g : MulAut V) * a * (g : MulAut V)⁻¹)) / 2))) = ⊥ := by
  classical
  haveI hAutFin : Finite (MulAut V) := Finite.of_injective _ DFunLike.coe_injective
  haveI hLfin : Finite ↥L := Finite.of_injective ((↑) : ↥L → MulAut V) Subtype.coe_injective
  let X := ↥L ⧸ center ↥L
  haveI hXfin : Finite X :=
    Finite.of_surjective (QuotientGroup.mk' (center ↥L)) (QuotientGroup.mk'_surjective _)
  have hperfL : Group.IsPerfect ↥L := ⟨hL.1⟩
  haveI : IsSimpleGroup X := hL.2
  have hZcenter : Subgroup.center X = ⊥ := by
    letI := hperfL
    haveI : Group.IsPerfect X :=
      Group.IsPerfect.ofSurjective (f := (QuotientGroup.mk' (center ↥L) : ↥L →* X))
        (QuotientGroup.mk'_surjective (center ↥L))
    exact TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative
      (Group.IsPerfect.not_isMulCommutative X)
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [← MonoidHom.ker_eq_bot_iff, CFSG.GroupTheory.ker_conj_eq_center]
    exact hZcenter
  set b : MulAut V := (g : MulAut V) * a * (g : MulAut V)⁻¹ with hbdef
  set w : MulAut V := a * b with hwdef
  have hwmem : w ∈ L := by
    have h1 : a * (g : MulAut V) * a⁻¹ ∈ L := hAL a haA _ g.2
    have h2 : w = (a * (g : MulAut V) * a⁻¹) * (g : MulAut V)⁻¹ := by
      rw [hwdef, hbdef, inv_eq_of_mul_eq_one_right ha]
      group
    rw [h2]
    exact L.mul_mem h1 (L.inv_mem g.2)
  let w' : ↥L := ⟨w, hwmem⟩
  set β' : MulAut X :=
    MulAut.conj (QuotientGroup.mk g) * β * (MulAut.conj (QuotientGroup.mk g))⁻¹ with hβ'def
  have hconj : MulAut.conj (QuotientGroup.mk w' : X) = β * β' := by
    rw [hβ'def]
    exact conj_mk_mul_conj_eq hAL haA ha hβ (by rw [hwdef, hbdef]) hwmem
  have horder : orderOf (QuotientGroup.mk w' : X) = orderOf (β * β') := by
    rw [← orderOf_injective (MulAut.conj : X →* MulAut X) hinj (QuotientGroup.mk w'), hconj]
  obtain ⟨r, hr_odd, hro⟩ := exists_odd_orderOf_mul_conj_eq hL hZ hAL haA ha hβ g
  set m : ℕ := orderOf (β * β') with hmdef
  set o : ℕ := orderOf (a * b) with hodef
  have ho_eq : o = m * r := by
    rw [hodef, hmdef, hbdef]
    exact hro
  have hm' : Even m := by
    rw [hmdef]
    exact hm
  obtain ⟨t, ht⟩ := hm'
  have hmeq : m = 2 * (m / 2) := by omega
  have ho2 : o / 2 = m / 2 * r := by
    have h2 : m * r = 2 * (m / 2 * r) := by
      nth_rewrite 1 [hmeq]
      ring
    rw [ho_eq, h2, Nat.mul_div_right _ (by norm_num : 0 < 2)]
  have ht2 : (β * β') ^ (m / 2) * (β * β') ^ (m / 2) = 1 := by
    rw [← pow_add]
    have hhalf : m / 2 + m / 2 = m := by omega
    rw [hhalf, hmdef, pow_orderOf_eq_one]
  have hb2 : b * b = 1 := by
    rw [hbdef]
    calc ((g : MulAut V) * a * (g : MulAut V)⁻¹) * ((g : MulAut V) * a * (g : MulAut V)⁻¹)
        = (g : MulAut V) * (a * a) * (g : MulAut V)⁻¹ := by group
      _ = 1 := by rw [ha]; simp
  have heven : Even (orderOf (a * b)) := by
    rw [← hodef, ho_eq]
    exact ⟨t * r, by rw [ht]; ring⟩
  set z : MulAut V := (a * b) ^ (o / 2) with hzdef
  have hzL : z ∈ L := by
    rw [hzdef, ← hwdef]
    exact L.pow_mem hwmem (o / 2)
  have hzconj : MulAut.conj (QuotientGroup.mk (⟨z, hzL⟩ : ↥L) : X) =
      (β * β') ^ (orderOf (β * β') / 2) := by
    have hz' : (⟨z, hzL⟩ : ↥L) = w' ^ (o / 2) := by
      apply Subtype.ext
      change z = w ^ (o / 2)
      rw [hzdef, hwdef]
    have hπz : (QuotientGroup.mk (⟨z, hzL⟩ : ↥L) : X) =
        (QuotientGroup.mk w' : X) ^ (o / 2) := by
      rw [hz', QuotientGroup.mk_pow]
    calc MulAut.conj (QuotientGroup.mk (⟨z, hzL⟩ : ↥L) : X)
        = MulAut.conj ((QuotientGroup.mk w' : X) ^ (o / 2)) := by rw [hπz]
      _ = (MulAut.conj (QuotientGroup.mk w' : X)) ^ (o / 2) := map_pow _ _ _
      _ = (β * β') ^ (o / 2) := by rw [hconj]
      _ = (β * β') ^ (m / 2 * r) := by rw [ho2]
      _ = ((β * β') ^ (m / 2)) ^ r := by rw [pow_mul]
      _ = (β * β') ^ (m / 2) := pow_eq_self_of_mul_self_eq_one_of_odd ht2 hr_odd
      _ = (β * β') ^ (orderOf (β * β') / 2) := by rw [hmdef]
  obtain ⟨j, hj | hj⟩ :=
    exists_conj_mul_pow_half (G := MulAut V) (a := a) (b := b)
      (by rw [pow_two]; exact ha) (by rw [pow_two]; exact hb2) heven
  · have hzpow : a * z = (a * b) ^ j * a * ((a * b) ^ j)⁻¹ := by
      rw [hzdef, hodef]
      exact hj
    have hmema : (a * b) ^ j ∈ L := by
      rw [← hwdef]
      exact L.zpow_mem hwmem j
    refine commV_inf_commV_conj_lam_eq_bot hL hZ hAL hA hfix haA ha hβ hB hgen hinj hzL hzconj
      (lam := ⟨(a * b) ^ j, hmema⟩) ?_
    simpa using hzpow.symm
  · have hzpow : a * z = (a * b) ^ j * b * ((a * b) ^ j)⁻¹ := by
      rw [hzdef, hodef]
      exact hj
    have hmema : (a * b) ^ j * (g : MulAut V) ∈ L :=
      L.mul_mem (by rw [← hwdef]; exact L.zpow_mem hwmem j) g.2
    refine commV_inf_commV_conj_lam_eq_bot hL hZ hAL hA hfix haA ha hβ hB hgen hinj hzL hzconj
      (lam := ⟨(a * b) ^ j * (g : MulAut V), hmema⟩) ?_
    change ((a * b) ^ j * (g : MulAut V)) * a * ((a * b) ^ j * (g : MulAut V))⁻¹ = a * z
    rw [hzpow, hbdef]
    group


end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
