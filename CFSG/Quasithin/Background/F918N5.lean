module

public import CFSG.Quasithin.Background.F918N0
public import CFSG.Quasithin.Background.F918E2
public import CFSG.Quasithin.Background.D2Conj
public import CFSG.Quasithin.Background.F7Basic
public import CFSG.Quasithin.Background.F918M7
public import CFSG.Quasithin.Background.F918P1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped commutatorElement

section General

variable {X : Type} [CommGroup X]

private theorem n5_map_one (U : Subgroup X) : U.map (1 : MulAut X).toMonoidHom = U := by
  ext x
  simp

private theorem n5_inv_fix {g : MulAut X} {v : X} (h : g v = v) : g⁻¹ v = v := by
  calc g⁻¹ v = g⁻¹ (g v) := by rw [h]
    _ = v := MulAut.inv_apply_self _ g v

private theorem n5_le_stab {G : Subgroup (MulAut X)} {U : Subgroup X}
    (hinv : ∀ g ∈ G, ∀ u ∈ U, g u ∈ U) : G ≤ stabSub U := by
  intro g hg u
  refine ⟨fun hu => ?_, hinv g hg u⟩
  have := hinv g⁻¹ (G.inv_mem hg) (g u) hu
  rwa [MulAut.inv_apply_self] at this

private theorem n5_mem_conj {t x : MulAut X} {Y : Subgroup (MulAut X)} :
    x ∈ conjAutSub t Y ↔ t⁻¹ * x * t ∈ Y := mem_conjBy_iff

private theorem n5_conj_mem_of_mem {t y : MulAut X} {Y : Subgroup (MulAut X)} (hy : y ∈ Y) :
    t * y * t⁻¹ ∈ conjAutSub t Y := mem_conjBy_of_mem hy

private theorem n5_map_inv_of_map_eq {x : MulAut X} {J J' : Subgroup X}
    (h : J.map x.toMonoidHom = J') : J'.map x⁻¹.toMonoidHom = J := by
  rw [← h, ← map_mul_aut', inv_mul_cancel, n5_map_one]

private def n5Perm (U U' : Subgroup X) : Subgroup (MulAut X) where
  carrier := {x | (U.map x.toMonoidHom = U ∧ U'.map x.toMonoidHom = U') ∨
    (U.map x.toMonoidHom = U' ∧ U'.map x.toMonoidHom = U)}
  one_mem' := by
    left
    exact ⟨n5_map_one U, n5_map_one U'⟩
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq, map_mul_aut'] at hx hy ⊢
    rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hx with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      simp only [h1, h2, h3, h4, and_self, true_or, or_true]
  inv_mem' := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨n5_map_inv_of_map_eq h1, n5_map_inv_of_map_eq h2⟩
    · exact Or.inr ⟨n5_map_inv_of_map_eq h2, n5_map_inv_of_map_eq h1⟩

private theorem mem_n5Perm {U U' : Subgroup X} {x : MulAut X} :
    x ∈ n5Perm U U' ↔ (U.map x.toMonoidHom = U ∧ U'.map x.toMonoidHom = U') ∨
      (U.map x.toMonoidHom = U' ∧ U'.map x.toMonoidHom = U) := Iff.rfl

private def n5Fix (g : MulAut X) (U : Subgroup X) : Subgroup X where
  carrier := {u | u ∈ U ∧ g u = u}
  one_mem' := ⟨U.one_mem, map_one g⟩
  mul_mem' := fun ha hb => ⟨U.mul_mem ha.1 hb.1, by rw [map_mul, ha.2, hb.2]⟩
  inv_mem' := fun ha => ⟨U.inv_mem ha.1, by rw [map_inv, ha.2]⟩

private theorem n5_iso_map {M : Subgroup (MulAut X)} {g : MulAut X}
    (hc : ∀ x ∈ M, g * x = x * g) (U : Subgroup X) : XMod.Iso ↥M U (U.map g.toMonoidHom) := by
  refine ⟨U.equivMapOfInjective g.toMonoidHom (fun x y hxy => g.injective hxy),
    fun m l l' hl => ?_⟩
  show m.1 (g l) = g l'
  rw [← hl]
  exact congrArg (fun φ : MulAut X => φ (l : X)) (hc m.1 m.2).symm

private theorem n5_orbSup_conj (g : MulAut X) (A : Subgroup (MulAut X)) (U : Subgroup X) :
    orbSup (conjBy g A) (U.map g.toMonoidHom) = (orbSup A U).map g.toMonoidHom := by
  apply le_antisymm
  · refine orbSup_le fun b hb => ?_
    rw [mem_conjBy_iff] at hb
    have e : (U.map g.toMonoidHom).map b.toMonoidHom =
        (U.map (g⁻¹ * b * g).toMonoidHom).map g.toMonoidHom := by
      rw [← map_mul_aut' b g U, ← map_mul_aut' g (g⁻¹ * b * g) U,
        show g * (g⁻¹ * b * g) = b * g by group]
    rw [e]
    exact Subgroup.map_mono (map_le_orbSup hb)
  · rw [Subgroup.map_le_iff_le_comap]
    refine orbSup_le fun a ha => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have e : (U.map a.toMonoidHom).map g.toMonoidHom =
        (U.map g.toMonoidHom).map (g * a * g⁻¹).toMonoidHom := by
      rw [← map_mul_aut' g a U, ← map_mul_aut' (g * a * g⁻¹) g U,
        show g * a * g⁻¹ * g = g * a by group]
    rw [e]
    exact map_le_orbSup (mem_conjBy_of_mem ha)

private theorem n5_rk_two [Finite X] {A : Subgroup (MulAut X)} {U₁ U₂ : Subgroup X}
    (h₁ : A ≤ stabSub U₁) (h₂ : A ≤ stabSub U₂) (hd : Disjoint U₁ U₂) :
    (rk U₁ - rk ↥(U₁ ⊓ fixV A)) + (rk U₂ - rk ↥(U₂ ⊓ fixV A)) ≤ rkIdx (fixV A) := by
  have hinf : (U₁ ⊔ U₂) ⊓ fixV A ≤ (U₁ ⊓ fixV A) ⊔ (U₂ ⊓ fixV A) := by
    rintro x ⟨hx, hxF⟩
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Subgroup.mem_sup.mp hx
    have hfix : ∀ a ∈ A, a u₁ = u₁ ∧ a u₂ = u₂ := by
      intro a ha
      have e1 : a u₁ * a u₂ = u₁ * u₂ := by rw [← map_mul]; exact hxF a ha
      have hm : a u₁ / u₁ ∈ U₁ ⊓ U₂ := by
        refine ⟨U₁.div_mem ((h₁ ha u₁).mpr hu₁) hu₁, ?_⟩
        have : a u₁ / u₁ = u₂ / a u₂ := by
          rw [div_eq_div_iff_mul_eq_mul, e1]
          exact mul_comm _ _
        rw [this]
        exact U₂.div_mem hu₂ ((h₂ ha u₂).mpr hu₂)
      rw [disjoint_iff.mp hd, Subgroup.mem_bot, div_eq_one] at hm
      refine ⟨hm, ?_⟩
      rw [hm] at e1
      exact mul_left_cancel e1
    exact Subgroup.mul_mem_sup ⟨hu₁, fun a ha => (hfix a ha).1⟩ ⟨hu₂, fun a ha => (hfix a ha).2⟩
  have e1 := rk_sup_add_rk_inf U₁ U₂
  rw [disjoint_iff.mp hd, rk_bot] at e1
  have e2 := rk_sup_add_rk_inf (U₁ ⊓ fixV A) (U₂ ⊓ fixV A)
  have e3 := rk_mono hinf
  have e4 := rk_sup_add_rk_inf (U₁ ⊔ U₂) (fixV A)
  have e5 : rk ↥((U₁ ⊔ U₂) ⊔ fixV A) ≤ rk X :=
    calc rk ↥((U₁ ⊔ U₂) ⊔ fixV A) ≤ rk ↥(⊤ : Subgroup X) := rk_mono le_top
      _ = rk X := rk_top
  have e6 := rk_add_rkIdx (fixV A)
  have e7 : rk ↥(U₁ ⊓ fixV A) ≤ rk U₁ := rk_mono inf_le_left
  have e8 : rk ↥(U₂ ⊓ fixV A) ≤ rk U₂ := rk_mono inf_le_left
  omega

end General

section Groups

variable {Ω : Type*} [Group Ω]

private theorem n5_commute_of_central {K L : Subgroup Ω} (hLK : L ≤ K) (hperf : ⁅L, L⁆ = L)
    {m : Ω} (hmK : ∀ l ∈ L, ⁅m, l⁆ ∈ K) (hZ : ∀ l ∈ L, ∀ k ∈ K, ⁅m, l⁆ * k = k * ⁅m, l⁆) :
    ∀ l ∈ L, m * l = l * m := by
  have hle : ⁅L, L⁆ ≤ Subgroup.centralizer ({m} : Set Ω) := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have ex : m * x * m⁻¹ = ⁅m, x⁆ * x := by simp only [commutatorElement_def]; group
    have ey : m * y * m⁻¹ = ⁅m, y⁆ * y := by simp only [commutatorElement_def]; group
    have c1 : Commute ⁅m, x⁆ x := hZ x hx x (hLK hx)
    have c2 : Commute ⁅m, x⁆ y := hZ x hx y (hLK hy)
    have c3 : Commute ⁅m, x⁆ ⁅m, y⁆ := hZ x hx _ (hmK y hy)
    have c4 : Commute ⁅m, y⁆ x := hZ y hy x (hLK hx)
    have c5 : Commute ⁅m, y⁆ y := hZ y hy y (hLK hy)
    have hY : Commute ⁅m, x⁆ (x * ⁅m, y⁆ * y * x⁻¹) :=
      ((c1.mul_right c3).mul_right c2).mul_right c1.inv_right
    have hQ : Commute ⁅m, y⁆ (x * y * x⁻¹ * y⁻¹) :=
      ((c4.mul_right c5).mul_right c4.inv_right).mul_right c5.inv_right
    have key : m * ⁅x, y⁆ * m⁻¹ = ⁅x, y⁆ := by
      have e : m * ⁅x, y⁆ * m⁻¹ = ⁅m * x * m⁻¹, m * y * m⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [e, ex, ey]
      set a := ⁅m, x⁆
      set b := ⁅m, y⁆
      rw [commutatorElement_def, commutatorElement_def]
      calc a * x * (b * y) * (a * x)⁻¹ * (b * y)⁻¹
          = a * (x * b * y * x⁻¹) * a⁻¹ * (y⁻¹ * b⁻¹) := by group
        _ = (x * b * y * x⁻¹) * a * a⁻¹ * (y⁻¹ * b⁻¹) := by rw [hY.eq]
        _ = x * b * (y * x⁻¹ * y⁻¹ * b⁻¹) := by group
        _ = b * x * (y * x⁻¹ * y⁻¹ * b⁻¹) := by rw [c4.eq]
        _ = b * (x * y * x⁻¹ * y⁻¹) * b⁻¹ := by group
        _ = (x * y * x⁻¹ * y⁻¹) * b * b⁻¹ := by rw [hQ.eq]
        _ = x * y * x⁻¹ * y⁻¹ := by group
    exact (mul_inv_eq_iff_eq_mul.mp key).symm
  intro l hl
  rw [← hperf] at hl
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hl)).symm

private theorem n5_central_or_eq {K H : Subgroup Ω} (hK : CFSG.Open.IsQuasisimple ↥K) (hHK : H ≤ K)
    (hn : ∀ k ∈ K, ∀ x ∈ H, k * x * k⁻¹ ∈ H) :
    (∀ x ∈ H, ∀ k ∈ K, x * k = k * x) ∨ K ≤ H := by
  have hN : (H.subgroupOf K).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using hn g g.2 x hx⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hK (H.subgroupOf K) with
    hc | ht
  · left
    intro x hx k hk
    have hmem : (⟨x, hHK hx⟩ : ↥K) ∈ H.subgroupOf K := hx
    have := Subgroup.mem_center_iff.mp (hc hmem) ⟨k, hk⟩
    exact (congrArg Subtype.val this).symm
  · right
    intro k hk
    have : (⟨k, hk⟩ : ↥K) ∈ H.subgroupOf K := ht ▸ Subgroup.mem_top _
    exact this

end Groups

section Z35Facts

variable {X : Type} [CommGroup X] [Finite X] {Mb Tb Lb : Subgroup (MulAut X)} {Vb : Subgroup X}

private theorem n5_le_normalizer (h : Z35 Mb Tb Lb Vb) :
    Tb ≤ Subgroup.normalizer (Mb : Set (MulAut X)) := by
  rw [h.Mp_eq]
  exact le_normalizer_conjClosure Lb Tb

private theorem n5_conj_mem (h : Z35 Mb Tb Lb Vb) {t : MulAut X} (ht : t ∈ Tb) {x : MulAut X}
    (hx : x ∈ Mb) : t * x * t⁻¹ ∈ Mb :=
  (Subgroup.mem_normalizer_iff.mp (n5_le_normalizer h ht) x).mp hx

private theorem n5_conj_mem' (h : Z35 Mb Tb Lb Vb) {t : MulAut X} (ht : t ∈ Tb) {x : MulAut X}
    (hx : x ∈ Mb) : t⁻¹ * x * t ∈ Mb :=
  (Subgroup.mem_normalizer_iff''.mp (n5_le_normalizer h ht) x).mp hx

private theorem n5_V_inv (h : Z35 Mb Tb Lb Vb) {m : MulAut X} (hm : m ∈ Mb) {v : X} (hv : v ∈ Vb) :
    m v ∈ Vb :=
  h.irr.1 ⟨m, hm⟩ v hv

private theorem n5_V_ne_bot (h : Z35 Mb Tb Lb Vb) : Vb ≠ ⊥ := h.irr.2.1.ne'

private theorem n5_map_ne_bot (h : Z35 Mb Tb Lb Vb) (t : MulAut X) : Vb.map t.toMonoidHom ≠ ⊥ :=
  fun he => n5_V_ne_bot h ((Subgroup.map_eq_bot_iff_of_injective _ t.injective).mp he)

private theorem n5_map_inv (h : Z35 Mb Tb Lb Vb) {t : MulAut X} (ht : t ∈ Tb) {m : MulAut X}
    (hm : m ∈ Mb) {w : X} (hw : w ∈ Vb.map t.toMonoidHom) : m w ∈ Vb.map t.toMonoidHom := by
  obtain ⟨v, hv, rfl⟩ := hw
  refine ⟨(t⁻¹ * m * t) v, n5_V_inv h (n5_conj_mem' h ht hm) hv, ?_⟩
  simp [MulAut.mul_apply]

private theorem n5_Mb_le_stab (h : Z35 Mb Tb Lb Vb) : Mb ≤ stabSub Vb :=
  n5_le_stab fun _ hm _ hv => n5_V_inv h hm hv

private theorem n5_Lb_le (h : Z35 Mb Tb Lb Vb) : Lb ≤ Mb := by
  rw [h.Mp_eq]
  exact le_conjClosure Lb Tb

private theorem n5_conj_le (h : Z35 Mb Tb Lb Vb) {s : MulAut X} (hs : s ∈ Tb) : conjAutSub s Lb ≤ Mb := by
  intro x hx
  have hx' := n5_mem_conj.mp hx
  have e : x = s * (s⁻¹ * x * s) * s⁻¹ := by group
  rw [e, h.Mp_eq]
  exact mem_conjClosure hs hx'

private theorem n5_orb_inv (h : Z35 Mb Tb Lb Vb) {A : Subgroup (MulAut X)} (hA : A ≤ Tb) {t : MulAut X}
    (ht : t ∈ Tb) {m : MulAut X} (hm : m ∈ Mb) {w : X} (hw : w ∈ orbSup A (Vb.map t.toMonoidHom)) :
    m w ∈ orbSup A (Vb.map t.toMonoidHom) := by
  have key : orbSup A (Vb.map t.toMonoidHom) ≤
      (orbSup A (Vb.map t.toMonoidHom)).comap m.toMonoidHom := by
    refine orbSup_le fun a ha => ?_
    intro x hx
    have hat : a * t ∈ Tb := Tb.mul_mem (hA ha) ht
    rw [← map_mul_aut'] at hx
    have := n5_map_inv h hat hm hx
    rw [map_mul_aut'] at this
    exact map_le_orbSup ha this
  exact key hw

private theorem n5_conj_rel (h : Z35 Mb Tb Lb Vb) {r s : MulAut X} (hr : r ∈ Tb) (hs : s ∈ Tb) :
    conjAutSub r Lb = conjAutSub s Lb ∨
      ∀ x ∈ conjAutSub r Lb, ∀ y ∈ conjAutSub s Lb, x * y = y * x := by
  rcases h.comm_conj (r⁻¹ * s) (Tb.mul_mem (Tb.inv_mem hr) hs) with he | hc
  · left
    ext x
    rw [n5_mem_conj, n5_mem_conj]
    constructor
    · intro hx
      rw [← he, n5_mem_conj] at hx
      have e : (r⁻¹ * s)⁻¹ * (r⁻¹ * x * r) * (r⁻¹ * s) = s⁻¹ * x * s := by group
      rwa [e] at hx
    · intro hx
      have : (r⁻¹ * s) * (s⁻¹ * x * s) * (r⁻¹ * s)⁻¹ ∈ conjAutSub (r⁻¹ * s) Lb :=
        n5_conj_mem_of_mem hx
      rw [he] at this
      have e : (r⁻¹ * s) * (s⁻¹ * x * s) * (r⁻¹ * s)⁻¹ = r⁻¹ * x * r := by group
      rwa [e] at this
  · right
    intro x hx y hy
    have hx' : r⁻¹ * x * r ∈ Lb := n5_mem_conj.mp hx
    have hy' : r⁻¹ * y * r ∈ conjAutSub (r⁻¹ * s) Lb := by
      rw [n5_mem_conj]
      have e : (r⁻¹ * s)⁻¹ * (r⁻¹ * y * r) * (r⁻¹ * s) = s⁻¹ * y * s := by group
      rw [e]
      exact n5_mem_conj.mp hy
    have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc hx'
    have hcomm := Subgroup.mem_centralizer_iff.mp hcen _ hy'
    calc x * y = r * ((r⁻¹ * x * r) * (r⁻¹ * y * r)) * r⁻¹ := by group
      _ = r * ((r⁻¹ * y * r) * (r⁻¹ * x * r)) * r⁻¹ := by rw [hcomm]
      _ = y * x := by group

private theorem n5_le_normalizer_conj (h : Z35 Mb Tb Lb Vb) {s : MulAut X} (hs : s ∈ Tb) :
    Mb ≤ Subgroup.normalizer (conjAutSub s Lb : Set (MulAut X)) := by
  rw [h.Mp_eq]
  refine conjClosure_le fun r hr y hy => ?_
  have hx : r * y * r⁻¹ ∈ conjAutSub r Lb := n5_conj_mem_of_mem hy
  rcases n5_conj_rel h hr hs with he | hc
  · rw [he] at hx
    exact Subgroup.le_normalizer hx
  · exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun z hz => (hc _ hx z hz).symm)

private theorem n5_quasi_conj (h : Z35 Mb Tb Lb Vb) (s : MulAut X) :
    CFSG.Open.IsQuasisimple ↥(conjAutSub s Lb) := by
  obtain ⟨hp, hs⟩ : CFSG.Open.IsQuasisimple ↥Lb := ⟨Group.isPerfect_def.mp h.quasi.1, h.quasi.2.1⟩
  let e : ↥Lb ≃* ↥(conjAutSub s Lb) :=
    Lb.equivMapOfInjective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective
  have hc : (Subgroup.center ↥Lb).map (e : ↥Lb →* ↥(conjAutSub s Lb)) =
      Subgroup.center ↥(conjAutSub s Lb) := Subgroup.map_center_eq e
  let e' : ↥Lb ⧸ Subgroup.center ↥Lb ≃* ↥(conjAutSub s Lb) ⧸ Subgroup.center ↥(conjAutSub s Lb) :=
    QuotientGroup.congr _ _ e hc
  refine ⟨?_, e'.symm.isSimpleGroup⟩
  rw [_root_.commutator_def] at hp ⊢
  rw [← Subgroup.map_top_of_surjective (e : ↥Lb →* ↥(conjAutSub s Lb)) e.surjective,
    ← Subgroup.map_commutator, hp]

private theorem n5_perf_conj (h : Z35 Mb Tb Lb Vb) (s : MulAut X) :
    ⁅conjAutSub s Lb, conjAutSub s Lb⁆ = conjAutSub s Lb := by
  have : Group.IsPerfect ↥(conjAutSub s Lb) := Group.isPerfect_def.mpr (n5_quasi_conj h s).1
  exact Subgroup.commutator_eq_self

private theorem n5_nontriv (h : Z35 Mb Tb Lb Vb) {s t : MulAut X} (hs : s ∈ Tb) (ht : t ∈ Tb) :
    ∃ l ∈ conjAutSub s Lb, ∃ w ∈ Vb.map t.toMonoidHom, l w ≠ w := by
  obtain ⟨l, hl, v, hv, hne⟩ := h.nontriv (t⁻¹ * s) (Tb.mul_mem (Tb.inv_mem ht) hs)
  refine ⟨t * l * t⁻¹, ?_, t v, ⟨v, hv, rfl⟩, ?_⟩
  · rw [n5_mem_conj]
    have e : s⁻¹ * (t * l * t⁻¹) * s = (t⁻¹ * s)⁻¹ * l * (t⁻¹ * s) := by group
    rw [e]
    exact n5_mem_conj.mp hl
  · intro heq
    apply hne
    have h1 : t (l v) = t v := by simpa [MulAut.mul_apply] using heq
    exact t.injective h1

private theorem n5_rank (h : Z35 Mb Tb Lb Vb) : 2 < rk ↥Vb := by
  by_contra hle
  have hle' : rk ↥Vb ≤ 2 := not_lt.mp hle
  have hcard : Nat.card ↥Vb ≤ 4 := by
    rw [card_eq_two_pow h.exp Vb]
    calc 2 ^ rk ↥Vb ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hle'
      _ = 4 := by norm_num
  have hLS : Lb ≤ stabSub Vb := (n5_Lb_le h).trans (n5_Mb_le_stab h)
  let ρ : ↥Lb →* MulAut ↥Vb := (resHom Vb).comp (Subgroup.inclusion hLS)
  have : Group.IsPerfect ↥Lb := h.quasi.1
  have : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
  have : Group.IsSolvable (Equiv.Perm ↥Vb) := Equiv.Perm.isSolvable hcard
  have : Group.IsSolvable (MulAut ↥Vb) :=
    Group.isSolvable_of_isSolvable_injective (f := MulAut.toPerm _) fun a b hab =>
      MulEquiv.ext fun u => congrArg (fun e : Equiv.Perm _ => e u) hab
  have hsub : Subsingleton ρ.range := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isSolvable ρ.range inferInstance
  obtain ⟨l, hl, v, hv, hne⟩ := h.nontriv 1 Tb.one_mem
  have hl' : l ∈ Lb := by
    have := n5_mem_conj.mp hl
    simpa using this
  apply hne
  have h1 : ρ ⟨l, hl'⟩ = 1 := by
    have : (⟨ρ ⟨l, hl'⟩, ⟨l, hl'⟩, rfl⟩ : ρ.range) = 1 := Subsingleton.elim _ _
    exact congrArg Subtype.val this
  have h2 := congrArg (fun φ : MulAut ↥Vb => ((φ ⟨v, hv⟩ : ↥Vb) : X)) h1
  exact h2

theorem z35_conj_irr (h : Z35 Mb Tb Lb Vb) {t : MulAut X} (ht : t ∈ Tb) :
    XMod.IsIrr ↥Mb (Vb.map t.toMonoidHom) := by
  refine ⟨fun m w hw => n5_map_inv h ht m.2 hw, (n5_map_ne_bot h t).bot_lt, fun J hJ _ hJV => ?_⟩
  have hJ' : XMod.IsInv ↥Mb (J.map t⁻¹.toMonoidHom) := by
    rintro m _ ⟨w, hw, rfl⟩
    refine ⟨(t * m.1 * t⁻¹) w, hJ ⟨t * m.1 * t⁻¹, n5_conj_mem h ht m.2⟩ w hw, ?_⟩
    show t⁻¹ ((t * m.1 * t⁻¹) w) = m.1 (t⁻¹ w)
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  have hJ'V : J.map t⁻¹.toMonoidHom ≤ Vb := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨v, hv, rfl⟩ := hJV hw
    simpa using hv
  have hJJ : J = (J.map t⁻¹.toMonoidHom).map t.toMonoidHom := by
    rw [← map_mul_aut', mul_inv_cancel, n5_map_one]
  rcases h.irr.2.2 _ hJ' bot_le hJ'V with h1 | h1
  · left
    rw [hJJ, h1, Subgroup.map_bot]
  · right
    rw [hJJ, h1]

theorem z35_independent_sum (h : Z35 Mb Tb Lb Vb) {A : Subgroup (MulAut X)} (hAT : A ≤ Tb)
    {s t : MulAut X} (hs : s ∈ Tb) (ht : t ∈ Tb)
    (hnot : ¬ Vb.map t.toMonoidHom ≤ orbSup A (Vb.map s.toMonoidHom)) :
    Disjoint (orbSup A (Vb.map s.toMonoidHom)) (orbSup A (Vb.map t.toMonoidHom)) := by
  set Cj : Set (Subgroup X) := {S | ∃ t ∈ Tb, S = Vb.map t.toMonoidHom}
  have hind : iSupIndep (fun i : ↥Cj => (i : Subgroup X)) := (sSupIndep_iff Cj).mp h.indep
  set P : Set ↥Cj := {i | ∃ a ∈ A, (i : Subgroup X) = (Vb.map s.toMonoidHom).map a.toMonoidHom}
  set Q : Set ↥Cj := {i | ∃ a ∈ A, (i : Subgroup X) = (Vb.map t.toMonoidHom).map a.toMonoidHom}
  have hPQ : Disjoint P Q := by
    rw [Set.disjoint_left]
    rintro i ⟨a, ha, hia⟩ ⟨b, hb, hib⟩
    apply hnot
    have e : Vb.map t.toMonoidHom = (Vb.map s.toMonoidHom).map (b⁻¹ * a).toMonoidHom := by
      rw [map_mul_aut' b⁻¹ a (Vb.map s.toMonoidHom), ← hia, hib,
        ← map_mul_aut' b⁻¹ b (Vb.map t.toMonoidHom), inv_mul_cancel, n5_map_one]
    rw [e]
    exact map_le_orbSup (A.mul_mem (A.inv_mem hb) ha)
  have hd := hind.disjoint_biSup_biSup' hPQ (Set.toFinite P)
  refine hd.mono ?_ ?_
  · refine orbSup_le fun a ha => ?_
    exact le_iSup₂_of_le (⟨(Vb.map s.toMonoidHom).map a.toMonoidHom, a * s, Tb.mul_mem (hAT ha) hs,
      (map_mul_aut' a s Vb).symm⟩ : ↥Cj) ⟨a, ha, rfl⟩ le_rfl
  · refine orbSup_le fun a ha => ?_
    exact le_iSup₂_of_le (⟨(Vb.map t.toMonoidHom).map a.toMonoidHom, a * t, Tb.mul_mem (hAT ha) ht,
      (map_mul_aut' a t Vb).symm⟩ : ↥Cj) ⟨a, ha, rfl⟩ le_rfl

end Z35Facts

section Faithful

variable {X : Type} [CommGroup X] [Finite X] {Mb Tb Lb : Subgroup (MulAut X)} {Vb : Subgroup X}

private theorem n5_triv_V (h : Z35 Mb Tb Lb Vb) {b : MulAut X} (hb : b ∈ Tb) (hb2 : b ^ 2 = 1)
    (hc : ∀ x ∈ Mb, b * x = x * b) : ∀ v ∈ Vb, b v = v := by
  have hstab : Vb.map b.toMonoidHom = Vb := by
    have h1 := h.homog 1 Tb.one_mem b hb
    rw [n5_map_one] at h1
    exact (h1 (n5_iso_map hc Vb)).symm
  have hbV : ∀ v ∈ Vb, b v ∈ Vb := fun v hv => hstab ▸ ⟨v, hv, rfl⟩
  have hbb : ∀ v, b (b v) = v := by
    intro v
    have := congrArg (fun φ : MulAut X => φ v) hb2
    simpa [pow_two] using this
  have hinv2 : ∀ x : X, x⁻¹ = x := fun x =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact h.exp x)
  have hJinv : XMod.IsInv ↥Mb (n5Fix b Vb) := by
    intro m v hv
    refine ⟨n5_V_inv h m.2 hv.1, ?_⟩
    show b (m.1 v) = m.1 v
    have e : b (m.1 v) = m.1 (b v) := congrArg (fun φ : MulAut X => φ v) (hc m.1 m.2)
    rw [e, hv.2]
  rcases h.irr.2.2 (n5Fix b Vb) hJinv bot_le (fun x hx => hx.1) with hJ | hJ
  · exfalso
    apply n5_V_ne_bot h
    rw [eq_bot_iff]
    intro v hv
    have hy : b v * v⁻¹ ∈ n5Fix b Vb := by
      refine ⟨Vb.mul_mem (hbV v hv) (Vb.inv_mem hv), ?_⟩
      rw [map_mul, map_inv, hbb, hinv2 v, hinv2 (b v), mul_comm]
    rw [hJ, Subgroup.mem_bot, mul_inv_eq_one] at hy
    have hvJ : v ∈ n5Fix b Vb := ⟨hv, hy⟩
    rw [hJ] at hvJ
    exact hvJ
  · intro v hv
    have : v ∈ n5Fix b Vb := by rw [hJ]; exact hv
    exact this.2

theorem z35_eq_one_of_commute (h : Z35 Mb Tb Lb Vb) {a : MulAut X} (ha : a ∈ Tb) (ha2 : a ^ 2 = 1)
    (hc : ∀ x ∈ Mb, a * x = x * a) : a = 1 := by
  have key : ∀ r ∈ Tb, ∀ v ∈ Vb, a (r v) = r v := by
    intro r hr v hv
    have hbT : r⁻¹ * a * r ∈ Tb := Tb.mul_mem (Tb.mul_mem (Tb.inv_mem hr) ha) hr
    have hb2 : (r⁻¹ * a * r) ^ 2 = 1 := by
      have haa : a * a = 1 := by rw [← pow_two]; exact ha2
      calc (r⁻¹ * a * r) ^ 2 = r⁻¹ * (a * a) * r := by rw [pow_two]; group
        _ = 1 := by rw [haa]; group
    have hbc : ∀ x ∈ Mb, r⁻¹ * a * r * x = x * (r⁻¹ * a * r) := by
      intro x hx
      have hx' : r * x * r⁻¹ ∈ Mb := n5_conj_mem h hr hx
      have := hc _ hx'
      calc r⁻¹ * a * r * x = r⁻¹ * (a * (r * x * r⁻¹)) * r := by group
        _ = r⁻¹ * ((r * x * r⁻¹) * a) * r := by rw [this]
        _ = x * (r⁻¹ * a * r) := by group
    have h1 := n5_triv_V h hbT hb2 hbc v hv
    have h2 : r⁻¹ (a (r v)) = v := h1
    have h3 := congrArg r h2
    rwa [MulAut.apply_inv_self] at h3
  have hle : orbSup Tb Vb ≤ n5Fix a ⊤ := orbSup_le fun r hr => by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨trivial, key r hr v hv⟩
  ext x
  have hx : x ∈ n5Fix a ⊤ := hle (h.gen ▸ Subgroup.mem_top x)
  exact hx.2

private theorem n5_ker_central (h : Z35 Mb Tb Lb Vb) {W : Subgroup X}
    (hWinv : ∀ m ∈ Mb, ∀ w ∈ W, m w ∈ W) {t : MulAut X} (ht : t ∈ Tb)
    (hSW : Vb.map t.toMonoidHom ≤ W) {n : MulAut X} (hn : n ∈ Mb) (hnW : ∀ w ∈ W, n w = w) :
    ∀ x ∈ Mb, n * x = x * n := by
  have hinvW : ∀ m ∈ Mb, ∀ w ∈ W, m⁻¹ w ∈ W := fun m hm w hw => hWinv m⁻¹ (Mb.inv_mem hm) w hw
  have hcomm : ∀ s ∈ Tb, ∀ l ∈ conjAutSub s Lb, n * l = l * n := by
    intro s hs
    have hKM : conjAutSub s Lb ≤ Mb := n5_conj_le h hs
    have hHn : ∀ k ∈ conjAutSub s Lb, ∀ x ∈ conjAutSub s Lb ⊓ centSub W,
        k * x * k⁻¹ ∈ conjAutSub s Lb ⊓ centSub W := by
      intro k hk x hx
      refine ⟨(conjAutSub s Lb).mul_mem ((conjAutSub s Lb).mul_mem hk hx.1)
        ((conjAutSub s Lb).inv_mem hk), fun w hw => ?_⟩
      show k (x (k⁻¹ w)) = w
      rw [hx.2 _ (hinvW k (hKM hk) w hw), MulAut.apply_inv_self]
    have hmem : ∀ l ∈ conjAutSub s Lb, ⁅n, l⁆ ∈ conjAutSub s Lb ⊓ centSub W := by
      intro l hl
      refine ⟨?_, fun w hw => ?_⟩
      · rw [commutatorElement_def]
        exact (conjAutSub s Lb).mul_mem
          ((Subgroup.mem_normalizer_iff.mp (n5_le_normalizer_conj h hs hn) l).mp hl)
          ((conjAutSub s Lb).inv_mem hl)
      · rw [commutatorElement_def]
        show n (l (n⁻¹ (l⁻¹ w))) = w
        have h1 : l⁻¹ w ∈ W := hinvW l (hKM hl) w hw
        rw [n5_inv_fix (hnW _ h1), MulAut.apply_inv_self, hnW w hw]
    rcases n5_central_or_eq (n5_quasi_conj h s) inf_le_left hHn with hc | htop
    · exact n5_commute_of_central le_rfl (n5_perf_conj h s) (fun l hl => (hmem l hl).1)
        (fun l hl k hk => hc _ (hmem l hl) k hk)
    · exfalso
      obtain ⟨l, hl, w, hw, hne⟩ := n5_nontriv h hs ht
      exact hne ((htop hl).2 w (hSW hw))
  have hcen : Mb ≤ Subgroup.centralizer ({n} : Set (MulAut X)) := by
    rw [h.Mp_eq]
    refine conjClosure_le fun s hs y hy => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcomm s hs _ (n5_conj_mem_of_mem hy)).symm
  intro x hx
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hcen hx)).symm

theorem z35_faithful_orbit (h : Z35 Mb Tb Lb Vb) {A : Subgroup (MulAut X)} (hA : A ≤ Tb)
    (hAe : IsElemAbelian2 A) :
    ∀ t ∈ Tb, ∀ a ∈ A, (∀ w ∈ orbSup A (Vb.map t.toMonoidHom), a w = w) → a = 1 := by
  intro t ht a haA hatriv
  have haT : a ∈ Tb := hA haA
  have hWinv : ∀ m ∈ Mb, ∀ w ∈ orbSup A (Vb.map t.toMonoidHom), m w ∈ orbSup A (Vb.map t.toMonoidHom) :=
    fun m hm w hw => n5_orb_inv h hA ht hm hw
  have hSW : Vb.map t.toMonoidHom ≤ orbSup A (Vb.map t.toMonoidHom) := by
    have := map_le_orbSup (T := A) (V := Vb.map t.toMonoidHom) A.one_mem
    rwa [n5_map_one] at this
  have hcomm : ∀ s ∈ Tb, ∀ l ∈ conjAutSub s Lb, a * l = l * a := by
    intro s hs
    have hKM : conjAutSub s Lb ≤ Mb := n5_conj_le h hs
    have hmK : ∀ l ∈ conjAutSub s Lb, ⁅a, l⁆ ∈ Mb := by
      intro l hl
      rw [commutatorElement_def]
      exact Mb.mul_mem (n5_conj_mem h haT (hKM hl)) (Mb.inv_mem (hKM hl))
    refine n5_commute_of_central hKM (n5_perf_conj h s) hmK fun l hl k hk => ?_
    refine n5_ker_central h hWinv ht hSW (hmK l hl) (fun w hw => ?_) k hk
    rw [commutatorElement_def]
    show a (l (a⁻¹ (l⁻¹ w))) = w
    have h1 : l⁻¹ w ∈ orbSup A (Vb.map t.toMonoidHom) := hWinv l⁻¹ (Mb.inv_mem (hKM hl)) w hw
    rw [n5_inv_fix (hatriv _ h1), MulAut.apply_inv_self, hatriv w hw]
  have hac : ∀ x ∈ Mb, a * x = x * a := by
    have hcen : Mb ≤ Subgroup.centralizer ({a} : Set (MulAut X)) := by
      rw [h.Mp_eq]
      refine conjClosure_le fun s hs y hy => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcomm s hs _ (n5_conj_mem_of_mem hy)).symm
    intro x hx
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hcen hx)).symm
  exact z35_eq_one_of_commute h haT (hAe.2 a haA) hac

end Faithful

section Offender

variable {X : Type} [CommGroup X] [Finite X] {Mb Tb Lb : Subgroup (MulAut X)} {Vb : Subgroup X}

private theorem n5_exists_qhat (h : Z35 Mb Tb Lb Vb) :
    ∃ A : Subgroup (MulAut X), A ∈ QhatStar (Mb ⊔ Tb) ∧ A ≤ Tb := by
  have hne : qhatOf (Mb ⊔ Tb) ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top h.qhat
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
  have hr2 : r ≤ 2 := WithTop.coe_le_coe.mp (hr ▸ h.qhat)
  obtain ⟨B, hB⟩ := QhatStar_nonempty hr.symm hr2
  have hB2 : IsPGroup 2 ↥B := by
    obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hB
    exact hA2.isElemAbelian2.isPGroup
  obtain ⟨x, hx, hBx⟩ := F7.isSylowTwoOf_exists_conj_le h.sylow (QhatStar_le hB) hB2
  refine ⟨conjBy x⁻¹ B, conjBy_mem_QhatStar hB ((Mb ⊔ Tb).inv_mem hx), fun y hy => ?_⟩
  rw [mem_conjBy_iff, inv_inv] at hy
  have := hBx hy
  rw [mem_conjSub] at this
  simpa [mul_assoc] using this

private theorem n5_kRPlusLe {G A : Subgroup (MulAut X)} (hAQ : A ∈ QhatStar G) :
    A ∈ kRPlusLe G 3 2 := by
  obtain ⟨r, hqr, hr2, hAk, -⟩ := QhatStar_spec hAQ
  have hA2 : IsA2 G A := hAk.1.1
  have hAr : rAV A = r := hAk.1.2
  have hcub : commSeries A 3 = ⊥ := hAk.2
  have hplus : A ∈ RPlus G := D2_3_2 hA2 hcub (by rw [hAr]; exact hqr.symm)
  exact ⟨⟨⟨hA2, by rw [hAr]; exact hr2⟩, hcub⟩, hplus⟩

private theorem n5_one_orbit (h : Z35 Mb Tb Lb Vb) {A : Subgroup (MulAut X)}
    (hAQ : A ∈ QhatStar (Mb ⊔ Tb)) (hAT : A ≤ Tb) : orbSup A Vb ≠ ⊤ := by
  intro hW
  have hmemA := n5_kRPlusLe hAQ
  obtain ⟨a, haA, haS⟩ : ∃ a ∈ A, a ∉ stabSub Vb := by
    by_contra hcon
    push Not at hcon
    exact h.lt.ne ((orbSup_eq_of_stab hcon).symm.trans hW)
  have haT : a ∈ Tb := hAT haA
  set Cj : Set (Subgroup X) := {S | ∃ t ∈ Tb, S = Vb.map t.toMonoidHom}
  have hind : iSupIndep (fun i : ↥Cj => (i : Subgroup X)) := (sSupIndep_iff Cj).mp h.indep
  have hsup : ⨆ i : ↥Cj, (i : Subgroup X) = ⊤ := by
    refine top_unique ?_
    rw [← h.gen]
    exact orbSup_le fun t ht => le_iSup_of_le (⟨Vb.map t.toMonoidHom, t, ht, rfl⟩ : ↥Cj) le_rfl
  have hrank : ∀ i : ↥Cj, 2 ≤ rk ↥(i : Subgroup X) := by
    rintro ⟨S, t, ht, rfl⟩
    show 2 ≤ rk ↥(Vb.map t.toMonoidHom)
    rw [rk_map_aut]
    exact (n5_rank h).le
  have hperm : ∀ g ∈ A, ∀ i : ↥Cj, ∃ j : ↥Cj,
      (i : Subgroup X).map g.toMonoidHom = (j : Subgroup X) := by
    rintro g hg ⟨S, t, ht, rfl⟩
    exact ⟨⟨Vb.map (g * t).toMonoidHom, g * t, Tb.mul_mem (hAT hg) ht, rfl⟩,
      (map_mul_aut' g t Vb).symm⟩
  have hVC : Vb ∈ Cj := ⟨1, Tb.one_mem, (n5_map_one Vb).symm⟩
  have hidx : (A ⊓ stabSub Vb).relIndex A ≤ 2 :=
    d29_index_le_two h.exp hmemA hind hsup hrank hperm ⟨Vb, hVC⟩
  have hcos : ∀ g ∈ A, g ∈ stabSub Vb ∨ a⁻¹ * g ∈ stabSub Vb := by
    have hne1 : ((A ⊓ stabSub Vb).subgroupOf A).index ≠ 1 := by
      rw [Ne, Subgroup.index_eq_one]
      intro htop
      have : (⟨a, haA⟩ : ↥A) ∈ (A ⊓ stabSub Vb).subgroupOf A := htop ▸ Subgroup.mem_top _
      exact haS (Subgroup.mem_subgroupOf.mp this).2
    have hne0 : ((A ⊓ stabSub Vb).subgroupOf A).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h2 : ((A ⊓ stabSub Vb).subgroupOf A).index = 2 := by
      have : ((A ⊓ stabSub Vb).subgroupOf A).index ≤ 2 := hidx
      omega
    intro g hg
    by_cases hgs : g ∈ stabSub Vb
    · exact Or.inl hgs
    · right
      have hmem : (⟨a, haA⟩ : ↥A)⁻¹ * ⟨g, hg⟩ ∈ (A ⊓ stabSub Vb).subgroupOf A := by
        rw [Subgroup.mul_mem_iff_of_index_two h2]
        constructor
        · intro ha'
          have h3 : a⁻¹ ∈ stabSub Vb := (Subgroup.mem_subgroupOf.mp ha').2
          exact absurd (by simpa using (stabSub Vb).inv_mem h3) haS
        · intro hg'
          exact absurd (Subgroup.mem_subgroupOf.mp hg').2 hgs
      exact (Subgroup.mem_subgroupOf.mp hmem).2
  have hne : Vb ≠ Vb.map a.toMonoidHom := fun he => haS (mem_stabSub_iff_map_eq.mpr he.symm)
  have hsup2 : Vb ⊔ Vb.map a.toMonoidHom = ⊤ := by
    refine top_unique ?_
    rw [← hW]
    refine orbSup_le fun g hg => ?_
    rcases hcos g hg with hgs | hgs
    · rw [mem_stabSub_iff_map_eq.mp hgs]
      exact le_sup_left
    · have e : Vb.map g.toMonoidHom = Vb.map a.toMonoidHom := by
        calc Vb.map g.toMonoidHom = Vb.map (a * (a⁻¹ * g)).toMonoidHom := by
              rw [mul_inv_cancel_left]
          _ = (Vb.map (a⁻¹ * g).toMonoidHom).map a.toMonoidHom := map_mul_aut' _ _ _
          _ = Vb.map a.toMonoidHom := by rw [mem_stabSub_iff_map_eq.mp hgs]
      rw [e]
      exact le_sup_right
  have hdisj : Disjoint Vb (Vb.map a.toMonoidHom) :=
    h.indep.pairwiseDisjoint hVC ⟨a, haT, rfl⟩ hne
  have hCj2 : ∀ S ∈ Cj, S = Vb ∨ S = Vb.map a.toMonoidHom := by
    intro S hS
    by_contra hcon
    have hsub : ({Vb, Vb.map a.toMonoidHom} : Set (Subgroup X)) ⊆ Cj := by
      intro x hx
      rcases hx with rfl | rfl
      · exact hVC
      · exact ⟨a, haT, rfl⟩
    have hnot : S ∉ ({Vb, Vb.map a.toMonoidHom} : Set (Subgroup X)) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact hcon
    have hd := h.indep.disjoint_sSup hS hsub hnot
    rw [sSup_pair, hsup2, disjoint_top] at hd
    obtain ⟨t, -, rfl⟩ := hS
    exact n5_map_ne_bot h t hd
  have hP : Mb ⊔ Tb ≤ n5Perm Vb (Vb.map a.toMonoidHom) := by
    refine sup_le (fun m hm => mem_n5Perm.mpr (Or.inl ⟨mem_stabSub_iff_map_eq.mp (n5_Mb_le_stab h hm),
      mem_stabSub_iff_map_eq.mp (n5_le_stab (fun m' hm' w hw => n5_map_inv h haT hm' hw) hm)⟩)) ?_
    intro s hs
    have hinj : ∀ J J' : Subgroup X, J.map s.toMonoidHom = J'.map s.toMonoidHom → J = J' :=
      fun J J' e => Subgroup.map_injective (f := s.toMonoidHom) (fun x y hxy => s.injective hxy) e
    rcases hCj2 (Vb.map s.toMonoidHom) ⟨s, hs, rfl⟩ with h1 | h1 <;>
      rcases hCj2 ((Vb.map a.toMonoidHom).map s.toMonoidHom)
        ⟨s * a, Tb.mul_mem hs haT, (map_mul_aut' s a Vb).symm⟩ with h2 | h2
    · exact absurd (hinj _ _ (h1.trans h2.symm)) hne
    · exact mem_n5Perm.mpr (Or.inl ⟨h1, h2⟩)
    · exact mem_n5Perm.mpr (Or.inr ⟨h1, h2⟩)
    · exact absurd (hinj _ _ (h1.trans h2.symm)) hne
  have hTS : TwoSummands (Mb ⊔ Tb) Vb (Vb.map a.toMonoidHom) :=
    ⟨hdisj, hsup2, fun g hg => mem_n5Perm.mp (hP hg)⟩
  exact haS (d29_six h.exp hTS (n5_rank h) h.o2 A hAQ haA)

private theorem n5_exists_good (h : Z35 Mb Tb Lb Vb) {A : Subgroup (MulAut X)}
    (hAQ : A ∈ QhatStar (Mb ⊔ Tb)) (hAT : A ≤ Tb) :
    ∃ t ∈ Tb, Nat.card ↥(orbSup A (Vb.map t.toMonoidHom)) ≤
      Nat.card A * Nat.card ↥(orbSup A (Vb.map t.toMonoidHom) ⊓ fixV A) := by
  obtain ⟨r, -, hr2, hAk, -⟩ := QhatStar_spec hAQ
  have hA2 : IsA2 (Mb ⊔ Tb) A := hAk.1.1
  have hAe : IsElemAbelian2 A := hA2.isElemAbelian2
  have hrAV : rkIdx (fixV A) ≤ 2 * rk A := by
    have h1 := hA2.rAV_mul
    have h2 : rAV A ≤ 2 := by rw [hAk.1.2]; exact hr2
    have h3 : (rkIdx (fixV A) : ℚ) ≤ 2 * rk A := by
      rw [← h1]
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    exact_mod_cast h3
  have key : ∀ U : Subgroup X, rk U ≤ rk A + rk ↥(U ⊓ fixV A) →
      Nat.card U ≤ Nat.card A * Nat.card ↥(U ⊓ fixV A) := by
    intro U hU
    rw [card_eq_two_pow h.exp U, card_eq_two_pow h.exp (U ⊓ fixV A),
      card_eq_two_pow_of_isPGroup hAe.isPGroup, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) hU
  obtain ⟨t, ht, hnot⟩ : ∃ t ∈ Tb, ¬ Vb.map t.toMonoidHom ≤ orbSup A Vb := by
    by_contra hcon
    push Not at hcon
    exact n5_one_orbit h hAQ hAT (top_unique (h.gen ▸ orbSup_le hcon))
  have hd := z35_independent_sum h hAT Tb.one_mem ht (by rwa [n5_map_one])
  rw [n5_map_one] at hd
  have hn := n5_rk_two (le_stabSub_orbSup A Vb) (le_stabSub_orbSup A (Vb.map t.toMonoidHom)) hd
  by_cases h1 : rk ↥(orbSup A Vb) ≤ rk A + rk ↥(orbSup A Vb ⊓ fixV A)
  · exact ⟨1, Tb.one_mem, by rw [n5_map_one]; exact key _ h1⟩
  by_cases h2 : rk ↥(orbSup A (Vb.map t.toMonoidHom)) ≤
      rk A + rk ↥(orbSup A (Vb.map t.toMonoidHom) ⊓ fixV A)
  · exact ⟨t, ht, key _ h2⟩
  exfalso
  omega

theorem z35_offender (h : Z35 Mb Tb Lb Vb) :
    ∃ A : Subgroup (MulAut X), A ∈ QhatStar (Mb ⊔ Tb) ∧ A ≤ Tb ∧
      (∀ a ∈ A, (∀ w ∈ orbSup A Vb, a w = w) → a = 1) ∧
      Nat.card ↥(orbSup A Vb) ≤ Nat.card A * Nat.card ↥(orbSup A Vb ⊓ fixV A) := by
  obtain ⟨A, hAQ, hAT⟩ := n5_exists_qhat h
  obtain ⟨t, ht, hineq⟩ := n5_exists_good h hAQ hAT
  have htG : t⁻¹ ∈ Mb ⊔ Tb := (Mb ⊔ Tb).inv_mem ((le_sup_right : Tb ≤ Mb ⊔ Tb) ht)
  have hA'Q : conjBy t⁻¹ A ∈ QhatStar (Mb ⊔ Tb) := conjBy_mem_QhatStar hAQ htG
  have hA'T : conjBy t⁻¹ A ≤ Tb := by
    intro y hy
    rw [mem_conjBy_iff, inv_inv] at hy
    have e : y = t⁻¹ * (t * y * t⁻¹) * t := by group
    rw [e]
    exact Tb.mul_mem (Tb.mul_mem (Tb.inv_mem ht) (hAT hy)) ht
  have hA'e : IsElemAbelian2 (conjBy t⁻¹ A) := by
    obtain ⟨r, -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA'Q
    exact hA2.isElemAbelian2
  have horb : orbSup (conjBy t⁻¹ A) Vb =
      (orbSup A (Vb.map t.toMonoidHom)).map t⁻¹.toMonoidHom := by
    have := n5_orbSup_conj t⁻¹ A (Vb.map t.toMonoidHom)
    rwa [← map_mul_aut' t⁻¹ t Vb, inv_mul_cancel, n5_map_one] at this
  have hinj : Function.Injective t⁻¹.toMonoidHom := fun x y hxy => t⁻¹.injective hxy
  refine ⟨conjBy t⁻¹ A, hA'Q, hA'T, ?_, ?_⟩
  · intro a ha hfa
    have := z35_faithful_orbit h hA'T hA'e 1 Tb.one_mem a ha
    rw [n5_map_one] at this
    exact this hfa
  · rw [horb, fixV_conjBy, ← Subgroup.map_inf_eq _ _ t⁻¹.toMonoidHom hinj,
      Subgroup.card_map_of_injective hinj, Subgroup.card_map_of_injective hinj, card_conjBy]
    exact hineq

end Offender

end CFSG.Quasithin
