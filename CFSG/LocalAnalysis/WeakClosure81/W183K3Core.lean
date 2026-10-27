module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2One
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Quasi
import CFSG.LocalAnalysis.WeakClosure81.W183K3Dyn

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183K3

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {R Y T L L₁ L₂ N : Subgroup (LGL 2 V)}

private theorem w183K3Core_exists_mul_of_mem_sup {A B : Subgroup (LGL 2 V)}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : LGL 2 V} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction (p := fun y _ => ∃ a ∈ A, ∃ b ∈ B, a * b = y)
    ?_ ?_ ?_ ?_ hx
  · rintro y (hy | hy)
    · exact ⟨y, hy, 1, B.one_mem, mul_one y⟩
    · exact ⟨1, A.one_mem, y, hy, one_mul y⟩
  · exact ⟨1, A.one_mem, 1, B.one_mem, mul_one 1⟩
  · rintro _ _ _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
    refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
    calc (a₁ * a₂) * (b₁ * b₂) = a₁ * ((a₂ * b₁) * b₂) := by group
      _ = a₁ * ((b₁ * a₂) * b₂) := by rw [hcomm a₂ ha₂ b₁ hb₁]
      _ = (a₁ * b₁) * (a₂ * b₂) := by group
  · rintro _ _ ⟨a, ha, b, hb, rfl⟩
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    rw [mul_inv_rev]
    exact hcomm a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)

private theorem w183K3Core_mem_quasiCentre_of_mem_center {L : Subgroup (LGL 2 V)} {t : ↥L}
    (ht : t ∈ Subgroup.center ↥L) : (t : LGL 2 V) ∈ quasiCentre L := by
  rw [mem_quasiCentre]
  refine ⟨t.2, fun l hl => ?_⟩
  have h := (Subgroup.mem_center_iff.mp ht) (⟨l, hl⟩ : ↥L)
  exact (congrArg Subtype.val h).symm

private theorem w183K3Core_mem_center_of_mem_quasiCentre' {L : Subgroup (LGL 2 V)}
    {t : ↥L} {z : LGL 2 V} (ht : (t : LGL 2 V) = z) (hz : z ∈ quasiCentre L) :
    t ∈ Subgroup.center ↥L := by
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  rw [← ht] at hz
  exact ((mem_quasiCentre.mp hz).2 (y : LGL 2 V) y.2).symm

private theorem w183K3Core_orderOf_odd_of_mem_quasiCentre {L : Subgroup (LGL 2 V)}
    (hodd : Odd (Nat.card ↥(Subgroup.center ↥L))) {z : LGL 2 V} (hz : z ∈ quasiCentre L) :
    Odd (orderOf z) := by
  obtain ⟨hzL, hzc⟩ := mem_quasiCentre.mp hz
  have hmem : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hzc (y : LGL 2 V) y.2).symm
  have hdvd : orderOf (⟨⟨z, hzL⟩, hmem⟩ : ↥(Subgroup.center ↥L)) ∣
      Nat.card ↥(Subgroup.center ↥L) := orderOf_dvd_natCard _
  have heq : orderOf (⟨⟨z, hzL⟩, hmem⟩ : ↥(Subgroup.center ↥L)) = orderOf z :=
    (Subgroup.orderOf_coe (G := ↥L) (H := Subgroup.center ↥L) _).symm.trans
      (Subgroup.orderOf_mk (H := L) z hzL)
  rw [heq] at hdvd
  exact Odd.of_dvd_nat hodd hdvd

structure QuasiCore (R L N : Subgroup (LGL 2 V)) : Prop where
  le : L ≤ R
  normal : ∀ y ∈ R, ∀ l ∈ L, y * l * y⁻¹ ∈ L
  quasi : CFSG.Open.IsQuasisimple ↥L
  odd : Odd (Nat.card ↥N)
  cent : ∀ y ∈ R, (∀ l ∈ L, y * l = l * y) → y ∈ N

structure Br3OneComp (Y T L : Subgroup (LGL 2 V)) : Prop where
  core : QuasiCore Y L (quasiCentre L)
  dynkin : ∃ τ ∈ T, ActsOnDynkinMod (quasiCentre L) L τ

structure Br3TwoComp (Y T L₁ L₂ : Subgroup (LGL 2 V)) : Prop where
  le₁ : L₁ ≤ Y
  le₂ : L₂ ≤ Y
  quasi₁ : CFSG.Open.IsQuasisimple ↥L₁
  quasi₂ : CFSG.Open.IsQuasisimple ↥L₂
  odd₁ : Odd (Nat.card ↥(Subgroup.center ↥L₁))
  odd₂ : Odd (Nat.card ↥(Subgroup.center ↥L₂))
  comm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a
  ne : L₁ ≠ L₂
  perm : ∀ y ∈ Y, (cj y L₁ = L₁ ∧ cj y L₂ = L₂) ∨ (cj y L₁ = L₂ ∧ cj y L₂ = L₁)
  swap : ∃ x ∈ T, cj x L₁ = L₂
  cent : ∀ y ∈ Y, (∀ l ∈ L₁, y * l = l * y) → (∀ l ∈ L₂, y * l = l * y) → y ∈ L₁ ⊔ L₂
  gen : ∀ y ∈ Y, ∃ l ∈ L₁ ⊔ L₂, ∃ t ∈ T, y = l * t

theorem Br3TwoComp.symm (h : Br3TwoComp Y T L₁ L₂) : Br3TwoComp Y T L₂ L₁ := by
  refine
    { le₁ := h.le₂
      le₂ := h.le₁
      quasi₁ := h.quasi₂
      quasi₂ := h.quasi₁
      odd₁ := h.odd₂
      odd₂ := h.odd₁
      comm := fun a ha b hb => (h.comm b hb a ha).symm
      ne := h.ne.symm
      perm := ?_
      swap := ?_
      cent := fun y hy h₂ h₁ => by rw [sup_comm]; exact h.cent y hy h₁ h₂
      gen := ?_ }
  · intro y hy
    rcases h.perm y hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr ⟨h2, h1⟩
  · obtain ⟨x, hxT, hx⟩ := h.swap
    refine ⟨x⁻¹, T.inv_mem hxT, ?_⟩
    change (L₂.map (MulAut.conj x⁻¹).toMonoidHom) = L₁
    rw [← hx]
    change (L₁.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = L₁
    rw [Subgroup.map_map]
    have hcomp : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
        MonoidHom.id (LGL 2 V) := by
      apply MonoidHom.ext
      intro a
      change MulAut.conj x⁻¹ (MulAut.conj x a) = a
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group
    rw [hcomp, Subgroup.map_id]
  · intro y hy
    obtain ⟨l, hl, t, ht, rfl⟩ := h.gen y hy
    exact ⟨l, by rw [sup_comm]; exact hl, t, ht, rfl⟩

theorem Br3TwoComp.eq_one_of_isPGroup_cent (h : Br3TwoComp Y T L₁ L₂) {x : LGL 2 V} (hxY : x ∈ Y)
    {k : ℕ} (hxk : x ^ (2 ^ k) = 1) (h₁ : ∀ l ∈ L₁, x * l = l * x)
    (h₂ : ∀ l ∈ L₂, x * l = l * x) : x = 1 := by
  obtain ⟨l₁, hl₁, l₂, hl₂, hxl⟩ :=
    w183K3Core_exists_mul_of_mem_sup h.comm (h.cent x hxY h₁ h₂)
  have hl₁c : l₁ ∈ quasiCentre L₁ := by
    rw [mem_quasiCentre]
    refine ⟨hl₁, fun l hl => ?_⟩
    have hll₂ : l * l₂ = l₂ * l := h.comm l hl l₂ hl₂
    have key : l₁ * l * l₂ = l * l₁ * l₂ := by
      calc l₁ * l * l₂ = l₁ * (l * l₂) := by group
        _ = l₁ * (l₂ * l) := by rw [hll₂]
        _ = (l₁ * l₂) * l := by group
        _ = x * l := by rw [← hxl]
        _ = l * x := h₁ l hl
        _ = l * (l₁ * l₂) := by rw [hxl]
        _ = l * l₁ * l₂ := by group
    exact mul_right_cancel key
  have hl₂c : l₂ ∈ quasiCentre L₂ := by
    rw [mem_quasiCentre]
    refine ⟨hl₂, fun l hl => ?_⟩
    have hl₁l : l₁ * l = l * l₁ := h.comm l₁ hl₁ l hl
    have key : l₁ * (l₂ * l) = l₁ * (l * l₂) := by
      calc l₁ * (l₂ * l) = (l₁ * l₂) * l := by group
        _ = x * l := by rw [hxl]
        _ = l * x := h₂ l hl
        _ = l * (l₁ * l₂) := by rw [hxl]
        _ = (l * l₁) * l₂ := by group
        _ = (l₁ * l) * l₂ := by rw [hl₁l]
        _ = l₁ * (l * l₂) := by group
    exact mul_left_cancel key
  have hodd₁ : Odd (orderOf l₁) := w183K3Core_orderOf_odd_of_mem_quasiCentre h.odd₁ hl₁c
  have hodd₂ : Odd (orderOf l₂) := w183K3Core_orderOf_odd_of_mem_quasiCentre h.odd₂ hl₂c
  have hcomm : Commute l₁ l₂ := h.comm l₁ hl₁ l₂ hl₂
  have hdvd : orderOf x ∣ orderOf l₁ * orderOf l₂ := by
    rw [← hxl]
    exact hcomm.orderOf_mul_dvd_mul_orderOf
  have hdvd2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hxk
  have hoddx : Odd (orderOf x) := Odd.of_dvd_nat (hodd₁.mul hodd₂) hdvd
  have hcop : Nat.Coprime (orderOf x) (2 ^ k) := (hoddx.coprime_two_right).pow_right k
  have hone : orderOf x = 1 := by
    have h1 : orderOf x ∣ 1 := hcop.dvd_of_dvd_mul_right (by simpa using hdvd2)
    exact Nat.dvd_one.mp h1
  exact orderOf_eq_one_iff.mp hone

@[expose] noncomputable def psiQuot (R L : Subgroup (LGL 2 V))
    (hn : ∀ y ∈ R, ∀ l ∈ L, y * l * y⁻¹ ∈ L) : ↥R →* MulAut (↥L ⧸ Subgroup.center ↥L) where
  toFun r := QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥L) (psiOf R L hn r)
    (Subgroup.map_center_eq (psiOf R L hn r))
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H l => simp [QuotientGroup.congr_mk]
  map_mul' := by
    intro a b
    ext x
    induction x using QuotientGroup.induction_on with
    | H l => simp [QuotientGroup.congr_mk]

theorem psiQuot_apply_mk (hn : ∀ y ∈ R, ∀ l ∈ L, y * l * y⁻¹ ∈ L) (r : ↥R) (l : ↥L) :
    psiQuot R L hn r (QuotientGroup.mk l) = QuotientGroup.mk (psiOf R L hn r l) :=
  QuotientGroup.congr_mk (Subgroup.center ↥L) (Subgroup.center ↥L) (psiOf R L hn r)
    (Subgroup.map_center_eq (psiOf R L hn r)) l

private theorem w183K3Core_psiQuot_apply_eq_conj (hn : ∀ y ∈ R, ∀ l ∈ L, y * l * y⁻¹ ∈ L)
    {l : LGL 2 V} (hlR : l ∈ R) (hl : l ∈ L) :
    psiQuot R L hn ⟨l, hlR⟩ = MulAut.conj (QuotientGroup.mk (⟨l, hl⟩ : ↥L)) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H a =>
    rw [psiQuot_apply_mk, MulAut.conj_apply]
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rfl

theorem mem_ker_psiQuot_iff (hn : ∀ y ∈ R, ∀ l ∈ L, y * l * y⁻¹ ∈ L) (r : ↥R) :
    r ∈ (psiQuot R L hn).ker ↔
      ∀ l ∈ L, (r : LGL 2 V) * l * (r : LGL 2 V)⁻¹ * l⁻¹ ∈ quasiCentre L := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h l hl
    let t : ↥L := psiOf R L hn r ⟨l, hl⟩ * (⟨l, hl⟩ : ↥L)⁻¹
    have h1 : (t : ↥L ⧸ Subgroup.center ↥L) = 1 := by
      have hx := congrArg (fun f : MulAut (↥L ⧸ Subgroup.center ↥L) =>
        f (QuotientGroup.mk (⟨l, hl⟩ : ↥L))) h
      rw [psiQuot_apply_mk, MulAut.one_apply] at hx
      change QuotientGroup.mk (psiOf R L hn r ⟨l, hl⟩ * (⟨l, hl⟩ : ↥L)⁻¹) = 1
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hx, mul_inv_cancel]
    have ht : t ∈ Subgroup.center ↥L := (QuotientGroup.eq_one_iff t).mp h1
    have hz := w183K3Core_mem_quasiCentre_of_mem_center ht
    have hteq : (t : LGL 2 V) = (r : LGL 2 V) * l * (r : LGL 2 V)⁻¹ * l⁻¹ := by
      simp only [t, Subgroup.coe_mul, Subgroup.coe_inv, psiOf_apply, Subtype.coe_mk]
    rwa [hteq] at hz
  · intro h
    ext x
    induction x using QuotientGroup.induction_on with
    | H l =>
      rw [psiQuot_apply_mk, MulAut.one_apply, QuotientGroup.eq]
      refine w183K3Core_mem_center_of_mem_quasiCentre' ?_ (h l⁻¹ (L.inv_mem l.2))
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, psiOf_apply, Subtype.coe_mk]
      group

theorem QuasiCore.mem_ker_psiQuot_iff_centralizes (c : QuasiCore R L N) (r : ↥R) :
    r ∈ (psiQuot R L c.normal).ker ↔ ∀ l ∈ L, (r : LGL 2 V) * l = l * (r : LGL 2 V) := by
  rw [mem_ker_psiQuot_iff]
  constructor
  · intro h
    exact quasi_comm_of_comm_mod_centre c.quasi (fun l hl => c.normal (r : LGL 2 V) r.2 l hl) h
  · intro h l hl
    rw [h l hl]
    simp

private theorem w183K3Core_imgOf_quasiCentre_eq_bot (c : QuasiCore R L N) :
    imgOf (psiQuot R L c.normal) (quasiCentre L) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  rw [imgOf, Subgroup.mem_map] at hx
  obtain ⟨r, hr, rfl⟩ := hx
  rw [Subgroup.mem_subgroupOf] at hr
  rw [Subgroup.mem_bot]
  rw [← MonoidHom.mem_ker, QuasiCore.mem_ker_psiQuot_iff_centralizes c]
  intro l hl
  exact (mem_quasiCentre.mp hr).2 l hl

theorem QuasiCore.inf_ker_psiQuot_eq_bot (c : QuasiCore R L N) {D : Subgroup (LGL 2 V)}
    (hD : D ≤ R) (hD2 : IsPGroup 2 D) :
    D.subgroupOf R ⊓ (psiQuot R L c.normal).ker = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro d hd
  rw [Subgroup.mem_inf] at hd
  obtain ⟨hdD, hdker⟩ := hd
  have hdD' : (d : LGL 2 V) ∈ D := Subgroup.mem_subgroupOf.mp hdD
  have hcent : ∀ l ∈ L, (d : LGL 2 V) * l = l * (d : LGL 2 V) :=
    (QuasiCore.mem_ker_psiQuot_iff_centralizes c d).mp hdker
  have hdN : (d : LGL 2 V) ∈ N := c.cent (d : LGL 2 V) d.2 hcent
  have hmem : (d : LGL 2 V) ∈ D ⊓ N := ⟨hdD', hdN⟩
  have hd1 : (d : LGL 2 V) = 1 := by
    rw [isPGroup_inf_odd_eq_bot hD2 c.odd] at hmem
    simpa using hmem
  exact Subtype.ext hd1

theorem QuasiCore.card_imgOf_psiQuot (c : QuasiCore R L N) {D : Subgroup (LGL 2 V)}
    (hD : D ≤ R) (hD2 : IsPGroup 2 D) :
    Nat.card ↥(imgOf (psiQuot R L c.normal) D) = Nat.card ↥D := by
  let ψ := psiQuot R L c.normal
  let K := D.subgroupOf R
  have hker : K ⊓ ψ.ker = ⊥ := QuasiCore.inf_ker_psiQuot_eq_bot c hD hD2
  let φ : ↥K →* ↥(K.map ψ) :=
    { toFun := fun x => ⟨ψ (x : ↥R), Subgroup.mem_map.mpr ⟨(x : ↥R), x.2, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hφ : Function.Bijective φ := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      have hxy' : ψ (x : ↥R) = ψ (y : ↥R) := congrArg Subtype.val hxy
      have hmem : ((x : ↥R)⁻¹ * (y : ↥R)) ∈ K ⊓ ψ.ker := by
        refine ⟨K.mul_mem (K.inv_mem x.2) y.2, ?_⟩
        show ψ ((x : ↥R)⁻¹ * (y : ↥R)) = 1
        rw [map_mul, map_inv, hxy', inv_mul_cancel]
      rw [hker] at hmem
      have h1 : (x : ↥R)⁻¹ * (y : ↥R) = 1 := by simpa using hmem
      exact Subtype.ext (inv_mul_eq_one.mp h1)
    · intro y
      obtain ⟨r, hr, hry⟩ := Subgroup.mem_map.mp y.2
      exact ⟨⟨r, hr⟩, Subtype.ext hry⟩
  change Nat.card ↥(K.map ψ) = Nat.card ↥D
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD).toEquiv

theorem QuasiCore.imgOf_psiQuot_L (c : QuasiCore R L N) :
    imgOf (psiQuot R L c.normal) L = innAutOf (↥L ⧸ Subgroup.center ↥L) := by
  apply le_antisymm
  · intro x hx
    rw [imgOf, Subgroup.mem_map] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    rw [Subgroup.mem_subgroupOf] at hr
    rw [innAutOf, MonoidHom.mem_range]
    exact ⟨QuotientGroup.mk (⟨(r : LGL 2 V), hr⟩ : ↥L),
      (w183K3Core_psiQuot_apply_eq_conj c.normal r.2 hr).symm⟩
  · intro x hx
    rw [innAutOf, MonoidHom.mem_range] at hx
    obtain ⟨q, rfl⟩ := hx
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    refine Subgroup.mem_map.mpr ⟨⟨(a : LGL 2 V), c.le a.2⟩,
      Subgroup.mem_subgroupOf.mpr a.2, ?_⟩
    exact w183K3Core_psiQuot_apply_eq_conj c.normal (c.le a.2) a.2

theorem QuasiCore.psiQuot_dynkin (c : QuasiCore R L N) {t : LGL 2 V} (ht : t ∈ R)
    (hd : ActsOnDynkinMod (quasiCentre L) L t) :
    ActsOnDynkinMod ⊥ (innAutOf (↥L ⧸ Subgroup.center ↥L)) (psiQuot R L c.normal ⟨t, ht⟩) := by
  let ψ := psiQuot R L c.normal
  have hker : ψ.ker ⊓ (L.subgroupOf R) ≤ (quasiCentre L).subgroupOf R := by
    intro r hr
    rw [Subgroup.mem_inf] at hr
    obtain ⟨hrker, hrL⟩ := hr
    rw [Subgroup.mem_subgroupOf] at hrL ⊢
    exact mem_quasiCentre.mpr
      ⟨hrL, (QuasiCore.mem_ker_psiQuot_iff_centralizes c r).mp hrker⟩
  have hsub := actsOnDynkinMod_subgroupOf R c.le ht hd
  have hmap := actsOnDynkinMod_map ψ hker hsub
  have himg : (L.subgroupOf R).map ψ = innAutOf (↥L ⧸ Subgroup.center ↥L) :=
    QuasiCore.imgOf_psiQuot_L c
  have hqc : ((quasiCentre L).subgroupOf R).map ψ = ⊥ :=
    w183K3Core_imgOf_quasiCentre_eq_bot c
  rwa [himg, hqc] at hmap

end W183K3

end CFSG.LocalAnalysis.WeakClosure81

end
