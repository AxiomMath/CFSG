module

public import CFSG.Quasithin.EmptyFaithful.LRed3Bridge
public import CFSG.Quasithin.H13.L32AC42f

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped IsMulCommutative

namespace Dec

variable {W : Type} [CommGroup W] {Vs : Subgroup W} {a : MulAut W}

theorem exists_eq (hcup : Vs ⊔ Vs.map a.toMonoidHom = ⊤) (m : W) :
    ∃ v ∈ Vs, ∃ w ∈ Vs, m = v * a w := by
  obtain ⟨v, hv, y, hy, hvy⟩ := Subgroup.mem_sup.mp (hcup ▸ Subgroup.mem_top m)
  obtain ⟨w, hw, rfl⟩ := hy
  exact ⟨v, hv, w, hw, hvy.symm⟩

theorem eq_of_mul_eq (hcap : Vs ⊓ Vs.map a.toMonoidHom = ⊥) {v w v' w' : W} (hv : v ∈ Vs)
    (hw : w ∈ Vs) (hv' : v' ∈ Vs) (hw' : w' ∈ Vs) (h : v * a w = v' * a w') :
    v = v' ∧ w = w' := by
  have h1 : v * v'⁻¹ = a (w' * w⁻¹) := by
    rw [map_mul, map_inv, eq_mul_inv_iff_mul_eq, mul_right_comm, h, mul_right_comm,
      mul_inv_cancel, one_mul]
  have hmem : v * v'⁻¹ ∈ Vs ⊓ Vs.map a.toMonoidHom :=
    ⟨Vs.mul_mem hv (Vs.inv_mem hv'), h1 ▸ ⟨w' * w⁻¹, Vs.mul_mem hw' (Vs.inv_mem hw), rfl⟩⟩
  rw [hcap, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  refine ⟨hmem, ?_⟩
  subst hmem
  exact a.injective (mul_left_cancel h)

theorem fix_parts (hcap : Vs ⊓ Vs.map a.toMonoidHom = ⊥) {g : MulAut W} (hgs : g ∈ stabSub Vs)
    (hga : g * a = a * g) {v w : W} (hv : v ∈ Vs) (hw : w ∈ Vs) (h : g (v * a w) = v * a w) :
    g v = v ∧ g w = w := by
  have e : g (v * a w) = g v * a (g w) := by
    rw [map_mul, ← MulAut.mul_apply, hga, MulAut.mul_apply]
  rw [e] at h
  exact eq_of_mul_eq hcap ((hgs v).mpr hv) ((hgs w).mpr hw) hv hw h

theorem eq_one_of_fix (hcup : Vs ⊔ Vs.map a.toMonoidHom = ⊤) {g : MulAut W} (hga : g * a = a * g)
    (hg : ∀ v ∈ Vs, g v = v) : g = 1 := by
  refine MulEquiv.ext fun m => ?_
  obtain ⟨v, hv, w, hw, rfl⟩ := exists_eq hcup m
  rw [map_mul, ← MulAut.mul_apply, hga, MulAut.mul_apply, hg v hv, hg w hw]
  rfl

theorem inf_centSub_eq_bot (hcup : Vs ⊔ Vs.map a.toMonoidHom = ⊤) {X : Subgroup (MulAut W)}
    (hXa : ∀ g ∈ X, g * a = a * g) : X ⊓ centSub Vs = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgX, hgc⟩
  exact Subgroup.mem_bot.mpr (eq_one_of_fix hcup (hXa g hgX) (mem_centSub.mp hgc))

theorem card_autSub [Finite W] (hcup : Vs ⊔ Vs.map a.toMonoidHom = ⊤) {X : Subgroup (MulAut W)}
    (hXs : X ≤ stabSub Vs) (hXa : ∀ g ∈ X, g * a = a * g) :
    Nat.card (autSub X Vs) = Nat.card X := by
  have h := card_autSub_mul hXs
  rw [inf_centSub_eq_bot hcup hXa, Subgroup.card_bot, mul_one] at h
  exact h

theorem eq_of_resHom_eq (hcup : Vs ⊔ Vs.map a.toMonoidHom = ⊤) {g g' : ↥(stabSub Vs)}
    (hga : (g : MulAut W) * a = a * g) (hga' : (g' : MulAut W) * a = a * g')
    (h : resHom Vs g = resHom Vs g') : g = g' := by
  set φ : MulAut W := ↑g with hφ
  set ψ : MulAut W := ↑g' with hψ
  have h1 : ψ⁻¹ * φ = 1 := by
    refine eq_one_of_fix hcup ?_ fun v hv => ?_
    · calc ψ⁻¹ * φ * a = ψ⁻¹ * (φ * a) := by group
        _ = ψ⁻¹ * (a * φ) := by rw [hga]
        _ = ψ⁻¹ * (a * ψ) * ψ⁻¹ * φ := by group
        _ = ψ⁻¹ * (ψ * a) * ψ⁻¹ * φ := by rw [hga']
        _ = a * (ψ⁻¹ * φ) := by group
    · have := congrArg (fun χ : MulAut ↥Vs => ((χ ⟨v, hv⟩ : ↥Vs) : W)) h
      simp only [resHom_apply] at this
      rw [MulAut.mul_apply, this]
      exact ψ.symm_apply_apply v
  exact Subtype.ext (inv_mul_eq_one.mp h1).symm

theorem card_eq_sq [Finite W] (hcap : Vs ⊓ Vs.map a.toMonoidHom = ⊥)
    (hcup : Vs ⊔ Vs.map a.toMonoidHom = ⊤) {F Y : Subgroup W} (hF : F ≤ Vs)
    (hY : ∀ v ∈ Vs, ∀ w ∈ Vs, v * a w ∈ Y ↔ v ∈ F ∧ w ∈ F) :
    Nat.card Y = Nat.card F ^ 2 := by
  let f : ↥F × ↥F → ↥Y := fun p =>
    ⟨p.1 * a p.2, (hY _ (hF p.1.2) _ (hF p.2.2)).mpr ⟨p.1.2, p.2.2⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p q hpq => ?_, fun y => ?_⟩
    · have h1 : (p.1 : W) * a p.2 = q.1 * a q.2 := congrArg Subtype.val hpq
      obtain ⟨h2, h3⟩ := eq_of_mul_eq hcap (hF p.1.2) (hF p.2.2) (hF q.1.2) (hF q.2.2) h1
      exact Prod.ext (Subtype.ext h2) (Subtype.ext h3)
    · obtain ⟨v, hv, w, hw, hvw⟩ := exists_eq hcup y
      have hmem := (hY v hv w hw).mp (hvw ▸ y.2)
      exact ⟨(⟨v, hmem.1⟩, ⟨w, hmem.2⟩), Subtype.ext hvw.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, sq]

theorem card_eq [Finite W] (hcap : Vs ⊓ Vs.map a.toMonoidHom = ⊥)
    (hcup : Vs ⊔ Vs.map a.toMonoidHom = ⊤) : Nat.card W = Nat.card Vs ^ 2 := by
  rw [← Subgroup.card_top (G := W)]
  exact card_eq_sq hcap hcup le_rfl fun v hv w hw => by simp [hv, hw]

theorem card_fixV [Finite W] (hcap : Vs ⊓ Vs.map a.toMonoidHom = ⊥)
    (hcup : Vs ⊔ Vs.map a.toMonoidHom = ⊤) {B : Subgroup (MulAut W)} (hBs : B ≤ stabSub Vs)
    (hBa : ∀ g ∈ B, g * a = a * g) :
    Nat.card (fixV B) = Nat.card ↥(Vs ⊓ fixV B) ^ 2 := by
  refine card_eq_sq hcap hcup inf_le_left fun v hv w hw => ⟨fun h => ?_, fun ⟨h1, h2⟩ => ?_⟩
  · have hp := fun g (hg : g ∈ B) => fix_parts hcap (hBs hg) (hBa g hg) hv hw (mem_fixV.mp h g hg)
    exact ⟨⟨hv, mem_fixV.mpr fun g hg => (hp g hg).1⟩, ⟨hw, mem_fixV.mpr fun g hg => (hp g hg).2⟩⟩
  · refine mem_fixV.mpr fun g hg => ?_
    rw [map_mul, ← MulAut.mul_apply, hBa g hg, MulAut.mul_apply, mem_fixV.mp h1.2 g hg,
      mem_fixV.mp h2.2 g hg]

theorem card_le_card_mul_fixV [Finite W] (hcap : Vs ⊓ Vs.map a.toMonoidHom = ⊥)
    (hcup : Vs ⊔ Vs.map a.toMonoidHom = ⊤) {B : Subgroup (MulAut W)} (hBs : B ≤ stabSub Vs)
    (hBa : ∀ g ∈ B, g * a = a * g) (hidx : (fixV B).index ≤ Nat.card B ^ 2) :
    Nat.card ↥Vs ≤ Nat.card (autSub B Vs) * Nat.card (fixV (autSub B Vs)) := by
  rw [card_autSub hcup hBs hBa]
  have hfix : Nat.card (fixV (autSub B Vs)) = Nat.card ↥(Vs ⊓ fixV B) := by
    rw [← map_subtype_fixV_autSub hBs, Subgroup.card_map_of_injective Vs.subtype_injective]
  rw [hfix]
  have h1 := (fixV B).card_mul_index
  rw [card_fixV hcap hcup hBs hBa, card_eq hcap hcup] at h1
  have h2 : Nat.card ↥Vs ^ 2 ≤ (Nat.card B * Nat.card ↥(Vs ⊓ fixV B)) ^ 2 := by
    rw [mul_pow, ← h1, mul_comm]
    exact Nat.mul_le_mul_right _ hidx
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h2

end Dec

theorem b4Hyp_autSub {W : Type} [CommGroup W] [Finite W] {M Mp T : Subgroup (MulAut W)}
    {Vs : Subgroup W} (hA21 : AsA21SQTKSection) (hD : D31 M Mp T Mp Vs) (hT : T ≤ stabSub Vs)
    (hfix : Vs ⊓ fixV Mp = ⊥) :
    B4Hyp (autSub (Mp ⊔ T) Vs) (autSub Mp Vs) ∧
      (∀ y ∈ autSub (Mp ⊔ T) Vs, ∃ e : ℕ, y ^ 2 ^ e ∈ autSub Mp Vs) ∧
      (∀ y ∈ autSub (Mp ⊔ T) Vs, ∀ k ∈ autSub Mp Vs, y * k * y⁻¹ ∈ autSub Mp Vs) ∧
      pCoreOf 2 (autSub (Mp ⊔ T) Vs) = ⊥ := by
  have hO2 := lred3_pCoreOf_autSub_sup_eq_bot hD hT
  have hq := lred3_qsec hD rfl hO2
  have hC : (Vs ⊓ fixV Mp).subgroupOf Vs = ⊥ := by rw [hfix, Subgroup.bot_subgroupOf]
  rw [hC] at hq
  refine ⟨⟨hq.sqtkGroup (lred3_sqtk hA21 hD rfl), ?_, hq.quasi, ?_⟩, hq.two, hq.normal, hO2⟩
  · exact (InternalSec.quasithinGenFitting_eq_of_two_pow hq.le hq.normal
      (B1Red.isQuasisimple_to_open hq.quasi) hq.two hO2).symm
  · refine ⟨hq.lt, fun J hJ _ _ => hq.irr J bot_le fun k hk w hw => ?_⟩
    exact hJ ⟨k, hk⟩ w hw

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

namespace Top42

variable {K I : Subgroup G} (C : Top42 T L V H K I) (D : TopW T L V H I)
include C D

variable [IsMulCommutative ↥(conjClosure V H)]

theorem autOf_comm_actS (h1332 : Stmt13_3_2) {B : Subgroup G}
    (hBR : B ≤ pCoreOf 2 (l1 T L V ⊔ T)) {x : ↥H ⧸ CFSG.pCore 2 ↥H}
    (hx : x ∈ modO2Image H (l1 T L V)) :
    ∀ g ∈ D.autOf B, g * D.actS x = D.actS x * g := by
  rintro _ ⟨b, hb, rfl⟩
  obtain ⟨l, hl, rfl⟩ := mem_modO2Image'.mp hx
  rw [D.actS_mk]
  have h2 : D.act (b * l * b⁻¹ * l⁻¹) = 1 := D.act_eq_one_of_mem
    (Setting147.comm_R1_l1 C.S h1332 (C.hHL h1332) (hBR (Subgroup.mem_subgroupOf.mp hb)) hl)
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
  calc D.act b * D.act l = (D.act b * D.act l * (D.act b)⁻¹ * (D.act l)⁻¹) *
      (D.act l * D.act b) := by group
    _ = D.act l * D.act b := by rw [h2, one_mul]

theorem b42 (hB42 : AsB42) (hA21 : AsA21SQTKSection) (h28 : Lemma14_7_28)
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h5 : Lemma14_7_5)
    {n : ℕ} (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K)))
    {x t : ↥H ⧸ CFSG.pCore 2 ↥H} (hx : x ∈ modO2Image H (l1 T L V)) (hx1 : x ≠ 1)
    (ht : t ∈ Subgroup.centralizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)))
    (htx : t * x * t⁻¹ = x⁻¹) {Vs : Subgroup (Hat V H I)}
    (hVs : Vs ∈ IrrPlusOn (D.autOf K) (orbSup (D.autOf T) Vs) (D.autOf T))
    (hst : ∀ g ∈ D.autOf T, g ∈ stabSub Vs) {B : Subgroup G}
    (hB : IsF918B T L (fsuV1 T V) V H (conjClosure K T) B) :
    B4Hyp (autSub (D.autOf K ⊔ D.autOf T) Vs) (autSub (D.autOf K) Vs) ∧
      (∀ y ∈ autSub (D.autOf K ⊔ D.autOf T) Vs, ∃ e : ℕ, y ^ 2 ^ e ∈ autSub (D.autOf K) Vs) ∧
      (∀ y ∈ autSub (D.autOf K ⊔ D.autOf T) Vs, ∀ k ∈ autSub (D.autOf K) Vs,
        y * k * y⁻¹ ∈ autSub (D.autOf K) Vs) ∧
      pCoreOf 2 (autSub (D.autOf K ⊔ D.autOf T) Vs) = ⊥ ∧
      ∃ A, IsFFStarOffender (autSub (D.autOf K ⊔ D.autOf T) Vs) A ∧
        B42Conclusion (autSub (D.autOf K ⊔ D.autOf T) Vs) (autSub (D.autOf K) Vs) A := by
  classical
  have : Finite (MulAut (Hat V H I)) := TopW.finite_mulAut
  have hl1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hBR : B ≤ pCoreOf 2 (l1 T L V ⊔ T) := hl1 ▸ hB.1
  have hBT : B ≤ T := hBR.trans (L32A.pCoreOf_le_of_le C.S.hyp le_sup_right)
  have hfaith := C.faithful D h28 h1222 h1332 h1334 h5 hLie
  have hf : ∀ b ∈ B, (∀ u ∈ conjClosure V H, b * u * b⁻¹ * u⁻¹ ∈ I) → b ∈ pCoreOf 2 H :=
    fun b hb h => hfaith ⟨b, C.hTH (hBT hb)⟩ ((D.act_eq_one_iff_comm _).mpr h)
  have hD31 := D.d31 C.hK C.hKn C.hq (C.autOf_K_ne_bot D)
    (C.pCoreOf_range D h28 h1222 h1332 h1334 h5 hLie) hVs
  have hfix : Vs ⊓ fixV (D.autOf K) = ⊥ := by rw [C.fixV_autOf_K D, inf_bot_eq]
  obtain ⟨hB4, h2, hnorm, hO2⟩ := b4Hyp_autSub hA21 hD31 (fun g hg => hst g hg) hfix
  obtain ⟨-, hcap, hcup⟩ := C.isCompl_of_stab D h28 h1222 h1332 h1334 h5 hLie hx hx1 ht htx
    ⟨le_top, hVs.1.2⟩ hst
  have hBTs : D.autOf B ≤ D.autOf T := Subgroup.map_mono fun y hy => hBT hy
  have hBs : D.autOf B ≤ stabSub Vs := fun g hg => hst g (hBTs hg)
  have hBa := C.autOf_comm_actS D h1332 hBR hx
  have hA2 := D.isA2_autOf hB.2.1 hf
  have hle := Dec.card_le_card_mul_fixV hcap hcup hBs hBa (D.index_fixV_autOf_le hB.2.1 hf)
  have hcard := Dec.card_autSub hcup hBs hBa
  have hFF : IsFFModule (autSub (D.autOf K ⊔ D.autOf T) Vs) := by
    refine ⟨autSub (D.autOf B) Vs, autSub_mono (hBTs.trans le_sup_right) Vs, ?_, ⟨?_, ?_⟩, hle⟩
    · intro h0
      rw [h0, Subgroup.card_bot] at hcard
      exact hA2.2.1 (Subgroup.card_eq_one.mp hcard.symm)
    · intro φ hφ ψ hψ
      obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
      obtain ⟨g', hg', rfl⟩ := mem_autSub.mp hψ
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext (hA2.2.2.1 _ hg _ hg'))
    · intro φ hφ
      obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
      rw [← map_pow]
      have : g ^ 2 = 1 := Subtype.ext (by simpa using hA2.2.2.2 _ hg)
      rw [this, map_one]
  obtain ⟨A, hA⟩ := B6.exists_isFFStarOffender hFF
  have hexp : ∀ v : ↥Vs, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using D.hexp (v : Hat V H I))
  exact ⟨hB4, h2, hnorm, hO2, A, hA, hB42 ↥Vs hexp _ _ hB4 A hA⟩

end Top42

end CFSG.Quasithin.H13.L32A.C
