module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsConj
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

private theorem w16f_stableUnder_le_stabSub {X : Subgroup (MulAut W)} {U : Subgroup W}
    (h : StableUnder X U) : X ≤ stabSub U := by
  intro x hx
  rw [mem_stabSub]
  intro u
  exact ⟨fun hxu => by
    have h1 := h x⁻¹ (X.inv_mem hx) (x u) hxu
    rwa [MulAut.inv_apply_self] at h1, h x hx u⟩

private theorem w16f_stableUnder_of_le_stabSub {X : Subgroup (MulAut W)} {U : Subgroup W}
    (h : X ≤ stabSub U) : StableUnder X U :=
  fun x hx u hu => (mem_stabSub.mp (h hx) u).mpr hu

private theorem w16f_stableUnder_sup {X Y : Subgroup (MulAut W)} {U : Subgroup W}
    (hX : StableUnder X U) (hY : StableUnder Y U) : StableUnder (X ⊔ Y) U :=
  w16f_stableUnder_of_le_stabSub
    (sup_le (w16f_stableUnder_le_stabSub hX) (w16f_stableUnder_le_stabSub hY))

private theorem w16f_map_eq_self_of_mem_stabSub {U : Subgroup W} {g : MulAut W}
    (hg : g ∈ stabSub U) : U.map g.toMonoidHom = U := by
  ext u
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (mem_stabSub.mp hg v).mpr hv
  · intro hu
    exact ⟨g⁻¹ u, (mem_stabSub.mp hg (g⁻¹ u)).mp (by simpa using hu),
      MulEquiv.apply_symm_apply g u⟩

private theorem w16f_mem_stabSub_of_map_eq {U : Subgroup W} {g : MulAut W}
    (h : U.map g.toMonoidHom = U) : g ∈ stabSub U := by
  rw [mem_stabSub]
  intro u
  constructor
  · intro hu
    have hmem : g u ∈ U.map g.toMonoidHom := by rw [h]; exact hu
    obtain ⟨v, hv, hgv⟩ := Subgroup.mem_map.mp hmem
    rwa [g.injective hgv] at hv
  · intro hu
    have : g u ∈ U.map g.toMonoidHom := Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
    rwa [h] at this

private theorem w16f_conj_conj_apply {t : MulAut W} (ht : t * t = 1) (a : MulAut W) :
    MulAut.conj t (MulAut.conj t a) = a := by
  rw [MulAut.conj_apply, MulAut.conj_apply]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rw [htinv]
  calc t * (t * a * t) * t = (t * t) * a * (t * t) := by group
    _ = a := by rw [ht]; simp

private theorem w16f_map_conj_conj {X : Subgroup (MulAut W)} {t : MulAut W}
    (ht : t * t = 1) :
    (X.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = X := by
  rw [Subgroup.map_map]
  have hcomp : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
      MonoidHom.id (MulAut W) := by
    refine MonoidHom.ext fun a => ?_
    exact w16f_conj_conj_apply ht a
  rw [hcomp, Subgroup.map_id]

private theorem w16f_map_map_self {S : Subgroup W} {t : MulAut W} (ht : t * t = 1) :
    (S.map t.toMonoidHom).map t.toMonoidHom = S := by
  rw [Subgroup.map_map]
  have hcomp : t.toMonoidHom.comp t.toMonoidHom = MonoidHom.id W := by
    ext w
    show t (t w) = w
    rw [← MulAut.mul_apply, ht, MulAut.one_apply]
  rw [hcomp, Subgroup.map_id]

private theorem w16f_comm_of_commutator_eq_bot {A B : Subgroup (MulAut W)}
    (h : ⁅A, B⁆ = ⊥) {a b : MulAut W} (ha : a ∈ A) (hb : b ∈ B) : a * b = b * a := by
  have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  have hm : a ∈ Subgroup.centralizer (B : Set (MulAut W)) := hle ha
  exact (Subgroup.mem_centralizer_iff.mp hm b hb).symm

private theorem w16f_mem_conj_of_map_eq {X : Subgroup (MulAut W)} {g x : MulAut W}
    (hX : X.map (MulAut.conj g).toMonoidHom = X) (hx : x ∈ X) : g * x * g⁻¹ ∈ X := by
  have h : MulAut.conj g x ∈ X.map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  rw [hX] at h
  simpa [MulAut.conj_apply] using h

private def w16f_secKer (S C : Subgroup W) : Subgroup (MulAut W) where
  carrier := {g | g ∈ stabSub S ∧ ∀ u ∈ S, g u * u⁻¹ ∈ C}
  one_mem' := ⟨(stabSub S).one_mem, fun u _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨(stabSub S).mul_mem ha1 hb1, fun u hu => ?_⟩
    have hbu : b u ∈ S := (mem_stabSub.mp hb1 u).mpr hu
    have he : (a * b) u * u⁻¹ = (a (b u) * (b u)⁻¹) * (b u * u⁻¹) := by
      rw [MulAut.mul_apply]
      group
    rw [he]
    exact C.mul_mem (ha2 _ hbu) (hb2 u hu)
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨(stabSub S).inv_mem ha1, fun u hu => ?_⟩
    have hu' : a⁻¹ u ∈ S := by
      have h := (mem_stabSub.mp ha1 (a⁻¹ u)).mp
      rw [MulAut.apply_inv_self] at h
      exact h hu
    have h := ha2 _ hu'
    rw [MulAut.apply_inv_self] at h
    have he : a⁻¹ u * u⁻¹ = (u * (a⁻¹ u)⁻¹)⁻¹ := by group
    rw [he]
    exact C.inv_mem h

private theorem w16f_conj_mem_secKer {S C : Subgroup W} {g k : MulAut W}
    (hgS : g ∈ stabSub S) (hgC : ∀ c ∈ C, g c ∈ C) (hk : k ∈ w16f_secKer S C) :
    g * k * g⁻¹ ∈ w16f_secKer S C := by
  obtain ⟨hk1, hk2⟩ := hk
  refine ⟨(stabSub S).mul_mem ((stabSub S).mul_mem hgS hk1) ((stabSub S).inv_mem hgS), ?_⟩
  intro u hu
  have hu' : g⁻¹ u ∈ S := ((mem_stabSub.mp ((stabSub S).inv_mem hgS) u)).mpr hu
  have h := hgC _ (hk2 _ hu')
  have he : g (k (g⁻¹ u) * (g⁻¹ u)⁻¹) = (g * k * g⁻¹) u * u⁻¹ := by
    simp only [map_mul, map_inv, MulAut.mul_apply, MulAut.apply_inv_self]
  rwa [he] at h

private theorem w16f_commSub_le_of_le_secKer {X : Subgroup (MulAut W)} {S C : Subgroup W}
    (hX : X ≤ w16f_secKer S C) : commSub S X ≤ C := by
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨x, hx, u, hu, rfl⟩
  exact (hX hx).2 u hu

private theorem w16f_E_symm {S C : Subgroup W} {x y : MulAut W}
    (h : x * y⁻¹ ∈ w16f_secKer S C) : y * x⁻¹ ∈ w16f_secKer S C := by
  have h' := (w16f_secKer S C).inv_mem h
  simpa [mul_inv_rev] using h'

private theorem w16f_E_trans {S C : Subgroup W} {x y z : MulAut W}
    (h1 : x * y⁻¹ ∈ w16f_secKer S C) (h2 : y * z⁻¹ ∈ w16f_secKer S C) :
    x * z⁻¹ ∈ w16f_secKer S C := by
  have hm := (w16f_secKer S C).mul_mem h1 h2
  have heq : x * y⁻¹ * (y * z⁻¹) = x * z⁻¹ := by group
  rwa [heq] at hm

private theorem w16f_E_mul_right {S C : Subgroup W} {x y : MulAut W}
    (h : x * y⁻¹ ∈ w16f_secKer S C) (z : MulAut W) :
    x * z * (y * z)⁻¹ ∈ w16f_secKer S C := by
  have heq : x * z * (y * z)⁻¹ = x * y⁻¹ := by group
  rwa [heq]

private theorem w16f_E_mul_left {S C : Subgroup W} {x y : MulAut W}
    (h : x * y⁻¹ ∈ w16f_secKer S C) {z : MulAut W}
    (hzS : z ∈ stabSub S) (hzC : ∀ c ∈ C, z c ∈ C) :
    z * x * (z * y)⁻¹ ∈ w16f_secKer S C := by
  have hk := w16f_conj_mem_secKer hzS hzC h
  have heq : z * x * (z * y)⁻¹ = z * (x * y⁻¹) * z⁻¹ := by group
  rwa [heq]

private theorem w16f_commutator_mem_secKer
    {K K' : Subgroup (MulAut W)} {t : MulAut W} {S U₀ : Subgroup W}
    (hKmap : K.map (MulAut.conj t).toMonoidHom = K')
    (hcomm : ⁅K, K'⁆ = ⊥)
    (hSstab : StableUnder (K ⊔ K') S) (hU₀stab : StableUnder (K ⊔ K') U₀)
    (hD : ∀ a ∈ K, a * (t * a * t⁻¹) ∈ w16f_secKer S U₀)
    {a b : MulAut W} (ha : a ∈ K) (hb : b ∈ K) :
    ⁅a, b⁆ ∈ w16f_secKer S U₀ := by
  have hpa : t * a * t⁻¹ ∈ K' := by
    have h : MulAut.conj t a ∈ K' := by
      rw [← hKmap]
      exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply] using h
  have hpb : t * b * t⁻¹ ∈ K' := by
    have h : MulAut.conj t b ∈ K' := by
      rw [← hKmap]
      exact Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
    simpa [MulAut.conj_apply] using h
  have hcomm' : ⁅K', K⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hcomm
  have hpa_inv_b : (t * a * t⁻¹)⁻¹ * b = b * (t * a * t⁻¹)⁻¹ :=
    w16f_comm_of_commutator_eq_bot hcomm' (K'.inv_mem hpa) hb
  have hA : a * ((t * a * t⁻¹)⁻¹)⁻¹ ∈ w16f_secKer S U₀ := by
    simpa using hD a ha
  have hB : b * ((t * b * t⁻¹)⁻¹)⁻¹ ∈ w16f_secKer S U₀ := by
    simpa using hD b hb
  have h1 : a * b * (b * (t * a * t⁻¹)⁻¹)⁻¹ ∈ w16f_secKer S U₀ := by
    have h := w16f_E_mul_right hA b
    rwa [hpa_inv_b] at h
  have h2 : (b * (t * a * t⁻¹)⁻¹) *
      ((t * b * t⁻¹)⁻¹ * (t * a * t⁻¹)⁻¹)⁻¹ ∈ w16f_secKer S U₀ :=
    w16f_E_mul_right hB ((t * a * t⁻¹)⁻¹)
  have h3 : a * b * ((t * b * t⁻¹)⁻¹ * (t * a * t⁻¹)⁻¹)⁻¹ ∈ w16f_secKer S U₀ :=
    w16f_E_trans h1 h2
  have hzS : (t * b * t⁻¹)⁻¹ ∈ stabSub S :=
    (w16f_stableUnder_le_stabSub hSstab) (Subgroup.mem_sup_right (K'.inv_mem hpb))
  have hzC : ∀ c ∈ U₀, (t * b * t⁻¹)⁻¹ c ∈ U₀ :=
    fun c hc => hU₀stab _ (Subgroup.mem_sup_right (K'.inv_mem hpb)) c hc
  have h1' : b * a * ((t * b * t⁻¹)⁻¹ * a)⁻¹ ∈ w16f_secKer S U₀ :=
    w16f_E_mul_right hB a
  have h2' : (t * b * t⁻¹)⁻¹ * a *
      ((t * b * t⁻¹)⁻¹ * (t * a * t⁻¹)⁻¹)⁻¹ ∈ w16f_secKer S U₀ :=
    w16f_E_mul_left hA hzS hzC
  have h3' : b * a * ((t * b * t⁻¹)⁻¹ * (t * a * t⁻¹)⁻¹)⁻¹ ∈ w16f_secKer S U₀ :=
    w16f_E_trans h1' h2'
  have hE : a * b * (b * a)⁻¹ ∈ w16f_secKer S U₀ :=
    w16f_E_trans h3 (w16f_E_symm h3')
  have heq : ⁅a, b⁆ = a * b * (b * a)⁻¹ := by
    rw [commutatorElement_def]
    group
  rwa [heq]

private theorem w16f_K_le_secKer_of_diag
    {K K' : Subgroup (MulAut W)} {t : MulAut W} {S U₀ : Subgroup W}
    (hK : ⁅K, K⁆ = K) (hKmap : K.map (MulAut.conj t).toMonoidHom = K')
    (hcomm : ⁅K, K'⁆ = ⊥)
    (hSstab : StableUnder (K ⊔ K') S) (hU₀stab : StableUnder (K ⊔ K') U₀)
    (hD : ∀ a ∈ K, a * (t * a * t⁻¹) ∈ w16f_secKer S U₀) :
    K ≤ w16f_secKer S U₀ := by
  rw [← hK]
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  exact w16f_commutator_mem_secKer hKmap hcomm hSstab hU₀stab hD ha hb

private theorem w16f_diag_mem_secKer
    {K K' : Subgroup (MulAut W)} {t : MulAut W} (ht2 : t * t = 1)
    (hKmap : K.map (MulAut.conj t).toMonoidHom = K')
    (hcomm : ⁅K, K'⁆ = ⊥)
    (htr : ∀ a ∈ K, ∀ u ∈ commSub ⊤ (Subgroup.zpowers t),
      (a * (t * a * t⁻¹)) u = u)
    {S U₀ : Subgroup W}
    (hSL : StableUnder (K ⊔ K') S)
    (hScap : S ⊓ S.map t.toMonoidHom = U₀)
    {a : MulAut W} (ha : a ∈ K) :
    a * (t * a * t⁻¹) ∈ w16f_secKer S U₀ := by
  have hpaK' : t * a * t⁻¹ ∈ K' := by
    have h : MulAut.conj t a ∈ K' := by
      rw [← hKmap]
      exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply] using h
  have hc : a * (t * a * t⁻¹) = (t * a * t⁻¹) * a :=
    w16f_comm_of_commutator_eq_bot hcomm ha hpaK'
  refine ⟨?_, ?_⟩
  · have hLstab : (K ⊔ K') ≤ stabSub S := w16f_stableUnder_le_stabSub hSL
    exact (stabSub S).mul_mem (hLstab (Subgroup.mem_sup_left ha))
      (hLstab (Subgroup.mem_sup_right hpaK'))
  · intro s hs
    have hdL : a * (t * a * t⁻¹) ∈ K ⊔ K' :=
      (K ⊔ K').mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hpaK')
    have huS : (a * (t * a * t⁻¹)) s * s⁻¹ ∈ S :=
      S.mul_mem (hSL _ hdL s hs) (S.inv_mem hs)
    have hdt : t * (a * (t * a * t⁻¹)) = (a * (t * a * t⁻¹)) * t := by
      have h1 : t * (a * (t * a * t⁻¹)) * t⁻¹ = a * (t * a * t⁻¹) := by
        calc t * (a * (t * a * t⁻¹)) * t⁻¹
            = (t * a * t⁻¹) * (t * (t * a * t⁻¹) * t⁻¹) := by group
          _ = (t * a * t⁻¹) * a := by
                congr 1
                have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
                rw [htinv]
                calc t * (t * a * t) * t = (t * t) * a * (t * t) := by group
                  _ = a := by rw [ht2]; simp
          _ = a * (t * a * t⁻¹) := hc.symm
      exact (mul_inv_eq_iff_eq_mul).mp h1
    have hdes : (a * (t * a * t⁻¹)) (t s * s⁻¹) = t s * s⁻¹ :=
      htr a ha (t s * s⁻¹)
        (Subgroup.subset_closure
          ⟨t, Subgroup.mem_zpowers t, s, Subgroup.mem_top s, rfl⟩)
    have h1' : t ((a * (t * a * t⁻¹)) s) *
        ((a * (t * a * t⁻¹)) s)⁻¹ = t s * s⁻¹ := by
      have h2 : (a * (t * a * t⁻¹)) (t s * s⁻¹) =
          t ((a * (t * a * t⁻¹)) s) * ((a * (t * a * t⁻¹)) s)⁻¹ := by
        rw [map_mul, map_inv]
        congr 1
        show (a * (t * a * t⁻¹)) (t s) = t ((a * (t * a * t⁻¹)) s)
        rw [← MulAut.mul_apply, ← hdt, MulAut.mul_apply]
      rw [← h2, hdes]
    have hfix : t ((a * (t * a * t⁻¹)) s * s⁻¹) =
        (a * (t * a * t⁻¹)) s * s⁻¹ := by
      have hA : t ((a * (t * a * t⁻¹)) s) =
          t s * s⁻¹ * ((a * (t * a * t⁻¹)) s) := by
        calc t ((a * (t * a * t⁻¹)) s)
            = t ((a * (t * a * t⁻¹)) s) * ((a * (t * a * t⁻¹)) s)⁻¹ *
                ((a * (t * a * t⁻¹)) s) := by group
          _ = (t s * s⁻¹) * ((a * (t * a * t⁻¹)) s) := by rw [h1']
      calc t ((a * (t * a * t⁻¹)) s * s⁻¹)
          = t ((a * (t * a * t⁻¹)) s) * (t s)⁻¹ := by rw [map_mul, map_inv]
        _ = (t s * s⁻¹ * ((a * (t * a * t⁻¹)) s)) * (t s)⁻¹ := by rw [hA]
        _ = (t s * (t s)⁻¹) * (((a * (t * a * t⁻¹)) s) * s⁻¹) := by ac_rfl
        _ = ((a * (t * a * t⁻¹)) s) * s⁻¹ := by rw [mul_inv_cancel, one_mul]
    have hutS : (a * (t * a * t⁻¹)) s * s⁻¹ ∈ S.map t.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨_, huS, hfix⟩
    have hmem : (a * (t * a * t⁻¹)) s * s⁻¹ ∈ S ⊓ S.map t.toMonoidHom := ⟨huS, hutS⟩
    rwa [hScap] at hmem

private theorem w16f_commSub_sup (A B : Subgroup W) (X : Subgroup (MulAut W)) :
    commSub (A ⊔ B) X = commSub A X ⊔ commSub B X := by
  refine le_antisymm ?_ ?_
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := Subgroup.mem_sup.mp hw
    have h1 : x (u * v) * (u * v)⁻¹ = (x u * u⁻¹) * (x v * v⁻¹) := by
      rw [map_mul, mul_inv_rev]
      calc x u * x v * (v⁻¹ * u⁻¹)
          = x u * x v * (u⁻¹ * v⁻¹) := by rw [mul_comm (v⁻¹) (u⁻¹)]
        _ = x u * (x v * (u⁻¹ * v⁻¹)) := by rw [mul_assoc]
        _ = x u * (u⁻¹ * (x v * v⁻¹)) := by
              rw [← mul_assoc (x v) (u⁻¹) (v⁻¹), mul_comm (x v) (u⁻¹), mul_assoc]
        _ = (x u * u⁻¹) * (x v * v⁻¹) := by rw [← mul_assoc]
    rw [h1]
    exact (commSub A X ⊔ commSub B X).mul_mem
      (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨x, hx, u, hu, rfl⟩))
      (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨x, hx, v, hv, rfl⟩))
  · exact sup_le (commSub_mono le_sup_left le_rfl) (commSub_mono le_sup_right le_rfl)

theorem swap_chief_isIrr {K : Subgroup (MulAut W)} {t : MulAut W} (hK : ⁅K, K⁆ = K)
    (ht2 : t * t = 1) (hcomm : ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ = ⊥)
    (htr : ∀ a ∈ K, ∀ u ∈ commSub ⊤ (Subgroup.zpowers t), (a * (t * a * t⁻¹)) u = u)
    {U₀ U : Subgroup W}
    (hirr : IsIrrOn (K ⊔ K.map (MulAut.conj t).toMonoidHom ⊔ Subgroup.zpowers t) U U₀)
    (hnt : ¬ commSub U (K ⊔ K.map (MulAut.conj t).toMonoidHom) ≤ U₀) :
    IsIrrOn (K ⊔ K.map (MulAut.conj t).toMonoidHom) U U₀ := by
  classical
  set K' : Subgroup (MulAut W) := K.map (MulAut.conj t).toMonoidHom with hK'def
  obtain ⟨hU₀ltU, hHU, hHU₀, hminH⟩ := hirr
  have hLH : (K ⊔ K') ≤ (K ⊔ K') ⊔ Subgroup.zpowers t := le_sup_left
  have hLU : StableUnder (K ⊔ K') U := fun x hx => hHU x (hLH hx)
  have hLU₀ : StableUnder (K ⊔ K') U₀ := fun x hx => hHU₀ x (hLH hx)
  have htH : t ∈ (K ⊔ K') ⊔ Subgroup.zpowers t :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have htU : t ∈ stabSub U := (w16f_stableUnder_le_stabSub hHU) htH
  have htU₀ : t ∈ stabSub U₀ := (w16f_stableUnder_le_stabSub hHU₀) htH
  have hUmap : U.map t.toMonoidHom = U := w16f_map_eq_self_of_mem_stabSub htU
  have hU₀map : U₀.map t.toMonoidHom = U₀ := w16f_map_eq_self_of_mem_stabSub htU₀
  have hLmap : (K ⊔ K').map (MulAut.conj t).toMonoidHom = K ⊔ K' := by
    change (K ⊔ K.map (MulAut.conj t).toMonoidHom).map
        (MulAut.conj t).toMonoidHom = K ⊔ K.map (MulAut.conj t).toMonoidHom
    rw [Subgroup.map_sup, w16f_map_conj_conj (X := K) ht2, sup_comm]
  refine ⟨hU₀ltU, hLU, hLU₀, ?_⟩
  intro J hJstab hU₀J hJU
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hJne₀, hJneU⟩ := hcon
  obtain ⟨S, hS, hSmin⟩ := Set.exists_min_image
    {S : Subgroup W | StableUnder (K ⊔ K') S ∧ U₀ ≤ S ∧ S ≤ U ∧ S ≠ U₀ ∧ S ≠ U}
    (fun S => Nat.card S) (Set.toFinite _) ⟨J, hJstab, hU₀J, hJU, hJne₀, hJneU⟩
  obtain ⟨hSstab, hU₀S, hSU, hSne₀, hSneU⟩ := hS
  have ht_norm : ∀ x ∈ K ⊔ K', t * x * t⁻¹ ∈ K ⊔ K' :=
    fun x hx => w16f_mem_conj_of_map_eq hLmap hx
  have ht_norm' : ∀ x ∈ K ⊔ K', t⁻¹ * x * t ∈ K ⊔ K' := by
    intro x hx
    simpa only [inv_eq_of_mul_eq_one_right ht2] using ht_norm x hx
  have htSstab : StableUnder (K ⊔ K') (S.map t.toMonoidHom) :=
    stableUnder_map_of_normalizes ht_norm' hSstab
  have hU₀tS : U₀ ≤ S.map t.toMonoidHom := by
    rw [← hU₀map]
    exact Subgroup.map_mono hU₀S
  have htSU : S.map t.toMonoidHom ≤ U := by
    have h := Subgroup.map_mono (f := t.toMonoidHom) hSU
    rwa [hUmap] at h
  have htSne₀ : S.map t.toMonoidHom ≠ U₀ := by
    intro h
    apply hSne₀
    calc S = (S.map t.toMonoidHom).map t.toMonoidHom :=
          (w16f_map_map_self (S := S) ht2).symm
      _ = U₀.map t.toMonoidHom := by rw [h]
      _ = U₀ := hU₀map
  have htSneU : S.map t.toMonoidHom ≠ U := by
    intro h
    apply hSneU
    calc S = (S.map t.toMonoidHom).map t.toMonoidHom :=
          (w16f_map_map_self (S := S) ht2).symm
      _ = U.map t.toMonoidHom := by rw [h]
      _ = U := hUmap
  have hSltU : S < U := lt_of_le_of_ne hSU hSneU
  have hSne_tS : S ≠ S.map t.toMonoidHom := by
    intro h
    have htS_stab : StableUnder (Subgroup.zpowers t) S := by
      refine w16f_stableUnder_of_le_stabSub (Subgroup.zpowers_le.mpr ?_)
      refine w16f_mem_stabSub_of_map_eq ?_
      rw [← h]
    have hSH : StableUnder ((K ⊔ K') ⊔ Subgroup.zpowers t) S :=
      w16f_stableUnder_sup hSstab htS_stab
    rcases hminH S hSH hU₀S hSU with h0 | hU
    · exact hSne₀ h0
    · exact hSneU hU
  have hSinf : S ⊓ S.map t.toMonoidHom = U₀ := by
    by_contra hne
    have hmem : S ⊓ S.map t.toMonoidHom ∈
        {S : Subgroup W | StableUnder (K ⊔ K') S ∧ U₀ ≤ S ∧ S ≤ U ∧ S ≠ U₀ ∧ S ≠ U} :=
      ⟨stableUnder_inf hSstab htSstab, le_inf hU₀S hU₀tS, inf_le_left.trans hSU, hne,
        ne_of_lt (lt_of_le_of_lt inf_le_left hSltU)⟩
    have hcard := hSmin _ hmem
    have hle : S ⊓ S.map t.toMonoidHom ≤ S := inf_le_left
    have heq : S ⊓ S.map t.toMonoidHom = S := Subgroup.eq_of_le_of_card_ge hle hcard
    have hSle : S ≤ S.map t.toMonoidHom := inf_eq_left.mp heq
    have hcard_eq : Nat.card (S.map t.toMonoidHom) ≤ Nat.card S := by
      rw [Subgroup.card_map_of_injective t.injective]
    exact hSne_tS (Subgroup.eq_of_le_of_card_ge hSle hcard_eq)
  have ht_map_sup : (S ⊔ S.map t.toMonoidHom).map t.toMonoidHom =
      S ⊔ S.map t.toMonoidHom := by
    rw [Subgroup.map_sup, w16f_map_map_self (S := S) ht2]
    exact sup_comm _ _
  have ht_stab_sup : t ∈ stabSub (S ⊔ S.map t.toMonoidHom) :=
    w16f_mem_stabSub_of_map_eq ht_map_sup
  have hZsup : StableUnder (Subgroup.zpowers t) (S ⊔ S.map t.toMonoidHom) :=
    w16f_stableUnder_of_le_stabSub (Subgroup.zpowers_le.mpr ht_stab_sup)
  have hHstab : StableUnder ((K ⊔ K') ⊔ Subgroup.zpowers t) (S ⊔ S.map t.toMonoidHom) :=
    w16f_stableUnder_sup (stableUnder_sup hSstab htSstab) hZsup
  have hSsup : S ⊔ S.map t.toMonoidHom = U := by
    rcases hminH (S ⊔ S.map t.toMonoidHom) hHstab (hU₀S.trans le_sup_left)
      (sup_le hSU htSU) with h | h
    · exfalso
      exact hSne₀ (le_antisymm (h ▸ le_sup_left) hU₀S)
    · exact h
  have hD : ∀ a ∈ K, a * (t * a * t⁻¹) ∈ w16f_secKer S U₀ :=
    fun a ha => w16f_diag_mem_secKer ht2 hK'def.symm hcomm htr hSstab hSinf ha
  have hKle : K ≤ w16f_secKer S U₀ :=
    w16f_K_le_secKer_of_diag hK hK'def.symm hcomm hSstab hLU₀ hD
  have hK'le : K' ≤ w16f_secKer S U₀ := by
    intro x hx
    rw [hK'def] at hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    have hpa : t * a * t⁻¹ ∈ K ⊔ K' :=
      Subgroup.mem_sup_right (by rw [hK'def]; exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
    refine ⟨(w16f_stableUnder_le_stabSub hSstab) hpa, fun s hs => ?_⟩
    have h1 : a ((t * a * t⁻¹) s) * s⁻¹ ∈ U₀ := (hD a ha).2 s hs
    have h2 : a ((t * a * t⁻¹) s) * ((t * a * t⁻¹) s)⁻¹ ∈ U₀ :=
      (hKle ha).2 ((t * a * t⁻¹) s) (hSstab _ hpa s hs)
    have h3 : ((t * a * t⁻¹) s) * s⁻¹ ∈ U₀ := by
      have hm := U₀.mul_mem h1 (U₀.inv_mem h2)
      have heq : a ((t * a * t⁻¹) s) * s⁻¹ *
          (a ((t * a * t⁻¹) s) * ((t * a * t⁻¹) s)⁻¹)⁻¹ =
          ((t * a * t⁻¹) s) * s⁻¹ := by
        rw [mul_inv_rev, inv_inv]
        calc a ((t * a * t⁻¹) s) * s⁻¹ *
              (((t * a * t⁻¹) s) * (a ((t * a * t⁻¹) s))⁻¹)
            = (a ((t * a * t⁻¹) s) * (a ((t * a * t⁻¹) s))⁻¹) *
                (((t * a * t⁻¹) s) * s⁻¹) := by ac_rfl
          _ = ((t * a * t⁻¹) s) * s⁻¹ := by rw [mul_inv_cancel, one_mul]
      rwa [heq] at hm
    exact h3
  have hLsec : K ⊔ K' ≤ w16f_secKer S U₀ := sup_le hKle hK'le
  have hScommSub : commSub S (K ⊔ K') ≤ U₀ := w16f_commSub_le_of_le_secKer hLsec
  have htScommSub : commSub (S.map t.toMonoidHom) (K ⊔ K') ≤ U₀ := by
    have heq : commSub (S.map t.toMonoidHom) (K ⊔ K') =
        (commSub S (K ⊔ K')).map t.toMonoidHom :=
      commSub_map_of_normalizes ht_norm ht_norm' S
    rw [heq]
    calc (commSub S (K ⊔ K')).map t.toMonoidHom ≤ U₀.map t.toMonoidHom :=
          Subgroup.map_mono hScommSub
      _ = U₀ := hU₀map
  have hUcommSub : commSub U (K ⊔ K') ≤ U₀ := by
    rw [← hSsup, w16f_commSub_sup]
    exact sup_le hScommSub htScommSub
  exact hnt hUcommSub

end CFSG.LocalAnalysis.WeakClosure81
