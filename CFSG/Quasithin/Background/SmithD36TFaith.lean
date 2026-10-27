module

public import CFSG.Quasithin.Background.SmithD36TLift
public import CFSG.Quasithin.Background.InternalSecIrr

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Perfect

variable {W : Type} [CommGroup W]

theorem fix_of_comm_le_fixV {L : Subgroup (MulAut W)} (hL : Group.IsPerfect ↥L) {J : Subgroup W}
    (hJ : ∀ l ∈ L, ∀ w ∈ J, l w * w⁻¹ ∈ fixV L) : ∀ l ∈ L, ∀ w ∈ J, l w = w := by
  intro l hl w hw
  let φ : ↥L →* W :=
    { toFun := fun k => (k : MulAut W) w * w⁻¹
      map_one' := by simp
      map_mul' := fun k₁ k₂ => by
        have hc : (k₁ : MulAut W) ((k₂ : MulAut W) w * w⁻¹) = (k₂ : MulAut W) w * w⁻¹ :=
          hJ k₂ k₂.2 w hw k₁ k₁.2
        have e : (k₂ : MulAut W) w = ((k₂ : MulAut W) w * w⁻¹) * w := by
          rw [inv_mul_cancel_right]
        show (k₁ : MulAut W) ((k₂ : MulAut W) w) * w⁻¹ = _
        conv_lhs => rw [e, map_mul, hc]
        rw [mul_comm ((k₁ : MulAut W) w * w⁻¹)]
        group }
  have hker : commutator ↥L ≤ φ.ker := Abelianization.commutator_subset_ker φ
  rw [hL.commutator_eq_top] at hker
  have h := hker (Subgroup.mem_top ⟨l, hl⟩)
  rw [MonoidHom.mem_ker] at h
  exact mul_inv_eq_one.mp h

end Perfect

section Simple

variable {W : Type} [CommGroup W]

theorem inf_centSub_eq_bot_of_simple {L : Subgroup (MulAut W)} [IsSimpleGroup ↥L]
    {Y : Subgroup W} (hLY : L ≤ stabSub Y) (hne : ∃ l ∈ L, ∃ w ∈ Y, l w ≠ w) :
    L ⊓ centSub Y = ⊥ := by
  have hN : ((L ⊓ centSub Y).subgroupOf L).Normal := by
    refine ⟨fun c hc k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    refine ⟨L.mul_mem (L.mul_mem k.2 hc.1) (L.inv_mem k.2), fun w hw => ?_⟩
    have hkw : (k : MulAut W)⁻¹ w ∈ Y := ((stabSub Y).inv_mem (hLY k.2) w).mpr hw
    show (k : MulAut W) ((c : MulAut W) ((k : MulAut W)⁻¹ w)) = w
    rw [hc.2 _ hkw]
    simp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((L ⊓ centSub Y).subgroupOf L) with h | h
  · rw [eq_bot_iff]
    intro g hg
    have : (⟨g, hg.1⟩ : ↥L) ∈ (L ⊓ centSub Y).subgroupOf L := Subgroup.mem_subgroupOf.mpr hg
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  · exfalso
    obtain ⟨l, hl, w, hw, hlw⟩ := hne
    have : (⟨l, hl⟩ : ↥L) ∈ (L ⊓ centSub Y).subgroupOf L := h ▸ Subgroup.mem_top _
    exact hlw ((Subgroup.mem_subgroupOf.mp this).2 w hw)

theorem eq_one_of_forall_commute_of_simple {L : Subgroup (MulAut W)} [IsSimpleGroup ↥L]
    (hq : CFSG.IsQuasisimple ↥L) {l : MulAut W} (hl : l ∈ L)
    (hc : ∀ k ∈ L, l * k = k * l) : l = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with h | h
  · have hmem : (⟨l, hl⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro k
      exact Subtype.ext (hc k k.2).symm
    rw [h, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exfalso
    obtain ⟨a, b, hab⟩ := InternalSec.exists_noncomm_of_isQuasisimple hq
    exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)

end Simple

section Norm

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

theorem d36t_exists_ne (n : D36Norm M Mp T L V t) : ∃ l ∈ L, ∃ v ∈ V, l v ≠ v := by
  by_contra hcon
  push Not at hcon
  obtain ⟨-, -, hlt, -⟩ := mem_irrPlus_top_iff.mp n.std.hyp.irr
  apply hlt.not_ge
  intro v hv
  refine ⟨hv, ?_⟩
  have hle : Mp ≤ centSub V := by
    rw [n.Mp_eq]
    exact sup_le (fun l hl w hw => hcon l hl w hw) (fun l hl w hw => n.triv w hw l hl)
  exact fun m hm => hle hm v hv

theorem d36t_V_not_le_fixV (n : D36Norm M Mp T L V t) : ¬ V ≤ fixV L := by
  intro h
  obtain ⟨l, hl, v, hv, hlv⟩ := d36t_exists_ne n
  exact hlv (h hv l hl)

theorem d36t_L_inv_Vs (n : D36Norm M Mp T L V t) {s : MulAut W}
    (hsN : s ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    ∀ l ∈ L, ∀ w ∈ V.map s.toMonoidHom, l w ∈ V.map s.toMonoidHom := by
  rintro l hl _ ⟨v, hv, rfl⟩
  have h1 : s⁻¹ * l * s ∈ L := (Subgroup.mem_normalizer_iff''.mp hsN l).mp hl
  refine ⟨(s⁻¹ * l * s) v, d36t_inv_V n (d36t_L_le_Mp n h1) hv, ?_⟩
  simp [MulAut.mul_apply]

theorem d36t_Vs_not_le_fixV (n : D36Norm M Mp T L V t) {s : MulAut W}
    (hsN : s ∈ Subgroup.normalizer (L : Set (MulAut W))) : ¬ V.map s.toMonoidHom ≤ fixV L := by
  intro h
  apply d36t_V_not_le_fixV n
  intro v hv l hl
  have h1 : s * l * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hsN l).mp hl
  have h2 := h ⟨v, hv, rfl⟩ _ h1
  have : s (l v) = s v := by simpa [MulAut.mul_apply] using h2
  exact s.injective this

theorem d36t_commute_of_triv [IsSimpleGroup ↥L] (n : D36Norm M Mp T L V t) {x : MulAut W}
    (hxN : x ∈ Subgroup.normalizer (L : Set (MulAut W))) {s : MulAut W}
    (hsN : s ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (htriv : ∀ w ∈ V.map s.toMonoidHom, x w * w⁻¹ ∈ fixV L) : ∀ l ∈ L, x * l = l * x := by
  have hperf : Group.IsPerfect ↥L := n.std.hyp.quasi.1
  have hinv := d36t_L_inv_Vs n hsN
  let N : Subgroup ↥L :=
    { carrier := {k | ∀ w ∈ V.map s.toMonoidHom, (k : MulAut W) w * w⁻¹ ∈ fixV L}
      one_mem' := fun w _ => by simp [(fixV L).one_mem]
      mul_mem' := fun {a b} ha hb w hw => by
        have e : (a * b : ↥L).1 w * w⁻¹ =
            ((a : MulAut W) ((b : MulAut W) w) * ((b : MulAut W) w)⁻¹) *
              ((b : MulAut W) w * w⁻¹) := by
          show (a : MulAut W) ((b : MulAut W) w) * w⁻¹ = _
          group
        rw [e]
        exact (fixV L).mul_mem (ha _ (hinv _ b.2 w hw)) (hb w hw)
      inv_mem' := fun {a} ha w hw => by
        have hw' : (a : MulAut W)⁻¹ w ∈ V.map s.toMonoidHom := hinv _ (L.inv_mem a.2) w hw
        have h1 := ha _ hw'
        have e : (a⁻¹ : ↥L).1 w * w⁻¹ =
            ((a : MulAut W) ((a : MulAut W)⁻¹ w) * ((a : MulAut W)⁻¹ w)⁻¹)⁻¹ := by
          show (a : MulAut W)⁻¹ w * w⁻¹ = _
          simp
        rw [e]
        exact (fixV L).inv_mem h1 }
  have hNn : N.Normal := by
    refine ⟨fun k hk l w hw => ?_⟩
    have hw' : (l : MulAut W)⁻¹ w ∈ V.map s.toMonoidHom := hinv _ (L.inv_mem l.2) w hw
    have h1 := hk _ hw'
    have e : (l * k * l⁻¹ : ↥L).1 w * w⁻¹ =
        (l : MulAut W) ((k : MulAut W) ((l : MulAut W)⁻¹ w) * ((l : MulAut W)⁻¹ w)⁻¹) := by
      show (l : MulAut W) ((k : MulAut W) ((l : MulAut W)⁻¹ w)) * w⁻¹ = _
      simp [map_mul, map_inv]
    rw [e, h1 l l.2]
    exact h1
  have hNbot : N = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · exfalso
      apply d36t_Vs_not_le_fixV n hsN
      intro w hw l hl
      have hall : ∀ l ∈ L, ∀ w ∈ V.map s.toMonoidHom, l w * w⁻¹ ∈ fixV L := by
        intro l hl w hw
        have : (⟨l, hl⟩ : ↥L) ∈ N := h ▸ Subgroup.mem_top _
        exact this w hw
      exact fix_of_comm_le_fixV hperf hall l hl w hw
  intro l hl
  have hl1 : x * l * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hxN l).mp hl
  have hk : (⟨x * l * x⁻¹, hl1⟩ * ⟨l, hl⟩⁻¹ : ↥L) ∈ N := by
    intro w hw
    have hw' : l⁻¹ w ∈ V.map s.toMonoidHom := hinv _ (L.inv_mem hl) w hw
    have hlw : l (l⁻¹ w) = w := by simp
    have h1 := htriv (l⁻¹ w) hw'
    have h2 := htriv w hw
    set w' := l⁻¹ w with hw'def
    set c := x w' * w'⁻¹ with hc
    have hxw : x w' = c * w' := by rw [hc, inv_mul_cancel_right]
    have h4 : (x * l * x⁻¹) c = c := h1 _ hl1
    have h3 : x w = c * (x * l * x⁻¹) w' := by
      have e1 : x w = (x * l * x⁻¹) (x w') := by
        rw [← hlw]
        simp [MulAut.mul_apply]
      rw [e1, hxw, map_mul, h4]
    have e : (⟨x * l * x⁻¹, hl1⟩ * ⟨l, hl⟩⁻¹ : ↥L).1 w * w⁻¹ = c⁻¹ * (x w * w⁻¹) := by
      show (x * l * x⁻¹) w' * w⁻¹ = _
      rw [h3]
      group
    rw [e]
    exact (fixV L).mul_mem ((fixV L).inv_mem h1) h2
  rw [hNbot, Subgroup.mem_bot] at hk
  have h5 : x * l * x⁻¹ * l⁻¹ = 1 := congrArg Subtype.val hk
  calc x * l = (x * l * x⁻¹ * l⁻¹) * (l * x) := by group
    _ = l * x := by rw [h5, one_mul]

end Norm

section Center

theorem mul_pow_mem_d36t {G : Type*} [Group G] {K : Subgroup G} {k σ : G} (hk : k ∈ K)
    (hσ : σ ∈ Subgroup.normalizer (K : Set G)) (n : ℕ) : ∃ k' ∈ K, (k * σ) ^ n = k' * σ ^ n := by
  induction n with
  | zero => exact ⟨1, K.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨k', hk', hn⟩ := ih
    have hσn : σ ^ n ∈ Subgroup.normalizer (K : Set G) := Subgroup.pow_mem _ hσ n
    have hc : σ ^ n * k * (σ ^ n)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hσn k).mp hk
    refine ⟨k' * (σ ^ n * k * (σ ^ n)⁻¹), K.mul_mem hk' hc, ?_⟩
    rw [pow_succ, hn]
    group

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

omit [Finite W] in
theorem eq_one_of_commute_resHom {K : Subgroup (MulAut W)} [IsSimpleGroup ↥K]
    (hq : CFSG.IsQuasisimple ↥K) {Y : Subgroup W} (hKY : K ≤ stabSub Y)
    (hne : ∃ k ∈ K, ∃ w ∈ Y, k w ≠ w) {l : MulAut W} (hl : l ∈ K)
    (hc : ∀ k (hk : k ∈ K), resHom Y ⟨l, hKY hl⟩ * resHom Y ⟨k, hKY hk⟩ =
      resHom Y ⟨k, hKY hk⟩ * resHom Y ⟨l, hKY hl⟩) : l = 1 := by
  have hKf := inf_centSub_eq_bot_of_simple hKY hne
  refine eq_one_of_forall_commute_of_simple hq hl fun k hk => ?_
  have h1 := hc k hk
  rw [← map_mul, ← map_mul] at h1
  have hmem : l * k * (k * l)⁻¹ ∈ K ⊓ centSub Y := by
    refine ⟨K.mul_mem (K.mul_mem hl hk) (K.inv_mem (K.mul_mem hk hl)), fun w hw => ?_⟩
    have hw' : (k * l)⁻¹ w ∈ Y := ((stabSub Y).inv_mem (hKY (K.mul_mem hk hl)) w).mpr hw
    have h2 := congrArg (fun φ : MulAut ↥Y => ((φ ⟨(k * l)⁻¹ w, hw'⟩ : ↥Y) : W)) h1
    simp only [resHom_apply] at h2
    show (l * k) ((k * l)⁻¹ w) = w
    have h3 : (k * l) ((k * l)⁻¹ w) = w := by simp
    exact h2.trans h3
  rw [hKf, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  exact hmem

theorem d36t_center_trivial [IsSimpleGroup ↥L] (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    ∀ p ∈ autSub Mp (orbSup T V), (∀ q ∈ autSub Mp (orbSup T V), p * q = q * p) → p = 1 := by
  intro p hp hc
  obtain ⟨m, hmMp, rfl⟩ := mem_autSub.mp hp
  have hMpS := d36t_Mp_le_stab_orbSup n
  have hLVT : L ≤ stabSub (orbSup T V) := (d36t_L_le_Mp n).trans hMpS
  have hLtVT : conjAutSub t L ≤ stabSub (orbSup T V) := (d36t_Lt_le_Mp n).trans hMpS
  have hq : CFSG.IsQuasisimple ↥L := n.std.hyp.quasi
  have hneL : ∃ l ∈ L, ∃ w ∈ orbSup T V, l w ≠ w := by
    obtain ⟨l, hl, v, hv, h⟩ := d36t_exists_ne n
    exact ⟨l, hl, v, le_orbSup T V hv, h⟩
  let e : ↥L ≃* ↥(conjAutSub t L) :=
    L.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective
  have : IsSimpleGroup ↥(conjAutSub t L) := e.symm.isSimpleGroup
  have hqt : CFSG.IsQuasisimple ↥(conjAutSub t L) := CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq
  have hneLt : ∃ l ∈ conjAutSub t L, ∃ w ∈ orbSup T V, l w ≠ w := by
    obtain ⟨l, hl, w, hw, h⟩ := hneL
    refine ⟨t * l * t⁻¹, mem_conjAutSub_iff.mpr (by simpa [mul_assoc] using hl), t w,
      mem_orbSup_of_mem_map n.tT hw, fun h' => h ?_⟩
    have : t (l w) = t w := by simpa [MulAut.mul_apply] using h'
    exact t.injective this
  have hLtN : conjAutSub t L ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (d36t_Lt_le_centralizer hL38 n).trans (Subgroup.centralizer_le_normalizer _)
  have hm' : (m : MulAut W) ∈ ((L ⊔ conjAutSub t L : Subgroup (MulAut W)) : Set (MulAut W)) := by
    rw [← n.Mp_eq]
    exact hmMp
  rw [Subgroup.coe_mul_of_right_le_normalizer_left L (conjAutSub t L) hLtN] at hm'
  obtain ⟨l, hl, l', hl', hll'⟩ := hm'
  have hmeq : m = ⟨l, hLVT hl⟩ * ⟨l', hLtVT hl'⟩ := Subtype.ext hll'.symm
  have hcomm : ∀ k ∈ L, l' * k = k * l' := fun k hk =>
    ((Subgroup.mem_centralizer_iff.mp (d36t_Lt_le_centralizer hL38 n hl')) k hk).symm
  have hres : ∀ k (hk : k ∈ Mp), resHom (orbSup T V) ⟨k, hMpS hk⟩ ∈ autSub Mp (orbSup T V) :=
    fun k hk => mem_autSub.mpr ⟨⟨k, hMpS hk⟩, hk, rfl⟩
  have hl1 : l = 1 := by
    refine eq_one_of_commute_resHom hq hLVT hneL hl fun k hk => ?_
    have h1 := hc _ (hres k (d36t_L_le_Mp n hk))
    have h2 : resHom (orbSup T V) ⟨l', hLtVT hl'⟩ * resHom (orbSup T V) ⟨k, hLVT hk⟩ =
        resHom (orbSup T V) ⟨k, hLVT hk⟩ * resHom (orbSup T V) ⟨l', hLtVT hl'⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcomm k hk)
    rw [hmeq, map_mul] at h1
    have h3 : resHom (orbSup T V) ⟨l, hLVT hl⟩ * resHom (orbSup T V) ⟨k, hLVT hk⟩ *
        resHom (orbSup T V) ⟨l', hLtVT hl'⟩ =
        resHom (orbSup T V) ⟨k, hLVT hk⟩ * resHom (orbSup T V) ⟨l, hLVT hl⟩ *
        resHom (orbSup T V) ⟨l', hLtVT hl'⟩ := by
      rw [mul_assoc, ← h2, ← mul_assoc, h1, mul_assoc]
    exact mul_right_cancel h3
  subst hl1
  have hl'1 : l' = 1 := by
    refine eq_one_of_commute_resHom hqt hLtVT hneLt hl' fun k hk => ?_
    have h1 := hc _ (hres k (d36t_Lt_le_Mp n hk))
    have hm1 : m = ⟨l', hLtVT hl'⟩ := by rw [hmeq]; exact Subtype.ext (one_mul _)
    rw [hm1] at h1
    exact h1
  have hm1 : m = 1 := Subtype.ext (by rw [← hll', hl'1]; simp)
  rw [hm1, map_one]

theorem d36t_centralizer_trivial [IsSimpleGroup ↥L] (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    ∀ h ∈ autSub (Mp ⊔ T) (orbSup T V),
      (∀ p ∈ autSub Mp (orbSup T V), h * p = p * h) → h = 1 := by
  have hZ := d36t_center_trivial hL38 n
  have hNM := d36t_sup_le_normalizer n
  have hPn : ∀ h ∈ autSub (Mp ⊔ T) (orbSup T V), ∀ p ∈ autSub Mp (orbSup T V),
      h⁻¹ * p * h ∈ autSub Mp (orbSup T V) := by
    intro h hh p hp
    obtain ⟨z, hzX, rfl⟩ := mem_autSub.mp hh
    obtain ⟨m, hm, rfl⟩ := mem_autSub.mp hp
    refine mem_autSub.mpr ⟨z⁻¹ * m * z, ?_, by rw [map_mul, map_mul, map_inv]⟩
    show (z : MulAut W)⁻¹ * (m : MulAut W) * (z : MulAut W) ∈ Mp
    exact (Subgroup.mem_normalizer_iff''.mp (hNM hzX) m).mp hm
  let K : Subgroup (MulAut ↥(orbSup T V)) :=
    autSub (Mp ⊔ T) (orbSup T V) ⊓
      Subgroup.centralizer (autSub Mp (orbSup T V) : Set (MulAut ↥(orbSup T V)))
  have hKX : K ≤ autSub (Mp ⊔ T) (orbSup T V) := inf_le_left
  have hconj : ∀ h ∈ autSub (Mp ⊔ T) (orbSup T V), ∀ k ∈ K, h * k * h⁻¹ ∈ K := by
    intro h hh k hk
    refine ⟨(autSub (Mp ⊔ T) (orbSup T V)).mul_mem
      ((autSub (Mp ⊔ T) (orbSup T V)).mul_mem hh hk.1)
        ((autSub (Mp ⊔ T) (orbSup T V)).inv_mem hh), Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro p hp
    have hq := (Subgroup.mem_centralizer_iff.mp hk.2) _ (hPn h hh p hp)
    calc p * (h * k * h⁻¹) = h * ((h⁻¹ * p * h) * k) * h⁻¹ := by group
      _ = h * (k * (h⁻¹ * p * h)) * h⁻¹ := by rw [hq]
      _ = h * k * h⁻¹ * p := by group
  have hnorm : autSub (Mp ⊔ T) (orbSup T V) ≤ Subgroup.normalizer (K : Set _) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨hconj h hh k, fun hk => ?_⟩
    have h1 := hconj h⁻¹ ((autSub (Mp ⊔ T) (orbSup T V)).inv_mem hh) _ hk
    have e : h⁻¹ * (h * k * h⁻¹) * h⁻¹⁻¹ = k := by group
    rwa [e] at h1
  have hK2 : IsPGroup 2 ↥K := by
    intro k
    obtain ⟨z, hzX, hz⟩ := mem_autSub.mp k.2.1
    have hz' : (z : MulAut W) ∈ ((Mp ⊔ T : Subgroup (MulAut W)) : Set (MulAut W)) := hzX
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Mp T (d36t_T_le_normalizer n)] at hz'
    obtain ⟨m, hm, s, hs, hms⟩ := hz'
    obtain ⟨e, he⟩ := (n.std.hyp.sylow.2.1 : IsPGroup 2 ↥T) ⟨s, hs⟩
    have he' : s ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
    obtain ⟨m', hm', hpow⟩ :=
      mul_pow_mem_d36t hm (d36t_T_le_normalizer n hs) (2 ^ e)
    rw [he', mul_one] at hpow
    refine ⟨e, Subtype.ext ?_⟩
    have hkpow : ((k ^ 2 ^ e : ↥K) : MulAut ↥(orbSup T V)) ∈ autSub Mp (orbSup T V) := by
      rw [Subgroup.coe_pow, ← hz, ← map_pow]
      refine mem_autSub.mpr ⟨z ^ 2 ^ e, ?_, rfl⟩
      rw [Subgroup.coe_pow, ← hms, hpow]
      exact hm'
    refine hZ _ hkpow fun q hq => ?_
    exact ((Subgroup.mem_centralizer_iff.mp (k ^ 2 ^ e).2.2) q hq).symm
  have hKO := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hKX hnorm hK2
  rw [d36_pCoreOf_eq_bot hL38 n] at hKO
  intro h hh hc
  have hK : h ∈ K := ⟨hh, Subgroup.mem_centralizer_iff.mpr fun p hp => (hc p hp).symm⟩
  exact Subgroup.mem_bot.mp (hKO hK)

theorem d36t_not_triv [IsSimpleGroup ↥L] (hL38 : D3L38) (n : D36Norm M Mp T L V t)
    (x y : ↥(stabSub (orbSup T V))) (hxX : (x : MulAut W) ∈ Mp ⊔ T)
    (hg1 : resHom (orbSup T V) x ≠ 1)
    (hxy : resHom (orbSup T V) x * resHom (orbSup T V) y =
      resHom (orbSup T V) y * resHom (orbSup T V) x)
    (hxN : (x : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hyL : conjAutSub (y : MulAut W) L = conjAutSub t L) {s : MulAut W}
    (hsN : s ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    ¬ ∀ w ∈ V.map s.toMonoidHom, (x : MulAut W) w * w⁻¹ ∈ fixV L := by
  intro htriv
  have hxc := d36t_commute_of_triv n hxN hsN htriv
  have hMpS := d36t_Mp_le_stab_orbSup n
  apply hg1
  refine d36t_centralizer_trivial hL38 n _ (mem_autSub.mpr ⟨x, hxX, rfl⟩) ?_
  let S : Subgroup (MulAut W) :=
    ((Subgroup.centralizer {resHom (orbSup T V) x}).comap (resHom (orbSup T V))).map
      (stabSub (orbSup T V)).subtype
  have hmemS : ∀ k (hk : k ∈ stabSub (orbSup T V)),
      resHom (orbSup T V) x * resHom (orbSup T V) ⟨k, hk⟩ =
        resHom (orbSup T V) ⟨k, hk⟩ * resHom (orbSup T V) x → k ∈ S := by
    intro k hk h
    exact ⟨⟨k, hk⟩, Subgroup.mem_comap.mpr (Subgroup.mem_centralizer_singleton_iff.mpr h.symm),
      rfl⟩
  have hLS : L ≤ S := by
    intro l hl
    refine hmemS l (hMpS (d36t_L_le_Mp n hl)) ?_
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hxc l hl)
  have hLtS : conjAutSub t L ≤ S := by
    intro l' hl'
    have hb : (y : MulAut W)⁻¹ * l' * y ∈ L := by
      rw [← hyL] at hl'
      exact mem_conjAutSub_iff.mp hl'
    have hl'S := hMpS (d36t_Lt_le_Mp n hl')
    have hbS := hMpS (d36t_L_le_Mp n hb)
    refine hmemS l' hl'S ?_
    have h1 : resHom (orbSup T V) x * resHom (orbSup T V) ⟨_, hbS⟩ =
        resHom (orbSup T V) ⟨_, hbS⟩ * resHom (orbSup T V) x := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hxc _ hb)
    have hbeq : (⟨_, hbS⟩ : ↥(stabSub (orbSup T V))) = y⁻¹ * ⟨l', hl'S⟩ * y := Subtype.ext rfl
    rw [hbeq, map_mul, map_mul, map_inv] at h1
    have hc1 : Commute (resHom (orbSup T V) x) (resHom (orbSup T V) y) := hxy
    have hc2 : Commute (resHom (orbSup T V) x) ((resHom (orbSup T V) y)⁻¹ *
        resHom (orbSup T V) ⟨l', hl'S⟩ * resHom (orbSup T V) y) := h1
    have hc3 := (hc1.mul_right hc2).mul_right hc1.inv_right
    have e : resHom (orbSup T V) y * ((resHom (orbSup T V) y)⁻¹ *
        resHom (orbSup T V) ⟨l', hl'S⟩ * resHom (orbSup T V) y) * (resHom (orbSup T V) y)⁻¹ =
        resHom (orbSup T V) ⟨l', hl'S⟩ := by group
    rw [e] at hc3
    exact hc3
  have hMpS' : Mp ≤ S := by
    rw [n.Mp_eq]
    exact sup_le hLS hLtS
  intro p hp
  obtain ⟨m, hm, rfl⟩ := mem_autSub.mp hp
  obtain ⟨m', hm', hmm'⟩ := hMpS' hm
  have hm'eq : m' = m := Subtype.ext hmm'
  subst hm'eq
  exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_comap.mp hm')).symm

end Center

end CFSG.Quasithin
