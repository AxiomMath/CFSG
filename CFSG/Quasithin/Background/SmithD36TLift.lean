module

public import CFSG.Quasithin.Background.F918Q3
public import CFSG.Quasithin.Background.F918Q4
public import CFSG.Quasithin.Background.F918R6

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Index

variable {Y : Type} [CommGroup Y] [Finite Y]

theorem mem_or_mem_or_mul_mem_of_rk_le (hY : ∀ y : Y, y ^ 2 = 1) {H K : Subgroup Y}
    (hHK : H ≤ K) (hr : rk ↥K ≤ rk ↥H + 1) {a b : Y} (ha : a ∈ K) (hb : b ∈ K) :
    a ∈ H ∨ b ∈ H ∨ a * b ∈ H := by
  have hc := Subgroup.card_mul_index (H.subgroupOf K)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv, card_eq_two_pow hY H,
    card_eq_two_pow hY K] at hc
  have hidx : (H.subgroupOf K).index ≤ 2 := by
    have h1 : 2 ^ rk ↥K ≤ 2 ^ (rk ↥H + 1) := Nat.pow_le_pow_right (by norm_num) hr
    rw [pow_succ, ← hc] at h1
    exact Nat.le_of_mul_le_mul_left h1 (by positivity)
  have hidx0 : (H.subgroupOf K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcases : (H.subgroupOf K).index = 1 ∨ (H.subgroupOf K).index = 2 := by omega
  rcases hcases with hi | hi
  · left
    have htop : H.subgroupOf K = ⊤ := Subgroup.index_eq_one.mp hi
    have hmem : (⟨a, ha⟩ : ↥K) ∈ H.subgroupOf K := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem
  · by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2, h3⟩ := hcon
    have h1' : (⟨a, ha⟩ : ↥K) ∉ H.subgroupOf K := fun h => h1 (Subgroup.mem_subgroupOf.mp h)
    have h2' : (⟨b, hb⟩ : ↥K) ∉ H.subgroupOf K := fun h => h2 (Subgroup.mem_subgroupOf.mp h)
    have hab := (Subgroup.mul_mem_iff_of_index_two hi).mpr (iff_of_false h1' h2')
    exact h3 (Subgroup.mem_subgroupOf.mp hab)

end Index

section Offender

variable {Y : Type} [CommGroup Y] [Finite Y]

omit [Finite Y] in
theorem apply_mem_map_iff_d36t {J : Subgroup Y} (g : MulAut Y) (x : Y) :
    g x ∈ J.map g.toMonoidHom ↔ x ∈ J := by
  rw [Subgroup.mem_map_equiv]
  simp

theorem exists_ne_one_of_tightSwap (hY : ∀ y : Y, y ^ 2 = 1) {X : Subgroup (MulAut Y)}
    {U U' : Subgroup Y} (hP : GluedPair X U U') (h3 : rk ↥(U ⊓ U') + 2 < rk ↥U)
    {A : Subgroup (MulAut Y)} (hA : TightSwap X U U' A) :
    ∃ g ∈ A, g ∈ stabSub U ∧ g ≠ 1 ∧ g * g = 1 ∧ ∃ a ∈ A, g * a = a * g ∧
      U.map a.toMonoidHom = U' ∧ U'.map a.toMonoidHom = U ∧
      ∀ u ∈ U, ∀ u' ∈ U, g u * u⁻¹ ∈ U ⊓ U' ∨ g u' * u'⁻¹ ∈ U ⊓ U' ∨
        g (u * u') * (u * u')⁻¹ ∈ U ⊓ U' := by
  obtain ⟨hQ, hAU, htight⟩ := hA
  obtain ⟨r, -, hr2, ⟨⟨hA2, hAr⟩, -⟩, -⟩ := QhatStar_spec hQ
  have hAel : IsElemAbelian2 A := hA2.2.2
  obtain ⟨a, haA, haU⟩ : ∃ a ∈ A, a ∉ stabSub U := by
    by_contra hcon
    push Not at hcon
    exact hAU fun g hg => hcon g hg
  obtain ⟨ha1, ha2⟩ : U.map a.toMonoidHom = U' ∧ U'.map a.toMonoidHom = U :=
    (hP.perm a (hA2.1 haA)).resolve_left fun h => haU h.1
  obtain ⟨g, hgA, hgU, hg1⟩ : ∃ g ∈ A, g ∈ stabSub U ∧ g ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hcases : ∀ b ∈ A, b = 1 ∨ b = a := by
      intro b hb
      by_cases hbU : b ∈ stabSub U
      · exact Or.inl (hcon b hb hbU)
      · right
        obtain ⟨hb1, -⟩ : U.map b.toMonoidHom = U' ∧ U'.map b.toMonoidHom = U :=
          (hP.perm b (hA2.1 hb)).resolve_left fun h => hbU h.1
        have hstab : a⁻¹ * b ∈ stabSub U := by
          intro y
          have e1 : (a⁻¹ * b) y ∈ U ↔ b y ∈ U' := by
            rw [MulAut.mul_apply, ← ha1, ← apply_mem_map_iff_d36t a]
            simp
          rw [e1, ← hb1]
          exact apply_mem_map_iff_d36t b y
        have := hcon _ (A.mul_mem (A.inv_mem haA) hb) hstab
        rw [inv_mul_eq_one] at this
        exact this.symm
    have ha1' : a ≠ 1 := fun h => haU (h ▸ (stabSub U).one_mem)
    have haa : a ^ 2 = 1 := hAel.2 a haA
    have hAeq : A = Subgroup.zpowers a := by
      refine le_antisymm (fun b hb => ?_) (Subgroup.zpowers_le.mpr haA)
      rcases hcases b hb with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
    have hord : orderOf a = 2 := orderOf_eq_prime haa ha1'
    have hrkA : rk ↥A = 1 := by
      unfold rk
      rw [hAeq, Nat.card_zpowers, hord]
      simp
    have hidx : rkIdx (fixV A) ≤ 2 := by
      have h1 := hA2.rAV_mul
      rw [hrkA, hAr] at h1
      have h2 : (rkIdx (fixV A) : ℚ) ≤ 2 := by
        rw [← h1]
        simpa using hr2
      exact_mod_cast h2
    have hFU : fixV A ⊓ U ≤ U ⊓ U' := by
      rintro y ⟨hyF, hyU⟩
      refine ⟨hyU, ?_⟩
      rw [← ha1]
      have := (apply_mem_map_iff_d36t (J := U) a y).mpr hyU
      rwa [hyF a haA] at this
    have e1 := rk_sup_add_rk_inf (fixV A) U
    have e2 := rk_add_rkIdx (fixV A)
    have e3 : rk ↥(fixV A ⊔ U) ≤ rk Y := (rk_mono le_top).trans_eq rk_top
    have e4 := rk_mono hFU
    omega
  have hgg : g * g = 1 := by simpa [pow_two] using hAel.2 g hgA
  refine ⟨g, hgA, hgU, hg1, hgg, a, haA, hAel.1 g hgA a haA, ha1, ha2, ?_⟩
  intro u hu u' hu'
  have hY' : ∀ y : Y, y ^ 2 = 1 := hY
  have hmem := mem_or_mem_or_mul_mem_of_rk_le hY'
    (commModSub_le U (A ⊓ stabSub U) (U ⊓ U')) htight hu hu'
  have hg0 : g ∈ A ⊓ stabSub U := ⟨hgA, hgU⟩
  rcases hmem with h | h | h
  · exact Or.inl (h.2 g hg0)
  · exact Or.inr (Or.inl (h.2 g hg0))
  · exact Or.inr (Or.inr (h.2 g hg0))

end Offender

section Plumbing

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

omit [Finite W] in
theorem conjAutSub_mul_d36t (a b : MulAut W) (L : Subgroup (MulAut W)) :
    conjAutSub (a * b) L = conjAutSub a (conjAutSub b L) := by
  ext x
  simp only [mem_conjAutSub_iff]
  have : (a * b)⁻¹ * x * (a * b) = b⁻¹ * (a⁻¹ * x * a) * b := by group
  rw [this]

theorem d36t_L_le_Mp (n : D36Norm M Mp T L V t) : L ≤ Mp := by
  rw [n.Mp_eq]
  exact le_sup_left

theorem d36t_Lt_le_Mp (n : D36Norm M Mp T L V t) : conjAutSub t L ≤ Mp := by
  rw [n.Mp_eq]
  exact le_sup_right

theorem d36t_T_le_normalizer (n : D36Norm M Mp T L V t) :
    T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := by
  rw [n.std.hyp.Mp_eq]
  exact le_normalizer_conjClosure L T

theorem d36t_sup_le_normalizer (n : D36Norm M Mp T L V t) :
    Mp ⊔ T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) :=
  sup_le Subgroup.le_normalizer (d36t_T_le_normalizer n)

theorem d36t_inv_V (n : D36Norm M Mp T L V t) {g : MulAut W} (hg : g ∈ Mp) {v : W}
    (hv : v ∈ V) : g v ∈ V :=
  n.std.hyp.irr.2.1 ⟨g, hg⟩ v hv

theorem d36t_Mp_le_stab_orbSup (n : D36Norm M Mp T L V t) : Mp ≤ stabSub (orbSup T V) := by
  have key : ∀ x ∈ Mp, ∀ w ∈ orbSup T V, x w ∈ orbSup T V := by
    intro x hx w hw
    have hle : orbSup T V ≤ (orbSup T V).comap x.toMonoidHom := by
      refine orbSup_le fun s hs => ?_
      rintro _ ⟨v, hv, rfl⟩
      show x (s v) ∈ orbSup T V
      have hx' : s⁻¹ * x * s ∈ Mp :=
        (Subgroup.mem_normalizer_iff''.mp (d36t_T_le_normalizer n hs) x).mp hx
      have h1 : x (s v) = s ((s⁻¹ * x * s) v) := by simp [MulAut.mul_apply]
      rw [h1]
      exact map_le_orbSup hs ⟨_, d36t_inv_V n hx' hv, rfl⟩
    exact hle hw
  intro x hx u
  refine ⟨fun hu => ?_, fun hu => key x hx u hu⟩
  have := key x⁻¹ (Mp.inv_mem hx) _ hu
  simpa using this

theorem d36t_Lt_le_centralizer (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    conjAutSub t L ≤ Subgroup.centralizer (L : Set (MulAut W)) := by
  have hc := (hL38 W M Mp T L V n.std t n.tT n.tn n.Mp_eq).2.1
  intro y hy
  refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
  have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc hh
  exact ((Subgroup.mem_centralizer_iff.mp this) y hy).symm

theorem d36t_L_le_centralizer (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    L ≤ Subgroup.centralizer (conjAutSub t L : Set (MulAut W)) := by
  intro y hy
  refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
  exact ((Subgroup.mem_centralizer_iff.mp (d36t_Lt_le_centralizer hL38 n hh)) y hy).symm

theorem d36t_Mp_le_normalizer (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    Mp ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
  rw [n.Mp_eq]
  exact sup_le Subgroup.le_normalizer
    ((d36t_Lt_le_centralizer hL38 n).trans (Subgroup.centralizer_le_normalizer _))

theorem d36t_Mp_le_normalizer_t (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    Mp ≤ Subgroup.normalizer (conjAutSub t L : Set (MulAut W)) := by
  rw [n.Mp_eq]
  exact sup_le ((d36t_L_le_centralizer hL38 n).trans (Subgroup.centralizer_le_normalizer _))
    Subgroup.le_normalizer

theorem d36t_conj_cases (hL38 : D3L38) (n : D36Norm M Mp T L V t) {z : MulAut W}
    (hz : z ∈ Mp ⊔ T) : conjAutSub z L = L ∨ conjAutSub z L = conjAutSub t L := by
  have hz' : z ∈ ((Mp ⊔ T : Subgroup (MulAut W)) : Set (MulAut W)) := hz
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Mp T (d36t_T_le_normalizer n)] at hz'
  obtain ⟨m, hm, s, hs, rfl⟩ := hz'
  have h1 : conjAutSub m L = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (d36t_Mp_le_normalizer hL38 n hm)
  have h2 : conjAutSub m (conjAutSub t L) = conjAutSub t L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (d36t_Mp_le_normalizer_t hL38 n hm)
  rw [conjAutSub_mul_d36t]
  rcases (hL38 W M Mp T L V n.std t n.tT n.tn n.Mp_eq).2.2.2 s hs with h | h
  · left
    rw [h, h1]
  · right
    rw [h, h2]

omit [Finite W] in
theorem d36t_map_U {x : MulAut W} (hx : x ∈ stabSub (orbSup T V)) :
    (commSub (orbSup T V) L).map x.toMonoidHom = commSub (orbSup T V) (conjAutSub x L) := by
  have h := commSub_conjBy x (orbSup T V) L
  rw [mem_stabSub_iff_map_eq.mp hx] at h
  exact h.symm

theorem d36t_Ut_eq (n : D36Norm M Mp T L V t) :
    (commSub (orbSup T V) L).map t.toMonoidHom = commSub (orbSup T V) (conjAutSub t L) :=
  d36t_map_U (le_stabSub_orbSup T V n.tT)

theorem d36t_U_le (n : D36Norm M Mp T L V t) : commSub (orbSup T V) L ≤ orbSup T V :=
  commSub_le_of_invariant fun _ hx w hw =>
    ((d36t_Mp_le_stab_orbSup n (d36t_L_le_Mp n hx)) w).mpr hw

theorem d36t_Ut_le (n : D36Norm M Mp T L V t) :
    (commSub (orbSup T V) L).map t.toMonoidHom ≤ orbSup T V := by
  rintro _ ⟨u, hu, rfl⟩
  exact mem_orbSup_of_mem_map n.tT (d36t_U_le n hu)

theorem d36t_L_inv_U (n : D36Norm M Mp T L V t) :
    ∀ l ∈ L, ∀ u ∈ commSub (orbSup T V) L, l u ∈ commSub (orbSup T V) L := by
  intro l hl u hu
  have h := (commSub (orbSup T V) L).mul_mem
    (Subgroup.subset_closure ⟨l, hl, u, d36t_U_le n hu, rfl⟩ :
      l u * u⁻¹ ∈ commSub (orbSup T V) L) hu
  rwa [inv_mul_cancel_right] at h

theorem d36t_rank (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    rk ↥(commSub (orbSup T V) L ⊓ (commSub (orbSup T V) L).map t.toMonoidHom) + 2 <
      rk ↥(commSub (orbSup T V) L) := by
  have h := d36_rank_Y hL38 n
  have hrk : ∀ J : Subgroup W, J ≤ orbSup T V → rk ↥(J.subgroupOf (orbSup T V)) = rk ↥J :=
    fun J hJ => by unfold rk; rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJ).toEquiv]
  have hinf : (commSub (orbSup T V) L).subgroupOf (orbSup T V) ⊓
      ((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V) =
      (commSub (orbSup T V) L ⊓ (commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf
        (orbSup T V) := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  rw [hinf, hrk _ (inf_le_left.trans (d36t_U_le n)), hrk _ (d36t_U_le n)] at h
  exact h

theorem d36t_U_ne_Ut (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    commSub (orbSup T V) L ≠ (commSub (orbSup T V) L).map t.toMonoidHom := by
  intro h
  have hr := d36t_rank hL38 n
  rw [← h, inf_idem] at hr
  omega

theorem d36t_mem_normalizer (hL38 : D3L38) (n : D36Norm M Mp T L V t) {x : MulAut W}
    (hxX : x ∈ Mp ⊔ T) (hxS : x ∈ stabSub (orbSup T V))
    (hxU : (commSub (orbSup T V) L).map x.toMonoidHom = commSub (orbSup T V) L) :
    x ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
  rcases d36t_conj_cases hL38 n hxX with h | h
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
  · exfalso
    apply d36t_U_ne_Ut hL38 n
    have e : (commSub (orbSup T V) L).map x.toMonoidHom =
        (commSub (orbSup T V) L).map t.toMonoidHom := by
      rw [d36t_map_U hxS, h, d36t_Ut_eq n]
    exact hxU.symm.trans e

theorem d36t_conj_eq_of_swap (hL38 : D3L38) (n : D36Norm M Mp T L V t) {y : MulAut W}
    (hyX : y ∈ Mp ⊔ T) (hyS : y ∈ stabSub (orbSup T V))
    (hyU : (commSub (orbSup T V) L).map y.toMonoidHom =
      (commSub (orbSup T V) L).map t.toMonoidHom) :
    conjAutSub y L = conjAutSub t L := by
  rcases d36t_conj_cases hL38 n hyX with h | h
  · exfalso
    apply d36t_U_ne_Ut hL38 n
    rw [← hyU, d36t_map_U hyS, h]
  · exact h

theorem d36t_L_fix_Ut (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    ∀ u ∈ commSub (orbSup T V) L, ∀ g ∈ L, g (t u) = t u :=
  CFSG.Quasithin.L_fix_UtQ3 hL38 n

theorem d36t_D_le_fixV (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    commSub (orbSup T V) L ⊓ (commSub (orbSup T V) L).map t.toMonoidHom ≤ fixV Mp := by
  have hle : Mp ≤
      centSub (commSub (orbSup T V) L ⊓ (commSub (orbSup T V) L).map t.toMonoidHom) := by
    rw [n.Mp_eq]
    refine sup_le (fun g hg d hd => ?_) (fun g hg d hd => (d36_part1 hL38 n).2 d hd.1 g hg)
    obtain ⟨u, hu, rfl⟩ := hd.2
    exact d36t_L_fix_Ut hL38 n u hu g hg
  intro d hd m hm
  exact hle hm d hd

end Plumbing

section Lift

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

omit [Finite W] in
theorem map_subgroupOf_resHom_d36t {Y J : Subgroup W} (x : stabSub Y) :
    (J.subgroupOf Y).map (resHom Y x).toMonoidHom =
      (J.map (x : MulAut W).toMonoidHom).subgroupOf Y :=
  CFSG.Quasithin.map_subgroupOf_resHomQ2 x

theorem d36t_lift (hL38 : D3L38) (n : D36Norm M Mp T L V t)
    {A : Subgroup (MulAut ↥(orbSup T V))}
    (hA : TightSwap (autSub (Mp ⊔ T) (orbSup T V))
      ((commSub (orbSup T V) L).subgroupOf (orbSup T V))
      (((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V)) A) :
    ∃ x y : ↥(stabSub (orbSup T V)), (x : MulAut W) ∈ Mp ⊔ T ∧ (y : MulAut W) ∈ Mp ⊔ T ∧
      resHom (orbSup T V) x ≠ 1 ∧
      resHom (orbSup T V) x * resHom (orbSup T V) y =
        resHom (orbSup T V) y * resHom (orbSup T V) x ∧
      (∀ w ∈ orbSup T V, (x : MulAut W) ((x : MulAut W) w) = w) ∧
      (x : MulAut W) ∈ stabSub (commSub (orbSup T V) L) ∧
      (x : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W)) ∧
      conjAutSub (y : MulAut W) L = conjAutSub t L ∧
      ∀ u ∈ commSub (orbSup T V) L, ∀ u' ∈ commSub (orbSup T V) L,
        (x : MulAut W) u * u⁻¹ ∈ fixV L ∨ (x : MulAut W) u' * u'⁻¹ ∈ fixV L ∨
          (x : MulAut W) (u * u') * (u * u')⁻¹ ∈ fixV L := by
  have hY : ∀ y : ↥(orbSup T V), y ^ 2 = 1 := fun y =>
    Subtype.ext (by simpa using n.std.hyp.exp y.1)
  have hP : GluedPair (autSub (Mp ⊔ T) (orbSup T V))
      ((commSub (orbSup T V) L).subgroupOf (orbSup T V))
      (((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V)) :=
    ⟨d36_sup_Y hL38 n, d36_perm_Y hL38 n, d36_swap_Y hL38 n, d36_faithful_Y hL38 n⟩
  have hA2 : IsA2 (autSub (Mp ⊔ T) (orbSup T V)) A := by
    obtain ⟨r, -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA.1
    exact hA2
  obtain ⟨g, hgA, hgU, hg1, hgg, a, haA, hga, ha1, -, htri⟩ :=
    exists_ne_one_of_tightSwap hY hP (d36_rank_Y hL38 n) hA
  obtain ⟨x, hxX, rfl⟩ := mem_autSub.mp (hA2.1 hgA)
  obtain ⟨y, hyX, rfl⟩ := mem_autSub.mp (hA2.1 haA)
  have hUle : (commSub (orbSup T V) L) ≤ (orbSup T V) := d36t_U_le n
  have hUtle : (commSub (orbSup T V) L).map t.toMonoidHom ≤ (orbSup T V) := d36t_Ut_le n
  have hxU : (x : MulAut W) ∈ stabSub (commSub (orbSup T V) L) := by
    intro w
    by_cases hw : w ∈ (orbSup T V)
    · have := hgU ⟨w, hw⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, resHom_apply] at this
      exact this
    · have hnu : w ∉ (commSub (orbSup T V) L) := fun h' => hw (hUle h')
      have hnx : (x : MulAut W) w ∉ (orbSup T V) := fun h' => hw ((x.2 w).mp h')
      exact ⟨fun h' => absurd (hUle h') hnx, fun h' => absurd h' hnu⟩
  have hxN := d36t_mem_normalizer hL38 n hxX x.2 (mem_stabSub_iff_map_eq.mp hxU)
  have hyU : (commSub (orbSup T V) L).map (y : MulAut W).toMonoidHom =
      (commSub (orbSup T V) L).map t.toMonoidHom := by
    have h1 := map_subgroupOf_resHom_d36t (J := (commSub (orbSup T V) L)) y
    rw [ha1] at h1
    have h2 := Subgroup.subgroupOf_inj.mp h1
    have hyle : (commSub (orbSup T V) L).map (y : MulAut W).toMonoidHom ≤ (orbSup T V) := by
      rintro _ ⟨u, hu, rfl⟩
      exact (y.2 u).mpr (hUle hu)
    rw [inf_of_le_left hUtle, inf_of_le_left hyle] at h2
    exact h2.symm
  have hyL := d36t_conj_eq_of_swap hL38 n hyX y.2 hyU
  have hfixL : fixV Mp ≤ fixV L := fun v hv l hl => hv l (d36t_L_le_Mp n hl)
  have hD := d36t_D_le_fixV hL38 n
  refine ⟨x, y, hxX, hyX, hg1, hga, ?_, hxU, hxN, hyL, ?_⟩
  · intro w hw
    have := congrArg (fun φ : MulAut ↥(orbSup T V) => ((φ ⟨w, hw⟩ : ↥(orbSup T V)) : W)) hgg
    simpa [MulAut.mul_apply, resHom_apply] using this
  · intro u hu u' hu'
    have huy : (⟨u, hUle hu⟩ : ↥(orbSup T V)) ∈
        (commSub (orbSup T V) L).subgroupOf (orbSup T V) := Subgroup.mem_subgroupOf.mpr hu
    have hu'y : (⟨u', hUle hu'⟩ : ↥(orbSup T V)) ∈
        (commSub (orbSup T V) L).subgroupOf (orbSup T V) := Subgroup.mem_subgroupOf.mpr hu'
    have key : ∀ z : ↥(orbSup T V), z ∈ (commSub (orbSup T V) L).subgroupOf (orbSup T V) ⊓
        ((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V) →
        (z : W) ∈ fixV L := fun z hz =>
      hfixL (hD ⟨Subgroup.mem_subgroupOf.mp hz.1, Subgroup.mem_subgroupOf.mp hz.2⟩)
    rcases htri _ huy _ hu'y with h | h | h
    · left
      have := key _ h
      simpa [resHom_apply] using this
    · right; left
      have := key _ h
      simpa [resHom_apply] using this
    · right; right
      have := key _ h
      simpa [resHom_apply] using this

end Lift

end CFSG.Quasithin
