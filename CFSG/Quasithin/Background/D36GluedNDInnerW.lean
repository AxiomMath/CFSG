module

public import CFSG.Quasithin.Background.D36GluedNDFinal
import CFSG.Quasithin.Background.D36GluedNDInner
import CFSG.Quasithin.Background.F918Z6Aux
public import CFSG.Quasithin.Background.F918P6

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

section InnerW

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

structure InnerData (T L : Subgroup (MulAut W)) (VT : Subgroup W) (g m : MulAut W) : Prop where
  gT : g ∈ T
  gN : g ∈ Subgroup.normalizer (L : Set (MulAut W))
  mL : m ∈ L
  gsq : ∀ v ∈ VT, g (g v) = v
  msq : ∀ v ∈ VT, m (m v) = v
  inn : ∀ l ∈ L, ∀ v ∈ VT, (g * l * g⁻¹) v = (m * l * m⁻¹) v

theorem core_aux (n : D36Norm M Mp T L V t) {c : MulAut W}
    (hcN : c ∈ Subgroup.normalizer (Mp : Set (MulAut W)))
    (hcVT : ∀ w ∈ orbSup T V, c w ∈ orbSup T V) (hcsq : ∀ w ∈ orbSup T V, c (c w) = w)
    (hcMp : ∀ a ∈ Mp, ∀ v ∈ V, c (a v) = a (c v)) :
    ∀ v ∈ V, c v * v⁻¹ ∈ modFix Mp (orbSup T V) := by
  have hcfix : modFix Mp (orbSup T V) ≤ (modFix Mp (orbSup T V)).comap c.toMonoidHom := by
    intro z hz
    have hz' : z ∈ orbSup T V ∧ ∀ a : ↥Mp, a • z = z := XMod.mem_fixed.mp hz
    refine Subgroup.mem_comap.mpr (XMod.mem_fixed.mpr ⟨hcVT z hz'.1, fun a => ?_⟩)
    have h1 : c⁻¹ * (a : MulAut W) * c ∈ Mp := (Subgroup.mem_normalizer_iff''.mp hcN a).mp a.2
    have h2 : (c⁻¹ * (a : MulAut W) * c) z = z := hz'.2 ⟨c⁻¹ * (a : MulAut W) * c, h1⟩
    have h3 : c⁻¹ ((a : MulAut W) (c z)) = z := by simpa [MulAut.mul_apply] using h2
    have h4 := congrArg c h3
    show (a : MulAut W) (c z) = c z
    simpa using h4
  let qc : (W ⧸ modFix Mp (orbSup T V)) →* (W ⧸ modFix Mp (orbSup T V)) :=
    QuotientGroup.map _ _ c.toMonoidHom hcfix
  have hqc : ∀ w : W, qc (QuotientGroup.mk w) = QuotientGroup.mk (c w) := fun w => rfl
  have hQ : ∀ q : W ⧸ modFix Mp (orbSup T V), q ^ 2 = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H w =>
      rw [← QuotientGroup.mk_pow, n.std.hyp.exp w]
      rfl
  have hbs : ∀ w : W, w ∈ (⨆ y ∈ T, y • V) → w ∈ orbSup T V := fun w hw => by
    rw [orbSup_eq_biSup_smul]
    exact hw
  have hbs' : ∀ w : W, w ∈ orbSup T V → w ∈ (⨆ y ∈ T, y • V) := fun w hw => by
    rw [orbSup_eq_biSup_smul] at hw
    exact hw
  have key := XMod.fixes_of_isHomComp (A := ↥Mp) (Q := W ⧸ modFix Mp (orbSup T V)) hQ
    n.std.irrT.2 qc (map_mul qc)
    (fun x hx => by
      obtain ⟨w, hw, rfl⟩ := mem_tilde_iff.mp hx
      rw [hqc, hqc, hcsq w (hbs w hw)])
    (fun q hq => by
      obtain ⟨w, hw, rfl⟩ := mem_tilde_iff.mp hq
      rw [hqc]
      exact mem_tilde_iff.mpr ⟨c w, hbs' _ (hcVT w (hbs w hw)), rfl⟩)
    (fun a q hq => by
      obtain ⟨v, hv, rfl⟩ := mem_tilde_iff.mp hq
      rw [XMod.smul_quotMk, hqc, hqc, XMod.smul_quotMk]
      exact congrArg QuotientGroup.mk (hcMp a a.2 v hv))
  intro v hv
  have h1 := key (QuotientGroup.mk v) (mem_tilde_iff.mpr ⟨v, hv, rfl⟩)
  rw [hqc] at h1
  have h2 := QuotientGroup.eq.mp h1
  have h3 : c v * v⁻¹ = ((c v)⁻¹ * v)⁻¹ := by
    rw [mul_inv_rev, inv_inv]
    exact mul_comm _ _
  rw [h3]
  exact (modFix Mp (orbSup T V)).inv_mem h2

namespace InnerData

variable {g m : MulAut W}

theorem g_stab (hd : InnerData T L (orbSup T V) g m) {v : W} (hv : v ∈ orbSup T V) :
    g v ∈ orbSup T V :=
  (le_stabSub_orbSup T V hd.gT v).mpr hv

theorem l_stab (n : D36Norm M Mp T L V t) {l : MulAut W} (hl : l ∈ L) {v : W}
    (hv : v ∈ orbSup T V) : l v ∈ orbSup T V :=
  (d36t_Mp_le_stab_orbSup n (d36t_L_le_Mp n hl) v).mpr hv

theorem minv (n : D36Norm M Mp T L V t) (hd : InnerData T L (orbSup T V) g m) {v : W}
    (hv : v ∈ orbSup T V) : m⁻¹ v = m v := by
  have h1 : m⁻¹ v ∈ orbSup T V := l_stab n (L.inv_mem hd.mL) hv
  have h2 := hd.msq _ h1
  have h3 : m (m⁻¹ v) = v := MulAut.apply_inv_self (M := W) m v
  rw [h3] at h2
  exact h2.symm

theorem comm (n : D36Norm M Mp T L V t) (hd : InnerData T L (orbSup T V) g m) {l : MulAut W}
    (hl : l ∈ L) {v : W} (hv : v ∈ orbSup T V) : (m⁻¹ * g) (l v) = l ((m⁻¹ * g) v) := by
  have h := hd.inn l hl (g v) (hd.g_stab hv)
  simp only [MulAut.mul_apply, MulAut.inv_apply_self (M := W)] at h
  have h' : g (l v) = m (l (m⁻¹ (g v))) := by
    have := h
    simpa using this
  show m⁻¹ (g (l v)) = l (m⁻¹ (g v))
  rw [h']
  exact MulAut.inv_apply_self (M := W) m _

theorem csq (n : D36Norm M Mp T L V t) (hd : InnerData T L (orbSup T V) g m) {v : W}
    (hv : v ∈ orbSup T V) : (m⁻¹ * g) ((m⁻¹ * g) v) = v := by
  have h1 : (m⁻¹ * g) (m⁻¹ (g v)) = m⁻¹ ((m⁻¹ * g) (g v)) :=
    hd.comm n (L.inv_mem hd.mL) (hd.g_stab hv)
  have e : (m⁻¹ * g) v = m⁻¹ (g v) := rfl
  rw [e, h1]
  have e2 : (m⁻¹ * g) (g v) = m⁻¹ (g (g v)) := rfl
  rw [e2, hd.gsq v hv, hd.minv n hv]
  exact MulAut.inv_apply_self (M := W) m v

theorem c_normalizes (n : D36Norm M Mp T L V t) (hd : InnerData T L (orbSup T V) g m) :
    m⁻¹ * g ∈ Subgroup.normalizer (Mp : Set (MulAut W)) :=
  (Subgroup.normalizer (Mp : Set (MulAut W))).mul_mem
    ((Subgroup.normalizer (Mp : Set (MulAut W))).inv_mem
      (Subgroup.le_normalizer (d36t_L_le_Mp n hd.mL)))
    (d36t_T_le_normalizer n hd.gT)

theorem conjAutSub_inj {a : MulAut W} {A B : Subgroup (MulAut W)}
    (h : conjAutSub a A = conjAutSub a B) : A = B := by
  ext y
  have := congrArg (fun S : Subgroup (MulAut W) => a * y * a⁻¹ ∈ S) h
  simp only [mem_conjAutSub_iff, eq_iff_iff] at this
  simpa [mul_assoc] using this

theorem g_normalizes_t (hL38 : D3L38) (n : D36Norm M Mp T L V t)
    (hd : InnerData T L (orbSup T V) g m) :
    g ∈ Subgroup.normalizer (conjAutSub t L : Set (MulAut W)) := by
  have hgt : g * t ∈ Mp ⊔ T := Subgroup.mem_sup_right (T.mul_mem hd.gT n.tT)
  have hgL : conjAutSub g L = L := Subgroup.mem_normalizer_iff_map_conj_eq.mp hd.gN
  rcases d36t_conj_cases hL38 n hgt with h | h
  · exfalso
    rw [conjAutSub_mul] at h
    have h2 : conjAutSub g (conjAutSub t L) = conjAutSub g L := h.trans hgL.symm
    have h3 : conjAutSub t L = L := conjAutSub_inj h2
    exact n.tn (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h3)
  · rw [conjAutSub_mul] at h
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h

theorem commt (hL38 : D3L38) (n : D36Norm M Mp T L V t) (hd : InnerData T L (orbSup T V) g m)
    {a : MulAut W} (ha : a ∈ conjAutSub t L) {v : W} (hv : v ∈ V) :
    (m⁻¹ * g) (a v) = a ((m⁻¹ * g) v) := by
  have hav : a v = v := n.triv v hv a ha
  have hgv : a (g v) = g v := by
    have h1 : g⁻¹ * a * g ∈ conjAutSub t L :=
      (Subgroup.mem_normalizer_iff''.mp (hd.g_normalizes_t hL38 n) a).mp ha
    have h2 : (g⁻¹ * a * g) v = v := n.triv v hv _ h1
    have h3 : g⁻¹ (a (g v)) = v := by simpa [MulAut.mul_apply] using h2
    have h4 := congrArg g h3
    simpa using h4
  have hmv : a (m⁻¹ (g v)) = m⁻¹ (g v) := by
    have hcm : a * m⁻¹ = m⁻¹ * a := by
      have h1 : m⁻¹ ∈ L := L.inv_mem hd.mL
      exact ((Subgroup.mem_centralizer_iff.mp (d36t_Lt_le_centralizer hL38 n ha)) _ h1).symm
    have := congrArg (fun φ : MulAut W => φ (g v)) hcm
    simp only [MulAut.mul_apply] at this
    rw [this, hgv]
  show m⁻¹ (g (a v)) = a (m⁻¹ (g v))
  rw [hav, hmv]

theorem commMp (hL38 : D3L38) (n : D36Norm M Mp T L V t) (hd : InnerData T L (orbSup T V) g m) :
    ∀ a ∈ Mp, ∀ v ∈ V, (m⁻¹ * g) (a v) = a ((m⁻¹ * g) v) := by
  set c : MulAut W := m⁻¹ * g with hc
  let Sub : Subgroup (MulAut W) :=
    { carrier := {a | a ∈ Mp ∧ ∀ v ∈ V, c (a v) = a (c v)}
      one_mem' := ⟨Mp.one_mem, fun v hv => rfl⟩
      mul_mem' := fun {a b} ha hb => ⟨Mp.mul_mem ha.1 hb.1, fun v hv => by
        have hbv : b v ∈ V := d36t_inv_V n hb.1 hv
        show c (a (b v)) = a (b (c v))
        rw [ha.2 (b v) hbv, hb.2 v hv]⟩
      inv_mem' := fun {a} ha => ⟨Mp.inv_mem ha.1, fun v hv => by
        have hav : a⁻¹ v ∈ V := d36t_inv_V n (Mp.inv_mem ha.1) hv
        have h1 := ha.2 (a⁻¹ v) hav
        rw [MulAut.apply_inv_self (M := W)] at h1
        show c (a⁻¹ v) = a⁻¹ (c v)
        rw [h1]
        exact (MulAut.inv_apply_self (M := W) a _).symm⟩ }
  have hL : L ≤ Sub := fun l hl =>
    ⟨d36t_L_le_Mp n hl, fun v hv => hd.comm n hl (n.lt.le hv)⟩
  have hLt : conjAutSub t L ≤ Sub := fun a ha =>
    ⟨d36t_Lt_le_Mp n ha, fun v hv => hd.commt hL38 n ha hv⟩
  intro a ha v hv
  rw [n.Mp_eq] at ha
  exact ((sup_le hL hLt : L ⊔ conjAutSub t L ≤ Sub) ha).2 v hv

theorem core (hL38 : D3L38) (n : D36Norm M Mp T L V t) (hd : InnerData T L (orbSup T V) g m) :
    ∀ v ∈ V, (m⁻¹ * g) v * v⁻¹ ∈ modFix Mp (orbSup T V) :=
  core_aux n (hd.c_normalizes n) (fun w hw => l_stab n (L.inv_mem hd.mL) (hd.g_stab hw))
    (fun w hw => hd.csq n hw) (hd.commMp hL38 n)

theorem gen (hL38 : D3L38) (n : D36Norm M Mp T L V t) (hd : InnerData T L (orbSup T V) g m)
    {l : MulAut W} (hl : l ∈ L) {v : W} (hv : v ∈ V) :
    (m⁻¹ * g) (l v * v⁻¹) = l v * v⁻¹ := by
  set c : MulAut W := m⁻¹ * g with hc
  have hz := hd.core hL38 n v hv
  set z : W := c v * v⁻¹ with hzdef
  have hcv : c v = z * v := by rw [hzdef]; group
  have hlz : l z = z := (XMod.mem_fixed.mp hz).2 ⟨l, d36t_L_le_Mp n hl⟩
  calc c (l v * v⁻¹) = c (l v) * (c v)⁻¹ := by rw [map_mul, map_inv]
    _ = l (c v) * (c v)⁻¹ := by rw [hd.comm n hl (n.lt.le hv)]
    _ = l (z * v) * (z * v)⁻¹ := by rw [hcv]
    _ = l v * v⁻¹ := by
      rw [map_mul, hlz]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel

theorem conj (n : D36Norm M Mp T L V t) (hd : InnerData T L (orbSup T V) g m) {s : MulAut W}
    (hsT : s ∈ T) (hsN : s ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    InnerData T L (orbSup T V) (s⁻¹ * g * s) (s⁻¹ * m * s) := by
  have hsV : ∀ v ∈ orbSup T V, s v ∈ orbSup T V := fun v hv =>
    (le_stabSub_orbSup T V hsT v).mpr hv
  have hN := Subgroup.normalizer (L : Set (MulAut W))
  refine ⟨T.mul_mem (T.mul_mem (T.inv_mem hsT) hd.gT) hsT,
    (Subgroup.normalizer (L : Set (MulAut W))).mul_mem
      ((Subgroup.normalizer (L : Set (MulAut W))).mul_mem
        ((Subgroup.normalizer (L : Set (MulAut W))).inv_mem hsN) hd.gN) hsN,
    (Subgroup.mem_normalizer_iff''.mp hsN m).mp hd.mL, fun v hv => ?_, fun v hv => ?_,
    fun l hl v hv => ?_⟩
  · show s⁻¹ (g (s (s⁻¹ (g (s v))))) = v
    rw [MulAut.apply_inv_self (M := W) s, hd.gsq _ (hsV v hv)]
    exact MulAut.inv_apply_self (M := W) s v
  · show s⁻¹ (m (s (s⁻¹ (m (s v))))) = v
    rw [MulAut.apply_inv_self (M := W) s, hd.msq _ (hsV v hv)]
    exact MulAut.inv_apply_self (M := W) s v
  · have hl₁ : s * l * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hsN l).mp hl
    have e1 : ∀ x : MulAut W, (s⁻¹ * x * s) * l * (s⁻¹ * x * s)⁻¹ =
        s⁻¹ * (x * (s * l * s⁻¹) * x⁻¹) * s := fun x => by group
    rw [e1 g, e1 m]
    have := hd.inn _ hl₁ (s v) (hsV v hv)
    change s⁻¹ ((g * (s * l * s⁻¹) * g⁻¹) (s v)) = s⁻¹ ((m * (s * l * s⁻¹) * m⁻¹) (s v))
    rw [this]

theorem gen_conj (hL38 : D3L38) (n : D36Norm M Mp T L V t)
    (hd : InnerData T L (orbSup T V) g m) {s : MulAut W} (hs : s ∈ T) {l : MulAut W}
    (hl : l ∈ L) {v : W} (hv : v ∈ V) :
    (m⁻¹ * g) (l (s v) * (s v)⁻¹) = l (s v) * (s v)⁻¹ := by
  by_cases hsN : s ∈ Subgroup.normalizer (L : Set (MulAut W))
  · have hd' := hd.conj n hs hsN
    have hl' : s⁻¹ * l * s ∈ L := (Subgroup.mem_normalizer_iff''.mp hsN l).mp hl
    have h1 := hd'.gen hL38 n hl' hv
    have e : (s⁻¹ * m * s)⁻¹ * (s⁻¹ * g * s) = s⁻¹ * (m⁻¹ * g) * s := by group
    rw [e] at h1
    have hx : s ((s⁻¹ * l * s) v * v⁻¹) = l (s v) * (s v)⁻¹ := by
      rw [map_mul, map_inv]
      simp [MulAut.mul_apply]
    have h3 : s⁻¹ ((m⁻¹ * g) (s ((s⁻¹ * l * s) v * v⁻¹))) = (s⁻¹ * l * s) v * v⁻¹ := h1
    have h4 := congrArg s h3
    rw [MulAut.apply_inv_self (M := W), hx] at h4
    exact h4
  · have hz : s⁻¹ ∈ Mp ⊔ T := Subgroup.mem_sup_right (T.inv_mem hs)
    have hsN' : s⁻¹ ∉ Subgroup.normalizer (L : Set (MulAut W)) := fun h =>
      hsN (by simpa using (Subgroup.normalizer (L : Set (MulAut W))).inv_mem h)
    rcases d36t_conj_cases hL38 n hz with h | h
    · exact absurd (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h) hsN'
    · have hmem : s⁻¹ * l * s ∈ conjAutSub s⁻¹ L := by
        rw [mem_conjAutSub_iff]
        simpa [mul_assoc] using hl
      rw [h] at hmem
      have h3 : s⁻¹ (l (s v)) = v := n.triv v hv _ hmem
      have h4 : l (s v) = s v := by
        have := congrArg s h3
        simpa using this
      rw [h4, mul_inv_cancel, map_one]

theorem fixes_comm (hL38 : D3L38) (n : D36Norm M Mp T L V t)
    (hd : InnerData T L (orbSup T V) g m) {w : W} (hw : w ∈ orbSup T V) {l : MulAut W}
    (hl : l ∈ L) : (m⁻¹ * g) (l w * w⁻¹) = l w * w⁻¹ := by
  let P : Subgroup W :=
    { carrier := {w | ∀ l ∈ L, (m⁻¹ * g) (l w * w⁻¹) = l w * w⁻¹}
      one_mem' := fun l hl => by simp
      mul_mem' := fun {a b} ha hb l hl => by
        have e : l (a * b) * (a * b)⁻¹ = (l a * a⁻¹) * (l b * b⁻¹) := by
          rw [map_mul, mul_inv_rev, mul_comm b⁻¹ a⁻¹]
          exact mul_mul_mul_comm _ _ _ _
        rw [e, map_mul, ha l hl, hb l hl]
      inv_mem' := fun {a} ha l hl => by
        have e : l a⁻¹ * (a⁻¹)⁻¹ = (l a * a⁻¹)⁻¹ := by
          rw [map_inv, inv_inv, mul_inv_rev, inv_inv]
          exact mul_comm _ _
        rw [e, map_inv, ha l hl] }
  have hP : orbSup T V ≤ P := by
    refine orbSup_le fun s hs => ?_
    rintro _ ⟨v, hv, rfl⟩ l hl
    exact hd.gen_conj hL38 n hs hl hv
  exact hP hw l hl

end InnerData

theorem d36Inner_holds : D36Inner := by
  intro hL38 W _ _ M Mp T L V t n g hg m hm hgU hgsq hmsq hinn u hu
  have hd : InnerData T L (orbSup T V) g m :=
    ⟨hg, d36nd_normalizer hL38 n hg hgU, hm, hgsq, hmsq, hinn⟩
  let F : Subgroup W :=
    { carrier := {x | (m⁻¹ * g) x = x}
      one_mem' := map_one _
      mul_mem' := fun {a b} ha hb => by
        have ha' : (m⁻¹ * g) a = a := ha
        have hb' : (m⁻¹ * g) b = b := hb
        show (m⁻¹ * g) (a * b) = a * b
        rw [map_mul, ha', hb']
      inv_mem' := fun {a} ha => by
        have ha' : (m⁻¹ * g) a = a := ha
        show (m⁻¹ * g) a⁻¹ = a⁻¹
        rw [map_inv, ha'] }
  have hF : commSub (orbSup T V) L ≤ F := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨l, hl, w, hw, rfl⟩
    exact hd.fixes_comm hL38 n hw hl
  have h1 : (m⁻¹ * g) u = u := hF hu
  have h2 : m⁻¹ (g u) = u := h1
  have h3 := congrArg m h2
  rw [MulAut.apply_inv_self (M := W)] at h3
  exact h3

end InnerW

end CFSG.Quasithin
