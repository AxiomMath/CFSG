module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXAA
public import CFSG.Quasithin.Background.FixVZPowersMem

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

private def w16g_phi1 (q : MulAut W) : W →* W where
  toFun w := (q ^ 3) w * q w * w
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul]
    ac_rfl

private def w16g_phi2 (q : MulAut W) : W →* W where
  toFun w := (q ^ 3) w * (q ^ 2) w * w
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul]
    ac_rfl

private def w16g_P (q : MulAut W) (u : W) : W :=
  (q ^ 6) u * (q ^ 5) u * (q ^ 4) u * (q ^ 3) u * (q ^ 2) u * q u * u

private theorem w16g_phi2_equiv {q x : MulAut W} (hxq : Commute x q) (u : W) :
    w16g_phi2 q (x u) = x (w16g_phi2 q u) := by
  have h3 : Commute x (q ^ 3) := hxq.pow_right 3
  have h2 : Commute x (q ^ 2) := hxq.pow_right 2
  change (q ^ 3) (x u) * (q ^ 2) (x u) * x u =
    x ((q ^ 3) u * (q ^ 2) u * u)
  rw [show (q ^ 3) (x u) = x ((q ^ 3) u) by
        rw [← MulAut.mul_apply, h3.eq.symm, MulAut.mul_apply],
      show (q ^ 2) (x u) = x ((q ^ 2) u) by
        rw [← MulAut.mul_apply, h2.eq.symm, MulAut.mul_apply]]
  rw [← map_mul, ← map_mul]

private theorem w16g_P_fix {q : MulAut W} (hq7 : q ^ 7 = 1) (u : W) :
    q (w16g_P q u) = w16g_P q u := by
  have h7 : (q ^ 7) u = u := by rw [hq7, MulAut.one_apply]
  have h16 : q ((q ^ 6) u) = (q ^ 7) u := by
    rw [← MulAut.mul_apply, ← pow_succ']
  have h15 : q ((q ^ 5) u) = (q ^ 6) u := by
    rw [← MulAut.mul_apply, ← pow_succ']
  have h14 : q ((q ^ 4) u) = (q ^ 5) u := by
    rw [← MulAut.mul_apply, ← pow_succ']
  have h13 : q ((q ^ 3) u) = (q ^ 4) u := by
    rw [← MulAut.mul_apply, ← pow_succ']
  have h12 : q ((q ^ 2) u) = (q ^ 3) u := by
    rw [← MulAut.mul_apply, ← pow_succ']
  have h11 : q (q u) = (q ^ 2) u := by
    rw [← MulAut.mul_apply, ← pow_two]
  change q ((q ^ 6) u * (q ^ 5) u * (q ^ 4) u * (q ^ 3) u * (q ^ 2) u * q u * u) =
    w16g_P q u
  simp only [map_mul]
  rw [h16, h15, h14, h13, h12, h11, h7]
  change u * (q ^ 6) u * (q ^ 5) u * (q ^ 4) u * (q ^ 3) u * (q ^ 2) u * q u =
    (q ^ 6) u * (q ^ 5) u * (q ^ 4) u * (q ^ 3) u * (q ^ 2) u * q u * u
  ac_rfl

private theorem w16g_P_mem {X : Subgroup (MulAut W)} {U₀ : Subgroup W}
    (hIrr : IsIrrOn X U₀ ⊥) {q : MulAut W} (hqX : q ∈ X) :
    ∀ u ∈ U₀, w16g_P q u ∈ U₀ := by
  intro u hu
  have hq : q u ∈ U₀ := hIrr.2.1 q hqX u hu
  have hk : ∀ k : ℕ, (q ^ k) u ∈ U₀ :=
    fun k => hIrr.2.1 (q ^ k) (X.pow_mem hqX k) u hu
  change (q ^ 6) u * (q ^ 5) u * (q ^ 4) u * (q ^ 3) u * (q ^ 2) u * q u * u ∈ U₀
  exact U₀.mul_mem (U₀.mul_mem (U₀.mul_mem (U₀.mul_mem (U₀.mul_mem
    (U₀.mul_mem (hk 6) (hk 5)) (hk 4)) (hk 3)) (hk 2)) hq) hu

private theorem w16g_phi1_phi2 (hW : ∀ w : W, w * w = 1) (q : MulAut W) (u : W) :
    w16g_phi1 q (w16g_phi2 q u) = w16g_P q u := by
  have h33 : (q ^ 3) ((q ^ 3) u) = (q ^ 6) u := by
    rw [← MulAut.mul_apply, ← pow_add]
  have h32 : (q ^ 3) ((q ^ 2) u) = (q ^ 5) u := by
    rw [← MulAut.mul_apply, ← pow_add]
  have h13 : q ((q ^ 3) u) = (q ^ 4) u := by
    rw [← MulAut.mul_apply, ← pow_succ']
  have h12 : q ((q ^ 2) u) = (q ^ 3) u := by
    rw [← MulAut.mul_apply, ← pow_succ']
  have hc : (q ^ 3) u * (q ^ 3) u * (q ^ 3) u = (q ^ 3) u := by
    rw [hW ((q ^ 3) u), one_mul]
  change (q ^ 3) ((q ^ 3) u * (q ^ 2) u * u) * q ((q ^ 3) u * (q ^ 2) u * u) *
      ((q ^ 3) u * (q ^ 2) u * u) = w16g_P q u
  simp only [map_mul]
  rw [h33, h32, h13, h12]
  calc (q ^ 6) u * (q ^ 5) u * (q ^ 3) u * ((q ^ 4) u * (q ^ 3) u * q u) *
        ((q ^ 3) u * (q ^ 2) u * u)
      = (q ^ 6) u * (q ^ 5) u * (q ^ 4) u *
          ((q ^ 3) u * (q ^ 3) u * (q ^ 3) u) * q u * (q ^ 2) u * u := by ac_rfl
    _ = (q ^ 6) u * (q ^ 5) u * (q ^ 4) u * (q ^ 3) u * q u * (q ^ 2) u * u := by
          rw [hc]
    _ = (q ^ 6) u * (q ^ 5) u * (q ^ 4) u * (q ^ 3) u * (q ^ 2) u * q u * u := by
          ac_rfl

private theorem w16g_triple_transfer_sec {X : Subgroup (MulAut W)} {U₀ V₁ : Subgroup W}
    {a b : MulAut W} (ha : a ∈ X) (hb : b ∈ X)
    (h₀ : ∀ w ∈ U₀, a w * b w * w = 1) (hsec : SecIsoOn X V₁ ⊥ U₀ ⊥) :
    ∀ z ∈ V₁, a z * b z * z = 1 := by
  obtain ⟨-, -, hSA, -, -, -, β, hβB, hβiff, -, hβeq⟩ := hsec
  intro z hz
  have haz : a z ∈ V₁ := hSA a ha z hz
  have hbz : b z ∈ V₁ := hSA b hb z hz
  have hβa : β ⟨a z, haz⟩ = a (β ⟨z, hz⟩) := by
    have h := hβeq a ha ⟨z, hz⟩ ⟨a z, haz⟩ rfl
    rw [Subgroup.mem_bot, mul_inv_eq_one] at h
    exact h
  have hβb : β ⟨b z, hbz⟩ = b (β ⟨z, hz⟩) := by
    have h := hβeq b hb ⟨z, hz⟩ ⟨b z, hbz⟩ rfl
    rw [Subgroup.mem_bot, mul_inv_eq_one] at h
    exact h
  have hβone : ∀ z' : ↥V₁, β z' = 1 ↔ (z' : W) = 1 := fun z' => by
    simpa using hβiff z'
  have harg : β (⟨a z, haz⟩ * ⟨b z, hbz⟩ * ⟨z, hz⟩) = 1 := by
    rw [map_mul, map_mul, hβa, hβb]
    exact h₀ (β ⟨z, hz⟩) (hβB ⟨z, hz⟩)
  have h1 : ((⟨a z, haz⟩ * ⟨b z, hbz⟩ * ⟨z, hz⟩ : ↥V₁) : W) = 1 := (hβone _).mp harg
  simpa using h1

private theorem w16g_mem_fixV_of_cubic {q : MulAut W} {u : W}
    (h1 : (q ^ 3) u * q u * u = 1) (h2 : (q ^ 3) u * (q ^ 2) u * u = 1) :
    u ∈ fixV (Subgroup.zpowers q) := by
  have hq : q u = (q ^ 2) u := by
    have h : (q ^ 3) u * q u * u = (q ^ 3) u * (q ^ 2) u * u := by rw [h1, h2]
    exact mul_left_cancel (mul_right_cancel h)
  have hq2 : q⁻¹ * q ^ 2 = q := by
    rw [pow_two, ← mul_assoc, inv_mul_cancel, one_mul]
  have hu : u = q u := by
    have h := congrArg (fun x => (q⁻¹) x) hq
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply, hq2] at h
    exact h
  exact mem_fixV_zpowers_iff_apply.mpr hu.symm

theorem s13_triple_transfer {X : Subgroup (MulAut W)} {U₀ : Subgroup W} {a b : MulAut W}
    (ha : a ∈ X) (hb : b ∈ X) (h₀ : ∀ w ∈ U₀, a w * b w * w = 1) :
    ∀ w ∈ s13IsoSum X U₀, a w * b w * w = 1 := by
  intro w hw
  rw [s13IsoSum] at hw
  refine Subgroup.iSup_induction _ (C := fun w => a w * b w * w = 1) hw ?_ ?_ ?_
  · intro V₁ y hy
    refine Subgroup.iSup_induction _ (C := fun w => a w * b w * w = 1) hy ?_ ?_ ?_
    · intro hsec z hz
      exact w16g_triple_transfer_sec ha hb h₀ hsec.2 z hz
    · simp
    · intro x y hx hy
      rw [map_mul, map_mul]
      calc (a x * a y) * (b x * b y) * (x * y)
          = (a x * b x * x) * (a y * b y * y) := by ac_rfl
        _ = 1 := by rw [hx, hy, one_mul]
  · simp
  · intro x y hx hy
    rw [map_mul, map_mul]
    calc (a x * a y) * (b x * b y) * (x * y)
        = (a x * b x * x) * (a y * b y * y) := by ac_rfl
      _ = 1 := by rw [hx, hy, one_mul]

theorem s13_seven_annihilator_irr (hW : ∀ w : W, w * w = 1) {X : Subgroup (MulAut W)}
    (hXc : IsMulCommutative ↥X) {U₀ : Subgroup W} (hIrr : IsIrrOn X U₀ ⊥) {q : MulAut W}
    (hqX : q ∈ X) (hq7 : q ^ 7 = 1) (hfix : U₀ ⊓ fixV (Subgroup.zpowers q) = ⊥) :
    (∀ w ∈ U₀, (q ^ 3) w * q w * w = 1) ∨ (∀ w ∈ U₀, (q ^ 3) w * (q ^ 2) w * w = 1) := by
  let K : Subgroup W := U₀ ⊓ MonoidHom.ker (w16g_phi2 q)
  have hmem : ∀ u ∈ U₀, w16g_phi2 q u ∈ U₀ := by
    intro u hu
    have h3 : q ^ 3 ∈ X := X.pow_mem hqX 3
    have h2 : q ^ 2 ∈ X := X.pow_mem hqX 2
    change (q ^ 3) u * (q ^ 2) u * u ∈ U₀
    exact U₀.mul_mem (U₀.mul_mem (hIrr.2.1 (q ^ 3) h3 u hu)
      (hIrr.2.1 (q ^ 2) h2 u hu)) hu
  have hKstab : StableUnder X K := by
    intro x hx u hu
    change u ∈ U₀ ⊓ MonoidHom.ker (w16g_phi2 q) at hu
    rw [Subgroup.mem_inf, MonoidHom.mem_ker] at hu
    change x u ∈ U₀ ⊓ MonoidHom.ker (w16g_phi2 q)
    rw [Subgroup.mem_inf, MonoidHom.mem_ker]
    refine ⟨hIrr.2.1 x hx u hu.1, ?_⟩
    have hxq : Commute x q := by
      have h := congrArg Subtype.val (hXc.is_comm.comm ⟨x, hx⟩ ⟨q, hqX⟩)
      exact h
    rw [w16g_phi2_equiv hxq u, hu.2, map_one]
  have hKle : K ≤ U₀ := inf_le_left
  rcases hIrr.2.2.2 K hKstab bot_le hKle with hKbot | hKtop
  · left
    let f : ↥U₀ → ↥U₀ := fun u => ⟨w16g_phi2 q (u : W), hmem u u.2⟩
    have hinj : Function.Injective f := by
      intro a b hab
      have h1 : w16g_phi2 q ((a : W) * (b : W)⁻¹) = 1 := by
        have hab' : w16g_phi2 q (a : W) = w16g_phi2 q (b : W) :=
          congrArg Subtype.val hab
        calc w16g_phi2 q ((a : W) * (b : W)⁻¹)
            = w16g_phi2 q (a : W) * (w16g_phi2 q (b : W))⁻¹ := by rw [map_mul, map_inv]
          _ = 1 := by rw [hab', mul_inv_cancel]
      have h2 : (a : W) * (b : W)⁻¹ ∈ U₀ := U₀.mul_mem a.2 (U₀.inv_mem b.2)
      have h3 : (a : W) * (b : W)⁻¹ ∈ K := ⟨h2, h1⟩
      rw [hKbot, Subgroup.mem_bot, mul_inv_eq_one] at h3
      exact Subtype.ext h3
    have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
    intro w hw
    obtain ⟨u, hu_eq⟩ := hsurj ⟨w, hw⟩
    have heq : w16g_phi2 q (u : W) = w := congrArg Subtype.val hu_eq
    have hfixP : q (w16g_P q (u : W)) = w16g_P q (u : W) := w16g_P_fix hq7 (u : W)
    have hmemP : w16g_P q (u : W) ∈ U₀ := w16g_P_mem hIrr hqX (u : W) u.2
    have hPU : w16g_P q (u : W) ∈ U₀ ⊓ fixV (Subgroup.zpowers q) :=
      ⟨hmemP, mem_fixV_zpowers_iff_apply.mpr hfixP⟩
    rw [hfix, Subgroup.mem_bot] at hPU
    rw [← heq]
    change w16g_phi1 q (w16g_phi2 q (u : W)) = 1
    rw [w16g_phi1_phi2 hW q (u : W)]
    exact hPU
  · right
    intro w hw
    have hwK : w ∈ K := by rw [hKtop]; exact hw
    have hker : w ∈ MonoidHom.ker (w16g_phi2 q) := (Subgroup.mem_inf.mp hwK).2
    exact MonoidHom.mem_ker.mp hker

theorem s13_seven_annihilator (hW : ∀ w : W, w * w = 1) {X : Subgroup (MulAut W)}
    (hXc : IsMulCommutative ↥X) {U₀ : Subgroup W} (hIrr : IsIrrOn X U₀ ⊥) {q : MulAut W}
    (hqX : q ∈ X) (hq7 : q ^ 7 = 1) (hfix : s13IsoSum X U₀ ⊓ fixV (Subgroup.zpowers q) = ⊥) :
    (∀ w ∈ s13IsoSum X U₀, (q ^ 3) w * q w * w = 1) ∨
      (∀ w ∈ s13IsoSum X U₀, (q ^ 3) w * (q ^ 2) w * w = 1) := by
  have hle : U₀ ≤ s13IsoSum X U₀ := w16g_le_s13IsoSum_self hIrr
  have hfix₀ : U₀ ⊓ fixV (Subgroup.zpowers q) = ⊥ := by
    apply le_bot_iff.mp
    calc U₀ ⊓ fixV (Subgroup.zpowers q)
        ≤ s13IsoSum X U₀ ⊓ fixV (Subgroup.zpowers q) := inf_le_inf hle le_rfl
      _ = ⊥ := hfix
  rcases s13_seven_annihilator_irr hW hXc hIrr hqX hq7 hfix₀ with h | h
  · left
    exact s13_triple_transfer (X := X) (U₀ := U₀) (a := q ^ 3) (b := q)
      (X.pow_mem hqX 3) hqX h
  · right
    exact s13_triple_transfer (X := X) (U₀ := U₀) (a := q ^ 3) (b := q ^ 2)
      (X.pow_mem hqX 3) (X.pow_mem hqX 2) h

theorem s13_seven_inverted_false {q s : MulAut W} (hsq : s * q * s⁻¹ = q⁻¹) {U : Subgroup W}
    (hsU : U.map s.toMonoidHom = U) (hfix : U ⊓ fixV (Subgroup.zpowers q) = ⊥)
    (hann : (∀ w ∈ U, (q ^ 3) w * q w * w = 1) ∨ (∀ w ∈ U, (q ^ 3) w * (q ^ 2) w * w = 1)) :
    U = ⊥ := by
  have hsq' : s⁻¹ * q * s = q⁻¹ := by
    have h : q = s⁻¹ * q⁻¹ * s := by
      calc q = s⁻¹ * (s * q * s⁻¹) * s := by group
        _ = s⁻¹ * q⁻¹ * s := by rw [hsq]
    have h3 : s⁻¹ * q * s = (s⁻¹ * q⁻¹ * s)⁻¹ := by group
    rw [h3, ← h]
  have hconj : ∀ k : ℕ, s⁻¹ * q ^ k * s = (q⁻¹) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, pow_succ]
        calc s⁻¹ * (q ^ k * q) * s = (s⁻¹ * q ^ k * s) * (s⁻¹ * q * s) := by group
          _ = (q⁻¹) ^ k * q⁻¹ := by rw [ih, hsq']
  have key1 : ∀ u : W, (q ^ 3) (s u) * q (s u) * (s u) = 1 →
      ((q⁻¹) ^ 3) u * (q⁻¹) u * u = 1 := by
    intro u h
    have h' := congrArg (fun x => (s⁻¹) x) h
    simp only [map_mul, map_one] at h'
    rw [show (s⁻¹) ((q ^ 3) (s u)) = ((q⁻¹) ^ 3) u by
          rw [← MulAut.mul_apply, ← MulAut.mul_apply, hconj 3],
        show (s⁻¹) (q (s u)) = (q⁻¹) u by
          rw [← MulAut.mul_apply, ← MulAut.mul_apply, hsq'],
        show (s⁻¹) (s u) = u by
          rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]] at h'
    exact h'
  have key2 : ∀ u : W, (q ^ 3) (s u) * (q ^ 2) (s u) * (s u) = 1 →
      ((q⁻¹) ^ 3) u * ((q⁻¹) ^ 2) u * u = 1 := by
    intro u h
    have h' := congrArg (fun x => (s⁻¹) x) h
    simp only [map_mul, map_one] at h'
    rw [show (s⁻¹) ((q ^ 3) (s u)) = ((q⁻¹) ^ 3) u by
          rw [← MulAut.mul_apply, ← MulAut.mul_apply, hconj 3],
        show (s⁻¹) ((q ^ 2) (s u)) = ((q⁻¹) ^ 2) u by
          rw [← MulAut.mul_apply, ← MulAut.mul_apply, hconj 2],
        show (s⁻¹) (s u) = u by
          rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]] at h'
    exact h'
  have key1' : ∀ u : W, ((q⁻¹) ^ 3) u * (q⁻¹) u * u = 1 →
      u * (q ^ 2) u * (q ^ 3) u = 1 := by
    intro u h
    have h' := congrArg (fun x => (q ^ 3) x) h
    simp only [map_mul, map_one] at h'
    rw [show (q ^ 3) (((q⁻¹) ^ 3) u) = u by
          rw [← MulAut.mul_apply, show q ^ 3 * (q⁻¹) ^ 3 = 1 by group, MulAut.one_apply],
        show (q ^ 3) ((q⁻¹) u) = (q ^ 2) u by
          rw [← MulAut.mul_apply, show q ^ 3 * q⁻¹ = q ^ 2 by group]] at h'
    exact h'
  have key2' : ∀ u : W, ((q⁻¹) ^ 3) u * ((q⁻¹) ^ 2) u * u = 1 →
      u * q u * (q ^ 3) u = 1 := by
    intro u h
    have h' := congrArg (fun x => (q ^ 3) x) h
    simp only [map_mul, map_one] at h'
    rw [show (q ^ 3) (((q⁻¹) ^ 3) u) = u by
          rw [← MulAut.mul_apply, show q ^ 3 * (q⁻¹) ^ 3 = 1 by group, MulAut.one_apply],
        show (q ^ 3) (((q⁻¹) ^ 2) u) = q u by
          rw [← MulAut.mul_apply, show q ^ 3 * (q⁻¹) ^ 2 = q by group]] at h'
    exact h'
  have concl : ∀ u : W, u ∈ U → (q ^ 3) u * q u * u = 1 →
      (q ^ 3) u * (q ^ 2) u * u = 1 → u = 1 := by
    intro u hu h1 h2
    have hmem : u ∈ fixV (Subgroup.zpowers q) := w16g_mem_fixV_of_cubic h1 h2
    have h : u ∈ U ⊓ fixV (Subgroup.zpowers q) := ⟨hu, hmem⟩
    rwa [hfix, Subgroup.mem_bot] at h
  apply eq_bot_iff.mpr
  intro u hu
  rw [Subgroup.mem_bot]
  have hsu : s u ∈ U := by
    have h := Subgroup.mem_map_of_mem s.toMonoidHom hu
    rwa [hsU] at h
  rcases hann with hann | hann
  · have hA : ((q⁻¹) ^ 3) u * (q⁻¹) u * u = 1 := key1 u (hann (s u) hsu)
    have hB : u * (q ^ 2) u * (q ^ 3) u = 1 := key1' u hA
    exact concl u hu (hann u hu) (by
      rwa [show u * (q ^ 2) u * (q ^ 3) u = (q ^ 3) u * (q ^ 2) u * u by ac_rfl] at hB)
  · have hA : ((q⁻¹) ^ 3) u * ((q⁻¹) ^ 2) u * u = 1 := key2 u (hann (s u) hsu)
    have hB : u * q u * (q ^ 3) u = 1 := key2' u hA
    exact concl u hu (by
      rwa [show u * q u * (q ^ 3) u = (q ^ 3) u * q u * u by ac_rfl] at hB) (hann u hu)

end CFSG.LocalAnalysis.WeakClosure81
