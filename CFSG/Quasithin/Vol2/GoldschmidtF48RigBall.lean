module

public import CFSG.Quasithin.Vol2.F48GenGeom

public section

namespace CFSG.Quasithin.H13.F48Rig

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.Quasithin.H13.F48Gen

universe u

variable {α : RankTwoAmalgam.{u}} {Y : Type} [Group Y]

abbrev Vs (c : α.Completion Y) (s : Bool) : Type := {v : c.Γ // CosetGeom.vtype v = s}

instance (c : α.Completion Y) (s : Bool) : MulAction c.G0 (Vs c s) where
  smul g z := ⟨g • z.1, (CosetGeom.vtype_smul g z.1).trans z.2⟩
  one_smul _ := Subtype.ext (one_smul _ _)
  mul_smul g h z := Subtype.ext (mul_smul g h z.1)

@[expose] def BallV (m : ℕ) (α : RankTwoAmalgam.{u}) (s : Bool) : Set α.Γhat :=
  {q | CosetGeom.vtype q = s ∧ α.graphHat.dist lhat q ≤ m - 1}

theorem dist_lv_le_sType (c : α.Completion Y) {m : ℕ} (hD : ∀ u v : c.Γ, c.graph.dist u v ≤ m)
    {z : c.Γ} (hz : CosetGeom.vtype z = decide (Odd m)) : c.graph.dist c.lv z ≤ m - 1 := by
  have hpar := GPath.dist_even_iff (connected_graph c)
    (fun _ _ h => CosetGeom.vtype_ne_of_adj h) c.lv z
  have h3 := hD c.lv z
  rcases Nat.even_or_odd m with hm | hm
  · have h0 : decide (Odd m) = false := decide_eq_false (Nat.not_odd_iff_even.mpr hm)
    rw [h0] at hz
    have h1 : CosetGeom.vtype c.lv ≠ CosetGeom.vtype z := by
      show true ≠ _
      rw [hz]
      decide
    have h2 : ¬ Even (c.graph.dist c.lv z) := fun he => h1 (hpar.2 he)
    rcases Nat.lt_or_ge (c.graph.dist c.lv z) m with h | h
    · omega
    · exact absurd (by have : c.graph.dist c.lv z = m := by omega
                       rw [this]; exact hm) h2
  · have h0 : decide (Odd m) = true := decide_eq_true hm
    rw [h0] at hz
    have h1 : CosetGeom.vtype c.lv = CosetGeom.vtype z := by
      show true = _
      rw [hz]
    have h2 : Even (c.graph.dist c.lv z) := hpar.1 h1
    rcases Nat.lt_or_ge (c.graph.dist c.lv z) m with h | h
    · omega
    · have : c.graph.dist c.lv z = m := by omega
      rw [this] at h2
      exact absurd h2 (Nat.not_even_iff_odd.mpr hm)

section Ball

variable (c : α.Completion Y) (hc : c.IsFaithful) {m : ℕ} (s : Bool)

@[expose] noncomputable def ballEquivV (F : Facts46 c m)
    (hs : ∀ z : c.Γ, CosetGeom.vtype z = s → c.graph.dist c.lv z ≤ m - 1) :
    ↥(BallV m α s) ≃ Vs c s :=
  Equiv.ofBijective (fun q => ⟨c.Θ hc q.1, by rw [Θ_vtype c hc]; exact q.2.1⟩)
    ⟨fun q q' h => Subtype.ext (Θ_inj_ball c hc F q.2.2 q'.2.2 (congrArg Subtype.val h)),
      fun z => by
        obtain ⟨q, hq, hz⟩ := exists_lift_ball c hc (hs z.1 z.2)
        refine ⟨⟨q, ?_, hq⟩, Subtype.ext hz⟩
        rw [← Θ_vtype c hc q, hz]
        exact z.2⟩

end Ball

section Equiv

variable {Y' : Type} [Group Y'] (c : α.Completion Y) (d : α.Completion Y')
  (hc : c.IsFaithful) (hd : d.IsFaithful) {m : ℕ} (s : Bool) (Fc : Facts46 c m) (Fd : Facts46 d m)
  (hsc : ∀ z : c.Γ, CosetGeom.vtype z = s → c.graph.dist c.lv z ≤ m - 1)
  (hsd : ∀ z : d.Γ, CosetGeom.vtype z = s → d.graph.dist d.lv z ≤ m - 1)

@[expose] noncomputable def vEquiv : Vs c s ≃ Vs d s :=
  (ballEquivV c hc s Fc hsc).symm.trans (ballEquivV d hd s Fd hsd)

theorem vEquiv_ball {q : ↥(BallV m α s)} :
    vEquiv c d hc hd s Fc Fd hsc hsd (ballEquivV c hc s Fc hsc q) = ballEquivV d hd s Fd hsd q := by
  simp [vEquiv]

theorem ballEquivV_xi2 (a : α.G2) (q : ↥(BallV m α s)) (hq : α.xi2 a • q.1 ∈ BallV m α s) :
    ballEquivV c hc s Fc hsc ⟨α.xi2 a • q.1, hq⟩ = f2 (c := c) a • ballEquivV c hc s Fc hsc q := by
  apply Subtype.ext
  show c.Θ hc (α.xi2 a • q.1) = f2 (c := c) a • c.Θ hc q.1
  rw [c.Θ_smul hc, theta0_xi2]

theorem xi2_mem_BallV (a : α.G2) {q : α.Γhat} (hq : q ∈ BallV m α s) :
    α.xi2 a • q ∈ BallV m α s := by
  refine ⟨by rw [CosetGeom.vtype_smul]; exact hq.1, ?_⟩
  have h := CosetGeom.dist_smul (α.xi2 a) lhat q
  rw [xi2_smul_lhat] at h
  rw [CosetGeom.dist] at h
  show α.graphHat.dist lhat (α.xi2 a • q) ≤ m - 1
  rw [h]
  exact hq.2

theorem vEquiv_f2 (a : α.G2) (z : Vs c s) :
    vEquiv c d hc hd s Fc Fd hsc hsd (f2 (c := c) a • z) =
      f2 (c := d) a • vEquiv c d hc hd s Fc Fd hsc hsd z := by
  obtain ⟨q, rfl⟩ := (ballEquivV c hc s Fc hsc).surjective z
  rw [← ballEquivV_xi2 c hc s Fc hsc a q (xi2_mem_BallV s a q.2),
    vEquiv_ball, vEquiv_ball, ballEquivV_xi2 d hd s Fd hsd a q (xi2_mem_BallV s a q.2)]

section Near

@[expose] def NearV (m : ℕ) (c : α.Completion Y) (z : c.Γ) : Prop := c.graph.dist c.xv z ≤ m - 2

@[expose] def NearHV (m : ℕ) (α : RankTwoAmalgam.{u}) : Set α.Γhat :=
  {q | α.graphHat.dist xhat q ≤ m - 2}

theorem NearHV_sub_BallV {m : ℕ} (hm : 2 ≤ m) {q : α.Γhat} (hq : q ∈ NearHV m α)
    (hs : CosetGeom.vtype q = s) : q ∈ BallV m α s := by
  refine ⟨hs, ?_⟩
  have hadj : α.graphHat.Adj xhat lhat := CosetGeom.adj_γ₀_γ₁
  have h1 : α.graphHat.dist lhat xhat = 1 := by
    rw [SimpleGraph.dist_comm]
    exact SimpleGraph.dist_eq_one_iff_adj.mpr hadj
  have h2 := hat_connected.dist_triangle (u := lhat) (v := xhat) (w := q)
  have : α.graphHat.dist xhat q ≤ m - 2 := hq
  show α.graphHat.dist lhat q ≤ m - 1
  omega

theorem xi1_mem_NearHV (a : α.G1) {q : α.Γhat} (hq : q ∈ NearHV m α) :
    α.xi1 a • q ∈ NearHV m α := by
  show α.graphHat.dist xhat (α.xi1 a • q) ≤ m - 2
  have h := CosetGeom.dist_smul (α.xi1 a) xhat q
  rw [xi1_smul_xhat] at h
  rw [CosetGeom.dist] at h
  rw [h]
  exact hq

variable {m : ℕ}

theorem exists_near_lift (c : α.Completion Y) (hc : c.IsFaithful) {z : c.Γ}
    (hz : NearV m c z) : ∃ q ∈ NearHV m α, c.Θ hc q = z := by
  obtain ⟨u, hu, hΘ⟩ := exists_lift_at c hc xhat (z := z) (n := m - 2)
    (by rw [Θ_xhat]; exact hz)
  exact ⟨u, hu, hΘ⟩

theorem NearV_Θ (c : α.Completion Y) (hc : c.IsFaithful) {q : α.Γhat} (hq : q ∈ NearHV m α) :
    NearV m c (c.Θ hc q) := by
  have h := dist_Θ_le c hc xhat q
  rw [Θ_xhat] at h
  exact h.trans hq

end Near

section NearEquiv

variable {Y' : Type} [Group Y'] (c : α.Completion Y) (d : α.Completion Y')
  (hc : c.IsFaithful) (hd : d.IsFaithful) {m : ℕ} (s : Bool) (Fc : Facts46 c m) (Fd : Facts46 d m)
  (hsc : ∀ z : c.Γ, CosetGeom.vtype z = s → c.graph.dist c.lv z ≤ m - 1)
  (hsd : ∀ z : d.Γ, CosetGeom.vtype z = s → d.graph.dist d.lv z ≤ m - 1)

theorem ballEquivV_xi1 (a : α.G1) (q : ↥(BallV m α s)) (hq : α.xi1 a • q.1 ∈ BallV m α s) :
    ballEquivV c hc s Fc hsc ⟨α.xi1 a • q.1, hq⟩ = f1 (c := c) a • ballEquivV c hc s Fc hsc q := by
  apply Subtype.ext
  show c.Θ hc (α.xi1 a • q.1) = f1 (c := c) a • c.Θ hc q.1
  rw [c.Θ_smul hc, theta0_xi1]

theorem exists_near_ball (hm : 2 ≤ m) (z : Vs c s) (hz : NearV m c z.1) :
    ∃ q : ↥(BallV m α s), q.1 ∈ NearHV m α ∧ ballEquivV c hc s Fc hsc q = z := by
  obtain ⟨q, hq, hΘ⟩ := exists_near_lift c hc hz
  have hs : CosetGeom.vtype q = s := by rw [← Θ_vtype c hc q, hΘ]; exact z.2
  exact ⟨⟨q, NearHV_sub_BallV s hm hq hs⟩, hq, Subtype.ext hΘ⟩

theorem vEquiv_f1 (hm : 2 ≤ m) (a : α.G1) (z : Vs c s) (hz : NearV m c z.1) :
    vEquiv c d hc hd s Fc Fd hsc hsd (f1 (c := c) a • z) =
      f1 (c := d) a • vEquiv c d hc hd s Fc Fd hsc hsd z := by
  obtain ⟨q, hqn, rfl⟩ := exists_near_ball c hc s Fc hsc hm z hz
  have hq' : α.xi1 a • q.1 ∈ BallV m α s :=
    NearHV_sub_BallV s hm (xi1_mem_NearHV a hqn) (by rw [CosetGeom.vtype_smul]; exact q.2.1)
  rw [← ballEquivV_xi1 c hc s Fc hsc a q hq', vEquiv_ball, vEquiv_ball,
    ballEquivV_xi1 d hd s Fd hsd a q hq']

theorem vEquiv_near (hm : 2 ≤ m) (z : Vs c s) :
    NearV m d (vEquiv c d hc hd s Fc Fd hsc hsd z).1 ↔ NearV m c z.1 := by
  constructor
  · intro h
    obtain ⟨q, hqn, hq⟩ := exists_near_ball d hd s Fd hsd hm _ h
    obtain ⟨q', rfl⟩ := (ballEquivV c hc s Fc hsc).surjective z
    have e : vEquiv c d hc hd s Fc Fd hsc hsd (ballEquivV c hc s Fc hsc q') =
        ballEquivV d hd s Fd hsd q' := vEquiv_ball c d hc hd s Fc Fd hsc hsd
    rw [e] at hq
    have := (ballEquivV d hd s Fd hsd).injective hq
    rw [this] at hqn
    exact NearV_Θ c hc hqn
  · intro h
    obtain ⟨q, hqn, rfl⟩ := exists_near_ball c hc s Fc hsc hm z h
    rw [vEquiv_ball]
    exact NearV_Θ d hd hqn

end NearEquiv

end Equiv

end CFSG.Quasithin.H13.F48Rig
