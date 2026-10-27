module
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.Decomposition
public section
namespace CFSG.LocalAnalysis.WeakClosure81.OddCentral
open Subgroup

section
variable {G M : Type*} [Group G] [Finite G] [AddCommGroup M] [Finite M] [DistribMulAction G M]

theorem mem_of_sq_mem {V H : Subgroup G} (hVodd : Odd (Nat.card V)) {w : G} (hw : w ∈ V)
    (h : w * w ∈ H) : w ∈ H := by
  obtain ⟨n, hn⟩ := hVodd
  have h1 : w ^ Nat.card V = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard V hw)
  have : (w * w) ^ (n + 1) = w := by
    rw [← sq, ← pow_mul, show 2 * (n + 1) = Nat.card V + 1 by omega, pow_succ, h1, one_mul]
  rw [← this]; exact pow_mem h _

theorem mem_normalizer_of_conj_mem {H : Subgroup G} {g : G} (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    g ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩; exact h x hx
  · rw [Subgroup.card_map_of_injective (f := (MulAut.conj g : G →* G))
      (fun a b hab => by simpa using hab)]

theorem orbit_prod_eq_one {V : Subgroup G} [hVn : V.Normal]
    (hVab : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) {x u : G} (hx : x * x = 1) (hu : u * u = 1)
    (hxu : x * u = u * x) (hC : ∀ w ∈ V, x * w * x⁻¹ = w → u * w * u⁻¹ = w → w = 1)
    {v : G} (hv : v ∈ V) :
    v * (x * v * x⁻¹) * (u * v * u⁻¹) * ((x * u) * v * (x * u)⁻¹) = 1 := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have cV : ∀ g : G, g * v * g⁻¹ ∈ V := fun g => hVn.conj_mem v hv g
  have e1 : x * x * v * (x * x)⁻¹ = v := by rw [hx]; group
  have e2 : u * u * v * (u * u)⁻¹ = v := by rw [hu]; group
  apply hC
  · apply V.mul_mem (V.mul_mem (V.mul_mem hv (cV _)) (cV _)) (cV _)
  · calc x * (v * (x * v * x⁻¹) * (u * v * u⁻¹) * ((x * u) * v * (x * u)⁻¹)) * x⁻¹
        = (x * v * x⁻¹) * (x * x * v * (x * x)⁻¹) * ((x * u) * v * (x * u)⁻¹) *
          ((x * x * u) * v * (x * x * u)⁻¹) := by group
      _ = (x * v * x⁻¹) * v * ((x * u) * v * (x * u)⁻¹) * (u * v * u⁻¹) := by
          rw [e1, hx, one_mul]
      _ = v * (x * v * x⁻¹) * (u * v * u⁻¹) * ((x * u) * v * (x * u)⁻¹) := by
          rw [hVab _ (cV x) _ hv, mul_assoc _ ((x * u) * v * (x * u)⁻¹),
            hVab _ (cV (x * u)) _ (cV u), ← mul_assoc]
  · calc u * (v * (x * v * x⁻¹) * (u * v * u⁻¹) * ((x * u) * v * (x * u)⁻¹)) * u⁻¹
        = (u * v * u⁻¹) * ((u * x) * v * (u * x)⁻¹) * (u * u * v * (u * u)⁻¹) *
          ((u * x * u) * v * (u * x * u)⁻¹) := by group
      _ = (u * v * u⁻¹) * ((x * u) * v * (x * u)⁻¹) * v * (x * v * x⁻¹) := by
          rw [e2, ← hxu, mul_assoc x u u, hu, mul_one]
      _ = v * (x * v * x⁻¹) * (u * v * u⁻¹) * ((x * u) * v * (x * u)⁻¹) := by
          rw [mul_assoc _ v (x * v * x⁻¹)]
          rw [hVab (u * v * u⁻¹ * (x * u * v * (x * u)⁻¹)) (V.mul_mem (cV u) (cV _))
            (v * (x * v * x⁻¹)) (V.mul_mem hv (cV x))]
          group

theorem neg_of_frame_fix {V H : Subgroup G} [hVn : V.Normal] (hVodd : Odd (Nat.card V))
    (hVab : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) (hHV : H ≤ V) {x u : G} (hx : x * x = 1)
    (hu : u * u = 1) (hxu : x * u = u * x)
    (hC : ∀ w ∈ V, x * w * x⁻¹ = w → u * w * u⁻¹ = w → w = 1)
    (hP : ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ H) : ∀ v ∈ V, u * v * u⁻¹ * v ∈ H := by
  intro v hv
  have cV : ∀ g : G, g * v * g⁻¹ ∈ V := fun g => hVn.conj_mem v hv g
  have hprod := orbit_prod_eq_one hVab hx hu hxu hC hv
  set w := u * v * u⁻¹ with hw
  have hwV : w ∈ V := cV u
  have ha := hP v hv
  have hb := hP w hwV
  have hxw : (x * u) * v * (x * u)⁻¹ = x * w * x⁻¹ := by rw [hw]; group
  rw [hxw] at hprod
  have key : (w * v) * (w * v) = ((x * v * x⁻¹ * v⁻¹) * (x * w * x⁻¹ * w⁻¹))⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← hprod]
    have c1 := hVab _ (cV x) _ hv
    have c2 := hVab _ hwV _ hv
    have c3 := hVab _ (hVn.conj_mem w hwV x) _ hwV
    have c4 := hVab _ (hVn.conj_mem w hwV x) _ hv
    have c5 := hVab _ (hVn.conj_mem w hwV x) _ (cV x)
    have c6 := hVab _ (V.inv_mem hv) _ hwV
    have c7 := hVab _ (V.inv_mem hv) _ (hVn.conj_mem w hwV x)
    have c8 := hVab _ (V.inv_mem hwV) _ hv
    have c9 := hVab _ (cV x) _ hwV
    calc w * v * (w * v) * (x * v * x⁻¹ * v⁻¹ * (x * w * x⁻¹ * w⁻¹))
        = w * v * w * (v * (x * v * x⁻¹)) * v⁻¹ * (x * w * x⁻¹) * w⁻¹ := by group
      _ = w * v * w * ((x * v * x⁻¹) * v) * v⁻¹ * (x * w * x⁻¹) * w⁻¹ := by rw [c1]
      _ = (w * v) * (w * (x * v * x⁻¹)) * (x * w * x⁻¹) * w⁻¹ := by group
      _ = (v * w) * ((x * v * x⁻¹) * w) * (x * w * x⁻¹) * w⁻¹ := by rw [c2, c9]
      _ = v * (w * (x * v * x⁻¹)) * (w * (x * w * x⁻¹)) * w⁻¹ := by group
      _ = v * ((x * v * x⁻¹) * w) * ((x * w * x⁻¹) * w) * w⁻¹ := by rw [c9, c3]
      _ = v * (x * v * x⁻¹) * w * (x * w * x⁻¹) := by group
  have hmem : (w * v) * (w * v) ∈ H := by
    rw [key]; exact H.inv_mem (H.mul_mem ha hb)
  have := mem_of_sq_mem hVodd (V.mul_mem hwV hv) hmem
  exact this


theorem smul_conj_inv (g a : G) (y : M) : a • (g⁻¹ • y) = g⁻¹ • ((g * a * g⁻¹) • y) := by
  rw [mul_smul, mul_smul, inv_smul_smul]

theorem false_of_frame_hyperplane {V H : Subgroup G} [hVn : V.Normal]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card M)) (hModd : Odd (Nat.card M))
    (hVab : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) (hVodd : Odd (Nat.card V)) (hHV : H ≤ V)
    (hHmax : ∀ K : Subgroup G, H ≤ K → K ≤ V → K = H ∨ K = V) (hHV' : H ≠ V)
    (hM0 : ∀ m : M, (∀ v ∈ V, v • m = m) → m = 0)
    {x : M} (hxH : ∀ h ∈ H, h • x = x) (hx0 : x ≠ 0)
    {c t : G} {z : Fin 3 → G} (hc : c * c = 1) (hz : ∀ a, z a * z a = 1)
    (hz2 : z 2 = z 0 * z 1) (hcz : ∀ a, c * z a = z a * c) (h01 : z 0 * z 1 = z 1 * z 0)
    (hcV : ∀ v ∈ V, c * v * c⁻¹ = v⁻¹)
    (hT : ∀ v ∈ V, z 0 * v * (z 0)⁻¹ = v → z 1 * v * (z 1)⁻¹ = v → v = 1)
    (hLA : ∀ m : M, ∀ a, c • m = m → z a • m = -m → m = 0)
    (ht : ∀ a, t * z a * t⁻¹ = z (a + 1))
    (hgen : normalClosure ({c * z 0} : Set G) = ⊤) : False := by
  classical
  have conj_mul : ∀ g a b : G, (g * a * g⁻¹) * (g * b * g⁻¹) = g * (a * b) * g⁻¹ :=
    fun g a b => by group
  have c02 : z 0 * z 2 = z 2 * z 0 := by rw [hz2, mul_assoc (z 0) (z 1) (z 0), ← h01]
  have c12 : z 1 * z 2 = z 2 * z 1 := by rw [hz2, ← mul_assoc, ← h01]
  have hzc : ∀ a b, z a * z b = z b * z a := by
    intro a b
    fin_cases a <;> fin_cases b <;>
      first | rfl | exact h01 | exact h01.symm | exact c02 | exact c02.symm | exact c12 | exact c12.symm
  have hconjV : ∀ g : G, ∀ v ∈ V, g⁻¹ * v * g ∈ V := fun g v hv => by
    simpa using hVn.conj_mem v hv g⁻¹
  have hCg : ∀ g : G, ∀ a b : Fin 3, a ≠ b → ∀ w ∈ V, (g * z a * g⁻¹) * w * (g * z a * g⁻¹)⁻¹ = w →
      (g * z b * g⁻¹) * w * (g * z b * g⁻¹)⁻¹ = w → w = 1 := by
    intro g a b hab w hw ha hb
    have ka : z a * (g⁻¹ * w * g) * (z a)⁻¹ = g⁻¹ * w * g := by
      calc z a * (g⁻¹ * w * g) * (z a)⁻¹
          = g⁻¹ * ((g * z a * g⁻¹) * w * (g * z a * g⁻¹)⁻¹) * g := by group
        _ = g⁻¹ * w * g := by rw [ha]
    have kb : z b * (g⁻¹ * w * g) * (z b)⁻¹ = g⁻¹ * w * g := by
      calc z b * (g⁻¹ * w * g) * (z b)⁻¹
          = g⁻¹ * ((g * z b * g⁻¹) * w * (g * z b * g⁻¹)⁻¹) * g := by group
        _ = g⁻¹ * w * g := by rw [hb]
    have h2 := fix_all_of_fix_two hz2 hab ka kb
    have h1 := hT _ (hconjV g w hw) h2.1 h2.2
    calc w = g * (g⁻¹ * w * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hstep1 : ∀ g : G, ∃ b : Fin 3,
      ∀ v ∈ V, (g * z b * g⁻¹) * v * (g * z b * g⁻¹)⁻¹ * v⁻¹ ∈ H := by
    intro g
    have hcV' : ∀ v ∈ V, (g * c * g⁻¹) * v * (g * c * g⁻¹)⁻¹ = v⁻¹ := by
      intro v hv
      calc (g * c * g⁻¹) * v * (g * c * g⁻¹)⁻¹ = g * (c * (g⁻¹ * v * g) * c⁻¹) * g⁻¹ := by group
        _ = v⁻¹ := by rw [hcV _ (hconjV g v hv)]; group
    have hLA' : ∀ y : M, ∀ u ∈ ({g * z 0 * g⁻¹, g * z 1 * g⁻¹,
        (g * z 0 * g⁻¹) * (g * z 1 * g⁻¹)} : Set G),
        (g * c * g⁻¹) • y = y → u • y = -y → y = 0 := by
      intro y u hu hcy huy
      have hc0 : c • (g⁻¹ • y) = g⁻¹ • y := by rw [smul_conj_inv, hcy]
      have key : ∀ a, (g * z a * g⁻¹) • y = -y → y = 0 := fun a h => by
        have h' : z a • (g⁻¹ • y) = -(g⁻¹ • y) := by rw [smul_conj_inv, h, smul_neg]
        have := hLA _ a hc0 h'
        simpa using congrArg (g • ·) this
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl | rfl
      · exact key 0 huy
      · exact key 1 huy
      · rw [conj_mul, ← hz2] at huy; exact key 2 huy
    obtain ⟨u, hu, -, hP⟩ := exists_fix_hyperplane (M₁ := ⊤) hcop hModd hVab hVodd hHV hHmax
      hHV' (fun _ _ _ _ => trivial) (fun m _ hm => hM0 m hm) (c := g * c * g⁻¹)
      (z₁ := g * z 0 * g⁻¹) (z₂ := g * z 1 * g⁻¹) (fun _ _ => trivial) (fun _ _ => trivial)
      (fun _ _ => trivial) (by rw [conj_mul, hc]; group) (by rw [conj_mul, hz 0]; group)
      (by rw [conj_mul, hz 1]; group) (by rw [conj_mul, conj_mul, hcz 0])
      (by rw [conj_mul, conj_mul, hcz 1]) (by rw [conj_mul, conj_mul, h01]) hcV'
      (fun v hv => hVn.conj_mem v hv _) (fun v hv => hVn.conj_mem v hv _) hLA' trivial hxH hx0
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl
    · exact ⟨0, hP⟩
    · exact ⟨1, hP⟩
    · exact ⟨2, by rw [hz2, ← conj_mul]; exact hP⟩
  have hnormP : ∀ y : G, (∀ v ∈ V, y * v * y⁻¹ * v⁻¹ ∈ H) → ∀ h ∈ H, y * h * y⁻¹ ∈ H :=
    fun y hy h hh => by
      have := H.mul_mem (hy h (hHV hh)) hh
      simpa using this
  have hnormN : ∀ y : G, (∀ v ∈ V, y * v * y⁻¹ * v ∈ H) → ∀ h ∈ H, y * h * y⁻¹ ∈ H :=
    fun y hy h hh => by
      have := H.mul_mem (hy h (hHV hh)) (H.inv_mem hh)
      simpa using this
  have hstep2 : ∀ g : G, ∀ a, ∀ h ∈ H, (g * z a * g⁻¹) * h * (g * z a * g⁻¹)⁻¹ ∈ H := by
    intro g a
    obtain ⟨b, hb⟩ := hstep1 g
    by_cases hab : a = b
    · subst hab; exact hnormP _ hb
    · apply hnormN
      exact neg_of_frame_fix hVodd hVab hHV (by rw [conj_mul, hz b]; group)
        (by rw [conj_mul, hz a]; group) (by rw [conj_mul, conj_mul, hzc b a])
        (fun w hw h1 h2 => hCg g b a (Ne.symm hab) w hw h1 h2) hb
  have hstep3 : ∀ g : G, ∀ h ∈ H, (g * c * g⁻¹) * h * (g * c * g⁻¹)⁻¹ ∈ H := by
    intro g
    apply hnormN
    intro v hv
    have : (g * c * g⁻¹) * v * (g * c * g⁻¹)⁻¹ = v⁻¹ := by
      calc (g * c * g⁻¹) * v * (g * c * g⁻¹)⁻¹ = g * (c * (g⁻¹ * v * g) * c⁻¹) * g⁻¹ := by group
        _ = v⁻¹ := by rw [hcV _ (hconjV g v hv)]; group
    rw [this, inv_mul_cancel]; exact H.one_mem
  have hle : normalClosure ({c * z 0} : Set G) ≤ normalizer (H : Set G) := by
    show closure (Group.conjugatesOfSet {c * z 0}) ≤ _
    rw [closure_le]
    intro y hy
    obtain ⟨d, hd, hdy⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    rw [Set.mem_singleton_iff] at hd
    subst hd
    obtain ⟨g, rfl⟩ := isConj_iff.mp hdy
    rw [show g * (c * z 0) * g⁻¹ = (g * c * g⁻¹) * (g * z 0 * g⁻¹) by group]
    exact mul_mem (mem_normalizer_of_conj_mem (hstep3 g))
      (mem_normalizer_of_conj_mem (hstep2 g 0))
  have hHn : ∀ g : G, ∀ h ∈ H, g * h * g⁻¹ ∈ H := by
    intro g h hh
    have hg : g ∈ normalizer (H : Set G) := hle (by rw [hgen]; exact mem_top g)
    exact (mem_normalizer_iff.mp hg h).mp hh
  obtain ⟨b, hb⟩ := hstep1 1
  simp only [one_mul, inv_one, mul_one] at hb
  have hrot : ∀ a, (∀ v ∈ V, z a * v * (z a)⁻¹ * v⁻¹ ∈ H) →
      ∀ v ∈ V, z (a + 1) * v * (z (a + 1))⁻¹ * v⁻¹ ∈ H := by
    intro a ha v hv
    rw [← ht a]
    have := hHn t _ (ha _ (hconjV t v hv))
    rw [show t * z a * t⁻¹ * v * (t * z a * t⁻¹)⁻¹ * v⁻¹
        = t * (z a * (t⁻¹ * v * t) * (z a)⁻¹ * (t⁻¹ * v * t)⁻¹) * t⁻¹ by group]
    exact this
  have hP : ∀ a, ∀ v ∈ V, z a * v * (z a)⁻¹ * v⁻¹ ∈ H := by
    intro a
    have key : ∀ a b : Fin 3, a = b ∨ a = b + 1 ∨ a = b + 1 + 1 := by decide
    rcases key a b with rfl | rfl | rfl
    · exact hb
    · exact hrot _ hb
    · exact hrot _ (hrot _ hb)
  apply hHV'
  refine le_antisymm hHV fun v hv => ?_
  have hN := neg_of_frame_fix hVodd hVab hHV (hz 0) (hz 1) h01 hT (hP 0) v hv
  have hP1 := hP 1 v hv
  apply mem_of_sq_mem hVodd hv
  have := H.mul_mem (H.inv_mem hP1) hN
  rwa [show (z 1 * v * (z 1)⁻¹ * v⁻¹)⁻¹ * (z 1 * v * (z 1)⁻¹ * v) = v * v by group] at this

end

end CFSG.LocalAnalysis.WeakClosure81.OddCentral

