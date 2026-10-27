module

public import CFSG.Sporadic.Co2Smith.RigidCenter

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Certificates.ExtraspecialNF

universe u

theorem frS_p12_0 :

    frS 6 * frS 0 = frS 2 * frS 6 := frS_p12 (k := 0) (by norm_num)

theorem frS_p23_2 :

    frS 7 * frS 2 = frS 4 * frS 7 := frS_p23 (k := 2) (by norm_num)

theorem frS_y_pow'
    (k : ℕ) (hk : k = 0 ∨ k = 2 ∨ k = 4) : frS k ^ 3 = 1 := by
  rcases hk with rfl | rfl | rfl
  · exact frS_y_pow (i := 0) (by norm_num)
  · exact frS_y_pow (i := 1) (by norm_num)
  · exact frS_y_pow (i := 2) (by norm_num)

theorem frS_comm'
    {k l : ℕ} (hk : k < 6) (hl : l < 6) (hkl : k / 2 ≠ l / 2) :
    frS k * frS l = frS l * frS k := by
  have h := frS_comm (i := k / 2) (j := l / 2) (by omega) (by omega) hkl (e := k % 2)
    (e' := l % 2) (by omega) (by omega)
  rwa [Nat.div_add_mod, Nat.div_add_mod] at h

theorem sq_eq_imp {n m : ℕ} (h : n ^ 2 = m ^ 2) : n = m :=
  Nat.pow_left_injective (by norm_num) h

namespace LocalConfig

variable (c : LocalConfig.{u})

theorem comm_center :
    ∀ a b : c.E, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center c.E :=
  c.center_structure.2.1

@[expose] def M : Type u := c.E ⧸ Subgroup.center c.E

noncomputable instance : Group c.M :=
  inferInstanceAs (Group (c.E ⧸ Subgroup.center c.E))

noncomputable instance :
    CommGroup c.M :=
  { (inferInstance : Group c.M) with
    mul_comm := c.quot_comm _ c.comm_center }

instance : Finite c.M := inferInstanceAs (Finite (c.E ⧸ Subgroup.center c.E))

@[expose] noncomputable def piM : c.E →* c.M := QuotientGroup.mk' (Subgroup.center c.E)

theorem piM_surjective : Function.Surjective c.piM := QuotientGroup.mk'_surjective _

theorem piM_eq_one_iff
    (e : c.E) : c.piM e = 1 ↔ e ∈ Subgroup.center c.E :=
  QuotientGroup.eq_one_iff e

theorem card_M :
    Nat.card c.M = 2 ^ 8 := by
  have h := c.card_quot_mul (Subgroup.center c.E)
  rw [c.center_structure.1] at h
  show Nat.card (c.E ⧸ Subgroup.center c.E) = 2 ^ 8
  omega

theorem sq_M
    (m : c.M) : m * m = 1 := c.center_structure.2.2.1 m

theorem inv_M
    (m : c.M) : m⁻¹ = m := inv_eq_of_mul_eq_one_right (c.sq_M m)

@[expose] noncomputable def mA
    (g : S0) : c.M →* c.M := c.sA (Subgroup.center c.E) c.comm_center g

theorem mA_piM_of
    {g : S0} {h : c.H} (hgh : (QuotientGroup.mk h : c.H ⧸ c.E) = c.ψ g)
    (e : c.E) : c.mA g (c.piM e) = c.piM (c.cE h e) := by
  rw [mA, c.sA_eq_secAct _ _ hgh]
  rfl

theorem mA_piM
    (g : S0) (e : c.E) : c.mA g (c.piM e) = c.piM (c.cE (c.ℓ g) e) :=
  c.mA_piM_of (c.ℓ_mk g) e

theorem mA_piM_fr
    (k : ℕ) (e : c.E) : c.mA (frS k) (c.piM e) = c.piM (c.cE (c.fr k) e) :=
  c.mA_piM (frS k) e

theorem mA_mul
    (g h : S0) (m : c.M) : c.mA (g * h) m = c.mA g (c.mA h m) :=
  c.sA_mul _ _ g h m

theorem mA_one
    (m : c.M) : c.mA 1 m = m := c.sA_one _ _ m

theorem mA_inv
    (g : S0) (m : c.M) : c.mA g (c.mA g⁻¹ m) = m := by
  rw [← mA_mul, mul_inv_cancel, mA_one]

theorem mA_inv'
    (g : S0) (m : c.M) : c.mA g⁻¹ (c.mA g m) = m := by
  rw [← mA_mul, inv_mul_cancel, mA_one]

theorem mA_injective
    (g : S0) : Function.Injective (c.mA g) := fun m n h => by
  rw [← c.mA_inv' g m, h, c.mA_inv']

theorem mA_comm_of
    {g h : S0} (hgh : g * h = h * g) (m : c.M) :
    c.mA g (c.mA h m) = c.mA h (c.mA g m) := by
  rw [← mA_mul, hgh, mA_mul]

theorem mA_conj_of
    {p g g' : S0} (hp : p * g = g' * p) (m : c.M) :
    c.mA p (c.mA g m) = c.mA g' (c.mA p m) := by
  rw [← mA_mul, hp, mA_mul]

theorem y1_fpf
    (m : c.M) (h : c.mA (frS 0) m = m) : m = 1 :=
  c.center_structure.2.2.2 c.comm_center m h

theorem fpf_of_conj
    {p g g' : S0} (hp : p * g = g' * p)
    (hg : ∀ m, c.mA g m = m → m = 1) (m : c.M) (h : c.mA g' m = m) : m = 1 := by
  have h1 : c.mA g (c.mA p⁻¹ m) = c.mA p⁻¹ m := by
    apply c.mA_injective p
    rw [c.mA_conj_of hp, c.mA_inv, h]
  have h2 := hg _ h1
  rw [← c.mA_inv p m, h2, map_one]

theorem y2_fpf
    (m : c.M) (h : c.mA (frS 2) m = m) : m = 1 :=
  c.fpf_of_conj frS_p12_0 c.y1_fpf m h

theorem y3_fpf
    (m : c.M) (h : c.mA (frS 4) m = m) : m = 1 :=
  c.fpf_of_conj frS_p23_2 c.y2_fpf m h

theorem mA_y3
    (k : ℕ) (hk : k = 0 ∨ k = 2 ∨ k = 4) (m : c.M) :
    c.mA (frS k) (c.mA (frS k) (c.mA (frS k) m)) = m := by
  rw [← mA_mul, ← mA_mul, ← pow_three', frS_y_pow' k hk, mA_one]

theorem mA_s2
    (i : ℕ) (hi : i < 3) (m : c.M) :
    c.mA (frS (2 * i + 1)) (c.mA (frS (2 * i + 1)) m) = m := by
  rw [← mA_mul, frS_s_sq hi, mA_one]

theorem mA_sy
    (i : ℕ) (hi : i < 3) (m : c.M) :
    c.mA (frS (2 * i + 1)) (c.mA (frS (2 * i)) (c.mA (frS (2 * i + 1)) m)) =
      c.mA (frS (2 * i)) (c.mA (frS (2 * i)) m) := by
  rw [← mA_mul, ← mA_mul, ← mA_mul, frS_s_y hi]

theorem yy_eq
    {k : ℕ} (hk : k = 0 ∨ k = 2 ∨ k = 4) (hfpf : ∀ m, c.mA (frS k) m = m → m = 1)
    (m : c.M) : c.mA (frS k) (c.mA (frS k) m) = m * c.mA (frS k) m := by
  set y := c.mA (frS k)
  have ht : y (m * y m * y (y m)) = m * y m * y (y m) := by
    rw [map_mul, map_mul, c.mA_y3 k hk, mul_comm (y m * y (y m)) m, ← mul_assoc]
  have h1 := hfpf _ ht
  have h2 : y (y m) = (m * y m)⁻¹ := eq_inv_of_mul_eq_one_right h1
  rw [h2, c.inv_M]

@[expose] noncomputable def C1 :
    Subgroup c.M := ⊤ ⊓ fixSub (c.mA (frS 1))

@[expose] noncomputable def C12 :
    Subgroup c.M := c.C1 ⊓ fixSub (c.mA (frS 3))

@[expose] noncomputable def C123 :
    Subgroup c.M := c.C12 ⊓ fixSub (c.mA (frS 5))

theorem mA_comm'
    {k l : ℕ} (hk : k < 6) (hl : l < 6) (hkl : k / 2 ≠ l / 2) (m : c.M) :
    c.mA (frS k) (c.mA (frS l) m) = c.mA (frS l) (c.mA (frS k) m) :=
  c.mA_comm_of (frS_comm' hk hl hkl) m

theorem decomp1 :
    Nat.card c.C1 ^ 2 = 2 ^ 8 ∧
    ∀ m : c.M, ∃ x ∈ c.C1, ∃ x' ∈ c.C1, m = x * c.mA (frS 0) x' := by
  have h := decomp mul_comm (c.mA (frS 0)) (c.mA (frS 1)) (c.mA_y3 0 (by norm_num))
    (c.mA_s2 0 (by norm_num)) (c.mA_sy 0 (by norm_num)) ⊤ (fun m _ => c.sq_M m)
    (fun _ _ => Subgroup.mem_top _) (fun _ _ => Subgroup.mem_top _)
    (fun m _ hm => c.y1_fpf m hm)
  rw [Subgroup.card_top, c.card_M] at h
  exact ⟨h.1, fun m => h.2 m (Subgroup.mem_top m)⟩

theorem mem_C1
    {m : c.M} : m ∈ c.C1 ↔ c.mA (frS 1) m = m :=
  ⟨fun h => h.2, fun h => ⟨Subgroup.mem_top m, h⟩⟩

theorem decomp2 :
    Nat.card c.C12 ^ 2 = Nat.card c.C1 ∧
    ∀ x ∈ c.C1, ∃ t ∈ c.C12, ∃ t' ∈ c.C12, x = t * c.mA (frS 2) t' := by
  have h := decomp mul_comm (c.mA (frS 2)) (c.mA (frS 3)) (c.mA_y3 2 (by norm_num))
    (c.mA_s2 1 (by norm_num)) (c.mA_sy 1 (by norm_num)) c.C1 (fun m _ => c.sq_M m)
    (fun m hm => by
      rw [mem_C1] at hm ⊢
      rw [c.mA_comm' (k := 1) (l := 2) (by norm_num) (by norm_num) (by norm_num), hm])
    (fun m hm => by
      rw [mem_C1] at hm ⊢
      rw [c.mA_comm' (k := 1) (l := 3) (by norm_num) (by norm_num) (by norm_num), hm])
    (fun m _ hm => c.y2_fpf m hm)
  exact h

theorem decomp3 :
    Nat.card c.C123 ^ 2 = Nat.card c.C12 ∧
    ∀ t ∈ c.C12, ∃ s ∈ c.C123, ∃ s' ∈ c.C123, t = s * c.mA (frS 4) s' := by
  have h := decomp mul_comm (c.mA (frS 4)) (c.mA (frS 5)) (c.mA_y3 4 (by norm_num))
    (c.mA_s2 2 (by norm_num)) (c.mA_sy 2 (by norm_num)) c.C12 (fun m _ => c.sq_M m)
    (fun m hm => by
      obtain ⟨hm1, hm2⟩ := hm
      refine ⟨?_, ?_⟩
      · have hm1' : c.mA (frS 1) m = m := c.mem_C1.mp hm1
        show c.mA (frS 4) m ∈ c.C1
        rw [mem_C1, c.mA_comm' (k := 1) (l := 4) (by norm_num) (by norm_num) (by norm_num),
          hm1']
      · have hm2' : c.mA (frS 3) m = m := hm2
        show c.mA (frS 3) (c.mA (frS 4) m) = c.mA (frS 4) m
        rw [c.mA_comm' (k := 3) (l := 4) (by norm_num) (by norm_num) (by norm_num), hm2'])
    (fun m hm => by
      obtain ⟨hm1, hm2⟩ := hm
      refine ⟨?_, ?_⟩
      · have hm1' : c.mA (frS 1) m = m := c.mem_C1.mp hm1
        show c.mA (frS 5) m ∈ c.C1
        rw [mem_C1, c.mA_comm' (k := 1) (l := 5) (by norm_num) (by norm_num) (by norm_num),
          hm1']
      · have hm2' : c.mA (frS 3) m = m := hm2
        show c.mA (frS 3) (c.mA (frS 5) m) = c.mA (frS 5) m
        rw [c.mA_comm' (k := 3) (l := 5) (by norm_num) (by norm_num) (by norm_num), hm2'])
    (fun m _ hm => c.y3_fpf m hm)
  exact h

theorem card_C1 :
    Nat.card c.C1 = 16 := sq_eq_imp (by rw [c.decomp1.1]; norm_num)

theorem card_C12 :
    Nat.card c.C12 = 4 := sq_eq_imp (by rw [c.decomp2.1, c.card_C1]; norm_num)

theorem card_C123 :
    Nat.card c.C123 = 2 := sq_eq_imp (by rw [c.decomp3.1, c.card_C12]; norm_num)

theorem exists_w :
    ∃ w ∈ c.C123, w ≠ 1 ∧ ∀ s ∈ c.C123, s = 1 ∨ s = w := by
  obtain ⟨⟨w, hw⟩, hne, huniq⟩ := (Nat.card_eq_two_iff' (1 : c.C123)).mp c.card_C123
  refine ⟨w, hw, fun h => hne (Subtype.ext h), fun s hs => ?_⟩
  by_cases h1 : s = 1
  · exact Or.inl h1
  · exact Or.inr (congrArg Subtype.val (huniq ⟨s, hs⟩ fun h => h1 (congrArg Subtype.val h)))

@[expose] noncomputable def w :
    c.M := c.exists_w.choose

theorem w_mem :
    c.w ∈ c.C123 := c.exists_w.choose_spec.1

theorem w_ne_one :
    c.w ≠ 1 := c.exists_w.choose_spec.2.1

theorem eq_w_of_mem
    {s : c.M} (hs : s ∈ c.C123) : s = 1 ∨ s = c.w :=
  c.exists_w.choose_spec.2.2 s hs

theorem s1_w :
    c.mA (frS 1) c.w = c.w := c.w_mem.1.1.2

theorem s2_w :
    c.mA (frS 3) c.w = c.w := c.w_mem.1.2

theorem s3_w :
    c.mA (frS 5) c.w = c.w := c.w_mem.2

end LocalConfig

end CFSG.Sporadic.Co2Smith
