module

public import CFSG.Quasithin.H13.L32NO3Model3
public import CFSG.Quasithin.H13.L32NLem14411b
public import Certificates.Certificate7237

public section

namespace CFSG.Quasithin.H13.O3cCert

open Mat8Cert L1442M O3Cert S7Cert CFSG.QuasithinUnique

theorem o3cCheck_eq : o3cCheck = true :=
  Certificates.certificate7237

theorem check_parts : p0B = true ∧ c4B = true ∧ c5B = true := by
  have h := o3cCheck_eq
  simp only [o3cCheck, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem p0B_spec :
    subB p0G p0E = true ∧ p0E.length = 16 ∧ (∀ g ∈ p0G, g ∈ om3E) ∧
      (∀ v < 256, (∀ g ∈ p0G, mv8 g v = v) → v = 0 ∨ v ∈ fixS) ∧ tS ∈ om3E ∧
      mul8 tS tI = one8 ∧ ∀ v ∈ fixS, mv8 tS v = v := by
  have h := check_parts.1
  simp only [p0B, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, h2, h3, fun v hv hfix => ?_, h5, h6, h7⟩
  have := h4 v (List.mem_range.mpr hv)
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, List.contains_iff_mem] at this
  rcases this with (h8 | h8) | h8
  · exfalso
    have h9 : (p0G.all fun g => mv8 g v == v) = true := by
      simp only [List.all_eq_true, beq_iff_eq]
      exact hfix
    rw [h9] at h8
    exact Bool.noConfusion h8
  · exact Or.inl h8
  · exact Or.inr h8

theorem c4B_spec {v : ℕ} (hv : v ∈ fixS) {x : List ℕ}
    (hx : x ∈ omNE) (hxv : mv8 x v = v) (hxx : mul8 x x = one8) (hx3 : x ∉ om3E)
    (hc : mul8 (mul8 (mul8 tS x) (mul8 tI x)) (mul8 (mul8 tS x) (mul8 tI x)) = one8) :
    mul8 sfG x ∈ om3E ∧ x ∉ om3FE ∧ fullImgB x = true := by
  have h := check_parts.2.1
  simp only [c4B, List.all_eq_true] at h
  have h1 := h v hv x hx
  have e1 : (mv8 x v == v) = true := beq_iff_eq.mpr hxv
  have e2 : (mul8 x x == one8) = true := beq_iff_eq.mpr hxx
  have e3 : (Std.HashSet.ofList om3E).contains x = false := by
    rw [Std.HashSet.contains_ofList]
    exact Bool.eq_false_iff.mpr fun h' => hx3 (List.contains_iff_mem.mp h')
  have e4 : (mul8 (mul8 (mul8 tS x) (mul8 tI x)) (mul8 (mul8 tS x) (mul8 tI x)) == one8) =
      true := beq_iff_eq.mpr hc
  simp only [e1, e2, e3, e4, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    Std.HashSet.contains_ofList, List.contains_iff_mem, Bool.not_eq_true'] at h1
  obtain ⟨⟨h2, h3⟩, h4⟩ := h1
  exact ⟨h2, fun h5 => by rw [List.contains_iff_mem.mpr h5] at h3; exact Bool.noConfusion h3, h4⟩

theorem c5B_spec {v : ℕ} (hv : v ∈ fixS) {x : List ℕ}
    (hx : x ∈ omNE) (hxv : mv8 x v = v) (hxx : mul8 x x = one8) (hs : mul8 sfG x ∈ om3E)
    (hP : ∀ p ∈ p0E, mul8 (mul8 x p) x ∈ p0E) :
    (p0E.filter fun p => mul8 p x == mul8 x p).length ≤ 4 := by
  have h := check_parts.2.2
  simp only [c5B, List.all_eq_true] at h
  have h1 := h v hv x hx
  have e1 : (mv8 x v == v) = true := beq_iff_eq.mpr hxv
  have e2 : (mul8 x x == one8) = true := beq_iff_eq.mpr hxx
  have e3 : (Std.HashSet.ofList om3E).contains (mul8 sfG x) = true := by
    rw [Std.HashSet.contains_ofList]
    exact List.contains_iff_mem.mpr hs
  have e4 : (p0E.all fun p => (Std.HashSet.ofList p0E).contains (mul8 (mul8 x p) x)) = true := by
    rw [List.all_eq_true]
    intro p hp
    rw [Std.HashSet.contains_ofList]
    exact List.contains_iff_mem.mpr (hP p hp)
  simp only [e1, e2, e3, e4, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h1
  exact h1

@[expose] def P0 : Subgroup (GL (Fin 8) (ZMod 2)) := genSub p0G

theorem p0_unit :
    ∀ g ∈ p0G, ∃ u : GL (Fin 8) (ZMod 2), (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g := by
  intro g hg
  obtain ⟨u, -, hu⟩ := exists_mem_omega3 (p0B_spec.2.2.1 g hg)
  exact ⟨u, hu⟩

theorem mem_P0_iff
    (u : GL (Fin 8) (ZMod 2)) : u ∈ P0 ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ p0E :=
  mem_genSub_iff_of p0B_spec.1 p0_unit u

theorem card_P0 :
    Nat.card P0 = 16 := by
  rw [P0, card_genSub_of p0B_spec.1 p0_unit]
  exact p0B_spec.2.1

theorem P0_le_omega3 :
    P0 ≤ omega3 := by
  refine (Subgroup.closure_le _).mpr fun u hu => ?_
  exact (mem_omega3_iff u).mpr (p0B_spec.2.2.1 _ hu)

theorem colsOf_lt {u : GL (Fin 8) (ZMod 2)} (n : ℕ) :
    mv8 (colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2))) n < 256 :=
  mv8_lt (valid8_colsOf _) n

theorem fixS_lt {n : ℕ} (hn : n ∈ fixS) : n < 256 := by
  simp only [fixS, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl <;> decide

theorem mv8_eq_of_fix {u : GL (Fin 8) (ZMod 2)} {n : ℕ} (hn : n < 256)
    (h : (u : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 n) = vec8 n) :
    mv8 (colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2))) n = n := by
  rw [mulVec_vec8] at h
  exact vec8_inj (colsOf_lt n) hn h

theorem fix_P0
    {v : Fin 8 → ZMod 2} (hv : v ≠ 0)
    (hfix : ∀ p ∈ P0, (p : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v = v) :
    ∃ n ∈ fixS, v = vec8 n := by
  have hgen : ∀ g ∈ p0G, mv8 g (code8 v) = code8 v := by
    intro g hg
    obtain ⟨u, hu⟩ := p0_unit g hg
    have hmem : colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ p0G := by
      rw [hu, colsOf_dec8 ((subB_spec p0B_spec.1).2.2.2.2 g hg)]
      exact hg
    have huP : u ∈ P0 := Subgroup.subset_closure hmem
    have h1 := hfix u huP
    rw [← vec8_code8 v] at h1
    have h2 := mv8_eq_of_fix (code8_lt v) h1
    rwa [hu, colsOf_dec8 ((subB_spec p0B_spec.1).2.2.2.2 g hg)] at h2
  rcases p0B_spec.2.2.2.1 _ (code8_lt v) hgen with h | h
  · exfalso
    apply hv
    rw [← vec8_code8 v, h, vec8_zero]
  · exact ⟨_, h, (vec8_code8 v).symm⟩

theorem exists_torus :
    ∃ t ∈ omega3, colsOf (t : Matrix (Fin 8) (Fin 8) (ZMod 2)) = tS ∧
      colsOf ((t⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) = tI ∧
      ∀ n ∈ fixS, (t : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 n) = vec8 n := by
  obtain ⟨t, ht3, htS⟩ := exists_mem_omega3 p0B_spec.2.2.2.2.1
  have hvS : Valid8 tS := by refine ⟨rfl, ?_⟩; decide
  have hvI : Valid8 tI := by refine ⟨rfl, ?_⟩; decide
  have hcS : colsOf (t : Matrix (Fin 8) (Fin 8) (ZMod 2)) = tS := by
    rw [htS, colsOf_dec8 hvS]
  refine ⟨t, ht3, hcS, ?_, fun n hn => ?_⟩
  ·
    have h1 : (t : Matrix (Fin 8) (Fin 8) (ZMod 2)) * dec8 tI = 1 := by
      rw [htS, ← dec8_mul8 _ _ hvI.1, p0B_spec.2.2.2.2.2.1, dec8_one8]
    have h2 : ((t⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 tI := by
      calc ((t⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2))
          = ((t⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *
            ((t : Matrix (Fin 8) (Fin 8) (ZMod 2)) * dec8 tI) := by rw [h1, Matrix.mul_one]
        _ = dec8 tI := by
          rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    rw [h2, colsOf_dec8 hvI]
  · rw [mulVec_vec8, hcS, p0B_spec.2.2.2.2.2.2 n hn]

theorem colsOf_sf : colsOf ((o3swap * o3field : GL (Fin 8) (ZMod 2)) :
    Matrix (Fin 8) (Fin 8) (ZMod 2)) = sfG := by
  rw [Units.val_mul, colsOf_mul, sfG, sG_cols, fG_cols]

theorem sf_mul_self : (o3swap * o3field : GL (Fin 8) (ZMod 2)) * (o3swap * o3field) = 1 := by
  apply eq_of_colsOf_eq
  rw [Units.val_mul, colsOf_mul, colsOf_sf, Units.val_one, colsOf_one]
  decide

theorem inv_spec
    {t : GL (Fin 8) (ZMod 2)} (htS : colsOf (t : Matrix (Fin 8) (Fin 8) (ZMod 2)) = tS)
    (htI : colsOf ((t⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) = tI)
    {n : ℕ} (hn : n ∈ fixS) {x : GL (Fin 8) (ZMod 2)} (hxN : x ∈ omega3N)
    (hxv : (x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 n) = vec8 n) (hxx : x * x = 1)
    (hx3 : x ∉ omega3) (hc : (t * x * t⁻¹ * x) * (t * x * t⁻¹ * x) = 1) :
    o3swap * o3field * x ∈ omega3 ∧ x ∉ omega3F ∧
      fullImgB (colsOf (x : Matrix (Fin 8) (Fin 8) (ZMod 2))) = true := by
  have hcols : ∀ u w : GL (Fin 8) (ZMod 2), colsOf ((u * w : GL (Fin 8) (ZMod 2)) :
      Matrix (Fin 8) (Fin 8) (ZMod 2)) = mul8 (colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)))
        (colsOf (w : Matrix (Fin 8) (Fin 8) (ZMod 2))) := fun u w => by
    rw [Units.val_mul, colsOf_mul]
  obtain ⟨h1, h2, h3⟩ := c4B_spec hn ((mem_omega3N_iff x).mp hxN)
    (mv8_eq_of_fix (fixS_lt hn) hxv)
    (by rw [← hcols, hxx, Units.val_one, colsOf_one])
    (fun h => hx3 ((mem_omega3_iff x).mpr h))
    (by
      have e : t * x * t⁻¹ * x = (t * x) * (t⁻¹ * x) := by group
      rw [e] at hc
      have hcc : colsOf ((((t * x) * (t⁻¹ * x)) * ((t * x) * (t⁻¹ * x)) : GL (Fin 8) (ZMod 2)) :
          Matrix (Fin 8) (Fin 8) (ZMod 2)) = one8 := by
        rw [hc, Units.val_one, colsOf_one]
      simp only [hcols, htS, htI] at hcc
      exact hcc)
  refine ⟨(mem_omega3_iff _).mpr (by rw [hcols, colsOf_sf]; exact h1),
    fun h => h2 ((mem_omega3F_iff x).mp h), h3⟩

theorem card_cent_le {n : ℕ}
    (hn : n ∈ fixS) {x : GL (Fin 8) (ZMod 2)} (hxN : x ∈ omega3N)
    (hxv : (x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 n) = vec8 n) (hxx : x * x = 1)
    (hs : o3swap * o3field * x ∈ omega3) (hP : ∀ p ∈ P0, x * p * x⁻¹ ∈ P0) :
    Nat.card ↥(P0 ⊓ Subgroup.centralizer ({x} : Set (GL (Fin 8) (ZMod 2)))) ≤ 4 := by
  classical
  have hcols : ∀ u w : GL (Fin 8) (ZMod 2), colsOf ((u * w : GL (Fin 8) (ZMod 2)) :
      Matrix (Fin 8) (Fin 8) (ZMod 2)) = mul8 (colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)))
        (colsOf (w : Matrix (Fin 8) (Fin 8) (ZMod 2))) := fun u w => by
    rw [Units.val_mul, colsOf_mul]
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  set cx := colsOf (x : Matrix (Fin 8) (Fin 8) (ZMod 2)) with hcx
  have hlen := c5B_spec hn ((mem_omega3N_iff x).mp hxN) (mv8_eq_of_fix (fixS_lt hn) hxv)
    (by rw [← hcols, hxx, Units.val_one, colsOf_one])
    (by rw [← colsOf_sf, ← hcols]; exact (mem_omega3_iff _).mp hs)
    (by
      intro p hp
      obtain ⟨w, rfl⟩ := mem_elemsOf hp
      obtain ⟨u, hu, hu'⟩ := exists_evalW _ (subB_spec p0B_spec.1).2.2.2.2 p0_unit w
      have hval : Valid8 (evalW p0G w) :=
        valid8_evalW _ (subB_spec p0B_spec.1).2.2.2.2 w
      have hcu : colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = evalW p0G w := by
        rw [hu', colsOf_dec8 hval]
      have h1 := hP u hu
      rw [hxinv, mem_P0_iff, hcols, hcols, hcu] at h1
      exact h1)
  let F : List (List ℕ) := p0E.filter fun p => mul8 p cx == mul8 cx p
  have hmap : ∀ p ∈ (P0 ⊓ Subgroup.centralizer ({x} : Set (GL (Fin 8) (ZMod 2)))),
      colsOf (p : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ F := by
    intro p hp
    have hpx : p * x = x * p := Subgroup.mem_centralizer_singleton_iff.mp hp.2
    refine List.mem_filter.mpr ⟨(mem_P0_iff p).mp hp.1, ?_⟩
    rw [beq_iff_eq, ← hcols, ← hcols, hpx]
  calc Nat.card ↥(P0 ⊓ Subgroup.centralizer ({x} : Set (GL (Fin 8) (ZMod 2))))
      ≤ Nat.card ↥F.toFinset := by
        refine Nat.card_le_card_of_injective
          (fun p => ⟨colsOf ((p : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)),
            List.mem_toFinset.mpr (hmap p p.2)⟩) ?_
        intro p q h
        exact Subtype.ext (eq_of_colsOf_eq (congrArg Subtype.val h))
    _ = F.toFinset.card := Nat.card_eq_finsetCard _
    _ ≤ F.length := List.toFinset_card_le _
    _ ≤ 4 := hlen

theorem shape_of
    {Γ T X : Subgroup (GL (Fin 8) (ZMod 2))} {v₀ : Fin 8 → ZMod 2}
    (hΓN : Γ ≤ omega3N) (h3Γ : omega3 ≤ Γ)
    (hn3 : ∀ γ ∈ Γ, ∀ k ∈ omega3, γ * k * γ⁻¹ ∈ omega3)
    (hT : IsSylowTwoOf T Γ) (hTP : T ⊓ omega3 = P0)
    (hTv : ∀ t ∈ T, (t : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v₀ = v₀) (hv₀ : v₀ ≠ 0)
    (hXΓ : X ≤ Γ) (hXv : ∀ x ∈ X, (x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v₀ = v₀)
    (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hXsq : ∀ x ∈ X, x * x = 1)
    (hXn : ∀ m ∈ Γ, (m : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v₀ = v₀ →
      ∀ x ∈ X, m * x * m⁻¹ ∈ X)
    (hX3 : ¬ X ≤ omega3) (hX8 : 8 ≤ Nat.card X) :
    Nat.card X = 8 ∧ ∃ xs ∈ X, xs ∉ omega3F ∧
      fullImgB (colsOf (xs : Matrix (Fin 8) (Fin 8) (ZMod 2))) = true ∧
      X = (T ⊓ omega3 ⊓ Subgroup.centralizer ({xs} : Set (GL (Fin 8) (ZMod 2)))) ⊔
        Subgroup.zpowers xs := by
  classical
  obtain ⟨n, hn, rfl⟩ := fix_P0 hv₀ fun p hp => hTv p (by
    have hp' : p ∈ T ⊓ omega3 := hTP ▸ hp
    exact hp'.1)
  obtain ⟨t, ht3, htS, htI, htv⟩ := exists_torus
  have htΓ : t ∈ Γ := h3Γ ht3
  have hX2 : IsPGroup 2 ↥X := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, sq, Subgroup.coe_one]; exact hXsq x x.2)⟩
  have hTX : T ≤ Subgroup.normalizer (X : Set (GL (Fin 8) (ZMod 2))) := by
    intro t' ht'
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact hXn t' (hT.1 ht') (hTv t' ht') h
    · intro hh
      have h1 := hXn t'⁻¹ (hT.1 (T.inv_mem ht'))
        (by
          have h2 := hTv t'⁻¹ (T.inv_mem ht')
          exact h2) _ hh
      simpa [mul_assoc] using h1
  have hXT : X ≤ T := L14411.le_of_normalizes hT hX2 hXΓ hTX
  have hout : ∀ x ∈ X, x ∉ omega3 → o3swap * o3field * x ∈ omega3 ∧ x ∉ omega3F ∧
      fullImgB (colsOf (x : Matrix (Fin 8) (Fin 8) (ZMod 2))) = true := by
    intro x hx hx3
    have hc : t * x * t⁻¹ * x ∈ X := X.mul_mem (hXn t htΓ (htv n hn) x hx) hx
    exact inv_spec htS htI hn (hΓN (hXΓ hx)) (hXv x hx) (hXsq x hx) hx3 (hXsq _ hc)
  obtain ⟨xs, hxs, hxs3⟩ := Set.not_subset.mp hX3
  obtain ⟨hs, hsF, hsfull⟩ := hout xs hxs hxs3
  have hsfinv : (o3swap * o3field : GL (Fin 8) (ZMod 2))⁻¹ = o3swap * o3field :=
    inv_eq_of_mul_eq_one_right sf_mul_self
  have hsfΓ : (o3swap * o3field : GL (Fin 8) (ZMod 2)) ∈ Γ := by
    have h1 := Γ.mul_mem (h3Γ hs) (Γ.inv_mem (hXΓ hxs))
    rwa [mul_inv_cancel_right] at h1
  have hprod : ∀ x ∈ X, x ∉ omega3 → x * xs ∈ omega3 := by
    intro x hx hx3
    obtain ⟨h1, -, -⟩ := hout x hx hx3
    have e : x * xs = (o3swap * o3field) * (o3swap * o3field * x) * (o3swap * o3field)⁻¹ *
        (o3swap * o3field * xs) := by
      rw [hsfinv]
      calc x * xs = ((o3swap * o3field) * (o3swap * o3field)) * x *
            ((o3swap * o3field) * (o3swap * o3field)) * xs := by
            rw [sf_mul_self, one_mul, mul_one]
        _ = _ := by group
    rw [e]
    exact omega3.mul_mem (hn3 _ hsfΓ _ h1) hs
  have hXP : ∀ x ∈ X, x ∈ omega3 →
      x ∈ P0 ⊓ Subgroup.centralizer ({xs} : Set (GL (Fin 8) (ZMod 2))) := by
    intro x hx hx3
    refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr (hXc x hx xs hxs)⟩
    rw [← hTP]
    exact ⟨hXT hx, hx3⟩
  have hxsP : ∀ p ∈ P0, xs * p * xs⁻¹ ∈ P0 := by
    intro p hp
    rw [← hTP] at hp ⊢
    exact ⟨T.mul_mem (T.mul_mem (hXT hxs) hp.1) (T.inv_mem (hXT hxs)),
      hn3 xs (hXΓ hxs) p hp.2⟩
  have hcard4 := card_cent_le hn (hΓN (hXΓ hxs)) (hXv xs hxs) (hXsq xs hxs) hs hxsP
  have hY : Nat.card X ≤ 2 * Nat.card ↥(X ⊓ omega3) := by
    let f : ↥X → ↥(X ⊓ omega3) × Bool := fun x =>
      if h : (x : GL (Fin 8) (ZMod 2)) ∈ omega3 then (⟨x, x.2, h⟩, false)
      else (⟨x * xs, X.mul_mem x.2 hxs, hprod x x.2 h⟩, true)
    have hf : Function.Injective f := by
      intro x y hxy
      by_cases hx : (x : GL (Fin 8) (ZMod 2)) ∈ omega3 <;>
        by_cases hy : (y : GL (Fin 8) (ZMod 2)) ∈ omega3 <;>
        simp only [f, hx, hy, ↓reduceDIte, Prod.mk.injEq,
          Bool.false_eq_true, Bool.true_eq_false, and_false, and_true] at hxy
      · exact Subtype.ext (congrArg (fun z : ↥(X ⊓ omega3) => (z : GL (Fin 8) (ZMod 2))) hxy)
      · exact Subtype.ext (mul_right_cancel
          (congrArg (fun z : ↥(X ⊓ omega3) => (z : GL (Fin 8) (ZMod 2))) hxy))
    calc Nat.card ↥X ≤ Nat.card (↥(X ⊓ omega3) × Bool) := Nat.card_le_card_of_injective f hf
      _ = 2 * Nat.card ↥(X ⊓ omega3) := by rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool),
          Fintype.card_bool, mul_comm]
  have hYle : X ⊓ omega3 ≤ P0 ⊓ Subgroup.centralizer ({xs} : Set (GL (Fin 8) (ZMod 2))) :=
    fun x hx => hXP x hx.1 hx.2
  have hYc := (Subgroup.card_le_of_le hYle).trans hcard4
  have h8 : Nat.card X = 8 := by omega
  have hYeq : X ⊓ omega3 = P0 ⊓ Subgroup.centralizer ({xs} : Set (GL (Fin 8) (ZMod 2))) :=
    Subgroup.eq_of_le_of_card_ge hYle (by omega)
  refine ⟨h8, xs, hxs, hsF, hsfull, ?_⟩
  rw [hTP]
  apply le_antisymm
  · intro x hx
    by_cases hx3 : x ∈ omega3
    · exact Subgroup.mem_sup_left (hXP x hx hx3)
    · have h1 : x * xs ∈ P0 ⊓ Subgroup.centralizer ({xs} : Set (GL (Fin 8) (ZMod 2))) :=
        hYeq ▸ ⟨X.mul_mem hx hxs, hprod x hx hx3⟩
      have e : x = (x * xs) * xs := by rw [mul_assoc, hXsq xs hxs, mul_one]
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers xs))
  · refine sup_le ?_ ?_
    · rw [← hYeq]
      exact inf_le_left
    · rw [Subgroup.zpowers_le]
      exact hxs

end CFSG.Quasithin.H13.O3cCert
