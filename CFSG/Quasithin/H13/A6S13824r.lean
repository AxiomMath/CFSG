module

public import CFSG.Quasithin.H13.A6S13824q

public section

namespace CFSG.Quasithin.H13.A6.S7C

open Equiv

theorem dec_idc : dec idc = 1 := cd_injective (by rw [cd_dec (by decide), cd_one])

theorem T0L_spec : ∀ t ∈ T0L, valid t = true ∧ inT0 t = true := by
  have h : (T0L.all fun t => valid t && inT0 t) = true := by decide +kernel
  intro t ht
  simpa using List.all_eq_true.mp h t ht

structure E4Dat where
  t1 : ℕ
  t2 : ℕ
  t3 : ℕ
  k : ℕ
  b : ℕ
  b' : ℕ
  x : ℕ
  cert : List (ℕ × ℕ × ℕ)

@[expose] def e4Tab : List E4Dat := [
  ⟨1725633, 1725640, 1754753, 1754704, 1725640, 1725633, 1725080,
    [(0, 1754760, 1260168), (0, 1754760, 1227912), (0, 1754760, 1751120), (0, 1754760, 1718864),
      (0, 1754760, 1754200), (0, 1754760, 1266776), (0, 1754760, 1747032), (0, 1754760, 1256024),
      (0, 1754760, 1717352), (0, 1754760, 1258600), (1, 1525384, 1743056), (1, 1525328, 1747144),
      (1, 1524824, 1751176)]⟩,
  ⟨1725633, 1726081, 1754312, 1754704, 1726081, 1725633, 1725962,
    [(0, 1754760, 1260168), (0, 1754760, 1227912), (0, 1754760, 1751120), (0, 1754760, 1718864),
      (0, 1754760, 1260112), (0, 1754760, 1227856), (0, 1754760, 1754200), (0, 1754760, 1266776),
      (0, 1754760, 1747032), (0, 1754760, 1256024), (0, 1754760, 739928), (0, 1754760, 707672),
      (0, 1754760, 1717352), (0, 1754760, 738920), (0, 1754760, 1225840), (0, 1754760, 706160),
      (1, 1525384, 1751176), (1, 1751176, 1252048), (1, 1457288, 1743056)]⟩,
  ⟨1725633, 1726088, 1754305, 1678096, 1726088, 1725633, 1753752,
    [(0, 1754760, 1260168), (0, 1754760, 1227912), (0, 1754760, 1751120), (0, 1754760, 1718864),
      (0, 1754760, 1754200), (0, 1754760, 1266776), (0, 1754760, 1747032), (0, 1754760, 1256024),
      (0, 1754760, 1717352), (0, 1754760, 1258600), (1, 1525384, 1751176), (1, 1525384, 1743056)]⟩,
  ⟨1725640, 1726081, 1754305, 1754704, 1725640, 1754305, 1725080,
    [(0, 1754760, 1260168), (0, 1754760, 1227912), (0, 1754760, 1751120), (0, 1754760, 1718864),
      (0, 1754760, 1754200), (0, 1754760, 1266776), (0, 1754760, 1747032), (0, 1754760, 1256024),
      (0, 1754760, 1717352), (0, 1754760, 1258600), (1, 1525384, 1751176), (1, 1525384, 1743056)]⟩,
  ⟨1725640, 1726088, 1754312, 1676332, 1726088, 1725640, 1753752,
    [(0, 1754760, 1260168), (0, 1754760, 1227912), (0, 1754760, 1751120), (0, 1754760, 1718864),
      (0, 1754760, 1754200), (0, 1754760, 1266776), (0, 1754760, 1747032), (0, 1754760, 1256024),
      (0, 1754760, 1717352), (0, 1754760, 1258600), (1, 1525384, 1751176), (1, 1525328, 1751176),
      (1, 1525265, 1751176)]⟩,
  ⟨1726081, 1726088, 1754753, 1678096, 1726088, 1726081, 1753752,
    [(0, 1754760, 1260168), (0, 1754760, 1227912), (0, 1754760, 1751120), (0, 1754760, 1718864),
      (0, 1754760, 1754200), (0, 1754760, 1266776), (0, 1754760, 1747032), (0, 1754760, 1256024),
      (0, 1754760, 1717352), (0, 1754760, 1258600), (1, 1525384, 1743056), (1, 1525328, 1747144),
      (1, 1524824, 1751176)]⟩,
  ⟨1754305, 1754312, 1754753, 1754704, 1754312, 1754305, 1753752,
    [(0, 1754760, 1751120), (0, 1754760, 1718864), (0, 1754760, 1260112), (0, 1754760, 1227856),
      (0, 1754760, 477904), (0, 1754760, 445648), (0, 1754760, 1754200), (0, 1754760, 1266776),
      (0, 1754760, 1747032), (0, 1754760, 1256024), (0, 1754760, 739928), (0, 1754760, 707672),
      (0, 1754760, 477848), (0, 1754760, 445592), (0, 1754760, 1717352), (0, 1754760, 738920),
      (0, 1754760, 1225840), (0, 1754760, 706160), (1, 1751176, 1252048), (1, 1457288, 1743056),
      (1, 1751120, 1256136), (1, 1457232, 1747144), (1, 1747032, 1260168), (1, 1453144, 1751176)]⟩]

@[expose] def E4Dat.mem (d : E4Dat) (t : ℕ) : Bool := t == d.t1 || t == d.t2 || t == d.t3

@[expose] def E4Dat.ok (d : E4Dat) : Bool :=
  valid d.t1 && valid d.t2 && valid d.t3 && valid d.k && d.mem d.b && d.mem d.b' &&
    inT0 (cm (cinv q2c) (cm (conjC d.k d.b') q1c)) && conjC d.k d.b == d.x && valid d.x &&
    (T0L.all fun t => valid (cm t d.x)) &&
    (DL.all fun g => inT0 g || T0L.any fun t => inT0 (cm (cinv (cm t d.x)) g)) &&
    (d.cert.all fun e => valid e.2.1 && valid e.2.2) &&
    (xorL (d.cert.map (entryKeys keyD q1c q2c d.t1 d.t2))).isPerm [keyD idc, keyD c456]

theorem e4Tab_ok : e4Tab.all E4Dat.ok = true := by decide +kernel

@[expose] def dispatch (x y : ℕ) : Bool :=
  x == idc || y == idc || x == y ||
    e4Tab.any fun d => [d.t1, d.t2, d.t3].all fun t => t == x || t == y || t == cm x y

theorem dispatch_ok : (E8L.all fun x => E8L.all fun y => dispatch x y) = true := by
  decide +kernel

theorem E4Dat.ok_spec {d : E4Dat} (h : d.ok = true) :
    valid d.t1 = true ∧ valid d.t2 = true ∧ valid d.t3 = true ∧ valid d.k = true ∧
      d.mem d.b = true ∧ d.mem d.b' = true ∧
      inT0 (cm (cinv q2c) (cm (conjC d.k d.b') q1c)) = true ∧ conjC d.k d.b = d.x ∧
      valid d.x = true ∧ (∀ t ∈ T0L, valid (cm t d.x) = true) ∧
      (∀ g ∈ DL, inT0 g = true ∨ ∃ t ∈ T0L, inT0 (cm (cinv (cm t d.x)) g) = true) ∧
      (d.cert.all fun e => valid e.2.1 && valid e.2.2) = true ∧
      (xorL (d.cert.map (entryKeys keyD q1c q2c d.t1 d.t2))).Perm [keyD idc, keyD c456] := by
  simp only [E4Dat.ok, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
    List.any_eq_true, List.isPerm_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hv1, hv2⟩, hv3⟩, hvk⟩, hb⟩, hb'⟩, hy⟩, hx⟩, hvx⟩, hvtx⟩, hcov⟩, hcert⟩,
    hperm⟩ := h
  refine ⟨hv1, hv2, hv3, hvk, hb, hb', hy, hx, hvx, hvtx, hcov, ?_, hperm⟩
  simpa only [List.all_eq_true, Bool.and_eq_true] using hcert

theorem E4Dat.valid_of_mem {d : E4Dat} (h : d.ok = true) {t : ℕ} (ht : d.mem t = true) :
    valid t = true := by
  obtain ⟨hv1, hv2, hv3, -⟩ := E4Dat.ok_spec h
  simp only [E4Dat.mem, Bool.or_eq_true, beq_iff_eq] at ht
  rcases ht with (rfl | rfl) | rfl
  · exact hv1
  · exact hv2
  · exact hv3

@[expose] def basis4 : List ℕ :=
  [4169, 585, 266312, 36929, 266816, 36936]

@[expose] def steps4 : List (ℕ × ℕ) :=
  [(1525384, 2), (1521800, 2), (1754704, 1), (1751120, 2), (1754200, 2), (1524824, 2),
    (1747032, 0), (1517656, 2), (1453144, 2), (1223768, 1), (707672, 1), (477848, 1), (1750112, 1),
    (1520736, 1), (1004640, 2), (1517152, 2), (743008, 1), (1682016, 0), (480928, 1), (1000552, 0),
    (1681512, 1), (993384, 2), (1158248, 0), (670824, 1), (473256, 2), (1455216, 0), (444080, 1),
    (219345, 1), (1751176, 2)]

@[expose] def K4 : List ℕ :=
  [33289, 299520, 37440, 262217, 295425, 266760, 294921, 294977, 4680, 32841, 295488, 36873,
    295432, 266305, 299009, 262728, 33352, 299072, 299016, 294984, 4673, 262721, 4617, 266753,
    37377, 33345, 37384, 262665, 266249, 4169, 585, 266312, 36929, 266816, 36936]

theorem bfs4_ok : bfsK key4 q1c q2c basis4 steps4 = some K4 := by decide +kernel

theorem K4_all (σ : Perm (Fin 7)) : K4.contains (key4 (cd σ)) = true :=
  forall_cd (P := fun x => K4.contains (key4 x)) (by decide +kernel) σ

theorem cov456_all (σ : Perm (Fin 7)) :
    (!inS4 (cd σ) || [idc, c456, c465].any fun w => inD (cm (cinv w) (cd σ))) = true :=
  forall_cd (P := fun x => !inS4 x || [idc, c456, c465].any fun w => inD (cm (cinv w) x))
    (by decide +kernel) σ

section CaseA

variable {M : Type*} [CommGroup M] {Φ : Perm (Fin 7) →* MulAut M} {m₀ : M}

theorem exists_e4 {E : Set (Perm (Fin 7))} {a a' : Perm (Fin 7)} (ha : a ∈ E) (ha' : a' ∈ E)
    (haa : a * a' ∈ E) (haE : inE8 (cd a) = true) (ha'E : inE8 (cd a') = true) (ha1 : a ≠ 1)
    (ha'1 : a' ≠ 1) (hne : a ≠ a') :
    ∃ d ∈ e4Tab, ∀ t, d.mem t = true → dec t ∈ E := by
  have hL := listsOK_all a
  have hL' := listsOK_all a'
  simp only [listsOK, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.contains_iff_mem] at hL hL'
  have haL : cd a ∈ E8L := hL.1.2.resolve_left (by rw [haE]; simp)
  have ha'L : cd a' ∈ E8L := hL'.1.2.resolve_left (by rw [ha'E]; simp)
  have hdis := List.all_eq_true.mp (List.all_eq_true.mp dispatch_ok _ haL) _ ha'L
  have hc1 : cd a ≠ idc := fun h => ha1 (cd_injective (h.trans cd_one.symm))
  have hc1' : cd a' ≠ idc := fun h => ha'1 (cd_injective (h.trans cd_one.symm))
  have hcne : cd a ≠ cd a' := fun h => hne (cd_injective h)
  simp only [dispatch, Bool.or_eq_true, beq_iff_eq, hc1, hc1', hcne, false_or, List.any_eq_true,
    List.all_eq_true, List.mem_cons, List.not_mem_nil, or_false] at hdis
  obtain ⟨d, hd, hdt⟩ := hdis
  refine ⟨d, hd, fun t ht => ?_⟩
  have h3 : (t = cd a ∨ t = cd a') ∨ t = cm (cd a) (cd a') := by
    simp only [E4Dat.mem, Bool.or_eq_true, beq_iff_eq] at ht
    rcases ht with (rfl | rfl) | rfl
    · exact hdt d.t1 (Or.inl rfl)
    · exact hdt d.t2 (Or.inr (Or.inl rfl))
    · exact hdt d.t3 (Or.inr (Or.inr rfl))
  rcases h3 with (rfl | rfl) | rfl
  · rw [dec_cd a (valid_cd a)]
    exact ha
  · rw [dec_cd a' (valid_cd a')]
    exact ha'
  · rw [← cd_mul, dec_cd _ (valid_cd _)]
    exact haa

theorem fix_x (hsq : ∀ x : M, x * x = 1)
    (hT : ∀ t : Perm (Fin 7), inT0 (cd t) = true → Φ t m₀ = m₀)
    (hrel : m₀ * Φ (dec q1c) m₀ * Φ (dec q2c) m₀ = 1) {E : Set (Perm (Fin 7))}
    (hq : IndQuad.QuadOn Φ E) {d : E4Dat} (hd : d.ok = true)
    (hmemE : ∀ t, d.mem t = true → dec t ∈ E) : Φ (dec d.x) m₀ = m₀ := by
  have hinv : ∀ x : M, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (hsq x)
  obtain ⟨-, -, -, hvk, hb, hb', hy, hx, hvx, -⟩ := E4Dat.ok_spec hd
  have hvb := E4Dat.valid_of_mem hd hb
  have hvb' := E4Dat.valid_of_mem hd hb'
  have hvq1 : valid q1c = true := by decide
  have hvq2 : valid q2c = true := by decide
  have h1 : Φ ((dec q2c)⁻¹ * (dec d.k * dec d.b' * (dec d.k)⁻¹ * dec q1c)) m₀ = m₀ := by
    refine hT _ ?_
    rw [cd_mul, cd_inv, cd_mul, cd_mul, cd_mul, cd_inv, cd_dec hvq2, cd_dec hvk, cd_dec hvb',
      cd_dec hvq1]
    exact hy
  have hyq : Φ (dec d.k * dec d.b' * (dec d.k)⁻¹) (Φ (dec q1c) m₀) = Φ (dec q2c) m₀ := by
    calc Φ (dec d.k * dec d.b' * (dec d.k)⁻¹) (Φ (dec q1c) m₀)
        = Φ (dec q2c) (Φ ((dec q2c)⁻¹ * (dec d.k * dec d.b' * (dec d.k)⁻¹ * dec q1c)) m₀) := by
          rw [← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel_left]
      _ = Φ (dec q2c) m₀ := by rw [h1]
  have hw : Φ (dec d.k * dec d.b' * (dec d.k)⁻¹) (Φ (dec q1c) m₀) * (Φ (dec q1c) m₀)⁻¹ =
      m₀ := by
    rw [hyq, hinv, mul_comm]
    have h2 : m₀ * (Φ (dec q1c) m₀ * Φ (dec q2c) m₀) = 1 := by rw [← mul_assoc]; exact hrel
    calc Φ (dec q1c) m₀ * Φ (dec q2c) m₀
        = m₀ * (m₀ * (Φ (dec q1c) m₀ * Φ (dec q2c) m₀)) := by rw [← mul_assoc, hsq, one_mul]
      _ = m₀ := by rw [h2, mul_one]
  have h := IndQuad.fix_of_comm hq (h := dec d.k) (hmemE _ hb) (hmemE _ hb') hw
  have e : dec d.k * dec d.b * (dec d.k)⁻¹ = dec d.x := by
    apply cd_injective
    rw [cd_dec hvx, ← hx, cd_mul, cd_mul, cd_inv, cd_dec hvk, cd_dec hvb]
    rfl
  rwa [e] at h

theorem fix_D (hT : ∀ t : Perm (Fin 7), inT0 (cd t) = true → Φ t m₀ = m₀) {d : E4Dat}
    (hd : d.ok = true) (hx : Φ (dec d.x) m₀ = m₀) (σ : Perm (Fin 7)) (hσ : inD (cd σ) = true) :
    Φ σ m₀ = m₀ := by
  obtain ⟨-, -, -, -, -, -, -, -, hvx, hvtx, hcov, -⟩ := E4Dat.ok_spec hd
  refine fix_of_cover hT (W := idc :: T0L.map fun t => cm t d.x) ?_ ?_ σ hσ
  · intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact ⟨by decide, by rw [dec_idc, map_one, MulAut.one_apply]⟩
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hw
    obtain ⟨hvt, hTt⟩ := T0L_spec t ht
    refine ⟨hvtx t ht, ?_⟩
    rw [apply_dec_mul hvt hvx, map_mul, MulAut.mul_apply, hx]
    exact hT _ (by rw [cd_dec hvt]; exact hTt)
  · intro τ hτ
    have hτL : cd τ ∈ DL := by
      have h := listsOK_all τ
      simp only [listsOK, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
        List.contains_iff_mem] at h
      exact h.1.1.1.2.resolve_left (by rw [hτ]; simp)
    rcases hcov _ hτL with h | ⟨t, ht, h⟩
    · refine List.any_eq_true.mpr ⟨idc, List.mem_cons_self, ?_⟩
      have e : cm (cinv idc) (cd τ) = cd τ := by
        rw [show cinv idc = idc by decide, ← cd_one, ← cd_mul, one_mul]
      rw [e]
      exact h
    · exact List.any_eq_true.mpr ⟨_, List.mem_cons_of_mem _ (List.mem_map_of_mem ht), h⟩

theorem fix_456 (hsq : ∀ x : M, x * x = 1)
    (hD : ∀ σ : Perm (Fin 7), inD (cd σ) = true → Φ σ m₀ = m₀)
    (hrel : m₀ * Φ (dec q1c) m₀ * Φ (dec q2c) m₀ = 1) {E : Set (Perm (Fin 7))}
    (hq : IndQuad.QuadOn Φ E) {d : E4Dat} (hd : d.ok = true)
    (hmemE : ∀ t, d.mem t = true → dec t ∈ E) : Φ (dec c456) m₀ = m₀ := by
  obtain ⟨hv1, hv2, -, -, -, -, -, -, -, -, -, hcert, hperm⟩ := E4Dat.ok_spec hd
  have hμ := mu_eq_val (X := D7) (fun t ht => hD t (mem_D7_iff.mp ht))
    (fun σ τ h => keyD_sound h)
  have h := cert_sound hsq hμ (by decide : valid q1c = true) (by decide : valid q2c = true) hrel
    hq (hmemE _ (by simp [E4Dat.mem])) (hmemE _ (by simp [E4Dat.mem])) hv1 hv2 d.cert hcert
  rw [(hperm.map _).prod_eq] at h
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  have e1 : Φ (dec c456) m₀ = val Φ m₀ keyD (keyD c456) := by
    rw [hμ, cd_dec (by decide)]
  have e2 : m₀ = val Φ m₀ keyD (keyD idc) := by
    rw [← cd_one, ← hμ, map_one, MulAut.one_apply]
  rw [e1]
  refine Eq.trans ?_ e2.symm
  calc val Φ m₀ keyD (keyD c456)
      = val Φ m₀ keyD (keyD idc) * (val Φ m₀ keyD (keyD idc) * val Φ m₀ keyD (keyD c456)) := by
        rw [← mul_assoc, hsq, one_mul]
    _ = val Φ m₀ keyD (keyD idc) := by rw [h, mul_one]

theorem fix_S43 (hD : ∀ σ : Perm (Fin 7), inD (cd σ) = true → Φ σ m₀ = m₀)
    (h456 : Φ (dec c456) m₀ = m₀) (σ : Perm (Fin 7)) (hσ : inS4 (cd σ) = true) :
    Φ σ m₀ = m₀ := by
  have hv : valid c456 = true := by decide
  refine fix_of_cover hD (W := [idc, c456, c465]) ?_ (fun τ hτ => ?_) σ hσ
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact ⟨by decide, by rw [dec_idc, map_one, MulAut.one_apply]⟩
    · exact ⟨hv, h456⟩
    · refine ⟨by decide, ?_⟩
      rw [show c465 = cm c456 c456 by decide, apply_dec_mul hv hv, map_mul, MulAut.mul_apply,
        h456, h456]
  · have h := cov456_all τ
    rw [hτ] at h
    simpa using h

theorem card_le_of_S43 [Finite M] (hsq : ∀ x : M, x * x = 1)
    (hS : ∀ σ : Perm (Fin 7), inS4 (cd σ) = true → Φ σ m₀ = m₀)
    (hrel : m₀ * Φ (dec q1c) m₀ * Φ (dec q2c) m₀ = 1)
    (hgen : Subgroup.closure (Set.range fun σ : Perm (Fin 7) => Φ σ m₀) = ⊤) :
    Nat.card M ≤ 2 ^ 6 := by
  have hμ := mu_eq_val (X := S43) (fun t ht => hS t (mem_S43_iff.mp ht))
    (fun σ τ h => key4_sound h)
  set v := val Φ m₀ key4 with hv
  set B := Subgroup.closure (Set.range fun i : Fin 6 => v (basis4.getD i 0)) with hB
  have hK0 : ∀ k ∈ basis4, v k ∈ B := by
    intro k hk
    simp only [basis4, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Subgroup.subset_closure ⟨0, rfl⟩
    · exact Subgroup.subset_closure ⟨1, rfl⟩
    · exact Subgroup.subset_closure ⟨2, rfl⟩
    · exact Subgroup.subset_closure ⟨3, rfl⟩
    · exact Subgroup.subset_closure ⟨4, rfl⟩
    · exact Subgroup.subset_closure ⟨5, rfl⟩
  have hK := bfs_sound hsq (B := B)
    (fun n hn => lam_inst hμ (by decide : valid q1c = true) (by decide : valid q2c = true) hrel hn)
    steps4 basis4 K4 bfs4_ok hK0
  have hall : ∀ σ : Perm (Fin 7), Φ σ m₀ ∈ B := fun σ => by
    rw [hμ]
    exact hK _ (List.contains_iff_mem.mp (K4_all σ))
  have htop : (⊤ : Subgroup M) ≤ B := by
    rw [← hgen, Subgroup.closure_le]
    rintro _ ⟨σ, rfl⟩
    exact hall σ
  calc Nat.card M = Nat.card (⊤ : Subgroup M) := Subgroup.card_top.symm
    _ ≤ Nat.card B := Subgroup.card_le_of_le htop
    _ ≤ 2 ^ 6 := card_closure_le hsq _

theorem card_le_of_PA [Finite M] (hsq : ∀ x : M, x * x = 1)
    (hT : ∀ t : Perm (Fin 7), inT0 (cd t) = true → Φ t m₀ = m₀)
    (hrel : m₀ * Φ (dec q1c) m₀ * Φ (dec q2c) m₀ = 1)
    (hgen : Subgroup.closure (Set.range fun σ : Perm (Fin 7) => Φ σ m₀) = ⊤)
    {E : Set (Perm (Fin 7))} (hq : IndQuad.QuadOn Φ E) {a a' : Perm (Fin 7)} (ha : a ∈ E)
    (ha' : a' ∈ E) (haa : a * a' ∈ E) (haE : inE8 (cd a) = true) (ha'E : inE8 (cd a') = true)
    (ha1 : a ≠ 1) (ha'1 : a' ≠ 1) (hne : a ≠ a') : Nat.card M ≤ 2 ^ 6 := by
  obtain ⟨d, hd, hmemE⟩ := exists_e4 ha ha' haa haE ha'E ha1 ha'1 hne
  have hok := List.all_eq_true.mp e4Tab_ok d hd
  have hx := fix_x hsq hT hrel hq hok hmemE
  have hD := fix_D hT hok hx
  exact card_le_of_S43 hsq (fix_S43 hD (fix_456 hsq hD hrel hq hok hmemE)) hrel hgen

theorem card_le_case_PA [Finite M] (hsq : ∀ x : M, x * x = 1)
    (hT : ∀ t : Perm (Fin 7), inT0 (cd t) = true → Φ t m₀ = m₀)
    (hgen : Subgroup.closure (Set.range fun σ : Perm (Fin 7) => Φ σ m₀) = ⊤)
    {c : Perm (Fin 7)} (hcPA : c ∈ PA) (h1 : Φ c m₀ ≠ m₀) (h2 : Φ (c * c) m₀ ≠ m₀)
    (h12 : Φ c m₀ ≠ Φ (c * c) m₀) (hcc : m₀ * Φ c m₀ = Φ (c * c) m₀)
    {E : Subgroup (Perm (Fin 7))} (hq : IndQuad.QuadOn Φ (E : Set (Perm (Fin 7))))
    (h4 : 4 ≤ Nat.card E)
    (hcore : ∀ x ∈ E, x ∈ T0 ∧ c * x * c⁻¹ ∈ T0 ∧ c⁻¹ * x * c ∈ T0) : Nat.card M ≤ 2 ^ 6 := by
  have hT' : ∀ t ∈ T0, Φ t m₀ = m₀ := fun t ht => hT t (mem_T0_iff.mp ht)
  have hcT : c ∉ T0 := fun h => h1 (hT' c h)
  have hrel := rel_of_cos hsq hT' (cosets_PA hcPA) (cosets_PA (PA.mul_mem hcPA hcPA)) h1 h2 h12 hcc
  obtain ⟨a, haE, ha1, -⟩ := exists_mem_ne_ne h4 1 1
  obtain ⟨a', ha'E, ha'1, ha'a⟩ := exists_mem_ne_ne h4 1 a
  have hE8 : ∀ x ∈ E, inE8 (cd x) = true := fun x hx => by
    obtain ⟨hx0, hx1, hx2⟩ := hcore x hx
    exact mem_E8_iff.mp (mem_E8_of_core hcPA hcT hx0 hx1 hx2)
  exact card_le_of_PA hsq hT hrel.1 hgen hq haE ha'E (E.mul_mem haE ha'E) (hE8 a haE)
    (hE8 a' ha'E) ha1 ha'1 (Ne.symm ha'a)

end CaseA

end CFSG.Quasithin.H13.A6.S7C
