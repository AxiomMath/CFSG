module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M23
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M12
public import Certificates.Certificate260401

public section

namespace CFSG.Quasithin.B45Mat

open CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier CFSG.Blueprint

theorem gen_witnesses :
    genWitOK NativeSporadic.M24 m24rl m24a m24b m24GenTab = true ∧
    genWitOK NativeSporadic.M23 m23rl m23GenA m23GenB m23GenTab = true ∧
    genWitOK NativeSporadic.M22 m22rl m22a m22b m22GenTab = true ∧
    genWitOK NativeSporadic.M12 m12rl m12a m12b m12GenTab = true := by
  obtain ⟨h1, h2, h3, h4⟩ := Certificates.certificate260401
  exact ⟨h1, h2, h3, h4⟩

section Witness

variable {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))

theorem sq_eq_one_of_mem_zpowers {G : Type*} [Group G] {x : G} (hx : x * x = 1) :
    ∀ y ∈ Subgroup.zpowers x, y * y = 1 := by
  intro y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have h2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two, hx]
  rw [← zpow_add, ← two_mul, zpow_mul, h2, one_zpow]

theorem gen3_of_witnesses (Rl : List ↥H) (a b : ↥H)
    (hgen : Subgroup.closure ({a, b} : Set ↥H) = ⊤)
    (hconj : ∀ x : ↥H, x * x = 1 → ∃ g : ↥H, g * x * g⁻¹ ∈ Rl) (idx : List ℕ)
    (hcov : ∀ x ∈ Rl, x ≠ 1 → x * x = 1 → ∃ i ∈ idx, ∃ r ∈ Rl, r * x * r⁻¹ = Rl.getD i 1)
    (tab : List (ℕ × List (List ℤ) × List ℕ × List ℕ)) (hidx : tab.map (·.1) = idx)
    (hok : genWitOK H Rl a b tab = true) :
    ∀ x : ↥H, x * x = 1 → x ≠ 1 →
      ∃ cs : List ↥H, cs.length = 3 ∧ Subgroup.closure (conjSet cs {x}) = ⊤ := by
  intro x hx hx1
  obtain ⟨g, hg⟩ := hconj x hx
  have hx' : g * x * g⁻¹ * (g * x * g⁻¹) = 1 := by
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hx]; group
  have hx1' : g * x * g⁻¹ ≠ 1 := fun h => hx1 (conj_eq_one_iff.1 h)
  obtain ⟨i, hi, r, -, hr⟩ := hcov _ hg hx1' hx'
  rw [← hidx] at hi
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hi
  have hwit := List.all_eq_true.1 hok e he
  simp only [Bool.and_eq_true, beq_iff_eq] at hwit
  obtain ⟨⟨hlen, hwa⟩, hwb⟩ := hwit
  set cj := e.2.1.map (evalN H [a, b]) with hcj
  set t0 := Rl.getD e.1 1 with ht0
  have htop : Subgroup.closure (conjSet (1 :: cj) {t0}) = ⊤ := by
    refine eq_top_iff.2 (hgen ▸ (Subgroup.closure_le _).2 ?_)
    have hsub : Subgroup.closure {y | y ∈ conjGens [t0] cj} ≤
        Subgroup.closure (conjSet (1 :: cj) {t0}) :=
      Subgroup.closure_mono fun y hy => by
        simpa using mem_conjSet_conjGens [t0] cj y hy
    rintro _ (rfl | rfl)
    · rw [← hwa]
      exact hsub (prodWord_mem_closure _ _)
    · rw [← hwb]
      exact hsub (prodWord_mem_closure _ _)
  refine ⟨(1 :: cj).map (· * (r * g)), by simp [hcj, hlen], eq_top_iff.2 fun y _ => ?_⟩
  refine closure_conjSet_transfer (T := {x}) (r * g) (fun t' ht' => ⟨x, rfl, ?_⟩) (1 :: cj)
    (htop ▸ Subgroup.mem_top y)
  rw [Set.mem_singleton_iff.1 ht', ← hr]
  group

theorem cover_of_g1cover {Rl : List ↥H} {G1 : List (ℕ × List (List ℤ) × List ℕ)}
    (h : g1cover Rl G1 = true) :
    ∀ x ∈ Rl, x ≠ 1 → x * x = 1 →
      ∃ i ∈ G1.map (·.1), ∃ r ∈ Rl, r * x * r⁻¹ = Rl.getD i 1 := by
  intro x hx hx1 hx2
  have hxi : x ∈ invG Rl := mem_invG.2 ⟨hx, hx1, hx2⟩
  obtain ⟨e, he, hanyr⟩ := List.any_eq_true.1 (List.all_eq_true.1 h x hxi)
  obtain ⟨r, hr, hrx⟩ := List.any_eq_true.1 hanyr
  exact ⟨e.1, List.mem_map.2 ⟨e, he, rfl⟩, r, hr, of_decide_eq_true hrx⟩

end Witness

theorem m24_gen3 :
    ∀ x : S24, x * x = 1 → x ≠ 1 →
      ∃ cs : List S24, cs.length = 3 ∧ Subgroup.closure (conjSet cs {x}) = ⊤ :=
  gen3_of_witnesses NativeSporadic.M24 m24rl m24a m24b (closure_pair_eq_top m24_eq _ _)
    (fun x hx => by
      obtain ⟨g, hg⟩ := m24_sylow.conj_into (Subgroup.zpowers x) (sq_eq_one_of_mem_zpowers hx)
      exact ⟨g, hg x (Subgroup.mem_zpowers x)⟩)
    _ (cover_of_g1cover _ m24_G1_check.2) m24GenTab (by decide) gen_witnesses.1

theorem m23_gen3 :
    ∀ x : S23, x * x = 1 → x ≠ 1 →
      ∃ cs : List S23, cs.length = 3 ∧ Subgroup.closure (conjSet cs {x}) = ⊤ :=
  gen3_of_witnesses NativeSporadic.M23 m23rl m23GenA m23GenB
    (closure_pair_eq_top m23_eq_closure _ _)
    (fun x hx => by
      obtain ⟨g, hg⟩ := m23_conj_into_R (Subgroup.zpowers x) (sq_eq_one_of_mem_zpowers hx)
      exact ⟨g, hg x (Subgroup.mem_zpowers x)⟩)
    (m23G1.map (·.1)) (by
      intro x hx hx1 hx2
      have hxi : x ∈ m23rinv := by
        rw [m23rinv, invList, List.mem_filter]
        exact ⟨hx, by simpa using ⟨hx1, hx2⟩⟩
      obtain ⟨e, he, hanyr⟩ :=
        List.any_eq_true.1 (List.all_eq_true.1 m23_G1_check.2 x hxi)
      obtain ⟨r, hr, hrx⟩ := List.any_eq_true.1 hanyr
      exact ⟨e.1, List.mem_map.2 ⟨e, he, rfl⟩, r, hr, beq_iff_eq.1 hrx⟩)
    m23GenTab (by decide) gen_witnesses.2.1

theorem m22_gen3 :
    ∀ x : S22, x * x = 1 → x ≠ 1 →
      ∃ cs : List S22, cs.length = 3 ∧ Subgroup.closure (conjSet cs {x}) = ⊤ :=
  gen3_of_witnesses NativeSporadic.M22 m22rl m22a m22b (closure_pair_eq_top m22_eq _ _)
    (fun x hx => by
      obtain ⟨g, hg⟩ := m22_sylow.conj_into (Subgroup.zpowers x) (sq_eq_one_of_mem_zpowers hx)
      exact ⟨g, hg x (Subgroup.mem_zpowers x)⟩)
    _ (cover_of_g1cover _ m22_G1_check.2) m22GenTab (by decide) gen_witnesses.2.2.1

theorem m12_gen3 :
    ∀ x : S12, x * x = 1 → x ≠ 1 →
      ∃ cs : List S12, cs.length = 3 ∧ Subgroup.closure (conjSet cs {x}) = ⊤ :=
  gen3_of_witnesses NativeSporadic.M12 m12rl m12a m12b (closure_pair_eq_top m12_eq _ _)
    (fun x hx => by
      obtain ⟨g, hg⟩ := m12_sylow.conj_into (Subgroup.zpowers x) (sq_eq_one_of_mem_zpowers hx)
      exact ⟨g, hg x (Subgroup.mem_zpowers x)⟩)
    _ (cover_of_g1cover _ m12_G1_check.2) m12GenTab (by decide) gen_witnesses.2.2.2

section Bound

variable {V : Type} [CommGroup V] [Finite V] {L : Subgroup (MulAut V)}

omit [Finite V] in
theorem fixV_eq_bot_of_irr (hirr : ∀ U : Subgroup V, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hLne : L ≠ ⊥) : fixV L = ⊥ := by
  rcases hirr (fixV L) (fun g hg u hu => by rw [hu g hg]; exact hu) with h | h
  · exact h
  · exfalso
    apply hLne
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    ext v
    exact (h ▸ Subgroup.mem_top v : v ∈ fixV L) g hg

theorem card_le_index_pow_of_gen
    (hirr : ∀ U : Subgroup V, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) (hLne : L ≠ ⊥)
    {B : Subgroup (MulAut V)} (cs : List ↥L) (hgen : Subgroup.closure (conjGen B cs) = ⊤) :
    Nat.card V ≤ (fixV B).index ^ cs.length := by
  have hle : L ≤ conjSup B (liftW cs) := by
    have h := map_closure_conjGen_le B cs
    rwa [hgen, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  have hbot : fixV (conjSup B (liftW cs)) = ⊥ :=
    eq_bot_iff.2 ((CFSG.QuasithinUnique.Setup.X1.fixV_anti hle).trans
      (fixV_eq_bot_of_irr hirr hLne).le)
  have h := index_fixV_conjSup_le B (liftW cs)
  rwa [hbot, Subgroup.index_bot, length_liftW] at h

theorem card_le_index_pow_three {S : Type} [Group S] (θ : ↥L ≃* S)
    (hS : ∀ x : S, x * x = 1 → x ≠ 1 →
      ∃ cs : List S, cs.length = 3 ∧ Subgroup.closure (conjSet cs {x}) = ⊤)
    (hirr : ∀ U : Subgroup V, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    {b : MulAut V} (hbL : b ∈ L) (hb2 : b * b = 1) (hb1 : b ≠ 1) :
    Nat.card V ≤ (fixV (Subgroup.zpowers b)).index ^ 3 := by
  have hLne : L ≠ ⊥ := fun h => hb1 (by rw [h] at hbL; exact (Subgroup.mem_bot).1 hbL)
  set b' : ↥L := ⟨b, hbL⟩
  have hx2 : θ b' * θ b' = 1 := by
    rw [← map_mul]
    have : b' * b' = 1 := Subtype.ext hb2
    rw [this, map_one]
  have hx1 : θ b' ≠ 1 := fun h =>
    hb1 (congrArg Subtype.val (θ.injective (h.trans (map_one θ).symm)))
  obtain ⟨cs, hcs, htop⟩ := hS (θ b') hx2 hx1
  have hgen : Subgroup.closure (conjGen (Subgroup.zpowers b) (cs.map θ.symm)) = ⊤ := by
    have hmap : Subgroup.closure (conjSet cs {θ b'}) ≤
        (Subgroup.closure (conjGen (Subgroup.zpowers b) (cs.map θ.symm))).map θ.toMonoidHom := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨c, hc, t, ht, rfl⟩
      rw [Set.mem_singleton_iff.1 ht]
      refine Subgroup.subset_closure ⟨θ.symm c * b' * (θ.symm c)⁻¹,
        ⟨θ.symm c, List.mem_map.2 ⟨c, hc, rfl⟩, b', Subgroup.mem_zpowers b, rfl⟩, ?_⟩
      simp
    rw [htop, top_le_iff] at hmap
    rw [eq_top_iff]
    intro y _
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 (hmap ▸ Subgroup.mem_top (θ y))
    rwa [θ.injective hzy] at hz
  have h := card_le_index_pow_of_gen hirr hLne (cs.map θ.symm) hgen
  rwa [List.length_map, hcs] at h

end Bound

end CFSG.Quasithin.B45Mat
