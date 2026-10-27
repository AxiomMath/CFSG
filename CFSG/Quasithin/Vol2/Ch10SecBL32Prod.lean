module

public import CFSG.Quasithin.Vol2.Ch10SecBL32K

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.L32

theorem u_conj_not_le : (∃ g : Γ, ∃ u ∈ uList, ¬ IsPa (g * u * g⁻¹)) ∧
    ∃ g : Γ, ∃ u ∈ uList, ¬ IsPb (g * u * g⁻¹) := by
  unfold uList IsPa IsPb ent; decide +kernel

theorem isPa_of_isU {g : Γ} (h : IsU g) : IsPa g := ⟨h.1, h.2.1⟩
theorem isPb_of_isU {g : Γ} (h : IsU g) : IsPb g := ⟨h.2.1, h.2.2⟩
theorem u3_le_pa : U3 ≤ Pa := fun _ h => isPa_of_isU h
theorem u3_le_pb : U3 ≤ Pb := fun _ h => isPb_of_isU h

theorem s2_not_mem_pa : s2 ∉ Pa := s_mem.2.2.2.2.2
theorem s1_not_mem_pb : s1 ∉ Pb := s_mem.2.2.2.2.1

theorem eq_pa_of_normal {N : Subgroup Γ} (hUN : U3 ≤ N) (hNP : N ≤ Pa)
    (hnorm : ∀ g ∈ Pa, ∀ n ∈ N, g * n * g⁻¹ ∈ N) : N = Pa := by
  rcases overgroups N hUN with h | h | h | h
  · exfalso
    obtain ⟨g, hg, u, hu, hn⟩ := u_not_normal_a
    have := hnorm g hg u (hUN ((mem_uList_iff u).mp hu))
    rw [h] at this
    exact hn this
  · exact h
  · exact absurd (hNP (h ▸ s_mem.2.2.1 : s2 ∈ N)) s2_not_mem_pa
  · exact absurd (hNP (h ▸ Subgroup.mem_top s2)) s2_not_mem_pa

theorem eq_pb_of_normal {N : Subgroup Γ} (hUN : U3 ≤ N) (hNP : N ≤ Pb)
    (hnorm : ∀ g ∈ Pb, ∀ n ∈ N, g * n * g⁻¹ ∈ N) : N = Pb := by
  rcases overgroups N hUN with h | h | h | h
  · exfalso
    obtain ⟨g, hg, u, hu, hn⟩ := u_not_normal_b
    have := hnorm g hg u (hUN ((mem_uList_iff u).mp hu))
    rw [h] at this
    exact hn this
  · exact absurd (hNP (h ▸ s_mem.1 : s1 ∈ N)) s1_not_mem_pb
  · exact h
  · exact absurd (hNP (h ▸ Subgroup.mem_top s1)) s1_not_mem_pb

theorem eq_top_of_normal {N : Subgroup Γ} (hUN : U3 ≤ N)
    (hnorm : ∀ g : Γ, ∀ n ∈ N, g * n * g⁻¹ ∈ N) : N = ⊤ := by
  obtain ⟨⟨g, u, hu, hn⟩, ⟨g', u', hu', hn'⟩⟩ := u_conj_not_le
  rcases overgroups N hUN with h | h | h | h
  · exact absurd (h ▸ hnorm g u (hUN ((mem_uList_iff u).mp hu)) : g * u * g⁻¹ ∈ U3)
      fun hU => hn (isPa_of_isU hU)
  · exact absurd (h ▸ hnorm g u (hUN ((mem_uList_iff u).mp hu)) : g * u * g⁻¹ ∈ Pa) hn
  · exact absurd (h ▸ hnorm g' u' (hUN ((mem_uList_iff u').mp hu')) : g' * u' * g'⁻¹ ∈ Pb) hn'
  · exact h

theorem prod_classify {B : Subgroup (Γ × Γ)} {c : Γ} (hc : IsU c) (hUB : U3.prod U3 ≤ B)
    (hσ : ∀ p ∈ B, (c * p.2 * c⁻¹, p.1) ∈ B) :
    ∃ A : Subgroup Γ, (A = U3 ∨ A = Pa ∨ A = Pb ∨ A = ⊤) ∧ B = A.prod A := by
  let A : Subgroup Γ := B.map (MonoidHom.fst Γ Γ)
  let N : Subgroup Γ := B.comap (MonoidHom.inl Γ Γ)
  have hUA : U3 ≤ A := fun u hu => ⟨(u, 1), hUB ⟨hu, U3.one_mem⟩, rfl⟩
  have hUN : U3 ≤ N := fun u hu => hUB ⟨hu, U3.one_mem⟩
  have hNA : N ≤ A := fun n hn => ⟨(n, 1), hn, rfl⟩
  have hnorm : ∀ g ∈ A, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    rintro g ⟨p, hp, rfl⟩ n hn
    have h := B.mul_mem (B.mul_mem hp hn) (B.inv_mem hp)
    have heq : p * (n, 1) * p⁻¹ = (p.1 * n * p.1⁻¹, 1) := by ext <;> simp
    show (p.1 * n * p.1⁻¹, (1 : Γ)) ∈ B
    rw [← heq]
    exact h
  have hNeq : N = A := by
    rcases overgroups A hUA with h | h | h | h
    · exact le_antisymm hNA (h ▸ hUN)
    · rw [h] at hNA hnorm ⊢; exact eq_pa_of_normal hUN hNA hnorm
    · rw [h] at hNA hnorm ⊢; exact eq_pb_of_normal hUN hNA hnorm
    · rw [h] at hnorm ⊢; exact eq_top_of_normal hUN fun g n hn => hnorm g (Subgroup.mem_top g) n hn
  have hcA : c ∈ A := hUA hc
  refine ⟨A, overgroups A hUA, le_antisymm ?_ ?_⟩
  · intro p hp
    refine ⟨⟨p, hp, rfl⟩, ?_⟩
    have h := hσ p hp
    have hmem : c * p.2 * c⁻¹ ∈ A := ⟨_, h, rfl⟩
    have := A.mul_mem (A.mul_mem (A.inv_mem hcA) hmem) hcA
    simpa [mul_assoc] using this
  · intro p hp
    obtain ⟨h1, h2⟩ := hp
    have hp1 : (p.1, (1 : Γ)) ∈ B := (hNeq ▸ h1 : p.1 ∈ N)
    have hp2 : ((1 : Γ), p.2) ∈ B := by
      have := hσ _ (hNeq ▸ h2 : p.2 ∈ N)
      simpa using this
    have := B.mul_mem hp1 hp2
    simpa using this

theorem ka_cosets : ∀ x k : Γ, IsKa x → ¬ IsEa x → IsKa k →
    IsEa k ∨ IsEa (k * x⁻¹) ∨ IsEa (k * x⁻¹ * x⁻¹) := by
  decide +kernel

theorem kb_cosets : ∀ x k : Γ, IsKb x → ¬ IsEb x → IsKb k →
    IsEb k ∨ IsEb (k * x⁻¹) ∨ IsEb (k * x⁻¹ * x⁻¹) := by
  decide +kernel

theorem ka_inv' : ∃ d ∈ uList, ∀ x : Γ, IsKa x → ¬ IsEa x →
    IsKa (x⁻¹ * d * x * d⁻¹) ∧ ¬ IsEa (x⁻¹ * d * x * d⁻¹) := by
  unfold uList; decide +kernel

theorem kb_inv' : ∃ d ∈ uList, ∀ x : Γ, IsKb x → ¬ IsEb x →
    IsKb (x⁻¹ * d * x * d⁻¹) ∧ ¬ IsEb (x⁻¹ * d * x * d⁻¹) := by
  unfold uList; decide +kernel

theorem prod_irred_of {K E : Subgroup Γ} {B : Subgroup (Γ × Γ)} {c : Γ}
    (hcK : ∀ k, c * k * c⁻¹ ∈ K ↔ k ∈ K) (hcE : ∀ e, c * e * c⁻¹ ∈ E ↔ e ∈ E)
    (hcos : ∀ x k : Γ, x ∈ K → x ∉ E → k ∈ K → k ∈ E ∨ k * x⁻¹ ∈ E ∨ k * x⁻¹ * x⁻¹ ∈ E)
    (hinv : ∃ d ∈ uList, ∀ x : Γ, x ∈ K → x ∉ E → x⁻¹ * d * x * d⁻¹ ∈ K ∧
      x⁻¹ * d * x * d⁻¹ ∉ E)
    (hEB : E.prod E ≤ B) (hBK : B ≤ K.prod K)
    (hU : ∀ u ∈ U3.prod U3, ∀ p ∈ B, u * p * u⁻¹ ∈ B) (hσ : ∀ p ∈ B, (c * p.2 * c⁻¹, p.1) ∈ B) :
    B = E.prod E ∨ B = K.prod K := by
  by_cases hB : B ≤ E.prod E
  · exact Or.inl (le_antisymm hB hEB)
  right
  obtain ⟨d, hd, hdinv⟩ := hinv
  have hdU : d ∈ U3 := (mem_uList_iff d).mp hd
  have key : ∀ x ∈ K, x ∉ E → ∀ b, (x, b) ∈ B → K.prod ⊥ ≤ B := by
    intro x hxK hxE b hxb
    have h1 : ((d, 1) : Γ × Γ) * (x, b) * (d, 1)⁻¹ ∈ B := hU _ ⟨hdU, U3.one_mem⟩ _ hxb
    have h2 := B.mul_mem (B.inv_mem hxb) h1
    have heq : (x, b)⁻¹ * (((d, 1) : Γ × Γ) * (x, b) * (d, 1)⁻¹) = (x⁻¹ * d * x * d⁻¹, 1) := by
      ext <;> simp [mul_assoc]
    rw [heq] at h2
    obtain ⟨hyK, hyE⟩ := hdinv x hxK hxE
    set y := x⁻¹ * d * x * d⁻¹
    intro p hp
    obtain ⟨hp1, hp2⟩ := hp
    have hp2' : p.2 = 1 := hp2
    have hy1 : ∀ e ∈ E, (e, (1 : Γ)) ∈ B := fun e he => hEB ⟨he, E.one_mem⟩
    have hpe : p = (p.1, 1) := by ext <;> simp [hp2']
    rw [hpe]
    rcases hcos y p.1 hyK hyE hp1 with h | h | h
    · exact hy1 _ h
    · have := B.mul_mem (hy1 _ h) h2
      simpa using this
    · have := B.mul_mem (B.mul_mem (hy1 _ h) h2) h2
      simpa [mul_assoc] using this
  have hK1 : K.prod ⊥ ≤ B := by
    obtain ⟨p, hpB, hpE⟩ := Set.not_subset.mp hB
    obtain ⟨hp1, hp2⟩ := hBK hpB
    by_cases h1 : p.1 ∈ E
    · have h2 : p.2 ∉ E := fun h => hpE ⟨h1, h⟩
      exact key _ ((hcK _).mpr hp2) (fun h => h2 ((hcE _).mp h)) _ (hσ p hpB)
    · exact key p.1 hp1 h1 p.2 hpB
  refine le_antisymm hBK fun p hp => ?_
  obtain ⟨hp1, hp2⟩ := hp
  have ha : (p.1, (1 : Γ)) ∈ B := hK1 ⟨hp1, Subgroup.mem_bot.mpr rfl⟩
  have hb : ((1 : Γ), p.2) ∈ B := by
    have := hσ _ (hK1 ⟨hp2, Subgroup.mem_bot.mpr rfl⟩ : (p.2, (1 : Γ)) ∈ B)
    simpa using this
  have := B.mul_mem ha hb
  simpa using this

theorem ka_prod_irred {B : Subgroup (Γ × Γ)} {c : Γ} (hc : IsU c) (hEB : Ea.prod Ea ≤ B)
    (hBK : B ≤ Ka.prod Ka) (hU : ∀ u ∈ U3.prod U3, ∀ p ∈ B, u * p * u⁻¹ ∈ B)
    (hσ : ∀ p ∈ B, (c * p.2 * c⁻¹, p.1) ∈ B) : B = Ea.prod Ea ∨ B = Ka.prod Ka := by
  have hcP : IsPa c := isPa_of_isU hc
  have hcP' : IsPa c⁻¹ := isPa_inv c hcP
  refine prod_irred_of (fun k => ⟨fun h => ?_, fun h => ka_normal c k hcP h⟩)
    (fun e => ⟨fun h => ?_, fun h => ea_normal c e hcP h⟩)
    (fun x k hx hxE hk => ka_cosets x k hx hxE hk) ka_inv' hEB hBK hU hσ
  · have := ka_normal c⁻¹ _ hcP' h
    show _ ∈ _
    rw [mem_Ka]
    simpa [mul_assoc] using this
  · have := ea_normal c⁻¹ _ hcP' h
    show _ ∈ _
    rw [mem_Ea]
    simpa [mul_assoc] using this

theorem kb_prod_irred {B : Subgroup (Γ × Γ)} {c : Γ} (hc : IsU c) (hEB : Eb.prod Eb ≤ B)
    (hBK : B ≤ Kb.prod Kb) (hU : ∀ u ∈ U3.prod U3, ∀ p ∈ B, u * p * u⁻¹ ∈ B)
    (hσ : ∀ p ∈ B, (c * p.2 * c⁻¹, p.1) ∈ B) : B = Eb.prod Eb ∨ B = Kb.prod Kb := by
  have hcP : IsPb c := isPb_of_isU hc
  have hcP' : IsPb c⁻¹ := isPb_inv c hcP
  refine prod_irred_of (fun k => ⟨fun h => ?_, fun h => kb_normal c k hcP h⟩)
    (fun e => ⟨fun h => ?_, fun h => eb_normal c e hcP h⟩)
    (fun x k hx hxE hk => kb_cosets x k hx hxE hk) kb_inv' hEB hBK hU hσ
  · have := kb_normal c⁻¹ _ hcP' h
    show _ ∈ _
    rw [mem_Kb]
    simpa [mul_assoc] using this
  · have := eb_normal c⁻¹ _ hcP' h
    show _ ∈ _
    rw [mem_Eb]
    simpa [mul_assoc] using this

end CFSG.Quasithin.Vol2.Ch10.SecB.L32
