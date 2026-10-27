module

public import Certificates.Kernel.Co2I301.SixBind
public import CFSG.Certificates.Kernel.Co2I301.Group
public import CFSG.Sporadic.Co2I301.Facts

public section

namespace CertificateChecks.KernelCo2I301

open CFSG.KC.Enum CFSG.KC.Co2I301 CFSG.KS CFSG.KS.Co2I301 CFSG.Sporadic.Co2I301
  CFSG.Sporadic.Co2Schreier CFSG.Monster.B.Co2

@[expose] def G6 : Subgroup (Equiv.Perm (Fin 63)) :=
  Subgroup.closure {π : Equiv.Perm (Fin 63) | ∃ i < 2, sixPi i = π}

@[expose] noncomputable def tgP (h : ℕ) : Equiv.Perm (Fin 63) := wordPerm sixPi (SX.tgw.getD h [])

@[expose] noncomputable def T6 : Subgroup (Equiv.Perm (Fin 63)) :=
  Subgroup.closure {t : Equiv.Perm (Fin 63) | ∃ h < 4, tgP h = t}

section Six


theorem sixPi_mem {g : ℕ} (hg : g < 2) : sixPi g ∈ G6 := Subgroup.subset_closure ⟨g, hg, rfl⟩

theorem card_G6 : Nat.card G6 = 1451520 := by
  rw [G6, ← sixChain_original]
  exact card_sixChain

theorem r7_TG {h : ℕ} (hh : h < 4) : R7 (TG h) (tgP h) := by
  rw [beq_true (allN_spec tg_ok h hh)]
  exact r7_wP (fun g hg => r7_PI hg) (fun g hg => r7_PII hg) _ (tw_ok h hh)

theorem tgP_mem {h : ℕ} (hh : h < 4) : tgP h ∈ G6 :=
  wordPerm_mem (fun _ hg => sixPi_mem hg) _ (tw_ok h hh)

theorem T6_le : T6 ≤ G6 := by
  rw [T6, Subgroup.closure_le]
  rintro _ ⟨h, hh, rfl⟩
  exact tgP_mem hh

theorem t_spec {j : ℕ} (hj : j < 512) :
    (tDep (TR j) = 0 → cd (TR j) = idc) ∧
    (tDep (TR j) ≠ 0 → tPar (TR j) < 512 ∧ tLet (TR j) < 4 ∧
      tDep (TR (tPar (TR j))) + 1 = tDep (TR j) ∧
      cd (TR j) = cp (cd (TR (tPar (TR j)))) (TG (tLet (TR j)))) ∧
    incr TR 512 j = true ∧
    (∀ g < 4, tTgt (TR j) g < 512 ∧ cd (TR (tTgt (TR j) g)) = cp (cd (TR j)) (TG g)) ∧
    (cp (cd (TR j)) (cd (TR j)) = idc → cd (TR j) ≠ idc →
      tInv (TR j) < 5103 ∧ cd (SR (tInv (TR j))) = cd (TR j)) :=
  tRec_spec (allN_spec t_ok j hj)

theorem t_mem : ∀ j < 512, ∃ t ∈ T6, R7 (cd (TR j)) t :=
  dep_ind (fun j => tDep (TR j)) (fun j => tPar (TR j)) (fun j => ∃ t ∈ T6, R7 (cd (TR j)) t)
    (fun j hj e => ⟨1, Subgroup.one_mem _, by rw [(t_spec hj).1 e]; exact r7_idc⟩)
    fun j hj e => by
      obtain ⟨hp, hl, hd, hc⟩ := (t_spec hj).2.1 e
      refine ⟨hp, hd, fun ⟨t, ht, hr⟩ => ⟨t * tgP (tLet (TR j)), Subgroup.mul_mem _ ht
        (Subgroup.subset_closure ⟨_, hl, rfl⟩), ?_⟩⟩
      rw [hc]
      exact r7_cp hr (r7_TG hl)

theorem t_cover : ∀ c ∈ T6, ∃ j < 512, R7 (cd (TR j)) c := by
  have key := closure_subset_of_mul (M := {c | ∃ j < 512, R7 (cd (TR j)) c})
    (S := {t | ∃ h < 4, tgP h = t}) ⟨511, by norm_num, by rw [beq_true troot]; exact r7_idc⟩
    (by
      rintro m ⟨j, hj, hm⟩ _ ⟨h, hh, rfl⟩
      obtain ⟨ht, hc⟩ := (t_spec hj).2.2.2.1 h hh
      exact ⟨_, ht, by rw [hc]; exact r7_cp hm (r7_TG hh)⟩)
  exact fun c hc => key hc

theorem card_T6 : Nat.card T6 = 2 ^ 9 := by
  choose! z hzT hz using t_mem
  have hinc : ∀ j < 512, incr TR 512 j = true := fun j hj => (t_spec hj).2.2.1
  refine card_eq_of_cover z hzT (fun i hi j hj e => incr_perm_inj hinc hi hj (hz i hi)
    (e ▸ hz j hj)) fun c hc => ?_
  obtain ⟨j, hj, hr⟩ := t_cover c hc
  exact ⟨j, hj, r7_unique (hz j hj) hr⟩

theorem s_spec {j : ℕ} (hj : j < 5103) :
    (∀ g < 2, sTgt (SR j) g < 5103 ∧ cd (SR (sTgt (SR j) g)) = cj (PI g) (PII g) (cd (SR j))) ∧
    sWd (SR j) < 3 ∧ sPt (SR j) < 63 ∧
    pt (cd (SR j)) (ysy HL HLI (sWd (SR j)) (cd (SR j)) (sPt (SR j))) ≠
      ysy HL HLI (sWd (SR j)) (cd (SR j)) (pt (cd (SR j)) (sPt (SR j))) :=
  sRec_spec (allN_spec s_ok j hj)

theorem s_conj : ∀ x ∈ G6, ∀ m ∈ {s : Equiv.Perm (Fin 63) | ∃ j < 5103, R7 (cd (SR j)) s},
    x * m * x⁻¹ ∈ {s : Equiv.Perm (Fin 63) | ∃ j < 5103, R7 (cd (SR j)) s} := by
  refine conj_mem_of_closure ?_
  rintro m ⟨j, hj, hm⟩ _ ⟨g, hg, rfl⟩
  obtain ⟨ht, hc⟩ := (s_spec hj).1 g hg
  exact ⟨_, ht, by rw [hc]; exact r7_cj (r7_PI hg) (r7_PII hg) hm⟩

theorem t_inv_mem {t : Equiv.Perm (Fin 63)} (ht : t ∈ T6) (htt : t * t = 1) (ht1 : t ≠ 1) :
    ∃ j < 5103, R7 (cd (SR j)) t := by
  obtain ⟨j, hj, hr⟩ := t_cover t ht
  have e1 : cp (cd (TR j)) (cd (TR j)) = idc :=
    eq_of_r7 (cp_shr _ _) idc_shr (r7_cp hr hr) (by rw [htt]; exact r7_idc)
  have e2 : cd (TR j) ≠ idc := fun e => ht1 (r7_unique hr (by rw [e]; exact r7_idc))
  obtain ⟨hi, hc⟩ := (t_spec hj).2.2.2.2 e1 e2
  exact ⟨_, hi, by rw [hc]; exact hr⟩

theorem s_wit {s : Equiv.Perm (Fin 63)} {j : ℕ} (hj : j < 5103) (hs : R7 (cd (SR j)) s) :
    ∃ t < 3, ¬ Commute s (permOfArr 63 (hl63 ())[t]! * s * (permOfArr 63 (hl63 ())[t]!)⁻¹) := by
  obtain ⟨-, ht, hp, hne⟩ := s_spec hj
  refine ⟨_, ht, fun hc => hne ?_⟩
  set Y := permOfArr 63 (hl63 ())[sWd (SR j)]!
  have hY := r7_HL ht
  have hYI := r7_HLI ht
  have hy : ∀ q : Fin 63, ysy HL HLI (sWd (SR j)) (cd (SR j)) q = (Y * s * Y⁻¹) q := by
    intro q
    unfold ysy
    rw [r7_apply hYI q, r7_apply hs, r7_apply hY]
    rfl
  have h1 := congrArg (fun f : Equiv.Perm (Fin 63) => (f ⟨sPt (SR j), hp⟩ : ℕ)) hc.eq
  simp only [Equiv.Perm.mul_apply] at h1
  rw [hy ⟨_, hp⟩, r7_apply hs]
  have e : ((Y * s * Y⁻¹) ⟨sPt (SR j), hp⟩ : ℕ) = ((Y * s * Y⁻¹) ⟨sPt (SR j), hp⟩ : Fin 63) := rfl
  rw [show pt (cd (SR j)) (sPt (SR j)) = (s ⟨sPt (SR j), hp⟩ : ℕ) from r7_apply hs ⟨_, hp⟩,
    show (s ⟨sPt (SR j), hp⟩ : ℕ) = ((s ⟨sPt (SR j), hp⟩ : Fin 63) : ℕ) from rfl,
    hy (s ⟨sPt (SR j), hp⟩)]
  simpa [Equiv.Perm.mul_apply] using h1

theorem six_facts : RowSixFacts := by
  intro Y hY g hg hgg hg1
  have hodd : ¬ 2 ∣ Nat.card G6 / Nat.card T6 := by rw [card_G6, card_T6]; decide
  obtain ⟨h, hh, hu⟩ := exists_conj_mem_of_sylow T6_le card_T6 hodd hg hgg
  have huu : h⁻¹ * g * h * (h⁻¹ * g * h) = 1 := by
    have e : h⁻¹ * g * h * (h⁻¹ * g * h) = h⁻¹ * (g * g) * h := by group
    rw [e, hgg]
    group
  have hu1 : h⁻¹ * g * h ≠ 1 := fun e => hg1 (by
    have e' : g = h * (h⁻¹ * g * h) * h⁻¹ := by group
    rw [e', e]
    group)
  have hs := t_inv_mem hu huu hu1
  have hg' := s_conj h hh _ hs
  have e : h * (h⁻¹ * g * h) * h⁻¹ = g := by group
  rw [e] at hg'
  obtain ⟨j, hj, hr⟩ := hg'
  obtain ⟨t, ht, hc⟩ := s_wit hj hr
  have hts : t < (hl63 ()).size := by rw [hl63_size]; exact ht
  have h1 := CFSG.KS.Raw.Orb.rep_unpack (r7_HL ht)
  rw [← hl63_get ht] at h1
  have hYt : Y t = permOfArr 63 (hl63 ())[t]! := (hY t hts).unique h1
  exact ⟨t, hts, by rw [hYt]; exact hc⟩

end Six

end CertificateChecks.KernelCo2I301

end
