module

public import CFSG.Quasithin.Background.Harris.KFact2d.Defs
public import CFSG.Quasithin.EmptyFaithful.SzN22Basic

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section Aux

variable {X : Type} [Group X]

private lemma mem_norm_inf {t : X} {A B : Subgroup X}
    (hA : t ∈ Subgroup.normalizer (A : Set X)) (hB : t ∈ Subgroup.normalizer (B : Set X)) :
    t ∈ Subgroup.normalizer ((A ⊓ B : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro h
  have h1 := hA h
  have h2 := hB h
  simp only [Subgroup.mem_inf] at h1 h2 ⊢
  tauto

private lemma conj_mem_centralizer {t : X} {A : Subgroup X}
    (hA : t ∈ Subgroup.normalizer (A : Set X)) {h : X}
    (hh : h ∈ Subgroup.centralizer (A : Set X)) :
    t * h * t⁻¹ ∈ Subgroup.centralizer (A : Set X) := by
  rw [Subgroup.mem_centralizer_iff] at hh ⊢
  intro g hg
  have hg' : t⁻¹ * g * t ∈ A := by
    have := (Subgroup.mem_normalizer_iff.mp hA (t⁻¹ * g * t)).mpr
    apply this
    simpa [mul_assoc] using hg
  have := hh _ hg'
  calc g * (t * h * t⁻¹) = t * ((t⁻¹ * g * t) * h) * t⁻¹ := by group
    _ = t * (h * (t⁻¹ * g * t)) * t⁻¹ := by rw [this]
    _ = t * h * t⁻¹ * g := by group

private lemma mem_norm_centralizer {t : X} {A : Subgroup X}
    (hA : t ∈ Subgroup.normalizer (A : Set X)) :
    t ∈ Subgroup.normalizer ((Subgroup.centralizer (A : Set X) : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_centralizer hA hh, fun hh => ?_⟩
  have hA' : t⁻¹ ∈ Subgroup.normalizer (A : Set X) := (Subgroup.normalizer _).inv_mem hA
  have := conj_mem_centralizer hA' hh
  simpa [mul_assoc] using this

private lemma le_normalizer_of_inv {T B : Subgroup X}
    (h : ∀ t ∈ T, ∀ x ∈ B, t * x * t⁻¹ ∈ B) : T ≤ Subgroup.normalizer (B : Set X) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h t ht x hx, fun hx => ?_⟩
  have := h t⁻¹ (T.inv_mem ht) _ hx
  simpa [mul_assoc] using this

private lemma odd_orderOf_conj {t x : X} (hx : Odd (orderOf x)) : Odd (orderOf (t * x * t⁻¹)) := by
  have : orderOf (t * x * t⁻¹) = orderOf x := by
    have := orderOf_injective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective x
    simpa using this
  rwa [this]

private def oddSub (Z : Subgroup X) (hc : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) : Subgroup X where
  carrier := {x | x ∈ Z ∧ Odd (orderOf x)}
  one_mem' := ⟨Z.one_mem, by simp⟩
  mul_mem' := by
    rintro x y ⟨hxZ, hx⟩ ⟨hyZ, hy⟩
    refine ⟨Z.mul_mem hxZ hyZ, ?_⟩
    have hd := (show Commute x y from hc x hxZ y hyZ).orderOf_mul_dvd_mul_orderOf
    exact (hx.mul hy).of_dvd_nat hd
  inv_mem' := by
    rintro x ⟨hxZ, hx⟩
    exact ⟨Z.inv_mem hxZ, by simpa using hx⟩

private lemma exists_minimal_inv [Finite X] (T O : Subgroup X) (hO : O ≠ ⊥)
    (hTO : ∀ t ∈ T, ∀ x ∈ O, t * x * t⁻¹ ∈ O) :
    ∃ B : Subgroup X, B ≤ O ∧ B ≠ ⊥ ∧ (∀ t ∈ T, ∀ x ∈ B, t * x * t⁻¹ ∈ B) ∧
      ∀ B' : Subgroup X, B' ≤ B → B' ≠ ⊥ → (∀ t ∈ T, ∀ x ∈ B', t * x * t⁻¹ ∈ B') → B' = B := by
  obtain ⟨B, ⟨hBO, hB0, hBi⟩, hmin⟩ :=
    (measure (fun B : Subgroup X => Nat.card B)).wf.has_min
      {B : Subgroup X | B ≤ O ∧ B ≠ ⊥ ∧ ∀ t ∈ T, ∀ x ∈ B, t * x * t⁻¹ ∈ B} ⟨O, le_rfl, hO, hTO⟩
  refine ⟨B, hBO, hB0, hBi, fun B' hB'B hB'0 hB'i => ?_⟩
  have := hmin B' ⟨hB'B.trans hBO, hB'0, hB'i⟩
  exact Subgroup.eq_of_le_of_card_ge hB'B (not_lt.mp this)

private lemma atom_minimal {T B B' : Subgroup X} (hinv : ∀ t ∈ T, ∀ x ∈ B, t * x * t⁻¹ ∈ B)
    (hmin : ∀ B'' : Subgroup X, B'' ≤ B → B'' ≠ ⊥ → (∀ t ∈ T, ∀ x ∈ B'', t * x * t⁻¹ ∈ B'') →
      B'' = B)
    (hB' : T ≤ B') (hlt : B' < T ⊔ B) : B' = T := by
  by_cases hbot : B' ⊓ B = ⊥
  · have hTN := le_normalizer_of_inv hinv
    refine le_antisymm (fun x hx => ?_) hB'
    obtain ⟨a, ha, e, he, rfl⟩ := SzN19.exists_mul_of_normalizes hTN (by rw [sup_comm] at hlt; exact hlt.le hx)
    have haB' : a ∈ B' := by
      have := B'.mul_mem hx (B'.inv_mem (hB' he))
      simpa using this
    have : a ∈ B' ⊓ B := ⟨haB', ha⟩
    rw [hbot, Subgroup.mem_bot] at this
    subst this
    simpa using he
  · exfalso
    have hinv' : ∀ t ∈ T, ∀ x ∈ B' ⊓ B, t * x * t⁻¹ ∈ B' ⊓ B := by
      intro t ht x hx
      refine ⟨?_, hinv t ht x hx.2⟩
      exact B'.mul_mem (B'.mul_mem (hB' ht) hx.1) (B'.inv_mem (hB' ht))
    have := hmin (B' ⊓ B) inf_le_right hbot hinv'
    have hBB' : B ≤ B' := by
      rw [← this]; exact inf_le_left
    exact absurd hlt (not_lt_of_ge (sup_le hB' hBB'))

end Aux

variable {X : Type} [Group X]

private lemma exists_mul_of_sup_eq_top {K T : Subgroup X} (hK : K.Normal) (hKT : K ⊔ T = ⊤)
    (m : X) : ∃ k ∈ K, ∃ t ∈ T, m = k * t := by
  have hTK : T ≤ Subgroup.normalizer (K : Set X) := by
    rw [@Subgroup.normalizer_eq_top _ _ K hK]; exact le_top
  exact SzN19.exists_mul_of_normalizes hTK (by rw [hKT]; exact Subgroup.mem_top m)

private lemma exists_nat_eq_one_of_odd_dvd_four {n : ℕ} (hn : Odd n) (hd : n ∣ 4) : n = 1 := by
  have : n ∣ 2 ^ 2 := by simpa using hd
  exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right 2 hn.coprime_two_right) this

private lemma eq_one_of_pow_four {c : X} (hc : c ^ 4 = 1) (ho : Odd (orderOf c)) : c = 1 := by
  have := exists_nat_eq_one_of_odd_dvd_four ho (orderOf_dvd_of_pow_eq_one hc)
  exact orderOf_eq_one_iff.mp this

theorem starStmt_of (h1 : F1Stmt) (h2 : F2Stmt) (h3 : F3Stmt) (h5 : F5Stmt) : StarStmt := by
  unfold StarStmt StarStmtFor
  intro X _ _ K T M V p _ hcase hV hVT hTV hAt
  obtain ⟨hA, hpp, hp2, hdisj, hMK⟩ := hcase
  by_cases hsmall : p = 3 ∨ p = 5 ∨ p = 7
  · exact h5 X K T M V p hsmall ⟨hA, hpp, hp2, hdisj, hMK⟩ hV hVT hTV hAt
  have hp11 : 11 ≤ p := by
    by_contra hlt
    have h11 : p < 11 := not_le.mp hlt
    have hp1 := hpp.two_le
    interval_cases p <;>
      (exfalso; first | exact hp2 rfl | (apply hsmall; simp; done) | (revert hpp; norm_num))
  have hL : IsL3U3 p ↥K :=
    hdisj.elim (fun h => Or.inl ⟨h.1, h.2⟩) (fun h => Or.inr ⟨h.1, h.2.1⟩)
  have hKn : K.Normal := hA.normal
  have hTK : T ≤ Subgroup.normalizer (K : Set X) := by
    rw [@Subgroup.normalizer_eq_top _ _ K hKn]; exact le_top
  have hTT : T ≤ Subgroup.normalizer (T : Set X) := Subgroup.le_normalizer
  set S : Subgroup X := T ⊓ K with hSdef
  have hSyl : IsSylowTwoOf S K :=
    SzN22.isSylowTwoOf_inf_normalized hA.minPar.isSylow le_top hTK
  have hTS : ∀ t ∈ T, t ∈ Subgroup.normalizer (S : Set X) := fun t ht =>
    mem_norm_inf (hTT ht) (hTK ht)
  have hTz : ∀ t ∈ T, t ∈ Subgroup.normalizer ((E2P.zOf S : Subgroup X) : Set X) := fun t ht =>
    mem_norm_inf (hTS t ht) (mem_norm_centralizer (hTS t ht))
  have hTC : ∀ t ∈ T, t ∈ Subgroup.normalizer ((cenZ K S : Subgroup X) : Set X) := fun t ht =>
    mem_norm_inf (hTK ht) (mem_norm_centralizer (hTz t ht))
  have hTZc : ∀ t ∈ T, t ∈ Subgroup.normalizer
      ((cenZ K S ⊓ Subgroup.centralizer (cenZ K S : Set X) : Subgroup X) : Set X) := fun t ht =>
    mem_norm_inf (hTC t ht) (mem_norm_centralizer (hTC t ht))
  have hTM : T ≤ M := hA.minPar.le
  have hCM : cenZ K S = M ⊓ K := hMK.symm
  set Zc : Subgroup X := cenZ K S ⊓ Subgroup.centralizer (cenZ K S : Set X) with hZc
  have hZcc : ∀ x ∈ Zc, ∀ y ∈ Zc, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp hx.2 y hy.1).symm
  obtain ⟨b, hbZ, hb1, hbodd⟩ := h2 X K S p hpp hp11 hL hSyl
  set O : Subgroup X := oddSub Zc hZcc with hOdef
  have hbO : b ∈ O := ⟨hbZ, hbodd⟩
  have hO0 : O ≠ ⊥ := fun h => hb1 (by rw [h] at hbO; simpa using hbO)
  have hTO : ∀ t ∈ T, ∀ x ∈ O, t * x * t⁻¹ ∈ O := fun t ht x hx =>
    ⟨(Subgroup.mem_normalizer_iff.mp (hTZc t ht) x).mp hx.1, odd_orderOf_conj hx.2⟩
  obtain ⟨B, hBO, hB0, hBinv, hBmin⟩ := exists_minimal_inv T O hO0 hTO
  have hBZ : ∀ x ∈ B, x ∈ Zc ∧ Odd (orderOf x) := fun x hx => hBO hx
  have hBM : B ≤ M := fun x hx => by
    have : x ∈ cenZ K S := (hBZ x hx).1.1
    rw [hCM] at this
    exact this.1
  set A : Subgroup X := T ⊔ B with hAdef
  have hAM : A ≤ M := sup_le hTM hBM
  have hAmin : ∀ B' : Subgroup X, T ≤ B' → B' ≤ A → B' = T ∨ B' = A :=
    fun B' hB' hle => by
      rcases hle.lt_or_eq with hlt | heq
      · exact Or.inl (atom_minimal hBinv hBmin hB' hlt)
      · exact Or.inr heq
  have hVK : V ≤ K := by
    intro u hu
    by_contra huK
    have hu2 : u * u = 1 := by have := hV.2 u hu; simpa [pow_two] using this
    obtain ⟨⟨c, hcB⟩, hc1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB0
    have hc1 : c ≠ 1 := fun h => hc1' (Subtype.ext h)
    have hcZ := hBZ c hcB
    have hinv : u * c * u⁻¹ = c⁻¹ :=
      h3 X K S p hpp hp2 hL hKn hA.cent hSyl u hu2 huK (hTS u (hVT hu)) c hcZ.1 hcZ.2
    have hcA : c ∈ A := Subgroup.mem_sup_right hcB
    have hinv' : u * c⁻¹ * u⁻¹ = c := by
      have := congrArg (·⁻¹) hinv
      simpa [mul_assoc] using this
    have hc4 : c ^ 4 = 1 := by
      by_cases hAn : A ≤ Subgroup.normalizer (V : Set X)
      · have h1' : c * u * c⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hAn hcA) u).mp hu
        have h2' : c * u * c⁻¹ * u⁻¹ ∈ V := V.mul_mem h1' (V.inv_mem hu)
        have h3' : c * u * c⁻¹ * u⁻¹ = c * c :=
          calc c * u * c⁻¹ * u⁻¹ = c * (u * c⁻¹ * u⁻¹) := by group
            _ = c * c := by rw [hinv']
        rw [h3'] at h2'
        calc c ^ 4 = (c * c) ^ 2 := by rw [← pow_two, ← pow_mul]
          _ = 1 := hV.2 _ h2'
      · have hW := hAt A le_sup_left hAM hAn hAmin
        have hu1 : u ∈ conjClosure V A := le_conjClosure V A hu
        have hu' : c * u * c⁻¹ ∈ conjClosure V A := mem_conjClosure hcA hu
        have hm := (conjClosure V A).mul_mem hu1 ((conjClosure V A).inv_mem hu')
        have hsq := hW.2 _ hm
        have e : u * (c * u * c⁻¹)⁻¹ = c⁻¹ * c⁻¹ :=
          calc u * (c * u * c⁻¹)⁻¹ = (u * c * u⁻¹) * c⁻¹ := by group
            _ = c⁻¹ * c⁻¹ := by rw [hinv]
        rw [e] at hsq
        calc c ^ 4 = ((c⁻¹ * c⁻¹) ^ 2)⁻¹ := by group
          _ = 1 := by rw [hsq]; simp
    exact hc1 (eq_one_of_pow_four hc4 hcZ.2)
  have hVS : V ≤ S := fun v hv => ⟨hVT hv, hVK hv⟩
  have hSV : S ≤ Subgroup.normalizer (V : Set X) := fun s hs => hTV hs.1
  have hVz : V ≤ E2P.zOf S := h1 X K S p hpp hp2 hL hSyl V hV hVS hSV
  refine hVz.trans ?_
  have hzS : E2P.zOf S ≤ S := inf_le_left
  have hz2 : IsPGroup 2 ↥(E2P.zOf S) :=
    hSyl.2.1.of_injective (Subgroup.inclusion hzS) (Subgroup.inclusion_injective hzS)
  have hnorm : M ≤ Subgroup.normalizer ((E2P.zOf S : Subgroup X) : Set X) := by
    intro m hm
    obtain ⟨k, hk, t, ht, rfl⟩ := exists_mul_of_sup_eq_top hKn hA.sup m
    have hkM : k ∈ M := by
      have := M.mul_mem hm (M.inv_mem (hTM ht))
      simpa using this
    have hkC : k ∈ cenZ K S := by rw [hCM]; exact ⟨hkM, hk⟩
    exact (Subgroup.normalizer _).mul_mem
      (Subgroup.centralizer_le_normalizer _ hkC.2) (hTz t ht)
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (hzS.trans (inf_le_left.trans hTM)) hnorm hz2

end CFSG.Quasithin.Background.Harris.KFact2d
