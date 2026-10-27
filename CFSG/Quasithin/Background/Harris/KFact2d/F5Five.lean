module

public import CFSG.Quasithin.Background.Harris.KFact2d.F5FiveOuter
public import CFSG.Quasithin.Background.Harris.KFact2d.F1
public import CFSG.Quasithin.Background.Harris.KFact2d.CaseI
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.F5Setup
public import CFSG.Quasithin.EmptyFaithful.SzN22Basic

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Subgroup
open CFSG.Quasithin.Background.Harris.OrdinaryProofs

variable {X : Type} [Group X]

private lemma mem_norm_inf' {t : X} {A B : Subgroup X}
    (hA : t ∈ Subgroup.normalizer (A : Set X)) (hB : t ∈ Subgroup.normalizer (B : Set X)) :
    t ∈ Subgroup.normalizer ((A ⊓ B : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro h
  have h1 := hA h
  have h2 := hB h
  simp only [Subgroup.mem_inf] at h1 h2 ⊢
  tauto

private lemma conj_mem_centralizer' {t : X} {A : Subgroup X}
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

private lemma mem_norm_centralizer' {t : X} {A : Subgroup X}
    (hA : t ∈ Subgroup.normalizer (A : Set X)) :
    t ∈ Subgroup.normalizer ((Subgroup.centralizer (A : Set X) : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_centralizer' hA hh, fun hh => ?_⟩
  have hA' : t⁻¹ ∈ Subgroup.normalizer (A : Set X) := (Subgroup.normalizer _).inv_mem hA
  have := conj_mem_centralizer' hA' hh
  simpa [mul_assoc] using this

variable [Finite X]

theorem card_sylow_five {K S : Subgroup X} (hK : IsPSU 3 5 1 ↥K) (hS : IsSylowTwoOf S K) :
    Nat.card ↥S = 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_of_isSylowTwoOf'' hS
  have hKc : Nat.card ↥K = 126000 :=
    (CFSG.RankThree.Classical.unitary_three_five_model ↥K hK).1
  have h1 := Sylow.card_eq_multiplicity P
  rw [hKc] at h1
  have hv : (126000 : ℕ).factorization 2 = 4 := by
    rw [Nat.factorization_def _ Nat.prime_two]
    have : (126000 : ℕ) = 2 ^ 4 * 7875 := by norm_num
    rw [this, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  rw [hv] at h1
  have h2 : Nat.card ↥(S.subgroupOf K) = Nat.card ↥S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv
  rw [← h2, ← hP]
  simpa using h1

theorem exists_cover {T M : Subgroup X} (hTM : T ≤ M) (hne : T ≠ M) :
    ∃ A : Subgroup X, T < A ∧ A ≤ M ∧ ∀ B : Subgroup X, T ≤ B → B ≤ A → B = T ∨ B = A := by
  obtain ⟨A, ⟨hTA, hAM⟩, hmin⟩ := (measure (fun B : Subgroup X => Nat.card B)).wf.has_min
    {B : Subgroup X | T < B ∧ B ≤ M} ⟨M, lt_of_le_of_ne hTM hne, le_rfl⟩
  refine ⟨A, hTA, hAM, fun B hTB hBA => ?_⟩
  by_cases hBT : B = T
  · exact Or.inl hBT
  · right
    have hlt : T < B := lt_of_le_of_ne hTB (Ne.symm hBT)
    have := hmin B ⟨hlt, hBA.trans hAM⟩
    exact Subgroup.eq_of_le_of_card_ge hBA (not_lt.mp this)

theorem comm_mem_zOf {K T A W V S : Subgroup X} (hKn : K.Normal) (hSdef : S = T ⊓ K)
    (hS : IsSylowTwoOf S K) (hL : IsL3U3 5 ↥K) (hTA : T ≤ A) (hW : IsElemAbelian 2 W)
    (hVW : V ≤ W) (hAW : A ≤ Subgroup.normalizer (W : Set X)) :
    ∀ u ∈ V, ∀ x ∈ A ⊓ K, u * x * u⁻¹ * x⁻¹ ∈ E2P.zOf S := by
  intro u hu x hx
  have hKnorm : ∀ g : X, g ∈ Subgroup.normalizer (K : Set X) := fun g => by
    rw [@Subgroup.normalizer_eq_top _ _ K hKn]; exact Subgroup.mem_top g
  set E := W ⊓ K with hE
  have hEW : E ≤ W := inf_le_left
  have hE' : IsElemAbelian 2 E := isElemAbelian_mono hW hEW
  have hE2 : IsPGroup 2 ↥E := fun g => ⟨1, by
    have := hE'.2 (g : X) g.2
    simp only [pow_one]
    exact Subtype.ext (by simpa using this)⟩
  have hSA : S ≤ A := by rw [hSdef]; exact inf_le_left.trans hTA
  have hSN : S ≤ Subgroup.normalizer (E : Set X) := fun s hs =>
    mem_norm_inf' (hAW (hSA hs)) (hKnorm s)
  have hES : E ≤ S := by
    have hsup : IsPGroup 2 ↥(S ⊔ E) := hS.isPGroup.to_sup_of_normal_right' hE2 hSN
    have := hS.eq_of_le le_sup_left (sup_le hS.1 inf_le_right) hsup
    exact this ▸ le_sup_right
  have hz := f1_holds X K S 5 Nat.prime_five (by norm_num) hL hS E hE' hES hSN
  apply hz
  refine ⟨?_, hKn.conj_mem x hx.2 u |> fun h => K.mul_mem h (K.inv_mem hx.2)⟩
  have h1 : x * u⁻¹ * x⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hAW hx.1) u⁻¹).mp
    (W.inv_mem (hVW hu))
  have := W.mul_mem (hVW hu) h1
  simpa [mul_assoc] using this

theorem f5_five :
    StarStmtFor fun q => q = 5 := by
  intro X _ _ K T M V p hp hcase hV hVT hTV hAt
  subst hp
  obtain ⟨hA, hpp, hp2, hdisj, hMK⟩ := hcase
  have hK : IsPSU 3 5 1 ↥K := by
    rcases hdisj with ⟨-, h⟩ | ⟨h, -, -⟩
    · exact h
    · omega
  have hL : IsL3U3 5 ↥K := Or.inl ⟨by norm_num, hK⟩
  have hKn : K.Normal := hA.normal
  have hKnorm : ∀ g : X, g ∈ Subgroup.normalizer (K : Set X) := fun g => by
    rw [@Subgroup.normalizer_eq_top _ _ K hKn]; exact Subgroup.mem_top g
  have hTK : T ≤ Subgroup.normalizer (K : Set X) := fun t _ => hKnorm t
  have hTT : T ≤ Subgroup.normalizer (T : Set X) := Subgroup.le_normalizer
  set S : Subgroup X := T ⊓ K with hSdef
  have hSyl : IsSylowTwoOf S K := SzN22.isSylowTwoOf_inf_normalized hA.minPar.isSylow le_top hTK
  have hTM : T ≤ M := hA.minPar.le
  have hCM : cenZ K S = M ⊓ K := hMK.symm
  have hsup : K ⊔ T = ⊤ := hA.sup
  have hTS : ∀ t ∈ T, t ∈ Subgroup.normalizer (S : Set X) := fun t ht =>
    mem_norm_inf' (hTT ht) (hKnorm t)
  have hTz : ∀ t ∈ T, t ∈ Subgroup.normalizer ((E2P.zOf S : Subgroup X) : Set X) := fun t ht =>
    mem_norm_inf' (hTS t ht) (mem_norm_centralizer' (hTS t ht))
  by_cases hVK : V ≤ K
  · have hVS : V ≤ S := fun v hv => ⟨hVT hv, hVK hv⟩
    have hSV : S ≤ Subgroup.normalizer (V : Set X) := fun s hs => hTV hs.1
    have hVz : V ≤ E2P.zOf S := f1_holds X K S 5 hpp hp2 hL hSyl V hV hVS hSV
    refine hVz.trans ?_
    have hzS : E2P.zOf S ≤ S := inf_le_left
    have hz2 : IsPGroup 2 ↥(E2P.zOf S) :=
      hSyl.2.1.of_injective (Subgroup.inclusion hzS) (Subgroup.inclusion_injective hzS)
    have hnorm : M ≤ Subgroup.normalizer ((E2P.zOf S : Subgroup X) : Set X) := by
      intro m hm
      obtain ⟨k, hk, t, ht, rfl⟩ := exists_mul_mem_of_sup_eq_top hsup m
      have hkM : k ∈ M := by
        have := M.mul_mem hm (M.inv_mem (hTM ht))
        simpa using this
      have hkC : k ∈ cenZ K S := by rw [hCM]; exact ⟨hkM, hk⟩
      exact (Subgroup.normalizer _).mul_mem
        (Subgroup.centralizer_le_normalizer _ hkC.2) (hTz t ht)
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (hzS.trans (inf_le_left.trans hTM)) hnorm hz2
  · exfalso
    obtain ⟨u, hu, huK⟩ := IsConcreteLE.not_le_iff_exists.mp hVK
    have huu : u * u = 1 := by
      have := hV.2 u hu
      simpa [pow_two] using this
    have hS16 := card_sylow_five hK hSyl
    have hCcard := (model_five hK hSyl).1
    have hne : T ≠ M := by
      intro h
      have hC : cenZ K S = S := by rw [hCM, ← h]
      rw [hC, hS16] at hCcard
      omega
    obtain ⟨A, hTA, hAM, hAmin⟩ := exists_cover hTM hne
    obtain ⟨W, hW, hVW, hAW⟩ : ∃ W : Subgroup X, IsElemAbelian 2 W ∧ V ≤ W ∧
        A ≤ Subgroup.normalizer (W : Set X) := by
      by_cases hAn : A ≤ Subgroup.normalizer (V : Set X)
      · exact ⟨V, hV, le_rfl, hAn⟩
      · exact ⟨conjClosure V A, hAt A hTA.le hAM hAn hAmin, le_conjClosure V A,
          le_normalizer_conjClosure V A⟩
    have hcomm := comm_mem_zOf hKn hSdef hSyl hL hTA.le hW hVW hAW u hu
    have huC : ∀ c ∈ cenZ K S, u * c * u⁻¹ ∈ cenZ K S := by
      intro c hc
      rw [hCM] at hc ⊢
      exact ⟨M.mul_mem (M.mul_mem (hTM (hVT hu)) hc.1) (M.inv_mem (hTM (hVT hu))),
        hKn.conj_mem c hc.2 u⟩
    have hPC : A ⊓ K ≤ cenZ K S := fun x hx => by
      rw [hCM]; exact ⟨hAM hx.1, hx.2⟩
    have hSP : S ≤ A ⊓ K := fun x hx => ⟨hTA.le hx.1, hx.2⟩
    have hSP' : S ≠ A ⊓ K := by
      intro h
      apply hTA.not_ge
      intro a ha
      obtain ⟨k, hk, t, ht, rfl⟩ := exists_mul_mem_of_sup_eq_top hsup a
      have hkA : k ∈ A := by
        have := A.mul_mem ha (A.inv_mem (hTA.le ht))
        simpa using this
      have hkS : k ∈ S := by rw [h]; exact ⟨hkA, hk⟩
      exact T.mul_mem hkS.1 ht
    exact outer_case hK hKn hA.cent hSyl huu huK huC hS16 hPC hSP hSP'
      (fun x hx => hcomm x hx)

end CFSG.Quasithin.Background.Harris.KFact2d
