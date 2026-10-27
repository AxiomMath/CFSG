module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4YAmalgam
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Simple
public import CFSG.Quasithin.EmptyFaithful.S1421Inputs

public section

namespace CFSG.Quasithin.Background.Harris.R1.D4Vert

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.Quasithin CFSG.Quasithin.D4Hex
  CFSG.LargeExtraspecial.S63 CFSG.QuasithinUnique

theorem exists_lieModel_d4 :
    ∃ (X : Type) (_ : Group X), LieModel X .trialityD4 0 2 1 := by
  refine ⟨DerivedCentralQuotient
    (twistedFixedGroup .D4 (GaloisField 2 3) (frobenius (GaloisField 2 3) 2)), inferInstance, ?_⟩
  refine Or.inr (Or.inl ⟨rfl, by decide, ⟨⟨Nat.prime_two, le_rfl, rfl⟩, ?_⟩⟩)
  refine ⟨GaloisField 2 3, inferInstance, inferInstance, ?_, frobenius (GaloisField 2 3) 2, ?_,
    ⟨MulEquiv.refl _⟩⟩
  · rw [GaloisField.card 2 3 (by norm_num)]
    rfl
  · intro c
    exact frobenius_def 2 c

theorem isLieOverTwo_D :
    IsLieOverTwo .trialityD4 0 1 D := by
  obtain ⟨X, _, hX⟩ := exists_lieModel_d4
  obtain ⟨f⟩ := CFSG.Quasithin.trialityD4ModelBridge_of_lieModel X hX
  obtain ⟨g⟩ := nonempty_quasithinTrialityD4Two_equiv
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (f.trans g) hX


section Iso

variable {G : Type} [Group G] [Finite G] {K1 L2 S : Subgroup G}

noncomputable def amalgamIsoOfVertices (hR : Hyp111R K1 L2 S)
    (hKB : K1 ⊔ bigB K1 L2 S = K1) (e : ↥K1 ≃* ↥d4H)
    (heB : ∀ k : ↥K1, (k : G) ∈ bigB K1 L2 S ↔ (e k : D) ∈ d4B)
    (ψ : ↥(L2 ⊔ bigB K1 L2 S) ≃* ↥d4N)
    (hψ : ∀ (b : G) (hb : b ∈ bigB K1 L2 S) (hbK : b ∈ K1),
      (ψ ⟨b, Subgroup.mem_sup_right hb⟩ : D) = (e ⟨b, hbK⟩ : D)) :
    (RankTwoAmalgam.ofSubgroups (K1 ⊔ bigB K1 L2 S) (L2 ⊔ bigB K1 L2 S)).Iso
      (RankTwoAmalgam.ofSubgroups d4H d4N) :=
  have hP : (K1 ⊔ bigB K1 L2 S) ⊓ (L2 ⊔ bigB K1 L2 S) = bigB K1 L2 S :=
    F1.parabolic_inf_parabolic hR
  have hK : ∀ {p : G}, p ∈ K1 ⊔ bigB K1 L2 S → p ∈ K1 := fun hp => hKB ▸ hp
  let f : ↥((K1 ⊔ bigB K1 L2 S) ⊓ (L2 ⊔ bigB K1 L2 S)) →* ↥(d4H ⊓ d4N) :=
    { toFun := fun p => ⟨(e ⟨p, hK p.2.1⟩ : D), (e _).2, by
        have hpB : (p : G) ∈ bigB K1 L2 S := hP.le p.2
        exact ((heB ⟨p, hK p.2.1⟩).mp hpB).2⟩
      map_one' := by
        apply Subtype.ext
        show (e 1 : D) = 1
        rw [map_one]; rfl
      map_mul' := fun p q => by
        have h := congrArg (fun x : ↥d4H => (x : D)) (map_mul e ⟨(p : G), hK p.2.1⟩ ⟨(q : G), hK q.2.1⟩)
        exact Subtype.ext h }
  have hf : Function.Bijective f := by
    constructor
    · intro p q h
      have h1 : ((f p : ↥(d4H ⊓ d4N)) : D) = (f q : D) := congrArg Subtype.val h
      change (e ⟨p, hK p.2.1⟩ : D) = (e ⟨q, hK q.2.1⟩ : D) at h1
      have h2 := e.injective (Subtype.ext h1)
      exact Subtype.ext (congrArg (fun x : ↥K1 => (x : G)) h2)
    · rintro ⟨d, hdH, hdN⟩
      set k : ↥K1 := e.symm ⟨d, hdH⟩ with hk
      have hek : (e k : D) = d := by rw [hk, MulEquiv.apply_symm_apply]
      have hkB : (k : G) ∈ bigB K1 L2 S := (heB k).mpr (by rw [hek]; exact ⟨hdH, hdN⟩)
      have hkP : (k : G) ∈ (K1 ⊔ bigB K1 L2 S) ⊓ (L2 ⊔ bigB K1 L2 S) := hP.ge hkB
      refine ⟨⟨k, hkP⟩, Subtype.ext ?_⟩
      show (e ⟨(k : G), _⟩ : D) = d
      rw [← hek]
  { φ1 := (MulEquiv.subgroupCongr hKB).trans e
    φ12 := MulEquiv.ofBijective f hf
    φ2 := ψ
    comm1 := fun g => Subtype.ext rfl
    comm2 := fun (g : ↥((K1 ⊔ bigB K1 L2 S) ⊓ (L2 ⊔ bigB K1 L2 S))) => by
      apply Subtype.ext
      have hgB : (g : G) ∈ bigB K1 L2 S := hP.le g.2
      show (e ⟨g, hK g.2.1⟩ : D) = (ψ ⟨g, g.2.2⟩ : D)
      rw [hψ g hgB (hK g.2.1)] }

end Iso

section Survivor


variable {G : Type} [Group G] [Finite G] {K1 L2 S : Subgroup G}

theorem survivor4_of_isos (hR : Hyp111R K1 L2 S) (hKB : K1 ⊔ bigB K1 L2 S = K1)
    (e : ↥K1 ≃* ↥d4H) (heB : ∀ k : ↥K1, (k : G) ∈ bigB K1 L2 S ↔ (e k : D) ∈ d4B)
    (ψ : ↥(L2 ⊔ bigB K1 L2 S) ≃* ↥d4N)
    (hψ : ∀ (b : G) (hb : b ∈ bigB K1 L2 S) (hbK : b ∈ K1),
      (ψ ⟨b, Subgroup.mem_sup_right hb⟩ : D) = (e ⟨b, hbK⟩ : D))
    (hL28 : IsL2Quot 3 (OTwoQuot K1)) (hsp : IsSpecialPow 2 2 4 ↥(pCoreOf 2 K1))
    (hL2 : IsL2Quot 1 (OTwoQuot L2)) (hO : Nat.card (pCoreOf 2 L2) = 2 ^ 11) :
    Survivor4LegacyBare K1 L2 S :=
  ⟨⟨D, inferInstance, isLieOverTwo_D, d4U, d4H, d4N,
    d4_isYAmalgamPair (d4_isSimpleGroup isLieOverTwo_D),
    ⟨amalgamIsoOfVertices hR hKB e heB ψ hψ⟩⟩, hL28, hsp, hL2, hO⟩

end Survivor

end CFSG.Quasithin.Background.Harris.R1.D4Vert
