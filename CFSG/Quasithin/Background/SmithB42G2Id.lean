module

public import CFSG.Quasithin.Background.SmithB42G2IdRoots
public import CFSG.Quasithin.Background.SmithB42G2IdRank
public import CFSG.Timmesfeld.RankTwo.ModelG2Rank
public import CFSG.Timmesfeld.RankTwo.Presentation
public import CFSG.Quasithin.EmptyFaithful.A38c4G2Center
public import CFSG.Quasithin.Background.P3G2Zorn
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate120

public section

namespace CFSG.Quasithin.B42G2Id

open CFSG.Open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Timmesfeld CFSG.Timmesfeld.RankTwo CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Frame

variable {F : Type} [Field F] [CharP F 2]

theorem zPsi_rels : ∀ w ∈ GradedPresentation.rels (g2Cm (K := F)),
    FreeGroup.lift (fun g : Σ _ : Fin 6, F => zPsi (hexRoot g.1) g.2) w = 1 := by
  have hfun : (fun g : Σ _ : Fin 6, F => zPsi (hexRoot g.1) g.2) = fun g => zPos g.1 g.2 :=
    funext fun g => zPsi_pos g.1 g.2
  rw [hfun]
  exact zPos_rels

theorem zPsi_weyl : ∀ i γ, IsRoot .G2 γ → ∀ c : F, zW F i * zPsi γ c * (zW F i)⁻¹ =
    zPsi ((RootSystem.ofCartan (g2Datum F).isFiniteType (g2Datum F).divisible).refl i γ) c :=
  fun i _ hγ c => zW_conj_zPsi i hγ c

theorem single_zero_eq_hexRoot : (Pi.single (0 : Fin 2) 1 : Fin 2 → ℤ) = hexRoot 5 := by
  funext k
  fin_cases k <;> decide

theorem single_one_eq_hexRoot : (Pi.single (1 : Fin 2) 1 : Fin 2 → ℤ) = hexRoot 0 := by
  funext k
  fin_cases k <;> decide

theorem zPsi_rankOne : ∀ i : Fin 2,
    ExtendsToHom (g2Datum F).rootGroup {Pi.single i 1, -Pi.single i 1} (g2PhiOf (zPsi (F := F)))
  | 0 => g2_extendsToHom_rankOne zPsi (0 : Fin 2) g2Long
      (fun c => (g2Long_sl2Upper c).trans ((zPsi_pos 5 c).symm.trans
        (congrArg (fun γ => zPsi γ c) single_zero_eq_hexRoot.symm)))
      (fun c => (g2Long_sl2Lower c).trans ((zPsi_neg 5 c).symm.trans
        (congrArg (fun γ => zPsi (-γ) c) single_zero_eq_hexRoot.symm)))
  | 1 => g2_extendsToHom_rankOne zPsi (1 : Fin 2) g2Short
      (fun c => (g2Short_sl2Upper c).trans ((zPsi_pos 0 c).symm.trans
        (congrArg (fun γ => zPsi γ c) single_one_eq_hexRoot.symm)))
      (fun c => (g2Short_sl2Lower c).trans ((zPsi_neg 0 c).symm.trans
        (congrArg (fun γ => zPsi (-γ) c) single_one_eq_hexRoot.symm)))

theorem zPsi_gen :
    Subgroup.closure (⋃ γ ∈ (g2Datum F).roots, Set.range (g2PhiOf (zPsi (F := F)) γ)) = ⊤ := by
  refine (congrArg Subgroup.closure (iUnion_range_g2PhiOf (zPsi (F := F)))).trans ?_
  set H := Subgroup.closure (⋃ γ ∈ (g2Datum F).roots, Set.range (zPsi (F := F) γ)) with hH
  have hmem : ∀ γ, IsRoot .G2 γ → ∀ t, zPsi γ t ∈ H := fun γ hγ t =>
    Subgroup.subset_closure (Set.mem_iUnion₂.2 ⟨γ, mem_adjDatum_roots.2 hγ, t, rfl⟩)
  have hpos : ∀ j t, zPos j t ∈ H := fun j t => by
    rw [← zPsi_pos]
    exact hmem _ (isRoot_hexRoot j) t
  have hneg : ∀ j t, zNeg j t ∈ H := fun j t => by
    rw [← zPsi_neg]
    exact hmem _ (CFSG.LieType.Chevalley.IsRoot.neg (isRoot_hexRoot j)) t
  rw [eq_top_iff, ← genE12_eq_top, genE12, Subgroup.closure_le]
  rintro g (⟨t, rfl | rfl⟩ | ⟨g', ⟨t, rfl | rfl⟩, rfl⟩)
  · exact hpos 4 t
  · exact hneg 4 t
  · change g2A swap12 * g2X ![0, t, 0] * (g2A swap12)⁻¹ ∈ H
    rw [conj_swap12_x1]
    exact hneg 2 t
  · change g2A swap12 * g2Y ![0, t, 0] * (g2A swap12)⁻¹ ∈ H
    rw [conj_swap12_y1]
    exact hpos 2 t

theorem zPsi_nontrivial : ∃ γ ∈ (g2Datum F).roots, ∃ x, g2PhiOf (zPsi (F := F)) γ x ≠ 1 := by
  refine ⟨hexRoot 0, mem_adjDatum_roots.2 (isRoot_hexRoot 0),
    ⟨xPar (rootOperatorFamily .G2) (hexRoot 0) 1, xPar_mem (isRoot_hexRoot 0) 1⟩, ?_⟩
  rw [g2PhiOf_xPar zPsi (isRoot_hexRoot 0) 1, zPsi_pos]
  intro h
  have h1 := congrArg (fun g : ↥(cayleyGroup F) => g2Act g (q6 0 0 0 1 0 0)) h
  simp only [zPos, g2Act_x0q, map_one, AddMonoid.End.coe_one, id_eq] at h1
  have h2 := congrFun h1 (.inl 0)
  simp [q6] at h2

theorem zPsi_coneCompatible [Finite F] :
    ConeCompatible (RootSystem.ofCartan (g2Datum F).isFiniteType (g2Datum F).divisible)
      (g2Datum F).rootGroup (g2PhiOf (zPsi (F := F))) :=
  g2_coneCompatible_of zPsi zPsi_rels (zW F) zPsi_weyl zPsi_rankOne

theorem exists_surjective_adjointGroup_hom_cayleyGroup [Finite F] :
    ∃ ψ : ↥(adjointGroup .G2 F) →* ↥(cayleyGroup F),
      (∀ γ, IsRoot .G2 γ → ∀ c, ψ (xPar (rootOperatorFamily .G2) γ c) = zPsi γ c) ∧
      Function.Surjective ψ := by
  obtain ⟨ψ, hψ, -⟩ := existsUnique_hom_of_coneCompatible (presentationA_G2 F)
    (zPsi_coneCompatible (F := F))
  refine ⟨ψ, fun γ hγ c => (hψ γ (mem_adjDatum_roots.2 hγ) ⟨_, xPar_mem hγ c⟩).trans
    (g2PhiOf_xPar zPsi hγ c), ?_⟩
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← zPsi_gen, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_iUnion, Set.mem_range] at hg
  obtain ⟨γ, hγ, x, rfl⟩ := hg
  exact ⟨x, hψ γ hγ x⟩

end Frame

section Iso

theorem exists_ne_zero_ne_one_of_three_le {K : Type} [Field K] (hK : 3 ≤ Nat.card K) :
    ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
  by_contra! h
  have hs : Function.Surjective fun b : Bool => if b then (1 : K) else 0 := fun t => by
    by_cases ht : t = 0
    · exact ⟨false, by simp [ht]⟩
    · exact ⟨true, by simp [h t ht]⟩
  have := Nat.card_le_card_of_surjective _ hs
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
  omega

theorem charP_two_of_card {K : Type} [Field K] [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    CharP K 2 := by
  have := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hK)

theorem three_le_two_pow {f : ℕ} (hf : 2 ≤ f) : 3 ≤ 2 ^ f :=
  le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)

theorem exists_adjointGroup_hom_cayleyGroup {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) :
    ∃ ψ : ↥(adjointGroup .G2 K) →* ↥(cayleyGroup K),
      (∀ γ, IsRoot .G2 γ → ∀ c, ψ (xPar (rootOperatorFamily .G2) γ c) = zPsi γ c) ∧
      Function.Surjective ψ ∧ ψ.ker = Subgroup.center ↥(adjointGroup .G2 K) := by
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_ne_one_of_three_le (K := K) (hK ▸ three_le_two_pow hf)
  obtain ⟨ψ, hψ, hsurj, hker, -⟩ := exists_lieModel_of_coneCompatible_G2 Nat.prime_two
    (by omega) (three_le_two_pow hf) hK (A318Excl.center_cayleyGroup_eq_bot hc0 hc1)
    zPsi_coneCompatible zPsi_gen zPsi_nontrivial
  refine ⟨ψ, fun γ hγ c => ?_, hsurj, hker⟩
  exact (hψ γ (mem_adjDatum_roots.2 hγ) ⟨_, xPar_mem hγ c⟩).trans (g2PhiOf_xPar zPsi hγ c)

theorem nonempty_cayleyGroup_mulEquiv_adjointQuotient {K : Type} [Field K] [Finite K]
    [CharP K 2] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) :
    Nonempty (↥(cayleyGroup K) ≃* AdjointQuotient .G2 K) := by
  obtain ⟨ψ, -, hsurj, hker⟩ := exists_adjointGroup_hom_cayleyGroup hK hf
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj)).symm⟩

theorem exists_adjointQuotient_mulEquiv_cayleyGroup {K : Type} [Field K] [Finite K] [CharP K 2]
    {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) :
    ∃ e : AdjointQuotient .G2 K ≃* ↥(cayleyGroup K), ∀ γ, IsRoot .G2 γ → ∀ c,
      e (QuotientGroup.mk (xPar (rootOperatorFamily .G2) γ c)) = zPsi γ c := by
  obtain ⟨ψ, hψ, hsurj, hker⟩ := exists_adjointGroup_hom_cayleyGroup hK hf
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj), fun γ hγ c => hψ γ hγ c⟩

theorem nonempty_quasithinG2_mulEquiv_adjointQuotient {K : Type} [Field K] [Finite K]
    [CharP K 2] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) :
    Nonempty (↥(quasithinG2 K) ≃* AdjointQuotient .G2 K) := by
  obtain ⟨e⟩ := nonempty_cayleyGroup_mulEquiv_adjointQuotient hK hf
  exact ⟨(MulEquiv.subgroupCongr G11.P3G2.quasithinG2_eq_cayleyGroup).trans e⟩

theorem chevalleyExceptionalModel_cayleyGroup {K : Type} [Field K] [Finite K] [CharP K 2]
    {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) :
    ChevalleyExceptionalModel (↥(cayleyGroup K)) .G2 2 f := by
  obtain ⟨e⟩ := nonempty_cayleyGroup_mulEquiv_adjointQuotient hK hf
  exact ⟨⟨Nat.prime_two, by omega, rfl, three_le_two_pow hf⟩, K, inferInstance, inferInstance, hK,
    ⟨e⟩⟩

theorem exists_cayleyGroup_of_chevalleyExceptionalModel {X : Type} [Group X] {f : ℕ}
    (h : ChevalleyExceptionalModel X .G2 2 f) :
    2 ≤ f ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ f ∧
      Nonempty (X ≃* ↥(cayleyGroup K)) := by
  obtain ⟨⟨-, hf1, -, hq⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hf : 2 ≤ f := by
    by_contra hlt
    have h1 : f = 1 := by omega
    rw [h1] at hq
    norm_num at hq
  have := charP_two_of_card hK
  obtain ⟨e'⟩ := nonempty_cayleyGroup_mulEquiv_adjointQuotient hK hf
  exact ⟨hf, K, inferInstance, inferInstance, inferInstance, hK, ⟨e.trans e'.symm⟩⟩

theorem exists_quasithinG2_of_chevalleyExceptionalModel {X : Type} [Group X] {f : ℕ}
    (h : ChevalleyExceptionalModel X .G2 2 f) :
    2 ≤ f ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ f ∧
      Nonempty (X ≃* ↥(quasithinG2 K)) := by
  obtain ⟨hf, K, _, _, _, hK, ⟨e⟩⟩ := exists_cayleyGroup_of_chevalleyExceptionalModel h
  exact ⟨hf, K, inferInstance, inferInstance, inferInstance, hK,
    ⟨e.trans (MulEquiv.subgroupCongr G11.P3G2.quasithinG2_eq_cayleyGroup.symm)⟩⟩

theorem exists_cayleyGroup_of_model_center_eq_bot {L : Type} [Group L] {f : ℕ}
    (hZ : Subgroup.center L = ⊥) (h : ChevalleyExceptionalModel (L ⧸ Subgroup.center L) .G2 2 f) :
    2 ≤ f ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ f ∧
      Nonempty (L ≃* ↥(cayleyGroup K)) := by
  obtain ⟨hf, K, _, _, _, hK, ⟨e⟩⟩ := exists_cayleyGroup_of_chevalleyExceptionalModel h
  exact ⟨hf, K, inferInstance, inferInstance, inferInstance, hK,
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e⟩⟩

end Iso

end CFSG.Quasithin.B42G2Id
