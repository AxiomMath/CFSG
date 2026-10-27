module

public import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
public import CFSG.RankThree.LocalRank.ThetaPlaneAlpha
import CFSG.RankThree.LocalRank.ThetaPlaneExactQuotients
import CFSG.RankThree.LocalRank.ThetaCoreQuotients
import CFSG.RankThree.LocalRank.PrimeComplementCentralizesNormal
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.RankThree.Coprime.PlaneCoreCentralizesComponent
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAReciprocalFusion

public section

namespace CFSG.RankThree

open CFSG CFSG.RankThree.LocalRank

section Layer

variable {X : Type*} [Group X]

theorem le_centralizer_layer_iff {V : Subgroup X} :
    V ≤ Subgroup.centralizer (layer X : Set X) ↔
      ∀ K : Subgroup X, IsComponent K → V ≤ Subgroup.centralizer (K : Set X) := by
  rw [Subgroup.le_centralizer_iff, layer, sSup_le_iff]
  exact forall_congr' fun K => imp_congr_right fun _ => Subgroup.le_centralizer_iff

theorem iInf_normalizer_components_normal :
    (⨅ (K : Subgroup X) (_ : IsComponent K), Subgroup.normalizer (K : Set X)).Normal := by
  refine ⟨fun w hw g => ?_⟩
  simp only [Subgroup.mem_iInf] at hw ⊢
  intro K hK
  have hK' : IsComponent (K.map (MulAut.conj g⁻¹).toMonoidHom) :=
    LocalCores.isComponent_map_mulEquiv _ hK
  have hw' := Subgroup.mem_normalizer_iff.mp (hw _ hK')
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have key : ∀ y : X, y ∈ K.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * y * g⁻¹ ∈ K := fun y => by
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
  rw [show h ∈ K ↔ g⁻¹ * h * g⁻¹⁻¹ ∈ K.map (MulAut.conj g⁻¹).toMonoidHom by
      rw [key]; group, hw', key]
  constructor <;> intro hmem <;> convert hmem using 1 <;> group

theorem commutator_le_normalizer_of_components {H B : Subgroup X}
    (hB : ∀ K : Subgroup X, IsComponent K → B ≤ Subgroup.normalizer (K : Set X))
    {K : Subgroup X} (hK : IsComponent K) : ⁅H, B⁆ ≤ Subgroup.normalizer (K : Set X) := by
  have := iInf_normalizer_components_normal (X := X)
  have hBW : B ≤ ⨅ (K : Subgroup X) (_ : IsComponent K), Subgroup.normalizer (K : Set X) :=
    le_iInf₂ hB
  exact (Subgroup.commutator_mono le_rfl hBW).trans
    ((Subgroup.commutator_le_right _ _).trans (iInf₂_le K hK))

end Layer

section CoreFree

variable {X : Type*} [Group X] [Finite X] {p : ℕ}

theorem fittingSubgroup_le_pCore_of_aschbacherSolvableCore_eq_bot (hp : p.Prime)
    (hθ : aschbacherSolvableCore p X = ⊥) : fittingSubgroup X ≤ pCore p X := by
  rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
  refine iSup_le fun r => ?_
  by_cases hr : (r : ℕ) = p
  · rw [hr]
  · exact ((solvable_prime_complement_core_characterization hp).2.2.2.2.2.2 r
      (Nat.prime_of_mem_primeFactors r.2) hr).trans (hθ ▸ bot_le)

theorem eq_bot_of_le_thetaCore_of_le_centralizer_layer (hp : p.Prime)
    (hθ : aschbacherSolvableCore p X = ⊥) {b : X} (hb : b ^ p = 1) {V : Subgroup X}
    (hV : V ≤ inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({b} : Set X)))
    (hVE : V ≤ Subgroup.centralizer (layer X : Set X)) : V = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer ({b} : Set X)
  set R := inSubgroup (aschbacherSolvableCore p) C
  have hRC : R ≤ C := Subgroup.map_subtype_le _
  have hRsub : R.subgroupOf C = aschbacherSolvableCore p C :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  have hRn : (R.subgroupOf C).Normal := by
    rw [hRsub]
    infer_instance
  have hRp : ¬ p ∣ Nat.card R := by
    rw [show Nat.card R = Nat.card (aschbacherSolvableCore p C) from
      Subgroup.card_map_of_injective C.subtype_injective]
    exact (solvable_prime_complement_core_characterization hp).2.2.1
  have hbp : IsPGroup p (Subgroup.zpowers b) := by
    by_cases h : b = 1
    · rw [h, Subgroup.zpowers_one_eq_bot]
      exact IsPGroup.of_bot
    · exact IsPGroup.of_card (n := 1)
        (by rw [Nat.card_zpowers, pow_one]; exact orderOf_eq_prime hb h)
  have hzc : Subgroup.centralizer ((Subgroup.zpowers b : Subgroup X) : Set X) = C := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hRP : ⁅R, pCore p X⁆ = ⊥ :=
    RankThree.LocalRank.local_prime_complement_centralizes_normal_prime_group hp
      (P := pCore p X) (A := Subgroup.zpowers b) (S := R) pCore_isPGroup hbp
      (by rw [hzc]; exact hRC) (by rw [hzc]; exact hRn) hRp
  have hVF : V ≤ Subgroup.centralizer (fittingSubgroup X : Set X) :=
    hV.trans ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hRP).trans
      (Subgroup.centralizer_le (fittingSubgroup_le_pCore_of_aschbacherSolvableCore_eq_bot hp hθ)))
  have hVstar : V ≤ Subgroup.centralizer (generalizedFitting X : Set X) := by
    rw [Subgroup.le_centralizer_iff, generalizedFitting, sup_le_iff]
    exact ⟨Subgroup.le_centralizer_iff.mp hVF, Subgroup.le_centralizer_iff.mp hVE⟩
  set Cs := Subgroup.centralizer (generalizedFitting X : Set X)
  have hCsle : Cs ≤ generalizedFitting X := centralizer_generalizedFitting_le X
  have hchar := (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).1
  have hCsn : Cs.Normal := Subgroup.normal_centralizer
  have hCscomm : IsMulCommutative Cs := ⟨⟨fun x y => Subtype.ext
    (Subgroup.mem_centralizer_iff.mp x.2 y (hCsle y.2)).symm⟩⟩
  have hCsF : Cs ≤ fittingSubgroup X :=
    CFSG.LocalCores.fitting_characteristic.2.2 Cs hCsn inferInstance
  have hVP : V ≤ pCore p X :=
    hVstar.trans (hCsF.trans (fittingSubgroup_le_pCore_of_aschbacherSolvableCore_eq_bot hp hθ))
  have hVp : IsPGroup p V := pCore_isPGroup.to_le hVP
  rcases hVp.card_eq_or_dvd with h1 | hdvd
  · exact Subgroup.card_eq_one.mp h1
  · exact absurd (hdvd.trans (Subgroup.card_dvd_of_le hV)) hRp

end CoreFree

theorem central_line_setup {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {A : Subgroup G} (hA : IsElementaryAbelian p A)
    (hAcard : Nat.card A = p ^ 3) (Z : Subgroup G) [Z.Normal]
    (hZc : Z ≤ Subgroup.center G) (hZp : Nat.card Z = p)
    (hnorm : ∀ L ∈ thetaComponents p G, A ≤ Subgroup.normalizer (L : Set G))
    (hα : ¬ thetaAlpha p (A.map (QuotientGroup.mk' Z)) ≤ aschbacherSolvableCore p (G ⧸ Z))
    (B : Subgroup G) (hBA : B ≤ A) (hBZ : Disjoint B Z) (hBZA : B ⊔ Z = A) :
    IsPGroup p A ∧
    CFSG.Assembly.IsElemAbelian p (B.map (QuotientGroup.mk' (aschbacherSolvableCore p G))) ∧
    IsElementaryAbelian p (B.map (QuotientGroup.mk' (aschbacherSolvableCore p G))) ∧
    Nat.card (B.map (QuotientGroup.mk' (aschbacherSolvableCore p G))) = p ^ 2 ∧
    (thetaAlpha p B).map (QuotientGroup.mk' (aschbacherSolvableCore p G)) =
      thetaAlpha p (B.map (QuotientGroup.mk' (aschbacherSolvableCore p G))) ∧
    (thetaAlpha p B).map (QuotientGroup.mk' (aschbacherSolvableCore p G)) ≠ ⊥ ∧
    aschbacherSolvableCore p (G ⧸ aschbacherSolvableCore p G) = ⊥ ∧
    ∀ K : Subgroup (G ⧸ aschbacherSolvableCore p G), IsComponent K →
      A.map (QuotientGroup.mk' (aschbacherSolvableCore p G)) ≤
        Subgroup.normalizer (K : Set (G ⧸ aschbacherSolvableCore p G)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hA : CFSG.Assembly.IsElemAbelian p A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A).mp hA
  set N := aschbacherSolvableCore p G with hNdef
  set ρ := QuotientGroup.mk' N with hρdef
  obtain ⟨hNsol, -, hNp, -⟩ := solvable_prime_complement_core_characterization (H := G) hp
  have hApg : IsPGroup p A := fun x => ⟨1, Subtype.ext (by simpa using hA.2 x x.2)⟩
  have hZpg : IsPGroup p Z := IsPGroup.of_card (n := 1) (by rw [hZp, pow_one])
  have hBel : CFSG.Assembly.IsElemAbelian p B :=
    ⟨⟨⟨fun x y => Subtype.ext (show (x : G) * y = y * x from congrArg (Subtype.val : A → G)
      (hA.1.is_comm.comm (⟨x, hBA x.2⟩ : A) ⟨y, hBA y.2⟩))⟩⟩, fun x hx => hA.2 x (hBA hx)⟩
  have hBcard : Nat.card B = p ^ 2 := by
    have h := CFSG.ComponentClassification.UnbalancedGS.ReciprocalFusion.card_sup_eq_mul_of_disjoint
      B Z (hZc.trans ((Subgroup.center_le_centralizer _).trans
        (Subgroup.centralizer_le_normalizer _))) hBZ
    rw [hBZA, hAcard, hZp] at h
    exact Nat.eq_of_mul_eq_mul_right hp.pos (by rw [← h]; ring)
  have hBmap : B.map (QuotientGroup.mk' Z) = A.map (QuotientGroup.mk' Z) := by
    rw [← hBZA, Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
  have hZB : Z ⊓ B = ⊥ := disjoint_iff.mp hBZ.symm
  have hαN : ¬ thetaAlpha p B ≤ N := by
    intro h
    obtain ⟨-, -, -, -, hc⟩ := theta_plane_alpha_exact_prime_kernel_quotients hp B hBel hBcard Z
      (Or.inr ⟨hZc, hZpg, hZB⟩)
    exact hα (hBmap ▸ (hc hZc hZpg hZB).mp h)
  obtain ⟨hBbarcard, -, -, hQmap, -⟩ :=
    theta_plane_alpha_exact_prime_kernel_quotients hp B hBel hBcard N (Or.inl ⟨hNsol, hNp⟩)
  set Bbar := B.map ρ with hBbardef
  set Q := (thetaAlpha p B).map ρ with hQdef
  have hQne : Q ≠ ⊥ := by
    intro h
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact hαN h
  have hθX : aschbacherSolvableCore p (G ⧸ N) = ⊥ :=
    (solvable_prime_complement_core_quotient_centralizers hp N hNsol hNp).2.2.1
  have hBbar : CFSG.Assembly.IsElemAbelian p Bbar := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp x.2
      obtain ⟨v, hv, hvy⟩ := Subgroup.mem_map.mp y.2
      apply Subtype.ext
      change (x : G ⧸ N) * y = y * x
      rw [← hux, ← hvy, ← map_mul, ← map_mul]
      exact congrArg ρ (congrArg Subtype.val (hBel.1.is_comm.comm (⟨u, hu⟩ : B) ⟨v, hv⟩))
    · obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
      rw [← map_pow, hBel.2 u hu, map_one]
  have hBbar' : IsElementaryAbelian p Bbar :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p Bbar).mpr hBbar
  obtain ⟨hbij, -, -⟩ := theta_component_quotient_correspondence (H := G) hp
  have hAK : ∀ K : Subgroup (G ⧸ N), IsComponent K → A.map ρ ≤ Subgroup.normalizer (K : Set _) := by
    intro K hK
    obtain ⟨L, hL, rfl⟩ := hbij.surjOn hK
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hAiff⟩ := theta_component_quotient_structure hp hL
    exact (hAiff A).mp (hnorm L hL)
  exact ⟨hApg, hBbar, hBbar', hBbarcard, hQmap, hQne, hθX, hAK⟩

theorem central_line_faithful_component_detection_of {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {A : Subgroup G} (hA : IsElementaryAbelian p A)
    (hAcard : Nat.card A = p ^ 3) (Z : Subgroup G) [Z.Normal] (hZA : Z ≤ A)
    (hZc : Z ≤ Subgroup.center G) (hZp : Nat.card Z = p)
    (hnorm : ∀ L ∈ thetaComponents p G, A ≤ Subgroup.normalizer (L : Set G))
    (hα : ¬ thetaAlpha p (A.map (QuotientGroup.mk' Z)) ≤ aschbacherSolvableCore p (G ⧸ Z))
    (B : Subgroup G) (hBA : B ≤ A) (hBZ : Disjoint B Z) (hBZA : B ⊔ Z = A)
    (hNF : ∀ E : Subgroup (G ⧸ aschbacherSolvableCore p G), IsElementaryAbelian p E →
      Nat.card E = p ^ 2 → ∀ t ∈ E, t ≠ 1 →
      ∀ K : Subgroup (G ⧸ aschbacherSolvableCore p G), IsComponent K →
      ⁅inSubgroup (aschbacherSolvableCore p)
          (Subgroup.centralizer ({t} : Set (G ⧸ aschbacherSolvableCore p G))), E⁆ ≤
        Subgroup.normalizer (K : Set (G ⧸ aschbacherSolvableCore p G)) →
      E ⊓ Subgroup.centralizer (K : Set (G ⧸ aschbacherSolvableCore p G)) ≠ ⊥ →
      ⁅⁅inSubgroup (aschbacherSolvableCore p)
          (Subgroup.centralizer ({t} : Set (G ⧸ aschbacherSolvableCore p G))), E⁆, K⁆ = ⊥ ∧
        ⁅thetaT p E, K⁆ = ⊥) :
    ∃ L ∈ thetaComponents p G, ∃ a : A →* MulAut (L ⧸ aschbacherSolvableCore p L),
      (∀ (x : A) (l l' : L), (l' : G) = x * l * (x : G)⁻¹ →
        a x (l : L ⧸ aschbacherSolvableCore p L) = (l' : L ⧸ aschbacherSolvableCore p L)) ∧
      (∀ x : A, a x = 1 ↔ (x : G) ∈ Z) ∧
      IsElementaryAbelian p a.range ∧ Nat.card a.range = p ^ 2 ∧
      ¬ (thetaAlpha p B).map (QuotientGroup.mk' (aschbacherSolvableCore p G)) ≤
        Subgroup.centralizer ((L.map (QuotientGroup.mk' (aschbacherSolvableCore p G)) :
          Subgroup (G ⧸ aschbacherSolvableCore p G)) : Set (G ⧸ aschbacherSolvableCore p G)) := by
  classical
  obtain ⟨hApg, hBbar, hBbar', hBbarcard, hQmap, hQne, hθX, hAK⟩ :=
    central_line_setup hp hA hAcard Z hZc hZp hnorm hα B hBA hBZ hBZA
  have hA : CFSG.Assembly.IsElemAbelian p A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A).mp hA
  obtain ⟨hbij, -, -⟩ := theta_component_quotient_correspondence (H := G) hp
  set N := aschbacherSolvableCore p G with hNdef
  set ρ := QuotientGroup.mk' N with hρdef
  set Bbar := B.map ρ with hBbardef
  set Q := (thetaAlpha p B).map ρ with hQdef
  have hBK : ∀ K : Subgroup (G ⧸ N), IsComponent K → Bbar ≤ Subgroup.normalizer (K : Set _) :=
    fun K hK => (Subgroup.map_mono hBA).trans (hAK K hK)
  have hVR : ∀ b ∈ Bbar, ⁅inSubgroup (aschbacherSolvableCore p)
      (Subgroup.centralizer ({b} : Set (G ⧸ N))), Bbar⁆ ≤
      inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({b} : Set (G ⧸ N))) := by
    intro b hb
    set C := Subgroup.centralizer ({b} : Set (G ⧸ N))
    have hRC : inSubgroup (aschbacherSolvableCore p) C ≤ C := Subgroup.map_subtype_le _
    have hRn : ((inSubgroup (aschbacherSolvableCore p) C).subgroupOf C).Normal := by
      rw [show (inSubgroup (aschbacherSolvableCore p) C).subgroupOf C =
        aschbacherSolvableCore p C from
        Subgroup.comap_map_eq_self_of_injective C.subtype_injective _]
      infer_instance
    have hBC : Bbar ≤ C := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hBbar.1.is_comm.comm (⟨x, hx⟩ : Bbar) ⟨b, hb⟩))
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hBC.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hRC).mp hRn))
  have hBne : Bbar ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hBbarcard
    have := Nat.one_lt_pow (by norm_num : 2 ≠ 0) hp.one_lt
    omega
  obtain ⟨⟨t, ht⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have hcent : ∀ K : Subgroup (G ⧸ N), IsComponent K →
      Bbar ⊓ Subgroup.centralizer (K : Set (G ⧸ N)) ≠ ⊥ →
      Q ≤ Subgroup.centralizer (K : Set (G ⧸ N)) := by
    intro K hK hCK
    rw [hQmap, thetaAlpha, sup_le_iff, thetaJ]
    refine ⟨iSup₂_le fun b hb => iSup_le fun hb1 => ?_, ?_⟩
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (hNF Bbar hBbar' hBbarcard b hb hb1 K hK (commutator_le_normalizer_of_components hBK hK)
          hCK).1
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (hNF Bbar hBbar' hBbarcard t ht ht1' K hK (commutator_le_normalizer_of_components hBK hK)
          hCK).2
  have hexists : ∃ K : Subgroup (G ⧸ N), IsComponent K ∧
      ¬ Q ≤ Subgroup.centralizer (K : Set (G ⧸ N)) := by
    by_contra hnone
    have hQE : Q ≤ Subgroup.centralizer (layer (G ⧸ N) : Set (G ⧸ N)) :=
      le_centralizer_layer_iff.mpr fun K hK => by_contra fun h => hnone ⟨K, hK, h⟩
    rw [hQmap, thetaAlpha, sup_le_iff] at hQE
    apply hQne
    rw [hQmap, thetaAlpha, thetaJ]
    have hJ : ∀ b ∈ Bbar, b ≠ 1 → ⁅inSubgroup (aschbacherSolvableCore p)
        (Subgroup.centralizer ({b} : Set (G ⧸ N))), Bbar⁆ = ⊥ := by
      intro b hb hb1
      refine eq_bot_of_le_thetaCore_of_le_centralizer_layer hp hθX (hBbar.2 b hb) (hVR b hb)
        (le_trans ?_ hQE.1)
      rw [thetaJ]
      exact le_iSup₂_of_le b hb (le_iSup_of_le hb1 le_rfl)
    have hT : thetaT p Bbar = ⊥ :=
      eq_bot_of_le_thetaCore_of_le_centralizer_layer hp hθX (hBbar.2 t ht)
        (iInf₂_le_of_le t ht (iInf_le _ ht1')) hQE.2
    rw [hT, sup_bot_eq, eq_bot_iff]
    exact iSup₂_le fun b hb => iSup_le fun hb1 => (hJ b hb hb1).le
  obtain ⟨K, hK, hQK⟩ := hexists
  have hCK : Bbar ⊓ Subgroup.centralizer (K : Set (G ⧸ N)) = ⊥ := by
    by_contra h
    exact hQK (hcent K hK h)
  have hinjA := injOn_mk_of_isPGroup hp hApg
  have hZK : ∀ x : A, ρ x ∈ Subgroup.centralizer (K : Set (G ⧸ N)) ↔ (x : G) ∈ Z := by
    intro x
    have hZcent : ∀ z ∈ Z, ρ z ∈ Subgroup.centralizer (K : Set (G ⧸ N)) := fun z hz =>
      Subgroup.center_le_centralizer _
        (Subgroup.map_center_le_center (QuotientGroup.mk'_surjective N)
          (Subgroup.mem_map_of_mem ρ (hZc hz)))
    constructor
    · intro hx
      have hxBZ : (x : G) ∈ B ⊔ Z := by rw [hBZA]; exact x.2
      obtain ⟨b, hb, z, hz, hbz⟩ := Subgroup.mem_sup_of_normal_right.mp hxBZ
      have hρb : ρ b ∈ Bbar ⊓ Subgroup.centralizer (K : Set (G ⧸ N)) := by
        refine ⟨Subgroup.mem_map_of_mem ρ hb, ?_⟩
        have h := Subgroup.mul_mem _ hx (Subgroup.inv_mem _ (hZcent z hz))
        rwa [← hbz, map_mul, mul_inv_cancel_right] at h
      rw [hCK, Subgroup.mem_bot] at hρb
      have hb1 : b = 1 := hinjA (hBA hb) A.one_mem (by rw [hρb, map_one])
      rw [← hbz, hb1, one_mul]
      exact hz
    · exact hZcent x
  obtain ⟨L, hL, hLK⟩ := hbij.surjOn hK
  have hLK : L.map ρ = K := hLK
  obtain ⟨-, a, -, -, ha, -, -, hkerC, -, -⟩ := theta_component_quotient_action hp hL A (hnorm L hL)
  have hker : ∀ x : A, a x = 1 ↔ (x : G) ∈ Z := fun x => by
    rw [hkerC x]
    change ρ x ∈ _ ↔ _
    rw [hLK]
    exact hZK x
  refine ⟨L, hL, a, ha, hker, (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p
    a.range).mpr ⟨⟨⟨fun u v => ?_⟩⟩, fun y hy => ?_⟩, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := u.2
    obtain ⟨y, hy⟩ := v.2
    apply Subtype.ext
    change (u : MulAut (L ⧸ aschbacherSolvableCore p L)) * v = v * u
    rw [← hx, ← hy, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (congrArg Subtype.val (hA.1.is_comm.comm x y))
  · obtain ⟨x, rfl⟩ := hy
    rw [← map_pow]
    have : x ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hA.2 x x.2)
    rw [this, map_one]
  · have hkerZ : a.ker = Z.subgroupOf A := by
      ext x
      rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    have hcardA := Subgroup.card_eq_card_quotient_mul_card_subgroup a.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange a).toEquiv, hkerZ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZA).toEquiv, hAcard, hZp] at hcardA
    exact Nat.eq_of_mul_eq_mul_right hp.pos (by rw [← hcardA]; ring)
  · rw [hLK]
    exact hQK

theorem central_line_faithful_component_detection {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {A : Subgroup G} (hA : IsElementaryAbelian p A)
    (hAcard : Nat.card A = p ^ 3) (Z : Subgroup G) [Z.Normal] (hZA : Z ≤ A)
    (hZc : Z ≤ Subgroup.center G) (hZp : Nat.card Z = p)
    (hnorm : ∀ L ∈ thetaComponents p G, A ≤ Subgroup.normalizer (L : Set G))
    (hα : ¬ thetaAlpha p (A.map (QuotientGroup.mk' Z)) ≤ aschbacherSolvableCore p (G ⧸ Z))
    (B : Subgroup G) (hBA : B ≤ A) (hBZ : Disjoint B Z) (hBZA : B ⊔ Z = A) :
    ∃ L ∈ thetaComponents p G, ∃ a : A →* MulAut (L ⧸ aschbacherSolvableCore p L),
      (∀ (x : A) (l l' : L), (l' : G) = x * l * (x : G)⁻¹ →
        a x (l : L ⧸ aschbacherSolvableCore p L) = (l' : L ⧸ aschbacherSolvableCore p L)) ∧
      (∀ x : A, a x = 1 ↔ (x : G) ∈ Z) ∧
      IsElementaryAbelian p a.range ∧ Nat.card a.range = p ^ 2 ∧
      ¬ (thetaAlpha p B).map (QuotientGroup.mk' (aschbacherSolvableCore p G)) ≤
        Subgroup.centralizer ((L.map (QuotientGroup.mk' (aschbacherSolvableCore p G)) :
          Subgroup (G ⧸ aschbacherSolvableCore p G)) : Set (G ⧸ aschbacherSolvableCore p G)) :=
  central_line_faithful_component_detection_of hp hA hAcard Z hZA hZc hZp hnorm hα B hBA hBZ hBZA
    fun _ hE hEcard _ ht ht1 _ hK hX hC =>
      (Coprime.nonfaithful_plane_local_core_product_centralizes_component hp hE hEcard ht ht1 hK
        hX hC).imp_right And.left

end CFSG.RankThree
