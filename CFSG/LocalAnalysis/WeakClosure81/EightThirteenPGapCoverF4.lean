module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapF4Data
public import CFSG.RankThree.Theta.TwoPlaneQuotient

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2)

private theorem wcgapcf_oTwoMod_bot_eq_pCoreOf {Y : Type} [Group Y] [Finite Y]
    (K : Subgroup Y) :
    oTwoMod (⊥ : Subgroup Y) K = CFSG.Open.pCoreOf 2 K := by
  rw [CFSG.Open.pCoreOf, CFSG.pCore_eq_iSup]
  apply le_antisymm
  · refine iSup₂_le fun W hW => ?_
    have hWK : W ≤ K := hW.2.1
    have hWnorm : (W.subgroupOf K).Normal := hW.2.2.1
    have hW2 : IsPGroup 2 (W.subgroupOf K) := by
      rw [isPGroup_iff_pow_pow_eq_one]
      intro x
      obtain ⟨n, hn⟩ := hW.2.2.2 (x : Y) x.2
      exact ⟨n, Subtype.ext (Subtype.ext (by simpa using Subgroup.mem_bot.mp hn))⟩
    have hle : W.subgroupOf K ≤
        ⨆ (N : Subgroup ↥K) (_ : N.Normal) (_ : IsPGroup 2 N), N :=
      le_iSup₂_of_le (W.subgroupOf K) hWnorm (le_iSup_of_le hW2 le_rfl)
    calc W = (W.subgroupOf K).map K.subtype := (Subgroup.map_subgroupOf_eq_of_le hWK).symm
      _ ≤ ((⨆ (N : Subgroup ↥K) (_ : N.Normal) (_ : IsPGroup 2 N), N)).map K.subtype :=
          Subgroup.map_mono hle
  · rw [Subgroup.map_iSup]
    refine iSup_le fun N => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hNnorm => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hN2 => ?_
    refine le_iSup₂_of_le (N.map K.subtype) ?_ le_rfl
    refine ⟨bot_le, Subgroup.map_subtype_le N, ?_, ?_⟩
    · change ((N.map K.subtype).comap K.subtype).Normal
      rw [Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
      exact hNnorm
    · intro w hw
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hw
      obtain ⟨j, hj⟩ := hN2.exists_pow_pow_eq_one ⟨n, hn⟩
      exact ⟨j, Subgroup.mem_bot.mpr (by
        rw [← map_pow]
        simpa using congrArg (fun x : ↥N => K.subtype (x : ↥K)) hj)⟩

private theorem wcgapcf_pCoreOf_map {G₀ G : Type} [Group G₀] [Finite G₀] [Group G]
    (α : G₀ →* G) (hα : Function.Surjective α) (hker : α.ker ≤ Subgroup.center G₀)
    (hodd : Odd (Nat.card ↥α.ker)) (K₀ : Subgroup G₀) :
    CFSG.Open.pCoreOf 2 (K₀.map α) = (CFSG.Open.pCoreOf 2 K₀).map α := by
  let f : ↥K₀ →* ↥(K₀.map α) :=
    (α.comp K₀.subtype).codRestrict (K₀.map α) fun x => ⟨x, x.2, rfl⟩
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  haveI : Finite ↥K₀ := Subtype.finite
  haveI : Finite ↥(K₀.map α) := Finite.of_surjective f hf
  have hfker : f.ker ≤ Subgroup.center ↥K₀ := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hx' : ((x : ↥K₀) : G₀) ∈ α.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val hx
    exact Subgroup.mem_center_iff.mp (hker hx') (y : G₀)
  have hfodd : Odd (Nat.card ↥f.ker) := by
    have hle : (f.ker).map K₀.subtype ≤ α.ker := by
      rintro g ⟨x, hx, rfl⟩
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val hx
    rw [← Subgroup.card_map_of_injective (K := f.ker) K₀.subtype_injective]
    exact hodd.of_dvd_nat (Subgroup.card_dvd_of_le hle)
  have hmain := CFSG.RankThree.Theta.TwoPlane.pCore_two_eq_map_of_central_kernel f hf hfker hfodd
  rw [CFSG.Open.pCoreOf, hmain, CFSG.Open.pCoreOf]
  simp only [Subgroup.map_map]
  congr 1

private def wcgapcf_oddSet {Y : Type} [Group Y] (N P : Subgroup Y) : Set (Subgroup Y) :=
  {Q | N ≤ Q ∧ Q ≤ P ∧ (Q.subgroupOf P).Normal ∧ Odd (Q.relIndex P)}

private theorem wcgapcf_oddResMod_bot_le {Y : Type} [Group Y] (P : Subgroup Y) :
    oddResMod (⊥ : Subgroup Y) P ≤ P := by
  refine (iInf_le (fun Q => ⨅ (_ : Q ∈ wcgapcf_oddSet (⊥ : Subgroup Y) P), Q) P).trans ?_
  refine iInf_le (fun _ => P) ?_
  exact ⟨bot_le, le_rfl, by rw [Subgroup.subgroupOf_self]; infer_instance,
    by rw [Subgroup.relIndex_self]; norm_num⟩

private theorem wcgapcf_normal_oddResMod {Y : Type} [Group Y] (P : Subgroup Y) :
    ((oddResMod (⊥ : Subgroup Y) P).subgroupOf P).Normal := by
  have hPmem : P ∈ wcgapcf_oddSet (⊥ : Subgroup Y) P :=
    ⟨bot_le, le_rfl, by rw [Subgroup.subgroupOf_self]; infer_instance,
      by rw [Subgroup.relIndex_self]; norm_num⟩
  have ho : oddResMod (⊥ : Subgroup Y) P =
      ⨅ Q : {Q : Subgroup Y // Q ∈ wcgapcf_oddSet (⊥ : Subgroup Y) P}, (Q : Subgroup Y) :=
    (iInf_subtype'' _ (fun Q : Subgroup Y => Q)).symm
  rw [ho]
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer ?_).mpr ?_
  · exact (iInf_le (fun Q : {Q : Subgroup Y // Q ∈ wcgapcf_oddSet (⊥ : Subgroup Y) P} =>
      (Q : Subgroup Y)) ⟨P, hPmem⟩)
  · refine le_trans ?_ (Subgroup.iInf_normalizer_le_normalizer_iInf
      (fun Q : {Q : Subgroup Y // Q ∈ wcgapcf_oddSet (⊥ : Subgroup Y) P} => (Q : Subgroup Y)))
    intro p hp
    rw [Subgroup.mem_iInf]
    intro Q
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer Q.2.2.1).mp Q.2.2.2.1 hp

private theorem wcgapcf_odd_inf_relIndex {Y : Type} [Group Y] {H K P : Subgroup Y}
    (hKP : K ≤ P) (hHn : (H.subgroupOf P).Normal)
    (hHodd : Odd (H.relIndex P)) (hKodd : Odd (K.relIndex P)) :
    Odd ((H ⊓ K).relIndex P) := by
  have hdvd : H.relIndex K ∣ H.relIndex P := by
    haveI : (H.subgroupOf P).Normal := hHn
    have h := Subgroup.relIndex_dvd_index_of_normal (H := H.subgroupOf P) (K := K.subgroupOf P)
    rw [Subgroup.relIndex_subgroupOf (H := H) (K := K) (L := P) hKP] at h
    exact h
  rw [← Subgroup.relIndex_inf_mul_relIndex (H := H) (K := K) (L := P), inf_eq_left.mpr hKP]
  exact (Odd.of_dvd_nat hHodd hdvd).mul hKodd

private theorem wcgapcf_finset_inf_odd {Y : Type} [Group Y] (P : Subgroup Y)
    (s : Finset {Q : Subgroup Y // Q ∈ wcgapcf_oddSet (⊥ : Subgroup Y) P}) :
    Odd ((s.inf (fun i => i.1) ⊓ P).relIndex P) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.inf_empty]
      simp
  | insert a t ha ih =>
      rw [Finset.inf_insert]
      have hAodd : Odd (a.1.relIndex P) := a.2.2.2.2
      have hAn : (a.1.subgroupOf P).Normal := a.2.2.2.1
      have hEq : (a.1 ⊓ t.inf (fun i => i.1)) ⊓ P =
          a.1 ⊓ (t.inf (fun i => i.1) ⊓ P) := inf_assoc _ _ _
      rw [hEq]
      exact wcgapcf_odd_inf_relIndex (H := a.1) (K := t.inf (fun i => i.1) ⊓ P) (P := P)
        inf_le_right hAn hAodd ih

private theorem wcgapcf_odd_oddResMod_relIndex {Y : Type} [Group Y] [Finite Y]
    (P : Subgroup Y) : Odd ((oddResMod (⊥ : Subgroup Y) P).relIndex P) := by
  classical
  let S := wcgapcf_oddSet (⊥ : Subgroup Y) P
  let idx := {Q : Subgroup Y // Q ∈ S}
  haveI : Fintype idx := Fintype.ofFinite idx
  have hPmem : P ∈ S :=
    ⟨bot_le, le_rfl, by rw [Subgroup.subgroupOf_self]; infer_instance,
      by rw [Subgroup.relIndex_self]; norm_num⟩
  have hK_eq : oddResMod (⊥ : Subgroup Y) P = (Finset.univ : Finset idx).inf (fun i => i.1) := by
    rw [oddResMod]
    refine le_antisymm ?_ ?_
    · refine Finset.le_inf fun i _ => ?_
      exact (iInf_le (fun Q' => ⨅ (_ : Q' ∈ wcgapcf_oddSet (⊥ : Subgroup Y) P), Q') i.1).trans
        (iInf_le (fun _ => i.1) i.2)
    · refine le_iInf fun Q' => le_iInf fun hQ' => ?_
      exact Finset.inf_le (Finset.mem_univ (⟨Q', hQ'⟩ : idx))
  have hinf_le_P : (Finset.univ : Finset idx).inf (fun i => i.1) ≤ P := by
    let iP : idx := ⟨P, hPmem⟩
    simpa using (Finset.inf_le (Finset.mem_univ iP) :
      (Finset.univ : Finset idx).inf (fun i => i.1) ≤ P)
  rw [hK_eq, ← inf_eq_left.mpr hinf_le_P]
  exact wcgapcf_finset_inf_odd P Finset.univ

private theorem wcgapcf_relIndex_map_map_dvd {G₀ G : Type} [Group G₀] [Group G]
    (α : G₀ →* G) {A B : Subgroup G₀} (hAB : A ≤ B) :
    (A.map α).relIndex (B.map α) ∣ A.relIndex B := by
  let f : ↥B →* ↥(B.map α) :=
    (α.comp B.subtype).codRestrict (B.map α) fun x => Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨b, hb⟩, Subtype.ext hby⟩
  have hmap : (A.subgroupOf B).map f = (A.map α).subgroupOf (B.map α) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Subgroup.mem_map.mpr ⟨(x : G₀), Subgroup.mem_subgroupOf.mp hx, rfl⟩
    · intro hy
      obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨a, hAB ha⟩, Subgroup.mem_subgroupOf.mpr ha, Subtype.ext hay⟩
  change ((A.map α).subgroupOf (B.map α)).index ∣ (A.subgroupOf B).index
  rw [← hmap]
  exact (A.subgroupOf B).index_map_dvd hf

theorem normalizer_map_of_cover {G₀ G : Type} [Group G₀] [Finite G₀] [Group G] (α : G₀ →* G)
    (hα : Function.Surjective α) (hker : α.ker ≤ Subgroup.center G₀)
    (hodd : Odd (Nat.card ↥α.ker)) {S₀ : Subgroup G₀} (hS₀ : IsPGroup 2 S₀) :
    normalizer ((S₀.map α : Subgroup G) : Set G) = (normalizer (S₀ : Set G₀)).map α :=
  (CFSG.ComponentClassification.OddKernelNormalizers.image α hα hodd S₀ hS₀).symm

theorem oTwoMod_bot_map_of_cover {G₀ G : Type} [Group G₀] [Finite G₀] [Group G] (α : G₀ →* G)
    (hα : Function.Surjective α) (hker : α.ker ≤ Subgroup.center G₀)
    (hodd : Odd (Nat.card ↥α.ker)) (K₀ : Subgroup G₀) :
    oTwoMod (⊥ : Subgroup G) (K₀.map α) = (oTwoMod (⊥ : Subgroup G₀) K₀).map α := by
  haveI : Finite G := Finite.of_surjective α hα
  rw [wcgapcf_oTwoMod_bot_eq_pCoreOf (K₀.map α), wcgapcf_oTwoMod_bot_eq_pCoreOf K₀]
  exact wcgapcf_pCoreOf_map α hα hker hodd K₀

theorem oddResMod_bot_map_of_cover {G₀ G : Type} [Group G₀] [Finite G₀] [Group G] (α : G₀ →* G)
    (P₀ : Subgroup G₀) :
    oddResMod (⊥ : Subgroup G) (P₀.map α) = (oddResMod (⊥ : Subgroup G₀) P₀).map α := by
  let f : ↥P₀ →* ↥(P₀.map α) :=
    (α.comp P₀.subtype).codRestrict (P₀.map α) fun x => ⟨x, x.2, rfl⟩
  let O₀ := oddResMod (⊥ : Subgroup G₀) P₀
  have hO₀le : O₀ ≤ P₀ := wcgapcf_oddResMod_bot_le P₀
  have hO₀odd : Odd (O₀.relIndex P₀) := wcgapcf_odd_oddResMod_relIndex P₀
  have hO₀n : (O₀.subgroupOf P₀).Normal := wcgapcf_normal_oddResMod P₀
  apply le_antisymm
  ·
    refine (iInf_le (fun Q => ⨅ (_ : Q ∈ wcgapcf_oddSet (⊥ : Subgroup G) (P₀.map α)), Q)
      (O₀.map α)).trans (iInf_le (fun _ => O₀.map α) ?_)
    refine ⟨bot_le, Subgroup.map_mono hO₀le, ?_, ?_⟩
    ·
      refine ⟨fun a ha b => ?_⟩
      obtain ⟨a₀, ha₀, haval⟩ := Subgroup.mem_map.mp (show (a : G) ∈ O₀.map α from ha)
      obtain ⟨b₀, hb₀, hbval⟩ := Subgroup.mem_map.mp b.2
      have hb₀N : b₀ ∈ Subgroup.normalizer (O₀ : Set G₀) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hO₀le).mp hO₀n hb₀
      have hconj : b₀ * a₀ * b₀⁻¹ ∈ O₀ :=
        (Subgroup.mem_normalizer_iff.mp hb₀N a₀).mp ha₀
      refine Subgroup.mem_map.mpr ⟨b₀ * a₀ * b₀⁻¹, hconj, ?_⟩
      show α (b₀ * a₀ * b₀⁻¹) = (b : G) * (a : G) * (b : G)⁻¹
      simp only [map_mul, map_inv, haval, hbval]
    · exact Odd.of_dvd_nat hO₀odd (wcgapcf_relIndex_map_map_dvd α hO₀le)
  ·
    refine le_iInf fun Q => le_iInf fun hQ => ?_
    have hQP : Q ≤ P₀.map α := hQ.2.1
    have hQn : (Q.subgroupOf (P₀.map α)).Normal := hQ.2.2.1
    have hQodd : Odd (Q.relIndex (P₀.map α)) := hQ.2.2.2
    have hQ₀mem : P₀ ⊓ Q.comap α ∈ wcgapcf_oddSet (⊥ : Subgroup G₀) P₀ := by
      refine ⟨bot_le, inf_le_left, ?_, ?_⟩
      · have hsub : (P₀ ⊓ Q.comap α).subgroupOf P₀ =
            (Q.subgroupOf (P₀.map α)).comap f := by
          ext x
          show (x : G₀) ∈ P₀ ⊓ Q.comap α ↔ α (x : G₀) ∈ Q
          constructor
          · intro hx
            exact Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hx).2
          · intro hx
            exact Subgroup.mem_inf.mpr ⟨x.2, Subgroup.mem_comap.mpr hx⟩
        rw [hsub]
        exact hQn.comap f
      · have hrel : (P₀ ⊓ Q.comap α).relIndex P₀ = Q.relIndex (P₀.map α) := by
          change ((P₀ ⊓ Q.comap α).subgroupOf P₀).index = Q.relIndex (P₀.map α)
          rw [Subgroup.inf_subgroupOf_left]
          exact Subgroup.relIndex_comap (f := α) (H := Q) (K := P₀)
        rw [hrel]
        exact hQodd
    have hO₀leQ₀ : O₀ ≤ P₀ ⊓ Q.comap α :=
      (iInf_le (fun Q' => ⨅ (_ : Q' ∈ wcgapcf_oddSet (⊥ : Subgroup G₀) P₀), Q')
        (P₀ ⊓ Q.comap α)).trans (iInf_le (fun _ => P₀ ⊓ Q.comap α) hQ₀mem)
    have hmapQ₀ : (P₀ ⊓ Q.comap α).map α = Q := by
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hx).2
      · intro q hq
        obtain ⟨p, hpP, hpval⟩ := Subgroup.mem_map.mp (hQP hq)
        exact Subgroup.mem_map.mpr ⟨p,
          Subgroup.mem_inf.mpr ⟨hpP, Subgroup.mem_comap.mpr (hpval ▸ hq)⟩, hpval⟩
    rw [← hmapQ₀]
    exact Subgroup.map_mono hO₀leQ₀

private theorem wcgapcf_center_eq_bot_of_isL2 {X : Type} [Group X] (h : IsL2 X 2) :
    Subgroup.center X = ⊥ := by
  obtain ⟨-, K, hField, hFinite, -, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  letI : Field K := hField
  letI : Finite K := hFinite
  let e' : X ≃* CFSG.GorensteinWalter.PSL2 K :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hZ : Subgroup.center (CFSG.GorensteinWalter.PSL2 K) = ⊥ :=
    CFSG.GorensteinWalter.psl2_center_eq_bot K
  have hmap := Subgroup.map_center_eq e'
  rw [hZ] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center X) (f := e'.toMonoidHom)
    e'.injective).mp hmap

private theorem wcgapcf_inf_ker_le_oTwoMod {G₀ G : Type} [Group G₀] [Finite G₀] [Group G]
    (α : G₀ →* G) (hker : α.ker ≤ Subgroup.center G₀) {K : Subgroup G₀}
    (h : HasQuotShape K (oTwoMod (⊥ : Subgroup G₀) K : Set G₀) (fun X _ => IsL2 X 2)) :
    K ⊓ α.ker ≤ oTwoMod (⊥ : Subgroup G₀) K := by
  obtain ⟨X, hX, φ, hφ, hkerφ, hL2⟩ := h
  letI : Group X := hX
  have hcenter : Subgroup.center X = ⊥ := wcgapcf_center_eq_bot_of_isL2 hL2
  intro z hz
  obtain ⟨hzK, hzker⟩ := Subgroup.mem_inf.mp hz
  have hzcenter : (⟨z, hzK⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hker hzker) (y : G₀)
  have hzφ : φ ⟨z, hzK⟩ ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨k, hk⟩ := hφ x
    rw [← hk, ← map_mul, ← map_mul]
    congr 1
    exact Subgroup.mem_center_iff.mp hzcenter k
  rw [hcenter, Subgroup.mem_bot] at hzφ
  exact (hkerφ ⟨z, hzK⟩).mp hzφ

private theorem wcgapcf_hasQuotShape_map {G₀ G : Type} [Group G₀] [Group G]
    (α : G₀ →* G) {K N : Subgroup G₀} (P : ∀ (X : Type) [Group X], Prop)
    (hNK : N ≤ K) (hker : K ⊓ α.ker ≤ N) (h : HasQuotShape K (N : Set G₀) P) :
    HasQuotShape (K.map α) ((N.map α : Subgroup G) : Set G) P := by
  obtain ⟨X, hX, φ, hφ, hkerφ, hP⟩ := h
  letI : Group X := hX
  let f : ↥K →* ↥(K.map α) :=
    (α.comp K.subtype).codRestrict (K.map α) fun x => ⟨x, x.2, rfl⟩
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hfker : f.ker ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (hkerφ x).mpr (hker (Subgroup.mem_inf.mpr ⟨x.2, by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val hx⟩))
  let ψ : ↥(K.map α) →* X := (MonoidHom.liftOfSurjective f hf) ⟨φ, hfker⟩
  have hψ : ∀ x : ↥K, ψ (f x) = φ x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply f (Function.surjInv hf)
      (Function.rightInverse_surjInv hf) ⟨φ, hfker⟩ x
  refine ⟨X, hX, ψ, ?_, ?_, hP⟩
  · intro x
    obtain ⟨k, hk⟩ := hφ x
    exact ⟨f k, by rw [hψ, hk]⟩
  · intro y
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := hf y
      rw [hψ] at hy
      exact Subgroup.mem_map.mpr ⟨(k : G₀), (hkerφ k).mp hy, rfl⟩
    · intro hy
      obtain ⟨k, rfl⟩ := hf y
      rw [hψ]
      obtain ⟨n, hn, hnval⟩ := Subgroup.mem_map.mp hy
      have hz : (k : G₀) * n⁻¹ ∈ α.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hnval]
        exact mul_inv_cancel (α k)
      have hk : (k : G₀) ∈ N := by
        have h1 : (k : G₀) * n⁻¹ ∈ K ⊓ α.ker :=
          Subgroup.mem_inf.mpr ⟨K.mul_mem k.2 (K.inv_mem (hNK hn)), hz⟩
        have h2 : (k : G₀) = ((k : G₀) * n⁻¹) * n := by group
        rw [h2]
        exact N.mul_mem (hker h1) hn
      exact (hkerφ k).mpr hk

private theorem wcgapcf_isSylowIn_map {G₀ G : Type} [Group G₀] [Group G]
    (α : G₀ →* G) {P H : Subgroup G₀} (h : IsSylowIn 2 P H) :
    IsSylowIn 2 (P.map α) (H.map α) :=
  ⟨Subgroup.map_mono h.le, h.isPGroup.map α, fun hdvd =>
    h.not_dvd_relIndex (hdvd.trans (wcgapcf_relIndex_map_map_dvd α h.le))⟩

private theorem wcgapcf_relIndex_map_eq_of_ker_le {G₀ G : Type} [Group G₀] [Group G]
    (α : G₀ →* G) {A B : Subgroup G₀} (hAB : A ≤ B) (hker : B ⊓ α.ker ≤ A) :
    (A.map α).relIndex (B.map α) = A.relIndex B := by
  let f : ↥B →* ↥(B.map α) :=
    (α.comp B.subtype).codRestrict (B.map α) fun x => ⟨x, x.2, rfl⟩
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨b, hb⟩, Subtype.ext hby⟩
  have hmap : (A.subgroupOf B).map f = (A.map α).subgroupOf (B.map α) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Subgroup.mem_map.mpr ⟨(x : G₀), Subgroup.mem_subgroupOf.mp hx, rfl⟩
    · intro hy
      obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨a, hAB ha⟩, Subgroup.mem_subgroupOf.mpr ha, Subtype.ext hay⟩
  have hkerle : f.ker ≤ A.subgroupOf B := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_subgroupOf]
    exact hker (Subgroup.mem_inf.mpr ⟨x.2, by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val hx⟩)
  change ((A.map α).subgroupOf (B.map α)).index = (A.subgroupOf B).index
  rw [← hmap]
  exact (A.subgroupOf B).index_map_eq hf hkerle

private theorem wcgapcf_relIndex_inf_normalizer_map {G₀ G : Type} [Group G₀] [Finite G₀] [Group G]
    (α : G₀ →* G) (hα : Function.Surjective α) (hker : α.ker ≤ Subgroup.center G₀)
    (hodd : Odd (Nat.card ↥α.ker)) {S₀ K : Subgroup G₀} (hS₀ : IsPGroup 2 S₀)
    (hidx : (K ⊓ ((⊤ : Subgroup G₀) ⊓ normalizer (S₀ : Set G₀))).relIndex K = 5) :
    (K.map α ⊓ ((⊤ : Subgroup G) ⊓ normalizer ((S₀.map α : Subgroup G) : Set G))).relIndex
      (K.map α) = 5 := by
  have hkerNS : α.ker ≤ Subgroup.normalizer (S₀ : Set G₀) :=
    hker.trans (Subgroup.center_le_normalizer (S₀ : Set G₀))
  have hmapinf : (K ⊓ Subgroup.normalizer (S₀ : Set G₀)).map α =
      K.map α ⊓ (Subgroup.normalizer (S₀ : Set G₀)).map α := by
    apply le_antisymm (Subgroup.map_inf_le K (Subgroup.normalizer (S₀ : Set G₀)) α)
    intro x hx
    obtain ⟨hk, hns⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨k, hkK, hkval⟩ := Subgroup.mem_map.mp hk
    obtain ⟨n, hnNS, hnval⟩ := Subgroup.mem_map.mp hns
    have hz : k * n⁻¹ ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hkval, hnval, mul_inv_cancel]
    have hkn : k * n⁻¹ ∈ Subgroup.normalizer (S₀ : Set G₀) := hkerNS hz
    have hk' : k = (k * n⁻¹) * n := by group
    exact Subgroup.mem_map.mpr ⟨k, Subgroup.mem_inf.mpr ⟨hkK, by
      rw [hk']; exact (Subgroup.normalizer (S₀ : Set G₀)).mul_mem hkn hnNS⟩, hkval⟩
  rw [top_inf_eq, normalizer_map_of_cover α hα hker hodd hS₀, ← hmapinf]
  rw [wcgapcf_relIndex_map_eq_of_ker_le α inf_le_left
    (le_inf inf_le_left (inf_le_right.trans hkerNS))]
  simpa only [top_inf_eq] using hidx

private theorem wcgapcf_eq_of_isPGroup_of_map_eq {G₀ G : Type} [Group G₀] [Group G]
    (α : G₀ →* G) (hker : α.ker ≤ Subgroup.center G₀) (hodd : Odd (Nat.card ↥α.ker))
    {a b : G₀} (ha : ∃ k, a ^ 2 ^ k = 1) (hb : ∃ k, b ^ 2 ^ k = 1)
    (hab : α a = α b) : a = b := by
  have hzker : a * b⁻¹ ∈ α.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hab, mul_inv_cancel]
  set z := a * b⁻¹ with hz
  have haz : z * b = a := by rw [hz]; group
  have hzodd : Odd (orderOf z) :=
    hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard α.ker hzker)
  have hcomm : Commute z b := (Subgroup.mem_center_iff.mp (hker hzker) b).symm
  obtain ⟨ka, hka⟩ := ha
  obtain ⟨kb, hkb⟩ := hb
  have hbN : b ^ 2 ^ max ka kb = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp
      (dvd_trans (orderOf_dvd_iff_pow_eq_one.mpr hkb) (Nat.pow_dvd_pow 2 (le_max_right _ _)))
  have haN : a ^ 2 ^ max ka kb = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp
      (dvd_trans (orderOf_dvd_iff_pow_eq_one.mpr hka) (Nat.pow_dvd_pow 2 (le_max_left _ _)))
  have hzN : z ^ 2 ^ max ka kb = 1 := by
    have h : (z * b) ^ 2 ^ max ka kb = 1 := by rw [haz, haN]
    rw [hcomm.mul_pow, hbN, mul_one] at h
    exact h
  have hz1 : z = 1 := by
    apply orderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes ((Nat.coprime_two_right.mpr hzodd).pow_right _)
      (dvd_refl _) (orderOf_dvd_iff_pow_eq_one.mpr hzN)
  rw [← haz, hz1, one_mul]

private theorem wcgapcf_isPGroup_of_pow_eq_one {G₀ : Type} [Group G₀] {S : Subgroup G₀}
    (h : ∀ s ∈ S, ∃ k, s ^ 2 ^ k = 1) : IsPGroup 2 S := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro s
  obtain ⟨k, hk⟩ := h s s.2
  exact ⟨k, Subtype.ext hk⟩

private theorem wcgapcf_isPGroup_oTwoMod {Y : Type} [Group Y] [Finite Y] (K : Subgroup Y) :
    IsPGroup 2 (oTwoMod (⊥ : Subgroup Y) K) := by
  rw [wcgapcf_oTwoMod_bot_eq_pCoreOf K]
  exact (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).map K.subtype

private theorem wcgapcf_isMaxParabolicMod_top_map {G₀ G : Type} [Group G₀] [Finite G₀] [Group G]
    (α : G₀ →* G) (hα : Function.Surjective α) (hker : α.ker ≤ Subgroup.center G₀)
    (hodd : Odd (Nat.card ↥α.ker)) {P : Subgroup G₀}
    (h : IsMaxParabolicMod (⊥ : Subgroup G₀) (⊤ : Subgroup G₀) P) :
    IsMaxParabolicMod (⊥ : Subgroup G) (⊤ : Subgroup G) (P.map α) := by
  obtain ⟨-, hPLt, hmax, S, -, -, hSpow, hSodd, hSnorm⟩ := h
  have hS2 : IsPGroup 2 S := wcgapcf_isPGroup_of_pow_eq_one fun s hs =>
    (hSpow s hs).imp fun k hk => Subgroup.mem_bot.mp hk
  have hkerP : α.ker ≤ P :=
    (hker.trans (Subgroup.center_le_normalizer (S : Set G₀))).trans
      (by simpa only [top_inf_eq] using hSnorm)
  have hPtop : P.map α < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    exact hPLt.ne (by
      rw [eq_top_iff]
      intro x _
      have hxmap : α x ∈ P.map α := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨p, hp, hpx⟩ := Subgroup.mem_map.mp hxmap
      have hz : x * p⁻¹ ∈ α.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hpx, mul_inv_cancel]
      have hxp : x = (x * p⁻¹) * p := by group
      rw [hxp]
      exact P.mul_mem (hkerP hz) hp)
  have hmaxmap : ∀ Y : Subgroup G, P.map α < Y → Y ≤ ⊤ → Y = ⊤ := by
    intro Y hPY _
    by_contra hYtop
    have hle : P ≤ Y.comap α := fun p hp => hPY.le (Subgroup.mem_map.mpr ⟨p, hp, rfl⟩)
    have hlt : P < Y.comap α := by
      refine lt_of_le_of_ne hle ?_
      intro heq
      exact hPY.ne (by rw [← Subgroup.map_comap_eq_self_of_surjective hα Y, heq])
    have hYcomap : Y.comap α = ⊤ := hmax (Y.comap α) hlt le_top
    exact hYtop (by rw [← Subgroup.map_comap_eq_self_of_surjective hα Y, hYcomap,
      Subgroup.map_top_of_surjective α hα])
  refine ⟨bot_le, hPtop, hmaxmap, S.map α, bot_le, le_top, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨s₀, hs₀, rfl⟩ := Subgroup.mem_map.mp hs
    obtain ⟨k, hk⟩ := hSpow s₀ hs₀
    exact ⟨k, Subgroup.mem_bot.mpr (by rw [← map_pow, Subgroup.mem_bot.mp hk, map_one])⟩
  · rw [← Subgroup.map_top_of_surjective α hα]
    exact fun hdvd => hSodd (hdvd.trans (wcgapcf_relIndex_map_map_dvd α le_top))
  · rw [top_inf_eq, normalizer_map_of_cover α hα hker hodd hS2]
    exact Subgroup.map_mono (by simpa only [top_inf_eq] using hSnorm)

theorem centralKData_of_cover {G₀ G : Type} [Group G₀] [Finite G₀] [Group G] (α : G₀ →* G)
    (hα : Function.Surjective α) (hker : α.ker ≤ Subgroup.center G₀)
    (hodd : Odd (Nat.card ↥α.ker)) {S₀ A₀ : Subgroup G₀} (hS₀ : IsPGroup 2 S₀) (hAS : A₀ ≤ S₀)
    (h : CentralKData S₀ A₀) :
    CentralKData (S₀.map α) (A₀.map α) := by
  obtain ⟨K₀, hAK, hnO₂, hshape, hsyl, hidx⟩ := h
  haveI : Finite G := Finite.of_surjective α hα
  have hinfker : K₀ ⊓ α.ker ≤ oTwoMod (⊥ : Subgroup G₀) K₀ :=
    wcgapcf_inf_ker_le_oTwoMod α hker hshape
  refine ⟨K₀.map α, Subgroup.map_mono hAK, ?_, ?_, ?_,
    wcgapcf_relIndex_inf_normalizer_map α hα hker hodd hS₀ hidx⟩
  · rw [oTwoMod_bot_map_of_cover α hα hker hodd K₀]
    intro hle
    apply hnO₂
    intro a ha
    have hA2 : IsPGroup 2 A₀ := hS₀.to_le hAS
    obtain ⟨ka, hka⟩ := hA2.exists_pow_pow_eq_one ⟨a, ha⟩
    have hka' : a ^ 2 ^ ka = 1 := congrArg Subtype.val hka
    obtain ⟨o, ho, hoa⟩ := Subgroup.mem_map.mp (hle (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩))
    obtain ⟨ko, hko⟩ := (wcgapcf_isPGroup_oTwoMod K₀).exists_pow_pow_eq_one ⟨o, ho⟩
    have hko' : o ^ 2 ^ ko = 1 := congrArg Subtype.val hko
    set z := o⁻¹ * a with hz
    have haz : o * z = a := by rw [hz]; group
    have hzker : z ∈ α.ker := by
      rw [hz, MonoidHom.mem_ker, map_mul, map_inv, hoa, inv_mul_cancel]
    have hzodd : Odd (orderOf z) :=
    hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard α.ker hzker)
    have hcomm : Commute o z := Subgroup.mem_center_iff.mp (hker hzker) o
    have hzN : z ^ 2 ^ max ka ko = 1 := by
      have h : (o * z) ^ 2 ^ max ka ko = 1 := by
        rw [haz]
        exact orderOf_dvd_iff_pow_eq_one.mp (dvd_trans (orderOf_dvd_iff_pow_eq_one.mpr hka')
          (Nat.pow_dvd_pow 2 (le_max_left ka ko)))
      rw [hcomm.mul_pow, orderOf_dvd_iff_pow_eq_one.mp (dvd_trans
        (orderOf_dvd_iff_pow_eq_one.mpr hko') (Nat.pow_dvd_pow 2 (le_max_right ka ko))),
        one_mul] at h
      exact h
    have hz1 : z = 1 := by
      apply orderOf_eq_one_iff.mp
      exact Nat.eq_one_of_dvd_coprimes ((Nat.coprime_two_right.mpr hzodd).pow_right _)
        (dvd_refl _) (orderOf_dvd_iff_pow_eq_one.mpr hzN)
    rw [← haz, hz1, mul_one]
    exact ho
  · rw [oTwoMod_bot_map_of_cover α hα hker hodd K₀]
    exact wcgapcf_hasQuotShape_map α (K := K₀) (N := oTwoMod (⊥ : Subgroup G₀) K₀)
      (fun X _ => IsL2 X 2) (iSup₂_le fun W hW => hW.2.1) hinfker hshape
  · refine ⟨inf_le_right, (hS₀.map α).to_le inf_le_left, fun hdvd => ?_⟩
    exact (wcgapcf_isSylowIn_map α hsyl).not_dvd_relIndex (hdvd.trans
      (Subgroup.relIndex_dvd_of_le_left (H := (S₀ ⊓ K₀).map α)
        (K := S₀.map α ⊓ K₀.map α) (L := K₀.map α)
        (le_inf (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right))))

theorem rankTwoParabData_of_cover {G₀ G : Type} [Group G₀] [Finite G₀] [Group G] (α : G₀ →* G)
    (hα : Function.Surjective α) (hker : α.ker ≤ Subgroup.center G₀)
    (hodd : Odd (Nat.card ↥α.ker)) {S₀ : Subgroup G₀}
    (hS₀ : IsSylowIn 2 S₀ (⊤ : Subgroup G₀)) (h : RankTwoParabData S₀) :
    RankTwoParabData (S₀.map α) := by
  obtain ⟨P, hmax, hS, hshape, hidx, hcomm⟩ := h
  haveI : Finite G := Finite.of_surjective α hα
  have hS2 : IsPGroup 2 S₀ := hS₀.isPGroup
  refine ⟨fun i => (P i).map α, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact wcgapcf_isMaxParabolicMod_top_map α hα hker hodd (P := P i) (hmax i)
  · intro i
    rw [oddResMod_bot_map_of_cover α (P i)]
    exact Subgroup.map_mono (hS i)
  · intro i
    rw [oddResMod_bot_map_of_cover α (P i),
      oTwoMod_bot_map_of_cover α hα hker hodd (oddResMod (⊥ : Subgroup G₀) (P i))]
    exact wcgapcf_hasQuotShape_map α (K := oddResMod (⊥ : Subgroup G₀) (P i))
      (N := oTwoMod (⊥ : Subgroup G₀) (oddResMod (⊥ : Subgroup G₀) (P i)))
      (fun X _ => IsL2 X 2) (iSup₂_le fun W hW => hW.2.1)
      (wcgapcf_inf_ker_le_oTwoMod α hker (hshape i)) (hshape i)
  · intro i
    rw [oddResMod_bot_map_of_cover α (P i)]
    exact wcgapcf_relIndex_inf_normalizer_map α hα hker hodd hS2
      (K := oddResMod (⊥ : Subgroup G₀) (P i)) (hidx i)
  · intro a' ha0' ha1' s' hs'
    rw [oddResMod_bot_map_of_cover α (P 0),
      oTwoMod_bot_map_of_cover α hα hker hodd (oddResMod (⊥ : Subgroup G₀) (P 0))] at ha0'
    rw [oddResMod_bot_map_of_cover α (P 1),
      oTwoMod_bot_map_of_cover α hα hker hodd (oddResMod (⊥ : Subgroup G₀) (P 1))] at ha1'
    obtain ⟨a, ha0, haval⟩ := Subgroup.mem_map.mp ha0'
    obtain ⟨b, hb1, hbval⟩ := Subgroup.mem_map.mp ha1'
    have ha2 : ∃ k, a ^ 2 ^ k = 1 := by
      obtain ⟨k, hk⟩ := (wcgapcf_isPGroup_oTwoMod
        (oddResMod (⊥ : Subgroup G₀) (P 0))).exists_pow_pow_eq_one ⟨a, ha0⟩
      exact ⟨k, congrArg Subtype.val hk⟩
    have hb2 : ∃ k, b ^ 2 ^ k = 1 := by
      obtain ⟨k, hk⟩ := (wcgapcf_isPGroup_oTwoMod
        (oddResMod (⊥ : Subgroup G₀) (P 1))).exists_pow_pow_eq_one ⟨b, hb1⟩
      exact ⟨k, congrArg Subtype.val hk⟩
    have hab_eq : a = b := wcgapcf_eq_of_isPGroup_of_map_eq α hker hodd ha2 hb2
      (haval.trans hbval.symm)
    have ha1 : a ∈ oTwoMod (⊥ : Subgroup G₀) (oddResMod (⊥ : Subgroup G₀) (P 1)) := by
      rw [hab_eq]; exact hb1
    obtain ⟨s, hsS, hsval⟩ := Subgroup.mem_map.mp hs'
    rw [← haval, ← hsval, ← map_mul, ← map_mul]
    exact congrArg α (hcomm a ha0 ha1 s hsS)

end CFSG.LocalAnalysis.WeakClosure81

end
