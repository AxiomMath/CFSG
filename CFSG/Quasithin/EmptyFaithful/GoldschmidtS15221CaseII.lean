module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15221Ext
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15221Odd
public import CFSG.Quasithin.EmptyFaithful.S152U18
public import CFSG.Quasithin.EmptyFaithful.S152O4Facts
public import CFSG.Quasithin.EmptyFaithful.S152Y17

public section

namespace CFSG.Quasithin.S15221

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

section CaseII

variable {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I : Subgroup G}

omit [Finite G] in
theorem oTwoZIn_le (Y : Subgroup G) : oTwoZIn Y ≤ Y := by
  unfold oTwoZIn preimageModTwoCore
  exact Subgroup.map_subtype_le _

theorem commutator_mem_pCoreOf_of_caseII (h : S152Y.Data T Mc M) (hs : Setting152 T Mc M)
    (hB₀ : IsB0 T Mc M B₀) (hD : Inputs152 T Mc M H B₀ I) (hii : Concl15218ii T Mc M H B₀ I)
    (hYn : M ≤ Subgroup.normalizer (yOf152 T Mc M : Set G))
    (hMb0 : oTwoUpper (mBar0 T Mc M) = oTwoUpper (autOn M (V154 T Mc M)))
    (hθ : oTwoUpper (oTwoZIn (yOf152 T Mc M)) =
      thetaOf (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)))
    {Y₀ : Subgroup G} (hY₀eq : Y₀ = oTwoUpper Y₀) (hY₀3 : (pCoreOf 2 Y₀).relIndex Y₀ = 3)
    (hY₀C : Y₀ ≤ M ⊓ Subgroup.centralizer (V154 T Mc M : Set G))
    {s y₀ : G} (hs' : s ∈ sOf152 T Mc M B₀) (hy₀ : y₀ ∈ Y₀) :
    s * y₀ * s⁻¹ * y₀⁻¹ ∈ pCoreOf 2 M := by
  have hOmS : Om4FactsStatement := fun _ _ _ _ hX => S152O4.om4_facts hX
  have hMV : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hTM : T ≤ M := T_le_M152 hs
  have hsM : s ∈ M := hTM (S_le_T152 hs')
  have hy₀M : y₀ ∈ M := (hY₀C hy₀).1
  obtain ⟨hodd, hEab⟩ := oTwoUpper_Mb_odd_comm hD hOmS
  have hodd0 : Odd (Nat.card (oTwoUpper (mBar0 T Mc M))) := by rw [hMb0]; exact hodd
  have hEab0 : ∀ a ∈ oTwoUpper (mBar0 T Mc M), ∀ b ∈ oTwoUpper (mBar0 T Mc M), a * b = b * a := by
    rw [hMb0]
    exact hEab
  have hcard := om4_card152 hOmS hii.2.2.1
  have hT4 : Nat.card (autOn T (V154 T Mc M)) = 4 := card_autOn_T152 hs hcard.1 hcard.2
  have hSB : autOn (sOf152 T Mc M B₀) (V154 T Mc M) = B₀ := autOn_S_eq_B₀152 hs hB₀ hD hT4
  have hY₀θ : Y₀ ≤ thetaOf (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) :=
    le_thetaOf_of_eq_oTwoUpper hY₀eq hY₀3 hY₀C
  have hθY : thetaOf (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) ≤ yOf152 T Mc M := by
    rw [← hθ]
    exact (oTwoUpper_le _).trans (oTwoZIn_le _)
  have hy₀Y : y₀ ∈ yOf152 T Mc M := hθY (hY₀θ hy₀)
  have hKcen := S152Y.K_central_Ys h
  have hKle := S152Y.Data.K_le_commutator h hodd0
  have hcomm_le := S152Y.Data.commutator_le_K h hEab0
  let g : OTwoQuot M := QuotientGroup.mk ⟨s, hsM⟩
  let u : OTwoQuot M := QuotientGroup.mk ⟨y₀, hy₀M⟩
  have huX : u ∈ S152Y.Ys T Mc M := mem_imageOTwoQuot_iff.mpr ⟨y₀, hy₀M, hy₀Y, rfl⟩
  have huK : u ∈ S152Y.Ys T Mc M ⊓ (S152Y.piStar h).ker :=
    ⟨huX, (S152Y.piStar_mk_eq_one_iff h hy₀M).mpr (hY₀C hy₀).2⟩
  have hgn : ∀ x ∈ S152Y.Ys T Mc M, g * x * g⁻¹ ∈ S152Y.Ys T Mc M := by
    have hSn : sOf152 T Mc M B₀ ≤ Subgroup.normalizer (yOf152 T Mc M : Set G) :=
      (S_le_T152.trans hTM).trans hYn
    have hgS : g ∈ imageOTwoQuot M (sOf152 T Mc M B₀) :=
      mem_imageOTwoQuot_iff.mpr ⟨s, hsM, hs', rfl⟩
    intro x hx
    exact (Subgroup.mem_normalizer_iff.mp (S152Y.imageOTwoQuot_le_normalizer hSn hgS) x).mp hx
  have hπg : S152Y.piStar h g = conjAct (V154 T Mc M) ⟨s, hMV hsM⟩ := rfl
  have hsb : conjAct (V154 T Mc M) ⟨s, hMV hsM⟩ ∈ B₀ := by
    rw [← hSB]
    exact mem_autOn_of_mem (hMV hsM) hs'
  have hπE : ∀ x ∈ S152Y.Ys T Mc M,
      S152Y.piStar h x ∈ oTwoUpper (autOn M (V154 T Mc M)) := by
    intro x hx
    rw [← hMb0]
    exact S152Y.Data.piStar_mem_of_mem_Ys h hx
  have hsc : (∀ x ∈ S152Y.Ys T Mc M, g * x * g⁻¹ * x⁻¹ ∈
        S152Y.Ys T Mc M ⊓ (S152Y.piStar h).ker) ∨
      (∀ x ∈ S152Y.Ys T Mc M, g * x * g⁻¹ * x ∈ S152Y.Ys T Mc M ⊓ (S152Y.piStar h).ker) := by
    by_cases hsb1 : conjAct (V154 T Mc M) ⟨s, hMV hsM⟩ = 1
    · left
      intro x hx
      refine Subgroup.mem_inf.mpr ⟨(S152Y.Ys T Mc M).mul_mem (hgn x hx)
        ((S152Y.Ys T Mc M).inv_mem hx), ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hπg, hsb1]
      simp
    · right
      intro x hx
      refine Subgroup.mem_inf.mpr ⟨(S152Y.Ys T Mc M).mul_mem (hgn x hx) hx, ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, hπg,
        B₀_inverts hs hB₀ hD hOmS _ hsb hsb1 _ (hπE x hx)]
      exact inv_mul_cancel _
  have hgu : g * u * g⁻¹ = u :=
    conj_eq_of_mem_commutator (X := S152Y.Ys T Mc M)
      (Z := S152Y.Ys T Mc M ⊓ (S152Y.piStar h).ker) inf_le_left
      (fun z hz x hx => (hKcen z hz x hx).symm)
      (fun a ha b hb => hcomm_le (Subgroup.commutator_mem_commutator ha hb)) hsc (hKle huK)
  have hcM : s * y₀ * s⁻¹ * y₀⁻¹ ∈ M :=
    M.mul_mem (M.mul_mem (M.mul_mem hsM hy₀M) (M.inv_mem hsM)) (M.inv_mem hy₀M)
  have h1 : (QuotientGroup.mk ⟨s * y₀ * s⁻¹ * y₀⁻¹, hcM⟩ : OTwoQuot M) = 1 := by
    have e : (⟨s * y₀ * s⁻¹ * y₀⁻¹, hcM⟩ : ↥M) =
        ⟨s, hsM⟩ * ⟨y₀, hy₀M⟩ * ⟨s, hsM⟩⁻¹ * ⟨y₀, hy₀M⟩⁻¹ := rfl
    rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, QuotientGroup.mk_inv]
    show g * u * g⁻¹ * u⁻¹ = 1
    rw [hgu, mul_inv_cancel]
  exact (mk_eq_one_iff_mem_pCoreOf _).mp h1

theorem false_of_caseII (h : S152Y.Data T Mc M) (hs : Setting152 T Mc M)
    (hB₀ : IsB0 T Mc M B₀) (hD : Inputs152 T Mc M H B₀ I) (hii : Concl15218ii T Mc M H B₀ I)
    (hYn : M ≤ Subgroup.normalizer (yOf152 T Mc M : Set G))
    (hMb0 : oTwoUpper (mBar0 T Mc M) = oTwoUpper (autOn M (V154 T Mc M)))
    (hθ : oTwoUpper (oTwoZIn (yOf152 T Mc M)) =
      thetaOf (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)))
    {Y₀ : Subgroup G} (hY₀eq : Y₀ = oTwoUpper Y₀) (hY₀3 : (pCoreOf 2 Y₀).relIndex Y₀ = 3)
    (hY₀C : Y₀ ≤ M ⊓ Subgroup.centralizer (V154 T Mc M : Set G))
    (hSY₀ : sOf152 T Mc M B₀ ≤ Subgroup.normalizer (Y₀ : Set G)) {d : G}
    (hdS : d ∈ sOf152 T Mc M B₀)
    (hd : ∀ y ∈ Y₀, y ∉ pCoreOf 2 Y₀ → d * y * d⁻¹ * y⁻¹ ∉ pCoreOf 2 Y₀) : False := by
  have hnle : ¬ Y₀ ≤ pCoreOf 2 Y₀ := fun hle => by
    have h1 := Subgroup.relIndex_eq_one.mpr hle
    rw [hY₀3] at h1
    omega
  obtain ⟨y, hy, hyn⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  apply hd y hy hyn
  have hc := commutator_mem_pCoreOf_of_caseII h hs hB₀ hD hii hYn hMb0 hθ hY₀eq hY₀3 hY₀C hdS hy
  have hYd : d * y * d⁻¹ * y⁻¹ ∈ Y₀ :=
    Y₀.mul_mem ((Subgroup.mem_normalizer_iff.mp (hSY₀ hdS) y).mp hy) (Y₀.inv_mem hy)
  exact inf_pCoreOf_le_pCoreOf (hY₀C.trans inf_le_left) ⟨hYd, hc⟩

end CaseII

end CFSG.Quasithin.S15221
