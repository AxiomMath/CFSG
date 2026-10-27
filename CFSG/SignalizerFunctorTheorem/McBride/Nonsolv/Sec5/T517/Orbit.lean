module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T517.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.SemisimpleFactors

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T517

variable {Γ : Type*} [Group Γ]

@[expose] def orbitOf (E J : Subgroup Γ) : Set (Subgroup Γ) :=
  {K | ∃ a ∈ E, K = J.map (MulAut.conj a).toMonoidHom}

theorem self_mem_orbitOf (E J : Subgroup Γ) : J ∈ orbitOf E J :=
  ⟨1, one_mem E, by ext y; simp [Subgroup.mem_map]⟩

theorem map_conj_mem_orbitOf {E J K : Subgroup Γ} (hK : K ∈ orbitOf E J) {a : Γ} (ha : a ∈ E) :
    K.map (MulAut.conj a).toMonoidHom ∈ orbitOf E J := by
  obtain ⟨c, hc, rfl⟩ := hK
  exact ⟨a * c, mul_mem ha hc, map_conj_map_conj J c a⟩

theorem orbitClosure_eq_sSup_orbitOf (E J : Subgroup Γ) :
    orbitClosure J E = sSup (orbitOf E J) := by
  apply le_antisymm
  · exact iSup₂_le fun a ha => le_sSup ⟨a, ha, rfl⟩
  · refine sSup_le fun K hK => ?_
    obtain ⟨a, ha, rfl⟩ := hK
    exact le_iSup₂_of_le a ha le_rfl

theorem mem_normalizer_smear {E J : Subgroup Γ} {v : Γ}
    (hv : ∀ K ∈ orbitOf E J, v ∈ Subgroup.normalizer (K : Set Γ))
    (hvE : ∀ a ∈ E, v * a = a * v) :
    v ∈ Subgroup.normalizer ((smear J E : Subgroup Γ) : Set Γ) := by
  refine mem_normalizer_inf ?_ (mem_normalizer_centralizer_of_commute hvE)
  rw [orbitClosure_eq_sSup_orbitOf]
  exact mem_normalizer_sSup_of_normalizes hv

variable [Finite Γ] {p : ℕ} {H B : Subgroup Γ} {θ : Γ → Subgroup Γ}

namespace Setting

variable (S : Setting p H B θ) {E J : Subgroup Γ}

include S

theorem orbitOf_subset (hE : E ≤ B) (hJ : J ∈ lcal H) : orbitOf E J ⊆ lcal H := by
  rintro _ ⟨a, ha, rfl⟩
  exact S.map_conj_mem (hE ha) hJ

theorem isDirectProduct_orbitOf (hE : E ≤ B) (hJ : J ∈ lcal H) :
    IsDirectProduct (orbitOf E J) (orbitClosure J E) :=
  isDirectProduct_orbit (hE.trans (S.le.trans Subgroup.le_normalizer)) hJ

theorem orbitClosure_le_kOf (hE : E ≤ B) (hJ : J ∈ lcal H) : orbitClosure J E ≤ kOf H := by
  rw [← (S.isDirectProduct_orbitOf hE hJ).sSup_eq]
  exact S.hK.sSup_diff_le _ (S.orbitOf_subset hE hJ)

theorem smear_le_apply {b : Γ} (hb : b ∈ B) (hb1 : b ≠ 1) (hJ : J ∈ lcal H) :
    smear J (Subgroup.zpowers b) ≤ θ b := by
  refine le_trans ?_ (S.kOf_inf_le b hb hb1)
  refine le_inf ((smear_le_orbitClosure J _).trans
    (S.orbitClosure_le_kOf (Subgroup.zpowers_le.mpr hb) hJ)) ?_
  exact (smear_le_centralizer J _).trans
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers b)))

theorem exists_mulEquiv_smear (hE : E ≤ B) (hJ : J ∈ lcal H) : Nonempty (↥(smear J E) ≃* ↥J) := by
  have hL := S.isDirectProduct_orbitOf hE hJ
  have hA : ∀ a ∈ E, ∀ K ∈ orbitOf E J, K.map (MulAut.conj a).toMonoidHom ∈ orbitOf E J :=
    fun a ha K hK => map_conj_mem_orbitOf hK ha
  have hfree : ∀ a ∈ E, a ≠ 1 → ∀ K ∈ orbitOf E J, K.map (MulAut.conj a).toMonoidHom ≠ K :=
    fun a ha ha1 K hK => S.free K (S.orbitOf_subset hE hJ hK) a (hE ha) ha1
  have htrans : ∀ K ∈ orbitOf E J, ∃ a ∈ E, K = J.map (MulAut.conj a).toMonoidHom :=
    fun K hK => hK
  have hJO := self_mem_orbitOf E J
  let φ : ↥(smear J E) →* ↥J :=
    (hL.coord hJO).comp (Subgroup.inclusion (smear_le_orbitClosure J E))
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have h1 : (y : Γ) ∈ sSup (orbitOf E J \ {J}) :=
      (hL.coord_eq_one_iff hJO ⟨y, smear_le_orbitClosure J E y.2⟩).mp hy
    have h2 := inf_centralizer_inf_sSup_eq_bot_of_transitive hL hA hJO htrans
    have h3 : (y : Γ) ∈ orbitClosure J E ⊓ Subgroup.centralizer (E : Set Γ) ⊓
        sSup (orbitOf E J \ {J}) := ⟨y.2, h1⟩
    rw [h2] at h3
    exact Subtype.ext (Subgroup.mem_bot.mp h3)
  have hsurj : Function.Surjective φ := by
    rintro ⟨j, hj⟩
    obtain ⟨y, hyX, hyj⟩ := (hL.mem_projIn_iff hJO).mp (mem_projIn_of_free hL hA hfree hJO hj)
    exact ⟨⟨y, hyX⟩, Subtype.ext hyj⟩
  exact ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩

theorem isSimpleGroup_smear (hE : E ≤ B) (hJ : J ∈ lcal H) :
    IsSimpleGroup ↥(smear J E) ∧ ¬ IsMulCommutative ↥(smear J E) := by
  obtain ⟨e⟩ := S.exists_mulEquiv_smear hE hJ
  obtain ⟨-, -, hs, hnc⟩ := mem_lcal_iff.mp hJ
  have := hs
  exact ⟨e.isSimpleGroup, fun h => hnc ((isMulCommutative_congr e).mp h)⟩

theorem centralizes_orbitOf (hE : E ≤ B) (hJ : J ∈ lcal H) {x : Γ}
    (hx : ∀ K ∈ orbitOf E J, x ∈ Subgroup.normalizer (K : Set Γ))
    (hxc : ∀ m ∈ smear J E, x * m = m * x) : ∀ K ∈ orbitOf E J, ∀ j ∈ K, x * j = j * x :=
  centralizes_of_centralizes_inf (S.isDirectProduct_orbitOf hE hJ)
    (fun _ ha _ hK => map_conj_mem_orbitOf hK ha)
    (fun a ha ha1 K hK => S.free K (S.orbitOf_subset hE hJ hK) a (hE ha) ha1) hx hxc

end Setting

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T517
