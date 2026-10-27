module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.L511.KRadical
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Projection
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.SemisimpleFactors

public section

open CFSG.Open CFSG.SignalizerFunctorTheorem.Nonsolvable CFSG.SignalizerFunctorTheorem.McBride

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L511

variable {Γ : Type*} [Group Γ]

@[expose] def orbitSet (A J : Subgroup Γ) : Set (Subgroup Γ) :=
  {K | ∃ b ∈ A, K = J.map (MulAut.conj b).toMonoidHom}

theorem map_conj_map_conj' (X : Subgroup Γ) (g h : Γ) :
    (X.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      X.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem map_conj_one' (X : Subgroup Γ) : X.map (MulAut.conj (1 : Γ)).toMonoidHom = X := by
  ext x
  simp [Subgroup.mem_map]

theorem self_mem_orbitSet (A J : Subgroup Γ) : J ∈ orbitSet A J :=
  ⟨1, one_mem A, (map_conj_one' J).symm⟩

theorem map_conj_mem_orbitSet {A J K : Subgroup Γ} (hK : K ∈ orbitSet A J) {a : Γ}
    (ha : a ∈ A) : K.map (MulAut.conj a).toMonoidHom ∈ orbitSet A J := by
  obtain ⟨b, hb, rfl⟩ := hK
  exact ⟨a * b, mul_mem ha hb, map_conj_map_conj' J a b⟩

theorem orbitSet_subset_lcal {A G J : Subgroup Γ} (hAG : A ≤ Subgroup.normalizer (G : Set Γ))
    (hJ : J ∈ lcal G) : orbitSet A J ⊆ lcal G := by
  rintro _ ⟨b, hb, rfl⟩
  exact map_conj_mem_lcal hJ (hAG hb)

theorem map_conj_eq_iff {J : Subgroup Γ} {x y : Γ} :
    J.map (MulAut.conj x).toMonoidHom = J.map (MulAut.conj y).toMonoidHom ↔
      x⁻¹ * y ∈ Subgroup.normalizer (J : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  constructor
  · intro h
    have h1 := congrArg (fun X : Subgroup Γ => X.map (MulAut.conj x⁻¹).toMonoidHom) h
    simp only [map_conj_map_conj', inv_mul_cancel, map_conj_one'] at h1
    change J.map (MulAut.conj (x⁻¹ * y)).toMonoidHom = J
    rw [← h1]
  · intro h
    have h1 : J.map (MulAut.conj (x⁻¹ * y)).toMonoidHom = J := h
    have h2 := congrArg (fun X : Subgroup Γ => X.map (MulAut.conj x).toMonoidHom) h1
    simp only [map_conj_map_conj', mul_inv_cancel_left] at h2
    exact h2.symm

theorem normal_subgroupOf_sSup {K : Subgroup Γ} {S : Set (Subgroup Γ)} (hSK : ∀ J ∈ S, J ≤ K)
    (hn : ∀ J ∈ S, K ≤ Subgroup.normalizer (J : Set Γ)) : ((sSup S).subgroupOf K).Normal := by
  have hle : sSup S ≤ K := sSup_le hSK
  rw [Subgroup.normal_subgroupOf_iff hle]
  intro h k hh hk
  have : sSup S ≤ (sSup S).comap (MulAut.conj k).toMonoidHom := by
    refine sSup_le fun J hJ z hz => ?_
    have hz' : k * z * k⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hn J hJ hk) z).mp hz
    exact le_sSup hJ hz'
  exact this hh

theorem commute_of_forall_commute_sSup {S T : Set (Subgroup Γ)}
    (h : ∀ J₁ ∈ S, ∀ J₂ ∈ T, ∀ x ∈ J₁, ∀ y ∈ J₂, Commute x y) :
    ∀ x ∈ sSup S, ∀ y ∈ sSup T, Commute x y := by
  have h1 : ∀ J₁ ∈ S, sSup T ≤ Subgroup.centralizer (J₁ : Set Γ) := fun J₁ hJ₁ =>
    sSup_le fun J₂ hJ₂ y hy => Subgroup.mem_centralizer_iff.mpr fun x hx =>
      (h J₁ hJ₁ J₂ hJ₂ x hx y hy).eq
  have h2 : sSup S ≤ Subgroup.centralizer ((sSup T : Subgroup Γ) : Set Γ) :=
    sSup_le fun J₁ hJ₁ => Subgroup.le_centralizer_iff.mpr (h1 J₁ hJ₁)
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.mp (h2 hx) y hy).symm

theorem centralizer_zpowers_eq (a : Γ) :
    Subgroup.centralizer ((Subgroup.zpowers a : Subgroup Γ) : Set Γ) =
      Subgroup.centralizer ({a} : Set Γ) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

section Diag

variable [Finite Γ] {p : ℕ} {G J : Subgroup Γ} {a : Γ}

theorem zpowers_eq_of_mem (hp : p.Prime) {x y : Γ} (hxp : x ^ p = 1) (hx1 : x ≠ 1)
    (hy : y ∈ Subgroup.zpowers x) (hy1 : y ≠ 1) : Subgroup.zpowers y = Subgroup.zpowers x := by
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hle : Subgroup.zpowers y ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hy
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rcases (Nat.dvd_prime hp).mp (hord ▸ orderOf_dvd_of_mem_zpowers hy) with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hy1
  · rw [Nat.card_zpowers, Nat.card_zpowers, hord, h]

theorem zpowers_inf_normalizer_eq_bot (hp : p.Prime) (hap : a ^ p = 1) (ha1 : a ≠ 1)
    (haJ : a ∉ Subgroup.normalizer (J : Set Γ)) :
    Subgroup.zpowers a ⊓ Subgroup.normalizer (J : Set Γ) = ⊥ := by
  rw [eq_bot_iff]
  intro b hb
  obtain ⟨hbE, hbN⟩ := Subgroup.mem_inf.mp hb
  rw [Subgroup.mem_bot]
  by_contra hb1
  have hmem : a ∈ Subgroup.zpowers b :=
    zpowers_eq_of_mem hp hap ha1 hbE hb1 ▸ Subgroup.mem_zpowers a
  exact haJ ((Subgroup.zpowers_le.mpr hbN) hmem)

theorem zpowers_inf_zpowers_eq_bot (hp : p.Prime) {b : Γ} (hbp : b ^ p = 1) (hb1 : b ≠ 1)
    (hb : b ∉ Subgroup.zpowers a) :
    Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  obtain ⟨hca, hcb⟩ := Subgroup.mem_inf.mp hc
  rw [Subgroup.mem_bot]
  by_contra hc1
  have hmem : b ∈ Subgroup.zpowers c :=
    zpowers_eq_of_mem hp hbp hb1 hcb hc1 ▸ Subgroup.mem_zpowers b
  exact hb ((Subgroup.zpowers_le.mpr hca) hmem)

theorem isDirectProduct_orbitSet (haG : a ∈ Subgroup.normalizer (G : Set Γ)) (hJ : J ∈ lcal G) :
    IsDirectProduct (orbitSet (Subgroup.zpowers a) J) (orbitClosure J (Subgroup.zpowers a)) :=
  isDirectProduct_orbit (Subgroup.zpowers_le.mpr haG) hJ

theorem projIn_smear_eq (hp : p.Prime) (haG : a ∈ Subgroup.normalizer (G : Set Γ))
    (hap : a ^ p = 1) (ha1 : a ≠ 1) (hJ : J ∈ lcal G)
    (haJ : a ∉ Subgroup.normalizer (J : Set Γ)) :
    projIn (orbitSet (Subgroup.zpowers a) J) J (smear J (Subgroup.zpowers a)) = J := by
  have hQ := isDirectProduct_orbitSet haG hJ
  have hAS : ∀ b ∈ Subgroup.zpowers a, ∀ K ∈ orbitSet (Subgroup.zpowers a) J,
      K.map (MulAut.conj b).toMonoidHom ∈ orbitSet (Subgroup.zpowers a) J :=
    fun b hb K hK => map_conj_mem_orbitSet hK hb
  have h := projIn_centralizer_eq hQ hAS (self_mem_orbitSet (Subgroup.zpowers a) J)
  rw [zpowers_inf_normalizer_eq_bot hp hap ha1 haJ] at h
  have hbot : Subgroup.centralizer ((⊥ : Subgroup Γ) : Set Γ) = ⊤ :=
    Subgroup.centralizer_eq_top_iff_subset.mpr (by simp)
  rw [hbot, inf_top_eq] at h
  exact h

theorem nonempty_mulEquiv_smear (hp : p.Prime) (haG : a ∈ Subgroup.normalizer (G : Set Γ))
    (hap : a ^ p = 1) (ha1 : a ≠ 1) (hJ : J ∈ lcal G)
    (haJ : a ∉ Subgroup.normalizer (J : Set Γ)) :
    Nonempty (↥(smear J (Subgroup.zpowers a)) ≃* ↥J) := by
  have hQ := isDirectProduct_orbitSet haG hJ
  have hAS : ∀ b ∈ Subgroup.zpowers a, ∀ K ∈ orbitSet (Subgroup.zpowers a) J,
      K.map (MulAut.conj b).toMonoidHom ∈ orbitSet (Subgroup.zpowers a) J :=
    fun b hb K hK => map_conj_mem_orbitSet hK hb
  have hJS := self_mem_orbitSet (Subgroup.zpowers a) J
  let ψ : ↥(smear J (Subgroup.zpowers a)) →* ↥J :=
    (hQ.coord hJS).comp (Subgroup.inclusion (smear_le_orbitClosure J (Subgroup.zpowers a)))
  refine ⟨MulEquiv.ofBijective ψ ⟨?_, ?_⟩⟩
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    have h1 : (y : Γ) ∈ sSup (orbitSet (Subgroup.zpowers a) J \ {J}) :=
      (hQ.coord_eq_one_iff hJS _).mp hy
    have h2 : (y : Γ) ∈ orbitClosure J (Subgroup.zpowers a) ⊓
        Subgroup.centralizer ((Subgroup.zpowers a : Subgroup Γ) : Set Γ) ⊓
          sSup (orbitSet (Subgroup.zpowers a) J \ {J}) :=
      Subgroup.mem_inf.mpr ⟨y.2, h1⟩
    rw [inf_centralizer_inf_sSup_eq_bot_of_transitive hQ hAS hJS (fun K hK => hK),
      Subgroup.mem_bot] at h2
    exact Subgroup.mem_bot.mpr (Subtype.ext h2)
  · rintro ⟨j, hj⟩
    have hj' : j ∈ projIn (orbitSet (Subgroup.zpowers a) J) J (smear J (Subgroup.zpowers a)) := by
      rw [projIn_smear_eq hp haG hap ha1 hJ haJ]
      exact hj
    obtain ⟨y, hy, hyj⟩ := (hQ.mem_projIn_iff hJS).mp hj'
    exact ⟨⟨y, hy⟩, Subtype.ext hyj⟩

theorem exists_diag_lift (hp : p.Prime) (haG : a ∈ Subgroup.normalizer (G : Set Γ))
    (hap : a ^ p = 1) (ha1 : a ≠ 1) (hJ : J ∈ lcal G)
    (haJ : a ∉ Subgroup.normalizer (J : Set Γ)) {j : Γ} (hj : j ∈ J) :
    ∃ l ∈ sSup (orbitSet (Subgroup.zpowers a) J \ {J}),
      j * l ∈ smear J (Subgroup.zpowers a) := by
  have hQ := isDirectProduct_orbitSet haG hJ
  have hj' : j ∈ projIn (orbitSet (Subgroup.zpowers a) J) J (smear J (Subgroup.zpowers a)) := by
    rw [projIn_smear_eq hp haG hap ha1 hJ haJ]
    exact hj
  obtain ⟨-, l, hl, hjl⟩ :=
    (mem_proj_iff (hQ.commute_sSup_diff (self_mem_orbitSet (Subgroup.zpowers a) J))).mp hj'
  exact ⟨l, hl, hjl⟩

theorem smear_le_kOf (hp : p.Prime) (haG : a ∈ Subgroup.normalizer (G : Set Γ)) (hap : a ^ p = 1)
    (ha1 : a ≠ 1) (hsol : sol G = ⊥) (hJ : J ∈ lcal G)
    (haJ : a ∉ Subgroup.normalizer (J : Set Γ)) :
    smear J (Subgroup.zpowers a) ≤ kOf (G ⊓ Subgroup.centralizer ({a} : Set Γ)) := by
  have hQ := isDirectProduct_orbitSet haG hJ
  have hK := isDirectProduct_lcal_kOf hsol
  have hSsub : orbitSet (Subgroup.zpowers a) J ⊆ lcal G :=
    orbitSet_subset_lcal (Subgroup.zpowers_le.mpr haG) hJ
  have hQK : orbitClosure J (Subgroup.zpowers a) ≤ kOf G := by
    rw [← hQ.sSup_eq]
    exact sSup_le fun K hK' => hK.le (hSsub hK')
  have hQn : ((orbitClosure J (Subgroup.zpowers a)).subgroupOf (kOf G)).Normal := by
    rw [← hQ.sSup_eq]
    exact normal_subgroupOf_sSup (fun K hK' => hK.le (hSsub hK'))
      (fun K hK' => hK.le_normalizer (hSsub hK'))
  have hsm : smear J (Subgroup.zpowers a) =
      orbitClosure J (Subgroup.zpowers a) ⊓ Subgroup.centralizer ({a} : Set Γ) := by
    unfold smear
    rw [centralizer_zpowers_eq]
  have hsub := isSubnormal_inf_centralizer hQK (kOf_le G) hQn (normal_kOf_subgroupOf G) {a}
  obtain ⟨e⟩ := nonempty_mulEquiv_smear hp haG hap ha1 hJ haJ
  obtain ⟨-, -, hs, hnc⟩ := mem_lcal_iff.mp hJ
  have : IsSimpleGroup J := hs
  have hD : smear J (Subgroup.zpowers a) ∈ lcal (G ⊓ Subgroup.centralizer ({a} : Set Γ)) := by
    refine mem_lcal_iff.mpr ⟨?_, ?_, e.isSimpleGroup,
      fun h => hnc ((isMulCommutative_congr e).mp h)⟩
    · rw [hsm]
      exact inf_le_inf_right _ (hQK.trans (kOf_le G))
    · rw [hsm]
      exact hsub
  exact le_kOf_of_mem_lcal hD

end Diag

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L511
