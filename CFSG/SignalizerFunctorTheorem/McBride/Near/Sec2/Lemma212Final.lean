module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma212Normal
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.PermutationAction

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma212

variable {Γ : Type*} [Group Γ] {p : ℕ} {A B G : Subgroup Γ}

theorem mem_normalizer_centralizer_of_mem {S : Set Γ} {g : Γ} (hg : g ∈ Subgroup.centralizer S) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer S : Set Γ) := by
  have key : ∀ {g : Γ}, g ∈ Subgroup.centralizer S → ∀ {h : Γ}, h ∈ Subgroup.centralizer S →
      g * h * g⁻¹ ∈ Subgroup.centralizer S := by
    intro g hg h hh
    rw [Subgroup.mem_centralizer_iff] at hg hh ⊢
    intro s hs
    have h1 : s * g = g * s := hg s hs
    have h2 : s * h = h * s := hh s hs
    have h3 : s * g⁻¹ = g⁻¹ * s := by
      calc s * g⁻¹ = g⁻¹ * (g * s) * g⁻¹ := by group
        _ = g⁻¹ * (s * g) * g⁻¹ := by rw [h1]
        _ = g⁻¹ * s := by group
    calc s * (g * h * g⁻¹) = (s * g) * h * g⁻¹ := by group
      _ = g * (s * h) * g⁻¹ := by rw [h1]; group
      _ = g * (h * s) * g⁻¹ := by rw [h2]
      _ = g * h * (s * g⁻¹) := by group
      _ = g * h * (g⁻¹ * s) := by rw [h3]
      _ = (g * h * g⁻¹) * s := by group
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key hg hh, fun hh => ?_⟩
  have := key (inv_mem hg) hh
  simpa [mul_assoc] using this

theorem mem_normalizer_cenIn {X : Subgroup Γ} {S : Set Γ} {g : Γ}
    (hX : g ∈ Subgroup.normalizer (X : Set Γ)) (hS : g ∈ Subgroup.centralizer S) :
    g ∈ Subgroup.normalizer (cenIn X S : Set Γ) :=
  Subgroup.inf_normalizer_le_normalizer_inf ⟨hX, mem_normalizer_centralizer_of_mem hS⟩

namespace GoodB

variable [Finite Γ] (H : Hyp p A G) (hB : GoodB A B G)

include H hB

omit [Finite Γ] in
theorem A_le_centralizer : A ≤ Subgroup.centralizer (B : Set Γ) := fun _ ha =>
  Subgroup.mem_centralizer_iff.mpr fun _ hb => H.comm (hB.le hb) ha

omit [Finite Γ] H in
theorem cenIn_le_cenIn : cenIn G A ≤ cenIn G B :=
  inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hB.le))

theorem not_isSolvable_cenIn : ¬ Group.IsSolvable ↥(cenIn (kOf G) B) := by
  obtain ⟨J, hJ⟩ := H.exists_lcal
  intro hs
  have : Group.IsSolvable ↥(kOf G ⊓ Subgroup.centralizer (B : Set Γ)) := hs
  exact not_isSolvable_smear H hB hJ (Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion (smear_le H hB hJ)) (Subgroup.inclusion_injective _))

theorem sup_eq : A ⊔ cenIn G B = A ⊔ cenIn G A ⊔ cenIn (kOf G) B := by
  refine le_antisymm ?_ (sup_le (sup_le le_sup_left
    (le_sup_of_le_right (cenIn_le_cenIn hB))) (le_sup_of_le_right (inf_le_inf_right _ (kOf_le G))))
  refine sup_le (le_sup_of_le_left le_sup_left) fun x hx => ?_
  obtain ⟨hxG, hxC⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨e, he, d, hd, rfl⟩ : x ∈ (layerIn G : Set Γ) * (cenIn G A : Set Γ) := H.prod ▸ hxG
  have hdC : d ∈ Subgroup.centralizer (B : Set Γ) := (cenIn_le_cenIn hB hd).2
  have heC : e ∈ Subgroup.centralizer (B : Set Γ) := by
    have : e = e * d * d⁻¹ := by group
    rw [this]
    exact mul_mem hxC (inv_mem hdC)
  rw [H.layerIn_eq] at he
  exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨he, heC⟩))
    (Subgroup.mem_sup_left (Subgroup.mem_sup_right hd))

theorem isChiefFactor : IsChiefFactorOf (A ⊔ cenIn G B) (cenIn (kOf G) B) ⊥ := by
  have hMC : cenIn (kOf G) B ≤ cenIn G B := inf_le_inf_right _ (kOf_le G)
  have hMH : cenIn (kOf G) B ≤ A ⊔ cenIn G B := le_sup_of_le_right hMC
  have hnormM : A ⊔ cenIn G B ≤ Subgroup.normalizer (cenIn (kOf G) B : Set Γ) := by
    refine sup_le (fun a ha => ?_) (fun c hc => ?_)
    · exact mem_normalizer_cenIn (H.A_le_normalizer ha) (A_le_centralizer H hB ha)
    · exact mem_normalizer_cenIn (H.G_le_normalizer (Subgroup.mem_inf.mp hc).1)
        (Subgroup.mem_inf.mp hc).2
  have hbot : A ⊔ cenIn G B ≤ Subgroup.normalizer ((⊥ : Subgroup Γ) : Set Γ) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  refine ⟨⟨bot_le, hbot⟩, ⟨hMH, hnormM⟩, ?_, ?_⟩
  · refine lt_of_le_of_ne bot_le fun h => ?_
    obtain ⟨J, hJ⟩ := H.exists_lcal
    have h1 : smear J B = ⊥ := le_bot_iff.mp ((smear_le H hB hJ).trans h.ge)
    exact not_isSolvable_smear H hB hJ (by rw [h1]; infer_instance)
  · intro N hN _ hNM
    by_cases hbot' : N = ⊥
    · exact Or.inl hbot'
    right
    have hNM' : N ≤ kOf G ⊓ Subgroup.centralizer (B : Set Γ) := hNM
    have hMnorm : kOf G ⊓ Subgroup.centralizer (B : Set Γ) ≤ Subgroup.normalizer (N : Set Γ) :=
      hMH.trans hN.2
    obtain ⟨J, hJ, hJN⟩ := exists_smear_le_of_normal H hB hNM' hMnorm hbot'
    have hall : ∀ J' ∈ lcal G, smear J' B ≤ N := by
      intro J' hJ'
      obtain ⟨a, ha, d, hd, rfl⟩ := H.transitive hJ hJ'
      have hdB : ∀ b ∈ B, b * d = d * b := fun b hb =>
        Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hd).2 b (hB.le hb)
      have hdJ : J.map (MulAut.conj d).toMonoidHom ∈ lcal G :=
        perm_lcal (Subgroup.le_normalizer (Subgroup.mem_inf.mp hd).1) hJ
      rw [← Thm210.map_conj_map_conj, smear_map_conj_of_mem H hB hdJ ha,
        ← smear_map_conj_of_commute J B hdB]
      have hdN : d ∈ Subgroup.normalizer (N : Set Γ) :=
        hN.2 (Subgroup.mem_sup_right (cenIn_le_cenIn hB hd))
      rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hdN y).mp (hJN hy)
    exact le_antisymm hNM ((kOf_inf_centralizer_le_iSup_smear H hB).trans (iSup₂_le hall))

theorem sol_cenIn_eq_bot : sol (cenIn G B) = ⊥ := by
  have hK := H.hK
  set C := cenIn G B with hCdef
  set R := sol C with hRdef
  set M := kOf G ⊓ Subgroup.centralizer (B : Set Γ) with hMdef
  have hCG : C ≤ G := inf_le_left
  have hRC : R ≤ C := sol_le C
  have hRG : R ≤ G := hRC.trans hCG
  have hMC : M ≤ C := inf_le_inf_right _ (kOf_le G)
  have hCR : C ≤ Subgroup.normalizer (R : Set Γ) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRC).mp (normal_sol_subgroupOf C)
  have hCM : C ≤ Subgroup.normalizer (M : Set Γ) := fun c hc =>
    mem_normalizer_cenIn (H.G_le_normalizer (hCG hc)) (Subgroup.mem_inf.mp hc).2
  have h1 : R ⊓ M = ⊥ := by
    by_contra hne
    obtain ⟨J, hJ, hJN⟩ := exists_smear_le_of_normal H hB (inf_le_right : R ⊓ M ≤ M)
      (fun m hm => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hCR (hMC hm), Subgroup.le_normalizer hm⟩) hne
    have : Group.IsSolvable ↥R := isSolvable_sol C
    exact not_isSolvable_smear H hB hJ (Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (hJN.trans inf_le_left)) (Subgroup.inclusion_injective _))
  have h2 : ∀ r ∈ R, ∀ m ∈ M, r * m = m * r := by
    intro r hr m hm
    have hmem : r * m * r⁻¹ * m⁻¹ ∈ R ⊓ M := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have h3 : m * r⁻¹ * m⁻¹ ∈ R :=
          (Subgroup.mem_normalizer_iff.mp (hCR (hMC hm)) r⁻¹).mp (inv_mem hr)
        have : r * m * r⁻¹ * m⁻¹ = r * (m * r⁻¹ * m⁻¹) := by group
        rw [this]
        exact mul_mem hr h3
      · have h3 : r * m * r⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp (hCM (hRC hr)) m).mp hm
        exact mul_mem h3 (inv_mem hm)
    rw [h1, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hmem
    exact hmem
  have hperm : ∀ r ∈ R, ∀ J' ∈ lcal G, J'.map (MulAut.conj r).toMonoidHom ∈ lcal G :=
    fun r hr J' hJ' => perm_lcal (Subgroup.le_normalizer (hRG hr)) hJ'
  have key : ∀ (r : Γ) (hr : r ∈ R) (J : Subgroup Γ) (hJ : J ∈ lcal G) (j : Γ), j ∈ J →
      ∃ xk : ↥(kOf G), (xk : Γ) ∈ smear J B ∧ ((hK.coord hJ xk : ↥J) : Γ) = j ∧
        ((hK.coord (hperm r hr J hJ) xk : ↥(J.map (MulAut.conj r).toMonoidHom)) : Γ) =
          r * j * r⁻¹ := by
    intro r hr J hJ j hj
    have hjP : j ∈ projIn (lcal G) J (smear J B) := by
      rw [projIn_smear H hB hJ]
      exact hj
    obtain ⟨xk, hxk, hxkj⟩ := (hK.mem_projIn_iff hJ).mp hjP
    have hxM := smear_le H hB hJ hxk
    have hrx : r * (xk : Γ) = (xk : Γ) * r := h2 r hr _ hxM
    have h3 := hK.coord_conj (hperm r hr) hJ xk.2
    have hxk' : (⟨r * (xk : Γ) * r⁻¹, hK.conj_mem (hperm r hr) xk.2⟩ : ↥(kOf G)) = xk :=
      Subtype.ext (show r * (xk : Γ) * r⁻¹ = (xk : Γ) by rw [hrx]; group)
    have h4 := congrArg (fun y => (((hK.coord (hperm r hr J hJ)) y : ↥(J.map
      (MulAut.conj r).toMonoidHom)) : Γ)) hxk'
    refine ⟨xk, hxk, hxkj, ?_⟩
    rw [← h4, h3]
    exact congrArg (fun t : Γ => r * t * r⁻¹) hxkj
  have claim1 : ∀ r ∈ R, ∀ J ∈ lcal G, ∃ a ∈ A,
      J.map (MulAut.conj r).toMonoidHom = J.map (MulAut.conj a).toMonoidHom := by
    intro r hr J hJ
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨j, hj⟩, hj1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (ne_bot_of_mem_lcal hJ)
    obtain ⟨xk, hxk, -, h5⟩ := key r hr J hJ j hj
    have h6 : hK.coord (hperm r hr J hJ) xk = 1 :=
      (hK.coord_eq_one_iff _ xk).mpr (smear_le_sSup H hB hJ hcon hxk)
    rw [h6] at h5
    apply hj1
    refine Subtype.ext ?_
    have h7 : r * j * r⁻¹ = 1 := h5.symm
    calc j = r⁻¹ * (r * j * r⁻¹) * r := by group
      _ = 1 := by rw [h7]; group
  have hRcop : Nat.Coprime p (Nat.card R) :=
    H.coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hRG)
  have hAC : A ≤ Subgroup.normalizer (C : Set Γ) := fun a ha =>
    mem_normalizer_cenIn (H.near.admits ha) (A_le_centralizer H hB ha)
  have hAR : A ≤ Subgroup.normalizer (R : Set Γ) := fun a ha =>
    normalizer_le_normalizer_sol C (hAC ha)
  have claim2 : ∀ J ∈ lcal G, R ≤ Subgroup.normalizer (J : Set Γ) := by
    intro J hJ r hr
    have hΩ : ∀ g ∈ R ⊔ A, ∀ J' ∈ {K | ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom},
        J'.map (MulAut.conj g).toMonoidHom ∈
          {K | ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom} := by
      refine fun g hg => map_conj_mem_of_mem_sup (X := R) (Y := A) ?_ ?_ hg
      · rintro g' hg' _ ⟨a, ha, rfl⟩
        obtain ⟨a', ha', h⟩ := claim1 g' hg' _ (H.A_perm_lcal ha hJ)
        refine ⟨a' * a, mul_mem ha' ha, ?_⟩
        rw [h, Thm210.map_conj_map_conj]
      · rintro g' hg' _ ⟨a, ha, rfl⟩
        exact ⟨g' * a, mul_mem hg' ha, Thm210.map_conj_map_conj J a g'⟩
    have htrans : ∀ J₁ ∈ {K | ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom},
        ∀ J₂ ∈ {K | ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom},
          ∃ a ∈ A, J₂ = J₁.map (MulAut.conj a).toMonoidHom := by
      rintro _ ⟨a₁, ha₁, rfl⟩ _ ⟨a₂, ha₂, rfl⟩
      refine ⟨a₂ * a₁⁻¹, mul_mem ha₂ (inv_mem ha₁), ?_⟩
      rw [Thm210.map_conj_map_conj, mul_assoc, inv_mul_cancel, mul_one]
    exact normalizes_of_isPGroup_transitive_conj H.near.prime H.isPGroup hRcop hAR hΩ htrans r hr J
      ⟨1, one_mem A, (Thm210.map_conj_one J).symm⟩
  have claim3 : ∀ r ∈ R, ∀ J ∈ lcal G, ∀ j ∈ J, j * r = r * j := by
    intro r hr J hJ j hj
    obtain ⟨xk, -, hxkj, h5⟩ := key r hr J hJ j hj
    have hJr : J.map (MulAut.conj r).toMonoidHom = J :=
      (mem_normalizer_iff_map_conj J r).mp (claim2 J hJ hr)
    have h6 := hK.coord_val_congr (hperm r hr J hJ) hJ hJr xk
    rw [h6, hxkj] at h5
    calc j * r = r * j * r⁻¹ * r := by rw [← h5]
      _ = r * j := by group
  rw [eq_bot_iff]
  intro r hr
  have hrC : r ∈ Subgroup.centralizer (kOf G : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have : kOf G ≤ Subgroup.centralizer ({r} : Set Γ) := by
      rw [← hK.sSup_eq]
      refine sSup_le fun J hJ j hj => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact claim3 r hr J hJ j hj
    exact Subgroup.mem_centralizer_singleton_iff.mp (this hk)
  have hmem : r ∈ G ⊓ Subgroup.centralizer (kOf G : Set Γ) := Subgroup.mem_inf.mpr ⟨hRG hr, hrC⟩
  rw [centralizer_kOf_eq_bot H.sol_eq] at hmem
  exact hmem

end GoodB

end CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma212
