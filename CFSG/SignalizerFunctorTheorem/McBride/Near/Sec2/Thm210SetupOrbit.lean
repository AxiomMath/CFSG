module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210Aux2
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210Setup

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

open Thm210

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A G J : Subgroup Γ}

omit [Finite Γ] in
theorem Thm210.orbitClosure_map_conj (J : Subgroup Γ) {a : Γ} (ha : a ∈ A) :
    orbitClosure (J.map (MulAut.conj a).toMonoidHom) A = orbitClosure J A := by
  refine le_antisymm (orbitClosure_le fun c hc => ?_) (orbitClosure_le fun c hc => ?_)
  · rw [map_conj_map_conj]
    exact map_conj_le_orbitClosure J (mul_mem hc ha)
  · have : J.map (MulAut.conj c).toMonoidHom =
        (J.map (MulAut.conj a).toMonoidHom).map (MulAut.conj (c * a⁻¹)).toMonoidHom := by
      rw [map_conj_map_conj, inv_mul_cancel_right]
    rw [this]
    exact map_conj_le_orbitClosure _ (mul_mem hc (inv_mem ha))

theorem SemisimpleAction.commute_orbitClosure (h : SemisimpleAction p A G) {J₁ J₂ : Subgroup Γ}
    (h₁ : J₁ ∈ lcal G) (h₂ : J₂ ∈ lcal G) (hne : orbitClosure J₁ A ≠ orbitClosure J₂ A) :
    ∀ x ∈ orbitClosure J₁ A, ∀ y ∈ orbitClosure J₂ A, x * y = y * x := by
  have hG := h.isDirectProduct_lcal
  have key : ∀ a ∈ A, ∀ b ∈ A, ∀ x ∈ J₁.map (MulAut.conj a).toMonoidHom,
      ∀ y ∈ J₂.map (MulAut.conj b).toMonoidHom, x * y = y * x := by
    intro a ha b hb x hx y hy
    have hne' : J₁.map (MulAut.conj a).toMonoidHom ≠ J₂.map (MulAut.conj b).toMonoidHom := by
      intro heq
      apply hne
      rw [← orbitClosure_map_conj J₁ ha, heq, orbitClosure_map_conj J₂ hb]
    exact hG.commute _ (h.permutes_lcal a ha J₁ h₁) _ (h.permutes_lcal b hb J₂ h₂) hne' x hx y hy
  have h1 : ∀ a ∈ A, orbitClosure J₂ A ≤
      Subgroup.centralizer ((J₁.map (MulAut.conj a).toMonoidHom : Subgroup Γ) : Set Γ) := by
    intro a ha
    refine orbitClosure_le fun b hb y hy => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact key a ha b hb x hx y hy
  have h2 : orbitClosure J₁ A ≤ Subgroup.centralizer (orbitClosure J₂ A : Set Γ) := by
    refine orbitClosure_le fun a ha x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (h1 a ha hy) x hx).symm
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.mp (h2 hx) y hy).symm

omit [Finite Γ] in
theorem Thm210.admits_orbitClosure (J : Subgroup Γ) :
    A ≤ Subgroup.normalizer (orbitClosure J A : Set Γ) := by
  refine le_normalizer_of_conj_mem fun a ha x hx => ?_
  have hle : orbitClosure J A ≤ (orbitClosure J A).comap (MulAut.conj a).toMonoidHom := by
    refine orbitClosure_le fun b hb y hy => ?_
    have : (J.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom ≤
        orbitClosure J A := by
      rw [map_conj_map_conj]
      exact map_conj_le_orbitClosure J (mul_mem ha hb)
    exact this ⟨y, hy, rfl⟩
  exact hle hx

theorem SemisimpleAction.isDirectProduct_orbitClosure (h : SemisimpleAction p A G) :
    IsDirectProduct {K | ∃ J ∈ lcal G, K = orbitClosure J A} G where
  commute := by
    rintro _ ⟨J₁, h₁, rfl⟩ _ ⟨J₂, h₂, rfl⟩ hne x hx y hy
    exact (h.commute_orbitClosure h₁ h₂ hne x hx y hy)
  indep := by
    rintro _ ⟨J, hJ, rfl⟩
    have hG := h.isDirectProduct_lcal
    have hO : ∀ J' ∈ lcal G, IsDirectProduct
        {K | ∃ a ∈ A, K = J'.map (MulAut.conj a).toMonoidHom} (orbitClosure J' A) :=
      fun J' hJ' => isDirectProduct_orbit h.admits hJ'
    have hOS : ∀ J' ∈ lcal G,
        {K | ∃ a ∈ A, K = J'.map (MulAut.conj a).toMonoidHom} ⊆ lcal G := by
      rintro J' hJ' _ ⟨a, ha, rfl⟩
      exact h.permutes_lcal a ha J' hJ'
    have h1 : orbitClosure J A ≤ sSup {K | ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom} :=
      (hO J hJ).sSup_eq.symm.le
    have h2 : Disjoint (sSup {K | ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom})
        (sSup (lcal G \ {K | ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom})) :=
      disjoint_sSup_sSup hG (hOS J hJ) Set.sdiff_subset Set.disjoint_sdiff_right
    refine Disjoint.mono h1 (sSup_le ?_) h2
    rintro _ ⟨⟨J', hJ', rfl⟩, hne⟩
    rw [← (hO J' hJ').sSup_eq]
    refine sSup_le_sSup fun X hX => ⟨hOS J' hJ' hX, fun hXO => hne ?_⟩
    obtain ⟨a, ha, rfl⟩ := hX
    obtain ⟨b, hb, hab⟩ := hXO
    show orbitClosure J' A = orbitClosure J A
    rw [← orbitClosure_map_conj J' ha, hab, orbitClosure_map_conj J hb]
  sSup_eq := by
    have hG := h.isDirectProduct_lcal
    refine le_antisymm (sSup_le ?_) (hG.sSup_eq.symm.le.trans (sSup_le fun J hJ => ?_))
    · rintro _ ⟨J, hJ, rfl⟩
      exact orbitClosure_le fun a ha => lcal_le (h.permutes_lcal a ha J hJ)
    · exact (le_orbitClosure J A).trans (le_sSup ⟨J, hJ, rfl⟩)

theorem SemisimpleAction.isDirectProduct_smear (h : SemisimpleAction p A G) :
    IsDirectProduct {X | ∃ J ∈ lcal G, X = smear J A} (cenIn G A) := by
  have hG' := h.isDirectProduct_orbitClosure
  have himg := isDirectProduct_image hG' (fun K => K ⊓ Subgroup.centralizer (A : Set Γ))
    fun K _ => inf_le_left
  have hset : {X | ∃ K ∈ {K | ∃ J ∈ lcal G, K = orbitClosure J A},
      X = K ⊓ Subgroup.centralizer (A : Set Γ)} = {X | ∃ J ∈ lcal G, X = smear J A} := by
    ext X
    constructor
    · rintro ⟨_, ⟨J, hJ, rfl⟩, rfl⟩
      exact ⟨J, hJ, rfl⟩
    · rintro ⟨J, hJ, rfl⟩
      exact ⟨_, ⟨J, hJ, rfl⟩, rfl⟩
  have hA' : ∀ a ∈ A, ∀ K ∈ {K | ∃ J ∈ lcal G, K = orbitClosure J A},
      K.map (MulAut.conj a).toMonoidHom ∈ {K | ∃ J ∈ lcal G, K = orbitClosure J A} := by
    rintro a ha _ ⟨J, hJ, rfl⟩
    refine ⟨J, hJ, ?_⟩
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (admits_orbitClosure J ha)
  have hsup : sSup {X | ∃ K ∈ {K | ∃ J ∈ lcal G, K = orbitClosure J A},
      X = K ⊓ Subgroup.centralizer (A : Set Γ)} = cenIn G A := by
    refine le_antisymm (sSup_le ?_) ?_
    · rintro _ ⟨K, ⟨J, hJ, rfl⟩, rfl⟩
      exact inf_le_inf_right _
        (orbitClosure_le fun a ha => lcal_le (h.permutes_lcal a ha J hJ))
    · refine (le_sSup_image_iff hG' (T := fun K => K ⊓ Subgroup.centralizer (A : Set Γ))
        fun K _ => inf_le_left).mpr ⟨inf_le_left, ?_⟩
      rintro _ ⟨J, hJ, rfl⟩
      have hAN : A ≤ Subgroup.normalizer (orbitClosure J A : Set Γ) := admits_orbitClosure J
      have hproj := projIn_centralizer_eq hG' hA' (J := orbitClosure J A) ⟨J, hJ, rfl⟩
      rw [inf_eq_left.mpr hAN] at hproj
      exact hproj.le
  rw [hset] at himg hsup
  rw [hsup] at himg
  exact himg

omit [Finite Γ] in
theorem Thm210.isSemisimple_of_isDirectProduct {S : Set (Subgroup Γ)} {L : Subgroup Γ}
    (hL : IsDirectProduct S L)
    (hS : ∀ K ∈ S, IsSimpleGroup K ∧ ∃ x ∈ K, ∃ y ∈ K, x * y ≠ y * x) : IsSemisimple L := by
  have hsc : CFSG.SignalizerFunctorTheorem.Nonsolvable.simpleComponents L = S := by
    ext T
    constructor
    · rintro ⟨hTL, hTn, hTs, x, hx, y, hy, hxy⟩
      by_contra hTS
      have hTnorm : ∀ u ∈ T, ∀ v ∈ L, v * u * v⁻¹ ∈ T := fun u hu v hv =>
        (Subgroup.normal_subgroupOf_iff hTL).mp hTn u v hu hv
      have hcomm : ∀ K ∈ S, ∀ u ∈ T, ∀ k ∈ K, u * k = k * u := by
        intro K hK u hu k hk
        obtain ⟨hKs, x₀, hx₀, y₀, hy₀, hxy₀⟩ := hS K hK
        have hKL : K ≤ L := hL.le hK
        have hLK : L ≤ Subgroup.normalizer (K : Set Γ) := hL.le_normalizer hK
        have hKT : ¬ K ≤ T := by
          intro hKT
          have hKnormT : (K.subgroupOf T).Normal :=
            (Subgroup.normal_subgroupOf_iff_le_normalizer hKT).mpr (hTL.trans hLK)
          rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.subgroupOf T) with hb | ht
          · apply hxy₀
            have hK1 : K = ⊥ := by
              rw [eq_bot_iff]
              intro z hz
              have : (⟨z, hKT hz⟩ : ↥T) ∈ K.subgroupOf T := hz
              rw [hb, Subgroup.mem_bot] at this
              exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
            rw [hK1, Subgroup.mem_bot] at hx₀ hy₀
            rw [hx₀, hy₀]
          · apply hTS
            have hTK : T ≤ K := fun z hz => by
              have : (⟨z, hz⟩ : ↥T) ∈ K.subgroupOf T := by rw [ht]; trivial
              exact this
            exact (le_antisymm hTK hKT |>.symm ▸ hK : T ∈ S)
        have hnormTK : ((T ⊓ K).subgroupOf K).Normal := by
          rw [Subgroup.normal_subgroupOf_iff inf_le_right]
          intro a b ha hb
          obtain ⟨haT, haK⟩ := Subgroup.mem_inf.mp ha
          exact Subgroup.mem_inf.mpr ⟨hTnorm a haT b (hKL hb),
            mul_mem (mul_mem hb haK) (inv_mem hb)⟩
        have hbot : T ⊓ K = ⊥ := by
          rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((T ⊓ K).subgroupOf K) with hb | ht
          · rw [eq_bot_iff]
            intro z hz
            have : (⟨z, (Subgroup.mem_inf.mp hz).2⟩ : ↥K) ∈ (T ⊓ K).subgroupOf K := hz
            rw [hb, Subgroup.mem_bot] at this
            exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
          · exfalso
            apply hKT
            intro z hz
            have : (⟨z, hz⟩ : ↥K) ∈ (T ⊓ K).subgroupOf K := by rw [ht]; trivial
            exact (Subgroup.mem_inf.mp this).1
        have hmem : u * k * u⁻¹ * k⁻¹ ∈ T ⊓ K := by
          refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
          · have h1 := mul_mem hu (hTnorm u⁻¹ (inv_mem hu) k (hKL hk))
            simpa [mul_assoc] using h1
          · exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hLK (hTL hu)) k).mp hk) (inv_mem hk)
        rw [hbot, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hmem
        exact hmem
      have hLT : L ≤ Subgroup.centralizer (T : Set Γ) := by
        rw [← hL.sSup_eq]
        refine sSup_le fun K hK k hk => ?_
        rw [Subgroup.mem_centralizer_iff]
        exact fun u hu => hcomm K hK u hu k hk
      exact hxy (Subgroup.mem_centralizer_iff.mp (hLT (hTL hy)) x hx)
    · intro hT
      obtain ⟨hTs, hTnc⟩ := hS T hT
      exact ⟨hL.le hT, (Subgroup.normal_subgroupOf_iff_le_normalizer (hL.le hT)).mpr
        (hL.le_normalizer hT), hTs, hTnc⟩
  unfold IsSemisimple
  rw [hsc]
  exact hL

theorem SemisimpleAction.orbit (h : SemisimpleAction p A G) (hJ : J ∈ lcal G) :
    SemisimpleAction p A (orbitClosure J A) := by
  have hle : orbitClosure J A ≤ G :=
    orbitClosure_le fun a ha => lcal_le (h.permutes_lcal a ha J hJ)
  obtain ⟨hJG, -, -, hnc⟩ := mem_lcal_iff.mp hJ
  have hle2 : cenIn (orbitClosure J A) A ≤ cenIn G A := inf_le_inf_right _ hle
  have hsol : Group.IsSolvable ↥(cenIn (orbitClosure J A) A) := by
    have := h.solvable_cen
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle2)
  refine ⟨⟨⟨h.prime, h.odd, h.elemAbelian, admits_orbitClosure J,
    signalizerNearPSolvable_of_le hle h.nearPSolvable⟩, hsol⟩, ?_, ?_⟩
  · refine isSemisimple_of_isDirectProduct (isDirectProduct_orbit h.admits hJ) ?_
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨-, -, hs, hnc'⟩ := mem_lcal_iff.mp (h.permutes_lcal a ha J hJ)
    obtain ⟨u, v, huv⟩ := exists_mul_ne_of_not_isMulCommutative hnc'
    exact ⟨hs, u, u.2, v, v.2, fun he => huv (Subtype.ext he)⟩
  · intro hbot
    apply hnc
    have : J = ⊥ := le_bot_iff.mp ((le_orbitClosure J A).trans hbot.le)
    rw [this]
    infer_instance

omit [Finite Γ] in
theorem Thm210.cenIn_orbitClosure (J A : Subgroup Γ) : cenIn (orbitClosure J A) A = smear J A :=
  rfl

end CFSG.SignalizerFunctorTheorem.McBride.Near
