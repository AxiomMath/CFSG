module

public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Background.Equivariance
public import CFSG.Quasithin.Background.B1Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

universe u

variable {G : Type u} [Group G]

section Sylow

variable [Finite G] {H T : Subgroup G}

theorem isSylowTwoOf_of_sylow (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H) :
    IsSylowTwoOf (T : Subgroup G) H :=
  ⟨hTH, T.isPGroup', fun h => T.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le hTH))⟩

theorem exists_conj_le_of_isSylowTwoOf {A : Subgroup G} (hT : IsSylowTwoOf T H) (hAH : A ≤ H)
    (hA : IsPGroup 2 A) : ∃ h ∈ H, cjSub h A ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T' : Sylow 2 H :=
    (hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm).toSylow hT.2.2
  have hA' : IsPGroup 2 (A.subgroupOf H) :=
    hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAH).symm
  obtain ⟨Q, hQ⟩ := hA'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H T' Q
  refine ⟨((g⁻¹ : H) : G), (g⁻¹).2, fun x hx => ?_⟩
  have hxA : (g : G) * x * (g : G)⁻¹ ∈ A := by simpa using mem_cjSub.1 hx
  have hxH : x ∈ H := by
    have h := H.mul_mem (H.mul_mem (H.inv_mem g.2) (hAH hxA)) g.2
    simpa [mul_assoc] using h
  have h1 : (⟨(g : G) * x * (g : G)⁻¹, hAH hxA⟩ : H) ∈ (Q : Subgroup H) :=
    hQ (Subgroup.mem_subgroupOf.2 hxA)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
  have h4 : ((MulAut.conj g)⁻¹ • (⟨(g : G) * x * (g : G)⁻¹, hAH hxA⟩ : H)) = ⟨x, hxH⟩ := by
    apply Subtype.ext
    simp [MulAut.smul_def, mul_assoc]
  rw [h4] at h1
  simp only [T', IsPGroup.toSylow_coe] at h1
  exact Subgroup.mem_subgroupOf.1 h1

theorem isMaxElemAbelian_of_isSylowTwoOf {A : Subgroup G} (hT : IsSylowTwoOf T H)
    (hA : IsMaxElemAbelian T A) : IsMaxElemAbelian H A := by
  refine ⟨hA.1.trans hT.1, hA.2.1, fun B hBH hB => ?_⟩
  obtain ⟨h, -, hle⟩ := exists_conj_le_of_isSylowTwoOf hT hBH (B2F.isPGroup_of_isElemAbelian hB)
  have := hA.2.2 (cjSub h B) hle (isElemAbelian_cjSub hB)
  rwa [card_cjSub] at this

theorem exists_conj_isMaxElemAbelian {A : Subgroup G} (hT : IsSylowTwoOf T H)
    (hA : IsMaxElemAbelian H A) : ∃ h ∈ H, IsMaxElemAbelian T (cjSub h A) := by
  obtain ⟨h, hh, hle⟩ :=
    exists_conj_le_of_isSylowTwoOf hT hA.1 (B2F.isPGroup_of_isElemAbelian hA.2.1)
  refine ⟨h, hh, hle, isElemAbelian_cjSub hA.2.1, fun B hBT hB => ?_⟩
  rw [card_cjSub]
  exact hA.2.2 B (hBT.trans hT.1) hB

theorem thompsonJ_le_thompsonJ_of_isSylowTwoOf (hT : IsSylowTwoOf T H) :
    thompsonJ T ≤ thompsonJ H :=
  iSup_le fun _ => iSup_le fun hA =>
    le_iSup₂_of_le _ (isMaxElemAbelian_of_isSylowTwoOf hT hA) le_rfl

theorem thompsonJ_le_of_normalizer {N : Subgroup G} (hT : IsSylowTwoOf T H)
    (hNH : H ≤ Subgroup.normalizer (N : Set G)) (hJ : thompsonJ T ≤ N) : thompsonJ H ≤ N := by
  refine iSup_le fun A => iSup_le fun hA => ?_
  obtain ⟨h, hh, hAT⟩ := exists_conj_isMaxElemAbelian hT hA
  intro x hx
  have h1 : h * x * h⁻¹ ∈ cjSub h A := by
    rw [mem_cjSub]
    simpa [mul_assoc] using hx
  have h2 : h * x * h⁻¹ ∈ N :=
    hJ ((le_iSup₂_of_le (cjSub h A) hAT le_rfl : cjSub h A ≤ thompsonJ T) h1)
  exact (Subgroup.mem_normalizer_iff.1 (hNH hh) x).2 h2

end Sylow

section ThompsonConj

variable {S R : Subgroup G}

theorem cjSub_thompsonJ_le {g : G} (hg : g ∈ Subgroup.normalizer (S : Set G)) :
    cjSub g (thompsonJ S) ≤ thompsonJ S := by
  unfold cjSub
  rw [thompsonJ, Subgroup.map_iSup]
  refine iSup_le fun A => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hA => ?_
  exact le_iSup₂_of_le _ (isMaxElemAbelian_cjSub hg hA) le_rfl

theorem cjSub_thompsonJ {g : G} (hg : g ∈ Subgroup.normalizer (S : Set G)) :
    cjSub g (thompsonJ S) = thompsonJ S := by
  refine le_antisymm (cjSub_thompsonJ_le hg) ?_
  have h := cjSub_mono (g := g) (cjSub_thompsonJ_le (inv_mem hg))
  rwa [cjSub_cjSub_inv] at h

variable [Finite G]

theorem thompsonJ_eq_of_le (hJ : thompsonJ S ≤ R) (hRS : R ≤ S) :
    thompsonJ S = thompsonJ R := by
  by_cases h : 0 < Open.pRank 2 S
  · rw [thompsonJ_eq_thompsonJi_zero, thompsonJ_eq_thompsonJi_zero]
    exact thompsonJi_eq_of_le h (by rwa [← thompsonJ_eq_thompsonJi_zero]) hRS
  · obtain ⟨B, hB⟩ := exists_isMaxElemAbelian S
    have hB1 : Nat.card B = 1 := by
      have := (isMaxElemAbelian_iff_corank_zero.1 hB).2.2
      rw [Nat.eq_zero_of_not_pos h] at this
      simpa using this
    have hbot : ∀ K : Subgroup G, K ≤ S → ∀ A, IsMaxElemAbelian K A → A = ⊥ := by
      intro K hK A hA
      have := hB.2.2 A (hA.1.trans hK) hA.2.1
      rw [hB1] at this
      exact Subgroup.card_eq_one.1 (le_antisymm this Nat.card_pos)
    have h1 : thompsonJ S = ⊥ :=
      eq_bot_iff.2 (iSup_le fun A => iSup_le fun hA => (hbot S le_rfl A hA).le)
    have h2 : thompsonJ R = ⊥ :=
      eq_bot_iff.2 (iSup_le fun A => iSup_le fun hA => (hbot R hRS A hA).le)
    rw [h1, h2]

end ThompsonConj

section Offenders

variable [Finite G] {V H : Subgroup G} (hV : IsElemAbelian 2 V)

@[expose] def offenderImages (H : Subgroup G) : Set (Subgroup (MulAut (IntMod V hV))) :=
  {B | ∃ A : Subgroup G, IsFFOffender H V A ∧ B = autI hV A}

omit [Finite G] in
theorem mem_offenderImages {B : Subgroup (MulAut (IntMod V hV))} :
    B ∈ offenderImages hV H ↔ ∃ A : Subgroup G, IsFFOffender H V A ∧ B = autI hV A := Iff.rfl

theorem offender_core (hVH : V ≤ H) (hHN : H ≤ Subgroup.normalizer (V : Set G)) {A : Subgroup G}
    (hA : IsMaxElemAbelian H A) {B : Subgroup (MulAut (IntMod V hV))} (hB : B ≤ autI hV A) :
    Nat.card B * Nat.card (fixV B) ≤ Nat.card (autI hV A) * Nat.card (fixV (autI hV A)) ∧
      (Nat.card B * Nat.card (fixV B) = Nat.card (autI hV A) * Nat.card (fixV (autI hV A)) →
        IsMaxElemAbelian H (preI hV A (hA.1.trans hHN) B ⊔
            (V ⊓ Subgroup.centralizer (preI hV A (hA.1.trans hHN) B : Set G))) ∧
          autI hV (preI hV A (hA.1.trans hHN) B ⊔
            (V ⊓ Subgroup.centralizer (preI hV A (hA.1.trans hHN) B : Set G))) = B) := by
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hA.1.trans hHN
  set B₀ := preI hV A hAN B with hB₀
  have hB₀A : B₀ ≤ A := preI_le hV
  have hB₀N : B₀ ≤ Subgroup.normalizer (V : Set G) := hB₀A.trans hAN
  have hB₀e : IsElemAbelian 2 B₀ := B2F.isElemAbelian_mono hB₀A hA.2.1
  set C := V ⊓ Subgroup.centralizer (B₀ : Set G) with hC
  have hCV : C ≤ V := inf_le_left
  have hCe : IsElemAbelian 2 C := B2F.isElemAbelian_mono hCV hV
  have hcomm : ∀ b ∈ B₀, ∀ c ∈ C, b * c = c * b := fun b hb c hc =>
    Subgroup.mem_centralizer_iff.1 hc.2 b hb
  set D := B₀ ⊔ C with hD
  have hDe : IsElemAbelian 2 D := B2F.isElemAbelian_sup_of_commute hB₀e hCe hcomm
  have hDH : D ≤ H := sup_le (hB₀A.trans hA.1) (hCV.trans hVH)
  have hcard : Nat.card D * Nat.card ↥(B₀ ⊓ C) = Nat.card B₀ * Nat.card C :=
    B2F.card_sup_mul_card_inf_of_commute hcomm
  have hinf : B₀ ⊓ C = A ⊓ V := by
    apply le_antisymm
    · intro x hx
      exact ⟨hB₀A hx.1, hx.2.1⟩
    · intro x hx
      refine ⟨inf_centralizer_le_preI hV ⟨hx.1, B2F.le_centralizer_self hV hx.2⟩, hx.2, ?_⟩
      exact Subgroup.mem_centralizer_iff.2 fun b hb => B2F.isElemAbelian_comm hA.2.1 (hB₀A hb) hx.1
  rw [hinf] at hcard
  have hcardB₀ : Nat.card B₀ = Nat.card B * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) :=
    card_preI hV hB
  have hautB₀ : autI hV B₀ = B := autI_preI hV hB
  have hfB : Nat.card (fixV B) = Nat.card C := by
    have := card_fixV_autI hV hB₀N
    rwa [hautB₀] at this
  have hfA : Nat.card (fixV (autI hV A)) = Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) :=
    card_fixV_autI hV hAN
  have hAA : Nat.card (autI hV A) * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) =
      Nat.card A := card_autI_mul_card_inf hV hAN
  have hDA : Nat.card D ≤ Nat.card A := hA.2.2 D hDH hDe
  have hi : Nat.card ↥(A ⊓ V) ≤ Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := by
    refine Subgroup.card_le_of_le fun x hx => ⟨hx.2, ?_⟩
    exact Subgroup.mem_centralizer_iff.2 fun a ha => B2F.isElemAbelian_comm hA.2.1 ha hx.1
  have hcpos : 0 < Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := Nat.card_pos
  have hipos : 0 < Nat.card ↥(A ⊓ V) := Nat.card_pos
  rw [hcardB₀, ← hfB] at hcard
  rw [hfA]
  set k := Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) with hk
  set i := Nat.card ↥(A ⊓ V) with hi'
  set fA := Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) with hfA'
  set b := Nat.card B with hb
  set fB := Nat.card (fixV B) with hfB'
  set d := Nat.card D with hd
  set a := Nat.card A with ha
  set aS := Nat.card (autI hV A) with haS
  have hmain : d * i = b * k * fB := by rw [hcard]
  refine ⟨?_, fun heq => ?_⟩
  · refine Nat.le_of_mul_le_mul_right ?_ hcpos
    calc b * fB * k = d * i := by rw [hmain]; ring
      _ ≤ a * i := Nat.mul_le_mul_right _ hDA
      _ = aS * k * i := by rw [← hAA]
      _ ≤ aS * k * fA := Nat.mul_le_mul_left _ hi
      _ = aS * fA * k := by ring
  · have h1 : d * i = a * fA := by
      calc d * i = b * k * fB := hmain
        _ = k * (b * fB) := by ring
        _ = k * (aS * fA) := by rw [heq]
        _ = aS * k * fA := by ring
        _ = a * fA := by rw [hAA]
    have h2 : a * i ≤ a * fA := Nat.mul_le_mul_left _ hi
    have h3 : d * i ≤ a * i := Nat.mul_le_mul_right _ hDA
    have h4 : d * i = a * i := le_antisymm h3 (by omega)
    have hdA : d = a := Nat.eq_of_mul_eq_mul_right hipos h4
    refine ⟨⟨hDH, hDe, fun B' hB'H hB' => ?_⟩, ?_⟩
    · exact (hA.2.2 B' hB'H hB').trans (le_of_eq hdA.symm)
    · have hCN : C ≤ Subgroup.normalizer (V : Set G) := hCV.trans (hVH.trans hHN)
      rw [hD, autI_sup hV hB₀N hCN, hautB₀,
        autI_eq_bot_of_le_centralizer hV (hCV.trans (B2F.le_centralizer_self hV)), sup_bot_eq]

theorem offenderImages_isFFStarOffender (hVH : V ≤ H) (hHN : H ≤ Subgroup.normalizer (V : Set G))
    {B : Subgroup (MulAut (IntMod V hV))} (hB : B ∈ offenderImages hV H) :
    IsFFStarOffender (autI hV H) B := by
  obtain ⟨A, hA, rfl⟩ := hB
  have h2 := isA2_autI hV hHN hA.1.1 hA.1.2.1 hA.2
  exact ⟨h2.1, h2.2.1, h2.2.2, fun B' hB' => (offender_core hV hVH hHN hA.1 hB').1⟩

omit [Finite G] in
theorem offenderImages_conj
    {B : Subgroup (MulAut (IntMod V hV))} (hB : B ∈ offenderImages hV H)
    {g : MulAut (IntMod V hV)} (hg : g ∈ autI hV H) :
    B.map (MulAut.conj g).toMonoidHom ∈ offenderImages hV H := by
  obtain ⟨A, hA, rfl⟩ := hB
  obtain ⟨h, hh, rfl⟩ := (mem_autI hV).1 hg
  exact ⟨cjSub h A, ⟨isMaxElemAbelian_cjSub (Subgroup.le_normalizer hh) hA.1,
    not_cjSub_le_centralizer h.2 hA.2⟩, (autI_cjSub hV h.2 A).symm ▸ rfl⟩

theorem offenderImages_ffLe (hVH : V ≤ H) (hHN : H ≤ Subgroup.normalizer (V : Set G))
    {A : Subgroup G} (hA : IsFFOffender H V A) {B : Subgroup (MulAut (IntMod V hV))}
    (hB : FFLe (autI hV H) B (autI hV A)) : B ∈ offenderImages hV H := by
  obtain ⟨hD, hDB⟩ := (offender_core hV hVH hHN hA.1 hB.2.2.1).2 hB.2.2.2
  refine ⟨_, ⟨hD, fun hDC => ?_⟩, hDB.symm⟩
  have := autI_eq_bot_of_le_centralizer hV hDC
  rw [hDB] at this
  exact hB.1.2.1 this

theorem B2_5 (hVH : V ≤ H) (hHN : H ≤ Subgroup.normalizer (V : Set G))
    (hne : (offenderImages hV H).Nonempty) : IsStableFF (autI hV H) (offenderImages hV H) :=
  ⟨hne, fun _ hB => offenderImages_isFFStarOffender hV hVH hHN hB,
    fun _ hB _ hg => offenderImages_conj hV hB hg,
    fun _ hA _ hB => by
      obtain ⟨A, hA', rfl⟩ := hA
      exact offenderImages_ffLe hV hVH hHN hA' hB⟩

omit [Finite G] in
theorem offenderImages_nonempty_iff :
    (offenderImages hV H).Nonempty ↔ ∃ A : Subgroup G, IsFFOffender H V A :=
  ⟨fun ⟨_, A, hA, _⟩ => ⟨A, hA⟩, fun ⟨A, hA⟩ => ⟨_, A, hA, rfl⟩⟩

omit [Finite G] in
theorem offenderImages_nonempty_iff_not_le :
    (offenderImages hV H).Nonempty ↔ ¬ thompsonJ H ≤ Subgroup.centralizer (V : Set G) := by
  rw [offenderImages_nonempty_iff]
  constructor
  · rintro ⟨A, hA, hAV⟩ hJ
    exact hAV ((le_iSup₂_of_le A hA le_rfl : A ≤ thompsonJ H).trans hJ)
  · intro h
    by_contra hcon
    push Not at hcon
    exact h (iSup_le fun A => iSup_le fun hA => by_contra fun hn => hcon A ⟨hA, hn⟩)

end Offenders

section Dichotomy

variable [Finite G] {V H T : Subgroup G} (hV : IsElemAbelian 2 V)

@[expose] def IsStrongFFOffender (H A : Subgroup G) : Prop :=
  IsFFOffender H V A ∧ IsStrongFFStarOffender (autI hV H) (autI hV A)

theorem not_two_dvd_relIndex_inf_of_normalizer {S D K : Subgroup G} (hSK : S ≤ K) (hDK : D ≤ K)
    (hS : ¬ 2 ∣ S.relIndex K) (hSN : S ≤ Subgroup.normalizer (D : Set G)) :
    ¬ 2 ∣ (S ⊓ D).relIndex D := by
  have h1 : (S ⊓ D).relIndex S * S.relIndex (S ⊔ D) = (S ⊓ D).relIndex (S ⊔ D) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left le_sup_left
  have h2 : (S ⊓ D).relIndex D * D.relIndex (S ⊔ D) = (S ⊓ D).relIndex (S ⊔ D) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right le_sup_right
  have h3 : D.relIndex (S ⊔ D) = (S ⊓ D).relIndex S :=
    (B2F.relIndex_sup_eq_of_le_normalizer' hSN).trans (Subgroup.inf_relIndex_left S D).symm
  have h4 : 0 < (S ⊓ D).relIndex S :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := ((S ⊓ D).subgroupOf S)))
  have h5 : (S ⊓ D).relIndex D = S.relIndex (S ⊔ D) := by
    refine Nat.eq_of_mul_eq_mul_left h4 ?_
    rw [h3] at h2
    rw [mul_comm ((S ⊓ D).relIndex S) ((S ⊓ D).relIndex D), h2, ← h1]
  rw [h5]
  have h6 : S.relIndex (S ⊔ D) * (S ⊔ D).relIndex K = S.relIndex K :=
    Subgroup.relIndex_mul_relIndex _ _ _ le_sup_left (sup_le hSK hDK)
  exact fun h => hS (h.trans (Dvd.intro _ h6))

omit [Finite G] in
theorem thompsonJ_le_self (S : Subgroup G) : thompsonJ S ≤ S :=
  iSup_le fun _ => iSup_le fun hA => hA.1

theorem B2_7_of_le_factor (hHN : H ≤ Subgroup.normalizer (V : Set G)) (hT : IsSylowTwoOf T H)
    (hJ : thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    thompsonJ H ≤ Subgroup.centralizer (V : Set G) ∧
      ∀ x ∈ H, ∃ n ∈ H ⊓ Subgroup.normalizer (thompsonJ T : Set G),
        ∃ c ∈ H ⊓ Subgroup.centralizer (V : Set G), x = n * c := by
  have hHC : H ≤ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) :=
    B2F.le_normalizer_centralizer hHN
  refine ⟨thompsonJ_le_of_normalizer hT hHC hJ, ?_⟩
  have hTH : T ≤ H := hT.1
  have hCN : H ≤ Subgroup.normalizer ((H ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    B2F.le_normalizer_inf Subgroup.le_normalizer hHC
  have hRC : T ⊓ Subgroup.centralizer (V : Set G) ≤ H ⊓ Subgroup.centralizer (V : Set G) :=
    inf_le_inf_right _ hTH
  have hR2 : IsPGroup 2 (T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) :=
    hT.2.1.to_le inf_le_left
  have hodd : ¬ 2 ∣ (T ⊓ Subgroup.centralizer (V : Set G)).relIndex
      (H ⊓ Subgroup.centralizer (V : Set G)) := by
    have h := not_two_dvd_relIndex_inf_of_normalizer (S := T) (D := H ⊓ Subgroup.centralizer (V : Set G))
      (K := H) hTH inf_le_left hT.2.2 (hTH.trans hCN)
    have heq : T ⊓ (H ⊓ Subgroup.centralizer (V : Set G)) = T ⊓ Subgroup.centralizer (V : Set G) :=
      le_antisymm (fun x hx => ⟨hx.1, hx.2.2⟩) (fun x hx => ⟨hx.1, hTH hx.1, hx.2⟩)
    rwa [heq] at h
  have hfrat := exists_mul_of_sylow inf_le_left hCN hRC hR2 hodd
  have hJR : thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G) := le_inf (thompsonJ_le_self T) hJ
  have hJeq : thompsonJ T = thompsonJ (T ⊓ Subgroup.centralizer (V : Set G)) :=
    thompsonJ_eq_of_le hJR inf_le_left
  intro x hx
  obtain ⟨n, hn, c, hc, rfl⟩ := hfrat x hx
  refine ⟨n, ⟨hn.1, ?_⟩, c, hc, rfl⟩
  have := normalizer_le_normalizer_thompsonJ (T ⊓ Subgroup.centralizer (V : Set G)) hn.2
  rwa [← hJeq] at this

theorem B2_7_of_le (hHN : H ≤ Subgroup.normalizer (V : Set G)) (hT : IsSylowTwoOf T H)
    (hJ : thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    thompsonJ H ≤ Subgroup.centralizer (V : Set G) ∧
      H = (H ⊓ Subgroup.normalizer (thompsonJ T : Set G)) ⊔
        (H ⊓ Subgroup.centralizer (V : Set G)) :=
  ⟨(B2_7_of_le_factor hHN hT hJ).1,
    B2F.eq_sup_of_forall_exists_mul inf_le_left inf_le_left (B2_7_of_le_factor hHN hT hJ).2⟩

omit [Finite G] in
theorem autI_thompsonJ (hHN : H ≤ Subgroup.normalizer (V : Set G)) :
    autI hV (thompsonJ H) = ffJP (offenderImages hV H) (autI hV H) := by
  unfold thompsonJ
  rw [autI_iSup₂ hV (fun A hA => hA.1.trans hHN)]
  apply le_antisymm
  · refine iSup_le fun A => iSup_le fun hA => ?_
    by_cases h : A ≤ Subgroup.centralizer (V : Set G)
    · rw [autI_eq_bot_of_le_centralizer hV h]
      exact bot_le
    · exact le_iSup₂_of_le (autI hV A) ⟨A, ⟨hA, h⟩, rfl⟩
        (le_iSup_of_le (autI_mono hV hA.1) le_rfl)
  · refine iSup_le fun B => iSup_le fun hB => iSup_le fun _ => ?_
    obtain ⟨A, hA, rfl⟩ := hB
    exact le_iSup₂_of_le A hA.1 le_rfl

theorem B2_7_of_not_le (hVH : V ≤ H) (hHN : H ≤ Subgroup.normalizer (V : Set G))
    (hJ : ¬ thompsonJ H ≤ Subgroup.centralizer (V : Set G)) :
    IsFFModule (autI hV H) ∧ IsStableFF (autI hV H) (offenderImages hV H) ∧
      autI hV (thompsonJ H) = ffJP (offenderImages hV H) (autI hV H) ∧
      ffJP (offenderImages hV H) (autI hV H) ≤ ffJ (autI hV H) := by
  have hne : (offenderImages hV H).Nonempty := (offenderImages_nonempty_iff_not_le hV).2 hJ
  refine ⟨?_, B2_5 hV hVH hHN hne, autI_thompsonJ hV hHN, ?_⟩
  · obtain ⟨B, hB⟩ := hne
    have hnon : {A | IsFFStarOffender (autI hV H) A}.Nonempty :=
      ⟨B, offenderImages_isFFStarOffender hV hVH hHN hB⟩
    exact ((B1_4_5 (fun v : IntMod V hV => IntMod.sq_eq_one v) (autI hV H)).out 2 1).1 hnon
  · refine iSup_le fun B => iSup_le fun hB => iSup_le fun _ => ?_
    exact le_iSup₂_of_le B (offenderImages_isFFStarOffender hV hVH hHN hB) le_rfl

theorem B2_7 (hVH : V ≤ H) (hHN : H ≤ Subgroup.normalizer (V : Set G)) (hT : IsSylowTwoOf T H) :
    (thompsonJ H ≤ Subgroup.centralizer (V : Set G) ∧
      H = (H ⊓ Subgroup.normalizer (thompsonJ T : Set G)) ⊔
        (H ⊓ Subgroup.centralizer (V : Set G))) ∨
    (¬ thompsonJ H ≤ Subgroup.centralizer (V : Set G) ∧ IsFFModule (autI hV H) ∧
      IsStableFF (autI hV H) (offenderImages hV H) ∧
      autI hV (thompsonJ H) = ffJP (offenderImages hV H) (autI hV H) ∧
      ffJP (offenderImages hV H) (autI hV H) ≤ ffJ (autI hV H)) := by
  by_cases h : thompsonJ T ≤ Subgroup.centralizer (V : Set G)
  · exact Or.inl (B2_7_of_le hHN hT h)
  · have hJH : ¬ thompsonJ H ≤ Subgroup.centralizer (V : Set G) := fun h' =>
      h ((thompsonJ_le_thompsonJ_of_isSylowTwoOf hT).trans h')
    exact Or.inr ⟨hJH, B2_7_of_not_le hV hVH hHN hJH⟩

theorem B2_8_card_eq (hVH : V ≤ H) (hHN : H ≤ Subgroup.normalizer (V : Set G)) {A : Subgroup G}
    (hA : IsFFOffender H V A) (hnot : ¬ IsStrongFFOffender hV H A) :
    Nat.card (IntMod V hV) = Nat.card (autI hV A) * Nat.card (fixV (autI hV A)) := by
  have hV2 : ∀ v : IntMod V hV, v ^ 2 = 1 := fun v => IntMod.sq_eq_one v
  have hAs := offenderImages_isFFStarOffender hV hVH hHN ⟨A, hA, rfl⟩
  have hle : rAV (autI hV A) ≤ 1 := B1_4_1 hV2 hAs
  have hnlt : ¬ rAV (autI hV A) < 1 := fun h => hnot ⟨hA, hAs, h⟩
  exact (rAV_eq_one_iff hV2 hAs.isA2).1 (le_antisymm hle (not_lt.1 hnlt))

theorem B2_8_ffLe (hVH : V ≤ H) (hHN : H ≤ Subgroup.normalizer (V : Set G)) {A : Subgroup G}
    (hA : IsFFOffender H V A) (hnot : ¬ IsStrongFFOffender hV H A)
    {B : Subgroup (MulAut (IntMod V hV))} (hB1 : B ≠ ⊥) (hBA : B ≤ autI hV A)
    (hr : rAV B ≤ 1) : FFLe (autI hV H) B (autI hV A) := by
  have hV2 : ∀ v : IntMod V hV, v ^ 2 = 1 := fun v => IntMod.sq_eq_one v
  have hAs := offenderImages_isFFStarOffender hV hVH hHN ⟨A, hA, rfl⟩
  have hB2 : IsA2 (autI hV H) B := hAs.isA2.mono hBA hB1
  have h1 := B2_8_card_eq hV hVH hHN hA hnot
  have h2 := (rAV_le_one_iff hV2 hB2).1 hr
  have h3 := hAs.card_le hBA
  exact ⟨hB2, hAs.isA2, hBA, le_antisymm h3 (h1 ▸ h2)⟩

theorem B2_9_1 (hVH : V ≤ H) (hHN : H ≤ Subgroup.normalizer (V : Set G)) {A : Subgroup G}
    (hA : IsFFOffender H V A) (hnot : ¬ IsStrongFFOffender hV H A)
    {B : Subgroup (MulAut (IntMod V hV))} (hB : IsFFStarOffender (autI hV H) B)
    (hBA : B ≤ autI hV A) : ∃ D : Subgroup G, IsFFOffender H V D ∧ autI hV D = B := by
  have hV2 : ∀ v : IntMod V hV, v ^ 2 = 1 := fun v => IntMod.sq_eq_one v
  have hff := B2_8_ffLe hV hVH hHN hA hnot hB.isA2.ne_bot hBA (B1_4_1 hV2 hB)
  obtain ⟨D, hD, rfl⟩ := offenderImages_ffLe hV hVH hHN hA hff
  exact ⟨D, hD, rfl⟩

theorem B2_9_2 (hVH : V ≤ H) (hHN : H ≤ Subgroup.normalizer (V : Set G)) {A : Subgroup G}
    (hA : IsFFOffender H V A) (hnot : ¬ IsStrongFFOffender hV H A)
    {B : Subgroup (MulAut (IntMod V hV))} (hB1 : B ≠ ⊥) (hBA : B ≤ autI hV A)
    (hr : rAV B ≤ 1) : ∃ D : Subgroup G, IsFFOffender H V D ∧ autI hV D = B := by
  have hff := B2_8_ffLe hV hVH hHN hA hnot hB1 hBA hr
  obtain ⟨D, hD, rfl⟩ := offenderImages_ffLe hV hVH hHN hA hff
  exact ⟨D, hD, rfl⟩

end Dichotomy

section Uniqueness

variable [Finite G] {V H : Subgroup G}

theorem inf_centralizer_le_of_isMaxElemAbelian (hV : IsElemAbelian 2 V) (hVH : V ≤ H)
    {A : Subgroup G} (hA : IsMaxElemAbelian H A) : V ⊓ Subgroup.centralizer (A : Set G) ≤ A := by
  have hcomm : ∀ a ∈ A, ∀ c ∈ V ⊓ Subgroup.centralizer (A : Set G), a * c = c * a :=
    fun a ha c hc => Subgroup.mem_centralizer_iff.1 hc.2 a ha
  have hCe : IsElemAbelian 2 (V ⊓ Subgroup.centralizer (A : Set G)) :=
    B2F.isElemAbelian_mono inf_le_left hV
  have hAC := B2F.isElemAbelian_sup_of_commute hA.2.1 hCe hcomm
  have hle : A ⊔ (V ⊓ Subgroup.centralizer (A : Set G)) ≤ H :=
    sup_le hA.1 (inf_le_left.trans hVH)
  have heq : A = A ⊔ (V ⊓ Subgroup.centralizer (A : Set G)) :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (hA.2.2 _ hle hAC)
  intro c hc
  have : c ∈ A ⊔ (V ⊓ Subgroup.centralizer (A : Set G)) := Subgroup.mem_sup_right hc
  rwa [← heq] at this

omit [Finite G] in
theorem exists_mul_inv_mem_centralizer (hV : IsElemAbelian 2 V) {K₁ K₂ : Subgroup G}
    (hK₁ : K₁ ≤ H) (hHN : H ≤ Subgroup.normalizer (V : Set G)) (h : autI hV K₁ = autI hV K₂) {x : G}
    (hx : x ∈ K₁) : ∃ y ∈ K₂, x * y⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  have h1 : convI hV ⟨x, hHN (hK₁ hx)⟩ ∈ autI hV K₂ := h ▸ convI_mem_autI hV hx (hHN (hK₁ hx))
  obtain ⟨g, hg, hgx⟩ := (mem_autI hV).1 h1
  refine ⟨g, hg, ?_⟩
  have h2 : convI hV (⟨x, hHN (hK₁ hx)⟩ * g⁻¹) = 1 := by
    rw [map_mul, map_inv, hgx, mul_inv_cancel]
  exact (convI_eq_one_iff hV _).1 h2

theorem B2_21 (hV : IsElemAbelian 2 V) (hVH : V ≤ H) (hHN : H ≤ Subgroup.normalizer (V : Set G))
    (hC : H ⊓ Subgroup.centralizer (V : Set G) = V) {A : Subgroup G}
    (hA : IsMaxElemAbelian H A) {a : G} (haA : a ∈ A)
    (ha : V ⊓ Subgroup.centralizer (A : Set G) = V ⊓ Subgroup.centralizer ({a} : Set G))
    {B : Subgroup G} (hB : IsMaxElemAbelian H B) (hAB : autI hV A = autI hV B) : B = A := by
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hA.1.trans hHN
  have hBN : B ≤ Subgroup.normalizer (V : Set G) := hB.1.trans hHN
  have hVAB : V ⊓ Subgroup.centralizer (A : Set G) = V ⊓ Subgroup.centralizer (B : Set G) := by
    ext v
    constructor
    · rintro ⟨hv, hvA⟩
      refine ⟨hv, ?_⟩
      have h1 : IntMod.mk hV ⟨v, hv⟩ ∈ fixV (autI hV A) := (mem_fixV_autI hV hAN _).2 hvA
      rw [hAB] at h1
      exact (mem_fixV_autI hV hBN _).1 h1
    · rintro ⟨hv, hvB⟩
      refine ⟨hv, ?_⟩
      have h1 : IntMod.mk hV ⟨v, hv⟩ ∈ fixV (autI hV B) := (mem_fixV_autI hV hBN _).2 hvB
      rw [← hAB] at h1
      exact (mem_fixV_autI hV hAN _).1 h1
  have hVA : V ⊓ Subgroup.centralizer (A : Set G) ≤ A :=
    inf_centralizer_le_of_isMaxElemAbelian hV hVH hA
  have hVB : V ⊓ Subgroup.centralizer (B : Set G) ≤ B :=
    inf_centralizer_le_of_isMaxElemAbelian hV hVH hB
  have haB : a ∈ B := by
    obtain ⟨b, hbB, hab⟩ := exists_mul_inv_mem_centralizer hV hA.1 hHN hAB haA
    have habV : a * b⁻¹ ∈ V := by
      rw [← hC]
      exact ⟨H.mul_mem (hA.1 haA) (H.inv_mem (hB.1 hbB)), hab⟩
    have hvV : b⁻¹ * a ∈ V := by
      have := (Subgroup.mem_normalizer_iff.1 (hHN (H.inv_mem (hB.1 hbB))) (a * b⁻¹)).1 habV
      simpa [mul_assoc] using this
    set v := b⁻¹ * a with hv
    have hva : a = b * v := by rw [hv]; group
    have ha2 : a * a = 1 := by simpa [pow_two] using hA.2.1.2 a haA
    have hb2 : b * b = 1 := by simpa [pow_two] using hB.2.1.2 b hbB
    have hv2 : v * v = 1 := by simpa [pow_two] using hV.2 v hvV
    have hbv : b * v = v * b := by
      have h1 : b * v * (b * v) = 1 := by rw [← hva]; exact ha2
      have h2 : b * v = (b * v)⁻¹ := mul_eq_one_iff_eq_inv.1 h1
      rw [h2, mul_inv_rev, inv_eq_of_mul_eq_one_right hv2, inv_eq_of_mul_eq_one_right hb2]
    have hvcomm : a * v = v * a := by
      rw [hva]
      calc b * v * v = b * (v * v) := by group
        _ = b := by rw [hv2, mul_one]
        _ = v * (b * v) := by rw [← mul_assoc, ← hbv, mul_assoc, hv2, mul_one]
    have hvC : v ∈ V ⊓ Subgroup.centralizer ({a} : Set G) :=
      ⟨hvV, Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff.1 hh]; exact hvcomm⟩
    have hvB : v ∈ B := hVB (hVAB ▸ ha ▸ hvC)
    rw [hva]
    exact B.mul_mem hbB hvB
  have hBA : B ≤ A := by
    intro b' hb'
    obtain ⟨a', ha'A, hab'⟩ := exists_mul_inv_mem_centralizer hV hB.1 hHN hAB.symm hb'
    have hvV : b' * a'⁻¹ ∈ V := by
      rw [← hC]
      exact ⟨H.mul_mem (hB.1 hb') (H.inv_mem (hA.1 ha'A)), hab'⟩
    have hc1 : b' * a = a * b' := B2F.isElemAbelian_comm hB.2.1 hb' haB
    have hc2 : a' * a = a * a' := B2F.isElemAbelian_comm hA.2.1 ha'A haA
    have hvC : b' * a'⁻¹ ∈ V ⊓ Subgroup.centralizer ({a} : Set G) := by
      refine ⟨hvV, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
      rw [Set.mem_singleton_iff.1 hh]
      calc a * (b' * a'⁻¹) = (a * b') * a'⁻¹ := by group
        _ = (b' * a) * a'⁻¹ := by rw [hc1]
        _ = b' * (a * a'⁻¹) := by group
        _ = b' * (a'⁻¹ * a) := by
          congr 1
          have : a'⁻¹ * (a' * a) * a'⁻¹ = a'⁻¹ * (a * a') * a'⁻¹ := by rw [hc2]
          simpa [mul_assoc] using this
        _ = b' * a'⁻¹ * a := by group
    have hvA : b' * a'⁻¹ ∈ A := hVA (ha ▸ hvC)
    have : b' = (b' * a'⁻¹) * a' := by group
    rw [this]
    exact A.mul_mem hvA ha'A
  exact Subgroup.eq_of_le_of_card_ge hBA (hB.2.2 A hA.1 hA.2.1)

end Uniqueness

end CFSG.Quasithin
