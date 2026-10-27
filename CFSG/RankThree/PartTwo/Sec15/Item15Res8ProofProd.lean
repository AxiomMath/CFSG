module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res6ProofComp
public import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofDiag
public import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofW2
import CFSG.RankThree.PartTwo.Sec15.Read148PerfProof
import CFSG.RankThree.PartTwo.Sec15.Item15Res3ProofInner
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofPGL
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
public import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Proof15Res8Prod

section Factors

variable {Γ : Type} [Group Γ] [Finite Γ] {D : Subgroup Γ}

theorem factors_of_normal {U₀ V₀ : Subgroup ↥D} (hU₀ : U₀.Normal) (hV₀ : V₀.Normal)
    (hsup : U₀ ⊔ V₀ = ⊤) (hc : ∀ a ∈ U₀, ∀ b ∈ V₀, a * b = b * a) :
    (∀ u ∈ U₀.map D.subtype, ∀ v ∈ V₀.map D.subtype, u * v = v * u) ∧
      U₀.map D.subtype ⊔ V₀.map D.subtype = D ∧
      D ≤ Subgroup.normalizer ((U₀.map D.subtype : Subgroup Γ) : Set Γ) ∧
      D ≤ Subgroup.normalizer ((V₀.map D.subtype : Subgroup Γ) : Set Γ) := by
  have hN : ∀ W₀ : Subgroup ↥D, W₀.Normal →
      D ≤ Subgroup.normalizer ((W₀.map D.subtype : Subgroup Γ) : Set Γ) := by
    intro W₀ hW₀ d hd
    apply Proof15Res8Diag.mem_normalizer_of_conj_mem
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨⟨d, hd⟩ * a * ⟨d, hd⟩⁻¹, hW₀.conj_mem a ha ⟨d, hd⟩, rfl⟩
  refine ⟨?_, ?_, hN U₀ hU₀, hN V₀ hV₀⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hc a ha b hb)
  · rw [← Subgroup.map_sup, hsup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

omit [Finite Γ] in
theorem map_inf_subtype (U₀ V₀ : Subgroup ↥D) :
    U₀.map D.subtype ⊓ V₀.map D.subtype = (U₀ ⊓ V₀).map D.subtype :=
  (Subgroup.map_inf _ _ _ D.subtype_injective).symm

theorem exists_factors_of_prod {P₁ P₂ : Type*} [Group P₁] [Group P₂] (φ : ↥D ≃* P₁ × P₂) :
    ∃ U V : Subgroup Γ, (∀ u ∈ U, ∀ v ∈ V, u * v = v * u) ∧ U ⊓ V = ⊥ ∧ U ⊔ V = D ∧
      D ≤ Subgroup.normalizer (U : Set Γ) ∧ D ≤ Subgroup.normalizer (V : Set Γ) ∧
      Nonempty (↥U ≃* P₁) ∧ Nonempty (↥V ≃* P₂) := by
  set ι₁ : P₁ →* Γ := D.subtype.comp (φ.symm.toMonoidHom.comp (MonoidHom.inl P₁ P₂)) with hι₁
  set ι₂ : P₂ →* Γ := D.subtype.comp (φ.symm.toMonoidHom.comp (MonoidHom.inr P₁ P₂)) with hι₂
  have hinl : Function.Injective (MonoidHom.inl P₁ P₂) := fun a b h => by
    simpa using congrArg Prod.fst h
  have hinr : Function.Injective (MonoidHom.inr P₁ P₂) := fun a b h => by
    simpa using congrArg Prod.snd h
  have hi₁ : Function.Injective ι₁ :=
    D.subtype_injective.comp (φ.symm.injective.comp hinl)
  have hi₂ : Function.Injective ι₂ :=
    D.subtype_injective.comp (φ.symm.injective.comp hinr)
  have hcoe : ∀ p : P₁ × P₂, ((φ.symm p : ↥D) : Γ) = ι₁ p.1 * ι₂ p.2 := by
    intro p
    have h1 : p = MonoidHom.inl P₁ P₂ p.1 * MonoidHom.inr P₁ P₂ p.2 := by
      ext <;> simp
    conv_lhs => rw [h1]
    rw [map_mul]
    rfl
  have hconj₁ : ∀ (q : P₁ × P₂) (a : P₁),
      (φ.symm q : Γ) * ι₁ a * (φ.symm q : Γ)⁻¹ = ι₁ (q.1 * a * q.1⁻¹) := by
    intro q a
    have h1 : q * MonoidHom.inl P₁ P₂ a * q⁻¹ = MonoidHom.inl P₁ P₂ (q.1 * a * q.1⁻¹) := by
      ext <;> simp
    show ((φ.symm q * φ.symm (MonoidHom.inl P₁ P₂ a) * (φ.symm q)⁻¹ : ↥D) : Γ) = _
    rw [← map_mul, ← map_inv, ← map_mul, h1]
    rfl
  have hconj₂ : ∀ (q : P₁ × P₂) (b : P₂),
      (φ.symm q : Γ) * ι₂ b * (φ.symm q : Γ)⁻¹ = ι₂ (q.2 * b * q.2⁻¹) := by
    intro q b
    have h1 : q * MonoidHom.inr P₁ P₂ b * q⁻¹ = MonoidHom.inr P₁ P₂ (q.2 * b * q.2⁻¹) := by
      ext <;> simp
    show ((φ.symm q * φ.symm (MonoidHom.inr P₁ P₂ b) * (φ.symm q)⁻¹ : ↥D) : Γ) = _
    rw [← map_mul, ← map_inv, ← map_mul, h1]
    rfl
  have hD : ∀ d ∈ D, ∃ q : P₁ × P₂, (φ.symm q : Γ) = d := fun d hd =>
    ⟨φ ⟨d, hd⟩, by rw [MulEquiv.symm_apply_apply]⟩
  refine ⟨ι₁.range, ι₂.range, ?_, ?_, ?_, ?_, ?_, ⟨(MonoidHom.ofInjective hi₁).symm⟩,
    ⟨(MonoidHom.ofInjective hi₂).symm⟩⟩
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    have h1 : MonoidHom.inl P₁ P₂ a * MonoidHom.inr P₁ P₂ b =
        MonoidHom.inr P₁ P₂ b * MonoidHom.inl P₁ P₂ a := by
      ext <;> simp
    show ((φ.symm (MonoidHom.inl P₁ P₂ a) * φ.symm (MonoidHom.inr P₁ P₂ b) : ↥D) : Γ) =
      ((φ.symm (MonoidHom.inr P₁ P₂ b) * φ.symm (MonoidHom.inl P₁ P₂ a) : ↥D) : Γ)
    rw [← map_mul, ← map_mul, h1]
  · rw [eq_bot_iff]
    rintro _ ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
    have h1 : MonoidHom.inr P₁ P₂ b = MonoidHom.inl P₁ P₂ a :=
      φ.symm.injective (Subtype.ext hb)
    have h2 : a = 1 := by
      have := congrArg Prod.fst h1
      simpa using this.symm
    rw [h2, map_one]
    exact Subgroup.one_mem _
  · apply le_antisymm
    · refine sup_le ?_ ?_
      · rintro _ ⟨a, rfl⟩
        exact (φ.symm (MonoidHom.inl P₁ P₂ a)).2
      · rintro _ ⟨b, rfl⟩
        exact (φ.symm (MonoidHom.inr P₁ P₂ b)).2
    · intro d hd
      obtain ⟨q, rfl⟩ := hD d hd
      rw [hcoe]
      exact mul_mem (Subgroup.mem_sup_left ⟨_, rfl⟩) (Subgroup.mem_sup_right ⟨_, rfl⟩)
  · intro d hd
    obtain ⟨q, rfl⟩ := hD d hd
    apply Proof15Res8Diag.mem_normalizer_of_conj_mem
    rintro _ ⟨a, rfl⟩
    exact ⟨_, (hconj₁ q a).symm⟩
  · intro d hd
    obtain ⟨q, rfl⟩ := hD d hd
    apply Proof15Res8Diag.mem_normalizer_of_conj_mem
    rintro _ ⟨b, rfl⟩
    exact ⟨_, (hconj₂ q b).symm⟩

end Factors

variable {G : Type} [Group G] [Finite G]

section Iota

variable {A M : Subgroup G} [(ker148 A M).Normal]

omit [Finite G] in
theorem pPrimeCore_le_ker :
    CFSG.pPrimeCore 3 ↥M ≤ ((QuotientGroup.mk' (ker148 A M)).comp
      (Subgroup.inclusion (le_sup_left : M ≤ M ⊔ A))).ker := by
  intro x hx
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, mk'_ker148_eq_one_iff]
  exact ⟨x, hx, rfl⟩

noncomputable def iota148 : (↥M ⧸ CFSG.pPrimeCore 3 ↥M) →* ↥(M ⊔ A) ⧸ ker148 A M :=
  QuotientGroup.lift _ _ pPrimeCore_le_ker

omit [Finite G] in
theorem iota148_mk (x : ↥M) :
    iota148 (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M) x) =
      QuotientGroup.mk' (ker148 A M) (Subgroup.inclusion (le_sup_left : M ≤ M ⊔ A) x) :=
  QuotientGroup.lift_mk _ _ _

omit [Finite G] in
theorem iota148_injective : Function.Injective (iota148 (A := A) (M := M)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro q hq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
  rw [MonoidHom.mem_ker, iota148_mk, mk'_ker148_eq_one_iff] at hq
  obtain ⟨y, hy, hyx⟩ := hq
  have hxy : y = x := Subtype.ext hyx
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hxy ▸ hy

omit [Finite G] in
theorem map_iota148 {X : Subgroup G} (hXM : X ≤ M) :
    ((X.subgroupOf M).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M))).map iota148 =
      img148 A M X := by
  ext q
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [iota148_mk]
    exact ⟨_, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx), rfl⟩
  · rintro ⟨x, hx, rfl⟩
    have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
    refine ⟨QuotientGroup.mk' _ ⟨x, hXM hxX⟩, ⟨⟨x, hXM hxX⟩, Subgroup.mem_subgroupOf.mpr hxX, rfl⟩,
      ?_⟩
    rw [iota148_mk]
    rfl

theorem exists_component_of_le {X Y : Subgroup G} (hXM : X ≤ M) (hYM : Y ≤ M)
    (hN : ((X.subgroupOf M).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M))).Normal)
    {W : Subgroup (↥(M ⊔ A) ⧸ ker148 A M)} (hWX : W ≤ img148 A M X)
    (hXW : img148 A M X ≤ Subgroup.normalizer (W : Set (↥(M ⊔ A) ⧸ ker148 A M)))
    (hWq : IsQuasisimple ↥W) (hYW : img148 A M Y ≤ W) :
    ∃ J : Subgroup (↥M ⧸ CFSG.pPrimeCore 3 ↥M), IsComponent J ∧
      (Y.subgroupOf M).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)) ≤ J := by
  set ι := iota148 (A := A) (M := M) with hι
  have hιi : Function.Injective ι := iota148_injective
  set Xs := (X.subgroupOf M).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)) with hXs
  have hXι : Xs.map ι = img148 A M X := map_iota148 (A := A) hXM
  set J := W.comap ι with hJ
  have hJX : J ≤ Xs := by
    intro q hq
    have h1 : ι q ∈ Xs.map ι := hXι ▸ hWX hq
    obtain ⟨x, hx, hxq⟩ := h1
    exact hιi hxq ▸ hx
  have hXJ : Xs ≤ Subgroup.normalizer (J : Set (↥M ⧸ CFSG.pPrimeCore 3 ↥M)) := by
    intro d hd
    apply Proof15Res8Diag.mem_normalizer_of_conj_mem
    intro q hq
    show ι (d * q * d⁻¹) ∈ W
    rw [map_mul, map_mul, map_inv]
    have hdW : ι d ∈ Subgroup.normalizer (W : Set (↥(M ⊔ A) ⧸ ker148 A M)) :=
      hXW (hXι ▸ Subgroup.mem_map_of_mem ι hd)
    exact (Subgroup.mem_normalizer_iff.mp hdW (ι q)).mp hq
  have hJW : J.map ι = W := by
    refine Subgroup.map_comap_eq_self ?_
    intro w hw
    obtain ⟨x, -, hxw⟩ := (hXι ▸ hWX hw : w ∈ Xs.map ι)
    exact ⟨x, hxw⟩
  have hJq : IsQuasisimple ↥J :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((J.equivMapOfInjective ι hιi).trans (MulEquiv.subgroupCongr hJW)).symm hWq
  refine ⟨J, ⟨hJq, Subgroup.IsSubnormal.step J Xs hJX hN.isSubnormal
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hJX).mpr hXJ)⟩, ?_⟩
  intro y hy
  show ι y ∈ W
  exact hYW (map_iota148 (A := A) hYM ▸ Subgroup.mem_map_of_mem ι hy)

end Iota

section ImgY

variable {A M : Subgroup G} [(ker148 A M).Normal]

theorem isSolvable_or_eq_img148 {Y : Subgroup G} (hYM : Y ≤ M ⊔ A) (hYp : Group.IsPerfect Y)
    (hYq : IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y)) {N : Subgroup (↥(M ⊔ A) ⧸ ker148 A M)}
    (hNY : N ≤ img148 A M Y)
    (hYN : img148 A M Y ≤ Subgroup.normalizer (N : Set (↥(M ⊔ A) ⧸ ker148 A M))) :
    Group.IsSolvable N ∨ N = img148 A M Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : ↥Y →* ↥(M ⊔ A) ⧸ ker148 A M :=
    (QuotientGroup.mk' (ker148 A M)).comp (Subgroup.inclusion hYM) with hφ
  have hrange : φ.range = img148 A M Y := by
    rw [hφ, MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  set N' := N.comap φ with hN'
  have hNmap : N'.map φ = N := Subgroup.map_comap_eq_self (hrange ▸ hNY)
  have hN'n : N'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    show φ (g * n * g⁻¹) ∈ N
    rw [map_mul, map_mul, map_inv]
    have hg : φ g ∈ Subgroup.normalizer (N : Set (↥(M ⊔ A) ⧸ ker148 A M)) :=
      hYN (hrange ▸ ⟨g, rfl⟩)
    exact (Subgroup.mem_normalizer_iff.mp hg (φ n)).mp hn
  set O := CFSG.pCore 2 ↥Y with hO
  have hOs : Group.IsSolvable O := by
    have := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).isNilpotent
    infer_instance
  have hmapn : (N'.map (QuotientGroup.mk' O)).Normal :=
    hN'n.map _ (QuotientGroup.mk'_surjective O)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hYq hmapn with htop | hcen
  · right
    have hsup : N' ⊔ O = ⊤ := by
      have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' O) N'
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
      exact h1.symm
    have hN'top : N' = ⊤ := by
      by_contra hne
      have : Nontrivial (↥Y ⧸ N') := QuotientGroup.nontrivial_iff.mpr hne
      have := hYp
      have hp : Group.IsPerfect (↥Y ⧸ N') :=
        Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N') (QuotientGroup.mk'_surjective _)
      have hsurj : Function.Surjective ((QuotientGroup.mk' N').comp O.subtype) := by
        intro q
        obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N' q
        have hy : y ∈ N' ⊔ O := hsup ▸ Subgroup.mem_top y
        rw [Subgroup.mem_sup_of_normal_right] at hy
        obtain ⟨a, ha, b, hb, rfl⟩ := hy
        refine ⟨⟨b, hb⟩, ?_⟩
        have ha1 : QuotientGroup.mk' N' a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
        rw [MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul, ha1, one_mul]
      have : Group.IsSolvable (↥Y ⧸ N') := Group.isSolvable_of_surjective hsurj
      exact Group.IsPerfect.not_isSolvable (↥Y ⧸ N') this
    rw [← hNmap, hN'top, ← MonoidHom.range_eq_map, hrange]
  · left
    have hle : N' ≤ (Subgroup.center (↥Y ⧸ O)).comap (QuotientGroup.mk' O) := by
      intro n hn
      exact hcen ⟨n, hn, rfl⟩
    have hK := Sec15.isSolvable_comap_center O hOs
    have : Group.IsSolvable N' :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
    rw [← hNmap]
    exact Group.isSolvable_of_surjective (φ.subgroupMap_surjective N')

omit [Finite G] in
theorem le_sSup_img148 {LB : Subgroup G → Subgroup G} {Y : Subgroup G} (hYM : Y ≤ M ⊔ A)
    (hY : Y = delta A LB Y) :
    img148 A M Y ≤ sSup {Q : Subgroup (↥(M ⊔ A) ⧸ ker148 A M) | Q ≤ img148 A M Y ∧
      img148 A M A ≤ Subgroup.normalizer (Q : Set (↥(M ⊔ A) ⧸ ker148 A M)) ∧
      ¬ 3 ∣ Nat.card Q} := by
  set S := {Q : Subgroup (↥(M ⊔ A) ⧸ ker148 A M) | Q ≤ img148 A M Y ∧
      img148 A M A ≤ Subgroup.normalizer (Q : Set (↥(M ⊔ A) ⧸ ker148 A M)) ∧
      ¬ 3 ∣ Nat.card Q} with hS
  set W₁ := ((sSup S).comap (QuotientGroup.mk' (ker148 A M))).map (M ⊔ A).subtype with hW₁
  have hQW : ∀ Q ∈ collectionIn (scriptQ A LB) Y, Q ≤ W₁ := by
    intro Q hQ
    have hQY : Q ≤ Y := hQ.2
    obtain ⟨hπ, hAQ, -⟩ := mem_scriptQ_iff.mp hQ.1
    have hQ3 : ¬ 3 ∣ Nat.card Q := fun h3 => hπ ⟨3, Nat.prime_three⟩ h3 rfl
    have hmem : img148 A M Q ∈ S :=
      ⟨img148_mono hQY, img148_le_normalizer hAQ,
        Item148PtRes.not_three_dvd_card_img148 hQ3⟩
    intro q hq
    have hqM : q ∈ M ⊔ A := hYM (hQY hq)
    refine ⟨⟨q, hqM⟩, ?_, rfl⟩
    exact le_sSup hmem ⟨⟨q, hqM⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
  have hYW : Y ≤ W₁ := by
    rw [hY]
    exact sSup_le hQW
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hzy⟩ := hYW (Subgroup.mem_subgroupOf.mp hy)
  have hzy' : z = y := Subtype.ext hzy
  exact hzy' ▸ hz

theorem card_le_of_isElemAbelian_img148 {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (hAM : A ≤ Subgroup.normalizer (M : Set G)) (hO : CFSG.Open.pCoreOf 2 M ≠ ⊥)
    {F : Subgroup (↥(M ⊔ A) ⧸ ker148 A M)} (hF : CFSG.Assembly.IsElemAbelian 3 F) :
    Nat.card F ≤ 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hlt
  push Not at hlt
  have hF3 : IsPGroup 3 F := Proof15Res8Diag.isPGroup_of_isElemAbelian hF
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hF3
  have h81 : 3 ^ 4 ∣ Nat.card F := by
    rw [hk]
    apply Nat.pow_dvd_pow
    by_contra h4
    push Not at h4
    rw [hk] at hlt
    interval_cases k <;> norm_num at hlt
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥F) 3 h81
  set F' := K.map F.subtype with hF'
  have hF'ab : CFSG.Assembly.IsElemAbelian 3 F' :=
    Proof15Res8Diag.isElemAbelian_of_le hF (Subgroup.map_subtype_le K)
  have hF'81 : Nat.card F' = 81 := by
    rw [hF', Subgroup.card_map_of_injective F.subtype_injective, hK]
    norm_num
  have hF'3 : IsPGroup 3 F' := Proof15Res8Diag.isPGroup_of_isElemAbelian hF'ab
  obtain ⟨P, -, hP3, hPF⟩ := Proof15Res3Inner.exists_isPGroup_map_eq_of_le_map
    (QuotientGroup.mk' (ker148 A M)) (H := ⊤) hF'3
    (by rw [← MonoidHom.range_eq_map, QuotientGroup.range_mk']; exact le_top)
  have hinj : Function.Injective ((QuotientGroup.mk' (ker148 A M)).comp P.subtype) := by
    intro u v huv
    have h1 : ((u : ↥(M ⊔ A)) : G)⁻¹ * ((v : ↥(M ⊔ A)) : G) ∈ pPrimeCoreOf 3 M :=
      mk'_ker148_eq_iff.mp huv
    obtain ⟨j, hj⟩ := hP3 (u⁻¹ * v)
    have h2 : (((u : ↥(M ⊔ A)) : G)⁻¹ * ((v : ↥(M ⊔ A)) : G)) ^ 3 ^ j = 1 := by
      have := congrArg (fun z : ↥P => ((z : ↥(M ⊔ A)) : G)) hj
      simpa using this
    have h3 := eq_one_of_pow_three_pow_eq_one148 (coprime_card_pPrimeCoreOf 3 M) h1 h2
    exact Subtype.ext (Subtype.ext (inv_mul_eq_one.mp h3))
  have hrange : ((QuotientGroup.mk' (ker148 A M)).comp P.subtype).range = F' := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hPF]
  let e : ↥P ≃* ↥F' := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have hPab : CFSG.Assembly.IsElemAbelian 3 P := by
    refine ⟨⟨⟨fun x y => e.injective ?_⟩⟩, fun x hx => ?_⟩
    · rw [map_mul, map_mul]
      exact hF'ab.1.is_comm.comm (e x) (e y)
    · have h1 : ((e ⟨x, hx⟩ : ↥F') : ↥(M ⊔ A) ⧸ ker148 A M) ^ 3 = 1 := hF'ab.2 _ (e ⟨x, hx⟩).2
      have h2 : e (⟨x, hx⟩ ^ 3) = e 1 := by
        apply Subtype.ext
        rw [map_pow, map_one, Subgroup.coe_pow, h1]
        rfl
      exact congrArg Subtype.val (e.injective h2)
  have hP81 : Nat.card P = 81 := (Nat.card_congr e.toEquiv).trans hF'81
  have hO' : CFSG.Open.pCoreOf 2 (M ⊔ A) ≠ ⊥ := by
    intro h0
    apply hO
    rw [eq_bot_iff, ← h0]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 M).trans le_sup_left)
      (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
        (hAM.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 M)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
  exact Proof15Res6.false_of_e81_le h hO' (CFSG.SectionRank.isElemAbelian_map hPab _)
    (by rw [Subgroup.card_map_of_injective (M ⊔ A).subtype_injective, hP81])
    (Subgroup.map_subtype_le P)

end ImgY

end Proof15Res8Prod

open Proof15Res8Prod Proof15Res8Diag

variable {G : Type} [Group G] [Finite G]

section Main


theorem step152CompJProdR_of
    (h148 : Item148R) : Step152CompJProdR := by
  intro G _ _ A c L hR Y hY M hM hYM hF hYΔ hY1 hq hcase
  have h14 := hR.toSec14Std
  have h148' := h148 G A c L hR
  have hAM : A ≤ Subgroup.normalizer (M : Set G) := hM.1.2
  let := ker148_normal hAM
  have hN148 := ((item148_iff A (lB A)).mp h148' M hM.1).1
  have hDp : Group.IsPerfect ↥(img148 A M (deltaZero A (lB A) M)) :=
    Read148Perf.isPerfect_img148 h14 h148' hM.1
  obtain ⟨hEab, hE27⟩ :=
    img148_isE27 (Y := M) (Late.isE27_of_mem_partTwoE h14.mem_partTwoE)
  have hED : img148 A M A ≤ Subgroup.normalizer
      ((img148 A M (deltaZero A (lB A) M) : Subgroup (↥(M ⊔ A) ⧸ ker148 A M)) :
        Set (↥(M ⊔ A) ⧸ ker148 A M)) :=
    img148_le_normalizer (Sec16.le_normalizer_deltaZero (A := A) (LB := lB A) M)
  have hEY : img148 A M A ≤ Subgroup.normalizer
      ((img148 A M Y : Subgroup (↥(M ⊔ A) ⧸ ker148 A M)) : Set (↥(M ⊔ A) ⧸ ker148 A M)) :=
    img148_le_normalizer hY.1.2
  have hYD : img148 A M Y ≤ img148 A M (deltaZero A (lB A) M) := img148_mono hYΔ
  have hYMA : Y ≤ M ⊔ A := hYM.trans le_sup_left
  have hYp0 := isPerfect_of_mem_scriptY4 hY
  have hYp : Group.IsPerfect ↥(img148 A M Y) := by
    have := hYp0
    have : Group.IsPerfect (Y.subgroupOf (M ⊔ A)) :=
      Group.IsPerfect.ofSurjective
        (f := (Subgroup.subgroupOfEquivOfLe hYMA).symm.toMonoidHom) (MulEquiv.surjective _)
    exact Group.IsPerfect.ofSurjective (f := (QuotientGroup.mk' (ker148 A M)).subgroupMap _)
      ((QuotientGroup.mk' (ker148 A M)).subgroupMap_surjective _)
  have hrank : ∀ F : Subgroup (↥(M ⊔ A) ⧸ ker148 A M), CFSG.Assembly.IsElemAbelian 3 F →
      Nat.card F ≤ 27 := fun F hF => card_le_of_isElemAbelian_img148 h14 hAM hM.2 hF
  have hfin : ∀ W : Subgroup (↥(M ⊔ A) ⧸ ker148 A M), W ≤ img148 A M (deltaZero A (lB A) M) →
      img148 A M (deltaZero A (lB A) M) ≤
        Subgroup.normalizer (W : Set (↥(M ⊔ A) ⧸ ker148 A M)) →
      IsQuasisimple ↥W → img148 A M Y ≤ W →
      ∃ J : Subgroup (↥M ⧸ CFSG.pPrimeCore 3 ↥M), IsComponent J ∧
        (Y.subgroupOf M).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)) ≤ J :=
    fun W hWD hDW hWq hYW => exists_component_of_le (deltaZero_le M) hYM hN148 hWD hDW hWq hYW
  have hDiag : ∀ U V : Subgroup (↥(M ⊔ A) ⧸ ker148 A M), (∀ u ∈ U, ∀ v ∈ V, u * v = v * u) →
      U ⊔ V = img148 A M (deltaZero A (lB A) M) → DiagHyp U V (img148 A M A) (img148 A M Y) :=
    fun U V hc hUV => ⟨hc, hEab, hE27, by rw [hUV]; exact hED, hEY, hYD.trans hUV.ge, hYp,
      fun N hNY hYN => isSolvable_or_eq_img148 hYMA hYp0 hY.2.2.2 hNY hYN, hrank⟩
  have hDp' : ∀ U V : Subgroup (↥(M ⊔ A) ⧸ ker148 A M),
      U ⊔ V = img148 A M (deltaZero A (lB A) M) → Group.IsPerfect ↥(U ⊔ V) := fun U V hUV =>
    Group.IsPerfect.ofSurjective (f := (MulEquiv.subgroupCongr hUV).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have hq5 : ∀ {X : Type} [Group X], (X ≃* alternatingGroup (Fin 5)) → IsQuasisimple X :=
    fun e => CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      Sec15.Y4Core.good3_alternatingGroup_five.1
  rcases hcase with ⟨-, hcase⟩ | h6
  · rcases hcase with ⟨U₀, V₀, hU₀, hV₀, hsup, hcomm, h3, hTU, hTV⟩ |
      ⟨U₀, V₀, hU₀, hV₀, hinf, hsup, hTU, ⟨eV⟩⟩ | ⟨⟨φ⟩⟩
    ·
      have hc₀ : ∀ a ∈ U₀, ∀ b ∈ V₀, a * b = b * a := fun a ha b hb =>
        Item148PtRes.commute_of_commutator_eq_bot hcomm ha hb
      obtain ⟨hc, hUV, hDU, hDV⟩ := factors_of_normal hU₀ hV₀ hsup hc₀
      have h3' : Nat.card (U₀.map (img148 A M (deltaZero A (lB A) M)).subtype ⊓
          V₀.map (img148 A M (deltaZero A (lB A) M)).subtype :
            Subgroup (↥(M ⊔ A) ⧸ ker148 A M)) = 3 := by
        rw [map_inf_subtype, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), h3]
      have hTU' := isTripleCover_congr
        (U₀.equivMapOfInjective _ (Subgroup.subtype_injective _)) hTU
      have hTV' := isTripleCover_congr
        (V₀.equivMapOfInjective _ (Subgroup.subtype_injective _)) hTV
      have hcV : ∀ v ∈ V₀.map (img148 A M (deltaZero A (lB A) M)).subtype,
          ∀ u ∈ U₀.map (img148 A M (deltaZero A (lB A) M)).subtype, v * u = u * v :=
        fun v hv u hu => (hc u hu v hv).symm
      have hUp := isPerfect_of_six_six hc h3' hTU' hTV' hrank
      have hVp := isPerfect_of_six_six hcV (by rwa [inf_comm]) hTV' hTU' hrank
      rcases le_or_le_of_six_six (hDiag _ _ hc hUV) h3' hTU' hTV' (hDp' _ _ hUV)
          (le_sSup_img148 hYMA hY.2.2.1) with hYU | hYV
      · exact hfin _ (le_sup_left.trans hUV.le) hDU (isQuasisimple_tripleCover hUp hTU') hYU
      · exact hfin _ (le_sup_right.trans hUV.le) hDV (isQuasisimple_tripleCover hVp hTV') hYV
    ·
      have hc₀ : ∀ a ∈ U₀, ∀ b ∈ V₀, a * b = b * a := fun a ha b hb =>
        Item148PtRes.commute_of_commutator_eq_bot
          (le_bot_iff.mp (hinf ▸ Subgroup.commutator_le_inf U₀ V₀)) ha hb
      obtain ⟨hc, hUV, hDU, hDV⟩ := factors_of_normal hU₀ hV₀ hsup hc₀
      have hinf' : U₀.map (img148 A M (deltaZero A (lB A) M)).subtype ⊓
          V₀.map (img148 A M (deltaZero A (lB A) M)).subtype = ⊥ := by
        rw [map_inf_subtype, hinf, Subgroup.map_bot]
      have hTU' := isTripleCover_congr
        (U₀.equivMapOfInjective _ (Subgroup.subtype_injective _)) hTU
      have eV' := (V₀.equivMapOfInjective _ (Subgroup.subtype_injective _)).symm.trans eV
      have hUp := isPerfect_of_six_five hc hinf' (hDp' _ _ hUV)
      rcases le_or_le_of_six_five (hDiag _ _ hc hUV) hinf' hTU' eV' (hDp' _ _ hUV) with
        hYU | hYV
      · exact hfin _ (le_sup_left.trans hUV.le) hDU (isQuasisimple_tripleCover hUp hTU') hYU
      · exact hfin _ (le_sup_right.trans hUV.le) hDV (hq5 eV') hYV
    ·
      obtain ⟨U, V, hc, hinf, hUV, hDU, hDV, ⟨eU⟩, ⟨eV⟩⟩ := exists_factors_of_prod φ
      rcases le_or_le_of_five_five (hDiag U V hc hUV) hinf eU eV with hYU | hYV
      · exact hfin U (le_sup_left.trans hUV.le) hDU (hq5 eU) hYU
      · exact hfin V (le_sup_right.trans hUV.le) hDV (hq5 eV) hYV
  ·
    obtain ⟨⟨φ⟩, -, -⟩ := h6
    obtain ⟨U, V, hc, hinf, hUV, hDU, hDV, ⟨eU⟩, ⟨eV⟩⟩ := exists_factors_of_prod φ
    rcases le_or_le_of_five_j2 (hDiag U V hc hUV) hinf eU eV with hYU | hYV
    · exact hfin U (le_sup_left.trans hUV.le) hDU (hq5 eU) hYU
    · exact hfin V (le_sup_right.trans hUV.le) hDV
        (isQuasisimple_of_mulEquiv_nativeJ2 CFSG.Sporadic.J2.isSimpleGroup_J2
          (KFacts.KS14.center_nativeJ2_eq_bot Sec4.Sporadic.rank3II_4_15) eV) hYV

theorem step152CompJNTR_of_item148R
    (h148 : Item148R) : Step152CompJNTR :=
  step152CompJNTR_of_res6 h148 (step152CompJProdR_of h148)

theorem step152CompJR_of_item148R
    (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) : Step152CompJR :=
  step152CompJR_of h134 h48 h415 (step152CompJNTR_of_item148R h148)

theorem step152CompR_of_item148R
    (h149 : Sec16.Item149S14) (h148 : Item148R)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) (hSz : KFacts.KPSz) :
    Step152CompR :=
  step152CompR_of' h149 h148 h134 h48 h415 hSz (step152CompJR_of_item148R h148 h134 h48 h415)

theorem item152R_of_item148R_excl
    (h149 : Sec16.Item149S14) (h148 : Item148R)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) (hSz : KFacts.KPSz)
    (hSL25 : Y4CoreExclSL25HJR) : Item152R :=
  item152R_of_compJ_excl h149 h148 h134 h48 h415 hSz (step152CompJNTR_of_item148R h148) hSL25

end Main

end CFSG.RankThree.PartTwo.Sec15
