module

public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS4
public import CFSG.Quasithin.Vol2.E2TenSevenPair
public import CFSG.Quasithin.Background.A3Structure312Iso
public import CFSG.Quasithin.Background.F6Basic

public section

namespace CFSG.Quasithin.SimsE210

open CFSG.Open CFSG.QuasithinUnique
open CFSG.Quasithin.E2.Pair (PP)
open scoped commutatorElement

@[expose] def imageModP {Γ : Type} [Group Γ] (X P S : Subgroup Γ) [(P.subgroupOf X).Normal] :
    Subgroup (↥X ⧸ P.subgroupOf X) :=
  (S.subgroupOf X).map (QuotientGroup.mk' (P.subgroupOf X))

@[expose] def IsPerfectCentralExtOfTwoGroupBySz8 (Y : Type) [Group Y] : Prop :=
  ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = ⊤ ∧
    ∃ N : Subgroup Y, N ≤ Subgroup.center Y ∧ IsPGroup 2 ↥N ∧
      ∃ (_ : N.Normal), IsSz 3 (Y ⧸ N)

@[expose] def IsInternalDirectProd {Y : Type} [Group Y] (Y₀ E : Subgroup Y) : Prop :=
  Y₀ ⊓ E = ⊥ ∧ Y₀ ⊔ E = ⊤ ∧ E ≤ Subgroup.centralizer (Y₀ : Set Y)

theorem isPerfectCentralExtOfTwoGroupBySz8_of_surjective {A Y : Type} [Group A] [Group Y]
    (ψ : A →* Y) (hψ : Function.Surjective ψ) {Zs : Subgroup A} [Zs.Normal]
    (hker : ψ.ker ≤ Zs) (h2 : ∀ z ∈ Zs, ∃ k : ℕ, ψ z ^ 2 ^ k = 1)
    (hcen : ⁅Zs, (⊤ : Subgroup A)⁆ ≤ ψ.ker) (hperf : ⁅(⊤ : Subgroup A), ⊤⁆ ⊔ ψ.ker = ⊤)
    (hSz : IsSz 3 (A ⧸ Zs)) : IsPerfectCentralExtOfTwoGroupBySz8 Y := by
  have hN : Zs.map ψ ≤ Subgroup.center Y := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨a, rfl⟩ := hψ y
    have h1 : ψ ⁅z, a⁆ = 1 := hcen (Subgroup.commutator_mem_commutator hz (Subgroup.mem_top a))
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hNn : (Zs.map ψ).Normal :=
    ⟨fun n hn g => by rw [Subgroup.mem_center_iff.1 (hN hn) g, mul_inv_cancel_right]; exact hn⟩
  unfold IsPerfectCentralExtOfTwoGroupBySz8
  refine ⟨?_, Zs.map ψ, hN, ?_, hNn, ?_⟩
  · have h1 : Subgroup.map ψ ⁅(⊤ : Subgroup A), ⊤⁆ = ⁅(⊤ : Subgroup Y), ⊤⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective ψ hψ]
    have h3 : Subgroup.map ψ ψ.ker = ⊥ := (Subgroup.map_eq_bot_iff _).2 le_rfl
    have h4 := congrArg (Subgroup.map ψ) hperf
    rwa [Subgroup.map_sup, h1, h3, sup_bot_eq, Subgroup.map_top_of_surjective ψ hψ] at h4
  · rintro ⟨_, z, hz, rfl⟩
    obtain ⟨k, hk⟩ := h2 z hz
    exact ⟨k, Subtype.ext hk⟩
  · have hψ' : Function.Surjective ((QuotientGroup.mk' (Zs.map ψ)).comp ψ) :=
      (QuotientGroup.mk'_surjective _).comp hψ
    have hker' : ((QuotientGroup.mk' (Zs.map ψ)).comp ψ).ker = Zs := by
      ext a
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      refine ⟨?_, fun ha => ⟨a, ha, rfl⟩⟩
      rintro ⟨z, hz, hza⟩
      have h5 : z⁻¹ * a ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hza, inv_mul_cancel]
      have h6 : a = z * (z⁻¹ * a) := by group
      rw [h6]
      exact Zs.mul_mem hz (hker h5)
    exact IsSz.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hker').symm.trans
        (QuotientGroup.quotientKerEquivOfSurjective _ hψ')) hSz

section Correspondence

variable {Γ : Type} [Group Γ] {X P S E : Subgroup Γ} [(P.subgroupOf X).Normal]

theorem mk_mem_imageModP_iff (hPS : P ≤ S) (x : ↥X) :
    QuotientGroup.mk' (P.subgroupOf X) x ∈ imageModP X P S ↔ (x : Γ) ∈ S := by
  refine ⟨?_, fun hx => ⟨x, hx, rfl⟩⟩
  rintro ⟨y, hy, hyx⟩
  have h1 := QuotientGroup.eq.1 hyx
  rw [Subgroup.mem_subgroupOf] at h1
  have hy' : (y : Γ) ∈ S := hy
  have e : (x : Γ) = (y : Γ) * ((y⁻¹ * x : ↥X) : Γ) := by simp
  rw [e]
  exact S.mul_mem hy' (hPS h1)

theorem imageModP_inf_eq_bot (hPS : P ≤ S) (hPE : P ≤ E) (h : S ⊓ E = P) :
    imageModP X P S ⊓ imageModP X P E = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hzS, hzE⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (P.subgroupOf X) z
  have hx : (x : Γ) ∈ S ⊓ E :=
    ⟨(mk_mem_imageModP_iff hPS x).1 hzS, (mk_mem_imageModP_iff hPE x).1 hzE⟩
  rw [h] at hx
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf]
  exact hx

theorem imageModP_sup_eq_top (h : S ⊔ E = X) :
    imageModP X P S ⊔ imageModP X P E = ⊤ := by
  rw [imageModP, imageModP, ← Subgroup.map_sup,
    ← Subgroup.subgroupOf_sup (h ▸ le_sup_left) (h ▸ le_sup_right), h, Subgroup.subgroupOf_self,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem imageModP_le_centralizer (h : ⁅E, S⁆ ≤ P) :
    imageModP X P E ≤ Subgroup.centralizer (imageModP X P S : Set (↥X ⧸ P.subgroupOf X)) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  have hx' : (x : Γ) ∈ E := hx
  have hy' : (y : Γ) ∈ S := hy
  have hc : (x : Γ)⁻¹ * (y : Γ)⁻¹ * (x : Γ) * (y : Γ) ∈ P := by
    have := h (Subgroup.commutator_mem_commutator (E.inv_mem hx') (S.inv_mem hy'))
    simpa [commutatorElement_def] using this
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  simpa [mul_assoc] using hc

theorem isElemAbelian_imageModP (hsq : ∀ x ∈ E, x ^ 2 ∈ P)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ P) :
    IsElemAbelian 2 (imageModP X P E) := by
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩
    refine Subtype.ext ?_
    have hx' : (x : Γ) ∈ E := hx
    have hy' : (y : Γ) ∈ E := hy
    have hc : (y : Γ)⁻¹ * (x : Γ)⁻¹ * (y : Γ) * (x : Γ) ∈ P := by
      simpa using hcomm _ (E.inv_mem hy') _ (E.inv_mem hx')
    show QuotientGroup.mk' _ x * QuotientGroup.mk' _ y =
      QuotientGroup.mk' _ y * QuotientGroup.mk' _ x
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using hc
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hsq _ hx

theorem imageModP_sup_self (hSX : S ≤ X) (hPX : P ≤ X) :
    imageModP X P (S ⊔ P) = imageModP X P S := by
  rw [imageModP, imageModP, Subgroup.subgroupOf_sup hSX hPX, Subgroup.map_sup,
    QuotientGroup.map_mk'_self, sup_bot_eq]

def toImageModP (hSX : S ≤ X) : ↥S →* ↥(imageModP X P S) :=
  ((QuotientGroup.mk' (P.subgroupOf X)).comp (Subgroup.inclusion hSX)).codRestrict
    (imageModP X P S) fun s => ⟨Subgroup.inclusion hSX s, s.2, rfl⟩

theorem toImageModP_surjective (hSX : S ≤ X) :
    Function.Surjective (toImageModP (P := P) hSX) := by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

theorem ker_toImageModP (hSX : S ≤ X) :
    (toImageModP (P := P) hSX).ker = P.subgroupOf S := by
  ext s
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have h1 : QuotientGroup.mk' (P.subgroupOf X) (Subgroup.inclusion hSX s) = 1 :=
      congrArg Subtype.val h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact h1
  · intro hs
    refine Subtype.ext ?_
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hs)

noncomputable def imageModPEquiv (hSX : S ≤ X) [(P.subgroupOf S).Normal] :
    ↥(imageModP X P S) ≃* ↥S ⧸ P.subgroupOf S :=
  (QuotientGroup.quotientKerEquivOfSurjective _ (toImageModP_surjective (P := P) hSX)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (ker_toImageModP (P := P) hSX))

theorem twoResidual_top_quotient [Finite Γ] (hPX : P ≤ X) :
    twoResidual (⊤ : Subgroup (↥X ⧸ P.subgroupOf X)) = imageModP X P (twoResidual X ⊔ P) := by
  have hq := QuotientGroup.mk'_surjective (P.subgroupOf X)
  have h1 : oTwoUpper (⊤ : Subgroup ↥X) = (oTwoUpper X).subgroupOf X := by
    have h2 := oTwoUpper_map X.subtype (⊤ : Subgroup ↥X)
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
    rw [h2]
    exact (Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective X) _).symm
  calc twoResidual (⊤ : Subgroup (↥X ⧸ P.subgroupOf X))
      = oTwoUpper (⊤ : Subgroup (↥X ⧸ P.subgroupOf X)) := F6.twoResidual_eq_oTwoUpper _
    _ = oTwoUpper (Subgroup.map (QuotientGroup.mk' (P.subgroupOf X)) ⊤) := by
        rw [Subgroup.map_top_of_surjective _ hq]
    _ = (oTwoUpper (⊤ : Subgroup ↥X)).map (QuotientGroup.mk' (P.subgroupOf X)) :=
        oTwoUpper_map _ _
    _ = ((oTwoUpper X).subgroupOf X).map (QuotientGroup.mk' (P.subgroupOf X)) := by rw [h1]
    _ = imageModP X P (twoResidual X ⊔ P) := by
        rw [F6.twoResidual_eq_oTwoUpper, imageModP_sup_self (oTwoUpper_le X) hPX]
        rfl

theorem isPerfectCentralExtOfTwoGroupBySz8_imageModP {Z : Subgroup Γ} (hSX : S ≤ X) (hPZ : P ≤ Z)
    (hZS : Z ≤ S) (hZ2 : ∀ z ∈ Z, ∃ k : ℕ, z ^ 2 ^ k ∈ P) (hZc : ⁅Z, S⁆ ≤ P)
    (hS : ⁅S, S⁆ ⊔ P = S) [(Z.subgroupOf S).Normal] (hSz : IsSz 3 (↥S ⧸ Z.subgroupOf S)) :
    IsPerfectCentralExtOfTwoGroupBySz8 ↥(imageModP X P S) := by
  have hPS : P ≤ S := hPZ.trans hZS
  have hle : ⁅S, S⁆ ≤ S := by
    rw [← Subgroup.map_subtype_commutator]
    exact Subgroup.map_subtype_le _
  have h1 : ⁅S, S⁆.subgroupOf S = ⁅(⊤ : Subgroup ↥S), ⊤⁆ := by
    rw [← Subgroup.map_subtype_commutator]
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective S) _
  have h2 : (⁅S, S⁆ ⊔ P).subgroupOf S = S.subgroupOf S := by rw [hS]
  rw [Subgroup.subgroupOf_sup hle hPS, h1, Subgroup.subgroupOf_self] at h2
  refine isPerfectCentralExtOfTwoGroupBySz8_of_surjective (toImageModP (P := P) hSX)
    (toImageModP_surjective hSX) (Zs := Z.subgroupOf S) ?_ ?_ ?_ ?_ hSz
  · rw [ker_toImageModP]
    exact Subgroup.subgroupOf_mono S hPZ
  · intro z hz
    obtain ⟨k, hk⟩ := hZ2 z hz
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have h3 : z ^ 2 ^ k ∈ (toImageModP (P := P) hSX).ker := by
      rw [ker_toImageModP]
      exact hk
    exact h3
  · rw [ker_toImageModP, Subgroup.commutator_le]
    intro a ha b _
    exact hZc (Subgroup.commutator_mem_commutator ha b.2)
  · rw [ker_toImageModP]
    exact h2

end Correspondence

section Main

theorem seven_of_AS (hS7 : ASInputs.AS_E_2_10_seven) {Γ : Type} [Group Γ] [Finite Γ]
    {X T M V : Subgroup Γ} {g : Γ} (h : E2.Pair X T M V g)
    [((PP M V X g).subgroupOf X).Normal]
    (hY : ∃ n : ℕ, 1 < n ∧ (IsPSL 2 2 n (E2.StarQuot M X) ∨ IsSz n (E2.StarQuot M X))) :
    pCoreOf 2 X = kerIn M X ∧
      (∃ E : Subgroup (↥X ⧸ (PP M V X g).subgroupOf X), IsElemAbelian 2 E ∧
        IsInternalDirectProd (twoResidual (⊤ : Subgroup (↥X ⧸ (PP M V X g).subgroupOf X))) E) ∧
      ((PP M V X g = pCoreOf 2 (twoResidual X ⊔ PP M V X g) ∧
          Nonempty (↥(imageModP X (PP M V X g) (twoResidual X ⊔ PP M V X g)) ≃*
            E2.StarQuot M X)) ∨
        IsPerfectCentralExtOfTwoGroupBySz8
          ↥(imageModP X (PP M V X g) (twoResidual X ⊔ PP M V X g))) := by
  obtain ⟨hJ, ⟨E, hPE, hEX, hE2, hEc, hEL, hEinf, hEsup⟩, hcase⟩ := hS7 Γ X T M V g h hY
  have hPX : PP M V X g ≤ X := hPE.trans hEX
  have hLX : oTwoUpper X ≤ X := oTwoUpper_le X
  have hSX : oTwoUpper X ⊔ PP M V X g ≤ X := sup_le hLX hPX
  have hPS : PP M V X g ≤ oTwoUpper X ⊔ PP M V X g := le_sup_right
  rw [F6.twoResidual_eq_oTwoUpper X]
  refine ⟨hJ.symm, ⟨imageModP X (PP M V X g) E, isElemAbelian_imageModP hE2 hEc, ?_⟩, ?_⟩
  · rw [twoResidual_top_quotient hPX, F6.twoResidual_eq_oTwoUpper X]
    unfold IsInternalDirectProd
    refine ⟨imageModP_inf_eq_bot hPS hPE (by rw [inf_comm]; exact hEinf),
      imageModP_sup_eq_top (by rw [sup_comm]; exact hEsup), ?_⟩
    rw [imageModP_sup_self hLX hPX]
    exact imageModP_le_centralizer hEL
  · rcases hcase with ⟨hpc, hN, ⟨e⟩⟩ | ⟨Z, hPZ, hZS, hZ2, hZc, hSS, hN, hSz⟩
    · exact Or.inl ⟨hpc.symm, ⟨(imageModPEquiv (P := PP M V X g) hSX).trans e⟩⟩
    · exact Or.inr (isPerfectCentralExtOfTwoGroupBySz8_imageModP hSX hPZ hZS hZ2 hZc hSS hSz)

theorem eight_of_AS (hS8 : ASInputs.AS_E_2_10_eight) {Γ : Type} [Group Γ] [Finite Γ]
    {X T M V : Subgroup Γ} {g : Γ} (h : E2.Pair X T M V g)
    [((PP M V X g).subgroupOf X).Normal]
    (hY : ∃ n : ℕ, 1 ≤ n ∧ IsPSp4 2 n (E2.StarQuot M X)) :
    pCoreOf 2 X = kerIn M X ∧
      (∃ Y₀ E : Subgroup (↥X ⧸ (PP M V X g).subgroupOf X), Nonempty (↥Y₀ ≃* E2.StarQuot M X) ∧
        IsElemAbelian 2 E ∧ IsInternalDirectProd Y₀ E) ∧
      pCoreOf 2 (twoResidual X ⊔ PP M V X g) = PP M V X g ∧
      Nonempty (↥(imageModP X (PP M V X g) (twoResidual X ⊔ PP M V X g)) ≃*
        ↥(⁅(⊤ : Subgroup (E2.StarQuot M X)), (⊤ : Subgroup (E2.StarQuot M X))⁆)) := by
  obtain ⟨hJ, ⟨C, E, hPC, hCX, hPE, hEX, ⟨hN, ⟨e⟩⟩, hE2, hEc, hCE, hCEinf, hCEsup⟩, hpc,
    hN2, ⟨e2⟩⟩ := hS8 Γ X T M V g h hY
  have hPX : PP M V X g ≤ X := hPC.trans hCX
  have hSX : oTwoUpper X ⊔ PP M V X g ≤ X := sup_le (oTwoUpper_le X) hPX
  rw [F6.twoResidual_eq_oTwoUpper X]
  refine ⟨hJ, ⟨imageModP X (PP M V X g) C, imageModP X (PP M V X g) E,
    ⟨(imageModPEquiv (P := PP M V X g) hCX).trans e⟩, isElemAbelian_imageModP hE2 hEc, ?_⟩, hpc,
    ⟨(imageModPEquiv (P := PP M V X g) hSX).trans e2⟩⟩
  unfold IsInternalDirectProd
  exact ⟨imageModP_inf_eq_bot hPC hPE hCEinf, imageModP_sup_eq_top hCEsup,
    imageModP_le_centralizer (by rw [Subgroup.commutator_comm]; exact hCE)⟩

end Main

end CFSG.Quasithin.SimsE210
