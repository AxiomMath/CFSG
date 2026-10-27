module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2Defs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2Sec2
public import CFSG.Quasithin.EmptyFaithful.S146zRSL2Set

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

namespace E9P2.Cfg

section Quotient

variable {G : Type} [Group G]

theorem qPi_mem_image_iff {G₁ X : Subgroup G} (hX : pCoreOf 2 G₁ ≤ X) {y : G} (hy : y ∈ G₁) :
    qPi G₁ ⟨y, hy⟩ ∈ imageOTwoQuot G₁ X ↔ y ∈ X := by
  have h1 : (⟨y, hy⟩ : ↥G₁) ∈ X.subgroupOf G₁ ↔ y ∈ X := Subgroup.mem_subgroupOf
  rw [← h1, ← imageOTwoQuot_comap hX]
  exact Iff.rfl

theorem exists_hat_quot {G₁ X Q : Subgroup G} (hXG : X ≤ G₁) (hQ : pCoreOf 2 G₁ ≤ Q)
    {N : Type*} [Group N] (f : ↥X →* N) (hs : Function.Surjective f)
    (hk : ∀ x : ↥X, f x = 1 ↔ (x : G) ∈ Q) :
    ∃ g : ↥(imageOTwoQuot G₁ X) →* N, Function.Surjective g ∧
      ∀ z : ↥(imageOTwoQuot G₁ X), g z = 1 ↔ (z : OTwoQuot G₁) ∈ imageOTwoQuot G₁ Q := by
  let τ : ↥X →* ↥(imageOTwoQuot G₁ X) :=
    ((qPi G₁).comp (Subgroup.inclusion hXG)).codRestrict (imageOTwoQuot G₁ X)
      fun x => ⟨Subgroup.inclusion hXG x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  have hτ : Function.Surjective τ := by
    rintro ⟨_, y, hy, rfl⟩
    exact ⟨⟨y, Subgroup.mem_subgroupOf.mp hy⟩, rfl⟩
  have hker : τ.ker ≤ f.ker := by
    intro x hx
    have h1 : qPi G₁ (Subgroup.inclusion hXG x) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have h2 : (x : G) ∈ pCoreOf 2 G₁ :=
      (mk_eq_one_iff_mem_pCoreOf (Subgroup.inclusion hXG x)).mp h1
    exact MonoidHom.mem_ker.mpr ((hk x).mpr (hQ h2))
  let g := MonoidHom.liftOfSurjective τ hτ ⟨f, hker⟩
  have hg : ∀ x : ↥X, g (τ x) = f x := fun x => by simp [g]
  refine ⟨g, ?_, ?_⟩
  · intro n
    obtain ⟨x, rfl⟩ := hs n
    exact ⟨τ x, hg x⟩
  · intro z
    obtain ⟨x, rfl⟩ := hτ z
    rw [hg, hk]
    exact (qPi_mem_image_iff hQ (hXG x.2)).symm

end Quotient

section Setting

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem pCoreOf_mcOf_le_T (S : Setting146 G T M) : pCoreOf 2 (mcOf T) ≤ T :=
  (isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow
    (le_centralizer_quasithinOmegaOneCenter T)).pCoreOf_le

theorem pCoreOf_mcOf_le_pCoreOf (S : Setting146 G T M) (hred : IsRedCE T M H PQ p) :
    pCoreOf 2 (mcOf T) ≤ pCoreOf 2 H :=
  le_pCoreOf_of_le_normalizer 2 ((pCoreOf_mcOf_le_T S).trans hred.isHTM.1.1)
    ((S.le_mcOf hred.isHTM).trans (le_normalizer_pCoreOf 2 (mcOf T)))
    (pCoreOf_isPGroup 2 (mcOf T))

theorem le_hat_pCoreOf (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    {A : Subgroup (OTwoQuot (mcOf T))} (hA2 : IsPGroup 2 A)
    (hAn : ∀ x ∈ imageOTwoQuot (mcOf T) H, x ∈ Subgroup.normalizer (A : Set (OTwoQuot (mcOf T)))) :
    A ≤ imageOTwoQuot (mcOf T) (pCoreOf 2 H) := by
  have hTn : imageOTwoQuot (mcOf T) T ≤ Subgroup.normalizer (A : Set (OTwoQuot (mcOf T))) :=
    fun x hx => hAn x (q_hatT_le_hatH hred hx)
  have hsyl : IsSylowTwoOf (imageOTwoQuot (mcOf T) T) (A ⊔ imageOTwoQuot (mcOf T) T) :=
    isSylowTwoOf_of_le (q_hatT_sylow S) le_sup_right
  have hAT : A ≤ imageOTwoQuot (mcOf T) T :=
    hsyl.le_of_normalizes le_sup_left (sup_le Subgroup.le_normalizer hTn) hA2
  intro a ha
  obtain ⟨t, htG, htT, rfl⟩ := mem_imageOTwoQuot_iff.mp (hAT ha)
  exact mem_imageOTwoQuot_iff.mpr ⟨t, htG, q_mem_pCoreOf_of_mem S hred hA2 hAn htT htG ha, rfl⟩

end Setting

end E9P2.Cfg

section Transport

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

open E9P2.Cfg

theorem e9Local_of_config (h35 : Lemma1435) (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (hshape : IsE9Z4Shape T H p) :
    ∃ Eh : Subgroup (OTwoQuot (mcOf T)),
      Eh ≤ imageOTwoQuot (mcOf T) (oTwoUpper H) ∧
      E9Local (imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T)))
        (imageOTwoQuot (mcOf T) T) (imageOTwoQuot (mcOf T) H) Eh
        (imageOTwoQuot (mcOf T) (pCoreOf 2 H)) := by
  obtain ⟨P, hPK, hPel, hPcard, hPdec⟩ := e9_exists_P h35 S hred hshape
  obtain ⟨φ₀, hφs, hφk⟩ := e9_quot_four h35 S hred hshape
  have hHG : H ≤ mcOf T := S.le_mcOf hred.isHTM
  have hTG : T ≤ mcOf T := hred.isHTM.1.1.trans hHG
  have hPG : P ≤ mcOf T := hPK.trans ((oTwoUpper_le H).trans hHG)
  obtain ⟨hE1, hE2⟩ := zm_isElemAbelian_subgroupOf hPG hPel
  obtain ⟨hEb, hEbc⟩ := isElemAbelian_map_quotient (CFSG.Open.pCore 2 ↥(mcOf T))
    (CFSG.LieType.BorelTits.pCore_isPGroup 2) (by norm_num : (3 : ℕ) ≠ 2) hE1
  obtain ⟨φ, hφs', hφk'⟩ := exists_hat_quot hTG (pCoreOf_mcOf_le_pCoreOf S hred) φ₀ hφs hφk
  refine ⟨imageOTwoQuot (mcOf T) P, q_image_mono hPK, ?_⟩
  exact
  { normal_L := q_normal_image_of_normal (SBc13.kz_le_mcOf S hred)
      (le_normalizer_conjClosure (oTwoUpper H) (mcOf T))
    sylow_T := q_hatT_sylow S
    T_le := q_hatT_le_hatH hred
    solv_H := q_hatH_solvable S hred
    E_le_L := q_image_mono (hPK.trans (le_conjClosure (oTwoUpper H) (mcOf T)))
    E_le_H := q_image_mono (hPK.trans (oTwoUpper_le H))
    card_E := by
      change Nat.card ↥((P.subgroupOf (mcOf T)).map _) = 9
      rw [hEbc, hE2, hPcard]
    exp_E := hEb.2
    comm_E := fun a ha b hb => zmComm hEb ha hb
    dec := by
      intro x hx
      obtain ⟨h, hhG, hhH, rfl⟩ := mem_imageOTwoQuot_iff.mp hx
      obtain ⟨y, hyP, t, htT, hyt⟩ := hPdec h hhH
      have hyG : y ∈ mcOf T := hPG hyP
      have htG : t ∈ mcOf T := hTG htT
      refine ⟨QuotientGroup.mk ⟨y, hyG⟩, mem_imageOTwoQuot_iff.mpr ⟨y, hyG, hyP, rfl⟩,
        QuotientGroup.mk ⟨t, htG⟩, mem_imageOTwoQuot_iff.mpr ⟨t, htG, htT, rfl⟩, ?_⟩
      rw [← QuotientGroup.mk_mul]
      exact congrArg QuotientGroup.mk (Subtype.ext hyt)
    R_le_T := q_image_mono (S.pCoreOf_le_T hred.isHTM)
    R_norm := fun x hx => q_image_mem_normalizer (le_normalizer_pCoreOf 2 H) hx
    R_max := fun A hA2 hAn => le_hat_pCoreOf S hred hA2 hAn
    quot4 := ⟨φ, hφs', hφk'⟩ }

end Transport

end CFSG.Quasithin
