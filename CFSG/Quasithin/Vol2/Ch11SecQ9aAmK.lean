module

public import CFSG.Quasithin.Vol2.Ch11SecSRole3
public import CFSG.Quasithin.Vol2.Ch11SecAVi2
public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmC
public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmD
public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmG

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G]

theorem commutator_le_right_of {A B : Subgroup G} (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    ⁅A, B⁆ ≤ B :=
  Subgroup.commutator_le.mpr fun _a ha b hb =>
    B.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAB ha) b).mp hb) (B.inv_mem hb)

theorem commutator_le_left_of {A B : Subgroup G} (hBA : B ≤ Subgroup.normalizer (A : Set G)) :
    ⁅A, B⁆ ≤ A :=
  Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def, show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) by group]
    exact A.mul_mem ha ((Subgroup.mem_normalizer_iff.mp (hBA hb) a⁻¹).mp (A.inv_mem ha))

theorem le_normalizer_commutator {S A B : Subgroup G}
    (hA : S ≤ Subgroup.normalizer (A : Set G)) (hB : S ≤ Subgroup.normalizer (B : Set G)) :
    S ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := fun s hs => by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA hs),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hB hs)]

theorem modO2Image_commutator {K A B : Subgroup G} (hA : A ≤ K) (hB : B ≤ K) :
    modO2Image K ⁅A, B⁆ = ⁅modO2Image K A, modO2Image K B⁆ := by
  have hAB : ⁅A, B⁆ ≤ K := Subgroup.commutator_le.mpr fun a ha b hb =>
    K.mul_mem (K.mul_mem (K.mul_mem (hA ha) (hB hb)) (K.inv_mem (hA ha))) (K.inv_mem (hB hb))
  have h : ⁅A.subgroupOf K, B.subgroupOf K⁆ = ⁅A, B⁆.subgroupOf K := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
      Subgroup.map_subgroupOf_eq_of_le hB, Subgroup.map_subgroupOf_eq_of_le hAB]
  unfold modO2Image
  rw [← h, Subgroup.map_commutator]

theorem modO2Image_le_centralizer {K A B : Subgroup G}
    (hAB : A ≤ Subgroup.centralizer (B : Set G)) :
    modO2Image K A ≤
      Subgroup.centralizer (modO2Image K B : Set (↥K ⧸ CFSG.pCore 2 ↥K)) := by
  rintro _ ⟨a, ha, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul]
  exact congrArg _ (Subtype.ext (Subgroup.mem_centralizer_iff.mp (hAB ha) b hb))

theorem modO2Image_eq_bot_of_le {K A : Subgroup G} (hA : A ≤ pCoreOf 2 K) :
    modO2Image K A = ⊥ := by
  refine eq_bot_iff.mpr ?_
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨b, hb, hba⟩ := hA ha
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have : b = a := Subtype.ext hba
  rw [← this]
  exact hb

variable [Finite G] {T L I V₁ V₂ X K : Subgroup G}

theorem not_isShort2_L₂ (hRad : FactParabRadical) (hN : NatFacts) (h1102 : Stmt11_0_2)
    (h : StarHyp G T L I V₁ V₂ X K) (cL : CartanL L V₁ V₂ X) :
    ¬ QuasithinUnique.IsShort2 (LOf L V₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨-, -, -, -, -, hirr⟩
  have hL₂L : LOf L V₂ ≤ L := (perfectCore_le _).trans inf_le_left
  have hL₂V₂ : LOf L V₂ ≤ Subgroup.normalizer (V₂ : Set G) :=
    (perfectCore_le _).trans inf_le_right
  have hL₂p : ⁅LOf L V₂, LOf L V₂⁆ = LOf L V₂ := perfectCore_perfect _
  have hL₂V : LOf L V₂ ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    hL₂L.trans (L_le_normalizer_fsuV h.hyp)
  have hV₂T : V₂ ≤ T := (SecA.IsVi.le_fsuV h.v₂).trans (SecA.fsuV_le_T h.hyp)
  have hV₂2 : IsPGroup 2 ↥V₂ := (SecA.isPGroup_fsuV h.hyp).to_le (SecA.IsVi.le_fsuV h.v₂)
  have hQ := CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) (LOf L V₂)
  have hU : LOf L V₂ ≤ Subgroup.normalizer
      (QuasithinUnique.blockU (LOf L V₂) : Set G) :=
    le_normalizer_commutator hQ Subgroup.le_normalizer
  have hNC : Subgroup.normalizer (LOf L V₂ : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (LOf L V₂ : Set G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer _)
  have hZ : LOf L V₂ ≤ Subgroup.normalizer (QuasithinUnique.blockZ (LOf L V₂) : Set G) :=
    fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hU hx, hNC (Subgroup.le_normalizer hx)⟩
  have hUV : LOf L V₂ ≤ Subgroup.normalizer
      ((QuasithinUnique.blockU (LOf L V₂) ⊓ fsuV T I : Subgroup G) : Set G) :=
    fun x hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨hU hx, hL₂V hx⟩
  have hUL₂ : QuasithinUnique.blockU (LOf L V₂) ≤ LOf L V₂ :=
    commutator_le_right_of ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans Subgroup.le_normalizer)
  rcases hirr (QuasithinUnique.blockZ (LOf L V₂) ⊔ (QuasithinUnique.blockU (LOf L V₂) ⊓ fsuV T I))
    le_sup_left (sup_le inf_le_left inf_le_left) (le_normalizer_sup' hZ hUV) with hW | hW
  ·
    have hUVZ : QuasithinUnique.blockU (LOf L V₂) ⊓ fsuV T I ≤ QuasithinUnique.blockZ (LOf L V₂) :=
      hW ▸ le_sup_right
    have hAL₂ : ⁅V₂, LOf L V₂⁆ ≤ LOf L V₂ :=
      commutator_le_right_of (hV₂T.trans h.T_le_normalizer_L₂)
    have hAV₂ : ⁅V₂, LOf L V₂⁆ ≤ V₂ := commutator_le_left_of hL₂V₂
    have hL₂A : LOf L V₂ ≤ Subgroup.normalizer ((⁅V₂, LOf L V₂⁆ : Subgroup G) : Set G) :=
      le_normalizer_commutator hL₂V₂ Subgroup.le_normalizer
    have hAQ : ⁅V₂, LOf L V₂⁆ ≤ pCoreOf 2 (LOf L V₂) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hAL₂ hL₂A (hV₂2.to_le hAV₂)
    have hAAU : ⁅⁅V₂, LOf L V₂⁆, LOf L V₂⁆ ≤ QuasithinUnique.blockU (LOf L V₂) :=
      Subgroup.commutator_mono hAQ le_rfl
    have hAAV : ⁅⁅V₂, LOf L V₂⁆, LOf L V₂⁆ ≤ fsuV T I :=
      (commutator_le_left_of hL₂A).trans (hAV₂.trans (SecA.IsVi.le_fsuV h.v₂))
    have h1 : ⁅⁅⁅V₂, LOf L V₂⁆, LOf L V₂⁆, LOf L V₂⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        ((le_inf hAAU hAAV).trans (hUVZ.trans inf_le_right))
    have h3 : ⁅V₂, LOf L V₂⁆ = ⊥ :=
      commutator_eq_bot_of_perfect hL₂p (commutator_eq_bot_of_perfect hL₂p h1)
    have hL₂C : LOf L V₂ ≤ Subgroup.centralizer (V₁ : Set G) :=
      (Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3)).trans
        (Subgroup.centralizer_le (SecA.IsVi.mono₁₂ hN h1102 h.hyp h.v₁ h.v₂))
    have hL₂L₁ : LOf L V₂ ≤ LOf L V₁ := by
      calc LOf L V₂ = perfectCore (LOf L V₂) := (perfectCore_eq_self_of_perfect hL₂p).symm
        _ ≤ LOf L V₁ :=
          perfectCore_mono (le_inf hL₂L (hL₂C.trans (Subgroup.centralizer_le_normalizer _)))
    have hXN : X ≤ Subgroup.normalizer (LOf L V₁ : Set G) :=
      cartan_le_normalizer_lOf hN h1102 h.hyp (Or.inl rfl) h.v₁ h.cartan
    have hcard := card_cartan cL hXN
      (cartan_inf_lOf_inf_sectionCentralizer hN h1102 h.hyp h.v₁ h.cartan)
    have hle : X ≤ X ⊓ LOf L V₁ := cL.b.trans (sup_le le_rfl (inf_le_inf_left X hL₂L₁))
    have := Subgroup.card_le_of_le hle
    rw [hcard, cL.card₁] at this
    omega
  ·
    have hVL : fsuV T I ⊓ L ≤ pCoreOf 2 L :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
        (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨L_le_normalizer_fsuV h.hyp hx, Subgroup.le_normalizer hx⟩)
        ((SecA.isPGroup_fsuV h.hyp).to_le inf_le_left)
    have hUL : QuasithinUnique.blockU (LOf L V₂) ≤ L := hUL₂.trans hL₂L
    have hZL : QuasithinUnique.blockZ (LOf L V₂) ≤ L := inf_le_left.trans hUL
    have hUVb : modO2Image L (QuasithinUnique.blockU (LOf L V₂) ⊓ fsuV T I) = ⊥ :=
      modO2Image_eq_bot_of_le (le_inf (inf_le_right) (inf_le_left.trans hUL) |>.trans hVL)
    have himg : modO2Image L (QuasithinUnique.blockU (LOf L V₂)) =
        modO2Image L (QuasithinUnique.blockZ (LOf L V₂)) := by
      conv_lhs => rw [← hW]
      rw [modO2Image_sup hZL (inf_le_left.trans hUL), hUVb, sup_bot_eq]
    have hQL : pCoreOf 2 (LOf L V₂) ≤ L := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hL₂L
    have h1 : ⁅⁅modO2Image L (pCoreOf 2 (LOf L V₂)), modO2Image L (LOf L V₂)⁆,
        modO2Image L (LOf L V₂)⁆ = ⊥ := by
      rw [← modO2Image_commutator hQL hL₂L]
      change ⁅modO2Image L (QuasithinUnique.blockU (LOf L V₂)), modO2Image L (LOf L V₂)⁆ = ⊥
      rw [himg]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (modO2Image_le_centralizer inf_le_right)
    have h2 := commutator_eq_bot_of_perfect (modO2Image_perfect hL₂L hL₂p) h1
    have hO : pCoreOf 2 (modO2Image L (LOf L V₂)) ≤ modO2Image L (pCoreOf 2 (LOf L V₂)) := by
      intro y hy
      obtain ⟨w, hw, rfl⟩ := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hy
      exact ⟨w, mem_pCoreOf_of_mk_mem hL₂L hw hy, rfl⟩
    have hSL : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L := isSylowTwoOf_inf_of h h.hyp.normal
    apply hRad _ h.hyp.shape _ _ (isSylowTwoOf_modO2Image hSL)
      (isL24Sub_lOf hN h1102 h.hyp (Or.inr rfl) h.v₂)
    exact le_bot_iff.mp (h2 ▸ Subgroup.commutator_mono hO le_rfl)

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS
